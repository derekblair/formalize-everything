import Garling.Chapter01
import Garling.Chapter02
import Garling.Chapter03
import Garling.Chapter04
import Garling.Chapter05
import Garling.Chapter06
import Mathlib.FieldTheory.SplittingField.Construction

/-!
# Chapter 7: Splitting fields

Formalization of Chapter 7 (*Splitting fields*, printed pp. 59–70 / PDF pp. 67–78) of
D. J. H. Garling, *A Course in Galois Theory* (Cambridge University Press, 1986):

- **Chapter 7 Preamble & `Exercise 7.1`** (printed p. 59 / PDF p. 67):
  complex linear factorization motivation, finite splitting subfields over `ℚ` inside `ℂ`, and
  `Exercise 7.1` (irreducible polynomials in `ℝ[x]` have degree `≤ 2`).
- **§7.1 Splitting fields** (printed pp. 60–62 / PDF pp. 68–70):
  prose definitions of *`f` splits over `L`* and *splitting field extension*, bridges to Mathlib's
  `Polynomial.Splits` and `Polynomial.IsSplittingField`, `Theorem 7.1` (with `f = 0` counterexample
  and exact `iff` characterization), `Corollary` [to Theorem 7.1], `Theorem 7.2`, `Theorem 7.3`
  (with `garlingDegree`, unconditional existence, and `natDegree!` bound), `Exercise 7.2`, and
  `Exercise 7.3`.
- **§7.2 The extension of monomorphisms** (printed pp. 62–67 / PDF pp. 70–75):
  induced polynomial-ring monomorphism `i : K[x] → L[x]`, `Theorem 7.4`, `Corollary 1` and
  `Corollary 2` [to Theorem 7.4], `Theorem 7.5`, `Corollary 1` and `Corollary 2` [to Theorem 7.5],
  and `Exercise 7.4`.
- **§7.3 Some examples** (printed pp. 67–70 / PDF pp. 75–78):
  worked `Example 1` (`x^p - 2 ∈ ℚ[x]` for prime `p`), `Example 2` (`x^6 - 1 ∈ ℚ[x]`),
  `Example 3` (`x^6 + 1 ∈ ℚ[x]`), `Example 4` (`x^2 + ax + b ∈ K[x]` in `char K ≠ 2` and `ℤ₂`),
  and `Exercises 7.5`–`7.10`.
-/

namespace Garling.Chapter07

open Garling.Chapter01 Garling.Chapter02 Garling.Chapter03
open Garling.Chapter04 Garling.Chapter05 Garling.Chapter06
open scoped BigOperators Polynomial

/-! ## Chapter 7 Preamble & `Exercise 7.1` (printed p. 59, PDF p. 67) -/

/-- Preamble motivation (printed p. 59 / PDF p. 67): every non-constant polynomial `p ∈ ℂ[X]` has a
root in `ℂ` (the 'fundamental theorem of algebra'), and every non-unit polynomial `f ∈ ℂ[X]` with
`f ≠ 0` splits into linear factors `c * ∏ j : Fin n, (X - C (α j))` (`n ≥ 1`). -/
theorem preamble_complex_linear_factorization :
    (∀ p : ℂ[X], 0 < p.natDegree → ∃ z : ℂ, p.IsRoot z) ∧
    (∀ f : ℂ[X], f ≠ 0 → ¬ IsUnit f →
      ∃ (n : ℕ) (c : ℂ) (α : Fin n → ℂ),
        1 ≤ n ∧ c ≠ 0 ∧
        f = Polynomial.C c * ∏ j : Fin n, (Polynomial.X - Polynomial.C (α j))) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    have hdeg0 : p.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_natDegree_gt hp)]
      exact mod_cast hp.ne'
    exact IsAlgClosed.exists_root p hdeg0
  · intro f hf0 hnu
    have hdeg_pos : 0 < f.natDegree := by
      by_contra hle
      push Not at hle
      have h0 : f.natDegree = 0 := Nat.eq_zero_of_le_zero hle
      rw [Polynomial.eq_C_of_natDegree_eq_zero h0] at hf0 hnu
      have hc0 : f.coeff 0 ≠ 0 := fun h => hf0 (by simp [h])
      exact hnu ((isUnit_iff_ne_zero.mpr hc0).map Polynomial.C)
    have hsplits : f.Splits := IsAlgClosed.splits f
    obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.mp hsplits
    let l : List ℂ := m.toList
    have hm_coe : (l : Multiset ℂ) = m := Multiset.coe_toList m
    have hprod :
        (Multiset.map (fun x : ℂ => Polynomial.X - Polynomial.C x) m).prod =
          ∏ j : Fin l.length, (Polynomial.X - Polynomial.C (l.get j)) := by
      conv_lhs =>
        rw [← hm_coe, Multiset.map_coe, Multiset.prod_coe, ← List.ofFn_get l, List.map_ofFn]
      simpa [Function.comp_def] using
        (List.prod_ofFn (f := fun j : Fin l.length => Polynomial.X - Polynomial.C (l.get j)))
    have hlen : l.length = f.natDegree := by
      have h1 := congrArg Polynomial.natDegree hm
      rw [hprod, Polynomial.natDegree_C_mul (Polynomial.leadingCoeff_ne_zero.mpr hf0),
        Polynomial.natDegree_prod _ _ (fun j _ => Polynomial.X_sub_C_ne_zero _)] at h1
      simpa using h1.symm
    refine ⟨l.length, f.leadingCoeff, l.get, by omega,
      Polynomial.leadingCoeff_ne_zero.mpr hf0, ?_⟩
    exact hm.trans (by rw [hprod])

private theorem natDegree_eq_of_associated {K : Type*} [Field K] {p q : K[X]}
    (hp : p ≠ 0) (hq : q ≠ 0) (h : Associated p q) :
    p.natDegree = q.natDegree :=
  le_antisymm
    (Polynomial.natDegree_le_of_dvd h.dvd hq)
    (Polynomial.natDegree_le_of_dvd h.symm.dvd hp)

/-- **Exercise 7.1** (Ch. 7 Preamble, printed p. 59 / PDF p. 67):
*"Suppose that `f` is an irreducible polynomial in `ℝ[x]`. Show that `degree f ≤ 2`."* -/
theorem exercise_7_1 {f : ℝ[X]} (hirr : Irreducible f) :
    garlingDegree f hirr.ne_zero ≤ 2 := by
  have hf0 : f ≠ 0 := hirr.ne_zero
  have hdeg_pos : 0 < f.natDegree := by
    by_contra hle
    push Not at hle
    have h0 : f.natDegree = 0 := Nat.eq_zero_of_le_zero hle
    have hfc : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
    have hc0 : f.coeff 0 ≠ 0 := fun h => hf0 (by rw [hfc, h, map_zero])
    exact hirr.not_isUnit (hfc ▸ (isUnit_iff_ne_zero.mpr hc0).map Polynomial.C)
  let fC : ℂ[X] := f.map (algebraMap ℝ ℂ)
  have hfC_deg : fC.natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective f
  have hfC_deg_ne0 : fC.degree ≠ 0 := by
    have hfC0 : fC ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hf0
    rw [Polynomial.degree_eq_natDegree hfC0, hfC_deg]
    exact mod_cast hdeg_pos.ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root fC hfC_deg_ne0
  have haeval : Polynomial.aeval z f = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact hz
  have hz_int : IsIntegral ℝ z :=
    isAlgebraic_iff_isIntegral.mp ⟨f, hf0, haeval⟩
  have hdvd : minpoly ℝ z ∣ f := minpoly.dvd ℝ z haeval
  have hm_irr : Irreducible (minpoly ℝ z) := minpoly.irreducible hz_int
  have hass : Associated (minpoly ℝ z) f :=
    hm_irr.associated_of_dvd hirr hdvd
  have hdeg_eq : (minpoly ℝ z).natDegree = f.natDegree :=
    natDegree_eq_of_associated hm_irr.ne_zero hf0 hass
  have hfinrank_le :
      Module.finrank ℝ (IntermediateField.adjoin ℝ ({z} : Set ℂ)) ≤ Module.finrank ℝ ℂ :=
    Submodule.finrank_le (IntermediateField.adjoin ℝ ({z} : Set ℂ)).toSubmodule
  have hadj_deg :
      Module.finrank ℝ (IntermediateField.adjoin ℝ ({z} : Set ℂ)) = (minpoly ℝ z).natDegree :=
    IntermediateField.adjoin.finrank hz_int
  have hC_dim : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  unfold garlingDegree
  omega

/-- **Exercise 7.1 (Garling irreducibility predicate)** (printed p. 59 / PDF p. 67):
If `f ∈ ℝ[x]` satisfies `IsGarlingIrreducible f`, then `1 ≤ garlingDegree f f.ne_zero` and
`garlingDegree f f.ne_zero ≤ 2`. -/
theorem exercise_7_1_garling {f : ℝ[X]} (hirr : IsGarlingIrreducible f) :
    1 ≤ garlingDegree f hirr.ne_zero ∧ garlingDegree f hirr.ne_zero ≤ 2 := by
  have hirr' : Irreducible f := (isGarlingIrreducible_iff f).mp hirr
  have hle2 : garlingDegree f hirr'.ne_zero ≤ 2 := exercise_7_1 hirr'
  have hge1 : 1 ≤ garlingDegree f hirr.ne_zero := by
    unfold garlingDegree
    by_contra hlt
    have h0 : f.natDegree = 0 := by omega
    have hfc : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
    have hc0 : f.coeff 0 ≠ 0 := fun h => hirr.ne_zero (by rw [hfc, h, map_zero])
    exact hirr'.not_isUnit (hfc ▸ (isUnit_iff_ne_zero.mpr hc0).map Polynomial.C)
  exact ⟨hge1, hle2⟩

/-! ## §7.1 Splitting fields (printed pp. 60–62, PDF pp. 68–70) -/

/-- Explicit linear factorization of `f ∈ K[X]` over an extension `L : K` (§7.1, printed p. 60):
`f = c * (x - α₁) ⋯ (x - α_n)` in `L[X]`, with `α₁, …, α_n ∈ L` and `c ∈ K` (note: p. 60 writes
`λ ∈ K` without restricting to `λ ≠ 0`). -/
def GarlingSplitsExplicit (K L : Type*) [Field K] [Field L] [Algebra K L]
    (f : K[X]) (n : ℕ) (c : K) (α : Fin n → L) : Prop :=
  f.map (algebraMap K L) =
    Polynomial.C (algebraMap K L c) * ∏ j : Fin n, (Polynomial.X - Polynomial.C (α j))

/-- Garling's prose definition of *`f` splits over `L`* (§7.1, printed p. 60 / PDF p. 68):
there exist `n : ℕ`, `c ∈ K`, and `α₁, …, α_n ∈ L` such that
`f = c * (x - α₁) ⋯ (x - α_n)` in `L[X]`. -/
def GarlingSplitsOver (K L : Type*) [Field K] [Field L] [Algebra K L] (f : K[X]) : Prop :=
  ∃ (n : ℕ) (c : K) (α : Fin n → L), GarlingSplitsExplicit K L f n c α

/-- Garling's prose definition of *splitting field extension* (`L : K` is a splitting field
extension for `f` over `K`, or `L` is a *splitting field* for `f`; §7.1, printed p. 60 / PDF p. 68):
first, `f` splits over `L`, and secondly, there is no proper subfield `L'` of `L` containing `K`
such that `f` splits over `L'`. -/
def IsGarlingSplittingFieldExtension (K L : Type*) [Field K] [Field L] [Algebra K L]
    (f : K[X]) : Prop :=
  GarlingSplitsOver K L f ∧
  ∀ M : IntermediateField K L, M ≠ ⊤ → ¬ GarlingSplitsOver K M f

/-- When `f ≠ 0`, any explicit splitting `f = c(x - α₁)⋯(x - α_n)` over `L : K` forces
`c = f.leadingCoeff ≠ 0`, `n = garlingDegree f hf = f.natDegree`, and `{α₁, …, α_n} = f.rootSet L`. -/
theorem garlingSplitsExplicit_props {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hf : f ≠ 0) {n : ℕ} {c : K} {α : Fin n → L}
    (hsplit : GarlingSplitsExplicit K L f n c α) :
    c = f.leadingCoeff ∧
    c ≠ 0 ∧
    n = garlingDegree f hf ∧
    Set.range α = f.rootSet L := by
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  have hfL0 : f.map (algebraMap K L) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hf
  have hprod_monic : (∏ j : Fin n, (Polynomial.X - Polynomial.C (α j))).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C (α j)
  have hlc : algebraMap K L c = (f.map (algebraMap K L)).leadingCoeff := by
    rw [hsplit, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hprod_monic.leadingCoeff,
      mul_one]
  have hc_eq : c = f.leadingCoeff := by
    apply hinj
    rw [hlc, Polynomial.leadingCoeff_map_of_injective hinj]
  have hc0 : c ≠ 0 := hc_eq ▸ Polynomial.leadingCoeff_ne_zero.mpr hf
  have hdeg : n = garlingDegree f hf := by
    have h1 := congrArg Polynomial.natDegree hsplit
    rw [Polynomial.natDegree_map_eq_of_injective hinj,
      Polynomial.natDegree_C_mul ((map_ne_zero (algebraMap K L)).mpr hc0),
      Polynomial.natDegree_prod _ _ (fun j _ => Polynomial.X_sub_C_ne_zero _)] at h1
    simpa [garlingDegree] using h1.symm
  have hroots : Set.range α = f.rootSet L := by
    ext x
    rw [Set.mem_range, Polynomial.mem_rootSet]
    have hcL0 : algebraMap K L c ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hc0
    have heval_iff : Polynomial.aeval x f = 0 ↔ ∃ j : Fin n, α j = x := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hsplit, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_prod, mul_eq_zero, or_iff_right hcL0,
        Finset.prod_eq_zero_iff]
      constructor
      · rintro ⟨j, _, hj⟩
        rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hj
        exact ⟨j, hj.symm⟩
      · rintro ⟨j, rfl⟩
        refine ⟨j, Finset.mem_univ j, ?_⟩
        rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
    exact ⟨fun hx => ⟨hf, heval_iff.mpr hx⟩, fun hx => heval_iff.mp hx.2⟩
  exact ⟨hc_eq, hc0, hdeg, hroots⟩

/-- Exact bridge: `GarlingSplitsOver K L f` agrees with Mathlib's `(f.map (algebraMap K L)).Splits`
for **every** polynomial `f ∈ K[X]` (including `f = 0` and degree-`0` constants). -/
theorem garlingSplitsOver_iff_splits (K L : Type*) [Field K] [Field L] [Algebra K L] (f : K[X]) :
    GarlingSplitsOver K L f ↔ (f.map (algebraMap K L)).Splits := by
  by_cases hf : f = 0
  · subst hf
    simp only [Polynomial.map_zero, Polynomial.Splits.zero, iff_true]
    refine ⟨0, 0, Fin.elim0, ?_⟩
    simp [GarlingSplitsExplicit]
  · have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
    constructor
    · rintro ⟨n, c, α, hsplit⟩
      rw [Polynomial.splits_iff_exists_multiset]
      obtain ⟨rfl, _, _, _⟩ := garlingSplitsExplicit_props hf hsplit
      refine ⟨Multiset.map α Finset.univ.val, ?_⟩
      rw [Polynomial.leadingCoeff_map_of_injective hinj, Multiset.map_map]
      simpa [GarlingSplitsExplicit, Finset.prod_eq_multiset_prod] using hsplit
    · intro hsplits
      obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.mp hsplits
      let l : List L := m.toList
      have hm_coe : (l : Multiset L) = m := Multiset.coe_toList m
      have hprod :
          (Multiset.map (fun x : L => Polynomial.X - Polynomial.C x) m).prod =
            ∏ j : Fin l.length, (Polynomial.X - Polynomial.C (l.get j)) := by
        conv_lhs =>
          rw [← hm_coe, Multiset.map_coe, Multiset.prod_coe, ← List.ofFn_get l, List.map_ofFn]
        simpa [Function.comp_def] using
          (List.prod_ofFn (f := fun j : Fin l.length => Polynomial.X - Polynomial.C (l.get j)))
      refine ⟨l.length, f.leadingCoeff, l.get, ?_⟩
      unfold GarlingSplitsExplicit
      rw [hm, Polynomial.leadingCoeff_map_of_injective hinj, hprod]

/-- Pushing an explicit splitting from an intermediate field `M : IntermediateField K L` to `L`
and pulling one back when all roots lie in `M`. -/
theorem garlingSplitsOver_intermediateField_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) (f : K[X]) :
    GarlingSplitsOver K M f ↔
      ∃ (n : ℕ) (c : K) (α : Fin n → L),
        (∀ j, α j ∈ M) ∧ GarlingSplitsExplicit K L f n c α := by
  constructor
  · rintro ⟨n, c, αM, hM⟩
    refine ⟨n, c, fun j => (αM j : L), fun j => (αM j).2, ?_⟩
    unfold GarlingSplitsExplicit at hM ⊢
    have hmap :
        (f.map (algebraMap K M)).map M.val.toRingHom = f.map (algebraMap K L) := by
      rw [Polynomial.map_map]
      rfl
    rw [← hmap, hM]
    simp [Polynomial.map_mul, Polynomial.map_prod]
  · rintro ⟨n, c, α, hmem, hL⟩
    refine ⟨n, c, fun j => ⟨α j, hmem j⟩, ?_⟩
    unfold GarlingSplitsExplicit at hL ⊢
    apply Polynomial.map_injective M.val.toRingHom M.val.injective
    have hmap :
        (f.map (algebraMap K M)).map M.val.toRingHom = f.map (algebraMap K L) := by
      rw [Polynomial.map_map]
      rfl
    rw [hmap, hL]
    simp [Polynomial.map_mul, Polynomial.map_prod]

/-- Equivalence between `IsGarlingSplittingFieldExtension` (stated with `IntermediateField K L`) and
the literal `Subfield L` formulation on printed p. 60 (*"no proper subfield `L'` of `L` containing
`K`"*). -/
theorem isGarlingSplittingFieldExtension_iff_subfield (K L : Type*) [Field K] [Field L]
    [Algebra K L] (f : K[X]) :
    IsGarlingSplittingFieldExtension K L f ↔
      GarlingSplitsOver K L f ∧
      ∀ L' : Subfield L, Set.range (algebraMap K L) ⊆ (L' : Set L) → L' ≠ ⊤ →
        ¬ ∃ (n : ℕ) (c : K) (α : Fin n → L),
            (∀ j, α j ∈ L') ∧ GarlingSplitsExplicit K L f n c α := by
  refine and_congr_right fun _ => ?_
  constructor
  · intro hmin L' hK hne hex
    let M : IntermediateField K L :=
      { L' with algebraMap_mem' := fun k => hK ⟨k, rfl⟩ }
    have hMne : M ≠ ⊤ := by
      intro htop
      apply hne
      ext x
      have hx : x ∈ M := htop ▸ IntermediateField.mem_top
      simpa [M] using hx
    exact hmin M hMne ((garlingSplitsOver_intermediateField_iff M f).mpr hex)
  · intro hmin M hMne hsplitM
    have hK : Set.range (algebraMap K L) ⊆ (M.toSubfield : Set L) := by
      rintro _ ⟨k, rfl⟩
      exact M.algebraMap_mem k
    have hsub_ne : M.toSubfield ≠ ⊤ := by
      intro htop
      apply hMne
      ext x
      simp only [IntermediateField.mem_top, iff_true]
      have hx : x ∈ M.toSubfield := htop ▸ Subfield.mem_top x
      exact hx
    exact hmin M.toSubfield hK hsub_ne ((garlingSplitsOver_intermediateField_iff M f).mp hsplitM)

/-- Exact characterization of splitting fields of the zero polynomial `0 ∈ K[X]`: because
`0 = 0 · 1` splits over every extension (in particular over `⊥ = K`), `L : K` is a splitting field
extension for `0` iff `⊥ = ⊤` (`algebraMap K L` is surjective). -/
theorem isGarlingSplittingFieldExtension_zero_iff (K L : Type*) [Field K] [Field L]
    [Algebra K L] :
    IsGarlingSplittingFieldExtension K L 0 ↔ (⊥ : IntermediateField K L) = ⊤ := by
  have hbot : GarlingSplitsOver K (⊥ : IntermediateField K L) 0 :=
    ⟨0, 0, Fin.elim0, by simp [GarlingSplitsExplicit]⟩
  constructor
  · rintro ⟨_, hmin⟩
    by_contra hne
    exact hmin ⊥ hne hbot
  · intro htop
    refine ⟨⟨0, 0, Fin.elim0, by simp [GarlingSplitsExplicit]⟩, fun M hMne _ => hMne ?_⟩
    exact top_unique (htop ▸ bot_le)

/-- **Counterexample to the literal `f = 0` case of `Theorem 7.1`** (§7.1, printed p. 60):
Over `ℂ : ℚ`, `f = 0 ∈ ℚ[X]` splits as `0 = 0 · (x - i)` (`n = 1`, `λ = 0 ∈ ℚ`, `α₁ = i ∈ ℂ`),
satisfying the literal printed hypotheses of `Theorem 7.1`, yet `ℚ(i)` is **not** a splitting field
for `0` over `ℚ` because `0 = 0 · 1` already splits over the proper subfield `ℚ ⊂neq ℚ(i)`. -/
theorem theorem_7_1_zero_counterexample :
    let α : Fin 1 → ℂ := fun _ => Complex.I
    GarlingSplitsExplicit ℚ ℂ 0 1 0 α ∧
    ¬ IsGarlingSplittingFieldExtension ℚ (IntermediateField.adjoin ℚ (Set.range α)) 0 := by
  intro α
  refine ⟨by simp [GarlingSplitsExplicit], ?_⟩
  rw [isGarlingSplittingFieldExtension_zero_iff]
  intro hbot_top
  have hI_mem :
      (⟨Complex.I, IntermediateField.subset_adjoin ℚ (Set.range α) ⟨0, rfl⟩⟩ :
        IntermediateField.adjoin ℚ (Set.range α)) ∈
        (⊥ : IntermediateField ℚ (IntermediateField.adjoin ℚ (Set.range α))) := by
    rw [hbot_top]
    exact IntermediateField.mem_top
  rw [IntermediateField.mem_bot] at hI_mem
  obtain ⟨q, hq⟩ := hI_mem
  have hqC : (algebraMap ℚ ℂ q) = Complex.I := congrArg Subtype.val hq
  have him := congrArg Complex.im hqC
  simp at him

/-- **Theorem 7.1** (§7.1, printed p. 60 / PDF p. 68, with explicit `f ≠ 0` guard; see `QUEUE.md`):
Suppose that `L : K` is an extension and that `f ∈ K[X]` (`f ≠ 0`) splits over `L` as
`f = λ(x - α₁)⋯(x - α_n)`. Then `K(α₁, …, α_n)` is a splitting field for `f` over `K`. -/
theorem theorem_7_1 {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hf : f ≠ 0) {n : ℕ} {c : K} {α : Fin n → L}
    (hsplit : GarlingSplitsExplicit K L f n c α) :
    IsGarlingSplittingFieldExtension K (IntermediateField.adjoin K (Set.range α)) f := by
  let E : IntermediateField K L := IntermediateField.adjoin K (Set.range α)
  have hαE : ∀ j : Fin n, α j ∈ E := fun j =>
    IntermediateField.subset_adjoin K (Set.range α) ⟨j, rfl⟩
  have hsplitE : GarlingSplitsOver K E f :=
    (garlingSplitsOver_intermediateField_iff E f).mpr ⟨n, c, α, hαE, hsplit⟩
  refine ⟨hsplitE, fun M hMne hsplitM => hMne ?_⟩
  obtain ⟨m, c', βM, hβM⟩ := hsplitM
  let β : Fin m → L := fun j => ((βM j : E) : L)
  have hsplitL_β : GarlingSplitsExplicit K L f m c' β := by
    unfold GarlingSplitsExplicit at hβM ⊢
    have hmap :
        (f.map (algebraMap K M)).map (E.val.toRingHom.comp M.val.toRingHom) =
          f.map (algebraMap K L) := by
      rw [Polynomial.map_map]
      rfl
    rw [← hmap, hβM]
    simp [Polynomial.map_mul, Polynomial.map_prod, β]
  have hrange_eq : Set.range α = Set.range β :=
    (garlingSplitsExplicit_props hf hsplit).2.2.2.trans
      (garlingSplitsExplicit_props hf hsplitL_β).2.2.2.symm
  let ML : IntermediateField K L := IntermediateField.map E.val M
  have hrange_sub : Set.range α ⊆ (ML : Set L) := by
    rw [hrange_eq]
    rintro _ ⟨j, rfl⟩
    exact ⟨(βM j : E), (βM j).2, rfl⟩
  have hE_le : E ≤ ML := IntermediateField.adjoin_le_iff.mpr hrange_sub
  ext x
  simp only [IntermediateField.mem_top, iff_true]
  obtain ⟨y, hyM, hyval⟩ := hE_le x.2
  have hxy : y = x := Subtype.ext hyval
  exact hxy ▸ hyM

/-- **Theorem 7.1 (non-zero leading scalar form)** (§7.1, printed p. 60):
Equivalent guard `hc : c ≠ 0` on `f = c(x - α₁)⋯(x - α_n)`. -/
theorem theorem_7_1_nonzero_coeff {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : K[X]} {n : ℕ} {c : K} (hc : c ≠ 0) {α : Fin n → L}
    (hsplit : GarlingSplitsExplicit K L f n c α) :
    IsGarlingSplittingFieldExtension K (IntermediateField.adjoin K (Set.range α)) f := by
  have hf : f ≠ 0 := by
    intro hf0
    have h0 : f.map (algebraMap K L) = 0 := by simp [hf0]
    rw [hsplit] at h0
    have hcL : algebraMap K L c ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hc
    have hprod0 : (∏ j : Fin n, (Polynomial.X - Polynomial.C (α j))) ≠ 0 :=
      (Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C (α j)).ne_zero
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hcL) hprod0 h0
  exact theorem_7_1 hf hsplit

/-- **Theorem 7.1 (`iff` characterization across all `f ∈ K[X]`, including `f = 0`)**:
Under `GarlingSplitsExplicit K L f n c α`, `K(α₁, …, α_n)` is a splitting field for `f` over `K`
if and only if `f ≠ 0` or every `α_j` already belongs to the base field `K`. -/
theorem theorem_7_1_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : K[X]} {n : ℕ} {c : K} {α : Fin n → L}
    (hsplit : GarlingSplitsExplicit K L f n c α) :
    IsGarlingSplittingFieldExtension K (IntermediateField.adjoin K (Set.range α)) f ↔
      (f ≠ 0 ∨ ∀ j : Fin n, α j ∈ (⊥ : IntermediateField K L)) := by
  by_cases hf : f = 0
  · subst hf
    simp only [ne_eq, not_true_eq_false, false_or, isGarlingSplittingFieldExtension_zero_iff]
    constructor
    · intro hbot_top j
      have hmemE :
          (⟨α j, IntermediateField.subset_adjoin K (Set.range α) ⟨j, rfl⟩⟩ :
            IntermediateField.adjoin K (Set.range α)) ∈
          (⊥ : IntermediateField K (IntermediateField.adjoin K (Set.range α))) := by
        rw [hbot_top]
        exact IntermediateField.mem_top
      rw [IntermediateField.mem_bot] at hmemE
      obtain ⟨k, hk⟩ := hmemE
      rw [IntermediateField.mem_bot]
      exact ⟨k, congrArg Subtype.val hk⟩
    · intro hall
      have hadj_bot : IntermediateField.adjoin K (Set.range α) = ⊥ := by
        apply le_antisymm
        · rw [IntermediateField.adjoin_le_iff]
          rintro _ ⟨j, rfl⟩
          exact hall j
        · exact bot_le
      ext x
      simp only [IntermediateField.mem_top, iff_true]
      have hx : (x : L) ∈ (⊥ : IntermediateField K L) := hadj_bot ▸ x.2
      rw [IntermediateField.mem_bot] at hx ⊢
      obtain ⟨k, hk⟩ := hx
      exact ⟨k, Subtype.ext hk⟩
  · exact ⟨fun _ => Or.inl hf, fun _ => theorem_7_1 hf hsplit⟩

/-- Exact bridge: `IsGarlingSplittingFieldExtension K L f` agrees with Mathlib's
`Polynomial.IsSplittingField K L f` for **every** `f ∈ K[X]` (including `f = 0` and constants). -/
theorem isGarlingSplittingFieldExtension_iff (K L : Type*) [Field K] [Field L] [Algebra K L]
    (f : K[X]) :
    IsGarlingSplittingFieldExtension K L f ↔ Polynomial.IsSplittingField K L f := by
  by_cases hf : f = 0
  · subst hf
    rw [isGarlingSplittingFieldExtension_zero_iff]
    constructor
    · intro hbot_top
      refine ⟨by simp, ?_⟩
      rw [Polynomial.rootSet_zero, Algebra.adjoin_empty]
      ext x
      simp only [Algebra.mem_top, iff_true, Algebra.mem_bot]
      have hx : x ∈ (⊥ : IntermediateField K L) := hbot_top ▸ IntermediateField.mem_top
      rwa [IntermediateField.mem_bot] at hx
    · intro hsf
      have hadj := hsf.adjoin_rootSet
      rw [Polynomial.rootSet_zero, Algebra.adjoin_empty] at hadj
      ext x
      simp only [IntermediateField.mem_top, iff_true, IntermediateField.mem_bot]
      have hx : x ∈ (⊥ : Subalgebra K L) := hadj ▸ Algebra.mem_top
      rwa [Algebra.mem_bot] at hx
  · constructor
    · rintro ⟨hsplit, hmin⟩
      obtain ⟨n, c, α, hexp⟩ := hsplit
      have hroots : Set.range α = f.rootSet L := (garlingSplitsExplicit_props hf hexp).2.2.2
      let M : IntermediateField K L := IntermediateField.adjoin K (Set.range α)
      have hM_split : GarlingSplitsOver K M f :=
        (garlingSplitsOver_intermediateField_iff M f).mpr
          ⟨n, c, α, fun j => IntermediateField.subset_adjoin K (Set.range α) ⟨j, rfl⟩, hexp⟩
      have hM_top : M = ⊤ := by
        by_contra hne
        exact hmin M hne hM_split
      have halg : ∀ x ∈ f.rootSet L, IsAlgebraic K x := by
        intro x hx
        rw [Polynomial.mem_rootSet] at hx
        exact ⟨f, hx.1, hx.2⟩
      have hsubalg :
          (IntermediateField.adjoin K (f.rootSet L)).toSubalgebra =
            Algebra.adjoin K (f.rootSet L) :=
        IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg
      refine ⟨(garlingSplitsOver_iff_splits K L f).mp ⟨n, c, α, hexp⟩, ?_⟩
      rw [← hsubalg, ← hroots]
      change M.toSubalgebra = ⊤
      rw [hM_top]
      rfl
    · intro hsf
      have hsplit : GarlingSplitsOver K L f :=
        (garlingSplitsOver_iff_splits K L f).mpr hsf.splits
      obtain ⟨n, c, α, hexp⟩ := hsplit
      have hroots : Set.range α = f.rootSet L := (garlingSplitsExplicit_props hf hexp).2.2.2
      have halg : ∀ x ∈ f.rootSet L, IsAlgebraic K x := by
        intro x hx
        rw [Polynomial.mem_rootSet] at hx
        exact ⟨f, hx.1, hx.2⟩
      have hsubalg :
          (IntermediateField.adjoin K (f.rootSet L)).toSubalgebra =
            Algebra.adjoin K (f.rootSet L) :=
        IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg
      have hadj_top : IntermediateField.adjoin K (Set.range α) = ⊤ := by
        rw [hroots]
        ext x
        change x ∈ (IntermediateField.adjoin K (f.rootSet L)).toSubalgebra ↔ x ∈ (⊤ : Subalgebra K L)
        rw [hsubalg, hsf.adjoin_rootSet]
      have h71 := theorem_7_1 hf hexp
      refine ⟨⟨n, c, α, hexp⟩, fun M hMne hsplitM => hMne ?_⟩
      obtain ⟨m', c'', γ, hγmem, hγexp⟩ :=
        (garlingSplitsOver_intermediateField_iff M f).mp hsplitM
      have hrange_eq : Set.range α = Set.range γ :=
        (garlingSplitsExplicit_props hf hexp).2.2.2.trans
          (garlingSplitsExplicit_props hf hγexp).2.2.2.symm
      have hle : IntermediateField.adjoin K (Set.range α) ≤ M := by
        rw [IntermediateField.adjoin_le_iff, hrange_eq]
        rintro _ ⟨j, rfl⟩
        exact hγmem j
      exact top_unique (hadj_top ▸ hle)

/-- Helper: `aeval α p` lies in `IntermediateField.adjoin K {α}` for every `p ∈ K[X]`. -/
private theorem aeval_mem_intermediateField_adjoin_singleton {K L : Type*} [Field K] [Field L]
    [Algebra K L] (α : L) (p : K[X]) :
    Polynomial.aeval α p ∈ IntermediateField.adjoin K ({α} : Set L) := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ ih₁ ih₂ =>
    rw [map_add]
    exact (IntermediateField.adjoin K ({α} : Set L)).add_mem ih₁ ih₂
  | monomial m a =>
    rw [Polynomial.aeval_monomial]
    exact (IntermediateField.adjoin K ({α} : Set L)).mul_mem
      ((IntermediateField.adjoin K ({α} : Set L)).algebraMap_mem a)
      (pow_mem (IntermediateField.mem_adjoin_simple_self K α) m)

/-- **Corollary [to Theorem 7.1]** (§7.1, printed p. 60 / PDF p. 68):
*"If `L : K` is a splitting field extension for `f ∈ K[x]` then `L : K` is a finite algebraic
extension."*
Holds literally as printed for **every** `f ∈ K[X]` (including `f = 0` and degree-`0` constants). -/
theorem corollary_to_theorem_7_1 {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hsf : IsGarlingSplittingFieldExtension K L f) :
    IsFiniteExtension K L ∧ IsAlgebraicExtension K L := by
  have hsf' : Polynomial.IsSplittingField K L f :=
    (isGarlingSplittingFieldExtension_iff K L f).mp hsf
  by_cases hf : f = 0
  · subst hf
    have hbot_top : (⊥ : IntermediateField K L) = ⊤ :=
      (isGarlingSplittingFieldExtension_zero_iff K L).mp hsf
    let α0 : Fin 0 → L := Fin.elim0
    have hadj0 : IntermediateField.adjoin K (Set.range α0) = ⊤ := by
      rw [Set.range_eq_empty α0, IntermediateField.adjoin_empty]
      exact hbot_top
    have halg_gen : ∀ i : Fin 0, IsGarlingAlgebraic K (α0 i) := fun i => Fin.elim0 i
    have hfin : IsFiniteExtension K L :=
      (theorem_4_6 K L).2.2.mpr ⟨0, α0, halg_gen, hadj0⟩
    exact ⟨hfin, ((theorem_4_6 K L).1.mp hfin).1⟩
  · obtain ⟨n, c, α, hexp⟩ := hsf.1
    have hroots : Set.range α = f.rootSet L := (garlingSplitsExplicit_props hf hexp).2.2.2
    have halg_set : ∀ x ∈ f.rootSet L, IsAlgebraic K x := by
      intro x hx
      rw [Polynomial.mem_rootSet] at hx
      exact ⟨f, hx.1, hx.2⟩
    have hadj_top : IntermediateField.adjoin K (Set.range α) = ⊤ := by
      rw [hroots]
      ext x
      change x ∈ (IntermediateField.adjoin K (f.rootSet L)).toSubalgebra ↔ x ∈ (⊤ : Subalgebra K L)
      rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg_set, hsf'.adjoin_rootSet]
    have halg_α : ∀ j : Fin n, IsGarlingAlgebraic K (α j) := by
      intro j
      have hj : α j ∈ f.rootSet L := hroots ▸ ⟨j, rfl⟩
      rw [Polynomial.mem_rootSet] at hj
      exact ⟨f, hj.1, hj.2⟩
    have hfin : IsFiniteExtension K L :=
      (theorem_4_6 K L).2.2.mpr ⟨n, α, halg_α, hadj_top⟩
    have halg : IsAlgebraicExtension K L :=
      ((theorem_4_6 K L).1.mp hfin).1
    exact ⟨hfin, halg⟩

/-- Explicit quotient construction `L = K[X] ⧸ (f)` of **Theorem 7.2** (§7.1, printed pp. 60–61 /
PDF pp. 68–69), directly formalizing Garling's commutative triangle `i = q ∘ j : K → K[X] → L` and
`α = q(X) = X + (f)`. -/
theorem theorem_7_2_quotient {K : Type*} [Field K] {f : K[X]} (hirr : Irreducible f) :
    letI : (Ideal.span {f}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hirr
    letI : Field (K[X] ⧸ Ideal.span {f}) := Ideal.Quotient.field (Ideal.span {f})
    let q : K[X] →+* (K[X] ⧸ Ideal.span {f}) := Ideal.Quotient.mk (Ideal.span {f})
    let j : K →+* K[X] := Polynomial.C
    let i : K →+* (K[X] ⧸ Ideal.span {f}) := q.comp j
    let α : K[X] ⧸ Ideal.span {f} := q Polynomial.X
    IsRingMonomorphism i ∧
    IsSimpleExtension K (K[X] ⧸ Ideal.span {f}) ∧
    IsAlgebraicExtension K (K[X] ⧸ Ideal.span {f}) ∧
    IntermediateField.adjoin K ({α} : Set (K[X] ⧸ Ideal.span {f})) = ⊤ ∧
    extDegree K (K[X] ⧸ Ideal.span {f}) = (garlingDegree f hirr.ne_zero : ℕ∞) ∧
    Polynomial.aeval α f = 0 := by
  have _ : (Ideal.span {f}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hirr
  let _ : Field (K[X] ⧸ Ideal.span {f}) := Ideal.Quotient.field (Ideal.span {f})
  let q : K[X] →+* (K[X] ⧸ Ideal.span {f}) := Ideal.Quotient.mk (Ideal.span {f})
  let j : K →+* K[X] := Polynomial.C
  let i : K →+* (K[X] ⧸ Ideal.span {f}) := q.comp j
  let α : K[X] ⧸ Ideal.span {f} := q Polynomial.X
  have hi_mono : IsRingMonomorphism i := i.injective
  have haeval_eq_q : ∀ p : K[X], Polynomial.aeval α p = q p := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p₁ p₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
    | monomial m a =>
      rw [Polynomial.aeval_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      rfl
  have hfα : Polynomial.aeval α f = 0 := by
    rw [haeval_eq_q]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
  have hadj_top : IntermediateField.adjoin K ({α} : Set (K[X] ⧸ Ideal.span {f})) = ⊤ := by
    ext z
    simp only [IntermediateField.mem_top, iff_true]
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    change q p ∈ IntermediateField.adjoin K ({α} : Set (K[X] ⧸ Ideal.span {f}))
    rw [← haeval_eq_q p]
    exact aeval_mem_intermediateField_adjoin_singleton α p
  have hα_alg : IsGarlingAlgebraic K α := ⟨f, hirr.ne_zero, hfα⟩
  have hα_int : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp hα_alg
  have hm_dvd : minpoly K α ∣ f := minpoly.dvd K α hfα
  have hm_irr : Irreducible (minpoly K α) := minpoly.irreducible hα_int
  have hass : Associated (minpoly K α) f := hm_irr.associated_of_dvd hirr hm_dvd
  have hdeg_min : (minpoly K α).natDegree = garlingDegree f hirr.ne_zero :=
    natDegree_eq_of_associated hm_irr.ne_zero hirr.ne_zero hass
  have hfin : IsFiniteExtension K (K[X] ⧸ Ideal.span {f}) :=
    (theorem_4_6 K (K[X] ⧸ Ideal.span {f})).2.2.mpr
      ⟨1, fun _ => α, fun _ => hα_alg, by simpa using hadj_top⟩
  have halg_ext : IsAlgebraicExtension K (K[X] ⧸ Ideal.span {f}) :=
    ((theorem_4_6 K (K[X] ⧸ Ideal.span {f})).1.mp hfin).1
  have hext_deg : extDegree K (K[X] ⧸ Ideal.span {f}) = (garlingDegree f hirr.ne_zero : ℕ∞) := by
    have htop_equiv :
        IntermediateField.adjoin K ({α} : Set (K[X] ⧸ Ideal.span {f})) ≃ₐ[K]
          (K[X] ⧸ Ideal.span {f}) :=
      (IntermediateField.equivOfEq hadj_top).trans IntermediateField.topEquiv
    have hfinrank_eq :
        Module.finrank K (IntermediateField.adjoin K ({α} : Set (K[X] ⧸ Ideal.span {f}))) =
          Module.finrank K (K[X] ⧸ Ideal.span {f}) :=
      LinearEquiv.finrank_eq htop_equiv.toLinearEquiv
    have : Module.Finite K (K[X] ⧸ Ideal.span {f}) :=
      (isFiniteExtension_iff_moduleFinite K _).mp hfin
    rw [extDegree_eq_finrank K (K[X] ⧸ Ideal.span {f}), ← hfinrank_eq,
      IntermediateField.adjoin.finrank hα_int, hdeg_min]
  exact ⟨hi_mono, ⟨α, hadj_top⟩, halg_ext, hadj_top, hext_deg, hfα⟩

/-- **Theorem 7.2** (§7.1, printed p. 60 / PDF p. 68; proof pp. 60–61):
*"Suppose that `f ∈ K[x]` is irreducible of degree `n`. Then there is a simple algebraic extension
`K(α) : K` such that `[K(α) : K] = n` and `f(α) = 0`."* -/
theorem theorem_7_2 {K : Type u} [Field K] {f : K[X]} (hirr : Irreducible f) {n : ℕ}
    (hn : garlingDegree f hirr.ne_zero = n) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (α : L),
      IsSimpleExtension K L ∧
      IsAlgebraicExtension K L ∧
      IntermediateField.adjoin K ({α} : Set L) = ⊤ ∧
      extDegree K L = (n : ℕ∞) ∧
      Polynomial.aeval α f = 0 := by
  have _ : (Ideal.span {f}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hirr
  let _ : Field (K[X] ⧸ Ideal.span {f}) := Ideal.Quotient.field (Ideal.span {f})
  obtain ⟨_, hsimple, halg, hadj, hdeg, hfα⟩ := theorem_7_2_quotient hirr
  exact ⟨K[X] ⧸ Ideal.span {f}, inferInstance, inferInstance,
    Ideal.Quotient.mk (Ideal.span {f}) Polynomial.X,
    hsimple, halg, hadj, hn ▸ hdeg, hfα⟩

/-- **Theorem 7.2 (Garling irreducibility predicate)** (§7.1, printed p. 60): -/
theorem theorem_7_2_garling {K : Type u} [Field K] {f : K[X]} (hirr : IsGarlingIrreducible f)
    {n : ℕ} (hn : garlingDegree f hirr.ne_zero = n) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (α : L),
      IsSimpleExtension K L ∧
      IsAlgebraicExtension K L ∧
      IntermediateField.adjoin K ({α} : Set L) = ⊤ ∧
      extDegree K L = (n : ℕ∞) ∧
      Polynomial.aeval α f = 0 :=
  theorem_7_2 ((isGarlingIrreducible_iff f).mp hirr) hn

private theorem splittingField_finrank_dvd_factorial_sameUniv :
    ∀ (n : ℕ) {K L : Type u} [Field K] [Field L] [Algebra K L] {f : K[X]},
      f.natDegree = n → IsGarlingSplittingFieldExtension K L f →
      Module.finrank K L ∣ n.factorial := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro K L _ _ _ f hdeg hsf
    have ⟨hfin, _⟩ := corollary_to_theorem_7_1 hsf
    have : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hfin
    by_cases hf0 : f = 0
    · subst hf0
      simp only [Polynomial.natDegree_zero] at hdeg
      subst hdeg
      have hbot_top : (⊥ : IntermediateField K L) = ⊤ :=
        (isGarlingSplittingFieldExtension_zero_iff K L).mp hsf
      have hequiv : K ≃ₐ[K] L :=
        (IntermediateField.botEquiv K L).symm.trans
          ((IntermediateField.equivOfEq hbot_top).trans IntermediateField.topEquiv)
      have hfr1 : Module.finrank K L = 1 := by
        rw [← LinearEquiv.finrank_eq hequiv.toLinearEquiv, Module.finrank_self]
      rw [hfr1]
      exact one_dvd _
    · by_cases hn1 : n ≤ 1
      · have hbot_splits : GarlingSplitsOver K (⊥ : IntermediateField K L) f := by
          rw [garlingSplitsOver_iff_splits]
          apply Polynomial.Splits.of_natDegree_le_one
          rw [Polynomial.natDegree_map_eq_of_injective
            (algebraMap K (⊥ : IntermediateField K L)).injective]
          omega
        have hbot_top : (⊥ : IntermediateField K L) = ⊤ := by
          by_contra hne
          exact hsf.2 ⊥ hne hbot_splits
        have hequiv : K ≃ₐ[K] L :=
          (IntermediateField.botEquiv K L).symm.trans
            ((IntermediateField.equivOfEq hbot_top).trans IntermediateField.topEquiv)
        have hfr1 : Module.finrank K L = 1 := by
          rw [← LinearEquiv.finrank_eq hequiv.toLinearEquiv, Module.finrank_self]
        rw [hfr1]
        exact one_dvd _
      · push Not at hn1
        by_cases hirr : Irreducible f
        · -- Case 2 (printed p. 62): `f` is irreducible of degree `n ≥ 2`.
          obtain ⟨m, c, α, hexp⟩ := hsf.1
          obtain ⟨_, _, hm_eq, hroots⟩ := garlingSplitsExplicit_props hf0 hexp
          have hm_n : m = n := by simpa [garlingDegree, hdeg] using hm_eq
          have hm_pos : 0 < m := by omega
          let idx0 : Fin m := ⟨0, hm_pos⟩
          let α₀ : L := α idx0
          have hα₀_root : Polynomial.aeval α₀ f = 0 := by
            have hmem : α₀ ∈ f.rootSet L := hroots ▸ ⟨idx0, rfl⟩
            exact (Polynomial.mem_rootSet.mp hmem).2
          have hα₀_int : IsIntegral K α₀ :=
            isAlgebraic_iff_isIntegral.mp ⟨f, hf0, hα₀_root⟩
          let F : IntermediateField K L := IntermediateField.adjoin K ({α₀} : Set L)
          have hF_deg : Module.finrank K F = n := by
            rw [IntermediateField.adjoin.finrank hα₀_int]
            have hm_irr : Irreducible (minpoly K α₀) := minpoly.irreducible hα₀_int
            have hass : Associated (minpoly K α₀) f :=
              hm_irr.associated_of_dvd hirr (minpoly.dvd K α₀ hα₀_root)
            rw [natDegree_eq_of_associated hm_irr.ne_zero hf0 hass, hdeg]
          let α₀F : F := ⟨α₀, IntermediateField.mem_adjoin_simple_self K α₀⟩
          have hfF_root : (f.map (algebraMap K F)).IsRoot α₀F := by
            rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def]
            apply Subtype.ext
            rw [ZeroMemClass.coe_zero]
            change F.val (Polynomial.aeval α₀F f) = 0
            rw [← Polynomial.aeval_algHom_apply]
            exact hα₀_root
          obtain ⟨h, hh⟩ := Polynomial.dvd_iff_isRoot.mpr hfF_root
          have hfF0 : f.map (algebraMap K F) ≠ 0 :=
            (Polynomial.map_ne_zero_iff (algebraMap K F).injective).mpr hf0
          have hh0 : h ≠ 0 := fun h0 => hfF0 (by rw [hh, h0, mul_zero])
          have hh_deg : h.natDegree = n - 1 := by
            have h1 := congrArg Polynomial.natDegree hh
            rw [Polynomial.natDegree_map_eq_of_injective (algebraMap K F).injective, hdeg,
              Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero α₀F) hh0,
              Polynomial.natDegree_X_sub_C] at h1
            omega
          have hsf_FL : IsGarlingSplittingFieldExtension F L h := by
            rw [isGarlingSplittingFieldExtension_iff]
            have hfL_map :
                (f.map (algebraMap K F)).map (algebraMap F L) = f.map (algebraMap K L) := by
              rw [Polynomial.map_map]
              rfl
            have hhL_eq :
                f.map (algebraMap K L) =
                  (Polynomial.X - Polynomial.C α₀) * h.map (algebraMap F L) := by
              rw [← hfL_map, hh, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
                Polynomial.map_C]
              rfl
            have hfL0 : f.map (algebraMap K L) ≠ 0 :=
              (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf0
            have hh_splits : (h.map (algebraMap F L)).Splits := by
              have hf_splits : (f.map (algebraMap K L)).Splits :=
                (garlingSplitsOver_iff_splits K L f).mp hsf.1
              exact Polynomial.Splits.of_dvd hf_splits hfL0
                ⟨Polynomial.X - Polynomial.C α₀, by rw [hhL_eq, mul_comm]⟩
            refine ⟨hh_splits, ?_⟩
            have hroot_union : f.rootSet L ⊆ insert α₀ (h.rootSet L) := by
              intro x hx
              rw [Polynomial.mem_rootSet] at hx
              have hev : (f.map (algebraMap K L)).eval x = 0 := by
                rw [Polynomial.eval_map, ← Polynomial.aeval_def]
                exact hx.2
              rw [hhL_eq, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
                Polynomial.eval_C, mul_eq_zero, sub_eq_zero] at hev
              rcases hev with rfl | hx_h
              · exact Set.mem_insert α₀ _
              · right
                rw [Polynomial.mem_rootSet]
                refine ⟨hh0, ?_⟩
                rw [Polynomial.aeval_def, ← Polynomial.eval_map]
                exact hx_h
            let AF : Subalgebra F L := Algebra.adjoin F (h.rootSet L)
            have hsub_AF : f.rootSet L ⊆ (AF : Set L) := by
              intro y hy
              rcases hroot_union hy with rfl | hyh
              · exact AF.algebraMap_mem α₀F
              · exact Algebra.subset_adjoin hyh
            have hK_le : Algebra.adjoin K (f.rootSet L) ≤ AF.restrictScalars K :=
              Algebra.adjoin_le hsub_AF
            have hsfK : Polynomial.IsSplittingField K L f :=
              (isGarlingSplittingFieldExtension_iff K L f).mp hsf
            rw [eq_top_iff]
            intro x _
            have hxK : x ∈ Algebra.adjoin K (f.rootSet L) := by
              rw [hsfK.adjoin_rootSet]
              trivial
            exact hK_le hxK
          have hdvd_ih : Module.finrank F L ∣ (n - 1).factorial :=
            ih (n - 1) (by omega) hh_deg hsf_FL
          have htower : Module.finrank K F * Module.finrank F L = Module.finrank K L :=
            Module.finrank_mul_finrank K F L
          rw [← htower, hF_deg, mul_comm]
          have hfac : n.factorial = (n - 1).factorial * n := by
            cases n with
            | zero => omega
            | succ k => simp [Nat.factorial_succ, mul_comm]
          rw [hfac]
          exact mul_dvd_mul_right hdvd_ih n
        · -- Case 1 (printed p. 61): `f` is reducible over `K`, `f = g * h` with `deg g, deg h < n`.
          have hnu : ¬ IsUnit f := by
            intro hu
            have hd0 : f.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
            omega
          rw [irreducible_iff] at hirr
          push Not at hirr
          obtain ⟨g, h, rfl, hgnu, hhnu⟩ := hirr hnu
          have hg0 : g ≠ 0 := left_ne_zero_of_mul hf0
          have hh0 : h ≠ 0 := right_ne_zero_of_mul hf0
          have hg_pos : 0 < g.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
            (Polynomial.degree_pos_of_ne_zero_of_nonunit hg0 hgnu)
          have hh_pos : 0 < h.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
            (Polynomial.degree_pos_of_ne_zero_of_nonunit hh0 hhnu)
          let s := g.natDegree
          let t := h.natDegree
          have hst : s + t = n := by
            rw [← hdeg, Polynomial.natDegree_mul hg0 hh0]
          have hgh_splits : ((g * h).map (algebraMap K L)).Splits :=
            (garlingSplitsOver_iff_splits K L (g * h)).mp hsf.1
          have hghL0 : ((g * h).map (algebraMap K L)) ≠ 0 :=
            (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf0
          have hg_splits : (g.map (algebraMap K L)).Splits :=
            Polynomial.Splits.of_dvd hgh_splits hghL0
              ⟨h.map (algebraMap K L), Polynomial.map_mul _⟩
          have hh_splits : (h.map (algebraMap K L)).Splits :=
            Polynomial.Splits.of_dvd hgh_splits hghL0
              ⟨g.map (algebraMap K L), by rw [Polynomial.map_mul, mul_comm]⟩
          obtain ⟨ng, cg, αg, hexpg⟩ := (garlingSplitsOver_iff_splits K L g).mpr hg_splits
          let M : IntermediateField K L := IntermediateField.adjoin K (Set.range αg)
          have hsf_KM : IsGarlingSplittingFieldExtension K M g := theorem_7_1 hg0 hexpg
          have hdvd_s : Module.finrank K M ∣ s.factorial :=
            ih s (by omega) rfl hsf_KM
          let hM : M[X] := h.map (algebraMap K M)
          have hhM0 : hM ≠ 0 :=
            (Polynomial.map_ne_zero_iff (algebraMap K M).injective).mpr hh0
          have hhM_deg : hM.natDegree = t :=
            Polynomial.natDegree_map_eq_of_injective (algebraMap K M).injective h
          have hsf_ML : IsGarlingSplittingFieldExtension M L hM := by
            rw [isGarlingSplittingFieldExtension_iff]
            have hhM_map : hM.map (algebraMap M L) = h.map (algebraMap K L) := by
              dsimp [hM]
              rw [Polynomial.map_map]
              rfl
            refine ⟨hhM_map ▸ hh_splits, ?_⟩
            have hg_roots : Set.range αg = g.rootSet L :=
              (garlingSplitsExplicit_props hg0 hexpg).2.2.2
            have hhM_roots : hM.rootSet L = h.rootSet L := by
              ext x
              rw [Polynomial.mem_rootSet, Polynomial.mem_rootSet,
                and_iff_right hhM0, and_iff_right hh0,
                Polynomial.aeval_def, ← Polynomial.eval_map, hhM_map, Polynomial.eval_map,
                ← Polynomial.aeval_def]
            have hmul_roots : (g * h).rootSet L ⊆ Set.range αg ∪ hM.rootSet L := by
              intro x hx
              rw [Polynomial.mem_rootSet] at hx
              have hev := hx.2
              rw [map_mul, mul_eq_zero] at hev
              rcases hev with hxg | hxh
              · left
                rw [hg_roots, Polynomial.mem_rootSet]
                exact ⟨hg0, hxg⟩
              · right
                rw [hhM_roots, Polynomial.mem_rootSet]
                exact ⟨hh0, hxh⟩
            let AM : Subalgebra M L := Algebra.adjoin M (hM.rootSet L)
            have hsub_AM : (g * h).rootSet L ⊆ (AM : Set L) := by
              intro y hy
              rcases hmul_roots hy with ⟨j, rfl⟩ | hyh
              · let yM : M := ⟨αg j, IntermediateField.subset_adjoin K (Set.range αg) ⟨j, rfl⟩⟩
                exact AM.algebraMap_mem yM
              · exact Algebra.subset_adjoin hyh
            have hK_le : Algebra.adjoin K ((g * h).rootSet L) ≤ AM.restrictScalars K :=
              Algebra.adjoin_le hsub_AM
            have hsfK : Polynomial.IsSplittingField K L (g * h) :=
              (isGarlingSplittingFieldExtension_iff K L (g * h)).mp hsf
            rw [eq_top_iff]
            intro x _
            have hxK : x ∈ Algebra.adjoin K ((g * h).rootSet L) := by
              rw [hsfK.adjoin_rootSet]
              trivial
            exact hK_le hxK
          have hdvd_t : Module.finrank M L ∣ t.factorial :=
            ih t (by omega) hhM_deg hsf_ML
          have htower : Module.finrank K M * Module.finrank M L = Module.finrank K L :=
            Module.finrank_mul_finrank K M L
          rw [← htower]
          have hdvd_prod : Module.finrank K M * Module.finrank M L ∣ s.factorial * t.factorial :=
            mul_dvd_mul hdvd_s hdvd_t
          have hprod_dvd_n : s.factorial * t.factorial ∣ n.factorial := by
            refine ⟨n.choose s, ?_⟩
            have hchoose := Nat.choose_mul_factorial_mul_factorial (n := n) (k := s) (by omega)
            have hts : n - s = t := by omega
            rw [hts] at hchoose
            linarith
          exact dvd_trans hdvd_prod hprod_dvd_n

/-- **Core divisibility lemma `[L : K] ∣ n!`** (universe-polymorphic over `{K : Type*} {L : Type*}`,
used both for `[L : K] ≤ n!` in `Theorem 7.3` on pp. 61–62 and directly in `Exercise 7.9` on
p. 70): for any field extension `L : K`, any `f ∈ K[X]` with `f.natDegree = n`, and any splitting
field extension `L : K` for `f`, `Module.finrank K L ∣ n.factorial`. -/
theorem splittingField_finrank_dvd_factorial (n : ℕ) {K L : Type*} [Field K] [Field L]
    [Algebra K L] {f : K[X]} (hdeg : f.natDegree = n)
    (hsf : IsGarlingSplittingFieldExtension K L f) :
    Module.finrank K L ∣ n.factorial := by
  let B : IntermediateField K L := ⊥
  let e : K ≃ₐ[K] B := (IntermediateField.botEquiv K L).symm
  let fB : B[X] := f.map e.toRingHom
  have hfB_deg : fB.natDegree = n :=
    (Polynomial.natDegree_map_eq_of_injective e.injective f).trans hdeg
  have hfB_map : fB.map (algebraMap B L) = f.map (algebraMap K L) := by
    dsimp [fB]
    rw [Polynomial.map_map]
    congr 1
  have hsfB : IsGarlingSplittingFieldExtension B L fB := by
    rw [isGarlingSplittingFieldExtension_iff]
    have hsfK : Polynomial.IsSplittingField K L f :=
      (isGarlingSplittingFieldExtension_iff K L f).mp hsf
    refine ⟨hfB_map ▸ hsfK.splits, ?_⟩
    by_cases hf0 : f = 0
    · subst hf0
      have hbot_top : (⊥ : IntermediateField K L) = ⊤ :=
        (isGarlingSplittingFieldExtension_zero_iff K L).mp hsf
      rw [eq_top_iff]
      intro x _
      have hxB : x ∈ B := by
        change x ∈ (⊥ : IntermediateField K L)
        rw [hbot_top]
        exact IntermediateField.mem_top
      exact (Algebra.adjoin B (fB.rootSet L)).algebraMap_mem ⟨x, hxB⟩
    · have hfB0 : fB ≠ 0 := (Polynomial.map_ne_zero_iff e.injective).mpr hf0
      have hroots_eq : f.rootSet L = fB.rootSet L := by
        ext x
        rw [Polynomial.mem_rootSet, Polynomial.mem_rootSet, and_iff_right hf0, and_iff_right hfB0,
          Polynomial.aeval_def, ← Polynomial.eval_map, ← hfB_map, Polynomial.eval_map,
          ← Polynomial.aeval_def]
      let AB : Subalgebra B L := Algebra.adjoin B (fB.rootSet L)
      have hsub : f.rootSet L ⊆ (AB : Set L) := by
        rw [hroots_eq]
        exact Algebra.subset_adjoin
      have hK_le : Algebra.adjoin K (f.rootSet L) ≤ AB.restrictScalars K :=
        Algebra.adjoin_le hsub
      rw [eq_top_iff]
      intro x _
      have hxK : x ∈ Algebra.adjoin K (f.rootSet L) := by
        rw [hsfK.adjoin_rootSet]
        trivial
      exact hK_le hxK
  have hdvdB : Module.finrank B L ∣ n.factorial :=
    splittingField_finrank_dvd_factorial_sameUniv n hfB_deg hsfB
  have hKB : Module.finrank K B = 1 := by
    rw [← LinearEquiv.finrank_eq e.toLinearEquiv, Module.finrank_self]
  have htower : Module.finrank K B * Module.finrank B L = Module.finrank K L :=
    Module.finrank_mul_finrank K B L
  rw [hKB, one_mul] at htower
  rwa [← htower]

/-- **Theorem 7.3** (§7.1, printed p. 61 / PDF p. 69; proof pp. 61–62; see `QUEUE.md`):
For every non-zero polynomial `f ∈ K[X]` of degree `n = garlingDegree f hf`, there exists a
splitting field extension `L : K` for `f` with `[L : K] ≤ n!`. -/
theorem theorem_7_3 {K : Type u} [Field K] {f : K[X]} (hf : f ≠ 0) {n : ℕ}
    (hn : garlingDegree f hf = n) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      IsGarlingSplittingFieldExtension K L f ∧
      extDegree K L ≤ (n.factorial : ℕ∞) := by
  let L : Type u := f.SplittingField
  have hsf : IsGarlingSplittingFieldExtension K L f :=
    (isGarlingSplittingFieldExtension_iff K L f).mpr inferInstance
  have hfin : IsFiniteExtension K L := (corollary_to_theorem_7_1 hsf).1
  have : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hfin
  have hdvd : Module.finrank K L ∣ n.factorial :=
    splittingField_finrank_dvd_factorial n (by simpa [garlingDegree] using hn) hsf
  have hle_nat : Module.finrank K L ≤ n.factorial :=
    Nat.le_of_dvd (Nat.factorial_pos n) hdvd
  refine ⟨L, inferInstance, inferInstance, hsf, ?_⟩
  rw [extDegree_eq_finrank K L]
  exact mod_cast hle_nat

/-- **Theorem 7.3 (unconditional existence & `natDegree!` bound for all `f ∈ K[X]`, incl. `f = 0`)**:
Every polynomial `f ∈ K[X]` (including `f = 0`) possesses a splitting field extension `L : K` with
`extDegree K L ≤ (f.natDegree.factorial : ℕ∞)`. -/
theorem theorem_7_3_natDegree {K : Type u} [Field K] (f : K[X]) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      IsGarlingSplittingFieldExtension K L f ∧
      extDegree K L ≤ (f.natDegree.factorial : ℕ∞) := by
  let L : Type u := f.SplittingField
  have hsf : IsGarlingSplittingFieldExtension K L f :=
    (isGarlingSplittingFieldExtension_iff K L f).mpr inferInstance
  have hfin : IsFiniteExtension K L := (corollary_to_theorem_7_1 hsf).1
  have : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hfin
  have hdvd : Module.finrank K L ∣ f.natDegree.factorial :=
    splittingField_finrank_dvd_factorial f.natDegree rfl hsf
  have hle_nat : Module.finrank K L ≤ f.natDegree.factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) hdvd
  refine ⟨L, inferInstance, inferInstance, hsf, ?_⟩
  rw [extDegree_eq_finrank K L]
  exact mod_cast hle_nat

/-- **Refutation of reading `n` in `Theorem 7.3` as an unbound universally quantified `n : ℕ`**:
For `f = X^2 + 1 ∈ ℝ[X]` and `n = 0`, every splitting field extension `L : ℝ` for `f` has
`extDegree ℝ L = 2 > 0! = 1` (confirming `n` in `Theorem 7.3` must be bound to `degree f` as in
line 1 of Garling's proof on p. 61). -/
theorem theorem_7_3_unbound_n_counterexample :
    let f : ℝ[X] := Polynomial.X ^ 2 + 1
    ∀ (L : Type) [Field L] [Algebra ℝ L],
      IsGarlingSplittingFieldExtension ℝ L f → ¬ (extDegree ℝ L ≤ ((0 : ℕ).factorial : ℕ∞)) := by
  intro f L _ _ hsf hle1
  have h1 : extDegree ℝ L = 1 := le_antisymm (by simpa using hle1) (one_le_extDegree ℝ L)
  have hsurj : Function.Surjective (algebraMap ℝ L) :=
    (extDegree_eq_one_iff_surjective ℝ L).mp h1
  obtain ⟨m, c, α, hexp⟩ := hsf.1
  have hf0 : f ≠ 0 := by
    dsimp [f]
    exact (Polynomial.monic_X_pow_add_C 1 (by norm_num : 2 ≠ 0)).ne_zero
  obtain ⟨_, _, hm, hroots⟩ := garlingSplitsExplicit_props hf0 hexp
  have hm2 : m = 2 := by
    have hd : f.natDegree = 2 := by
      dsimp [f]
      compute_degree!
    simpa [garlingDegree, hd] using hm
  have hmem : α ⟨0, by omega⟩ ∈ f.rootSet L := hroots ▸ ⟨⟨0, by omega⟩, rfl⟩
  rw [Polynomial.mem_rootSet] at hmem
  obtain ⟨r, hr⟩ := hsurj (α ⟨0, by omega⟩)
  have hr_ev : Polynomial.aeval (algebraMap ℝ L r) f = 0 := hr ▸ hmem.2
  rw [Polynomial.aeval_algebraMap_apply, map_eq_zero_iff _ (algebraMap ℝ L).injective] at hr_ev
  have hr2 : r ^ 2 + 1 = 0 := by simpa [f] using hr_ev
  nlinarith [sq_nonneg r]

/-! ### Exercise 7.2 (§7.1, printed p. 62 / PDF p. 70) -/

/-- The polynomial `f = x^3 - x + 1 ∈ ℤ₃[x]` of `Exercise 7.2` (printed p. 62). -/
noncomputable def ex72Poly : (ZMod 3)[X] :=
  Polynomial.X ^ 3 - Polynomial.X + 1

/-- **Exercise 7.2, Part 1** (§7.1, printed p. 62):
`f = x^3 - x + 1` has no roots in `ℤ₃` (`f(0) = f(1) = f(2) = 1`) and is irreducible in `ℤ₃[x]`. -/
theorem exercise_7_2_irreducible :
    (∀ a : ZMod 3, ex72Poly.eval a = 1) ∧
    Irreducible ex72Poly ∧
    IsGarlingIrreducible ex72Poly := by
  have heval : ∀ a : ZMod 3, ex72Poly.eval a = 1 := by
    intro a
    simp only [ex72Poly, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one]
    fin_cases a <;> decide
  have hmonic : ex72Poly.Monic := by
    unfold ex72Poly
    monicity!
  have hdeg : ex72Poly.natDegree = 3 := by
    unfold ex72Poly
    compute_degree!
  have hirr : Irreducible ex72Poly := by
    rw [irreducible_iff]
    refine ⟨?_, ?_⟩
    · intro hu
      have hd := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    · intro g h hgh
      by_contra hboth
      push Not at hboth
      obtain ⟨hgnu, hhnu⟩ := hboth
      have hg0 : g ≠ 0 := fun h0 => hmonic.ne_zero (by rw [hgh, h0, zero_mul])
      have hh0 : h ≠ 0 := fun h0 => hmonic.ne_zero (by rw [hgh, h0, mul_zero])
      have hg_pos : 0 < g.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
        (Polynomial.degree_pos_of_ne_zero_of_nonunit hg0 hgnu)
      have hh_pos : 0 < h.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
        (Polynomial.degree_pos_of_ne_zero_of_nonunit hh0 hhnu)
      have hsum : g.natDegree + h.natDegree = 3 := by
        calc g.natDegree + h.natDegree = (g * h).natDegree := (Polynomial.natDegree_mul hg0 hh0).symm
          _ = ex72Poly.natDegree := by rw [← hgh]
          _ = 3 := hdeg
      have hdeg1 : g.natDegree = 1 ∨ h.natDegree = 1 := by omega
      rcases hdeg1 with hg1 | hh1
      · obtain ⟨r, hr⟩ := Polynomial.exists_root_of_degree_eq_one
          (Polynomial.degree_eq_iff_natDegree_eq hg0 |>.mpr hg1)
        have hfr : ex72Poly.eval r = 0 := by rw [hgh, Polynomial.eval_mul, hr, zero_mul]
        have hfr1 := heval r
        rw [hfr] at hfr1
        exact zero_ne_one hfr1
      · obtain ⟨r, hr⟩ := Polynomial.exists_root_of_degree_eq_one
          (Polynomial.degree_eq_iff_natDegree_eq hh0 |>.mpr hh1)
        have hfr : ex72Poly.eval r = 0 := by rw [hgh, Polynomial.eval_mul, hr, mul_zero]
        have hfr1 := heval r
        rw [hfr] at hfr1
        exact zero_ne_one hfr1
  exact ⟨heval, hirr, (isGarlingIrreducible_iff ex72Poly).mpr hirr⟩

/-- **Exercise 7.2, Part 2** (§7.1, printed p. 62):
If `ζ` is a root of `f = x^3 - x + 1` in any extension `L` of `ℤ₃` (in particular in a splitting
field extension), then `ζ + 1` and `ζ - 1` are also roots of `f`, the three roots `ζ, ζ + 1, ζ - 1`
are pairwise distinct, and `f = (x - ζ)(x - (ζ + 1))(x - (ζ - 1))` over `L`. -/
theorem exercise_7_2_roots {L : Type*} [Field L] [Algebra (ZMod 3) L] {ζ : L}
    (hζ : Polynomial.aeval ζ ex72Poly = 0) :
    Polynomial.aeval (ζ + 1) ex72Poly = 0 ∧
    Polynomial.aeval (ζ - 1) ex72Poly = 0 ∧
    ζ ≠ ζ + 1 ∧ ζ ≠ ζ - 1 ∧ ζ + 1 ≠ ζ - 1 ∧
    ex72Poly.map (algebraMap (ZMod 3) L) =
      (Polynomial.X - Polynomial.C ζ) *
      (Polynomial.X - Polynomial.C (ζ + 1)) *
      (Polynomial.X - Polynomial.C (ζ - 1)) := by
  have hchar3 : (3 : L) = 0 := by
    have h0 : algebraMap (ZMod 3) L (3 : ZMod 3) = 0 := by
      rw [(by decide : (3 : ZMod 3) = 0), map_zero]
    simpa only [map_ofNat] using h0
  have hζ_eq : ζ ^ 3 - ζ + 1 = 0 := by
    simpa only [ex72Poly, map_add, map_sub, map_pow, map_one, Polynomial.aeval_X] using hζ
  have hplus : Polynomial.aeval (ζ + 1) ex72Poly = 0 := by
    simp only [ex72Poly, map_add, map_sub, map_pow, map_one, Polynomial.aeval_X]
    calc (ζ + 1) ^ 3 - (ζ + 1) + 1
        = (ζ ^ 3 - ζ + 1) + (3 : L) * (ζ ^ 2 + ζ) := by ring
      _ = 0 := by rw [hζ_eq, hchar3]; ring
  have hminus : Polynomial.aeval (ζ - 1) ex72Poly = 0 := by
    simp only [ex72Poly, map_add, map_sub, map_pow, map_one, Polynomial.aeval_X]
    calc (ζ - 1) ^ 3 - (ζ - 1) + 1
        = (ζ ^ 3 - ζ + 1) + (3 : L) * (-ζ ^ 2 + ζ) := by ring
      _ = 0 := by rw [hζ_eq, hchar3]; ring
  have hne1 : ζ ≠ ζ + 1 := fun h => by
    have h1 : (1 : L) = 0 := by linear_combination h.symm
    exact one_ne_zero h1
  have hne2 : ζ ≠ ζ - 1 := fun h => by
    have h1 : (0 : L) = -1 := by
      calc (0 : L) = ζ - ζ := (sub_self ζ).symm
        _ = (ζ - 1) - ζ := by nth_rw 1 [h]
        _ = -1 := by ring
    exact one_ne_zero (neg_eq_zero.mp h1.symm)
  have hne3 : ζ + 1 ≠ ζ - 1 := fun h => by
    have h2 : (2 : L) = 0 := by
      calc (2 : L) = (ζ + 1) - (ζ - 1) := by ring
        _ = 0 := sub_eq_zero.mpr h
    have h1 : (1 : L) = 0 := by
      calc (1 : L) = (3 : L) - (2 : L) := by norm_num
        _ = 0 := by rw [hchar3, h2, sub_self]
    exact one_ne_zero h1
  have hfac :
      ex72Poly.map (algebraMap (ZMod 3) L) =
        (Polynomial.X - Polynomial.C ζ) *
        (Polynomial.X - Polynomial.C (ζ + 1)) *
        (Polynomial.X - Polynomial.C (ζ - 1)) := by
    have hmap : ex72Poly.map (algebraMap (ZMod 3) L) = Polynomial.X ^ 3 - Polynomial.X + 1 := by
      simp [ex72Poly]
    rw [hmap]
    have h3C : (3 : L[X]) = 0 := by
      rw [← map_ofNat Polynomial.C 3, hchar3, map_zero]
    have hζC : Polynomial.C ζ ^ 3 - Polynomial.C ζ + 1 = (0 : L[X]) := by
      have h0 := congrArg Polynomial.C hζ_eq
      simpa only [map_add, map_sub, map_pow, map_one, map_zero] using h0
    calc (Polynomial.X ^ 3 - Polynomial.X + 1 : L[X])
        = (Polynomial.X - Polynomial.C ζ) *
            (Polynomial.X - Polynomial.C (ζ + 1)) *
            (Polynomial.X - Polynomial.C (ζ - 1)) +
          (3 : L[X]) * Polynomial.C ζ * Polynomial.X ^ 2 -
          (3 : L[X]) * Polynomial.C ζ ^ 2 * Polynomial.X +
          (Polynomial.C ζ ^ 3 - Polynomial.C ζ + 1) := by
            simp only [map_add, map_sub, map_one]
            ring
      _ = (Polynomial.X - Polynomial.C ζ) *
            (Polynomial.X - Polynomial.C (ζ + 1)) *
            (Polynomial.X - Polynomial.C (ζ - 1)) := by
            rw [h3C, hζC]; ring
  exact ⟨hplus, hminus, hne1, hne2, hne3, hfac⟩

/-- Carrier of the explicit 27-element splitting field `𝔽₂₇ = ℤ₃(ζ)` for `x^3 - x + 1` in
`Exercise 7.2` (printed p. 62), representing `a + b ζ + c ζ²` (`ζ³ = ζ - 1`) as triples
`(a, b, c) ∈ ℤ₃³`. -/
abbrev Ex72Elem : Type := ZMod 3 × ZMod 3 × ZMod 3

/-- Computable multiplication law (`27 × 27` multiplication table) on `Ex72Elem = ℤ₃³` in the basis
`{1, ζ, ζ²}` where `ζ³ = ζ - 1` (`ζ⁴ = ζ² - ζ`):
`(a₁ + b₁ζ + c₁ζ²)(a₂ + b₂ζ + c₂ζ²) = (a₁a₂ - b₁c₂ - c₁b₂) + (a₁b₂ + b₁a₂ + b₁c₂ + c₁b₂ - c₁c₂)ζ + (a₁c₂ + b₁b₂ + c₁a₂ + c₁c₂)ζ²`. -/
def ex72MulTable (u v : Ex72Elem) : Ex72Elem :=
  let (a₁, b₁, c₁) := u
  let (a₂, b₂, c₂) := v
  (a₁ * a₂ - b₁ * c₂ - c₁ * b₂,
   a₁ * b₂ + b₁ * a₂ + b₁ * c₂ + c₁ * b₂ - c₁ * c₂,
   a₁ * c₂ + b₁ * b₂ + c₁ * a₂ + c₁ * c₂)

/-- Explicit `27 × 27` multiplication matrix indexed by `Ex72Elem` (`Exercise 7.2`, p. 62). -/
def ex72MulMatrix : Matrix Ex72Elem Ex72Elem Ex72Elem :=
  Matrix.of ex72MulTable

/-- Canonical quotient splitting field `ℤ₃[x] ⧸ (x^3 - x + 1) = AdjoinRoot ex72Poly` for
`Exercise 7.2`. -/
abbrev Ex72Field : Type := AdjoinRoot ex72Poly

instance ex72PolyFactIrreducible : Fact (Irreducible ex72Poly) :=
  ⟨exercise_7_2_irreducible.2.1⟩

/-- Coordinate evaluation map `(a, b, c) ↦ a + b ζ + c ζ²` from `Ex72Elem` onto `Ex72Field`. -/
noncomputable def ex72FromCoords (u : Ex72Elem) : Ex72Field :=
  let ζ : Ex72Field := AdjoinRoot.root ex72Poly
  algebraMap (ZMod 3) Ex72Field u.1 +
    algebraMap (ZMod 3) Ex72Field u.2.1 * ζ +
    algebraMap (ZMod 3) Ex72Field u.2.2 * ζ ^ 2

/-- **Exercise 7.2** (§7.1, printed p. 62 / PDF p. 70; see `QUEUE.md`):
Complete proof of all parts of `Exercise 7.2`:
1. `f = x^3 - x + 1` is irreducible in `ℤ₃[x]`;
2. for any root `ζ` of `f` in any extension of `ℤ₃`, `ζ + 1` and `ζ - 1` are also roots;
3. `Ex72Field = ℤ₃[x] ⧸ (x^3 - x + 1)` is a 27-element splitting field extension for `f` over `ℤ₃`
   of degree `3`, and `ex72FromCoords : Ex72Elem → Ex72Field` is a bijection under which field
   multiplication is given on all `27 × 27 = 729` pairs by the explicit multiplication table
   `ex72MulTable` (`ex72MulMatrix`). -/
theorem exercise_7_2 :
    Irreducible ex72Poly ∧
    IsGarlingIrreducible ex72Poly ∧
    (∀ (L : Type) [Field L] [Algebra (ZMod 3) L] (ζ : L),
      Polynomial.aeval ζ ex72Poly = 0 →
      Polynomial.aeval (ζ + 1) ex72Poly = 0 ∧ Polynomial.aeval (ζ - 1) ex72Poly = 0) ∧
    IsGarlingSplittingFieldExtension (ZMod 3) Ex72Field ex72Poly ∧
    extDegree (ZMod 3) Ex72Field = 3 ∧
    Function.Bijective ex72FromCoords ∧
    Fintype.card Ex72Elem = 27 ∧
    (∀ u v : Ex72Elem,
      ex72FromCoords (ex72MulMatrix u v) = ex72FromCoords u * ex72FromCoords v) := by
  obtain ⟨_, hirr, hgirr⟩ := exercise_7_2_irreducible
  let ζ : Ex72Field := AdjoinRoot.root ex72Poly
  have hζ_root : Polynomial.aeval ζ ex72Poly = 0 :=
    (AdjoinRoot.aeval_eq ex72Poly).trans AdjoinRoot.mk_self
  obtain ⟨hplus, hminus, _, _, _, hfac⟩ := exercise_7_2_roots hζ_root
  have hadj_ζ : IntermediateField.adjoin (ZMod 3) ({ζ} : Set Ex72Field) = ⊤ := by
    ext z
    simp only [IntermediateField.mem_top, iff_true]
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    rw [← AdjoinRoot.aeval_eq]
    exact aeval_mem_intermediateField_adjoin_singleton ζ p
  have hsf : IsGarlingSplittingFieldExtension (ZMod 3) Ex72Field ex72Poly := by
    let α : Fin 3 → Ex72Field := ![ζ, ζ + 1, ζ - 1]
    have hexp : GarlingSplitsExplicit (ZMod 3) Ex72Field ex72Poly 3 1 α := by
      unfold GarlingSplitsExplicit
      rw [hfac, Fin.prod_univ_three]
      simp [α, mul_assoc]
    have h71 := theorem_7_1 hirr.ne_zero hexp
    have hadj_top : IntermediateField.adjoin (ZMod 3) (Set.range α) = ⊤ := by
      apply top_unique
      rw [← hadj_ζ, IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact IntermediateField.subset_adjoin (ZMod 3) (Set.range α) ⟨0, rfl⟩
    rw [isGarlingSplittingFieldExtension_iff] at h71 ⊢
    refine ⟨(garlingSplitsOver_iff_splits _ _ _).mp ⟨3, 1, α, hexp⟩, ?_⟩
    have hroots : Set.range α = ex72Poly.rootSet Ex72Field :=
      (garlingSplitsExplicit_props hirr.ne_zero hexp).2.2.2
    have halg : ∀ x ∈ ex72Poly.rootSet Ex72Field, IsAlgebraic (ZMod 3) x := fun x hx =>
      ⟨ex72Poly, (Polynomial.mem_rootSet.mp hx).1, (Polynomial.mem_rootSet.mp hx).2⟩
    ext x
    change x ∈ Algebra.adjoin (ZMod 3) (ex72Poly.rootSet Ex72Field) ↔ x ∈ (⊤ : Subalgebra (ZMod 3) Ex72Field)
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, ← hroots]
    change x ∈ (IntermediateField.adjoin (ZMod 3) (Set.range α)).toSubalgebra ↔ _
    rw [hadj_top]
    rfl
  have hdeg3 : extDegree (ZMod 3) Ex72Field = 3 := by
    have hζ_int : IsIntegral (ZMod 3) ζ :=
      isAlgebraic_iff_isIntegral.mp ⟨ex72Poly, hirr.ne_zero, hζ_root⟩
    have hmonic : ex72Poly.Monic := by unfold ex72Poly; monicity!
    have hmin : minpoly (ZMod 3) ζ = ex72Poly :=
      (minpoly.eq_of_irreducible_of_monic hirr hζ_root hmonic).symm
    have hfin : IsFiniteExtension (ZMod 3) Ex72Field := (corollary_to_theorem_7_1 hsf).1
    have : Module.Finite (ZMod 3) Ex72Field := (isFiniteExtension_iff_moduleFinite _ _).mp hfin
    rw [extDegree_eq_finrank (ZMod 3) Ex72Field]
    have hequiv :
        IntermediateField.adjoin (ZMod 3) ({ζ} : Set Ex72Field) ≃ₐ[ZMod 3] Ex72Field :=
      (IntermediateField.equivOfEq hadj_ζ).trans IntermediateField.topEquiv
    rw [← LinearEquiv.finrank_eq hequiv.toLinearEquiv, IntermediateField.adjoin.finrank hζ_int,
      hmin]
    have hd : ex72Poly.natDegree = 3 := by unfold ex72Poly; compute_degree!
    exact mod_cast hd
  have hpb_deg : ex72Poly.natDegree = 3 := by unfold ex72Poly; compute_degree!
  let pb : PowerBasis (ZMod 3) Ex72Field := AdjoinRoot.powerBasis hirr.ne_zero
  have hpb_dim : pb.dim = 3 := by simpa [pb, AdjoinRoot.powerBasis_dim] using hpb_deg
  have hpb_gen : pb.gen = ζ := rfl
  have hbij : Function.Bijective ex72FromCoords := by
    let coordEquiv : Ex72Elem ≃ (Fin 3 → ZMod 3) :=
      { toFun := fun u => ![u.1, u.2.1, u.2.2]
        invFun := fun g => (g 0, g 1, g 2)
        left_inv := fun ⟨a, b, c⟩ => by simp
        right_inv := fun g => by ext i; fin_cases i <;> simp }
    let idxEquiv : (Fin 3 → ZMod 3) ≃ (Fin pb.dim → ZMod 3) :=
      Equiv.arrowCongr (finCongr hpb_dim.symm) (Equiv.refl _)
    let fullEquiv : Ex72Elem ≃ Ex72Field :=
      (coordEquiv.trans idxEquiv).trans pb.basis.equivFun.symm.toEquiv
    have heq : (fullEquiv : Ex72Elem → Ex72Field) = ex72FromCoords := by
      ext ⟨a, b, c⟩
      change pb.basis.equivFun.symm (idxEquiv (coordEquiv (a, b, c))) =
        ex72FromCoords (a, b, c)
      rw [Module.Basis.equivFun_symm_apply]
      let e : Fin 3 ≃ Fin pb.dim := finCongr hpb_dim.symm
      rw [← e.sum_comp]
      simp [Fin.sum_univ_three, e, idxEquiv, coordEquiv, PowerBasis.coe_basis, hpb_gen, ζ,
        ex72FromCoords, Algebra.smul_def, add_assoc]
    exact heq ▸ fullEquiv.bijective
  have hcard27 : Fintype.card Ex72Elem = 27 := by decide
  have hζ3 : ζ ^ 3 = ζ - 1 := by
    have h0 : ζ ^ 3 - ζ + 1 = 0 := by
      simpa only [ex72Poly, map_add, map_sub, map_pow, map_one, Polynomial.aeval_X] using hζ_root
    linear_combination h0
  have hζ4 : ζ ^ 4 = ζ ^ 2 - ζ := by
    calc ζ ^ 4 = ζ * ζ ^ 3 := by ring
      _ = ζ * (ζ - 1) := by rw [hζ3]
      _ = ζ ^ 2 - ζ := by ring
  have hmul :
      ∀ u v : Ex72Elem,
        ex72FromCoords (ex72MulMatrix u v) = ex72FromCoords u * ex72FromCoords v := by
    intro ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩
    simp only [ex72MulMatrix, Matrix.of_apply, ex72MulTable, ex72FromCoords, map_add, map_sub,
      map_mul]
    set A₁ : Ex72Field := algebraMap (ZMod 3) Ex72Field a₁
    set B₁ : Ex72Field := algebraMap (ZMod 3) Ex72Field b₁
    set C₁ : Ex72Field := algebraMap (ZMod 3) Ex72Field c₁
    set A₂ : Ex72Field := algebraMap (ZMod 3) Ex72Field a₂
    set B₂ : Ex72Field := algebraMap (ZMod 3) Ex72Field b₂
    set C₂ : Ex72Field := algebraMap (ZMod 3) Ex72Field c₂
    calc (A₁ * A₂ - B₁ * C₂ - C₁ * B₂) +
            (A₁ * B₂ + B₁ * A₂ + B₁ * C₂ + C₁ * B₂ - C₁ * C₂) * ζ +
            (A₁ * C₂ + B₁ * B₂ + C₁ * A₂ + C₁ * C₂) * ζ ^ 2
        = A₁ * A₂ + (A₁ * B₂ + B₁ * A₂) * ζ + (A₁ * C₂ + B₁ * B₂ + C₁ * A₂) * ζ ^ 2 +
            (B₁ * C₂ + C₁ * B₂) * (ζ - 1) + C₁ * C₂ * (ζ ^ 2 - ζ) := by ring
      _ = A₁ * A₂ + (A₁ * B₂ + B₁ * A₂) * ζ + (A₁ * C₂ + B₁ * B₂ + C₁ * A₂) * ζ ^ 2 +
            (B₁ * C₂ + C₁ * B₂) * ζ ^ 3 + C₁ * C₂ * ζ ^ 4 := by rw [← hζ3, ← hζ4]
      _ = (A₁ + B₁ * ζ + C₁ * ζ ^ 2) * (A₂ + B₂ * ζ + C₂ * ζ ^ 2) := by ring
  exact ⟨hirr, hgirr, fun L _ _ ζ₀ hζ₀ => ⟨(exercise_7_2_roots hζ₀).1, (exercise_7_2_roots hζ₀).2.1⟩,
    hsf, hdeg3, hbij, hcard27, hmul⟩

/-! ### Exercise 7.3 (§7.1, printed p. 62 / PDF p. 70) -/

/-- **Counterexample to the omitted `n ≥ 1` case (`n = 0`) of `Exercise 7.3`** (printed p. 62):
Over any field `K`, `X^0 - 1 = 0` splits over `K`, and `K(t) = FractionRing K[X]` is a simple
transcendental extension of `K`, yet:
1. `X^0 - t = 1 - t` is a unit in `K(t)[X]` and therefore **not** irreducible; and
2. for any simple transcendental extension `K(s) : K`, **no** ring homomorphism `i : K(t) →+* K(s)`
   fixes `K` and sends `t ↦ s^0 = 1`. -/
theorem exercise_7_3_zero_counterexample (K : Type*) [Field K] :
    let t : FractionRing K[X] := ratFuncVar K
    GarlingSplitsOver K K (Polynomial.X ^ 0 - 1 : K[X]) ∧
    IsSimpleExtension K (FractionRing K[X]) ∧
    IsGarlingTranscendental K t ∧
    IsUnit (Polynomial.X ^ 0 - Polynomial.C t : (FractionRing K[X])[X]) ∧
    ¬ Irreducible (Polynomial.X ^ 0 - Polynomial.C t : (FractionRing K[X])[X]) ∧
    ¬ ∃ i : FractionRing K[X] →+* FractionRing K[X],
        (∀ k : K, i (algebraMap K (FractionRing K[X]) k) = algebraMap K (FractionRing K[X]) k) ∧
        i t = t ^ 0 := by
  intro t
  have hsplit0 : GarlingSplitsOver K K (Polynomial.X ^ 0 - 1 : K[X]) := by
    have h0 : (Polynomial.X ^ 0 - 1 : K[X]) = 0 := by simp
    rw [h0]
    exact ⟨0, 0, Fin.elim0, by simp [GarlingSplitsExplicit]⟩
  have haeval_t : ∀ p : K[X], Polynomial.aeval t p = algebraMap K[X] (FractionRing K[X]) p := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p₁ p₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂]
    | monomial m a =>
      rw [Polynomial.aeval_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      have hCa : algebraMap K (FractionRing K[X]) a =
          algebraMap K[X] (FractionRing K[X]) (Polynomial.C a) :=
        IsScalarTower.algebraMap_apply K K[X] (FractionRing K[X]) a
      rw [hCa]
      rfl
  have htr : IsGarlingTranscendental K t := by
    rintro ⟨p, hp0, hpt⟩
    have hinj : Function.Injective (algebraMap K[X] (FractionRing K[X])) :=
      IsFractionRing.injective K[X] (FractionRing K[X])
    exact hp0 (hinj (by rw [← haeval_t p, hpt, map_zero]))
  have hadj : IntermediateField.adjoin K ({t} : Set (FractionRing K[X])) = ⊤ := by
    ext z
    simp only [IntermediateField.mem_top, iff_true]
    obtain ⟨num, den, _, rfl⟩ := IsFractionRing.div_surjective (A := K[X]) z
    have hmem : ∀ p : K[X],
        algebraMap K[X] (FractionRing K[X]) p ∈
          IntermediateField.adjoin K ({t} : Set (FractionRing K[X])) := by
      intro p
      rw [← haeval_t p]
      exact aeval_mem_intermediateField_adjoin_singleton t p
    exact (IntermediateField.adjoin K ({t} : Set (FractionRing K[X]))).div_mem
      (hmem num) (hmem den)
  have ht_ne1 : (1 : FractionRing K[X]) - t ≠ 0 := by
    intro h0
    have ht1 : t = 1 := (sub_eq_zero.mp h0).symm
    apply htr
    refine ⟨Polynomial.X - 1, Polynomial.X_sub_C_ne_zero 1, ?_⟩
    simp [ht1]
  have hunit : IsUnit (Polynomial.X ^ 0 - Polynomial.C t : (FractionRing K[X])[X]) := by
    have heq : (Polynomial.X ^ 0 - Polynomial.C t : (FractionRing K[X])[X]) =
        Polynomial.C (1 - t) := by simp [map_sub]
    rw [heq]
    exact (isUnit_iff_ne_zero.mpr ht_ne1).map Polynomial.C
  refine ⟨hsplit0, ⟨t, hadj⟩, htr, hunit, fun hirr => hirr.not_isUnit hunit, ?_⟩
  rintro ⟨i, hfix, hit⟩
  have h1 : i (1 - t) = 0 := by
    rw [map_sub, map_one, hit, pow_zero, sub_self]
  exact ht_ne1 (i.injective (h1.trans i.map_zero.symm))

/-- Unique `K`-algebra isomorphism between any simple transcendental extension `Kt : K` (generated
by a transcendental element `t ∈ Kt`) and `FractionRing K[X]` sending `ratFuncVar K ↦ t`. -/
noncomputable def simpleTranscendentalEquiv {K Kt : Type*} [Field K] [Field Kt] [Algebra K Kt]
    {t : Kt} (ht : IsGarlingTranscendental K t)
    (hadj : IntermediateField.adjoin K ({t} : Set Kt) = ⊤) :
    FractionRing K[X] ≃ₐ[K] Kt := by
  have heval_inj : Function.Injective (Polynomial.aeval t : K[X] →ₐ[K] Kt) :=
    (evalRingHom_injective_iff K t).1.mpr ht
  let liftHom : FractionRing K[X] →ₐ[K] Kt :=
    IsFractionRing.liftAlgHom heval_inj
  have hsurj : Function.Surjective liftHom := by
    intro z
    have hz : z ∈ IntermediateField.adjoin K ({t} : Set Kt) := hadj ▸ IntermediateField.mem_top
    obtain ⟨p, q, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff K z).mp hz
    by_cases hq0 : q = 0
    · subst hq0
      exact ⟨0, by simp⟩
    · refine ⟨algebraMap K[X] (FractionRing K[X]) p / algebraMap K[X] (FractionRing K[X]) q, ?_⟩
      simp [liftHom]
  exact AlgEquiv.ofBijective liftHom ⟨liftHom.toRingHom.injective, hsurj⟩

theorem simpleTranscendentalEquiv_var {K Kt : Type*} [Field K] [Field Kt] [Algebra K Kt]
    {t : Kt} (ht : IsGarlingTranscendental K t)
    (hadj : IntermediateField.adjoin K ({t} : Set Kt) = ⊤) :
    simpleTranscendentalEquiv ht hadj (ratFuncVar K) = t := by
  have heval_inj : Function.Injective (Polynomial.aeval t : K[X] →ₐ[K] Kt) :=
    (evalRingHom_injective_iff K t).1.mpr ht
  change IsFractionRing.liftAlgHom heval_inj (algebraMap K[X] (FractionRing K[X]) Polynomial.X) = t
  simp

/-- **Exercise 7.3** (§7.1, printed p. 62 / PDF p. 70, with explicit `1 ≤ n` guard; see `QUEUE.md`):
Suppose `1 ≤ n`, `K` is a field over which `x^n - 1` splits, and `Kt : K` (with transcendental
generator `t`) and `Ks : K` (with transcendental generator `s`) are simple transcendental
extensions. Then:
1. `x^n - t` is irreducible in `Kt[x]` (by `Exercise 5.4`);
2. there exists a **unique** monomorphism `i : Kt →+* Ks` fixing `K` and sending `t ↦ s^n`; and
3. under the extension `(i, Kt, Ks)` (`letI : Algebra Kt Ks := RingHom.toAlgebra i`), `Ks : Kt` is a
   splitting field extension for `x^n - t` over `Kt` (of degree `n`). -/
theorem exercise_7_3 {K Kt Ks : Type*} [Field K] [Field Kt] [Field Ks]
    [Algebra K Kt] [Algebra K Ks] {n : ℕ} (hn : 1 ≤ n)
    (hsplit1 : GarlingSplitsOver K K (Polynomial.X ^ n - 1))
    {t : Kt} (ht : IsGarlingTranscendental K t)
    (hadj_t : IntermediateField.adjoin K ({t} : Set Kt) = ⊤)
    {s : Ks} (hs : IsGarlingTranscendental K s)
    (hadj_s : IntermediateField.adjoin K ({s} : Set Ks) = ⊤) :
    Irreducible (Polynomial.X ^ n - Polynomial.C t : Kt[X]) ∧
    IsGarlingIrreducible (Polynomial.X ^ n - Polynomial.C t : Kt[X]) ∧
    (∃! i : Kt →+* Ks,
      IsRingMonomorphism i ∧
      (∀ k : K, i (algebraMap K Kt k) = algebraMap K Ks k) ∧
      i t = s ^ n) ∧
    ∃ i : Kt →+* Ks,
      IsRingMonomorphism i ∧
      (∀ k : K, i (algebraMap K Kt k) = algebraMap K Ks k) ∧
      i t = s ^ n ∧
      (letI : Algebra Kt Ks := RingHom.toAlgebra i
       IsGarlingSplittingFieldExtension Kt Ks (Polynomial.X ^ n - Polynomial.C t) ∧
       extDegree Kt Ks = (n : ℕ∞)) := by
  -- 1. Irreducibility of `X^n - t` in `Kt[X]` via `Exercise 5.4`.
  let eKt : FractionRing K[X] ≃ₐ[K] Kt := simpleTranscendentalEquiv ht hadj_t
  have heKt_var : eKt (ratFuncVar K) = t := simpleTranscendentalEquiv_var ht hadj_t
  have hrelPrime : IsRelPrime (Polynomial.X ^ n : K[X]) (1 : K[X]) := isRelPrime_one_right
  have hdeg_pos : 0 < (Polynomial.X ^ n : K[X]).natDegree ∨ 0 < (1 : K[X]).natDegree :=
    Or.inl (by rw [Polynomial.natDegree_X_pow]; omega)
  have hirr_ratFunc :
      Irreducible (linearPencilRatFunc (Polynomial.X ^ n : K[X]) (1 : K[X])) :=
    exercise_5_4_relPrime hrelPrime hdeg_pos
  let mapEquiv : (FractionRing K[X])[X] ≃+* Kt[X] := Polynomial.mapEquiv eKt.toRingEquiv
  have hmap_pencil :
      mapEquiv (linearPencilRatFunc (Polynomial.X ^ n : K[X]) (1 : K[X])) =
        (Polynomial.X ^ n - Polynomial.C t : Kt[X]) := by
    simp [mapEquiv, linearPencilRatFunc, Polynomial.map_sub, Polynomial.map_pow, heKt_var]
  have hirr_Kt : Irreducible (Polynomial.X ^ n - Polynomial.C t : Kt[X]) :=
    hmap_pencil ▸ hirr_ratFunc.map mapEquiv
  have hgirr_Kt : IsGarlingIrreducible (Polynomial.X ^ n - Polynomial.C t : Kt[X]) :=
    (isGarlingIrreducible_iff _).mpr hirr_Kt
  -- 2. Unique `K`-fixing monomorphism `i : Kt →+* Ks` sending `t ↦ s^n`.
  have hsn_tr : IsGarlingTranscendental K (s ^ n) := by
    rintro ⟨p, hp0, hpsn⟩
    let q : K[X] := p.expand K n
    have hq0 : q ≠ 0 := (Polynomial.expand_ne_zero (by omega)).mpr hp0
    have hqs : Polynomial.aeval s q = 0 := by
      dsimp [q]
      rw [Polynomial.expand_aeval]
      exact hpsn
    exact hs ⟨q, hq0, hqs⟩
  have heval_sn_inj : Function.Injective (Polynomial.aeval (s ^ n) : K[X] →ₐ[K] Ks) :=
    (evalRingHom_injective_iff K (s ^ n)).1.mpr hsn_tr
  let lift_sn : FractionRing K[X] →ₐ[K] Ks := IsFractionRing.liftAlgHom heval_sn_inj
  let iAlg : Kt →ₐ[K] Ks := lift_sn.comp eKt.symm.toAlgHom
  let i : Kt →+* Ks := iAlg.toRingHom
  have hi_fix : ∀ k : K, i (algebraMap K Kt k) = algebraMap K Ks k := iAlg.commutes
  have hi_t : i t = s ^ n := by
    have hsymm : eKt.symm t = ratFuncVar K := by
      apply eKt.injective
      simp [heKt_var]
    change lift_sn (eKt.symm t) = s ^ n
    rw [hsymm]
    simp [lift_sn, ratFuncVar]
  have hi_unique :
      ∀ j : Kt →+* Ks,
        (IsRingMonomorphism j ∧
          (∀ k : K, j (algebraMap K Kt k) = algebraMap K Ks k) ∧
          j t = s ^ n) → j = i := by
    rintro j ⟨_, hj_fix, hj_t⟩
    let jAlg : Kt →ₐ[K] Ks := ⟨j, hj_fix⟩
    have haeval_eq : ∀ p : K[X], j (Polynomial.aeval t p) = i (Polynomial.aeval t p) := by
      intro p
      change jAlg (Polynomial.aeval t p) = iAlg (Polynomial.aeval t p)
      rw [← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply]
      have hjt : jAlg t = iAlg t := hj_t.trans hi_t.symm
      rw [hjt]
    ext x
    have hx : x ∈ IntermediateField.adjoin K ({t} : Set Kt) := hadj_t ▸ IntermediateField.mem_top
    obtain ⟨p, q, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff K x).mp hx
    rw [map_div₀, map_div₀, haeval_eq p, haeval_eq q]
  -- 3. `(i, Kt, Ks)` is a splitting field extension for `X^n - t` over `Kt` of degree `n`.
  let _ : Algebra Kt Ks := RingHom.toAlgebra i
  have : IsScalarTower K Kt Ks := IsScalarTower.of_algebraMap_eq fun k => (hi_fix k).symm
  obtain ⟨m, c, ζ, hexp1⟩ := hsplit1
  have hXn1_monic : (Polynomial.X ^ n - 1 : K[X]).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : K) (by omega : n ≠ 0)
  have hXn1_ne0 : (Polynomial.X ^ n - 1 : K[X]) ≠ 0 := hXn1_monic.ne_zero
  obtain ⟨hc1, _, hm_eq, hroots1⟩ := garlingSplitsExplicit_props hXn1_ne0 hexp1
  have hc_one : c = 1 := hc1.trans hXn1_monic.leadingCoeff
  have hm_n : m = n := by
    have hd : (Polynomial.X ^ n - 1 : K[X]).natDegree = n := by
      simpa using (Polynomial.natDegree_X_pow_sub_C (R := K) (n := n) (r := 1))
    simpa [garlingDegree, hd] using hm_eq
  subst hm_n
  have h1_in_range : (1 : K) ∈ Set.range ζ := by
    rw [hroots1, Polynomial.mem_rootSet]
    exact ⟨hXn1_ne0, by simp⟩
  let rootKs : Fin m → Ks := fun j => algebraMap K Ks (ζ j) * s
  have hsplit_Ks :
      GarlingSplitsExplicit Kt Ks (Polynomial.X ^ m - Polynomial.C t) m 1 rootKs := by
    unfold GarlingSplitsExplicit
    have hexpK : (Polynomial.X ^ m - 1 : K[X]) =
        ∏ j : Fin m, (Polynomial.X - Polynomial.C (ζ j)) := by
      have hmap_id := hexp1
      unfold GarlingSplitsExplicit at hmap_id
      simpa [hc_one] using hmap_id
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hs ⟨Polynomial.X, Polynomial.X_ne_zero, by simp⟩
    let scaleHom : Ks[X] →+* Ks[X] :=
      Polynomial.eval₂RingHom Polynomial.C (Polynomial.C s⁻¹ * Polynomial.X)
    have hX_scale : scaleHom Polynomial.X = Polynomial.C s⁻¹ * Polynomial.X := by
      dsimp [scaleHom]
      exact Polynomial.eval₂_X Polynomial.C (Polynomial.C s⁻¹ * Polynomial.X)
    have hC_scale : ∀ a : Ks, scaleHom (Polynomial.C a) = Polynomial.C a := by
      intro a
      dsimp [scaleHom]
      exact Polynomial.eval₂_C Polynomial.C (Polynomial.C s⁻¹ * Polynomial.X)
    have hmap_Ks := congrArg (scaleHom ∘ Polynomial.map (algebraMap K Ks)) hexpK
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one, Polynomial.map_prod, Polynomial.map_C] at hmap_Ks
    have hlhs :
        scaleHom (Polynomial.X ^ m - 1 : Ks[X]) =
          Polynomial.C (s ^ m)⁻¹ * (Polynomial.X ^ m - Polynomial.C (s ^ m)) := by
      rw [map_sub, map_pow, map_one, hX_scale, mul_pow, ← Polynomial.C_pow, inv_pow, mul_sub,
        ← Polynomial.C_mul, inv_mul_cancel₀ (pow_ne_zero m hs0), map_one]
    have hrhs :
        scaleHom (∏ j : Fin m, (Polynomial.X - Polynomial.C (algebraMap K Ks (ζ j)))) =
          Polynomial.C (s ^ m)⁻¹ *
            ∏ j : Fin m, (Polynomial.X - Polynomial.C (rootKs j)) := by
      rw [map_prod]
      have hterm : ∀ j : Fin m,
          scaleHom (Polynomial.X - Polynomial.C (algebraMap K Ks (ζ j))) =
            Polynomial.C s⁻¹ * (Polynomial.X - Polynomial.C (rootKs j)) := by
        intro j
        rw [map_sub, hX_scale, hC_scale, mul_sub, ← Polynomial.C_mul]
        congr 2
        dsimp [rootKs]
        rw [mul_comm (algebraMap K Ks (ζ j)) s, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
      simp_rw [hterm]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Polynomial.C_pow, inv_pow]
    rw [hlhs, hrhs] at hmap_Ks
    have hcancel := mul_left_cancel₀
      (Polynomial.C_ne_zero.mpr (inv_ne_zero (pow_ne_zero m hs0))) hmap_Ks
    have hmap_lhs :
        (Polynomial.X ^ m - Polynomial.C t : Kt[X]).map (algebraMap Kt Ks) =
          Polynomial.X ^ m - Polynomial.C (s ^ m) := by
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
      change Polynomial.X ^ m - Polynomial.C (i t) = _
      rw [hi_t]
    rw [hmap_lhs, hcancel]
    simp
  have hs_in_roots : s ∈ Set.range rootKs := by
    obtain ⟨j0, hj0⟩ := h1_in_range
    exact ⟨j0, by simp [rootKs, hj0]⟩
  have hsf_Ks : IsGarlingSplittingFieldExtension Kt Ks (Polynomial.X ^ m - Polynomial.C t) := by
    have h71 := theorem_7_1 hirr_Kt.ne_zero hsplit_Ks
    have hadj_top_Kt : IntermediateField.adjoin Kt (Set.range rootKs) = ⊤ := by
      ext z
      simp only [IntermediateField.mem_top, iff_true]
      let M_K : IntermediateField K Ks :=
        (IntermediateField.adjoin Kt (Set.range rootKs)).restrictScalars K
      have hs_mem : s ∈ M_K :=
        IntermediateField.subset_adjoin Kt (Set.range rootKs) hs_in_roots
      have hM_K_top : M_K = ⊤ :=
        top_unique (hadj_s ▸ IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hs_mem))
      have hz : z ∈ M_K := hM_K_top ▸ IntermediateField.mem_top
      exact hz
    rw [isGarlingSplittingFieldExtension_iff] at h71 ⊢
    refine ⟨(garlingSplitsOver_iff_splits _ _ _).mp ⟨m, 1, rootKs, hsplit_Ks⟩, ?_⟩
    have hroots_eq : Set.range rootKs = (Polynomial.X ^ m - Polynomial.C t : Kt[X]).rootSet Ks :=
      (garlingSplitsExplicit_props hirr_Kt.ne_zero hsplit_Ks).2.2.2
    have halg : ∀ x ∈ (Polynomial.X ^ m - Polynomial.C t : Kt[X]).rootSet Ks,
        IsAlgebraic Kt x := fun x hx =>
      ⟨_, (Polynomial.mem_rootSet.mp hx).1, (Polynomial.mem_rootSet.mp hx).2⟩
    ext x
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, ← hroots_eq, hadj_top_Kt]
    rfl
  have hext_deg : extDegree Kt Ks = (m : ℕ∞) := by
    have hs_root : Polynomial.aeval s (Polynomial.X ^ m - Polynomial.C t : Kt[X]) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      change s ^ m - i t = 0
      rw [hi_t, sub_self]
    have hs_int : IsIntegral Kt s :=
      isAlgebraic_iff_isIntegral.mp ⟨_, hirr_Kt.ne_zero, hs_root⟩
    have hmonic : (Polynomial.X ^ m - Polynomial.C t : Kt[X]).Monic :=
      Polynomial.monic_X_pow_sub_C t (by omega)
    have hmin : minpoly Kt s = Polynomial.X ^ m - Polynomial.C t :=
      (minpoly.eq_of_irreducible_of_monic hirr_Kt hs_root hmonic).symm
    have hadj_s_Kt : IntermediateField.adjoin Kt ({s} : Set Ks) = ⊤ := by
      ext z
      simp only [IntermediateField.mem_top, iff_true]
      let M_K : IntermediateField K Ks :=
        (IntermediateField.adjoin Kt ({s} : Set Ks)).restrictScalars K
      have hs_mem : s ∈ M_K := IntermediateField.mem_adjoin_simple_self Kt s
      have htop : M_K = ⊤ :=
        top_unique (hadj_s ▸ IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hs_mem))
      have hz : z ∈ M_K := htop ▸ IntermediateField.mem_top
      exact hz
    have hfin : IsFiniteExtension Kt Ks := (corollary_to_theorem_7_1 hsf_Ks).1
    have : Module.Finite Kt Ks := (isFiniteExtension_iff_moduleFinite Kt Ks).mp hfin
    rw [extDegree_eq_finrank Kt Ks]
    have hequiv : IntermediateField.adjoin Kt ({s} : Set Ks) ≃ₐ[Kt] Ks :=
      (IntermediateField.equivOfEq hadj_s_Kt).trans IntermediateField.topEquiv
    rw [← LinearEquiv.finrank_eq hequiv.toLinearEquiv, IntermediateField.adjoin.finrank hs_int,
      hmin, Polynomial.natDegree_X_pow_sub_C]
  exact ⟨hirr_Kt, hgirr_Kt, ⟨i, ⟨i.injective, hi_fix, hi_t⟩, hi_unique⟩,
    ⟨i, i.injective, hi_fix, hi_t, hsf_Ks, hext_deg⟩⟩

/-- **Exercise 7.3 (`iff` characterization across all `n : ℕ`)**:
For any simple transcendental extension `Kt : K` with transcendental generator `t`,
`x^n - t` is irreducible in `Kt[x]` if and only if `1 ≤ n`. -/
theorem exercise_7_3_iff {K Kt : Type*} [Field K] [Field Kt] [Algebra K Kt]
    {t : Kt} (ht : IsGarlingTranscendental K t)
    (hadj_t : IntermediateField.adjoin K ({t} : Set Kt) = ⊤) (n : ℕ) :
    Irreducible (Polynomial.X ^ n - Polynomial.C t : Kt[X]) ↔ 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · constructor
    · intro hirr
      exfalso
      have ht_ne1 : (1 : Kt) - t ≠ 0 := by
        intro h0
        exact ht ⟨Polynomial.X - 1, Polynomial.X_sub_C_ne_zero 1,
          by simp [(sub_eq_zero.mp h0).symm]⟩
      have hunit : IsUnit (Polynomial.X ^ 0 - Polynomial.C t : Kt[X]) := by
        have heq : (Polynomial.X ^ 0 - Polynomial.C t : Kt[X]) = Polynomial.C (1 - t) := by
          simp [map_sub]
        rw [heq]
        exact (isUnit_iff_ne_zero.mpr ht_ne1).map Polynomial.C
      exact hirr.not_isUnit hunit
    · omega
  · refine ⟨fun _ => Nat.succ_le_of_lt hpos, fun _ => ?_⟩
    let eKt : FractionRing K[X] ≃ₐ[K] Kt := simpleTranscendentalEquiv ht hadj_t
    have heKt_var : eKt (ratFuncVar K) = t := simpleTranscendentalEquiv_var ht hadj_t
    have hirr_rf :
        Irreducible (linearPencilRatFunc (Polynomial.X ^ n : K[X]) (1 : K[X])) :=
      exercise_5_4_relPrime isRelPrime_one_right
        (Or.inl (by rw [Polynomial.natDegree_X_pow]; omega))
    let mapEquiv : (FractionRing K[X])[X] ≃+* Kt[X] := Polynomial.mapEquiv eKt.toRingEquiv
    have hmap_pencil :
        mapEquiv (linearPencilRatFunc (Polynomial.X ^ n : K[X]) (1 : K[X])) =
          (Polynomial.X ^ n - Polynomial.C t : Kt[X]) := by
      simp [mapEquiv, linearPencilRatFunc, Polynomial.map_sub, Polynomial.map_pow, heKt_var]
    exact hmap_pencil ▸ hirr_rf.map mapEquiv

/-! ## §7.2 The extension of monomorphisms (printed pp. 62–67, PDF pp. 70–75) -/

/-- Induced polynomial-ring homomorphism `i : K[x] →+* L[x]` sending
`a_0 + a_1 x + ⋯ + a_n x^n ↦ i(a_0) + i(a_1) x + ⋯ + i(a_n) x^n`
(§7.2 prose definition, printed p. 63 / PDF p. 71). -/
noncomputable def garlingMapPoly {K L : Type*} [Field K] [Field L] (i : K →+* L) : K[X] →+* L[X] :=
  Polynomial.mapRingHom i

@[simp]
theorem garlingMapPoly_apply {K L : Type*} [Field K] [Field L] (i : K →+* L) (f : K[X]) :
    garlingMapPoly i f = f.map i :=
  rfl

/-- Prose remark (§7.2, printed p. 63 / PDF p. 71): any ring homomorphism `i : K →+* L` between
fields is a monomorphism (`IsRingMonomorphism i`), and its extension `garlingMapPoly i : K[X] →+* L[X]`
is likewise a ring monomorphism, inducing an isomorphism `K[X] ≃+* i(K)[X]`. -/
theorem garlingMapPoly_monomorphism {K L : Type*} [Field K] [Field L] (i : K →+* L) :
    IsRingMonomorphism i ∧
    IsRingMonomorphism (garlingMapPoly i) ∧
    Nonempty (K[X] ≃+* (i.fieldRange)[X]) := by
  have hi : Function.Injective i := i.injective
  have hmap : Function.Injective (garlingMapPoly i) := Polynomial.map_injective i hi
  let g : K →+* i.fieldRange :=
    { toFun := fun k => ⟨i k, ⟨k, rfl⟩⟩
      map_one' := Subtype.ext i.map_one
      map_mul' := fun x y => Subtype.ext (i.map_mul x y)
      map_zero' := Subtype.ext i.map_zero
      map_add' := fun x y => Subtype.ext (i.map_add x y) }
  let eField : K ≃+* i.fieldRange :=
    RingEquiv.ofBijective g
      ⟨fun x y hxy => hi (congrArg Subtype.val hxy),
       by rintro ⟨_, k, rfl⟩; exact ⟨k, rfl⟩⟩
  exact ⟨hi, hmap, ⟨Polynomial.mapEquiv eField⟩⟩

/-- Splitting equivalence for `i(f) ∈ L[x]`: `GarlingSplitsOver L L (garlingMapPoly i f)` holds iff
`(f.map i).Splits` iff `i(f) = i(λ) (x - β_1) ⋯ (x - β_n)` with `λ ∈ K` and `β_r ∈ L`. -/
theorem garlingSplitsOver_mapPoly_iff {K L : Type*} [Field K] [Field L]
    (i : K →+* L) (f : K[X]) :
    (GarlingSplitsOver L L (garlingMapPoly i f) ↔ (f.map i).Splits) ∧
    (GarlingSplitsOver L L (garlingMapPoly i f) ↔
      ∃ (n : ℕ) (c : K) (β : Fin n → L),
        garlingMapPoly i f =
          Polynomial.C (i c) * ∏ r : Fin n, (Polynomial.X - Polynomial.C (β r))) := by
  have h1 : GarlingSplitsOver L L (garlingMapPoly i f) ↔ (f.map i).Splits := by
    rw [garlingSplitsOver_iff_splits]
    change ((f.map i).map (RingHom.id L)).Splits ↔ (f.map i).Splits
    rw [Polynomial.map_id]
  refine ⟨h1, ⟨fun h => ?_, fun ⟨n, c, β, hfac⟩ => ?_⟩⟩
  · by_cases hf0 : f = 0
    · refine ⟨0, 0, Fin.elim0, ?_⟩
      simp [hf0]
    · obtain ⟨n, cL, β, hfac⟩ := h
      rw [GarlingSplitsExplicit] at hfac
      simp only [garlingMapPoly_apply, Algebra.algebraMap_self, Polynomial.map_id,
        RingHom.id_apply] at hfac
      have hprod_monic :
          (∏ r : Fin n, (Polynomial.X - Polynomial.C (β r) : L[X])).Monic :=
        Polynomial.monic_prod_of_monic _ _ fun r _ => Polynomial.monic_X_sub_C (β r)
      have hcL : cL = i f.leadingCoeff := by
        have hlc := congrArg Polynomial.leadingCoeff hfac
        rw [Polynomial.leadingCoeff_map_of_injective i.injective,
          Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hprod_monic.leadingCoeff,
          mul_one] at hlc
        exact hlc.symm
      exact ⟨n, f.leadingCoeff, β, by simpa [hcL] using hfac⟩
  · refine ⟨n, i c, β, ?_⟩
    rw [GarlingSplitsExplicit]
    simpa [Algebra.algebraMap_self, Polynomial.map_id] using hfac

/-- **Theorem 7.4** (§7.2, printed p. 63 / PDF p. 71; proof pp. 63–64):
*"Suppose that `K(α):K` is a simple extension and that `α` is algebraic over `K`, with minimal
polynomial `m_α`. Suppose that `i` is a monomorphism from `K` into a field `L` and that `β ∈ L`.
Then a necessary and sufficient condition for there to be a monomorphism `j` from `K(α)` to `L`
with `j(α) = β` and `j|_K = i` is that `i(m_α)(β) = 0`. If the condition is satisfied then `j`
is unique."* -/
theorem theorem_7_4 {K Kα L : Type*} [Field K] [Field Kα] [Algebra K Kα] [Field L]
    {α : Kα} (hadj : IntermediateField.adjoin K ({α} : Set Kα) = ⊤)
    (hα : IsGarlingAlgebraic K α)
    {i : K →+* L} (_hi : IsRingMonomorphism i) (β : L) :
    ((∃ j : Kα →+* L,
        IsRingMonomorphism j ∧ j α = β ∧ ∀ k : K, j (algebraMap K Kα k) = i k) ↔
      (garlingMapPoly i (minpoly K α)).eval β = 0) ∧
    ((garlingMapPoly i (minpoly K α)).eval β = 0 →
      ∃! j : Kα →+* L,
        IsRingMonomorphism j ∧ j α = β ∧ ∀ k : K, j (algebraMap K Kα k) = i k) := by
  have hexists :
      (∃ j : Kα →+* L,
          IsRingMonomorphism j ∧ j α = β ∧ ∀ k : K, j (algebraMap K Kα k) = i k) ↔
        (garlingMapPoly i (minpoly K α)).eval β = 0 := by
    constructor
    · rintro ⟨j, _hj, hjα, hjk⟩
      have hi_eq : i = j.comp (algebraMap K Kα) := RingHom.ext fun k => (hjk k).symm
      rw [garlingMapPoly_apply, Polynomial.eval_map, hi_eq, ← hjα,
        ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval K α, map_zero]
    · intro hβ
      let _ : Algebra K L := i.toAlgebra
      have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp hα
      let pb₀ : PowerBasis K (IntermediateField.adjoin K ({α} : Set Kα)) :=
        IntermediateField.adjoin.powerBasis hint
      have hgen_val : (pb₀.gen : Kα) = α := by
        rw [IntermediateField.adjoin.powerBasis_gen]
        rfl
      have hmin_eq : minpoly K pb₀.gen = minpoly K α := by
        have h := minpoly.algHom_eq (IntermediateField.adjoin K ({α} : Set Kα)).val
          (IntermediateField.adjoin K ({α} : Set Kα)).val.injective pb₀.gen
        simpa [hgen_val] using h.symm
      have hβ_aeval : Polynomial.aeval β (minpoly K pb₀.gen) = 0 := by
        rw [hmin_eq, Polynomial.aeval_def, ← Polynomial.eval_map]
        exact hβ
      let ϕ₀ : IntermediateField.adjoin K ({α} : Set Kα) →ₐ[K] L := pb₀.lift β hβ_aeval
      let eTop : IntermediateField.adjoin K ({α} : Set Kα) ≃ₐ[K] Kα :=
        (IntermediateField.equivOfEq hadj).trans IntermediateField.topEquiv
      have heTop_symm : eTop.symm α = pb₀.gen := by
        apply eTop.injective
        rw [AlgEquiv.apply_symm_apply]
        exact hgen_val.symm
      let ϕ : Kα →ₐ[K] L := ϕ₀.comp eTop.symm.toAlgHom
      refine ⟨ϕ.toRingHom, ϕ.toRingHom.injective, ?_, fun k => ϕ.commutes k⟩
      change ϕ₀ (eTop.symm α) = β
      rw [heTop_symm, PowerBasis.lift_gen]
  refine ⟨hexists, fun hβ => ?_⟩
  obtain ⟨j, hj_mono, hjα, hjk⟩ := hexists.mpr hβ
  refine ⟨j, ⟨hj_mono, hjα, hjk⟩, ?_⟩
  rintro j' ⟨_hj'_mono, hj'α, hj'k⟩
  let F : IntermediateField K Kα :=
    { carrier := {x : Kα | j' x = j x}
      mul_mem' := by intro a b ha hb; change j' (a * b) = j (a * b); rw [map_mul, map_mul, ha, hb]
      add_mem' := by intro a b ha hb; change j' (a + b) = j (a + b); rw [map_add, map_add, ha, hb]
      algebraMap_mem' := fun k => (hj'k k).trans (hjk k).symm
      inv_mem' := by intro a ha; change j' a⁻¹ = j a⁻¹; rw [map_inv₀, map_inv₀, ha] }
  have hαF : α ∈ F := hj'α.trans hjα.symm
  have hF_top : F = ⊤ :=
    top_unique (hadj ▸ IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hαF))
  ext x
  have hx : x ∈ F := hF_top ▸ IntermediateField.mem_top
  exact hx

/-- Subfield `IntermediateField.adjoin K {α}` specialization of **Theorem 7.4** (§7.2, p. 63). -/
theorem theorem_7_4_adjoin {K M L : Type*} [Field K] [Field M] [Algebra K M] [Field L]
    {α : M} (hα : IsGarlingAlgebraic K α)
    {i : K →+* L} (hi : IsRingMonomorphism i) (β : L) :
    ((∃ j : IntermediateField.adjoin K ({α} : Set M) →+* L,
        IsRingMonomorphism j ∧
        j (IntermediateField.AdjoinSimple.gen K α) = β ∧
        ∀ k : K, j (algebraMap K (IntermediateField.adjoin K ({α} : Set M)) k) = i k) ↔
      (garlingMapPoly i (minpoly K α)).eval β = 0) ∧
    ((garlingMapPoly i (minpoly K α)).eval β = 0 →
      ∃! j : IntermediateField.adjoin K ({α} : Set M) →+* L,
        IsRingMonomorphism j ∧
        j (IntermediateField.AdjoinSimple.gen K α) = β ∧
        ∀ k : K, j (algebraMap K (IntermediateField.adjoin K ({α} : Set M)) k) = i k) := by
  let F : IntermediateField K M := IntermediateField.adjoin K ({α} : Set M)
  let gen : F := IntermediateField.AdjoinSimple.gen K α
  have hadj_gen : IntermediateField.adjoin K ({gen} : Set F) = ⊤ := by
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    let L0 : IntermediateField K M := (IntermediateField.adjoin K ({gen} : Set F)).map F.val
    have hα_mem : α ∈ L0 := ⟨gen, IntermediateField.mem_adjoin_simple_self K gen, rfl⟩
    have hle : F ≤ L0 :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hα_mem)
    obtain ⟨y, hy, hyx⟩ := hle x.2
    exact (F.val.injective hyx) ▸ hy
  have hgen_alg : IsGarlingAlgebraic K gen := by
    obtain ⟨p, hp0, hpeval⟩ := hα
    exact ⟨p, hp0, Subtype.ext ((Polynomial.aeval_algHom_apply F.val gen p).symm.trans hpeval)⟩
  have hmin : minpoly K gen = minpoly K α :=
    (minpoly.algHom_eq F.val F.val.injective gen).symm
  simpa [hmin] using theorem_7_4 hadj_gen hgen_alg hi β

private theorem ratFuncVar_transcendental_and_adjoin (K : Type*) [Field K] :
    IsGarlingTranscendental K (ratFuncVar K) ∧
    IntermediateField.adjoin K ({ratFuncVar K} : Set (FractionRing K[X])) = ⊤ := by
  let t : FractionRing K[X] := ratFuncVar K
  have haeval_t : ∀ p : K[X], Polynomial.aeval t p = algebraMap K[X] (FractionRing K[X]) p := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p₁ p₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂]
    | monomial m a =>
      rw [Polynomial.aeval_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      have hCa : algebraMap K (FractionRing K[X]) a =
          algebraMap K[X] (FractionRing K[X]) (Polynomial.C a) :=
        IsScalarTower.algebraMap_apply K K[X] (FractionRing K[X]) a
      rw [hCa]
      rfl
  have htr : IsGarlingTranscendental K t := by
    rintro ⟨p, hp0, hpt⟩
    have hinj : Function.Injective (algebraMap K[X] (FractionRing K[X])) :=
      IsFractionRing.injective K[X] (FractionRing K[X])
    exact hp0 (hinj (by rw [← haeval_t p, hpt, map_zero]))
  have hadj : IntermediateField.adjoin K ({t} : Set (FractionRing K[X])) = ⊤ := by
    ext z
    simp only [IntermediateField.mem_top, iff_true]
    obtain ⟨num, den, _, rfl⟩ := IsFractionRing.div_surjective (A := K[X]) z
    have hmem : ∀ p : K[X],
        algebraMap K[X] (FractionRing K[X]) p ∈
          IntermediateField.adjoin K ({t} : Set (FractionRing K[X])) := by
      intro p
      induction p using Polynomial.induction_on' with
      | add p₁ p₂ ih₁ ih₂ => rw [map_add]; exact add_mem ih₁ ih₂
      | monomial m a =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
        have hCa : algebraMap K[X] (FractionRing K[X]) (Polynomial.C a) =
            algebraMap K (FractionRing K[X]) a :=
          (IsScalarTower.algebraMap_apply K K[X] (FractionRing K[X]) a).symm
        rw [hCa]
        exact mul_mem ((IntermediateField.adjoin K ({t} : Set (FractionRing K[X]))).algebraMap_mem a)
          (pow_mem (IntermediateField.mem_adjoin_simple_self K t) m)
    exact div_mem (hmem num) (hmem den)
  exact ⟨htr, hadj⟩

/-- Ambient-field counterexample to the literal printed wording *"α' algebraic over K"* in
**Corollary 1** [to Theorem 7.4] (§7.2, printed p. 64 / PDF p. 72):
inside `M = ℤ₂(s)(t)`, the subfields `K = ℤ₂(t)` and `K' = ℤ₂(s)` are isomorphic (`i : K ≃+* K'`),
`K(α) : K` and `K'(α') : K'` with `α = α' = t` are simple extensions, and `α'` is literally
algebraic over `K` (`α' ∈ K`), yet `α'` is transcendental over `K'` so Garling's minimal
polynomial `m_{α'} ∈ K'[x]` (monic generator of `evalKer K' α'`) does not exist. -/
theorem corollary_1_to_theorem_7_4_ambient_counterexample :
    ∃ (M : Type) (_ : Field M) (_ : Algebra (ZMod 2) M)
      (K K' : IntermediateField (ZMod 2) M) (_i : K ≃+* K') (α α' : M),
      IntermediateField.adjoin (ZMod 2) ({α} : Set M) = K ∧
      IsGarlingAlgebraic K α ∧
      IsGarlingAlgebraic K α' ∧
      (IntermediateField.adjoin K' ({α'} : Set M)).restrictScalars (ZMod 2) = ⊤ ∧
      ¬ IsGarlingAlgebraic K' α' ∧
      ¬ ∃ m : K'[X], m.Monic ∧ evalKer K' α' = Ideal.span {m} := by
  let F1 : Type := FractionRing (ZMod 2)[X]
  let M : Type := FractionRing F1[X]
  let s1 : F1 := ratFuncVar (ZMod 2)
  let s : M := algebraMap F1 M s1
  let t : M := ratFuncVar F1
  let K : IntermediateField (ZMod 2) M := IntermediateField.adjoin (ZMod 2) ({t} : Set M)
  let K' : IntermediateField (ZMod 2) M := IntermediateField.adjoin (ZMod 2) ({s} : Set M)
  have hs1_tr : IsGarlingTranscendental (ZMod 2) s1 :=
    (ratFuncVar_transcendental_and_adjoin (ZMod 2)).1
  have ht_tr_F1 : IsGarlingTranscendental F1 t := (ratFuncVar_transcendental_and_adjoin F1).1
  have hmap_s : ∀ p : (ZMod 2)[X], (algebraMap F1 M) (Polynomial.aeval s1 p) = Polynomial.aeval s p := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p₁ p₂ ih₁ ih₂ => rw [map_add, map_add, map_add, ih₁, ih₂]
    | monomial n c =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow,
        ← IsScalarTower.algebraMap_apply (ZMod 2) F1 M]
  have hs_tr : IsGarlingTranscendental (ZMod 2) s := by
    rintro ⟨p, hp0, hpeval⟩
    apply hs1_tr
    refine ⟨p, hp0, ?_⟩
    apply (algebraMap F1 M).injective
    rw [map_zero]
    exact (hmap_s p).trans hpeval
  have ht_tr : IsGarlingTranscendental (ZMod 2) t := by
    rintro ⟨p, hp0, hpeval⟩
    apply ht_tr_F1
    refine ⟨p.map (algebraMap (ZMod 2) F1),
      (Polynomial.map_ne_zero_iff (algebraMap (ZMod 2) F1).injective).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq (ZMod 2) F1 M]
    exact hpeval
  let tK : K := IntermediateField.AdjoinSimple.gen (ZMod 2) t
  let sK' : K' := IntermediateField.AdjoinSimple.gen (ZMod 2) s
  have htK_tr : IsGarlingTranscendental (ZMod 2) tK := by
    rintro ⟨p, hp0, hpeval⟩
    have hval := congrArg K.val hpeval
    rw [← Polynomial.aeval_algHom_apply K.val, map_zero] at hval
    exact ht_tr ⟨p, hp0, hval⟩
  have hsK'_tr : IsGarlingTranscendental (ZMod 2) sK' := by
    rintro ⟨p, hp0, hpeval⟩
    have hval := congrArg K'.val hpeval
    rw [← Polynomial.aeval_algHom_apply K'.val, map_zero] at hval
    exact hs_tr ⟨p, hp0, hval⟩
  have hadj_tK : IntermediateField.adjoin (ZMod 2) ({tK} : Set K) = ⊤ := by
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    let L0 : IntermediateField (ZMod 2) M :=
      (IntermediateField.adjoin (ZMod 2) ({tK} : Set K)).map K.val
    have ht_mem : t ∈ L0 := ⟨tK, IntermediateField.mem_adjoin_simple_self (ZMod 2) tK, rfl⟩
    have hle : K ≤ L0 :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ht_mem)
    obtain ⟨y, hy, hyx⟩ := hle x.2
    exact (K.val.injective hyx) ▸ hy
  have hadj_sK' : IntermediateField.adjoin (ZMod 2) ({sK'} : Set K') = ⊤ := by
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    let L0 : IntermediateField (ZMod 2) M :=
      (IntermediateField.adjoin (ZMod 2) ({sK'} : Set K')).map K'.val
    have hs_mem : s ∈ L0 := ⟨sK', IntermediateField.mem_adjoin_simple_self (ZMod 2) sK', rfl⟩
    have hle : K' ≤ L0 :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hs_mem)
    obtain ⟨y, hy, hyx⟩ := hle x.2
    exact (K'.val.injective hyx) ▸ hy
  let eK : FractionRing (ZMod 2)[X] ≃+* K := (simpleTranscendentalEquiv htK_tr hadj_tK).toRingEquiv
  let eK' : FractionRing (ZMod 2)[X] ≃+* K' := (simpleTranscendentalEquiv hsK'_tr hadj_sK').toRingEquiv
  let i : K ≃+* K' := eK.symm.trans eK'
  have ht_alg_K : IsGarlingAlgebraic K t := by
    refine ⟨Polynomial.X - Polynomial.C ⟨t, IntermediateField.mem_adjoin_simple_self (ZMod 2) t⟩,
      Polynomial.X_sub_C_ne_zero _, ?_⟩
    simp
  have hK'_range :
      ∀ x : K', ∃ y : F1, algebraMap F1 M y = (x : M) := by
    let imF1 : IntermediateField (ZMod 2) M :=
      { carrier := Set.range (algebraMap F1 M)
        mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, map_mul _ a b⟩
        add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add _ a b⟩
        algebraMap_mem' := fun q =>
          ⟨algebraMap (ZMod 2) F1 q, (IsScalarTower.algebraMap_apply (ZMod 2) F1 M q).symm⟩
        inv_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨a⁻¹, map_inv₀ _ a⟩ }
    have hs_im : s ∈ imF1 := ⟨s1, rfl⟩
    have hle : K' ≤ imF1 :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hs_im)
    intro x
    exact hle x.2
  have ht_not_alg_K' : ¬ IsGarlingAlgebraic K' t := by
    rintro ⟨p, hp0, hpeval⟩
    let jK'F1 : K' →+* F1 :=
      { toFun := fun x => Classical.choose (hK'_range x)
        map_one' := (algebraMap F1 M).injective (by
          rw [Classical.choose_spec (hK'_range 1), map_one]; rfl)
        map_mul' := fun x y => (algebraMap F1 M).injective (by
          rw [Classical.choose_spec (hK'_range (x * y)), map_mul,
            Classical.choose_spec (hK'_range x), Classical.choose_spec (hK'_range y)]; rfl)
        map_zero' := (algebraMap F1 M).injective (by
          rw [Classical.choose_spec (hK'_range 0), map_zero]; rfl)
        map_add' := fun x y => (algebraMap F1 M).injective (by
          rw [Classical.choose_spec (hK'_range (x + y)), map_add,
            Classical.choose_spec (hK'_range x), Classical.choose_spec (hK'_range y)]; rfl) }
    have hj_comp : (algebraMap F1 M).comp jK'F1 = algebraMap K' M := by
      ext x
      exact Classical.choose_spec (hK'_range x)
    apply ht_tr_F1
    refine ⟨p.map jK'F1, (Polynomial.map_ne_zero_iff jK'F1.injective).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hj_comp]
    exact hpeval
  have hno_minpoly : ¬ ∃ m : K'[X], m.Monic ∧ evalKer K' t = Ideal.span {m} := by
    rintro ⟨m, hm_monic, hm_ker⟩
    apply ht_not_alg_K'
    refine ⟨m, hm_monic.ne_zero, ?_⟩
    have hm_mem : m ∈ evalKer K' t := hm_ker.symm ▸ Ideal.mem_span_singleton_self m
    exact RingHom.mem_ker.mp hm_mem
  have hadj_K't_top : (IntermediateField.adjoin K' ({t} : Set M)).restrictScalars (ZMod 2) = ⊤ := by
    let E : IntermediateField (ZMod 2) M :=
      (IntermediateField.adjoin K' ({t} : Set M)).restrictScalars (ZMod 2)
    have hs_E : s ∈ E := by
      change s ∈ IntermediateField.adjoin K' ({t} : Set M)
      exact (IntermediateField.adjoin K' ({t} : Set M)).algebraMap_mem
        ⟨s, IntermediateField.mem_adjoin_simple_self (ZMod 2) s⟩
    have ht_E : t ∈ E := IntermediateField.mem_adjoin_simple_self K' t
    have hF1_E : ∀ y : F1, algebraMap F1 M y ∈ E := by
      intro y
      let subF1 : Subfield F1 := E.toSubfield.comap (algebraMap F1 M)
      have hQ_sub : ∀ q : ZMod 2, algebraMap (ZMod 2) F1 q ∈ subF1 := fun q => by
        change algebraMap F1 M (algebraMap (ZMod 2) F1 q) ∈ E
        rw [← IsScalarTower.algebraMap_apply (ZMod 2) F1 M]
        exact E.algebraMap_mem q
      let ifF1 : IntermediateField (ZMod 2) F1 := { subF1 with algebraMap_mem' := hQ_sub }
      have hs1_if : s1 ∈ ifF1 := hs_E
      have hadj_s1 : IntermediateField.adjoin (ZMod 2) ({s1} : Set F1) = ⊤ :=
        (ratFuncVar_transcendental_and_adjoin (ZMod 2)).2
      have htop_F1 : ifF1 = ⊤ :=
        top_unique (hadj_s1 ▸ IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hs1_if))
      have hy_mem : y ∈ ifF1 := htop_F1 ▸ IntermediateField.mem_top
      exact hy_mem
    let ifM : IntermediateField F1 M :=
      { E.toSubfield with algebraMap_mem' := hF1_E }
    have ht_ifM : t ∈ ifM := ht_E
    have hadj_tM : IntermediateField.adjoin F1 ({t} : Set M) = ⊤ :=
      (ratFuncVar_transcendental_and_adjoin F1).2
    have htop_M : ifM = ⊤ :=
      top_unique (hadj_tM ▸ IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ht_ifM))
    ext z
    simp only [IntermediateField.mem_top, iff_true]
    have hz : z ∈ ifM := htop_M ▸ IntermediateField.mem_top
    exact hz
  exact ⟨M, inferInstance, inferInstance, K, K', i, t, t, rfl, ht_alg_K, ht_alg_K,
    hadj_K't_top, ht_not_alg_K', hno_minpoly⟩

/-- **Corollary 1** [to Theorem 7.4] (§7.2, printed p. 64 / PDF p. 72; repaired with
`IsGarlingAlgebraic K' α'` in place of the printed slip *"α' algebraic over K"*):
Suppose `K(α) : K` and `K'(α') : K'` are simple extensions with `α` algebraic over `K` and `α'`
algebraic over `K'`, and `i : K → K'` is a ring isomorphism. Then there exists a ring isomorphism
`j : K(α) → K'(α')` with `j(α) = α'` and `j|_K = i` if and only if `i(m_α) = m_{α'}`, and if so,
`j` is unique. -/
theorem corollary_1_to_theorem_7_4 {K Kα K' K'α' : Type*}
    [Field K] [Field Kα] [Algebra K Kα]
    [Field K'] [Field K'α'] [Algebra K' K'α']
    {α : Kα} (hadj : IntermediateField.adjoin K ({α} : Set Kα) = ⊤)
    (hα : IsGarlingAlgebraic K α)
    {α' : K'α'} (hadj' : IntermediateField.adjoin K' ({α'} : Set K'α') = ⊤)
    (_hα' : IsGarlingAlgebraic K' α')
    {i : K →+* K'} (hi : IsRingIsomorphism i) :
    ((∃ j : Kα →+* K'α',
        IsRingIsomorphism j ∧ j α = α' ∧
        ∀ k : K, j (algebraMap K Kα k) = algebraMap K' K'α' (i k)) ↔
      garlingMapPoly i (minpoly K α) = minpoly K' α') ∧
    (garlingMapPoly i (minpoly K α) = minpoly K' α' →
      ∃! j : Kα →+* K'α',
        IsRingIsomorphism j ∧ j α = α' ∧
        ∀ k : K, j (algebraMap K Kα k) = algebraMap K' K'α' (i k)) := by
  let i' : K →+* K'α' := (algebraMap K' K'α').comp i
  have hi'_mono : IsRingMonomorphism i' := i'.injective
  have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp hα
  let eK : K ≃+* K' := RingEquiv.ofBijective i hi
  have hiff :
      (∃ j : Kα →+* K'α',
          IsRingIsomorphism j ∧ j α = α' ∧
          ∀ k : K, j (algebraMap K Kα k) = algebraMap K' K'α' (i k)) ↔
        garlingMapPoly i (minpoly K α) = minpoly K' α' := by
    constructor
    · rintro ⟨j, hj_iso, hjα, hjk⟩
      have heval : (garlingMapPoly i' (minpoly K α)).eval α' = 0 :=
        (theorem_7_4 hadj hα hi'_mono α').1.mp ⟨j, hj_iso.1, hjα, hjk⟩
      have haeval : Polynomial.aeval α' (garlingMapPoly i (minpoly K α)) = 0 := by
        rw [Polynomial.aeval_def, ← Polynomial.eval_map, garlingMapPoly_apply, Polynomial.map_map]
        exact heval
      have hmonic : (garlingMapPoly i (minpoly K α)).Monic :=
        (minpoly.monic hint).map i
      have hirr : Irreducible (garlingMapPoly i (minpoly K α)) := by
        have hmap_eq : garlingMapPoly i (minpoly K α) = Polynomial.mapEquiv eK (minpoly K α) := rfl
        rw [hmap_eq]
        exact (minpoly.irreducible hint).map (Polynomial.mapEquiv eK)
      exact minpoly.eq_of_irreducible_of_monic hirr haeval hmonic
    · intro hm
      have heval : (garlingMapPoly i' (minpoly K α)).eval α' = 0 := by
        have hmap : garlingMapPoly i' (minpoly K α) =
            (garlingMapPoly i (minpoly K α)).map (algebraMap K' K'α') := by
          simp [i', garlingMapPoly_apply, Polynomial.map_map]
        rw [hmap, hm, Polynomial.eval_map, ← Polynomial.aeval_def, minpoly.aeval K' α']
      obtain ⟨j, ⟨hj_mono, hjα, hjk⟩, _⟩ := (theorem_7_4 hadj hα hi'_mono α').2 heval
      have hj_surj : Function.Surjective j := by
        let F : IntermediateField K' K'α' :=
          { carrier := Set.range j
            mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, map_mul j a b⟩
            add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add j a b⟩
            algebraMap_mem' := fun k' => by
              obtain ⟨k, rfl⟩ := hi.2 k'
              exact ⟨algebraMap K Kα k, hjk k⟩
            inv_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨a⁻¹, map_inv₀ j a⟩ }
        have hα'F : α' ∈ F := ⟨α, hjα⟩
        have hF_top : F = ⊤ :=
          top_unique (hadj' ▸ IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hα'F))
        intro y
        have hy : y ∈ F := hF_top ▸ IntermediateField.mem_top
        exact hy
      exact ⟨j, ⟨hj_mono, hj_surj⟩, hjα, hjk⟩
  refine ⟨hiff, fun hm => ?_⟩
  obtain ⟨j, hj_iso, hjα, hjk⟩ := hiff.mpr hm
  have heval : (garlingMapPoly i' (minpoly K α)).eval α' = 0 :=
    (theorem_7_4 hadj hα hi'_mono α').1.mp ⟨j, hj_iso.1, hjα, hjk⟩
  obtain ⟨_, _, hj_uniq⟩ := (theorem_7_4 hadj hα hi'_mono α').2 heval
  refine ⟨j, ⟨hj_iso, hjα, hjk⟩, ?_⟩
  rintro j' ⟨hj'_iso, hj'α, hj'k⟩
  exact (hj_uniq j' ⟨hj'_iso.1, hj'α, hj'k⟩).trans (hj_uniq j ⟨hj_iso.1, hjα, hjk⟩).symm

/-- Bundled `RingEquiv` form of **Corollary 1** [to Theorem 7.4] (§7.2, p. 64). -/
theorem corollary_1_to_theorem_7_4_equiv {K Kα K' K'α' : Type*}
    [Field K] [Field Kα] [Algebra K Kα]
    [Field K'] [Field K'α'] [Algebra K' K'α']
    {α : Kα} (hadj : IntermediateField.adjoin K ({α} : Set Kα) = ⊤)
    (hα : IsGarlingAlgebraic K α)
    {α' : K'α'} (hadj' : IntermediateField.adjoin K' ({α'} : Set K'α') = ⊤)
    (hα' : IsGarlingAlgebraic K' α')
    (i : K ≃+* K') :
    ((∃ j : Kα ≃+* K'α',
        j α = α' ∧ ∀ k : K, j (algebraMap K Kα k) = algebraMap K' K'α' (i k)) ↔
      garlingMapPoly i.toRingHom (minpoly K α) = minpoly K' α') ∧
    (garlingMapPoly i.toRingHom (minpoly K α) = minpoly K' α' →
      ∃! j : Kα ≃+* K'α',
        j α = α' ∧ ∀ k : K, j (algebraMap K Kα k) = algebraMap K' K'α' (i k)) := by
  have hcor := corollary_1_to_theorem_7_4 hadj hα hadj' hα' (i := i.toRingHom) i.bijective
  refine ⟨?_, fun hm => ?_⟩
  · constructor
    · rintro ⟨j, hjα, hjk⟩
      exact hcor.1.mp ⟨j.toRingHom, j.bijective, hjα, hjk⟩
    · intro hm
      obtain ⟨j, ⟨hj_iso, hjα, hjk⟩, _⟩ := hcor.2 hm
      exact ⟨RingEquiv.ofBijective j hj_iso, hjα, hjk⟩
  · obtain ⟨j, ⟨hj_iso, hjα, hjk⟩, hj_uniq⟩ := hcor.2 hm
    refine ⟨RingEquiv.ofBijective j hj_iso, ⟨hjα, hjk⟩, ?_⟩
    rintro j' ⟨hj'α, hj'k⟩
    have heq : j'.toRingHom = j := hj_uniq j'.toRingHom ⟨j'.bijective, hj'α, hj'k⟩
    ext x
    exact RingHom.congr_fun heq x

/-- Explicit bijection between `i`-extending monomorphisms `j : K(α) →+* L` and roots `β ∈ L` of
`i(m_α)` underlying **Corollary 2** [to Theorem 7.4] (§7.2, printed p. 64 / PDF p. 72). -/
noncomputable def monomorphismEquivRoot {K Kα L : Type*}
    [Field K] [Field Kα] [Algebra K Kα] [Field L]
    {α : Kα} (hadj : IntermediateField.adjoin K ({α} : Set Kα) = ⊤)
    (hα : IsGarlingAlgebraic K α)
    {i : K →+* L} (hi : IsRingMonomorphism i) :
    {j : Kα →+* L // IsRingMonomorphism j ∧ ∀ k : K, j (algebraMap K Kα k) = i k} ≃
      {β : L // (garlingMapPoly i (minpoly K α)).IsRoot β} where
  toFun j := ⟨j.1 α, (theorem_7_4 hadj hα hi (j.1 α)).1.mp ⟨j.1, j.2.1, rfl, j.2.2⟩⟩
  invFun β :=
    ⟨Classical.choose ((theorem_7_4 hadj hα hi β.1).1.mpr β.2),
     (Classical.choose_spec ((theorem_7_4 hadj hα hi β.1).1.mpr β.2)).1,
     (Classical.choose_spec ((theorem_7_4 hadj hα hi β.1).1.mpr β.2)).2.2⟩
  left_inv j := by
    apply Subtype.ext
    have hβ : (garlingMapPoly i (minpoly K α)).eval (j.1 α) = 0 :=
      (theorem_7_4 hadj hα hi (j.1 α)).1.mp ⟨j.1, j.2.1, rfl, j.2.2⟩
    have hspec := Classical.choose_spec ((theorem_7_4 hadj hα hi (j.1 α)).1.mpr hβ)
    obtain ⟨j₀, _, hj₀_uniq⟩ := (theorem_7_4 hadj hα hi (j.1 α)).2 hβ
    exact (hj₀_uniq _ hspec).trans (hj₀_uniq j.1 ⟨j.2.1, rfl, j.2.2⟩).symm
  right_inv β := by
    apply Subtype.ext
    exact (Classical.choose_spec ((theorem_7_4 hadj hα hi β.1).1.mpr β.2)).2.1

/-- **Corollary 2** [to Theorem 7.4] (§7.2, printed p. 64 / PDF p. 72):
*"Suppose that `K(α):K` is simple and that `α` is algebraic over `K`. Suppose that `i: K → L` is a
monomorphism, and that `i(m_α)` has `r` distinct roots in `L`. Then there are exactly `r` distinct
monomorphisms `j: K(α) → L` with `j|_K = i`."* -/
theorem corollary_2_to_theorem_7_4 {K Kα L : Type*}
    [Field K] [Field Kα] [Algebra K Kα] [Field L]
    {α : Kα} (hadj : IntermediateField.adjoin K ({α} : Set Kα) = ⊤)
    (hα : IsGarlingAlgebraic K α)
    {i : K →+* L} (hi : IsRingMonomorphism i) {r : ℕ}
    (hroots : setOrder {β : L | (garlingMapPoly i (minpoly K α)).IsRoot β} = (r : ℕ∞)) :
    setOrder {j : Kα →+* L | IsRingMonomorphism j ∧ ∀ k : K, j (algebraMap K Kα k) = i k} =
      (r : ℕ∞) ∧
    Nat.card {j : Kα →+* L // IsRingMonomorphism j ∧ ∀ k : K, j (algebraMap K Kα k) = i k} = r := by
  classical
  let e := monomorphismEquivRoot hadj hα hi
  have hset :
      setOrder {j : Kα →+* L | IsRingMonomorphism j ∧ ∀ k : K, j (algebraMap K Kα k) = i k} =
        setOrder {β : L | (garlingMapPoly i (minpoly K α)).IsRoot β} :=
    ENat.card_congr e
  have hset_r :
      setOrder {j : Kα →+* L | IsRingMonomorphism j ∧ ∀ k : K, j (algebraMap K Kα k) = i k} =
        (r : ℕ∞) := hset.trans hroots
  refine ⟨hset_r, ?_⟩
  have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp hα
  have hmap_ne0 : garlingMapPoly i (minpoly K α) ≠ 0 :=
    ((minpoly.monic hint).map i).ne_zero
  have hsub_fin :
      Finite {β : L // (garlingMapPoly i (minpoly K α)).IsRoot β} := by
    refine Finite.of_injective
      (fun β : {β : L // (garlingMapPoly i (minpoly K α)).IsRoot β} =>
        (⟨β.1, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hmap_ne0).mpr β.2)⟩ :
          (garlingMapPoly i (minpoly K α)).roots.toFinset))
      (fun _ _ hab => Subtype.ext (Subtype.mk.inj hab))
  have _ : Finite {j : Kα →+* L // IsRingMonomorphism j ∧ ∀ k : K, j (algebraMap K Kα k) = i k} :=
    Finite.of_equiv _ e.symm
  have hcard_enat :
      (Nat.card {j : Kα →+* L // IsRingMonomorphism j ∧ ∀ k : K, j (algebraMap K Kα k) = i k} : ℕ∞) =
        (r : ℕ∞) :=
    (ENat.card_eq_coe_natCard
      {j : Kα →+* L // IsRingMonomorphism j ∧ ∀ k : K, j (algebraMap K Kα k) = i k}).symm.trans hset_r
  exact Nat.cast_injective hcard_enat

/-- `Finset.card` companion to **Corollary 2** [to Theorem 7.4] (§7.2, p. 64):
if `(garlingMapPoly i (minpoly K α)).roots.toFinset.card = r`, then there are `r` distinct
`i`-extending monomorphisms `j : K(α) →+* L`. -/
theorem corollary_2_to_theorem_7_4_finset {K Kα L : Type*}
    [Field K] [Field Kα] [Algebra K Kα] [Field L] [DecidableEq L]
    {α : Kα} (hadj : IntermediateField.adjoin K ({α} : Set Kα) = ⊤)
    (hα : IsGarlingAlgebraic K α)
    {i : K →+* L} (hi : IsRingMonomorphism i) {r : ℕ}
    (hroots : (garlingMapPoly i (minpoly K α)).roots.toFinset.card = r) :
    setOrder {j : Kα →+* L | IsRingMonomorphism j ∧ ∀ k : K, j (algebraMap K Kα k) = i k} =
      (r : ℕ∞) ∧
    Nat.card {j : Kα →+* L // IsRingMonomorphism j ∧ ∀ k : K, j (algebraMap K Kα k) = i k} = r := by
  have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp hα
  have hmap_ne0 : garlingMapPoly i (minpoly K α) ≠ 0 :=
    ((minpoly.monic hint).map i).ne_zero
  let s : Finset L := (garlingMapPoly i (minpoly K α)).roots.toFinset
  let eFin : {β : L // (garlingMapPoly i (minpoly K α)).IsRoot β} ≃ s :=
    { toFun := fun β => ⟨β.1, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hmap_ne0).mpr β.2)⟩
      invFun := fun β => ⟨β.1, (Polynomial.mem_roots hmap_ne0).mp (Multiset.mem_toFinset.mp β.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hset :
      setOrder {β : L | (garlingMapPoly i (minpoly K α)).IsRoot β} = (r : ℕ∞) := by
    have h1 : setOrder {β : L | (garlingMapPoly i (minpoly K α)).IsRoot β} =
        ENat.card s := ENat.card_congr eFin
    rw [h1, ENat.card_eq_coe_fintype_card, Fintype.card_coe]
    exact mod_cast hroots
  exact corollary_2_to_theorem_7_4 hadj hα hi hset

/-- **Theorem 7.5** (§7.2, printed pp. 64–65 / PDF pp. 72–73; proof pp. 65–66):
*"Suppose that `Σ:K` is a splitting field extension for a polynomial `f` in `K[x]` and that `i` is
a monomorphism from `K` into a field `L`. Then a necessary and sufficient condition for there to
be a monomorphism `j` from `Σ` into `L` with `j|_K = i` is that `i(f)` splits over `L`."* -/
theorem theorem_7_5 {K E L : Type*} [Field K] [Field E] [Algebra K E] [Field L]
    {f : K[X]} (hsf : IsGarlingSplittingFieldExtension K E f)
    {i : K →+* L} (_hi : IsRingMonomorphism i) :
    (∃ j : E →+* L, IsRingMonomorphism j ∧ ∀ k : K, j (algebraMap K E k) = i k) ↔
      GarlingSplitsOver L L (garlingMapPoly i f) := by
  rw [(garlingSplitsOver_mapPoly_iff i f).1]
  have hsf_ml : Polynomial.IsSplittingField K E f :=
    (isGarlingSplittingFieldExtension_iff K E f).mp hsf
  constructor
  · rintro ⟨j, _hj, hjk⟩
    have hi_eq : i = j.comp (algebraMap K E) := RingHom.ext fun k => (hjk k).symm
    rw [hi_eq, ← Polynomial.map_map]
    exact hsf_ml.splits.map j
  · intro hsplits
    let _ : Algebra K L := i.toAlgebra
    let ϕ : E →ₐ[K] L := Polynomial.IsSplittingField.lift E f hsplits
    exact ⟨ϕ.toRingHom, ϕ.toRingHom.injective, fun k => ϕ.commutes k⟩

/-- **Corollary 1** [to Theorem 7.5] (§7.2, printed p. 66 / PDF p. 74):
*"Suppose that `i: K → K'` is an isomorphism and that `f ∈ K[x]`. Suppose that `Σ:K` is a
splitting field extension for `f`, `Σ':K'` a splitting field extension for `i(f)`. Then there
exists an isomorphism `j: Σ → Σ'` such that `j|_K = i`."* -/
theorem corollary_1_to_theorem_7_5 {K K' E E' : Type*}
    [Field K] [Field K'] [Field E] [Field E']
    [Algebra K E] [Algebra K' E']
    {i : K →+* K'} (hi : IsRingIsomorphism i) (f : K[X])
    (hsf : IsGarlingSplittingFieldExtension K E f)
    (hsf' : IsGarlingSplittingFieldExtension K' E' (garlingMapPoly i f)) :
    ∃ j : E →+* E',
      IsRingIsomorphism j ∧ ∀ k : K, j (algebraMap K E k) = algebraMap K' E' (i k) := by
  let i' : K →+* E' := (algebraMap K' E').comp i
  have hsf'_ml : Polynomial.IsSplittingField K' E' (garlingMapPoly i f) :=
    (isGarlingSplittingFieldExtension_iff K' E' (garlingMapPoly i f)).mp hsf'
  have hi'_splits : GarlingSplitsOver E' E' (garlingMapPoly i' f) := by
    rw [(garlingSplitsOver_mapPoly_iff i' f).1]
    have hmap : f.map i' = (garlingMapPoly i f).map (algebraMap K' E') := by
      simp [i', garlingMapPoly_apply, Polynomial.map_map]
    rw [hmap]
    exact hsf'_ml.splits
  obtain ⟨j, hj_mono, hjk⟩ := (theorem_7_5 hsf i'.injective).mpr hi'_splits
  refine ⟨j, ⟨hj_mono, ?_⟩, hjk⟩
  let F : IntermediateField K' E' :=
    { carrier := Set.range j
      mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, map_mul j a b⟩
      add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add j a b⟩
      algebraMap_mem' := fun k' => by
        obtain ⟨k, rfl⟩ := hi.2 k'
        exact ⟨algebraMap K E k, hjk k⟩
      inv_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨a⁻¹, map_inv₀ j a⟩ }
  let jF : E →+* F :=
    { toFun := fun x => ⟨j x, ⟨x, rfl⟩⟩
      map_one' := Subtype.ext j.map_one
      map_mul' := fun x y => Subtype.ext (j.map_mul x y)
      map_zero' := Subtype.ext j.map_zero
      map_add' := fun x y => Subtype.ext (j.map_add x y) }
  have hcomm : (algebraMap K' F).comp i = jF.comp (algebraMap K E) := by
    ext k
    exact (hjk k).symm
  have hF_splits : GarlingSplitsOver K' F (garlingMapPoly i f) := by
    rw [garlingSplitsOver_iff_splits]
    have hsf_ml : Polynomial.IsSplittingField K E f :=
      (isGarlingSplittingFieldExtension_iff K E f).mp hsf
    have hmap :
        (garlingMapPoly i f).map (algebraMap K' F) = (f.map (algebraMap K E)).map jF := by
      rw [garlingMapPoly_apply, Polynomial.map_map, hcomm, ← Polynomial.map_map]
    rw [hmap]
    exact hsf_ml.splits.map jF
  have hF_top : F = ⊤ := by
    by_contra hne
    exact hsf'.2 F hne hF_splits
  intro y
  have hy : y ∈ F := hF_top ▸ IntermediateField.mem_top
  exact hy

/-- Bundled `RingEquiv` and `AlgEquiv` companions to **Corollary 1** [to Theorem 7.5] (§7.2, p. 66):
any two splitting fields of `f ∈ K[X]` (or of `f` and `i(f)` along `i : K ≃+* K'`) are isomorphic
over `K`. -/
theorem corollary_1_to_theorem_7_5_equiv {K K' E E' : Type*}
    [Field K] [Field K'] [Field E] [Field E']
    [Algebra K E] [Algebra K' E']
    (i : K ≃+* K') (f : K[X])
    (hsf : IsGarlingSplittingFieldExtension K E f)
    (hsf' : IsGarlingSplittingFieldExtension K' E' (garlingMapPoly i.toRingHom f)) :
    ∃ j : E ≃+* E', ∀ k : K, j (algebraMap K E k) = algebraMap K' E' (i k) := by
  obtain ⟨j, hj_iso, hjk⟩ :=
    corollary_1_to_theorem_7_5 (i := i.toRingHom) ⟨i.injective, i.surjective⟩ f hsf hsf'
  exact ⟨RingEquiv.ofBijective j hj_iso, hjk⟩

theorem splitting_field_unique_up_to_algEquiv {K E₁ E₂ : Type*}
    [Field K] [Field E₁] [Field E₂] [Algebra K E₁] [Algebra K E₂] {f : K[X]}
    (hsf₁ : IsGarlingSplittingFieldExtension K E₁ f)
    (hsf₂ : IsGarlingSplittingFieldExtension K E₂ f) :
    Nonempty (E₁ ≃ₐ[K] E₂) := by
  have hsf₂' : IsGarlingSplittingFieldExtension K E₂ (garlingMapPoly (RingHom.id K) f) := by
    simpa [garlingMapPoly_apply, Polynomial.map_id] using hsf₂
  obtain ⟨j, hj_iso, hjk⟩ :=
    corollary_1_to_theorem_7_5 (i := RingHom.id K)
      ⟨Function.injective_id, Function.surjective_id⟩ f hsf₁ hsf₂'
  let e : E₁ ≃+* E₂ := RingEquiv.ofBijective j hj_iso
  exact ⟨AlgEquiv.ofRingEquiv (f := e) fun k => hjk k⟩

private theorem eq_of_monic_of_associated_field {K : Type*} [Field K] {p q : K[X]}
    (hp : p.Monic) (hq : q.Monic) (h : Associated p q) : p = q := by
  obtain ⟨r, hr⟩ := h.dvd
  have hr0 : r ≠ 0 := fun h0 => hq.ne_zero (by rw [hr, h0, mul_zero])
  have hdeg_le : q.natDegree ≤ p.natDegree :=
    Polynomial.natDegree_le_of_dvd h.symm.dvd hp.ne_zero
  have hsum : q.natDegree = p.natDegree + r.natDegree := by
    rw [hr, Polynomial.natDegree_mul hp.ne_zero hr0]
  have hr_deg0 : r.natDegree = 0 := by omega
  have hrc : r = Polynomial.C (r.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hr_deg0
  have hlc : r.coeff 0 = 1 := by
    have h1 := congrArg Polynomial.leadingCoeff hr
    rw [hq.leadingCoeff, Polynomial.leadingCoeff_mul, hp.leadingCoeff, one_mul,
      Polynomial.leadingCoeff, hr_deg0] at h1
    exact h1.symm
  rw [hr, hrc, hlc, map_one, mul_one]

/-- **Corollary 2** [to Theorem 7.5] (§7.2, printed p. 66 / PDF p. 74):
*"Suppose that `f ∈ K[x]` is irreducible and that `Σ:K` is a splitting field extension for `f`.
If `α` and `β` are roots of `f` in `Σ`, there is an automorphism `σ: Σ → Σ` such that `σ(α) = β`
and `σ` fixes `K`."* -/
theorem corollary_2_to_theorem_7_5 {K E : Type*} [Field K] [Field E] [Algebra K E]
    {f : K[X]} (hirr : Irreducible f)
    (hsf : IsGarlingSplittingFieldExtension K E f)
    {α β : E} (hα : Polynomial.aeval α f = 0) (hβ : Polynomial.aeval β f = 0) :
    ∃ σ : E →+* E,
      IsRingIsomorphism σ ∧ σ α = β ∧
      ∀ k : K, σ (algebraMap K E k) = algebraMap K E k := by
  have hf0 : f ≠ 0 := hirr.ne_zero
  have hα_alg : IsGarlingAlgebraic K α := ⟨f, hf0, hα⟩
  have hβ_alg : IsGarlingAlgebraic K β := ⟨f, hf0, hβ⟩
  have hintα : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp hα_alg
  have hintβ : IsIntegral K β := (isGarlingAlgebraic_iff_isIntegral K β).mp hβ_alg
  have hassα : Associated (minpoly K α) f :=
    (minpoly.irreducible hintα).associated_of_dvd hirr (minpoly.dvd K α hα)
  have hassβ : Associated (minpoly K β) f :=
    (minpoly.irreducible hintβ).associated_of_dvd hirr (minpoly.dvd K β hβ)
  have hmin_eq : minpoly K α = minpoly K β :=
    eq_of_monic_of_associated_field (minpoly.monic hintα) (minpoly.monic hintβ)
      (hassα.trans hassβ.symm)
  let Kα : IntermediateField K E := IntermediateField.adjoin K ({α} : Set E)
  let Kβ : IntermediateField K E := IntermediateField.adjoin K ({β} : Set E)
  let α₀ : Kα := IntermediateField.AdjoinSimple.gen K α
  let β₀ : Kβ := IntermediateField.AdjoinSimple.gen K β
  have hadj_α₀ : IntermediateField.adjoin K ({α₀} : Set Kα) = ⊤ := by
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    let L0 : IntermediateField K E := (IntermediateField.adjoin K ({α₀} : Set Kα)).map Kα.val
    have hα_mem : α ∈ L0 := ⟨α₀, IntermediateField.mem_adjoin_simple_self K α₀, rfl⟩
    have hle : Kα ≤ L0 :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hα_mem)
    obtain ⟨y, hy, hyx⟩ := hle x.2
    exact (Kα.val.injective hyx) ▸ hy
  have hadj_β₀ : IntermediateField.adjoin K ({β₀} : Set Kβ) = ⊤ := by
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    let L0 : IntermediateField K E := (IntermediateField.adjoin K ({β₀} : Set Kβ)).map Kβ.val
    have hβ_mem : β ∈ L0 := ⟨β₀, IntermediateField.mem_adjoin_simple_self K β₀, rfl⟩
    have hle : Kβ ≤ L0 :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hβ_mem)
    obtain ⟨y, hy, hyx⟩ := hle x.2
    exact (Kβ.val.injective hyx) ▸ hy
  have hα₀_alg : IsGarlingAlgebraic K α₀ :=
    ⟨f, hf0, Subtype.ext ((Polynomial.aeval_algHom_apply Kα.val α₀ f).symm.trans hα)⟩
  have hβ₀_alg : IsGarlingAlgebraic K β₀ :=
    ⟨f, hf0, Subtype.ext ((Polynomial.aeval_algHom_apply Kβ.val β₀ f).symm.trans hβ)⟩
  have hmin_α₀ : minpoly K α₀ = minpoly K α :=
    (minpoly.algHom_eq Kα.val Kα.val.injective α₀).symm
  have hmin_β₀ : minpoly K β₀ = minpoly K β :=
    (minpoly.algHom_eq Kβ.val Kβ.val.injective β₀).symm
  have hmap_min : garlingMapPoly (RingHom.id K) (minpoly K α₀) = minpoly K β₀ := by
    rw [garlingMapPoly_apply, Polynomial.map_id, hmin_α₀, hmin_eq, ← hmin_β₀]
  obtain ⟨τ, ⟨hτ_iso, hτ_gen, hτ_K⟩, _⟩ :=
    (corollary_1_to_theorem_7_4 hadj_α₀ hα₀_alg hadj_β₀ hβ₀_alg
      (i := RingHom.id K) ⟨Function.injective_id, Function.surjective_id⟩).2 hmap_min
  have hsf_ml : Polynomial.IsSplittingField K E f :=
    (isGarlingSplittingFieldExtension_iff K E f).mp hsf
  have _ : Polynomial.IsSplittingField K E f := hsf_ml
  let fα : Kα[X] := f.map (algebraMap K Kα)
  let fβ : Kβ[X] := f.map (algebraMap K Kβ)
  have hsf_α : IsGarlingSplittingFieldExtension Kα E fα := by
    rw [isGarlingSplittingFieldExtension_iff]
    exact Polynomial.IsSplittingField.map E f
  have hsf_β : IsGarlingSplittingFieldExtension Kβ E (garlingMapPoly τ fα) := by
    have hmap_τ : garlingMapPoly τ fα = fβ := by
      dsimp [fα, fβ, garlingMapPoly]
      rw [Polynomial.map_map]
      congr 1
      ext k
      exact congrArg Subtype.val (hτ_K k)
    rw [hmap_τ, isGarlingSplittingFieldExtension_iff]
    exact Polynomial.IsSplittingField.map E f
  obtain ⟨σ, hσ_iso, hσ_τ⟩ := corollary_1_to_theorem_7_5 hτ_iso fα hsf_α hsf_β
  refine ⟨σ, hσ_iso, ?_, ?_⟩
  · have h1 := hσ_τ α₀
    rw [hτ_gen] at h1
    exact h1
  · intro k
    have h1 := hσ_τ (algebraMap K Kα k)
    rw [hτ_K k] at h1
    exact h1

/-- Bundled `E ≃ₐ[K] E` and `IsGarlingIrreducible` companions to **Corollary 2** [to Theorem 7.5]
(§7.2, p. 66). -/
theorem corollary_2_to_theorem_7_5_algEquiv {K E : Type*} [Field K] [Field E] [Algebra K E]
    {f : K[X]} (hirr : Irreducible f)
    (hsf : IsGarlingSplittingFieldExtension K E f)
    {α β : E} (hα : Polynomial.aeval α f = 0) (hβ : Polynomial.aeval β f = 0) :
    ∃ σ : E ≃ₐ[K] E, σ α = β := by
  obtain ⟨σ, hσ_iso, hσα, hσK⟩ := corollary_2_to_theorem_7_5 hirr hsf hα hβ
  let e : E ≃+* E := RingEquiv.ofBijective σ hσ_iso
  exact ⟨AlgEquiv.ofRingEquiv (f := e) hσK, hσα⟩

theorem corollary_2_to_theorem_7_5_garling {K E : Type*} [Field K] [Field E] [Algebra K E]
    {f : K[X]} (hirr : IsGarlingIrreducible f)
    (hsf : IsGarlingSplittingFieldExtension K E f)
    {α β : E} (hα : Polynomial.aeval α f = 0) (hβ : Polynomial.aeval β f = 0) :
    ∃ σ : E ≃ₐ[K] E, σ α = β :=
  corollary_2_to_theorem_7_5_algEquiv ((isGarlingIrreducible_iff f).mp hirr) hsf hα hβ

/-- Quartic polynomial `f = x^4 - 2x^3 + 7x^2 - 6x + 12 ∈ ℚ[x]` of **Exercise 7.4**
(§7.2, printed p. 67 / PDF p. 75). -/
noncomputable def ex74Poly : ℚ[X] :=
  Polynomial.X ^ 4 - 2 * Polynomial.X ^ 3 + 7 * Polynomial.X ^ 2 - 6 * Polynomial.X + 12

/-- Complex roots `i√3` and `1 + i√3` of `ex74Poly` in **Exercise 7.4** (§7.2, p. 67). -/
noncomputable def ex74Root1 : ℂ := Complex.I * Real.sqrt 3
noncomputable def ex74Root2 : ℂ := 1 + Complex.I * Real.sqrt 3

/-- Splitting field `Σ ⊆ ℂ` of `ex74Poly` over `ℚ` inside `ℂ`. -/
noncomputable abbrev Ex74SplittingField : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (ex74Poly.rootSet ℂ)

/-- **Exercise 7.4** (§7.2, printed p. 67 / PDF p. 75):
*"The complex numbers `i√3` and `1 + i√3` are roots of the quartic `f = x^4 - 2x^3 + 7x^2 - 6x + 12`.
Does there exist an automorphism `σ` of the splitting field extension for `f` over `ℚ` with
`σ(i√3) = 1 + i√3`?"*

Answered in the negative: `f = (x^2 + 3)(x^2 - 2x + 4)`, both `i√3` and `1 + i√3` are roots of `f`
lying in the splitting field `Ex74SplittingField : ℚ` inside `ℂ`, and **no** automorphism (nor even
any ring endomorphism) `σ` of `Ex74SplittingField` maps `i√3` to `1 + i√3`. -/
theorem exercise_7_4 :
    ex74Poly = (Polynomial.X ^ 2 + 3) * (Polynomial.X ^ 2 - 2 * Polynomial.X + 4) ∧
    Polynomial.aeval ex74Root1 ex74Poly = 0 ∧
    Polynomial.aeval ex74Root2 ex74Poly = 0 ∧
    IsGarlingSplittingFieldExtension ℚ Ex74SplittingField ex74Poly ∧
    ∃ (r₁ r₂ : Ex74SplittingField),
      (r₁ : ℂ) = ex74Root1 ∧
      (r₂ : ℂ) = ex74Root2 ∧
      (¬ ∃ σ : Ex74SplittingField ≃ₐ[ℚ] Ex74SplittingField, σ r₁ = r₂) ∧
      (¬ ∃ σ : Ex74SplittingField →+* Ex74SplittingField, σ r₁ = r₂) := by
  have hfac : ex74Poly = (Polynomial.X ^ 2 + 3) * (Polynomial.X ^ 2 - 2 * Polynomial.X + 4) := by
    unfold ex74Poly
    ring
  have hsq3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hr1_quad : ex74Root1 ^ 2 + 3 = 0 := by
    unfold ex74Root1
    rw [mul_pow, Complex.I_sq, hsq3]
    ring
  have hr2_quad : ex74Root2 ^ 2 - 2 * ex74Root2 + 4 = 0 := by
    have hsub : ex74Root2 ^ 2 - 2 * ex74Root2 + 4 = ex74Root1 ^ 2 + 3 := by
      unfold ex74Root2 ex74Root1
      ring
    rw [hsub, hr1_quad]
  have hr1_eval : Polynomial.aeval ex74Root1 ex74Poly = 0 := by
    rw [hfac, map_mul]
    have h1 : Polynomial.aeval ex74Root1 (Polynomial.X ^ 2 + 3 : ℚ[X]) = ex74Root1 ^ 2 + 3 := by
      simp [map_ofNat]
    rw [h1, hr1_quad, zero_mul]
  have hr2_eval : Polynomial.aeval ex74Root2 ex74Poly = 0 := by
    rw [hfac, map_mul]
    have h2 : Polynomial.aeval ex74Root2 (Polynomial.X ^ 2 - 2 * Polynomial.X + 4 : ℚ[X]) =
        ex74Root2 ^ 2 - 2 * ex74Root2 + 4 := by
      simp [map_ofNat]
    rw [h2, hr2_quad, mul_zero]
  have hf_ne0 : ex74Poly ≠ 0 := by
    have hd : ex74Poly.natDegree = 4 := by unfold ex74Poly; compute_degree!
    exact Polynomial.ne_zero_of_natDegree_gt (n := 0) (by rw [hd]; decide)
  have hsf : IsGarlingSplittingFieldExtension ℚ Ex74SplittingField ex74Poly := by
    rw [isGarlingSplittingFieldExtension_iff]
    exact IntermediateField.adjoin_rootSet_isSplittingField
      (IsAlgClosed.splits (ex74Poly.map (algebraMap ℚ ℂ)))
  have hr1_mem : ex74Root1 ∈ Ex74SplittingField :=
    IntermediateField.subset_adjoin ℚ (ex74Poly.rootSet ℂ)
      (Polynomial.mem_rootSet.mpr ⟨hf_ne0, hr1_eval⟩)
  have hr2_mem : ex74Root2 ∈ Ex74SplittingField :=
    IntermediateField.subset_adjoin ℚ (ex74Poly.rootSet ℂ)
      (Polynomial.mem_rootSet.mpr ⟨hf_ne0, hr2_eval⟩)
  let r₁ : Ex74SplittingField := ⟨ex74Root1, hr1_mem⟩
  let r₂ : Ex74SplittingField := ⟨ex74Root2, hr2_mem⟩
  have hno_ringHom : ¬ ∃ σ : Ex74SplittingField →+* Ex74SplittingField, σ r₁ = r₂ := by
    rintro ⟨σ, hσ⟩
    have hr1_eq : r₁ ^ 2 + 3 = 0 := Subtype.ext (by push_cast; exact hr1_quad)
    have hr2_eq : r₂ ^ 2 + 3 = 0 := by
      have h := congrArg σ hr1_eq
      rw [map_add, map_pow, map_ofNat, map_zero, hσ] at h
      exact h
    have hr2_C : ex74Root2 ^ 2 + 3 = 0 := by
      have h := congrArg Subtype.val hr2_eq
      push_cast at h
      exact h
    have h1 : (1 : ℂ) + 2 * Complex.I * Real.sqrt 3 = 0 := by
      have hcalc : ex74Root2 ^ 2 + 3 = (1 : ℂ) + 2 * Complex.I * Real.sqrt 3 + (ex74Root1 ^ 2 + 3) := by
        unfold ex74Root2 ex74Root1
        ring
      rw [hr1_quad, add_zero] at hcalc
      exact hcalc.symm.trans hr2_C
    have hre := congrArg Complex.re h1
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hre
  have hno_algEquiv : ¬ ∃ σ : Ex74SplittingField ≃ₐ[ℚ] Ex74SplittingField, σ r₁ = r₂ := by
    rintro ⟨σ, hσ⟩
    exact hno_ringHom ⟨σ.toRingHom, hσ⟩
  exact ⟨hfac, hr1_eval, hr2_eval, hsf, r₁, r₂, rfl, rfl, hno_algEquiv, hno_ringHom⟩

/-! ## §7.3 Some examples (printed pp. 67–70 / PDF pp. 75–78) -/

open scoped IntermediateField

/-- Helper: if `f ≠ 0` splits explicitly over `L` with root tuple `α : Fin n → L` and
`F = K(α_1, ..., α_n)`, then `F : K` is a splitting field extension for `f`. -/
private theorem isGarlingSplittingFieldExtension_of_eq_adjoin_range
    {K L : Type*} [Field K] [Field L] [Algebra K L] {f : K[X]} (hf : f ≠ 0)
    {n : ℕ} {c : K} {α : Fin n → L} (hexp : GarlingSplitsExplicit K L f n c α)
    {F : IntermediateField K L} (hF : F = IntermediateField.adjoin K (Set.range α)) :
    IsGarlingSplittingFieldExtension K F f := by
  subst hF
  exact theorem_7_1 hf hexp

/-- Helper: if `f ≠ 0` splits explicitly over `L : K` with root tuple `α : Fin n → L` and
`IntermediateField.adjoin K (Set.range α) = ⊤`, then `L : K` itself is a splitting field extension
for `f`. -/
private theorem isGarlingSplittingFieldExtension_of_adjoin_range_eq_top
    {K L : Type*} [Field K] [Field L] [Algebra K L] {f : K[X]} (hf : f ≠ 0)
    {n : ℕ} {c : K} {α : Fin n → L} (hexp : GarlingSplitsExplicit K L f n c α)
    (htop : IntermediateField.adjoin K (Set.range α) = ⊤) :
    IsGarlingSplittingFieldExtension K L f := by
  rw [isGarlingSplittingFieldExtension_iff]
  have hroots : Set.range α = f.rootSet L := (garlingSplitsExplicit_props hf hexp).2.2.2
  have halg : ∀ x ∈ f.rootSet L, IsAlgebraic K x := fun x hx =>
    ⟨f, (Polynomial.mem_rootSet.mp hx).1, (Polynomial.mem_rootSet.mp hx).2⟩
  refine ⟨(garlingSplitsOver_iff_splits K L f).mp ⟨n, c, α, hexp⟩, ?_⟩
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, ← hroots, htop]
  rfl

/-- Helper: over the base field `K` itself, `K : K` is a splitting field extension for `f` iff `f`
splits over `K`. -/
private theorem isGarlingSplittingFieldExtension_self_iff (K : Type*) [Field K] (f : K[X]) :
    IsGarlingSplittingFieldExtension K K f ↔ GarlingSplitsOver K K f := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun M hMne _ => hMne ?_⟩⟩
  ext x
  simp only [IntermediateField.mem_top, iff_true]
  exact M.algebraMap_mem x

/-- Helper: `2 = 0` in `(ZMod 2)[X]`. -/
private theorem zmod2_poly_two_eq_zero : (2 : (ZMod 2)[X]) = 0 := by
  ext n
  have h1 : (2 : (ZMod 2)[X]) = Polynomial.C (2 : ZMod 2) := (map_ofNat Polynomial.C 2).symm
  rw [h1, show (2 : ZMod 2) = 0 by decide, map_zero]

/-- Helper: every element of `ZMod 2` is `0` or `1`. -/
private theorem zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

/-- Helper: any monic polynomial `Q ∈ F[X]` of degree `n` having `n` distinct roots `α : Fin n → F`
factors completely as `∏ i : Fin n, (X - C (α i))`. -/
private theorem monic_eq_prod_X_sub_C_of_roots {F : Type*} [Field F] {Q : F[X]} {n : ℕ}
    (hmon : Q.Monic) (hdeg : Q.natDegree = n) {α : Fin n → F}
    (hinj : Function.Injective α) (hroots : ∀ i : Fin n, Q.eval (α i) = 0) :
    Q = ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)) := by
  by_cases hn0 : n = 0
  · subst hn0
    rw [Polynomial.eq_one_of_monic_natDegree_zero hmon hdeg]
    simp
  · classical
    let P : F[X] := ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))
    have hP_mon : P.Monic :=
      Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (α i)
    have hP_deg : P.natDegree = n := by
      rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (α i)]
      simp
    by_contra hne
    have hQP0 : Q - P ≠ 0 := sub_ne_zero.mpr hne
    have hQP_deg : (Q - P).natDegree ≤ n - 1 := by
      refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
      rw [Polynomial.coeff_sub]
      by_cases hkn : k = n
      · subst hkn
        have hQ_lc : Q.coeff k = 1 := by
          rw [← hdeg]
          exact hmon.leadingCoeff
        have hP_lc : P.coeff k = 1 := by
          rw [← hP_deg]
          exact hP_mon.leadingCoeff
        rw [hQ_lc, hP_lc, sub_self]
      · have hkn_gt : n < k := by omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg ▸ hkn_gt),
          Polynomial.coeff_eq_zero_of_natDegree_lt (hP_deg ▸ hkn_gt), sub_self]
    let img : Finset F := Finset.univ.image α
    have himg_card : img.card = n := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
    have himg_sub : img ⊆ (Q - P).roots.toFinset := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      have hP_ev : P.eval (α i) = 0 := by
        rw [Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
      have hQP_root : (Q - P).IsRoot (α i) := by
        rw [Polynomial.IsRoot.def, Polynomial.eval_sub, hroots i, hP_ev, sub_self]
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQP0).mpr hQP_root)
    have h1 : img.card ≤ (Q - P).roots.toFinset.card := Finset.card_le_card himg_sub
    have h2 : (Q - P).roots.toFinset.card ≤ Multiset.card (Q - P).roots :=
      Multiset.toFinset_card_le _
    have h3 : Multiset.card (Q - P).roots ≤ (Q - P).natDegree := Polynomial.card_roots' (Q - P)
    omega

/-- Helper: every element of a degree-`2` simple algebraic intermediate field `K(α) ⊆ M` can be
written as `a + b * α` with `a, b ∈ K`. -/
private theorem exists_eq_add_mul_of_mem_adjoin_of_natDegree_eq_two
    {K M : Type*} [Field K] [Field M] [Algebra K M] {α : M}
    (hint : IsIntegral K α) (hdeg : (minpoly K α).natDegree = 2)
    {z : M} (hz : z ∈ IntermediateField.adjoin K ({α} : Set M)) :
    ∃ a b : K, z = algebraMap K M a + algebraMap K M b * α := by
  let pb := IntermediateField.adjoin.powerBasis hint
  have hdim : pb.dim = 2 := by rw [IntermediateField.adjoin.powerBasis_dim, hdeg]
  let zF : IntermediateField.adjoin K ({α} : Set M) := ⟨z, hz⟩
  have hsum := pb.basis.sum_repr zF
  let e : Fin 2 ≃ Fin pb.dim := finCongr hdim.symm
  rw [← Equiv.sum_comp e, Fin.sum_univ_two] at hsum
  refine ⟨pb.basis.repr zF (e 0), pb.basis.repr zF (e 1), ?_⟩
  have h0 : (pb.basis (e 0) : M) = 1 := by
    rw [pb.basis_eq_pow, IntermediateField.adjoin.powerBasis_gen]
    simp [e]
  have h1 : (pb.basis (e 1) : M) = α := by
    rw [pb.basis_eq_pow, IntermediateField.adjoin.powerBasis_gen]
    simp [e]
  have hval := congrArg Subtype.val hsum.symm
  rw [Algebra.smul_def, Algebra.smul_def] at hval
  push_cast at hval
  rw [h0, h1, mul_one] at hval
  exact hval

/-- Helper: if `β ∈ M` is a root of a monic quadratic `p ∈ F[X]` and `β ∉ F`, then
`[F(β) : F] = 2` and `minpoly F β = p`. -/
private theorem minpoly_and_finrank_eq_two_of_aeval_deg_two_of_not_mem
    {F M : Type*} [Field F] [Field M] [Algebra F M] {β : M} {p : F[X]}
    (hp_mon : p.Monic) (hp_deg : p.natDegree = 2) (hp_eval : Polynomial.aeval β p = 0)
    (hnot : ∀ x : F, algebraMap F M x ≠ β) :
    minpoly F β = p ∧ Module.finrank F (IntermediateField.adjoin F ({β} : Set M)) = 2 := by
  have hint : IsIntegral F β := ⟨p, hp_mon, hp_eval⟩
  have hdvd : minpoly F β ∣ p := minpoly.dvd F β hp_eval
  have hle2 : (minpoly F β).natDegree ≤ 2 :=
    hp_deg ▸ Polynomial.natDegree_le_of_dvd hdvd hp_mon.ne_zero
  have hpos : 0 < (minpoly F β).natDegree := minpoly.natDegree_pos hint
  have hne1 : (minpoly F β).natDegree ≠ 1 := by
    intro h1
    have hlin : minpoly F β = Polynomial.X + Polynomial.C ((minpoly F β).coeff 0) := by
      have heq := Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq h1)
      have hlc : (minpoly F β).coeff 1 = 1 := by
        rw [← h1]
        exact (minpoly.monic hint).leadingCoeff
      simpa [hlc] using heq
    have hev := minpoly.aeval F β
    rw [hlin, map_add, Polynomial.aeval_X, Polynomial.aeval_C] at hev
    have hβ_eq : algebraMap F M (-((minpoly F β).coeff 0)) = β := by
      rw [map_neg]
      linear_combination -hev
    exact hnot (-((minpoly F β).coeff 0)) hβ_eq
  have hm_deg : (minpoly F β).natDegree = 2 := by omega
  obtain ⟨r, hr⟩ := hdvd
  have hr0 : r ≠ 0 := fun h0 => hp_mon.ne_zero (by rw [hr, h0, mul_zero])
  have hsum : p.natDegree = (minpoly F β).natDegree + r.natDegree := by
    rw [hr, Polynomial.natDegree_mul (minpoly.ne_zero hint) hr0]
  have hr_deg0 : r.natDegree = 0 := by omega
  have hrc : r = Polynomial.C (r.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hr_deg0
  have hlc : r.coeff 0 = 1 := by
    have h1 := congrArg Polynomial.leadingCoeff hr
    rw [hp_mon.leadingCoeff, Polynomial.leadingCoeff_mul, (minpoly.monic hint).leadingCoeff,
      one_mul, Polynomial.leadingCoeff, hr_deg0] at h1
    exact h1.symm
  have hm_eq : minpoly F β = p := by
    rw [hr, hrc, hlc, map_one, mul_one]
  exact ⟨hm_eq, by rw [IntermediateField.adjoin.finrank hint, hm_deg]⟩

/-- Helper: a monic polynomial `p ∈ F[X]` of degree `2` or `3` with no roots in `F` is irreducible
over `F`. -/
private theorem irreducible_of_monic_deg_two_or_three_of_no_roots
    {F : Type*} [Field F] {p : F[X]} (hmon : p.Monic)
    (hdeg : p.natDegree = 2 ∨ p.natDegree = 3) (hno : ∀ a : F, p.eval a ≠ 0) :
    Irreducible p := by
  rw [irreducible_iff]
  refine ⟨fun hu => ?_, fun g h hgh => ?_⟩
  · have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rcases hdeg with hd | hd <;> omega
  · by_cases hg0 : g.natDegree = 0
    · exact Or.inl (Polynomial.isUnit_iff.mpr
        ⟨g.coeff 0, isUnit_iff_ne_zero.mpr fun hc0 => hmon.ne_zero (by
          rw [hgh, Polynomial.eq_C_of_natDegree_eq_zero hg0, hc0, map_zero, zero_mul]),
          (Polynomial.eq_C_of_natDegree_eq_zero hg0).symm⟩)
    · by_cases hh0 : h.natDegree = 0
      · exact Or.inr (Polynomial.isUnit_iff.mpr
          ⟨h.coeff 0, isUnit_iff_ne_zero.mpr fun hc0 => hmon.ne_zero (by
            rw [hgh, Polynomial.eq_C_of_natDegree_eq_zero hh0, hc0, map_zero, mul_zero]),
            (Polynomial.eq_C_of_natDegree_eq_zero hh0).symm⟩)
      · have hg_ne : g ≠ 0 := fun h0 => hmon.ne_zero (by rw [hgh, h0, zero_mul])
        have hh_ne : h ≠ 0 := fun h0 => hmon.ne_zero (by rw [hgh, h0, mul_zero])
        have hsum : p.natDegree = g.natDegree + h.natDegree := by
          rw [hgh, Polynomial.natDegree_mul hg_ne hh_ne]
        have hdeg1 : g.natDegree = 1 ∨ h.natDegree = 1 := by
          rcases hdeg with hd | hd <;> omega
        rcases hdeg1 with hg1 | hh1
        · have hroot : g.eval (-g.coeff 0 / g.coeff 1) = 0 := by
            have hlc : g.coeff 1 ≠ 0 := by rw [← hg1]; exact Polynomial.leadingCoeff_ne_zero.mpr hg_ne
            rw [Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq hg1)]
            simp [div_eq_mul_inv]
            field_simp [hlc]
            ring
          exact False.elim (hno (-g.coeff 0 / g.coeff 1)
            (by rw [hgh, Polynomial.eval_mul, hroot, zero_mul]))
        · have hroot : h.eval (-h.coeff 0 / h.coeff 1) = 0 := by
            have hlc : h.coeff 1 ≠ 0 := by rw [← hh1]; exact Polynomial.leadingCoeff_ne_zero.mpr hh_ne
            rw [Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq hh1)]
            simp [div_eq_mul_inv]
            field_simp [hlc]
            ring
          exact False.elim (hno (-h.coeff 0 / h.coeff 1)
            (by rw [hgh, Polynomial.eval_mul, hroot, mul_zero]))

/-! ### §7.3 Example 1: `f = x^p - 2 ∈ ℚ[x]` (`p` prime) (printed pp. 67–68 / PDF pp. 75–76) -/

/-- Positive real `n`-th root `2^{1/n}` viewed in `ℂ` (§7.3 `Example 1`, p. 67; recalled in Ch. 20
p. 160). -/
noncomputable def twoPowInvNat (n : ℕ) : ℂ :=
  ((2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) : ℝ)

/-- Standard complex primitive `n`-th root of unity `exp(2πi / n)` (§7.3 `Example 1`, p. 67). -/
noncomputable def primRootOfUnityComplex (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))

/-- For any prime `p`, `primRootOfUnityComplex p` satisfies `ω^p = 1` and `ω ≠ 1`. -/
theorem primRootOfUnityComplex_spec {p : ℕ} (hp : Nat.Prime p) :
    (primRootOfUnityComplex p) ^ p = 1 ∧ primRootOfUnityComplex p ≠ 1 := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpow : (primRootOfUnityComplex p) ^ p = 1 := by
    unfold primRootOfUnityComplex
    rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ hpC, Complex.exp_two_pi_mul_I]
  refine ⟨hpow, fun h1 => ?_⟩
  unfold primRootOfUnityComplex at h1
  rw [Complex.exp_eq_one_iff] at h1
  obtain ⟨k, hk⟩ := h1
  have h2piI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hdiv : (1 : ℂ) / (p : ℂ) = (k : ℂ) := by
    apply mul_right_cancel₀ h2piI
    calc (1 : ℂ) / (p : ℂ) * (2 * Real.pi * Complex.I)
        = 2 * Real.pi * Complex.I / (p : ℂ) := by ring
      _ = (k : ℂ) * (2 * Real.pi * Complex.I) := hk
  have hkpC : (k : ℂ) * (p : ℂ) = 1 := by
    calc (k : ℂ) * (p : ℂ) = (1 / (p : ℂ)) * (p : ℂ) := by rw [hdiv]
      _ = 1 := one_div_mul_cancel hpC
  have hkpZ : k * (p : ℤ) = 1 := by exact_mod_cast hkpC
  have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  have hk_pos : 0 < k := by nlinarith
  nlinarith

private theorem X_sub_one_mul_garlingPrimeCyclotomicRat (k : ℕ) :
    (Polynomial.X - 1) * garlingPrimeCyclotomicRat k = (Polynomial.X : ℚ[X]) ^ k - 1 := by
  unfold garlingPrimeCyclotomicRat
  induction k with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

private theorem garlingPrimeCyclotomicRat_monic_and_natDegree {p : ℕ} (hp : Nat.Prime p) :
    (garlingPrimeCyclotomicRat p).Monic ∧ (garlingPrimeCyclotomicRat p).natDegree = p - 1 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hcoeff : ∀ k : ℕ, (garlingPrimeCyclotomicRat p).coeff k = if k < p then 1 else 0 := by
    intro k
    unfold garlingPrimeCyclotomicRat
    rw [Polynomial.finsetSum_coeff]
    by_cases hk : k < p
    · rw [Finset.sum_eq_single k]
      · simp [hk, Polynomial.coeff_X_pow]
      · intro j _ hjk; simp [Polynomial.coeff_X_pow, Ne.symm hjk]
      · intro habs; exact absurd (Finset.mem_range.mpr hk) habs
    · simp only [hk, ↓reduceIte]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjk : k ≠ j := by have := Finset.mem_range.mp hj; omega
      simp [Polynomial.coeff_X_pow, hjk]
  have hle : (garlingPrimeCyclotomicRat p).natDegree ≤ p - 1 := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
    rw [hcoeff k]
    have hnot : ¬ k < p := by omega
    simp [hnot]
  have htop : (garlingPrimeCyclotomicRat p).coeff (p - 1) = 1 := by
    rw [hcoeff (p - 1)]
    have hlt : p - 1 < p := by omega
    simp [hlt]
  have hdeg : (garlingPrimeCyclotomicRat p).natDegree = p - 1 :=
    le_antisymm hle (Polynomial.le_natDegree_of_ne_zero (htop ▸ one_ne_zero))
  exact ⟨by rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg, htop], hdeg⟩

/-- **§7.3 Example 1** (printed pp. 67–68 / PDF pp. 75–76; recalled in Ch. 20 p. 160):
For any prime `p` and any root `ω ∈ ℂ` of `x^p - 1` with `ω ≠ 1` (for instance
`primRootOfUnityComplex p`), with `r = twoPowInvNat p = 2^{1/p}`:
1. `x^p - 2` is irreducible in `ℚ[x]`, has minimal polynomial `minpoly ℚ r = x^p - 2`, and
   `[ℚ(2^{1/p}) : ℚ] = p`;
2. `x^p - 1 = (x - 1)(x^{p-1} + ... + 1)`, `garlingPrimeCyclotomicRat p` is irreducible over `ℚ`,
   `minpoly ℚ ω = garlingPrimeCyclotomicRat p`, `[ℚ(ω) : ℚ] = p - 1`, and `ℚ(ω) : ℚ` is a
   splitting field extension for `x^p - 1`;
3. `ℚ(ω, 2^{1/p}) : ℚ` is a splitting field extension for `x^p - 2` of degree
   `[ℚ(ω, 2^{1/p}) : ℚ] = p(p - 1)`, and `x^p - 2` remains irreducible over `ℚ(ω)`. -/
theorem example_7_3_1 {p : ℕ} (hp : Nat.Prime p) {ω : ℂ} (hω_pow : ω ^ p = 1) (hω_ne1 : ω ≠ 1) :
    let r : ℂ := twoPowInvNat p
    let E : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({ω, r} : Set ℂ)
    Irreducible (Polynomial.X ^ p - 2 : ℚ[X]) ∧
    minpoly ℚ r = Polynomial.X ^ p - 2 ∧
    Module.finrank ℚ ℚ⟮r⟯ = p ∧
    (Polynomial.X ^ p - 1 : ℚ[X]) = (Polynomial.X - 1) * garlingPrimeCyclotomicRat p ∧
    Irreducible (garlingPrimeCyclotomicRat p) ∧
    minpoly ℚ ω = garlingPrimeCyclotomicRat p ∧
    Module.finrank ℚ ℚ⟮ω⟯ = p - 1 ∧
    IsGarlingSplittingFieldExtension ℚ ℚ⟮ω⟯ (Polynomial.X ^ p - 1) ∧
    IsGarlingSplittingFieldExtension ℚ E (Polynomial.X ^ p - 2) ∧
    Module.finrank ℚ E = p * (p - 1) ∧
    extDegree ℚ E = ((p * (p - 1) : ℕ) : ℕ∞) ∧
    Irreducible (Polynomial.X ^ p - 2 : ℚ⟮ω⟯[X]) := by
  intro r E
  have hp2 : 2 ≤ p := hp.two_le
  -- 1. `r = 2^{1/p}` and `X^p - 2` over `ℚ`.
  have hf_eq : (Polynomial.X ^ p - 2 : ℚ[X]) = Polynomial.X ^ p - Polynomial.C ((2 : ℕ) : ℚ) := by
    norm_num
    rw [map_ofNat]
  have hf_irr : Irreducible (Polynomial.X ^ p - 2 : ℚ[X]) := by
    rw [hf_eq]
    exact (exercise_5_7 Nat.prime_two hp.pos).1
  obtain ⟨hr0_pow, _, hr0_min, _⟩ :=
    real_rpow_inv_nat_minpoly_of_prime Nat.prime_two hp.pos
  let r₀ : ℝ := (2 : ℝ) ^ ((1 : ℝ) / (p : ℝ))
  have hr0_eq : ((2 : ℕ) : ℝ) ^ ((1 : ℝ) / (p : ℝ)) = r₀ := by
    simp [r₀]
  rw [hr0_eq] at hr0_pow hr0_min
  have hr_coe : (IsScalarTower.toAlgHom ℚ ℝ ℂ) r₀ = r := rfl
  have hr_pow : r ^ p = 2 := by
    change ((r₀ : ℂ) ^ p) = 2
    rw [← Complex.ofReal_pow, hr0_pow]
    norm_num
  have hr_ne0 : r ≠ 0 := fun h0 => by
    rw [h0, zero_pow hp.ne_zero] at hr_pow
    norm_num at hr_pow
  have hr_min : minpoly ℚ r = Polynomial.X ^ p - 2 := by
    rw [← hr_coe, minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ ℝ ℂ) Complex.ofReal_injective r₀,
      hr0_min]
    norm_num
    rw [map_ofNat]
  have hr_int : IsIntegral ℚ r :=
    ⟨Polynomial.X ^ p - Polynomial.C 2, Polynomial.monic_X_pow_sub_C (2 : ℚ) hp.ne_zero, by
      simp [hr_pow]⟩
  have hfin_r : Module.finrank ℚ ℚ⟮r⟯ = p := by
    rw [IntermediateField.adjoin.finrank hr_int, hr_min, ← map_ofNat Polynomial.C 2,
      Polynomial.natDegree_X_pow_sub_C]
  -- 2. `ω`, `garlingPrimeCyclotomicRat p`, and splitting field of `X^p - 1`.
  have hcyc_fac :
      (Polynomial.X ^ p - 1 : ℚ[X]) = (Polynomial.X - 1) * garlingPrimeCyclotomicRat p :=
    (X_sub_one_mul_garlingPrimeCyclotomicRat p).symm
  have hcyc_irr : Irreducible (garlingPrimeCyclotomicRat p) := (exercise_5_11 hp).1
  obtain ⟨hcyc_mon, hcyc_deg⟩ := garlingPrimeCyclotomicRat_monic_and_natDegree hp
  have hω_cyc : Polynomial.aeval ω (garlingPrimeCyclotomicRat p) = 0 := by
    have hev := congrArg (Polynomial.aeval ω) hcyc_fac
    rw [map_sub, map_pow, map_one, Polynomial.aeval_X, hω_pow, sub_self, map_mul, map_sub,
      map_one, Polynomial.aeval_X] at hev
    exact (mul_eq_zero.mp hev.symm).resolve_left (sub_ne_zero.mpr hω_ne1)
  have hω_int : IsIntegral ℚ ω := ⟨garlingPrimeCyclotomicRat p, hcyc_mon, hω_cyc⟩
  have hω_min : minpoly ℚ ω = garlingPrimeCyclotomicRat p :=
    (minpoly.eq_of_irreducible_of_monic hcyc_irr hω_cyc hcyc_mon).symm
  have hfin_ω : Module.finrank ℚ ℚ⟮ω⟯ = p - 1 := by
    rw [IntermediateField.adjoin.finrank hω_int, hω_min, hcyc_deg]
  have hω_ne0 : ω ≠ 0 := fun h0 => by
    rw [h0, zero_pow hp.ne_zero] at hω_pow
    exact zero_ne_one hω_pow
  have hord : orderOf ω = p := by
    rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hω_pow) with h1 | hp_eq
    · exact False.elim (hω_ne1 (orderOf_eq_one_iff.mp h1))
    · exact hp_eq
  have hω_inj : Function.Injective (fun k : Fin p => ω ^ (k : ℕ)) := by
    intro i j hij
    dsimp at hij
    rcases le_total (i : ℕ) (j : ℕ) with hle | hle
    · have hsub : ω ^ ((j : ℕ) - (i : ℕ)) = 1 := by
        apply mul_left_cancel₀ (pow_ne_zero (i : ℕ) hω_ne0)
        rw [← pow_add, Nat.add_sub_of_le hle, mul_one, hij]
      have hdvd' : orderOf ω ∣ ((j : ℕ) - (i : ℕ)) := orderOf_dvd_of_pow_eq_one hsub
      have hdvd : p ∣ ((j : ℕ) - (i : ℕ)) := by rwa [hord] at hdvd'
      have hz : (j : ℕ) - (i : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      exact Fin.ext (by omega)
    · have hsub : ω ^ ((i : ℕ) - (j : ℕ)) = 1 := by
        apply mul_left_cancel₀ (pow_ne_zero (j : ℕ) hω_ne0)
        rw [← pow_add, Nat.add_sub_of_le hle, mul_one, hij]
      have hdvd' : orderOf ω ∣ ((i : ℕ) - (j : ℕ)) := orderOf_dvd_of_pow_eq_one hsub
      have hdvd : p ∣ ((i : ℕ) - (j : ℕ)) := by rwa [hord] at hdvd'
      have hz : (i : ℕ) - (j : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      exact Fin.ext (by omega)
  let α₁ : Fin p → ℂ := fun k => ω ^ (k : ℕ)
  have hexp₁ : GarlingSplitsExplicit ℚ ℂ (Polynomial.X ^ p - 1) p 1 α₁ := by
    unfold GarlingSplitsExplicit
    have hmap : (Polynomial.X ^ p - 1 : ℚ[X]).map (algebraMap ℚ ℂ) =
        Polynomial.X ^ p - Polynomial.C 1 := by
      simp
    rw [hmap]
    simp only [map_one, one_mul]
    refine monic_eq_prod_X_sub_C_of_roots (Polynomial.monic_X_pow_sub_C 1 hp.ne_zero)
      Polynomial.natDegree_X_pow_sub_C
      hω_inj fun k => ?_
    simp only [α₁, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [← pow_mul, mul_comm (k : ℕ) p, pow_mul, hω_pow, one_pow, sub_self]
  have hadj₁ : ℚ⟮ω⟯ = IntermediateField.adjoin ℚ (Set.range α₁) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact IntermediateField.subset_adjoin ℚ (Set.range α₁)
        ⟨⟨1, hp.one_lt⟩, by simp [α₁]⟩
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨k, rfl⟩
      exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ ω) (k : ℕ)
  have hsf_ω : IsGarlingSplittingFieldExtension ℚ ℚ⟮ω⟯ (Polynomial.X ^ p - 1) :=
    isGarlingSplittingFieldExtension_of_eq_adjoin_range
      (by rw [← map_one Polynomial.C]; exact (Polynomial.monic_X_pow_sub_C (1 : ℚ) hp.ne_zero).ne_zero)
      hexp₁ hadj₁
  -- 3. Splitting field `E = ℚ(ω, 2^{1/p})` of `X^p - 2`, degree `p(p - 1)`, and irreducibility.
  let α₂ : Fin p → ℂ := fun k => ω ^ (k : ℕ) * r
  have hα₂_inj : Function.Injective α₂ := fun i j hij =>
    hω_inj (mul_right_cancel₀ hr_ne0 hij)
  have hexp₂ : GarlingSplitsExplicit ℚ ℂ (Polynomial.X ^ p - 2) p 1 α₂ := by
    unfold GarlingSplitsExplicit
    have hmap : (Polynomial.X ^ p - 2 : ℚ[X]).map (algebraMap ℚ ℂ) =
        Polynomial.X ^ p - Polynomial.C 2 := by
      simp [map_ofNat]
    rw [hmap]
    simp only [map_one, one_mul]
    refine monic_eq_prod_X_sub_C_of_roots (Polynomial.monic_X_pow_sub_C 2 hp.ne_zero)
      Polynomial.natDegree_X_pow_sub_C
      hα₂_inj fun k => ?_
    simp only [α₂, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [mul_pow, ← pow_mul, mul_comm (k : ℕ) p, pow_mul, hω_pow, one_pow, one_mul, hr_pow,
      sub_self]
  have hadj₂ : E = IntermediateField.adjoin ℚ (Set.range α₂) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hzw | hzr
      · rw [hzw]
        have hr_mem : r ∈ IntermediateField.adjoin ℚ (Set.range α₂) :=
          IntermediateField.subset_adjoin ℚ (Set.range α₂) ⟨⟨0, hp.pos⟩, by simp [α₂]⟩
        have hωr_mem : ω * r ∈ IntermediateField.adjoin ℚ (Set.range α₂) :=
          IntermediateField.subset_adjoin ℚ (Set.range α₂) ⟨⟨1, hp.one_lt⟩, by simp [α₂]⟩
        have hdiv : (ω * r) / r = ω := mul_div_cancel_right₀ ω hr_ne0
        exact hdiv ▸ div_mem hωr_mem hr_mem
      · rw [hzr]
        exact IntermediateField.subset_adjoin ℚ (Set.range α₂) ⟨⟨0, hp.pos⟩, by simp [α₂]⟩
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨k, rfl⟩
      have hωE : ω ∈ E := IntermediateField.subset_adjoin ℚ ({ω, r} : Set ℂ) (by simp)
      have hrE : r ∈ E := IntermediateField.subset_adjoin ℚ ({ω, r} : Set ℂ) (by simp)
      exact mul_mem (pow_mem hωE (k : ℕ)) hrE
  have hsf_E : IsGarlingSplittingFieldExtension ℚ E (Polynomial.X ^ p - 2) :=
    isGarlingSplittingFieldExtension_of_eq_adjoin_range hf_irr.ne_zero hexp₂ hadj₂
  have hE_fin : Module.Finite ℚ E :=
    (isFiniteExtension_iff_moduleFinite ℚ E).mp (corollary_to_theorem_7_1 hsf_E).1
  -- Tower bounds via `ℚ ⊆ ℚ(r) ⊆ E` and `ℚ ⊆ ℚ(ω) ⊆ ℚ(ω)(r) = E`.
  have hle_r : ℚ⟮r⟯ ≤ E := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin ℚ ({ω, r} : Set ℂ) (by simp)
  have hp_dvd : p ∣ Module.finrank ℚ E := by
    let _ : Algebra ℚ⟮r⟯ E := (IntermediateField.inclusion hle_r).toAlgebra
    have _ : IsScalarTower ℚ ℚ⟮r⟯ E := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hmul := Module.finrank_mul_finrank ℚ ℚ⟮r⟯ E
    exact ⟨Module.finrank ℚ⟮r⟯ E, by rw [← hmul, hfin_r]⟩
  let Kω : IntermediateField ℚ ℂ := ℚ⟮ω⟯
  let Eω : IntermediateField Kω ℂ := IntermediateField.adjoin Kω ({r} : Set ℂ)
  have hEω_eq : Eω.restrictScalars ℚ = E := by
    apply le_antisymm
    · intro z hz
      have hKω_le : Kω ≤ E := by
        rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact IntermediateField.subset_adjoin ℚ ({ω, r} : Set ℂ) (by simp)
      let E_over_Kω : IntermediateField Kω ℂ :=
        { E.toSubfield with algebraMap_mem' := fun x => hKω_le x.2 }
      have hr_mem : r ∈ E_over_Kω :=
        IntermediateField.subset_adjoin ℚ ({ω, r} : Set ℂ) (by simp)
      have hle_Kω : Eω ≤ E_over_Kω :=
        IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hr_mem)
      exact hle_Kω hz
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hzw | hzr
      · rw [hzw]
        exact Eω.algebraMap_mem ⟨ω, IntermediateField.mem_adjoin_simple_self ℚ ω⟩
      · rw [hzr]
        exact IntermediateField.mem_adjoin_simple_self Kω r
  have hr_int_Kω : IsIntegral Kω r :=
    ⟨Polynomial.X ^ p - Polynomial.C 2, Polynomial.monic_X_pow_sub_C (2 : Kω) hp.ne_zero, by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
        map_ofNat, hr_pow, sub_self]⟩
  have hmin_Kω_dvd : minpoly Kω r ∣ (Polynomial.X ^ p - 2 : Kω[X]) :=
    minpoly.dvd Kω r (by rw [map_sub, map_pow, Polynomial.aeval_X, map_ofNat, hr_pow, sub_self])
  have hmin_Kω_le : (minpoly Kω r).natDegree ≤ p := by
    have hd : (Polynomial.X ^ p - 2 : Kω[X]).natDegree = p := by
      rw [← map_ofNat Polynomial.C 2, Polynomial.natDegree_X_pow_sub_C]
    exact hd ▸ Polynomial.natDegree_le_of_dvd hmin_Kω_dvd
      (Polynomial.monic_X_pow_sub_C (2 : Kω) hp.ne_zero).ne_zero
  have hfin_Eω : Module.finrank Kω Eω = (minpoly Kω r).natDegree :=
    IntermediateField.adjoin.finrank hr_int_Kω
  have htower_ω : (p - 1) * (minpoly Kω r).natDegree = Module.finrank ℚ E := by
    have hmul : Module.finrank ℚ Kω * Module.finrank Kω Eω =
        Module.finrank ℚ (Eω.restrictScalars ℚ) :=
      Module.finrank_mul_finrank ℚ Kω Eω
    rw [hfin_ω, hfin_Eω, hEω_eq] at hmul
    exact hmul
  have hp1_dvd : (p - 1) ∣ Module.finrank ℚ E := ⟨(minpoly Kω r).natDegree, htower_ω.symm⟩
  have hcop : Nat.Coprime p (p - 1) := by
    have h1 : p = (p - 1) + 1 := by omega
    rw [h1]
    exact Nat.coprime_self_add_left.mpr (Nat.coprime_one_left (p - 1))
  have hprod_dvd : p * (p - 1) ∣ Module.finrank ℚ E :=
    hcop.mul_dvd_of_dvd_of_dvd hp_dvd hp1_dvd
  have hE_pos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hge : p * (p - 1) ≤ Module.finrank ℚ E := Nat.le_of_dvd hE_pos hprod_dvd
  have hle : Module.finrank ℚ E ≤ p * (p - 1) := by
    have h1 : (p - 1) * (minpoly Kω r).natDegree ≤ (p - 1) * p :=
      Nat.mul_le_mul_left (p - 1) hmin_Kω_le
    rw [htower_ω, mul_comm (p - 1) p] at h1
    exact h1
  have hfin_E : Module.finrank ℚ E = p * (p - 1) := le_antisymm hle hge
  have hext_E : extDegree ℚ E = ((p * (p - 1) : ℕ) : ℕ∞) := by
    rw [extDegree_eq_finrank ℚ E, hfin_E]
  have hmin_Kω_deg : (minpoly Kω r).natDegree = p := by
    have h1 : (p - 1) * (minpoly Kω r).natDegree = (p - 1) * p := by
      rw [htower_ω, hfin_E, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (by omega) h1
  have hirr_Kω : Irreducible (Polynomial.X ^ p - 2 : Kω[X]) := by
    obtain ⟨q, hq⟩ := hmin_Kω_dvd
    have hmonP : (Polynomial.X ^ p - 2 : Kω[X]).Monic := by
      rw [← map_ofNat Polynomial.C 2]
      exact Polynomial.monic_X_pow_sub_C (2 : Kω) hp.ne_zero
    have hq0 : q ≠ 0 := fun h0 => hmonP.ne_zero (by rw [hq, h0, mul_zero])
    have hsum : (Polynomial.X ^ p - 2 : Kω[X]).natDegree =
        (minpoly Kω r).natDegree + q.natDegree := by
      rw [hq, Polynomial.natDegree_mul (minpoly.ne_zero hr_int_Kω) hq0]
    have hdP : (Polynomial.X ^ p - 2 : Kω[X]).natDegree = p := by
      rw [← map_ofNat Polynomial.C 2, Polynomial.natDegree_X_pow_sub_C]
    have hq_deg0 : q.natDegree = 0 := by omega
    have hqc : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hq_deg0
    have hlc : q.coeff 0 = 1 := by
      have h1 := congrArg Polynomial.leadingCoeff hq
      rw [hmonP.leadingCoeff, Polynomial.leadingCoeff_mul,
        (minpoly.monic hr_int_Kω).leadingCoeff, one_mul, Polynomial.leadingCoeff, hq_deg0] at h1
      exact h1.symm
    have hmin_eq_P : minpoly Kω r = (Polynomial.X ^ p - 2 : Kω[X]) := by
      rw [hq, hqc, hlc, map_one, mul_one]
    exact hmin_eq_P ▸ minpoly.irreducible hr_int_Kω
  exact ⟨hf_irr, hr_min, hfin_r, hcyc_fac, hcyc_irr, hω_min, hfin_ω, hsf_ω, hsf_E,
    hfin_E, hext_E, hirr_Kω⟩

/-! ### §7.3 Examples 2 & 3: `x^6 - 1` and `x^6 + 1` in `ℚ[x]` (printed pp. 68–69 / PDF pp. 76–77) -/

/-- Primitive cube root of unity `ω = -1/2 + (√3 / 2) i ∈ ℂ` used in §7.3 `Examples 2–3`
(printed pp. 68–69). -/
noncomputable def omegaCubeRoot : ℂ :=
  -1 / 2 + ((Real.sqrt 3 : ℝ) : ℂ) / 2 * Complex.I

theorem omegaCubeRoot_props :
    omegaCubeRoot ^ 2 + omegaCubeRoot + 1 = 0 ∧
    omegaCubeRoot ^ 3 = 1 ∧
    omegaCubeRoot ≠ 1 := by
  have hsq3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hquad : omegaCubeRoot ^ 2 + omegaCubeRoot + 1 = 0 := by
    have hcalc : omegaCubeRoot ^ 2 + omegaCubeRoot + 1 =
        (1 / 4 : ℂ) * (((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * Complex.I ^ 2 + 3) := by
      unfold omegaCubeRoot
      ring
    rw [hcalc, hsq3, Complex.I_sq]
    norm_num
  have hcube : omegaCubeRoot ^ 3 = 1 := by
    linear_combination (omegaCubeRoot - 1) * hquad
  have hne1 : omegaCubeRoot ≠ 1 := by
    intro h1
    have him := congrArg Complex.im h1
    unfold omegaCubeRoot at him
    simp [Complex.add_im, Complex.mul_im] at him
  exact ⟨hquad, hcube, hne1⟩

/-- **§7.3 Example 2** (printed p. 68 / PDF p. 76):
`f = x^6 - 1 ∈ ℚ[x]` factorizes as `(x - 1)(x^2 + x + 1)(x + 1)(x^2 - x + 1)`, splits over `ℚ(ω)`
(where `ω = omegaCubeRoot`) as `(x - 1)(x - ω)(x - ω^2)(x + 1)(x + ω)(x + ω^2)`, and `ℚ(ω) : ℚ`
is a splitting field extension for `x^6 - 1` with `[ℚ(ω) : ℚ] = 2`. -/
theorem example_7_3_2 :
    let ω : ℂ := omegaCubeRoot
    (Polynomial.X ^ 6 - 1 : ℚ[X]) =
      (Polynomial.X - 1) * (Polynomial.X ^ 2 + Polynomial.X + 1) *
      (Polynomial.X + 1) * (Polynomial.X ^ 2 - Polynomial.X + 1) ∧
    IsGarlingSplittingFieldExtension ℚ ℚ⟮ω⟯ (Polynomial.X ^ 6 - 1) ∧
    Module.finrank ℚ ℚ⟮ω⟯ = 2 ∧
    extDegree ℚ ℚ⟮ω⟯ = 2 := by
  intro ω
  obtain ⟨hquad, hcube, hne1⟩ := omegaCubeRoot_props
  have hfacQ :
      (Polynomial.X ^ 6 - 1 : ℚ[X]) =
        (Polynomial.X - 1) * (Polynomial.X ^ 2 + Polynomial.X + 1) *
        (Polynomial.X + 1) * (Polynomial.X ^ 2 - Polynomial.X + 1) := by
    ring
  have hex1 := example_7_3_1 Nat.prime_three hcube hne1
  have hfin_ω : Module.finrank ℚ ℚ⟮ω⟯ = 2 := by
    have h := hex1.2.2.2.2.2.2.1
    simpa using h
  let α : Fin 6 → ℂ := ![1, ω, ω ^ 2, -1, -ω, -(ω ^ 2)]
  have hsum : ω + ω ^ 2 = -1 := by linear_combination hquad
  have hprod : ω * ω ^ 2 = 1 := by linear_combination (ω - 1) * hquad
  have hexp : GarlingSplitsExplicit ℚ ℂ (Polynomial.X ^ 6 - 1) 6 1 α := by
    unfold GarlingSplitsExplicit
    have hmap : (Polynomial.X ^ 6 - 1 : ℚ[X]).map (algebraMap ℚ ℂ) = Polynomial.X ^ 6 - 1 := by
      simp
    rw [hmap]
    simp only [map_one, one_mul, α, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, mul_one, map_neg, sub_neg_eq_add]
    have hq1 : (Polynomial.X - Polynomial.C ω) * (Polynomial.X - Polynomial.C (ω ^ 2)) =
        (Polynomial.X ^ 2 + Polynomial.X + 1 : ℂ[X]) := by
      calc (Polynomial.X - Polynomial.C ω) * (Polynomial.X - Polynomial.C (ω ^ 2))
          = Polynomial.X ^ 2 - Polynomial.C (ω + ω ^ 2) * Polynomial.X +
              Polynomial.C (ω * ω ^ 2) := by
            simp only [map_add, map_mul]
            ring
        _ = Polynomial.X ^ 2 + Polynomial.X + 1 := by
            rw [hsum, hprod, map_neg, map_one]
            ring
    have hq2 : (Polynomial.X + Polynomial.C ω) * (Polynomial.X + Polynomial.C (ω ^ 2)) =
        (Polynomial.X ^ 2 - Polynomial.X + 1 : ℂ[X]) := by
      calc (Polynomial.X + Polynomial.C ω) * (Polynomial.X + Polynomial.C (ω ^ 2))
          = Polynomial.X ^ 2 + Polynomial.C (ω + ω ^ 2) * Polynomial.X +
              Polynomial.C (ω * ω ^ 2) := by
            simp only [map_add, map_mul]
            ring
        _ = Polynomial.X ^ 2 - Polynomial.X + 1 := by
            rw [hsum, hprod, map_neg, map_one]
            ring
    calc (Polynomial.X ^ 6 - 1 : ℂ[X])
        = (Polynomial.X - 1) * (Polynomial.X ^ 2 + Polynomial.X + 1) *
            (Polynomial.X + 1) * (Polynomial.X ^ 2 - Polynomial.X + 1) := by ring
      _ = (Polynomial.X - 1) *
            ((Polynomial.X - Polynomial.C ω) * (Polynomial.X - Polynomial.C (ω ^ 2))) *
            (Polynomial.X + 1) *
            ((Polynomial.X + Polynomial.C ω) * (Polynomial.X + Polynomial.C (ω ^ 2))) := by
            rw [hq1, hq2]
      _ = _ := by ring
  have hadj : ℚ⟮ω⟯ = IntermediateField.adjoin ℚ (Set.range α) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact IntermediateField.subset_adjoin ℚ (Set.range α) ⟨1, by simp [α]⟩
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      have hω_mem : ω ∈ ℚ⟮ω⟯ := IntermediateField.mem_adjoin_simple_self ℚ ω
      fin_cases i
      · exact ℚ⟮ω⟯.one_mem
      · exact hω_mem
      · exact pow_mem hω_mem 2
      · exact neg_mem ℚ⟮ω⟯.one_mem
      · exact neg_mem hω_mem
      · exact neg_mem (pow_mem hω_mem 2)
  have hsf : IsGarlingSplittingFieldExtension ℚ ℚ⟮ω⟯ (Polynomial.X ^ 6 - 1) :=
    isGarlingSplittingFieldExtension_of_eq_adjoin_range
      (Polynomial.monic_X_pow_sub_C (1 : ℚ) (by norm_num)).ne_zero hexp hadj
  have hfin_inst : Module.Finite ℚ ℚ⟮ω⟯ :=
    (isFiniteExtension_iff_moduleFinite ℚ ℚ⟮ω⟯).mp (corollary_to_theorem_7_1 hsf).1
  exact ⟨hfacQ, hsf, hfin_ω, by rw [extDegree_eq_finrank ℚ ℚ⟮ω⟯, hfin_ω]; rfl⟩

/-- **§7.3 Example 3** (printed pp. 68–69 / PDF pp. 76–77):
For `f = x^6 + 1 ∈ ℚ[x]` and `ω = omegaCubeRoot = -1/2 + (√3/2)i`:
`f` splits in `ℂ` with roots `±i, ±iω, ±iω^2`, `ω ∉ ℚ(i)`, `ℚ(i) ≠ ℚ(ω)`, and `ℚ(i, ω) : ℚ` is a
splitting field extension for `x^6 + 1` of degree `[ℚ(i, ω) : ℚ] = 4`. -/
theorem example_7_3_3 :
    let ω : ℂ := omegaCubeRoot
    let E : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({Complex.I, ω} : Set ℂ)
    ω ∉ ℚ⟮Complex.I⟯ ∧
    ℚ⟮Complex.I⟯ ≠ ℚ⟮ω⟯ ∧
    IsGarlingSplittingFieldExtension ℚ E (Polynomial.X ^ 6 + 1) ∧
    Module.finrank ℚ E = 4 ∧
    extDegree ℚ E = 4 := by
  intro ω E
  obtain ⟨hquad, hcube, _⟩ := omegaCubeRoot_props
  have hsum : ω + ω ^ 2 = -1 := by linear_combination hquad
  have hprod : ω * ω ^ 2 = 1 := by linear_combination (ω - 1) * hquad
  -- 1. `[ℚ(i) : ℚ] = 2` and `ω ∉ ℚ(i)`.
  have hI_not_Q : ∀ q : ℚ, algebraMap ℚ ℂ q ≠ Complex.I := by
    intro q hq
    have him := congrArg Complex.im hq
    simp at him
  obtain ⟨hmin_I, hfin_I⟩ := minpoly_and_finrank_eq_two_of_aeval_deg_two_of_not_mem
    (p := (Polynomial.X ^ 2 + 1 : ℚ[X]))
    (Polynomial.monic_X_pow_add_C 1 (by norm_num))
    (by compute_degree!)
    (by simp [Complex.I_sq])
    hI_not_Q
  have hI_int : IsIntegral ℚ Complex.I :=
    ⟨Polynomial.X ^ 2 + 1, Polynomial.monic_X_pow_add_C 1 (by norm_num), by simp [Complex.I_sq]⟩
  have hω_not_QI : ω ∉ ℚ⟮Complex.I⟯ := by
    intro hmem
    obtain ⟨_a, b, hab⟩ := exists_eq_add_mul_of_mem_adjoin_of_natDegree_eq_two hI_int
      (by rw [hmin_I]; compute_degree!) hmem
    have him' : Real.sqrt 3 / 2 = (b : ℝ) := by
      have h1 := congrArg Complex.im hab
      unfold ω omegaCubeRoot at h1
      simp [Complex.add_im, Complex.mul_im] at h1
      exact h1
    have hsq : ((2 * b : ℚ) : ℝ) ^ 2 = 3 := by
      push_cast
      have h2 : (2 : ℝ) * (b : ℝ) = Real.sqrt 3 := by linarith
      rw [h2, Real.sq_sqrt (by norm_num)]
    have hsqQ : (2 * b : ℚ) ^ 2 = 3 := by exact_mod_cast hsq
    have hirr3 : Irreducible (Polynomial.X ^ 2 - 3 : ℚ[X]) := by
      have h3 : (Polynomial.X ^ 2 - 3 : ℚ[X]) = Polynomial.X ^ 2 - Polynomial.C ((3 : ℕ) : ℚ) := by
        norm_num
        rw [map_ofNat]
      rw [h3]
      exact (exercise_5_7 Nat.prime_three (by omega)).1
    have hroot3 : (Polynomial.X ^ 2 - 3 : ℚ[X]).IsRoot (2 * b) := by
      simp [Polynomial.IsRoot.def, hsqQ]
    obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.mpr hroot3
    rcases hirr3.isUnit_or_isUnit hg with hu | hu
    · exact absurd (Polynomial.natDegree_eq_zero_of_isUnit hu)
        (by rw [Polynomial.natDegree_X_sub_C]; decide)
    · have hg0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      have hd := congrArg Polynomial.natDegree hg
      have hg_ne : g ≠ 0 := hu.ne_zero
      rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hg_ne,
        Polynomial.natDegree_X_sub_C, hg0] at hd
      have hd2 : (Polynomial.X ^ 2 - 3 : ℚ[X]).natDegree = 2 := by compute_degree!
      omega
  have hQI_ne_Qω : ℚ⟮Complex.I⟯ ≠ ℚ⟮ω⟯ := fun heq =>
    hω_not_QI (heq ▸ IntermediateField.mem_adjoin_simple_self ℚ ω)
  -- 2. Splitting field of `X^6 + 1`.
  let α : Fin 6 → ℂ :=
    ![Complex.I, Complex.I * ω, Complex.I * ω ^ 2,
      -Complex.I, -(Complex.I * ω), -(Complex.I * ω ^ 2)]
  have hexp : GarlingSplitsExplicit ℚ ℂ (Polynomial.X ^ 6 + 1) 6 1 α := by
    unfold GarlingSplitsExplicit
    have hmap : (Polynomial.X ^ 6 + 1 : ℚ[X]).map (algebraMap ℚ ℂ) = Polynomial.X ^ 6 + 1 := by
      simp
    rw [hmap]
    simp only [map_one, one_mul, α, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, mul_one, map_neg, sub_neg_eq_add]
    have hp1 : (Polynomial.X - Polynomial.C Complex.I) *
        (Polynomial.X + Polynomial.C Complex.I) = (Polynomial.X ^ 2 + 1 : ℂ[X]) := by
      calc (Polynomial.X - Polynomial.C Complex.I) * (Polynomial.X + Polynomial.C Complex.I)
          = Polynomial.X ^ 2 - Polynomial.C (Complex.I ^ 2) := by
            simp only [map_pow]
            ring
        _ = Polynomial.X ^ 2 + 1 := by rw [Complex.I_sq, map_neg, map_one]; ring
    have hp2 : (Polynomial.X - Polynomial.C (Complex.I * ω)) *
        (Polynomial.X - Polynomial.C (Complex.I * ω ^ 2)) =
        (Polynomial.X ^ 2 + Polynomial.C Complex.I * Polynomial.X - 1 : ℂ[X]) := by
      calc (Polynomial.X - Polynomial.C (Complex.I * ω)) *
            (Polynomial.X - Polynomial.C (Complex.I * ω ^ 2))
          = Polynomial.X ^ 2 - Polynomial.C (Complex.I * (ω + ω ^ 2)) * Polynomial.X +
              Polynomial.C (Complex.I ^ 2 * (ω * ω ^ 2)) := by
            simp only [map_add, map_mul, map_pow]
            ring
        _ = Polynomial.X ^ 2 + Polynomial.C Complex.I * Polynomial.X - 1 := by
            rw [hsum, hprod, Complex.I_sq]
            simp only [mul_neg, mul_one, neg_mul, map_neg, map_one]
            ring
    have hp3 : (Polynomial.X + Polynomial.C (Complex.I * ω)) *
        (Polynomial.X + Polynomial.C (Complex.I * ω ^ 2)) =
        (Polynomial.X ^ 2 - Polynomial.C Complex.I * Polynomial.X - 1 : ℂ[X]) := by
      calc (Polynomial.X + Polynomial.C (Complex.I * ω)) *
            (Polynomial.X + Polynomial.C (Complex.I * ω ^ 2))
          = Polynomial.X ^ 2 + Polynomial.C (Complex.I * (ω + ω ^ 2)) * Polynomial.X +
              Polynomial.C (Complex.I ^ 2 * (ω * ω ^ 2)) := by
            simp only [map_add, map_mul, map_pow]
            ring
        _ = Polynomial.X ^ 2 - Polynomial.C Complex.I * Polynomial.X - 1 := by
            rw [hsum, hprod, Complex.I_sq]
            simp only [mul_neg, mul_one, neg_mul, map_neg, map_one]
            ring
    calc (Polynomial.X ^ 6 + 1 : ℂ[X])
        = (Polynomial.X ^ 2 + 1) *
            ((Polynomial.X ^ 2 - 1) ^ 2 - Polynomial.C (Complex.I ^ 2) * Polynomial.X ^ 2) := by
            rw [Complex.I_sq, map_neg, map_one]
            ring
      _ = (Polynomial.X ^ 2 + 1) *
            ((Polynomial.X ^ 2 + Polynomial.C Complex.I * Polynomial.X - 1) *
             (Polynomial.X ^ 2 - Polynomial.C Complex.I * Polynomial.X - 1)) := by
            simp only [map_pow]
            ring
      _ = ((Polynomial.X - Polynomial.C Complex.I) * (Polynomial.X + Polynomial.C Complex.I)) *
            (((Polynomial.X - Polynomial.C (Complex.I * ω)) *
              (Polynomial.X - Polynomial.C (Complex.I * ω ^ 2))) *
             ((Polynomial.X + Polynomial.C (Complex.I * ω)) *
              (Polynomial.X + Polynomial.C (Complex.I * ω ^ 2)))) := by
            rw [hp1, hp2, hp3]
      _ = _ := by ring
  have hadj : E = IntermediateField.adjoin ℚ (Set.range α) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact IntermediateField.subset_adjoin ℚ (Set.range α) ⟨0, by simp [α]⟩
      · have hI_mem : Complex.I ∈ IntermediateField.adjoin ℚ (Set.range α) :=
          IntermediateField.subset_adjoin ℚ (Set.range α) ⟨0, by simp [α]⟩
        have hIω_mem : Complex.I * ω ∈ IntermediateField.adjoin ℚ (Set.range α) :=
          IntermediateField.subset_adjoin ℚ (Set.range α) ⟨1, by simp [α]⟩
        have hdiv : (Complex.I * ω) / Complex.I = ω :=
          mul_div_cancel_left₀ ω Complex.I_ne_zero
        exact hdiv ▸ div_mem hIω_mem hI_mem
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      have hIE : Complex.I ∈ E := IntermediateField.subset_adjoin ℚ ({Complex.I, ω} : Set ℂ) (by simp)
      have hωE : ω ∈ E := IntermediateField.subset_adjoin ℚ ({Complex.I, ω} : Set ℂ) (by simp)
      fin_cases i
      · exact hIE
      · exact mul_mem hIE hωE
      · exact mul_mem hIE (pow_mem hωE 2)
      · exact neg_mem hIE
      · exact neg_mem (mul_mem hIE hωE)
      · exact neg_mem (mul_mem hIE (pow_mem hωE 2))
  have hsf : IsGarlingSplittingFieldExtension ℚ E (Polynomial.X ^ 6 + 1) :=
    isGarlingSplittingFieldExtension_of_eq_adjoin_range
      (Polynomial.monic_X_pow_add_C (1 : ℚ) (by norm_num)).ne_zero hexp hadj
  -- 3. `[E : ℚ] = 4` via `ℚ ⊆ ℚ(i) ⊆ ℚ(i)(ω) = E`.
  let KI : IntermediateField ℚ ℂ := ℚ⟮Complex.I⟯
  let EI : IntermediateField KI ℂ := IntermediateField.adjoin KI ({ω} : Set ℂ)
  have hEI_eq : EI.restrictScalars ℚ = E := by
    apply le_antisymm
    · intro z hz
      have hKI_le : KI ≤ E := by
        rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact IntermediateField.subset_adjoin ℚ ({Complex.I, ω} : Set ℂ) (by simp)
      let E_over_KI : IntermediateField KI ℂ :=
        { E.toSubfield with algebraMap_mem' := fun x => hKI_le x.2 }
      have hω_mem : ω ∈ E_over_KI :=
        IntermediateField.subset_adjoin ℚ ({Complex.I, ω} : Set ℂ) (by simp)
      exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hω_mem) hz
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact EI.algebraMap_mem ⟨Complex.I, IntermediateField.mem_adjoin_simple_self ℚ Complex.I⟩
      · exact IntermediateField.mem_adjoin_simple_self KI ω
  have hfin_EI : Module.finrank KI EI = 2 :=
    (minpoly_and_finrank_eq_two_of_aeval_deg_two_of_not_mem
      (p := (Polynomial.X ^ 2 + Polynomial.X + 1 : KI[X]))
      (by monicity!)
      (by compute_degree!)
      (by simpa [ω] using hquad)
      (fun x hx => by
        change (x : ℂ) = ω at hx
        exact hω_not_QI (hx ▸ x.2))).2
  have hfin_E : Module.finrank ℚ E = 4 := by
    have hmul : Module.finrank ℚ KI * Module.finrank KI EI =
        Module.finrank ℚ (EI.restrictScalars ℚ) :=
      Module.finrank_mul_finrank ℚ KI EI
    rw [hfin_I, hfin_EI, hEI_eq] at hmul
    exact hmul.symm
  have hE_fin : Module.Finite ℚ E :=
    (isFiniteExtension_iff_moduleFinite ℚ E).mp (corollary_to_theorem_7_1 hsf).1
  exact ⟨hω_not_QI, hQI_ne_Qω, hsf, hfin_E, by rw [extDegree_eq_finrank ℚ E, hfin_E]; rfl⟩

/-! ### §7.3 Example 4: `f = x^2 + ax + b ∈ K[x]` (printed pp. 69–70 / PDF pp. 77–78) -/

/-- **§7.3 Example 4 (`char K ≠ 2` case)** (printed p. 69 / PDF p. 77):
If `(2 : K) ≠ 0`, `f = x^2 + ax + b` completes the square as `(x + a/2)^2 - μ` where
`μ = (a^2 - 4b)/4`:
1. `f` splits over `K` if and only if `μ` has a square root in `K`;
2. If `μ` has no square root in `K`, then `x^2 - μ` and `f` are irreducible over `K`, and for any
   extension `L : K` containing `v ∈ L` with `v^2 = μ`, `K(v) : K` is a splitting field extension
   for `f` of degree `2`;
3. In particular, `ℂ : ℝ` (`ℝ(i) = ⊤`) is a splitting field extension for `x^2 + 1` over `ℝ`. -/
theorem example_7_3_4_char_ne_two {K : Type*} [Field K] (hchar : (2 : K) ≠ 0) (a b : K) :
    let f : K[X] := Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b
    let μ : K := (a ^ 2 - 4 * b) / 4
    f = (Polynomial.X + Polynomial.C (a / 2)) ^ 2 - Polynomial.C μ ∧
    (GarlingSplitsOver K K f ↔ ∃ v : K, v ^ 2 = μ) ∧
    ((¬ ∃ v : K, v ^ 2 = μ) →
      Irreducible (Polynomial.X ^ 2 - Polynomial.C μ : K[X]) ∧
      Irreducible f ∧
      ∀ {L : Type*} [Field L] [Algebra K L] (v : L),
        v ^ 2 = algebraMap K L μ →
        IsGarlingSplittingFieldExtension K K⟮v⟯ f ∧ Module.finrank K K⟮v⟯ = 2) := by
  intro f μ
  have h4 : (4 : K) ≠ 0 := by
    have h4eq : (4 : K) = (2 : K) * (2 : K) := by norm_num
    rw [h4eq]
    exact mul_ne_zero hchar hchar
  have hlin : 2 * (a / 2) = a := mul_div_cancel₀ a hchar
  have hconst : (a / 2) ^ 2 - μ = b := by
    dsimp [μ]
    field_simp [hchar, h4]
    ring
  have hcomp : f = (Polynomial.X + Polynomial.C (a / 2)) ^ 2 - Polynomial.C μ := by
    dsimp [f]
    calc Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b
        = Polynomial.X ^ 2 + Polynomial.C (2 * (a / 2)) * Polynomial.X +
            Polynomial.C ((a / 2) ^ 2 - μ) := by rw [hlin, hconst]
      _ = (Polynomial.X + Polynomial.C (a / 2)) ^ 2 - Polynomial.C μ := by
            simp only [map_sub, map_mul, map_pow, map_ofNat]
            ring
  have hf_mon : f.Monic := by
    dsimp [f]
    monicity!
  have hf_deg : f.natDegree = 2 := by
    dsimp [f]
    compute_degree!
  have hiff : GarlingSplitsOver K K f ↔ ∃ v : K, v ^ 2 = μ := by
    constructor
    · rintro ⟨m, c, α, hexp⟩
      obtain ⟨_, _, hm_eq, hroots⟩ := garlingSplitsExplicit_props hf_mon.ne_zero hexp
      have hm2 : m = 2 := by simpa [garlingDegree, hf_deg] using hm_eq
      have hmem : α ⟨0, by omega⟩ ∈ f.rootSet K := hroots ▸ ⟨⟨0, by omega⟩, rfl⟩
      rw [Polynomial.mem_rootSet] at hmem
      have hev : f.eval (α ⟨0, by omega⟩) = 0 := by simpa using hmem.2
      rw [hcomp] at hev
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_C] at hev
      exact ⟨α ⟨0, by omega⟩ + a / 2, sub_eq_zero.mp hev⟩
    · rintro ⟨v, hv⟩
      let α : Fin 2 → K := ![-a / 2 + v, -a / 2 - v]
      refine ⟨2, 1, α, ?_⟩
      unfold GarlingSplitsExplicit
      have hmap : f.map (algebraMap K K) = f := by simp
      rw [hmap, hcomp, ← hv]
      have hneg : Polynomial.C (-a / 2) = -Polynomial.C (a / 2) := by
        rw [neg_div, map_neg]
      simp only [map_one, one_mul, Fin.prod_univ_two, α, Matrix.cons_val_zero, Matrix.cons_val_one,
        map_add, map_sub, map_pow, hneg]
      ring
  refine ⟨hcomp, hiff, fun hno => ?_⟩
  have hno_g : ∀ x : K, (Polynomial.X ^ 2 - Polynomial.C μ).eval x ≠ 0 := by
    intro x hx
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hx
    exact hno ⟨x, sub_eq_zero.mp hx⟩
  have hno_f : ∀ x : K, f.eval x ≠ 0 := by
    intro x hx
    rw [hcomp] at hx
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C] at hx
    exact hno ⟨x + a / 2, sub_eq_zero.mp hx⟩
  have hirr_g : Irreducible (Polynomial.X ^ 2 - Polynomial.C μ : K[X]) :=
    irreducible_of_monic_deg_two_or_three_of_no_roots
      (Polynomial.monic_X_pow_sub_C μ (by norm_num))
      (Or.inl Polynomial.natDegree_X_pow_sub_C)
      hno_g
  have hirr_f : Irreducible f :=
    irreducible_of_monic_deg_two_or_three_of_no_roots hf_mon (Or.inl hf_deg) hno_f
  refine ⟨hirr_g, hirr_f, ?_⟩
  intro L _ _ v hv
  let a2L : L := algebraMap K L (a / 2)
  let α : Fin 2 → L := ![-a2L + v, -a2L - v]
  have hexp : GarlingSplitsExplicit K L f 2 1 α := by
    unfold GarlingSplitsExplicit
    rw [hcomp]
    simp only [map_one, one_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add,
      Polynomial.map_X, Polynomial.map_C, ← hv, Fin.prod_univ_two, α, a2L,
      Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_sub, map_neg, map_pow]
    ring
  have hadj : K⟮v⟯ = IntermediateField.adjoin K (Set.range α) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      have hr0 : -a2L + v ∈ IntermediateField.adjoin K (Set.range α) :=
        IntermediateField.subset_adjoin K (Set.range α) ⟨0, by simp [α]⟩
      have ha2 : a2L ∈ IntermediateField.adjoin K (Set.range α) :=
        (IntermediateField.adjoin K (Set.range α)).algebraMap_mem (a / 2)
      have hsum_v : a2L + (-a2L + v) = v := by ring
      exact hsum_v ▸ add_mem ha2 hr0
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      have hv_mem : v ∈ K⟮v⟯ := IntermediateField.mem_adjoin_simple_self K v
      have ha2_mem : a2L ∈ K⟮v⟯ := K⟮v⟯.algebraMap_mem (a / 2)
      fin_cases i
      · exact add_mem (neg_mem ha2_mem) hv_mem
      · exact sub_mem (neg_mem ha2_mem) hv_mem
  have hsf : IsGarlingSplittingFieldExtension K K⟮v⟯ f :=
    isGarlingSplittingFieldExtension_of_eq_adjoin_range hf_mon.ne_zero hexp hadj
  have hv_not_K : ∀ x : K, algebraMap K L x ≠ v := by
    intro x hx
    apply hno
    refine ⟨x, (algebraMap K L).injective ?_⟩
    rw [map_pow, hx, hv]
  have hfin : Module.finrank K K⟮v⟯ = 2 :=
    (minpoly_and_finrank_eq_two_of_aeval_deg_two_of_not_mem
      (p := (Polynomial.X ^ 2 - Polynomial.C μ : K[X]))
      (Polynomial.monic_X_pow_sub_C μ (by norm_num))
      Polynomial.natDegree_X_pow_sub_C
      (by rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hv, sub_self])
      hv_not_K).2
  exact ⟨hsf, hfin⟩

/-- Special case noted at the bottom of p. 69: `ℂ = ℝ(i)` is a splitting field for `x^2 + 1`
over `ℝ`. -/
theorem example_7_3_4_complex_over_real :
    ℝ⟮Complex.I⟯ = ⊤ ∧ IsGarlingSplittingFieldExtension ℝ ℂ (Polynomial.X ^ 2 + 1) := by
  have hadj : ℝ⟮Complex.I⟯ = ⊤ := by
    ext z
    simp only [IntermediateField.mem_top, iff_true]
    have hz : z = algebraMap ℝ ℂ z.re + algebraMap ℝ ℂ z.im * Complex.I :=
      (Complex.re_add_im z).symm
    rw [hz]
    exact add_mem (ℝ⟮Complex.I⟯.algebraMap_mem z.re)
      (mul_mem (ℝ⟮Complex.I⟯.algebraMap_mem z.im) (IntermediateField.mem_adjoin_simple_self ℝ Complex.I))
  let α : Fin 2 → ℂ := ![Complex.I, -Complex.I]
  have hexp : GarlingSplitsExplicit ℝ ℂ (Polynomial.X ^ 2 + 1) 2 1 α := by
    unfold GarlingSplitsExplicit
    have hmap : (Polynomial.X ^ 2 + 1 : ℝ[X]).map (algebraMap ℝ ℂ) = Polynomial.X ^ 2 + 1 := by
      simp
    rw [hmap]
    simp only [map_one, one_mul, Fin.prod_univ_two, α, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_neg, sub_neg_eq_add]
    calc (Polynomial.X ^ 2 + 1 : ℂ[X])
        = Polynomial.X ^ 2 - Polynomial.C (Complex.I ^ 2) := by
            rw [Complex.I_sq, map_neg, map_one]; ring
      _ = (Polynomial.X - Polynomial.C Complex.I) * (Polynomial.X + Polynomial.C Complex.I) := by
            simp only [map_pow]; ring
  have htop_range : IntermediateField.adjoin ℝ (Set.range α) = ⊤ := by
    refine top_unique (hadj ▸ IntermediateField.adjoin_le_iff.mpr ?_)
    rw [Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin ℝ (Set.range α) ⟨0, by simp [α]⟩
  exact ⟨hadj, isGarlingSplittingFieldExtension_of_adjoin_range_eq_top
    (Polynomial.monic_X_pow_add_C (1 : ℝ) (by norm_num)).ne_zero hexp htop_range⟩

/-- Irreducible quadratic `x^2 + x + 1 ∈ ℤ₂[x]` of §7.3 `Example 4` (printed p. 70 / PDF p. 78)
and `Exercise 7.6`. -/
noncomputable def zmod2IrredQuad : (ZMod 2)[X] :=
  Polynomial.X ^ 2 + Polynomial.X + 1

theorem zmod2IrredQuad_irreducible : Irreducible zmod2IrredQuad := by
  refine irreducible_of_monic_deg_two_or_three_of_no_roots (by unfold zmod2IrredQuad; monicity!)
    (Or.inl (by unfold zmod2IrredQuad; compute_degree!)) ?_
  intro a
  unfold zmod2IrredQuad
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  fin_cases a <;> decide

instance : Fact (Irreducible zmod2IrredQuad) := ⟨zmod2IrredQuad_irreducible⟩

/-- The `4`-element field `𝔽₄ = ℤ₂[x] / (x^2 + x + 1)` of §7.3 `Example 4` (printed p. 70). -/
noncomputable abbrev ZMod2QuadField : Type := AdjoinRoot zmod2IrredQuad

/-- **§7.3 Example 4 (`K = ℤ₂` case)** (printed p. 70 / PDF p. 78):
1. The first three monic quadratics `x^2`, `x^2 + x`, `x^2 + 1` in `ℤ₂[x]` split over `ℤ₂`;
2. `zmod2IrredQuad = x^2 + x + 1` is irreducible over `ℤ₂`, and `ZMod2QuadField` (`𝔽₄`) has `4`
   elements (`0, 1, α, β = α + 1`), degree `2` over `ℤ₂`, `α^2 = β`, `β^2 = α`, `α^3 = β^3 = 1`;
3. `ZMod2QuadField : ℤ₂` is a splitting field extension for both `x^2 + x + 1` and `x^3 - 1`, and
   is **not** obtained by adjoining a square root of any element of `ℤ₂` (every element of
   `ZMod2QuadField` whose square lies in `ℤ₂` already lies in `ℤ₂`). -/
theorem example_7_3_4_zmod2 :
    GarlingSplitsOver (ZMod 2) (ZMod 2) (Polynomial.X ^ 2) ∧
    GarlingSplitsOver (ZMod 2) (ZMod 2) (Polynomial.X ^ 2 + Polynomial.X) ∧
    GarlingSplitsOver (ZMod 2) (ZMod 2) (Polynomial.X ^ 2 + 1) ∧
    Irreducible zmod2IrredQuad ∧
    Nat.card ZMod2QuadField = 4 ∧
    Module.finrank (ZMod 2) ZMod2QuadField = 2 ∧
    IsGarlingSplittingFieldExtension (ZMod 2) ZMod2QuadField zmod2IrredQuad ∧
    IsGarlingSplittingFieldExtension (ZMod 2) ZMod2QuadField (Polynomial.X ^ 3 - 1) ∧
    (let α : ZMod2QuadField := AdjoinRoot.root zmod2IrredQuad
     let β : ZMod2QuadField := α + 1
     α ^ 2 = β ∧ β ^ 2 = α ∧ α ^ 3 = 1 ∧ β ^ 3 = 1) ∧
    (∀ x : ZMod2QuadField,
      x ^ 2 ∈ Set.range (algebraMap (ZMod 2) ZMod2QuadField) →
      x ∈ Set.range (algebraMap (ZMod 2) ZMod2QuadField)) := by
  have hs1 : GarlingSplitsOver (ZMod 2) (ZMod 2) (Polynomial.X ^ 2) := by
    refine ⟨2, 1, ![0, 0], ?_⟩
    unfold GarlingSplitsExplicit
    simp
    ring
  have hs2 : GarlingSplitsOver (ZMod 2) (ZMod 2) (Polynomial.X ^ 2 + Polynomial.X) := by
    refine ⟨2, 1, ![0, 1], ?_⟩
    unfold GarlingSplitsExplicit
    have hmap : (Polynomial.X ^ 2 + Polynomial.X : (ZMod 2)[X]).map (algebraMap (ZMod 2) (ZMod 2)) =
        Polynomial.X ^ 2 + Polynomial.X := by simp
    rw [hmap]
    simp only [map_one, one_mul, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_zero, sub_zero]
    calc (Polynomial.X ^ 2 + Polynomial.X : (ZMod 2)[X])
        = Polynomial.X * (Polynomial.X - 1) + 2 * Polynomial.X := by ring
      _ = Polynomial.X * (Polynomial.X - 1) := by rw [zmod2_poly_two_eq_zero]; ring
  have hs3 : GarlingSplitsOver (ZMod 2) (ZMod 2) (Polynomial.X ^ 2 + 1) := by
    refine ⟨2, 1, ![1, 1], ?_⟩
    unfold GarlingSplitsExplicit
    have hmap : (Polynomial.X ^ 2 + 1 : (ZMod 2)[X]).map (algebraMap (ZMod 2) (ZMod 2)) =
        Polynomial.X ^ 2 + 1 := by simp
    rw [hmap]
    simp only [map_one, one_mul, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc (Polynomial.X ^ 2 + 1 : (ZMod 2)[X])
        = (Polynomial.X - 1) * (Polynomial.X - 1) + 2 * Polynomial.X := by ring
      _ = (Polynomial.X - 1) * (Polynomial.X - 1) := by rw [zmod2_poly_two_eq_zero]; ring
  let pb := AdjoinRoot.powerBasis zmod2IrredQuad_irreducible.ne_zero
  have hdeg : zmod2IrredQuad.natDegree = 2 := by unfold zmod2IrredQuad; compute_degree!
  have hfin : Module.finrank (ZMod 2) ZMod2QuadField = 2 := by
    rw [Module.finrank_eq_card_basis pb.basis, Fintype.card_fin, AdjoinRoot.powerBasis_dim, hdeg]
  let eVec : ZMod2QuadField ≃ (Fin pb.dim → ZMod 2) := pb.basis.equivFun.toEquiv
  have hcard : Nat.card ZMod2QuadField = 4 := by
    rw [Nat.card_congr eVec, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
      ZMod.card, AdjoinRoot.powerBasis_dim, hdeg]
    norm_num
  let α : ZMod2QuadField := AdjoinRoot.root zmod2IrredQuad
  let β : ZMod2QuadField := α + 1
  have hchar2 : (2 : ZMod2QuadField) = 0 := by
    have h2 : (2 : ZMod 2) = 0 := by decide
    have hm := congrArg (algebraMap (ZMod 2) ZMod2QuadField) h2
    rw [map_ofNat, map_zero] at hm
    exact hm
  have hneg_eq : ∀ x : ZMod2QuadField, -x = x := fun x => by
    have h2x : x + x = 0 := by
      calc x + x = 2 * x := (two_mul x).symm
        _ = 0 := by rw [hchar2, zero_mul]
    linear_combination -h2x
  have hα_root : Polynomial.aeval α zmod2IrredQuad = 0 :=
    (AdjoinRoot.aeval_eq zmod2IrredQuad).trans AdjoinRoot.mk_self
  have hα_rel : α ^ 2 + α + 1 = 0 := by
    simpa only [zmod2IrredQuad, map_add, map_pow, map_one, Polynomial.aeval_X] using hα_root
  have hα2 : α ^ 2 = β := by
    calc α ^ 2 = -(α + 1) := by linear_combination hα_rel
      _ = α + 1 := hneg_eq (α + 1)
  have hβ2 : β ^ 2 = α := by
    dsimp [β]
    calc (α + 1) ^ 2 = α ^ 2 + 2 * α + 1 := by ring
      _ = α + 1 + 0 * α + 1 := by rw [hα2, hchar2]
      _ = α + 2 * 1 := by ring
      _ = α := by rw [hchar2]; ring
  have hα3 : α ^ 3 = 1 := by
    calc α ^ 3 = α ^ 2 * α := by ring
      _ = (α + 1) * α := by rw [hα2]
      _ = α ^ 2 + α := by ring
      _ = (α + 1) + α := by rw [hα2]
      _ = 2 * α + 1 := by ring
      _ = 1 := by rw [hchar2]; ring
  have hβ3 : β ^ 3 = 1 := by
    calc β ^ 3 = β ^ 2 * β := by ring
      _ = α * (α + 1) := by rw [hβ2]
      _ = (α + 1) + α := by rw [show α * (α + 1) = α ^ 2 + α by ring, hα2]
      _ = 2 * α + 1 := by ring
      _ = 1 := by rw [hchar2]; ring
  have hα_ne_β : α ≠ β := by
    intro h
    have h1 : (1 : ZMod2QuadField) = 0 := by
      dsimp [β] at h
      linear_combination -h
    exact one_ne_zero h1
  have hexp_q : GarlingSplitsExplicit (ZMod 2) ZMod2QuadField zmod2IrredQuad 2 1 ![α, β] := by
    unfold GarlingSplitsExplicit
    have hmap : zmod2IrredQuad.map (algebraMap (ZMod 2) ZMod2QuadField) =
        Polynomial.X ^ 2 + Polynomial.X + 1 := by
      unfold zmod2IrredQuad; simp
    rw [hmap]
    simp only [map_one, one_mul]
    refine monic_eq_prod_X_sub_C_of_roots (by monicity!) (by compute_degree!) ?_ ?_
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · exact absurd hij hα_ne_β
      · exact absurd hij.symm hα_ne_β
    · intro i
      fin_cases i
      · simp [hα_rel]
      · change Polynomial.eval β (Polynomial.X ^ 2 + Polynomial.X + 1) = 0
        simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
        rw [hβ2]
        dsimp [β]
        calc α + (α + 1) + 1 = 2 * α + 2 * 1 := by ring
          _ = 0 := by rw [hchar2]; ring
  have hadj_α_top : IntermediateField.adjoin (ZMod 2) ({α} : Set ZMod2QuadField) = ⊤ := by
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [← AdjoinRoot.aeval_eq]
    exact aeval_mem_intermediateField_adjoin_singleton α p
  have hsf_q : IsGarlingSplittingFieldExtension (ZMod 2) ZMod2QuadField zmod2IrredQuad := by
    refine isGarlingSplittingFieldExtension_of_adjoin_range_eq_top zmod2IrredQuad_irreducible.ne_zero
      hexp_q (top_unique (hadj_α_top ▸ IntermediateField.adjoin_le_iff.mpr ?_))
    rw [Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin (ZMod 2) (Set.range ![α, β]) ⟨0, rfl⟩
  -- Splitting field for `X^3 - 1` as well (`1, α, β` distinct).
  have hα_ne1 : α ≠ 1 := fun h1 => by
    rw [h1] at hα_rel
    have h3 : (1 : ZMod2QuadField) + 1 + 1 = 0 := by simpa using hα_rel
    have h10 : (1 : ZMod2QuadField) = 0 := by
      calc (1 : ZMod2QuadField) = (1 + 1 + 1) - 2 * 1 := by ring
        _ = 0 := by rw [h3, hchar2]; ring
    exact one_ne_zero h10
  have hβ_ne1 : β ≠ 1 := fun h1 => by
    have hα0 : α = 0 := by dsimp [β] at h1; linear_combination h1
    rw [hα0] at hα_rel
    simp at hα_rel
  have hexp_c : GarlingSplitsExplicit (ZMod 2) ZMod2QuadField (Polynomial.X ^ 3 - 1) 3 1 ![1, α, β] := by
    unfold GarlingSplitsExplicit
    have hmap : (Polynomial.X ^ 3 - 1 : (ZMod 2)[X]).map (algebraMap (ZMod 2) ZMod2QuadField) =
        Polynomial.X ^ 3 - Polynomial.C 1 := by simp
    rw [hmap]
    simp only [map_one, one_mul]
    refine monic_eq_prod_X_sub_C_of_roots
      (Polynomial.monic_X_pow_sub_C 1 (by norm_num))
      Polynomial.natDegree_X_pow_sub_C
      ?_ ?_
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · exact absurd hij.symm hα_ne1
      · exact absurd hij.symm hβ_ne1
      · exact absurd hij hα_ne1
      · exact absurd hij hα_ne_β
      · exact absurd hij hβ_ne1
      · exact absurd hij.symm hα_ne_β
    · intro i
      fin_cases i <;> simp [hα3, hβ3]
  have hsf_c : IsGarlingSplittingFieldExtension (ZMod 2) ZMod2QuadField (Polynomial.X ^ 3 - 1) := by
    refine isGarlingSplittingFieldExtension_of_adjoin_range_eq_top
      (Polynomial.monic_X_pow_sub_C (1 : ZMod 2) (by norm_num)).ne_zero hexp_c
      (top_unique (hadj_α_top ▸ IntermediateField.adjoin_le_iff.mpr ?_))
    rw [Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin (ZMod 2) (Set.range ![1, α, β]) ⟨1, rfl⟩
  -- Not obtained by adjoining a square root of an element of `ℤ₂`.
  have hno_sqrt : ∀ x : ZMod2QuadField,
      x ^ 2 ∈ Set.range (algebraMap (ZMod 2) ZMod2QuadField) →
      x ∈ Set.range (algebraMap (ZMod 2) ZMod2QuadField) := by
    intro x ⟨c, hc⟩
    have hsum := pb.basis.sum_repr x
    let e : Fin 2 ≃ Fin pb.dim := finCongr (by rw [AdjoinRoot.powerBasis_dim, hdeg])
    rw [← Equiv.sum_comp e, Fin.sum_univ_two] at hsum
    let c0 : ZMod 2 := pb.basis.repr x (e 0)
    have hb0 : pb.basis (e 0) = 1 := by
      rw [pb.basis_eq_pow, AdjoinRoot.powerBasis_gen]
      simp [e]
    have hb1 : pb.basis (e 1) = α := by
      rw [pb.basis_eq_pow, AdjoinRoot.powerBasis_gen]
      simp [e, α]
    let c1 : ZMod 2 := pb.basis.repr x (e 1)
    have hx_eq : x = algebraMap (ZMod 2) ZMod2QuadField c0 +
        algebraMap (ZMod 2) ZMod2QuadField c1 * α := by
      simpa [c0, c1, hb0, hb1, Algebra.smul_def] using hsum.symm
    rcases zmod2_eq_zero_or_one c1 with hc1_0 | hc1_1
    · rw [hx_eq, hc1_0, map_zero, zero_mul, add_zero]
      exact ⟨c0, rfl⟩
    · exfalso
      have hsq : x ^ 2 = algebraMap (ZMod 2) ZMod2QuadField (c0 ^ 2) + 1 + α := by
        rw [hx_eq, hc1_1, map_one, one_mul, map_pow]
        calc (algebraMap (ZMod 2) ZMod2QuadField c0 + α) ^ 2
            = (algebraMap (ZMod 2) ZMod2QuadField c0) ^ 2 + 2 * (algebraMap (ZMod 2) ZMod2QuadField c0) * α + α ^ 2 := by ring
          _ = (algebraMap (ZMod 2) ZMod2QuadField c0) ^ 2 + 0 * (algebraMap (ZMod 2) ZMod2QuadField c0) * α + (α + 1) := by
                rw [hchar2, hα2]
          _ = (algebraMap (ZMod 2) ZMod2QuadField c0) ^ 2 + 1 + α := by ring
      let d : ZMod 2 := c - c0 ^ 2 - 1
      have hα_in : α = algebraMap (ZMod 2) ZMod2QuadField d := by
        dsimp [d]
        rw [map_sub, map_sub, map_one]
        have h1 : algebraMap (ZMod 2) ZMod2QuadField c =
            algebraMap (ZMod 2) ZMod2QuadField (c0 ^ 2) + 1 + α := hc.trans hsq
        calc α = -(algebraMap (ZMod 2) ZMod2QuadField (c0 ^ 2) + 1 -
              algebraMap (ZMod 2) ZMod2QuadField c) := by linear_combination -h1
          _ = algebraMap (ZMod 2) ZMod2QuadField (c0 ^ 2) + 1 -
              algebraMap (ZMod 2) ZMod2QuadField c := hneg_eq _
          _ = algebraMap (ZMod 2) ZMod2QuadField c -
              algebraMap (ZMod 2) ZMod2QuadField (c0 ^ 2) - 1 := by
              have hsub : ∀ u v : ZMod2QuadField, u - v = u + v := fun u v => by
                rw [sub_eq_add_neg, hneg_eq]
              rw [hsub, hsub, hsub]
              ring
      rcases zmod2_eq_zero_or_one d with hd0 | hd1
      · rw [hd0, map_zero] at hα_in
        rw [hα_in] at hα_rel
        simp at hα_rel
      · rw [hd1, map_one] at hα_in
        exact hα_ne1 hα_in
  exact ⟨hs1, hs2, hs3, zmod2IrredQuad_irreducible, hcard, hfin, hsf_q, hsf_c,
    ⟨hα2, hβ2, hα3, hβ3⟩, hno_sqrt⟩

/-! ### Exercises 7.5 & 7.9 (§7.3, printed p. 70 / PDF p. 78) -/

/-- **Exercise 7.5** (§7.3, printed p. 70 / PDF p. 78):
*"Suppose that `M:L` and `L:K` are extensions, and that `α ∈ M` is algebraic over `K`. Does
`[L(α):L]` always divide `[K(α):K]`?"*

Answered in the negative: taking `K = ℚ`, `M = ℂ`, `α = 2^{1/3}`, and `L = ℚ(ω · 2^{1/3})` (where
`ω = primRootOfUnityComplex 3`), `α` is algebraic over `ℚ` with `[ℚ(α) : ℚ] = 3`, while
`L(α) = ℚ(ω, 2^{1/3})` has `[L(α) : ℚ] = 6` and `[L : ℚ] = 3`, so `[L(α) : L] = 2`, which does
not divide `3`. -/
theorem exercise_7_5 :
    (¬ ∀ (K L M : Type) [Field K] [Field L] [Field M]
        [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] (α : M),
        IsGarlingAlgebraic K α →
        Module.finrank L (IntermediateField.adjoin L ({α} : Set M)) ∣
          Module.finrank K (IntermediateField.adjoin K ({α} : Set M))) ∧
    (¬ ∀ (K L M : Type) [Field K] [Field L] [Field M]
        [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] (α : M),
        IsGarlingAlgebraic K α →
        ∃ d : ℕ, extDegree L (IntermediateField.adjoin L ({α} : Set M)) * (d : ℕ∞) =
          extDegree K (IntermediateField.adjoin K ({α} : Set M))) := by
  obtain ⟨hω_pow, hω_ne1⟩ := primRootOfUnityComplex_spec Nat.prime_three
  let ω : ℂ := primRootOfUnityComplex 3
  let α : ℂ := twoPowInvNat 3
  let β : ℂ := ω * α
  let L : IntermediateField ℚ ℂ := ℚ⟮β⟯
  let E : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({ω, α} : Set ℂ)
  have hex1 := example_7_3_1 Nat.prime_three hω_pow hω_ne1
  have hfin_Kα : Module.finrank ℚ ℚ⟮α⟯ = 3 := hex1.2.2.1
  have hfin_E : Module.finrank ℚ E = 6 := by
    have h := hex1.2.2.2.2.2.2.2.2.2.1
    simpa using h
  have hα_pow : α ^ 3 = 2 := by
    obtain ⟨hr0_pow, _, _, _⟩ := real_rpow_inv_nat_minpoly_of_prime Nat.prime_two (by decide : 1 ≤ 3)
    norm_num at hr0_pow
    change (((2 : ℝ) ^ ((1 : ℝ) / (3 : ℝ)) : ℝ) : ℂ) ^ 3 = 2
    rw [← Complex.ofReal_pow]
    norm_num [hr0_pow]
  have hα_ne0 : α ≠ 0 := fun h0 => by
    rw [h0] at hα_pow
    norm_num at hα_pow
  have hα_alg : IsGarlingAlgebraic ℚ α :=
    ⟨Polynomial.X ^ 3 - Polynomial.C 2,
      (Polynomial.monic_X_pow_sub_C (2 : ℚ) (by norm_num)).ne_zero, by simp [hα_pow]⟩
  have hβ_pow : β ^ 3 = 2 := by
    dsimp [β]
    rw [mul_pow, hω_pow, hα_pow, one_mul]
  have hβ_eval : Polynomial.aeval β (Polynomial.X ^ 3 - 2 : ℚ[X]) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, map_ofNat, hβ_pow, sub_self]
  have hβ_mon : (Polynomial.X ^ 3 - 2 : ℚ[X]).Monic := by
    rw [← map_ofNat Polynomial.C 2]
    exact Polynomial.monic_X_pow_sub_C (2 : ℚ) (by norm_num)
  have hβ_int : IsIntegral ℚ β :=
    ⟨Polynomial.X ^ 3 - 2, hβ_mon, hβ_eval⟩
  have hβ_min : minpoly ℚ β = Polynomial.X ^ 3 - 2 :=
    (minpoly.eq_of_irreducible_of_monic hex1.1 hβ_eval hβ_mon).symm
  have hfin_L : Module.finrank ℚ L = 3 := by
    rw [IntermediateField.adjoin.finrank hβ_int, hβ_min, ← map_ofNat Polynomial.C 2,
      Polynomial.natDegree_X_pow_sub_C]
  let Lα : IntermediateField L ℂ := IntermediateField.adjoin L ({α} : Set ℂ)
  have hLα_eq : Lα.restrictScalars ℚ = E := by
    apply le_antisymm
    · intro z hz
      have hL_le : L ≤ E := by
        rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        have hωE : ω ∈ E := IntermediateField.subset_adjoin ℚ ({ω, α} : Set ℂ) (by simp)
        have hαE : α ∈ E := IntermediateField.subset_adjoin ℚ ({ω, α} : Set ℂ) (by simp)
        exact mul_mem hωE hαE
      let E_over_L : IntermediateField L ℂ :=
        { E.toSubfield with algebraMap_mem' := fun x => hL_le x.2 }
      have hα_mem : α ∈ E_over_L :=
        IntermediateField.subset_adjoin ℚ ({ω, α} : Set ℂ) (by simp)
      exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hα_mem) hz
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · have hβ_in : β ∈ Lα :=
          Lα.algebraMap_mem ⟨β, IntermediateField.mem_adjoin_simple_self ℚ β⟩
        have hα_in : α ∈ Lα := IntermediateField.mem_adjoin_simple_self L α
        have hdiv : β / α = ω := mul_div_cancel_right₀ ω hα_ne0
        exact hdiv ▸ div_mem hβ_in hα_in
      · exact IntermediateField.mem_adjoin_simple_self L α
  have hfin_Lα : Module.finrank L Lα = 2 := by
    have hmul : Module.finrank ℚ L * Module.finrank L Lα =
        Module.finrank ℚ (Lα.restrictScalars ℚ) :=
      Module.finrank_mul_finrank ℚ L Lα
    rw [hfin_L, hLα_eq, hfin_E] at hmul
    omega
  refine ⟨fun hall => ?_, fun hall => ?_⟩
  · have hdvd := hall ℚ L ℂ α hα_alg
    change Module.finrank L Lα ∣ Module.finrank ℚ ℚ⟮α⟯ at hdvd
    rw [hfin_Lα, hfin_Kα] at hdvd
    exact absurd hdvd (by decide)
  · obtain ⟨d, hd⟩ := hall ℚ L ℂ α hα_alg
    have hα_int_L : IsIntegral L α :=
      ⟨Polynomial.X ^ 3 - Polynomial.C 2, Polynomial.monic_X_pow_sub_C (2 : L) (by norm_num), by
        rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
          map_ofNat, hα_pow, sub_self]⟩
    have _ : Module.Finite L Lα := IntermediateField.adjoin.finiteDimensional hα_int_L
    have _ : Module.Finite ℚ ℚ⟮α⟯ :=
      IntermediateField.adjoin.finiteDimensional ((isGarlingAlgebraic_iff_isIntegral ℚ α).mp hα_alg)
    change extDegree L Lα * (d : ℕ∞) = extDegree ℚ ℚ⟮α⟯ at hd
    rw [extDegree_eq_finrank L Lα, extDegree_eq_finrank ℚ ℚ⟮α⟯, hfin_Lα, hfin_Kα] at hd
    have hd_nat : 2 * d = 3 := by exact_mod_cast hd
    omega

/-- **Exercise 7.9** (§7.3, printed p. 70 / PDF p. 78):
*"Suppose that `L:K` is a splitting field extension for a polynomial of degree `n`. Show that
`[L:K]` divides `n!`"* -/
theorem exercise_7_9 {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hf : f ≠ 0) {n : ℕ} (hdeg : garlingDegree f hf = n)
    (hsf : IsGarlingSplittingFieldExtension K L f) :
    Module.finrank K L ∣ n.factorial ∧
    ∃ k : ℕ, extDegree K L * (k : ℕ∞) = (n.factorial : ℕ∞) := by
  have hfin : Module.Finite K L :=
    (isFiniteExtension_iff_moduleFinite K L).mp (corollary_to_theorem_7_1 hsf).1
  have hdvd : Module.finrank K L ∣ n.factorial :=
    splittingField_finrank_dvd_factorial n (by simpa [garlingDegree] using hdeg) hsf
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨⟨k, hk⟩, k, ?_⟩
  rw [extDegree_eq_finrank K L]
  exact_mod_cast hk.symm

/-- Companion to `Exercise 7.9` stated unconditionally via `Polynomial.natDegree` (valid even at
`f = 0`). -/
theorem exercise_7_9_natDegree {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hsf : IsGarlingSplittingFieldExtension K L f) :
    Module.finrank K L ∣ f.natDegree.factorial ∧
    ∃ k : ℕ, extDegree K L * (k : ℕ∞) = (f.natDegree.factorial : ℕ∞) := by
  have hfin : Module.Finite K L :=
    (isFiniteExtension_iff_moduleFinite K L).mp (corollary_to_theorem_7_1 hsf).1
  have hdvd : Module.finrank K L ∣ f.natDegree.factorial :=
    splittingField_finrank_dvd_factorial f.natDegree rfl hsf
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨⟨k, hk⟩, k, ?_⟩
  rw [extDegree_eq_finrank K L]
  exact_mod_cast hk.symm

/-! ### Exercise 7.6 (§7.3, printed p. 70 / PDF p. 78) -/

/-- The `8` monic cubic polynomials in `ℤ₂[x]` (`Exercise 7.6`, printed p. 70 / PDF p. 78):
- `0`: `x^3`
- `1`: `x^3 + x^2`
- `2`: `x^3 + x`
- `3`: `x^3 + x^2 + x + 1`
- `4`: `x^3 + x^2 + x`
- `5`: `x^3 + 1`
- `6`: `x^3 + x + 1`
- `7`: `x^3 + x^2 + 1` -/
noncomputable def ex76Cubic : Fin 8 → (ZMod 2)[X]
  | ⟨0, _⟩ => Polynomial.X ^ 3
  | ⟨1, _⟩ => Polynomial.X ^ 3 + Polynomial.X ^ 2
  | ⟨2, _⟩ => Polynomial.X ^ 3 + Polynomial.X
  | ⟨3, _⟩ => Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1
  | ⟨4, _⟩ => Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X
  | ⟨5, _⟩ => Polynomial.X ^ 3 + 1
  | ⟨6, _⟩ => Polynomial.X ^ 3 + Polynomial.X + 1
  | ⟨_ + 7, _⟩ => Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1

private def ex76CoeffTriple (p : (ZMod 2)[X]) : ZMod 2 × ZMod 2 × ZMod 2 :=
  (p.coeff 2, p.coeff 1, p.coeff 0)

theorem ex76Cubic_monic_and_natDegree (i : Fin 8) :
    (ex76Cubic i).Monic ∧ (ex76Cubic i).natDegree = 3 := by
  fin_cases i <;>
    refine ⟨by dsimp [ex76Cubic]; monicity!, by dsimp [ex76Cubic]; compute_degree!⟩

private def ex76ExpectedTriple : Fin 8 → ZMod 2 × ZMod 2 × ZMod 2 :=
  ![(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 1),
    (1, 1, 0), (0, 0, 1), (0, 1, 1), (1, 0, 1)]

theorem ex76Cubic_injective : Function.Injective ex76Cubic := by
  have htrip : ∀ i : Fin 8, ex76CoeffTriple (ex76Cubic i) = ex76ExpectedTriple i := by
    rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | m, hm⟩
    · simp [ex76CoeffTriple, ex76Cubic, ex76ExpectedTriple, Polynomial.coeff_X_pow]
    · simp [ex76CoeffTriple, ex76Cubic, ex76ExpectedTriple, Polynomial.coeff_X_pow]
    · simp [ex76CoeffTriple, ex76Cubic, ex76ExpectedTriple, Polynomial.coeff_X_pow,
        Polynomial.coeff_X]
    · simp [ex76CoeffTriple, ex76Cubic, ex76ExpectedTriple, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_one]
    · simp [ex76CoeffTriple, ex76Cubic, ex76ExpectedTriple, Polynomial.coeff_X_pow,
        Polynomial.coeff_X]
    · simp [ex76CoeffTriple, ex76Cubic, ex76ExpectedTriple, Polynomial.coeff_X_pow,
        Polynomial.coeff_one]
    · simp [ex76CoeffTriple, ex76Cubic, ex76ExpectedTriple, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_one]
    · simp [ex76CoeffTriple, ex76Cubic, ex76ExpectedTriple, Polynomial.coeff_X_pow,
        Polynomial.coeff_one]
    · omega
  have hinj_exp : Function.Injective ex76ExpectedTriple := by decide
  intro i j hij
  apply hinj_exp
  rw [← htrip i, ← htrip j, hij]

/-- Every monic cubic polynomial in `ℤ₂[x]` equals `ex76Cubic i` for a unique `i : Fin 8`. -/
theorem ex76Cubic_complete (p : (ZMod 2)[X]) :
    (p.Monic ∧ p.natDegree = 3) ↔ ∃ i : Fin 8, p = ex76Cubic i := by
  refine ⟨fun ⟨hmon, hdeg⟩ => ?_, fun ⟨i, hi⟩ => hi ▸ ex76Cubic_monic_and_natDegree i⟩
  have hp_expand :
      p = Polynomial.X ^ 3 + Polynomial.C (p.coeff 2) * Polynomial.X ^ 2 +
          Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) := by
    ext n
    rcases n with _ | _ | _ | _ | m
    · simp
    · simp [Polynomial.coeff_X_pow]
    · simp [Polynomial.coeff_X_pow]
    · have hc3 : p.coeff 3 = 1 := by rw [← hdeg]; exact hmon.leadingCoeff
      simp [hc3, Polynomial.coeff_X_pow]
    · have hcn : p.coeff (m + 4) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [hcn, Polynomial.coeff_X_pow]
  rcases zmod2_eq_zero_or_one (p.coeff 2) with h2 | h2 <;>
    rcases zmod2_eq_zero_or_one (p.coeff 1) with h1 | h1 <;>
    rcases zmod2_eq_zero_or_one (p.coeff 0) with h0 | h0
  · refine ⟨0, ?_⟩; rw [hp_expand, h2, h1, h0]; dsimp [ex76Cubic]; simp
  · refine ⟨5, ?_⟩; rw [hp_expand, h2, h1, h0]; dsimp [ex76Cubic]; simp
  · refine ⟨2, ?_⟩; rw [hp_expand, h2, h1, h0]; dsimp [ex76Cubic]; simp
  · refine ⟨6, ?_⟩; rw [hp_expand, h2, h1, h0]; dsimp [ex76Cubic]; simp
  · refine ⟨1, ?_⟩; rw [hp_expand, h2, h1, h0]; dsimp [ex76Cubic]; simp
  · refine ⟨7, ?_⟩; rw [hp_expand, h2, h1, h0]; dsimp [ex76Cubic]; simp
  · refine ⟨4, ?_⟩; rw [hp_expand, h2, h1, h0]; dsimp [ex76Cubic]; simp
  · refine ⟨3, ?_⟩; rw [hp_expand, h2, h1, h0]; dsimp [ex76Cubic]; simp

theorem ex76Cubic6_irreducible : Irreducible (ex76Cubic 6) := by
  refine irreducible_of_monic_deg_two_or_three_of_no_roots
    (ex76Cubic_monic_and_natDegree 6).1 (Or.inr (ex76Cubic_monic_and_natDegree 6).2) ?_
  intro a
  dsimp [ex76Cubic]
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  revert a
  decide

theorem ex76Cubic7_irreducible : Irreducible (ex76Cubic 7) := by
  refine irreducible_of_monic_deg_two_or_three_of_no_roots
    (ex76Cubic_monic_and_natDegree 7).1 (Or.inr (ex76Cubic_monic_and_natDegree 7).2) ?_
  intro a
  dsimp [ex76Cubic]
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  revert a
  decide

instance : Fact (Irreducible (ex76Cubic 6)) := ⟨ex76Cubic6_irreducible⟩
instance : Fact (Irreducible (ex76Cubic 7)) := ⟨ex76Cubic7_irreducible⟩

/-- The `8`-element field `ℤ₂[x] / (x^3 + x + 1)` of `Exercise 7.6`. -/
noncomputable abbrev Ex76CubicField6 : Type := AdjoinRoot (ex76Cubic 6)

/-- The `8`-element field `ℤ₂[x] / (x^3 + x^2 + 1)` of `Exercise 7.6`. -/
noncomputable abbrev Ex76CubicField7 : Type := AdjoinRoot (ex76Cubic 7)

/-- Complete irreducible factorizations of all `8` monic cubics in `ℤ₂[x]` (`Exercise 7.6`). -/
theorem ex76Cubic_factorizations :
    Irreducible (Polynomial.X : (ZMod 2)[X]) ∧
    Irreducible (Polynomial.X + 1 : (ZMod 2)[X]) ∧
    Irreducible zmod2IrredQuad ∧
    Irreducible (ex76Cubic 6) ∧
    Irreducible (ex76Cubic 7) ∧
    ex76Cubic 0 = Polynomial.X * Polynomial.X * Polynomial.X ∧
    ex76Cubic 1 = Polynomial.X * Polynomial.X * (Polynomial.X + 1) ∧
    ex76Cubic 2 = Polynomial.X * (Polynomial.X + 1) * (Polynomial.X + 1) ∧
    ex76Cubic 3 = (Polynomial.X + 1) * (Polynomial.X + 1) * (Polynomial.X + 1) ∧
    ex76Cubic 4 = Polynomial.X * zmod2IrredQuad ∧
    ex76Cubic 5 = (Polynomial.X + 1) * zmod2IrredQuad := by
  have hirrX : Irreducible (Polynomial.X : (ZMod 2)[X]) := Polynomial.irreducible_X
  have hirrX1 : Irreducible (Polynomial.X + 1 : (ZMod 2)[X]) := by
    have heq : (Polynomial.X + 1 : (ZMod 2)[X]) = Polynomial.X - Polynomial.C 1 := by
      rw [map_one]
      calc (Polynomial.X + 1 : (ZMod 2)[X]) = (Polynomial.X - 1) + 2 * 1 := by ring
        _ = Polynomial.X - 1 := by rw [zmod2_poly_two_eq_zero]; ring
    rw [heq]
    exact Polynomial.irreducible_X_sub_C (1 : ZMod 2)
  refine ⟨hirrX, hirrX1, zmod2IrredQuad_irreducible, ex76Cubic6_irreducible,
    ex76Cubic7_irreducible, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [ex76Cubic]; ring
  · dsimp [ex76Cubic]; ring
  · dsimp [ex76Cubic]
    calc (Polynomial.X ^ 3 + Polynomial.X : (ZMod 2)[X])
        = Polynomial.X * (Polynomial.X + 1) * (Polynomial.X + 1) - 2 * Polynomial.X ^ 2 := by ring
      _ = Polynomial.X * (Polynomial.X + 1) * (Polynomial.X + 1) := by
            rw [zmod2_poly_two_eq_zero]; ring
  · dsimp [ex76Cubic]
    calc (Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 2)[X])
        = (Polynomial.X + 1) * (Polynomial.X + 1) * (Polynomial.X + 1) -
            2 * (Polynomial.X ^ 2 + Polynomial.X) := by ring
      _ = (Polynomial.X + 1) * (Polynomial.X + 1) * (Polynomial.X + 1) := by
            rw [zmod2_poly_two_eq_zero]; ring
  · dsimp [ex76Cubic, zmod2IrredQuad]; ring
  · dsimp [ex76Cubic, zmod2IrredQuad]
    calc (Polynomial.X ^ 3 + 1 : (ZMod 2)[X])
        = (Polynomial.X + 1) * (Polynomial.X ^ 2 + Polynomial.X + 1) -
            2 * (Polynomial.X ^ 2 + Polynomial.X) := by ring
      _ = (Polynomial.X + 1) * (Polynomial.X ^ 2 + Polynomial.X + 1) := by
            rw [zmod2_poly_two_eq_zero]; ring

/-- Splitting field extension `Ex76Field i` over `ℤ₂` constructed for each monic cubic
`ex76Cubic i` (`i : Fin 8`) in `Exercise 7.6`. -/
noncomputable def Ex76Field : Fin 8 → Type
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => ZMod 2
  | ⟨4, _⟩ | ⟨5, _⟩ => ZMod2QuadField
  | ⟨6, _⟩ => Ex76CubicField6
  | ⟨_ + 7, _⟩ => Ex76CubicField7

noncomputable instance instFieldEx76Field : (i : Fin 8) → Field (Ex76Field i)
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => inferInstanceAs (Field (ZMod 2))
  | ⟨4, _⟩ | ⟨5, _⟩ => inferInstanceAs (Field ZMod2QuadField)
  | ⟨6, _⟩ => inferInstanceAs (Field Ex76CubicField6)
  | ⟨_ + 7, _⟩ => inferInstanceAs (Field Ex76CubicField7)

noncomputable instance instAlgebraEx76Field : (i : Fin 8) → Algebra (ZMod 2) (Ex76Field i)
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => inferInstanceAs (Algebra (ZMod 2) (ZMod 2))
  | ⟨4, _⟩ | ⟨5, _⟩ => inferInstanceAs (Algebra (ZMod 2) ZMod2QuadField)
  | ⟨6, _⟩ => inferInstanceAs (Algebra (ZMod 2) Ex76CubicField6)
  | ⟨_ + 7, _⟩ => inferInstanceAs (Algebra (ZMod 2) Ex76CubicField7)

/-- Degree `[Ex76Field i : ℤ₂]` (`1` for `0..3`, `2` for `4..5`, `3` for `6..7`). -/
def ex76Deg : Fin 8 → ℕ := ![1, 1, 1, 1, 2, 2, 3, 3]

/-- Explicit `ℤ₂`-algebra isomorphism `ℤ₂[x]/(x^3 + x + 1) ≃ₐ[ℤ₂] ℤ₂[x]/(x^3 + x^2 + 1)`
sending `γ ↦ δ + 1` and `δ ↦ γ + 1` (`Exercise 7.6`, printed p. 70). -/
noncomputable def ex76CubicFieldEquiv : Ex76CubicField6 ≃ₐ[ZMod 2] Ex76CubicField7 := by
  let γ : Ex76CubicField6 := AdjoinRoot.root (ex76Cubic 6)
  let δ : Ex76CubicField7 := AdjoinRoot.root (ex76Cubic 7)
  have hchar6 : (2 : Ex76CubicField6) = 0 := by
    have hm := congrArg (algebraMap (ZMod 2) Ex76CubicField6) (show (2 : ZMod 2) = 0 by decide)
    simpa only [map_ofNat, map_zero] using hm
  have hchar7 : (2 : Ex76CubicField7) = 0 := by
    have hm := congrArg (algebraMap (ZMod 2) Ex76CubicField7) (show (2 : ZMod 2) = 0 by decide)
    simpa only [map_ofNat, map_zero] using hm
  have hγ_rel : γ ^ 3 + γ + 1 = 0 := by
    have hr : Polynomial.aeval γ (ex76Cubic 6) = 0 :=
      (AdjoinRoot.aeval_eq (ex76Cubic 6)).trans AdjoinRoot.mk_self
    dsimp [ex76Cubic] at hr
    simpa only [map_add, map_pow, map_one, Polynomial.aeval_X] using hr
  have hδ_rel : δ ^ 3 + δ ^ 2 + 1 = 0 := by
    have hr : Polynomial.aeval δ (ex76Cubic 7) = 0 :=
      (AdjoinRoot.aeval_eq (ex76Cubic 7)).trans AdjoinRoot.mk_self
    dsimp [ex76Cubic] at hr
    simpa only [map_add, map_pow, map_one, Polynomial.aeval_X] using hr
  have hc6_def : ex76Cubic 6 = Polynomial.X ^ 3 + Polynomial.X + 1 := rfl
  have hc7_def : ex76Cubic 7 = Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1 := rfl
  have h6_at_δ1 : Polynomial.eval₂ (Algebra.ofId (ZMod 2) Ex76CubicField7)
      (δ + 1) (ex76Cubic 6) = 0 := by
    rw [hc6_def]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_one]
    calc (δ + 1) ^ 3 + (δ + 1) + 1
        = (δ ^ 3 + δ ^ 2 + 1) + 2 * (δ ^ 2 + 2 * δ + 1) := by ring
      _ = 0 := by rw [hδ_rel, hchar7]; ring
  have h7_at_γ1 : Polynomial.eval₂ (Algebra.ofId (ZMod 2) Ex76CubicField6)
      (γ + 1) (ex76Cubic 7) = 0 := by
    rw [hc7_def]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_one]
    calc (γ + 1) ^ 3 + (γ + 1) ^ 2 + 1
        = (γ ^ 3 + γ + 1) + 2 * (2 * γ ^ 2 + 2 * γ + 1) := by ring
      _ = 0 := by rw [hγ_rel, hchar6]; ring
  refine AlgEquiv.ofAlgHom
    (AdjoinRoot.liftAlgHom (ex76Cubic 6) (Algebra.ofId (ZMod 2) Ex76CubicField7) (δ + 1) h6_at_δ1)
    (AdjoinRoot.liftAlgHom (ex76Cubic 7) (Algebra.ofId (ZMod 2) Ex76CubicField6) (γ + 1) h7_at_γ1)
    (AdjoinRoot.algHom_ext ?_)
    (AdjoinRoot.algHom_ext ?_)
  · rw [AlgHom.comp_apply, AlgHom.id_apply, AdjoinRoot.liftAlgHom_root, map_add, map_one,
      AdjoinRoot.liftAlgHom_root]
    dsimp [δ]
    calc AdjoinRoot.root (ex76Cubic 7) + 1 + 1
        = AdjoinRoot.root (ex76Cubic 7) + 2 * 1 := by ring
      _ = AdjoinRoot.root (ex76Cubic 7) := by rw [hchar7]; ring
  · rw [AlgHom.comp_apply, AlgHom.id_apply, AdjoinRoot.liftAlgHom_root, map_add, map_one,
      AdjoinRoot.liftAlgHom_root]
    dsimp [γ]
    calc AdjoinRoot.root (ex76Cubic 6) + 1 + 1
        = AdjoinRoot.root (ex76Cubic 6) + 2 * 1 := by ring
      _ = AdjoinRoot.root (ex76Cubic 6) := by rw [hchar6]; ring

private theorem ex76Cubic6_splitting :
    IsGarlingSplittingFieldExtension (ZMod 2) Ex76CubicField6 (ex76Cubic 6) ∧
    Module.finrank (ZMod 2) Ex76CubicField6 = 3 ∧
    Nat.card Ex76CubicField6 = 8 := by
  let pb := AdjoinRoot.powerBasis ex76Cubic6_irreducible.ne_zero
  have hdeg : (ex76Cubic 6).natDegree = 3 := (ex76Cubic_monic_and_natDegree 6).2
  have hfin : Module.finrank (ZMod 2) Ex76CubicField6 = 3 := by
    rw [Module.finrank_eq_card_basis pb.basis, Fintype.card_fin, AdjoinRoot.powerBasis_dim, hdeg]
  let eVec : Ex76CubicField6 ≃ (Fin pb.dim → ZMod 2) := pb.basis.equivFun.toEquiv
  have hcard : Nat.card Ex76CubicField6 = 8 := by
    rw [Nat.card_congr eVec, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
      ZMod.card, AdjoinRoot.powerBasis_dim, hdeg]
    norm_num
  let γ : Ex76CubicField6 := AdjoinRoot.root (ex76Cubic 6)
  have hchar2 : (2 : Ex76CubicField6) = 0 := by
    have hm := congrArg (algebraMap (ZMod 2) Ex76CubicField6) (show (2 : ZMod 2) = 0 by decide)
    simpa only [map_ofNat, map_zero] using hm
  have hc6_def : ex76Cubic 6 = Polynomial.X ^ 3 + Polynomial.X + 1 := rfl
  have hγ_rel : γ ^ 3 + γ + 1 = 0 := by
    have hr : Polynomial.aeval γ (ex76Cubic 6) = 0 :=
      (AdjoinRoot.aeval_eq (ex76Cubic 6)).trans AdjoinRoot.mk_self
    have hr' : Polynomial.aeval γ (Polynomial.X ^ 3 + Polynomial.X + 1 : (ZMod 2)[X]) = 0 :=
      (congrArg (Polynomial.aeval γ) hc6_def.symm).trans hr
    simpa only [map_add, map_pow, map_one, Polynomial.aeval_X] using hr'
  have hγ3 : γ ^ 3 = γ + 1 := by
    calc γ ^ 3 = -(γ + 1) + (γ ^ 3 + γ + 1) := by ring
      _ = -(γ + 1) := by rw [hγ_rel, add_zero]
      _ = (γ + 1) - 2 * (γ + 1) := by ring
      _ = γ + 1 := by rw [hchar2]; ring
  have hγ_ne0 : γ ≠ 0 := fun h0 => by
    rw [h0] at hγ_rel; simp at hγ_rel
  have hγ_ne1 : γ ≠ 1 := fun h1 => by
    rw [h1] at hγ3
    have h10 : (1 : Ex76CubicField6) = 0 := by linear_combination -hγ3
    exact one_ne_zero h10
  let α : Fin 3 → Ex76CubicField6 := ![γ, γ ^ 2, γ ^ 2 + γ]
  have hexp : GarlingSplitsExplicit (ZMod 2) Ex76CubicField6 (ex76Cubic 6) 3 1 α := by
    unfold GarlingSplitsExplicit
    have hmap : (ex76Cubic 6).map (algebraMap (ZMod 2) Ex76CubicField6) =
        Polynomial.X ^ 3 + Polynomial.X + 1 := by
      refine (congrArg (Polynomial.map (algebraMap (ZMod 2) Ex76CubicField6)) hc6_def).trans ?_
      simp
    rw [hmap]
    simp only [map_one, one_mul]
    refine monic_eq_prod_X_sub_C_of_roots (by monicity!) (by compute_degree!) ?_ ?_
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp [α] at hij ⊢
      · have hmul : γ * (γ - 1) = 0 := by linear_combination -hij
        rcases mul_eq_zero.mp hmul with h0 | h1
        · exact absurd h0 hγ_ne0
        · exact absurd (sub_eq_zero.mp h1) hγ_ne1
      · exact absurd hij hγ_ne0
      · have hmul : γ * (γ - 1) = 0 := by linear_combination hij
        rcases mul_eq_zero.mp hmul with h0 | h1
        · exact absurd h0 hγ_ne0
        · exact absurd (sub_eq_zero.mp h1) hγ_ne1
      · exact absurd hij hγ_ne0
      · exact absurd hij hγ_ne0
      · exact absurd hij hγ_ne0
    · intro i
      fin_cases i
      · simp [α, hγ_rel]
      · change Polynomial.eval (γ ^ 2) (Polynomial.X ^ 3 + Polynomial.X + 1) = 0
        simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
        calc (γ ^ 2) ^ 3 + γ ^ 2 + 1 = (γ ^ 3) ^ 2 + γ ^ 2 + 1 := by ring
          _ = (γ + 1) ^ 2 + γ ^ 2 + 1 := by rw [hγ3]
          _ = 2 * (γ ^ 2 + γ + 1) := by ring
          _ = 0 := by rw [hchar2]; ring
      · change Polynomial.eval (γ ^ 2 + γ) (Polynomial.X ^ 3 + Polynomial.X + 1) = 0
        simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
        have hsq : (γ ^ 2 + γ) ^ 2 = γ := by
          calc (γ ^ 2 + γ) ^ 2 = γ * γ ^ 3 + 2 * γ ^ 3 + γ ^ 2 := by ring
            _ = γ * (γ + 1) + 2 * (γ + 1) + γ ^ 2 := by rw [hγ3]
            _ = γ + 2 * (γ ^ 2 + γ + 1) := by ring
            _ = γ := by rw [hchar2]; ring
        calc (γ ^ 2 + γ) ^ 3 + (γ ^ 2 + γ) + 1
            = (γ ^ 2 + γ) ^ 2 * (γ ^ 2 + γ) + (γ ^ 2 + γ) + 1 := by ring
          _ = γ * (γ ^ 2 + γ) + (γ ^ 2 + γ) + 1 := by rw [hsq]
          _ = γ ^ 3 + 2 * γ ^ 2 + γ + 1 := by ring
          _ = (γ + 1) + 2 * γ ^ 2 + γ + 1 := by rw [hγ3]
          _ = 2 * (γ ^ 2 + γ + 1) := by ring
          _ = 0 := by rw [hchar2]; ring
  have hadj_top : IntermediateField.adjoin (ZMod 2) ({γ} : Set Ex76CubicField6) = ⊤ := by
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [← AdjoinRoot.aeval_eq]
    exact aeval_mem_intermediateField_adjoin_singleton γ p
  have hsf : IsGarlingSplittingFieldExtension (ZMod 2) Ex76CubicField6 (ex76Cubic 6) := by
    refine isGarlingSplittingFieldExtension_of_adjoin_range_eq_top ex76Cubic6_irreducible.ne_zero
      hexp (top_unique (hadj_top ▸ IntermediateField.adjoin_le_iff.mpr ?_))
    rw [Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin (ZMod 2) (Set.range α) ⟨0, rfl⟩
  exact ⟨hsf, hfin, hcard⟩

private theorem ex76Cubic7_splitting :
    IsGarlingSplittingFieldExtension (ZMod 2) Ex76CubicField7 (ex76Cubic 7) ∧
    Module.finrank (ZMod 2) Ex76CubicField7 = 3 ∧
    Nat.card Ex76CubicField7 = 8 := by
  let pb := AdjoinRoot.powerBasis ex76Cubic7_irreducible.ne_zero
  have hdeg : (ex76Cubic 7).natDegree = 3 := (ex76Cubic_monic_and_natDegree 7).2
  have hfin : Module.finrank (ZMod 2) Ex76CubicField7 = 3 := by
    rw [Module.finrank_eq_card_basis pb.basis, Fintype.card_fin, AdjoinRoot.powerBasis_dim, hdeg]
  let eVec : Ex76CubicField7 ≃ (Fin pb.dim → ZMod 2) := pb.basis.equivFun.toEquiv
  have hcard : Nat.card Ex76CubicField7 = 8 := by
    rw [Nat.card_congr eVec, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
      ZMod.card, AdjoinRoot.powerBasis_dim, hdeg]
    norm_num
  let δ : Ex76CubicField7 := AdjoinRoot.root (ex76Cubic 7)
  have hchar2 : (2 : Ex76CubicField7) = 0 := by
    have hm := congrArg (algebraMap (ZMod 2) Ex76CubicField7) (show (2 : ZMod 2) = 0 by decide)
    simpa only [map_ofNat, map_zero] using hm
  have hδ_rel : δ ^ 3 + δ ^ 2 + 1 = 0 := by
    have hr : Polynomial.aeval δ (ex76Cubic 7) = 0 :=
      (AdjoinRoot.aeval_eq (ex76Cubic 7)).trans AdjoinRoot.mk_self
    dsimp [ex76Cubic] at hr
    simpa only [map_add, map_pow, map_one, Polynomial.aeval_X] using hr
  have hδ3 : δ ^ 3 = δ ^ 2 + 1 := by
    calc δ ^ 3 = -(δ ^ 2 + 1) + (δ ^ 3 + δ ^ 2 + 1) := by ring
      _ = -(δ ^ 2 + 1) := by rw [hδ_rel, add_zero]
      _ = (δ ^ 2 + 1) - 2 * (δ ^ 2 + 1) := by ring
      _ = δ ^ 2 + 1 := by rw [hchar2]; ring
  have hδ_ne0 : δ ≠ 0 := fun h0 => by
    rw [h0] at hδ_rel; simp at hδ_rel
  have hδ_ne1 : δ ≠ 1 := fun h1 => by
    rw [h1] at hδ3
    have h10 : (1 : Ex76CubicField7) = 0 := by linear_combination -hδ3
    exact one_ne_zero h10
  have hδ_add1_ne0 : δ + 1 ≠ 0 := fun h0 => hδ_ne1 (by
    calc δ = (δ + 1) + 1 - 2 * 1 := by ring
      _ = 1 := by rw [h0, hchar2]; ring)
  let α : Fin 3 → Ex76CubicField7 := ![δ, δ ^ 2, δ ^ 2 + δ + 1]
  have hc7_def : ex76Cubic 7 = Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1 := rfl
  have hexp : GarlingSplitsExplicit (ZMod 2) Ex76CubicField7 (ex76Cubic 7) 3 1 α := by
    unfold GarlingSplitsExplicit
    have hmap : (ex76Cubic 7).map (algebraMap (ZMod 2) Ex76CubicField7) =
        Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1 := by
      refine (congrArg (Polynomial.map (algebraMap (ZMod 2) Ex76CubicField7)) hc7_def).trans ?_
      simp
    rw [hmap]
    simp only [map_one, one_mul]
    refine monic_eq_prod_X_sub_C_of_roots (by monicity!) (by compute_degree!) ?_ ?_
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp [α] at hij ⊢
      · have hmul : δ * (δ - 1) = 0 := by linear_combination -hij
        rcases mul_eq_zero.mp hmul with h0 | h1
        · exact absurd h0 hδ_ne0
        · exact absurd (sub_eq_zero.mp h1) hδ_ne1
      · have hsq0 : (δ + 1) ^ 2 = 0 := by
          calc (δ + 1) ^ 2 = (δ ^ 2 + 1) + 2 * δ := by ring
            _ = (δ ^ 2 + δ + 1 - δ) + 2 * δ := by ring
            _ = (δ - δ) + 2 * δ := by rw [← hij]
            _ = 0 := by rw [hchar2]; ring
        exact absurd hsq0 (pow_ne_zero 2 hδ_add1_ne0)
      · have hmul : δ * (δ - 1) = 0 := by linear_combination hij
        rcases mul_eq_zero.mp hmul with h0 | h1
        · exact absurd h0 hδ_ne0
        · exact absurd (sub_eq_zero.mp h1) hδ_ne1
      · exact absurd (by linear_combination -hij : δ + 1 = 0) hδ_add1_ne0
      · have hsq0 : (δ + 1) ^ 2 = 0 := by
          calc (δ + 1) ^ 2 = (δ ^ 2 + δ + 1 - δ) + 2 * δ := by ring
            _ = (δ - δ) + 2 * δ := by rw [hij]
            _ = 0 := by rw [hchar2]; ring
        exact absurd hsq0 (pow_ne_zero 2 hδ_add1_ne0)
      · exact absurd (by linear_combination hij : δ + 1 = 0) hδ_add1_ne0
    · intro i
      fin_cases i
      · simp [α, hδ_rel]
      · change Polynomial.eval (δ ^ 2) (Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1) = 0
        simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
        calc (δ ^ 2) ^ 3 + (δ ^ 2) ^ 2 + 1
            = (δ ^ 3) ^ 2 + δ * δ ^ 3 + 1 := by ring
          _ = (δ ^ 2 + 1) ^ 2 + δ * (δ ^ 2 + 1) + 1 := by rw [hδ3]
          _ = δ * δ ^ 3 + δ ^ 3 + 2 * δ ^ 2 + δ + 2 := by ring
          _ = δ * (δ ^ 2 + 1) + (δ ^ 2 + 1) + 2 * δ ^ 2 + δ + 2 := by rw [hδ3]
          _ = δ ^ 3 + 3 * δ ^ 2 + 2 * δ + 3 := by ring
          _ = (δ ^ 2 + 1) + 3 * δ ^ 2 + 2 * δ + 3 := by rw [hδ3]
          _ = 2 * (2 * δ ^ 2 + δ + 2) := by ring
          _ = 0 := by rw [hchar2]; ring
      · change Polynomial.eval (δ ^ 2 + δ + 1) (Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1) = 0
        simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
        have hsq : (δ ^ 2 + δ + 1) ^ 2 = δ := by
          calc (δ ^ 2 + δ + 1) ^ 2
              = δ * δ ^ 3 + δ ^ 2 + 1 + 2 * (δ ^ 3 + δ ^ 2 + δ) := by ring
            _ = δ * (δ ^ 2 + 1) + δ ^ 2 + 1 + 2 * ((δ ^ 2 + 1) + δ ^ 2 + δ) := by rw [hδ3]
            _ = δ ^ 3 + δ ^ 2 + δ + 1 + 2 * (2 * δ ^ 2 + δ + 1) := by ring
            _ = (δ ^ 2 + 1) + δ ^ 2 + δ + 1 + 2 * (2 * δ ^ 2 + δ + 1) := by rw [hδ3]
            _ = δ + 2 * (3 * δ ^ 2 + δ + 2) := by ring
            _ = δ := by rw [hchar2]; ring
        calc (δ ^ 2 + δ + 1) ^ 3 + (δ ^ 2 + δ + 1) ^ 2 + 1
            = (δ ^ 2 + δ + 1) ^ 2 * (δ ^ 2 + δ + 1) + (δ ^ 2 + δ + 1) ^ 2 + 1 := by ring
          _ = δ * (δ ^ 2 + δ + 1) + δ + 1 := by rw [hsq]
          _ = δ ^ 3 + δ ^ 2 + 2 * δ + 1 := by ring
          _ = (δ ^ 2 + 1) + δ ^ 2 + 2 * δ + 1 := by rw [hδ3]
          _ = 2 * (δ ^ 2 + δ + 1) := by ring
          _ = 0 := by rw [hchar2]; ring
  have hadj_top : IntermediateField.adjoin (ZMod 2) ({δ} : Set Ex76CubicField7) = ⊤ := by
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [← AdjoinRoot.aeval_eq]
    exact aeval_mem_intermediateField_adjoin_singleton δ p
  have hsf : IsGarlingSplittingFieldExtension (ZMod 2) Ex76CubicField7 (ex76Cubic 7) := by
    refine isGarlingSplittingFieldExtension_of_adjoin_range_eq_top ex76Cubic7_irreducible.ne_zero
      hexp (top_unique (hadj_top ▸ IntermediateField.adjoin_le_iff.mpr ?_))
    rw [Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin (ZMod 2) (Set.range α) ⟨0, rfl⟩
  exact ⟨hsf, hfin, hcard⟩

/-- **Exercise 7.6** (§7.3, printed p. 70 / PDF p. 78):
*"Write down all monic cubic polynomials in `ℤ₂[x]`, factorize them completely and construct a
splitting field for each of them. Which of these fields are isomorphic?"*

Summary packaged here:
1. `ex76Cubic : Fin 8 → (ZMod 2)[X]` injectively and exhaustively enumerates all `8` monic cubic
   polynomials in `ℤ₂[x]`;
2. `ex76Cubic_factorizations` gives the complete factorization of every `ex76Cubic i` into
   irreducible polynomials over `ℤ₂`;
3. For every `i : Fin 8`, `Ex76Field i` is a splitting field extension for `ex76Cubic i` over `ℤ₂`
   of degree `ex76Deg i` (`1` for `i ∈ {0,1,2,3}`, `2` for `i ∈ {4,5}`, `3` for `i ∈ {6,7}`) and
   cardinality `2 ^ (ex76Deg i)`;
4. Two splitting fields `Ex76Field i` and `Ex76Field j` are isomorphic (equivalently as fields or
   as `ℤ₂`-algebras) if and only if `ex76Deg i = ex76Deg j`, partitioning the `8` splitting fields
   into the three isomorphism classes `{0, 1, 2, 3}` (`𝔽₂`), `{4, 5}` (`𝔽₄`), and `{6, 7}` (`𝔽₈`,
   with `Ex76CubicField6 ≃ₐ[ZMod 2] Ex76CubicField7` given explicitly by `ex76CubicFieldEquiv`). -/
theorem exercise_7_6 :
    Function.Injective ex76Cubic ∧
    (∀ p : (ZMod 2)[X], (p.Monic ∧ p.natDegree = 3) ↔ ∃ i : Fin 8, p = ex76Cubic i) ∧
    (∀ i : Fin 8,
      IsGarlingSplittingFieldExtension (ZMod 2) (Ex76Field i) (ex76Cubic i) ∧
      Module.finrank (ZMod 2) (Ex76Field i) = ex76Deg i ∧
      Nat.card (Ex76Field i) = 2 ^ (ex76Deg i)) ∧
    (∀ i j : Fin 8,
      (Nonempty (Ex76Field i ≃ₐ[ZMod 2] Ex76Field j) ↔ ex76Deg i = ex76Deg j) ∧
      (Nonempty (Ex76Field i ≃+* Ex76Field j) ↔ ex76Deg i = ex76Deg j)) := by
  obtain ⟨_, _, _, _, hcard4, hfin4, hsf_quad, hsf_x3_sub1, _, _⟩ := example_7_3_4_zmod2
  have hcard2 : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hfin2 : Module.finrank (ZMod 2) (ZMod 2) = 1 := Module.finrank_self (ZMod 2)
  have hneg1 : (-1 : (ZMod 2)[X]) = 1 := by
    calc (-1 : (ZMod 2)[X]) = 1 - 2 * 1 := by ring
      _ = 1 := by rw [zmod2_poly_two_eq_zero]; ring
  have hper_i : ∀ i : Fin 8,
      IsGarlingSplittingFieldExtension (ZMod 2) (Ex76Field i) (ex76Cubic i) ∧
      Module.finrank (ZMod 2) (Ex76Field i) = ex76Deg i ∧
      Nat.card (Ex76Field i) = 2 ^ (ex76Deg i) := by
    rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | m, hm⟩
    · change IsGarlingSplittingFieldExtension (ZMod 2) (ZMod 2) (ex76Cubic 0) ∧
        Module.finrank (ZMod 2) (ZMod 2) = ex76Deg 0 ∧ Nat.card (ZMod 2) = 2 ^ (ex76Deg 0)
      refine ⟨(isGarlingSplittingFieldExtension_self_iff (ZMod 2) _).mpr
        ⟨3, 1, ![0, 0, 0], ?_⟩, hfin2, hcard2⟩
      unfold GarlingSplitsExplicit
      dsimp [ex76Cubic]
      simp only [ Polynomial.map_pow, Polynomial.map_X, map_one, one_mul, Fin.prod_univ_succ,
        Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one, map_zero, sub_zero]
      ring
    · change IsGarlingSplittingFieldExtension (ZMod 2) (ZMod 2) (ex76Cubic 1) ∧
        Module.finrank (ZMod 2) (ZMod 2) = ex76Deg 1 ∧ Nat.card (ZMod 2) = 2 ^ (ex76Deg 1)
      refine ⟨(isGarlingSplittingFieldExtension_self_iff (ZMod 2) _).mpr
        ⟨3, 1, ![0, 0, 1], ?_⟩, hfin2, hcard2⟩
      unfold GarlingSplitsExplicit
      have hmap : (ex76Cubic 1).map (algebraMap (ZMod 2) (ZMod 2)) =
          Polynomial.X ^ 3 + Polynomial.X ^ 2 := by dsimp [ex76Cubic]; simp
      rw [hmap]
      simp only [map_one, one_mul, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, mul_one, map_zero, sub_zero]
      rw [show (Polynomial.X - 1 : (ZMod 2)[X]) = Polynomial.X + (-1) by ring, hneg1]
      ring
    · change IsGarlingSplittingFieldExtension (ZMod 2) (ZMod 2) (ex76Cubic 2) ∧
        Module.finrank (ZMod 2) (ZMod 2) = ex76Deg 2 ∧ Nat.card (ZMod 2) = 2 ^ (ex76Deg 2)
      refine ⟨(isGarlingSplittingFieldExtension_self_iff (ZMod 2) _).mpr
        ⟨3, 1, ![0, 1, 1], ?_⟩, hfin2, hcard2⟩
      unfold GarlingSplitsExplicit
      have hmap : (ex76Cubic 2).map (algebraMap (ZMod 2) (ZMod 2)) = ex76Cubic 2 := by
        dsimp [ex76Cubic]; simp
      rw [hmap, ex76Cubic_factorizations.2.2.2.2.2.2.2.1]
      simp only [map_one, one_mul, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, mul_one, map_zero, sub_zero]
      rw [show (Polynomial.X - 1 : (ZMod 2)[X]) = Polynomial.X + (-1) by ring, hneg1]
      ring
    · change IsGarlingSplittingFieldExtension (ZMod 2) (ZMod 2) (ex76Cubic 3) ∧
        Module.finrank (ZMod 2) (ZMod 2) = ex76Deg 3 ∧ Nat.card (ZMod 2) = 2 ^ (ex76Deg 3)
      refine ⟨(isGarlingSplittingFieldExtension_self_iff (ZMod 2) _).mpr
        ⟨3, 1, ![1, 1, 1], ?_⟩, hfin2, hcard2⟩
      unfold GarlingSplitsExplicit
      have hmap : (ex76Cubic 3).map (algebraMap (ZMod 2) (ZMod 2)) = ex76Cubic 3 := by
        dsimp [ex76Cubic]; simp
      rw [hmap, ex76Cubic_factorizations.2.2.2.2.2.2.2.2.1]
      simp only [map_one, one_mul, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, mul_one]
      rw [show (Polynomial.X - 1 : (ZMod 2)[X]) = Polynomial.X + (-1) by ring, hneg1]
      ring
    · change IsGarlingSplittingFieldExtension (ZMod 2) ZMod2QuadField (ex76Cubic 4) ∧
        Module.finrank (ZMod 2) ZMod2QuadField = ex76Deg 4 ∧
        Nat.card ZMod2QuadField = 2 ^ (ex76Deg 4)
      let α : ZMod2QuadField := AdjoinRoot.root zmod2IrredQuad
      have hchar4 : (2 : ZMod2QuadField) = 0 := by
        have hm := congrArg (algebraMap (ZMod 2) ZMod2QuadField) (show (2 : ZMod 2) = 0 by decide)
        simpa only [map_ofNat, map_zero] using hm
      have hα_rel : α ^ 2 + α + 1 = 0 := by
        have hr : Polynomial.aeval α zmod2IrredQuad = 0 :=
          (AdjoinRoot.aeval_eq zmod2IrredQuad).trans AdjoinRoot.mk_self
        simpa only [zmod2IrredQuad, map_add, map_pow, map_one, Polynomial.aeval_X] using hr
      have hexp4 : GarlingSplitsExplicit (ZMod 2) ZMod2QuadField (ex76Cubic 4) 3 1
          ![0, α, α + 1] := by
        unfold GarlingSplitsExplicit
        have hc4_def : ex76Cubic 4 = Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X := rfl
        have hmap : (ex76Cubic 4).map (algebraMap (ZMod 2) ZMod2QuadField) =
            Polynomial.X * (Polynomial.X ^ 2 + Polynomial.X + 1) := by
          rw [hc4_def]; simp; ring
        rw [hmap]
        simp only [map_one, one_mul, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, mul_one, map_zero, sub_zero]
        have hq : (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C (α + 1)) =
            (Polynomial.X ^ 2 + Polynomial.X + 1 : ZMod2QuadField[X]) := by
          have hs : α + (α + 1) = -1 := by
            calc α + (α + 1) = -1 + 2 * (α + 1) := by ring
              _ = -1 := by rw [hchar4]; ring
          have hp : α * (α + 1) = 1 := by
            calc α * (α + 1) = (α ^ 2 + α + 1) + 1 - 2 * 1 := by ring
              _ = 1 := by rw [hα_rel, hchar4]; ring
          calc (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C (α + 1))
              = Polynomial.X ^ 2 - Polynomial.C (α + (α + 1)) * Polynomial.X +
                  Polynomial.C (α * (α + 1)) := by simp only [map_add, map_mul]; ring
            _ = Polynomial.X ^ 2 + Polynomial.X + 1 := by rw [hs, hp, map_neg, map_one]; ring
        rw [← hq]
      have hadj_top : IntermediateField.adjoin (ZMod 2) ({α} : Set ZMod2QuadField) = ⊤ := by
        ext x
        simp only [IntermediateField.mem_top, iff_true]
        obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
        rw [← AdjoinRoot.aeval_eq]
        exact aeval_mem_intermediateField_adjoin_singleton α p
      have hsf4 : IsGarlingSplittingFieldExtension (ZMod 2) ZMod2QuadField (ex76Cubic 4) := by
        refine isGarlingSplittingFieldExtension_of_adjoin_range_eq_top
          (ex76Cubic_monic_and_natDegree 4).1.ne_zero hexp4
          (top_unique (hadj_top ▸ IntermediateField.adjoin_le_iff.mpr ?_))
        rw [Set.singleton_subset_iff]
        exact IntermediateField.subset_adjoin (ZMod 2) (Set.range ![0, α, α + 1]) ⟨1, rfl⟩
      exact ⟨hsf4, hfin4, hcard4⟩
    · change IsGarlingSplittingFieldExtension (ZMod 2) ZMod2QuadField (ex76Cubic 5) ∧
        Module.finrank (ZMod 2) ZMod2QuadField = ex76Deg 5 ∧
        Nat.card ZMod2QuadField = 2 ^ (ex76Deg 5)
      have heq5 : ex76Cubic 5 = (Polynomial.X ^ 3 - 1 : (ZMod 2)[X]) := by
        dsimp [ex76Cubic]
        rw [show (Polynomial.X ^ 3 - 1 : (ZMod 2)[X]) = Polynomial.X ^ 3 + (-1) by ring, hneg1]
      exact ⟨heq5 ▸ hsf_x3_sub1, hfin4, hcard4⟩
    · exact ex76Cubic6_splitting
    · exact ex76Cubic7_splitting
    · omega
  refine ⟨ex76Cubic_injective, ex76Cubic_complete, hper_i, fun i j => ?_⟩
  have hcard_iso : ∀ {i j : Fin 8},
      Nonempty (Ex76Field i ≃+* Ex76Field j) → ex76Deg i = ex76Deg j := by
    rintro i j ⟨e⟩
    have hc : 2 ^ (ex76Deg i) = 2 ^ (ex76Deg j) := by
      rw [← (hper_i i).2.2, ← (hper_i j).2.2]
      exact Nat.card_congr e.toEquiv
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc
  have hdeg1_iso : ∀ i : Fin 8, ex76Deg i = 1 →
      Nonempty (Ex76Field i ≃ₐ[ZMod 2] ZMod 2) := by
    rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | m, hm⟩ h
    · exact ⟨AlgEquiv.refl⟩
    · exact ⟨AlgEquiv.refl⟩
    · exact ⟨AlgEquiv.refl⟩
    · exact ⟨AlgEquiv.refl⟩
    · exfalso; revert hm h; decide
    · exfalso; revert hm h; decide
    · exfalso; revert hm h; decide
    · exfalso; revert hm h; decide
    · omega
  have hdeg2_iso : ∀ i : Fin 8, ex76Deg i = 2 →
      Nonempty (Ex76Field i ≃ₐ[ZMod 2] ZMod2QuadField) := by
    rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | m, hm⟩ h
    · exfalso; revert hm h; decide
    · exfalso; revert hm h; decide
    · exfalso; revert hm h; decide
    · exfalso; revert hm h; decide
    · exact ⟨AlgEquiv.refl⟩
    · exact ⟨AlgEquiv.refl⟩
    · exfalso; revert hm h; decide
    · exfalso; revert hm h; decide
    · omega
  have hdeg3_iso : ∀ i : Fin 8, ex76Deg i = 3 →
      Nonempty (Ex76Field i ≃ₐ[ZMod 2] Ex76CubicField6) := by
    rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | m, hm⟩ h
    · exfalso; revert hm h; decide
    · exfalso; revert hm h; decide
    · exfalso; revert hm h; decide
    · exfalso; revert hm h; decide
    · exfalso; revert hm h; decide
    · exfalso; revert hm h; decide
    · exact ⟨AlgEquiv.refl⟩
    · exact ⟨ex76CubicFieldEquiv.symm⟩
    · omega
  have halg_iso : ∀ {i j : Fin 8},
      ex76Deg i = ex76Deg j → Nonempty (Ex76Field i ≃ₐ[ZMod 2] Ex76Field j) := by
    have hcases : ∀ k : Fin 8, ex76Deg k = 1 ∨ ex76Deg k = 2 ∨ ex76Deg k = 3 := by
      decide
    intro i j hdeg
    rcases hcases i with hd1 | hd2 | hd3
    · obtain ⟨ei⟩ := hdeg1_iso i hd1
      obtain ⟨ej⟩ := hdeg1_iso j (hdeg.symm.trans hd1)
      exact ⟨ei.trans ej.symm⟩
    · obtain ⟨ei⟩ := hdeg2_iso i hd2
      obtain ⟨ej⟩ := hdeg2_iso j (hdeg.symm.trans hd2)
      exact ⟨ei.trans ej.symm⟩
    · obtain ⟨ei⟩ := hdeg3_iso i hd3
      obtain ⟨ej⟩ := hdeg3_iso j (hdeg.symm.trans hd3)
      exact ⟨ei.trans ej.symm⟩
  exact ⟨⟨fun ⟨e⟩ => hcard_iso ⟨e.toRingEquiv⟩, halg_iso⟩,
    ⟨hcard_iso, fun hdeg => let ⟨e⟩ := halg_iso hdeg; ⟨e.toRingEquiv⟩⟩⟩

/-! ### Shared Helpers for Exercises 7.7 & 7.8 -/

private theorem adjoin_pair_restrictScalars_eq {K M : Type*} [Field K] [Field M] [Algebra K M]
    (a b : M) :
    (IntermediateField.adjoin (K⟮a⟯) ({b} : Set M)).restrictScalars K =
      IntermediateField.adjoin K ({a, b} : Set M) := by
  let Ka : IntermediateField K M := K⟮a⟯
  let Eab : IntermediateField Ka M := IntermediateField.adjoin Ka ({b} : Set M)
  let E : IntermediateField K M := IntermediateField.adjoin K ({a, b} : Set M)
  change Eab.restrictScalars K = E
  apply le_antisymm
  · intro z hz
    have hKa_le : Ka ≤ E := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact IntermediateField.subset_adjoin K ({a, b} : Set M) (by simp)
    let E_over_Ka : IntermediateField Ka M :=
      { E.toSubfield with algebraMap_mem' := fun x => hKa_le x.2 }
    have hb_mem : b ∈ E_over_Ka :=
      IntermediateField.subset_adjoin K ({a, b} : Set M) (by simp)
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hb_mem) hz
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hza | hzb
    · rw [hza]
      exact Eab.algebraMap_mem ⟨a, IntermediateField.mem_adjoin_simple_self K a⟩
    · rw [hzb]
      exact IntermediateField.mem_adjoin_simple_self Ka b

private theorem finrank_adjoin_pair_mul_two {K M : Type*} [Field K] [Field M] [Algebra K M]
    {a b : M} {d : ℕ} (hfin_a : Module.finrank K K⟮a⟯ = d) {p : (K⟮a⟯)[X]}
    (hp_mon : p.Monic) (hp_deg : p.natDegree = 2) (hp_eval : Polynomial.aeval b p = 0)
    (hb_not : b ∉ K⟮a⟯) :
    Module.finrank K (IntermediateField.adjoin K ({a, b} : Set M)) = d * 2 := by
  let Ka : IntermediateField K M := K⟮a⟯
  let Eab : IntermediateField Ka M := IntermediateField.adjoin Ka ({b} : Set M)
  have hfin_b : Module.finrank Ka Eab = 2 :=
    (minpoly_and_finrank_eq_two_of_aeval_deg_two_of_not_mem hp_mon hp_deg hp_eval
      (fun x hx => hb_not (by
        have hx' : (x : M) = b := hx
        exact hx' ▸ x.2))).2
  have hmul : Module.finrank K Ka * Module.finrank Ka Eab =
      Module.finrank K (Eab.restrictScalars K) :=
    Module.finrank_mul_finrank K Ka Eab
  rw [hfin_a, hfin_b, adjoin_pair_restrictScalars_eq] at hmul
  exact hmul.symm

private theorem complex_I_not_mem_adjoin_ofReal (x₀ : ℝ) :
    Complex.I ∉ ℚ⟮((x₀ : ℝ) : ℂ)⟯ := by
  intro hmem
  let φ : ℝ →ₐ[ℚ] ℂ := IsScalarTower.toAlgHom ℚ ℝ ℂ
  let R : IntermediateField ℚ ℂ := IntermediateField.map φ ⊤
  have hle : ℚ⟮((x₀ : ℝ) : ℂ)⟯ ≤ R := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    change ((x₀ : ℝ) : ℂ) ∈ IntermediateField.map φ ⊤
    rw [IntermediateField.mem_map]
    exact ⟨x₀, IntermediateField.mem_top, rfl⟩
  have hIR : Complex.I ∈ IntermediateField.map φ ⊤ := hle hmem
  rw [IntermediateField.mem_map] at hIR
  obtain ⟨x, _, hx⟩ := hIR
  have him := congrArg Complex.im hx
  change ((x : ℝ) : ℂ).im = Complex.I.im at him
  rw [Complex.ofReal_im, Complex.I_im] at him
  norm_num at him

private theorem rat_sq_ne_of_prime_dvd {n p : ℕ} (hp : Nat.Prime p)
    (hdvd : p ∣ n) (hndvd : ¬ p ^ 2 ∣ n) (q : ℚ) : q ^ 2 ≠ (n : ℚ) := by
  intro hq
  have hden_ne : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.pos.ne'
  have hnum_eq : ((q.num : ℚ) / (q.den : ℚ)) ^ 2 = (n : ℚ) := by
    rwa [Rat.num_div_den]
  have hmulQ : (q.num : ℚ) ^ 2 = (n : ℚ) * (q.den : ℚ) ^ 2 := by
    field_simp [hden_ne] at hnum_eq
    linarith
  have hmulZ : q.num ^ 2 = (n : ℤ) * (q.den : ℤ) ^ 2 := by exact_mod_cast hmulQ
  have hmulN : q.num.natAbs ^ 2 = n * q.den ^ 2 := by
    have habs := congrArg Int.natAbs hmulZ
    simpa [Int.natAbs_pow, Int.natAbs_mul] using habs
  have hp_num : p ∣ q.num.natAbs :=
    hp.dvd_of_dvd_pow (hmulN ▸ dvd_trans hdvd (dvd_mul_right n (q.den ^ 2)))
  obtain ⟨k, hk⟩ := hp_num
  obtain ⟨m, rfl⟩ := hdvd
  have hpm : p * (p * k ^ 2) = p * (m * q.den ^ 2) := by
    calc p * (p * k ^ 2) = (p * k) ^ 2 := by ring
      _ = p * m * q.den ^ 2 := by rw [← hk, hmulN]
      _ = p * (m * q.den ^ 2) := by ring
  have hcancel : p * k ^ 2 = m * q.den ^ 2 := Nat.eq_of_mul_eq_mul_left hp.pos hpm
  rcases hp.dvd_mul.mp ⟨k ^ 2, hcancel.symm⟩ with ⟨c, rfl⟩ | hpd2
  · exact hndvd ⟨c, by ring⟩
  · have hpd : p ∣ q.den := hp.dvd_of_dvd_pow hpd2
    exact hp.not_dvd_one (q.reduced.gcd_eq_one ▸ Nat.dvd_gcd ⟨k, hk⟩ hpd)

/-! ### Exercise 7.7 (§7.3, printed p. 70 / PDF p. 78) -/

/-- Positive real fourth root `5^{1/4}` viewed in `ℂ` (`Exercise 7.7`, printed p. 70 / PDF p. 78). -/
noncomputable def fivePowQuarter : ℂ :=
  ((5 : ℝ) ^ ((1 : ℝ) / 4) : ℝ)

/-- **Exercise 7.7** (§7.3, printed p. 70 / PDF p. 78):
*"Find a splitting field extension `K : ℚ` for each of the following polynomials over `ℚ`:
`x^4 - 5x^2 + 6`, `x^4 + 5x^2 + 6`, `x^4 - 5`.
In each case determine the degree `[K : ℚ]` and find `α` such that `K = ℚ(α)`."*

Explicit splitting fields, degrees, and primitive elements proved here:
1. For `f₁ = x^4 - 5x^2 + 6 = (x^2 - 2)(x^2 - 3)`:
   `K₁ = ℚ(√2, √3)` is a splitting field over `ℚ`, `[K₁ : ℚ] = 4`, and `K₁ = ℚ(√2 + √3)`.
2. For `f₂ = x^4 + 5x^2 + 6 = (x^2 + 2)(x^2 + 3)`:
   `K₂ = ℚ(i√2, i√3)` is a splitting field over `ℚ`, `[K₂ : ℚ] = 4`, and `K₂ = ℚ(i√2 + i√3)`.
3. For `f₃ = x^4 - 5`:
   `K₃ = ℚ(5^{1/4}, i)` is a splitting field over `ℚ`, `[K₃ : ℚ] = 8`, and
   `K₃ = ℚ(5^{1/4} + i)`. -/
theorem exercise_7_7 :
    let s2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
    let s3 : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)
    let is2 : ℂ := Complex.I * s2
    let is3 : ℂ := Complex.I * s3
    let r5 : ℂ := fivePowQuarter
    let K₁ : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({s2, s3} : Set ℂ)
    let K₂ : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({is2, is3} : Set ℂ)
    let K₃ : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({r5, Complex.I} : Set ℂ)
    (IsGarlingSplittingFieldExtension ℚ K₁ (Polynomial.X ^ 4 - 5 * Polynomial.X ^ 2 + 6) ∧
      Module.finrank ℚ K₁ = 4 ∧ extDegree ℚ K₁ = 4 ∧ K₁ = ℚ⟮s2 + s3⟯) ∧
    (IsGarlingSplittingFieldExtension ℚ K₂ (Polynomial.X ^ 4 + 5 * Polynomial.X ^ 2 + 6) ∧
      Module.finrank ℚ K₂ = 4 ∧ extDegree ℚ K₂ = 4 ∧ K₂ = ℚ⟮is2 + is3⟯) ∧
    (IsGarlingSplittingFieldExtension ℚ K₃ (Polynomial.X ^ 4 - 5) ∧
      Module.finrank ℚ K₃ = 8 ∧ extDegree ℚ K₃ = 8 ∧ K₃ = ℚ⟮r5 + Complex.I⟯) := by
  intro s2 s3 is2 is3 r5 K₁ K₂ K₃
  have hs2_sq : s2 ^ 2 = 2 := by
    dsimp [s2]; rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs3_sq : s3 ^ 2 = 3 := by
    dsimp [s3]; rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have his2_sq : is2 ^ 2 = -2 := by
    dsimp [is2]
    calc (Complex.I * s2) ^ 2 = Complex.I ^ 2 * s2 ^ 2 := by ring
      _ = -2 := by rw [Complex.I_sq, hs2_sq]; ring
  have his3_sq : is3 ^ 2 = -3 := by
    dsimp [is3]
    calc (Complex.I * s3) ^ 2 = Complex.I ^ 2 * s3 ^ 2 := by ring
      _ = -3 := by rw [Complex.I_sq, hs3_sq]; ring
  have hno2 : ∀ q : ℚ, q ^ 2 ≠ 2 :=
    rat_sq_ne_of_prime_dvd Nat.prime_two (by decide) (by decide)
  have hno3 : ∀ q : ℚ, q ^ 2 ≠ 3 :=
    rat_sq_ne_of_prime_dvd Nat.prime_three (by decide) (by decide)
  have hno6 : ∀ q : ℚ, q ^ 2 ≠ 6 :=
    rat_sq_ne_of_prime_dvd Nat.prime_two (by decide) (by decide)
  -- Part 1: `f₁ = X^4 - 5*X^2 + 6`, `K₁ = ℚ(s2, s3) = ℚ(s2 + s3)`, `[K₁ : ℚ] = 4`.
  have hp1 : IsGarlingSplittingFieldExtension ℚ K₁ (Polynomial.X ^ 4 - 5 * Polynomial.X ^ 2 + 6) ∧
      Module.finrank ℚ K₁ = 4 ∧ extDegree ℚ K₁ = 4 ∧ K₁ = ℚ⟮s2 + s3⟯ := by
    let α₁ : Fin 4 → ℂ := ![s2, -s2, s3, -s3]
    have hexp₁ : GarlingSplitsExplicit ℚ ℂ (Polynomial.X ^ 4 - 5 * Polynomial.X ^ 2 + 6) 4 1 α₁ := by
      unfold GarlingSplitsExplicit
      have hmap : (Polynomial.X ^ 4 - 5 * Polynomial.X ^ 2 + 6 : ℚ[X]).map (algebraMap ℚ ℂ) =
          Polynomial.X ^ 4 - 5 * Polynomial.X ^ 2 + 6 := by simp
      rw [hmap]
      simp only [map_one, one_mul, α₁, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, mul_one, map_neg, sub_neg_eq_add]
      have hq2 : (Polynomial.X - Polynomial.C s2) * (Polynomial.X + Polynomial.C s2) =
          (Polynomial.X ^ 2 - 2 : ℂ[X]) := by
        calc (Polynomial.X - Polynomial.C s2) * (Polynomial.X + Polynomial.C s2)
            = Polynomial.X ^ 2 - Polynomial.C (s2 ^ 2) := by simp only [map_pow]; ring
          _ = Polynomial.X ^ 2 - 2 := by rw [hs2_sq, map_ofNat]
      have hq3 : (Polynomial.X - Polynomial.C s3) * (Polynomial.X + Polynomial.C s3) =
          (Polynomial.X ^ 2 - 3 : ℂ[X]) := by
        calc (Polynomial.X - Polynomial.C s3) * (Polynomial.X + Polynomial.C s3)
            = Polynomial.X ^ 2 - Polynomial.C (s3 ^ 2) := by simp only [map_pow]; ring
          _ = Polynomial.X ^ 2 - 3 := by rw [hs3_sq, map_ofNat]
      calc (Polynomial.X ^ 4 - 5 * Polynomial.X ^ 2 + 6 : ℂ[X])
          = (Polynomial.X ^ 2 - 2) * (Polynomial.X ^ 2 - 3) := by ring
        _ = ((Polynomial.X - Polynomial.C s2) * (Polynomial.X + Polynomial.C s2)) *
              ((Polynomial.X - Polynomial.C s3) * (Polynomial.X + Polynomial.C s3)) := by
              rw [hq2, hq3]
        _ = _ := by ring
    have hadj₁ : K₁ = IntermediateField.adjoin ℚ (Set.range α₁) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_le_iff]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hz2 | hz3
        · rw [hz2]; exact IntermediateField.subset_adjoin ℚ (Set.range α₁) ⟨0, by simp [α₁]⟩
        · rw [hz3]; exact IntermediateField.subset_adjoin ℚ (Set.range α₁) ⟨2, by simp [α₁]⟩
      · rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨i, rfl⟩
        have hs2K : s2 ∈ K₁ := IntermediateField.subset_adjoin ℚ ({s2, s3} : Set ℂ) (by simp)
        have hs3K : s3 ∈ K₁ := IntermediateField.subset_adjoin ℚ ({s2, s3} : Set ℂ) (by simp)
        fin_cases i
        · exact hs2K
        · exact neg_mem hs2K
        · exact hs3K
        · exact neg_mem hs3K
    have hf₁_mon : (Polynomial.X ^ 4 - 5 * Polynomial.X ^ 2 + 6 : ℚ[X]).Monic := by monicity!
    have hsf₁ : IsGarlingSplittingFieldExtension ℚ K₁
        (Polynomial.X ^ 4 - 5 * Polynomial.X ^ 2 + 6) :=
      isGarlingSplittingFieldExtension_of_eq_adjoin_range hf₁_mon.ne_zero hexp₁ hadj₁
    have hs2_not_Q : ∀ q : ℚ, algebraMap ℚ ℂ q ≠ s2 := fun q hq => by
      apply hno2 q
      have hsq : (q : ℂ) ^ 2 = 2 := by
        have hq' : (q : ℂ) = s2 := hq
        rw [hq', hs2_sq]
      exact_mod_cast hsq
    obtain ⟨hmin_s2, hfin_s2⟩ := minpoly_and_finrank_eq_two_of_aeval_deg_two_of_not_mem
      (p := (Polynomial.X ^ 2 - 2 : ℚ[X])) (by monicity!) (by compute_degree!)
      (by rw [map_sub, map_pow, Polynomial.aeval_X, map_ofNat, hs2_sq, sub_self]) hs2_not_Q
    have hs2_int : IsIntegral ℚ s2 :=
      ⟨Polynomial.X ^ 2 - Polynomial.C 2, Polynomial.monic_X_pow_sub_C 2 (by decide), by
        simp [hs2_sq]⟩
    have hs3_not_Qs2 : s3 ∉ ℚ⟮s2⟯ := by
      intro hmem
      obtain ⟨a, b, hab⟩ := exists_eq_add_mul_of_mem_adjoin_of_natDegree_eq_two hs2_int
        (by rw [hmin_s2]; compute_degree!) hmem
      have hre : Real.sqrt 3 = (a : ℝ) + (b : ℝ) * Real.sqrt 2 := by
        have h := congrArg Complex.re hab
        dsimp [s2, s3] at h
        simpa [Complex.add_re, Complex.mul_re] using h
      have hsqR : (3 : ℝ) = (a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 + 2 * (a : ℝ) * (b : ℝ) * Real.sqrt 2 := by
        calc (3 : ℝ) = (Real.sqrt 3) ^ 2 := (Real.sq_sqrt (by norm_num)).symm
          _ = ((a : ℝ) + (b : ℝ) * Real.sqrt 2) ^ 2 := by rw [hre]
          _ = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 * (Real.sqrt 2) ^ 2 + 2 * (a : ℝ) * (b : ℝ) * Real.sqrt 2 := by
                ring
          _ = (a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 + 2 * (a : ℝ) * (b : ℝ) * Real.sqrt 2 := by
                rw [Real.sq_sqrt (by norm_num)]; ring
      by_cases ha0 : a = 0
      · subst ha0
        have hbR : 2 * (b : ℝ) ^ 2 = 3 := by simpa using hsqR.symm
        have hbQ : (2 * b) ^ 2 = 6 := by
          have hbQ' : 2 * b ^ 2 = 3 := by exact_mod_cast hbR
          linear_combination 2 * hbQ'
        exact hno6 (2 * b) hbQ
      · by_cases hb0 : b = 0
        · subst hb0
          have haR : (a : ℝ) ^ 2 = 3 := by simpa using hsqR.symm
          exact hno3 a (by exact_mod_cast haR)
        · have hab_ne : (2 * (a : ℝ) * (b : ℝ)) ≠ 0 :=
            mul_ne_zero (mul_ne_zero two_ne_zero (Rat.cast_ne_zero.mpr ha0))
              (Rat.cast_ne_zero.mpr hb0)
          let c : ℚ := (3 - a ^ 2 - 2 * b ^ 2) / (2 * a * b)
          have hcR : (c : ℝ) = Real.sqrt 2 := by
            dsimp [c]; push_cast
            apply mul_right_cancel₀ hab_ne
            rw [div_mul_cancel₀ _ hab_ne]
            linarith
          have hc2R : (c : ℝ) ^ 2 = 2 := by rw [hcR, Real.sq_sqrt (by norm_num)]
          exact hno2 c (by exact_mod_cast hc2R)
    have hfin_K₁ : Module.finrank ℚ K₁ = 4 :=
      finrank_adjoin_pair_mul_two hfin_s2
        (p := (Polynomial.X ^ 2 - 3 : (ℚ⟮s2⟯)[X])) (by monicity!) (by compute_degree!)
        (by rw [map_sub, map_pow, Polynomial.aeval_X, map_ofNat, hs3_sq, sub_self])
        hs3_not_Qs2
    have hprim₁ : K₁ = ℚ⟮s2 + s3⟯ := by
      let γ : ℂ := s2 + s3
      have hs2_expr : (1 / 2 : ℂ) * (γ ^ 3 - 9 * γ) = s2 := by
        dsimp [γ]
        calc (1 / 2 : ℂ) * ((s2 + s3) ^ 3 - 9 * (s2 + s3))
            = (1 / 2 : ℂ) * (s2 * (s2 ^ 2 + 3 * s3 ^ 2 - 9) +
                s3 * (3 * s2 ^ 2 + s3 ^ 2 - 9)) := by ring
          _ = s2 := by rw [hs2_sq, hs3_sq]; ring
      apply le_antisymm
      · rw [IntermediateField.adjoin_le_iff]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        have hγ : γ ∈ ℚ⟮γ⟯ := IntermediateField.mem_adjoin_simple_self ℚ γ
        have hs2_mem : s2 ∈ ℚ⟮γ⟯ := by
          rw [← hs2_expr]
          exact mul_mem (div_mem ℚ⟮γ⟯.one_mem (ℚ⟮γ⟯.algebraMap_mem 2))
            (sub_mem (pow_mem hγ 3) (mul_mem (ℚ⟮γ⟯.algebraMap_mem 9) hγ))
        rcases hz with hz2 | hz3
        · rw [hz2]; exact hs2_mem
        · rw [hz3]
          have hs3_eq : γ - s2 = s3 := by dsimp [γ]; ring
          have hmem_sub : γ - s2 ∈ ℚ⟮γ⟯ := sub_mem hγ hs2_mem
          rwa [hs3_eq] at hmem_sub
      · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact add_mem (IntermediateField.subset_adjoin ℚ ({s2, s3} : Set ℂ) (by simp))
          (IntermediateField.subset_adjoin ℚ ({s2, s3} : Set ℂ) (by simp))
    have _ : Module.Finite ℚ K₁ :=
      (isFiniteExtension_iff_moduleFinite ℚ K₁).mp (corollary_to_theorem_7_1 hsf₁).1
    exact ⟨hsf₁, hfin_K₁, by rw [extDegree_eq_finrank ℚ K₁, hfin_K₁]; rfl, hprim₁⟩
  -- Part 2: `f₂ = X^4 + 5*X^2 + 6`, `K₂ = ℚ(is2, is3) = ℚ(is2 + is3)`, `[K₂ : ℚ] = 4`.
  have hp2 : IsGarlingSplittingFieldExtension ℚ K₂ (Polynomial.X ^ 4 + 5 * Polynomial.X ^ 2 + 6) ∧
      Module.finrank ℚ K₂ = 4 ∧ extDegree ℚ K₂ = 4 ∧ K₂ = ℚ⟮is2 + is3⟯ := by
    let α₂ : Fin 4 → ℂ := ![is2, -is2, is3, -is3]
    have hexp₂ : GarlingSplitsExplicit ℚ ℂ (Polynomial.X ^ 4 + 5 * Polynomial.X ^ 2 + 6) 4 1 α₂ := by
      unfold GarlingSplitsExplicit
      have hmap : (Polynomial.X ^ 4 + 5 * Polynomial.X ^ 2 + 6 : ℚ[X]).map (algebraMap ℚ ℂ) =
          Polynomial.X ^ 4 + 5 * Polynomial.X ^ 2 + 6 := by simp
      rw [hmap]
      simp only [map_one, one_mul, α₂, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, mul_one, map_neg, sub_neg_eq_add]
      have hq2 : (Polynomial.X - Polynomial.C is2) * (Polynomial.X + Polynomial.C is2) =
          (Polynomial.X ^ 2 + 2 : ℂ[X]) := by
        calc (Polynomial.X - Polynomial.C is2) * (Polynomial.X + Polynomial.C is2)
            = Polynomial.X ^ 2 - Polynomial.C (is2 ^ 2) := by simp only [map_pow]; ring
          _ = Polynomial.X ^ 2 + 2 := by rw [his2_sq, map_neg, map_ofNat]; ring
      have hq3 : (Polynomial.X - Polynomial.C is3) * (Polynomial.X + Polynomial.C is3) =
          (Polynomial.X ^ 2 + 3 : ℂ[X]) := by
        calc (Polynomial.X - Polynomial.C is3) * (Polynomial.X + Polynomial.C is3)
            = Polynomial.X ^ 2 - Polynomial.C (is3 ^ 2) := by simp only [map_pow]; ring
          _ = Polynomial.X ^ 2 + 3 := by rw [his3_sq, map_neg, map_ofNat]; ring
      calc (Polynomial.X ^ 4 + 5 * Polynomial.X ^ 2 + 6 : ℂ[X])
          = (Polynomial.X ^ 2 + 2) * (Polynomial.X ^ 2 + 3) := by ring
        _ = ((Polynomial.X - Polynomial.C is2) * (Polynomial.X + Polynomial.C is2)) *
              ((Polynomial.X - Polynomial.C is3) * (Polynomial.X + Polynomial.C is3)) := by
              rw [hq2, hq3]
        _ = _ := by ring
    have hadj₂ : K₂ = IntermediateField.adjoin ℚ (Set.range α₂) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_le_iff]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hz2 | hz3
        · rw [hz2]; exact IntermediateField.subset_adjoin ℚ (Set.range α₂) ⟨0, by simp [α₂]⟩
        · rw [hz3]; exact IntermediateField.subset_adjoin ℚ (Set.range α₂) ⟨2, by simp [α₂]⟩
      · rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨i, rfl⟩
        have his2K : is2 ∈ K₂ := IntermediateField.subset_adjoin ℚ ({is2, is3} : Set ℂ) (by simp)
        have his3K : is3 ∈ K₂ := IntermediateField.subset_adjoin ℚ ({is2, is3} : Set ℂ) (by simp)
        fin_cases i
        · exact his2K
        · exact neg_mem his2K
        · exact his3K
        · exact neg_mem his3K
    have hf₂_mon : (Polynomial.X ^ 4 + 5 * Polynomial.X ^ 2 + 6 : ℚ[X]).Monic := by monicity!
    have hsf₂ : IsGarlingSplittingFieldExtension ℚ K₂
        (Polynomial.X ^ 4 + 5 * Polynomial.X ^ 2 + 6) :=
      isGarlingSplittingFieldExtension_of_eq_adjoin_range hf₂_mon.ne_zero hexp₂ hadj₂
    have his2_eval : Polynomial.aeval is2 (Polynomial.X ^ 2 + 2 : ℚ[X]) = 0 := by
      rw [map_add, map_pow, Polynomial.aeval_X, map_ofNat, his2_sq]; ring
    have his2_not_Q : ∀ q : ℚ, algebraMap ℚ ℂ q ≠ is2 := fun q hq => by
      have him := congrArg Complex.im hq
      dsimp [is2, s2] at him
      simp [Complex.mul_im] at him
      linarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
    obtain ⟨hmin_is2, hfin_is2⟩ := minpoly_and_finrank_eq_two_of_aeval_deg_two_of_not_mem
      (p := (Polynomial.X ^ 2 + 2 : ℚ[X])) (by monicity!) (by compute_degree!)
      his2_eval his2_not_Q
    have his2_int : IsIntegral ℚ is2 :=
      ⟨Polynomial.X ^ 2 + 2, by monicity!, his2_eval⟩
    have his3_not_Qis2 : is3 ∉ ℚ⟮is2⟯ := by
      intro hmem
      obtain ⟨_a, b, hab⟩ := exists_eq_add_mul_of_mem_adjoin_of_natDegree_eq_two his2_int
        (by rw [hmin_is2]; compute_degree!) hmem
      have him : Real.sqrt 3 = (b : ℝ) * Real.sqrt 2 := by
        have h := congrArg Complex.im hab
        dsimp [is2, is3, s2, s3] at h
        simpa [Complex.add_im, Complex.mul_im] using h
      have hsqR : (3 : ℝ) = 2 * (b : ℝ) ^ 2 := by
        calc (3 : ℝ) = (Real.sqrt 3) ^ 2 := (Real.sq_sqrt (by norm_num)).symm
          _ = ((b : ℝ) * Real.sqrt 2) ^ 2 := by rw [him]
          _ = (b : ℝ) ^ 2 * (Real.sqrt 2) ^ 2 := by ring
          _ = 2 * (b : ℝ) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; ring
      have hbQ : 2 * b ^ 2 = 3 := by exact_mod_cast hsqR.symm
      exact hno6 (2 * b) (by linear_combination 2 * hbQ)
    have hfin_K₂ : Module.finrank ℚ K₂ = 4 :=
      finrank_adjoin_pair_mul_two hfin_is2
        (p := (Polynomial.X ^ 2 + 3 : (ℚ⟮is2⟯)[X])) (by monicity!) (by compute_degree!)
        (by rw [map_add, map_pow, Polynomial.aeval_X, map_ofNat, his3_sq]; ring)
        his3_not_Qis2
    have hprim₂ : K₂ = ℚ⟮is2 + is3⟯ := by
      let γ : ℂ := is2 + is3
      have his2_expr : (-1 / 2 : ℂ) * (γ ^ 3 + 9 * γ) = is2 := by
        dsimp [γ]
        calc (-1 / 2 : ℂ) * ((is2 + is3) ^ 3 + 9 * (is2 + is3))
            = (-1 / 2 : ℂ) * (is2 * (is2 ^ 2 + 3 * is3 ^ 2 + 9) +
                is3 * (3 * is2 ^ 2 + is3 ^ 2 + 9)) := by ring
          _ = is2 := by rw [his2_sq, his3_sq]; ring
      apply le_antisymm
      · rw [IntermediateField.adjoin_le_iff]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        have hγ : γ ∈ ℚ⟮γ⟯ := IntermediateField.mem_adjoin_simple_self ℚ γ
        have his2_mem : is2 ∈ ℚ⟮γ⟯ := by
          rw [← his2_expr]
          have hmhalf : (-1 / 2 : ℂ) ∈ ℚ⟮γ⟯ := by
            simpa using ℚ⟮γ⟯.algebraMap_mem (-1 / 2 : ℚ)
          exact mul_mem hmhalf
            (add_mem (pow_mem hγ 3) (mul_mem (ℚ⟮γ⟯.algebraMap_mem 9) hγ))
        rcases hz with hz2 | hz3
        · rw [hz2]; exact his2_mem
        · rw [hz3]
          have his3_eq : γ - is2 = is3 := by dsimp [γ]; ring
          have hmem_sub : γ - is2 ∈ ℚ⟮γ⟯ := sub_mem hγ his2_mem
          rwa [his3_eq] at hmem_sub
      · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact add_mem (IntermediateField.subset_adjoin ℚ ({is2, is3} : Set ℂ) (by simp))
          (IntermediateField.subset_adjoin ℚ ({is2, is3} : Set ℂ) (by simp))
    have _ : Module.Finite ℚ K₂ :=
      (isFiniteExtension_iff_moduleFinite ℚ K₂).mp (corollary_to_theorem_7_1 hsf₂).1
    exact ⟨hsf₂, hfin_K₂, by rw [extDegree_eq_finrank ℚ K₂, hfin_K₂]; rfl, hprim₂⟩
  -- Part 3: `f₃ = X^4 - 5`, `K₃ = ℚ(r5, i) = ℚ(r5 + i)`, `[K₃ : ℚ] = 8`.
  have hp3 : IsGarlingSplittingFieldExtension ℚ K₃ (Polynomial.X ^ 4 - 5) ∧
      Module.finrank ℚ K₃ = 8 ∧ extDegree ℚ K₃ = 8 ∧ K₃ = ℚ⟮r5 + Complex.I⟯ := by
    let r5R : ℝ := (5 : ℝ) ^ ((1 : ℝ) / 4)
    obtain ⟨hr5R_pow, _, hr5R_min, _⟩ :=
      real_rpow_inv_nat_minpoly_of_prime (by decide : Nat.Prime 5) (by decide : 1 ≤ 4)
    have hr5R_eq : ((5 : ℕ) : ℝ) ^ ((1 : ℝ) / (4 : ℕ)) = r5R := by simp [r5R]
    rw [hr5R_eq] at hr5R_pow hr5R_min
    have hr5_coe : (IsScalarTower.toAlgHom ℚ ℝ ℂ) r5R = r5 := rfl
    have hr5_pow : r5 ^ 4 = 5 := by
      change ((r5R : ℂ) ^ 4) = 5
      rw [← Complex.ofReal_pow, hr5R_pow]; norm_num
    have hr5_ne0 : r5 ≠ 0 := fun h0 => by
      rw [h0] at hr5_pow; norm_num at hr5_pow
    have hr5_min : minpoly ℚ r5 = Polynomial.X ^ 4 - 5 := by
      rw [← hr5_coe, minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ ℝ ℂ) Complex.ofReal_injective r5R,
        hr5R_min]
      norm_num
      rw [map_ofNat]
    have hr5_int : IsIntegral ℚ r5 :=
      ⟨Polynomial.X ^ 4 - Polynomial.C 5, Polynomial.monic_X_pow_sub_C 5 (by decide), by
        simp [hr5_pow]⟩
    have hfin_r5 : Module.finrank ℚ ℚ⟮r5⟯ = 4 := by
      rw [IntermediateField.adjoin.finrank hr5_int, hr5_min, ← map_ofNat Polynomial.C 5,
        Polynomial.natDegree_X_pow_sub_C]
    let α₃ : Fin 4 → ℂ := ![r5, -r5, Complex.I * r5, -(Complex.I * r5)]
    have hexp₃ : GarlingSplitsExplicit ℚ ℂ (Polynomial.X ^ 4 - 5) 4 1 α₃ := by
      unfold GarlingSplitsExplicit
      have hmap : (Polynomial.X ^ 4 - 5 : ℚ[X]).map (algebraMap ℚ ℂ) = Polynomial.X ^ 4 - 5 := by
        simp
      rw [hmap]
      simp only [map_one, one_mul, α₃, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, mul_one, map_neg, sub_neg_eq_add]
      have hq1 : (Polynomial.X - Polynomial.C r5) * (Polynomial.X + Polynomial.C r5) =
          (Polynomial.X ^ 2 - Polynomial.C (r5 ^ 2) : ℂ[X]) := by
        simp only [map_pow]; ring
      have hq2 : (Polynomial.X - Polynomial.C (Complex.I * r5)) *
          (Polynomial.X + Polynomial.C (Complex.I * r5)) =
          (Polynomial.X ^ 2 + Polynomial.C (r5 ^ 2) : ℂ[X]) := by
        calc (Polynomial.X - Polynomial.C (Complex.I * r5)) *
              (Polynomial.X + Polynomial.C (Complex.I * r5))
            = Polynomial.X ^ 2 - Polynomial.C (Complex.I ^ 2 * r5 ^ 2) := by
              simp only [map_mul, map_pow]; ring
          _ = Polynomial.X ^ 2 + Polynomial.C (r5 ^ 2) := by
              rw [Complex.I_sq, neg_one_mul, map_neg]; ring
      calc (Polynomial.X ^ 4 - 5 : ℂ[X])
          = Polynomial.X ^ 4 - Polynomial.C (r5 ^ 4) := by rw [hr5_pow, map_ofNat]
        _ = (Polynomial.X ^ 2 - Polynomial.C (r5 ^ 2)) *
              (Polynomial.X ^ 2 + Polynomial.C (r5 ^ 2)) := by simp only [map_pow]; ring
        _ = ((Polynomial.X - Polynomial.C r5) * (Polynomial.X + Polynomial.C r5)) *
              ((Polynomial.X - Polynomial.C (Complex.I * r5)) *
               (Polynomial.X + Polynomial.C (Complex.I * r5))) := by rw [hq1, hq2]
        _ = _ := by ring
    have hadj₃ : K₃ = IntermediateField.adjoin ℚ (Set.range α₃) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_le_iff]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        have hr5_mem : r5 ∈ IntermediateField.adjoin ℚ (Set.range α₃) :=
          IntermediateField.subset_adjoin ℚ (Set.range α₃) ⟨0, by simp [α₃]⟩
        rcases hz with hzr | hzi
        · rw [hzr]; exact hr5_mem
        · rw [hzi]
          have hir5_mem : Complex.I * r5 ∈ IntermediateField.adjoin ℚ (Set.range α₃) :=
            IntermediateField.subset_adjoin ℚ (Set.range α₃) ⟨2, by simp [α₃]⟩
          have hdiv : (Complex.I * r5) / r5 = Complex.I := mul_div_cancel_right₀ Complex.I hr5_ne0
          exact hdiv ▸ div_mem hir5_mem hr5_mem
      · rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨i, rfl⟩
        have hr5K : r5 ∈ K₃ := IntermediateField.subset_adjoin ℚ ({r5, Complex.I} : Set ℂ) (by simp)
        have hiK : Complex.I ∈ K₃ :=
          IntermediateField.subset_adjoin ℚ ({r5, Complex.I} : Set ℂ) (by simp)
        fin_cases i
        · exact hr5K
        · exact neg_mem hr5K
        · exact mul_mem hiK hr5K
        · exact neg_mem (mul_mem hiK hr5K)
    have hf₃_mon : (Polynomial.X ^ 4 - 5 : ℚ[X]).Monic := by
      rw [← map_ofNat Polynomial.C 5]
      exact Polynomial.monic_X_pow_sub_C 5 (by decide)
    have hsf₃ : IsGarlingSplittingFieldExtension ℚ K₃ (Polynomial.X ^ 4 - 5) :=
      isGarlingSplittingFieldExtension_of_eq_adjoin_range hf₃_mon.ne_zero hexp₃ hadj₃
    have hI_not_Qr5 : Complex.I ∉ ℚ⟮r5⟯ := complex_I_not_mem_adjoin_ofReal r5R
    have hfin_K₃ : Module.finrank ℚ K₃ = 8 :=
      finrank_adjoin_pair_mul_two hfin_r5
        (p := (Polynomial.X ^ 2 + 1 : (ℚ⟮r5⟯)[X])) (by monicity!) (by compute_degree!)
        (by rw [map_add, map_pow, Polynomial.aeval_X, map_one, Complex.I_sq]; ring)
        hI_not_Qr5
    have hprim₃ : K₃ = ℚ⟮r5 + Complex.I⟯ := by
      let γ : ℂ := r5 + Complex.I
      have hrel : γ ^ 4 - 6 * γ ^ 2 - 4 = (4 * γ ^ 3 - 4 * γ) * Complex.I := by
        have hr5_sub : (γ - Complex.I) ^ 4 = 5 := by
          have h : γ - Complex.I = r5 := by dsimp [γ]; ring
          rw [h, hr5_pow]
        have hexp_sub : (γ - Complex.I) ^ 4 =
            (γ ^ 4 - 6 * γ ^ 2 + 1) - (4 * γ ^ 3 - 4 * γ) * Complex.I := by
          calc (γ - Complex.I) ^ 4
              = γ ^ 4 - 4 * γ ^ 3 * Complex.I + 6 * γ ^ 2 * Complex.I ^ 2 -
                  4 * γ * (Complex.I ^ 2 * Complex.I) + (Complex.I ^ 2) ^ 2 := by ring
            _ = (γ ^ 4 - 6 * γ ^ 2 + 1) - (4 * γ ^ 3 - 4 * γ) * Complex.I := by
                  rw [Complex.I_sq]; ring
        linear_combination hexp_sub.symm.trans hr5_sub
      have hden_ne : 4 * γ ^ 3 - 4 * γ ≠ 0 := by
        have hfac : 4 * γ ^ 3 - 4 * γ = 4 * γ * (γ - 1) * (γ + 1) := by ring
        rw [hfac]
        have hγ_im : γ.im = 1 := by
          change ((r5R : ℂ) + Complex.I).im = 1
          simp
        refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) ?_
        · intro h0; rw [h0, Complex.zero_im] at hγ_im; norm_num at hγ_im
        · intro h0
          have him := congrArg Complex.im h0
          simp [hγ_im] at him
        · intro h0
          have him := congrArg Complex.im h0
          simp [hγ_im] at him
      have hI_expr : (γ ^ 4 - 6 * γ ^ 2 - 4) / (4 * γ ^ 3 - 4 * γ) = Complex.I := by
        rw [hrel, mul_div_cancel_left₀ _ hden_ne]
      apply le_antisymm
      · rw [IntermediateField.adjoin_le_iff]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        have hγ : γ ∈ ℚ⟮γ⟯ := IntermediateField.mem_adjoin_simple_self ℚ γ
        have hI_mem : Complex.I ∈ ℚ⟮γ⟯ := by
          rw [← hI_expr]
          exact div_mem
            (sub_mem (sub_mem (pow_mem hγ 4) (mul_mem (ℚ⟮γ⟯.algebraMap_mem 6) (pow_mem hγ 2)))
              (ℚ⟮γ⟯.algebraMap_mem 4))
            (sub_mem (mul_mem (ℚ⟮γ⟯.algebraMap_mem 4) (pow_mem hγ 3))
              (mul_mem (ℚ⟮γ⟯.algebraMap_mem 4) hγ))
        rcases hz with hzr | hzi
        · rw [hzr]
          have hr5_eq : γ - Complex.I = r5 := by dsimp [γ]; ring
          have hmem_sub : γ - Complex.I ∈ ℚ⟮γ⟯ := sub_mem hγ hI_mem
          rwa [hr5_eq] at hmem_sub
        · rw [hzi]; exact hI_mem
      · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact add_mem (IntermediateField.subset_adjoin ℚ ({r5, Complex.I} : Set ℂ) (by simp))
          (IntermediateField.subset_adjoin ℚ ({r5, Complex.I} : Set ℂ) (by simp))
    have _ : Module.Finite ℚ K₃ :=
      (isFiniteExtension_iff_moduleFinite ℚ K₃).mp (corollary_to_theorem_7_1 hsf₃).1
    exact ⟨hsf₃, hfin_K₃, by rw [extDegree_eq_finrank ℚ K₃, hfin_K₃]; rfl, hprim₃⟩
  exact ⟨hp1, hp2, hp3⟩

/-! ### Exercise 7.8 (§7.3, printed p. 70 / PDF p. 78) -/

/-- Primitive eighth root of unity `ζ₈ = (1 + i) / √2 ∈ ℂ` (`Exercise 7.8`, printed p. 70). -/
noncomputable def zeta8 : ℂ :=
  (1 + Complex.I) / ((Real.sqrt 2 : ℝ) : ℂ)

/-- **Exercise 7.8** (§7.3, printed p. 70 / PDF p. 78):
*"Find a splitting field extension `K : ℚ` for each of the following polynomials over `ℚ`:
`x^4 + 1`, `x^4 + 4`, `(x^4 + 1)(x^4 + 4)`, `(x^4 - 1)(x^4 + 4)`.
In each case determine the degree `[K : ℚ]` and find `α` such that `K = ℚ(α)`."*

Explicit splitting fields, degrees, and primitive elements proved here (with `ζ₈ = (1 + i)/√2`):
1. `x^4 + 1`: splitting field `ℚ(ζ₈) = ℚ(√2, i)` over `ℚ`, degree `4`, primitive element `ζ₈`;
2. `x^4 + 4 = (x^2 - 2x + 2)(x^2 + 2x + 2)`: splitting field `ℚ(i)` over `ℚ`, degree `2`,
   primitive element `i`;
3. `(x^4 + 1)(x^4 + 4)`: splitting field `ℚ(ζ₈)` over `ℚ`, degree `4`, primitive element `ζ₈`;
4. `(x^4 - 1)(x^4 + 4)`: splitting field `ℚ(i)` over `ℚ`, degree `2`, primitive element `i`. -/
theorem exercise_7_8 :
    let ζ : ℂ := zeta8
    (ℚ⟮ζ⟯ = IntermediateField.adjoin ℚ ({((Real.sqrt 2 : ℝ) : ℂ), Complex.I} : Set ℂ)) ∧
    (IsGarlingSplittingFieldExtension ℚ ℚ⟮ζ⟯ (Polynomial.X ^ 4 + 1) ∧
      Module.finrank ℚ ℚ⟮ζ⟯ = 4 ∧ extDegree ℚ ℚ⟮ζ⟯ = 4 ∧ ℚ⟮ζ⟯ = ℚ⟮ζ⟯) ∧
    (IsGarlingSplittingFieldExtension ℚ ℚ⟮Complex.I⟯ (Polynomial.X ^ 4 + 4) ∧
      Module.finrank ℚ ℚ⟮Complex.I⟯ = 2 ∧ extDegree ℚ ℚ⟮Complex.I⟯ = 2 ∧
      ℚ⟮Complex.I⟯ = ℚ⟮Complex.I⟯) ∧
    (IsGarlingSplittingFieldExtension ℚ ℚ⟮ζ⟯
        ((Polynomial.X ^ 4 + 1) * (Polynomial.X ^ 4 + 4)) ∧
      Module.finrank ℚ ℚ⟮ζ⟯ = 4 ∧ extDegree ℚ ℚ⟮ζ⟯ = 4 ∧ ℚ⟮ζ⟯ = ℚ⟮ζ⟯) ∧
    (IsGarlingSplittingFieldExtension ℚ ℚ⟮Complex.I⟯
        ((Polynomial.X ^ 4 - 1) * (Polynomial.X ^ 4 + 4)) ∧
      Module.finrank ℚ ℚ⟮Complex.I⟯ = 2 ∧ extDegree ℚ ℚ⟮Complex.I⟯ = 2 ∧
      ℚ⟮Complex.I⟯ = ℚ⟮Complex.I⟯) := by
  intro ζ
  let s2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
  have hs2_sq : s2 ^ 2 = 2 := by
    dsimp [s2]; rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs2_ne0 : s2 ≠ 0 := fun h0 => by
    rw [h0] at hs2_sq; norm_num at hs2_sq
  have hζ_sq : ζ ^ 2 = Complex.I := by
    change ((1 + Complex.I) / s2) ^ 2 = Complex.I
    rw [div_pow, hs2_sq]
    calc (1 + Complex.I) ^ 2 / 2 = (1 + 2 * Complex.I + Complex.I ^ 2) / 2 := by ring
      _ = Complex.I := by rw [Complex.I_sq]; ring
  have hζ_sub_cube : ζ - ζ ^ 3 = s2 := by
    have hcube : ζ ^ 3 = Complex.I * ζ := by
      calc ζ ^ 3 = ζ ^ 2 * ζ := by ring
        _ = Complex.I * ζ := by rw [hζ_sq]
    rw [hcube]
    change (1 + Complex.I) / s2 - Complex.I * ((1 + Complex.I) / s2) = s2
    apply mul_right_cancel₀ hs2_ne0
    calc ((1 + Complex.I) / s2 - Complex.I * ((1 + Complex.I) / s2)) * s2
        = ((1 + Complex.I) / s2 * s2) - Complex.I * ((1 + Complex.I) / s2 * s2) := by ring
      _ = (1 + Complex.I) - Complex.I * (1 + Complex.I) := by rw [div_mul_cancel₀ _ hs2_ne0]
      _ = 1 - Complex.I ^ 2 := by ring
      _ = 2 := by rw [Complex.I_sq]; ring
      _ = s2 * s2 := by linear_combination -hs2_sq
  have hζ_adjoin : ℚ⟮ζ⟯ = IntermediateField.adjoin ℚ ({s2, Complex.I} : Set ℂ) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      change (1 + Complex.I) / s2 ∈ IntermediateField.adjoin ℚ ({s2, Complex.I} : Set ℂ)
      exact div_mem
        (add_mem (IntermediateField.adjoin ℚ ({s2, Complex.I} : Set ℂ)).one_mem
          (IntermediateField.subset_adjoin ℚ ({s2, Complex.I} : Set ℂ) (by simp)))
        (IntermediateField.subset_adjoin ℚ ({s2, Complex.I} : Set ℂ) (by simp))
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      have hζ_mem : ζ ∈ ℚ⟮ζ⟯ := IntermediateField.mem_adjoin_simple_self ℚ ζ
      rcases hz with hz2 | hzi
      · rw [hz2, ← hζ_sub_cube]
        exact sub_mem hζ_mem (pow_mem hζ_mem 3)
      · rw [hzi, ← hζ_sq]
        exact pow_mem hζ_mem 2
  -- Degrees `[ℚ(i) : ℚ] = 2` and `[ℚ(ζ₈) : ℚ] = 4`.
  have hI_not_Q : ∀ q : ℚ, algebraMap ℚ ℂ q ≠ Complex.I := fun q hq => by
    have him := congrArg Complex.im hq; simp at him
  have hfin_I : Module.finrank ℚ ℚ⟮Complex.I⟯ = 2 :=
    (minpoly_and_finrank_eq_two_of_aeval_deg_two_of_not_mem
      (p := (Polynomial.X ^ 2 + 1 : ℚ[X])) (by monicity!) (by compute_degree!)
      (by simp [Complex.I_sq]) hI_not_Q).2
  have hs2_not_Q : ∀ q : ℚ, algebraMap ℚ ℂ q ≠ s2 := fun q hq => by
    apply rat_sq_ne_of_prime_dvd (n := 2) Nat.prime_two (by decide) (by decide) q
    have hsq : (q : ℂ) ^ 2 = 2 := by
      have hq' : (q : ℂ) = s2 := hq
      rw [hq', hs2_sq]
    exact_mod_cast hsq
  have hfin_s2 : Module.finrank ℚ ℚ⟮s2⟯ = 2 :=
    (minpoly_and_finrank_eq_two_of_aeval_deg_two_of_not_mem
      (p := (Polynomial.X ^ 2 - 2 : ℚ[X])) (by monicity!) (by compute_degree!)
      (by rw [map_sub, map_pow, Polynomial.aeval_X, map_ofNat, hs2_sq, sub_self]) hs2_not_Q).2
  have hfin_ζ : Module.finrank ℚ ℚ⟮ζ⟯ = 4 := by
    rw [hζ_adjoin]
    exact finrank_adjoin_pair_mul_two hfin_s2
      (p := (Polynomial.X ^ 2 + 1 : (ℚ⟮s2⟯)[X])) (by monicity!) (by compute_degree!)
      (by rw [map_add, map_pow, Polynomial.aeval_X, map_one, Complex.I_sq]; ring)
      (complex_I_not_mem_adjoin_ofReal (Real.sqrt 2))
  -- Explicit linear factorizations in `ℂ[X]`.
  let β₁ : Fin 4 → ℂ := ![ζ, -ζ, Complex.I * ζ, -(Complex.I * ζ)]
  let β₂ : Fin 4 → ℂ := ![1 + Complex.I, 1 - Complex.I, -1 + Complex.I, -1 - Complex.I]
  have hfac₁ : (Polynomial.X ^ 4 + 1 : ℂ[X]) =
      ∏ i : Fin 4, (Polynomial.X - Polynomial.C (β₁ i)) := by
    simp only [β₁, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, mul_one, map_neg, sub_neg_eq_add]
    have hp1 : (Polynomial.X - Polynomial.C ζ) * (Polynomial.X + Polynomial.C ζ) =
        (Polynomial.X ^ 2 - Polynomial.C Complex.I : ℂ[X]) := by
      calc (Polynomial.X - Polynomial.C ζ) * (Polynomial.X + Polynomial.C ζ)
          = Polynomial.X ^ 2 - Polynomial.C (ζ ^ 2) := by simp only [map_pow]; ring
        _ = Polynomial.X ^ 2 - Polynomial.C Complex.I := by rw [hζ_sq]
    have hp2 : (Polynomial.X - Polynomial.C (Complex.I * ζ)) *
        (Polynomial.X + Polynomial.C (Complex.I * ζ)) =
        (Polynomial.X ^ 2 + Polynomial.C Complex.I : ℂ[X]) := by
      calc (Polynomial.X - Polynomial.C (Complex.I * ζ)) *
            (Polynomial.X + Polynomial.C (Complex.I * ζ))
          = Polynomial.X ^ 2 - Polynomial.C (Complex.I ^ 2 * ζ ^ 2) := by
            simp only [map_mul, map_pow]; ring
        _ = Polynomial.X ^ 2 + Polynomial.C Complex.I := by
            rw [Complex.I_sq, hζ_sq, neg_one_mul, map_neg]; ring
    calc (Polynomial.X ^ 4 + 1 : ℂ[X])
        = Polynomial.X ^ 4 - Polynomial.C (Complex.I ^ 2) := by
            rw [Complex.I_sq, map_neg, map_one]; ring
      _ = (Polynomial.X ^ 2 - Polynomial.C Complex.I) *
            (Polynomial.X ^ 2 + Polynomial.C Complex.I) := by simp only [map_pow]; ring
      _ = ((Polynomial.X - Polynomial.C ζ) * (Polynomial.X + Polynomial.C ζ)) *
            ((Polynomial.X - Polynomial.C (Complex.I * ζ)) *
             (Polynomial.X + Polynomial.C (Complex.I * ζ))) := by rw [hp1, hp2]
      _ = _ := by ring
  have hfac₂ : (Polynomial.X ^ 4 + 4 : ℂ[X]) =
      ∏ i : Fin 4, (Polynomial.X - Polynomial.C (β₂ i)) := by
    simp only [β₂, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, mul_one]
    have hq1 : (Polynomial.X - Polynomial.C (1 + Complex.I)) *
        (Polynomial.X - Polynomial.C (1 - Complex.I)) =
        (Polynomial.X ^ 2 - 2 * Polynomial.X + 2 : ℂ[X]) := by
      calc (Polynomial.X - Polynomial.C (1 + Complex.I)) *
            (Polynomial.X - Polynomial.C (1 - Complex.I))
          = Polynomial.X ^ 2 - 2 * Polynomial.X + Polynomial.C (1 - Complex.I ^ 2) := by
            simp only [map_add, map_sub, map_one, map_pow]; ring
        _ = Polynomial.X ^ 2 - 2 * Polynomial.X + 2 := by
            rw [Complex.I_sq]; norm_num; rw [map_ofNat]
    have hq2 : (Polynomial.X - Polynomial.C (-1 + Complex.I)) *
        (Polynomial.X - Polynomial.C (-1 - Complex.I)) =
        (Polynomial.X ^ 2 + 2 * Polynomial.X + 2 : ℂ[X]) := by
      calc (Polynomial.X - Polynomial.C (-1 + Complex.I)) *
            (Polynomial.X - Polynomial.C (-1 - Complex.I))
          = Polynomial.X ^ 2 + 2 * Polynomial.X + Polynomial.C (1 - Complex.I ^ 2) := by
            simp only [map_add, map_sub, map_neg, map_one, map_pow]; ring
        _ = Polynomial.X ^ 2 + 2 * Polynomial.X + 2 := by
            rw [Complex.I_sq]; norm_num; rw [map_ofNat]
    calc (Polynomial.X ^ 4 + 4 : ℂ[X])
        = (Polynomial.X ^ 2 - 2 * Polynomial.X + 2) *
            (Polynomial.X ^ 2 + 2 * Polynomial.X + 2) := by ring
      _ = ((Polynomial.X - Polynomial.C (1 + Complex.I)) *
            (Polynomial.X - Polynomial.C (1 - Complex.I))) *
          ((Polynomial.X - Polynomial.C (-1 + Complex.I)) *
            (Polynomial.X - Polynomial.C (-1 - Complex.I))) := by rw [hq1, hq2]
      _ = _ := by ring
  -- 1. `g₁ = X^4 + 1`.
  have hexp₁ : GarlingSplitsExplicit ℚ ℂ (Polynomial.X ^ 4 + 1) 4 1 β₁ := by
    unfold GarlingSplitsExplicit
    have hmap : (Polynomial.X ^ 4 + 1 : ℚ[X]).map (algebraMap ℚ ℂ) = Polynomial.X ^ 4 + 1 := by
      simp
    rw [hmap]
    simp only [map_one, one_mul]
    exact hfac₁
  have hadj₁ : ℚ⟮ζ⟯ = IntermediateField.adjoin ℚ (Set.range β₁) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact IntermediateField.subset_adjoin ℚ (Set.range β₁) ⟨0, by simp [β₁]⟩
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      have hζ_mem : ζ ∈ ℚ⟮ζ⟯ := IntermediateField.mem_adjoin_simple_self ℚ ζ
      have hI_mem : Complex.I ∈ ℚ⟮ζ⟯ := hζ_sq ▸ pow_mem hζ_mem 2
      fin_cases i
      · exact hζ_mem
      · exact neg_mem hζ_mem
      · exact mul_mem hI_mem hζ_mem
      · exact neg_mem (mul_mem hI_mem hζ_mem)
  have hsf₁ : IsGarlingSplittingFieldExtension ℚ ℚ⟮ζ⟯ (Polynomial.X ^ 4 + 1) :=
    isGarlingSplittingFieldExtension_of_eq_adjoin_range
      (Polynomial.monic_X_pow_add_C (1 : ℚ) (by decide)).ne_zero hexp₁ hadj₁
  -- 2. `g₂ = X^4 + 4`.
  have hexp₂ : GarlingSplitsExplicit ℚ ℂ (Polynomial.X ^ 4 + 4) 4 1 β₂ := by
    unfold GarlingSplitsExplicit
    have hmap : (Polynomial.X ^ 4 + 4 : ℚ[X]).map (algebraMap ℚ ℂ) = Polynomial.X ^ 4 + 4 := by
      simp
    rw [hmap]
    simp only [map_one, one_mul]
    exact hfac₂
  have hadj₂ : ℚ⟮Complex.I⟯ = IntermediateField.adjoin ℚ (Set.range β₂) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      have h1I : 1 + Complex.I ∈ IntermediateField.adjoin ℚ (Set.range β₂) :=
        IntermediateField.subset_adjoin ℚ (Set.range β₂) ⟨0, by simp [β₂]⟩
      have hsub : (1 + Complex.I) - 1 = Complex.I := by ring
      exact hsub ▸ sub_mem h1I (IntermediateField.adjoin ℚ (Set.range β₂)).one_mem
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      have hI_mem : Complex.I ∈ ℚ⟮Complex.I⟯ :=
        IntermediateField.mem_adjoin_simple_self ℚ Complex.I
      fin_cases i
      · exact add_mem ℚ⟮Complex.I⟯.one_mem hI_mem
      · exact sub_mem ℚ⟮Complex.I⟯.one_mem hI_mem
      · exact add_mem (neg_mem ℚ⟮Complex.I⟯.one_mem) hI_mem
      · exact sub_mem (neg_mem ℚ⟮Complex.I⟯.one_mem) hI_mem
  have hg₂_mon : (Polynomial.X ^ 4 + 4 : ℚ[X]).Monic := by
    rw [← map_ofNat Polynomial.C 4]
    exact Polynomial.monic_X_pow_add_C 4 (by decide)
  have hsf₂ : IsGarlingSplittingFieldExtension ℚ ℚ⟮Complex.I⟯ (Polynomial.X ^ 4 + 4) :=
    isGarlingSplittingFieldExtension_of_eq_adjoin_range hg₂_mon.ne_zero hexp₂ hadj₂
  -- 3. `g₃ = (X^4 + 1)(X^4 + 4)`.
  let β₃ : Fin 8 → ℂ :=
    ![ζ, -ζ, Complex.I * ζ, -(Complex.I * ζ),
      1 + Complex.I, 1 - Complex.I, -1 + Complex.I, -1 - Complex.I]
  have hexp₃ : GarlingSplitsExplicit ℚ ℂ ((Polynomial.X ^ 4 + 1) * (Polynomial.X ^ 4 + 4)) 8 1
      β₃ := by
    unfold GarlingSplitsExplicit
    have hmap : (((Polynomial.X ^ 4 + 1) * (Polynomial.X ^ 4 + 4) : ℚ[X]).map (algebraMap ℚ ℂ)) =
        (Polynomial.X ^ 4 + 1) * (Polynomial.X ^ 4 + 4) := by simp
    rw [hmap, hfac₁, hfac₂]
    simp only [map_one, one_mul, β₁, β₂, β₃, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one]
    ring
  have hadj₃ : ℚ⟮ζ⟯ = IntermediateField.adjoin ℚ (Set.range β₃) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact IntermediateField.subset_adjoin ℚ (Set.range β₃) ⟨0, by simp [β₃]⟩
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      have hζ_mem : ζ ∈ ℚ⟮ζ⟯ := IntermediateField.mem_adjoin_simple_self ℚ ζ
      have hI_mem : Complex.I ∈ ℚ⟮ζ⟯ := hζ_sq ▸ pow_mem hζ_mem 2
      fin_cases i
      · exact hζ_mem
      · exact neg_mem hζ_mem
      · exact mul_mem hI_mem hζ_mem
      · exact neg_mem (mul_mem hI_mem hζ_mem)
      · exact add_mem ℚ⟮ζ⟯.one_mem hI_mem
      · exact sub_mem ℚ⟮ζ⟯.one_mem hI_mem
      · exact add_mem (neg_mem ℚ⟮ζ⟯.one_mem) hI_mem
      · exact sub_mem (neg_mem ℚ⟮ζ⟯.one_mem) hI_mem
  have hg₃_ne0 : ((Polynomial.X ^ 4 + 1) * (Polynomial.X ^ 4 + 4) : ℚ[X]) ≠ 0 :=
    mul_ne_zero (Polynomial.monic_X_pow_add_C (1 : ℚ) (by decide)).ne_zero hg₂_mon.ne_zero
  have hsf₃ : IsGarlingSplittingFieldExtension ℚ ℚ⟮ζ⟯
      ((Polynomial.X ^ 4 + 1) * (Polynomial.X ^ 4 + 4)) :=
    isGarlingSplittingFieldExtension_of_eq_adjoin_range hg₃_ne0 hexp₃ hadj₃
  -- 4. `g₄ = (X^4 - 1)(X^4 + 4)`.
  let β₄ : Fin 8 → ℂ :=
    ![1, -1, Complex.I, -Complex.I,
      1 + Complex.I, 1 - Complex.I, -1 + Complex.I, -1 - Complex.I]
  have hfac_m1 : (Polynomial.X ^ 4 - 1 : ℂ[X]) =
      (Polynomial.X - 1) * (Polynomial.X + 1) *
      (Polynomial.X - Polynomial.C Complex.I) * (Polynomial.X + Polynomial.C Complex.I) := by
    calc (Polynomial.X ^ 4 - 1 : ℂ[X])
        = (Polynomial.X ^ 2 - 1) * (Polynomial.X ^ 2 - Polynomial.C (Complex.I ^ 2)) := by
            rw [Complex.I_sq, map_neg, map_one]; ring
      _ = (Polynomial.X - 1) * (Polynomial.X + 1) *
            (Polynomial.X - Polynomial.C Complex.I) * (Polynomial.X + Polynomial.C Complex.I) := by
            simp only [map_pow]; ring
  have hexp₄ : GarlingSplitsExplicit ℚ ℂ ((Polynomial.X ^ 4 - 1) * (Polynomial.X ^ 4 + 4)) 8 1
      β₄ := by
    unfold GarlingSplitsExplicit
    have hmap : (((Polynomial.X ^ 4 - 1) * (Polynomial.X ^ 4 + 4) : ℚ[X]).map (algebraMap ℚ ℂ)) =
        (Polynomial.X ^ 4 - 1) * (Polynomial.X ^ 4 + 4) := by simp
    rw [hmap, hfac_m1, hfac₂]
    simp only [β₂, β₄, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, mul_one, map_one, one_mul, map_neg, sub_neg_eq_add]
    ring
  have hadj₄ : ℚ⟮Complex.I⟯ = IntermediateField.adjoin ℚ (Set.range β₄) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact IntermediateField.subset_adjoin ℚ (Set.range β₄) ⟨2, by simp [β₄]⟩
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      have hI_mem : Complex.I ∈ ℚ⟮Complex.I⟯ :=
        IntermediateField.mem_adjoin_simple_self ℚ Complex.I
      fin_cases i
      · exact ℚ⟮Complex.I⟯.one_mem
      · exact neg_mem ℚ⟮Complex.I⟯.one_mem
      · exact hI_mem
      · exact neg_mem hI_mem
      · exact add_mem ℚ⟮Complex.I⟯.one_mem hI_mem
      · exact sub_mem ℚ⟮Complex.I⟯.one_mem hI_mem
      · exact add_mem (neg_mem ℚ⟮Complex.I⟯.one_mem) hI_mem
      · exact sub_mem (neg_mem ℚ⟮Complex.I⟯.one_mem) hI_mem
  have hg₄_ne0 : ((Polynomial.X ^ 4 - 1) * (Polynomial.X ^ 4 + 4) : ℚ[X]) ≠ 0 :=
    mul_ne_zero (Polynomial.monic_X_pow_sub_C (1 : ℚ) (by decide)).ne_zero hg₂_mon.ne_zero
  have hsf₄ : IsGarlingSplittingFieldExtension ℚ ℚ⟮Complex.I⟯
      ((Polynomial.X ^ 4 - 1) * (Polynomial.X ^ 4 + 4)) :=
    isGarlingSplittingFieldExtension_of_eq_adjoin_range hg₄_ne0 hexp₄ hadj₄
  have _ : Module.Finite ℚ ℚ⟮ζ⟯ :=
    (isFiniteExtension_iff_moduleFinite ℚ ℚ⟮ζ⟯).mp (corollary_to_theorem_7_1 hsf₁).1
  have _ : Module.Finite ℚ ℚ⟮Complex.I⟯ :=
    (isFiniteExtension_iff_moduleFinite ℚ ℚ⟮Complex.I⟯).mp (corollary_to_theorem_7_1 hsf₂).1
  have hext_ζ : extDegree ℚ ℚ⟮ζ⟯ = 4 := by rw [extDegree_eq_finrank ℚ ℚ⟮ζ⟯, hfin_ζ]; rfl
  have hext_I : extDegree ℚ ℚ⟮Complex.I⟯ = 2 := by
    rw [extDegree_eq_finrank ℚ ℚ⟮Complex.I⟯, hfin_I]; rfl
  exact ⟨hζ_adjoin, ⟨hsf₁, hfin_ζ, hext_ζ, rfl⟩, ⟨hsf₂, hfin_I, hext_I, rfl⟩,
    ⟨hsf₃, hfin_ζ, hext_ζ, rfl⟩, ⟨hsf₄, hfin_I, hext_I, rfl⟩⟩

/-! ### Exercise 7.10 (§7.3, printed p. 70 / PDF p. 78) -/

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (Nat.Prime 11) := ⟨by decide⟩
instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- The cubic `x^3 - 5 ∈ ℤ₇[x]` (`Exercise 7.10`, printed p. 70 / PDF p. 78). -/
noncomputable def ex710Poly7 : (ZMod 7)[X] :=
  Polynomial.X ^ 3 - 5

theorem ex710Poly7_irreducible : Irreducible ex710Poly7 := by
  have hc : ex710Poly7 = Polynomial.X ^ 3 - Polynomial.C 5 := by
    unfold ex710Poly7; rw [map_ofNat]
  refine irreducible_of_monic_deg_two_or_three_of_no_roots
    (hc ▸ Polynomial.monic_X_pow_sub_C 5 (by decide))
    (Or.inr (hc ▸ Polynomial.natDegree_X_pow_sub_C)) ?_
  intro a
  unfold ex710Poly7
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
  revert a
  decide

instance : Fact (Irreducible ex710Poly7) := ⟨ex710Poly7_irreducible⟩

/-- Splitting field `𝔽₃₄₃ = ℤ₇[x] / (x^3 - 5)` for `x^3 - 5` over `ℤ₇` (`Exercise 7.10`). -/
noncomputable abbrev Ex710Field7 : Type := AdjoinRoot ex710Poly7

/-- Irreducible quadratic factor `x^2 + 3x + 9` of `x^3 - 5 = (x - 3)(x^2 + 3x + 9)` in `ℤ₁₁[x]`
(`Exercise 7.10`, printed p. 70). -/
noncomputable def ex710Quad11 : (ZMod 11)[X] :=
  Polynomial.X ^ 2 + 3 * Polynomial.X + 9

theorem ex710Quad11_irreducible : Irreducible ex710Quad11 := by
  refine irreducible_of_monic_deg_two_or_three_of_no_roots
    (by unfold ex710Quad11; monicity!)
    (Or.inl (by unfold ex710Quad11; compute_degree!)) ?_
  intro a
  unfold ex710Quad11
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_ofNat]
  revert a
  decide

instance : Fact (Irreducible ex710Quad11) := ⟨ex710Quad11_irreducible⟩

/-- Splitting field `𝔽₁₂₁ = ℤ₁₁[x] / (x^2 + 3x + 9)` for `x^3 - 5` over `ℤ₁₁` (`Exercise 7.10`). -/
noncomputable abbrev Ex710Field11 : Type := AdjoinRoot ex710Quad11

/-- **Exercise 7.10** (§7.3, printed p. 70 / PDF p. 78):
*"Find a splitting field extension for `x^3 - 5` over `ℤ₇`, `ℤ₁₁` and `ℤ₁₃`."*

All three splitting-field regimes occur:
1. Over `ℤ₇`: `x^3 - 5` is irreducible in `ℤ₇[x]`, and `Ex710Field7 = ℤ₇[x] / (x^3 - 5)` (`𝔽₃₄₃`)
   is a splitting field extension of degree `3` (since `1^3 = 2^3 = 4^3 = 1` in `ℤ₇`, the roots are
   `α, 2α, 4α`);
2. Over `ℤ₁₁`: `x^3 - 5 = (x - 3)(x^2 + 3x + 9)` with `x^2 + 3x + 9` irreducible in `ℤ₁₁[x]`, and
   `Ex710Field11 = ℤ₁₁[x] / (x^2 + 3x + 9)` (`𝔽₁₂₁`) is a splitting field extension of degree `2`
   (roots `3, β, -3 - β`);
3. Over `ℤ₁₃`: `x^3 - 5 = (x - 7)(x - 8)(x - 11)` already splits in `ℤ₁₃[x]`, so `ℤ₁₃ : ℤ₁₃` is a
   splitting field extension of degree `1`. -/
theorem exercise_7_10 :
    (Irreducible (Polynomial.X ^ 3 - 5 : (ZMod 7)[X]) ∧
      IsGarlingSplittingFieldExtension (ZMod 7) Ex710Field7 (Polynomial.X ^ 3 - 5) ∧
      Module.finrank (ZMod 7) Ex710Field7 = 3 ∧
      Nat.card Ex710Field7 = 343) ∧
    ((Polynomial.X ^ 3 - 5 : (ZMod 11)[X]) = (Polynomial.X - 3) * ex710Quad11 ∧
      Irreducible ex710Quad11 ∧
      IsGarlingSplittingFieldExtension (ZMod 11) Ex710Field11 (Polynomial.X ^ 3 - 5) ∧
      Module.finrank (ZMod 11) Ex710Field11 = 2 ∧
      Nat.card Ex710Field11 = 121) ∧
    ((Polynomial.X ^ 3 - 5 : (ZMod 13)[X]) =
        (Polynomial.X - 7) * (Polynomial.X - 8) * (Polynomial.X - 11) ∧
      IsGarlingSplittingFieldExtension (ZMod 13) (ZMod 13) (Polynomial.X ^ 3 - 5) ∧
      Module.finrank (ZMod 13) (ZMod 13) = 1 ∧
      Nat.card (ZMod 13) = 13) := by
  -- 1. Over `ℤ₇`:
  have hp7 : Irreducible (Polynomial.X ^ 3 - 5 : (ZMod 7)[X]) ∧
      IsGarlingSplittingFieldExtension (ZMod 7) Ex710Field7 (Polynomial.X ^ 3 - 5) ∧
      Module.finrank (ZMod 7) Ex710Field7 = 3 ∧
      Nat.card Ex710Field7 = 343 := by
    let pb7 := AdjoinRoot.powerBasis ex710Poly7_irreducible.ne_zero
    have hdeg7 : ex710Poly7.natDegree = 3 := by
      have hc : ex710Poly7 = Polynomial.X ^ 3 - Polynomial.C 5 := by unfold ex710Poly7; rw [map_ofNat]
      rw [hc, Polynomial.natDegree_X_pow_sub_C]
    have hfin7 : Module.finrank (ZMod 7) Ex710Field7 = 3 := by
      rw [Module.finrank_eq_card_basis pb7.basis, Fintype.card_fin, AdjoinRoot.powerBasis_dim, hdeg7]
    let eVec7 : Ex710Field7 ≃ (Fin pb7.dim → ZMod 7) := pb7.basis.equivFun.toEquiv
    have hcard7 : Nat.card Ex710Field7 = 343 := by
      rw [Nat.card_congr eVec7, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
        ZMod.card, AdjoinRoot.powerBasis_dim, hdeg7]
      norm_num
    let α : Ex710Field7 := AdjoinRoot.root ex710Poly7
    have hp7_def : ex710Poly7 = Polynomial.X ^ 3 - 5 := rfl
    have hα_pow : α ^ 3 = 5 := by
      have hr : Polynomial.aeval α ex710Poly7 = 0 :=
        (AdjoinRoot.aeval_eq ex710Poly7).trans AdjoinRoot.mk_self
      have hr' : Polynomial.aeval α (Polynomial.X ^ 3 - 5 : (ZMod 7)[X]) = 0 :=
        (congrArg (Polynomial.aeval α) hp7_def.symm).trans hr
      rw [map_sub, map_pow, Polynomial.aeval_X, map_ofNat] at hr'
      exact sub_eq_zero.mp hr'
    have hα_ne0 : α ≠ 0 := fun h0 => by
      rw [h0, zero_pow (by decide)] at hα_pow
      have h5 : algebraMap (ZMod 7) Ex710Field7 (5 : ZMod 7) = 0 := by
        simpa only [map_ofNat] using hα_pow.symm
      have h50 : (5 : ZMod 7) = 0 :=
        (algebraMap (ZMod 7) Ex710Field7).injective (h5.trans (map_zero _).symm)
      exact absurd h50 (by decide)
    have h2_cube : (2 : Ex710Field7) ^ 3 = 1 := by
      have hm := congrArg (algebraMap (ZMod 7) Ex710Field7) (show (2 : ZMod 7) ^ 3 = 1 by decide)
      simpa only [map_pow, map_ofNat, map_one] using hm
    have h4_cube : (4 : Ex710Field7) ^ 3 = 1 := by
      have hm := congrArg (algebraMap (ZMod 7) Ex710Field7) (show (4 : ZMod 7) ^ 3 = 1 by decide)
      simpa only [map_pow, map_ofNat, map_one] using hm
    let r7 : Fin 3 → Ex710Field7 := ![α, 2 * α, 4 * α]
    have hexp7 : GarlingSplitsExplicit (ZMod 7) Ex710Field7 (Polynomial.X ^ 3 - 5) 3 1 r7 := by
      unfold GarlingSplitsExplicit
      have hmap : (Polynomial.X ^ 3 - 5 : (ZMod 7)[X]).map (algebraMap (ZMod 7) Ex710Field7) =
          Polynomial.X ^ 3 - Polynomial.C 5 := by simp [map_ofNat]
      rw [hmap]
      simp only [map_one, one_mul]
      refine monic_eq_prod_X_sub_C_of_roots
        (Polynomial.monic_X_pow_sub_C 5 (by decide))
        Polynomial.natDegree_X_pow_sub_C ?_ ?_
      · have hne12 : (1 : Ex710Field7) ≠ 2 := fun h => by
          have hm : algebraMap (ZMod 7) Ex710Field7 1 = algebraMap (ZMod 7) Ex710Field7 2 := by
            simpa only [map_one, map_ofNat] using h
          exact absurd ((algebraMap (ZMod 7) Ex710Field7).injective hm) (by decide)
        have hne14 : (1 : Ex710Field7) ≠ 4 := fun h => by
          have hm : algebraMap (ZMod 7) Ex710Field7 1 = algebraMap (ZMod 7) Ex710Field7 4 := by
            simpa only [map_one, map_ofNat] using h
          exact absurd ((algebraMap (ZMod 7) Ex710Field7).injective hm) (by decide)
        have hne24 : (2 : Ex710Field7) ≠ 4 := fun h => by
          have hm : algebraMap (ZMod 7) Ex710Field7 2 = algebraMap (ZMod 7) Ex710Field7 4 := by
            simpa only [map_ofNat] using h
          exact absurd ((algebraMap (ZMod 7) Ex710Field7).injective hm) (by decide)
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp [r7] at hij ⊢
        · exact absurd (mul_right_cancel₀ hα_ne0 (by simpa using hij)) hne12
        · exact absurd (mul_right_cancel₀ hα_ne0 (by simpa using hij)) hne14
        · exact absurd (mul_right_cancel₀ hα_ne0 (by simpa using hij.symm)) hne12
        · rcases hij with h24 | h0
          · exact absurd h24 hne24
          · exact absurd h0 hα_ne0
        · exact absurd (mul_right_cancel₀ hα_ne0 (by simpa using hij.symm)) hne14
        · rcases hij with h42 | h0
          · exact absurd h42.symm hne24
          · exact absurd h0 hα_ne0
      · rintro ⟨_ | _ | _ | m, hm⟩
        · change Polynomial.eval α (Polynomial.X ^ 3 - Polynomial.C 5) = 0
          simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_C, hα_pow, sub_self]
        · change Polynomial.eval (2 * α) (Polynomial.X ^ 3 - Polynomial.C 5) = 0
          simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
          rw [mul_pow, h2_cube, one_mul, hα_pow, sub_self]
        · change Polynomial.eval (4 * α) (Polynomial.X ^ 3 - Polynomial.C 5) = 0
          simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
          rw [mul_pow, h4_cube, one_mul, hα_pow, sub_self]
        · omega
    have hadj7 : IntermediateField.adjoin (ZMod 7) ({α} : Set Ex710Field7) = ⊤ := by
      ext x
      simp only [IntermediateField.mem_top, iff_true]
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
      rw [← AdjoinRoot.aeval_eq]
      exact aeval_mem_intermediateField_adjoin_singleton α p
    have hsf7 : IsGarlingSplittingFieldExtension (ZMod 7) Ex710Field7 (Polynomial.X ^ 3 - 5) := by
      refine isGarlingSplittingFieldExtension_of_adjoin_range_eq_top
        ex710Poly7_irreducible.ne_zero hexp7
        (top_unique (hadj7 ▸ IntermediateField.adjoin_le_iff.mpr ?_))
      rw [Set.singleton_subset_iff]
      exact IntermediateField.subset_adjoin (ZMod 7) (Set.range r7) ⟨0, rfl⟩
    exact ⟨ex710Poly7_irreducible, hsf7, hfin7, hcard7⟩
  -- 2. Over `ℤ₁₁`:
  have hp11 : (Polynomial.X ^ 3 - 5 : (ZMod 11)[X]) = (Polynomial.X - 3) * ex710Quad11 ∧
      Irreducible ex710Quad11 ∧
      IsGarlingSplittingFieldExtension (ZMod 11) Ex710Field11 (Polynomial.X ^ 3 - 5) ∧
      Module.finrank (ZMod 11) Ex710Field11 = 2 ∧
      Nat.card Ex710Field11 = 121 := by
    have hq11_def : ex710Quad11 = Polynomial.X ^ 2 + 3 * Polynomial.X + 9 := rfl
    have hfac11 : (Polynomial.X ^ 3 - 5 : (ZMod 11)[X]) = (Polynomial.X - 3) * ex710Quad11 := by
      rw [hq11_def]
      symm
      calc (Polynomial.X - 3) * (Polynomial.X ^ 2 + 3 * Polynomial.X + 9 : (ZMod 11)[X])
          = Polynomial.X ^ 3 - 27 := by ring
        _ = Polynomial.X ^ 3 - Polynomial.C (27 : ZMod 11) := by rw [map_ofNat]
        _ = Polynomial.X ^ 3 - Polynomial.C (5 : ZMod 11) := by
              rw [show (27 : ZMod 11) = 5 by decide]
        _ = Polynomial.X ^ 3 - 5 := by rw [map_ofNat]
    let pb11 := AdjoinRoot.powerBasis ex710Quad11_irreducible.ne_zero
    have hdeg11 : ex710Quad11.natDegree = 2 := by rw [hq11_def]; compute_degree!
    have hfin11 : Module.finrank (ZMod 11) Ex710Field11 = 2 := by
      rw [Module.finrank_eq_card_basis pb11.basis, Fintype.card_fin, AdjoinRoot.powerBasis_dim,
        hdeg11]
    let eVec11 : Ex710Field11 ≃ (Fin pb11.dim → ZMod 11) := pb11.basis.equivFun.toEquiv
    have hcard11 : Nat.card Ex710Field11 = 121 := by
      rw [Nat.card_congr eVec11, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
        ZMod.card, AdjoinRoot.powerBasis_dim, hdeg11]
      norm_num
    let β : Ex710Field11 := AdjoinRoot.root ex710Quad11
    have hβ_rel : β ^ 2 + 3 * β + 9 = 0 := by
      have hr : Polynomial.aeval β ex710Quad11 = 0 :=
        (AdjoinRoot.aeval_eq ex710Quad11).trans AdjoinRoot.mk_self
      have hr' : Polynomial.aeval β (Polynomial.X ^ 2 + 3 * Polynomial.X + 9 : (ZMod 11)[X]) = 0 :=
        (congrArg (Polynomial.aeval β) hq11_def.symm).trans hr
      simpa only [map_add, map_mul, map_pow, map_ofNat, Polynomial.aeval_X] using hr'
    let r11 : Fin 3 → Ex710Field11 := ![3, β, -3 - β]
    have hexp11 : GarlingSplitsExplicit (ZMod 11) Ex710Field11 (Polynomial.X ^ 3 - 5) 3 1 r11 := by
      unfold GarlingSplitsExplicit
      have hfac11' : (Polynomial.X ^ 3 - 5 : (ZMod 11)[X]) =
          (Polynomial.X - 3) * (Polynomial.X ^ 2 + 3 * Polynomial.X + 9) := by
        rw [hfac11, hq11_def]
      have hmap : (Polynomial.X ^ 3 - 5 : (ZMod 11)[X]).map (algebraMap (ZMod 11) Ex710Field11) =
          (Polynomial.X - 3) * (Polynomial.X ^ 2 + 3 * Polynomial.X + 9) := by
        refine (congrArg (Polynomial.map (algebraMap (ZMod 11) Ex710Field11)) hfac11').trans ?_
        simp
      rw [hmap]
      simp only [map_one, one_mul, r11, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one, map_ofNat]
      have hq : (Polynomial.X - Polynomial.C β) * (Polynomial.X - Polynomial.C (-3 - β)) =
          (Polynomial.X ^ 2 + 3 * Polynomial.X + 9 : Ex710Field11[X]) := by
        have hsum : β + (-3 - β) = -3 := by ring
        have hprod : β * (-3 - β) = 9 := by linear_combination -hβ_rel
        calc (Polynomial.X - Polynomial.C β) * (Polynomial.X - Polynomial.C (-3 - β))
            = Polynomial.X ^ 2 - Polynomial.C (β + (-3 - β)) * Polynomial.X +
                Polynomial.C (β * (-3 - β)) := by simp only [map_add, map_mul]; ring
          _ = Polynomial.X ^ 2 + 3 * Polynomial.X + 9 := by
                rw [hsum, hprod, map_neg, map_ofNat, map_ofNat]; ring
      rw [← hq]
    have hadj11 : IntermediateField.adjoin (ZMod 11) ({β} : Set Ex710Field11) = ⊤ := by
      ext x
      simp only [IntermediateField.mem_top, iff_true]
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
      rw [← AdjoinRoot.aeval_eq]
      exact aeval_mem_intermediateField_adjoin_singleton β p
    have hf11_ne0 : (Polynomial.X ^ 3 - 5 : (ZMod 11)[X]) ≠ 0 := by
      rw [← map_ofNat Polynomial.C 5]
      exact (Polynomial.monic_X_pow_sub_C 5 (by decide)).ne_zero
    have hsf11 : IsGarlingSplittingFieldExtension (ZMod 11) Ex710Field11 (Polynomial.X ^ 3 - 5) := by
      refine isGarlingSplittingFieldExtension_of_adjoin_range_eq_top hf11_ne0 hexp11
        (top_unique (hadj11 ▸ IntermediateField.adjoin_le_iff.mpr ?_))
      rw [Set.singleton_subset_iff]
      exact IntermediateField.subset_adjoin (ZMod 11) (Set.range r11) ⟨1, rfl⟩
    exact ⟨hfac11, ex710Quad11_irreducible, hsf11, hfin11, hcard11⟩
  -- 3. Over `ℤ₁₃`:
  have hp13 : (Polynomial.X ^ 3 - 5 : (ZMod 13)[X]) =
        (Polynomial.X - 7) * (Polynomial.X - 8) * (Polynomial.X - 11) ∧
      IsGarlingSplittingFieldExtension (ZMod 13) (ZMod 13) (Polynomial.X ^ 3 - 5) ∧
      Module.finrank (ZMod 13) (ZMod 13) = 1 ∧
      Nat.card (ZMod 13) = 13 := by
    have hfac13 : (Polynomial.X ^ 3 - 5 : (ZMod 13)[X]) =
        (Polynomial.X - 7) * (Polynomial.X - 8) * (Polynomial.X - 11) := by
      symm
      calc (Polynomial.X - 7) * (Polynomial.X - 8) * (Polynomial.X - 11 : (ZMod 13)[X])
          = Polynomial.X ^ 3 - 26 * Polynomial.X ^ 2 + 221 * Polynomial.X - 616 := by ring
        _ = Polynomial.X ^ 3 - Polynomial.C (26 : ZMod 13) * Polynomial.X ^ 2 +
              Polynomial.C (221 : ZMod 13) * Polynomial.X - Polynomial.C (616 : ZMod 13) := by
              simp only [map_ofNat]
        _ = Polynomial.X ^ 3 - Polynomial.C (0 : ZMod 13) * Polynomial.X ^ 2 +
              Polynomial.C (0 : ZMod 13) * Polynomial.X - Polynomial.C (5 : ZMod 13) := by
              rw [show (26 : ZMod 13) = 0 by decide,
                  show (221 : ZMod 13) = 0 by decide,
                  show (616 : ZMod 13) = 5 by decide]
        _ = Polynomial.X ^ 3 - 5 := by simp only [map_zero, map_ofNat]; ring
    have hexp13 : GarlingSplitsExplicit (ZMod 13) (ZMod 13) (Polynomial.X ^ 3 - 5) 3 1
        ![7, 8, 11] := by
      unfold GarlingSplitsExplicit
      have hmap : (Polynomial.X ^ 3 - 5 : (ZMod 13)[X]).map (algebraMap (ZMod 13) (ZMod 13)) =
          Polynomial.X ^ 3 - 5 := by simp
      rw [hmap, hfac13]
      simp only [map_one, one_mul, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, mul_one, map_ofNat]
      ring
    have hsf13 : IsGarlingSplittingFieldExtension (ZMod 13) (ZMod 13) (Polynomial.X ^ 3 - 5) :=
      (isGarlingSplittingFieldExtension_self_iff (ZMod 13) _).mpr ⟨3, 1, ![7, 8, 11], hexp13⟩
    have hcard13 : Nat.card (ZMod 13) = 13 := by
      rw [Nat.card_eq_fintype_card, ZMod.card]
    exact ⟨hfac13, hsf13, Module.finrank_self (ZMod 13), hcard13⟩
  exact ⟨hp7, hp11, hp13⟩

end Garling.Chapter07
