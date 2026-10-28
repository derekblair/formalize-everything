import Mathlib

/-!
# Chapter 2: Positive Borel Measures

The topology results below follow the numbered statements of the 1987
third edition. Coverage and the remaining measure-theoretic nodes are
recorded in `INVENTORY-CH02.md`. A real cutoff is explicitly embedded into
the book's complex-valued `C_c(X)`; compact support means the closure of
the nonzero locus. No normality, metrizability or σ-finiteness assumption
is added to the locally compact Hausdorff hypotheses.
-/

noncomputable section

open Set
open scoped Topology CompactlySupported

namespace RudinRCA.Chapter02

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- 2.4: a closed subset of a compact set is compact. -/
theorem theorem_2_4 {K F : Set X} (hK : IsCompact K) (hF : IsClosed F)
    (hFK : F ⊆ K) : IsCompact F :=
  hK.of_isClosed_subset hF hFK

/-- The unnumbered corollary following 2.4. -/
theorem theorem_2_4_corollary {A B : Set X} (hAB : A ⊆ B)
    (hB : IsCompact (closure B)) : IsCompact (closure A) :=
  hB.of_isClosed_subset isClosed_closure (closure_mono hAB)

/-- 2.5: a point outside a compact set has a disjoint open neighborhood. -/
theorem theorem_2_5 [T2Space X] {K : Set X} {p : X}
    (hK : IsCompact K) (hp : p ∉ K) :
    ∃ U W : Set X, IsOpen U ∧ IsOpen W ∧ p ∈ U ∧ K ⊆ W ∧ U ∩ W = ∅ := by
  obtain ⟨W, U, hW, hU, hKW, hpU, hdisj⟩ := hK.separation_of_notMem hp
  exact ⟨U, W, hU, hW, hpU, hKW, hdisj.symm.inter_eq⟩

/-- Corollary (a) following 2.5. -/
theorem theorem_2_5_corollary_a [T2Space X] {K : Set X}
    (hK : IsCompact K) : IsClosed K := hK.isClosed

/-- Corollary (b) following 2.5. -/
theorem theorem_2_5_corollary_b [T2Space X] {K F : Set X}
    (hF : IsClosed F) (hK : IsCompact K) : IsCompact (F ∩ K) :=
  hK.inter_left hF

/-- 2.6: an empty intersection of compact sets already has a finite
empty subintersection. The empty index type is included. -/
theorem theorem_2_6 [T2Space X] {ι : Type*} (K : ι → Set X)
    (hK : ∀ i, IsCompact (K i)) (hempty : (⋂ i, K i) = ∅) :
    ∃ s : Finset ι, (⋂ i ∈ s, K i) = ∅ := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    let := hι
    refine ⟨∅, ?_⟩
    simpa using hempty
  | inr hι =>
    let := hι
    let i₀ : ι := Classical.choice hι
    have hdisj : Disjoint (K i₀) (⋂ i, K i) := by rw [hempty]; exact disjoint_empty _
    obtain ⟨s, hs⟩ := (hK i₀).elim_finite_subfamily_closed K
      (fun i => (hK i).isClosed) hdisj
    refine ⟨insert i₀ s, ?_⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact Set.disjoint_left.mp hs (Set.mem_iInter₂.mp hx i₀ (Finset.mem_insert_self _ _))
      (Set.mem_iInter₂.mpr fun i hi => Set.mem_iInter₂.mp hx i (Finset.mem_insert_of_mem hi))

/-- 2.7: interpolate an open set with compact closure. -/
theorem theorem_2_7 [T2Space X] [LocallyCompactSpace X] {K U : Set X}
    (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K) :
    ∃ V : Set X, IsOpen V ∧ IsCompact (closure V) ∧
      K ⊆ V ∧ V ⊆ closure V ∧ closure V ⊆ U := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  exact ⟨V, hV, hVc, hKV, subset_closure, hVU⟩

/-- 2.10: continuous images of compact sets are compact. -/
theorem theorem_2_10 {f : X → Y} (hf : Continuous f) {K : Set X}
    (hK : IsCompact K) : IsCompact (f '' K) := hK.image hf

/-- The complex-valued compact-range corollary following 2.10. -/
theorem theorem_2_10_corollary (f : C_c(X, ℂ)) : IsCompact (range f) :=
  f.hasCompactSupport.isCompact_range f.continuous

/-- The common `[0,1]` range condition in the two notations of 2.11.
The existential expresses the real interval inside the complex field. -/
def IsCutoff (f : C_c(X, ℂ)) : Prop :=
  ∀ x, ∃ r : ℝ, r ∈ Icc 0 1 ∧ f x = (r : ℂ)

/-- The relation `K ≺ f` from 2.11, including compactness of `K`. -/
def CompactCutoff (K : Set X) (f : C_c(X, ℂ)) : Prop :=
  IsCompact K ∧ IsCutoff f ∧ EqOn f 1 K

/-- The relation `f ≺ V` from 2.11, including openness of `V`. -/
def OpenCutoff (f : C_c(X, ℂ)) (V : Set X) : Prop :=
  IsOpen V ∧ IsCutoff f ∧ tsupport f ⊆ V

/-- A real compactly supported continuous function viewed as complex-valued. -/
def ofRealCutoff (f : C(X, ℝ)) (hf : HasCompactSupport f) : C_c(X, ℂ) where
  toFun x := (f x : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous
  hasCompactSupport' := hf.comp_left (g := Complex.ofReal) (by simp)

/-- 2.12 (Urysohn): the cutoff lies in the book's complex-valued `C_c(X)`. -/
theorem lemma_2_12 [T2Space X] [LocallyCompactSpace X] {K V : Set X}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ f : C_c(X, ℂ), CompactCutoff K f ∧ OpenCutoff f V := by
  obtain ⟨g, hgK, hgcomp, hgV, hgrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
  let f := ofRealCutoff g hgcomp
  have hfrange : IsCutoff f := fun x => ⟨g x, hgrange x, rfl⟩
  refine ⟨f, ⟨hK, hfrange, ?_⟩, ⟨hV, hfrange, ?_⟩⟩
  · intro x hx
    change (g x : ℂ) = 1
    simp only [hgK hx, Pi.one_apply, Complex.ofReal_one]
  · exact (tsupport_comp_subset (g := Complex.ofReal) (by simp) g).trans hgV

/-- 2.13: a finite open cover of a compact set has a subordinate partition
of unity, with complex-valued compactly supported continuous functions. -/
theorem theorem_2_13 [T2Space X] [LocallyCompactSpace X] {n : ℕ}
    (V : Fin n → Set X) {K : Set X} (hV : ∀ i, IsOpen (V i))
    (hK : IsCompact K) (hcover : K ⊆ ⋃ i, V i) :
    ∃ f : Fin n → C_c(X, ℂ),
      (∀ i, OpenCutoff (f i) (V i)) ∧ ∀ x ∈ K, ∑ i, f i x = 1 := by
  obtain ⟨g, hgV, hgsum, hgrange, hgcomp⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact hV hK hcover
  refine ⟨fun i => ofRealCutoff (g i) (hgcomp i), ?_, ?_⟩
  · intro i
    refine ⟨hV i, (fun x => ⟨g i x, hgrange i x, rfl⟩), ?_⟩
    exact (tsupport_comp_subset (g := Complex.ofReal) (by simp) (g i)).trans (hgV i)
  · intro x hx
    have heq : ∑ i, g i x = 1 := by simpa using hgsum hx
    change ∑ i, (g i x : ℂ) = 1
    rw [← Complex.ofReal_sum, heq, Complex.ofReal_one]

end RudinRCA.Chapter02
