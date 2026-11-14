import Mathlib
import RudinRCA.Chapter01

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

open Set MeasureTheory
open scoped Topology CompactlySupported ENNReal

namespace RudinRCA.Chapter02

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The complex vector spaces of 2.1 use the additive group and module
structures; a linear functional has the scalar field as its target. -/
abbrev ComplexVectorSpace (V : Type*) [AddCommGroup V] := Module ℂ V

abbrev LinearFunctional (V : Type*) [AddCommGroup V] [Module ℂ V] := V →ₗ[ℂ] ℂ

/-- All the algebraic laws in 2.1, including uniqueness of zero and inverses.
The field parameter also covers the explicitly mentioned real case. -/
theorem definition_2_1_vectorSpace {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V]
    [Module 𝕜 V] :
    (∀ x y : V, x + y = y + x) ∧
    (∀ x y z : V, x + (y + z) = (x + y) + z) ∧
    (∃! o : V, ∀ x, x + o = x) ∧
    (∀ x : V, ∃! y, x + y = 0) ∧
    (∀ x : V, (1 : 𝕜) • x = x) ∧
    (∀ (a b : 𝕜) (x : V), a • (b • x) = (a * b) • x) ∧
    (∀ (a : 𝕜) (x y : V), a • (x + y) = a • x + a • y) ∧
    (∀ (a b : 𝕜) (x : V), (a + b) • x = a • x + b • x) := by
  refine ⟨add_comm, fun _ _ _ => (add_assoc _ _ _).symm, ?_, ?_,
    one_smul 𝕜, fun _ _ _ => (mul_smul _ _ _).symm, smul_add, add_smul⟩
  · exact ⟨0, add_zero, fun o ho => by simpa using ho 0⟩
  · intro x
    exact ⟨-x, add_neg_cancel x, fun y hy => eq_neg_of_add_eq_zero_right hy⟩

/-- 2.1's single two-vector identity is equivalent to a bundled linear map. -/
theorem definition_2_1_linear {𝕜 V W : Type*} [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W] (A : V → W) :
    (∀ (a b : 𝕜) (x y : V), A (a • x + b • y) = a • A x + b • A y) ↔
      ∃ L : V →ₗ[𝕜] W, (L : V → W) = A := by
  constructor
  · intro h
    refine ⟨{ toFun := A, map_add' := ?_, map_smul' := ?_ }, rfl⟩
    · intro x y
      simpa using h 1 1 x y
    · intro a x
      simpa using h a 0 x 0
  · rintro ⟨L, rfl⟩ a b x y
    simp only [map_add, map_smul]

/-- Rudin's neighborhood convention in 2.3(d) requires the set itself to be open. -/
def BookNeighborhood (p : X) (U : Set X) : Prop := IsOpen U ∧ p ∈ U

/-- The 2.3(f) definition, stated without silently adding a separation axiom. -/
def BookLocallyCompact (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ p : X, ∃ U : Set X, BookNeighborhood p U ∧ IsCompact (closure U)

/-- 2.3(a): closedness and the closure properties stated with the definition. -/
theorem definition_2_3_closed (E : Set X) : IsClosed E ↔ IsOpen Eᶜ :=
  isOpen_compl_iff.symm

theorem proposition_2_3_closed :
    IsClosed (∅ : Set X) ∧ IsClosed (univ : Set X) ∧
    (∀ E F : Set X, IsClosed E → IsClosed F → IsClosed (E ∪ F)) ∧
    (∀ S : Set (Set X), (∀ E ∈ S, IsClosed E) → IsClosed (⋂₀ S)) :=
  ⟨isClosed_empty, isClosed_univ, fun _ _ hE hF => hE.union hF,
    fun _ hS => isClosed_sInter hS⟩

theorem proposition_2_3_closed_finite_union {ι : Type*} (s : Finset ι)
    (E : ι → Set X) (hE : ∀ i ∈ s, IsClosed (E i)) :
    IsClosed (⋃ i ∈ s, E i) := isClosed_biUnion_finset hE

/-- 2.3(b): the closure is the least closed superset. -/
theorem definition_2_3_closure (E : Set X) :
    IsClosed (closure E) ∧ E ⊆ closure E ∧
      ∀ F : Set X, IsClosed F → E ⊆ F → closure E ⊆ F :=
  ⟨isClosed_closure, subset_closure, fun _ hF hEF => closure_minimal hEF hF⟩

/-- 2.3(c): compactness is precisely the finite-open-subcover property. -/
theorem definition_2_3_compact (K : Set X) :
    IsCompact K ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → K ⊆ ⋃ i, U i →
        ∃ s : Finset ι, K ⊆ ⋃ i ∈ s, U i :=
  isCompact_iff_finite_subcover

theorem definition_2_3_compactSpace : CompactSpace X ↔ IsCompact (univ : Set X) :=
  ⟨fun _ => isCompact_univ, fun h => ⟨h⟩⟩

/-- Relation between the open-neighborhood convention and Mathlib's filter. -/
theorem definition_2_3_neighborhood (p : X) (U : Set X) :
    BookNeighborhood p U ↔ IsOpen U ∧ U ∈ 𝓝 p := by
  constructor
  · rintro ⟨hU, hp⟩
    exact ⟨hU, hU.mem_nhds hp⟩
  · rintro ⟨hU, hp⟩
    exact ⟨hU, mem_of_mem_nhds hp⟩

/-- 2.3(e): Hausdorff separation, using the book's neighborhoods. -/
theorem definition_2_3_hausdorff :
    T2Space X ↔ ∀ p q : X, p ≠ q → ∃ U V : Set X,
      BookNeighborhood p U ∧ BookNeighborhood q V ∧ U ∩ V = ∅ := by
  constructor
  · intro h p q hpq
    let := h
    obtain ⟨U, V, hU, hV, hp, hq, hUV⟩ := t2_separation hpq
    exact ⟨U, V, ⟨hU, hp⟩, ⟨hV, hq⟩, hUV.inter_eq⟩
  · intro h
    refine ⟨fun p q hpq => ?_⟩
    obtain ⟨U, V, ⟨hU, hp⟩, ⟨hV, hq⟩, hUV⟩ := h p q hpq
    exact ⟨U, V, hU, hV, hp, hq, Set.disjoint_iff_inter_eq_empty.mpr hUV⟩

/-- The book and Mathlib local-compactness conventions agree on Hausdorff spaces. -/
theorem definition_2_3_locallyCompact [T2Space X] :
    BookLocallyCompact X ↔ LocallyCompactSpace X := by
  constructor
  · intro h
    let : WeaklyLocallyCompactSpace X := ⟨fun p => by
      obtain ⟨U, ⟨hU, hp⟩, hc⟩ := h p
      exact ⟨closure U, hc, Filter.mem_of_superset (hU.mem_nhds hp) subset_closure⟩⟩
    infer_instance
  · intro h p
    let := h
    obtain ⟨U, hU, hp, hc⟩ := exists_isOpen_mem_isCompact_closure p
    exact ⟨U, ⟨hU, hp⟩, hc⟩

/-- The final assertion of 2.3: compact spaces satisfy the book's definition. -/
theorem proposition_2_3_compact_locallyCompact [CompactSpace X] : BookLocallyCompact X := by
  intro p
  exact ⟨univ, ⟨isOpen_univ, mem_univ p⟩, by simpa using (isCompact_univ : IsCompact (univ : Set X))⟩

/-- The Heine–Borel reminder following 2.3. -/
theorem proposition_2_3_heineBorel {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact E ↔ IsClosed E ∧ Bornology.IsBounded E :=
  Metric.isCompact_iff_isClosed_bounded

theorem proposition_2_3_euclidean (n : ℕ) :
    BookLocallyCompact (EuclideanSpace ℝ (Fin n)) ∧
      T2Space (EuclideanSpace ℝ (Fin n)) :=
  ⟨definition_2_3_locallyCompact.mpr inferInstance, inferInstance⟩

theorem proposition_2_3_metric_hausdorff (Z : Type*) [MetricSpace Z] : T2Space Z :=
  inferInstance

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

/-- 2.8 uses real thresholds even when the function can take infinite values. -/
def BookLowerSemicontinuous (f : X → EReal) : Prop :=
  ∀ a : ℝ, IsOpen {x | (a : EReal) < f x}

def BookUpperSemicontinuous (f : X → EReal) : Prop :=
  ∀ a : ℝ, IsOpen {x | f x < (a : EReal)}

/-- The real-threshold definition agrees with Mathlib also at both endpoints. -/
theorem definition_2_8_lower (f : X → EReal) :
    BookLowerSemicontinuous f ↔ LowerSemicontinuous f := by
  constructor
  · intro hf
    rw [lowerSemicontinuous_iff_isOpen_preimage]
    intro a
    have heq : f ⁻¹' Ioi a = ⋃ r : {r : ℝ // a < (r : EReal)},
        {x | ((r : ℝ) : EReal) < f x} := by
      ext x
      constructor
      · intro hx
        obtain ⟨r, har, hrx⟩ := EReal.exists_between_coe_real hx
        exact mem_iUnion.mpr ⟨⟨r, har⟩, hrx⟩
      · intro hx
        obtain ⟨r, hrx⟩ := mem_iUnion.mp hx
        exact r.property.trans hrx
    rw [heq]
    exact isOpen_iUnion (fun r => hf r)
  · intro hf a
    exact hf.isOpen_preimage a

theorem definition_2_8_upper (f : X → EReal) :
    BookUpperSemicontinuous f ↔ UpperSemicontinuous f := by
  constructor
  · intro hf
    rw [upperSemicontinuous_iff_isOpen_preimage]
    intro a
    have heq : f ⁻¹' Iio a = ⋃ r : {r : ℝ // (r : EReal) < a},
        {x | f x < ((r : ℝ) : EReal)} := by
      ext x
      constructor
      · intro hx
        obtain ⟨r, hxr, hra⟩ := EReal.exists_between_coe_real hx
        exact mem_iUnion.mpr ⟨⟨r, hra⟩, hxr⟩
      · intro hx
        obtain ⟨r, hxr⟩ := mem_iUnion.mp hx
        exact hxr.trans r.property
    rw [heq]
    exact isOpen_iUnion (fun r => hf r)
  · intro hf a
    exact hf.isOpen_preimage a

/-- The real-valued definitions in 2.8. -/
theorem definition_2_8_real_lower (f : X → ℝ) :
    LowerSemicontinuous f ↔ ∀ a : ℝ, IsOpen {x | a < f x} :=
  lowerSemicontinuous_iff_isOpen_preimage

theorem definition_2_8_real_upper (f : X → ℝ) :
    UpperSemicontinuous f ↔ ∀ a : ℝ, IsOpen {x | f x < a} :=
  upperSemicontinuous_iff_isOpen_preimage

/-- The continuity characterization following 2.8. -/
theorem proposition_2_8_continuous (f : X → ℝ) :
    Continuous f ↔ LowerSemicontinuous f ∧ UpperSemicontinuous f :=
  continuous_iff_lower_upperSemicontinuous

/-- 2.8(a,b): characteristic functions of open and closed sets. -/
theorem proposition_2_8a {U : Set X} (hU : IsOpen U) :
    BookLowerSemicontinuous (U.indicator (fun _ => (1 : EReal))) :=
  (definition_2_8_lower _).mpr (hU.lowerSemicontinuous_indicator zero_le_one)

theorem proposition_2_8b {F : Set X} (hF : IsClosed F) :
    BookUpperSemicontinuous (F.indicator (fun _ => (1 : EReal))) :=
  (definition_2_8_upper _).mpr (hF.upperSemicontinuous_indicator zero_le_one)

theorem proposition_2_8a_real {U : Set X} (hU : IsOpen U) :
    LowerSemicontinuous (U.indicator (fun _ => (1 : ℝ))) :=
  hU.lowerSemicontinuous_indicator zero_le_one

theorem proposition_2_8b_real {F : Set X} (hF : IsClosed F) :
    UpperSemicontinuous (F.indicator (fun _ => (1 : ℝ))) :=
  hF.upperSemicontinuous_indicator zero_le_one

/-- 2.8(c): arbitrary families, including empty or unbounded families.
Extended reals keep every pointwise supremum and infimum defined. -/
theorem proposition_2_8c_sup {ι : Type*} (f : ι → X → EReal)
    (hf : ∀ i, BookLowerSemicontinuous (f i)) :
    BookLowerSemicontinuous (fun x => ⨆ i, f i x) :=
  (definition_2_8_lower _).mpr
    (lowerSemicontinuous_iSup (fun i => (definition_2_8_lower _).mp (hf i)))

theorem proposition_2_8c_inf {ι : Type*} (f : ι → X → EReal)
    (hf : ∀ i, BookUpperSemicontinuous (f i)) :
    BookUpperSemicontinuous (fun x => ⨅ i, f i x) :=
  (definition_2_8_upper _).mpr
    (upperSemicontinuous_iInf (fun i => (definition_2_8_upper _).mp (hf i)))

/-- 2.9: support includes the closure of the nonzero locus. -/
def BookSupport (f : X → ℂ) : Set X := closure {x | f x ≠ 0}

def BookCc (f : X → ℂ) : Prop := Continuous f ∧ IsCompact (BookSupport f)

theorem definition_2_9_support (f : X → ℂ) : BookSupport f = tsupport f := rfl

/-- The book's unbundled definition and Mathlib's bundled continuous maps. -/
theorem definition_2_9_cc (f : X → ℂ) :
    BookCc f ↔ ∃ g : C_c(X, ℂ), (g : X → ℂ) = f := by
  constructor
  · rintro ⟨hc, hs⟩
    exact ⟨⟨⟨f, hc⟩, hs⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g.continuous, g.hasCompactSupport⟩

/-- 2.9(a): the support of a sum lies in the union of the two supports. -/
theorem proposition_2_9_support_add (f g : X → ℂ) :
    BookSupport (f + g) ⊆ BookSupport f ∪ BookSupport g :=
  tsupport_add f g

theorem proposition_2_9_support_smul (a : ℂ) (f : X → ℂ) :
    BookSupport (a • f) ⊆ BookSupport f :=
  tsupport_smul_subset_right (fun _ => a) f

/-- The vector-space assertion of 2.9, with its pointwise operations. -/
def compactlySupportedSubmodule : Submodule ℂ (X → ℂ) where
  carrier := {f | BookCc f}
  zero_mem' := ⟨continuous_const, by
    change HasCompactSupport (0 : X → ℂ)
    exact HasCompactSupport.zero⟩
  add_mem' := by
    rintro f g ⟨hf, hfs⟩ ⟨hg, hgs⟩
    exact ⟨hf.add hg, (hfs.union hgs).of_isClosed_subset isClosed_closure
      (proposition_2_9_support_add f g)⟩
  smul_mem' := by
    rintro a f ⟨hf, hfs⟩
    exact ⟨continuous_const.smul hf, hfs.of_isClosed_subset isClosed_closure
      (proposition_2_9_support_smul a f)⟩

/-- 2.9(b) and its parenthetical continuity assertions. -/
theorem proposition_2_9_continuous {f g : X → ℂ} (hf : Continuous f)
    (hg : Continuous g) (a : ℂ) :
    Continuous (f + g) ∧ Continuous (a • f) ∧ Continuous (f * g) :=
  ⟨hf.add hg, continuous_const.smul hf, hf.mul hg⟩

theorem proposition_2_9_compact_union {ι : Type*} (s : Finset ι)
    (K : ι → Set X) (hK : ∀ i ∈ s, IsCompact (K i)) :
    IsCompact (⋃ i ∈ s, K i) := s.finite_toSet.isCompact_biUnion hK

/-- The continuous counterpart of 1.8 recalled in the paragraph after 2.9. -/
theorem proposition_2_9_continuous_pair {f g : X → ℝ} (hf : Continuous f)
    (hg : Continuous g) {Φ : ℝ × ℝ → Y} (hΦ : Continuous Φ) :
    Continuous (fun x => Φ (f x, g x)) := hΦ.comp (hf.prodMk hg)

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

/-- 2.15: a positive Borel measure has precisely the Borel sigma algebra
as its domain. The chapter considers these on locally compact Hausdorff spaces. -/
abbrev BookPositiveBorelMeasure (X : Type*) [TopologicalSpace X] :=
  @Measure X (borel X)

/-- The complex-measure version of the Borel-measure terminology in 2.15. -/
abbrev BookComplexBorelMeasure (X : Type*) [TopologicalSpace X] :=
  @ComplexMeasure X (borel X)

section SetRegularity

variable [MeasurableSpace X]

/-- Outer regularity of a specified set, with the open-superset formula
of 2.14(c) used by 2.15. -/
def BookOuterRegularSet (μ : Measure X) (E : Set X) : Prop :=
  μ E = ⨅ (V : Set X) (_ : E ⊆ V) (_ : IsOpen V), μ V

/-- Inner regularity of a specified set, with the compact-subset formula
of 2.14(d) used by 2.15 and 2.16. -/
def BookInnerRegularSet (μ : Measure X) (E : Set X) : Prop :=
  μ E = ⨆ (K : Set X) (_ : K ⊆ E) (_ : IsCompact K), μ K

end SetRegularity

/-- Rudin 2.15 requires both forms of regularity on every Borel set.
This is deliberately not an abbreviation of Mathlib's `Measure.Regular`,
whose compact inner-regularity condition only concerns open sets. -/
def BookRegularBorelMeasure (μ : BookPositiveBorelMeasure X) : Prop :=
  ∀ E : Set X, @MeasurableSet X (borel X) E →
    @BookOuterRegularSet X _ (borel X) μ E ∧ @BookInnerRegularSet X _ (borel X) μ E

/-- Expansion of the book's regularity condition with all quantifiers visible. -/
theorem definition_2_15_regular (μ : BookPositiveBorelMeasure X) :
    BookRegularBorelMeasure μ ↔ ∀ E : Set X, @MeasurableSet X (borel X) E →
      (μ E = ⨅ (V : Set X) (_ : E ⊆ V) (_ : IsOpen V), μ V) ∧
      (μ E = ⨆ (K : Set X) (_ : K ⊆ E) (_ : IsCompact K), μ K) :=
  Iff.rfl

/-- 2.16: sigma-compactness is a countable union of compact sets. -/
theorem definition_2_16_sigmaCompact (E : Set X) :
    IsSigmaCompact E ↔ ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = E :=
  Iff.rfl

section SigmaFiniteSets

variable [MeasurableSpace X]

/-- 2.16's setwise sigma-finiteness, rather than a global assumption on the measure.
Mathlib's measure also assigns outer measures to nonmeasurable sets; the next
lemma recovers a measurable cover whenever the set itself is measurable. -/
def BookSigmaFiniteSet (μ : Measure X) (E : Set X) : Prop :=
  ∃ A : ℕ → Set X, (∀ n, μ (A n) < ∞) ∧ ⋃ n, A n = E

omit [TopologicalSpace X] in
/-- On a measurable set, allowing outer-measure-finite cover sets does not
change the book's measurable-set notion of sigma-finiteness. -/
theorem definition_2_16_measurableCover (μ : Measure X) {E : Set X}
    (hE : MeasurableSet E) :
    BookSigmaFiniteSet μ E ↔ ∃ A : ℕ → Set X,
      (∀ n, MeasurableSet (A n) ∧ μ (A n) < ∞) ∧ ⋃ n, A n = E := by
  constructor
  · rintro ⟨A, hA, hcov⟩
    refine ⟨fun n => E ∩ toMeasurable μ (A n), ?_, ?_⟩
    · intro n
      refine ⟨hE.inter (measurableSet_toMeasurable _ _), ?_⟩
      exact (measure_mono inter_subset_right).trans_lt (by simpa using hA n)
    · apply subset_antisymm
      · exact iUnion_subset (fun _ => inter_subset_left)
      · intro x hx
        obtain ⟨n, hn⟩ := mem_iUnion.mp (hcov.symm ▸ hx)
        exact mem_iUnion.mpr ⟨n, hx, subset_toMeasurable μ (A n) hn⟩
  · rintro ⟨A, hA, hcov⟩
    exact ⟨A, fun n => (hA n).2, hcov⟩

/-- The first implication following 2.16 uses exactly compact finiteness,
which is clause (b) of 2.14. -/
theorem proposition_2_16_sigmaFinite (μ : Measure X)
    (hcompact : ∀ K : Set X, IsCompact K → μ K < ∞)
    {E : Set X} (hE : IsSigmaCompact E) : BookSigmaFiniteSet μ E := by
  obtain ⟨K, hK, hcov⟩ := hE
  exact ⟨K, fun n => hcompact (K n) (hK n), hcov⟩

/-- The second implication following 2.16. The only regularity input is
2.14(d) for finite measurable sets; no global sigma-finiteness is required. -/
theorem proposition_2_16_innerRegular (μ : Measure X)
    (hfinite : ∀ A : Set X, MeasurableSet A → μ A < ∞ → BookInnerRegularSet μ A)
    {E : Set X} (hE : MeasurableSet E) (hσ : BookSigmaFiniteSet μ E) :
    BookInnerRegularSet μ E := by
  obtain ⟨A, hA, hcov⟩ := (definition_2_16_measurableCover μ hE).mp hσ
  have hsub (n : ℕ) : accumulate A n ⊆ E := by
    rw [← hcov]
    exact accumulate_subset_iUnion n
  have hmeas (n : ℕ) : MeasurableSet (accumulate A n) := by
    rw [accumulate_def]
    exact MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ => (hA i).1))
  have hfin (n : ℕ) : μ (accumulate A n) < ∞ := by
    rw [accumulate_def]
    exact measure_biUnion_lt_top (finite_Iic n) (fun i _ => (hA i).2)
  unfold BookInnerRegularSet
  apply le_antisymm
  · have hsup : μ E = ⨆ n, μ (accumulate A n) := by
      rw [← hcov, measure_iUnion_eq_iSup_accumulate]
    rw [hsup]
    refine iSup_le (fun n => ?_)
    rw [hfinite _ (hmeas n) (hfin n)]
    refine iSup_le (fun K => iSup_le (fun hK => iSup_le (fun hc => ?_)))
    exact le_iSup_of_le K (le_iSup_of_le (hK.trans (hsub n)) (le_iSup_of_le hc le_rfl))
  · exact iSup_le (fun K => iSup_le (fun hK => iSup_le (fun _ => measure_mono hK)))

end SigmaFiniteSets

/-!
## 2.2: Exposition — Integration functionals (printed p. 34)
-/

section Exposition2_2

/-- Rudin's convention `z ≥ 0` in `ℂ`: real (zero imaginary part) and nonnegative real part. -/
def BookNonnegComplex (z : ℂ) : Prop :=
  z.im = 0 ∧ 0 ≤ z.re

theorem proposition_2_2_nonneg_iff (z : ℂ) :
    BookNonnegComplex z ↔ ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ) := by
  constructor
  · rintro ⟨him, hre⟩
    refine ⟨z.re, hre, ?_⟩
    apply Complex.ext <;> simp [him]
  · rintro ⟨r, hr, rfl⟩
    exact ⟨Complex.ofReal_im r, by simpa using hr⟩

/-- Pointwise real-nonnegativity of a complex-valued function (`f ≥ 0` in RCA 2.2). -/
def BookNonnegFun {α : Type*} (f : α → ℂ) : Prop :=
  ∀ x, BookNonnegComplex (f x)

/-- Positivity of a linear functional on a complex vector space of functions (`RCA 2.2`, p. 34):
`Λ f ≥ 0` whenever `f ≥ 0`. -/
def IsPositiveLinearFunctional {α : Type*} (V : Submodule ℂ (α → ℂ))
    (Λ : LinearFunctional V) : Prop :=
  ∀ f : V, BookNonnegFun (f : α → ℂ) → BookNonnegComplex (Λ f)

/-- Positivity of a complex linear functional on `C_c(X)` (`RCA 2.2` / `2.14`). -/
def IsPositiveCcFunctional (Λ : LinearFunctional C_c(X, ℂ)) : Prop :=
  ∀ f : C_c(X, ℂ), BookNonnegFun (f : X → ℂ) → BookNonnegComplex (Λ f)

/-- `L^1(μ)` (`Chapter01.BookL1 μ`) as a complex vector subspace of `α → ℂ` (`RCA 2.2`, p. 34). -/
def bookL1Submodule {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    Submodule ℂ (α → ℂ) where
  carrier := {f | Chapter01.BookL1 μ f}
  zero_mem' := by
    rw [Set.mem_ofPred_eq, Chapter01.definition_1_30]
    exact ⟨measurable_const, integrable_zero _ _ _⟩
  add_mem' := by
    intro f g hf hg
    rw [Set.mem_ofPred_eq, Chapter01.definition_1_30] at hf hg ⊢
    exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    rw [Set.mem_ofPred_eq, Chapter01.definition_1_30] at hf ⊢
    exact ⟨measurable_const.smul hf.1, hf.2.smul c⟩

/-- The integration functional `f ↦ ∫_X f dμ` on `L^1(μ)` (`RCA 2.2`, first example, p. 34). -/
def bookIntegralFunctional {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    LinearFunctional (bookL1Submodule μ) where
  toFun f := Chapter01.BookComplexIntegral μ Set.univ f.1
  map_add' f g := by
    have hf := (Chapter01.definition_1_30 μ f.1).mp f.2
    have hg := (Chapter01.definition_1_30 μ g.1).mp g.2
    have hfg : Chapter01.BookL1 μ (f.1 + g.1) := (f + g).2
    change Chapter01.BookComplexIntegral μ Set.univ (f.1 + g.1) =
      Chapter01.BookComplexIntegral μ Set.univ f.1 + Chapter01.BookComplexIntegral μ Set.univ g.1
    rw [Chapter01.definition_1_31 μ Set.univ (f.1 + g.1) hfg,
      Chapter01.definition_1_31 μ Set.univ f.1 f.2,
      Chapter01.definition_1_31 μ Set.univ g.1 g.2]
    simp only [Measure.restrict_univ]
    exact integral_add hf.2 hg.2
  map_smul' c f := by
    have hcf : Chapter01.BookL1 μ (c • f.1) := (c • f).2
    change Chapter01.BookComplexIntegral μ Set.univ (c • f.1) =
      (RingHom.id ℂ) c • Chapter01.BookComplexIntegral μ Set.univ f.1
    rw [Chapter01.definition_1_31 μ Set.univ (c • f.1) hcf,
      Chapter01.definition_1_31 μ Set.univ f.1 f.2]
    simp only [Measure.restrict_univ, RingHom.id_apply]
    exact integral_smul c f.1

/-- `RCA 2.2`: `f ↦ ∫_X f dμ` is a positive linear functional on `L^1(μ)`. -/
theorem proposition_2_2_l1_positive {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    (∀ f : bookL1Submodule μ, bookIntegralFunctional μ f = ∫ x, f.1 x ∂μ) ∧
    IsPositiveLinearFunctional (bookL1Submodule μ) (bookIntegralFunctional μ) := by
  refine ⟨fun f => ?_, ?_⟩
  · change Chapter01.BookComplexIntegral μ Set.univ f.1 = ∫ x, f.1 x ∂μ
    rw [Chapter01.definition_1_31 μ Set.univ f.1 f.2, Measure.restrict_univ]
  · intro f hnonneg
    have hval : bookIntegralFunctional μ f = ∫ x, f.1 x ∂μ := by
      change Chapter01.BookComplexIntegral μ Set.univ f.1 = ∫ x, f.1 x ∂μ
      rw [Chapter01.definition_1_31 μ Set.univ f.1 f.2, Measure.restrict_univ]
    have hfeq : ∀ x, f.1 x = ((f.1 x).re : ℂ) := by
      intro x
      apply Complex.ext
      · simp
      · simpa using (hnonneg x).1
    have hint_eq : (∫ x, f.1 x ∂μ) = ((∫ x, (f.1 x).re ∂μ : ℝ) : ℂ) :=
      (integral_congr_ae (Filter.Eventually.of_forall hfeq)).trans integral_ofReal
    rw [hval, hint_eq]
    exact ⟨Complex.ofReal_im _, integral_nonneg (fun x => (hnonneg x).2)⟩

/-- Embedding of `C_c(X, ℝ)` into the book's complex-valued `C_c(X, ℂ)`. -/
def ofRealCc (f : C_c(X, ℝ)) : C_c(X, ℂ) :=
  ofRealCutoff f.toContinuousMap f.hasCompactSupport

@[simp]
theorem ofRealCc_apply (f : C_c(X, ℝ)) (x : X) :
    ofRealCc f x = (f x : ℂ) := rfl

/-- Integration against a Borel/opens-measurable measure finite on compact sets as a complex
linear functional on `C_c(X, ℂ)` (`RCA 2.2`, p. 34). -/
def ccIntegralFunctional [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] : LinearFunctional C_c(X, ℂ) where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := integral_add f.integrable g.integrable
  map_smul' c f := by
    simp only [RingHom.id_apply]
    exact integral_smul c (f : X → ℂ)

/-- `RCA 2.2`: positivity of `ccIntegralFunctional μ` on `C_c(X, ℂ)` and exact compatibility with
Mathlib's real `CompactlySupportedContinuousMap.integralPositiveLinearMap`. -/
theorem proposition_2_2_cc_positive [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] :
    IsPositiveCcFunctional (ccIntegralFunctional μ) ∧
    (∀ g : C_c(X, ℝ),
      ccIntegralFunctional μ (ofRealCc g) =
        ((CompactlySupportedContinuousMap.integralPositiveLinearMap μ g : ℝ) : ℂ)) := by
  refine ⟨?_, ?_⟩
  · intro f hnonneg
    change BookNonnegComplex (∫ x, f x ∂μ)
    have hfeq : ∀ x, f x = ((f x).re : ℂ) := by
      intro x
      apply Complex.ext
      · simp
      · simpa using (hnonneg x).1
    have hint_eq : (∫ x, f x ∂μ) = ((∫ x, (f x).re ∂μ : ℝ) : ℂ) :=
      (integral_congr_ae (Filter.Eventually.of_forall hfeq)).trans integral_ofReal
    rw [hint_eq]
    exact ⟨Complex.ofReal_im _, integral_nonneg (fun x => (hnonneg x).2)⟩
  · intro g
    change (∫ x, (g x : ℂ) ∂μ) = ((∫ x, g x ∂μ : ℝ) : ℂ)
    exact integral_ofReal

/-- `RCA 2.2` (second example, p. 34): interval integration on `C([a, b], ℂ)` (`a ≤ b`) as a
complex linear functional. -/
def intervalContinuousFunctional {a b : ℝ} (hab : a ≤ b) :
    LinearFunctional C(Icc a b, ℂ) where
  toFun f := ∫ x in a..b, f (Set.projIcc a b hab x)
  map_add' f g := by
    have hf : Continuous (fun x => f (Set.projIcc a b hab x)) := f.continuous.comp continuous_projIcc
    have hg : Continuous (fun x => g (Set.projIcc a b hab x)) := g.continuous.comp continuous_projIcc
    exact intervalIntegral.integral_add (hf.intervalIntegrable a b) (hg.intervalIntegrable a b)
  map_smul' c f := by
    simp only [RingHom.id_apply]
    exact intervalIntegral.integral_smul c (fun x => f (Set.projIcc a b hab x))

/-- `RCA 2.2`: positivity of the interval integration functional on `C([a, b], ℂ)` for `a ≤ b`,
together with recovery of subinterval length `d - c` (`a ≤ c ≤ d ≤ b`) from continuous functions
below `χ_{(c, d)}` and above `χ_{[c, d]}` (printed p. 34). -/
theorem proposition_2_2_interval_positive_and_length {a b : ℝ} (hab : a ≤ b) :
    (∀ f : C(Icc a b, ℂ), BookNonnegFun (f : Icc a b → ℂ) →
      BookNonnegComplex (intervalContinuousFunctional hab f)) ∧
    (∀ {c d : ℝ}, a ≤ c → c ≤ d → d ≤ b →
      d - c = sSup {r : ℝ | ∃ f : C(Icc a b, ℝ),
        (∀ x : Icc a b, 0 ≤ f x ∧ f x ≤ (Ioo c d).indicator 1 (x : ℝ)) ∧
        r = ∫ x in a..b, f (Set.projIcc a b hab x)} ∧
      d - c = sInf {r : ℝ | ∃ f : C(Icc a b, ℝ),
        (∀ x : Icc a b, (Icc c d).indicator 1 (x : ℝ) ≤ f x) ∧
        r = ∫ x in a..b, f (Set.projIcc a b hab x)}) := by
  refine ⟨?_, ?_⟩
  · intro f hnonneg
    change BookNonnegComplex (∫ x in a..b, f (Set.projIcc a b hab x))
    have hfeq : ∀ x, f (Set.projIcc a b hab x) = ((f (Set.projIcc a b hab x)).re : ℂ) := by
      intro x
      apply Complex.ext
      · simp
      · simpa using (hnonneg (Set.projIcc a b hab x)).1
    have hint_eq : (∫ x in a..b, f (Set.projIcc a b hab x)) =
        ((∫ x in a..b, (f (Set.projIcc a b hab x)).re : ℝ) : ℂ) :=
      (intervalIntegral.integral_congr fun x _ => hfeq x).trans intervalIntegral.integral_ofReal
    rw [hint_eq]
    exact ⟨Complex.ofReal_im _,
      intervalIntegral.integral_nonneg hab (fun x _ => (hnonneg (Set.projIcc a b hab x)).2)⟩
  · intro c d hac hcd hdb
    let S_low : Set ℝ := {r : ℝ | ∃ f : C(Icc a b, ℝ),
      (∀ x : Icc a b, 0 ≤ f x ∧ f x ≤ (Ioo c d).indicator 1 (x : ℝ)) ∧
      r = ∫ x in a..b, f (Set.projIcc a b hab x)}
    let S_high : Set ℝ := {r : ℝ | ∃ f : C(Icc a b, ℝ),
      (∀ x : Icc a b, (Icc c d).indicator 1 (x : ℝ) ≤ f x) ∧
      r = ∫ x in a..b, f (Set.projIcc a b hab x)}
    have hlow_zero : (0 : ℝ) ∈ S_low := by
      refine ⟨0, fun x => ⟨le_rfl, ?_⟩, by simp⟩
      by_cases hx : (x : ℝ) ∈ Ioo c d <;> simp [hx]
    have hlow_ub : ∀ r ∈ S_low, r ≤ d - c := by
      rintro r ⟨f, hf, rfl⟩
      have hcont : Continuous (fun x => f (Set.projIcc a b hab x)) :=
        f.continuous.comp continuous_projIcc
      have hsplit1 := (intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable (μ := volume) a c)
        (hcont.intervalIntegrable (μ := volume) c b)).symm
      have hsplit2 := (intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable (μ := volume) c d)
        (hcont.intervalIntegrable (μ := volume) d b)).symm
      have h_ac : ∫ x in a..c, f (Set.projIcc a b hab x) = 0 := by
        refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_).trans
          intervalIntegral.integral_zero
        intro x hx
        rw [Set.uIcc_of_le hac] at hx
        have hproj : (Set.projIcc a b hab x : ℝ) = x :=
          congrArg Subtype.val (Set.projIcc_of_mem hab ⟨hx.1, hx.2.trans (hcd.trans hdb)⟩)
        have hnot : (Set.projIcc a b hab x : ℝ) ∉ Ioo c d := by
          rw [hproj]
          intro hmem
          linarith [hx.2, hmem.1]
        have hle := (hf (Set.projIcc a b hab x)).2
        have hge := (hf (Set.projIcc a b hab x)).1
        simp [hnot] at hle
        linarith
      have h_db : ∫ x in d..b, f (Set.projIcc a b hab x) = 0 := by
        refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_).trans
          intervalIntegral.integral_zero
        intro x hx
        rw [Set.uIcc_of_le hdb] at hx
        have hproj : (Set.projIcc a b hab x : ℝ) = x :=
          congrArg Subtype.val (Set.projIcc_of_mem hab ⟨(hac.trans hcd).trans hx.1, hx.2⟩)
        have hnot : (Set.projIcc a b hab x : ℝ) ∉ Ioo c d := by
          rw [hproj]
          intro hmem
          linarith [hx.1, hmem.2]
        have hle := (hf (Set.projIcc a b hab x)).2
        have hge := (hf (Set.projIcc a b hab x)).1
        simp [hnot] at hle
        linarith
      have h_cd : ∫ x in c..d, f (Set.projIcc a b hab x) ≤ d - c := by
        calc
          ∫ x in c..d, f (Set.projIcc a b hab x)
              ≤ ∫ _ in c..d, (1 : ℝ) := by
                apply intervalIntegral.integral_mono_on hcd (hcont.intervalIntegrable c d)
                  intervalIntegrable_const
                intro x _
                have hle := (hf (Set.projIcc a b hab x)).2
                by_cases hmem : (Set.projIcc a b hab x : ℝ) ∈ Ioo c d <;> simp [hmem] at hle <;> linarith
          _ = d - c := by simp
      rw [hsplit1, hsplit2, h_ac, h_db]
      linarith
    have hhigh_one : b - a ∈ S_high := by
      refine ⟨1, fun x => ?_, ?_⟩
      · by_cases hx : (x : ℝ) ∈ Icc c d <;> simp [hx]
      · simp
    have hhigh_lb : ∀ r ∈ S_high, d - c ≤ r := by
      rintro r ⟨f, hf, rfl⟩
      have hcont : Continuous (fun x => f (Set.projIcc a b hab x)) :=
        f.continuous.comp continuous_projIcc
      have hsplit1 := (intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable (μ := volume) a c)
        (hcont.intervalIntegrable (μ := volume) c b)).symm
      have hsplit2 := (intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable (μ := volume) c d)
        (hcont.intervalIntegrable (μ := volume) d b)).symm
      have hf_nonneg : ∀ x : ℝ, 0 ≤ f (Set.projIcc a b hab x) := by
        intro x
        have h := hf (Set.projIcc a b hab x)
        by_cases hm : (Set.projIcc a b hab x : ℝ) ∈ Icc c d <;> simp [hm] at h <;> linarith
      have h_ac : 0 ≤ ∫ x in a..c, f (Set.projIcc a b hab x) :=
        intervalIntegral.integral_nonneg hac (fun x _ => hf_nonneg x)
      have h_db : 0 ≤ ∫ x in d..b, f (Set.projIcc a b hab x) :=
        intervalIntegral.integral_nonneg hdb (fun x _ => hf_nonneg x)
      have h_cd : d - c ≤ ∫ x in c..d, f (Set.projIcc a b hab x) := by
        calc
          d - c = ∫ _ in c..d, (1 : ℝ) := by simp
          _ ≤ ∫ x in c..d, f (Set.projIcc a b hab x) := by
            apply intervalIntegral.integral_mono_on hcd intervalIntegrable_const
              (hcont.intervalIntegrable c d)
            intro x hx
            have hproj : (Set.projIcc a b hab x : ℝ) = x :=
              congrArg Subtype.val
                (Set.projIcc_of_mem hab ⟨hac.trans hx.1, hx.2.trans hdb⟩)
            have h := hf (Set.projIcc a b hab x)
            rw [hproj, indicator_of_mem hx] at h
            exact h
      rw [hsplit1, hsplit2]
      linarith
    refine ⟨?_, ?_⟩
    · refine le_antisymm ?_ (csSup_le ⟨0, hlow_zero⟩ hlow_ub)
      rcases eq_or_lt_of_le hcd with rfl | hlt
      · rw [sub_self]
        exact le_csSup ⟨c - c, hlow_ub⟩ hlow_zero
      · refine le_of_forall_pos_le_add fun ε hε => ?_
        let δ : ℝ := min (ε / 2) ((d - c) / 3)
        have hδ_pos : 0 < δ := lt_min (half_pos hε) (by linarith)
        have hδ_le_eps : 2 * δ ≤ ε := by
          have : δ ≤ ε / 2 := min_le_left _ _
          linarith
        have hcp_le_dq : c + δ ≤ d - δ := by
          have : δ ≤ (d - c) / 3 := min_le_right _ _
          linarith
        let g : ℝ → ℝ := fun x =>
          max 0 (1 - max 0 (max (c + δ - x) (x - (d - δ))) / (δ / 2))
        have hg_cont : Continuous g := by
          unfold g
          fun_prop
        let f : C(Icc a b, ℝ) := ⟨fun x => g x.1, hg_cont.comp continuous_subtype_val⟩
        have hf_mem : ∫ x in a..b, f (Set.projIcc a b hab x) ∈ S_low := by
          refine ⟨f, fun x => ⟨le_max_left _ _, ?_⟩, rfl⟩
          by_cases hx : (x : ℝ) ∈ Ioo c d
          · rw [indicator_of_mem hx, Pi.one_apply]
            have hdist_nonneg : 0 ≤ max 0 (max (c + δ - (x : ℝ)) ((x : ℝ) - (d - δ))) / (δ / 2) :=
              div_nonneg (le_max_left _ _) (half_pos hδ_pos).le
            exact max_le zero_le_one (by linarith)
          · rw [indicator_of_notMem hx]
            have hxc_or_dx : (x : ℝ) ≤ c ∨ d ≤ (x : ℝ) := by
              rcases le_or_gt (x : ℝ) c with hxc | hcx
              · exact Or.inl hxc
              · exact Or.inr (le_of_not_gt fun hxd => hx ⟨hcx, hxd⟩)
            have hge : δ / 2 ≤ max 0 (max (c + δ - (x : ℝ)) ((x : ℝ) - (d - δ))) := by
              rcases hxc_or_dx with hxc | hdx
              · exact le_trans (by linarith)
                  ((le_max_left _ _).trans (le_max_right (0 : ℝ) _))
              · exact le_trans (by linarith)
                  ((le_max_right _ _).trans (le_max_right (0 : ℝ) _))
            have hdiv : 1 ≤ max 0 (max (c + δ - (x : ℝ)) ((x : ℝ) - (d - δ))) / (δ / 2) :=
              (one_le_div (half_pos hδ_pos)).mpr hge
            exact max_le le_rfl (by linarith)
        have hf_int_ge : (d - δ) - (c + δ) ≤ ∫ x in a..b, f (Set.projIcc a b hab x) := by
          have hcont : Continuous (fun x => f (Set.projIcc a b hab x)) :=
            f.continuous.comp continuous_projIcc
          have hsplit1 := (intervalIntegral.integral_add_adjacent_intervals
            (hcont.intervalIntegrable (μ := volume) a (c + δ))
            (hcont.intervalIntegrable (μ := volume) (c + δ) b)).symm
          have hsplit2 := (intervalIntegral.integral_add_adjacent_intervals
            (hcont.intervalIntegrable (μ := volume) (c + δ) (d - δ))
            (hcont.intervalIntegrable (μ := volume) (d - δ) b)).symm
          have h1 : 0 ≤ ∫ x in a..(c + δ), f (Set.projIcc a b hab x) :=
            intervalIntegral.integral_nonneg (by linarith) (fun _ _ => le_max_left _ _)
          have h2 : 0 ≤ ∫ x in (d - δ)..b, f (Set.projIcc a b hab x) :=
            intervalIntegral.integral_nonneg (by linarith) (fun _ _ => le_max_left _ _)
          have h3 : (d - δ) - (c + δ) ≤ ∫ x in (c + δ)..(d - δ), f (Set.projIcc a b hab x) := by
            calc
              (d - δ) - (c + δ) = ∫ _ in (c + δ)..(d - δ), (1 : ℝ) := by simp
              _ ≤ ∫ x in (c + δ)..(d - δ), f (Set.projIcc a b hab x) := by
                apply intervalIntegral.integral_mono_on hcp_le_dq intervalIntegrable_const
                  (hcont.intervalIntegrable _ _)
                intro x hx
                have hxab : x ∈ Icc a b := ⟨by linarith [hx.1], by linarith [hx.2]⟩
                have hproj : Set.projIcc a b hab x = ⟨x, hxab⟩ := Set.projIcc_of_mem hab hxab
                rw [hproj]
                change 1 ≤ g x
                have hmax0 : max 0 (max (c + δ - x) (x - (d - δ))) = 0 :=
                  max_eq_left (max_le (by linarith [hx.1]) (by linarith [hx.2]))
                simp [g, hmax0]
          rw [hsplit1, hsplit2]
          linarith
        have hle_sup := le_csSup ⟨d - c, hlow_ub⟩ hf_mem
        linarith
    · refine le_antisymm (le_csInf ⟨b - a, hhigh_one⟩ hhigh_lb) ?_
      refine le_of_forall_pos_le_add fun ε hε => ?_
      let δ : ℝ := ε / 2
      have hδ_pos : 0 < δ := half_pos hε
      let g : ℝ → ℝ := fun x =>
        max 0 (1 - max 0 (max (c - x) (x - d)) / δ)
      have hg_cont : Continuous g := by
        unfold g
        fun_prop
      let f : C(Icc a b, ℝ) := ⟨fun x => g x.1, hg_cont.comp continuous_subtype_val⟩
      have hf_mem : ∫ x in a..b, f (Set.projIcc a b hab x) ∈ S_high := by
        refine ⟨f, fun x => ?_, rfl⟩
        by_cases hx : (x : ℝ) ∈ Icc c d
        · rw [indicator_of_mem hx, Pi.one_apply]
          change 1 ≤ g x.1
          have hmax0 : max 0 (max (c - (x : ℝ)) ((x : ℝ) - d)) = 0 :=
            max_eq_left (max_le (by linarith [hx.1]) (by linarith [hx.2]))
          simp [g, hmax0]
        · rw [indicator_of_notMem hx]
          exact le_max_left _ _
      have hf_int_le : ∫ x in a..b, f (Set.projIcc a b hab x) ≤ d - c + 2 * δ := by
        let p := max a (c - δ)
        let q := min b (d + δ)
        have hap : a ≤ p := le_max_left _ _
        have hpq : p ≤ q := max_le
          (le_min hab (by linarith))
          (le_min (by linarith) (by linarith))
        have hqb : q ≤ b := min_le_left _ _
        have hcont : Continuous (fun x => f (Set.projIcc a b hab x)) :=
          f.continuous.comp continuous_projIcc
        have hsplit1 := (intervalIntegral.integral_add_adjacent_intervals
          (hcont.intervalIntegrable (μ := volume) a p)
          (hcont.intervalIntegrable (μ := volume) p b)).symm
        have hsplit2 := (intervalIntegral.integral_add_adjacent_intervals
          (hcont.intervalIntegrable (μ := volume) p q)
          (hcont.intervalIntegrable (μ := volume) q b)).symm
        have h_ap : ∫ x in a..p, f (Set.projIcc a b hab x) = 0 := by
          rcases le_total a (c - δ) with hacδ | hcaδ
          · have hp_eq : p = c - δ := max_eq_right hacδ
            refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_).trans
              intervalIntegral.integral_zero
            intro x hx
            rw [Set.uIcc_of_le hap] at hx
            have hxcδ : x ≤ c - δ := hp_eq ▸ hx.2
            have hxab : x ∈ Icc a b := ⟨hx.1, hxcδ.trans (by linarith)⟩
            have hproj : Set.projIcc a b hab x = ⟨x, hxab⟩ := Set.projIcc_of_mem hab hxab
            dsimp only
            rw [hproj]
            change g x = 0
            have hge : δ ≤ max 0 (max (c - x) (x - d)) :=
              le_trans (by linarith) ((le_max_left _ _).trans (le_max_right (0 : ℝ) _))
            have hdiv : 1 ≤ max 0 (max (c - x) (x - d)) / δ := (one_le_div hδ_pos).mpr hge
            exact le_antisymm (max_le le_rfl (by linarith)) (le_max_left _ _)
          · have hp_eq : p = a := max_eq_left hcaδ
            simp [hp_eq]
        have h_qb : ∫ x in q..b, f (Set.projIcc a b hab x) = 0 := by
          rcases le_total (d + δ) b with hdbδ | hbdδ
          · have hq_eq : q = d + δ := min_eq_right hdbδ
            refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_).trans
              intervalIntegral.integral_zero
            intro x hx
            rw [Set.uIcc_of_le hqb] at hx
            have hdxδ : d + δ ≤ x := hq_eq ▸ hx.1
            have hxab : x ∈ Icc a b := ⟨(by linarith : a ≤ d + δ).trans hdxδ, hx.2⟩
            have hproj : Set.projIcc a b hab x = ⟨x, hxab⟩ := Set.projIcc_of_mem hab hxab
            dsimp only
            rw [hproj]
            change g x = 0
            have hge : δ ≤ max 0 (max (c - x) (x - d)) :=
              le_trans (by linarith) ((le_max_right _ _).trans (le_max_right (0 : ℝ) _))
            have hdiv : 1 ≤ max 0 (max (c - x) (x - d)) / δ := (one_le_div hδ_pos).mpr hge
            exact le_antisymm (max_le le_rfl (by linarith)) (le_max_left _ _)
          · have hq_eq : q = b := min_eq_left hbdδ
            simp [hq_eq]
        have h_pq : ∫ x in p..q, f (Set.projIcc a b hab x) ≤ q - p := by
          calc
            ∫ x in p..q, f (Set.projIcc a b hab x)
                ≤ ∫ _ in p..q, (1 : ℝ) := by
                  apply intervalIntegral.integral_mono_on hpq (hcont.intervalIntegrable p q)
                    intervalIntegrable_const
                  intro x _
                  change g (Set.projIcc a b hab x).1 ≤ 1
                  have hnn : 0 ≤ max 0 (max (c - (Set.projIcc a b hab x : ℝ))
                      ((Set.projIcc a b hab x : ℝ) - d)) / δ :=
                    div_nonneg (le_max_left _ _) hδ_pos.le
                  exact max_le zero_le_one (by linarith)
            _ = q - p := by simp
        have hqp_le : q - p ≤ d - c + 2 * δ := by
          have hp_ge : c - δ ≤ p := le_max_right _ _
          have hq_le : q ≤ d + δ := min_le_right _ _
          linarith
        rw [hsplit1, hsplit2, h_ap, h_qb]
        linarith
      have hinf_le := csInf_le ⟨d - c, hhigh_lb⟩ hf_mem
      have h2δ : 2 * δ = ε := by ring
      linarith

end Exposition2_2

/-!
## 2.19: Exposition — Euclidean cells and dyadic decomposition (printed pp. 49–50)
-/

section Exposition2_19

/-- Boundary conventions for each coordinate interval of a Euclidean `k`-cell (`RCA 2.19`, p. 49). -/
inductive CellIntervalKind : Type
  | openInterval
  | closedInterval
  | closedOpen
  | openClosed
  deriving DecidableEq

/-- Coordinate interval `I_i` of a `k`-cell under one of Rudin's four boundary choices. -/
def cellCoordInterval (kind : CellIntervalKind) (a b : ℝ) : Set ℝ :=
  match kind with
  | .openInterval => Ioo a b
  | .closedInterval => Icc a b
  | .closedOpen => Ico a b
  | .openClosed => Ioc a b

/-- General Euclidean `k`-cell `∏_{i=1}^k I_i` in `ℝ^k = EuclideanSpace ℝ (Fin k)` (`RCA 2.19`). -/
def kCell {k : ℕ} (kind : Fin k → CellIntervalKind) (a b : Fin k → ℝ) :
    Set (EuclideanSpace ℝ (Fin k)) :=
  {x | ∀ i : Fin k, x i ∈ cellCoordInterval (kind i) (a i) (b i)}

/-- Open `k`-cell `∏_i (a_i, b_i)`. -/
def openKCell {k : ℕ} (a b : Fin k → ℝ) : Set (EuclideanSpace ℝ (Fin k)) :=
  kCell (fun _ => .openInterval) a b

/-- Closed `k`-cell `∏_i [a_i, b_i]`. -/
def closedKCell {k : ℕ} (a b : Fin k → ℝ) : Set (EuclideanSpace ℝ (Fin k)) :=
  kCell (fun _ => .closedInterval) a b

/-- Half-open `k`-cell `∏_i [a_i, b_i)` used for Rudin's `δ`-boxes and dyadic boxes. -/
def halfOpenKCell {k : ℕ} (a b : Fin k → ℝ) : Set (EuclideanSpace ℝ (Fin k)) :=
  kCell (fun _ => .closedOpen) a b

/-- Elementary volume `vol(W) = ∏_{i=1}^k max(0, b_i - a_i)` of a `k`-cell (`∏_i (b_i - a_i)` when
`a_i ≤ b_i` for all `i`, `RCA 2.19`, p. 49). -/
def cellVolume {k : ℕ} (a b : Fin k → ℝ) : ℝ :=
  ∏ i : Fin k, max 0 (b i - a i)

theorem cellVolume_of_le {k : ℕ} {a b : Fin k → ℝ} (hab : ∀ i, a i ≤ b i) :
    cellVolume a b = ∏ i : Fin k, (b i - a i) := by
  unfold cellVolume
  refine Finset.prod_congr rfl fun i _ => max_eq_right (sub_nonneg.mpr (hab i))

theorem measurableSet_cellCoordInterval (kind : CellIntervalKind) (a b : ℝ) :
    MeasurableSet (cellCoordInterval kind a b) := by
  cases kind with
  | openInterval => exact measurableSet_Ioo
  | closedInterval => exact measurableSet_Icc
  | closedOpen => exact measurableSet_Ico
  | openClosed => exact measurableSet_Ioc

theorem volume_cellCoordInterval (kind : CellIntervalKind) (a b : ℝ) :
    volume (cellCoordInterval kind a b) = ENNReal.ofReal (b - a) := by
  cases kind with
  | openInterval => exact Real.volume_Ioo
  | closedInterval => exact Real.volume_Icc
  | closedOpen => exact Real.volume_Ico
  | openClosed => exact Real.volume_Ioc

theorem measurableSet_kCell {k : ℕ} (kind : Fin k → CellIntervalKind) (a b : Fin k → ℝ) :
    MeasurableSet (kCell kind a b) := by
  have heq : kCell kind a b =
      (@WithLp.ofLp 2 (Fin k → ℝ)) ⁻¹'
        (Set.pi univ fun i => cellCoordInterval (kind i) (a i) (b i)) := by
    ext x
    simp [kCell]
  rw [heq]
  exact (PiLp.volume_preserving_ofLp (Fin k)).measurable
    (MeasurableSet.univ_pi fun i => measurableSet_cellCoordInterval (kind i) (a i) (b i))

/-- Volume of any `k`-cell in `EuclideanSpace ℝ (Fin k)` equals `cellVolume a b` regardless of
which of the `4^k` endpoint conventions is chosen on each coordinate (`RCA 2.19` / `2.20(a)`). -/
theorem proposition_2_19_cell_volume {k : ℕ} (kind : Fin k → CellIntervalKind)
    (a b : Fin k → ℝ) :
    volume (kCell kind a b) = ENNReal.ofReal (cellVolume a b) := by
  have heq : kCell kind a b =
      (@WithLp.ofLp 2 (Fin k → ℝ)) ⁻¹'
        (Set.pi univ fun i => cellCoordInterval (kind i) (a i) (b i)) := by
    ext x
    simp [kCell]
  have hmeas : MeasurableSet (Set.pi univ fun i => cellCoordInterval (kind i) (a i) (b i)) :=
    MeasurableSet.univ_pi fun i => measurableSet_cellCoordInterval (kind i) (a i) (b i)
  rw [heq, (PiLp.volume_preserving_ofLp (Fin k)).measure_preimage hmeas.nullMeasurableSet,
    MeasureTheory.volume_pi_pi]
  simp_rw [volume_cellCoordInterval]
  unfold cellVolume
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => le_max_left 0 (b i - a i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : 0 ≤ b i - a i
  · rw [max_eq_right h]
  · have hle : b i - a i ≤ 0 := le_of_not_ge h
    rw [max_eq_left hle, ENNReal.ofReal_of_nonpos hle, ENNReal.ofReal_zero]

/-- Bridge between `kCell` on `EuclideanSpace ℝ (Fin k)` and Mathlib's `BoxIntegral.Box (Fin k)`. -/
theorem proposition_2_19_boxIntegral_bridge {k : ℕ} (I : BoxIntegral.Box (Fin k)) :
    (@WithLp.ofLp 2 (Fin k → ℝ)) ⁻¹' (I : Set (Fin k → ℝ)) =
      kCell (fun _ => .openClosed) I.lower I.upper ∧
    (@WithLp.ofLp 2 (Fin k → ℝ)) ⁻¹' (BoxIntegral.Box.Icc I) =
      closedKCell I.lower I.upper := by
  refine ⟨?_, ?_⟩
  · ext x
    simp [kCell, cellCoordInterval, BoxIntegral.Box.mem_coe, BoxIntegral.Box.mem_def]
  · ext x
    simp [closedKCell, kCell, cellCoordInterval, BoxIntegral.Box.Icc_eq_pi, Pi.le_def, forall_and]

/-- Rudin's `δ`-box `Q(a; δ) = ∏_{i=1}^k [a_i, a_i + δ)` with corner `a` (`RCA 2.19`, p. 49). -/
def deltaBox {k : ℕ} (a : Fin k → ℝ) (δ : ℝ) : Set (EuclideanSpace ℝ (Fin k)) :=
  halfOpenKCell a (fun i => a i + δ)

/-- Corner point `m / 2^n ∈ P_n` in `EuclideanSpace ℝ (Fin k)` (`RCA 2.19`, p. 49). -/
def dyadicCorner {k : ℕ} (n : ℕ) (m : Fin k → ℤ) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => (m i : ℝ) / (2 : ℝ) ^ n)

/-- Dyadic vertex lattice `P_n` of points whose coordinates are integral multiples of `2^{-n}`. -/
def dyadicGrid (k n : ℕ) : Set (EuclideanSpace ℝ (Fin k)) :=
  range (dyadicCorner (k := k) n)

/-- Half-open `2^{-n}`-box `Q(m / 2^n; 2^{-n})` with corner in `P_n`. -/
def dyadicBox (k n : ℕ) (m : Fin k → ℤ) : Set (EuclideanSpace ℝ (Fin k)) :=
  deltaBox (fun i => (m i : ℝ) / (2 : ℝ) ^ n) ((1 : ℝ) / (2 : ℝ) ^ n)

/-- Collection `Ω_n` of all `2^{-n}`-boxes with corners in `P_n` (`RCA 2.19`, p. 49). -/
def dyadicCollection (k n : ℕ) : Set (Set (EuclideanSpace ℝ (Fin k))) :=
  range (dyadicBox k n)

theorem mem_dyadicBox_iff {k n : ℕ} {m : Fin k → ℤ} {x : EuclideanSpace ℝ (Fin k)} :
    x ∈ dyadicBox k n m ↔
      ∀ i : Fin k, (m i : ℝ) / (2 : ℝ) ^ n ≤ x i ∧ x i < ((m i : ℝ) + 1) / (2 : ℝ) ^ n := by
  simp only [dyadicBox, deltaBox, halfOpenKCell, kCell, cellCoordInterval, Set.mem_ofPred_eq,
    mem_Ico]
  refine forall_congr' fun i => and_congr_right fun _ => ?_
  rw [add_div]

theorem dyadicCorner_mem_self {k n : ℕ} (m : Fin k → ℤ) :
    dyadicCorner n m ∈ dyadicBox k n m := by
  rw [mem_dyadicBox_iff]
  intro i
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos zero_lt_two n
  refine ⟨le_rfl, ?_⟩
  change (m i : ℝ) / (2 : ℝ) ^ n < ((m i : ℝ) + 1) / (2 : ℝ) ^ n
  exact div_lt_div_of_pos_right (by linarith) h2n

theorem dyadicCorner_injective (k n : ℕ) :
    Function.Injective (dyadicCorner (k := k) n) := by
  intro m₁ m₂ h
  funext i
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  have hi : (dyadicCorner n m₁) i = (dyadicCorner n m₂) i := congrArg (fun x => x i) h
  change (m₁ i : ℝ) / (2 : ℝ) ^ n = (m₂ i : ℝ) / (2 : ℝ) ^ n at hi
  have hreal : (m₁ i : ℝ) = (m₂ i : ℝ) := (div_left_inj' h2n).mp hi
  exact_mod_cast hreal

theorem dyadicBox_injective (k n : ℕ) :
    Function.Injective (dyadicBox k n) := by
  intro m₁ m₂ h
  have hmem : dyadicCorner n m₁ ∈ dyadicBox k n m₂ := h ▸ dyadicCorner_mem_self m₁
  rw [mem_dyadicBox_iff] at hmem
  funext i
  have hi := hmem i
  change (m₂ i : ℝ) / (2 : ℝ) ^ n ≤ (m₁ i : ℝ) / (2 : ℝ) ^ n ∧
    (m₁ i : ℝ) / (2 : ℝ) ^ n < ((m₂ i : ℝ) + 1) / (2 : ℝ) ^ n at hi
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos zero_lt_two n
  have hle : (m₂ i : ℝ) ≤ (m₁ i : ℝ) := (div_le_div_iff_of_pos_right h2n).mp hi.1
  have hlt : (m₁ i : ℝ) < (m₂ i : ℝ) + 1 := (div_lt_div_iff_of_pos_right h2n).mp hi.2
  have hle_z : m₂ i ≤ m₁ i := by exact_mod_cast hle
  have hlt_z : m₁ i < m₂ i + 1 := by exact_mod_cast hlt
  omega

/-- `RCA 2.19(a)` (p. 49): for fixed `n`, every `x ∈ ℝ^k` lies in one and only one member of `Ω_n`. -/
theorem proposition_2_19a (k n : ℕ) (x : EuclideanSpace ℝ (Fin k)) :
    (∃! m : Fin k → ℤ, x ∈ dyadicBox k n m) ∧
    (∃! Q : Set (EuclideanSpace ℝ (Fin k)), Q ∈ dyadicCollection k n ∧ x ∈ Q) := by
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos zero_lt_two n
  let m₀ : Fin k → ℤ := fun i => ⌊x i * (2 : ℝ) ^ n⌋
  have hm₀ : x ∈ dyadicBox k n m₀ := by
    rw [mem_dyadicBox_iff]
    intro i
    refine ⟨(div_le_iff₀ h2n).mpr (Int.floor_le _),
      (lt_div_iff₀ h2n).mpr (Int.lt_floor_add_one _)⟩
  have huniq_m : ∀ m : Fin k → ℤ, x ∈ dyadicBox k n m → m = m₀ := by
    intro m hm
    rw [mem_dyadicBox_iff] at hm
    funext i
    have hle : (m i : ℝ) ≤ x i * (2 : ℝ) ^ n := (div_le_iff₀ h2n).mp (hm i).1
    have hlt : x i * (2 : ℝ) ^ n < (m i : ℝ) + 1 := (lt_div_iff₀ h2n).mp (hm i).2
    exact (Int.floor_eq_iff.mpr ⟨hle, hlt⟩).symm
  refine ⟨⟨m₀, hm₀, huniq_m⟩, ⟨dyadicBox k n m₀, ⟨⟨m₀, rfl⟩, hm₀⟩, ?_⟩⟩
  rintro Q ⟨⟨m, rfl⟩, hxQ⟩
  rw [huniq_m m hxQ]

/-- `RCA 2.19(b)` (p. 49): if `Q₁ ∈ Ω_n`, `Q₂ ∈ Ω_r`, and `n ≤ r`, then either `Q₂ ⊆ Q₁` or
`Q₁ ∩ Q₂ = ∅`. -/
theorem proposition_2_19b {k n r : ℕ} (hnr : n ≤ r)
    {Q₁ Q₂ : Set (EuclideanSpace ℝ (Fin k))}
    (hQ₁ : Q₁ ∈ dyadicCollection k n) (hQ₂ : Q₂ ∈ dyadicCollection k r) :
    Q₂ ⊆ Q₁ ∨ Q₁ ∩ Q₂ = ∅ := by
  by_cases hne : (Q₁ ∩ Q₂).Nonempty
  · left
    obtain ⟨m₁, rfl⟩ := hQ₁
    obtain ⟨m₂, rfl⟩ := hQ₂
    obtain ⟨x, hx₁, hx₂⟩ := hne
    rw [mem_dyadicBox_iff] at hx₁ hx₂
    intro y hy
    rw [mem_dyadicBox_iff] at hy ⊢
    intro i
    have h2n : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos zero_lt_two n
    have h2r : (0 : ℝ) < (2 : ℝ) ^ r := pow_pos zero_lt_two r
    have hpow_eq : (2 : ℝ) ^ r = (2 : ℝ) ^ n * (2 : ℝ) ^ (r - n) := by
      rw [← pow_add, Nat.add_sub_cancel' hnr]
    have hx₁_le : (m₁ i : ℝ) * (2 : ℝ) ^ (r - n) ≤ x i * (2 : ℝ) ^ r := by
      have h := (div_le_iff₀ h2n).mp (hx₁ i).1
      have h2d : (0 : ℝ) ≤ (2 : ℝ) ^ (r - n) := pow_nonneg zero_le_two _
      calc
        (m₁ i : ℝ) * (2 : ℝ) ^ (r - n) ≤ (x i * (2 : ℝ) ^ n) * (2 : ℝ) ^ (r - n) :=
          mul_le_mul_of_nonneg_right h h2d
        _ = x i * (2 : ℝ) ^ r := by rw [mul_assoc, ← hpow_eq]
    have hx₁_lt : x i * (2 : ℝ) ^ r < ((m₁ i : ℝ) + 1) * (2 : ℝ) ^ (r - n) := by
      have h := (lt_div_iff₀ h2n).mp (hx₁ i).2
      have h2d : (0 : ℝ) < (2 : ℝ) ^ (r - n) := pow_pos zero_lt_two _
      calc
        x i * (2 : ℝ) ^ r = (x i * (2 : ℝ) ^ n) * (2 : ℝ) ^ (r - n) := by
          rw [mul_assoc, ← hpow_eq]
        _ < ((m₁ i : ℝ) + 1) * (2 : ℝ) ^ (r - n) := mul_lt_mul_of_pos_right h h2d
    have hx₂_le : (m₂ i : ℝ) ≤ x i * (2 : ℝ) ^ r := (div_le_iff₀ h2r).mp (hx₂ i).1
    have hx₂_lt : x i * (2 : ℝ) ^ r < (m₂ i : ℝ) + 1 := (lt_div_iff₀ h2r).mp (hx₂ i).2
    have hlt_z1 : m₁ i * (2 : ℤ) ^ (r - n) < m₂ i + 1 := by
      have hreal : ((m₁ i * (2 : ℤ) ^ (r - n) : ℤ) : ℝ) < ((m₂ i + 1 : ℤ) : ℝ) := by
        push_cast
        exact lt_of_le_of_lt hx₁_le hx₂_lt
      exact_mod_cast hreal
    have hlt_z2 : m₂ i < (m₁ i + 1) * (2 : ℤ) ^ (r - n) := by
      have hreal : (m₂ i : ℝ) < (((m₁ i + 1) * (2 : ℤ) ^ (r - n) : ℤ) : ℝ) := by
        push_cast
        exact lt_of_le_of_lt hx₂_le hx₁_lt
      exact_mod_cast hreal
    have hle_z1 : m₁ i * (2 : ℤ) ^ (r - n) ≤ m₂ i := by omega
    have hle_z2 : m₂ i + 1 ≤ (m₁ i + 1) * (2 : ℤ) ^ (r - n) := by omega
    have hle_r1 : (m₁ i : ℝ) / (2 : ℝ) ^ n ≤ (m₂ i : ℝ) / (2 : ℝ) ^ r := by
      rw [div_le_div_iff₀ h2n h2r, hpow_eq]
      have hreal : ((m₁ i * (2 : ℤ) ^ (r - n) : ℤ) : ℝ) ≤ (m₂ i : ℝ) := by
        exact_mod_cast hle_z1
      push_cast at hreal
      nlinarith [h2n]
    have hle_r2 : ((m₂ i : ℝ) + 1) / (2 : ℝ) ^ r ≤ ((m₁ i : ℝ) + 1) / (2 : ℝ) ^ n := by
      rw [div_le_div_iff₀ h2r h2n, hpow_eq]
      have hreal : ((m₂ i + 1 : ℤ) : ℝ) ≤ (((m₁ i + 1) * (2 : ℤ) ^ (r - n) : ℤ) : ℝ) := by
        exact_mod_cast hle_z2
      push_cast at hreal
      nlinarith [h2n]
    exact ⟨hle_r1.trans (hy i).1, (hy i).2.trans_le hle_r2⟩
  · right
    exact Set.not_nonempty_iff_eq_empty.mp hne

/-- `RCA 2.19(c)` (p. 50): if `Q ∈ Ω_n`, then `vol(Q) = 2^{-nk}`; and if `n ≤ r`, the set `P_r` has
exactly `2^{(r - n) k}` points in `Q`. -/
theorem proposition_2_19c {k n : ℕ} {Q : Set (EuclideanSpace ℝ (Fin k))}
    (hQ : Q ∈ dyadicCollection k n) :
    (∃ m : Fin k → ℤ,
      Q = dyadicBox k n m ∧
      cellVolume (fun i => (m i : ℝ) / (2 : ℝ) ^ n)
        (fun i => (m i : ℝ) / (2 : ℝ) ^ n + (1 : ℝ) / (2 : ℝ) ^ n) = ((2 : ℝ) ^ (n * k))⁻¹) ∧
    volume Q = ENNReal.ofReal (((2 : ℝ) ^ (n * k))⁻¹) ∧
    (∀ {r : ℕ}, n ≤ r →
      (dyadicGrid k r ∩ Q).Finite ∧ (dyadicGrid k r ∩ Q).ncard = 2 ^ ((r - n) * k)) := by
  obtain ⟨m, rfl⟩ := hQ
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos zero_lt_two n
  have hvol_real : cellVolume (fun i : Fin k => (m i : ℝ) / (2 : ℝ) ^ n)
      (fun i : Fin k => (m i : ℝ) / (2 : ℝ) ^ n + (1 : ℝ) / (2 : ℝ) ^ n) =
      ((2 : ℝ) ^ (n * k))⁻¹ := by
    rw [cellVolume_of_le (fun i => by linarith [div_pos zero_lt_one h2n_pos])]
    simp only [add_sub_cancel_left, one_div, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, inv_pow, ← pow_mul]
  refine ⟨⟨m, rfl, hvol_real⟩, ?_, ?_⟩
  · rw [dyadicBox, deltaBox, halfOpenKCell, proposition_2_19_cell_volume, hvol_real]
  · intro r hnr
    let d : ℕ := r - n
    let S : Finset (Fin k → ℤ) :=
      Fintype.piFinset fun i : Fin k =>
        Finset.Ico (m i * (2 : ℤ) ^ d) ((m i + 1) * (2 : ℤ) ^ d)
    have himg : (dyadicCorner (k := k) r '' (S : Set (Fin k → ℤ))) =
        dyadicGrid k r ∩ dyadicBox k n m := by
      ext x
      constructor
      · rintro ⟨m', hm'S, rfl⟩
        refine ⟨⟨m', rfl⟩, ?_⟩
        rw [Finset.mem_coe, Fintype.mem_piFinset] at hm'S
        rw [mem_dyadicBox_iff]
        intro i
        have hi := Finset.mem_Ico.mp (hm'S i)
        have h2r : (0 : ℝ) < (2 : ℝ) ^ r := pow_pos zero_lt_two r
        have hpow_eq : (2 : ℝ) ^ r = (2 : ℝ) ^ n * (2 : ℝ) ^ d := by
          rw [← pow_add, Nat.add_sub_cancel' hnr]
        change (m i : ℝ) / (2 : ℝ) ^ n ≤ (m' i : ℝ) / (2 : ℝ) ^ r ∧
          (m' i : ℝ) / (2 : ℝ) ^ r < ((m i : ℝ) + 1) / (2 : ℝ) ^ n
        refine ⟨?_, ?_⟩
        · rw [div_le_div_iff₀ h2n_pos h2r, hpow_eq]
          have hreal : ((m i * (2 : ℤ) ^ d : ℤ) : ℝ) ≤ (m' i : ℝ) := by exact_mod_cast hi.1
          push_cast at hreal
          nlinarith [h2n_pos]
        · rw [div_lt_div_iff₀ h2r h2n_pos, hpow_eq]
          have hreal : (m' i : ℝ) < (((m i + 1) * (2 : ℤ) ^ d : ℤ) : ℝ) := by exact_mod_cast hi.2
          push_cast at hreal
          nlinarith [h2n_pos]
      · rintro ⟨⟨m', rfl⟩, hm'Q⟩
        refine ⟨m', ?_, rfl⟩
        rw [Finset.mem_coe, Fintype.mem_piFinset]
        intro i
        rw [mem_dyadicBox_iff] at hm'Q
        have hi := hm'Q i
        change (m i : ℝ) / (2 : ℝ) ^ n ≤ (m' i : ℝ) / (2 : ℝ) ^ r ∧
          (m' i : ℝ) / (2 : ℝ) ^ r < ((m i : ℝ) + 1) / (2 : ℝ) ^ n at hi
        have h2r : (0 : ℝ) < (2 : ℝ) ^ r := pow_pos zero_lt_two r
        have hpow_eq : (2 : ℝ) ^ r = (2 : ℝ) ^ n * (2 : ℝ) ^ d := by
          rw [← pow_add, Nat.add_sub_cancel' hnr]
        rw [Finset.mem_Ico]
        refine ⟨?_, ?_⟩
        · have hle := (div_le_div_iff₀ h2n_pos h2r).mp hi.1
          rw [hpow_eq] at hle
          have hreal : ((m i * (2 : ℤ) ^ d : ℤ) : ℝ) ≤ (m' i : ℝ) * (2 : ℝ) ^ n / (2 : ℝ) ^ n := by
            rw [mul_div_cancel_right₀ _ h2n_pos.ne']
            push_cast
            nlinarith
          rw [mul_div_cancel_right₀ _ h2n_pos.ne'] at hreal
          exact_mod_cast hreal
        · have hlt := (div_lt_div_iff₀ h2r h2n_pos).mp hi.2
          rw [hpow_eq] at hlt
          have hreal : (m' i : ℝ) < (((m i + 1) * (2 : ℤ) ^ d : ℤ) : ℝ) := by
            push_cast
            nlinarith
          exact_mod_cast hreal
    have hfin : (dyadicGrid k r ∩ dyadicBox k n m).Finite := by
      rw [← himg]
      exact S.finite_toSet.image _
    refine ⟨hfin, ?_⟩
    rw [← himg, Set.ncard_image_of_injective _ (dyadicCorner_injective k r), Set.ncard_coe_finset]
    simp only [S, Fintype.card_piFinset, Int.card_Ico]
    have hsub : ∀ i : Fin k,
        ((m i + 1) * (2 : ℤ) ^ d - m i * (2 : ℤ) ^ d).toNat = 2 ^ d := by
      intro i
      have hring : (m i + 1) * (2 : ℤ) ^ d - m i * (2 : ℤ) ^ d = ((2 ^ d : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hring, Int.toNat_natCast]
    simp only [hsub, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, d]

/-- `RCA 2.19(d)` (p. 50): every open set `V ⊆ ℝ^k` is a countable union of pairwise disjoint
boxes belonging to `Ω_1 ∪ Ω_2 ∪ Ω_3 ∪ ⋯`. -/
theorem proposition_2_19d {k : ℕ} {V : Set (EuclideanSpace ℝ (Fin k))} (hV : IsOpen V) :
    ∃ 𝒞 : Set (Set (EuclideanSpace ℝ (Fin k))),
      𝒞.Countable ∧
      (∀ Q ∈ 𝒞, ∃ n : ℕ, 1 ≤ n ∧ Q ∈ dyadicCollection k n) ∧
      𝒞.PairwiseDisjoint id ∧
      ⋃₀ 𝒞 = V := by
  classical
  let 𝒞n : ℕ → Set (Set (EuclideanSpace ℝ (Fin k))) := fun n =>
    {Q ∈ dyadicCollection k n |
      Q ⊆ V ∧ ∀ j : ℕ, 1 ≤ j → j < n → ∀ Q' ∈ dyadicCollection k j, ¬ (Q ⊆ Q' ∧ Q' ⊆ V)}
  let 𝒞 : Set (Set (EuclideanSpace ℝ (Fin k))) := ⋃ n ∈ Ici 1, 𝒞n n
  have hcount : 𝒞.Countable := by
    refine (Set.countable_univ.mono (subset_univ (Ici 1))).biUnion fun n _ => ?_
    exact (Set.countable_range (dyadicBox k n)).mono fun Q hQ => hQ.1
  have hmem_level : ∀ Q ∈ 𝒞, ∃ n : ℕ, 1 ≤ n ∧ Q ∈ dyadicCollection k n := by
    intro Q hQ
    obtain ⟨n, hn, hQn⟩ := mem_iUnion₂.mp hQ
    exact ⟨n, hn, hQn.1⟩
  have hdisj : 𝒞.PairwiseDisjoint id := by
    intro Q₁ hQ₁ Q₂ hQ₂ hne
    obtain ⟨n₁, hn₁, hQ₁n⟩ := mem_iUnion₂.mp hQ₁
    obtain ⟨n₂, hn₂, hQ₂n⟩ := mem_iUnion₂.mp hQ₂
    rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
    by_contra hinter
    have hnonempty : (Q₁ ∩ Q₂).Nonempty := Set.nonempty_iff_ne_empty.mpr hinter
    rcases lt_trichotomy n₁ n₂ with hlt | rfl | hgt
    · rcases proposition_2_19b hlt.le hQ₁n.1 hQ₂n.1 with hsub | hempty
      · exact hQ₂n.2.2 n₁ hn₁ hlt Q₁ hQ₁n.1 ⟨hsub, hQ₁n.2.1⟩
      · exact hinter hempty
    · obtain ⟨x, hx₁, hx₂⟩ := hnonempty
      have huniq := (proposition_2_19a k n₁ x).2
      exact hne (huniq.unique ⟨hQ₁n.1, hx₁⟩ ⟨hQ₂n.1, hx₂⟩)
    · rcases proposition_2_19b hgt.le hQ₂n.1 hQ₁n.1 with hsub | hempty
      · exact hQ₁n.2.2 n₂ hn₂ hgt Q₂ hQ₂n.1 ⟨hsub, hQ₂n.2.1⟩
      · exact hinter (by rwa [inter_comm])
  have hunion : ⋃₀ 𝒞 = V := by
    apply subset_antisymm
    · refine sUnion_subset fun Q hQ => ?_
      obtain ⟨n, _, hQn⟩ := mem_iUnion₂.mp hQ
      exact hQn.2.1
    · intro x hxV
      obtain ⟨r, hr_pos, hball⟩ := Metric.isOpen_iff.mp hV x hxV
      have hex : ∃ n : ℕ, 1 ≤ n ∧ ∃ Q ∈ dyadicCollection k n, x ∈ Q ∧ Q ⊆ V := by
        obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hr_pos (Real.sqrt_pos.mpr
          (by positivity : (0 : ℝ) < k + 1))) (by norm_num : (1 / 2 : ℝ) < 1)
        let n := N + 1
        have hn1 : 1 ≤ n := Nat.succ_le_succ (Nat.zero_le N)
        obtain ⟨Q, ⟨hQ_mem, hxQ⟩, _⟩ := (proposition_2_19a k n x).2
        refine ⟨n, hn1, Q, hQ_mem, hxQ, ?_⟩
        intro y hyQ
        apply hball
        rw [Metric.mem_ball, EuclideanSpace.dist_eq]
        obtain ⟨m, rfl⟩ := hQ_mem
        rw [mem_dyadicBox_iff] at hxQ hyQ
        have hcoord : ∀ i : Fin k, dist (y i) (x i) ^ 2 ≤ ((1 : ℝ) / (2 : ℝ) ^ n) ^ 2 := by
          intro i
          rw [Real.dist_eq, sq_abs]
          have h1 := hxQ i
          have h2 := hyQ i
          have hsub1 : -(1 / (2 : ℝ) ^ n) ≤ y i - x i := by
            rw [add_div] at h1
            linarith [h1.2, h2.1]
          have hsub2 : y i - x i ≤ 1 / (2 : ℝ) ^ n := by
            rw [add_div] at h2
            linarith [h1.1, h2.2]
          have habs : |y i - x i| ≤ 1 / (2 : ℝ) ^ n := abs_le.mpr ⟨hsub1, hsub2⟩
          rw [← sq_abs (y i - x i)]
          exact sq_le_sq' (by linarith [abs_nonneg (y i - x i)]) habs
        have hsum : ∑ i : Fin k, dist (y i) (x i) ^ 2 ≤ (k : ℝ) * ((1 : ℝ) / (2 : ℝ) ^ n) ^ 2 := by
          calc
            ∑ i : Fin k, dist (y i) (x i) ^ 2
                ≤ ∑ _i : Fin k, ((1 : ℝ) / (2 : ℝ) ^ n) ^ 2 :=
                  Finset.sum_le_sum fun i _ => hcoord i
            _ = (k : ℝ) * ((1 : ℝ) / (2 : ℝ) ^ n) ^ 2 := by simp
        have h2n_pos : (0 : ℝ) < (1 : ℝ) / (2 : ℝ) ^ n := by positivity
        calc
          √(∑ i : Fin k, dist (y i) (x i) ^ 2)
              ≤ √((k : ℝ) * ((1 : ℝ) / (2 : ℝ) ^ n) ^ 2) := Real.sqrt_le_sqrt hsum
          _ = √(k : ℝ) * ((1 : ℝ) / (2 : ℝ) ^ n) := by
                rw [Real.sqrt_mul (Nat.cast_nonneg k), Real.sqrt_sq h2n_pos.le]
          _ ≤ √((k : ℝ) + 1) * ((1 : ℝ) / (2 : ℝ) ^ N) := by
                have hpow_le : (1 : ℝ) / (2 : ℝ) ^ n ≤ (1 : ℝ) / (2 : ℝ) ^ N := by
                  refine one_div_le_one_div_of_le (pow_pos zero_lt_two N) ?_
                  exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ N)
                exact mul_le_mul (Real.sqrt_le_sqrt (by linarith)) hpow_le h2n_pos.le
                  (Real.sqrt_nonneg _)
          _ < r := by
                have hN' : ((1 : ℝ) / 2) ^ N < r / √((k : ℝ) + 1) := hN
                rw [one_div_pow] at hN'
                have hsqrt_pos : 0 < √((k : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
                have := (lt_div_iff₀ hsqrt_pos).mp hN'
                linarith
      let n₀ := Nat.find hex
      obtain ⟨hn₀, Q₀, hQ₀_col, hxQ₀, hQ₀V⟩ := Nat.find_spec hex
      refine mem_sUnion.mpr ⟨Q₀, mem_iUnion₂.mpr ⟨n₀, hn₀, hQ₀_col, hQ₀V, ?_⟩, hxQ₀⟩
      intro j hj1 hjlt Q' hQ' ⟨hsub, hQ'V⟩
      exact Nat.find_min hex hjlt ⟨hj1, Q', hQ', hsub hxQ₀, hQ'V⟩
  exact ⟨𝒞, hcount, hmem_level, hdisj, hunion⟩

end Exposition2_19

/-!
## 2.23: Exposition — Determinant scale factor (printed pp. 54–55)
-/

section Exposition2_23

/-- Completed Lebesgue `σ`-algebra `𝔐` on `ℝ^k = EuclideanSpace ℝ (Fin k)` (`RCA 2.20` / `2.23`). -/
abbrev lebesgueSigma (k : ℕ) : MeasurableSpace (EuclideanSpace ℝ (Fin k)) :=
  Chapter01.completionSigma (volume : Measure (EuclideanSpace ℝ (Fin k)))

/-- Completed Lebesgue measure `m` on `ℝ^k = EuclideanSpace ℝ (Fin k)` (`RCA 2.20` / `2.23`). -/
def lebesgueMeasure (k : ℕ) : @Measure (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) :=
  Chapter01.completedMeasure (volume : Measure (EuclideanSpace ℝ (Fin k)))

/-- Scale factor `Δ(T) = m(T(Q_0))` of a linear operator `T : ℝ^k → ℝ^k` evaluated on the unit
half-open cube `Q_0 = [0, 1)^k` (`RCA 2.20(e)` / `2.23`, p. 54). -/
def linearScaleFactor {k : ℕ}
    (T : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) : ℝ :=
  (lebesgueMeasure k (T '' halfOpenKCell 0 1)).toReal

/-- `RCA 2.23` (pp. 54–55): for **every** linear operator `T : ℝ^k → ℝ^k` (both nonsingular and
singular) and every completed Lebesgue-measurable set `E ∈ 𝔐`:
1. `Δ(T) = |det T|`;
2. `T(E) ∈ 𝔐` (retaining singular maps via nullness of proper subspaces and nonsingular maps via
   quasi-measure-preserving homeomorphism);
3. `m(T(E)) = |det T| · m(E)` (`0 * ∞ = 0` when `det T = 0`);
4. `det T = 0 ↔ m(range T) = 0`;
5. `Δ(S ∘ T) = Δ(S) · Δ(T)`. -/
theorem proposition_2_23_det_scale_factor {k : ℕ}
    (T : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) :
    linearScaleFactor T = |LinearMap.det T| ∧
    (∀ E : Set (EuclideanSpace ℝ (Fin k)),
      @MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) E →
        @MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) (T '' E) ∧
        lebesgueMeasure k (T '' E) =
          ENNReal.ofReal |LinearMap.det T| * lebesgueMeasure k E) ∧
    (LinearMap.det T = 0 ↔ lebesgueMeasure k (range T) = 0) ∧
    (∀ S : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      linearScaleFactor (S.comp T) = linearScaleFactor S * linearScaleFactor T) := by
  have happly : ∀ A : Set (EuclideanSpace ℝ (Fin k)), lebesgueMeasure k A = volume A :=
    fun A => Measure.completion_apply _ A
  have hunit : volume (halfOpenKCell (0 : Fin k → ℝ) (1 : Fin k → ℝ)) = 1 := by
    rw [halfOpenKCell, proposition_2_19_cell_volume]
    have hcv : cellVolume (0 : Fin k → ℝ) (1 : Fin k → ℝ) = 1 := by
      unfold cellVolume
      simp
    rw [hcv, ENNReal.ofReal_one]
  have hscale : ∀ A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      linearScaleFactor A = |LinearMap.det A| := by
    intro A
    unfold linearScaleFactor
    rw [happly, Measure.addHaar_image_linearMap volume A, hunit, mul_one,
      ENNReal.toReal_ofReal (abs_nonneg _)]
  refine ⟨hscale T, ?_, ?_, ?_⟩
  · intro E hE
    change NullMeasurableSet E volume at hE
    refine ⟨?_, ?_⟩
    · change NullMeasurableSet (T '' E) volume
      by_cases hdet : LinearMap.det T = 0
      · have hsub : volume (LinearMap.range T : Set (EuclideanSpace ℝ (Fin k))) = 0 :=
          Measure.addHaar_submodule volume (LinearMap.range T)
            (LinearMap.range_lt_top_of_det_eq_zero hdet).ne
        exact NullMeasurableSet.of_null (measure_mono_null (image_subset_range T E) hsub)
      · let e : EuclideanSpace ℝ (Fin k) ≃L[ℝ] EuclideanSpace ℝ (Fin k) :=
          (T.equivOfDetNeZero hdet).toContinuousLinearEquiv
        have himg : T '' E = e.symm ⁻¹' E := by
          change (e : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) '' E = e.symm ⁻¹' E
          exact ContinuousLinearEquiv.image_eq_preimage_symm e E
        have hdet_symm : LinearMap.det (e.symm.toLinearMap) ≠ 0 :=
          (LinearEquiv.isUnit_det' e.symm.toLinearEquiv).ne_zero
        have hqmp : Measure.QuasiMeasurePreserving e.symm volume volume :=
          Measure.LinearMap.quasiMeasurePreserving volume e.symm.toLinearMap hdet_symm
        rw [himg]
        exact hE.preimage hqmp
    · rw [happly, happly]
      exact Measure.addHaar_image_linearMap volume T E
  · rw [happly]
    constructor
    · intro hdet
      exact Measure.addHaar_submodule volume (LinearMap.range T)
        (LinearMap.range_lt_top_of_det_eq_zero hdet).ne
    · intro hzero
      by_contra hdet
      have hsub : T '' halfOpenKCell (0 : Fin k → ℝ) 1 ⊆ range T := image_subset_range _ _
      have hzero_img : volume (T '' halfOpenKCell (0 : Fin k → ℝ) 1) = 0 :=
        measure_mono_null hsub hzero
      rw [Measure.addHaar_image_linearMap volume T, hunit, mul_one] at hzero_img
      exact (ENNReal.ofReal_pos.mpr (abs_pos.mpr hdet)).ne' hzero_img
  · intro S
    rw [hscale, hscale, hscale, LinearMap.det_comp, abs_mul]

/-- Matrix and coordinate-space (`Fin k → ℝ`) formulations of `RCA 2.23`: a `k × k` real matrix `A`
acting in the standard orthonormal coordinates scales Lebesgue measure by `|det A|`, and on
`Fin k → ℝ` nonsingular pushforward satisfies `Real.map_linearMap_volume_pi_eq_smul_volume_pi`. -/
theorem proposition_2_23_matrix_and_pi {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) :
    (∀ E : Set (EuclideanSpace ℝ (Fin k)),
      @MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) E →
        @MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k)
          ((Matrix.toLin (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin k) ℝ).toBasis A) '' E) ∧
        lebesgueMeasure k
          ((Matrix.toLin (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin k) ℝ).toBasis A) '' E) =
          ENNReal.ofReal |A.det| * lebesgueMeasure k E) ∧
    (∀ {L : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)}, LinearMap.det L ≠ 0 →
      Measure.map L volume = ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume) := by
  refine ⟨?_, fun hL => Real.map_linearMap_volume_pi_eq_smul_volume_pi hL⟩
  intro E hE
  let T := Matrix.toLin (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin k) ℝ).toBasis A
  have hdet : LinearMap.det T = A.det :=
    LinearMap.det_toLin (EuclideanSpace.basisFun (Fin k) ℝ).toBasis A
  simpa [T, hdet] using (proposition_2_23_det_scale_factor T).2.1 E hE

end Exposition2_23

/-!
## Regularity Hypotheses of 2.14, Regular Approximation (2.17), Vitali–Carathéodory (2.25), and Remarks (2.21)
-/

section RegularityHypotheses2_14

/-- The Borel-containment, compact-finiteness, outer-regularity, and open/finite-measure
inner-regularity clauses 2.14(a–d) (matching `Chapter03.Book214RegularityHypotheses`). -/
def Book214RegularityHypotheses {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (μ : Measure α) : Prop :=
  borel α ≤ ‹MeasurableSpace α› ∧
  (∀ K : Set α, IsCompact K → μ K < ∞) ∧
  (∀ E : Set α, MeasurableSet E → BookOuterRegularSet μ E) ∧
  (∀ U : Set α, IsOpen U → BookInnerRegularSet μ U) ∧
  (∀ E : Set α, MeasurableSet E → μ E < ∞ → BookInnerRegularSet μ E)

theorem Book214RegularityHypotheses.opensMeasurableSpace {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} (hreg : Book214RegularityHypotheses μ) :
    OpensMeasurableSpace α :=
  ⟨hreg.1⟩

theorem Book214RegularityHypotheses.measurableSet_of_isOpen {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} (hreg : Book214RegularityHypotheses μ)
    {U : Set α} (hU : IsOpen U) : MeasurableSet U :=
  hreg.1 _ (MeasurableSpace.measurableSet_generateFrom hU)

theorem Book214RegularityHypotheses.measurableSet_of_isClosed {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} (hreg : Book214RegularityHypotheses μ)
    {F : Set α} (hF : IsClosed F) : MeasurableSet F := by
  simpa using (hreg.measurableSet_of_isOpen hF.isOpen_compl).compl

theorem Book214RegularityHypotheses.exists_isOpen_lt_add {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} (hreg : Book214RegularityHypotheses μ)
    {E : Set α} (hE : MeasurableSet E) (hfin : μ E < ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ V : Set α, E ⊆ V ∧ IsOpen V ∧ μ V < μ E + ε := by
  have hlt : (⨅ (V : Set α) (_ : E ⊆ V) (_ : IsOpen V), μ V) < μ E + ε := by
    rw [← hreg.2.2.1 E hE]
    exact ENNReal.lt_add_right hfin.ne hε
  rcases iInf_lt_iff.mp hlt with ⟨V, hlt⟩
  rcases iInf_lt_iff.mp hlt with ⟨hEV, hlt⟩
  rcases iInf_lt_iff.mp hlt with ⟨hV, hμV⟩
  exact ⟨V, hEV, hV, hμV⟩

theorem Book214RegularityHypotheses.exists_isOpen_diff_lt {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} (hreg : Book214RegularityHypotheses μ)
    {E : Set α} (hE : MeasurableSet E) (hfin : μ E < ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ V : Set α, E ⊆ V ∧ IsOpen V ∧ μ (V \ E) < ε := by
  obtain ⟨V, hEV, hV, hμV⟩ := hreg.exists_isOpen_lt_add hE hfin hε
  refine ⟨V, hEV, hV, ?_⟩
  have hadd : μ E + μ (V \ E) = μ V := by
    rw [← measure_union disjoint_sdiff_self_right ((hreg.measurableSet_of_isOpen hV).diff hE),
      union_sdiff_cancel hEV]
  exact (ENNReal.add_lt_add_iff_left hfin.ne).mp (hadd.trans_lt hμV)

theorem Book214RegularityHypotheses.exists_isCompact_lt_add {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} (hreg : Book214RegularityHypotheses μ)
    {E : Set α} (hE : MeasurableSet E) (hfin : μ E < ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set α, K ⊆ E ∧ IsCompact K ∧ μ E < μ K + ε := by
  by_cases h0 : μ E = 0
  · refine ⟨∅, empty_subset E, isCompact_empty, ?_⟩
    rwa [measure_empty, h0, zero_add, pos_iff_ne_zero]
  · have hlt : μ E - ε < ⨆ (K : Set α) (_ : K ⊆ E) (_ : IsCompact K), μ K := by
      rw [← hreg.2.2.2.2 E hE hfin]
      exact ENNReal.sub_lt_self hfin.ne h0 hε
    rcases lt_iSup_iff.mp hlt with ⟨K, hlt⟩
    rcases lt_iSup_iff.mp hlt with ⟨hKE, hlt⟩
    rcases lt_iSup_iff.mp hlt with ⟨hK, hrK⟩
    exact ⟨K, hKE, hK, ENNReal.lt_add_of_sub_lt_right (Or.inl hfin.ne) hrK⟩

theorem Book214RegularityHypotheses.exists_isCompact_diff_lt {α : Type*} [TopologicalSpace α]
    [T2Space α] [MeasurableSpace α] {μ : Measure α} (hreg : Book214RegularityHypotheses μ)
    {E : Set α} (hE : MeasurableSet E) (hfin : μ E < ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set α, K ⊆ E ∧ IsCompact K ∧ μ (E \ K) < ε := by
  obtain ⟨K, hKE, hK, hμK⟩ := hreg.exists_isCompact_lt_add hE hfin hε
  refine ⟨K, hKE, hK, ?_⟩
  have hK_meas : MeasurableSet K := hreg.measurableSet_of_isClosed hK.isClosed
  have hK_fin : μ K < ∞ := (measure_mono hKE).trans_lt hfin
  have hadd : μ K + μ (E \ K) = μ E := by
    rw [← measure_union disjoint_sdiff_self_right (hE.diff hK_meas), union_sdiff_cancel hKE]
  exact (ENNReal.add_lt_add_iff_left hK_fin.ne).mp (hadd.trans_lt hμK)

end RegularityHypotheses2_14

/-!
## 2.17: Regular approximation (printed p. 48)
-/

section RegularApproximation2_17

private theorem exists_isOpen_diff_lt_of_sigmaCompact {α : Type*} [TopologicalSpace α]
    [T2Space α] [SigmaCompactSpace α] [MeasurableSpace α] {μ : Measure α}
    (hreg : Book214RegularityHypotheses μ) {E : Set α} (hE : MeasurableSet E)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ V : Set α, E ⊆ V ∧ IsOpen V ∧ μ (V \ E) < δ := by
  rcases ENNReal.exists_pos_sum_of_countable' hδ ℕ with ⟨η, ηpos, hη⟩
  let K : ℕ → Set α := compactCovering α
  have hV_ex : ∀ n : ℕ, ∃ Vn : Set α, E ∩ K n ⊆ Vn ∧ IsOpen Vn ∧ μ (Vn \ (E ∩ K n)) < η n := by
    intro n
    have hKn_compact : IsCompact (K n) := isCompact_compactCovering α n
    have hKn_meas : MeasurableSet (K n) := hreg.measurableSet_of_isClosed hKn_compact.isClosed
    have hKn_fin : μ (E ∩ K n) < ∞ :=
      (measure_mono inter_subset_right).trans_lt (hreg.2.1 (K n) hKn_compact)
    exact hreg.exists_isOpen_diff_lt (hE.inter hKn_meas) hKn_fin (ηpos n).ne'
  choose Vn hEVn hVn_open hVn_lt using hV_ex
  refine ⟨⋃ n, Vn n, ?_, isOpen_iUnion hVn_open, ?_⟩
  · intro x hx
    have hx_univ : x ∈ ⋃ n, K n := by rw [iUnion_compactCovering]; trivial
    rcases mem_iUnion.mp hx_univ with ⟨n, hxn⟩
    exact mem_iUnion.mpr ⟨n, hEVn n ⟨hx, hxn⟩⟩
  · have hdiff_sub : (⋃ n, Vn n) \ E ⊆ ⋃ n, (Vn n \ (E ∩ K n)) := by
      intro x hx
      rcases mem_iUnion.mp hx.1 with ⟨n, hxn⟩
      exact mem_iUnion.mpr ⟨n, hxn, fun h => hx.2 h.1⟩
    calc
      μ ((⋃ n, Vn n) \ E) ≤ μ (⋃ n, (Vn n \ (E ∩ K n))) := measure_mono hdiff_sub
      _ ≤ ∑' n, μ (Vn n \ (E ∩ K n)) := measure_iUnion_le _
      _ ≤ ∑' n, η n := ENNReal.tsum_le_tsum fun n => (hVn_lt n).le
      _ < δ := hη

/-- **Theorem 2.17** (Regular approximation on locally compact `σ`-compact Hausdorff spaces,
`RCA` p. 48): if `(𝔐, μ)` satisfies the regularity properties 2.14(a–d) (`Book214RegularityHypotheses μ`),
then:
- (a) for every `E ∈ 𝔐` and `ε > 0`, there exist closed `F` and open `V` with `F ⊆ E ⊆ V` and
  `μ(V \ F) < ε`;
- (b) every `E ∈ 𝔐` is both outer regular and inner regular, and restricting `μ` to `borel α`
  yields a regular Borel measure in Rudin's sense (`BookRegularBorelMeasure`);
- (c) for every `E ∈ 𝔐`, there exist an `F_σ`-set `A` and a `G_δ`-set `B` with `A ⊆ E ⊆ B` and
  `μ(B \ A) = 0`. -/
theorem theorem_2_17 {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
    [SigmaCompactSpace α] [MeasurableSpace α] {μ : Measure α}
    (hreg : Book214RegularityHypotheses μ) :
    (∀ E : Set α, MeasurableSet E → ∀ {ε : ℝ}, 0 < ε →
      ∃ F V : Set α, IsClosed F ∧ IsOpen V ∧ F ⊆ E ∧ E ⊆ V ∧
        μ (V \ F) < ENNReal.ofReal ε) ∧
    ((∀ E : Set α, MeasurableSet E → BookOuterRegularSet μ E ∧ BookInnerRegularSet μ E) ∧
      BookRegularBorelMeasure (μ.trim hreg.1)) ∧
    (∀ E : Set α, MeasurableSet E →
      ∃ A B : Set α, Chapter01.IsFSigma A ∧ IsGδ B ∧ A ⊆ E ∧ E ⊆ B ∧ μ (B \ A) = 0) := by
  have hpart_a : ∀ E : Set α, MeasurableSet E → ∀ {ε : ℝ}, 0 < ε →
      ∃ F V : Set α, IsClosed F ∧ IsOpen V ∧ F ⊆ E ∧ E ⊆ V ∧
        μ (V \ F) < ENNReal.ofReal ε := by
    intro E hE ε hε
    have hδ_pos : ENNReal.ofReal (ε / 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
    obtain ⟨V, hEV, hV, hVE⟩ :=
      exists_isOpen_diff_lt_of_sigmaCompact hreg hE hδ_pos
    obtain ⟨W, hEcW, hW, hWEc⟩ :=
      exists_isOpen_diff_lt_of_sigmaCompact hreg hE.compl hδ_pos
    let F : Set α := Wᶜ
    have hF_closed : IsClosed F := hW.isClosed_compl
    have hFE : F ⊆ E := fun x hx => by_contra fun hxE => hx (hEcW hxE)
    have hWEc_eq : W \ Eᶜ = E \ F := by
      ext x
      simp [F, and_comm]
    have hVF_sub : V \ F ⊆ (V \ E) ∪ (E \ F) := by
      intro x hx
      by_cases hxE : x ∈ E
      · exact Or.inr ⟨hxE, hx.2⟩
      · exact Or.inl ⟨hx.1, hxE⟩
    refine ⟨F, V, hF_closed, hV, hFE, hEV, ?_⟩
    calc
      μ (V \ F) ≤ μ ((V \ E) ∪ (E \ F)) := measure_mono hVF_sub
      _ ≤ μ (V \ E) + μ (E \ F) := measure_union_le _ _
      _ = μ (V \ E) + μ (W \ Eᶜ) := by rw [hWEc_eq]
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hVE hWEc
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
  have hpart_b_all : ∀ E : Set α, MeasurableSet E →
      BookOuterRegularSet μ E ∧ BookInnerRegularSet μ E := by
    intro E hE
    refine ⟨hreg.2.2.1 E hE, ?_⟩
    have huniv_σ : BookSigmaFiniteSet μ univ :=
      proposition_2_16_sigmaFinite μ hreg.2.1 isSigmaCompact_univ
    obtain ⟨C, hC_fin, hC_cov⟩ := huniv_σ
    have hE_σ : BookSigmaFiniteSet μ E := by
      refine ⟨fun n => E ∩ C n,
        fun n => (measure_mono inter_subset_right).trans_lt (hC_fin n), ?_⟩
      rw [← inter_iUnion, hC_cov, inter_univ]
    exact proposition_2_16_innerRegular μ hreg.2.2.2.2 hE hE_σ
  refine ⟨hpart_a, ⟨hpart_b_all, ?_⟩, ?_⟩
  · intro E hEb
    have hE_meas : MeasurableSet E := hreg.1 E hEb
    obtain ⟨hout, hinn⟩ := hpart_b_all E hE_meas
    refine ⟨?_, ?_⟩
    · unfold BookOuterRegularSet at hout ⊢
      rw [trim_measurableSet_eq hreg.1 hEb, hout]
      refine le_antisymm
        (le_iInf fun V => le_iInf fun hEV => le_iInf fun hV => by
          have hVb : @MeasurableSet α (borel α) V := MeasurableSpace.measurableSet_generateFrom hV
          rw [trim_measurableSet_eq hreg.1 hVb]
          exact iInf_le_of_le V (iInf_le_of_le hEV (iInf_le_of_le hV le_rfl)))
        (le_iInf fun V => le_iInf fun hEV => le_iInf fun hV => by
          have hVb : @MeasurableSet α (borel α) V := MeasurableSpace.measurableSet_generateFrom hV
          rw [← trim_measurableSet_eq hreg.1 hVb]
          exact iInf_le_of_le V (iInf_le_of_le hEV (iInf_le_of_le hV le_rfl)))
    · unfold BookInnerRegularSet at hinn ⊢
      rw [trim_measurableSet_eq hreg.1 hEb, hinn]
      refine le_antisymm
        (iSup_le fun K => iSup_le fun hKE => iSup_le fun hK => by
          have hKb : @MeasurableSet α (borel α) K :=
            @MeasurableSet.of_compl α _ (borel α)
              (MeasurableSpace.measurableSet_generateFrom hK.isClosed.isOpen_compl)
          rw [← trim_measurableSet_eq hreg.1 hKb]
          exact le_iSup_of_le K (le_iSup_of_le hKE (le_iSup_of_le hK le_rfl)))
        (iSup_le fun K => iSup_le fun hKE => iSup_le fun hK => by
          have hKb : @MeasurableSet α (borel α) K :=
            @MeasurableSet.of_compl α _ (borel α)
              (MeasurableSpace.measurableSet_generateFrom hK.isClosed.isOpen_compl)
          rw [trim_measurableSet_eq hreg.1 hKb]
          exact le_iSup_of_le K (le_iSup_of_le hKE (le_iSup_of_le hK le_rfl)))
  · intro E hE
    have hex : ∀ j : ℕ, ∃ F V : Set α, IsClosed F ∧ IsOpen V ∧ F ⊆ E ∧ E ⊆ V ∧
        μ (V \ F) < ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
      intro j
      exact hpart_a E hE (by positivity)
    choose F V hF hV hFE hEV hVF using hex
    refine ⟨⋃ j, F j, ⋂ j, V j, ⟨F, hF, rfl⟩,
      isGδ_iff_eq_iInter_nat.mpr ⟨V, hV, rfl⟩, iUnion_subset hFE, subset_iInter hEV, ?_⟩
    refine le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_) zero_le
    rw [zero_add]
    by_cases hδ_top : δ = ∞
    · rw [hδ_top]; exact le_top
    · have hδ_real_pos : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδ_top
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ_real_pos
      have hsub : (⋂ i, V i) \ (⋃ i, F i) ⊆ V j \ F j := by
        intro x hx
        exact ⟨mem_iInter.mp hx.1 j, fun hxj => hx.2 (mem_iUnion.mpr ⟨j, hxj⟩)⟩
      calc
        μ ((⋂ i, V i) \ (⋃ i, F i)) ≤ μ (V j \ F j) := measure_mono hsub
        _ ≤ ENNReal.ofReal (1 / ((j : ℝ) + 1)) := (hVF j).le
        _ ≤ ENNReal.ofReal δ.toReal := ENNReal.ofReal_le_ofReal hj.le
        _ = δ := ENNReal.ofReal_toReal hδ_top

/-- **Corollary to Theorem 2.17** (`RCA` p. 48): under the hypotheses of Theorem 2.17, every
`E ∈ 𝔐` is the disjoint union of an `F_σ`-set and a measurable set of measure `0`. -/
theorem theorem_2_17_corollary {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
    [SigmaCompactSpace α] [MeasurableSpace α] {μ : Measure α}
    (hreg : Book214RegularityHypotheses μ) {E : Set α} (hE : MeasurableSet E) :
    ∃ A N : Set α, Chapter01.IsFSigma A ∧ MeasurableSet N ∧ μ N = 0 ∧
      Disjoint A N ∧ E = A ∪ N := by
  obtain ⟨A, B, hA, _, hAE, hEB, hBA⟩ := (theorem_2_17 hreg).2.2 E hE
  have hA_meas : MeasurableSet A := by
    rcases hA with ⟨F, hF, rfl⟩
    exact MeasurableSet.iUnion fun n => hreg.measurableSet_of_isClosed (hF n)
  refine ⟨A, E \ A, hA, hE.diff hA_meas, ?_, disjoint_sdiff_self_right,
    (union_sdiff_cancel hAE).symm⟩
  exact measure_mono_null (sdiff_subset_sdiff_left hEB) hBA

end RegularApproximation2_17

/-!
## 2.25: Vitali–Carathéodory Theorem (printed p. 56)
-/

section VitaliCaratheodory2_25

open scoped NNReal

private theorem simpleFunc_exists_le_lsc {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : Measure α} (hreg : Book214RegularityHypotheses μ) (f : SimpleFunc α ℝ≥0) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) :
    ∃ g : α → ℝ≥0, (∀ x, f x ≤ g x) ∧ LowerSemicontinuous g ∧
      (∫⁻ x, (g x : ℝ≥0∞) ∂μ) ≤ (∫⁻ x, (f x : ℝ≥0∞) ∂μ) + ε := by
  have : OpensMeasurableSpace α := hreg.opensMeasurableSpace
  induction f using MeasureTheory.SimpleFunc.induction generalizing ε with
  | @const c s hs =>
    let f₀ := SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.const α 0)
    by_cases htop : (∫⁻ x, (f₀ x : ℝ≥0∞) ∂μ) = ∞
    · refine ⟨fun _ => c, fun x => ?_, lowerSemicontinuous_const, ?_⟩
      · simp only [SimpleFunc.coe_piecewise, SimpleFunc.coe_const, SimpleFunc.const_zero,
          SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
        exact Set.indicator_le_self _ _ _
      · change (∫⁻ x, (c : ℝ≥0∞) ∂μ) ≤ (∫⁻ x, (f₀ x : ℝ≥0∞) ∂μ) + ε
        rw [htop, top_add]
        exact le_top
    by_cases hc : c = 0
    · refine ⟨fun _ => 0, ?_, lowerSemicontinuous_const, ?_⟩
      · intro x
        simp [hc]
      · simp
    have hs_lt_top : μ s < ∞ := by
      have hlint : (∫⁻ x, (f₀ x : ℝ≥0∞) ∂μ) = (c : ℝ≥0∞) * μ s := by
        simp [f₀, hs, Set.piecewise_eq_indicator, ENNReal.coe_indicator, lintegral_indicator]
      rw [hlint] at htop
      have hc_enn : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hc
      exact lt_top_iff_ne_top.mpr fun hμs =>
        htop (ENNReal.mul_eq_top.mpr (Or.inl ⟨hc_enn, hμs⟩))
    have hdiv_ne : ε / (c : ℝ≥0∞) ≠ 0 :=
      (ENNReal.div_pos_iff.mpr ⟨hε, ENNReal.coe_ne_top⟩).ne'
    obtain ⟨u, hsu, hu_open, hμu⟩ := hreg.exists_isOpen_lt_add hs hs_lt_top hdiv_ne
    refine ⟨u.indicator fun _ => c, fun x => ?_, hu_open.lowerSemicontinuous_indicator (by simp), ?_⟩
    · simp only [SimpleFunc.coe_piecewise, SimpleFunc.coe_const, SimpleFunc.const_zero,
        SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
      exact Set.indicator_le_indicator_of_subset hsu (fun _ => zero_le) x
    · have hmul : (c : ℝ≥0∞) * μ u ≤ (c : ℝ≥0∞) * μ s + ε := by
        calc
          (c : ℝ≥0∞) * μ u ≤ (c : ℝ≥0∞) * (μ s + ε / (c : ℝ≥0∞)) :=
            mul_le_mul_of_nonneg_left hμu.le zero_le
          _ = (c : ℝ≥0∞) * μ s + (c : ℝ≥0∞) * (ε / (c : ℝ≥0∞)) := mul_add _ _ _
          _ = (c : ℝ≥0∞) * μ s + ε := by
            rw [ENNReal.mul_div_cancel (by simpa using hc) ENNReal.coe_ne_top]
      simpa [hs, hu_open.measurableSet, Set.piecewise_eq_indicator, ENNReal.coe_indicator,
        lintegral_indicator] using hmul
  | @add f₁ f₂ _ h₁ h₂ =>
    have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
    rcases h₁ hε2 with ⟨g₁, hfg₁, hg₁_lsc, hg₁_int⟩
    rcases h₂ hε2 with ⟨g₂, hfg₂, hg₂_lsc, hg₂_int⟩
    refine ⟨fun x => g₁ x + g₂ x, fun x => add_le_add (hfg₁ x) (hfg₂ x), hg₁_lsc.add hg₂_lsc, ?_⟩
    simp only [SimpleFunc.coe_add, ENNReal.coe_add, Pi.add_apply]
    rw [lintegral_add_left f₁.measurable.coe_nnreal_ennreal,
      lintegral_add_left hg₁_lsc.measurable.coe_nnreal_ennreal]
    calc
      (∫⁻ x, (g₁ x : ℝ≥0∞) ∂μ) + (∫⁻ x, (g₂ x : ℝ≥0∞) ∂μ)
          ≤ ((∫⁻ x, (f₁ x : ℝ≥0∞) ∂μ) + ε / 2) + ((∫⁻ x, (f₂ x : ℝ≥0∞) ∂μ) + ε / 2) :=
        add_le_add hg₁_int hg₂_int
      _ = ((∫⁻ x, (f₁ x : ℝ≥0∞) ∂μ) + (∫⁻ x, (f₂ x : ℝ≥0∞) ∂μ)) + (ε / 2 + ε / 2) := by ac_rfl
      _ = ((∫⁻ x, (f₁ x : ℝ≥0∞) ∂μ) + (∫⁻ x, (f₂ x : ℝ≥0∞) ∂μ)) + ε := by
        rw [ENNReal.add_halves]

private theorem exists_le_lsc_lintegral {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : Measure α} (hreg : Book214RegularityHypotheses μ) (f : α → ℝ≥0∞) (hf : Measurable f)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : α → ℝ≥0∞, (∀ x, f x ≤ g x) ∧ LowerSemicontinuous g ∧
      (∫⁻ x, g x ∂μ) ≤ (∫⁻ x, f x ∂μ) + ε := by
  have : OpensMeasurableSpace α := hreg.opensMeasurableSpace
  rcases ENNReal.exists_pos_sum_of_countable' hε ℕ with ⟨δ, δpos, hδ⟩
  have hex : ∀ n : ℕ, ∃ g : α → ℝ≥0,
      (∀ x, SimpleFunc.eapproxDiff f n x ≤ g x) ∧ LowerSemicontinuous g ∧
        (∫⁻ x, (g x : ℝ≥0∞) ∂μ) ≤ (∫⁻ x, (SimpleFunc.eapproxDiff f n x : ℝ≥0∞) ∂μ) + δ n :=
    fun n => simpleFunc_exists_le_lsc hreg (SimpleFunc.eapproxDiff f n) (δpos n).ne'
  choose g hfg hg_lsc hg_int using hex
  refine ⟨fun x => ∑' n, (g n x : ℝ≥0∞), fun x => ?_, ?_, ?_⟩
  · rw [← SimpleFunc.tsum_eapproxDiff f hf]
    exact ENNReal.tsum_le_tsum fun n => ENNReal.coe_le_coe.mpr (hfg n x)
  · refine lowerSemicontinuous_tsum fun n => ?_
    exact ENNReal.continuous_coe.comp_lowerSemicontinuous (hg_lsc n) fun _ _ hxy =>
      ENNReal.coe_le_coe.mpr hxy
  · calc
      (∫⁻ x, ∑' n, (g n x : ℝ≥0∞) ∂μ)
          = ∑' n, ∫⁻ x, (g n x : ℝ≥0∞) ∂μ := by
        rw [lintegral_tsum fun n => (hg_lsc n).measurable.coe_nnreal_ennreal.aemeasurable]
      _ ≤ ∑' n, ((∫⁻ x, (SimpleFunc.eapproxDiff f n x : ℝ≥0∞) ∂μ) + δ n) :=
        ENNReal.tsum_le_tsum hg_int
      _ = (∑' n, ∫⁻ x, (SimpleFunc.eapproxDiff f n x : ℝ≥0∞) ∂μ) + ∑' n, δ n := ENNReal.tsum_add
      _ ≤ (∫⁻ x, f x ∂μ) + ε := by
        refine add_le_add ?_ hδ.le
        rw [← lintegral_tsum fun n =>
          (SimpleFunc.measurable _).coe_nnreal_ennreal.aemeasurable]
        simp_rw [SimpleFunc.tsum_eapproxDiff f hf, le_rfl]

private theorem simpleFunc_exists_usc_le {α : Type*} [TopologicalSpace α] [T2Space α]
    [MeasurableSpace α] {μ : Measure α} (hreg : Book214RegularityHypotheses μ)
    (f : SimpleFunc α ℝ≥0) (hf_int : (∫⁻ x, (f x : ℝ≥0∞) ∂μ) ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : α → ℝ≥0, (∀ x, g x ≤ f x) ∧ UpperSemicontinuous g ∧
      (∫⁻ x, (f x : ℝ≥0∞) ∂μ) ≤ (∫⁻ x, (g x : ℝ≥0∞) ∂μ) + ε := by
  have : OpensMeasurableSpace α := hreg.opensMeasurableSpace
  induction f using MeasureTheory.SimpleFunc.induction generalizing ε with
  | @const c s hs =>
    by_cases hc : c = 0
    · refine ⟨fun _ => 0, fun _ => by simp [hc], upperSemicontinuous_const, by simp [hc]⟩
    have hs_lt_top : μ s < ∞ := by
      have hlint : (∫⁻ x, ((SimpleFunc.piecewise s hs (SimpleFunc.const α c)
          (SimpleFunc.const α 0)) x : ℝ≥0∞) ∂μ) = (c : ℝ≥0∞) * μ s := by
        simp [hs, Set.piecewise_eq_indicator, ENNReal.coe_indicator, lintegral_indicator]
      rw [hlint] at hf_int
      have hc_enn : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hc
      exact lt_top_iff_ne_top.mpr fun hμs =>
        hf_int (ENNReal.mul_eq_top.mpr (Or.inl ⟨hc_enn, hμs⟩))
    have hdiv_ne : ε / (c : ℝ≥0∞) ≠ 0 :=
      (ENNReal.div_pos_iff.mpr ⟨hε, ENNReal.coe_ne_top⟩).ne'
    obtain ⟨K, hKs, hK_compact, hμK⟩ := hreg.exists_isCompact_lt_add hs hs_lt_top hdiv_ne
    refine ⟨K.indicator fun _ => c, fun x => ?_,
      hK_compact.isClosed.upperSemicontinuous_indicator (by simp), ?_⟩
    · simp only [SimpleFunc.coe_piecewise, SimpleFunc.coe_const, SimpleFunc.const_zero,
        SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
      exact Set.indicator_le_indicator_of_subset hKs (fun _ => zero_le) x
    · have hmul : (c : ℝ≥0∞) * μ s ≤ (c : ℝ≥0∞) * μ K + ε := by
        calc
          (c : ℝ≥0∞) * μ s ≤ (c : ℝ≥0∞) * (μ K + ε / (c : ℝ≥0∞)) :=
            mul_le_mul_of_nonneg_left hμK.le zero_le
          _ = (c : ℝ≥0∞) * μ K + (c : ℝ≥0∞) * (ε / (c : ℝ≥0∞)) := mul_add _ _ _
          _ = (c : ℝ≥0∞) * μ K + ε := by
            rw [ENNReal.mul_div_cancel (by simpa using hc) ENNReal.coe_ne_top]
      simpa [hs, hK_compact.isClosed.measurableSet, Set.piecewise_eq_indicator,
        ENNReal.coe_indicator, lintegral_indicator] using hmul
  | @add f₁ f₂ _ h₁ h₂ =>
    have hsum_ne : ((∫⁻ x, (f₁ x : ℝ≥0∞) ∂μ) + (∫⁻ x, (f₂ x : ℝ≥0∞) ∂μ)) ≠ ∞ := by
      rwa [← lintegral_add_left f₁.measurable.coe_nnreal_ennreal]
    have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
    rcases h₁ (ENNReal.add_ne_top.mp hsum_ne).1 hε2 with ⟨g₁, hgf₁, hg₁_usc, hg₁_int⟩
    rcases h₂ (ENNReal.add_ne_top.mp hsum_ne).2 hε2 with ⟨g₂, hgf₂, hg₂_usc, hg₂_int⟩
    refine ⟨fun x => g₁ x + g₂ x, fun x => add_le_add (hgf₁ x) (hgf₂ x), hg₁_usc.add hg₂_usc, ?_⟩
    simp only [SimpleFunc.coe_add, ENNReal.coe_add, Pi.add_apply]
    rw [lintegral_add_left f₁.measurable.coe_nnreal_ennreal,
      lintegral_add_left hg₁_usc.measurable.coe_nnreal_ennreal]
    calc
      (∫⁻ x, (f₁ x : ℝ≥0∞) ∂μ) + (∫⁻ x, (f₂ x : ℝ≥0∞) ∂μ)
          ≤ ((∫⁻ x, (g₁ x : ℝ≥0∞) ∂μ) + ε / 2) + ((∫⁻ x, (g₂ x : ℝ≥0∞) ∂μ) + ε / 2) :=
        add_le_add hg₁_int hg₂_int
      _ = ((∫⁻ x, (g₁ x : ℝ≥0∞) ∂μ) + (∫⁻ x, (g₂ x : ℝ≥0∞) ∂μ)) + (ε / 2 + ε / 2) := by ac_rfl
      _ = ((∫⁻ x, (g₁ x : ℝ≥0∞) ∂μ) + (∫⁻ x, (g₂ x : ℝ≥0∞) ∂μ)) + ε := by
        rw [ENNReal.add_halves]

private theorem exists_bounded_usc_le_lintegral {α : Type*} [TopologicalSpace α] [T2Space α]
    [MeasurableSpace α] {μ : Measure α} (hreg : Book214RegularityHypotheses μ)
    (f : α → ℝ≥0) (hf_int : (∫⁻ x, (f x : ℝ≥0∞) ∂μ) ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : α → ℝ≥0, (∃ M : ℝ≥0, ∀ x, g x ≤ M) ∧ (∀ x, g x ≤ f x) ∧ UpperSemicontinuous g ∧
      (∫⁻ x, (f x : ℝ≥0∞) ∂μ) ≤ (∫⁻ x, (g x : ℝ≥0∞) ∂μ) + ε := by
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  obtain ⟨fs, hfs_le, hfs_int⟩ :
      ∃ fs : SimpleFunc α ℝ≥0, (∀ x, fs x ≤ f x) ∧
        (∫⁻ x, (f x : ℝ≥0∞) ∂μ) ≤ (∫⁻ x, (fs x : ℝ≥0∞) ∂μ) + ε / 2 := by
    have hlt := ENNReal.lt_add_right hf_int hε2
    conv_rhs at hlt => rw [lintegral_eq_nnreal (fun x => (f x : ℝ≥0∞)) μ]
    rw [ENNReal.biSup_add' ⟨0, fun _ => by simp⟩] at hlt
    simp only [lt_iSup_iff] at hlt
    rcases hlt with ⟨fs, hfs_le, hfs_lt⟩
    refine ⟨fs, fun x => ENNReal.coe_le_coe.mp (hfs_le x), ?_⟩
    have heq : (fs.map ((↑) : ℝ≥0 → ℝ≥0∞)).lintegral μ = ∫⁻ x, (fs x : ℝ≥0∞) ∂μ := by
      rw [← SimpleFunc.lintegral_eq_lintegral]
      rfl
    rw [← heq]
    exact hfs_lt.le
  have hfs_ne_top : (∫⁻ x, (fs x : ℝ≥0∞) ∂μ) ≠ ∞ :=
    ne_top_of_le_ne_top hf_int (lintegral_mono fun x => ENNReal.coe_le_coe.mpr (hfs_le x))
  obtain ⟨g, hg_le_fs, hg_usc, hg_int⟩ := simpleFunc_exists_usc_le hreg fs hfs_ne_top hε2
  refine ⟨g, ⟨fs.range.sup id, fun x => (hg_le_fs x).trans
      (Finset.le_sup (f := id) (fs.mem_range_self x))⟩,
    fun x => (hg_le_fs x).trans (hfs_le x), hg_usc, ?_⟩
  calc
    (∫⁻ x, (f x : ℝ≥0∞) ∂μ) ≤ (∫⁻ x, (fs x : ℝ≥0∞) ∂μ) + ε / 2 := hfs_int
    _ ≤ ((∫⁻ x, (g x : ℝ≥0∞) ∂μ) + ε / 2) + ε / 2 := add_le_add hg_int le_rfl
    _ = (∫⁻ x, (g x : ℝ≥0∞) ∂μ) + ε := by rw [add_assoc, ENNReal.add_halves]

/-- **Theorem 2.25** (Vitali–Carathéodory Theorem, `RCA` p. 56): suppose `f : α → ℝ` is in `L^1(μ)`
on a locally compact Hausdorff space `α` whose measure `μ` satisfies the regularity properties
2.14(a–d) (`Book214RegularityHypotheses μ`), with **no** `σ`-finiteness or `[BorelSpace α]`
assumption. Then for every `ε > 0`, there exist `u, v : α → [-∞, +∞]` (`EReal`) such that `u` is
upper semicontinuous and bounded above, `v` is lower semicontinuous and bounded below, `u ≤ f ≤ v`
pointwise everywhere on `α`, `u` and `v` are `μ`-integrable, and `∫_α (v - u) dμ < ε`. -/
theorem theorem_2_25 {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
    [MeasurableSpace α] {μ : Measure α} (hreg : Book214RegularityHypotheses μ)
    (f : α → ℝ) (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u v : α → EReal,
      BookUpperSemicontinuous u ∧
      BookLowerSemicontinuous v ∧
      (∃ M : ℝ, ∀ x, u x ≤ (M : EReal)) ∧
      (∃ M : ℝ, ∀ x, (M : EReal) ≤ v x) ∧
      (∀ x, u x ≤ (f x : EReal) ∧ (f x : EReal) ≤ v x) ∧
      Integrable (fun x => (u x).toReal) μ ∧
      Integrable (fun x => (v x).toReal) μ ∧
      (∫⁻ x, (v x - u x).toENNReal ∂μ) < ENNReal.ofReal ε ∧
      ∫ x, ((v x).toReal - (u x).toReal) ∂μ < ε := by
  have : OpensMeasurableSpace α := hreg.opensMeasurableSpace
  let f₀ : α → ℝ := hf.aemeasurable.mk f
  have hf₀_meas : Measurable f₀ := hf.aemeasurable.measurable_mk
  have hf_ae : f =ᵐ[μ] f₀ := hf.aemeasurable.ae_eq_mk
  have hf₀_int : Integrable f₀ μ := hf.congr hf_ae
  let D : Set α := {x | f x ≠ f₀ x}
  have hD_zero : μ D = 0 := hf_ae
  let N : Set α := toMeasurable μ D
  have hN_meas : MeasurableSet N := measurableSet_toMeasurable μ D
  have hDN : D ⊆ N := subset_toMeasurable μ D
  have hN_zero : μ N = 0 := by rw [measure_toMeasurable]; exact hD_zero
  let δ : ℝ≥0 := ⟨ε / 7, by positivity⟩
  have hδ_pos : (0 : ℝ) < (δ : ℝ) := by
    change 0 < ε / 7
    positivity
  have hδ_enn_ne : (δ : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (NNReal.coe_pos.mp hδ_pos).ne'
  -- Build LSC `g_null : α → ℝ≥0∞` equal to `⊤` on `N` with `lintegral ≤ δ`.
  rcases ENNReal.exists_pos_sum_of_countable' hδ_enn_ne ℕ with ⟨η, ηpos, hη⟩
  have hW_ex : ∀ k : ℕ, ∃ W : Set α, N ⊆ W ∧ IsOpen W ∧ μ W < η k := by
    intro k
    obtain ⟨W, hNW, hW_open, hμW⟩ :=
      hreg.exists_isOpen_lt_add hN_meas (by simp [hN_zero]) (ηpos k).ne'
    exact ⟨W, hNW, hW_open, by simpa [hN_zero] using hμW⟩
  choose W hNW hW_open hμW using hW_ex
  let g_null : α → ℝ≥0∞ := fun x => ∑' k : ℕ, (W k).indicator (fun _ => (1 : ℝ≥0∞)) x
  have hg_null_lsc : LowerSemicontinuous g_null := by
    refine lowerSemicontinuous_tsum fun k => ?_
    have hlsc_nn : LowerSemicontinuous ((W k).indicator fun _ => (1 : ℝ≥0)) :=
      (hW_open k).lowerSemicontinuous_indicator zero_le_one
    have hfn_eq : ((W k).indicator fun _ => (1 : ℝ≥0∞)) =
        (((↑) : ℝ≥0 → ℝ≥0∞) ∘ (W k).indicator fun _ => (1 : ℝ≥0)) := by
      ext x
      by_cases hx : x ∈ W k <;> simp [hx]
    rw [hfn_eq]
    exact ENNReal.continuous_coe.comp_lowerSemicontinuous hlsc_nn
      (fun _ _ hxy => ENNReal.coe_le_coe.mpr hxy)
  have hg_null_top : ∀ x ∈ N, g_null x = ∞ := by
    intro x hx
    have hconst : (fun k : ℕ => (W k).indicator (fun _ => (1 : ℝ≥0∞)) x) = fun _ => 1 := by
      ext k
      exact Set.indicator_of_mem (hNW k hx) _
    dsimp only [g_null]
    rw [hconst]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  have hg_null_int : (∫⁻ x, g_null x ∂μ) ≤ (δ : ℝ≥0∞) := by
    calc
      (∫⁻ x, g_null x ∂μ)
          = ∑' k : ℕ, ∫⁻ x, (W k).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
        rw [lintegral_tsum fun k =>
          (measurable_const.indicator (hW_open k).measurableSet).aemeasurable]
      _ = ∑' k : ℕ, μ (W k) := by
        congr 1 with k
        rw [lintegral_indicator (hW_open k).measurableSet, lintegral_const, one_mul,
          Measure.restrict_apply MeasurableSet.univ, univ_inter]
      _ ≤ ∑' k : ℕ, η k := ENNReal.tsum_le_tsum fun k => (hμW k).le
      _ ≤ (δ : ℝ≥0∞) := hη.le
  -- Positive and negative parts of `f₀`.
  let fp : α → ℝ≥0 := fun x => (f₀ x).toNNReal
  let fm : α → ℝ≥0 := fun x => (-f₀ x).toNNReal
  have hfp_meas : Measurable fp := hf₀_meas.real_toNNReal
  have hfm_meas : Measurable fm := hf₀_meas.neg.real_toNNReal
  have hfp_int : Integrable (fun x => (fp x : ℝ)) μ := hf₀_int.real_toNNReal
  have hfm_int : Integrable (fun x => (fm x : ℝ)) μ := hf₀_int.neg.real_toNNReal
  have hfp_lint_lt : (∫⁻ x, (fp x : ℝ≥0∞) ∂μ) < ∞ :=
    hasFiniteIntegral_iff_ofNNReal.mp hfp_int.hasFiniteIntegral
  have hfm_lint_lt : (∫⁻ x, (fm x : ℝ≥0∞) ∂μ) < ∞ :=
    hasFiniteIntegral_iff_ofNNReal.mp hfm_int.hasFiniteIntegral
  -- LSC upper bounds `gp`, `gm` and bounded USC lower bounds `hp`, `hm`.
  obtain ⟨gp, hfp_le_gp, hgp_lsc, hgp_int⟩ :=
    exists_le_lsc_lintegral hreg (fun x => (fp x : ℝ≥0∞)) hfp_meas.coe_nnreal_ennreal hδ_enn_ne
  obtain ⟨gm, hfm_le_gm, hgm_lsc, hgm_int⟩ :=
    exists_le_lsc_lintegral hreg (fun x => (fm x : ℝ≥0∞)) hfm_meas.coe_nnreal_ennreal hδ_enn_ne
  obtain ⟨hp, ⟨Mp, hhp_bdd⟩, hhp_le_fp, hhp_usc, hhp_int⟩ :=
    exists_bounded_usc_le_lintegral hreg fp hfp_lint_lt.ne hδ_enn_ne
  obtain ⟨hm, ⟨Mm, hhm_bdd⟩, hhm_le_fm, hhm_usc, hhm_int⟩ :=
    exists_bounded_usc_le_lintegral hreg fm hfm_lint_lt.ne hδ_enn_ne
  let gp_tot : α → ℝ≥0∞ := fun x => gp x + g_null x
  let gm_tot : α → ℝ≥0∞ := fun x => gm x + g_null x
  have hgp_tot_lsc : LowerSemicontinuous gp_tot := hgp_lsc.add hg_null_lsc
  have hgm_tot_lsc : LowerSemicontinuous gm_tot := hgm_lsc.add hg_null_lsc
  have hgp_tot_lint_le : (∫⁻ x, gp_tot x ∂μ) ≤ (∫⁻ x, (fp x : ℝ≥0∞) ∂μ) + 2 * (δ : ℝ≥0∞) := by
    rw [lintegral_add_left hgp_lsc.measurable]
    calc
      (∫⁻ x, gp x ∂μ) + (∫⁻ x, g_null x ∂μ)
          ≤ ((∫⁻ x, (fp x : ℝ≥0∞) ∂μ) + (δ : ℝ≥0∞)) + (δ : ℝ≥0∞) :=
        add_le_add hgp_int hg_null_int
      _ = (∫⁻ x, (fp x : ℝ≥0∞) ∂μ) + 2 * (δ : ℝ≥0∞) := by rw [add_assoc, two_mul]
  have hgm_tot_lint_le : (∫⁻ x, gm_tot x ∂μ) ≤ (∫⁻ x, (fm x : ℝ≥0∞) ∂μ) + 2 * (δ : ℝ≥0∞) := by
    rw [lintegral_add_left hgm_lsc.measurable]
    calc
      (∫⁻ x, gm x ∂μ) + (∫⁻ x, g_null x ∂μ)
          ≤ ((∫⁻ x, (fm x : ℝ≥0∞) ∂μ) + (δ : ℝ≥0∞)) + (δ : ℝ≥0∞) :=
        add_le_add hgm_int hg_null_int
      _ = (∫⁻ x, (fm x : ℝ≥0∞) ∂μ) + 2 * (δ : ℝ≥0∞) := by rw [add_assoc, two_mul]
  have h2δ_ne_top : 2 * (δ : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top
  have hgp_tot_lt_top : (∫⁻ x, gp_tot x ∂μ) < ∞ :=
    hgp_tot_lint_le.trans_lt (ENNReal.add_lt_top.mpr ⟨hfp_lint_lt, h2δ_ne_top.lt_top⟩)
  have hgm_tot_lt_top : (∫⁻ x, gm_tot x ∂μ) < ∞ :=
    hgm_tot_lint_le.trans_lt (ENNReal.add_lt_top.mpr ⟨hfm_lint_lt, h2δ_ne_top.lt_top⟩)
  let u : α → EReal := fun x => ((hp x : ℝ) : EReal) - (gm_tot x : EReal)
  let v : α → EReal := fun x => (gp_tot x : EReal) - ((hm x : ℝ) : EReal)
  -- Semicontinuity of `u` and `v`.
  have hu_usc : UpperSemicontinuous u := by
    show UpperSemicontinuous fun x => ((hp x : ℝ) : EReal) + -(gm_tot x : EReal)
    refine UpperSemicontinuous.add' ?_ ?_ ?_
    · exact continuous_coe_real_ereal.comp_upperSemicontinuous
        (NNReal.continuous_coe.comp_upperSemicontinuous hhp_usc fun _ _ h => h)
        fun _ _ h => EReal.coe_le_coe_iff.mpr h
    · refine continuous_neg.comp_lowerSemicontinuous_antitone ?_
        fun _ _ h => EReal.neg_le_neg_iff.mpr h
      exact continuous_coe_ennreal_ereal.comp_lowerSemicontinuous hgm_tot_lsc
        fun _ _ h => EReal.coe_ennreal_le_coe_ennreal_iff.mpr h
    · intro x
      exact EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))
  have hv_lsc : LowerSemicontinuous v := by
    show LowerSemicontinuous fun x => (gp_tot x : EReal) + -((hm x : ℝ) : EReal)
    refine LowerSemicontinuous.add' ?_ ?_ ?_
    · exact continuous_coe_ennreal_ereal.comp_lowerSemicontinuous hgp_tot_lsc
        fun _ _ h => EReal.coe_ennreal_le_coe_ennreal_iff.mpr h
    · refine continuous_neg.comp_upperSemicontinuous_antitone ?_
        fun _ _ h => EReal.neg_le_neg_iff.mpr h
      exact continuous_coe_real_ereal.comp_upperSemicontinuous
        (NNReal.continuous_coe.comp_upperSemicontinuous hhm_usc fun _ _ h => h)
        fun _ _ h => EReal.coe_le_coe_iff.mpr h
    · intro x
      exact EReal.continuousAt_add (Or.inr (by simp)) (Or.inr (by simp))
  -- Pointwise bounds `u ≤ Mp`, `-Mm ≤ v`, and `u ≤ f ≤ v`.
  have hu_bdd : ∀ x, u x ≤ ((Mp : ℝ) : EReal) := by
    intro x
    dsimp only [u]
    calc
      ((hp x : ℝ) : EReal) - (gm_tot x : EReal)
          ≤ ((Mp : ℝ) : EReal) - (0 : EReal) := by
        refine EReal.sub_le_sub ?_ ?_
        · exact EReal.coe_le_coe_iff.mpr (NNReal.coe_le_coe.mpr (hhp_bdd x))
        · exact EReal.coe_ennreal_nonneg _
      _ = ((Mp : ℝ) : EReal) := sub_zero _
  have hv_bdd : ∀ x, ((-(Mm : ℝ)) : EReal) ≤ v x := by
    intro x
    dsimp only [v]
    calc
      ((-(Mm : ℝ)) : EReal) = (0 : EReal) - ((Mm : ℝ) : EReal) := by simp
      _ ≤ (gp_tot x : EReal) - ((hm x : ℝ) : EReal) := by
        refine EReal.sub_le_sub (EReal.coe_ennreal_nonneg _) ?_
        exact EReal.coe_le_coe_iff.mpr (NNReal.coe_le_coe.mpr (hhm_bdd x))
  have huv_f : ∀ x, u x ≤ (f x : EReal) ∧ (f x : EReal) ≤ v x := by
    intro x
    by_cases hxN : x ∈ N
    · have hgm_top : gm_tot x = ∞ := by
        dsimp only [gm_tot]
        rw [hg_null_top x hxN, add_top]
      have hgp_top : gp_tot x = ∞ := by
        dsimp only [gp_tot]
        rw [hg_null_top x hxN, add_top]
      constructor
      · dsimp only [u]
        rw [hgm_top, EReal.coe_ennreal_top]
        simp
      · dsimp only [v]
        rw [hgp_top, EReal.coe_ennreal_top]
        simp
    · have hfx : f x = f₀ x := by
        by_contra hne
        exact hxN (hDN hne)
      rw [hfx, EReal.coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal (f₀ x)]
      constructor
      · dsimp only [u]
        refine EReal.sub_le_sub ?_ ?_
        · exact EReal.coe_le_coe_iff.mpr (NNReal.coe_le_coe.mpr (hhp_le_fp x))
        · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
            ((hfm_le_gm x).trans (le_self_add))
      · dsimp only [v]
        refine EReal.sub_le_sub ?_ ?_
        · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
            ((hfp_le_gp x).trans (le_self_add))
        · exact EReal.coe_le_coe_iff.mpr (NNReal.coe_le_coe.mpr (hhm_le_fm x))
  -- Integrability of `hp`, `hm`, `gp_tot.toReal`, `gm_tot.toReal`, `u.toReal`, `v.toReal`.
  have hhp_int_real : Integrable (fun x => (hp x : ℝ)) μ := by
    refine hfp_int.mono hhp_usc.measurable.coe_nnreal_real.aemeasurable.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
      exact NNReal.coe_le_coe.mpr (hhp_le_fp x)
  have hhm_int_real : Integrable (fun x => (hm x : ℝ)) μ := by
    refine hfm_int.mono hhm_usc.measurable.coe_nnreal_real.aemeasurable.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
      exact NNReal.coe_le_coe.mpr (hhm_le_fm x)
  have hgp_tot_ae : ∀ᵐ x ∂μ, gp_tot x < ∞ := ae_lt_top hgp_tot_lsc.measurable hgp_tot_lt_top.ne
  have hgm_tot_ae : ∀ᵐ x ∂μ, gm_tot x < ∞ := ae_lt_top hgm_tot_lsc.measurable hgm_tot_lt_top.ne
  have hgp_tot_int_real : Integrable (fun x => (gp_tot x).toReal) μ := by
    refine ⟨hgp_tot_lsc.measurable.ennreal_toReal.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    refine (lintegral_mono_ae ?_).trans_lt hgp_tot_lt_top
    filter_upwards [hgp_tot_ae] with x hx
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
  have hgm_tot_int_real : Integrable (fun x => (gm_tot x).toReal) μ := by
    refine ⟨hgm_tot_lsc.measurable.ennreal_toReal.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    refine (lintegral_mono_ae ?_).trans_lt hgm_tot_lt_top
    filter_upwards [hgm_tot_ae] with x hx
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
  have hu_ae_eq : (fun x => (u x).toReal) =ᵐ[μ] fun x => (hp x : ℝ) - (gm_tot x).toReal := by
    filter_upwards [hgm_tot_ae] with x hx
    dsimp only [u]
    rw [EReal.toReal_sub (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
      (by simpa using hx.ne) (EReal.coe_ennreal_ne_bot _),
      EReal.toReal_coe, EReal.toReal_coe_ennreal]
  have hv_ae_eq : (fun x => (v x).toReal) =ᵐ[μ] fun x => (gp_tot x).toReal - (hm x : ℝ) := by
    filter_upwards [hgp_tot_ae] with x hx
    dsimp only [v]
    rw [EReal.toReal_sub (by simpa using hx.ne) (EReal.coe_ennreal_ne_bot _)
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
      EReal.toReal_coe_ennreal, EReal.toReal_coe]
  have hu_int : Integrable (fun x => (u x).toReal) μ :=
    (hhp_int_real.sub hgm_tot_int_real).congr hu_ae_eq.symm
  have hv_int : Integrable (fun x => (v x).toReal) μ :=
    (hgp_tot_int_real.sub hhm_int_real).congr hv_ae_eq.symm
  -- Bound the integral of `v - u`.
  have hp_lint_lt : (∫⁻ x, (hp x : ℝ≥0∞) ∂μ) < ∞ :=
    (lintegral_mono fun x => ENNReal.coe_le_coe.mpr (hhp_le_fp x)).trans_lt hfp_lint_lt
  have hm_lint_lt : (∫⁻ x, (hm x : ℝ≥0∞) ∂μ) < ∞ :=
    (lintegral_mono fun x => ENNReal.coe_le_coe.mpr (hhm_le_fm x)).trans_lt hfm_lint_lt
  have hgp_real_le : ∫ x, (gp_tot x).toReal ∂μ ≤ ∫ x, (fp x : ℝ) ∂μ + 2 * (δ : ℝ) := by
    rw [integral_toReal hgp_tot_lsc.measurable.aemeasurable hgp_tot_ae,
      integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ => NNReal.coe_nonneg _) hfp_int.aestronglyMeasurable]
    have hfp_ofReal : (∫⁻ x, ENNReal.ofReal (fp x : ℝ) ∂μ) = ∫⁻ x, (fp x : ℝ≥0∞) ∂μ := by
      refine lintegral_congr fun x => ?_
      simp [ENNReal.ofReal_coe_nnreal]
    rw [hfp_ofReal]
    have hmono := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hfp_lint_lt.ne, h2δ_ne_top⟩) hgp_tot_lint_le
    rw [ENNReal.toReal_add hfp_lint_lt.ne h2δ_ne_top] at hmono
    simpa [ENNReal.toReal_mul] using hmono
  have hgm_real_le : ∫ x, (gm_tot x).toReal ∂μ ≤ ∫ x, (fm x : ℝ) ∂μ + 2 * (δ : ℝ) := by
    rw [integral_toReal hgm_tot_lsc.measurable.aemeasurable hgm_tot_ae,
      integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ => NNReal.coe_nonneg _) hfm_int.aestronglyMeasurable]
    have hfm_ofReal : (∫⁻ x, ENNReal.ofReal (fm x : ℝ) ∂μ) = ∫⁻ x, (fm x : ℝ≥0∞) ∂μ := by
      refine lintegral_congr fun x => ?_
      simp [ENNReal.ofReal_coe_nnreal]
    rw [hfm_ofReal]
    have hmono := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hfm_lint_lt.ne, h2δ_ne_top⟩) hgm_tot_lint_le
    rw [ENNReal.toReal_add hfm_lint_lt.ne h2δ_ne_top] at hmono
    simpa [ENNReal.toReal_mul] using hmono
  have hhp_real_ge : ∫ x, (fp x : ℝ) ∂μ ≤ ∫ x, (hp x : ℝ) ∂μ + (δ : ℝ) := by
    rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ => NNReal.coe_nonneg _) hfp_int.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ => NNReal.coe_nonneg _)
        hhp_int_real.aestronglyMeasurable]
    have h1 : (∫⁻ x, ENNReal.ofReal (fp x : ℝ) ∂μ) = ∫⁻ x, (fp x : ℝ≥0∞) ∂μ :=
      lintegral_congr fun _ => by simp [ENNReal.ofReal_coe_nnreal]
    have h2 : (∫⁻ x, ENNReal.ofReal (hp x : ℝ) ∂μ) = ∫⁻ x, (hp x : ℝ≥0∞) ∂μ :=
      lintegral_congr fun _ => by simp [ENNReal.ofReal_coe_nnreal]
    rw [h1, h2]
    have hmono := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hp_lint_lt.ne, ENNReal.coe_ne_top⟩) hhp_int
    rwa [ENNReal.toReal_add hp_lint_lt.ne ENNReal.coe_ne_top, ENNReal.coe_toReal] at hmono
  have hhm_real_ge : ∫ x, (fm x : ℝ) ∂μ ≤ ∫ x, (hm x : ℝ) ∂μ + (δ : ℝ) := by
    rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ => NNReal.coe_nonneg _) hfm_int.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ => NNReal.coe_nonneg _)
        hhm_int_real.aestronglyMeasurable]
    have h1 : (∫⁻ x, ENNReal.ofReal (fm x : ℝ) ∂μ) = ∫⁻ x, (fm x : ℝ≥0∞) ∂μ :=
      lintegral_congr fun _ => by simp [ENNReal.ofReal_coe_nnreal]
    have h2 : (∫⁻ x, ENNReal.ofReal (hm x : ℝ) ∂μ) = ∫⁻ x, (hm x : ℝ≥0∞) ∂μ :=
      lintegral_congr fun _ => by simp [ENNReal.ofReal_coe_nnreal]
    rw [h1, h2]
    have hmono := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hm_lint_lt.ne, ENNReal.coe_ne_top⟩) hhm_int
    rwa [ENNReal.toReal_add hm_lint_lt.ne ENNReal.coe_ne_top, ENNReal.coe_toReal] at hmono
  have hint_diff_lt : ∫ x, ((v x).toReal - (u x).toReal) ∂μ < ε := by
    have hdiff_ae : (fun x => (v x).toReal - (u x).toReal) =ᵐ[μ]
        fun x => ((gp_tot x).toReal - (hp x : ℝ)) + ((gm_tot x).toReal - (hm x : ℝ)) := by
      filter_upwards [hu_ae_eq, hv_ae_eq] with x hux hvx
      rw [hux, hvx]
      ring
    have h1_int : Integrable (fun x => (gp_tot x).toReal - (hp x : ℝ)) μ :=
      hgp_tot_int_real.sub hhp_int_real
    have h2_int : Integrable (fun x => (gm_tot x).toReal - (hm x : ℝ)) μ :=
      hgm_tot_int_real.sub hhm_int_real
    rw [integral_congr_ae hdiff_ae, integral_add h1_int h2_int,
      integral_sub hgp_tot_int_real hhp_int_real,
      integral_sub hgm_tot_int_real hhm_int_real]
    have hδ_val : (δ : ℝ) = ε / 7 := rfl
    linarith
  have hlint_diff_lt : (∫⁻ x, (v x - u x).toENNReal ∂μ) < ENNReal.ofReal ε := by
    have hae_enn : (fun x => (v x - u x).toENNReal) =ᵐ[μ]
        fun x => ENNReal.ofReal ((v x).toReal - (u x).toReal) := by
      filter_upwards [hgp_tot_ae, hgm_tot_ae] with x hgpx hgmx
      have hux : u x = (((hp x : ℝ) - (gm_tot x).toReal : ℝ) : EReal) := by
        dsimp only [u]
        rw [← EReal.coe_ennreal_toReal hgmx.ne, EReal.coe_sub]
      have hvx : v x = (((gp_tot x).toReal - (hm x : ℝ) : ℝ) : EReal) := by
        dsimp only [v]
        rw [← EReal.coe_ennreal_toReal hgpx.ne, EReal.coe_sub]
      rw [hvx, hux, ← EReal.coe_sub, EReal.toReal_coe, EReal.toReal_coe]
      rfl
    have hnonneg_ae : 0 ≤ᵐ[μ] fun x => (v x).toReal - (u x).toReal := by
      filter_upwards [hgp_tot_ae, hgm_tot_ae] with x hgpx hgmx
      have huvx : u x ≤ v x := (huv_f x).1.trans (huv_f x).2
      have hux : u x = (((hp x : ℝ) - (gm_tot x).toReal : ℝ) : EReal) := by
        dsimp only [u]
        rw [← EReal.coe_ennreal_toReal hgmx.ne, EReal.coe_sub]
      have hvx : v x = (((gp_tot x).toReal - (hm x : ℝ) : ℝ) : EReal) := by
        dsimp only [v]
        rw [← EReal.coe_ennreal_toReal hgpx.ne, EReal.coe_sub]
      rw [hux, hvx, EReal.coe_le_coe_iff] at huvx
      dsimp only [Pi.zero_apply]
      rw [hux, hvx, EReal.toReal_coe, EReal.toReal_coe]
      linarith
    have hsub_int : Integrable (fun x => (v x).toReal - (u x).toReal) μ := hv_int.sub hu_int
    rw [lintegral_congr_ae hae_enn,
      ← ofReal_integral_eq_lintegral_ofReal hsub_int hnonneg_ae]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr hint_diff_lt
  exact ⟨u, v, (definition_2_8_upper u).mpr hu_usc, (definition_2_8_lower v).mpr hv_lsc,
    ⟨(Mp : ℝ), hu_bdd⟩, ⟨-(Mm : ℝ), hv_bdd⟩, huv_f, hu_int, hv_int,
    hlint_diff_lt, hint_diff_lt⟩

/-- `BookL1` specialization of **Theorem 2.25**: for real-valued `f` with `(f · : ℂ) ∈ L^1(μ)`
(`Chapter01.BookL1 μ`), `theorem_2_25` applies directly without `σ`-finiteness. -/
theorem theorem_2_25_bookL1 {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
    [MeasurableSpace α] {μ : Measure α} (hreg : Book214RegularityHypotheses μ)
    (f : α → ℝ) (hf : Chapter01.BookL1 μ (fun x => (f x : ℂ))) {ε : ℝ} (hε : 0 < ε) :
    ∃ u v : α → EReal,
      BookUpperSemicontinuous u ∧
      BookLowerSemicontinuous v ∧
      (∃ M : ℝ, ∀ x, u x ≤ (M : EReal)) ∧
      (∃ M : ℝ, ∀ x, (M : EReal) ≤ v x) ∧
      (∀ x, u x ≤ (f x : EReal) ∧ (f x : EReal) ≤ v x) ∧
      Integrable (fun x => (u x).toReal) μ ∧
      Integrable (fun x => (v x).toReal) μ ∧
      (∫⁻ x, (v x - u x).toENNReal ∂μ) < ENNReal.ofReal ε ∧
      ∫ x, ((v x).toReal - (u x).toReal) ∂μ < ε := by
  have hf_int_c : Integrable (fun x => (f x : ℂ)) μ :=
    ((Chapter01.definition_1_30 μ _).mp hf).2
  have hf_int : Integrable f μ := by
    simpa using Complex.reCLM.integrable_comp hf_int_c
  exact theorem_2_25 hreg f hf_int hε

end VitaliCaratheodory2_25

/-!
## 2.21: Exposition — Remarks on interval integrals, Riemann integrals, and non-Borel sets (printed p. 53)

Per the binding `2.21` scope note (`INVENTORY-CH02.md` / `BRIEF.md`), node `2.21` is recorded as
**exposition** (and conservatively excluded from `PROGRESS.md` `Done`), because Rudin's narrative
cross-reference to *Principles of Mathematical Analysis* Ch. 11 for the converse characterization
of Riemann-integrable functions is stated as background commentary without proof in `RCA`. The
formal statements below supply the mathematical facts discussed in `2.21`: `L^1(E)` via measure
restriction, singleton nullity and endpoint-insensitivity of 1D Lebesgue / interval integrals,
agreement of the `BoxIntegral` Riemann integral with the Lebesgue integral for continuous and
bounded a.e.-continuous functions, and the Cantor-set cardinality existence of a Lebesgue-measurable
non-Borel subset of `ℝ`.
-/

section Exposition2_21

open scoped Pointwise

/-- `RCA 2.21` (first remark, p. 53): restricting `lebesgueMeasure k` to a Lebesgue-measurable set
`E ⊆ ℝ^k` identifies `L^1` functions on `(E, m|_E)` with `E.indicator f ∈ L^1(ℝ^k)` and identifies
the restricted integral `∫_E f dm` with `BookComplexIntegral`. -/
theorem remarks_2_21_restrict_l1 {k : ℕ} {E : Set (EuclideanSpace ℝ (Fin k))}
    (hE : @MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) E)
    {f : EuclideanSpace ℝ (Fin k) → ℂ}
    (hf : @Chapter01.BookL1 (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) (lebesgueMeasure k) f) :
    @Chapter01.BookL1 (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k)
      (lebesgueMeasure k) (E.indicator f) ∧
    @Chapter01.BookL1 (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k)
      ((lebesgueMeasure k).restrict E) f ∧
    @Chapter01.BookComplexIntegral (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k)
      ((lebesgueMeasure k).restrict E) Set.univ f =
      @Chapter01.BookComplexIntegral (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k)
        (lebesgueMeasure k) E f := by
  let _ : MeasurableSpace (EuclideanSpace ℝ (Fin k)) := lebesgueSigma k
  obtain ⟨hf_meas, hf_int⟩ := (Chapter01.definition_1_30 (lebesgueMeasure k) f).mp hf
  have hf_ind : Chapter01.BookL1 (lebesgueMeasure k) (E.indicator f) :=
    (Chapter01.definition_1_30 (lebesgueMeasure k) (E.indicator f)).mpr
      ⟨hf_meas.indicator hE, hf_int.indicator hE⟩
  have hf_rest : Chapter01.BookL1 ((lebesgueMeasure k).restrict E) f :=
    (Chapter01.definition_1_30 ((lebesgueMeasure k).restrict E) f).mpr
      ⟨hf_meas, hf_int.restrict⟩
  refine ⟨hf_ind, hf_rest, ?_⟩
  rw [Chapter01.definition_1_31 ((lebesgueMeasure k).restrict E) Set.univ f hf_rest,
    Chapter01.definition_1_31 (lebesgueMeasure k) E f hf, Measure.restrict_univ]

/-- `RCA 2.21` (interval-integral remark, p. 53): singletons in `ℝ` have Lebesgue measure `0`,
all four interval boundary conventions `[a, b]`, `(a, b)`, `[a, b)`, `(a, b]` (`a ≤ b`) have
measure `b - a`, and their Lebesgue integrals agree with `∫ x in a..b, f x`. -/
theorem remarks_2_21_singleton_and_intervals {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℂ) :
    volume ({a} : Set ℝ) = 0 ∧
    volume (Icc a b) = ENNReal.ofReal (b - a) ∧
    volume (Ioo a b) = ENNReal.ofReal (b - a) ∧
    volume (Ico a b) = ENNReal.ofReal (b - a) ∧
    volume (Ioc a b) = ENNReal.ofReal (b - a) ∧
    (∫ x in Icc a b, f x) = (∫ x in Ioo a b, f x) ∧
    (∫ x in Icc a b, f x) = (∫ x in Ico a b, f x) ∧
    (∫ x in Icc a b, f x) = (∫ x in Ioc a b, f x) ∧
    (∫ x in Icc a b, f x) = (∫ x in a..b, f x) := by
  refine ⟨measure_singleton a, Real.volume_Icc, Real.volume_Ioo, Real.volume_Ico, Real.volume_Ioc,
    integral_Icc_eq_integral_Ioo, ?_, integral_Icc_eq_integral_Ioc, ?_⟩
  · rw [integral_Icc_eq_integral_Ioo, integral_Ico_eq_integral_Ioo]
  · rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

/-- `RCA 2.21` (Riemann-vs-Lebesgue comparison, p. 53): on a nonempty box `I` in `ℝ^k` with any
locally finite measure `μ` (in particular Lebesgue `volume` on `ℝ¹`), every continuous function on
`Icc` and every bounded `μ`-a.e.-continuous function is Riemann integrable
(`BoxIntegral.IntegrationParams.Riemann`) with Riemann integral equal to its Lebesgue integral. -/
theorem remarks_2_21_riemann_eq_lebesgue {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ))
    [IsLocallyFiniteMeasure μ] (I : BoxIntegral.Box ι) (f : (ι → ℝ) → ℂ) :
    (ContinuousOn f (BoxIntegral.Box.Icc I) →
      BoxIntegral.HasIntegral I BoxIntegral.IntegrationParams.Riemann f
        μ.toBoxAdditive.toSMul (∫ x in I, f x ∂μ) ∧
      BoxIntegral.integral I BoxIntegral.IntegrationParams.Riemann f μ.toBoxAdditive.toSMul =
        ∫ x in I, f x ∂μ) ∧
    ((∃ C : ℝ, ∀ x ∈ BoxIntegral.Box.Icc I, ‖f x‖ ≤ C) → (∀ᵐ x ∂μ, ContinuousAt f x) →
      BoxIntegral.HasIntegral I BoxIntegral.IntegrationParams.Riemann f
        μ.toBoxAdditive.toSMul (∫ x in I, f x ∂μ) ∧
      BoxIntegral.integral I BoxIntegral.IntegrationParams.Riemann f μ.toBoxAdditive.toSMul =
        ∫ x in I, f x ∂μ) :=
  ⟨fun hc =>
    let h := hc.hasBoxIntegral μ BoxIntegral.IntegrationParams.Riemann
    ⟨h, h.integral_eq⟩,
   fun hb hc =>
    let h := AEContinuous.hasBoxIntegral μ hb hc BoxIntegral.IntegrationParams.Riemann
    ⟨h, h.integral_eq⟩⟩

/-- `RCA 2.21` (Cantor-set / non-Borel Lebesgue-measurable set discussion, p. 53): the middle-thirds
Cantor set `cantorSet ⊆ [0, 1]` has Lebesgue measure `0` and continuum cardinality `𝔠`, so every
subset of `cantorSet` is Lebesgue measurable (`NullMeasurableSet _ volume`) while there exists a
Lebesgue-measurable subset `E ⊆ cantorSet` that is not a Borel set. -/
theorem remarks_2_21_cantor_non_borel :
    volume cantorSet = 0 ∧
    Cardinal.mk cantorSet = Cardinal.continuum ∧
    (∀ E : Set ℝ, E ⊆ cantorSet → NullMeasurableSet E volume) ∧
    (∃ E : Set ℝ, E ⊆ cantorSet ∧ NullMeasurableSet E volume ∧ ¬ @MeasurableSet ℝ (borel ℝ) E) := by
  have hpre : ∀ n : ℕ, volume (preCantorSet n) ≤ ((2 : ℝ≥0∞) / 3) ^ n := by
    intro n
    induction n with
    | zero =>
      simp [preCantorSet_zero, Real.volume_Icc]
    | succ n ih =>
      rw [preCantorSet_succ]
      have hdiv3 : (· / (3 : ℝ)) '' preCantorSet n = (3⁻¹ : ℝ) • preCantorSet n := by
        ext x
        simp only [mem_image, mem_smul_set, smul_eq_mul]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨y, hy, by ring⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨y, hy, by ring⟩
      have hshift : (fun x : ℝ => (2 + x) / 3) '' preCantorSet n =
          (fun y : ℝ => (2 / 3 : ℝ) + y) '' ((· / (3 : ℝ)) '' preCantorSet n) := by
        rw [← image_comp]
        congr 1
        ext x; dsimp; ring
      have hm1 : volume ((· / 3) '' preCantorSet n) =
          ((1 : ℝ≥0∞) / 3) * volume (preCantorSet n) := by
        rw [hdiv3, Measure.addHaar_smul volume (3⁻¹ : ℝ) (preCantorSet n),
          Module.finrank_self, pow_one]
        have hnorm : ENNReal.ofReal |(3⁻¹ : ℝ)| = (1 : ℝ≥0∞) / 3 := by
          rw [abs_of_pos (by positivity), ← one_div,
            ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 3), ENNReal.ofReal_one,
            ENNReal.ofReal_ofNat]
        rw [hnorm]
      have hm2 : volume ((fun x : ℝ => (2 + x) / 3) '' preCantorSet n) =
          ((1 : ℝ≥0∞) / 3) * volume (preCantorSet n) := by
        rw [hshift, image_add_left, measure_preimage_add, hm1]
      calc
        volume ((· / 3) '' preCantorSet n ∪ (fun x : ℝ => (2 + x) / 3) '' preCantorSet n)
            ≤ volume ((· / 3) '' preCantorSet n) +
                volume ((fun x : ℝ => (2 + x) / 3) '' preCantorSet n) :=
          measure_union_le _ _
        _ = ((1 : ℝ≥0∞) / 3) * volume (preCantorSet n) +
              ((1 : ℝ≥0∞) / 3) * volume (preCantorSet n) := by rw [hm1, hm2]
        _ = (((1 : ℝ≥0∞) / 3) + ((1 : ℝ≥0∞) / 3)) * volume (preCantorSet n) :=
          (add_mul _ _ _).symm
        _ ≤ (((1 : ℝ≥0∞) / 3) + ((1 : ℝ≥0∞) / 3)) * ((2 : ℝ≥0∞) / 3) ^ n :=
          mul_le_mul_of_nonneg_left ih zero_le
        _ = ((2 : ℝ≥0∞) / 3) ^ (n + 1) := by
          have h12 : ((1 : ℝ≥0∞) / 3) + ((1 : ℝ≥0∞) / 3) = (2 : ℝ≥0∞) / 3 := by
            rw [← ENNReal.add_div, one_add_one_eq_two]
          rw [h12, pow_succ']
  have hvol_zero : volume cantorSet = 0 := by
    have hlt1 : ((2 : ℝ≥0∞) / 3) < 1 := by
      rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl ENNReal.ofNat_ne_top), one_mul]
      norm_num
    have htend : Filter.Tendsto (fun n : ℕ => ((2 : ℝ≥0∞) / 3) ^ n) Filter.atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt1
    refine le_antisymm ?_ zero_le
    exact ge_of_tendsto htend (Filter.Eventually.of_forall fun n =>
      (measure_mono (iInter_subset preCantorSet n)).trans (hpre n))
  have hcard : Cardinal.mk cantorSet = Cardinal.continuum := by
    rw [Cardinal.mk_congr cantorSetEquivNatToBool]
    simp [Cardinal.two_power_aleph0]
  have hsub_null : ∀ E : Set ℝ, E ⊆ cantorSet → NullMeasurableSet E volume :=
    fun E hE => NullMeasurableSet.of_null (measure_mono_null hE hvol_zero)
  refine ⟨hvol_zero, hcard, hsub_null, ?_⟩
  by_contra h_all_borel
  have hall : ∀ S : Set cantorSet, @MeasurableSet ℝ (borel ℝ) (Subtype.val '' S) := by
    intro S
    by_contra hnot
    exact h_all_borel ⟨Subtype.val '' S, Subtype.coe_image_subset cantorSet S,
      hsub_null _ (Subtype.coe_image_subset cantorSet S), hnot⟩
  let φ : Set cantorSet → {E : Set ℝ | @MeasurableSet ℝ (borel ℝ) E} :=
    fun S => ⟨Subtype.val '' S, hall S⟩
  have hφ_inj : Function.Injective φ := by
    intro S₁ S₂ h
    have himg : (Subtype.val '' S₁ : Set ℝ) = Subtype.val '' S₂ := congrArg Subtype.val h
    exact Subtype.val_injective.image_injective himg
  have hle_borel : Cardinal.mk (Set cantorSet) ≤
      Cardinal.mk {E : Set ℝ | @MeasurableSet ℝ (borel ℝ) E} :=
    Cardinal.mk_le_of_injective hφ_inj
  have hborel_le_c : Cardinal.mk {E : Set ℝ | @MeasurableSet ℝ (borel ℝ) E} ≤ Cardinal.continuum := by
    have hgen : borel ℝ = MeasurableSpace.generateFrom (TopologicalSpace.countableBasis ℝ) :=
      (TopologicalSpace.isBasis_countableBasis ℝ).borel_eq_generateFrom
    rw [hgen]
    refine MeasurableSpace.cardinal_measurableSet_le_continuum ?_
    exact (TopologicalSpace.countable_countableBasis ℝ).le_aleph0.trans Cardinal.aleph0_le_continuum
  have hpow : Cardinal.mk (Set cantorSet) = (2 : Cardinal) ^ Cardinal.continuum := by
    rw [Cardinal.mk_set, hcard]
  have hlt : Cardinal.continuum < Cardinal.mk (Set cantorSet) := by
    rw [hpow]
    exact Cardinal.cantor Cardinal.continuum
  exact (hlt.trans_le (hle_borel.trans hborel_le_c)).false

end Exposition2_21

/-!
## 2.14: The Riesz Representation Theorem (printed pp. 40–47)
-/

section RieszRepresentation2_14

/-- Pointwise real-part projection `C_c(α, ℂ) → C_c(α, ℝ)` (`RCA 2.14`, p. 41). -/
def reCc {α : Type*} [TopologicalSpace α] (f : C_c(α, ℂ)) : C_c(α, ℝ) where
  toFun x := (f x).re
  continuous_toFun := Complex.continuous_re.comp f.continuous
  hasCompactSupport' := f.hasCompactSupport.comp_left Complex.zero_re

/-- Pointwise imaginary-part projection `C_c(α, ℂ) → C_c(α, ℝ)` (`RCA 2.14`, p. 41). -/
def imCc {α : Type*} [TopologicalSpace α] (f : C_c(α, ℂ)) : C_c(α, ℝ) where
  toFun x := (f x).im
  continuous_toFun := Complex.continuous_im.comp f.continuous
  hasCompactSupport' := f.hasCompactSupport.comp_left Complex.zero_im

@[simp]
theorem reCc_apply {α : Type*} [TopologicalSpace α] (f : C_c(α, ℂ)) (x : α) :
    reCc f x = (f x).re := rfl

@[simp]
theorem imCc_apply {α : Type*} [TopologicalSpace α] (f : C_c(α, ℂ)) (x : α) :
    imCc f x = (f x).im := rfl

theorem ofRealCc_reCc_add_imCc {α : Type*} [TopologicalSpace α] (f : C_c(α, ℂ)) :
    f = ofRealCc (reCc f) + Complex.I • ofRealCc (imCc f) := by
  ext x
  simp [mul_comm Complex.I, Complex.re_add_im]

/-- Positive part `g ⊔ 0` in `C_c(α, ℝ)` used to split real compactly supported functions
into nonnegative parts (`RCA 2.14`, Step X, p. 46). -/
def posPartCc {α : Type*} [TopologicalSpace α] (g : C_c(α, ℝ)) : C_c(α, ℝ) :=
  g ⊔ 0

@[simp]
theorem posPartCc_apply {α : Type*} [TopologicalSpace α] (g : C_c(α, ℝ)) (x : α) :
    posPartCc g x = max (g x) 0 := rfl

theorem ofRealCc_add {α : Type*} [TopologicalSpace α] (g₁ g₂ : C_c(α, ℝ)) :
    ofRealCc (g₁ + g₂) = ofRealCc g₁ + ofRealCc g₂ := by
  ext x; simp

theorem ofRealCc_sub {α : Type*} [TopologicalSpace α] (g₁ g₂ : C_c(α, ℝ)) :
    ofRealCc (g₁ - g₂) = ofRealCc g₁ - ofRealCc g₂ := by
  ext x; simp

theorem ofRealCc_smul {α : Type*} [TopologicalSpace α] (c : ℝ) (g : C_c(α, ℝ)) :
    ofRealCc (c • g) = (c : ℂ) • ofRealCc g := by
  ext x; simp

/-- Every positive complex linear functional `Λ` on `C_c(α, ℂ)` takes real values on real-valued
functions `ofRealCc g` (`g : C_c(α, ℝ)`) and nonnegative real values when `0 ≤ g`. -/
theorem IsPositiveCcFunctional.im_ofRealCc_eq_zero {α : Type*} [TopologicalSpace α]
    {Λ : LinearFunctional C_c(α, ℂ)} (hΛ : IsPositiveCcFunctional Λ) (g : C_c(α, ℝ)) :
    (Λ (ofRealCc g)).im = 0 := by
  have hdecomp : g = posPartCc g - posPartCc (-g) := by
    ext x
    change g x = max (g x) 0 - max (-g x) 0
    rcases le_total 0 (g x) with hx | hx
    · have h1 : max (g x) 0 = g x := max_eq_left hx
      have h2 : max (-g x) 0 = 0 := max_eq_right (neg_nonpos.mpr hx)
      linarith
    · have h1 : max (g x) 0 = 0 := max_eq_right hx
      have h2 : max (-g x) 0 = -g x := max_eq_left (neg_nonneg.mpr hx)
      linarith
  have hpos1 : BookNonnegComplex (Λ (ofRealCc (posPartCc g))) :=
    hΛ _ fun x => ⟨Complex.ofReal_im _, by simp⟩
  have hpos2 : BookNonnegComplex (Λ (ofRealCc (posPartCc (-g)))) :=
    hΛ _ fun x => ⟨Complex.ofReal_im _, by simp⟩
  conv_lhs => rw [hdecomp, ofRealCc_sub, map_sub]
  simp [hpos1.1, hpos2.1]

/-- Real positive linear functional `C_c(α, ℝ) →ₚ[ℝ] ℝ` canonically induced by a positive complex
linear functional `Λ` on `C_c(α, ℂ)`. -/
def rieszRealFunctional {α : Type*} [TopologicalSpace α]
    (Λ : LinearFunctional C_c(α, ℂ)) (hΛ : IsPositiveCcFunctional Λ) :
    C_c(α, ℝ) →ₚ[ℝ] ℝ where
  toFun g := (Λ (ofRealCc g)).re
  map_add' g₁ g₂ := by
    rw [ofRealCc_add, map_add, Complex.add_re]
  map_smul' c g := by
    rw [ofRealCc_smul, map_smul]
    simp
  monotone' g₁ g₂ hg := by
    have hnonneg : BookNonnegComplex (Λ (ofRealCc (g₂ - g₁))) := by
      refine hΛ _ fun x => ⟨Complex.ofReal_im _, ?_⟩
      simpa using sub_nonneg.mpr (hg x)
    have hre : 0 ≤ (Λ (ofRealCc g₂)).re - (Λ (ofRealCc g₁)).re := by
      simpa [ofRealCc_sub, map_sub] using hnonneg.2
    linarith

theorem rieszRealFunctional_ofRealCc {α : Type*} [TopologicalSpace α]
    (Λ : LinearFunctional C_c(α, ℂ)) (hΛ : IsPositiveCcFunctional Λ) (g : C_c(α, ℝ)) :
    Λ (ofRealCc g) = ((rieszRealFunctional Λ hΛ g : ℝ) : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using hΛ.im_ofRealCc_eq_zero g

/-- Every Mathlib regular Borel measure `[BorelSpace α] [μ.Regular]` satisfies Rudin's
`Book214RegularityHypotheses` (`2.14(b–d)`). -/
theorem mathlib_regular_satisfies_214 {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] (μ : Measure α) [μ.Regular] :
    Book214RegularityHypotheses μ := by
  refine ⟨le_of_eq BorelSpace.measurable_eq.symm,
    fun _ hK => hK.measure_lt_top,
    fun E _ => Set.measure_eq_iInf_isOpen E μ, ?_, ?_⟩
  · intro U hU
    unfold BookInnerRegularSet
    refine le_antisymm ?_
      (iSup_le fun K => iSup_le fun hKU => iSup_le fun _ => measure_mono hKU)
    refine le_of_forall_lt fun r hr => ?_
    obtain ⟨K, hKU, hKc, hrK⟩ := Measure.Regular.innerRegular hU r hr
    exact lt_iSup_iff.mpr ⟨K, lt_iSup_iff.mpr ⟨hKU, lt_iSup_iff.mpr ⟨hKc, hrK⟩⟩⟩
  · intro E hE hE_fin
    unfold BookInnerRegularSet
    refine le_antisymm ?_
      (iSup_le fun K => iSup_le fun hKE => iSup_le fun _ => measure_mono hKE)
    refine le_of_forall_lt fun r hr => ?_
    obtain ⟨K, hKE, hKc, hrK⟩ :=
      Measure.InnerRegularCompactLTTop.innerRegular ⟨hE, hE_fin.ne⟩ r hr
    exact lt_iSup_iff.mpr ⟨K, lt_iSup_iff.mpr ⟨hKE, lt_iSup_iff.mpr ⟨hKc, hrK⟩⟩⟩

/-- Passing to the Chapter 1 completion (`Chapter01.completionSigma`, `Chapter01.completedMeasure`)
preserves `Book214RegularityHypotheses`. -/
theorem completedMeasure_preserves_214 {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} (hreg : Book214RegularityHypotheses μ) :
    @Book214RegularityHypotheses α _ (Chapter01.completionSigma μ)
      (Chapter01.completedMeasure μ) := by
  obtain ⟨hborel, hK_fin, houter, hopen_inner, hfin_inner⟩ := hreg
  have hle_comp : ‹MeasurableSpace α› ≤ Chapter01.completionSigma μ :=
    fun _ hs => hs.nullMeasurableSet
  have happly : ∀ S : Set α, Chapter01.completedMeasure μ S = μ S :=
    fun S => Measure.completion_apply μ S
  refine ⟨hborel.trans hle_comp, fun K hK => by rw [happly]; exact hK_fin K hK, ?_, ?_, ?_⟩
  · intro E hE
    unfold BookOuterRegularSet
    obtain ⟨A, B, hA, hB, hAE, hEB, hnull⟩ := ((Chapter01.theorem_1_36 μ).1 E).mp hE
    have hμE : Chapter01.completedMeasure μ E = μ A :=
      (Chapter01.theorem_1_36 μ).2.1 E A B hA hB hAE hEB hnull
    have hμBA : μ B = μ A := by
      refine le_antisymm ?_ (measure_mono (hAE.trans hEB))
      calc
        μ B ≤ μ (A ∪ (B \ A)) := measure_mono fun x hx => by
          by_cases hxA : x ∈ A
          · exact Or.inl hxA
          · exact Or.inr ⟨hx, hxA⟩
        _ ≤ μ A + μ (B \ A) := measure_union_le A (B \ A)
        _ = μ A := by rw [hnull, add_zero]
    refine le_antisymm
      (le_iInf fun V => le_iInf fun hEV => le_iInf fun _ => by
        rw [happly, happly]
        exact measure_mono hEV) ?_
    calc
      (⨅ (V : Set α) (_ : E ⊆ V) (_ : IsOpen V), Chapter01.completedMeasure μ V)
          ≤ ⨅ (V : Set α) (_ : B ⊆ V) (_ : IsOpen V), μ V := by
        refine le_iInf fun V => le_iInf fun hBV => le_iInf fun hV => ?_
        rw [← happly V]
        exact iInf_le_of_le V (iInf_le_of_le (hEB.trans hBV) (iInf_le_of_le hV le_rfl))
      _ = μ B := (houter B hB).symm
      _ = Chapter01.completedMeasure μ E := by rw [hμBA, hμE]
  · intro U hU
    unfold BookInnerRegularSet
    simp_rw [happly]
    exact hopen_inner U hU
  · intro E hE hE_fin
    unfold BookInnerRegularSet
    obtain ⟨A, B, hA, hB, hAE, hEB, hnull⟩ := ((Chapter01.theorem_1_36 μ).1 E).mp hE
    have hμE : Chapter01.completedMeasure μ E = μ A :=
      (Chapter01.theorem_1_36 μ).2.1 E A B hA hB hAE hEB hnull
    have hμA_fin : μ A < ∞ := by rwa [← hμE]
    refine le_antisymm ?_
      (iSup_le fun K => iSup_le fun hKE => iSup_le fun _ => by
        rw [happly, happly]
        exact measure_mono hKE)
    calc
      Chapter01.completedMeasure μ E = μ A := hμE
      _ = ⨆ (K : Set α) (_ : K ⊆ A) (_ : IsCompact K), μ K := hfin_inner A hA hμA_fin
      _ ≤ ⨆ (K : Set α) (_ : K ⊆ E) (_ : IsCompact K), Chapter01.completedMeasure μ K := by
        refine iSup_le fun K => iSup_le fun hKA => iSup_le fun hKc => ?_
        rw [← happly K]
        exact le_iSup_of_le K (le_iSup_of_le (hKA.trans hAE) (le_iSup_of_le hKc le_rfl))

/-- Every `f : C_c(α, ℂ)` belongs to `Chapter01.BookL1 μ` whenever `μ` satisfies
`Book214RegularityHypotheses`. -/
theorem Book214RegularityHypotheses.bookL1_cc {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} (hreg : Book214RegularityHypotheses μ)
    (f : C_c(α, ℂ)) : Chapter01.BookL1 μ f := by
  have : OpensMeasurableSpace α := hreg.opensMeasurableSpace
  have : IsFiniteMeasureOnCompacts μ := ⟨hreg.2.1⟩
  exact (Chapter01.definition_1_30 μ f).mpr ⟨f.continuous.measurable, f.integrable⟩

/-- **Uniqueness part of Theorem 2.14** (`RCA` pp. 41–42): on any `σ`-algebra `𝔐` containing
`borel α`, any two positive measures `μ₁, μ₂` satisfying `Book214RegularityHypotheses` that give
the same integral to every `f ∈ C_c(α, ℂ)` are identical on `𝔐`. -/
theorem theorem_2_14_uniqueness_on_sigma {α : Type*} [TopologicalSpace α]
    [T2Space α] [LocallyCompactSpace α] [MeasurableSpace α] {μ₁ μ₂ : Measure α}
    (h₁ : Book214RegularityHypotheses μ₁) (h₂ : Book214RegularityHypotheses μ₂)
    (hint : ∀ f : C_c(α, ℂ), ∫ x, f x ∂μ₁ = ∫ x, f x ∂μ₂) :
    μ₁ = μ₂ := by
  have hcompact_le : ∀ {ν₁ ν₂ : Measure α},
      Book214RegularityHypotheses ν₁ → Book214RegularityHypotheses ν₂ →
      (∀ f : C_c(α, ℂ), ∫ x, f x ∂ν₁ = ∫ x, f x ∂ν₂) →
      ∀ {K : Set α}, IsCompact K → ν₁ K ≤ ν₂ K := by
    intro ν₁ ν₂ hν₁ hν₂ hν_eq K hK
    have : OpensMeasurableSpace α := hν₁.opensMeasurableSpace
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε_ne : (ε : ℝ≥0∞) ≠ 0 := (ENNReal.coe_pos.mpr hε).ne'
    obtain ⟨V, hKV, hV, hν₂V⟩ :=
      hν₂.exists_isOpen_lt_add (hν₂.measurableSet_of_isClosed hK.isClosed) (hν₂.2.1 K hK) hε_ne
    obtain ⟨f, hfK, hfV⟩ := lemma_2_12 hK hV hKV
    let g : C_c(α, ℝ) := reCc f
    have hg_nonneg : ∀ x, 0 ≤ g x := by
      intro x
      rcases hfK.2.1 x with ⟨r, ⟨hr0, _⟩, hfx⟩
      simpa [g, hfx] using hr0
    have hg_le_one : ∀ x, g x ≤ 1 := by
      intro x
      rcases hfK.2.1 x with ⟨r, ⟨_, hr1⟩, hfx⟩
      simpa [g, hfx] using hr1
    have hg_int₁ : Integrable g ν₁ := by
      have : IsFiniteMeasureOnCompacts ν₁ := ⟨hν₁.2.1⟩
      exact g.integrable
    have hg_int₂ : Integrable g ν₂ := by
      have : OpensMeasurableSpace α := hν₂.opensMeasurableSpace
      have : IsFiniteMeasureOnCompacts ν₂ := ⟨hν₂.2.1⟩
      exact g.integrable
    have hg_eq_int : ∫ x, g x ∂ν₁ = ∫ x, g x ∂ν₂ := by
      have hc := hν_eq (ofRealCc g)
      have h1 : (∫ x, ofRealCc g x ∂ν₁) = ((∫ x, g x ∂ν₁ : ℝ) : ℂ) := integral_ofReal
      have h2 : (∫ x, ofRealCc g x ∂ν₂) = ((∫ x, g x ∂ν₂ : ℝ) : ℂ) := integral_ofReal
      rw [h1, h2] at hc
      exact Complex.ofReal_injective hc
    have hlint_eq : (∫⁻ x, ENNReal.ofReal (g x) ∂ν₁) = ∫⁻ x, ENNReal.ofReal (g x) ∂ν₂ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hg_int₁ (Filter.Eventually.of_forall hg_nonneg),
        ← ofReal_integral_eq_lintegral_ofReal hg_int₂ (Filter.Eventually.of_forall hg_nonneg),
        hg_eq_int]
    have hK_le : ν₁ K ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂ν₁ := by
      rw [← lintegral_indicator_one (hν₁.measurableSet_of_isClosed hK.isClosed)]
      refine lintegral_mono fun x => ?_
      by_cases hxK : x ∈ K
      · have hgx : g x = 1 := by
          have := hfK.2.2 hxK
          simpa [g] using congrArg Complex.re this
        simp [hxK, hgx]
      · simp [hxK]
    have h_le_V : (∫⁻ x, ENNReal.ofReal (g x) ∂ν₂) ≤ ν₂ V := by
      rw [← lintegral_indicator_one (hν₂.measurableSet_of_isOpen hV)]
      refine lintegral_mono fun x => ?_
      by_cases hxV : x ∈ V
      · simp [hxV, ENNReal.ofReal_le_one.mpr (hg_le_one x)]
      · have hx_not_supp : x ∉ tsupport (f : α → ℂ) := fun h => hxV (hfV.2.2 h)
        have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport hx_not_supp
        have hgx : g x = 0 := by simp [g, hfx]
        simp [hxV, hgx]
    exact hK_le.trans (hlint_eq.le.trans (h_le_V.trans hν₂V.le))
  have hcompact_eq : ∀ K : Set α, IsCompact K → μ₁ K = μ₂ K := fun K hK =>
    le_antisymm (hcompact_le h₁ h₂ hint hK) (hcompact_le h₂ h₁ (fun f => (hint f).symm) hK)
  have hopen_eq : ∀ V : Set α, IsOpen V → μ₁ V = μ₂ V := by
    intro V hV
    rw [h₁.2.2.2.1 V hV, h₂.2.2.2.1 V hV]
    exact iSup_congr fun K => iSup_congr fun _ => iSup_congr fun hKc => hcompact_eq K hKc
  ext E hE
  rw [h₁.2.2.1 E hE, h₂.2.2.1 E hE]
  exact iInf_congr fun V => iInf_congr fun _ => iInf_congr fun hVo => hopen_eq V hVo

/-- Underlying regular Borel measure `μ₀ : BookPositiveBorelMeasure α` constructed from a positive
complex linear functional `Λ` on `C_c(α, ℂ)` via `RealRMK.rieszMeasure`. -/
noncomputable def rieszBorelMeasure {α : Type*} [TopologicalSpace α]
    [T2Space α] [LocallyCompactSpace α]
    (Λ : LinearFunctional C_c(α, ℂ)) (hΛ : IsPositiveCcFunctional Λ) :
    BookPositiveBorelMeasure α :=
  letI : MeasurableSpace α := borel α
  haveI : BorelSpace α := ⟨rfl⟩
  RealRMK.rieszMeasure (rieszRealFunctional Λ hΛ)

/-- Completed Riesz `σ`-algebra `𝔐` (`Chapter01.completionSigma`) associated to `Λ` (`RCA 2.14`). -/
abbrev rieszSigma {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
    (Λ : LinearFunctional C_c(α, ℂ)) (hΛ : IsPositiveCcFunctional Λ) :
    MeasurableSpace α :=
  @Chapter01.completionSigma α (borel α) (rieszBorelMeasure Λ hΛ)

/-- Completed Riesz positive measure `μ` (`Chapter01.completedMeasure`) on `rieszSigma Λ hΛ`
(`RCA 2.14`). -/
noncomputable def rieszCompletedMeasure {α : Type*} [TopologicalSpace α]
    [T2Space α] [LocallyCompactSpace α]
    (Λ : LinearFunctional C_c(α, ℂ)) (hΛ : IsPositiveCcFunctional Λ) :
    @Measure α (rieszSigma Λ hΛ) :=
  @Chapter01.completedMeasure α (borel α) (rieszBorelMeasure Λ hΛ)

/-- Specification of `rieszBorelMeasure Λ hΛ`: regularity (`Book214RegularityHypotheses`) and
representation of `Λ` on all complex-valued `f ∈ C_c(α, ℂ)`. -/
theorem rieszBorelMeasure_spec {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
    (Λ : LinearFunctional C_c(α, ℂ)) (hΛ : IsPositiveCcFunctional Λ) :
    @Book214RegularityHypotheses α _ (borel α) (rieszBorelMeasure Λ hΛ) ∧
    ∀ f : C_c(α, ℂ),
      @Chapter01.BookL1 α (borel α) (rieszBorelMeasure Λ hΛ) f ∧
      Λ f = @Chapter01.BookComplexIntegral α (borel α) (rieszBorelMeasure Λ hΛ) Set.univ f ∧
      Λ f = ∫ x, f x ∂(rieszBorelMeasure Λ hΛ) := by
  let : MeasurableSpace α := borel α
  have : BorelSpace α := ⟨rfl⟩
  let μ₀ : BookPositiveBorelMeasure α := rieszBorelMeasure Λ hΛ
  have : Measure.Regular μ₀ :=
    RealRMK.regular_rieszMeasure (rieszRealFunctional Λ hΛ)
  have hreg214 : Book214RegularityHypotheses μ₀ :=
    mathlib_regular_satisfies_214 μ₀
  have : IsFiniteMeasureOnCompacts μ₀ := ⟨hreg214.2.1⟩
  have hrep : ∀ f : C_c(α, ℂ), Λ f = ∫ x, f x ∂μ₀ := by
    intro f
    have hre_int : ∫ x, reCc f x ∂μ₀ = rieszRealFunctional Λ hΛ (reCc f) :=
      RealRMK.integral_rieszMeasure (rieszRealFunctional Λ hΛ) (reCc f)
    have him_int : ∫ x, imCc f x ∂μ₀ = rieszRealFunctional Λ hΛ (imCc f) :=
      RealRMK.integral_rieszMeasure (rieszRealFunctional Λ hΛ) (imCc f)
    have hf_decomp := ofRealCc_reCc_add_imCc f
    have hΛ_val : Λ f =
        ((rieszRealFunctional Λ hΛ (reCc f) : ℝ) : ℂ) +
          Complex.I * ((rieszRealFunctional Λ hΛ (imCc f) : ℝ) : ℂ) := by
      conv_lhs => rw [hf_decomp]
      rw [map_add, map_smul, rieszRealFunctional_ofRealCc Λ hΛ, rieszRealFunctional_ofRealCc Λ hΛ]
      simp
    have hint_re : (∫ x, ofRealCc (reCc f) x ∂μ₀) = ((∫ x, reCc f x ∂μ₀ : ℝ) : ℂ) :=
      integral_ofReal
    have hint_im : (∫ x, ofRealCc (imCc f) x ∂μ₀) = ((∫ x, imCc f x ∂μ₀ : ℝ) : ℂ) :=
      integral_ofReal
    have hint_f : (∫ x, f x ∂μ₀) =
        (∫ x, ofRealCc (reCc f) x ∂μ₀) + Complex.I * ∫ x, ofRealCc (imCc f) x ∂μ₀ := by
      have hf_pt : (f : α → ℂ) =
          (fun x => ofRealCc (reCc f) x + Complex.I * ofRealCc (imCc f) x) := by
        ext x
        simpa using congrArg (fun h : C_c(α, ℂ) => h x) hf_decomp
      rw [hf_pt, integral_add (ofRealCc (reCc f)).integrable
        ((ofRealCc (imCc f)).integrable.const_mul Complex.I),
        integral_const_mul]
    rw [hΛ_val, hint_f, hint_re, hint_im, hre_int, him_int]
  refine ⟨hreg214, fun f => ?_⟩
  have hL1 : Chapter01.BookL1 μ₀ f := hreg214.bookL1_cc f
  refine ⟨hL1, ?_, hrep f⟩
  rw [Chapter01.definition_1_31 μ₀ Set.univ f hL1, Measure.restrict_univ]
  exact hrep f

/-- Borel-measure specialization of **Theorem 2.14**: existence and uniqueness of a positive Borel
measure `μ₀ : BookPositiveBorelMeasure α` satisfying `Book214RegularityHypotheses` and representing
`Λ` on all complex-valued `f ∈ C_c(α, ℂ)`. -/
theorem theorem_2_14_borel {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
    (Λ : LinearFunctional C_c(α, ℂ)) (hΛ : IsPositiveCcFunctional Λ) :
    ∃! μ₀ : BookPositiveBorelMeasure α,
      @Book214RegularityHypotheses α _ (borel α) μ₀ ∧
      ∀ f : C_c(α, ℂ),
        @Chapter01.BookL1 α (borel α) μ₀ f ∧
        Λ f = @Chapter01.BookComplexIntegral α (borel α) μ₀ Set.univ f ∧
        Λ f = ∫ x, f x ∂μ₀ := by
  let : MeasurableSpace α := borel α
  obtain ⟨hreg214, hrep⟩ := rieszBorelMeasure_spec Λ hΛ
  refine ⟨rieszBorelMeasure Λ hΛ, ⟨hreg214, hrep⟩, ?_⟩
  rintro ν ⟨hν_reg, hν_rep⟩
  exact theorem_2_14_uniqueness_on_sigma hν_reg hreg214
    fun f => (hν_rep f).2.2.symm.trans (hrep f).2.2

/-- **Theorem 2.14** (The Riesz Representation Theorem, `RCA` pp. 40–47): on a locally compact
Hausdorff space `α`, for every positive complex linear functional `Λ` on `C_c(α, ℂ)`, there exists
a `σ`-algebra `𝔐` containing `borel α` and a unique positive measure `μ` on `𝔐` such that:
- (a) `∀ f : C_c(α, ℂ)`, `f ∈ L^1(μ)` and `Λ f = ∫_α f dμ` (both `Chapter01.BookComplexIntegral`
  and Mathlib's Bochner integral);
- (b) `μ K < ∞` for every compact `K ⊆ α`;
- (c) `μ E = inf {μ V : E ⊆ V, V open}` for every `E ∈ 𝔐`;
- (d) `μ E = sup {μ K : K ⊆ E, K compact}` for every open `E` and for every `E ∈ 𝔐` with
  `μ E < ∞` (together with `borel α ≤ 𝔐` and (b)–(c), packaged as `Book214RegularityHypotheses`);
- (e) `μ` is complete on `𝔐`: if `E ∈ 𝔐`, `A ⊆ E`, and `μ E = 0`, then `A ∈ 𝔐`;
- and `μ` is unique on `𝔐` among positive measures satisfying (a) and `Book214RegularityHypotheses`. -/
theorem theorem_2_14 {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
    (Λ : LinearFunctional C_c(α, ℂ)) (hΛ : IsPositiveCcFunctional Λ) :
    ∃ (𝔐 : MeasurableSpace α) (μ : @Measure α 𝔐),
      borel α ≤ 𝔐 ∧
      @Book214RegularityHypotheses α _ 𝔐 μ ∧
      @Measure.IsComplete α 𝔐 μ ∧
      (∀ E A : Set α, @MeasurableSet α 𝔐 E → A ⊆ E → μ E = 0 → @MeasurableSet α 𝔐 A) ∧
      (∀ f : C_c(α, ℂ),
        @Chapter01.BookL1 α 𝔐 μ f ∧
        Λ f = @Chapter01.BookComplexIntegral α 𝔐 μ Set.univ f ∧
        Λ f = ∫ x, f x ∂μ) ∧
      (∀ ν : @Measure α 𝔐,
        @Book214RegularityHypotheses α _ 𝔐 ν →
        (∀ f : C_c(α, ℂ), Λ f = ∫ x, f x ∂ν) →
        ν = μ) := by
  obtain ⟨hreg₀, hrep₀⟩ := rieszBorelMeasure_spec Λ hΛ
  let 𝔐 : MeasurableSpace α := rieszSigma Λ hΛ
  let : MeasurableSpace α := 𝔐
  let μ : Measure α := rieszCompletedMeasure Λ hΛ
  have hle : borel α ≤ 𝔐 := fun _ hs =>
    @MeasurableSet.nullMeasurableSet α (borel α) (rieszBorelMeasure Λ hΛ) _ hs
  have hreg : Book214RegularityHypotheses μ :=
    @completedMeasure_preserves_214 α _ (borel α) (rieszBorelMeasure Λ hΛ) hreg₀
  have hcomp : Measure.IsComplete μ :=
    Measure.isComplete_iff.mpr fun _ hs => NullMeasurableSet.of_null hs
  have hnull_sub : ∀ E A : Set α, MeasurableSet E → A ⊆ E → μ E = 0 → MeasurableSet A :=
    fun E A hE hAE hzero =>
      (@Chapter01.theorem_1_36 α (borel α) (rieszBorelMeasure Λ hΛ)).2.2 E A hE hzero hAE
  have htrim_eq : μ.trim hle = rieszBorelMeasure Λ hΛ := by
    refine @Measure.ext α (borel α) _ _ fun s hs => ?_
    rw [trim_measurableSet_eq hle hs]
    exact @Measure.completion_apply α (borel α) (rieszBorelMeasure Λ hΛ) s
  have hrep : ∀ f : C_c(α, ℂ), Λ f = ∫ x, f x ∂μ := by
    intro f
    have hf_sm : StronglyMeasurable[borel α] (f : α → ℂ) := by
      let : MeasurableSpace α := borel α
      have : BorelSpace α := ⟨rfl⟩
      exact f.continuous.stronglyMeasurable
    have hint_trim : (∫ x, f x ∂μ) = ∫ x, f x ∂(μ.trim hle) :=
      integral_trim hle hf_sm
    rw [hint_trim, htrim_eq]
    exact (hrep₀ f).2.2
  refine ⟨𝔐, μ, hle, hreg, hcomp, hnull_sub, ?_, ?_⟩
  · intro f
    have hL1 : Chapter01.BookL1 μ f := hreg.bookL1_cc f
    refine ⟨hL1, ?_, hrep f⟩
    rw [Chapter01.definition_1_31 μ Set.univ f hL1, Measure.restrict_univ]
    exact hrep f
  · intro ν hν_reg hν_rep
    exact theorem_2_14_uniqueness_on_sigma hν_reg hreg
      fun f => (hν_rep f).symm.trans (hrep f)

end RieszRepresentation2_14

/-!
## 2.18: Automatic Borel regularity (printed p. 48)
-/

section AutomaticRegularity2_18

/-- **Theorem 2.18** (Automatic Borel regularity, `RCA` p. 48): if `α` is a locally compact
Hausdorff space in which **every open set is `σ`-compact** (without assuming pseudometrizability or
second countability), and `lam` is any positive Borel measure on `α` with `lam K < ∞` for all
compact `K ⊆ α`, then `lam` is regular in Rudin's sense (`BookRegularBorelMeasure lam`). -/
theorem theorem_2_18 {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
    (hopen : ∀ V : Set α, IsOpen V → IsSigmaCompact V)
    (lam : BookPositiveBorelMeasure α)
    (hfin : ∀ K : Set α, IsCompact K → lam K < ∞) :
    BookRegularBorelMeasure lam := by
  let : MeasurableSpace α := borel α
  have : BorelSpace α := ⟨rfl⟩
  have : IsFiniteMeasureOnCompacts lam := ⟨hfin⟩
  have : SigmaCompactSpace α := isSigmaCompact_univ_iff.mp (hopen univ isOpen_univ)
  let Λ : LinearFunctional C_c(α, ℂ) := ccIntegralFunctional lam
  have hΛ : IsPositiveCcFunctional Λ := (proposition_2_2_cc_positive lam).1
  let μ : BookPositiveBorelMeasure α := rieszBorelMeasure Λ hΛ
  obtain ⟨hμ_reg214, hμ_rep⟩ := rieszBorelMeasure_spec Λ hΛ
  have : IsFiniteMeasureOnCompacts μ := ⟨hμ_reg214.2.1⟩
  have hμ_regular : BookRegularBorelMeasure μ := by
    have htrim := (theorem_2_17 hμ_reg214).2.1.2
    have hself : μ.trim hμ_reg214.1 = μ :=
      Measure.ext fun s hs => trim_measurableSet_eq hμ_reg214.1 hs
    rwa [hself] at htrim
  have hopen_eq : ∀ V : Set α, IsOpen V → lam V = μ V := by
    intro V hV
    obtain ⟨C, hC_comp, hC_cov⟩ := hopen V hV
    have hCV : ∀ m : ℕ, C m ⊆ V := fun m => by
      rw [← hC_cov]
      exact subset_iUnion C m
    have hcut : ∀ m : ℕ, ∃ f : C_c(α, ℂ), CompactCutoff (C m) f ∧ OpenCutoff f V :=
      fun m => lemma_2_12 (hC_comp m) hV (hCV m)
    choose f hfC hfV using hcut
    let ψ : ℕ → C_c(α, ℝ) := fun m => reCc (f m)
    let g : ℕ → C_c(α, ℝ) :=
      fun n => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one ψ
    have hψ_nonneg : ∀ m x, 0 ≤ ψ m x := by
      intro m x
      rcases (hfC m).2.1 x with ⟨r, ⟨hr0, _⟩, hfx⟩
      simpa [ψ, hfx] using hr0
    have hψ_le_one : ∀ m x, ψ m x ≤ 1 := by
      intro m x
      rcases (hfC m).2.1 x with ⟨r, ⟨_, hr1⟩, hfx⟩
      simpa [ψ, hfx] using hr1
    have hψ_on_C : ∀ m, ∀ x ∈ C m, ψ m x = 1 := by
      intro m x hx
      have := (hfC m).2.2 hx
      simpa [ψ] using congrArg Complex.re this
    have hψ_out_V : ∀ m, ∀ x ∉ V, ψ m x = 0 := by
      intro m x hxV
      have hx_not : x ∉ tsupport (f m : α → ℂ) := fun h => hxV ((hfV m).2.2 h)
      have hfx : f m x = 0 := image_eq_zero_of_notMem_tsupport hx_not
      simp [ψ, hfx]
    have hg_apply : ∀ n x, g n x =
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun m => ψ m x) :=
      fun n x => CompactlySupportedContinuousMap.finsetSup'_apply
        Finset.nonempty_range_add_one ψ x
    have hg_nonneg : ∀ n x, 0 ≤ g n x := by
      intro n x
      rw [hg_apply]
      exact (hψ_nonneg 0 x).trans
        (Finset.le_sup' (fun m => ψ m x) (Finset.mem_range.mpr (Nat.zero_lt_succ n)))
    have hg_mono : Monotone (fun n x => ENNReal.ofReal (g n x)) := by
      intro n₁ n₂ hn x
      apply ENNReal.ofReal_le_ofReal
      rw [hg_apply, hg_apply]
      exact Finset.sup'_mono (fun m => ψ m x)
        (Finset.range_mono (Nat.add_le_add_right hn 1)) Finset.nonempty_range_add_one
    have hg_iSup : ∀ x, (⨆ n : ℕ, ENNReal.ofReal (g n x)) =
        V.indicator (1 : α → ℝ≥0∞) x := by
      intro x
      by_cases hxV : x ∈ V
      · have hxU : x ∈ ⋃ m, C m := hC_cov ▸ hxV
        rcases mem_iUnion.mp hxU with ⟨m₀, hxm₀⟩
        simp only [hxV, indicator_of_mem, Pi.one_apply]
        refine le_antisymm (iSup_le fun n => ?_) ?_
        · apply ENNReal.ofReal_le_one.mpr
          rw [hg_apply]
          exact Finset.sup'_le Finset.nonempty_range_add_one _ fun m _ => hψ_le_one m x
        · refine le_iSup_of_le m₀ ?_
          have hge : 1 ≤ g m₀ x := by
            rw [hg_apply, ← hψ_on_C m₀ x hxm₀]
            exact Finset.le_sup' (fun m => ψ m x) (Finset.mem_range.mpr (Nat.lt_succ_self m₀))
          have hle1 : g m₀ x ≤ 1 := by
            rw [hg_apply]
            exact Finset.sup'_le Finset.nonempty_range_add_one _ fun m _ => hψ_le_one m x
          rw [le_antisymm hle1 hge, ENNReal.ofReal_one]
      · simp only [hxV, not_false_eq_true, indicator_of_notMem]
        refine le_antisymm (iSup_le fun n => ?_) zero_le
        have hgz : g n x = 0 := by
          rw [hg_apply]
          refine le_antisymm
            (Finset.sup'_le Finset.nonempty_range_add_one _ fun m _ => (hψ_out_V m x hxV).le) ?_
          rw [← hg_apply]
          exact hg_nonneg n x
        simp [hgz]
    have hmeas_gn : ∀ n : ℕ, Measurable (fun x => ENNReal.ofReal (g n x)) :=
      fun n => ENNReal.measurable_ofReal.comp (g n).continuous.measurable
    have hlam_V : lam V = ⨆ n : ℕ, ENNReal.ofReal (∫ x, g n x ∂lam) := by
      rw [← lintegral_indicator_one hV.measurableSet]
      have hcongr : (∫⁻ x, V.indicator (1 : α → ℝ≥0∞) x ∂lam) =
          ∫⁻ x, (⨆ n : ℕ, ENNReal.ofReal (g n x)) ∂lam :=
        lintegral_congr fun x => (hg_iSup x).symm
      rw [hcongr, lintegral_iSup hmeas_gn hg_mono]
      exact iSup_congr fun n => (ofReal_integral_eq_lintegral_ofReal (g n).integrable
        (Filter.Eventually.of_forall (hg_nonneg n))).symm
    have hμ_V : μ V = ⨆ n : ℕ, ENNReal.ofReal (∫ x, g n x ∂μ) := by
      rw [← lintegral_indicator_one hV.measurableSet]
      have hcongr : (∫⁻ x, V.indicator (1 : α → ℝ≥0∞) x ∂μ) =
          ∫⁻ x, (⨆ n : ℕ, ENNReal.ofReal (g n x)) ∂μ :=
        lintegral_congr fun x => (hg_iSup x).symm
      rw [hcongr, lintegral_iSup hmeas_gn hg_mono]
      exact iSup_congr fun n => (ofReal_integral_eq_lintegral_ofReal (g n).integrable
        (Filter.Eventually.of_forall (hg_nonneg n))).symm
    rw [hlam_V, hμ_V]
    refine iSup_congr fun n => ?_
    have hc : ∫ x, ofRealCc (g n) x ∂lam = ∫ x, ofRealCc (g n) x ∂μ := (hμ_rep (ofRealCc (g n))).2.2
    have h1 : (∫ x, ofRealCc (g n) x ∂lam) = ((∫ x, g n x ∂lam : ℝ) : ℂ) := integral_ofReal
    have h2 : (∫ x, ofRealCc (g n) x ∂μ) = ((∫ x, g n x ∂μ : ℝ) : ℂ) := integral_ofReal
    rw [h1, h2] at hc
    rw [Complex.ofReal_injective hc]
  have hU_ex : ∀ n : ℕ, ∃ Un : Set α, IsOpen Un ∧ compactCovering α n ⊆ Un ∧
      IsCompact (closure Un) := by
    intro n
    obtain ⟨Un, hUn_open, hcomp, hsub, _, _⟩ :=
      theorem_2_7 isOpen_univ (subset_univ _) (isCompact_compactCovering α n)
    exact ⟨Un, hUn_open, hsub, hcomp⟩
  choose U hU_open hKU hU_comp using hU_ex
  have hU_cov : (⋃ n, U n) = univ := by
    refine eq_univ_iff_forall.mpr fun x => ?_
    have hx : x ∈ ⋃ n, compactCovering α n := by rw [iUnion_compactCovering]; trivial
    rcases mem_iUnion.mp hx with ⟨n, hxn⟩
    exact mem_iUnion.mpr ⟨n, hKU n hxn⟩
  have hrest_eq : ∀ n : ℕ, lam.restrict (U n) = μ.restrict (U n) := by
    intro n
    have hlam_Un_lt : lam (U n) < ∞ :=
      (measure_mono subset_closure).trans_lt (hfin (closure (U n)) (hU_comp n))
    have : IsFiniteMeasure (lam.restrict (U n)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hlam_Un_lt⟩
    refine ext_of_generate_finite {V : Set α | IsOpen V} rfl isPiSystem_isOpen ?_ ?_
    · intro V hV
      rw [Measure.restrict_apply hV.measurableSet, Measure.restrict_apply hV.measurableSet]
      exact hopen_eq (V ∩ U n) (hV.inter (hU_open n))
    · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
      exact hopen_eq (U n) (hU_open n)
  have hlam_eq_μ : lam = μ := by
    let D : ℕ → Set α := disjointed U
    have hD_meas : ∀ n, MeasurableSet (D n) :=
      MeasurableSet.disjointed fun n => (hU_open n).measurableSet
    have hD_disj : Pairwise (fun i j => Disjoint (D i) (D j)) := disjoint_disjointed U
    have hD_cov : (⋃ n, D n) = univ := by rw [iUnion_disjointed, hU_cov]
    ext E hE
    have hED_cov : (⋃ n, E ∩ D n) = E := by
      rw [← inter_iUnion, hD_cov, inter_univ]
    have hED_disj : Pairwise (fun i j => Disjoint (E ∩ D i) (E ∩ D j)) :=
      fun i j hij => (hD_disj hij).mono inter_subset_right inter_subset_right
    have hED_meas : ∀ n, MeasurableSet (E ∩ D n) := fun n => hE.inter (hD_meas n)
    rw [← hED_cov, measure_iUnion hED_disj hED_meas, measure_iUnion hED_disj hED_meas]
    refine tsum_congr fun n => ?_
    have hsub_Un : E ∩ D n ⊆ U n := inter_subset_right.trans (disjointed_subset U n)
    have hr := congrArg (fun m : Measure α => m (E ∩ D n)) (hrest_eq n)
    simpa [Measure.restrict_apply (hED_meas n), inter_eq_self_of_subset_left hsub_Un] using hr
  rwa [hlam_eq_μ]

/-- Remark following **Theorem 2.18** (`RCA` pp. 48–49): in any second-countable locally compact
Hausdorff space, every open set is `σ`-compact; hence every locally finite positive Borel measure
is regular in Rudin's sense. -/
theorem proposition_2_18_secondCountable {α : Type*} [TopologicalSpace α] [T2Space α]
    [LocallyCompactSpace α] [SecondCountableTopology α] :
    (∀ V : Set α, IsOpen V → IsSigmaCompact V) ∧
    (∀ lam : BookPositiveBorelMeasure α,
      (∀ K : Set α, IsCompact K → lam K < ∞) → BookRegularBorelMeasure lam) := by
  have hopen : ∀ V : Set α, IsOpen V → IsSigmaCompact V := by
    intro V hV
    let ℬ : Set (Set α) := TopologicalSpace.countableBasis α
    have hℬ_basis : TopologicalSpace.IsTopologicalBasis ℬ :=
      TopologicalSpace.isBasis_countableBasis α
    have hℬ_count : ℬ.Countable := TopologicalSpace.countable_countableBasis α
    let S : Set (Set α) := closure '' {B ∈ ℬ | closure B ⊆ V ∧ IsCompact (closure B)}
    have hS_count : S.Countable := (hℬ_count.mono fun _ h => h.1).image closure
    have hS_comp : ∀ K ∈ S, IsCompact K := by
      rintro K ⟨B, ⟨_, _, hBc⟩, rfl⟩
      exact hBc
    have hS_union : ⋃₀ S = V := by
      refine subset_antisymm ?_ ?_
      · rintro x ⟨K, ⟨B, ⟨_, hBV, _⟩, rfl⟩, hxK⟩
        exact hBV hxK
      · intro x hxV
        obtain ⟨W, hW_open, hW_comp, hxW, _, hWV⟩ :=
          theorem_2_7 hV (singleton_subset_iff.mpr hxV) isCompact_singleton
        obtain ⟨B, hBℬ, hxB, hBW⟩ := hℬ_basis.exists_subset_of_mem_open (hxW rfl) hW_open
        have hcl_sub : closure B ⊆ closure W := closure_mono hBW
        exact mem_sUnion.mpr ⟨closure B,
          ⟨B, ⟨hBℬ, hcl_sub.trans hWV, hW_comp.of_isClosed_subset isClosed_closure hcl_sub⟩, rfl⟩,
          subset_closure hxB⟩
    rw [← hS_union]
    exact isSigmaCompact_sUnion_of_isCompact hS_count hS_comp
  exact ⟨hopen, fun lam hfin => theorem_2_18 hopen lam hfin⟩

/-- Euclidean corollary of **Theorem 2.18** (`RCA` p. 49): on `ℝ^k`, every open set is `σ`-compact
and every positive Borel measure finite on compact sets is regular. -/
theorem proposition_2_18_euclidean (k : ℕ) :
    (∀ V : Set (EuclideanSpace ℝ (Fin k)), IsOpen V → IsSigmaCompact V) ∧
    (∀ lam : BookPositiveBorelMeasure (EuclideanSpace ℝ (Fin k)),
      (∀ K : Set (EuclideanSpace ℝ (Fin k)), IsCompact K → lam K < ∞) →
        BookRegularBorelMeasure lam) :=
  proposition_2_18_secondCountable

end AutomaticRegularity2_18

/-!
## 2.20: Lebesgue measure package on `ℝ^k` (printed pp. 50–52)
-/

section LebesgueMeasurePackage2_20

open scoped NNReal

/-- Transport of a measure on a `[BorelSpace α]` to `BookPositiveBorelMeasure α` (`@Measure α (borel α)`)
via `Measure.trim`, agreeing definitionally on every Borel set without `Eq.rec`. -/
def toBorelMeasure {α : Type*} [TopologicalSpace α] [m : MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) : BookPositiveBorelMeasure α :=
  μ.trim (le_of_eq BorelSpace.measurable_eq.symm)

theorem toBorelMeasure_apply {α : Type*} [TopologicalSpace α] [m : MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) {E : Set α} (hE : @MeasurableSet α (borel α) E) :
    toBorelMeasure μ E = μ E :=
  trim_measurableSet_eq (le_of_eq BorelSpace.measurable_eq.symm) hE

/-- **Theorem 2.20** (Lebesgue measure on `ℝ^k`, `RCA` pp. 50–52): `(lebesgueSigma k, lebesgueMeasure k)`
is a positive complete measure `(𝔐, m)` on `ℝ^k = EuclideanSpace ℝ (Fin k)` satisfying all five
printed clauses:
- (a) `m(W) = vol(W)` for every `k`-cell `W` under **all `4^k` endpoint boundary conventions**;
- (b) `borel (ℝ^k) ≤ 𝔐`, `E ∈ 𝔐` **if and only if** `∃ A B`, `IsFSigma A`, `IsGδ B`, `A ⊆ E ⊆ B`,
  and `m(B \ A) = 0`, and `m` is regular (both `Book214RegularityHypotheses` and setwise outer+inner
  regularity on all `E ∈ 𝔐`, plus `BookRegularBorelMeasure` on `borel (ℝ^k)`);
- (c) `m` is translation-invariant (`E + x ∈ 𝔐 ↔ E ∈ 𝔐` and `m(E + x) = m(E)`);
- (d) every translation-invariant positive Borel measure `μ` on `ℝ^k` with `μ(K) < ∞` on compact
  sets is a nonnegative constant multiple `c • m` (`μ E = c * m E` on all Borel sets);
- (e) for every linear map `T : ℝ^k →ₗ[ℝ] ℝ^k` there exists `Δ(T) ≥ 0` (`= |det T|`) such that
  `T(E) ∈ 𝔐` and `m(T(E)) = Δ(T) · m(E)` for every `E ∈ 𝔐`, and in particular `m(U(E)) = m(E)`
  for every orthogonal transformation / linear isometry equivalence `U`. -/
theorem theorem_2_20 (k : ℕ) :
    @Measure.IsComplete (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) (lebesgueMeasure k) ∧
    -- (a) Cell volume for all 4^k boundary conventions
    (∀ (kinds : Fin k → CellIntervalKind) (a b : Fin k → ℝ),
      @MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) (kCell kinds a b) ∧
      lebesgueMeasure k (kCell kinds a b) = ENNReal.ofReal (cellVolume a b)) ∧
    -- (b) Borel containment, iff F_σ / G_δ sandwich characterization, and full regularity
    (borel (EuclideanSpace ℝ (Fin k)) ≤ lebesgueSigma k ∧
      (∀ E : Set (EuclideanSpace ℝ (Fin k)),
        @MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) E ↔
          ∃ A B : Set (EuclideanSpace ℝ (Fin k)),
            Chapter01.IsFSigma A ∧ IsGδ B ∧ A ⊆ E ∧ E ⊆ B ∧ lebesgueMeasure k (B \ A) = 0) ∧
      @Book214RegularityHypotheses (EuclideanSpace ℝ (Fin k)) _ (lebesgueSigma k)
        (lebesgueMeasure k) ∧
      (∀ E : Set (EuclideanSpace ℝ (Fin k)),
        @MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) E →
          @BookOuterRegularSet (EuclideanSpace ℝ (Fin k)) _ (lebesgueSigma k)
            (lebesgueMeasure k) E ∧
          @BookInnerRegularSet (EuclideanSpace ℝ (Fin k)) _ (lebesgueSigma k)
            (lebesgueMeasure k) E) ∧
      BookRegularBorelMeasure (toBorelMeasure (volume : Measure (EuclideanSpace ℝ (Fin k))))) ∧
    -- (c) Translation invariance
    (∀ (x : EuclideanSpace ℝ (Fin k)) (E : Set (EuclideanSpace ℝ (Fin k))),
      (@MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) ((· + x) '' E) ↔
        @MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) E) ∧
      lebesgueMeasure k ((· + x) '' E) = lebesgueMeasure k E) ∧
    -- (d) Uniqueness up to constant multiple among locally finite translation-invariant Borel measures
    (∀ μ : BookPositiveBorelMeasure (EuclideanSpace ℝ (Fin k)),
      (∀ K : Set (EuclideanSpace ℝ (Fin k)), IsCompact K → μ K < ∞) →
      (∀ (x : EuclideanSpace ℝ (Fin k)) (E : Set (EuclideanSpace ℝ (Fin k))),
        @MeasurableSet (EuclideanSpace ℝ (Fin k)) (borel (EuclideanSpace ℝ (Fin k))) E →
          μ ((· + x) '' E) = μ E) →
      ∃ c : ℝ≥0,
        μ = c • toBorelMeasure (volume : Measure (EuclideanSpace ℝ (Fin k))) ∧
        ∀ E : Set (EuclideanSpace ℝ (Fin k)),
          @MeasurableSet (EuclideanSpace ℝ (Fin k)) (borel (EuclideanSpace ℝ (Fin k))) E →
            μ E = (c : ℝ≥0∞) * lebesgueMeasure k E) ∧
    -- (e) Linear transformations and orthogonal / isometric transformations
    ((∀ T : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      ∃ Δ : ℝ, 0 ≤ Δ ∧
        ∀ E : Set (EuclideanSpace ℝ (Fin k)),
          @MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) E →
            @MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) (T '' E) ∧
            lebesgueMeasure k (T '' E) = ENNReal.ofReal Δ * lebesgueMeasure k E) ∧
      (∀ U : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
        ∀ E : Set (EuclideanSpace ℝ (Fin k)),
          @MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) E →
            @MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) (U '' E) ∧
            lebesgueMeasure k (U '' E) = lebesgueMeasure k E)) := by
  let E_k := EuclideanSpace ℝ (Fin k)
  have happly : ∀ S : Set E_k, lebesgueMeasure k S = (volume : Measure E_k) S :=
    fun S => Measure.completion_apply _ S
  have hcomp : @Measure.IsComplete E_k (lebesgueSigma k) (lebesgueMeasure k) :=
    @Measure.isComplete_iff E_k (lebesgueSigma k) (lebesgueMeasure k) |>.mpr
      fun _ hs => NullMeasurableSet.of_null hs
  have hreg_vol : Book214RegularityHypotheses (volume : Measure E_k) :=
    mathlib_regular_satisfies_214 (volume : Measure E_k)
  have hreg_leb : @Book214RegularityHypotheses E_k _ (lebesgueSigma k) (lebesgueMeasure k) :=
    completedMeasure_preserves_214 hreg_vol
  have h217 := @theorem_2_17 E_k _ _ _ _ (lebesgueSigma k) (lebesgueMeasure k) hreg_leb
  refine ⟨hcomp, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a)
    intro kinds a b
    refine ⟨(measurableSet_kCell kinds a b).nullMeasurableSet, ?_⟩
    rw [happly, proposition_2_19_cell_volume]
  · -- (b)
    refine ⟨hreg_leb.1, ?_, hreg_leb, h217.2.1.1, ?_⟩
    · intro E
      constructor
      · intro hE
        exact h217.2.2 E hE
      · rintro ⟨A, B, hA_fs, hB_gd, hAE, hEB, hnull⟩
        have hA_meas : MeasurableSet A := by
          rcases hA_fs with ⟨F, hF_closed, rfl⟩
          exact MeasurableSet.iUnion fun n => (hF_closed n).measurableSet
        have hB_meas : MeasurableSet B := hB_gd.measurableSet
        rw [happly] at hnull
        exact ((Chapter01.theorem_1_36 (volume : Measure E_k)).1 E).mpr
          ⟨A, B, hA_meas, hB_meas, hAE, hEB, hnull⟩
    · have htrim_eq : @Measure.trim E_k (borel E_k) (lebesgueSigma k) (lebesgueMeasure k)
          hreg_leb.1 = toBorelMeasure (volume : Measure E_k) := by
        have htb : ∀ {s : Set E_k}, @MeasurableSet E_k (borel E_k) s →
            toBorelMeasure (volume : Measure E_k) s = (volume : Measure E_k) s :=
          fun hs => toBorelMeasure_apply (volume : Measure E_k) hs
        let : MeasurableSpace E_k := lebesgueSigma k
        refine @Measure.ext E_k (borel E_k) _ _ fun s hs => ?_
        rw [trim_measurableSet_eq hreg_leb.1 hs, htb hs, happly]
      simpa [htrim_eq] using h217.2.1.2
  · -- (c)
    intro x E
    have hshift_pres : ∀ (y : E_k) {S : Set E_k},
        @MeasurableSet E_k (lebesgueSigma k) S →
          @MeasurableSet E_k (lebesgueSigma k) ((· + y) '' S) := by
      intro y S hS
      change NullMeasurableSet S volume at hS
      change NullMeasurableSet ((· + y) '' S) volume
      rw [image_add_right]
      exact hS.preimage (measurePreserving_add_right volume (-y)).quasiMeasurePreserving
    refine ⟨⟨fun hEx => ?_, hshift_pres x⟩, ?_⟩
    · have hback := hshift_pres (-x) hEx
      have heq : (· + (-x)) '' ((· + x) '' E) = E := by
        ext z
        simp only [mem_image]
        constructor
        · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
          simpa [add_assoc] using hu
        · intro hz
          exact ⟨z + x, ⟨z, hz, rfl⟩, by abel⟩
      rwa [heq] at hback
    · rw [happly, happly, image_add_right, measure_preimage_add_right]
  · -- (d)
    intro μ hK_fin htrans
    have htb : ∀ {s : Set E_k}, @MeasurableSet E_k (borel E_k) s →
        toBorelMeasure (volume : Measure E_k) s = (volume : Measure E_k) s :=
      fun hs => toBorelMeasure_apply (volume : Measure E_k) hs
    let m_std : MeasurableSpace E_k := inferInstance
    have hle1 : m_std ≤ borel E_k := le_of_eq BorelSpace.measurable_eq
    let μ' : Measure E_k := @Measure.trim E_k m_std (borel E_k) μ hle1
    have hμ'_apply : ∀ {E : Set E_k}, MeasurableSet E → μ' E = μ E := by
      intro E hE
      let : MeasurableSpace E_k := borel E_k
      exact trim_measurableSet_eq hle1 hE
    have : IsFiniteMeasureOnCompacts μ' := by
      refine ⟨fun K hK => ?_⟩
      rw [hμ'_apply hK.measurableSet]
      exact hK_fin K hK
    have : Measure.IsAddLeftInvariant μ' := by
      refine ⟨fun g => ?_⟩
      ext E hE
      rw [Measure.map_apply (measurable_const_add g) hE]
      have hpre : (g + ·) ⁻¹' E = (· + (-g)) '' E := by
        ext y
        simp only [mem_preimage, mem_image]
        constructor
        · intro hy
          exact ⟨g + y, hy, by abel⟩
        · rintro ⟨z, hz, rfl⟩
          simpa [add_assoc] using hz
      have hEb : @MeasurableSet E_k (borel E_k) E := hle1 E hE
      have hpre_m : MeasurableSet ((g + ·) ⁻¹' E) := (measurable_const_add g) hE
      rw [hμ'_apply hpre_m, hμ'_apply hE, hpre]
      exact htrans (-g) E hEb
    have hsmul : μ' = Measure.addHaarScalarFactor μ' (volume : Measure E_k) •
        (volume : Measure E_k) :=
      Measure.isAddLeftInvariant_eq_smul μ' (volume : Measure E_k)
    let c : ℝ≥0 := Measure.addHaarScalarFactor μ' (volume : Measure E_k)
    have hval : ∀ E : Set E_k, @MeasurableSet E_k (borel E_k) E →
        μ E = (c : ℝ≥0∞) * lebesgueMeasure k E := by
      intro E hEb
      have hE_std : MeasurableSet E := (le_of_eq BorelSpace.measurable_eq.symm) E hEb
      rw [← hμ'_apply hE_std, hsmul, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, happly]
    refine ⟨c, ?_, hval⟩
    let : MeasurableSpace E_k := borel E_k
    ext E hEb
    rw [hval E hEb, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, htb hEb, happly]
  · -- (e)
    refine ⟨?_, ?_⟩
    · intro T
      exact ⟨|LinearMap.det T|, abs_nonneg _, (proposition_2_23_det_scale_factor T).2.1⟩
    · intro U E hE
      change NullMeasurableSet E volume at hE
      have hmp : MeasurePreserving U.symm (volume : Measure E_k) (volume : Measure E_k) :=
        LinearIsometryEquiv.measurePreserving U.symm
      have himg : (U : E_k → E_k) '' E = U.symm ⁻¹' E := U.toEquiv.image_eq_preimage_symm E
      refine ⟨?_, ?_⟩
      · change NullMeasurableSet (U '' E) volume
        rw [himg]
        exact hE.preimage hmp.quasiMeasurePreserving
      · rw [happly, happly, himg]
        exact hmp.measure_preimage_emb U.symm.toHomeomorph.measurableEmbedding E

end LebesgueMeasurePackage2_20

/-!
## 2.22: Nonmeasurable subsets (Vitali transversal, printed p. 53)
-/

section NonmeasurableSubsets2_22

/-- Completed Lebesgue `σ`-algebra `𝔐` on `ℝ` (`RCA 2.20` / `2.22`, `k = 1`). -/
abbrev realLebesgueSigma : MeasurableSpace ℝ :=
  Chapter01.completionSigma (volume : Measure ℝ)

/-- Completed Lebesgue measure `m` on `ℝ` (`RCA 2.20` / `2.22`, `k = 1`). -/
def realLebesgueMeasure : @Measure ℝ realLebesgueSigma :=
  Chapter01.completedMeasure (volume : Measure ℝ)

/-- Equivalence relation on `ℝ` identifying real numbers whose difference is rational
(`RCA 2.22`, p. 53). -/
def ratDiffSetoid : Setoid ℝ where
  r x y := ∃ q : ℚ, x - y = (q : ℝ)
  iseqv :=
    { refl := fun x => ⟨0, by simp⟩
      symm := by
        rintro x y ⟨q, hq⟩
        exact ⟨-q, by push_cast; linarith⟩
      trans := by
        rintro x y z ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩
        exact ⟨q₁ + q₂, by push_cast; linarith⟩ }

/-- Vitali transversal `E_0 ⊂ ℝ` choosing one representative from each `ℚ`-coset of `ℝ`
(`RCA 2.22`, p. 53). -/
def vitaliTransversal : Set ℝ :=
  range (Quotient.out (s := ratDiffSetoid))

private theorem ennreal_eq_zero_of_tsum_const_lt_top {c : ℝ≥0∞}
    (h : (∑' _ : ℕ, c) < ∞) : c = 0 := by
  by_contra hc
  have hc_top : c ≠ ∞ := ((ENNReal.le_tsum (f := fun _ : ℕ => c) 0).trans_lt h).ne
  have hδ : 0 < c.toReal := ENNReal.toReal_pos hc hc_top
  let S : ℝ := (∑' _ : ℕ, c).toReal
  obtain ⟨M, hM⟩ := exists_nat_gt (S / c.toReal)
  have hgt : S < (M : ℝ) * c.toReal := (div_lt_iff₀ hδ).mp hM
  have hsum : (M : ℝ≥0∞) * c ≤ ∑' _ : ℕ, c := by
    simpa using ENNReal.sum_le_tsum (f := fun _ : ℕ => c) (Finset.range M)
  have hle : ((M : ℝ≥0∞) * c).toReal ≤ S := ENNReal.toReal_mono h.ne hsum
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hle
  linarith

/-- `RCA 2.22` (p. 53, `NullMeasurableSet` form): if `A ⊆ ℝ` and every subset `E ⊆ A` is Lebesgue
measurable, then `A` is Lebesgue measurable and has Lebesgue measure `0`. -/
theorem theorem_2_22_nullMeasurable (A : Set ℝ)
    (hA : ∀ E : Set ℝ, E ⊆ A → NullMeasurableSet E (volume : Measure ℝ)) :
    NullMeasurableSet A (volume : Measure ℝ) ∧ (volume : Measure ℝ) A = 0 := by
  refine ⟨hA A Subset.rfl, ?_⟩
  have hcover : A ⊆ ⋃ q : ℚ, (A ∩ ((· + (q : ℝ)) '' vitaliTransversal)) := by
    intro x hxA
    let c : Quotient ratDiffSetoid := Quotient.mk ratDiffSetoid x
    let e : ℝ := Quotient.out c
    have he_mem : e ∈ vitaliTransversal := ⟨c, rfl⟩
    have hrel : ratDiffSetoid.r e x := Quotient.exact (Quotient.out_eq c)
    obtain ⟨q, hq⟩ := hrel
    refine mem_iUnion.mpr ⟨-q, hxA, e, he_mem, ?_⟩
    push_cast
    linarith
  refine measure_mono_null hcover (measure_iUnion_null_iff.mpr fun q => ?_)
  let B : Set ℝ := A ∩ ((· + (q : ℝ)) '' vitaliTransversal)
  have hB_cover : B ⊆ ⋃ N : ℕ, (B ∩ Icc (-(N : ℝ)) (N : ℝ)) := by
    intro x hxB
    obtain ⟨N, hN⟩ := exists_nat_ge |x|
    exact mem_iUnion.mpr ⟨N, hxB, abs_le.mp hN⟩
  refine measure_mono_null hB_cover (measure_iUnion_null_iff.mpr fun N => ?_)
  let C : Set ℝ := B ∩ Icc (-(N : ℝ)) (N : ℝ)
  have hC_meas : NullMeasurableSet C (volume : Measure ℝ) :=
    hA C (inter_subset_left.trans inter_subset_left)
  let r : ℕ → ℚ := fun n => 1 / ((n : ℚ) + 2)
  have hr_bounds : ∀ n : ℕ, 0 ≤ (r n : ℝ) ∧ (r n : ℝ) ≤ 1 := by
    intro n
    have h1 : (r n : ℝ) = 1 / ((n : ℝ) + 2) := by simp [r]
    rw [h1]
    exact ⟨by positivity,
      div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)⟩
  have hr_inj : Function.Injective r := by
    intro n m hnm
    have hreal : (r n : ℝ) = (r m : ℝ) := congrArg (fun x : ℚ => (x : ℝ)) hnm
    simp only [r, Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_ofNat] at hreal
    have hn_pos : ((n : ℝ) + 2) ≠ 0 := by positivity
    have hm_pos : ((m : ℝ) + 2) ≠ 0 := by positivity
    field_simp [hn_pos, hm_pos] at hreal
    exact Nat.cast_inj.mp (by linarith : (n : ℝ) = (m : ℝ))
  let T : ℕ → Set ℝ := fun n => (· + (r n : ℝ)) '' C
  have hT_disj : Pairwise (Function.onFun Disjoint T) := by
    intro n m hnm
    rw [Function.onFun, Set.disjoint_left]
    intro z hzn hzm
    rcases hzn with ⟨x, hxC, rfl⟩
    rcases hzm with ⟨y, hyC, hyz⟩
    rcases hxC.1.2 with ⟨e₁, ⟨c₁, rfl⟩, rfl⟩
    rcases hyC.1.2 with ⟨e₂, ⟨c₂, rfl⟩, rfl⟩
    have hdiff : ratDiffSetoid.r (Quotient.out c₁) (Quotient.out c₂) := by
      refine ⟨r m - r n, ?_⟩
      push_cast
      linarith
    have hc_eq : c₁ = c₂ := by
      rw [← Quotient.out_eq c₁, ← Quotient.out_eq c₂]
      exact Quotient.sound hdiff
    subst hc_eq
    have hr_eq : (r n : ℝ) = (r m : ℝ) := by linarith
    exact hnm (hr_inj (Rat.cast_inj.mp hr_eq))
  have hT_meas : ∀ n : ℕ, NullMeasurableSet (T n) (volume : Measure ℝ) := by
    intro n
    dsimp [T]
    rw [image_add_right]
    exact hC_meas.preimage
      (measurePreserving_add_right (volume : Measure ℝ) (-(r n : ℝ))).quasiMeasurePreserving
  have hT_vol : ∀ n : ℕ, (volume : Measure ℝ) (T n) = (volume : Measure ℝ) C := by
    intro n
    dsimp [T]
    rw [image_add_right, measure_preimage_add_right]
  have hT_sub : (⋃ n : ℕ, T n) ⊆ Icc (-(N : ℝ)) ((N : ℝ) + 1) := by
    intro z hz
    rcases mem_iUnion.mp hz with ⟨n, x, hxC, rfl⟩
    have hxI := hxC.2
    have hrb := hr_bounds n
    exact ⟨by linarith [hxI.1, hrb.1], by linarith [hxI.2, hrb.2]⟩
  have htsum_lt : (∑' _ : ℕ, (volume : Measure ℝ) C) < ∞ := by
    rw [← tsum_congr hT_vol,
      ← measure_iUnion₀ (fun n m hnm => (hT_disj hnm).aedisjoint) hT_meas]
    calc
      (volume : Measure ℝ) (⋃ n : ℕ, T n)
          ≤ (volume : Measure ℝ) (Icc (-(N : ℝ)) ((N : ℝ) + 1)) := measure_mono hT_sub
      _ = ENNReal.ofReal (((N : ℝ) + 1) - (-(N : ℝ))) := Real.volume_Icc
      _ < ∞ := ENNReal.ofReal_lt_top
  exact ennreal_eq_zero_of_tsum_const_lt_top htsum_lt

/-- `RCA 2.22` (Theorem, p. 53): if `A ⊆ ℝ` and every subset of `A` is Lebesgue measurable
(in the completed Lebesgue `σ`-algebra `realLebesgueSigma`), then `m(A) = 0`. -/
theorem theorem_2_22 (A : Set ℝ)
    (hA : ∀ E : Set ℝ, E ⊆ A → @MeasurableSet ℝ realLebesgueSigma E) :
    @MeasurableSet ℝ realLebesgueSigma A ∧
    realLebesgueMeasure A = 0 ∧
    (volume : Measure ℝ) A = 0 := by
  obtain ⟨hAm, hvol⟩ := theorem_2_22_nullMeasurable A hA
  refine ⟨hAm, ?_, hvol⟩
  change (volume : Measure ℝ).completion A = 0
  rwa [Measure.completion_apply]

/-- `RCA 2.22` (Corollary, p. 53): every set of positive Lebesgue measure in `ℝ` has a
non-Lebesgue-measurable subset. -/
theorem theorem_2_22_corollary (A : Set ℝ) (hpos : 0 < realLebesgueMeasure A) :
    ∃ E : Set ℝ, E ⊆ A ∧ ¬ @MeasurableSet ℝ realLebesgueSigma E := by
  by_contra h_all
  have hall' : ∀ E : Set ℝ, E ⊆ A → @MeasurableSet ℝ realLebesgueSigma E := by
    intro E hEA
    by_contra hE
    exact h_all ⟨E, hEA, hE⟩
  exact hpos.ne' (theorem_2_22 A hall').2.1

/-- `RCA 2.22` (Corollary, `NullMeasurableSet` form): every `A ⊆ ℝ` with `0 < volume A` contains
a subset that is not Lebesgue measurable. -/
theorem theorem_2_22_corollary_nullMeasurable (A : Set ℝ) (hpos : 0 < (volume : Measure ℝ) A) :
    ∃ E : Set ℝ, E ⊆ A ∧ ¬ NullMeasurableSet E (volume : Measure ℝ) := by
  have hpos' : 0 < realLebesgueMeasure A := by
    change 0 < (volume : Measure ℝ).completion A
    rwa [Measure.completion_apply]
  exact theorem_2_22_corollary A hpos'

/-- Equivalence relation on `ℝ^k` identifying vectors whose coordinatewise differences are rational
(`RCA 2.22` higher-dimensional extension). -/
def ratVecSetoid (k : ℕ) : Setoid (EuclideanSpace ℝ (Fin k)) where
  r x y := ∀ i : Fin k, ∃ q : ℚ, x i - y i = (q : ℝ)
  iseqv :=
    { refl := fun x _ => ⟨0, by simp⟩
      symm := by
        intro x y hxy i
        obtain ⟨q, hq⟩ := hxy i
        exact ⟨-q, by push_cast; linarith⟩
      trans := by
        intro x y z hxy hyz i
        obtain ⟨q₁, hq₁⟩ := hxy i
        obtain ⟨q₂, hq₂⟩ := hyz i
        exact ⟨q₁ + q₂, by push_cast; linarith⟩ }

/-- Vitali transversal choosing one representative from each `(ℚ^k)`-coset of `ℝ^k`. -/
def vitaliVecTransversal (k : ℕ) : Set (EuclideanSpace ℝ (Fin k)) :=
  range (Quotient.out (s := ratVecSetoid k))

/-- Embedding `ℚ^k → ℝ^k = EuclideanSpace ℝ (Fin k)`. -/
def embedRatVec {k : ℕ} (q : Fin k → ℚ) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => (q i : ℝ))

/-- `RCA 2.22` on `ℝ^k` (`k ≥ 1`): if every subset of `A ⊆ ℝ^k` is completed Lebesgue measurable,
then `m(A) = 0`. -/
theorem theorem_2_22_euclidean {k : ℕ} (hk : 1 ≤ k) (A : Set (EuclideanSpace ℝ (Fin k)))
    (hA : ∀ E : Set (EuclideanSpace ℝ (Fin k)), E ⊆ A →
      @MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) E) :
    @MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) A ∧
    lebesgueMeasure k A = 0 := by
  let E_k := EuclideanSpace ℝ (Fin k)
  refine ⟨hA A Subset.rfl, ?_⟩
  change (volume : Measure E_k).completion A = 0
  rw [Measure.completion_apply]
  have hcover : A ⊆ ⋃ q : Fin k → ℚ, (A ∩ ((· + embedRatVec q) '' vitaliVecTransversal k)) := by
    intro x hxA
    let c : Quotient (ratVecSetoid k) := Quotient.mk (ratVecSetoid k) x
    let e : E_k := Quotient.out c
    have he_mem : e ∈ vitaliVecTransversal k := ⟨c, rfl⟩
    have hrel : (ratVecSetoid k).r e x := Quotient.exact (Quotient.out_eq c)
    choose q hq using hrel
    refine mem_iUnion.mpr ⟨fun i => -q i, hxA, e, he_mem, ?_⟩
    ext i
    have hi : (e + embedRatVec (fun j => -q j)) i = e i + ((-q i : ℚ) : ℝ) := rfl
    rw [hi]
    push_cast
    linarith [hq i]
  refine measure_mono_null hcover (measure_iUnion_null_iff.mpr fun q => ?_)
  let B : Set E_k := A ∩ ((· + embedRatVec q) '' vitaliVecTransversal k)
  have hB_cover : B ⊆ ⋃ N : ℕ,
      (B ∩ closedKCell (fun _ : Fin k => -(N : ℝ)) (fun _ : Fin k => (N : ℝ))) := by
    intro x hxB
    obtain ⟨N, hN⟩ := exists_nat_ge (∑ j : Fin k, |x j|)
    refine mem_iUnion.mpr ⟨N, hxB, fun i => ?_⟩
    have hxi : |x i| ≤ (N : ℝ) :=
      (Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)).trans hN
    exact abs_le.mp hxi
  refine measure_mono_null hB_cover (measure_iUnion_null_iff.mpr fun N => ?_)
  let C : Set E_k := B ∩ closedKCell (fun _ : Fin k => -(N : ℝ)) (fun _ : Fin k => (N : ℝ))
  have hC_meas : NullMeasurableSet C (volume : Measure E_k) :=
    hA C (inter_subset_left.trans inter_subset_left)
  let i₀ : Fin k := ⟨0, hk⟩
  let r : ℕ → ℚ := fun n => 1 / ((n : ℚ) + 2)
  let rVec : ℕ → E_k := fun n => embedRatVec (fun _ => r n)
  have hr_bounds : ∀ n : ℕ, 0 ≤ (r n : ℝ) ∧ (r n : ℝ) ≤ 1 := by
    intro n
    have h1 : (r n : ℝ) = 1 / ((n : ℝ) + 2) := by simp [r]
    rw [h1]
    exact ⟨by positivity,
      div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)⟩
  have hr_inj : Function.Injective r := by
    intro n m hnm
    have hreal : (r n : ℝ) = (r m : ℝ) := congrArg (fun x : ℚ => (x : ℝ)) hnm
    simp only [r, Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_ofNat] at hreal
    have hn_pos : ((n : ℝ) + 2) ≠ 0 := by positivity
    have hm_pos : ((m : ℝ) + 2) ≠ 0 := by positivity
    field_simp [hn_pos, hm_pos] at hreal
    exact Nat.cast_inj.mp (by linarith : (n : ℝ) = (m : ℝ))
  let T : ℕ → Set E_k := fun n => (· + rVec n) '' C
  have hT_disj : Pairwise (Function.onFun Disjoint T) := by
    intro n m hnm
    rw [Function.onFun, Set.disjoint_left]
    intro z hzn hzm
    rcases hzn with ⟨x, hxC, rfl⟩
    rcases hzm with ⟨y, hyC, hyz⟩
    rcases hxC.1.2 with ⟨e₁, ⟨c₁, rfl⟩, rfl⟩
    rcases hyC.1.2 with ⟨e₂, ⟨c₂, rfl⟩, rfl⟩
    have hdiff : (ratVecSetoid k).r (Quotient.out c₁) (Quotient.out c₂) := by
      intro i
      refine ⟨r m - r n, ?_⟩
      have hi := congrArg (fun v : E_k => v i) hyz.symm
      change (Quotient.out c₁ i + (q i : ℝ)) + (r n : ℝ) =
          (Quotient.out c₂ i + (q i : ℝ)) + (r m : ℝ) at hi
      push_cast
      linarith
    have hc_eq : c₁ = c₂ := by
      rw [← Quotient.out_eq c₁, ← Quotient.out_eq c₂]
      exact Quotient.sound hdiff
    subst hc_eq
    have hi₀ := congrArg (fun v : E_k => v i₀) hyz.symm
    change (Quotient.out c₁ i₀ + (q i₀ : ℝ)) + (r n : ℝ) =
        (Quotient.out c₁ i₀ + (q i₀ : ℝ)) + (r m : ℝ) at hi₀
    have hr_eq : (r n : ℝ) = (r m : ℝ) := by linarith
    exact hnm (hr_inj (Rat.cast_inj.mp hr_eq))
  have hT_meas : ∀ n : ℕ, NullMeasurableSet (T n) (volume : Measure E_k) := by
    intro n
    dsimp [T]
    rw [image_add_right]
    exact hC_meas.preimage
      (measurePreserving_add_right (volume : Measure E_k) (-(rVec n))).quasiMeasurePreserving
  have hT_vol : ∀ n : ℕ, (volume : Measure E_k) (T n) = (volume : Measure E_k) C := by
    intro n
    dsimp [T]
    rw [image_add_right, measure_preimage_add_right]
  have hT_sub : (⋃ n : ℕ, T n) ⊆
      closedKCell (fun _ : Fin k => -(N : ℝ)) (fun _ : Fin k => (N : ℝ) + 1) := by
    intro z hz i
    rcases mem_iUnion.mp hz with ⟨n, x, hxC, rfl⟩
    have hxI : x i ∈ Icc (-(N : ℝ)) (N : ℝ) := hxC.2 i
    have hrb := hr_bounds n
    have hzi : (x + rVec n) i = x i + (r n : ℝ) := rfl
    rw [cellCoordInterval, hzi]
    exact ⟨by linarith [hxI.1, hrb.1], by linarith [hxI.2, hrb.2]⟩
  have htsum_lt : (∑' _ : ℕ, (volume : Measure E_k) C) < ∞ := by
    rw [← tsum_congr hT_vol,
      ← measure_iUnion₀ (fun n m hnm => (hT_disj hnm).aedisjoint) hT_meas]
    calc
      (volume : Measure E_k) (⋃ n : ℕ, T n)
          ≤ (volume : Measure E_k)
              (closedKCell (fun _ : Fin k => -(N : ℝ)) (fun _ : Fin k => (N : ℝ) + 1)) :=
            measure_mono hT_sub
      _ = ENNReal.ofReal
            (cellVolume (fun _ : Fin k => -(N : ℝ)) (fun _ : Fin k => (N : ℝ) + 1)) := by
            rw [closedKCell, proposition_2_19_cell_volume]
      _ < ∞ := ENNReal.ofReal_lt_top
  exact ennreal_eq_zero_of_tsum_const_lt_top htsum_lt

/-- `RCA 2.22` (Corollary on `ℝ^k`, `k ≥ 1`): every subset of `ℝ^k` of positive Lebesgue measure
contains a non-Lebesgue-measurable subset. -/
theorem theorem_2_22_corollary_euclidean {k : ℕ} (hk : 1 ≤ k)
    (A : Set (EuclideanSpace ℝ (Fin k))) (hpos : 0 < lebesgueMeasure k A) :
    ∃ E : Set (EuclideanSpace ℝ (Fin k)), E ⊆ A ∧
      ¬ @MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) E := by
  by_contra h_all
  have hall' : ∀ E : Set (EuclideanSpace ℝ (Fin k)), E ⊆ A →
      @MeasurableSet (EuclideanSpace ℝ (Fin k)) (lebesgueSigma k) E := by
    intro E hEA
    by_contra hE
    exact h_all ⟨E, hEA, hE⟩
  exact hpos.ne' (theorem_2_22_euclidean hk A hall').2

end NonmeasurableSubsets2_22

/-!
## 2.24: Lusin's theorem and bounded a.e. approximation corollary (printed pp. 55–56)
-/

section LusinApproximation2_24

open BoundedContinuousFunction

private theorem tietze_cutoff_extension {α : Type*} [TopologicalSpace α] [T2Space α]
    {K V : Set α} (hK : IsCompact K) (hV_open : IsOpen V) (hV_comp : IsCompact (closure V))
    (hKV : K ⊆ V) (φ : C_c(α, ℂ)) (hφ_norm : ∀ x, ‖φ x‖ ≤ 1) (hφ_one : EqOn φ 1 K)
    (hφ_supp : tsupport φ ⊆ V) (f : α → ℂ) (hfK : ContinuousOn f K) {M : ℝ} (hM0 : 0 ≤ M)
    (hfM : ∀ x ∈ K, ‖f x‖ ≤ M) :
    ∃ g : C_c(α, ℂ), (∀ x : α, ‖g x‖ ≤ M) ∧ (∀ x ∈ K, g x = f x) ∧ (∀ x ∉ V, g x = 0) := by
  let Y := ↥(closure V)
  have : CompactSpace Y := isCompact_iff_compactSpace.mp hV_comp
  let s : Set Y := ((↑) : Y → α) ⁻¹' K
  have hs_closed : IsClosed s := hK.isClosed.preimage continuous_subtype_val
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs_closed.isCompact
  have hf_cont_s : Continuous (fun z : s => f z.1.1) :=
    hfK.comp_continuous (continuous_subtype_val.comp continuous_subtype_val) (fun z => z.2)
  let f₀ : s →ᵇ ℂ := mkOfCompact ⟨fun z : s => f z.1.1, hf_cont_s⟩
  have hf₀_norm : ‖f₀‖ ≤ M := (norm_le hM0).mpr fun z => hfM z.1.1 z.2
  obtain ⟨h, hh_norm, hh_eq⟩ := exists_norm_eq_domRestrict_eq hs_closed ℂ f₀
  classical
  let g_fun : α → ℂ := fun x => if hx : x ∈ V then φ x * h ⟨x, subset_closure hx⟩ else 0
  have hg_cont : Continuous g_fun := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx_supp : x ∈ tsupport φ
    · have hxV : x ∈ V := hφ_supp hx_supp
      have he : Continuous (fun z : V => (⟨z.1, subset_closure z.2⟩ : Y)) :=
        Continuous.subtype_mk continuous_subtype_val (fun z => subset_closure z.2)
      have hk : Continuous (fun z : V => g_fun z.1) := by
        have hcongr : (fun z : V => g_fun z.1) =
            (fun z : V => φ z.1 * h ⟨z.1, subset_closure z.2⟩) := by
          ext z
          simp [g_fun, z.2]
        rw [hcongr]
        exact (φ.continuous.comp continuous_subtype_val).mul (h.continuous.comp he)
      exact (continuousOn_iff_continuous_domRestrict.mpr hk).continuousAt (hV_open.mem_nhds hxV)
    · have hzero : g_fun =ᶠ[𝓝 x] 0 := by
        filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx_supp] with y hy
        have hφy : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp [g_fun, hφy]
      exact continuousAt_const.congr hzero.symm
  have hg_supp : HasCompactSupport g_fun :=
    φ.hasCompactSupport.mono fun x hx => fun hφx => hx (by simp [g_fun, hφx])
  refine ⟨⟨⟨g_fun, hg_cont⟩, hg_supp⟩, ?_, ?_, ?_⟩
  · intro x
    dsimp [g_fun]
    split_ifs with hxV
    · calc
        ‖φ x * h ⟨x, subset_closure hxV⟩‖
            = ‖φ x‖ * ‖h ⟨x, subset_closure hxV⟩‖ := norm_mul _ _
        _ ≤ 1 * M := mul_le_mul (hφ_norm x)
              ((h.norm_coe_le_norm _).trans (hh_norm.le.trans hf₀_norm))
              (norm_nonneg _) zero_le_one
        _ = M := one_mul M
    · simpa using hM0
  · intro x hxK
    have hxV : x ∈ V := hKV hxK
    have hhx : h ⟨x, subset_closure hxV⟩ = f x := by
      have h1 := DFunLike.congr_fun hh_eq ⟨⟨x, subset_closure hxV⟩, hxK⟩
      simpa [f₀] using h1
    simp [g_fun, hxV, hφ_one hxK, hhx]
  · intro x hxV
    simp [g_fun, hxV]

/-- `RCA 2.24` (Lusin's Theorem, pp. 55–56): let `X` be a locally compact Hausdorff space and `μ` a
measure on `X` satisfying the regularity clauses of `2.14` (`Book214RegularityHypotheses μ`, with no
`σ`-finiteness, metrizability, or Borel-only restriction). Suppose `f : X → ℂ` is measurable,
`μ(A) < ∞`, `f(x) = 0` for `x ∉ A`, and `ε > 0`. Then there exists `g ∈ C_c(X)` such that
`μ({x : f(x) ≠ g(x)}) < ε` and `sup_{x ∈ X} |g(x)| ≤ sup_{x ∈ X} |f(x)|` (expressed simultaneously
in extended-real supremum `⨆ x, ‖·‖ₑ`, `ENNReal.ofReal` supremum, universal upper-bound transfer,
and real `sSup` whenever `f` is bounded). -/
theorem theorem_2_24 {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
    [MeasurableSpace α] {μ : Measure α} (hreg : Book214RegularityHypotheses μ)
    {f : α → ℂ} (hf : Measurable f) {A : Set α} (hA : μ A < ∞) (hfA : ∀ x ∉ A, f x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C_c(α, ℂ),
      μ {x : α | f x ≠ g x} < ENNReal.ofReal ε ∧
      (⨆ x : α, ‖g x‖ₑ) ≤ (⨆ x : α, ‖f x‖ₑ) ∧
      (⨆ x : α, ENNReal.ofReal ‖g x‖) ≤ (⨆ x : α, ENNReal.ofReal ‖f x‖) ∧
      (∀ R : ℝ, (∀ x : α, ‖f x‖ ≤ R) → ∀ x : α, ‖g x‖ ≤ R) ∧
      (BddAbove (range fun x : α => ‖f x‖) →
        sSup (range fun x : α => ‖g x‖) ≤ sSup (range fun x : α => ‖f x‖)) := by
  let S : Set α := {x : α | f x ≠ 0}
  have hS_eq : S = f ⁻¹' ({(0 : ℂ)}ᶜ) := by
    ext x
    simp [S]
  have hS_meas : MeasurableSet S := hS_eq ▸ hf (measurableSet_singleton (0 : ℂ)).compl
  have hSA : S ⊆ A := by
    intro x hx
    by_contra hxA
    exact hx (hfA x hxA)
  have hS_fin : μ S < ∞ := (measure_mono hSA).trans_lt hA
  have hb_ne : (TopologicalSpace.countableBasis ℂ).Nonempty := by
    obtain ⟨b, hb, _, _⟩ :=
      (TopologicalSpace.isBasis_countableBasis ℂ).exists_subset_of_mem_open
        (mem_univ (0 : ℂ)) isOpen_univ
    exact ⟨b, hb⟩
  obtain ⟨B, hB_eq⟩ := (TopologicalSpace.countable_countableBasis ℂ).exists_eq_range hb_ne
  have hB_open : ∀ n : ℕ, IsOpen (B n) := fun n =>
    TopologicalSpace.isOpen_of_mem_countableBasis (hB_eq ▸ mem_range_self n)
  have hδ_ne : ENNReal.ofReal (ε / 4) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  rcases ENNReal.exists_pos_sum_of_countable' hδ_ne ℕ with ⟨η, hη_pos, hη_sum⟩
  let E : ℕ → Set α := fun n => S ∩ f ⁻¹' (B n)
  let F : ℕ → Set α := fun n => S \ E n
  have hE_meas : ∀ n : ℕ, MeasurableSet (E n) := fun n =>
    hS_meas.inter (hf (hB_open n).measurableSet)
  have hE_fin : ∀ n : ℕ, μ (E n) < ∞ := fun n =>
    (measure_mono inter_subset_left).trans_lt hS_fin
  have hF_meas : ∀ n : ℕ, MeasurableSet (F n) := fun n => hS_meas.diff (hE_meas n)
  have hF_fin : ∀ n : ℕ, μ (F n) < ∞ := fun n => (measure_mono sdiff_subset).trans_lt hS_fin
  choose C hCE hC_comp hEC_lt using fun n =>
    hreg.exists_isCompact_diff_lt (hE_meas n) (hE_fin n) (hη_pos n).ne'
  choose D hDF hD_comp hFD_lt using fun n =>
    hreg.exists_isCompact_diff_lt (hF_meas n) (hF_fin n) (hη_pos n).ne'
  let K : Set α := ⋂ n : ℕ, (C n ∪ D n)
  have hK_closed : IsClosed K :=
    isClosed_iInter fun n => (hC_comp n).isClosed.union (hD_comp n).isClosed
  have hK_comp : IsCompact K :=
    ((hC_comp 0).union (hD_comp 0)).of_isClosed_subset hK_closed (iInter_subset _ 0)
  have hKS : K ⊆ S :=
    (iInter_subset (fun n => C n ∪ D n) 0).trans
      (union_subset ((hCE 0).trans inter_subset_left) ((hDF 0).trans sdiff_subset))
  have hSK : μ (S \ K) < ENNReal.ofReal (ε / 2) := by
    have hstep : ∀ n : ℕ, μ (S \ (C n ∪ D n)) ≤ η n + η n := by
      intro n
      have hsub : S \ (C n ∪ D n) ⊆ (E n \ C n) ∪ (F n \ D n) := by
        rintro x ⟨hxS, hxCD⟩
        by_cases hxE : x ∈ E n
        · exact Or.inl ⟨hxE, fun hxC => hxCD (Or.inl hxC)⟩
        · exact Or.inr ⟨⟨hxS, hxE⟩, fun hxD => hxCD (Or.inr hxD)⟩
      exact (measure_mono hsub).trans
        ((measure_union_le _ _).trans (add_le_add (hEC_lt n).le (hFD_lt n).le))
    have h1 : μ (S \ K) ≤ ∑' n : ℕ, (η n + η n) := by
      rw [show S \ K = ⋃ n : ℕ, (S \ (C n ∪ D n)) by simp only [K, sdiff_iInter]]
      exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hstep)
    rw [ENNReal.tsum_add] at h1
    have h2 : (∑' n : ℕ, η n) + (∑' n : ℕ, η n) <
        ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
      ENNReal.add_lt_add hη_sum hη_sum
    have h4 : ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) = ENNReal.ofReal (ε / 2) := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      ring_nf
    exact h1.trans_lt (h2.trans_eq h4)
  have hfK : ContinuousOn f K := by
    rw [(TopologicalSpace.isBasis_countableBasis ℂ).continuousOn_iff]
    intro t ht
    rw [hB_eq] at ht
    rcases ht with ⟨n, rfl⟩
    refine ⟨(D n)ᶜ, (hD_comp n).isClosed.isOpen_compl, ?_⟩
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff]
    constructor
    · rintro ⟨hfx, hxK⟩
      refine ⟨fun hxD => ?_, hxK⟩
      exact (hDF n hxD).2 ⟨hKS hxK, hfx⟩
    · rintro ⟨hxD, hxK⟩
      rcases mem_iInter.mp hxK n with hxC | hxD'
      · exact ⟨(hCE n hxC).2, hxK⟩
      · exact False.elim (hxD hxD')
  by_cases hK_ne : K.Nonempty
  · obtain ⟨x_max, hx_max, hmax⟩ :=
      hK_comp.exists_isMaxOn hK_ne (continuous_norm.comp_continuousOn hfK)
    have hfM : ∀ x ∈ K, ‖f x‖ ≤ ‖f x_max‖ := fun x hx => isMaxOn_iff.mp hmax x hx
    have hK_meas : MeasurableSet K := hreg.measurableSet_of_isClosed hK_closed
    have hK_fin : μ K < ∞ := hreg.2.1 K hK_comp
    obtain ⟨U, hKU, hU_open, hUK⟩ :=
      hreg.exists_isOpen_diff_lt hK_meas hK_fin (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
    obtain ⟨V, hV_open, hV_comp, hKV, hV_sub_cl, hcl_sub_U⟩ := theorem_2_7 hU_open hKU hK_comp
    obtain ⟨φ, hφ_comp, hφ_open⟩ := lemma_2_12 hK_comp hV_open hKV
    have hφ_norm : ∀ x : α, ‖φ x‖ ≤ 1 := by
      intro x
      obtain ⟨r, ⟨hr0, hr1⟩, hφx⟩ := hφ_comp.2.1 x
      rw [hφx, Complex.norm_real, Real.norm_of_nonneg hr0]
      exact hr1
    obtain ⟨g, hg_norm, hg_eqK, hg_zeroV⟩ :=
      tietze_cutoff_extension hK_comp hV_open hV_comp hKV φ hφ_norm hφ_comp.2.2 hφ_open.2.2
        f hfK (norm_nonneg (f x_max)) hfM
    have hVU : V ⊆ U := hV_sub_cl.trans hcl_sub_U
    refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
    · have hdis : {x : α | f x ≠ g x} ⊆ (S \ K) ∪ (U \ K) := by
        intro x hx
        have hx_notK : x ∉ K := fun hxK => hx (hg_eqK x hxK).symm
        by_cases hxS : x ∈ S
        · exact Or.inl ⟨hxS, hx_notK⟩
        · have hfx0 : f x = 0 := not_not.mp hxS
          have hgx_ne : g x ≠ 0 := fun hgx0 => hx (hfx0.trans hgx0.symm)
          have hxV : x ∈ V := by
            by_contra hxV
            exact hgx_ne (hg_zeroV x hxV)
          exact Or.inr ⟨hVU hxV, hx_notK⟩
      have hadd_lt : μ (S \ K) + μ (U \ K) < ENNReal.ofReal ε := by
        have hlt := ENNReal.add_lt_add hSK hUK
        have heq : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
        exact hlt.trans_eq heq
      exact (measure_mono hdis).trans_lt ((measure_union_le _ _).trans_lt hadd_lt)
    · refine iSup_le fun x => ?_
      exact (enorm_le_iff_norm_le.mpr (hg_norm x)).trans
        (le_iSup (fun y : α => ‖f y‖ₑ) x_max)
    · refine iSup_le fun x => ?_
      exact (ENNReal.ofReal_le_ofReal (hg_norm x)).trans
        (le_iSup (fun y : α => ENNReal.ofReal ‖f y‖) x_max)
    · intro R hR x
      exact (hg_norm x).trans (hR x_max)
    · intro hbdd
      exact csSup_le ⟨‖g x_max‖, x_max, rfl⟩ (by
        rintro _ ⟨x, rfl⟩
        exact (hg_norm x).trans (le_csSup hbdd ⟨x_max, rfl⟩))
  · have hK_empty : K = ∅ := not_nonempty_iff_eq_empty.mp hK_ne
    refine ⟨0, ?_, ?_, ?_, ?_, ?_⟩
    · have hdis : {x : α | f x ≠ (0 : C_c(α, ℂ)) x} = S \ K := by
        ext x
        simp [S, hK_empty]
      rw [hdis]
      exact hSK.trans (ENNReal.ofReal_lt_ofReal_iff hε |>.mpr (by linarith))
    · refine iSup_le fun x => ?_
      simp
    · refine iSup_le fun x => ?_
      simp
    · intro R hR x
      simpa using (norm_nonneg (f x)).trans (hR x)
    · intro hbdd
      by_cases hα : Nonempty α
      · rcases hα with ⟨x₀⟩
        exact csSup_le ⟨‖(0 : C_c(α, ℂ)) x₀‖, x₀, rfl⟩ (by
          rintro _ ⟨x, rfl⟩
          simpa using (norm_nonneg (f x₀)).trans (le_csSup hbdd ⟨x₀, rfl⟩))
      · have : IsEmpty α := not_nonempty_iff.mp hα
        simp [range_eq_empty]

/-- `RCA 2.24` (Corollary, p. 56): under the hypotheses of Lusin's theorem together with
`|f(x)| ≤ 1`, there is a sequence `g_n ∈ C_c(X)` with `|g_n(x)| ≤ 1` for all `n, x` and
`f(x) = lim_{n → ∞} g_n(x)` `μ`-almost everywhere. -/
theorem theorem_2_24_corollary {α : Type*} [TopologicalSpace α] [T2Space α]
    [LocallyCompactSpace α] [MeasurableSpace α] {μ : Measure α}
    (hreg : Book214RegularityHypotheses μ) {f : α → ℂ} (hf : Measurable f)
    {A : Set α} (hA : μ A < ∞) (hfA : ∀ x ∉ A, f x = 0)
    (hbound : ∀ x : α, ‖f x‖ ≤ 1) :
    ∃ g : ℕ → C_c(α, ℂ),
      (∀ n : ℕ, ∀ x : α, ‖g n x‖ ≤ 1) ∧
      (∀ᵐ x ∂μ, Filter.Tendsto (fun n => g n x) Filter.atTop (𝓝 (f x))) := by
  have : OpensMeasurableSpace α := hreg.opensMeasurableSpace
  have hstep : ∀ n : ℕ, ∃ g : C_c(α, ℂ),
      μ {x : α | f x ≠ g x} < ((2 : ℝ≥0∞)⁻¹) ^ n ∧ ∀ x : α, ‖g x‖ ≤ 1 := by
    intro n
    have hε_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
    obtain ⟨g, hg_meas, _, _, hg_ub, _⟩ := theorem_2_24 hreg hf hA hfA hε_pos
    have hpow : ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = ((2 : ℝ≥0∞)⁻¹) ^ n := by
      rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2) n, one_div,
        ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat]
    exact ⟨g, hpow ▸ hg_meas, hg_ub 1 hbound⟩
  choose g hg_lt hg_le using hstep
  let D : ℕ → Set α := fun n => {x : α | f x ≠ g n x}
  have hD_meas : ∀ n : ℕ, MeasurableSet (D n) := by
    intro n
    have heq : D n = (fun x => f x - g n x) ⁻¹' ({(0 : ℂ)}ᶜ) := by
      ext x
      simp [D, sub_eq_zero]
    rw [heq]
    exact (hf.sub (g n).continuous.measurable) (measurableSet_singleton (0 : ℂ)).compl
  have hsum : (∑' n : ℕ, μ (D n)) < ∞ := by
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun n => (hg_lt n).le) ?_
    simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using
      (ENNReal.ofNat_lt_top : (2 : ℝ≥0∞) < ∞)
  have hae : ∀ᵐ x ∂μ, {n : ℕ | x ∈ D n}.Finite :=
    Chapter01.theorem_1_41 μ D hD_meas hsum
  refine ⟨g, hg_le, ?_⟩
  filter_upwards [hae] with x hx_fin
  have hev : (fun n : ℕ => g n x) =ᶠ[Filter.atTop] (fun _ : ℕ => f x) := by
    rw [Filter.EventuallyEq, ← Nat.cofinite_eq_atTop, Filter.Eventually, Filter.mem_cofinite]
    have hcompl : {n : ℕ | g n x = f x}ᶜ = {n : ℕ | x ∈ D n} := by
      ext n
      simp [D, eq_comm]
    rwa [hcompl]
  exact tendsto_const_nhds.congr' hev.symm

/-- Finite-support convenience specialization of `theorem_2_24` (`A = {x | f x ≠ 0}`). -/
theorem theorem_2_24_support_finite {α : Type*} [TopologicalSpace α] [T2Space α]
    [LocallyCompactSpace α] [MeasurableSpace α] {μ : Measure α}
    (hreg : Book214RegularityHypotheses μ) {f : α → ℂ} (hf : Measurable f)
    (hfin : μ {x : α | f x ≠ 0} < ∞) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C_c(α, ℂ),
      μ {x : α | f x ≠ g x} < ENNReal.ofReal ε ∧
      (⨆ x : α, ‖g x‖ₑ) ≤ (⨆ x : α, ‖f x‖ₑ) ∧
      (⨆ x : α, ENNReal.ofReal ‖g x‖) ≤ (⨆ x : α, ENNReal.ofReal ‖f x‖) ∧
      (∀ R : ℝ, (∀ x : α, ‖f x‖ ≤ R) → ∀ x : α, ‖g x‖ ≤ R) ∧
      (BddAbove (range fun x : α => ‖f x‖) →
        sSup (range fun x : α => ‖g x‖) ≤ sSup (range fun x : α => ‖f x‖)) :=
  theorem_2_24 hreg hf hfin (fun _ hx => not_not.mp hx) hε

/-- Finite-support convenience specialization of `theorem_2_24_corollary` (`A = {x | f x ≠ 0}`). -/
theorem theorem_2_24_corollary_support_finite {α : Type*} [TopologicalSpace α] [T2Space α]
    [LocallyCompactSpace α] [MeasurableSpace α] {μ : Measure α}
    (hreg : Book214RegularityHypotheses μ) {f : α → ℂ} (hf : Measurable f)
    (hfin : μ {x : α | f x ≠ 0} < ∞) (hbound : ∀ x : α, ‖f x‖ ≤ 1) :
    ∃ g : ℕ → C_c(α, ℂ),
      (∀ n : ℕ, ∀ x : α, ‖g n x‖ ≤ 1) ∧
      (∀ᵐ x ∂μ, Filter.Tendsto (fun n => g n x) Filter.atTop (𝓝 (f x))) :=
  theorem_2_24_corollary hreg hf hfin (fun _ hx => not_not.mp hx) hbound

end LusinApproximation2_24

end RudinRCA.Chapter02
