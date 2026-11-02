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

end RudinRCA.Chapter02
