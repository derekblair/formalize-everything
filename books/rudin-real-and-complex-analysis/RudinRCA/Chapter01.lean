import Mathlib

/-!
# Chapter 1: Abstract integration

Numbering follows the 1987 third edition. `ℝ≥0∞` represents `[0,∞]`,
`EReal` represents `[-∞,∞]`, and `Measurable` into a topological space always
uses its Borel sigma algebra. Sequences start at zero (a reindexing of the
book's positive integers). See `INVENTORY-CH01.md` for coverage and sources.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace RudinRCA.Chapter01

/-! §§1.1–1.4 introduce sets, topology and measurability. These are represented
by Lean's `Set`, `TopologicalSpace`, `MeasurableSpace`, `Continuous` and
`Measurable`; the codomain measurable structure in §1.3(c) is `borel`. -/

/-- 1.5: global continuity is continuity at every point. -/
theorem theorem_1_5 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Continuous f ↔ ∀ x, ContinuousAt f x :=
  continuous_iff_continuousAt

/-- 1.6: empty sets, finite unions, countable intersections and differences. -/
theorem proposition_1_6 {X : Type*} [MeasurableSpace X] :
    MeasurableSet (∅ : Set X) ∧
    (∀ (n : ℕ) (A : Fin n → Set X), (∀ i, MeasurableSet (A i)) →
      MeasurableSet (⋃ i, A i)) ∧
    (∀ A : ℕ → Set X, (∀ n, MeasurableSet (A n)) → MeasurableSet (⋂ n, A n)) ∧
    (∀ A B : Set X, MeasurableSet A → MeasurableSet B → MeasurableSet (A \ B)) := by
  exact ⟨MeasurableSet.empty, fun _ _ h => MeasurableSet.iUnion h,
    fun _ h => MeasurableSet.iInter h, fun _ _ hA hB => hA.diff hB⟩

/-- 1.7(a). -/
theorem theorem_1_7a {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X → Y} {g : Y → Z}
    (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := hg.comp hf

/-- 1.7(b), with precisely the Borel interpretation of §1.3(c). -/
theorem theorem_1_7b {X Y Z : Type*} [MeasurableSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y} {g : Y → Z}
    (hf : @Measurable X Y _ (borel Y) f) (hg : Continuous g) :
    @Measurable X Z _ (borel Z) (g ∘ f) := by
  exact hg.borel_measurable.comp hf

/-- 1.8: a continuous function of two real measurable functions. -/
theorem theorem_1_8 {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y]
    {u v : X → ℝ} {Φ : ℝ × ℝ → Y}
    (hu : Measurable u) (hv : Measurable v) (hΦ : Continuous Φ) :
    @Measurable X Y _ (borel Y) (fun x => Φ (u x, v x)) := by
  borelize Y
  exact hΦ.measurable.comp (hu.prodMk hv)

/-- 1.9(a–d): measurable complex functions and indicators. -/
theorem proposition_1_9a {X : Type*} [MeasurableSpace X] {u v : X → ℝ}
    (hu : Measurable u) (hv : Measurable v) :
    Measurable (fun x => (u x : ℂ) + (v x : ℂ) * Complex.I) := by fun_prop

theorem proposition_1_9b {X : Type*} [MeasurableSpace X] {f : X → ℂ}
    (hf : Measurable f) :
    Measurable (fun x => (f x).re) ∧ Measurable (fun x => (f x).im) ∧
      Measurable (fun x => ‖f x‖) := by
  exact ⟨hf.re, hf.im, hf.norm⟩

theorem proposition_1_9c {X : Type*} [MeasurableSpace X] {f g : X → ℂ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (f + g) ∧ Measurable (f * g) := ⟨hf.add hg, hf.mul hg⟩

theorem proposition_1_9d {X : Type*} [MeasurableSpace X] {E : Set X}
    (hE : MeasurableSet E) : Measurable (E.indicator (fun _ => (1 : ℂ))) :=
  measurable_const.indicator hE

/-- 1.9(e): the phase is chosen to be one at zeros. -/
theorem proposition_1_9e {X : Type*} [MeasurableSpace X] {f : X → ℂ}
    (hf : Measurable f) :
    ∃ a : X → ℂ, Measurable a ∧ (∀ x, ‖a x‖ = 1) ∧
      ∀ x, f x = a x * (‖f x‖ : ℂ) := by
  let a : X → ℂ := fun x => if f x = 0 then 1 else f x / (‖f x‖ : ℂ)
  refine ⟨a, ?_, ?_, ?_⟩
  · exact measurable_const.ite (hf (measurableSet_singleton 0)) (hf.div hf.norm.complex_ofReal)
  · intro x
    dsimp [a]
    split_ifs with hx
    · simp
    · simp [norm_ne_zero_iff.mpr hx]
  · intro x
    dsimp [a]
    split_ifs with hx
    · simp [hx]
    · exact (div_mul_cancel₀ (f x) (by exact_mod_cast norm_ne_zero_iff.mpr hx)).symm

/-- 1.10: existence and minimality of the generated sigma algebra. -/
theorem theorem_1_10 {X : Type*} (F : Set (Set X)) :
    ∃ m : MeasurableSpace X, (∀ s ∈ F, @MeasurableSet X m s) ∧
      ∀ m' : MeasurableSpace X, (∀ s ∈ F, @MeasurableSet X m' s) → m ≤ m' := by
  exact ⟨MeasurableSpace.generateFrom F,
    fun _ hs => MeasurableSpace.measurableSet_generateFrom hs,
    fun _ h => MeasurableSpace.generateFrom_le h⟩

/-- 1.11: continuous maps are Borel measurable. -/
theorem proposition_1_11 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) : @Measurable X Y (borel X) (borel Y) f := by
  exact hf.borel_measurable

/-- 1.12(a): the sets with measurable inverse image form a sigma algebra. -/
abbrev pullbackSigma {X Y : Type*} [m : MeasurableSpace X] (f : X → Y) :
    MeasurableSpace Y := MeasurableSpace.map f m

theorem theorem_1_12a {X Y : Type*} [MeasurableSpace X] (f : X → Y) (E : Set Y) :
    @MeasurableSet Y (pullbackSigma f) E ↔ MeasurableSet (f ⁻¹' E) := Iff.rfl

/-- 1.12(b): inverse images of Borel sets. -/
theorem theorem_1_12b {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : @Measurable X Y _ (borel Y) f)
    {E : Set Y} (hE : @MeasurableSet Y (borel Y) E) :
    MeasurableSet (f ⁻¹' E) := hf hE

/-- 1.12(d): composition with a Borel map. -/
theorem theorem_1_12d {X Y Z : Type*} [MeasurableSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y} {g : Y → Z}
    (hf : @Measurable X Y _ (borel Y) f)
    (hg : @Measurable Y Z (borel Y) (borel Z) g) :
    @Measurable X Z _ (borel Z) (g ∘ f) := hg.comp hf

/-- 1.14: measurable suprema and upper limits, including infinite values. -/
theorem theorem_1_14 {X : Type*} [MeasurableSpace X] {f : ℕ → X → EReal}
    (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x => ⨆ n, f n x) ∧
      Measurable (fun x => limsup (fun n => f n x) atTop) := by
  constructor
  · exact Measurable.iSup hf
  · simp only [limsup_eq_iInf_iSup_of_nat]
    exact Measurable.iInf fun n => Measurable.iSup fun i => Measurable.iSup fun _ => hf i

/-- Corollary 1.14(a). -/
theorem corollary_1_14a {X : Type*} [MeasurableSpace X] {f : ℕ → X → ℂ}
    {g : X → ℂ} (hf : ∀ n, Measurable (f n))
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Measurable g :=
  measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.mpr hlim)

/-- Corollary 1.14(b), including positive and negative parts. -/
theorem corollary_1_14b {X : Type*} [MeasurableSpace X] {f g : X → EReal}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => max (f x) (g x)) ∧
    Measurable (fun x => min (f x) (g x)) ∧
    Measurable (fun x => max (f x) 0) ∧
    Measurable (fun x => -min (f x) 0) := by
  exact ⟨hf.max hg, hf.min hg, hf.max measurable_const, (hf.min measurable_const).neg⟩

/-- 1.17: monotone, finite-valued measurable simple approximants. -/
theorem theorem_1_17 {X : Type*} [MeasurableSpace X] {f : X → ℝ≥0∞}
    (hf : Measurable f) : ∃ s : ℕ → SimpleFunc X ℝ≥0∞,
    (∀ n x, s n x < ∞) ∧ Monotone (fun n x => s n x) ∧
    (∀ n x, s n x ≤ f x) ∧
    ∀ x, Tendsto (fun n => s n x) atTop (𝓝 (f x)) := by
  refine ⟨SimpleFunc.eapprox f, SimpleFunc.eapprox_lt_top f,
    SimpleFunc.monotone_eapprox f, ?_, SimpleFunc.tendsto_eapprox hf⟩
  intro n x
  rw [← SimpleFunc.iSup_eapprox_apply hf x]
  exact le_iSup (fun n => SimpleFunc.eapprox f n x) n

/-- 1.19(a). -/
theorem theorem_1_19a {X : Type*} [MeasurableSpace X] (μ : Measure X) :
    μ ∅ = 0 := measure_empty

/-- 1.19(b). -/
theorem theorem_1_19b {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (n : ℕ) (A : Fin n → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) : μ (⋃ i, A i) = ∑ i, μ (A i) := by
  rw [measure_iUnion hd hA, tsum_fintype]

/-- 1.19(c). -/
theorem theorem_1_19c {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {A B : Set X} (h : A ⊆ B) : μ A ≤ μ B := measure_mono h

/-- 1.19(d). -/
theorem theorem_1_19d {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {A : ℕ → Set X} (hA : Monotone A) :
    Tendsto (fun n => μ (A n)) atTop (𝓝 (μ (⋃ n, A n))) :=
  tendsto_measure_iUnion_atTop hA

/-- 1.19(e), retaining the finite first-set assumption. -/
theorem theorem_1_19e {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {A : ℕ → Set X} (hm : ∀ n, MeasurableSet (A n))
    (hA : Antitone A) (hfin : μ (A 0) ≠ ∞) :
    Tendsto (fun n => μ (A n)) atTop (𝓝 (μ (⋂ n, A n))) :=
  tendsto_measure_iInter_atTop (fun n => (hm n).nullMeasurableSet) hA ⟨0, hfin⟩

/-- 1.24(a–f): elementary properties of the nonnegative integral. -/
theorem proposition_1_24a {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (E : Set X) {f g : X → ℝ≥0∞} (h : f ≤ g) :
    ∫⁻ x in E, f x ∂μ ≤ ∫⁻ x in E, g x ∂μ := lintegral_mono h

theorem proposition_1_24b {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {A B : Set X} (h : A ⊆ B) (f : X → ℝ≥0∞) :
    ∫⁻ x in A, f x ∂μ ≤ ∫⁻ x in B, f x ∂μ := lintegral_mono_set h

theorem proposition_1_24c {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (E : Set X) {f : X → ℝ≥0∞} (hf : Measurable f) (c : ℝ≥0) :
    ∫⁻ x in E, (c : ℝ≥0∞) * f x ∂μ = c * ∫⁻ x in E, f x ∂μ :=
  lintegral_const_mul _ hf

theorem proposition_1_24d {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {E : Set X} (hE : MeasurableSet E) {f : X → ℝ≥0∞} (h : ∀ x ∈ E, f x = 0) :
    ∫⁻ x in E, f x ∂μ = 0 := setLIntegral_eq_zero hE h

theorem proposition_1_24e {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {E : Set X} (h : μ E = 0) (f : X → ℝ≥0∞) : ∫⁻ x in E, f x ∂μ = 0 := by
  simp [Measure.restrict_eq_zero.mpr h]

theorem proposition_1_24f {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {E : Set X} (hE : MeasurableSet E) (f : X → ℝ≥0∞) :
    ∫⁻ x in E, f x ∂μ = ∫⁻ x, E.indicator f x ∂μ := (lintegral_indicator hE f).symm


section Integration
variable {X : Type*} [MeasurableSpace X]

/-- RCA 1.25. A nonnegative, finite-valued measurable simple function defines
    a measure by integration; the simple integral is additive. -/
theorem proposition_1_25 (μ : Measure X) (s t : SimpleFunc X ℝ≥0) :
    (∃ φ : Measure X, ∀ E : Set X, MeasurableSet E →
      φ E = ∫⁻ x in E, (s x : ℝ≥0∞) ∂μ) ∧
    (∫⁻ x, ((s x : ℝ≥0∞) + (t x : ℝ≥0∞)) ∂μ) =
      (∫⁻ x, (s x : ℝ≥0∞) ∂μ) + ∫⁻ x, (t x : ℝ≥0∞) ∂μ := by
  constructor
  · exact ⟨μ.withDensity (fun x => (s x : ℝ≥0∞)),
      fun E hE => withDensity_apply _ hE⟩
  · exact lintegral_add_left s.measurable.coe_nnreal_ennreal _

/-- RCA 1.26, including measurability of the pointwise limit. -/
theorem theorem_1_26 (μ : Measure X) (f : ℕ → X → ℝ≥0∞) (F : X → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n))
    (hmono : ∀ x, Monotone (fun n => f n x))
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x))) :
    Measurable F ∧
      Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, F x ∂μ)) := by
  exact ⟨ENNReal.measurable_of_tendsto hf (tendsto_pi_nhds.mpr hlim),
    lintegral_tendsto_of_tendsto_of_monotone (fun n => (hf n).aemeasurable)
      (Filter.Eventually.of_forall hmono) (Filter.Eventually.of_forall hlim)⟩

/-- RCA 1.27: nonnegative series can be integrated term by term. -/
theorem theorem_1_27 (μ : Measure X) (f : ℕ → X → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) :
    (∫⁻ x, ∑' n, f n x ∂μ) = ∑' n, ∫⁻ x, f n x ∂μ := by
  exact lintegral_tsum (fun n => (hf n).aemeasurable)

/-- The unnumbered corollary attached to RCA 1.27. -/
theorem corollary_1_27 (a : ℕ → ℕ → ℝ≥0∞) :
    (∑' i, ∑' j, a i j) = ∑' j, ∑' i, a i j := by
  exact ENNReal.tsum_comm

/-- RCA 1.28 (Fatou's lemma). -/
theorem theorem_1_28 (μ : Measure X) (f : ℕ → X → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) :
    (∫⁻ x, Filter.liminf (fun n => f n x) atTop ∂μ) ≤
      Filter.liminf (fun n => ∫⁻ x, f n x ∂μ) atTop := by
  exact lintegral_liminf_le hf

/-- RCA 1.29: the measure defined by a density and its change-of-measure
    identity. No finiteness or sigma-finiteness assumption is added. -/
theorem theorem_1_29 (μ : Measure X) (f : X → ℝ≥0∞) (hf : Measurable f) :
    ∃ φ : Measure X,
      (∀ E : Set X, MeasurableSet E → φ E = ∫⁻ x in E, f x ∂μ) ∧
      (∀ g : X → ℝ≥0∞, Measurable g →
        (∫⁻ x, g x ∂φ) = ∫⁻ x, g x * f x ∂μ) := by
  refine ⟨μ.withDensity f, (fun E hE => withDensity_apply _ hE), ?_⟩
  intro g hg
  simpa only [Pi.mul_apply, mul_comm] using
    lintegral_withDensity_eq_lintegral_mul μ hf hg

end Integration

end RudinRCA.Chapter01
