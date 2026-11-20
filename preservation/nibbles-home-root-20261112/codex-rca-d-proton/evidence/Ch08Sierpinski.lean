module
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

public section

open Set MeasureTheory
open scoped ENNReal

namespace RudinRCA.Chapter08

variable {X W : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
  [LinearOrder W] (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- The set in 8.9(c), using the well-order supplied in Rudin's conditional construction. -/
def sierpinskiSet (j : X ≃ W) : Set (X × X) := {p | j p.1 < j p.2}

/-- 8.9(c), conditional form with precisely the countable-predecessor well-order that
Rudin takes from CH. No continuum-hypothesis axiom is introduced. Instantiating `X`
with the unit interval and its Lebesgue probability measure gives the printed example.
The additional CH-to-existence implication is not asserted by this theorem. -/
theorem sierpinski_counterexample (j : X ≃ W)
    (_hw : WellFounded ((· < ·) : W → W → Prop))
    (hcount : ∀ w : W, (Set.Iio w).Countable) :
    (∀ x : X, MeasurableSet {y | (x, y) ∈ sierpinskiSet j} ∧
      μ {y | (x, y) ∈ sierpinskiSet j} = 1) ∧
    (∀ y : X, MeasurableSet {x | (x, y) ∈ sierpinskiSet j} ∧
      μ {x | (x, y) ∈ sierpinskiSet j} = 0) ∧
    (∫⁻ x, μ {y | (x, y) ∈ sierpinskiSet j} ∂μ) = 1 ∧
    (∫⁻ y, μ {x | (x, y) ∈ sierpinskiSet j} ∂μ) = 0 ∧
    ¬ MeasurableSet (sierpinskiSet j) := by
  classical
  have hpred (y : X) : {x : X | j x < j y}.Countable :=
    (hcount (j y)).preimage j.injective
  have hsucc (x : X) : ({y : X | j x < j y}ᶜ).Countable := by
    have heq : {y : X | j x < j y}ᶜ = {y : X | j y < j x} ∪ {x} := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union,
        Set.mem_singleton_iff, not_lt, le_iff_lt_or_eq, j.injective.eq_iff]
    rw [heq]
    exact (hpred x).union (Set.countable_singleton x)
  have hx (x : X) : MeasurableSet {y | (x, y) ∈ sierpinskiSet j} ∧
      μ {y | (x, y) ∈ sierpinskiSet j} = 1 := by
    constructor
    · simpa only [compl_compl, sierpinskiSet, Set.mem_ofPred_eq] using (hsucc x).measurableSet.compl
    · have h := measure_compl (hsucc x).measurableSet
        (measure_ne_top μ ({y : X | j x < j y}ᶜ))
      simpa only [compl_compl, (hsucc x).measure_zero μ, measure_univ, tsub_zero, sierpinskiSet, Set.mem_ofPred_eq] using h
  have hy (y : X) : MeasurableSet {x | (x, y) ∈ sierpinskiSet j} ∧
      μ {x | (x, y) ∈ sierpinskiSet j} = 0 :=
    ⟨(hpred y).measurableSet, (hpred y).measure_zero μ⟩
  have hxint : (∫⁻ x, μ {y | (x, y) ∈ sierpinskiSet j} ∂μ) = 1 := by
    calc
      _ = ∫⁻ _ : X, (1 : ℝ≥0∞) ∂μ := lintegral_congr (fun x => (hx x).2)
      _ = 1 := by simp
  have hyint : (∫⁻ y, μ {x | (x, y) ∈ sierpinskiSet j} ∂μ) = 0 := by
    calc
      _ = ∫⁻ _ : X, (0 : ℝ≥0∞) ∂μ := lintegral_congr (fun y => (hy y).2)
      _ = 0 := by simp
  refine ⟨hx, hy, hxint, hyint, ?_⟩
  intro hQ
  have h := (Measure.prod_apply (μ := μ) (ν := μ) hQ).symm.trans
    (Measure.prod_apply_symm (μ := μ) (ν := μ) hQ)
  change (∫⁻ x, μ {y | (x, y) ∈ sierpinskiSet j} ∂μ) =
    (∫⁻ y, μ {x | (x, y) ∈ sierpinskiSet j} ∂μ) at h
  rw [hxint, hyint] at h
  exact one_ne_zero h


/-- A concrete well-order of first uncountable cardinality. -/
abbrev SierpinskiOrder := (Cardinal.aleph 1 : Cardinal.{0}).ord.ToType

/-- The set-theoretic step used in 8.9(c), explicitly conditional on CH.
The hypothesis is a proposition, never an added axiom. -/
theorem ch_unitInterval_wellOrder
    (hCH : Cardinal.continuum = (Cardinal.aleph 1 : Cardinal.{0})) :
    Nonempty ((Set.Icc (0 : ℝ) 1) ≃ SierpinskiOrder) ∧
    WellFounded ((· < ·) : SierpinskiOrder → SierpinskiOrder → Prop) ∧
    (∀ w : SierpinskiOrder, (Set.Iio w).Countable) := by
  constructor
  · apply Cardinal.eq.mp
    rw [Cardinal.mk_Icc_real zero_lt_one]
    exact hCH.trans (Cardinal.mk_ord_toType _).symm
  · constructor
    · exact wellFounded_lt
    · intro w
      apply Cardinal.le_aleph0_iff_set_countable.mp
      apply Cardinal.lt_aleph_one_iff.mp
      have ho : (Cardinal.mk SierpinskiOrder).ord = Ordinal.type ((· < ·) : SierpinskiOrder → SierpinskiOrder → Prop) := by
        simp only [SierpinskiOrder, Cardinal.mk_ord_toType, Ordinal.type_toType]
      have h := Cardinal.mk_Iio_lt w ho
      simpa only [SierpinskiOrder, Cardinal.mk_ord_toType] using h

/-- The literal unit interval used in the printed counterexample. -/
abbrev SierpinskiInterval := Set.Icc (0 : ℝ) 1

/-- Lebesgue measure restricted to the unit interval and regarded as a measure on it. -/
noncomputable def sierpinskiIntervalMeasure : Measure SierpinskiInterval :=
  (volume : Measure ℝ).comap Subtype.val

instance sierpinskiInterval_probability : IsProbabilityMeasure sierpinskiIntervalMeasure where
  measure_univ := by
    change ((volume : Measure ℝ).comap (Subtype.val : SierpinskiInterval → ℝ)) Set.univ = 1
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply]
    simp only [Set.image_univ, Subtype.range_coe_subtype, ofPred_mem_eq]
    change volume (Set.Icc (0 : ℝ) 1) = 1
    simp only [Real.volume_Icc, sub_zero, ENNReal.ofReal_one]

instance sierpinskiInterval_nullSingletons : NullSingletonClass sierpinskiIntervalMeasure where
  measure_singleton x := by
    change ((volume : Measure ℝ).comap (Subtype.val : SierpinskiInterval → ℝ)) {x} = 0
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply]
    simp

/-- The unit interval with the completed Lebesgue σ-algebra, as in Rudin. -/
abbrev CompletedSierpinskiInterval :=
  NullMeasurableSpace SierpinskiInterval sierpinskiIntervalMeasure

noncomputable abbrev completeSierpinskiIntervalMeasure : Measure CompletedSierpinskiInterval :=
  sierpinskiIntervalMeasure.completion

instance completedSierpinskiInterval_probability :
    IsProbabilityMeasure completeSierpinskiIntervalMeasure where
  measure_univ := by
    change sierpinskiIntervalMeasure Set.univ = 1
    exact measure_univ

instance completedSierpinskiInterval_nullSingletons :
    NullSingletonClass completeSierpinskiIntervalMeasure where
  measure_singleton x := by
    change sierpinskiIntervalMeasure {x} = 0
    exact @measure_singleton SierpinskiInterval _ sierpinskiIntervalMeasure
      sierpinskiInterval_nullSingletons x

/-- 8.9(c) on the unit square, with CH as an explicit hypothesis. The section integrals
are those of the characteristic function of `Q`, because each section is measurable. -/
theorem unit_square_sierpinski_under_CH
    (hCH : Cardinal.continuum = (Cardinal.aleph 1 : Cardinal.{0})) :
    ∃ Q : Set (CompletedSierpinskiInterval × CompletedSierpinskiInterval),
      (∀ x : CompletedSierpinskiInterval, MeasurableSet {y | (x, y) ∈ Q} ∧
        completeSierpinskiIntervalMeasure {y | (x, y) ∈ Q} = 1) ∧
      (∀ y : CompletedSierpinskiInterval, MeasurableSet {x | (x, y) ∈ Q} ∧
        completeSierpinskiIntervalMeasure {x | (x, y) ∈ Q} = 0) ∧
      (∫⁻ x, completeSierpinskiIntervalMeasure {y | (x, y) ∈ Q} ∂completeSierpinskiIntervalMeasure) = 1 ∧
      (∫⁻ y, completeSierpinskiIntervalMeasure {x | (x, y) ∈ Q} ∂completeSierpinskiIntervalMeasure) = 0 ∧
      ¬ MeasurableSet Q := by
  obtain ⟨⟨j⟩, hw, hc⟩ := ch_unitInterval_wellOrder hCH
  exact ⟨sierpinskiSet j, sierpinski_counterexample completeSierpinskiIntervalMeasure j hw hc⟩

/-- The sections in Sierpinski's construction are Borel sets in the literal unit
interval, which is stronger than measurability in its Lebesgue completion. This
companion retains the Borel statement explicitly alongside the completed endpoint. -/
theorem unit_square_sierpinski_borel_sections_under_CH
    (hCH : Cardinal.continuum = (Cardinal.aleph 1 : Cardinal.{0})) :
    ∃ Q : Set (SierpinskiInterval × SierpinskiInterval),
      (∀ x : SierpinskiInterval,
        @MeasurableSet SierpinskiInterval (borel SierpinskiInterval) {y | (x, y) ∈ Q} ∧
          sierpinskiIntervalMeasure {y | (x, y) ∈ Q} = 1) ∧
      (∀ y : SierpinskiInterval,
        @MeasurableSet SierpinskiInterval (borel SierpinskiInterval) {x | (x, y) ∈ Q} ∧
          sierpinskiIntervalMeasure {x | (x, y) ∈ Q} = 0) ∧
      (∫⁻ x, sierpinskiIntervalMeasure {y | (x, y) ∈ Q} ∂sierpinskiIntervalMeasure) = 1 ∧
      (∫⁻ y, sierpinskiIntervalMeasure {x | (x, y) ∈ Q} ∂sierpinskiIntervalMeasure) = 0 ∧
      ¬ MeasurableSet Q := by
  obtain ⟨⟨j⟩, hw, hc⟩ := ch_unitInterval_wellOrder hCH
  have H := sierpinski_counterexample sierpinskiIntervalMeasure j hw hc
  have hb : (inferInstance : MeasurableSpace SierpinskiInterval) = borel SierpinskiInterval :=
    BorelSpace.measurable_eq
  refine ⟨sierpinskiSet j, ?_, ?_, H.2.2.1, H.2.2.2.1, H.2.2.2.2⟩
  · intro x
    refine ⟨?_, (H.1 x).2⟩
    rw [← hb]
    exact (H.1 x).1
  · intro y
    refine ⟨?_, (H.2.1 y).2⟩
    rw [← hb]
    exact (H.2.1 y).1

end RudinRCA.Chapter08
