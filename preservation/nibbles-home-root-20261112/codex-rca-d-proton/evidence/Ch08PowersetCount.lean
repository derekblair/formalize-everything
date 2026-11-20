module
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Count

public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RudinRCA.Chapter08

/-- A copy of X with the power-set sigma algebra used for the counting factor in 8.9(b). -/
structure PowersetCopy (X : Type*) where
  val : X

instance (X : Type*) : MeasurableSpace (PowersetCopy X) := ⊤
instance (X : Type*) : MeasurableSingletonClass (PowersetCopy X) := ⟨fun _ => trivial⟩

/-- 8.9(b), with the full power-set counting sigma algebra and an arbitrary atomless
probability first factor. The explicit diagonal measurability hypothesis holds for the
completed Lebesgue unit interval, as shown in the specialization below. -/
theorem powerset_counting_counterexample {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hd : MeasurableSet {p : X × X | p.1 = p.2}) :
    ∃ Q : Set (X × PowersetCopy X), MeasurableSet Q ∧
      (∀ x, Measure.count {y | (x, y) ∈ Q} = 1) ∧
      (∀ y, μ {x | (x, y) ∈ Q} = 0) ∧
      (∫⁻ x, Measure.count {y | (x, y) ∈ Q} ∂μ) = 1 ∧
      (∫⁻ y, μ {x | (x, y) ∈ Q} ∂Measure.count) = 0 := by
  let Q : Set (X × PowersetCopy X) := {p | p.1 = p.2.val}
  have hv : Measurable (PowersetCopy.val : PowersetCopy X → X) := fun _ _ => trivial
  have hQ : MeasurableSet Q := hd.preimage (measurable_fst.prodMk (hv.comp measurable_snd))
  have hx (x : X) : {y : PowersetCopy X | (x, y) ∈ Q} = {⟨x⟩} := by
    ext y
    cases y
    simp [Q, eq_comm]
  have hy (y : PowersetCopy X) : {x : X | (x, y) ∈ Q} = {y.val} := by
    ext x
    simp [Q]
  refine ⟨Q, hQ, ?_, ?_, ?_, ?_⟩
  · intro x; rw [hx]; simp
  · intro y; rw [hy]; simp
  · simp_rw [hx]; simp
  · simp_rw [hy]; simp

/-- The exact completed-Lebesgue / power-set-counting unit-square instance of 8.9(b).
This declaration is assembled after the interval-measure definitions accompanying 8.9(c). -/
theorem unit_square_powerset_counting_counterexample :
    ∃ Q : Set (CompletedSierpinskiInterval × PowersetCopy CompletedSierpinskiInterval),
      MeasurableSet Q ∧
      (∀ x, Measure.count {y | (x, y) ∈ Q} = 1) ∧
      (∀ y, completeSierpinskiIntervalMeasure {x | (x, y) ∈ Q} = 0) ∧
      (∫⁻ x, Measure.count {y | (x, y) ∈ Q} ∂completeSierpinskiIntervalMeasure) = 1 ∧
      (∫⁻ y, completeSierpinskiIntervalMeasure {x | (x, y) ∈ Q} ∂Measure.count) = 0 := by
  apply powerset_counting_counterexample completeSierpinskiIntervalMeasure
  have hm : Measurable (fun x : CompletedSierpinskiInterval => (show SierpinskiInterval from x).val) := by
    intro s hs
    exact (measurable_subtype_coe hs).nullMeasurableSet
  have hd := measurableSet_eq_fun (hm.comp measurable_fst) (hm.comp measurable_snd)
  convert hd using 1
  ext p
  exact Subtype.ext_iff

/-- The counting factor used in the exact example is not sigma-finite. -/
theorem unit_interval_powerset_count_not_sigmaFinite :
    ¬ SigmaFinite (Measure.count : Measure (PowersetCopy CompletedSierpinskiInterval)) := by
  intro hc
  letI := hc
  obtain ⟨Q, hQ, _, _, hi, hj⟩ := unit_square_powerset_counting_counterexample
  have h := (Measure.prod_apply (μ := completeSierpinskiIntervalMeasure)
    (ν := (Measure.count : Measure (PowersetCopy CompletedSierpinskiInterval))) hQ).symm.trans
    (Measure.prod_apply_symm (μ := completeSierpinskiIntervalMeasure)
      (ν := (Measure.count : Measure (PowersetCopy CompletedSierpinskiInterval))) hQ)
  change (∫⁻ x, Measure.count {y | (x, y) ∈ Q} ∂completeSierpinskiIntervalMeasure) =
    (∫⁻ y, completeSierpinskiIntervalMeasure {x | (x, y) ∈ Q} ∂Measure.count) at h
  rw [hi, hj] at h
  exact one_ne_zero h

end RudinRCA.Chapter08
