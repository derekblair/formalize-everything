module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

public section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

/-- The centered Hardy–Littlewood maximal function, using all positive radii.
For Euclidean space and Lebesgue measure this is Rudin's maximal function of `|f|`. -/
noncomputable def maximalFunction {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ r : ℝ, ⨆ (_ : 0 < r), (∫⁻ y in ball x r, ‖f y‖ₑ ∂μ) / μ (ball x r)

/-- 8.17's L∞ estimate in the stronger pointwise form. The concrete weak (1,1)
estimate is proved separately by the covering argument. -/
theorem maximalFunction_le_essSup {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) (x : X) :
    maximalFunction μ f x ≤ eLpNormEssSup f μ := by
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  calc
    (∫⁻ y in ball x r, ‖f y‖ₑ ∂μ) / μ (ball x r) ≤
        (eLpNormEssSup f μ * μ (ball x r)) / μ (ball x r) := by
      apply ENNReal.div_le_div_right
      calc
        (∫⁻ y in ball x r, ‖f y‖ₑ ∂μ) ≤
            ∫⁻ _y in ball x r, eLpNormEssSup f μ ∂μ :=
          lintegral_mono_ae (ae_restrict_of_ae ae_le_eLpNormEssSup)
        _ = _ := by simp
    _ ≤ eLpNormEssSup f μ := by
      rw [div_eq_mul_inv, mul_assoc]
      exact (mul_le_mul_right (ENNReal.mul_inv_le_one _) _).trans_eq (mul_one _)

/-- The high part in Rudin's interpolation proof is integrable. This is support for
8.18, not the maximal-function theorem itself. -/
theorem integrable_highPart {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℂ} (hfmeas : Measurable f)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ∞) (hf : MemLp f p μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) (hεtop : ε ≠ ∞) :
    Integrable ({x | ε < ‖f x‖ₑ}.indicator f) μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hs : MeasurableSet {x | ε < ‖f x‖ₑ} :=
    measurableSet_lt measurable_const hfmeas.enorm
  have hsub : {x | ε < ‖f x‖ₑ} ⊆ {x | ε ≤ ‖f x‖ₑ} := by
    intro x hx
    change ε < ‖f x‖ₑ at hx
    change ε ≤ ‖f x‖ₑ
    exact hx.le
  have hmeasure : μ {x | ε < ‖f x‖ₑ} < ∞ :=
    (measure_mono hsub).trans_lt
      (hf.meas_ge_lt_top'_enorm hp0 hptop hε (fun h => (hεtop h).elim))
  apply memLp_one_iff_integrable.mp
  exact (hf.indicator hs).mono_exponent_of_measure_support_ne_top
    (fun x hx => Set.indicator_of_notMem hx f) hmeasure.ne hp

end RudinRCA.Chapter08
