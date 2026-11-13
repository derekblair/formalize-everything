module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Layercake

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution

namespace RudinRCA.Chapter08

/-- Rudin's convolution convention, including the standard zero choice on the null set
where the Bochner integral is not defined. -/
noncomputable def rudinConvolution (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, f (x - y) * g y

lemma rudinConvolution_eq (f g : ℝ → ℂ) :
    rudinConvolution f g = convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext x
  exact (convolution_mul_swap (f := f) (g := g) (x := x)).symm

/-- 8.14: absolute convergence for almost every point, integrability of the convolution,
and the sharp L¹ norm estimate. The functions are arbitrary Lebesgue-a.e. measurable
representatives, not just Borel representatives. -/
theorem theorem_8_14 {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∀ᵐ x : ℝ, Integrable (fun y => f (x - y) * g y)) ∧
    Integrable (rudinConvolution f g) ∧
    (∫ x, ‖rudinConvolution f g x‖) ≤ (∫ x, ‖f x‖) * (∫ x, ‖g x‖) := by
  have hex := hf.ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ) hg
  have hi := hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hex] with x hx
    exact hx.integrable_swap
  · simpa only [rudinConvolution_eq] using hi
  · rw [rudinConvolution_eq]
    calc
      (∫ x, ‖convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume x‖) ≤
          ∫ x, convolution (fun t => ‖f t‖) (fun t => ‖g t‖)
            (ContinuousLinearMap.mul ℝ ℝ) volume x := by
        apply integral_mono hi.norm
          (hf.norm.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hg.norm)
        intro x
        simp only [convolution_mul]
        simpa only [norm_mul] using norm_integral_le_integral_norm (fun t => f t * g (x - t))
      _ = (∫ x, ‖f x‖) * (∫ x, ‖g x‖) := by
        exact integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf.norm hg.norm

/-- 8.15: Rudin's distribution function, defined at every real threshold.
Only its restriction to the nonnegative real line is used in the book. -/
noncomputable def distributionFunction {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  μ {x | ENNReal.ofReal t < f x}

/-- 8.15: the distribution function is nonincreasing. -/
theorem distributionFunction_antitone {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) : Antitone (distributionFunction μ f) := by
  intro s t hst
  exact measure_mono fun x hx => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) hx

/-- 8.15: the distribution function is Borel measurable. -/
theorem distributionFunction_measurable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) : Measurable (distributionFunction μ f) :=
  (distributionFunction_antitone μ f).measurable

-- The following finite-valued cases are support lemmas only; they do NOT complete
-- Rudin 8.15/8.16, where f may take the value ∞.
theorem layerCake_real {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} (hf : AEMeasurable f μ) (hfn : 0 ≤ᵐ[μ] f) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ∫⁻ t in Ioi 0, μ {x | t < f x} :=
  lintegral_eq_lintegral_meas_lt μ hfn hf

theorem layerCake_integratedWeight_real {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} {g : ℝ → ℝ}
    (hf : AEMeasurable f μ) (hfn : 0 ≤ᵐ[μ] f)
    (hg : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (hgn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ g t) :
    ∫⁻ x, ENNReal.ofReal (∫ t in 0..f x, g t) ∂μ =
      ∫⁻ t in Ioi 0, μ {x | t < f x} * ENNReal.ofReal (g t) :=
  lintegral_comp_eq_lintegral_meas_lt_mul μ hfn hf hg hgn


end RudinRCA.Chapter08
