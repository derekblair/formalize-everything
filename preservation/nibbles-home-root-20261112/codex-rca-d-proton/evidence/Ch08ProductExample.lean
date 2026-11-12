module

public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.Convolution

public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RudinRCA.Chapter08

/-- The function in 8.13: x^(-1/2) on (0,1), zero elsewhere. -/
def inverseSqrtExample : ℝ → ℝ := (Ioo (0 : ℝ) 1).indicator (fun x => x ^ (-1 / 2 : ℝ))

/-- The printed function in 8.13 is in L1. -/
theorem inverseSqrtExample_integrable : Integrable inverseSqrtExample := by
  rw [inverseSqrtExample, integrable_indicator_iff measurableSet_Ioo]
  exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by norm_num)

/-- A product of two L1 functions need not be in L1, using the printed example. -/
theorem inverseSqrtExample_square_not_integrable :
    ¬ Integrable (fun x => inverseSqrtExample x * inverseSqrtExample x) := by
  have heq : (fun x => inverseSqrtExample x * inverseSqrtExample x) =
      (Ioo (0 : ℝ) 1).indicator (fun x => x ^ (-1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Ioo (0 : ℝ) 1
    · simp only [inverseSqrtExample, indicator_of_mem hx]
      rw [← Real.rpow_add hx.1]
      norm_num
    · simp [inverseSqrtExample, hx]
  rw [heq, integrable_indicator_iff measurableSet_Ioo,
    intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
  exact lt_irrefl _

/-- Extended-valued positive convolution from 8.13, defined even at exceptional points. -/
def positiveConvolution (f g : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (f (x - y) * g y)

/-- 8.13: positive L1 factors give a finite positive convolution almost everywhere,
with finite integral; the exceptional values were never replaced by zero. -/
theorem positiveConvolution_finite {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    AEMeasurable (positiveConvolution f g) volume ∧
    (∫⁻ x, positiveConvolution f g x) < ∞ ∧
    (∀ᵐ x, positiveConvolution f g x < ∞) := by
  have hi : Integrable (fun p : ℝ × ℝ => f (p.1 - p.2) * g p.2)
      (volume.prod volume) := by
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
      hg.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hf
  have he (p : ℝ × ℝ) : ‖f (p.1 - p.2) * g p.2‖ₑ =
      ENNReal.ofReal (f (p.1 - p.2) * g p.2) :=
    Real.enorm_eq_ofReal (mul_nonneg (hfn _) (hgn _))
  have hm : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (f (p.1 - p.2) * g p.2))
      (volume.prod volume) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hi.aestronglyMeasurable.aemeasurable
  have hfinProd : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (f (p.1 - p.2) * g p.2)
      ∂volume.prod volume) < ∞ := by
    simpa only [hasFiniteIntegral_iff_enorm, he] using hi.hasFiniteIntegral
  have hm' : AEMeasurable (positiveConvolution f g) volume := hm.lintegral_prod_right'
  have hfin : (∫⁻ x, positiveConvolution f g x) < ∞ := by
    change (∫⁻ x, ∫⁻ y, ENNReal.ofReal (f (x - y) * g y)) < ∞
    rw [← lintegral_prod _ hm]
    exact hfinProd
  exact ⟨hm', hfin, ae_lt_top' hm' hfin.ne⟩

end RudinRCA.Chapter08
