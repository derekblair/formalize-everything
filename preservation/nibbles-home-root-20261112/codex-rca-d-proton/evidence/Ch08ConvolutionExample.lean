module

/- Abandoned duplicate draft: root-owned Ch08ProductExample.lean supersedes this file.
Not compiled, not included in combined support checks, and not proposed for integration. -/

public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Complex.Basic

public section

open MeasureTheory Set

namespace RudinRCA.Chapter08

/-- The exact singular function used in the discussion preceding the convolution theorem. -/
noncomputable def convolutionSingularity (x : ℝ) : ℝ :=
  (Ioo (0 : ℝ) 1).indicator (fun x => x ^ (-(1 / 2 : ℝ))) x

theorem convolutionSingularity_integrable : Integrable convolutionSingularity := by
  apply (integrable_indicator_iff measurableSet_Ioo).mpr
  exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mpr
    (by norm_num)

theorem convolutionSingularity_product_not_integrable :
    ¬ Integrable (fun x => convolutionSingularity x * convolutionSingularity x) := by
  intro hi
  have he (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      convolutionSingularity x * convolutionSingularity x = x ^ (-1 : ℝ) := by
    simp only [convolutionSingularity, indicator_of_mem hx]
    rw [← Real.rpow_add hx.1]
    norm_num
  have hpow : IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Ioo 0 1) :=
    hi.integrableOn.congr_fun he measurableSet_Ioo
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mp hpow
  linarith

/-- 8.13's counterexample, included as complex-valued L1 functions. -/
theorem example_8_13 :
    Integrable (fun x : ℝ => (convolutionSingularity x : ℂ)) ∧
      ¬ Integrable (fun x : ℝ =>
        (convolutionSingularity x : ℂ) * (convolutionSingularity x : ℂ)) := by
  refine ⟨convolutionSingularity_integrable.ofReal, ?_⟩
  intro hi
  apply convolutionSingularity_product_not_integrable
  have hreal := hi.re
  simpa using hreal

end RudinRCA.Chapter08
