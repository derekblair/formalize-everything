import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Operator.Basic

/-! Zero extension from a measurable restriction, for the sigma-finite Lp duality proof. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]

set_option maxHeartbeats 800000 in
/-- Zero extension is a complex-linear isometry from Lp of a measurable
restriction into Lp of the ambient measure. -/
def lpZeroExtend {S : Set X} (hS : MeasurableSet S) :
    Lp ℂ p (μ.restrict S) →ₗᵢ[ℂ] Lp ℂ p μ where
  toFun f := ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).toLp (S.indicator f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards
      [MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp (f + g))),
        Lp.coeFn_add
          (((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).toLp (S.indicator f))
          (((memLp_indicator_iff_restrict hS).mpr (Lp.memLp g)).toLp (S.indicator g)),
        MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)),
        MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp g)),
        (ae_eq_restrict_iff_indicator_ae_eq hS).mp (Lp.coeFn_add f g)]
      with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₂, Pi.add_apply, h₃, h₄, h₅]
    by_cases hx : x ∈ S <;> simp [hx]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards
      [MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp (c • f))),
        Lp.coeFn_smul c
          (((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).toLp (S.indicator f)),
        MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)),
        (ae_eq_restrict_iff_indicator_ae_eq hS).mp (Lp.coeFn_smul c f)]
      with x h₁ h₂ h₃ h₄
    rw [h₁, h₂, Pi.smul_apply, h₃, h₄]
    by_cases hx : x ∈ S <;> simp [hx]
  norm_map' f := by
    rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_indicator_eq_eLpNorm_restrict hS]

theorem lpZeroExtend_coeFn {S : Set X} (hS : MeasurableSet S)
    (f : Lp ℂ p (μ.restrict S)) :
    lpZeroExtend μ p hS f =ᵐ[μ] S.indicator f :=
  MemLp.coeFn_toLp _

/-- Restrict a functional by applying it to zero extensions. -/
def lpFunctionalOnRestriction (Φ : Lp ℂ p μ →L[ℂ] ℂ)
    {S : Set X} (hS : MeasurableSet S) : Lp ℂ p (μ.restrict S) →L[ℂ] ℂ :=
  Φ.comp (lpZeroExtend μ p hS).toContinuousLinearMap

theorem lpFunctionalOnRestriction_norm_le (Φ : Lp ℂ p μ →L[ℂ] ℂ)
    {S : Set X} (hS : MeasurableSet S) :
    ‖lpFunctionalOnRestriction μ p Φ hS‖ ≤ ‖Φ‖ := by
  calc
    _ ≤ ‖Φ‖ * ‖(lpZeroExtend μ p hS).toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Φ‖ * 1 := mul_le_mul_of_nonneg_left
      (lpZeroExtend μ p hS).norm_toContinuousLinearMap_le (norm_nonneg _)
    _ = ‖Φ‖ := mul_one _

theorem lpZeroExtend_indicatorConstLp {S E : Set X} (hS : MeasurableSet S)
    (hE : MeasurableSet E) (hES : E ⊆ S) (hμE : μ E ≠ ∞) (c : ℂ) :
    lpZeroExtend μ p hS
      (indicatorConstLp p hE (ne_top_of_le_ne_top hμE (Measure.restrict_le_self E)) c) =
        indicatorConstLp p hE hμE c := by
  apply Lp.ext
  have hlocal := (ae_eq_restrict_iff_indicator_ae_eq hS).mp
    (indicatorConstLp_coeFn (p := p) (μ := μ.restrict S) (hs := hE)
      (hμs := ne_top_of_le_ne_top hμE (Measure.restrict_le_self E)) (c := c))
  filter_upwards [lpZeroExtend_coeFn μ p hS
    (indicatorConstLp p hE (ne_top_of_le_ne_top hμE (Measure.restrict_le_self E)) c),
      hlocal, (indicatorConstLp_coeFn (p := p) (μ := μ) (hs := hE) (hμs := hμE) (c := c))]
    with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  by_cases hx : x ∈ E
  · simp [hx, hES hx]
  · simp [hx]

#print axioms lpZeroExtend
#print axioms lpZeroExtend_coeFn
#print axioms lpFunctionalOnRestriction
#print axioms lpFunctionalOnRestriction_norm_le
#print axioms lpZeroExtend_indicatorConstLp

end RudinRCA.Chapter06
