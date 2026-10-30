import Scratch616B
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! The finite-measure p = 1 bound in the proof of Rudin 6.16. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ComplexConjugate

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

/-- The bounded complex phase that turns z into its norm by multiplication. -/
def dualityPhase (z : ℂ) : ℂ := conj z / (‖z‖ : ℂ)

theorem dualityPhase_mul (z : ℂ) : dualityPhase z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [dualityPhase, hz]
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
  rw [dualityPhase, div_mul_eq_mul_div, div_eq_iff hn]
  simpa only [pow_two] using Complex.conj_mul' z

theorem norm_dualityPhase_le (z : ℂ) : ‖dualityPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [dualityPhase, hz]
  simp [dualityPhase, norm_div, norm_ne_zero_iff.mpr hz]

theorem measurable_dualityPhase : Measurable dualityPhase := by
  unfold dualityPhase
  fun_prop

variable (μ : Measure X) [IsFiniteMeasure μ]

/-- A density representing an L1 functional on indicators is essentially
bounded by the norm of the functional. -/
theorem lpOneFunctional_density_ae_bound
    (Φ : Lp ℂ 1 μ →L[ℂ] ℂ) {g : X → ℂ} (hgm : Measurable g) (hg : Integrable g μ)
    (hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp 1 hE (measure_ne_top μ E) 1) = ∫ x in E, g x ∂μ) :
    ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖Φ‖ := by
  apply ae_le_of_forall_setIntegral_le hg.norm (integrable_const ‖Φ‖)
  intro E hE hμE
  let f : X → ℂ := E.indicator (fun x => dualityPhase (g x))
  have hfm : Measurable f := (measurable_dualityPhase.comp hgm).indicator hE
  have hfbound : ∀ x, ‖f x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ E
    · simpa only [f, indicator_of_mem hx] using norm_dualityPhase_le (g x)
    · simp [f, hx]
  have hfp : MemLp f 1 μ := MemLp.of_bound hfm.aestronglyMeasurable 1 (ae_of_all μ hfbound)
  let F := hfp.toLp f
  have hFnorm : ‖F‖ ≤ μ.real E := by
    have hle : ‖F‖ ≤ ‖indicatorConstLp 1 hE (measure_ne_top μ E) (1 : ℂ)‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [MemLp.coeFn_toLp hfp,
        (indicatorConstLp_coeFn (p := 1) (hs := hE)
          (hμs := measure_ne_top μ E) (c := (1 : ℂ)))] with x h₁ h₂
      change ‖hfp.toLp f x‖ ≤ ‖indicatorConstLp 1 hE (measure_ne_top μ E) (1 : ℂ) x‖
      rw [h₁, h₂]
      by_cases hx : x ∈ E
      · simpa [hx] using hfbound x
      · simp [f, hx]
    simpa [norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top] using hle
  have hΦF : Φ F = Complex.ofReal (∫ x in E, ‖g x‖ ∂μ) := by
    have hrep := lpFunctional_eq_bounded_of_indicator μ 1 ENNReal.one_ne_top Φ hg hind
      hfm 1 hfbound hfp
    have hprod : (fun x => f x * g x) = E.indicator (fun x => (‖g x‖ : ℂ)) := by
      funext x
      by_cases hx : x ∈ E
      · simpa only [f, indicator_of_mem hx] using dualityPhase_mul (g x)
      · simp [f, hx]
    change Φ (hfp.toLp f) = _
    rw [hrep, hprod, integral_indicator hE, integral_complex_ofReal]
  have hnonneg : 0 ≤ ∫ x in E, ‖g x‖ ∂μ := integral_nonneg fun x => norm_nonneg _
  calc
    (∫ x in E, ‖g x‖ ∂μ) = ‖Φ F‖ := by
      rw [hΦF, Complex.norm_real, Real.norm_of_nonneg hnonneg]
    _ ≤ ‖Φ‖ * ‖F‖ := Φ.le_opNorm F
    _ ≤ ‖Φ‖ * μ.real E := mul_le_mul_of_nonneg_left hFnorm (norm_nonneg _)
    _ = ∫ x in E, ‖Φ‖ ∂μ := by simp [mul_comm]

theorem lpOneFunctional_density_memLp_top
    (Φ : Lp ℂ 1 μ →L[ℂ] ℂ) {g : X → ℂ} (hgm : Measurable g) (hg : Integrable g μ)
    (hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp 1 hE (measure_ne_top μ E) 1) = ∫ x in E, g x ∂μ) :
    MemLp g ∞ μ :=
  memLp_top_of_bound hg.aestronglyMeasurable ‖Φ‖
    (lpOneFunctional_density_ae_bound μ Φ hgm hg hind)

#print axioms dualityPhase_mul
#print axioms norm_dualityPhase_le
#print axioms measurable_dualityPhase
#print axioms lpOneFunctional_density_ae_bound
#print axioms lpOneFunctional_density_memLp_top

end RudinRCA.Chapter06
