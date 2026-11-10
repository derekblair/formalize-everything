import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Uncompiled draft of the actual boundary-limit prerequisite used by 15.19.
The first step constructs a Lipschitz primitive and proves almost-everywhere
angular differentiability of its boundary trace. The Poisson derivative peak
argument remains to be added; these lemmas alone do not claim radial limits.
-/

noncomputable section

open Complex MeasureTheory Metric Set Filter
open scoped Topology

namespace RudinRCA.Chapter15

/-- A bounded holomorphic function on the unit disc has a primitive with a
global Lipschitz extension. The extension retains the actual derivative on
the entire open disc. -/
theorem bounded_holomorphic_lipschitz_primitive {f : ℂ → ℂ} (M : ℝ≥0)
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖₊ ≤ M) :
    ∃ F : ℂ → ℂ, LipschitzWith (lipschitzExtensionConstant ℂ * M) F ∧
      ∀ z ∈ ball (0 : ℂ) 1, HasDerivAt F (f z) z := by
  obtain ⟨P, hP⟩ := hf.isExactOn_ball
  have hPlip : LipschitzOnWith M P (ball 0 1) :=
    (convex_ball (0 : ℂ) (1 : ℝ)).lipschitzOnWith_of_nnnorm_deriv_le
      (fun z hz ↦ (hP z hz).differentiableAt)
      (fun z hz ↦ by rw [(hP z hz).deriv]; exact hbound z hz)
  obtain ⟨F, hF, hFP⟩ := hPlip.extend_finite_dimension
  refine ⟨F, hF, ?_⟩
  intro z hz
  apply (hP z hz).congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact (hFP hw).symm

theorem lipschitz_unit_circle_parameter : LipschitzWith 1 (circleMap 0 1) := by
  apply lipschitzWith_of_nnnorm_deriv_le (differentiable_circleMap 0 1)
  intro θ
  change ‖deriv (circleMap 0 1) θ‖ ≤ (1 : ℝ)
  simp only [deriv_circleMap, norm_mul, norm_I, mul_one, norm_circleMap_zero, abs_one, le_refl]

/-- The boundary trace of the primitive has an ordinary angular derivative
almost everywhere. This conclusion is supplied by the proved real-variable
Lipschitz differentiation theorem, without assuming radial boundary values. -/
theorem bounded_holomorphic_primitive_boundary_differentiable_ae {f : ℂ → ℂ} (M : ℝ≥0)
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖₊ ≤ M) :
    ∃ F : ℂ → ℂ, LipschitzWith (lipschitzExtensionConstant ℂ * M) F ∧
      (∀ z ∈ ball (0 : ℂ) 1, HasDerivAt F (f z) z) ∧
      ∀ᵐ θ : ℝ, DifferentiableAt ℝ (fun t ↦ F (circleMap 0 1 t)) θ := by
  obtain ⟨F, hF, hderiv⟩ := bounded_holomorphic_lipschitz_primitive M hf hbound
  refine ⟨F, hF, hderiv, ?_⟩
  exact (hF.comp lipschitz_unit_circle_parameter).ae_differentiableAt_real

/-- The ordinary angular Poisson kernel of the unit disc. -/
def radialPoissonKernel (r t : ℝ) : ℝ :=
  (1 - r ^ 2) / (1 + r ^ 2 - 2 * r * Real.cos t)

/-- The nonnegative derivative peak used to recover the angular derivative
of the primitive from its boundary difference quotient. -/
def radialPoissonDerivativePeak (r t : ℝ) : ℝ :=
  r * (1 - r ^ 2) * (t * Real.sin t) /
    (Real.pi * (1 + r ^ 2 - 2 * r * Real.cos t) ^ 2)

theorem radialPoisson_denominator_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    0 < 1 + r ^ 2 - 2 * r * Real.cos t := by
  have hcos : 0 ≤ 2 * r * (1 - Real.cos t) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one t))
  nlinarith [sq_pos_of_pos (sub_pos.mpr hr1)]

theorem hasDerivAt_radialPoissonKernel {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    HasDerivAt (radialPoissonKernel r)
      (-(1 - r ^ 2) * (2 * r * Real.sin t) /
        (1 + r ^ 2 - 2 * r * Real.cos t) ^ 2) t := by
  convert (hasDerivAt_const t (1 - r ^ 2)).div
    ((hasDerivAt_const t (1 + r ^ 2)).sub ((Real.hasDerivAt_cos t).const_mul (2 * r)))
    (radialPoisson_denominator_pos hr0 hr1 t).ne' using 1 <;> ring

theorem radialPoissonDerivativePeak_eq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    radialPoissonDerivativePeak r t =
      -(t * deriv (radialPoissonKernel r) t) / (2 * Real.pi) := by
  rw [(hasDerivAt_radialPoissonKernel hr0 hr1 t).deriv]
  unfold radialPoissonDerivativePeak
  field_simp [Real.pi_ne_zero, (radialPoisson_denominator_pos hr0 hr1 t).ne'] <;> ring

theorem radialPoissonDerivativePeak_nonneg {r t : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ht : t ∈ Icc (-Real.pi) Real.pi) :
    0 ≤ radialPoissonDerivativePeak r t := by
  have htSin : 0 ≤ t * Real.sin t := by
    by_cases ht0 : 0 ≤ t
    · exact mul_nonneg ht0 (Real.sin_nonneg_of_nonneg_of_le_pi ht0 ht.2)
    · have hneg : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht0)
      have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hneg (by linarith [ht.1])
      rw [Real.sin_neg] at hsin
      exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge ht0) (by linarith)
  unfold radialPoissonDerivativePeak
  exact div_nonneg (mul_nonneg (mul_nonneg hr0 (by nlinarith)) htSin)
    (mul_nonneg Real.pi_pos.le (sq_nonneg _))

/-- Away from the angular origin, the derivative peak converges uniformly to
zero on every compact subset of the integration interval. The convergence
actually holds from both sides of r=1. -/
theorem radialPoissonDerivativePeak_uniformly_away_zero {K : Set ℝ}
    (hK : IsCompact K) (hKI : K ⊆ Icc (-Real.pi) Real.pi) (hK0 : 0 ∉ K) :
    TendstoUniformlyOn radialPoissonDerivativePeak (fun _ ↦ 0) (𝓝 (1 : ℝ)) K := by
  letI : CompactSpace K := hK.compactSpace
  let F : ℝ → K → ℝ := fun r t ↦ radialPoissonDerivativePeak r t
  have hcont : ContinuousOn F.uncurry (Ioo (0 : ℝ) 2 ×ˢ univ) := by
    unfold F radialPoissonDerivativePeak Function.uncurry
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    have ht := hKI x.2.property
    have ht0 : (x.2 : ℝ) ≠ 0 := fun h ↦ hK0 (h ▸ x.2.property)
    have hcos : Real.cos (x.2 : ℝ) < 1 := by
      apply lt_of_le_of_ne (Real.cos_le_one _)
      exact fun h ↦ ht0 ((Real.cos_eq_one_iff_of_lt_of_lt
        (by linarith [Real.pi_pos, ht.1]) (by linarith [Real.pi_pos, ht.2])).1 h)
    have hd : 0 < 1 + x.1 ^ 2 - 2 * x.1 * Real.cos (x.2 : ℝ) := by
      have hm : 0 < 2 * x.1 * (1 - Real.cos (x.2 : ℝ)) := by positivity
      nlinarith [sq_nonneg (x.1 - 1)]
    exact mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 hd.ne')
  have hlim := ContinuousOn.tendstoUniformly
    (Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)) hcont
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  simpa only [F, radialPoissonDerivativePeak, one_pow, sub_self, mul_zero, zero_mul,
    zero_div, Function.comp_def] using hlim

theorem radialPoissonKernel_eq_complex (r t : ℝ) :
    radialPoissonKernel r t = poissonKernel 0 (r : ℂ) (circleMap 0 1 t) := by
  have hd : ‖circleMap 0 1 t - (r : ℂ)‖ ^ 2 =
      1 + r ^ 2 - 2 * r * Real.cos t := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [circleMap, ofReal_one, one_mul, zero_add, exp_ofReal_mul_I,
      normSq_apply, sub_re, add_re, ofReal_re, mul_re, I_re, ofReal_im,
      I_im, sub_im, add_im, mul_im, mul_zero, zero_mul, sub_zero, add_zero,
      zero_add, mul_one]
    nlinarith [Real.sin_sq_add_cos_sq t]
  simp only [poissonKernel, sub_zero, norm_circleMap_zero, abs_one, one_pow,
    norm_real, Real.norm_eq_abs, sq_abs, hd, radialPoissonKernel]

theorem continuous_radialPoissonKernel {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (radialPoissonKernel r) :=
  fun t ↦ (hasDerivAt_radialPoissonKernel hr0 hr1 t).continuousAt

theorem continuous_deriv_radialPoissonKernel {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) : Continuous (deriv (radialPoissonKernel r)) := by
  have heq : deriv (radialPoissonKernel r) = fun t ↦
      -(1 - r ^ 2) * (2 * r * Real.sin t) /
        (1 + r ^ 2 - 2 * r * Real.cos t) ^ 2 :=
    funext fun t ↦ (hasDerivAt_radialPoissonKernel hr0 hr1 t).deriv
  rw [heq]
  exact (by fun_prop).div (by fun_prop)
    (fun t ↦ pow_ne_zero 2 (radialPoisson_denominator_pos hr0 hr1 t).ne')

theorem continuous_radialPoissonDerivativePeak {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) : Continuous (radialPoissonDerivativePeak r) := by
  simp_rw [radialPoissonDerivativePeak_eq hr0 hr1]
  exact (continuous_id.mul (continuous_deriv_radialPoissonKernel hr0 hr1)).neg.div_const _

/-- The normalization of the angular Poisson kernel follows from the already
proved complex Poisson formula applied to the constant function one. -/
theorem integral_radialPoissonKernel {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ t in -Real.pi..Real.pi, radialPoissonKernel r t = 2 * Real.pi := by
  have hr : (r : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_iff_norm, abs_of_nonneg hr0] using hr1
  have hformula := (diffContOnCl_const :
    DiffContOnCl ℂ (fun _ : ℂ ↦ (1 : ℂ)) (ball 0 1)).circleAverage_poissonKernel_smul hr
  have hc : ((2 * Real.pi)⁻¹ : ℝ) *
      (∫ t in 0..2 * Real.pi, radialPoissonKernel r t) = 1 := by
    simp only [Real.circleAverage, Pi.smul_apply, Complex.real_smul, mul_one,
      ← radialPoissonKernel_eq_complex, intervalIntegral.integral_ofReal,
      ← Complex.ofReal_mul, ← Complex.ofReal_one] at hformula
    exact Complex.ofReal_injective hformula
  have hmass : ∫ t in 0..2 * Real.pi, radialPoissonKernel r t = 2 * Real.pi := by
    calc
      _ = (2 * Real.pi) * (((2 * Real.pi)⁻¹ : ℝ) *
          (∫ t in 0..2 * Real.pi, radialPoissonKernel r t)) := by
            field_simp [Real.pi_ne_zero]
      _ = 2 * Real.pi := by rw [hc, mul_one]
  have hperiod : Function.Periodic (radialPoissonKernel r) (2 * Real.pi) := by
    intro t
    simp [radialPoissonKernel, Real.cos_add_two_pi]
  have hshift := hperiod.intervalIntegral_add_eq (-Real.pi) 0
  convert hshift.trans hmass using 1 <;> congr 1 <;> ring

/-- The differentiated Poisson peak has mass `1-Pᵣ(π)`. In particular its mass
tends to one at the boundary. -/
theorem integral_radialPoissonDerivativePeak {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ t in Icc (-Real.pi) Real.pi, radialPoissonDerivativePeak r t =
      1 - radialPoissonKernel r Real.pi := by
  have hP := continuous_radialPoissonKernel hr0 hr1
  have hPd := continuous_deriv_radialPoissonKernel hr0 hr1
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ ↦ t) (u' := fun _ ↦ (1 : ℝ))
    (v := radialPoissonKernel r) (v' := deriv (radialPoissonKernel r))
    (a := -Real.pi) (b := Real.pi)
    (fun t _ ↦ hasDerivAt_id t)
    (fun t _ ↦ (hasDerivAt_radialPoissonKernel hr0 hr1 t).differentiableAt.hasDerivAt)
    intervalIntegrable_const hPd.intervalIntegrable
  simp only [one_mul, radialPoissonKernel, Real.cos_neg] at hparts
  have hmass := integral_radialPoissonKernel hr0 hr1
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  simp_rw [radialPoissonDerivativePeak_eq hr0 hr1]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_neg]
  rw [hparts]
  change -(Real.pi * radialPoissonKernel r Real.pi -
    -Real.pi * radialPoissonKernel r Real.pi -
    ∫ t in -Real.pi..Real.pi, radialPoissonKernel r t) / (2 * Real.pi) = _
  rw [hmass]
  field_simp [Real.pi_ne_zero] <;> ring

theorem tendsto_integral_radialPoissonDerivativePeak :
    Tendsto (fun r ↦ ∫ t in Icc (-Real.pi) Real.pi, radialPoissonDerivativePeak r t)
      (𝓝[<] (1 : ℝ)) (𝓝 1) := by
  have hcont : ContinuousAt (fun r ↦ 1 - radialPoissonKernel r Real.pi) 1 := by
    unfold radialPoissonKernel
    exact continuousAt_const.sub ((by fun_prop).div (by fun_prop) (by norm_num))
  have hlim : Tendsto (fun r ↦ 1 - radialPoissonKernel r Real.pi)
      (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    simpa [radialPoissonKernel] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
  exact (integral_radialPoissonDerivativePeak hr.1.le hr.2).symm

/-- The derivative peak is an approximate identity at the angular origin.
Only ordinary continuity at zero is required of the boundary difference
quotient; all concentration and normalization hypotheses are proved here. -/
theorem radialPoissonDerivativePeak_approximate_identity {G : ℝ → ℂ} {a : ℂ}
    (hG : IntegrableOn G (Icc (-Real.pi) Real.pi))
    (hG0 : Tendsto G (𝓝 0) (𝓝 a)) :
    Tendsto (fun r ↦ ∫ t in Icc (-Real.pi) Real.pi,
      radialPoissonDerivativePeak r t • G t) (𝓝[<] (1 : ℝ)) (𝓝 a) := by
  apply tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto
    (s := Icc (-Real.pi) Real.pi) (t := Icc (-Real.pi) Real.pi) (x₀ := (0 : ℝ))
    measurableSet_Icc measurableSet_Icc subset_rfl self_mem_nhdsWithin
    (by simp) ?_ ?_ tendsto_integral_radialPoissonDerivativePeak ?_ hG
    (hG0.mono_left nhdsWithin_le_nhds)
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
    exact fun t ht ↦ radialPoissonDerivativePeak_nonneg hr.1.le hr.2 ht
  · intro U hU hU0
    exact (radialPoissonDerivativePeak_uniformly_away_zero
      (isCompact_Icc.diff hU) sdiff_subset (by simp [hU0])).mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
    exact (continuous_radialPoissonDerivativePeak hr.1.le hr.2).aestronglyMeasurable

/-- A difference quotient filled in by its derivative at the origin. -/
def radialBoundaryDifference (B : ℝ → ℂ) (θ : ℝ) (a : ℂ) : ℝ → ℂ :=
  Function.update (fun t ↦ t⁻¹ • (B (θ + t) - B θ)) 0 a

theorem continuous_radialBoundaryDifference {B : ℝ → ℂ} {θ : ℝ} {a : ℂ}
    (hB : Continuous B) (hd : HasDerivAt B a θ) :
    Continuous (radialBoundaryDifference B θ a) := by
  intro t
  by_cases ht : t = 0
  · subst t
    exact continuousAt_update_same.mpr hd.tendsto_slope_zero
  · apply (continuousAt_update_of_ne ht).mpr
    exact (continuousAt_id.inv₀ ht).smul
      ((hB.continuousAt.comp (continuousAt_const.add continuousAt_id)).sub
        continuousAt_const)

theorem radialBoundaryDifference_peak_limit {B : ℝ → ℂ} {θ : ℝ} {a : ℂ}
    (hB : Continuous B) (hd : HasDerivAt B a θ) :
    Tendsto (fun r ↦ ∫ t in Icc (-Real.pi) Real.pi,
      radialPoissonDerivativePeak r t • radialBoundaryDifference B θ a t)
      (𝓝[<] (1 : ℝ)) (𝓝 a) := by
  have hG := continuous_radialBoundaryDifference hB hd
  apply radialPoissonDerivativePeak_approximate_identity
    (hG.continuousOn.integrableOn_compact isCompact_Icc)
  simpa only [radialBoundaryDifference, Function.update_same] using hG.continuousAt.tendsto

theorem poissonKernel_circleMap_angle (r t θ : ℝ) :
    poissonKernel 0 (circleMap 0 r θ) (circleMap 0 1 t) =
      radialPoissonKernel r (t - θ) := by
  have he : circleMap 0 1 (t - θ) * circleMap 0 1 θ = circleMap 0 1 t := by
    simp only [circleMap, zero_add, ofReal_one, one_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have he' : (circleMap 0 1 (t - θ) - (r : ℂ)) * circleMap 0 1 θ =
      circleMap 0 1 t - circleMap 0 r θ := by
    rw [sub_mul, he]
    simp [circleMap]
  have hn : ‖circleMap 0 1 t - circleMap 0 r θ‖ =
      ‖circleMap 0 1 (t - θ) - (r : ℂ)‖ := by
    rw [← he', norm_mul, norm_circleMap_zero, abs_one, mul_one]
  rw [radialPoissonKernel_eq_complex]
  simp only [poissonKernel, sub_zero, norm_circleMap_zero, abs_one,
    norm_real, Real.norm_eq_abs, hn]

theorem radialPoisson_formula {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    (2 * Real.pi)⁻¹ • (∫ t in 0..2 * Real.pi,
      radialPoissonKernel r (t - θ) • F (circleMap 0 1 t)) = F (circleMap 0 r θ) := by
  have hr : circleMap 0 r θ ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_iff_norm, abs_of_nonneg hr0] using hr1
  simpa only [Real.circleAverage, Pi.smul_apply, poissonKernel_circleMap_angle]
    using hF.circleAverage_poissonKernel_smul hr

/-- Differentiation of the Poisson convolution in its angular parameter. A
compactness bound supplies the domination required by the integral derivative
theorem; no derivative of the boundary trace is used here. -/
theorem hasDerivAt_radialPoisson_convolution {B : ℝ → ℂ} (hB : Continuous B)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    HasDerivAt (fun η ↦ (2 * Real.pi)⁻¹ • (∫ t in 0..2 * Real.pi,
      radialPoissonKernel r (t - η) • B t))
      ((2 * Real.pi)⁻¹ • (∫ t in 0..2 * Real.pi,
        -deriv (radialPoissonKernel r) (t - θ) • B t)) θ := by
  let D : ℝ → ℝ → ℂ := fun η t ↦ -deriv (radialPoissonKernel r) (t - η) • B t
  have hD : Continuous D.uncurry :=
    ((continuous_deriv_radialPoissonKernel hr0 hr1).comp
      (continuous_snd.sub continuous_fst)).neg.smul (hB.comp continuous_snd)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (θ - 1) (θ + 1) ×ˢ Icc 0 (2 * Real.pi)) hD.continuousOn
  apply HasDerivAt.const_smul
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := D) (bound := fun _ ↦ C)
    (s := Ioo (θ - 1) (θ + 1)) (Ioo_mem_nhds (by linarith) (by linarith))
    ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
  · filter_upwards with η
    exact (((continuous_radialPoissonKernel hr0 hr1).comp
      (continuous_id.sub continuous_const)).smul hB).aestronglyMeasurable
  · exact (((continuous_radialPoissonKernel hr0 hr1).comp
      (continuous_id.sub continuous_const)).smul hB).intervalIntegrable
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards with t ht η hη
    apply hC (η, t)
    exact ⟨⟨hη.1.le, hη.2.le⟩,
      (uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi) ▸ ht).1.le,
      (uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi) ▸ ht).2⟩
  · filter_upwards with t _ η _
    have hPd := (hasDerivAt_radialPoissonKernel hr0 hr1 (t - η)).differentiableAt.hasDerivAt
    convert (hPd.comp η ((hasDerivAt_id η).const_sub t)).smul_const (B t) using 1 <;>
      simp [D, Function.comp_def]

theorem radialPoisson_angular_derivative {F f : ℂ → ℂ}
    (hF : DiffContOnCl ℂ F (ball 0 1)) (hFc : Continuous F)
    (hFd : ∀ z ∈ ball (0 : ℂ) 1, HasDerivAt F (f z) z)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    (2 * Real.pi)⁻¹ • (∫ t in 0..2 * Real.pi,
      -deriv (radialPoissonKernel r) (t - θ) • F (circleMap 0 1 t)) =
      f (circleMap 0 r θ) * (circleMap 0 r θ * I) := by
  have hleft := hasDerivAt_radialPoisson_convolution
    (hFc.comp (continuous_circleMap 0 1)) hr0 hr1 θ
  have heq : (fun η ↦ (2 * Real.pi)⁻¹ • (∫ t in 0..2 * Real.pi,
      radialPoissonKernel r (t - η) • F (circleMap 0 1 t))) =
      fun η ↦ F (circleMap 0 r η) := funext (radialPoisson_formula hF hr0 hr1)
  rw [heq] at hleft
  have hr : circleMap 0 r θ ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_iff_norm, abs_of_nonneg hr0] using hr1
  exact hleft.unique ((hFd _ hr).comp θ (hasDerivAt_circleMap 0 r θ))

#print axioms bounded_holomorphic_lipschitz_primitive
#print axioms lipschitz_unit_circle_parameter
#print axioms bounded_holomorphic_primitive_boundary_differentiable_ae
#print axioms radialPoisson_denominator_pos
#print axioms hasDerivAt_radialPoissonKernel
#print axioms radialPoissonDerivativePeak_eq
#print axioms radialPoissonDerivativePeak_nonneg
#print axioms radialPoissonDerivativePeak_uniformly_away_zero
#print axioms radialPoissonKernel_eq_complex
#print axioms integral_radialPoissonKernel
#print axioms integral_radialPoissonDerivativePeak
#print axioms tendsto_integral_radialPoissonDerivativePeak
#print axioms radialPoissonDerivativePeak_approximate_identity
#print axioms continuous_radialBoundaryDifference
#print axioms radialBoundaryDifference_peak_limit
#print axioms poissonKernel_circleMap_angle
#print axioms radialPoisson_formula
#print axioms hasDerivAt_radialPoisson_convolution
#print axioms radialPoisson_angular_derivative

end RudinRCA.Chapter15
