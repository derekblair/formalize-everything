import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology unitInterval

namespace RudinRCA.Chapter06

/-- Relative Lebesgue measure on the closed unit interval charges every
nonempty relatively open set, including neighborhoods of either endpoint. -/
theorem unitInterval_volume_openPos :
    (volume : Measure I).IsOpenPosMeasure := by
  constructor
  intro U hU hUne
  rcases isOpen_induced_iff.mp hU with ⟨V, hV, rfl⟩
  obtain ⟨x, hx⟩ := hUne
  have hxcl : (x : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo zero_ne_one]
    exact x.property
  have hne : (V ∩ Ioo (0 : ℝ) 1).Nonempty :=
    mem_closure_iff.mp hxcl V hV hx
  have hpos : 0 < volume (V ∩ Ioo (0 : ℝ) 1) :=
    (hV.inter isOpen_Ioo).measure_pos volume hne
  rw [unitInterval.volume_apply]
  apply ne_of_gt
  apply hpos.trans_le
  apply measure_mono
  rintro y ⟨hyV, hyI⟩
  exact ⟨⟨y, hyI.1.le, hyI.2.le⟩, hyV, rfl⟩

private theorem continuous_eval_le_LpTop
    (f : C(I, ℂ)) (x : I) :
    ‖f x‖ ≤ ‖ContinuousMap.toLp ∞ volume ℂ f‖ := by
  letI := unitInterval_volume_openPos
  let J := ContinuousMap.toLp ∞ (volume : Measure I) ℂ (E := ℂ)
  have hae : ∀ᵐ y ∂(volume : Measure I), ‖f y‖ ≤ ‖J f‖ := by
    filter_upwards [enorm_ae_le_eLpNormEssSup (J f) volume,
      ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) volume f] with y hy hfy
    have he : eLpNormEssSup (J f) volume = ‖J f‖ₑ :=
      (eLpNorm_exponent_top (Lp.aestronglyMeasurable (J f))).symm.trans
        (Lp.enorm_def (J f)).symm
    rw [he, hfy] at hy
    exact enorm_le_iff_norm_le.mp hy
  have hd := Measure.dense_of_ae hae
  have hc : IsClosed {y : I | ‖f y‖ ≤ ‖J f‖} :=
    isClosed_le f.continuous.norm continuous_const
  have hx := hd x
  rwa [hc.closure_eq] at hx

/-- Endpoint evaluation on continuous functions extends to a bounded complex
functional on Lebesgue L-infinity of the closed unit interval. -/
theorem exists_LpTop_endpoint_extension :
    ∃ Φ : Lp ℂ ∞ (volume : Measure I) →L[ℂ] ℂ,
      ∀ f : C(I, ℂ), Φ (ContinuousMap.toLp ∞ volume ℂ f) = f 0 := by
  letI := unitInterval_volume_openPos
  let J : C(I, ℂ) →L[ℂ] Lp ℂ ∞ (volume : Measure I) := ContinuousMap.toLp ∞ volume ℂ
  have hJ : Function.Injective J := ContinuousMap.toLp_injective volume
  let e := LinearEquiv.ofInjective J.toLinearMap hJ
  let L : J.range →ₗ[ℂ] ℂ := (ContinuousMap.evalCLM ℂ (0 : I)).toLinearMap.comp e.symm.toLinearMap
  have hL (u : J.range) : ‖L u‖ ≤ 1 * ‖u‖ := by
    change ‖e.symm u 0‖ ≤ 1 * ‖u‖
    have hb := continuous_eval_le_LpTop (e.symm u) 0
    have he : J (e.symm u) = (u : Lp ℂ ∞ volume) :=
      congrArg Subtype.val (e.apply_symm_apply u)
    change ‖e.symm u 0‖ ≤ ‖J (e.symm u)‖ at hb
    rw [he] at hb
    simpa only [one_mul] using hb
  let F : J.range →L[ℂ] ℂ := L.mkContinuous 1 hL
  obtain ⟨Φ, hΦ, _⟩ := exists_extension_norm_eq J.range F
  refine ⟨Φ, ?_⟩
  intro f
  have h := hΦ (e f)
  change Φ (J f) = (e.symm (e f)) 0 at h
  simpa only [e.symm_apply_apply] using h

private def endpointBump (n : ℕ) : C(I, ℂ) where
  toFun x := (((1 - (x : ℝ)) ^ n : ℝ) : ℂ)
  continuous_toFun := by fun_prop

private theorem endpointBump_bound (n : ℕ) (x : I) : ‖endpointBump n x‖ ≤ 1 := by
  change ‖(((1 - (x : ℝ)) ^ n : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (sub_nonneg.mpr x.property.2) n)]
  exact pow_le_one₀ (sub_nonneg.mpr x.property.2) (by linarith [x.property.1])

/-- The negative endpoint assertion printed in6.15: on Lebesgue measure of
[0,1], some bounded complex L-infinity functional has no integrable density.
The stronger annihilator construction requested by Exercise13 is unnecessary. -/
theorem theorem_6_15_infinity_not_representable :
    ∃ Φ : Lp ℂ ∞ (volume : Measure I) →L[ℂ] ℂ,
      ¬ ∃ g : I → ℂ, Integrable g volume ∧
        ∀ f : Lp ℂ ∞ volume, Φ f = ∫ x, f x * g x ∂volume := by
  obtain ⟨Φ, hΦ⟩ := exists_LpTop_endpoint_extension
  refine ⟨Φ, ?_⟩
  rintro ⟨g, hg, hrep⟩
  have hint (n : ℕ) : (∫ x : I, endpointBump n x * g x ∂volume) = 1 := by
    calc
      _ = ∫ x : I, (ContinuousMap.toLp ∞ volume ℂ (endpointBump n)) x * g x ∂volume := by
        apply integral_congr_ae
        filter_upwards [ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) volume (endpointBump n)] with x hx
        rw [hx]
      _ = Φ (ContinuousMap.toLp ∞ volume ℂ (endpointBump n)) := (hrep _).symm
      _ = endpointBump n 0 := hΦ _
      _ = 1 := by simp [endpointBump]
  have hpoint : ∀ᵐ x : I ∂volume,
      Tendsto (fun n : ℕ ↦ endpointBump n x * g x) atTop (𝓝 (0 : ℂ)) := by
    have hxne : ∀ᵐ x : I ∂volume, x ≠ 0 := by simp
    filter_upwards [hxne] with x hx
    have hxreal : (x : ℝ) ≠ 0 := fun h ↦ hx (Subtype.ext h)
    have hxpos : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 hxreal.symm
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (sub_nonneg.mpr x.property.2) (show 1 - (x : ℝ) < 1 by linarith)
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hp
    change Tendsto (fun n : ℕ ↦ (((1 - (x : ℝ)) ^ n : ℝ) : ℂ) * g x) atTop (𝓝 0)
    simpa only [Complex.ofReal_zero, zero_mul] using hc.mul_const (g x)
  have hlim : Tendsto (fun n ↦ ∫ x : I, endpointBump n x * g x ∂volume) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := (volume : Measure I))
      (F := fun n x ↦ endpointBump n x * g x) (f := fun _ ↦ (0 : ℂ))
      (fun x ↦ ‖g x‖)
      (fun n ↦ (endpointBump n).continuous.aestronglyMeasurable.mul hg.aestronglyMeasurable)
      hg.norm (fun n ↦ ae_of_all _ fun x ↦ by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (endpointBump_bound n x)) hpoint
    simpa only [integral_zero] using h
  have heq : (1 : ℂ) = 0 := tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [hint] using hlim)
  exact one_ne_zero heq

#print axioms unitInterval_volume_openPos
#print axioms exists_LpTop_endpoint_extension
#print axioms theorem_6_15_infinity_not_representable
end RudinRCA.Chapter06
