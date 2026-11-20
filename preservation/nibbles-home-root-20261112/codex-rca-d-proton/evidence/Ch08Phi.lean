module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

/-- Weighted Cavalieri formula, retaining infinite values of `f`. -/
theorem layerCake_ennreal_weight {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x, ∫⁻ t in Ioi 0, {t : ℝ | ENNReal.ofReal t < f x}.indicator g t ∂volume ∂μ) =
      ∫⁻ t in Ioi 0, μ {x | ENNReal.ofReal t < f x} * g t := by
  let F : X × ℝ → ℝ≥0∞ :=
    {q : X × ℝ | ENNReal.ofReal q.2 < f q.1}.indicator (fun q => g q.2)
  have hset : MeasurableSet {q : X × ℝ | ENNReal.ofReal q.2 < f q.1} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hf.comp measurable_fst)
  have hF : Measurable F := (hg.comp measurable_snd).indicator hset
  change (∫⁻ x, ∫⁻ t in Ioi 0, F (x, t) ∂volume ∂μ) = _
  calc
    _ = ∫⁻ t in Ioi 0, ∫⁻ x, F (x, t) ∂μ :=
      lintegral_lintegral_swap (μ := μ) (ν := volume.restrict (Ioi 0))
        (f := fun x t => F (x, t)) hF.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro t
      change (∫⁻ x, {x | ENNReal.ofReal t < f x}.indicator (fun _ => g t) x ∂μ) = _
      rw [lintegral_indicator (measurableSet_lt measurable_const hf)]
      simp [mul_comm]

lemma lintegral_deriv_Ioo {φ : ℝ → ℝ} (hm : Monotone φ) (h0 : φ 0 = 0)
    {T : ℝ} (hT : 0 ≤ T) (ha : AbsolutelyContinuousOnInterval φ 0 T) :
    ∫⁻ t in Ioo 0 T, ENNReal.ofReal (deriv φ t) = ENNReal.ofReal (φ T) := by
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Ioc : Ioo 0 T =ᵐ[volume] Ioc 0 T)]
  rw [← ofReal_integral_eq_lintegral_ofReal ha.intervalIntegrable_deriv.1
    (Eventually.of_forall fun _ => hm.deriv_nonneg)]
  rw [← intervalIntegral.integral_of_le hT, ha.integral_deriv_eq_sub, h0, sub_zero]

/-- Extending a nonnegative real function continuously to a possibly infinite value at infinity. -/
noncomputable def extendedNonnegative (φ : ℝ → ℝ) (φInfinity : ℝ≥0∞) (a : ℝ≥0∞) : ℝ≥0∞ :=
  if a = ∞ then φInfinity else ENNReal.ofReal (φ a.toReal)

lemma extendedNonnegative_eq_integral {φ : ℝ → ℝ} {φInfinity : ℝ≥0∞}
    (hm : Monotone φ) (h0 : φ 0 = 0)
    (hac : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval φ 0 T)
    (hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (φ t)) atTop (𝓝 φInfinity))
    (a : ℝ≥0∞) :
    extendedNonnegative φ φInfinity a =
      ∫⁻ t in Ioi 0, {t : ℝ | ENNReal.ofReal t < a}.indicator
        (fun t => ENNReal.ofReal (deriv φ t)) t := by
  by_cases ha : a = ∞
  · subst a
    simp only [extendedNonnegative, if_pos rfl, ENNReal.ofReal_lt_top,
      setOf_true, indicator_univ]
    let ν : Measure ℝ := volume.restrict (Ioi 0)
    have hc : AECover ν atTop (fun n : ℕ => Iio (n : ℝ)) :=
      aecover_Iio (μ := ν) tendsto_natCast_atTop_atTop
    have he (n : ℕ) :
        ∫⁻ t in Iio (n : ℝ), ENNReal.ofReal (deriv φ t) ∂ν =
          ENNReal.ofReal (φ n) := by
      rw [show ν = volume.restrict (Ioi 0) from rfl,
        Measure.restrict_restrict measurableSet_Iio]
      have hs : Iio (n : ℝ) ∩ Ioi 0 = Ioo 0 (n : ℝ) := by
        ext t
        simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]
        exact and_comm
      rw [hs]
      exact lintegral_deriv_Ioo hm h0 (Nat.cast_nonneg n) (hac n (Nat.cast_nonneg n))
    exact (hc.lintegral_eq_of_tendsto φInfinity
      (ENNReal.measurable_ofReal.comp (measurable_deriv φ)).aemeasurable
      (by simpa only [Function.comp_def, he] using hlim.comp tendsto_natCast_atTop_atTop)).symm
  · rw [extendedNonnegative, if_neg ha]
    rw [lintegral_indicator (measurableSet_lt ENNReal.measurable_ofReal measurable_const),
      Measure.restrict_restrict (measurableSet_lt ENNReal.measurable_ofReal measurable_const)]
    have hs : {t : ℝ | ENNReal.ofReal t < a} ∩ Ioi 0 = Ioo 0 a.toReal := by
      ext t
      constructor
      · rintro ⟨hat, ht⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) ha).mp hat⟩
      · rintro ⟨ht, hat⟩
        exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal ht.le ha).mpr hat, ht⟩
    rw [hs]
    exact (lintegral_deriv_Ioo hm h0 ENNReal.toReal_nonneg
      (hac _ ENNReal.toReal_nonneg)).symm

/-- 8.16, in the real-coordinate representation of the finite part of φ. -/
theorem layerCake_locallyAbsolutelyContinuous {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    {φ : ℝ → ℝ} {φInfinity : ℝ≥0∞}
    (hm : Monotone φ) (h0 : φ 0 = 0)
    (hac : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval φ 0 T)
    (hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (φ t)) atTop (𝓝 φInfinity)) :
    (∫⁻ x, extendedNonnegative φ φInfinity (f x) ∂μ) =
      ∫⁻ t in Ioi 0, μ {x | ENNReal.ofReal t < f x} * ENNReal.ofReal (deriv φ t) := by
  simp_rw [extendedNonnegative_eq_integral hm h0 hac hlim]
  exact layerCake_ennreal_weight μ hf (ENNReal.measurable_ofReal.comp (measurable_deriv φ))

/-- 8.16: full extended-valued formulation. Local absolute continuity is expressed
in real coordinates on each finite interval. Its finite-value condition records that
absolutely continuous functions there are real valued, as in the printed definition. -/
theorem theorem_8_16 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    {Φ : ℝ≥0∞ → ℝ≥0∞} (hm : Monotone Φ) (h0 : Φ 0 = 0)
    (hfinite : ∀ t : ℝ, Φ (ENNReal.ofReal t) ≠ ∞)
    (hac : ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval
      (fun t => (Φ (ENNReal.ofReal t)).toReal) 0 T)
    (hlim : Tendsto (fun t : ℝ => Φ (ENNReal.ofReal t)) atTop (𝓝 (Φ ∞))) :
    (∫⁻ x, Φ (f x) ∂μ) =
      ∫⁻ t in Ioi 0, μ {x | ENNReal.ofReal t < f x} *
        ENNReal.ofReal (deriv (fun t => (Φ (ENNReal.ofReal t)).toReal) t) := by
  let φ : ℝ → ℝ := fun t => (Φ (ENNReal.ofReal t)).toReal
  have hm' : Monotone φ := fun s t hst =>
    ENNReal.toReal_mono (hfinite t) (hm (ENNReal.ofReal_le_ofReal hst))
  have h0' : φ 0 = 0 := by simp [φ, h0]
  have hlim' : Tendsto (fun t : ℝ => ENNReal.ofReal (φ t)) atTop (𝓝 (Φ ∞)) := by
    simpa only [φ, ENNReal.ofReal_toReal (hfinite _)] using hlim
  have he (a : ℝ≥0∞) : extendedNonnegative φ (Φ ∞) a = Φ a := by
    by_cases ha : a = ∞
    · simp [extendedNonnegative, ha]
    · have hfa : Φ a ≠ ∞ := by
        simpa only [ENNReal.ofReal_toReal ha] using hfinite a.toReal
      simp [extendedNonnegative, ha, φ, ENNReal.ofReal_toReal ha,
        ENNReal.ofReal_toReal hfa]
  simpa only [he] using layerCake_locallyAbsolutelyContinuous μ hf hm' h0' hac hlim'

end RudinRCA.Chapter08
