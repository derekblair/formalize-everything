module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

lemma lintegral_rpow_Ioo {p T : ℝ} (hp : 0 < p) (hT : 0 ≤ T) :
    (∫⁻ t in Ioo 0 T, ENNReal.ofReal (t ^ (p - 1))) =
      ENNReal.ofReal (T ^ p / p) := by
  have hi : IntervalIntegrable (fun t : ℝ => t ^ (p - 1)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hn : 0 ≤ᵐ[volume.restrict (Ioc 0 T)] (fun t : ℝ => t ^ (p - 1)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Ioc : Ioo 0 T =ᵐ[volume] Ioc 0 T),
    ← ofReal_integral_eq_lintegral_ofReal hi.1 hn,
    ← intervalIntegral.integral_of_le hT, integral_rpow (Or.inl (by linarith))]
  simp [show p - 1 + 1 = p by ring, Real.zero_rpow hp.ne']

/-- The power primitive on an extended interval, including an infinite upper endpoint. -/
theorem lintegral_rpow_below_ennreal (a : ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (∫⁻ t in Ioi 0, {t : ℝ | ENNReal.ofReal t < a}.indicator
      (fun t => ENNReal.ofReal (t ^ (p - 1))) t) = a ^ p / ENNReal.ofReal p := by
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (p - 1))) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow measurable_const)
  by_cases ha : a = ∞
  · subst a
    simp only [ENNReal.ofReal_lt_top, setOf_true, indicator_univ]
    let ν : Measure ℝ := volume.restrict (Ioi 0)
    have hc : AECover ν atTop (fun n : ℕ => Iio (n : ℝ)) :=
      aecover_Iio (μ := ν) tendsto_natCast_atTop_atTop
    have he (n : ℕ) :
        (∫⁻ t in Iio (n : ℝ), ENNReal.ofReal (t ^ (p - 1)) ∂ν) =
          (n : ℝ≥0∞) ^ p / ENNReal.ofReal p := by
      rw [show ν = volume.restrict (Ioi 0) from rfl,
        Measure.restrict_restrict measurableSet_Iio]
      have hs : Iio (n : ℝ) ∩ Ioi 0 = Ioo 0 (n : ℝ) := by
        ext t
        simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]
        exact and_comm
      rw [hs, lintegral_rpow_Ioo hp (Nat.cast_nonneg n),
        ENNReal.ofReal_div_of_pos hp,
        ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg n) hp.le]
      simp
    have hlim : Tendsto (fun n : ℕ => (n : ℝ≥0∞) ^ p / ENNReal.ofReal p) atTop
        (𝓝 ((∞ : ℝ≥0∞) ^ p / ENNReal.ofReal p)) :=
      ENNReal.Tendsto.div_const
        (((ENNReal.continuous_rpow_const (y := p)).tendsto ∞).comp
          ENNReal.tendsto_nat_nhds_top) (Or.inr (ENNReal.ofReal_pos.mpr hp).ne')
    apply hc.lintegral_eq_of_tendsto _ hm.aemeasurable
    simpa only [he] using hlim
  · rw [lintegral_indicator (measurableSet_lt ENNReal.measurable_ofReal measurable_const),
      Measure.restrict_restrict (measurableSet_lt ENNReal.measurable_ofReal measurable_const)]
    have hs : {t : ℝ | ENNReal.ofReal t < a} ∩ Ioi 0 = Ioo 0 a.toReal := by
      ext t
      constructor
      · rintro ⟨hat, ht⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht.le ha).mp hat⟩
      · rintro ⟨ht, hat⟩
        exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal ht.le ha).mpr hat, ht⟩
    rw [hs, lintegral_rpow_Ioo hp ENNReal.toReal_nonneg, ENNReal.ofReal_div_of_pos hp,
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le,
      ENNReal.ofReal_toReal ha]

-- The following theorem is a combined-file fragment: it depends on
-- layerCake_ennreal_weight from Ch08Phi.lean.
theorem layerCake_rpow_ennreal {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, f x ^ p ∂μ) = ENNReal.ofReal p *
      ∫⁻ t in Ioi 0, μ {x | ENNReal.ofReal t < f x} * ENNReal.ofReal (t ^ (p - 1)) := by
  have h := layerCake_ennreal_weight (g := fun t : ℝ => ENNReal.ofReal (t ^ (p - 1))) μ hf
    (ENNReal.measurable_ofReal.comp (measurable_id.pow measurable_const) :
      Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (p - 1))))
  simp_rw [lintegral_rpow_below_ennreal _ hp] at h
  calc
    (∫⁻ x, f x ^ p ∂μ) =
        ENNReal.ofReal p * ∫⁻ x, f x ^ p / ENNReal.ofReal p ∂μ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro x
      rw [mul_comm, ENNReal.div_mul_cancel (ENNReal.ofReal_pos.mpr hp).ne'
        ENNReal.ofReal_ne_top]
    _ = _ := congrArg (ENNReal.ofReal p * ·) h

end RudinRCA.Chapter08
