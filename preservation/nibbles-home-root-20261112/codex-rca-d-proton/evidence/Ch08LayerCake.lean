module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

lemma volume_positive_lt_ennreal (a : ℝ≥0∞) :
    volume {t : ℝ | 0 < t ∧ ENNReal.ofReal t < a} = a := by
  by_cases ha : a = ∞
  · simp only [ha, ENNReal.ofReal_lt_top, and_true]
    change volume (Ioi (0 : ℝ)) = ∞
    exact Real.volume_Ioi
  · have hs : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < a} = Ioo 0 a.toReal := by
      ext t
      constructor
      · rintro ⟨ht, hat⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht.le ha).mp hat⟩
      · rintro ⟨ht, hat⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht.le ha).mpr hat⟩
    rw [hs, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal ha]

/-- Cavalieri's formula for a genuinely extended-valued function. -/
theorem layerCake_ennreal {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μ = ∫⁻ t in Ioi 0, μ {x | ENNReal.ofReal t < f x} := by
  let F : X × ℝ → ℝ≥0∞ := fun p =>
    {q : X × ℝ | ENNReal.ofReal q.2 < f q.1}.indicator (fun _ => 1) p
  have hset : MeasurableSet {q : X × ℝ | ENNReal.ofReal q.2 < f q.1} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hf.comp measurable_fst)
  have hF : Measurable F := measurable_const.indicator hset
  have hx (x : X) : ∫⁻ t in Ioi 0, F (x, t) = f x := by
    rw [show (fun t => F (x, t)) = {t : ℝ | ENNReal.ofReal t < f x}.indicator (fun _ => 1) by rfl]
    rw [lintegral_indicator (measurableSet_lt ENNReal.measurable_ofReal measurable_const)]
    simp only [lintegral_const, one_mul, Measure.restrict_apply_univ]
    rw [Measure.restrict_apply (measurableSet_lt ENNReal.measurable_ofReal measurable_const)]
    have hs : {t : ℝ | ENNReal.ofReal t < f x} ∩ Ioi 0 =
        {t : ℝ | 0 < t ∧ ENNReal.ofReal t < f x} := by
      ext t
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi]
      exact and_comm
    rw [hs]
    exact volume_positive_lt_ennreal (f x)
  calc
    (∫⁻ x, f x ∂μ) = ∫⁻ x, ∫⁻ t in Ioi 0, F (x, t) ∂volume ∂μ :=
      lintegral_congr fun x => (hx x).symm
    _ = ∫⁻ t in Ioi 0, ∫⁻ x, F (x, t) ∂μ :=
      lintegral_lintegral_swap hF.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro t
      change (∫⁻ x, {x | ENNReal.ofReal t < f x}.indicator (fun _ => 1) x ∂μ) = _
      rw [lintegral_indicator (measurableSet_lt measurable_const hf)]
      simp

end RudinRCA.Chapter08
