module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

public section

open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

theorem weighted_truncation_tails_parameter {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) (d : ℝ) (hd : 0 < d) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p - 2)) *
      ∫⁻ x in {x | ENNReal.ofReal (t / d) < f x}, f x ∂μ) =
      ((ENNReal.ofReal d : ℝ≥0∞) ^ (p - 1) / ENNReal.ofReal (p - 1)) * ∫⁻ x, f x ^ p ∂μ := by
  classical
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (p - 2))
  have hw : Measurable w :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow measurable_const)
  let F : X × ℝ → ℝ≥0∞ :=
    {z : X × ℝ | ENNReal.ofReal (z.2 / d) < f z.1}.indicator
      (fun z => f z.1 * w z.2)
  have hs : MeasurableSet {z : X × ℝ | ENNReal.ofReal (z.2 / d) < f z.1} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp (measurable_snd.div_const d))
      (hf.comp measurable_fst)
  have hF : Measurable F := ((hf.comp measurable_fst).mul (hw.comp measurable_snd)).indicator hs
  have hinner (t : ℝ) : (∫⁻ x, F (x, t) ∂μ) =
      w t * ∫⁻ x in {x | ENNReal.ofReal (t / d) < f x}, f x ∂μ := by
    change (∫⁻ x, {x | ENNReal.ofReal (t / d) < f x}.indicator (fun x => f x * w t) x ∂μ) = _
    rw [lintegral_indicator (measurableSet_lt measurable_const hf), lintegral_mul_const _ hf]
    exact mul_comm _ _
  have hcut (a : ℝ≥0∞) : {t : ℝ | ENNReal.ofReal (t / d) < a} =
      {t : ℝ | ENNReal.ofReal t < ENNReal.ofReal d * a} := by
    ext t
    rw [mem_setOf_eq, mem_setOf_eq, ENNReal.ofReal_div_of_pos hd]
    rw [ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_pos.mpr hd).ne') (Or.inl ENNReal.ofReal_ne_top), mul_comm a]
  have hxinner (x : X) : (∫⁻ t in Ioi 0, F (x, t)) =
      ((ENNReal.ofReal d : ℝ≥0∞) ^ (p - 1) / ENNReal.ofReal (p - 1)) * f x ^ p := by
    have he : (fun t => F (x, t)) =
        (fun t => f x * {t : ℝ | ENNReal.ofReal (t / d) < f x}.indicator w t) := by
      funext t
      by_cases ht : ENNReal.ofReal (t / d) < f x <;> simp [F, ht]
    have hmeas : Measurable ({t : ℝ | ENNReal.ofReal (t / d) < f x}.indicator w) :=
      hw.indicator (measurableSet_lt
        (ENNReal.measurable_ofReal.comp (measurable_id.div_const d)) measurable_const)
    rw [he, lintegral_const_mul _ hmeas, hcut]
    have hwexp : w = (fun t : ℝ => ENNReal.ofReal (t ^ ((p - 1) - 1))) := by
      funext t
      change ENNReal.ofReal (t ^ (p - 2)) = ENNReal.ofReal (t ^ ((p - 1) - 1))
      rw [show p - 2 = (p - 1) - 1 by ring]
    rw [hwexp, lintegral_rpow_below_ennreal _ (by linarith : 0 < p - 1),
      ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ p - 1)]
    have hpow : f x * f x ^ (p - 1) = f x ^ p := by
      calc
        f x * f x ^ (p - 1) = f x ^ (1 : ℝ) * f x ^ (p - 1) := by rw [ENNReal.rpow_one]
        _ = f x ^ (1 + (p - 1)) :=
          (ENNReal.rpow_add_of_nonneg 1 (p - 1) (by norm_num) (by linarith)).symm
        _ = f x ^ p := by congr 1; ring
    calc
      f x * (ENNReal.ofReal d ^ (p - 1) * f x ^ (p - 1) / ENNReal.ofReal (p - 1)) =
          (ENNReal.ofReal d ^ (p - 1) / ENNReal.ofReal (p - 1)) * (f x * f x ^ (p - 1)) := by
            simp only [div_eq_mul_inv]
            ac_rfl
      _ = _ := by rw [hpow]
  calc
    _ = ∫⁻ t in Ioi 0, ∫⁻ x, F (x, t) ∂μ := by simp only [hinner, w]
    _ = ∫⁻ x, ∫⁻ t in Ioi 0, F (x, t) ∂volume ∂μ :=
      (lintegral_lintegral_swap (μ := μ) (ν := volume.restrict (Ioi 0))
        (f := fun x t => F (x, t)) hF.aemeasurable).symm
    _ = _ := by
      simp_rw [hxinner]
      exact lintegral_const_mul _ (hf.pow_const p)


/-- Truncation at an arbitrary fraction `1 / d` of the level. -/
theorem centeredMaximal_truncation_tail_parameter {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {f : E → ℝ≥0∞} (hf : Measurable f) {t d : ℝ} (ht : 0 < t) (hd : 1 < d) :
    ENNReal.ofReal ((1 - 1 / d) * t) * μ {x | ENNReal.ofReal t < centeredMaximal μ f x} ≤
      ENNReal.ofReal (5 ^ Module.finrank ℝ E) *
        ∫⁻ x in {x | ENNReal.ofReal (t / d) < f x}, f x ∂μ := by
  have hd0 : 0 < d := lt_trans zero_lt_one hd
  have hc : 0 < 1 - 1 / d := by rw [sub_pos, div_lt_one hd0]; exact hd
  let q := ENNReal.ofReal (t / d)
  let a := ENNReal.ofReal ((1 - 1 / d) * t)
  let g := {x | q < f x}.indicator f
  have hsum : a + q = ENNReal.ofReal t := by
    change ENNReal.ofReal ((1 - 1 / d) * t) + ENNReal.ofReal (t / d) = ENNReal.ofReal t
    rw [← ENNReal.ofReal_add (mul_nonneg hc.le ht.le) (div_nonneg ht.le hd0.le)]
    congr 1
    ring
  have hfg (x : E) : f x ≤ g x + q := by
    by_cases hx : q < f x
    · simp only [g, mem_setOf_eq, hx, indicator_of_mem]
      exact le_add_right le_rfl
    · simp only [g, mem_setOf_eq, hx, not_false_eq_true, indicator_of_notMem, zero_add]
      exact le_of_not_gt hx
  have hM (x : E) : centeredMaximal μ f x ≤ centeredMaximal μ g x + q :=
    centeredMaximal_le_add_const μ hfg
      (fun x r hr => ⟨(measure_ball_pos μ x hr).ne', measure_ball_ne_top⟩) x
  have hs : {x | ENNReal.ofReal t < centeredMaximal μ f x} ⊆
      {x | a < centeredMaximal μ g x} := by
    intro x hx
    by_contra hnot
    have hle := (hM x).trans (add_le_add (le_of_not_gt hnot) le_rfl)
    rw [hsum] at hle
    exact (not_le_of_gt hx) hle
  calc
    a * μ {x | ENNReal.ofReal t < centeredMaximal μ f x} ≤
        a * μ {x | a < centeredMaximal μ g x} := mul_le_mul_right (measure_mono hs) a
    _ ≤ ENNReal.ofReal (5 ^ Module.finrank ℝ E) * ∫⁻ x, g x ∂μ :=
      centeredMaximal_weak_one μ g a
    _ = _ := by rw [lintegral_indicator (measurableSet_lt measurable_const hf)]

/-- The strong estimate before choosing the truncation parameter. -/
theorem centeredMaximal_strong_bound_parameter {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {f : E → ℝ≥0∞} (hf : Measurable f) {p d : ℝ} (hp : 1 < p) (hd : 1 < d) :
    (∫⁻ x, centeredMaximal μ f x ^ p ∂μ) ≤
      ENNReal.ofReal p * (ENNReal.ofReal (1 / (1 - 1 / d)) *
        ENNReal.ofReal (5 ^ Module.finrank ℝ E)) *
      (ENNReal.ofReal d ^ (p - 1) / ENNReal.ofReal (p - 1)) * ∫⁻ x, f x ^ p ∂μ := by
  have hd0 : 0 < d := lt_trans zero_lt_one hd
  have hc : 0 < 1 - 1 / d := by rw [sub_pos, div_lt_one hd0]; exact hd
  let C : ℝ≥0∞ := ENNReal.ofReal (5 ^ Module.finrank ℝ E)
  let b : ℝ≥0∞ := ENNReal.ofReal (1 / (1 - 1 / d))
  have htbound (t : ℝ) (ht : 0 < t) :
      μ {x | ENNReal.ofReal t < centeredMaximal μ f x} * ENNReal.ofReal (t ^ (p - 1)) ≤
        (b * C) * (ENNReal.ofReal (t ^ (p - 2)) *
          ∫⁻ x in {x | ENNReal.ofReal (t / d) < f x}, f x ∂μ) := by
    have h := mul_le_mul_right (centeredMaximal_truncation_tail_parameter μ hf ht hd)
      (b * ENNReal.ofReal (t ^ (p - 2)))
    have hcoeff : b * ENNReal.ofReal (t ^ (p - 2)) * ENNReal.ofReal ((1 - 1 / d) * t) =
        ENNReal.ofReal (t ^ (p - 1)) := by
      change ENNReal.ofReal (1 / (1 - 1 / d)) * ENNReal.ofReal (t ^ (p - 2)) *
        ENNReal.ofReal ((1 - 1 / d) * t) = _
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (1 - 1 / d)),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (1 - 1 / d) * t ^ (p - 2))]
      congr 1
      calc
        1 / (1 - 1 / d) * t ^ (p - 2) * ((1 - 1 / d) * t) =
            t ^ (p - 2) * t ^ (1 : ℝ) := by
              rw [Real.rpow_one]
              calc
                _ = (1 / (1 - 1 / d) * (1 - 1 / d)) * (t ^ (p - 2) * t) := by ring
                _ = _ := by rw [div_mul_cancel₀ 1 hc.ne', one_mul]
        _ = t ^ (p - 2 + 1) := (Real.rpow_add ht _ _).symm
        _ = _ := by congr 1; ring
    calc
      _ = (b * ENNReal.ofReal (t ^ (p - 2))) *
          (ENNReal.ofReal ((1 - 1 / d) * t) *
            μ {x | ENNReal.ofReal t < centeredMaximal μ f x}) := by
              rw [← mul_assoc, hcoeff, mul_comm]
      _ ≤ _ := by simpa only [C, mul_assoc, mul_left_comm, mul_comm] using h
  rw [layerCake_rpow_ennreal μ (centeredMaximal_measurable μ hf) (by linarith : 0 < p)]
  calc
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi 0, (b * C) * (ENNReal.ofReal (t ^ (p - 2)) *
        ∫⁻ x in {x | ENNReal.ofReal (t / d) < f x}, f x ∂μ) := by
      apply mul_le_mul_right
      apply setLIntegral_mono' measurableSet_Ioi
      exact fun t ht => htbound t ht
    _ = _ := by
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
        weighted_truncation_tails_parameter μ hf hp d hd0]
      simp only [C, b, mul_assoc]

end RudinRCA.Chapter08
