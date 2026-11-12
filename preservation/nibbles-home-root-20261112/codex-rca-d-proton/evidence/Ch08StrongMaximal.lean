module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

public section

open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

/-- Tonelli evaluation of the truncated tails used in the maximal interpolation proof.
This fragment follows the power-layer-cake and weak-maximal fragments in a combined file. -/
theorem weighted_truncation_tails {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p - 2)) *
      ∫⁻ x in {x | ENNReal.ofReal (t / 2) < f x}, f x ∂μ) =
      ((2 : ℝ≥0∞) ^ (p - 1) / ENNReal.ofReal (p - 1)) * ∫⁻ x, f x ^ p ∂μ := by
  classical
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (p - 2))
  have hw : Measurable w :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow measurable_const)
  let F : X × ℝ → ℝ≥0∞ :=
    {z : X × ℝ | ENNReal.ofReal (z.2 / 2) < f z.1}.indicator
      (fun z => f z.1 * w z.2)
  have hs : MeasurableSet {z : X × ℝ | ENNReal.ofReal (z.2 / 2) < f z.1} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp (measurable_snd.div_const 2))
      (hf.comp measurable_fst)
  have hF : Measurable F := ((hf.comp measurable_fst).mul (hw.comp measurable_snd)).indicator hs
  have hinner (t : ℝ) : (∫⁻ x, F (x, t) ∂μ) =
      w t * ∫⁻ x in {x | ENNReal.ofReal (t / 2) < f x}, f x ∂μ := by
    change (∫⁻ x, {x | ENNReal.ofReal (t / 2) < f x}.indicator (fun x => f x * w t) x ∂μ) = _
    rw [lintegral_indicator (measurableSet_lt measurable_const hf), lintegral_mul_const _ hf]
    exact mul_comm _ _
  have hcut (a : ℝ≥0∞) : {t : ℝ | ENNReal.ofReal (t / 2) < a} =
      {t : ℝ | ENNReal.ofReal t < 2 * a} := by
    ext t
    rw [mem_setOf_eq, mem_setOf_eq, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num only [ENNReal.ofReal_ofNat]
    rw [ENNReal.div_lt_iff (by norm_num) (by norm_num), mul_comm a]
  have hxinner (x : X) : (∫⁻ t in Ioi 0, F (x, t)) =
      ((2 : ℝ≥0∞) ^ (p - 1) / ENNReal.ofReal (p - 1)) * f x ^ p := by
    have he : (fun t => F (x, t)) =
        (fun t => f x * {t : ℝ | ENNReal.ofReal (t / 2) < f x}.indicator w t) := by
      funext t
      by_cases ht : ENNReal.ofReal (t / 2) < f x <;> simp [F, ht]
    have hmeas : Measurable ({t : ℝ | ENNReal.ofReal (t / 2) < f x}.indicator w) :=
      hw.indicator (measurableSet_lt
        (ENNReal.measurable_ofReal.comp (measurable_id.div_const 2)) measurable_const)
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
      f x * (2 ^ (p - 1) * f x ^ (p - 1) / ENNReal.ofReal (p - 1)) =
          (2 ^ (p - 1) / ENNReal.ofReal (p - 1)) * (f x * f x ^ (p - 1)) := by
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

/-- Strong integral estimate with an explicit, nonoptimal dimension-dependent constant.
Rudin optimizes the truncation parameter; fixing it at one half suffices for membership. -/
theorem centeredMaximal_strong_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℝ≥0∞} (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, centeredMaximal μ f x ^ p ∂μ) ≤
      ENNReal.ofReal p * (2 * ENNReal.ofReal (5 ^ Module.finrank ℝ E)) *
      ((2 : ℝ≥0∞) ^ (p - 1) / ENNReal.ofReal (p - 1)) * ∫⁻ x, f x ^ p ∂μ := by
  let C : ℝ≥0∞ := ENNReal.ofReal (5 ^ Module.finrank ℝ E)
  have htbound (t : ℝ) (ht : 0 < t) :
      μ {x | ENNReal.ofReal t < centeredMaximal μ f x} * ENNReal.ofReal (t ^ (p - 1)) ≤
        (2 * C) * (ENNReal.ofReal (t ^ (p - 2)) *
          ∫⁻ x in {x | ENNReal.ofReal (t / 2) < f x}, f x ∂μ) := by
    have h := mul_le_mul_right (centeredMaximal_truncation_tail μ hf ht)
      (2 * ENNReal.ofReal (t ^ (p - 2)))
    have hcoeff : (2 : ℝ≥0∞) * ENNReal.ofReal (t ^ (p - 2)) * ENNReal.ofReal (t / 2) =
        ENNReal.ofReal (t ^ (p - 1)) := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * t ^ (p - 2))]
      congr 1
      calc
        2 * t ^ (p - 2) * (t / 2) = t ^ (p - 2) * t ^ (1 : ℝ) := by rw [Real.rpow_one]; ring
        _ = t ^ (p - 2 + 1) := (Real.rpow_add ht _ _).symm
        _ = _ := by congr 1; ring
    calc
      _ = (2 * ENNReal.ofReal (t ^ (p - 2))) *
          (ENNReal.ofReal (t / 2) * μ {x | ENNReal.ofReal t < centeredMaximal μ f x}) := by
            rw [← mul_assoc, hcoeff, mul_comm]
      _ ≤ _ := by simpa only [C, mul_assoc, mul_left_comm, mul_comm] using h
  rw [layerCake_rpow_ennreal μ (centeredMaximal_measurable μ hf) (by linarith : 0 < p)]
  calc
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi 0, (2 * C) * (ENNReal.ofReal (t ^ (p - 2)) *
        ∫⁻ x in {x | ENNReal.ofReal (t / 2) < f x}, f x ∂μ) := by
      apply mul_le_mul_right
      apply setLIntegral_mono' measurableSet_Ioi
      exact fun t ht => htbound t ht
    _ = _ := by
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top), weighted_truncation_tails μ hf hp]
      simp only [C, mul_assoc]

/-- The maximal operator depends only on the almost-everywhere class of its input. -/
theorem centeredMaximal_congr_ae {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℝ≥0∞} (hfg : f =ᵐ[μ] g) :
    centeredMaximal μ f = centeredMaximal μ g := by
  funext x
  unfold centeredMaximal
  congr 1
  funext r
  congr 1
  funext hr
  rw [lintegral_congr_ae (ae_restrict_of_ae hfg)]

/-- Finiteness of the strong integral implies an almost-everywhere finite maximal function
and actual real-valued Lp membership. The separate finiteness clause prevents `toReal` from
concealing infinite maximal values. -/
theorem centeredMaximal_memLp_of_lintegral_rpow_lt_top {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {f : E → ℝ≥0∞} (hf : Measurable f) {p : ℝ} (hp : 1 < p)
    (hfi : (∫⁻ x, f x ^ p ∂μ) < ∞) :
    (∀ᵐ x ∂μ, centeredMaximal μ f x < ∞) ∧
      MemLp (fun x => (centeredMaximal μ f x).toReal) (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hMi : (∫⁻ x, centeredMaximal μ f x ^ p ∂μ) < ∞ := by
    apply lt_of_le_of_lt (centeredMaximal_strong_bound μ hf hp)
    apply ENNReal.mul_lt_top
    · apply ENNReal.mul_lt_top
      · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
      · apply ENNReal.div_lt_top
        · exact (ENNReal.rpow_lt_top_of_nonneg (by linarith) (by norm_num)).ne
        · exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    · exact hfi
  have hm := centeredMaximal_measurable μ hf
  have hae : ∀ᵐ x ∂μ, centeredMaximal μ f x < ∞ := by
    filter_upwards [ae_lt_top (hm.pow_const p) hMi.ne] with x hx
    exact (ENNReal.rpow_lt_top_iff_of_pos hp0).mp hx
  refine ⟨hae, ?_⟩
  change eLpNorm (fun x => (centeredMaximal μ f x).toReal) (ENNReal.ofReal p) μ < ∞
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
    hm.ennreal_toReal.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
  have he : (∫⁻ x, ‖(centeredMaximal μ f x).toReal‖ₑ ^ p ∂μ) =
      ∫⁻ x, centeredMaximal μ f x ^ p ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hae] with x hx
    rw [Real.enorm_toReal hx.ne]
  rwa [he]

/-- Rudin 8.18 for complex-valued functions on any finite-dimensional real normed
space with Haar measure, hence in particular Euclidean R^k with Lebesgue measure. -/
theorem theorem_8_18 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℂ}
    {p : ℝ} (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    (∀ᵐ x ∂μ, maximalFunction μ f x < ∞) ∧
      MemLp (fun x => (maximalFunction μ f x).toReal) (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  let g : E → ℝ≥0∞ := fun x => ‖hf.aestronglyMeasurable.mk f x‖ₑ
  have hg : Measurable g := hf.aestronglyMeasurable.measurable_mk.enorm
  have hfg : (fun x => ‖f x‖ₑ) =ᵐ[μ] g := by
    filter_upwards [hf.aestronglyMeasurable.ae_eq_mk] with x hx
    exact congrArg (fun z : ℂ => ‖z‖ₑ) hx
  have hgi : (∫⁻ x, g x ^ p ∂μ) < ∞ := by
    have hfi := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top hf.eLpNorm_lt_top
    rw [ENNReal.toReal_ofReal hp0.le] at hfi
    have hpow : (fun x => ‖f x‖ₑ ^ p) =ᵐ[μ] (fun x => g x ^ p) := by
      filter_upwards [hfg] with x hx
      rw [hx]
    rw [← lintegral_congr_ae hpow]
    exact hfi
  have he : maximalFunction μ f = centeredMaximal μ g :=
    centeredMaximal_congr_ae μ hfg
  rw [he]
  exact centeredMaximal_memLp_of_lintegral_rpow_lt_top μ hg hp hgi

end RudinRCA.Chapter08
