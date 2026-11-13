module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

public section

open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

theorem maximalFunction_measurable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℂ}
    (hf : AEStronglyMeasurable f μ) : Measurable (maximalFunction μ f) := by
  let g : E → ℝ≥0∞ := fun x => ‖hf.mk f x‖ₑ
  have hg : Measurable g := hf.measurable_mk.enorm
  have hfg : (fun x => ‖f x‖ₑ) =ᵐ[μ] g := by
    filter_upwards [hf.ae_eq_mk] with x hx
    exact congrArg (fun z : ℂ => ‖z‖ₑ) hx
  have he : maximalFunction μ f = centeredMaximal μ g := centeredMaximal_congr_ae μ hfg
  rw [he]
  exact centeredMaximal_measurable μ hg

/-- The weak-L1 assertion recalled in 8.17, expressed as uniform boundedness
of level times distribution measure. -/
theorem theorem_8_17_weak_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℂ} (hf : Integrable f μ) :
    Measurable (maximalFunction μ f) ∧ ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {x | ENNReal.ofReal t < maximalFunction μ f x} ≤ C := by
  refine ⟨maximalFunction_measurable μ hf.aestronglyMeasurable,
    ENNReal.ofReal (5 ^ Module.finrank ℝ E) * ∫⁻ x, ‖f x‖ₑ ∂μ, ?_, ?_⟩
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hasFiniteIntegral_iff_enorm.mp hf.hasFiniteIntegral)
  · intro t ht
    exact centeredMaximal_weak_one μ (fun x => ‖f x‖ₑ) (ENNReal.ofReal t)

/-- The L-infinity contraction printed in 8.17, for the actual real-valued maximal function. -/
theorem theorem_8_17_infty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℂ} (hf : MemLp f ∞ μ) :
    (∀ x, maximalFunction μ f x < ∞) ∧
      MemLp (fun x => (maximalFunction μ f x).toReal) ∞ μ ∧
      eLpNorm (fun x => (maximalFunction μ f x).toReal) ∞ μ ≤ eLpNorm f ∞ μ := by
  have hm := maximalFunction_measurable μ hf.aestronglyMeasurable
  have hfinite (x : E) : maximalFunction μ f x < ∞ := by
    apply lt_of_le_of_lt (maximalFunction_le_essSup μ f x)
    simpa only [eLpNorm_exponent_top hf.aestronglyMeasurable] using hf.eLpNorm_lt_top
  have hn : eLpNorm (fun x => (maximalFunction μ f x).toReal) ∞ μ ≤ eLpNorm f ∞ μ := by
    rw [eLpNorm_exponent_top hm.ennreal_toReal.aestronglyMeasurable,
      eLpNorm_exponent_top hf.aestronglyMeasurable]
    apply eLpNormEssSup_le_of_ae_enorm_bound
    apply Eventually.of_forall
    intro x
    rw [Real.enorm_toReal (hfinite x).ne]
    exact maximalFunction_le_essSup μ f x
  exact ⟨hfinite, hn.trans_lt hf.eLpNorm_lt_top, hn⟩

theorem maximalFunction_strong_bound_parameter {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {f : E → ℂ} (hf : AEStronglyMeasurable f μ) {p d : ℝ} (hp : 1 < p) (hd : 1 < d) :
    (∫⁻ x, maximalFunction μ f x ^ p ∂μ) ≤
      ENNReal.ofReal p * (ENNReal.ofReal (1 / (1 - 1 / d)) *
        ENNReal.ofReal (5 ^ Module.finrank ℝ E)) *
      (ENNReal.ofReal d ^ (p - 1) / ENNReal.ofReal (p - 1)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  let g : E → ℝ≥0∞ := fun x => ‖hf.mk f x‖ₑ
  have hg : Measurable g := hf.measurable_mk.enorm
  have hfg : (fun x => ‖f x‖ₑ) =ᵐ[μ] g := by
    filter_upwards [hf.ae_eq_mk] with x hx
    exact congrArg (fun z : ℂ => ‖z‖ₑ) hx
  have he : maximalFunction μ f = centeredMaximal μ g := centeredMaximal_congr_ae μ hfg
  have hpow : (fun x => ‖f x‖ₑ ^ p) =ᵐ[μ] (fun x => g x ^ p) := by
    filter_upwards [hfg] with x hx
    rw [hx]
  rw [he, lintegral_congr_ae hpow]
  exact centeredMaximal_strong_bound_parameter μ hg hp hd

/-- Conversion of an integral-power estimate to the corresponding Lp seminorm estimate. -/
theorem maximalFunction_eLpNorm_le_of_integral_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {f : E → ℂ} {p : ℝ} (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) μ)
    {B : ℝ≥0∞} (hbound : (∫⁻ x, maximalFunction μ f x ^ p ∂μ) ≤
      B * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) :
    eLpNorm (fun x => (maximalFunction μ f x).toReal) (ENNReal.ofReal p) μ ≤
      B ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hm := maximalFunction_measurable μ hf.aestronglyMeasurable
  have hae := (theorem_8_18 μ hp hf).1
  have he : (∫⁻ x, ‖(maximalFunction μ f x).toReal‖ₑ ^ p ∂μ) =
      ∫⁻ x, maximalFunction μ f x ^ p ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hae] with x hx
    rw [Real.enorm_toReal hx.ne]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
      ENNReal.ofReal_ne_top hm.ennreal_toReal.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
      ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le, he]
  calc
    _ ≤ (B * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1 / p) :=
      ENNReal.rpow_le_rpow hbound (by positivity)
    _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by positivity)

/-- The quantitative conclusion accompanying Rudin 8.18, with the displayed
constant `(A * exp 1 * p * q)^(1/p)` and `A = 5^dim`. -/
theorem theorem_8_18_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℂ}
    {p : ℝ} (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    eLpNorm (fun x => (maximalFunction μ f x).toReal) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (maximalLpConstant (5 ^ Module.finrank ℝ E) p) *
        eLpNorm f (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpd : 0 < p - 1 := sub_pos.mpr hp
  let q : ℝ := p / (p - 1)
  let A : ℝ := 5 ^ Module.finrank ℝ E
  have hA : 0 ≤ A := by positivity
  have hq : 1 < q := by
    change 1 < p / (p - 1)
    rw [one_lt_div hpd]
    linarith
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hc : 0 < 1 - 1 / q := by rw [sub_pos, div_lt_one hq0]; exact hq
  have hb : 0 ≤ 1 / (1 - 1 / q) := by positivity
  have hecoeff :
      ENNReal.ofReal p * (ENNReal.ofReal (1 / (1 - 1 / q)) * ENNReal.ofReal A) *
        (ENNReal.ofReal q ^ (p - 1) / ENNReal.ofReal (p - 1)) =
      ENNReal.ofReal (p * (1 / (1 - 1 / q)) * A * (q ^ (p - 1) / (p - 1))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hq0.le hpd.le,
      ← ENNReal.ofReal_div_of_pos hpd,
      ← ENNReal.ofReal_mul hb,
      ← ENNReal.ofReal_mul hp0.le,
      ← ENNReal.ofReal_mul (mul_nonneg hp0.le (mul_nonneg hb hA))]
    congr 1
    ring
  have hcoeff :
      ENNReal.ofReal p * (ENNReal.ofReal (1 / (1 - 1 / q)) * ENNReal.ofReal A) *
        (ENNReal.ofReal q ^ (p - 1) / ENNReal.ofReal (p - 1)) ≤
      ENNReal.ofReal (A * Real.exp 1 * p * q) := by
    rw [hecoeff]
    exact ENNReal.ofReal_le_ofReal (maximalLpParameterizedCoefficient_le hA hp)
  have hbound : (∫⁻ x, maximalFunction μ f x ^ p ∂μ) ≤
      ENNReal.ofReal (A * Real.exp 1 * p * q) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ :=
    (maximalFunction_strong_bound_parameter μ hf.aestronglyMeasurable hp hq).trans
      (mul_le_mul_left hcoeff _)
  have hnorm := maximalFunction_eLpNorm_le_of_integral_bound μ hp hf hbound
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)] at hnorm
  exact hnorm

/-- The printed Euclidean-space specialization, including finiteness and the norm bound. -/
theorem theorem_8_18_euclidean (k : ℕ) {f : EuclideanSpace ℝ (Fin k) → ℂ}
    {p : ℝ} (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) volume) :
    (∀ᵐ x, maximalFunction volume f x < ∞) ∧
      MemLp (fun x => (maximalFunction volume f x).toReal) (ENNReal.ofReal p) volume ∧
      eLpNorm (fun x => (maximalFunction volume f x).toReal) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (maximalLpConstant (5 ^ k) p) * eLpNorm f (ENNReal.ofReal p) volume := by
  refine ⟨(theorem_8_18 volume hp hf).1, (theorem_8_18 volume hp hf).2, ?_⟩
  simpa only [finrank_euclideanSpace_fin] using theorem_8_18_norm_bound volume hp hf

end RudinRCA.Chapter08
