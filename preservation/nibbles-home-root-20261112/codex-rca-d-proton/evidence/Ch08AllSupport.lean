module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public section

/- Source fragment Ch08Later.lean -/



open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution

namespace RudinRCA.Chapter08

/-- Rudin's convolution convention, including the standard zero choice on the null set
where the Bochner integral is not defined. -/
noncomputable def rudinConvolution (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, f (x - y) * g y

lemma rudinConvolution_eq (f g : ℝ → ℂ) :
    rudinConvolution f g = convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext x
  exact (convolution_mul_swap (f := f) (g := g) (x := x)).symm

/-- 8.14: absolute convergence for almost every point, integrability of the convolution,
and the sharp L¹ norm estimate. The functions are arbitrary Lebesgue-a.e. measurable
representatives, not just Borel representatives. -/
theorem theorem_8_14 {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∀ᵐ x : ℝ, Integrable (fun y => f (x - y) * g y)) ∧
    Integrable (rudinConvolution f g) ∧
    (∫ x, ‖rudinConvolution f g x‖) ≤ (∫ x, ‖f x‖) * (∫ x, ‖g x‖) := by
  have hex := hf.ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ) hg
  have hi := hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hex] with x hx
    exact hx.integrable_swap
  · simpa only [rudinConvolution_eq] using hi
  · rw [rudinConvolution_eq]
    calc
      (∫ x, ‖convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume x‖) ≤
          ∫ x, convolution (fun t => ‖f t‖) (fun t => ‖g t‖)
            (ContinuousLinearMap.mul ℝ ℝ) volume x := by
        apply integral_mono hi.norm
          (hf.norm.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hg.norm)
        intro x
        simp only [convolution_mul]
        simpa only [norm_mul] using norm_integral_le_integral_norm (fun t => f t * g (x - t))
      _ = (∫ x, ‖f x‖) * (∫ x, ‖g x‖) := by
        exact integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf.norm hg.norm

/-- 8.15: Rudin's distribution function, defined at every real threshold.
Only its restriction to the nonnegative real line is used in the book. -/
noncomputable def distributionFunction {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  μ {x | ENNReal.ofReal t < f x}

/-- 8.15: the distribution function is nonincreasing. -/
theorem distributionFunction_antitone {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) : Antitone (distributionFunction μ f) := by
  intro s t hst
  exact measure_mono fun x hx => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) hx

/-- 8.15: the distribution function is Borel measurable. -/
theorem distributionFunction_measurable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) : Measurable (distributionFunction μ f) :=
  (distributionFunction_antitone μ f).measurable

-- The following finite-valued cases are support lemmas only; they do NOT complete
-- Rudin 8.15/8.16, where f may take the value ∞.
theorem layerCake_real {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} (hf : AEMeasurable f μ) (hfn : 0 ≤ᵐ[μ] f) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ∫⁻ t in Ioi 0, μ {x | t < f x} :=
  lintegral_eq_lintegral_meas_lt μ hfn hf

theorem layerCake_integratedWeight_real {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} {g : ℝ → ℝ}
    (hf : AEMeasurable f μ) (hfn : 0 ≤ᵐ[μ] f)
    (hg : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (hgn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ g t) :
    ∫⁻ x, ENNReal.ofReal (∫ t in 0..f x, g t) ∂μ =
      ∫⁻ t in Ioi 0, μ {x | t < f x} * ENNReal.ofReal (g t) :=
  lintegral_comp_eq_lintegral_meas_lt_mul μ hfn hf hg hgn


end RudinRCA.Chapter08

/- Source fragment Ch08LayerCake.lean -/



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

/- Source fragment Ch08Phi.lean -/



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

/- Source fragment Ch08Maximal.lean -/



open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

/-- The centered Hardy–Littlewood maximal function, using all positive radii.
For Euclidean space and Lebesgue measure this is Rudin's maximal function of `|f|`. -/
noncomputable def maximalFunction {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ r : ℝ, ⨆ (_ : 0 < r), (∫⁻ y in ball x r, ‖f y‖ₑ ∂μ) / μ (ball x r)

/-- 8.17's L∞ estimate in the stronger pointwise form. The weak (1,1) assertion
recalled from Chapter 7 is a separate, not yet supplied theorem. -/
theorem maximalFunction_le_essSup {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) (x : X) :
    maximalFunction μ f x ≤ eLpNormEssSup f μ := by
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  calc
    (∫⁻ y in ball x r, ‖f y‖ₑ ∂μ) / μ (ball x r) ≤
        (eLpNormEssSup f μ * μ (ball x r)) / μ (ball x r) := by
      apply ENNReal.div_le_div_right
      calc
        (∫⁻ y in ball x r, ‖f y‖ₑ ∂μ) ≤
            ∫⁻ _y in ball x r, eLpNormEssSup f μ ∂μ :=
          lintegral_mono_ae (ae_restrict_of_ae ae_le_eLpNormEssSup)
        _ = _ := by simp
    _ ≤ eLpNormEssSup f μ := by
      rw [div_eq_mul_inv, mul_assoc]
      exact (mul_le_mul_right (ENNReal.mul_inv_le_one _) _).trans_eq (mul_one _)

/-- The high part in Rudin's interpolation proof is integrable. This is support for
8.18, not the maximal-function theorem itself. -/
theorem integrable_highPart {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℂ} (hfmeas : Measurable f)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ∞) (hf : MemLp f p μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) (hεtop : ε ≠ ∞) :
    Integrable ({x | ε < ‖f x‖ₑ}.indicator f) μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hs : MeasurableSet {x | ε < ‖f x‖ₑ} :=
    measurableSet_lt measurable_const hfmeas.enorm
  have hsub : {x | ε < ‖f x‖ₑ} ⊆ {x | ε ≤ ‖f x‖ₑ} := by
    intro x hx
    change ε < ‖f x‖ₑ at hx
    change ε ≤ ‖f x‖ₑ
    exact hx.le
  have hmeasure : μ {x | ε < ‖f x‖ₑ} < ∞ :=
    (measure_mono hsub).trans_lt
      (hf.meas_ge_lt_top'_enorm hp0 hptop hε (fun h => (hεtop h).elim))
  apply memLp_one_iff_integrable.mp
  exact (hf.indicator hs).mono_exponent_of_measure_support_ne_top
    (fun x hx => Set.indicator_of_notMem hx f) hmeasure.ne hp

end RudinRCA.Chapter08

/- Source fragment Ch08WeakMaximal.lean -/



open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

/-- Covering-lemma part of the concrete maximal weak estimate. This is support only:
to apply it to an entire maximal-function level set, uniformly bound witness radii. -/
theorem weak_bound_of_bounded_ball_witnesses {X : Type*} [PseudoMetricSpace X]
    [SeparableSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) {s : Set X} {t C : ℝ≥0∞} {R : ℝ}
    (hgrowth : ∀ (x : X) (r : ℝ), 0 < r →
      μ (ball x (5 * r)) ≤ C * μ (ball x r))
    (hwitness : ∀ x ∈ s, ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      t * μ (ball x r) ≤ ∫⁻ y in ball x r, f y ∂μ) :
    t * μ s ≤ C * ∫⁻ x, f x ∂μ := by
  classical
  choose r hrpos hrbound hrint using fun x : s => hwitness x x.property
  obtain ⟨u, hu, hdis, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      (univ : Set s) (fun x : s => (x : X)) r R (fun x _ => hrbound x) 5 (by norm_num)
  have huc : u.Countable := hdis.countable_of_isOpen
    (fun _ _ => isOpen_ball) (fun x _ => nonempty_ball.mpr (hrpos x))
  letI : Countable u := huc.to_subtype
  have hscover : s ⊆ ⋃ i : u, ball ((i : s) : X) (5 * r i) := by
    intro x hx
    obtain ⟨i, hi, hinc⟩ := hcover ⟨x, hx⟩ (mem_univ _)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hinc (mem_ball_self (hrpos ⟨x, hx⟩))⟩
  have hmeasure : μ s ≤ C * ∑' i : u, μ (ball ((i : s) : X) (r i)) := by
    calc
      μ s ≤ μ (⋃ i : u, ball ((i : s) : X) (5 * r i)) := measure_mono hscover
      _ ≤ ∑' i : u, μ (ball ((i : s) : X) (5 * r i)) := measure_iUnion_le _
      _ ≤ ∑' i : u, C * μ (ball ((i : s) : X) (r i)) :=
        ENNReal.tsum_le_tsum fun i => hgrowth i (r i) (hrpos i)
      _ = _ := ENNReal.tsum_mul_left
  have hiunion : (∑' i : u, ∫⁻ x in ball ((i : s) : X) (r i), f x ∂μ) ≤
      ∫⁻ x, f x ∂μ := by
    rw [← lintegral_iUnion (fun _ => measurableSet_ball) (hdis.subtype _ _)]
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  calc
    t * μ s ≤ t * (C * ∑' i : u, μ (ball ((i : s) : X) (r i))) :=
      mul_le_mul_right hmeasure t
    _ = C * ∑' i : u, t * μ (ball ((i : s) : X) (r i)) := by
      rw [ENNReal.tsum_mul_left]
      ac_rfl
    _ ≤ C * ∑' i : u, ∫⁻ x in ball ((i : s) : X) (r i), f x ∂μ :=
      mul_le_mul_right (ENNReal.tsum_le_tsum fun i : u => hrint (i : s)) C
    _ ≤ C * ∫⁻ x, f x ∂μ := mul_le_mul_right hiunion C

/-- The Euclidean ball-growth constant required in the weak estimate. -/
theorem haar_ball_five_growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (x : E) (r : ℝ) :
    μ (ball x (5 * r)) = ENNReal.ofReal (5 ^ Module.finrank ℝ E) * μ (ball x r) := by
  rw [μ.addHaar_ball_mul_of_pos x (by norm_num : (0 : ℝ) < 5) r,
    μ.addHaar_ball_center x r]

/-- Centered maximal operator for nonnegative extended-valued functions. -/
noncomputable def centeredMaximal {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ⨆ r : ℝ, ⨆ (_ : 0 < r), (∫⁻ y in ball x r, f y ∂μ) / μ (ball x r)

/-- The weak estimate follows by exhausting bounded-radius witnesses. The measure
continuity theorem used here works for arbitrary level sets, before measurability is known. -/
theorem centeredMaximal_weak_bound {X : Type*} [PseudoMetricSpace X]
    [SeparableSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) {t C : ℝ≥0∞}
    (hballs : ∀ (x : X) (r : ℝ), 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞)
    (hgrowth : ∀ (x : X) (r : ℝ), 0 < r →
      μ (ball x (5 * r)) ≤ C * μ (ball x r)) :
    t * μ {x | t < centeredMaximal μ f x} ≤ C * ∫⁻ x, f x ∂μ := by
  let S : ℕ → Set X := fun n => {x | ∃ r : ℝ, 0 < r ∧ r ≤ (n : ℝ) ∧
    t * μ (ball x r) ≤ ∫⁻ y in ball x r, f y ∂μ}
  have hSmono : Monotone S := by
    intro m n hmn x hx
    obtain ⟨r, hrpos, hrbound, hrint⟩ := hx
    exact ⟨r, hrpos, hrbound.trans (by exact_mod_cast hmn), hrint⟩
  have hSbound (n : ℕ) : t * μ (S n) ≤ C * ∫⁻ x, f x ∂μ :=
    weak_bound_of_bounded_ball_witnesses μ f hgrowth (fun _ hx => hx)
  have hcover : {x | t < centeredMaximal μ f x} ⊆ ⋃ n : ℕ, S n := by
    intro x hx
    change t < centeredMaximal μ f x at hx
    unfold centeredMaximal at hx
    obtain ⟨r, hr⟩ := lt_iSup_iff.mp hx
    obtain ⟨hrpos, hrmean⟩ := lt_iSup_iff.mp hr
    obtain ⟨n, hn⟩ := exists_nat_ge r
    refine mem_iUnion.mpr ⟨n, r, hrpos, hn, ?_⟩
    exact ((ENNReal.lt_div_iff_mul_lt (Or.inl (hballs x r hrpos).1)
      (Or.inl (hballs x r hrpos).2)).mp hrmean).le
  calc
    t * μ {x | t < centeredMaximal μ f x} ≤ t * μ (⋃ n : ℕ, S n) :=
      mul_le_mul_right (measure_mono hcover) t
    _ = ⨆ n : ℕ, t * μ (S n) := by rw [hSmono.measure_iUnion, ENNReal.mul_iSup]
    _ ≤ C * ∫⁻ x, f x ∂μ := iSup_le hSbound

/-- Concrete weak (1,1) bound for the centered maximal operator on a finite-dimensional
real normed space, with explicit dimension-dependent constant 5^dim. -/
theorem centeredMaximal_weak_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (f : E → ℝ≥0∞) (t : ℝ≥0∞) :
    t * μ {x | t < centeredMaximal μ f x} ≤
      ENNReal.ofReal (5 ^ Module.finrank ℝ E) * ∫⁻ x, f x ∂μ := by
  apply centeredMaximal_weak_bound μ f
  · intro x r hr
    exact ⟨(measure_ball_pos μ x hr).ne', measure_ball_ne_top⟩
  · intro x r hr
    exact (haar_ball_five_growth μ x r).le

/-- All radii can be replaced by positive rational radii, because open balls are
unions of smaller rational-radius balls. -/
theorem centeredMaximal_eq_rational {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞) (x : X)
    (hballs : ∀ r : ℝ, 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞) :
    centeredMaximal μ f x =
      ⨆ q : ℚ, ⨆ (_ : 0 < (q : ℝ)),
        (∫⁻ y in ball x (q : ℝ), f y ∂μ) / μ (ball x (q : ℝ)) := by
  let S := ⨆ q : ℚ, ⨆ (_ : 0 < (q : ℝ)),
    (∫⁻ y in ball x (q : ℝ), f y ∂μ) / μ (ball x (q : ℝ))
  apply le_antisymm
  · apply iSup_le
    intro r
    apply iSup_le
    intro hr
    apply ENNReal.div_le_of_le_mul
    let Q := {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < r}
    have hu : ball x r = ⋃ q : Q, ball x ((q : ℚ) : ℝ) := by
      ext y
      constructor
      · intro hy
        change dist y x < r at hy
        obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hy
        exact mem_iUnion.mpr ⟨⟨q, lt_of_le_of_lt dist_nonneg hq₁, hq₂⟩, hq₁⟩
      · intro hy
        obtain ⟨q, hq⟩ := mem_iUnion.mp hy
        exact hq.trans q.property.2
    have hd : Directed (· ⊆ ·) (fun q : Q => ball x ((q : ℚ) : ℝ)) := by
      intro a b
      rcases le_total (a : ℚ) (b : ℚ) with hab | hba
      · exact ⟨b, ball_subset_ball (by exact_mod_cast hab), Subset.rfl⟩
      · exact ⟨a, Subset.rfl, ball_subset_ball (by exact_mod_cast hba)⟩
    have hi : (∫⁻ y in ball x r, f y ∂μ) =
        ⨆ q : Q, ∫⁻ y in ball x ((q : ℚ) : ℝ), f y ∂μ := by
      rw [hu, setLIntegral_iUnion_of_directed f hd]
    rw [hi]
    apply iSup_le
    intro q
    calc
      (∫⁻ y in ball x ((q : ℚ) : ℝ), f y ∂μ) ≤
          S * μ (ball x ((q : ℚ) : ℝ)) := by
        apply (ENNReal.div_le_iff_le_mul (Or.inl (hballs _ q.property.1).1)
          (Or.inl (hballs _ q.property.1).2)).mp
        exact le_iSup_of_le (q : ℚ) (le_iSup_of_le q.property.1 le_rfl)
      _ ≤ S * μ (ball x r) :=
        mul_le_mul_right (measure_mono (ball_subset_ball q.property.2.le)) S
  · apply iSup_le
    intro q
    apply iSup_le
    intro hq
    exact le_iSup_of_le (q : ℝ) (le_iSup_of_le hq le_rfl)

/-- Measurability of the mass of a ball with moving center. -/
theorem measurable_lintegral_ball {X : Type*} [PseudoMetricSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f) (r : ℝ) :
    Measurable (fun x => ∫⁻ y in ball x r, f y ∂μ) := by
  let F : X × X → ℝ≥0∞ :=
    {p : X × X | dist p.2 p.1 < r}.indicator (fun p => f p.2)
  have hF : Measurable F := (hf.comp measurable_snd).indicator
    (measurableSet_lt (continuous_snd.dist continuous_fst).measurable measurable_const)
  have hmeas : Measurable (fun x => ∫⁻ y, F (x, y) ∂μ) := hF.lintegral_prod_right'
  have he : (fun x => ∫⁻ y in ball x r, f y ∂μ) = (fun x => ∫⁻ y, F (x, y) ∂μ) := by
    funext x
    rw [← lintegral_indicator measurableSet_ball]
    rfl
  rw [he]
  exact hmeas

/-- The centered maximal function is measurable for a measurable nonnegative input. -/
theorem centeredMaximal_measurable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℝ≥0∞} (hf : Measurable f) :
    Measurable (centeredMaximal μ f) := by
  have he (x : E) : centeredMaximal μ f x =
      ⨆ q : ℚ, ⨆ (_ : 0 < (q : ℝ)),
        (∫⁻ y in ball x (q : ℝ), f y ∂μ) / μ (ball 0 (q : ℝ)) := by
    rw [centeredMaximal_eq_rational μ f x
      (fun r hr => ⟨(measure_ball_pos μ x hr).ne', measure_ball_ne_top⟩)]
    simp_rw [μ.addHaar_ball_center x]
  have hefun : centeredMaximal μ f = (fun x =>
      ⨆ q : ℚ, ⨆ (_ : 0 < (q : ℝ)),
        (∫⁻ y in ball x (q : ℝ), f y ∂μ) / μ (ball 0 (q : ℝ))) := funext he
  rw [hefun]
  exact Measurable.iSup fun q => Measurable.iSup fun _ =>
    (measurable_lintegral_ball μ hf (q : ℝ)).div measurable_const

/-- Adding a pointwise constant bound adds at most that constant to the maximal average. -/
theorem centeredMaximal_le_add_const {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ x, f x ≤ g x + c)
    (hballs : ∀ (x : X) (r : ℝ), 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞)
    (x : X) : centeredMaximal μ f x ≤ centeredMaximal μ g x + c := by
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  calc
    (∫⁻ y in ball x r, f y ∂μ) / μ (ball x r) ≤
        (∫⁻ y in ball x r, g y + c ∂μ) / μ (ball x r) :=
      ENNReal.div_le_div_right (lintegral_mono h) _
    _ = (∫⁻ y in ball x r, g y ∂μ) / μ (ball x r) + c := by
      rw [lintegral_add_right _ measurable_const, lintegral_const,
        Measure.restrict_apply_univ, ENNReal.add_div,
        ENNReal.mul_div_cancel_right (hballs x r hr).1 (hballs x r hr).2]
    _ ≤ centeredMaximal μ g x + c :=
      add_le_add (le_iSup_of_le r (le_iSup_of_le hr le_rfl)) le_rfl

/-- The truncation-distribution inequality at c=1/2, the main intermediate estimate
in Rudin's proof of 8.18. It is concrete, with no assumed weak-type hypothesis. -/
theorem centeredMaximal_truncation_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℝ≥0∞} (hf : Measurable f)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t / 2) * μ {x | ENNReal.ofReal t < centeredMaximal μ f x} ≤
      ENNReal.ofReal (5 ^ Module.finrank ℝ E) *
        ∫⁻ x in {x | ENNReal.ofReal (t / 2) < f x}, f x ∂μ := by
  let q := ENNReal.ofReal (t / 2)
  let g := {x | q < f x}.indicator f
  have hqsum : q + q = ENNReal.ofReal t := by
    change ENNReal.ofReal (t / 2) + ENNReal.ofReal (t / 2) = ENNReal.ofReal t
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ t / 2) (by positivity : 0 ≤ t / 2)]
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
      {x | q < centeredMaximal μ g x} := by
    intro x hx
    by_contra hnot
    have hle := (hM x).trans (add_le_add (le_of_not_gt hnot) le_rfl)
    rw [hqsum] at hle
    exact (not_le_of_gt hx) hle
  calc
    q * μ {x | ENNReal.ofReal t < centeredMaximal μ f x} ≤
        q * μ {x | q < centeredMaximal μ g x} := mul_le_mul_right (measure_mono hs) q
    _ ≤ ENNReal.ofReal (5 ^ Module.finrank ℝ E) * ∫⁻ x, g x ∂μ :=
      centeredMaximal_weak_one μ g q
    _ = _ := by rw [lintegral_indicator (measurableSet_lt measurable_const hf)]

end RudinRCA.Chapter08

/- Source fragment Ch08PowerLayerCake.lean -/



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

/- Source fragment Ch08StrongMaximal.lean -/



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
      congr 2
      ring
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
    rw [← lintegral_congr_ae (hfg.pow_const p)]
    exact hfi
  have he : maximalFunction μ f = centeredMaximal μ g :=
    centeredMaximal_congr_ae μ hfg
  rw [he]
  exact centeredMaximal_memLp_of_lintegral_rpow_lt_top μ hg hp hgi

end RudinRCA.Chapter08

/- Source fragment Ch08ParameterizedMaximal.lean -/



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
      congr 2
      ring
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

/- Source fragment Ch08MaximalConstant.lean -/

open Filter Set
open scoped Topology
namespace RudinRCA.Chapter08

/-- The elementary exponential estimate used in Rudin's optimized maximal bound. -/
theorem conjugateExponent_rpow_le_exp {p : ℝ} (hp : 1 < p) :
    (p / (p - 1)) ^ (p - 1) ≤ Real.exp 1 := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hd : 0 < p - 1 := sub_pos.mpr hp
  have hq : 0 < p / (p - 1) := div_pos hp0 hd
  rw [Real.rpow_def_of_pos hq, Real.exp_le_exp]
  have hlog := mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos hq) hd.le
  have he : (p / (p - 1) - 1) * (p - 1) = 1 := by
    field_simp [hd.ne']
    ring
  exact hlog.trans_eq he

/-- Bounding the optimized p-th-power coefficient by the one printed in 8.18. -/
theorem maximalLpCoefficient_le {A p : ℝ} (hA : 0 ≤ A) (hp : 1 < p) :
    A * p * (p / (p - 1)) ^ p ≤ A * Real.exp 1 * p * (p / (p - 1)) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq : 0 < p / (p - 1) := div_pos hp0 (sub_pos.mpr hp)
  have hpow : (p / (p - 1)) ^ p =
      (p / (p - 1)) * (p / (p - 1)) ^ (p - 1) := by
    calc
      _ = (p / (p - 1)) ^ (1 + (p - 1)) := by congr 1; ring
      _ = (p / (p - 1)) ^ (1 : ℝ) * (p / (p - 1)) ^ (p - 1) := Real.rpow_add hq _ _
      _ = _ := by rw [Real.rpow_one]
  calc
    _ = (A * p * (p / (p - 1))) * (p / (p - 1)) ^ (p - 1) := by rw [hpow]; ring
    _ ≤ (A * p * (p / (p - 1))) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (conjugateExponent_rpow_le_exp hp) (by positivity)
    _ = _ := by ring

/-- Scalar form of the optimized truncation coefficient, with cutoff t/q. -/
theorem maximalLpParameterizedCoefficient_le {A p : ℝ} (hA : 0 ≤ A) (hp : 1 < p) :
    p * (1 / (1 - 1 / (p / (p - 1)))) * A *
        ((p / (p - 1)) ^ (p - 1) / (p - 1)) ≤
      A * Real.exp 1 * p * (p / (p - 1)) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hd : 0 < p - 1 := sub_pos.mpr hp
  have hq : 0 < p / (p - 1) := div_pos hp0 hd
  have hden : 1 - 1 / (p / (p - 1)) = 1 / p := by
    field_simp [hp0.ne', hd.ne']
    ring
  have hpow : (p / (p - 1)) ^ p =
      (p / (p - 1)) * (p / (p - 1)) ^ (p - 1) := by
    calc
      _ = (p / (p - 1)) ^ (1 + (p - 1)) := by congr 1; ring
      _ = (p / (p - 1)) ^ (1 : ℝ) * (p / (p - 1)) ^ (p - 1) := Real.rpow_add hq _ _
      _ = _ := by rw [Real.rpow_one]
  calc
    _ = A * p * (p / (p - 1)) ^ p := by
      rw [hden, one_div_one_div, hpow]
      ring
    _ ≤ _ := maximalLpCoefficient_le hA hp

/-- The constant displayed after the proof of 8.18, for weak-type constant A. -/
noncomputable def maximalLpConstant (A p : ℝ) : ℝ :=
  (A * Real.exp 1 * p * (p / (p - 1))) ^ (1 / p)

/-- The optimized constant approaches one as p increases without bound. -/
theorem maximalLpConstant_tendsto_atTop {A : ℝ} (hA : 0 < A) :
    Tendsto (maximalLpConstant A) atTop (𝓝 1) := by
  have hi : Tendsto (fun p : ℝ => 1 / p) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hq : Tendsto (fun p : ℝ => p / (p - 1)) atTop (𝓝 1) := by
    have hdtop : Tendsto (fun p : ℝ => p - 1) atTop atTop := by
      apply tendsto_atTop.mpr
      intro b
      filter_upwards [eventually_ge_atTop (b + 1)] with p hp
      linarith
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_inv_atTop_zero.comp hdtop)
    apply (show Tendsto (fun p : ℝ => 1 + (p - 1)⁻¹) atTop (𝓝 1) by simpa using h).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with p hp
    field_simp [(sub_pos.mpr hp).ne']
    ring
  have hc : Tendsto (fun p : ℝ => (A * Real.exp 1) ^ (1 / p)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := A * Real.exp 1)).rpow hi
      (Or.inl (ne_of_gt (mul_pos hA (Real.exp_pos _))))
  have hqp : Tendsto (fun p : ℝ => (p / (p - 1)) ^ (1 / p)) atTop (𝓝 1) := by
    simpa using hq.rpow hi (Or.inl one_ne_zero)
  have hprod : Tendsto (fun p : ℝ => (A * Real.exp 1) ^ (1 / p) *
      p ^ (1 / p) * (p / (p - 1)) ^ (1 / p)) atTop (𝓝 1) := by
    simpa [Pi.mul_apply] using (hc.mul Real.tendsto_rpow_div).mul hqp
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with p hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < p / (p - 1) := div_pos hp0 (sub_pos.mpr hp)
  dsimp [maximalLpConstant]
  rw [Real.mul_rpow (by positivity : 0 ≤ A * Real.exp 1 * p) hq0.le,
    Real.mul_rpow (by positivity : 0 ≤ A * Real.exp 1) hp0.le]

/-- The optimized constant diverges as p decreases to one from above. -/
theorem maximalLpConstant_tendsto_one_right {A : ℝ} (hA : 0 < A) :
    Tendsto (maximalLpConstant A) (𝓝[>] 1) atTop := by
  have hid : Tendsto (fun p : ℝ => p) (𝓝[>] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hd : Tendsto (fun p : ℝ => p - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using hid.sub_const 1
    · filter_upwards [self_mem_nhdsWithin] with p hp
      exact sub_pos.mpr hp
  have hq : Tendsto (fun p : ℝ => p / (p - 1)) (𝓝[>] 1) atTop := by
    simpa only [div_eq_mul_inv, Function.comp_def] using
      hid.pos_mul_atTop zero_lt_one (tendsto_inv_nhdsGT_zero.comp hd)
  have hb : Tendsto (fun p : ℝ => A * Real.exp 1 * p * (p / (p - 1)))
      (𝓝[>] 1) atTop := by
    have hc : Tendsto (fun p : ℝ => A * Real.exp 1 * p) (𝓝[>] 1)
        (𝓝 (A * Real.exp 1)) := by simpa using hid.const_mul (A * Real.exp 1)
    exact hc.pos_mul_atTop (mul_pos hA (Real.exp_pos _)) hq
  have hi : Tendsto (fun p : ℝ => 1 / p) (𝓝[>] 1) (𝓝 1) := by
    simpa [Pi.div_apply] using (tendsto_const_nhds (x := (1 : ℝ))).div hid one_ne_zero
  have h := Real.tendsto_exp_atTop.comp
    ((Real.tendsto_log_atTop.comp hb).atTop_mul_pos zero_lt_one hi)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < p / (p - 1) := div_pos hp0 (sub_pos.mpr hp)
  exact (Real.rpow_def_of_pos (by positivity : 0 < A * Real.exp 1 * p * (p / (p - 1))) _).symm

end RudinRCA.Chapter08

/- Source fragment Ch08MaximalNorm.lean -/



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
  rw [he, lintegral_congr_ae (hfg.pow_const p)]
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
