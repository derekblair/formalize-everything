import RudinRCA.Chapter05
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Algebra.UnitizationL1
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Chapter 9: Fourier Transforms

Numbered declarations follow Walter Rudin, *Real and Complex Analysis*, third edition
(McGraw-Hill, 1987), Chapter 9 (printed pp. 178–193, nodes `9.1`–`9.23`).
Pinned Mathlib claims checks, normalization routes, and statement obligations are recorded
in `SCOPING-D.md` and `CLAIMS-D-CH09.md`.

Rudin normalizes Lebesgue measure on `ℝ` by `(2π)^(-1/2)` and uses the kernel `exp(-i x t)`,
whereas Mathlib's `𝓕` uses unscaled `volume` and `exp(-2π i x t)`. Both the direct frequency/mass
scaling identities and the isometric coordinate-dilation bridge (`u ↦ √(2π) * u`) are proved
explicitly in Section `Node9_1`.
-/

noncomputable section

open MeasureTheory Set Filter Metric TopologicalSpace Complex FourierTransform
open scoped ENNReal NNReal Topology ComplexConjugate Convolution RealInnerProductSpace Pointwise

namespace RudinRCA.Chapter09

/-! ## §9.1: Normalized measure, Lp norms, convolution, Fourier transform, C₀, characters,
and the explicit Mathlib normalization bridge -/

section Node9_1

/-- The scale factor `√(2π)` appearing in Rudin's Chapter 9 Lebesgue normalization. -/
def rudinScale : ℝ := Real.sqrt (2 * Real.pi)

/-- The reciprocal normalization constant `(2π)^(-1/2) = (√(2π))⁻¹`. -/
def rudinFactor : ℝ := (Real.sqrt (2 * Real.pi))⁻¹

/-- Nonnegative real bundled form of `(2π)^(-1/2)`, used so scaled Haar/locally-finite instances
synthesize automatically on `rudinMeasure`. -/
def rudinNNFactor : ℝ≥0 := ⟨rudinFactor, by unfold rudinFactor; positivity⟩

lemma rudinScale_pos : 0 < rudinScale := by
  unfold rudinScale
  positivity

lemma rudinScale_ne_zero : rudinScale ≠ 0 := rudinScale_pos.ne'

lemma rudinScale_sq : rudinScale ^ 2 = 2 * Real.pi := by
  unfold rudinScale
  exact Real.sq_sqrt (by positivity)

lemma rudinFactor_pos : 0 < rudinFactor := by
  unfold rudinFactor
  positivity

lemma rudinFactor_ne_zero : rudinFactor ≠ 0 := rudinFactor_pos.ne'

lemma rudinFactor_eq_inv_scale : rudinFactor = rudinScale⁻¹ := rfl

lemma rudinScale_mul_factor : rudinScale * rudinFactor = 1 :=
  mul_inv_cancel₀ rudinScale_ne_zero

lemma rudinFactor_mul_scale : rudinFactor * rudinScale = 1 :=
  inv_mul_cancel₀ rudinScale_ne_zero

lemma rudinNNFactor_coe : (rudinNNFactor : ℝ) = rudinFactor := rfl

lemma rudinNNFactor_pos : 0 < rudinNNFactor :=
  NNReal.coe_pos.mp rudinFactor_pos

lemma rudinNNFactor_ne_zero : rudinNNFactor ≠ 0 := rudinNNFactor_pos.ne'

/-- 9.1: Rudin's normalized Lebesgue measure `dm(x) = dx / √(2π)` on `ℝ`. -/
def rudinMeasure : Measure ℝ := rudinNNFactor • (volume : Measure ℝ)

theorem rudinMeasure_eq_ofReal_smul :
    rudinMeasure = ENNReal.ofReal rudinFactor • (volume : Measure ℝ) := by
  unfold rudinMeasure rudinNNFactor
  rw [ENNReal.ofReal_eq_coe_nnreal rudinFactor_pos.le]
  rfl

theorem rudinMeasure_apply (E : Set ℝ) :
    rudinMeasure E = ENNReal.ofReal (1 / Real.sqrt (2 * Real.pi)) * volume E := by
  rw [rudinMeasure_eq_ofReal_smul, Measure.smul_apply, smul_eq_mul, one_div, rudinFactor]

/-- Homeomorphism `u ↦ √(2π) * u` implementing the isometric bridge `(ℝ, volume) → (ℝ, m)`. -/
def rudinScaleHomeo : ℝ ≃ₜ ℝ := Homeomorph.mulLeft₀ rudinScale rudinScale_ne_zero

theorem map_rudinScale_volume :
    Measure.map (rudinScale * ·) (volume : Measure ℝ) = rudinMeasure := by
  rw [Real.map_volume_mul_left rudinScale_ne_zero, abs_of_pos (inv_pos.mpr rudinScale_pos),
    rudinMeasure_eq_ofReal_smul, rudinFactor_eq_inv_scale]

theorem measurePreserving_rudinScaleHomeo :
    MeasurePreserving rudinScaleHomeo volume rudinMeasure := by
  refine ⟨rudinScaleHomeo.measurable, ?_⟩
  change Measure.map (rudinScale * ·) volume = rudinMeasure
  exact map_rudinScale_volume

theorem measurePreserving_rudinScaleHomeo_symm :
    MeasurePreserving rudinScaleHomeo.symm rudinMeasure volume :=
  measurePreserving_rudinScaleHomeo.symm rudinScaleHomeo.toMeasurableEquiv

instance : SigmaFinite rudinMeasure := by
  unfold rudinMeasure
  infer_instance

instance : IsLocallyFiniteMeasure rudinMeasure := by
  unfold rudinMeasure
  infer_instance

instance : Measure.IsAddLeftInvariant rudinMeasure := by
  unfold rudinMeasure
  infer_instance

instance : Measure.IsAddRightInvariant rudinMeasure := by
  unfold rudinMeasure
  infer_instance

instance : Measure.IsNegInvariant rudinMeasure := by
  constructor
  ext E hE
  change Measure.map Neg.neg rudinMeasure E = rudinMeasure E
  rw [Measure.map_apply measurable_neg hE, rudinMeasure_apply, rudinMeasure_apply]
  congr 1
  have hv : Measure.map Neg.neg (volume : Measure ℝ) = volume := Measure.map_neg_eq_self volume
  exact (Measure.map_apply measurable_neg hE).symm.trans (congr_arg (fun μ : Measure ℝ => μ E) hv)

instance : NullSingletonClass rudinMeasure := by
  constructor
  intro x
  rw [rudinMeasure_apply, measure_singleton, mul_zero]

instance : Measure.IsAddHaarMeasure rudinMeasure := by
  let e : ℝ ≃ₗ[ℝ] ℝ :=
    { toFun := (rudinScale * ·)
      invFun := (rudinScale⁻¹ * ·)
      map_add' := fun x y => mul_add rudinScale x y
      map_smul' := fun c x => by simp [mul_left_comm]
      left_inv := fun x => inv_mul_cancel_left₀ rudinScale_ne_zero x
      right_inv := fun x => mul_inv_cancel_left₀ rudinScale_ne_zero x }
  have hmap : Measure.map e (volume : Measure ℝ) = rudinMeasure := map_rudinScale_volume
  rw [← hmap]
  infer_instance

instance : Measure.IsOpenPosMeasure rudinMeasure := by
  infer_instance

instance : Measure.InnerRegularCompactLTTop rudinMeasure := by
  infer_instance

theorem integral_rudinMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    ∫ x, f x ∂rudinMeasure = rudinFactor • ∫ x, f x := by
  unfold rudinMeasure
  rw [integral_smul_nnreal_measure]
  rfl

theorem setIntegral_rudinMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (S : Set ℝ) :
    ∫ x in S, f x ∂rudinMeasure = rudinFactor • ∫ x in S, f x := by
  rw [rudinMeasure_eq_ofReal_smul, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal rudinFactor_pos.le]

theorem integrable_rudinMeasure_iff {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} :
    Integrable f rudinMeasure ↔ Integrable f volume := by
  rw [rudinMeasure_eq_ofReal_smul]
  exact integrable_smul_measure (ENNReal.ofReal_pos.mpr rudinFactor_pos).ne' ENNReal.ofReal_ne_top

theorem memLp_rudinMeasure_iff {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {p : ℝ≥0∞} :
    MemLp f p rudinMeasure ↔ MemLp f p volume := by
  rw [rudinMeasure_eq_ofReal_smul]
  have hc0 : ENNReal.ofReal rudinFactor ≠ 0 := (ENNReal.ofReal_pos.mpr rudinFactor_pos).ne'
  refine ⟨fun h => ?_, fun h => h.smul_measure ENNReal.ofReal_ne_top⟩
  have h' := h.smul_measure (c := (ENNReal.ofReal rudinFactor)⁻¹) (ENNReal.inv_ne_top.mpr hc0)
  rwa [smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_smul] at h'

theorem ae_rudinMeasure_iff {P : ℝ → Prop} :
    (∀ᵐ x ∂rudinMeasure, P x) ↔ ∀ᵐ x ∂volume, P x := by
  rw [ae_iff, ae_iff, rudinMeasure_apply]
  exact mul_eq_zero.trans <| or_iff_right (ENNReal.ofReal_pos.mpr (by positivity)).ne'

/-- 9.1: Rudin's `L^p` space on `ℝ` with respect to normalized Lebesgue measure `m = dx / √(2π)`. -/
abbrev RudinLp (p : ℝ≥0∞) := Lp ℂ p rudinMeasure

/-- 9.1: Rudin's explicit `L^p` norm formula `(∫ |f|^p dm)^(1/p)` for `1 ≤ p < ∞`. -/
def rudinLpNorm (p : ℝ) (f : ℝ → ℂ) : ℝ :=
  (∫ x, ‖f x‖ ^ p ∂rudinMeasure) ^ (1 / p)

/-- 9.1: Rudin's essential supremum norm `‖f‖_∞` with respect to `m` (agreeing with ordinary
Lebesgue essential supremum since `m` and `volume` are mutually absolutely continuous). -/
def rudinLinftyNorm (f : ℝ → ℂ) : ℝ :=
  (eLpNorm f ∞ rudinMeasure).toReal

theorem rudinLpNorm_eq_volume (p : ℝ) (_hp : 0 < p) (f : ℝ → ℂ) :
    rudinLpNorm p f = rudinFactor ^ (1 / p) * (∫ x, ‖f x‖ ^ p) ^ (1 / p) := by
  unfold rudinLpNorm
  rw [integral_rudinMeasure, smul_eq_mul]
  have hnonneg : 0 ≤ ∫ x, ‖f x‖ ^ p :=
    integral_nonneg (fun x : ℝ => Real.rpow_nonneg (norm_nonneg (f x)) p)
  exact Real.mul_rpow rudinFactor_pos.le hnonneg

theorem rudinLp_norm_eq_rudinLpNorm {p : ℝ} (hp : 1 ≤ p) {f : ℝ → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) rudinMeasure) :
    ‖hf.toLp f‖ = rudinLpNorm p f := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  rw [Lp.norm_toLp, rudinLpNorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  have hint : Integrable (fun x => ‖f x‖ ^ p) rudinMeasure :=
    hf.integrable_norm_rpow hp_ne_zero ENNReal.ofReal_ne_top
      |>.congr (ae_of_all _ fun x => by rw [ENNReal.toReal_ofReal hp0.le])
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun x => Real.rpow_nonneg (norm_nonneg _) _) hint.aestronglyMeasurable,
    ENNReal.toReal_rpow]
  congr 2
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ofReal_norm]

theorem rudinLinftyNorm_eq_volume (f : ℝ → ℂ) :
    rudinLinftyNorm f = (eLpNorm f ∞ volume).toReal := by
  unfold rudinLinftyNorm
  rw [rudinMeasure_eq_ofReal_smul,
    eLpNorm_smul_measure_of_ne_zero (ENNReal.ofReal_pos.mpr rudinFactor_pos).ne']
  simp

/-- 9.1: Rudin's convolution `(f * g)(x) = ∫ f(x - y) g(y) dm(y)` with normalized measure `m`. -/
def rudinConv (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, f (x - y) * g y ∂rudinMeasure

/-- `rudinConv` agrees identically at every point with Mathlib's `MeasureTheory.convolution`
with respect to `rudinMeasure`. -/
theorem rudinConv_eq_convolution_rudinMeasure (f g : ℝ → ℂ) (x : ℝ) :
    rudinConv f g x = (f ⋆[ContinuousLinearMap.mul ℂ ℂ, rudinMeasure] g) x := by
  unfold rudinConv MeasureTheory.convolution
  simp only [ContinuousLinearMap.mul_apply']
  simpa [sub_sub_cancel] using
    (integral_sub_left_eq_self (fun y => f (x - y) * g y) rudinMeasure x).symm

/-- Direct scaling bridge between Rudin's convolution and Mathlib's unnormalized convolution. -/
theorem rudinConv_eq_smul_volume_convolution (f g : ℝ → ℂ) (x : ℝ) :
    rudinConv f g x = rudinFactor • (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) x := by
  rw [rudinConv_eq_convolution_rudinMeasure]
  unfold MeasureTheory.convolution
  rw [integral_rudinMeasure]

/-- 9.1: Rudin's Fourier transform `f̂(t) = ∫ f(x) exp(-i x t) dm(x)`. -/
def rudinFourier (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x, f x * Complex.exp (-Complex.I * x * t) ∂rudinMeasure

/-- Rudin's inverse Fourier integral `∫ g(t) exp(i x t) dm(t)`. -/
def rudinFourierInv (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t, g t * Complex.exp (Complex.I * x * t) ∂rudinMeasure

theorem norm_exp_neg_I_mul_mul (x t : ℝ) :
    ‖Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ))‖ = 1 := by
  have h : -Complex.I * (x : ℂ) * (t : ℂ) = (-(x * t) : ℝ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem norm_exp_I_mul_mul (x t : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))‖ = 1 := by
  have h : Complex.I * (x : ℂ) * (t : ℂ) = ((x * t) : ℝ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- 9.1: For `f ∈ L¹(m)`, the Fourier integrand `x ↦ f(x) e^(-i x t)` belongs to `L¹(m)` for
every real `t`, so `f̂(t)` is defined at every `t ∈ ℝ`. -/
theorem rudinFourier_integrand_integrable {f : ℝ → ℂ} (hf : Integrable f rudinMeasure) (t : ℝ) :
    Integrable (fun x : ℝ => f x * Complex.exp (-Complex.I * x * t)) rudinMeasure := by
  have hcont : Continuous (fun x : ℝ => Complex.exp (-Complex.I * x * t)) := by fun_prop
  refine (integrable_norm_iff (hf.aestronglyMeasurable.mul hcont.aestronglyMeasurable)).mp ?_
  refine hf.norm.congr (ae_of_all _ fun x => ?_)
  dsimp
  rw [norm_mul, norm_exp_neg_I_mul_mul, mul_one]

theorem rudinFourierInv_integrand_integrable {g : ℝ → ℂ} (hg : Integrable g rudinMeasure) (x : ℝ) :
    Integrable (fun t : ℝ => g t * Complex.exp (Complex.I * x * t)) rudinMeasure := by
  have hcont : Continuous (fun t : ℝ => Complex.exp (Complex.I * x * t)) := by fun_prop
  refine (integrable_norm_iff (hg.aestronglyMeasurable.mul hcont.aestronglyMeasurable)).mp ?_
  refine hg.norm.congr (ae_of_all _ fun t => ?_)
  dsimp
  rw [norm_mul, norm_exp_I_mul_mul, mul_one]

theorem rudinFourierInv_eq_rudinFourier_neg (g : ℝ → ℂ) (x : ℝ) :
    rudinFourierInv g x = rudinFourier g (-x) := by
  unfold rudinFourierInv rudinFourier
  congr 1 with t
  congr 2
  push_cast
  ring

theorem rudinFourier_congr_ae {f₁ f₂ : ℝ → ℂ} (h : f₁ =ᵐ[rudinMeasure] f₂) :
    rudinFourier f₁ = rudinFourier f₂ := by
  ext t
  unfold rudinFourier
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

/-- Direct normalization bridge: `rudinFourier f t = (√(2π))⁻¹ * (𝓕 f) (t / (2π))`, connecting
Rudin's `exp(-i x t) dm(x)` transform to Mathlib's `𝓕` (`exp(-2π i x t) dx`). -/
theorem rudinFourier_eq_mathlib_fourier (f : ℝ → ℂ) (t : ℝ) :
    rudinFourier f t = (rudinFactor : ℂ) * (𝓕 f) (t / (2 * Real.pi)) := by
  unfold rudinFourier
  rw [integral_rudinMeasure, Complex.real_smul, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [smul_eq_mul, mul_comm]
  congr 1
  congr 1
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (mul_pos two_pos Real.pi_pos).ne'
  push_cast
  field_simp [hpi]

/-- Direct normalization bridge for the inverse Fourier integral:
`rudinFourierInv g x = (√(2π))⁻¹ * (𝓕⁻ g) (x / (2π))`. -/
theorem rudinFourierInv_eq_mathlib_fourierInv (g : ℝ → ℂ) (x : ℝ) :
    rudinFourierInv g x = (rudinFactor : ℂ) * (𝓕⁻ g) (x / (2 * Real.pi)) := by
  rw [rudinFourierInv_eq_rudinFourier_neg, rudinFourier_eq_mathlib_fourier,
    Real.fourierInv_eq_fourier_neg, neg_div]

/-- Coordinate dilation `(rudinDilate f) u = f (√(2π) * u)`, mapping functions on `(ℝ, m)`
isometrically to functions on `(ℝ, volume)` while intertwining `rudinFourier` with `𝓕`. -/
def rudinDilate (f : ℝ → ℂ) (u : ℝ) : ℂ := f (rudinScale * u)

/-- Inverse coordinate dilation `(rudinUnDilate g) x = g (x / √(2π))`. -/
def rudinUnDilate (g : ℝ → ℂ) (x : ℝ) : ℂ := g (x / rudinScale)

@[simp]
theorem rudinUnDilate_rudinDilate (f : ℝ → ℂ) :
    rudinUnDilate (rudinDilate f) = f := by
  ext x
  simp only [rudinUnDilate, rudinDilate, mul_div_cancel₀ x rudinScale_ne_zero]

@[simp]
theorem rudinDilate_rudinUnDilate (g : ℝ → ℂ) :
    rudinDilate (rudinUnDilate g) = g := by
  ext u
  simp only [rudinUnDilate, rudinDilate, mul_div_cancel_left₀ u rudinScale_ne_zero]

theorem integral_rudinDilate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    ∫ u, f (rudinScale * u) = ∫ x, f x ∂rudinMeasure :=
  measurePreserving_rudinScaleHomeo.integral_comp rudinScaleHomeo.toMeasurableEquiv.measurableEmbedding f

/-- Isometric equivalence `Lp ℂ p rudinMeasure ≃ₗᵢ[ℂ] Lp ℂ p volume` induced by `u ↦ √(2π) * u`. -/
def rudinScaleLpEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)] : RudinLp p ≃ₗᵢ[ℂ] Lp ℂ p (volume : Measure ℝ) :=
  LinearIsometryEquiv.ofLinearIsometry
    (Lp.compMeasurePreservingₗᵢ ℂ rudinScaleHomeo measurePreserving_rudinScaleHomeo)
    (Lp.compMeasurePreservingₗ ℂ rudinScaleHomeo.symm measurePreserving_rudinScaleHomeo_symm)
    (by
      ext g : 1
      change Lp.compMeasurePreserving rudinScaleHomeo measurePreserving_rudinScaleHomeo
        (Lp.compMeasurePreserving rudinScaleHomeo.symm measurePreserving_rudinScaleHomeo_symm g) = g
      rw [← Lp.compMeasurePreserving_comp_apply]
      have hid : (rudinScaleHomeo.symm ∘ rudinScaleHomeo) = id := by
        ext u; exact rudinScaleHomeo.symm_apply_apply u
      simp [hid])
    (by
      ext f : 1
      change Lp.compMeasurePreserving rudinScaleHomeo.symm measurePreserving_rudinScaleHomeo_symm
        (Lp.compMeasurePreserving rudinScaleHomeo measurePreserving_rudinScaleHomeo f) = f
      rw [← Lp.compMeasurePreserving_comp_apply]
      have hid : (rudinScaleHomeo ∘ rudinScaleHomeo.symm) = id := by
        ext x; exact rudinScaleHomeo.apply_symm_apply x
      simp [hid])

theorem rudinScaleLpEquiv_coeFn (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : RudinLp p) :
    (rudinScaleLpEquiv p f : ℝ → ℂ) =ᵐ[volume] rudinDilate f :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_rudinScaleHomeo

theorem rudinScaleLpEquiv_symm_coeFn (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : Lp ℂ p (volume : Measure ℝ)) :
    ((rudinScaleLpEquiv p).symm g : ℝ → ℂ) =ᵐ[rudinMeasure] rudinUnDilate g := by
  have h : ((rudinScaleLpEquiv p).symm g : ℝ → ℂ) =ᵐ[rudinMeasure] g ∘ rudinScaleHomeo.symm :=
    Lp.coeFn_compMeasurePreserving g measurePreserving_rudinScaleHomeo_symm
  filter_upwards [h] with x hx
  rw [hx]
  change g (rudinScale⁻¹ * x) = g (x / rudinScale)
  rw [div_eq_inv_mul]

/-- Dilation bridge for the Fourier transform: `U (F_R f) = 𝓕 (U f)` everywhere on `ℝ`. -/
theorem rudinDilate_rudinFourier (f : ℝ → ℂ) :
    rudinDilate (rudinFourier f) = 𝓕 (rudinDilate f) := by
  ext v
  unfold rudinDilate rudinFourier
  rw [← integral_rudinDilate, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with u
  rw [smul_eq_mul, mul_comm]
  congr 1
  congr 1
  have hsq : (rudinScale : ℂ) * rudinScale = 2 * Real.pi := by
    exact_mod_cast (pow_two rudinScale ▸ rudinScale_sq)
  calc
    -Complex.I * ↑(rudinScale * u) * ↑(rudinScale * v)
        = -((rudinScale : ℂ) * rudinScale) * u * v * Complex.I := by push_cast; ring
    _ = -(2 * Real.pi) * u * v * Complex.I := by rw [hsq]
    _ = ↑(-2 * Real.pi * u * v) * Complex.I := by push_cast; ring

/-- Dilation bridge for the inverse Fourier integral: `U (F_R_inv g) = 𝓕⁻ (U g)` everywhere. -/
theorem rudinDilate_rudinFourierInv (g : ℝ → ℂ) :
    rudinDilate (rudinFourierInv g) = 𝓕⁻ (rudinDilate g) := by
  ext v
  have h1 := congr_fun (rudinDilate_rudinFourier g) (-v)
  change rudinFourier g (rudinScale * -v) = 𝓕 (rudinDilate g) (-v) at h1
  rw [mul_neg, ← rudinFourierInv_eq_rudinFourier_neg, ← Real.fourierInv_eq_fourier_neg] at h1
  exact h1

/-- Dilation bridge for convolution: `U (f *_R g) = (U f) ⋆ (U g)` everywhere on `ℝ`. -/
theorem rudinDilate_rudinConv (f g : ℝ → ℂ) :
    rudinDilate (rudinConv f g) =
      (rudinDilate f) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (rudinDilate g) := by
  ext v
  unfold rudinDilate rudinConv MeasureTheory.convolution
  simp only [ContinuousLinearMap.mul_apply']
  rw [← integral_rudinDilate]
  have hsub : ∀ u : ℝ, rudinScale * v - rudinScale * u = rudinScale * (v - u) := fun u => by ring
  simp_rw [hsub]
  simpa [sub_sub_cancel] using
    (integral_sub_left_eq_self (fun u => f (rudinScale * (v - u)) * g (rudinScale * u)) volume v).symm

/-- 9.1: `C₀(ℝ)`, the space of continuous complex-valued functions on `ℝ` vanishing at infinity. -/
abbrev RudinC0 := ZeroAtInftyContinuousMap ℝ ℂ

/-- 9.1: Rudin's printed compact-complement definition of vanishing at infinity (`C₀`). -/
def IsVanishingAtInfty (g : ℝ → ℂ) : Prop :=
  Continuous g ∧ ∀ ε : ℝ, 0 < ε → ∃ K : Set ℝ, IsCompact K ∧ ∀ x : ℝ, x ∉ K → ‖g x‖ < ε

theorem isVanishingAtInfty_iff_cocompact {g : ℝ → ℂ} :
    IsVanishingAtInfty g ↔ Continuous g ∧ Tendsto g (cocompact ℝ) (𝓝 0) := by
  unfold IsVanishingAtInfty
  refine and_congr_right fun _ => ?_
  rw [Metric.tendsto_nhds]
  constructor
  · intro h ε hε
    obtain ⟨K, hK, hbound⟩ := h ε hε
    rw [Filter.Eventually, Filter.mem_cocompact]
    exact ⟨K, hK, fun x hx => by simpa [dist_zero_right] using hbound x hx⟩
  · intro h ε hε
    have hev := h ε hε
    rw [Filter.Eventually, Filter.mem_cocompact] at hev
    obtain ⟨K, hK, hsub⟩ := hev
    exact ⟨K, hK, fun x hx => by simpa [dist_zero_right] using hsub hx⟩

/-- 9.1: `C₀(ℝ)` is a Banach space under the supremum norm. -/
theorem rudinC0_completeSpace : CompleteSpace RudinC0 := inferInstance

/-- 9.1: Continuous unit-modulus additive characters `φ : ℝ → ℂ` (`|φ(x)| = 1`, `φ(x+y) = φ(x)φ(y)`). -/
def IsRudinCharacter (φ : ℝ → ℂ) : Prop :=
  Continuous φ ∧ (∀ x : ℝ, ‖φ x‖ = 1) ∧ ∀ x y : ℝ, φ (x + y) = φ x * φ y

/-- The concrete additive character `x ↦ exp(i t x)` associated to a real frequency `t`. -/
def rudinFreqChar (t : ℝ) (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * t * x)

theorem rudinFreqChar_isRudinCharacter (t : ℝ) : IsRudinCharacter (rudinFreqChar t) := by
  refine ⟨by unfold rudinFreqChar; fun_prop, fun x => ?_, fun x y => ?_⟩
  · unfold rudinFreqChar
    exact norm_exp_I_mul_mul t x
  · unfold rudinFreqChar
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

end Node9_1

/-! ## §9.2–9.3: Transform calculus and the finite-difference remark -/

section Node9_2_9_3

/-- 9.2(a): Modulating `f ∈ L¹(m)` by `e^(i α x)` shifts `f̂` by `α`: `ĝ(t) = f̂(t - α)`. -/
theorem theorem_9_2_a {f : ℝ → ℂ} (_hf : Integrable f rudinMeasure) (α t : ℝ) :
    rudinFourier (fun x => f x * Complex.exp (Complex.I * α * x)) t =
      rudinFourier f (t - α) := by
  unfold rudinFourier
  congr 1 with x
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- 9.2(b): Translating `f ∈ L¹(m)` by `α` (`g(x) = f(x - α)`) multiplies `f̂(t)` by `e^(-i α t)`. -/
theorem theorem_9_2_b {f : ℝ → ℂ} (_hf : Integrable f rudinMeasure) (α t : ℝ) :
    rudinFourier (fun x => f (x - α)) t =
      rudinFourier f t * Complex.exp (-Complex.I * α * t) := by
  unfold rudinFourier
  have hsub := integral_sub_right_eq_self
    (fun x : ℝ => f x * Complex.exp (-Complex.I * (x + α) * t)) α (μ := rudinMeasure)
  have hsub' : (fun x : ℝ => f (x - α) * Complex.exp (-Complex.I * ((x - α : ℝ) + α) * t)) =
      fun x : ℝ => f (x - α) * Complex.exp (-Complex.I * x * t) := by
    ext x
    congr 2
    push_cast
    ring
  rw [← hsub', hsub]
  have hexp : ∀ x : ℝ,
      f x * Complex.exp (-Complex.I * (x + α) * t) =
        Complex.exp (-Complex.I * α * t) * (f x * Complex.exp (-Complex.I * x * t)) := by
    intro x
    have h1 : -Complex.I * ((x : ℂ) + α) * t = (-Complex.I * α * t) + (-Complex.I * x * t) := by
      ring
    rw [h1, Complex.exp_add]
    ring
  simp_rw [hexp]
  rw [integral_const_mul, mul_comm]

/-- 9.2(c): For `f, g ∈ L¹(m)`, `h = f * g` belongs to `L¹(m)` and `ĥ(t) = f̂(t) ĝ(t)`. -/
theorem theorem_9_2_c {f g : ℝ → ℂ} (hf : Integrable f rudinMeasure)
    (hg : Integrable g rudinMeasure) :
    Integrable (rudinConv f g) rudinMeasure ∧
      ∀ t : ℝ, rudinFourier (rudinConv f g) t = rudinFourier f t * rudinFourier g t := by
  have hint : Integrable (rudinConv f g) rudinMeasure := by
    have hconv := hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg
    exact hconv.congr (ae_of_all _ fun x => (rudinConv_eq_convolution_rudinMeasure f g x).symm)
  refine ⟨hint, fun t => ?_⟩
  have hUf : Integrable (rudinDilate f) volume :=
    (measurePreserving_rudinScaleHomeo.integrable_comp_emb
      rudinScaleHomeo.toMeasurableEquiv.measurableEmbedding).mpr hf
  have hUg : Integrable (rudinDilate g) volume :=
    (measurePreserving_rudinScaleHomeo.integrable_comp_emb
      rudinScaleHomeo.toMeasurableEquiv.measurableEmbedding).mpr hg
  let v := t / rudinScale
  have hv : rudinScale * v = t := mul_div_cancel₀ t rudinScale_ne_zero
  calc
    rudinFourier (rudinConv f g) t
        = rudinDilate (rudinFourier (rudinConv f g)) v := by simp [rudinDilate, hv]
    _ = 𝓕 (rudinDilate (rudinConv f g)) v := by rw [rudinDilate_rudinFourier]
    _ = 𝓕 ((rudinDilate f) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (rudinDilate g)) v := by
        rw [rudinDilate_rudinConv]
    _ = 𝓕 (rudinDilate f) v * 𝓕 (rudinDilate g) v :=
        Real.fourier_mul_convolution_eq hUf hUg v
    _ = rudinDilate (rudinFourier f) v * rudinDilate (rudinFourier g) v := by
        rw [← rudinDilate_rudinFourier, ← rudinDilate_rudinFourier]
    _ = rudinFourier f t * rudinFourier g t := by simp [rudinDilate, hv]

/-- 9.2(d): Conjugate-reflection: if `g(x) = conj(f(-x))`, then `ĝ(t) = conj(f̂(t))`. -/
theorem theorem_9_2_d {f : ℝ → ℂ} (_hf : Integrable f rudinMeasure) (t : ℝ) :
    rudinFourier (fun x => conj (f (-x))) t = conj (rudinFourier f t) := by
  unfold rudinFourier
  rw [← integral_conj]
  have hneg := integral_neg_eq_self
    (fun x : ℝ => conj (f x * Complex.exp (-Complex.I * x * t))) rudinMeasure
  rw [← hneg]
  congr 1 with x
  rw [map_mul, ← Complex.exp_conj]
  congr 1
  congr 1
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

/-- 9.2(e): Positive dilation: if `g(x) = f(x / λ)` for `λ > 0`, then `ĝ(t) = λ f̂(λ t)`. -/
theorem theorem_9_2_e {f : ℝ → ℂ} (_hf : Integrable f rudinMeasure) {l : ℝ} (hl : 0 < l)
    (t : ℝ) :
    rudinFourier (fun x => f (x / l)) t = (l : ℂ) * rudinFourier f (l * t) := by
  unfold rudinFourier
  rw [integral_rudinMeasure, integral_rudinMeasure, Complex.real_smul, Complex.real_smul]
  have hcomp := Measure.integral_comp_div
    (fun u : ℝ => f u * Complex.exp (-Complex.I * u * ↑(l * t))) l
  rw [abs_of_pos hl, Complex.real_smul] at hcomp
  have heq : (fun x : ℝ => f (x / l) * Complex.exp (-Complex.I * x * t)) =
      fun x : ℝ => f (x / l) * Complex.exp (-Complex.I * ↑(x / l) * ↑(l * t)) := by
    ext x
    congr 2
    have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
    push_cast
    field_simp [hl']
  rw [heq, hcomp]
  ring

/-- 9.2(f): Differentiation under the Fourier integral: if `f ∈ L¹(m)` and `g(x) = -i x f(x)`
also belongs to `L¹(m)`, then `f̂` is differentiable at every `t ∈ ℝ` with `(f̂)'(t) = ĝ(t)`. -/
theorem theorem_9_2_f_hasDerivAt {f : ℝ → ℂ} (hf : Integrable f rudinMeasure)
    (hg : Integrable (fun x : ℝ => -Complex.I * x * f x) rudinMeasure) (t : ℝ) :
    HasDerivAt (rudinFourier f) (rudinFourier (fun x : ℝ => -Complex.I * x * f x) t) t := by
  have hUf : Integrable (rudinDilate f) volume :=
    (measurePreserving_rudinScaleHomeo.integrable_comp_emb
      rudinScaleHomeo.toMeasurableEquiv.measurableEmbedding).mpr hf
  have hUg : Integrable (rudinDilate (fun x : ℝ => -Complex.I * x * f x)) volume :=
    (measurePreserving_rudinScaleHomeo.integrable_comp_emb
      rudinScaleHomeo.toMeasurableEquiv.measurableEmbedding).mpr hg
  have hUf' : Integrable (fun u : ℝ => u • rudinDilate f u) volume := by
    have hs : (rudinScale : ℂ) ≠ 0 := by exact_mod_cast rudinScale_ne_zero
    have hconst : (-Complex.I * rudinScale) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hs
    have hsmul := hUg.smul ((-Complex.I * rudinScale)⁻¹)
    refine hsmul.congr (ae_of_all _ fun u => ?_)
    change (-Complex.I * ↑rudinScale)⁻¹ * (-Complex.I * ↑(rudinScale * u) * f (rudinScale * u)) =
      (u : ℂ) * f (rudinScale * u)
    push_cast
    field_simp [hconst, hs]
  have hfeq : rudinFourier f = (𝓕 (rudinDilate f)) ∘ fun w : ℝ => w / rudinScale := by
    ext w
    have hw : rudinScale * (w / rudinScale) = w := mul_div_cancel₀ w rudinScale_ne_zero
    calc
      rudinFourier f w = rudinDilate (rudinFourier f) (w / rudinScale) := by
        simp only [rudinDilate, hw]
      _ = (𝓕 (rudinDilate f)) (w / rudinScale) :=
        congr_fun (rudinDilate_rudinFourier f) (w / rudinScale)
      _ = ((𝓕 (rudinDilate f)) ∘ fun w : ℝ => w / rudinScale) w := rfl
  rw [hfeq]
  have hd1 := Real.hasDerivAt_fourier hUf hUf' (t / rudinScale)
  have hd2 : HasDerivAt (fun w : ℝ => w / rudinScale) (rudinScale⁻¹) t := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id t).mul_const rudinScale⁻¹
  have hd := hd1.scomp t hd2
  refine hd.congr_deriv ?_
  have hgoal : rudinFourier (fun x : ℝ => -Complex.I * x * f x) t =
      𝓕 (rudinDilate (fun x : ℝ => -Complex.I * x * f x)) (t / rudinScale) := by
    rw [← rudinDilate_rudinFourier]
    simp only [rudinDilate, mul_div_cancel₀ t rudinScale_ne_zero]
  rw [hgoal, Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_smul]
  apply integral_congr_ae
  filter_upwards with u
  simp only [rudinDilate, Complex.real_smul, smul_eq_mul, Complex.ofReal_inv]
  have hc : (rudinScale : ℂ)⁻¹ * (-2 * ↑Real.pi * Complex.I * ↑u) =
      -Complex.I * ↑(rudinScale * u) := by
    have h2pi : (2 * (Real.pi : ℂ)) = (rudinScale : ℂ) ^ 2 := by
      exact_mod_cast rudinScale_sq.symm
    have hs : (rudinScale : ℂ) ≠ 0 := by exact_mod_cast rudinScale_ne_zero
    push_cast
    linear_combination (-Complex.I * u * (rudinScale : ℂ)⁻¹) * h2pi +
      (-Complex.I * u * rudinScale) * (inv_mul_cancel₀ hs)
  calc
    (rudinScale : ℂ)⁻¹ *
        (Complex.exp (↑(-2 * Real.pi * u * (t / rudinScale)) * Complex.I) *
          (-2 * ↑Real.pi * Complex.I * ↑u * f (rudinScale * u)))
        = Complex.exp (↑(-2 * Real.pi * u * (t / rudinScale)) * Complex.I) *
            (((rudinScale : ℂ)⁻¹ * (-2 * ↑Real.pi * Complex.I * ↑u)) * f (rudinScale * u)) := by
          ring
    _ = Complex.exp (↑(-2 * Real.pi * u * (t / rudinScale)) * Complex.I) *
          (-Complex.I * ↑(rudinScale * u) * f (rudinScale * u)) := by rw [hc]

/-- 9.2(f): Global differentiability and derivative formula `(f̂)' = (-i x f)^`. -/
theorem theorem_9_2_f {f : ℝ → ℂ} (hf : Integrable f rudinMeasure)
    (hg : Integrable (fun x : ℝ => -Complex.I * x * f x) rudinMeasure) :
    Differentiable ℝ (rudinFourier f) ∧
      deriv (rudinFourier f) = rudinFourier (fun x : ℝ => -Complex.I * x * f x) := by
  refine ⟨fun t => (theorem_9_2_f_hasDerivAt hf hg t).differentiableAt, ?_⟩
  ext t
  exact (theorem_9_2_f_hasDerivAt hf hg t).deriv

/-- 9.3 (first obligation): Sequential convergence along arbitrary nonzero sequences `α_n → 0`
is equivalent to punctured-neighborhood convergence `α → 0` (`α ≠ 0`) on `ℝ`, justifying Rudin's
invocation of sequential dominated convergence in the proof of 9.2(f). -/
theorem remark_9_3_punctured_seq_tendsto {E : Type*} [TopologicalSpace E]
    (Φ : ℝ → E) (L : E) :
    Tendsto Φ (𝓝[≠] (0 : ℝ)) (𝓝 L) ↔
      ∀ α : ℕ → ℝ, (∀ n, α n ≠ 0) → Tendsto α atTop (𝓝 0) → Tendsto (Φ ∘ α) atTop (𝓝 L) := by
  rw [Filter.tendsto_iff_seq_tendsto]
  constructor
  · intro h α hne hlim
    apply h α
    exact tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hne⟩
  · intro h α hα
    rw [tendsto_nhdsWithin_iff] at hα
    obtain ⟨hlim, hev⟩ := hα
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    have hshift : Tendsto (Φ ∘ fun n => α (n + N)) atTop (𝓝 L) :=
      h (fun n => α (n + N)) (fun n => hN (n + N) (Nat.le_add_left N n))
        (hlim.comp (tendsto_add_atTop_nat N))
    exact (tendsto_add_atTop_iff_nat N).mp hshift

/-- 9.3 (second obligation): Displayed finite-difference Fourier identity on p. 180:
for `f ∈ L¹(m)` and `α ≠ 0`, the transform of `x ↦ (f(x + α) - f(x)) / α` is
`t ↦ f̂(t) (e^(i α t) - 1) / α`. -/
theorem remark_9_3_finite_difference {f : ℝ → ℂ} (hf : Integrable f rudinMeasure)
    {α : ℝ} (hα : α ≠ 0) (t : ℝ) :
    rudinFourier (fun x => (f (x + α) - f x) / (α : ℂ)) t =
      rudinFourier f t * (Complex.exp (Complex.I * α * t) - 1) / (α : ℂ) := by
  have hf_shift : Integrable (fun x => f (x - (-α))) rudinMeasure :=
    hf.comp_sub_right (-α)
  have h1 : (fun x : ℝ => (f (x + α) - f x) / (α : ℂ)) =
      fun x : ℝ => ((α : ℂ)⁻¹) * (f (x - (-α)) - f x) := by
    ext x
    rw [sub_neg_eq_add, div_eq_inv_mul]
  rw [h1]
  have hlin : rudinFourier (fun x => (α : ℂ)⁻¹ * (f (x - -α) - f x)) t =
      (α : ℂ)⁻¹ * (rudinFourier (fun x => f (x - -α)) t - rudinFourier f t) := by
    unfold rudinFourier
    have h2 : (fun x : ℝ => (α : ℂ)⁻¹ * (f (x - -α) - f x) * Complex.exp (-Complex.I * x * t)) =
        fun x : ℝ => (α : ℂ)⁻¹ *
          (f (x - -α) * Complex.exp (-Complex.I * x * t) -
            f x * Complex.exp (-Complex.I * x * t)) := by
      ext x; ring
    simp_rw [h2]
    rw [integral_const_mul, integral_sub
      (rudinFourier_integrand_integrable hf_shift t)
      (rudinFourier_integrand_integrable hf t)]
  rw [hlin, theorem_9_2_b hf (-α) t]
  have hexp : Complex.exp (-Complex.I * ↑(-α) * ↑t) = Complex.exp (Complex.I * α * t) := by
    congr 1
    push_cast
    ring
  rw [hexp]
  have hα' : (α : ℂ) ≠ 0 := by exact_mod_cast hα
  field_simp [hα']

end Node9_2_9_3

/-! ## §9.5, §9.7–9.10: Auxiliary Poisson kernels, Lp translation continuity,
and Lp approximate-identity convergence -/

section Node9_5_9_7_to_9_10

/-- 9.7: Rudin's auxiliary tent-exponential kernel `H(t) = e^(-|t|)`. -/
def rudinH (t : ℝ) : ℝ := Real.exp (-|t|)

/-- 9.7: Rudin's inverse-Fourier Poisson integral `h_λ(x) = ∫ H(λ t) e^(i t x) dm(t)`. -/
def rudinPoissonInt (l x : ℝ) : ℂ :=
  ∫ t, (rudinH (l * t) : ℂ) * Complex.exp (Complex.I * t * x) ∂rudinMeasure

/-- 9.7: Closed-form real Poisson/Cauchy kernel `h_λ(x) = √(2/π) λ / (λ² + x²)`. -/
def rudinPoisson (l x : ℝ) : ℝ :=
  Real.sqrt (2 / Real.pi) * l / (l ^ 2 + x ^ 2)

/-- 9.7: `0 < H(t) ≤ 1` for every `t ∈ ℝ`. -/
theorem theorem_9_7_H_bounds (t : ℝ) : 0 < rudinH t ∧ rudinH t ≤ 1 := by
  unfold rudinH
  refine ⟨Real.exp_pos _, ?_⟩
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg t))

theorem rudinH_zero : rudinH 0 = 1 := by
  simp [rudinH]

theorem continuous_rudinH : Continuous rudinH := by
  unfold rudinH
  fun_prop

/-- 9.7: `H(λ t) → 1` as `λ ↓ 0` for every `t ∈ ℝ`. -/
theorem theorem_9_7_H_tendsto_one (t : ℝ) :
    Tendsto (fun l : ℝ => rudinH (l * t)) (𝓝[>] 0) (𝓝 1) := by
  have hcont : Continuous (fun l : ℝ => rudinH (l * t)) :=
    continuous_rudinH.comp (continuous_id.mul continuous_const)
  have h0 : rudinH (0 * t) = 1 := by simp [rudinH]
  rw [← h0]
  exact (hcont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds

theorem rudinH_scaled_integrable {l : ℝ} (hl : 0 < l) :
    Integrable (fun t : ℝ => rudinH (l * t)) rudinMeasure := by
  rw [integrable_rudinMeasure_iff]
  have hIic : IntegrableOn (fun t : ℝ => rudinH (l * t)) (Iic 0) volume := by
    refine (integrableOn_exp_mul_Iic hl 0).congr_fun (fun t (ht : t ≤ 0) => ?_) measurableSet_Iic
    unfold rudinH
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hl.le ht)]
    ring_nf
  have hIoi : IntegrableOn (fun t : ℝ => rudinH (l * t)) (Ioi 0) volume := by
    refine (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hl) 0).congr_fun
      (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    unfold rudinH
    rw [abs_of_pos (mul_pos hl ht)]
    ring_nf
  rw [← integrableOn_univ, ← Iic_union_Ioi]
  exact hIic.union hIoi

private lemma rudinFactor_mul_two_eq_sqrt_two_div_pi :
    rudinFactor * 2 = Real.sqrt (2 / Real.pi) := by
  have hlhs_pos : 0 ≤ rudinFactor * 2 := mul_nonneg rudinFactor_pos.le (by positivity)
  have hrhs_pos : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  rw [← Real.sqrt_sq hlhs_pos, Real.sqrt_inj (sq_nonneg _) (by positivity)]
  unfold rudinFactor
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_pos.ne'
  calc
    ((Real.sqrt (2 * Real.pi))⁻¹ * 2) ^ 2
        = ((Real.sqrt (2 * Real.pi)) ^ 2)⁻¹ * 4 := by ring
    _ = (2 * Real.pi)⁻¹ * 4 := by rw [Real.sq_sqrt (by positivity)]
    _ = 2 / Real.pi := by field_simp [hpi]; ring

private lemma rudinFactor_mul_sqrt_two_div_pi :
    rudinFactor * Real.sqrt (2 / Real.pi) = Real.pi⁻¹ := by
  have hlhs_pos : 0 ≤ rudinFactor * Real.sqrt (2 / Real.pi) :=
    mul_nonneg rudinFactor_pos.le (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq hlhs_pos, ← Real.sqrt_sq (inv_nonneg.mpr Real.pi_pos.le),
    Real.sqrt_inj (sq_nonneg _) (sq_nonneg _)]
  unfold rudinFactor
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_pos.ne'
  calc
    ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (2 / Real.pi)) ^ 2
        = ((Real.sqrt (2 * Real.pi)) ^ 2)⁻¹ * (Real.sqrt (2 / Real.pi)) ^ 2 := by ring
    _ = (2 * Real.pi)⁻¹ * (2 / Real.pi) := by
        rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    _ = (Real.pi⁻¹) ^ 2 := by field_simp [hpi]

/-- 9.7: Explicit evaluation `∫ H(λ t) e^(i t x) dm(t) = √(2/π) λ / (λ² + x²)` for `λ > 0`. -/
theorem theorem_9_7_poisson_formula {l : ℝ} (hl : 0 < l) (x : ℝ) :
    rudinPoissonInt l x = (rudinPoisson l x : ℂ) := by
  unfold rudinPoissonInt
  rw [integral_rudinMeasure, Complex.real_smul]
  let a₁ : ℂ := (l : ℂ) + Complex.I * x
  let a₂ : ℂ := -(l : ℂ) + Complex.I * x
  have ha₁ : 0 < a₁.re := by simp [a₁, hl]
  have ha₂ : a₂.re < 0 := by simp [a₂, hl]
  let φ : ℝ → ℂ := fun t => (rudinH (l * t) : ℂ) * Complex.exp (Complex.I * t * x)
  have hφ_Iic : EqOn φ (fun t : ℝ => Complex.exp (a₁ * t)) (Iic 0) := by
    intro t (ht : t ≤ 0)
    simp only [φ, rudinH, Complex.ofReal_exp, ← Complex.exp_add]
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hl.le ht)]
    congr 1
    simp only [a₁]
    push_cast
    ring
  have hφ_Ioi : EqOn φ (fun t : ℝ => Complex.exp (a₂ * t)) (Ioi 0) := by
    intro t (ht : 0 < t)
    simp only [φ, rudinH, Complex.ofReal_exp, ← Complex.exp_add]
    rw [abs_of_pos (mul_pos hl ht)]
    congr 1
    simp only [a₂]
    push_cast
    ring
  have hint_Iic : IntegrableOn φ (Iic 0) volume :=
    (integrableOn_exp_mul_complex_Iic ha₁ 0).congr_fun hφ_Iic.symm measurableSet_Iic
  have hint_Ioi : IntegrableOn φ (Ioi 0) volume :=
    (integrableOn_exp_mul_complex_Ioi ha₂ 0).congr_fun hφ_Ioi.symm measurableSet_Ioi
  have hcompl : (Iic (0 : ℝ))ᶜ = Ioi 0 := compl_Iic
  have hint_all : Integrable φ volume := by
    rw [← integrableOn_univ, ← Iic_union_Ioi]
    exact hint_Iic.union hint_Ioi
  rw [← integral_add_compl measurableSet_Iic hint_all, hcompl,
    setIntegral_congr_fun measurableSet_Iic hφ_Iic,
    setIntegral_congr_fun measurableSet_Ioi hφ_Ioi,
    integral_exp_mul_complex_Iic ha₁ 0,
    integral_exp_mul_complex_Ioi ha₂ 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have ha₁_ne : a₁ ≠ 0 := fun h => ha₁.ne' (by simp [h])
  have ha₂_ne : a₂ ≠ 0 := fun h => ha₂.ne (by simp [h])
  have hdenom_pos : 0 < l ^ 2 + x ^ 2 := by positivity
  have hdenom_ne : ((l : ℂ) ^ 2 + (x : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hdenom_pos.ne'
  have hsum : (1 : ℂ) / a₁ + -(1 : ℂ) / a₂ = 2 * (l : ℂ) / ((l : ℂ) ^ 2 + (x : ℂ) ^ 2) := by
    have hprod : a₁ * (-a₂) = (l : ℂ) ^ 2 + (x : ℂ) ^ 2 := by
      simp only [a₁, a₂]
      linear_combination -((x : ℂ) ^ 2) * Complex.I_sq
    have hneg_a₂ : -a₂ ≠ 0 := neg_ne_zero.mpr ha₂_ne
    rw [← hprod]
    field_simp [ha₁_ne, ha₂_ne, hneg_a₂]
    simp only [a₁, a₂]
    ring
  rw [hsum]
  unfold rudinPoisson
  rw [← rudinFactor_mul_two_eq_sqrt_two_div_pi]
  push_cast
  ring

theorem rudinPoisson_pos {l : ℝ} (hl : 0 < l) (x : ℝ) : 0 < rudinPoisson l x := by
  unfold rudinPoisson
  positivity

theorem rudinPoisson_even (l x : ℝ) : rudinPoisson l (-x) = rudinPoisson l x := by
  unfold rudinPoisson
  ring

theorem rudinPoisson_le {l : ℝ} (hl : 0 < l) (x : ℝ) :
    rudinPoisson l x ≤ Real.sqrt (2 / Real.pi) / l := by
  unfold rudinPoisson
  have h1 : l ^ 2 ≤ l ^ 2 + x ^ 2 := le_add_of_nonneg_right (sq_nonneg x)
  have h2 : Real.sqrt (2 / Real.pi) * l / (l ^ 2 + x ^ 2) ≤
      Real.sqrt (2 / Real.pi) * l / l ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hl) h1
  refine h2.trans_eq ?_
  field_simp [hl.ne']

theorem continuous_rudinPoisson {l : ℝ} (hl : 0 < l) : Continuous (rudinPoisson l) := by
  unfold rudinPoisson
  refine Continuous.div (by fun_prop) (by fun_prop) (fun x => ?_)
  positivity

theorem rudinPoisson_eq_cauchy {l : ℝ} (hl : 0 ≤ l) (x : ℝ) :
    rudinFactor * rudinPoisson l x = ProbabilityTheory.cauchyPDFReal 0 ⟨l, hl⟩ x := by
  let γ : ℝ≥0 := ⟨l, hl⟩
  change rudinFactor * rudinPoisson l x = ProbabilityTheory.cauchyPDFReal 0 γ x
  unfold rudinPoisson
  rw [ProbabilityTheory.cauchyPDFReal_def]
  simp only [γ, sub_zero]
  calc
    rudinFactor * (Real.sqrt (2 / Real.pi) * l / (l ^ 2 + x ^ 2))
        = (rudinFactor * Real.sqrt (2 / Real.pi)) * l * (x ^ 2 + l ^ 2)⁻¹ := by
          rw [add_comm (l ^ 2) (x ^ 2)]; ring
    _ = Real.pi⁻¹ * l * (x ^ 2 + l ^ 2)⁻¹ := by rw [rudinFactor_mul_sqrt_two_div_pi]

/-- 9.7: `h_λ ∈ L¹(m)` and `∫ h_λ(x) dm(x) = 1` for every `λ > 0`. -/
theorem theorem_9_7_poisson_integrable {l : ℝ} (hl : 0 < l) :
    Integrable (rudinPoisson l) rudinMeasure := by
  rw [rudinMeasure_eq_ofReal_smul]
  have hint := ProbabilityTheory.integrable_cauchyPDFReal 0 (γ := ⟨l, hl.le⟩)
  have heq : (fun x => rudinFactor * rudinPoisson l x) =
      ProbabilityTheory.cauchyPDFReal 0 ⟨l, hl.le⟩ := by
    ext x; exact rudinPoisson_eq_cauchy hl.le x
  rw [← heq] at hint
  have h2 : Integrable (rudinPoisson l) volume :=
    (hint.const_mul rudinFactor⁻¹).congr (ae_of_all _ fun x => by
      dsimp; rw [← mul_assoc, inv_mul_cancel₀ rudinFactor_ne_zero, one_mul])
  exact h2.smul_measure ENNReal.ofReal_ne_top

/-- 9.7: Normalization `∫_(-∞)^∞ h_λ(x) dm(x) = 1` for every `λ > 0`. -/
theorem theorem_9_7_poisson_integral_eq_one {l : ℝ} (hl : 0 < l) :
    ∫ x, rudinPoisson l x ∂rudinMeasure = 1 := by
  rw [integral_rudinMeasure, smul_eq_mul, ← integral_const_mul]
  have heq : (fun x => rudinFactor * rudinPoisson l x) =
      ProbabilityTheory.cauchyPDFReal 0 ⟨l, hl.le⟩ := by
    ext x; exact rudinPoisson_eq_cauchy hl.le x
  rw [heq]
  have hne : (⟨l, hl.le⟩ : ℝ≥0) ≠ 0 := by
    intro h
    exact hl.ne' (congr_arg Subtype.val h)
  exact ProbabilityTheory.integral_cauchyPDFReal_eq_one 0 hne

theorem rudinPoisson_scale {l : ℝ} (hl : 0 < l) (u : ℝ) :
    l * rudinPoisson l (l * u) = rudinPoisson 1 u := by
  unfold rudinPoisson
  have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl.ne'
  have h1 : l ^ 2 + (l * u) ^ 2 = l ^ 2 * (1 ^ 2 + u ^ 2) := by ring
  rw [h1]
  have hu : 1 ^ 2 + u ^ 2 ≠ 0 := by positivity
  field_simp [hl.ne', hl2, hu]

/-- 9.8: For `f ∈ L¹(m)` and `λ > 0`, `(f * h_λ)(x) = ∫ H(λ t) f̂(t) e^(i x t) dm(t)`. -/
theorem theorem_9_8 {f : ℝ → ℂ} (hf : Integrable f rudinMeasure) {l : ℝ} (hl : 0 < l) (x : ℝ) :
    rudinConv f (fun y => (rudinPoisson l y : ℂ)) x =
      ∫ t, (rudinH (l * t) : ℂ) * rudinFourier f t * Complex.exp (Complex.I * x * t)
        ∂rudinMeasure := by
  let Φ : ℝ × ℝ → ℂ := fun p =>
    f (x - p.1) * ((rudinH (l * p.2) : ℂ) * Complex.exp (Complex.I * p.2 * p.1))
  have hf_sub : Integrable (fun y : ℝ => f (x - y)) rudinMeasure :=
    (rudinMeasure.measurePreserving_sub_left x).integrable_comp_of_integrable hf
  have hH_int : Integrable (fun t : ℝ => rudinH (l * t)) rudinMeasure :=
    rudinH_scaled_integrable hl
  have hΦ_meas : AEStronglyMeasurable Φ (rudinMeasure.prod rudinMeasure) := by
    have hm1 : AEStronglyMeasurable (fun p : ℝ × ℝ => f (x - p.1))
        (rudinMeasure.prod rudinMeasure) := hf_sub.aestronglyMeasurable.comp_fst
    have hm2 : Continuous (fun p : ℝ × ℝ =>
        (rudinH (l * p.2) : ℂ) * Complex.exp (Complex.I * p.2 * p.1)) := by
      have hcH : Continuous (fun p : ℝ × ℝ => (rudinH (l * p.2) : ℂ)) :=
        Complex.continuous_ofReal.comp (continuous_rudinH.comp (continuous_const.mul continuous_snd))
      exact hcH.mul (by fun_prop)
    exact hm1.mul hm2.aestronglyMeasurable
  have hΦ_int : Integrable Φ (rudinMeasure.prod rudinMeasure) := by
    have hdom : Integrable (fun p : ℝ × ℝ => ‖f (x - p.1)‖ * rudinH (l * p.2))
        (rudinMeasure.prod rudinMeasure) := hf_sub.norm.mul_prod hH_int
    refine hdom.mono' hΦ_meas (ae_of_all _ fun p => ?_)
    dsimp [Φ]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (theorem_9_7_H_bounds _).1.le,
      norm_exp_I_mul_mul, mul_one]
  calc
    rudinConv f (fun y => (rudinPoisson l y : ℂ)) x
        = ∫ y, f (x - y) * rudinPoissonInt l y ∂rudinMeasure := by
          unfold rudinConv
          congr 1 with y
          rw [theorem_9_7_poisson_formula hl y]
    _ = ∫ y, ∫ t, Φ (y, t) ∂rudinMeasure ∂rudinMeasure := by
          congr 1 with y
          unfold rudinPoissonInt
          rw [← integral_const_mul]
    _ = ∫ t, ∫ y, Φ (y, t) ∂rudinMeasure ∂rudinMeasure := integral_integral_swap hΦ_int
    _ = ∫ t, (rudinH (l * t) : ℂ) * rudinFourier f t * Complex.exp (Complex.I * x * t)
          ∂rudinMeasure := by
          congr 1 with t
          have hpull : (fun y : ℝ => Φ (y, t)) =
              fun y : ℝ => (rudinH (l * t) : ℂ) *
                (f (x - y) * Complex.exp (Complex.I * t * y)) := by
            ext y; dsimp [Φ]; ring
          simp_rw [hpull]
          rw [integral_const_mul]
          have hsub := integral_sub_left_eq_self
            (fun u : ℝ => f u * Complex.exp (Complex.I * t * ((x : ℂ) - u))) rudinMeasure x
          have hsub' : (fun y : ℝ => f (x - y) * Complex.exp (Complex.I * t * ((x : ℂ) - ↑(x - y)))) =
              fun y : ℝ => f (x - y) * Complex.exp (Complex.I * t * y) := by
            ext y
            congr 2
            push_cast
            ring
          rw [hsub'] at hsub
          rw [hsub]
          have hexp : (fun u : ℝ => f u * Complex.exp (Complex.I * t * ((x : ℂ) - u))) =
              fun u : ℝ => Complex.exp (Complex.I * x * t) *
                (f u * Complex.exp (-Complex.I * u * t)) := by
            ext u
            have h1 : Complex.I * (t : ℂ) * ((x : ℂ) - u) =
                (Complex.I * x * t) + (-Complex.I * u * t) := by
              ring
            rw [h1, Complex.exp_add]
            ring
          simp_rw [hexp]
          rw [integral_const_mul]
          unfold rudinFourier
          ring

/-- 9.5: Pointwise translation `(rudinTranslate y f)(x) = f_y(x) = f(x - y)`. -/
def rudinTranslate (y : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := f (x - y)

/-- 9.5: Isometric translation operator `f ↦ f_y` (`f_y(x) = f(x - y)`) on `L^p(m)`. -/
def rudinTranslateLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (y : ℝ) : RudinLp p ≃ₗᵢ[ℂ] RudinLp p :=
  LinearIsometryEquiv.ofLinearIsometry
    (Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x - y) (measurePreserving_sub_right rudinMeasure y))
    (Lp.compMeasurePreservingₗ ℂ (fun x : ℝ => x - (-y)) (measurePreserving_sub_right rudinMeasure (-y)))
    (by
      ext f : 1
      change Lp.compMeasurePreserving (fun x : ℝ => x - y) (measurePreserving_sub_right rudinMeasure y)
        (Lp.compMeasurePreserving (fun x : ℝ => x - -y)
          (measurePreserving_sub_right rudinMeasure (-y)) f) = f
      rw [← Lp.compMeasurePreserving_comp_apply]
      have hid : ((fun x : ℝ => x - -y) ∘ fun x : ℝ => x - y) = id := by ext x; simp
      simp_rw [hid]
      exact Lp.compMeasurePreserving_id_apply f)
    (by
      ext f : 1
      change Lp.compMeasurePreserving (fun x : ℝ => x - -y)
        (measurePreserving_sub_right rudinMeasure (-y))
        (Lp.compMeasurePreserving (fun x : ℝ => x - y)
          (measurePreserving_sub_right rudinMeasure y) f) = f
      rw [← Lp.compMeasurePreserving_comp_apply]
      have hid : ((fun x : ℝ => x - y) ∘ fun x : ℝ => x - -y) = id := by ext x; simp
      simp_rw [hid]
      exact Lp.compMeasurePreserving_id_apply f)

theorem rudinTranslateLp_coeFn (p : ℝ≥0∞) [Fact (1 ≤ p)] (y : ℝ) (f : RudinLp p) :
    (rudinTranslateLp p y f : ℝ → ℂ) =ᵐ[rudinMeasure] rudinTranslate y f :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right rudinMeasure y)

@[simp]
theorem rudinTranslateLp_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : RudinLp p) :
    rudinTranslateLp p 0 f = f := by
  change Lp.compMeasurePreserving (fun x : ℝ => x - 0)
    (measurePreserving_sub_right rudinMeasure 0) f = f
  have hid : (fun x : ℝ => x - 0) = id := by ext x; simp
  simp_rw [hid]
  exact Lp.compMeasurePreserving_id_apply f

theorem rudinTranslateLp_add (p : ℝ≥0∞) [Fact (1 ≤ p)] (y₁ y₂ : ℝ) (f : RudinLp p) :
    rudinTranslateLp p (y₁ + y₂) f = rudinTranslateLp p y₁ (rudinTranslateLp p y₂ f) := by
  change Lp.compMeasurePreserving (fun x : ℝ => x - (y₁ + y₂))
    (measurePreserving_sub_right rudinMeasure (y₁ + y₂)) f =
    Lp.compMeasurePreserving (fun x : ℝ => x - y₁) (measurePreserving_sub_right rudinMeasure y₁)
      (Lp.compMeasurePreserving (fun x : ℝ => x - y₂)
        (measurePreserving_sub_right rudinMeasure y₂) f)
  rw [← Lp.compMeasurePreserving_comp_apply]
  have heq : (fun x : ℝ => x - (y₁ + y₂)) = ((fun x : ℝ => x - y₂) ∘ fun x : ℝ => x - y₁) := by
    ext x; dsimp; ring
  simp_rw [heq]

/-- 9.5: If `1 ≤ p < ∞` and `f ∈ L^p(m)`, then `y ↦ f_y` is uniformly continuous from `ℝ`
into `L^p(m)`. -/
theorem theorem_9_5 (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (f : RudinLp p) :
    UniformContinuous (fun y : ℝ => rudinTranslateLp p y f) := by
  let g : C(ℝ, C(ℝ, ℝ)) :=
    (ContinuousMap.mk (fun a : ℝ × ℝ => a.2 - a.1) (continuous_snd.sub continuous_fst)).curry
  have hcont : Continuous (fun y : ℝ => rudinTranslateLp p y f) :=
    continuous_const.compMeasurePreservingLp g.continuous
      (fun y => measurePreserving_sub_right rudinMeasure y) hp
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hc0 : ContinuousAt (fun y : ℝ => rudinTranslateLp p y f) 0 := hcont.continuousAt
  rw [Metric.continuousAt_iff] at hc0
  obtain ⟨δ, hδ, hball⟩ := hc0 ε hε
  refine ⟨δ, hδ, fun {y₁ y₂} hdist => ?_⟩
  have hsub_dist : dist (y₁ - y₂) 0 < δ := by
    simpa [Real.dist_eq, sub_zero] using hdist
  have h0 := hball hsub_dist
  rw [rudinTranslateLp_zero, dist_eq_norm] at h0
  rw [dist_eq_norm]
  have hisom : rudinTranslateLp p y₁ f - rudinTranslateLp p y₂ f =
      rudinTranslateLp p y₂ (rudinTranslateLp p (y₁ - y₂) f - f) := by
    rw [map_sub, ← rudinTranslateLp_add, add_sub_cancel]
  rw [hisom, LinearIsometryEquiv.norm_map]
  exact h0

private lemma quasiMeasurePreserving_affine_sub {l : ℝ} (hl : 0 < l) (x : ℝ) :
    Measure.QuasiMeasurePreserving (fun u : ℝ => x - l * u) rudinMeasure rudinMeasure := by
  have h1 : Measure.QuasiMeasurePreserving (fun v : ℝ => x - v) rudinMeasure rudinMeasure :=
    (rudinMeasure.measurePreserving_sub_left x).quasiMeasurePreserving
  have h2 : Measure.QuasiMeasurePreserving (fun u : ℝ => l * u) rudinMeasure rudinMeasure := by
    refine ⟨by fun_prop, Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_⟩
    rw [Measure.map_apply (by fun_prop) hs, rudinMeasure_apply]
    rw [rudinMeasure_apply] at hzero
    have hv : volume s = 0 :=
      (mul_eq_zero.mp hzero).resolve_left (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hmap := Real.map_volume_mul_left hl.ne'
    have hpre : volume ((fun u : ℝ => l * u) ⁻¹' s) =
        (ENNReal.ofReal |l⁻¹| • (volume : Measure ℝ)) s := by
      rw [← hmap, Measure.map_apply (by fun_prop) hs]
    simp [hpre, hv]
  exact h1.comp h2

/-- 9.9: If `g ∈ L^∞(m)` (essential boundedness, not global pointwise boundedness) and `g` is
continuous at a point `x`, then `(g * h_λ)(x)` exists for all `λ > 0` and converges to `g(x)`
as `λ ↓ 0`. -/
theorem theorem_9_9 {g : ℝ → ℂ} (hg : MemLp g ∞ rudinMeasure) {x : ℝ}
    (hcont : ContinuousAt g x) :
    (∀ l : ℝ, 0 < l → Integrable (fun y : ℝ => g (x - y) * (rudinPoisson l y : ℂ)) rudinMeasure) ∧
      Tendsto (fun l : ℝ => rudinConv g (fun y => (rudinPoisson l y : ℂ)) x)
        (𝓝[>] 0) (𝓝 (g x)) := by
  have hg_ae : ∀ᵐ z ∂rudinMeasure, ‖g z‖ ≤ rudinLinftyNorm g := by
    have h1 : ∀ᵐ z ∂rudinMeasure, ‖g z‖ₑ ≤ eLpNorm g ∞ rudinMeasure := by
      simp only [eLpNorm, hg.aestronglyMeasurable, ↓reduceIte, ENNReal.top_ne_zero]
      exact ae_le_eLpNormEssSup
    filter_upwards [h1] with z hz
    rw [rudinLinftyNorm]
    have hfin : eLpNorm g ∞ rudinMeasure ≠ ∞ := hg.eLpNorm_lt_top.ne
    exact (ENNReal.toReal_le_toReal (enorm_ne_top) hfin).mpr hz
  have hint : ∀ l : ℝ, 0 < l →
      Integrable (fun y : ℝ => g (x - y) * (rudinPoisson l y : ℂ)) rudinMeasure := by
    intro l hl
    have hg_sub : MemLp (fun y : ℝ => g (x - y)) ∞ rudinMeasure :=
      hg.comp_measurePreserving (rudinMeasure.measurePreserving_sub_left x)
    have hP : MemLp (fun y : ℝ => (rudinPoisson l y : ℂ)) 1 rudinMeasure :=
      memLp_one_iff_integrable.mpr ((theorem_9_7_poisson_integrable hl).ofReal)
    exact memLp_one_iff_integrable.mp ((hP.mul hg_sub).ae_eq
      (ae_of_all _ fun y => mul_comm _ _))
  refine ⟨hint, ?_⟩
  have hrescale : ∀ l : ℝ, 0 < l →
      rudinConv g (fun y => (rudinPoisson l y : ℂ)) x - g x =
        ∫ u, (g (x - l * u) - g x) * (rudinPoisson 1 u : ℂ) ∂rudinMeasure := by
    intro l hl
    have hmass : ∫ y, g x * (rudinPoisson l y : ℂ) ∂rudinMeasure = g x := by
      rw [integral_const_mul, integral_complex_ofReal, theorem_9_7_poisson_integral_eq_one hl,
        Complex.ofReal_one, mul_one]
    have hconst_int : Integrable (fun y : ℝ => g x * (rudinPoisson l y : ℂ)) rudinMeasure :=
      ((theorem_9_7_poisson_integrable hl).ofReal).const_mul (g x)
    calc
      rudinConv g (fun y => (rudinPoisson l y : ℂ)) x - g x
          = ∫ y, g (x - y) * (rudinPoisson l y : ℂ) ∂rudinMeasure -
              ∫ y, g x * (rudinPoisson l y : ℂ) ∂rudinMeasure := by
            unfold rudinConv; rw [hmass]
      _ = ∫ y, (g (x - y) - g x) * (rudinPoisson l y : ℂ) ∂rudinMeasure := by
            rw [← integral_sub (hint l hl) hconst_int]
            congr 1 with y; ring
      _ = ∫ u, (g (x - l * u) - g x) * (rudinPoisson 1 u : ℂ) ∂rudinMeasure := by
            rw [integral_rudinMeasure, integral_rudinMeasure]
            congr 1
            let ψ : ℝ → ℂ := fun u =>
              (g (x - l * u) - g x) * (rudinPoisson l (l * u) : ℂ)
            have hcomp := Measure.integral_comp_mul_left ψ l⁻¹
            have hl_inv_pos : 0 < l⁻¹ := inv_pos.mpr hl
            rw [inv_inv, abs_of_pos hl, Complex.real_smul] at hcomp
            have hψ : (fun y : ℝ => ψ (l⁻¹ * y)) =
                fun y : ℝ => (g (x - y) - g x) * (rudinPoisson l y : ℂ) := by
              ext y
              dsimp [ψ]
              rw [mul_inv_cancel_left₀ hl.ne' y]
            rw [hψ] at hcomp
            rw [hcomp, ← integral_const_mul]
            congr 1 with u
            dsimp [ψ]
            have hsc : (l : ℂ) * (rudinPoisson l (l * u) : ℂ) = (rudinPoisson 1 u : ℂ) := by
              exact_mod_cast rudinPoisson_scale hl u
            calc
              (l : ℂ) * ((g (x - l * u) - g x) * (rudinPoisson l (l * u) : ℂ))
                  = (g (x - l * u) - g x) * ((l : ℂ) * (rudinPoisson l (l * u) : ℂ)) := by ring
              _ = (g (x - l * u) - g x) * (rudinPoisson 1 u : ℂ) := by rw [hsc]
  let F : ℝ → ℝ → ℂ := fun l u => (g (x - l * u) - g x) * (rudinPoisson 1 u : ℂ)
  let bound : ℝ → ℝ := fun u => (rudinLinftyNorm g + ‖g x‖) * rudinPoisson 1 u
  have hF_meas : ∀ᶠ l in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (F l) rudinMeasure := by
    filter_upwards [self_mem_nhdsWithin] with l (hl : 0 < l)
    have hqmp := quasiMeasurePreserving_affine_sub hl x
    have hm1 : AEStronglyMeasurable (fun u => g (x - l * u)) rudinMeasure :=
      hg.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
    have hm2 : Continuous (fun u : ℝ => (rudinPoisson 1 u : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_rudinPoisson one_pos)
    exact (hm1.sub aestronglyMeasurable_const).mul hm2.aestronglyMeasurable
  have hF_bound : ∀ᶠ l in 𝓝[>] (0 : ℝ), ∀ᵐ u ∂rudinMeasure, ‖F l u‖ ≤ bound u := by
    filter_upwards [self_mem_nhdsWithin] with l (hl : 0 < l)
    have hqmp := quasiMeasurePreserving_affine_sub hl x
    filter_upwards [hqmp.ae hg_ae] with u hu
    dsimp [F, bound]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (rudinPoisson_pos one_pos u).le]
    exact mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add hu le_rfl))
      (rudinPoisson_pos one_pos u).le
  have hbound_int : Integrable bound rudinMeasure :=
    (theorem_9_7_poisson_integrable one_pos).const_mul (rudinLinftyNorm g + ‖g x‖)
  have hF_lim : ∀ᵐ u ∂rudinMeasure, Tendsto (fun l => F l u) (𝓝[>] 0) (𝓝 0) := by
    refine ae_of_all _ fun u => ?_
    have hlin : Tendsto (fun l : ℝ => x - l * u) (𝓝[>] 0) (𝓝 x) := by
      have hc : Continuous (fun l : ℝ => x - l * u) := by fun_prop
      have h0 : x - (0 : ℝ) * u = x := by ring
      simpa only [h0] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    have hg_tendsto : Tendsto (fun l : ℝ => g (x - l * u) - g x) (𝓝[>] 0) (𝓝 0) := by
      simpa [sub_self] using (hcont.tendsto.comp hlin).sub (tendsto_const_nhds (x := g x))
    simpa [F, zero_mul] using hg_tendsto.mul_const (rudinPoisson 1 u : ℂ)
  have hdct := tendsto_integral_filter_of_dominated_convergence bound hF_meas hF_bound
    hbound_int hF_lim
  simp only [integral_zero] at hdct
  have hsub_tendsto :
      Tendsto (fun l : ℝ => rudinConv g (fun y => (rudinPoisson l y : ℂ)) x - g x)
        (𝓝[>] 0) (𝓝 0) :=
    hdct.congr' (by filter_upwards [self_mem_nhdsWithin] with l hl; exact (hrescale l hl).symm)
  simpa using hsub_tendsto.add (tendsto_const_nhds (x := g x))

private lemma rudinPoisson_memLp {l : ℝ} (hl : 0 < l) (q : ℝ≥0∞) (hq : 1 ≤ q) :
    MemLp (fun y : ℝ => (rudinPoisson l y : ℂ)) q rudinMeasure := by
  let M : ℝ := Real.sqrt (2 / Real.pi) / l
  have hM_nonneg : 0 ≤ M := by dsimp [M]; positivity
  have hbound : ∀ y : ℝ, ‖(rudinPoisson l y : ℂ)‖ ≤ M := by
    intro y
    rw [Complex.norm_real, Real.norm_of_nonneg (rudinPoisson_pos hl y).le]
    exact rudinPoisson_le hl y
  have hmeas : AEStronglyMeasurable (fun y : ℝ => (rudinPoisson l y : ℂ)) rudinMeasure :=
    (Complex.continuous_ofReal.comp (continuous_rudinPoisson hl)).aestronglyMeasurable
  by_cases hqtop : q = ∞
  · rw [hqtop]
    exact memLp_top_of_bound hmeas M (ae_of_all _ hbound)
  · have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
    rw [← integrable_norm_rpow_iff hmeas hq0 hqtop]
    have hq1 : 1 ≤ q.toReal := by
      simpa using (ENNReal.toReal_le_toReal ENNReal.one_ne_top hqtop).mpr hq
    have hexp_nonneg : 0 ≤ q.toReal - 1 := sub_nonneg.mpr hq1
    have hdom : Integrable (fun y : ℝ => M ^ (q.toReal - 1) * rudinPoisson l y) rudinMeasure :=
      (theorem_9_7_poisson_integrable hl).const_mul (M ^ (q.toReal - 1))
    refine hdom.mono' (by
      have hc : Continuous (fun y : ℝ => ‖(rudinPoisson l y : ℂ)‖ ^ q.toReal) :=
        ((Complex.continuous_ofReal.comp (continuous_rudinPoisson hl)).norm).rpow_const
          (fun _ => Or.inr (zero_le_one.trans hq1))
      exact hc.aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    dsimp
    have hy_pos : 0 < rudinPoisson l y := rudinPoisson_pos hl y
    have hnorm_eq : ‖(rudinPoisson l y : ℂ)‖ = rudinPoisson l y := by
      rw [Complex.norm_real, Real.norm_of_nonneg hy_pos.le]
    rw [hnorm_eq, abs_of_nonneg (Real.rpow_nonneg hy_pos.le _)]
    calc
      rudinPoisson l y ^ q.toReal
          = rudinPoisson l y ^ (q.toReal - 1 + 1) := by ring_nf
      _ = rudinPoisson l y ^ (q.toReal - 1) * rudinPoisson l y := by
            rw [Real.rpow_add hy_pos, Real.rpow_one]
      _ ≤ M ^ (q.toReal - 1) * rudinPoisson l y :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow hy_pos.le (rudinPoisson_le hl y) hexp_nonneg) hy_pos.le

/-- 9.10 (pointwise existence via conjugate-exponent Hölder): For `1 ≤ p` (including `p < ∞`)
and `f ∈ L^p(m)`, the Poisson convolution integrand `y ↦ f(x - y) h_λ(y)` is integrable on `(ℝ, m)`
at every `x ∈ ℝ` and for every `λ > 0`. -/
theorem theorem_9_10_exists (p : ℝ≥0∞) [Fact (1 ≤ p)] {f : ℝ → ℂ}
    (hf : MemLp f p rudinMeasure) {l : ℝ} (hl : 0 < l) (x : ℝ) :
    Integrable (fun y : ℝ => f (x - y) * (rudinPoisson l y : ℂ)) rudinMeasure := by
  have hp1 : 1 ≤ p := Fact.out
  let q : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  have hp_inv_le : p⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hp1
  have hconj : ENNReal.HolderConjugate p q :=
    ⟨by rw [inv_inv, add_tsub_cancel_of_le hp_inv_le, inv_one]⟩
  have hconj_symm : ENNReal.HolderConjugate q p := @ENNReal.HolderConjugate.symm p q hconj
  have hq1 : 1 ≤ q := @ENNReal.HolderConjugate.one_le q p hconj_symm
  have hf_sub : MemLp (fun y : ℝ => f (x - y)) p rudinMeasure :=
    hf.comp_measurePreserving (rudinMeasure.measurePreserving_sub_left x)
  have hP_q : MemLp (fun y : ℝ => (rudinPoisson l y : ℂ)) q rudinMeasure :=
    rudinPoisson_memLp hl q hq1
  exact memLp_one_iff_integrable.mp (hf_sub.mul hP_q (hpqr := hconj))

/-- 9.10 (`L^p` membership and norm bound): For `1 ≤ p < ∞`, `f ∈ L^p(m)`, and `λ > 0`,
`f * h_λ ∈ L^p(m)` and `‖f * h_λ - f‖_p^(p.toReal) ≤ ∫ ‖f_y - f‖_p^(p.toReal) h_λ(y) dm(y)`. -/
theorem theorem_9_10_memLp_and_bound (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f : RudinLp p) {l : ℝ} (hl : 0 < l) :
    ∃ hconv : MemLp (rudinConv f (fun y => (rudinPoisson l y : ℂ))) p rudinMeasure,
      ‖hconv.toLp (rudinConv f (fun y => (rudinPoisson l y : ℂ))) - f‖ ^ p.toReal ≤
        ∫ y, ‖rudinTranslateLp p y f - f‖ ^ p.toReal * rudinPoisson l y ∂rudinMeasure := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  let r : ℝ := p.toReal
  have hr1 : 1 ≤ r := by simpa [r] using (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp).mpr hp1
  have hr_pos : 0 < r := zero_lt_one.trans_le hr1
  let F : ℝ → ℂ := (Lp.aestronglyMeasurable f).mk f
  have hF_meas : StronglyMeasurable F := (Lp.aestronglyMeasurable f).stronglyMeasurable_mk
  have hF_ae : (f : ℝ → ℂ) =ᵐ[rudinMeasure] F := (Lp.aestronglyMeasurable f).ae_eq_mk
  have hF_lp : MemLp F p rudinMeasure := (Lp.memLp f).ae_eq hF_ae
  have hconv_eq : ∀ x : ℝ,
      rudinConv f (fun y => (rudinPoisson l y : ℂ)) x =
        rudinConv F (fun y => (rudinPoisson l y : ℂ)) x := by
    intro x
    unfold rudinConv
    apply integral_congr_ae
    have hsub_ae := (rudinMeasure.measurePreserving_sub_left x).quasiMeasurePreserving.ae hF_ae
    filter_upwards [hsub_ae] with y hy
    rw [hy]
  let hNN : ℝ → ℝ≥0 := fun y => ⟨rudinPoisson l y, (rudinPoisson_pos hl y).le⟩
  have hhNN_coe : ∀ y : ℝ, (hNN y : ℝ) = rudinPoisson l y := fun _ => rfl
  have hhNN_meas : Measurable hNN := (continuous_rudinPoisson hl).measurable.subtype_mk
  let ν : Measure ℝ := rudinMeasure.withDensity (fun y => (hNN y : ℝ≥0∞))
  have hν_prob : IsProbabilityMeasure ν := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have h1 := theorem_9_7_poisson_integral_eq_one hl
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun y => (rudinPoisson_pos hl y).le)
      (theorem_9_7_poisson_integrable hl).aestronglyMeasurable] at h1
    have h2 : (∫⁻ y, (hNN y : ℝ≥0∞) ∂rudinMeasure) =
        ∫⁻ y, ENNReal.ofReal (rudinPoisson l y) ∂rudinMeasure := by
      apply lintegral_congr
      intro y
      rw [ENNReal.ofReal_eq_coe_nnreal (rudinPoisson_pos hl y).le]
      rfl
    rw [h2, ← ENNReal.toReal_eq_one_iff]
    exact h1
  have hjensen : ∀ x : ℝ,
      ‖rudinConv F (fun y => (rudinPoisson l y : ℂ)) x - F x‖ ^ r ≤
        ∫ y, ‖F (x - y) - F x‖ ^ r * rudinPoisson l y ∂rudinMeasure := by
    intro x
    have hint_F_sub : Integrable (fun y : ℝ => F (x - y) * (rudinPoisson l y : ℂ)) rudinMeasure :=
      theorem_9_10_exists p hF_lp hl x
    have hint_Fx : Integrable (fun y : ℝ => F x * (rudinPoisson l y : ℂ)) rudinMeasure :=
      ((theorem_9_7_poisson_integrable hl).ofReal).const_mul (F x)
    have hint_diff_C : Integrable (fun y : ℝ => (F (x - y) - F x) * (rudinPoisson l y : ℂ))
        rudinMeasure :=
      (hint_F_sub.sub hint_Fx).congr (ae_of_all _ fun y => by dsimp; ring)
    have hdiff_eq : rudinConv F (fun y => (rudinPoisson l y : ℂ)) x - F x =
        ∫ y, F (x - y) - F x ∂ν := by
      have hmass : ∫ y, F x * (rudinPoisson l y : ℂ) ∂rudinMeasure = F x := by
        rw [integral_const_mul, integral_complex_ofReal, theorem_9_7_poisson_integral_eq_one hl,
          Complex.ofReal_one, mul_one]
      calc
        rudinConv F (fun y => (rudinPoisson l y : ℂ)) x - F x
            = ∫ y, F (x - y) * (rudinPoisson l y : ℂ) ∂rudinMeasure -
                ∫ y, F x * (rudinPoisson l y : ℂ) ∂rudinMeasure := by
              unfold rudinConv; rw [hmass]
        _ = ∫ y, (F (x - y) - F x) * (rudinPoisson l y : ℂ) ∂rudinMeasure := by
              rw [← integral_sub hint_F_sub hint_Fx]
              congr 1 with y; ring
        _ = ∫ y, hNN y • (F (x - y) - F x) ∂rudinMeasure := by
              congr 1 with y
              rw [NNReal.smul_def, hhNN_coe y, Complex.real_smul, mul_comm]
        _ = ∫ y, F (x - y) - F x ∂ν :=
              (integral_withDensity_eq_integral_smul hhNN_meas _).symm
    have hint_norm_ν : Integrable (fun y : ℝ => ‖F (x - y) - F x‖) ν := by
      rw [integrable_withDensity_iff_integrable_coe_smul hhNN_meas]
      refine hint_diff_C.norm.congr (ae_of_all _ fun y => ?_)
      dsimp only
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (rudinPoisson_pos hl y).le,
        hhNN_coe y, smul_eq_mul, mul_comm]
    have hint_rpow_m : Integrable (fun y : ℝ => ‖F (x - y) - F x‖ ^ r * rudinPoisson l y)
        rudinMeasure := by
      have hF_sub_r : Integrable (fun y : ℝ => ‖F (x - y)‖ ^ r) rudinMeasure := by
        have hF_sub : MemLp (fun y : ℝ => F (x - y)) p rudinMeasure :=
          hF_lp.comp_measurePreserving (rudinMeasure.measurePreserving_sub_left x)
        exact (integrable_norm_rpow_iff hF_sub.aestronglyMeasurable hp0 hp).mpr hF_sub
      let M : ℝ := Real.sqrt (2 / Real.pi) / l
      have hdom : Integrable
          (fun y : ℝ => (2 : ℝ) ^ r * (‖F (x - y)‖ ^ r * M + ‖F x‖ ^ r * rudinPoisson l y))
          rudinMeasure := by
        refine Integrable.const_mul ?_ ((2 : ℝ) ^ r)
        exact (hF_sub_r.mul_const M).add
          ((theorem_9_7_poisson_integrable hl).const_mul (‖F x‖ ^ r))
      have hm_rpow : Measurable (fun y : ℝ => ‖F (x - y) - F x‖ ^ r * rudinPoisson l y) := by
        have hmF : Measurable (fun y : ℝ => F (x - y) - F x) :=
          (hF_meas.measurable.comp (measurable_const.sub measurable_id)).sub measurable_const
        exact (hmF.norm.pow_const r).mul (continuous_rudinPoisson hl).measurable
      refine hdom.mono' hm_rpow.aestronglyMeasurable (ae_of_all _ fun y => ?_)
      dsimp
      have hP_pos : 0 ≤ rudinPoisson l y := (rudinPoisson_pos hl y).le
      rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hP_pos)]
      have htri : ‖F (x - y) - F x‖ ≤ 2 * max ‖F (x - y)‖ ‖F x‖ := by
        calc
          ‖F (x - y) - F x‖ ≤ ‖F (x - y)‖ + ‖F x‖ := norm_sub_le _ _
          _ ≤ max ‖F (x - y)‖ ‖F x‖ + max ‖F (x - y)‖ ‖F x‖ :=
            add_le_add (le_max_left _ _) (le_max_right _ _)
          _ = 2 * max ‖F (x - y)‖ ‖F x‖ := by ring
      have hrpow_le : ‖F (x - y) - F x‖ ^ r ≤ (2 : ℝ) ^ r * (‖F (x - y)‖ ^ r + ‖F x‖ ^ r) := by
        calc
          ‖F (x - y) - F x‖ ^ r
              ≤ (2 * max ‖F (x - y)‖ ‖F x‖) ^ r :=
                Real.rpow_le_rpow (norm_nonneg _) htri hr_pos.le
          _ = (2 : ℝ) ^ r * (max ‖F (x - y)‖ ‖F x‖) ^ r :=
                Real.mul_rpow (by positivity) (le_trans (norm_nonneg _) (le_max_left _ _))
          _ ≤ (2 : ℝ) ^ r * (‖F (x - y)‖ ^ r + ‖F x‖ ^ r) := by
                gcongr
                rcases max_cases ‖F (x - y)‖ ‖F x‖ with ⟨hmax, _⟩ | ⟨hmax, _⟩
                · rw [hmax]; exact le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _)
                · rw [hmax]; exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)
      calc
        ‖F (x - y) - F x‖ ^ r * rudinPoisson l y
            ≤ ((2 : ℝ) ^ r * (‖F (x - y)‖ ^ r + ‖F x‖ ^ r)) * rudinPoisson l y :=
              mul_le_mul_of_nonneg_right hrpow_le hP_pos
        _ = (2 : ℝ) ^ r * (‖F (x - y)‖ ^ r * rudinPoisson l y + ‖F x‖ ^ r * rudinPoisson l y) := by
              ring
        _ ≤ (2 : ℝ) ^ r * (‖F (x - y)‖ ^ r * M + ‖F x‖ ^ r * rudinPoisson l y) := by
              gcongr
              exact rudinPoisson_le hl y
    have hint_rpow_ν : Integrable ((fun u : ℝ => u ^ r) ∘ fun y : ℝ => ‖F (x - y) - F x‖) ν := by
      rw [integrable_withDensity_iff_integrable_coe_smul hhNN_meas]
      refine hint_rpow_m.congr (ae_of_all _ fun y => ?_)
      dsimp only [Function.comp_apply]
      rw [hhNN_coe y, smul_eq_mul, mul_comm]
    calc
      ‖rudinConv F (fun y => (rudinPoisson l y : ℂ)) x - F x‖ ^ r
          = ‖∫ y, F (x - y) - F x ∂ν‖ ^ r := by rw [hdiff_eq]
      _ ≤ (∫ y, ‖F (x - y) - F x‖ ∂ν) ^ r :=
            Real.rpow_le_rpow (norm_nonneg _) (norm_integral_le_integral_norm _) hr_pos.le
      _ ≤ ∫ y, ‖F (x - y) - F x‖ ^ r ∂ν := by
            exact (convexOn_rpow hr1).map_integral_le
              (continuousOn_id.rpow_const fun _ _ => Or.inr hr_pos.le)
              isClosed_Ici (ae_of_all _ fun y => norm_nonneg _) hint_norm_ν hint_rpow_ν
      _ = ∫ y, ‖F (x - y) - F x‖ ^ r * rudinPoisson l y ∂rudinMeasure := by
            rw [integral_withDensity_eq_integral_smul hhNN_meas]
            congr 1 with y
            rw [NNReal.smul_def, hhNN_coe y, smul_eq_mul, mul_comm]
  have hshift_lintegral : ∀ y : ℝ,
      (∫⁻ x, ENNReal.ofReal (‖F (x - y) - F x‖ ^ r) ∂rudinMeasure) =
        ENNReal.ofReal (‖rudinTranslateLp p y f - f‖ ^ r) := by
    intro y
    have hdiff_ae : (((rudinTranslateLp p y f - f : RudinLp p) : ℝ → ℂ)) =ᵐ[rudinMeasure]
        fun x => F (x - y) - F x := by
      have hsub_ae := (measurePreserving_sub_right rudinMeasure y).quasiMeasurePreserving.ae hF_ae
      filter_upwards [Lp.coeFn_sub (rudinTranslateLp p y f) f,
        rudinTranslateLp_coeFn p y f, hsub_ae, hF_ae] with x hx1 hx2 hx3 hx4
      rw [hx1, Pi.sub_apply, hx2, rudinTranslate, hx3, hx4]
    have hlp : MemLp (fun x => F (x - y) - F x) p rudinMeasure :=
      (Lp.memLp (rudinTranslateLp p y f - f)).ae_eq hdiff_ae
    have hnorm_eq : ‖rudinTranslateLp p y f - f‖ ^ r =
        (∫⁻ x, ‖F (x - y) - F x‖ₑ ^ r ∂rudinMeasure).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae hdiff_ae,
        eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hlp.aestronglyMeasurable]
      change (((∫⁻ x, ‖F (x - y) - F x‖ₑ ^ r ∂rudinMeasure) ^ (1 / r)).toReal) ^ r = _
      rw [← ENNReal.toReal_rpow, ← Real.rpow_mul ENNReal.toReal_nonneg,
        one_div_mul_cancel hr_pos.ne', Real.rpow_one]
    have hfin : (∫⁻ x, ‖F (x - y) - F x‖ₑ ^ r ∂rudinMeasure) ≠ ∞ := by
      have hint := (integrable_norm_rpow_iff hlp.aestronglyMeasurable hp0 hp).mpr hlp
      have heq : (∫⁻ x, ‖F (x - y) - F x‖ₑ ^ r ∂rudinMeasure) =
          ∫⁻ x, ‖‖F (x - y) - F x‖ ^ r‖ₑ ∂rudinMeasure := by
        apply lintegral_congr; intro x
        rw [Real.enorm_rpow_of_nonneg (norm_nonneg _) hr_pos.le, enorm_norm]
      rw [heq]
      exact hint.2.ne
    have heq : (∫⁻ x, ENNReal.ofReal (‖F (x - y) - F x‖ ^ r) ∂rudinMeasure) =
        ∫⁻ x, ‖F (x - y) - F x‖ₑ ^ r ∂rudinMeasure := by
      apply lintegral_congr; intro x
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr_pos.le, ofReal_norm]
    rw [heq, hnorm_eq, ENNReal.ofReal_toReal hfin]
  have hRHS_int : Integrable (fun y : ℝ => ‖rudinTranslateLp p y f - f‖ ^ r * rudinPoisson l y)
      rudinMeasure := by
    have hcont_y : Continuous (fun y : ℝ => ‖rudinTranslateLp p y f - f‖ ^ r) :=
      (((theorem_9_5 p hp f).continuous.sub continuous_const).norm).rpow_const
        fun _ => Or.inr hr_pos.le
    have hdom : Integrable (fun y : ℝ => (2 * ‖f‖) ^ r * rudinPoisson l y) rudinMeasure :=
      (theorem_9_7_poisson_integrable hl).const_mul ((2 * ‖f‖) ^ r)
    refine hdom.mono' (hcont_y.mul (continuous_rudinPoisson hl)).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    dsimp
    have hP_pos : 0 ≤ rudinPoisson l y := (rudinPoisson_pos hl y).le
    rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hP_pos)]
    gcongr
    calc
      ‖rudinTranslateLp p y f - f‖ ≤ ‖rudinTranslateLp p y f‖ + ‖f‖ := norm_sub_le _ _
      _ = 2 * ‖f‖ := by rw [LinearIsometryEquiv.norm_map]; ring
  have hjoint_meas : Measurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal (‖F (q.1 - q.2) - F q.1‖ ^ r * rudinPoisson l q.2)) := by
    have hm1 : Measurable (fun q : ℝ × ℝ => F (q.1 - q.2) - F q.1) :=
      (hF_meas.measurable.comp (measurable_fst.sub measurable_snd)).sub
        (hF_meas.measurable.comp measurable_fst)
    exact ENNReal.measurable_ofReal.comp
      ((hm1.norm.pow_const r).mul ((continuous_rudinPoisson hl).measurable.comp measurable_snd))
  have htonelli :
      (∫⁻ x, ENNReal.ofReal (‖rudinConv F (fun y => (rudinPoisson l y : ℂ)) x - F x‖ ^ r)
        ∂rudinMeasure) ≤
        ENNReal.ofReal (∫ y, ‖rudinTranslateLp p y f - f‖ ^ r * rudinPoisson l y ∂rudinMeasure) := by
    calc
      (∫⁻ x, ENNReal.ofReal (‖rudinConv F (fun y => (rudinPoisson l y : ℂ)) x - F x‖ ^ r)
        ∂rudinMeasure)
          ≤ ∫⁻ x, ENNReal.ofReal (∫ y, ‖F (x - y) - F x‖ ^ r * rudinPoisson l y ∂rudinMeasure)
              ∂rudinMeasure := by
            apply lintegral_mono; intro x
            exact ENNReal.ofReal_le_ofReal (hjensen x)
      _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖F (x - y) - F x‖ ^ r * rudinPoisson l y)
            ∂rudinMeasure ∂rudinMeasure := by
            apply lintegral_mono; intro x; dsimp only
            by_cases hi : Integrable (fun y => ‖F (x - y) - F x‖ ^ r * rudinPoisson l y) rudinMeasure
            · rw [ofReal_integral_eq_lintegral_ofReal hi
                (ae_of_all _ fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
                  (rudinPoisson_pos hl y).le)]
            · rw [integral_undef hi, ENNReal.ofReal_zero]; exact bot_le
      _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (‖F (x - y) - F x‖ ^ r * rudinPoisson l y)
            ∂rudinMeasure ∂rudinMeasure :=
            lintegral_lintegral_swap hjoint_meas.aemeasurable
      _ = ∫⁻ y, ENNReal.ofReal (‖rudinTranslateLp p y f - f‖ ^ r * rudinPoisson l y)
            ∂rudinMeasure := by
            apply lintegral_congr; intro y
            have hP_pos : 0 ≤ rudinPoisson l y := (rudinPoisson_pos hl y).le
            simp_rw [ENNReal.ofReal_mul' hP_pos]
            rw [lintegral_mul_const _ (by
              have hm : Measurable (fun x : ℝ => ENNReal.ofReal (‖F (x - y) - F x‖ ^ r)) :=
                ENNReal.measurable_ofReal.comp
                  (((hF_meas.measurable.comp (measurable_id.sub measurable_const)).sub
                    hF_meas.measurable).norm.pow_const r)
              exact hm), hshift_lintegral y]
      _ = ENNReal.ofReal (∫ y, ‖rudinTranslateLp p y f - f‖ ^ r * rudinPoisson l y ∂rudinMeasure) :=
            (ofReal_integral_eq_lintegral_ofReal hRHS_int
              (ae_of_all _ fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
                (rudinPoisson_pos hl y).le)).symm
  have hconv_meas : AEStronglyMeasurable (rudinConv F (fun y => (rudinPoisson l y : ℂ)))
      rudinMeasure := by
    have h1 : AEStronglyMeasurable
        (F ⋆[ContinuousLinearMap.mul ℂ ℂ, rudinMeasure] fun y => (rudinPoisson l y : ℂ))
        rudinMeasure :=
      hF_meas.aestronglyMeasurable.convolution (L := ContinuousLinearMap.mul ℂ ℂ)
        (Complex.continuous_ofReal.comp (continuous_rudinPoisson hl)).aestronglyMeasurable
    exact h1.congr (ae_of_all _ fun x => (rudinConv_eq_convolution_rudinMeasure F _ x).symm)
  have hdiff_lp : MemLp (fun x => rudinConv F (fun y => (rudinPoisson l y : ℂ)) x - F x)
      p rudinMeasure := by
    have hm : AEStronglyMeasurable
        (fun x => rudinConv F (fun y => (rudinPoisson l y : ℂ)) x - F x) rudinMeasure :=
      hconv_meas.sub hF_meas.aestronglyMeasurable
    rw [← integrable_norm_rpow_iff hm hp0 hp]
    refine ⟨(continuous_id.rpow_const fun _ => Or.inr hr_pos.le).comp_aestronglyMeasurable hm.norm,
      ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have heq : (∫⁻ x, ‖‖rudinConv F (fun y => (rudinPoisson l y : ℂ)) x - F x‖ ^ r‖ₑ
        ∂rudinMeasure) =
        ∫⁻ x, ENNReal.ofReal (‖rudinConv F (fun y => (rudinPoisson l y : ℂ)) x - F x‖ ^ r)
          ∂rudinMeasure := by
      apply lintegral_congr; intro x
      rw [← ofReal_norm, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    rw [heq]
    exact htonelli.trans_lt ENNReal.ofReal_lt_top
  have hconvF_lp : MemLp (rudinConv F (fun y => (rudinPoisson l y : ℂ))) p rudinMeasure :=
    (hdiff_lp.add hF_lp).ae_eq (ae_of_all _ fun x => sub_add_cancel _ _)
  have hconv_lp : MemLp (rudinConv f (fun y => (rudinPoisson l y : ℂ))) p rudinMeasure :=
    hconvF_lp.ae_eq (ae_of_all _ fun x => (hconv_eq x).symm)
  refine ⟨hconv_lp, ?_⟩
  have htoLp_diff_ae :
      (((hconv_lp.toLp (rudinConv f (fun y => (rudinPoisson l y : ℂ))) - f : RudinLp p) : ℝ → ℂ))
        =ᵐ[rudinMeasure]
        fun x => rudinConv F (fun y => (rudinPoisson l y : ℂ)) x - F x := by
    filter_upwards [Lp.coeFn_sub (hconv_lp.toLp _) f, hconv_lp.coeFn_toLp, hF_ae] with x hx1 hx2 hx3
    rw [hx1, Pi.sub_apply, hx2, hconv_eq x, hx3]
  have hnorm_r :
      ‖hconv_lp.toLp (rudinConv f (fun y => (rudinPoisson l y : ℂ))) - f‖ ^ r =
        (∫⁻ x, ENNReal.ofReal (‖rudinConv F (fun y => (rudinPoisson l y : ℂ)) x - F x‖ ^ r)
          ∂rudinMeasure).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae htoLp_diff_ae,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hdiff_lp.aestronglyMeasurable]
    change (((∫⁻ x, ‖rudinConv F (fun y => (rudinPoisson l y : ℂ)) x - F x‖ₑ ^ r
      ∂rudinMeasure) ^ (1 / r)).toReal) ^ r = _
    rw [← ENNReal.toReal_rpow, ← Real.rpow_mul ENNReal.toReal_nonneg,
      one_div_mul_cancel hr_pos.ne', Real.rpow_one]
    congr 1
    apply lintegral_congr; intro x
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr_pos.le, ofReal_norm]
  rw [hnorm_r]
  have hRHS_nonneg : 0 ≤ ∫ y, ‖rudinTranslateLp p y f - f‖ ^ r * rudinPoisson l y ∂rudinMeasure :=
    integral_nonneg fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (rudinPoisson_pos hl y).le
  calc
    (∫⁻ x, ENNReal.ofReal (‖rudinConv F (fun y => (rudinPoisson l y : ℂ)) x - F x‖ ^ r)
      ∂rudinMeasure).toReal
        ≤ (ENNReal.ofReal
            (∫ y, ‖rudinTranslateLp p y f - f‖ ^ r * rudinPoisson l y ∂rudinMeasure)).toReal :=
          (ENNReal.toReal_le_toReal (htonelli.trans_lt ENNReal.ofReal_lt_top).ne
            ENNReal.ofReal_ne_top).mpr htonelli
    _ = ∫ y, ‖rudinTranslateLp p y f - f‖ ^ r * rudinPoisson l y ∂rudinMeasure :=
          ENNReal.toReal_ofReal hRHS_nonneg

/-- 9.10: For `1 ≤ p < ∞` and `f ∈ L^p(m)`, `f * h_λ ∈ L^p(m)` for every `λ > 0` and
`‖f * h_λ - f‖_p → 0` as `λ ↓ 0`. -/
theorem theorem_9_10 (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (f : RudinLp p) :
    (∀ l : ℝ, 0 < l → MemLp (rudinConv f (fun y => (rudinPoisson l y : ℂ))) p rudinMeasure) ∧
      Tendsto (fun l : ℝ =>
        if hl : 0 < l then
          ‖(theorem_9_10_memLp_and_bound p hp f hl).choose.toLp
            (rudinConv f (fun y => (rudinPoisson l y : ℂ))) - f‖
        else 0) (𝓝[>] 0) (𝓝 0) := by
  refine ⟨fun l hl => (theorem_9_10_memLp_and_bound p hp f hl).choose, ?_⟩
  have hp1 : 1 ≤ p := Fact.out
  let r : ℝ := p.toReal
  have hr1 : 1 ≤ r := by simpa [r] using (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp).mpr hp1
  have hr_pos : 0 < r := zero_lt_one.trans_le hr1
  let G : ℝ → ℂ := fun z => ((‖rudinTranslateLp p (-z) f - f‖ ^ r : ℝ) : ℂ)
  have hG_cont : Continuous G := by
    refine Complex.continuous_ofReal.comp ?_
    exact (((theorem_9_5 p hp f).continuous.comp continuous_neg |>.sub continuous_const).norm).rpow_const
      fun _ => Or.inr hr_pos.le
  have hG_bdd : MemLp G ∞ rudinMeasure := by
    refine memLp_top_of_bound hG_cont.aestronglyMeasurable ((2 * ‖f‖) ^ r) (ae_of_all _ fun z => ?_)
    dsimp [G]
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    gcongr
    calc
      ‖rudinTranslateLp p (-z) f - f‖ ≤ ‖rudinTranslateLp p (-z) f‖ + ‖f‖ := norm_sub_le _ _
      _ = 2 * ‖f‖ := by rw [LinearIsometryEquiv.norm_map]; ring
  have hG0 : G 0 = 0 := by
    simp [G, Real.zero_rpow hr_pos.ne']
  have h99 := (theorem_9_9 hG_bdd (hG_cont.continuousAt (x := 0))).2
  rw [hG0] at h99
  have hre_tendsto : Tendsto (fun l : ℝ =>
      ∫ y, ‖rudinTranslateLp p y f - f‖ ^ r * rudinPoisson l y ∂rudinMeasure)
      (𝓝[>] 0) (𝓝 0) := by
    have hre := (Complex.continuous_re.tendsto 0).comp h99
    simp only [Complex.zero_re] at hre
    refine hre.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with l (hl : 0 < l)
    dsimp [rudinConv, G]
    simp_rw [zero_sub, neg_neg, ← Complex.ofReal_mul]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  have hrpow_inv : Tendsto (fun l : ℝ =>
      (∫ y, ‖rudinTranslateLp p y f - f‖ ^ r * rudinPoisson l y ∂rudinMeasure) ^ (1 / r))
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun u : ℝ => u ^ (1 / r)) :=
      continuous_id.rpow_const fun _ => Or.inr (by positivity)
    have h0 : (0 : ℝ) ^ (1 / r) = 0 := Real.zero_rpow (by positivity)
    have hcomp := ((hc.continuousAt (x := 0)).tendsto).comp hre_tendsto
    rw [h0] at hcomp
    exact hcomp
  refine squeeze_zero' ?_ ?_ hrpow_inv
  · filter_upwards [self_mem_nhdsWithin] with l (hl : 0 < l)
    rw [dite_eq_left_of_eq_true (eq_true hl)]
    exact norm_nonneg _
  · filter_upwards [self_mem_nhdsWithin] with l (hl : 0 < l)
    rw [dite_eq_left_of_eq_true (eq_true hl)]
    have hbd := (theorem_9_10_memLp_and_bound p hp f hl).choose_spec
    calc
      ‖(theorem_9_10_memLp_and_bound p hp f hl).choose.toLp
        (rudinConv f (fun y => (rudinPoisson l y : ℂ))) - f‖
          = (‖(theorem_9_10_memLp_and_bound p hp f hl).choose.toLp
              (rudinConv f (fun y => (rudinPoisson l y : ℂ))) - f‖ ^ r) ^ (1 / r) := by
            rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hr_pos.ne', Real.rpow_one]
      _ ≤ (∫ y, ‖rudinTranslateLp p y f - f‖ ^ r * rudinPoisson l y ∂rudinMeasure) ^ (1 / r) :=
            Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hbd (by positivity)

end Node9_5_9_7_to_9_10

/-! ## §9.4, §9.6, §9.11–9.12: Riemann–Lebesgue, `L¹` Inversion, Uniqueness, and Circle Bridge -/

section Node9_4_9_6_9_11_9_12

open RudinRCA.Chapter04 RudinRCA.Chapter05

/-- 9.6 (pointwise bound): For any `f : ℝ → ℂ` and `t ∈ ℝ`, `|f̂(t)| ≤ ∫ |f| dm`. -/
theorem theorem_9_6_pointwise_bound (f : ℝ → ℂ) (t : ℝ) :
    ‖rudinFourier f t‖ ≤ ∫ x, ‖f x‖ ∂rudinMeasure := by
  calc
    ‖rudinFourier f t‖ = ‖∫ x, f x * Complex.exp (-Complex.I * x * t) ∂rudinMeasure‖ := rfl
    _ ≤ ∫ x, ‖f x * Complex.exp (-Complex.I * x * t)‖ ∂rudinMeasure :=
      norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ ∂rudinMeasure := by
      congr 1 with x
      rw [norm_mul, norm_exp_neg_I_mul_mul, mul_one]

/-- 9.6 (continuity): If `f ∈ L¹(m)`, then `f̂` is continuous on `ℝ`. -/
theorem theorem_9_6_continuous {f : ℝ → ℂ} (hf : Integrable f rudinMeasure) :
    Continuous (rudinFourier f) := by
  have hf_mem : MemLp f 1 volume := memLp_one_iff_integrable.mpr (integrable_rudinMeasure_iff.mp hf)
  have hcont_M : Continuous (𝓕 f) := by
    rw [← Real.fourierTransform_toLp hf_mem]
    exact (Real.Lp.fourierTransform hf_mem.toLp).continuous
  have h_eq : rudinFourier f = fun t : ℝ => (rudinFactor : ℂ) * (𝓕 f) (t / (2 * Real.pi)) := by
    ext t
    exact rudinFourier_eq_mathlib_fourier f t
  rw [h_eq]
  exact continuous_const.mul (hcont_M.comp (continuous_id.div_const _))

/-- 9.6 (vanishing at infinity / Riemann–Lebesgue): For `f : ℝ → ℂ`, `f̂(t) → 0` as `|t| → ∞`. -/
theorem theorem_9_6_zero_at_infty (f : ℝ → ℂ) :
    Tendsto (rudinFourier f) (cocompact ℝ) (𝓝 0) := by
  have h_eq : rudinFourier f = fun t : ℝ => (rudinFactor : ℂ) * (𝓕 f) (t / (2 * Real.pi)) := by
    ext t
    exact rudinFourier_eq_mathlib_fourier f t
  rw [h_eq]
  have h2pi : (2 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero (mul_pos two_pos Real.pi_pos).ne'
  let φ : ℝ ≃ₜ ℝ := Homeomorph.mulRight₀ (2 * Real.pi)⁻¹ h2pi
  have hcomp : Tendsto (fun t : ℝ => (𝓕 f) (t / (2 * Real.pi))) (cocompact ℝ) (𝓝 0) := by
    have h1 := (Real.zero_at_infty_fourier f).comp φ.toCocompactMap.cocompact_tendsto'
    refine h1.congr fun t => ?_
    change (𝓕 f) (t * (2 * Real.pi)⁻¹) = (𝓕 f) (t / (2 * Real.pi))
    rw [div_eq_mul_inv]
  simpa only [mul_zero] using hcomp.const_mul (rudinFactor : ℂ)

/-- 9.6: Bundled `C₀(ℝ)` Fourier transform of `f ∈ L¹(m)`. -/
def rudinFourierC0 {f : ℝ → ℂ} (hf : Integrable f rudinMeasure) : RudinC0 where
  toFun := rudinFourier f
  continuous_toFun := theorem_9_6_continuous hf
  zero_at_infty' := theorem_9_6_zero_at_infty f

@[simp]
theorem rudinFourierC0_apply {f : ℝ → ℂ} (hf : Integrable f rudinMeasure) (t : ℝ) :
    rudinFourierC0 hf t = rudinFourier f t := rfl

/-- 9.6: If `f ∈ L¹(m)`, then `f̂ ∈ C₀(ℝ)` and `‖f̂‖_∞ ≤ ‖f‖₁`. -/
theorem theorem_9_6 {f : ℝ → ℂ} (hf : Integrable f rudinMeasure) :
    IsVanishingAtInfty (rudinFourier f) ∧
      ‖rudinFourierC0 hf‖ ≤ ∫ x, ‖f x‖ ∂rudinMeasure ∧
      ‖rudinFourierC0 hf‖ ≤ rudinLpNorm 1 f := by
  have hvan : IsVanishingAtInfty (rudinFourier f) :=
    isVanishingAtInfty_iff_cocompact.mpr ⟨theorem_9_6_continuous hf, theorem_9_6_zero_at_infty f⟩
  have hnonneg : 0 ≤ ∫ x, ‖f x‖ ∂rudinMeasure := integral_nonneg fun _ => norm_nonneg _
  have hnorm : ‖rudinFourierC0 hf‖ ≤ ∫ x, ‖f x‖ ∂rudinMeasure := by
    change ‖(rudinFourierC0 hf).toBCF‖ ≤ ∫ x, ‖f x‖ ∂rudinMeasure
    exact (BoundedContinuousFunction.norm_le hnonneg).mpr (theorem_9_6_pointwise_bound f)
  have hlp1 : rudinLpNorm 1 f = ∫ x, ‖f x‖ ∂rudinMeasure := by
    unfold rudinLpNorm
    simp
  exact ⟨hvan, hnorm, hlp1 ▸ hnorm⟩

/-- Bundled continuous linear map `L¹(m) →L[ℂ] C₀(ℝ)` sending `f` to `f̂` with operator norm `≤ 1`. -/
def rudinFourierCLM : RudinLp 1 →L[ℂ] RudinC0 :=
  LinearMap.mkContinuous
    { toFun := fun f => rudinFourierC0 (L1.integrable_coeFn f)
      map_add' := fun f g => by
        ext t
        change rudinFourier (↑(f + g)) t = rudinFourier f t + rudinFourier g t
        rw [rudinFourier_congr_ae (Lp.coeFn_add f g)]
        unfold rudinFourier
        simp_rw [Pi.add_apply, add_mul]
        exact integral_add (rudinFourier_integrand_integrable (L1.integrable_coeFn f) t)
          (rudinFourier_integrand_integrable (L1.integrable_coeFn g) t)
      map_smul' := fun c f => by
        ext t
        change rudinFourier (↑(c • f)) t = c * rudinFourier f t
        rw [rudinFourier_congr_ae (Lp.coeFn_smul c f)]
        unfold rudinFourier
        simp_rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact integral_const_mul c _ }
    1
    (fun f => by
      have hb := (theorem_9_6 (L1.integrable_coeFn f)).2.1
      rw [← L1.norm_eq_integral_norm f] at hb
      change ‖rudinFourierC0 (L1.integrable_coeFn f)‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact hb)

@[simp]
theorem rudinFourierCLM_apply (f : RudinLp 1) (t : ℝ) :
    rudinFourierCLM f t = rudinFourier f t := rfl

theorem rudinFourierCLM_norm_le_one : ‖rudinFourierCLM‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    have hb := (theorem_9_6 (L1.integrable_coeFn f)).2.1
    rw [← L1.norm_eq_integral_norm f] at hb
    change ‖rudinFourierC0 (L1.integrable_coeFn f)‖ ≤ 1 * ‖f‖
    rw [one_mul]
    exact hb

/-- 9.11 (The Inversion Theorem): If `f ∈ L¹(m)` and `f̂ ∈ L¹(m)` (with no continuity assumption
on `f`), and `g(x) = ∫ f̂(t) e^(i x t) dm(t)`, then `g ∈ C₀(ℝ)` and `f(x) = g(x)` a.e. `[m]`. -/
theorem theorem_9_11 {f : ℝ → ℂ} (hf : Integrable f rudinMeasure)
    (hhat : Integrable (rudinFourier f) rudinMeasure) :
    IsVanishingAtInfty (rudinFourierInv (rudinFourier f)) ∧
      f =ᵐ[rudinMeasure] rudinFourierInv (rudinFourier f) := by
  have h_inv_eq : rudinFourierInv (rudinFourier f) =
      fun x : ℝ => rudinFourier (rudinFourier f) (-x) := by
    ext x
    exact rudinFourierInv_eq_rudinFourier_neg (rudinFourier f) x
  have hg_cont : Continuous (rudinFourierInv (rudinFourier f)) := by
    rw [h_inv_eq]
    exact (theorem_9_6_continuous hhat).comp continuous_neg
  have hg_zero : Tendsto (rudinFourierInv (rudinFourier f)) (cocompact ℝ) (𝓝 0) := by
    rw [h_inv_eq]
    exact (theorem_9_6_zero_at_infty (rudinFourier f)).comp
      (Homeomorph.neg ℝ).toCocompactMap.cocompact_tendsto'
  refine ⟨isVanishingAtInfty_iff_cocompact.mpr ⟨hg_cont, hg_zero⟩, ?_⟩
  let l : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hl_pos : ∀ n : ℕ, 0 < l n := fun n => by dsimp [l]; positivity
  have hl_tendsto : Tendsto l atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall hl_pos⟩
  have hpt : ∀ x : ℝ, Tendsto
      (fun n : ℕ => rudinConv f (fun y => (rudinPoisson (l n) y : ℂ)) x)
      atTop (𝓝 (rudinFourierInv (rudinFourier f) x)) := by
    intro x
    have hcongr : (fun n : ℕ => rudinConv f (fun y => (rudinPoisson (l n) y : ℂ)) x) =
        fun n : ℕ => ∫ t, (rudinH (l n * t) : ℂ) *
          (rudinFourier f t * Complex.exp (Complex.I * x * t)) ∂rudinMeasure := by
      ext n
      rw [theorem_9_8 hf (hl_pos n) x]
      congr 1 with t
      ring
    rw [hcongr]
    refine tendsto_integral_of_dominated_convergence (fun t => ‖rudinFourier f t‖)
      (fun n => ?_) hhat.norm (fun n => ae_of_all _ fun t => ?_) (ae_of_all _ fun t => ?_)
    · have hcH : Continuous (fun t : ℝ => (rudinH (l n * t) : ℂ)) :=
        Complex.continuous_ofReal.comp (continuous_rudinH.comp (continuous_const.mul continuous_id))
      exact hcH.aestronglyMeasurable.mul (rudinFourierInv_integrand_integrable hhat x).aestronglyMeasurable
    · rw [norm_mul, norm_mul, norm_exp_I_mul_mul, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (theorem_9_7_H_bounds (l n * t)).1.le]
      exact mul_le_of_le_one_left (norm_nonneg _) (theorem_9_7_H_bounds (l n * t)).2
    · have hHt : Tendsto (fun n : ℕ => (rudinH (l n * t) : ℂ)) atTop (𝓝 1) := by
        have h1 := (Complex.continuous_ofReal.tendsto 1).comp
          ((theorem_9_7_H_tendsto_one t).comp hl_tendsto)
        rw [Complex.ofReal_one] at h1
        exact h1
      simpa only [one_mul] using hHt.mul_const (rudinFourier f t * Complex.exp (Complex.I * x * t))
  let F : RudinLp 1 := (memLp_one_iff_integrable.mpr hf).toLp f
  have hF_ae : (F : ℝ → ℂ) =ᵐ[rudinMeasure] f := (memLp_one_iff_integrable.mpr hf).coeFn_toLp
  have hconv_eq : ∀ (n : ℕ) (x : ℝ),
      rudinConv (F : ℝ → ℂ) (fun y => (rudinPoisson (l n) y : ℂ)) x =
        rudinConv f (fun y => (rudinPoisson (l n) y : ℂ)) x := by
    intro n x
    unfold rudinConv
    apply integral_congr_ae
    have hsub := (rudinMeasure.measurePreserving_sub_left x).quasiMeasurePreserving.ae hF_ae
    filter_upwards [hsub] with y hy
    rw [hy]
  let u : ℕ → RudinLp 1 := fun n =>
    (theorem_9_10_memLp_and_bound 1 ENNReal.one_ne_top F (hl_pos n)).choose.toLp
      (rudinConv F (fun y => (rudinPoisson (l n) y : ℂ)))
  have hu_tendsto : Tendsto u atTop (𝓝 F) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h910 := ((theorem_9_10 1 ENNReal.one_ne_top F).2).comp hl_tendsto
    refine h910.congr fun n => ?_
    dsimp only [Function.comp_def, u]
    rw [dite_eq_left_of_eq_true (eq_true (hl_pos n))]
  have hm := tendstoInMeasure_of_tendsto_Lp hu_tendsto
  have hu_ae : ∀ n : ℕ, (u n : ℝ → ℂ) =ᵐ[rudinMeasure]
      fun x => rudinConv f (fun y => (rudinPoisson (l n) y : ℂ)) x := by
    intro n
    filter_upwards [(theorem_9_10_memLp_and_bound 1 ENNReal.one_ne_top F (hl_pos n)).choose.coeFn_toLp]
      with x hx
    rw [hx, hconv_eq n x]
  obtain ⟨ns, hns_mono, hns_ae⟩ := (hm.congr_left hu_ae).exists_seq_tendsto_ae
  filter_upwards [hns_ae, hF_ae] with x hx_F hx_f
  rw [hx_f] at hx_F
  exact tendsto_nhds_unique hx_F ((hpt x).comp hns_mono.tendsto_atTop)

/-- Bundled `C₀(ℝ)` inverse Fourier integral when `f̂ ∈ L¹(m)`. -/
def rudinFourierInvC0 {f : ℝ → ℂ} (hhat : Integrable (rudinFourier f) rudinMeasure) : RudinC0 where
  toFun := rudinFourierInv (rudinFourier f)
  continuous_toFun := by
    have h : rudinFourierInv (rudinFourier f) = fun x : ℝ => rudinFourier (rudinFourier f) (-x) := by
      ext x; exact rudinFourierInv_eq_rudinFourier_neg _ x
    rw [h]
    exact (theorem_9_6_continuous hhat).comp continuous_neg
  zero_at_infty' := by
    have h : rudinFourierInv (rudinFourier f) = fun x : ℝ => rudinFourier (rudinFourier f) (-x) := by
      ext x; exact rudinFourierInv_eq_rudinFourier_neg _ x
    rw [h]
    exact (theorem_9_6_zero_at_infty (rudinFourier f)).comp
      (Homeomorph.neg ℝ).toCocompactMap.cocompact_tendsto'

/-- 9.12 (The Uniqueness Theorem): If `f ∈ L¹(m)` and `f̂(t) = 0` for all `t ∈ ℝ`, then
`f(x) = 0` a.e. `[m]`. -/
theorem theorem_9_12 {f : ℝ → ℂ} (hf : Integrable f rudinMeasure)
    (hzero : ∀ t : ℝ, rudinFourier f t = 0) :
    f =ᵐ[rudinMeasure] 0 := by
  have hhat_eq : rudinFourier f = 0 := funext hzero
  have hhat : Integrable (rudinFourier f) rudinMeasure := by
    rw [hhat_eq]
    exact integrable_zero _ _ _
  have h11 := (theorem_9_11 hf hhat).2
  refine h11.trans (ae_of_all _ fun x => ?_)
  simp [rudinFourierInv, hzero]

/-- Two `L¹(m)` functions with the same Fourier transform agree almost everywhere. -/
theorem theorem_9_12_eq {f₁ f₂ : ℝ → ℂ} (hf₁ : Integrable f₁ rudinMeasure)
    (hf₂ : Integrable f₂ rudinMeasure) (heq : ∀ t : ℝ, rudinFourier f₁ t = rudinFourier f₂ t) :
    f₁ =ᵐ[rudinMeasure] f₂ := by
  have hdiff : ∀ t : ℝ, rudinFourier (fun x => f₁ x - f₂ x) t = 0 := by
    intro t
    unfold rudinFourier
    simp_rw [sub_mul]
    rw [integral_sub (rudinFourier_integrand_integrable hf₁ t)
      (rudinFourier_integrand_integrable hf₂ t)]
    exact sub_eq_zero.mpr (heq t)
  filter_upwards [theorem_9_12 (hf₁.sub hf₂) hdiff] with x hx
  exact sub_eq_zero.mp hx

/-- The bundled `L¹(m) → C₀(ℝ)` Fourier transform is injective on `L¹(m)`. -/
theorem rudinFourierCLM_injective : Function.Injective rudinFourierCLM := by
  intro f₁ f₂ h
  apply Lp.ext
  exact theorem_9_12_eq (L1.integrable_coeFn f₁) (L1.integrable_coeFn f₂) fun t =>
    congr_arg (fun g : RudinC0 => g t) h

/-- 9.4 (circle `L¹` inversion under absolutely summable coefficients): For any arbitrary
`f ∈ L¹(𝕋)` (without assuming continuity of `f`), if `∑_{n ∈ ℤ} |f̂(n)| < ∞`, then the Fourier
series `∑_{n ∈ ℤ} f̂(n) e^(i n x)` converges uniformly to a continuous function `g ∈ C(𝕋)` whose
Fourier coefficients equal `f̂`, and `f(x) = g(x)` almost everywhere on `𝕋`. -/
theorem theorem_9_4_circle_l1_inversion (f : CircleL1)
    (hsumm : Summable (fun n : ℤ => ‖circleFourierCoeff f n‖)) :
    ∃ g : C(FourierCircle, ℂ),
      HasSum (fun n : ℤ => circleFourierCoeff f n • trigMonomial n) g ∧
      Tendsto (fun N : ℕ => circleFourierPartialSum f N) atTop (𝓝 g) ∧
      (∀ n : ℤ, circleFourierCoeff g n = circleFourierCoeff f n) ∧
      (f : FourierCircle → ℂ) =ᵐ[circleMeasure] g := by
  have hterm_summ : Summable (fun n : ℤ => circleFourierCoeff f n • trigMonomial n) := by
    refine .of_norm_bounded hsumm fun n => ?_
    rw [norm_smul]
    have hmn : ‖trigMonomial n‖ ≤ 1 :=
      (ContinuousMap.norm_le _ zero_le_one).mpr fun x => by
        simp [trigMonomial, fourier_apply]
    exact mul_le_of_le_one_right (norm_nonneg _) hmn
  let g : C(FourierCircle, ℂ) := ∑' n : ℤ, circleFourierCoeff f n • trigMonomial n
  have hg_hasSum : HasSum (fun n : ℤ => circleFourierCoeff f n • trigMonomial n) g :=
    hterm_summ.hasSum
  have hg_partial : Tendsto (fun N : ℕ => circleFourierPartialSum f N) atTop (𝓝 g) :=
    hg_hasSum.comp (Finset.tendsto_Icc_neg (R := ℤ))
  have hg_coeff : ∀ k : ℤ, circleFourierCoeff g k = circleFourierCoeff f k := by
    intro k
    let Lk : C(FourierCircle, ℂ) →L[ℂ] ℂ :=
      (fourierCoeffL1 k).comp (ContinuousMap.toLp 1 circleMeasure ℂ)
    have hLk_sum : HasSum (fun n : ℤ => Lk (circleFourierCoeff f n • trigMonomial n)) (Lk g) :=
      Lk.hasSum hg_hasSum
    have hLk_g : Lk g = circleFourierCoeff g k := fourierCoeffL1_toLp k g
    rw [hLk_g] at hLk_sum
    have hLk_term : (fun n : ℤ => Lk (circleFourierCoeff f n • trigMonomial n)) =
        fun n : ℤ => if n = k then circleFourierCoeff f k else 0 := by
      ext n
      change fourierCoeffL1 k (ContinuousMap.toLp 1 circleMeasure ℂ
        (circleFourierCoeff f n • trigMonomial n)) = _
      rw [map_smul, map_smul, fourierCoeffL1_toLp, smul_eq_mul]
      change circleFourierCoeff f n * fourierCoeff (fourier n) k = _
      rw [fourierCoeff_fourier]
      by_cases hnk : n = k
      · subst hnk; simp
      · simp [hnk, Ne.symm hnk]
    rw [hLk_term] at hLk_sum
    exact hLk_sum.unique (hasSum_ite_eq k (circleFourierCoeff f k))
  let G : CircleL1 := ContinuousMap.toLp 1 circleMeasure ℂ g
  have hdiff_zero : ∀ k : ℤ, circleFourierCoeff (f - G : CircleL1) k = 0 := by
    intro k
    rw [← fourierCoeffL1_apply, map_sub, fourierCoeffL1_apply, fourierCoeffL1_toLp, hg_coeff k,
      sub_self]
  have hfG_ae : (f - G : CircleL1) =ᵐ[circleMeasure] (0 : FourierCircle → ℂ) :=
    ae_eq_zero_of_fourierCoeff (f - G) hdiff_zero
  have hfg_ae : (f : FourierCircle → ℂ) =ᵐ[circleMeasure] g := by
    filter_upwards [Lp.coeFn_sub f G,
      ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (1 : ℝ≥0∞)) circleMeasure g, hfG_ae]
      with x hx_sub hx_G hx_zero
    rw [hx_sub, Pi.sub_apply, hx_G] at hx_zero
    exact sub_eq_zero.mp hx_zero
  exact ⟨g, hg_hasSum, hg_partial, hg_coeff, hfg_ae⟩

/-- 9.4 (recalled circle `L²` convergence from §4.26): Partial sums of the Fourier series of any
`f ∈ L²(𝕋)` converge to `f` in `L²(𝕋)`. -/
theorem remark_9_4_circle_l2_convergence (f : CircleL2) :
    Tendsto (fourierPartialSum f) atTop (𝓝 f) :=
  fourierPartialSum_tendsto f

/-- 9.4 (recalled continuous divergence from §5.11–5.12): Continuous functions on `𝕋` can have
divergent Fourier series on a dense `G_δ` subset. -/
theorem remark_9_4_circle_continuous_divergence :
    ∃ E : Set C(FourierCircle, ℂ), Dense E ∧ IsGδ E ∧
      ∀ f ∈ E, Dense (fourierDivergencePoints f) ∧ IsGδ (fourierDivergencePoints f) :=
  theorem_5_12

/-- 9.4 (nonintegrability of the naive Fubini oscillatory kernel on `ℝ`): For every `x, y ∈ ℝ`,
the oscillatory kernel `t ↦ e^(i (x - y) t)` has constant modulus `1` on `(ℝ, m)` of infinite
measure, so it is never in `L¹(m)` and naive reversal of integration in `∫ f̂(t) e^(i x t) dm(t)`
is illegitimate. -/
theorem remark_9_4_oscillatory_not_integrable (x y : ℝ) :
    ¬ Integrable (fun t : ℝ => Complex.exp (Complex.I * (x - y) * t)) rudinMeasure := by
  intro hint
  have hnorm : Integrable (fun _ : ℝ => (1 : ℝ)) rudinMeasure := by
    refine hint.norm.congr (ae_of_all _ fun t => ?_)
    dsimp
    rw [← Complex.ofReal_sub]
    exact norm_exp_I_mul_mul (x - y) t
  rw [integrable_const_iff] at hnorm
  rcases hnorm with h10 | hfin
  · norm_num at h10
  · have : IsFiniteMeasure rudinMeasure := hfin
    have huniv : rudinMeasure univ = ∞ := by
      rw [rudinMeasure_apply, Real.volume_univ,
        ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne']
    exact (measure_lt_top rudinMeasure univ).ne huniv

end Node9_4_9_6_9_11_9_12

/-! ## §9.13–9.15: Plancherel's Theorem and `L²` Fourier Inversion -/

section Node9_13_to_9_15

open SchwartzMap

/-- Auxiliary `L¹ ∩ L²` forward compatibility on `(ℝ, volume)` between `Lp.fourierTransformₗᵢ`
and the pointwise Fourier integral `𝓕`. -/
private lemma volume_fourierL2_ae_eq_fourier {u : ℝ → ℂ} (hu1 : Integrable u volume)
    (hu2 : MemLp u 2 volume) :
    (Lp.fourierTransformₗᵢ ℝ ℂ (hu2.toLp u) : ℝ → ℂ) =ᵐ[volume] 𝓕 u := by
  have hFu_cont : Continuous (𝓕 u) := by
    have hm1 : MemLp u 1 volume := memLp_one_iff_integrable.mpr hu1
    rw [← Real.fourierTransform_toLp hm1]
    exact (Real.Lp.fourierTransform hm1.toLp).continuous
  apply ae_eq_of_integral_contDiff_smul_eq (μ := volume)
    ((Lp.memLp (Lp.fourierTransformₗᵢ ℝ ℂ (hu2.toLp u))).locallyIntegrable one_le_two)
    hFu_cont.locallyIntegrable
  intro g hg_smooth hg_cpt
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hg_cpt.comp_left rfl
  have hg₂ := Complex.ofRealCLM.contDiff.comp hg_smooth
  let φ : 𝓢(ℝ, ℂ) := hg₁.toSchwartzMap hg₂
  have hφ_apply : ∀ x : ℝ, (φ : ℝ → ℂ) x = (g x : ℂ) := fun x => by simp [φ]
  have hdist : (𝓕 ((hu2.toLp u : Lp ℂ 2 (volume : Measure ℝ)) : 𝓢'(ℝ, ℂ))) φ =
      ((Lp.fourierTransformₗᵢ ℝ ℂ (hu2.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) : 𝓢'(ℝ, ℂ)) φ :=
    congr_arg (fun T : 𝓢'(ℝ, ℂ) => T φ) (Lp.fourier_toTemperedDistribution_eq (hu2.toLp u))
  exact calc
    (∫ x : ℝ, g x • (Lp.fourierTransformₗᵢ ℝ ℂ (hu2.toLp u) : ℝ → ℂ) x ∂volume)
        = ((Lp.fourierTransformₗᵢ ℝ ℂ (hu2.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) : 𝓢'(ℝ, ℂ)) φ := by
          simp [φ, Lp.toTemperedDistribution_apply]
    _ = (𝓕 ((hu2.toLp u : Lp ℂ 2 (volume : Measure ℝ)) : 𝓢'(ℝ, ℂ))) φ := hdist.symm
    _ = ∫ x : ℝ, (𝓕 (φ : ℝ → ℂ)) x • u x := by
          rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
          apply integral_congr_ae
          filter_upwards [hu2.coeFn_toLp] with x hx
          rw [hx, SchwartzMap.fourier_coe]
    _ = ∫ x : ℝ, (φ : ℝ → ℂ) x • (𝓕 u) x := by
          simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
            Real.continuous_fourierChar continuous_inner φ.integrable hu1
    _ = ∫ x : ℝ, g x • (𝓕 u) x ∂volume := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          dsimp only
          rw [hφ_apply x, smul_eq_mul, Complex.real_smul]

/-- Auxiliary `L¹ ∩ L²` inverse compatibility on `(ℝ, volume)` between
`(Lp.fourierTransformₗᵢ ℝ ℂ).symm` and `𝓕⁻`. -/
private lemma volume_fourierInvL2_ae_eq_fourierInv {u : ℝ → ℂ} (hu1 : Integrable u volume)
    (hu2 : MemLp u 2 volume) :
    ((Lp.fourierTransformₗᵢ ℝ ℂ).symm (hu2.toLp u) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ u := by
  have hu_neg1 : Integrable (fun x : ℝ => u (-x)) volume :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hu1
  have hFu_cont : Continuous (𝓕⁻ u) := by
    rw [Real.fourierInv_eq_fourier_comp_neg]
    have hm1 : MemLp (fun x : ℝ => u (-x)) 1 volume := memLp_one_iff_integrable.mpr hu_neg1
    rw [← Real.fourierTransform_toLp hm1]
    exact (Real.Lp.fourierTransform hm1.toLp).continuous
  apply ae_eq_of_integral_contDiff_smul_eq (μ := volume)
    ((Lp.memLp ((Lp.fourierTransformₗᵢ ℝ ℂ).symm (hu2.toLp u))).locallyIntegrable one_le_two)
    hFu_cont.locallyIntegrable
  intro g hg_smooth hg_cpt
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hg_cpt.comp_left rfl
  have hg₂ := Complex.ofRealCLM.contDiff.comp hg_smooth
  let φ : 𝓢(ℝ, ℂ) := hg₁.toSchwartzMap hg₂
  have hφ_apply : ∀ x : ℝ, (φ : ℝ → ℂ) x = (g x : ℂ) := fun x => by simp [φ]
  have hdist : (𝓕⁻ ((hu2.toLp u : Lp ℂ 2 (volume : Measure ℝ)) : 𝓢'(ℝ, ℂ))) φ =
      (((Lp.fourierTransformₗᵢ ℝ ℂ).symm (hu2.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) : 𝓢'(ℝ, ℂ)) φ :=
    congr_arg (fun T : 𝓢'(ℝ, ℂ) => T φ) (Lp.fourierInv_toTemperedDistribution_eq (hu2.toLp u))
  exact calc
    (∫ x : ℝ, g x • ((Lp.fourierTransformₗᵢ ℝ ℂ).symm (hu2.toLp u) : ℝ → ℂ) x ∂volume)
        = (((Lp.fourierTransformₗᵢ ℝ ℂ).symm (hu2.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) :
            𝓢'(ℝ, ℂ)) φ := by
          simp [φ, Lp.toTemperedDistribution_apply]
    _ = (𝓕⁻ ((hu2.toLp u : Lp ℂ 2 (volume : Measure ℝ)) : 𝓢'(ℝ, ℂ))) φ := hdist.symm
    _ = ∫ x : ℝ, (𝓕⁻ (φ : ℝ → ℂ)) x • u x := by
          rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]
          apply integral_congr_ae
          filter_upwards [hu2.coeFn_toLp] with x hx
          rw [hx, SchwartzMap.fourierInv_coe]
    _ = ∫ y : ℝ, (𝓕 (φ : ℝ → ℂ)) y • u (-y) := by
          simp_rw [Real.fourierInv_eq_fourier_neg]
          refine (integral_neg_eq_self
            (fun x : ℝ => (𝓕 (φ : ℝ → ℂ)) (-x) • u x) volume).symm.trans ?_
          simp_rw [neg_neg]
    _ = ∫ x : ℝ, (φ : ℝ → ℂ) x • 𝓕 (fun y : ℝ => u (-y)) x := by
          simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
            Real.continuous_fourierChar continuous_inner φ.integrable hu_neg1
    _ = ∫ x : ℝ, g x • (𝓕⁻ u) x ∂volume := by
          rw [← Real.fourierInv_eq_fourier_comp_neg]
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          dsimp only
          rw [hφ_apply x, smul_eq_mul, Complex.real_smul]

/-- 9.13: Rudin's Plancherel Hilbert-space isomorphism `L²(m) ≃ₗᵢ[ℂ] L²(m)`, obtained by
conjugating Mathlib's `Lp.fourierTransformₗᵢ ℝ ℂ` with the isometric coordinate dilation
`rudinScaleLpEquiv 2 : L²(m) ≃ₗᵢ[ℂ] L²(volume)`. -/
def rudinPlancherel : RudinLp 2 ≃ₗᵢ[ℂ] RudinLp 2 :=
  (rudinScaleLpEquiv 2).trans
    ((Lp.fourierTransformₗᵢ ℝ ℂ).trans (rudinScaleLpEquiv 2).symm)

/-- 9.13 (`L¹ ∩ L²` compatibility): For `f ∈ L¹(m) ∩ L²(m)`, the Plancherel transform
`rudinPlancherel (hf2.toLp f)` agrees `m`-almost everywhere with the classical Fourier integral
`rudinFourier f`. -/
theorem theorem_9_13_L1_L2_compat {f : ℝ → ℂ} (hf1 : Integrable f rudinMeasure)
    (hf2 : MemLp f 2 rudinMeasure) :
    (rudinPlancherel (hf2.toLp f) : ℝ → ℂ) =ᵐ[rudinMeasure] rudinFourier f := by
  let u : ℝ → ℂ := rudinDilate f
  have hu1 : Integrable u volume :=
    (measurePreserving_rudinScaleHomeo.integrable_comp_emb
      rudinScaleHomeo.toMeasurableEquiv.measurableEmbedding).mpr hf1
  have hu2 : MemLp u 2 volume := hf2.comp_measurePreserving measurePreserving_rudinScaleHomeo
  have hscale_eq : rudinScaleLpEquiv 2 (hf2.toLp f) = hu2.toLp u := by
    apply Lp.ext
    have hdil_ae : rudinDilate (hf2.toLp f) =ᵐ[volume] u :=
      measurePreserving_rudinScaleHomeo.quasiMeasurePreserving.ae hf2.coeFn_toLp
    exact (rudinScaleLpEquiv_coeFn 2 (hf2.toLp f)).trans (hdil_ae.trans hu2.coeFn_toLp.symm)
  have hplan_eq : rudinPlancherel (hf2.toLp f) =
      (rudinScaleLpEquiv 2).symm (Lp.fourierTransformₗᵢ ℝ ℂ (hu2.toLp u)) := by
    simp [rudinPlancherel, hscale_eq]
  rw [hplan_eq]
  have hvol_ae := volume_fourierL2_ae_eq_fourier hu1 hu2
  have hundil_ae : rudinUnDilate (Lp.fourierTransformₗᵢ ℝ ℂ (hu2.toLp u)) =ᵐ[rudinMeasure]
      rudinUnDilate (𝓕 u) := by
    have hpull := measurePreserving_rudinScaleHomeo_symm.quasiMeasurePreserving.ae hvol_ae
    filter_upwards [hpull] with x hx
    change (Lp.fourierTransformₗᵢ ℝ ℂ (hu2.toLp u) : ℝ → ℂ) (x / rudinScale) = (𝓕 u) (x / rudinScale)
    rw [div_eq_inv_mul]
    exact hx
  refine (rudinScaleLpEquiv_symm_coeFn 2 _).trans (hundil_ae.trans (ae_of_all _ fun x => ?_))
  have hbridge : rudinUnDilate (𝓕 u) = rudinFourier f := by
    dsimp [u]
    rw [← rudinDilate_rudinFourier f, rudinUnDilate_rudinDilate]
  exact congr_fun hbridge x

/-- Inverse `L¹ ∩ L²` compatibility: For `g ∈ L¹(m) ∩ L²(m)`, `rudinPlancherel.symm (hg2.toLp g)`
agrees `m`-almost everywhere with `rudinFourierInv g`. -/
theorem theorem_9_13_inv_L1_L2_compat {g : ℝ → ℂ} (hg1 : Integrable g rudinMeasure)
    (hg2 : MemLp g 2 rudinMeasure) :
    (rudinPlancherel.symm (hg2.toLp g) : ℝ → ℂ) =ᵐ[rudinMeasure] rudinFourierInv g := by
  let u : ℝ → ℂ := rudinDilate g
  have hu1 : Integrable u volume :=
    (measurePreserving_rudinScaleHomeo.integrable_comp_emb
      rudinScaleHomeo.toMeasurableEquiv.measurableEmbedding).mpr hg1
  have hu2 : MemLp u 2 volume := hg2.comp_measurePreserving measurePreserving_rudinScaleHomeo
  have hscale_eq : rudinScaleLpEquiv 2 (hg2.toLp g) = hu2.toLp u := by
    apply Lp.ext
    have hdil_ae : rudinDilate (hg2.toLp g) =ᵐ[volume] u :=
      measurePreserving_rudinScaleHomeo.quasiMeasurePreserving.ae hg2.coeFn_toLp
    exact (rudinScaleLpEquiv_coeFn 2 (hg2.toLp g)).trans (hdil_ae.trans hu2.coeFn_toLp.symm)
  have hplan_eq : rudinPlancherel.symm (hg2.toLp g) =
      (rudinScaleLpEquiv 2).symm ((Lp.fourierTransformₗᵢ ℝ ℂ).symm (hu2.toLp u)) := by
    simp [rudinPlancherel, hscale_eq]
  rw [hplan_eq]
  have hvol_ae := volume_fourierInvL2_ae_eq_fourierInv hu1 hu2
  have hundil_ae : rudinUnDilate ((Lp.fourierTransformₗᵢ ℝ ℂ).symm (hu2.toLp u)) =ᵐ[rudinMeasure]
      rudinUnDilate (𝓕⁻ u) := by
    have hpull := measurePreserving_rudinScaleHomeo_symm.quasiMeasurePreserving.ae hvol_ae
    filter_upwards [hpull] with x hx
    change ((Lp.fourierTransformₗᵢ ℝ ℂ).symm (hu2.toLp u) : ℝ → ℂ) (x / rudinScale) =
      (𝓕⁻ u) (x / rudinScale)
    rw [div_eq_inv_mul]
    exact hx
  refine (rudinScaleLpEquiv_symm_coeFn 2 _).trans (hundil_ae.trans (ae_of_all _ fun x => ?_))
  have hbridge : rudinUnDilate (𝓕⁻ u) = rudinFourierInv g := by
    dsimp [u]
    rw [← rudinDilate_rudinFourierInv g, rudinUnDilate_rudinDilate]
  exact congr_fun hbridge x

/-- 9.13: Plancherel norm identity `‖f̂‖₂ = ‖f‖₂` on `L²(m)`. -/
theorem theorem_9_13_norm (f : RudinLp 2) :
    ‖rudinPlancherel f‖ = ‖f‖ :=
  rudinPlancherel.norm_map f

/-- 9.13: Parseval / inner-product identity `(f̂, ĝ) = (f, g)` on `L²(m)`, both in abstract
Hilbert-space inner product form and explicit `m`-integral form. -/
theorem theorem_9_13_inner (f g : RudinLp 2) :
    inner ℂ (rudinPlancherel f) (rudinPlancherel g) = inner ℂ f g ∧
      ∫ t, (rudinPlancherel g : ℝ → ℂ) t * conj ((rudinPlancherel f : ℝ → ℂ) t) ∂rudinMeasure =
        ∫ x, (g : ℝ → ℂ) x * conj ((f : ℝ → ℂ) x) ∂rudinMeasure := by
  refine ⟨rudinPlancherel.inner_map_map f g, ?_⟩
  have h := rudinPlancherel.inner_map_map f g
  rw [L2.inner_def, L2.inner_def] at h
  simpa only [RCLike.inner_apply, mul_comm] using h

/-- 9.13: `rudinPlancherel` is a Hilbert-space isomorphism of `L²(m)` onto `L²(m)`. -/
theorem theorem_9_13_surjective : Function.Surjective rudinPlancherel :=
  rudinPlancherel.surjective

/-- 9.13: Truncated forward Fourier integral `φ_A(t) = ∫_{-A}^A f(x) e^(-i x t) dm(x)`. -/
def rudinTruncatedFourier (f : ℝ → ℂ) (A : ℝ) (t : ℝ) : ℂ :=
  ∫ x in Icc (-A) A, f x * Complex.exp (-Complex.I * x * t) ∂rudinMeasure

/-- 9.13: Truncated inverse Fourier integral `ψ_A(x) = ∫_{-A}^A g(t) e^(i x t) dm(t)`. -/
def rudinTruncatedFourierInv (g : ℝ → ℂ) (A : ℝ) (x : ℝ) : ℂ :=
  ∫ t in Icc (-A) A, g t * Complex.exp (Complex.I * x * t) ∂rudinMeasure

theorem rudinTruncatedFourier_eq_indicator (f : ℝ → ℂ) (A : ℝ) :
    rudinTruncatedFourier f A = rudinFourier ((Icc (-A) A).indicator f) := by
  ext t
  unfold rudinTruncatedFourier rudinFourier
  rw [← integral_indicator measurableSet_Icc]
  congr 1 with x
  by_cases hx : x ∈ Icc (-A) A <;> simp [hx]

theorem rudinTruncatedFourierInv_eq_indicator (g : ℝ → ℂ) (A : ℝ) :
    rudinTruncatedFourierInv g A = rudinFourierInv ((Icc (-A) A).indicator g) := by
  ext x
  unfold rudinTruncatedFourierInv rudinFourierInv
  rw [← integral_indicator measurableSet_Icc]
  congr 1 with t
  by_cases ht : t ∈ Icc (-A) A <;> simp [ht]

private lemma indicator_Icc_integrable_of_L2 (f : RudinLp 2) (A : ℝ) :
    Integrable ((Icc (-A) A).indicator (f : ℝ → ℂ)) rudinMeasure := by
  let χ : RudinLp 2 :=
    indicatorConstLp 2 (s := Icc (-A) A) measurableSet_Icc isCompact_Icc.measure_lt_top.ne (1 : ℂ)
  have hχ_ae : (χ : ℝ → ℂ) =ᵐ[rudinMeasure] (Icc (-A) A).indicator fun _ => (1 : ℂ) :=
    indicatorConstLp_coeFn
  have hint := L2.integrable_inner (𝕜 := ℂ) χ f
  refine hint.congr ?_
  filter_upwards [hχ_ae] with x hx
  change inner ℂ ((χ : ℝ → ℂ) x) ((f : ℝ → ℂ) x) = (Icc (-A) A).indicator (f : ℝ → ℂ) x
  rw [RCLike.inner_apply, hx]
  by_cases hmem : x ∈ Icc (-A) A <;> simp [hmem]

private lemma indicator_Icc_toLp_tendsto (f : RudinLp 2) :
    Tendsto (fun A : ℝ =>
      ((Lp.memLp f).indicator measurableSet_Icc :
        MemLp ((Icc (-A) A).indicator (f : ℝ → ℂ)) 2 rudinMeasure).toLp
        ((Icc (-A) A).indicator (f : ℝ → ℂ)))
      atTop (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm_sq : ∀ A : ℝ,
      ‖((Lp.memLp f).indicator measurableSet_Icc :
          MemLp ((Icc (-A) A).indicator (f : ℝ → ℂ)) 2 rudinMeasure).toLp
          ((Icc (-A) A).indicator (f : ℝ → ℂ)) - f‖ ^ 2 =
        ∫ x, ‖(Icc (-A) A).indicator (f : ℝ → ℂ) x - (f : ℝ → ℂ) x‖ ^ 2 ∂rudinMeasure := by
    intro A
    let d : RudinLp 2 :=
      ((Lp.memLp f).indicator measurableSet_Icc).toLp ((Icc (-A) A).indicator (f : ℝ → ℂ)) - f
    have hd_ae : (d : ℝ → ℂ) =ᵐ[rudinMeasure]
        fun x => (Icc (-A) A).indicator (f : ℝ → ℂ) x - (f : ℝ → ℂ) x := by
      filter_upwards [Lp.coeFn_sub (((Lp.memLp f).indicator measurableSet_Icc).toLp _) f,
        ((Lp.memLp f).indicator measurableSet_Icc).coeFn_toLp] with x hx1 hx2
      rw [hx1, Pi.sub_apply, hx2]
    calc
      ‖d‖ ^ 2 = RCLike.re (inner ℂ d d) := norm_sq_eq_re_inner d
      _ = RCLike.re (∫ x, inner ℂ ((d : ℝ → ℂ) x) ((d : ℝ → ℂ) x) ∂rudinMeasure) := by
            rw [L2.inner_def]
      _ = ∫ x, ‖(d : ℝ → ℂ) x‖ ^ 2 ∂rudinMeasure := by
            simp_rw [inner_self_eq_norm_sq_to_K]
            norm_cast
      _ = ∫ x, ‖(Icc (-A) A).indicator (f : ℝ → ℂ) x - (f : ℝ → ℂ) x‖ ^ 2 ∂rudinMeasure := by
            apply integral_congr_ae
            filter_upwards [hd_ae] with x hx
            rw [hx]
  have hint_sq : Integrable (fun x : ℝ => ‖(f : ℝ → ℂ) x‖ ^ 2) rudinMeasure := by
    simpa using (Lp.memLp f).integrable_norm_pow two_ne_zero
  have h_int_tendsto : Tendsto (fun A : ℝ =>
      ∫ x, ‖(Icc (-A) A).indicator (f : ℝ → ℂ) x - (f : ℝ → ℂ) x‖ ^ 2 ∂rudinMeasure)
      atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) ∂rudinMeasure := by simp
    rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖(f : ℝ → ℂ) x‖ ^ 2)
      (Eventually.of_forall fun A => ?_)
      (Eventually.of_forall fun A => ae_of_all _ fun x => ?_)
      hint_sq
      (ae_of_all _ fun x => ?_)
    · exact ((((Lp.aestronglyMeasurable f).indicator measurableSet_Icc).sub
        (Lp.aestronglyMeasurable f)).norm.pow 2)
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      by_cases hx : x ∈ Icc (-A) A <;> simp [hx]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ici_mem_atTop |x|] with A (hA : |x| ≤ A)
      have hx : x ∈ Icc (-A) A := abs_le.mp hA
      simp [hx]
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp h_int_tendsto
  rw [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun A => ?_
  dsimp only [Function.comp_def]
  rw [← hnorm_sq A, Real.sqrt_sq (norm_nonneg _)]

/-- 9.13 (forward truncated-integral `L²` convergence): For every `f ∈ L²(m)` and `A ∈ ℝ`,
`φ_A(t) = ∫_{-A}^A f(x) e^(-i x t) dm(x)` belongs to `L²(m)` and `‖φ_A - f̂‖₂ → 0` as `A → ∞`. -/
theorem theorem_9_13_truncated_forward_memLp (f : RudinLp 2) (A : ℝ) :
    MemLp (rudinTruncatedFourier f A) 2 rudinMeasure := by
  have hf1 : Integrable ((Icc (-A) A).indicator (f : ℝ → ℂ)) rudinMeasure :=
    indicator_Icc_integrable_of_L2 f A
  have hf2 : MemLp ((Icc (-A) A).indicator (f : ℝ → ℂ)) 2 rudinMeasure :=
    (Lp.memLp f).indicator measurableSet_Icc
  have hae := theorem_9_13_L1_L2_compat hf1 hf2
  rw [← rudinTruncatedFourier_eq_indicator] at hae
  exact (Lp.memLp _).ae_eq hae

theorem theorem_9_13_truncated_forward_tendsto (f : RudinLp 2) :
    Tendsto (fun A : ℝ =>
      ‖(theorem_9_13_truncated_forward_memLp f A).toLp (rudinTruncatedFourier f A) -
        rudinPlancherel f‖) atTop (𝓝 0) := by
  have heq : ∀ A : ℝ,
      (theorem_9_13_truncated_forward_memLp f A).toLp (rudinTruncatedFourier f A) =
        rudinPlancherel (((Lp.memLp f).indicator measurableSet_Icc).toLp
          ((Icc (-A) A).indicator (f : ℝ → ℂ))) := by
    intro A
    apply Lp.ext
    have hf1 := indicator_Icc_integrable_of_L2 f A
    have hf2 : MemLp ((Icc (-A) A).indicator (f : ℝ → ℂ)) 2 rudinMeasure :=
      (Lp.memLp f).indicator measurableSet_Icc
    have hae := theorem_9_13_L1_L2_compat hf1 hf2
    rw [← rudinTruncatedFourier_eq_indicator] at hae
    exact (theorem_9_13_truncated_forward_memLp f A).coeFn_toLp.trans hae.symm
  simp_rw [heq, ← map_sub, LinearIsometryEquiv.norm_map]
  exact tendsto_iff_norm_sub_tendsto_zero.mp (indicator_Icc_toLp_tendsto f)

/-- 9.13 (inverse truncated-integral `L²` convergence): For every `f ∈ L²(m)` and `A ∈ ℝ`,
`ψ_A(x) = ∫_{-A}^A f̂(t) e^(i x t) dm(t)` belongs to `L²(m)` and `‖ψ_A - f‖₂ → 0` as `A → ∞`. -/
theorem theorem_9_13_truncated_inverse_memLp (f : RudinLp 2) (A : ℝ) :
    MemLp (rudinTruncatedFourierInv (rudinPlancherel f) A) 2 rudinMeasure := by
  have hg1 : Integrable ((Icc (-A) A).indicator (rudinPlancherel f : ℝ → ℂ)) rudinMeasure :=
    indicator_Icc_integrable_of_L2 (rudinPlancherel f) A
  have hg2 : MemLp ((Icc (-A) A).indicator (rudinPlancherel f : ℝ → ℂ)) 2 rudinMeasure :=
    (Lp.memLp (rudinPlancherel f)).indicator measurableSet_Icc
  have hae := theorem_9_13_inv_L1_L2_compat hg1 hg2
  rw [← rudinTruncatedFourierInv_eq_indicator] at hae
  exact (Lp.memLp _).ae_eq hae

theorem theorem_9_13_truncated_inverse_tendsto (f : RudinLp 2) :
    Tendsto (fun A : ℝ =>
      ‖(theorem_9_13_truncated_inverse_memLp f A).toLp
        (rudinTruncatedFourierInv (rudinPlancherel f) A) - f‖) atTop (𝓝 0) := by
  have heq : ∀ A : ℝ,
      (theorem_9_13_truncated_inverse_memLp f A).toLp
        (rudinTruncatedFourierInv (rudinPlancherel f) A) =
        rudinPlancherel.symm (((Lp.memLp (rudinPlancherel f)).indicator measurableSet_Icc).toLp
          ((Icc (-A) A).indicator (rudinPlancherel f : ℝ → ℂ))) := by
    intro A
    apply Lp.ext
    have hg1 := indicator_Icc_integrable_of_L2 (rudinPlancherel f) A
    have hg2 : MemLp ((Icc (-A) A).indicator (rudinPlancherel f : ℝ → ℂ)) 2 rudinMeasure :=
      (Lp.memLp (rudinPlancherel f)).indicator measurableSet_Icc
    have hae := theorem_9_13_inv_L1_L2_compat hg1 hg2
    rw [← rudinTruncatedFourierInv_eq_indicator] at hae
    exact (theorem_9_13_truncated_inverse_memLp f A).coeFn_toLp.trans hae.symm
  have hf_symm : ∀ A : ℝ,
      ‖rudinPlancherel.symm (((Lp.memLp (rudinPlancherel f)).indicator measurableSet_Icc).toLp
        ((Icc (-A) A).indicator (rudinPlancherel f : ℝ → ℂ))) - f‖ =
        ‖(((Lp.memLp (rudinPlancherel f)).indicator measurableSet_Icc).toLp
          ((Icc (-A) A).indicator (rudinPlancherel f : ℝ → ℂ))) - rudinPlancherel f‖ := by
    intro A
    let uA : RudinLp 2 :=
      ((Lp.memLp (rudinPlancherel f)).indicator measurableSet_Icc).toLp
        ((Icc (-A) A).indicator (rudinPlancherel f : ℝ → ℂ))
    change ‖rudinPlancherel.symm uA - f‖ = ‖uA - rudinPlancherel f‖
    calc
      ‖rudinPlancherel.symm uA - f‖ =
          ‖rudinPlancherel (rudinPlancherel.symm uA - f)‖ :=
        (rudinPlancherel.norm_map _).symm
      _ = ‖uA - rudinPlancherel f‖ := by
        rw [map_sub, rudinPlancherel.apply_symm_apply]
  simp_rw [heq, hf_symm]
  exact tendsto_iff_norm_sub_tendsto_zero.mp (indicator_Icc_toLp_tendsto (rudinPlancherel f))

/-- 9.13: `L¹(m) ∩ L²(m)` is dense in `L²(m)`. -/
theorem theorem_9_13_dense_L1_inter_L2 :
    Dense {f : RudinLp 2 | Integrable (f : ℝ → ℂ) rudinMeasure} := by
  intro f
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun n : ℕ => ((Lp.memLp f).indicator measurableSet_Icc).toLp
    ((Icc (-(n : ℝ)) (n : ℝ)).indicator (f : ℝ → ℂ)), fun n => ?_, ?_⟩
  · dsimp
    exact (integrable_congr (((Lp.memLp f).indicator measurableSet_Icc).coeFn_toLp)).mpr
      (indicator_Icc_integrable_of_L2 f (n : ℝ))
  · exact (indicator_Icc_toLp_tendsto f).comp tendsto_natCast_atTop_atTop

/-- 9.13 (uniqueness of the Plancherel extension): `rudinPlancherel` is the unique continuous map
`L²(m) → L²(m)` agreeing `m`-almost everywhere with `rudinFourier` on `L¹(m) ∩ L²(m)`. -/
theorem theorem_9_13_unique (Φ : RudinLp 2 → RudinLp 2) (hΦ_cont : Continuous Φ)
    (hΦ_compat : ∀ f : RudinLp 2, Integrable (f : ℝ → ℂ) rudinMeasure →
      (Φ f : ℝ → ℂ) =ᵐ[rudinMeasure] rudinFourier (f : ℝ → ℂ)) :
    Φ = rudinPlancherel := by
  refine Continuous.ext_on theorem_9_13_dense_L1_inter_L2 hΦ_cont rudinPlancherel.continuous ?_
  intro f (hf1 : Integrable (f : ℝ → ℂ) rudinMeasure)
  apply Lp.ext
  have h1 := hΦ_compat f hf1
  have h2 := theorem_9_13_L1_L2_compat hf1 (Lp.memLp f)
  have htoLp : (Lp.memLp f).toLp (f : ℝ → ℂ) = f := Lp.toLp_coeFn f (Lp.memLp f)
  rw [htoLp] at h2
  exact h1.trans h2.symm

/-- 9.14: If `f ∈ L²(m)` and its Plancherel transform `f̂` belongs to `L¹(m)` (without requiring
`f ∈ L¹(m)`), then `f(x) = ∫ f̂(t) e^(i x t) dm(t)` almost everywhere `[m]` (and the RHS is in
`C₀(ℝ)`). -/
theorem theorem_9_14 (f : RudinLp 2) (hhat : Integrable (rudinPlancherel f) rudinMeasure) :
    IsVanishingAtInfty (rudinFourierInv (rudinPlancherel f)) ∧
      (f : ℝ → ℂ) =ᵐ[rudinMeasure] rudinFourierInv (rudinPlancherel f) := by
  have hg_cont : Continuous (rudinFourierInv (rudinPlancherel f)) := by
    have h : rudinFourierInv (rudinPlancherel f) =
        fun x : ℝ => rudinFourier (rudinPlancherel f) (-x) := by
      ext x; exact rudinFourierInv_eq_rudinFourier_neg _ x
    rw [h]
    exact (theorem_9_6_continuous hhat).comp continuous_neg
  have hg_zero : Tendsto (rudinFourierInv (rudinPlancherel f)) (cocompact ℝ) (𝓝 0) := by
    have h : rudinFourierInv (rudinPlancherel f) =
        fun x : ℝ => rudinFourier (rudinPlancherel f) (-x) := by
      ext x; exact rudinFourierInv_eq_rudinFourier_neg _ x
    rw [h]
    exact (theorem_9_6_zero_at_infty _).comp
      (Homeomorph.neg ℝ).toCocompactMap.cocompact_tendsto'
  refine ⟨isVanishingAtInfty_iff_cocompact.mpr ⟨hg_cont, hg_zero⟩, ?_⟩
  have hinv := theorem_9_13_inv_L1_L2_compat hhat (Lp.memLp (rudinPlancherel f))
  have htoLp : (Lp.memLp (rudinPlancherel f)).toLp (rudinPlancherel f : ℝ → ℂ) =
      rudinPlancherel f := Lp.toLp_coeFn (rudinPlancherel f) (Lp.memLp (rudinPlancherel f))
  rw [htoLp, rudinPlancherel.symm_apply_apply] at hinv
  exact hinv

/-- 9.15 (canonical pointwise representative on `L¹ ∩ L²` vs a.e. class on `L²`):
(1) When `f ∈ L¹(m) ∩ L²(m)`, `rudinFourier f` is the unique continuous representative in the
`m`-a.e. equivalence class of `rudinPlancherel (hf2.toLp f)`.
(2) For general `f ∈ L²(m)`, `rudinPlancherel f` is determined only modulo `m`-null sets; in
particular, altering any representative at a single point `t₀` changes its value at `t₀` while
remaining a valid representative of the `L²` Fourier transform `rudinPlancherel f`. -/
theorem remark_9_15_canonical_continuous {f : ℝ → ℂ} (hf1 : Integrable f rudinMeasure)
    (hf2 : MemLp f 2 rudinMeasure) (h : ℝ → ℂ) :
    (Continuous h ∧ h =ᵐ[rudinMeasure] rudinPlancherel (hf2.toLp f)) ↔ h = rudinFourier f := by
  constructor
  · rintro ⟨hcont, hae⟩
    have hae' : h =ᵐ[rudinMeasure] rudinFourier f :=
      hae.trans (theorem_9_13_L1_L2_compat hf1 hf2)
    exact (hcont.ae_eq_iff_eq rudinMeasure (theorem_9_6_continuous hf1)).mp hae'
  · rintro rfl
    exact ⟨theorem_9_6_continuous hf1, (theorem_9_13_L1_L2_compat hf1 hf2).symm⟩

theorem remark_9_15_ae_indeterminacy (f : RudinLp 2) (t₀ : ℝ) (z : ℂ) :
    MemLp (Function.update (rudinPlancherel f : ℝ → ℂ) t₀ z) 2 rudinMeasure ∧
      Function.update (rudinPlancherel f : ℝ → ℂ) t₀ z =ᵐ[rudinMeasure] rudinPlancherel f ∧
      Function.update (rudinPlancherel f : ℝ → ℂ) t₀ z t₀ = z := by
  have hae : Function.update (rudinPlancherel f : ℝ → ℂ) t₀ z =ᵐ[rudinMeasure]
      (rudinPlancherel f : ℝ → ℂ) := by
    rw [EventuallyEq, ae_iff]
    refine measure_mono_null (fun t ht => ?_) (measure_singleton (μ := rudinMeasure) t₀)
    by_contra hne
    exact ht (Function.update_of_ne hne _ _)
  exact ⟨(Lp.memLp (rudinPlancherel f)).ae_eq hae.symm, hae, by simp⟩

end Node9_13_to_9_15

/-! ## §9.16–9.17: Translation-Invariant Subspaces of `L²` -/

section Node9_16_9_17

/-- 9.16: A subspace `M` of `L²(m)` is translation-invariant if `f ∈ M` implies `f_α ∈ M`
(`f_α(x) = f(x - α)`) for every real `α`. -/
def IsTranslationInvariant (M : Submodule ℂ (RudinLp 2)) : Prop :=
  ∀ α : ℝ, ∀ f ∈ M, rudinTranslateLp 2 α f ∈ M

/-- Pointwise multiplication by `t ↦ e^(-i α t)`. -/
def charMulFun (α : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  g t * Complex.exp (-Complex.I * α * t)

private lemma charMulFun_memLp (α : ℝ) {g : ℝ → ℂ} (hg : MemLp g 2 rudinMeasure) :
    MemLp (charMulFun α g) 2 rudinMeasure := by
  have hcont : Continuous (fun t : ℝ => Complex.exp (-Complex.I * α * t)) := by fun_prop
  have hm : AEStronglyMeasurable (charMulFun α g) rudinMeasure :=
    hg.aestronglyMeasurable.mul hcont.aestronglyMeasurable
  rw [memLp_iff]
  have heq : eLpNorm (charMulFun α g) 2 rudinMeasure = eLpNorm g 2 rudinMeasure := by
    refine eLpNorm_congr_norm_ae hm hg.aestronglyMeasurable (ae_of_all _ fun t => ?_)
    dsimp [charMulFun]
    rw [norm_mul, norm_exp_neg_I_mul_mul, mul_one]
  rw [heq]
  exact hg

/-- Unitary multiplication operator on `L²(m)` sending `g(t)` to `g(t) e^(-i α t)`. -/
def charMulLinearIsometry (α : ℝ) : RudinLp 2 →ₗᵢ[ℂ] RudinLp 2 where
  toFun g := (charMulFun_memLp α (Lp.memLp g)).toLp (charMulFun α g)
  map_add' g₁ g₂ := by
    apply Lp.ext
    filter_upwards [(charMulFun_memLp α (Lp.memLp (g₁ + g₂))).coeFn_toLp,
      Lp.coeFn_add ((charMulFun_memLp α (Lp.memLp g₁)).toLp _)
        ((charMulFun_memLp α (Lp.memLp g₂)).toLp _),
      (charMulFun_memLp α (Lp.memLp g₁)).coeFn_toLp,
      (charMulFun_memLp α (Lp.memLp g₂)).coeFn_toLp,
      Lp.coeFn_add g₁ g₂] with t ht_sum ht_add ht1 ht2 h12
    rw [ht_sum, ht_add, Pi.add_apply, ht1, ht2]
    unfold charMulFun
    rw [h12, Pi.add_apply, add_mul]
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [(charMulFun_memLp α (Lp.memLp (c • g))).coeFn_toLp,
      Lp.coeFn_smul c ((charMulFun_memLp α (Lp.memLp g)).toLp _),
      (charMulFun_memLp α (Lp.memLp g)).coeFn_toLp,
      Lp.coeFn_smul c g] with t ht_smul1 ht_smul2 ht hc
    rw [ht_smul1]
    change charMulFun α (↑(c • g)) t =
      (c • (charMulFun_memLp α (Lp.memLp g)).toLp (charMulFun α g) : RudinLp 2) t
    rw [ht_smul2, Pi.smul_apply, ht]
    unfold charMulFun
    rw [hc, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
  norm_map' g := by
    change ‖(charMulFun_memLp α (Lp.memLp g)).toLp (charMulFun α g)‖ = ‖g‖
    rw [Lp.norm_toLp, Lp.norm_def]
    congr 1
    refine eLpNorm_congr_norm_ae
      (charMulFun_memLp α (Lp.memLp g)).aestronglyMeasurable
      (Lp.aestronglyMeasurable g)
      (ae_of_all _ fun t => ?_)
    dsimp [charMulFun]
    rw [norm_mul, norm_exp_neg_I_mul_mul, mul_one]

/-- 9.16: Unitary character-multiplication equivalence on `L²(m)` multiplying by `e^(-i α t)`. -/
def charMulL2 (α : ℝ) : RudinLp 2 ≃ₗᵢ[ℂ] RudinLp 2 :=
  LinearIsometryEquiv.ofLinearIsometry
    (charMulLinearIsometry α)
    (charMulLinearIsometry (-α)).toLinearMap
    (by
      ext g : 1
      apply Lp.ext
      change ((charMulFun_memLp α (Lp.memLp (charMulLinearIsometry (-α) g))).toLp
        (charMulFun α (charMulLinearIsometry (-α) g)) : ℝ → ℂ) =ᵐ[rudinMeasure] g
      filter_upwards [(charMulFun_memLp α (Lp.memLp (charMulLinearIsometry (-α) g))).coeFn_toLp,
        (charMulFun_memLp (-α) (Lp.memLp g)).coeFn_toLp] with t ht1 ht2
      rw [ht1]
      unfold charMulFun
      change ((charMulFun_memLp (-α) (Lp.memLp g)).toLp (charMulFun (-α) g) : ℝ → ℂ) t *
        Complex.exp (-Complex.I * ↑α * ↑t) = (g : ℝ → ℂ) t
      rw [ht2]
      dsimp [charMulFun]
      rw [mul_assoc, ← Complex.exp_add]
      have h0 : -Complex.I * ↑(-α) * ↑t + -Complex.I * ↑α * ↑t = 0 := by push_cast; ring
      rw [h0, Complex.exp_zero, mul_one])
    (by
      ext g : 1
      apply Lp.ext
      change ((charMulFun_memLp (-α) (Lp.memLp (charMulLinearIsometry α g))).toLp
        (charMulFun (-α) (charMulLinearIsometry α g)) : ℝ → ℂ) =ᵐ[rudinMeasure] g
      filter_upwards [(charMulFun_memLp (-α) (Lp.memLp (charMulLinearIsometry α g))).coeFn_toLp,
        (charMulFun_memLp α (Lp.memLp g)).coeFn_toLp] with t ht1 ht2
      rw [ht1]
      unfold charMulFun
      change ((charMulFun_memLp α (Lp.memLp g)).toLp (charMulFun α g) : ℝ → ℂ) t *
        Complex.exp (-Complex.I * ↑(-α) * ↑t) = (g : ℝ → ℂ) t
      rw [ht2]
      dsimp [charMulFun]
      rw [mul_assoc, ← Complex.exp_add]
      have h0 : -Complex.I * ↑α * ↑t + -Complex.I * ↑(-α) * ↑t = 0 := by push_cast; ring
      rw [h0, Complex.exp_zero, mul_one])

theorem charMulL2_coeFn (α : ℝ) (g : RudinLp 2) :
    (charMulL2 α g : ℝ → ℂ) =ᵐ[rudinMeasure]
      fun t : ℝ => (g : ℝ → ℂ) t * Complex.exp (-Complex.I * α * t) :=
  (charMulFun_memLp α (Lp.memLp g)).coeFn_toLp

/-- 9.16: Plancherel intertwines translation by `α` on `L²(m)` with multiplication by `e^(-i α t)`. -/
theorem theorem_9_16_plancherel_translate (α : ℝ) (f : RudinLp 2) :
    rudinPlancherel (rudinTranslateLp 2 α f) = charMulL2 α (rudinPlancherel f) := by
  have hlhs_cont : Continuous (fun h : RudinLp 2 => rudinPlancherel (rudinTranslateLp 2 α h)) :=
    rudinPlancherel.continuous.comp (rudinTranslateLp 2 α).continuous
  have hrhs_cont : Continuous (fun h : RudinLp 2 => charMulL2 α (rudinPlancherel h)) :=
    (charMulL2 α).continuous.comp rudinPlancherel.continuous
  refine congr_fun (Continuous.ext_on theorem_9_13_dense_L1_inter_L2 hlhs_cont hrhs_cont ?_) f
  intro h (hh1 : Integrable (h : ℝ → ℂ) rudinMeasure)
  apply Lp.ext
  have htr1 : Integrable (fun x : ℝ => (h : ℝ → ℂ) (x - α)) rudinMeasure :=
    (measurePreserving_sub_right rudinMeasure α).integrable_comp_of_integrable hh1
  have htr2 : MemLp (fun x : ℝ => (h : ℝ → ℂ) (x - α)) 2 rudinMeasure :=
    (Lp.memLp h).comp_measurePreserving (measurePreserving_sub_right rudinMeasure α)
  have htr_toLp : htr2.toLp (fun x : ℝ => (h : ℝ → ℂ) (x - α)) = rudinTranslateLp 2 α h := by
    apply Lp.ext
    exact htr2.coeFn_toLp.trans (rudinTranslateLp_coeFn 2 α h).symm
  have hlhs_ae := theorem_9_13_L1_L2_compat htr1 htr2
  rw [htr_toLp] at hlhs_ae
  have hh_toLp : (Lp.memLp h).toLp (h : ℝ → ℂ) = h := Lp.toLp_coeFn h (Lp.memLp h)
  have hcompat_h := theorem_9_13_L1_L2_compat hh1 (Lp.memLp h)
  rw [hh_toLp] at hcompat_h
  filter_upwards [hlhs_ae, charMulL2_coeFn α (rudinPlancherel h), hcompat_h] with t ht1 ht2 ht3
  rw [ht1, theorem_9_2_b hh1 α t, ht2, ht3]

/-- 9.16: Under `rudinPlancherel`, closed translation-invariant subspaces `M ⊆ L²(m)` correspond
to closed subspaces `Y ⊆ L²(m)` invariant under multiplication by all characters `e^(-i α t)`. -/
theorem theorem_9_16_invariant_iff (M : Submodule ℂ (RudinLp 2)) :
    let Y : Submodule ℂ (RudinLp 2) := M.map rudinPlancherel.toLinearEquiv.toLinearMap
    (IsClosed (M : Set (RudinLp 2)) ↔ IsClosed (Y : Set (RudinLp 2))) ∧
      (IsTranslationInvariant M ↔ ∀ α : ℝ, ∀ g ∈ Y, charMulL2 α g ∈ Y) := by
  intro Y
  have hset : (Y : Set (RudinLp 2)) = rudinPlancherel '' (M : Set (RudinLp 2)) := rfl
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact (rudinPlancherel.toHomeomorph.isClosed_image (s := (M : Set (RudinLp 2)))).symm
  · constructor
    · intro hM α g hg
      rcases hg with ⟨f, hfM, rfl⟩
      exact ⟨rudinTranslateLp 2 α f, hM α f hfM, theorem_9_16_plancherel_translate α f⟩
    · intro hY α f hfM
      have hgY : rudinPlancherel f ∈ Y := ⟨f, hfM, rfl⟩
      have hcharY : charMulL2 α (rudinPlancherel f) ∈ Y := hY α _ hgY
      rw [← theorem_9_16_plancherel_translate α f] at hcharY
      rcases hcharY with ⟨f', hf'M, hf'_eq⟩
      rwa [rudinPlancherel.injective hf'_eq] at hf'M

/-- 9.16 (core orthogonality lemma): If `Y ⊆ L²(m)` is invariant under `charMulL2 α` for all
`α ∈ ℝ`, then for every `h ∈ Y` and `w ∈ Yᗮ`, `(w * h)(t) = 0` `m`-almost everywhere. -/
theorem theorem_9_16_orthogonal_mul_ae_zero {Y : Submodule ℂ (RudinLp 2)}
    (hY_inv : ∀ α : ℝ, ∀ g ∈ Y, charMulL2 α g ∈ Y)
    {h w : RudinLp 2} (hh : h ∈ Y) (hw : w ∈ Yᗮ) :
    ∀ᵐ t ∂rudinMeasure, (w : ℝ → ℂ) t * (h : ℝ → ℂ) t = 0 := by
  let q : ℝ → ℂ := fun t => inner ℂ ((h : ℝ → ℂ) t) ((w : ℝ → ℂ) t)
  have hq_int : Integrable q rudinMeasure := L2.integrable_inner (𝕜 := ℂ) h w
  have hq_hat : ∀ s : ℝ, rudinFourier q s = 0 := by
    intro s
    have hmem : charMulL2 (-s) h ∈ Y := hY_inv (-s) h hh
    have horth : inner ℂ (charMulL2 (-s) h) w = 0 := (Y.mem_orthogonal w).mp hw _ hmem
    rw [L2.inner_def] at horth
    have heq : rudinFourier q s =
        ∫ t, inner ℂ ((charMulL2 (-s) h : ℝ → ℂ) t) ((w : ℝ → ℂ) t) ∂rudinMeasure := by
      unfold rudinFourier
      apply integral_congr_ae
      filter_upwards [charMulL2_coeFn (-s) h] with t ht
      change (w : ℝ → ℂ) t * conj ((h : ℝ → ℂ) t) * Complex.exp (-Complex.I * (t : ℂ) * (s : ℂ)) =
        (w : ℝ → ℂ) t * conj ((charMulL2 (-s) h : ℝ → ℂ) t)
      rw [ht, map_mul, ← Complex.exp_conj]
      have hexp : conj (-Complex.I * ↑(-s) * (t : ℂ)) = -Complex.I * (t : ℂ) * (s : ℂ) := by
        push_cast
        simp
        ring
      rw [hexp]
      ring
    rw [heq, horth]
  filter_upwards [theorem_9_12 hq_int hq_hat] with t ht
  change (w : ℝ → ℂ) t * conj ((h : ℝ → ℂ) t) = 0 at ht
  simp only [mul_eq_zero, map_eq_zero] at ht
  rcases ht with hw0 | hh0
  · simp [hw0]
  · simp [hh0]

private lemma rudinH_memLp_two : MemLp (fun t : ℝ => (rudinH t : ℂ)) 2 rudinMeasure := by
  have hm : AEStronglyMeasurable (fun t : ℝ => (rudinH t : ℂ)) rudinMeasure :=
    (Complex.continuous_ofReal.comp continuous_rudinH).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine (rudinH_scaled_integrable two_pos).congr (ae_of_all _ fun t => ?_)
  dsimp [rudinH]
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 1
  push_cast
  rw [abs_mul, abs_of_pos two_pos]
  ring

/-- 9.16 (orthogonal projection multiplier theorem): For any closed character-invariant subspace
`Y` of `L²(m)`, there exists a Borel measurable set `E ⊆ ℝ` such that the orthogonal projection
`P : L²(m) →L[ℂ] L²(m)` onto `Y` is given almost everywhere by multiplication by the `{0, 1}`-valued
characteristic function `ψ = 1_{Eᶜ}` (`(P g)(t) = ψ(t) g(t)` a.e. `[m]` for every `g ∈ L²(m)`). -/
theorem theorem_9_16_projection_multiplier (Y : Submodule ℂ (RudinLp 2))
    (hY_closed : IsClosed (Y : Set (RudinLp 2)))
    (hY_inv : ∀ α : ℝ, ∀ g ∈ Y, charMulL2 α g ∈ Y) :
    have : CompleteSpace Y := hY_closed.isComplete.completeSpace_coe
    ∃ E : Set ℝ, MeasurableSet E ∧
      ∀ g : RudinLp 2,
        (Y.starProjection g : ℝ → ℂ) =ᵐ[rudinMeasure]
          fun t : ℝ => Eᶜ.indicator (1 : ℝ → ℂ) t * (g : ℝ → ℂ) t := by
  have : CompleteSpace Y := hY_closed.isComplete.completeSpace_coe
  let K0 : RudinLp 2 := rudinH_memLp_two.toLp (fun t : ℝ => (rudinH t : ℂ))
  let u0 : RudinLp 2 := Y.starProjection K0
  let w0 : RudinLp 2 := K0 - u0
  have hu0_mem : u0 ∈ Y := Y.starProjection_apply_mem K0
  have hw0_mem : w0 ∈ Yᗮ := Submodule.sub_starProjection_mem_orthogonal K0
  let u_rep : ℝ → ℂ := (Lp.aestronglyMeasurable u0).mk u0
  have hu_meas : Measurable u_rep := (Lp.aestronglyMeasurable u0).stronglyMeasurable_mk.measurable
  have hu_ae : (u0 : ℝ → ℂ) =ᵐ[rudinMeasure] u_rep := (Lp.aestronglyMeasurable u0).ae_eq_mk
  let E : Set ℝ := {t : ℝ | u_rep t = 0}
  have hE_meas : MeasurableSet E := hu_meas (measurableSet_singleton 0)
  refine ⟨E, hE_meas, ?_⟩
  let ψ : ℝ → ℂ := Eᶜ.indicator 1
  have hH_ne : ∀ t : ℝ, (rudinH t : ℂ) ≠ 0 :=
    fun t => Complex.ofReal_ne_zero.mpr (theorem_9_7_H_bounds t).1.ne'
  have hw0_u0 := theorem_9_16_orthogonal_mul_ae_zero hY_inv hu0_mem hw0_mem
  have hu0_w0_id : ∀ᵐ t ∂rudinMeasure,
      (u0 : ℝ → ℂ) t = ψ t * (rudinH t : ℂ) ∧
        (w0 : ℝ → ℂ) t = (1 - ψ t) * (rudinH t : ℂ) := by
    filter_upwards [hw0_u0, Lp.coeFn_sub K0 u0, rudinH_memLp_two.coeFn_toLp, hu_ae]
      with t hprod hw_sub hK0 hu_eq
    rw [hw_sub, Pi.sub_apply, hK0, hu_eq] at hprod
    by_cases htE : t ∈ E
    · have hurep0 : u_rep t = 0 := htE
      have hψ0 : ψ t = 0 := by simp [ψ, htE]
      refine ⟨by rw [hu_eq, hurep0, hψ0, zero_mul], ?_⟩
      rw [hw_sub, Pi.sub_apply, hK0, hu_eq, hurep0, sub_zero, hψ0, sub_zero, one_mul]
    · have hurep_ne : u_rep t ≠ 0 := htE
      have hsub0 : (rudinH t : ℂ) - u_rep t = 0 :=
        (mul_eq_zero.mp hprod).resolve_right hurep_ne
      have hurep_eq : u_rep t = (rudinH t : ℂ) := (sub_eq_zero.mp hsub0).symm
      have hψ1 : ψ t = 1 := by simp [ψ, htE]
      refine ⟨by rw [hu_eq, hurep_eq, hψ1, one_mul], ?_⟩
      rw [hw_sub, Pi.sub_apply, hK0, hu_eq, hurep_eq, sub_self, hψ1, sub_self, zero_mul]
  intro g
  have horth1 := theorem_9_16_orthogonal_mul_ae_zero hY_inv hu0_mem
    (Submodule.sub_starProjection_mem_orthogonal g)
  have horth2 := theorem_9_16_orthogonal_mul_ae_zero hY_inv
    (Y.starProjection_apply_mem g) hw0_mem
  filter_upwards [hu0_w0_id, horth1, horth2, Lp.coeFn_sub g (Y.starProjection g)]
    with t ⟨hu_id, hw_id⟩ h1 h2 hgsub
  rw [hgsub, Pi.sub_apply, hu_id, ← mul_assoc] at h1
  have h1' : ((g : ℝ → ℂ) t - (Y.starProjection g : ℝ → ℂ) t) * ψ t = 0 :=
    (mul_eq_zero.mp h1).resolve_right (hH_ne t)
  rw [hw_id, mul_right_comm] at h2
  have h2' : (1 - ψ t) * (Y.starProjection g : ℝ → ℂ) t = 0 :=
    (mul_eq_zero.mp h2).resolve_right (hH_ne t)
  linear_combination -h1' + h2'

/-- 9.17: For any set `E ⊆ ℝ`, `rudinSubspace E` (`M_E`) is the space of all `f ∈ L²(m)` such that
`f̂(t) = 0` almost everywhere on `E`. -/
def rudinSubspace (E : Set ℝ) : Submodule ℂ (RudinLp 2) where
  carrier := {f : RudinLp 2 | ∀ᵐ t ∂rudinMeasure, t ∈ E → (rudinPlancherel f : ℝ → ℂ) t = 0}
  zero_mem' := by
    change ∀ᵐ t ∂rudinMeasure, t ∈ E → (rudinPlancherel 0 : ℝ → ℂ) t = 0
    rw [map_zero]
    filter_upwards [Lp.coeFn_zero ℂ 2 rudinMeasure] with t ht _
    exact ht
  add_mem' {f₁ f₂} hf₁ hf₂ := by
    change ∀ᵐ t ∂rudinMeasure, t ∈ E → (rudinPlancherel (f₁ + f₂) : ℝ → ℂ) t = 0
    rw [map_add]
    filter_upwards [Lp.coeFn_add (rudinPlancherel f₁) (rudinPlancherel f₂), hf₁, hf₂]
      with t hadd h1 h2 htE
    rw [hadd, Pi.add_apply, h1 htE, h2 htE, add_zero]
  smul_mem' c {f} hf := by
    change ∀ᵐ t ∂rudinMeasure, t ∈ E → (rudinPlancherel (c • f) : ℝ → ℂ) t = 0
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul c (rudinPlancherel f), hf] with t hsmul h1 htE
    rw [hsmul, Pi.smul_apply, h1 htE, smul_zero]

theorem mem_rudinSubspace_iff_ae_restrict {E : Set ℝ} (hE : MeasurableSet E) (f : RudinLp 2) :
    f ∈ rudinSubspace E ↔ ∀ᵐ t ∂(rudinMeasure.restrict E), (rudinPlancherel f : ℝ → ℂ) t = 0 :=
  (ae_restrict_iff' hE).symm

/-- 9.17: Every `rudinSubspace E` is translation-invariant. -/
theorem rudinSubspace_isTranslationInvariant (E : Set ℝ) :
    IsTranslationInvariant (rudinSubspace E) := by
  intro α f hf
  change ∀ᵐ t ∂rudinMeasure, t ∈ E →
    (rudinPlancherel (rudinTranslateLp 2 α f) : ℝ → ℂ) t = 0
  rw [theorem_9_16_plancherel_translate α f]
  filter_upwards [charMulL2_coeFn α (rudinPlancherel f), hf] with t ht h0 htE
  rw [ht, h0 htE, zero_mul]

/-- 9.17: For every measurable set `E ⊆ ℝ`, `rudinSubspace E` is a closed subspace of `L²(m)`. -/
theorem rudinSubspace_isClosed {E : Set ℝ} (hE : MeasurableSet E) :
    IsClosed (rudinSubspace E : Set (RudinLp 2)) := by
  let multLin : RudinLp 2 →ₗ[ℂ] RudinLp 2 :=
    { toFun := fun g => ((Lp.memLp g).indicator hE).toLp (E.indicator (g : ℝ → ℂ))
      map_add' := fun g₁ g₂ => by
        apply Lp.ext
        filter_upwards [((Lp.memLp (g₁ + g₂)).indicator hE).coeFn_toLp,
          Lp.coeFn_add (((Lp.memLp g₁).indicator hE).toLp _) (((Lp.memLp g₂).indicator hE).toLp _),
          ((Lp.memLp g₁).indicator hE).coeFn_toLp,
          ((Lp.memLp g₂).indicator hE).coeFn_toLp,
          Lp.coeFn_add g₁ g₂] with t h1 h2 h3 h4 h5
        rw [h1, h2, Pi.add_apply, h3, h4]
        by_cases htE : t ∈ E
        · rw [indicator_of_mem htE, indicator_of_mem htE, indicator_of_mem htE, h5, Pi.add_apply]
        · simp [htE]
      map_smul' := fun c g => by
        apply Lp.ext
        filter_upwards [((Lp.memLp (c • g)).indicator hE).coeFn_toLp,
          Lp.coeFn_smul c (((Lp.memLp g).indicator hE).toLp _),
          ((Lp.memLp g).indicator hE).coeFn_toLp,
          Lp.coeFn_smul c g] with t h1 h2 h3 h4
        rw [h1]
        change E.indicator (↑(c • g)) t =
          (c • ((Lp.memLp g).indicator hE).toLp (E.indicator (g : ℝ → ℂ)) : RudinLp 2) t
        rw [h2, Pi.smul_apply, h3]
        by_cases htE : t ∈ E
        · rw [indicator_of_mem htE, indicator_of_mem htE, h4, Pi.smul_apply]
        · simp [htE] }
  let multCLM : RudinLp 2 →L[ℂ] RudinLp 2 :=
    multLin.mkContinuous 1 fun g => by
      change ‖((Lp.memLp g).indicator hE).toLp (E.indicator (g : ℝ → ℂ))‖ ≤ 1 * ‖g‖
      rw [one_mul, Lp.norm_toLp, Lp.norm_def]
      refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top g) ?_
      exact eLpNorm_indicator_le (g : ℝ → ℂ) hE
  have hpre : (rudinSubspace E : Set (RudinLp 2)) =
      (fun f : RudinLp 2 => multCLM (rudinPlancherel f)) ⁻¹' {0} := by
    ext f
    simp only [SetLike.mem_coe, mem_preimage, mem_singleton_iff]
    change (∀ᵐ t ∂rudinMeasure, t ∈ E → (rudinPlancherel f : ℝ → ℂ) t = 0) ↔
      ((Lp.memLp (rudinPlancherel f)).indicator hE).toLp
        (E.indicator (rudinPlancherel f : ℝ → ℂ)) = 0
    rw [Lp.ext_iff]
    constructor
    · intro hf
      filter_upwards [((Lp.memLp (rudinPlancherel f)).indicator hE).coeFn_toLp,
        Lp.coeFn_zero ℂ 2 rudinMeasure, hf] with t h1 h2 h0
      rw [h1, h2, Pi.zero_apply]
      by_cases htE : t ∈ E
      · simp [htE, h0 htE]
      · simp [htE]
    · intro hzero
      filter_upwards [((Lp.memLp (rudinPlancherel f)).indicator hE).coeFn_toLp,
        Lp.coeFn_zero ℂ 2 rudinMeasure, hzero] with t h1 h2 heq htE
      rw [h1, h2, Pi.zero_apply] at heq
      simpa [htE] using heq
  rw [hpre]
  exact isClosed_singleton.preimage (multCLM.continuous.comp rudinPlancherel.continuous)

/-- 9.17 (existence): Every closed translation-invariant subspace `M` of `L²(m)` is of the form
`rudinSubspace E` for some Borel measurable set `E ⊆ ℝ`. -/
theorem theorem_9_17_exists (M : Submodule ℂ (RudinLp 2))
    (hM_closed : IsClosed (M : Set (RudinLp 2))) (hM_inv : IsTranslationInvariant M) :
    ∃ E : Set ℝ, MeasurableSet E ∧ M = rudinSubspace E := by
  let Y : Submodule ℂ (RudinLp 2) := M.map rudinPlancherel.toLinearEquiv.toLinearMap
  have hY_closed : IsClosed (Y : Set (RudinLp 2)) :=
    (theorem_9_16_invariant_iff M).1.mp hM_closed
  have hY_inv : ∀ α : ℝ, ∀ g ∈ Y, charMulL2 α g ∈ Y :=
    (theorem_9_16_invariant_iff M).2.mp hM_inv
  have : CompleteSpace Y := hY_closed.isComplete.completeSpace_coe
  obtain ⟨E, hE_meas, hproj⟩ := theorem_9_16_projection_multiplier Y hY_closed hY_inv
  refine ⟨E, hE_meas, ?_⟩
  ext f
  have hf_iff_Y : f ∈ M ↔ rudinPlancherel f ∈ Y := by
    constructor
    · intro hfM; exact ⟨f, hfM, rfl⟩
    · rintro ⟨f', hf'M, heq⟩
      rwa [rudinPlancherel.injective heq] at hf'M
  rw [hf_iff_Y, ← Submodule.starProjection_eq_self_iff (K := Y), Lp.ext_iff]
  change (Y.starProjection (rudinPlancherel f) : ℝ → ℂ) =ᵐ[rudinMeasure] rudinPlancherel f ↔
    ∀ᵐ t ∂rudinMeasure, t ∈ E → (rudinPlancherel f : ℝ → ℂ) t = 0
  constructor
  · intro heq
    filter_upwards [heq, hproj (rudinPlancherel f)] with t ht1 ht2 htE
    rw [ht1] at ht2
    simpa [htE] using ht2
  · intro hzero
    filter_upwards [hproj (rudinPlancherel f), hzero] with t ht2 h0
    rw [ht2]
    by_cases htE : t ∈ E
    · simp [htE, h0 htE]
    · simp [htE]

/-- 9.17 (uniqueness modulo null symmetric difference): For measurable sets `A, B ⊆ ℝ`,
`M_A = M_B` if and only if `m((A \ B) ∪ (B \ A)) = 0` (`m(symmDiff A B) = 0`). -/
theorem theorem_9_17_unique {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (rudinSubspace A = rudinSubspace B ↔ rudinMeasure (symmDiff A B) = 0) ∧
      (rudinSubspace A = rudinSubspace B ↔ rudinMeasure ((A \ B) ∪ (B \ A)) = 0) := by
  have hsymm : symmDiff A B = (A \ B) ∪ (B \ A) := symmDiff_def A B
  suffices hmain : rudinSubspace A = rudinSubspace B ↔ rudinMeasure ((A \ B) ∪ (B \ A)) = 0 by
    exact ⟨hsymm ▸ hmain, hmain⟩
  have hle_diff : ∀ {S T : Set ℝ}, MeasurableSet S → MeasurableSet T →
      rudinSubspace T ≤ rudinSubspace S → rudinMeasure (S \ T) = 0 := by
    intro S T hS hT hle
    have hcover : S \ T = ⋃ n : ℕ, (S \ T) ∩ Icc (-(n : ℝ)) (n : ℝ) := by
      ext t
      simp only [mem_iUnion, mem_inter_iff, mem_Icc]
      refine ⟨fun ht => ?_, fun ⟨_, ht, _⟩ => ht⟩
      obtain ⟨n, hn⟩ := exists_nat_ge |t|
      exact ⟨n, ht, abs_le.mp hn⟩
    rw [hcover, measure_iUnion_null_iff]
    intro n
    let Kn : Set ℝ := (S \ T) ∩ Icc (-(n : ℝ)) (n : ℝ)
    have hKn_meas : MeasurableSet Kn := (hS.diff hT).inter measurableSet_Icc
    have hKn_fin : rudinMeasure Kn ≠ ∞ :=
      ((measure_mono inter_subset_right).trans_lt isCompact_Icc.measure_lt_top).ne
    let g : RudinLp 2 := indicatorConstLp 2 (s := Kn) hKn_meas hKn_fin (1 : ℂ)
    have hg_ae : (g : ℝ → ℂ) =ᵐ[rudinMeasure] Kn.indicator fun _ => (1 : ℂ) :=
      indicatorConstLp_coeFn
    let f : RudinLp 2 := rudinPlancherel.symm g
    have hf_plan : rudinPlancherel f = g := rudinPlancherel.apply_symm_apply g
    have hfT : f ∈ rudinSubspace T := by
      change ∀ᵐ t ∂rudinMeasure, t ∈ T → (rudinPlancherel f : ℝ → ℂ) t = 0
      rw [hf_plan]
      filter_upwards [hg_ae] with t ht htT
      rw [ht]
      have hnot : t ∉ Kn := fun hmem => hmem.1.2 htT
      simp [hnot]
    have hfS : f ∈ rudinSubspace S := hle hfT
    change ∀ᵐ t ∂rudinMeasure, t ∈ S → (rudinPlancherel f : ℝ → ℂ) t = 0 at hfS
    rw [hf_plan] at hfS
    have hae_not : ∀ᵐ t ∂rudinMeasure, t ∉ Kn := by
      filter_upwards [hg_ae, hfS] with t ht h0 htKn
      have h1 : (g : ℝ → ℂ) t = 1 := by rw [ht]; simp [htKn]
      have h2 : (g : ℝ → ℂ) t = 0 := h0 htKn.1.1
      exact one_ne_zero (h1.symm.trans h2)
    simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hae_not
  constructor
  · intro hAB
    exact measure_union_null (hle_diff hA hB hAB.ge) (hle_diff hB hA hAB.le)
  · intro hnull
    have hAB_null : rudinMeasure (A \ B) = 0 :=
      measure_mono_null subset_union_left hnull
    have hBA_null : rudinMeasure (B \ A) = 0 :=
      measure_mono_null subset_union_right hnull
    have hae_AB : ∀ᵐ t ∂rudinMeasure, t ∉ A \ B := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using hAB_null
    have hae_BA : ∀ᵐ t ∂rudinMeasure, t ∉ B \ A := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using hBA_null
    ext f
    change (∀ᵐ t ∂rudinMeasure, t ∈ A → (rudinPlancherel f : ℝ → ℂ) t = 0) ↔
      ∀ᵐ t ∂rudinMeasure, t ∈ B → (rudinPlancherel f : ℝ → ℂ) t = 0
    constructor
    · intro hfA
      filter_upwards [hfA, hae_BA] with t h0 hnot htB
      exact h0 (by_contra fun htA => hnot ⟨htB, htA⟩)
    · intro hfB
      filter_upwards [hfB, hae_AB] with t h0 hnot htA
      exact h0 (by_contra fun htB => hnot ⟨htA, htB⟩)

/-- 9.17 (Full classification of closed translation-invariant subspaces of `L²(m)`):
(1) For every measurable set `E ⊆ ℝ`, `rudinSubspace E` is closed and translation-invariant.
(2) Every closed translation-invariant subspace `M` of `L²(m)` equals `rudinSubspace E` for some
measurable set `E ⊆ ℝ`.
(3) `rudinSubspace A = rudinSubspace B` iff `m((A \ B) ∪ (B \ A)) = 0`. -/
theorem theorem_9_17 :
    (∀ E : Set ℝ, MeasurableSet E →
      IsClosed (rudinSubspace E : Set (RudinLp 2)) ∧
        IsTranslationInvariant (rudinSubspace E)) ∧
    (∀ M : Submodule ℂ (RudinLp 2),
      IsClosed (M : Set (RudinLp 2)) → IsTranslationInvariant M →
        ∃ E : Set ℝ, MeasurableSet E ∧ M = rudinSubspace E) ∧
    (∀ A B : Set ℝ, MeasurableSet A → MeasurableSet B →
      (rudinSubspace A = rudinSubspace B ↔ rudinMeasure ((A \ B) ∪ (B \ A)) = 0)) :=
  ⟨fun E hE => ⟨rudinSubspace_isClosed hE, rudinSubspace_isTranslationInvariant E⟩,
   theorem_9_17_exists,
   fun _ _ hA hB => (theorem_9_17_unique hA hB).2⟩

end Node9_16_9_17

/-! ## §9.18–9.23: Banach Algebras, Complex Homomorphisms, and the Character Space of `L¹` -/

section Node9_18_to_9_23

/-- 9.18: A complex Banach algebra in Rudin's sense (p. 190): a complete complex normed space
equipped with an associative bilinear multiplication satisfying `‖x * y‖ ≤ ‖x‖ * ‖y‖`
(no multiplicative unit required). -/
class IsRudinBanachAlgebra (A : Type*) [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A] : Prop where
  submultiplicative : ∀ x y : A, ‖x * y‖ ≤ ‖x‖ * ‖y‖

instance instIsRudinBanachAlgebra (A : Type*) [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A] :
    IsRudinBanachAlgebra A :=
  ⟨norm_mul_le⟩

/-- 9.18: Explicit verification of all printed Banach-algebra axioms (associativity, left and right
distributivity, scalar-multiplication bilinearity, submultiplicative norm, and completeness). -/
theorem theorem_9_18_axioms (A : Type*) [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A] [IsRudinBanachAlgebra A] :
    (∀ x y z : A, (x * y) * z = x * (y * z)) ∧
    (∀ x y z : A, x * (y + z) = x * y + x * z) ∧
    (∀ x y z : A, (x + y) * z = x * z + y * z) ∧
    (∀ (c : ℂ) (x y : A), c • (x * y) = (c • x) * y ∧ c • (x * y) = x * (c • y)) ∧
    (∀ x y : A, ‖x * y‖ ≤ ‖x‖ * ‖y‖) ∧
    CompleteSpace A :=
  ⟨mul_assoc, left_distrib, right_distrib,
   fun c x y => ⟨(smul_mul_assoc c x y).symm, (mul_smul_comm c x y).symm⟩,
   IsRudinBanachAlgebra.submultiplicative, inferInstance⟩

/-- 9.19(a): For any compact Hausdorff space `X`, `C(X, ℂ)` with pointwise operations and supremum
norm is a commutative complex Banach algebra with multiplicative identity `1`. -/
theorem theorem_9_19_a (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    IsRudinBanachAlgebra C(X, ℂ) ∧
      (∀ f g : C(X, ℂ), f * g = g * f) ∧
      (∀ f : C(X, ℂ), (1 : C(X, ℂ)) * f = f ∧ f * (1 : C(X, ℂ)) = f) :=
  ⟨inferInstance, mul_comm, fun f => ⟨one_mul f, mul_one f⟩⟩

theorem theorem_9_19_a_norm_one (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Nonempty X] : ‖(1 : C(X, ℂ))‖ = 1 :=
  norm_one

private lemma rudinC0_strictly_nonzero : ∃ f₀ : RudinC0, ∀ x : ℝ, f₀ x ≠ 0 := by
  have hfH_real : Integrable (fun t : ℝ => rudinH (1 * t)) rudinMeasure :=
    rudinH_scaled_integrable one_pos
  have hfH : Integrable (fun t : ℝ => (rudinH (1 * t) : ℂ)) rudinMeasure :=
    Complex.ofRealCLM.integrable_comp hfH_real
  refine ⟨rudinFourierC0 hfH, fun x => ?_⟩
  have heq : (rudinFourierC0 hfH : ℝ → ℂ) x = (rudinPoisson 1 (-x) : ℂ) := by
    change rudinFourier (fun t : ℝ => (rudinH (1 * t) : ℂ)) x = (rudinPoisson 1 (-x) : ℂ)
    rw [← theorem_9_7_poisson_formula one_pos (-x)]
    unfold rudinFourier rudinPoissonInt
    congr 1
    ext t
    congr 2
    push_cast
    ring
  rw [heq]
  exact Complex.ofReal_ne_zero.mpr (rudinPoisson_pos one_pos (-x)).ne'

/-- 9.19(b): `C₀(ℝ)` (`RudinC0`) with pointwise multiplication and supremum norm is a commutative
complex Banach algebra possessing no multiplicative unit. -/
theorem theorem_9_19_b :
    IsRudinBanachAlgebra RudinC0 ∧
      (∀ f g : RudinC0, f * g = g * f) ∧
      (¬ ∃ e : RudinC0, ∀ f : RudinC0, e * f = f) ∧
      (¬ ∃ e : RudinC0, ∀ f : RudinC0, f * e = f) := by
  have hno_left : ¬ ∃ e : RudinC0, ∀ f : RudinC0, e * f = f := by
    rintro ⟨e, he⟩
    obtain ⟨f₀, hf₀_ne⟩ := rudinC0_strictly_nonzero
    have hef₀ : e * f₀ = f₀ := he f₀
    have he_one : ∀ x : ℝ, e x = 1 := by
      intro x
      have hx : e x * f₀ x = 1 * f₀ x := by
        simpa only [one_mul, ZeroAtInftyContinuousMap.mul_apply] using
          congr_arg (fun g : RudinC0 => g x) hef₀
      exact mul_right_cancel₀ (hf₀_ne x) hx
    have hvan : IsVanishingAtInfty e :=
      isVanishingAtInfty_iff_cocompact.mpr ⟨e.continuous, zero_at_infty e⟩
    obtain ⟨K, hK_cpt, hK_lt⟩ := hvan.2 1 zero_lt_one
    obtain ⟨R, hR⟩ := hK_cpt.isBounded.subset_closedBall (0 : ℝ)
    let x₀ : ℝ := max R 0 + 1
    have hx₀_not : x₀ ∉ K := by
      intro hxK
      have hdist : dist x₀ 0 ≤ R := mem_closedBall.mp (hR hxK)
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at hdist
      linarith [le_max_left R 0]
    have hlt := hK_lt x₀ hx₀_not
    rw [he_one x₀, norm_one] at hlt
    exact lt_irrefl (1 : ℝ) hlt
  refine ⟨inferInstance, mul_comm, hno_left, ?_⟩
  rintro ⟨e, he⟩
  exact hno_left ⟨e, fun f => by rw [mul_comm, he f]⟩

/-- 9.19(c): Bounded linear endomorphisms `E →L[ℂ] E` of any complex Banach space `E` form a
complex Banach algebra with identity `ContinuousLinearMap.id ℂ E`. -/
theorem theorem_9_19_c_banachAlgebra (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] :
    IsRudinBanachAlgebra (E →L[ℂ] E) ∧
      (∀ T : E →L[ℂ] E, (1 : E →L[ℂ] E) * T = T ∧ T * (1 : E →L[ℂ] E) = T) :=
  ⟨inferInstance, fun T => ⟨one_mul T, mul_one T⟩⟩

/-- 9.19(c) (noncommutativity on `ℝ^k` for `k > 1`): Bounded linear operators on `ℝ^k` (`k > 1`)
are noncommutative. -/
theorem theorem_9_19_c_noncomm_real {k : ℕ} (hk : 1 < k) :
    ∃ A B : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ), A * B ≠ B * A := by
  let i₀ : Fin k := ⟨0, by omega⟩
  let i₁ : Fin k := ⟨1, hk⟩
  have h10 : i₁ ≠ i₀ := by simp [i₀, i₁]
  let A : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
    (ContinuousLinearMap.proj i₀).smulRight (Pi.single i₀ (1 : ℝ))
  let B : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
    (ContinuousLinearMap.proj i₁).smulRight (Pi.single i₀ (1 : ℝ))
  refine ⟨A, B, fun heq => ?_⟩
  let v : Fin k → ℝ := Pi.single i₁ (1 : ℝ)
  have hv := congr_fun (congr_arg (fun T : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) => (T v : Fin k → ℝ)) heq) i₀
  simp [A, B, v, Pi.single_eq_of_ne h10] at hv

/-- 9.19(c) (noncommutativity on `ℂ^k` for `k > 1`): Bounded complex-linear operators on `ℂ^k`
(`k > 1`) form a noncommutative complex Banach algebra. -/
theorem theorem_9_19_c_noncomm_complex {k : ℕ} (hk : 1 < k) :
    ∃ A B : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ), A * B ≠ B * A := by
  let i₀ : Fin k := ⟨0, by omega⟩
  let i₁ : Fin k := ⟨1, hk⟩
  have h10 : i₁ ≠ i₀ := by simp [i₀, i₁]
  let A : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ) :=
    (ContinuousLinearMap.proj i₀).smulRight (Pi.single i₀ (1 : ℂ))
  let B : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ) :=
    (ContinuousLinearMap.proj i₁).smulRight (Pi.single i₀ (1 : ℂ))
  refine ⟨A, B, fun heq => ?_⟩
  let v : Fin k → ℂ := Pi.single i₁ (1 : ℂ)
  have hv := congr_fun (congr_arg (fun T : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ) => (T v : Fin k → ℂ)) heq) i₀
  simp [A, B, v, Pi.single_eq_of_ne h10] at hv

/-- 9.19(d): Type wrapper equipping `L¹(m)` (`RudinLp 1`) with Rudin's convolution multiplication
`(f * g)(x) = ∫ f(x - y) g(y) dm(y)`. -/
@[ext]
structure RudinL1Algebra where
  ofLp ::
  toLp : RudinLp 1

namespace RudinL1Algebra

instance : AddCommGroup RudinL1Algebra where
  zero := ⟨0⟩
  add f g := ⟨f.toLp + g.toLp⟩
  neg f := ⟨-f.toLp⟩
  sub f g := ⟨f.toLp - g.toLp⟩
  nsmul n f := ⟨n • f.toLp⟩
  zsmul n f := ⟨n • f.toLp⟩
  add_assoc a b c := RudinL1Algebra.ext (add_assoc a.toLp b.toLp c.toLp)
  zero_add a := RudinL1Algebra.ext (zero_add a.toLp)
  add_zero a := RudinL1Algebra.ext (add_zero a.toLp)
  nsmul_zero a := RudinL1Algebra.ext (zero_smul ℕ a.toLp)
  nsmul_succ n a := RudinL1Algebra.ext (succ_nsmul a.toLp n)
  zsmul_zero' a := RudinL1Algebra.ext (zero_smul ℤ a.toLp)
  zsmul_succ' n a := RudinL1Algebra.ext (SubNegMonoid.zsmul_succ' n a.toLp)
  zsmul_neg' n a := RudinL1Algebra.ext (SubNegMonoid.zsmul_neg' n a.toLp)
  neg_add_cancel a := RudinL1Algebra.ext (neg_add_cancel a.toLp)
  add_comm a b := RudinL1Algebra.ext (add_comm a.toLp b.toLp)
  sub_eq_add_neg a b := RudinL1Algebra.ext (sub_eq_add_neg a.toLp b.toLp)

@[simp] theorem toLp_zero : (0 : RudinL1Algebra).toLp = 0 := rfl
@[simp] theorem toLp_add (f g : RudinL1Algebra) : (f + g).toLp = f.toLp + g.toLp := rfl
@[simp] theorem toLp_neg (f : RudinL1Algebra) : (-f).toLp = -f.toLp := rfl
@[simp] theorem toLp_sub (f g : RudinL1Algebra) : (f - g).toLp = f.toLp - g.toLp := rfl

def toLpAddEquiv : RudinL1Algebra ≃+ RudinLp 1 where
  toFun := toLp
  invFun := ofLp
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

instance : NormedAddCommGroup RudinL1Algebra :=
  NormedAddCommGroup.induced RudinL1Algebra (RudinLp 1) toLpAddEquiv toLpAddEquiv.injective

@[simp] theorem norm_toLp (f : RudinL1Algebra) : ‖f.toLp‖ = ‖f‖ := rfl
@[simp] theorem norm_ofLp (f : RudinLp 1) : ‖ofLp f‖ = ‖f‖ := rfl

instance : SMul ℂ RudinL1Algebra where
  smul c f := ⟨c • f.toLp⟩

@[simp] theorem toLp_smul (c : ℂ) (f : RudinL1Algebra) : (c • f).toLp = c • f.toLp := rfl

instance : NormedSpace ℂ RudinL1Algebra where
  one_smul a := RudinL1Algebra.ext (one_smul ℂ a.toLp)
  mul_smul c d a := RudinL1Algebra.ext (mul_smul c d a.toLp)
  smul_zero c := RudinL1Algebra.ext (smul_zero c)
  smul_add c a b := RudinL1Algebra.ext (smul_add c a.toLp b.toLp)
  add_smul c d a := RudinL1Algebra.ext (add_smul c d a.toLp)
  zero_smul a := RudinL1Algebra.ext (zero_smul ℂ a.toLp)
  norm_smul_le c a := norm_smul_le c a.toLp

instance : CompleteSpace RudinL1Algebra := by
  have hiso : Isometry (toLpAddEquiv.toEquiv : RudinL1Algebra → RudinLp 1) := fun _ _ => rfl
  exact (completeSpace_congr hiso.isUniformEmbedding).mpr inferInstance

end RudinL1Algebra

private lemma rudinConv_eq_mathlib_conv (u v : ℝ → ℂ) :
    rudinConv u v = u ⋆[ContinuousLinearMap.mul ℂ ℂ, rudinMeasure] v := by
  ext x
  exact (MeasureTheory.convolution_mul_swap (𝕜 := ℂ) (μ := rudinMeasure)).symm

private lemma rudinL1_conv_memLp (f g : RudinLp 1) :
    MemLp (rudinConv f g) 1 rudinMeasure := by
  rw [memLp_one_iff_integrable, rudinConv_eq_mathlib_conv]
  exact (L1.integrable_coeFn f).integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (L1.integrable_coeFn g)

instance : Mul RudinL1Algebra where
  mul f g := RudinL1Algebra.ofLp ((rudinL1_conv_memLp f.toLp g.toLp).toLp (rudinConv f.toLp g.toLp))

theorem rudinL1Algebra_mul_coeFn (f g : RudinL1Algebra) :
    ((f * g).toLp : ℝ → ℂ) =ᵐ[rudinMeasure] rudinConv f.toLp g.toLp :=
  (rudinL1_conv_memLp f.toLp g.toLp).coeFn_toLp

private lemma rudinFourierCLM_mul (f g : RudinL1Algebra) :
    rudinFourierCLM (f * g).toLp = rudinFourierCLM f.toLp * rudinFourierCLM g.toLp := by
  ext t
  change rudinFourier (f * g).toLp t = rudinFourier f.toLp t * rudinFourier g.toLp t
  rw [rudinFourier_congr_ae (rudinL1Algebra_mul_coeFn f g),
    (theorem_9_2_c (L1.integrable_coeFn f.toLp) (L1.integrable_coeFn g.toLp)).2 t]

private lemma rudinL1Algebra_norm_mul_le (f g : RudinL1Algebra) :
    ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
  change ‖(rudinL1_conv_memLp f.toLp g.toLp).toLp (rudinConv f.toLp g.toLp)‖ ≤
    ‖f.toLp‖ * ‖g.toLp‖
  rw [Lp.norm_toLp, L1.norm_eq_integral_norm f.toLp, L1.norm_eq_integral_norm g.toLp]
  have hnorm_toReal : (eLpNorm (rudinConv f.toLp g.toLp) 1 rudinMeasure).toReal =
      ∫ x, ‖rudinConv f.toLp g.toLp x‖ ∂rudinMeasure := by
    have hm := rudinL1_conv_memLp f.toLp g.toLp
    rw [← Lp.norm_toLp (f := rudinConv f.toLp g.toLp) (hf := hm), L1.norm_eq_integral_norm]
    exact integral_congr_ae (hm.coeFn_toLp.mono fun x hx => congr_arg norm hx)
  rw [hnorm_toReal]
  let uf : ℝ → ℝ := fun x => ‖(f.toLp : ℝ → ℂ) x‖
  let ug : ℝ → ℝ := fun x => ‖(g.toLp : ℝ → ℂ) x‖
  have huf : Integrable uf rudinMeasure := (L1.integrable_coeFn f.toLp).norm
  have hug : Integrable ug rudinMeasure := (L1.integrable_coeFn g.toLp).norm
  have hconv_int : Integrable (uf ⋆[ContinuousLinearMap.mul ℝ ℝ, rudinMeasure] ug) rudinMeasure :=
    huf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hug
  have hpt : ∀ x : ℝ, ‖rudinConv f.toLp g.toLp x‖ ≤
      (uf ⋆[ContinuousLinearMap.mul ℝ ℝ, rudinMeasure] ug) x := by
    intro x
    rw [MeasureTheory.convolution_mul_swap]
    unfold rudinConv
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    congr 1
    ext y
    exact norm_mul _ _
  have hle := integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) hconv_int
    (ae_of_all _ hpt)
  have hint_eq := MeasureTheory.integral_convolution (ContinuousLinearMap.mul ℝ ℝ) huf hug
  simpa only [ContinuousLinearMap.mul_apply'] using hle.trans_eq hint_eq

instance : NonUnitalNormedCommRing RudinL1Algebra where
  left_distrib a b c := by
    apply RudinL1Algebra.ext
    apply rudinFourierCLM_injective
    simp [rudinFourierCLM_mul, mul_add]
  right_distrib a b c := by
    apply RudinL1Algebra.ext
    apply rudinFourierCLM_injective
    simp [rudinFourierCLM_mul, add_mul]
  zero_mul a := by
    apply RudinL1Algebra.ext
    apply rudinFourierCLM_injective
    simp [rudinFourierCLM_mul]
  mul_zero a := by
    apply RudinL1Algebra.ext
    apply rudinFourierCLM_injective
    simp [rudinFourierCLM_mul]
  mul_assoc a b c := by
    apply RudinL1Algebra.ext
    apply rudinFourierCLM_injective
    simp [rudinFourierCLM_mul, mul_assoc]
  mul_comm a b := by
    apply RudinL1Algebra.ext
    apply rudinFourierCLM_injective
    simp [rudinFourierCLM_mul, mul_comm]
  dist_eq x y := by rw [dist_eq_norm, ← norm_neg, neg_sub, sub_eq_add_neg, add_comm]
  norm_mul_le := rudinL1Algebra_norm_mul_le

instance : IsScalarTower ℂ RudinL1Algebra RudinL1Algebra where
  smul_assoc c a b := by
    apply RudinL1Algebra.ext
    apply rudinFourierCLM_injective
    simp [rudinFourierCLM_mul, smul_mul_assoc]

instance : SMulCommClass ℂ RudinL1Algebra RudinL1Algebra where
  smul_comm c a b := by
    apply RudinL1Algebra.ext
    apply rudinFourierCLM_injective
    simp [rudinFourierCLM_mul, mul_smul_comm]

/-- 9.19(d): The Fourier transform bundled as a non-unital complex algebra homomorphism
`L¹(m) →ₙₐ[ℂ] C₀(ℝ)`. -/
def rudinFourierAlgHom : RudinL1Algebra →ₙₐ[ℂ] RudinC0 where
  toFun f := rudinFourierCLM f.toLp
  map_mul' := rudinFourierCLM_mul
  map_zero' := by simp
  map_add' f g := by simp
  map_smul' c f := by simp

@[simp]
theorem rudinFourierAlgHom_apply (f : RudinL1Algebra) (t : ℝ) :
    rudinFourierAlgHom f t = rudinFourier f.toLp t := rfl

/-- 9.19(d): `L¹(m)` with convolution is a commutative complex Banach algebra with no
multiplicative unit, and `f ↦ f̂` (`rudinFourierAlgHom`) is an injective algebra isomorphism of
`L¹(m)` onto a subalgebra of `C₀(ℝ)`. -/
theorem theorem_9_19_d :
    IsRudinBanachAlgebra RudinL1Algebra ∧
      (∀ f g : RudinL1Algebra, f * g = g * f) ∧
      Function.Injective rudinFourierAlgHom ∧
      (∀ f : RudinL1Algebra, ‖rudinFourierAlgHom f‖ ≤ ‖f‖) ∧
      (¬ ∃ e : RudinL1Algebra, ∀ f : RudinL1Algebra, e * f = f) ∧
      (¬ ∃ e : RudinL1Algebra, ∀ f : RudinL1Algebra, f * e = f) := by
  have hinj : Function.Injective rudinFourierAlgHom := fun f g h =>
    RudinL1Algebra.ext (rudinFourierCLM_injective h)
  have hnorm : ∀ f : RudinL1Algebra, ‖rudinFourierAlgHom f‖ ≤ ‖f‖ := fun f => by
    change ‖rudinFourierCLM f.toLp‖ ≤ ‖f.toLp‖
    have h1 := rudinFourierCLM.le_opNorm f.toLp
    have h2 := mul_le_mul_of_nonneg_right rudinFourierCLM_norm_le_one (norm_nonneg f.toLp)
    exact h1.trans (by simpa only [one_mul] using h2)
  have hno_left : ¬ ∃ e : RudinL1Algebra, ∀ f : RudinL1Algebra, e * f = f := by
    rintro ⟨e, he⟩
    have hfH_real : Integrable (fun t : ℝ => rudinH (1 * t)) rudinMeasure :=
      rudinH_scaled_integrable one_pos
    have hfH : Integrable (fun t : ℝ => (rudinH (1 * t) : ℂ)) rudinMeasure :=
      Complex.ofRealCLM.integrable_comp hfH_real
    let f₀ : RudinL1Algebra :=
      RudinL1Algebra.ofLp ((memLp_one_iff_integrable.mpr hfH).toLp
        (fun t : ℝ => (rudinH (1 * t) : ℂ)))
    have hf₀_hat : ∀ t : ℝ, rudinFourierAlgHom f₀ t ≠ 0 := by
      intro t
      change rudinFourier f₀.toLp t ≠ 0
      rw [rudinFourier_congr_ae (memLp_one_iff_integrable.mpr hfH).coeFn_toLp]
      have heq : rudinFourier (fun s : ℝ => (rudinH (1 * s) : ℂ)) t =
          (rudinPoisson 1 (-t) : ℂ) := by
        rw [← theorem_9_7_poisson_formula one_pos (-t)]
        unfold rudinFourier rudinPoissonInt
        congr 1; ext s; congr 2; push_cast; ring
      rw [heq]
      exact Complex.ofReal_ne_zero.mpr (rudinPoisson_pos one_pos (-t)).ne'
    have hmul_eq : rudinFourierAlgHom e * rudinFourierAlgHom f₀ = rudinFourierAlgHom f₀ := by
      rw [← map_mul, he f₀]
    have he_one : ∀ t : ℝ, rudinFourierAlgHom e t = 1 := by
      intro t
      have ht : rudinFourierAlgHom e t * rudinFourierAlgHom f₀ t =
          1 * rudinFourierAlgHom f₀ t := by
        simpa only [one_mul, ZeroAtInftyContinuousMap.mul_apply] using
          congr_arg (fun g : RudinC0 => g t) hmul_eq
      exact mul_right_cancel₀ (hf₀_hat t) ht
    have hvan : IsVanishingAtInfty (rudinFourierAlgHom e) :=
      isVanishingAtInfty_iff_cocompact.mpr
        ⟨(rudinFourierAlgHom e).continuous, zero_at_infty (rudinFourierAlgHom e)⟩
    obtain ⟨K, hK_cpt, hK_lt⟩ := hvan.2 1 zero_lt_one
    obtain ⟨R, hR⟩ := hK_cpt.isBounded.subset_closedBall (0 : ℝ)
    let t₀ : ℝ := max R 0 + 1
    have ht₀_not : t₀ ∉ K := by
      intro htK
      have hdist : dist t₀ 0 ≤ R := mem_closedBall.mp (hR htK)
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at hdist
      linarith [le_max_left R 0]
    have hlt := hK_lt t₀ ht₀_not
    rw [he_one t₀, norm_one] at hlt
    exact lt_irrefl (1 : ℝ) hlt
  refine ⟨inferInstance, mul_comm, hinj, hnorm, hno_left, ?_⟩
  rintro ⟨e, he⟩
  exact hno_left ⟨e, fun f => by rw [mul_comm, he f]⟩

/-- 9.20: A complex homomorphism on a complex algebra `A` is a complex-linear multiplicative
functional `A →ₙₐ[ℂ] ℂ` (including the zero homomorphism `0`, with **no** continuity or
boundedness assumed in the definition). -/
abbrev RudinComplexHom (A : Type*) [NonUnitalSemiring A] [Module ℂ A] :=
  A →ₙₐ[ℂ] ℂ

theorem theorem_9_20_zero_mem (A : Type*) [NonUnitalSemiring A] [Module ℂ A] :
    ∃ h : RudinComplexHom A, ∀ x : A, h x = 0 :=
  ⟨0, fun _ => rfl⟩

/-- 9.21: Every complex homomorphism `h` on a complex Banach algebra `A` (even when `A` has no
multiplicative unit, and with no continuity assumed a priori) satisfies `‖h x‖ ≤ ‖x‖` for every
`x ∈ A`, hence is continuous with operator norm at most `1`. -/
theorem theorem_9_21_apply_le {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]
    (h : RudinComplexHom A) (x : A) :
    ‖h x‖ ≤ ‖x‖ := by
  let φ : WithLp 1 (Unitization ℂ A) →ₐ[ℂ] ℂ :=
    (Unitization.lift h).comp (WithLp.unitizationAlgEquiv ℂ (𝕜 := ℂ) (A := A)).toAlgHom
  let u : WithLp 1 (Unitization ℂ A) := WithLp.toLp 1 (x : Unitization ℂ A)
  have hφu : φ u = h x := by
    simp [φ, u, Unitization.lift_apply]
  rw [← hφu, ← WithLp.unitization_norm_inr (𝕜 := ℂ) x]
  exact AlgHom.norm_apply_le_self φ u

/-- 9.21: Bundled continuous linear functional `A →L[ℂ] ℂ` associated to any complex homomorphism
`h : RudinComplexHom A`, proved continuous via `theorem_9_21_apply_le`. -/
def rudinComplexHomToCLM {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]
    (h : RudinComplexHom A) : A →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := h
      map_add' := map_add h
      map_smul' := map_smul h }
    1
    fun x => by
      change ‖h x‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using theorem_9_21_apply_le h x

@[simp]
theorem rudinComplexHomToCLM_apply {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]
    (h : RudinComplexHom A) (x : A) :
    rudinComplexHomToCLM h x = h x := rfl

theorem theorem_9_21 {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]
    (h : RudinComplexHom A) :
    (∀ x : A, ‖h x‖ ≤ ‖x‖) ∧ Continuous h ∧ ‖rudinComplexHomToCLM h‖ ≤ 1 := by
  have hcont : Continuous h := by
    have hcoe : (rudinComplexHomToCLM h : A → ℂ) = h := by
      ext x; exact rudinComplexHomToCLM_apply h x
    rw [← hcoe]
    exact (rudinComplexHomToCLM h).continuous
  refine ⟨theorem_9_21_apply_le h, hcont, ?_⟩
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

private lemma integrable_mul_of_ae_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u v : α → ℂ} (hu : Integrable u μ) (hv_meas : AEStronglyMeasurable v μ)
    (C : ℝ) (hv : ∀ᵐ x ∂μ, ‖v x‖ ≤ C) :
    Integrable (fun x => u x * v x) μ := by
  refine (hu.norm.mul_const (max C 0)).mono' (hu.aestronglyMeasurable.mul hv_meas) ?_
  filter_upwards [hv] with x hx
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hx.trans (le_max_left C 0)) (norm_nonneg _)

/-- Auxiliary local Riesz representation on a single unit interval `Ico (n : ℝ) (n + 1)` for a
continuous linear functional `Λ : L¹(m) →L[ℂ] ℂ`. -/
private lemma L1_dual_unit_interval (Λ : RudinLp 1 →L[ℂ] ℂ) (n : ℤ) :
    ∃ βn : ℝ → ℂ, Measurable βn ∧ (∀ x : ℝ, ‖βn x‖ ≤ ‖Λ‖) ∧
      ∀ g : ℝ → ℂ, Measurable g → (∀ x : ℝ, ‖g x‖ ≤ 1 → True) →
        (∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, ‖g x‖ ≤ M) →
        (∀ x : ℝ, x ∉ Ico (n : ℝ) (n + 1) → g x = 0) →
        ∀ hg1 : MemLp g 1 rudinMeasure,
          Λ (hg1.toLp g) = ∫ x in Ico (n : ℝ) (n + 1), g x * βn x ∂rudinMeasure := by
  let In : Set ℝ := Ico (n : ℝ) (n + 1)
  have hIn_meas : MeasurableSet In := measurableSet_Ico
  have hIn_lt_top : rudinMeasure In < ∞ :=
    (measure_mono Ico_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top
  let μn : Measure ℝ := rudinMeasure.restrict In
  have : IsFiniteMeasure μn := ⟨by rw [Measure.restrict_apply_univ]; exact hIn_lt_top⟩
  have hmem1_of_L2 : ∀ u : Lp ℂ 2 μn, MemLp (In.indicator (u : ℝ → ℂ)) 1 rudinMeasure := by
    intro u
    rw [memLp_iff, eLpNorm_indicator_eq_eLpNorm_restrict hIn_meas]
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ one_le_two (Lp.aestronglyMeasurable u)).trans_lt ?_
    exact ENNReal.mul_lt_top (Lp.memLp u)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_lt_top μn univ).ne)
  let ιLin : Lp ℂ 2 μn →ₗ[ℂ] RudinLp 1 :=
    { toFun := fun u => (hmem1_of_L2 u).toLp (In.indicator (u : ℝ → ℂ))
      map_add' := fun u₁ u₂ => by
        apply Lp.ext
        have hadd_μn : ((u₁ + u₂ : Lp ℂ 2 μn) : ℝ → ℂ) =ᵐ[μn] u₁ + u₂ := Lp.coeFn_add u₁ u₂
        rw [EventuallyEq, ae_restrict_iff' hIn_meas] at hadd_μn
        filter_upwards [(hmem1_of_L2 (u₁ + u₂)).coeFn_toLp,
          Lp.coeFn_add ((hmem1_of_L2 u₁).toLp _) ((hmem1_of_L2 u₂).toLp _),
          (hmem1_of_L2 u₁).coeFn_toLp, (hmem1_of_L2 u₂).coeFn_toLp, hadd_μn]
          with x h1 h2 h3 h4 h5
        rw [h1, h2, Pi.add_apply, h3, h4]
        by_cases hx : x ∈ In
        · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx, h5 hx, Pi.add_apply]
        · simp [hx]
      map_smul' := fun c u => by
        apply Lp.ext
        have hsmul_μn : ((c • u : Lp ℂ 2 μn) : ℝ → ℂ) =ᵐ[μn] c • (u : ℝ → ℂ) :=
          Lp.coeFn_smul c u
        rw [EventuallyEq, ae_restrict_iff' hIn_meas] at hsmul_μn
        filter_upwards [(hmem1_of_L2 (c • u)).coeFn_toLp,
          Lp.coeFn_smul c ((hmem1_of_L2 u).toLp _),
          (hmem1_of_L2 u).coeFn_toLp, hsmul_μn] with x h1 h2 h3 h4
        rw [h1]
        change In.indicator (↑(c • u)) x =
          (c • (hmem1_of_L2 u).toLp (In.indicator (u : ℝ → ℂ)) : RudinLp 1) x
        rw [h2, Pi.smul_apply, h3]
        by_cases hx : x ∈ In
        · rw [indicator_of_mem hx, indicator_of_mem hx, h4 hx, Pi.smul_apply]
        · simp [hx] }
  let C_n : ℝ := (μn univ).toReal ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
  let ιCLM : Lp ℂ 2 μn →L[ℂ] RudinLp 1 :=
    ιLin.mkContinuous C_n fun u => by
      change ‖(hmem1_of_L2 u).toLp (In.indicator (u : ℝ → ℂ))‖ ≤ C_n * ‖u‖
      rw [Lp.norm_toLp, Lp.norm_def, mul_comm C_n]
      have hle : eLpNorm (In.indicator (u : ℝ → ℂ)) 1 rudinMeasure ≤
          eLpNorm (u : ℝ → ℂ) 2 μn *
            μn univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hIn_meas]
        exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ one_le_two (Lp.aestronglyMeasurable u)
      have hrhs_ne : eLpNorm (u : ℝ → ℂ) 2 μn *
          μn univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ∞ :=
        (ENNReal.mul_lt_top (Lp.memLp u)
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_lt_top μn univ).ne)).ne
      have htr := ENNReal.toReal_mono hrhs_ne hle
      rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at htr
  let ℓ : StrongDual ℂ (Lp ℂ 2 μn) := Λ.comp ιCLM
  let w : Lp ℂ 2 μn := (InnerProductSpace.toDual ℂ (Lp ℂ 2 μn)).symm ℓ
  let w_mk : ℝ → ℂ := (Lp.aestronglyMeasurable w).mk w
  have hw_meas : Measurable w_mk := (Lp.aestronglyMeasurable w).stronglyMeasurable_mk.measurable
  have hw_ae : (w : ℝ → ℂ) =ᵐ[μn] w_mk := (Lp.aestronglyMeasurable w).ae_eq_mk
  let b_raw : ℝ → ℂ := fun x => conj (w_mk x)
  have hb_raw_meas : Measurable b_raw := continuous_star.measurable.comp hw_meas
  have hriesz : ∀ u : Lp ℂ 2 μn, Λ (ιCLM u) = ∫ x, (u : ℝ → ℂ) x * b_raw x ∂μn := by
    intro u
    have h1 : Λ (ιCLM u) = inner ℂ w u := (InnerProductSpace.toDual_symm_apply (x := u) (y := ℓ)).symm
    rw [h1, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hw_ae] with x hx
    rw [RCLike.inner_apply, hx]
  have hb_ae_le : ∀ᵐ x ∂μn, ‖b_raw x‖ ≤ ‖Λ‖ := by
    have hcover : {x : ℝ | ‖Λ‖ < ‖b_raw x‖} =
        ⋃ k : ℕ, {x : ℝ | ‖Λ‖ + 1 / ((k : ℝ) + 1) ≤ ‖b_raw x‖} := by
      ext x
      simp only [Set.mem_ofPred_eq, mem_iUnion]
      constructor
      · intro hlt
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        exact ⟨k, by linarith⟩
      · rintro ⟨k, hk⟩
        have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    rw [ae_iff]
    have hcompl : {x : ℝ | ¬ ‖b_raw x‖ ≤ ‖Λ‖} = {x : ℝ | ‖Λ‖ < ‖b_raw x‖} := by
      ext x; simp
    rw [hcompl, hcover, measure_iUnion_null_iff]
    intro k
    let δ : ℝ := 1 / ((k : ℝ) + 1)
    have hδ_pos : 0 < δ := by positivity
    let Sk : Set ℝ := {x : ℝ | ‖Λ‖ + δ ≤ ‖b_raw x‖}
    have hSk_meas : MeasurableSet Sk := measurableSet_le measurable_const hb_raw_meas.norm
    let vk : ℝ → ℂ := Sk.indicator fun x => conj (b_raw x) / (‖b_raw x‖ : ℂ)
    have hvk_meas : Measurable vk := by
      refine Measurable.indicator ?_ hSk_meas
      exact (continuous_star.measurable.comp hb_raw_meas).div
        (Complex.continuous_ofReal.measurable.comp hb_raw_meas.norm)
    have hvk_norm : ∀ x : ℝ, ‖vk x‖ ≤ 1 := by
      intro x
      by_cases hx : x ∈ Sk
      · have hbn_pos : 0 < ‖b_raw x‖ := by
          have h0 : 0 ≤ ‖Λ‖ := norm_nonneg Λ
          have hx' : ‖Λ‖ + δ ≤ ‖b_raw x‖ := hx
          linarith
        simp only [vk, indicator_of_mem hx, norm_div, RCLike.norm_conj, Complex.norm_real,
          Real.norm_of_nonneg hbn_pos.le, div_self hbn_pos.ne', le_refl]
      · simp [vk, hx]
    have hvk_mem2 : MemLp vk 2 μn :=
      (memLp_top_of_bound hvk_meas.aestronglyMeasurable 1 (ae_of_all _ hvk_norm)).mono_exponent le_top
    let uk : Lp ℂ 2 μn := hvk_mem2.toLp vk
    have hι_norm : ‖ιCLM uk‖ ≤ (μn Sk).toReal := by
      change ‖(hmem1_of_L2 uk).toLp (In.indicator (uk : ℝ → ℂ))‖ ≤ (μn Sk).toReal
      rw [L1.norm_eq_integral_norm]
      have hcoe_eq : ∫ x, ‖(((hmem1_of_L2 uk).toLp (In.indicator (uk : ℝ → ℂ)) : RudinLp 1) :
          ℝ → ℂ) x‖ ∂rudinMeasure =
          ∫ x, In.indicator (fun y => ‖(uk : ℝ → ℂ) y‖) x ∂rudinMeasure := by
        refine integral_congr_ae ?_
        filter_upwards [(hmem1_of_L2 uk).coeFn_toLp] with x hx
        rw [hx]
        by_cases hxI : x ∈ In <;> simp [hxI]
      rw [hcoe_eq, integral_indicator hIn_meas]
      have huk_eq : ∫ x, ‖(uk : ℝ → ℂ) x‖ ∂μn = ∫ x, ‖vk x‖ ∂μn := by
        refine integral_congr_ae ?_
        filter_upwards [hvk_mem2.coeFn_toLp] with x hx
        rw [hx]
      rw [huk_eq]
      have hvk_int : Integrable (fun x => ‖vk x‖) μn :=
        (hvk_mem2.integrable one_le_two).norm
      have h1_int : Integrable (Sk.indicator fun _ : ℝ => (1 : ℝ)) μn :=
        (integrable_const (1 : ℝ)).indicator hSk_meas
      have hle := integral_mono hvk_int h1_int fun x => by
        by_cases hx : x ∈ Sk
        · rw [indicator_of_mem hx]
          exact hvk_norm x
        · simp [vk, hx]
      have heval : ∫ x, Sk.indicator (fun _ : ℝ => (1 : ℝ)) x ∂μn = (μn Sk).toReal := by
        rw [integral_indicator_const _ hSk_meas, smul_eq_mul, mul_one, measureReal_def]
      linarith
    have hupper : (Λ (ιCLM uk)).re ≤ ‖Λ‖ * (μn Sk).toReal := by
      calc
        (Λ (ιCLM uk)).re ≤ ‖Λ (ιCLM uk)‖ := Complex.re_le_norm _
        _ ≤ ‖Λ‖ * ‖ιCLM uk‖ := Λ.le_opNorm _
        _ ≤ ‖Λ‖ * (μn Sk).toReal := mul_le_mul_of_nonneg_left hι_norm (norm_nonneg Λ)
    have hprod_eq : ∀ x : ℝ, vk x * b_raw x = (Sk.indicator (fun y => ‖b_raw y‖) x : ℂ) := by
      intro x
      by_cases hx : x ∈ Sk
      · have hbn_pos : 0 < ‖b_raw x‖ := by
          have h0 : 0 ≤ ‖Λ‖ := norm_nonneg Λ
          have hx' : ‖Λ‖ + δ ≤ ‖b_raw x‖ := hx
          linarith
        have hbn_ne : (‖b_raw x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hbn_pos.ne'
        simp only [vk, indicator_of_mem hx]
        rw [div_mul_eq_mul_div, mul_comm (conj (b_raw x)), Complex.mul_conj,
          Complex.normSq_eq_norm_sq]
        field_simp [hbn_ne]
        push_cast
        ring
      · simp [vk, hx]
    have hlower : (‖Λ‖ + δ) * (μn Sk).toReal ≤ (Λ (ιCLM uk)).re := by
      rw [hriesz uk]
      have hint_ae : (fun x => (uk : ℝ → ℂ) x * b_raw x) =ᵐ[μn]
          fun x => (Sk.indicator (fun y => ‖b_raw y‖) x : ℂ) := by
        filter_upwards [hvk_mem2.coeFn_toLp] with x hx
        rw [hx, hprod_eq x]
      rw [integral_congr_ae hint_ae]
      have hbn_int : Integrable (Sk.indicator fun y => ‖b_raw y‖) μn := by
        have hw_int : Integrable (fun y => ‖(w : ℝ → ℂ) y‖) μn :=
          (Lp.memLp w).integrable one_le_two |>.norm
        have hbr_int : Integrable (fun y => ‖b_raw y‖) μn := by
          refine hw_int.congr ?_
          filter_upwards [hw_ae] with y hy
          simp [b_raw, hy]
        exact hbr_int.indicator hSk_meas
      have hre_eq : (∫ x, (Sk.indicator (fun y => ‖b_raw y‖) x : ℂ) ∂μn).re =
          ∫ x, Sk.indicator (fun y => ‖b_raw y‖) x ∂μn := by
        have hpush : ∀ x : ℝ,
            (Sk.indicator (fun y => (‖b_raw y‖ : ℂ)) x) =
              Complex.ofRealCLM (Sk.indicator (fun y => ‖b_raw y‖) x) := fun x => by
          by_cases hx : x ∈ Sk <;> simp [hx]
        simp_rw [hpush]
        rw [Complex.ofRealCLM.integral_comp_comm hbn_int, Complex.ofRealCLM_apply,
          Complex.ofReal_re]
      rw [hre_eq]
      have hconst_int : Integrable (Sk.indicator fun _ : ℝ => ‖Λ‖ + δ) μn :=
        (integrable_const (‖Λ‖ + δ)).indicator hSk_meas
      have hmono := integral_mono hconst_int hbn_int fun x => by
        by_cases hx : x ∈ Sk
        · rw [indicator_of_mem hx, indicator_of_mem hx]
          exact hx
        · simp [hx]
      have hconst_eval : ∫ x, Sk.indicator (fun _ : ℝ => ‖Λ‖ + δ) x ∂μn =
          (‖Λ‖ + δ) * (μn Sk).toReal := by
        rw [integral_indicator_const _ hSk_meas, smul_eq_mul, mul_comm, measureReal_def]
      linarith
    have hle_zero : δ * (μn Sk).toReal ≤ 0 := by linarith
    have htr_nonneg : 0 ≤ (μn Sk).toReal := ENNReal.toReal_nonneg
    have htr_zero : (μn Sk).toReal = 0 :=
      le_antisymm (nonpos_of_mul_nonpos_right hle_zero hδ_pos) htr_nonneg
    exact (ENNReal.toReal_eq_zero_iff (μn Sk)).mp htr_zero |>.resolve_right
      (measure_lt_top μn Sk).ne
  let S_good : Set ℝ := {x : ℝ | ‖b_raw x‖ ≤ ‖Λ‖}
  have hS_good_meas : MeasurableSet S_good := measurableSet_le hb_raw_meas.norm measurable_const
  let βn : ℝ → ℂ := S_good.indicator b_raw
  have hβn_meas : Measurable βn := hb_raw_meas.indicator hS_good_meas
  have hβn_bound : ∀ x : ℝ, ‖βn x‖ ≤ ‖Λ‖ := by
    intro x
    by_cases hx : x ∈ S_good
    · dsimp only [βn]
      rw [indicator_of_mem hx]
      exact hx
    · simp [βn, hx, norm_nonneg Λ]
  have hβn_ae : βn =ᵐ[μn] b_raw := by
    filter_upwards [hb_ae_le] with x hx
    have hx' : x ∈ S_good := hx
    exact indicator_of_mem hx' b_raw
  refine ⟨βn, hβn_meas, hβn_bound, ?_⟩
  intro g hg_meas _ ⟨M, _, hg_bdd⟩ hg_supp hg1
  have hg2 : MemLp g 2 μn :=
    (memLp_top_of_bound hg_meas.aestronglyMeasurable M (ae_of_all _ hg_bdd)).mono_exponent le_top
  let ug : Lp ℂ 2 μn := hg2.toLp g
  have hι_eq : ιCLM ug = hg1.toLp g := by
    apply Lp.ext
    have hug_ae : (ug : ℝ → ℂ) =ᵐ[μn] g := hg2.coeFn_toLp
    rw [EventuallyEq, ae_restrict_iff' hIn_meas] at hug_ae
    filter_upwards [(hmem1_of_L2 ug).coeFn_toLp, hg1.coeFn_toLp, hug_ae] with x h1 h2 h3
    change (((hmem1_of_L2 ug).toLp (In.indicator (ug : ℝ → ℂ)) : RudinLp 1) : ℝ → ℂ) x =
      ((hg1.toLp g : RudinLp 1) : ℝ → ℂ) x
    rw [h1, h2]
    by_cases hx : x ∈ In
    · rw [indicator_of_mem hx, h3 hx]
    · rw [indicator_of_notMem hx, hg_supp x hx]
  rw [← hι_eq, hriesz ug]
  refine integral_congr_ae ?_
  filter_upwards [hg2.coeFn_toLp, hβn_ae] with x hx1 hx2
  rw [hx1, hx2]

/-- 9.22 (`(L¹)* ≅ L^∞` representation and uniqueness): For every continuous linear functional
`Λ : L¹(m) →L[ℂ] ℂ`, there exists a Borel measurable function `β : ℝ → ℂ` bounded everywhere by
`‖Λ‖` (hence `β ∈ L^∞(m)` with `‖β‖_∞ ≤ ‖Λ‖`, in fact `‖β‖_∞ = ‖Λ‖`) such that
`Λ f = ∫ x, f(x) β(x) dm(x)` for every `f ∈ L¹(m)`, and `β` is unique up to `m`-null sets. -/
theorem theorem_9_22_L1_dual (Λ : RudinLp 1 →L[ℂ] ℂ) :
    (∃ β : ℝ → ℂ, Measurable β ∧ (∀ x : ℝ, ‖β x‖ ≤ ‖Λ‖) ∧ MemLp β ∞ rudinMeasure ∧
      rudinLinftyNorm β = ‖Λ‖ ∧
      ∀ f : RudinLp 1, Λ f = ∫ x, (f : ℝ → ℂ) x * β x ∂rudinMeasure) ∧
    (∀ β₁ β₂ : ℝ → ℂ, MemLp β₁ ∞ rudinMeasure → MemLp β₂ ∞ rudinMeasure →
      (∀ f : RudinLp 1, ∫ x, (f : ℝ → ℂ) x * β₁ x ∂rudinMeasure =
        ∫ x, (f : ℝ → ℂ) x * β₂ x ∂rudinMeasure) →
      β₁ =ᵐ[rudinMeasure] β₂) := by
  constructor
  · choose βn hβn_meas hβn_bdd hβn_rep using L1_dual_unit_interval Λ
    let β : ℝ → ℂ := fun x => βn ⌊x⌋ x
    have hβ_on_Ico : ∀ (n : ℤ) {x : ℝ}, x ∈ Ico (n : ℝ) (n + 1) → β x = βn n x := by
      intro n x hx
      dsimp [β]
      rw [Int.floor_eq_iff.mpr ⟨hx.1, hx.2⟩]
    have hβ_meas : Measurable β := by
      intro U hU
      have hpre : β ⁻¹' U = ⋃ n : ℤ, Ico (n : ℝ) (n + 1) ∩ (βn n ⁻¹' U) := by
        ext x
        simp only [mem_preimage, mem_iUnion, mem_inter_iff]
        constructor
        · intro hxU
          refine ⟨⌊x⌋, ⟨Int.floor_le x, Int.lt_floor_add_one x⟩, hxU⟩
        · rintro ⟨n, hxI, hxU⟩
          rwa [hβ_on_Ico n hxI]
      rw [hpre]
      exact MeasurableSet.iUnion fun n => measurableSet_Ico.inter (hβn_meas n hU)
    have hβ_bdd : ∀ x : ℝ, ‖β x‖ ≤ ‖Λ‖ := fun x => hβn_bdd ⌊x⌋ x
    have hβ_mem_top : MemLp β ∞ rudinMeasure :=
      memLp_top_of_bound hβ_meas.aestronglyMeasurable ‖Λ‖ (ae_of_all _ hβ_bdd)
    have hrep_all : ∀ f : RudinLp 1, Λ f = ∫ x, (f : ℝ → ℂ) x * β x ∂rudinMeasure := by
      intro f
      let f_mk : ℝ → ℂ := (Lp.aestronglyMeasurable f).mk f
      have hf_meas : Measurable f_mk := (Lp.aestronglyMeasurable f).stronglyMeasurable_mk.measurable
      have hf_ae : (f : ℝ → ℂ) =ᵐ[rudinMeasure] f_mk := (Lp.aestronglyMeasurable f).ae_eq_mk
      have hf_int : Integrable f_mk rudinMeasure :=
        (integrable_congr hf_ae).mp (L1.integrable_coeFn f)
      let S_cap : ℕ → Set ℝ := fun N => {x : ℝ | ‖f_mk x‖ ≤ (N : ℝ)}
      have hScap_meas : ∀ N : ℕ, MeasurableSet (S_cap N) := fun N =>
        measurableSet_le hf_meas.norm measurable_const
      let piece : ℕ → ℤ → ℝ → ℂ := fun N n =>
        (Ico (n : ℝ) (n + 1) ∩ S_cap N).indicator f_mk
      have hpiece_meas : ∀ N n, Measurable (piece N n) := fun N n =>
        hf_meas.indicator (measurableSet_Ico.inter (hScap_meas N))
      have hpiece_mem1 : ∀ N n, MemLp (piece N n) 1 rudinMeasure := fun N n =>
        memLp_one_iff_integrable.mpr
          (hf_int.indicator (measurableSet_Ico.inter (hScap_meas N)))
      have hpiece_eq : ∀ N n,
          Λ ((hpiece_mem1 N n).toLp (piece N n)) =
            ∫ x, piece N n x * β x ∂rudinMeasure := by
        intro N n
        have h1 := hβn_rep n (piece N n) (hpiece_meas N n) (fun _ _ => trivial)
          ⟨N, Nat.cast_nonneg N, fun x => by
            by_cases hx : x ∈ Ico (n : ℝ) (n + 1) ∩ S_cap N
            · dsimp only [piece]
              rw [indicator_of_mem hx]
              exact hx.2
            · simp [piece, hx]⟩
          (fun x hx => indicator_of_notMem (fun hmem => hx hmem.1) f_mk)
          (hpiece_mem1 N n)
        rw [h1, ← integral_indicator measurableSet_Ico]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        dsimp only
        by_cases hx : x ∈ Ico (n : ℝ) (n + 1)
        · rw [indicator_of_mem hx, hβ_on_Ico n hx]
        · have hx' : x ∉ Ico (n : ℝ) (n + 1) ∩ S_cap N := fun h => hx h.1
          simp [piece, hx, hx']
      let GN : ℕ → ℝ → ℂ := fun N =>
        (Ico (-(N : ℝ)) ((N : ℝ) + 1) ∩ S_cap N).indicator f_mk
      have hGN_mem1 : ∀ N : ℕ, MemLp (GN N) 1 rudinMeasure := fun N =>
        memLp_one_iff_integrable.mpr
          (hf_int.indicator (measurableSet_Ico.inter (hScap_meas N)))
      have hGN_sum : ∀ (N : ℕ) (x : ℝ),
          GN N x = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), piece N n x := by
        intro N x
        by_cases hx : x ∈ Ico (-(N : ℝ)) ((N : ℝ) + 1) ∩ S_cap N
        · have hn_mem : ⌊x⌋ ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
            rw [Finset.mem_Icc]
            constructor
            · exact Int.le_floor.mpr (by exact_mod_cast hx.1.1)
            · have hlt : ⌊x⌋ < (N : ℤ) + 1 := by
                rw [Int.floor_lt]
                exact_mod_cast hx.1.2
              omega
          rw [Finset.sum_eq_single ⌊x⌋]
          · have hx_piece : x ∈ Ico (⌊x⌋ : ℝ) (⌊x⌋ + 1) ∩ S_cap N :=
              ⟨⟨Int.floor_le x, Int.lt_floor_add_one x⟩, hx.2⟩
            simp [GN, piece, hx, hx_piece]
          · intro m _ hm_ne
            have hx_not : x ∉ Ico (m : ℝ) (m + 1) ∩ S_cap N := by
              intro hmem
              exact hm_ne (Int.floor_eq_iff.mpr hmem.1).symm
            simp [piece, hx_not]
          · intro hnot
            exact (hnot hn_mem).elim
        · have hGN0 : GN N x = 0 := by simp [GN, hx]
          rw [hGN0]
          symm
          refine Finset.sum_eq_zero fun n hn => ?_
          rw [Finset.mem_Icc] at hn
          have hx_not : x ∉ Ico (n : ℝ) (n + 1) ∩ S_cap N := by
            intro hmem
            apply hx
            refine ⟨⟨?_, ?_⟩, hmem.2⟩
            · have hle : (-(N : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hn.1
              exact hle.trans hmem.1.1
            · have hle : (n : ℝ) + 1 ≤ (N : ℝ) + 1 := by
                have : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
                linarith
              exact hmem.1.2.trans_le hle
          simp [piece, hx_not]
      have hGN_toLp : ∀ N : ℕ,
          (hGN_mem1 N).toLp (GN N) =
            ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (hpiece_mem1 N n).toLp (piece N n) := by
        intro N
        apply Lp.ext
        have hsum_ae : ∀ s : Finset ℤ,
            ((∑ n ∈ s, (hpiece_mem1 N n).toLp (piece N n) : RudinLp 1) : ℝ → ℂ) =ᵐ[rudinMeasure]
              fun x => ∑ n ∈ s, piece N n x := by
          intro s
          induction s using Finset.induction_on with
          | empty =>
            simp only [Finset.sum_empty]
            exact (Lp.coeFn_zero ℂ 1 rudinMeasure).trans (ae_of_all _ fun _ => rfl)
          | @insert a s ha ih =>
            simp only [Finset.sum_insert ha]
            filter_upwards [Lp.coeFn_add ((hpiece_mem1 N a).toLp (piece N a))
              (∑ n ∈ s, (hpiece_mem1 N n).toLp (piece N n)),
              (hpiece_mem1 N a).coeFn_toLp, ih] with x h1 h2 h3
            rw [h1, Pi.add_apply, h2, h3]
        filter_upwards [(hGN_mem1 N).coeFn_toLp,
          hsum_ae (Finset.Icc (-(N : ℤ)) (N : ℤ))] with x hx1 hx2
        rw [hx1, hx2, hGN_sum N x]
      have hGN_eval : ∀ N : ℕ,
          Λ ((hGN_mem1 N).toLp (GN N)) = ∫ x, GN N x * β x ∂rudinMeasure := by
        intro N
        rw [hGN_toLp N, map_sum]
        simp_rw [hpiece_eq N]
        rw [← integral_finsetSum _ fun n _ => ?_]
        · refine integral_congr_ae (ae_of_all _ fun x => ?_)
          dsimp only
          rw [← Finset.sum_mul, ← hGN_sum N x]
        · exact integrable_mul_of_ae_bound (memLp_one_iff_integrable.mp (hpiece_mem1 N n))
            hβ_meas.aestronglyMeasurable ‖Λ‖ (ae_of_all _ hβ_bdd)
      have hGN_tendsto : Tendsto (fun N : ℕ => (hGN_mem1 N).toLp (GN N)) atTop (𝓝 f) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        have hnorm_eq : ∀ N : ℕ,
            ‖(hGN_mem1 N).toLp (GN N) - f‖ = ∫ x, ‖GN N x - f_mk x‖ ∂rudinMeasure := by
          intro N
          rw [L1.norm_eq_integral_norm]
          refine integral_congr_ae ?_
          filter_upwards [Lp.coeFn_sub ((hGN_mem1 N).toLp (GN N)) f,
            (hGN_mem1 N).coeFn_toLp, hf_ae] with x h1 h2 h3
          rw [h1, Pi.sub_apply, h2, h3]
        simp_rw [hnorm_eq]
        have h0 : (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) ∂rudinMeasure := by simp
        rw [h0]
        refine tendsto_integral_filter_of_dominated_convergence
          (fun x => ‖f_mk x‖)
          (Eventually.of_forall fun N =>
            ((hf_meas.indicator (measurableSet_Ico.inter (hScap_meas N))).sub
              hf_meas).norm.aestronglyMeasurable)
          (Eventually.of_forall fun N => ae_of_all _ fun x => ?_)
          hf_int.norm
          (ae_of_all _ fun x => ?_)
        · rw [Real.norm_of_nonneg (norm_nonneg _)]
          by_cases hx : x ∈ Ico (-(N : ℝ)) ((N : ℝ) + 1) ∩ S_cap N <;> simp [GN, hx]
        · refine tendsto_const_nhds.congr' ?_
          obtain ⟨N₁, hN₁⟩ := exists_nat_ge |x|
          obtain ⟨N₂, hN₂⟩ := exists_nat_ge ‖f_mk x‖
          filter_upwards [Ici_mem_atTop (max N₁ N₂)] with N (hN : max N₁ N₂ ≤ N)
          have hx1 : |x| ≤ (N : ℝ) := hN₁.trans (by exact_mod_cast (le_max_left N₁ N₂).trans hN)
          have hx2 : ‖f_mk x‖ ≤ (N : ℝ) :=
            hN₂.trans (by exact_mod_cast (le_max_right N₁ N₂).trans hN)
          have hx_mem : x ∈ Ico (-(N : ℝ)) ((N : ℝ) + 1) ∩ S_cap N := by
            refine ⟨⟨(abs_le.mp hx1).1, ?_⟩, hx2⟩
            linarith [(abs_le.mp hx1).2]
          simp [GN, hx_mem]
      let Λ_rhs : RudinLp 1 →L[ℂ] ℂ :=
        LinearMap.mkContinuous
          { toFun := fun g => ∫ x, (g : ℝ → ℂ) x * β x ∂rudinMeasure
            map_add' := fun g₁ g₂ => by
              have h1 : Integrable (fun x => (g₁ : ℝ → ℂ) x * β x) rudinMeasure :=
                integrable_mul_of_ae_bound (L1.integrable_coeFn g₁)
                  hβ_meas.aestronglyMeasurable ‖Λ‖ (ae_of_all _ hβ_bdd)
              have h2 : Integrable (fun x => (g₂ : ℝ → ℂ) x * β x) rudinMeasure :=
                integrable_mul_of_ae_bound (L1.integrable_coeFn g₂)
                  hβ_meas.aestronglyMeasurable ‖Λ‖ (ae_of_all _ hβ_bdd)
              rw [← integral_add h1 h2]
              refine integral_congr_ae ?_
              filter_upwards [Lp.coeFn_add g₁ g₂] with x hx
              rw [hx, Pi.add_apply, add_mul]
            map_smul' := fun c g => by
              simp only [RingHom.id_apply, smul_eq_mul]
              rw [← integral_const_mul]
              refine integral_congr_ae ?_
              filter_upwards [Lp.coeFn_smul c g] with x hx
              rw [hx, Pi.smul_apply, smul_eq_mul, mul_assoc] }
          ‖Λ‖
          (fun g => by
            change ‖∫ x, (g : ℝ → ℂ) x * β x ∂rudinMeasure‖ ≤ ‖Λ‖ * ‖g‖
            refine (norm_integral_le_integral_norm _).trans ?_
            rw [L1.norm_eq_integral_norm g, ← integral_const_mul]
            refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
              ((L1.integrable_coeFn g).norm.const_mul ‖Λ‖) (ae_of_all _ fun x => ?_)
            dsimp only
            rw [norm_mul, mul_comm ‖Λ‖]
            exact mul_le_mul_of_nonneg_left (hβ_bdd x) (norm_nonneg _))
      have hlhs_lim : Tendsto (fun N => Λ ((hGN_mem1 N).toLp (GN N))) atTop (𝓝 (Λ f)) :=
        (Λ.continuous.tendsto f).comp hGN_tendsto
      have hrhs_lim : Tendsto (fun N => Λ ((hGN_mem1 N).toLp (GN N))) atTop (𝓝 (Λ_rhs f)) := by
        refine ((Λ_rhs.continuous.tendsto f).comp hGN_tendsto).congr' ?_
        filter_upwards with N
        dsimp only [Function.comp_def, Λ_rhs, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
          AddHom.coe_mk]
        rw [hGN_eval N]
        refine integral_congr_ae ?_
        filter_upwards [(hGN_mem1 N).coeFn_toLp] with x hx
        rw [hx]
      exact tendsto_nhds_unique hlhs_lim hrhs_lim
    have hβ_norm_eq : rudinLinftyNorm β = ‖Λ‖ := by
      apply le_antisymm
      · unfold rudinLinftyNorm
        have hle : eLpNorm β ∞ rudinMeasure ≤ ENNReal.ofReal ‖Λ‖ := by
          rw [eLpNorm_exponent_top hβ_meas.aestronglyMeasurable]
          refine eLpNormEssSup_le_of_ae_enorm_bound (ae_of_all _ fun x => ?_)
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hβ_bdd x)
        exact (ENNReal.toReal_le_of_le_ofReal (norm_nonneg Λ) hle)
      · refine ContinuousLinearMap.opNorm_le_bound Λ (by unfold rudinLinftyNorm; exact ENNReal.toReal_nonneg)
          fun f => ?_
        rw [hrep_all f]
        have hβ_ae_linf : ∀ᵐ x ∂rudinMeasure, ‖β x‖ ≤ rudinLinftyNorm β := by
          have h1 : ∀ᵐ x ∂rudinMeasure, ‖β x‖ₑ ≤ eLpNorm β ∞ rudinMeasure := by
            rw [eLpNorm_exponent_top hβ_meas.aestronglyMeasurable]
            exact ae_le_eLpNormEssSup
          filter_upwards [h1] with x hx
          exact (ENNReal.toReal_le_toReal enorm_ne_top hβ_mem_top.ne).mpr hx
        refine (norm_integral_le_integral_norm _).trans ?_
        rw [L1.norm_eq_integral_norm f, ← integral_const_mul]
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
          ((L1.integrable_coeFn f).norm.const_mul (rudinLinftyNorm β)) ?_
        filter_upwards [hβ_ae_linf] with x hx
        rw [norm_mul, mul_comm (rudinLinftyNorm β)]
        exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
    exact ⟨β, hβ_meas, hβ_bdd, hβ_mem_top, hβ_norm_eq, hrep_all⟩
  · intro β₁ β₂ hβ₁ hβ₂ heq
    let d : ℝ → ℂ := fun x => β₁ x - β₂ x
    have hd_top : MemLp d ∞ rudinMeasure := hβ₁.sub hβ₂
    have hd_ae_bdd : ∀ᵐ x ∂rudinMeasure, ‖d x‖ ≤ rudinLinftyNorm d := by
      have h1 : ∀ᵐ x ∂rudinMeasure, ‖d x‖ₑ ≤ eLpNorm d ∞ rudinMeasure := by
        rw [eLpNorm_exponent_top hd_top.aestronglyMeasurable]
        exact ae_le_eLpNormEssSup
      filter_upwards [h1] with x hx
      exact (ENNReal.toReal_le_toReal enorm_ne_top hd_top.ne).mpr hx
    have hcover : {x : ℝ | d x ≠ 0} = ⋃ N : ℕ, {x : ℝ | d x ≠ 0} ∩ Icc (-(N : ℝ)) (N : ℝ) := by
      ext x
      simp only [Set.mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_Icc]
      refine ⟨fun hx => ?_, fun ⟨_, hx, _⟩ => hx⟩
      obtain ⟨N, hN⟩ := exists_nat_ge |x|
      exact ⟨N, hx, abs_le.mp hN⟩
    rw [EventuallyEq, ae_iff]
    have hset : {x : ℝ | ¬ β₁ x = β₂ x} = {x : ℝ | d x ≠ 0} := by
      ext x; simp [d, sub_eq_zero]
    rw [hset, hcover, measure_iUnion_null_iff]
    intro N
    let testF : ℝ → ℂ := (Icc (-(N : ℝ)) (N : ℝ)).indicator fun x => conj (d x)
    have htest_mem1 : MemLp testF 1 rudinMeasure := by
      have hmeas : AEStronglyMeasurable testF rudinMeasure :=
        (continuous_star.comp_aestronglyMeasurable hd_top.aestronglyMeasurable).indicator
          measurableSet_Icc
      have hconst_int : Integrable
          ((Icc (-(N : ℝ)) (N : ℝ)).indicator fun _ : ℝ => rudinLinftyNorm d) rudinMeasure :=
        (integrableOn_const isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
      refine memLp_one_iff_integrable.mpr (hconst_int.mono' hmeas ?_)
      filter_upwards [hd_ae_bdd] with x hx
      by_cases hxI : x ∈ Icc (-(N : ℝ)) (N : ℝ)
      · simpa [testF, hxI] using hx
      · simp [testF, hxI]
    have hzero : ∫ x, testF x * d x ∂rudinMeasure = 0 := by
      have hβ₁_ae : ∀ᵐ x ∂rudinMeasure, ‖β₁ x‖ ≤ rudinLinftyNorm β₁ := by
        have h1 : ∀ᵐ x ∂rudinMeasure, ‖β₁ x‖ₑ ≤ eLpNorm β₁ ∞ rudinMeasure := by
          rw [eLpNorm_exponent_top hβ₁.aestronglyMeasurable]; exact ae_le_eLpNormEssSup
        filter_upwards [h1] with x hx
        exact (ENNReal.toReal_le_toReal enorm_ne_top hβ₁.ne).mpr hx
      have hβ₂_ae : ∀ᵐ x ∂rudinMeasure, ‖β₂ x‖ ≤ rudinLinftyNorm β₂ := by
        have h1 : ∀ᵐ x ∂rudinMeasure, ‖β₂ x‖ₑ ≤ eLpNorm β₂ ∞ rudinMeasure := by
          rw [eLpNorm_exponent_top hβ₂.aestronglyMeasurable]; exact ae_le_eLpNormEssSup
        filter_upwards [h1] with x hx
        exact (ENNReal.toReal_le_toReal enorm_ne_top hβ₂.ne).mpr hx
      let F : RudinLp 1 := htest_mem1.toLp testF
      have hint1 : Integrable (fun x => (F : ℝ → ℂ) x * β₁ x) rudinMeasure :=
        integrable_mul_of_ae_bound (L1.integrable_coeFn F)
          hβ₁.aestronglyMeasurable (rudinLinftyNorm β₁) hβ₁_ae
      have hint2 : Integrable (fun x => (F : ℝ → ℂ) x * β₂ x) rudinMeasure :=
        integrable_mul_of_ae_bound (L1.integrable_coeFn F)
          hβ₂.aestronglyMeasurable (rudinLinftyNorm β₂) hβ₂_ae
      have hsub_zero : ∫ x, ((F : ℝ → ℂ) x * β₁ x - (F : ℝ → ℂ) x * β₂ x) ∂rudinMeasure = 0 := by
        rw [integral_sub hint1 hint2, heq F, sub_self]
      rw [← hsub_zero]
      refine integral_congr_ae ?_
      filter_upwards [htest_mem1.coeFn_toLp] with x hx
      rw [hx]
      dsimp [d]
      ring
    have hreal_int : Integrable ((Icc (-(N : ℝ)) (N : ℝ)).indicator fun x => ‖d x‖ ^ 2)
        rudinMeasure := by
      have hconst_int : Integrable
          ((Icc (-(N : ℝ)) (N : ℝ)).indicator fun _ : ℝ => rudinLinftyNorm d ^ 2) rudinMeasure :=
        (integrableOn_const isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
      refine hconst_int.mono' ((hd_top.aestronglyMeasurable.norm.pow 2).indicator measurableSet_Icc) ?_
      filter_upwards [hd_ae_bdd] with x hx
      by_cases hxI : x ∈ Icc (-(N : ℝ)) (N : ℝ)
      · simp only [indicator_of_mem hxI, Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) hx 2
      · simp [hxI]
    have hreal_zero : ∫ x, (Icc (-(N : ℝ)) (N : ℝ)).indicator (fun y => ‖d y‖ ^ 2) x ∂rudinMeasure = 0 := by
      have hcast : ∀ x : ℝ, testF x * d x =
          Complex.ofRealCLM ((Icc (-(N : ℝ)) (N : ℝ)).indicator (fun y => ‖d y‖ ^ 2) x) := by
        intro x
        by_cases hxI : x ∈ Icc (-(N : ℝ)) (N : ℝ)
        · simp only [testF, indicator_of_mem hxI, mul_comm (conj (d x)), Complex.mul_conj,
            Complex.normSq_eq_norm_sq, Complex.ofRealCLM_apply]
        · simp [testF, hxI]
      simp_rw [hcast] at hzero
      rw [Complex.ofRealCLM.integral_comp_comm hreal_int, Complex.ofRealCLM_apply,
        Complex.ofReal_eq_zero] at hzero
      exact hzero
    have hae_sq_zero :
        (Icc (-(N : ℝ)) (N : ℝ)).indicator (fun y => ‖d y‖ ^ 2) =ᵐ[rudinMeasure] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae
        (ae_of_all _ fun x => by
          by_cases hxI : x ∈ Icc (-(N : ℝ)) (N : ℝ) <;> simp [hxI])
        hreal_int).mp hreal_zero
    rw [EventuallyEq, ae_iff] at hae_sq_zero
    refine measure_mono_null (fun x ⟨hdx, hxI⟩ => ?_) hae_sq_zero
    change ¬ (Icc (-(N : ℝ)) (N : ℝ)).indicator (fun y => ‖d y‖ ^ 2) x = 0
    rw [indicator_of_mem hxI]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hdx)

/-- 9.22 (exponential characterization of continuous unit-modulus multiplicative functions on `ℝ`):
Every continuous `γ : ℝ → ℂ` satisfying `γ 0 = 1`, `∀ x y, γ (x + y) = γ x * γ y`, and
`∀ x, ‖γ x‖ ≤ 1` is differentiable everywhere on `ℝ` and equals `x ↦ e^(-i x t)` for a real `t`. -/
theorem theorem_9_22_exponential_character {γ : ℝ → ℂ} (hγ_cont : Continuous γ)
    (hγ_zero : γ 0 = 1) (hγ_add : ∀ x y : ℝ, γ (x + y) = γ x * γ y)
    (hγ_le_one : ∀ x : ℝ, ‖γ x‖ ≤ 1) :
    IsRudinCharacter γ ∧ Differentiable ℝ γ ∧
      ∃ t : ℝ, (∀ x : ℝ, HasDerivAt γ (-Complex.I * t * γ x) x) ∧
        ∀ x : ℝ, γ x = Complex.exp (-Complex.I * x * t) := by
  have hγ_unit : ∀ x : ℝ, ‖γ x‖ = 1 := by
    intro x
    apply le_antisymm (hγ_le_one x)
    have hprod : 1 = ‖γ x‖ * ‖γ (-x)‖ := by
      calc
        (1 : ℝ) = ‖(1 : ℂ)‖ := norm_one.symm
        _ = ‖γ (x + (-x))‖ := by rw [add_neg_cancel, hγ_zero]
        _ = ‖γ x * γ (-x)‖ := by rw [hγ_add]
        _ = ‖γ x‖ * ‖γ (-x)‖ := norm_mul _ _
    have hle := mul_le_mul_of_nonneg_left (hγ_le_one (-x)) (norm_nonneg (γ x))
    linarith
  have hchar : IsRudinCharacter γ := ⟨hγ_cont, hγ_unit, hγ_add⟩
  have hre_cont : ContinuousAt (fun y : ℝ => (γ y).re) 0 :=
    (Complex.continuous_re.comp hγ_cont).continuousAt
  rw [Metric.continuousAt_iff] at hre_cont
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := hre_cont (1 / 2) (by norm_num)
  let d : ℝ := δ / 2
  have hd_pos : 0 < d := half_pos hδ_pos
  have hre_ge : ∀ y ∈ Icc (0 : ℝ) d, (1 / 2 : ℝ) ≤ (γ y).re := by
    intro y hy
    have hdist : dist y 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hy.1]
      have hyd : y ≤ δ / 2 := hy.2
      linarith
    have hlt := hδ_ball hdist
    rw [Real.dist_eq, hγ_zero, Complex.one_re] at hlt
    linarith [(abs_lt.mp hlt).1]
  let A : ℂ := ∫ y in (0 : ℝ)..d, γ y
  have hA_ne : A ≠ 0 := by
    intro hA0
    have hAre0 : A.re = 0 := by simp [hA0]
    have hAre_eq : A.re = ∫ y in (0 : ℝ)..d, (γ y).re := by
      simpa [A] using (Complex.reCLM.intervalIntegral_comp_comm
        (hγ_cont.intervalIntegrable 0 d)).symm
    have hmono := intervalIntegral.integral_mono_on hd_pos.le
      (intervalIntegrable_const (μ := volume))
      ((Complex.continuous_re.comp hγ_cont).intervalIntegrable 0 d)
      hre_ge
    dsimp only [Function.comp_def] at hmono
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, ← hAre_eq, hAre0] at hmono
    linarith
  have hγ_int_id : ∀ x : ℝ,
      γ x = ((∫ u in (0 : ℝ)..(x + d), γ u) - (∫ u in (0 : ℝ)..x, γ u)) * A⁻¹ := by
    intro x
    have hmulA : γ x * A = (∫ u in (0 : ℝ)..(x + d), γ u) - (∫ u in (0 : ℝ)..x, γ u) := by
      calc
        γ x * A = ∫ y in (0 : ℝ)..d, γ x * γ y :=
          (intervalIntegral.integral_const_mul (γ x) _).symm
        _ = ∫ y in (0 : ℝ)..d, γ (x + y) := by simp_rw [← hγ_add x]
        _ = ∫ u in x + 0..x + d, γ u := intervalIntegral.integral_comp_add_left γ x
        _ = ∫ u in x..(x + d), γ u := by rw [add_zero]
        _ = (∫ u in (0 : ℝ)..(x + d), γ u) - (∫ u in (0 : ℝ)..x, γ u) := by
          rw [eq_sub_iff_add_eq, add_comm]
          exact intervalIntegral.integral_add_adjacent_intervals
            (hγ_cont.intervalIntegrable 0 x)
            (hγ_cont.intervalIntegrable x (x + d))
    rw [← hmulA, mul_assoc, mul_inv_cancel₀ hA_ne, mul_one]
  let c : ℂ := (γ d - 1) * A⁻¹
  have hγ_deriv : ∀ x : ℝ, HasDerivAt γ (c * γ x) x := by
    intro x
    have hd1 : HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, γ s) (γ (x + d)) (x + d) :=
      intervalIntegral.integral_hasDerivAt_right
        (hγ_cont.intervalIntegrable 0 (x + d))
        hγ_cont.stronglyMeasurable.stronglyMeasurableAtFilter
        hγ_cont.continuousAt
    have hd1_comp : HasDerivAt (fun v : ℝ => ∫ s in (0 : ℝ)..(v + d), γ s) (γ (x + d)) x := by
      have hshift : HasDerivAt (fun v : ℝ => v + d) 1 x := by
        simpa using (hasDerivAt_id' x).add_const d
      simpa only [Function.comp_def, one_smul] using hd1.scomp x hshift
    have hd2 : HasDerivAt (fun v : ℝ => ∫ s in (0 : ℝ)..v, γ s) (γ x) x :=
      intervalIntegral.integral_hasDerivAt_right
        (hγ_cont.intervalIntegrable 0 x)
        hγ_cont.stronglyMeasurable.stronglyMeasurableAtFilter
        hγ_cont.continuousAt
    have hd_rhs : HasDerivAt
        (fun v : ℝ => ((∫ u in (0 : ℝ)..(v + d), γ u) - (∫ u in (0 : ℝ)..v, γ u)) * A⁻¹)
        ((γ (x + d) - γ x) * A⁻¹) x :=
      (hd1_comp.sub hd2).mul_const A⁻¹
    have hfun_eq : γ =
        fun v : ℝ => ((∫ u in (0 : ℝ)..(v + d), γ u) - (∫ u in (0 : ℝ)..v, γ u)) * A⁻¹ :=
      funext hγ_int_id
    have hval_eq : (γ (x + d) - γ x) * A⁻¹ = c * γ x := by
      rw [hγ_add x d]
      dsimp [c]
      ring
    rwa [← hfun_eq, hval_eq] at hd_rhs
  let ψ : ℝ → ℂ := fun x => γ x * Complex.exp (-c * (x : ℂ))
  have hψ_deriv : ∀ x : ℝ, HasDerivAt ψ 0 x := by
    intro x
    have hlin : HasDerivAt (fun y : ℝ => -c * (y : ℂ)) (-c) x := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using
        (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-c)
    have hexp : HasDerivAt (fun y : ℝ => Complex.exp (-c * (y : ℂ)))
        (Complex.exp (-c * (x : ℂ)) * (-c)) x := hlin.cexp
    have hprod := (hγ_deriv x).mul hexp
    convert hprod using 1
    ring
  have hψ_const : ∀ x : ℝ, ψ x = 1 := by
    have hdiff : Differentiable ℝ ψ := fun x => (hψ_deriv x).differentiableAt
    have hderiv0 : ∀ x : ℝ, deriv ψ x = 0 := fun x => (hψ_deriv x).deriv
    intro x
    have hx0 := is_const_of_deriv_eq_zero hdiff hderiv0 x 0
    simpa [ψ, hγ_zero] using hx0
  have hγ_exp_c : ∀ x : ℝ, γ x = Complex.exp (c * (x : ℂ)) := by
    intro x
    calc
      γ x = γ x * (Complex.exp (-c * (x : ℂ)) * Complex.exp (c * (x : ℂ))) := by
        rw [← Complex.exp_add]
        have h0 : -c * (x : ℂ) + c * (x : ℂ) = 0 := by ring
        rw [h0, Complex.exp_zero, mul_one]
      _ = ψ x * Complex.exp (c * (x : ℂ)) := by dsimp [ψ]; ring
      _ = Complex.exp (c * (x : ℂ)) := by rw [hψ_const x, one_mul]
  have hc_re : c.re = 0 := by
    have h1 : ‖γ 1‖ = 1 := hγ_unit 1
    rw [hγ_exp_c 1, Complex.ofReal_one, mul_one, Complex.norm_exp] at h1
    exact Real.exp_injective (h1.trans Real.exp_zero.symm)
  let t : ℝ := -c.im
  have hc_eq : c = -Complex.I * (t : ℂ) := by
    apply Complex.ext
    · simp [t, hc_re]
    · simp [t]
  refine ⟨hchar, fun x => (hγ_deriv x).differentiableAt, t, ?_, ?_⟩
  · intro x
    simpa only [hc_eq] using hγ_deriv x
  · intro x
    rw [hγ_exp_c x, hc_eq]
    congr 1
    ring

/-- 9.22 (full `L¹` homomorphism structural development): For every nonzero complex homomorphism
`h : RudinComplexHom RudinL1Algebra`, there exist a bounded Borel measurable representative
`β ∈ L^∞(m)` (`‖β‖ ≤ 1`), a unique continuous character representative `γ : ℝ → ℂ` equal to `β`
almost everywhere `[m]` satisfying `γ(x + y) = γ(x) γ(y)` and `|γ(x)| = 1` for all `x, y ∈ ℝ`,
and a real number `t ∈ ℝ` such that `γ(x) = e^(-i x t)` and `h f = f̂(t)` for every `f ∈ L¹(m)`. -/
theorem theorem_9_22 {h : RudinComplexHom RudinL1Algebra} (hh_ne : h ≠ 0) :
    ∃ (β γ : ℝ → ℂ) (t : ℝ),
      Measurable β ∧ (∀ x : ℝ, ‖β x‖ ≤ 1) ∧
      IsRudinCharacter γ ∧ Differentiable ℝ γ ∧
      β =ᵐ[rudinMeasure] γ ∧
      (∀ x : ℝ, γ x = Complex.exp (-Complex.I * x * t)) ∧
      (∀ f : RudinL1Algebra, h f = ∫ x, (f.toLp : ℝ → ℂ) x * γ x ∂rudinMeasure) ∧
      (∀ f : RudinL1Algebra, h f = rudinFourier f.toLp t) := by
  have ⟨f₀, hf₀_ne⟩ : ∃ f₀ : RudinL1Algebra, h f₀ ≠ 0 := by
    by_contra! hall
    apply hh_ne
    ext f
    exact hall f
  let Λ : RudinLp 1 →L[ℂ] ℂ :=
    LinearMap.mkContinuous
      { toFun := fun u => h (RudinL1Algebra.ofLp u)
        map_add' := fun u v => map_add h (RudinL1Algebra.ofLp u) (RudinL1Algebra.ofLp v)
        map_smul' := fun c u => map_smul h c (RudinL1Algebra.ofLp u) }
      1
      (fun u => by
        change ‖h (RudinL1Algebra.ofLp u)‖ ≤ 1 * ‖u‖
        simpa only [one_mul, RudinL1Algebra.norm_ofLp] using
          theorem_9_21_apply_le h (RudinL1Algebra.ofLp u))
  have hΛ_norm_le : ‖Λ‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  obtain ⟨⟨β, hβ_meas, hβ_bdd_Λ, hβ_top, _, hβ_rep⟩, hβ_uniq⟩ := theorem_9_22_L1_dual Λ
  have hβ_bdd_one : ∀ x : ℝ, ‖β x‖ ≤ 1 := fun x => (hβ_bdd_Λ x).trans hΛ_norm_le
  have hconv_fubini : ∀ f g : RudinL1Algebra,
      h (f * g) = ∫ y, (g.toLp : ℝ → ℂ) y * Λ (rudinTranslateLp 1 y f.toLp) ∂rudinMeasure := by
    intro f g
    change Λ (f * g).toLp = _
    rw [hβ_rep (f * g).toLp]
    let uf : ℝ → ℂ := f.toLp
    let ug : ℝ → ℂ := g.toLp
    have huf : Integrable uf rudinMeasure := L1.integrable_coeFn f.toLp
    have hug : Integrable ug rudinMeasure := L1.integrable_coeFn g.toLp
    have hprod_int : Integrable (fun p : ℝ × ℝ => uf (p.1 - p.2) * ug p.2 * β p.1)
        (rudinMeasure.prod rudinMeasure) := by
      have hconv_int := hug.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) huf
      have hconv_swap : Integrable (fun p : ℝ × ℝ => uf (p.1 - p.2) * ug p.2)
          (rudinMeasure.prod rudinMeasure) := by
        refine hconv_int.congr (ae_of_all _ fun p => ?_)
        simp [ContinuousLinearMap.mul_apply', mul_comm]
      exact integrable_mul_of_ae_bound hconv_swap
        (hβ_meas.comp measurable_fst).aestronglyMeasurable
        1 (ae_of_all _ fun p => hβ_bdd_one p.1)
    have hae_conv := hug.ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ) huf
    have hlhs_eq : ∫ x, ((f * g).toLp : ℝ → ℂ) x * β x ∂rudinMeasure =
        ∫ x, ∫ y, uf (x - y) * ug y * β x ∂rudinMeasure ∂rudinMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [rudinL1Algebra_mul_coeFn f g, hae_conv] with x hx hconv_x
      rw [hx]
      unfold rudinConv
      have hconv_x' : Integrable (fun y => uf (x - y) * ug y) rudinMeasure := by
        refine hconv_x.congr (ae_of_all _ fun y => ?_)
        simp [ContinuousLinearMap.mul_apply', mul_comm]
      simpa only [mul_comm _ (β x), mul_assoc] using
        (integral_const_mul (β x) fun y => uf (x - y) * ug y).symm.trans
          (integral_congr_ae (ae_of_all _ fun y => by ring))
    rw [hlhs_eq, ← integral_prod _ hprod_int, integral_prod_symm _ hprod_int]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    dsimp only
    have hpull : ∫ x, uf (x - y) * ug y * β x ∂rudinMeasure =
        ug y * ∫ x, uf (x - y) * β x ∂rudinMeasure := by
      have h1 : (fun x => uf (x - y) * ug y * β x) = fun x => ug y * (uf (x - y) * β x) := by
        ext x; ring
      rw [h1, integral_const_mul]
    rw [hpull, hβ_rep (rudinTranslateLp 1 y f.toLp)]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [rudinTranslateLp_coeFn 1 y f.toLp] with x hx
    rw [hx]
    rfl
  let γ : ℝ → ℂ := fun y => Λ (rudinTranslateLp 1 y f₀.toLp) / h f₀
  have hγ_cont : Continuous γ := by
    have htr_cont : Continuous (fun y : ℝ => rudinTranslateLp 1 y f₀.toLp) :=
      (theorem_9_5 1 ENNReal.one_ne_top f₀.toLp).continuous
    exact (Λ.continuous.comp htr_cont).div_const (h f₀)
  have hγ_zero : γ 0 = 1 := by
    dsimp [γ]
    rw [rudinTranslateLp_zero]
    exact div_self hf₀_ne
  have hγ_int_rep : ∀ g : RudinLp 1, Λ g = ∫ y, (g : ℝ → ℂ) y * γ y ∂rudinMeasure := by
    intro g
    let g_alg : RudinL1Algebra := RudinL1Algebra.ofLp g
    have hmul : h f₀ * Λ g = ∫ y, (g : ℝ → ℂ) y * (h f₀ * γ y) ∂rudinMeasure := by
      calc
        h f₀ * Λ g = h (f₀ * g_alg) := (map_mul h f₀ g_alg).symm
        _ = ∫ y, (g : ℝ → ℂ) y * Λ (rudinTranslateLp 1 y f₀.toLp) ∂rudinMeasure :=
          hconv_fubini f₀ g_alg
        _ = ∫ y, (g : ℝ → ℂ) y * (h f₀ * γ y) ∂rudinMeasure := by
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          dsimp [γ]
          rw [mul_div_cancel₀ _ hf₀_ne]
    have hpull : ∫ y, (g : ℝ → ℂ) y * (h f₀ * γ y) ∂rudinMeasure =
        h f₀ * ∫ y, (g : ℝ → ℂ) y * γ y ∂rudinMeasure := by
      have h1 : (fun y => (g : ℝ → ℂ) y * (h f₀ * γ y)) =
          fun y => h f₀ * ((g : ℝ → ℂ) y * γ y) := by ext y; ring
      rw [h1, integral_const_mul]
    rw [hpull] at hmul
    exact mul_left_cancel₀ hf₀_ne hmul
  have hγ_bdd_tr : ∀ y : ℝ, ‖γ y‖ ≤ ‖f₀‖ / ‖h f₀‖ := by
    intro y
    dsimp [γ]
    rw [norm_div]
    refine div_le_div_of_nonneg_right ?_ (norm_nonneg (h f₀))
    calc
      ‖Λ (rudinTranslateLp 1 y f₀.toLp)‖ ≤ ‖Λ‖ * ‖rudinTranslateLp 1 y f₀.toLp‖ := Λ.le_opNorm _
      _ ≤ 1 * ‖rudinTranslateLp 1 y f₀.toLp‖ :=
        mul_le_mul_of_nonneg_right hΛ_norm_le (norm_nonneg _)
      _ = ‖f₀‖ := by rw [one_mul, LinearIsometryEquiv.norm_map, RudinL1Algebra.norm_toLp]
  have hγ_top : MemLp γ ∞ rudinMeasure :=
    memLp_top_of_bound hγ_cont.aestronglyMeasurable (‖f₀‖ / ‖h f₀‖) (ae_of_all _ hγ_bdd_tr)
  have hβ_eq_γ_ae : β =ᵐ[rudinMeasure] γ :=
    hβ_uniq β γ hβ_top hγ_top fun g => (hβ_rep g).symm.trans (hγ_int_rep g)
  have hγ_le_one : ∀ y : ℝ, ‖γ y‖ ≤ 1 := by
    intro y₀
    by_contra! hgt
    have hopen : IsOpen {y : ℝ | 1 < ‖γ y‖} := isOpen_lt continuous_const hγ_cont.norm
    have hpos : 0 < rudinMeasure {y : ℝ | 1 < ‖γ y‖} := hopen.measure_pos rudinMeasure ⟨y₀, hgt⟩
    have hnull : rudinMeasure {y : ℝ | 1 < ‖γ y‖} = 0 := by
      rw [EventuallyEq, ae_iff] at hβ_eq_γ_ae
      refine measure_mono_null (fun y (hy : 1 < ‖γ y‖) => ?_) hβ_eq_γ_ae
      intro hβγ
      have h1 := hβ_bdd_one y
      rw [hβγ] at h1
      linarith
    exact hpos.ne' hnull
  have htranslate_id : ∀ (f : RudinL1Algebra) (y : ℝ),
      Λ (rudinTranslateLp 1 y f.toLp) = h f * γ y := by
    intro f
    let lhs : ℝ → ℂ := fun y => Λ (rudinTranslateLp 1 y f.toLp)
    let rhs : ℝ → ℂ := fun y => h f * γ y
    have hlhs_cont : Continuous lhs :=
      Λ.continuous.comp (theorem_9_5 1 ENNReal.one_ne_top f.toLp).continuous
    have hrhs_cont : Continuous rhs := continuous_const.mul hγ_cont
    have hlhs_top : MemLp lhs ∞ rudinMeasure :=
      memLp_top_of_bound hlhs_cont.aestronglyMeasurable ‖f‖ (ae_of_all _ fun y => by
        calc
          ‖Λ (rudinTranslateLp 1 y f.toLp)‖ ≤ ‖Λ‖ * ‖rudinTranslateLp 1 y f.toLp‖ := Λ.le_opNorm _
          _ ≤ 1 * ‖rudinTranslateLp 1 y f.toLp‖ :=
            mul_le_mul_of_nonneg_right hΛ_norm_le (norm_nonneg _)
          _ = ‖f‖ := by rw [one_mul, LinearIsometryEquiv.norm_map, RudinL1Algebra.norm_toLp])
    have hrhs_top : MemLp rhs ∞ rudinMeasure :=
      memLp_top_of_bound hrhs_cont.aestronglyMeasurable ‖h f‖ (ae_of_all _ fun y => by
        dsimp [rhs]
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hγ_le_one y))
    have hae_eq : lhs =ᵐ[rudinMeasure] rhs := by
      refine hβ_uniq lhs rhs hlhs_top hrhs_top fun g => ?_
      let g_alg : RudinL1Algebra := RudinL1Algebra.ofLp g
      calc
        ∫ y, (g : ℝ → ℂ) y * lhs y ∂rudinMeasure = h (f * g_alg) := (hconv_fubini f g_alg).symm
        _ = h f * Λ g := map_mul h f g_alg
        _ = h f * ∫ y, (g : ℝ → ℂ) y * γ y ∂rudinMeasure := by rw [hγ_int_rep g]
        _ = ∫ y, (g : ℝ → ℂ) y * rhs y ∂rudinMeasure := by
          rw [← integral_const_mul]
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          dsimp [rhs]; ring
    exact congr_fun ((hlhs_cont.ae_eq_iff_eq rudinMeasure hrhs_cont).mp hae_eq)
  have hγ_add : ∀ x y : ℝ, γ (x + y) = γ x * γ y := by
    intro x y
    let fx : RudinL1Algebra := RudinL1Algebra.ofLp (rudinTranslateLp 1 x f₀.toLp)
    have hfx_eval : h fx = h f₀ * γ x := htranslate_id f₀ x
    have hxy : h f₀ * γ (x + y) = Λ (rudinTranslateLp 1 (x + y) f₀.toLp) := by
      dsimp [γ]
      rw [mul_div_cancel₀ _ hf₀_ne]
    have hcomp : rudinTranslateLp 1 (x + y) f₀.toLp = rudinTranslateLp 1 y fx.toLp := by
      rw [add_comm x y, rudinTranslateLp_add]
    rw [hcomp, htranslate_id fx y, hfx_eval, mul_assoc] at hxy
    exact mul_left_cancel₀ hf₀_ne hxy
  obtain ⟨hchar, hγ_diff, t, _, hγ_exp⟩ :=
    theorem_9_22_exponential_character hγ_cont hγ_zero hγ_add hγ_le_one
  refine ⟨β, γ, t, hβ_meas, hβ_bdd_one, hchar, hγ_diff, hβ_eq_γ_ae, hγ_exp, ?_, ?_⟩
  · intro f
    exact hγ_int_rep f.toLp
  · intro f
    change Λ f.toLp = rudinFourier f.toLp t
    rw [hγ_int_rep f.toLp]
    unfold rudinFourier
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [hγ_exp x]

/-- 9.23: Every real `t ∈ ℝ` defines a nonzero complex homomorphism `f ↦ f̂(t)` of the convolution
Banach algebra `L¹(m)`. -/
def rudinFourierEvalHom (t : ℝ) : RudinComplexHom RudinL1Algebra where
  toFun f := rudinFourier f.toLp t
  map_mul' f g := by
    change rudinFourierCLM (f * g).toLp t = rudinFourierCLM f.toLp t * rudinFourierCLM g.toLp t
    rw [rudinFourierCLM_mul]; rfl
  map_zero' := by
    change rudinFourierCLM (0 : RudinLp 1) t = 0
    simp
  map_add' f g := by
    change rudinFourierCLM (f.toLp + g.toLp) t =
      rudinFourierCLM f.toLp t + rudinFourierCLM g.toLp t
    rw [map_add]; rfl
  map_smul' c f := by
    change rudinFourierCLM (c • f.toLp) t = c • rudinFourierCLM f.toLp t
    rw [map_smul]; rfl

theorem rudinFourierEvalHom_ne_zero (t : ℝ) : rudinFourierEvalHom t ≠ 0 := by
  intro hzero
  have hfH_real : Integrable (fun x : ℝ => rudinH (1 * x)) rudinMeasure :=
    rudinH_scaled_integrable one_pos
  have hfH : Integrable (fun x : ℝ => (rudinH (1 * x) : ℂ)) rudinMeasure :=
    Complex.ofRealCLM.integrable_comp hfH_real
  let f₀ : RudinL1Algebra :=
    RudinL1Algebra.ofLp ((memLp_one_iff_integrable.mpr hfH).toLp
      (fun x : ℝ => (rudinH (1 * x) : ℂ)))
  have hval0 : rudinFourierEvalHom t f₀ = 0 := by rw [hzero]; rfl
  change rudinFourier f₀.toLp t = 0 at hval0
  rw [rudinFourier_congr_ae (memLp_one_iff_integrable.mpr hfH).coeFn_toLp] at hval0
  have heq : rudinFourier (fun x : ℝ => (rudinH (1 * x) : ℂ)) t =
      (rudinPoisson 1 (-t) : ℂ) := by
    rw [← theorem_9_7_poisson_formula one_pos (-t)]
    unfold rudinFourier rudinPoissonInt
    congr 1; ext x; congr 2; push_cast; ring
  rw [heq] at hval0
  exact (Complex.ofReal_ne_zero.mpr (rudinPoisson_pos one_pos (-t)).ne') hval0

/-- 9.23: To every nonzero complex homomorphism `h` of the convolution Banach algebra `L¹(m)` there
corresponds a **unique** real number `t ∈ ℝ` such that `h(f) = f̂(t)` for every `f ∈ L¹(m)`. -/
theorem theorem_9_23 {h : RudinComplexHom RudinL1Algebra} (hh_ne : h ≠ 0) :
    ∃! t : ℝ, ∀ f : RudinL1Algebra, h f = rudinFourier f.toLp t := by
  obtain ⟨_, _, t, _, _, _, _, _, _, _, ht_eval⟩ := theorem_9_22 hh_ne
  refine ⟨t, ht_eval, ?_⟩
  intro s hs_eval
  have hfH_real : Integrable (fun x : ℝ => rudinH (1 * x)) rudinMeasure :=
    rudinH_scaled_integrable one_pos
  have hfH : Integrable (fun x : ℝ => (rudinH (1 * x) : ℂ)) rudinMeasure :=
    Complex.ofRealCLM.integrable_comp hfH_real
  let g_mod : ℝ → ℂ := fun x => (rudinH (1 * x) : ℂ) * Complex.exp (Complex.I * t * x)
  have hg_mod_int : Integrable g_mod rudinMeasure := by
    refine integrable_mul_of_ae_bound hfH
      (by fun_prop : Continuous fun x : ℝ => Complex.exp (Complex.I * t * x)).aestronglyMeasurable
      1 (ae_of_all _ fun x => ?_)
    have h1 : Complex.I * (t : ℂ) * (x : ℂ) = ↑(t * x) * Complex.I := by push_cast; ring
    rw [h1, Complex.norm_exp_ofReal_mul_I]
  let f_mod : RudinL1Algebra :=
    RudinL1Algebra.ofLp ((memLp_one_iff_integrable.mpr hg_mod_int).toLp g_mod)
  have hhat_mod : ∀ u : ℝ,
      rudinFourier f_mod.toLp u = (rudinPoisson 1 (t - u) : ℂ) := by
    intro u
    rw [rudinFourier_congr_ae (memLp_one_iff_integrable.mpr hg_mod_int).coeFn_toLp]
    dsimp [g_mod]
    rw [theorem_9_2_a hfH t u, ← theorem_9_7_poisson_formula one_pos (t - u)]
    unfold rudinFourier rudinPoissonInt
    congr 1; ext x; congr 2; push_cast; ring
  have heq_st : rudinFourier f_mod.toLp s = rudinFourier f_mod.toLp t :=
    (hs_eval f_mod).symm.trans (ht_eval f_mod)
  rw [hhat_mod s, hhat_mod t, sub_self] at heq_st
  have hreal_eq : rudinPoisson 1 (t - s) = rudinPoisson 1 0 :=
    Complex.ofReal_injective heq_st
  unfold rudinPoisson at hreal_eq
  have hc_pos : 0 < Real.sqrt (2 / Real.pi) := by positivity
  have hd_pos : 0 < (1 : ℝ) ^ 2 + (t - s) ^ 2 := by positivity
  have h1 : (1 : ℝ) ^ 2 + (t - s) ^ 2 = 1 := by
    have hcleared : Real.sqrt (2 / Real.pi) * 1 =
        Real.sqrt (2 / Real.pi) * 1 / (1 ^ 2 + 0 ^ 2) * (1 ^ 2 + (t - s) ^ 2) :=
      (div_eq_iff hd_pos.ne').mp hreal_eq
    have hc_ne : Real.sqrt (2 / Real.pi) ≠ 0 := hc_pos.ne'
    have hdiv : Real.sqrt (2 / Real.pi) * 1 / (1 ^ 2 + 0 ^ 2) = Real.sqrt (2 / Real.pi) := by ring
    rw [hdiv, mul_one] at hcleared
    exact mul_left_cancel₀ hc_ne (by linarith)
  have hsq0 : (t - s) ^ 2 = 0 := by linarith
  have hsub0 : t - s = 0 := sq_eq_zero_iff.mp hsq0
  linarith

end Node9_18_to_9_23

end RudinRCA.Chapter09
