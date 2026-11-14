import RudinRCA.Chapter09
import RudinRCA.Chapter15
import RudinRCA.Chapter17
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus

/-!
# Chapter 19: Holomorphic Fourier Transforms (`19.1`–`19.11`)

Complete formalization of Walter Rudin, *Real and Complex Analysis* (3rd ed., McGraw-Hill, 1987),
Chapter 19, all 11 numbered nodes `19.1`–`19.11` (printed pp. 371–383), following
`SCOPING-H-19-20.md` and `BRIEF.md`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric TopologicalSpace Complex
open scoped ENNReal NNReal Topology ComplexConjugate

namespace RudinRCA.Chapter19

/-! ## §19.0: Chapter 19 Normalization & `L¹ ∩ L²` / `L²` Fourier Adapters -/

/-- Forward Fourier integral on `(ℝ, volume)` with Chapter 19 kernel `exp(i t x)`. -/
def ch19Fourier (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t : ℝ, g t * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))

/-- Inverse Fourier integral on `(ℝ, volume)` with factor `1 / (2π)` and kernel `exp(-i t x)`. -/
def ch19InvFourier (h : ℝ → ℂ) (t : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ x : ℝ, h x * Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))

lemma ch19Fourier_eq_rudinFourierInv (g : ℝ → ℂ) (x : ℝ) :
    ch19Fourier g x = (RudinRCA.Chapter09.rudinScale : ℂ) *
      RudinRCA.Chapter09.rudinFourierInv g x := by
  unfold ch19Fourier RudinRCA.Chapter09.rudinFourierInv
  rw [RudinRCA.Chapter09.integral_rudinMeasure, Complex.real_smul, ← mul_assoc]
  have hsf : (RudinRCA.Chapter09.rudinScale : ℂ) * (RudinRCA.Chapter09.rudinFactor : ℂ) = 1 := by
    exact_mod_cast RudinRCA.Chapter09.rudinScale_mul_factor
  rw [hsf, one_mul]
  congr 1 with t
  congr 2
  ring

lemma ch19InvFourier_eq_rudinFourier (h : ℝ → ℂ) (t : ℝ) :
    ch19InvFourier h t = (RudinRCA.Chapter09.rudinFactor : ℂ) *
      RudinRCA.Chapter09.rudinFourier h t := by
  unfold ch19InvFourier RudinRCA.Chapter09.rudinFourier
  rw [RudinRCA.Chapter09.integral_rudinMeasure, Complex.real_smul, ← mul_assoc]
  congr 1
  · have hsq : RudinRCA.Chapter09.rudinFactor ^ 2 = 1 / (2 * Real.pi) := by
      rw [RudinRCA.Chapter09.rudinFactor_eq_inv_scale, inv_pow,
        RudinRCA.Chapter09.rudinScale_sq, one_div]
    exact_mod_cast hsq.symm.trans (sq RudinRCA.Chapter09.rudinFactor)
  · congr 1 with x
    congr 2
    ring

lemma norm_exp_I_mul_real_mul_real (t x : ℝ) :
    ‖Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))‖ = 1 := by
  have h : Complex.I * (t : ℂ) * (x : ℂ) = ((t * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma norm_exp_neg_I_mul_real_mul_real (t x : ℝ) :
    ‖Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))‖ = 1 := by
  have h : -Complex.I * (t : ℂ) * (x : ℂ) = ((-(t * x) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma norm_exp_I_mul_real_mul_complex (t : ℝ) (z : ℂ) :
    ‖Complex.exp (Complex.I * (t : ℂ) * z)‖ = Real.exp (-t * z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

lemma continuous_ch19Fourier_of_integrable {g : ℝ → ℂ} (hg : Integrable g volume) :
    Continuous (ch19Fourier g) := by
  have hg_m : Integrable g RudinRCA.Chapter09.rudinMeasure :=
    RudinRCA.Chapter09.integrable_rudinMeasure_iff.mpr hg
  have h_eq : ch19Fourier g = fun x => (RudinRCA.Chapter09.rudinScale : ℂ) *
      RudinRCA.Chapter09.rudinFourier g (-x) := by
    ext x
    rw [ch19Fourier_eq_rudinFourierInv, RudinRCA.Chapter09.rudinFourierInv_eq_rudinFourier_neg]
  rw [h_eq]
  exact continuous_const.mul ((RudinRCA.Chapter09.theorem_9_6_continuous hg_m).comp continuous_neg)

lemma continuous_ch19InvFourier_of_integrable {h : ℝ → ℂ} (hh : Integrable h volume) :
    Continuous (ch19InvFourier h) := by
  have hh_m : Integrable h RudinRCA.Chapter09.rudinMeasure :=
    RudinRCA.Chapter09.integrable_rudinMeasure_iff.mpr hh
  have h_eq : ch19InvFourier h = fun t => (RudinRCA.Chapter09.rudinFactor : ℂ) *
      RudinRCA.Chapter09.rudinFourier h t := by
    ext t; exact ch19InvFourier_eq_rudinFourier h t
  rw [h_eq]
  exact continuous_const.mul (RudinRCA.Chapter09.theorem_9_6_continuous hh_m)

private lemma l2_norm_sq_rudinMeasure_to_volume {u : ℝ → ℂ}
    (hu : MemLp u 2 RudinRCA.Chapter09.rudinMeasure) :
    ‖hu.toLp u‖ ^ 2 = RudinRCA.Chapter09.rudinFactor * ∫ x : ℝ, ‖u x‖ ^ 2 := by
  rw [Lp.norm_toLp, hu.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  rw [ENNReal.toReal_ofReal (by positivity), RudinRCA.Chapter09.integral_rudinMeasure, smul_eq_mul]
  have hnn : 0 ≤ RudinRCA.Chapter09.rudinFactor * ∫ x : ℝ, ‖u x‖ ^ (2 : ℝ) :=
    mul_nonneg RudinRCA.Chapter09.rudinFactor_pos.le
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _)
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hnn]
  norm_num

/-- `L¹ ∩ L²` Plancherel identity for `ch19Fourier`:
`(1 / (2π)) ∫ ‖∫ g(t) e^{itx} dt‖² dx = ∫ ‖g(t)‖² dt`. -/
theorem ch19Fourier_plancherel_L1_L2 {g : ℝ → ℂ}
    (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume) :
    MemLp (ch19Fourier g) 2 volume ∧
      (1 / (2 * Real.pi)) * ∫ x : ℝ, ‖ch19Fourier g x‖ ^ 2 = ∫ t : ℝ, ‖g t‖ ^ 2 := by
  have hg1_m : Integrable g RudinRCA.Chapter09.rudinMeasure :=
    RudinRCA.Chapter09.integrable_rudinMeasure_iff.mpr hg1
  have hg2_m : MemLp g 2 RudinRCA.Chapter09.rudinMeasure :=
    RudinRCA.Chapter09.memLp_rudinMeasure_iff.mpr hg2
  have hae_m := RudinRCA.Chapter09.theorem_9_13_inv_L1_L2_compat hg1_m hg2_m
  let Φ := RudinRCA.Chapter09.rudinPlancherel.symm (hg2_m.toLp g)
  have hΦ_mem_m : MemLp (Φ : ℝ → ℂ) 2 RudinRCA.Chapter09.rudinMeasure := Lp.memLp Φ
  have hfinv_mem_m : MemLp (RudinRCA.Chapter09.rudinFourierInv g) 2 RudinRCA.Chapter09.rudinMeasure :=
    hΦ_mem_m.ae_eq hae_m
  have hfinv_mem : MemLp (RudinRCA.Chapter09.rudinFourierInv g) 2 volume :=
    RudinRCA.Chapter09.memLp_rudinMeasure_iff.mp hfinv_mem_m
  have hch_eq : ch19Fourier g = fun x => (RudinRCA.Chapter09.rudinScale : ℂ) *
      RudinRCA.Chapter09.rudinFourierInv g x := funext (ch19Fourier_eq_rudinFourierInv g)
  have hch_mem : MemLp (ch19Fourier g) 2 volume := by
    rw [hch_eq]
    exact hfinv_mem.const_mul _
  refine ⟨hch_mem, ?_⟩
  have hiso : ‖Φ‖ ^ 2 = ‖hg2_m.toLp g‖ ^ 2 := by
    rw [RudinRCA.Chapter09.rudinPlancherel.symm.norm_map]
  have hΦ_toLp : hΦ_mem_m.toLp (Φ : ℝ → ℂ) = Φ := Lp.toLp_coeFn Φ hΦ_mem_m
  have h_lhs_m : ‖Φ‖ ^ 2 = RudinRCA.Chapter09.rudinFactor *
      ∫ x : ℝ, ‖RudinRCA.Chapter09.rudinFourierInv g x‖ ^ 2 := by
    rw [← hΦ_toLp, l2_norm_sq_rudinMeasure_to_volume hΦ_mem_m]
    congr 1
    apply integral_congr_ae
    filter_upwards [RudinRCA.Chapter09.ae_rudinMeasure_iff.mp hae_m] with x hx
    rw [hx]
  have h_rhs_m : ‖hg2_m.toLp g‖ ^ 2 = RudinRCA.Chapter09.rudinFactor * ∫ t : ℝ, ‖g t‖ ^ 2 :=
    l2_norm_sq_rudinMeasure_to_volume hg2_m
  have heq_int : ∫ x : ℝ, ‖RudinRCA.Chapter09.rudinFourierInv g x‖ ^ 2 = ∫ t : ℝ, ‖g t‖ ^ 2 :=
    mul_left_cancel₀ RudinRCA.Chapter09.rudinFactor_ne_zero (h_lhs_m.symm.trans (hiso.trans h_rhs_m))
  have hnorm_sq : ∀ x : ℝ, ‖ch19Fourier g x‖ ^ 2 =
      (2 * Real.pi) * ‖RudinRCA.Chapter09.rudinFourierInv g x‖ ^ 2 := by
    intro x
    rw [ch19Fourier_eq_rudinFourierInv, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg RudinRCA.Chapter09.rudinScale_pos.le, mul_pow,
      RudinRCA.Chapter09.rudinScale_sq]
  simp_rw [hnorm_sq, integral_const_mul]
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := (mul_pos two_pos Real.pi_pos).ne'
  rw [← mul_assoc, one_div, inv_mul_cancel₀ h2pi, one_mul, heq_int]

/-- `L¹ ∩ L²` Plancherel identity for `ch19InvFourier`:
`∫ ‖(1/(2π)) ∫ h(x) e^{-itx} dx‖² dt = (1 / (2π)) ∫ ‖h(x)‖² dx`. -/
theorem ch19InvFourier_plancherel_L1_L2 {h : ℝ → ℂ}
    (hh1 : Integrable h volume) (hh2 : MemLp h 2 volume) :
    MemLp (ch19InvFourier h) 2 volume ∧
      ∫ t : ℝ, ‖ch19InvFourier h t‖ ^ 2 = (1 / (2 * Real.pi)) * ∫ x : ℝ, ‖h x‖ ^ 2 := by
  have hh1_m : Integrable h RudinRCA.Chapter09.rudinMeasure :=
    RudinRCA.Chapter09.integrable_rudinMeasure_iff.mpr hh1
  have hh2_m : MemLp h 2 RudinRCA.Chapter09.rudinMeasure :=
    RudinRCA.Chapter09.memLp_rudinMeasure_iff.mpr hh2
  have hae_m := RudinRCA.Chapter09.theorem_9_13_L1_L2_compat hh1_m hh2_m
  let Ψ := RudinRCA.Chapter09.rudinPlancherel (hh2_m.toLp h)
  have hΨ_mem_m : MemLp (Ψ : ℝ → ℂ) 2 RudinRCA.Chapter09.rudinMeasure := Lp.memLp Ψ
  have hf_mem_m : MemLp (RudinRCA.Chapter09.rudinFourier h) 2 RudinRCA.Chapter09.rudinMeasure :=
    hΨ_mem_m.ae_eq hae_m
  have hf_mem : MemLp (RudinRCA.Chapter09.rudinFourier h) 2 volume :=
    RudinRCA.Chapter09.memLp_rudinMeasure_iff.mp hf_mem_m
  have hinv_eq : ch19InvFourier h = fun t => (RudinRCA.Chapter09.rudinFactor : ℂ) *
      RudinRCA.Chapter09.rudinFourier h t := funext (ch19InvFourier_eq_rudinFourier h)
  refine ⟨by rw [hinv_eq]; exact hf_mem.const_mul _, ?_⟩
  have hiso : ‖Ψ‖ ^ 2 = ‖hh2_m.toLp h‖ ^ 2 := by
    rw [RudinRCA.Chapter09.rudinPlancherel.norm_map]
  have hΨ_toLp : hΨ_mem_m.toLp (Ψ : ℝ → ℂ) = Ψ := Lp.toLp_coeFn Ψ hΨ_mem_m
  have h_lhs_m : ‖Ψ‖ ^ 2 = RudinRCA.Chapter09.rudinFactor *
      ∫ t : ℝ, ‖RudinRCA.Chapter09.rudinFourier h t‖ ^ 2 := by
    rw [← hΨ_toLp, l2_norm_sq_rudinMeasure_to_volume hΨ_mem_m]
    congr 1
    apply integral_congr_ae
    filter_upwards [RudinRCA.Chapter09.ae_rudinMeasure_iff.mp hae_m] with t ht
    rw [ht]
  have h_rhs_m : ‖hh2_m.toLp h‖ ^ 2 = RudinRCA.Chapter09.rudinFactor * ∫ x : ℝ, ‖h x‖ ^ 2 :=
    l2_norm_sq_rudinMeasure_to_volume hh2_m
  have heq_int : ∫ t : ℝ, ‖RudinRCA.Chapter09.rudinFourier h t‖ ^ 2 = ∫ x : ℝ, ‖h x‖ ^ 2 :=
    mul_left_cancel₀ RudinRCA.Chapter09.rudinFactor_ne_zero (h_lhs_m.symm.trans (hiso.trans h_rhs_m))
  have hfac_sq : RudinRCA.Chapter09.rudinFactor ^ 2 = 1 / (2 * Real.pi) := by
    rw [RudinRCA.Chapter09.rudinFactor_eq_inv_scale, inv_pow,
      RudinRCA.Chapter09.rudinScale_sq, one_div]
  have hnorm_sq : ∀ t : ℝ, ‖ch19InvFourier h t‖ ^ 2 =
      (1 / (2 * Real.pi)) * ‖RudinRCA.Chapter09.rudinFourier h t‖ ^ 2 := by
    intro t
    rw [ch19InvFourier_eq_rudinFourier, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg RudinRCA.Chapter09.rudinFactor_pos.le, mul_pow, hfac_sq]
  simp_rw [hnorm_sq, integral_const_mul, heq_int]

/-- `L¹` Fourier inversion in Chapter 19 normalization: if `h ∈ L¹(ℝ)` and `ch19InvFourier h ∈ L¹(ℝ)`,
then `h =ᵐ[volume] ch19Fourier (ch19InvFourier h)`. -/
theorem ch19_fourier_inversion_ae {h : ℝ → ℂ}
    (hh1 : Integrable h volume) (hG1 : Integrable (ch19InvFourier h) volume) :
    h =ᵐ[volume] ch19Fourier (ch19InvFourier h) := by
  have hh1_m : Integrable h RudinRCA.Chapter09.rudinMeasure :=
    RudinRCA.Chapter09.integrable_rudinMeasure_iff.mpr hh1
  have hhat_eq : RudinRCA.Chapter09.rudinFourier h = fun t =>
      (RudinRCA.Chapter09.rudinScale : ℂ) * ch19InvFourier h t := by
    ext t
    rw [ch19InvFourier_eq_rudinFourier, ← mul_assoc]
    have hsf : (RudinRCA.Chapter09.rudinScale : ℂ) * (RudinRCA.Chapter09.rudinFactor : ℂ) = 1 := by
      exact_mod_cast RudinRCA.Chapter09.rudinScale_mul_factor
    rw [hsf, one_mul]
  have hhat_m : Integrable (RudinRCA.Chapter09.rudinFourier h) RudinRCA.Chapter09.rudinMeasure := by
    apply RudinRCA.Chapter09.integrable_rudinMeasure_iff.mpr
    rw [hhat_eq]
    exact hG1.const_mul _
  have hinv := (RudinRCA.Chapter09.theorem_9_11 hh1_m hhat_m).2
  filter_upwards [RudinRCA.Chapter09.ae_rudinMeasure_iff.mp hinv] with x hx
  rw [hx, ch19Fourier_eq_rudinFourierInv]
  unfold RudinRCA.Chapter09.rudinFourierInv
  rw [hhat_eq]
  simp_rw [mul_assoc]
  rw [integral_const_mul]

theorem ch19_fourier_inversion_pointwise {h : ℝ → ℂ}
    (hh_cont : Continuous h) (hh1 : Integrable h volume)
    (hG1 : Integrable (ch19InvFourier h) volume) :
    ∀ x : ℝ, h x = ch19Fourier (ch19InvFourier h) x := by
  have hae := ch19_fourier_inversion_ae hh1 hG1
  have hcont_rhs := continuous_ch19Fourier_of_integrable hG1
  exact congr_fun (Continuous.ae_eq_iff_eq volume hh_cont hcont_rhs |>.mp hae)

/-- `L²` inverse Fourier transform in Chapter 19 normalization. -/
def ch19InvFourierL2 (h : ℝ → ℂ) (hh : MemLp h 2 volume) : ℝ → ℂ :=
  let hh_m : MemLp h 2 RudinRCA.Chapter09.rudinMeasure :=
    RudinRCA.Chapter09.memLp_rudinMeasure_iff.mpr hh
  fun t => (RudinRCA.Chapter09.rudinFactor : ℂ) *
    (RudinRCA.Chapter09.rudinPlancherel (hh_m.toLp h) : ℝ → ℂ) t

theorem ch19InvFourierL2_memLp {h : ℝ → ℂ} (hh : MemLp h 2 volume) :
    MemLp (ch19InvFourierL2 h hh) 2 volume := by
  let hh_m : MemLp h 2 RudinRCA.Chapter09.rudinMeasure :=
    RudinRCA.Chapter09.memLp_rudinMeasure_iff.mpr hh
  have hm : MemLp (RudinRCA.Chapter09.rudinPlancherel (hh_m.toLp h) : ℝ → ℂ) 2 volume :=
    RudinRCA.Chapter09.memLp_rudinMeasure_iff.mp (Lp.memLp _)
  exact hm.const_mul _

theorem ch19InvFourierL2_compat {h : ℝ → ℂ} (hh1 : Integrable h volume) (hh2 : MemLp h 2 volume) :
    ch19InvFourierL2 h hh2 =ᵐ[volume] ch19InvFourier h := by
  let hh1_m : Integrable h RudinRCA.Chapter09.rudinMeasure :=
    RudinRCA.Chapter09.integrable_rudinMeasure_iff.mpr hh1
  let hh2_m : MemLp h 2 RudinRCA.Chapter09.rudinMeasure :=
    RudinRCA.Chapter09.memLp_rudinMeasure_iff.mpr hh2
  have hae := RudinRCA.Chapter09.ae_rudinMeasure_iff.mp
    (RudinRCA.Chapter09.theorem_9_13_L1_L2_compat hh1_m hh2_m)
  filter_upwards [hae] with t ht
  dsimp [ch19InvFourierL2]
  rw [ht, ch19InvFourier_eq_rudinFourier]

theorem ch19InvFourierL2_sub_norm_sq {h₁ h₂ : ℝ → ℂ}
    (hh₁ : MemLp h₁ 2 volume) (hh₂ : MemLp h₂ 2 volume) :
    ∫ t : ℝ, ‖ch19InvFourierL2 h₁ hh₁ t - ch19InvFourierL2 h₂ hh₂ t‖ ^ 2 =
      (1 / (2 * Real.pi)) * ∫ x : ℝ, ‖h₁ x - h₂ x‖ ^ 2 := by
  let hh₁_m : MemLp h₁ 2 RudinRCA.Chapter09.rudinMeasure :=
    RudinRCA.Chapter09.memLp_rudinMeasure_iff.mpr hh₁
  let hh₂_m : MemLp h₂ 2 RudinRCA.Chapter09.rudinMeasure :=
    RudinRCA.Chapter09.memLp_rudinMeasure_iff.mpr hh₂
  let u₁ := hh₁_m.toLp h₁
  let u₂ := hh₂_m.toLp h₂
  let Ψ := RudinRCA.Chapter09.rudinPlancherel (u₁ - u₂)
  have hΨ_norm : ‖Ψ‖ ^ 2 = ‖u₁ - u₂‖ ^ 2 := by
    rw [RudinRCA.Chapter09.rudinPlancherel.norm_map]
  have hΨ_sub : (Ψ : ℝ → ℂ) =ᵐ[volume] fun t =>
      (RudinRCA.Chapter09.rudinPlancherel u₁ : ℝ → ℂ) t -
        (RudinRCA.Chapter09.rudinPlancherel u₂ : ℝ → ℂ) t := by
    have hmap : Ψ = RudinRCA.Chapter09.rudinPlancherel u₁ - RudinRCA.Chapter09.rudinPlancherel u₂ :=
      map_sub RudinRCA.Chapter09.rudinPlancherel u₁ u₂
    rw [hmap]
    exact RudinRCA.Chapter09.ae_rudinMeasure_iff.mp (Lp.coeFn_sub _ _)
  have hΨ_mem := Lp.memLp Ψ
  have hΨ_toLp : hΨ_mem.toLp (Ψ : ℝ → ℂ) = Ψ := Lp.toLp_coeFn Ψ hΨ_mem
  have h_lhs : ‖Ψ‖ ^ 2 = RudinRCA.Chapter09.rudinFactor *
      ∫ t : ℝ, ‖(RudinRCA.Chapter09.rudinPlancherel u₁ : ℝ → ℂ) t -
        (RudinRCA.Chapter09.rudinPlancherel u₂ : ℝ → ℂ) t‖ ^ 2 := by
    rw [← hΨ_toLp, l2_norm_sq_rudinMeasure_to_volume hΨ_mem]
    congr 1
    apply integral_congr_ae
    filter_upwards [hΨ_sub] with t ht
    rw [ht]
  have h_u_sub : ((u₁ - u₂ : RudinRCA.Chapter09.RudinLp 2) : ℝ → ℂ) =ᵐ[volume] fun x => h₁ x - h₂ x := by
    have h1 := RudinRCA.Chapter09.ae_rudinMeasure_iff.mp (Lp.coeFn_sub u₁ u₂)
    have h2 := RudinRCA.Chapter09.ae_rudinMeasure_iff.mp hh₁_m.coeFn_toLp
    have h3 := RudinRCA.Chapter09.ae_rudinMeasure_iff.mp hh₂_m.coeFn_toLp
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    exact hx1.trans (by simp [u₁, u₂, hx2, hx3])
  have hu_mem := Lp.memLp (u₁ - u₂)
  have hu_toLp : hu_mem.toLp ((u₁ - u₂ : RudinRCA.Chapter09.RudinLp 2) : ℝ → ℂ) = u₁ - u₂ :=
    Lp.toLp_coeFn (u₁ - u₂) hu_mem
  have h_rhs : ‖u₁ - u₂‖ ^ 2 = RudinRCA.Chapter09.rudinFactor * ∫ x : ℝ, ‖h₁ x - h₂ x‖ ^ 2 := by
    rw [← hu_toLp, l2_norm_sq_rudinMeasure_to_volume hu_mem]
    congr 1
    apply integral_congr_ae
    filter_upwards [h_u_sub] with x hx
    rw [hx]
  have heq_int : ∫ t : ℝ, ‖(RudinRCA.Chapter09.rudinPlancherel u₁ : ℝ → ℂ) t -
      (RudinRCA.Chapter09.rudinPlancherel u₂ : ℝ → ℂ) t‖ ^ 2 = ∫ x : ℝ, ‖h₁ x - h₂ x‖ ^ 2 :=
    mul_left_cancel₀ RudinRCA.Chapter09.rudinFactor_ne_zero (h_lhs.symm.trans (hΨ_norm.trans h_rhs))
  have hfac_sq : RudinRCA.Chapter09.rudinFactor ^ 2 = 1 / (2 * Real.pi) := by
    rw [RudinRCA.Chapter09.rudinFactor_eq_inv_scale, inv_pow,
      RudinRCA.Chapter09.rudinScale_sq, one_div]
  have hpt : ∀ t : ℝ, ‖ch19InvFourierL2 h₁ hh₁ t - ch19InvFourierL2 h₂ hh₂ t‖ ^ 2 =
      (1 / (2 * Real.pi)) * ‖(RudinRCA.Chapter09.rudinPlancherel u₁ : ℝ → ℂ) t -
        (RudinRCA.Chapter09.rudinPlancherel u₂ : ℝ → ℂ) t‖ ^ 2 := by
    intro t
    dsimp [ch19InvFourierL2]
    rw [← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg RudinRCA.Chapter09.rudinFactor_pos.le, mul_pow, hfac_sq]
  simp_rw [hpt, integral_const_mul, heq_int]

/-- `L²` Fourier inversion (`Chapter09.theorem_9_14` bridge). -/
theorem ch19InvFourierL2_inversion_ae {h F : ℝ → ℂ} (hh : MemLp h 2 volume)
    (hF_ae : F =ᵐ[volume] ch19InvFourierL2 h hh) (hF1 : Integrable F volume) :
    h =ᵐ[volume] ch19Fourier F := by
  let hh_m : MemLp h 2 RudinRCA.Chapter09.rudinMeasure :=
    RudinRCA.Chapter09.memLp_rudinMeasure_iff.mpr hh
  have hplan_ae : (RudinRCA.Chapter09.rudinPlancherel (hh_m.toLp h) : ℝ → ℂ) =ᵐ[volume]
      fun t => (RudinRCA.Chapter09.rudinScale : ℂ) * F t := by
    filter_upwards [hF_ae] with t ht
    rw [ht]
    dsimp [ch19InvFourierL2]
    rw [← mul_assoc]
    have hsf : (RudinRCA.Chapter09.rudinScale : ℂ) * (RudinRCA.Chapter09.rudinFactor : ℂ) = 1 := by
      exact_mod_cast RudinRCA.Chapter09.rudinScale_mul_factor
    rw [hsf, one_mul]
  have hplan_int_vol : Integrable (RudinRCA.Chapter09.rudinPlancherel (hh_m.toLp h) : ℝ → ℂ) volume :=
    (hF1.const_mul (RudinRCA.Chapter09.rudinScale : ℂ)).congr hplan_ae.symm
  have hplan_int_m : Integrable (RudinRCA.Chapter09.rudinPlancherel (hh_m.toLp h) : ℝ → ℂ)
      RudinRCA.Chapter09.rudinMeasure :=
    RudinRCA.Chapter09.integrable_rudinMeasure_iff.mpr hplan_int_vol
  have h914 := RudinRCA.Chapter09.ae_rudinMeasure_iff.mp
    (RudinRCA.Chapter09.theorem_9_14 (hh_m.toLp h) hplan_int_m).2
  have h_toLp_ae := RudinRCA.Chapter09.ae_rudinMeasure_iff.mp hh_m.coeFn_toLp
  have h_rhs_eq : ∀ x : ℝ,
      RudinRCA.Chapter09.rudinFourierInv (RudinRCA.Chapter09.rudinPlancherel (hh_m.toLp h)) x =
        ch19Fourier F x := by
    intro x
    have hcongr : RudinRCA.Chapter09.rudinFourierInv
        (RudinRCA.Chapter09.rudinPlancherel (hh_m.toLp h)) x =
        RudinRCA.Chapter09.rudinFourierInv
          (fun t => (RudinRCA.Chapter09.rudinScale : ℂ) * F t) x := by
      unfold RudinRCA.Chapter09.rudinFourierInv
      apply integral_congr_ae
      filter_upwards [RudinRCA.Chapter09.ae_rudinMeasure_iff.mpr hplan_ae] with t ht
      rw [ht]
    rw [hcongr, ch19Fourier_eq_rudinFourierInv]
    unfold RudinRCA.Chapter09.rudinFourierInv
    simp_rw [mul_assoc]
    rw [integral_const_mul]
  filter_upwards [h_toLp_ae, h914] with x hx1 hx2
  rw [← hx1, hx2, h_rhs_eq]

/-! ## §19.1: Holomorphic Fourier Transforms on `(0, ∞)` and `[-A, A]` & Exponential Type
(RCA pp. 371–372) -/

/-- **19.1:** Half-line holomorphic Fourier transform `f(z) = ∫_0^∞ F(t) exp(i t z) dt`. -/
def holomorphicFourierHalfLine (F : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), F t * Complex.exp (Complex.I * (t : ℂ) * z)

/-- **19.1:** Finite-interval holomorphic Fourier transform `f(z) = ∫_{-A}^A F(t) exp(i t z) dt`. -/
def holomorphicFourierInterval (A : ℝ) (F : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in Set.Icc (-A) A, F t * Complex.exp (Complex.I * (t : ℂ) * z)

/-- **19.1:** Entire function of exponential type at most `A`:
`f` is entire and `∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ C * exp (A * ‖z‖)`. -/
def IsExponentialTypeAtMost (A : ℝ) (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * ‖z‖)

/-- **19.1:** Entire function of exponential type (RCA p. 372):
`f` is entire and `∃ A > 0, ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ C * exp (A * ‖z‖)`. -/
def IsExponentialType (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∃ A > 0, ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * ‖z‖)

lemma memLp_exp_neg_mul_Ioi {c : ℝ} (hc : 0 < c) :
    MemLp (fun t : ℝ => Real.exp (-c * t)) 2 (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(2 * c) * t)) (Set.Ioi (0 : ℝ)) volume :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  refine (memLp_two_iff_integrable_sq
    (Continuous.aestronglyMeasurable (by fun_prop))).mpr ?_
  refine hint.congr_fun (fun t _ => ?_) measurableSet_Ioi
  rw [← Real.exp_nat_mul]
  exact congr_arg Real.exp (by ring)

lemma integrableOn_halfLine_of_memLp {F : ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (Set.Ioi (0 : ℝ)))) {z : ℂ} (hz : 0 < z.im) :
    IntegrableOn (fun t : ℝ => F t * Complex.exp (Complex.I * (t : ℂ) * z))
      (Set.Ioi (0 : ℝ)) volume := by
  have hexp : MemLp (fun t : ℝ => Real.exp (-z.im * t)) 2 (volume.restrict (Set.Ioi (0 : ℝ))) :=
    memLp_exp_neg_mul_Ioi hz
  have hprod : Integrable (fun t : ℝ => ‖F t‖ * Real.exp (-z.im * t))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hF.norm.integrable_mul hexp
  have hmeas : AEStronglyMeasurable (fun t : ℝ => F t * Complex.exp (Complex.I * (t : ℂ) * z))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hF.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))
  refine Integrable.mono' hprod hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
  rw [norm_mul, norm_exp_I_mul_real_mul_complex]
  exact le_of_eq (by ring_nf)

theorem differentiableOn_holomorphicFourierHalfLine {F : ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (Set.Ioi (0 : ℝ)))) :
    DifferentiableOn ℂ (holomorphicFourierHalfLine F) {z : ℂ | 0 < z.im} := by
  intro z₀ hz₀
  have hy₀ : 0 < z₀.im := hz₀
  apply DifferentiableAt.differentiableWithinAt
  let μ := volume.restrict (Set.Ioi (0 : ℝ))
  let s := Metric.ball z₀ (z₀.im / 2)
  have hs_nhds : s ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ (half_pos hy₀)
  let Φ : ℂ → ℝ → ℂ := fun z t => F t * Complex.exp (Complex.I * (t : ℂ) * z)
  let Φ' : ℝ → ℂ := fun t => F t * (Complex.I * (t : ℂ)) * Complex.exp (Complex.I * (t : ℂ) * z₀)
  let bound : ℝ → ℝ := fun t => ‖F t‖ * (4 / z₀.im) * Real.exp (-(z₀.im / 4) * t)
  have h_bound_int : Integrable bound μ := by
    have hexp : MemLp (fun t : ℝ => Real.exp (-(z₀.im / 4) * t)) 2 μ :=
      memLp_exp_neg_mul_Ioi (by positivity)
    have hmul := (hF.norm.const_mul (4 / z₀.im)).integrable_mul hexp
    exact hmul.congr (ae_of_all _ fun t => by dsimp [bound]; ring)
  have h_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (Φ z) μ :=
    Eventually.of_forall fun z =>
      hF.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))
  have h_int₀ : Integrable (Φ z₀) μ := integrableOn_halfLine_of_memLp hF hy₀
  have h_meas' : AEStronglyMeasurable Φ' μ :=
    (hF.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))).mul
      (Continuous.aestronglyMeasurable (by fun_prop))
  have h_diff_w : ∀ t : ℝ, ∀ w : ℂ,
      HasDerivAt (fun z => Φ z t) (F t * (Complex.I * (t : ℂ)) * Complex.exp (Complex.I * (t : ℂ) * w)) w := by
    intro t w
    have h1 : HasDerivAt (fun z : ℂ => Complex.I * (t : ℂ) * z) (Complex.I * (t : ℂ)) w := by
      simpa using (hasDerivAt_id w).const_mul (Complex.I * (t : ℂ))
    have h2 : HasDerivAt (fun z : ℂ => Complex.exp (Complex.I * (t : ℂ) * z))
        (Complex.exp (Complex.I * (t : ℂ) * w) * (Complex.I * (t : ℂ))) w := h1.cexp
    simpa [Φ, mul_assoc, mul_comm, mul_left_comm] using h2.const_mul (F t)
  have h_lip : ∀ᵐ t ∂μ, LipschitzOnWith (Real.nnabs (bound t)) (fun z => Φ z t) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := ht
    have h_b_nn : 0 ≤ bound t := by
      dsimp [bound]
      positivity
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun z _ => (h_diff_w t z).differentiableAt)
      (fun z hz => ?_) (convex_ball z₀ (z₀.im / 2))
    rw [(h_diff_w t z).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs, abs_of_nonneg h_b_nn]
    have hz_im : z₀.im / 2 ≤ z.im := by
      have hd : ‖z - z₀‖ < z₀.im / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
      have him : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
        simpa using Complex.abs_im_le_norm (z - z₀)
      linarith [(abs_le.mp him).1]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg ht_pos.le, norm_exp_I_mul_real_mul_complex]
    have h_te : t * Real.exp (-t * z.im) ≤ (4 / z₀.im) * Real.exp (-(z₀.im / 4) * t) := by
      have h1 : (z₀.im / 4) * t ≤ Real.exp ((z₀.im / 4) * t) :=
        (le_trans (by linarith) (Real.add_one_le_exp ((z₀.im / 4) * t)))
      have h2 : t ≤ (4 / z₀.im) * Real.exp ((z₀.im / 4) * t) := by
        have hpos : 0 < z₀.im / 4 := by positivity
        calc t = (4 / z₀.im) * ((z₀.im / 4) * t) := by field_simp [hy₀.ne']
          _ ≤ (4 / z₀.im) * Real.exp ((z₀.im / 4) * t) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
      calc t * Real.exp (-t * z.im)
          ≤ ((4 / z₀.im) * Real.exp ((z₀.im / 4) * t)) * Real.exp (-t * (z₀.im / 2)) := by
            refine mul_le_mul h2 (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by positivity)
            nlinarith
        _ = (4 / z₀.im) * Real.exp (-(z₀.im / 4) * t) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            ring
    calc ‖F t‖ * t * Real.exp (-t * z.im)
        = ‖F t‖ * (t * Real.exp (-t * z.im)) := by ring
      _ ≤ ‖F t‖ * ((4 / z₀.im) * Real.exp (-(z₀.im / 4) * t)) :=
          mul_le_mul_of_nonneg_left h_te (norm_nonneg _)
      _ = bound t := by dsimp [bound]; ring
  have h_diff₀ : ∀ᵐ t ∂μ, HasDerivAt (fun z => Φ z t) (Φ' t) z₀ :=
    Eventually.of_forall fun t => h_diff_w t z₀
  exact (hasDerivAt_integral_of_dominated_loc_of_lip hs_nhds h_meas h_int₀ h_meas'
    h_lip h_bound_int h_diff₀).2.differentiableAt

theorem holomorphicFourierHalfLine_plancherel {F : ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (Set.Ioi (0 : ℝ)))) {y : ℝ} (hy : 0 < y) :
    MemLp (fun x : ℝ => holomorphicFourierHalfLine F ((x : ℂ) + (y : ℂ) * Complex.I)) 2 volume ∧
      (1 / (2 * Real.pi)) *
          ∫ x : ℝ, ‖holomorphicFourierHalfLine F ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 =
        ∫ t in Set.Ioi (0 : ℝ), ‖F t‖ ^ 2 * Real.exp (-2 * t * y) ∧
      ∫ t in Set.Ioi (0 : ℝ), ‖F t‖ ^ 2 * Real.exp (-2 * t * y) ≤
        ∫ t in Set.Ioi (0 : ℝ), ‖F t‖ ^ 2 := by
  let g : ℝ → ℂ := Set.indicator (Set.Ioi (0 : ℝ)) (fun t => F t * (Real.exp (-t * y) : ℂ))
  have hg1 : Integrable g volume := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    have hexp : MemLp (fun t : ℝ => Real.exp (-y * t)) 2 (volume.restrict (Set.Ioi (0 : ℝ))) :=
      memLp_exp_neg_mul_Ioi hy
    have hprod := hF.norm.integrable_mul hexp
    have hmeas : AEStronglyMeasurable (fun t : ℝ => F t * (Real.exp (-t * y) : ℂ))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      hF.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))
    refine Integrable.mono' hprod hmeas ?_
    filter_upwards with t
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    dsimp [Pi.mul_apply]
    exact le_of_eq (congr_arg (‖F t‖ * ·) (congr_arg Real.exp (by ring)))
  have hg2 : MemLp g 2 volume := by
    rw [memLp_indicator_iff_restrict measurableSet_Ioi]
    refine MemLp.mono' hF.norm
      (hF.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := ht
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hexp_le : Real.exp (-t * y) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    exact mul_le_of_le_one_right (norm_nonneg _) hexp_le
  have h_eq : (fun x : ℝ => holomorphicFourierHalfLine F ((x : ℂ) + (y : ℂ) * Complex.I)) =
      ch19Fourier g := by
    ext x
    unfold holomorphicFourierHalfLine ch19Fourier
    have hind : (fun t : ℝ => g t * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) =
        Set.indicator (Set.Ioi (0 : ℝ))
          (fun t : ℝ => F t * (Real.exp (-t * y) : ℂ) * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) := by
      ext t; by_cases ht : t ∈ Set.Ioi (0 : ℝ) <;> simp [g, ht, mul_assoc]
    rw [hind, integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with t
    rw [mul_assoc (F t), Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    exact congr_arg Complex.exp (by push_cast; ring_nf; simp [Complex.I_sq]; ring)
  obtain ⟨hmem, hplan⟩ := ch19Fourier_plancherel_L1_L2 hg1 hg2
  rw [← h_eq] at hmem hplan
  have hg_sq : ∫ t : ℝ, ‖g t‖ ^ 2 = ∫ t in Set.Ioi (0 : ℝ), ‖F t‖ ^ 2 * Real.exp (-2 * t * y) := by
    have hind : (fun t : ℝ => ‖g t‖ ^ 2) =
        Set.indicator (Set.Ioi (0 : ℝ)) (fun t : ℝ => ‖F t‖ ^ 2 * Real.exp (-2 * t * y)) := by
      ext t
      by_cases ht : t ∈ Set.Ioi (0 : ℝ)
      · simp only [g, indicator_of_mem ht, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, ← Real.exp_nat_mul]
        congr 1
        exact congr_arg Real.exp (by ring)
      · simp [g, ht]
    rw [hind, integral_indicator measurableSet_Ioi]
  refine ⟨hmem, hplan.trans hg_sq, ?_⟩
  have hF_sq : Integrable (fun t : ℝ => ‖F t‖ ^ 2) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hF.norm.integrable_sq
  have hg_sq_int : Integrable (fun t : ℝ => ‖F t‖ ^ 2 * Real.exp (-2 * t * y))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine hF_sq.mono' (hF_sq.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := ht
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    exact mul_le_of_le_one_right (sq_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith))
  refine integral_mono_ae hg_sq_int hF_sq ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht_pos : 0 < t := ht
  exact mul_le_of_le_one_right (sq_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith))

/-- Null-endpoint equivalences between `Set.Ioo (-A) A`, `Set.Icc (-A) A`, and `-A..A`. -/
theorem holomorphicFourierInterval_endpoint_eq {A : ℝ} (hA : 0 ≤ A) (F : ℝ → ℂ) (z : ℂ) :
    (MemLp F 2 (volume.restrict (Set.Ioo (-A) A)) ↔
      MemLp F 2 (volume.restrict (Set.Icc (-A) A))) ∧
    holomorphicFourierInterval A F z =
      ∫ t in Set.Ioo (-A) A, F t * Complex.exp (Complex.I * (t : ℂ) * z) ∧
    holomorphicFourierInterval A F z =
      ∫ t in (-A)..A, F t * Complex.exp (Complex.I * (t : ℂ) * z) := by
  have h_ioo_icc : volume.restrict (Set.Ioo (-A) A) = volume.restrict (Set.Icc (-A) A) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  have h_ioc_icc : volume.restrict (Set.Ioc (-A) A) = volume.restrict (Set.Icc (-A) A) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc
  refine ⟨by rw [h_ioo_icc], ?_, ?_⟩
  · unfold holomorphicFourierInterval
    rw [h_ioo_icc]
  · unfold holomorphicFourierInterval
    rw [intervalIntegral.integral_of_le (by linarith), h_ioc_icc]

theorem holomorphicFourierInterval_properties {A : ℝ} (hA : 0 < A) {F : ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (Set.Ioo (-A) A))) :
    let f := holomorphicFourierInterval A F
    let C := ∫ t in Set.Icc (-A) A, ‖F t‖
    IntegrableOn F (Set.Icc (-A) A) volume ∧
    Differentiable ℂ f ∧
    MemLp (fun x : ℝ => f (x : ℂ)) 2 volume ∧
    (1 / (2 * Real.pi)) * ∫ x : ℝ, ‖f (x : ℂ)‖ ^ 2 =
      ∫ t in Set.Icc (-A) A, ‖F t‖ ^ 2 ∧
    (∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * |z.im|) ∧
      C * Real.exp (A * |z.im|) ≤ C * Real.exp (A * ‖z‖)) ∧
    IsExponentialTypeAtMost A f ∧
    IsExponentialType f := by
  have h_ioo_icc : volume.restrict (Set.Ioo (-A) A) = volume.restrict (Set.Icc (-A) A) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  have hF_icc : MemLp F 2 (volume.restrict (Set.Icc (-A) A)) := by rwa [← h_ioo_icc]
  let μ := volume.restrict (Set.Icc (-A) A)
  have : IsFiniteMeasure μ := ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hF_int : Integrable F μ := hF_icc.integrable one_le_two
  let f := holomorphicFourierInterval A F
  let C := ∫ t in Set.Icc (-A) A, ‖F t‖
  have hC_nn : 0 ≤ C := integral_nonneg fun t => norm_nonneg _
  have hf_diff : Differentiable ℂ f := by
    intro z₀
    let s := Metric.ball z₀ 1
    have hs_nhds : s ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ one_pos
    let R := ‖z₀‖ + 1
    let Φ : ℂ → ℝ → ℂ := fun z t => F t * Complex.exp (Complex.I * (t : ℂ) * z)
    let Φ' : ℝ → ℂ := fun t => F t * (Complex.I * (t : ℂ)) * Complex.exp (Complex.I * (t : ℂ) * z₀)
    let bound : ℝ → ℝ := fun t => ‖F t‖ * (A * Real.exp (A * R))
    have h_bound_int : Integrable bound μ := hF_int.norm.mul_const _
    have h_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (Φ z) μ :=
      Eventually.of_forall fun z =>
        hF_icc.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))
    have h_int₀ : Integrable (Φ z₀) μ := by
      refine (hF_int.norm.mul_const (Real.exp (A * ‖z₀‖))).mono'
        (hF_icc.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [norm_mul, norm_exp_I_mul_real_mul_complex]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      have ht_abs : |t| ≤ A := abs_le.mpr ht
      have hneg : -t * z₀.im ≤ |t| * |z₀.im| := by
        have := neg_le_abs (t * z₀.im); rw [abs_mul] at this; linarith
      exact hneg.trans (mul_le_mul ht_abs (Complex.abs_im_le_norm z₀) (abs_nonneg _) hA.le)
    have h_meas' : AEStronglyMeasurable Φ' μ :=
      (hF_icc.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))).mul
        (Continuous.aestronglyMeasurable (by fun_prop))
    have h_diff_w : ∀ t : ℝ, ∀ w : ℂ,
        HasDerivAt (fun z => Φ z t) (F t * (Complex.I * (t : ℂ)) * Complex.exp (Complex.I * (t : ℂ) * w)) w := by
      intro t w
      have h1 : HasDerivAt (fun z : ℂ => Complex.I * (t : ℂ) * z) (Complex.I * (t : ℂ)) w := by
        simpa using (hasDerivAt_id w).const_mul (Complex.I * (t : ℂ))
      simpa [Φ, mul_assoc, mul_comm, mul_left_comm] using h1.cexp.const_mul (F t)
    have h_lip : ∀ᵐ t ∂μ, LipschitzOnWith (Real.nnabs (bound t)) (fun z => Φ z t) s := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have h_b_nn : 0 ≤ bound t := by dsimp [bound]; positivity
      apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
        (fun z _ => (h_diff_w t z).differentiableAt)
        (fun z hz => ?_) (convex_ball z₀ 1)
      rw [(h_diff_w t z).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs, abs_of_nonneg h_b_nn]
      have hz_norm : ‖z‖ ≤ R := by
        have hd : ‖z - z₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
        have := norm_sub_norm_le z z₀
        dsimp [R]; linarith
      have ht_abs : |t| ≤ A := abs_le.mpr ht
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        norm_exp_I_mul_real_mul_complex, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine mul_le_mul ht_abs (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hA.le
      have hneg : -t * z.im ≤ |t| * |z.im| := by
        have := neg_le_abs (t * z.im); rw [abs_mul] at this; linarith
      exact hneg.trans (mul_le_mul ht_abs ((Complex.abs_im_le_norm z).trans hz_norm) (abs_nonneg _) hA.le)
    exact (hasDerivAt_integral_of_dominated_loc_of_lip hs_nhds h_meas h_int₀ h_meas'
      h_lip h_bound_int (Eventually.of_forall fun t => h_diff_w t z₀)).2.differentiableAt
  let g : ℝ → ℂ := Set.indicator (Set.Icc (-A) A) F
  have hg1 : Integrable g volume := (integrable_indicator_iff measurableSet_Icc).mpr hF_int
  have hg2 : MemLp g 2 volume := (memLp_indicator_iff_restrict measurableSet_Icc).mpr hF_icc
  have hf_real : (fun x : ℝ => f (x : ℂ)) = ch19Fourier g := by
    ext x
    unfold f holomorphicFourierInterval ch19Fourier
    have hind : (fun t : ℝ => g t * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) =
        Set.indicator (Set.Icc (-A) A) (fun t : ℝ => F t * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) := by
      ext t; by_cases ht : t ∈ Set.Icc (-A) A <;> simp [g, ht]
    rw [hind, integral_indicator measurableSet_Icc]
  obtain ⟨hmem, hplan⟩ := ch19Fourier_plancherel_L1_L2 hg1 hg2
  rw [← hf_real] at hmem hplan
  have hg_sq : ∫ t : ℝ, ‖g t‖ ^ 2 = ∫ t in Set.Icc (-A) A, ‖F t‖ ^ 2 := by
    have hind : (fun t : ℝ => ‖g t‖ ^ 2) = Set.indicator (Set.Icc (-A) A) (fun t : ℝ => ‖F t‖ ^ 2) := by
      ext t; by_cases ht : t ∈ Set.Icc (-A) A <;> simp [g, ht]
    rw [hind, integral_indicator measurableSet_Icc]
  have hbound : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * |z.im|) ∧
      C * Real.exp (A * |z.im|) ≤ C * Real.exp (A * ‖z‖) := by
    intro z
    constructor
    · calc ‖f z‖
          ≤ ∫ t in Set.Icc (-A) A, ‖F t * Complex.exp (Complex.I * (t : ℂ) * z)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ t in Set.Icc (-A) A, ‖F t‖ * Real.exp (A * |z.im|) := by
            refine integral_mono_ae ?_ (hF_int.norm.mul_const _) ?_
            · refine (hF_int.norm.mul_const (Real.exp (A * |z.im|))).mono'
                ((hF_icc.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))).norm) ?_
              filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
              rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul, norm_exp_I_mul_real_mul_complex]
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
              have ht_abs : |t| ≤ A := abs_le.mpr ht
              have hneg : -t * z.im ≤ |t| * |z.im| := by
                have := neg_le_abs (t * z.im); rw [abs_mul] at this; linarith
              exact hneg.trans (mul_le_mul_of_nonneg_right ht_abs (abs_nonneg _))
            · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
              rw [norm_mul, norm_exp_I_mul_real_mul_complex]
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
              have ht_abs : |t| ≤ A := abs_le.mpr ht
              have hneg : -t * z.im ≤ |t| * |z.im| := by
                have := neg_le_abs (t * z.im); rw [abs_mul] at this; linarith
              exact hneg.trans (mul_le_mul_of_nonneg_right ht_abs (abs_nonneg _))
        _ = C * Real.exp (A * |z.im|) := integral_mul_const _ _
    · exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) hA.le)) hC_nn
  have hexpA : IsExponentialTypeAtMost A f := by
    refine ⟨hf_diff, C + 1, by linarith, fun z => ?_⟩
    calc ‖f z‖ ≤ C * Real.exp (A * ‖z‖) := (hbound z).1.trans (hbound z).2
      _ ≤ (C + 1) * Real.exp (A * ‖z‖) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  refine ⟨hF_int, hf_diff, hmem, hplan.trans hg_sq, hbound, hexpA, ?_⟩
  exact ⟨hf_diff, A, hA, hexpA.2⟩

/-- **Node 19.1 (RCA pp. 371–372, packaged forward theorems & exponential-type bounds):**
1. For `F ∈ L²(0, ∞)`, `f(z) = ∫_0^∞ F(t) exp(i t z) dt` exists and is holomorphic on `{Im z > 0}`,
   and for every `y > 0`, `(1/(2π)) ∫_ℝ |f(x+iy)|² dx = ∫_0^∞ |F(t)|² exp(-2ty) dt ≤ ∫_0^∞ |F(t)|² dt`.
2. For `A > 0` and `F ∈ L²(-A, A)`, `f(z) = ∫_{-A}^A F(t) exp(i t z) dt` is entire, `L²` on `ℝ` with
   `(1/(2π)) ∫_ℝ |f(x)|² dx = ∫_{-A}^A |F(t)|² dt`, and satisfies
   `|f(z)| ≤ C exp(A |Im z|) ≤ C exp(A |z|)` with `C = ∫_{-A}^A |F|` (hence `IsExponentialType f`). -/
theorem theorem19_1 :
    (∀ F : ℝ → ℂ, MemLp F 2 (volume.restrict (Set.Ioi (0 : ℝ))) →
      (∀ z : ℂ, 0 < z.im →
        IntegrableOn (fun t : ℝ => F t * Complex.exp (Complex.I * (t : ℂ) * z))
          (Set.Ioi (0 : ℝ)) volume) ∧
      DifferentiableOn ℂ (holomorphicFourierHalfLine F) {z : ℂ | 0 < z.im} ∧
      (∀ y : ℝ, 0 < y →
        MemLp (fun x : ℝ => holomorphicFourierHalfLine F ((x : ℂ) + (y : ℂ) * Complex.I)) 2 volume ∧
        (1 / (2 * Real.pi)) *
            ∫ x : ℝ, ‖holomorphicFourierHalfLine F ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 =
          ∫ t in Set.Ioi (0 : ℝ), ‖F t‖ ^ 2 * Real.exp (-2 * t * y) ∧
        ∫ t in Set.Ioi (0 : ℝ), ‖F t‖ ^ 2 * Real.exp (-2 * t * y) ≤
          ∫ t in Set.Ioi (0 : ℝ), ‖F t‖ ^ 2)) ∧
    (∀ (A : ℝ), 0 < A → ∀ F : ℝ → ℂ, MemLp F 2 (volume.restrict (Set.Ioo (-A) A)) →
      let f := holomorphicFourierInterval A F
      let C := ∫ t in Set.Icc (-A) A, ‖F t‖
      Differentiable ℂ f ∧
      MemLp (fun x : ℝ => f (x : ℂ)) 2 volume ∧
      (1 / (2 * Real.pi)) * ∫ x : ℝ, ‖f (x : ℂ)‖ ^ 2 =
        ∫ t in Set.Icc (-A) A, ‖F t‖ ^ 2 ∧
      (∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * |z.im|) ∧
        C * Real.exp (A * |z.im|) ≤ C * Real.exp (A * ‖z‖)) ∧
      IsExponentialTypeAtMost A f ∧
      IsExponentialType f) := by
  refine ⟨fun F hF => ⟨fun z hz => integrableOn_halfLine_of_memLp hF hz,
    differentiableOn_holomorphicFourierHalfLine hF,
    fun y hy => holomorphicFourierHalfLine_plancherel hF hy⟩, ?_⟩
  intro A hA F hF
  obtain ⟨_, h1, h2, h3, h4, h5, h6⟩ := holomorphicFourierInterval_properties hA hF
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-! ## §19.2: First Paley–Wiener Theorem on the Upper Half-Plane (RCA pp. 372–374) -/

section Node19_2

private def pwDamp (ε : ℝ) (z : ℂ) : ℂ :=
  (1 - Complex.I * (ε : ℂ) * z)⁻¹

private def pwDamped (f : ℂ → ℂ) (ε : ℝ) (z : ℂ) : ℂ :=
  f z * pwDamp ε z

private lemma norm_sq_one_sub_I_mul_eps_mul {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : 0 < z.im) :
    (1 + ε * z.im) ^ 2 + (ε * z.re) ^ 2 = ‖1 - Complex.I * (ε : ℂ) * z‖ ^ 2 ∧
      1 + (ε * z.re) ^ 2 ≤ ‖1 - Complex.I * (ε : ℂ) * z‖ ^ 2 ∧
      1 ≤ ‖1 - Complex.I * (ε : ℂ) * z‖ ∧
      1 - Complex.I * (ε : ℂ) * z ≠ 0 := by
  have hsq : ‖1 - Complex.I * (ε : ℂ) * z‖ ^ 2 = (1 + ε * z.im) ^ 2 + (ε * z.re) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
      Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.mul_im]
    ring
  have hge1 : 1 + (ε * z.re) ^ 2 ≤ ‖1 - Complex.I * (ε : ℂ) * z‖ ^ 2 := by
    rw [hsq]
    nlinarith [mul_pos hε hz]
  have hnorm1 : 1 ≤ ‖1 - Complex.I * (ε : ℂ) * z‖ := by
    nlinarith [norm_nonneg (1 - Complex.I * (ε : ℂ) * z), sq_nonneg (ε * z.re)]
  refine ⟨hsq.symm, hge1, hnorm1, ?_⟩
  intro h0
  rw [h0, norm_zero] at hnorm1
  linarith

private lemma norm_pwDamp_le_one {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : 0 < z.im) :
    ‖pwDamp ε z‖ ≤ 1 := by
  unfold pwDamp
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ (norm_sq_one_sub_I_mul_eps_mul hε hz).2.2.1

private lemma norm_pwDamp_sq_le {ε : ℝ} (hε : 0 < ε) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖pwDamp ε ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ≤ (1 + (ε * x) ^ 2)⁻¹ := by
  have hz : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simp [hy]
  have hre : ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by simp
  have hle := (norm_sq_one_sub_I_mul_eps_mul hε hz).2.1
  rw [hre] at hle
  unfold pwDamp
  rw [norm_inv, inv_pow]
  exact inv_anti₀ (by positivity) hle

private lemma differentiableOn_pwDamped {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) {ε : ℝ} (hε : 0 < ε) :
    DifferentiableOn ℂ (pwDamped f ε) {z : ℂ | 0 < z.im} := by
  refine hf.mul ?_
  intro z hz
  have hne := (norm_sq_one_sub_I_mul_eps_mul hε hz).2.2.2
  have hd : DifferentiableAt ℂ (fun w : ℂ => 1 - Complex.I * (ε : ℂ) * w) z := by fun_prop
  exact (hd.inv hne).differentiableWithinAt

private lemma exists_large_pos_small_lintegral {Ψ : ℝ → ℝ≥0∞}
    (hΨ_meas : Measurable Ψ) (hΨ_fin : ∫⁻ x : ℝ, Ψ x < ⊤) (k : ℕ) :
    ∃ X : ℝ, (k : ℝ) ≤ X ∧ Ψ X ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
  by_contra! h
  let δ := ENNReal.ofReal (1 / ((k : ℝ) + 1))
  have hδ_pos : 0 < δ := ENNReal.ofReal_pos.mpr (by positivity)
  have htop : ⊤ ≤ ∫⁻ x : ℝ, Ψ x := by
    calc (⊤ : ℝ≥0∞)
        = δ * volume (Set.Ici (k : ℝ)) := by
          rw [Real.volume_Ici, ENNReal.mul_top hδ_pos.ne']
      _ = ∫⁻ _ in Set.Ici (k : ℝ), δ := (setLIntegral_const (Set.Ici (k : ℝ)) δ).symm
      _ ≤ ∫⁻ x in Set.Ici (k : ℝ), Ψ x := by
          refine setLIntegral_mono hΨ_meas fun x hx => (h x hx).le
      _ ≤ ∫⁻ x : ℝ, Ψ x := lintegral_mono' Measure.restrict_le_self le_rfl
  exact absurd hΨ_fin (not_lt.mpr htop)

private lemma exists_large_neg_small_lintegral {Ψ : ℝ → ℝ≥0∞}
    (hΨ_meas : Measurable Ψ) (hΨ_fin : ∫⁻ x : ℝ, Ψ x < ⊤) (k : ℕ) :
    ∃ X' : ℝ, X' ≤ -(k : ℝ) ∧ Ψ X' ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
  by_contra! h
  let δ := ENNReal.ofReal (1 / ((k : ℝ) + 1))
  have hδ_pos : 0 < δ := ENNReal.ofReal_pos.mpr (by positivity)
  have htop : ⊤ ≤ ∫⁻ x : ℝ, Ψ x := by
    calc (⊤ : ℝ≥0∞)
        = δ * volume (Set.Iic (-(k : ℝ))) := by
          rw [Real.volume_Iic, ENNReal.mul_top hδ_pos.ne']
      _ = ∫⁻ _ in Set.Iic (-(k : ℝ)), δ := (setLIntegral_const (Set.Iic (-(k : ℝ))) δ).symm
      _ ≤ ∫⁻ x in Set.Iic (-(k : ℝ)), Ψ x := by
          refine setLIntegral_mono hΨ_meas fun x hx => (h x hx).le
      _ ≤ ∫⁻ x : ℝ, Ψ x := lintegral_mono' Measure.restrict_le_self le_rfl
  exact absurd hΨ_fin (not_lt.mpr htop)

private lemma pwDamped_slice_props {f : ℂ → ℂ} {C : ℝ}
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hL2 : ∀ y : ℝ, 0 < y → MemLp (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I)) 2 volume)
    (hC_ub : ∀ y : ℝ, 0 < y →
      (1 / (2 * Real.pi)) * ∫ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    let w_ε : ℝ → ℝ := fun x => (1 + (ε * x) ^ 2)⁻¹
    Integrable w_ε volume ∧
    ∀ y : ℝ, 0 < y →
      Continuous (fun x : ℝ => pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)) ∧
      MemLp (fun x : ℝ => pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)) 2 volume ∧
      Integrable (fun x : ℝ => pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)) volume ∧
      ∫ x : ℝ, ‖pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        (1 / 2) * (2 * Real.pi * C + ∫ x : ℝ, w_ε x) := by
  let w_ε : ℝ → ℝ := fun x => (1 + (ε * x) ^ 2)⁻¹
  have hw_int : Integrable w_ε volume := integrable_inv_one_add_sq.comp_mul_left' hε.ne'
  refine ⟨hw_int, fun y hy => ?_⟩
  have hd_contOn : ContinuousOn (pwDamped f ε) {z : ℂ | 0 < z.im} :=
    (differentiableOn_pwDamped hf hε).continuousOn
  have hslice_cont : Continuous (fun x : ℝ => pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)) := by
    refine hd_contOn.comp_continuous (by fun_prop) fun x => ?_
    simp [hy]
  have hmem2 : MemLp (fun x : ℝ => pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)) 2 volume := by
    refine (hL2 y hy).norm.mono' hslice_cont.aestronglyMeasurable ?_
    filter_upwards with x
    unfold pwDamped
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (norm_pwDamp_le_one hε (by simp [hy]))
  have h_pt_bound : ∀ x : ℝ,
      ‖pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        (1 / 2) * (‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 + w_ε x) := by
    intro x
    unfold pwDamped
    rw [norm_mul]
    have hab := two_mul_le_add_sq ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖
      ‖pwDamp ε ((x : ℂ) + (y : ℂ) * Complex.I)‖
    have hd := norm_pwDamp_sq_le hε x hy
    dsimp [w_ε]
    linarith
  have h_major_int : Integrable
      (fun x : ℝ => (1 / 2) * (‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 + w_ε x)) volume :=
    (((hL2 y hy).norm.integrable_sq).add hw_int).const_mul (1 / 2)
  have hint1 : Integrable (fun x : ℝ => pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)) volume := by
    refine h_major_int.mono' hslice_cont.aestronglyMeasurable ?_
    filter_upwards with x
    exact h_pt_bound x
  refine ⟨hslice_cont, hmem2, hint1, ?_⟩
  have hle1 : ∫ x : ℝ, ‖pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      ∫ x : ℝ, (1 / 2) * (‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 + w_ε x) :=
    integral_mono hint1.norm h_major_int h_pt_bound
  have hf_int_le : ∫ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ≤ 2 * Real.pi * C := by
    have h := hC_ub y hy
    have h2pi_pos : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
    have := mul_le_mul_of_nonneg_left h h2pi_pos.le
    rwa [← mul_assoc, one_div, mul_inv_cancel₀ h2pi_pos.ne', one_mul] at this
  calc ∫ x : ℝ, ‖pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ ∫ x : ℝ, (1 / 2) * (‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 + w_ε x) := hle1
    _ = (1 / 2) * ((∫ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) + ∫ x : ℝ, w_ε x) := by
        rw [integral_const_mul, integral_add ((hL2 y hy).norm.integrable_sq) hw_int]
    _ ≤ (1 / 2) * (2 * Real.pi * C + ∫ x : ℝ, w_ε x) := by linarith

private lemma pwDamped_height_independence {f : ℂ → ℂ} {C : ℝ}
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hL2 : ∀ y : ℝ, 0 < y → MemLp (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I)) 2 volume)
    (hC_ub : ∀ y : ℝ, 0 < y →
      (1 / (2 * Real.pi)) * ∫ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ≤ C)
    {ε : ℝ} (hε : 0 < ε) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (t : ℝ) :
    (Real.exp (t * y₁) : ℂ) *
        ch19InvFourier (fun x => pwDamped f ε ((x : ℂ) + (y₁ : ℂ) * Complex.I)) t =
      (Real.exp (t * y₂) : ℂ) *
        ch19InvFourier (fun x => pwDamped f ε ((x : ℂ) + (y₂ : ℂ) * Complex.I)) t := by
  suffices hlt : ∀ {a b : ℝ}, 0 < a → a < b →
      (Real.exp (t * a) : ℂ) *
          ch19InvFourier (fun x => pwDamped f ε ((x : ℂ) + (a : ℂ) * Complex.I)) t =
        (Real.exp (t * b) : ℂ) *
          ch19InvFourier (fun x => pwDamped f ε ((x : ℂ) + (b : ℂ) * Complex.I)) t by
    rcases lt_trichotomy y₁ y₂ with h | rfl | h
    · exact hlt hy₁ h
    · rfl
    · exact (hlt hy₂ h).symm
  intro a b ha hab
  have hb : 0 < b := ha.trans hab
  obtain ⟨hw_int, hprops⟩ := pwDamped_slice_props hf hL2 hC_ub hε
  let K : ℝ := (1 / 2) * (2 * Real.pi * C + ∫ x : ℝ, (1 + (ε * x) ^ 2)⁻¹)
  have hK_nn : 0 ≤ K := by
    have := (hprops 1 one_pos).2.2.2
    have h0 : 0 ≤ ∫ x : ℝ, ‖pwDamped f ε ((x : ℂ) + (1 : ℂ) * Complex.I)‖ :=
      integral_nonneg fun _ => norm_nonneg _
    exact h0.trans this
  let clamp : ℝ → ℝ := fun y => max a (min b y)
  have hclamp_cont : Continuous clamp := continuous_const.max (continuous_const.min continuous_id)
  have hclamp_pos : ∀ y : ℝ, 0 < clamp y := fun y => ha.trans_le (le_max_left a _)
  let φ : ℝ → ℝ → ℝ≥0∞ := fun x y =>
    ‖pwDamped f ε ((x : ℂ) + (clamp y : ℂ) * Complex.I)‖ₑ
  have hφ_cont : Continuous (Function.uncurry φ) := by
    have hd_cont : ContinuousOn (pwDamped f ε) {z : ℂ | 0 < z.im} :=
      (differentiableOn_pwDamped hf hε).continuousOn
    have hcomp : Continuous (fun p : ℝ × ℝ => pwDamped f ε ((p.1 : ℂ) + (clamp p.2 : ℂ) * Complex.I)) := by
      refine hd_cont.comp_continuous ?_ fun p => ?_
      · exact (Complex.continuous_ofReal.comp continuous_fst).add
          ((Complex.continuous_ofReal.comp (hclamp_cont.comp continuous_snd)).mul continuous_const)
      · simp [hclamp_pos p.2]
    exact hcomp.enorm
  let Ψ : ℝ → ℝ≥0∞ := fun x => ∫⁻ y in Set.Icc a b, φ x y
  have hΨ_meas : Measurable Ψ := hφ_cont.measurable.lintegral_prod_right'
  have hΨ_fin : ∫⁻ x : ℝ, Ψ x < ⊤ := by
    have hswap := MeasureTheory.lintegral_lintegral_swap
      (μ := volume) (ν := volume.restrict (Set.Icc a b)) hφ_cont.measurable.aemeasurable
    rw [hswap]
    have h_inner : ∀ y ∈ Set.Icc a b, (∫⁻ x : ℝ, φ x y) ≤ ENNReal.ofReal K := by
      intro y hy
      have hcy : clamp y = y := by
        simp [clamp, min_eq_right hy.2, max_eq_right hy.1]
      have hy_pos : 0 < y := ha.trans_le hy.1
      obtain ⟨hcont_y, _, hint_y, hbd_y⟩ := hprops y hy_pos
      have heq : (∫⁻ x : ℝ, φ x y) = ENNReal.ofReal
          (∫ x : ℝ, ‖pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)‖) := by
        rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => norm_nonneg _)
          hcont_y.norm.aestronglyMeasurable, ENNReal.ofReal_toReal]
        · apply lintegral_congr
          intro x
          simp [φ, hcy, ofReal_norm]
        · exact hint_y.norm.lintegral_lt_top.ne
      rw [heq]
      exact ENNReal.ofReal_le_ofReal hbd_y
    calc ∫⁻ y in Set.Icc a b, ∫⁻ x : ℝ, φ x y
        ≤ ∫⁻ _ in Set.Icc a b, ENNReal.ofReal K :=
          setLIntegral_mono measurable_const h_inner
      _ = ENNReal.ofReal K * volume (Set.Icc a b) := setLIntegral_const _ _
      _ < ⊤ := by
          rw [Real.volume_Icc]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  choose X hX_ge hX_bd using exists_large_pos_small_lintegral hΨ_meas hΨ_fin
  choose X' hX'_le hX'_bd using exists_large_neg_small_lintegral hΨ_meas hΨ_fin
  have hX_top : Tendsto X atTop atTop :=
    tendsto_atTop_mono hX_ge tendsto_natCast_atTop_atTop
  have hX'_bot : Tendsto X' atTop atBot :=
    tendsto_atBot_mono hX'_le (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  let g : ℂ → ℂ := fun z => pwDamped f ε z * Complex.exp (-Complex.I * (t : ℂ) * z)
  have hg_diff : DifferentiableOn ℂ g {z : ℂ | 0 < z.im} :=
    (differentiableOn_pwDamped hf hε).mul
      ((Differentiable.differentiableOn (by fun_prop)))
  have h_vert_bound : ∀ (x₀ : ℝ) (k : ℕ), Ψ x₀ ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) →
      ‖∫ y in a..b, g ((x₀ : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        Real.exp (|t| * b) * (1 / ((k : ℝ) + 1)) := by
    intro x₀ k hk
    have hcont_v : ContinuousOn (fun y : ℝ => ‖pwDamped f ε ((x₀ : ℂ) + (y : ℂ) * Complex.I)‖)
        (Set.Icc a b) := by
      refine ContinuousOn.norm ?_
      refine (differentiableOn_pwDamped hf hε).continuousOn.comp
        (Continuous.continuousOn (by fun_prop)) fun y hy => ?_
      change 0 < ((x₀ : ℂ) + (y : ℂ) * Complex.I).im
      simp [ha.trans_le hy.1]
    have hint_v : IntervalIntegrable
        (fun y : ℝ => ‖pwDamped f ε ((x₀ : ℂ) + (y : ℂ) * Complex.I)‖) volume a b :=
      (hcont_v.mono (by rw [Set.uIcc_of_le hab.le])).intervalIntegrable
    have h_int_le : ∫ y in a..b, ‖pwDamped f ε ((x₀ : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        1 / ((k : ℝ) + 1) := by
      rw [intervalIntegral.integral_of_le hab.le,
        Measure.restrict_congr_set Ioc_ae_eq_Icc,
        integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => norm_nonneg _)
          (hcont_v.integrableOn_Icc.aestronglyMeasurable)]
      have hl : (∫⁻ y in Set.Icc a b,
          ENNReal.ofReal ‖pwDamped f ε ((x₀ : ℂ) + (y : ℂ) * Complex.I)‖) = Ψ x₀ := by
        refine setLIntegral_congr_fun measurableSet_Icc fun y hy => ?_
        have hcy : clamp y = y := by simp [clamp, min_eq_right hy.2, max_eq_right hy.1]
        simp [φ, hcy, ofReal_norm]
      rw [hl]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hk
    calc ‖∫ y in a..b, g ((x₀ : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ ∫ y in a..b, ‖g ((x₀ : ℂ) + (y : ℂ) * Complex.I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hab.le
      _ ≤ ∫ y in a..b, Real.exp (|t| * b) * ‖pwDamped f ε ((x₀ : ℂ) + (y : ℂ) * Complex.I)‖ := by
          refine intervalIntegral.integral_mono_on hab.le ?_ (hint_v.const_mul _) fun y hy => ?_
          · refine (ContinuousOn.norm ?_).mono (by rw [Set.uIcc_of_le hab.le]) |>.intervalIntegrable
            refine hg_diff.continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun y hy => ?_
            change 0 < ((x₀ : ℂ) + (y : ℂ) * Complex.I).im
            simp [ha.trans_le hy.1]
          · dsimp [g]
            rw [norm_mul, Complex.norm_exp]
            have hre_exp : (-Complex.I * (t : ℂ) * ((x₀ : ℂ) + (y : ℂ) * Complex.I)).re = t * y := by
              simp [Complex.mul_re, Complex.mul_im]
            rw [hre_exp, mul_comm]
            refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
            have hy_pos : 0 ≤ y := (ha.trans_le hy.1).le
            calc t * y ≤ |t| * y := mul_le_mul_of_nonneg_right (le_abs_self t) hy_pos
              _ ≤ |t| * b := mul_le_mul_of_nonneg_left hy.2 (abs_nonneg t)
      _ = Real.exp (|t| * b) * ∫ y in a..b, ‖pwDamped f ε ((x₀ : ℂ) + (y : ℂ) * Complex.I)‖ :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ Real.exp (|t| * b) * (1 / ((k : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h_int_le (Real.exp_pos _).le
  have h_rect : ∀ k : ℕ,
      ((∫ x in X' k..X k, g ((x : ℂ) + (a : ℂ) * Complex.I)) -
        ∫ x in X' k..X k, g ((x : ℂ) + (b : ℂ) * Complex.I)) +
      Complex.I • (∫ y in a..b, g ((X k : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I • (∫ y in a..b, g ((X' k : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
    intro k
    let z₁ : ℂ := (X' k : ℂ) + (a : ℂ) * Complex.I
    let z₂ : ℂ := (X k : ℂ) + (b : ℂ) * Complex.I
    have hz₁_re : z₁.re = X' k := by simp [z₁]
    have hz₁_im : z₁.im = a := by simp [z₁]
    have hz₂_re : z₂.re = X k := by simp [z₂]
    have hz₂_im : z₂.im = b := by simp [z₂]
    have hrect_sub : Set.uIcc z₁.re z₂.re ×ℂ Set.uIcc z₁.im z₂.im ⊆ {z : ℂ | 0 < z.im} := by
      intro z hz
      rw [hz₁_im, hz₂_im, Set.uIcc_of_le hab.le] at hz
      exact ha.trans_le hz.2.1
    have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g z₁ z₂
      (hg_diff.mono hrect_sub)
    simpa [hz₁_re, hz₁_im, hz₂_re, hz₂_im] using hcauchy
  have hg_int_y : ∀ {y : ℝ}, 0 < y → Integrable (fun x : ℝ => g ((x : ℂ) + (y : ℂ) * Complex.I)) volume := by
    intro y hy
    obtain ⟨hcont_y, _, hint_y, _⟩ := hprops y hy
    have h_eq : (fun x : ℝ => g ((x : ℂ) + (y : ℂ) * Complex.I)) =
        fun x : ℝ => (Real.exp (t * y) : ℂ) *
          (pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I) *
            Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) := by
      ext x
      dsimp [g]
      rw [Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
      congr 1
      exact congr_arg Complex.exp (by push_cast; ring_nf; simp [Complex.I_sq])
    rw [h_eq]
    refine Integrable.const_mul ?_ _
    refine hint_y.norm.mono'
      (hcont_y.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
    filter_upwards with x
    rw [norm_mul, norm_exp_neg_I_mul_real_mul_real, mul_one]
  have hlim_a : Tendsto (fun k => ∫ x in X' k..X k, g ((x : ℂ) + (a : ℂ) * Complex.I))
      atTop (𝓝 (∫ x : ℝ, g ((x : ℂ) + (a : ℂ) * Complex.I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral (hg_int_y ha) hX'_bot hX_top
  have hlim_b : Tendsto (fun k => ∫ x in X' k..X k, g ((x : ℂ) + (b : ℂ) * Complex.I))
      atTop (𝓝 (∫ x : ℝ, g ((x : ℂ) + (b : ℂ) * Complex.I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral (hg_int_y hb) hX'_bot hX_top
  have hlim_bound : Tendsto (fun k : ℕ => Real.exp (|t| * b) * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ => Real.exp (|t| * b) * (1 / ((k : ℝ) + 1)))
        atTop (𝓝 (Real.exp (|t| * b) * 0)) :=
      tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [mul_zero] at h
  have hlim_vr : Tendsto (fun k => Complex.I • ∫ y in a..b, g ((X k : ℂ) + (y : ℂ) * Complex.I))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hlim_bound
    rw [norm_smul, Complex.norm_I, one_mul]
    exact h_vert_bound (X k) k (hX_bd k)
  have hlim_vl : Tendsto (fun k => Complex.I • ∫ y in a..b, g ((X' k : ℂ) + (y : ℂ) * Complex.I))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hlim_bound
    rw [norm_smul, Complex.norm_I, one_mul]
    exact h_vert_bound (X' k) k (hX'_bd k)
  have hlim_tot := ((hlim_a.sub hlim_b).add hlim_vr).sub hlim_vl
  have hzero : Tendsto (fun k : ℕ =>
      (((∫ x in X' k..X k, g ((x : ℂ) + (a : ℂ) * Complex.I)) -
        ∫ x in X' k..X k, g ((x : ℂ) + (b : ℂ) * Complex.I)) +
      Complex.I • (∫ y in a..b, g ((X k : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I • (∫ y in a..b, g ((X' k : ℂ) + (y : ℂ) * Complex.I)))) atTop (𝓝 0) := by
    simp_rw [h_rect]
    exact tendsto_const_nhds
  have heq_ab : (∫ x : ℝ, g ((x : ℂ) + (a : ℂ) * Complex.I)) =
      ∫ x : ℝ, g ((x : ℂ) + (b : ℂ) * Complex.I) := by
    have := tendsto_nhds_unique hlim_tot hzero
    simpa [sub_eq_zero] using this
  have hfactor : ∀ y : ℝ,
      (Real.exp (t * y) : ℂ) *
        ch19InvFourier (fun x => pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)) t =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ x : ℝ, g ((x : ℂ) + (y : ℂ) * Complex.I) := by
    intro y
    unfold ch19InvFourier
    rw [mul_left_comm, ← integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    dsimp [g]
    rw [Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
    congr 1
    exact congr_arg Complex.exp (by push_cast; ring_nf; simp [Complex.I_sq])
  rw [hfactor a, hfactor b, heq_ab]

private lemma pwDamped_representation {f : ℂ → ℂ} {C : ℝ}
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hL2 : ∀ y : ℝ, 0 < y → MemLp (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I)) 2 volume)
    (hC_ub : ∀ y : ℝ, 0 < y →
      (1 / (2 * Real.pi)) * ∫ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ≤ C)
    (hC_nn : 0 ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ F_ε : ℝ → ℂ,
      Continuous F_ε ∧
      (∀ t : ℝ, t < 0 → F_ε t = 0) ∧
      MemLp F_ε 2 (volume.restrict (Set.Ioi (0 : ℝ))) ∧
      ∫ t in Set.Ioi (0 : ℝ), ‖F_ε t‖ ^ 2 ≤ C ∧
      (∀ (y : ℝ), 0 < y → ∀ t : ℝ,
        ch19InvFourier (fun x => pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)) t =
          F_ε t * (Real.exp (-t * y) : ℂ)) ∧
      (∀ z : ℂ, 0 < z.im → pwDamped f ε z = holomorphicFourierHalfLine F_ε z) := by
  obtain ⟨hw_int, hprops⟩ := pwDamped_slice_props hf hL2 hC_ub hε
  let K : ℝ := (1 / 2) * (2 * Real.pi * C + ∫ x : ℝ, (1 + (ε * x) ^ 2)⁻¹)
  let F_ε : ℝ → ℂ := fun t =>
    (Real.exp t : ℂ) * ch19InvFourier (fun x => pwDamped f ε ((x : ℂ) + (1 : ℂ) * Complex.I)) t
  have hF_cont : Continuous F_ε :=
    (Complex.continuous_ofReal.comp Real.continuous_exp).mul
      (continuous_ch19InvFourier_of_integrable (hprops 1 one_pos).2.2.1)
  have hF_height : ∀ (y : ℝ), 0 < y → ∀ t : ℝ,
      ch19InvFourier (fun x => pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)) t =
        F_ε t * (Real.exp (-t * y) : ℂ) := by
    intro y hy t
    have hind := pwDamped_height_independence hf hL2 hC_ub hε hy one_pos t
    have hmul := congr_arg (· * (Real.exp (-t * y) : ℂ)) hind
    dsimp [F_ε] at hmul ⊢
    have hexp_cancel : (Real.exp (t * y) : ℂ) * (Real.exp (-t * y) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      simp
    have hlhs : (Real.exp (t * y) : ℂ) *
        ch19InvFourier (fun x => pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)) t *
          (Real.exp (-t * y) : ℂ) =
        ch19InvFourier (fun x => pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)) t := by
      calc _ = ((Real.exp (t * y) : ℂ) * (Real.exp (-t * y) : ℂ)) *
          ch19InvFourier (fun x => pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)) t := by ring
        _ = _ := by rw [hexp_cancel, one_mul]
    rw [hlhs] at hmul
    simpa [mul_assoc] using hmul
  have hF_neg : ∀ t : ℝ, t < 0 → F_ε t = 0 := by
    intro t ht
    have hnorm_le : ∀ n : ℕ, ‖F_ε t‖ ≤
        Real.exp (t * ((n : ℝ) + 1)) * ((1 / (2 * Real.pi)) * K) := by
      intro n
      let y : ℝ := (n : ℝ) + 1
      have hy : 0 < y := by positivity
      have hid := pwDamped_height_independence hf hL2 hC_ub hε one_pos hy t
      have h1 : F_ε t = (Real.exp (t * y) : ℂ) *
          ch19InvFourier (fun x => pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)) t := by
        simpa [F_ε] using hid
      rw [h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      unfold ch19InvFourier
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ‖∫ x : ℝ, pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I) *
              Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))‖
          ≤ ∫ x : ℝ, ‖pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I) *
              Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))‖ := norm_integral_le_integral_norm _
        _ = ∫ x : ℝ, ‖pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by
            congr 1 with x
            rw [norm_mul, norm_exp_neg_I_mul_real_mul_real, mul_one]
        _ ≤ K := (hprops y hy).2.2.2
    have hlim0 : Tendsto (fun n : ℕ => Real.exp (t * ((n : ℝ) + 1)) * ((1 / (2 * Real.pi)) * K))
        atTop (𝓝 0) := by
      have h_atBot : Tendsto (fun n : ℕ => t * ((n : ℝ) + 1)) atTop atBot := by
        have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
          tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
        exact tendsto_const_nhds.neg_mul_atTop ht h1
      simpa using (Real.tendsto_exp_atBot.comp h_atBot).mul_const ((1 / (2 * Real.pi)) * K)
    have hle0 : ‖F_ε t‖ ≤ 0 := ge_of_tendsto hlim0 (Eventually.of_forall hnorm_le)
    exact norm_le_zero_iff.mp hle0
  have hF_y_bound : ∀ y : ℝ, 0 < y →
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖F_ε t‖ ^ 2 * Real.exp (-2 * t * y)) ≤
        ENNReal.ofReal C := by
    intro y hy
    obtain ⟨_, hmem2_y, hint1_y, _⟩ := hprops y hy
    obtain ⟨hinv_mem, hinv_plan⟩ := ch19InvFourier_plancherel_L1_L2 hint1_y hmem2_y
    have h_slice_le : (1 / (2 * Real.pi)) *
        ∫ x : ℝ, ‖pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ≤ C := by
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) (hC_ub y hy)
      refine integral_mono hmem2_y.norm.integrable_sq (hL2 y hy).norm.integrable_sq fun x => ?_
      unfold pwDamped
      rw [norm_mul]
      have hle1 := norm_pwDamp_le_one hε (z := (x : ℂ) + (y : ℂ) * Complex.I) (by simp [hy])
      have hle_norm : ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ *
          ‖pwDamp ε ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
          ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ :=
        mul_le_of_le_one_right (norm_nonneg _) hle1
      have hnn1 := norm_nonneg (f ((x : ℂ) + (y : ℂ) * Complex.I))
      have hnn2 := norm_nonneg (pwDamp ε ((x : ℂ) + (y : ℂ) * Complex.I))
      exact pow_le_pow_left₀ (mul_nonneg hnn1 hnn2) hle_norm 2
    have h_int_le : ∫ t : ℝ, ‖ch19InvFourier
        (fun x => pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)) t‖ ^ 2 ≤ C :=
      hinv_plan.trans_le h_slice_le
    have h_lint : ∫⁻ t : ℝ, ENNReal.ofReal
        (‖ch19InvFourier (fun x => pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)) t‖ ^ 2) ≤
        ENNReal.ofReal C := by
      rw [← ofReal_integral_eq_lintegral_ofReal hinv_mem.norm.integrable_sq
        (Eventually.of_forall fun _ => sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal h_int_le
    refine le_trans ?_ h_lint
    calc ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖F_ε t‖ ^ 2 * Real.exp (-2 * t * y))
        = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal
            (‖ch19InvFourier (fun x => pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)) t‖ ^ 2) := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
          rw [hF_height y hy t]
          have hnorm_rhs : ∀ z : ℂ,
              ‖z * (Real.exp (-t * y) : ℂ)‖ ^ 2 = ‖z‖ ^ 2 * Real.exp (-2 * t * y) := by
            intro z
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
              mul_pow, ← Real.exp_nat_mul]
            exact congr_arg (‖z‖ ^ 2 * ·) (congr_arg Real.exp (by push_cast; ring))
          rw [hnorm_rhs (F_ε t)]
      _ ≤ ∫⁻ t : ℝ, ENNReal.ofReal
            (‖ch19InvFourier (fun x => pwDamped f ε ((x : ℂ) + (y : ℂ) * Complex.I)) t‖ ^ 2) :=
          lintegral_mono' Measure.restrict_le_self le_rfl
  have hF_lint_le : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖F_ε t‖ ^ 2) ≤ ENNReal.ofReal C := by
    let u : ℕ → ℝ → ℝ≥0∞ := fun m t =>
      if 0 < t then ENNReal.ofReal (‖F_ε t‖ ^ 2 * Real.exp (-2 * t * (1 / ((m : ℝ) + 1)))) else 0
    have hu_meas : ∀ m : ℕ, Measurable (u m) := fun m =>
      Measurable.ite measurableSet_Ioi
        (ENNReal.measurable_ofReal.comp ((hF_cont.norm.pow 2).mul (by fun_prop)).measurable)
        measurable_const
    have hu_mono : Monotone u := by
      intro m₁ m₂ hm t
      dsimp [u]
      split_ifs with ht
      · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (sq_nonneg _))
        have hdiv : 1 / ((m₂ : ℝ) + 1) ≤ 1 / ((m₁ : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
        nlinarith
      · exact le_rfl
    have h_sup_eq : ∀ t ∈ Set.Ioi (0 : ℝ), (⨆ m : ℕ, u m t) = ENNReal.ofReal (‖F_ε t‖ ^ 2) := by
      intro t ht
      have ht_pos : 0 < t := ht
      have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal
          (‖F_ε t‖ ^ 2 * Real.exp (-2 * t * (1 / ((m : ℝ) + 1)))))
          atTop (𝓝 (ENNReal.ofReal (‖F_ε t‖ ^ 2))) := by
        refine ENNReal.continuous_ofReal.continuousAt.tendsto.comp ?_
        have h0 : Tendsto (fun m : ℕ => -2 * t * (1 / ((m : ℝ) + 1))) atTop (𝓝 (-2 * t * 0)) :=
          tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
        rw [mul_zero] at h0
        simpa using tendsto_const_nhds.mul (Real.continuous_exp.continuousAt.tendsto.comp h0)
      have heq_u : (fun m : ℕ => u m t) = fun m : ℕ =>
          ENNReal.ofReal (‖F_ε t‖ ^ 2 * Real.exp (-2 * t * (1 / ((m : ℝ) + 1)))) := by
        ext m; simp [u, ht_pos]
      rw [heq_u]
      exact tendsto_nhds_unique (tendsto_atTop_ciSup (fun a b hab => by
        have := hu_mono hab t; simpa [u, ht_pos] using this) ⟨ENNReal.ofReal (‖F_ε t‖ ^ 2), by
        rintro _ ⟨m, rfl⟩
        refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (sq_nonneg _) (Real.exp_le_one_iff.mpr ?_))
        have : 0 < 1 / ((m : ℝ) + 1) := by positivity
        nlinarith⟩) hlim
    calc ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖F_ε t‖ ^ 2)
        = ∫⁻ t in Set.Ioi (0 : ℝ), (⨆ m : ℕ, u m t) :=
          setLIntegral_congr_fun measurableSet_Ioi fun t ht => (h_sup_eq t ht).symm
      _ = ⨆ m : ℕ, ∫⁻ t in Set.Ioi (0 : ℝ), u m t :=
          MeasureTheory.lintegral_iSup hu_meas hu_mono
      _ ≤ ENNReal.ofReal C := iSup_le fun m => by
          have heq : (∫⁻ t in Set.Ioi (0 : ℝ), u m t) =
              ∫⁻ t in Set.Ioi (0 : ℝ),
                ENNReal.ofReal (‖F_ε t‖ ^ 2 * Real.exp (-2 * t * (1 / ((m : ℝ) + 1)))) := by
            refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
            simp [u, show 0 < t from ht]
          rw [heq]
          exact hF_y_bound (1 / ((m : ℝ) + 1)) (by positivity)
  have hF_mem2 : MemLp F_ε 2 (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine (memLp_norm_iff (hF_cont.aestronglyMeasurable)).mp ?_
    refine (memLp_two_iff_integrable_sq (hF_cont.norm.aestronglyMeasurable)).mpr ?_
    refine ⟨((hF_cont.norm.pow 2).aestronglyMeasurable), ?_⟩
    calc ∫⁻ t in Set.Ioi (0 : ℝ), ‖‖F_ε t‖ ^ 2‖ₑ
        = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖F_ε t‖ ^ 2) := by
          refine lintegral_congr fun t => ?_
          rw [← ofReal_norm, Real.norm_of_nonneg (sq_nonneg _)]
      _ < ⊤ := hF_lint_le.trans_lt ENNReal.ofReal_lt_top
  have hF_norm_le : ∫ t in Set.Ioi (0 : ℝ), ‖F_ε t‖ ^ 2 ≤ C := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
      hF_mem2.norm.integrable_sq.aestronglyMeasurable]
    have hcongr : (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖F_ε t‖ ^ 2)) =
        ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((fun x => ‖F_ε x‖ ^ 2) t) := rfl
    exact ENNReal.toReal_le_of_le_ofReal hC_nn hF_lint_le
  refine ⟨F_ε, hF_cont, hF_neg, hF_mem2, hF_norm_le, hF_height, fun z hz => ?_⟩
  let x := z.re
  let y := z.im
  have hy : 0 < y := hz
  have hz_eq : z = (x : ℂ) + (y : ℂ) * Complex.I := (Complex.re_add_im z).symm
  rw [hz_eq]
  obtain ⟨hcont_y, _, hint1_y, _⟩ := hprops y hy
  have hG_ae : ch19InvFourier (fun u => pwDamped f ε ((u : ℂ) + (y : ℂ) * Complex.I)) =ᵐ[volume]
      Set.indicator (Set.Ioi (0 : ℝ)) (fun t => F_ε t * (Real.exp (-t * y) : ℂ)) := by
    have h0 : ({0} : Set ℝ)ᶜ ∈ ae volume := by
      rw [mem_ae_iff, compl_compl, Real.volume_singleton]
    filter_upwards [h0] with t ht0
    have ht_ne : t ≠ 0 := ht0
    rcases lt_or_gt_of_ne ht_ne with hlt | hgt
    · have hnm : t ∉ Set.Ioi (0 : ℝ) := not_lt.mpr hlt.le
      rw [hF_height y hy t, hF_neg t hlt, zero_mul, Set.indicator_of_notMem hnm]
    · have hm : t ∈ Set.Ioi (0 : ℝ) := hgt
      rw [hF_height y hy t, Set.indicator_of_mem hm]
  have hG_int : Integrable
      (ch19InvFourier (fun u => pwDamped f ε ((u : ℂ) + (y : ℂ) * Complex.I))) volume := by
    refine Integrable.congr ?_ hG_ae.symm
    rw [integrable_indicator_iff measurableSet_Ioi]
    have hexp : MemLp (fun t : ℝ => Real.exp (-y * t)) 2 (volume.restrict (Set.Ioi (0 : ℝ))) :=
      memLp_exp_neg_mul_Ioi hy
    refine (hF_mem2.norm.integrable_mul hexp).mono'
      (hF_cont.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
    filter_upwards with t
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    dsimp [Pi.mul_apply]
    exact le_of_eq (congr_arg (‖F_ε t‖ * ·) (congr_arg Real.exp (by ring)))
  have hinv_pt := ch19_fourier_inversion_pointwise hcont_y hint1_y hG_int x
  rw [hinv_pt]
  unfold ch19Fourier holomorphicFourierHalfLine
  have hcongr_ae : (fun t : ℝ =>
      ch19InvFourier (fun u => pwDamped f ε ((u : ℂ) + (y : ℂ) * Complex.I)) t *
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) =ᵐ[volume]
      Set.indicator (Set.Ioi (0 : ℝ))
        (fun t : ℝ => F_ε t * Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))) := by
    filter_upwards [hG_ae] with t ht
    rw [ht]
    by_cases hpos : t ∈ Set.Ioi (0 : ℝ)
    · simp only [Set.indicator_of_mem hpos]
      rw [mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      exact congr_arg Complex.exp (by push_cast; ring_nf; simp [Complex.I_sq])
    · simp [hpos]
  rw [integral_congr_ae hcongr_ae, integral_indicator measurableSet_Ioi]

/-- **Theorem 19.2 (First Paley–Wiener Theorem, RCA pp. 372–374):**
Suppose `f` is holomorphic in the open upper half-plane `{z : ℂ | 0 < z.im}` and
`C = sup_{y > 0} (1 / (2π)) ∫_{-∞}^∞ |f(x + i y)|² dx < ∞` (encoded via `IsLeast` of upper bounds).
Then there exists `F ∈ L²(0, ∞)` such that `f(z) = ∫_0^∞ F(t) exp(i t z) dt` for every `z` with
`0 < z.im`, and `∫_0^∞ |F(t)|² dt = C`. -/
theorem theorem19_2 {f : ℂ → ℂ} {C : ℝ}
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hL2 : ∀ y : ℝ, 0 < y → MemLp (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I)) 2 volume)
    (hC_sup : IsLeast
      {M : ℝ | ∀ y : ℝ, 0 < y →
        (1 / (2 * Real.pi)) * ∫ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ≤ M} C) :
    ∃ F : ℝ → ℂ,
      MemLp F 2 (volume.restrict (Set.Ioi (0 : ℝ))) ∧
      (∀ z : ℂ, 0 < z.im → f z = holomorphicFourierHalfLine F z) ∧
      ∫ t in Set.Ioi (0 : ℝ), ‖F t‖ ^ 2 = C := by
  have hC_ub : ∀ y : ℝ, 0 < y →
      (1 / (2 * Real.pi)) * ∫ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ≤ C := hC_sup.1
  have hC_nn : 0 ≤ C := by
    refine le_trans ?_ (hC_ub 1 one_pos)
    exact mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)
  let εseq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε_pos : ∀ n : ℕ, 0 < εseq n := fun n => by dsimp [εseq]; positivity
  choose Fseq hF_cont hF_neg hF_mem2 hF_norm_le hF_height hF_rep using
    fun n : ℕ => pwDamped_representation hf hL2 hC_ub hC_nn (hε_pos n)
  let μ := volume.restrict (Set.Ioi (0 : ℝ))
  -- For every y > 0, pwDamped f (εseq n) (· + iy) → f (· + iy) in L²(ℝ)
  have h_damped_L2_conv : ∀ y : ℝ, 0 < y →
      Tendsto (fun n : ℕ =>
        ∫ x : ℝ, ‖pwDamped f (εseq n) ((x : ℂ) + (y : ℂ) * Complex.I) -
          f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) atTop (𝓝 0) := by
    intro y hy
    obtain ⟨hw_int, hprops⟩ := pwDamped_slice_props hf hL2 hC_ub (hε_pos 0)
    have hdom : Integrable (fun x : ℝ => 4 * ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) volume :=
      (hL2 y hy).norm.integrable_sq.const_mul 4
    have h0_int : (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) := by simp
    rw [h0_int]
    refine tendsto_integral_of_dominated_convergence
      (fun x : ℝ => 4 * ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2)
      (fun n => ?_) hdom (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · obtain ⟨_, hprops_n⟩ := pwDamped_slice_props hf hL2 hC_ub (hε_pos n)
      exact ((hprops_n y hy).2.1.sub (hL2 y hy)).norm.integrable_sq.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h1 : ‖pwDamped f (εseq n) ((x : ℂ) + (y : ℂ) * Complex.I) -
          f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
          2 * ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by
        have hle1 := norm_pwDamp_le_one (hε_pos n) (z := (x : ℂ) + (y : ℂ) * Complex.I) (by simp [hy])
        calc ‖pwDamped f (εseq n) ((x : ℂ) + (y : ℂ) * Complex.I) -
              f ((x : ℂ) + (y : ℂ) * Complex.I)‖
            ≤ ‖pwDamped f (εseq n) ((x : ℂ) + (y : ℂ) * Complex.I)‖ +
                ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ := norm_sub_le _ _
          _ = ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ *
                ‖pwDamp (εseq n) ((x : ℂ) + (y : ℂ) * Complex.I)‖ +
                ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by unfold pwDamped; rw [norm_mul]
          _ ≤ ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ * 1 +
                ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by
              gcongr
          _ = 2 * ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by ring
      nlinarith [norm_nonneg (pwDamped f (εseq n) ((x : ℂ) + (y : ℂ) * Complex.I) -
        f ((x : ℂ) + (y : ℂ) * Complex.I))]
    · have h_eps0 : Tendsto (fun n : ℕ => (εseq n : ℂ)) atTop (𝓝 0) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
      have h_denom : Tendsto
          (fun n : ℕ => 1 - Complex.I * (εseq n : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))
          atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.sub ((tendsto_const_nhds.mul h_eps0).mul tendsto_const_nhds)
      have h_damp : Tendsto (fun n : ℕ => pwDamp (εseq n) ((x : ℂ) + (y : ℂ) * Complex.I))
          atTop (𝓝 1) := by
        simpa [pwDamp] using h_denom.inv₀ one_ne_zero
      have h_pt : Tendsto (fun n : ℕ => pwDamped f (εseq n) ((x : ℂ) + (y : ℂ) * Complex.I))
          atTop (𝓝 (f ((x : ℂ) + (y : ℂ) * Complex.I))) := by
        simpa [pwDamped] using tendsto_const_nhds.mul h_damp
      have h_sub : Tendsto (fun n : ℕ => ‖pwDamped f (εseq n) ((x : ℂ) + (y : ℂ) * Complex.I) -
          f ((x : ℂ) + (y : ℂ) * Complex.I)‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.mp h_pt
      simpa using h_sub.pow 2
  -- For every y > 0, G_y n (t) := Fseq n t * exp(-t * y) is Cauchy in Lp ℂ 2 μ, hence converges!
  have hGy_mem : ∀ (y : ℝ), 0 < y → ∀ n : ℕ,
      MemLp (fun t : ℝ => Fseq n t * (Real.exp (-t * y) : ℂ)) 2 μ := by
    intro y hy n
    refine (hF_mem2 n).norm.mono'
      ((hF_cont n).aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := ht
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith))
  have hGy_conv : ∀ (y : ℝ) (hy : 0 < y),
      ∃ g_y : Lp ℂ 2 μ,
        Tendsto (fun n : ℕ => (hGy_mem y hy n).toLp
          (fun t : ℝ => Fseq n t * (Real.exp (-t * y) : ℂ))) atTop (𝓝 g_y) := by
    intro y hy
    let u : ℕ → Lp ℂ 2 μ := fun n =>
      (hGy_mem y hy n).toLp (fun t : ℝ => Fseq n t * (Real.exp (-t * y) : ℂ))
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro δ hδ
    have hδ2 : 0 < δ ^ 2 / 4 := by positivity
    have hlim_y := h_damped_L2_conv y hy
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim_y (2 * Real.pi * (δ ^ 2 / 4)) (by positivity)
    refine ⟨N, fun n hn m hm => ?_⟩
    obtain ⟨_, hprops_n⟩ := pwDamped_slice_props hf hL2 hC_ub (hε_pos n)
    obtain ⟨_, hprops_m⟩ := pwDamped_slice_props hf hL2 hC_ub (hε_pos m)
    let hn_slice := fun x : ℝ => pwDamped f (εseq n) ((x : ℂ) + (y : ℂ) * Complex.I)
    let hm_slice := fun x : ℝ => pwDamped f (εseq m) ((x : ℂ) + (y : ℂ) * Complex.I)
    have hdiff_int1 : Integrable (fun x => hn_slice x - hm_slice x) volume :=
      (hprops_n y hy).2.2.1.sub (hprops_m y hy).2.2.1
    have hdiff_mem2 : MemLp (fun x => hn_slice x - hm_slice x) 2 volume :=
      (hprops_n y hy).2.1.sub (hprops_m y hy).2.1
    have hplan_diff := (ch19InvFourier_plancherel_L1_L2 hdiff_int1 hdiff_mem2).2
    have h_inv_sub : ∀ t : ℝ,
        ch19InvFourier (fun x => hn_slice x - hm_slice x) t =
          Fseq n t * (Real.exp (-t * y) : ℂ) - Fseq m t * (Real.exp (-t * y) : ℂ) := by
      intro t
      have hlin : ch19InvFourier (fun x => hn_slice x - hm_slice x) t =
          ch19InvFourier hn_slice t - ch19InvFourier hm_slice t := by
        unfold ch19InvFourier
        have hsub : ∀ x : ℝ, (hn_slice x - hm_slice x) *
            Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) =
            hn_slice x * Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) -
            hm_slice x * Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) := fun _ => sub_mul _ _ _
        simp_rw [hsub]
        rw [integral_sub]
        · ring
        · refine (hprops_n y hy).2.2.1.norm.mono'
            ((hprops_n y hy).1.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
          filter_upwards with x; rw [norm_mul, norm_exp_neg_I_mul_real_mul_real, mul_one]
        · refine (hprops_m y hy).2.2.1.norm.mono'
            ((hprops_m y hy).1.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
          filter_upwards with x; rw [norm_mul, norm_exp_neg_I_mul_real_mul_real, mul_one]
      rw [hlin, hF_height n y hy t, hF_height m y hy t]
    have h_dist_sq : dist (u n) (u m) ^ 2 ≤
        (1 / (2 * Real.pi)) * ∫ x : ℝ, ‖hn_slice x - hm_slice x‖ ^ 2 := by
      rw [dist_eq_norm]
      let fnm := (fun t : ℝ => Fseq n t * (Real.exp (-t * y) : ℂ)) -
        (fun t : ℝ => Fseq m t * (Real.exp (-t * y) : ℂ))
      have hmem_sub : MemLp fnm 2 μ := (hGy_mem y hy n).sub (hGy_mem y hy m)
      have h_unm : u n - u m = hmem_sub.toLp fnm := by
        dsimp [u, fnm]
        exact (MemLp.toLp_sub (hGy_mem y hy n) (hGy_mem y hy m)).symm
      rw [h_unm, Lp.norm_toLp, hmem_sub.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
      simp only [ENNReal.toReal_ofNat]
      rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _),
        show (2 : ℝ)⁻¹ * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
      rw [← hplan_diff]
      have h_int_sub := (ch19InvFourier_plancherel_L1_L2 hdiff_int1 hdiff_mem2).1.norm.integrable_sq
      simp_rw [h_inv_sub] at h_int_sub ⊢
      refine le_trans ?_
        (setIntegral_le_integral (s := Set.Ioi (0 : ℝ)) h_int_sub
          (Eventually.of_forall fun _ => sq_nonneg _))
      exact le_of_eq (by dsimp [μ]; congr 1 with t; dsimp [fnm]; rw [Real.rpow_two])
    have h_tri_sq : ∫ x : ℝ, ‖hn_slice x - hm_slice x‖ ^ 2 < 2 * Real.pi * δ ^ 2 := by
      let fn_err := fun x : ℝ => ‖hn_slice x - f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2
      let fm_err := fun x : ℝ => ‖hm_slice x - f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2
      have hfn_lt : ∫ x : ℝ, fn_err x < 2 * Real.pi * (δ ^ 2 / 4) := by
        have hd := hN n hn
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at hd
        exact hd
      have hfm_lt : ∫ x : ℝ, fm_err x < 2 * Real.pi * (δ ^ 2 / 4) := by
        have hd := hN m hm
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at hd
        exact hd
      have hpt : ∀ x : ℝ, ‖hn_slice x - hm_slice x‖ ^ 2 ≤ 2 * fn_err x + 2 * fm_err x := by
        intro x
        have htri : ‖hn_slice x - hm_slice x‖ ≤
            ‖hn_slice x - f ((x : ℂ) + (y : ℂ) * Complex.I)‖ +
            ‖hm_slice x - f ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by
          calc ‖hn_slice x - hm_slice x‖
              = ‖(hn_slice x - f ((x : ℂ) + (y : ℂ) * Complex.I)) -
                  (hm_slice x - f ((x : ℂ) + (y : ℂ) * Complex.I))‖ := by congr 1; ring
            _ ≤ _ := norm_sub_le _ _
        dsimp [fn_err, fm_err]
        have hsq_diff := sq_nonneg (‖hn_slice x - f ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
          ‖hm_slice x - f ((x : ℂ) + (y : ℂ) * Complex.I)‖)
        nlinarith [norm_nonneg (hn_slice x - hm_slice x)]
      have hint_fn : Integrable fn_err volume :=
        ((hprops_n y hy).2.1.sub (hL2 y hy)).norm.integrable_sq
      have hint_fm : Integrable fm_err volume :=
        ((hprops_m y hy).2.1.sub (hL2 y hy)).norm.integrable_sq
      calc ∫ x : ℝ, ‖hn_slice x - hm_slice x‖ ^ 2
          ≤ ∫ x : ℝ, (2 * fn_err x + 2 * fm_err x) :=
            integral_mono hdiff_mem2.norm.integrable_sq ((hint_fn.const_mul 2).add (hint_fm.const_mul 2)) hpt
        _ = 2 * (∫ x : ℝ, fn_err x) + 2 * (∫ x : ℝ, fm_err x) := by
            rw [integral_add (hint_fn.const_mul 2) (hint_fm.const_mul 2),
              integral_const_mul, integral_const_mul]
        _ < 2 * (2 * Real.pi * (δ ^ 2 / 4)) + 2 * (2 * Real.pi * (δ ^ 2 / 4)) := by linarith
        _ = 2 * Real.pi * δ ^ 2 := by ring
    have hlt_sq : dist (u n) (u m) ^ 2 < δ ^ 2 := by
      calc dist (u n) (u m) ^ 2
          ≤ (1 / (2 * Real.pi)) * ∫ x : ℝ, ‖hn_slice x - hm_slice x‖ ^ 2 := h_dist_sq
        _ < (1 / (2 * Real.pi)) * (2 * Real.pi * δ ^ 2) :=
            mul_lt_mul_of_pos_left h_tri_sq (by positivity)
        _ = δ ^ 2 := by field_simp [(mul_pos two_pos Real.pi_pos).ne']
    nlinarith [dist_nonneg (x := u n) (y := u m)]
  choose g_lim hg_lim using hGy_conv
  let g₁ := g_lim 1 one_pos
  let F : ℝ → ℂ := fun t => if 0 < t then (g₁ : ℝ → ℂ) t * (Real.exp t : ℂ) else 0
  -- Helper: L² convergence implies ∫ ‖G_n - g_y‖² → 0 on μ
  have hg_lim_int_sq : ∀ (y : ℝ) (hy : 0 < y),
      Tendsto (fun n : ℕ => ∫ t, ‖Fseq n t * (Real.exp (-t * y) : ℂ) - (g_lim y hy : ℝ → ℂ) t‖ ^ 2 ∂μ)
        atTop (𝓝 0) := by
    intro y hy
    have hlim_norm : Tendsto (fun n : ℕ =>
        ‖(hGy_mem y hy n).toLp (fun t : ℝ => Fseq n t * (Real.exp (-t * y) : ℂ)) - g_lim y hy‖ ^ 2)
        atTop (𝓝 0) := by
      simpa using ((tendsto_iff_norm_sub_tendsto_zero.mp (hg_lim y hy)).pow 2)
    refine hlim_norm.congr' (Eventually.of_forall fun n => ?_)
    let v := (hGy_mem y hy n).toLp (fun t : ℝ => Fseq n t * (Real.exp (-t * y) : ℂ)) - g_lim y hy
    have hv_mem := Lp.memLp v
    have hv_ae : (v : ℝ → ℂ) =ᵐ[μ] fun t =>
        Fseq n t * (Real.exp (-t * y) : ℂ) - (g_lim y hy : ℝ → ℂ) t := by
      filter_upwards [Lp.coeFn_sub
          ((hGy_mem y hy n).toLp (fun t : ℝ => Fseq n t * (Real.exp (-t * y) : ℂ))) (g_lim y hy),
        (hGy_mem y hy n).coeFn_toLp] with t ht1 ht2
      exact ht1.trans (by dsimp [Pi.sub_apply]; rw [ht2])
    have hv_norm : ‖v‖ ^ 2 = ∫ t, ‖(v : ℝ → ℂ) t‖ ^ 2 ∂μ := by
      rw [Lp.norm_def, hv_mem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
      simp only [ENNReal.toReal_ofNat]
      rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _)]
      norm_num
    rw [hv_norm]
    apply integral_congr_ae
    filter_upwards [hv_ae] with t ht
    rw [ht]
  -- Consistency across heights: g_lim y hy =ᵐ[μ] fun t => F t * exp(-t * y)
  have hg_compat : ∀ (y : ℝ) (hy : 0 < y),
      (g_lim y hy : ℝ → ℂ) =ᵐ[μ] fun t => F t * (Real.exp (-t * y) : ℂ) := by
    intro y hy
    let diff : ℝ → ℂ := fun t =>
      (g_lim y hy : ℝ → ℂ) t * (Real.exp (-t) : ℂ) - (g₁ : ℝ → ℂ) t * (Real.exp (-t * y) : ℂ)
    have hdiff_mem2 : MemLp diff 2 μ := by
      have h1 : MemLp (fun t => (g_lim y hy : ℝ → ℂ) t * (Real.exp (-t) : ℂ)) 2 μ := by
        refine (Lp.memLp (g_lim y hy)).norm.mono'
          ((Lp.memLp (g_lim y hy)).aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht_pos : 0 < t := ht
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (by linarith))
      have h2 : MemLp (fun t => (g₁ : ℝ → ℂ) t * (Real.exp (-t * y) : ℂ)) 2 μ := by
        refine (Lp.memLp g₁).norm.mono'
          ((Lp.memLp g₁).aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht_pos : 0 < t := ht
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith))
      exact h1.sub h2
    have h_int_zero : ∫ t, ‖diff t‖ ^ 2 ∂μ = 0 := by
      refine le_antisymm ?_ (integral_nonneg fun _ => sq_nonneg _)
      have h_le_seq : ∀ n : ℕ, ∫ t, ‖diff t‖ ^ 2 ∂μ ≤
          2 * (∫ t, ‖Fseq n t * (Real.exp (-t * y) : ℂ) - (g_lim y hy : ℝ → ℂ) t‖ ^ 2 ∂μ) +
          2 * (∫ t, ‖Fseq n t * (Real.exp (-t * 1) : ℂ) - (g₁ : ℝ → ℂ) t‖ ^ 2 ∂μ) := by
        intro n
        let e1 := fun t : ℝ => ‖Fseq n t * (Real.exp (-t * y) : ℂ) - (g_lim y hy : ℝ → ℂ) t‖ ^ 2
        let e2 := fun t : ℝ => ‖Fseq n t * (Real.exp (-t * 1) : ℂ) - (g₁ : ℝ → ℂ) t‖ ^ 2
        have he1_int : Integrable e1 μ :=
          ((hGy_mem y hy n).sub (Lp.memLp (g_lim y hy))).norm.integrable_sq
        have he2_int : Integrable e2 μ :=
          ((hGy_mem 1 one_pos n).sub (Lp.memLp g₁)).norm.integrable_sq
        calc ∫ t, ‖diff t‖ ^ 2 ∂μ
            ≤ ∫ t, (2 * e1 t + 2 * e2 t) ∂μ := by
              refine integral_mono_ae hdiff_mem2.norm.integrable_sq
                ((he1_int.const_mul 2).add (he2_int.const_mul 2)) ?_
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              have ht_pos : 0 < t := ht
              have hid_n : Fseq n t * (Real.exp (-t * y) : ℂ) * (Real.exp (-t) : ℂ) =
                  Fseq n t * (Real.exp (-t * 1) : ℂ) * (Real.exp (-t * y) : ℂ) := by
                simp only [mul_one]; ring
              have htri : ‖diff t‖ ≤
                  ‖Fseq n t * (Real.exp (-t * y) : ℂ) - (g_lim y hy : ℝ → ℂ) t‖ +
                  ‖Fseq n t * (Real.exp (-t * 1) : ℂ) - (g₁ : ℝ → ℂ) t‖ := by
                have hsplit : diff t =
                    ((g_lim y hy : ℝ → ℂ) t - Fseq n t * (Real.exp (-t * y) : ℂ)) * (Real.exp (-t) : ℂ) +
                    (Fseq n t * (Real.exp (-t * 1) : ℂ) - (g₁ : ℝ → ℂ) t) * (Real.exp (-t * y) : ℂ) := by
                  dsimp [diff]
                  rw [mul_one]
                  ring
                rw [hsplit]
                refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
                · rw [norm_mul, norm_sub_rev, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
                  exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (by linarith))
                · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
                  exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith))
              dsimp [e1, e2]
              have hsq_diff := sq_nonneg (‖Fseq n t * (Real.exp (-t * y) : ℂ) - (g_lim y hy : ℝ → ℂ) t‖ -
                ‖Fseq n t * (Real.exp (-t * 1) : ℂ) - (g₁ : ℝ → ℂ) t‖)
              nlinarith [norm_nonneg (diff t)]
          _ = 2 * (∫ t, e1 t ∂μ) + 2 * (∫ t, e2 t ∂μ) := by
              rw [integral_add (he1_int.const_mul 2) (he2_int.const_mul 2),
                integral_const_mul, integral_const_mul]
      have hlim0 : Tendsto (fun n : ℕ =>
          2 * (∫ t, ‖Fseq n t * (Real.exp (-t * y) : ℂ) - (g_lim y hy : ℝ → ℂ) t‖ ^ 2 ∂μ) +
          2 * (∫ t, ‖Fseq n t * (Real.exp (-t * 1) : ℂ) - (g₁ : ℝ → ℂ) t‖ ^ 2 ∂μ)) atTop (𝓝 0) := by
        simpa using ((hg_lim_int_sq y hy).const_mul 2).add ((hg_lim_int_sq 1 one_pos).const_mul 2)
      exact ge_of_tendsto hlim0 (Eventually.of_forall h_le_seq)
    have hae_diff0 : (fun t => ‖diff t‖ ^ 2) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
        hdiff_mem2.norm.integrable_sq).mp h_int_zero
    filter_upwards [hae_diff0, ae_restrict_mem measurableSet_Ioi] with t ht0 ht_pos
    have hpos : 0 < t := ht_pos
    have hd0 : diff t = 0 := by
      have : ‖diff t‖ ^ 2 = 0 := ht0
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp this)
    have heq1 : (g_lim y hy : ℝ → ℂ) t * (Real.exp (-t) : ℂ) =
        (g₁ : ℝ → ℂ) t * (Real.exp (-t * y) : ℂ) := sub_eq_zero.mp hd0
    have hmul_e := congr_arg (· * (Real.exp t : ℂ)) heq1
    have hcancel : (Real.exp (-t) : ℂ) * (Real.exp t : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
    have hlhs : (g_lim y hy : ℝ → ℂ) t * (Real.exp (-t) : ℂ) * (Real.exp t : ℂ) =
        (g_lim y hy : ℝ → ℂ) t := by
      rw [mul_assoc, hcancel, mul_one]
    rw [hlhs] at hmul_e
    rw [hmul_e]
    dsimp [F]
    simp only [hpos, ↓reduceIte]
    ring
  -- Norm bound ∫_{Ioi 0} ‖g_lim y hy‖² ≤ C for every y > 0
  have hg_norm_le : ∀ (y : ℝ) (hy : 0 < y),
      ∫ t, ‖(g_lim y hy : ℝ → ℂ) t‖ ^ 2 ∂μ ≤ C := by
    intro y hy
    have hseq_le : ∀ n : ℕ, ‖(hGy_mem y hy n).toLp
        (fun t : ℝ => Fseq n t * (Real.exp (-t * y) : ℂ))‖ ^ 2 ≤ C := by
      intro n
      rw [Lp.norm_toLp, (hGy_mem y hy n).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
      simp only [ENNReal.toReal_ofNat]
      rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _),
        show (2 : ℝ)⁻¹ * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
      refine le_trans ?_ (hF_norm_le n)
      refine integral_mono_ae (by simpa [Real.rpow_two] using (hGy_mem y hy n).norm.integrable_sq)
        (hF_mem2 n).norm.integrable_sq ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht_pos : 0 < t := ht
      rw [Real.rpow_two]
      have hexp_le : ‖(Real.exp (-t * y) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_one_iff.mpr (by nlinarith)
      have hprod_le : ‖Fseq n t * (Real.exp (-t * y) : ℂ)‖ ≤ ‖Fseq n t‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) hexp_le
      exact pow_le_pow_left₀ (norm_nonneg _) hprod_le 2
    have hlim_sq : Tendsto (fun n : ℕ => ‖(hGy_mem y hy n).toLp
        (fun t : ℝ => Fseq n t * (Real.exp (-t * y) : ℂ))‖ ^ 2) atTop (𝓝 (‖g_lim y hy‖ ^ 2)) :=
      ((hg_lim y hy).norm).pow 2
    have hnorm_g_le : ‖g_lim y hy‖ ^ 2 ≤ C := le_of_tendsto hlim_sq (Eventually.of_forall hseq_le)
    have h_eq : ‖g_lim y hy‖ ^ 2 = ∫ t, ‖(g_lim y hy : ℝ → ℂ) t‖ ^ 2 ∂μ := by
      have hm := Lp.memLp (g_lim y hy)
      rw [Lp.norm_def, hm.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
      simp only [ENNReal.toReal_ofNat]
      rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _)]
      norm_num
    rwa [← h_eq]
  -- MCT as y = 1/(m+1) → 0⁺ gives MemLp F 2 μ and ∫ ‖F‖² ∂μ ≤ C
  have hF_aemeas : AEStronglyMeasurable F μ := by
    have h1 : AEStronglyMeasurable (fun t : ℝ => (g₁ : ℝ → ℂ) t * (Real.exp t : ℂ)) μ :=
      (Lp.memLp g₁).aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))
    refine h1.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp [F, show 0 < t from ht]
  have hF_lint_le : ∫⁻ t, ENNReal.ofReal (‖F t‖ ^ 2) ∂μ ≤ ENNReal.ofReal C := by
    let u : ℕ → ℝ → ℝ≥0∞ := fun m t =>
      ENNReal.ofReal (‖F t‖ ^ 2 * Real.exp (-2 * t * (1 / ((m : ℝ) + 1))))
    have hu_aemeas : ∀ m : ℕ, AEMeasurable (u m) μ := fun m =>
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((hF_aemeas.norm.pow 2).aemeasurable.mul (Continuous.aemeasurable (by fun_prop)))
    have hu_mono : ∀ᵐ t ∂μ, Monotone (fun m : ℕ => u m t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht m₁ m₂ hm
      have ht_pos : 0 < t := ht
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (sq_nonneg _))
      have hdiv : 1 / ((m₂ : ℝ) + 1) ≤ 1 / ((m₁ : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
      nlinarith
    have h_sup_ae : (fun t => ENNReal.ofReal (‖F t‖ ^ 2)) =ᵐ[μ] fun t => ⨆ m : ℕ, u m t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht_pos : 0 < t := ht
      symm
      have hlim : Tendsto (fun m : ℕ => u m t) atTop (𝓝 (ENNReal.ofReal (‖F t‖ ^ 2))) := by
        refine ENNReal.continuous_ofReal.continuousAt.tendsto.comp ?_
        have h0 : Tendsto (fun m : ℕ => -2 * t * (1 / ((m : ℝ) + 1))) atTop (𝓝 (-2 * t * 0)) :=
          tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
        rw [mul_zero] at h0
        simpa using tendsto_const_nhds.mul (Real.continuous_exp.continuousAt.tendsto.comp h0)
      exact tendsto_nhds_unique (tendsto_atTop_ciSup (fun a b hab => by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (sq_nonneg _))
        have hdiv : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
        nlinarith) ⟨ENNReal.ofReal (‖F t‖ ^ 2), by
        rintro _ ⟨m, rfl⟩
        refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (sq_nonneg _) (Real.exp_le_one_iff.mpr ?_))
        have : 0 < 1 / ((m : ℝ) + 1) := by positivity
        nlinarith⟩) hlim
    rw [lintegral_congr_ae h_sup_ae, MeasureTheory.lintegral_iSup' hu_aemeas hu_mono]
    refine iSup_le fun m => ?_
    let ym : ℝ := 1 / ((m : ℝ) + 1)
    have hym : 0 < ym := by positivity
    have hcongr_m : (fun t => u m t) =ᵐ[μ]
        fun t => ENNReal.ofReal (‖(g_lim ym hym : ℝ → ℂ) t‖ ^ 2) := by
      filter_upwards [hg_compat ym hym] with t ht
      dsimp [u, ym]
      rw [ht, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        mul_pow, ← Real.exp_nat_mul]
      congr 1
      exact congr_arg (‖F t‖ ^ 2 * ·) (congr_arg Real.exp (by ring))
    rw [lintegral_congr_ae hcongr_m,
      ← ofReal_integral_eq_lintegral_ofReal (Lp.memLp (g_lim ym hym)).norm.integrable_sq
        (Eventually.of_forall fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hg_norm_le ym hym)
  have hF_mem : MemLp F 2 μ := by
    refine (memLp_norm_iff hF_aemeas).mp ?_
    refine (memLp_two_iff_integrable_sq hF_aemeas.norm).mpr ?_
    refine ⟨(hF_aemeas.norm.pow 2), ?_⟩
    calc ∫⁻ t, ‖‖F t‖ ^ 2‖ₑ ∂μ
        = ∫⁻ t, ENNReal.ofReal (‖F t‖ ^ 2) ∂μ := by
          refine lintegral_congr fun t => ?_
          rw [← ofReal_norm, Real.norm_of_nonneg (sq_nonneg _)]
      _ < ⊤ := hF_lint_le.trans_lt ENNReal.ofReal_lt_top
  have hF_int_le : ∫ t in Set.Ioi (0 : ℝ), ‖F t‖ ^ 2 ≤ C := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
      hF_mem.norm.integrable_sq.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hC_nn hF_lint_le
  -- Pointwise representation f z = holomorphicFourierHalfLine F z for all 0 < z.im
  have hF_rep_z : ∀ z : ℂ, 0 < z.im → f z = holomorphicFourierHalfLine F z := by
    intro z hz
    let y2 := z.im / 2
    have hy2 : 0 < y2 := half_pos hz
    let ψ : ℝ → ℂ := fun t => Complex.exp (Complex.I * (t : ℂ) * z + ((t * y2 : ℝ) : ℂ))
    have hψ_norm : ∀ t : ℝ, ‖ψ t‖ = Real.exp (-y2 * t) := by
      intro t
      dsimp [ψ]
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.add_re, Complex.mul_re, Complex.mul_im]
      dsimp [y2]; ring
    have hψ_mem2 : MemLp ψ 2 μ := by
      refine (memLp_exp_neg_mul_Ioi hy2).mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
      filter_upwards with t
      rw [hψ_norm]
    have h_split : ∀ (H : ℝ → ℂ) (t : ℝ),
        H t * Complex.exp (Complex.I * (t : ℂ) * z) =
          (H t * (Real.exp (-t * y2) : ℂ)) * ψ t := by
      intro H t
      dsimp [ψ]
      rw [Complex.ofReal_exp, mul_assoc (H t), ← Complex.exp_add]
      congr 1
      exact congr_arg Complex.exp (by push_cast; ring)
    have hlim_rhs : Tendsto (fun n : ℕ => holomorphicFourierHalfLine (Fseq n) z)
        atTop (𝓝 (holomorphicFourierHalfLine F z)) := by
      rw [Metric.tendsto_nhds]
      intro ε₀ hε₀
      let Iψ := ∫ t, ‖ψ t‖ ^ 2 ∂μ + 1
      have hIψ_pos : 0 < Iψ := by dsimp [Iψ]; positivity
      let δ := ε₀ / Iψ
      have hδ_pos : 0 < δ := div_pos hε₀ hIψ_pos
      have h_l2_lim : Tendsto (fun n : ℕ =>
          ∫ t, ‖Fseq n t * (Real.exp (-t * y2) : ℂ) - F t * (Real.exp (-t * y2) : ℂ)‖ ^ 2 ∂μ)
          atTop (𝓝 0) := by
        refine (hg_lim_int_sq y2 hy2).congr' (Eventually.of_forall fun n => ?_)
        apply integral_congr_ae
        filter_upwards [hg_compat y2 hy2] with t ht
        rw [ht]
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h_l2_lim (δ * ε₀) (mul_pos hδ_pos hε₀)
      refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      rw [dist_eq_norm]
      have hdiff_eq : holomorphicFourierHalfLine (Fseq n) z - holomorphicFourierHalfLine F z =
          ∫ t, ((Fseq n t * (Real.exp (-t * y2) : ℂ) - F t * (Real.exp (-t * y2) : ℂ)) * ψ t) ∂μ := by
        unfold holomorphicFourierHalfLine
        rw [← integral_sub (integrableOn_halfLine_of_memLp (hF_mem2 n) hz)
          (integrableOn_halfLine_of_memLp hF_mem hz)]
        congr 1 with t
        rw [h_split (Fseq n) t, h_split F t, sub_mul]
      rw [hdiff_eq]
      let dn := fun t : ℝ => Fseq n t * (Real.exp (-t * y2) : ℂ) - F t * (Real.exp (-t * y2) : ℂ)
      have hdn_mem2 : MemLp dn 2 μ := by
        refine (hGy_mem y2 hy2 n).sub ?_
        refine hF_mem.norm.mono'
          (hF_aemeas.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht_pos : 0 < t := ht
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith))
      have h_int_prod : Integrable (fun t => ‖dn t * ψ t‖) μ := by
        refine (hdn_mem2.norm.integrable_mul hψ_mem2.norm).congr ?_
        filter_upwards with t
        simp [Pi.mul_apply]
      have h_young : ∀ t : ℝ, ‖dn t * ψ t‖ ≤
          (1 / (2 * δ)) * ‖dn t‖ ^ 2 + (δ / 2) * ‖ψ t‖ ^ 2 := by
        intro t
        rw [norm_mul]
        have hsq := sq_nonneg (‖dn t‖ / Real.sqrt δ - Real.sqrt δ * ‖ψ t‖)
        have h1 : (‖dn t‖ / Real.sqrt δ) ^ 2 = ‖dn t‖ ^ 2 / δ := by
          rw [div_pow, Real.sq_sqrt hδ_pos.le]
        have h2 : (Real.sqrt δ * ‖ψ t‖) ^ 2 = δ * ‖ψ t‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hδ_pos.le]
        have h3 : 2 * (‖dn t‖ / Real.sqrt δ) * (Real.sqrt δ * ‖ψ t‖) = 2 * (‖dn t‖ * ‖ψ t‖) := by
          have hs_ne : Real.sqrt δ ≠ 0 := (Real.sqrt_pos.mpr hδ_pos).ne'
          field_simp [hs_ne]
        have hexp_sq : (‖dn t‖ / Real.sqrt δ - Real.sqrt δ * ‖ψ t‖) ^ 2 =
            (‖dn t‖ / Real.sqrt δ) ^ 2 - 2 * (‖dn t‖ / Real.sqrt δ) * (Real.sqrt δ * ‖ψ t‖) +
            (Real.sqrt δ * ‖ψ t‖) ^ 2 := sub_sq _ _
        rw [hexp_sq, h1, h2, h3] at hsq
        have hdiv_eq : ‖dn t‖ ^ 2 / δ = 2 * ((1 / (2 * δ)) * ‖dn t‖ ^ 2) := by
          field_simp [hδ_pos.ne']
        linarith
      have hdn_lt : ∫ t, ‖dn t‖ ^ 2 ∂μ < δ * ε₀ := by
        have hd := hN n hn
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at hd
        exact hd
      calc ‖∫ t, dn t * ψ t ∂μ‖
          ≤ ∫ t, ‖dn t * ψ t‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ t, ((1 / (2 * δ)) * ‖dn t‖ ^ 2 + (δ / 2) * ‖ψ t‖ ^ 2) ∂μ :=
            integral_mono h_int_prod
              ((hdn_mem2.norm.integrable_sq.const_mul _).add (hψ_mem2.norm.integrable_sq.const_mul _))
              h_young
        _ = (1 / (2 * δ)) * (∫ t, ‖dn t‖ ^ 2 ∂μ) + (δ / 2) * (∫ t, ‖ψ t‖ ^ 2 ∂μ) := by
            rw [integral_add (hdn_mem2.norm.integrable_sq.const_mul _)
              (hψ_mem2.norm.integrable_sq.const_mul _), integral_const_mul, integral_const_mul]
        _ < (1 / (2 * δ)) * (δ * ε₀) + (δ / 2) * Iψ := by
            have hlt1 : (1 / (2 * δ)) * (∫ t, ‖dn t‖ ^ 2 ∂μ) < (1 / (2 * δ)) * (δ * ε₀) :=
              mul_lt_mul_of_pos_left hdn_lt (by positivity)
            have hlt2 : (δ / 2) * (∫ t, ‖ψ t‖ ^ 2 ∂μ) < (δ / 2) * Iψ :=
              mul_lt_mul_of_pos_left (by dsimp [Iψ]; linarith) (by positivity)
            linarith
        _ = ε₀ := by
            dsimp [δ]
            field_simp [hδ_pos.ne', hIψ_pos.ne']
            ring
    have hlim_lhs : Tendsto (fun n : ℕ => pwDamped f (εseq n) z) atTop (𝓝 (f z)) := by
      have h_eps0 : Tendsto (fun n : ℕ => (εseq n : ℂ)) atTop (𝓝 0) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
      have h_denom : Tendsto (fun n : ℕ => 1 - Complex.I * (εseq n : ℂ) * z) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.sub ((tendsto_const_nhds.mul h_eps0).mul tendsto_const_nhds)
      simpa [pwDamped, pwDamp] using tendsto_const_nhds.mul (h_denom.inv₀ one_ne_zero)
    have hlim_lhs' : Tendsto (fun n : ℕ => holomorphicFourierHalfLine (Fseq n) z) atTop (𝓝 (f z)) :=
      hlim_lhs.congr (fun n => hF_rep n z hz)
    exact tendsto_nhds_unique hlim_lhs' hlim_rhs
  -- Exact norm equality ∫_{Ioi 0} ‖F‖² = C via 19.1 + IsLeast
  have hC_le_F : C ≤ ∫ t in Set.Ioi (0 : ℝ), ‖F t‖ ^ 2 := by
    refine hC_sup.2 ?_
    intro y hy
    have h19_1 := holomorphicFourierHalfLine_plancherel hF_mem hy
    have hcongr : (∫ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) =
        ∫ x : ℝ, ‖holomorphicFourierHalfLine F ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 := by
      congr 1 with x
      rw [hF_rep_z ((x : ℂ) + (y : ℂ) * Complex.I) (by simp [hy])]
    rw [hcongr, h19_1.2.1]
    exact h19_1.2.2
  exact ⟨F, hF_mem, hF_rep_z, le_antisymm hF_int_le hC_le_F⟩

/-- **Theorem 19.2 (`⨆` signature, RCA pp. 372–374):**
Equivalent signature of the First Paley–Wiener Theorem with `BddAbove` and explicit `⨆`. -/
theorem theorem19_2_iSup {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hL2 : ∀ y : ℝ, 0 < y → MemLp (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I)) 2 volume)
    (hbdd : BddAbove (Set.range fun y : {y : ℝ // 0 < y} =>
      (1 / (2 * Real.pi)) * ∫ x : ℝ, ‖f ((x : ℂ) + (y.1 : ℂ) * Complex.I)‖ ^ 2)) :
    let C := ⨆ y : {y : ℝ // 0 < y},
      (1 / (2 * Real.pi)) * ∫ x : ℝ, ‖f ((x : ℂ) + (y.1 : ℂ) * Complex.I)‖ ^ 2
    ∃ F : ℝ → ℂ,
      MemLp F 2 (volume.restrict (Set.Ioi (0 : ℝ))) ∧
      (∀ z : ℂ, 0 < z.im → f z = holomorphicFourierHalfLine F z) ∧
      ∫ t in Set.Ioi (0 : ℝ), ‖F t‖ ^ 2 = C := by
  have : Nonempty {y : ℝ // 0 < y} := ⟨⟨1, one_pos⟩⟩
  refine theorem19_2 hf hL2 ⟨?_, ?_⟩
  · intro y hy
    exact le_ciSup hbdd ⟨y, hy⟩
  · intro M hM
    exact ciSup_le fun y => hM y.1 y.2

end Node19_2



/-! ## Analytic Uniqueness Helpers (used in §§19.3–19.5, 19.9, 19.11) -/

/-- If `f` is holomorphic on a connected open set `Ω ⊆ ℂ` and all iterated derivatives of `f`
vanish at some `z₀ ∈ Ω`, then `f` vanishes identically on `Ω`. -/
lemma holomorphic_eq_zero_of_iteratedDeriv_eq_zero {Ω : Set ℂ} {f : ℂ → ℂ} {z₀ : ℂ}
    (hΩ_open : IsOpen Ω) (hΩ_conn : IsPreconnected Ω)
    (hf : DifferentiableOn ℂ f Ω) (hz₀ : z₀ ∈ Ω)
    (hderiv : ∀ n : ℕ, iteratedDeriv n f z₀ = 0) :
    ∀ z ∈ Ω, f z = 0 := by
  have han : AnalyticOnNhd ℂ f Ω := hf.analyticOnNhd hΩ_open
  have han₀ : AnalyticAt ℂ f z₀ := han z₀ hz₀
  have hord_ge : ∀ n : ℕ, (n : ℕ∞) ≤ analyticOrderAt f z₀ := fun n =>
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han₀).mpr fun i _ => hderiv i
  have hord_top : analyticOrderAt f z₀ = ⊤ := by
    by_contra hne
    let m : ℕ := (analyticOrderAt f z₀).toNat
    have hm : (m : ℕ∞) = analyticOrderAt f z₀ := ENat.natCast_toNat hne
    have hle : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := hm ▸ hord_ge (m + 1)
    exact Nat.not_succ_le_self m (Nat.cast_le.mp hle)
  have hev : f =ᶠ[𝓝 z₀] 0 := analyticOrderAt_eq_top.mp hord_top
  exact fun z hz => han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩ_conn hz₀ hev hz

/-- If two functions holomorphic on a connected open set `Ω ⊆ ℂ` agree on a nonempty open
intersection `Ω ∩ U`, then they agree on all of `Ω`. -/
lemma eqOn_of_differentiableOn_of_eqOn_open {Ω U : Set ℂ} {f g : ℂ → ℂ}
    (hΩ_open : IsOpen Ω) (hΩ_conn : IsPreconnected Ω)
    (hf : DifferentiableOn ℂ f Ω) (hg : DifferentiableOn ℂ g Ω)
    (hU_open : IsOpen U) (hne : (Ω ∩ U).Nonempty) (heq : Set.EqOn f g (Ω ∩ U)) :
    Set.EqOn f g Ω := by
  obtain ⟨z₀, hz₀Ω, hz₀U⟩ := hne
  have han : AnalyticOnNhd ℂ (f - g) Ω := (hf.sub hg).analyticOnNhd hΩ_open
  have hev : f - g =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [(hΩ_open.inter hU_open).mem_nhds ⟨hz₀Ω, hz₀U⟩] with z hz
    simp [Pi.sub_apply, heq hz]
  intro z hz
  exact sub_eq_zero.mp (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩ_conn hz₀Ω hev hz)

/-- Two entire functions that agree at every real number agree on all of `ℂ`. -/
lemma entire_eq_of_eq_on_reals {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hreal : ∀ x : ℝ, f x = g x) :
    ∀ z : ℂ, f z = g z := by
  have han_f : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have han_g : AnalyticOnNhd ℂ g Set.univ := hg.differentiableOn.analyticOnNhd isOpen_univ
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z := by
    let u : ℕ → ℂ := fun n => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
    have hu_lim : Tendsto u atTop (𝓝 (0 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
    have hu_nhds : Tendsto u atTop (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hu_lim, Eventually.of_forall fun n => ?_⟩
      dsimp [u]
      exact Complex.ofReal_ne_zero.mpr (by positivity)
    exact hu_nhds.frequently ((Eventually.of_forall fun n => hreal _).frequently)
  intro z
  exact han_f.eqOn_of_preconnected_of_frequently_eq han_g isPreconnected_univ
    (Set.mem_univ (0 : ℂ)) hfreq (Set.mem_univ z)

/-! ## §§19.3–19.5: Second Paley–Wiener Theorem, Ray-Laplace Continuation, & Uniqueness (RCA pp. 375–377) -/

/-- Rudin's ray Laplace transform along ray angle `θ` (RCA p. 375, eq. (3)):
`Φ_θ(w) = ∫_0^∞ f(r e^{i θ}) exp(-w r e^{i θ}) e^{i θ} dr`. -/
def rayLaplace (f : ℂ → ℂ) (θ : ℝ) (w : ℂ) : ℂ :=
  ∫ r in Set.Ioi (0 : ℝ),
    f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
      Complex.exp (-w * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
      Complex.exp ((θ : ℂ) * Complex.I)

/-- Open half-plane `Π_θ = {w ∈ ℂ : Re(w e^{i θ}) > A}` on which `rayLaplace f θ` converges
absolutely for entire `f` satisfying `|f(z)| ≤ C exp(A |z|)` (RCA p. 375). -/
def rayHalfPlane (A θ : ℝ) : Set ℂ :=
  {w : ℂ | A < (w * Complex.exp ((θ : ℂ) * Complex.I)).re}

/-- The slit complex plane `ℂ \ [-A i, A i]` on which the ray Laplace transforms glue to a single
holomorphic function in Remark 19.4 (RCA p. 376). -/
def slitPlane (A : ℝ) : Set ℂ :=
  {w : ℂ | ¬ (w.re = 0 ∧ w.im ∈ Set.Icc (-A) A)}

/-- Explicit glued Laplace transform on `ℂ \ [-A i, A i]` (RCA §§19.3–19.4). -/
def gluedLaplace (A : ℝ) (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  if 0 < w.re then rayLaplace f 0 w
  else if w.re < 0 then rayLaplace f Real.pi w
  else if w.im < -A then rayLaplace f (Real.pi / 2) w
  else rayLaplace f (-(Real.pi / 2)) w

section Node19_3_4

private lemma isOpen_rayHalfPlane (A θ : ℝ) : IsOpen (rayHalfPlane A θ) :=
  isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_id.mul continuous_const))

private lemma isPreconnected_rayHalfPlane (A θ : ℝ) : IsPreconnected (rayHalfPlane A θ) := by
  let eθ : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hlin : IsLinearMap ℝ (fun w : ℂ => (w * eθ).re) :=
    { map_add := fun x y => by simp [add_mul]
      map_smul := fun c x => by simp [Complex.real_smul, mul_assoc] }
  exact (convex_halfSpace_gt hlin A).isPreconnected

private lemma isOpen_slitPlane (A : ℝ) : IsOpen (slitPlane A) := by
  have heq : slitPlane A =
      ({w : ℂ | w.re = 0} ∩ (Complex.im ⁻¹' Set.Icc (-A) A))ᶜ := by
    ext w; simp [slitPlane]
  rw [heq]
  exact ((isClosed_eq Complex.continuous_re continuous_const).inter
    (isClosed_Icc.preimage Complex.continuous_im)).isOpen_compl

private lemma norm_exp_theta_I (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

private lemma re_mul_exp_theta_I (w : ℂ) (θ : ℝ) :
    (w * Complex.exp ((θ : ℂ) * Complex.I)).re =
      w.re * Real.cos θ - w.im * Real.sin θ := by
  rw [Complex.exp_mul_I]
  simp [Complex.mul_re, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im]

private lemma rayLaplace_zero_eq (f : ℂ → ℂ) (w : ℂ) :
    rayLaplace f 0 w = holomorphicFourierHalfLine (fun r : ℝ => f r) (Complex.I * w) := by
  unfold rayLaplace holomorphicFourierHalfLine
  congr 1 with r
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  congr 1
  exact congr_arg Complex.exp (by ring_nf; simp [Complex.I_sq])

private lemma rayLaplace_pi_eq (f : ℂ → ℂ) (w : ℂ) :
    rayLaplace f Real.pi w =
      -holomorphicFourierHalfLine (fun r : ℝ => f (-(r : ℂ))) (-Complex.I * w) := by
  unfold rayLaplace holomorphicFourierHalfLine
  rw [← integral_neg]
  congr 1 with r
  rw [Complex.exp_pi_mul_I]
  have hexp : -w * (r : ℂ) * (-1 : ℂ) = Complex.I * (r : ℂ) * (-Complex.I * w) := by
    ring_nf; simp [Complex.I_sq]
  have hr : (r : ℂ) * (-1 : ℂ) = -(r : ℂ) := by ring
  rw [hr, hexp]
  ring

private lemma differentiableOn_rayLaplace_zero {f : ℂ → ℂ}
    (hL2 : MemLp (fun x : ℝ => f x) 2 volume) :
    DifferentiableOn ℂ (rayLaplace f 0) {w : ℂ | 0 < w.re} := by
  have hmem : MemLp (fun r : ℝ => f r) 2 (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hL2.restrict (Set.Ioi (0 : ℝ))
  have hdiff := differentiableOn_holomorphicFourierHalfLine hmem
  have hcomp : DifferentiableOn ℂ
      (fun w : ℂ => holomorphicFourierHalfLine (fun r : ℝ => f r) (Complex.I * w))
      {w : ℂ | 0 < w.re} := by
    refine hdiff.comp (Differentiable.differentiableOn (by fun_prop)) ?_
    intro w hw
    change 0 < (Complex.I * w).im
    simpa [Complex.mul_im] using hw
  exact hcomp.congr fun w _ => rayLaplace_zero_eq f w

private lemma differentiableOn_rayLaplace_pi {f : ℂ → ℂ}
    (hL2 : MemLp (fun x : ℝ => f x) 2 volume) :
    DifferentiableOn ℂ (rayLaplace f Real.pi) {w : ℂ | w.re < 0} := by
  have hneg_L2 : MemLp (fun r : ℝ => f (-(r : ℂ))) 2 volume := by
    have h := hL2.comp_measurePreserving (Measure.measurePreserving_neg volume)
    exact h.ae_eq (Eventually.of_forall fun r => by simp)
  have hmem : MemLp (fun r : ℝ => f (-(r : ℂ))) 2 (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hneg_L2.restrict (Set.Ioi (0 : ℝ))
  have hdiff := differentiableOn_holomorphicFourierHalfLine hmem
  have hcomp : DifferentiableOn ℂ
      (fun w : ℂ => -holomorphicFourierHalfLine (fun r : ℝ => f (-(r : ℂ))) (-Complex.I * w))
      {w : ℂ | w.re < 0} := by
    refine DifferentiableOn.neg ?_
    refine hdiff.comp (Differentiable.differentiableOn (by fun_prop)) ?_
    intro w hw
    change 0 < (-Complex.I * w).im
    have him : (-Complex.I * w).im = -w.re := by simp [Complex.mul_im]
    rw [him]
    linarith [show w.re < 0 from hw]
  exact hcomp.congr fun w _ => rayLaplace_pi_eq f w

private lemma r_le_const_mul_exp {δ r : ℝ} (hδ : 0 < δ) (_hr : 0 ≤ r) :
    r ≤ (2 / δ) * Real.exp ((δ / 2) * r) := by
  have h1 : (δ / 2) * r + 1 ≤ Real.exp ((δ / 2) * r) := Real.add_one_le_exp ((δ / 2) * r)
  have h2 : (δ / 2) * r ≤ Real.exp ((δ / 2) * r) := by linarith
  have hmul := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 / δ by positivity)
  have hcancel : (2 / δ) * ((δ / 2) * r) = r := by field_simp [hδ.ne']
  rwa [hcancel] at hmul

private lemma integrableOn_rayLaplace_integrand {A C : ℝ} {f : ℂ → ℂ}
    (hf_cont : Continuous f) (hbound : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * ‖z‖))
    (θ : ℝ) {w : ℂ} (hw : w ∈ rayHalfPlane A θ) :
    IntegrableOn
      (fun r : ℝ =>
        f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp (-w * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp ((θ : ℂ) * Complex.I))
      (Set.Ioi (0 : ℝ)) volume := by
  let eθ : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  let δ : ℝ := (w * eθ).re - A
  have hδ : 0 < δ := sub_pos.mpr hw
  have hdom : IntegrableOn (fun r : ℝ => C * Real.exp (-δ * r)) (Set.Ioi (0 : ℝ)) volume :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul C
  have hcont : Continuous (fun r : ℝ =>
      f ((r : ℂ) * eθ) * Complex.exp (-w * (r : ℂ) * eθ) * eθ) :=
    ((hf_cont.comp (Complex.continuous_ofReal.mul continuous_const)).mul (by fun_prop)).mul
      continuous_const
  refine hdom.mono' hcont.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr_pos : 0 < r := hr
  rw [norm_mul, norm_mul, norm_exp_theta_I, mul_one, Complex.norm_exp]
  have hnorm_re : ‖(r : ℂ) * eθ‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr_pos.le, norm_exp_theta_I, mul_one]
  have hre : (-w * (r : ℂ) * eθ).re = -r * (w * eθ).re := by
    have : -w * (r : ℂ) * eθ = -(r : ℂ) * (w * eθ) := by ring
    rw [this, Complex.mul_re]
    simp
  calc ‖f ((r : ℂ) * eθ)‖ * Real.exp (-w * (r : ℂ) * eθ).re
      ≤ (C * Real.exp (A * r)) * Real.exp (-r * (w * eθ).re) := by
        rw [hre]
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        have hb := hbound ((r : ℂ) * eθ)
        rwa [hnorm_re] at hb
    _ = C * Real.exp (-δ * r) := by
        rw [mul_assoc, ← Real.exp_add]
        exact congr_arg (C * ·) (congr_arg Real.exp (by dsimp [δ]; ring))

/-- `rayLaplace f θ` is holomorphic on `rayHalfPlane A θ`. -/
lemma differentiableOn_rayLaplace {A C : ℝ} (hC : 0 < C) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hbound : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * ‖z‖)) (θ : ℝ) :
    DifferentiableOn ℂ (rayLaplace f θ) (rayHalfPlane A θ) := by
  intro w₀ hw₀
  let eθ : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  let σ₀ : ℝ := (w₀ * eθ).re
  let δ : ℝ := (σ₀ - A) / 2
  have hδ : 0 < δ := half_pos (sub_pos.mpr hw₀)
  let μ := volume.restrict (Set.Ioi (0 : ℝ))
  let F_int : ℂ → ℝ → ℂ := fun w r =>
    f ((r : ℂ) * eθ) * Complex.exp (-w * (r : ℂ) * eθ) * eθ
  let F'_int : ℂ → ℝ → ℂ := fun w r =>
    f ((r : ℂ) * eθ) * ((-(r : ℂ) * eθ) * Complex.exp (-w * (r : ℂ) * eθ)) * eθ
  let bound : ℝ → ℝ := fun r => (2 * C / δ) * Real.exp (-(δ / 2) * r)
  have hball_re : ∀ w ∈ Metric.ball w₀ δ, A + δ ≤ (w * eθ).re := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hdiff : ((w - w₀) * eθ).re ≥ -‖(w - w₀) * eθ‖ := neg_le_of_abs_le (Complex.abs_re_le_norm _)
    have hnorm : ‖(w - w₀) * eθ‖ = ‖w - w₀‖ := by rw [norm_mul, norm_exp_theta_I, mul_one]
    have hexp_re : (w * eθ).re = σ₀ + ((w - w₀) * eθ).re := by
      dsimp [σ₀]; rw [sub_mul, Complex.sub_re]; ring
    dsimp [δ] at hw ⊢
    linarith
  have hball_mem : ∀ w ∈ Metric.ball w₀ δ, w ∈ rayHalfPlane A θ := fun w hw => by
    have := hball_re w hw
    change A < (w * eθ).re
    linarith
  have hF_meas : ∀ᶠ w in 𝓝 w₀, AEStronglyMeasurable (F_int w) μ := by
    filter_upwards [Metric.ball_mem_nhds w₀ hδ] with w hw
    exact (integrableOn_rayLaplace_integrand hf.continuous hbound θ (hball_mem w hw)).aestronglyMeasurable
  have hF_int : Integrable (F_int w₀) μ :=
    integrableOn_rayLaplace_integrand hf.continuous hbound θ hw₀
  have hF'_meas : AEStronglyMeasurable (F'_int w₀) μ := by
    have hc : Continuous (F'_int w₀) := by
      dsimp [F'_int]
      exact ((hf.continuous.comp (Complex.continuous_ofReal.mul continuous_const)).mul
        ((by fun_prop : Continuous fun r : ℝ => -(r : ℂ) * eθ).mul (by fun_prop))).mul continuous_const
    exact hc.aestronglyMeasurable
  have h_lip : ∀ᵐ r ∂μ, ∀ w ∈ Metric.ball w₀ δ, ‖F'_int w r‖ ≤ bound r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr w hw
    have hr_pos : 0 < r := hr
    have hre_ge := hball_re w hw
    dsimp [F'_int, bound]
    rw [norm_mul, norm_mul, norm_mul, norm_exp_theta_I, mul_one, Complex.norm_exp]
    have hnorm_re : ‖(r : ℂ) * eθ‖ = r := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr_pos.le, norm_exp_theta_I, mul_one]
    have hnorm_neg_re : ‖-(r : ℂ) * eθ‖ = r := by
      rw [neg_mul, norm_neg, hnorm_re]
    have hre_val : (-w * (r : ℂ) * eθ).re = -r * (w * eθ).re := by
      have : -w * (r : ℂ) * eθ = -(r : ℂ) * (w * eθ) := by ring
      rw [this, Complex.mul_re]; simp
    rw [hnorm_neg_re, hre_val]
    have hf_le : ‖f ((r : ℂ) * eθ)‖ ≤ C * Real.exp (A * r) := by
      have hb := hbound ((r : ℂ) * eθ)
      rwa [hnorm_re] at hb
    have hexp_le : Real.exp (-r * (w * eθ).re) ≤ Real.exp (-r * (A + δ)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hr_le : r ≤ (2 / δ) * Real.exp ((δ / 2) * r) := r_le_const_mul_exp hδ hr_pos.le
    calc ‖f ((r : ℂ) * eθ)‖ * (r * Real.exp (-r * (w * eθ).re))
        ≤ (C * Real.exp (A * r)) * (((2 / δ) * Real.exp ((δ / 2) * r)) * Real.exp (-r * (A + δ))) := by
          refine mul_le_mul hf_le (mul_le_mul hr_le hexp_le (Real.exp_pos _).le (by positivity))
            (by positivity) (by positivity)
      _ = (2 * C / δ) * (Real.exp (A * r) * Real.exp ((δ / 2) * r) * Real.exp (-r * (A + δ))) := by ring
      _ = (2 * C / δ) * Real.exp (-(δ / 2) * r) := by
          rw [← Real.exp_add, ← Real.exp_add]
          exact congr_arg ((2 * C / δ) * ·) (congr_arg Real.exp (by ring))
  have h_bound_int : Integrable bound μ :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul (2 * C / δ)
  have h_diff : ∀ᵐ r ∂μ, ∀ w ∈ Metric.ball w₀ δ, HasDerivAt (fun z => F_int z r) (F'_int w r) w := by
    filter_upwards with r w _
    dsimp [F_int, F'_int]
    have h1 : HasDerivAt (fun z : ℂ => -z * (r : ℂ) * eθ) (-(r : ℂ) * eθ) w :=
      (((hasDerivAt_id w).neg.mul_const (r : ℂ)).mul_const eθ).congr_deriv (by ring)
    have h2 : HasDerivAt (fun z : ℂ => Complex.exp (-z * (r : ℂ) * eθ))
        ((-(r : ℂ) * eθ) * Complex.exp (-w * (r : ℂ) * eθ)) w :=
      h1.cexp.congr_deriv (by ring)
    exact (h2.const_mul (f ((r : ℂ) * eθ))).mul_const eθ
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds w₀ hδ) hF_meas hF_int hF'_meas h_lip h_bound_int h_diff
  exact hmain.2.differentiableAt.differentiableWithinAt

private lemma sector_re_ge {θ₁ θ₂ σ : ℝ} (hlt : θ₁ < θ₂) (hpi : θ₂ - θ₁ < Real.pi)
    (hσ : 0 < σ) {w : ℂ}
    (hw₁ : σ ≤ (w * Complex.exp ((θ₁ : ℂ) * Complex.I)).re)
    (hw₂ : σ ≤ (w * Complex.exp ((θ₂ : ℂ) * Complex.I)).re)
    {θ : ℝ} (hθ : θ ∈ Set.Icc θ₁ θ₂) :
    σ ≤ (w * Complex.exp ((θ : ℂ) * Complex.I)).re := by
  have hΔ_pos : 0 < θ₂ - θ₁ := sub_pos.mpr hlt
  have hsinΔ_pos : 0 < Real.sin (θ₂ - θ₁) := Real.sin_pos_of_pos_of_lt_pi hΔ_pos hpi
  have hsin₁_nn : 0 ≤ Real.sin (θ₂ - θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hθ.2) (by linarith [hθ.1])
  have hsin₂_nn : 0 ≤ Real.sin (θ - θ₁) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hθ.1) (by linarith [hθ.2])
  have h_id : Real.sin (θ₂ - θ₁) * (w * Complex.exp ((θ : ℂ) * Complex.I)).re =
      Real.sin (θ₂ - θ) * (w * Complex.exp ((θ₁ : ℂ) * Complex.I)).re +
      Real.sin (θ - θ₁) * (w * Complex.exp ((θ₂ : ℂ) * Complex.I)).re := by
    rw [re_mul_exp_theta_I, re_mul_exp_theta_I, re_mul_exp_theta_I,
      Real.sin_sub, Real.sin_sub, Real.sin_sub]
    ring
  have hsum_sin : Real.sin (θ₂ - θ₁) ≤ Real.sin (θ₂ - θ) + Real.sin (θ - θ₁) := by
    let h := (θ₂ - θ₁) / 2
    let d := θ - (θ₁ + θ₂) / 2
    have hh_pos : 0 < h := half_pos hΔ_pos
    have hh_lt : h < Real.pi / 2 := by dsimp [h]; linarith
    have hd_abs : |d| ≤ h := abs_le.mpr ⟨by dsimp [d, h]; linarith [hθ.1],
      by dsimp [d, h]; linarith [hθ.2]⟩
    have hcos_le : Real.cos h ≤ Real.cos d := by
      rw [← Real.cos_abs d]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg d) (by linarith [Real.pi_pos]) hd_abs
    have hsin_h : 0 < Real.sin h := Real.sin_pos_of_pos_of_lt_pi hh_pos (by linarith [Real.pi_pos])
    have heq_lhs : Real.sin (θ₂ - θ₁) = 2 * Real.sin h * Real.cos h := by
      have : θ₂ - θ₁ = 2 * h := by dsimp [h]; ring
      rw [this, Real.sin_two_mul]
    have heq_rhs : Real.sin (θ₂ - θ) + Real.sin (θ - θ₁) = 2 * Real.sin h * Real.cos d := by
      have h1 : θ₂ - θ = h - d := by dsimp [h, d]; ring
      have h2 : θ - θ₁ = h + d := by dsimp [h, d]; ring
      rw [h1, h2, Real.sin_sub, Real.sin_add]
      ring
    rw [heq_lhs, heq_rhs]
    nlinarith
  have hineq : Real.sin (θ₂ - θ₁) * σ ≤
      Real.sin (θ₂ - θ₁) * (w * Complex.exp ((θ : ℂ) * Complex.I)).re := by
    rw [h_id]
    calc Real.sin (θ₂ - θ₁) * σ
        ≤ (Real.sin (θ₂ - θ) + Real.sin (θ - θ₁)) * σ :=
          mul_le_mul_of_nonneg_right hsum_sin hσ.le
      _ = Real.sin (θ₂ - θ) * σ + Real.sin (θ - θ₁) * σ := add_mul _ _ _
      _ ≤ Real.sin (θ₂ - θ) * (w * Complex.exp ((θ₁ : ℂ) * Complex.I)).re +
          Real.sin (θ - θ₁) * (w * Complex.exp ((θ₂ : ℂ) * Complex.I)).re :=
          add_le_add (mul_le_mul_of_nonneg_left hw₁ hsin₁_nn)
            (mul_le_mul_of_nonneg_left hw₂ hsin₂_nn)
  exact le_of_mul_le_mul_left hineq hsinΔ_pos

private def raySectorIntegrand (f : ℂ → ℂ) (w u : ℂ) : ℂ :=
  f (Complex.exp u) * Complex.exp (-w * Complex.exp u) * Complex.exp u

private lemma differentiable_raySectorIntegrand {f : ℂ → ℂ} (hf : Differentiable ℂ f) (w : ℂ) :
    Differentiable ℂ (raySectorIntegrand f w) := by
  unfold raySectorIntegrand
  exact ((hf.comp Complex.differentiable_exp).mul
    (Complex.differentiable_exp.comp (Complex.differentiable_exp.const_mul (-w)))).mul
    Complex.differentiable_exp

private lemma rayLaplace_eq_horiz_lim {A C : ℝ} (hA : 0 < A) (hC : 0 < C) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hbound : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * ‖z‖))
    (θ : ℝ) {w : ℂ} (hwθ : w ∈ rayHalfPlane A θ) :
    Tendsto
      (fun k : ℕ => ∫ ρ in -((k : ℝ) + 1)..((k : ℝ) + 1),
        raySectorIntegrand f w ((ρ : ℂ) + (θ : ℂ) * Complex.I))
      atTop (𝓝 (rayLaplace f θ w)) := by
  have hh_cont : Continuous (fun r : ℝ =>
      f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
        Complex.exp (-w * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
        Complex.exp ((θ : ℂ) * Complex.I)) :=
    ((hf.continuous.comp (Complex.continuous_ofReal.mul continuous_const)).mul (by fun_prop)).mul
      continuous_const
  have hh_int : IntegrableOn
      (fun r : ℝ =>
        f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp (-w * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp ((θ : ℂ) * Complex.I))
      (Set.Ioi (0 : ℝ)) volume :=
    integrableOn_rayLaplace_integrand hf.continuous hbound θ hwθ
  have h_sub_eq : ∀ k : ℕ,
      (∫ ρ in -((k : ℝ) + 1)..((k : ℝ) + 1),
        raySectorIntegrand f w ((ρ : ℂ) + (θ : ℂ) * Complex.I)) =
        (∫ r in (0 : ℝ)..Real.exp ((k : ℝ) + 1),
          f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
            Complex.exp (-w * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
            Complex.exp ((θ : ℂ) * Complex.I)) -
        (∫ r in (0 : ℝ)..Real.exp (-((k : ℝ) + 1)),
          f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
            Complex.exp (-w * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
            Complex.exp ((θ : ℂ) * Complex.I)) := by
    intro k
    have hcomp := intervalIntegral.integral_deriv_smul_comp
      (a := -((k : ℝ) + 1)) (b := (k : ℝ) + 1)
      (f := Real.exp) (f' := Real.exp)
      (g := fun r : ℝ =>
        f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp (-w * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp ((θ : ℂ) * Complex.I))
      (fun x _ => Real.hasDerivAt_exp x)
      Real.continuous_exp.continuousOn hh_cont
    have hcongr :
        (∫ ρ in -((k : ℝ) + 1)..((k : ℝ) + 1),
          raySectorIntegrand f w ((ρ : ℂ) + (θ : ℂ) * Complex.I)) =
        ∫ ρ in -((k : ℝ) + 1)..((k : ℝ) + 1),
          Real.exp ρ •
            ((fun r : ℝ =>
              f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
                Complex.exp (-w * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
                Complex.exp ((θ : ℂ) * Complex.I)) ∘ Real.exp) ρ := by
      refine intervalIntegral.integral_congr fun ρ _ => ?_
      simp only [raySectorIntegrand, Function.comp_apply, Complex.exp_add, Complex.ofReal_exp,
        Complex.real_smul]
      ring_nf
    rw [hcongr, hcomp]
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (a := (0 : ℝ)) (b := Real.exp (-((k : ℝ) + 1))) (c := Real.exp ((k : ℝ) + 1))
      (hh_cont.intervalIntegrable (μ := volume) _ _)
      (hh_cont.intervalIntegrable (μ := volume) _ _)
    exact eq_sub_of_add_eq' hadj
  have hlim_top : Tendsto
      (fun k : ℕ => ∫ r in (0 : ℝ)..Real.exp ((k : ℝ) + 1),
        f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp (-w * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp ((θ : ℂ) * Complex.I))
      atTop (𝓝 (rayLaplace f θ w)) := by
    have hexp_top : Tendsto (fun k : ℕ => Real.exp ((k : ℝ) + 1)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hh_int hexp_top
  have hlim_bot : Tendsto
      (fun k : ℕ => ∫ r in (0 : ℝ)..Real.exp (-((k : ℝ) + 1)),
        f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp (-w * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp ((θ : ℂ) * Complex.I))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h_bd : ∀ k : ℕ,
        ‖∫ r in (0 : ℝ)..Real.exp (-((k : ℝ) + 1)),
          f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
            Complex.exp (-w * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
            Complex.exp ((θ : ℂ) * Complex.I)‖ ≤
          (C * Real.exp A) * Real.exp (-((k : ℝ) + 1)) := by
      intro k
      have he_le1 : Real.exp (-((k : ℝ) + 1)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
      have hpt : ∀ r ∈ Set.uIoc (0 : ℝ) (Real.exp (-((k : ℝ) + 1))),
          ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
            Complex.exp (-w * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
            Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ C * Real.exp A := by
        intro r hr
        rw [Set.uIoc_of_le (Real.exp_pos _).le] at hr
        rw [norm_mul, norm_mul, norm_exp_theta_I, mul_one, Complex.norm_exp]
        have hnr : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.1.le, norm_exp_theta_I, mul_one]
        have hre_neg : (-w * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re ≤ 0 := by
          have h1 : -w * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) =
              -(r : ℂ) * (w * Complex.exp ((θ : ℂ) * Complex.I)) := by ring
          rw [h1, Complex.mul_re]
          simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im]
          have hw_pos : 0 < (w * Complex.exp ((θ : ℂ) * Complex.I)).re := hA.trans hwθ
          nlinarith [hr.1]
        calc ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ *
              Real.exp (-w * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re
            ≤ (C * Real.exp (A * r)) * 1 := by
              refine mul_le_mul ?_ (Real.exp_le_one_iff.mpr hre_neg) (Real.exp_pos _).le (by positivity)
              have hb := hbound ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
              rwa [hnr] at hb
          _ ≤ C * Real.exp A := by
              rw [mul_one]
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
              have hr1 : r ≤ 1 := hr.2.trans he_le1
              nlinarith
      have hle := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      rwa [sub_zero, abs_of_pos (Real.exp_pos _)] at hle
    have h_zero : Tendsto (fun k : ℕ => (C * Real.exp A) * Real.exp (-((k : ℝ) + 1))) atTop (𝓝 0) := by
      have hbot : Tendsto (fun k : ℕ => -((k : ℝ) + 1)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have h0 := tendsto_const_nhds (x := C * Real.exp A).mul (Real.tendsto_exp_atBot.comp hbot)
      rwa [mul_zero] at h0
    exact squeeze_zero (fun _ => norm_nonneg _) h_bd h_zero
  have hsub := hlim_top.sub hlim_bot
  rw [sub_zero] at hsub
  exact hsub.congr' (Eventually.of_forall fun k => (h_sub_eq k).symm)

/-- Sector Cauchy gluing: when `|θ₁ - θ₂| < π`, `rayLaplace f θ₁` and `rayLaplace f θ₂` agree on
`rayHalfPlane A θ₁ ∩ rayHalfPlane A θ₂` (RCA p. 376). -/
lemma rayLaplace_eq_on_inter {A C : ℝ} (hA : 0 < A) (hC : 0 < C) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hbound : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * ‖z‖))
    {θ₁ θ₂ : ℝ} (hθ : |θ₁ - θ₂| < Real.pi) {w : ℂ}
    (hw₁ : w ∈ rayHalfPlane A θ₁) (hw₂ : w ∈ rayHalfPlane A θ₂) :
    rayLaplace f θ₁ w = rayLaplace f θ₂ w := by
  suffices hlt_case : ∀ {a b : ℝ}, a < b → b - a < Real.pi →
      w ∈ rayHalfPlane A a → w ∈ rayHalfPlane A b → rayLaplace f a w = rayLaplace f b w by
    rcases lt_trichotomy θ₁ θ₂ with h | rfl | h
    · exact hlt_case h (by rw [abs_sub_comm, abs_of_pos (sub_pos.mpr h)] at hθ; exact hθ) hw₁ hw₂
    · rfl
    · exact (hlt_case h (by rw [abs_of_pos (sub_pos.mpr h)] at hθ; exact hθ) hw₂ hw₁).symm
  intro a b hab hpi hwa hwb
  set σ : ℝ := min (w * Complex.exp ((a : ℂ) * Complex.I)).re
    (w * Complex.exp ((b : ℂ) * Complex.I)).re
  have hA_lt_σ : A < σ := lt_min hwa hwb
  have hσ_pos : 0 < σ := hA.trans hA_lt_σ
  set δ : ℝ := σ - A
  have hδ_pos : 0 < δ := sub_pos.mpr hA_lt_σ
  have h_sec : ∀ θ ∈ Set.Icc a b, A + δ ≤ (w * Complex.exp ((θ : ℂ) * Complex.I)).re := by
    intro θ hθ_mem
    have hAδ : A + δ = σ := by ring
    rw [hAδ]
    exact sector_re_ge hab hpi hσ_pos (min_le_left _ _) (min_le_right _ _) hθ_mem
  have hG_diff : Differentiable ℂ (raySectorIntegrand f w) :=
    differentiable_raySectorIntegrand hf w
  have h_vr : Tendsto (fun k : ℕ =>
      Complex.I • ∫ θ in a..b, raySectorIntegrand f w ((((k : ℝ) + 1 : ℝ) : ℂ) + (θ : ℂ) * Complex.I))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h_bd : ∀ k : ℕ,
        ‖Complex.I • ∫ θ in a..b,
          raySectorIntegrand f w ((((k : ℝ) + 1 : ℝ) : ℂ) + (θ : ℂ) * Complex.I)‖ ≤
          ((2 * C / δ) * Real.exp (-(δ / 2) * ((k : ℝ) + 1))) * |b - a| := by
      intro k
      rw [norm_smul, Complex.norm_I, one_mul]
      set R : ℝ := Real.exp ((k : ℝ) + 1)
      have hR_pos : 0 < R := Real.exp_pos _
      have hR_ge : (k : ℝ) + 1 ≤ R := by
        have := Real.add_one_le_exp ((k : ℝ) + 1)
        linarith
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => ?_
      rw [Set.uIoc_of_le hab.le] at hθ
      have hre_sec := h_sec θ ⟨hθ.1.le, hθ.2⟩
      have hexp_split : Complex.exp ((((k : ℝ) + 1 : ℝ) : ℂ) + (θ : ℂ) * Complex.I) =
          (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
        rw [Complex.exp_add, Complex.ofReal_exp]
      unfold raySectorIntegrand
      rw [hexp_split, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR_pos.le,
        norm_exp_theta_I, mul_one, Complex.norm_exp]
      have hnr : ‖(R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = R := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR_pos.le, norm_exp_theta_I, mul_one]
      have hre_val : (-w * ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re =
          -R * (w * Complex.exp ((θ : ℂ) * Complex.I)).re := by
        have h1 : -w * ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
            -(R : ℂ) * (w * Complex.exp ((θ : ℂ) * Complex.I)) := by ring
        rw [h1, Complex.mul_re]
        simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im]
        ring
      rw [hre_val]
      have hf_le : ‖f ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ C * Real.exp (A * R) := by
        have hb := hbound ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        rwa [hnr] at hb
      have hexp_le : Real.exp (-R * (w * Complex.exp ((θ : ℂ) * Complex.I)).re) ≤
          Real.exp (-R * (A + δ)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hR_le : R ≤ (2 / δ) * Real.exp ((δ / 2) * R) := r_le_const_mul_exp hδ_pos hR_pos.le
      calc ‖f ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ *
            Real.exp (-R * (w * Complex.exp ((θ : ℂ) * Complex.I)).re) * R
          ≤ (C * Real.exp (A * R)) * Real.exp (-R * (A + δ)) * ((2 / δ) * Real.exp ((δ / 2) * R)) := by
            refine mul_le_mul (mul_le_mul hf_le hexp_le (Real.exp_pos _).le (by positivity))
              hR_le hR_pos.le (by positivity)
        _ = (2 * C / δ) * (Real.exp (A * R) * Real.exp (-R * (A + δ)) * Real.exp ((δ / 2) * R)) := by ring
        _ = (2 * C / δ) * Real.exp (-(δ / 2) * R) := by
            rw [← Real.exp_add, ← Real.exp_add]
            exact congr_arg ((2 * C / δ) * ·) (congr_arg Real.exp (by ring))
        _ ≤ (2 * C / δ) * Real.exp (-(δ / 2) * ((k : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
    have h_zero : Tendsto
        (fun k : ℕ => ((2 * C / δ) * Real.exp (-(δ / 2) * ((k : ℝ) + 1))) * |b - a|)
        atTop (𝓝 0) := by
      have hbot : Tendsto (fun k : ℕ => -(δ / 2) * ((k : ℝ) + 1)) atTop atBot :=
        tendsto_const_nhds.neg_mul_atTop (by linarith)
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have h0 := (tendsto_const_nhds (x := 2 * C / δ).mul (Real.tendsto_exp_atBot.comp hbot)).mul_const |b - a|
      rwa [mul_zero, zero_mul] at h0
    exact squeeze_zero (fun _ => norm_nonneg _) h_bd h_zero
  have h_vl : Tendsto (fun k : ℕ =>
      Complex.I • ∫ θ in a..b, raySectorIntegrand f w (((-((k : ℝ) + 1) : ℝ) : ℂ) + (θ : ℂ) * Complex.I))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h_bd : ∀ k : ℕ,
        ‖Complex.I • ∫ θ in a..b,
          raySectorIntegrand f w (((-((k : ℝ) + 1) : ℝ) : ℂ) + (θ : ℂ) * Complex.I)‖ ≤
          ((C * Real.exp A) * Real.exp (-((k : ℝ) + 1))) * |b - a| := by
      intro k
      rw [norm_smul, Complex.norm_I, one_mul]
      set r : ℝ := Real.exp (-((k : ℝ) + 1))
      have hr_pos : 0 < r := Real.exp_pos _
      have hr_le1 : r ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => ?_
      rw [Set.uIoc_of_le hab.le] at hθ
      have hre_sec := h_sec θ ⟨hθ.1.le, hθ.2⟩
      have hexp_split : Complex.exp (((-((k : ℝ) + 1) : ℝ) : ℂ) + (θ : ℂ) * Complex.I) =
          (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
        rw [Complex.exp_add, Complex.ofReal_exp]
      unfold raySectorIntegrand
      rw [hexp_split, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr_pos.le,
        norm_exp_theta_I, mul_one, Complex.norm_exp]
      have hnr : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr_pos.le, norm_exp_theta_I, mul_one]
      have hre_neg : (-w * ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re ≤ 0 := by
        have h1 : -w * ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
            -(r : ℂ) * (w * Complex.exp ((θ : ℂ) * Complex.I)) := by ring
        rw [h1, Complex.mul_re]
        simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im]
        nlinarith
      calc ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ *
            Real.exp (-w * ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re * r
          ≤ (C * Real.exp (A * r)) * 1 * r := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul ?_ (Real.exp_le_one_iff.mpr hre_neg) (Real.exp_pos _).le (by positivity)) hr_pos.le
            have hb := hbound ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
            rwa [hnr] at hb
        _ ≤ (C * Real.exp A) * r := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC.le) hr_pos.le
    have h_zero : Tendsto
        (fun k : ℕ => ((C * Real.exp A) * Real.exp (-((k : ℝ) + 1))) * |b - a|)
        atTop (𝓝 0) := by
      have hbot : Tendsto (fun k : ℕ => -((k : ℝ) + 1)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have h0 := (tendsto_const_nhds (x := C * Real.exp A).mul (Real.tendsto_exp_atBot.comp hbot)).mul_const |b - a|
      rwa [mul_zero, zero_mul] at h0
    exact squeeze_zero (fun _ => norm_nonneg _) h_bd h_zero
  have h_rect : ∀ k : ℕ,
      ((∫ ρ in -((k : ℝ) + 1)..((k : ℝ) + 1),
          raySectorIntegrand f w ((ρ : ℂ) + (a : ℂ) * Complex.I)) -
        ∫ ρ in -((k : ℝ) + 1)..((k : ℝ) + 1),
          raySectorIntegrand f w ((ρ : ℂ) + (b : ℂ) * Complex.I)) +
      Complex.I • (∫ θ in a..b,
        raySectorIntegrand f w ((((k : ℝ) + 1 : ℝ) : ℂ) + (θ : ℂ) * Complex.I)) -
      Complex.I • (∫ θ in a..b,
        raySectorIntegrand f w (((-((k : ℝ) + 1) : ℝ) : ℂ) + (θ : ℂ) * Complex.I)) = 0 := by
    intro k
    have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (raySectorIntegrand f w) ⟨-((k : ℝ) + 1), a⟩ ⟨(k : ℝ) + 1, b⟩ hG_diff.differentiableOn
    exact hc
  have hlim_tot := (((rayLaplace_eq_horiz_lim hA hC hf hbound a hwa).sub
    (rayLaplace_eq_horiz_lim hA hC hf hbound b hwb)).add h_vr).sub h_vl
  have hlim_zero : Tendsto (fun k : ℕ =>
      (((∫ ρ in -((k : ℝ) + 1)..((k : ℝ) + 1),
          raySectorIntegrand f w ((ρ : ℂ) + (a : ℂ) * Complex.I)) -
        ∫ ρ in -((k : ℝ) + 1)..((k : ℝ) + 1),
          raySectorIntegrand f w ((ρ : ℂ) + (b : ℂ) * Complex.I)) +
      Complex.I • (∫ θ in a..b,
        raySectorIntegrand f w ((((k : ℝ) + 1 : ℝ) : ℂ) + (θ : ℂ) * Complex.I)) -
      Complex.I • (∫ θ in a..b,
        raySectorIntegrand f w (((-((k : ℝ) + 1) : ℝ) : ℂ) + (θ : ℂ) * Complex.I))))
      atTop (𝓝 0) := by
    simp_rw [h_rect]
    exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hlim_tot hlim_zero
  rw [add_zero, sub_zero] at heq
  exact sub_eq_zero.mp heq

private lemma rayHalfPlane_zero (A : ℝ) :
    rayHalfPlane A 0 = {w : ℂ | A < w.re} := by
  ext w; simp [rayHalfPlane]

private lemma rayHalfPlane_pi_div_two (A : ℝ) :
    rayHalfPlane A (Real.pi / 2) = {w : ℂ | w.im < -A} := by
  ext w
  dsimp [rayHalfPlane]
  rw [re_mul_exp_theta_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
  constructor <;> intro h <;> linarith

private lemma rayHalfPlane_neg_pi_div_two (A : ℝ) :
    rayHalfPlane A (-(Real.pi / 2)) = {w : ℂ | A < w.im} := by
  ext w
  dsimp [rayHalfPlane]
  rw [re_mul_exp_theta_I, Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg, Real.sin_pi_div_two]
  constructor <;> intro h <;> linarith

private lemma rayHalfPlane_pi (A : ℝ) :
    rayHalfPlane A Real.pi = {w : ℂ | w.re < -A} := by
  ext w
  dsimp [rayHalfPlane]
  rw [re_mul_exp_theta_I, Real.cos_pi, Real.sin_pi]
  constructor <;> intro h <;> linarith

private lemma rayLaplace_neg_pi_eq_pi (f : ℂ → ℂ) :
    rayLaplace f (-Real.pi) = rayLaplace f Real.pi := by
  ext w
  unfold rayLaplace
  have hexp : Complex.exp (((-Real.pi : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp
  simp_rw [hexp]

private lemma rayHalfPlane_subset_slitPlane {A : ℝ} (θ : ℝ) :
    rayHalfPlane A θ ⊆ slitPlane A := by
  intro w hw
  rintro ⟨hre, him⟩
  have hnorm_w : ‖w‖ = |w.im| := by
    have hw_eq : w = (w.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hre]
    conv_lhs => rw [hw_eq]
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have hle : (w * Complex.exp ((θ : ℂ) * Complex.I)).re ≤ A := by
    calc (w * Complex.exp ((θ : ℂ) * Complex.I)).re
        ≤ ‖w * Complex.exp ((θ : ℂ) * Complex.I)‖ := Complex.re_le_norm _
      _ = ‖w‖ := by rw [norm_mul, norm_exp_theta_I, mul_one]
      _ = |w.im| := hnorm_w
      _ ≤ A := abs_le.mpr him
  exact not_lt_of_ge hle hw

private lemma exp_add_int_mul_two_pi_I (θ : ℝ) (k : ℤ) :
    Complex.exp (((θ - 2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I) := by
  have hsplit : ((θ - 2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I =
      (θ : ℂ) * Complex.I - (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [hsplit, Complex.exp_sub, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow, div_one]

/-- **Remark / Theorem 19.4 (Analytic Continuation of Ray Laplace Transforms, RCA pp. 376–377):**
Under the hypotheses of Theorem 19.3, the family of ray Laplace transforms `rayLaplace f θ`
glues to a single holomorphic function `gluedLaplace A f` on `slitPlane A = ℂ \ [-A i, A i]`,
agreeing with the positive real-axis Laplace transform on `{Re w > 0}`, the negative real-axis
Laplace transform on `{Re w < 0}`, `rayLaplace f (π/2)` on `{Im w < -A}`, `rayLaplace f (-π/2)`
on `{Im w > A}`, and `rayLaplace f θ` on `rayHalfPlane A θ` for every `θ : ℝ`. -/
theorem theorem19_4 {A C : ℝ} (hA : 0 < A) (hC : 0 < C) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * ‖z‖))
    (hL2 : MemLp (fun x : ℝ => f x) 2 volume) :
    DifferentiableOn ℂ (gluedLaplace A f) (slitPlane A) ∧
    (∀ w : ℂ, 0 < w.re → gluedLaplace A f w = rayLaplace f 0 w) ∧
    (∀ w : ℂ, w.re < 0 → gluedLaplace A f w = rayLaplace f Real.pi w) ∧
    (∀ w : ℂ, w.im < -A → gluedLaplace A f w = rayLaplace f (Real.pi / 2) w) ∧
    (∀ w : ℂ, A < w.im → gluedLaplace A f w = rayLaplace f (-(Real.pi / 2)) w) ∧
    (∀ θ : ℝ, ∀ w ∈ rayHalfPlane A θ, gluedLaplace A f w = rayLaplace f θ w) := by
  have hd0 := differentiableOn_rayLaplace_zero hL2
  have hdpi := differentiableOn_rayLaplace_pi hL2
  have hdp2 := differentiableOn_rayLaplace hC hf hbound (Real.pi / 2)
  have hdnp2 := differentiableOn_rayLaplace hC hf hbound (-(Real.pi / 2))
  have hre_lin : IsLinearMap ℝ (fun w : ℂ => w.re) :=
    { map_add := Complex.add_re, map_smul := fun c w => by simp [Complex.real_smul] }
  have him_lin : IsLinearMap ℝ (fun w : ℂ => w.im) :=
    { map_add := Complex.add_im, map_smul := fun c w => by simp [Complex.real_smul] }
  -- 1. Right ∩ Down overlap
  have h_rd : ∀ w : ℂ, 0 < w.re → w.im < -A → rayLaplace f 0 w = rayLaplace f (Real.pi / 2) w := by
    intro w hw_re hw_im
    let Ω := {z : ℂ | 0 < z.re} ∩ {z : ℂ | z.im < -A}
    have hΩ_open : IsOpen Ω := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_im continuous_const)
    have hΩ_conn : IsPreconnected Ω :=
      ((convex_halfSpace_gt hre_lin 0).inter (convex_halfSpace_lt him_lin (-A))).isPreconnected
    let U := rayHalfPlane A 0
    have hne : (Ω ∩ U).Nonempty := ⟨(⟨A + 1, -(A + 1)⟩ : ℂ),
      ⟨⟨by change 0 < A + 1; linarith, by change -(A + 1) < -A; linarith⟩,
        by dsimp [U]; rw [rayHalfPlane_zero]; change A < A + 1; linarith⟩⟩
    refine eqOn_of_differentiableOn_of_eqOn_open hΩ_open hΩ_conn
      (hd0.mono Set.inter_subset_left)
      (hdp2.mono (by rw [rayHalfPlane_pi_div_two]; exact Set.inter_subset_right))
      (isOpen_rayHalfPlane A 0) hne (fun z hz => ?_) ⟨hw_re, hw_im⟩
    refine rayLaplace_eq_on_inter hA hC hf hbound ?_ hz.2 ?_
    · rw [zero_sub, abs_neg, abs_of_pos (half_pos Real.pi_pos)]
      linarith [Real.pi_pos]
    · rw [rayHalfPlane_pi_div_two]; exact hz.1.2
  -- 2. Right ∩ Up overlap
  have h_ru : ∀ w : ℂ, 0 < w.re → A < w.im → rayLaplace f 0 w = rayLaplace f (-(Real.pi / 2)) w := by
    intro w hw_re hw_im
    let Ω := {z : ℂ | 0 < z.re} ∩ {z : ℂ | A < z.im}
    have hΩ_open : IsOpen Ω := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
    have hΩ_conn : IsPreconnected Ω :=
      ((convex_halfSpace_gt hre_lin 0).inter (convex_halfSpace_gt him_lin A)).isPreconnected
    let U := rayHalfPlane A 0
    have hne : (Ω ∩ U).Nonempty := ⟨(⟨A + 1, A + 1⟩ : ℂ),
      ⟨⟨by change 0 < A + 1; linarith, by change A < A + 1; linarith⟩,
        by dsimp [U]; rw [rayHalfPlane_zero]; change A < A + 1; linarith⟩⟩
    refine eqOn_of_differentiableOn_of_eqOn_open hΩ_open hΩ_conn
      (hd0.mono Set.inter_subset_left)
      (hdnp2.mono (by rw [rayHalfPlane_neg_pi_div_two]; exact Set.inter_subset_right))
      (isOpen_rayHalfPlane A 0) hne (fun z hz => ?_) ⟨hw_re, hw_im⟩
    refine rayLaplace_eq_on_inter hA hC hf hbound ?_ hz.2 ?_
    · rw [sub_neg_eq_add, zero_add, abs_of_pos (half_pos Real.pi_pos)]
      linarith [Real.pi_pos]
    · rw [rayHalfPlane_neg_pi_div_two]; exact hz.1.2
  -- 3. Left ∩ Down overlap
  have h_ld : ∀ w : ℂ, w.re < 0 → w.im < -A → rayLaplace f Real.pi w = rayLaplace f (Real.pi / 2) w := by
    intro w hw_re hw_im
    let Ω := {z : ℂ | z.re < 0} ∩ {z : ℂ | z.im < -A}
    have hΩ_open : IsOpen Ω := (isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt Complex.continuous_im continuous_const)
    have hΩ_conn : IsPreconnected Ω :=
      ((convex_halfSpace_lt hre_lin 0).inter (convex_halfSpace_lt him_lin (-A))).isPreconnected
    let U := rayHalfPlane A Real.pi
    have hne : (Ω ∩ U).Nonempty := ⟨(⟨-(A + 1), -(A + 1)⟩ : ℂ),
      ⟨⟨by change -(A + 1) < 0; linarith, by change -(A + 1) < -A; linarith⟩,
        by dsimp [U]; rw [rayHalfPlane_pi]; change -(A + 1) < -A; linarith⟩⟩
    refine eqOn_of_differentiableOn_of_eqOn_open hΩ_open hΩ_conn
      (hdpi.mono Set.inter_subset_left)
      (hdp2.mono (by rw [rayHalfPlane_pi_div_two]; exact Set.inter_subset_right))
      (isOpen_rayHalfPlane A Real.pi) hne (fun z hz => ?_) ⟨hw_re, hw_im⟩
    refine rayLaplace_eq_on_inter hA hC hf hbound ?_ hz.2 ?_
    · have : Real.pi - Real.pi / 2 = Real.pi / 2 := by ring
      rw [this, abs_of_pos (half_pos Real.pi_pos)]
      linarith [Real.pi_pos]
    · rw [rayHalfPlane_pi_div_two]; exact hz.1.2
  -- 4. Left ∩ Up overlap (via θ = -π)
  have h_lu : ∀ w : ℂ, w.re < 0 → A < w.im → rayLaplace f Real.pi w = rayLaplace f (-(Real.pi / 2)) w := by
    intro w hw_re hw_im
    let Ω := {z : ℂ | z.re < 0} ∩ {z : ℂ | A < z.im}
    have hΩ_open : IsOpen Ω := (isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)
    have hΩ_conn : IsPreconnected Ω :=
      ((convex_halfSpace_lt hre_lin 0).inter (convex_halfSpace_gt him_lin A)).isPreconnected
    let U := rayHalfPlane A Real.pi
    have hne : (Ω ∩ U).Nonempty := ⟨(⟨-(A + 1), A + 1⟩ : ℂ),
      ⟨⟨by change -(A + 1) < 0; linarith, by change A < A + 1; linarith⟩,
        by dsimp [U]; rw [rayHalfPlane_pi]; change -(A + 1) < -A; linarith⟩⟩
    refine eqOn_of_differentiableOn_of_eqOn_open hΩ_open hΩ_conn
      (hdpi.mono Set.inter_subset_left)
      (hdnp2.mono (by rw [rayHalfPlane_neg_pi_div_two]; exact Set.inter_subset_right))
      (isOpen_rayHalfPlane A Real.pi) hne (fun z hz => ?_) ⟨hw_re, hw_im⟩
    rw [← rayLaplace_neg_pi_eq_pi]
    refine rayLaplace_eq_on_inter hA hC hf hbound ?_ ?_ ?_
    · have : -Real.pi - -(Real.pi / 2) = -(Real.pi / 2) := by ring
      rw [this, abs_neg, abs_of_pos (half_pos Real.pi_pos)]
      linarith [Real.pi_pos]
    · have : rayHalfPlane A (-Real.pi) = rayHalfPlane A Real.pi := by
        ext ζ; simp [rayHalfPlane, Complex.exp_mul_I]
      rw [this]; exact hz.2
    · rw [rayHalfPlane_neg_pi_div_two]; exact hz.1.2
  -- 5. Agreement of gluedLaplace on the 4 open half-planes
  have h_eq_r : ∀ w : ℂ, 0 < w.re → gluedLaplace A f w = rayLaplace f 0 w := by
    intro w hw; simp [gluedLaplace, hw]
  have h_eq_l : ∀ w : ℂ, w.re < 0 → gluedLaplace A f w = rayLaplace f Real.pi w := by
    intro w hw
    have hnot : ¬ (0 < w.re) := not_lt.mpr hw.le
    simp [gluedLaplace, hnot, hw]
  have h_eq_d : ∀ w : ℂ, w.im < -A → gluedLaplace A f w = rayLaplace f (Real.pi / 2) w := by
    intro w hw
    unfold gluedLaplace
    split_ifs with h1 h2
    · exact h_rd w h1 hw
    · exact h_ld w h2 hw
    · rfl
  have h_eq_u : ∀ w : ℂ, A < w.im → gluedLaplace A f w = rayLaplace f (-(Real.pi / 2)) w := by
    intro w hw
    have hnot_d : ¬ (w.im < -A) := not_lt.mpr (by linarith)
    unfold gluedLaplace
    split_ifs with h1 h2
    · exact h_ru w h1 hw
    · exact h_lu w h2 hw
    · rfl
  -- 6. Holomorphy on slitPlane A
  have h_diff_slit : DifferentiableOn ℂ (gluedLaplace A f) (slitPlane A) := by
    intro w₀ hw₀
    have hcov : 0 < w₀.re ∨ w₀.re < 0 ∨ w₀.im < -A ∨ A < w₀.im := by
      by_contra! h
      have hre0 : w₀.re = 0 := le_antisymm h.1 h.2.1
      exact hw₀ ⟨hre0, h.2.2.1, h.2.2.2⟩
    rcases hcov with hr | hl | hd | hu
    · have hnhds := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hr
      have hev : gluedLaplace A f =ᶠ[𝓝 w₀] rayLaplace f 0 := by
        filter_upwards [hnhds] with w hw; exact h_eq_r w hw
      exact ((hd0.differentiableAt hnhds).congr_of_eventuallyEq hev).differentiableWithinAt
    · have hnhds := (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hl
      have hev : gluedLaplace A f =ᶠ[𝓝 w₀] rayLaplace f Real.pi := by
        filter_upwards [hnhds] with w hw; exact h_eq_l w hw
      exact ((hdpi.differentiableAt hnhds).congr_of_eventuallyEq hev).differentiableWithinAt
    · have hnhds := (isOpen_lt Complex.continuous_im continuous_const).mem_nhds hd
      have hev : gluedLaplace A f =ᶠ[𝓝 w₀] rayLaplace f (Real.pi / 2) := by
        filter_upwards [hnhds] with w hw; exact h_eq_d w hw
      have hdp2' : DifferentiableAt ℂ (rayLaplace f (Real.pi / 2)) w₀ :=
        hdp2.differentiableAt (by rwa [rayHalfPlane_pi_div_two])
      exact (hdp2'.congr_of_eventuallyEq hev).differentiableWithinAt
    · have hnhds := (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hu
      have hev : gluedLaplace A f =ᶠ[𝓝 w₀] rayLaplace f (-(Real.pi / 2)) := by
        filter_upwards [hnhds] with w hw; exact h_eq_u w hw
      have hdnp2' : DifferentiableAt ℂ (rayLaplace f (-(Real.pi / 2))) w₀ :=
        hdnp2.differentiableAt (by rwa [rayHalfPlane_neg_pi_div_two])
      exact (hdnp2'.congr_of_eventuallyEq hev).differentiableWithinAt
  -- 7. Agreement with rayLaplace f θ on rayHalfPlane A θ for all θ : ℝ
  refine ⟨h_diff_slit, h_eq_r, h_eq_l, h_eq_d, h_eq_u, fun θ w hw => ?_⟩
  let k : ℤ := round (θ / (2 * Real.pi))
  let θ' : ℝ := θ - 2 * Real.pi * (k : ℝ)
  have hexp_eq : Complex.exp ((θ' : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) :=
    exp_add_int_mul_two_pi_I θ k
  have hray_eq : rayLaplace f θ' = rayLaplace f θ := by
    ext ζ; unfold rayLaplace; simp_rw [hexp_eq]
  have hhp_eq : rayHalfPlane A θ' = rayHalfPlane A θ := by
    ext ζ; simp [rayHalfPlane, hexp_eq]
  have habs_le : |θ'| ≤ Real.pi := by
    have hr := abs_sub_round (θ / (2 * Real.pi))
    have h2pi : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
    have hmul := mul_le_mul_of_nonneg_left hr h2pi.le
    have hrew : 2 * Real.pi * |θ / (2 * Real.pi) - (k : ℝ)| = |θ'| := by
      calc 2 * Real.pi * |θ / (2 * Real.pi) - (k : ℝ)|
          = |2 * Real.pi| * |θ / (2 * Real.pi) - (k : ℝ)| := by rw [abs_of_pos h2pi]
        _ = |2 * Real.pi * (θ / (2 * Real.pi) - (k : ℝ))| := (abs_mul _ _).symm
        _ = |θ'| := congr_arg abs (by dsimp [θ']; field_simp [h2pi.ne'])
    rw [hrew] at hmul
    linarith
  rcases lt_or_eq_of_le habs_le with hlt_pi | heq_pi
  · -- |θ'| < π: connect rayHalfPlane A θ' with rayHalfPlane A 0
    have hcos_gt : -1 < Real.cos θ' := by
      rw [← Real.cos_abs θ', ← Real.cos_pi]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg θ') le_rfl hlt_pi
    have h1cos_pos : 0 < 1 + Real.cos θ' := by linarith
    let M : ℝ := (A + 1) / (1 + Real.cos θ')
    have hM_pos : 0 < M := div_pos (by linarith) h1cos_pos
    let w₁ : ℂ := (M : ℂ) * (1 + Complex.exp (-(θ' : ℂ) * Complex.I))
    have hw₁_0 : w₁ ∈ rayHalfPlane A 0 := by
      rw [rayHalfPlane_zero]
      change A < w₁.re
      have hre1 : w₁.re = M * (1 + Real.cos θ') := by
        dsimp [w₁]
        have : -(θ' : ℂ) * Complex.I = ((-θ' : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [this, Complex.exp_mul_I]
        simp [Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_im]
      have hM_mul : M * (1 + Real.cos θ') = A + 1 := div_mul_cancel₀ (A + 1) h1cos_pos.ne'
      linarith
    have hw₁_θ' : w₁ ∈ rayHalfPlane A θ' := by
      change A < (w₁ * Complex.exp ((θ' : ℂ) * Complex.I)).re
      have hprod : w₁ * Complex.exp ((θ' : ℂ) * Complex.I) =
          (M : ℂ) * (Complex.exp ((θ' : ℂ) * Complex.I) + 1) := by
        dsimp [w₁]
        rw [mul_assoc, add_mul, one_mul, ← Complex.exp_add]
        simp [mul_add]
      have hre2 : ((M : ℂ) * (Complex.exp ((θ' : ℂ) * Complex.I) + 1)).re =
          M * (1 + Real.cos θ') := by
        rw [Complex.exp_mul_I]
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.one_re, Complex.I_re, Complex.I_im,
          Complex.cos_ofReal_re, Complex.sin_ofReal_im]
        ring
      have hM_mul : M * (1 + Real.cos θ') = A + 1 := div_mul_cancel₀ (A + 1) h1cos_pos.ne'
      rw [hprod, hre2, hM_mul]
      linarith
    have hw' : w ∈ rayHalfPlane A θ' := by rwa [hhp_eq]
    have heq_on := eqOn_of_differentiableOn_of_eqOn_open
      (isOpen_rayHalfPlane A θ') (isPreconnected_rayHalfPlane A θ')
      (h_diff_slit.mono (rayHalfPlane_subset_slitPlane θ'))
      (differentiableOn_rayLaplace hC hf hbound θ')
      (isOpen_rayHalfPlane A 0) ⟨w₁, hw₁_θ', hw₁_0⟩
      (fun z hz => by
        have hz2 := hz.2
        rw [rayHalfPlane_zero] at hz2
        have hz_re : 0 < z.re := hA.trans hz2
        rw [h_eq_r z hz_re]
        exact (rayLaplace_eq_on_inter hA hC hf hbound (by simpa using hlt_pi) hz.1 hz.2).symm)
      hw'
    rwa [hray_eq] at heq_on
  · -- |θ'| = π: exp(θ' * I) = -1 = exp(π * I)
    have hexp_neg1 : Complex.exp ((θ' : ℂ) * Complex.I) = -1 := by
      rcases eq_or_eq_neg_of_abs_eq heq_pi with h | h
      · rw [h, Complex.exp_pi_mul_I]
      · rw [h, Complex.exp_mul_I]; simp
    have hexp_θ : Complex.exp ((θ : ℂ) * Complex.I) = -1 := hexp_eq.symm.trans hexp_neg1
    have hw_re_lt : w.re < 0 := by
      have : A < (w * (-1 : ℂ)).re := by simpa [rayHalfPlane, hexp_θ] using hw
      simp at this
      linarith
    rw [h_eq_l w hw_re_lt]
    unfold rayLaplace
    simp_rw [hexp_θ, Complex.exp_pi_mul_I]

/-- **Theorem 19.3 (Second Paley–Wiener Theorem, RCA pp. 375–376):**
Let `A > 0` and `C > 0`. Suppose `f : ℂ → ℂ` is entire (`Differentiable ℂ f`), satisfies
`‖f z‖ ≤ C * exp(A * ‖z‖)` for every `z : ℂ`, and its restriction `x ↦ f x` belongs to `L²(ℝ)`.
Then there exists `F ∈ L²(-A, A)` (both on `Set.Ioo (-A) A` and `Set.Icc (-A) A` since `{±A}`
have measure zero) such that `f(z) = ∫_{-A}^A F(t) exp(i t z) dt` for every `z : ℂ`. -/
theorem theorem19_3 {A C : ℝ} (hA : 0 < A) (hC : 0 < C) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * ‖z‖))
    (hL2 : MemLp (fun x : ℝ => f x) 2 volume) :
    ∃ F : ℝ → ℂ,
      MemLp F 2 (volume.restrict (Set.Ioo (-A) A)) ∧
      MemLp F 2 (volume.restrict (Set.Icc (-A) A)) ∧
      (∀ z : ℂ, f z = holomorphicFourierInterval A F z) ∧
      (∀ z : ℂ, f z = ∫ t in Set.Ioo (-A) A, F t * Complex.exp (Complex.I * (t : ℂ) * z)) ∧
      (∀ z : ℂ, f z = ∫ t in (-A)..A, F t * Complex.exp (Complex.I * (t : ℂ) * z)) := by
  obtain ⟨hΦ_diff, hΦ_r, hΦ_l, _, _, _⟩ := theorem19_4 hA hC hf hbound hL2
  let εseq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε_pos : ∀ n : ℕ, 0 < εseq n := fun n => by dsimp [εseq]; positivity
  let h_seq : ℕ → ℝ → ℂ := fun n x => f x * (Real.exp (-εseq n * |x|) : ℂ)
  have hf_real_cont : Continuous (fun x : ℝ => f x) :=
    hf.continuous.comp Complex.continuous_ofReal
  -- Each h_seq n is in L¹(ℝ) ∩ L²(ℝ)
  have hh_mem2 : ∀ n : ℕ, MemLp (h_seq n) 2 volume := by
    intro n
    refine hL2.norm.mono'
      (hf_real_cont.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
    filter_upwards with x
    dsimp [h_seq]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have : -εseq n * |x| ≤ 0 := by nlinarith [hε_pos n, abs_nonneg x]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr this)
  have hh_int1 : ∀ n : ℕ, Integrable (h_seq n) volume := by
    intro n
    have hexp_mem2 : MemLp (fun x : ℝ => Real.exp (-εseq n * |x|)) 2 volume := by
      have hc : Continuous (fun x : ℝ => Real.exp (-εseq n * |x|)) := by fun_prop
      refine (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr ?_
      have hint_pos : IntegrableOn (fun x : ℝ => Real.exp (-(2 * εseq n) * x)) (Set.Ioi 0) volume :=
        integrableOn_exp_mul_Ioi (by linarith [hε_pos n]) 0
      have hint_neg : IntegrableOn (fun x : ℝ => Real.exp (-(2 * εseq n) * (-x))) (Set.Iic 0) volume := by
        have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
        have h1 : IntegrableOn (fun x : ℝ => Real.exp (-(2 * εseq n) * x)) (Set.Ici 0) volume := by
          rwa [IntegrableOn, Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
        have h2 := (hmp.integrable_comp_emb (Homeomorph.neg ℝ).measurableEmbedding
          (g := Set.indicator (Set.Ici (0 : ℝ)) (fun u => Real.exp (-(2 * εseq n) * u)))).mpr
          ((integrable_indicator_iff measurableSet_Ici).mpr h1)
        rw [← integrable_indicator_iff measurableSet_Iic]
        refine h2.congr (Eventually.of_forall fun x => ?_)
        by_cases hx : x ≤ 0
        · have hnx : (-x) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (neg_nonneg.mpr hx)
          have hx' : x ∈ Set.Iic (0 : ℝ) := Set.mem_Iic.mpr hx
          change Set.indicator (Set.Ici (0 : ℝ)) (fun u => Real.exp (-(2 * εseq n) * u)) (-x) =
            Set.indicator (Set.Iic (0 : ℝ)) (fun u => Real.exp (-(2 * εseq n) * (-u))) x
          rw [Set.indicator_of_mem hnx, Set.indicator_of_mem hx']
        · have hnx : (-x) ∉ Set.Ici (0 : ℝ) := by rw [Set.mem_Ici]; linarith
          have hx' : x ∉ Set.Iic (0 : ℝ) := hx
          change Set.indicator (Set.Ici (0 : ℝ)) (fun u => Real.exp (-(2 * εseq n) * u)) (-x) =
            Set.indicator (Set.Iic (0 : ℝ)) (fun u => Real.exp (-(2 * εseq n) * (-u))) x
          rw [Set.indicator_of_notMem hnx, Set.indicator_of_notMem hx']
      have hint_union : IntegrableOn (fun x : ℝ => (Real.exp (-εseq n * |x|)) ^ 2)
          (Set.Iic 0 ∪ Set.Ioi 0) volume := by
        refine IntegrableOn.union ?_ ?_
        · refine hint_neg.congr_fun (fun x hx => ?_) measurableSet_Iic
          rw [abs_of_nonpos hx, ← Real.exp_nat_mul]
          exact congr_arg Real.exp (by push_cast; ring)
        · refine hint_pos.congr_fun (fun x hx => ?_) measurableSet_Ioi
          have hxp : 0 < x := hx
          rw [abs_of_pos hxp, ← Real.exp_nat_mul]
          exact congr_arg Real.exp (by push_cast; ring)
      rwa [Set.Iic_union_Ioi, integrableOn_univ] at hint_union
    refine (hL2.norm.integrable_mul hexp_mem2).mono'
      (hf_real_cont.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
    filter_upwards with x
    dsimp [h_seq, Pi.mul_apply]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  -- Formula relating ch19InvFourier (h_seq n) t to gluedLaplace A f
  have hh_inv_eq : ∀ (n : ℕ) (t : ℝ),
      ch19InvFourier (h_seq n) t =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (gluedLaplace A f ((εseq n : ℂ) + Complex.I * (t : ℂ)) -
            gluedLaplace A f (-(εseq n : ℂ) + Complex.I * (t : ℂ))) := by
    intro n t
    unfold ch19InvFourier
    congr 1
    let ψ : ℝ → ℂ := fun x => h_seq n x * Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))
    have hψ_int : Integrable ψ volume := by
      refine (hh_int1 n).norm.mono'
        (((hh_int1 n).aestronglyMeasurable).mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
      filter_upwards with x
      dsimp [ψ]
      rw [norm_mul, norm_exp_neg_I_mul_real_mul_real, mul_one]
    have hsplit_univ :=
      (MeasureTheory.integral_add_compl (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi hψ_int).symm
    have hcompl : (Set.Ioi (0 : ℝ))ᶜ = Set.Iic (0 : ℝ) := Set.compl_Ioi
    rw [hcompl] at hsplit_univ
    rw [hsplit_univ]
    have h_pos_part : (∫ x in Set.Ioi (0 : ℝ), ψ x) =
        gluedLaplace A f ((εseq n : ℂ) + Complex.I * (t : ℂ)) := by
      have hre : 0 < ((εseq n : ℂ) + Complex.I * (t : ℂ)).re := by simp [hε_pos n]
      rw [hΦ_r _ hre]
      unfold rayLaplace
      refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
      have hr_pos : 0 < r := hr
      dsimp [ψ, h_seq]
      rw [abs_of_pos hr_pos, Complex.ofReal_exp, mul_assoc]
      simp only [zero_mul, Complex.exp_zero, mul_one, ← Complex.exp_add]
      congr 1
      exact congr_arg Complex.exp (by push_cast; ring)
    have h_neg_part : (∫ x in Set.Iic (0 : ℝ), ψ x) =
        -gluedLaplace A f (-(εseq n : ℂ) + Complex.I * (t : ℂ)) := by
      have hre : (-(εseq n : ℂ) + Complex.I * (t : ℂ)).re < 0 := by simp [hε_pos n]
      rw [hΦ_l _ hre]
      have hIio : (∫ x in Set.Iic (0 : ℝ), ψ x) = ∫ x in Set.Iio (0 : ℝ), ψ x :=
        setIntegral_congr_set Iio_ae_eq_Iic.symm
      rw [hIio]
      have hpre : Neg.neg ⁻¹' Set.Ioi (0 : ℝ) = Set.Iio (0 : ℝ) := by ext x; simp
      have hmp := (Measure.measurePreserving_neg volume).setIntegral_preimage_emb
        (Homeomorph.neg ℝ).measurableEmbedding (fun x => ψ (-x)) (Set.Ioi (0 : ℝ))
      simp only [hpre, neg_neg] at hmp
      rw [hmp]
      unfold rayLaplace
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
      have hr_pos : 0 < r := hr
      dsimp [ψ, h_seq]
      rw [abs_neg, abs_of_pos hr_pos, Complex.exp_pi_mul_I, Complex.ofReal_neg,
        Complex.ofReal_exp, mul_assoc (f (-(r : ℂ))), ← Complex.exp_add]
      have hr1 : (r : ℂ) * (-1 : ℂ) = -(r : ℂ) := by ring
      have hexp1 : -(-(εseq n : ℂ) + Complex.I * (t : ℂ)) * (r : ℂ) * (-1 : ℂ) =
          ((-εseq n * r : ℝ) : ℂ) + -Complex.I * (t : ℂ) * -(r : ℂ) := by
        push_cast; ring
      rw [hr1, hexp1]
      ring
    rw [h_pos_part, h_neg_part, sub_eq_add_neg]
  -- Pointwise vanishing of ch19InvFourier (h_seq n) t → 0 for |t| > A
  have hh_inv_zero : ∀ t : ℝ, A < |t| →
      Tendsto (fun n : ℕ => ch19InvFourier (h_seq n) t) atTop (𝓝 0) := by
    intro t ht
    let w₀ : ℂ := Complex.I * (t : ℂ)
    have hw₀_slit : w₀ ∈ slitPlane A := by
      rintro ⟨_, him⟩
      have him_eq : w₀.im = t := by simp [w₀]
      rw [him_eq] at him
      exact not_le_of_gt ht (abs_le.mpr him)
    have hΦ_cont : ContinuousAt (gluedLaplace A f) w₀ :=
      (hΦ_diff.differentiableAt ((isOpen_slitPlane A).mem_nhds hw₀_slit)).continuousAt
    have h_eps0 : Tendsto (fun n : ℕ => (εseq n : ℂ)) atTop (𝓝 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
    have hw_pos : Tendsto (fun n : ℕ => (εseq n : ℂ) + w₀) atTop (𝓝 w₀) := by
      simpa using h_eps0.add tendsto_const_nhds
    have hw_neg : Tendsto (fun n : ℕ => -(εseq n : ℂ) + w₀) atTop (𝓝 w₀) := by
      simpa using h_eps0.neg.add tendsto_const_nhds
    have hdiff_lim : Tendsto (fun n : ℕ =>
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (gluedLaplace A f ((εseq n : ℂ) + w₀) - gluedLaplace A f (-(εseq n : ℂ) + w₀)))
        atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul ((hΦ_cont.tendsto.comp hw_pos).sub (hΦ_cont.tendsto.comp hw_neg))
    exact hdiff_lim.congr fun n => (hh_inv_eq n t).symm
  -- L² convergence h_seq n → f|_ℝ, hence ch19InvFourier (h_seq n) → G in L²(ℝ)
  let G : ℝ → ℂ := ch19InvFourierL2 (fun x : ℝ => f x) hL2
  have hG_mem2 : MemLp G 2 volume := ch19InvFourierL2_memLp hL2
  have hh_L2_conv : Tendsto (fun n : ℕ => ∫ x : ℝ, ‖h_seq n x - f x‖ ^ 2) atTop (𝓝 0) := by
    have hdom : Integrable (fun x : ℝ => 4 * ‖f x‖ ^ 2) volume := hL2.norm.integrable_sq.const_mul 4
    have h0_int : (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) := by simp
    rw [h0_int]
    refine tendsto_integral_of_dominated_convergence (fun x : ℝ => 4 * ‖f x‖ ^ 2)
      (fun n => ((hh_mem2 n).sub hL2).norm.integrable_sq.aestronglyMeasurable) hdom
      (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h1 : ‖h_seq n x - f x‖ ≤ 2 * ‖f x‖ := by
        have he1 : Real.exp (-εseq n * |x|) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [hε_pos n, abs_nonneg x])
        calc ‖h_seq n x - f x‖
            ≤ ‖h_seq n x‖ + ‖f x‖ := norm_sub_le _ _
          _ = ‖f x‖ * Real.exp (-εseq n * |x|) + ‖f x‖ := by
              dsimp [h_seq]
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
          _ ≤ ‖f x‖ * 1 + ‖f x‖ := by gcongr
          _ = 2 * ‖f x‖ := by ring
      nlinarith [norm_nonneg (h_seq n x - f x)]
    · have hexp1 : Tendsto (fun n : ℕ => (Real.exp (-εseq n * |x|) : ℂ)) atTop (𝓝 1) := by
        have h0 : Tendsto (fun n : ℕ => -(|x| * εseq n)) atTop (𝓝 (- (|x| * 0))) :=
          (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat).neg
        rw [mul_zero, neg_zero] at h0
        have h0' : Tendsto (fun n : ℕ => -εseq n * |x|) atTop (𝓝 0) :=
          h0.congr fun n => by ring
        have h1 : Tendsto (fun n : ℕ => Real.exp (-εseq n * |x|)) atTop (𝓝 (Real.exp 0)) :=
          (Real.continuous_exp.tendsto 0).comp h0'
        rw [Real.exp_zero] at h1
        have h2 : Tendsto (fun n : ℕ => (Real.exp (-εseq n * |x|) : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
          (Complex.continuous_ofReal.tendsto 1).comp h1
        rwa [Complex.ofReal_one] at h2
      have hpt : Tendsto (fun n : ℕ => h_seq n x) atTop (𝓝 (f x)) := by
        simpa [h_seq] using tendsto_const_nhds.mul hexp1
      have hsub := tendsto_iff_norm_sub_tendsto_zero.mp hpt
      simpa using hsub.pow 2
  have hG_L2_conv : Tendsto (fun n : ℕ => eLpNorm (ch19InvFourier (h_seq n) - G) 2 volume)
      atTop (𝓝 0) := by
    have hint_sq_lim : Tendsto (fun n : ℕ => ∫ t : ℝ, ‖ch19InvFourier (h_seq n) t - G t‖ ^ 2)
        atTop (𝓝 0) := by
      have hscaled : Tendsto (fun n : ℕ => (1 / (2 * Real.pi)) * ∫ x : ℝ, ‖h_seq n x - f x‖ ^ 2)
          atTop (𝓝 0) := by
        simpa using hh_L2_conv.const_mul (1 / (2 * Real.pi))
      refine hscaled.congr' (Eventually.of_forall fun n => ?_)
      have hcompat := ch19InvFourierL2_compat (hh_int1 n) (hh_mem2 n)
      have hsub_sq := ch19InvFourierL2_sub_norm_sq (hh_mem2 n) hL2
      rw [← hsub_sq]
      apply integral_congr_ae
      filter_upwards [hcompat] with t ht
      rw [ht]
    have h_enorm : ∀ n : ℕ, eLpNorm (ch19InvFourier (h_seq n) - G) 2 volume =
        ENNReal.ofReal ((∫ t : ℝ, ‖ch19InvFourier (h_seq n) t - G t‖ ^ 2) ^ (2 : ℝ)⁻¹) := by
      intro n
      have hm := ((ch19InvFourier_plancherel_L1_L2 (hh_int1 n) (hh_mem2 n)).1).sub hG_mem2
      rw [hm.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
      simp only [ENNReal.toReal_ofNat, Pi.sub_apply, Real.rpow_two]
    simp_rw [h_enorm]
    have hrpow : Tendsto (fun n : ℕ => (∫ t : ℝ, ‖ch19InvFourier (h_seq n) t - G t‖ ^ 2) ^ (2 : ℝ)⁻¹)
        atTop (𝓝 0) := by
      have h := ((Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹)).tendsto 0).comp
        hint_sq_lim
      rw [Real.zero_rpow (by positivity)] at h
      exact h
    have hof := (ENNReal.continuous_ofReal.tendsto 0).comp hrpow
    rw [ENNReal.ofReal_zero] at hof
    exact hof
  -- Extract a.e.-convergent subsequence to deduce G = 0 a.e. outside [-A, A]
  have h_in_meas := MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hG_L2_conv
  obtain ⟨ns, hns_mono, hns_ae⟩ := h_in_meas.exists_seq_tendsto_ae
  let F : ℝ → ℂ := Set.indicator (Set.Icc (-A) A) G
  have hG_eq_F_ae : G =ᵐ[volume] F := by
    filter_upwards [hns_ae] with t ht_lim
    by_cases ht_mem : t ∈ Set.Icc (-A) A
    · simp [F, Set.indicator_of_mem ht_mem]
    · simp only [F, Set.indicator_of_notMem ht_mem]
      have habs_gt : A < |t| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht_mem
        rcases ht_mem with h | h
        · have hneg : A < -t := by linarith
          exact hneg.trans_le (neg_le_abs t)
        · exact h.trans_le (le_abs_self t)
      have h0_sub : Tendsto (fun i : ℕ => ch19InvFourier (h_seq (ns i)) t) atTop (𝓝 0) :=
        (hh_inv_zero t habs_gt).comp hns_mono.tendsto_atTop
      exact tendsto_nhds_unique ht_lim h0_sub
  have hF_mem2_vol : MemLp F 2 volume := hG_mem2.ae_eq hG_eq_F_ae
  have hF_mem2_Icc : MemLp F 2 (volume.restrict (Set.Icc (-A) A)) :=
    hF_mem2_vol.restrict (Set.Icc (-A) A)
  have hF_mem2_Ioo : MemLp F 2 (volume.restrict (Set.Ioo (-A) A)) :=
    hF_mem2_vol.restrict (Set.Ioo (-A) A)
  have hF_int1_vol : Integrable F volume := by
    change Integrable (Set.indicator (Set.Icc (-A) A) G) volume
    rw [integrable_indicator_iff measurableSet_Icc]
    have : Fact (volume (Set.Icc (-A) A) < ⊤) := ⟨by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
    have : IsFiniteMeasure (volume.restrict (Set.Icc (-A) A)) := inferInstance
    exact (hG_mem2.restrict (Set.Icc (-A) A)).integrable one_le_two
  have hG_int1_vol : Integrable G volume := hF_int1_vol.congr hG_eq_F_ae.symm
  -- L² Fourier inversion gives f = holomorphicFourierInterval A F a.e. on ℝ, hence everywhere on ℝ and ℂ
  have hf_ae : (fun x : ℝ => f x) =ᵐ[volume] fun x : ℝ => holomorphicFourierInterval A F x := by
    filter_upwards [ch19InvFourierL2_inversion_ae hL2 (ae_eq_refl G) hG_int1_vol] with x hx
    rw [hx]
    unfold ch19Fourier holomorphicFourierInterval
    have hcongr : (fun t : ℝ => G t * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) =ᵐ[volume]
        Set.indicator (Set.Icc (-A) A)
          (fun t : ℝ => F t * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) := by
      filter_upwards [hG_eq_F_ae] with t ht
      rw [ht]
      by_cases hm : t ∈ Set.Icc (-A) A
      · simp [Set.indicator_of_mem hm]
      · simp [F, Set.indicator_of_notMem hm]
    rw [integral_congr_ae hcongr, integral_indicator measurableSet_Icc]
  have hg_entire : Differentiable ℂ (holomorphicFourierInterval A F) :=
    (holomorphicFourierInterval_properties hA hF_mem2_Ioo).2.1
  have hg_real_cont : Continuous (fun x : ℝ => holomorphicFourierInterval A F x) :=
    hg_entire.continuous.comp Complex.continuous_ofReal
  have hf_eq_real_fun : (fun x : ℝ => f x) = fun x : ℝ => holomorphicFourierInterval A F x :=
    (Continuous.ae_eq_iff_eq volume hf_real_cont hg_real_cont).mp hf_ae
  have hf_eq_entire : ∀ z : ℂ, f z = holomorphicFourierInterval A F z :=
    entire_eq_of_eq_on_reals hf hg_entire (congr_fun hf_eq_real_fun)
  exact ⟨F, hF_mem2_Ioo, hF_mem2_Icc, hf_eq_entire,
    fun z => (hf_eq_entire z).trans (holomorphicFourierInterval_endpoint_eq hA.le F z).2.1,
    fun z => (hf_eq_entire z).trans (holomorphicFourierInterval_endpoint_eq hA.le F z).2.2⟩

end Node19_3_4

/-! ## §19.5: Uniqueness of Holomorphic Functions vs. Smooth Real Counterexample (RCA p. 377) -/

/-- **Node 19.5 (Analytic Uniqueness vs. Smooth Compactly Supported Counterexample, RCA p. 377):**
1. Every function holomorphic on a connected open set `Ω ⊆ ℂ` whose iterated derivatives all vanish
   at one point `z₀ ∈ Ω` vanishes identically on `Ω`.
2. By contrast, on `ℝ` there exists a nonzero smooth (`C^∞`) compactly supported complex-valued
   function `f : ℝ → ℂ` that vanishes on `(-1, 1)` (hence has `D^n f(0) = 0` for every `n : ℕ`). -/
theorem theorem19_5 :
    (∀ (Ω : Set ℂ) (f : ℂ → ℂ) (z₀ : ℂ),
      IsOpen Ω → IsPreconnected Ω → DifferentiableOn ℂ f Ω → z₀ ∈ Ω →
        (∀ n : ℕ, iteratedDeriv n f z₀ = 0) → ∀ z ∈ Ω, f z = 0) ∧
    (∃ f : ℝ → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      HasCompactSupport f ∧
      (∀ x ∈ Set.Ioo (-1 : ℝ) 1, f x = 0) ∧
      (∀ n : ℕ, iteratedDeriv n f 0 = 0) ∧
      ∃ x : ℝ, f x ≠ 0) := by
  refine ⟨fun Ω f z₀ hopen hconn hf hz₀ hderiv =>
    holomorphic_eq_zero_of_iteratedDeriv_eq_zero hopen hconn hf hz₀ hderiv, ?_⟩
  let b : ContDiffBump (2 : ℝ) :=
    { rIn := 1 / 2
      rOut := 1
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  let f : ℝ → ℂ := fun x => ((b x : ℝ) : ℂ)
  have hf_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f :=
    Complex.ofRealCLM.contDiff.comp (b.contDiff (n := ⊤))
  have hf_supp : HasCompactSupport f := by
    refine b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hf_Ioo : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, f x = 0 := by
    intro x hx
    dsimp [f]
    have hdist : b.rOut ≤ dist x (2 : ℝ) := by
      rw [Real.dist_eq, abs_of_neg (by linarith [hx.2])]
      change (1 : ℝ) ≤ -(x - 2)
      linarith [hx.2]
    rw [b.zero_of_le_dist hdist, Complex.ofReal_zero]
  have hf_deriv0 : ∀ n : ℕ, iteratedDeriv n f 0 = 0 := by
    intro n
    have hev : f =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℂ) := by
      filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with x hx
      exact hf_Ioo x hx
    rw [(hev.iteratedDeriv n).self_of_nhds, iteratedDeriv_const]
    split_ifs <;> rfl
  have hf_ne : f 2 ≠ 0 := by
    dsimp [f]
    have hmem : (2 : ℝ) ∈ Metric.closedBall (2 : ℝ) b.rIn :=
      Metric.mem_closedBall_self (by dsimp [b]; norm_num)
    rw [b.one_of_mem_closedBall hmem, Complex.ofReal_one]
    exact one_ne_zero
  exact ⟨f, hf_smooth, hf_supp, hf_Ioo, hf_deriv0, 2, hf_ne⟩


/-! ## §19.6: Weighted Smooth Classes `C{M_n}`, Closure Properties, and Hazards (RCA pp. 377–378) -/

open scoped ContDiff

/-- **Node 19.6 (`C{M_n}`, RCA p. 377):**
For a sequence `M : ℕ → ℝ`, `CM M` is the class of smooth (`C^∞`) functions `f : ℝ → ℂ` for which
there exist constants `β > 0` and `B > 0` satisfying `‖D^n f(x)‖ ≤ β * B^n * M_n` for all `n : ℕ`
and `x : ℝ`. -/
def CM (M : ℕ → ℝ) : Set (ℝ → ℂ) :=
  {f : ℝ → ℂ | ContDiff ℝ ∞ f ∧
    ∃ β > 0, ∃ B > 0, ∀ n : ℕ, ∀ x : ℝ, ‖iteratedDeriv n f x‖ ≤ β * B ^ n * M n}

/-- **Node 19.6 (Standing positivity, normalization `M_0 = 1`, and log-convexity hypotheses,
RCA pp. 377–378):** `0 < M_n` for all `n`, `M_0 = 1`, and `M_n^2 ≤ M_{n-1} M_{n+1}` for `n ≥ 1`. -/
def IsPosNormLogConvex (M : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 < M n) ∧ M 0 = 1 ∧ ∀ n : ℕ, 1 ≤ n → (M n) ^ 2 ≤ M (n - 1) * M (n + 1)

section Node19_6_Helpers

lemma contDiff_iteratedDeriv_infty {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  rw [iteratedDeriv_eq_iterate]
  exact hf.iterate_deriv n

lemma differentiable_iteratedDeriv_of_infty {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n f) :=
  (contDiff_infty_iff_deriv.mp (contDiff_iteratedDeriv_infty hf n)).1

lemma continuous_iteratedDeriv_of_infty {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    Continuous (iteratedDeriv n f) :=
  (contDiff_iteratedDeriv_infty hf n).continuous

/-- Iterated derivative of `t ↦ exp(i c t)` on `ℝ`. -/
lemma iteratedDeriv_exp_I_mul_real (c : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t : ℝ => Complex.exp (Complex.I * (c : ℂ) * (t : ℂ))) x =
      (Complex.I * (c : ℂ)) ^ n * Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv n (fun t : ℝ => Complex.exp (Complex.I * (c : ℂ) * (t : ℂ))) =
        fun t : ℝ => (Complex.I * (c : ℂ)) ^ n * Complex.exp (Complex.I * (c : ℂ) * (t : ℂ)) :=
      funext ih
    rw [hfun]
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (Complex.I * (c : ℂ) * z))
        (Complex.I * (c : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (x : ℂ))) (x : ℂ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id (x : ℂ)).const_mul (Complex.I * (c : ℂ))).cexp)
    have h2 : HasDerivAt
        (fun t : ℝ => (Complex.I * (c : ℂ)) ^ n * Complex.exp (Complex.I * (c : ℂ) * (t : ℂ)))
        ((Complex.I * (c : ℂ)) ^ (n + 1) * Complex.exp (Complex.I * (c : ℂ) * (x : ℂ))) x := by
      simpa [pow_succ, mul_assoc] using (h1.comp_ofReal).const_mul ((Complex.I * (c : ℂ)) ^ n)
    exact h2.deriv

/-- Smoothness of `t ↦ exp(i c t)` on `ℝ`. -/
lemma contDiff_exp_I_mul_real (c : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => Complex.exp (Complex.I * (c : ℂ) * (t : ℂ))) := by
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => Complex.I * (c : ℂ) * (t : ℂ)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff)
  exact h1.cexp

/-- Iterated derivative of an affine composition `t ↦ f(a t + b)` for smooth `f : ℝ → ℂ`. -/
theorem iteratedDeriv_comp_affine {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t : ℝ => f (a * t + b)) x =
      (a ^ n : ℝ) • iteratedDeriv n f (a * x + b) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv n (fun t : ℝ => f (a * t + b)) =
        fun t : ℝ => (a ^ n : ℝ) • iteratedDeriv n f (a * t + b) := funext ih
    rw [hfun]
    have hg_diff : Differentiable ℝ (iteratedDeriv n f) :=
      differentiable_iteratedDeriv_of_infty hf n
    have hu : HasDerivAt (fun t : ℝ => a * t + b) a x := by
      have hmul : HasDerivAt (fun t : ℝ => a * t) (a * 1) x := (hasDerivAt_id x).const_mul a
      simpa using hmul.add_const b
    have hcomp : HasDerivAt (fun t : ℝ => iteratedDeriv n f (a * t + b))
        (a • deriv (iteratedDeriv n f) (a * x + b)) x := by
      change HasDerivAt ((iteratedDeriv n f) ∘ fun t : ℝ => a * t + b)
        (a • deriv (iteratedDeriv n f) (a * x + b)) x
      exact HasDerivAt.scomp x (hg_diff (a * x + b)).hasDerivAt hu
    have hsmul : HasDerivAt (fun t : ℝ => (a ^ n : ℝ) • iteratedDeriv n f (a * t + b))
        ((a ^ (n + 1) : ℝ) • iteratedDeriv (n + 1) f (a * x + b)) x := by
      refine (hcomp.const_smul (a ^ n : ℝ)).congr_deriv ?_
      rw [← iteratedDeriv_succ, smul_smul, ← pow_succ]
    exact hsmul.deriv

/-- Zero belongs to `CM M` whenever every `M_n > 0`. -/
theorem zero_mem_CM {M : ℕ → ℝ} (hM : ∀ n : ℕ, 0 < M n) :
    (0 : ℝ → ℂ) ∈ CM M := by
  refine ⟨contDiff_const, 1, zero_lt_one, 1, zero_lt_one, fun n x => ?_⟩
  have h0 : iteratedDeriv n (0 : ℝ → ℂ) x = 0 := by
    change iteratedDeriv n (fun _ : ℝ => (0 : ℂ)) x = 0
    rw [iteratedDeriv_const]
    split_ifs <;> rfl
  rw [h0, norm_zero]
  exact le_of_lt (by positivity [hM n])

/-- Closure of `CM M` under addition. -/
theorem add_mem_CM {M : ℕ → ℝ} (hM : ∀ n : ℕ, 0 < M n) {f g : ℝ → ℂ}
    (hf : f ∈ CM M) (hg : g ∈ CM M) :
    f + g ∈ CM M := by
  rcases hf with ⟨hf_cd, β₁, hβ₁, B₁, hB₁, hbd₁⟩
  rcases hg with ⟨hg_cd, β₂, hβ₂, B₂, hB₂, hbd₂⟩
  refine ⟨hf_cd.add hg_cd, β₁ + β₂, add_pos hβ₁ hβ₂, max B₁ B₂, lt_max_of_lt_left hB₁, fun n x => ?_⟩
  have hadd : iteratedDeriv n (f + g) x = iteratedDeriv n f x + iteratedDeriv n g x :=
    iteratedDeriv_add ((contDiff_infty.mp hf_cd n).contDiffAt) ((contDiff_infty.mp hg_cd n).contDiffAt)
  rw [hadd]
  have hpow₁ : B₁ ^ n ≤ (max B₁ B₂) ^ n := pow_le_pow_left₀ hB₁.le (le_max_left _ _) n
  have hpow₂ : B₂ ^ n ≤ (max B₁ B₂) ^ n := pow_le_pow_left₀ hB₂.le (le_max_right _ _) n
  have hMnn : 0 ≤ M n := (hM n).le
  calc
    ‖iteratedDeriv n f x + iteratedDeriv n g x‖
      ≤ ‖iteratedDeriv n f x‖ + ‖iteratedDeriv n g x‖ := norm_add_le _ _
    _ ≤ β₁ * B₁ ^ n * M n + β₂ * B₂ ^ n * M n := add_le_add (hbd₁ n x) (hbd₂ n x)
    _ ≤ β₁ * (max B₁ B₂) ^ n * M n + β₂ * (max B₁ B₂) ^ n * M n := by
        gcongr
    _ = (β₁ + β₂) * (max B₁ B₂) ^ n * M n := by ring

/-- Closure of `CM M` under complex scalar multiplication. -/
theorem smul_mem_CM {M : ℕ → ℝ} {f : ℝ → ℂ} (c : ℂ) (hf : f ∈ CM M) :
    c • f ∈ CM M := by
  rcases hf with ⟨hf_cd, β, hβ, B, hB, hbd⟩
  refine ⟨hf_cd.const_smul c, (‖c‖ + 1) * β, mul_pos (by positivity) hβ, B, hB, fun n x => ?_⟩
  have hsmul : iteratedDeriv n (c • f) x = c * iteratedDeriv n f x := by
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      rw [iteratedDeriv_succ, show iteratedDeriv n (c • f) = fun y => c * iteratedDeriv n f y from
        funext ih]
      have hd : DifferentiableAt ℝ (iteratedDeriv n f) x :=
        (differentiable_iteratedDeriv_of_infty hf_cd n) x
      rw [(hd.hasDerivAt.const_mul c).deriv, ← iteratedDeriv_succ]
  rw [hsmul, norm_mul]
  have hM_nonneg : 0 ≤ B ^ n * M n := by
    have h0 := hbd n x
    have hnorm : 0 ≤ ‖iteratedDeriv n f x‖ := norm_nonneg _
    have hprod : 0 ≤ β * (B ^ n * M n) := by linarith
    exact nonneg_of_mul_nonneg_right hprod hβ
  calc
    ‖c‖ * ‖iteratedDeriv n f x‖ ≤ ‖c‖ * (β * B ^ n * M n) :=
      mul_le_mul_of_nonneg_left (hbd n x) (norm_nonneg c)
    _ ≤ (‖c‖ + 1) * (β * B ^ n * M n) := by
      have : 0 ≤ β * B ^ n * M n := by
        simpa [mul_assoc] using mul_nonneg hβ.le hM_nonneg
      nlinarith
    _ = ((‖c‖ + 1) * β) * B ^ n * M n := by ring

end Node19_6_Helpers

/-- **Node 19.6 (`CMSubmodule`, RCA p. 377):**
For any positive sequence `M_n > 0`, `CM M` is a `ℂ`-linear subspace of `ℝ → ℂ`. -/
def CMSubmodule (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n) : Submodule ℂ (ℝ → ℂ) where
  carrier := CM M
  zero_mem' := zero_mem_CM hM
  add_mem' hf hg := add_mem_CM hM hf hg
  smul_mem' c _ hf := smul_mem_CM c hf

/-- **Node 19.6 (`limsup` characterization of `C{M_n}`, RCA p. 377):**
For positive `M_n` and smooth `f : ℝ → ℂ`, `f ∈ CM M` if and only if each derivative `D^n f` is
bounded on `ℝ` and `limsup_{n → ∞} (‖D^n f‖_∞ / M_n)^{1/n} < ∞`. -/
theorem mem_CM_iff_limsup {M : ℕ → ℝ} (hM : ∀ n : ℕ, 0 < M n) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) :
    f ∈ CM M ↔
      (∀ n : ℕ, BddAbove (Set.range fun x : ℝ => ‖iteratedDeriv n f x‖)) ∧
      Filter.limsup
        (fun n : ℕ =>
          ENNReal.ofReal (((⨆ x : ℝ, ‖iteratedDeriv n f x‖) / M n) ^ (1 / (n : ℝ))))
        atTop < ⊤ := by
  let S : ℕ → ℝ := fun n => ⨆ x : ℝ, ‖iteratedDeriv n f x‖
  let u : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal ((S n / M n) ^ (1 / (n : ℝ)))
  constructor
  · rintro ⟨_, β, hβ, B, hB, hbd⟩
    have hbdd : ∀ n : ℕ, BddAbove (Set.range fun x : ℝ => ‖iteratedDeriv n f x‖) := by
      intro n
      exact ⟨β * B ^ n * M n, by rintro _ ⟨x, rfl⟩; exact hbd n x⟩
    refine ⟨hbdd, ?_⟩
    have hS_le : ∀ n : ℕ, S n / M n ≤ β * B ^ n := by
      intro n
      rw [div_le_iff₀ (hM n)]
      exact ciSup_le fun x => hbd n x
    -- Bound β^(1/n) ≤ max β 1 for n ≥ 1
    let C : ℝ := max β 1 * B
    have h_ev : ∀ᶠ n : ℕ in atTop, u n ≤ ENNReal.ofReal C := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
      have hSn_nonneg : 0 ≤ S n :=
        le_trans (norm_nonneg (iteratedDeriv n f 0)) (le_ciSup (hbdd n) 0)
      have hdiv_nonneg : 0 ≤ S n / M n := div_nonneg hSn_nonneg (hM n).le
      have hβ1 : 1 ≤ max β 1 := le_max_right _ _
      have hpow_le : (S n / M n) ^ (1 / (n : ℝ)) ≤ C := by
        calc
          (S n / M n) ^ (1 / (n : ℝ))
            ≤ (β * B ^ n) ^ (1 / (n : ℝ)) :=
              Real.rpow_le_rpow hdiv_nonneg (hS_le n) (by positivity)
          _ ≤ (max β 1 * B ^ n) ^ (1 / (n : ℝ)) := by
              refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
              exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ = (max β 1) ^ (1 / (n : ℝ)) * (B ^ n) ^ (1 / (n : ℝ)) :=
              Real.mul_rpow (by positivity) (by positivity)
          _ = (max β 1) ^ (1 / (n : ℝ)) * B := by
              congr 1
              rw [← Real.rpow_natCast B n, ← Real.rpow_mul hB.le,
                mul_one_div_cancel hn_pos.ne', Real.rpow_one]
          _ ≤ (max β 1) ^ (1 : ℝ) * B := by
              refine mul_le_mul_of_nonneg_right ?_ hB.le
              refine Real.rpow_le_rpow_of_exponent_le hβ1 ?_
              rw [div_le_one hn_pos]
              exact_mod_cast hn
          _ = C := by rw [Real.rpow_one]
      exact ENNReal.ofReal_le_ofReal hpow_le
    exact lt_of_le_of_lt (Filter.limsup_le_of_le (h := h_ev)) ENNReal.ofReal_lt_top
  · rintro ⟨hbdd, hlim⟩
    -- Pick B > 0 with limsup u < ENNReal.ofReal B
    let L : ℝ := (Filter.limsup u atTop).toReal
    let B : ℝ := L + 1
    have hB_pos : 0 < B := by
      have : 0 ≤ L := ENNReal.toReal_nonneg
      linarith
    have hlim_lt : Filter.limsup u atTop < ENNReal.ofReal B := by
      rw [← ENNReal.ofReal_toReal hlim.ne]
      exact ENNReal.ofReal_lt_ofReal_iff hB_pos |>.mpr (by dsimp [B, L]; linarith)
    rw [Filter.limsup_eq_iInf_iSup_of_nat, iInf_lt_iff] at hlim_lt
    obtain ⟨N, hN⟩ := hlim_lt
    -- For n ≥ max N 1, S n ≤ B^n * M n
    have htail : ∀ n : ℕ, max N 1 ≤ n → S n ≤ B ^ n * M n := by
      intro n hn
      have hnN : N ≤ n := le_trans (le_max_left _ _) hn
      have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
      have hun : u n ≤ ENNReal.ofReal B :=
        le_trans (le_iSup₂ (f := fun i (_ : i ≥ N) => u i) n hnN) hN.le
      have hSn_nonneg : 0 ≤ S n :=
        le_trans (norm_nonneg (iteratedDeriv n f 0)) (le_ciSup (hbdd n) 0)
      have hdiv_nonneg : 0 ≤ S n / M n := div_nonneg hSn_nonneg (hM n).le
      have hrpow_le : (S n / M n) ^ (1 / (n : ℝ)) ≤ B :=
        (ENNReal.ofReal_le_ofReal_iff hB_pos.le).mp hun
      have hdiv_le : S n / M n ≤ B ^ n := by
        calc
          S n / M n = ((S n / M n) ^ (1 / (n : ℝ))) ^ (n : ℝ) := by
            rw [← Real.rpow_mul hdiv_nonneg, one_div_mul_cancel hn_pos.ne', Real.rpow_one]
          _ ≤ B ^ (n : ℝ) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hdiv_nonneg _) hrpow_le hn_pos.le
          _ = B ^ n := Real.rpow_natCast B n
      exact (div_le_iff₀ (hM n)).mp hdiv_le
    -- Absorb finitely many indices n < max N 1 into β
    let K_fin : ℝ := ∑ k ∈ Finset.range (max N 1), S k / (B ^ k * M k)
    let β : ℝ := K_fin + 1
    have hβ_pos : 0 < β := by
      have hK_nonneg : 0 ≤ K_fin := by
        refine Finset.sum_nonneg fun k _ => ?_
        have hSk : 0 ≤ S k :=
          le_trans (norm_nonneg (iteratedDeriv k f 0)) (le_ciSup (hbdd k) 0)
        exact div_nonneg hSk (mul_pos (pow_pos hB_pos k) (hM k)).le
      dsimp [β]; linarith
    refine ⟨hf, β, hβ_pos, B, hB_pos, fun n x => ?_⟩
    have hx_le : ‖iteratedDeriv n f x‖ ≤ S n := le_ciSup (hbdd n) x
    refine hx_le.trans ?_
    by_cases hn : max N 1 ≤ n
    · have h1 : 1 ≤ β := by
        have hK_nonneg : 0 ≤ K_fin := by
          refine Finset.sum_nonneg fun k _ => ?_
          have hSk : 0 ≤ S k :=
            le_trans (norm_nonneg (iteratedDeriv k f 0)) (le_ciSup (hbdd k) 0)
          exact div_nonneg hSk (mul_pos (pow_pos hB_pos k) (hM k)).le
        dsimp [β]; linarith
      calc
        S n ≤ B ^ n * M n := htail n hn
        _ = 1 * (B ^ n * M n) := (one_mul _).symm
        _ ≤ β * (B ^ n * M n) :=
          mul_le_mul_of_nonneg_right h1 (mul_pos (pow_pos hB_pos n) (hM n)).le
        _ = β * B ^ n * M n := by ring
    · push Not at hn
      have hmem : n ∈ Finset.range (max N 1) := Finset.mem_range.mpr hn
      have hterm_le : S n / (B ^ n * M n) ≤ K_fin := by
        refine Finset.single_le_sum (f := fun k : ℕ => S k / (B ^ k * M k)) (fun k _ => ?_) hmem
        have hSk : 0 ≤ S k :=
          le_trans (norm_nonneg (iteratedDeriv k f 0)) (le_ciSup (hbdd k) 0)
        exact div_nonneg hSk (mul_pos (pow_pos hB_pos k) (hM k)).le
      have hleβ : S n / (B ^ n * M n) ≤ β := by dsimp [β]; linarith
      have hBM_pos : 0 < B ^ n * M n := mul_pos (pow_pos hB_pos n) (hM n)
      have := (div_le_iff₀ hBM_pos).mp hleβ
      linarith

/-- **Hazard 19.6a (`node19_6_affine_witness_counterexample`, `SCOPING-H-19-20.md` §hazard 1):**
Rudin p. 377 proposes the affine witness `B_g = a * B_f` for `g(x) = f(a x + b)` without restricting
`a > 0`. Taking `M_n = 1`, `f(x) = exp(i x)`, `β_f = B_f = 1`, `a = -1`, `b = 0` satisfies the
hypothesis `‖D^n f(x)‖ ≤ β_f B_f^n M_n`, yet `a * B_f = -1 ≤ 0` violates `B_g > 0` AND fails the
bound `‖D^1 g(0)‖ ≤ β_f (a B_f)^1 M_1` (`1 ≤ -1`). -/
theorem node19_6_affine_witness_counterexample :
    let M : ℕ → ℝ := fun _ => 1
    let f : ℝ → ℂ := fun x => Complex.exp (Complex.I * (x : ℂ))
    let β_f : ℝ := 1
    let B_f : ℝ := 1
    let a : ℝ := -1
    let b : ℝ := 0
    let g : ℝ → ℂ := fun x => f (a * x + b)
    (∀ n : ℕ, 0 < M n) ∧
    ContDiff ℝ ∞ f ∧
    (∀ n : ℕ, ∀ x : ℝ, ‖iteratedDeriv n f x‖ ≤ β_f * B_f ^ n * M n) ∧
    ¬ (0 < a * B_f) ∧
    ¬ (‖iteratedDeriv 1 g 0‖ ≤ β_f * (a * B_f) ^ 1 * M 1) := by
  dsimp only
  refine ⟨fun _ => zero_lt_one, ?_, ?_, by norm_num, ?_⟩
  · simpa using contDiff_exp_I_mul_real 1
  · intro n x
    have hd := iteratedDeriv_exp_I_mul_real 1 n x
    simp only [Complex.ofReal_one, mul_one] at hd
    rw [hd, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
      show Complex.I * (x : ℂ) = ((x : ℝ) : ℂ) * Complex.I from mul_comm _ _,
      Complex.norm_exp_ofReal_mul_I]
    norm_num
  · have hg_eq : (fun x : ℝ => Complex.exp (Complex.I * (((-1 : ℝ) * x + 0 : ℝ) : ℂ))) =
        fun x : ℝ => Complex.exp (Complex.I * ((-1 : ℝ) : ℂ) * (x : ℂ)) := by
      ext x; congr 1; push_cast; ring
    rw [hg_eq, iteratedDeriv_exp_I_mul_real (-1) 1 0]
    simp [Complex.norm_I]

/-- **Node 19.6 (Corrected affine invariance of `C{M_n}`, RCA p. 377):**
If `‖D^n f(x)‖ ≤ β B^n M_n` with `β, B > 0`, then `g(x) = f(a x + b)` satisfies:
- for `a ≠ 0`, `0 < |a| * B` and `‖D^n g(x)‖ ≤ β (|a| B)^n M_n`;
- for all `a, b : ℝ` (including `a = 0`), `0 < max 1 |a| * B` and
  `‖D^n g(x)‖ ≤ β (max 1 |a| * B)^n M_n`, so `g ∈ CM M`. -/
theorem CM_comp_affine_bounds {M : ℕ → ℝ} (hM : ∀ n : ℕ, 0 < M n)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) {β B : ℝ} (hβ : 0 < β) (hB : 0 < B)
    (hbd : ∀ n : ℕ, ∀ x : ℝ, ‖iteratedDeriv n f x‖ ≤ β * B ^ n * M n) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ => f (a * x + b)) ∧
    (a ≠ 0 → 0 < |a| * B ∧
      ∀ n : ℕ, ∀ x : ℝ,
        ‖iteratedDeriv n (fun t : ℝ => f (a * t + b)) x‖ ≤ β * (|a| * B) ^ n * M n) ∧
    (0 < max 1 |a| * B ∧
      ∀ n : ℕ, ∀ x : ℝ,
        ‖iteratedDeriv n (fun t : ℝ => f (a * t + b)) x‖ ≤ β * (max 1 |a| * B) ^ n * M n) := by
  have hg_cd : ContDiff ℝ ∞ (fun x : ℝ => f (a * x + b)) :=
    hf.comp ((contDiff_const.mul contDiff_id).add contDiff_const)
  refine ⟨hg_cd, ?_, ?_⟩
  · intro ha
    refine ⟨mul_pos (abs_pos.mpr ha) hB, fun n x => ?_⟩
    rw [iteratedDeriv_comp_affine hf a b n x, norm_smul, Real.norm_eq_abs, abs_pow]
    calc
      |a| ^ n * ‖iteratedDeriv n f (a * x + b)‖
        ≤ |a| ^ n * (β * B ^ n * M n) :=
          mul_le_mul_of_nonneg_left (hbd n (a * x + b)) (pow_nonneg (abs_nonneg a) n)
      _ = β * (|a| * B) ^ n * M n := by rw [mul_pow]; ring
  · refine ⟨mul_pos (lt_max_of_lt_left zero_lt_one) hB, fun n x => ?_⟩
    rw [iteratedDeriv_comp_affine hf a b n x, norm_smul, Real.norm_eq_abs, abs_pow]
    have hpow : |a| ^ n ≤ (max 1 |a|) ^ n :=
      pow_le_pow_left₀ (abs_nonneg a) (le_max_right 1 |a|) n
    calc
      |a| ^ n * ‖iteratedDeriv n f (a * x + b)‖
        ≤ |a| ^ n * (β * B ^ n * M n) :=
          mul_le_mul_of_nonneg_left (hbd n (a * x + b)) (pow_nonneg (abs_nonneg a) n)
      _ ≤ (max 1 |a|) ^ n * (β * B ^ n * M n) :=
          mul_le_mul_of_nonneg_right hpow (by positivity [hM n])
      _ = β * (max 1 |a| * B) ^ n * M n := by rw [mul_pow]; ring

theorem CM_comp_affine {M : ℕ → ℝ} (hM : ∀ n : ℕ, 0 < M n) {f : ℝ → ℂ}
    (hf : f ∈ CM M) (a b : ℝ) :
    (fun x : ℝ => f (a * x + b)) ∈ CM M := by
  rcases hf with ⟨hf_cd, β, hβ, B, hB, hbd⟩
  have h := CM_comp_affine_bounds hM hf_cd hβ hB hbd a b
  exact ⟨h.1, β, hβ, max 1 |a| * B, h.2.2.1, h.2.2.2⟩

/-- Translation invariance `x ↦ f(x + x₀)` preserves `CM M` for every sequence `M` (with identical
witnesses `β, B`). -/
theorem CM_comp_add_right {M : ℕ → ℝ} {f : ℝ → ℂ} (hf : f ∈ CM M) (x₀ : ℝ) :
    (fun x : ℝ => f (x + x₀)) ∈ CM M := by
  rcases hf with ⟨hf_cd, β, hβ, B, hB, hbd⟩
  have hg_cd : ContDiff ℝ ∞ (fun x : ℝ => f (x + x₀)) :=
    hf_cd.comp (contDiff_id.add contDiff_const)
  refine ⟨hg_cd, β, hβ, B, hB, fun n x => ?_⟩
  have h_eq : (fun t : ℝ => f (t + x₀)) = fun t : ℝ => f (1 * t + x₀) := by ext t; congr 1; ring
  rw [h_eq, iteratedDeriv_comp_affine hf_cd 1 x₀ n x, one_pow, one_smul, one_mul]
  exact hbd n (x + x₀)

/-- Normalization `M_n ↦ M_n / M_0` leaves the class `CM M` unchanged when `M_n > 0`. -/
theorem CM_div_zero {M : ℕ → ℝ} (hM : ∀ n : ℕ, 0 < M n) :
    CM (fun n : ℕ => M n / M 0) = CM M := by
  ext f
  constructor
  · rintro ⟨hf_cd, β, hβ, B, hB, hbd⟩
    refine ⟨hf_cd, β / M 0, div_pos hβ (hM 0), B, hB, fun n x => ?_⟩
    calc
      ‖iteratedDeriv n f x‖ ≤ β * B ^ n * (M n / M 0) := hbd n x
      _ = (β / M 0) * B ^ n * M n := by ring
  · rintro ⟨hf_cd, β, hβ, B, hB, hbd⟩
    refine ⟨hf_cd, β * M 0, mul_pos hβ (hM 0), B, hB, fun n x => ?_⟩
    have h0 : M 0 ≠ 0 := (hM 0).ne'
    calc
      ‖iteratedDeriv n f x‖ ≤ β * B ^ n * M n := hbd n x
      _ = (β * M 0) * B ^ n * (M n / M 0) := by field_simp [h0]

section LogConvexHelpers

/-- Successive ratios `M_{k+1} / M_k` of a positive normalized log-convex sequence are monotone
nondecreasing. -/
theorem IsPosNormLogConvex.ratio_mono {M : ℕ → ℝ} (hM : IsPosNormLogConvex M) :
    Monotone (fun k : ℕ => M (k + 1) / M k) := by
  refine monotone_nat_of_le_succ fun k => ?_
  rw [div_le_div_iff₀ (hM.1 k) (hM.1 (k + 1))]
  have hlc := hM.2.2 (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
  simp only [Nat.add_sub_cancel] at hlc
  linarith [sq (M (k + 1))]

/-- Every positive normalized log-convex sequence `N` satisfies `(N 1)^n ≤ N n` for all `n : ℕ`. -/
theorem IsPosNormLogConvex.pow_one_le {M : ℕ → ℝ} (hM : IsPosNormLogConvex M) (n : ℕ) :
    (M 1) ^ n ≤ M n := by
  induction n with
  | zero => simp [hM.2.1]
  | succ n ih =>
    have hrat : M 1 / M 0 ≤ M (n + 1) / M n := hM.ratio_mono (Nat.zero_le n)
    rw [hM.2.1, div_one, le_div_iff₀ (hM.1 n)] at hrat
    calc
      (M 1) ^ (n + 1) = (M 1) ^ n * M 1 := pow_succ (M 1) n
      _ ≤ M n * M 1 := mul_le_mul_of_nonneg_right ih (hM.1 1).le
      _ = M 1 * M n := mul_comm _ _
      _ ≤ M (n + 1) := hrat

/-- Log-convexity implies supermultiplicativity `M_j * M_k ≤ M_{j + k}` for all `j, k : ℕ`. -/
theorem IsPosNormLogConvex.mul_le_add {M : ℕ → ℝ} (hM : IsPosNormLogConvex M) (j k : ℕ) :
    M j * M k ≤ M (j + k) := by
  induction j with
  | zero => simp [hM.2.1]
  | succ j ih =>
    have hrat : M (j + 1) / M j ≤ M (j + k + 1) / M (j + k) :=
      hM.ratio_mono (Nat.le_add_right j k)
    rw [div_le_div_iff₀ (hM.1 j) (hM.1 (j + k))] at hrat
    have h1 : M j * (M (j + 1) * M k) ≤ M j * M (j + 1 + k) := by
      calc
        M j * (M (j + 1) * M k)
          = M (j + 1) * (M j * M k) := by ring
        _ ≤ M (j + 1) * M (j + k) := mul_le_mul_of_nonneg_left ih (hM.1 (j + 1)).le
        _ ≤ M (j + k + 1) * M j := hrat
        _ = M j * M (j + 1 + k) := by
            rw [mul_comm]
            congr 2
            omega
    exact le_of_mul_le_mul_left h1 (hM.1 j)

/-- Log-convexity inequality `M_j * M_{n - j} ≤ M_n` for `0 ≤ j ≤ n` (RCA eq. 19.7(1), p. 378). -/
theorem IsPosNormLogConvex.mul_sub_le {M : ℕ → ℝ} (hM : IsPosNormLogConvex M)
    {n j : ℕ} (hj : j ≤ n) :
    M j * M (n - j) ≤ M n := by
  simpa [Nat.add_sub_of_le hj] using hM.mul_le_add j (n - j)

end LogConvexHelpers

/-- **Hazard 19.6b (`node19_6_regularization_counterexample`, `SCOPING-H-19-20.md` §hazard 8):**
Rudin p. 378 asserts without qualification that every class `C{M_n}` defined by a positive sequence
`M_n > 0` equals `C{N_n}` for some positive normalized log-convex sequence `N_n`.
Taking `M_bad(n) = exp(-n^2)` and `f₀(x) = exp(i x)`:
1. `M_bad(n) > 0` for all `n` and `M_bad(0) = 1`;
2. `f₀ ∉ CM M_bad`;
3. for EVERY positive normalized log-convex sequence `N`, `f₀ ∈ CM N`, hence `CM M_bad ≠ CM N`;
4. consequently the unrestricted positive log-convex regularization claim is false. -/
theorem node19_6_regularization_counterexample :
    let M_bad : ℕ → ℝ := fun n => Real.exp (-(n : ℝ) ^ 2)
    let f₀ : ℝ → ℂ := fun x => Complex.exp (Complex.I * (x : ℂ))
    ((∀ n : ℕ, 0 < M_bad n) ∧ M_bad 0 = 1) ∧
    f₀ ∉ CM M_bad ∧
    (∀ N : ℕ → ℝ, IsPosNormLogConvex N → f₀ ∈ CM N ∧ CM M_bad ≠ CM N) ∧
    ¬ (∀ M : ℕ → ℝ, (∀ n : ℕ, 0 < M n) → ∃ N : ℕ → ℝ, IsPosNormLogConvex N ∧ CM M = CM N) := by
  let M_bad : ℕ → ℝ := fun n => Real.exp (-(n : ℝ) ^ 2)
  let f₀ : ℝ → ℂ := fun x => Complex.exp (Complex.I * (x : ℂ))
  have hf₀_cd : ContDiff ℝ ∞ f₀ := by
    simpa [f₀] using contDiff_exp_I_mul_real 1
  have hf₀_norm : ∀ n : ℕ, ∀ x : ℝ, ‖iteratedDeriv n f₀ x‖ = 1 := by
    intro n x
    have hd := iteratedDeriv_exp_I_mul_real 1 n x
    simp only [Complex.ofReal_one, mul_one] at hd
    change ‖iteratedDeriv n (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ))) x‖ = 1
    rw [hd, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
      show Complex.I * (x : ℂ) = ((x : ℝ) : ℂ) * Complex.I from mul_comm _ _,
      Complex.norm_exp_ofReal_mul_I]
  have hM_pos : ∀ n : ℕ, 0 < M_bad n := fun n => Real.exp_pos _
  have hM_zero : M_bad 0 = 1 := by simp [M_bad]
  have hf₀_not_mem : f₀ ∉ CM M_bad := by
    rintro ⟨_, β, hβ, B, hB, hbd⟩
    obtain ⟨K, hK⟩ := exists_nat_gt (max 1 (|Real.log β| + |Real.log B|))
    have hK1 : (1 : ℝ) < K := lt_of_le_of_lt (le_max_left _ _) hK
    have hKab : |Real.log β| + |Real.log B| < K := lt_of_le_of_lt (le_max_right _ _) hK
    let n : ℕ := 2 * K
    have hn_bd := hbd n 0
    rw [hf₀_norm n 0] at hn_bd
    have hexp_eq : β * B ^ n * M_bad n =
        Real.exp (Real.log β + (n : ℝ) * Real.log B - (n : ℝ) ^ 2) := by
      dsimp [M_bad]
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log hβ,
        Real.exp_nat_mul, Real.exp_log hB]
    rw [hexp_eq, ← Real.exp_zero, Real.exp_le_exp] at hn_bd
    have hlogβ : Real.log β ≤ |Real.log β| := le_abs_self _
    have hlogB : (n : ℝ) * Real.log B ≤ (n : ℝ) * |Real.log B| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg n)
    have hn_cast : (n : ℝ) = 2 * (K : ℝ) := by dsimp [n]; push_cast; ring
    have hcontra : Real.log β + (n : ℝ) * Real.log B - (n : ℝ) ^ 2 < 0 := by
      have h1 : Real.log β + (n : ℝ) * Real.log B ≤ (K : ℝ) + 2 * (K : ℝ) * (K : ℝ) := by
        have hB_le : |Real.log B| ≤ K := by
          have := abs_nonneg (Real.log β); linarith
        have hβ_le : Real.log β ≤ K := by
          have := abs_nonneg (Real.log B); linarith
        rw [hn_cast]
        nlinarith
      rw [hn_cast]
      nlinarith
    linarith
  have hN_mem : ∀ N : ℕ → ℝ, IsPosNormLogConvex N → f₀ ∈ CM N ∧ CM M_bad ≠ CM N := by
    intro N hN
    have hmem : f₀ ∈ CM N := by
      refine ⟨hf₀_cd, 1, zero_lt_one, (N 1)⁻¹, inv_pos.mpr (hN.1 1), fun n x => ?_⟩
      rw [hf₀_norm n x, one_mul, inv_pow]
      have hpow : (N 1) ^ n ≤ N n := hN.pow_one_le n
      have hpos : 0 < (N 1) ^ n := pow_pos (hN.1 1) n
      calc
        (1 : ℝ) = ((N 1) ^ n)⁻¹ * (N 1) ^ n := (inv_mul_cancel₀ hpos.ne').symm
        _ ≤ ((N 1) ^ n)⁻¹ * N n := mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hpos.le)
    refine ⟨hmem, ?_⟩
    intro heq
    exact hf₀_not_mem (heq ▸ hmem)
  refine ⟨⟨hM_pos, hM_zero⟩, hf₀_not_mem, hN_mem, ?_⟩
  intro hall
  obtain ⟨N, hN, heq⟩ := hall M_bad hM_pos
  exact (hN_mem N hN).2 heq

/-- **Hazard 19.6b (`node19_6_regularization_necessary_exp_lower_bound`,
`SCOPING-H-19-20.md` §hazard 8):**
For any positive sequence `M_n > 0`:
1. `exp(i ·) ∈ CM M` if and only if `M` admits an exponential lower bound `c * r^n ≤ M_n` for some
   `c > 0`, `r > 0`;
2. consequently, a necessary condition for `CM M = CM N` for some positive normalized log-convex
   `N` is `∃ c > 0, ∃ r > 0, ∀ n : ℕ, c * r^n ≤ M_n`. -/
theorem node19_6_regularization_necessary_exp_lower_bound {M : ℕ → ℝ}
    (_ : ∀ n : ℕ, 0 < M n) :
    ((fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) ∈ CM M ↔
      ∃ c > 0, ∃ r > 0, ∀ n : ℕ, c * r ^ n ≤ M n) ∧
    ((∃ N : ℕ → ℝ, IsPosNormLogConvex N ∧ CM M = CM N) →
      ∃ c > 0, ∃ r > 0, ∀ n : ℕ, c * r ^ n ≤ M n) := by
  let f₀ : ℝ → ℂ := fun x => Complex.exp (Complex.I * (x : ℂ))
  have hf₀_cd : ContDiff ℝ ∞ f₀ := by
    simpa [f₀] using contDiff_exp_I_mul_real 1
  have hf₀_norm : ∀ n : ℕ, ∀ x : ℝ, ‖iteratedDeriv n f₀ x‖ = 1 := by
    intro n x
    have hd := iteratedDeriv_exp_I_mul_real 1 n x
    simp only [Complex.ofReal_one, mul_one] at hd
    change ‖iteratedDeriv n (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ))) x‖ = 1
    rw [hd, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
      show Complex.I * (x : ℂ) = ((x : ℝ) : ℂ) * Complex.I from mul_comm _ _,
      Complex.norm_exp_ofReal_mul_I]
  have hiff : f₀ ∈ CM M ↔ ∃ c > 0, ∃ r > 0, ∀ n : ℕ, c * r ^ n ≤ M n := by
    constructor
    · rintro ⟨_, β, hβ, B, hB, hbd⟩
      refine ⟨β⁻¹, inv_pos.mpr hβ, B⁻¹, inv_pos.mpr hB, fun n => ?_⟩
      have h0 := hbd n 0
      rw [hf₀_norm n 0] at h0
      have hpos : 0 < β * B ^ n := mul_pos hβ (pow_pos hB n)
      rw [inv_pow, ← mul_inv]
      exact (inv_le_iff_one_le_mul₀' hpos).mpr h0
    · rintro ⟨c, hc, r, hr, hle⟩
      refine ⟨hf₀_cd, c⁻¹, inv_pos.mpr hc, r⁻¹, inv_pos.mpr hr, fun n x => ?_⟩
      rw [hf₀_norm n x, inv_pow, ← mul_inv]
      have hpos : 0 < c * r ^ n := mul_pos hc (pow_pos hr n)
      calc
        (1 : ℝ) = (c * r ^ n)⁻¹ * (c * r ^ n) := (inv_mul_cancel₀ hpos.ne').symm
        _ ≤ (c * r ^ n)⁻¹ * M n := mul_le_mul_of_nonneg_left (hle n) (inv_nonneg.mpr hpos.le)
  refine ⟨hiff, ?_⟩
  rintro ⟨N, hN, heq⟩
  apply hiff.mp
  rw [heq]
  have hN_mem := (node19_6_regularization_counterexample.2.2.1 N hN).1
  exact hN_mem

/-- **Node 19.6 (Summary theorem for `C{M_n}`, RCA pp. 377–378, with Hazards 19.6a & 19.6b
resolved):**
1. `limsup` characterization of `CM M`;
2. `ℂ`-vector-space closure (`0`, `+`, `•`);
3. corrected affine invariance (`|a| * B` for `a ≠ 0`, `max 1 |a| * B` for all `a, b : ℝ`);
4. `M_0 = 1` rescaling invariance `CM (fun n => M n / M 0) = CM M`;
5. Hazard 19.6a counterexample to Rudin's unguarded `a * B` witness when `a < 0`;
6. Hazard 19.6b counterexample (`M_n = exp(-n^2)`) to unrestricted positive log-convex
   regularization and necessary exponential lower bound `c * r^n ≤ M_n`. -/
theorem theorem19_6 {M : ℕ → ℝ} (hM : ∀ n : ℕ, 0 < M n) :
    (∀ f : ℝ → ℂ, ContDiff ℝ ∞ f →
      (f ∈ CM M ↔
        (∀ n : ℕ, BddAbove (Set.range fun x : ℝ => ‖iteratedDeriv n f x‖)) ∧
        Filter.limsup
          (fun n : ℕ =>
            ENNReal.ofReal (((⨆ x : ℝ, ‖iteratedDeriv n f x‖) / M n) ^ (1 / (n : ℝ))))
          atTop < ⊤)) ∧
    ((0 : ℝ → ℂ) ∈ CM M ∧
      (∀ f ∈ CM M, ∀ g ∈ CM M, f + g ∈ CM M) ∧
      (∀ (c : ℂ), ∀ f ∈ CM M, c • f ∈ CM M)) ∧
    (∀ f ∈ CM M, ∀ a b : ℝ, (fun x : ℝ => f (a * x + b)) ∈ CM M) ∧
    CM (fun n : ℕ => M n / M 0) = CM M ∧
    ((∃ N : ℕ → ℝ, IsPosNormLogConvex N ∧ CM M = CM N) →
      ∃ c > 0, ∃ r > 0, ∀ n : ℕ, c * r ^ n ≤ M n) :=
  ⟨fun _ hf => mem_CM_iff_limsup hM hf,
   ⟨zero_mem_CM hM, fun _ hf _ hg => add_mem_CM hM hf hg, fun c _ hf => smul_mem_CM c hf⟩,
   fun _ hf a b => CM_comp_affine hM hf a b,
   CM_div_zero hM,
   (node19_6_regularization_necessary_exp_lower_bound hM).2⟩

/-! ## §19.7: Pointwise Multiplication and Algebra Structure of `C{M_n}` (RCA p. 378) -/

/-- Explicit Leibniz bound for `f * g` under positive normalized log-convex `M`: witnesses
`β_{fg} = β_f * β_g` and `B_{fg} = B_f + B_g`. -/
theorem CM_mul_explicit_bound {M : ℕ → ℝ} (hM : IsPosNormLogConvex M)
    {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {β_f B_f β_g B_g : ℝ}
    (hβf : 0 < β_f) (hBf : 0 < B_f) (hβg : 0 < β_g) (hBg : 0 < B_g)
    (hf_bd : ∀ n : ℕ, ∀ x : ℝ, ‖iteratedDeriv n f x‖ ≤ β_f * B_f ^ n * M n)
    (hg_bd : ∀ n : ℕ, ∀ x : ℝ, ‖iteratedDeriv n g x‖ ≤ β_g * B_g ^ n * M n) :
    ContDiff ℝ ∞ (f * g) ∧
    ∀ n : ℕ, ∀ x : ℝ,
      ‖iteratedDeriv n (f * g) x‖ ≤ (β_f * β_g) * (B_f + B_g) ^ n * M n := by
  refine ⟨hf.mul hg, fun n x => ?_⟩
  have hleib := iteratedDeriv_mul
    ((contDiff_infty.mp hf n).contDiffAt) ((contDiff_infty.mp hg n).contDiffAt) (x := x)
  rw [hleib]
  calc
    ‖∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℂ) * iteratedDeriv j f x * iteratedDeriv (n - j) g x‖
      ≤ ∑ j ∈ Finset.range (n + 1),
          ‖(n.choose j : ℂ) * iteratedDeriv j f x * iteratedDeriv (n - j) g x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1),
          (β_f * β_g) * (B_f ^ j * B_g ^ (n - j) * (n.choose j : ℝ)) * M n := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj_le : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [norm_mul, norm_mul, Complex.norm_natCast]
        calc
          (n.choose j : ℝ) * ‖iteratedDeriv j f x‖ * ‖iteratedDeriv (n - j) g x‖
            ≤ (n.choose j : ℝ) * (β_f * B_f ^ j * M j) * (β_g * B_g ^ (n - j) * M (n - j)) := by
              exact mul_le_mul
                (mul_le_mul_of_nonneg_left (hf_bd j x) (Nat.cast_nonneg _))
                (hg_bd (n - j) x) (norm_nonneg _) (by positivity [hM.1 j])
          _ = (β_f * β_g) * (B_f ^ j * B_g ^ (n - j) * (n.choose j : ℝ)) *
                (M j * M (n - j)) := by ring
          _ ≤ (β_f * β_g) * (B_f ^ j * B_g ^ (n - j) * (n.choose j : ℝ)) * M n := by
              exact mul_le_mul_of_nonneg_left (hM.mul_sub_le hj_le) (by positivity)
    _ = (β_f * β_g) *
          (∑ j ∈ Finset.range (n + 1), B_f ^ j * B_g ^ (n - j) * (n.choose j : ℝ)) * M n := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = (β_f * β_g) * (B_f + B_g) ^ n * M n := by
        rw [← add_pow B_f B_g n]

theorem mul_mem_CM {M : ℕ → ℝ} (hM : IsPosNormLogConvex M) {f g : ℝ → ℂ}
    (hf : f ∈ CM M) (hg : g ∈ CM M) :
    f * g ∈ CM M := by
  rcases hf with ⟨hf_cd, β_f, hβf, B_f, hBf, hf_bd⟩
  rcases hg with ⟨hg_cd, β_g, hβg, B_g, hBg, hg_bd⟩
  have h := CM_mul_explicit_bound hM hf_cd hg_cd hβf hBf hβg hBg hf_bd hg_bd
  exact ⟨h.1, β_f * β_g, mul_pos hβf hβg, B_f + B_g, add_pos hBf hBg, h.2⟩

theorem const_mem_CM {M : ℕ → ℝ} (hM : IsPosNormLogConvex M) (c : ℂ) :
    (fun _ : ℝ => c) ∈ CM M := by
  refine ⟨contDiff_const, ‖c‖ + 1, by positivity, 1, zero_lt_one, fun n x => ?_⟩
  rw [iteratedDeriv_const]
  split_ifs with hn
  · subst hn
    rw [pow_zero, mul_one, hM.2.1, mul_one]
    linarith
  · rw [norm_zero]
    exact le_of_lt (by positivity [hM.1 n])

/-- **Node 19.7 (`CMSubalgebra`, RCA p. 378):**
Under positive normalized log-convexity of `M`, `CM M` is a unital `ℂ`-subalgebra of `ℝ → ℂ`. -/
def CMSubalgebra (M : ℕ → ℝ) (hM : IsPosNormLogConvex M) : Subalgebra ℂ (ℝ → ℂ) where
  carrier := CM M
  mul_mem' hf hg := mul_mem_CM hM hf hg
  one_mem' := const_mem_CM hM 1
  add_mem' hf hg := add_mem_CM hM.1 hf hg
  zero_mem' := zero_mem_CM hM.1
  algebraMap_mem' c := const_mem_CM hM c

/-- **Theorem 19.7 (Algebra Closure of `C{M_n}`, RCA p. 378):**
If `M` is positive, normalized (`M_0 = 1`), and log-convex (`M_n^2 ≤ M_{n-1} M_{n+1}` for `n ≥ 1`),
then `M_j M_{n-j} ≤ M_n` for `0 ≤ j ≤ n`, `C{M_n}` is closed under pointwise multiplication with
explicit witnesses `(β_f β_g, B_f + B_g)`, and `C{M_n}` forms an algebra over `ℂ` with respect to
pointwise multiplication. -/
theorem theorem19_7 {M : ℕ → ℝ} (hM : IsPosNormLogConvex M) :
    (∀ n j : ℕ, j ≤ n → M j * M (n - j) ≤ M n) ∧
    (∀ {f g : ℝ → ℂ} {β_f B_f β_g B_g : ℝ},
      ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      0 < β_f → 0 < B_f → 0 < β_g → 0 < B_g →
      (∀ n x, ‖iteratedDeriv n f x‖ ≤ β_f * B_f ^ n * M n) →
      (∀ n x, ‖iteratedDeriv n g x‖ ≤ β_g * B_g ^ n * M n) →
      ContDiff ℝ ∞ (f * g) ∧
      ∀ n x, ‖iteratedDeriv n (f * g) x‖ ≤ (β_f * β_g) * (B_f + B_g) ^ n * M n) ∧
    (∀ f ∈ CM M, ∀ g ∈ CM M, f * g ∈ CM M) ∧
    (∀ c : ℂ, (fun _ : ℝ => c) ∈ CM M) :=
  ⟨fun _ _ hj => hM.mul_sub_le hj,
   fun hf hg hβf hBf hβg hBg hf_bd hg_bd =>
     CM_mul_explicit_bound hM hf hg hβf hBf hβg hBg hf_bd hg_bd,
   fun _ hf _ hg => mul_mem_CM hM hf hg,
   const_mem_CM hM⟩

/-! ## §19.8: Quasi-Analytic Classes and Base-Point Invariance (RCA p. 378) -/

/-- **Node 19.8 (`IsQuasiAnalytic`, RCA p. 378):**
A class `C{M_n}` is *quasi-analytic* if every `f ∈ C{M_n}` satisfying `D^n f(0) = 0` for all
`n : ℕ` vanishes identically on `ℝ`. -/
def IsQuasiAnalytic (M : ℕ → ℝ) : Prop :=
  ∀ f ∈ CM M, (∀ n : ℕ, iteratedDeriv n f 0 = 0) → ∀ x : ℝ, f x = 0

/-- **Node 19.8 (Base-Point Invariance of Quasi-Analyticity, RCA p. 378):**
Replacing `0` by any fixed real point `x₀ : ℝ` yields an equivalent definition of
`IsQuasiAnalytic M`. -/
theorem theorem19_8 (M : ℕ → ℝ) (x₀ : ℝ) :
    IsQuasiAnalytic M ↔
      ∀ f ∈ CM M, (∀ n : ℕ, iteratedDeriv n f x₀ = 0) → ∀ x : ℝ, f x = 0 := by
  constructor
  · intro hQA f hf hderiv x
    let g : ℝ → ℂ := fun t => f (t + x₀)
    have hg_CM : g ∈ CM M := CM_comp_add_right hf x₀
    have hg_deriv : ∀ n : ℕ, iteratedDeriv n g 0 = 0 := by
      intro n
      have h_eq : g = fun t : ℝ => f (1 * t + x₀) := by ext t; dsimp [g]; congr 1; ring
      rw [h_eq, iteratedDeriv_comp_affine hf.1 1 x₀ n 0, one_pow, one_smul, mul_zero, zero_add]
      exact hderiv n
    have h0 := hQA g hg_CM hg_deriv (x - x₀)
    simpa [g] using h0
  · intro hQA_x₀ f hf hderiv x
    let g : ℝ → ℂ := fun t => f (t + (-x₀))
    have hg_CM : g ∈ CM M := CM_comp_add_right hf (-x₀)
    have hg_deriv : ∀ n : ℕ, iteratedDeriv n g x₀ = 0 := by
      intro n
      have h_eq : g = fun t : ℝ => f (1 * t + (-x₀)) := by ext t; dsimp [g]; congr 1; ring
      rw [h_eq, iteratedDeriv_comp_affine hf.1 1 (-x₀) n x₀, one_pow, one_smul, one_mul,
        add_neg_cancel]
      exact hderiv n
    have h0 := hQA_x₀ g hg_CM hg_deriv (x + x₀)
    simpa [g] using h0

/-! ## §19.9: Characterization & Quasi-Analyticity of `C{n!}` (RCA pp. 378–379) -/

section Node19_9_Helpers

/-- Restriction of complex iterated derivatives to the real axis inside an open domain `U ⊆ ℂ`. -/
lemma holomorphic_iteratedDeriv_comp_ofReal {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) (n : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv n F) U ∧
    ∀ x : ℝ, (x : ℂ) ∈ U → iteratedDeriv n (fun t : ℝ => F t) x = iteratedDeriv n F (x : ℂ) := by
  induction n with
  | zero => exact ⟨hF, fun _ _ => rfl⟩
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · rw [iteratedDeriv_succ]
      exact ih.1.deriv hU
    · intro x hx
      have hV : (((↑) : ℝ → ℂ) ⁻¹' U) ∈ 𝓝 x :=
        (hU.preimage Complex.continuous_ofReal).mem_nhds hx
      have hev : iteratedDeriv n (fun t : ℝ => F t) =ᶠ[𝓝 x]
          (fun y : ℝ => iteratedDeriv n F (y : ℂ)) := by
        filter_upwards [hV] with y hy
        exact ih.2 y hy
      have hd_cplx : HasDerivAt (iteratedDeriv n F) (deriv (iteratedDeriv n F) (x : ℂ)) (x : ℂ) :=
        (ih.1.differentiableAt (hU.mem_nhds hx)).hasDerivAt
      have hd_real : HasDerivAt (iteratedDeriv n (fun t : ℝ => F t))
          (deriv (iteratedDeriv n F) (x : ℂ)) x :=
        hd_cplx.comp_ofReal.congr_of_eventuallyEq hev
      rw [iteratedDeriv_succ, iteratedDeriv_succ, hd_real.deriv]

/-- Integral Taylor remainder formula on `ℝ` using global `iteratedDeriv` for smooth `f : ℝ → ℂ`. -/
lemma smooth_taylor_integral_remainder {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (a x : ℝ) (n : ℕ) :
    f x - ∑ k ∈ Finset.range (n + 1),
        (iteratedDeriv k f a / (k.factorial : ℂ)) * ((x : ℂ) - (a : ℂ)) ^ k =
      ∫ t in a..x,
        ((((x - t) ^ n / (n.factorial : ℝ)) : ℝ) : ℂ) * iteratedDeriv (n + 1) f t := by
  induction n with
  | zero =>
    simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one,
      div_one, pow_zero, mul_one, zero_add, iteratedDeriv_zero, Complex.ofReal_one, one_mul]
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := f) (f' := iteratedDeriv 1 f) (a := a) (b := x)
      (fun t _ => by
        rw [iteratedDeriv_one]
        exact ((differentiable_iteratedDeriv_of_infty hf 0) t).hasDerivAt)
      ((continuous_iteratedDeriv_of_infty hf 1).intervalIntegrable _ _)
    exact hftc.symm
  | succ n ih =>
    let u : ℝ → ℂ := fun t => (((-(x - t) ^ (n + 1) / ((n + 1).factorial : ℝ)) : ℝ) : ℂ)
    let u' : ℝ → ℂ := fun t => ((((x - t) ^ n / (n.factorial : ℝ)) : ℝ) : ℂ)
    let v : ℝ → ℂ := iteratedDeriv (n + 1) f
    let v' : ℝ → ℂ := iteratedDeriv (n + 2) f
    have hu_deriv : ∀ t : ℝ, HasDerivAt u (u' t) t := by
      intro t
      have hsub : HasDerivAt (fun s : ℝ => x - s) (0 - 1) t :=
        (hasDerivAt_const t x).fun_sub (hasDerivAt_id t)
      have hpow : HasDerivAt (fun s : ℝ => (x - s) ^ (n + 1))
          (((n + 1 : ℕ) : ℝ) * (x - t) ^ (n + 1 - 1) * (0 - 1)) t :=
        hsub.fun_pow (n + 1)
      have hreal : HasDerivAt (fun s : ℝ => -(x - s) ^ (n + 1) / ((n + 1).factorial : ℝ))
          ((x - t) ^ n / (n.factorial : ℝ)) t := by
        refine (hpow.neg.div_const ((n + 1).factorial : ℝ)).congr_deriv ?_
        simp only [Nat.add_sub_cancel, zero_sub]
        rw [Nat.factorial_succ, Nat.cast_mul]
        have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hn1]
      exact (Complex.ofRealCLM.hasDerivAt.scomp t hreal).congr_deriv (by simp [u'])
    have hv_deriv : ∀ t : ℝ, HasDerivAt v (v' t) t := by
      intro t
      have hv_eq : v' = deriv v := iteratedDeriv_succ (n := n + 1) (f := f)
      rw [hv_eq]
      exact ((differentiable_iteratedDeriv_of_infty hf (n + 1)) t).hasDerivAt
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := u) (v := v) (u' := u') (v' := v') (a := a) (b := x)
      (fun t _ => hu_deriv t) (fun t _ => hv_deriv t)
      (( Continuous.intervalIntegrable (by dsimp [u']; fun_prop) _ _ ))
      ((continuous_iteratedDeriv_of_infty hf (n + 2)).intervalIntegrable _ _)
    have hux : u x = 0 := by simp [u]
    have hua : u a = -((((x - a) ^ (n + 1) / ((n + 1).factorial : ℝ)) : ℝ) : ℂ) := by
      dsimp [u]; push_cast; ring
    have h_int_eq : (∫ t in a..x, u' t * v t) =
        (iteratedDeriv (n + 1) f a / ((n + 1).factorial : ℂ)) * ((x : ℂ) - (a : ℂ)) ^ (n + 1) +
          ∫ t in a..x, (-u t) * v' t := by
      have h1 : (∫ t in a..x, u' t * v t) =
          (u x * v x - u a * v a) - ∫ t in a..x, u t * v' t := by
        have hcomm1 : (∫ t in a..x, u' t * v t) = ∫ t in a..x, v t * u' t := by
          refine intervalIntegral.integral_congr fun t _ => mul_comm _ _
        rw [hcomm1]
        have hibp' := intervalIntegral.integral_mul_deriv_eq_deriv_mul
          (u := v) (v := u) (u' := v') (v' := u') (a := a) (b := x)
          (fun t _ => hv_deriv t) (fun t _ => hu_deriv t)
          ((continuous_iteratedDeriv_of_infty hf (n + 2)).intervalIntegrable _ _)
          ((Continuous.intervalIntegrable (by dsimp [u']; fun_prop) _ _))
        rw [hibp']
        congr 1
        · ring
        · refine intervalIntegral.integral_congr fun t _ => mul_comm _ _
      rw [h1, hux, zero_mul, zero_sub, hua]
      have hneg_int : -(∫ t in a..x, u t * v' t) = ∫ t in a..x, (-u t) * v' t := by
        rw [← intervalIntegral.integral_neg]
        refine intervalIntegral.integral_congr fun t _ => by ring
      rw [sub_eq_add_neg, hneg_int]
      congr 1
      dsimp [v]
      push_cast
      ring
    have hneg_u : ∀ t : ℝ, -u t = ((((x - t) ^ (n + 1) / ((n + 1).factorial : ℝ)) : ℝ) : ℂ) := by
      intro t; dsimp [u]; push_cast; ring
    rw [Finset.sum_range_succ, ← sub_sub, ih, h_int_eq]
    simp only [hneg_u, v']
    ring

/-- Elementary limit `(n + 1) * q ^ (n + 1) → 0` as `n → ∞` for `0 ≤ q < 1`. -/
lemma tendsto_succ_mul_pow_zero_of_lt_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * q ^ (n + 1)) atTop (𝓝 0) := by
  rcases eq_or_lt_of_le hq0 with rfl | hq_pos
  · simp
  · let r : ℝ := (q + 1) / 2
    have hqr : q < r := by dsimp [r]; linarith
    have hr1 : r < 1 := by dsimp [r]; linarith
    have hr0 : 0 < r := lt_trans hq_pos hqr
    let η : ℝ := r / q - 1
    have hη_pos : 0 < η := by
      dsimp [η]
      linarith [(one_lt_div hq_pos).mpr hqr]
    have hbound : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * q ^ (n + 1) ≤ (1 / η) * r ^ (n + 1) := by
      intro n
      have hbern : 1 + ((n + 1 : ℕ) : ℝ) * η ≤ (1 + η) ^ (n + 1) :=
        one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ η) (n + 1)
      have h1η : 1 + η = r / q := by dsimp [η]; ring
      rw [h1η, div_pow] at hbern
      have hmul : ((n + 1 : ℕ) : ℝ) * η * q ^ (n + 1) ≤ r ^ (n + 1) := by
        have hqp : 0 < q ^ (n + 1) := pow_pos hq_pos (n + 1)
        have := (le_div_iff₀ hqp).mp (by linarith : ((n + 1 : ℕ) : ℝ) * η ≤ r ^ (n + 1) / q ^ (n + 1))
        exact this
      have : η * (((n + 1 : ℕ) : ℝ) * q ^ (n + 1)) ≤ r ^ (n + 1) := by linarith
      calc
        ((n + 1 : ℕ) : ℝ) * q ^ (n + 1)
          = (1 / η) * (η * (((n + 1 : ℕ) : ℝ) * q ^ (n + 1))) := by field_simp [hη_pos.ne']
        _ ≤ (1 / η) * r ^ (n + 1) := mul_le_mul_of_nonneg_left this (by positivity)
    have hlim_r : Tendsto (fun n : ℕ => (1 / η) * r ^ (n + 1)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul
        ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).comp (tendsto_add_atTop_nat 1))
    exact squeeze_zero (fun n => by positivity) hbound hlim_r

end Node19_9_Helpers

/-- **Theorem 19.9 (Strip Characterization & Quasi-Analyticity of `C{n!}`, RCA pp. 378–379):**
1. A function `f : ℝ → ℂ` belongs to `C{n!}` if and only if there exist `b > 0`, `K > 0`, and a
   function `F : ℂ → ℂ` holomorphic and bounded by `K` on the horizontal strip `{z : ℂ | |z.im| < b}`
   whose restriction to `ℝ` equals `f`.
2. Consequently, `C{n!}` is quasi-analytic. -/
theorem theorem19_9 :
    (∀ f : ℝ → ℂ,
      f ∈ CM (fun n : ℕ => (n.factorial : ℝ)) ↔
        ∃ b > 0, ∃ K > 0, ∃ F : ℂ → ℂ,
          DifferentiableOn ℂ F {z : ℂ | |z.im| < b} ∧
          (∀ z : ℂ, |z.im| < b → ‖F z‖ ≤ K) ∧
          (∀ x : ℝ, f x = F x)) ∧
    IsQuasiAnalytic (fun n : ℕ => (n.factorial : ℝ)) := by
  have hchar : ∀ f : ℝ → ℂ,
      f ∈ CM (fun n : ℕ => (n.factorial : ℝ)) ↔
        ∃ b > 0, ∃ K > 0, ∃ F : ℂ → ℂ,
          DifferentiableOn ℂ F {z : ℂ | |z.im| < b} ∧
          (∀ z : ℂ, |z.im| < b → ‖F z‖ ≤ K) ∧
          (∀ x : ℝ, f x = F x) := by
    intro f
    constructor
    · -- Forward: f ∈ C{n!} → bounded holomorphic extension to {|Im z| < 1 / (2 B)}
      rintro ⟨hf_cd, β, hβ, B, hB, hbd⟩
      let b : ℝ := 1 / (2 * B)
      let K : ℝ := 2 * β
      have hb_pos : 0 < b := by dsimp [b]; positivity
      have hK_pos : 0 < K := by dsimp [K]; positivity
      let R : ℝ := 1 / B
      have hR_pos : 0 < R := one_div_pos.mpr hB
      -- Local Taylor power series centered at a : ℝ
      let term : ℝ → ℕ → ℂ → ℂ :=
        fun a n z => (iteratedDeriv n f a / (n.factorial : ℂ)) * (z - (a : ℂ)) ^ n
      let P : ℝ → ℂ → ℂ := fun a z => ∑' n : ℕ, term a n z
      have hterm_norm : ∀ (a : ℝ) (n : ℕ) (z : ℂ),
          ‖term a n z‖ ≤ β * (B * ‖z - (a : ℂ)‖) ^ n := by
        intro a n z
        dsimp [term]
        rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow]
        have hn_pos : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
        have h1 : ‖iteratedDeriv n f a‖ / (n.factorial : ℝ) ≤ β * B ^ n :=
          (div_le_iff₀ hn_pos).mpr (hbd n a)
        calc
          (‖iteratedDeriv n f a‖ / (n.factorial : ℝ)) * ‖z - (a : ℂ)‖ ^ n
            ≤ (β * B ^ n) * ‖z - (a : ℂ)‖ ^ n :=
              mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg _) n)
          _ = β * (B * ‖z - (a : ℂ)‖) ^ n := by rw [mul_pow]; ring
      -- Holomorphy of P a on Metric.ball (a : ℂ) R
      have hP_diff : ∀ a : ℝ, DifferentiableOn ℂ (P a) (Metric.ball (a : ℂ) R) := by
        intro a z₀ hz₀
        rw [Metric.mem_ball, dist_eq_norm] at hz₀
        let r : ℝ := (‖z₀ - (a : ℂ)‖ + R) / 2
        have hz₀_r : z₀ ∈ Metric.ball (a : ℂ) r := by
          rw [Metric.mem_ball, dist_eq_norm]; dsimp [r]; linarith
        have hrR : r < R := by dsimp [r]; linarith
        have hr_nonneg : 0 ≤ r := by
          have := norm_nonneg (z₀ - (a : ℂ)); dsimp [r]; linarith
        have hBr_lt : B * r < 1 := by
          calc
            B * r < B * R := mul_lt_mul_of_pos_left hrR hB
            _ = 1 := by dsimp [R]; exact mul_one_div_cancel hB.ne'
        have hu_sum : Summable (fun n : ℕ => β * (B * r) ^ n) :=
          (summable_geometric_of_lt_one (mul_nonneg hB.le hr_nonneg) hBr_lt).mul_left β
        have hterm_diff : ∀ n : ℕ, DifferentiableOn ℂ (term a n) (Metric.ball (a : ℂ) r) := by
          intro n
          dsimp [term]
          fun_prop
        have h_on_r : DifferentiableOn ℂ (P a) (Metric.ball (a : ℂ) r) := by
          refine differentiableOn_tsum_of_summable_norm hu_sum hterm_diff Metric.isOpen_ball ?_
          intro n w hw
          rw [Metric.mem_ball, dist_eq_norm] at hw
          exact (hterm_norm a n w).trans
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by positivity)
                (mul_le_mul_of_nonneg_left hw.le hB.le) n) hβ.le)
        exact (h_on_r.differentiableAt (Metric.isOpen_ball.mem_nhds hz₀_r)).differentiableWithinAt
      -- Bound ‖P a z‖ ≤ K when ‖z - a‖ ≤ b
      have hP_bound : ∀ (a : ℝ) (z : ℂ), ‖z - (a : ℂ)‖ ≤ b → ‖P a z‖ ≤ K := by
        intro a z hz
        have hBz : B * ‖z - (a : ℂ)‖ ≤ 1 / 2 := by
          calc
            B * ‖z - (a : ℂ)‖ ≤ B * b := mul_le_mul_of_nonneg_left hz hB.le
            _ = 1 / 2 := by dsimp [b]; field_simp [hB.ne']
        have hu_sum : Summable (fun n : ℕ => β * (1 / 2 : ℝ) ^ n) :=
          (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left β
        have hterm_le : ∀ n : ℕ, ‖term a n z‖ ≤ β * (1 / 2 : ℝ) ^ n := by
          intro n
          exact (hterm_norm a n z).trans
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by positivity) hBz n) hβ.le)
        calc
          ‖P a z‖ ≤ ∑' n : ℕ, ‖term a n z‖ := norm_tsum_le_tsum_norm (hu_sum.of_nonneg_of_le
            (fun _ => norm_nonneg _) hterm_le)
          _ ≤ ∑' n : ℕ, β * (1 / 2 : ℝ) ^ n :=
            Summable.tsum_le_tsum hterm_le
              (hu_sum.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le) hu_sum
          _ = β * ∑' n : ℕ, (1 / 2 : ℝ) ^ n := tsum_mul_left
          _ = K := by
            rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
            dsimp [K]; ring
      -- Real agreement P a x = f x for |x - a| < R
      have hP_real : ∀ (a x : ℝ), |x - a| < R → P a (x : ℂ) = f x := by
        intro a x hxa
        let q : ℝ := B * |x - a|
        have hq0 : 0 ≤ q := by dsimp [q]; positivity
        have hq1 : q < 1 := by
          calc
            q = B * |x - a| := rfl
            _ < B * R := mul_lt_mul_of_pos_left hxa hB
            _ = 1 := by dsimp [R]; exact mul_one_div_cancel hB.ne'
        have hrem_bd : ∀ n : ℕ,
            ‖f x - ∑ k ∈ Finset.range (n + 1), term a k (x : ℂ)‖ ≤
              β * (((n + 1 : ℕ) : ℝ) * q ^ (n + 1)) := by
          intro n
          rw [smooth_taylor_integral_remainder hf_cd a x n]
          have hconst : ∀ t ∈ Set.uIoc a x,
              ‖((((x - t) ^ n / (n.factorial : ℝ)) : ℝ) : ℂ) * iteratedDeriv (n + 1) f t‖ ≤
                (|x - a| ^ n / (n.factorial : ℝ)) * (β * B ^ (n + 1) * ((n + 1).factorial : ℝ)) := by
            intro t ht
            have ht_cc : t ∈ Set.uIcc a x := Set.uIoc_subset_uIcc ht
            have hxt : |x - t| ≤ |x - a| := by
              rw [Set.mem_uIcc] at ht_cc
              rcases ht_cc with ⟨hat, htx⟩ | ⟨htx, hat⟩
              · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
              · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow,
              abs_of_pos (a := (n.factorial : ℝ)) (Nat.cast_pos.mpr (Nat.factorial_pos n))]
            exact mul_le_mul
              (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hxt n)
                (Nat.cast_nonneg _))
              (hbd (n + 1) t) (norm_nonneg _) (by positivity)
          calc
            ‖∫ t in a..x,
                ((((x - t) ^ n / (n.factorial : ℝ)) : ℝ) : ℂ) * iteratedDeriv (n + 1) f t‖
              ≤ ((|x - a| ^ n / (n.factorial : ℝ)) *
                  (β * B ^ (n + 1) * ((n + 1).factorial : ℝ))) * |x - a| :=
                intervalIntegral.norm_integral_le_of_norm_le_const hconst
            _ = β * (((n + 1 : ℕ) : ℝ) * q ^ (n + 1)) := by
                dsimp [q]
                rw [Nat.factorial_succ, Nat.cast_mul, mul_pow]
                have hnf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
                field_simp [hnf]
                ring
        have hlim0 : Tendsto
            (fun n : ℕ => ‖f x - ∑ k ∈ Finset.range (n + 1), term a k (x : ℂ)‖) atTop (𝓝 0) :=
          squeeze_zero (fun _ => norm_nonneg _) hrem_bd
            (by simpa using tendsto_const_nhds.mul (tendsto_succ_mul_pow_zero_of_lt_one hq0 hq1))
        have hsum_lim : Tendsto
            (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), term a k (x : ℂ)) atTop (𝓝 (f x)) := by
          rw [tendsto_iff_norm_sub_tendsto_zero]
          refine hlim0.congr fun n => ?_
          rw [norm_sub_rev]
        have hsummable : Summable (fun k : ℕ => term a k (x : ℂ)) := by
          refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_left β) ?_
          intro k
          have hnorm_eq : ‖(x : ℂ) - (a : ℂ)‖ = |x - a| := by
            rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          simpa [q, hnorm_eq] using hterm_norm a k (x : ℂ)
        have htsum_lim : Tendsto
            (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), term a k (x : ℂ)) atTop
            (𝓝 (P a (x : ℂ))) :=
          (hsummable.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
        exact tendsto_nhds_unique htsum_lim hsum_lim
      -- Overlap agreement P a₁ z = P a₂ z on ball a₁ R ∩ ball a₂ R
      have hP_overlap : ∀ (a₁ a₂ : ℝ) (z : ℂ),
          z ∈ Metric.ball (a₁ : ℂ) R ∩ Metric.ball (a₂ : ℂ) R → P a₁ z = P a₂ z := by
        intro a₁ a₂ z hz
        let U : Set ℂ := Metric.ball (a₁ : ℂ) R ∩ Metric.ball (a₂ : ℂ) R
        have hU_open : IsOpen U := Metric.isOpen_ball.inter Metric.isOpen_ball
        have hU_preconn : IsPreconnected U :=
          ((convex_ball (a₁ : ℂ) R).inter (convex_ball (a₂ : ℂ) R)).isPreconnected
        have ha_dist : |a₁ - a₂| < 2 * R := by
          have hd : dist (a₁ : ℂ) (a₂ : ℂ) < R + R := by
            calc
              dist (a₁ : ℂ) (a₂ : ℂ) ≤ dist (a₁ : ℂ) z + dist z (a₂ : ℂ) := dist_triangle _ _ _
              _ = dist z (a₁ : ℂ) + dist z (a₂ : ℂ) := by rw [dist_comm (a₁ : ℂ) z]
              _ < R + R := add_lt_add hz.1 hz.2
          have hd_real : dist (a₁ : ℂ) (a₂ : ℂ) = |a₁ - a₂| := by
            rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          linarith
        let m : ℝ := (a₁ + a₂) / 2
        have hm1 : |m - a₁| < R := by
          have : m - a₁ = -(a₁ - a₂) / 2 := by dsimp [m]; ring
          rw [this, abs_div, abs_neg, abs_two]; linarith
        have hm2 : |m - a₂| < R := by
          have : m - a₂ = (a₁ - a₂) / 2 := by dsimp [m]; ring
          rw [this, abs_div, abs_two]; linarith
        have hm_U : (m : ℂ) ∈ U := by
          refine ⟨?_, ?_⟩
          · rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
              Real.norm_eq_abs]
            exact hm1
          · rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
              Real.norm_eq_abs]
            exact hm2
        let hdiff : ℂ → ℂ := fun w => P a₁ w - P a₂ w
        have hh_diff : DifferentiableOn ℂ hdiff U :=
          ((hP_diff a₁).mono Set.inter_subset_left).sub ((hP_diff a₂).mono Set.inter_subset_right)
        have hh_real_zero : (fun t : ℝ => hdiff t) =ᶠ[𝓝 m] 0 := by
          let ε : ℝ := R - |a₁ - a₂| / 2
          have hε_pos : 0 < ε := by dsimp [ε]; linarith
          filter_upwards [Ioo_mem_nhds (by linarith : m - ε < m) (by linarith : m < m + ε)]
            with t ht
          have ht1 : |t - a₁| < R := by
            have htm : |t - m| < ε := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
            have hma : |m - a₁| = |a₁ - a₂| / 2 := by
              have : m - a₁ = -(a₁ - a₂) / 2 := by dsimp [m]; ring
              rw [this, abs_div, abs_neg, abs_two]
            calc
              |t - a₁| = |(t - m) + (m - a₁)| := by congr 1; ring
              _ ≤ |t - m| + |m - a₁| := abs_add_le _ _
              _ < ε + |a₁ - a₂| / 2 := by linarith
              _ = R := by dsimp [ε]; ring
          have ht2 : |t - a₂| < R := by
            have htm : |t - m| < ε := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
            have hma : |m - a₂| = |a₁ - a₂| / 2 := by
              have : m - a₂ = (a₁ - a₂) / 2 := by dsimp [m]; ring
              rw [this, abs_div, abs_two]
            calc
              |t - a₂| = |(t - m) + (m - a₂)| := by congr 1; ring
              _ ≤ |t - m| + |m - a₂| := abs_add_le _ _
              _ < ε + |a₁ - a₂| / 2 := by linarith
              _ = R := by dsimp [ε]; ring
          dsimp [hdiff]
          rw [hP_real a₁ t ht1, hP_real a₂ t ht2, sub_self]
        have hh_deriv0 : ∀ n : ℕ, iteratedDeriv n hdiff (m : ℂ) = 0 := by
          intro n
          rw [← (holomorphic_iteratedDeriv_comp_ofReal hU_open hh_diff n).2 m hm_U,
            hh_real_zero.iteratedDeriv_eq n]
          change iteratedDeriv n (fun _ : ℝ => (0 : ℂ)) m = 0
          rw [iteratedDeriv_const]
          split_ifs <;> rfl
        have hz0 := holomorphic_eq_zero_of_iteratedDeriv_eq_zero
          hU_open hU_preconn hh_diff hm_U hh_deriv0 z hz
        exact sub_eq_zero.mp hz0
      -- Glued extension F z := P z.re z on S := {z | |z.im| < b}
      let F : ℂ → ℂ := fun z => P z.re z
      refine ⟨b, hb_pos, K, hK_pos, F, ?_, ?_, ?_⟩
      · intro z₀ hz₀
        change |z₀.im| < b at hz₀
        let δ : ℝ := 1 / (4 * B)
        have hδ_pos : 0 < δ := by dsimp [δ]; positivity
        have hbR : b = R / 2 := by dsimp [b, R]; ring
        have hδR : δ = R / 4 := by dsimp [δ, R]; ring
        have hz₀_ball : z₀ ∈ Metric.ball (z₀.re : ℂ) R := by
          rw [Metric.mem_ball, dist_eq_norm]
          have hsub : z₀ - (z₀.re : ℂ) = (z₀.im : ℂ) * Complex.I := by
            apply Complex.ext <;> simp
          rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
          linarith
        have hev : F =ᶠ[𝓝 z₀] P z₀.re := by
          filter_upwards [Metric.ball_mem_nhds z₀ hδ_pos] with w hw
          have hw_norm : ‖w - z₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
          have hw_z₀ : w ∈ Metric.ball (z₀.re : ℂ) R := by
            rw [Metric.mem_ball, dist_eq_norm]
            have hz₀_re : ‖z₀ - (z₀.re : ℂ)‖ = |z₀.im| := by
              have hsub : z₀ - (z₀.re : ℂ) = (z₀.im : ℂ) * Complex.I := by
                apply Complex.ext <;> simp
              rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
            calc
              ‖w - (z₀.re : ℂ)‖ = ‖(w - z₀) + (z₀ - (z₀.re : ℂ))‖ := by congr 1; ring
              _ ≤ ‖w - z₀‖ + ‖z₀ - (z₀.re : ℂ)‖ := norm_add_le _ _
              _ = ‖w - z₀‖ + |z₀.im| := by rw [hz₀_re]
              _ < δ + b := add_lt_add hw_norm hz₀
              _ < R := by linarith
          have hw_self : w ∈ Metric.ball (w.re : ℂ) R := by
            rw [Metric.mem_ball, dist_eq_norm]
            have hw_re : ‖w - (w.re : ℂ)‖ = |w.im| := by
              have hsub : w - (w.re : ℂ) = (w.im : ℂ) * Complex.I := by
                apply Complex.ext <;> simp
              rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
            have him_diff : |w.im - z₀.im| ≤ ‖w - z₀‖ := by
              simpa using Complex.abs_im_le_norm (w - z₀)
            rw [hw_re]
            calc
              |w.im| = |(w.im - z₀.im) + z₀.im| := by congr 1; ring
              _ ≤ |w.im - z₀.im| + |z₀.im| := abs_add_le _ _
              _ < δ + b := by linarith
              _ < R := by linarith
          exact hP_overlap w.re z₀.re w ⟨hw_self, hw_z₀⟩
        exact (((hP_diff z₀.re).differentiableAt
          (Metric.isOpen_ball.mem_nhds hz₀_ball)).congr_of_eventuallyEq hev).differentiableWithinAt
      · intro z hz
        have hz_re : ‖z - (z.re : ℂ)‖ ≤ b := by
          have hsub : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
            apply Complex.ext <;> simp
          rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
          exact hz.le
        exact hP_bound z.re z hz_re
      · intro x
        dsimp [F]
        exact (hP_real x x (by simp [hR_pos])).symm
    · -- Reverse: bounded holomorphic F on {|Im z| < b} restricts to f ∈ C{n!}
      rintro ⟨b, hb, K, hK, F, hF_diff, hF_bd, hfF⟩
      let S : Set ℂ := {z : ℂ | |z.im| < b}
      have hS_open : IsOpen S := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
      have hreal_mem : ∀ x : ℝ, (x : ℂ) ∈ S := fun x => by simp [S, hb]
      have hf_eq_fun : f = fun x : ℝ => F x := funext hfF
      have hf_cd : ContDiff ℝ ∞ f := by
        rw [hf_eq_fun]
        exact ((hF_diff.contDiffOn hS_open).restrict_scalars ℝ).comp_contDiff
          Complex.ofRealCLM.contDiff (fun x => hreal_mem x)
      refine ⟨hf_cd, K, hK, 2 / b, by positivity, fun n x => ?_⟩
      rw [hf_eq_fun, (holomorphic_iteratedDeriv_comp_ofReal hS_open hF_diff n).2 x (hreal_mem x)]
      have hcb_sub : Metric.closedBall (x : ℂ) (b / 2) ⊆ S := by
        intro z hz
        rw [Metric.mem_closedBall, dist_eq_norm] at hz
        have him : |z.im| ≤ ‖z - (x : ℂ)‖ := by
          simpa using Complex.abs_im_le_norm (z - (x : ℂ))
        change |z.im| < b
        linarith
      have hdiffCont : DiffContOnCl ℂ F (Metric.ball (x : ℂ) (b / 2)) :=
        (hF_diff.mono (Metric.closure_ball_subset_closedBall.trans hcb_sub)).diffContOnCl
      have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
        n (half_pos hb) hdiffCont
        (fun z hz => hF_bd z (hcb_sub (Metric.sphere_subset_closedBall hz)))
      calc
        ‖iteratedDeriv n F (x : ℂ)‖ ≤ (n.factorial : ℝ) * K / (b / 2) ^ n := hcauchy
        _ = K * (2 / b) ^ n * (n.factorial : ℝ) := by
          rw [div_pow, div_pow]
          field_simp [hb.ne']
  refine ⟨hchar, ?_⟩
  -- Consequence: IsQuasiAnalytic (fun n => n!)
  intro f hf hderiv0 x
  obtain ⟨b, hb, K, _, F, hF_diff, _, hfF⟩ := (hchar f).mp hf
  let S : Set ℂ := {z : ℂ | |z.im| < b}
  have hS_open : IsOpen S := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hS_conv : Convex ℝ S := by
    intro z₁ hz₁ z₂ hz₂ u v hu hv huv
    change |z₁.im| < b at hz₁
    change |z₂.im| < b at hz₂
    change |(u • z₁ + v • z₂).im| < b
    have him : (u • z₁ + v • z₂).im = u * z₁.im + v * z₂.im := by simp
    rw [him]
    rcases eq_or_lt_of_le hu with rfl | hu_pos
    · simp only [zero_add] at huv
      subst huv
      simpa using hz₂
    · calc
        |u * z₁.im + v * z₂.im| ≤ |u * z₁.im| + |v * z₂.im| := abs_add_le _ _
        _ = u * |z₁.im| + v * |z₂.im| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hu_pos.le, abs_of_nonneg hv]
        _ < u * b + v * b := by
            have h1 : u * |z₁.im| < u * b := mul_lt_mul_of_pos_left hz₁ hu_pos
            have h2 : v * |z₂.im| ≤ v * b := mul_le_mul_of_nonneg_left (le_of_lt hz₂) hv
            linarith
        _ = b := by rw [← add_mul, huv, one_mul]
  have h0_S : (0 : ℂ) ∈ S := by simp [S, hb]
  have hF_deriv0 : ∀ n : ℕ, iteratedDeriv n F 0 = 0 := by
    intro n
    have h_eq : f = fun t : ℝ => F t := funext hfF
    have h_real := (holomorphic_iteratedDeriv_comp_ofReal hS_open hF_diff n).2 0 h0_S
    simpa [h_eq] using h_real.symm.trans (h_eq ▸ hderiv0 n)
  have hF_zero := holomorphic_eq_zero_of_iteratedDeriv_eq_zero
    hS_open hS_conv.isPreconnected hF_diff h0_S hF_deriv0 (x : ℂ) (by simp [S, hb])
  rw [hfF x, hF_zero]

/-! ## §19.10: Compact-Support Characterization of Quasi-Analyticity (RCA p. 379) -/

section Node19_10_Helpers

/-- Truncation `x ↦ if 0 < x then h x else 0` on `(0, ∞)`. -/
private def cutPos (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then h x else 0

private lemma hasDerivAt_cutPos {h : ℝ → ℂ} (hh : Differentiable ℝ h)
    (h0 : h 0 = 0) (hd0 : deriv h 0 = 0) (x : ℝ) :
    HasDerivAt (cutPos h) (cutPos (deriv h) x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hev : cutPos h =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      have hy' : y < 0 := hy
      dsimp [cutPos]
      split_ifs with hp
      · exfalso; linarith
      · rfl
    have hval : cutPos (deriv h) x = 0 := by
      dsimp [cutPos]
      split_ifs with hp
      · exfalso; linarith
      · rfl
    rw [hval]
    exact (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hev
  · have hval : cutPos (deriv h) 0 = 0 := by dsimp [cutPos]; simp
    rw [hval, hasDerivAt_iff_tendsto]
    have hh0 : HasDerivAt h 0 0 := by simpa [hd0] using (hh 0).hasDerivAt
    rw [hasDerivAt_iff_tendsto] at hh0
    refine squeeze_zero (fun y => by positivity) (fun y => ?_) hh0
    have hcut0 : cutPos h 0 = 0 := by dsimp [cutPos]; simp
    simp only [sub_zero, hcut0, h0, smul_zero]
    dsimp [cutPos]
    split_ifs
    · exact le_rfl
    · rw [norm_zero, mul_zero]; positivity
  · have hev : cutPos h =ᶠ[𝓝 x] h := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      have hy' : 0 < y := hy
      dsimp [cutPos]
      simp [hy']
    have hval : cutPos (deriv h) x = deriv h x := by
      dsimp [cutPos]
      simp [hx]
    rw [hval]
    exact (hh x).hasDerivAt.congr_of_eventuallyEq hev

private lemma cutPos_smooth_and_iteratedDeriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hflat : ∀ n : ℕ, iteratedDeriv n f 0 = 0) :
    ContDiff ℝ ∞ (cutPos f) ∧
    ∀ n : ℕ, iteratedDeriv n (cutPos f) = cutPos (iteratedDeriv n f) := by
  have hstep : ∀ k : ℕ, Differentiable ℝ (cutPos (iteratedDeriv k f)) ∧
      deriv (cutPos (iteratedDeriv k f)) = cutPos (iteratedDeriv (k + 1) f) := by
    intro k
    have hd : ∀ x : ℝ, HasDerivAt (cutPos (iteratedDeriv k f))
        (cutPos (iteratedDeriv (k + 1) f) x) x := by
      intro x
      have hd_eq : deriv (iteratedDeriv k f) = iteratedDeriv (k + 1) f :=
        (iteratedDeriv_succ (n := k) (f := f)).symm
      rw [← hd_eq]
      exact hasDerivAt_cutPos (differentiable_iteratedDeriv_of_infty hf k)
        (hflat k) (by rw [hd_eq]; exact hflat (k + 1)) x
    exact ⟨fun x => (hd x).differentiableAt, funext fun x => (hd x).deriv⟩
  have hiter : ∀ n : ℕ, iteratedDeriv n (cutPos f) = cutPos (iteratedDeriv n f) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iteratedDeriv_succ, ih, (hstep n).2]
  have hcd_nat : ∀ (m : ℕ) (k : ℕ), ContDiff ℝ (m : ℕ) (cutPos (iteratedDeriv k f)) := by
    intro m
    induction m with
    | zero =>
      intro k
      exact contDiff_zero.mpr (hstep k).1.continuous
    | succ m ih =>
      intro k
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨(hstep k).1, ?_, ?_⟩
      · intro hω
        simp at hω
      · rw [(hstep k).2]
        exact ih (k + 1)
  exact ⟨contDiff_infty.mpr fun m => hcd_nat m 0, hiter⟩

end Node19_10_Helpers

/-- **Theorem 19.10 (Compact-Support Characterization of Quasi-Analyticity, RCA p. 379):**
For any positive normalized log-convex sequence `M`, `C{M_n}` is quasi-analytic if and only if
`C{M_n}` contains no nonzero function of compact support. -/
theorem theorem19_10 {M : ℕ → ℝ} (hM : IsPosNormLogConvex M) :
    IsQuasiAnalytic M ↔ ¬ ∃ f ∈ CM M, HasCompactSupport f ∧ ∃ x : ℝ, f x ≠ 0 := by
  constructor
  · -- Forward: quasi-analytic → no nonzero compactly supported member
    rintro hQA ⟨f, hf_CM, hf_supp, x₁, hx₁⟩
    obtain ⟨R, hR⟩ := hf_supp.isBounded.subset_closedBall (0 : ℝ)
    let x₀ : ℝ := max R 0 + 1
    have hx₀_not_tsupp : x₀ ∉ tsupport f := by
      intro hmem
      have hcb := hR hmem
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero,
        abs_of_pos (by dsimp [x₀]; positivity)] at hcb
      have : R ≤ max R 0 := le_max_left _ _
      dsimp [x₀] at hcb
      linarith
    have hev : f =ᶠ[𝓝 x₀] 0 := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx₀_not_tsupp] with y hy
      by_contra hfy
      exact hy (subset_tsupport f hfy)
    have hderiv : ∀ n : ℕ, iteratedDeriv n f x₀ = 0 := by
      intro n
      rw [hev.iteratedDeriv_eq n]
      change iteratedDeriv n (fun _ : ℝ => (0 : ℂ)) x₀ = 0
      rw [iteratedDeriv_const]
      split_ifs <;> rfl
    exact hx₁ (((theorem19_8 M x₀).mp hQA) f hf_CM hderiv x₁)
  · -- Converse: ¬ IsQuasiAnalytic M → construct nonzero compactly supported g ∈ CM M
    intro hno_cs
    by_contra hnot_QA
    unfold IsQuasiAnalytic at hnot_QA
    push Not at hnot_QA
    obtain ⟨f₀, hf₀_CM, hf₀_flat, x₀, hx₀_ne⟩ := hnot_QA
    have hx₀_nz : x₀ ≠ 0 := by
      rintro rfl
      exact hx₀_ne (by simpa using hf₀_flat 0)
    -- Ensure witness point x₁ > 0 by reflecting x ↦ f₀(-x) if x₀ < 0
    have hex_pos : ∃ (f : ℝ → ℂ) (x₁ : ℝ),
        f ∈ CM M ∧ (∀ n : ℕ, iteratedDeriv n f 0 = 0) ∧ 0 < x₁ ∧ f x₁ ≠ 0 := by
      rcases lt_or_gt_of_ne hx₀_nz with hx_neg | hx_pos
      · let f : ℝ → ℂ := fun x => f₀ ((-1 : ℝ) * x + 0)
        refine ⟨f, -x₀, CM_comp_affine hM.1 hf₀_CM (-1) 0, ?_, neg_pos.mpr hx_neg, ?_⟩
        · intro n
          rw [iteratedDeriv_comp_affine hf₀_CM.1 (-1) 0 n 0]
          simp [hf₀_flat n]
        · dsimp [f]
          simpa using hx₀_ne
      · exact ⟨f₀, x₀, hf₀_CM, hf₀_flat, hx_pos, hx₀_ne⟩
    obtain ⟨f, x₁, hf_CM, hf_flat, hx₁_pos, hfx₁_ne⟩ := hex_pos
    rcases hf_CM with ⟨hf_cd, β, hβ, B, hB, hbd⟩
    -- Cut f at 0: f₁(x) = if 0 < x then f(x) else 0
    let f₁ : ℝ → ℂ := cutPos f
    obtain ⟨hf₁_cd, hf₁_iter⟩ := cutPos_smooth_and_iteratedDeriv hf_cd hf_flat
    have hf₁_CM : f₁ ∈ CM M := by
      refine ⟨hf₁_cd, β, hβ, B, hB, fun n x => ?_⟩
      rw [hf₁_iter n]
      dsimp [cutPos]
      split_ifs
      · exact hbd n x
      · rw [norm_zero]; exact le_of_lt (by positivity [hM.1 n])
    -- Multiply by reflected translate f₂(x) = f₁(-x + 2 x₁)
    let f₂ : ℝ → ℂ := fun x => f₁ ((-1 : ℝ) * x + 2 * x₁)
    have hf₂_CM : f₂ ∈ CM M := CM_comp_affine hM.1 hf₁_CM (-1) (2 * x₁)
    let g : ℝ → ℂ := f₁ * f₂
    have hg_CM : g ∈ CM M := mul_mem_CM hM hf₁_CM hf₂_CM
    have hg_supp : HasCompactSupport g := by
      refine HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc (a := (0 : ℝ)) (b := 2 * x₁)) fun x hx => ?_
      rw [Function.mem_support] at hx
      by_contra hx_out
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx_out
      rcases hx_out with hx_neg | hx_gt
      · apply hx
        dsimp [g, f₁, cutPos]
        split_ifs with hp
        · exfalso; linarith
        · simp
      · apply hx
        have hf₂_zero : f₂ x = 0 := by
          dsimp [f₂, f₁, cutPos]
          split_ifs with hp
          · exfalso; linarith
          · rfl
        change f₁ x * f₂ x = 0
        rw [hf₂_zero, mul_zero]
    have hgx₁_ne : g x₁ ≠ 0 := by
      dsimp [g, f₂, f₁, cutPos]
      have harg : (-1 : ℝ) * x₁ + 2 * x₁ = x₁ := by ring
      rw [harg]
      simp [hx₁_pos, mul_ne_zero hfx₁_ne hfx₁_ne]
    exact hno_cs ⟨g, hg_CM, hg_supp, x₁, hgx₁_ne⟩


/-! ## §19.11: The Denjoy–Carleman Theorem (RCA pp. 380–383) -/

/-- **Node 19.11 (`dcQ`, RCA p. 380, Hazard 4 extended-value semantics):**
`Q(x) = ∑_{n=0}^∞ x^n / M_n` valued in `ℝ≥0∞` so divergent series faithfully evaluate to `⊤`. -/
def dcQ (M : ℕ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (x ^ n / M n)

/-- **Node 19.11 (`dcq`, RCA p. 380, Hazard 4 extended-value semantics):**
`q(x) = sup_{n ≥ 0} (x^n / M_n)` valued in `ℝ≥0∞` so unbounded suprema faithfully evaluate to `⊤`. -/
def dcq (M : ℕ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (x ^ n / M n)

/-- **Node 19.11 (`ennrealLog`, RCA p. 380, Hazard 4 extended-value semantics):**
Extended nonnegative logarithm on `ℝ≥0∞`: maps `⊤ ↦ ⊤` and finite `y ↦ ENNReal.ofReal (log y)`,
so `ennrealLog y = 0` for `y ≤ 1` and `ennrealLog` is monotone and measurable on `ℝ≥0∞`. -/
def ennrealLog (y : ℝ≥0∞) : ℝ≥0∞ :=
  if y = ⊤ then ⊤ else ENNReal.ofReal (Real.log y.toReal)

section Node19_11_Helpers

lemma one_le_dcq {M : ℕ → ℝ} (hM : IsPosNormLogConvex M) {x : ℝ} (_hx : 0 ≤ x) :
    1 ≤ dcq M x := by
  calc
    (1 : ℝ≥0∞) = ENNReal.ofReal (x ^ 0 / M 0) := by simp [hM.2.1]
    _ ≤ dcq M x := le_iSup (fun n : ℕ => ENNReal.ofReal (x ^ n / M n)) 0

lemma dcq_le_dcQ (M : ℕ → ℝ) (x : ℝ) :
    dcq M x ≤ dcQ M x := by
  unfold dcq dcQ
  exact iSup_le fun n => ENNReal.le_tsum (f := fun k => ENNReal.ofReal (x ^ k / M k)) n

lemma ennrealLog_mono : Monotone ennrealLog := by
  intro u v huv
  unfold ennrealLog
  by_cases hv : v = ⊤
  · simp [hv]
  · have hu : u ≠ ⊤ := ne_top_of_le_ne_top hv huv
    simp only [hu, hv, ↓reduceIte]
    by_cases hu0 : u = 0
    · simp [hu0]
    · have hu_pos : 0 < u.toReal := ENNReal.toReal_pos hu0 hu
      have huv_real : u.toReal ≤ v.toReal := (ENNReal.toReal_le_toReal hu hv).mpr huv
      exact ENNReal.ofReal_le_ofReal (Real.log_le_log hu_pos huv_real)

@[simp]
lemma ennrealLog_ofReal {r : ℝ} (hr : 0 < r) :
    ennrealLog (ENNReal.ofReal r) = ENNReal.ofReal (Real.log r) := by
  unfold ennrealLog
  simp [ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr.le]

lemma ennrealLog_mul {a b : ℝ≥0∞} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ennrealLog (a * b) = ennrealLog a + ennrealLog b := by
  have ha0 : a ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ha)
  have hb0 : b ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hb)
  unfold ennrealLog
  by_cases hat : a = ⊤
  · subst hat
    rw [ENNReal.top_mul hb0]
    simp
  · by_cases hbt : b = ⊤
    · subst hbt
      rw [ENNReal.mul_top ha0]
      simp
    · have habt : a * b ≠ ⊤ := ENNReal.mul_ne_top hat hbt
      simp only [hat, hbt, habt, ↓reduceIte]
      have ha1 : 1 ≤ a.toReal := by
        simpa using (ENNReal.toReal_le_toReal ENNReal.one_ne_top hat).mpr ha
      have hb1 : 1 ≤ b.toReal := by
        simpa using (ENNReal.toReal_le_toReal ENNReal.one_ne_top hbt).mpr hb
      have hapos : 0 < a.toReal := lt_of_lt_of_le zero_lt_one ha1
      have hbpos : 0 < b.toReal := lt_of_lt_of_le zero_lt_one hb1
      rw [ENNReal.toReal_mul, Real.log_mul hapos.ne' hbpos.ne',
        ENNReal.ofReal_add (Real.log_nonneg ha1) (Real.log_nonneg hb1)]

lemma tsum_ofReal_lt_top_iff_summable {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) :
    (∑' n : ℕ, ENNReal.ofReal (u n)) < ⊤ ↔ Summable u := by
  constructor
  · intro hlt
    by_contra hnot_sum
    have hdiv : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, u k) atTop atTop :=
      not_summable_iff_tendsto_nat_atTop_of_nonneg hu |>.mp hnot_sum
    obtain ⟨n, hn⟩ := (hdiv.eventually_ge_atTop
      ((∑' k : ℕ, ENNReal.ofReal (u k)).toReal + 1)).exists
    have hfin : ENNReal.ofReal (∑ k ∈ Finset.range n, u k) ≤
        ∑' k : ℕ, ENNReal.ofReal (u k) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hu k)]
      exact ENNReal.sum_le_tsum (Finset.range n)
    have hreal := (ENNReal.ofReal_le_iff_le_toReal hlt.ne).mp hfin
    linarith
  · intro hsum
    rw [← ENNReal.ofReal_tsum_of_nonneg hu hsum]
    exact ENNReal.ofReal_lt_top

lemma lintegral_inv_one_add_sq_lt_top :
    (∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (1 / (1 + x ^ 2))) < ⊤ := by
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt Real.arctan (1 / (1 + x ^ 2)) (Set.Ioi (0 : ℝ)) x :=
    fun x _ => (Real.hasDerivAt_arctan x).hasDerivWithinAt
  have hmono : MonotoneOn Real.arctan (Set.Ioi (0 : ℝ)) :=
    Real.arctan_mono.monotoneOn _
  rw [lintegral_deriv_eq_volume_image_of_monotoneOn measurableSet_Ioi hderiv hmono]
  have himg : Real.arctan '' Set.Ioi (0 : ℝ) ⊆ Set.Icc 0 (Real.pi / 2) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(Real.arctan_pos.mpr hx).le, (Real.arctan_lt_pi_div_two x).le⟩
  exact lt_of_le_of_lt (measure_mono himg) (by simp [Real.volume_Icc])

/-- Equivalence `(b) ↔ (c)` in Theorem 19.11. -/
theorem dc_b_iff_c {M : ℕ → ℝ} (hM : IsPosNormLogConvex M) :
    ((∫⁻ x in Set.Ioi (0 : ℝ), ennrealLog (dcQ M x) / ENNReal.ofReal (1 + x ^ 2)) < ⊤) ↔
    ((∫⁻ x in Set.Ioi (0 : ℝ), ennrealLog (dcq M x) / ENNReal.ofReal (1 + x ^ 2)) < ⊤) := by
  constructor
  · intro hb
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun x _ => ?_) hb
    exact ENNReal.div_le_div_right (ennrealLog_mono (dcq_le_dcQ M x)) _
  · intro hc
    -- For x > 0, dcQ M x ≤ 2 * dcq M (2 * x)
    have hQ_le : ∀ x : ℝ, 0 < x → dcQ M x ≤ 2 * dcq M (2 * x) := by
      intro x hx
      unfold dcQ
      have hterm : ∀ n : ℕ,
          ENNReal.ofReal (x ^ n / M n) ≤
            ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * dcq M (2 * x) := by
        intro n
        have heq : x ^ n / M n = (1 / 2 : ℝ) ^ n * ((2 * x) ^ n / M n) := by
          rw [mul_pow, ← mul_div_assoc, ← mul_assoc, ← mul_pow]
          norm_num
        rw [heq, ENNReal.ofReal_mul (by positivity)]
        exact mul_le_mul_of_nonneg_left
          (le_iSup (fun k : ℕ => ENNReal.ofReal ((2 * x) ^ k / M k)) n) zero_le
      calc
        (∑' n : ℕ, ENNReal.ofReal (x ^ n / M n))
          ≤ ∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * dcq M (2 * x) :=
            ENNReal.tsum_le_tsum hterm
        _ = (∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) * dcq M (2 * x) :=
            ENNReal.tsum_mul_right
        _ = 2 * dcq M (2 * x) := by
            congr 1
            have hsum : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
              summable_geometric_of_lt_one (by norm_num) (by norm_num)
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsum,
              tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
            norm_num
    -- Pointwise bound on integrand
    have hpt : ∀ x ∈ Set.Ioi (0 : ℝ),
        ennrealLog (dcQ M x) / ENNReal.ofReal (1 + x ^ 2) ≤
          ENNReal.ofReal (Real.log 2) * ENNReal.ofReal (1 / (1 + x ^ 2)) +
          (4 : ℝ≥0∞) * (ennrealLog (dcq M (2 * x)) / ENNReal.ofReal (1 + (2 * x) ^ 2)) := by
      intro x hx
      have hx_pos : 0 < x := hx
      have h2_le : (1 : ℝ≥0∞) ≤ 2 := by norm_num
      have hlog_le : ennrealLog (dcQ M x) ≤
          ENNReal.ofReal (Real.log 2) + ennrealLog (dcq M (2 * x)) := by
        calc
          ennrealLog (dcQ M x) ≤ ennrealLog (2 * dcq M (2 * x)) :=
            ennrealLog_mono (hQ_le x hx_pos)
          _ = ennrealLog (ENNReal.ofReal 2 * dcq M (2 * x)) := by norm_num
          _ = ENNReal.ofReal (Real.log 2) + ennrealLog (dcq M (2 * x)) := by
              rw [ennrealLog_mul (by norm_num) (one_le_dcq hM (by positivity)),
                ennrealLog_ofReal zero_lt_two]
      have h1x_pos : 0 < 1 + x ^ 2 := by positivity
      have hdiv_add :
          (ENNReal.ofReal (Real.log 2) + ennrealLog (dcq M (2 * x))) /
              ENNReal.ofReal (1 + x ^ 2) =
            ENNReal.ofReal (Real.log 2) / ENNReal.ofReal (1 + x ^ 2) +
              ennrealLog (dcq M (2 * x)) / ENNReal.ofReal (1 + x ^ 2) :=
        ENNReal.add_div
      calc
        ennrealLog (dcQ M x) / ENNReal.ofReal (1 + x ^ 2)
          ≤ (ENNReal.ofReal (Real.log 2) + ennrealLog (dcq M (2 * x))) /
              ENNReal.ofReal (1 + x ^ 2) :=
            ENNReal.div_le_div_right hlog_le _
        _ = ENNReal.ofReal (Real.log 2) / ENNReal.ofReal (1 + x ^ 2) +
              ennrealLog (dcq M (2 * x)) / ENNReal.ofReal (1 + x ^ 2) := hdiv_add
        _ ≤ ENNReal.ofReal (Real.log 2) * ENNReal.ofReal (1 / (1 + x ^ 2)) +
              (4 : ℝ≥0∞) * (ennrealLog (dcq M (2 * x)) / ENNReal.ofReal (1 + (2 * x) ^ 2)) := by
            refine add_le_add ?_ ?_
            · rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos h1x_pos, one_div]
            · have hden : 1 + (2 * x) ^ 2 ≤ 4 * (1 + x ^ 2) := by nlinarith
              have hden_pos : 0 < 1 + (2 * x) ^ 2 := by positivity
              rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc,
                mul_comm (4 : ℝ≥0∞) (ennrealLog (dcq M (2 * x))), mul_assoc]
              refine mul_le_mul_of_nonneg_left ?_ zero_le
              rw [← ENNReal.ofReal_inv_of_pos h1x_pos, ← ENNReal.ofReal_inv_of_pos hden_pos,
                show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
                ← ENNReal.ofReal_mul (by norm_num)]
              exact ENNReal.ofReal_le_ofReal (by
                rw [le_mul_inv_iff₀ hden_pos, inv_mul_le_iff₀ h1x_pos]
                linarith)
    -- Change of variables u = 2 * x on Ioi 0
    have hsub2 :
        (∫⁻ x in Set.Ioi (0 : ℝ),
          (2 : ℝ≥0∞) * (ennrealLog (dcq M (2 * x)) / ENNReal.ofReal (1 + (2 * x) ^ 2))) =
        ∫⁻ u in Set.Ioi (0 : ℝ), ennrealLog (dcq M u) / ENNReal.ofReal (1 + u ^ 2) := by
      have himg : (fun x : ℝ => 2 * x) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
        ext u; simp only [Set.mem_image, Set.mem_Ioi]
        constructor
        · rintro ⟨x, hx, rfl⟩; positivity
        · intro hu; exact ⟨u / 2, by positivity, by ring⟩
      have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
          HasDerivWithinAt (fun t : ℝ => 2 * t) 2 (Set.Ioi (0 : ℝ)) x := by
        intro x _
        simpa using ((hasDerivAt_id x).const_mul (2 : ℝ)).hasDerivWithinAt
      have hmono : MonotoneOn (fun t : ℝ => 2 * t) (Set.Ioi (0 : ℝ)) :=
        fun x _ y _ hxy => by linarith
      have hjac := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
        measurableSet_Ioi hderiv hmono
        (fun u : ℝ => ennrealLog (dcq M u) / ENNReal.ofReal (1 + u ^ 2))
      rw [himg] at hjac
      simpa using hjac.symm
    have hterm2_lt :
        (∫⁻ x in Set.Ioi (0 : ℝ),
          (4 : ℝ≥0∞) * (ennrealLog (dcq M (2 * x)) / ENNReal.ofReal (1 + (2 * x) ^ 2))) < ⊤ := by
      have heq4 :
          (∫⁻ x in Set.Ioi (0 : ℝ),
            (4 : ℝ≥0∞) * (ennrealLog (dcq M (2 * x)) / ENNReal.ofReal (1 + (2 * x) ^ 2))) =
          (2 : ℝ≥0∞) * ∫⁻ u in Set.Ioi (0 : ℝ),
            ennrealLog (dcq M u) / ENNReal.ofReal (1 + u ^ 2) := by
        have h4 : ∀ x : ℝ,
            (4 : ℝ≥0∞) * (ennrealLog (dcq M (2 * x)) / ENNReal.ofReal (1 + (2 * x) ^ 2)) =
              (2 : ℝ≥0∞) * ((2 : ℝ≥0∞) *
                (ennrealLog (dcq M (2 * x)) / ENNReal.ofReal (1 + (2 * x) ^ 2))) := by
          intro x; rw [← mul_assoc]; norm_num
        simp_rw [h4]
        rw [lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num), hsub2]
      rw [heq4]
      exact ENNReal.mul_lt_top (by norm_num) hc
    have hterm1_lt :
        (∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.log 2) * ENNReal.ofReal (1 / (1 + x ^ 2))) < ⊤ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top lintegral_inv_one_add_sq_lt_top
    have hmeas1 : Measurable (fun x : ℝ =>
        ENNReal.ofReal (Real.log 2) * ENNReal.ofReal (1 / (1 + x ^ 2))) := by
      fun_prop
    calc
      (∫⁻ x in Set.Ioi (0 : ℝ), ennrealLog (dcQ M x) / ENNReal.ofReal (1 + x ^ 2))
        ≤ ∫⁻ x in Set.Ioi (0 : ℝ),
            (ENNReal.ofReal (Real.log 2) * ENNReal.ofReal (1 / (1 + x ^ 2)) +
              (4 : ℝ≥0∞) * (ennrealLog (dcq M (2 * x)) / ENNReal.ofReal (1 + (2 * x) ^ 2))) :=
          setLIntegral_mono' measurableSet_Ioi hpt
      _ = (∫⁻ x in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (Real.log 2) * ENNReal.ofReal (1 / (1 + x ^ 2))) +
          (∫⁻ x in Set.Ioi (0 : ℝ),
            (4 : ℝ≥0∞) * (ennrealLog (dcq M (2 * x)) / ENNReal.ofReal (1 + (2 * x) ^ 2))) :=
          lintegral_add_left hmeas1 _
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hterm1_lt, hterm2_lt⟩

/-- Telescoping product representation `M_n = ∏_{k < n} (M_{k+1} / M_k)`. -/
lemma prod_ratio_eq_M {M : ℕ → ℝ} (hM : IsPosNormLogConvex M) (n : ℕ) :
    (∏ k ∈ Finset.range n, (M (k + 1) / M k)) = M n := by
  induction n with
  | zero => simp [hM.2.1]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, mul_div_cancel₀ _ (hM.1 n).ne']

/-- Exact identity `ennrealLog (dcq M x) = ∑' k, ENNReal.ofReal (max 0 (log (x / a_k)))` for all
`x > 0`, valid whether `dcq M x` is finite or `⊤`. -/
lemma ennrealLog_dcq_eq_tsum {M : ℕ → ℝ} (hM : IsPosNormLogConvex M) {x : ℝ} (hx : 0 < x) :
    ennrealLog (dcq M x) =
      ∑' k : ℕ, ENNReal.ofReal (max 0 (Real.log (x / (M (k + 1) / M k)))) := by
  let a : ℕ → ℝ := fun k => M (k + 1) / M k
  have ha_pos : ∀ k : ℕ, 0 < a k := fun k => div_pos (hM.1 (k + 1)) (hM.1 k)
  have ha_mono : Monotone a := hM.ratio_mono
  have hterm_exp : ∀ n : ℕ, x ^ n / M n = Real.exp (∑ k ∈ Finset.range n, Real.log (x / a k)) := by
    intro n
    have hprod : x ^ n / M n = ∏ k ∈ Finset.range n, (x / a k) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, prod_ratio_eq_M hM n]
    rw [hprod, Real.exp_sum]
    refine Finset.prod_congr rfl fun k _ => (Real.exp_log (div_pos hx (ha_pos k))).symm
  by_cases hex : ∃ N : ℕ, x < a N
  · obtain ⟨N, hN⟩ := hex
    -- Partition 0..N-1 into {k : a k ≤ x} and {k : x < a k} via monotonicity of a
    have hsplit_N : ∀ m : ℕ, ∃ n₀ ≤ m,
        (∀ k < n₀, a k ≤ x) ∧ (∀ k, n₀ ≤ k → k < m → x < a k) := by
      intro m
      induction m with
      | zero => exact ⟨0, le_rfl, fun _ hk => absurd hk (Nat.not_lt_zero _),
          fun _ _ hk => absurd hk (Nat.not_lt_zero _)⟩
      | succ m ih =>
        obtain ⟨n₀, hn₀_le, hle_x, hgt_x⟩ := ih
        by_cases hxm : a m ≤ x
        · refine ⟨m + 1, le_rfl, fun k hk => ?_, fun _ hge hlt => by omega⟩
          exact le_trans (ha_mono (Nat.lt_succ_iff.mp hk)) hxm
        · push Not at hxm
          refine ⟨n₀, Nat.le_succ_of_le hn₀_le, hle_x, fun k hge hlt => ?_⟩
          rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hlt) with rfl | hk_lt
          · exact hxm
          · exact hgt_x k hge hk_lt
    obtain ⟨n₀, hn₀_le, hle_x, hgt_x⟩ := hsplit_N N
    have htail_zero : ∀ k : ℕ, N ≤ k → max 0 (Real.log (x / a k)) = 0 := by
      intro k hk
      have hxk : x < a k := lt_of_lt_of_le hN (ha_mono hk)
      have hdiv_le : x / a k ≤ 1 := (div_le_one (ha_pos k)).mpr hxk.le
      exact max_eq_left (Real.log_nonpos (div_pos hx (ha_pos k)).le hdiv_le)
    have hsum_N : (∑ k ∈ Finset.range N, max 0 (Real.log (x / a k))) =
        ∑ k ∈ Finset.range n₀, Real.log (x / a k) := by
      have hsub : Finset.range n₀ ⊆ Finset.range N := Finset.range_mono hn₀_le
      rw [← Finset.sum_subset hsub]
      · refine Finset.sum_congr rfl fun k hk => ?_
        have h1 : 1 ≤ x / a k := (one_le_div (ha_pos k)).mpr (hle_x k (Finset.mem_range.mp hk))
        exact max_eq_right (Real.log_nonneg h1)
      · intro k hkN hkn₀
        have hk_ge : n₀ ≤ k := Nat.not_lt.mp (fun hlt => hkn₀ (Finset.mem_range.mpr hlt))
        have hxk : x < a k := hgt_x k hk_ge (Finset.mem_range.mp hkN)
        exact max_eq_left (Real.log_nonpos (div_pos hx (ha_pos k)).le
          ((div_le_one (ha_pos k)).mpr hxk.le))
    have hmax_all : ∀ n : ℕ, x ^ n / M n ≤ x ^ n₀ / M n₀ := by
      intro n
      rw [hterm_exp n, hterm_exp n₀, Real.exp_le_exp, ← hsum_N]
      calc
        (∑ k ∈ Finset.range n, Real.log (x / a k))
          ≤ ∑ k ∈ Finset.range n, max 0 (Real.log (x / a k)) :=
            Finset.sum_le_sum fun k _ => le_max_right _ _
        _ ≤ ∑ k ∈ Finset.range (max n N), max 0 (Real.log (x / a k)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left n N))
              (fun _ _ _ => le_max_left _ _)
        _ = ∑ k ∈ Finset.range N, max 0 (Real.log (x / a k)) :=
            (Finset.sum_subset (Finset.range_mono (le_max_right n N)) fun k _ hkN =>
              htail_zero k (Nat.not_lt.mp (fun hlt => hkN (Finset.mem_range.mpr hlt)))).symm
    have hdcq_eq : dcq M x = ENNReal.ofReal (x ^ n₀ / M n₀) := by
      refine le_antisymm
        (iSup_le fun n => ENNReal.ofReal_le_ofReal (hmax_all n))
        (le_iSup (fun n : ℕ => ENNReal.ofReal (x ^ n / M n)) n₀)
    rw [hdcq_eq, ennrealLog_ofReal (div_pos (pow_pos hx n₀) (hM.1 n₀)),
      hterm_exp n₀, Real.log_exp, ← hsum_N]
    rw [tsum_eq_sum (s := Finset.range N) (fun k hk => by
      have hk_ge : N ≤ k := Nat.not_lt.mp (fun hlt => hk (Finset.mem_range.mpr hlt))
      simp [a, htail_zero k hk_ge])]
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => le_max_left _ _)]
  · push Not at hex
    -- Here a k ≤ x for every k : ℕ, so c k := log (x / a k) ≥ 0
    let c : ℕ → ℝ := fun k => Real.log (x / a k)
    have hc_nonneg : ∀ k : ℕ, 0 ≤ c k := fun k =>
      Real.log_nonneg ((one_le_div (ha_pos k)).mpr (hex k))
    have hmax_eq : ∀ k : ℕ, max 0 (Real.log (x / a k)) = c k :=
      fun k => max_eq_right (hc_nonneg k)
    simp_rw [show ∀ k : ℕ, M (k + 1) / M k = a k from fun _ => rfl, hmax_eq]
    by_cases hsum : Summable c
    · let S : ℝ := ∑' k : ℕ, c k
      have hpart_le : ∀ n : ℕ, ∑ k ∈ Finset.range n, c k ≤ S :=
        fun n => Summable.sum_le_tsum (Finset.range n) (fun k _ => hc_nonneg k) hsum
      have hdcq_le : dcq M x ≤ ENNReal.ofReal (Real.exp S) := by
        refine iSup_le fun n => ?_
        rw [hterm_exp n]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hpart_le n))
      have hlim_exp : Tendsto
          (fun n : ℕ => ENNReal.ofReal (Real.exp (∑ k ∈ Finset.range n, c k)))
          atTop (𝓝 (ENNReal.ofReal (Real.exp S))) :=
        (ENNReal.continuous_ofReal.comp Real.continuous_exp).continuousAt.tendsto.comp
          hsum.hasSum.tendsto_sum_nat
      have hdcq_ge : ENNReal.ofReal (Real.exp S) ≤ dcq M x :=
        le_of_tendsto hlim_exp (Eventually.of_forall fun n => by
          dsimp only [c]
          rw [← hterm_exp n]
          exact le_iSup (fun m : ℕ => ENNReal.ofReal (x ^ m / M m)) n)
      rw [le_antisymm hdcq_le hdcq_ge, ennrealLog_ofReal (Real.exp_pos S), Real.log_exp,
        ENNReal.ofReal_tsum_of_nonneg hc_nonneg hsum]
    · -- Divergent nonnegative series c: partial sums → +∞, so both sides equal ⊤
      have hdiv : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, c k) atTop atTop :=
        not_summable_iff_tendsto_nat_atTop_of_nonneg hc_nonneg |>.mp hsum
      have hdcq_top : dcq M x = ⊤ := by
        by_contra hne
        let R : ℝ := Real.log ((dcq M x).toReal + 1)
        obtain ⟨n, hn⟩ := (hdiv.eventually_ge_atTop R).exists
        have hle : ENNReal.ofReal (x ^ n / M n) ≤ dcq M x :=
          le_iSup (fun m : ℕ => ENNReal.ofReal (x ^ m / M m)) n
        have hreal : x ^ n / M n ≤ (dcq M x).toReal :=
          (ENNReal.ofReal_le_iff_le_toReal hne).mp hle
        have hgt : (dcq M x).toReal + 1 ≤ x ^ n / M n := by
          rw [hterm_exp n, ← Real.exp_log (by positivity : 0 < (dcq M x).toReal + 1)]
          exact Real.exp_le_exp.mpr hn
        linarith
      have htsum_top : (∑' k : ℕ, ENNReal.ofReal (c k)) = ⊤ := by
        by_contra hne
        obtain ⟨n, hn⟩ := (hdiv.eventually_ge_atTop
          ((∑' k : ℕ, ENNReal.ofReal (c k)).toReal + 1)).exists
        have hfin : ENNReal.ofReal (∑ k ∈ Finset.range n, c k) ≤
            ∑' k : ℕ, ENNReal.ofReal (c k) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hc_nonneg k)]
          exact ENNReal.sum_le_tsum (Finset.range n)
        have hreal := (ENNReal.ofReal_le_iff_le_toReal hne).mp hfin
        linarith
      rw [hdcq_top, htsum_top]
      rfl

/-- Equivalence `(c) ↔ (e)` in Theorem 19.11 via Tonelli's theorem. -/
theorem dc_c_iff_e {M : ℕ → ℝ} (hM : IsPosNormLogConvex M) :
    ((∫⁻ x in Set.Ioi (0 : ℝ), ennrealLog (dcq M x) / ENNReal.ofReal (1 + x ^ 2)) < ⊤) ↔
    ((∑' k : ℕ, ENNReal.ofReal (M k / M (k + 1))) < ⊤) := by
  let a : ℕ → ℝ := fun k => M (k + 1) / M k
  have ha_pos : ∀ k : ℕ, 0 < a k := fun k => div_pos (hM.1 (k + 1)) (hM.1 k)
  have ha0_le : ∀ k : ℕ, a 0 ≤ a k := fun k => hM.ratio_mono (Nat.zero_le k)
  -- Express integrand on Ioi 0 as tsum over k
  let g : ℕ → ℝ → ℝ≥0∞ :=
    fun k x => ENNReal.ofReal (max 0 (Real.log (x / a k)) / (1 + x ^ 2))
  have hg_meas : ∀ k : ℕ, Measurable (g k) := by
    intro k; dsimp [g]; fun_prop
  have hlhs_eq :
      (∫⁻ x in Set.Ioi (0 : ℝ), ennrealLog (dcq M x) / ENNReal.ofReal (1 + x ^ 2)) =
      ∑' k : ℕ, ∫⁻ x in Set.Ioi (0 : ℝ), g k x := by
    have hcongr :
        (∫⁻ x in Set.Ioi (0 : ℝ), ennrealLog (dcq M x) / ENNReal.ofReal (1 + x ^ 2)) =
        ∫⁻ x in Set.Ioi (0 : ℝ), ∑' k : ℕ, g k x := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx_pos : 0 < x := hx
      have h1x : 0 < 1 + x ^ 2 := by positivity
      rw [ennrealLog_dcq_eq_tsum hM hx_pos, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
      refine tsum_congr fun k => ?_
      dsimp only [g, a]
      rw [← ENNReal.ofReal_inv_of_pos h1x, ← ENNReal.ofReal_mul (le_max_left _ _),
        ← div_eq_mul_inv]
    rw [hcongr, lintegral_tsum fun k => (hg_meas k).aemeasurable]
  rw [hlhs_eq]
  -- Upper bound on each k-th integral: ≤ ENNReal.ofReal (M k / M (k + 1))
  have h_upper : ∀ k : ℕ,
      (∫⁻ x in Set.Ioi (0 : ℝ), g k x) ≤ ENNReal.ofReal (M k / M (k + 1)) := by
    intro k
    have hak : 0 < a k := ha_pos k
    -- Split Ioi 0 = Ioc 0 (a k) ∪ Ioi (a k); integral on Ioc 0 (a k) vanishes
    have hsplit_set : Set.Ioi (0 : ℝ) = Set.Ioc 0 (a k) ∪ Set.Ioi (a k) := by
      ext x; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro hx; rcases le_or_gt x (a k) with hle | hgt
        · exact Or.inl ⟨hx, hle⟩
        · exact Or.inr hgt
      · rintro (⟨hx, _⟩ | hgt)
        · exact hx
        · exact lt_trans hak hgt
    have hdisj : Disjoint (Set.Ioc 0 (a k)) (Set.Ioi (a k)) :=
      Set.disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2
    have hzero_left : (∫⁻ x in Set.Ioc 0 (a k), g k x) = 0 := by
      refine (setLIntegral_eq_zero_iff measurableSet_Ioc (hg_meas k)).mpr ?_
      refine Eventually.of_forall fun x hx => ?_
      dsimp [g]
      have hdiv1 : x / a k ≤ 1 := (div_le_one hak).mpr hx.2
      rw [max_eq_left (Real.log_nonpos (div_pos hx.1 hak).le hdiv1), zero_div, ENNReal.ofReal_zero]
    rw [hsplit_set, lintegral_union measurableSet_Ioi hdisj, hzero_left, zero_add]
    -- On Ioi (a k), g k x ≤ log (x / a k) / x ^ 2 = deriv (x ↦ -(1 + log (x / a k)) / x)
    let F : ℝ → ℝ := fun x => -(1 + Real.log (x / a k)) / x
    have hF_hasDeriv : ∀ x ∈ Set.Ioi (a k),
        HasDerivAt F (Real.log (x / a k) / x ^ 2) x := by
      intro x hx
      have hx_pos : 0 < x := lt_trans hak hx
      have hdiv_pos : 0 < x / a k := div_pos hx_pos hak
      have hd1 : HasDerivAt (fun t : ℝ => t / a k) (1 / a k) x := by
        simpa using (hasDerivAt_id x).div_const (a k)
      have hd2 : HasDerivAt (fun t : ℝ => -(1 + Real.log (t / a k)))
          (-(1 / x)) x := by
        refine (((hasDerivAt_const x (1 : ℝ)).add (hd1.log hdiv_pos.ne')).neg).congr_deriv ?_
        field_simp [hak.ne', hx_pos.ne']
        ring
      refine (hd2.div (hasDerivAt_id x) hx_pos.ne').congr_deriv ?_
      dsimp only [id]
      field_simp [hx_pos.ne']
      ring
    have hF_deriv : ∀ x ∈ Set.Ioi (a k),
        HasDerivWithinAt F (Real.log (x / a k) / x ^ 2) (Set.Ioi (a k)) x :=
      fun x hx => (hF_hasDeriv x hx).hasDerivWithinAt
    have hF_mono : MonotoneOn F (Set.Ioi (a k)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ioi (a k))
        (fun x hx => (hF_hasDeriv x hx).continuousAt.continuousWithinAt) ?_ ?_
      · rw [interior_Ioi]
        exact fun x hx => (hF_hasDeriv x hx).differentiableAt.differentiableWithinAt
      · rw [interior_Ioi]
        intro x hx
        rw [(hF_hasDeriv x hx).deriv]
        exact div_nonneg (Real.log_nonneg ((one_le_div hak).mpr (le_of_lt hx))) (sq_nonneg x)
    have hle_sq : ∀ x ∈ Set.Ioi (a k),
        g k x ≤ ENNReal.ofReal (Real.log (x / a k) / x ^ 2) := by
      intro x hx
      have hx_pos : 0 < x := lt_trans hak hx
      have hlog_nn : 0 ≤ Real.log (x / a k) :=
        Real.log_nonneg ((one_le_div hak).mpr (le_of_lt hx))
      dsimp [g]
      rw [max_eq_right hlog_nn]
      refine ENNReal.ofReal_le_ofReal ?_
      exact div_le_div_of_nonneg_left hlog_nn (sq_pos_of_pos hx_pos) (by linarith)
    have himg_sub : F '' Set.Ioi (a k) ⊆ Set.Icc (-(1 / a k)) 0 := by
      rintro _ ⟨x, hx, rfl⟩
      have hx_pos : 0 < x := lt_trans hak hx
      have hlog_nn : 0 ≤ Real.log (x / a k) :=
        Real.log_nonneg ((one_le_div hak).mpr (le_of_lt hx))
      dsimp [F]
      refine ⟨?_, ?_⟩
      · rw [neg_div, neg_le_neg_iff]
        calc
          (1 + Real.log (x / a k)) / x ≤ (x / a k) / x := by
            refine div_le_div_of_nonneg_right ?_ hx_pos.le
            have h1 := Real.log_le_sub_one_of_pos (div_pos hx_pos hak)
            linarith
          _ = 1 / a k := by field_simp [hx_pos.ne']
      · rw [neg_div, Left.neg_nonpos_iff]
        exact div_nonneg (by linarith) hx_pos.le
    calc
      (∫⁻ x in Set.Ioi (a k), g k x)
        ≤ ∫⁻ x in Set.Ioi (a k), ENNReal.ofReal (Real.log (x / a k) / x ^ 2) :=
          setLIntegral_mono' measurableSet_Ioi hle_sq
      _ = volume (F '' Set.Ioi (a k)) :=
          lintegral_deriv_eq_volume_image_of_monotoneOn measurableSet_Ioi hF_deriv hF_mono
      _ ≤ volume (Set.Icc (-(1 / a k)) 0) := measure_mono himg_sub
      _ = ENNReal.ofReal (M k / M (k + 1)) := by
          rw [Real.volume_Icc, zero_sub, neg_neg]
          dsimp [a]
          rw [one_div_div]
  -- Lower bound on each k-th integral from [2 a_k, 4 a_k]
  let C_low : ℝ := 2 * Real.log 2 / (1 / (a 0) ^ 2 + 16)
  have hC_low_pos : 0 < C_low := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have ha0 : 0 < a 0 := ha_pos 0
    dsimp [C_low]
    positivity
  have h_lower : ∀ k : ℕ,
      ENNReal.ofReal C_low * ENNReal.ofReal (M k / M (k + 1)) ≤
        ∫⁻ x in Set.Ioi (0 : ℝ), g k x := by
    intro k
    have hak : 0 < a k := ha_pos k
    have ha0 : 0 < a 0 := ha_pos 0
    have hsub_J : Set.Ioo (2 * a k) (4 * a k) ⊆ Set.Ioi (0 : ℝ) :=
      fun x hx => lt_trans (by positivity) hx.1
    have hpt_J : ∀ x ∈ Set.Ioo (2 * a k) (4 * a k),
        ENNReal.ofReal ((Real.log 2 / (1 / (a 0) ^ 2 + 16)) / (a k) ^ 2) ≤ g k x := by
      intro x hx
      dsimp [g]
      refine ENNReal.ofReal_le_ofReal ?_
      have hlog_ge : Real.log 2 ≤ max 0 (Real.log (x / a k)) := by
        refine le_trans ?_ (le_max_right 0 _)
        exact Real.log_le_log zero_lt_two ((lt_div_iff₀ hak).mpr hx.1).le
      have hden_le : 1 + x ^ 2 ≤ (1 / (a 0) ^ 2 + 16) * (a k) ^ 2 := by
        have h1_le : 1 ≤ (1 / (a 0) ^ 2) * (a k) ^ 2 := by
          have hsq : (a 0) ^ 2 ≤ (a k) ^ 2 := pow_le_pow_left₀ ha0.le (ha0_le k) 2
          calc
            (1 : ℝ) = (1 / (a 0) ^ 2) * (a 0) ^ 2 := by field_simp [ha0.ne']
            _ ≤ (1 / (a 0) ^ 2) * (a k) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
        have hx_sq : x ^ 2 ≤ 16 * (a k) ^ 2 := by nlinarith [hx.1, hx.2, hak]
        linarith
      have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      calc
        (Real.log 2 / (1 / (a 0) ^ 2 + 16)) / (a k) ^ 2
          = Real.log 2 / ((1 / (a 0) ^ 2 + 16) * (a k) ^ 2) := div_div _ _ _
        _ ≤ Real.log 2 / (1 + x ^ 2) :=
          div_le_div_of_nonneg_left hlog2.le (by positivity) hden_le
        _ ≤ max 0 (Real.log (x / a k)) / (1 + x ^ 2) :=
          div_le_div_of_nonneg_right hlog_ge (by positivity)
    calc
      ENNReal.ofReal C_low * ENNReal.ofReal (M k / M (k + 1))
        = ENNReal.ofReal ((Real.log 2 / (1 / (a 0) ^ 2 + 16)) / (a k) ^ 2) *
            volume (Set.Ioo (2 * a k) (4 * a k)) := by
          rw [Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          dsimp [C_low, a]
          field_simp [hak.ne']
          ring
      _ = ∫⁻ _ in Set.Ioo (2 * a k) (4 * a k),
            ENNReal.ofReal ((Real.log 2 / (1 / (a 0) ^ 2 + 16)) / (a k) ^ 2) := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ x in Set.Ioo (2 * a k) (4 * a k), g k x :=
          setLIntegral_mono' measurableSet_Ioo hpt_J
      _ ≤ ∫⁻ x in Set.Ioi (0 : ℝ), g k x :=
          lintegral_mono_set hsub_J
  constructor
  · intro hc
    have hmul_lt : ENNReal.ofReal C_low * ∑' k : ℕ, ENNReal.ofReal (M k / M (k + 1)) < ⊤ := by
      rw [← ENNReal.tsum_mul_left]
      exact lt_of_le_of_lt (ENNReal.tsum_le_tsum h_lower) hc
    by_contra htop
    rw [not_lt_top_iff] at htop
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hC_low_pos).ne'] at hmul_lt
    exact lt_irrefl ⊤ hmul_lt
  · intro he
    exact lt_of_le_of_lt (ENNReal.tsum_le_tsum h_upper) he

/-- Elementary factorial bound `((m + 1 : ℝ) ^ m) ≤ exp m * m!`. -/
lemma succ_pow_le_exp_mul_factorial (m : ℕ) :
    ((m + 1 : ℕ) : ℝ) ^ m ≤ Real.exp (m : ℝ) * (m.factorial : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hstep1 : ((m + 1 : ℕ) : ℝ) ^ (m + 1) ≤
        Real.exp (m : ℝ) * ((m + 1).factorial : ℝ) := by
      rw [pow_succ, Nat.factorial_succ, Nat.cast_mul]
      calc
        ((m + 1 : ℕ) : ℝ) ^ m * ((m + 1 : ℕ) : ℝ)
          ≤ (Real.exp (m : ℝ) * (m.factorial : ℝ)) * ((m + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right ih hm1_pos.le
        _ = Real.exp (m : ℝ) * (((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ)) := by ring
    have hexp1 : (1 + 1 / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) ≤ Real.exp 1 := by
      calc
        (1 + 1 / ((m + 1 : ℕ) : ℝ)) ^ (m + 1)
          ≤ (Real.exp (1 / ((m + 1 : ℕ) : ℝ))) ^ (m + 1) := by
            refine pow_le_pow_left₀ (by positivity) ?_ (m + 1)
            linarith [Real.add_one_le_exp (1 / ((m + 1 : ℕ) : ℝ))]
        _ = Real.exp (((m + 1 : ℕ) : ℝ) * (1 / ((m + 1 : ℕ) : ℝ))) :=
            (Real.exp_nat_mul _ (m + 1)).symm
        _ = Real.exp 1 := by rw [mul_one_div_cancel hm1_pos.ne']
    have hratio : ((m + 2 : ℕ) : ℝ) ^ (m + 1) =
        (1 + 1 / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) * ((m + 1 : ℕ) : ℝ) ^ (m + 1) := by
      rw [← mul_pow]
      congr 1
      have : ((m + 2 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [this]
      field_simp [hm1_pos.ne']
    rw [hratio]
    calc
      (1 + 1 / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) * ((m + 1 : ℕ) : ℝ) ^ (m + 1)
        ≤ Real.exp 1 * (Real.exp (m : ℝ) * ((m + 1).factorial : ℝ)) :=
          mul_le_mul hexp1 hstep1 (by positivity) (Real.exp_pos 1).le
      _ = Real.exp ((m + 1 : ℕ) : ℝ) * ((m + 1).factorial : ℝ) := by
          rw [Nat.cast_add, Nat.cast_one, Real.exp_add]
          ring

/-- Equivalence `(d) ↔ (e)` in Theorem 19.11 via monotone ratios and Carleman's inequality. -/
theorem dc_d_iff_e {M : ℕ → ℝ} (hM : IsPosNormLogConvex M) :
    ((∑' n : ℕ, ENNReal.ofReal ((M (n + 1)) ^ (-(1 / ((n + 1 : ℕ) : ℝ))))) < ⊤) ↔
    ((∑' k : ℕ, ENNReal.ofReal (M k / M (k + 1))) < ⊤) := by
  constructor
  · -- (d) → (e): M_k / M_{k+1} ≤ M_{k+1}^{-1/(k+1)} term-by-term
    intro hd
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun k => ?_) hd
    refine ENNReal.ofReal_le_ofReal ?_
    let a : ℕ → ℝ := fun j => M (j + 1) / M j
    have ha_pos : ∀ j : ℕ, 0 < a j := fun j => div_pos (hM.1 (j + 1)) (hM.1 j)
    have hM_le_pow : M (k + 1) ≤ (a k) ^ (k + 1) := by
      rw [← prod_ratio_eq_M hM (k + 1)]
      calc
        (∏ j ∈ Finset.range (k + 1), a j)
          ≤ ∏ _ ∈ Finset.range (k + 1), a k := by
            refine Finset.prod_le_prod₀ (fun j _ => (ha_pos j).le) fun j hj => ?_
            exact hM.ratio_mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
        _ = (a k) ^ (k + 1) := by rw [Finset.prod_const, Finset.card_range]
    have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hrpow_le : (M (k + 1)) ^ (1 / ((k + 1 : ℕ) : ℝ)) ≤ a k := by
      calc
        (M (k + 1)) ^ (1 / ((k + 1 : ℕ) : ℝ))
          ≤ ((a k) ^ (k + 1)) ^ (1 / ((k + 1 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow (hM.1 (k + 1)).le hM_le_pow (by positivity)
        _ = a k := by
            rw [← Real.rpow_natCast (a k) (k + 1), ← Real.rpow_mul (ha_pos k).le,
              mul_one_div_cancel hk1_pos.ne', Real.rpow_one]
    have hinv : (a k)⁻¹ ≤ ((M (k + 1)) ^ (1 / ((k + 1 : ℕ) : ℝ)))⁻¹ :=
      inv_anti₀ (Real.rpow_pos_of_pos (hM.1 (k + 1)) _) hrpow_le
    calc
      M k / M (k + 1) = (a k)⁻¹ := by dsimp [a]; rw [inv_div]
      _ ≤ ((M (k + 1)) ^ (1 / ((k + 1 : ℕ) : ℝ)))⁻¹ := hinv
      _ = (M (k + 1)) ^ (-(1 / ((k + 1 : ℕ) : ℝ))) :=
          (Real.rpow_neg (hM.1 (k + 1)).le _).symm
  · -- (e) → (d): Carleman's inequality via weighted AM-GM
    intro he
    let u : ℕ → ℝ := fun k => M k / M (k + 1)
    have hu_pos : ∀ k : ℕ, 0 < u k := fun k => div_pos (hM.1 k) (hM.1 (k + 1))
    -- Pointwise Carleman bound for m = n + 1
    have hcarl : ∀ n : ℕ,
        (M (n + 1)) ^ (-(1 / ((n + 1 : ℕ) : ℝ))) ≤
          Real.exp 1 * ∑ k ∈ Finset.range (n + 1),
            (((k + 1 : ℕ) : ℝ) * u k) /
              (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) := by
      intro n
      let m : ℕ := n + 1
      have hm_pos : (0 : ℝ) < (m : ℝ) := by dsimp [m]; positivity
      let w : ℕ → ℝ := fun _ => 1 / (m : ℝ)
      let z : ℕ → ℝ := fun k => ((k + 1 : ℕ) : ℝ) * u k
      have hw_nn : ∀ k ∈ Finset.range m, 0 ≤ w k := fun _ _ => by dsimp [w]; positivity
      have hw_sum : ∑ k ∈ Finset.range m, w k = 1 := by
        dsimp [w]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div_cancel hm_pos.ne']
      have hz_nn : ∀ k ∈ Finset.range m, 0 ≤ z k :=
        fun k _ => mul_nonneg (by positivity) (hu_pos k).le
      have hamgm := Real.geom_mean_le_arith_mean_weighted (Finset.range m) w z hw_nn hw_sum hz_nn
      -- Evaluate geometric mean = (m!)^(1/m) * (M m)^(-1/m)
      have hprod_z : ∏ k ∈ Finset.range m, z k = (m.factorial : ℝ) / M m := by
        have hfact : (∏ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ)) = (m.factorial : ℝ) := by
          clear hamgm hw_sum
          induction m with
          | zero => simp
          | succ r ihr =>
            rw [Finset.prod_range_succ, ihr, Nat.factorial_succ, Nat.cast_mul, mul_comm]
        have hu_prod : (∏ k ∈ Finset.range m, u k) = (M m)⁻¹ := by
          rw [← prod_ratio_eq_M hM m, ← Finset.prod_inv_distrib]
          refine Finset.prod_congr rfl fun k _ => ?_
          dsimp [u]; rw [inv_div]
        dsimp [z]
        rw [Finset.prod_mul_distrib, hfact, hu_prod, div_eq_mul_inv]
      have hgeom_eq : (∏ k ∈ Finset.range m, (z k) ^ (w k)) =
          (m.factorial : ℝ) ^ (1 / (m : ℝ)) * (M m) ^ (-(1 / (m : ℝ))) := by
        dsimp [w]
        rw [Real.finsetProd_rpow (Finset.range m) z (fun k hk => hz_nn k hk),
          hprod_z, div_eq_mul_inv,
          Real.mul_rpow (Nat.cast_nonneg _) (inv_nonneg.mpr (hM.1 m).le),
          Real.inv_rpow (hM.1 m).le, ← Real.rpow_neg (hM.1 m).le]
      -- Bound (m!)^(-1/m) ≤ exp 1 / (m + 1)
      have hfact_inv : (m.factorial : ℝ) ^ (-(1 / (m : ℝ))) ≤
          Real.exp 1 / ((m + 1 : ℕ) : ℝ) := by
        have h1 := succ_pow_le_exp_mul_factorial m
        have hexp_rpow : (Real.exp (m : ℝ) * (m.factorial : ℝ)) ^ (1 / (m : ℝ)) =
            Real.exp 1 * (m.factorial : ℝ) ^ (1 / (m : ℝ)) := by
          rw [Real.mul_rpow (Real.exp_pos _).le (Nat.cast_nonneg _),
            ← Real.exp_mul, mul_one_div_cancel hm_pos.ne']
        have h2 : ((m + 1 : ℕ) : ℝ) ≤ Real.exp 1 * (m.factorial : ℝ) ^ (1 / (m : ℝ)) := by
          calc
            ((m + 1 : ℕ) : ℝ)
              = (((m + 1 : ℕ) : ℝ) ^ m) ^ (1 / (m : ℝ)) := by
                rw [← Real.rpow_natCast _ m, ← Real.rpow_mul (by positivity),
                  mul_one_div_cancel hm_pos.ne', Real.rpow_one]
            _ ≤ (Real.exp (m : ℝ) * (m.factorial : ℝ)) ^ (1 / (m : ℝ)) :=
                Real.rpow_le_rpow (by positivity) h1 (by positivity)
            _ = Real.exp 1 * (m.factorial : ℝ) ^ (1 / (m : ℝ)) := hexp_rpow
        have hfpos : 0 < (m.factorial : ℝ) ^ (1 / (m : ℝ)) :=
          Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos m)) _
        rw [Real.rpow_neg (Nat.cast_nonneg _), inv_eq_one_div,
          div_le_div_iff₀ hfpos (by positivity), one_mul]
        exact h2
      have hpos_f : 0 < (m.factorial : ℝ) ^ (1 / (m : ℝ)) :=
        Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos m)) _
      have hMm_le : (M m) ^ (-(1 / (m : ℝ))) ≤
          (m.factorial : ℝ) ^ (-(1 / (m : ℝ))) * ∑ k ∈ Finset.range m, w k * z k := by
        rw [hgeom_eq] at hamgm
        have hcancel : (m.factorial : ℝ) ^ (-(1 / (m : ℝ))) *
            ((m.factorial : ℝ) ^ (1 / (m : ℝ)) * (M m) ^ (-(1 / (m : ℝ)))) =
            (M m) ^ (-(1 / (m : ℝ))) := by
          rw [← mul_assoc, Real.rpow_neg (Nat.cast_nonneg _), inv_mul_cancel₀ hpos_f.ne', one_mul]
        calc
          (M m) ^ (-(1 / (m : ℝ)))
            = (m.factorial : ℝ) ^ (-(1 / (m : ℝ))) *
                ((m.factorial : ℝ) ^ (1 / (m : ℝ)) * (M m) ^ (-(1 / (m : ℝ)))) := hcancel.symm
          _ ≤ (m.factorial : ℝ) ^ (-(1 / (m : ℝ))) * ∑ k ∈ Finset.range m, w k * z k :=
              mul_le_mul_of_nonneg_left hamgm (by positivity)
      calc
        (M (n + 1)) ^ (-(1 / ((n + 1 : ℕ) : ℝ)))
          ≤ (Real.exp 1 / ((m + 1 : ℕ) : ℝ)) * ∑ k ∈ Finset.range m, w k * z k :=
            hMm_le.trans (mul_le_mul_of_nonneg_right hfact_inv
              (Finset.sum_nonneg fun k hk => mul_nonneg (hw_nn k hk) (hz_nn k hk)))
        _ = Real.exp 1 * ∑ k ∈ Finset.range (n + 1),
              (((k + 1 : ℕ) : ℝ) * u k) / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) := by
            dsimp [m, w, z]
            rw [div_eq_mul_inv, mul_assoc, Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl fun k _ => ?_
            have : ((n + 1 + 1 : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) := by norm_cast
            rw [this]
            ring
    -- Sum Carleman's bound over n : ℕ via Tonelli on ℕ × ℕ
    let T : ℕ → ℕ → ℝ≥0∞ := fun n k =>
      if k < n + 1 then
        ENNReal.ofReal ((((k + 1 : ℕ) : ℝ) * u k) / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)))
      else 0
    have hinner_k : ∀ k : ℕ, (∑' n : ℕ, T n k) ≤ ENNReal.ofReal (u k) := by
      intro k
      have huk : 0 < u k := hu_pos k
      have htele : ∀ J : ℕ,
          (∑ j ∈ Finset.range J,
            (1 : ℝ) / (((k + j + 1 : ℕ) : ℝ) * ((k + j + 2 : ℕ) : ℝ))) =
          1 / ((k + 1 : ℕ) : ℝ) - 1 / ((k + J + 1 : ℕ) : ℝ) := by
        intro J
        induction J with
        | zero => simp
        | succ J ihJ =>
          rw [Finset.sum_range_succ, ihJ]
          have h1 : (0 : ℝ) < ((k + J + 1 : ℕ) : ℝ) := by positivity
          have h2 : (0 : ℝ) < ((k + J + 2 : ℕ) : ℝ) := by positivity
          have hcast1 : ((k + (J + 1) + 1 : ℕ) : ℝ) = ((k + J + 2 : ℕ) : ℝ) := by
            push_cast; ring
          rw [hcast1]
          have hfrac : (1 : ℝ) / (((k + J + 1 : ℕ) : ℝ) * ((k + J + 2 : ℕ) : ℝ)) =
              1 / ((k + J + 1 : ℕ) : ℝ) - 1 / ((k + J + 2 : ℕ) : ℝ) := by
            field_simp [h1.ne', h2.ne']
            push_cast; ring
          linarith
      refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
      by_cases hNk : N ≤ k
      · have h0 : ∑ n ∈ Finset.range N, T n k = 0 := by
          refine Finset.sum_eq_zero fun n hn => ?_
          have hn_lt : n < N := Finset.mem_range.mp hn
          dsimp [T]
          split_ifs with hlt
          · omega
          · rfl
        rw [h0]
        exact zero_le
      · push Not at hNk
        let J : ℕ := N - k
        have hN_eq : N = k + J := (Nat.add_sub_of_le hNk.le).symm
        rw [hN_eq, Finset.sum_range_add]
        have h0 : ∑ n ∈ Finset.range k, T n k = 0 := by
          refine Finset.sum_eq_zero fun n hn => ?_
          have hn_lt : n < k := Finset.mem_range.mp hn
          dsimp [T]
          split_ifs with hlt
          · omega
          · rfl
        rw [h0, zero_add]
        have hterm_nn : ∀ j ∈ Finset.range J,
            0 ≤ (((k + 1 : ℕ) : ℝ) * u k) /
              (((k + j + 1 : ℕ) : ℝ) * ((k + j + 2 : ℕ) : ℝ)) :=
          fun j _ => div_nonneg (mul_nonneg (by positivity) huk.le) (by positivity)
        have hT_eq : (∑ j ∈ Finset.range J, T (k + j) k) =
            ENNReal.ofReal (∑ j ∈ Finset.range J,
              (((k + 1 : ℕ) : ℝ) * u k) /
                (((k + j + 1 : ℕ) : ℝ) * ((k + j + 2 : ℕ) : ℝ))) := by
          rw [ENNReal.ofReal_sum_of_nonneg hterm_nn]
          refine Finset.sum_congr rfl fun j _ => ?_
          dsimp [T]
          split_ifs with hlt
          · rfl
          · omega
        rw [hT_eq]
        refine ENNReal.ofReal_le_ofReal ?_
        have hfactor :
            (∑ j ∈ Finset.range J,
              (((k + 1 : ℕ) : ℝ) * u k) /
                (((k + j + 1 : ℕ) : ℝ) * ((k + j + 2 : ℕ) : ℝ))) =
            (((k + 1 : ℕ) : ℝ) * u k) *
              (∑ j ∈ Finset.range J,
                (1 : ℝ) / (((k + j + 1 : ℕ) : ℝ) * ((k + j + 2 : ℕ) : ℝ))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [hfactor, htele J]
        have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
        have hJk1 : (0 : ℝ) ≤ 1 / ((k + J + 1 : ℕ) : ℝ) := by positivity
        calc
          (((k + 1 : ℕ) : ℝ) * u k) * (1 / ((k + 1 : ℕ) : ℝ) - 1 / ((k + J + 1 : ℕ) : ℝ))
            ≤ (((k + 1 : ℕ) : ℝ) * u k) * (1 / ((k + 1 : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by positivity) huk.le)
          _ = u k := by field_simp [hk1.ne']
    have h_n_le : ∀ n : ℕ,
        ENNReal.ofReal ((M (n + 1)) ^ (-(1 / ((n + 1 : ℕ) : ℝ)))) ≤
          ENNReal.ofReal (Real.exp 1) * ∑' k : ℕ, T n k := by
      intro n
      have hsum_T : (∑' k : ℕ, T n k) =
          ENNReal.ofReal (∑ k ∈ Finset.range (n + 1),
            (((k + 1 : ℕ) : ℝ) * u k) /
              (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) := by
        rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun k hk => by
          dsimp [T]
          split_ifs with hlt
          · exact absurd (Finset.mem_range.mpr hlt) hk
          · rfl)]
        rw [ENNReal.ofReal_sum_of_nonneg
          (fun k _ => div_nonneg (mul_nonneg (by positivity) (hu_pos k).le) (by positivity))]
        refine Finset.sum_congr rfl fun k hk => ?_
        dsimp [T]
        split_ifs with hlt
        · rfl
        · exact absurd (Finset.mem_range.mp hk) hlt
      rw [hsum_T, ← ENNReal.ofReal_mul (Real.exp_pos 1).le]
      exact ENNReal.ofReal_le_ofReal (hcarl n)
    calc
      (∑' n : ℕ, ENNReal.ofReal ((M (n + 1)) ^ (-(1 / ((n + 1 : ℕ) : ℝ)))))
        ≤ ∑' n : ℕ, ENNReal.ofReal (Real.exp 1) * ∑' k : ℕ, T n k :=
          ENNReal.tsum_le_tsum h_n_le
      _ = ENNReal.ofReal (Real.exp 1) * ∑' n : ℕ, ∑' k : ℕ, T n k := ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (Real.exp 1) * ∑' k : ℕ, ∑' n : ℕ, T n k := by rw [ENNReal.tsum_comm]
      _ ≤ ENNReal.ofReal (Real.exp 1) * ∑' k : ℕ, ENNReal.ofReal (u k) :=
          mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum hinner_k) zero_le
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top he

/-- Entire normalized sinc function `(1/2) ∫_{-1}^1 exp(i t w) dt`. -/
private def ch19Sinc (w : ℂ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) * ∫ t in (-1 : ℝ)..1, Complex.exp (Complex.I * (t : ℂ) * w)

private lemma ch19Sinc_eq_holomorphicFourierInterval (w : ℂ) :
    ch19Sinc w = holomorphicFourierInterval 1 (fun _ : ℝ => ((1 / 2 : ℝ) : ℂ)) w := by
  have heq := (holomorphicFourierInterval_endpoint_eq (by norm_num : (0 : ℝ) ≤ 1)
    (fun _ : ℝ => ((1 / 2 : ℝ) : ℂ)) w).2.2
  rw [heq]
  unfold ch19Sinc
  rw [← intervalIntegral.integral_const_mul]

private lemma differentiable_ch19Sinc : Differentiable ℂ ch19Sinc := by
  have hmem : MemLp (fun _ : ℝ => ((1 / 2 : ℝ) : ℂ)) 2 (volume.restrict (Set.Ioo (-1) 1)) :=
    memLp_const _
  have hent := (holomorphicFourierInterval_properties zero_lt_one hmem).2.1
  rw [show ch19Sinc = holomorphicFourierInterval 1 (fun _ : ℝ => ((1 / 2 : ℝ) : ℂ)) from
    funext ch19Sinc_eq_holomorphicFourierInterval]
  exact hent

private lemma ch19Sinc_zero : ch19Sinc 0 = 1 := by
  unfold ch19Sinc
  simp only [mul_zero, Complex.exp_zero, intervalIntegral.integral_const]
  norm_num

private lemma norm_ch19Sinc_le_exp_abs_im (w : ℂ) :
    ‖ch19Sinc w‖ ≤ Real.exp |w.im| := by
  unfold ch19Sinc
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hbd : ∀ t ∈ Set.uIoc (-1 : ℝ) 1,
      ‖Complex.exp (Complex.I * (t : ℂ) * w)‖ ≤ Real.exp |w.im| := by
    intro t ht
    have ht_cc : t ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
      exact ⟨ht.1.le, ht.2⟩
    rw [norm_exp_I_mul_real_mul_complex, Real.exp_le_exp]
    have h1 : |-t * w.im| ≤ |w.im| := by
      rw [abs_mul, abs_neg]
      have ht_abs : |t| ≤ 1 := abs_le.mpr ht_cc
      calc
        |t| * |w.im| ≤ 1 * |w.im| := mul_le_mul_of_nonneg_right ht_abs (abs_nonneg _)
        _ = |w.im| := one_mul _
    exact (le_abs_self _).trans h1
  calc
    (1 / 2 : ℝ) * ‖∫ t in (-1 : ℝ)..1, Complex.exp (Complex.I * (t : ℂ) * w)‖
      ≤ (1 / 2 : ℝ) * (Real.exp |w.im| * |1 - (-1 : ℝ)|) :=
        mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_of_norm_le_const hbd)
          (by norm_num)
    _ = Real.exp |w.im| := by norm_num; ring

private lemma norm_ch19Sinc_real_le_one (x : ℝ) : ‖ch19Sinc (x : ℂ)‖ ≤ 1 := by
  simpa using norm_ch19Sinc_le_exp_abs_im (x : ℂ)

private lemma norm_ch19Sinc_real_le_inv_abs {x : ℝ} (hx : x ≠ 0) :
    ‖ch19Sinc (x : ℂ)‖ ≤ 1 / |x| := by
  unfold ch19Sinc
  have hix_ne : Complex.I * (x : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hx)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) / (Complex.I * (x : ℂ)))
    (f' := fun t : ℝ => Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)))
    (a := -1) (b := 1)
    (fun t _ => by
      have hd1 : HasDerivAt (fun z : ℂ => Complex.exp (Complex.I * z * (x : ℂ)))
          (Complex.I * (x : ℂ) * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) (t : ℂ) := by
        have hlin : HasDerivAt (fun z : ℂ => Complex.I * z * (x : ℂ))
            (Complex.I * (x : ℂ)) (t : ℂ) := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            ((hasDerivAt_id (t : ℂ)).const_mul Complex.I).mul_const (x : ℂ)
        exact hlin.cexp.congr_deriv (by ring)
      exact (hd1.comp_ofReal.div_const (Complex.I * (x : ℂ))).congr_deriv
        (mul_div_cancel_left₀ _ hix_ne))
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [hftc, ← sub_div, norm_mul, norm_div, norm_mul, Complex.norm_I, one_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hnum : ‖Complex.exp (Complex.I * ((1 : ℝ) : ℂ) * (x : ℂ)) -
      Complex.exp (Complex.I * ((-1 : ℝ) : ℂ) * (x : ℂ))‖ ≤ 2 := by
    calc
      ‖Complex.exp (Complex.I * ((1 : ℝ) : ℂ) * (x : ℂ)) -
          Complex.exp (Complex.I * ((-1 : ℝ) : ℂ) * (x : ℂ))‖
        ≤ ‖Complex.exp (Complex.I * ((1 : ℝ) : ℂ) * (x : ℂ))‖ +
            ‖Complex.exp (Complex.I * ((-1 : ℝ) : ℂ) * (x : ℂ))‖ := norm_sub_le _ _
      _ = 1 + 1 := by
          rw [norm_exp_I_mul_real_mul_real, norm_exp_I_mul_real_mul_real]
      _ = 2 := by norm_num
  have hx_abs : 0 < |x| := abs_pos.mpr hx
  calc
    (1 / 2 : ℝ) * (‖Complex.exp (Complex.I * ((1 : ℝ) : ℂ) * (x : ℂ)) -
        Complex.exp (Complex.I * ((-1 : ℝ) : ℂ) * (x : ℂ))‖ / |x|)
      ≤ (1 / 2 : ℝ) * (2 / |x|) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hx_abs.le) (by norm_num)
    _ = 1 / |x| := by ring

private lemma norm_one_sub_ch19Sinc_le (w : ℂ) :
    ‖1 - ch19Sinc w‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
  have hexp_sub : ∀ u : ℂ, ‖1 - Complex.exp u‖ ≤ ‖u‖ * Real.exp ‖u‖ := by
    intro u
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => Complex.exp ((s : ℂ) * u))
      (f' := fun s : ℝ => u * Complex.exp ((s : ℂ) * u))
      (a := 0) (b := 1)
      (fun s _ => by
        have hd : HasDerivAt (fun z : ℂ => Complex.exp (z * u))
            (u * Complex.exp ((s : ℂ) * u)) (s : ℂ) := by
          simpa [mul_comm] using ((hasDerivAt_id (s : ℂ)).mul_const u).cexp
        exact hd.comp_ofReal)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    have h1 : 1 - Complex.exp u = -(∫ s in (0 : ℝ)..1, u * Complex.exp ((s : ℂ) * u)) := by
      rw [hftc]; simp
    rw [h1, norm_neg]
    have hbd : ∀ s ∈ Set.uIoc (0 : ℝ) 1, ‖u * Complex.exp ((s : ℂ) * u)‖ ≤ ‖u‖ * Real.exp ‖u‖ := by
      intro s hs
      rw [Set.uIoc_of_le zero_le_one] at hs
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg u)
      calc
        ‖Complex.exp ((s : ℂ) * u)‖ ≤ Real.exp ‖(s : ℂ) * u‖ := Complex.norm_exp_le_exp_norm _
        _ ≤ Real.exp ‖u‖ := by
            rw [Real.exp_le_exp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hs.1]
            exact mul_le_of_le_one_left (norm_nonneg u) hs.2
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbd
  have h1_int : (1 : ℂ) = ((1 / 2 : ℝ) : ℂ) * ∫ _t in (-1 : ℝ)..1, (1 : ℂ) := by
    simp [intervalIntegral.integral_const]; norm_num
  have hdiff : 1 - ch19Sinc w =
      ((1 / 2 : ℝ) : ℂ) * ∫ t in (-1 : ℝ)..1, (1 - Complex.exp (Complex.I * (t : ℂ) * w)) := by
    nth_rw 1 [h1_int]
    unfold ch19Sinc
    rw [← mul_sub, ← intervalIntegral.integral_sub intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hbd : ∀ t ∈ Set.uIoc (-1 : ℝ) 1,
      ‖1 - Complex.exp (Complex.I * (t : ℂ) * w)‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
    have ht_abs : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have hnorm_le : ‖Complex.I * (t : ℂ) * w‖ ≤ ‖w‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg w) ht_abs
    exact (hexp_sub _).trans (mul_le_mul hnorm_le (Real.exp_le_exp.mpr hnorm_le)
      (Real.exp_pos _).le (norm_nonneg w))
  calc
    (1 / 2 : ℝ) * ‖∫ t in (-1 : ℝ)..1, (1 - Complex.exp (Complex.I * (t : ℂ) * w))‖
      ≤ (1 / 2 : ℝ) * ((‖w‖ * Real.exp ‖w‖) * |1 - (-1 : ℝ)|) :=
        mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_of_norm_le_const hbd)
          (by norm_num)
    _ = ‖w‖ * Real.exp ‖w‖ := by norm_num; ring

/-- Implication `(e) → (a)` in Theorem 19.11 via an entire infinite product of `sinc` factors and
Theorem 19.3 (Second Paley–Wiener Theorem). -/
theorem dc_e_imp_a {M : ℕ → ℝ} (hM : IsPosNormLogConvex M)
    (he : (∑' k : ℕ, ENNReal.ofReal (M k / M (k + 1))) < ⊤) :
    ¬ IsQuasiAnalytic M := by
  let u : ℕ → ℝ := fun k => M k / M (k + 1)
  have hu_pos : ∀ k : ℕ, 0 < u k := fun k => div_pos (hM.1 k) (hM.1 (k + 1))
  have hu_sum : Summable u :=
    (tsum_ofReal_lt_top_iff_summable (fun k => (hu_pos k).le)).mp he
  -- Sequence c_0 = u 0, c_1 = u 0, c_{k+2} = u k
  let c : ℕ → ℝ := fun m =>
    match m with
    | 0 => u 0
    | 1 => u 0
    | k + 2 => u k
  have hc_pos : ∀ m : ℕ, 0 < c m := by
    intro m; rcases m with _ | _ | k <;> exact hu_pos _
  have hc_shift : (fun k : ℕ => c (k + 2)) = u := rfl
  have hc_sum : Summable c := (summable_nat_add_iff 2).mp (hc_shift ▸ hu_sum)
  let A : ℝ := ∑' m : ℕ, c m
  have hc_le_A : ∀ m : ℕ, c m ≤ A :=
    fun m => Summable.le_tsum hc_sum m (fun j _ => (hc_pos j).le)
  have hA_pos : 0 < A := lt_of_lt_of_le (hc_pos 0) (hc_le_A 0)
  -- Entire infinite product H(z) = ∏' m, ch19Sinc (c_m z) via Chapter 15 Theorem 15.6
  let fn : ℕ → ℂ → ℂ := fun m z => ch19Sinc ((c m : ℂ) * z)
  have hfn_diff : ∀ m : ℕ, DifferentiableOn ℂ (fn m) Set.univ := fun m =>
    (differentiable_ch19Sinc.comp ((differentiable_const (c m : ℂ)).mul differentiable_id)).differentiableOn
  have hfn_nz : ∀ (m : ℕ) (z : ℂ), z ∈ (Set.univ : Set ℂ) →
      ∃ w ∈ connectedComponentIn (Set.univ : Set ℂ) z, fn m w ≠ 0 := by
    intro m z _
    refine ⟨0, ?_, ?_⟩
    · rw [isPreconnected_univ.connectedComponentIn (Set.mem_univ z)]
      trivial
    · dsimp [fn]; rw [mul_zero, ch19Sinc_zero]; exact one_ne_zero
  have hseries : ∃ S : ℂ → ℝ, TendstoLocallyUniformlyOn
      (fun N z => ∑ m ∈ Finset.range N, ‖1 - fn m z‖) S atTop Set.univ := by
    refine ⟨fun z => ∑' m : ℕ, ‖1 - fn m z‖, ?_⟩
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    let R' : ℝ := max R 1
    have hR'_pos : 0 < R' := lt_max_of_lt_right zero_lt_one
    have hdom_sum : Summable (fun m : ℕ => (R' * Real.exp (A * R')) * c m) :=
      hc_sum.mul_left _
    have hbd_K : ∀ (m : ℕ) (z : ℂ), z ∈ K →
        ‖1 - fn m z‖ ≤ (R' * Real.exp (A * R')) * c m := by
      intro m z hz
      have hz_norm : ‖z‖ ≤ R' := by
        have h1 := hKR hz
        rw [Metric.mem_closedBall, dist_zero_right] at h1
        exact h1.trans (le_max_left R 1)
      have hcmz : ‖(c m : ℂ) * z‖ = c m * ‖z‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hc_pos m)]
      calc
        ‖1 - fn m z‖ ≤ ‖(c m : ℂ) * z‖ * Real.exp ‖(c m : ℂ) * z‖ :=
          norm_one_sub_ch19Sinc_le _
        _ = (c m * ‖z‖) * Real.exp (c m * ‖z‖) := by rw [hcmz]
        _ ≤ (c m * R') * Real.exp (A * R') := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hz_norm (hc_pos m).le) ?_
              (Real.exp_pos _).le (mul_nonneg (hc_pos m).le hR'_pos.le)
            exact Real.exp_le_exp.mpr (mul_le_mul (hc_le_A m) hz_norm
              (norm_nonneg z) hA_pos.le)
        _ = (R' * Real.exp (A * R')) * c m := by ring
    exact tendstoUniformlyOn_tsum_nat hdom_sum fun m z hz => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact hbd_K m z hz
  obtain ⟨H, hH_diff_on, hH_loc, _, _⟩ :=
    RudinRCA.Chapter15.theorem15_6 isOpen_univ hfn_diff hfn_nz hseries
  have hH_entire : Differentiable ℂ H := differentiableOn_univ.mp hH_diff_on
  have hH_tendsto : ∀ z : ℂ,
      Tendsto (fun N : ℕ => ∏ m ∈ Finset.range N, fn m z) atTop (𝓝 (H z)) :=
    fun z => hH_loc.tendsto_at trivial
  have hH_zero : H 0 = 1 := by
    have h1 : ∀ N : ℕ, ∏ m ∈ Finset.range N, fn m 0 = 1 := by
      intro N
      refine Finset.prod_eq_one fun m _ => ?_
      dsimp [fn]; rw [mul_zero, ch19Sinc_zero]
    exact tendsto_nhds_unique (hH_tendsto 0) (by simp_rw [h1]; exact tendsto_const_nhds)
  -- Exponential type bound ‖H z‖ ≤ 1 * exp(A ‖z‖)
  have hH_exp_bd : ∀ z : ℂ, ‖H z‖ ≤ 1 * Real.exp (A * ‖z‖) := by
    intro z
    rw [one_mul]
    refine le_of_tendsto ((continuous_norm.tendsto (H z)).comp (hH_tendsto z)) ?_
    refine Eventually.of_forall fun N => ?_
    dsimp only [Function.comp_apply]
    rw [norm_prod]
    calc
      (∏ m ∈ Finset.range N, ‖fn m z‖)
        ≤ ∏ m ∈ Finset.range N, Real.exp (c m * ‖z‖) := by
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun m _ => ?_
          dsimp [fn]
          have him : |((c m : ℂ) * z).im| ≤ c m * ‖z‖ := by
            calc
              |((c m : ℂ) * z).im| ≤ ‖(c m : ℂ) * z‖ := Complex.abs_im_le_norm _
              _ = c m * ‖z‖ := by
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hc_pos m)]
          exact (norm_ch19Sinc_le_exp_abs_im _).trans (Real.exp_le_exp.mpr him)
      _ = Real.exp (∑ m ∈ Finset.range N, c m * ‖z‖) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (A * ‖z‖) := by
          rw [← Finset.sum_mul]
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
            (Summable.sum_le_tsum (Finset.range N) (fun j _ => (hc_pos j).le) hc_sum)
            (norm_nonneg z))
  -- Real moment & decay bound: (1 + (c 0 * x)^2) * |x|^n * ‖H x‖ ≤ 2 * M n
  have hH_moment : ∀ (n : ℕ) (x : ℝ),
      (1 + (c 0 * x) ^ 2) * |x| ^ n * ‖H (x : ℂ)‖ ≤ 2 * M n := by
    intro n x
    have hnorm_lim : Tendsto
        (fun N : ℕ => (1 + (c 0 * x) ^ 2) * |x| ^ n * ‖∏ m ∈ Finset.range N, fn m (x : ℂ)‖)
        atTop (𝓝 ((1 + (c 0 * x) ^ 2) * |x| ^ n * ‖H (x : ℂ)‖)) :=
      tendsto_const_nhds.mul ((continuous_norm.tendsto _).comp (hH_tendsto (x : ℂ)))
    refine le_of_tendsto hnorm_lim ?_
    filter_upwards [eventually_ge_atTop (n + 2)] with N hN
    rw [norm_prod]
    have hfn_real_le1 : ∀ m : ℕ, ‖fn m (x : ℂ)‖ ≤ 1 := by
      intro m
      dsimp [fn]
      rw [← Complex.ofReal_mul]
      exact norm_ch19Sinc_real_le_one (c m * x)
    -- Drop tail factors m ≥ n + 2 (each ∈ [0, 1])
    have hprod_drop : (∏ m ∈ Finset.range N, ‖fn m (x : ℂ)‖) ≤
        ∏ m ∈ Finset.range (n + 2), ‖fn m (x : ℂ)‖ := by
      have hsplit : Finset.range N =
          Finset.range (n + 2) ∪ Finset.Ico (n + 2) N := by
        ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      have hdisj : Disjoint (Finset.range (n + 2)) (Finset.Ico (n + 2) N) := by
        rw [Finset.disjoint_left]
        intro j hj1 hj2
        rw [Finset.mem_range] at hj1
        rw [Finset.mem_Ico] at hj2
        omega
      rw [hsplit, Finset.prod_union hdisj]
      refine mul_le_of_le_one_right
        (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun m _ => hfn_real_le1 m)
    by_cases hcx : |c 0 * x| ≤ 1
    · -- Small |x|: |c 0 * x| ≤ 1 implies |x| ≤ M 1, so |x|^n ≤ (M 1)^n ≤ M n
      have hc0_eq : c 0 = 1 / M 1 := by dsimp [c, u]; rw [hM.2.1]
      have hx_le_M1 : |x| ≤ M 1 := by
        rw [abs_mul, abs_of_pos (hc_pos 0), hc0_eq, one_div] at hcx
        simpa using (inv_mul_le_iff₀ (hM.1 1)).mp hcx
      have h1_le2 : 1 + (c 0 * x) ^ 2 ≤ 2 := by
        have hsq : (c 0 * x) ^ 2 ≤ 1 := by
          rw [← sq_abs]
          nlinarith [abs_nonneg (c 0 * x)]
        linarith
      have hxn_le : |x| ^ n ≤ M n :=
        (pow_le_pow_left₀ (abs_nonneg x) hx_le_M1 n).trans (hM.pow_one_le n)
      have hprod_le1 : ∏ m ∈ Finset.range (n + 2), ‖fn m (x : ℂ)‖ ≤ 1 :=
        Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun m _ => hfn_real_le1 m
      calc
        (1 + (c 0 * x) ^ 2) * |x| ^ n * ∏ m ∈ Finset.range N, ‖fn m (x : ℂ)‖
          ≤ (1 + (c 0 * x) ^ 2) * |x| ^ n * 1 :=
            mul_le_mul_of_nonneg_left (hprod_drop.trans hprod_le1) (by positivity)
        _ = (1 + (c 0 * x) ^ 2) * |x| ^ n := mul_one _
        _ ≤ 2 * M n := mul_le_mul h1_le2 hxn_le (pow_nonneg (abs_nonneg x) n) zero_le_two
    · -- Large |x|: 1 < |c 0 * x|, bound each of the first n + 2 factors by 1 / |c_m * x|
      push Not at hcx
      have hx_ne : x ≠ 0 := by
        rintro rfl; simp at hcx; linarith
      have hx_abs_pos : 0 < |x| := abs_pos.mpr hx_ne
      have hfac_inv : ∀ m : ℕ, ‖fn m (x : ℂ)‖ ≤ 1 / (c m * |x|) := by
        intro m
        dsimp [fn]
        rw [← Complex.ofReal_mul]
        have hcm_x_ne : c m * x ≠ 0 := mul_ne_zero (hc_pos m).ne' hx_ne
        simpa [abs_mul, abs_of_pos (hc_pos m)] using norm_ch19Sinc_real_le_inv_abs hcm_x_ne
      -- Split range (n + 2) = {0, 1} + shift by 2 of range n
      have hprod_split : (∏ m ∈ Finset.range (n + 2), ‖fn m (x : ℂ)‖) =
          ‖fn 0 (x : ℂ)‖ * ‖fn 1 (x : ℂ)‖ *
            ∏ k ∈ Finset.range n, ‖fn (k + 2) (x : ℂ)‖ := by
        clear hnorm_lim hprod_drop hN
        induction n with
        | zero =>
          simp [Finset.prod_range_succ]
        | succ r ihr =>
          rw [show r + 1 + 2 = (r + 2) + 1 from by omega, Finset.prod_range_succ, ihr,
            Finset.prod_range_succ, mul_assoc]
      have h01 : ‖fn 0 (x : ℂ)‖ * ‖fn 1 (x : ℂ)‖ ≤ 1 / (c 0 * x) ^ 2 := by
        have h0 := hfac_inv 0
        have h1 : ‖fn 1 (x : ℂ)‖ ≤ 1 / (c 0 * |x|) := hfac_inv 1
        have hc0_pos : 0 < c 0 := hc_pos 0
        calc
          ‖fn 0 (x : ℂ)‖ * ‖fn 1 (x : ℂ)‖
            ≤ (1 / (c 0 * |x|)) * (1 / (c 0 * |x|)) :=
              mul_le_mul h0 h1 (norm_nonneg _) (by positivity)
          _ = 1 / (c 0 * x) ^ 2 := by
              rw [div_mul_div_comm, one_mul, ← sq, mul_pow, sq_abs, ← mul_pow]
      have htail_n : (∏ k ∈ Finset.range n, ‖fn (k + 2) (x : ℂ)‖) ≤ M n / |x| ^ n := by
        calc
          (∏ k ∈ Finset.range n, ‖fn (k + 2) (x : ℂ)‖)
            ≤ ∏ k ∈ Finset.range n, (1 / (c (k + 2) * |x|)) :=
              Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => hfac_inv (k + 2)
          _ = ∏ k ∈ Finset.range n, ((M (k + 1) / M k) / |x|) := by
              refine Finset.prod_congr rfl fun k _ => ?_
              dsimp [c, u]
              field_simp [(hM.1 k).ne', (hM.1 (k + 1)).ne', hx_abs_pos.ne']
          _ = M n / |x| ^ n := by
              rw [Finset.prod_div_distrib, prod_ratio_eq_M hM n, Finset.prod_const,
                Finset.card_range]
      have hquad : (1 + (c 0 * x) ^ 2) * (1 / (c 0 * x) ^ 2) ≤ 2 := by
        have hsq1 : 1 < (c 0 * x) ^ 2 := by
          rw [← sq_abs]
          nlinarith
        have hsq_pos : 0 < (c 0 * x) ^ 2 := lt_trans zero_lt_one hsq1
        rw [mul_one_div, div_le_iff₀ hsq_pos]
        linarith
      calc
        (1 + (c 0 * x) ^ 2) * |x| ^ n * ∏ m ∈ Finset.range N, ‖fn m (x : ℂ)‖
          ≤ (1 + (c 0 * x) ^ 2) * |x| ^ n * ∏ m ∈ Finset.range (n + 2), ‖fn m (x : ℂ)‖ :=
            mul_le_mul_of_nonneg_left hprod_drop (by positivity)
        _ ≤ (1 + (c 0 * x) ^ 2) * |x| ^ n * ((1 / (c 0 * x) ^ 2) * (M n / |x| ^ n)) := by
            rw [hprod_split]
            refine mul_le_mul_of_nonneg_left
              (mul_le_mul h01 htail_n (Finset.prod_nonneg fun _ _ => norm_nonneg _)
                (by positivity)) (by positivity)
        _ = ((1 + (c 0 * x) ^ 2) * (1 / (c 0 * x) ^ 2)) * M n := by
            have hxn_ne : |x| ^ n ≠ 0 := pow_ne_zero n hx_abs_pos.ne'
            field_simp [hxn_ne]
        _ ≤ 2 * M n := mul_le_mul_of_nonneg_right hquad (hM.1 n).le
  -- Integrability of 1 / (1 + (c 0 * x)^2) on ℝ
  let dom : ℝ → ℝ := fun x => 1 / (1 + (c 0 * x) ^ 2)
  have hdom_int : Integrable dom volume := by
    have hc0 : 0 < c 0 := hc_pos 0
    have hderiv : ∀ x : ℝ, HasDerivAt (fun t : ℝ => (1 / c 0) * Real.arctan (c 0 * t))
        (dom x) x := by
      intro x
      have hd1 : HasDerivAt (fun t : ℝ => c 0 * t) (c 0) x := by
        simpa using (hasDerivAt_id x).const_mul (c 0)
      refine ((Real.hasDerivAt_arctan (c 0 * x)).comp x hd1 |>.const_mul (1 / c 0)).congr_deriv ?_
      dsimp [dom]
      field_simp [hc0.ne']
    have hcont : Continuous dom := by
      dsimp [dom]
      exact continuous_const.div (continuous_const.add ((continuous_const.mul continuous_id).pow 2))
        fun x => by positivity
    have hmono : MonotoneOn (fun t : ℝ => (1 / c 0) * Real.arctan (c 0 * t)) Set.univ := by
      intro x _ y _ hxy
      exact mul_le_mul_of_nonneg_left
        (Real.arctan_mono (mul_le_mul_of_nonneg_left hxy hc0.le)) (by positivity)
    refine ⟨hcont.aestronglyMeasurable, ?_⟩
    change (∫⁻ x : ℝ, ‖dom x‖ₑ) < ⊤
    have hnn : ∀ x : ℝ, ‖dom x‖ₑ = ENNReal.ofReal (dom x) := fun x => by
      dsimp [dom]
      rw [Real.enorm_eq_ofReal (by positivity)]
    simp_rw [hnn]
    rw [← setLIntegral_univ,
      lintegral_deriv_eq_volume_image_of_monotoneOn MeasurableSet.univ
        (fun x _ => (hderiv x).hasDerivWithinAt) hmono]
    have himg : (fun t : ℝ => (1 / c 0) * Real.arctan (c 0 * t)) '' Set.univ ⊆
        Set.Icc (-(Real.pi / (2 * c 0))) (Real.pi / (2 * c 0)) := by
      rintro _ ⟨x, _, rfl⟩
      have h1 := (Real.neg_pi_div_two_lt_arctan (c 0 * x)).le
      have h2 := (Real.arctan_lt_pi_div_two (c 0 * x)).le
      refine ⟨?_, ?_⟩
      · calc
          -(Real.pi / (2 * c 0)) = (1 / c 0) * (-(Real.pi / 2)) := by ring
          _ ≤ (1 / c 0) * Real.arctan (c 0 * x) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
      · calc
          (1 / c 0) * Real.arctan (c 0 * x) ≤ (1 / c 0) * (Real.pi / 2) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = Real.pi / (2 * c 0) := by ring
    exact lt_of_le_of_lt (measure_mono himg) (by simp [Real.volume_Icc])
  -- H|_ℝ ∈ L¹(ℝ) ∩ L²(ℝ)
  let h : ℝ → ℂ := fun x => H (x : ℂ)
  have hh_cont : Continuous h := hH_entire.continuous.comp Complex.continuous_ofReal
  have hh_le_dom : ∀ x : ℝ, ‖h x‖ ≤ 2 * dom x := by
    intro x
    have hm0 := hH_moment 0 x
    rw [pow_zero, mul_one, hM.2.1, mul_one] at hm0
    dsimp [h, dom]
    have hpos : 0 < 1 + (c 0 * x) ^ 2 := by positivity
    rw [mul_one_div, le_div_iff₀' hpos]
    exact hm0
  have hh_int1 : Integrable h volume := by
    refine (hdom_int.const_mul 2).mono' hh_cont.aestronglyMeasurable ?_
    filter_upwards with x
    exact hh_le_dom x
  have hh_mem2 : MemLp h 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hh_cont.aestronglyMeasurable).mpr ?_
    refine (hdom_int.const_mul 4).mono' (hh_cont.norm.pow 2).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hdom_le1 : dom x ≤ 1 := by
      dsimp [dom]
      exact div_le_one_of_le₀ (by linarith [sq_nonneg (c 0 * x)]) (by positivity)
    calc
      ‖h x‖ ^ 2 ≤ (2 * dom x) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hh_le_dom x) 2
      _ = 4 * dom x * dom x := by ring
      _ ≤ 4 * dom x * 1 :=
        mul_le_mul_of_nonneg_left hdom_le1 (by dsimp [dom]; positivity)
      _ = 4 * dom x := mul_one _
  -- Apply Second Paley–Wiener Theorem (theorem19_3) to H
  obtain ⟨F, _, hF_mem2_Icc, hH_rep, _, _⟩ :=
    theorem19_3 hA_pos zero_lt_one hH_entire hH_exp_bd hh_mem2
  -- Define φ := ch19InvFourier h and show φ =ᵐ F_ext := indicator [-A, A] F
  let φ : ℝ → ℂ := ch19InvFourier h
  have hφ_cont : Continuous φ := continuous_ch19InvFourier_of_integrable hh_int1
  let F_ext : ℝ → ℂ := Set.indicator (Set.Icc (-A) A) F
  have hF_ext_int1 : Integrable F_ext volume := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact hF_mem2_Icc.integrable one_le_two
  have hFourier_F_ext : ∀ x : ℝ, ch19Fourier F_ext x = h x := by
    intro x
    dsimp only [h]
    rw [hH_rep (x : ℂ)]
    unfold ch19Fourier holomorphicFourierInterval
    rw [← integral_indicator measurableSet_Icc]
    congr 1 with t
    by_cases ht : t ∈ Set.Icc (-A) A
    · simp [F_ext, ht]
    · simp [F_ext, ht]
  have hφ_ae_F_ext : F_ext =ᵐ[volume] φ := by
    have hinv_F_ext : ch19InvFourier F_ext =
        fun y : ℝ => ((1 / (2 * Real.pi) : ℝ) : ℂ) * h (-y) := by
      ext y
      unfold ch19InvFourier
      congr 1
      rw [← hFourier_F_ext (-y)]
      unfold ch19Fourier
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      dsimp only
      congr 1
      exact congr_arg Complex.exp (by push_cast; ring)
    have hmp_neg := Measure.measurePreserving_neg (volume : Measure ℝ)
    have hinv_F_ext_int : Integrable (ch19InvFourier F_ext) volume := by
      rw [hinv_F_ext]
      have hh_neg_int : Integrable (fun y : ℝ => h (-y)) volume :=
        (hmp_neg.integrable_comp_emb (Homeomorph.neg ℝ).measurableEmbedding (g := h)).mpr hh_int1
      exact hh_neg_int.const_mul _
    have hae := ch19_fourier_inversion_ae hF_ext_int1 hinv_F_ext_int
    have hrhs_eq : ch19Fourier (ch19InvFourier F_ext) = φ := by
      ext t
      unfold ch19Fourier
      rw [hinv_F_ext]
      have hpull : (fun y : ℝ => (((1 / (2 * Real.pi) : ℝ) : ℂ) * h (-y)) *
            Complex.exp (Complex.I * (y : ℂ) * (t : ℂ))) =
          fun y : ℝ => ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (h (-y) * Complex.exp (Complex.I * (y : ℂ) * (t : ℂ))) :=
        funext fun _ => mul_assoc _ _ _
      rw [hpull, integral_const_mul]
      dsimp [φ, ch19InvFourier]
      congr 1
      let ψ : ℝ → ℂ := fun x => h x * Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))
      have hψ_neg : (fun y : ℝ => h (-y) * Complex.exp (Complex.I * (y : ℂ) * (t : ℂ))) =
          fun y : ℝ => ψ (-y) := by
        ext y
        dsimp [ψ]
        congr 1
        exact congr_arg Complex.exp (by push_cast; ring)
      rw [hψ_neg]
      exact hmp_neg.integral_comp (Homeomorph.neg ℝ).measurableEmbedding ψ
    rwa [hrhs_eq] at hae
  -- Support of φ lies in [-A, A] by continuity + F_ext =ᵐ φ
  have hφ_out : ∀ t : ℝ, t ∉ Set.Icc (-A) A → φ t = 0 := by
    intro t₀ ht₀
    by_contra hne
    let U : Set ℝ := (Set.Icc (-A) A)ᶜ ∩ {t : ℝ | φ t ≠ 0}
    have hU_open : IsOpen U :=
      isClosed_Icc.isOpen_compl.inter (isOpen_ne_fun hφ_cont continuous_const)
    have ht₀_U : t₀ ∈ U := ⟨ht₀, hne⟩
    obtain ⟨δ, hδ, hball_U⟩ := Metric.isOpen_iff.mp hU_open t₀ ht₀_U
    have hsub_ne : Metric.ball t₀ δ ⊆ {t : ℝ | F_ext t ≠ φ t} := by
      intro t ht
      obtain ⟨ht_out, hφt_ne⟩ := hball_U ht
      have hF0 : F_ext t = 0 := Set.indicator_of_notMem ht_out F
      change F_ext t ≠ φ t
      rw [hF0]
      exact hφt_ne.symm
    have hvol0 : volume {t : ℝ | F_ext t ≠ φ t} = 0 := ae_iff.mp hφ_ae_F_ext
    have hball0 : volume (Metric.ball t₀ δ) = 0 :=
      le_antisymm ((measure_mono hsub_ne).trans_eq hvol0) zero_le
    rw [Real.volume_ball] at hball0
    exact (ENNReal.ofReal_pos.mpr (by linarith : 0 < 2 * δ)).ne' hball0
  have hφ_supp : HasCompactSupport φ := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -A) (b := A)) fun t ht => ?_
    rw [Function.mem_support] at ht
    by_contra hnot
    exact ht (hφ_out t hnot)
  -- Nonvanishing of φ from ∫ F_ext = H 0 = 1
  have hφ_nonzero : ∃ t₀ : ℝ, φ t₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    have hae0 : F_ext =ᵐ[volume] (fun _ : ℝ => (0 : ℂ)) :=
      hφ_ae_F_ext.trans (Eventually.of_forall hall)
    have hint0 : ch19Fourier F_ext 0 = 0 := by
      unfold ch19Fourier
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hae0] with t ht
      simp [ht]
    rw [hFourier_F_ext 0] at hint0
    dsimp [h] at hint0
    rw [hH_zero] at hint0
    exact one_ne_zero hint0
  -- Smoothness and C{M_n} derivative bounds for φ via differentiation under the integral
  let Ker : ℕ → ℝ → ℝ → ℂ := fun n t x =>
    h x * (-Complex.I * (x : ℂ)) ^ n * Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))
  let ψ : ℕ → ℝ → ℂ := fun n t =>
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ x : ℝ, Ker n t x
  have hKer_norm : ∀ (n : ℕ) (t x : ℝ), ‖Ker n t x‖ ≤ (2 * M n) * dom x := by
    intro n t x
    dsimp [Ker]
    have hix_pow : ‖(-Complex.I * (x : ℂ)) ^ n‖ = |x| ^ n := by
      rw [norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul, norm_mul, hix_pow, norm_exp_neg_I_mul_real_mul_real, mul_one]
    have hm := hH_moment n x
    dsimp [h, dom]
    have hpos : 0 < 1 + (c 0 * x) ^ 2 := by positivity
    rw [mul_one_div, le_div_iff₀' hpos]
    linarith
  have hKer_int : ∀ (n : ℕ) (t : ℝ), Integrable (Ker n t) volume := by
    intro n t
    have hc : Continuous (Ker n t) := by
      dsimp [Ker]
      exact (hh_cont.mul (by fun_prop)).mul (by fun_prop)
    refine (hdom_int.const_mul (2 * M n)).mono' hc.aestronglyMeasurable ?_
    filter_upwards with x
    exact hKer_norm n t x
  have hψ_deriv : ∀ (n : ℕ) (t₀ : ℝ), HasDerivAt (ψ n) (ψ (n + 1) t₀) t₀ := by
    intro n t₀
    have hc0 : Continuous (Ker n t₀) := by
      dsimp [Ker]; exact (hh_cont.mul (by fun_prop)).mul (by fun_prop)
    have hc1 : Continuous (Ker (n + 1) t₀) := by
      dsimp [Ker]; exact (hh_cont.mul (by fun_prop)).mul (by fun_prop)
    have hmeas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (Ker n t) volume := by
      refine Eventually.of_forall fun t => ?_
      have hc : Continuous (Ker n t) := by
        dsimp [Ker]; exact (hh_cont.mul (by fun_prop)).mul (by fun_prop)
      exact hc.aestronglyMeasurable
    have hdiff_ker : ∀ (x t : ℝ), HasDerivAt (fun s : ℝ => Ker n s x) (Ker (n + 1) t x) t := by
      intro x t
      have hexp : HasDerivAt (fun z : ℂ => Complex.exp (-Complex.I * z * (x : ℂ)))
          ((-Complex.I * (x : ℂ)) * Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) (t : ℂ) := by
        have hlin : HasDerivAt (fun z : ℂ => -Complex.I * z * (x : ℂ))
            (-Complex.I * (x : ℂ)) (t : ℂ) := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            ((hasDerivAt_id (t : ℂ)).const_mul (-Complex.I)).mul_const (x : ℂ)
        exact hlin.cexp.congr_deriv (by ring)
      have hreal := (hexp.comp_ofReal).const_mul (h x * (-Complex.I * (x : ℂ)) ^ n)
      refine hreal.congr_deriv ?_
      dsimp [Ker]
      rw [pow_succ]
      ring
    have hdom_step := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := Ker n) (F' := Ker (n + 1)) (s := Set.univ) (x₀ := t₀) (μ := volume)
      (bound := fun x : ℝ => (2 * M (n + 1)) * dom x)
      univ_mem hmeas (hKer_int n t₀) hc1.aestronglyMeasurable
      (Eventually.of_forall fun x t _ => hKer_norm (n + 1) t x)
      (hdom_int.const_mul (2 * M (n + 1)))
      (Eventually.of_forall fun x t _ => hdiff_ker x t)).2
    exact hdom_step.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ))
  have hψ0_eq : ψ 0 = φ := by
    ext t
    dsimp [ψ, Ker, φ, ch19InvFourier]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => by simp)
  have hiter_φ : ∀ n : ℕ, iteratedDeriv n φ = ψ n := by
    intro n
    induction n with
    | zero => exact hψ0_eq.symm
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      ext t
      exact (hψ_deriv n t).deriv
  have hcd_nat : ∀ (m k : ℕ), ContDiff ℝ (m : ℕ) (ψ k) := by
    intro m
    induction m with
    | zero =>
      intro k
      exact contDiff_zero.mpr (Differentiable.continuous fun t => (hψ_deriv k t).differentiableAt)
    | succ m ih =>
      intro k
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨fun t => (hψ_deriv k t).differentiableAt, fun hω => by simp at hω, ?_⟩
      have hd_eq : deriv (ψ k) = ψ (k + 1) := funext fun t => (hψ_deriv k t).deriv
      rw [hd_eq]
      exact ih (k + 1)
  have hφ_cd : ContDiff ℝ ∞ φ := by
    rw [← hψ0_eq]
    exact contDiff_infty.mpr fun m => hcd_nat m 0
  let β_φ : ℝ := (1 / Real.pi) * (∫ x : ℝ, dom x) + 1
  have hdom_int_nn : 0 ≤ ∫ x : ℝ, dom x :=
    integral_nonneg fun x => by dsimp [dom]; positivity
  have hβ_φ_pos : 0 < β_φ := by
    dsimp [β_φ]
    have : 0 ≤ (1 / Real.pi) * ∫ x : ℝ, dom x := mul_nonneg (by positivity) hdom_int_nn
    linarith
  have hφ_CM : φ ∈ CM M := by
    refine ⟨hφ_cd, β_φ, hβ_φ_pos, 1, zero_lt_one, fun n t => ?_⟩
    rw [hiter_φ n, one_pow, mul_one]
    dsimp [ψ]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
    calc
      (1 / (2 * Real.pi)) * ‖∫ x : ℝ, Ker n t x‖
        ≤ (1 / (2 * Real.pi)) * ∫ x : ℝ, ‖Ker n t x‖ :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
      _ ≤ (1 / (2 * Real.pi)) * ∫ x : ℝ, (2 * M n) * dom x := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact integral_mono (hKer_int n t).norm (hdom_int.const_mul (2 * M n))
            fun x => hKer_norm n t x
      _ = ((1 / Real.pi) * ∫ x : ℝ, dom x) * M n := by
          rw [integral_const_mul]
          have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
          field_simp [hpi]
      _ ≤ β_φ * M n := by
          dsimp [β_φ]
          nlinarith [hM.1 n]
  -- Contradict quasi-analyticity via Theorem 19.10
  intro hQA
  exact (theorem19_10 hM).mp hQA ⟨φ, hφ_CM, hφ_supp, hφ_nonzero⟩

/-- Implication `(a) → (b)` in Theorem 19.11 via Theorem 19.10, integration by parts, Cayley
pullback to the unit disk, and Theorem 17.17 (`log |h*| ∈ L¹(T)` for nonzero `h ∈ H^∞(U)`). -/
theorem dc_a_imp_b {M : ℕ → ℝ} (hM : IsPosNormLogConvex M)
    (hnot_QA : ¬ IsQuasiAnalytic M) :
    (∫⁻ u in Set.Ioi (0 : ℝ), ennrealLog (dcQ M u) / ENNReal.ofReal (1 + u ^ 2)) < ⊤ := by
  -- Extract nonzero compactly supported g₀ ∈ CM M from Theorem 19.10
  have hex_cs : ∃ g₀ ∈ CM M, HasCompactSupport g₀ ∧ ∃ t₀ : ℝ, g₀ t₀ ≠ 0 := by
    by_contra hno
    exact hnot_QA ((theorem19_10 hM).mpr hno)
  obtain ⟨g₀, hg₀_CM, hg₀_supp, t₀, ht₀_ne⟩ := hex_cs
  obtain ⟨R₀, hR₀⟩ := hg₀_supp.isBounded.subset_closedBall (0 : ℝ)
  let R : ℝ := max R₀ 1
  have hR_pos : 0 < R := lt_max_of_lt_right zero_lt_one
  have hg₀_out : ∀ s : ℝ, s ∉ Set.Icc (-R) R → g₀ s = 0 := by
    intro s hs
    by_contra hgs
    have hcb := hR₀ (subset_tsupport g₀ hgs)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hcb
    have hs_abs : |s| ≤ R := hcb.trans (le_max_left R₀ 1)
    exact hs (abs_le.mp hs_abs)
  -- Shift g₀ so its support lies strictly inside (1/2, A - 1/2) ⊂ (0, A)
  let A : ℝ := 2 * R + 2
  have hA_pos : 0 < A := by dsimp [A]; linarith
  let g₁ : ℝ → ℂ := fun t => g₀ ((1 : ℝ) * t + (-R - 1))
  have hg₁_CM : g₁ ∈ CM M := CM_comp_affine hM.1 hg₀_CM 1 (-R - 1)
  rcases hg₁_CM with ⟨hg₁_cd, β₁, hβ₁_pos, B, hB_pos, hg₁_bd⟩
  -- Normalize scalar so ‖D^n g(t)‖ ≤ (1 / A) * B^n * M_n
  let c : ℝ := 1 / (A * β₁)
  have hc_pos : 0 < c := by dsimp [c]; positivity
  let g : ℝ → ℂ := fun t => (c : ℂ) * g₁ t
  have hg_cd : ContDiff ℝ ∞ g := contDiff_const.mul hg₁_cd
  have hg_margin : ∀ s : ℝ, (s < 1 / 2 ∨ A - 1 / 2 < s) → g s = 0 := by
    intro s hs
    dsimp [g, g₁]
    have hout : (1 : ℝ) * s + (-R - 1) ∉ Set.Icc (-R) R := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le]
      rcases hs with hs_lt | hs_gt
      · left; linarith
      · right; dsimp [A] at hs_gt; linarith
    rw [hg₀_out _ hout, mul_zero]
  have hg_out_0A : ∀ s : ℝ, (s ≤ 0 ∨ A ≤ s) → g s = 0 := by
    intro s hs
    refine hg_margin s ?_
    rcases hs with hs0 | hsA
    · left; linarith
    · right; linarith
  have hg_deriv_0 : ∀ n : ℕ, iteratedDeriv n g 0 = 0 := by
    intro n
    have hev : g =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℂ)) := by
      filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
      exact hg_margin s (Or.inl hs)
    rw [hev.iteratedDeriv_eq n]
    change iteratedDeriv n (fun _ : ℝ => (0 : ℂ)) 0 = 0
    rw [iteratedDeriv_const]
    split_ifs <;> rfl
  have hg_deriv_A : ∀ n : ℕ, iteratedDeriv n g A = 0 := by
    intro n
    have hev : g =ᶠ[𝓝 A] (fun _ => (0 : ℂ)) := by
      filter_upwards [Ioi_mem_nhds (by linarith : A - 1 / 2 < A)] with s hs
      exact hg_margin s (Or.inr hs)
    rw [hev.iteratedDeriv_eq n]
    change iteratedDeriv n (fun _ : ℝ => (0 : ℂ)) A = 0
    rw [iteratedDeriv_const]
    split_ifs <;> rfl
  have hg_iter_scale : ∀ (n : ℕ) (t : ℝ),
      iteratedDeriv n g t = (c : ℂ) * iteratedDeriv n g₁ t := by
    intro n
    induction n with
    | zero => intro t; rfl
    | succ n ih =>
      intro t
      rw [iteratedDeriv_succ, show iteratedDeriv n g = fun s => (c : ℂ) * iteratedDeriv n g₁ s from
        funext ih]
      have hd : DifferentiableAt ℝ (iteratedDeriv n g₁) t :=
        differentiable_iteratedDeriv_of_infty hg₁_cd n t
      rw [(hd.hasDerivAt.const_mul (c : ℂ)).deriv, ← iteratedDeriv_succ]
  have hg_bd : ∀ (n : ℕ) (t : ℝ), ‖iteratedDeriv n g t‖ ≤ (1 / A) * B ^ n * M n := by
    intro n t
    rw [hg_iter_scale n t, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc_pos]
    calc
      c * ‖iteratedDeriv n g₁ t‖ ≤ c * (β₁ * B ^ n * M n) :=
        mul_le_mul_of_nonneg_left (hg₁_bd n t) hc_pos.le
      _ = (1 / A) * B ^ n * M n := by
        dsimp [c]
        field_simp [hA_pos.ne', hβ₁_pos.ne']
  let t₁ : ℝ := t₀ + R + 1
  have hgt₁_ne : g t₁ ≠ 0 := by
    dsimp [g, g₁, t₁]
    have harg : (1 : ℝ) * (t₀ + R + 1) + (-R - 1) = t₀ := by ring
    rw [harg]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hc_pos.ne') ht₀_ne
  -- Entire transform f(z) = ∫_0^A g(t) exp(i t z) dt
  let f : ℂ → ℂ := fun z =>
    ∫ t in (0 : ℝ)..A, g t * Complex.exp (Complex.I * (t : ℂ) * z)
  have hf_eq_interval : ∀ z : ℂ, f z = holomorphicFourierInterval A g z := by
    intro z
    rw [(holomorphicFourierInterval_endpoint_eq hA_pos.le g z).2.2]
    have hcont_int : Continuous (fun t : ℝ => g t * Complex.exp (Complex.I * (t : ℂ) * z)) :=
      hg_cd.continuous.mul (by fun_prop)
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (a := -A) (b := 0) (c := A)
      (hcont_int.intervalIntegrable _ _) (hcont_int.intervalIntegrable _ _)]
    have hleft0 : (∫ t in (-A)..(0 : ℝ), g t * Complex.exp (Complex.I * (t : ℂ) * z)) = 0 := by
      rw [intervalIntegral.integral_of_le (by linarith : -A ≤ (0 : ℝ))]
      refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
      rw [hg_out_0A t (Or.inl ht.2), zero_mul]
    rw [hleft0, zero_add]
  have hg_mem2_Ioo : MemLp g 2 (volume.restrict (Set.Ioo (-A) A)) := by
    refine (memLp_two_iff_integrable_sq_norm hg_cd.continuous.aestronglyMeasurable).mpr ?_
    exact ((hg_cd.continuous.norm.pow 2).continuousOn.integrableOn_Icc).mono_set
      Set.Ioo_subset_Icc_self
  have hf_entire : Differentiable ℂ f := by
    rw [show f = holomorphicFourierInterval A g from funext hf_eq_interval]
    exact (holomorphicFourierInterval_properties hA_pos hg_mem2_Ioo).2.1
  -- Nonvanishing of f at some point z₀ in the open upper half-plane
  have hf_uhp_nonzero : ∃ z₀ : ℂ, 0 < z₀.im ∧ f z₀ ≠ 0 := by
    by_contra hall0
    push Not at hall0
    have hf_real0 : ∀ x : ℝ, f (x : ℂ) = 0 := by
      intro x
      have hseq : Tendsto (fun k : ℕ => f ((x : ℂ) + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * Complex.I))
          atTop (𝓝 (f (x : ℂ))) := by
        have htend_z : Tendsto
            (fun k : ℕ => (x : ℂ) + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * Complex.I)
            atTop (𝓝 ((x : ℂ) + (0 : ℂ) * Complex.I)) := by
          refine tendsto_const_nhds.add ((Complex.continuous_ofReal.tendsto 0 |>.comp ?_).mul_const _)
          exact tendsto_const_nhds.div_atTop
            ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
        have hcomp := (hf_entire.continuous.tendsto ((x : ℂ) + (0 : ℂ) * Complex.I)).comp htend_z
        simpa [Function.comp_def] using hcomp
      have hseq0 : ∀ k : ℕ, f ((x : ℂ) + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * Complex.I) = 0 := by
        intro k
        refine hall0 _ ?_
        simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero]
        positivity
      exact tendsto_nhds_unique hseq (by simp_rw [hseq0]; exact tendsto_const_nhds)
    have hg_supp : HasCompactSupport g := by
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 0) (b := A))
        fun s hs => ?_
      rw [Function.mem_support] at hs
      by_contra hout
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hout
      exact hs (hg_out_0A s (hout.imp le_of_lt le_of_lt))
    have hg_int1 : Integrable g volume := hg_cd.continuous.integrable_of_hasCompactSupport hg_supp
    have hg_sq_int : Integrable (fun t : ℝ => ‖g t‖ ^ 2) volume :=
      (hg_cd.continuous.norm.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 0) (b := A))
          fun s hs => by
            rw [Function.mem_support] at hs
            by_contra hout
            rw [Set.mem_Icc, not_and_or, not_le, not_le] at hout
            exact hs (by simp [hg_out_0A s (hout.imp le_of_lt le_of_lt)]))
    have hg_mem2 : MemLp g 2 volume :=
      (memLp_two_iff_integrable_sq_norm hg_cd.continuous.aestronglyMeasurable).mpr hg_sq_int
    have hFour_eq : ch19Fourier g = fun x : ℝ => f (x : ℂ) := by
      ext x
      rw [hf_eq_interval (x : ℂ)]
      unfold ch19Fourier holomorphicFourierInterval
      have hind : (fun t : ℝ => g t * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) =
          Set.indicator (Set.Icc (-A) A)
            (fun t : ℝ => g t * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) := by
        ext t
        by_cases ht : t ∈ Set.Icc (-A) A
        · simp [ht]
        · rw [Set.indicator_of_notMem ht]
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
          have hgt0 : g t = 0 := hg_out_0A t (ht.imp
            (fun hlt => by linarith) (fun hgt => by linarith))
          simp [hgt0]
      nth_rw 1 [hind]
      rw [integral_indicator measurableSet_Icc]
    have hplanch := (ch19Fourier_plancherel_L1_L2 hg_int1 hg_mem2).2
    rw [hFour_eq] at hplanch
    simp only [hf_real0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero, mul_zero] at hplanch
    have hae_sq0 : (fun t : ℝ => ‖g t‖ ^ 2) =ᵐ[volume] (fun _ : ℝ => (0 : ℝ)) :=
      (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hg_sq_int).mp hplanch.symm
    have hsq_eq0 := congr_fun
      ((Continuous.ae_eq_iff_eq volume (hg_cd.continuous.norm.pow 2) continuous_const).mp hae_sq0)
      t₁
    exact hgt₁_ne (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq_eq0))
  obtain ⟨z₀, hz₀_im, hfz₀_ne⟩ := hf_uhp_nonzero
  -- Integration by parts on [0, A]: (-i z)^n f(z) = ∫_0^A (D^n g)(t) exp(i t z) dt
  have hibp : ∀ (n : ℕ) (z : ℂ),
      (-Complex.I * z) ^ n * f z =
        ∫ t in (0 : ℝ)..A, iteratedDeriv n g t * Complex.exp (Complex.I * (t : ℂ) * z) := by
    intro n z
    induction n with
    | zero =>
      simp [f]
    | succ n ih =>
      let u : ℝ → ℂ := iteratedDeriv n g
      let v : ℝ → ℂ := fun t => Complex.exp (Complex.I * (t : ℂ) * z)
      have hu_cont : Continuous u := continuous_iteratedDeriv_of_infty hg_cd n
      have hu'_cont : Continuous (iteratedDeriv (n + 1) g) :=
        continuous_iteratedDeriv_of_infty hg_cd (n + 1)
      have hv_cont : Continuous v := by dsimp [v]; fun_prop
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t : ℝ => u t * v t)
        (f' := fun t : ℝ => iteratedDeriv (n + 1) g t * v t + (Complex.I * z) * (u t * v t))
        (a := 0) (b := A)
        (fun t _ => by
          have hdu : HasDerivAt u (iteratedDeriv (n + 1) g t) t := by
            rw [iteratedDeriv_succ]
            exact (differentiable_iteratedDeriv_of_infty hg_cd n t).hasDerivAt
          have hdv : HasDerivAt v ((Complex.I * z) * v t) t := by
            have hc : HasDerivAt (fun w : ℂ => Complex.exp (Complex.I * w * z))
                ((Complex.I * z) * Complex.exp (Complex.I * (t : ℂ) * z)) (t : ℂ) := by
              have hlin : HasDerivAt (fun w : ℂ => Complex.I * w * z)
                  (Complex.I * z) (t : ℂ) := by
                simpa [mul_assoc, mul_comm, mul_left_comm] using
                  ((hasDerivAt_id (t : ℂ)).const_mul Complex.I).mul_const z
              exact hlin.cexp.congr_deriv (by ring)
            exact hc.comp_ofReal
          exact (hdu.mul hdv).congr_deriv (by ring))
        (((hu'_cont.mul hv_cont).add (continuous_const.mul (hu_cont.mul hv_cont))).intervalIntegrable
          _ _)
      have hbdry : u A * v A - u 0 * v 0 = 0 := by
        dsimp [u]
        rw [hg_deriv_A n, hg_deriv_0 n, zero_mul, zero_mul, sub_self]
      rw [hbdry] at hftc
      rw [intervalIntegral.integral_add
        (f := fun y : ℝ => iteratedDeriv (n + 1) g y * v y)
        (g := fun y : ℝ => (Complex.I * z) * (u y * v y))
        ((hu'_cont.mul hv_cont).intervalIntegrable _ _)
        ((continuous_const.mul (hu_cont.mul hv_cont)).intervalIntegrable _ _),
        intervalIntegral.integral_const_mul] at hftc
      have hstep : (∫ t in (0 : ℝ)..A, iteratedDeriv (n + 1) g t * v t) =
          (-Complex.I * z) * ∫ t in (0 : ℝ)..A, u t * v t := by
        linear_combination hftc
      dsimp [u, v] at hstep
      rw [pow_succ', mul_assoc, ih, hstep]
  -- Upper half-plane moment bound: for z.im ≥ 0, ‖z‖^n * ‖f z‖ ≤ B^n * M_n
  have hf_uhp_bd : ∀ (n : ℕ) {z : ℂ}, 0 ≤ z.im → ‖z‖ ^ n * ‖f z‖ ≤ B ^ n * M n := by
    intro n z hzim
    have hnorm_lhs : ‖(-Complex.I * z) ^ n * f z‖ = ‖z‖ ^ n * ‖f z‖ := by
      rw [norm_mul, norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul]
    rw [← hnorm_lhs, hibp n z]
    have hpt : ∀ t ∈ Set.uIoc (0 : ℝ) A,
        ‖iteratedDeriv n g t * Complex.exp (Complex.I * (t : ℂ) * z)‖ ≤
          (1 / A) * B ^ n * M n := by
      intro t ht
      rw [Set.uIoc_of_le hA_pos.le] at ht
      rw [norm_mul, norm_exp_I_mul_real_mul_complex]
      have hexp1 : Real.exp (-t * z.im) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [ht.1]
      exact (mul_le_of_le_one_right (norm_nonneg _) hexp1).trans (hg_bd n t)
    calc
      ‖∫ t in (0 : ℝ)..A, iteratedDeriv n g t * Complex.exp (Complex.I * (t : ℂ) * z)‖
        ≤ ((1 / A) * B ^ n * M n) * |A - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hpt
      _ = B ^ n * M n := by
          rw [sub_zero, abs_of_pos hA_pos]
          field_simp [hA_pos.ne']
  have hf_le_one : ∀ {z : ℂ}, 0 ≤ z.im → ‖f z‖ ≤ 1 := by
    intro z hzim
    simpa [hM.2.1] using hf_uhp_bd 0 hzim
  -- Pointwise bound on dcQ M u via f(2 B u) for u > 0 when f(2 B u) ≠ 0
  have hdcQ_le_f : ∀ {u : ℝ}, 0 < u → f (((2 * B * u : ℝ) : ℂ)) ≠ 0 →
      dcQ M u ≤ ENNReal.ofReal (2 / ‖f (((2 * B * u : ℝ) : ℂ))‖) := by
    intro u hu hf_nz
    let x : ℝ := 2 * B * u
    have hx_pos : 0 < x := by dsimp [x]; positivity
    have hfx_pos : 0 < ‖f (x : ℂ)‖ := norm_pos_iff.mpr hf_nz
    have hterm : ∀ n : ℕ,
        ENNReal.ofReal (u ^ n / M n) ≤
          ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * ENNReal.ofReal (1 / ‖f (x : ℂ)‖) := by
      intro n
      have hbd_n := hf_uhp_bd n (z := (x : ℂ)) (by simp)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos] at hbd_n
      have hx_pow : x ^ n = (2 : ℝ) ^ n * B ^ n * u ^ n := by
        dsimp [x]; ring
      rw [hx_pow] at hbd_n
      have hcancel_B : (2 : ℝ) ^ n * u ^ n * ‖f (x : ℂ)‖ ≤ M n := by
        have hBn : 0 < B ^ n := pow_pos hB_pos n
        nlinarith
      have hdiv_le : u ^ n / M n ≤ (1 / 2 : ℝ) ^ n * (1 / ‖f (x : ℂ)‖) := by
        have hden_pos : 0 < (2 : ℝ) ^ n * ‖f (x : ℂ)‖ := mul_pos (by positivity) hfx_pos
        rw [one_div_pow, div_mul_div_comm, one_mul, div_le_div_iff₀ (hM.1 n) hden_pos]
        linarith
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hdiv_le
    calc
      dcQ M u ≤ ∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * ENNReal.ofReal (1 / ‖f (x : ℂ)‖) :=
        ENNReal.tsum_le_tsum hterm
      _ = (∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) * ENNReal.ofReal (1 / ‖f (x : ℂ)‖) :=
        ENNReal.tsum_mul_right
      _ = ENNReal.ofReal (2 / ‖f (x : ℂ)‖) := by
        have hsum : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
          summable_geometric_of_lt_one (by norm_num) (by norm_num)
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsum,
          tsum_geometric_of_lt_one (by norm_num) (by norm_num),
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
  -- Cayley pullback h(w) = f(i (1 - w) / (1 + w)) ∈ H^∞(U)
  let cayley : ℂ → ℂ := fun w => Complex.I * (1 - w) / (1 + w)
  let h : ℂ → ℂ := fun w => f (cayley w)
  have h1w_ne_of_ball : ∀ {w : ℂ}, w ∈ Metric.ball (0 : ℂ) 1 → 1 + w ≠ 0 := by
    intro w hw h0
    have hw_lt : ‖w‖ < 1 := by simpa [Metric.mem_ball] using hw
    have hw_eq : w = -1 := by linear_combination h0
    rw [hw_eq, norm_neg, norm_one] at hw_lt
    exact lt_irrefl 1 hw_lt
  have hcayley_im_pos : ∀ {w : ℂ}, w ∈ Metric.ball (0 : ℂ) 1 → 0 < (cayley w).im := by
    intro w hw
    have h1w_ne := h1w_ne_of_ball hw
    have hw_lt : ‖w‖ < 1 := by simpa [Metric.mem_ball] using hw
    have hw_sq : Complex.normSq w < 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg w]
    have hrew : cayley w =
        (Complex.I * (1 - w) * starRingEnd ℂ (1 + w)) / (Complex.normSq (1 + w) : ℂ) := by
      dsimp [cayley]
      have hconj_ne : starRingEnd ℂ (1 + w) ≠ 0 := by
        intro h0
        exact h1w_ne (by simpa using congr_arg (starRingEnd ℂ) h0)
      rw [← Complex.mul_conj (1 + w), mul_div_mul_right _ _ hconj_ne]
    rw [hrew, Complex.div_ofReal_im]
    have hnum_im : (Complex.I * (1 - w) * starRingEnd ℂ (1 + w)).im = 1 - Complex.normSq w := by
      simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
      ring
    rw [hnum_im]
    exact div_pos (by linarith) (Complex.normSq_pos.mpr h1w_ne)
  have hh_hol : RudinRCA.Chapter10.HolomorphicOn h (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    have hc_diff : DifferentiableAt ℂ cayley w :=
      ((differentiableAt_const Complex.I).mul
        ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)).div
        ((differentiableAt_const (1 : ℂ)).add differentiableAt_id)
        (h1w_ne_of_ball hw)
    exact (hf_entire (cayley w)).comp w hc_diff
  have hh_hardy : RudinRCA.Chapter17.IsInHardySpace ⊤ h := by
    rw [RudinRCA.Chapter17.isInHardySpace_top_iff]
    refine ⟨hh_hol, 1, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hf_le_one (hcayley_im_pos hw).le
  -- Nonzero witness w₀ = (i - z₀) / (i + z₀) ∈ ball 0 1
  let w₀ : ℂ := (Complex.I - z₀) / (Complex.I + z₀)
  have hIz₀_ne : Complex.I + z₀ ≠ 0 := by
    intro h0
    have him : (Complex.I + z₀).im = 1 + z₀.im := by simp
    rw [h0, Complex.zero_im] at him
    linarith
  have hw₀_ball : w₀ ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [w₀]
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hIz₀_ne)]
    have hsq_lt : ‖Complex.I - z₀‖ ^ 2 < ‖Complex.I + z₀‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.I_re, zero_sub, Complex.sub_im,
        Complex.I_im, Complex.add_re, zero_add, Complex.add_im]
      nlinarith
    nlinarith [norm_nonneg (Complex.I - z₀), norm_nonneg (Complex.I + z₀)]
  have hhw₀_ne : h w₀ ≠ 0 := by
    have hc_w₀ : cayley w₀ = z₀ := by
      dsimp [cayley, w₀]
      field_simp [hIz₀_ne, Complex.I_ne_zero]
      ring
    dsimp [h]
    rw [hc_w₀]
    exact hfz₀_ne
  -- Apply Chapter 17 Theorem 17.17 to h ∈ H^∞(U)
  obtain ⟨hlog_int, hpos_ae, _⟩ :=
    RudinRCA.Chapter17.theorem17_17 ENNReal.top_ne_zero hh_hardy ⟨w₀, hw₀_ball, hhw₀_ne⟩
  -- Identify radialBoundaryLimit h (θ : FourierCircle) = f(tan(θ/2)) on θ ∈ (0, π)
  have hrad_arc : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi,
      RudinRCA.Chapter17.radialBoundaryLimit h (θ : RudinRCA.Chapter04.FourierCircle) =
        f (Real.tan (θ / 2) : ℂ) := by
    intro θ hθ
    let α : ℝ := θ / 2
    have hα_pos : 0 < α := by dsimp [α]; linarith [hθ.1]
    have hα_lt : α < Real.pi / 2 := by dsimp [α]; linarith [hθ.2]
    have hcosα_pos : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα_lt⟩
    let ζ₀ : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
    have hθ_eq : θ = 2 * α := by dsimp [α]; ring
    have h1ζ₀_ne : 1 + ζ₀ ≠ 0 := by
      intro h0
      have hre : (1 + ζ₀).re = 2 * (Real.cos α) ^ 2 := by
        dsimp [ζ₀]
        rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
        rw [hθ_eq, Real.cos_two_mul]
        ring
      rw [h0, Complex.zero_re] at hre
      nlinarith
    have hcayley_ζ₀ : cayley ζ₀ = (Real.tan α : ℂ) := by
      dsimp [cayley]
      rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div,
        div_eq_div_iff h1ζ₀_ne (Complex.ofReal_ne_zero.mpr hcosα_pos.ne')]
      dsimp [ζ₀]
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        hθ_eq, Real.cos_two_mul, Real.sin_two_mul]
      push_cast
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
      have hs2 : (Real.sin α : ℂ) ^ 2 + (Real.cos α : ℂ) ^ 2 = 1 := by
        exact_mod_cast Real.sin_sq_add_cos_sq α
      linear_combination
        (-2 * (Real.cos α : ℂ) * Complex.I) * hs2 +
        (-2 * (Real.sin α : ℂ) * (Real.cos α : ℂ) ^ 2) * Complex.I_sq
    have hh_contAt : ContinuousAt h ζ₀ := by
      have hc_contAt : ContinuousAt cayley ζ₀ :=
        (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
          (continuousAt_const.add continuousAt_id) h1ζ₀_ne
      exact (hf_entire.continuous.continuousAt).comp hc_contAt
    have hrad_tend : Tendsto
        (fun r : ℝ => RudinRCA.Chapter17.radialSlice h r (θ : RudinRCA.Chapter04.FourierCircle))
        (𝓝[<] (1 : ℝ)) (𝓝 (h ζ₀)) := by
      have hr_tend : Tendsto (fun r : ℝ => (r : ℂ) * ζ₀) (𝓝[<] (1 : ℝ)) (𝓝 ζ₀) := by
        have h1 : Continuous (fun r : ℝ => (r : ℂ) * ζ₀) :=
          Complex.continuous_ofReal.mul continuous_const
        simpa using (h1.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
      have hslice_eq : (fun r : ℝ =>
          RudinRCA.Chapter17.radialSlice h r (θ : RudinRCA.Chapter04.FourierCircle)) =
          fun r : ℝ => h ((r : ℂ) * ζ₀) := by
        ext r
        simp [RudinRCA.Chapter17.radialSlice, RudinRCA.Chapter17.circlePoint_coe, ζ₀]
      rw [hslice_eq]
      exact hh_contAt.tendsto.comp hr_tend
    have hlim_eq : RudinRCA.Chapter17.radialBoundaryLimit h
        (θ : RudinRCA.Chapter04.FourierCircle) = h ζ₀ :=
      hrad_tend.limUnder_eq
    rw [hlim_eq]
    dsimp [h]
    rw [hcayley_ζ₀]
  -- Pull back boundary log-integrability via K : FourierCircle → ℝ≥0∞ (= ⊤ on the null zero set)
  let G : RudinRCA.Chapter04.FourierCircle → ℝ≥0∞ :=
    fun ζ => ENNReal.ofReal (max 0 (-Real.log ‖RudinRCA.Chapter17.radialBoundaryLimit h ζ‖))
  let K : RudinRCA.Chapter04.FourierCircle → ℝ≥0∞ :=
    fun ζ => if ‖RudinRCA.Chapter17.radialBoundaryLimit h ζ‖ = 0 then ⊤ else G ζ
  have hG_lt_top : (∫⁻ ζ, G ζ ∂RudinRCA.Chapter04.circleMeasure) < ⊤ := by
    have hle : ∀ ζ : RudinRCA.Chapter04.FourierCircle,
        G ζ ≤ ‖Real.log ‖RudinRCA.Chapter17.radialBoundaryLimit h ζ‖‖ₑ := by
      intro ζ
      dsimp [G]
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (max_le (abs_nonneg _) (neg_le_abs _))
    exact lt_of_le_of_lt (lintegral_mono hle) hlog_int.2
  have hK_lt_top : (∫⁻ ζ, K ζ ∂RudinRCA.Chapter04.circleMeasure) < ⊤ := by
    have hae_KG : K =ᵐ[RudinRCA.Chapter04.circleMeasure] G := by
      filter_upwards [hpos_ae] with ζ hζ
      dsimp [K]
      simp [hζ.ne']
    rwa [lintegral_congr_ae hae_KG]
  -- Pull back K from circleMeasure to Set.Ioo 0 π
  have hK_arc_lt_top :
      (∫⁻ θ in Set.Ioo (0 : ℝ) Real.pi, K (θ : RudinRCA.Chapter04.FourierCircle)) < ⊤ := by
    have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
    have hpre := AddCircle.lintegral_preimage (2 * Real.pi) 0 K
    rw [zero_add, AddCircle.volume_eq_smul_haarAddCircle, lintegral_smul_measure,
      smul_eq_mul] at hpre
    have hsub : Set.Ioo (0 : ℝ) Real.pi ⊆ Set.Ioc 0 (2 * Real.pi) :=
      fun θ hθ => ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    calc
      (∫⁻ θ in Set.Ioo (0 : ℝ) Real.pi, K (θ : RudinRCA.Chapter04.FourierCircle))
        ≤ ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), K (θ : RudinRCA.Chapter04.FourierCircle) :=
          lintegral_mono_set hsub
      _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ ζ, K ζ ∂RudinRCA.Chapter04.circleMeasure := hpre
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK_lt_top
  -- Substitute θ = 2 * arctan x for x ∈ Ioi 0
  let K_real : ℝ → ℝ≥0∞ := fun x =>
    if f (x : ℂ) = 0 then ⊤ else ENNReal.ofReal (max 0 (-Real.log ‖f (x : ℂ)‖))
  have hK_real_lt_top :
      (∫⁻ x in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (2 / (1 + x ^ 2)) * K_real x) < ⊤ := by
    let φ_θ : ℝ → ℝ := fun x => 2 * Real.arctan x
    have himg : φ_θ '' Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) Real.pi := by
      ext θ
      simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Ioo]
      constructor
      · rintro ⟨x, hx, rfl⟩
        dsimp [φ_θ]
        exact ⟨by linarith [Real.arctan_pos.mpr hx],
          by linarith [Real.arctan_lt_pi_div_two x]⟩
      · rintro ⟨hθ0, hθpi⟩
        have h1 : -(Real.pi / 2) < θ / 2 := by linarith [Real.pi_pos]
        have h2 : θ / 2 < Real.pi / 2 := by linarith
        refine ⟨Real.tan (θ / 2), Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) h2, ?_⟩
        dsimp [φ_θ]
        rw [Real.arctan_tan h1 h2]
        ring
    have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivWithinAt φ_θ (2 / (1 + x ^ 2)) (Set.Ioi (0 : ℝ)) x := by
      intro x _
      dsimp [φ_θ]
      refine ((Real.hasDerivAt_arctan x).const_mul 2).congr_deriv ?_ |>.hasDerivWithinAt
      ring
    have hmono : MonotoneOn φ_θ (Set.Ioi (0 : ℝ)) :=
      fun x _ y _ hxy => mul_le_mul_of_nonneg_left (Real.arctan_mono hxy) zero_le_two
    have hjac := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
      measurableSet_Ioi hderiv hmono
      (fun θ : ℝ => K (θ : RudinRCA.Chapter04.FourierCircle))
    rw [himg] at hjac
    have hcongr :
        (∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (2 / (1 + x ^ 2)) * K_real x) =
        ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (2 / (1 + x ^ 2)) *
            K ((φ_θ x : ℝ) : RudinRCA.Chapter04.FourierCircle) := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      congr 1
      have hθ_mem : φ_θ x ∈ Set.Ioo (0 : ℝ) Real.pi := by
        rw [← himg]; exact ⟨x, hx, rfl⟩
      have hrad_x := hrad_arc (φ_θ x) hθ_mem
      have htan : Real.tan (φ_θ x / 2) = x := by
        dsimp [φ_θ]
        rw [mul_div_cancel_left₀ _ two_ne_zero, Real.tan_arctan]
      rw [htan] at hrad_x
      dsimp [K_real, K, G]
      rw [hrad_x]
      simp only [norm_eq_zero]
    rw [hcongr, ← hjac]
    exact hK_arc_lt_top
  -- Scale x = 2 * B * u on u ∈ Ioi 0 and bound ennrealLog (dcQ M u) / (1 + u^2)
  have hK_scaled_lt_top :
      (∫⁻ u in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (2 * B) *
          (ENNReal.ofReal (2 / (1 + (2 * B * u) ^ 2)) * K_real (2 * B * u))) < ⊤ := by
    have h2B_pos : 0 < 2 * B := by positivity
    have himg : (fun u : ℝ => 2 * B * u) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
      ext x
      simp only [Set.mem_image, Set.mem_Ioi]
      constructor
      · rintro ⟨u, hu, rfl⟩; positivity
      · intro hx; exact ⟨x / (2 * B), div_pos hx h2B_pos, mul_div_cancel₀ x h2B_pos.ne'⟩
    have hderiv : ∀ u ∈ Set.Ioi (0 : ℝ),
        HasDerivWithinAt (fun s : ℝ => 2 * B * s) (2 * B) (Set.Ioi (0 : ℝ)) u := by
      intro u _
      simpa using ((hasDerivAt_id u).const_mul (2 * B)).hasDerivWithinAt
    have hmono : MonotoneOn (fun s : ℝ => 2 * B * s) (Set.Ioi (0 : ℝ)) :=
      fun u₁ _ u₂ _ hle => mul_le_mul_of_nonneg_left hle h2B_pos.le
    have hjac := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
      measurableSet_Ioi hderiv hmono
      (fun x : ℝ => ENNReal.ofReal (2 / (1 + x ^ 2)) * K_real x)
    rw [himg] at hjac
    rwa [← hjac]
  let C_B : ℝ := max 1 ((2 * B) ^ 2)
  have hC_B_pos : 0 < C_B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  -- Pointwise domination valid at ALL u > 0 (including where f(2 B u) = 0, since K_real = ⊤ there)
  have hpt_u : ∀ u ∈ Set.Ioi (0 : ℝ),
      ennrealLog (dcQ M u) / ENNReal.ofReal (1 + u ^ 2) ≤
        ENNReal.ofReal (Real.log 2) * ENNReal.ofReal (1 / (1 + u ^ 2)) +
        ENNReal.ofReal (C_B / (4 * B)) *
          (ENNReal.ofReal (2 * B) *
            (ENNReal.ofReal (2 / (1 + (2 * B * u) ^ 2)) * K_real (2 * B * u))) := by
    intro u hu
    have hu_pos : 0 < u := hu
    have h1u_pos : 0 < 1 + u ^ 2 := by positivity
    have hlog_le : ennrealLog (dcQ M u) ≤
        ENNReal.ofReal (Real.log 2) + K_real (2 * B * u) := by
      dsimp [K_real]
      split_ifs with hfx0
      · simp
      · have hfx_pos : 0 < ‖f ((2 * B * u : ℝ) : ℂ)‖ := norm_pos_iff.mpr hfx0
        have hfx_le1 : ‖f ((2 * B * u : ℝ) : ℂ)‖ ≤ 1 := hf_le_one (by simp)
        have hneg_log_nn : 0 ≤ -Real.log ‖f ((2 * B * u : ℝ) : ℂ)‖ := by
          linarith [Real.log_nonpos hfx_pos.le hfx_le1]
        rw [max_eq_right hneg_log_nn]
        calc
          ennrealLog (dcQ M u)
            ≤ ennrealLog (ENNReal.ofReal (2 / ‖f ((2 * B * u : ℝ) : ℂ)‖)) :=
              ennrealLog_mono (hdcQ_le_f hu_pos hfx0)
          _ = ENNReal.ofReal (Real.log (2 / ‖f ((2 * B * u : ℝ) : ℂ)‖)) :=
              ennrealLog_ofReal (div_pos zero_lt_two hfx_pos)
          _ = ENNReal.ofReal (Real.log 2 + (-Real.log ‖f ((2 * B * u : ℝ) : ℂ)‖)) := by
              rw [Real.log_div two_ne_zero hfx_pos.ne', sub_eq_add_neg]
          _ = ENNReal.ofReal (Real.log 2) +
                ENNReal.ofReal (-Real.log ‖f ((2 * B * u : ℝ) : ℂ)‖) :=
              ENNReal.ofReal_add (Real.log_nonneg one_le_two) hneg_log_nn
    have hden_le : 1 + (2 * B * u) ^ 2 ≤ C_B * (1 + u ^ 2) := by
      have h1 : 1 ≤ C_B := le_max_left _ _
      have h2 : (2 * B) ^ 2 ≤ C_B := le_max_right _ _
      have h3 : (2 * B * u) ^ 2 = (2 * B) ^ 2 * u ^ 2 := by ring
      rw [h3]
      nlinarith [sq_nonneg u]
    have hcoeff_le : ENNReal.ofReal (1 / (1 + u ^ 2)) ≤
        ENNReal.ofReal (C_B / (4 * B)) *
          (ENNReal.ofReal (2 * B) * ENNReal.ofReal (2 / (1 + (2 * B * u) ^ 2))) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hden2_pos : 0 < 1 + (2 * B * u) ^ 2 := by positivity
      have hrhs_eq : (C_B / (4 * B)) * ((2 * B) * (2 / (1 + (2 * B * u) ^ 2))) =
          C_B / (1 + (2 * B * u) ^ 2) := by
        field_simp [hB_pos.ne', hden2_pos.ne']
        ring
      rw [hrhs_eq, div_le_div_iff₀ h1u_pos hden2_pos, one_mul]
      exact hden_le
    calc
      ennrealLog (dcQ M u) / ENNReal.ofReal (1 + u ^ 2)
        ≤ (ENNReal.ofReal (Real.log 2) + K_real (2 * B * u)) / ENNReal.ofReal (1 + u ^ 2) :=
          ENNReal.div_le_div_right hlog_le _
      _ = ENNReal.ofReal (Real.log 2) / ENNReal.ofReal (1 + u ^ 2) +
            K_real (2 * B * u) / ENNReal.ofReal (1 + u ^ 2) := ENNReal.add_div
      _ ≤ ENNReal.ofReal (Real.log 2) * ENNReal.ofReal (1 / (1 + u ^ 2)) +
            ENNReal.ofReal (C_B / (4 * B)) *
              (ENNReal.ofReal (2 * B) *
                (ENNReal.ofReal (2 / (1 + (2 * B * u) ^ 2)) * K_real (2 * B * u))) := by
          refine add_le_add ?_ ?_
          · rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos h1u_pos, one_div]
          · rw [div_eq_mul_inv, mul_comm _ (ENNReal.ofReal (1 + u ^ 2))⁻¹,
              ← ENNReal.ofReal_inv_of_pos h1u_pos, ← one_div]
            simpa only [mul_assoc] using
              mul_le_mul_of_nonneg_right hcoeff_le zero_le
  have hterm1_lt :
      (∫⁻ u in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (Real.log 2) * ENNReal.ofReal (1 / (1 + u ^ 2))) < ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top lintegral_inv_one_add_sq_lt_top
  have hterm2_lt :
      (∫⁻ u in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (C_B / (4 * B)) *
          (ENNReal.ofReal (2 * B) *
            (ENNReal.ofReal (2 / (1 + (2 * B * u) ^ 2)) * K_real (2 * B * u)))) < ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK_scaled_lt_top
  have hmeas1 : Measurable (fun u : ℝ =>
      ENNReal.ofReal (Real.log 2) * ENNReal.ofReal (1 / (1 + u ^ 2))) := by
    fun_prop
  calc
    (∫⁻ u in Set.Ioi (0 : ℝ), ennrealLog (dcQ M u) / ENNReal.ofReal (1 + u ^ 2))
      ≤ ∫⁻ u in Set.Ioi (0 : ℝ),
          (ENNReal.ofReal (Real.log 2) * ENNReal.ofReal (1 / (1 + u ^ 2)) +
            ENNReal.ofReal (C_B / (4 * B)) *
              (ENNReal.ofReal (2 * B) *
                (ENNReal.ofReal (2 / (1 + (2 * B * u) ^ 2)) * K_real (2 * B * u)))) :=
        setLIntegral_mono' measurableSet_Ioi hpt_u
    _ = (∫⁻ u in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.log 2) * ENNReal.ofReal (1 / (1 + u ^ 2))) +
        (∫⁻ u in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (C_B / (4 * B)) *
            (ENNReal.ofReal (2 * B) *
              (ENNReal.ofReal (2 / (1 + (2 * B * u) ^ 2)) * K_real (2 * B * u)))) :=
        lintegral_add_left hmeas1 _
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hterm1_lt, hterm2_lt⟩

end Node19_11_Helpers

/-- **Hazard 19.11 Measurability Semantics (`SCOPING-H-19-20.md` §hazard 4):**
`ennrealLog`, `dcQ M`, and `dcq M` are Borel-measurable in `ℝ≥0∞`. -/
theorem measurable_ennrealLog : Measurable ennrealLog := by
  unfold ennrealLog
  exact Measurable.ite (measurableSet_singleton ⊤) measurable_const (by fun_prop)

theorem measurable_dcQ (M : ℕ → ℝ) : Measurable (dcQ M) := by
  have heq : dcQ M = fun x : ℝ =>
      ⨆ N : ℕ, ∑ n ∈ Finset.range N, ENNReal.ofReal (x ^ n / M n) := by
    ext x
    exact ENNReal.tsum_eq_iSup_nat
  rw [heq]
  exact Measurable.isLUB
    (fun N => Finset.measurable_sum (Finset.range N) fun n _ => by fun_prop)
    (fun _ => isLUB_iSup)

theorem measurable_dcq (M : ℕ → ℝ) : Measurable (dcq M) :=
  Measurable.isLUB (fun _ => by fun_prop) (fun _ => isLUB_iSup)

/-- **Node 19.11 (`IsPosNormLogConvex` for `M_n = n!`, RCA p. 380):**
The factorial sequence `M_n = n!` is positive, normalized (`0! = 1`), and log-convex. -/
theorem isPosNormLogConvex_factorial :
    IsPosNormLogConvex (fun n : ℕ => (n.factorial : ℝ)) := by
  refine ⟨fun n => Nat.cast_pos.mpr (Nat.factorial_pos n), by simp, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  simp only [Nat.add_sub_cancel]
  have h1 : ((k + 1).factorial : ℝ) = ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
  have h2 : ((k + 1 + 1).factorial : ℝ) =
      ((k + 2 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ)) := by
    rw [show k + 1 + 1 = (k + 1) + 1 from rfl, Nat.factorial_succ, Nat.cast_mul, h1]
  rw [h1, h2]
  have hle : ((k + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ (k + 1)
  calc
    (((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ)) ^ 2
      = ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) ^ 2 := by ring
    _ ≤ ((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hle (by positivity))
          (sq_nonneg _)
    _ = (k.factorial : ℝ) * (((k + 2 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ))) := by
        ring

/-- **Theorem 19.11 (The Denjoy–Carleman Theorem, RCA pp. 380–383):**
Let `M : ℕ → ℝ` satisfy the standing hypotheses (`0 < M_n`, `M_0 = 1`, `M_n^2 ≤ M_{n-1} M_{n+1}`).
With extended-value `Q = dcQ M` and `q = dcq M` in `ℝ≥0∞` (`SCOPING-H-19-20.md` §hazard 4),
the following five conditions are equivalent:
- **(a)** `C{M_n}` is **not** quasi-analytic (`¬ IsQuasiAnalytic M`);
- **(b)** `∫_0^∞ log Q(x) / (1 + x^2) dx < ∞`;
- **(c)** `∫_0^∞ log q(x) / (1 + x^2) dx < ∞`;
- **(d)** `∑_{n=1}^∞ M_n^{-1/n} < ∞`;
- **(e)** `∑_{n=1}^∞ M_{n-1} / M_n < ∞`.

Moreover, `(d)` and `(e)` coincide with real `Summable` of their positive series, and if
`Q(x_0) = ∞` for some `x_0 > 0` (the divergent-`Q` case highlighted on p. 380), then the integral
in `(b)` is `∞` and `C{M_n}` is quasi-analytic. -/
theorem theorem19_11 {M : ℕ → ℝ} (hM : IsPosNormLogConvex M) :
    List.TFAE [
      ¬ IsQuasiAnalytic M,
      (∫⁻ x in Set.Ioi (0 : ℝ), ennrealLog (dcQ M x) / ENNReal.ofReal (1 + x ^ 2)) < ⊤,
      (∫⁻ x in Set.Ioi (0 : ℝ), ennrealLog (dcq M x) / ENNReal.ofReal (1 + x ^ 2)) < ⊤,
      (∑' n : ℕ, ENNReal.ofReal ((M (n + 1)) ^ (-(1 / ((n + 1 : ℕ) : ℝ))))) < ⊤,
      (∑' n : ℕ, ENNReal.ofReal (M n / M (n + 1))) < ⊤
    ] ∧
    ((∑' n : ℕ, ENNReal.ofReal ((M (n + 1)) ^ (-(1 / ((n + 1 : ℕ) : ℝ))))) < ⊤ ↔
      Summable (fun n : ℕ => (M (n + 1)) ^ (-(1 / ((n + 1 : ℕ) : ℝ))))) ∧
    ((∑' n : ℕ, ENNReal.ofReal (M n / M (n + 1))) < ⊤ ↔
      Summable (fun n : ℕ => M n / M (n + 1))) ∧
    ((∃ x₀ : ℝ, 0 < x₀ ∧ dcQ M x₀ = ⊤) →
      (∫⁻ x in Set.Ioi (0 : ℝ), ennrealLog (dcQ M x) / ENNReal.ofReal (1 + x ^ 2)) = ⊤ ∧
      IsQuasiAnalytic M) := by
  have hab : ¬ IsQuasiAnalytic M →
      (∫⁻ x in Set.Ioi (0 : ℝ), ennrealLog (dcQ M x) / ENNReal.ofReal (1 + x ^ 2)) < ⊤ :=
    dc_a_imp_b hM
  have hbc := dc_b_iff_c hM
  have hce := dc_c_iff_e hM
  have hde := dc_d_iff_e hM
  have hea : (∑' n : ℕ, ENNReal.ofReal (M n / M (n + 1))) < ⊤ → ¬ IsQuasiAnalytic M :=
    dc_e_imp_a hM
  have ha_iff_b : ¬ IsQuasiAnalytic M ↔
      (∫⁻ x in Set.Ioi (0 : ℝ), ennrealLog (dcQ M x) / ENNReal.ofReal (1 + x ^ 2)) < ⊤ :=
    ⟨hab, fun hb => hea (hce.mp (hbc.mp hb))⟩
  have htfae : List.TFAE [
      ¬ IsQuasiAnalytic M,
      (∫⁻ x in Set.Ioi (0 : ℝ), ennrealLog (dcQ M x) / ENNReal.ofReal (1 + x ^ 2)) < ⊤,
      (∫⁻ x in Set.Ioi (0 : ℝ), ennrealLog (dcq M x) / ENNReal.ofReal (1 + x ^ 2)) < ⊤,
      (∑' n : ℕ, ENNReal.ofReal ((M (n + 1)) ^ (-(1 / ((n + 1 : ℕ) : ℝ))))) < ⊤,
      (∑' n : ℕ, ENNReal.ofReal (M n / M (n + 1))) < ⊤] := by
    intro p hp q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl | rfl | rfl <;>
      tauto
  refine ⟨htfae, ?_, ?_, ?_⟩
  · exact tsum_ofReal_lt_top_iff_summable (fun n => (Real.rpow_pos_of_pos (hM.1 (n + 1)) _).le)
  · exact tsum_ofReal_lt_top_iff_summable (fun n => (div_pos (hM.1 n) (hM.1 (n + 1))).le)
  · rintro ⟨x₀, hx₀_pos, hx₀_top⟩
    have htop_int :
        (∫⁻ x in Set.Ioi (0 : ℝ), ennrealLog (dcQ M x) / ENNReal.ofReal (1 + x ^ 2)) = ⊤ := by
      have hsub : Set.Ioo x₀ (x₀ + 1) ⊆ Set.Ioi (0 : ℝ) :=
        fun x hx => lt_trans hx₀_pos hx.1
      have hpt_top : ∀ x ∈ Set.Ioo x₀ (x₀ + 1),
          (⊤ : ℝ≥0∞) ≤ ennrealLog (dcQ M x) / ENNReal.ofReal (1 + x ^ 2) := by
        intro x hx
        have hdcQ_mono : dcQ M x₀ ≤ dcQ M x := by
          unfold dcQ
          refine ENNReal.tsum_le_tsum fun n => ENNReal.ofReal_le_ofReal ?_
          exact div_le_div_of_nonneg_right
            (pow_le_pow_left₀ hx₀_pos.le hx.1.le n) (hM.1 n).le
        have hx_top : dcQ M x = ⊤ := top_unique (hx₀_top ▸ hdcQ_mono)
        have hden_ne_top : ENNReal.ofReal (1 + x ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
        rw [hx_top, show ennrealLog ⊤ = ⊤ from rfl, div_eq_mul_inv,
          ENNReal.top_mul (ENNReal.inv_ne_zero.mpr hden_ne_top)]
      have hge : (⊤ : ℝ≥0∞) ≤
          ∫⁻ x in Set.Ioi (0 : ℝ), ennrealLog (dcQ M x) / ENNReal.ofReal (1 + x ^ 2) := by
        calc
          (⊤ : ℝ≥0∞) = (⊤ : ℝ≥0∞) * volume (Set.Ioo x₀ (x₀ + 1)) := by
            rw [Real.volume_Ioo, add_sub_cancel_left, ENNReal.ofReal_one, mul_one]
          _ = ∫⁻ _ in Set.Ioo x₀ (x₀ + 1), (⊤ : ℝ≥0∞) := (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ x in Set.Ioo x₀ (x₀ + 1),
                ennrealLog (dcQ M x) / ENNReal.ofReal (1 + x ^ 2) :=
            setLIntegral_mono' measurableSet_Ioo hpt_top
          _ ≤ ∫⁻ x in Set.Ioi (0 : ℝ),
                ennrealLog (dcQ M x) / ENNReal.ofReal (1 + x ^ 2) :=
            lintegral_mono_set hsub
      exact top_unique hge
    refine ⟨htop_int, ?_⟩
    by_contra hnot
    have hlt := hab hnot
    rw [htop_int] at hlt
    exact lt_irrefl ⊤ hlt

/-- **Node 19.11 Consequence (`theorem19_11_factorial_quasiAnalytic`, RCA p. 380):**
Denjoy–Carleman immediately recovers quasi-analyticity of `C{n!}` since
`∑_{n=0}^∞ n! / (n + 1)! = ∑_{n=0}^∞ 1 / (n + 1) = ∞`. -/
theorem theorem19_11_factorial_quasiAnalytic :
    IsQuasiAnalytic (fun n : ℕ => (n.factorial : ℝ)) := by
  obtain ⟨htfae, _, hsum_iff, _⟩ := theorem19_11 isPosNormLogConvex_factorial
  have hnot_sum : ¬ Summable (fun n : ℕ => (n.factorial : ℝ) / ((n + 1).factorial : ℝ)) := by
    have hcongr : (fun n : ℕ => (n.factorial : ℝ) / ((n + 1).factorial : ℝ)) =
        fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) := by
      ext n
      rw [Nat.factorial_succ, Nat.cast_mul]
      have hnf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      field_simp [hnf]
    rw [hcongr]
    intro hsum
    exact Real.not_summable_one_div_natCast
      ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp hsum)
  have ha_iff_e := htfae.out 1 5
  by_contra hnot_QA
  exact hnot_sum (hsum_iff.mp (ha_iff_e.mp hnot_QA))

end RudinRCA.Chapter19

end

#print axioms RudinRCA.Chapter19.ch19Fourier_plancherel_L1_L2
#print axioms RudinRCA.Chapter19.ch19InvFourier_plancherel_L1_L2
#print axioms RudinRCA.Chapter19.ch19_fourier_inversion_pointwise
#print axioms RudinRCA.Chapter19.ch19InvFourierL2_inversion_ae
#print axioms RudinRCA.Chapter19.differentiableOn_holomorphicFourierHalfLine
#print axioms RudinRCA.Chapter19.holomorphicFourierHalfLine_plancherel
#print axioms RudinRCA.Chapter19.holomorphicFourierInterval_endpoint_eq
#print axioms RudinRCA.Chapter19.holomorphicFourierInterval_properties
#print axioms RudinRCA.Chapter19.theorem19_1
#print axioms RudinRCA.Chapter19.theorem19_2
#print axioms RudinRCA.Chapter19.theorem19_2_iSup
#print axioms RudinRCA.Chapter19.theorem19_3
#print axioms RudinRCA.Chapter19.theorem19_4
#print axioms RudinRCA.Chapter19.theorem19_5
#print axioms RudinRCA.Chapter19.CMSubmodule
#print axioms RudinRCA.Chapter19.mem_CM_iff_limsup
#print axioms RudinRCA.Chapter19.node19_6_affine_witness_counterexample
#print axioms RudinRCA.Chapter19.CM_comp_affine_bounds
#print axioms RudinRCA.Chapter19.CM_comp_affine
#print axioms RudinRCA.Chapter19.CM_div_zero
#print axioms RudinRCA.Chapter19.node19_6_regularization_counterexample
#print axioms RudinRCA.Chapter19.node19_6_regularization_necessary_exp_lower_bound
#print axioms RudinRCA.Chapter19.theorem19_6
#print axioms RudinRCA.Chapter19.CM_mul_explicit_bound
#print axioms RudinRCA.Chapter19.CMSubalgebra
#print axioms RudinRCA.Chapter19.theorem19_7
#print axioms RudinRCA.Chapter19.theorem19_8
#print axioms RudinRCA.Chapter19.theorem19_9
#print axioms RudinRCA.Chapter19.theorem19_10
#print axioms RudinRCA.Chapter19.measurable_ennrealLog
#print axioms RudinRCA.Chapter19.measurable_dcQ
#print axioms RudinRCA.Chapter19.measurable_dcq
#print axioms RudinRCA.Chapter19.isPosNormLogConvex_factorial
#print axioms RudinRCA.Chapter19.theorem19_11
#print axioms RudinRCA.Chapter19.theorem19_11_factorial_quasiAnalytic
