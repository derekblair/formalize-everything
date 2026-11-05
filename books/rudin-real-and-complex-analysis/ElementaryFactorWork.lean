import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Scratch development of Rudin's exact elementary-factor estimate (15.8).
Definitions are duplicated here to permit independent compilation before integration.
-/

namespace RudinRCA.Chapter15.ElementaryFactorWork

noncomputable def elementaryExponent (p : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1 : ℂ)

noncomputable def elementaryFactor (p : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp (elementaryExponent p z)

noncomputable def realElementaryExponent (p : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range p, t ^ (k + 1) / (k + 1 : ℝ)

noncomputable def realElementaryFactor (p : ℕ) (t : ℝ) : ℝ :=
  (1 - t) * Real.exp (realElementaryExponent p t)

theorem hasDerivAt_elementaryExponent (p : ℕ) (z : ℂ) :
    HasDerivAt (elementaryExponent p) (∑ k ∈ Finset.range p, z ^ k) z := by
  apply HasDerivAt.fun_sum
  intro k hk
  have hk0 : (k + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero k
  simpa [Nat.cast_add, Nat.cast_one, mul_div_cancel_left₀ _ hk0] using
    (hasDerivAt_pow (k + 1) z).div_const (k + 1 : ℂ)

theorem hasDerivAt_realElementaryExponent (p : ℕ) (t : ℝ) :
    HasDerivAt (realElementaryExponent p) (∑ k ∈ Finset.range p, t ^ k) t := by
  apply HasDerivAt.fun_sum
  intro k hk
  have hk0 : (k + 1 : ℝ) ≠ 0 := Nat.cast_add_one_ne_zero k
  simpa [Nat.cast_add, Nat.cast_one, mul_div_cancel_left₀ _ hk0] using
    (hasDerivAt_pow (k + 1) t).div_const (k + 1 : ℝ)

theorem hasDerivAt_elementaryFactor (p : ℕ) (z : ℂ) :
    HasDerivAt (elementaryFactor p)
      (-(z ^ p * Complex.exp (elementaryExponent p z))) z := by
  change HasDerivAt (fun w ↦ (1 - w) * Complex.exp (elementaryExponent p w)) _ z
  refine (((hasDerivAt_id z).const_sub 1).mul
    (hasDerivAt_elementaryExponent p z).cexp).congr_deriv ?_
  calc
    -1 * Complex.exp (elementaryExponent p z) + (1 - z) *
        (Complex.exp (elementaryExponent p z) * (∑ k ∈ Finset.range p, z ^ k)) =
        ((1 - z) * (∑ k ∈ Finset.range p, z ^ k) - 1) *
          Complex.exp (elementaryExponent p z) := by ring
    _ = _ := by rw [mul_neg_geom_sum]; ring

theorem hasDerivAt_realElementaryFactor (p : ℕ) (t : ℝ) :
    HasDerivAt (realElementaryFactor p)
      (-(t ^ p * Real.exp (realElementaryExponent p t))) t := by
  change HasDerivAt (fun x ↦ (1 - x) * Real.exp (realElementaryExponent p x)) _ t
  refine (((hasDerivAt_id t).const_sub 1).mul
    (hasDerivAt_realElementaryExponent p t).exp).congr_deriv ?_
  calc
    -1 * Real.exp (realElementaryExponent p t) + (1 - t) *
        (Real.exp (realElementaryExponent p t) * (∑ k ∈ Finset.range p, t ^ k)) =
        ((1 - t) * (∑ k ∈ Finset.range p, t ^ k) - 1) *
          Real.exp (realElementaryExponent p t) := by ring
    _ = _ := by rw [mul_neg_geom_sum]; ring

theorem elementary_weight_integral (p : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..1, t ^ p * Real.exp (realElementaryExponent p t)) = 1 := by
  have hcont : Continuous (fun t : ℝ ↦ t ^ p * Real.exp (realElementaryExponent p t)) := by
    unfold realElementaryExponent
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f := fun t ↦ 1 - realElementaryFactor p t)
    (f' := fun t ↦ t ^ p * Real.exp (realElementaryExponent p t))
    (fun t _ ↦ by simpa using (hasDerivAt_realElementaryFactor p t).const_sub 1)
    (hcont.intervalIntegrable _ _)
  simpa [realElementaryFactor, realElementaryExponent] using h

theorem norm_elementaryExponent_line_le (p : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖elementaryExponent p ((t : ℂ) * z)‖ ≤ realElementaryExponent p t := by
  unfold elementaryExponent realElementaryExponent
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)
  simp only [norm_div, Complex.norm_pow, Complex.norm_mul, Complex.norm_of_nonneg ht,
    ← Nat.cast_add_one, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀ (mul_nonneg ht (norm_nonneg z))
  simpa using mul_le_mul_of_nonneg_left hz ht

theorem hasDerivAt_elementaryFactor_line (p : ℕ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ elementaryFactor p ((x : ℂ) * z))
      (-( ((t : ℂ) * z) ^ p * Complex.exp (elementaryExponent p ((t : ℂ) * z))) * z) t := by
  simpa only [Function.comp_apply, id_eq, one_mul] using!
    ((hasDerivAt_elementaryFactor p ((t : ℂ) * z)).comp (t : ℂ)
      ((hasDerivAt_id (t : ℂ)).mul_const z)).comp_ofReal

theorem norm_elementaryFactor_line_deriv_le (p : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖deriv (fun x : ℝ ↦ elementaryFactor p ((x : ℂ) * z)) t‖ ≤
      ‖z‖ ^ (p + 1) * (t ^ p * Real.exp (realElementaryExponent p t)) := by
  rw [(hasDerivAt_elementaryFactor_line p z t).deriv]
  simp only [Complex.norm_mul, norm_neg, Complex.norm_pow, Complex.norm_of_nonneg ht]
  have he : ‖Complex.exp (elementaryExponent p ((t : ℂ) * z))‖ ≤
      Real.exp (realElementaryExponent p t) :=
    (Complex.norm_exp_le_exp_norm _).trans
      (Real.exp_le_exp.mpr (norm_elementaryExponent_line_le p z hz t ht))
  calc
    (t * ‖z‖) ^ p * ‖Complex.exp (elementaryExponent p ((t : ℂ) * z))‖ * ‖z‖ ≤
        (t * ‖z‖) ^ p * Real.exp (realElementaryExponent p t) * ‖z‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left he (pow_nonneg (mul_nonneg ht (norm_nonneg z)) p))
        (norm_nonneg z)
    _ = ‖z‖ ^ (p + 1) * (t ^ p * Real.exp (realElementaryExponent p t)) := by
      rw [mul_pow, pow_succ]
      ring

/-- Rudin 15.8, including the boundary `‖z‖ = 1` and the case `p = 0`. -/
theorem norm_one_sub_elementaryFactor_le (p : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖1 - elementaryFactor p z‖ ≤ ‖z‖ ^ (p + 1) := by
  have hc : Continuous (fun t : ℝ ↦ elementaryFactor p ((t : ℂ) * z)) :=
    continuous_iff_continuousAt.mpr (fun t ↦ (hasDerivAt_elementaryFactor_line p z t).continuousAt)
  have hd : DifferentiableOn ℝ (fun t : ℝ ↦ elementaryFactor p ((t : ℂ) * z))
      (Set.Ioo 0 1) :=
    fun t _ ↦ (hasDerivAt_elementaryFactor_line p z t).differentiableAt.differentiableWithinAt
  have hBc : Continuous (fun t : ℝ ↦ ‖z‖ ^ (p + 1) *
      (t ^ p * Real.exp (realElementaryExponent p t))) := by
    unfold realElementaryExponent
    fun_prop
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le
    (a := (0 : ℝ)) (b := 1) (by norm_num) hc.continuousOn hd
    (Filter.Eventually.of_forall (fun t ht ↦
      norm_elementaryFactor_line_deriv_le p z hz t ht.1.le)) (hBc.intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, elementary_weight_integral, mul_one] at h
  have hzero : elementaryFactor p 0 = 1 := by
    simp [elementaryFactor, elementaryExponent]
  simpa only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, hzero,
    norm_sub_rev] using h

#print axioms hasDerivAt_elementaryExponent
#print axioms hasDerivAt_realElementaryExponent
#print axioms hasDerivAt_elementaryFactor
#print axioms hasDerivAt_realElementaryFactor
#print axioms elementary_weight_integral
#print axioms norm_elementaryExponent_line_le
#print axioms hasDerivAt_elementaryFactor_line
#print axioms norm_elementaryFactor_line_deriv_le
#print axioms norm_one_sub_elementaryFactor_le

end RudinRCA.Chapter15.ElementaryFactorWork
