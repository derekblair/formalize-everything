import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Real Complex Set MeasureTheory
open scoped BigOperators

namespace RCA63

lemma integral_pos_cos :
    (∫ t in (-(Real.pi / 2))..(Real.pi + Real.pi / 2), max (Real.cos t) 0) = 2 := by
  have hc : Continuous (fun t : ℝ => max (Real.cos t) 0) :=
    Real.continuous_cos.max continuous_const
  have h₁ : (∫ t in (-(Real.pi / 2))..(Real.pi / 2), max (Real.cos t) 0) = 2 := by
    calc
      _ = ∫ t in (-(Real.pi / 2))..(Real.pi / 2), Real.cos t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
        exact max_eq_left (Real.cos_nonneg_of_mem_Icc ht)
      _ = 2 := by rw [integral_cos]; simp only [Real.sin_pi_div_two, Real.sin_neg]; norm_num
  have h₂ : (∫ t in (Real.pi / 2)..(Real.pi + Real.pi / 2), max (Real.cos t) 0) = 0 := by
    calc
      _ = ∫ t in (Real.pi / 2)..(Real.pi + Real.pi / 2), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
        exact max_eq_right (Real.cos_nonpos_of_pi_div_two_le_of_le ht.1 ht.2)
      _ = 0 := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := Real.pi / 2) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), h₁, h₂, add_zero]

lemma integral_pos_cos_shift (a : ℝ) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), max (Real.cos (t - a)) 0) = 2 := by
  have hp : Function.Periodic (fun t : ℝ => max (Real.cos t) 0) (2 * Real.pi) :=
    fun t => by
      change max (Real.cos (t + 2 * Real.pi)) 0 = max (Real.cos t) 0
      rw [Real.cos_add_two_pi]
  calc
    _ = ∫ t in (-a)..(-a + 2 * Real.pi), max (Real.cos t) 0 := by
      simpa only [zero_sub, sub_eq_add_neg, add_comm, add_zero] using
        intervalIntegral.integral_comp_sub_right
          (fun t : ℝ => max (Real.cos t) 0) (a := 0) (b := 2 * Real.pi) a
    _ = ∫ t in (-(Real.pi / 2))..(-(Real.pi / 2) + 2 * Real.pi),
        max (Real.cos t) 0 := hp.intervalIntegral_add_eq (-a) (-(Real.pi / 2))
    _ = ∫ t in (-(Real.pi / 2))..(Real.pi + Real.pi / 2), max (Real.cos t) 0 := by
      congr 1 <;> ring
    _ = 2 := integral_pos_cos

lemma projection_arg (z : ℂ) (t : ℝ) :
    (Complex.exp (-(t : ℂ) * Complex.I) * z).re =
      ‖z‖ * Real.cos (t - Complex.arg z) := by
  calc
    _ = Real.cos t * z.re + Real.sin t * z.im := by
      rw [Complex.mul_re, Complex.exp_re, Complex.exp_im]
      simp [Complex.mul_im, Complex.mul_re]
    _ = Real.cos t * (‖z‖ * Real.cos (Complex.arg z)) +
        Real.sin t * (‖z‖ * Real.sin (Complex.arg z)) := by
      rw [Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]
    _ = ‖z‖ * Real.cos (t - Complex.arg z) := by
      rw [Real.cos_sub]
      ring

lemma integral_pos_projection (z : ℂ) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      max (Complex.exp (-(t : ℂ) * Complex.I) * z).re 0) = 2 * ‖z‖ := by
  simp_rw [projection_arg]
  have heq : (fun t : ℝ => max (‖z‖ * Real.cos (t - Complex.arg z)) 0) =
      (fun t : ℝ => ‖z‖ * max (Real.cos (t - Complex.arg z)) 0) := by
    funext t
    rw [mul_max_of_nonneg _ _ (norm_nonneg z), mul_zero]
  rw [heq, intervalIntegral.integral_const_mul, integral_pos_cos_shift]
  ring

lemma projection_continuous (z : ℂ) :
    Continuous (fun t : ℝ => max (Complex.exp (-(t : ℂ) * Complex.I) * z).re 0) := by
  simp_rw [projection_arg]
  fun_prop

theorem exists_subset_sum_norm {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ∃ S ⊆ s, (∑ i ∈ s, ‖z i‖) / Real.pi ≤ ‖∑ i ∈ S, z i‖ := by
  classical
  obtain ⟨S, hS, hmax⟩ := s.powerset.exists_max_image
    (fun S : Finset ι => ‖∑ i ∈ S, z i‖) ⟨∅, by simp⟩
  refine ⟨S, Finset.mem_powerset.mp hS, ?_⟩
  have hbound (t : ℝ) :
      (∑ i ∈ s, max (Complex.exp (-(t : ℂ) * Complex.I) * z i).re 0) ≤
        ‖∑ i ∈ S, z i‖ := by
    let u : ℂ := Complex.exp (-(t : ℂ) * Complex.I)
    let T := s.filter (fun i => 0 ≤ (u * z i).re)
    have hT : T ⊆ s := Finset.filter_subset _ _
    have heq : (∑ i ∈ s, max (u * z i).re 0) = (u * ∑ i ∈ T, z i).re := by
      simp only [Finset.mul_sum, Complex.re_sum, T, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs with h
      · exact max_eq_left h
      · simpa only [mul_zero, Complex.zero_re] using max_eq_right (le_of_not_ge h)
    calc
      _ = (u * ∑ i ∈ T, z i).re := heq
      _ ≤ ‖u * ∑ i ∈ T, z i‖ := Complex.re_le_norm _
      _ = ‖∑ i ∈ T, z i‖ := by simp [u, Complex.norm_exp]
      _ ≤ ‖∑ i ∈ S, z i‖ := hmax T (Finset.mem_powerset.mpr hT)
  have hcont : Continuous (fun t : ℝ =>
      ∑ i ∈ s, max (Complex.exp (-(t : ℂ) * Complex.I) * z i).re 0) :=
    continuous_finsetSum _ fun i hi => projection_continuous (z i)
  have hint := intervalIntegral.integral_mono (μ := volume) (a := 0) (b := 2 * Real.pi)
    (by positivity) (hcont.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _) hbound
  rw [intervalIntegral.integral_finsetSum
    (fun i hi => (projection_continuous (z i)).intervalIntegrable _ _)] at hint
  simp_rw [integral_pos_projection] at hint
  rw [← Finset.mul_sum] at hint
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hint
  apply (div_le_iff₀ Real.pi_pos).mpr
  nlinarith

#print axioms exists_subset_sum_norm
end RCA63
