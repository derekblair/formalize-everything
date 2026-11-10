import BlaschkeWork
import LogMeansWork
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section
open Filter Set
open scoped Topology

namespace RudinRCA.Chapter15

/-- The scalar logarithms of the Blaschke radii are absolutely summable. -/
theorem summable_log_blaschke_radii {a : ℕ → ℂ}
    (hsum : Summable (fun n ↦ 1 - ‖a n‖)) :
    Summable (fun n ↦ Real.log ‖a n‖) := by
  have h := Real.summable_log_one_add_of_summable hsum.neg
  convert h using 1
  funext n
  congr 1
  ring

/-- The summable domination used at the end of the proof of 15.24. -/
theorem norm_log_max_radius_le {t r : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hr : r ≤ 1) : ‖Real.log (max r t)‖ ≤ ‖Real.log t‖ := by
  have hpos : 0 < max r t := ht.trans_le (le_max_right _ _)
  have hmax : max r t ≤ 1 := max_le hr ht1
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonpos (Real.log_nonpos hpos.le hmax),
    abs_of_nonpos (Real.log_nonpos ht.le ht1)]
  exact neg_le_neg (Real.log_le_log ht (le_max_right _ _))

/-- The numerical logarithmic-mean expression for a Blaschke product tends to
zero at the boundary. Its identification with the analytic circle mean is a
separate Jensen/product step. -/
theorem blaschke_log_radius_sum_tendsto_zero {a : ℕ → ℂ}
    (ha0 : ∀ n, a n ≠ 0) (ha : ∀ n, ‖a n‖ < 1)
    (hsum : Summable (fun n ↦ 1 - ‖a n‖)) (k : ℕ) :
    Tendsto (fun r : ℝ ↦ (k : ℝ) * Real.log r +
      ∑' n, Real.log (max r ‖a n‖)) (𝓝[<] 1) (𝓝 0) := by
  have hlogs := summable_log_blaschke_radii hsum
  have ht : Tendsto (fun r : ℝ ↦ ∑' n, Real.log (max r ‖a n‖))
      (𝓝[<] 1) (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
    apply tendsto_tsum_of_dominated_convergence hlogs.norm
    · intro n
      have hm : Tendsto (fun r : ℝ ↦ max r ‖a n‖) (𝓝[<] 1) (𝓝 1) := by
        simpa only [max_eq_left (ha n).le] using
          (tendsto_id'.mono_left nhdsWithin_le_nhds).max tendsto_const_nhds
      simpa only [Real.log_one] using (Real.continuousAt_log one_ne_zero).tendsto.comp hm
    · filter_upwards [self_mem_nhdsWithin] with r hr n
      exact norm_log_max_radius_le (norm_pos_iff.mpr (ha0 n)) (ha n).le hr.le
  have hk : Tendsto (fun r : ℝ ↦ (k : ℝ) * Real.log r) (𝓝[<] 1) (𝓝 0) := by
    simpa only [Real.log_one, mul_zero] using
      ((Real.continuousAt_log one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds).const_mul (k : ℝ)
  simpa only [tsum_zero, add_zero] using hk.add ht

/-- Every individual factor is unimodular on the unit circle. -/
theorem norm_blaschkeFactor_on_sphere {a z : ℂ}
    (ha0 : a ≠ 0) (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    ‖blaschkeFactor a z‖ = 1 := by
  have hden := blaschke_denominator_ne_zero ha hz.le
  have hsq := blaschke_norm_difference a z
  rw [hz] at hsq
  have hnorm : ‖a - z‖ = ‖1 - star a * z‖ := by
    nlinarith [norm_nonneg (a - z), norm_nonneg (1 - star a * z)]
  rw [blaschkeFactor, norm_div, norm_mul, norm_blaschke_phase ha0, one_mul,
    hnorm, div_self (norm_ne_zero_iff.mpr hden)]

/-- The finite and empty cases of the boundary-modulus statement in 15.24. -/
theorem norm_finiteBlaschkeProduct_on_sphere {ι : Type*} (k : ℕ)
    (s : Finset ι) (a : ι → ℂ) (ha0 : ∀ n ∈ s, a n ≠ 0)
    (ha : ∀ n ∈ s, ‖a n‖ < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖finiteBlaschkeProduct k s a z‖ = 1 := by
  rw [finiteBlaschkeProduct, norm_mul, norm_pow, hz, one_pow, one_mul, norm_prod]
  exact Finset.prod_eq_one (fun n hn ↦ norm_blaschkeFactor_on_sphere (ha0 n hn) (ha n hn) hz)

#print axioms summable_log_blaschke_radii
#print axioms norm_log_max_radius_le
#print axioms blaschke_log_radius_sum_tendsto_zero
#print axioms norm_blaschkeFactor_on_sphere
#print axioms norm_finiteBlaschkeProduct_on_sphere

end RudinRCA.Chapter15
