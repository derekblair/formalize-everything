import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic.Ring

/-!
Rudin 15.17–15.18. The angular integrals below are Lebesgue interval integrals.
The explicit integrability conclusions account for logarithmic singularities at
zeros on the circle; changing the value at those finitely many points does not
change these integrals.
-/

namespace RudinRCA.Chapter15.JensenWork

open MeasureTheory Metric Real Set

/-- Rudin 15.17, with integrability at the endpoint singularities included. -/
theorem log_one_sub_exp_circle_integral :
    IntervalIntegrable (fun θ : ℝ ↦ Real.log ‖1 - Complex.exp ((θ : ℂ) * Complex.I)‖)
        volume 0 (2 * Real.pi) ∧
      (2 * Real.pi)⁻¹ *
        (∫ θ : ℝ in 0..2 * Real.pi,
          Real.log ‖1 - Complex.exp ((θ : ℂ) * Complex.I)‖) = 0 := by
  constructor
  · simpa [CircleIntegrable, circleMap, norm_sub_rev] using
      (circleIntegrable_log_norm_sub_const (a := (1 : ℂ)) (c := 0) 1)
  · simpa [circleAverage, circleMap, smul_eq_mul, norm_sub_rev] using
      (circleAverage_log_norm_sub_const₁ (a := (1 : ℂ)) (by simp))

/-- Write the circle average with Rudin's interval of angles `[-π, π]`. -/
theorem circleAverage_eq_angular_integral (g : ℂ → ℝ) (r : ℝ) :
    circleAverage g 0 r = (2 * Real.pi)⁻¹ *
      (∫ θ : ℝ in -Real.pi..Real.pi, g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := by
  have hp : Function.Periodic (fun θ ↦ g (circleMap 0 r θ)) (2 * Real.pi) :=
    fun θ ↦ by rw [periodic_circleMap 0 r θ]
  have hi := hp.intervalIntegral_add_eq 0 (-Real.pi)
  have hend : -Real.pi + 2 * Real.pi = Real.pi := by ring
  simp only [zero_add, hend] at hi
  rw [circleAverage, hi]
  simp only [smul_eq_mul, circleMap_zero]

/-- Number of appearances of `z` in a finite indexed list, including repetitions. -/
noncomputable def zeroMultiplicity {N : ℕ} (a : Fin N → ℂ) (z : ℂ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i ↦ a i = z).card

/-- A finite list of all zeros in the closed disc, with each zero repeated exactly
as often as its analytic order. In particular, zeros on the boundary are included. -/
structure EnumeratesClosedDiscZeros {N : ℕ} (f : ℂ → ℂ) (r : ℝ) (a : Fin N → ℂ) : Prop where
  location : ∀ i, ‖a i‖ ≤ r
  zero : ∀ i, f (a i) = 0
  multiplicity : ∀ z, ‖z‖ ≤ r → analyticOrderAt f z = (zeroMultiplicity a z : ℕ∞)

theorem finsum_zeroMultiplicity {N : ℕ} (a : Fin N → ℂ) (w : ℂ → ℝ) :
    (∑ᶠ z, (zeroMultiplicity a z : ℝ) * w z) = ∑ i, w (a i) := by
  classical
  have hfib (z : ℂ) :
      (∑ i ∈ Finset.univ.filter (fun i ↦ a i = z), w (a i)) =
        (zeroMultiplicity a z : ℝ) * w z := by
    calc
      (∑ i ∈ Finset.univ.filter (fun i ↦ a i = z), w (a i)) =
          ∑ i ∈ Finset.univ.filter (fun i ↦ a i = z), w z := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _ = _ := by simp [zeroMultiplicity, nsmul_eq_mul]
  simpa only [hfib] using
    (finsum_sum_filter a Finset.univ (fun i ↦ w (a i)))

theorem EnumeratesClosedDiscZeros.divisor_eq {N : ℕ} {f : ℂ → ℂ} {r : ℝ}
    {a : Fin N → ℂ} (ha : EnumeratesClosedDiscZeros f r a)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (z : ℂ) :
    MeromorphicOn.divisor f (closedBall 0 r) z = (zeroMultiplicity a z : ℤ) := by
  classical
  by_cases hz : z ∈ closedBall (0 : ℂ) r
  · simp [hf.divisor_apply hz, ha.multiplicity z (by simpa using hz)]
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]
    have hc : zeroMultiplicity a z = 0 := by
      unfold zeroMultiplicity
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi hai
      apply hz
      simpa [← hai] using ha.location i
    simp [hc]

theorem jensen_angular_log_integrable {R r : ℝ} {f : ℂ → ℂ}
    (hr : 0 < r) (hrR : r < R) (hf : DifferentiableOn ℂ f (ball 0 R)) :
    IntervalIntegrable (fun θ : ℝ ↦
      Real.log ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)
      volume (-Real.pi) Real.pi := by
  have hA : AnalyticOnNhd ℂ f (closedBall 0 |r|) := by
    apply (hf.analyticOnNhd isOpen_ball).mono
    simpa [abs_of_pos hr] using closedBall_subset_ball hrR
  have hc : CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 r :=
    (hA.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hp : Function.Periodic (fun θ ↦ Real.log ‖f (circleMap 0 r θ)‖) (2 * Real.pi) :=
    fun θ ↦ by rw [periodic_circleMap 0 r θ]
  simpa only [circleMap_zero] using
    hp.intervalIntegrable₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero) hc (-Real.pi) Real.pi

/-- Rudin 15.18 in its printed product form, for the closed-disc list of zeros and
the angular interval `[-π,π]`. Boundary zeros contribute the factor `r / r = 1`. -/
theorem jensen_formula {N : ℕ} {R r : ℝ} {f : ℂ → ℂ} (a : Fin N → ℂ)
    (hr : 0 < r) (hrR : r < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf0 : f 0 ≠ 0) (ha : EnumeratesClosedDiscZeros f r a) :
    IntervalIntegrable (fun θ : ℝ ↦
      Real.log ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)
      volume (-Real.pi) Real.pi ∧
    ‖f 0‖ * (∏ i, r / ‖a i‖) = Real.exp ((2 * Real.pi)⁻¹ *
      (∫ θ : ℝ in -Real.pi..Real.pi,
        Real.log ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)) := by
  refine ⟨jensen_angular_log_integrable hr hrR hf, ?_⟩
  have hA : AnalyticOnNhd ℂ f (closedBall 0 r) :=
    (hf.analyticOnNhd isOpen_ball).mono (closedBall_subset_ball hrR)
  have hA' : AnalyticOnNhd ℂ f (closedBall 0 |r|) := by
    simpa only [abs_of_pos hr] using hA
  have hne (i : Fin N) : a i ≠ 0 := by
    intro hi
    exact hf0 (by simpa [hi] using ha.zero i)
  have hj := hA'.circleAverage_log_norm hr.ne' hf0
  simp only [abs_of_pos hr, ha.divisor_eq hA, Int.cast_natCast, zero_sub, norm_neg,
    ← div_eq_mul_inv] at hj
  rw [finsum_zeroMultiplicity] at hj
  have hexp (i : Fin N) : Real.exp (Real.log (r / ‖a i‖)) = r / ‖a i‖ :=
    Real.exp_log (div_pos hr (norm_pos_iff.mpr (hne i)))
  have he := congrArg Real.exp hj
  rw [Real.exp_add, Real.exp_sum, Real.exp_log (norm_pos_iff.mpr hf0)] at he
  simp only [hexp] at he
  calc
    ‖f 0‖ * (∏ i, r / ‖a i‖) = Real.exp (circleAverage (fun z ↦ Real.log ‖f z‖) 0 r) := by
      simpa only [mul_comm] using he.symm
    _ = _ := by rw [circleAverage_eq_angular_integral]

#print axioms log_one_sub_exp_circle_integral
#print axioms circleAverage_eq_angular_integral
#print axioms finsum_zeroMultiplicity
#print axioms EnumeratesClosedDiscZeros.divisor_eq
#print axioms jensen_angular_log_integrable
#print axioms jensen_formula

end RudinRCA.Chapter15.JensenWork
