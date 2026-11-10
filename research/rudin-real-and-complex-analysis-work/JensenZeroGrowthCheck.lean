import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith


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


namespace RudinRCA.Chapter15.ZeroGrowthWork

open Filter Metric Set
open scoped Topology

/-- The maximum modulus on the circle of radius `r`. -/
noncomputable def maximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z ↦ ‖f z‖) '' sphere 0 r)

/-- Closed-disc zero count, with multiplicity. Entire functions have nonnegative
divisors, so `toNat` here only changes the representation of their sum. -/
noncomputable def entireZeroCount (f : ℂ → ℂ) (r : ℝ) : ℕ :=
  Int.toNat (∑ᶠ z, MeromorphicOn.divisor f (closedBall 0 r) z)

theorem norm_le_maximumModulus {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} {z : ℂ}
    (hz : z ∈ sphere 0 r) : ‖f z‖ ≤ maximumModulus f r := by
  exact le_csSup ((isCompact_sphere (0 : ℂ) r).image hf.norm).bddAbove ⟨z, hz, rfl⟩

theorem one_le_maximumModulus {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 = 1)
    {r : ℝ} (hr : 0 < r) : 1 ≤ maximumModulus f r := by
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le
    (f := f) (U := ball (0 : ℂ) r) isBounded_ball
    ⟨hf.differentiableOn, hf.continuous.continuousOn⟩
    (fun z hz ↦ norm_le_maximumModulus hf.continuous (frontier_ball_subset_sphere hz))
    (subset_closure (mem_ball_self hr))
  simpa [hf0] using h

theorem entireZeroCount_intCast {f : ℂ → ℂ} (hf : Differentiable ℂ f) (r : ℝ) :
    (entireZeroCount f r : ℤ) = ∑ᶠ z, MeromorphicOn.divisor f (closedBall 0 r) z := by
  have hA : AnalyticOnNhd ℂ f (closedBall 0 r) := fun z _ ↦ hf.analyticAt z
  exact Int.toNat_of_nonneg (finsum_nonneg (fun z ↦ hA.divisor_nonneg z))

/-- Rudin 15.20(2), using the actual circle maximum and the closed-disc zero count. -/
theorem zero_count_log_two_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 = 1)
    {r : ℝ} (hr : 0 < r) :
    (entireZeroCount f r : ℝ) * Real.log 2 ≤ Real.log (maximumModulus f (2 * r)) := by
  have h2r : 0 < 2 * r := mul_pos (by norm_num) hr
  have hA : AnalyticOnNhd ℂ f (closedBall 0 |2 * r|) := fun z _ ↦ hf.analyticAt z
  have hb : ∀ z ∈ sphere (0 : ℂ) |2 * r|, ‖f z‖ ≤ maximumModulus f (2 * r) := by
    intro z hz
    apply norm_le_maximumModulus hf.continuous
    simpa only [abs_of_pos h2r] using hz
  have hj := hA.sum_divisor_le (r := r) (R := 2 * r)
    (by simpa [abs_of_pos hr] using hr)
    (by simp only [abs_of_pos hr, abs_of_pos h2r]; linarith)
    (one_le_maximumModulus hf hf0 h2r) (by simp [hf0]) hb
  have hc : (entireZeroCount f r : ℝ) =
      ((∑ᶠ z, MeromorphicOn.divisor f (closedBall 0 r) z : ℤ) : ℝ) := by
    simpa only [Int.cast_natCast] using congrArg (fun n : ℤ ↦ (n : ℝ)) (entireZeroCount_intCast hf r)
  have hratio : (2 * r) / r = 2 := by field_simp [hr.ne']
  simp only [abs_of_pos hr, hf0, norm_one, div_one, hratio] at hj
  rw [← hc] at hj
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp hj

/-- A general logarithmic growth bound for natural-valued counts. The library's
`log 0 = 0` convention gives zero for an identically zero count; the corresponding
extended-real logarithm is `-∞` and also satisfies the asserted upper bound. -/
theorem limsup_log_count_le_of_polynomial_bound (n : ℝ → ℕ) {C k : ℝ}
    (hC : 1 ≤ C) (hk : 0 ≤ k)
    (hn : ∀ᶠ r in atTop, (n r : ℝ) ≤ C * r ^ k) :
    Filter.limsup (fun r : ℝ ↦ Real.log (n r) / Real.log r) atTop ≤ k := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hu : ∀ᶠ r in atTop,
      Real.log (n r) / Real.log r ≤ Real.log C / Real.log r + k := by
    filter_upwards [hn, eventually_gt_atTop (1 : ℝ)] with r hnr hr
    have hrpos : 0 < r := zero_lt_one.trans hr
    have hlr : 0 < Real.log r := Real.log_pos hr
    by_cases hn0 : n r = 0
    · simp only [hn0, Nat.cast_zero, Real.log_zero, zero_div]
      exact add_nonneg (div_nonneg (Real.log_nonneg hC) hlr.le) hk
    · have hnpos : (0 : ℝ) < n r := by exact_mod_cast Nat.pos_of_ne_zero hn0
      calc
        Real.log (n r) / Real.log r ≤ Real.log (C * r ^ k) / Real.log r :=
          div_le_div_of_nonneg_right (Real.log_le_log hnpos hnr) hlr.le
        _ = Real.log C / Real.log r + k := by
          rw [Real.log_mul hCpos.ne' (Real.rpow_pos_of_pos hrpos k).ne',
            Real.log_rpow hrpos, add_div, mul_div_cancel_right₀ _ hlr.ne']
  have hlow : ∀ᶠ r in atTop, 0 ≤ Real.log (n r) / Real.log r := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    exact div_nonneg (Real.log_natCast_nonneg _) (Real.log_pos hr).le
  have hco := isCoboundedUnder_le_of_eventually_le atTop hlow
  have ht : Tendsto (fun r : ℝ ↦ Real.log C / Real.log r + k) atTop (𝓝 k) := by
    have ht0 : Tendsto (fun r : ℝ ↦ Real.log C / Real.log r) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    simpa using ht0.add_const k
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  apply Filter.limsup_le_of_le hco
  filter_upwards [hu, ht.eventually_lt_const hb] with r hur hr
  exact hur.trans hr.le

/-- Rudin 15.20(3)–(4): an eventual exponential bound for the maximum modulus
controls the upper logarithmic growth rate of the zero count. -/
theorem zero_count_growth_limsup {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 = 1)
    {A k : ℝ} (hA : 0 < A) (hk : 0 < k)
    (hgrowth : ∀ᶠ r in atTop, maximumModulus f r ≤ Real.exp (A * r ^ k)) :
    Filter.limsup (fun r : ℝ ↦ Real.log (entireZeroCount f r) / Real.log r) atTop ≤ k := by
  let C : ℝ := A * (2 : ℝ) ^ k / Real.log 2
  apply limsup_log_count_le_of_polynomial_bound (C := max 1 C) (le_max_left _ _) hk.le
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.mp hgrowth
  filter_upwards [eventually_ge_atTop (max 1 r₀)] with r hr
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hrpos : 0 < r := zero_lt_one.trans_le hr1
  have h2r : 0 < 2 * r := mul_pos (by norm_num) hrpos
  have h₂ : maximumModulus f (2 * r) ≤ Real.exp (A * (2 * r) ^ k) :=
    hr₀ (2 * r) (by have := (le_max_right 1 r₀).trans hr; linarith)
  have hlog : Real.log (maximumModulus f (2 * r)) ≤ A * (2 * r) ^ k := by
    simpa only [Real.log_exp] using Real.log_le_log
      (zero_lt_one.trans_le (one_le_maximumModulus hf hf0 h2r)) h₂
  have hn := (zero_count_log_two_le hf hf0 hrpos).trans hlog
  have hln2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (entireZeroCount f r : ℝ) ≤ A * (2 * r) ^ k / Real.log 2 := (le_div_iff₀ hln2).mpr hn
    _ = C * r ^ k := by rw [Real.mul_rpow (by norm_num) hrpos.le]; dsimp [C]; ring
    _ ≤ max 1 C * r ^ k :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hrpos.le k)

/-- Remove the order-`k` origin zero of `1 - exp(z^k)` and normalize to value one. -/
noncomputable def normalizedSharpnessExample (k : ℕ) (z : ℂ) : ℂ :=
  dslope Complex.exp 0 (z ^ k)

theorem normalizedSharpnessExample_entire (k : ℕ) :
    Differentiable ℂ (normalizedSharpnessExample k) := by
  have hd : Differentiable ℂ (dslope Complex.exp 0) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (by simp)).mpr Complex.differentiable_exp.differentiableOn
  exact hd.comp (differentiable_id.pow k)

theorem normalizedSharpnessExample_at_zero {k : ℕ} (hk : 0 < k) :
    normalizedSharpnessExample k 0 = 1 := by
  simp [normalizedSharpnessExample, zero_pow hk.ne', Complex.deriv_exp]

theorem sharpnessExample_origin_factor {k : ℕ} (hk : 0 < k) (z : ℂ) :
    1 - Complex.exp (z ^ k) = -(z ^ k) * normalizedSharpnessExample k z := by
  by_cases hz : z = 0
  · simp [hz, zero_pow hk.ne']
  · rw [normalizedSharpnessExample, dslope_of_ne _ (pow_ne_zero _ hz)]
    simp only [slope, sub_zero, Complex.exp_zero, smul_eq_mul]
    field_simp [pow_ne_zero k hz] <;> ring

/-- The unnormalized printed sharpness example has an origin zero of exactly
order `k`; the normalized example removes precisely this zero. -/
theorem sharpnessExample_origin_order {k : ℕ} (hk : 0 < k) :
    analyticOrderAt (fun z : ℂ ↦ 1 - Complex.exp (z ^ k)) 0 = (k : ℕ∞) := by
  have hg := (normalizedSharpnessExample_entire k).analyticAt 0
  have hgz : analyticOrderAt (normalizedSharpnessExample k) 0 = 0 :=
    hg.analyticOrderAt_eq_zero.mpr (by rw [normalizedSharpnessExample_at_zero hk]; norm_num)
  have heq : (fun z : ℂ ↦ 1 - Complex.exp (z ^ k)) =
      (-((id : ℂ → ℂ) ^ k)) * normalizedSharpnessExample k := by
    funext z
    exact sharpnessExample_origin_factor hk z
  rw [heq, analyticOrderAt_mul (by fun_prop) hg]
  simp [analyticOrderAt_neg, analyticOrderAt_pow (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) 0),
    hgz]

/-- Each zero of a nonzero entire function contributes at least one to its divisor. -/
theorem one_le_divisor_of_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    {r : ℝ} {z : ℂ} (hz : z ∈ closedBall 0 r) (hfz : f z = 0) :
    (1 : ℤ) ≤ MeromorphicOn.divisor f (closedBall 0 r) z := by
  have hA : AnalyticOnNhd ℂ f Set.univ := fun w _ ↦ hf.analyticAt w
  have hfin : analyticOrderAt f z ≠ ⊤ :=
    hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 0) (mem_univ z)
      (by rw [(hf.analyticAt 0).analyticOrderAt_eq_zero.mpr hf0]; simp)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  have hmpos : 0 < m := by
    have hne := (hf.analyticAt z).analyticOrderAt_ne_zero.mpr hfz
    rw [← hm] at hne
    exact Nat.pos_of_ne_zero (by simpa using hne)
  have hAr : AnalyticOnNhd ℂ f (closedBall 0 r) := fun w _ ↦ hf.analyticAt w
  rw [hAr.divisor_apply hz, ← hm]
  simpa using (show (1 : ℤ) ≤ m by exact_mod_cast hmpos)

/-- Any finite collection of distinct zeros gives a lower bound for the count. -/
theorem finite_distinct_zeros_le_count {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) {r : ℝ} {N : ℕ} (a : Fin N → ℂ) (ha : Function.Injective a)
    (har : ∀ i, a i ∈ closedBall 0 r) (haz : ∀ i, f (a i) = 0) :
    N ≤ entireZeroCount f r := by
  classical
  let d := MeromorphicOn.divisor f (closedBall 0 r)
  have hA : AnalyticOnNhd ℂ f (closedBall 0 r) := fun w _ ↦ hf.analyticAt w
  have hd : d.support.Finite := d.finiteSupport (isCompact_closedBall 0 r)
  let s : Finset ℂ := Finset.univ.image a
  have hs : s ⊆ hd.toFinset := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    apply hd.mem_toFinset.mpr
    exact ne_of_gt ((by norm_num : (0 : ℤ) < 1).trans_le
      (one_le_divisor_of_zero hf hf0 (har i) (haz i)))
  have hn : (N : ℤ) ≤ ∑ᶠ z, d z := by
    rw [finsum_eq_finsetSum_of_support_subset d (s := hd.toFinset)
      (by simp only [Set.Finite.coe_toFinset]; exact subset_rfl)]
    calc
      (N : ℤ) = ∑ i : Fin N, (1 : ℤ) := by simp
      _ ≤ ∑ i : Fin N, d (a i) := Finset.sum_le_sum fun i _ ↦
        one_le_divisor_of_zero hf hf0 (har i) (haz i)
      _ = ∑ z ∈ s, d z := (Finset.sum_image (fun i _ j _ h ↦ ha h)).symm
      _ ≤ ∑ z ∈ hd.toFinset, d z :=
        Finset.sum_le_sum_of_subset_of_nonneg hs (fun z _ _ ↦ hA.divisor_nonneg z)
  rw [← entireZeroCount_intCast hf r] at hn
  exact_mod_cast hn

/-- Select one zero for every positive integer exponential period. -/
theorem exists_sharpness_zero_sequence {k : ℕ} (hk : 0 < k) :
    ∃ a : ℕ → ℂ, Function.Injective a ∧
      (∀ n, normalizedSharpnessExample k (a n) = 0) ∧
      (∀ n, ‖a n‖ ^ k = 2 * Real.pi * (n + 1 : ℕ)) := by
  classical
  letI : NeZero k := ⟨hk.ne'⟩
  have hex : ∀ n : ℕ, ∃ z : ℂ, z ^ k = (n + 1 : ℕ) * (2 * Real.pi * Complex.I) :=
    fun n ↦ (Complex.isOpenQuotientMap_pow k).surjective _
  choose a ha using hex
  have hperiod : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  refine ⟨a, ?_, ?_, ?_⟩
  · intro m n h
    have hp : ((m + 1 : ℕ) : ℂ) = (n + 1 : ℕ) :=
      mul_right_cancel₀ hperiod (by rw [← ha m, ← ha n, h])
    exact Nat.add_right_cancel (by exact_mod_cast hp)
  · intro n
    have hne : a n ^ k ≠ 0 := by
      rw [ha n]
      exact mul_ne_zero (by exact_mod_cast Nat.add_one_ne_zero n) hperiod
    rw [normalizedSharpnessExample, dslope_of_ne _ hne]
    simp [slope, ha n, Complex.exp_nat_mul_two_pi_mul_I]
  · intro n
    have h := congrArg norm (ha n)
    simpa only [norm_pow, norm_mul, Complex.norm_natCast, Complex.norm_I, mul_one,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      mul_comm] using h

/-- A quantitative lower count sufficient for sharpness, retaining the origin normalization. -/
theorem sharpness_zero_count_floor_le {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 ≤ r) :
    ⌊r ^ k / (2 * Real.pi)⌋₊ ≤ entireZeroCount (normalizedSharpnessExample k) r := by
  obtain ⟨a, ha, haz, hanorm⟩ := exists_sharpness_zero_sequence hk
  let N := ⌊r ^ k / (2 * Real.pi)⌋₊
  apply finite_distinct_zeros_le_count (normalizedSharpnessExample_entire k)
    (by rw [normalizedSharpnessExample_at_zero hk]; norm_num)
    (fun i : Fin N ↦ a i) (ha.comp Fin.val_injective) _ (fun i ↦ haz i)
  intro i
  simp only [mem_closedBall, dist_zero_right]
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) hr hk.ne').mp
  rw [hanorm]
  have hi : ((i.val + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast i.isLt
  have hN : (N : ℝ) ≤ r ^ k / (2 * Real.pi) :=
    Nat.floor_le (div_nonneg (pow_nonneg hr _) (by positivity))
  have h := (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mp (hi.trans hN)
  simpa only [mul_comm] using h

theorem norm_normalizedSharpnessExample_le (k : ℕ) (z : ℂ) :
    ‖normalizedSharpnessExample k z‖ ≤ Real.exp (‖z‖ ^ k) := by
  by_cases hz : z ^ k = 0
  · simp only [normalizedSharpnessExample, hz, dslope_same, Complex.deriv_exp,
      Complex.exp_zero, norm_one]
    exact Real.one_le_exp (pow_nonneg (norm_nonneg _) _)
  · have h : ‖Complex.exp (z ^ k) - 1‖ ≤ ‖z ^ k‖ * Real.exp ‖z ^ k‖ := by
      simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp (z ^ k) 1
    rw [normalizedSharpnessExample, dslope_of_ne _ hz]
    simp only [slope, sub_zero, Complex.exp_zero, smul_eq_mul, norm_mul, norm_inv]
    calc
      ‖z ^ k‖⁻¹ * ‖Complex.exp (z ^ k) - 1‖ ≤
          ‖z ^ k‖⁻¹ * (‖z ^ k‖ * Real.exp ‖z ^ k‖) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (norm_nonneg _))
      _ = Real.exp (‖z‖ ^ k) := by rw [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz), one_mul, norm_pow]

theorem maximumModulus_normalizedSharpnessExample_le (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    maximumModulus (normalizedSharpnessExample k) r ≤ Real.exp (r ^ k) := by
  apply csSup_le
  · refine ⟨‖normalizedSharpnessExample k (r : ℂ)‖, (r : ℂ), ?_, rfl⟩
    simp [mem_sphere, dist_zero_right, abs_of_nonneg hr]
  · rintro x ⟨z, hz, rfl⟩
    have hnorm : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    simpa only [hnorm] using norm_normalizedSharpnessExample_le k z

/-- The unnormalized printed example obeys the required exponential growth bound. -/
theorem maximumModulus_sharpnessExample_le {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 ≤ r) :
    maximumModulus (fun z : ℂ ↦ 1 - Complex.exp (z ^ k)) r ≤ Real.exp (2 * r ^ k) := by
  apply csSup_le
  · refine ⟨‖1 - Complex.exp ((r : ℂ) ^ k)‖, (r : ℂ), ?_, rfl⟩
    simp [mem_sphere, dist_zero_right, abs_of_nonneg hr]
  · rintro x ⟨z, hz, rfl⟩
    have hnorm : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    rw [sharpnessExample_origin_factor hk, norm_mul, norm_neg, norm_pow, hnorm]
    have hg := norm_normalizedSharpnessExample_le k z
    rw [hnorm] at hg
    calc
      r ^ k * ‖normalizedSharpnessExample k z‖ ≤ r ^ k * Real.exp (r ^ k) :=
        mul_le_mul_of_nonneg_left hg (pow_nonneg hr _)
      _ ≤ Real.exp (r ^ k) * Real.exp (r ^ k) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (r ^ k)]) (Real.exp_pos _).le
      _ = Real.exp (2 * r ^ k) := by rw [← Real.exp_add]; congr 1; ring

/-- Polynomial upper and lower bounds give the exact logarithmic growth exponent. -/
theorem tendsto_log_count_of_polynomial_bounds (n : ℝ → ℕ) (k : ℕ) {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ᶠ r in atTop, c * r ^ k ≤ n r ∧ (n r : ℝ) ≤ C * r ^ k) :
    Tendsto (fun r : ℝ ↦ Real.log (n r) / Real.log r) atTop (𝓝 (k : ℝ)) := by
  have hlim (b : ℝ) : Tendsto (fun r : ℝ ↦ Real.log b / Real.log r + k)
      atTop (𝓝 (k : ℝ)) := by
    have hzero : Tendsto (fun r : ℝ ↦ Real.log b / Real.log r) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    simpa using hzero.add_const (k : ℝ)
  have heq (b : ℝ) (hb : 0 < b) {r : ℝ} (hr : 1 < r) :
      Real.log (b * r ^ k) / Real.log r = Real.log b / Real.log r + k := by
    rw [Real.log_mul hb.ne' (pow_pos (zero_lt_one.trans hr) k).ne', Real.log_pow,
      add_div, mul_div_cancel_right₀ _ (Real.log_pos hr).ne']
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim c) (hlim C)
  · filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with r hrb hr
    rw [← heq c hc hr]
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (mul_pos hc (pow_pos (zero_lt_one.trans hr) k)) hrb.1)
      (Real.log_pos hr).le
  · filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with r hrb hr
    rw [← heq C hC hr]
    exact div_le_div_of_nonneg_right
      (Real.log_le_log ((mul_pos hc (pow_pos (zero_lt_one.trans hr) k)).trans_le hrb.1) hrb.2)
      (Real.log_pos hr).le

/-- Matching polynomial bounds for the normalized example's zero count. -/
theorem normalizedSharpnessExample_polynomial_zero_bounds {k : ℕ} (hk : 0 < k) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ r in atTop,
      c * r ^ k ≤ entireZeroCount (normalizedSharpnessExample k) r ∧
      (entireZeroCount (normalizedSharpnessExample k) r : ℝ) ≤ C * r ^ k := by
  let c : ℝ := 1 / (4 * Real.pi)
  let C : ℝ := (2 : ℝ) ^ k / Real.log 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 < C := div_pos (pow_pos (by norm_num) _) (Real.log_pos (by norm_num))
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (4 * Real.pi))] with r hr
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hrpos : 0 < r := zero_lt_one.trans_le hr1
  have hrpow : 4 * Real.pi ≤ r ^ k :=
    ((le_max_right _ _).trans hr).trans (le_self_pow₀ hr1 hk.ne')
  constructor
  · have hf := Nat.lt_floor_add_one (r ^ k / (2 * Real.pi))
    have hl := sharpness_zero_count_floor_le hk hrpos.le
    have hl' : (⌊r ^ k / (2 * Real.pi)⌋₊ : ℝ) ≤
        entireZeroCount (normalizedSharpnessExample k) r := by exact_mod_cast hl
    have hunit : 1 ≤ r ^ k / (4 * Real.pi) :=
      (le_div_iff₀ (by positivity : 0 < 4 * Real.pi)).mpr (by simpa using hrpow)
    have heq : r ^ k / (2 * Real.pi) = 2 * (r ^ k / (4 * Real.pi)) := by
      field_simp
      <;> ring
    rw [heq] at hf
    dsimp [c]
    rw [one_div_mul_eq_div]
    linarith
  · have hbound := zero_count_log_two_le (normalizedSharpnessExample_entire k)
      (normalizedSharpnessExample_at_zero hk) hrpos
    have hm := maximumModulus_normalizedSharpnessExample_le k (mul_nonneg (by norm_num) hrpos.le)
    have hMpos := zero_lt_one.trans_le (one_le_maximumModulus
      (normalizedSharpnessExample_entire k) (normalizedSharpnessExample_at_zero hk)
      (mul_pos (by norm_num) hrpos))
    have hlog := Real.log_le_log hMpos hm
    rw [Real.log_exp, mul_pow] at hlog
    have h := (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr (hbound.trans hlog)
    simpa only [C, div_mul_eq_mul_div] using h

/-- The normalized printed example attains the exponent in 15.20. -/
theorem normalizedSharpnessExample_zero_count_limit {k : ℕ} (hk : 0 < k) :
    Tendsto (fun r : ℝ ↦ Real.log (entireZeroCount (normalizedSharpnessExample k) r) /
      Real.log r) atTop (𝓝 (k : ℝ)) := by
  obtain ⟨c, C, hc, hC, hb⟩ := normalizedSharpnessExample_polynomial_zero_bounds hk
  exact tendsto_log_count_of_polynomial_bounds _ k hc hC hb

/-- Normalization removes exactly the `k` zeros at the origin from every closed disc. -/
theorem sharpnessExample_zero_count_eq {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 ≤ r) :
    entireZeroCount (fun z : ℂ ↦ 1 - Complex.exp (z ^ k)) r =
      k + entireZeroCount (normalizedSharpnessExample k) r := by
  classical
  let f : ℂ → ℂ := fun z ↦ 1 - Complex.exp (z ^ k)
  let g := normalizedSharpnessExample k
  have hf : Differentiable ℂ f := by dsimp [f]; fun_prop
  have hg : Differentiable ℂ g := normalizedSharpnessExample_entire k
  have hAf : AnalyticOnNhd ℂ f (closedBall 0 r) := fun z _ ↦ hf.analyticAt z
  have hAg : AnalyticOnNhd ℂ g (closedBall 0 r) := fun z _ ↦ hg.analyticAt z
  have heq : f = (-((id : ℂ → ℂ) ^ k)) * g := by
    funext z
    exact sharpnessExample_origin_factor hk z
  have hord (z : ℂ) (hz : z ≠ 0) : analyticOrderAt f z = analyticOrderAt g z := by
    rw [heq, analyticOrderAt_mul (by fun_prop) (hg.analyticAt z)]
    have hP : AnalyticAt ℂ (-((id : ℂ → ℂ) ^ k)) z := by fun_prop
    rw [hP.analyticOrderAt_eq_zero.mpr (by simpa using pow_ne_zero k hz), zero_add]
  let e : ℂ → ℤ := fun z ↦ if z = 0 then k else 0
  have hd (z : ℂ) : MeromorphicOn.divisor f (closedBall 0 r) z =
      e z + MeromorphicOn.divisor g (closedBall 0 r) z := by
    by_cases hz : z = 0
    · subst z
      have h0 : (0 : ℂ) ∈ closedBall 0 r := by simpa using hr
      rw [hAf.divisor_apply h0, hAg.divisor_apply h0]
      have hgz : analyticOrderAt g 0 = 0 := (hg.analyticAt 0).analyticOrderAt_eq_zero.mpr
        (by dsimp [g]; rw [normalizedSharpnessExample_at_zero hk]; norm_num)
      simp [f, e, sharpnessExample_origin_order hk, hgz]
    · by_cases hzr : z ∈ closedBall 0 r
      · rw [hAf.divisor_apply hzr, hAg.divisor_apply hzr, hord z hz]
        simp [e, hz]
      · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzr, e, hz]
  have hefin : e.support.Finite := by
    apply (Set.finite_singleton (0 : ℂ)).subset
    intro z hz
    by_contra hz0
    exact hz (by simp [e, hz0])
  have he : (∑ᶠ z, e z) = k := by
    rw [finsum_eq_single e 0 (by intro z hz; simp [e, hz])]
    simp [e]
  have hs : (∑ᶠ z, MeromorphicOn.divisor f (closedBall 0 r) z) =
      (k : ℤ) + ∑ᶠ z, MeromorphicOn.divisor g (closedBall 0 r) z := by
    simp_rw [hd]
    rw [finsum_add_distrib hefin
      ((MeromorphicOn.divisor g (closedBall 0 r)).finiteSupport (isCompact_closedBall 0 r)), he]
  rw [← entireZeroCount_intCast hf r, ← entireZeroCount_intCast hg r] at hs
  exact_mod_cast hs

/-- Rudin's printed example `1 - exp(z^k)` has exactly the asserted limiting exponent. -/
theorem sharpnessExample_zero_count_limit {k : ℕ} (hk : 0 < k) :
    Tendsto (fun r : ℝ ↦
      Real.log (entireZeroCount (fun z : ℂ ↦ 1 - Complex.exp (z ^ k)) r) / Real.log r)
      atTop (𝓝 (k : ℝ)) := by
  obtain ⟨c, C, hc, hC, hb⟩ := normalizedSharpnessExample_polynomial_zero_bounds hk
  apply tendsto_log_count_of_polynomial_bounds _ k hc
    (show 0 < C + k from add_pos_of_pos_of_nonneg hC (Nat.cast_nonneg k))
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with r hrb hr
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  rw [sharpnessExample_zero_count_eq hk hr0, Nat.cast_add]
  constructor
  · exact hrb.1.trans (le_add_of_nonneg_left (Nat.cast_nonneg k))
  · calc
      (k : ℝ) + entireZeroCount (normalizedSharpnessExample k) r ≤ k * r ^ k + C * r ^ k :=
        add_le_add (le_mul_of_one_le_right (Nat.cast_nonneg k) (one_le_pow₀ hr)) hrb.2
      _ = (C + k) * r ^ k := by ring

#print axioms norm_le_maximumModulus
#print axioms one_le_maximumModulus
#print axioms entireZeroCount_intCast
#print axioms zero_count_log_two_le
#print axioms limsup_log_count_le_of_polynomial_bound
#print axioms zero_count_growth_limsup
#print axioms normalizedSharpnessExample_entire
#print axioms normalizedSharpnessExample_at_zero
#print axioms sharpnessExample_origin_factor
#print axioms sharpnessExample_origin_order
#print axioms one_le_divisor_of_zero
#print axioms finite_distinct_zeros_le_count
#print axioms exists_sharpness_zero_sequence
#print axioms sharpness_zero_count_floor_le
#print axioms norm_normalizedSharpnessExample_le
#print axioms maximumModulus_normalizedSharpnessExample_le
#print axioms maximumModulus_sharpnessExample_le
#print axioms tendsto_log_count_of_polynomial_bounds
#print axioms normalizedSharpnessExample_polynomial_zero_bounds
#print axioms normalizedSharpnessExample_zero_count_limit
#print axioms sharpnessExample_zero_count_eq
#print axioms sharpnessExample_zero_count_limit

end RudinRCA.Chapter15.ZeroGrowthWork
