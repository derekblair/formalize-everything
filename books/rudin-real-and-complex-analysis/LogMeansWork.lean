import RudinRCA.Chapter15
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Instances.EReal.Lemmas

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace RudinRCA.Chapter15

/-- The extended logarithm used in 15.19; it has value -∞ at zero. -/
def extendedLogNorm (z : ℂ) : EReal := ENNReal.log (ENNReal.ofReal ‖z‖)

@[simp] theorem extendedLogNorm_zero : extendedLogNorm 0 = ⊥ := by
  simp [extendedLogNorm]

theorem extendedLogNorm_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    extendedLogNorm z = (Real.log ‖z‖ : EReal) :=
  ENNReal.log_ofReal_of_pos (norm_pos_iff.mpr hz)

theorem continuous_extendedLogNorm : Continuous extendedLogNorm :=
  ENNReal.continuous_log.comp (ENNReal.continuous_ofReal.comp continuous_norm)

/-- The negative part of the extended logarithm, retaining +∞ at a zero. -/
def negativeLogNorm (z : ℂ) : ℝ≥0∞ := (-extendedLogNorm z).toENNReal

@[simp] theorem negativeLogNorm_zero : negativeLogNorm 0 = ⊤ := by
  simp [negativeLogNorm]

theorem continuous_negativeLogNorm : Continuous negativeLogNorm :=
  EReal.continuous_toENNReal.comp continuous_extendedLogNorm.neg

/-- For positive radii, isolated zeros have angular measure zero. Thus the real
integral used here agrees with the extended-log convention once integrability
and the negligible-zero-set bridge have been established. -/
def logCircleMean (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 r

/-- Jensen's sum on a single fixed larger disk, with positive logarithms.
This form makes monotonicity in the smaller radius explicit. -/
theorem logCircleMean_eq_posLog_divisor_sum {f : ℂ → ℂ} {r s : ℝ}
    (hr : 0 < r) (hrs : r ≤ s)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 s)) (h0 : f 0 ≠ 0) :
    logCircleMean f r =
      (∑ᶠ z, (MeromorphicOn.divisor f (Metric.closedBall 0 s) z : ℝ) *
        Real.posLog (r / ‖z‖)) + Real.log ‖f 0‖ := by
  have hfr : AnalyticOnNhd ℂ f (Metric.closedBall 0 r) :=
    hf.mono (Metric.closedBall_subset_closedBall hrs)
  have hfr' : AnalyticOnNhd ℂ f (Metric.closedBall 0 |r|) := by
    simpa only [abs_of_pos hr] using hfr
  have hj := hfr'.circleAverage_log_norm hr.ne' h0
  rw [abs_of_pos hr] at hj
  change logCircleMean f r = _ at hj
  rw [hj]
  congr 1
  apply finsum_congr
  intro z
  by_cases hz0 : z = 0
  · subst z
    have hd0 (t : ℝ) (ht : 0 ≤ t) (hft : AnalyticOnNhd ℂ f (Metric.closedBall 0 t)) :
        MeromorphicOn.divisor f (Metric.closedBall 0 t) 0 = 0 := by
      rw [hft.divisor_apply (Metric.mem_closedBall_self ht),
        (hft 0 (Metric.mem_closedBall_self ht)).analyticOrderAt_eq_zero.mpr h0]
      simp
    simp [hd0 r hr.le hfr, hd0 s (hr.le.trans hrs) hf]
  · have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    by_cases hzr : ‖z‖ ≤ r
    · have hzr' : z ∈ Metric.closedBall (0 : ℂ) r := by simpa using hzr
      have hzs' : z ∈ Metric.closedBall (0 : ℂ) s := by simpa using hzr.trans hrs
      have hlog : Real.posLog (r / ‖z‖) = Real.log (r / ‖z‖) := by
        apply Real.posLog_eq_log
        rw [abs_of_nonneg (div_nonneg hr.le hzn.le)]
        exact (le_div_iff₀ hzn).2 (by simpa using hzr)
      rw [hfr.meromorphicOn.divisor_apply hzr', hf.meromorphicOn.divisor_apply hzs', hlog]
      simp [div_eq_mul_inv]
    · have hzr' : z ∉ Metric.closedBall (0 : ℂ) r := by simpa using hzr
      have hd0 : MeromorphicOn.divisor f (Metric.closedBall 0 r) z = 0 := by
        by_contra hn
        exact hzr' ((MeromorphicOn.divisor f (Metric.closedBall 0 r)).supportWithinDomain hn)
      have hlog : Real.posLog (r / ‖z‖) = 0 := by
        apply (Real.posLog_eq_zero_iff _).2
        rw [abs_of_nonneg (div_nonneg hr.le hzn.le)]
        exact (div_le_one hzn).2 (le_of_lt (lt_of_not_ge hzr))
      simp [hd0, hlog]

/-- Monotonicity in 15.19 when the center value is nonzero. The general case
follows by removing the finite-order zero at the origin. -/
theorem logCircleMean_mono_of_center_ne_zero {f : ℂ → ℂ} {r s : ℝ}
    (hr : 0 < r) (hrs : r ≤ s)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 s)) (h0 : f 0 ≠ 0) :
    logCircleMean f r ≤ logCircleMean f s := by
  have hs : 0 < s := hr.trans_le hrs
  rw [logCircleMean_eq_posLog_divisor_sum hr hrs hf h0,
    logCircleMean_eq_posLog_divisor_sum hs le_rfl hf h0]
  apply add_le_add_right
  have hD : Function.HasFiniteSupport
      (fun z ↦ (MeromorphicOn.divisor f (Metric.closedBall 0 s) z : ℝ)) := by
    simpa [Function.HasFiniteSupport, Function.support] using
      (MeromorphicOn.divisor f (Metric.closedBall 0 s)).finiteSupport (isCompact_closedBall 0 s)
  apply finsum_le_finsum (hD.mul_left _) (hD.mul_left _)
  intro z
  have hm : (0 : ℝ) ≤ MeromorphicOn.divisor f (Metric.closedBall 0 s) z := by
    exact_mod_cast hf.divisor_nonneg z
  apply mul_le_mul_of_nonneg_left _ hm
  apply Real.posLog_le_posLog
  · have hn : 0 ≤ r / ‖z‖ := div_nonneg hr.le (norm_nonneg z)
    linarith
  · exact div_le_div_of_nonneg_right hrs (norm_nonneg z)

/-- The origin correction in Jensen's formula is retained when the center is
itself a zero. This identity uses a single larger-disk divisor. -/
theorem logCircleMean_eq_posLog_divisor_sum_general {f : ℂ → ℂ} {r s : ℝ}
    (hr : 0 < r) (hrs : r ≤ s)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 s)) :
    logCircleMean f r =
      (∑ᶠ z, (MeromorphicOn.divisor f (Metric.closedBall 0 s) z : ℝ) *
        Real.posLog (r / ‖z‖)) +
      (MeromorphicOn.divisor f (Metric.closedBall 0 s) 0 : ℝ) * Real.log r +
      Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have hfr : AnalyticOnNhd ℂ f (Metric.closedBall 0 r) :=
    hf.mono (Metric.closedBall_subset_closedBall hrs)
  have hfr' : AnalyticOnNhd ℂ f (Metric.closedBall 0 |r|) := by
    simpa only [abs_of_pos hr] using hfr
  have hj := hfr'.meromorphicOn.circleAverage_log_norm hr.ne'
  rw [abs_of_pos hr] at hj
  change logCircleMean f r = _ at hj
  rw [hj]
  have hcenter : MeromorphicOn.divisor f (Metric.closedBall 0 r) 0 =
      MeromorphicOn.divisor f (Metric.closedBall 0 s) 0 := by
    rw [hfr.meromorphicOn.divisor_apply (Metric.mem_closedBall_self hr.le),
      hf.meromorphicOn.divisor_apply (Metric.mem_closedBall_self (hr.le.trans hrs))]
  rw [hcenter]
  congr 2
  apply finsum_congr
  intro z
  by_cases hz0 : z = 0
  · subst z
    simp
  · have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    by_cases hzr : ‖z‖ ≤ r
    · have hzr' : z ∈ Metric.closedBall (0 : ℂ) r := by simpa using hzr
      have hzs' : z ∈ Metric.closedBall (0 : ℂ) s := by simpa using hzr.trans hrs
      have hlog : Real.posLog (r / ‖z‖) = Real.log (r / ‖z‖) := by
        apply Real.posLog_eq_log
        rw [abs_of_nonneg (div_nonneg hr.le hzn.le)]
        exact (le_div_iff₀ hzn).2 (by simpa using hzr)
      rw [hfr.meromorphicOn.divisor_apply hzr', hf.meromorphicOn.divisor_apply hzs', hlog]
      simp [div_eq_mul_inv]
    · have hzr' : z ∉ Metric.closedBall (0 : ℂ) r := by simpa using hzr
      have hd0 : MeromorphicOn.divisor f (Metric.closedBall 0 r) z = 0 := by
        by_contra hn
        exact hzr' ((MeromorphicOn.divisor f (Metric.closedBall 0 r)).supportWithinDomain hn)
      have hlog : Real.posLog (r / ‖z‖) = 0 := by
        apply (Real.posLog_eq_zero_iff _).2
        rw [abs_of_nonneg (div_nonneg hr.le hzn.le)]
        exact (div_le_one hzn).2 (le_of_lt (lt_of_not_ge hzr))
      simp [hd0, hlog]

/-- The monotonicity conclusion of 15.19, including zeros at the center. -/
theorem logCircleMean_mono {f : ℂ → ℂ} {r s : ℝ}
    (hr : 0 < r) (hrs : r ≤ s)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 s)) :
    logCircleMean f r ≤ logCircleMean f s := by
  have hs : 0 < s := hr.trans_le hrs
  rw [logCircleMean_eq_posLog_divisor_sum_general hr hrs hf,
    logCircleMean_eq_posLog_divisor_sum_general hs le_rfl hf]
  apply add_le_add_right
  apply add_le_add
  · have hD : Function.HasFiniteSupport
        (fun z ↦ (MeromorphicOn.divisor f (Metric.closedBall 0 s) z : ℝ)) := by
      simpa [Function.HasFiniteSupport, Function.support] using
        (MeromorphicOn.divisor f (Metric.closedBall 0 s)).finiteSupport (isCompact_closedBall 0 s)
    apply finsum_le_finsum (hD.mul_left _) (hD.mul_left _)
    intro z
    have hm : (0 : ℝ) ≤ MeromorphicOn.divisor f (Metric.closedBall 0 s) z := by
      exact_mod_cast hf.divisor_nonneg z
    apply mul_le_mul_of_nonneg_left _ hm
    apply Real.posLog_le_posLog
    · have hn : 0 ≤ r / ‖z‖ := div_nonneg hr.le (norm_nonneg z)
      linarith
    · exact div_le_div_of_nonneg_right hrs (norm_nonneg z)
  · apply mul_le_mul_of_nonneg_left (Real.log_le_log hr hrs)
    exact_mod_cast hf.divisor_nonneg 0

/-- The disk version requires no analytic extension across its boundary. -/
theorem disk_logCircleMean_mono {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) {r s : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) (hs : s < 1) :
    logCircleMean f r ≤ logCircleMean f s :=
  logCircleMean_mono hr hrs
    ((hf.analyticOnNhd Metric.isOpen_ball).mono (Metric.closedBall_subset_ball hs))

/-- Removing the origin zero on the unit disk, without any extension hypothesis
outside the disk. This is the local-to-global step used in 15.19. -/
theorem disk_remove_zero_at_origin {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hne : ∃ w ∈ Metric.ball 0 1, f w ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball 0 1) ∧ h 0 ≠ 0 ∧
      ∀ z ∈ Metric.ball 0 1, f z = z ^ analyticOrderNatAt f 0 * h z := by
  have hfa := hf.analyticOnNhd Metric.isOpen_ball
  have hfinite : analyticOrderAt f 0 ≠ ⊤ := by
    apply analyticOrderAt_ne_top_of_component_nonzero Metric.isOpen_ball hf
    · intro z hz
      rw [(convex_ball (0 : ℂ) 1).isPreconnected.connectedComponentIn hz]
      exact hne
    · exact Metric.mem_ball_self zero_lt_one
  obtain ⟨g, hga, hg0, heq⟩ :=
    (hfa 0 (Metric.mem_ball_self zero_lt_one)).analyticOrderAt_ne_top.mp hfinite
  let k := analyticOrderNatAt f 0
  let h : ℂ → ℂ := fun z ↦ if z = 0 then g 0 else f z / z ^ k
  have heq' : f =ᶠ[𝓝 0] fun z ↦ z ^ k * g z := by
    simpa only [sub_zero, smul_eq_mul] using heq
  have hnear : h =ᶠ[𝓝 0] g := by
    filter_upwards [heq'] with z hz
    by_cases hz0 : z = 0
    · simp [h, hz0]
    · simp [h, hz0, hz, mul_div_cancel_left₀, pow_ne_zero _ hz0]
  have hh : DifferentiableOn ℂ h (Metric.ball 0 1) := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    by_cases hz0 : z = 0
    · subst z
      exact (hga.congr hnear.symm).differentiableAt
    · apply AnalyticAt.differentiableAt
      apply ((hfa z hz).div (analyticAt_id.pow k) (pow_ne_zero _ hz0)).congr
      filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
      simp [h, hw]
  refine ⟨h, hh, by simpa [h] using hg0, ?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    simpa only [h, if_pos rfl] using heq'.eq_of_nhds
  · dsimp only [h]
    rw [if_neg hz0]
    exact (mul_div_cancel₀ (f z) (pow_ne_zero k hz0)).symm

/-- Near the origin the logarithmic mean has the exact form k log r + C.
This includes the extended-real limit -∞ when the origin is a zero. -/
theorem exists_small_radius_logCircleMean_formula {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hne : ∃ w ∈ Metric.ball 0 1, f w ≠ 0) :
    ∃ k : ℕ, ∃ C R : ℝ, 0 < R ∧ (k = 0 ↔ f 0 ≠ 0) ∧
      (k = 0 → C = Real.log ‖f 0‖) ∧
      ∀ r : ℝ, 0 < r → r < R → logCircleMean f r = (k : ℝ) * Real.log r + C := by
  obtain ⟨h, hh, hh0, heq⟩ := disk_remove_zero_at_origin hf hne
  let k := analyticOrderNatAt f 0
  have h0mem : (0 : ℂ) ∈ Metric.ball 0 1 := Metric.mem_ball_self zero_lt_one
  have hha := hh.analyticOnNhd Metric.isOpen_ball
  have hzero := (hha 0 h0mem).continuousAt.eventually_ne hh0
  obtain ⟨ε, hε, hεzero⟩ := Metric.eventually_nhds_iff.mp hzero
  let R := min ε 1
  have hR : 0 < R := lt_min hε zero_lt_one
  have hk : k = 0 ↔ f 0 ≠ 0 := by
    constructor
    · intro hk
      have hz := heq 0 h0mem
      have hz' : f 0 = h 0 := by
        simpa only [← show analyticOrderNatAt f 0 = k from rfl, hk, pow_zero, one_mul] using hz
      exact hz'.trans_ne hh0
    · intro hfn
      have hz : analyticOrderAt f 0 = 0 :=
        ((hf.analyticOnNhd Metric.isOpen_ball) 0 h0mem).analyticOrderAt_eq_zero.mpr hfn
      simp only [k, analyticOrderNatAt, hz, ENat.toNat_zero]
  refine ⟨k, Real.log ‖h 0‖, R, hR, hk, ?_, ?_⟩
  · intro hk0
    have hz := heq 0 h0mem
    have hz' : f 0 = h 0 := by simpa only [← show analyticOrderNatAt f 0 = k from rfl,
      hk0, pow_zero, one_mul] using hz
    rw [hz']
  · intro r hr hrR
    have hr1 : r < 1 := hrR.trans_le (min_le_right _ _)
    have hrε : r < ε := hrR.trans_le (min_le_left _ _)
    have hclosed : Metric.closedBall (0 : ℂ) |r| ⊆ Metric.ball 0 1 := by
      exact Metric.closedBall_subset_ball (by simpa only [abs_of_pos hr] using hr1)
    have hhclosed := hha.mono hclosed
    have hhz : ∀ z ∈ Metric.closedBall (0 : ℂ) |r|, h z ≠ 0 := by
      intro z hz
      apply hεzero
      have hzn : ‖z‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right,
        abs_of_pos hr] using hz
      simpa only [dist_zero_right] using hzn.trans_lt hrε
    have hcongr : Set.EqOn (fun z ↦ Real.log ‖f z‖)
        (fun z ↦ (k : ℝ) * Real.log r + Real.log ‖h z‖)
        (Metric.sphere 0 |r|) := by
      intro z hz
      have hzn : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right,
        abs_of_pos hr] using hz
      have hzneq : ‖z‖ ≠ 0 := by rw [hzn]; exact hr.ne'
      rw [heq z (hclosed (Metric.sphere_subset_closedBall hz)), norm_mul, norm_pow,
        Real.log_mul (pow_ne_zero _ hzneq)
          (norm_ne_zero_iff.mpr (hhz z (Metric.sphere_subset_closedBall hz))),
        Real.log_pow, hzn]
    rw [logCircleMean, Real.circleAverage_congr_sphere hcongr,
      Real.circleAverage_fun_add (circleIntegrable_const _ _ _)
        (hhclosed.mono Metric.sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm,
      Real.circleAverage_const, hhclosed.circleAverage_log_norm_of_ne_zero hhz]

/-- The r↓0 conclusion of 15.19, with the printed extended value log 0=-∞. -/
theorem logCircleMean_tendsto_origin {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hne : ∃ w ∈ Metric.ball 0 1, f w ≠ 0) :
    Tendsto (fun r : ℝ ↦ (logCircleMean f r : EReal)) (𝓝[>] 0)
      (𝓝 (extendedLogNorm (f 0))) := by
  obtain ⟨k, C, R, hR, hk, hC, heq⟩ := exists_small_radius_logCircleMean_formula hf hne
  have hevent : (fun r : ℝ ↦ (logCircleMean f r : EReal)) =ᶠ[𝓝[>] 0]
      (fun r ↦ ((k : ℝ) * Real.log r + C : EReal)) := by
    filter_upwards [self_mem_nhdsWithin,
      (nhdsWithin_le_nhds (Iio_mem_nhds hR) : ∀ᶠ r : ℝ in 𝓝[>] 0, r < R)] with r hr hrR
    exact congrArg (fun x : ℝ ↦ (x : EReal)) (heq r hr hrR)
  by_cases h0 : f 0 = 0
  · have hk0 : k ≠ 0 := fun h ↦ (hk.mp h) h0
    have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
    have ht : Tendsto (fun r : ℝ ↦ (k : ℝ) * Real.log r + C) (𝓝[>] 0) atBot :=
      tendsto_atBot_add_const_right _ C (Real.tendsto_log_nhdsGT_zero.const_mul_atBot hkpos)
    rw [h0, extendedLogNorm_zero]
    exact (EReal.tendsto_coe_atBot.comp ht).congr' hevent.symm
  · have hk0 := hk.mpr h0
    have hconst : Tendsto (fun r : ℝ ↦ ((k : ℝ) * Real.log r + C : EReal))
        (𝓝[>] 0) (𝓝 (extendedLogNorm (f 0))) := by
      simpa only [hk0, Nat.cast_zero, zero_mul, zero_add, hC hk0,
        extendedLogNorm_of_ne_zero h0] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (Real.log ‖f 0‖ : EReal))
          (𝓝[>] 0) (𝓝 (Real.log ‖f 0‖ : EReal)))
    exact hconst.congr' hevent.symm

/-- The nonzero points form a codiscrete set on the disk. -/
theorem disk_codiscrete_nonzero {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hne : ∃ w ∈ Metric.ball 0 1, f w ≠ 0) :
    ∀ᶠ z in codiscreteWithin (Metric.ball (0 : ℂ) 1), f z ≠ 0 := by
  rcases (hf.analyticOnNhd Metric.isOpen_ball).
    eqOn_zero_or_eventually_ne_zero_of_preconnected
      (convex_ball (0 : ℂ) 1).isPreconnected with hz | hn
  · obtain ⟨w, hw, hfw⟩ := hne
    exact False.elim (hfw (hz hw))
  · exact hn

/-- Isolated interior zeros meet each circle in an angular null set. -/
theorem disk_angular_ae_nonzero {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hne : ∃ w ∈ Metric.ball 0 1, f w ≠ 0) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    ∀ᵐ θ : ℝ, f (circleMap 0 r θ) ≠ 0 := by
  have hcod : ∀ᶠ z in codiscreteWithin (Metric.ball (0 : ℂ) 1), f z ≠ 0 := by
    rcases (hf.analyticOnNhd Metric.isOpen_ball).
      eqOn_zero_or_eventually_ne_zero_of_preconnected
        (convex_ball (0 : ℂ) 1).isPreconnected with hz | hn
    · obtain ⟨w, hw, hfw⟩ := hne
      exact False.elim (hfw (hz hw))
    · exact hn
  have hsub : Metric.sphere (0 : ℂ) |r| ⊆ Metric.ball 0 1 :=
    Metric.sphere_subset_ball (by simpa only [abs_of_pos hr] using hr1)
  have hθ := circleMap_preimage_codiscrete hr.ne'
    (codiscreteWithin_mono hsub hcod)
  have hae : ae (volume : Measure ℝ) ≤ codiscrete ℝ := by
    simpa using (ae_restrict_le_codiscreteWithin
      (μ := (volume : Measure ℝ)) measurableSet_univ)
  exact hae hθ

/-- The real logarithm agrees almost everywhere with the printed extended-log
convention on every positive circle inside the disk. -/
theorem disk_angular_extendedLogNorm_eq {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hne : ∃ w ∈ Metric.ball 0 1, f w ≠ 0) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    ∀ᵐ θ : ℝ, extendedLogNorm (f (circleMap 0 r θ)) =
      (Real.log ‖f (circleMap 0 r θ)‖ : EReal) :=
  (disk_angular_ae_nonzero hf hne hr hr1).mono
    (fun _ hθ ↦ extendedLogNorm_of_ne_zero hθ)

theorem negativeLogNorm_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    negativeLogNorm z = ENNReal.ofReal (-Real.log ‖z‖) := by
  rw [negativeLogNorm, extendedLogNorm_of_ne_zero hz, ← EReal.coe_neg,
    EReal.real_coe_toENNReal]

/-- Unnormalized angular measure; the factor `2π` is explicit in mean identities. -/
def angularMeasure : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))

/-- Exact conversion between the nonnegative extended integral and the usual
circle mean, under the harmless normalization `|f| ≤ 1`. -/
theorem negativeLogNorm_angular_integral_eq {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hne : ∃ w ∈ Metric.ball 0 1, f w ≠ 0)
    (hbound : ∀ z ∈ Metric.ball 0 1, ‖f z‖ ≤ 1) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    (∫⁻ θ, negativeLogNorm (f (circleMap 0 r θ)) ∂angularMeasure) =
      ENNReal.ofReal (-(2 * Real.pi) * logCircleMean f r) := by
  have hs : Metric.sphere (0 : ℂ) |r| ⊆ Metric.ball 0 1 :=
    Metric.sphere_subset_ball (by simpa only [abs_of_pos hr] using hr1)
  have hi : CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 r :=
    ((hf.analyticOnNhd Metric.isOpen_ball).mono hs).meromorphicOn.circleIntegrable_log_norm
  have hi' : Integrable (fun θ ↦ Real.log ‖f (circleMap 0 r θ)‖) angularMeasure :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : 0 ≤ 2 * Real.pi)).1 hi
  have hn : ∀ᵐ θ ∂angularMeasure, 0 ≤ -Real.log ‖f (circleMap 0 r θ)‖ := by
    apply ae_of_all
    intro θ
    apply neg_nonneg.mpr
    exact Real.log_nonpos (norm_nonneg _) (hbound _ (hs (circleMap_mem_sphere' _ _ _)))
  have heq : (fun θ ↦ negativeLogNorm (f (circleMap 0 r θ))) =ᵐ[angularMeasure]
      (fun θ ↦ ENNReal.ofReal (-Real.log ‖f (circleMap 0 r θ)‖)) := by
    have hzero := ae_restrict_of_ae (disk_angular_ae_nonzero hf hne hr hr1)
    exact hzero.mono fun _ hz ↦ negativeLogNorm_of_ne_zero hz
  rw [lintegral_congr_ae heq, ← ofReal_integral_eq_lintegral_ofReal hi'.neg hn]
  congr 1
  rw [integral_neg]
  simp only [logCircleMean, Real.circleAverage, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * Real.pi), angularMeasure]
  field_simp

/-- Fatou's step in 15.19, stated independently of the existence theorem for
radial boundary values. The extended negative logarithm detects boundary zeros. -/
theorem negativeLogNorm_fatou {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℂ} {g : α → ℂ}
    (hmeas : ∀ n, AEMeasurable (f n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    (∫⁻ x, negativeLogNorm (g x) ∂μ) ≤
      liminf (fun n ↦ ∫⁻ x, negativeLogNorm (f n x) ∂μ) atTop := by
  have h := lintegral_liminf_le'
    (fun n ↦ continuous_negativeLogNorm.measurable.comp_aemeasurable (hmeas n))
  have heq : (fun x ↦ liminf (fun n ↦ negativeLogNorm (f n x)) atTop) =ᵐ[μ]
      (fun x ↦ negativeLogNorm (g x)) := by
    filter_upwards [hlim] with x hx
    exact (continuous_negativeLogNorm.continuousAt.tendsto.comp hx).liminf_eq
  rwa [lintegral_congr_ae heq] at h

/-- A finite integral of the extended negative logarithm rules out zeros on any
set of positive measure, as required for the final assertion of 15.19. -/
theorem ae_nonzero_of_negativeLogNorm_integral_finite {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {g : α → ℂ}
    (hg : AEMeasurable g μ) (hfinite : (∫⁻ x, negativeLogNorm (g x) ∂μ) ≠ ⊤) :
    ∀ᵐ x ∂μ, g x ≠ 0 := by
  have hlt := ae_lt_top'
    (continuous_negativeLogNorm.measurable.comp_aemeasurable hg) hfinite
  filter_upwards [hlt] with x hx hz
  simpa only [hz, negativeLogNorm_zero, lt_self_iff_false] using hx

/-- Finite negative-log integral implies ordinary logarithmic integrability
when the boundary function has norm at most one. -/
theorem integrable_log_norm_of_negativeLogNorm_finite {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {g : α → ℂ}
    (hg : AEMeasurable g μ) (hbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ 1)
    (hfinite : (∫⁻ x, negativeLogNorm (g x) ∂μ) ≠ ⊤) :
    Integrable (fun x ↦ Real.log ‖g x‖) μ := by
  have hmeas := continuous_negativeLogNorm.measurable.comp_aemeasurable hg
  have hi := integrable_toReal_of_lintegral_ne_top hmeas hfinite
  apply hi.neg.congr
  filter_upwards [ae_nonzero_of_negativeLogNorm_integral_finite hg hfinite, hbound]
    with x hx hxb
  rw [negativeLogNorm_of_ne_zero hx,
    ENNReal.toReal_ofReal (neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hxb)), neg_neg]

/-- The normalized boundary conclusion of 15.19, conditional only on actual
radial convergence along the specified circles. A separate existence proof
supplies these limits; this helper is not counted as that existence theorem. -/
theorem disk_boundary_log_integrable_of_radial_sequence {f : ℂ → ℂ} {g : ℝ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hne : ∃ w ∈ Metric.ball 0 1, f w ≠ 0)
    (hbound : ∀ z ∈ Metric.ball 0 1, ‖f z‖ ≤ 1)
    (r : ℕ → ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hrlower : ∀ n, r₀ ≤ r n) (hrupper : ∀ n, r n < 1)
    (hlim : ∀ᵐ θ ∂angularMeasure,
      Tendsto (fun n ↦ f (circleMap 0 (r n) θ)) atTop (𝓝 (g θ))) :
    (∫⁻ θ, negativeLogNorm (g θ) ∂angularMeasure) ≤
      ENNReal.ofReal (-(2 * Real.pi) * logCircleMean f r₀) ∧
    Integrable (fun θ ↦ Real.log ‖g θ‖) angularMeasure ∧
    (∀ᵐ θ ∂angularMeasure, g θ ≠ 0) := by
  have hrpos (n : ℕ) : 0 < r n := hr₀.trans_le (hrlower n)
  have hcircle (n : ℕ) (θ : ℝ) : circleMap 0 (r n) θ ∈ Metric.ball (0 : ℂ) 1 := by
    apply Metric.sphere_subset_ball _ (circleMap_mem_sphere' _ _ _)
    simpa only [abs_of_pos (hrpos n)] using hrupper n
  have hmeas (n : ℕ) : AEMeasurable (fun θ ↦ f (circleMap 0 (r n) θ)) angularMeasure :=
    (hf.continuousOn.comp_continuous (continuous_circleMap 0 (r n)) (hcircle n)).measurable.aemeasurable
  have hgm : AEMeasurable g angularMeasure :=
    aemeasurable_of_tendsto_metrizable_ae atTop hmeas hlim
  have hgb : ∀ᵐ θ ∂angularMeasure, ‖g θ‖ ≤ 1 := by
    filter_upwards [hlim] with θ hθ
    exact le_of_tendsto hθ.norm (Eventually.of_forall (fun n ↦ hbound _ (hcircle n θ)))
  have hb (n : ℕ) :
      (∫⁻ θ, negativeLogNorm (f (circleMap 0 (r n) θ)) ∂angularMeasure) ≤
        ENNReal.ofReal (-(2 * Real.pi) * logCircleMean f r₀) := by
    rw [negativeLogNorm_angular_integral_eq hf hne hbound (hrpos n) (hrupper n)]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonpos_left
      (disk_logCircleMean_mono hf hr₀ (hrlower n) (hrupper n)) (by positivity)
  have hb' := (negativeLogNorm_fatou hmeas hlim).trans
    (liminf_le_of_frequently_le' (Eventually.of_forall hb).frequently)
  have hfinite : (∫⁻ θ, negativeLogNorm (g θ) ∂angularMeasure) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb'
  exact ⟨hb', integrable_log_norm_of_negativeLogNorm_finite hgm hgb hfinite,
    ae_nonzero_of_negativeLogNorm_integral_finite hgm hfinite⟩

/-- Conversion for boundary functions after the null-zero-set and integrability
conclusions have been established. -/
theorem negativeLogNorm_integral_eq_of_integrable {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {g : α → ℂ}
    (hzero : ∀ᵐ x ∂μ, g x ≠ 0) (hbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ 1)
    (hi : Integrable (fun x ↦ Real.log ‖g x‖) μ) :
    (∫⁻ x, negativeLogNorm (g x) ∂μ) =
      ENNReal.ofReal (-(∫ x, Real.log ‖g x‖ ∂μ)) := by
  have heq : (fun x ↦ negativeLogNorm (g x)) =ᵐ[μ]
      (fun x ↦ ENNReal.ofReal (-Real.log ‖g x‖)) :=
    hzero.mono (fun _ hx ↦ negativeLogNorm_of_ne_zero hx)
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ -Real.log ‖g x‖ :=
    hbound.mono (fun _ hx ↦ neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hx))
  rw [lintegral_congr_ae heq, ← ofReal_integral_eq_lintegral_ofReal hi.neg hnonneg,
    integral_neg]

/-- The mean inequality in 15.19 follows with its exact normalization from the
extended Fatou bound. -/
theorem mean_le_boundary_log_mean {g : ℝ → ℂ} {m : ℝ} (hm : m ≤ 0)
    (hzero : ∀ᵐ θ ∂angularMeasure, g θ ≠ 0)
    (hbound : ∀ᵐ θ ∂angularMeasure, ‖g θ‖ ≤ 1)
    (hi : Integrable (fun θ ↦ Real.log ‖g θ‖) angularMeasure)
    (hfatou : (∫⁻ θ, negativeLogNorm (g θ) ∂angularMeasure) ≤
      ENNReal.ofReal (-(2 * Real.pi) * m)) :
    m ≤ (2 * Real.pi)⁻¹ * ∫ θ, Real.log ‖g θ‖ ∂angularMeasure := by
  rw [negativeLogNorm_integral_eq_of_integrable hzero hbound hi] at hfatou
  have hnonneg : 0 ≤ -(2 * Real.pi) * m := mul_nonneg_of_nonpos_of_nonpos (by positivity) hm
  have hreal := (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hfatou
  have hdiv : m ≤ (∫ θ, Real.log ‖g θ‖ ∂angularMeasure) / (2 * Real.pi) :=
    (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2 (by linarith)
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

/-- A concrete sequence approaching 1 through the interval [r₀,1). -/
theorem exists_radial_sequence_above {r₀ : ℝ} (hr₀ : r₀ < 1) :
    ∃ r : ℕ → ℝ, (∀ n, r₀ ≤ r n) ∧ (∀ n, r n < 1) ∧
      Tendsto r atTop (𝓝[<] 1) := by
  let r : ℕ → ℝ := fun n ↦ 1 - (1 - r₀) * (1 / 2 : ℝ) ^ n
  have hpos : 0 < 1 - r₀ := sub_pos.mpr hr₀
  have hlow (n : ℕ) : r₀ ≤ r n := by
    have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h := mul_le_mul_of_nonneg_left hp hpos.le
    dsimp [r]
    linarith
  have hupp (n : ℕ) : r n < 1 := by
    have hp : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
    dsimp [r]
    exact sub_lt_self _ (mul_pos hpos hp)
  have ht : Tendsto r atTop (𝓝 1) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    simpa only [r, mul_zero, sub_zero] using
      tendsto_const_nhds.sub (hp.const_mul (1 - r₀))
  exact ⟨r, hlow, hupp, tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall hupp⟩⟩

/-- Actual radial convergence gives the normalized boundary estimate in 15.19.
The existence of the radial function is supplied by the separate Fatou theorem. -/
theorem normalized_log_means_of_radial_limits {f : ℂ → ℂ} {g : ℝ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hne : ∃ w ∈ Metric.ball 0 1, f w ≠ 0)
    (hbound : ∀ z ∈ Metric.ball 0 1, ‖f z‖ ≤ 1)
    (hradial : ∀ᵐ θ : ℝ,
      Tendsto (fun r : ℝ ↦ f (circleMap 0 r θ)) (𝓝[<] 1) (𝓝 (g θ))) :
    Integrable (fun θ ↦ Real.log ‖g θ‖) angularMeasure ∧
      (∀ᵐ θ ∂angularMeasure, g θ ≠ 0) ∧
      ∀ r : ℝ, 0 < r → r < 1 →
        logCircleMean f r ≤ (2 * Real.pi)⁻¹ * ∫ θ, Real.log ‖g θ‖ ∂angularMeasure := by
  have hrang : ∀ᵐ θ ∂angularMeasure,
      Tendsto (fun r : ℝ ↦ f (circleMap 0 r θ)) (𝓝[<] 1) (𝓝 (g θ)) :=
    ae_restrict_of_ae hradial
  obtain ⟨r, hrl, hru, hrt⟩ := exists_radial_sequence_above (by norm_num : (1 / 2 : ℝ) < 1)
  have hseq : ∀ᵐ θ ∂angularMeasure,
      Tendsto (fun n ↦ f (circleMap 0 (r n) θ)) atTop (𝓝 (g θ)) :=
    hrang.mono (fun _ hθ ↦ hθ.comp hrt)
  obtain ⟨_, hi, hzero⟩ := disk_boundary_log_integrable_of_radial_sequence hf hne hbound r
    (by norm_num : (0 : ℝ) < 1 / 2) hrl hru hseq
  have hgb : ∀ᵐ θ ∂angularMeasure, ‖g θ‖ ≤ 1 := by
    filter_upwards [hseq] with θ hθ
    apply le_of_tendsto hθ.norm
    apply Eventually.of_forall
    intro n
    apply hbound
    apply Metric.sphere_subset_ball _ (circleMap_mem_sphere' _ _ _)
    rw [abs_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hrl n))]
    exact hru n
  refine ⟨hi, hzero, ?_⟩
  intro s hs hs1
  obtain ⟨r', hr'l, hr'u, hr't⟩ := exists_radial_sequence_above hs1
  have hseq' : ∀ᵐ θ ∂angularMeasure,
      Tendsto (fun n ↦ f (circleMap 0 (r' n) θ)) atTop (𝓝 (g θ)) :=
    hrang.mono (fun _ hθ ↦ hθ.comp hr't)
  obtain ⟨hfatou, _, _⟩ := disk_boundary_log_integrable_of_radial_sequence hf hne hbound r'
    hs hr'l hr'u hseq'
  have hsub : Metric.sphere (0 : ℂ) |s| ⊆ Metric.ball 0 1 :=
    Metric.sphere_subset_ball (by simpa only [abs_of_pos hs] using hs1)
  have hmean : logCircleMean f s ≤ 0 := by
    apply Real.circleAverage_mono_on_of_le_circle
      ((hf.analyticOnNhd Metric.isOpen_ball).mono hsub).meromorphicOn.circleIntegrable_log_norm
    intro z hz
    exact Real.log_nonpos (norm_nonneg _) (hbound z (hsub hz))
  exact mean_le_boundary_log_mean hmean hzero hgb hi hfatou

/-- Positive constant rescaling shifts every interior logarithmic mean by the
same real constant; angular zeros are handled by codiscrete equality. -/
theorem logCircleMean_div_pos_const {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hne : ∃ w ∈ Metric.ball 0 1, f w ≠ 0) {C r : ℝ}
    (hC : 0 < C) (hr : 0 < r) (hr1 : r < 1) :
    logCircleMean (fun z ↦ f z / (C : ℂ)) r = logCircleMean f r - Real.log C := by
  have hsub : Metric.sphere (0 : ℂ) |r| ⊆ Metric.ball 0 1 :=
    Metric.sphere_subset_ball (by simpa only [abs_of_pos hr] using hr1)
  have hzero := codiscreteWithin_mono hsub (disk_codiscrete_nonzero hf hne)
  have heq : (fun z ↦ Real.log ‖f z / (C : ℂ)‖) =ᶠ[codiscreteWithin (Metric.sphere 0 |r|)]
      (fun z ↦ Real.log ‖f z‖ - Real.log C) := by
    filter_upwards [hzero] with z hz
    rw [norm_div, Complex.norm_of_nonneg hC.le, Real.log_div (norm_ne_zero_iff.mpr hz) hC.ne']
  rw [logCircleMean, Real.circleAverage_congr_codiscreteWithin heq hr.ne',
    Real.circleAverage_fun_sub
      ((hf.analyticOnNhd Metric.isOpen_ball).mono hsub).meromorphicOn.circleIntegrable_log_norm
      (circleIntegrable_const _ _ _), Real.circleAverage_const]
  rfl

/-- Every bounded nonzero disk function admits a positive normalization to the
closed unit ball without changing its zero set. -/
theorem normalize_bounded_holomorphic {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hne : ∃ w ∈ Metric.ball 0 1, f w ≠ 0)
    (hbounded : ∃ M : ℝ, ∀ z ∈ Metric.ball 0 1, ‖f z‖ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ DifferentiableOn ℂ (fun z ↦ f z / (C : ℂ)) (Metric.ball 0 1) ∧
      (∃ w ∈ Metric.ball 0 1, f w / (C : ℂ) ≠ 0) ∧
      ∀ z ∈ Metric.ball 0 1, ‖f z / (C : ℂ)‖ ≤ 1 := by
  obtain ⟨M, hM⟩ := hbounded
  let C : ℝ := max M 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC0 : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  refine ⟨C, hC, hf.div_const _, ?_, ?_⟩
  · obtain ⟨w, hw, hfw⟩ := hne
    exact ⟨w, hw, div_ne_zero hfw hC0⟩
  · intro z hz
    rw [norm_div, Complex.norm_of_nonneg hC.le, div_le_one hC]
    exact (hM z hz).trans (le_max_left _ _)

#print axioms extendedLogNorm_zero
#print axioms extendedLogNorm_of_ne_zero
#print axioms continuous_extendedLogNorm
#print axioms negativeLogNorm_zero
#print axioms continuous_negativeLogNorm
#print axioms logCircleMean_eq_posLog_divisor_sum
#print axioms logCircleMean_mono_of_center_ne_zero
#print axioms disk_remove_zero_at_origin
#print axioms logCircleMean_eq_posLog_divisor_sum_general
#print axioms logCircleMean_mono
#print axioms disk_logCircleMean_mono
#print axioms exists_small_radius_logCircleMean_formula
#print axioms logCircleMean_tendsto_origin
#print axioms disk_angular_ae_nonzero
#print axioms disk_angular_extendedLogNorm_eq
#print axioms negativeLogNorm_of_ne_zero
#print axioms negativeLogNorm_angular_integral_eq
#print axioms negativeLogNorm_fatou
#print axioms ae_nonzero_of_negativeLogNorm_integral_finite
#print axioms integrable_log_norm_of_negativeLogNorm_finite
#print axioms disk_boundary_log_integrable_of_radial_sequence
#print axioms negativeLogNorm_integral_eq_of_integrable
#print axioms mean_le_boundary_log_mean
#print axioms exists_radial_sequence_above
#print axioms disk_codiscrete_nonzero
#print axioms normalized_log_means_of_radial_limits
#print axioms logCircleMean_div_pos_const
#print axioms normalize_bounded_holomorphic

end RudinRCA.Chapter15
