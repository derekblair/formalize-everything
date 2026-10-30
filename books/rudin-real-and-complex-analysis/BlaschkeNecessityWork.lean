import NevanlinnaWork
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

noncomputable section

open Filter Metric Real Set
open scoped Topology

namespace RudinRCA.Chapter15.BlaschkeNecessityWork

theorem divisor_eq_analyticOrderNatAt {f : ℂ → ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) {z : ℂ} (hz : z ∈ closedBall 0 r) :
    MeromorphicOn.divisor f (closedBall 0 r) z = (analyticOrderNatAt f z : ℤ) := by
  rw [hf.divisor_apply hz]
  by_cases ht : analyticOrderAt f z = ⊤
  · simp [analyticOrderNatAt, ht]
  · rw [← Nat.cast_analyticOrderNatAt ht]
    simp

/-- A finite list may use each zero at most its actual multiplicity. -/
def CountsAtMostOrders (f : ℂ → ℂ) (a : ℕ → ℂ) : Prop := by
  classical
  exact ∀ z ∈ ball (0 : ℂ) 1, ∀ s : Finset ℕ,
    (s.filter fun n ↦ a n = z).card ≤ analyticOrderNatAt f z

theorem countsAtMostOrders_of_hasSum {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hcount : ∀ z ∈ ball (0 : ℂ) 1,
      HasSum (fun n ↦ if a n = z then (1 : ℕ) else 0) (analyticOrderNatAt f z)) :
    CountsAtMostOrders f a := by
  classical
  intro z hz s
  simpa only [Finset.sum_boole] using
    sum_le_hasSum s (fun n _ ↦ Nat.zero_le _) (hcount z hz)

theorem finite_fiber_weight_sum (s : Finset ℕ) (a : ℕ → ℂ) (w : ℂ → ℝ) :
    ∑ᶠ z, ((s.filter fun n ↦ a n = z).card : ℝ) * w z = ∑ n ∈ s, w (a n) := by
  classical
  have heq (z : ℂ) : (∑ n ∈ s.filter (fun n ↦ a n = z), w (a n)) =
      ((s.filter fun n ↦ a n = z).card : ℝ) * w z := by
    calc
      (∑ n ∈ s.filter (fun n ↦ a n = z), w (a n)) =
          ∑ n ∈ s.filter (fun n ↦ a n = z), w z := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [(Finset.mem_filter.mp hn).2]
      _ = _ := by simp [nsmul_eq_mul]
  simpa only [heq] using finsum_sum_filter a s (fun n ↦ w (a n))

/-- Jensen's sum dominates every finite list that respects zero multiplicities. -/
theorem finite_zero_log_sum_le_jensen {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hc : CountsAtMostOrders f a)
    (s : Finset ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (har : ∀ n ∈ s, ‖a n‖ ≤ r) :
    ∑ n ∈ s, Real.log (r / ‖a n‖) ≤
      ∑ᶠ z, (MeromorphicOn.divisor f (closedBall 0 r) z : ℝ) * Real.log (r / ‖z‖) := by
  classical
  have hA : AnalyticOnNhd ℂ f (closedBall 0 r) :=
    (hf.analyticOnNhd isOpen_ball).mono (closedBall_subset_ball hr1)
  let b : ℂ → ℝ := fun z ↦ ((s.filter fun n ↦ a n = z).card : ℝ)
  let d := MeromorphicOn.divisor f (closedBall 0 r)
  let w : ℂ → ℝ := fun z ↦ Real.log (r / ‖z‖)
  have hbfin : b.support.Finite := by
    apply (s.finite_toSet.image a).subset
    intro z hz
    by_contra h
    have hz0 : (s.filter fun n ↦ a n = z) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro n hn heq
      exact h ⟨n, hn, heq⟩
    exact hz (by simp [b, hz0])
  have hdfin : (fun z ↦ (d z : ℝ)).support.Finite := by
    apply (d.finiteSupport (isCompact_closedBall 0 r)).subset
    intro z hz hdz
    exact hz (by simp [hdz])
  rw [← finite_fiber_weight_sum s a w]
  apply finsum_le_finsum (hbfin.subset (Function.support_mul_subset_left _ _))
    (hdfin.subset (Function.support_mul_subset_left _ _))
  intro z
  by_cases hz : z ∈ closedBall (0 : ℂ) r
  · have hzU : z ∈ ball (0 : ℂ) 1 := (closedBall_subset_ball hr1) hz
    have hbd : b z ≤ d z := by
      dsimp [b, d]
      rw [divisor_eq_analyticOrderNatAt hA hz]
      exact_mod_cast hc z hzU s
    have hw : 0 ≤ w z := by
      dsimp [w]
      by_cases hz0 : z = 0
      · simp [hz0]
      · apply Real.log_nonneg
        exact (le_div_iff₀ (norm_pos_iff.mpr hz0)).mpr (by simpa using hz)
    exact mul_le_mul_of_nonneg_right hbd hw
  · have hb0 : b z = 0 := by
      dsimp [b]
      have he : s.filter (fun n ↦ a n = z) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro n hn heq
        apply hz
        simpa [← heq] using har n hn
      simp [he]
    have hd0 : d z = 0 := Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz
    simp [hb0, hd0]

/-- A uniform upper bound for Jensen's non-origin zero sum on `1/2 ≤ r < 1`. -/
theorem nevanlinna_jensen_sum_le {f : ℂ → ℂ} (hf : NevanlinnaClass f)
    {M : ℝ} (hM : ∀ r ∈ Ioo (0 : ℝ) 1,
      circleAverage (fun z ↦ Real.posLog ‖f z‖) 0 r ≤ M)
    {r : ℝ} (hrhalf : (1 / 2 : ℝ) ≤ r) (hr1 : r < 1) :
    (∑ᶠ z, (MeromorphicOn.divisor f (closedBall 0 r) z : ℝ) * Real.log (r / ‖z‖)) ≤
      M + (analyticOrderNatAt f 0 : ℝ) * Real.log 2 - Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have hr0 : 0 < r := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hrhalf
  have hA : AnalyticOnNhd ℂ f (closedBall 0 r) :=
    (hf.1.analyticOnNhd isOpen_ball).mono (closedBall_subset_ball hr1)
  have hAr : AnalyticOnNhd ℂ f (closedBall 0 |r|) := by simpa [abs_of_pos hr0] using hA
  have hj := hAr.meromorphicOn.circleAverage_log_norm hr0.ne'
  simp only [abs_of_pos hr0, zero_sub, norm_neg, ← div_eq_mul_inv] at hj
  have hlogmean : circleAverage (fun z ↦ Real.log ‖f z‖) 0 r ≤ M := by
    apply le_trans _ (hM r ⟨hr0, hr1⟩)
    apply circleAverage_mono (hAr.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
      (circleIntegrable_posLog_norm hf.1 hr0.le hr1)
    intro z hz
    exact le_max_right _ _
  have hd0 := divisor_eq_analyticOrderNatAt hA (show (0 : ℂ) ∈ closedBall 0 r by simp [hr0.le])
  rw [hd0] at hj
  have hlr : -Real.log 2 ≤ Real.log r := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hrhalf
    simpa only [one_div, Real.log_inv] using h
  have hm := mul_le_mul_of_nonneg_left hlr (Nat.cast_nonneg (analyticOrderNatAt f 0) :
    (0 : ℝ) ≤ analyticOrderNatAt f 0)
  simp only [Int.cast_natCast] at hj
  linarith

/-- Elementary logarithmic lower bound used without passing a circle through a zero. -/
theorem half_one_sub_le_log_ratio {x r : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hr : (1 + x) / 2 ≤ r) (hr1 : r < 1) :
    (1 - x) / 2 ≤ Real.log (r / x) := by
  have hr0 : 0 < r := (by linarith : 0 < (1 + x) / 2).trans_le hr
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hr0 hx)
  rw [inv_div] at h
  have hxr : x ≤ r := by linarith
  have h1 : (1 - x) / 2 ≤ r - x := by linarith
  have h2 : r - x ≤ 1 - x / r := by
    have hmul : (r - x) * r ≤ r - x := mul_le_of_le_one_right (by linarith) hr1.le
    have hdiv := (le_div_iff₀ hr0).mpr hmul
    have heq : (r - x) / r = 1 - x / r := by field_simp; ring
    simpa only [heq] using hdiv
  exact h1.trans (h2.trans h)

theorem exists_radius_for_finite_zeros (s : Finset ℕ) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ < 1) :
    ∃ r : ℝ, (1 / 2 : ℝ) ≤ r ∧ r < 1 ∧ ∀ n ∈ s, (1 + ‖a n‖) / 2 ≤ r := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨3 / 4, by norm_num, by norm_num, by simp⟩
  | @insert n s hn ih =>
    obtain ⟨r, hrhalf, hr1, hsr⟩ := ih
    refine ⟨max r ((1 + ‖a n‖) / 2), hrhalf.trans (le_max_left _ _), ?_, ?_⟩
    · exact max_lt_iff.mpr ⟨hr1, by linarith [ha n]⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact le_max_right _ _
      · exact (hsr j hj).trans (le_max_left _ _)

/-- The Blaschke condition holds for every sequence using each zero no more
often than its analytic multiplicity. No preexisting summability or escape
assumption is used. -/
theorem nevanlinna_blaschke_summable_of_counts {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : NevanlinnaClass f) (ha : ∀ n, ‖a n‖ < 1) (hc : CountsAtMostOrders f a) :
    Summable (fun n ↦ 1 - ‖a n‖) := by
  classical
  obtain ⟨M, hM⟩ := hf.2
  let C : ℝ := M + (analyticOrderNatAt f 0 : ℝ) * Real.log 2 -
    Real.log ‖meromorphicTrailingCoeffAt f 0‖
  have hs : Summable (fun n ↦ if a n = 0 then (0 : ℝ) else 1 - ‖a n‖) := by
    apply summable_of_sum_le (c := 2 * C)
    · intro n
      split_ifs
      · exact le_rfl
      · exact sub_nonneg.mpr (ha n).le
    · intro s
      obtain ⟨r, hrhalf, hr1, har⟩ := exists_radius_for_finite_zeros s ha
      have hr0 : 0 < r := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hrhalf
      have hlogs := (finite_zero_log_sum_le_jensen hf.1 hc s hr0 hr1
        (fun n hn ↦ by have := har n hn; have := ha n; linarith)).trans
        (nevanlinna_jensen_sum_le hf hM hrhalf hr1)
      have hhalf : (∑ n ∈ s, if a n = 0 then (0 : ℝ) else 1 - ‖a n‖) / 2 ≤
          ∑ n ∈ s, Real.log (r / ‖a n‖) := by
        rw [Finset.sum_div]
        apply Finset.sum_le_sum
        intro n hn
        by_cases hn0 : a n = 0
        · simp [hn0]
        · simp only [if_neg hn0]
          exact half_one_sub_le_log_ratio (norm_pos_iff.mpr hn0) (ha n) (har n hn) hr1
      dsimp [C]
      linarith
  have hs0 : Summable (fun n ↦ if a n = 0 then (1 : ℝ) else 0) := by
    apply summable_of_sum_le (c := (analyticOrderNatAt f 0 : ℝ))
    · intro n
      split_ifs <;> norm_num
    · intro s
      have h := hc 0 (by simp) s
      simpa only [Finset.sum_boole] using (show
        ((s.filter fun n ↦ a n = 0).card : ℝ) ≤ analyticOrderNatAt f 0 by exact_mod_cast h)
  have heq : (fun n ↦ 1 - ‖a n‖) =
      (fun n ↦ if a n = 0 then (1 : ℝ) else 0) +
      (fun n ↦ if a n = 0 then (0 : ℝ) else 1 - ‖a n‖) := by
    funext n
    by_cases hn : a n = 0 <;> simp [hn]
  rw [heq]
  exact hs0.add hs

/-- Rudin 15.23 for a complete zero list with actual finite multiplicity sums. -/
theorem nevanlinna_zeros_blaschke {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : NevanlinnaClass f) (ha : ∀ n, ‖a n‖ < 1)
    (hcount : ∀ z ∈ ball (0 : ℂ) 1,
      HasSum (fun n ↦ if a n = z then (1 : ℕ) else 0) (analyticOrderNatAt f z)) :
    Summable (fun n ↦ 1 - ‖a n‖) :=
  nevanlinna_blaschke_summable_of_counts hf ha (countsAtMostOrders_of_hasSum hcount)

/-- Finite and empty zero lists automatically satisfy the same condition. -/
theorem finite_zeros_blaschke {ι : Type*} [Finite ι] (a : ι → ℂ) :
    Summable (fun n ↦ 1 - ‖a n‖) := by
  letI : Fintype ι := Fintype.ofFinite ι
  exact (hasSum_fintype (fun n ↦ 1 - ‖a n‖)).summable

theorem countsAtMostOrders_of_injective_zeros {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hne : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0)
    (ha : Function.Injective a) (haz : ∀ n, f (a n) = 0) : CountsAtMostOrders f a := by
  classical
  obtain ⟨w, hw, hfw⟩ := hne
  have hA := hf.analyticOnNhd isOpen_ball
  have hfinite (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : analyticOrderAt f z ≠ ⊤ :=
    hA.analyticOrderAt_ne_top_of_isPreconnected (convex_ball (0 : ℂ) 1).isPreconnected hw hz
      (by rw [(hA w hw).analyticOrderAt_eq_zero.mpr hfw]; simp)
  intro z hz s
  by_cases hs : (s.filter fun n ↦ a n = z).Nonempty
  · obtain ⟨n, hn⟩ := hs
    have hnz := (Finset.mem_filter.mp hn).2
    have hfz : f z = 0 := by rw [← hnz]; exact haz n
    have ho : 0 < analyticOrderNatAt f z := by
      apply Nat.pos_of_ne_zero
      intro hzero
      have ht := (hA z hz).analyticOrderAt_ne_zero.mpr hfz
      rw [← Nat.cast_analyticOrderNatAt (hfinite z hz), hzero, Nat.cast_zero] at ht
      exact ht rfl
    apply (show (s.filter fun n ↦ a n = z).card ≤ 1 from ?_).trans ho
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact ha ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty, Nat.zero_le]

/-- The uniqueness corollary of 15.23: a non-Blaschke sequence of distinct zeros
forces a Nevanlinna function to vanish throughout the unit disc. -/
theorem nevanlinna_zero_of_non_blaschke {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : NevanlinnaClass f) (haU : ∀ n, ‖a n‖ < 1) (ha : Function.Injective a)
    (haz : ∀ n, f (a n) = 0) (hdiv : ¬ Summable (fun n ↦ 1 - ‖a n‖)) :
    ∀ z ∈ ball (0 : ℂ) 1, f z = 0 := by
  by_contra h
  push_neg at h
  exact hdiv (nevanlinna_blaschke_summable_of_counts hf haU
    (countsAtMostOrders_of_injective_zeros hf.1 h ha haz))

/-- In particular, the same uniqueness conclusion holds for bounded holomorphic functions. -/
theorem boundedHolomorphic_zero_of_non_blaschke {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : BoundedHolomorphic f) (haU : ∀ n, ‖a n‖ < 1) (ha : Function.Injective a)
    (haz : ∀ n, f (a n) = 0) (hdiv : ¬ Summable (fun n ↦ 1 - ‖a n‖)) :
    ∀ z ∈ ball (0 : ℂ) 1, f z = 0 :=
  nevanlinna_zero_of_non_blaschke hf.nevanlinnaClass haU ha haz hdiv

#print axioms divisor_eq_analyticOrderNatAt
#print axioms countsAtMostOrders_of_hasSum
#print axioms finite_fiber_weight_sum
#print axioms finite_zero_log_sum_le_jensen
#print axioms nevanlinna_jensen_sum_le
#print axioms half_one_sub_le_log_ratio
#print axioms exists_radius_for_finite_zeros
#print axioms nevanlinna_blaschke_summable_of_counts
#print axioms nevanlinna_zeros_blaschke
#print axioms finite_zeros_blaschke
#print axioms countsAtMostOrders_of_injective_zeros
#print axioms nevanlinna_zero_of_non_blaschke
#print axioms boundedHolomorphic_zero_of_non_blaschke

end RudinRCA.Chapter15.BlaschkeNecessityWork
