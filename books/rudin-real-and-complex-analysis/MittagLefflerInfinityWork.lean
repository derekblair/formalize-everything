import MittagLefflerSeriesWork
import Mathlib.Tactic.LinearCombination

/-!
The infinity chart of the explicit Mittag-Leffler series. This is required when
a point of the original domain is moved to infinity by normalization. Every
corrected summand has value zero in this chart at zero, and the same geometric
majorant proves normal convergence on a fixed chart disc.

Draft: awaiting the serialized Lean check.
-/

noncomputable section
open Filter Finset Set Metric
open scoped Topology

namespace RudinRCA.Chapter15

def reciprocalExpansionAtInfinity (N : ℕ) (a b w : ℂ) : ℂ :=
  ∑ k ∈ range N, ((a - b) * w / (1 - b * w)) ^ k * (w / (1 - b * w))

def correctedPrincipalPartAtInfinity (P : Polynomial ℂ) (N : ℕ) (a b w : ℂ) : ℂ :=
  P.eval (w / (1 - a * w)) - P.eval (reciprocalExpansionAtInfinity N a b w)

theorem reciprocal_at_infinity_eq {a w : ℂ} (hw : w ≠ 0) :
    w / (1 - a * w) = 1 / (1 / w - a) := by
  by_cases hd : 1 - a * w = 0
  · have hd' : 1 / w - a = 0 := by
      apply (mul_right_cancel₀ hw)
      field_simp [hw]
      linear_combination hd
    simp [hd, hd']
  · have hd' : 1 / w - a ≠ 0 := by
      intro h
      apply hd
      field_simp [hw] at h
      linear_combination h
    field_simp [hw, hd, hd']

theorem reciprocalExpansionAtInfinity_eq (N : ℕ) (a b : ℂ)
    {w : ℂ} (hw : w ≠ 0) :
    reciprocalExpansionAtInfinity N a b w = reciprocalExpansion N a b (1 / w) := by
  apply Finset.sum_congr rfl
  intro k _
  have hr : (a - b) * w / (1 - b * w) = (a - b) / (1 / w - b) := by
    calc
      (a - b) * w / (1 - b * w) = (a - b) * (w / (1 - b * w)) := by ring
      _ = (a - b) * (1 / (1 / w - b)) := by rw [reciprocal_at_infinity_eq hw]
      _ = (a - b) / (1 / w - b) := by ring
  rw [hr, reciprocal_at_infinity_eq hw]
  ring

theorem correctedPrincipalPartAtInfinity_eq (P : Polynomial ℂ) (N : ℕ)
    (a b : ℂ) {w : ℂ} (hw : w ≠ 0) :
    correctedPrincipalPartAtInfinity P N a b w =
      correctedPrincipalPart P N a b (1 / w) := by
  simp only [correctedPrincipalPartAtInfinity, correctedPrincipalPart,
    reciprocal_at_infinity_eq hw, reciprocalExpansionAtInfinity_eq N a b hw]

@[simp] theorem correctedPrincipalPartAtInfinity_zero
    (P : Polynomial ℂ) (N : ℕ) (a b : ℂ) :
    correctedPrincipalPartAtInfinity P N a b 0 = 0 := by
  simp [correctedPrincipalPartAtInfinity, reciprocalExpansionAtInfinity]

theorem correctedPrincipalPartAtInfinity_analyticAt (P : Polynomial ℂ) (N : ℕ)
    {a b w : ℂ} (ha : 1 - a * w ≠ 0) (hb : 1 - b * w ≠ 0) :
    AnalyticAt ℂ (correctedPrincipalPartAtInfinity P N a b) w := by
  have had : AnalyticAt ℂ (fun v : ℂ ↦ 1 - a * v) w :=
    analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  have hbd : AnalyticAt ℂ (fun v : ℂ ↦ 1 - b * v) w :=
    analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  have htrue : AnalyticAt ℂ (fun v : ℂ ↦ v / (1 - a * v)) w := analyticAt_id.div had ha
  have happ : AnalyticAt ℂ (reciprocalExpansionAtInfinity N a b) w :=
    Finset.analyticAt_fun_sum _ fun k _ ↦
      (((analyticAt_const.mul analyticAt_id).div hbd hb).pow k).mul
        (analyticAt_id.div hbd hb)
  exact (htrue.aeval_polynomial P).sub (happ.aeval_polynomial P)

theorem infinity_exterior_of_small_difference {a b w : ℂ}
    (hw : w ≠ 0) (hw1 : ‖w‖ ≤ 1)
    (hden : (1 / 2 : ℝ) ≤ ‖1 - b * w‖) (hab : ‖a - b‖ ≤ 1 / 4) :
    2 * ‖a - b‖ ≤ ‖1 / w - b‖ := by
  have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have heq : 1 / w - b = (1 - b * w) / w := by field_simp [hw]
  rw [heq, norm_div, le_div_iff₀ hwp]
  have hprod : 2 * ‖a - b‖ * ‖w‖ ≤ 2 * (1 / 4 : ℝ) * 1 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hab (by norm_num)) hw1
      (norm_nonneg _) (by norm_num)
  linarith

/-- The corrected series is analytic in a full neighborhood of infinity. Its
chart value at zero is zero, which makes the normalization point removable. -/
theorem principal_part_series_analytic_at_infinity
    (P : ℕ → Polynomial ℂ) (N : ℕ → ℕ) (a b : ℕ → ℂ)
    (B : ℝ) (hB : 0 < B) (haB : ∀ n, ‖a n‖ ≤ B) (hbB : ∀ n, ‖b n‖ ≤ B)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0))
    (happrox : ∀ n z, 2 * ‖a n - b n‖ ≤ ‖z - b n‖ →
      ‖correctedPrincipalPart (P n) (N n) (a n) (b n) z‖ < (1 / 2 : ℝ) ^ n) :
    let G := fun w ↦ ∑' n, correctedPrincipalPartAtInfinity (P n) (N n) (a n) (b n) w
    AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧
      ∀ w, w ≠ 0 → G w = ∑' n, correctedPrincipalPart (P n) (N n) (a n) (b n) (1 / w) := by
  obtain ⟨ρa, hρa, hρa1, ha⟩ := exists_infinity_disc_denominator_lower_bound a B hB haB
  obtain ⟨ρb, hρb, hρb1, hb⟩ := exists_infinity_disc_denominator_lower_bound b B hB hbB
  let ρ := min ρa ρb
  have hρ : 0 < ρ := lt_min hρa hρb
  have hρ1 : ρ ≤ 1 := (min_le_left _ _).trans hρa1
  have hbound : ∀ᶠ n in atTop, ∀ w ∈ closedBall (0 : ℂ) ρ,
      ‖correctedPrincipalPartAtInfinity (P n) (N n) (a n) (b n) w‖ ≤ (1 / 2 : ℝ) ^ n := by
    filter_upwards [(tendsto_order.mp hsmall).2 (1 / 4) (by norm_num)] with n hn w hw
    have hwρ : ‖w‖ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hw
    by_cases hw0 : w = 0
    · simp [hw0, pow_nonneg]
    · rw [correctedPrincipalPartAtInfinity_eq (P n) (N n) (a n) (b n) hw0]
      exact (happrox n (1 / w) (infinity_exterior_of_small_difference hw0 (hwρ.trans hρ1)
        (hb n w (hwρ.trans (min_le_right _ _))) hn.le)).le
  have hconv := tendstoUniformlyOn_tsum_nat_eventually
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) hbound
  have han : ∀ n, AnalyticOnNhd ℂ
      (correctedPrincipalPartAtInfinity (P n) (N n) (a n) (b n)) (ball 0 ρ) := by
    intro n w hw
    have hwρ : ‖w‖ ≤ ρ := (by simpa only [mem_ball, dist_zero_right] using hw : ‖w‖ < ρ).le
    apply correctedPrincipalPartAtInfinity_analyticAt
    · exact norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 2).trans_le
        (ha n w (hwρ.trans (min_le_left _ _))))
    · exact norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 2).trans_le
        (hb n w (hwρ.trans (min_le_right _ _))))
  have hhol := (hconv.tendstoLocallyUniformlyOn.mono ball_subset_closedBall).differentiableOn
    (Eventually.of_forall fun M ↦ DifferentiableOn.fun_sum
      fun n _ ↦ (han n).differentiableOn) isOpen_ball
  refine ⟨(hhol.analyticOnNhd isOpen_ball) 0 (mem_ball_self hρ), ?_, ?_⟩
  · simp
  · intro w hw
    exact tsum_congr fun n ↦ correctedPrincipalPartAtInfinity_eq (P n) (N n) (a n) (b n) hw

#print axioms reciprocal_at_infinity_eq
#print axioms reciprocalExpansionAtInfinity_eq
#print axioms correctedPrincipalPartAtInfinity_eq
#print axioms correctedPrincipalPartAtInfinity_zero
#print axioms correctedPrincipalPartAtInfinity_analyticAt
#print axioms infinity_exterior_of_small_difference
#print axioms principal_part_series_analytic_at_infinity

end RudinRCA.Chapter15
