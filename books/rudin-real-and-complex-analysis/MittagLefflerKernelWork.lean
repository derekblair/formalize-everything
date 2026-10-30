import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Explicit rational approximations for the Mittag-Leffler construction underlying
15.13. No Runge or Mittag-Leffler existence theorem is assumed. The finite
geometric expansion moves an approximate simple pole from a to the omitted
point b, with a uniform geometric error outside a controlled disc about b.
-/

noncomputable section
open Filter Finset Set Metric
open scoped Topology

namespace RudinRCA.Chapter15

def reciprocalExpansion (N : ℕ) (a b z : ℂ) : ℂ :=
  ∑ k ∈ range N, ((a - b) / (z - b)) ^ k / (z - b)

/-- Exact remainder after replacing a simple pole at a by poles at b. -/
theorem reciprocalExpansion_error (N : ℕ) (a b z : ℂ)
    (hza : z ≠ a) (hzb : z ≠ b) :
    1 / (z - a) - reciprocalExpansion N a b z =
      ((a - b) / (z - b)) ^ N / (z - a) := by
  induction N with
  | zero => simp [reciprocalExpansion]
  | succ N hN =>
    rw [reciprocalExpansion, sum_range_succ]
    change 1 / (z - a) - (reciprocalExpansion N a b z +
      ((a - b) / (z - b)) ^ N / (z - b)) = _
    rw [sub_add_eq_sub_sub, hN, pow_succ]
    field_simp [sub_ne_zero.mpr hza, sub_ne_zero.mpr hzb]
    ring

/-- Every approximant is analytic away from the chosen omitted point. -/
theorem analyticAt_reciprocalExpansion (N : ℕ) (a b : ℂ) {z : ℂ} (hzb : z ≠ b) :
    AnalyticAt ℂ (reciprocalExpansion N a b) z := by
  have hd : AnalyticAt ℂ (fun w : ℂ ↦ w - b) z :=
    analyticAt_id.sub analyticAt_const
  exact Finset.analyticAt_fun_sum _ fun k _ ↦
    ((analyticAt_const.div hd (sub_ne_zero.mpr hzb)).pow k).div hd
      (sub_ne_zero.mpr hzb)

/-- On the exterior disc used by the construction, both the true pole and its
finite expansion stay a definite distance from their singularities. -/
theorem reciprocalExpansion_exterior_geometry {a b z : ℂ} (hab : a ≠ b)
    (hz : 2 * ‖a - b‖ ≤ ‖z - b‖) :
    z ≠ a ∧ z ≠ b ∧ ‖a - b‖ ≤ ‖z - a‖ ∧
      ‖(a - b) / (z - b)‖ ≤ (1 / 2 : ℝ) := by
  have hD : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hden : 0 < ‖z - b‖ := by linarith
  have htri : ‖z - b‖ ≤ ‖z - a‖ + ‖a - b‖ := by
    calc
      ‖z - b‖ = ‖(z - a) + (a - b)‖ := by congr 1; ring
      _ ≤ ‖z - a‖ + ‖a - b‖ := norm_add_le _ _
  have hdist : ‖a - b‖ ≤ ‖z - a‖ := by linarith
  refine ⟨sub_ne_zero.mp (norm_pos_iff.mp (hD.trans_le hdist)),
    sub_ne_zero.mp (norm_pos_iff.mp hden), hdist, ?_⟩
  rw [norm_div, div_le_iff₀ hden]
  linarith

theorem norm_reciprocalExpansion_error_le (N : ℕ) {a b z : ℂ} (hab : a ≠ b)
    (hz : 2 * ‖a - b‖ ≤ ‖z - b‖) :
    ‖1 / (z - a) - reciprocalExpansion N a b z‖ ≤
      (1 / 2 : ℝ) ^ N / ‖a - b‖ := by
  obtain ⟨hza, hzb, hdist, hratio⟩ := reciprocalExpansion_exterior_geometry hab hz
  have hD : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  rw [reciprocalExpansion_error N a b z hza hzb, norm_div, norm_pow]
  calc
    ‖(a - b) / (z - b)‖ ^ N / ‖z - a‖ ≤ (1 / 2 : ℝ) ^ N / ‖z - a‖ :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hratio N) (norm_nonneg _)
    _ ≤ (1 / 2 : ℝ) ^ N / ‖a - b‖ :=
      div_le_div_of_nonneg_left (pow_nonneg (by norm_num) _) hD hdist

/-- Uniform simple-pole approximation on the whole exterior region, rather than
only on a particular compact set. -/
theorem reciprocalExpansion_tendstoUniformlyOn {a b : ℂ} (hab : a ≠ b) :
    TendstoUniformlyOn (fun N z ↦ reciprocalExpansion N a b z)
      (fun z ↦ 1 / (z - a)) atTop {z : ℂ | 2 * ‖a - b‖ ≤ ‖z - b‖} := by
  have hlim : Tendsto (fun N : ℕ ↦ (1 / 2 : ℝ) ^ N / ‖a - b‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).div_const ‖a - b‖
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with N hN z hz
  rw [dist_eq_norm]
  exact (norm_reciprocalExpansion_error_le N hab hz).trans_lt hN

theorem reciprocalExpansion_uniform_bounds (N : ℕ) {a b z : ℂ} (hab : a ≠ b)
    (hz : 2 * ‖a - b‖ ≤ ‖z - b‖) :
    ‖1 / (z - a)‖ ≤ 2 / ‖a - b‖ ∧
      ‖reciprocalExpansion N a b z‖ ≤ 2 / ‖a - b‖ := by
  have hD : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hdist := (reciprocalExpansion_exterior_geometry hab hz).2.2.1
  have hinv : ‖1 / (z - a)‖ ≤ 1 / ‖a - b‖ := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hD hdist
  have herr : ‖1 / (z - a) - reciprocalExpansion N a b z‖ ≤ 1 / ‖a - b‖ :=
    (norm_reciprocalExpansion_error_le N hab hz).trans
      (div_le_div_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) hD.le)
  constructor
  · exact hinv.trans (div_le_div_of_nonneg_right (by norm_num) hD.le)
  · calc
      ‖reciprocalExpansion N a b z‖ =
          ‖(reciprocalExpansion N a b z - 1 / (z - a)) + 1 / (z - a)‖ := by
            congr 1; ring
      _ ≤ ‖reciprocalExpansion N a b z - 1 / (z - a)‖ + ‖1 / (z - a)‖ := norm_add_le _ _
      _ ≤ 1 / ‖a - b‖ + 1 / ‖a - b‖ := by
        rw [norm_sub_rev]
        exact add_le_add herr hinv
      _ = 2 / ‖a - b‖ := by ring

/-- Every finite principal-part polynomial has an arbitrarily accurate rational
approximation with poles only at b. This is the approximation step needed in the
direct Mittag-Leffler series; it does not assume a global approximation theorem. -/
theorem exists_polynomial_reciprocal_approximation (P : Polynomial ℂ)
    {a b : ℂ} (hab : a ≠ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ z : ℂ, 2 * ‖a - b‖ ≤ ‖z - b‖ →
      ‖P.eval (1 / (z - a)) - P.eval (reciprocalExpansion N a b z)‖ < ε := by
  have huc : UniformContinuousOn P.eval (closedBall 0 (2 / ‖a - b‖)) :=
    (isCompact_closedBall (0 : ℂ) (2 / ‖a - b‖)).uniformContinuousOn_of_continuous P.continuousOn
  obtain ⟨δ, hδ, hdist⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.mp
    (reciprocalExpansion_tendstoUniformlyOn hab) δ hδ).exists
  refine ⟨N, fun z hz ↦ ?_⟩
  obtain ⟨htrue, happ⟩ := reciprocalExpansion_uniform_bounds N hab hz
  have htrue' : 1 / (z - a) ∈ closedBall 0 (2 / ‖a - b‖) := by
    simpa only [mem_closedBall, dist_zero_right] using htrue
  have happ' : reciprocalExpansion N a b z ∈ closedBall 0 (2 / ‖a - b‖) := by
    simpa only [mem_closedBall, dist_zero_right] using happ
  simpa only [dist_eq_norm] using hdist _ htrue' _ happ' (hN z hz)

#print axioms reciprocalExpansion_error
#print axioms analyticAt_reciprocalExpansion
#print axioms reciprocalExpansion_exterior_geometry
#print axioms norm_reciprocalExpansion_error_le
#print axioms reciprocalExpansion_tendstoUniformlyOn
#print axioms reciprocalExpansion_uniform_bounds
#print axioms exists_polynomial_reciprocal_approximation

end RudinRCA.Chapter15
