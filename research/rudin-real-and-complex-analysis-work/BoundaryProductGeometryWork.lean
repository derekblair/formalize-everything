import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
Geometry for the normalized proof of Rudin 15.11.

After a point of the domain outside the zero set is moved to infinity, the
finite zero sequence is bounded and the omitted set C is compact. The first
lemma extracts convergence of the nearest-boundary distance from escape from
compact subsets. The remaining lemmas give one-half ratio bounds on compact
plane sets and on a fixed infinity-chart disc. These are the geometric inputs
for the elementary-factor estimate 15.8 and holomorphic product theorem 15.6.

This draft is not a completed prescribed-zero existence theorem.
-/

noncomputable section

open Filter Set Metric Bornology
open scoped Topology

namespace RudinRCA.Chapter15

/-- A bounded zero sequence escaping every compact subset of the domain must
approach its closed complement. Compactness of the complement is not needed
for this particular implication. -/
theorem infDist_tendsto_zero_of_bounded_escape (a : ℕ → ℂ) (C : Set ℂ)
    (R : ℝ) (hbound : ∀ n, ‖a n‖ ≤ R)
    (hescape : ∀ K : Set ℂ, IsCompact K → K ⊆ Cᶜ →
      ∀ᶠ n in atTop, a n ∉ K) :
    Tendsto (fun n ↦ infDist (a n) C) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro r hr
    exact Eventually.of_forall (fun n ↦ hr.trans_le infDist_nonneg)
  · intro ε hε
    let K : Set ℂ := closedBall 0 R ∩ {z | ε ≤ infDist z C}
    have hK : IsCompact K :=
      (isCompact_closedBall 0 R).inter_right
        (isClosed_le continuous_const (continuous_infDist_pt C))
    have hKC : K ⊆ Cᶜ := by
      intro z hz hzin
      have h := hz.2
      rw [infDist_zero_of_mem hzin] at h
      exact (not_le_of_gt hε) h
    filter_upwards [hescape K hK hKC] with n hn
    apply lt_of_not_ge
    intro h
    exact hn ⟨by simpa only [mem_closedBall, dist_zero_right] using hbound n, h⟩

/-- A nearest-point choice gives an actual small complex difference. -/
theorem nearest_boundary_difference_tendsto_zero (a b : ℕ → ℂ) (C : Set ℂ)
    (hnearest : ∀ n, infDist (a n) C = dist (a n) (b n))
    (h : Tendsto (fun n ↦ infDist (a n) C) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0) := by
  simpa only [hnearest, dist_eq_norm] using h

/-- Uniform positive distance from a compact set to a disjoint nonempty closed set. -/
theorem compact_infDist_lower_bound {C K : Set ℂ} (hC : IsClosed C)
    (hCne : C.Nonempty) (hK : IsCompact K) (hKC : K ⊆ Cᶜ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, δ ≤ infDist z C := by
  apply hK.exists_forall_le' (continuous_infDist_pt C).continuousOn
  intro z hz
  exact (hC.notMem_iff_infDist_pos hCne).1 (hKC hz)

/-- The pole factors' arguments eventually have norm at most one half on every
compact subset of the domain. -/
theorem boundary_ratios_small_on_compact (a b : ℕ → ℂ) {C K : Set ℂ}
    (hC : IsClosed C) (hCne : C.Nonempty) (hb : ∀ n, b n ∈ C)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0))
    (hK : IsCompact K) (hKC : K ⊆ Cᶜ) :
    ∀ᶠ n in atTop, ∀ z ∈ K, ‖(a n - b n) / (z - b n)‖ ≤ (1 / 2 : ℝ) := by
  obtain ⟨δ, hδ, hδK⟩ := compact_infDist_lower_bound hC hCne hK hKC
  filter_upwards [(tendsto_order.1 hsmall).2 (δ / 2) (half_pos hδ)] with n hn
  intro z hz
  have hden : δ ≤ ‖z - b n‖ :=
    (hδK z hz).trans (by simpa only [dist_eq_norm] using infDist_le_dist_of_mem (hb n))
  rw [norm_div, div_le_iff₀ (hδ.trans_le hden)]
  linarith

/-- A uniform pole bound supplies a single infinity-chart disc on which all
denominators are nonzero. -/
theorem exists_infinity_disc_denominator_lower_bound (b : ℕ → ℂ)
    (B : ℝ) (hB : 0 < B) (hb : ∀ n, ‖b n‖ ≤ B) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ n (w : ℂ), ‖w‖ ≤ ρ → (1 / 2 : ℝ) ≤ ‖1 - b n * w‖ := by
  let ρ : ℝ := min 1 (1 / (2 * B))
  have hρ : 0 < ρ := lt_min zero_lt_one (one_div_pos.2 (by positivity))
  refine ⟨ρ, hρ, min_le_left _ _, ?_⟩
  intro n w hw
  have hmul : ‖b n * w‖ ≤ (1 / 2 : ℝ) := by
    calc
      ‖b n * w‖ = ‖b n‖ * ‖w‖ := norm_mul _ _
      _ ≤ B * (1 / (2 * B)) :=
        mul_le_mul (hb n) (hw.trans (min_le_right _ _)) (norm_nonneg _) hB.le
      _ = 1 / 2 := by field_simp [hB.ne']
  have h := norm_sub_norm_le (1 : ℂ) (b n * w)
  norm_num only [norm_one] at h
  linarith

/-- The same one-half ratio estimate holds on a fixed neighborhood of infinity,
using its actual local coordinate w=1/z and the exact rational expression. -/
theorem boundary_ratios_small_at_infinity (a b : ℕ → ℂ)
    (B : ℝ) (hB : 0 < B) (hb : ∀ n, ‖b n‖ ≤ B)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ n (w : ℂ), ‖w‖ ≤ ρ → 1 - b n * w ≠ 0) ∧
      (∀ᶠ n in atTop, ∀ w : ℂ, ‖w‖ ≤ ρ →
        ‖(a n - b n) * w / (1 - b n * w)‖ ≤ (1 / 2 : ℝ)) := by
  obtain ⟨ρ, hρ, hρ1, hden⟩ :=
    exists_infinity_disc_denominator_lower_bound b B hB hb
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro n w hw hzero
    have h := hden n w hw
    simpa [hzero] using h
  · filter_upwards [(tendsto_order.1 hsmall).2 (1 / 4) (by norm_num)] with n hn
    intro w hw
    have hd := hden n w hw
    have hdpos : 0 < ‖1 - b n * w‖ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hd
    rw [norm_div, div_le_iff₀ hdpos, norm_mul]
    have hnum : ‖a n - b n‖ * ‖w‖ ≤ (1 / 4 : ℝ) := by
      calc
        ‖a n - b n‖ * ‖w‖ ≤ (1 / 4 : ℝ) * 1 :=
          mul_le_mul hn.le (hw.trans hρ1) (norm_nonneg _) (by norm_num)
        _ = 1 / 4 := mul_one _
    linarith

#print axioms infDist_tendsto_zero_of_bounded_escape
#print axioms nearest_boundary_difference_tendsto_zero
#print axioms boundary_ratios_small_on_compact
#print axioms exists_infinity_disc_denominator_lower_bound
#print axioms boundary_ratios_small_at_infinity

end RudinRCA.Chapter15
