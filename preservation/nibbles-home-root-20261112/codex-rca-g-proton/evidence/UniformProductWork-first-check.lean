import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

open Filter Finset
open scoped Topology

namespace RudinRCA.Chapter15

/-- The exact uniform-norm-series hypothesis of Rudin 15.4 implies uniform
convergence of the ordered partial products. No summable sup-norm majorant is
assumed, and the underlying set needs no topology. -/
theorem uniform_product_of_uniform_norm_series {S : Type*}
    (u : ℕ → S → ℂ) (A : S → ℝ)
    (hbdd : ∀ n, ∃ C : ℝ, ∀ s, ‖u n s‖ ≤ C)
    (hconv : TendstoUniformly (fun N s ↦ ∑ n ∈ range N, ‖u n s‖) A atTop) :
    TendstoUniformly (fun N s ↦ ∏ n ∈ range N, (1 + u n s))
      (fun s ↦ ∏' n, (1 + u n s)) atTop := by
  classical
  let P (N : ℕ) (s : S) : ℂ := ∏ n ∈ range N, (1 + u n s)
  let V (N : ℕ) (s : S) : ℝ := ∑ n ∈ range N, ‖u n s‖
  have hsum (s : S) : HasSum (fun n ↦ ‖u n s‖) (A s) :=
    (hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ norm_nonneg (u n s)) (A s)).2
      (hconv.tendsto_at s)
  have hV (N : ℕ) (s : S) : V N s ≤ A s := by
    simpa [V, (hsum s).tsum_eq] using
      (hsum s).summable.sum_le_tsum (range N) (fun n _ ↦ norm_nonneg (u n s))
  have hmul (s : S) : Multipliable (fun n ↦ 1 + u n s) :=
    multipliable_one_add_of_summable (hsum s).summable
  choose C hC using hbdd
  obtain ⟨N₀, hN₀⟩ :=
    (Metric.tendstoUniformly_iff.1 hconv 1 (by norm_num)).exists
  let B : ℝ := (∑ n ∈ range N₀, C n) + 1
  have hA (s : S) : A s ≤ B := by
    have hc : V N₀ s ≤ ∑ n ∈ range N₀, C n := sum_le_sum (fun n _ ↦ hC n s)
    have hd : |A s - V N₀ s| < 1 := by simpa [Real.dist_eq, V] using hN₀ s
    have := (abs_lt.1 hd).2
    dsimp [B]
    linarith
  have hP (N : ℕ) (s : S) : ‖P N s‖ ≤ Real.exp B := by
    calc
      ‖P N s‖ ≤ ∏ n ∈ range N, ‖1 + u n s‖ := norm_prod_le _ _
      _ ≤ ∏ n ∈ range N, (1 + ‖u n s‖) :=
        prod_le_prod₀ (fun n _ ↦ norm_nonneg _) (fun n _ ↦ by
          simpa using norm_add_le (1 : ℂ) (u n s))
      _ ≤ Real.exp (V N s) := Real.prod_one_add_le_exp_sum _ (fun n ↦ norm_nonneg _)
      _ ≤ Real.exp B := Real.exp_le_exp.mpr ((hV N s).trans (hA s))
  have htail (n m : ℕ) (hnm : n ≤ m) (s : S) :
      (∑ i ∈ Ico n m, ‖u i s‖) ≤ A s - V n s := by
    have heq := sum_range_add_sum_Ico (fun i ↦ ‖u i s‖) hnm
    have hm := hV m s
    change V n s + _ = V m s at heq
    linarith
  have hdiff (n m : ℕ) (hnm : n ≤ m) (s : S) :
      ‖P m s - P n s‖ ≤ Real.exp B * (Real.exp (A s - V n s) - 1) := by
    calc
      ‖P m s - P n s‖ =
          ‖P n s * ((∏ i ∈ Ico n m, (1 + u i s)) - 1)‖ := by
        dsimp [P]
        rw [← prod_range_mul_prod_Ico (fun i ↦ 1 + u i s) hnm]
        congr 1
        ring
      _ ≤ ‖P n s‖ * ‖(∏ i ∈ Ico n m, (1 + u i s)) - 1‖ := norm_mul_le _ _
      _ ≤ Real.exp B * (Real.exp (∑ i ∈ Ico n m, ‖u i s‖) - 1) :=
        mul_le_mul (hP n s) ((Ico n m).norm_prod_one_add_sub_one_le (fun i ↦ u i s))
          (norm_nonneg _) (Real.exp_nonneg _)
      _ ≤ Real.exp B * (Real.exp (A s - V n s) - 1) :=
        mul_le_mul_of_nonneg_left
          (sub_le_sub_right (Real.exp_le_exp.mpr (htail n m hnm s)) 1) (Real.exp_nonneg _)
  have hlimit (n : ℕ) (s : S) :
      ‖(∏' i, (1 + u i s)) - P n s‖ ≤
        Real.exp B * (Real.exp (A s - V n s) - 1) := by
    apply le_of_tendsto (((hmul s).tendsto_prod_tprod_nat).sub_const (P n s)).norm
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hdiff n m hm s
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  let δ : ℝ := min 1 (ε / (2 * Real.exp B))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  filter_upwards [Metric.tendstoUniformly_iff.1 hconv δ hδ] with n hn s
  have ht0 : 0 ≤ A s - V n s := sub_nonneg.mpr (hV n s)
  have htδ : A s - V n s < δ := by
    have := hn s
    simpa [Real.dist_eq, V, abs_of_nonneg ht0] using this
  have ht1 : |A s - V n s| ≤ 1 := by
    rw [abs_of_nonneg ht0]
    exact htδ.le.trans (min_le_left _ _)
  have hexp : Real.exp (A s - V n s) - 1 ≤ 2 * (A s - V n s) := by
    exact (le_abs_self _).trans (by
      simpa [abs_of_nonneg ht0] using Real.abs_exp_sub_one_le ht1)
  have hsmall : Real.exp B * (2 * (A s - V n s)) < ε := by
    have ht := lt_of_lt_of_le htδ (min_le_right 1 (ε / (2 * Real.exp B)))
    have hp : 0 < 2 * Real.exp B := by positivity
    have hm := (lt_div_iff₀ hp).1 ht
    nlinarith
  change dist (∏' i, (1 + u i s)) (P n s) < ε
  rw [dist_eq_norm]
  exact (hlimit n s).trans_lt
    ((mul_le_mul_of_nonneg_left hexp (Real.exp_nonneg _)).trans_lt hsmall)

/-- Set-restricted form of the exact uniform product theorem 15.4. -/
theorem uniform_productOn_of_uniform_norm_series {S : Type*}
    (u : ℕ → S → ℂ) (A : S → ℝ) (K : Set S)
    (hbdd : ∀ n, ∃ C : ℝ, ∀ s ∈ K, ‖u n s‖ ≤ C)
    (hconv : TendstoUniformlyOn (fun N s ↦ ∑ n ∈ range N, ‖u n s‖) A atTop K) :
    TendstoUniformlyOn (fun N s ↦ ∏ n ∈ range N, (1 + u n s))
      (fun s ↦ ∏' n, (1 + u n s)) atTop K := by
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe] at hconv ⊢
  apply uniform_product_of_uniform_norm_series (fun n (s : K) ↦ u n s) (fun s ↦ A s)
  · intro n
    obtain ⟨C, hC⟩ := hbdd n
    exact ⟨C, fun s ↦ hC s s.property⟩
  · exact hconv

/-- The zero-set assertion of 15.4 under its exact norm-series hypothesis. -/
theorem product_eq_zero_iff_of_uniform_norm_series {S : Type*}
    (u : ℕ → S → ℂ) (A : S → ℝ)
    (hconv : TendstoUniformly (fun N s ↦ ∑ n ∈ range N, ‖u n s‖) A atTop)
    (s : S) : (∏' n, (1 + u n s)) = 0 ↔ ∃ n, u n s = -1 := by
  have hsum : Summable (fun n ↦ ‖u n s‖) :=
    ((hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ norm_nonneg (u n s)) (A s)).2
      (hconv.tendsto_at s)).summable
  constructor
  · contrapose!
    intro h
    apply tprod_one_add_ne_zero_of_summable _ hsum
    intro n
    have := h n
    exact fun heq ↦ this (by linear_combination heq)
  · rintro ⟨n, hn⟩
    exact tprod_of_exists_eq_zero ⟨n, by simp [hn]⟩

/-- Uniform convergence of a nonnegative series is unchanged by a permutation.
This uses finite-set inclusion, not a summable bound for the sup norms. -/
theorem uniform_norm_series_reindex {S : Type*}
    (u : ℕ → S → ℂ) (A : S → ℝ) (e : ℕ ≃ ℕ)
    (hconv : TendstoUniformly (fun N s ↦ ∑ n ∈ range N, ‖u n s‖) A atTop) :
    TendstoUniformly (fun N s ↦ ∑ n ∈ range N, ‖u (e n) s‖) A atTop := by
  classical
  have hsum (s : S) : HasSum (fun n ↦ ‖u n s‖) (A s) :=
    (hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ norm_nonneg (u n s)) (A s)).2
      (hconv.tendsto_at s)
  have hperm (s : S) : HasSum (fun n ↦ ‖u (e n) s‖) (A s) :=
    e.hasSum_iff.2 (hsum s)
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformly_iff.1 hconv ε hε)
  obtain ⟨M, hM⟩ := ((range N).map e.symm.toEmbedding).exists_nat_subset_range
  filter_upwards [eventually_ge_atTop M] with m hm s
  have hupper : (∑ i ∈ range m, ‖u (e i) s‖) ≤ A s := by
    simpa [(hperm s).tsum_eq] using
      (hperm s).summable.sum_le_tsum (range m) (fun i _ ↦ norm_nonneg (u (e i) s))
  have hlower : (∑ i ∈ range N, ‖u i s‖) ≤ ∑ i ∈ range m, ‖u (e i) s‖ := by
    calc
      (∑ i ∈ range N, ‖u i s‖) =
          ∑ i ∈ (range N).map e.symm.toEmbedding, ‖u (e i) s‖ := by simp
      _ ≤ ∑ i ∈ range m, ‖u (e i) s‖ :=
        sum_le_sum_of_subset_of_nonneg (hM.trans (range_mono hm)) (fun i _ _ ↦ norm_nonneg _)
  have hbound : A s - (∑ i ∈ range N, ‖u i s‖) < ε :=
    (le_abs_self _).trans_lt (by simpa [Real.dist_eq] using hN N le_rfl s)
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hupper)]
  linarith

/-- All permutations have the same uniform product limit in Theorem 15.4. -/
theorem uniform_product_reindex_of_uniform_norm_series {S : Type*}
    (u : ℕ → S → ℂ) (A : S → ℝ) (e : ℕ ≃ ℕ)
    (hbdd : ∀ n, ∃ C : ℝ, ∀ s, ‖u n s‖ ≤ C)
    (hconv : TendstoUniformly (fun N s ↦ ∑ n ∈ range N, ‖u n s‖) A atTop) :
    TendstoUniformly (fun N s ↦ ∏ n ∈ range N, (1 + u (e n) s))
      (fun s ↦ ∏' n, (1 + u n s)) atTop := by
  have h := uniform_product_of_uniform_norm_series (fun n s ↦ u (e n) s) A
    (fun n ↦ hbdd (e n)) (uniform_norm_series_reindex u A e hconv)
  have heq : (fun s ↦ ∏' n, (1 + u (e n) s)) =
      (fun s ↦ ∏' n, (1 + u n s)) :=
    funext fun s ↦ e.tprod_eq (fun n ↦ 1 + u n s)
  exact heq ▸ h

/-- Reindexing preserves the pointwise product in 15.4. The uniform convergence
claim for the reordered partial products is proved separately. -/
theorem product_reindex {S : Type*} (u : ℕ → S → ℂ) (e : ℕ ≃ ℕ) (s : S) :
    (∏' n, (1 + u (e n) s)) = ∏' n, (1 + u n s) :=
  e.tprod_eq (fun n ↦ 1 + u n s)

#print axioms uniform_product_of_uniform_norm_series
#print axioms uniform_productOn_of_uniform_norm_series
#print axioms product_eq_zero_iff_of_uniform_norm_series
#print axioms uniform_norm_series_reindex
#print axioms uniform_product_reindex_of_uniform_norm_series
#print axioms product_reindex

end RudinRCA.Chapter15
