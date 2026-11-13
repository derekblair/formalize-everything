import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.ENat.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.MonotoneConvergence

/-
Rudin, Real and Complex Analysis, Chapter 15

Numbering follows the third edition. The sequential product convention in 15.2
allows zero limits. Coverage is tracked in SCOPING-G.md.
-/


noncomputable section

open Filter Finset
open scoped Topology

namespace RudinRCA.Chapter15

/-- The isolated-zero assertion recalled in 15.1. The hypothesis that the
function is not identically zero also includes nonzero constant functions. -/
theorem zeros_have_no_accumulation {Ω : Set ℂ} {f : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hf : DifferentiableOn ℂ f Ω)
    (hnonzero : ∃ w ∈ Ω, f w ≠ 0) {z : ℂ} (hz : z ∈ Ω) :
    z ∉ closure ({w | f w = 0} \ {z}) := by
  intro hacc
  have hzero := (hf.analyticOnNhd hΩ).eqOn_zero_of_preconnected_of_mem_closure hc hz hacc
  obtain ⟨w, hw, hn⟩ := hnonzero
  exact hn (hzero hw)

/-- The sequential product limit used in Definition 15.2 (zero is allowed).
The book starts indexing at one; here the same sequence is indexed from zero. -/
def HasSequentialProduct {R : Type*} [CommMonoid R] [TopologicalSpace R]
    (f : ℕ → R) (p : R) : Prop :=
  Tendsto (fun n ↦ ∏ k ∈ range n, f k) atTop (𝓝 p)

/-- Definition 15.2: convergence means existence of a limit of partial products. -/
def ProductConverges {R : Type*} [CommMonoid R] [TopologicalSpace R]
    (f : ℕ → R) : Prop := ∃ p, HasSequentialProduct f p

/-- Definition 15.2 explicitly includes products with a zero limit. -/
theorem sequentialProduct_zero : HasSequentialProduct (fun _ : ℕ ↦ (0 : ℂ)) 0 := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hmem : 0 ∈ range n := mem_range.mpr (by omega)
  exact (Finset.prod_eq_zero hmem (by rfl)).symm

/-- An unordered Mathlib product supplies Rudin's sequential limit. -/
theorem HasProd.hasSequentialProduct {R : Type*} [CommMonoid R] [TopologicalSpace R]
    {f : ℕ → R} {p : R} (h : _root_.HasProd f p) : HasSequentialProduct f p :=
  h.tendsto_prod_nat

/-- Theorem 15.3, first estimate: the product of `1 + |uᵢ|` is at most the
exponential of the sum of the absolute values. -/
theorem finite_product_majorant_le_exp {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    (∏ i ∈ s, (1 + ‖u i‖)) ≤ Real.exp (∑ i ∈ s, ‖u i‖) :=
  Real.prod_one_add_le_exp_sum s (fun i ↦ norm_nonneg (u i))

/-- Theorem 15.3, second estimate: subtracting one from the product is bounded
by subtracting one from its nonnegative majorant. -/
theorem norm_finite_product_sub_one_le {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    ‖(∏ i ∈ s, (1 + u i)) - 1‖ ≤ (∏ i ∈ s, (1 + ‖u i‖)) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    calc
      ‖(1 + u a) * (∏ i ∈ s, (1 + u i)) - 1‖ =
          ‖(1 + u a) * ((∏ i ∈ s, (1 + u i)) - 1) + u a‖ := by
            congr 1
            ring
      _ ≤ ‖(1 + u a) * ((∏ i ∈ s, (1 + u i)) - 1)‖ + ‖u a‖ :=
        norm_add_le _ _
      _ = ‖1 + u a‖ * ‖(∏ i ∈ s, (1 + u i)) - 1‖ + ‖u a‖ := by
        rw [Complex.norm_mul]
      _ ≤ (1 + ‖u a‖) * ‖(∏ i ∈ s, (1 + u i)) - 1‖ + ‖u a‖ := by
        apply add_le_add _ le_rfl
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa using norm_add_le (1 : ℂ) (u a)
      _ ≤ (1 + ‖u a‖) * ((∏ i ∈ s, (1 + ‖u i‖)) - 1) + ‖u a‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_left ih (add_nonneg zero_le_one (norm_nonneg _))) le_rfl
      _ = (1 + ‖u a‖) * (∏ i ∈ s, (1 + ‖u i‖)) - 1 := by ring

/-- Theorem 15.3, with the two printed estimates stated together. -/
theorem finite_product_estimates {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    (∏ i ∈ s, (1 + ‖u i‖)) ≤ Real.exp (∑ i ∈ s, ‖u i‖) ∧
      ‖(∏ i ∈ s, (1 + u i)) - 1‖ ≤ (∏ i ∈ s, (1 + ‖u i‖)) - 1 :=
  ⟨finite_product_majorant_le_exp s u, norm_finite_product_sub_one_le s u⟩

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

/-- The convergence assertion in 15.5 also covers divergent sums, when the
product limit can be zero. -/
theorem product_one_sub_converges {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n < 1) :
    ProductConverges (fun n ↦ 1 - u n) := by
  have hanti : Antitone (fun n ↦ ∏ k ∈ range n, (1 - u k)) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [prod_range_succ]
    exact mul_le_of_le_one_right
      (prod_nonneg fun i _ ↦ sub_nonneg.mpr (hu1 i).le) (by linarith [hu n])
  refine ⟨⨅ n, ∏ k ∈ range n, (1 - u k), tendsto_atTop_ciInf hanti ?_⟩
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact prod_nonneg fun i _ ↦ sub_nonneg.mpr (hu1 i).le

/-- Theorem 15.5, with positivity expressed by existence of a positive
sequential product limit, rather than by Mathlib's default value for `tprod`. -/
theorem positive_product_one_sub_iff {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n < 1) :
    (∃ p : ℝ, 0 < p ∧ HasSequentialProduct (fun n ↦ 1 - u n) p) ↔ Summable u := by
  constructor
  · rintro ⟨p, hp, hlim⟩
    have hanti : Antitone (fun n ↦ ∏ k ∈ range n, (1 - u k)) := by
      apply antitone_nat_of_succ_le
      intro n
      rw [prod_range_succ]
      exact mul_le_of_le_one_right
        (prod_nonneg fun i _ ↦ sub_nonneg.mpr (hu1 i).le) (by linarith [hu n])
    apply summable_of_sum_range_le hu (c := -Real.log p)
    intro n
    have hprod : (∏ k ∈ range n, (1 - u k)) ≤ Real.exp (-(∑ k ∈ range n, u k)) := by
      calc
        _ ≤ ∏ k ∈ range n, Real.exp (-u k) :=
          prod_le_prod₀ (fun k _ ↦ sub_nonneg.mpr (hu1 k).le)
            (fun k _ ↦ by simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-u k))
        _ = _ := by rw [← Real.exp_sum, sum_neg_distrib]
    have hlog := (Real.log_le_iff_le_exp hp).2 ((hanti.le_of_tendsto hlim n).trans hprod)
    linarith
  · intro hsum
    have hnorm : Summable (fun n ↦ ‖u n‖) := by simpa [Real.norm_eq_abs, abs_of_nonneg (hu _)] using hsum
    have hmul := multipliable_one_sub_of_summable hnorm
    refine ⟨∏' n, (1 - u n), ?_, HasProd.hasSequentialProduct hmul.hasProd⟩
    have hnonneg : 0 ≤ ∏' n, (1 - u n) := tprod_nonneg (fun n ↦ sub_nonneg.mpr (hu1 n).le)
    have hne : (∏' n, (1 - u n)) ≠ 0 := by
      have hneg : Summable (fun n ↦ ‖-u n‖) := by simpa using hnorm
      simpa [sub_eq_add_neg] using
        (tprod_one_add_ne_zero_of_summable (fun n ↦ by linarith [hu1 n]) hneg)
    exact lt_of_le_of_ne hnonneg hne.symm

/-- Removing finitely many terms preserves the exact uniform-series
convergence hypothesis used by 15.4 and 15.6. -/
theorem uniform_series_tail {S : Type*} (u : ℕ → S → ℝ) (A : S → ℝ)
    (hconv : TendstoUniformly (fun n s ↦ ∑ i ∈ range n, u i s) A atTop)
    (N : ℕ) :
    TendstoUniformly (fun n s ↦ ∑ i ∈ range n, u (i + N) s)
      (fun s ↦ A s - ∑ i ∈ range N, u i s) atTop := by
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  have hshift := (tendsto_add_atTop_nat N).eventually
    (Metric.tendstoUniformly_iff.1 hconv ε hε)
  filter_upwards [hshift] with n hn s
  have hsum : (∑ i ∈ range (n + N), u i s) =
      (∑ i ∈ range N, u i s) + ∑ i ∈ range n, u (i + N) s := by
    simpa [Nat.add_comm] using sum_range_add (fun i ↦ u i s) N n
  have hdist : dist (A s - ∑ i ∈ range N, u i s)
      (∑ i ∈ range n, u (i + N) s) =
      dist (A s) (∑ i ∈ range (n + N), u i s) := by
    rw [Real.dist_eq, Real.dist_eq, hsum]
    congr 1
    ring
  rw [hdist]
  exact hn s

/-- The holomorphic-limit step in Theorem 15.6. -/
theorem holomorphic_of_locally_uniform_products
    {Ω : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hF : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hlim : TendstoLocallyUniformlyOn
      (fun N z ↦ ∏ n ∈ range N, F n z) f atTop Ω) :
    DifferentiableOn ℂ f Ω := by
  apply hlim.differentiableOn _ hΩ
  exact Filter.Eventually.of_forall fun N ↦
    DifferentiableOn.fun_finsetProd fun n _ ↦ hF n

/-- The finite-factor multiplicity calculation used in Theorem 15.6. -/
theorem analyticOrderAt_finset_product {ι : Type*} (s : Finset ι)
    {F : ι → ℂ → ℂ} {z : ℂ} (hF : ∀ n ∈ s, AnalyticAt ℂ (F n) z) :
    analyticOrderAt (fun w ↦ ∏ n ∈ s, F n w) z =
      ∑ n ∈ s, analyticOrderAt (F n) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [analyticOrderAt_eq_zero]
  | @insert a s ha ih =>
    have has : ∀ n ∈ s, AnalyticAt ℂ (F n) z := fun n hn ↦ hF n (mem_insert_of_mem hn)
    have hprod : AnalyticAt ℂ (fun w ↦ ∏ n ∈ s, F n w) z :=
      s.analyticAt_fun_prod has
    simp only [prod_insert ha, sum_insert ha]
    exact (analyticOrderAt_mul (hF a (mem_insert_self a s)) hprod).trans
      (congrArg (fun v ↦ analyticOrderAt (F a) z + v) (ih has))

/-- A nonvanishing analytic tail does not change the order of a finite prefix. -/
theorem analyticOrderAt_product_with_nonzero_tail {F : ℕ → ℂ → ℂ}
    {f tail : ℂ → ℂ} {z : ℂ} (N : ℕ)
    (hF : ∀ n ∈ range N, AnalyticAt ℂ (F n) z)
    (htail : AnalyticAt ℂ tail z) (hne : tail z ≠ 0)
    (hfactor : f =ᶠ[𝓝 z] fun w ↦ (∏ n ∈ range N, F n w) * tail w) :
    analyticOrderAt f z = ∑ n ∈ range N, analyticOrderAt (F n) z := by
  rw [analyticOrderAt_congr hfactor]
  have hprefix : AnalyticAt ℂ (fun w ↦ ∏ n ∈ range N, F n w) z :=
    (range N).analyticAt_fun_prod hF
  rw [show (fun w ↦ (∏ n ∈ range N, F n w) * tail w) =
      (fun w ↦ ∏ n ∈ range N, F n w) * tail from rfl,
    analyticOrderAt_mul hprefix htail,
    htail.analyticOrderAt_eq_zero.mpr hne, add_zero]
  exact analyticOrderAt_finset_product _ hF

/-- A holomorphic function nonzero somewhere on each component has finite
order at every point. This states the component qualification of 15.6 explicitly. -/
theorem analyticOrderAt_ne_top_of_component_nonzero
    {Ω : Set ℂ} {f : ℂ → ℂ} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω)
    (hnonzero : ∀ z ∈ Ω, ∃ w ∈ connectedComponentIn Ω z, f w ≠ 0)
    {z : ℂ} (hz : z ∈ Ω) : analyticOrderAt f z ≠ ⊤ := by
  intro htop
  obtain ⟨w, hw, hfw⟩ := hnonzero z hz
  have han : AnalyticOnNhd ℂ f (connectedComponentIn Ω z) :=
    (hf.analyticOnNhd hΩ).mono (connectedComponentIn_subset Ω z)
  have heq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_connectedComponentIn (mem_connectedComponentIn hz)
    (analyticOrderAt_eq_top.mp htop)
  exact hfw (heq hw)

/-- The multiplicity argument of 15.6 once holomorphicity of all tail products
has been established. The norm-series hypothesis is pointwise here; the full
theorem's local uniform hypothesis supplies this and holomorphic tail products. -/
theorem analyticOrderAt_infinite_product_finite_prefix
    {Ω : Set ℂ} {F : ℕ → ℂ → ℂ} (hΩ : IsOpen Ω)
    (hF : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hsum : ∀ z ∈ Ω, Summable (fun n ↦ ‖F n z - 1‖))
    (htail : ∀ N, DifferentiableOn ℂ (fun z ↦ ∏' n, F (n + N) z) Ω)
    {z : ℂ} (hz : z ∈ Ω) :
    ∃ N, analyticOrderAt (fun w ↦ ∏' n, F n w) z =
        ∑ n ∈ range N, analyticOrderAt (F n) z ∧
      ∀ n, N ≤ n → analyticOrderAt (F n) z = 0 := by
  classical
  have hsmall : ∀ᶠ n in atTop, ‖F n z - 1‖ < 1 :=
    (hsum z hz).tendsto_atTop_zero.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  have hne : ∀ n, N ≤ n → F n z ≠ 0 := by
    intro n hn hzero
    simpa [hzero] using hN n hn
  have hshift : ∀ w ∈ Ω, Summable (fun n ↦ ‖F (n + N) w - 1‖) := by
    intro w hw
    exact (hsum w hw).comp_injective (add_left_injective N)
  have hone : ∀ n w, (1 : ℂ) + (F (n + N) w - 1) = F (n + N) w := by
    intro n w
    ring
  have hmultipliable : ∀ w ∈ Ω, Multipliable (fun n ↦ F (n + N) w) := by
    intro w hw
    simpa only [hone] using multipliable_one_add_of_summable (hshift w hw)
  have htail_ne : (∏' n, F (n + N) z) ≠ 0 := by
    simpa only [hone] using tprod_one_add_ne_zero_of_summable
      (fun n ↦ by rw [hone]; exact hne _ (Nat.le_add_left N n)) (hshift z hz)
  have hfactor : (fun w ↦ ∏' n, F n w) =ᶠ[𝓝 z]
      fun w ↦ (∏ n ∈ range N, F n w) * ∏' n, F (n + N) w := by
    filter_upwards [hΩ.mem_nhds hz] with w hw
    exact ((hmultipliable w hw).hasProd.prod_range_mul).tprod_eq
  refine ⟨N, analyticOrderAt_product_with_nonzero_tail N
    (fun n _ ↦ (hF n).analyticAt (hΩ.mem_nhds hz))
    ((htail N).analyticAt (hΩ.mem_nhds hz)) htail_ne hfactor, ?_⟩
  intro n hn
  exact ((hF n).analyticAt (hΩ.mem_nhds hz)).analyticOrderAt_eq_zero.mpr (hne n hn)

/-- Converts the extended-natural order calculation to Rudin's ordinary
finite multiplicities, using precisely his componentwise nonidentity condition. -/
theorem finite_multiplicity_of_prefix_order
    {Ω : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hΩ : IsOpen Ω)
    (hF : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hnonzero : ∀ n z, z ∈ Ω → ∃ w ∈ connectedComponentIn Ω z, F n w ≠ 0)
    {z : ℂ} (hz : z ∈ Ω) {N : ℕ}
    (horder : analyticOrderAt f z = ∑ n ∈ range N, analyticOrderAt (F n) z) :
    analyticOrderAt f z ≠ ⊤ ∧
      analyticOrderNatAt f z = ∑ n ∈ range N, analyticOrderNatAt (F n) z := by
  have hfinite : ∀ n ∈ range N, analyticOrderAt (F n) z ≠ ⊤ :=
    fun n _ ↦ analyticOrderAt_ne_top_of_component_nonzero hΩ (hF n) (hnonzero n) hz
  constructor
  · rw [horder]
    exact ENat.sum_ne_top.mpr hfinite
  · simpa only [analyticOrderNatAt, horder] using ENat.toNat_sum hfinite

/-- Since all sufficiently late factors have zero multiplicity, the finite
prefix formula is also the ordinary infinite sum formula printed in 15.6. -/
theorem multiplicity_tsum_of_finite_prefix
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {z : ℂ} {N : ℕ}
    (hprefix : analyticOrderNatAt f z = ∑ n ∈ range N, analyticOrderNatAt (F n) z)
    (hzero : ∀ n, N ≤ n → analyticOrderAt (F n) z = 0) :
    analyticOrderNatAt f z = ∑' n, analyticOrderNatAt (F n) z := by
  classical
  rw [tsum_eq_sum (s := range N)]
  · exact hprefix
  · intro n hn
    have hNn : N ≤ n := by simpa only [mem_range, not_lt] using hn
    simp [analyticOrderNatAt, hzero n hNn]

/-- Assembly of the analytic parts of 15.6 from 15.4. The first argument is
exactly the separately established theorem 15.4, not an additional analytic
hypothesis on the factors. A final book-facing wrapper supplies that theorem. -/
theorem holomorphic_product_of_uniform_norm_series_using_15_4
    (h15_4 : ∀ (S : Type) (u : ℕ → S → ℂ) (A : S → ℝ),
      (∀ n, ∃ C : ℝ, ∀ s, ‖u n s‖ ≤ C) →
      TendstoUniformly (fun N s ↦ ∑ n ∈ range N, ‖u n s‖) A atTop →
      TendstoUniformly (fun N s ↦ ∏ n ∈ range N, (1 + u n s))
        (fun s ↦ ∏' n, (1 + u n s)) atTop)
    {Ω : Set ℂ} {F : ℕ → ℂ → ℂ} {A : ℂ → ℝ}
    (hΩ : IsOpen Ω) (hF : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hconv : TendstoLocallyUniformlyOn
      (fun N z ↦ ∑ n ∈ range N, ‖F n z - 1‖) A atTop Ω) :
    TendstoLocallyUniformlyOn (fun N z ↦ ∏ n ∈ range N, F n z)
        (fun z ↦ ∏' n, F n z) atTop Ω ∧
      DifferentiableOn ℂ (fun z ↦ ∏' n, F n z) Ω ∧
      ∀ z ∈ Ω, ∃ N,
        analyticOrderAt (fun w ↦ ∏' n, F n w) z =
          ∑ n ∈ range N, analyticOrderAt (F n) z ∧
        ∀ n, N ≤ n → analyticOrderAt (F n) z = 0 := by
  have hlim (N : ℕ) :
      TendstoLocallyUniformlyOn (fun M z ↦ ∏ n ∈ range M, F (n + N) z)
        (fun z ↦ ∏' n, F (n + N) z) atTop Ω := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).2
    intro K hKΩ hK
    have hKconv := (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).1 hconv K hKΩ hK
    have hsub := tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.1 hKconv
    have hshift := uniform_series_tail (fun n (z : K) ↦ ‖F n z - 1‖)
      (fun z : K ↦ A z) hsub N
    have hbdd : ∀ n, ∃ C : ℝ, ∀ z : K, ‖F (n + N) z - 1‖ ≤ C := by
      intro n
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
        (((hF (n + N)).continuousOn.sub continuousOn_const).mono hKΩ)
      exact ⟨C, fun z ↦ hC z z.property⟩
    have hproduct := h15_4 K (fun n (z : K) ↦ F (n + N) z - 1)
      (fun z : K ↦ A z - ∑ i ∈ range N, ‖F i z - 1‖) hbdd hshift
    have hone (v : ℂ) : 1 + (v - 1) = v := by ring
    apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.2
    simpa only [hone, Function.comp_def] using hproduct
  have hhol (N : ℕ) : DifferentiableOn ℂ (fun z ↦ ∏' n, F (n + N) z) Ω :=
    holomorphic_of_locally_uniform_products hΩ (fun n ↦ hF (n + N)) (hlim N)
  have hsum : ∀ z ∈ Ω, Summable (fun n ↦ ‖F n z - 1‖) := by
    intro z hz
    exact ((hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ norm_nonneg _) (A z)).2
      (hconv.tendsto_at hz)).summable
  refine ⟨by simpa using hlim 0, by simpa using hhol 0, ?_⟩
  intro z hz
  exact analyticOrderAt_infinite_product_finite_prefix hΩ hF hsum hhol hz

/-- Full statement of 15.6, including finite natural-number multiplicities,
assembled from 15.4. The book-facing theorem specializes `h15_4` to the proved
`uniform_product_of_uniform_norm_series`. -/
theorem holomorphic_product_multiplicity_using_15_4
    (h15_4 : ∀ (S : Type) (u : ℕ → S → ℂ) (A : S → ℝ),
      (∀ n, ∃ C : ℝ, ∀ s, ‖u n s‖ ≤ C) →
      TendstoUniformly (fun N s ↦ ∑ n ∈ range N, ‖u n s‖) A atTop →
      TendstoUniformly (fun N s ↦ ∏ n ∈ range N, (1 + u n s))
        (fun s ↦ ∏' n, (1 + u n s)) atTop)
    {Ω : Set ℂ} {F : ℕ → ℂ → ℂ}
    (hΩ : IsOpen Ω) (hF : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hnonzero : ∀ n z, z ∈ Ω → ∃ w ∈ connectedComponentIn Ω z, F n w ≠ 0)
    (hseries : ∃ A : ℂ → ℝ, TendstoLocallyUniformlyOn
      (fun N z ↦ ∑ n ∈ range N, ‖1 - F n z‖) A atTop Ω) :
    TendstoLocallyUniformlyOn (fun N z ↦ ∏ n ∈ range N, F n z)
        (fun z ↦ ∏' n, F n z) atTop Ω ∧
      DifferentiableOn ℂ (fun z ↦ ∏' n, F n z) Ω ∧
      ∀ z ∈ Ω,
        (∀ n, analyticOrderAt (F n) z ≠ ⊤) ∧
        analyticOrderAt (fun w ↦ ∏' n, F n w) z ≠ ⊤ ∧
        analyticOrderNatAt (fun w ↦ ∏' n, F n w) z =
          ∑' n, analyticOrderNatAt (F n) z ∧
        ∃ N, (∀ n, N ≤ n → F n z ≠ 0) ∧
          analyticOrderNatAt (fun w ↦ ∏' n, F n w) z =
            ∑ n ∈ range N, analyticOrderNatAt (F n) z := by
  obtain ⟨A, hA⟩ := hseries
  have hconv : TendstoLocallyUniformlyOn
      (fun N z ↦ ∑ n ∈ range N, ‖F n z - 1‖) A atTop Ω := by
    simpa only [norm_sub_rev] using hA
  obtain ⟨hlim, hhol, horder⟩ :=
    holomorphic_product_of_uniform_norm_series_using_15_4 h15_4 hΩ hF hconv
  refine ⟨hlim, hhol, ?_⟩
  intro z hz
  obtain ⟨N, hNorder, hNzero⟩ := horder z hz
  obtain ⟨hfinite, hprefix⟩ := finite_multiplicity_of_prefix_order hΩ hF hnonzero hz hNorder
  refine ⟨(fun n ↦ analyticOrderAt_ne_top_of_component_nonzero hΩ (hF n)
    (hnonzero n) hz), hfinite, multiplicity_tsum_of_finite_prefix hprefix hNzero,
    N, ?_, hprefix⟩
  intro n hn
  exact ((hF n).analyticAt (hΩ.mem_nhds hz)).analyticOrderAt_eq_zero.mp (hNzero n hn)

/-- Theorem 15.6: locally uniform holomorphic products, with finite natural
zero multiplicities and their exact sum. The component hypothesis is explicit. -/
theorem holomorphic_product_multiplicity
    {Ω : Set ℂ} {F : ℕ → ℂ → ℂ}
    (hΩ : IsOpen Ω) (hF : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hnonzero : ∀ n z, z ∈ Ω → ∃ w ∈ connectedComponentIn Ω z, F n w ≠ 0)
    (hseries : ∃ A : ℂ → ℝ, TendstoLocallyUniformlyOn
      (fun N z ↦ ∑ n ∈ range N, ‖1 - F n z‖) A atTop Ω) :
    TendstoLocallyUniformlyOn (fun N z ↦ ∏ n ∈ range N, F n z)
        (fun z ↦ ∏' n, F n z) atTop Ω ∧
      DifferentiableOn ℂ (fun z ↦ ∏' n, F n z) Ω ∧
      ∀ z ∈ Ω,
        (∀ n, analyticOrderAt (F n) z ≠ ⊤) ∧
        analyticOrderAt (fun w ↦ ∏' n, F n w) z ≠ ⊤ ∧
        analyticOrderNatAt (fun w ↦ ∏' n, F n w) z =
          ∑' n, analyticOrderNatAt (F n) z ∧
        ∃ N, (∀ n, N ≤ n → F n z ≠ 0) ∧
          analyticOrderNatAt (fun w ↦ ∏' n, F n w) z =
            ∑ n ∈ range N, analyticOrderNatAt (F n) z :=
  holomorphic_product_multiplicity_using_15_4
    (fun _ u A hb hc ↦ uniform_product_of_uniform_norm_series u A hb hc)
    hΩ hF hnonzero hseries

/-- Definition 15.7: the polynomial in the exponential of a primary factor. -/
def elementaryExponent (p : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ range p, z ^ (k + 1) / (k + 1 : ℂ)

/-- Definition 15.7: Weierstrass's elementary factor, including `p = 0`. -/
def elementaryFactor (p : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp (elementaryExponent p z)

@[simp] theorem elementaryFactor_zero (z : ℂ) : elementaryFactor 0 z = 1 - z := by
  simp [elementaryFactor, elementaryExponent]

/-- The sole zero of any elementary factor is the point `1`. -/
@[simp] theorem elementaryFactor_eq_zero_iff (p : ℕ) (z : ℂ) :
    elementaryFactor p z = 0 ↔ z = 1 := by
  simp [elementaryFactor, Complex.exp_ne_zero, sub_eq_zero, eq_comm]

/-- Elementary factors are entire. -/
theorem differentiable_elementaryFactor (p : ℕ) : Differentiable ℂ (elementaryFactor p) := by
  unfold elementaryFactor elementaryExponent
  fun_prop

/-- The zero in Definition 15.7 is simple. -/
theorem analyticOrderAt_elementaryFactor (p : ℕ) (z : ℂ) :
    analyticOrderAt (elementaryFactor p) z = if z = 1 then 1 else 0 := by
  have hlin : AnalyticAt ℂ (fun w : ℂ ↦ 1 - w) z := by fun_prop
  have hexp : AnalyticAt ℂ (fun w ↦ Complex.exp (elementaryExponent p w)) z := by
    unfold elementaryExponent
    fun_prop
  rw [show elementaryFactor p = (fun w : ℂ ↦ 1 - w) *
    (fun w ↦ Complex.exp (elementaryExponent p w)) from rfl,
    analyticOrderAt_mul hlin hexp,
    hexp.analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _), add_zero]
  have hneg : (fun w : ℂ ↦ 1 - w) = -(fun w : ℂ ↦ w - 1) := by
    funext w
    simp
  rw [hneg, analyticOrderAt_neg]
  by_cases hz : z = 1
  · subst z
    simp
  · simp [hz, analyticOrderAt_id_sub_const_of_ne hz]

/-- Rescaling an elementary factor places its simple zero at `a ≠ 0`. -/
theorem analyticOrderAt_scaled_elementaryFactor (p : ℕ) {a : ℂ} (ha : a ≠ 0) (z : ℂ) :
    analyticOrderAt (fun w ↦ elementaryFactor p (w / a)) z =
      if z = a then 1 else 0 := by
  have hd : HasDerivAt (fun w : ℂ ↦ w / a) (1 / a) z :=
    (hasDerivAt_id z).div_const a
  have hg : AnalyticAt ℂ (fun w : ℂ ↦ w / a) z := by fun_prop
  have hg' : deriv (fun w : ℂ ↦ w / a) z ≠ 0 := by
    rw [hd.deriv]
    simp [ha]
  change analyticOrderAt (elementaryFactor p ∘ (fun w : ℂ ↦ w / a)) z = _
  rw [analyticOrderAt_comp_of_deriv_ne_zero hg hg', analyticOrderAt_elementaryFactor]
  simp only [div_eq_one_iff_eq ha]

#print axioms holomorphic_of_locally_uniform_products
#print axioms uniform_series_tail
#print axioms analyticOrderAt_finset_product
#print axioms analyticOrderAt_product_with_nonzero_tail
#print axioms analyticOrderAt_ne_top_of_component_nonzero
#print axioms analyticOrderAt_infinite_product_finite_prefix
#print axioms finite_multiplicity_of_prefix_order
#print axioms multiplicity_tsum_of_finite_prefix
#print axioms holomorphic_product_of_uniform_norm_series_using_15_4
#print axioms holomorphic_product_multiplicity_using_15_4
#print axioms holomorphic_product_multiplicity
#print axioms analyticOrderAt_scaled_elementaryFactor
#print axioms uniform_product_of_uniform_norm_series
#print axioms uniform_productOn_of_uniform_norm_series
#print axioms product_eq_zero_iff_of_uniform_norm_series
#print axioms uniform_norm_series_reindex
#print axioms uniform_product_reindex_of_uniform_norm_series
#print axioms product_reindex
#print axioms analyticOrderAt_elementaryFactor
#print axioms finite_product_majorant_le_exp
#print axioms norm_finite_product_sub_one_le
#print axioms finite_product_estimates
#print axioms zeros_have_no_accumulation
#print axioms elementaryFactor_zero
#print axioms elementaryFactor_eq_zero_iff
#print axioms differentiable_elementaryFactor
#print axioms sequentialProduct_zero
#print axioms HasProd.hasSequentialProduct
#print axioms product_one_sub_converges
#print axioms positive_product_one_sub_iff

end RudinRCA.Chapter15
