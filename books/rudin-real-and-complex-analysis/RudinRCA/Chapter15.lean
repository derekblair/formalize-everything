import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.FunProp
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
import RudinRCA.Chapter10
import RudinRCA.Chapter13
import RudinRCA.Chapter14
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Bezout
import Mathlib.Topology.MetricSpace.HausdorffDistance
import RudinRCA.Chapter04
import RudinRCA.Chapter11
import RudinRCA.Chapter12
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.MeasureTheory.Covering.OneDim
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Instances.ENat
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Data.Fintype.BigOperators

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
  simp only [elementaryFactor, mul_eq_zero, Complex.exp_ne_zero, or_false, sub_eq_zero]
  exact eq_comm

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


/-! ## 15.8: the elementary-factor estimate -/

noncomputable def realElementaryExponent (p : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range p, t ^ (k + 1) / (k + 1 : ℝ)

noncomputable def realElementaryFactor (p : ℕ) (t : ℝ) : ℝ :=
  (1 - t) * Real.exp (realElementaryExponent p t)

theorem hasDerivAt_elementaryExponent (p : ℕ) (z : ℂ) :
    HasDerivAt (elementaryExponent p) (∑ k ∈ Finset.range p, z ^ k) z := by
  apply HasDerivAt.fun_sum
  intro k hk
  have hk0 : (k + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero k
  simpa [Nat.cast_add, Nat.cast_one, mul_div_cancel_left₀ _ hk0] using
    (hasDerivAt_pow (k + 1) z).div_const (k + 1 : ℂ)

theorem hasDerivAt_realElementaryExponent (p : ℕ) (t : ℝ) :
    HasDerivAt (realElementaryExponent p) (∑ k ∈ Finset.range p, t ^ k) t := by
  apply HasDerivAt.fun_sum
  intro k hk
  have hk0 : (k + 1 : ℝ) ≠ 0 := Nat.cast_add_one_ne_zero k
  simpa [Nat.cast_add, Nat.cast_one, mul_div_cancel_left₀ _ hk0] using
    (hasDerivAt_pow (k + 1) t).div_const (k + 1 : ℝ)

theorem hasDerivAt_elementaryFactor (p : ℕ) (z : ℂ) :
    HasDerivAt (elementaryFactor p)
      (-(z ^ p * Complex.exp (elementaryExponent p z))) z := by
  change HasDerivAt (fun w ↦ (1 - w) * Complex.exp (elementaryExponent p w)) _ z
  refine (((hasDerivAt_id z).const_sub 1).mul
    (hasDerivAt_elementaryExponent p z).cexp).congr_deriv ?_
  calc
    -1 * Complex.exp (elementaryExponent p z) + (1 - z) *
        (Complex.exp (elementaryExponent p z) * (∑ k ∈ Finset.range p, z ^ k)) =
        ((1 - z) * (∑ k ∈ Finset.range p, z ^ k) - 1) *
          Complex.exp (elementaryExponent p z) := by ring
    _ = _ := by rw [mul_neg_geom_sum]; ring

theorem hasDerivAt_realElementaryFactor (p : ℕ) (t : ℝ) :
    HasDerivAt (realElementaryFactor p)
      (-(t ^ p * Real.exp (realElementaryExponent p t))) t := by
  change HasDerivAt (fun x ↦ (1 - x) * Real.exp (realElementaryExponent p x)) _ t
  refine (((hasDerivAt_id t).const_sub 1).mul
    (hasDerivAt_realElementaryExponent p t).exp).congr_deriv ?_
  calc
    -1 * Real.exp (realElementaryExponent p t) + (1 - t) *
        (Real.exp (realElementaryExponent p t) * (∑ k ∈ Finset.range p, t ^ k)) =
        ((1 - t) * (∑ k ∈ Finset.range p, t ^ k) - 1) *
          Real.exp (realElementaryExponent p t) := by ring
    _ = _ := by rw [mul_neg_geom_sum]; ring

theorem elementary_weight_integral (p : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..1, t ^ p * Real.exp (realElementaryExponent p t)) = 1 := by
  have hcont : Continuous (fun t : ℝ ↦ t ^ p * Real.exp (realElementaryExponent p t)) := by
    unfold realElementaryExponent
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f := fun t ↦ 1 - realElementaryFactor p t)
    (f' := fun t ↦ t ^ p * Real.exp (realElementaryExponent p t))
    (fun t _ ↦ by simpa using (hasDerivAt_realElementaryFactor p t).const_sub 1)
    (hcont.intervalIntegrable _ _)
  simpa [realElementaryFactor, realElementaryExponent] using h

theorem norm_elementaryExponent_line_le (p : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖elementaryExponent p ((t : ℂ) * z)‖ ≤ realElementaryExponent p t := by
  unfold elementaryExponent realElementaryExponent
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)
  simp only [norm_div, Complex.norm_pow, Complex.norm_mul, Complex.norm_of_nonneg ht,
    ← Nat.cast_add_one, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀ (mul_nonneg ht (norm_nonneg z))
  simpa using mul_le_mul_of_nonneg_left hz ht

theorem hasDerivAt_elementaryFactor_line (p : ℕ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ elementaryFactor p ((x : ℂ) * z))
      (-( ((t : ℂ) * z) ^ p * Complex.exp (elementaryExponent p ((t : ℂ) * z))) * z) t := by
  simpa only [Function.comp_apply, id_eq, one_mul] using!
    ((hasDerivAt_elementaryFactor p ((t : ℂ) * z)).comp (t : ℂ)
      ((hasDerivAt_id (t : ℂ)).mul_const z)).comp_ofReal

theorem norm_elementaryFactor_line_deriv_le (p : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖deriv (fun x : ℝ ↦ elementaryFactor p ((x : ℂ) * z)) t‖ ≤
      ‖z‖ ^ (p + 1) * (t ^ p * Real.exp (realElementaryExponent p t)) := by
  rw [(hasDerivAt_elementaryFactor_line p z t).deriv]
  simp only [Complex.norm_mul, norm_neg, Complex.norm_pow, Complex.norm_of_nonneg ht]
  have he : ‖Complex.exp (elementaryExponent p ((t : ℂ) * z))‖ ≤
      Real.exp (realElementaryExponent p t) :=
    (Complex.norm_exp_le_exp_norm _).trans
      (Real.exp_le_exp.mpr (norm_elementaryExponent_line_le p z hz t ht))
  calc
    (t * ‖z‖) ^ p * ‖Complex.exp (elementaryExponent p ((t : ℂ) * z))‖ * ‖z‖ ≤
        (t * ‖z‖) ^ p * Real.exp (realElementaryExponent p t) * ‖z‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left he (pow_nonneg (mul_nonneg ht (norm_nonneg z)) p))
        (norm_nonneg z)
    _ = ‖z‖ ^ (p + 1) * (t ^ p * Real.exp (realElementaryExponent p t)) := by
      rw [mul_pow, pow_succ]
      ring

/-- Rudin 15.8, including the boundary `‖z‖ = 1` and the case `p = 0`. -/
theorem norm_one_sub_elementaryFactor_le (p : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖1 - elementaryFactor p z‖ ≤ ‖z‖ ^ (p + 1) := by
  have hc : Continuous (fun t : ℝ ↦ elementaryFactor p ((t : ℂ) * z)) :=
    continuous_iff_continuousAt.mpr (fun t ↦ (hasDerivAt_elementaryFactor_line p z t).continuousAt)
  have hd : DifferentiableOn ℝ (fun t : ℝ ↦ elementaryFactor p ((t : ℂ) * z))
      (Set.Ioo 0 1) :=
    fun t _ ↦ (hasDerivAt_elementaryFactor_line p z t).differentiableAt.differentiableWithinAt
  have hBc : Continuous (fun t : ℝ ↦ ‖z‖ ^ (p + 1) *
      (t ^ p * Real.exp (realElementaryExponent p t))) := by
    unfold realElementaryExponent
    fun_prop
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le
    (a := (0 : ℝ)) (b := 1) (by norm_num) hc.continuousOn hd
    (Filter.Eventually.of_forall (fun t ht ↦
      norm_elementaryFactor_line_deriv_le p z hz t ht.1.le)) (hBc.intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, elementary_weight_integral, mul_one] at h
  have hzero : elementaryFactor p 0 = 1 := by
    simp [elementaryFactor, elementaryExponent]
  simpa only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, hzero,
    norm_sub_rev] using h

#print axioms hasDerivAt_elementaryExponent
#print axioms hasDerivAt_realElementaryExponent
#print axioms hasDerivAt_elementaryFactor
#print axioms hasDerivAt_realElementaryFactor
#print axioms elementary_weight_integral
#print axioms norm_elementaryExponent_line_le
#print axioms hasDerivAt_elementaryFactor_line
#print axioms norm_elementaryFactor_line_deriv_le
#print axioms norm_one_sub_elementaryFactor_le



/-! ## Entire logarithms and removable quotients for 15.10 -/
section
open Set
open scoped Classical

/-- A continuous logarithm of a holomorphic function is holomorphic. The
nonzero derivative of the exponential supplies the derivative of the branch. -/
theorem differentiableOn_of_continuous_log {U : Set ℂ} {f g : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hg : ContinuousOn g U)
    (heq : EqOn (Complex.exp ∘ g) f U) : DifferentiableOn ℂ g U := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  have hgc : ContinuousAt g z := hg.continuousAt (hU.mem_nhds hz)
  have hfd : HasDerivAt f (deriv f z) z :=
    (hf.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hevent : Complex.exp ∘ g =ᶠ[𝓝 z] f := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact heq hw
  exact (HasDerivAt.of_comp_left hgc (Complex.hasDerivAt_exp (g z)) hfd
    (Complex.exp_ne_zero (g z)) hevent).differentiableAt

/-- A zero-free holomorphic function on an open simply connected domain has a
holomorphic logarithm. Its existence is derived from the covering-space lift. -/
theorem exists_holomorphic_log {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hsc : IsSimplyConnected U)
    (hf : DifferentiableOn ℂ f U) (hzero : ∀ z ∈ U, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, Complex.exp (g z) = f z := by
  have hzero' : 0 ∉ f '' U := by
    rintro ⟨z, hz, heq⟩
    exact hzero z hz heq
  obtain ⟨g, hgc, hgexp⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hsc hU hf.continuousOn hzero'
  exact ⟨g, differentiableOn_of_continuous_log hU hf hgc hgexp, hgexp⟩

/-- The exponential-factor prerequisite of Theorem 15.10: every zero-free entire
function is the exponential of an entire function. This does not assert the
canonical-product factorization or enumerate its zeros. -/
theorem exists_entire_log {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hzero : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, Complex.exp (g z) = f z := by
  have hsc : IsSimplyConnected (univ : Set ℂ) := by
    let : ContractibleSpace (univ : Set ℂ) :=
      (convex_univ : Convex ℝ (univ : Set ℂ)).contractibleSpace univ_nonempty
    exact inferInstanceAs (SimplyConnectedSpace (univ : Set ℂ))
  obtain ⟨g, hg, heq⟩ := exists_holomorphic_log isOpen_univ hsc hf.differentiableOn
    (fun z _ ↦ hzero z)
  exact ⟨g, differentiableOn_univ.1 hg, fun z ↦ heq z (mem_univ z)⟩

/-- A natural-valued count with an actual finite sum has finite support. Using
`HasSum` rather than an equality involving `tsum` excludes its default-value case. -/
theorem finite_fiber_of_hasSum_count {ι X : Type*} (a : ι → X) (z : X) (m : ℕ)
    (h : HasSum (fun n ↦ if a n = z then (1 : ℕ) else 0) m) :
    (a ⁻¹' {z}).Finite := by
  classical
  have hi := h.map (Nat.castAddMonoidHom ℤ) continuous_of_discreteTopology
  have hs := hi.summable.hasFiniteSupport_of_discreteTopology _
  change Set.Finite {x | a x = z}
  simpa [Function.HasFiniteSupport, Function.support, Function.comp_def] using hs

/-- A sequence of zeros of a nonzero entire function, with each zero repeated
only finitely often, leaves every bounded set. Completeness of the enumeration
is not needed for this implication. -/
theorem zero_sequence_norm_tendsto_atTop {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (ha : ∀ n, f (a n) = 0) (hfiber : ∀ z, (a ⁻¹' {z}).Finite) :
    Tendsto (fun n ↦ ‖a n‖) atTop atTop := by
  have hfa : AnalyticOnNhd ℂ f univ := fun z _ ↦ hf.analyticAt z
  have hcod := hfa.preimage_zero_mem_codiscrete h0
  have hzd : IsClosed (f ⁻¹' {0}) ∧ IsDiscrete (f ⁻¹' {0}) :=
    compl_mem_codiscrete_iff.mp hcod
  have hproper : Tendsto a cofinite (cocompact ℂ) := by
    apply tendsto_cofinite_cocompact_iff.mpr
    intro K hK
    have hfin : (K ∩ f ⁻¹' {0}).Finite :=
      (hK.inter_right hzd.1).finite (hzd.2.mono inter_subset_right)
    have hpre : (a ⁻¹' (K ∩ f ⁻¹' {0})).Finite :=
      hfin.preimage' (fun z _ ↦ hfiber z)
    exact hpre.subset (fun n hn ↦ ⟨hn, ha n⟩)
  simpa only [Nat.cofinite_eq_atTop, Function.comp_def] using
    tendsto_norm_cocompact_atTop.comp hproper

/-- The printed zero enumeration in 15.10 forces its nonzero entries to tend to
infinity; this is a conclusion, not an extra canonical-product hypothesis. -/
theorem zero_enumeration_norm_tendsto_atTop {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (ha : ∀ n, f (a n) = 0)
    (hcount : ∀ z, HasSum (fun n ↦ if a n = z then (1 : ℕ) else 0)
      (analyticOrderNatAt f z)) :
    (∀ n, a n ≠ 0) ∧ Tendsto (fun n ↦ ‖a n‖) atTop atTop := by
  refine ⟨fun n hn ↦ h0 (hn ▸ ha n), zero_sequence_norm_tendsto_atTop hf h0 ha ?_⟩
  intro z
  exact finite_fiber_of_hasSum_count a z (analyticOrderNatAt f z) (hcount z)

/-- The removable quotient prerequisite for 15.10. Equal finite vanishing orders
give an entire nonvanishing quotient. This is conditional on a supplied entire
product and does not itself construct that canonical product. -/
theorem exists_entire_nonvanishing_quotient_of_order_eq {f P : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hP : Differentiable ℂ P)
    (hfinite : ∀ z, analyticOrderAt P z ≠ ⊤)
    (horder : ∀ z, analyticOrderAt f z = analyticOrderAt P z) :
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ (∀ z, q z ≠ 0) ∧ ∀ z, f z = q z * P z := by
  let q : ℂ → ℂ := toMeromorphicNFOn (f / P) univ
  have hm : MeromorphicOn (f / P) univ :=
    fun z _ ↦ (hf.analyticAt z).meromorphicAt.div (hP.analyticAt z).meromorphicAt
  have hnf : ∀ z, MeromorphicNFAt q z :=
    fun z ↦ meromorphicNFOn_toMeromorphicNFOn (f / P) univ (mem_univ z)
  have hqord : ∀ z, meromorphicOrderAt q z = 0 := by
    intro z
    dsimp only [q]
    rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ z),
      meromorphicOrderAt_div (hf.analyticAt z).meromorphicAt (hP.analyticAt z).meromorphicAt,
      (hf.analyticAt z).meromorphicOrderAt_eq, (hP.analyticAt z).meromorphicOrderAt_eq,
      horder z]
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hfinite z)
    rw [← hm]
    simp
  have hqa : ∀ z, AnalyticAt ℂ q z := fun z ↦
    (hnf z).meromorphicOrderAt_nonneg_iff_analyticAt.mp (le_of_eq (hqord z).symm)
  have hqd : Differentiable ℂ q := fun z ↦ (hqa z).differentiableAt
  refine ⟨q, hqd, fun z ↦ (hnf z).meromorphicOrderAt_eq_zero_iff.mp (hqord z), ?_⟩
  intro z
  have hne : ∀ᶠ w in 𝓝[≠] z, P w ≠ 0 :=
    (hP.analyticAt z).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun h ↦ hfinite z (analyticOrderAt_eq_top.mpr h))
  have heq : (fun w ↦ q w * P w) =ᶠ[𝓝[≠] z] f := by
    filter_upwards [hm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z), hne] with w hw hPw
    change q w = f w / P w at hw
    rw [hw, div_mul_cancel₀ _ hPw]
  have hmul : ContinuousAt (fun w ↦ q w * P w) z :=
    hqd.continuous.continuousAt.mul hP.continuous.continuousAt
  have heqnhds : (fun w ↦ q w * P w) =ᶠ[𝓝 z] f :=
    (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hmul
      hf.continuous.continuousAt).mp heq
  exact heqnhds.eq_of_nhds.symm

/-- Once the canonical product has the actual orders of `f`, the missing factor
is the exponential of an entire function. Product existence remains a separate
obligation of the full 15.10 theorem. -/
theorem exists_entire_exponential_factor_of_order_eq {f P : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hP : Differentiable ℂ P)
    (hfinite : ∀ z, analyticOrderAt P z ≠ ⊤)
    (horder : ∀ z, analyticOrderAt f z = analyticOrderAt P z) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) * P z := by
  obtain ⟨q, hqd, hqne, heq⟩ :=
    exists_entire_nonvanishing_quotient_of_order_eq hf hP hfinite horder
  obtain ⟨g, hgd, hg⟩ := exists_entire_log hqd hqne
  exact ⟨g, hgd, fun z ↦ by rw [hg z]; exact heq z⟩

/-- A nonzero entire function has finite order at every point. -/
theorem analyticOrderAt_ne_top_of_entire_nonzero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (z : ℂ) :
    analyticOrderAt f z ≠ ⊤ := by
  intro htop
  have hfun : f = 0 :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hf.analyticAt).mp htop
  exact h0 (congrFun hfun 0)

/-- A natural-order interface for the exponential factor, suitable for the
finite multiplicity sum supplied by 15.9. -/
theorem exists_entire_exponential_factor_of_nat_order_eq {f P : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hP : Differentiable ℂ P)
    (hf0 : f 0 ≠ 0) (hP0 : P 0 ≠ 0)
    (horder : ∀ z, analyticOrderNatAt f z = analyticOrderNatAt P z) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) * P z := by
  have hfinf := analyticOrderAt_ne_top_of_entire_nonzero hf hf0
  have hfinP := analyticOrderAt_ne_top_of_entire_nonzero hP hP0
  apply exists_entire_exponential_factor_of_order_eq hf hP hfinP
  intro z
  rw [← Nat.cast_analyticOrderNatAt (hfinf z), ← Nat.cast_analyticOrderNatAt (hfinP z),
    horder z]

#print axioms differentiableOn_of_continuous_log
#print axioms exists_holomorphic_log
#print axioms exists_entire_log
#print axioms finite_fiber_of_hasSum_count
#print axioms zero_sequence_norm_tendsto_atTop
#print axioms zero_enumeration_norm_tendsto_atTop
#print axioms exists_entire_nonvanishing_quotient_of_order_eq
#print axioms exists_entire_exponential_factor_of_order_eq
#print axioms analyticOrderAt_ne_top_of_entire_nonzero
#print axioms exists_entire_exponential_factor_of_nat_order_eq


end



/-- The admissibility assertion in 15.9: with zero-based indexing, `p n = n`
always works for a sequence of nonzero points escaping to infinity. -/
theorem summable_primary_majorant_nat {a : ℕ → ℂ}
    (ha : ∀ n, a n ≠ 0) (hinfty : Tendsto (fun n ↦ ‖a n‖) atTop atTop)
    {r : ℝ} (hr : 0 < r) :
    Summable (fun n ↦ (r / ‖a n‖) ^ (n + 1)) := by
  have hgeo : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1)) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).comp_injective
      (fun n m h ↦ Nat.add_right_cancel h)
  apply hgeo.of_norm_bounded_eventually_nat
  filter_upwards [hinfty.eventually (eventually_ge_atTop (2 * r))] with n hn
  have hapos : 0 < ‖a n‖ := norm_pos_iff.mpr (ha n)
  have hnonneg : 0 ≤ r / ‖a n‖ := div_nonneg hr.le hapos.le
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hnonneg _)]
  apply pow_le_pow_left₀ hnonneg
  apply (div_le_iff₀ hapos).2
  linarith

/-- Local uniform summability of the primary-factor errors in 15.9. -/
theorem primary_errors_locally_uniform {a : ℕ → ℂ} {p : ℕ → ℕ}
    (ha : ∀ n, a n ≠ 0) (hinfty : Tendsto (fun n ↦ ‖a n‖) atTop atTop)
    (hsum : ∀ r : ℝ, 0 < r → Summable (fun n ↦ (r / ‖a n‖) ^ (p n + 1))) :
    TendstoLocallyUniformlyOn
      (fun N z ↦ ∑ n ∈ range N, ‖1 - elementaryFactor (p n) (z / a n)‖)
      (fun z ↦ ∑' n, ‖1 - elementaryFactor (p n) (z / a n)‖) atTop Set.univ := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).2
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (f := fun z : ℂ ↦ z) continuousOn_id
  let r : ℝ := max R 1
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  apply tendstoUniformlyOn_tsum_nat_eventually (hsum r hr)
  filter_upwards [hinfty.eventually (eventually_ge_atTop r)] with n hn z hz
  have hapos : 0 < ‖a n‖ := norm_pos_iff.mpr (ha n)
  have hzr : ‖z‖ ≤ r := (hR z hz).trans (le_max_left _ _)
  have hz1 : ‖z / a n‖ ≤ 1 := by
    rw [norm_div, div_le_one hapos]
    exact hzr.trans hn
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact (norm_one_sub_elementaryFactor_le (p n) (z / a n) hz1).trans
    (pow_le_pow_left₀ (norm_nonneg (z / a n))
      (by rw [norm_div]; exact div_le_div_of_nonneg_right hzr hapos.le) (p n + 1))

/-- The entire product and multiplicities in 15.9, with repetitions of the
sequence counted by the natural sum of their indicator functions. -/
theorem entire_primary_product {a : ℕ → ℂ} {p : ℕ → ℕ}
    (ha : ∀ n, a n ≠ 0) (hinfty : Tendsto (fun n ↦ ‖a n‖) atTop atTop)
    (hsum : ∀ r : ℝ, 0 < r → Summable (fun n ↦ (r / ‖a n‖) ^ (p n + 1))) :
    let f := fun z ↦ ∏' n, elementaryFactor (p n) (z / a n)
    TendstoLocallyUniformlyOn
      (fun N z ↦ ∏ n ∈ range N, elementaryFactor (p n) (z / a n)) f atTop Set.univ ∧
    Differentiable ℂ f ∧
    ∀ z, (f z = 0 ↔ ∃ n, z = a n) ∧
      analyticOrderAt f z ≠ ⊤ ∧
      analyticOrderNatAt f z = ∑' n, if z = a n then (1 : ℕ) else 0 := by
  let F : ℕ → ℂ → ℂ := fun n z ↦ elementaryFactor (p n) (z / a n)
  have hF : ∀ n, DifferentiableOn ℂ (F n) Set.univ := by
    intro n
    exact ((differentiable_elementaryFactor (p n)).comp
      (differentiable_id.div_const (a n))).differentiableOn
  have hnonzero : ∀ n z, z ∈ (Set.univ : Set ℂ) →
      ∃ w ∈ connectedComponentIn Set.univ z, F n w ≠ 0 := by
    intro n z _
    refine ⟨0, by simp [connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ], ?_⟩
    simp [F, elementaryFactor, elementaryExponent]
  have herr := primary_errors_locally_uniform ha hinfty hsum
  obtain ⟨hlim, hhol, horder⟩ := holomorphic_product_multiplicity
    isOpen_univ hF hnonzero ⟨_, herr⟩
  refine ⟨hlim, differentiableOn_univ.mp hhol, ?_⟩
  intro z
  obtain ⟨_, hfinite, hm, _⟩ := horder z (Set.mem_univ z)
  have hsz : Summable (fun n ↦ ‖1 - F n z‖) :=
    ((hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ norm_nonneg _) _).2
      (herr.tendsto_at (Set.mem_univ z))).summable
  have hzero : (∏' n, F n z) = 0 ↔ ∃ n, z = a n := by
    constructor
    · intro hz
      by_contra h
      push_neg at h
      have hnone : ∀ n, F n z ≠ 0 := by
        intro n
        simpa [F, elementaryFactor_eq_zero_iff, div_eq_one_iff_eq (ha n)] using h n
      have hone : ∀ n, 1 + (F n z - 1) = F n z := by intro n; ring
      have hnorm : Summable (fun n ↦ ‖F n z - 1‖) := by simpa only [norm_sub_rev] using hsz
      have hn := tprod_one_add_ne_zero_of_summable
        (fun n ↦ by simpa only [hone] using hnone n) hnorm
      exact hn (by simpa only [hone] using hz)
    · rintro ⟨n, hz⟩
      exact tprod_of_exists_eq_zero ⟨n, by simp [F, hz, ha n]⟩
  refine ⟨hzero, hfinite, ?_⟩
  rw [hm]
  apply tsum_congr
  intro n
  simp only [F, analyticOrderNatAt, analyticOrderAt_scaled_elementaryFactor (p n) (ha n)]
  split_ifs <;> simp

/-- Finite and empty products obey the same entire-function and zero-count
conventions used in 15.9–15.10. -/
theorem finite_primary_product {ι : Type*} (s : Finset ι) (a : ι → ℂ) (p : ι → ℕ)
    (ha : ∀ n ∈ s, a n ≠ 0) :
    let f := fun z ↦ ∏ n ∈ s, elementaryFactor (p n) (z / a n)
    Differentiable ℂ f ∧ f 0 = 1 ∧
      ∀ z, (f z = 0 ↔ ∃ n ∈ s, z = a n) ∧
        analyticOrderAt f z = ∑ n ∈ s, if z = a n then (1 : ℕ∞) else 0 := by
  classical
  have hd (n : ι) : Differentiable ℂ (fun z ↦ elementaryFactor (p n) (z / a n)) :=
    (differentiable_elementaryFactor (p n)).comp (differentiable_id.div_const (a n))
  refine ⟨Differentiable.fun_finsetProd (fun n _ ↦ hd n), ?_, ?_⟩
  · simp [elementaryFactor, elementaryExponent]
  · intro z
    constructor
    · rw [Finset.prod_eq_zero_iff]
      constructor
      · rintro ⟨n, hn, hz⟩
        exact ⟨n, hn, (div_eq_one_iff_eq (ha n hn)).1
          ((elementaryFactor_eq_zero_iff (p n) (z / a n)).1 hz)⟩
      · rintro ⟨n, hn, hz⟩
        refine ⟨n, hn, (elementaryFactor_eq_zero_iff (p n) (z / a n)).2 ?_⟩
        exact (div_eq_one_iff_eq (ha n hn)).2 hz
    · rw [analyticOrderAt_finset_product s (fun n _ ↦ (hd n).analyticAt z)]
      apply Finset.sum_congr rfl
      intro n hn
      exact analyticOrderAt_scaled_elementaryFactor (p n) (ha n hn) z

#print axioms finite_primary_product
#print axioms summable_primary_majorant_nat
#print axioms primary_errors_locally_uniform
#print axioms entire_primary_product

/-- The convention following 15.10: remove the finite-order zero at the origin
before applying the nonvanishing-at-zero factorization statement. -/
theorem entire_remove_zero_at_origin {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ h 0 ≠ 0 ∧
      ∀ z, f z = z ^ analyticOrderNatAt f 0 * h z := by
  have hfinite : analyticOrderAt f 0 ≠ ⊤ := by
    intro htop
    exact hne ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0 hf.analyticAt).mp htop)
  obtain ⟨g, hga, hg0, heq⟩ := (hf.analyticAt 0).analyticOrderAt_ne_top.mp hfinite
  let k := analyticOrderNatAt f 0
  let h : ℂ → ℂ := fun z ↦ if z = 0 then g 0 else f z / z ^ k
  have heq' : f =ᶠ[𝓝 0] fun z ↦ z ^ k * g z := by
    simpa only [sub_zero, smul_eq_mul] using heq
  have hnear : h =ᶠ[𝓝 0] g := by
    filter_upwards [heq'] with z hz
    by_cases hz0 : z = 0
    · simp [h, hz0]
    · simp [h, hz0, hz, mul_div_cancel_left₀, pow_ne_zero _ hz0]
  have hh : Differentiable ℂ h := by
    intro z
    by_cases hz0 : z = 0
    · subst z
      exact (hga.congr hnear.symm).differentiableAt
    · apply AnalyticAt.differentiableAt
      apply ((hf.analyticAt z).div (analyticAt_id.pow k) (pow_ne_zero _ hz0)).congr
      filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
      simp [h, hw]
  refine ⟨h, hh, by simpa [h] using hg0, ?_⟩
  intro z
  by_cases hz0 : z = 0
  · subst z
    simpa only [h, if_pos rfl] using heq'.eq_of_nhds
  · dsimp only [h]
    rw [if_neg hz0]
    exact (mul_div_cancel₀ (f z) (pow_ne_zero k hz0)).symm

/-- Theorem 15.10 for an infinite sequence listing all zeros with multiplicity.
`HasSum` records actual finite multiplicities, and escape to infinity is derived.
With zero-based indexing the admissible choice is `p n = n`. -/
theorem entire_function_factorization_infinite {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (ha : ∀ n, f (a n) = 0)
    (hcount : ∀ z, HasSum (fun n ↦ if a n = z then (1 : ℕ) else 0)
      (analyticOrderNatAt f z)) :
    ∃ p : ℕ → ℕ, ∃ g : ℂ → ℂ,
      p = (fun n ↦ n) ∧ Differentiable ℂ g ∧
      TendstoLocallyUniformlyOn
        (fun N z ↦ ∏ n ∈ range N, elementaryFactor (p n) (z / a n))
        (fun z ↦ ∏' n, elementaryFactor (p n) (z / a n)) atTop Set.univ ∧
      ∀ z, f z = Complex.exp (g z) * ∏' n, elementaryFactor (p n) (z / a n) := by
  obtain ⟨ha0, hinfty⟩ := zero_enumeration_norm_tendsto_atTop hf h0 ha hcount
  obtain ⟨hlim, hP, hprop⟩ := entire_primary_product (p := fun n ↦ n) ha0 hinfty
    (fun r hr ↦ summable_primary_majorant_nat ha0 hinfty hr)
  have hP0 : (∏' n, elementaryFactor n (0 / a n)) ≠ 0 := by
    intro hz
    obtain ⟨n, hn⟩ := (hprop 0).1.mp hz
    exact ha0 n hn.symm
  have hm : ∀ z, analyticOrderNatAt f z =
      analyticOrderNatAt (fun w ↦ ∏' n, elementaryFactor n (w / a n)) z := by
    intro z
    rw [(hprop z).2.2]
    simpa only [eq_comm] using (hcount z).tsum_eq.symm
  obtain ⟨g, hg, heq⟩ :=
    exists_entire_exponential_factor_of_nat_order_eq hf hP h0 hP0 hm
  exact ⟨(fun n ↦ n), g, rfl, hg, hlim, heq⟩

/-- The finite and empty zero-list cases of 15.10. The primary factors may all
have genus zero, and an empty list gives the entire logarithm theorem. The finite
sum hypothesis counts every zero exactly with its multiplicity. -/
theorem entire_function_factorization_finite {ι : Type*} {f : ℂ → ℂ}
    (s : Finset ι) (a : ι → ℂ) (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (ha : ∀ n ∈ s, f (a n) = 0)
    (hcount : ∀ z, (∑ n ∈ s, if a n = z then (1 : ℕ) else 0) =
      analyticOrderNatAt f z) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ z, f z = Complex.exp (g z) * ∏ n ∈ s, elementaryFactor 0 (z / a n) := by
  classical
  have ha0 : ∀ n ∈ s, a n ≠ 0 := by
    intro n hn hzero
    exact h0 (hzero ▸ ha n hn)
  obtain ⟨hP, hP0, hprop⟩ := finite_primary_product s a (fun _ ↦ 0) ha0
  have hPne : (∏ n ∈ s, elementaryFactor 0 (0 / a n)) ≠ 0 := by
    exact hP0.trans_ne one_ne_zero
  have hfinite := analyticOrderAt_ne_top_of_entire_nonzero hP hPne
  have hfinitef := analyticOrderAt_ne_top_of_entire_nonzero hf h0
  apply exists_entire_exponential_factor_of_order_eq hf hP hfinite
  intro z
  rw [(hprop z).2, ← Nat.cast_analyticOrderNatAt (hfinitef z), ← hcount z,
    Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hz : a n = z
  · simp [hz]
  · simp [hz, Ne.symm hz]

#print axioms entire_function_factorization_infinite
#print axioms entire_function_factorization_finite
#print axioms entire_remove_zero_at_origin


section Chapter15PartA
set_option autoImplicit false
open Filter Finset Set Metric
open scoped Topology OnePoint Classical


/-! ## 15.2: Infinite Products `∏ (1 + u_n)` -/

/-- Definition 15.2: `∏_{n=0}^∞ (1 + u_n) = p` means the partial products converge to `p`
(explicitly allowing `p = 0`). -/
def HasInfiniteProductOneAdd (u : ℕ → ℂ) (p : ℂ) : Prop :=
  HasSequentialProduct (fun n ↦ 1 + u n) p

/-- Definition 15.2: convergence of `∏_{n=0}^∞ (1 + u_n)` (allowing a zero limit). -/
def InfiniteProductOneAddConverges (u : ℕ → ℂ) : Prop :=
  ∃ p : ℂ, HasInfiniteProductOneAdd u p

/-- **Rudin RCA 15.2** (Infinite product convention, zero limits, and nonzero-limit consequences):
1. `InfiniteProductOneAddConverges u` holds iff the finite partial products `∏_{n < N} (1 + u_n)`
   converge in `ℂ`, and the limit is unique when it exists;
2. A zero limit explicitly counts as convergence (e.g. `u_0 = -1`, `u_n = 0` for `n ≥ 1`, and more
   generally whenever some factor `1 + u_n` vanishes);
3. If `HasInfiniteProductOneAdd u p` with `p ≠ 0`, then every factor `1 + u_n` is nonzero
   (in particular `∀ᶠ n in atTop, 1 + u_n ≠ 0`) and `u_n → 0` as `n → ∞`. -/
theorem theorem15_2 :
    (∀ u : ℕ → ℂ,
      (InfiniteProductOneAddConverges u ↔
        ∃ p : ℂ, Tendsto (fun N ↦ ∏ n ∈ Finset.range N, (1 + u n)) Filter.atTop (𝓝 p)) ∧
      (∀ p q : ℂ, HasInfiniteProductOneAdd u p → HasInfiniteProductOneAdd u q → p = q)) ∧
    HasInfiniteProductOneAdd (fun n ↦ if n = 0 then -1 else 0) 0 ∧
    (∀ u : ℕ → ℂ, (∃ n, 1 + u n = 0) → HasInfiniteProductOneAdd u 0) ∧
    (∀ (u : ℕ → ℂ) (p : ℂ), HasInfiniteProductOneAdd u p → p ≠ 0 →
      (∀ n, 1 + u n ≠ 0) ∧
      (∀ᶠ n in Filter.atTop, 1 + u n ≠ 0) ∧
      Tendsto u Filter.atTop (𝓝 0)) := by
  have hzero_gen : ∀ u : ℕ → ℂ, (∃ n, 1 + u n = 0) → HasInfiniteProductOneAdd u 0 := by
    rintro u ⟨n₀, hn₀⟩
    unfold HasInfiniteProductOneAdd HasSequentialProduct
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (n₀ + 1)] with N hN
    exact (Finset.prod_eq_zero (Finset.mem_range.mpr (by omega)) hn₀).symm
  refine ⟨fun u ↦ ⟨Iff.rfl, fun p q hp hq ↦ tendsto_nhds_unique hp hq⟩,
    hzero_gen _ ⟨0, by simp⟩, hzero_gen, ?_⟩
  intro u p hp hp0
  have hnz_all : ∀ n, 1 + u n ≠ 0 := by
    intro n hn
    exact hp0 (tendsto_nhds_unique hp (hzero_gen u ⟨n, hn⟩))
  refine ⟨hnz_all, Eventually.of_forall hnz_all, ?_⟩
  let P : ℕ → ℂ := fun N ↦ ∏ n ∈ Finset.range N, (1 + u n)
  have hP : Tendsto P atTop (𝓝 p) := hp
  have hP_succ : Tendsto (fun N ↦ P (N + 1)) atTop (𝓝 p) :=
    hP.comp (tendsto_add_atTop_nat 1)
  have hquot : Tendsto (fun N ↦ P (N + 1) / P N) atTop (𝓝 (p / p)) :=
    hP_succ.div hP hp0
  rw [div_self hp0] at hquot
  have hPN_ne : ∀ N, P N ≠ 0 := fun N ↦ Finset.prod_ne_zero_iff.mpr fun n _ ↦ hnz_all n
  have h1u : Tendsto (fun N ↦ 1 + u N) atTop (𝓝 1) := by
    refine hquot.congr fun N ↦ ?_
    dsimp [P]
    rw [Finset.prod_range_succ, mul_div_cancel_left₀ _ (hPN_ne N)]
  simpa using h1u.const_sub 1 |>.neg

/-! ## 15.3: Finite Product Estimates -/

/-- **Rudin RCA 15.3** (Finite product estimates):
For any finite index set `s : Finset ι` and `u : ι → ℂ`, let `p = ∏_{i ∈ s} (1 + u_i)` and
`p* = ∏_{i ∈ s} (1 + ‖u_i‖)`. Then `p* ≤ exp(∑_{i ∈ s} ‖u_i‖)` and `‖p - 1‖ ≤ p* - 1`. -/
theorem theorem15_3 {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    let p : ℂ := ∏ i ∈ s, (1 + u i)
    let pStar : ℝ := ∏ i ∈ s, (1 + ‖u i‖)
    pStar ≤ Real.exp (∑ i ∈ s, ‖u i‖) ∧ ‖p - 1‖ ≤ pStar - 1 :=
  finite_product_estimates s u

/-! ## 15.4: Uniform Convergence of Infinite Products -/

/-- **Rudin RCA 15.4** (Uniform convergence, zeros, and permutation invariance of products):
Let `S` be an arbitrary type and `u : ℕ → S → ℂ` be bounded for each `n` such that
`∑_{n < N} ‖u_n(s)‖` converges uniformly on `S`. Then there exists `f : S → ℂ` such that:
- `(a)` `∏_{n < N} (1 + u_n(s))` converges uniformly on `S` to `f`,
- `(b)` at each `s : S`, `f s = 0 ↔ ∃ n, 1 + u n s = 0`,
- `(c)` for every permutation `e : ℕ ≃ ℕ`, `∏_{n < N} (1 + u_{e(n)}(s))` converges uniformly on `S`
  to the same function `f`. -/
theorem theorem15_4 {S : Type*} (u : ℕ → S → ℂ)
    (hbdd : ∀ n, ∃ C : ℝ, ∀ s, ‖u n s‖ ≤ C)
    (hconv : ∃ A : S → ℝ, TendstoUniformly (fun N s ↦ ∑ n ∈ Finset.range N, ‖u n s‖) A Filter.atTop) :
    ∃ f : S → ℂ,
      TendstoUniformly (fun N s ↦ ∏ n ∈ Finset.range N, (1 + u n s)) f Filter.atTop ∧
      (∀ s, f s = 0 ↔ ∃ n, 1 + u n s = 0) ∧
      (∀ e : ℕ ≃ ℕ,
        TendstoUniformly (fun N s ↦ ∏ n ∈ Finset.range N, (1 + u (e n) s)) f Filter.atTop) := by
  obtain ⟨A, hA⟩ := hconv
  refine ⟨fun s ↦ ∏' n, (1 + u n s),
    uniform_product_of_uniform_norm_series u A hbdd hA,
    fun s ↦ ?_,
    fun e ↦ uniform_product_reindex_of_uniform_norm_series u A e hbdd hA⟩
  rw [product_eq_zero_iff_of_uniform_norm_series u A hA s]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by simp [hn]⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by linear_combination hn⟩

/-! ## 15.5: Real Infinite Products `∏ (1 - u_n)` with `0 ≤ u_n < 1` -/

/-- **Rudin RCA 15.5**:
If `u : ℕ → ℝ` satisfies `0 ≤ u_n` and `u_n < 1` for all `n`, then `∏_{n=0}^∞ (1 - u_n)` converges
to a unique real limit `p`, with `0 ≤ p ≤ 1`, and `0 < p ↔ Summable u`. -/
theorem theorem15_5 {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n < 1) :
    (∃! p : ℝ, HasSequentialProduct (fun n ↦ 1 - u n) p) ∧
    ∀ p : ℝ, HasSequentialProduct (fun n ↦ 1 - u n) p →
      0 ≤ p ∧ p ≤ 1 ∧ (0 < p ↔ Summable u) := by
  obtain ⟨p₀, hp₀⟩ := product_one_sub_converges hu hu1
  refine ⟨⟨p₀, hp₀, fun q hq ↦ tendsto_nhds_unique hq hp₀⟩, ?_⟩
  intro p hp
  have hnonneg : 0 ≤ p :=
    ge_of_tendsto' hp fun N ↦ Finset.prod_nonneg fun k _ ↦ sub_nonneg.mpr (hu1 k).le
  have hle_one : p ≤ 1 := by
    refine le_of_tendsto' hp fun N ↦ ?_
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ]
      calc
        (∏ j ∈ Finset.range k, (1 - u j)) * (1 - u k) ≤ 1 * 1 :=
          mul_le_mul ih (sub_le_self 1 (hu k)) (sub_nonneg.mpr (hu1 k).le) zero_le_one
        _ = 1 := mul_one 1
  refine ⟨hnonneg, hle_one, ?_⟩
  constructor
  · intro hpos
    exact (positive_product_one_sub_iff hu hu1).mp ⟨p, hpos, hp⟩
  · intro hsum
    obtain ⟨q, hq_pos, hq⟩ := (positive_product_one_sub_iff hu hu1).mpr hsum
    rwa [tendsto_nhds_unique hp hq]

/-! ## 15.6: Infinite Products of Holomorphic Functions -/

/-- **Rudin RCA 15.6** (Locally uniform products in `H(Ω)` and zero multiplicities):
Let `Ω ⊆ ℂ` be open and `f_n : ℕ → ℂ → ℂ` be holomorphic on `Ω`, with no `f_n` identically zero on
any connected component of `Ω`, such that `∑_{n < N} ‖1 - f_n(z)‖` converges locally uniformly on
`Ω`. Then there exists `f : ℂ → ℂ` holomorphic on `Ω` such that `∏_{n < N} f_n(z)` converges
locally uniformly on `Ω` (and uniformly on every compact `K ⊆ Ω`) to `f`, and at each `z ∈ Ω`,
`analyticOrderAt f z ≠ ⊤`, `analyticOrderNatAt f z = ∑' n, analyticOrderNatAt (f_n n) z`, and on
some open disc `ball z r ⊆ Ω` (`r > 0`) all `f_n` with `n ≥ N` are nonvanishing (hence have zero
multiplicity `0` throughout `ball z r`). -/
theorem theorem15_6 {Ω : Set ℂ} {f_n : ℕ → ℂ → ℂ}
    (hΩ : IsOpen Ω)
    (hf : ∀ n, DifferentiableOn ℂ (f_n n) Ω)
    (hnonzero : ∀ n z, z ∈ Ω → ∃ w ∈ connectedComponentIn Ω z, f_n n w ≠ 0)
    (hseries : ∃ A : ℂ → ℝ, TendstoLocallyUniformlyOn
      (fun N z ↦ ∑ n ∈ Finset.range N, ‖1 - f_n n z‖) A Filter.atTop Ω) :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f Ω ∧
      TendstoLocallyUniformlyOn (fun N z ↦ ∏ n ∈ Finset.range N, f_n n z) f Filter.atTop Ω ∧
      (∀ K ⊆ Ω, IsCompact K →
        TendstoUniformlyOn (fun N z ↦ ∏ n ∈ Finset.range N, f_n n z) f Filter.atTop K) ∧
      ∀ z ∈ Ω,
        analyticOrderAt f z ≠ ⊤ ∧
        analyticOrderNatAt f z = ∑' n, analyticOrderNatAt (f_n n) z ∧
        ∃ r > 0, Metric.ball z r ⊆ Ω ∧
          ∃ N, ∀ n ≥ N, ∀ w ∈ Metric.ball z r,
            f_n n w ≠ 0 ∧ analyticOrderNatAt (f_n n) w = 0 := by
  obtain ⟨hlim, hhol, hmult⟩ := holomorphic_product_multiplicity hΩ hf hnonzero hseries
  obtain ⟨A, hA⟩ := hseries
  refine ⟨fun z ↦ ∏' n, f_n n z, hhol, hlim,
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp hlim, ?_⟩
  intro z hz
  obtain ⟨_, hfin, hsum_eq, _⟩ := hmult z hz
  obtain ⟨R, hR, hballR⟩ := Metric.isOpen_iff.mp hΩ z hz
  let r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hcb_sub : Metric.closedBall z r ⊆ Ω :=
    (Metric.closedBall_subset_ball (half_lt_self hR)).trans hballR
  have hball_sub : Metric.ball z r ⊆ Ω := Metric.ball_subset_closedBall.trans hcb_sub
  have hunif_cb := (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp hA
    (Metric.closedBall z r) hcb_sub (isCompact_closedBall z r)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Metric.tendstoUniformlyOn_iff.mp hunif_cb (1 / 3) (by norm_num))
  refine ⟨hfin, hsum_eq, r, hr, hball_sub, N, ?_⟩
  intro n hn w hw
  have hw_cb : w ∈ Metric.closedBall z r := Metric.ball_subset_closedBall hw
  have hd1 : |A w - ∑ k ∈ Finset.range n, ‖1 - f_n k w‖| < 1 / 3 := by
    simpa [Real.dist_eq] using hN n hn w hw_cb
  have hd2 : |A w - ∑ k ∈ Finset.range (n + 1), ‖1 - f_n k w‖| < 1 / 3 := by
    simpa [Real.dist_eq] using hN (n + 1) (Nat.le_succ_of_le hn) w hw_cb
  have hterm_lt : ‖1 - f_n n w‖ < 1 := by
    have hstep : (∑ k ∈ Finset.range (n + 1), ‖1 - f_n k w‖) -
        (∑ k ∈ Finset.range n, ‖1 - f_n k w‖) = ‖1 - f_n n w‖ := by
      rw [Finset.sum_range_succ, add_sub_cancel_left]
    have h1 := (abs_lt.mp hd1).2
    have h2 := (abs_lt.mp hd2).1
    linarith
  have hfn_ne : f_n n w ≠ 0 := by
    intro h0
    rw [h0, sub_zero, norm_one] at hterm_lt
    exact lt_irrefl 1 hterm_lt
  have hord0 : analyticOrderNatAt (f_n n) w = 0 := by
    have han : AnalyticAt ℂ (f_n n) w := (hf n).analyticAt (hΩ.mem_nhds (hball_sub hw))
    simp [analyticOrderNatAt, han.analyticOrderAt_eq_zero.mpr hfn_ne]
  exact ⟨hfn_ne, hord0⟩

/-! ## 15.7 & 15.8: Weierstrass Elementary Factors and Primary Estimate -/

/-- **Rudin RCA 15.7** (Weierstrass elementary factors `E_p`):
`E_0(z) = 1 - z`, and for `p ≥ 1`, `E_p(z) = (1 - z) exp(∑_{k=1}^p z^k / k)`. Every `E_p` is
entire, vanishes solely at `z = 1`, and has a simple zero at `z = 1` (`analyticOrderAt = 1`). -/
theorem theorem15_7 :
    (∀ z : ℂ, elementaryFactor 0 z = 1 - z) ∧
    (∀ (p : ℕ), 1 ≤ p → ∀ z : ℂ,
      elementaryFactor p z =
        (1 - z) * Complex.exp (∑ k ∈ Finset.Icc 1 p, z ^ k / (k : ℂ))) ∧
    (∀ p : ℕ, Differentiable ℂ (elementaryFactor p)) ∧
    (∀ (p : ℕ) (z : ℂ), elementaryFactor p z = 0 ↔ z = 1) ∧
    (∀ (p : ℕ) (z : ℂ), analyticOrderAt (elementaryFactor p) z = if z = 1 then 1 else 0) := by
  refine ⟨elementaryFactor_zero, ?_, differentiable_elementaryFactor,
    elementaryFactor_eq_zero_iff, analyticOrderAt_elementaryFactor⟩
  intro p _ z
  unfold elementaryFactor elementaryExponent
  congr 2
  refine Finset.sum_nbij (fun k ↦ k + 1) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_range] at hk
    exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  · intro k₁ _ k₂ _ h
    exact Nat.add_right_cancel h
  · intro m hm
    simp only [Finset.mem_coe, Finset.mem_Icc] at hm
    exact ⟨m - 1, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp; omega⟩
  · intro k _
    push_cast
    rfl

/-- **Rudin RCA 15.8** (Primary-factor inequality):
For every integer `p ≥ 0` and every `z ∈ ℂ` with `‖z‖ ≤ 1` (including the boundary `‖z‖ = 1`),
`‖1 - E_p(z)‖ ≤ ‖z‖ ^ (p + 1)`. -/
theorem theorem15_8 (p : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖1 - elementaryFactor p z‖ ≤ ‖z‖ ^ (p + 1) :=
  norm_one_sub_elementaryFactor_le p z hz

/-! ## 15.9: Entire Weierstrass Products and Canonical Products -/

/-- **Rudin RCA 15.9** (Entire products with prescribed nonzero zeros and canonical products):
1. Given nonzero `a : ℕ → ℂ` with `‖a_n‖ → ∞` and `p : ℕ → ℕ` such that
   `∑_n (r / ‖a_n‖) ^ (p_n + 1) < ∞` for every `r > 0`, `P(z) = ∏' n, E_{p_n}(z / a_n)` converges
   locally uniformly on `ℂ` to an entire function whose zeros are `{a_n}` with exact multiplicity
   equal to the repetition count of `z` in `a`;
2. With `0`-based indexing (`p_n = n`, corresponding to `1`-based `p_n = n - 1`), the majorant
   series converges for every `r > 0` without additional hypotheses on `a`;
3. Constant genus `p_n = p` (canonical product) satisfies the majorant condition for all `r > 0`
   iff `∑_n ‖a_n‖⁻¹ ^ (p + 1) < ∞`, in which case `∏' n, E_p(z / a_n)` is an entire canonical
   product with the prescribed zeros and multiplicities. -/
theorem theorem15_9 {a : ℕ → ℂ} (ha : ∀ n, a n ≠ 0)
    (hinfty : Tendsto (fun n ↦ ‖a n‖) Filter.atTop Filter.atTop) :
    (∀ p : ℕ → ℕ,
      (∀ r : ℝ, 0 < r → Summable (fun n ↦ (r / ‖a n‖) ^ (p n + 1))) →
      let P := fun z ↦ ∏' n, elementaryFactor (p n) (z / a n)
      TendstoLocallyUniformlyOn
        (fun N z ↦ ∏ n ∈ Finset.range N, elementaryFactor (p n) (z / a n)) P Filter.atTop Set.univ ∧
      Differentiable ℂ P ∧
      ∀ z, (P z = 0 ↔ ∃ n, z = a n) ∧
        analyticOrderAt P z ≠ ⊤ ∧
        analyticOrderNatAt P z = ∑' n, if z = a n then (1 : ℕ) else 0) ∧
    (∀ r : ℝ, 0 < r → Summable (fun n ↦ (r / ‖a n‖) ^ (n + 1))) ∧
    (∀ p : ℕ,
      ((∀ r : ℝ, 0 < r → Summable (fun n ↦ (r / ‖a n‖) ^ (p + 1))) ↔
        Summable (fun n ↦ ‖a n‖⁻¹ ^ (p + 1))) ∧
      (Summable (fun n ↦ ‖a n‖⁻¹ ^ (p + 1)) →
        let P := fun z ↦ ∏' n, elementaryFactor p (z / a n)
        TendstoLocallyUniformlyOn
          (fun N z ↦ ∏ n ∈ Finset.range N, elementaryFactor p (z / a n)) P Filter.atTop Set.univ ∧
        Differentiable ℂ P ∧
        ∀ z, (P z = 0 ↔ ∃ n, z = a n) ∧
          analyticOrderAt P z ≠ ⊤ ∧
          analyticOrderNatAt P z = ∑' n, if z = a n then (1 : ℕ) else 0)) := by
  have hcanon_iff : ∀ p : ℕ,
      (∀ r : ℝ, 0 < r → Summable (fun n ↦ (r / ‖a n‖) ^ (p + 1))) ↔
        Summable (fun n ↦ ‖a n‖⁻¹ ^ (p + 1)) := by
    intro p
    constructor
    · intro h
      simpa [one_div] using h 1 zero_lt_one
    · intro h r _
      have heq : (fun n ↦ (r / ‖a n‖) ^ (p + 1)) =
          fun n ↦ r ^ (p + 1) * (‖a n‖⁻¹ ^ (p + 1)) := by
        funext n
        rw [div_eq_mul_inv, mul_pow]
      rw [heq]
      exact h.mul_left (r ^ (p + 1))
  exact ⟨fun p hsum ↦ entire_primary_product ha hinfty hsum,
    fun r hr ↦ summable_primary_majorant_nat ha hinfty hr,
    fun p ↦ ⟨hcanon_iff p, fun hsum ↦
      entire_primary_product (p := fun _ ↦ p) ha hinfty ((hcanon_iff p).mpr hsum)⟩⟩

/-! ## Discrete Multiplicity Enumeration & 15.10 (Weierstrass Factorization) -/

/-- Equivalence between `AccPt x (𝓟 A)` and `x ∈ closure (A \ {x})` in any topological space. -/
theorem accPt_principal_iff_mem_closure_diff {X : Type*} [TopologicalSpace X] {A : Set X} {x : X} :
    AccPt x (𝓟 A) ↔ x ∈ closure (A \ {x}) := by
  rw [accPt_iff_clusterPt, mem_closure_iff_clusterPt, inf_principal, Set.inter_comm]
  rfl

/-- Codiscreteness of the complement of a set without interior accumulation points. -/
theorem compl_mem_codiscreteWithin_of_no_limit_pt {Ω A : Set ℂ}
    (hAΩ : A ⊆ Ω) (hacc : ∀ z ∈ Ω, z ∉ closure (A \ {z})) :
    Aᶜ ∈ codiscreteWithin Ω := by
  rw [mem_codiscreteWithin_accPt]
  have heq : Ω \ Aᶜ = A := by
    ext w
    simp only [Set.mem_sdiff, Set.mem_compl_iff, not_not, and_iff_right_iff_imp]
    exact fun hw ↦ hAΩ hw
  rw [heq]
  intro w hw
  rw [accPt_principal_iff_mem_closure_diff]
  exact hacc w hw

/-- Any sequence in a set `A ⊆ Ω` without limit points in `Ω` and with finite fibers in `Ω`
eventually leaves every compact subset `L ⊆ Ω`. -/
theorem eventually_notMem_compact_of_no_limit_pt {Ω A L : Set ℂ} {z : ℕ → ℂ}
    (hAΩ : A ⊆ Ω) (hacc : ∀ w ∈ Ω, w ∉ closure (A \ {w}))
    (hL : IsCompact L) (hLΩ : L ⊆ Ω)
    (hz : ∀ n, z n ∈ A) (hfiber : ∀ w ∈ Ω, (z ⁻¹' {w}).Finite) :
    ∀ᶠ n in Filter.atTop, z n ∉ L := by
  have hcod := compl_mem_codiscreteWithin_of_no_limit_pt hAΩ hacc
  have hfin_diff := hL.finite_sdiff_of_mem_codiscreteWithin (Filter.codiscreteWithin_mono hLΩ hcod)
  have hfin_AL : (A ∩ L).Finite := by
    have heq : L \ Aᶜ = A ∩ L := by ext w; simp [and_comm]
    rwa [heq] at hfin_diff
  have hpre : (z ⁻¹' (A ∩ L)).Finite :=
    hfin_AL.preimage' (fun w hw ↦ hfiber w (hLΩ hw.2))
  have hpreL : (z ⁻¹' L).Finite := hpre.subset (fun n hn ↦ ⟨hz n, hn⟩)
  have hmem : (z ⁻¹' L)ᶜ ∈ Filter.atTop := Nat.cofinite_eq_atTop ▸ hpreL.compl_mem_cofinite
  filter_upwards [hmem] with n hn
  exact hn

/-- Unconditional discrete multiplicity enumeration on an open set `Ω ⊆ ℂ`:
If `A ⊆ Ω` has no limit point in `Ω` and `m : ℂ → ℕ` assigns a positive multiplicity to each
`a ∈ A`, then `A` is countable and the multiplicity-weighted index set `Σ a : A, Fin (m a.1)` is
either finite (giving `N : ℕ` and `z : Fin N → ℂ`, including `N = 0` when `A = ∅`) or countably
infinite (giving `z : ℕ → ℂ`), enumerating `A` with exact multiplicity `m w` at every `w`. -/
theorem discrete_multiplicity_enumeration {Ω A : Set ℂ}
    (_hΩ : IsOpen Ω) (hAΩ : A ⊆ Ω)
    (hacc : ∀ z ∈ Ω, z ∉ closure (A \ {z}))
    (m : ℂ → ℕ) (_hm : ∀ a ∈ A, 0 < m a) :
    A.Countable ∧
    ((∃ (N : ℕ) (z : Fin N → ℂ),
        (∀ i, z i ∈ A) ∧
        (∀ w : ℂ, (Finset.univ.filter (fun i ↦ z i = w)).card =
          if w ∈ A then m w else 0)) ∨
     (∃ z : ℕ → ℂ,
        (∀ n, z n ∈ A) ∧
        (∀ w : ℂ, HasSum (fun n ↦ if z n = w then (1 : ℕ) else 0)
          (if w ∈ A then m w else 0)))) := by
  classical
  have hcod := compl_mem_codiscreteWithin_of_no_limit_pt hAΩ hacc
  have hd : IsDiscrete A := by
    have hd' := isDiscrete_of_codiscreteWithin (s := A) hcod
    rwa [Set.inter_eq_self_of_subset_left hAΩ] at hd'
  have hA_count : A.Countable :=
    (HereditarilyLindelofSpace.isLindelof A).countable_of_isDiscrete hd
  refine ⟨hA_count, ?_⟩
  let Idx := Σ a : A, Fin (m a.1)
  have : Countable A := hA_count.to_subtype
  have : Countable Idx := inferInstance
  rcases finite_or_infinite Idx with hfin | hinf
  · left
    let _ : Fintype Idx := Fintype.ofFinite Idx
    let N := Fintype.card Idx
    let e : Fin N ≃ Idx := (Fintype.equivFin Idx).symm
    let z : Fin N → ℂ := fun i ↦ (e i).1.1
    refine ⟨N, z, fun i ↦ (e i).1.2, ?_⟩
    intro w
    by_cases hw : w ∈ A
    · simp only [hw, ↓reduceIte]
      symm
      rw [← Finset.card_fin (m w)]
      refine Finset.card_bij (fun (j : Fin (m w)) _ ↦ e.symm ⟨⟨w, hw⟩, j⟩) ?_ ?_ ?_
      · intro j _
        simp [z]
      · intro j₁ _ j₂ _ h
        have h' : (⟨⟨w, hw⟩, j₁⟩ : Idx) = ⟨⟨w, hw⟩, j₂⟩ := e.symm.injective h
        exact Fin.ext (congrArg (fun x : Idx ↦ x.2.val) h')
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, z] at hi
        rcases h_ei : e i with ⟨⟨u, hu⟩, j⟩
        have huw : u = w := by simpa [h_ei] using hi
        subst huw
        exact ⟨j, Finset.mem_univ j, e.symm_apply_eq.mpr h_ei.symm⟩
    · simp only [hw, ↓reduceIte]
      exact Finset.card_eq_zero.mpr
        (Finset.filter_eq_empty_iff.mpr fun i _ hi ↦ hw (hi ▸ (e i).1.2))
  · right
    let e : ℕ ≃ Idx := (nonempty_equiv_of_countable (α := ℕ) (β := Idx)).some
    let z : ℕ → ℂ := fun n ↦ (e n).1.1
    refine ⟨z, fun n ↦ (e n).1.2, ?_⟩
    intro w
    by_cases hw : w ∈ A
    · simp only [hw, ↓reduceIte]
      let φ : Fin (m w) → ℕ := fun j ↦ e.symm ⟨⟨w, hw⟩, j⟩
      have hφ_inj : Function.Injective φ := by
        intro j₁ j₂ h
        have h' : (⟨⟨w, hw⟩, j₁⟩ : Idx) = ⟨⟨w, hw⟩, j₂⟩ := e.symm.injective h
        exact Fin.ext (congrArg (fun x : Idx ↦ x.2.val) h')
      let S : Finset ℕ := Finset.univ.image φ
      have hsupp : ∀ n ∉ S, (if z n = w then (1 : ℕ) else 0) = 0 := by
        intro n hn
        split_ifs with hzn
        · exfalso
          rcases h_en : e n with ⟨⟨u, hu⟩, j⟩
          have huw : u = w := by simpa [z, h_en] using hzn
          subst huw
          exact hn (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, e.symm_apply_eq.mpr h_en.symm⟩)
        · rfl
      have hsumS : (∑ n ∈ S, if z n = w then (1 : ℕ) else 0) = m w := by
        have hones : ∀ n ∈ S, (if z n = w then (1 : ℕ) else 0) = 1 := by
          intro n hn
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hn
          simp [z, φ]
        rw [Finset.sum_congr rfl hones, Finset.sum_const, smul_eq_mul, mul_one,
          Finset.card_image_of_injective _ hφ_inj, Finset.card_fin]
      rw [← hsumS]
      exact hasSum_sum_of_ne_finset_zero hsupp
    · simp only [hw, ↓reduceIte]
      have hzero : (fun n ↦ if z n = w then (1 : ℕ) else 0) = fun _ ↦ 0 := by
        funext n
        have hne : z n ≠ w := fun h ↦ hw (h ▸ (e n).1.2)
        simp [hne]
      rw [hzero]
      exact hasSum_zero

/-- **Rudin RCA 15.10 (Nonvanishing at the origin)**:
Every entire function `f` with `f 0 ≠ 0` (without any external zero-enumeration hypothesis)
either has finitely many zeros (including zero zeros when `N = 0`) and factors as
`f(z) = exp(g(z)) ∏_{i < N} E_0(z / a_i)`, or has infinitely many zeros and factors as
`f(z) = exp(g(z)) ∏'_{n=0}^∞ E_{p_n}(z / a_n)` with `p_n = n`, entire `g`, `‖a_n‖ → ∞`, and `a`
listing all zeros of `f` with exact multiplicity. -/
theorem theorem15_10_nonzero_at_origin {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    (∃ (N : ℕ) (a : Fin N → ℂ) (g : ℂ → ℂ),
      Differentiable ℂ g ∧
      (∀ i, a i ≠ 0 ∧ f (a i) = 0) ∧
      (∀ w : ℂ, (Finset.univ.filter (fun i ↦ a i = w)).card = analyticOrderNatAt f w) ∧
      (∀ z : ℂ, f z = Complex.exp (g z) * ∏ i : Fin N, elementaryFactor 0 (z / a i))) ∨
    (∃ (a : ℕ → ℂ) (p : ℕ → ℕ) (g : ℂ → ℂ),
      p = (fun n ↦ n) ∧
      Differentiable ℂ g ∧
      (∀ n, a n ≠ 0 ∧ f (a n) = 0) ∧
      Tendsto (fun n ↦ ‖a n‖) Filter.atTop Filter.atTop ∧
      (∀ w : ℂ, HasSum (fun n ↦ if a n = w then (1 : ℕ) else 0) (analyticOrderNatAt f w)) ∧
      TendstoLocallyUniformlyOn
        (fun N z ↦ ∏ n ∈ Finset.range N, elementaryFactor (p n) (z / a n))
        (fun z ↦ ∏' n, elementaryFactor (p n) (z / a n)) Filter.atTop Set.univ ∧
      (∀ z : ℂ, f z = Complex.exp (g z) * ∏' n, elementaryFactor (p n) (z / a n))) := by
  classical
  let A : Set ℂ := {w : ℂ | f w = 0}
  let m : ℂ → ℕ := fun w ↦ analyticOrderNatAt f w
  have hacc : ∀ z ∈ (Set.univ : Set ℂ), z ∉ closure (A \ {z}) :=
    fun z hz ↦ zeros_have_no_accumulation isOpen_univ isPreconnected_univ
      hf.differentiableOn ⟨0, Set.mem_univ 0, h0⟩ hz
  have hm_pos : ∀ w ∈ A, 0 < m w := by
    intro w hw
    have hfin := analyticOrderAt_ne_top_of_entire_nonzero hf h0 w
    have hne0 : analyticOrderAt f w ≠ 0 := by
      intro hord0
      exact ((hf.analyticAt w).analyticOrderAt_eq_zero.mp hord0) hw
    have hcast := Nat.cast_analyticOrderNatAt hfin
    by_contra hle
    have hm0 : m w = 0 := Nat.eq_zero_of_not_pos hle
    apply hne0
    rw [← hcast]
    exact congrArg Nat.cast hm0
  have hm_eq : ∀ w : ℂ, (if w ∈ A then m w else 0) = analyticOrderNatAt f w := by
    intro w
    by_cases hw : w ∈ A
    · simp [hw, m]
    · have hfw : f w ≠ 0 := hw
      have hord0 : analyticOrderAt f w = 0 := (hf.analyticAt w).analyticOrderAt_eq_zero.mpr hfw
      simp [hw, analyticOrderNatAt, hord0]
  obtain ⟨_, hcases⟩ := discrete_multiplicity_enumeration isOpen_univ (Set.subset_univ A) hacc m hm_pos
  rcases hcases with ⟨N, a, haA, hcard⟩ | ⟨a, haA, hsum⟩
  · left
    have ha_zero : ∀ i, f (a i) = 0 := fun i ↦ haA i
    have hcard' : ∀ w : ℂ, (Finset.univ.filter (fun i ↦ a i = w)).card = analyticOrderNatAt f w :=
      fun w ↦ (hcard w).trans (hm_eq w)
    have hsum_fin : ∀ w : ℂ, (∑ i ∈ (Finset.univ : Finset (Fin N)), if a i = w then (1 : ℕ) else 0) =
        analyticOrderNatAt f w := by
      intro w
      rw [← hcard' w, Finset.card_filter]
    obtain ⟨g, hg, hfac⟩ := entire_function_factorization_finite (f := f) Finset.univ a hf h0
      (fun i _ ↦ ha_zero i) hsum_fin
    refine ⟨N, a, g, hg, fun i ↦ ⟨fun hi0 ↦ h0 (hi0 ▸ ha_zero i), ha_zero i⟩, hcard', hfac⟩
  · right
    have hsum' : ∀ w : ℂ, HasSum (fun n ↦ if a n = w then (1 : ℕ) else 0) (analyticOrderNatAt f w) :=
      fun w ↦ hm_eq w ▸ hsum w
    obtain ⟨ha0, hinfty⟩ := zero_enumeration_norm_tendsto_atTop hf h0 haA hsum'
    obtain ⟨p, g, hp, hg, hlim, hfac⟩ := entire_function_factorization_infinite hf h0 haA hsum'
    exact ⟨a, p, g, hp, hg, fun n ↦ ⟨ha0 n, haA n⟩, hinfty, hsum', hlim, hfac⟩

/-- **Rudin RCA 15.10 (General entire Weierstrass factorization)**:
Every nonzero entire function `f` factors unconditionally as
`f(z) = z^k exp(g(z)) ∏_{i < N} E_0(z / a_i)` (finite/empty nonzero zero list) or
`f(z) = z^k exp(g(z)) ∏'_{n=0}^∞ E_{p_n}(z / a_n)` (infinite nonzero zero list, with `p_n = n`
and `‖a_n‖ → ∞`), where `k = analyticOrderNatAt f 0`, `g` is entire, and `a` enumerates all
nonzero zeros of `f` with exact multiplicity `analyticOrderNatAt f w`. -/
theorem theorem15_10 {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) :
    let k := analyticOrderNatAt f 0
    (∃ (N : ℕ) (a : Fin N → ℂ) (g : ℂ → ℂ),
      Differentiable ℂ g ∧
      (∀ i, a i ≠ 0 ∧ f (a i) = 0) ∧
      (∀ w : ℂ, w ≠ 0 → (Finset.univ.filter (fun i ↦ a i = w)).card = analyticOrderNatAt f w) ∧
      (∀ z : ℂ, f z = z ^ k * Complex.exp (g z) *
        ∏ i : Fin N, elementaryFactor 0 (z / a i))) ∨
    (∃ (a : ℕ → ℂ) (p : ℕ → ℕ) (g : ℂ → ℂ),
      p = (fun n ↦ n) ∧
      Differentiable ℂ g ∧
      (∀ n, a n ≠ 0 ∧ f (a n) = 0) ∧
      Tendsto (fun n ↦ ‖a n‖) Filter.atTop Filter.atTop ∧
      (∀ w : ℂ, w ≠ 0 →
        HasSum (fun n ↦ if a n = w then (1 : ℕ) else 0) (analyticOrderNatAt f w)) ∧
      TendstoLocallyUniformlyOn
        (fun N z ↦ ∏ n ∈ Finset.range N, elementaryFactor (p n) (z / a n))
        (fun z ↦ ∏' n, elementaryFactor (p n) (z / a n)) Filter.atTop Set.univ ∧
      (∀ z : ℂ, f z = z ^ k * Complex.exp (g z) *
        ∏' n, elementaryFactor (p n) (z / a n))) := by
  dsimp only
  obtain ⟨h, hh, hh0, hfh⟩ := entire_remove_zero_at_origin hf hne
  let k := analyticOrderNatAt f 0
  have hord_eq : ∀ w : ℂ, w ≠ 0 → analyticOrderNatAt h w = analyticOrderNatAt f w := by
    intro w hw
    have hf_eq : f = (fun z ↦ z ^ k) * h := funext hfh
    have hpow_an : AnalyticAt ℂ (fun z : ℂ ↦ z ^ k) w := analyticAt_id.pow k
    have hpow_ord : analyticOrderAt (fun z : ℂ ↦ z ^ k) w = 0 :=
      hpow_an.analyticOrderAt_eq_zero.mpr (pow_ne_zero k hw)
    have hord : analyticOrderAt f w = analyticOrderAt h w := by
      rw [hf_eq, analyticOrderAt_mul hpow_an (hh.analyticAt w), hpow_ord, zero_add]
    simp only [analyticOrderNatAt, hord]
  rcases theorem15_10_nonzero_at_origin hh hh0 with
    ⟨N, a, g, hg, ha, hcard, hfac⟩ | ⟨a, p, g, hp, hg, ha, hinfty, hsum, hlim, hfac⟩
  · left
    refine ⟨N, a, g, hg, ?_, ?_, ?_⟩
    · intro i
      exact ⟨(ha i).1, by rw [hfh (a i), (ha i).2, mul_zero]⟩
    · intro w hw
      rw [hcard w, hord_eq w hw]
    · intro z
      rw [hfh z, hfac z, mul_assoc]
  · right
    refine ⟨a, p, g, hp, hg, ?_, hinfty, ?_, hlim, ?_⟩
    · intro n
      exact ⟨(ha n).1, by rw [hfh (a n), (ha n).2, mul_zero]⟩
    · intro w hw
      rw [← hord_eq w hw]
      exact hsum w
    · intro z
      rw [hfh z, hfac z, mul_assoc]

/-! ## 15.11 & 15.1: Prescribed Zeros on Proper Open Subsets of the Riemann Sphere -/

/-- Holomorphicity on an open subset `Ω` of the Riemann sphere `ℂ ∪ {∞}`:
holomorphic on the finite chart `Ω ∩ ℂ`, and analytic at `0` in the chart `w ↦ 1 / w` when `∞ ∈ Ω`. -/
def HolomorphicOnSphere (Ω : Set RudinRCA.Chapter13.RiemannSphere)
    (f : RudinRCA.Chapter13.RiemannSphere → ℂ) : Prop :=
  DifferentiableOn ℂ (fun z : ℂ ↦ f (z : RudinRCA.Chapter13.RiemannSphere))
    (((↑) : ℂ → RudinRCA.Chapter13.RiemannSphere) ⁻¹' Ω) ∧
  ((∞ : RudinRCA.Chapter13.RiemannSphere) ∈ Ω →
    AnalyticAt ℂ (fun w : ℂ ↦
      if w = 0 then f ∞ else f ((w⁻¹ : ℂ) : RudinRCA.Chapter13.RiemannSphere)) 0)

/-- Zero order of `f : RiemannSphere → ℂ` at `p ∈ RiemannSphere`, computed in the standard local
chart (`ζ ↦ ζ` at finite points and `w ↦ w⁻¹` at `∞`). -/
def sphereZeroOrder (f : RudinRCA.Chapter13.RiemannSphere → ℂ)
    (p : RudinRCA.Chapter13.RiemannSphere) : ℕ∞ :=
  OnePoint.rec
    (analyticOrderAt (fun w : ℂ ↦
      if w = 0 then f ∞ else f ((w⁻¹ : ℂ) : RudinRCA.Chapter13.RiemannSphere)) 0)
    (fun z : ℂ ↦ analyticOrderAt (fun ζ : ℂ ↦ f (ζ : RudinRCA.Chapter13.RiemannSphere)) z)
    p

/-- Natural-number zero multiplicity on the Riemann sphere. -/
def sphereZeroOrderNat (f : RudinRCA.Chapter13.RiemannSphere → ℂ)
    (p : RudinRCA.Chapter13.RiemannSphere) : ℕ :=
  (sphereZeroOrder f p).toNat

@[simp] theorem sphereZeroOrder_infty (f : RudinRCA.Chapter13.RiemannSphere → ℂ) :
    sphereZeroOrder f ∞ =
      analyticOrderAt (fun w : ℂ ↦
        if w = 0 then f ∞ else f ((w⁻¹ : ℂ) : RudinRCA.Chapter13.RiemannSphere)) 0 :=
  rfl

@[simp] theorem sphereZeroOrder_coe (f : RudinRCA.Chapter13.RiemannSphere → ℂ) (z : ℂ) :
    sphereZeroOrder f (z : RudinRCA.Chapter13.RiemannSphere) =
      analyticOrderAt (fun ζ : ℂ ↦ f (ζ : RudinRCA.Chapter13.RiemannSphere)) z :=
  rfl

/-- Helper for finite zero lists: `P(w) = ∏_{i < N} (w - z_i)` is entire with exact multiplicity
equal to the fiber cardinality at every `w : ℂ`. -/
theorem finite_linear_product {N : ℕ} (z : Fin N → ℂ) :
    let P : ℂ → ℂ := fun w ↦ ∏ i : Fin N, (w - z i)
    Differentiable ℂ P ∧
    (∀ w : ℂ, P w = 0 ↔ ∃ i, z i = w) ∧
    (∀ w : ℂ, analyticOrderAt P w = ↑((Finset.univ.filter (fun i ↦ z i = w)).card)) ∧
    (∀ w : ℂ, analyticOrderNatAt P w = (Finset.univ.filter (fun i ↦ z i = w)).card) := by
  classical
  dsimp only
  have hP : Differentiable ℂ (fun w ↦ ∏ i : Fin N, (w - z i)) :=
    Differentiable.fun_finsetProd fun i _ ↦ differentiable_id.sub_const (z i)
  have hzero : ∀ w : ℂ, (∏ i : Fin N, (w - z i)) = 0 ↔ ∃ i, z i = w := by
    intro w
    rw [Finset.prod_eq_zero_iff]
    simp [sub_eq_zero, eq_comm]
  have hord : ∀ w : ℂ,
      analyticOrderAt (fun ζ ↦ ∏ i : Fin N, (ζ - z i)) w =
        ↑((Finset.univ.filter (fun i ↦ z i = w)).card) := by
    intro w
    have han : ∀ i ∈ (Finset.univ : Finset (Fin N)), AnalyticAt ℂ (fun ζ : ℂ ↦ ζ - z i) w :=
      fun i _ ↦ by fun_prop
    rw [analyticOrderAt_finset_product Finset.univ han]
    have hterm : ∀ i : Fin N, analyticOrderAt (fun ζ : ℂ ↦ ζ - z i) w =
        if z i = w then (1 : ℕ∞) else 0 := by
      intro i
      by_cases hi : z i = w
      · subst hi
        simp
      · simp only [hi, ↓reduceIte]
        exact analyticOrderAt_id_sub_const_of_ne (Ne.symm hi)
    simp_rw [hterm]
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> simp
  refine ⟨hP, hzero, hord, fun w ↦ ?_⟩
  simp [analyticOrderNatAt, hord w]

/-- Helper for `exists_holomorphic_prescribed_zeros_plane` when `0 ∉ Ω₀`. -/
private theorem exists_holomorphic_prescribed_zeros_plane_zero_notMem {Ω₀ A₀ : Set ℂ}
    (hΩ₀ : IsOpen Ω₀) (h0 : (0 : ℂ) ∉ Ω₀) (hA₀ : A₀ ⊆ Ω₀)
    (hacc : ∀ z ∈ Ω₀, z ∉ closure (A₀ \ {z}))
    {m₀ : ℂ → ℕ} (hm₀ : ∀ a ∈ A₀, 0 < m₀ a) :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f Ω₀ ∧
      (∀ z ∈ Ω₀, f z = 0 ↔ z ∈ A₀) ∧
      (∀ z ∈ Ω₀, analyticOrderAt f z ≠ ⊤) ∧
      (∀ z ∈ Ω₀, analyticOrderNatAt f z = if z ∈ A₀ then m₀ z else 0) := by
  classical
  obtain ⟨_, hcases⟩ := discrete_multiplicity_enumeration hΩ₀ hA₀ hacc m₀ hm₀
  rcases hcases with ⟨N, z, hzA, hcard⟩ | ⟨z, hzA, hcount⟩
  · obtain ⟨hP, hPzero, hPord, hPnat⟩ := finite_linear_product z
    refine ⟨fun w ↦ ∏ i : Fin N, (w - z i), hP.differentiableOn, ?_, ?_, ?_⟩
    · intro w _
      rw [hPzero w]
      constructor
      · rintro ⟨i, rfl⟩
        exact hzA i
      · intro hwA
        have hpos : 0 < (Finset.univ.filter (fun i ↦ z i = w)).card := by
          simp only [hcard w, hwA, ↓reduceIte]
          exact hm₀ w hwA
        obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
        exact ⟨i, (Finset.mem_filter.mp hi).2⟩
    · intro w _
      rw [hPord w]
      exact ENat.natCast_ne_top _
    · intro w _
      rw [hPnat w, hcard w]
  · have hcompl_ne : Ω₀ᶜ.Nonempty := ⟨0, h0⟩
    have hcompl_closed : IsClosed Ω₀ᶜ := hΩ₀.isClosed_compl
    have hzΩ : ∀ n, z n ∈ Ω₀ := fun n ↦ hA₀ (hzA n)
    have hz0 : ∀ n, z n ≠ 0 := fun n hn ↦ h0 (hn ▸ hzΩ n)
    have hex_α : ∀ n, ∃ α ∈ Ω₀ᶜ, Metric.infDist (z n) Ω₀ᶜ = dist (z n) α :=
      fun n ↦ hcompl_closed.exists_infDist_eq_dist hcompl_ne (z n)
    choose α hα_mem hα_dist using hex_α
    have hzn_sub_ne : ∀ n, z n - α n ≠ 0 :=
      fun n h ↦ hα_mem n (sub_eq_zero.mp h ▸ hzΩ n)
    have hw_sub_ne : ∀ n, ∀ w ∈ Ω₀, w - α n ≠ 0 :=
      fun n w hw h ↦ hα_mem n (sub_eq_zero.mp h ▸ hw)
    let F : ℕ → ℂ → ℂ := fun n w ↦
      if Metric.infDist (z n) Ω₀ᶜ ≤ 1 then
        elementaryFactor n ((z n - α n) / (w - α n))
      else
        elementaryFactor n (w / z n)
    have hF_diff : ∀ n, DifferentiableOn ℂ (F n) Ω₀ := by
      intro n
      dsimp only [F]
      split_ifs
      · refine (differentiable_elementaryFactor n).comp_differentiableOn ?_
        exact (differentiableOn_const (z n - α n)).div
          (differentiableOn_id.sub (differentiableOn_const (α n)))
          (fun w hw ↦ hw_sub_ne n w hw)
      · exact ((differentiable_elementaryFactor n).comp
          (differentiable_id.div_const (z n))).differentiableOn
    have hF_ord : ∀ n, ∀ w ∈ Ω₀,
        analyticOrderAt (F n) w = if z n = w then 1 else 0 := by
      intro n w hw
      by_cases hdist : Metric.infDist (z n) Ω₀ᶜ ≤ 1
      · have hFn : F n = fun ζ ↦ elementaryFactor n ((z n - α n) / (ζ - α n)) := by
          funext ζ
          simp [F, hdist]
        rw [hFn]
        let ψ : ℂ → ℂ := fun ζ ↦ (z n - α n) / (ζ - α n)
        have hψ_an : AnalyticAt ℂ ψ w :=
          analyticAt_const.div (analyticAt_id.sub analyticAt_const) (hw_sub_ne n w hw)
        have hψ_deriv : HasDerivAt ψ (-(z n - α n) / (w - α n) ^ 2) w := by
          have hd := (hasDerivAt_const w (z n - α n)).div
            ((hasDerivAt_id w).sub_const (α n)) (hw_sub_ne n w hw)
          dsimp only [id] at hd
          change HasDerivAt ψ _ w at hd
          exact hd.congr_deriv (by ring)
        have hψ_ne : deriv ψ w ≠ 0 := by
          rw [hψ_deriv.deriv]
          exact div_ne_zero (neg_ne_zero.mpr (hzn_sub_ne n)) (pow_ne_zero 2 (hw_sub_ne n w hw))
        change analyticOrderAt (elementaryFactor n ∘ ψ) w = _
        rw [analyticOrderAt_comp_of_deriv_ne_zero hψ_an hψ_ne, analyticOrderAt_elementaryFactor]
        have h1 : ψ w = 1 ↔ z n = w := by
          dsimp [ψ]
          rw [div_eq_one_iff_eq (hw_sub_ne n w hw), sub_left_inj]
        by_cases hzw : z n = w
        · simp [h1.mpr hzw, hzw]
        · have hne1 : ψ w ≠ 1 := fun h ↦ hzw (h1.mp h)
          simp [hne1, hzw]
      · have hFn : F n = fun ζ ↦ elementaryFactor n (ζ / z n) := by
          funext ζ
          simp [F, hdist]
        rw [hFn, analyticOrderAt_scaled_elementaryFactor n (hz0 n) w]
        by_cases hzw : z n = w
        · simp [hzw]
        · simp [hzw, Ne.symm hzw]
    have hF_nonzero : ∀ n, ∀ w ∈ Ω₀, ∃ u ∈ connectedComponentIn Ω₀ w, F n u ≠ 0 := by
      intro n w hw
      have hcomp_open : IsOpen (connectedComponentIn Ω₀ w) := hΩ₀.connectedComponentIn
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hcomp_open w (mem_connectedComponentIn hw)
      by_cases hzw : z n = w
      · let u : ℂ := w + (r / 2 : ℝ)
        have hu_ball : u ∈ Metric.ball w r := by
          rw [Metric.mem_ball, dist_eq_norm]
          have hsub : u - w = ((r / 2 : ℝ) : ℂ) := by simp [u]
          have hnorm : ‖u - w‖ = r / 2 := by
            rw [hsub, Complex.norm_of_nonneg (half_pos hr).le]
          linarith
        have hu_comp : u ∈ connectedComponentIn Ω₀ w := hball hu_ball
        have hu_Ω : u ∈ Ω₀ := connectedComponentIn_subset Ω₀ w hu_comp
        have hzu : z n ≠ u := by
          rw [hzw]
          intro heq
          have : (r / 2 : ℝ) = (0 : ℂ) := by linear_combination -heq
          have hr0 : r / 2 = 0 := Complex.ofReal_eq_zero.mp this
          linarith
        have hord0 : analyticOrderAt (F n) u = 0 := by simp [hF_ord n u hu_Ω, hzu]
        exact ⟨u, hu_comp, ((hF_diff n).analyticAt (hΩ₀.mem_nhds hu_Ω)).analyticOrderAt_eq_zero.mp hord0⟩
      · have hord0 : analyticOrderAt (F n) w = 0 := by simp [hF_ord n w hw, hzw]
        exact ⟨w, mem_connectedComponentIn hw,
          ((hF_diff n).analyticAt (hΩ₀.mem_nhds hw)).analyticOrderAt_eq_zero.mp hord0⟩
    have hseries : TendstoLocallyUniformlyOn
        (fun N w ↦ ∑ n ∈ Finset.range N, ‖1 - F n w‖)
        (fun w ↦ ∑' n, ‖1 - F n w‖) Filter.atTop Ω₀ := by
      rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ₀]
      intro K hKΩ hK
      rcases K.eq_empty_or_nonempty with rfl | hKne
      · exact tendstoUniformlyOn_empty
      · obtain ⟨w_min, hw_min_K, hw_min⟩ :=
          hK.exists_isMinOn hKne (continuous_infDist_pt Ω₀ᶜ).continuousOn
        have hw_min_not : w_min ∉ Ω₀ᶜ := not_not.mpr (hKΩ hw_min_K)
        have hpos_min : 0 < Metric.infDist w_min Ω₀ᶜ :=
          (hcompl_closed.notMem_iff_infDist_pos hcompl_ne).mp hw_min_not
        let δ : ℝ := min (Metric.infDist w_min Ω₀ᶜ) 1
        have hδ_pos : 0 < δ := lt_min hpos_min zero_lt_one
        have hδ_le_one : δ ≤ 1 := min_le_right _ _
        have hδ_K : ∀ w ∈ K, δ ≤ Metric.infDist w Ω₀ᶜ :=
          fun w hw ↦ (min_le_left _ _).trans (hw_min hw)
        obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn (f := fun w : ℂ ↦ w) continuousOn_id
        let R : ℝ := max R₀ 3
        have hR3 : 3 ≤ R := le_max_right _ _
        have hR_K : ∀ w ∈ K, ‖w‖ ≤ R := fun w hw ↦ (hR₀ w hw).trans (le_max_left _ _)
        let L : Set ℂ := Metric.closedBall (0 : ℂ) (2 * R) ∩
          {w : ℂ | δ / 2 ≤ Metric.infDist w Ω₀ᶜ}
        have hL_compact : IsCompact L :=
          (isCompact_closedBall (0 : ℂ) (2 * R)).inter_right
            (isClosed_le continuous_const (continuous_infDist_pt Ω₀ᶜ))
        have hL_sub : L ⊆ Ω₀ := by
          intro w hw
          by_contra hw_not
          have hzero_dist : Metric.infDist w Ω₀ᶜ = 0 := Metric.infDist_zero_of_mem hw_not
          have : δ / 2 ≤ 0 := hzero_dist ▸ hw.2
          linarith
        have hfiber : ∀ w ∈ Ω₀, (z ⁻¹' {w}).Finite :=
          fun w hw ↦ finite_fiber_of_hasSum_count z w _ (hcount w)
        have hevL := eventually_notMem_compact_of_no_limit_pt hA₀ hacc hL_compact hL_sub hzA hfiber
        have hgeo : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1)) :=
          (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).comp_injective
            (fun n m h ↦ Nat.add_right_cancel h)
        refine tendstoUniformlyOn_tsum_nat_eventually hgeo ?_
        filter_upwards [hevL] with n hnL w hwK
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        have hnotL : 2 * R < ‖z n‖ ∨ Metric.infDist (z n) Ω₀ᶜ < δ / 2 := by
          by_contra h
          push Not at h
          exact hnL ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using h.1, h.2⟩
        dsimp only [F]
        split_ifs with hdist
        · have hquot_half : ‖(z n - α n) / (w - α n)‖ ≤ 1 / 2 := by
            have hnum_eq : ‖z n - α n‖ = Metric.infDist (z n) Ω₀ᶜ := by
              rw [hα_dist n, dist_eq_norm]
            rcases hnotL with hbig | hsmall
            · have hnum1 : ‖z n - α n‖ ≤ 1 := hnum_eq.trans_le hdist
              have hwR : ‖w‖ ≤ R := hR_K w hwK
              have htri : ‖z n‖ ≤ ‖z n - α n‖ + ‖w - α n‖ + ‖w‖ := by
                have h1 := norm_add_le ((z n - α n) - (w - α n)) w
                have h2 := norm_sub_le (z n - α n) (w - α n)
                have hid : (z n - α n) - (w - α n) + w = z n := by ring
                rw [hid] at h1
                linarith
              have hden2 : 2 ≤ ‖w - α n‖ := by linarith
              have hden_pos : 0 < ‖w - α n‖ := by linarith
              rw [norm_div, div_le_iff₀ hden_pos]
              linarith
            · have hden_δ : δ ≤ ‖w - α n‖ := by
                rw [← dist_eq_norm]
                exact (hδ_K w hwK).trans (Metric.infDist_le_dist_of_mem (hα_mem n))
              have hden_pos : 0 < ‖w - α n‖ := lt_of_lt_of_le hδ_pos hden_δ
              rw [norm_div, div_le_iff₀ hden_pos]
              linarith [hnum_eq]
          exact (norm_one_sub_elementaryFactor_le n _ (hquot_half.trans (by norm_num))).trans
            (pow_le_pow_left₀ (norm_nonneg _) hquot_half (n + 1))
        · rcases hnotL with hbig | hsmall
          · have hquot_half : ‖w / z n‖ ≤ 1 / 2 := by
              have hwR : ‖w‖ ≤ R := hR_K w hwK
              have hzn_pos : 0 < ‖z n‖ := by linarith
              rw [norm_div, div_le_iff₀ hzn_pos]
              linarith
            exact (norm_one_sub_elementaryFactor_le n _ (hquot_half.trans (by norm_num))).trans
              (pow_le_pow_left₀ (norm_nonneg _) hquot_half (n + 1))
          · exfalso
            linarith
    obtain ⟨_, hhol, hmult⟩ := holomorphic_product_multiplicity hΩ₀ hF_diff hF_nonzero ⟨_, hseries⟩
    let f : ℂ → ℂ := fun w ↦ ∏' n, F n w
    have hf_fin : ∀ w ∈ Ω₀, analyticOrderAt f w ≠ ⊤ := fun w hw ↦ (hmult w hw).2.1
    have hf_ord : ∀ w ∈ Ω₀, analyticOrderNatAt f w = if w ∈ A₀ then m₀ w else 0 := by
      intro w hw
      rw [(hmult w hw).2.2.1]
      have hterm : (fun n ↦ analyticOrderNatAt (F n) w) =
          fun n ↦ if z n = w then (1 : ℕ) else 0 := by
        funext n
        simp only [analyticOrderNatAt, hF_ord n w hw]
        split_ifs <;> simp
      rw [hterm, (hcount w).tsum_eq]
    refine ⟨f, hhol, ?_, hf_fin, hf_ord⟩
    intro w hw
    have han : AnalyticAt ℂ f w := hhol.analyticAt (hΩ₀.mem_nhds hw)
    have h0_iff : f w = 0 ↔ analyticOrderNatAt f w ≠ 0 := by
      constructor
      · intro hfw hnat0
        have hord0 : analyticOrderAt f w = 0 := by
          rw [← Nat.cast_analyticOrderNatAt (hf_fin w hw), hnat0, Nat.cast_zero]
        exact (han.analyticOrderAt_eq_zero.mp hord0) hfw
      · intro hnat_ne
        by_contra hfw
        have hord0 : analyticOrderAt f w = 0 := han.analyticOrderAt_eq_zero.mpr hfw
        exact hnat_ne (by simp [analyticOrderNatAt, hord0])
    rw [h0_iff, hf_ord w hw]
    by_cases hwA : w ∈ A₀
    · simp [hwA, (hm₀ w hwA).ne']
    · simp [hwA]

/-- Planar case of Theorem 15.11: for any open `Ω₀ ⊆ ℂ` (both `Ω₀ = Set.univ` and `Ω₀ ≠ Set.univ`),
any `A₀ ⊆ Ω₀` without limit points in `Ω₀`, and positive multiplicities `m₀`, there exists
`f ∈ H(Ω₀)` whose zero set in `Ω₀` is `A₀` with exact zero multiplicity `m₀` at every `a ∈ A₀`. -/
theorem exists_holomorphic_prescribed_zeros_plane {Ω₀ A₀ : Set ℂ}
    (hΩ₀ : IsOpen Ω₀) (hA₀ : A₀ ⊆ Ω₀)
    (hacc : ∀ z ∈ Ω₀, z ∉ closure (A₀ \ {z}))
    {m₀ : ℂ → ℕ} (hm₀ : ∀ a ∈ A₀, 0 < m₀ a) :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f Ω₀ ∧
      (∀ z ∈ Ω₀, f z = 0 ↔ z ∈ A₀) ∧
      (∀ z ∈ Ω₀, analyticOrderAt f z ≠ ⊤) ∧
      (∀ z ∈ Ω₀, analyticOrderNatAt f z = if z ∈ A₀ then m₀ z else 0) := by
  classical
  by_cases hΩ_univ : Ω₀ = Set.univ
  · subst hΩ_univ
    let A' : Set ℂ := A₀ \ {0}
    have hacc' : ∀ z ∈ (Set.univ : Set ℂ), z ∉ closure (A' \ {z}) := by
      intro z hz hmem
      refine hacc z hz (closure_mono ?_ hmem)
      exact Set.sdiff_subset_sdiff_left Set.sdiff_subset
    have hm' : ∀ a ∈ A', 0 < m₀ a := fun a ha ↦ hm₀ a ha.1
    have hP_ex : ∃ P : ℂ → ℂ,
        Differentiable ℂ P ∧ P 0 ≠ 0 ∧
        (∀ w : ℂ, P w = 0 ↔ w ∈ A') ∧
        (∀ w : ℂ, analyticOrderAt P w ≠ ⊤) ∧
        (∀ w : ℂ, analyticOrderNatAt P w = if w ∈ A' then m₀ w else 0) := by
      obtain ⟨_, hcases⟩ := discrete_multiplicity_enumeration isOpen_univ
        (Set.subset_univ A') hacc' m₀ hm'
      rcases hcases with ⟨N, a, haA', hcard⟩ | ⟨a, haA', hcount⟩
      · obtain ⟨hP, hPzero, hPord, hPnat⟩ := finite_linear_product a
        have hP0 : (∏ i : Fin N, ((0 : ℂ) - a i)) ≠ 0 := by
          intro h0
          obtain ⟨i, hi0⟩ := (hPzero 0).mp h0
          exact (haA' i).2 hi0
        refine ⟨fun w ↦ ∏ i : Fin N, (w - a i), hP, hP0, ?_, ?_, ?_⟩
        · intro w
          rw [hPzero w]
          constructor
          · rintro ⟨i, rfl⟩
            exact haA' i
          · intro hwA'
            have hpos : 0 < (Finset.univ.filter (fun i ↦ a i = w)).card := by
              simp only [hcard w, hwA', ↓reduceIte]
              exact hm' w hwA'
            obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
            exact ⟨i, (Finset.mem_filter.mp hi).2⟩
        · intro w
          rw [hPord w]
          exact ENat.natCast_ne_top _
        · intro w
          rw [hPnat w, hcard w]
          by_cases hw : w ∈ A' <;> simp [hw]
      · have ha0 : ∀ n, a n ≠ 0 := fun n ↦ (haA' n).2
        have hfiber : ∀ w ∈ (Set.univ : Set ℂ), (a ⁻¹' {w}).Finite :=
          fun w _ ↦ finite_fiber_of_hasSum_count a w _ (hcount w)
        have hinfty : Tendsto (fun n ↦ ‖a n‖) Filter.atTop Filter.atTop := by
          rw [Filter.tendsto_atTop_atTop]
          intro b
          let R : ℝ := max b 0
          have hev := eventually_notMem_compact_of_no_limit_pt (Set.subset_univ A') hacc'
            (isCompact_closedBall (0 : ℂ) R) (Set.subset_univ _) haA' hfiber
          obtain ⟨N, hN⟩ := eventually_atTop.mp hev
          refine ⟨N, fun n hn ↦ ?_⟩
          have hnot : ¬ ‖a n‖ ≤ R := by
            simpa [Metric.mem_closedBall, dist_zero_right] using hN n hn
          exact (le_max_left b 0).trans (le_of_lt (not_le.mp hnot))
        obtain ⟨_, hP, hprop⟩ := entire_primary_product (p := fun n ↦ n) ha0 hinfty
          (fun r hr ↦ summable_primary_majorant_nat ha0 hinfty hr)
        let P : ℂ → ℂ := fun w ↦ ∏' n, elementaryFactor n (w / a n)
        have hP0 : P 0 ≠ 0 := by
          intro h0
          obtain ⟨n, hn⟩ := (hprop 0).1.mp h0
          exact ha0 n hn.symm
        refine ⟨P, hP, hP0, ?_, fun w ↦ (hprop w).2.1, ?_⟩
        · intro w
          rw [(hprop w).1]
          constructor
          · rintro ⟨n, rfl⟩
            exact haA' n
          · intro hwA'
            by_contra hnone
            push Not at hnone
            have hzero_fn : (fun n ↦ if a n = w then (1 : ℕ) else 0) = fun _ ↦ 0 := by
              funext n
              have hne : a n ≠ w := Ne.symm (hnone n)
              simp [hne]
            have h0eq : m₀ w = 0 := by
              have hc := hcount w
              simp only [hwA', ↓reduceIte, hzero_fn] at hc
              exact hasSum_zero.unique hc |>.symm
            exact (hm' w hwA').ne' h0eq
        · intro w
          rw [(hprop w).2.2]
          have hcongr : (fun n ↦ if w = a n then (1 : ℕ) else 0) =
              fun n ↦ if a n = w then (1 : ℕ) else 0 := by
            funext n
            simp [eq_comm]
          rw [hcongr, (hcount w).tsum_eq]
          by_cases hw : w ∈ A' <;> simp [hw]
    obtain ⟨P, hP, hP0, hPzero, hPfin, hPnat⟩ := hP_ex
    let k : ℕ := if (0 : ℂ) ∈ A₀ then m₀ 0 else 0
    let f : ℂ → ℂ := fun w ↦ w ^ k * P w
    have hf : Differentiable ℂ f := (differentiable_id.pow k).mul hP
    have hf_ord : ∀ w : ℂ, analyticOrderAt f w = ↑(if w ∈ A₀ then m₀ w else 0) := by
      intro w
      have hpow_an : AnalyticAt ℂ (fun ζ : ℂ ↦ ζ ^ k) w := by fun_prop
      change analyticOrderAt ((fun ζ : ℂ ↦ ζ ^ k) * P) w = _
      rw [analyticOrderAt_mul hpow_an (hP.analyticAt w)]
      by_cases hw0 : w = 0
      · subst hw0
        have hP_ord0 : analyticOrderAt P 0 = 0 := (hP.analyticAt 0).analyticOrderAt_eq_zero.mpr hP0
        have hpow_ord0 : analyticOrderAt (fun ζ : ℂ ↦ ζ ^ k) 0 = (k : ℕ∞) := by
          change analyticOrderAt ((fun x : ℂ ↦ x) ^ k) 0 = (k : ℕ∞)
          simpa using analyticOrderAt_centeredMonomial (𝕜 := ℂ) (z₀ := (0 : ℂ)) (n := k)
        rw [hpow_ord0, hP_ord0, add_zero]
      · have hpow_ord : analyticOrderAt (fun ζ : ℂ ↦ ζ ^ k) w = 0 :=
          hpow_an.analyticOrderAt_eq_zero.mpr (pow_ne_zero k hw0)
        rw [hpow_ord, zero_add, ← Nat.cast_analyticOrderNatAt (hPfin w), hPnat w]
        have hA'_iff : w ∈ A' ↔ w ∈ A₀ := ⟨fun h ↦ h.1, fun h ↦ ⟨h, hw0⟩⟩
        simp [hA'_iff]
    refine ⟨f, hf.differentiableOn, ?_, ?_, ?_⟩
    · intro w _
      dsimp only [f]
      rw [mul_eq_zero]
      by_cases hw0 : w = 0
      · subst hw0
        simp only [hP0, or_false]
        by_cases h0A : (0 : ℂ) ∈ A₀
        · simp [k, h0A, (hm₀ 0 h0A).ne']
        · simp [k, h0A]
      · simp only [pow_ne_zero k hw0, false_or, hPzero w, A', Set.mem_sdiff, Set.mem_singleton_iff,
          hw0, not_false_eq_true, and_true]
    · intro w _
      rw [hf_ord w]
      exact ENat.natCast_ne_top _
    · intro w _
      by_cases hwA : w ∈ A₀ <;> simp [analyticOrderNatAt, hf_ord w, hwA]
  · obtain ⟨w₀, hw₀⟩ := Set.nonempty_compl.mpr hΩ_univ
    let Ω' : Set ℂ := (fun ζ ↦ ζ + w₀) ⁻¹' Ω₀
    let A' : Set ℂ := (fun ζ ↦ ζ + w₀) ⁻¹' A₀
    let m' : ℂ → ℕ := fun ζ ↦ m₀ (ζ + w₀)
    have hΩ' : IsOpen Ω' := hΩ₀.preimage (continuous_id.add continuous_const)
    have h0' : (0 : ℂ) ∉ Ω' := by simpa [Ω'] using hw₀
    have hA' : A' ⊆ Ω' := Set.preimage_mono hA₀
    have hacc' : ∀ ζ ∈ Ω', ζ ∉ closure (A' \ {ζ}) := by
      intro ζ hζ hmem
      have himg : (fun u ↦ u + w₀) '' (A' \ {ζ}) ⊆ A₀ \ {ζ + w₀} := by
        rintro _ ⟨u, ⟨huA, huζ⟩, rfl⟩
        exact ⟨huA, fun h ↦ huζ (add_right_cancel h)⟩
      have hcl := image_closure_subset_closure_image (continuous_id.add continuous_const)
        (Set.mem_image_of_mem (fun u ↦ u + w₀) hmem)
      exact hacc (ζ + w₀) hζ (closure_mono himg hcl)
    have hm' : ∀ a ∈ A', 0 < m' a := fun a ha ↦ hm₀ (a + w₀) ha
    obtain ⟨F, hF_diff, hF_zero, hF_fin, hF_ord⟩ :=
      exists_holomorphic_prescribed_zeros_plane_zero_notMem hΩ' h0' hA' hacc' hm'
    let f : ℂ → ℂ := fun z ↦ F (z - w₀)
    have hf_diff : DifferentiableOn ℂ f Ω₀ := by
      refine hF_diff.comp (differentiableOn_id.sub (differentiableOn_const w₀)) ?_
      intro z hz
      simpa [Ω'] using hz
    have hf_ord_eq : ∀ z : ℂ, analyticOrderAt f z = analyticOrderAt F (z - w₀) := by
      intro z
      have hτ_an : AnalyticAt ℂ (fun u : ℂ ↦ u - w₀) z := analyticAt_id.sub analyticAt_const
      have hτ_hd : HasDerivAt (fun u : ℂ ↦ u - w₀) 1 z := by
        simpa using (hasDerivAt_id z).sub_const w₀
      have hτ_d : deriv (fun u : ℂ ↦ u - w₀) z ≠ 0 := by
        rw [hτ_hd.deriv]
        exact one_ne_zero
      exact analyticOrderAt_comp_of_deriv_ne_zero hτ_an hτ_d
    refine ⟨f, hf_diff, ?_, ?_, ?_⟩
    · intro z hz
      have hz' : z - w₀ ∈ Ω' := by simpa [Ω'] using hz
      simpa [f, A'] using hF_zero (z - w₀) hz'
    · intro z hz
      rw [hf_ord_eq z]
      exact hF_fin (z - w₀) (by simpa [Ω'] using hz)
    · intro z hz
      have hz' : z - w₀ ∈ Ω' := by simpa [Ω'] using hz
      have hnat : analyticOrderNatAt f z = analyticOrderNatAt F (z - w₀) := by
        simp [analyticOrderNatAt, hf_ord_eq z]
      rw [hnat, hF_ord (z - w₀) hz']
      by_cases hzA : z ∈ A₀ <;> simp [A', m', hzA]

/-- **Rudin RCA 15.11** (Prescribed zeros on proper open subsets of the Riemann sphere):
Let `Ω` be a **proper open subset** of `RiemannSphere` (`IsOpen Ω`, `Ω ≠ Set.univ`), `A ⊆ Ω` be a
subset without limit points in `Ω` (`∀ p ∈ Ω, p ∉ closure (A \ {p})`), and `m : RiemannSphere → ℕ`
satisfy `0 < m a` for every `a ∈ A`. Then there exists `f : RiemannSphere → ℂ` holomorphic on `Ω`
whose zero set in `Ω` is `A` and whose zero multiplicity at every `a ∈ A` is `m a` (and `0` on
`Ω \ A`). -/
theorem theorem15_11 {Ω A : Set RudinRCA.Chapter13.RiemannSphere}
    (hΩ : IsOpen Ω) (hΩ_ne : Ω ≠ Set.univ) (hAΩ : A ⊆ Ω)
    (hacc : ∀ p ∈ Ω, p ∉ closure (A \ {p}))
    {m : RudinRCA.Chapter13.RiemannSphere → ℕ} (hm : ∀ a ∈ A, 0 < m a) :
    ∃ f : RudinRCA.Chapter13.RiemannSphere → ℂ,
      HolomorphicOnSphere Ω f ∧
      (∀ p ∈ Ω, f p = 0 ↔ p ∈ A) ∧
      (∀ p ∈ Ω, sphereZeroOrder f p ≠ ⊤) ∧
      (∀ a ∈ A, sphereZeroOrderNat f a = m a) ∧
      (∀ p ∈ Ω, sphereZeroOrderNat f p = if p ∈ A then m p else 0) := by
  classical
  by_cases hinf : (∞ : RudinRCA.Chapter13.RiemannSphere) ∈ Ω
  · obtain ⟨p₀, hp₀⟩ := Set.nonempty_compl.mpr hΩ_ne
    have hw₀_ex : ∃ w₀ : ℂ, (w₀ : RudinRCA.Chapter13.RiemannSphere) ∉ Ω := by
      induction p₀ using OnePoint.rec with
      | infty => exact (hp₀ hinf).elim
      | coe w₀ => exact ⟨w₀, hp₀⟩
    obtain ⟨w₀, hw₀⟩ := hw₀_ex
    let φ : ℂ → RudinRCA.Chapter13.RiemannSphere :=
      fun ζ ↦ if ζ = 0 then ∞ else ((w₀ + ζ⁻¹ : ℂ) : RudinRCA.Chapter13.RiemannSphere)
    have hφ_inj : Function.Injective φ := by
      intro ζ₁ ζ₂ h
      dsimp only [φ] at h
      by_cases h1 : ζ₁ = 0 <;> by_cases h2 : ζ₂ = 0
      · exact h1.trans h2.symm
      · simp only [h1, h2, ↓reduceIte] at h
        exact (OnePoint.infty_ne_coe _ h).elim
      · simp only [h1, h2, ↓reduceIte] at h
        exact (OnePoint.coe_ne_infty _ h).elim
      · simp only [h1, h2, ↓reduceIte] at h
        exact inv_injective (add_left_cancel (OnePoint.coe_injective h))
    have hφ_cont : Continuous φ := by
      rw [continuous_iff_continuousAt]
      intro ζ
      by_cases hζ : ζ = 0
      · subst hζ
        rw [ContinuousAt, show φ 0 = ∞ by simp [φ], Filter.tendsto_def]
        intro s hs
        obtain ⟨r, hr, hrs⟩ := RudinRCA.Chapter13.mem_nhds_infinity_iff.mp hs
        let δ : ℝ := (r + ‖w₀‖ + 1)⁻¹
        have hpos_denom : 0 < r + ‖w₀‖ + 1 := by positivity
        have hδ : 0 < δ := inv_pos.mpr hpos_denom
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδ] with u hu
        apply hrs
        by_cases hu0 : u = 0
        · simp [φ, hu0]
        · simp only [φ, hu0, ↓reduceIte, RudinRCA.Chapter13.coe_mem_infinityDisc]
          have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
          have hu_lt : ‖u‖ < (r + ‖w₀‖ + 1)⁻¹ := by
            simpa [Metric.mem_ball, dist_zero_right, δ] using hu
          have hinv_gt : r + ‖w₀‖ + 1 < ‖u⁻¹‖ := by
            rw [norm_inv]
            exact (lt_inv_comm₀ hu_pos hpos_denom).mp hu_lt
          have htri : ‖u⁻¹‖ ≤ ‖w₀ + u⁻¹‖ + ‖w₀‖ := by
            calc
              ‖u⁻¹‖ = ‖(w₀ + u⁻¹) - w₀‖ := by ring_nf
              _ ≤ ‖w₀ + u⁻¹‖ + ‖w₀‖ := norm_sub_le _ _
          linarith
      · have h_nhds : φ =ᶠ[𝓝 ζ]
            fun u : ℂ ↦ ((w₀ + u⁻¹ : ℂ) : RudinRCA.Chapter13.RiemannSphere) := by
          filter_upwards [isOpen_ne.mem_nhds hζ] with u hu
          simp [φ, hu]
        exact (OnePoint.continuous_coe.continuousAt.comp
          (continuousAt_const.add (continuousAt_inv₀ hζ))).congr h_nhds.symm
    let Ω₁ : Set ℂ := φ ⁻¹' Ω
    let A₁ : Set ℂ := φ ⁻¹' A
    let m₁ : ℂ → ℕ := fun ζ ↦ m (φ ζ)
    have hΩ₁ : IsOpen Ω₁ := hΩ.preimage hφ_cont
    have hA₁ : A₁ ⊆ Ω₁ := Set.preimage_mono hAΩ
    have hacc₁ : ∀ ζ ∈ Ω₁, ζ ∉ closure (A₁ \ {ζ}) := by
      intro ζ hζ hmem
      have himg : φ '' (A₁ \ {ζ}) ⊆ A \ {φ ζ} := by
        rintro _ ⟨u, ⟨huA, huζ⟩, rfl⟩
        exact ⟨huA, fun h ↦ huζ (hφ_inj h)⟩
      have hcl := image_closure_subset_closure_image hφ_cont (Set.mem_image_of_mem φ hmem)
      exact hacc (φ ζ) hζ (closure_mono himg hcl)
    have hm₁ : ∀ a ∈ A₁, 0 < m₁ a := fun a ha ↦ hm (φ a) ha
    obtain ⟨F, hF_diff, hF_zero, hF_fin, hF_ord⟩ :=
      exists_holomorphic_prescribed_zeros_plane hΩ₁ hA₁ hacc₁ hm₁
    let f : RudinRCA.Chapter13.RiemannSphere → ℂ :=
      OnePoint.rec (F 0) (fun z : ℂ ↦ if z = w₀ then 0 else F ((z - w₀)⁻¹))
    have hf_inf_eq : f ∞ = F 0 := rfl
    have hf_coe_eq : ∀ u : ℂ, f (u : RudinRCA.Chapter13.RiemannSphere) =
        if u = w₀ then 0 else F ((u - w₀)⁻¹) := fun _ ↦ rfl
    have h0Ω₁ : (0 : ℂ) ∈ Ω₁ := by simpa [Ω₁, φ] using hinf
    have hz_mem_Ω₁ : ∀ z : ℂ, (z : RudinRCA.Chapter13.RiemannSphere) ∈ Ω →
        z ≠ w₀ ∧ (z - w₀)⁻¹ ∈ Ω₁ ∧ φ ((z - w₀)⁻¹) = (z : RudinRCA.Chapter13.RiemannSphere) := by
      intro z hz
      have hne : z ≠ w₀ := fun h ↦ hw₀ (h ▸ hz)
      have hsub_ne : z - w₀ ≠ 0 := sub_ne_zero.mpr hne
      have hφ_eq : φ ((z - w₀)⁻¹) = (z : RudinRCA.Chapter13.RiemannSphere) := by
        simp [φ, inv_ne_zero hsub_ne]
      exact ⟨hne, by simpa [Ω₁, hφ_eq] using hz, hφ_eq⟩
    have hf_fin_ord_coe : ∀ z : ℂ, (z : RudinRCA.Chapter13.RiemannSphere) ∈ Ω →
        sphereZeroOrder f (z : RudinRCA.Chapter13.RiemannSphere) =
          analyticOrderAt F ((z - w₀)⁻¹) := by
      intro z hz
      obtain ⟨hne, _, _⟩ := hz_mem_Ω₁ z hz
      have hsub_ne : z - w₀ ≠ 0 := sub_ne_zero.mpr hne
      let ψ : ℂ → ℂ := fun u ↦ (u - w₀)⁻¹
      have heq_nhds : (fun u : ℂ ↦ f (u : RudinRCA.Chapter13.RiemannSphere)) =ᶠ[𝓝 z] F ∘ ψ := by
        filter_upwards [isOpen_ne.mem_nhds hne] with u hu
        simp [hf_coe_eq, ψ, hu]
      have hψ_an : AnalyticAt ℂ ψ z := (analyticAt_id.sub analyticAt_const).inv hsub_ne
      have hψ_deriv : HasDerivAt ψ (-1 / (z - w₀) ^ 2) z := by
        have hd := ((hasDerivAt_id z).sub_const w₀).inv hsub_ne
        dsimp only [id] at hd
        change HasDerivAt ψ _ z at hd
        exact hd.congr_deriv (by ring)
      have hψ_ne : deriv ψ z ≠ 0 := by
        rw [hψ_deriv.deriv]
        exact div_ne_zero (by norm_num) (pow_ne_zero 2 hsub_ne)
      rw [sphereZeroOrder_coe, analyticOrderAt_congr heq_nhds,
        analyticOrderAt_comp_of_deriv_ne_zero hψ_an hψ_ne]
    let θ : ℂ → ℂ := fun w ↦ w / (1 - w₀ * w)
    have hθ_an : AnalyticAt ℂ θ 0 :=
      analyticAt_id.div (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (by simp)
    have hθ0 : θ 0 = 0 := by simp [θ]
    have hinf_nhds : (fun w : ℂ ↦
        if w = 0 then f ∞ else f ((w⁻¹ : ℂ) : RudinRCA.Chapter13.RiemannSphere)) =ᶠ[𝓝 0]
        F ∘ θ := by
      have hrad : 0 < (‖w₀‖ + 1)⁻¹ := inv_pos.mpr (by positivity)
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hrad] with w hw
      by_cases hw0_eq : w = 0
      · simp [hw0_eq, hf_inf_eq, θ]
      · have hw_lt : ‖w‖ < (‖w₀‖ + 1)⁻¹ := by
          simpa [Metric.mem_ball, dist_zero_right] using hw
        have hmul_lt : ‖w₀ * w‖ < 1 := by
          rw [norm_mul]
          calc
            ‖w₀‖ * ‖w‖ ≤ ‖w₀‖ * (‖w₀‖ + 1)⁻¹ :=
              mul_le_mul_of_nonneg_left hw_lt.le (norm_nonneg w₀)
            _ < (‖w₀‖ + 1) * (‖w₀‖ + 1)⁻¹ := by
              refine mul_lt_mul_of_pos_right (by linarith) hrad
            _ = 1 := mul_inv_cancel₀ (by positivity)
        have h1_ne : 1 - w₀ * w ≠ 0 := by
          intro h0
          have : ‖w₀ * w‖ = 1 := by
            rw [← sub_eq_zero.mp h0, norm_one]
          linarith
        have hwinv_ne : w⁻¹ ≠ w₀ := by
          intro heq
          apply h1_ne
          rw [← heq, inv_mul_cancel₀ hw0_eq, sub_self]
        simp only [hw0_eq, ↓reduceIte, hf_coe_eq, hwinv_ne, Function.comp_apply, θ]
        congr 1
        field_simp [hw0_eq, h1_ne]
    have hf_inf_an : AnalyticAt ℂ (fun w : ℂ ↦
        if w = 0 then f ∞ else f ((w⁻¹ : ℂ) : RudinRCA.Chapter13.RiemannSphere)) 0 := by
      have hF0_an : AnalyticAt ℂ F (θ 0) := by
        rw [hθ0]
        exact hF_diff.analyticAt (hΩ₁.mem_nhds h0Ω₁)
      exact (hF0_an.comp hθ_an).congr hinf_nhds.symm
    have hf_ord_inf : sphereZeroOrder f ∞ = analyticOrderAt F 0 := by
      have hθ_deriv : HasDerivAt θ 1 0 := by
        have hd := (hasDerivAt_id (0 : ℂ)).div
          ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub ((hasDerivAt_id (0 : ℂ)).const_mul w₀))
          (by simp)
        change HasDerivAt θ _ 0 at hd
        exact hd.congr_deriv (by simp)
      have hθ_ne : deriv θ 0 ≠ 0 := by
        rw [hθ_deriv.deriv]
        exact one_ne_zero
      rw [sphereZeroOrder_infty, analyticOrderAt_congr hinf_nhds,
        analyticOrderAt_comp_of_deriv_ne_zero hθ_an hθ_ne, hθ0]
    have hf_hol : HolomorphicOnSphere Ω f := by
      refine ⟨?_, fun _ ↦ hf_inf_an⟩
      intro z hz
      obtain ⟨hne, hz₁, _⟩ := hz_mem_Ω₁ z hz
      have hsub_ne : z - w₀ ≠ 0 := sub_ne_zero.mpr hne
      have heq_nhds : (fun u : ℂ ↦ f (u : RudinRCA.Chapter13.RiemannSphere)) =ᶠ[𝓝 z]
          fun u ↦ F ((u - w₀)⁻¹) := by
        filter_upwards [isOpen_ne.mem_nhds hne] with u hu
        simp [hf_coe_eq, hu]
      have hd : DifferentiableAt ℂ (fun u ↦ F ((u - w₀)⁻¹)) z :=
        (hF_diff.differentiableAt (hΩ₁.mem_nhds hz₁)).comp z
          (((differentiableAt_id.sub_const w₀)).inv hsub_ne)
      exact (hd.congr_of_eventuallyEq heq_nhds).differentiableWithinAt
    have hf_nat : ∀ p ∈ Ω, sphereZeroOrderNat f p = if p ∈ A then m p else 0 := by
      intro p hp
      induction p using OnePoint.rec with
      | infty =>
        simp only [sphereZeroOrderNat, hf_ord_inf]
        simpa [analyticOrderNatAt, A₁, m₁, φ] using hF_ord 0 h0Ω₁
      | coe z =>
        obtain ⟨_, hz₁, hφz⟩ := hz_mem_Ω₁ z hp
        simp only [sphereZeroOrderNat, hf_fin_ord_coe z hp]
        simpa [analyticOrderNatAt, A₁, m₁, hφz] using hF_ord ((z - w₀)⁻¹) hz₁
    refine ⟨f, hf_hol, ?_, ?_, fun a ha ↦ by simp [hf_nat a (hAΩ ha), ha], hf_nat⟩
    · intro p hp
      induction p using OnePoint.rec with
      | infty =>
        rw [hf_inf_eq]
        simpa [A₁, φ] using hF_zero 0 h0Ω₁
      | coe z =>
        obtain ⟨hne, hz₁, hφz⟩ := hz_mem_Ω₁ z hp
        have hfz : f (z : RudinRCA.Chapter13.RiemannSphere) = F ((z - w₀)⁻¹) := by
          simp [hf_coe_eq, hne]
        rw [hfz]
        simpa [A₁, hφz] using hF_zero ((z - w₀)⁻¹) hz₁
    · intro p hp
      induction p using OnePoint.rec with
      | infty =>
        rw [hf_ord_inf]
        exact hF_fin 0 h0Ω₁
      | coe z =>
        obtain ⟨_, hz₁, _⟩ := hz_mem_Ω₁ z hp
        rw [hf_fin_ord_coe z hp]
        exact hF_fin ((z - w₀)⁻¹) hz₁
  · let Ω₀ : Set ℂ := ((↑) : ℂ → RudinRCA.Chapter13.RiemannSphere) ⁻¹' Ω
    let A₀ : Set ℂ := ((↑) : ℂ → RudinRCA.Chapter13.RiemannSphere) ⁻¹' A
    let m₀ : ℂ → ℕ := fun z ↦ m (z : RudinRCA.Chapter13.RiemannSphere)
    have hΩ₀ : IsOpen Ω₀ := hΩ.preimage OnePoint.continuous_coe
    have hA₀ : A₀ ⊆ Ω₀ := Set.preimage_mono hAΩ
    have hacc₀ : ∀ z ∈ Ω₀, z ∉ closure (A₀ \ {z}) := by
      intro z hz hmem
      have himg : ((↑) : ℂ → RudinRCA.Chapter13.RiemannSphere) '' (A₀ \ {z}) ⊆
          A \ {(z : RudinRCA.Chapter13.RiemannSphere)} := by
        rintro _ ⟨u, ⟨huA, huz⟩, rfl⟩
        exact ⟨huA, fun h ↦ huz (OnePoint.coe_injective h)⟩
      have hcl := image_closure_subset_closure_image OnePoint.continuous_coe
        (Set.mem_image_of_mem ((↑) : ℂ → RudinRCA.Chapter13.RiemannSphere) hmem)
      exact hacc (z : RudinRCA.Chapter13.RiemannSphere) hz (closure_mono himg hcl)
    have hm₀ : ∀ a ∈ A₀, 0 < m₀ a := fun a ha ↦ hm (a : RudinRCA.Chapter13.RiemannSphere) ha
    obtain ⟨F, hF_diff, hF_zero, hF_fin, hF_ord⟩ :=
      exists_holomorphic_prescribed_zeros_plane hΩ₀ hA₀ hacc₀ hm₀
    let f : RudinRCA.Chapter13.RiemannSphere → ℂ := OnePoint.rec 0 F
    have hf_coe : (fun z : ℂ ↦ f (z : RudinRCA.Chapter13.RiemannSphere)) = F := rfl
    have hf_hol : HolomorphicOnSphere Ω f := ⟨hf_coe ▸ hF_diff, fun h ↦ (hinf h).elim⟩
    have hf_nat : ∀ p ∈ Ω, sphereZeroOrderNat f p = if p ∈ A then m p else 0 := by
      intro p hp
      induction p using OnePoint.rec with
      | infty => exact (hinf hp).elim
      | coe z =>
        simpa [sphereZeroOrderNat, sphereZeroOrder_coe, hf_coe, analyticOrderNatAt, A₀, m₀] using
          hF_ord z hp
    refine ⟨f, hf_hol, ?_, ?_, fun a ha ↦ by simp [hf_nat a (hAΩ ha), ha], hf_nat⟩
    · intro p hp
      induction p using OnePoint.rec with
      | infty => exact (hinf hp).elim
      | coe z => exact hF_zero z hp
    · intro p hp
      induction p using OnePoint.rec with
      | infty => exact (hinf hp).elim
      | coe z =>
        rw [sphereZeroOrder_coe, hf_coe]
        exact hF_fin z hp

/-- **Rudin RCA 15.1** (Isolated zeros on plane regions and the converse zero-set problem):
1. On any plane region `Ω` (`IsOpen Ω` and `IsPreconnected Ω`), the zeros of any holomorphic `f`
   not identically zero on `Ω` have no limit point in `Ω` and finite multiplicity everywhere in `Ω`;
2. Conversely (as announced in 15.1 and proved in 15.11), on every proper open subset of the
   Riemann sphere `Ω ⊊ RiemannSphere` — and in particular on every open subset `Ω₀ ⊆ ℂ` — any
   subset without limit points in the domain and any positive multiplicity function are realized as
   the exact zero set and zero multiplicities of a holomorphic function. -/
theorem theorem15_1 :
    (∀ {Ω : Set ℂ} {f : ℂ → ℂ},
      IsOpen Ω → IsPreconnected Ω → DifferentiableOn ℂ f Ω → (∃ w ∈ Ω, f w ≠ 0) →
      ∀ z ∈ Ω, z ∉ closure ({w : ℂ | f w = 0} \ {z}) ∧ analyticOrderAt f z ≠ ⊤) ∧
    (∀ {Ω A : Set RudinRCA.Chapter13.RiemannSphere} {m : RudinRCA.Chapter13.RiemannSphere → ℕ},
      IsOpen Ω → Ω ≠ Set.univ → A ⊆ Ω → (∀ p ∈ Ω, p ∉ closure (A \ {p})) →
      (∀ a ∈ A, 0 < m a) →
      ∃ f : RudinRCA.Chapter13.RiemannSphere → ℂ,
        HolomorphicOnSphere Ω f ∧
        (∀ p ∈ Ω, f p = 0 ↔ p ∈ A) ∧
        (∀ p ∈ Ω, sphereZeroOrder f p ≠ ⊤) ∧
        (∀ a ∈ A, sphereZeroOrderNat f a = m a)) ∧
    (∀ {Ω₀ A₀ : Set ℂ} {m₀ : ℂ → ℕ},
      IsOpen Ω₀ → A₀ ⊆ Ω₀ → (∀ z ∈ Ω₀, z ∉ closure (A₀ \ {z})) →
      (∀ a ∈ A₀, 0 < m₀ a) →
      ∃ f : ℂ → ℂ,
        DifferentiableOn ℂ f Ω₀ ∧
        (∀ z ∈ Ω₀, f z = 0 ↔ z ∈ A₀) ∧
        (∀ z ∈ Ω₀, analyticOrderAt f z ≠ ⊤) ∧
        (∀ z ∈ Ω₀, analyticOrderNatAt f z = if z ∈ A₀ then m₀ z else 0)) := by
  refine ⟨?_, ?_, fun hΩ₀ hA₀ hacc hm₀ ↦ exists_holomorphic_prescribed_zeros_plane hΩ₀ hA₀ hacc hm₀⟩
  · intro Ω f hΩ hc hf ⟨w, hw, hfw⟩ z hz
    refine ⟨zeros_have_no_accumulation hΩ hc hf ⟨w, hw, hfw⟩ hz, ?_⟩
    intro htop
    have hev : f =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.mp htop
    exact hfw ((hf.analyticOnNhd hΩ).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hz hev hw)
  · intro Ω A m hΩ hΩ_ne hAΩ hacc hm
    obtain ⟨f, hhol, hzero, hfin, hmult, _⟩ := theorem15_11 hΩ hΩ_ne hAΩ hacc hm
    exact ⟨f, hhol, hzero, hfin, hmult⟩

/-! ## 15.12: Meromorphic Functions as Quotients of Holomorphic Functions -/

/-- Bridge from Mathlib's `MeromorphicOn` to Chapter 10's `BookMeromorphicWithPoles` via
`toMeromorphicNFOn`: on an open set `Ω ⊆ ℂ`, if `MeromorphicOn f Ω`, then `F := toMeromorphicNFOn f Ω`
satisfies `BookMeromorphicWithPoles F Ω {a ∈ Ω | meromorphicOrderAt F a < 0}`, agrees with `f`
codiscretely on `Ω`, and agrees pointwise with `f` wherever `f` is analytic in `Ω`. -/
theorem bookMeromorphicWithPoles_toMeromorphicNFOn {Ω : Set ℂ} {f : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hf : MeromorphicOn f Ω) :
    let F : ℂ → ℂ := toMeromorphicNFOn f Ω
    let P : Set ℂ := {a ∈ Ω | meromorphicOrderAt F a < 0}
    RudinRCA.Chapter10.BookMeromorphicWithPoles F Ω P ∧
    (f =ᶠ[Filter.codiscreteWithin Ω] F) ∧
    (∀ z ∈ Ω, AnalyticAt ℂ f z → F z = f z) := by
  classical
  dsimp only
  let F : ℂ → ℂ := toMeromorphicNFOn f Ω
  let P : Set ℂ := {a ∈ Ω | meromorphicOrderAt F a < 0}
  have hPΩ : P ⊆ Ω := fun _ ha ↦ ha.1
  have hnf : ∀ z ∈ Ω, MeromorphicNFAt F z :=
    fun z hz ↦ meromorphicNFOn_toMeromorphicNFOn f Ω hz
  have hF_an_outside : ∀ z ∈ Ω \ P, AnalyticAt ℂ F z := by
    rintro z ⟨hzΩ, hzP⟩
    have hnn : 0 ≤ meromorphicOrderAt F z := not_lt.mp (fun hlt ↦ hzP ⟨hzΩ, hlt⟩)
    exact (hnf z hzΩ).meromorphicOrderAt_nonneg_iff_analyticAt.mp hnn
  have hpole_nbhd : ∀ a ∈ P, ∃ V : Set ℂ,
      IsOpen V ∧ a ∈ V ∧ V ⊆ Ω ∧ (∀ z ∈ V \ {a}, z ∉ P) ∧ RudinRCA.Chapter10.HasPole F V a := by
    rintro a ⟨haΩ, hneg⟩
    lift meromorphicOrderAt F a to ℤ using hneg.ne_top with k hk
    have hk_neg : k < 0 := WithTop.coe_lt_zero.mp (hk ▸ hneg)
    let m : ℕ := (-k).toNat
    have hm_pos : 0 < m := by omega
    have hk_eq : k = -(m : ℤ) := by omega
    obtain ⟨u, hu_an, hu0, hFu⟩ :=
      (meromorphicOrderAt_eq_int_iff (hnf a haΩ).meromorphicAt).mp hk.symm
    have hFu' : ∀ᶠ z in 𝓝[≠] a, F z = (z - a) ^ (-(m : ℤ)) • u z := by
      simpa only [hk_eq] using hFu
    have hnhds : Ω ∩ {z | AnalyticAt ℂ u z} ∩
        {z | z ≠ a → F z = (z - a) ^ (-(m : ℤ)) • u z} ∈ 𝓝 a :=
      Filter.inter_mem (Filter.inter_mem (hΩ.mem_nhds haΩ) hu_an.eventually_analyticAt)
        (eventually_nhdsWithin_iff.mp hFu')
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    let V : Set ℂ := Metric.ball a r
    have hV_open : IsOpen V := Metric.isOpen_ball
    have haV : a ∈ V := Metric.mem_ball_self hr
    have hVΩ : V ⊆ Ω := fun z hz ↦ (hball hz).1.1
    have hu_holo : RudinRCA.Chapter10.HolomorphicOn u V :=
      fun z hz ↦ (hball hz).1.2.differentiableAt
    obtain ⟨d, G, hG_holo, hd0, hTaylor⟩ :=
      RudinRCA.Chapter10.dslope_taylor_expansion hV_open haV hu_holo m
    let c : ℕ → ℂ := fun j ↦ if j ∈ Finset.Icc 1 m then d (m - j) else 0
    let Q : ℂ → ℂ := fun z ↦ ∑ j ∈ Finset.Icc 1 m, c j * (z - a)⁻¹ ^ j
    have hcm_ne : c m ≠ 0 := by
      have hm1 : 1 ≤ m := by omega
      simp [c, hm1, hd0, hu0]
    have hQ_pp : RudinRCA.Chapter10.IsPrincipalPart Q a :=
      ⟨m, c, hm_pos, hcm_ne, fun _ ↦ rfl⟩
    have hdecomp_ne : ∀ z : ℂ, z ≠ a → (z - a) ^ (-(m : ℤ)) • u z = G z + Q z := by
      intro z hza
      have hsub_ne : z - a ≠ 0 := sub_ne_zero.mpr hza
      have hQ_mul : (z - a) ^ m * Q z =
          ∑ i ∈ Finset.range m, d i * (z - a) ^ i := by
        dsimp only [Q]
        rw [Finset.mul_sum]
        refine Finset.sum_nbij (fun j ↦ m - j) ?_ ?_ ?_ ?_
        · intro j hj
          simp only [Finset.mem_Icc] at hj
          exact Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))
        · intro j₁ hj₁ j₂ hj₂ h
          simp only [Finset.mem_coe, Finset.mem_Icc] at hj₁ hj₂
          dsimp at h
          omega
        · intro i hi
          simp only [Finset.mem_coe, Finset.mem_range] at hi
          refine ⟨m - i, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), ?_⟩
          dsimp
          omega
        · intro j hj
          have hj_mem : j ∈ Finset.Icc 1 m := hj
          obtain ⟨hj1, hj_le⟩ := Finset.mem_Icc.mp hj_mem
          have hpow_split : (z - a) ^ m = (z - a) ^ (m - j) * (z - a) ^ j := by
            rw [← pow_add, Nat.sub_add_cancel hj_le]
          have hcancel : (z - a) ^ j * (z - a)⁻¹ ^ j = 1 := by
            rw [← mul_pow, mul_inv_cancel₀ hsub_ne, one_pow]
          have hc_eq : c j = d (m - j) := by
            simp [c, hj1, hj_le]
          calc
            (z - a) ^ m * (c j * (z - a)⁻¹ ^ j)
                = d (m - j) * ((z - a) ^ (m - j) * ((z - a) ^ j * (z - a)⁻¹ ^ j)) := by
                    rw [hc_eq, hpow_split]; ring
            _ = d (m - j) * (z - a) ^ (m - j) := by rw [hcancel, mul_one]
      have hu_eq : u z = (z - a) ^ m * (G z + Q z) := by
        rw [hTaylor z, ← hQ_mul]
        ring
      simp only [zpow_neg, zpow_natCast, smul_eq_mul, hu_eq]
      exact inv_mul_cancel_left₀ (pow_ne_zero m hsub_ne) (G z + Q z)
    have heq_V : Set.EqOn F (fun z ↦ G z + Q z) (V \ {a}) := by
      rintro z ⟨hzV, hza⟩
      rw [(hball hzV).2 hza, hdecomp_ne z hza]
    have hQ_holo : RudinRCA.Chapter10.HolomorphicOn Q (V \ {a}) := by
      rintro z ⟨_, hza⟩
      have hsub_ne : z - a ≠ 0 := sub_ne_zero.mpr hza
      dsimp only [Q]
      refine DifferentiableAt.fun_sum fun j _ ↦ ?_
      exact (differentiableAt_const (c j)).mul
        (((differentiableAt_id.sub (differentiableAt_const a)).inv hsub_ne).pow j)
    have hV_sdiff_open : IsOpen (V \ {a}) := hV_open.sdiff isClosed_singleton
    have hF_holo_punct : RudinRCA.Chapter10.HolomorphicOn F (V \ {a}) := by
      intro z hz
      have hsum_diff : DifferentiableAt ℂ (fun w ↦ G w + Q w) z :=
        (hG_holo z hz.1).add (hQ_holo z hz)
      have hev : F =ᶠ[𝓝 z] fun w ↦ G w + Q w := by
        filter_upwards [hV_sdiff_open.mem_nhds hz] with w hw
        exact heq_V hw
      exact hsum_diff.congr_of_eventuallyEq hev
    have hdisj_P : ∀ z ∈ V \ {a}, z ∉ P := by
      intro z hz hzP
      have hdiff_on : DifferentiableOn ℂ F (V \ {a}) :=
        (RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn hV_sdiff_open).mp hF_holo_punct
      have han_z : AnalyticAt ℂ F z := hdiff_on.analyticAt (hV_sdiff_open.mem_nhds hz)
      exact not_lt_of_ge han_z.meromorphicOrderAt_nonneg hzP.2
    exact ⟨V, hV_open, haV, hVΩ, hdisj_P, ⟨hV_open, haV, hF_holo_punct⟩, G, Q, hG_holo, hQ_pp, heq_V⟩
  have hno_acc : ∀ z ∈ Ω, ¬ AccPt z (𝓟 P) := by
    intro z hzΩ hacc
    by_cases hzP : z ∈ P
    · obtain ⟨V, hV_open, hzV, _, hdisj_P, _⟩ := hpole_nbhd z hzP
      rcases accPt_iff_nhds.mp hacc V (hV_open.mem_nhds hzV) with ⟨w, ⟨hwV, hwP⟩, hwz⟩
      exact hdisj_P w ⟨hwV, hwz⟩ hwP
    · have han_z : AnalyticAt ℂ F z := hF_an_outside z ⟨hzΩ, hzP⟩
      have hU : Ω ∩ {w | AnalyticAt ℂ F w} ∈ 𝓝 z :=
        Filter.inter_mem (hΩ.mem_nhds hzΩ) han_z.eventually_analyticAt
      rcases accPt_iff_nhds.mp hacc _ hU with ⟨w, ⟨⟨_, han_w⟩, hwP⟩, _⟩
      exact not_lt_of_ge han_w.meromorphicOrderAt_nonneg hwP.2
  refine ⟨⟨hΩ, hPΩ, hno_acc, fun z hz ↦ (hF_an_outside z hz).differentiableAt,
    fun a ha ↦ let ⟨V, h1, h2, h3, _, h5⟩ := hpole_nbhd a ha; ⟨V, h1, h2, h3, h5⟩⟩,
    toMeromorphicNFOn_eqOn_codiscrete hf, ?_⟩
  intro z hz han
  have hnf_z : MeromorphicNFAt f z := han.meromorphicNFAt
  simp [toMeromorphicNFOn, hf, hz, toMeromorphicNFAt_eq_self.mpr hnf_z]

/-- Helper for `15.12(a)`: every `BookMeromorphicOn f Ω` is a quotient `g / h` of functions in `H(Ω)`
with `{z ∈ Ω | h z = 0} = poleSet f Ω` and `f = g / h` throughout `Ω \ poleSet f Ω`. -/
theorem exists_quotient_of_bookMeromorphicOn {Ω : Set ℂ} {f : ℂ → ℂ}
    (hmero : RudinRCA.Chapter10.BookMeromorphicOn f Ω) :
    ∃ g h : ℂ → ℂ,
      DifferentiableOn ℂ g Ω ∧
      DifferentiableOn ℂ h Ω ∧
      (∀ z ∈ Ω, ∃ w ∈ connectedComponentIn Ω z, h w ≠ 0) ∧
      {z ∈ Ω | h z = 0} = RudinRCA.Chapter10.poleSet f Ω ∧
      (∀ z ∈ Ω \ RudinRCA.Chapter10.poleSet f Ω, f z = g z / h z) ∧
      MeromorphicOn (g / h) Ω ∧
      (f =ᶠ[Filter.codiscreteWithin Ω] (g / h)) := by
  classical
  rcases hmero with ⟨A, hA_mero⟩
  have hΩ : IsOpen Ω := hA_mero.1
  have hAΩ : A ⊆ Ω := hA_mero.2.1
  have hacc : ∀ z ∈ Ω, ¬ AccPt z (𝓟 A) := hA_mero.2.2.1
  have hf_holo : RudinRCA.Chapter10.HolomorphicOn f (Ω \ A) := hA_mero.2.2.2.1
  obtain ⟨hopen_sdiff, hpole_eq, _, _, hlocal⟩ := RudinRCA.Chapter10.theorem10_41 hA_mero
  have hacc_cl : ∀ z ∈ Ω, z ∉ closure (A \ {z}) :=
    fun z hz ↦ mt accPt_principal_iff_mem_closure_diff.mpr (hacc z hz)
  have hex_pole : ∀ a : A, ∃ (V : Set ℂ) (G : ℂ → ℂ) (m : ℕ) (c : ℕ → ℂ),
      IsOpen V ∧ a.1 ∈ V ∧ V ⊆ Ω ∧ V \ {a.1} ⊆ Ω \ A ∧
      RudinRCA.Chapter10.HolomorphicOn G V ∧ 0 < m ∧ c m ≠ 0 ∧
      Set.EqOn f (fun z ↦ G z + ∑ k ∈ Finset.Icc 1 m, c k * (z - a.1)⁻¹ ^ k) (V \ {a.1}) := by
    intro ⟨a, ha⟩
    obtain ⟨V, G, Q, hV, haV, hVΩ, hVsdiff, hG, ⟨m, c, hm, hcm, hQeq⟩, heq, _⟩ := hlocal a ha
    refine ⟨V, G, m, c, hV, haV, hVΩ, hVsdiff, hG, hm, hcm, ?_⟩
    intro z hz
    simpa only [hQeq z] using heq hz
  choose V_p G_p m_p c_p hV_open ha_mem_V hV_sub_Ω hV_sdiff hG_holo hm_pos hc_ne hf_eq_p using hex_pole
  let m : ℂ → ℕ := fun z ↦ if hz : z ∈ A then m_p ⟨z, hz⟩ else 0
  have hm_A : ∀ a ∈ A, 0 < m a := by
    intro a ha
    simp [m, ha, hm_pos ⟨a, ha⟩]
  obtain ⟨h, hh_diff, hh_zero, hh_fin, hh_ord⟩ :=
    exists_holomorphic_prescribed_zeros_plane hΩ hAΩ hacc_cl hm_A
  have hh_comp_nz : ∀ z ∈ Ω, ∃ w ∈ connectedComponentIn Ω z, h w ≠ 0 := by
    intro z hz
    by_contra hall
    push Not at hall
    have hcomp_open : IsOpen (connectedComponentIn Ω z) := hΩ.connectedComponentIn
    have hev0 : h =ᶠ[𝓝 z] 0 := by
      filter_upwards [hcomp_open.mem_nhds (mem_connectedComponentIn hz)] with w hw
      exact hall w hw
    exact hh_fin z hz (analyticOrderAt_eq_top.mpr hev0)
  have hex_u : ∀ a : A, ∃ u : ℂ → ℂ,
      AnalyticAt ℂ u a.1 ∧ u a.1 ≠ 0 ∧
      h =ᶠ[𝓝 a.1] fun z ↦ (z - a.1) ^ (m_p a) * u z := by
    intro a
    have haΩ : a.1 ∈ Ω := hAΩ a.2
    have han_h : AnalyticAt ℂ h a.1 := hh_diff.analyticAt (hΩ.mem_nhds haΩ)
    obtain ⟨u, hu_an, hu0, hhu⟩ := han_h.analyticOrderAt_ne_top.mp (hh_fin a.1 haΩ)
    have hord_a : analyticOrderNatAt h a.1 = m_p a := by
      simpa [m, a.2] using hh_ord a.1 haΩ
    refine ⟨u, hu_an, hu0, ?_⟩
    simpa only [hord_a, smul_eq_mul] using hhu
  choose u_p hu_an hu_ne hh_local using hex_u
  let g : ℂ → ℂ := fun z ↦
    if hz : z ∈ A then c_p ⟨z, hz⟩ (m_p ⟨z, hz⟩) * u_p ⟨z, hz⟩ z else f z * h z
  have hg_diff : DifferentiableOn ℂ g Ω := by
    intro z hzΩ
    by_cases hzA : z ∈ A
    · let p : A := ⟨z, hzA⟩
      let Φ : ℂ → ℂ := fun w ↦
        (G_p p w * (w - z) ^ (m_p p) +
          ∑ k ∈ Finset.Icc 1 (m_p p), c_p p k * (w - z) ^ (m_p p - k)) * u_p p w
      have hG_an : AnalyticAt ℂ (G_p p) z :=
        ((RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn (hV_open p)).mp (hG_holo p)).analyticAt
          ((hV_open p).mem_nhds (ha_mem_V p))
      have hpoly_an : AnalyticAt ℂ
          (fun w ↦ ∑ k ∈ Finset.Icc 1 (m_p p), c_p p k * (w - z) ^ (m_p p - k)) z := by
        fun_prop
      have hΦ_an : AnalyticAt ℂ Φ z :=
        (hG_an.mul ((analyticAt_id.sub analyticAt_const).pow (m_p p)) |>.add hpoly_an).mul (hu_an p)
      have hg_eq_Φ : g =ᶠ[𝓝 z] Φ := by
        filter_upwards [(hV_open p).mem_nhds (ha_mem_V p), hh_local p] with w hwV hhw
        by_cases hwz : w = z
        · subst hwz
          have hm0 : m_p p ≠ 0 := (hm_pos p).ne'
          have hsum_z : (∑ k ∈ Finset.Icc 1 (m_p p), c_p p k * ((0 : ℂ)) ^ (m_p p - k)) =
              c_p p (m_p p) := by
            rw [Finset.sum_eq_single (m_p p)]
            · simp
            · intro k hk hkm
              have hk_le : k ≤ m_p p := (Finset.mem_Icc.mp hk).2
              have hsub_ne : m_p p - k ≠ 0 := by omega
              simp [zero_pow hsub_ne]
            · intro hnot
              exact (hnot (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)).elim
          simp [g, p, hzA, Φ, zero_pow hm0, hsum_z]
        · have hw_sdiff : w ∈ Ω \ A := hV_sdiff p ⟨hwV, hwz⟩
          have hw_notA : w ∉ A := hw_sdiff.2
          have hsub_ne : w - z ≠ 0 := sub_ne_zero.mpr hwz
          have hf_w : f w = G_p p w + ∑ k ∈ Finset.Icc 1 (m_p p), c_p p k * (w - z)⁻¹ ^ k :=
            hf_eq_p p ⟨hwV, hwz⟩
          have hsum_cancel :
              (∑ k ∈ Finset.Icc 1 (m_p p), c_p p k * (w - z)⁻¹ ^ k) * (w - z) ^ (m_p p) =
              ∑ k ∈ Finset.Icc 1 (m_p p), c_p p k * (w - z) ^ (m_p p - k) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun k hk ↦ ?_
            have hk_le : k ≤ m_p p := (Finset.mem_Icc.mp hk).2
            have hpow_split : (w - z) ^ (m_p p) = (w - z) ^ k * (w - z) ^ (m_p p - k) := by
              rw [← pow_add, Nat.add_sub_of_le hk_le]
            have hcancel : (w - z)⁻¹ ^ k * (w - z) ^ k = 1 := by
              rw [← mul_pow, inv_mul_cancel₀ hsub_ne, one_pow]
            calc
              c_p p k * (w - z)⁻¹ ^ k * (w - z) ^ (m_p p)
                  = c_p p k * (((w - z)⁻¹ ^ k * (w - z) ^ k) * (w - z) ^ (m_p p - k)) := by
                      rw [hpow_split]; ring
              _ = c_p p k * (w - z) ^ (m_p p - k) := by rw [hcancel, one_mul]
          simp only [g, hw_notA, ↓reduceDIte, hf_w, hhw, Φ]
          calc
            (G_p p w + ∑ k ∈ Finset.Icc 1 (m_p p), c_p p k * (w - z)⁻¹ ^ k) *
                ((w - z) ^ (m_p p) * u_p p w)
                = (G_p p w * (w - z) ^ (m_p p) +
                    (∑ k ∈ Finset.Icc 1 (m_p p), c_p p k * (w - z)⁻¹ ^ k) * (w - z) ^ (m_p p)) *
                    u_p p w := by ring
            _ = (G_p p w * (w - z) ^ (m_p p) +
                  ∑ k ∈ Finset.Icc 1 (m_p p), c_p p k * (w - z) ^ (m_p p - k)) * u_p p w := by
                  rw [hsum_cancel]
      exact (hΦ_an.differentiableAt.congr_of_eventuallyEq hg_eq_Φ).differentiableWithinAt
    · have hz_sdiff : z ∈ Ω \ A := ⟨hzΩ, hzA⟩
      have hg_nhds : g =ᶠ[𝓝 z] fun w ↦ f w * h w := by
        filter_upwards [hopen_sdiff.mem_nhds hz_sdiff] with w hw
        simp [g, hw.2]
      have hd : DifferentiableAt ℂ (fun w ↦ f w * h w) z :=
        (hf_holo z hz_sdiff).mul (hh_diff.differentiableAt (hΩ.mem_nhds hzΩ))
      exact (hd.congr_of_eventuallyEq hg_nhds).differentiableWithinAt
  have hzero_eq : {z ∈ Ω | h z = 0} = RudinRCA.Chapter10.poleSet f Ω := by
    rw [← hpole_eq]
    ext z
    constructor
    · rintro ⟨hzΩ, hhz⟩
      exact (hh_zero z hzΩ).mp hhz
    · intro hzA
      exact ⟨hAΩ hzA, (hh_zero z (hAΩ hzA)).mpr hzA⟩
  have hquot_eq : ∀ z ∈ Ω \ RudinRCA.Chapter10.poleSet f Ω, f z = g z / h z := by
    rw [← hpole_eq]
    rintro z ⟨hzΩ, hzA⟩
    have hhz : h z ≠ 0 := fun h0 ↦ hzA ((hh_zero z hzΩ).mp h0)
    simp [g, hzA, mul_div_cancel_right₀ _ hhz]
  have hmero_gh : MeromorphicOn (g / h) Ω :=
    fun z hz ↦ (hg_diff.analyticAt (hΩ.mem_nhds hz)).meromorphicAt.div
      (hh_diff.analyticAt (hΩ.mem_nhds hz)).meromorphicAt
  have hcod_A : Aᶜ ∈ Filter.codiscreteWithin Ω :=
    compl_mem_codiscreteWithin_of_no_limit_pt hAΩ hacc_cl
  have hcod_eq : f =ᶠ[Filter.codiscreteWithin Ω] (g / h) := by
    have hΩ_mem : Ω ∈ Filter.codiscreteWithin Ω := by simp
    filter_upwards [hΩ_mem, hcod_A] with z hzΩ hzA
    have hz_not_pole : z ∈ Ω \ RudinRCA.Chapter10.poleSet f Ω := by
      rw [← hpole_eq]
      exact ⟨hzΩ, hzA⟩
    exact hquot_eq z hz_not_pole
  exact ⟨g, h, hg_diff, hh_diff, hh_comp_nz, hzero_eq, hquot_eq, hmero_gh, hcod_eq⟩

/-- **Rudin RCA 15.12** (Characterization of meromorphic functions on open subsets of `ℂ`):
Let `Ω ⊆ ℂ` be an arbitrary open set.
- `(a)` Every `BookMeromorphicOn f Ω` is a quotient `g / h` of holomorphic functions `g, h ∈ H(Ω)`
  with `h` not identically zero on any component of `Ω`, `{z ∈ Ω | h z = 0} = poleSet f Ω`,
  `f z = g z / h z` for all `z ∈ Ω \ poleSet f Ω`, and `f =ᶠ[codiscreteWithin Ω] g / h`.
  Likewise, every `MeromorphicOn f Ω` satisfies `f =ᶠ[codiscreteWithin Ω] g / h` for such `g, h ∈ H(Ω)`.
- `(b)` Conversely, if `g, h ∈ H(Ω)` and `h` is not identically zero on any connected component of
  `Ω`, then `{z ∈ Ω | h z ≠ 0}` is codiscrete in `Ω`, `MeromorphicOn (g / h) Ω`, and there exists a
  canonical meromorphic function `F` (`BookMeromorphicOn F Ω`) extending `g / h` across removable
  zeros of `h` with `F z = g z / h z` whenever `z ∈ Ω` and `h z ≠ 0` (and `F =ᶠ[codiscreteWithin Ω] g / h`). -/
theorem theorem15_12 {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    (∀ {f : ℂ → ℂ}, RudinRCA.Chapter10.BookMeromorphicOn f Ω →
      ∃ g h : ℂ → ℂ,
        DifferentiableOn ℂ g Ω ∧
        DifferentiableOn ℂ h Ω ∧
        (∀ z ∈ Ω, ∃ w ∈ connectedComponentIn Ω z, h w ≠ 0) ∧
        {z ∈ Ω | h z = 0} = RudinRCA.Chapter10.poleSet f Ω ∧
        (∀ z ∈ Ω \ RudinRCA.Chapter10.poleSet f Ω, f z = g z / h z) ∧
        MeromorphicOn (g / h) Ω ∧
        (f =ᶠ[Filter.codiscreteWithin Ω] (g / h))) ∧
    (∀ {f : ℂ → ℂ}, MeromorphicOn f Ω →
      ∃ g h : ℂ → ℂ,
        DifferentiableOn ℂ g Ω ∧
        DifferentiableOn ℂ h Ω ∧
        (∀ z ∈ Ω, ∃ w ∈ connectedComponentIn Ω z, h w ≠ 0) ∧
        (f =ᶠ[Filter.codiscreteWithin Ω] (g / h))) ∧
    (∀ {g h : ℂ → ℂ},
      DifferentiableOn ℂ g Ω →
      DifferentiableOn ℂ h Ω →
      (∀ z ∈ Ω, ∃ w ∈ connectedComponentIn Ω z, h w ≠ 0) →
      ({z ∈ Ω | h z = 0}ᶜ ∈ Filter.codiscreteWithin Ω) ∧
      MeromorphicOn (g / h) Ω ∧
      ∃ F : ℂ → ℂ,
        RudinRCA.Chapter10.BookMeromorphicOn F Ω ∧
        (∀ z ∈ Ω, h z ≠ 0 → F z = g z / h z) ∧
        (F =ᶠ[Filter.codiscreteWithin Ω] (g / h))) := by
  refine ⟨fun hmero ↦ exists_quotient_of_bookMeromorphicOn hmero, ?_, ?_⟩
  · intro f hf
    obtain ⟨hF_book, hfF_cod, _⟩ := bookMeromorphicWithPoles_toMeromorphicNFOn hΩ hf
    obtain ⟨g, h, hg, hh, hcomp, _, _, _, hFgh_cod⟩ :=
      exists_quotient_of_bookMeromorphicOn ⟨_, hF_book⟩
    exact ⟨g, h, hg, hh, hcomp, hfF_cod.trans hFgh_cod⟩
  · intro g h hg hh hcomp
    have hZ_no_acc : ∀ z ∈ Ω, z ∉ closure ({w ∈ Ω | h w = 0} \ {z}) := by
      intro z hz hmem
      obtain ⟨w, hw_comp, hhw⟩ := hcomp z hz
      have hcomp_open : IsOpen (connectedComponentIn Ω z) := hΩ.connectedComponentIn
      have hcomp_sub : connectedComponentIn Ω z ⊆ Ω := connectedComponentIn_subset Ω z
      have hz_comp : z ∈ connectedComponentIn Ω z := mem_connectedComponentIn hz
      have hmem_comp : z ∈ closure ({u : ℂ | h u = 0} \ {z}) := by
        refine closure_mono ?_ hmem
        rintro u ⟨⟨_, hu0⟩, huz⟩
        exact ⟨hu0, huz⟩
      have han_comp : AnalyticOnNhd ℂ h (connectedComponentIn Ω z) :=
        (hh.analyticOnNhd hΩ).mono hcomp_sub
      exact hhw (han_comp.eqOn_zero_of_preconnected_of_mem_closure
        isPreconnected_connectedComponentIn hz_comp hmem_comp hw_comp)
    have hcod_Z : {z ∈ Ω | h z = 0}ᶜ ∈ Filter.codiscreteWithin Ω :=
      compl_mem_codiscreteWithin_of_no_limit_pt (fun _ hz ↦ hz.1) hZ_no_acc
    have hmero_gh : MeromorphicOn (g / h) Ω :=
      fun z hz ↦ (hg.analyticAt (hΩ.mem_nhds hz)).meromorphicAt.div
        (hh.analyticAt (hΩ.mem_nhds hz)).meromorphicAt
    obtain ⟨hF_book, hcod_F, hF_an⟩ := bookMeromorphicWithPoles_toMeromorphicNFOn hΩ hmero_gh
    refine ⟨hcod_Z, hmero_gh, toMeromorphicNFOn (g / h) Ω, ⟨_, hF_book⟩, ?_, hcod_F.symm⟩
    intro z hz hhz
    have han_gh : AnalyticAt ℂ (g / h) z :=
      (hg.analyticAt (hΩ.mem_nhds hz)).div (hh.analyticAt (hΩ.mem_nhds hz)) hhz
    exact hF_an z hz han_gh

/-! ## 15.13: Mittag-Leffler / Weierstrass Jet Interpolation -/

/-- **Rudin RCA 15.13** (Prescribed Taylor jets on discrete subsets of an open plane set):
Let `Ω ⊆ ℂ` be open, `A ⊆ Ω` have no accumulation point in `Ω`, `m : ℂ → ℕ` assign nonnegative
orders, and `w : ℂ → ℕ → ℂ` be arbitrary complex jet data. Then there exists `f ∈ H(Ω)` such that
`f^(n)(a) = n! * w a n` for every `a ∈ A` and every `0 ≤ n ≤ m a`. -/
theorem theorem15_13 {Ω A : Set ℂ}
    (hΩ : IsOpen Ω) (hAΩ : A ⊆ Ω)
    (hacc : ∀ z ∈ Ω, ¬ AccPt z (𝓟 A))
    (m : ℂ → ℕ) (w : ℂ → ℕ → ℂ) :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f Ω ∧
      ∀ a ∈ A, ∀ n ≤ m a, iteratedDeriv n f a = (n.factorial : ℂ) * w a n := by
  classical
  have hacc_cl : ∀ z ∈ Ω, z ∉ closure (A \ {z}) :=
    fun z hz ↦ mt accPt_principal_iff_mem_closure_diff.mpr (hacc z hz)
  have hopen_sdiff : IsOpen (Ω \ A) := RudinRCA.Chapter10.isOpen_sdiff_of_no_accPt hΩ hacc
  let M : ℂ → ℕ := fun a ↦ m a + 1
  have hM_pos : ∀ a ∈ A, 0 < M a := fun a _ ↦ Nat.succ_pos _
  obtain ⟨h, hh_diff, _, hh_fin, hh_ord⟩ :=
    exists_holomorphic_prescribed_zeros_plane hΩ hAΩ hacc_cl hM_pos
  let W : ℂ → ℂ → ℂ := fun a z ↦ ∑ k ∈ Finset.range (m a + 1), w a k * (z - a) ^ k
  have hex_local : ∀ a : A, ∃ (r : ℝ) (u R : ℂ → ℂ) (d : ℕ → ℂ),
      0 < r ∧ Metric.ball a.1 r ⊆ Ω ∧
      RudinRCA.Chapter10.HolomorphicOn u (Metric.ball a.1 r) ∧
      RudinRCA.Chapter10.HolomorphicOn R (Metric.ball a.1 r) ∧
      (∀ z ∈ Metric.ball a.1 r, u z ≠ 0) ∧
      (∀ z ∈ Metric.ball a.1 r, h z = (z - a.1) ^ (m a.1 + 1) * u z) ∧
      (∀ z ∈ Metric.ball a.1 r,
        W a.1 z = (∑ j ∈ Finset.range (m a.1 + 1), d j * (z - a.1) ^ j) * u z +
          (z - a.1) ^ (m a.1 + 1) * (R z * u z)) := by
    intro ⟨a, ha⟩
    have haΩ : a ∈ Ω := hAΩ ha
    have han_h : AnalyticAt ℂ h a := hh_diff.analyticAt (hΩ.mem_nhds haΩ)
    obtain ⟨u, hu_an, hu0, hhu⟩ := han_h.analyticOrderAt_ne_top.mp (hh_fin a haΩ)
    have hord_a : analyticOrderNatAt h a = m a + 1 := by
      simpa [M, ha] using hh_ord a haΩ
    have hhu' : h =ᶠ[𝓝 a] fun z ↦ (z - a) ^ (m a + 1) * u z := by
      simpa only [hord_a, smul_eq_mul] using hhu
    have hnhds : Ω ∩ {z | AnalyticAt ℂ u z} ∩ {z | u z ≠ 0} ∩
        {z | h z = (z - a) ^ (m a + 1) * u z} ∈ 𝓝 a :=
      Filter.inter_mem
        (Filter.inter_mem
          (Filter.inter_mem (hΩ.mem_nhds haΩ) hu_an.eventually_analyticAt)
          (hu_an.continuousAt.eventually_ne hu0))
        hhu'
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    let B : Set ℂ := Metric.ball a r
    have hB_Ω : B ⊆ Ω := fun z hz ↦ (hball hz).1.1.1
    have hu_holo : RudinRCA.Chapter10.HolomorphicOn u B :=
      fun z hz ↦ (hball hz).1.1.2.differentiableAt
    have hu_nz : ∀ z ∈ B, u z ≠ 0 := fun z hz ↦ (hball hz).1.2
    have hh_B : ∀ z ∈ B, h z = (z - a) ^ (m a + 1) * u z := fun z hz ↦ (hball hz).2
    have hW_holo : RudinRCA.Chapter10.HolomorphicOn (W a) B := by
      intro z _
      dsimp only [W]
      refine DifferentiableAt.fun_sum fun k _ ↦ ?_
      exact (differentiableAt_const (w a k)).mul ((differentiableAt_id.sub_const a).pow k)
    have hq_holo : RudinRCA.Chapter10.HolomorphicOn (fun z ↦ W a z / u z) B :=
      fun z hz ↦ (hW_holo z hz).div (hu_holo z hz) (hu_nz z hz)
    obtain ⟨d, R, hR_holo, _, hq_taylor⟩ := RudinRCA.Chapter10.dslope_taylor_expansion
      Metric.isOpen_ball (Metric.mem_ball_self hr) hq_holo (m a + 1)
    refine ⟨r, u, R, d, hr, hB_Ω, hu_holo, hR_holo, hu_nz, hh_B, ?_⟩
    intro z hz
    have hmul := congrArg (fun x ↦ x * u z) (hq_taylor z)
    rw [div_mul_cancel₀ _ (hu_nz z hz)] at hmul
    linear_combination hmul
  choose r_p u_p R_p d_p hr_pos hB_sub hu_holo hR_holo _ hh_B hW_eq using hex_local
  let c : ℂ → ℕ → ℂ := fun a k ↦
    if ha : a ∈ A then
      if k ∈ Finset.Icc 1 (m a + 1) then d_p ⟨a, ha⟩ (m a + 1 - k) else 0
    else 0
  obtain ⟨φ, hφ_mero, hφ_local⟩ := RudinRCA.Chapter13.theorem13_10 hΩ hAΩ hacc M hM_pos c
  have hA_eff_sub : {α ∈ A | ∃ j ∈ Finset.Icc 1 (M α), c α j ≠ 0} ⊆ A := fun _ hα ↦ hα.1
  have hφ_holo_sdiff : RudinRCA.Chapter10.HolomorphicOn φ (Ω \ A) := by
    intro z hz
    exact hφ_mero.2.2.2.1 z ⟨hz.1, fun h ↦ hz.2 (hA_eff_sub h)⟩
  let f : ℂ → ℂ := fun z ↦ if z ∈ A then w z 0 else φ z * h z
  have hf_local_ball : ∀ p : A, ∃ (ρ : ℝ) (H : ℂ → ℂ),
      0 < ρ ∧ Metric.ball p.1 ρ ⊆ Ω ∧
      RudinRCA.Chapter10.HolomorphicOn H (Metric.ball p.1 ρ) ∧
      ∀ z ∈ Metric.ball p.1 ρ, f z = W p.1 z + (z - p.1) ^ (m p.1 + 1) * H z := by
    intro p
    obtain ⟨V, g_p, hV_open, hpV, _, hVsdiff, hg_holo, hφ_eq⟩ := hφ_local p.1 p.2
    have hU_nhds : Metric.ball p.1 (r_p p) ∩ V ∈ 𝓝 p.1 :=
      Filter.inter_mem (Metric.ball_mem_nhds p.1 (hr_pos p)) (hV_open.mem_nhds hpV)
    obtain ⟨ρ, hρ, hball_ρ⟩ := Metric.mem_nhds_iff.mp hU_nhds
    let H : ℂ → ℂ := fun z ↦ (g_p z - R_p p z) * u_p p z
    have hH_holo : RudinRCA.Chapter10.HolomorphicOn H (Metric.ball p.1 ρ) := by
      intro z hz
      obtain ⟨hzB, hzV⟩ := hball_ρ hz
      exact ((hg_holo z hzV).sub (hR_holo p z hzB)).mul (hu_holo p z hzB)
    refine ⟨ρ, H, hρ, fun z hz ↦ hB_sub p (hball_ρ hz).1, hH_holo, ?_⟩
    intro z hz
    obtain ⟨hzB, hzV⟩ := hball_ρ hz
    by_cases hzp : z = p.1
    · subst hzp
      have hW0 : W p.1 p.1 = w p.1 0 := by
        dsimp only [W]
        rw [Finset.sum_eq_single 0]
        · simp
        · intro k _ hk0
          simp [zero_pow hk0]
        · intro hnot
          exact (hnot (Finset.mem_range.mpr (Nat.succ_pos _))).elim
      simp [f, p.2, hW0, zero_pow (Nat.succ_ne_zero _)]
    · have hz_sdiff : z ∈ Ω \ A := hVsdiff ⟨hzV, hzp⟩
      have hz_notA : z ∉ A := hz_sdiff.2
      have hsub_ne : z - p.1 ≠ 0 := sub_ne_zero.mpr hzp
      have hφ_z := hφ_eq ⟨hzV, hzp⟩
      have hsum_cancel :
          (∑ j ∈ Finset.Icc 1 (m p.1 + 1), c p.1 j * (z - p.1)⁻¹ ^ j) *
            (z - p.1) ^ (m p.1 + 1) =
          ∑ i ∈ Finset.range (m p.1 + 1), d_p p i * (z - p.1) ^ i := by
        rw [Finset.sum_mul]
        refine Finset.sum_nbij (fun j ↦ m p.1 + 1 - j) ?_ ?_ ?_ ?_
        · intro j hj
          simp only [Finset.mem_Icc] at hj
          exact Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))
        · intro j₁ hj₁ j₂ hj₂ h
          simp only [Finset.mem_coe, Finset.mem_Icc] at hj₁ hj₂
          dsimp at h
          omega
        · intro i hi
          simp only [Finset.mem_coe, Finset.mem_range] at hi
          refine ⟨m p.1 + 1 - i,
            Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), ?_⟩
          dsimp
          omega
        · intro j hj
          have hj_mem : j ∈ Finset.Icc 1 (m p.1 + 1) := hj
          obtain ⟨hj1, hj_le⟩ := Finset.mem_Icc.mp hj_mem
          have hpow_split : (z - p.1) ^ (m p.1 + 1) =
              (z - p.1) ^ j * (z - p.1) ^ (m p.1 + 1 - j) := by
            rw [← pow_add, Nat.add_sub_of_le hj_le]
          have hcancel : (z - p.1)⁻¹ ^ j * (z - p.1) ^ j = 1 := by
            rw [← mul_pow, inv_mul_cancel₀ hsub_ne, one_pow]
          have hc_eq : c p.1 j = d_p p (m p.1 + 1 - j) := by
            simp [c, p.2, hj1, hj_le]
          calc
            c p.1 j * (z - p.1)⁻¹ ^ j * (z - p.1) ^ (m p.1 + 1)
                = d_p p (m p.1 + 1 - j) *
                    (((z - p.1)⁻¹ ^ j * (z - p.1) ^ j) * (z - p.1) ^ (m p.1 + 1 - j)) := by
                    rw [hc_eq, hpow_split]; ring
            _ = d_p p (m p.1 + 1 - j) * (z - p.1) ^ (m p.1 + 1 - j) := by
                    rw [hcancel, one_mul]
      have hWz := hW_eq p z hzB
      simp only [f, hz_notA, ↓reduceIte, hφ_z, hh_B p z hzB, M, H]
      calc
        (g_p z + ∑ j ∈ Finset.Icc 1 (m p.1 + 1), c p.1 j * (z - p.1)⁻¹ ^ j) *
            ((z - p.1) ^ (m p.1 + 1) * u_p p z)
            = g_p z * (z - p.1) ^ (m p.1 + 1) * u_p p z +
                ((∑ j ∈ Finset.Icc 1 (m p.1 + 1), c p.1 j * (z - p.1)⁻¹ ^ j) *
                  (z - p.1) ^ (m p.1 + 1)) * u_p p z := by ring
        _ = g_p z * (z - p.1) ^ (m p.1 + 1) * u_p p z +
              (∑ i ∈ Finset.range (m p.1 + 1), d_p p i * (z - p.1) ^ i) * u_p p z := by
              rw [hsum_cancel]
        _ = W p.1 z + (z - p.1) ^ (m p.1 + 1) * ((g_p z - R_p p z) * u_p p z) := by
              linear_combination -hWz
  have hf_diff : DifferentiableOn ℂ f Ω := by
    intro z hzΩ
    by_cases hzA : z ∈ A
    · obtain ⟨ρ, H, hρ, _, hH_holo, hf_eq⟩ := hf_local_ball ⟨z, hzA⟩
      have hΨ_diff : DifferentiableAt ℂ (fun u ↦ W z u + (u - z) ^ (m z + 1) * H u) z := by
        have hW_diff : DifferentiableAt ℂ (W z) z := by
          dsimp only [W]
          refine DifferentiableAt.fun_sum fun k _ ↦ ?_
          exact (differentiableAt_const (w z k)).mul ((differentiableAt_id.sub_const z).pow k)
        exact hW_diff.add (((differentiableAt_id.sub_const z).pow (m z + 1)).mul
          (hH_holo z (Metric.mem_ball_self hρ)))
      have hev : f =ᶠ[𝓝 z] fun u ↦ W z u + (u - z) ^ (m z + 1) * H u := by
        filter_upwards [Metric.ball_mem_nhds z hρ] with u hu
        exact hf_eq u hu
      exact (hΨ_diff.congr_of_eventuallyEq hev).differentiableWithinAt
    · have hz_sdiff : z ∈ Ω \ A := ⟨hzΩ, hzA⟩
      have hev : f =ᶠ[𝓝 z] fun u ↦ φ u * h u := by
        filter_upwards [hopen_sdiff.mem_nhds hz_sdiff] with u hu
        simp [f, hu.2]
      have hd : DifferentiableAt ℂ (fun u ↦ φ u * h u) z :=
        (hφ_holo_sdiff z hz_sdiff).mul (hh_diff.differentiableAt (hΩ.mem_nhds hzΩ))
      exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt
  refine ⟨f, hf_diff, ?_⟩
  intro a ha n hn_le
  obtain ⟨ρ, H, hρ, _, hH_holo, hf_eq⟩ := hf_local_ball ⟨a, ha⟩
  let r : ℝ := ρ / 2
  have hr : 0 < r := half_pos hρ
  have hsub_r : RudinRCA.Chapter10.disc a r ⊆ Metric.ball a ρ :=
    Metric.ball_subset_ball (half_lt_self hρ).le
  obtain ⟨b, hb⟩ := RudinRCA.Chapter10.representableByPowerSeries_of_holomorphicOn hH_holo
    a r hr hsub_r
  let K : ℕ := m a + 1
  let coeff : ℕ → ℂ := fun k ↦ if k < K then w a k else b (k - K)
  have hf_sum : ∀ z ∈ RudinRCA.Chapter10.disc a r,
      HasSum (fun k ↦ coeff k * (z - a) ^ k) (f z) := by
    intro z hz
    have hz_ρ : z ∈ Metric.ball a ρ := hsub_r hz
    have hsum1 : HasSum (fun k ↦ (if k < K then w a k else 0) * (z - a) ^ k) (W a z) := by
      have hsupp : ∀ k ∉ Finset.range K, (if k < K then w a k else 0) * (z - a) ^ k = 0 := by
        intro k hk
        have hnot : ¬ k < K := by simpa [Finset.mem_range] using hk
        simp [hnot]
      have hfin_eq : (∑ k ∈ Finset.range K, (if k < K then w a k else 0) * (z - a) ^ k) = W a z := by
        dsimp only [W, K]
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        simp [Finset.mem_range.mp hk]
      rw [← hfin_eq]
      exact hasSum_sum_of_ne_finset_zero hsupp
    let g₂ : ℕ → ℂ := fun k ↦ (if k < K then 0 else b (k - K)) * (z - a) ^ k
    have hsum2 : HasSum g₂ ((z - a) ^ K * H z) := by
      have hzero_init : ∑ k ∈ Finset.range K, g₂ k = 0 := by
        refine Finset.sum_eq_zero fun k hk ↦ ?_
        simp [g₂, Finset.mem_range.mp hk]
      rw [← hasSum_nat_add_iff' K, hzero_init, sub_zero]
      have hshift : (fun j ↦ g₂ (j + K)) = fun j ↦ (z - a) ^ K * (b j * (z - a) ^ j) := by
        funext j
        have hnot : ¬ j + K < K := by omega
        simp only [g₂, hnot, ↓reduceIte, Nat.add_sub_cancel, pow_add]
        ring
      rw [hshift]
      exact (hb z hz).mul_left ((z - a) ^ K)
    rw [hf_eq z hz_ρ]
    refine (hsum1.add hsum2).congr_fun fun k ↦ ?_
    by_cases hk : k < K <;> simp [coeff, g₂, hk]
  have hcoeff := RudinRCA.Chapter10.powerSeries_coefficient hr hf_sum n
  have hn_lt : n < K := Nat.lt_succ_of_le hn_le
  simpa [coeff, hn_lt] using hcoeff.symm

/-! ## 15.14 & 15.15: Finitely Generated Ideals in `H(Ω)` and the Bézout Property -/

/-- Definition 15.14: The commutative ring `H(Ω)` of holomorphic functions on `Ω ⊆ ℂ`, represented
by functions `f : Ω → ℂ` admitting a `ℂ`-differentiable ambient representative on `Ω`. -/
def HolomorphicRing (Ω : Set ℂ) : Type :=
  {f : Ω → ℂ // ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧ ∀ z : Ω, f z = F z}

instance instCoeFunHolomorphicRing (Ω : Set ℂ) : CoeFun (HolomorphicRing Ω) (fun _ ↦ Ω → ℂ) :=
  ⟨Subtype.val⟩

instance instCommRingHolomorphicRing (Ω : Set ℂ) : CommRing (HolomorphicRing Ω) := by
  let zeroH : HolomorphicRing Ω := ⟨0, 0, differentiableOn_const 0, fun _ ↦ rfl⟩
  let oneH : HolomorphicRing Ω := ⟨1, 1, differentiableOn_const 1, fun _ ↦ rfl⟩
  let addH : HolomorphicRing Ω → HolomorphicRing Ω → HolomorphicRing Ω :=
    fun f g ↦ ⟨f.1 + g.1, fun w ↦ f.2.choose w + g.2.choose w,
      f.2.choose_spec.1.add g.2.choose_spec.1,
      fun z ↦ by change f.1 z + g.1 z = _; rw [f.2.choose_spec.2 z, g.2.choose_spec.2 z]⟩
  let mulH : HolomorphicRing Ω → HolomorphicRing Ω → HolomorphicRing Ω :=
    fun f g ↦ ⟨f.1 * g.1, fun w ↦ f.2.choose w * g.2.choose w,
      f.2.choose_spec.1.mul g.2.choose_spec.1,
      fun z ↦ by change f.1 z * g.1 z = _; rw [f.2.choose_spec.2 z, g.2.choose_spec.2 z]⟩
  let negH : HolomorphicRing Ω → HolomorphicRing Ω :=
    fun f ↦ ⟨-f.1, fun w ↦ -f.2.choose w, f.2.choose_spec.1.neg,
      fun z ↦ by change -f.1 z = _; rw [f.2.choose_spec.2 z]⟩
  let subH : HolomorphicRing Ω → HolomorphicRing Ω → HolomorphicRing Ω :=
    fun f g ↦ ⟨f.1 - g.1, fun w ↦ f.2.choose w - g.2.choose w,
      f.2.choose_spec.1.sub g.2.choose_spec.1,
      fun z ↦ by change f.1 z - g.1 z = _; rw [f.2.choose_spec.2 z, g.2.choose_spec.2 z]⟩
  let nsmulH : ℕ → HolomorphicRing Ω → HolomorphicRing Ω :=
    fun n f ↦ ⟨n • f.1, fun w ↦ (n : ℂ) * f.2.choose w,
      (differentiableOn_const (n : ℂ)).mul f.2.choose_spec.1,
      fun z ↦ by change n • f.1 z = _; rw [f.2.choose_spec.2 z, nsmul_eq_mul]⟩
  let zsmulH : ℤ → HolomorphicRing Ω → HolomorphicRing Ω :=
    fun n f ↦ ⟨n • f.1, fun w ↦ (n : ℂ) * f.2.choose w,
      (differentiableOn_const (n : ℂ)).mul f.2.choose_spec.1,
      fun z ↦ by change n • f.1 z = _; rw [f.2.choose_spec.2 z, zsmul_eq_mul]⟩
  let npowH : ℕ → HolomorphicRing Ω → HolomorphicRing Ω :=
    fun n f ↦ ⟨f.1 ^ n, fun w ↦ f.2.choose w ^ n, f.2.choose_spec.1.pow n,
      fun z ↦ by change f.1 z ^ n = _; rw [f.2.choose_spec.2 z]⟩
  let natCastH : ℕ → HolomorphicRing Ω :=
    fun n ↦ ⟨(n : Ω → ℂ), fun _ ↦ (n : ℂ), differentiableOn_const _, fun _ ↦ rfl⟩
  let intCastH : ℤ → HolomorphicRing Ω :=
    fun n ↦ ⟨(n : Ω → ℂ), fun _ ↦ (n : ℂ), differentiableOn_const _, fun _ ↦ rfl⟩
  letI : Zero (HolomorphicRing Ω) := ⟨zeroH⟩
  letI : One (HolomorphicRing Ω) := ⟨oneH⟩
  letI : Add (HolomorphicRing Ω) := ⟨addH⟩
  letI : Mul (HolomorphicRing Ω) := ⟨mulH⟩
  letI : Neg (HolomorphicRing Ω) := ⟨negH⟩
  letI : Sub (HolomorphicRing Ω) := ⟨subH⟩
  letI : SMul ℕ (HolomorphicRing Ω) := ⟨nsmulH⟩
  letI : SMul ℤ (HolomorphicRing Ω) := ⟨zsmulH⟩
  letI : Pow (HolomorphicRing Ω) ℕ := ⟨fun f n ↦ npowH n f⟩
  letI : NatCast (HolomorphicRing Ω) := ⟨natCastH⟩
  letI : IntCast (HolomorphicRing Ω) := ⟨intCastH⟩
  exact Function.Injective.commRing Subtype.val Subtype.val_injective
    rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

@[simp] theorem HolomorphicRing.val_zero {Ω : Set ℂ} :
    (0 : HolomorphicRing Ω).1 = 0 := rfl

@[simp] theorem HolomorphicRing.val_one {Ω : Set ℂ} :
    (1 : HolomorphicRing Ω).1 = 1 := rfl

@[simp] theorem HolomorphicRing.val_add {Ω : Set ℂ} (f g : HolomorphicRing Ω) :
    (f + g).1 = f.1 + g.1 := rfl

@[simp] theorem HolomorphicRing.val_mul {Ω : Set ℂ} (f g : HolomorphicRing Ω) :
    (f * g).1 = f.1 * g.1 := rfl

/-- Definition 15.14: Zero multiplicity `m(f, a)` of `f ∈ H(Ω)` at `a ∈ Ω`, equal to `0` when
`f a ≠ 0` and `analyticOrderNatAt F a` otherwise for an ambient holomorphic representative `F`. -/
def holomorphicZeroMultiplicity {Ω : Set ℂ} (f : HolomorphicRing Ω) (a : Ω) : ℕ :=
  if f.1 a ≠ 0 then 0 else analyticOrderNatAt f.2.choose a.1

/-- **Rudin RCA 15.14** (Finitely generated ideals, principal ideals, and zero multiplicity in `H(Ω)`):
1. Membership in the ideal generated by `g₁, ..., g_k ∈ H(Ω)` holds iff `f = ∑ i, c_i * g_i` for
   some `c_1, ..., c_k ∈ H(Ω)`;
2. An ideal `I` of `H(Ω)` is principal iff `I = Ideal.span {d}` for a single generator `d ∈ H(Ω)`,
   and `f ∈ Ideal.span {d} ↔ ∃ h ∈ H(Ω), f = h * d`;
3. On an open set `Ω`, `holomorphicZeroMultiplicity f a = 0` whenever `f a ≠ 0`, and for every
   ambient holomorphic representative `F` of `f` on `Ω`,
   `holomorphicZeroMultiplicity f a = analyticOrderNatAt F a`. -/
theorem theorem15_14 {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    (∀ {k : ℕ} (g : Fin k → HolomorphicRing Ω) (f : HolomorphicRing Ω),
      f ∈ Ideal.span (Set.range g) ↔ ∃ c : Fin k → HolomorphicRing Ω, f = ∑ i, c i * g i) ∧
    (∀ I : Ideal (HolomorphicRing Ω),
      I.IsPrincipal ↔ ∃ d : HolomorphicRing Ω, I = Ideal.span {d}) ∧
    (∀ d f : HolomorphicRing Ω,
      f ∈ Ideal.span ({d} : Set (HolomorphicRing Ω)) ↔ ∃ h : HolomorphicRing Ω, f = h * d) ∧
    (∀ (f : HolomorphicRing Ω) (a : Ω),
      (f.1 a ≠ 0 → holomorphicZeroMultiplicity f a = 0) ∧
      (∀ F : ℂ → ℂ, DifferentiableOn ℂ F Ω → (∀ z : Ω, f.1 z = F z) →
        holomorphicZeroMultiplicity f a = analyticOrderNatAt F a.1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k g f
    simpa [smul_eq_mul, eq_comm] using
      (Submodule.mem_span_range_iff_exists_fun (R := HolomorphicRing Ω) (v := g) (x := f))
  · intro I
    exact ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩
  · intro d f
    rw [Ideal.mem_span_singleton]
    exact ⟨fun ⟨h, hh⟩ ↦ ⟨h, by rw [hh, mul_comm]⟩, fun ⟨h, hh⟩ ↦ ⟨h, by rw [hh, mul_comm]⟩⟩
  · intro f a
    refine ⟨fun hne ↦ by simp [holomorphicZeroMultiplicity, hne], ?_⟩
    intro F hF hFeq
    have hev : f.2.choose =ᶠ[𝓝 a.1] F := by
      filter_upwards [hΩ.mem_nhds a.2] with w hw
      rw [← f.2.choose_spec.2 ⟨w, hw⟩, hFeq ⟨w, hw⟩]
    have hord_eq : analyticOrderAt f.2.choose a.1 = analyticOrderAt F a.1 :=
      analyticOrderAt_congr hev
    by_cases hne : f.1 a ≠ 0
    · have hFa : F a.1 ≠ 0 := hFeq a ▸ hne
      have han_F : AnalyticAt ℂ F a.1 := hF.analyticAt (hΩ.mem_nhds a.2)
      have hord0 : analyticOrderAt F a.1 = 0 := han_F.analyticOrderAt_eq_zero.mpr hFa
      simp [holomorphicZeroMultiplicity, hne, analyticOrderNatAt, hord0]
    · simp only [holomorphicZeroMultiplicity, hne, ↓reduceIte, analyticOrderNatAt]
      rw [hord_eq]

/-- Reusable removable-quotient helper on open `U ⊆ ℂ`: if `num, den ∈ H(U)` with
`analyticOrderAt den z ≠ ⊤` and `analyticOrderAt den z ≤ analyticOrderAt num z` on `U`, then
`q := toMeromorphicNFOn (num / den) U` belongs to `H(U)`, satisfies `num z = q z * den z` on `U`,
and satisfies `q z ≠ 0 ↔ analyticOrderAt num z = analyticOrderAt den z` on `U`. -/
private theorem exists_holomorphic_quotient_of_order_le {U : Set ℂ} {num den : ℂ → ℂ}
    (hU : IsOpen U)
    (hnum : DifferentiableOn ℂ num U) (hden : DifferentiableOn ℂ den U)
    (hden_fin : ∀ z ∈ U, analyticOrderAt den z ≠ ⊤)
    (hle : ∀ z ∈ U, analyticOrderAt den z ≤ analyticOrderAt num z) :
    ∃ q : ℂ → ℂ,
      DifferentiableOn ℂ q U ∧
      (∀ z ∈ U, num z = q z * den z) ∧
      (∀ z ∈ U, q z ≠ 0 ↔ analyticOrderAt num z = analyticOrderAt den z) := by
  let q : ℂ → ℂ := toMeromorphicNFOn (num / den) U
  have hm : MeromorphicOn (num / den) U :=
    fun z hz ↦ (hnum.analyticAt (hU.mem_nhds hz)).meromorphicAt.div
      (hden.analyticAt (hU.mem_nhds hz)).meromorphicAt
  have hnf : ∀ z ∈ U, MeromorphicNFAt q z :=
    fun z hz ↦ meromorphicNFOn_toMeromorphicNFOn (num / den) U hz
  have hord_calc : ∀ z ∈ U,
      0 ≤ meromorphicOrderAt q z ∧
      (meromorphicOrderAt q z = 0 ↔ analyticOrderAt num z = analyticOrderAt den z) := by
    intro z hz
    have hnum_an : AnalyticAt ℂ num z := hnum.analyticAt (hU.mem_nhds hz)
    have hden_an : AnalyticAt ℂ den z := hden.analyticAt (hU.mem_nhds hz)
    have hq_ord : meromorphicOrderAt q z =
        meromorphicOrderAt num z - meromorphicOrderAt den z := by
      dsimp only [q]
      rw [meromorphicOrderAt_toMeromorphicNFOn hm hz,
        meromorphicOrderAt_div hnum_an.meromorphicAt hden_an.meromorphicAt]
    rw [hq_ord, hnum_an.meromorphicOrderAt_eq, hden_an.meromorphicOrderAt_eq]
    obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (hden_fin z hz)
    rw [← hb]
    by_cases htop : analyticOrderAt num z = ⊤
    · rw [htop]
      refine ⟨by simp, ?_⟩
      simp
    · obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp htop
      rw [← ha]
      have hba : b ≤ a := by
        have h := hle z hz
        rw [← hb, ← ha] at h
        exact Nat.cast_le.mp h
      change 0 ≤ (((a : ℤ) - (b : ℤ) : ℤ) : WithTop ℤ) ∧
        ((((a : ℤ) - (b : ℤ) : ℤ) : WithTop ℤ) = 0 ↔ (a : ℕ∞) = (b : ℕ∞))
      rw [WithTop.coe_nonneg, WithTop.coe_eq_zero]
      exact ⟨by omega, ⟨fun h ↦ congrArg Nat.cast (by omega : a = b),
        fun h ↦ by have hab : a = b := Nat.cast_injective h; omega⟩⟩
  have hq_an : ∀ z ∈ U, AnalyticAt ℂ q z :=
    fun z hz ↦ (hnf z hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hord_calc z hz).1
  have hq_diff : DifferentiableOn ℂ q U :=
    fun z hz ↦ (hq_an z hz).differentiableAt.differentiableWithinAt
  refine ⟨q, hq_diff, ?_, ?_⟩
  · intro z hz
    have hden_an : AnalyticAt ℂ den z := hden.analyticAt (hU.mem_nhds hz)
    have hne : ∀ᶠ w in 𝓝[≠] z, den w ≠ 0 :=
      hden_an.eventually_eq_zero_or_eventually_ne_zero.resolve_left
        (fun h ↦ hden_fin z hz (analyticOrderAt_eq_top.mpr h))
    have heq : (fun w ↦ q w * den w) =ᶠ[𝓝[≠] z] num := by
      filter_upwards [hm.toMeromorphicNFOn_eq_self_on_nhdsNE hz, hne] with w hw hdw
      change q w = num w / den w at hw
      rw [hw, div_mul_cancel₀ _ hdw]
    have hmul_cont : ContinuousAt (fun w ↦ q w * den w) z :=
      (hq_an z hz).continuousAt.mul hden_an.continuousAt
    have hnum_cont : ContinuousAt num z := (hnum.analyticAt (hU.mem_nhds hz)).continuousAt
    exact ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hmul_cont hnum_cont).mp
      heq).eq_of_nhds.symm
  · intro z hz
    rw [← (hnf z hz).meromorphicOrderAt_eq_zero_iff, (hord_calc z hz).2]

/-- Clopenness of `{z ∈ Ω | analyticOrderAt g z = ⊤}` for `g ∈ H(Ω)` on open `Ω`. -/
private theorem isOpen_analyticOrderAt_eq_top_and_ne_top {Ω : Set ℂ} {g : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) :
    IsOpen {z ∈ Ω | analyticOrderAt g z = ⊤} ∧
    IsOpen {z ∈ Ω | analyticOrderAt g z ≠ ⊤} := by
  constructor
  · rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzΩ, htop⟩
    have hcomp_open : IsOpen (connectedComponentIn Ω z) := hΩ.connectedComponentIn
    have hcomp_sub : connectedComponentIn Ω z ⊆ Ω := connectedComponentIn_subset Ω z
    have han_comp : AnalyticOnNhd ℂ g (connectedComponentIn Ω z) :=
      (hg.analyticOnNhd hΩ).mono hcomp_sub
    have hzero_comp := han_comp.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_connectedComponentIn (mem_connectedComponentIn hzΩ)
      (analyticOrderAt_eq_top.mp htop)
    filter_upwards [hcomp_open.mem_nhds (mem_connectedComponentIn hzΩ)] with u hu
    refine ⟨hcomp_sub hu, analyticOrderAt_eq_top.mpr ?_⟩
    filter_upwards [hcomp_open.mem_nhds hu] with w hw
    exact hzero_comp hw
  · rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzΩ, hne_top⟩
    have hcomp_open : IsOpen (connectedComponentIn Ω z) := hΩ.connectedComponentIn
    have hcomp_sub : connectedComponentIn Ω z ⊆ Ω := connectedComponentIn_subset Ω z
    have han_comp : AnalyticOnNhd ℂ g (connectedComponentIn Ω z) :=
      (hg.analyticOnNhd hΩ).mono hcomp_sub
    filter_upwards [hcomp_open.mem_nhds (mem_connectedComponentIn hzΩ)] with u hu
    refine ⟨hcomp_sub hu, ?_⟩
    intro hutop
    have hzero_comp := han_comp.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_connectedComponentIn hu (analyticOrderAt_eq_top.mp hutop)
    apply hne_top
    refine analyticOrderAt_eq_top.mpr ?_
    filter_upwards [hcomp_open.mem_nhds (mem_connectedComponentIn hzΩ)] with w hw
    exact hzero_comp hw

/-- Binary Bézout step on an arbitrary open set `Ω ⊆ ℂ` (including disconnected `Ω`, `Ω = ∅`, and
generators vanishing on some or all connected components of `Ω`). -/
private theorem exists_bezout_pair_holomorphic {Ω : Set ℂ} {g₁ g₂ : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hg₁ : DifferentiableOn ℂ g₁ Ω) (hg₂ : DifferentiableOn ℂ g₂ Ω) :
    ∃ d f₁ f₂ h₁ h₂ : ℂ → ℂ,
      DifferentiableOn ℂ d Ω ∧
      DifferentiableOn ℂ f₁ Ω ∧
      DifferentiableOn ℂ f₂ Ω ∧
      DifferentiableOn ℂ h₁ Ω ∧
      DifferentiableOn ℂ h₂ Ω ∧
      (∀ z ∈ Ω, d z = f₁ z * g₁ z + f₂ z * g₂ z) ∧
      (∀ z ∈ Ω, g₁ z = h₁ z * d z) ∧
      (∀ z ∈ Ω, g₂ z = h₂ z * d z) := by
  classical
  obtain ⟨hT₁, hN₁⟩ := isOpen_analyticOrderAt_eq_top_and_ne_top hΩ hg₁
  obtain ⟨hT₂, hN₂⟩ := isOpen_analyticOrderAt_eq_top_and_ne_top hΩ hg₂
  let Ω₀₀ : Set ℂ := {z ∈ Ω | analyticOrderAt g₁ z = ⊤} ∩ {z ∈ Ω | analyticOrderAt g₂ z = ⊤}
  let Ω₁₀ : Set ℂ := {z ∈ Ω | analyticOrderAt g₁ z ≠ ⊤} ∩ {z ∈ Ω | analyticOrderAt g₂ z = ⊤}
  let Ω₀₁ : Set ℂ := {z ∈ Ω | analyticOrderAt g₁ z = ⊤} ∩ {z ∈ Ω | analyticOrderAt g₂ z ≠ ⊤}
  let Ω₁₁ : Set ℂ := {z ∈ Ω | analyticOrderAt g₁ z ≠ ⊤} ∩ {z ∈ Ω | analyticOrderAt g₂ z ≠ ⊤}
  have hΩ₀₀_open : IsOpen Ω₀₀ := hT₁.inter hT₂
  have hΩ₁₀_open : IsOpen Ω₁₀ := hN₁.inter hT₂
  have hΩ₀₁_open : IsOpen Ω₀₁ := hT₁.inter hN₂
  have hΩ₁₁_open : IsOpen Ω₁₁ := hN₁.inter hN₂
  have hΩ₁₁_sub : Ω₁₁ ⊆ Ω := fun _ hz ↦ hz.1.1
  -- Solve on `Ω₁₁` where both `g₁` and `g₂` have finite order everywhere
  let hg₁_11 : DifferentiableOn ℂ g₁ Ω₁₁ := hg₁.mono hΩ₁₁_sub
  let hg₂_11 : DifferentiableOn ℂ g₂ Ω₁₁ := hg₂.mono hΩ₁₁_sub
  let A : Set ℂ := {z ∈ Ω₁₁ | g₁ z = 0 ∧ g₂ z = 0}
  let m : ℂ → ℕ := fun z ↦ min (analyticOrderNatAt g₁ z) (analyticOrderNatAt g₂ z)
  have hA_sub : A ⊆ Ω₁₁ := fun _ hz ↦ hz.1
  have hA_no_acc : ∀ z ∈ Ω₁₁, z ∉ closure (A \ {z}) := by
    intro z hz hmem
    have hcomp_open : IsOpen (connectedComponentIn Ω₁₁ z) := hΩ₁₁_open.connectedComponentIn
    have hcomp_sub : connectedComponentIn Ω₁₁ z ⊆ Ω₁₁ := connectedComponentIn_subset Ω₁₁ z
    have han_comp : AnalyticOnNhd ℂ g₁ (connectedComponentIn Ω₁₁ z) :=
      (hg₁_11.analyticOnNhd hΩ₁₁_open).mono hcomp_sub
    have hmem' : z ∈ closure ({w : ℂ | g₁ w = 0} \ {z}) :=
      closure_mono (s := A \ {z}) (t := {w : ℂ | g₁ w = 0} \ {z})
        (fun _ hw ↦ ⟨hw.1.2.1, hw.2⟩) hmem
    have hzero_comp := han_comp.eqOn_zero_of_preconnected_of_mem_closure
      isPreconnected_connectedComponentIn (mem_connectedComponentIn hz) hmem'
    apply hz.1.2
    refine analyticOrderAt_eq_top.mpr ?_
    filter_upwards [hcomp_open.mem_nhds (mem_connectedComponentIn hz)] with w hw
    exact hzero_comp hw
  have hm_pos : ∀ a ∈ A, 0 < m a := by
    rintro a ⟨ha11, hg1a, hg2a⟩
    have han1 : AnalyticAt ℂ g₁ a := hg₁_11.analyticAt (hΩ₁₁_open.mem_nhds ha11)
    have han2 : AnalyticAt ℂ g₂ a := hg₂_11.analyticAt (hΩ₁₁_open.mem_nhds ha11)
    have hpos1 : 0 < analyticOrderNatAt g₁ a := by
      by_contra hle
      have h0 : analyticOrderNatAt g₁ a = 0 := Nat.eq_zero_of_not_pos hle
      have hord0 : analyticOrderAt g₁ a = 0 := by
        rw [← Nat.cast_analyticOrderNatAt ha11.1.2, h0, Nat.cast_zero]
      exact (han1.analyticOrderAt_eq_zero.mp hord0) hg1a
    have hpos2 : 0 < analyticOrderNatAt g₂ a := by
      by_contra hle
      have h0 : analyticOrderNatAt g₂ a = 0 := Nat.eq_zero_of_not_pos hle
      have hord0 : analyticOrderAt g₂ a = 0 := by
        rw [← Nat.cast_analyticOrderNatAt ha11.2.2, h0, Nat.cast_zero]
      exact (han2.analyticOrderAt_eq_zero.mp hord0) hg2a
    exact lt_min hpos1 hpos2
  obtain ⟨Φ, hΦ_diff, _, hΦ_fin, hΦ_ord⟩ :=
    exists_holomorphic_prescribed_zeros_plane hΩ₁₁_open hA_sub hA_no_acc hm_pos
  have hΦ_ord_min : ∀ z ∈ Ω₁₁,
      analyticOrderAt Φ z = min (analyticOrderAt g₁ z) (analyticOrderAt g₂ z) := by
    intro z hz
    rw [← Nat.cast_analyticOrderNatAt (hΦ_fin z hz), hΦ_ord z hz,
      ← Nat.cast_analyticOrderNatAt hz.1.2, ← Nat.cast_analyticOrderNatAt hz.2.2]
    by_cases hzA : z ∈ A
    · simp only [hzA, ↓reduceIte, m]
      rcases le_total (analyticOrderNatAt g₁ z) (analyticOrderNatAt g₂ z) with hle | hle
      · rw [min_eq_left hle, min_eq_left (Nat.cast_le.mpr hle)]
      · rw [min_eq_right hle, min_eq_right (Nat.cast_le.mpr hle)]
    · simp only [hzA, ↓reduceIte, Nat.cast_zero]
      have hnot : g₁ z ≠ 0 ∨ g₂ z ≠ 0 := by
        by_contra h
        push Not at h
        exact hzA ⟨hz, h.1, h.2⟩
      rcases hnot with h1 | h2
      · have ho1 : analyticOrderNatAt g₁ z = 0 := by
          have ho : analyticOrderAt g₁ z = 0 :=
            (hg₁_11.analyticAt (hΩ₁₁_open.mem_nhds hz)).analyticOrderAt_eq_zero.mpr h1
          simp [analyticOrderNatAt, ho]
        simp [ho1]
      · have ho2 : analyticOrderNatAt g₂ z = 0 := by
          have ho : analyticOrderAt g₂ z = 0 :=
            (hg₂_11.analyticAt (hΩ₁₁_open.mem_nhds hz)).analyticOrderAt_eq_zero.mpr h2
          simp [analyticOrderNatAt, ho]
        simp [ho2]
  obtain ⟨q₁, hq₁_diff, hq₁_mul, hq₁_nz⟩ := exists_holomorphic_quotient_of_order_le hΩ₁₁_open
    hg₁_11 hΦ_diff hΦ_fin (fun z hz ↦ by rw [hΦ_ord_min z hz]; exact min_le_left _ _)
  obtain ⟨q₂, hq₂_diff, hq₂_mul, hq₂_nz⟩ := exists_holomorphic_quotient_of_order_le hΩ₁₁_open
    hg₂_11 hΦ_diff hΦ_fin (fun z hz ↦ by rw [hΦ_ord_min z hz]; exact min_le_right _ _)
  have hcoprime : ∀ z ∈ Ω₁₁, q₁ z ≠ 0 ∨ q₂ z ≠ 0 := by
    intro z hz
    rw [hq₁_nz z hz, hq₂_nz z hz, hΦ_ord_min z hz]
    rcases min_cases (analyticOrderAt g₁ z) (analyticOrderAt g₂ z) with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hq₁_fin : ∀ z ∈ Ω₁₁, analyticOrderAt q₁ z ≠ ⊤ := by
    intro z hz htop
    have han_q₁ : AnalyticAt ℂ q₁ z := hq₁_diff.analyticAt (hΩ₁₁_open.mem_nhds hz)
    have han_Φ : AnalyticAt ℂ Φ z := hΦ_diff.analyticAt (hΩ₁₁_open.mem_nhds hz)
    have hev : g₁ =ᶠ[𝓝 z] q₁ * Φ := by
      filter_upwards [hΩ₁₁_open.mem_nhds hz] with w hw
      exact hq₁_mul w hw
    have hord_g₁ : analyticOrderAt g₁ z = ⊤ := by
      rw [analyticOrderAt_congr hev, analyticOrderAt_mul han_q₁ han_Φ, htop, top_add]
    exact hz.1.2 hord_g₁
  let B : Set ℂ := {z ∈ Ω₁₁ | q₁ z = 0}
  have hB_sub : B ⊆ Ω₁₁ := fun _ hz ↦ hz.1
  have hB_no_acc : ∀ z ∈ Ω₁₁, ¬ AccPt z (𝓟 B) := by
    intro z hz hacc
    have hmem : z ∈ closure (B \ {z}) := accPt_principal_iff_mem_closure_diff.mp hacc
    have hcomp_open : IsOpen (connectedComponentIn Ω₁₁ z) := hΩ₁₁_open.connectedComponentIn
    have hcomp_sub : connectedComponentIn Ω₁₁ z ⊆ Ω₁₁ := connectedComponentIn_subset Ω₁₁ z
    have han_comp : AnalyticOnNhd ℂ q₁ (connectedComponentIn Ω₁₁ z) :=
      (hq₁_diff.analyticOnNhd hΩ₁₁_open).mono hcomp_sub
    have hmem' : z ∈ closure ({w : ℂ | q₁ w = 0} \ {z}) :=
      closure_mono (s := B \ {z}) (t := {w : ℂ | q₁ w = 0} \ {z})
        (fun _ hw ↦ ⟨hw.1.2, hw.2⟩) hmem
    have hzero_comp := han_comp.eqOn_zero_of_preconnected_of_mem_closure
      isPreconnected_connectedComponentIn (mem_connectedComponentIn hz) hmem'
    apply hq₁_fin z hz
    refine analyticOrderAt_eq_top.mpr ?_
    filter_upwards [hcomp_open.mem_nhds (mem_connectedComponentIn hz)] with w hw
    exact hzero_comp hw
  let μ : ℂ → ℕ := fun a ↦ analyticOrderNatAt q₁ a
  let w_jet : ℂ → ℕ → ℂ :=
    fun a n ↦ iteratedDeriv n (fun z ↦ (q₂ z)⁻¹) a / (n.factorial : ℂ)
  obtain ⟨s₂, hs₂_diff, hs₂_jet⟩ := theorem15_13 hΩ₁₁_open hB_sub hB_no_acc μ w_jet
  have hrem_ord_le : ∀ z ∈ Ω₁₁,
      analyticOrderAt q₁ z ≤ analyticOrderAt (fun w ↦ 1 - s₂ w * q₂ w) z := by
    intro z hz
    by_cases hzB : z ∈ B
    · have hq₂_ne : q₂ z ≠ 0 := (hcoprime z hz).resolve_left (fun hne ↦ hne hzB.2)
      have hs₂_an : AnalyticAt ℂ s₂ z := hs₂_diff.analyticAt (hΩ₁₁_open.mem_nhds hz)
      have hq₂_an : AnalyticAt ℂ q₂ z := hq₂_diff.analyticAt (hΩ₁₁_open.mem_nhds hz)
      have hinv_an : AnalyticAt ℂ (fun w ↦ (q₂ w)⁻¹) z := hq₂_an.inv hq₂_ne
      let δ : ℂ → ℂ := fun w ↦ (q₂ w)⁻¹ - s₂ w
      have hδ_an : AnalyticAt ℂ δ z := hinv_an.sub hs₂_an
      have hδ_ord : (μ z : ℕ∞) ≤ analyticOrderAt δ z := by
        rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hδ_an]
        intro i hi
        have hi_le : i ≤ μ z := le_of_lt hi
        have hjet := hs₂_jet z hzB i hi_le
        have hfac_ne : (i.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr i.factorial_ne_zero
        have hderiv_eq : iteratedDeriv i s₂ z = iteratedDeriv i (fun u ↦ (q₂ u)⁻¹) z := by
          rw [hjet]
          dsimp [w_jet]
          exact mul_div_cancel₀ _ hfac_ne
        rw [iteratedDeriv_fun_sub hinv_an.contDiffAt hs₂_an.contDiffAt, hderiv_eq, sub_self]
      have hev_rem : (fun w ↦ 1 - s₂ w * q₂ w) =ᶠ[𝓝 z] δ * q₂ := by
        filter_upwards [hq₂_an.continuousAt.eventually_ne hq₂_ne] with w hqw
        change 1 - s₂ w * q₂ w = ((q₂ w)⁻¹ - s₂ w) * q₂ w
        rw [sub_mul, inv_mul_cancel₀ hqw]
      have hge : (μ z : ℕ∞) ≤ analyticOrderAt (fun w ↦ 1 - s₂ w * q₂ w) z := by
        rw [analyticOrderAt_congr hev_rem, analyticOrderAt_mul hδ_an hq₂_an]
        exact le_self_add.trans' hδ_ord
      rwa [← Nat.cast_analyticOrderNatAt (hq₁_fin z hz)]
    · have hq₁_ne : q₁ z ≠ 0 := fun h0 ↦ hzB ⟨hz, h0⟩
      have hord0 : analyticOrderAt q₁ z = 0 :=
        (hq₁_diff.analyticAt (hΩ₁₁_open.mem_nhds hz)).analyticOrderAt_eq_zero.mpr hq₁_ne
      rw [hord0]
      exact zero_le
  obtain ⟨s₁, hs₁_diff, hs₁_mul, _⟩ := exists_holomorphic_quotient_of_order_le hΩ₁₁_open
    ((differentiableOn_const (1 : ℂ)).sub (hs₂_diff.mul hq₂_diff)) hq₁_diff hq₁_fin hrem_ord_le
  -- Glue across the 4 pairwise-disjoint open regions `Ω₀₀, Ω₁₀, Ω₀₁, Ω₁₁`
  let d : ℂ → ℂ := fun z ↦
    if z ∈ Ω₀₀ then 0 else if z ∈ Ω₁₀ then g₁ z else if z ∈ Ω₀₁ then g₂ z else Φ z
  let f₁ : ℂ → ℂ := fun z ↦
    if z ∈ Ω₀₀ then 0 else if z ∈ Ω₁₀ then 1 else if z ∈ Ω₀₁ then 0 else s₁ z
  let f₂ : ℂ → ℂ := fun z ↦
    if z ∈ Ω₀₀ then 0 else if z ∈ Ω₁₀ then 0 else if z ∈ Ω₀₁ then 1 else s₂ z
  let h₁ : ℂ → ℂ := fun z ↦
    if z ∈ Ω₀₀ then 0 else if z ∈ Ω₁₀ then 1 else if z ∈ Ω₀₁ then 0 else q₁ z
  let h₂ : ℂ → ℂ := fun z ↦
    if z ∈ Ω₀₀ then 0 else if z ∈ Ω₁₀ then 0 else if z ∈ Ω₀₁ then 1 else q₂ z
  have hg₁_zero_of_top : ∀ z ∈ Ω, analyticOrderAt g₁ z = ⊤ → g₁ z = 0 :=
    fun z _ htop ↦ (analyticOrderAt_eq_top.mp htop).self_of_nhds
  have hg₂_zero_of_top : ∀ z ∈ Ω, analyticOrderAt g₂ z = ⊤ → g₂ z = 0 :=
    fun z _ htop ↦ (analyticOrderAt_eq_top.mp htop).self_of_nhds
  have hglue_diff : ∀ (F₀₀ F₁₀ F₀₁ F₁₁ : ℂ → ℂ),
      DifferentiableOn ℂ F₀₀ Ω₀₀ → DifferentiableOn ℂ F₁₀ Ω₁₀ →
      DifferentiableOn ℂ F₀₁ Ω₀₁ → DifferentiableOn ℂ F₁₁ Ω₁₁ →
      DifferentiableOn ℂ (fun z ↦
        if z ∈ Ω₀₀ then F₀₀ z else if z ∈ Ω₁₀ then F₁₀ z else if z ∈ Ω₀₁ then F₀₁ z else F₁₁ z) Ω := by
    intro F₀₀ F₁₀ F₀₁ F₁₁ h00 h10 h01 h11 z hzΩ
    by_cases ht1 : analyticOrderAt g₁ z = ⊤ <;> by_cases ht2 : analyticOrderAt g₂ z = ⊤
    · have hz00 : z ∈ Ω₀₀ := ⟨⟨hzΩ, ht1⟩, ⟨hzΩ, ht2⟩⟩
      have hev : (fun w ↦ if w ∈ Ω₀₀ then F₀₀ w else if w ∈ Ω₁₀ then F₁₀ w
          else if w ∈ Ω₀₁ then F₀₁ w else F₁₁ w) =ᶠ[𝓝 z] F₀₀ := by
        filter_upwards [hΩ₀₀_open.mem_nhds hz00] with w hw
        simp [hw]
      exact ((h00.differentiableAt (hΩ₀₀_open.mem_nhds hz00)).congr_of_eventuallyEq
        hev).differentiableWithinAt
    · have hz01 : z ∈ Ω₀₁ := ⟨⟨hzΩ, ht1⟩, ⟨hzΩ, ht2⟩⟩
      have hev : (fun w ↦ if w ∈ Ω₀₀ then F₀₀ w else if w ∈ Ω₁₀ then F₁₀ w
          else if w ∈ Ω₀₁ then F₀₁ w else F₁₁ w) =ᶠ[𝓝 z] F₀₁ := by
        filter_upwards [hΩ₀₁_open.mem_nhds hz01] with w hw
        have hn00 : w ∉ Ω₀₀ := fun h ↦ hw.2.2 h.2.2
        have hn10 : w ∉ Ω₁₀ := fun h ↦ h.1.2 hw.1.2
        simp [hn00, hn10, hw]
      exact ((h01.differentiableAt (hΩ₀₁_open.mem_nhds hz01)).congr_of_eventuallyEq
        hev).differentiableWithinAt
    · have hz10 : z ∈ Ω₁₀ := ⟨⟨hzΩ, ht1⟩, ⟨hzΩ, ht2⟩⟩
      have hev : (fun w ↦ if w ∈ Ω₀₀ then F₀₀ w else if w ∈ Ω₁₀ then F₁₀ w
          else if w ∈ Ω₀₁ then F₀₁ w else F₁₁ w) =ᶠ[𝓝 z] F₁₀ := by
        filter_upwards [hΩ₁₀_open.mem_nhds hz10] with w hw
        have hn00 : w ∉ Ω₀₀ := fun h ↦ hw.1.2 h.1.2
        simp [hn00, hw]
      exact ((h10.differentiableAt (hΩ₁₀_open.mem_nhds hz10)).congr_of_eventuallyEq
        hev).differentiableWithinAt
    · have hz11 : z ∈ Ω₁₁ := ⟨⟨hzΩ, ht1⟩, ⟨hzΩ, ht2⟩⟩
      have hev : (fun w ↦ if w ∈ Ω₀₀ then F₀₀ w else if w ∈ Ω₁₀ then F₁₀ w
          else if w ∈ Ω₀₁ then F₀₁ w else F₁₁ w) =ᶠ[𝓝 z] F₁₁ := by
        filter_upwards [hΩ₁₁_open.mem_nhds hz11] with w hw
        have hn00 : w ∉ Ω₀₀ := fun h ↦ hw.1.2 h.1.2
        have hn10 : w ∉ Ω₁₀ := fun h ↦ hw.2.2 h.2.2
        have hn01 : w ∉ Ω₀₁ := fun h ↦ hw.1.2 h.1.2
        simp [hn00, hn10, hn01]
      exact ((h11.differentiableAt (hΩ₁₁_open.mem_nhds hz11)).congr_of_eventuallyEq
        hev).differentiableWithinAt
  refine ⟨d, f₁, f₂, h₁, h₂,
    hglue_diff _ _ _ _ (differentiableOn_const 0) (hg₁.mono fun _ h ↦ h.1.1)
      (hg₂.mono fun _ h ↦ h.1.1) hΦ_diff,
    hglue_diff _ _ _ _ (differentiableOn_const 0) (differentiableOn_const 1)
      (differentiableOn_const 0) hs₁_diff,
    hglue_diff _ _ _ _ (differentiableOn_const 0) (differentiableOn_const 0)
      (differentiableOn_const 1) hs₂_diff,
    hglue_diff _ _ _ _ (differentiableOn_const 0) (differentiableOn_const 1)
      (differentiableOn_const 0) hq₁_diff,
    hglue_diff _ _ _ _ (differentiableOn_const 0) (differentiableOn_const 0)
      (differentiableOn_const 1) hq₂_diff,
    ?_, ?_, ?_⟩
  · intro z hzΩ
    by_cases ht1 : analyticOrderAt g₁ z = ⊤ <;> by_cases ht2 : analyticOrderAt g₂ z = ⊤
    · have hz00 : z ∈ Ω₀₀ := ⟨⟨hzΩ, ht1⟩, ⟨hzΩ, ht2⟩⟩
      simp [d, f₁, f₂, hz00]
    · have hz01 : z ∈ Ω₀₁ := ⟨⟨hzΩ, ht1⟩, ⟨hzΩ, ht2⟩⟩
      have hn00 : z ∉ Ω₀₀ := fun h ↦ ht2 h.2.2
      have hn10 : z ∉ Ω₁₀ := fun h ↦ h.1.2 ht1
      simp [d, f₁, f₂, hn00, hn10, hz01]
    · have hz10 : z ∈ Ω₁₀ := ⟨⟨hzΩ, ht1⟩, ⟨hzΩ, ht2⟩⟩
      have hn00 : z ∉ Ω₀₀ := fun h ↦ ht1 h.1.2
      simp [d, f₁, f₂, hn00, hz10]
    · have hz11 : z ∈ Ω₁₁ := ⟨⟨hzΩ, ht1⟩, ⟨hzΩ, ht2⟩⟩
      have hn00 : z ∉ Ω₀₀ := fun h ↦ ht1 h.1.2
      have hn10 : z ∉ Ω₁₀ := fun h ↦ ht2 h.2.2
      have hn01 : z ∉ Ω₀₁ := fun h ↦ ht1 h.1.2
      have h1 : 1 - s₂ z * q₂ z = s₁ z * q₁ z := hs₁_mul z hz11
      have hbez : s₁ z * q₁ z + s₂ z * q₂ z = 1 := by linear_combination -h1
      simp only [d, f₁, f₂, hn00, hn10, hn01, ↓reduceIte, hq₁_mul z hz11, hq₂_mul z hz11]
      calc
        Φ z = (s₁ z * q₁ z + s₂ z * q₂ z) * Φ z := by rw [hbez, one_mul]
        _ = s₁ z * (q₁ z * Φ z) + s₂ z * (q₂ z * Φ z) := by ring
  · intro z hzΩ
    by_cases ht1 : analyticOrderAt g₁ z = ⊤ <;> by_cases ht2 : analyticOrderAt g₂ z = ⊤
    · have hz00 : z ∈ Ω₀₀ := ⟨⟨hzΩ, ht1⟩, ⟨hzΩ, ht2⟩⟩
      simp [d, h₁, hz00, hg₁_zero_of_top z hzΩ ht1]
    · have hz01 : z ∈ Ω₀₁ := ⟨⟨hzΩ, ht1⟩, ⟨hzΩ, ht2⟩⟩
      have hn00 : z ∉ Ω₀₀ := fun h ↦ ht2 h.2.2
      have hn10 : z ∉ Ω₁₀ := fun h ↦ h.1.2 ht1
      simp [d, h₁, hn00, hn10, hz01, hg₁_zero_of_top z hzΩ ht1]
    · have hz10 : z ∈ Ω₁₀ := ⟨⟨hzΩ, ht1⟩, ⟨hzΩ, ht2⟩⟩
      have hn00 : z ∉ Ω₀₀ := fun h ↦ ht1 h.1.2
      simp [d, h₁, hn00, hz10]
    · have hz11 : z ∈ Ω₁₁ := ⟨⟨hzΩ, ht1⟩, ⟨hzΩ, ht2⟩⟩
      have hn00 : z ∉ Ω₀₀ := fun h ↦ ht1 h.1.2
      have hn10 : z ∉ Ω₁₀ := fun h ↦ ht2 h.2.2
      have hn01 : z ∉ Ω₀₁ := fun h ↦ ht1 h.1.2
      simp [d, h₁, hn00, hn10, hn01, hq₁_mul z hz11]
  · intro z hzΩ
    by_cases ht1 : analyticOrderAt g₁ z = ⊤ <;> by_cases ht2 : analyticOrderAt g₂ z = ⊤
    · have hz00 : z ∈ Ω₀₀ := ⟨⟨hzΩ, ht1⟩, ⟨hzΩ, ht2⟩⟩
      simp [d, h₂, hz00, hg₂_zero_of_top z hzΩ ht2]
    · have hz01 : z ∈ Ω₀₁ := ⟨⟨hzΩ, ht1⟩, ⟨hzΩ, ht2⟩⟩
      have hn00 : z ∉ Ω₀₀ := fun h ↦ ht2 h.2.2
      have hn10 : z ∉ Ω₁₀ := fun h ↦ h.1.2 ht1
      simp [d, h₂, hn00, hn10, hz01]
    · have hz10 : z ∈ Ω₁₀ := ⟨⟨hzΩ, ht1⟩, ⟨hzΩ, ht2⟩⟩
      have hn00 : z ∉ Ω₀₀ := fun h ↦ ht1 h.1.2
      simp [d, h₂, hn00, hz10, hg₂_zero_of_top z hzΩ ht2]
    · have hz11 : z ∈ Ω₁₁ := ⟨⟨hzΩ, ht1⟩, ⟨hzΩ, ht2⟩⟩
      have hn00 : z ∉ Ω₀₀ := fun h ↦ ht1 h.1.2
      have hn10 : z ∉ Ω₁₀ := fun h ↦ ht2 h.2.2
      have hn01 : z ∉ Ω₀₁ := fun h ↦ ht1 h.1.2
      simp [d, h₂, hn00, hn10, hn01, hq₂_mul z hz11]

/-- **Rudin RCA 15.15 (Concrete form)**:
For ANY open set `Ω ⊆ ℂ` (including disconnected `Ω`, `Ω = ∅`, `k = 0`, and identically zero
generators) and any `g : Fin k → ℂ → ℂ` holomorphic on `Ω`, there exist `d ∈ H(Ω)` and
`f, h : Fin k → ℂ → ℂ` in `H(Ω)` such that `d(z) = ∑_i f_i(z) g_i(z)` and `g_i(z) = h_i(z) d(z)`
for all `z ∈ Ω` and all `i`. -/
theorem theorem15_15_concrete {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    ∀ {k : ℕ} (g : Fin k → ℂ → ℂ), (∀ i, DifferentiableOn ℂ (g i) Ω) →
      ∃ (d : ℂ → ℂ) (f h : Fin k → ℂ → ℂ),
        DifferentiableOn ℂ d Ω ∧
        (∀ i, DifferentiableOn ℂ (f i) Ω) ∧
        (∀ i, DifferentiableOn ℂ (h i) Ω) ∧
        (∀ z ∈ Ω, d z = ∑ i, f i z * g i z) ∧
        (∀ i, ∀ z ∈ Ω, g i z = h i z * d z)
  | 0, _, _ =>
    ⟨0, Fin.elim0, Fin.elim0, differentiableOn_const 0,
      fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i,
      fun _ _ ↦ by simp, fun i ↦ Fin.elim0 i⟩
  | k + 1, g, hg => by
    obtain ⟨d₀, f₀, h₀, hd₀, hf₀, hh₀, hsum₀, hdiv₀⟩ :=
      theorem15_15_concrete hΩ (fun j : Fin k ↦ g j.castSucc) (fun j ↦ hg j.castSucc)
    obtain ⟨d, u₁, u₂, v₁, v₂, hd, hu₁, hu₂, hv₁, hv₂, hbez, hd₀_div, hlast_div⟩ :=
      exists_bezout_pair_holomorphic hΩ hd₀ (hg (Fin.last k))
    let f : Fin (k + 1) → ℂ → ℂ :=
      Fin.snoc (fun j w ↦ u₁ w * f₀ j w) u₂
    let h : Fin (k + 1) → ℂ → ℂ :=
      Fin.snoc (fun j w ↦ h₀ j w * v₁ w) v₂
    refine ⟨d, f, h, hd, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simp only [f, Fin.snoc_last]
        exact hu₂
      · intro j
        simp only [f, Fin.snoc_castSucc]
        exact hu₁.mul (hf₀ j)
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simp only [h, Fin.snoc_last]
        exact hv₂
      · intro j
        simp only [h, Fin.snoc_castSucc]
        exact (hh₀ j).mul hv₁
    · intro z hz
      rw [Fin.sum_univ_castSucc]
      simp only [f, Fin.snoc_castSucc, Fin.snoc_last]
      have hmul_sum : (∑ j : Fin k, u₁ z * f₀ j z * g j.castSucc z) = u₁ z * d₀ z := by
        rw [hsum₀ z hz, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ by ring
      rw [hmul_sum, hbez z hz]
    · intro i z hz
      refine Fin.lastCases ?_ ?_ i
      · simpa [h] using hlast_div z hz
      · intro j
        simp only [h, Fin.snoc_castSucc]
        calc
          g j.castSucc z = h₀ j z * d₀ z := hdiv₀ j z hz
          _ = h₀ j z * (v₁ z * d z) := by rw [hd₀_div z hz]
          _ = h₀ j z * v₁ z * d z := by ring

/-- **Rudin RCA 15.15** (Every finitely generated ideal in `H(Ω)` is principal / `IsBezout`):
For every open set `Ω ⊆ ℂ`, every finitely generated ideal `I` of `HolomorphicRing Ω` is principal,
and `HolomorphicRing Ω` is a Bézout ring (`IsBezout (HolomorphicRing Ω)`). -/
theorem theorem15_15 {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    (∀ I : Ideal (HolomorphicRing Ω), I.FG → I.IsPrincipal) ∧
    IsBezout (HolomorphicRing Ω) := by
  have hfg_prin : ∀ I : Ideal (HolomorphicRing Ω), I.FG → I.IsPrincipal := by
    classical
    intro I ⟨S, hS⟩
    let k := S.card
    let e : Fin k ≃ S := S.equivFin.symm
    let G : Fin k → ℂ → ℂ := fun i ↦ (e i).1.2.choose
    have hG : ∀ i, DifferentiableOn ℂ (G i) Ω := fun i ↦ (e i).1.2.choose_spec.1
    obtain ⟨d, f, h, hd, hf, hh, hbez, hdiv⟩ := theorem15_15_concrete hΩ G hG
    let dR : HolomorphicRing Ω := ⟨fun z ↦ d z.1, d, hd, fun _ ↦ rfl⟩
    let fR : Fin k → HolomorphicRing Ω := fun i ↦ ⟨fun z ↦ f i z.1, f i, hf i, fun _ ↦ rfl⟩
    let hR : Fin k → HolomorphicRing Ω := fun i ↦ ⟨fun z ↦ h i z.1, h i, hh i, fun _ ↦ rfl⟩
    have hd_mem : dR ∈ I := by
      have hd_eq : dR = ∑ i : Fin k, fR i * (e i).1 := by
        apply Subtype.ext
        funext z
        have hsum_val : (∑ i : Fin k, fR i * (e i).1).1 z =
            ∑ i : Fin k, f i z.1 * G i z.1 := by
          have hcoe : (∑ i : Fin k, fR i * (e i).1).1 =
              ∑ i : Fin k, (fR i * (e i).1).1 := by
            let φ : HolomorphicRing Ω →+ (Ω → ℂ) :=
              { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
            exact map_sum φ (fun i ↦ fR i * (e i).1) Finset.univ
          rw [hcoe, Finset.sum_apply]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          change f i z.1 * (e i).1.1 z = f i z.1 * G i z.1
          rw [(e i).1.2.choose_spec.2 z]
        rw [hsum_val]
        exact hbez z.1 z.2
      rw [← hS, hd_eq]
      refine Ideal.sum_mem _ fun i _ ↦ ?_
      exact Ideal.mul_mem_left _ (fR i) (Ideal.subset_span (e i).2)
    have hI_le : I ≤ Ideal.span {dR} := by
      rw [← hS, Ideal.span_le]
      intro x hx
      let i : Fin k := e.symm ⟨x, hx⟩
      have hxi : (e i).1 = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
      have hx_eq : x = hR i * dR := by
        rw [← hxi]
        apply Subtype.ext
        funext z
        change (e i).1.1 z = h i z.1 * d z.1
        rw [(e i).1.2.choose_spec.2 z]
        exact hdiv i z.1 z.2
      rw [SetLike.mem_coe, Ideal.mem_span_singleton]
      exact ⟨hR i, by rw [hx_eq, mul_comm]⟩
    have hspan_le : Ideal.span {dR} ≤ I :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hd_mem)
    exact ⟨⟨dR, le_antisymm hI_le hspan_le⟩⟩
  refine ⟨hfg_prin, ?_⟩
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro x y
  exact hfg_prin (Ideal.span {x, y}) ⟨{x, y}, by simp⟩

/-! ## Axiom Verification (`#print axioms`) -/

#print axioms HasInfiniteProductOneAdd
#print axioms InfiniteProductOneAddConverges
#print axioms theorem15_2
#print axioms theorem15_3
#print axioms theorem15_4
#print axioms theorem15_5
#print axioms theorem15_6
#print axioms theorem15_7
#print axioms theorem15_8
#print axioms theorem15_9
#print axioms accPt_principal_iff_mem_closure_diff
#print axioms compl_mem_codiscreteWithin_of_no_limit_pt
#print axioms eventually_notMem_compact_of_no_limit_pt
#print axioms discrete_multiplicity_enumeration
#print axioms theorem15_10_nonzero_at_origin
#print axioms theorem15_10
#print axioms HolomorphicOnSphere
#print axioms sphereZeroOrder
#print axioms sphereZeroOrderNat
#print axioms sphereZeroOrder_infty
#print axioms sphereZeroOrder_coe
#print axioms finite_linear_product
#print axioms exists_holomorphic_prescribed_zeros_plane_zero_notMem
#print axioms exists_holomorphic_prescribed_zeros_plane
#print axioms theorem15_11
#print axioms theorem15_1
#print axioms bookMeromorphicWithPoles_toMeromorphicNFOn
#print axioms exists_quotient_of_bookMeromorphicOn
#print axioms theorem15_12
#print axioms theorem15_13
#print axioms HolomorphicRing
#print axioms instCoeFunHolomorphicRing
#print axioms instCommRingHolomorphicRing
#print axioms HolomorphicRing.val_zero
#print axioms HolomorphicRing.val_one
#print axioms HolomorphicRing.val_add
#print axioms HolomorphicRing.val_mul
#print axioms holomorphicZeroMultiplicity
#print axioms theorem15_14
#print axioms exists_holomorphic_quotient_of_order_le
#print axioms isOpen_analyticOrderAt_eq_top_and_ne_top
#print axioms exists_bezout_pair_holomorphic
#print axioms theorem15_15_concrete
#print axioms theorem15_15


end Chapter15PartA

section Chapter15PartB
set_option autoImplicit false
open Filter Finset MeasureTheory Set Metric Complex
open scoped Topology ENNReal NNReal



/-!
## Basic Circle-Average and Periodic Interval-Integral Bridges
-/

/-- `circleMap 0 r θ` is `(r : ℂ) * Complex.exp (θ * Complex.I)`. -/
lemma circleMap_zero_eq (r θ : ℝ) :
    circleMap (0 : ℂ) r θ = (r : ℂ) * Complex.exp (θ * Complex.I) := by
  simp [circleMap]

/-- `circleMap 0 1 θ` is `Complex.exp (θ * Complex.I)`. -/
lemma circleMap_zero_one_eq (θ : ℝ) :
    circleMap (0 : ℂ) 1 θ = Complex.exp (θ * Complex.I) := by
  simp [circleMap]

/-- Periodicity of `θ ↦ g ((r : ℂ) * Complex.exp (θ * Complex.I))` with period `2 * π`. -/
lemma periodic_polar_comp {E : Type*} (g : ℂ → E) (r : ℝ) :
    Function.Periodic (fun θ : ℝ ↦ g ((r : ℂ) * Complex.exp (θ * Complex.I))) (2 * Real.pi) := by
  intro θ
  have h := periodic_circleMap (0 : ℂ) r θ
  simpa only [circleMap_zero_eq] using congrArg g h

/-- `CircleIntegrable g 0 r` is equivalent to `IntervalIntegrable` on `0..(2 * π)`. -/
lemma circleIntegrable_iff_intervalIntegrable_zero_two_pi {E : Type*} [NormedAddCommGroup E]
    (g : ℂ → E) (r : ℝ) :
    CircleIntegrable g 0 r ↔
      IntervalIntegrable (fun θ : ℝ ↦ g ((r : ℂ) * Complex.exp (θ * Complex.I)))
        MeasureTheory.volume 0 (2 * Real.pi) := by
  simp only [CircleIntegrable, circleMap_zero_eq]

/-- `CircleIntegrable g 0 r` is equivalent to `IntervalIntegrable` on `(-π)..π`. -/
lemma circleIntegrable_iff_intervalIntegrable_neg_pi_pi {E : Type*} [NormedAddCommGroup E]
    (g : ℂ → E) (r : ℝ) :
    CircleIntegrable g 0 r ↔
      IntervalIntegrable (fun θ : ℝ ↦ g ((r : ℂ) * Complex.exp (θ * Complex.I)))
        MeasureTheory.volume (-Real.pi) Real.pi := by
  rw [circleIntegrable_iff_intervalIntegrable_zero_two_pi]
  have hper := periodic_polar_comp g r
  have hiff := hper.intervalIntegrable_iff (t₁ := 0) (t₂ := -Real.pi)
  have h1 : (0 : ℝ) + 2 * Real.pi = 2 * Real.pi := zero_add _
  have h2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rwa [h1, h2] at hiff

/-- `Real.circleAverage g 0 r` equals `(2 * π)⁻¹ * ∫ θ in 0..(2 * π), g (r * exp(iθ))`. -/
lemma circleAverage_zero_eq_zero_two_pi (g : ℂ → ℝ) (r : ℝ) :
    Real.circleAverage g 0 r =
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        g ((r : ℂ) * Complex.exp (θ * Complex.I)) := by
  simp [Real.circleAverage_def, circleMap_zero_eq, smul_eq_mul]

/-- `Real.circleAverage g 0 r` equals `(2 * π)⁻¹ * ∫ θ in (-π)..π, g (r * exp(iθ))`. -/
lemma circleAverage_zero_eq_neg_pi_pi (g : ℂ → ℝ) (r : ℝ) :
    Real.circleAverage g 0 r =
      (2 * Real.pi)⁻¹ * ∫ θ in (-Real.pi)..Real.pi,
        g ((r : ℂ) * Complex.exp (θ * Complex.I)) := by
  rw [circleAverage_zero_eq_zero_two_pi]
  congr 1
  have hper := periodic_polar_comp g r
  have heq := hper.intervalIntegral_add_eq 0 (-Real.pi)
  have h1 : (0 : ℝ) + 2 * Real.pi = 2 * Real.pi := zero_add _
  have h2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rwa [h1, h2] at heq

/-!
## 15.17: Lemma on `(2π)⁻¹ ∫_{-π}^π log |1 - e^{iθ}| dθ = 0`
-/

/-- **Lemma 15.17** (Rudin, *Real and Complex Analysis*, 3rd ed., p. 307):
`log ‖1 - z‖` is circle-integrable on the unit circle with circle average `0`, and equivalently
`θ ↦ log ‖1 - exp(iθ)‖` is Lebesgue interval-integrable on both `[0, 2π]` and `[-π, π]` with
normalized integral `0`. -/
theorem theorem15_17 :
    (CircleIntegrable (fun z : ℂ ↦ Real.log ‖1 - z‖) 0 1 ∧
      Real.circleAverage (fun z : ℂ ↦ Real.log ‖1 - z‖) 0 1 = 0) ∧
    (IntervalIntegrable (fun θ : ℝ ↦ Real.log ‖1 - Complex.exp (θ * Complex.I)‖)
        MeasureTheory.volume 0 (2 * Real.pi) ∧
      (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log ‖1 - Complex.exp (θ * Complex.I)‖) = 0) ∧
    (IntervalIntegrable (fun θ : ℝ ↦ Real.log ‖1 - Complex.exp (θ * Complex.I)‖)
        MeasureTheory.volume (-Real.pi) Real.pi ∧
      (2 * Real.pi)⁻¹ *
        (∫ θ in (-Real.pi)..Real.pi, Real.log ‖1 - Complex.exp (θ * Complex.I)‖) = 0) := by
  have hfun : (fun z : ℂ ↦ Real.log ‖1 - z‖) = (fun z : ℂ ↦ Real.log ‖z - 1‖) := by
    ext z
    rw [norm_sub_rev]
  have hcint : CircleIntegrable (fun z : ℂ ↦ Real.log ‖1 - z‖) 0 1 := by
    rw [hfun]
    exact MeromorphicOn.circleIntegrable_log_norm (f := fun z : ℂ ↦ z - 1) (by fun_prop)
  have hcavg : Real.circleAverage (fun z : ℂ ↦ Real.log ‖1 - z‖) 0 1 = 0 := by
    rw [hfun]
    exact _root_.circleAverage_log_norm_sub_const₁ (a := (1 : ℂ)) (by simp)
  have hint_0_2pi : IntervalIntegrable (fun θ : ℝ ↦ Real.log ‖1 - Complex.exp (θ * Complex.I)‖)
      MeasureTheory.volume 0 (2 * Real.pi) := by
    simpa [circleIntegrable_iff_intervalIntegrable_zero_two_pi] using hcint
  have hint_neg_pi_pi : IntervalIntegrable (fun θ : ℝ ↦ Real.log ‖1 - Complex.exp (θ * Complex.I)‖)
      MeasureTheory.volume (-Real.pi) Real.pi := by
    simpa [circleIntegrable_iff_intervalIntegrable_neg_pi_pi] using hcint
  have havg_0_2pi :
      (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log ‖1 - Complex.exp (θ * Complex.I)‖) = 0 := by
    have h := circleAverage_zero_eq_zero_two_pi (fun z : ℂ ↦ Real.log ‖1 - z‖) 1
    simpa using h.symm.trans hcavg
  have havg_neg_pi_pi :
      (2 * Real.pi)⁻¹ *
        (∫ θ in (-Real.pi)..Real.pi, Real.log ‖1 - Complex.exp (θ * Complex.I)‖) = 0 := by
    have h := circleAverage_zero_eq_neg_pi_pi (fun z : ℂ ↦ Real.log ‖1 - z‖) 1
    simpa using h.symm.trans hcavg
  exact ⟨⟨hcint, hcavg⟩, ⟨hint_0_2pi, havg_0_2pi⟩, ⟨hint_neg_pi_pi, havg_neg_pi_pi⟩⟩

/-!
## Extended-Real Log Modulus (`log 0 = -∞`) and Jensen's Formula (15.18)
-/

/-- Extended-real logarithm of the complex modulus, following Rudin's convention `log 0 = -∞`
(`⊥ : EReal`) in 15.18–15.19 (`SCOPING-G.md` Caution 4). -/
def eLogNorm (w : ℂ) : EReal :=
  if w = 0 then ⊥ else (Real.log ‖w‖ : EReal)

@[simp] lemma eLogNorm_zero : eLogNorm 0 = ⊥ := by simp [eLogNorm]

lemma eLogNorm_of_ne_zero {w : ℂ} (hw : w ≠ 0) :
    eLogNorm w = (Real.log ‖w‖ : EReal) := by
  simp [eLogNorm, hw]

/-- For `r > 0` and any `w : ℂ`, `{θ ∈ [-π, π] | r * exp(iθ) = w}` has at most two points
(`{-π, π}` or a singleton in `(-π, π)`), hence is finite. -/
private lemma finite_Icc_polar_eq {r : ℝ} (hr : 0 < r) (w : ℂ) :
    {θ ∈ Set.Icc (-Real.pi) Real.pi | (r : ℂ) * Complex.exp (θ * Complex.I) = w}.Finite := by
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  let S₀ : Set ℝ := {θ ∈ Set.Ico (-Real.pi) Real.pi | (r : ℂ) * Complex.exp (θ * Complex.I) = w}
  have hsub : {θ ∈ Set.Icc (-Real.pi) Real.pi | (r : ℂ) * Complex.exp (θ * Complex.I) = w} ⊆
      S₀ ∪ {Real.pi} := by
    rintro θ ⟨⟨hlo, hhi⟩, heq⟩
    rcases eq_or_lt_of_le hhi with rfl | hlt
    · exact Or.inr (mem_singleton _)
    · exact Or.inl ⟨⟨hlo, hlt⟩, heq⟩
  refine (Set.Subsingleton.finite ?_ |>.union (finite_singleton Real.pi)).subset hsub
  rintro θ₁ ⟨hθ₁, heq₁⟩ θ₂ ⟨hθ₂, heq₂⟩
  have hexp : Complex.exp (θ₁ * Complex.I) = Complex.exp (θ₂ * Complex.I) :=
    mul_left_cancel₀ hr_ne (heq₁.trans heq₂.symm)
  rw [Complex.exp_eq_exp_iff_exists_int] at hexp
  obtain ⟨k, hk⟩ := hexp
  have him : θ₁ = θ₂ + (k : ℝ) * (2 * Real.pi) := by
    have h2 : ((θ₁ : ℂ) - ((θ₂ + (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ)) * Complex.I = 0 := by
      push_cast
      linear_combination hk
    have h3 := (mul_eq_zero.mp h2).resolve_right Complex.I_ne_zero
    exact sub_eq_zero.mp (Complex.ofReal_injective (by simpa using h3))
  have hk0 : k = 0 := by
    by_contra hkne
    rcases lt_or_gt_of_ne hkne with hkneg | hkpos
    · have hkle : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hkneg
      have : θ₁ < -Real.pi := by nlinarith [Real.pi_pos, hθ₂.2]
      linarith [hθ₁.1]
    · have hkge : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hkpos
      have : Real.pi ≤ θ₁ := by nlinarith [Real.pi_pos, hθ₂.1]
      linarith [hθ₁.2]
  simp [him, hk0]

/-- Nonzero holomorphic functions on `Metric.ball 0 R` have `analyticOrderAt f z ≠ ⊤` everywhere
on `Metric.ball 0 R`. -/
lemma analyticOrderAt_ne_top_on_ball {R : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    {z₀ : ℂ} (hz₀ : z₀ ∈ Metric.ball (0 : ℂ) R) (hfz₀ : f z₀ ≠ 0)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    analyticOrderAt f z ≠ ⊤ := by
  have hana : AnalyticOnNhd ℂ f (Metric.ball 0 R) := hf.analyticOnNhd Metric.isOpen_ball
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hzero := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℂ) R).isPreconnected hz htop
  exact hfz₀ (hzero hz₀)

/-- Local factorization removing a zero at `0` on `Metric.ball 0 R` (`R > 0`), analogous to
`Chapter15.entire_remove_zero_at_origin`. -/
theorem disc_remove_zero_at_origin {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hnonzero : ∃ z₀ ∈ Metric.ball (0 : ℂ) R, f z₀ ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball 0 R) ∧ h 0 ≠ 0 ∧
      (∀ z ∈ Metric.ball (0 : ℂ) R, f z = z ^ analyticOrderNatAt f 0 * h z) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) R \ {0}, analyticOrderNatAt h z = analyticOrderNatAt f z) := by
  obtain ⟨z₀, hz₀, hfz₀⟩ := hnonzero
  have h0_mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self hR
  have hana : AnalyticOnNhd ℂ f (Metric.ball 0 R) := hf.analyticOnNhd Metric.isOpen_ball
  have hne_top : analyticOrderAt f 0 ≠ ⊤ := analyticOrderAt_ne_top_on_ball hf hz₀ hfz₀ h0_mem
  obtain ⟨g, hg_ana, hg0, hfg⟩ := (hana 0 h0_mem).analyticOrderAt_ne_top.mp hne_top
  let k := analyticOrderNatAt f 0
  let h : ℂ → ℂ := fun z ↦ if z = 0 then g 0 else f z / z ^ k
  have h_ev : h =ᶠ[𝓝 (0 : ℂ)] g := by
    filter_upwards [ hfg ] with z hz
    dsimp [h, k]
    by_cases hz0 : z = 0
    · simp [hz0]
    · simp only [hz0, ↓reduceIte]
      rw [hz, smul_eq_mul, sub_zero, mul_div_cancel_left₀ _ (pow_ne_zero _ hz0)]
  have hh_diff : DifferentiableOn ℂ h (Metric.ball 0 R) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      exact (hg_ana.differentiableAt.congr_of_eventuallyEq h_ev).differentiableWithinAt
    · have hev_z : h =ᶠ[𝓝 z] fun w ↦ f w / w ^ k := by
        filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
        simp [h, hw]
      have hd : DifferentiableAt ℂ (fun w ↦ f w / w ^ k) z :=
        (hf.differentiableAt (Metric.isOpen_ball.mem_nhds hz)).div
          (differentiableAt_id.pow k) (pow_ne_zero k hz0)
      exact (hd.congr_of_eventuallyEq hev_z).differentiableWithinAt
  refine ⟨h, hh_diff, by simpa [h] using hg0, ?_, ?_⟩
  · intro z hz
    dsimp [h, k]
    by_cases hz0 : z = 0
    · subst hz0
      have hself := hfg.self_of_nhds
      by_cases hk0 : analyticOrderNatAt f 0 = 0
      · simp only [sub_self, hk0, pow_zero, one_smul] at hself
        simp [hk0, hself]
      · simp only [sub_self, zero_pow hk0, zero_smul] at hself
        simp [zero_pow hk0, hself]
    · simp [hz0, mul_div_cancel₀ _ (pow_ne_zero _ hz0)]
  · intro z ⟨hz, hz0⟩
    have hana_h : AnalyticOnNhd ℂ h (Metric.ball 0 R) := hh_diff.analyticOnNhd Metric.isOpen_ball
    have hzk_ana : AnalyticAt ℂ (fun w : ℂ ↦ w ^ k) z := analyticAt_id.pow k
    have heq_nhds : f =ᶠ[𝓝 z] fun w ↦ w ^ k * h w := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz, isOpen_ne.mem_nhds hz0] with w hw hw0
      simp [h, hw0, k, mul_div_cancel₀ _ (pow_ne_zero _ hw0)]
    have hord_eq : analyticOrderAt f z = analyticOrderAt (fun w ↦ w ^ k * h w) z :=
      analyticOrderAt_congr heq_nhds
    have hord_mul : analyticOrderAt (fun w ↦ w ^ k * h w) z =
        analyticOrderAt (fun w : ℂ ↦ w ^ k) z + analyticOrderAt h z :=
      analyticOrderAt_mul hzk_ana (hana_h z hz)
    have hord_zk : analyticOrderAt (fun w : ℂ ↦ w ^ k) z = 0 :=
      hzk_ana.analyticOrderAt_eq_zero.mpr (pow_ne_zero k hz0)
    rw [hord_mul, hord_zk, zero_add] at hord_eq
    simp [analyticOrderNatAt, hord_eq]

/-- **Theorem 15.18 (Jensen's Formula)** (Rudin, *Real and Complex Analysis*, 3rd ed., pp. 307–308):
Let `0 < r < R` and `f ∈ H(D(0, R))` with `f(0) ≠ 0`.
1. `z ↦ log ‖f z‖` is circle-integrable on `C(0, r)`, `θ ↦ log ‖f(r e^{iθ})‖` is Lebesgue
   interval-integrable on `[0, 2π]` and `[-π, π]`, `{θ ∈ [-π, π] | f(r e^{iθ}) = 0}` is finite,
   and `eLogNorm (f (r e^{iθ}))` (with `log 0 = -∞`) agrees a.e. with `(log ‖f(r e^{iθ})‖ : EReal)`.
2. There exists a finite multiplicity list `(N, a)` of ALL zeros of `f` in the **closed** disc
   `closedBall 0 r` (boundary zeros `‖a i‖ = r` included, whose factors `r / ‖a i‖` equal `1`),
   and for EVERY such multiplicity list `(N, a)`:
   `‖f 0‖ * ∏_{i=1}^N (r / ‖a_i‖) = exp ((2π)⁻¹ ∫_{-π}^π log ‖f(r e^{iθ})‖ dθ)`
   `= exp (circleAverage (log ‖f ·‖) 0 r)`. -/
theorem theorem15_18 {r R : ℝ} (hr : 0 < r) (hrR : r < R) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) (hf0 : f 0 ≠ 0) :
    (CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 r ∧
      IntervalIntegrable (fun θ : ℝ ↦ Real.log ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖)
        MeasureTheory.volume 0 (2 * Real.pi) ∧
      IntervalIntegrable (fun θ : ℝ ↦ Real.log ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖)
        MeasureTheory.volume (-Real.pi) Real.pi ∧
      {θ ∈ Set.Icc (-Real.pi) Real.pi | f ((r : ℂ) * Complex.exp (θ * Complex.I)) = 0}.Finite ∧
      (fun θ : ℝ ↦ eLogNorm (f ((r : ℂ) * Complex.exp (θ * Complex.I)))) =ᵐ[
          MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)]
        (fun θ : ℝ ↦ (Real.log ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ : EReal))) ∧
    (∃ (N : ℕ) (a : Fin N → ℂ),
      (∀ i, a i ∈ Metric.closedBall (0 : ℂ) r ∧ a i ≠ 0) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) r,
        (Finset.univ.filter (fun i ↦ a i = z)).card = analyticOrderNatAt f z) ∧
    (∀ (N : ℕ) (a : Fin N → ℂ),
      (∀ i, a i ∈ Metric.closedBall (0 : ℂ) r ∧ a i ≠ 0) →
      (∀ z ∈ Metric.closedBall (0 : ℂ) r,
        (Finset.univ.filter (fun i ↦ a i = z)).card = analyticOrderNatAt f z) →
      ‖f 0‖ * (∏ i : Fin N, (r / ‖a i‖)) =
        Real.exp ((2 * Real.pi)⁻¹ *
          ∫ θ in (-Real.pi)..Real.pi, Real.log ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖) ∧
      ‖f 0‖ * (∏ i : Fin N, (r / ‖a i‖)) =
        Real.exp (Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 r)) := by
  have hR_pos : 0 < R := lt_trans hr hrR
  have h0_mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self hR_pos
  have hana : AnalyticOnNhd ℂ f (Metric.ball 0 R) := hf.analyticOnNhd Metric.isOpen_ball
  have hr_abs : |r| = r := abs_of_pos hr
  have hcl_sub : Metric.closedBall (0 : ℂ) |r| ⊆ Metric.ball (0 : ℂ) R := by
    rw [hr_abs]
    exact Metric.closedBall_subset_ball hrR
  have hana_cl : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) |r|) := hana.mono hcl_sub
  -- Integrability
  have hcint : CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 r :=
    (hana_cl.mono Metric.sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hint_0_2pi :
      IntervalIntegrable (fun θ : ℝ ↦ Real.log ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖)
        MeasureTheory.volume 0 (2 * Real.pi) :=
    (circleIntegrable_iff_intervalIntegrable_zero_two_pi _ r).mp hcint
  have hint_neg_pi_pi :
      IntervalIntegrable (fun θ : ℝ ↦ Real.log ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖)
        MeasureTheory.volume (-Real.pi) Real.pi :=
    (circleIntegrable_iff_intervalIntegrable_neg_pi_pi _ r).mp hcint
  -- Zero set in `closedBall 0 r` is finite
  let D := MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) |r|)
  have hD_fin : D.support.Finite := D.finiteSupport (isCompact_closedBall 0 |r|)
  have hord_pos_iff : ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      0 < analyticOrderNatAt f z ↔ f z = 0 := by
    intro z hz
    have hz_ball : z ∈ Metric.ball (0 : ℂ) R := hcl_sub (by rwa [hr_abs])
    have hne_top : analyticOrderAt f z ≠ ⊤ :=
      analyticOrderAt_ne_top_on_ball hf h0_mem hf0 hz_ball
    constructor
    · intro hpos
      have hne0 : analyticOrderAt f z ≠ 0 := by
        intro h0
        simp [analyticOrderNatAt, h0] at hpos
      exact (hana z hz_ball).analyticOrderAt_ne_zero.mp hne0
    · intro hfz
      have hne0 : analyticOrderAt f z ≠ 0 :=
        (hana z hz_ball).analyticOrderAt_ne_zero.mpr hfz
      unfold analyticOrderNatAt
      exact Nat.pos_of_ne_zero (ENat.toNat_eq_zero.not.mpr (not_or.mpr ⟨hne0, hne_top⟩))
  have hzeros_sub_D : {z ∈ Metric.closedBall (0 : ℂ) r | f z = 0} ⊆ D.support := by
    rintro z ⟨hz, hfz⟩
    have hz_abs : z ∈ Metric.closedBall (0 : ℂ) |r| := by rwa [hr_abs]
    rw [Function.mem_support]
    have hD_val : D z = (analyticOrderNatAt f z : ℤ) := by
      rw [show D z = (ENat.map Nat.cast (analyticOrderAt f z)).untop₀ from
        MeromorphicOn.AnalyticOnNhd.divisor_apply hana_cl hz_abs]
      unfold analyticOrderNatAt
      cases analyticOrderAt f z <;> rfl
    rw [hD_val]
    exact Int.natCast_ne_zero.mpr ((hord_pos_iff z hz).mpr hfz).ne'
  have hzeros_fin : {z ∈ Metric.closedBall (0 : ℂ) r | f z = 0}.Finite :=
    hD_fin.subset hzeros_sub_D
  -- Finiteness of `{θ ∈ [-π, π] | f(r e^{iθ}) = 0}`
  have hθ_zeros_fin :
      {θ ∈ Set.Icc (-Real.pi) Real.pi | f ((r : ℂ) * Complex.exp (θ * Complex.I)) = 0}.Finite := by
    let Z := {z ∈ Metric.closedBall (0 : ℂ) r | f z = 0}
    have hsub : {θ ∈ Set.Icc (-Real.pi) Real.pi | f ((r : ℂ) * Complex.exp (θ * Complex.I)) = 0} ⊆
        ⋃ z ∈ Z, {θ ∈ Set.Icc (-Real.pi) Real.pi | (r : ℂ) * Complex.exp (θ * Complex.I) = z} := by
      rintro θ ⟨hθIcc, hfθ⟩
      have hmem_cl : (r : ℂ) * Complex.exp (θ * Complex.I) ∈ Metric.closedBall (0 : ℂ) r := by
        rw [ ← circleMap_zero_eq ]
        exact Metric.sphere_subset_closedBall (circleMap_mem_sphere 0 hr.le θ)
      exact mem_biUnion ⟨hmem_cl, hfθ⟩ ⟨hθIcc, rfl⟩
    exact (hzeros_fin.biUnion fun z _ ↦ finite_Icc_polar_eq hr z).subset hsub
  have hae_eLog :
      (fun θ : ℝ ↦ eLogNorm (f ((r : ℂ) * Complex.exp (θ * Complex.I)))) =ᵐ[
          MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)]
        (fun θ : ℝ ↦ (Real.log ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ : EReal)) := by
    have hnull : MeasureTheory.volume
        {θ ∈ Set.Icc (-Real.pi) Real.pi | f ((r : ℂ) * Complex.exp (θ * Complex.I)) = 0} = 0 :=
      hθ_zeros_fin.countable.measure_zero _
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with θ hθ_not hθIcc
    have hne : f ((r : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 :=
      fun h0 ↦ hθ_not ⟨hθIcc, h0⟩
    exact eLogNorm_of_ne_zero hne
  -- Construct canonical finite multiplicity list `(N, a)`
  let S : Finset ℂ := hzeros_fin.toFinset
  let L : List ℂ := S.toList.flatMap (fun z ↦ List.replicate (analyticOrderNatAt f z) z)
  have hL_mem : ∀ w ∈ L, w ∈ Metric.closedBall (0 : ℂ) r ∧ w ≠ 0 := by
    intro w hw
    rw [List.mem_flatMap] at hw
    obtain ⟨z, hzS, hw_rep⟩ := hw
    have hzw : w = z := (List.mem_replicate.mp hw_rep).2
    subst hzw
    have hz_mem : w ∈ {z ∈ Metric.closedBall (0 : ℂ) r | f z = 0} := by
      simpa [S] using Finset.mem_toList.mp hzS
    exact ⟨hz_mem.1, fun h0 ↦ hf0 (h0 ▸ hz_mem.2)⟩
  have hL_count : ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      (Finset.univ.filter (fun i : Fin L.length ↦ L[i] = z)).card = analyticOrderNatAt f z := by
    intro z hz
    have hcard_eq_count :
        (Finset.univ.filter (fun i : Fin L.length ↦ L[i] = z)).card = L.count z := by
      classical
      have : L.count z = (List.finRange L.length |>.filter (fun i ↦ decide (L[i] = z))).length := by
        conv_lhs => rw [← List.map_getElem_finRange L]
        rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
        congr 1
      rw [this]
      have hnodup : (List.finRange L.length |>.filter (fun i ↦ decide (L[i] = z))).Nodup :=
        (List.nodup_finRange L.length).filter _
      rw [← List.toFinset_card_of_nodup hnodup]
      congr 1
      ext i
      simp
    rw [hcard_eq_count]
    by_cases hfz : f z = 0
    · have hzS : z ∈ S := hzeros_fin.mem_toFinset.mpr ⟨hz, hfz⟩
      classical
      rw [List.count_flatMap, Function.comp_def]
      have hmap : List.map (fun w ↦ (List.replicate (analyticOrderNatAt f w) w).count z) S.toList =
          List.map (fun w ↦ if w = z then analyticOrderNatAt f z else 0) S.toList := by
        refine List.map_congr_left fun w _ ↦ ?_
        by_cases hwz : w = z
        · subst hwz; simp
        · simp [List.count_replicate, hwz]
      rw [hmap]
      have hsum_nodup : ∀ (l : List ℂ), l.Nodup → z ∈ l →
          (l.map (fun w ↦ if w = z then analyticOrderNatAt f z else 0)).sum =
            analyticOrderNatAt f z := by
        intro l hl hzl
        induction l with
        | nil => cases hzl
        | cons hd tl ih =>
          rw [List.nodup_cons] at hl
          rw [List.mem_cons] at hzl
          simp only [List.map_cons, List.sum_cons]
          rcases hzl with hdz | hztl
          · subst hdz
            simp only [↓reduceIte]
            have h0 : (tl.map (fun w ↦ if w = z then analyticOrderNatAt f z else 0)).sum = 0 := by
              refine List.sum_eq_zero fun x hx ↦ ?_
              rw [List.mem_map] at hx
              obtain ⟨w, hw, rfl⟩ := hx
              have hne : w ≠ z := fun h ↦ hl.1 (h ▸ hw)
              simp [hne]
            omega
          · have hne : hd ≠ z := fun h ↦ hl.1 (h ▸ hztl)
            simp [hne, ih hl.2 hztl]
      exact hsum_nodup S.toList S.nodup_toList (Finset.mem_toList.mpr hzS)
    · have hz_not_S : z ∉ S := by
        simp [S, hfz]
      have h0 : analyticOrderNatAt f z = 0 := by
        by_contra hne
        exact hfz ((hord_pos_iff z hz).mp (Nat.pos_of_ne_zero hne))
      rw [h0]
      apply List.count_eq_zero.mpr
      intro hzL
      rw [List.mem_flatMap] at hzL
      obtain ⟨w, hwS, hzw⟩ := hzL
      have hw_eq : z = w := (List.mem_replicate.mp hzw).2
      exact hz_not_S (hw_eq ▸ Finset.mem_toList.mp hwS)
  -- Jensen formula for any multiplicity list `(N, a)`
  have hjensen_any : ∀ (N : ℕ) (a : Fin N → ℂ),
      (∀ i, a i ∈ Metric.closedBall (0 : ℂ) r ∧ a i ≠ 0) →
      (∀ z ∈ Metric.closedBall (0 : ℂ) r,
        (Finset.univ.filter (fun i ↦ a i = z)).card = analyticOrderNatAt f z) →
      ‖f 0‖ * (∏ i : Fin N, (r / ‖a i‖)) =
        Real.exp ((2 * Real.pi)⁻¹ *
          ∫ θ in (-Real.pi)..Real.pi, Real.log ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖) ∧
      ‖f 0‖ * (∏ i : Fin N, (r / ‖a i‖)) =
        Real.exp (Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 r) := by
    intro N a ha_mem ha_mult
    have hmaps_S : ∀ i ∈ (Finset.univ : Finset (Fin N)), a i ∈ S := by
      intro i _
      have hi_cl : a i ∈ Metric.closedBall (0 : ℂ) r := (ha_mem i).1
      have hcard_pos : 0 < (Finset.univ.filter (fun j : Fin N ↦ a j = a i)).card :=
        Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩
      rw [ha_mult (a i) hi_cl] at hcard_pos
      exact hzeros_fin.mem_toFinset.mpr ⟨hi_cl, (hord_pos_iff (a i) hi_cl).mp hcard_pos⟩
    have hprod_eq : (∏ i : Fin N, (r / ‖a i‖)) =
        ∏ z ∈ S, (r / ‖z‖) ^ analyticOrderNatAt f z := by
      rw [← Finset.prod_fiberwise_of_maps_to hmaps_S (fun i ↦ r / ‖a i‖)]
      refine Finset.prod_congr rfl fun z hzS ↦ ?_
      have hz_cl : z ∈ Metric.closedBall (0 : ℂ) r := (hzeros_fin.mem_toFinset.mp hzS).1
      have hcongr : (∏ i ∈ Finset.univ.filter (fun i : Fin N ↦ a i = z), (r / ‖a i‖)) =
          ∏ _i ∈ Finset.univ.filter (fun i : Fin N ↦ a i = z), (r / ‖z‖) := by
        refine Finset.prod_congr rfl fun i hi ↦ ?_
        rw [(Finset.mem_filter.mp hi).2]
      rw [hcongr, Finset.prod_const, ha_mult z hz_cl]
    have hmathlib_jensen := hana_cl.circleAverage_log_norm hr.ne' hf0
    have hD_supp_sub_S : (Function.support fun u ↦ (D u : ℝ) * Real.log (r * ‖(0 : ℂ) - u‖⁻¹)) ⊆
        (S : Set ℂ) := by
      intro u hu
      rw [Function.mem_support] at hu
      have hDu_ne : D u ≠ 0 := by
        intro h0
        simp [h0] at hu
      by_cases hu_cl : u ∈ Metric.closedBall (0 : ℂ) |r|
      · have hu_cl' : u ∈ Metric.closedBall (0 : ℂ) r := by rwa [hr_abs] at hu_cl
        have hD_eq : D u = (analyticOrderNatAt f u : ℤ) := by
          rw [show D u = (ENat.map Nat.cast (analyticOrderAt f u)).untop₀ from
            MeromorphicOn.AnalyticOnNhd.divisor_apply hana_cl hu_cl]
          unfold analyticOrderNatAt
          cases analyticOrderAt f u <;> rfl
        rw [hD_eq] at hDu_ne
        have hpos : 0 < analyticOrderNatAt f u :=
          Nat.pos_of_ne_zero (Int.natCast_ne_zero.mp hDu_ne)
        exact hzeros_fin.mem_toFinset.mpr ⟨hu_cl', (hord_pos_iff u hu_cl').mp hpos⟩
      · exact (hDu_ne (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem D hu_cl)).elim
    have hfinsum_eq :
        (∑ᶠ u, (D u : ℝ) * Real.log (r * ‖(0 : ℂ) - u‖⁻¹)) =
          ∑ z ∈ S, (analyticOrderNatAt f z : ℝ) * Real.log (r / ‖z‖) := by
      rw [finsum_eq_sum_of_support_subset _ hD_supp_sub_S]
      refine Finset.sum_congr rfl fun z hzS ↦ ?_
      have hz_cl : z ∈ Metric.closedBall (0 : ℂ) |r| := by
        rw [hr_abs]
        exact (hzeros_fin.mem_toFinset.mp hzS).1
      have hD_eq : D z = (analyticOrderNatAt f z : ℤ) := by
        rw [show D z = (ENat.map Nat.cast (analyticOrderAt f z)).untop₀ from
          MeromorphicOn.AnalyticOnNhd.divisor_apply hana_cl hz_cl]
        unfold analyticOrderNatAt
        cases analyticOrderAt f z <;> rfl
      rw [hD_eq, Int.cast_natCast, zero_sub, norm_neg, div_eq_mul_inv]
    have hcavg_eq :
        Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 r =
          Real.log ‖f 0‖ + ∑ z ∈ S, (analyticOrderNatAt f z : ℝ) * Real.log (r / ‖z‖) := by
      rw [hmathlib_jensen, hfinsum_eq, add_comm]
    have hexp_cavg :
        ‖f 0‖ * (∏ i : Fin N, (r / ‖a i‖)) =
          Real.exp (Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 r) := by
      rw [hcavg_eq, Real.exp_add, Real.exp_log (norm_pos_iff.mpr hf0), Real.exp_sum, hprod_eq]
      congr 1
      refine Finset.prod_congr rfl fun z hzS ↦ ?_
      have hfz0 : f z = 0 := (hzeros_fin.mem_toFinset.mp hzS).2
      have hzne0 : z ≠ 0 := fun h0 ↦ hf0 (h0 ▸ hfz0)
      have hpos_ratio : 0 < r / ‖z‖ := div_pos hr (norm_pos_iff.mpr hzne0)
      rw [Real.exp_nat_mul, Real.exp_log hpos_ratio]
    refine ⟨?_, hexp_cavg⟩
    rw [← circleAverage_zero_eq_neg_pi_pi (fun z ↦ Real.log ‖f z‖) r]
    exact hexp_cavg
  exact ⟨⟨hcint, hint_0_2pi, hint_neg_pi_pi, hθ_zeros_fin, hae_eLog⟩,
    ⟨L.length, fun i ↦ L[i], fun i ↦ hL_mem L[i] (List.getElem_mem _), hL_count⟩,
    hjensen_any⟩

/-!
## Reusable Poisson Nontangential & Radial Limit Theorem at Lebesgue Points
-/

/-- Chord estimate `‖1 - exp(α * I)‖ ≤ |α|` on the unit circle. -/
lemma norm_one_sub_exp_mul_I_le (α : ℝ) :
    ‖(1 : ℂ) - Complex.exp ((α : ℂ) * Complex.I)‖ ≤ |α| := by
  have hsq : ‖(1 : ℂ) - Complex.exp ((α : ℂ) * Complex.I)‖ ^ 2 = 2 * (1 - Real.cos α) := by
    have h := RudinRCA.Chapter11.norm_sq_one_sub_polar 1 α
    simp only [Complex.ofReal_one, one_mul, one_pow] at h
    linarith
  have hcos : 1 - Real.cos α = 2 * Real.sin (α / 2) ^ 2 := by
    have h2 : α = 2 * (α / 2) := by ring
    conv_lhs => rw [h2, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (α / 2)]
  have hsin : |Real.sin (α / 2)| ≤ |α| / 2 := by
    simpa only [abs_div, abs_of_pos (zero_lt_two' ℝ)] using (Real.abs_sin_le_abs (x := α / 2))
  have hsin_sq : Real.sin (α / 2) ^ 2 ≤ (|α| / 2) ^ 2 := by
    rw [← sq_abs (Real.sin (α / 2))]
    exact pow_le_pow_left₀ (abs_nonneg _) hsin 2
  have hle_sq : ‖(1 : ℂ) - Complex.exp ((α : ℂ) * Complex.I)‖ ^ 2 ≤ |α| ^ 2 := by
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp hle_sq

/-- Nontangential domination of the Poisson kernel: for `0 ≤ r < 1`, `0 ≤ K`, and
`|α| ≤ K * (1 - r)`, the shifted kernel at `α - t` is bounded by `(1 + K) ^ 2` times the
centered kernel at `-t`. -/
theorem poissonKernel_nontangential_le {r K α : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hK : 0 ≤ K)
    (hα : |α| ≤ K * (1 - r)) (t : ℝ) :
    (1 - r ^ 2) / ‖(1 : ℂ) - (r : ℂ) * Complex.exp (((α - t : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
      (1 + K) ^ 2 *
        ((1 - r ^ 2) / ‖(1 : ℂ) - (r : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)‖ ^ 2) := by
  let u : ℂ := 1 - (r : ℂ) * Complex.exp (((α - t : ℝ) : ℂ) * Complex.I)
  let v : ℂ := 1 - (r : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)
  have hr_le : r ≤ 1 := hr1.le
  have h1mr_pos : 0 < 1 - r := sub_pos.mpr hr1
  have hu_lb : 1 - r ≤ ‖u‖ := by
    have hnorm_rexp : ‖(r : ℂ) * Complex.exp (((α - t : ℝ) : ℂ) * Complex.I)‖ = r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have htri := norm_sub_norm_le (1 : ℂ) ((r : ℂ) * Complex.exp (((α - t : ℝ) : ℂ) * Complex.I))
    simpa only [norm_one, hnorm_rexp] using htri
  have hv_lb : 1 - r ≤ ‖v‖ := by
    have hnorm_rexp : ‖(r : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)‖ = r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have htri := norm_sub_norm_le (1 : ℂ) ((r : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I))
    simpa only [norm_one, hnorm_rexp] using htri
  have hu_pos : 0 < ‖u‖ := lt_of_lt_of_le h1mr_pos hu_lb
  have hv_pos : 0 < ‖v‖ := lt_of_lt_of_le h1mr_pos hv_lb
  have hdiff_eq : v - u =
      (r : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I) *
        (Complex.exp ((α : ℂ) * Complex.I) - 1) := by
    dsimp [u, v]
    have hexp : Complex.exp (((-t : ℝ) : ℂ) * Complex.I) * Complex.exp ((α : ℂ) * Complex.I) =
        Complex.exp (((α - t : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc (1 - (r : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) -
          (1 - (r : ℂ) * Complex.exp (((α - t : ℝ) : ℂ) * Complex.I))
        = (r : ℂ) * (Complex.exp (((α - t : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) := by ring
      _ = (r : ℂ) * (Complex.exp (((-t : ℝ) : ℂ) * Complex.I) *
            Complex.exp ((α : ℂ) * Complex.I) -
            Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) := by rw [hexp]
      _ = (r : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I) *
            (Complex.exp ((α : ℂ) * Complex.I) - 1) := by ring
  have hdiff_le : ‖v - u‖ ≤ K * ‖u‖ := by
    rw [hdiff_eq, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      Complex.norm_exp_ofReal_mul_I, mul_one, norm_sub_rev]
    calc r * ‖(1 : ℂ) - Complex.exp ((α : ℂ) * Complex.I)‖
        ≤ 1 * |α| := mul_le_mul hr_le (norm_one_sub_exp_mul_I_le α) (norm_nonneg _) zero_le_one
      _ = |α| := one_mul _
      _ ≤ K * (1 - r) := hα
      _ ≤ K * ‖u‖ := mul_le_mul_of_nonneg_left hu_lb hK
  have hv_le : ‖v‖ ≤ (1 + K) * ‖u‖ := by
    calc ‖v‖ = ‖u + (v - u)‖ := by rw [add_sub_cancel]
      _ ≤ ‖u‖ + ‖v - u‖ := norm_add_le _ _
      _ ≤ ‖u‖ + K * ‖u‖ := add_le_add_right hdiff_le _
      _ = (1 + K) * ‖u‖ := by ring
  have hv_sq_le : ‖v‖ ^ 2 ≤ (1 + K) ^ 2 * ‖u‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hv_le 2
  have h1mr2_nn : 0 ≤ 1 - r ^ 2 := by nlinarith
  change (1 - r ^ 2) / ‖u‖ ^ 2 ≤ (1 + K) ^ 2 * ((1 - r ^ 2) / ‖v‖ ^ 2)
  rw [← mul_div_assoc, div_le_div_iff₀ (sq_pos_of_pos hu_pos) (sq_pos_of_pos hv_pos)]
  calc (1 - r ^ 2) * ‖v‖ ^ 2
      ≤ (1 - r ^ 2) * ((1 + K) ^ 2 * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hv_sq_le h1mr2_nn
    _ = (1 + K) ^ 2 * (1 - r ^ 2) * ‖u‖ ^ 2 := by ring

/-- `RudinRCA.Chapter11.poissonKernel` form of `poissonKernel_nontangential_le`. -/
lemma poissonKernel_nontangential_le' {r K α : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hK : 0 ≤ K)
    (hα : |α| ≤ K * (1 - r)) (t : ℝ) :
    RudinRCA.Chapter11.poissonKernel r (α - t) ≤
      (1 + K) ^ 2 * RudinRCA.Chapter11.poissonKernel r t := by
  have h := poissonKernel_nontangential_le hr0 hr1 hK hα t
  rw [RudinRCA.Chapter11.norm_sq_one_sub_polar, RudinRCA.Chapter11.norm_sq_one_sub_polar,
    Real.cos_neg] at h
  exact h

/-- Derivative formula for `- deriv (poissonKernel r)` on `ℝ` (`0 ≤ r < 1`). -/
private def poissonKernelNegDeriv (r u : ℝ) : ℝ :=
  (1 - r ^ 2) * (2 * r * Real.sin u) / (1 - 2 * r * Real.cos u + r ^ 2) ^ 2

private lemma hasDerivAt_poissonKernel {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (u : ℝ) :
    HasDerivAt (RudinRCA.Chapter11.poissonKernel r) (-poissonKernelNegDeriv r u) u := by
  have hden_pos : 0 < 1 - 2 * r * Real.cos u + r ^ 2 := by
    nlinarith [Real.cos_le_one u, sq_pos_of_pos (sub_pos.mpr hr1)]
  have hden_deriv : HasDerivAt (fun x : ℝ ↦ 1 - 2 * r * Real.cos x + r ^ 2)
      (2 * r * Real.sin u) u := by
    have hcos := (Real.hasDerivAt_cos u).const_mul (2 * r)
    have hsub := (hasDerivAt_const u (1 : ℝ)).sub hcos
    have hadd := hsub.add (hasDerivAt_const u (r ^ 2))
    convert hadd using 1
    ring
  have hquot := (hasDerivAt_const u (1 - r ^ 2)).div hden_deriv hden_pos.ne'
  refine hquot.congr_deriv ?_
  unfold poissonKernelNegDeriv
  ring

private lemma locInt_intervalIntegrable {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : LocallyIntegrable f MeasureTheory.volume) (a b : ℝ) :
    IntervalIntegrable f MeasureTheory.volume a b :=
  (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable

private lemma locInt_norm {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : LocallyIntegrable f MeasureTheory.volume) :
    LocallyIntegrable (fun x ↦ ‖f x‖) MeasureTheory.volume :=
  fun x ↦ (hf x).norm

private lemma locInt_comp_add_left {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : LocallyIntegrable f MeasureTheory.volume) (c : ℝ) :
    LocallyIntegrable (fun x ↦ f (c + x)) MeasureTheory.volume := by
  intro x
  have hii : IntervalIntegrable f MeasureTheory.volume (x - 1 + c) (x + 1 + c) :=
    locInt_intervalIntegrable hf (x - 1 + c) (x + 1 + c)
  have hcomp := hii.comp_add_left c
  rw [show x - 1 + c - c = x - 1 by ring, show x + 1 + c - c = x + 1 by ring,
    intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)] at hcomp
  exact ⟨Set.Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith),
    hcomp.mono_set Ioo_subset_Ioc_self⟩

private lemma locInt_comp_sub_left {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : LocallyIntegrable f MeasureTheory.volume) (c : ℝ) :
    LocallyIntegrable (fun x ↦ f (c - x)) MeasureTheory.volume := by
  intro x
  have hii : IntervalIntegrable f MeasureTheory.volume (c - (x - 1)) (c - (x + 1)) :=
    locInt_intervalIntegrable hf (c - (x - 1)) (c - (x + 1))
  have hcomp := hii.comp_sub_left c
  rw [show c - (c - (x - 1)) = x - 1 by ring, show c - (c - (x + 1)) = x + 1 by ring,
    intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)] at hcomp
  exact ⟨Set.Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith),
    hcomp.mono_set Ioo_subset_Ioc_self⟩

private lemma poissonKernel_eq_pi_add_integral {r s : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    RudinRCA.Chapter11.poissonKernel r s =
      RudinRCA.Chapter11.poissonKernel r Real.pi +
        ∫ u in s..Real.pi, poissonKernelNegDeriv r u := by
  have hcont : Continuous (fun u : ℝ ↦ -poissonKernelNegDeriv r u) := by
    unfold poissonKernelNegDeriv
    refine Continuous.neg (Continuous.div (by fun_prop) (by fun_prop) fun u ↦ ?_)
    have hden_pos : 0 < 1 - 2 * r * Real.cos u + r ^ 2 := by
      nlinarith [Real.cos_le_one u, sq_pos_of_pos (sub_pos.mpr hr1)]
    exact (sq_pos_of_pos hden_pos).ne'
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ ↦ hasDerivAt_poissonKernel hr0 hr1 u) (hcont.intervalIntegrable s Real.pi)
  rw [intervalIntegral.integral_neg] at hftc
  linarith

private lemma poissonKernel_half_integral {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ u in (0 : ℝ)..Real.pi, RudinRCA.Chapter11.poissonKernel r u = Real.pi := by
  have hint_full := (RudinRCA.Chapter11.node11_5_integral_eq_one hr0 hr1).1
  have hcont := RudinRCA.Chapter11.continuous_poissonKernel hr0 hr1
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) (-Real.pi) 0)
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 Real.pi)
  have hneg : (∫ u in (-Real.pi)..(0 : ℝ), RudinRCA.Chapter11.poissonKernel r u) =
      ∫ u in (0 : ℝ)..Real.pi, RudinRCA.Chapter11.poissonKernel r u := by
    have hc := intervalIntegral.integral_comp_neg (RudinRCA.Chapter11.poissonKernel r)
      (a := (0 : ℝ)) (b := Real.pi)
    simp only [neg_zero, RudinRCA.Chapter11.node11_5_even] at hc
    exact hc.symm
  rw [← hsplit, hneg] at hint_full
  have h2pi : 0 < 2 * Real.pi := Real.two_pi_pos
  have hsum : (∫ u in (0 : ℝ)..Real.pi, RudinRCA.Chapter11.poissonKernel r u) +
      (∫ u in (0 : ℝ)..Real.pi, RudinRCA.Chapter11.poissonKernel r u) = 2 * Real.pi := by
    exact ((inv_mul_eq_one₀ h2pi.ne').mp hint_full).symm
  linarith

/-- Fubini integration-by-parts identity on `[0, π]` for the Poisson kernel against a nonnegative
integrable function `φ`:
`∫_0^π P_r(s) φ(s) ds = P_r(π) Φ(π) + ∫_0^π (-P_r'(u)) Φ(u) du` where `Φ(u) = ∫_0^u φ`. -/
private lemma poissonKernel_fubini_ibp {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {φ : ℝ → ℝ} (hφ_loc : LocallyIntegrable φ MeasureTheory.volume) (hφ_nn : ∀ s, 0 ≤ φ s) :
    (∫ s in (0 : ℝ)..Real.pi, RudinRCA.Chapter11.poissonKernel r s * φ s) =
      RudinRCA.Chapter11.poissonKernel r Real.pi * (∫ s in (0 : ℝ)..Real.pi, φ s) +
        ∫ u in (0 : ℝ)..Real.pi,
          poissonKernelNegDeriv r u * (∫ s in (0 : ℝ)..u, φ s) := by
  let P := RudinRCA.Chapter11.poissonKernel r
  let Q := poissonKernelNegDeriv r
  let Φ : ℝ → ℝ := fun u ↦ ∫ s in (0 : ℝ)..u, φ s
  let μ₀ : Measure ℝ := MeasureTheory.volume.restrict (Set.Icc 0 Real.pi)
  have hP_cont : Continuous P := RudinRCA.Chapter11.continuous_poissonKernel hr0 hr1
  have hQ_cont : Continuous Q := by
    unfold Q poissonKernelNegDeriv
    refine Continuous.div (by fun_prop) (by fun_prop) fun u ↦ ?_
    have hden_pos : 0 < 1 - 2 * r * Real.cos u + r ^ 2 := by
      nlinarith [Real.cos_le_one u, sq_pos_of_pos (sub_pos.mpr hr1)]
    exact (sq_pos_of_pos hden_pos).ne'
  have hQ_nn : ∀ u ∈ Set.Icc (0 : ℝ) Real.pi, 0 ≤ Q u := by
    intro u hu
    unfold Q poissonKernelNegDeriv
    have hsin : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi hu.1 hu.2
    have h1mr2 : 0 ≤ 1 - r ^ 2 := by nlinarith
    have hden_pos : 0 < 1 - 2 * r * Real.cos u + r ^ 2 := by
      nlinarith [Real.cos_le_one u, sq_pos_of_pos (sub_pos.mpr hr1)]
    positivity
  have hΦ_cont : ContinuousOn Φ (Set.Icc 0 Real.pi) := by
    have h := intervalIntegral.continuousOn_primitive_interval
      (a := (0 : ℝ)) (b := Real.pi)
      (hφ_loc.integrableOn_isCompact isCompact_uIcc)
    rwa [Set.uIcc_of_le Real.pi_pos.le] at h
  have hΦ_nn : ∀ u ∈ Set.Icc (0 : ℝ) Real.pi, 0 ≤ Φ u := by
    intro u hu
    exact intervalIntegral.integral_nonneg hu.1 fun s _ ↦ hφ_nn s
  have hφ_int_Icc : Integrable φ μ₀ := hφ_loc.integrableOn_isCompact isCompact_Icc
  have hPφ_int_Icc : Integrable (fun s ↦ P s * φ s) μ₀ := by
    have hint := (locInt_intervalIntegrable hφ_loc 0 Real.pi).continuousOn_mul hP_cont.continuousOn
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le Real.pi_pos.le] at hint
    change IntegrableOn (fun s ↦ P s * φ s) (Set.Icc 0 Real.pi) MeasureTheory.volume
    simpa only [mul_comm] using hint
  have hQΦ_int_Icc : Integrable (fun u ↦ Q u * Φ u) μ₀ :=
    (hQ_cont.continuousOn.mul hΦ_cont).integrableOn_Icc
  have hP_ofReal : ∀ s ∈ Set.Icc (0 : ℝ) Real.pi,
      ENNReal.ofReal (P s) =
        ENNReal.ofReal (P Real.pi) +
          ∫⁻ u, (if s ≤ u then ENNReal.ofReal (Q u) else 0) ∂μ₀ := by
    intro s hs
    have hQ_int_s : IntegrableOn Q (Set.Icc s Real.pi) MeasureTheory.volume :=
      hQ_cont.integrableOn_Icc
    have hQ_nn_s : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc s Real.pi)] Q :=
      ae_restrict_of_forall_mem measurableSet_Icc fun u hu ↦
        hQ_nn u ⟨hs.1.trans hu.1, hu.2⟩
    have hlint_s :
        (∫⁻ u, (if s ≤ u then ENNReal.ofReal (Q u) else 0) ∂μ₀) =
          ENNReal.ofReal (∫ u in s..Real.pi, Q u) := by
      have hind : (fun u ↦ if s ≤ u then ENNReal.ofReal (Q u) else 0) =
          Set.indicator (Set.Ici s) (fun u ↦ ENNReal.ofReal (Q u)) := by
        ext u; simp [Set.indicator]
      have hinter : Set.Icc (0 : ℝ) Real.pi ∩ Set.Ici s = Set.Icc s Real.pi := by
        ext u; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]; constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨hs.1.trans h1, h2⟩, h1⟩
      rw [hind, lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
        Set.inter_comm, hinter, ← ofReal_integral_eq_lintegral_ofReal hQ_int_s hQ_nn_s,
        intervalIntegral.integral_of_le hs.2, integral_Icc_eq_integral_Ioc]
    have hP_pi_nn : 0 ≤ P Real.pi := (RudinRCA.Chapter11.node11_5_pos hr0 hr1 Real.pi).le
    have hint_nn : 0 ≤ ∫ u in s..Real.pi, Q u :=
      intervalIntegral.integral_nonneg hs.2 fun u hu ↦ hQ_nn u ⟨hs.1.trans hu.1, hu.2⟩
    rw [hlint_s, ← ENNReal.ofReal_add hP_pi_nn hint_nn,
      ← poissonKernel_eq_pi_add_integral hr0 hr1]
  have hLHS : ENNReal.ofReal (∫ s in (0 : ℝ)..Real.pi, P s * φ s) =
      ∫⁻ s, ENNReal.ofReal (P s * φ s) ∂μ₀ := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, ← integral_Icc_eq_integral_Ioc]
    exact ofReal_integral_eq_lintegral_ofReal hPφ_int_Icc
      (ae_of_all _ fun s ↦ mul_nonneg (RudinRCA.Chapter11.node11_5_pos hr0 hr1 s).le (hφ_nn s))
  have hswap :
      (∫⁻ s, (∫⁻ u, (if s ≤ u then ENNReal.ofReal (Q u) else 0) ∂μ₀) *
          ENNReal.ofReal (φ s) ∂μ₀) =
        ∫⁻ u, ENNReal.ofReal (Q u * Φ u) ∂μ₀ := by
    have hstep1 :
        (∫⁻ s, (∫⁻ u, (if s ≤ u then ENNReal.ofReal (Q u) else 0) ∂μ₀) *
            ENNReal.ofReal (φ s) ∂μ₀) =
          ∫⁻ s, ∫⁻ u,
            (if s ≤ u then ENNReal.ofReal (Q u) * ENNReal.ofReal (φ s) else 0) ∂μ₀ ∂μ₀ := by
      refine lintegral_congr fun s ↦ ?_
      have hm : AEMeasurable (fun u : ℝ ↦ if s ≤ u then ENNReal.ofReal (Q u) else 0) μ₀ :=
        (Measurable.ite measurableSet_Ici hQ_cont.measurable.ennreal_ofReal
          measurable_const).aemeasurable
      rw [← lintegral_mul_const'' _ hm]
      refine lintegral_congr fun u ↦ ?_
      split_ifs <;> simp
    have hprod_meas : AEMeasurable
        (Function.uncurry fun s u : ℝ ↦
          if s ≤ u then ENNReal.ofReal (Q u) * ENNReal.ofReal (φ s) else 0)
        (μ₀.prod μ₀) := by
      have hle_meas : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
        isClosed_le continuous_fst continuous_snd |>.measurableSet
      have hQ_aem : AEMeasurable (fun p : ℝ × ℝ ↦ ENNReal.ofReal (Q p.2)) (μ₀.prod μ₀) :=
        (hQ_cont.measurable.ennreal_ofReal.comp measurable_snd).aemeasurable
      have hφ_aem : AEMeasurable (fun p : ℝ × ℝ ↦ ENNReal.ofReal (φ p.1)) (μ₀.prod μ₀) :=
        hφ_int_Icc.aestronglyMeasurable.aemeasurable.ennreal_ofReal.comp_quasiMeasurePreserving
          MeasureTheory.Measure.quasiMeasurePreserving_fst
      have hind_eq : (Function.uncurry fun s u : ℝ ↦
          if s ≤ u then ENNReal.ofReal (Q u) * ENNReal.ofReal (φ s) else 0) =
          Set.indicator {p : ℝ × ℝ | p.1 ≤ p.2}
            (fun p : ℝ × ℝ ↦ ENNReal.ofReal (Q p.2) * ENNReal.ofReal (φ p.1)) := by
        ext ⟨s, u⟩; simp [Set.indicator]
      rw [hind_eq]
      exact (hQ_aem.mul hφ_aem).indicator hle_meas
    rw [hstep1, lintegral_lintegral_swap hprod_meas]
    refine (lintegral_congr_ae ?_)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hpull :
        (∫⁻ s, (if s ≤ u then ENNReal.ofReal (Q u) * ENNReal.ofReal (φ s) else 0) ∂μ₀) =
          ENNReal.ofReal (Q u) * ∫⁻ s, (if s ≤ u then ENNReal.ofReal (φ s) else 0) ∂μ₀ := by
      have hm : AEMeasurable (fun s : ℝ ↦ if s ≤ u then ENNReal.ofReal (φ s) else 0) μ₀ := by
        have hind_eq : (fun s : ℝ ↦ if s ≤ u then ENNReal.ofReal (φ s) else 0) =
            Set.indicator (Set.Iic u) (fun s : ℝ ↦ ENNReal.ofReal (φ s)) := by
          ext s; simp [Set.indicator]
        rw [hind_eq]
        exact hφ_int_Icc.aestronglyMeasurable.aemeasurable.ennreal_ofReal.indicator
          measurableSet_Iic
      rw [← lintegral_const_mul'' _ hm]
      refine lintegral_congr fun s ↦ ?_
      split_ifs <;> simp
    have hΦ_u : (∫⁻ s, (if s ≤ u then ENNReal.ofReal (φ s) else 0) ∂μ₀) =
        ENNReal.ofReal (Φ u) := by
      have hind : (fun s ↦ if s ≤ u then ENNReal.ofReal (φ s) else 0) =
          Set.indicator (Set.Iic u) (fun s ↦ ENNReal.ofReal (φ s)) := by
        ext s; simp [Set.indicator]
      have hinter : Set.Iic u ∩ Set.Icc (0 : ℝ) Real.pi = Set.Icc 0 u := by
        ext s; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]; constructor
        · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hu.2⟩
      have hφ_int_u : IntegrableOn φ (Set.Icc 0 u) MeasureTheory.volume :=
        hφ_loc.integrableOn_isCompact isCompact_Icc
      rw [hind, lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
        hinter, ← ofReal_integral_eq_lintegral_ofReal hφ_int_u (ae_of_all _ hφ_nn),
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu.1]
    rw [hpull, hΦ_u, ← ENNReal.ofReal_mul (hQ_nn u hu)]
  have hRHS_eq :
      (∫⁻ s, ENNReal.ofReal (P s * φ s) ∂μ₀) =
        ENNReal.ofReal (P Real.pi * Φ Real.pi + ∫ u in (0 : ℝ)..Real.pi, Q u * Φ u) := by
    have hcongr :
        (∫⁻ s, ENNReal.ofReal (P s * φ s) ∂μ₀) =
          ∫⁻ s, (ENNReal.ofReal (P Real.pi) * ENNReal.ofReal (φ s) +
            (∫⁻ u, (if s ≤ u then ENNReal.ofReal (Q u) else 0) ∂μ₀) *
              ENNReal.ofReal (φ s)) ∂μ₀ := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      rw [ENNReal.ofReal_mul (RudinRCA.Chapter11.node11_5_pos hr0 hr1 s).le, hP_ofReal s hs,
        add_mul]
    have hm1 : AEMeasurable (fun s ↦ ENNReal.ofReal (P Real.pi) * ENNReal.ofReal (φ s)) μ₀ :=
      aemeasurable_const.mul hφ_int_Icc.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    have hm2 : AEMeasurable
        (fun s ↦ (∫⁻ u, (if s ≤ u then ENNReal.ofReal (Q u) else 0) ∂μ₀) *
          ENNReal.ofReal (φ s)) μ₀ := by
      have hprod_meas : Measurable
          (Function.uncurry fun s u : ℝ ↦ if s ≤ u then ENNReal.ofReal (Q u) else 0) :=
        Measurable.ite (isClosed_le continuous_fst continuous_snd).measurableSet
          (hQ_cont.measurable.ennreal_ofReal.comp measurable_snd) measurable_const
      exact hprod_meas.lintegral_prod_right'.aemeasurable.mul
        hφ_int_Icc.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    have hterm1 :
        (∫⁻ s, ENNReal.ofReal (P Real.pi) * ENNReal.ofReal (φ s) ∂μ₀) =
          ENNReal.ofReal (P Real.pi * Φ Real.pi) := by
      rw [lintegral_const_mul'' _ hφ_int_Icc.aestronglyMeasurable.aemeasurable.ennreal_ofReal,
        ← ofReal_integral_eq_lintegral_ofReal hφ_int_Icc (ae_of_all _ hφ_nn)]
      have hint_pi : (∫ s, φ s ∂μ₀) = Φ Real.pi := by
        change (∫ s in Set.Icc 0 Real.pi, φ s) = ∫ s in (0 : ℝ)..Real.pi, φ s
        rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le Real.pi_pos.le]
      rw [hint_pi, ← ENNReal.ofReal_mul (RudinRCA.Chapter11.node11_5_pos hr0 hr1 Real.pi).le]
    have hterm2 :
        (∫⁻ u, ENNReal.ofReal (Q u * Φ u) ∂μ₀) =
          ENNReal.ofReal (∫ u in (0 : ℝ)..Real.pi, Q u * Φ u) := by
      rw [intervalIntegral.integral_of_le Real.pi_pos.le, ← integral_Icc_eq_integral_Ioc,
        ofReal_integral_eq_lintegral_ofReal hQΦ_int_Icc]
      exact ae_restrict_of_forall_mem measurableSet_Icc fun u hu ↦
        mul_nonneg (hQ_nn u hu) (hΦ_nn u hu)
    have hnn1 : 0 ≤ P Real.pi * Φ Real.pi :=
      mul_nonneg (RudinRCA.Chapter11.node11_5_pos hr0 hr1 Real.pi).le
        (hΦ_nn Real.pi ⟨Real.pi_pos.le, le_rfl⟩)
    have hnn2 : 0 ≤ ∫ u in (0 : ℝ)..Real.pi, Q u * Φ u :=
      intervalIntegral.integral_nonneg Real.pi_pos.le fun u hu ↦
        mul_nonneg (hQ_nn u hu) (hΦ_nn u hu)
    rw [hcongr, lintegral_add_left' hm1, hterm1, hswap, hterm2, ← ENNReal.ofReal_add hnn1 hnn2]
  have hLHS_nn : 0 ≤ ∫ s in (0 : ℝ)..Real.pi, P s * φ s :=
    intervalIntegral.integral_nonneg Real.pi_pos.le fun s _ ↦
      mul_nonneg (RudinRCA.Chapter11.node11_5_pos hr0 hr1 s).le (hφ_nn s)
  have hRHS_nn : 0 ≤ P Real.pi * Φ Real.pi + ∫ u in (0 : ℝ)..Real.pi, Q u * Φ u :=
    add_nonneg
      (mul_nonneg (RudinRCA.Chapter11.node11_5_pos hr0 hr1 Real.pi).le
        (hΦ_nn Real.pi ⟨Real.pi_pos.le, le_rfl⟩))
      (intervalIntegral.integral_nonneg Real.pi_pos.le fun u hu ↦
        mul_nonneg (hQ_nn u hu) (hΦ_nn u hu))
  exact (ENNReal.ofReal_eq_ofReal_iff hLHS_nn hRHS_nn).mp (hLHS.trans hRHS_eq)

/-- Uniform nontangential Poisson estimate at a symmetric Lebesgue point `θ₀` (universe-free helper
for `poisson_nontangential_tendsto_of_lebesgue_pt`). -/
private lemma poisson_nontangential_eps_delta
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E} (hg_per : Function.Periodic g (2 * Real.pi))
    (hg_loc : LocallyIntegrable g MeasureTheory.volume) {θ₀ : ℝ}
    (hθ₀ : Tendsto (fun h : ℝ ↦ (2 * h)⁻¹ * ∫ y in (θ₀ - h)..(θ₀ + h), ‖g y - g θ₀‖)
      (𝓝[>] 0) (𝓝 0))
    {K : ℝ} (hK : 0 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ θ : ℝ, |θ - θ₀| ≤ K * (1 - r) →
      ‖((2 * Real.pi)⁻¹ •
        ∫ t in (-Real.pi)..Real.pi,
          ((1 - r ^ 2) /
            ‖(1 : ℂ) - (r : ℂ) * Complex.exp (((θ - t : ℝ) : ℂ) * Complex.I)‖ ^ 2) • g t) -
        g θ₀‖ < ε := by
  let C_K : ℝ := (1 + K) ^ 2
  have hCK_pos : 0 < C_K := by positivity
  let η : ℝ := ε / (2 * C_K)
  have hη_pos : 0 < η := div_pos hε (by positivity)
  let φ : ℝ → ℝ := fun s ↦ ‖g (θ₀ + s) - g θ₀‖ + ‖g (θ₀ - s) - g θ₀‖
  let Φ : ℝ → ℝ := fun u ↦ ∫ s in (0 : ℝ)..u, φ s
  have hsub_loc : LocallyIntegrable (fun y ↦ ‖g y - g θ₀‖) MeasureTheory.volume :=
    locInt_norm (LocallyIntegrable.sub hg_loc (locallyIntegrable_const (g θ₀)))
  have hφ_loc : LocallyIntegrable φ MeasureTheory.volume :=
    LocallyIntegrable.add (locInt_comp_add_left hsub_loc θ₀) (locInt_comp_sub_left hsub_loc θ₀)
  have hφ_nn : ∀ s, 0 ≤ φ s := fun s ↦ add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hΦ_eq_symm : ∀ u : ℝ, 0 ≤ u → Φ u = ∫ y in (θ₀ - u)..(θ₀ + u), ‖g y - g θ₀‖ := by
    intro u _
    dsimp [Φ, φ]
    have hi1 : IntervalIntegrable (fun s ↦ ‖g (θ₀ + s) - g θ₀‖) MeasureTheory.volume 0 u :=
      locInt_intervalIntegrable (locInt_comp_add_left hsub_loc θ₀) 0 u
    have hi2 : IntervalIntegrable (fun s ↦ ‖g (θ₀ - s) - g θ₀‖) MeasureTheory.volume 0 u :=
      locInt_intervalIntegrable (locInt_comp_sub_left hsub_loc θ₀) 0 u
    rw [intervalIntegral.integral_add hi1 hi2]
    have hc1 : (∫ s in (0 : ℝ)..u, ‖g (θ₀ + s) - g θ₀‖) =
        ∫ y in θ₀..(θ₀ + u), ‖g y - g θ₀‖ := by
      simpa [add_comm] using
        intervalIntegral.integral_comp_add_left (fun y ↦ ‖g y - g θ₀‖) θ₀ (a := 0) (b := u)
    have hc2 : (∫ s in (0 : ℝ)..u, ‖g (θ₀ - s) - g θ₀‖) =
        ∫ y in (θ₀ - u)..θ₀, ‖g y - g θ₀‖ := by
      have h := intervalIntegral.integral_comp_sub_left (fun y ↦ ‖g y - g θ₀‖) θ₀ (a := 0) (b := u)
      simpa only [sub_zero] using h
    rw [hc1, hc2, add_comm, intervalIntegral.integral_add_adjacent_intervals
      (locInt_intervalIntegrable hsub_loc (θ₀ - u) θ₀)
      (locInt_intervalIntegrable hsub_loc θ₀ (θ₀ + u))]
  have hleb_ev : ∀ᶠ u in 𝓝[>] (0 : ℝ),
      dist ((2 * u)⁻¹ * ∫ y in (θ₀ - u)..(θ₀ + u), ‖g y - g θ₀‖) 0 < η :=
    Metric.tendsto_nhds.mp hθ₀ η hη_pos
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hleb_ev
  obtain ⟨δ₀, hδ₀_pos, hδ₀_sub⟩ := hleb_ev
  let δ₁ : ℝ := min (δ₀ / 2) (Real.pi / 2)
  have hδ₁_pos : 0 < δ₁ := lt_min (half_pos hδ₀_pos) (half_pos Real.pi_pos)
  have hδ₁_le_pi : δ₁ ≤ Real.pi := (min_le_right _ _).trans (by linarith [Real.pi_pos])
  have hΦ_bound : ∀ u ∈ Set.Icc 0 δ₁, Φ u ≤ 2 * η * u := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with rfl | hu_pos
    · simp [Φ]
    · have hu_dist : dist u 0 < δ₀ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hu_pos]
        exact lt_of_le_of_lt (hu.2.trans (min_le_left _ _)) (half_lt_self hδ₀_pos)
      have hdist := hδ₀_sub hu_dist hu_pos
      rw [Real.dist_eq, sub_zero, ← hΦ_eq_symm u hu_pos.le,
        abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (by positivity))
          (intervalIntegral.integral_nonneg hu_pos.le fun s _ ↦ hφ_nn s))] at hdist
      have h2u_pos : 0 < 2 * u := by positivity
      calc Φ u = (2 * u) * ((2 * u)⁻¹ * Φ u) := by field_simp
        _ ≤ (2 * u) * η := mul_le_mul_of_nonneg_left hdist.le h2u_pos.le
        _ = 2 * η * u := by ring
  have htail_lim : Tendsto
      (fun r : ℝ ↦ (2 * Real.pi)⁻¹ * C_K *
        (RudinRCA.Chapter11.poissonKernel r δ₁ * Φ Real.pi))
      (𝓝[<] 1) (𝓝 0) := by
    have h0 := (RudinRCA.Chapter11.node11_5_tail_tendsto_zero hδ₁_pos hδ₁_le_pi).1
    simpa using (h0.mul_const (Φ Real.pi)).const_mul ((2 * Real.pi)⁻¹ * C_K)
  have hr_pos_ev : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT zero_lt_one
  have hr_tail_ev := htail_lim.eventually (Metric.ball_mem_nhds 0 (half_pos hε))
  filter_upwards [hr_pos_ev, hr_tail_ev] with r ⟨hr0_lt, hr1⟩ htail_j θ hθ_cone
  have hr0 : 0 ≤ r := hr0_lt.le
  -- Step 1: Rewrite kernel in terms of `poissonKernel` and subtract `g θ₀` inside the integral
  have hkern_eq : ∀ t : ℝ,
      (1 - r ^ 2) / ‖(1 : ℂ) - (r : ℂ) * Complex.exp (((θ - t : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
        RudinRCA.Chapter11.poissonKernel r (θ - t) := fun t ↦ by
    rw [RudinRCA.Chapter11.norm_sq_one_sub_polar]
    rfl
  have hP_shift_int_one :
      (2 * Real.pi)⁻¹ * (∫ t in (-Real.pi)..Real.pi,
        RudinRCA.Chapter11.poissonKernel r (θ - t)) = 1 := by
    have hper : Function.Periodic (fun t ↦ RudinRCA.Chapter11.poissonKernel r (θ - t))
        (2 * Real.pi) := by
      intro t
      dsimp only
      rw [← RudinRCA.Chapter11.node11_5_even, ← RudinRCA.Chapter11.node11_5_even r (θ - t)]
      have : -(θ - (t + 2 * Real.pi)) = -(θ - t) + 2 * Real.pi := by ring
      rw [this, RudinRCA.Chapter11.node11_5_periodic]
    have hshift := hper.intervalIntegral_add_eq (θ - Real.pi) (-Real.pi)
    have he1 : θ - Real.pi + 2 * Real.pi = θ + Real.pi := by ring
    have he2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [he1, he2] at hshift
    rw [← hshift]
    have hcomp := intervalIntegral.integral_comp_sub_left
      (RudinRCA.Chapter11.poissonKernel r) θ (a := θ - Real.pi) (b := θ + Real.pi)
    have hs1 : θ - (θ + Real.pi) = -Real.pi := by ring
    have hs2 : θ - (θ - Real.pi) = Real.pi := by ring
    rw [hs1, hs2] at hcomp
    rw [hcomp]
    exact (RudinRCA.Chapter11.node11_5_integral_eq_one hr0 hr1).1
  have hPg_int : IntervalIntegrable
      (fun t ↦ RudinRCA.Chapter11.poissonKernel r (θ - t) • g t)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (locInt_intervalIntegrable hg_loc (-Real.pi) Real.pi).continuousOn_smul
      ((RudinRCA.Chapter11.continuous_poissonKernel hr0 hr1).comp
        (continuous_const.sub continuous_id)).continuousOn
  have hPconst_int : IntervalIntegrable
      (fun t ↦ RudinRCA.Chapter11.poissonKernel r (θ - t) • g θ₀)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (((RudinRCA.Chapter11.continuous_poissonKernel hr0 hr1).comp
      (continuous_const.sub continuous_id)).smul continuous_const).intervalIntegrable _ _
  have hdiff_repr :
      ((2 * Real.pi)⁻¹ • ∫ t in (-Real.pi)..Real.pi,
        ((1 - r ^ 2) /
          ‖(1 : ℂ) - (r : ℂ) * Complex.exp (((θ - t : ℝ) : ℂ) * Complex.I)‖ ^ 2) • g t) -
        g θ₀ =
      (2 * Real.pi)⁻¹ • ∫ t in (-Real.pi)..Real.pi,
        RudinRCA.Chapter11.poissonKernel r (θ - t) • (g t - g θ₀) := by
    simp_rw [hkern_eq]
    have hg0_eq : g θ₀ = (2 * Real.pi)⁻¹ • ∫ t in (-Real.pi)..Real.pi,
        RudinRCA.Chapter11.poissonKernel r (θ - t) • g θ₀ := by
      rw [intervalIntegral.integral_smul_const, smul_smul, hP_shift_int_one, one_smul]
    conv_lhs => rw [hg0_eq]
    rw [← smul_sub, ← intervalIntegral.integral_sub hPg_int hPconst_int]
    congr 1
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    rw [smul_sub]
  have hnorm_le_1 :
      ‖((2 * Real.pi)⁻¹ • ∫ t in (-Real.pi)..Real.pi,
        ((1 - r ^ 2) /
          ‖(1 : ℂ) - (r : ℂ) * Complex.exp (((θ - t : ℝ) : ℂ) * Complex.I)‖ ^ 2) • g t) -
        g θ₀‖ ≤
      (2 * Real.pi)⁻¹ * ∫ t in (-Real.pi)..Real.pi,
        RudinRCA.Chapter11.poissonKernel r (θ - t) * ‖g t - g θ₀‖ := by
    rw [hdiff_repr, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr Real.two_pi_pos.le)]
    gcongr
    calc ‖∫ t in (-Real.pi)..Real.pi,
          RudinRCA.Chapter11.poissonKernel r (θ - t) • (g t - g θ₀)‖
        ≤ ∫ t in (-Real.pi)..Real.pi,
            ‖RudinRCA.Chapter11.poissonKernel r (θ - t) • (g t - g θ₀)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith [Real.pi_pos])
      _ = ∫ t in (-Real.pi)..Real.pi,
            RudinRCA.Chapter11.poissonKernel r (θ - t) * ‖g t - g θ₀‖ := by
          refine intervalIntegral.integral_congr fun t _ ↦ ?_
          rw [norm_smul, Real.norm_of_nonneg
            (RudinRCA.Chapter11.node11_5_pos hr0 hr1 (θ - t)).le]
  -- Step 2: Shift integration variable `t = θ₀ + s` by `2π`-periodicity and apply cone bound
  let α : ℝ := θ - θ₀
  have hshift_θ₀ :
      (∫ t in (-Real.pi)..Real.pi,
        RudinRCA.Chapter11.poissonKernel r (θ - t) * ‖g t - g θ₀‖) =
      ∫ s in (-Real.pi)..Real.pi,
        RudinRCA.Chapter11.poissonKernel r (α - s) * ‖g (θ₀ + s) - g θ₀‖ := by
    have hper : Function.Periodic
        (fun t ↦ RudinRCA.Chapter11.poissonKernel r (θ - t) * ‖g t - g θ₀‖)
        (2 * Real.pi) := by
      intro t
      have hP : RudinRCA.Chapter11.poissonKernel r (θ - (t + 2 * Real.pi)) =
          RudinRCA.Chapter11.poissonKernel r (θ - t) := by
        rw [← RudinRCA.Chapter11.node11_5_even, ← RudinRCA.Chapter11.node11_5_even r (θ - t)]
        have : -(θ - (t + 2 * Real.pi)) = -(θ - t) + 2 * Real.pi := by ring
        rw [this, RudinRCA.Chapter11.node11_5_periodic]
      dsimp only
      rw [hP, hg_per t]
    have hp := hper.intervalIntegral_add_eq (θ₀ - Real.pi) (-Real.pi)
    have he1 : θ₀ - Real.pi + 2 * Real.pi = θ₀ + Real.pi := by ring
    have he2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [he1, he2] at hp
    rw [← hp]
    have hc := intervalIntegral.integral_comp_add_left
      (fun t ↦ RudinRCA.Chapter11.poissonKernel r (θ - t) * ‖g t - g θ₀‖) θ₀
      (a := -Real.pi) (b := Real.pi)
    rw [show θ₀ + -Real.pi = θ₀ - Real.pi by ring] at hc
    rw [← hc]
    refine intervalIntegral.integral_congr fun s _ ↦ ?_
    have hαs : θ - (θ₀ + s) = α - s := by dsimp [α]; ring
    rw [hαs]
  have hcone_int :
      (∫ s in (-Real.pi)..Real.pi,
        RudinRCA.Chapter11.poissonKernel r (α - s) * ‖g (θ₀ + s) - g θ₀‖) ≤
      C_K * ∫ s in (0 : ℝ)..Real.pi, RudinRCA.Chapter11.poissonKernel r s * φ s := by
    have hi_lhs : IntervalIntegrable
        (fun s ↦ RudinRCA.Chapter11.poissonKernel r (α - s) * ‖g (θ₀ + s) - g θ₀‖)
        MeasureTheory.volume (-Real.pi) Real.pi := by
      have h := (locInt_intervalIntegrable (locInt_comp_add_left hsub_loc θ₀) (-Real.pi) Real.pi).continuousOn_mul
        ((RudinRCA.Chapter11.continuous_poissonKernel hr0 hr1).comp
          (show Continuous fun s : ℝ ↦ α - s by fun_prop)).continuousOn
      simpa only [Function.comp_def, mul_comm] using h
    have hi_rhs : IntervalIntegrable
        (fun s ↦ C_K * (RudinRCA.Chapter11.poissonKernel r s * ‖g (θ₀ + s) - g θ₀‖))
        MeasureTheory.volume (-Real.pi) Real.pi := by
      have h := (locInt_intervalIntegrable (locInt_comp_add_left hsub_loc θ₀) (-Real.pi) Real.pi).continuousOn_mul
        (RudinRCA.Chapter11.continuous_poissonKernel hr0 hr1).continuousOn
      have h' : IntervalIntegrable
          (fun s ↦ RudinRCA.Chapter11.poissonKernel r s * ‖g (θ₀ + s) - g θ₀‖)
          MeasureTheory.volume (-Real.pi) Real.pi := by
        simpa only [mul_comm] using h
      exact h'.const_mul C_K
    have hle1 :
        (∫ s in (-Real.pi)..Real.pi,
          RudinRCA.Chapter11.poissonKernel r (α - s) * ‖g (θ₀ + s) - g θ₀‖) ≤
        C_K * ∫ s in (-Real.pi)..Real.pi,
          RudinRCA.Chapter11.poissonKernel r s * ‖g (θ₀ + s) - g θ₀‖ := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) hi_lhs hi_rhs
        fun s _ ↦ ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (poissonKernel_nontangential_le' hr0 hr1 hK hθ_cone s) (norm_nonneg _)
    have hfold :
        (∫ s in (-Real.pi)..Real.pi,
          RudinRCA.Chapter11.poissonKernel r s * ‖g (θ₀ + s) - g θ₀‖) =
        ∫ s in (0 : ℝ)..Real.pi, RudinRCA.Chapter11.poissonKernel r s * φ s := by
      have hi_a : IntervalIntegrable
          (fun s ↦ RudinRCA.Chapter11.poissonKernel r s * ‖g (θ₀ + s) - g θ₀‖)
          MeasureTheory.volume (-Real.pi) 0 := by
        have h := (locInt_intervalIntegrable (locInt_comp_add_left hsub_loc θ₀) (-Real.pi) 0).continuousOn_mul
          (RudinRCA.Chapter11.continuous_poissonKernel hr0 hr1).continuousOn
        simpa only [mul_comm] using h
      have hi_b : IntervalIntegrable
          (fun s ↦ RudinRCA.Chapter11.poissonKernel r s * ‖g (θ₀ + s) - g θ₀‖)
          MeasureTheory.volume 0 Real.pi := by
        have h := (locInt_intervalIntegrable (locInt_comp_add_left hsub_loc θ₀) 0 Real.pi).continuousOn_mul
          (RudinRCA.Chapter11.continuous_poissonKernel hr0 hr1).continuousOn
        simpa only [mul_comm] using h
      have hi_c : IntervalIntegrable
          (fun s ↦ RudinRCA.Chapter11.poissonKernel r s * ‖g (θ₀ - s) - g θ₀‖)
          MeasureTheory.volume 0 Real.pi := by
        have h := (locInt_intervalIntegrable (locInt_comp_sub_left hsub_loc θ₀) 0 Real.pi).continuousOn_mul
          (RudinRCA.Chapter11.continuous_poissonKernel hr0 hr1).continuousOn
        simpa only [mul_comm] using h
      rw [← intervalIntegral.integral_add_adjacent_intervals hi_a hi_b]
      have hneg := intervalIntegral.integral_comp_neg
        (fun s ↦ RudinRCA.Chapter11.poissonKernel r s * ‖g (θ₀ + s) - g θ₀‖)
        (a := 0) (b := Real.pi)
      simp only [neg_zero, RudinRCA.Chapter11.node11_5_even, ← sub_eq_add_neg] at hneg
      rw [← hneg, add_comm, ← intervalIntegral.integral_add hi_b hi_c]
      refine intervalIntegral.integral_congr fun s _ ↦ ?_
      dsimp [φ]
      ring
    rwa [hfold] at hle1
  -- Step 3: Apply Fubini IBP and split `[0, π]` at `δ₁`
  have hibp := poissonKernel_fubini_ibp hr0 hr1 hφ_loc hφ_nn
  have hQ_cont : Continuous (poissonKernelNegDeriv r) := by
    unfold poissonKernelNegDeriv
    refine Continuous.div (by fun_prop) (by fun_prop) fun u ↦ ?_
    have hden_pos : 0 < 1 - 2 * r * Real.cos u + r ^ 2 := by
      nlinarith [Real.cos_le_one u, sq_pos_of_pos (sub_pos.mpr hr1)]
    exact (sq_pos_of_pos hden_pos).ne'
  have hQ_nn : ∀ u ∈ Set.Icc (0 : ℝ) Real.pi, 0 ≤ poissonKernelNegDeriv r u := by
    intro u hu
    unfold poissonKernelNegDeriv
    have hsin : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi hu.1 hu.2
    have h1mr2 : 0 ≤ 1 - r ^ 2 := by nlinarith
    have hden_pos : 0 < 1 - 2 * r * Real.cos u + r ^ 2 := by
      nlinarith [Real.cos_le_one u, sq_pos_of_pos (sub_pos.mpr hr1)]
    positivity
  have hΦ_cont_Icc : ContinuousOn Φ (Set.Icc 0 Real.pi) := by
    have h := intervalIntegral.continuousOn_primitive_interval
      (a := (0 : ℝ)) (b := Real.pi)
      (hφ_loc.integrableOn_isCompact isCompact_uIcc)
    rwa [Set.uIcc_of_le Real.pi_pos.le] at h
  have hQΦ_int_0_δ : IntervalIntegrable (fun u ↦ poissonKernelNegDeriv r u * Φ u)
      MeasureTheory.volume 0 δ₁ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hδ₁_pos.le]
    exact (hQ_cont.continuousOn.mul
      (hΦ_cont_Icc.mono (Set.Icc_subset_Icc_right hδ₁_le_pi))).integrableOn_Icc
  have hQΦ_int_δ_pi : IntervalIntegrable (fun u ↦ poissonKernelNegDeriv r u * Φ u)
      MeasureTheory.volume δ₁ Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hδ₁_le_pi]
    exact (hQ_cont.continuousOn.mul
      (hΦ_cont_Icc.mono (Set.Icc_subset_Icc_left hδ₁_pos.le))).integrableOn_Icc
  have hsplit_δ :
      (∫ u in (0 : ℝ)..Real.pi, poissonKernelNegDeriv r u * Φ u) =
        (∫ u in (0 : ℝ)..δ₁, poissonKernelNegDeriv r u * Φ u) +
          (∫ u in δ₁..Real.pi, poissonKernelNegDeriv r u * Φ u) :=
    (intervalIntegral.integral_add_adjacent_intervals hQΦ_int_0_δ hQΦ_int_δ_pi).symm
  have hnear_le :
      (∫ u in (0 : ℝ)..δ₁, poissonKernelNegDeriv r u * Φ u) ≤ 2 * Real.pi * η := by
    have hle_u :
        (∫ u in (0 : ℝ)..δ₁, poissonKernelNegDeriv r u * Φ u) ≤
          2 * η * ∫ u in (0 : ℝ)..δ₁, poissonKernelNegDeriv r u * u := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on hδ₁_pos.le
        hQΦ_int_0_δ
        (((hQ_cont.mul continuous_id).const_mul (2 * η)).intervalIntegrable 0 δ₁)
        fun u hu ↦ ?_
      have hQu : 0 ≤ poissonKernelNegDeriv r u :=
        hQ_nn u ⟨hu.1, hu.2.trans hδ₁_le_pi⟩
      calc poissonKernelNegDeriv r u * Φ u
          ≤ poissonKernelNegDeriv r u * (2 * η * u) :=
            mul_le_mul_of_nonneg_left (hΦ_bound u hu) hQu
        _ = 2 * η * (poissonKernelNegDeriv r u * u) := by ring
    have hQu_ibp :
        (∫ u in (0 : ℝ)..δ₁, poissonKernelNegDeriv r u * u) ≤ Real.pi := by
      have hprod_deriv : ∀ u : ℝ,
          HasDerivAt (fun x ↦ RudinRCA.Chapter11.poissonKernel r x * x)
            (-poissonKernelNegDeriv r u * u + RudinRCA.Chapter11.poissonKernel r u) u := by
        intro u
        refine ((hasDerivAt_poissonKernel hr0 hr1 u).mul (hasDerivAt_id' u)).congr_deriv ?_
        ring
      have hcont_f1 : Continuous (fun u ↦ -poissonKernelNegDeriv r u * u) :=
        (hQ_cont.neg).mul continuous_id
      have hcont_f2 : Continuous (RudinRCA.Chapter11.poissonKernel r) :=
        RudinRCA.Chapter11.continuous_poissonKernel hr0 hr1
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ ↦ hprod_deriv u) ((hcont_f1.add hcont_f2).intervalIntegrable 0 δ₁)
      rw [intervalIntegral.integral_add
          (hcont_f1.intervalIntegrable 0 δ₁) (hcont_f2.intervalIntegrable 0 δ₁)] at hftc
      have hneg_mul : (∫ u in (0 : ℝ)..δ₁, -poissonKernelNegDeriv r u * u) =
          -∫ u in (0 : ℝ)..δ₁, poissonKernelNegDeriv r u * u := by
        simp_rw [neg_mul]
        exact intervalIntegral.integral_neg
      rw [hneg_mul, mul_zero, sub_zero] at hftc
      have hPδ_nn : 0 ≤ RudinRCA.Chapter11.poissonKernel r δ₁ * δ₁ :=
        mul_nonneg (RudinRCA.Chapter11.node11_5_pos hr0 hr1 δ₁).le hδ₁_pos.le
      have hP_le_pi :
          (∫ u in (0 : ℝ)..δ₁, RudinRCA.Chapter11.poissonKernel r u) ≤ Real.pi := by
        rw [← poissonKernel_half_integral hr0 hr1,
          ← intervalIntegral.integral_add_adjacent_intervals
            (hcont_f2.intervalIntegrable 0 δ₁) (hcont_f2.intervalIntegrable δ₁ Real.pi)]
        have hrest : 0 ≤ ∫ u in δ₁..Real.pi, RudinRCA.Chapter11.poissonKernel r u :=
          intervalIntegral.integral_nonneg hδ₁_le_pi fun u _ ↦
            (RudinRCA.Chapter11.node11_5_pos hr0 hr1 u).le
        linarith
      linarith
    nlinarith
  have hfar_le :
      RudinRCA.Chapter11.poissonKernel r Real.pi * Φ Real.pi +
        (∫ u in δ₁..Real.pi, poissonKernelNegDeriv r u * Φ u) ≤
      RudinRCA.Chapter11.poissonKernel r δ₁ * Φ Real.pi := by
    have hΦ_mono : ∀ u ∈ Set.Icc δ₁ Real.pi, Φ u ≤ Φ Real.pi := by
      intro u hu
      dsimp [Φ]
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (locInt_intervalIntegrable hφ_loc 0 u) (locInt_intervalIntegrable hφ_loc u Real.pi)]
      have hrest : 0 ≤ ∫ s in u..Real.pi, φ s :=
        intervalIntegral.integral_nonneg hu.2 fun s _ ↦ hφ_nn s
      linarith
    have hle_const :
        (∫ u in δ₁..Real.pi, poissonKernelNegDeriv r u * Φ u) ≤
          (∫ u in δ₁..Real.pi, poissonKernelNegDeriv r u) * Φ Real.pi := by
      rw [← intervalIntegral.integral_mul_const]
      refine intervalIntegral.integral_mono_on hδ₁_le_pi
        hQΦ_int_δ_pi
        ((hQ_cont.mul continuous_const).intervalIntegrable δ₁ Real.pi)
        fun u hu ↦ mul_le_mul_of_nonneg_left (hΦ_mono u hu)
          (hQ_nn u ⟨hδ₁_pos.le.trans hu.1, hu.2⟩)
    have hcollapse := poissonKernel_eq_pi_add_integral (s := δ₁) hr0 hr1
    have hΦ_pi_nn : 0 ≤ Φ Real.pi :=
      intervalIntegral.integral_nonneg Real.pi_pos.le fun s _ ↦ hφ_nn s
    nlinarith
  -- Step 4: Combine near and far bounds
  have htail_lt :
      (2 * Real.pi)⁻¹ * C_K * (RudinRCA.Chapter11.poissonKernel r δ₁ * Φ Real.pi) < ε / 2 := by
    rw [Real.dist_eq, sub_zero] at htail_j
    exact (le_abs_self _).trans_lt htail_j
  have hnear_eq : (2 * Real.pi)⁻¹ * C_K * (2 * Real.pi * η) = ε / 2 := by
    dsimp [η]
    have h2pi_ne : 2 * Real.pi ≠ 0 := Real.two_pi_pos.ne'
    have hCK_ne : C_K ≠ 0 := hCK_pos.ne'
    field_simp
  calc ‖((2 * Real.pi)⁻¹ • ∫ t in (-Real.pi)..Real.pi,
          ((1 - r ^ 2) /
            ‖(1 : ℂ) - (r : ℂ) * Complex.exp (((θ - t : ℝ) : ℂ) * Complex.I)‖ ^ 2) • g t) -
          g θ₀‖
      ≤ (2 * Real.pi)⁻¹ * ∫ t in (-Real.pi)..Real.pi,
          RudinRCA.Chapter11.poissonKernel r (θ - t) * ‖g t - g θ₀‖ := hnorm_le_1
    _ = (2 * Real.pi)⁻¹ * ∫ s in (-Real.pi)..Real.pi,
          RudinRCA.Chapter11.poissonKernel r (α - s) * ‖g (θ₀ + s) - g θ₀‖ := by
        rw [hshift_θ₀]
    _ ≤ (2 * Real.pi)⁻¹ * (C_K * ∫ s in (0 : ℝ)..Real.pi,
          RudinRCA.Chapter11.poissonKernel r s * φ s) :=
        mul_le_mul_of_nonneg_left hcone_int (inv_nonneg.mpr Real.two_pi_pos.le)
    _ = (2 * Real.pi)⁻¹ * C_K *
          (RudinRCA.Chapter11.poissonKernel r Real.pi * Φ Real.pi +
            ((∫ u in (0 : ℝ)..δ₁, poissonKernelNegDeriv r u * Φ u) +
              (∫ u in δ₁..Real.pi, poissonKernelNegDeriv r u * Φ u))) := by
        rw [hibp, hsplit_δ]
        ring
    _ ≤ (2 * Real.pi)⁻¹ * C_K *
          ((2 * Real.pi * η) + RudinRCA.Chapter11.poissonKernel r δ₁ * Φ Real.pi) := by
        have hsum_le :
            RudinRCA.Chapter11.poissonKernel r Real.pi * Φ Real.pi +
              ((∫ u in (0 : ℝ)..δ₁, poissonKernelNegDeriv r u * Φ u) +
                (∫ u in δ₁..Real.pi, poissonKernelNegDeriv r u * Φ u)) ≤
            (2 * Real.pi * η) + RudinRCA.Chapter11.poissonKernel r δ₁ * Φ Real.pi := by linarith
        exact mul_le_mul_of_nonneg_left hsum_le
          (mul_nonneg (inv_nonneg.mpr Real.two_pi_pos.le) hCK_pos.le)
    _ = (2 * Real.pi)⁻¹ * C_K * (2 * Real.pi * η) +
          (2 * Real.pi)⁻¹ * C_K * (RudinRCA.Chapter11.poissonKernel r δ₁ * Φ Real.pi) := by ring
    _ < ε / 2 + ε / 2 := by linarith [hnear_eq, htail_lt]
    _ = ε := add_halves ε

/-- Radial Poisson convergence at any symmetric Lebesgue point `θ₀`. -/
lemma poisson_radial_tendsto_of_lebesgue_pt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E} (hg_per : Function.Periodic g (2 * Real.pi))
    (hg_loc : LocallyIntegrable g MeasureTheory.volume) {θ₀ : ℝ}
    (hθ₀ : Tendsto (fun h : ℝ ↦ (2 * h)⁻¹ * ∫ y in (θ₀ - h)..(θ₀ + h), ‖g y - g θ₀‖)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ ↦ (2 * Real.pi)⁻¹ •
      ∫ t in (-Real.pi)..Real.pi,
        ((1 - r ^ 2) /
          ‖(1 : ℂ) - (r : ℂ) * Complex.exp (((θ₀ - t : ℝ) : ℂ) * Complex.I)‖ ^ 2) • g t)
      (𝓝[<] 1) (𝓝 (g θ₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [poisson_nontangential_eps_delta hg_per hg_loc hθ₀ (K := 0) le_rfl hε] with r hr
  rw [dist_eq_norm]
  exact hr θ₀ (by simp)

/-- Reusable nontangential and radial Poisson convergence theorem at any symmetric Lebesgue point
`θ₀` of a `2π`-periodic locally integrable function `g : ℝ → E` (reused in Chapter 17). -/
theorem poisson_nontangential_tendsto_of_lebesgue_pt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E} (hg_per : Function.Periodic g (2 * Real.pi))
    (hg_loc : LocallyIntegrable g MeasureTheory.volume) {θ₀ : ℝ}
    (hθ₀ : Tendsto (fun h : ℝ ↦ (2 * h)⁻¹ * ∫ y in (θ₀ - h)..(θ₀ + h), ‖g y - g θ₀‖)
      (𝓝[>] 0) (𝓝 0)) :
    (∀ {K : ℝ}, 0 ≤ K → ∀ {ι : Type*} {l : Filter ι} (r θ : ι → ℝ),
      Tendsto r l (𝓝[<] 1) →
      (∀ᶠ j in l, |θ j - θ₀| ≤ K * (1 - r j)) →
      Tendsto (fun j ↦ (2 * Real.pi)⁻¹ •
        ∫ t in (-Real.pi)..Real.pi,
          ((1 - (r j) ^ 2) /
            ‖(1 : ℂ) - ((r j : ℝ) : ℂ) * Complex.exp (((θ j - t : ℝ) : ℂ) * Complex.I)‖ ^ 2) •
            g t)
        l (𝓝 (g θ₀))) ∧
    Tendsto (fun r : ℝ ↦ (2 * Real.pi)⁻¹ •
      ∫ t in (-Real.pi)..Real.pi,
        ((1 - r ^ 2) /
          ‖(1 : ℂ) - (r : ℂ) * Complex.exp (((θ₀ - t : ℝ) : ℂ) * Complex.I)‖ ^ 2) • g t)
      (𝓝[<] 1) (𝓝 (g θ₀)) := by
  refine ⟨?_, poisson_radial_tendsto_of_lebesgue_pt hg_per hg_loc hθ₀⟩
  intro K hK ι l r_seq θ_seq hr_lim hcone
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hr_lim.eventually (poisson_nontangential_eps_delta hg_per hg_loc hθ₀ hK hε),
    hcone] with j hj hθj
  rw [dist_eq_norm]
  exact hj (θ_seq j) hθj

/-- Almost-everywhere symmetric Lebesgue-point property on `ℝ` for locally integrable functions. -/
lemma ae_symmetric_lebesgue_pt {E : Type*} [NormedAddCommGroup E]
    {g : ℝ → E} (hg_loc : LocallyIntegrable g MeasureTheory.volume) :
    ∀ᵐ θ₀ ∂MeasureTheory.volume,
      Tendsto (fun h : ℝ ↦ (2 * h)⁻¹ * ∫ y in (θ₀ - h)..(θ₀ + h), ‖g y - g θ₀‖)
        (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
    MeasureTheory.volume hg_loc 0] with θ₀ hθ₀
  have h0 := hθ₀ (fun _ : ℝ ↦ θ₀) id tendsto_id (Eventually.of_forall fun h ↦ by simp)
  refine h0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh_pos : 0 < h := hh
  dsimp only [id]
  rw [MeasureTheory.setAverage_eq, Real.closedBall_eq_Icc,
    Real.volume_real_Icc_of_le (by linarith : θ₀ - h ≤ θ₀ + h),
    show (θ₀ + h) - (θ₀ - h) = 2 * h by ring, smul_eq_mul,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : θ₀ - h ≤ θ₀ + h)]

/-- Almost-everywhere radial and nontangential Poisson convergence for any `2π`-periodic locally
integrable function `g : ℝ → E` (both on `ℝ` and restricted to `[-π, π]`). -/
theorem ae_poisson_nontangential_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E} (hg_per : Function.Periodic g (2 * Real.pi))
    (hg_loc : LocallyIntegrable g MeasureTheory.volume) :
    (∀ᵐ θ₀ ∂MeasureTheory.volume,
      (∀ {K : ℝ}, 0 ≤ K → ∀ {ι : Type*} {l : Filter ι} (r θ : ι → ℝ),
        Tendsto r l (𝓝[<] 1) →
        (∀ᶠ j in l, |θ j - θ₀| ≤ K * (1 - r j)) →
        Tendsto (fun j ↦ (2 * Real.pi)⁻¹ •
          ∫ t in (-Real.pi)..Real.pi,
            ((1 - (r j) ^ 2) /
              ‖(1 : ℂ) - ((r j : ℝ) : ℂ) * Complex.exp (((θ j - t : ℝ) : ℂ) * Complex.I)‖ ^ 2) •
              g t)
          l (𝓝 (g θ₀))) ∧
      Tendsto (fun r : ℝ ↦ (2 * Real.pi)⁻¹ •
        ∫ t in (-Real.pi)..Real.pi,
          ((1 - r ^ 2) /
            ‖(1 : ℂ) - (r : ℂ) * Complex.exp (((θ₀ - t : ℝ) : ℂ) * Complex.I)‖ ^ 2) • g t)
        (𝓝[<] 1) (𝓝 (g θ₀))) ∧
    (∀ᵐ θ₀ ∂(MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)),
      Tendsto (fun r : ℝ ↦ (2 * Real.pi)⁻¹ •
        ∫ t in (-Real.pi)..Real.pi,
          ((1 - r ^ 2) /
            ‖(1 : ℂ) - (r : ℂ) * Complex.exp (((θ₀ - t : ℝ) : ℂ) * Complex.I)‖ ^ 2) • g t)
        (𝓝[<] 1) (𝓝 (g θ₀))) := by
  have hae_leb : ∀ᵐ θ₀ ∂MeasureTheory.volume,
      Tendsto (fun h : ℝ ↦ (2 * h)⁻¹ * ∫ y in (θ₀ - h)..(θ₀ + h), ‖g y - g θ₀‖)
        (𝓝[>] 0) (𝓝 0) := ae_symmetric_lebesgue_pt hg_loc
  refine ⟨?_, ?_⟩
  · filter_upwards [hae_leb] with θ₀ hθ₀
    exact poisson_nontangential_tendsto_of_lebesgue_pt hg_per hg_loc hθ₀
  · filter_upwards [ae_restrict_of_ae hae_leb] with θ₀ hθ₀
    exact poisson_radial_tendsto_of_lebesgue_pt hg_per hg_loc hθ₀

/-- Local integrability on `ℝ` of the lift of any `circleMeasure`-integrable function on
`FourierCircle`. -/
lemma locallyIntegrable_of_integrable_circleMeasure {E : Type*} [NormedAddCommGroup E]
    {G : RudinRCA.Chapter04.FourierCircle → E}
    (hG : Integrable G RudinRCA.Chapter04.circleMeasure) :
    LocallyIntegrable (fun t : ℝ ↦ G (t : RudinRCA.Chapter04.FourierCircle))
      MeasureTheory.volume := by
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have hG_vol : Integrable G (MeasureTheory.volume : Measure RudinRCA.Chapter04.FourierCircle) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact hG.smul_measure ENNReal.ofReal_ne_top
  intro x
  have hmp := AddCircle.measurePreserving_mk (2 * Real.pi) (x - 1)
  have hint_Ioc : IntegrableOn (fun t : ℝ ↦ G (t : RudinRCA.Chapter04.FourierCircle))
      (Set.Ioc (x - 1) (x - 1 + 2 * Real.pi)) MeasureTheory.volume :=
    memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr hG_vol).comp_measurePreserving hmp)
  have hsub : Set.Ioo (x - 1) (x + 1) ⊆ Set.Ioc (x - 1) (x - 1 + 2 * Real.pi) := by
    intro y hy
    exact ⟨hy.1, hy.2.le.trans (by linarith [Real.two_le_pi])⟩
  exact ⟨Set.Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith),
    hint_Ioc.mono_set hsub⟩

/-- Circle-measure version of `ae_poisson_nontangential_tendsto` for `G : FourierCircle → E`
integrable wrt `RudinRCA.Chapter04.circleMeasure`. -/
theorem ae_poisson_nontangential_tendsto_circle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : RudinRCA.Chapter04.FourierCircle → E}
    (hG : Integrable G RudinRCA.Chapter04.circleMeasure) :
    ∀ᵐ ζ ∂RudinRCA.Chapter04.circleMeasure, ∀ θ₀ : ℝ,
      (θ₀ : RudinRCA.Chapter04.FourierCircle) = ζ →
      (∀ {K : ℝ}, 0 ≤ K → ∀ {ι : Type*} {l : Filter ι} (r θ : ι → ℝ),
        Tendsto r l (𝓝[<] 1) →
        (∀ᶠ j in l, |θ j - θ₀| ≤ K * (1 - r j)) →
        Tendsto (fun j ↦ (2 * Real.pi)⁻¹ •
          ∫ t in (-Real.pi)..Real.pi,
            ((1 - (r j) ^ 2) /
              ‖(1 : ℂ) - ((r j : ℝ) : ℂ) * Complex.exp (((θ j - t : ℝ) : ℂ) * Complex.I)‖ ^ 2) •
              G (t : RudinRCA.Chapter04.FourierCircle))
          l (𝓝 (G ζ))) ∧
      Tendsto (fun r : ℝ ↦ (2 * Real.pi)⁻¹ •
        ∫ t in (-Real.pi)..Real.pi,
          ((1 - r ^ 2) /
            ‖(1 : ℂ) - (r : ℂ) * Complex.exp (((θ₀ - t : ℝ) : ℂ) * Complex.I)‖ ^ 2) •
            G (t : RudinRCA.Chapter04.FourierCircle))
        (𝓝[<] 1) (𝓝 (G ζ)) := by
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  let g : ℝ → E := fun t ↦ G (t : RudinRCA.Chapter04.FourierCircle)
  have hg_per : Function.Periodic g (2 * Real.pi) := by
    intro t
    change G ((t + 2 * Real.pi : ℝ) : RudinRCA.Chapter04.FourierCircle) =
      G (t : RudinRCA.Chapter04.FourierCircle)
    rw [AddCircle.coe_add_period]
  have hg_loc : LocallyIntegrable g MeasureTheory.volume :=
    locallyIntegrable_of_integrable_circleMeasure hG
  let P_pt : ℝ → Prop := fun θ₀ ↦
    Tendsto (fun h : ℝ ↦ (2 * h)⁻¹ * ∫ y in (θ₀ - h)..(θ₀ + h), ‖g y - g θ₀‖)
      (𝓝[>] 0) (𝓝 0)
  have hP_per : ∀ θ₀ : ℝ, ∀ k : ℤ, P_pt (θ₀ + k * (2 * Real.pi)) ↔ P_pt θ₀ := by
    intro θ₀ k
    suffices hconv : ∀ x : ℝ, ∀ m : ℤ, P_pt x → P_pt (x + m * (2 * Real.pi)) by
      refine ⟨fun h ↦ ?_, fun h ↦ hconv θ₀ k h⟩
      simpa [Int.cast_neg, neg_mul, add_neg_cancel_right] using
        hconv (θ₀ + k * (2 * Real.pi)) (-k) h
    intro x m hx
    dsimp [P_pt] at hx ⊢
    refine hx.congr' (Eventually.of_forall fun h ↦ ?_)
    congr 1
    have hc := intervalIntegral.integral_comp_add_right
      (fun y ↦ ‖g y - g (x + m * (2 * Real.pi))‖) (m * (2 * Real.pi))
      (a := x - h) (b := x + h)
    have ha : x - h + m * (2 * Real.pi) = x + m * (2 * Real.pi) - h := by ring
    have hb : x + h + m * (2 * Real.pi) = x + m * (2 * Real.pi) + h := by ring
    rw [ha, hb] at hc
    rw [← hc]
    refine intervalIntegral.integral_congr fun y _ ↦ ?_
    have hg_xm : g (x + m * (2 * Real.pi)) = g x := by
      simpa [mul_comm] using hg_per.int_mul m x
    have hg_ym : g (y + m * (2 * Real.pi)) = g y := by
      simpa [mul_comm] using hg_per.int_mul m y
    rw [hg_ym, hg_xm]
  let e := AddCircle.measurableEquivIoc (2 * Real.pi) (-Real.pi)
  have hae_P : ∀ᵐ θ₀ ∂MeasureTheory.volume, P_pt θ₀ := ae_symmetric_lebesgue_pt hg_loc
  let E₀ : Set ℝ := toMeasurable MeasureTheory.volume {θ₀ : ℝ | ¬ P_pt θ₀}
  have hE₀_meas : MeasurableSet E₀ := measurableSet_toMeasurable _ _
  have hE₀_sub : {θ₀ : ℝ | ¬ P_pt θ₀} ⊆ E₀ := subset_toMeasurable _ _
  have hE₀_null : MeasureTheory.volume E₀ = 0 := by
    rw [measure_toMeasurable]
    exact mem_ae_iff.mp hae_P
  let B : Set RudinRCA.Chapter04.FourierCircle := (fun ζ ↦ ((e ζ : Set.Ioc _ _) : ℝ)) ⁻¹' E₀
  have hB_meas : MeasurableSet B :=
    (measurable_subtype_coe.comp e.measurable) hE₀_meas
  have hB_vol_zero : (MeasureTheory.volume : Measure RudinRCA.Chapter04.FourierCircle) B = 0 := by
    rw [← (AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi)).map_eq,
      Measure.map_apply AddCircle.measurable_mk' hB_meas,
      Measure.restrict_apply (AddCircle.measurable_mk' hB_meas)]
    refine measure_mono_null (fun x hx ↦ ?_) hE₀_null
    rcases hx with ⟨hxB, hxIoc⟩
    change ((e (x : RudinRCA.Chapter04.FourierCircle) : Set.Ioc _ _) : ℝ) ∈ E₀ at hxB
    have he_coe : (e (x : RudinRCA.Chapter04.FourierCircle) : Set.Ioc _ _) = ⟨x, hxIoc⟩ :=
      (AddCircle.equivIoc (2 * Real.pi) (-Real.pi)).right_inv ⟨x, hxIoc⟩
    rwa [he_coe] at hxB
  have hB_circle_zero : RudinRCA.Chapter04.circleMeasure B = 0 := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply, smul_eq_mul, mul_eq_zero]
      at hB_vol_zero
    have h2pi_ne : ENNReal.ofReal (2 * Real.pi) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr Real.two_pi_pos).ne'
    exact hB_vol_zero.resolve_left h2pi_ne
  have hae_B : ∀ᵐ ζ ∂RudinRCA.Chapter04.circleMeasure, ζ ∉ B :=
    compl_mem_ae_iff.mpr hB_circle_zero
  filter_upwards [hae_B] with ζ hζ θ₀ hθ₀_eq
  let x₁ : ℝ := ((e ζ : Set.Ioc _ _) : ℝ)
  have hx₁_not_E₀ : x₁ ∉ E₀ := hζ
  have hx₁_P : P_pt x₁ := by
    by_contra hnot
    exact hx₁_not_E₀ (hE₀_sub hnot)
  have hx₁_coe : (x₁ : RudinRCA.Chapter04.FourierCircle) = ζ := by
    change (AddCircle.equivIoc (2 * Real.pi) (-Real.pi)).symm (e ζ) = ζ
    exact (AddCircle.equivIoc (2 * Real.pi) (-Real.pi)).left_inv ζ
  have hcoe_eq : (θ₀ : RudinRCA.Chapter04.FourierCircle) = (x₁ : RudinRCA.Chapter04.FourierCircle) :=
    hθ₀_eq.trans hx₁_coe.symm
  obtain ⟨k, hk⟩ := QuotientAddGroup.eq.mp hcoe_eq
  have hθ₀_form : θ₀ = x₁ + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
    have hk' : (k : ℝ) * (2 * Real.pi) = -θ₀ + x₁ := by simpa [zsmul_eq_mul] using hk
    push_cast
    linarith
  have hθ₀_P : P_pt θ₀ := by
    rw [hθ₀_form]
    exact (hP_per x₁ (-k)).mpr hx₁_P
  have hlim := poisson_nontangential_tendsto_of_lebesgue_pt hg_per hg_loc hθ₀_P
  have hg_θ₀ : g θ₀ = G ζ := by
    dsimp [g]
    rw [hθ₀_eq]
  simpa only [hg_θ₀] using hlim

/-!
## 15.19: Boundary Limits and Radial Log-Modulus Means of Bounded Holomorphic Functions on `U`
-/

/-- Construction of the `2π`-periodic, Borel measurable, `M`-bounded boundary function `fStar` of
any bounded holomorphic function `f` on `Metric.ball 0 1`, via power-series Parseval (`10.22`),
Riesz–Fischer (`4.26`), Poisson representation, and `ae_poisson_nontangential_tendsto`. -/
theorem exists_radial_limit_of_bounded_holomorphic.{u} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) {M : ℝ}
    (hM : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ M) :
    ∃ fStar : ℝ → ℂ,
      Function.Periodic fStar (2 * Real.pi) ∧
      Measurable fStar ∧
      (∀ θ : ℝ, ‖fStar θ‖ ≤ M) ∧
      (∀ r : ℝ, 0 ≤ r → r < 1 → ∀ θ : ℝ,
        f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
          (2 * Real.pi)⁻¹ • ∫ t in (-Real.pi)..Real.pi,
            (RudinRCA.Chapter11.poissonKernel r (θ - t) : ℂ) * fStar t) ∧
      (∀ᵐ (θ₀ : ℝ) ∂MeasureTheory.volume,
        (∀ {K : ℝ}, 0 ≤ K → ∀ {ι : Type u} {l : Filter ι} (r θ : ι → ℝ),
          Tendsto r l (𝓝[<] 1) →
          (∀ᶠ j in l, |θ j - θ₀| ≤ K * (1 - r j)) →
          Tendsto (fun j ↦ f (((r j : ℝ) : ℂ) * Complex.exp (((θ j : ℝ) : ℂ) * Complex.I)))
            l (𝓝 (fStar θ₀))) ∧
        Tendsto (fun r : ℝ ↦ f ((r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)))
          (𝓝[<] 1) (𝓝 (fStar θ₀))) ∧
      (∀ᵐ (θ₀ : ℝ) ∂(MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)),
        Tendsto (fun r : ℝ ↦ f ((r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)))
          (𝓝[<] 1) (𝓝 (fStar θ₀))) := by
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have hM_nn : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0 (Metric.mem_ball_self zero_lt_one))
  -- Step 1: Power series of `f` on `ball 0 1` and square-summability of Taylor coefficients
  let c : ℕ → ℂ := fun n ↦ ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0)
  have hc_hasSum : ∀ z ∈ RudinRCA.Chapter10.disc (0 : ℂ) 1,
      HasSum (fun n : ℕ ↦ c n * (z - 0) ^ n) (f z) := by
    intro z hz
    convert Complex.hasSum_taylorSeries_on_ball hf hz using 2 with n
    simp only [c, smul_eq_mul]
    ring
  have hc_part_le : ∀ N : ℕ, ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 ≤ M ^ 2 := by
    intro N
    let r_seq : ℕ → ℝ := fun k ↦ 1 - 1 / ((k : ℝ) + 2)
    have hr_pos : ∀ k : ℕ, 0 < r_seq k := fun k ↦ by
      dsimp [r_seq]
      have hk : (1 : ℝ) < (k : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
      linarith [div_lt_one (by positivity : (0 : ℝ) < (k : ℝ) + 2) |>.mpr hk]
    have hr_lt : ∀ k : ℕ, r_seq k < 1 := fun k ↦ by
      dsimp [r_seq]
      linarith [div_pos zero_lt_one (by positivity : (0 : ℝ) < (k : ℝ) + 2)]
    have hr_tendsto : Tendsto r_seq atTop (𝓝 1) := by
      have hdiv : Tendsto (fun k : ℕ ↦ (1 : ℝ) / ((k : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
      simpa [r_seq] using (tendsto_const_nhds (x := (1 : ℝ))).sub hdiv
    have hle_k : ∀ k : ℕ, ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 * (r_seq k) ^ (2 * n) ≤ M ^ 2 := by
      intro k
      have hparseval := (RudinRCA.Chapter10.theorem10_22 (hr_pos k) (hr_lt k) hc_hasSum).1
      have hsum_le : ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 * (r_seq k) ^ (2 * n) ≤
          (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap 0 (r_seq k) θ)‖ ^ 2 :=
        sum_le_hasSum (Finset.range N)
          (fun n _ ↦ mul_nonneg (sq_nonneg _) (pow_nonneg (hr_pos k).le _)) hparseval
      have hcont_θ : Continuous (fun θ : ℝ ↦ ‖f (circleMap 0 (r_seq k) θ)‖ ^ 2) := by
        have hmaps : ∀ θ : ℝ, circleMap (0 : ℂ) (r_seq k) θ ∈ Metric.ball (0 : ℂ) 1 := fun θ ↦ by
          rw [Metric.mem_ball, dist_zero_right, circleMap_zero_eq, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (hr_pos k), Complex.norm_exp_ofReal_mul_I, mul_one]
          exact hr_lt k
        exact ((hf.continuousOn.comp_continuous (continuous_circleMap 0 (r_seq k)) hmaps).norm.pow 2)
      have hint_le : (∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap 0 (r_seq k) θ)‖ ^ 2) ≤
          ∫ _θ in (0 : ℝ)..2 * Real.pi, M ^ 2 := by
        refine intervalIntegral.integral_mono_on Real.two_pi_pos.le
          (hcont_θ.intervalIntegrable 0 (2 * Real.pi)) intervalIntegrable_const fun θ _ ↦ ?_
        have hmem : circleMap (0 : ℂ) (r_seq k) θ ∈ Metric.ball (0 : ℂ) 1 := by
          rw [Metric.mem_ball, dist_zero_right, circleMap_zero_eq, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (hr_pos k), Complex.norm_exp_ofReal_mul_I, mul_one]
          exact hr_lt k
        exact pow_le_pow_left₀ (norm_nonneg _) (hM _ hmem) 2
      have hconst_int : (2 * Real.pi)⁻¹ * (∫ _θ in (0 : ℝ)..2 * Real.pi, M ^ 2) = M ^ 2 := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
          inv_mul_cancel_left₀ Real.two_pi_pos.ne']
      exact hsum_le.trans ((mul_le_mul_of_nonneg_left hint_le (inv_nonneg.mpr Real.two_pi_pos.le)).trans_eq hconst_int)
    have htend_sum : Tendsto (fun k : ℕ ↦ ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 * (r_seq k) ^ (2 * n))
        atTop (𝓝 (∑ n ∈ Finset.range N, ‖c n‖ ^ 2)) := by
      have h := tendsto_finsetSum (Finset.range N) fun n _ ↦
        (tendsto_const_nhds (x := ‖c n‖ ^ 2)).mul (hr_tendsto.pow (2 * n))
      simpa only [one_pow, mul_one] using h
    exact le_of_tendsto htend_sum (Eventually.of_forall hle_k)
  have hc_sum : Summable (fun n : ℕ ↦ ‖c n‖ ^ 2) :=
    summable_of_sum_range_le (fun n ↦ sq_nonneg _) hc_part_le
  -- Step 2: Riesz–Fischer on `FourierCircle`
  let cZ : ℤ → ℂ := fun n ↦ if 0 ≤ n then c n.toNat else 0
  have hcZ_sum : Summable (fun n : ℤ ↦ ‖cZ n‖ ^ 2) := by
    rw [← (Nat.cast_injective (R := ℤ)).summable_iff]
    · refine hc_sum.congr fun m ↦ ?_
      simp [cZ]
    · intro n hn
      have hn_neg : ¬ (0 ≤ n) := fun hnn ↦ hn ⟨n.toNat, Int.toNat_of_nonneg hnn⟩
      simp [cZ, hn_neg]
  obtain ⟨F, hF_coeff⟩ := RudinRCA.Chapter04.fourier_riesz_fischer cZ hcZ_sum
  have hF_aem : AEMeasurable F RudinRCA.Chapter04.circleMeasure :=
    (Lp.aestronglyMeasurable F).aemeasurable
  let G₀ : RudinRCA.Chapter04.FourierCircle → ℂ := hF_aem.mk F
  have hG₀_meas : Measurable G₀ := hF_aem.measurable_mk
  have hFG₀_ae : (F : RudinRCA.Chapter04.FourierCircle → ℂ) =ᵐ[RudinRCA.Chapter04.circleMeasure] G₀ :=
    hF_aem.ae_eq_mk
  have hG₀_int : Integrable G₀ RudinRCA.Chapter04.circleMeasure :=
    (RudinRCA.Chapter04.circleL2_integrable F).congr hFG₀_ae
  have hG₀_coeff : ∀ n : ℤ, RudinRCA.Chapter04.circleFourierCoeff G₀ n = cZ n := by
    intro n
    rw [← hF_coeff n]
    unfold RudinRCA.Chapter04.circleFourierCoeff fourierCoeff
    refine integral_congr_ae ?_
    filter_upwards [hFG₀_ae.symm] with ζ hζ
    rw [hζ]
  -- Step 3: Poisson integral representation of `f` by `G₀`
  let g₀ : ℝ → ℂ := fun t ↦ G₀ (t : RudinRCA.Chapter04.FourierCircle)
  have hg₀_meas : Measurable g₀ := hG₀_meas.comp AddCircle.measurable_mk'
  have hg₀_per : Function.Periodic g₀ (2 * Real.pi) := by
    intro t
    change G₀ ((t + 2 * Real.pi : ℝ) : RudinRCA.Chapter04.FourierCircle) =
      G₀ (t : RudinRCA.Chapter04.FourierCircle)
    rw [AddCircle.coe_add_period]
  have hg₀_loc : LocallyIntegrable g₀ MeasureTheory.volume :=
    locallyIntegrable_of_integrable_circleMeasure hG₀_int
  have hf_poisson_g₀ : ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ θ : ℝ,
      f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
        (2 * Real.pi)⁻¹ • ∫ t in (-Real.pi)..Real.pi,
          (RudinRCA.Chapter11.poissonKernel r (θ - t) : ℂ) * g₀ t := by
    intro r hr0 hr1 θ
    let z : ℂ := (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
    have hz_ball : z ∈ RudinRCA.Chapter10.disc (0 : ℂ) 1 := by
      rw [RudinRCA.Chapter10.disc, Metric.mem_ball, dist_zero_right]
      dsimp [z]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hr1
    have hc_z : HasSum (fun m : ℕ ↦ c m * z ^ m) (f z) := by
      simpa only [sub_zero] using hc_hasSum z hz_ball
    let S : ℕ → ℝ → ℂ := fun N t ↦
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ((r : ℂ) ^ n.natAbs * Complex.exp (Complex.I * (n : ℂ) * ((θ - t : ℝ) : ℂ))) * g₀ t
    have hS_lim : ∀ t : ℝ,
        Tendsto (fun N : ℕ ↦ S N t) atTop
          (𝓝 ((RudinRCA.Chapter11.poissonKernel r (θ - t) : ℂ) * g₀ t)) := by
      intro t
      have hp := (RudinRCA.Chapter11.node11_5_hasSum_fourier hr0 hr1 (θ - t)).mul_right (g₀ t)
      exact hp.comp (Finset.tendsto_Icc_neg (R := ℤ))
    have hgeom_bound : ∀ N : ℕ,
        ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), r ^ n.natAbs ≤ 1 + 2 * (1 - r)⁻¹ := by
      intro N
      have hsym : ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), r ^ n.natAbs =
          1 + ∑ k ∈ Finset.range N,
            (r ^ ((k : ℤ) + 1).natAbs + r ^ (-((k : ℤ) + 1)).natAbs) := by
        induction N with
        | zero => simp
        | succ k ih =>
          rw [Nat.cast_succ, Finset.sum_Icc_succ_eq_add_endpoints, Finset.sum_range_succ, ih]
          ring
      rw [hsym]
      have hgeom : HasSum (fun k : ℕ ↦ r ^ k) (1 - r)⁻¹ := hasSum_geometric_of_lt_one hr0 hr1
      have hpart : ∑ k ∈ Finset.range N, r ^ k ≤ (1 - r)⁻¹ :=
        sum_le_hasSum (Finset.range N) (fun k _ ↦ pow_nonneg hr0 k) hgeom
      have hmodes : ∑ k ∈ Finset.range N,
          (r ^ ((k : ℤ) + 1).natAbs + r ^ (-((k : ℤ) + 1)).natAbs) ≤
          2 * ∑ k ∈ Finset.range N, r ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k _ ↦ ?_
        have hk1 : ((k : ℤ) + 1).natAbs = k + 1 := by omega
        have hk2 : (-((k : ℤ) + 1)).natAbs = k + 1 := by omega
        rw [hk1, hk2]
        have hpow_le : r ^ (k + 1) ≤ r ^ k := pow_le_pow_of_le_one hr0 hr1.le (Nat.le_succ k)
        linarith
      linarith
    let μ_Ioc := MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi)
    have hS_meas : ∀ N : ℕ, AEStronglyMeasurable (S N) μ_Ioc := by
      intro N
      dsimp [S]
      refine Measurable.aestronglyMeasurable (Finset.measurable_sum _ fun n _ ↦ ?_)
      refine Measurable.mul ?_ hg₀_meas
      have hcont : Continuous (fun t : ℝ ↦
          (r : ℂ) ^ n.natAbs * Complex.exp (Complex.I * (n : ℂ) * ((θ - t : ℝ) : ℂ))) := by
        fun_prop
      exact hcont.measurable
    have hbound_int : Integrable (fun t : ℝ ↦ (1 + 2 * (1 - r)⁻¹) * ‖g₀ t‖) μ_Ioc := by
      have hi := (locInt_intervalIntegrable (locInt_norm hg₀_loc) (-Real.pi) Real.pi).1
      exact hi.const_mul (1 + 2 * (1 - r)⁻¹)
    have hS_bound : ∀ N : ℕ, ∀ᵐ t ∂μ_Ioc, ‖S N t‖ ≤ (1 + 2 * (1 - r)⁻¹) * ‖g₀ t‖ := by
      intro N
      refine Eventually.of_forall fun t ↦ ?_
      dsimp [S]
      calc ‖∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            ((r : ℂ) ^ n.natAbs * Complex.exp (Complex.I * (n : ℂ) * ((θ - t : ℝ) : ℂ))) * g₀ t‖
          ≤ ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
              ‖((r : ℂ) ^ n.natAbs * Complex.exp (Complex.I * (n : ℂ) * ((θ - t : ℝ) : ℂ))) * g₀ t‖ :=
            norm_sum_le _ _
        _ = (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), r ^ n.natAbs) * ‖g₀ t‖ := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun n _ ↦ ?_
            have hexp_eq : Complex.I * (n : ℂ) * ((θ - t : ℝ) : ℂ) =
                ((((n : ℝ) * (θ - t)) : ℝ) : ℂ) * Complex.I := by
              push_cast
              ring
            rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hr0, hexp_eq, Complex.norm_exp_ofReal_mul_I, mul_one]
        _ ≤ (1 + 2 * (1 - r)⁻¹) * ‖g₀ t‖ :=
            mul_le_mul_of_nonneg_right (hgeom_bound N) (norm_nonneg _)
    have hdom := MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun t : ℝ ↦ (1 + 2 * (1 - r)⁻¹) * ‖g₀ t‖) hS_meas hbound_int hS_bound
      (Eventually.of_forall hS_lim)
    have hpi_le : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
    have hdom_ivl : Tendsto
        (fun N : ℕ ↦ (2 * Real.pi)⁻¹ • ∫ t in (-Real.pi)..Real.pi, S N t) atTop
        (𝓝 ((2 * Real.pi)⁻¹ • ∫ t in (-Real.pi)..Real.pi,
          (RudinRCA.Chapter11.poissonKernel r (θ - t) : ℂ) * g₀ t)) := by
      simp_rw [intervalIntegral.integral_of_le hpi_le]
      exact hdom.const_smul (2 * Real.pi)⁻¹
    -- Evaluate `(2 * π)⁻¹ • ∫_{-π}^π S N t dt = ∑_{m < N + 1} c m * z ^ m`
    have hSN_eval : ∀ N : ℕ,
        (2 * Real.pi)⁻¹ • (∫ t in (-Real.pi)..Real.pi, S N t) =
          ∑ m ∈ Finset.range (N + 1), c m * z ^ m := by
      intro N
      have hterm_int : ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          IntervalIntegrable
            (fun t : ℝ ↦ ((r : ℂ) ^ n.natAbs *
              Complex.exp (Complex.I * (n : ℂ) * ((θ - t : ℝ) : ℂ))) * g₀ t)
            MeasureTheory.volume (-Real.pi) Real.pi := by
        intro n _
        have hcont : Continuous (fun t : ℝ ↦
            (r : ℂ) ^ n.natAbs * Complex.exp (Complex.I * (n : ℂ) * ((θ - t : ℝ) : ℂ))) := by
          fun_prop
        have h := (locInt_intervalIntegrable hg₀_loc (-Real.pi) Real.pi).continuousOn_mul
          hcont.continuousOn
        simpa only [mul_comm] using h
      dsimp [S]
      rw [intervalIntegral.integral_finsetSum hterm_int, Finset.mul_sum]
      have hsum_Z : (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t in (-Real.pi)..Real.pi,
            ((r : ℂ) ^ n.natAbs * Complex.exp (Complex.I * (n : ℂ) * ((θ - t : ℝ) : ℂ))) * g₀ t) =
          ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            ((r : ℂ) ^ n.natAbs * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)) * cZ n := by
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        have hrew : (fun t : ℝ ↦ ((r : ℂ) ^ n.natAbs *
            Complex.exp (Complex.I * (n : ℂ) * ((θ - t : ℝ) : ℂ))) * g₀ t) =
            fun t : ℝ ↦ ((r : ℂ) ^ n.natAbs * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)) *
              (Complex.exp (-(n : ℂ) * (t : ℂ) * Complex.I) * g₀ t) := by
          funext t
          have hexp_split : Complex.exp (Complex.I * (n : ℂ) * ((θ - t : ℝ) : ℂ)) =
              Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I) *
                Complex.exp (-(n : ℂ) * (t : ℂ) * Complex.I) := by
            rw [← Complex.exp_add]
            congr 1
            push_cast
            ring
          rw [hexp_split]
          ring
        rw [hrew, intervalIntegral.integral_const_mul]
        have hfc := RudinRCA.Chapter04.circleFourierCoeff_integral G₀ n
        rw [hG₀_coeff n, one_div, Complex.real_smul] at hfc
        dsimp [g₀]
        linear_combination ((r : ℂ) ^ n.natAbs * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)) * hfc.symm
      rw [hsum_Z]
      clear hterm_int hsum_Z
      induction N with
      | zero =>
        simp only [Nat.cast_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton,
          Int.natAbs_zero, pow_zero, Int.cast_zero, zero_mul, Complex.exp_zero, mul_one, one_mul,
          zero_add, Finset.range_one]
        simp [cZ]
      | succ k ih =>
        rw [Nat.cast_succ, Finset.sum_Icc_succ_eq_add_endpoints, ih,
          Finset.sum_range_succ _ (k + 1)]
        have hneg_zero : cZ (-((k : ℤ) + 1)) = 0 := by
          dsimp [cZ]
          split_ifs with hle
          · omega
          · rfl
        have hpos_eq : cZ ((k : ℤ) + 1) = c (k + 1) := by
          have hnn : 0 ≤ (k : ℤ) + 1 := by omega
          have htonat : ((k : ℤ) + 1).toNat = k + 1 := by omega
          simp [cZ, hnn, htonat]
        have hnatabs : ((k : ℤ) + 1).natAbs = k + 1 := by omega
        have hz_pow : z ^ (k + 1) =
            (r : ℂ) ^ (k + 1) * Complex.exp (((k + 1 : ℕ) : ℂ) * (θ : ℂ) * Complex.I) := by
          dsimp [z]
          rw [mul_pow, ← Complex.exp_nat_mul]
          congr 2
          ring
        rw [hneg_zero, mul_zero, add_zero, hpos_eq, hnatabs, hz_pow]
        push_cast
        ring
    have hSN_lim_f : Tendsto (fun N : ℕ ↦ (2 * Real.pi)⁻¹ • ∫ t in (-Real.pi)..Real.pi, S N t)
        atTop (𝓝 (f z)) := by
      simp_rw [hSN_eval]
      exact hc_z.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique hSN_lim_f hdom_ivl
  -- Step 4: Nontangential & radial limits a.e., `‖g₀ θ‖ ≤ M` a.e., and truncation `fStar`
  have hker_eq : ∀ {r : ℝ}, 0 ≤ r → r < 1 → ∀ (θ t : ℝ),
      ((1 - r ^ 2) /
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (((θ - t : ℝ) : ℂ) * Complex.I)‖ ^ 2) • g₀ t =
        (RudinRCA.Chapter11.poissonKernel r (θ - t) : ℂ) * g₀ t := by
    intro r _ _ θ t
    rw [RudinRCA.Chapter11.norm_sq_one_sub_polar, Complex.real_smul]
    rfl
  have hae_g₀ := (ae_poisson_nontangential_tendsto.{0, u} hg₀_per hg₀_loc).1
  have hae_f_to_g₀ : ∀ᵐ (θ₀ : ℝ) ∂MeasureTheory.volume,
      (∀ {K : ℝ}, 0 ≤ K → ∀ {ι : Type u} {l : Filter ι} (r θ : ι → ℝ),
        Tendsto r l (𝓝[<] 1) →
        (∀ᶠ j in l, |θ j - θ₀| ≤ K * (1 - r j)) →
        Tendsto (fun j ↦ f (((r j : ℝ) : ℂ) * Complex.exp (((θ j : ℝ) : ℂ) * Complex.I)))
          l (𝓝 (g₀ θ₀))) ∧
      Tendsto (fun r : ℝ ↦ f ((r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)))
        (𝓝[<] 1) (𝓝 (g₀ θ₀)) ∧
      ‖g₀ θ₀‖ ≤ M := by
    filter_upwards [hae_g₀] with θ₀ hθ₀
    have hnt : ∀ {K : ℝ}, 0 ≤ K → ∀ {ι : Type u} {l : Filter ι} (r θ : ι → ℝ),
        Tendsto r l (𝓝[<] 1) →
        (∀ᶠ j in l, |θ j - θ₀| ≤ K * (1 - r j)) →
        Tendsto (fun j ↦ f (((r j : ℝ) : ℂ) * Complex.exp (((θ j : ℝ) : ℂ) * Complex.I)))
          l (𝓝 (g₀ θ₀)) := by
      intro K hK ι l r θ hr_lim hcone
      have hev_Ioo : ∀ᶠ j in l, r j ∈ Set.Ioo (0 : ℝ) 1 :=
        hr_lim.eventually (Ioo_mem_nhdsLT zero_lt_one)
      refine (hθ₀.1 hK r θ hr_lim hcone).congr' ?_
      filter_upwards [hev_Ioo] with j hj
      rw [hf_poisson_g₀ (r j) hj.1.le hj.2 (θ j)]
      congr 1
      refine intervalIntegral.integral_congr fun t _ ↦ ?_
      exact hker_eq hj.1.le hj.2 (θ j) t
    have hrad : Tendsto (fun r : ℝ ↦ f ((r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)))
        (𝓝[<] 1) (𝓝 (g₀ θ₀)) := by
      refine hθ₀.2.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
      rw [hf_poisson_g₀ r hr.1.le hr.2 θ₀]
      congr 1
      refine intervalIntegral.integral_congr fun t _ ↦ ?_
      exact hker_eq hr.1.le hr.2 θ₀ t
    have hnorm_le : ‖g₀ θ₀‖ ≤ M := by
      let r_seq : ℕ → ℝ := fun k ↦ 1 - 1 / ((k : ℝ) + 2)
      have hr_Ioo : ∀ k : ℕ, r_seq k ∈ Set.Ioo (0 : ℝ) 1 := fun k ↦ by
        dsimp [r_seq]
        have hk : (1 : ℝ) < (k : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
        refine ⟨?_, ?_⟩
        · linarith [div_lt_one (by positivity : (0 : ℝ) < (k : ℝ) + 2) |>.mpr hk]
        · linarith [div_pos zero_lt_one (by positivity : (0 : ℝ) < (k : ℝ) + 2)]
      have hr_lt1 : Tendsto r_seq atTop (𝓝[<] 1) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k ↦ (hr_Ioo k).2⟩
        have hdiv : Tendsto (fun k : ℕ ↦ (1 : ℝ) / ((k : ℝ) + 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop
            ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
        simpa [r_seq] using (tendsto_const_nhds (x := (1 : ℝ))).sub hdiv
      have hseq_lim : Tendsto
          (fun k : ℕ ↦ ‖f (((r_seq k : ℝ) : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I))‖)
          atTop (𝓝 ‖g₀ θ₀‖) := (hrad.comp hr_lt1).norm
      refine le_of_tendsto hseq_lim (Eventually.of_forall fun k ↦ hM _ ?_)
      rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hr_Ioo k).1, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact (hr_Ioo k).2
    exact ⟨hnt, hrad, hnorm_le⟩
  let fStar : ℝ → ℂ := fun θ ↦ if ‖g₀ θ‖ ≤ M then g₀ θ else 0
  have hfStar_per : Function.Periodic fStar (2 * Real.pi) := by
    intro θ
    simp only [fStar, hg₀_per θ]
  have hfStar_meas : Measurable fStar :=
    Measurable.ite (hg₀_meas.norm measurableSet_Iic) hg₀_meas measurable_const
  have hfStar_bdd : ∀ θ : ℝ, ‖fStar θ‖ ≤ M := by
    intro θ
    dsimp [fStar]
    split_ifs with h
    · exact h
    · simpa using hM_nn
  have hfStar_ae_eq : fStar =ᵐ[MeasureTheory.volume] g₀ := by
    filter_upwards [hae_f_to_g₀] with θ hθ
    simp [fStar, hθ.2.2]
  have hf_poisson_fStar : ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ θ : ℝ,
      f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
        (2 * Real.pi)⁻¹ • ∫ t in (-Real.pi)..Real.pi,
          (RudinRCA.Chapter11.poissonKernel r (θ - t) : ℂ) * fStar t := by
    intro r hr0 hr1 θ
    rw [hf_poisson_g₀ r hr0 hr1 θ]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hfStar_ae_eq] with t ht _
    rw [ht]
  have hae_fStar : ∀ᵐ (θ₀ : ℝ) ∂MeasureTheory.volume,
      (∀ {K : ℝ}, 0 ≤ K → ∀ {ι : Type u} {l : Filter ι} (r θ : ι → ℝ),
        Tendsto r l (𝓝[<] 1) →
        (∀ᶠ j in l, |θ j - θ₀| ≤ K * (1 - r j)) →
        Tendsto (fun j ↦ f (((r j : ℝ) : ℂ) * Complex.exp (((θ j : ℝ) : ℂ) * Complex.I)))
          l (𝓝 (fStar θ₀))) ∧
      Tendsto (fun r : ℝ ↦ f ((r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)))
        (𝓝[<] 1) (𝓝 (fStar θ₀)) := by
    filter_upwards [hae_f_to_g₀, hfStar_ae_eq] with θ₀ hθ₀ heq
    rw [heq]
    exact ⟨hθ₀.1, hθ₀.2.1⟩
  have hae_fStar_Icc : ∀ᵐ (θ₀ : ℝ) ∂(MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)),
      Tendsto (fun r : ℝ ↦ f ((r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)))
        (𝓝[<] 1) (𝓝 (fStar θ₀)) := by
    filter_upwards [ae_restrict_of_ae hae_fStar] with θ₀ hθ₀
    exact hθ₀.2
  exact ⟨fStar, hfStar_per, hfStar_meas, hfStar_bdd, hf_poisson_fStar, hae_fStar, hae_fStar_Icc⟩

/-- Helper for `15.19` and `15.23`: logarithmic form of Jensen's formula on `closedBall 0 r`
(`0 < r < R`, `h 0 ≠ 0`), expressing `circleAverage (log ‖h ·‖) 0 r` as `log ‖h 0‖` plus the
nonnegative sum over zeros in `closedBall 0 r`, together with monotonicity in `r`. -/
lemma jensen_circleAverage_mono_and_near_zero {R : ℝ} (hR : 0 < R) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 R)) (hh0 : h 0 ≠ 0) :
    (∀ r s : ℝ, 0 < r → r < s → s < R →
      Real.circleAverage (fun z ↦ Real.log ‖h z‖) 0 r ≤
        Real.circleAverage (fun z ↦ Real.log ‖h z‖) 0 s) ∧
    (∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∀ r : ℝ, 0 < r → r < ρ →
      Real.circleAverage (fun z ↦ Real.log ‖h z‖) 0 r = Real.log ‖h 0‖) := by
  have hana : AnalyticOnNhd ℂ h (Metric.ball 0 R) := hh.analyticOnNhd Metric.isOpen_ball
  have h0_mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self hR
  -- Helper expressing `circleAverage` at any `0 < t < R` via finite zero set in `closedBall 0 t`
  have hcavg_formula : ∀ t : ℝ, 0 < t → t < R →
      ∃ S : Finset ℂ,
        (∀ z : ℂ, z ∈ S ↔ z ∈ Metric.closedBall (0 : ℂ) t ∧ h z = 0) ∧
        Real.circleAverage (fun z ↦ Real.log ‖h z‖) 0 t =
          Real.log ‖h 0‖ + ∑ z ∈ S, (analyticOrderNatAt h z : ℝ) * Real.log (t / ‖z‖) := by
    intro t ht htR
    have ht_abs : |t| = t := abs_of_pos ht
    have hcl_sub : Metric.closedBall (0 : ℂ) |t| ⊆ Metric.ball (0 : ℂ) R := by
      rw [ht_abs]
      exact Metric.closedBall_subset_ball htR
    have hana_cl : AnalyticOnNhd ℂ h (Metric.closedBall (0 : ℂ) |t|) := hana.mono hcl_sub
    let D := MeromorphicOn.divisor h (Metric.closedBall (0 : ℂ) |t|)
    have hD_fin : D.support.Finite := D.finiteSupport (isCompact_closedBall 0 |t|)
    have hord_pos_iff : ∀ z ∈ Metric.closedBall (0 : ℂ) t,
        0 < analyticOrderNatAt h z ↔ h z = 0 := by
      intro z hz
      have hz_ball : z ∈ Metric.ball (0 : ℂ) R := hcl_sub (by rwa [ht_abs])
      have hne_top : analyticOrderAt h z ≠ ⊤ :=
        analyticOrderAt_ne_top_on_ball hh h0_mem hh0 hz_ball
      constructor
      · intro hpos
        have hne0 : analyticOrderAt h z ≠ 0 := by
          intro h0
          simp [analyticOrderNatAt, h0] at hpos
        exact (hana z hz_ball).analyticOrderAt_ne_zero.mp hne0
      · intro hhz
        have hne0 : analyticOrderAt h z ≠ 0 :=
          (hana z hz_ball).analyticOrderAt_ne_zero.mpr hhz
        unfold analyticOrderNatAt
        cases hval : analyticOrderAt h z with
        | top => exact (hne_top hval).elim
        | coe n =>
          have hn : n ≠ 0 := by
            intro hn0
            apply hne0
            simp [hval, hn0]
          exact Nat.pos_of_ne_zero hn
    have hzeros_fin : {z ∈ Metric.closedBall (0 : ℂ) t | h z = 0}.Finite := by
      refine hD_fin.subset fun z ⟨hz_cl, hhz⟩ ↦ ?_
      rw [Function.mem_support]
      have hz_cl' : z ∈ Metric.closedBall (0 : ℂ) |t| := by rwa [ht_abs]
      have hD_eq : D z = (analyticOrderNatAt h z : ℤ) := by
        rw [show D z = (ENat.map Nat.cast (analyticOrderAt h z)).untop₀ from
          MeromorphicOn.AnalyticOnNhd.divisor_apply hana_cl hz_cl']
        unfold analyticOrderNatAt
        cases analyticOrderAt h z <;> rfl
      rw [hD_eq]
      exact Int.natCast_ne_zero.mpr ((hord_pos_iff z hz_cl).mpr hhz).ne'
    let S : Finset ℂ := hzeros_fin.toFinset
    have hS_mem : ∀ z : ℂ, z ∈ S ↔ z ∈ Metric.closedBall (0 : ℂ) t ∧ h z = 0 :=
      fun z ↦ hzeros_fin.mem_toFinset
    have hmathlib_jensen := hana_cl.circleAverage_log_norm ht.ne' hh0
    have hD_supp_sub_S : (Function.support fun u ↦ (D u : ℝ) * Real.log (t * ‖(0 : ℂ) - u‖⁻¹)) ⊆
        (S : Set ℂ) := by
      intro u hu
      rw [Function.mem_support] at hu
      have hDu_ne : D u ≠ 0 := fun h0 ↦ by simp [h0] at hu
      by_cases hu_cl : u ∈ Metric.closedBall (0 : ℂ) |t|
      · have hu_cl' : u ∈ Metric.closedBall (0 : ℂ) t := by rwa [ht_abs] at hu_cl
        have hD_eq : D u = (analyticOrderNatAt h u : ℤ) := by
          rw [show D u = (ENat.map Nat.cast (analyticOrderAt h u)).untop₀ from
            MeromorphicOn.AnalyticOnNhd.divisor_apply hana_cl hu_cl]
          unfold analyticOrderNatAt
          cases analyticOrderAt h u <;> rfl
        rw [hD_eq] at hDu_ne
        have hpos : 0 < analyticOrderNatAt h u :=
          Nat.pos_of_ne_zero (Int.natCast_ne_zero.mp hDu_ne)
        exact (hS_mem u).mpr ⟨hu_cl', (hord_pos_iff u hu_cl').mp hpos⟩
      · exact (hDu_ne (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem D hu_cl)).elim
    have hfinsum_eq :
        (∑ᶠ u, (D u : ℝ) * Real.log (t * ‖(0 : ℂ) - u‖⁻¹)) =
          ∑ z ∈ S, (analyticOrderNatAt h z : ℝ) * Real.log (t / ‖z‖) := by
      rw [finsum_eq_sum_of_support_subset _ hD_supp_sub_S]
      refine Finset.sum_congr rfl fun z hzS ↦ ?_
      have hz_cl : z ∈ Metric.closedBall (0 : ℂ) |t| := by
        rw [ht_abs]
        exact ((hS_mem z).mp hzS).1
      have hD_eq : D z = (analyticOrderNatAt h z : ℤ) := by
        rw [show D z = (ENat.map Nat.cast (analyticOrderAt h z)).untop₀ from
          MeromorphicOn.AnalyticOnNhd.divisor_apply hana_cl hz_cl]
        unfold analyticOrderNatAt
        cases analyticOrderAt h z <;> rfl
      rw [hD_eq, Int.cast_natCast, zero_sub, norm_neg, div_eq_mul_inv]
    refine ⟨S, hS_mem, ?_⟩
    rw [hmathlib_jensen, hfinsum_eq, add_comm]
  refine ⟨?_, ?_⟩
  · intro r s hr hrs hsR
    obtain ⟨Sr, hSr_mem, hSr_eq⟩ := hcavg_formula r hr (lt_trans hrs hsR)
    obtain ⟨Ss, hSs_mem, hSs_eq⟩ := hcavg_formula s (lt_trans hr hrs) hsR
    rw [hSr_eq, hSs_eq]
    have hSr_sub : Sr ⊆ Ss := fun z hz ↦ by
      obtain ⟨hz_cl, hhz⟩ := (hSr_mem z).mp hz
      exact (hSs_mem z).mpr ⟨Metric.closedBall_subset_closedBall hrs.le hz_cl, hhz⟩
    have hsum_le1 : ∑ z ∈ Sr, (analyticOrderNatAt h z : ℝ) * Real.log (r / ‖z‖) ≤
        ∑ z ∈ Sr, (analyticOrderNatAt h z : ℝ) * Real.log (s / ‖z‖) := by
      refine Finset.sum_le_sum fun z hz ↦ ?_
      have hhz : h z = 0 := ((hSr_mem z).mp hz).2
      have hzne : z ≠ 0 := fun h0 ↦ hh0 (h0 ▸ hhz)
      have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hzne
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (div_pos hr hz_pos) (div_le_div_of_nonneg_right hrs.le hz_pos.le))
        (Nat.cast_nonneg _)
    have hsum_le2 : ∑ z ∈ Sr, (analyticOrderNatAt h z : ℝ) * Real.log (s / ‖z‖) ≤
        ∑ z ∈ Ss, (analyticOrderNatAt h z : ℝ) * Real.log (s / ‖z‖) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hSr_sub fun z hzSs _ ↦ ?_
      obtain ⟨hz_cl, hhz⟩ := (hSs_mem z).mp hzSs
      have hzne : z ≠ 0 := fun h0 ↦ hh0 (h0 ▸ hhz)
      have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hzne
      have hz_le_s : ‖z‖ ≤ s := by simpa [Metric.mem_closedBall, dist_zero_right] using hz_cl
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg ((one_le_div hz_pos).mpr hz_le_s))
    linarith
  · have hcont0 : ContinuousAt h 0 :=
      (hh.differentiableAt (Metric.isOpen_ball.mem_nhds h0_mem)).continuousAt
    obtain ⟨δ, hδ_pos, hδ_nz⟩ := Metric.mem_nhds_iff.mp (hcont0.eventually_ne hh0)
    let ρ : ℝ := min (δ / 2) R
    have hρ_pos : 0 < ρ := lt_min (half_pos hδ_pos) hR
    refine ⟨ρ, hρ_pos, min_le_right _ _, fun r hr hrρ ↦ ?_⟩
    obtain ⟨Sr, hSr_mem, hSr_eq⟩ := hcavg_formula r hr (lt_of_lt_of_le hrρ (min_le_right _ _))
    have hSr_empty : Sr = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr fun z hz ↦ ?_
      obtain ⟨hz_cl, hhz⟩ := (hSr_mem z).mp hz
      have hz_δ : z ∈ Metric.ball (0 : ℂ) δ := by
        rw [Metric.mem_closedBall, dist_zero_right] at hz_cl
        rw [Metric.mem_ball, dist_zero_right]
        have hr_lt_δ : r < δ := lt_of_lt_of_le hrρ
          ((min_le_left _ _).trans (half_lt_self hδ_pos).le)
        exact lt_of_le_of_lt hz_cl hr_lt_δ
      exact hδ_nz hz_δ hhz
    rw [hSr_eq, hSr_empty, Finset.sum_empty, add_zero]

/-- **Theorem 15.19** (Rudin, *Real and Complex Analysis*, 3rd ed., pp. 308–309):
Suppose `f ∈ H(U)` (`U = Metric.ball 0 1`) is bounded and not identically zero.
Let `μ_r := circleAverage (log ‖f ·‖) 0 r = (2π)⁻¹ ∫_{-π}^π log ‖f(r e^{iθ})‖ dθ` (`0 < r < 1`).
Then there exists a `2π`-periodic, Borel measurable, bounded radial/nontangential boundary limit
function `fStar : ℝ → ℂ` (`f(r e^{iθ}) → fStar(θ)` as `r → 1⁻` for a.e. `θ ∈ [-π, π]` and a.e. `θ ∈ ℝ`)
such that, putting `μStar := (2π)⁻¹ ∫_{-π}^π log ‖fStar θ‖ dθ` and `eLogNorm 0 = ⊥ = -∞`:
1. `0 < r < s < 1 → μ r ≤ μ s`,
2. `(μ r : EReal) → eLogNorm (f 0)` as `r → 0⁺` (covering both `f 0 ≠ 0` and `f 0 = 0`),
3. `log ‖fStar ·‖` is Lebesgue interval-integrable on `[-π, π]` and `[0, 2π]` (`log |f*| ∈ L¹(T)`),
4. `fStar θ ≠ 0` for a.e. `θ ∈ [-π, π]` and a.e. `θ ∈ ℝ` (so `eLogNorm (fStar θ) = log ‖fStar θ‖` a.e.),
5. `μ r ≤ μStar` for all `0 < r < 1`. -/
theorem theorem15_19 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hbdd : ∃ M : ℝ, ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ M)
    (hnonzero : ∃ z₀ ∈ Metric.ball (0 : ℂ) 1, f z₀ ≠ 0) :
    let μ : ℝ → ℝ := fun r ↦ Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 r
    ∃ fStar : ℝ → ℂ,
      Function.Periodic fStar (2 * Real.pi) ∧
      Measurable fStar ∧
      (∃ M : ℝ, ∀ θ : ℝ, ‖fStar θ‖ ≤ M) ∧
      (∀ᵐ (θ : ℝ) ∂(MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)),
        Tendsto (fun r : ℝ ↦ f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
          (𝓝[<] 1) (𝓝 (fStar θ))) ∧
      (∀ᵐ (θ : ℝ) ∂MeasureTheory.volume,
        Tendsto (fun r : ℝ ↦ f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
          (𝓝[<] 1) (𝓝 (fStar θ))) ∧
      (∀ r : ℝ, 0 < r → r < 1 →
        CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 r ∧
        μ r = (2 * Real.pi)⁻¹ *
          ∫ θ in (-Real.pi)..Real.pi, Real.log ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) ∧
      (∀ r s : ℝ, 0 < r → r < s → s < 1 → μ r ≤ μ s) ∧
      Tendsto (fun r : ℝ ↦ (μ r : EReal)) (𝓝[>] 0) (𝓝 (eLogNorm (f 0))) ∧
      IntervalIntegrable (fun θ : ℝ ↦ Real.log ‖fStar θ‖) MeasureTheory.volume (-Real.pi) Real.pi ∧
      IntervalIntegrable (fun θ : ℝ ↦ Real.log ‖fStar θ‖) MeasureTheory.volume 0 (2 * Real.pi) ∧
      (∀ᵐ (θ : ℝ) ∂(MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)), fStar θ ≠ 0) ∧
      (∀ᵐ (θ : ℝ) ∂MeasureTheory.volume, fStar θ ≠ 0) ∧
      ((fun θ : ℝ ↦ eLogNorm (fStar θ)) =ᵐ[
          MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)]
        (fun θ : ℝ ↦ (Real.log ‖fStar θ‖ : EReal))) ∧
      ∀ r : ℝ, 0 < r → r < 1 →
        μ r ≤ (2 * Real.pi)⁻¹ * ∫ θ in (-Real.pi)..Real.pi, Real.log ‖fStar θ‖ := by
  intro μ
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨fStar, hfStar_per, hfStar_meas, hfStar_bdd, _, hae_vol, hae_Icc⟩ :=
    exists_radial_limit_of_bounded_holomorphic.{0} hf hM
  have hae_rad_vol : ∀ᵐ (θ : ℝ) ∂MeasureTheory.volume,
      Tendsto (fun r : ℝ ↦ f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (𝓝[<] 1) (𝓝 (fStar θ)) := by
    filter_upwards [hae_vol] with θ hθ
    exact hθ.2
  -- Factor `f z = z ^ k * h z` on `ball 0 1` with `h 0 ≠ 0`
  let k : ℕ := analyticOrderNatAt f 0
  obtain ⟨h, hh_diff, hh0, hf_fac, _⟩ := disc_remove_zero_at_origin zero_lt_one hf hnonzero
  obtain ⟨hh_mono, ρ, hρ_pos, hρ_le1, hh_near0⟩ :=
    jensen_circleAverage_mono_and_near_zero zero_lt_one hh_diff hh0
  -- Decompose `μ r = k * log r + circleAverage (log ‖h ·‖) 0 r` for `0 < r < 1`
  have hμ_decomp : ∀ r : ℝ, 0 < r → r < 1 →
      CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 r ∧
      {θ ∈ Set.Icc (-Real.pi) Real.pi | f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0}.Finite ∧
      μ r = (k : ℝ) * Real.log r + Real.circleAverage (fun z ↦ Real.log ‖h z‖) 0 r := by
    intro r hr hr1
    have h18_h := (theorem15_18 hr hr1 hh_diff hh0).1
    have hana_f : AnalyticOnNhd ℂ f (Metric.ball 0 1) := hf.analyticOnNhd Metric.isOpen_ball
    have hcint_f : CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 r := by
      have hsub : Metric.sphere (0 : ℂ) |r| ⊆ Metric.ball (0 : ℂ) 1 := by
        rw [abs_of_pos hr]
        exact Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_ball hr1)
      exact (hana_f.mono hsub).meromorphicOn.circleIntegrable_log_norm
    have hfin_h := h18_h.2.2.2.1
    have hfin_f :
        {θ ∈ Set.Icc (-Real.pi) Real.pi |
          f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0}.Finite := by
      refine hfin_h.subset fun θ ⟨hθ_Icc, hf0_θ⟩ ↦ ⟨hθ_Icc, ?_⟩
      have hz_ball : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr, Complex.norm_exp_ofReal_mul_I, mul_one]
        exact hr1
      have hfac_θ := hf_fac _ hz_ball
      rw [hfac_θ] at hf0_θ
      have hzk_ne : ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ k ≠ 0 :=
        pow_ne_zero k (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (Complex.exp_ne_zero _))
      exact (mul_eq_zero.mp hf0_θ).resolve_left hzk_ne
    have hμ_eq : μ r = (k : ℝ) * Real.log r + Real.circleAverage (fun z ↦ Real.log ‖h z‖) 0 r := by
      dsimp [μ]
      rw [circleAverage_zero_eq_neg_pi_pi, circleAverage_zero_eq_neg_pi_pi]
      have hcongr : (∫ θ in (-Real.pi)..Real.pi,
            Real.log ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) =
          ∫ θ in (-Real.pi)..Real.pi,
            ((k : ℝ) * Real.log r + Real.log ‖h ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [hfin_h.countable.ae_notMem MeasureTheory.volume] with θ hθ_not hθ_uIoc
        have hpi_le : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
        rw [Set.uIoc_of_le hpi_le] at hθ_uIoc
        have hθ_Icc : θ ∈ Set.Icc (-Real.pi) Real.pi := Set.Ioc_subset_Icc_self hθ_uIoc
        have hh_ne : h ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 :=
          fun hh0_θ ↦ hθ_not ⟨hθ_Icc, hh0_θ⟩
        have hz_ball : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) 1 := by
          rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hr, Complex.norm_exp_ofReal_mul_I, mul_one]
          exact hr1
        have hnorm_z : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
            Complex.norm_exp_ofReal_mul_I, mul_one]
        rw [hf_fac _ hz_ball, norm_mul, norm_pow, hnorm_z,
          Real.log_mul (pow_pos hr k).ne' (norm_ne_zero_iff.mpr hh_ne), Real.log_pow]
      rw [hcongr, intervalIntegral.integral_add intervalIntegrable_const h18_h.2.2.1,
        intervalIntegral.integral_const, smul_eq_mul]
      have hlen : Real.pi - -Real.pi = 2 * Real.pi := by ring
      rw [hlen, mul_add, inv_mul_cancel_left₀ Real.two_pi_pos.ne']
    exact ⟨hcint_f, hfin_f, hμ_eq⟩
  -- Claim 1: Monotonicity of `μ`
  have hμ_mono : ∀ r s : ℝ, 0 < r → r < s → s < 1 → μ r ≤ μ s := by
    intro r s hr hrs hs1
    rw [(hμ_decomp r hr (lt_trans hrs hs1)).2.2, (hμ_decomp s (lt_trans hr hrs) hs1).2.2]
    exact add_le_add (mul_le_mul_of_nonneg_left (Real.log_le_log hr hrs.le) (Nat.cast_nonneg k))
      (hh_mono r s hr hrs hs1)
  -- Claim 2: `Tendsto (fun r ↦ (μ r : EReal)) (𝓝[>] 0) (𝓝 (eLogNorm (f 0)))`
  have hμ_tendsto_zero : Tendsto (fun r : ℝ ↦ (μ r : EReal)) (𝓝[>] 0) (𝓝 (eLogNorm (f 0))) := by
    have hρ_lt1 : ρ / 2 < 1 := by linarith
    have hρ2_pos : 0 < ρ / 2 := half_pos hρ_pos
    have hev_μ : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ r = (k : ℝ) * Real.log r + Real.log ‖h 0‖ := by
      filter_upwards [Ioo_mem_nhdsGT hρ2_pos] with r hr
      rw [(hμ_decomp r hr.1 (lt_trans hr.2 hρ_lt1)).2.2,
        hh_near0 r hr.1 (lt_trans hr.2 (half_lt_self hρ_pos))]
    by_cases hk0 : k = 0
    · have hf0_eq : f 0 = h 0 := by
        have h0_fac := hf_fac 0 (Metric.mem_ball_self zero_lt_one)
        change f 0 = (0 : ℂ) ^ k * h 0 at h0_fac
        simpa [hk0] using h0_fac
      have hf0_ne : f 0 ≠ 0 := hf0_eq ▸ hh0
      rw [eLogNorm_of_ne_zero hf0_ne, hf0_eq]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev_μ] with r hr
      simp [hr, hk0]
    · have hk_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
      have hf0_zero : f 0 = 0 := by
        have h0_fac := hf_fac 0 (Metric.mem_ball_self zero_lt_one)
        change f 0 = (0 : ℂ) ^ k * h 0 at h0_fac
        rw [h0_fac, zero_pow hk0, zero_mul]
      rw [hf0_zero, eLogNorm_zero]
      have hlog_atBot : Tendsto Real.log (𝓝[>] 0) atBot := by
        rw [Filter.tendsto_atBot]
        intro B
        filter_upwards [Ioo_mem_nhdsGT (Real.exp_pos B)] with r hr
        calc Real.log r ≤ Real.log (Real.exp B) := Real.log_le_log hr.1 hr.2.le
          _ = B := Real.log_exp B
      have hlin_atBot : Tendsto (fun r : ℝ ↦ (k : ℝ) * Real.log r + Real.log ‖h 0‖)
          (𝓝[>] 0) atBot :=
        (hlog_atBot.const_mul_atBot hk_pos).atBot_add tendsto_const_nhds
      have hμ_atBot : Tendsto μ (𝓝[>] 0) atBot :=
        hlin_atBot.congr' (hev_μ.mono fun r hr ↦ hr.symm)
      have hcoe_bot : Tendsto (fun x : ℝ ↦ (x : EReal)) atBot (𝓝 (⊥ : EReal)) := by
        rw [tendsto_order]
        refine ⟨fun b hb ↦ (not_lt_bot hb).elim, fun b hb ↦ ?_⟩
        induction b using EReal.rec with
        | bot => exact (lt_irrefl _ hb).elim
        | coe c =>
          filter_upwards [Filter.eventually_lt_atBot c] with x hx
          exact EReal.coe_lt_coe_iff.mpr hx
        | top => exact Eventually.of_forall fun x ↦ EReal.coe_lt_top x
      exact hcoe_bot.comp hμ_atBot
  -- Claims 3, 4, 5 via Fatou's lemma on `ψ(w) = log M₁ - log ‖w‖` (`ψ 0 = ⊤`)
  let M₁ : ℝ := max M 1
  have hM₁_ge1 : 1 ≤ M₁ := le_max_right M 1
  have hM₁_pos : 0 < M₁ := zero_lt_one.trans_le hM₁_ge1
  have hlogM₁_nn : 0 ≤ Real.log M₁ := Real.log_nonneg hM₁_ge1
  have hf_le_M₁ : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ M₁ :=
    fun z hz ↦ (hM z hz).trans (le_max_left M 1)
  have hfStar_le_M₁ : ∀ θ : ℝ, ‖fStar θ‖ ≤ M₁ :=
    fun θ ↦ (hfStar_bdd θ).trans (le_max_left M 1)
  let ψ : ℂ → ℝ≥0∞ := fun w ↦ if w = 0 then ⊤ else ENNReal.ofReal (Real.log M₁ - Real.log ‖w‖)
  have hψ_meas : Measurable ψ :=
    Measurable.ite (measurableSet_singleton 0) measurable_const
      (ENNReal.measurable_ofReal.comp
        (measurable_const.sub (Real.measurable_log.comp continuous_norm.measurable)))
  have hψ_seq_tendsto : ∀ (w_seq : ℕ → ℂ) (w : ℂ),
      Tendsto w_seq atTop (𝓝 w) → Tendsto (fun n : ℕ ↦ ψ (w_seq n)) atTop (𝓝 (ψ w)) := by
    intro w_seq w hw_lim
    by_cases hw0 : w = 0
    · subst hw0
      have hψ0 : ψ 0 = ⊤ := by simp [ψ]
      rw [hψ0, tendsto_order]
      refine ⟨fun b hb ↦ ?_, fun b hb ↦ (not_top_lt hb).elim⟩
      let B : ℝ := b.toReal + 1
      have hb_lt_B : b < ENNReal.ofReal B := by
        rw [← ENNReal.ofReal_toReal hb.ne]
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by dsimp [B]; linarith)
      have hev_norm : ∀ᶠ n in atTop, ‖w_seq n‖ < Real.exp (Real.log M₁ - B) := by
        have h0_lim : Tendsto (fun n ↦ ‖w_seq n‖) atTop (𝓝 0) := by
          simpa using hw_lim.norm
        exact h0_lim.eventually (Iio_mem_nhds (Real.exp_pos _))
      filter_upwards [hev_norm] with n hn
      dsimp [ψ]
      split_ifs with hwn0
      · exact hb
      · have hpos_wn : 0 < ‖w_seq n‖ := norm_pos_iff.mpr hwn0
        have hlog_lt : Real.log ‖w_seq n‖ < Real.log M₁ - B := by
          calc Real.log ‖w_seq n‖ < Real.log (Real.exp (Real.log M₁ - B)) :=
                Real.log_lt_log hpos_wn hn
            _ = Real.log M₁ - B := Real.log_exp _
        have hB_le : B ≤ Real.log M₁ - Real.log ‖w_seq n‖ := by linarith
        exact lt_of_lt_of_le hb_lt_B (ENNReal.ofReal_le_ofReal hB_le)
    · have hψw : ψ w = ENNReal.ofReal (Real.log M₁ - Real.log ‖w‖) := by simp [ψ, hw0]
      rw [hψw]
      have hlog_lim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (Real.log M₁ - Real.log ‖w_seq n‖))
          atTop (𝓝 (ENNReal.ofReal (Real.log M₁ - Real.log ‖w‖))) :=
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          (tendsto_const_nhds.sub
            ((Real.continuousAt_log (norm_ne_zero_iff.mpr hw0)).tendsto.comp hw_lim.norm))
      refine hlog_lim.congr' ?_
      filter_upwards [hw_lim.eventually (isOpen_ne.mem_nhds hw0)] with n hwn
      simp [ψ, hwn]
  let ν := MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)
  let r_seq : ℕ → ℝ := fun n ↦ 1 - 1 / ((n : ℝ) + 2)
  have hr_Ioo : ∀ n : ℕ, r_seq n ∈ Set.Ioo (0 : ℝ) 1 := fun n ↦ by
    dsimp [r_seq]
    have hn : (1 : ℝ) < (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    exact ⟨by linarith [div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 2) |>.mpr hn],
      by linarith [div_pos zero_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 2)]⟩
  have hr_lt1 : Tendsto r_seq atTop (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n ↦ (hr_Ioo n).2⟩
    have hdiv : Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
    simpa [r_seq] using (tendsto_const_nhds (x := (1 : ℝ))).sub hdiv
  let g_seq : ℕ → ℝ → ℝ≥0∞ := fun n θ ↦
    ψ (f (((r_seq n : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
  have hg_seq_meas : ∀ n : ℕ, AEMeasurable (g_seq n) ν := by
    intro n
    have hmaps : ∀ θ : ℝ, ((r_seq n : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈
        Metric.ball (0 : ℂ) 1 := fun θ ↦ by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hr_Ioo n).1, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact (hr_Ioo n).2
    have hcont_f : Continuous (fun θ : ℝ ↦
        f (((r_seq n : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) :=
      hf.continuousOn.comp_continuous (by fun_prop) hmaps
    exact (hψ_meas.comp hcont_f.measurable).aemeasurable
  have hpi_le : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hg_seq_lint : ∀ n : ℕ,
      ∫⁻ θ, g_seq n θ ∂ν = ENNReal.ofReal (2 * Real.pi * (Real.log M₁ - μ (r_seq n))) := by
    intro n
    obtain ⟨hcint_n, hfin_n, _⟩ := hμ_decomp (r_seq n) (hr_Ioo n).1 (hr_Ioo n).2
    have hint_log_n : IntervalIntegrable
        (fun θ : ℝ ↦ Real.log ‖f (((r_seq n : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)
        MeasureTheory.volume (-Real.pi) Real.pi :=
      (circleIntegrable_iff_intervalIntegrable_neg_pi_pi _ (r_seq n)).mp hcint_n
    let φ_n : ℝ → ℝ := fun θ ↦
      Real.log M₁ - Real.log ‖f (((r_seq n : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖
    have hφ_n_intOn : IntegrableOn φ_n (Set.Icc (-Real.pi) Real.pi) MeasureTheory.volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hpi_le).mp
        (intervalIntegrable_const.sub hint_log_n)
    have hφ_n_nn : ∀ θ : ℝ, 0 ≤ φ_n θ := by
      intro θ
      dsimp [φ_n]
      by_cases hfz : f (((r_seq n : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0
      · simp [hfz, hlogM₁_nn]
      · have hz_ball : ((r_seq n : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈
            Metric.ball (0 : ℂ) 1 := by
          rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (hr_Ioo n).1, Complex.norm_exp_ofReal_mul_I, mul_one]
          exact (hr_Ioo n).2
        have hle : Real.log ‖f (((r_seq n : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
            Real.log M₁ :=
          Real.log_le_log (norm_pos_iff.mpr hfz) (hf_le_M₁ _ hz_ball)
        linarith
    have hae_eq_n : g_seq n =ᵐ[ν] fun θ ↦ ENNReal.ofReal (φ_n θ) := by
      have hae_not_zero : ∀ᵐ (θ : ℝ) ∂ν,
          f (((r_seq n : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 := by
        rw [ae_restrict_iff' measurableSet_Icc]
        filter_upwards [hfin_n.countable.ae_notMem MeasureTheory.volume] with θ hθ_not hθ_Icc h0
        exact hθ_not ⟨hθ_Icc, h0⟩
      filter_upwards [hae_not_zero] with θ hθ
      simp [g_seq, ψ, φ_n, hθ]
    rw [lintegral_congr_ae hae_eq_n,
      ← ofReal_integral_eq_lintegral_ofReal hφ_n_intOn (Eventually.of_forall hφ_n_nn)]
    congr 1
    change (∫ θ in Set.Icc (-Real.pi) Real.pi, φ_n θ) = 2 * Real.pi * (Real.log M₁ - μ (r_seq n))
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi_le]
    dsimp [φ_n, μ]
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint_log_n,
      intervalIntegral.integral_const, smul_eq_mul, circleAverage_zero_eq_neg_pi_pi]
    have hlen : Real.pi - -Real.pi = 2 * Real.pi := by ring
    rw [hlen, mul_sub, mul_inv_cancel_left₀ Real.two_pi_pos.ne']
  have hfatou_bound : ∀ r : ℝ, 0 < r → r < 1 →
      ∫⁻ θ, ψ (fStar θ) ∂ν ≤ ENNReal.ofReal (2 * Real.pi * (Real.log M₁ - μ r)) := by
    intro r hr hr1
    have hae_liminf : (fun θ ↦ ψ (fStar θ)) =ᵐ[ν]
        fun θ ↦ Filter.liminf (fun n : ℕ ↦ g_seq n θ) atTop := by
      filter_upwards [hae_Icc] with θ hθ
      exact (hψ_seq_tendsto _ (fStar θ) (hθ.comp hr_lt1)).liminf_eq.symm
    have h1 : ∫⁻ θ, ψ (fStar θ) ∂ν ≤ Filter.liminf (fun n : ℕ ↦ ∫⁻ θ, g_seq n θ ∂ν) atTop := by
      rw [lintegral_congr_ae hae_liminf]
      exact MeasureTheory.lintegral_liminf_le' hg_seq_meas
    refine h1.trans ?_
    have hev_r_lt : ∀ᶠ n in atTop, r < r_seq n := by
      have hr_tendsto1 : Tendsto r_seq atTop (𝓝 1) := tendsto_nhdsWithin_iff.mp hr_lt1 |>.1
      exact hr_tendsto1.eventually (Ioi_mem_nhds hr1)
    have hev_le : ∀ᶠ n in atTop,
        ∫⁻ θ, g_seq n θ ∂ν ≤ ENNReal.ofReal (2 * Real.pi * (Real.log M₁ - μ r)) := by
      filter_upwards [hev_r_lt] with n hn
      rw [hg_seq_lint n]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (sub_le_sub_left (hμ_mono r (r_seq n) hr hn (hr_Ioo n).2) _) Real.two_pi_pos.le)
    exact Filter.liminf_le_of_le (by isBoundedDefault) fun b hb ↦ by
      obtain ⟨n, hn⟩ := (hb.and hev_le).exists
      exact hn.1.trans hn.2
  -- Claim 4: `fStar ≠ 0` a.e. on `Icc (-π) π` and on `ℝ`
  have hψ_lint_lt_top : ∫⁻ θ, ψ (fStar θ) ∂ν < ⊤ :=
    lt_of_le_of_lt (hfatou_bound (1 / 2) (by norm_num) (by norm_num)) ENNReal.ofReal_lt_top
  have hae_fStar_nz_Icc : ∀ᵐ (θ : ℝ) ∂ν, fStar θ ≠ 0 := by
    have hae_lt := ae_lt_top (hψ_meas.comp hfStar_meas) hψ_lint_lt_top.ne
    filter_upwards [hae_lt] with θ hθ h0
    simp [ψ, h0] at hθ
  have hae_fStar_nz_vol : ∀ᵐ (θ : ℝ) ∂MeasureTheory.volume, fStar θ ≠ 0 := by
    rw [ae_iff]
    change MeasureTheory.volume {θ : ℝ | ¬ fStar θ ≠ 0} = 0
    simp only [not_ne_iff]
    have hIcc_zero : MeasureTheory.volume ({θ : ℝ | fStar θ = 0} ∩ Set.Icc (-Real.pi) Real.pi) = 0 := by
      have h0_ae : (MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi))
          {θ : ℝ | ¬ fStar θ ≠ 0} = 0 := ae_iff.mp hae_fStar_nz_Icc
      simp only [not_ne_iff] at h0_ae
      have hmeas0 : MeasurableSet {θ : ℝ | fStar θ = 0} := hfStar_meas (measurableSet_singleton 0)
      rwa [Measure.restrict_apply hmeas0] at h0_ae
    have hcover : {θ : ℝ | fStar θ = 0} ⊆
        ⋃ m : ℤ, {θ : ℝ | fStar θ = 0} ∩
          Set.Icc (-Real.pi + (m : ℝ) * (2 * Real.pi)) (Real.pi + (m : ℝ) * (2 * Real.pi)) := by
      intro θ hθ
      rw [Set.mem_iUnion]
      let m : ℤ := ⌊(θ + Real.pi) / (2 * Real.pi)⌋
      refine ⟨m, hθ, ?_, ?_⟩
      · have hle := Int.floor_le ((θ + Real.pi) / (2 * Real.pi))
        have hmul := (le_div_iff₀ Real.two_pi_pos).mp hle
        dsimp [m]
        linarith
      · have hlt := Int.lt_floor_add_one ((θ + Real.pi) / (2 * Real.pi))
        have hmul := (div_lt_iff₀ Real.two_pi_pos).mp hlt
        dsimp [m]
        linarith
    refine measure_mono_null hcover (measure_iUnion_null fun m ↦ ?_)
    let shift : ℝ := (m : ℝ) * (2 * Real.pi)
    have hpre : {θ : ℝ | fStar θ = 0} ∩ Set.Icc (-Real.pi + shift) (Real.pi + shift) =
        (fun θ : ℝ ↦ θ + (-shift)) ⁻¹'
          ({θ : ℝ | fStar θ = 0} ∩ Set.Icc (-Real.pi) Real.pi) := by
      ext θ
      change (fStar θ = 0 ∧ -Real.pi + shift ≤ θ ∧ θ ≤ Real.pi + shift) ↔
        (fStar (θ + -shift) = 0 ∧ -Real.pi ≤ θ + -shift ∧ θ + -shift ≤ Real.pi)
      have hper_m : fStar (θ + -shift) = fStar θ := by
        have hper := hfStar_per.int_mul (-m) θ
        simpa [shift, mul_comm] using hper
      rw [hper_m]
      exact ⟨fun ⟨h0, h1, h2⟩ ↦ ⟨h0, by linarith, by linarith⟩,
        fun ⟨h0, h1, h2⟩ ↦ ⟨h0, by linarith, by linarith⟩⟩
    rw [hpre, measure_preimage_add_right]
    exact hIcc_zero
  have hae_eLog_fStar : (fun θ : ℝ ↦ eLogNorm (fStar θ)) =ᵐ[ν]
      (fun θ : ℝ ↦ (Real.log ‖fStar θ‖ : EReal)) := by
    filter_upwards [hae_fStar_nz_Icc] with θ hθ
    exact eLogNorm_of_ne_zero hθ
  -- Claim 3: `IntervalIntegrable (fun θ ↦ Real.log ‖fStar θ‖)` on `(-π)..π` and `0..(2π)`
  let φStar : ℝ → ℝ := fun θ ↦ Real.log M₁ - Real.log ‖fStar θ‖
  have hφStar_nn : ∀ θ : ℝ, 0 ≤ φStar θ := by
    intro θ
    dsimp [φStar]
    by_cases h0 : fStar θ = 0
    · simp [h0, hlogM₁_nn]
    · have hle : Real.log ‖fStar θ‖ ≤ Real.log M₁ :=
        Real.log_le_log (norm_pos_iff.mpr h0) (hfStar_le_M₁ θ)
      linarith
  have hφStar_enorm_ae : (fun θ : ℝ ↦ ‖φStar θ‖ₑ) =ᵐ[ν] fun θ : ℝ ↦ ψ (fStar θ) := by
    filter_upwards [hae_fStar_nz_Icc] with θ hθ
    rw [Real.enorm_eq_ofReal (hφStar_nn θ)]
    simp [ψ, φStar, hθ]
  have hφStar_int : Integrable φStar ν := by
    refine ⟨(measurable_const.sub (Real.measurable_log.comp hfStar_meas.norm)).aestronglyMeasurable, ?_⟩
    change ∫⁻ θ, ‖φStar θ‖ₑ ∂ν < ⊤
    rw [lintegral_congr_ae hφStar_enorm_ae]
    exact hψ_lint_lt_top
  have hlog_fStar_intOn :
      IntegrableOn (fun θ : ℝ ↦ Real.log ‖fStar θ‖)
        (Set.Icc (-Real.pi) Real.pi) MeasureTheory.volume := by
    have hconst_int : Integrable (fun _ : ℝ ↦ Real.log M₁) ν :=
      integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)
    have hsub : Integrable (fun θ : ℝ ↦ Real.log M₁ - φStar θ) ν := hconst_int.sub hφStar_int
    exact hsub.congr (Eventually.of_forall fun θ ↦ by dsimp [φStar]; ring)
  have hint_fStar_neg_pi_pi :
      IntervalIntegrable (fun θ : ℝ ↦ Real.log ‖fStar θ‖)
        MeasureTheory.volume (-Real.pi) Real.pi :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hpi_le).mpr hlog_fStar_intOn
  have hint_fStar_0_2pi :
      IntervalIntegrable (fun θ : ℝ ↦ Real.log ‖fStar θ‖)
        MeasureTheory.volume 0 (2 * Real.pi) := by
    have hper_log : Function.Periodic (fun θ : ℝ ↦ Real.log ‖fStar θ‖) (2 * Real.pi) :=
      fun θ ↦ by simp [hfStar_per θ]
    have hiff := hper_log.intervalIntegrable_iff (t₁ := -Real.pi) (t₂ := 0)
    have h1 : -Real.pi + 2 * Real.pi = Real.pi := by ring
    have h2 : (0 : ℝ) + 2 * Real.pi = 2 * Real.pi := zero_add _
    rw [h1, h2] at hiff
    exact hiff.mp hint_fStar_neg_pi_pi
  -- Claim 5: `∀ r ∈ (0, 1), μ r ≤ μStar`
  have hμ_le_μStar : ∀ r : ℝ, 0 < r → r < 1 →
      μ r ≤ (2 * Real.pi)⁻¹ * ∫ θ in (-Real.pi)..Real.pi, Real.log ‖fStar θ‖ := by
    intro r hr hr1
    have hμ_le_logM₁ : μ r ≤ Real.log M₁ := by
      dsimp [μ]
      rw [circleAverage_zero_eq_neg_pi_pi]
      have hcint_r := (hμ_decomp r hr hr1).1
      have hint_r := (circleIntegrable_iff_intervalIntegrable_neg_pi_pi _ r).mp hcint_r
      have hle_int : (∫ θ in (-Real.pi)..Real.pi,
            Real.log ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) ≤
          ∫ _θ in (-Real.pi)..Real.pi, Real.log M₁ := by
        refine intervalIntegral.integral_mono_on hpi_le hint_r intervalIntegrable_const fun θ _ ↦ ?_
        by_cases h0 : f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0
        · simp [h0, hlogM₁_nn]
        · have hz_ball : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) 1 := by
            rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hr, Complex.norm_exp_ofReal_mul_I, mul_one]
            exact hr1
          exact Real.log_le_log (norm_pos_iff.mpr h0) (hf_le_M₁ _ hz_ball)
      have hconst_eval : (2 * Real.pi)⁻¹ * (∫ _θ in (-Real.pi)..Real.pi, Real.log M₁) =
          Real.log M₁ := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        have hlen : Real.pi - -Real.pi = 2 * Real.pi := by ring
        rw [hlen, inv_mul_cancel_left₀ Real.two_pi_pos.ne']
      exact (mul_le_mul_of_nonneg_left hle_int (inv_nonneg.mpr Real.two_pi_pos.le)).trans_eq
        hconst_eval
    have hofReal_eq : ENNReal.ofReal (∫ θ, φStar θ ∂ν) = ∫⁻ θ, ψ (fStar θ) ∂ν := by
      rw [ofReal_integral_eq_lintegral_ofReal hφStar_int (Eventually.of_forall hφStar_nn)]
      refine lintegral_congr_ae ?_
      filter_upwards [hae_fStar_nz_Icc] with θ hθ
      simp [ψ, φStar, hθ]
    have hrhs_nn : 0 ≤ 2 * Real.pi * (Real.log M₁ - μ r) :=
      mul_nonneg Real.two_pi_pos.le (sub_nonneg.mpr hμ_le_logM₁)
    have hle_real : ∫ θ, φStar θ ∂ν ≤ 2 * Real.pi * (Real.log M₁ - μ r) := by
      refine (ENNReal.ofReal_le_ofReal_iff hrhs_nn).mp ?_
      rw [hofReal_eq]
      exact hfatou_bound r hr hr1
    have hint_φStar_eval : ∫ θ, φStar θ ∂ν =
        2 * Real.pi * Real.log M₁ - ∫ θ in (-Real.pi)..Real.pi, Real.log ‖fStar θ‖ := by
      change (∫ θ in Set.Icc (-Real.pi) Real.pi, φStar θ) = _
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi_le]
      dsimp [φStar]
      rw [intervalIntegral.integral_sub intervalIntegrable_const hint_fStar_neg_pi_pi,
        intervalIntegral.integral_const, smul_eq_mul]
      have hlen : Real.pi - -Real.pi = 2 * Real.pi := by ring
      rw [hlen]
    rw [hint_φStar_eval] at hle_real
    have h2pi_pos : 0 < 2 * Real.pi := Real.two_pi_pos
    have hdiv := (le_div_iff₀' h2pi_pos).mpr (by linarith :
      2 * Real.pi * μ r ≤ ∫ θ in (-Real.pi)..Real.pi, Real.log ‖fStar θ‖)
    simpa only [div_eq_inv_mul] using hdiv
  refine ⟨fStar, hfStar_per, hfStar_meas, ⟨M, hfStar_bdd⟩, hae_Icc, hae_rad_vol,
    fun r hr hr1 ↦ ⟨(hμ_decomp r hr hr1).1, circleAverage_zero_eq_neg_pi_pi _ r⟩,
    hμ_mono, hμ_tendsto_zero, hint_fStar_neg_pi_pi, hint_fStar_0_2pi,
    hae_fStar_nz_Icc, hae_fStar_nz_vol, hae_eLog_fStar, hμ_le_μStar⟩

/-! ### 15.20: Zero-Counting Bounds for Entire Functions (`entireMaxModulus`, `entireZeroCount`, `theorem15_20`) -/

open scoped Classical

/-- Maximum modulus `M(r) = sup_{|z| ≤ r} ‖f(z)‖` of `f : ℂ → ℂ` on the closed disc of radius `r`
(Rudin 15.20). For entire `f` and `r ≥ 0`, `entireMaxModulus_eq_sphere` shows this agrees with
`sup_{|z| = r} ‖f(z)‖`. -/
def entireMaxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z : ℂ ↦ ‖f z‖) '' Metric.closedBall (0 : ℂ) r)

/-- Total zero count `n(r)` (with multiplicity) of `f : ℂ → ℂ` in the closed disc
`Metric.closedBall 0 r` (Rudin 15.20). -/
def entireZeroCount (f : ℂ → ℂ) (r : ℝ) : ℕ :=
  ∑ᶠ z : ℂ, if z ∈ Metric.closedBall (0 : ℂ) r then analyticOrderNatAt f z else 0

lemma le_entireMaxModulus {f : ℂ → ℂ} {r : ℝ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) r))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) r) :
    ‖f z‖ ≤ entireMaxModulus f r := by
  have hbdd : BddAbove ((fun w : ℂ ↦ ‖f w‖) '' Metric.closedBall (0 : ℂ) r) :=
    ((isCompact_closedBall (0 : ℂ) r).image_of_continuousOn hf.norm).bddAbove
  exact le_csSup hbdd (Set.mem_image_of_mem _ hz)

lemma entireMaxModulus_le_of_forall_closedBall {f : ℂ → ℂ} {r B : ℝ}
    (hr : 0 ≤ r) (hB : ∀ z ∈ Metric.closedBall (0 : ℂ) r, ‖f z‖ ≤ B) :
    entireMaxModulus f r ≤ B := by
  refine csSup_le ((Metric.nonempty_closedBall.mpr hr).image _) ?_
  rintro _ ⟨z, hz, rfl⟩
  exact hB z hz

/-- Maximum Modulus equality for `entireMaxModulus`: for entire `f` and `r ≥ 0` (in particular
`r > 0`), the supremum of `‖f‖` on `Metric.closedBall 0 r` equals the supremum on
`Metric.sphere 0 r`. -/
theorem entireMaxModulus_eq_sphere {f : ℂ → ℂ} {r : ℝ}
    (hf : Differentiable ℂ f) (hr : 0 ≤ r) :
    entireMaxModulus f r = sSup ((fun z : ℂ ↦ ‖f z‖) '' Metric.sphere (0 : ℂ) r) := by
  rcases eq_or_lt_of_le hr with rfl | hr_pos
  · simp [entireMaxModulus, Metric.closedBall_zero, Metric.sphere_zero]
  · have hsp_ne : (Metric.sphere (0 : ℂ) r).Nonempty :=
      ⟨(r : ℂ), by simp [abs_of_pos hr_pos]⟩
    have hbdd_cl : BddAbove ((fun w : ℂ ↦ ‖f w‖) '' Metric.closedBall (0 : ℂ) r) :=
      ((isCompact_closedBall (0 : ℂ) r).image_of_continuousOn
        hf.continuous.continuousOn.norm).bddAbove
    have hbdd_sp : BddAbove ((fun w : ℂ ↦ ‖f w‖) '' Metric.sphere (0 : ℂ) r) :=
      hbdd_cl.mono (Set.image_mono Metric.sphere_subset_closedBall)
    apply le_antisymm
    · refine entireMaxModulus_le_of_forall_closedBall hr fun z hz ↦ ?_
      have hz_cl : z ∈ closure (Metric.ball (0 : ℂ) r) := by
        rwa [closure_ball (0 : ℂ) hr_pos.ne']
      refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
        ⟨hf.differentiableOn, hf.continuous.continuousOn⟩ (fun w hw ↦ ?_) hz_cl
      rw [frontier_ball (0 : ℂ) hr_pos.ne'] at hw
      exact le_csSup hbdd_sp (Set.mem_image_of_mem _ hw)
    · exact csSup_le_csSup hbdd_cl (hsp_ne.image _)
        (Set.image_mono Metric.sphere_subset_closedBall)

lemma entireMaxModulus_le_of_forall_sphere {f : ℂ → ℂ} {r B : ℝ}
    (hf : Differentiable ℂ f) (hr : 0 ≤ r)
    (hB : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ B) :
    entireMaxModulus f r ≤ B := by
  rw [entireMaxModulus_eq_sphere hf hr]
  have hsp_ne : (Metric.sphere (0 : ℂ) r).Nonempty :=
    ⟨(r : ℂ), by simp [abs_of_nonneg hr]⟩
  refine csSup_le (hsp_ne.image _) ?_
  rintro _ ⟨z, hz, rfl⟩
  exact hB z hz

/-- Bridge between `entireZeroCount f r` and `∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 |r|) u`
for entire `f` and `r ≥ 0`. -/
lemma entireZeroCount_cast_eq_finsum_divisor {f : ℂ → ℂ} {r : ℝ}
    (hf : Differentiable ℂ f) (hr : 0 ≤ r) :
    (entireZeroCount f r : ℤ) =
      ∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) |r|) u := by
  have hr_abs : |r| = r := abs_of_nonneg hr
  let D := MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) |r|)
  have hana : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) |r|) :=
    fun z _ ↦ hf.analyticAt z
  have hD_eq : ∀ u : ℂ,
      D u = ((if u ∈ Metric.closedBall (0 : ℂ) r then analyticOrderNatAt f u else 0 : ℕ) : ℤ) := by
    intro u
    by_cases hu : u ∈ Metric.closedBall (0 : ℂ) r
    · have hu_abs : u ∈ Metric.closedBall (0 : ℂ) |r| := by rwa [hr_abs]
      simp only [hu, ↓reduceIte]
      rw [show D u = (ENat.map Nat.cast (analyticOrderAt f u)).untop₀ from
        MeromorphicOn.AnalyticOnNhd.divisor_apply hana hu_abs]
      unfold analyticOrderNatAt
      cases analyticOrderAt f u <;> rfl
    · have hu_abs : u ∉ Metric.closedBall (0 : ℂ) |r| := by rwa [hr_abs]
      simp only [hu, ↓reduceIte, Int.ofNat_zero]
      exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem D hu_abs
  have hsupp_fin : (Function.support fun u : ℂ ↦
      if u ∈ Metric.closedBall (0 : ℂ) r then analyticOrderNatAt f u else 0).Finite := by
    refine (D.finiteSupport (isCompact_closedBall 0 |r|)).subset fun u hu ↦ ?_
    rw [Function.mem_support] at hu ⊢
    rw [hD_eq u]
    exact Int.natCast_ne_zero.mpr hu
  unfold entireZeroCount
  rw [show (∑ᶠ u : ℂ, MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) |r|) u) = ∑ᶠ u : ℂ,
      ((if u ∈ Metric.closedBall (0 : ℂ) r then analyticOrderNatAt f u else 0 : ℕ) : ℤ) from
      finsum_congr hD_eq]
  exact map_finsum (Nat.castAddMonoidHom ℤ) hsupp_fin

/-- Helper: `analyticOrderAt (fun z : ℂ ↦ z ^ k) 0 = k`. -/
lemma analyticOrderAt_pow_origin (k : ℕ) :
    analyticOrderAt (fun z : ℂ ↦ z ^ k) 0 = (k : ℕ∞) := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.cast_zero]
    exact analyticAt_const.analyticOrderAt_eq_zero.mpr one_ne_zero
  | succ m ih =>
    have h_eq : (fun z : ℂ ↦ z ^ (m + 1)) =
        (fun z : ℂ ↦ z ^ m) * (fun z : ℂ ↦ z - 0) := by
      funext z
      simp [pow_succ]
    have hana1 : AnalyticAt ℂ (fun z : ℂ ↦ z ^ m) 0 := by fun_prop
    have hana2 : AnalyticAt ℂ (fun z : ℂ ↦ z - (0 : ℂ)) 0 := by fun_prop
    rw [h_eq, analyticOrderAt_mul hana1 hana2, ih]
    have hid : analyticOrderAt (fun z : ℂ ↦ z - (0 : ℂ)) 0 = 1 := by
      simp only [sub_zero]
      exact analyticOrderAt_id (𝕜 := ℂ)
    rw [hid, Nat.cast_add, Nat.cast_one]

/-- Helper: cardinality of `(Finset.Icc (-M : ℤ) M).erase 0` is `2 * M`. -/
private lemma card_Icc_neg_erase_zero (M : ℕ) :
    ((Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0).card = 2 * M := by
  have hcard_int : ∑ _x ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (1 : ℤ) = 2 * (M : ℤ) + 1 := by
    induction M with
    | zero => simp
    | succ m ih =>
      rw [Nat.cast_succ,
        Finset.sum_Icc_succ_eq_add_endpoints (f := fun _ : ℤ ↦ (1 : ℤ)) (N := m), ih]
      omega
  have hcard_Icc : (Finset.Icc (-(M : ℤ)) (M : ℤ)).card = 2 * M + 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hcard_int
    exact_mod_cast hcard_int
  have h0_mem : (0 : ℤ) ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [Finset.card_erase_of_mem h0_mem, hcard_Icc]
  omega

/-- **15.20 (Entire Zero-Count Bounds and Sharpness)**:
- `(a)` For entire `f` with `f 0 = 1` and `r > 0`,
  `(entireZeroCount f r : ℝ) * Real.log 2 ≤ Real.log (entireMaxModulus f (2 * r))`.
- `(b)` Under exponential order growth `entireMaxModulus f r ≤ Real.exp (A * r ^ k)` for `r ≥ R₀`
  (`k > 0`, `R₀ > 0`), `limsup_{r → ∞} log n(r) / log r ≤ k` (both in `EReal` with `-∞` when
  `n(r) = 0`, and in `ℝ` whenever `n(r) ≥ 1` eventually).
- `(c)` Sharpness (`k : ℕ`, `1 ≤ k`, `SCOPING-G.md` Caution 5): states and proves all zero-count,
  multiplicity, growth, and asymptotic-exponent claims for **both** Rudin's unnormalized function
  `f_k z = 1 - Complex.exp (z ^ k)` (which has a zero of multiplicity `k` at `0`) **and** its
  origin-zero-removed normalized entire function
  `h_k z = if z = 0 then 1 else (Complex.exp (z ^ k) - 1) / z ^ k` (along with `g_k = -h_k`). -/
theorem theorem15_20 :
    -- (a) Jensen zero-counting inequality for entire `f` with `f 0 = 1`
    (∀ {f : ℂ → ℂ}, Differentiable ℂ f → f 0 = 1 → ∀ r : ℝ, 0 < r →
      (entireZeroCount f r : ℝ) * Real.log 2 ≤ Real.log (entireMaxModulus f (2 * r))) ∧
    -- (b) Asymptotic zero-exponent bound from `M(r) ≤ exp(A r^k)`
    (∀ {f : ℂ → ℂ} {k A R₀ : ℝ}, Differentiable ℂ f → f 0 = 1 →
      0 < k → 0 < R₀ →
      (∀ r : ℝ, R₀ ≤ r → entireMaxModulus f r ≤ Real.exp (A * r ^ k)) →
      Filter.limsup (fun r : ℝ ↦
          if entireZeroCount f r = 0 then (⊥ : EReal)
          else ((Real.log (entireZeroCount f r) / Real.log r : ℝ) : EReal))
        Filter.atTop ≤ (k : EReal) ∧
      ((∀ᶠ r : ℝ in Filter.atTop, 1 ≤ entireZeroCount f r) →
        Filter.limsup (fun r : ℝ ↦ Real.log (entireZeroCount f r) / Real.log r)
          Filter.atTop ≤ k)) ∧
    -- (c) Sharpness for every integer `k ≥ 1` (both `f_k` and origin-normalized `h_k`, `g_k = -h_k`)
    (∀ (k : ℕ), 1 ≤ k →
      let f_k : ℂ → ℂ := fun z ↦ 1 - Complex.exp (z ^ k)
      let h_k : ℂ → ℂ := fun z ↦ if z = 0 then 1 else (Complex.exp (z ^ k) - 1) / z ^ k
      let g_k : ℂ → ℂ := fun z ↦ if z = 0 then -1 else (1 - Complex.exp (z ^ k)) / z ^ k
      Differentiable ℂ f_k ∧
      analyticOrderNatAt f_k 0 = k ∧
      (∀ r : ℝ, 1 ≤ r → entireMaxModulus f_k r ≤ Real.exp (2 * r ^ k)) ∧
      (∀ r : ℝ, 0 < r → entireZeroCount f_k r = k + 2 * k * Nat.floor (r ^ k / (2 * Real.pi))) ∧
      Tendsto (fun r : ℝ ↦ Real.log (entireZeroCount f_k r) / Real.log r)
        Filter.atTop (𝓝 (k : ℝ)) ∧
      Differentiable ℂ h_k ∧
      h_k 0 = 1 ∧
      (∀ z : ℂ, g_k z = -h_k z ∧ f_k z = z ^ k * g_k z) ∧
      (∀ r : ℝ, 1 ≤ r → entireMaxModulus h_k r ≤ Real.exp (2 * r ^ k)) ∧
      (∀ r : ℝ, 0 < r → entireZeroCount h_k r = 2 * k * Nat.floor (r ^ k / (2 * Real.pi))) ∧
      Tendsto (fun r : ℝ ↦ Real.log (entireZeroCount h_k r) / Real.log r)
        Filter.atTop (𝓝 (k : ℝ))) := by
  have hpart_a : ∀ {f : ℂ → ℂ}, Differentiable ℂ f → f 0 = 1 → ∀ r : ℝ, 0 < r →
      (entireZeroCount f r : ℝ) * Real.log 2 ≤ Real.log (entireMaxModulus f (2 * r)) := by
    intro f hf hf0 r hr
    let M := entireMaxModulus f (2 * r)
    have h0_mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) (2 * r) :=
      Metric.mem_closedBall_self (by positivity)
    have h1_le_M : 1 ≤ M := by
      have h := le_entireMaxModulus hf.continuous.continuousOn h0_mem
      simpa [hf0] using h
    have hr_abs : |r| = r := abs_of_pos hr
    have h2r_abs : |2 * r| = 2 * r := abs_of_pos (by positivity)
    have hana : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) |2 * r|) :=
      fun z _ ↦ hf.analyticAt z
    have hf0_ne : f 0 ≠ 0 := by simp [hf0]
    have hsp_bound : ∀ z ∈ Metric.sphere (0 : ℂ) |2 * r|, ‖f z‖ ≤ M := by
      intro z hz
      rw [h2r_abs] at hz
      exact le_entireMaxModulus hf.continuous.continuousOn (Metric.sphere_subset_closedBall hz)
    have hjensen := AnalyticOnNhd.sum_divisor_le
      (by rw [hr_abs]; exact hr) (by rw [hr_abs, h2r_abs]; linarith)
      h1_le_M hana hf0_ne hsp_bound
    rw [← entireZeroCount_cast_eq_finsum_divisor hf hr.le, Int.cast_natCast,
      hf0, norm_one, div_one, mul_div_cancel_right₀ (2 : ℝ) hr.ne'] at hjensen
    exact (le_div_iff₀ (Real.log_pos one_lt_two)).mp hjensen
  refine ⟨hpart_a, ?_, ?_⟩
  · -- Part (b): limsup bound under `entireMaxModulus f r ≤ exp (A * r ^ k)`
    intro f k A R₀ hf hf0 hk hR₀ hgrowth
    let C : ℝ := max ((A * (2 : ℝ) ^ k) / Real.log 2) 1
    have h1_le_C : 1 ≤ C := le_max_right _ _
    have hC_pos : 0 < C := zero_lt_one.trans_le h1_le_C
    -- Pointwise upper bound on `Real.log (entireZeroCount f r) / Real.log r` when `n(r) ≥ 1`
    have hratio_le : ∀ r : ℝ, max R₀ 2 ≤ r → 1 ≤ entireZeroCount f r →
        Real.log (entireZeroCount f r) / Real.log r ≤ Real.log C / Real.log r + k := by
      intro r hr hn_ge
      have hr2 : 2 ≤ r := (le_max_right R₀ 2).trans hr
      have hr_pos : 0 < r := by linarith
      have hr_gt1 : 1 < r := by linarith
      have hlogr_pos : 0 < Real.log r := Real.log_pos hr_gt1
      have h2r_ge : R₀ ≤ 2 * r := by
        have hR₀_le : R₀ ≤ r := (le_max_left R₀ 2).trans hr
        linarith
      have h0_mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) (2 * r) :=
        Metric.mem_closedBall_self (by positivity)
      have h1_le_M : 1 ≤ entireMaxModulus f (2 * r) := by
        have h := le_entireMaxModulus hf.continuous.continuousOn h0_mem
        simpa [hf0] using h
      have hM_pos : 0 < entireMaxModulus f (2 * r) := zero_lt_one.trans_le h1_le_M
      have hlogM_le : Real.log (entireMaxModulus f (2 * r)) ≤ (A * (2 : ℝ) ^ k) * r ^ k := by
        have hle := Real.log_le_log hM_pos (hgrowth (2 * r) h2r_ge)
        rw [Real.log_exp, Real.mul_rpow two_pos.le hr_pos.le] at hle
        linarith
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hn_le : (entireZeroCount f r : ℝ) ≤ C * r ^ k := by
        have ha := (le_div_iff₀ hlog2_pos).mpr (hpart_a hf hf0 r hr_pos)
        have hb : Real.log (entireMaxModulus f (2 * r)) / Real.log 2 ≤
            ((A * (2 : ℝ) ^ k) / Real.log 2) * r ^ k := by
          have h := div_le_div_of_nonneg_right hlogM_le hlog2_pos.le
          simpa only [mul_div_right_comm] using h
        have hrk_pos : 0 < r ^ k := Real.rpow_pos_of_pos hr_pos k
        exact ha.trans (hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hrk_pos.le))
      have hn_pos : 0 < (entireZeroCount f r : ℝ) := by exact_mod_cast hn_ge
      have hlog_n : Real.log (entireZeroCount f r) ≤ Real.log C + k * Real.log r := by
        have hrk_pos : 0 < r ^ k := Real.rpow_pos_of_pos hr_pos k
        have h := Real.log_le_log hn_pos hn_le
        rwa [Real.log_mul hC_pos.ne' hrk_pos.ne', Real.log_rpow hr_pos] at h
      calc
        Real.log (entireZeroCount f r) / Real.log r
            ≤ (Real.log C + k * Real.log r) / Real.log r :=
          div_le_div_of_nonneg_right hlog_n hlogr_pos.le
        _ = Real.log C / Real.log r + k := by
          rw [add_div, mul_div_cancel_right₀ k hlogr_pos.ne']
    have hupper_tendsto : Tendsto (fun r : ℝ ↦ Real.log C / Real.log r + k)
        Filter.atTop (𝓝 k) := by
      have hdiv0 : Tendsto (fun r : ℝ ↦ Real.log C * (Real.log r)⁻¹) Filter.atTop (𝓝 0) := by
        simpa using tendsto_const_nhds.mul Real.tendsto_log_atTop.inv_tendsto_atTop
      simpa only [div_eq_mul_inv, zero_add] using hdiv0.add tendsto_const_nhds
    constructor
    · -- EReal limsup
      let uE : ℝ → EReal := fun r ↦
        if entireZeroCount f r = 0 then (⊥ : EReal)
        else ((Real.log (entireZeroCount f r) / Real.log r : ℝ) : EReal)
      have hle_eps : ∀ ε : ℝ, 0 < ε → Filter.limsup uE Filter.atTop ≤ ((k + ε : ℝ) : EReal) := by
        intro ε hε
        refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
        have hev_up := hupper_tendsto.eventually (Iio_mem_nhds (by linarith : k < k + ε))
        filter_upwards [eventually_ge_atTop (max R₀ 2), hev_up] with r hr hlt
        dsimp [uE]
        by_cases h0 : entireZeroCount f r = 0
        · simp [h0]
        · simp only [h0, ↓reduceIte]
          exact_mod_cast (hratio_le r hr (Nat.one_le_iff_ne_zero.mpr h0)).trans (le_of_lt hlt)
      generalize hL : Filter.limsup uE Filter.atTop = L
      rw [hL] at hle_eps
      induction L using EReal.rec with
      | bot => exact bot_le
      | top =>
        exact absurd (top_le_iff.mp (hle_eps 1 zero_lt_one)) (EReal.coe_ne_top _)
      | coe x =>
        rw [EReal.coe_le_coe_iff]
        exact le_of_forall_pos_le_add fun ε hε ↦ EReal.coe_le_coe_iff.mp (hle_eps ε hε)
    · -- Real limsup under `∀ᶠ r in atTop, 1 ≤ entireZeroCount f r`
      intro hev_ge1
      let uR : ℝ → ℝ := fun r ↦ Real.log (entireZeroCount f r) / Real.log r
      have hev_nn : ∀ᶠ r : ℝ in Filter.atTop, 0 ≤ uR r := by
        filter_upwards [eventually_ge_atTop (2 : ℝ), hev_ge1] with r hr hn
        have hlogr : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
        have hlogn : 0 ≤ Real.log (entireZeroCount f r) :=
          Real.log_nonneg (by exact_mod_cast hn)
        exact div_nonneg hlogn hlogr
      have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop uR := by
        refine ⟨0, fun a ha ↦ ?_⟩
        have ha' : ∀ᶠ r : ℝ in Filter.atTop, uR r ≤ a := eventually_map.mp ha
        obtain ⟨r, hr0, hra⟩ := (hev_nn.and ha').exists
        exact hr0.trans hra
      refine le_of_forall_pos_le_add fun ε hε ↦ ?_
      refine Filter.limsup_le_of_le hcobdd ?_
      have hev_up := hupper_tendsto.eventually (Iio_mem_nhds (by linarith : k < k + ε))
      filter_upwards [eventually_ge_atTop (max R₀ 2), hev_ge1, hev_up] with r hr hn hlt
      exact (hratio_le r hr hn).trans (le_of_lt hlt)
  · -- Part (c): Sharpness example `f_k z = 1 - exp(z^k)` and origin-normalized `h_k`
    intro k hk
    have hk_pos : 0 < k := by omega
    let f_k : ℂ → ℂ := fun z ↦ 1 - Complex.exp (z ^ k)
    let h_k : ℂ → ℂ := fun z ↦ if z = 0 then 1 else (Complex.exp (z ^ k) - 1) / z ^ k
    let g_k : ℂ → ℂ := fun z ↦ if z = 0 then -1 else (1 - Complex.exp (z ^ k)) / z ^ k
    -- Construct entire `ψ` with `exp w - 1 = w * ψ w` and `ψ 0 = 1`
    let φ : ℂ → ℂ := fun w ↦ Complex.exp w - 1
    have hφ_diff : Differentiable ℂ φ := differentiable_exp.sub (differentiable_const 1)
    have hφ_ne : φ ≠ 0 := by
      intro h0
      have h1 : Complex.exp (1 : ℂ) - 1 = 0 := congrFun h0 1
      have hnorm : ‖Complex.exp (1 : ℂ)‖ = 1 := by rw [sub_eq_zero.mp h1, norm_one]
      rw [Complex.norm_exp, Complex.one_re] at hnorm
      have hgt : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      linarith
    have hφ_ord : analyticOrderNatAt φ 0 = 1 := by
      have hcomp : φ = (fun u : ℂ ↦ u - 1) ∘ Complex.exp := rfl
      have hderiv_exp : deriv Complex.exp 0 ≠ 0 := by
        rw [(Complex.hasDerivAt_exp 0).deriv, Complex.exp_zero]
        exact one_ne_zero
      have haord : analyticOrderAt φ 0 = 1 := by
        rw [hcomp, analyticOrderAt_comp_of_deriv_ne_zero (differentiable_exp.analyticAt 0)
          hderiv_exp, Complex.exp_zero]
        simp
      simp [analyticOrderNatAt, haord]
    obtain ⟨ψ, hψ_diff, _, hψ_fac⟩ :=
      entire_remove_zero_at_origin hφ_diff hφ_ne
    have hψ_fac1 : ∀ w : ℂ, Complex.exp w - 1 = w * ψ w := by
      intro w
      simpa [φ, hφ_ord] using hψ_fac w
    have hψ0 : ψ 0 = 1 := by
      have hd1 : HasDerivAt φ 1 0 := by
        simpa [φ, Complex.exp_zero] using (Complex.hasDerivAt_exp 0).sub_const (1 : ℂ)
      have hd2 : HasDerivAt (fun w : ℂ ↦ w * ψ w) (1 * ψ 0 + 0 * deriv ψ 0) 0 :=
        (hasDerivAt_id 0).mul hψ_diff.differentiableAt.hasDerivAt
      have heq_fn : φ = fun w : ℂ ↦ w * ψ w := funext hψ_fac1
      rw [heq_fn] at hd1
      have hu := hd2.unique hd1
      simpa using hu
    have hh_eq_ψ : ∀ z : ℂ, h_k z = ψ (z ^ k) := by
      intro z
      by_cases hz : z = 0
      · subst z
        simp [h_k, zero_pow hk_pos.ne', hψ0]
      · have hzk : z ^ k ≠ 0 := pow_ne_zero k hz
        simp [h_k, hz, hψ_fac1 (z ^ k), mul_div_cancel_left₀ _ hzk]
    have hh_diff : Differentiable ℂ h_k := by
      rw [show h_k = fun z : ℂ ↦ ψ (z ^ k) from funext hh_eq_ψ]
      exact hψ_diff.comp (differentiable_id.pow k)
    have hh0 : h_k 0 = 1 := by simp [h_k]
    have hf_diff : Differentiable ℂ f_k :=
      (differentiable_const 1).sub (differentiable_exp.comp (differentiable_id.pow k))
    have hgk_rel : ∀ z : ℂ, g_k z = -h_k z ∧ f_k z = z ^ k * g_k z := by
      intro z
      by_cases hz : z = 0
      · subst z
        simp [g_k, h_k, f_k, zero_pow hk_pos.ne']
      · have hzk : z ^ k ≠ 0 := pow_ne_zero k hz
        refine ⟨?_, ?_⟩
        · simp only [g_k, h_k, hz, ↓reduceIte]
          ring
        · simp only [g_k, f_k, hz, ↓reduceIte]
          exact (mul_div_cancel₀ _ hzk).symm
    have hfk_eq : f_k = -((fun z : ℂ ↦ z ^ k) * h_k) := by
      funext z
      have h := (hgk_rel z)
      change f_k z = -(z ^ k * h_k z)
      rw [h.2, h.1, mul_neg]
    -- Multiplicities of `f_k` and `h_k` at `0` and away from `0`
    have hh_ord0 : analyticOrderAt h_k 0 = 0 :=
      (hh_diff.analyticAt 0).analyticOrderAt_eq_zero.mpr (by simp [hh0])
    have hh_nat_ord0 : analyticOrderNatAt h_k 0 = 0 := by simp [analyticOrderNatAt, hh_ord0]
    have hf_ord0 : analyticOrderAt f_k 0 = (k : ℕ∞) := by
      have hpow_ana0 : AnalyticAt ℂ (fun z : ℂ ↦ z ^ k) 0 := by fun_prop
      rw [hfk_eq, analyticOrderAt_neg,
        analyticOrderAt_mul hpow_ana0 (hh_diff.analyticAt 0),
        analyticOrderAt_pow_origin k, hh_ord0, add_zero]
    have hf_nat_ord0 : analyticOrderNatAt f_k 0 = k := by simp [analyticOrderNatAt, hf_ord0]
    have hord_nz : ∀ {z : ℂ}, z ≠ 0 →
        analyticOrderNatAt f_k z = (if Complex.exp (z ^ k) = 1 then 1 else 0) ∧
        analyticOrderNatAt h_k z = (if Complex.exp (z ^ k) = 1 then 1 else 0) := by
      intro z hz
      let E : ℂ → ℂ := fun w ↦ Complex.exp (w ^ k)
      have hE_hd : HasDerivAt E (Complex.exp (z ^ k) * ((k : ℂ) * z ^ (k - 1))) z :=
        (hasDerivAt_pow k z).cexp
      have hE_deriv_ne : deriv E z ≠ 0 := by
        rw [hE_hd.deriv]
        exact mul_ne_zero (Complex.exp_ne_zero _)
          (mul_ne_zero (Nat.cast_ne_zero.mpr hk_pos.ne') (pow_ne_zero _ hz))
      have hf_comp : f_k = (fun u : ℂ ↦ 1 - u) ∘ E := rfl
      have hE_ana : AnalyticAt ℂ E z := by unfold E; fun_prop
      have hf_aord : analyticOrderAt f_k z = if Complex.exp (z ^ k) = 1 then 1 else 0 := by
        rw [hf_comp, analyticOrderAt_comp_of_deriv_ne_zero hE_ana hE_deriv_ne]
        have hneg_lin : (fun u : ℂ ↦ 1 - u) = -(fun u : ℂ ↦ u - 1) := by
          funext u
          simp only [Pi.neg_apply]
          ring
        rw [hneg_lin, analyticOrderAt_neg]
        by_cases hexp1 : E z = 1
        · simp [E] at hexp1 ⊢
          rw [hexp1]
          simp
        · have hne : E z ≠ 1 := hexp1
          simp only [E] at hne ⊢
          simp only [hne, ↓reduceIte]
          exact analyticOrderAt_id_sub_const_of_ne hne
      have hpow_ana : AnalyticAt ℂ (fun w : ℂ ↦ w ^ k) z := by fun_prop
      have hpow_ord0 : analyticOrderAt (fun w : ℂ ↦ w ^ k) z = 0 :=
        hpow_ana.analyticOrderAt_eq_zero.mpr (pow_ne_zero k hz)
      have hh_aord : analyticOrderAt h_k z = analyticOrderAt f_k z := by
        rw [hfk_eq, analyticOrderAt_neg,
          analyticOrderAt_mul hpow_ana (hh_diff.analyticAt z),
          hpow_ord0, zero_add]
      have hnat : analyticOrderNatAt f_k z = if Complex.exp (z ^ k) = 1 then 1 else 0 := by
        unfold analyticOrderNatAt
        rw [hf_aord]
        split_ifs <;> simp
      have hh_nat : analyticOrderNatAt h_k z = analyticOrderNatAt f_k z := by
        simp [analyticOrderNatAt, hh_aord]
      exact ⟨hnat, hh_nat.trans hnat⟩
    -- Growth bounds `entireMaxModulus f_k r ≤ exp(2 r^k)` and `entireMaxModulus h_k r ≤ exp(2 r^k)`
    have hfk_bound_cl : ∀ {r : ℝ}, 1 ≤ r → ∀ z ∈ Metric.closedBall (0 : ℂ) r,
        ‖f_k z‖ ≤ Real.exp (2 * r ^ k) := by
      intro r hr z hz
      have hzr : ‖z‖ ≤ r := mem_closedBall_zero_iff.mp hz
      have hr_nn : 0 ≤ r := by linarith
      have hzk_le : ‖z ^ k‖ ≤ r ^ k := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg z) hzr k
      have hrk_ge1 : 1 ≤ r ^ k := one_le_pow₀ hr
      have h2_le_exp : (2 : ℝ) ≤ Real.exp (r ^ k) := by
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        exact h2.trans (Real.exp_le_exp.mpr hrk_ge1)
      calc
        ‖f_k z‖ = ‖1 - Complex.exp (z ^ k)‖ := rfl
        _ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (z ^ k)‖ := norm_sub_le _ _
        _ = 1 + Real.exp (z ^ k).re := by rw [norm_one, Complex.norm_exp]
        _ ≤ 1 + Real.exp ‖z ^ k‖ := by gcongr; exact Complex.re_le_norm _
        _ ≤ 1 + Real.exp (r ^ k) := by gcongr
        _ ≤ 2 * Real.exp (r ^ k) := by linarith [Real.one_le_exp (by positivity : 0 ≤ r ^ k)]
        _ ≤ Real.exp (r ^ k) * Real.exp (r ^ k) :=
          mul_le_mul_of_nonneg_right h2_le_exp (Real.exp_pos _).le
        _ = Real.exp (2 * r ^ k) := by rw [← Real.exp_add]; ring_nf
    have hfk_growth : ∀ r : ℝ, 1 ≤ r → entireMaxModulus f_k r ≤ Real.exp (2 * r ^ k) :=
      fun r hr ↦ entireMaxModulus_le_of_forall_closedBall (by linarith) (hfk_bound_cl hr)
    have hhk_growth : ∀ r : ℝ, 1 ≤ r → entireMaxModulus h_k r ≤ Real.exp (2 * r ^ k) := by
      intro r hr
      refine entireMaxModulus_le_of_forall_sphere hh_diff (by linarith) fun z hz ↦ ?_
      have hzr : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
      have hz0 : z ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hzr
        linarith
      have hzk_ge1 : 1 ≤ ‖z ^ k‖ := by
        rw [norm_pow, hzr]
        exact one_le_pow₀ hr
      have hle_fk : ‖h_k z‖ ≤ ‖f_k z‖ := by
        simp only [h_k, f_k, hz0, ↓reduceIte, norm_div, norm_sub_rev (1 : ℂ)]
        exact div_le_self (norm_nonneg _) hzk_ge1
      exact hle_fk.trans (hfk_bound_cl hr z (Metric.sphere_subset_closedBall hz))
    -- Exact zero counts of `h_k` and `f_k` in `closedBall 0 r` (`r > 0`)
    have hzero_counts : ∀ r : ℝ, 0 < r →
        entireZeroCount h_k r = 2 * k * Nat.floor (r ^ k / (2 * Real.pi)) ∧
        entireZeroCount f_k r = k + 2 * k * Nat.floor (r ^ k / (2 * Real.pi)) := by
      intro r hr
      let M : ℕ := Nat.floor (r ^ k / (2 * Real.pi))
      let I_M : Finset ℤ := (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0
      let w_m : ℤ → ℂ := fun m ↦ (m : ℂ) * (2 * Real.pi * Complex.I)
      have hw_ne : ∀ {m : ℤ}, m ≠ 0 → w_m m ≠ 0 :=
        fun hm ↦ mul_ne_zero (Int.cast_ne_zero.mpr hm) Complex.two_pi_I_ne_zero
      have hroots : ∀ (m : ℤ) (hm : m ≠ 0),
          {z : ℂ | z ^ k = w_m m}.Finite ∧ {z : ℂ | z ^ k = w_m m}.ncard = k := by
        intro m hm
        have h31 := (RudinRCA.Chapter10.theorem10_31 hk_pos).1 (w_m m) (hw_ne hm)
        exact ⟨h31.2.2.2.1, h31.2.2.2.2⟩
      let fib : ℤ → Finset ℂ := fun m ↦
        if hm : m ≠ 0 then (hroots m hm).1.toFinset else ∅
      have hfib_mem : ∀ {m : ℤ} (hm : m ≠ 0) (z : ℂ), z ∈ fib m ↔ z ^ k = w_m m := by
        intro m hm z
        dsimp [fib]
        split_ifs with h
        · exact (hm h).elim
        · exact (hroots m h).1.mem_toFinset
      have hfib_card : ∀ m ∈ I_M, (fib m).card = k := by
        intro m hm
        have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
        have hcoe : ((fib m : Finset ℂ) : Set ℂ) = {z : ℂ | z ^ k = w_m m} := by
          ext z
          exact hfib_mem hm0 z
        rw [← (hroots m hm0).2, ← hcoe, Set.ncard_coe_finset]
      have hfib_disj : (I_M : Set ℤ).PairwiseDisjoint fib := by
        intro m₁ hm₁ m₂ hm₂ hne
        change Disjoint (fib m₁) (fib m₂)
        rw [Finset.disjoint_left]
        intro z hz₁ hz₂
        have hm₁0 : m₁ ≠ 0 := (Finset.mem_erase.mp hm₁).1
        have hm₂0 : m₂ ≠ 0 := (Finset.mem_erase.mp hm₂).1
        have hz₁' : z ^ k = w_m m₁ := (hfib_mem hm₁0 z).mp hz₁
        have hz₂' : z ^ k = w_m m₂ := (hfib_mem hm₂0 z).mp hz₂
        have heq : (m₁ : ℂ) * (2 * Real.pi * Complex.I) =
            (m₂ : ℂ) * (2 * Real.pi * Complex.I) := hz₁'.symm.trans hz₂'
        have hcast := mul_right_cancel₀ Complex.two_pi_I_ne_zero heq
        exact hne (Int.cast_injective hcast)
      let S : Finset ℂ := I_M.biUnion fib
      have hS_card : S.card = 2 * k * M := by
        rw [Finset.card_biUnion hfib_disj, Finset.sum_congr rfl hfib_card,
          Finset.sum_const, card_Icc_neg_erase_zero M, smul_eq_mul]
        ring
      have hmem_S_iff : ∀ z : ℂ,
          z ∈ S ↔ (z ∈ Metric.closedBall (0 : ℂ) r ∧ z ≠ 0 ∧ Complex.exp (z ^ k) = 1) := by
        intro z
        rw [Finset.mem_biUnion]
        constructor
        · rintro ⟨m, hmI, hzm⟩
          have hm0 : m ≠ 0 := (Finset.mem_erase.mp hmI).1
          have hm_Icc := Finset.mem_Icc.mp (Finset.mem_erase.mp hmI).2
          have hzk : z ^ k = w_m m := (hfib_mem hm0 z).mp hzm
          have hz0 : z ≠ 0 := by
            intro h0
            rw [h0, zero_pow hk_pos.ne'] at hzk
            exact hw_ne hm0 hzk.symm
          have hexp1 : Complex.exp (z ^ k) = 1 :=
            Complex.exp_eq_one_iff.mpr ⟨m, hzk⟩
          have hnorm_zk : ‖z‖ ^ k ≤ r ^ k := by
            have hn1 : ‖z‖ ^ k = |(m : ℝ)| * (2 * Real.pi) := by
              have h := congrArg norm hzk
              simp only [w_m, norm_pow, norm_mul, Complex.norm_intCast, Complex.norm_ofNat,
                Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I,
                mul_one] at h
              exact h
            have hm_le_M : |(m : ℝ)| ≤ (M : ℝ) := by
              refine abs_le.mpr ⟨?_, ?_⟩
              · exact_mod_cast hm_Icc.1
              · exact_mod_cast hm_Icc.2
            have hM_le : (M : ℝ) ≤ r ^ k / (2 * Real.pi) :=
              Nat.floor_le (by positivity)
            have hmul_le := mul_le_mul_of_nonneg_right (hm_le_M.trans hM_le) Real.two_pi_pos.le
            rw [div_mul_cancel₀ _ Real.two_pi_pos.ne'] at hmul_le
            linarith
          have hzr : ‖z‖ ≤ r := by
            by_contra! hgt
            exact absurd (pow_lt_pow_left₀ hgt hr.le hk_pos.ne') (not_lt_of_ge hnorm_zk)
          exact ⟨mem_closedBall_zero_iff.mpr hzr, hz0, hexp1⟩
        · rintro ⟨hz_cl, hz0, hexp1⟩
          obtain ⟨m, hm_eq⟩ := Complex.exp_eq_one_iff.mp hexp1
          have hm0 : m ≠ 0 := by
            intro h0
            rw [h0, Int.cast_zero, zero_mul] at hm_eq
            exact pow_ne_zero k hz0 hm_eq
          have hzr : ‖z‖ ≤ r := mem_closedBall_zero_iff.mp hz_cl
          have hn1 : |(m : ℝ)| * (2 * Real.pi) ≤ r ^ k := by
            have h := congrArg norm hm_eq
            simp only [norm_pow, norm_mul, Complex.norm_intCast, Complex.norm_ofNat,
              Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one] at h
            exact h.symm.trans_le (pow_le_pow_left₀ (norm_nonneg z) hzr k)
          have habs_le_div : |(m : ℝ)| ≤ r ^ k / (2 * Real.pi) :=
            (le_div_iff₀ Real.two_pi_pos).mpr hn1
          have hlt_M1 : r ^ k / (2 * Real.pi) < (M : ℝ) + 1 :=
            Nat.lt_floor_add_one (r ^ k / (2 * Real.pi))
          have hm_upper : m ≤ (M : ℤ) := by
            by_contra! hgt
            have h1 : (M : ℤ) + 1 ≤ m := by omega
            have h2 : (M : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h1
            linarith [le_abs_self (m : ℝ)]
          have hm_lower : -(M : ℤ) ≤ m := by
            by_contra! hlt
            have h1 : (M : ℤ) + 1 ≤ -m := by omega
            have h2 : (M : ℝ) + 1 ≤ -(m : ℝ) := by exact_mod_cast h1
            linarith [neg_le_abs (m : ℝ)]
          have hmI : m ∈ I_M := Finset.mem_erase.mpr ⟨hm0, Finset.mem_Icc.mpr ⟨hm_lower, hm_upper⟩⟩
          exact ⟨m, hmI, (hfib_mem hm0 z).mpr hm_eq⟩
      -- Evaluate `entireZeroCount h_k r`
      have hhk_term : ∀ z : ℂ,
          (if z ∈ Metric.closedBall (0 : ℂ) r then analyticOrderNatAt h_k z else 0) =
            if z ∈ S then 1 else 0 := by
        intro z
        by_cases hz0 : z = 0
        · subst z
          have h0_not_S : (0 : ℂ) ∉ S := fun h ↦ ((hmem_S_iff 0).mp h).2.1 rfl
          simp [Metric.mem_closedBall_self hr.le, hh_nat_ord0, h0_not_S]
        · by_cases hzS : z ∈ S
          · obtain ⟨hz_cl, _, hexp1⟩ := (hmem_S_iff z).mp hzS
            simp [hzS, hz_cl, (hord_nz hz0).2, hexp1]
          · by_cases hz_cl : z ∈ Metric.closedBall (0 : ℂ) r
            · have hexp_ne : Complex.exp (z ^ k) ≠ 1 :=
                fun h ↦ hzS ((hmem_S_iff z).mpr ⟨hz_cl, hz0, h⟩)
              simp [hzS, hz_cl, (hord_nz hz0).2, hexp_ne]
            · simp [hzS, hz_cl]
      have hhk_cnt : entireZeroCount h_k r = 2 * k * M := by
        unfold entireZeroCount
        rw [finsum_congr hhk_term, finsum_eq_sum_of_support_subset (s := S) _ (fun z hz ↦ by
          rw [Function.mem_support] at hz
          by_contra hnot
          rw [Finset.mem_coe] at hnot
          exact hz (by simp [hnot]))]
        have hsum1 : (∑ z ∈ S, if z ∈ S then (1 : ℕ) else 0) = ∑ _z ∈ S, (1 : ℕ) :=
          Finset.sum_congr rfl fun z hz ↦ by simp [hz]
        rw [hsum1, Finset.sum_const, smul_eq_mul, mul_one, hS_card]
      -- Evaluate `entireZeroCount f_k r`
      have h0_not_S : (0 : ℂ) ∉ S := fun h ↦ ((hmem_S_iff 0).mp h).2.1 rfl
      have hfk_term : ∀ z : ℂ,
          (if z ∈ Metric.closedBall (0 : ℂ) r then analyticOrderNatAt f_k z else 0) =
            if z = 0 then k else if z ∈ S then 1 else 0 := by
        intro z
        by_cases hz0 : z = 0
        · subst z
          simp [Metric.mem_closedBall_self hr.le, hf_nat_ord0]
        · simp only [hz0, ↓reduceIte]
          by_cases hzS : z ∈ S
          · obtain ⟨hz_cl, _, hexp1⟩ := (hmem_S_iff z).mp hzS
            simp [hzS, hz_cl, (hord_nz hz0).1, hexp1]
          · by_cases hz_cl : z ∈ Metric.closedBall (0 : ℂ) r
            · have hexp_ne : Complex.exp (z ^ k) ≠ 1 :=
                fun h ↦ hzS ((hmem_S_iff z).mpr ⟨hz_cl, hz0, h⟩)
              simp [hzS, hz_cl, (hord_nz hz0).1, hexp_ne]
            · simp [hzS, hz_cl]
      have hfk_cnt : entireZeroCount f_k r = k + 2 * k * M := by
        unfold entireZeroCount
        rw [finsum_congr hfk_term,
          finsum_eq_sum_of_support_subset (s := insert (0 : ℂ) S) _ (fun z hz ↦ by
            rw [Function.mem_support] at hz
            refine Finset.mem_insert.mpr ?_
            by_cases hz0 : z = 0
            · exact Or.inl hz0
            · right
              by_contra hnot
              simp [hz0, hnot] at hz)]
        rw [Finset.sum_insert h0_not_S]
        simp only [↓reduceIte]
        have hsumS : (∑ z ∈ S, if z = 0 then k else if z ∈ S then 1 else 0) =
            ∑ _z ∈ S, (1 : ℕ) := by
          refine Finset.sum_congr rfl fun z hz ↦ ?_
          have hz0 : z ≠ 0 := fun h ↦ h0_not_S (h ▸ hz)
          simp [hz0, hz]
        rw [hsumS, Finset.sum_const, smul_eq_mul, mul_one, hS_card]
      exact ⟨hhk_cnt, hfk_cnt⟩
    -- Asymptotic squeeze `log n(r) / log r → k` for BOTH `h_k` and `f_k`
    have hasymp_both :
        Tendsto (fun r : ℝ ↦ Real.log (entireZeroCount f_k r) / Real.log r)
          Filter.atTop (𝓝 (k : ℝ)) ∧
        Tendsto (fun r : ℝ ↦ Real.log (entireZeroCount h_k r) / Real.log r)
          Filter.atTop (𝓝 (k : ℝ)) := by
      let c₁ : ℝ := (k : ℝ) / (2 * Real.pi)
      let c₂ : ℝ := (3 * (k : ℝ)) / (2 * Real.pi)
      have hc₁_pos : 0 < c₁ := div_pos (Nat.cast_pos.mpr hk_pos) Real.two_pi_pos
      have hc₂_pos : 0 < c₂ := by positivity
      have hlim_bound : ∀ c : ℝ,
          Tendsto (fun r : ℝ ↦ Real.log c / Real.log r + (k : ℝ))
            Filter.atTop (𝓝 (k : ℝ)) := by
        intro c
        have h0 : Tendsto (fun r : ℝ ↦ Real.log c * (Real.log r)⁻¹) Filter.atTop (𝓝 0) := by
          simpa using tendsto_const_nhds.mul Real.tendsto_log_atTop.inv_tendsto_atTop
        simpa only [div_eq_mul_inv, zero_add] using h0.add tendsto_const_nhds
      have hsqueeze_bounds : ∀ᶠ r : ℝ in Filter.atTop,
          Real.log c₁ / Real.log r + (k : ℝ) ≤
            Real.log (entireZeroCount h_k r) / Real.log r ∧
          Real.log (entireZeroCount h_k r) / Real.log r ≤
            Real.log (entireZeroCount f_k r) / Real.log r ∧
          Real.log (entireZeroCount f_k r) / Real.log r ≤
            Real.log c₂ / Real.log r + (k : ℝ) := by
        filter_upwards [eventually_ge_atTop (4 * Real.pi)] with r hr
        have hr_gt2 : 2 < r := by linarith [Real.two_le_pi]
        have hr_pos : 0 < r := by linarith
        have hr_ge1 : 1 ≤ r := by linarith
        have hlogr_pos : 0 < Real.log r := Real.log_pos (by linarith)
        obtain ⟨hh_cnt, hf_cnt⟩ := hzero_counts r hr_pos
        let M : ℕ := Nat.floor (r ^ k / (2 * Real.pi))
        have hrk_ge : 4 * Real.pi ≤ r ^ k := by
          have h1 : r ≤ r ^ k := by simpa only [pow_one] using pow_le_pow_right₀ hr_ge1 hk
          exact hr.trans h1
        have hquot_ge2 : 2 ≤ r ^ k / (2 * Real.pi) := by
          rw [le_div_iff₀ Real.two_pi_pos]
          linarith
        have hM_ge1 : 1 ≤ M := by
          exact (show 1 ≤ 2 by omega).trans (Nat.le_floor hquot_ge2)
        have hM_upper : (M : ℝ) ≤ r ^ k / (2 * Real.pi) := Nat.floor_le (by positivity)
        have hM_lower : (r ^ k / (2 * Real.pi)) / 2 ≤ (M : ℝ) := by
          have hlt := Nat.lt_floor_add_one (r ^ k / (2 * Real.pi))
          change r ^ k / (2 * Real.pi) < (M : ℝ) + 1 at hlt
          linarith
        have hc₁_le_h : c₁ * r ^ k ≤ (entireZeroCount h_k r : ℝ) := by
          rw [hh_cnt]
          push_cast
          have h := mul_le_mul_of_nonneg_left hM_lower (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ))
          dsimp [c₁]
          linarith [show 2 * (k : ℝ) * (r ^ k / (2 * Real.pi) / 2) =
            (k : ℝ) / (2 * Real.pi) * r ^ k by ring]
        have hh_le_f : (entireZeroCount h_k r : ℝ) ≤ (entireZeroCount f_k r : ℝ) := by
          rw [hh_cnt, hf_cnt]
          exact_mod_cast Nat.le_add_left _ _
        have hf_le_c₂ : (entireZeroCount f_k r : ℝ) ≤ c₂ * r ^ k := by
          rw [hf_cnt]
          have hnat : k + 2 * k * M ≤ 3 * k * M := by
            have hkM : k ≤ k * M := Nat.le_mul_of_pos_right k hM_ge1
            linarith
          have hreal1 : ((k + 2 * k * M : ℕ) : ℝ) ≤ 3 * (k : ℝ) * (M : ℝ) := by
            exact_mod_cast hnat
          have hreal2 : 3 * (k : ℝ) * (M : ℝ) ≤ c₂ * r ^ k := by
            have h := mul_le_mul_of_nonneg_left hM_upper (by positivity : (0 : ℝ) ≤ 3 * (k : ℝ))
            dsimp [c₂]
            linarith [show 3 * (k : ℝ) * (r ^ k / (2 * Real.pi)) =
              3 * (k : ℝ) / (2 * Real.pi) * r ^ k by ring]
          exact hreal1.trans hreal2
        have hrk_pos : 0 < r ^ k := pow_pos hr_pos k
        have hc₁_rk_pos : 0 < c₁ * r ^ k := mul_pos hc₁_pos hrk_pos
        have hh_pos : 0 < (entireZeroCount h_k r : ℝ) := hc₁_rk_pos.trans_le hc₁_le_h
        have hf_pos : 0 < (entireZeroCount f_k r : ℝ) := hh_pos.trans_le hh_le_f
        have hlog1 : Real.log c₁ / Real.log r + (k : ℝ) ≤
            Real.log (entireZeroCount h_k r) / Real.log r := by
          have hl := Real.log_le_log hc₁_rk_pos hc₁_le_h
          rw [Real.log_mul hc₁_pos.ne' hrk_pos.ne', Real.log_pow] at hl
          have hd := div_le_div_of_nonneg_right hl hlogr_pos.le
          rwa [add_div, mul_div_cancel_right₀ (k : ℝ) hlogr_pos.ne'] at hd
        have hlog2 : Real.log (entireZeroCount h_k r) / Real.log r ≤
            Real.log (entireZeroCount f_k r) / Real.log r :=
          div_le_div_of_nonneg_right (Real.log_le_log hh_pos hh_le_f) hlogr_pos.le
        have hlog3 : Real.log (entireZeroCount f_k r) / Real.log r ≤
            Real.log c₂ / Real.log r + (k : ℝ) := by
          have hl := Real.log_le_log hf_pos hf_le_c₂
          rw [Real.log_mul hc₂_pos.ne' hrk_pos.ne', Real.log_pow] at hl
          have hd := div_le_div_of_nonneg_right hl hlogr_pos.le
          rwa [add_div, mul_div_cancel_right₀ (k : ℝ) hlogr_pos.ne'] at hd
        exact ⟨hlog1, hlog2, hlog3⟩
      refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim_bound c₁) (hlim_bound c₂)
        (hsqueeze_bounds.mono fun r h ↦ h.1.trans h.2.1)
        (hsqueeze_bounds.mono fun r h ↦ h.2.2),
        tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim_bound c₁) (hlim_bound c₂)
        (hsqueeze_bounds.mono fun r h ↦ h.1)
        (hsqueeze_bounds.mono fun r h ↦ h.2.1.trans h.2.2)⟩
    exact ⟨hf_diff, hf_nat_ord0, hfk_growth, fun r hr ↦ (hzero_counts r hr).2,
      hasymp_both.1, hh_diff, hh0, hgk_rel, hhk_growth, fun r hr ↦ (hzero_counts r hr).1,
      hasymp_both.2⟩

/-! ### 15.21: Blaschke Factors and Blaschke Products (`blaschkeFactor`, `IsBlaschkeProduct`, `theorem15_21`) -/

/-- Single Blaschke factor `b_a(z) = (‖a‖ / a) * (a - z) / (1 - conj(a) z)` (Rudin 15.21). -/
def blaschkeFactor (a z : ℂ) : ℂ :=
  ((‖a‖ : ℂ) / a) * ((a - z) / (1 - star a * z))

lemma blaschkeFactor_eq_neg_mul_phi (a z : ℂ) :
    blaschkeFactor a z = -(((‖a‖ : ℂ) / a) * RudinRCA.Chapter12.phi a z) := by
  simp only [blaschkeFactor, RudinRCA.Chapter12.phi]
  ring

lemma blaschkeFactor_zero {a : ℂ} (ha0 : a ≠ 0) :
    blaschkeFactor a 0 = (‖a‖ : ℂ) := by
  simp [blaschkeFactor, div_mul_cancel₀ _ ha0]

lemma blaschkeFactor_self (a : ℂ) :
    blaschkeFactor a a = 0 := by
  simp [blaschkeFactor]

lemma norm_blaschkeFactor_eq_norm_phi {a : ℂ} (ha0 : a ≠ 0) (z : ℂ) :
    ‖blaschkeFactor a z‖ = ‖RudinRCA.Chapter12.phi a z‖ := by
  rw [blaschkeFactor_eq_neg_mul_phi, norm_neg, norm_mul, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg a), div_self (norm_ne_zero_iff.mpr ha0), one_mul]

lemma norm_blaschkeFactor_lt_one {a z : ℂ}
    (ha : a ∈ Metric.ball (0 : ℂ) 1) (ha0 : a ≠ 0) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    ‖blaschkeFactor a z‖ < 1 := by
  rw [norm_blaschkeFactor_eq_norm_phi ha0]
  exact mem_ball_zero_iff.mp (RudinRCA.Chapter12.mapsTo_phi_ball ha hz)

lemma norm_blaschkeFactor_le_one {a z : ℂ}
    (ha : a ∈ Metric.ball (0 : ℂ) 1) (ha0 : a ≠ 0) (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    ‖blaschkeFactor a z‖ ≤ 1 := by
  rw [norm_blaschkeFactor_eq_norm_phi ha0]
  exact mem_closedBall_zero_iff.mp (RudinRCA.Chapter12.mapsTo_phi_closedBall ha hz)

lemma norm_blaschkeFactor_eq_one {a ζ : ℂ}
    (ha : a ∈ Metric.ball (0 : ℂ) 1) (ha0 : a ≠ 0) (hζ : ζ ∈ Metric.sphere (0 : ℂ) 1) :
    ‖blaschkeFactor a ζ‖ = 1 := by
  rw [norm_blaschkeFactor_eq_norm_phi ha0]
  have hζ_cl : ζ ∈ Metric.closedBall (0 : ℂ) 1 := Metric.sphere_subset_closedBall hζ
  have hden := RudinRCA.Chapter12.phi_denom_ne_zero ha hζ_cl
  have hsq := RudinRCA.Chapter12.one_sub_norm_phi_sq hden
  rw [mem_sphere_zero_iff_norm.mp hζ] at hsq
  have hrhs0 : (1 - ‖a‖ ^ 2) * (1 - 1 ^ 2) / ‖1 - star a * ζ‖ ^ 2 = 0 := by ring
  have h1 : ‖RudinRCA.Chapter12.phi a ζ‖ ^ 2 = 1 := by linarith
  nlinarith [norm_nonneg (RudinRCA.Chapter12.phi a ζ)]

lemma analyticAt_blaschkeFactor {a z : ℂ}
    (ha : a ∈ Metric.ball (0 : ℂ) 1) (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    AnalyticAt ℂ (blaschkeFactor a) z := by
  have hden : 1 - star a * z ≠ 0 := RudinRCA.Chapter12.phi_denom_ne_zero ha hz
  unfold blaschkeFactor
  exact analyticAt_const.mul
    ((analyticAt_const.sub analyticAt_id).div
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) hden)

lemma differentiableOn_blaschkeFactor_closedBall {a : ℂ}
    (ha : a ∈ Metric.ball (0 : ℂ) 1) :
    DifferentiableOn ℂ (blaschkeFactor a) (Metric.closedBall (0 : ℂ) 1) :=
  fun _z hz ↦ (analyticAt_blaschkeFactor ha hz).differentiableAt.differentiableWithinAt

lemma differentiableOn_blaschkeFactor_ball {a : ℂ}
    (ha : a ∈ Metric.ball (0 : ℂ) 1) :
    DifferentiableOn ℂ (blaschkeFactor a) (Metric.ball (0 : ℂ) 1) :=
  (differentiableOn_blaschkeFactor_closedBall ha).mono Metric.ball_subset_closedBall

lemma blaschkeFactor_eq_zero_iff {a z : ℂ}
    (ha : a ∈ Metric.ball (0 : ℂ) 1) (ha0 : a ≠ 0) (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    blaschkeFactor a z = 0 ↔ z = a := by
  have hden : 1 - star a * z ≠ 0 := RudinRCA.Chapter12.phi_denom_ne_zero ha hz
  have hc : ((‖a‖ : ℂ) / a) ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha0)) ha0
  simp only [blaschkeFactor, mul_eq_zero, hc, false_or, div_eq_zero_iff, hden, or_false,
    sub_eq_zero]
  exact eq_comm

lemma analyticOrderAt_blaschkeFactor {a z : ℂ}
    (ha : a ∈ Metric.ball (0 : ℂ) 1) (ha0 : a ≠ 0) (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    analyticOrderAt (blaschkeFactor a) z = if z = a then 1 else 0 := by
  by_cases hza : z = a
  · subst z
    let g : ℂ → ℂ := fun w ↦ -(((‖a‖ : ℂ) / a) / (1 - star a * w))
    have hden : 1 - star a * a ≠ 0 := RudinRCA.Chapter12.phi_denom_ne_zero ha hz
    have hc : ((‖a‖ : ℂ) / a) ≠ 0 :=
      div_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha0)) ha0
    have hg_ana : AnalyticAt ℂ g a :=
      (analyticAt_const.div
        (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) hden).neg
    have hlin_ana : AnalyticAt ℂ (fun w : ℂ ↦ w - a) a := by fun_prop
    have hg_ne : g a ≠ 0 := neg_ne_zero.mpr (div_ne_zero hc hden)
    have hfac : blaschkeFactor a = g * (fun w : ℂ ↦ w - a) := by
      funext w
      dsimp [blaschkeFactor, g]
      ring
    simp only [↓reduceIte]
    rw [hfac, analyticOrderAt_mul hg_ana hlin_ana,
      hg_ana.analyticOrderAt_eq_zero.mpr hg_ne, zero_add]
    simp
  · simp only [hza, ↓reduceIte]
    exact (analyticAt_blaschkeFactor ha hz).analyticOrderAt_eq_zero.mpr
      ((blaschkeFactor_eq_zero_iff ha ha0 hz).not.mpr hza)

/-- **Key Estimate in 15.21**: for `a ∈ ball 0 1 \ {0}` and `z ∈ closedBall 0 r` (`0 ≤ r < 1`),
`‖1 - blaschkeFactor a z‖ ≤ (2 / (1 - r)) * (1 - ‖a‖)`. -/
theorem norm_one_sub_blaschkeFactor_le {a z : ℂ} {r : ℝ}
    (ha : a ∈ Metric.ball (0 : ℂ) 1) (ha0 : a ≠ 0)
    (_hr0 : 0 ≤ r) (hr1 : r < 1) (hz : z ∈ Metric.closedBall (0 : ℂ) r) :
    ‖1 - blaschkeFactor a z‖ ≤ (2 / (1 - r)) * (1 - ‖a‖) := by
  have ha_lt : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hzr : ‖z‖ ≤ r := mem_closedBall_zero_iff.mp hz
  have hz_cl1 : z ∈ Metric.closedBall (0 : ℂ) 1 :=
    Metric.closedBall_subset_closedBall hr1.le hz
  have hden : 1 - star a * z ≠ 0 := RudinRCA.Chapter12.phi_denom_ne_zero ha hz_cl1
  have hnum_id : a * (1 - star a * z) - (‖a‖ : ℂ) * (a - z) =
      (a + (‖a‖ : ℂ) * z) * ((1 - ‖a‖ : ℝ) : ℂ) := by
    have hconj : a * star a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
    calc
      a * (1 - star a * z) - (‖a‖ : ℂ) * (a - z)
          = a - (a * star a) * z - (‖a‖ : ℂ) * a + (‖a‖ : ℂ) * z := by ring
      _ = a - ((‖a‖ ^ 2 : ℝ) : ℂ) * z - (‖a‖ : ℂ) * a + (‖a‖ : ℂ) * z := by rw [hconj]
      _ = (a + (‖a‖ : ℂ) * z) * ((1 - ‖a‖ : ℝ) : ℂ) := by push_cast; ring
  have hid : 1 - blaschkeFactor a z =
      ((a + (‖a‖ : ℂ) * z) / a) * (((1 - ‖a‖ : ℝ) : ℂ) / (1 - star a * z)) := by
    rw [blaschkeFactor, div_mul_div_comm, div_mul_div_comm,
      one_sub_div (mul_ne_zero ha0 hden), hnum_id]
  have hnum_le : ‖(a + (‖a‖ : ℂ) * z) / a‖ ≤ 2 := by
    rw [norm_div]
    have h1 : ‖a + (‖a‖ : ℂ) * z‖ ≤ 2 * ‖a‖ := by
      calc
        ‖a + (‖a‖ : ℂ) * z‖ ≤ ‖a‖ + ‖(‖a‖ : ℂ) * z‖ := norm_add_le _ _
        _ = ‖a‖ + ‖a‖ * ‖z‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha_pos.le]
        _ ≤ ‖a‖ + ‖a‖ * 1 := by gcongr; linarith
        _ = 2 * ‖a‖ := by ring
    exact (div_le_iff₀ ha_pos).mpr h1
  have hden_ge : 1 - r ≤ ‖1 - star a * z‖ := by
    have h1 : ‖(1 : ℂ)‖ - ‖star a * z‖ ≤ ‖1 - star a * z‖ := norm_sub_norm_le _ _
    rw [norm_one, norm_mul, norm_star] at h1
    have hmul_le : ‖a‖ * ‖z‖ ≤ r := by
      calc
        ‖a‖ * ‖z‖ ≤ 1 * r :=
          mul_le_mul ha_lt.le hzr (norm_nonneg z) zero_le_one
        _ = r := one_mul r
    linarith
  have h1r_pos : 0 < 1 - r := sub_pos.mpr hr1
  have h1a_nn : 0 ≤ 1 - ‖a‖ := sub_nonneg.mpr ha_lt.le
  rw [hid, norm_mul, norm_div ((1 - ‖a‖ : ℝ) : ℂ), Complex.norm_real,
    Real.norm_of_nonneg h1a_nn]
  calc
    ‖(a + (‖a‖ : ℂ) * z) / a‖ * ((1 - ‖a‖) / ‖1 - star a * z‖)
        ≤ 2 * ((1 - ‖a‖) / (1 - r)) := by
      refine mul_le_mul hnum_le ?_ (div_nonneg h1a_nn (norm_nonneg _)) (by positivity)
      exact div_le_div_of_nonneg_left h1a_nn h1r_pos hden_ge
    _ = (2 / (1 - r)) * (1 - ‖a‖) := by ring

/-- **Definition 15.21 (`IsBlaschkeProduct`)**: A function `B : ℂ → ℂ` is a Blaschke product on
`U = Metric.ball 0 1` if it agrees on `U` either with a finite Blaschke product
`z ^ k * ∏_{i < N} b_{a_i}(z)` (including empty products `N = 0`, such as `B(z) = 1` when `k = 0`
or `B(z) = z ^ k`) or with a convergent infinite Blaschke product `z ^ k * ∏'_{n : ℕ} b_{a_n}(z)`
where `a_n ∈ U \ {0}` and `∑ (1 - ‖a_n‖) < ∞`. -/
def IsBlaschkeProduct (B : ℂ → ℂ) : Prop :=
  (∃ (k N : ℕ) (a : Fin N → ℂ),
    (∀ i, a i ∈ Metric.ball (0 : ℂ) 1 ∧ a i ≠ 0) ∧
    ∀ z ∈ Metric.ball (0 : ℂ) 1, B z = z ^ k * ∏ i : Fin N, blaschkeFactor (a i) z) ∨
  (∃ (k : ℕ) (a : ℕ → ℂ),
    (∀ n, a n ∈ Metric.ball (0 : ℂ) 1 ∧ a n ≠ 0) ∧
    Summable (fun n ↦ 1 - ‖a n‖) ∧
    ∀ z ∈ Metric.ball (0 : ℂ) 1, B z = z ^ k * ∏' n, blaschkeFactor (a n) z)

/-- The empty Blaschke product `B(z) = 1` (`k = 0, N = 0`) satisfies `IsBlaschkeProduct`. -/
lemma isBlaschkeProduct_one : IsBlaschkeProduct (fun _ : ℂ ↦ 1) :=
  Or.inl ⟨0, 0, Fin.elim0, fun i ↦ Fin.elim0 i, fun z _ ↦ by simp⟩

/-- Any monomial `B(z) = z ^ k` (`N = 0`) satisfies `IsBlaschkeProduct`. -/
lemma isBlaschkeProduct_pow (k : ℕ) : IsBlaschkeProduct (fun z : ℂ ↦ z ^ k) :=
  Or.inl ⟨k, 0, Fin.elim0, fun i ↦ Fin.elim0 i, fun z _ ↦ by simp⟩

/-- Properties of finite (including empty `N = 0`) Blaschke products in 15.21. -/
theorem finite_blaschke_product (k N : ℕ) (a : Fin N → ℂ)
    (ha : ∀ i, a i ∈ Metric.ball (0 : ℂ) 1 ∧ a i ≠ 0) :
    let B : ℂ → ℂ := fun z ↦ z ^ k * ∏ i : Fin N, blaschkeFactor (a i) z
    IsBlaschkeProduct B ∧
    DifferentiableOn ℂ B (Metric.closedBall (0 : ℂ) 1) ∧
    DifferentiableOn ℂ B (Metric.ball (0 : ℂ) 1) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, ‖B z‖ ≤ 1) ∧
    (∀ ζ ∈ Metric.sphere (0 : ℂ) 1, ‖B ζ‖ = 1) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, B z = 0 ↔ (z = 0 ∧ 0 < k) ∨ ∃ i, z = a i) ∧
    analyticOrderNatAt B 0 = k ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1 \ {0},
      analyticOrderNatAt B z = (Finset.univ.filter (fun i ↦ a i = z)).card) := by
  classical
  let P : ℂ → ℂ := fun z ↦ ∏ i : Fin N, blaschkeFactor (a i) z
  let B : ℂ → ℂ := fun z ↦ z ^ k * P z
  have hB_is : IsBlaschkeProduct B := Or.inl ⟨k, N, a, ha, fun _ _ ↦ rfl⟩
  have hP_ana : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ P z := by
    intro z hz
    have hstep : ∀ s : Finset (Fin N),
        AnalyticAt ℂ (fun w ↦ ∏ i ∈ s, blaschkeFactor (a i) w) z := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using analyticAt_const
      | insert j s hj ih =>
        have hfn : (fun w ↦ ∏ i ∈ insert j s, blaschkeFactor (a i) w) =
            blaschkeFactor (a j) * (fun w ↦ ∏ i ∈ s, blaschkeFactor (a i) w) := by
          funext w
          exact Finset.prod_insert hj
        rw [hfn]
        exact (analyticAt_blaschkeFactor (ha j).1 hz).mul ih
    exact hstep Finset.univ
  have hB_ana : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ B z :=
    fun z hz ↦ (analyticAt_id.pow k).mul (hP_ana z hz)
  have hB_diff_cl : DifferentiableOn ℂ B (Metric.closedBall (0 : ℂ) 1) :=
    fun z hz ↦ (hB_ana z hz).differentiableAt.differentiableWithinAt
  have hB_diff_ball : DifferentiableOn ℂ B (Metric.ball (0 : ℂ) 1) :=
    hB_diff_cl.mono Metric.ball_subset_closedBall
  have hB_norm_le : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖B z‖ ≤ 1 := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
    have hz_cl : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz
    dsimp [B, P]
    rw [norm_mul, norm_pow, norm_prod]
    have hp1 : ‖z‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg z) hz1
    have hp2 : (∏ i : Fin N, ‖blaschkeFactor (a i) z‖) ≤ 1 :=
      (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
        (fun i _ ↦ norm_blaschkeFactor_le_one (ha i).1 (ha i).2 hz_cl)).trans_eq
        Finset.prod_const_one
    calc
      ‖z‖ ^ k * ∏ i : Fin N, ‖blaschkeFactor (a i) z‖ ≤ 1 * 1 :=
        mul_le_mul hp1 hp2 (Finset.prod_nonneg fun i _ ↦ norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hB_norm_sp : ∀ ζ ∈ Metric.sphere (0 : ℂ) 1, ‖B ζ‖ = 1 := by
    intro ζ hζ
    dsimp [B, P]
    rw [norm_mul, norm_pow, mem_sphere_zero_iff_norm.mp hζ, one_pow, one_mul, norm_prod]
    exact Finset.prod_eq_one fun i _ ↦ norm_blaschkeFactor_eq_one (ha i).1 (ha i).2 hζ
  have hB_zero : ∀ z ∈ Metric.ball (0 : ℂ) 1, B z = 0 ↔ (z = 0 ∧ 0 < k) ∨ ∃ i, z = a i := by
    intro z hz
    have hz_cl : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz
    dsimp [B, P]
    rw [mul_eq_zero, pow_eq_zero_iff', Finset.prod_eq_zero_iff]
    simp only [Finset.mem_univ, true_and, ne_eq]
    constructor
    · rintro (⟨rfl, hk0⟩ | ⟨i, hi⟩)
      · exact Or.inl ⟨rfl, Nat.pos_of_ne_zero hk0⟩
      · exact Or.inr ⟨i, (blaschkeFactor_eq_zero_iff (ha i).1 (ha i).2 hz_cl).mp hi⟩
    · rintro (⟨rfl, hkpos⟩ | ⟨i, rfl⟩)
      · exact Or.inl ⟨rfl, hkpos.ne'⟩
      · exact Or.inr ⟨i, blaschkeFactor_self (a i)⟩
  have hP_aord : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      analyticOrderAt P z = ∑ i : Fin N, if z = a i then (1 : ℕ∞) else 0 := by
    intro z hz
    dsimp [P]
    rw [analyticOrderAt_finset_product Finset.univ
      (fun i _ ↦ analyticAt_blaschkeFactor (ha i).1 hz)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact analyticOrderAt_blaschkeFactor (ha i).1 (ha i).2 hz
  have hB_ord0 : analyticOrderNatAt B 0 = k := by
    have h0_cl : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := Metric.mem_closedBall_self zero_le_one
    have hP0_ord : analyticOrderAt P 0 = 0 := by
      rw [hP_aord 0 h0_cl]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      simp [(ha i).2.symm]
    have hB0_ord : analyticOrderAt B 0 = (k : ℕ∞) := by
      have hpow_ana0 : AnalyticAt ℂ (fun z : ℂ ↦ z ^ k) 0 := by fun_prop
      change analyticOrderAt ((fun z : ℂ ↦ z ^ k) * P) 0 = (k : ℕ∞)
      rw [analyticOrderAt_mul hpow_ana0 (hP_ana 0 h0_cl),
        analyticOrderAt_pow_origin k, hP0_ord, add_zero]
    simp [analyticOrderNatAt, hB0_ord]
  have hB_ord_nz : ∀ z ∈ Metric.ball (0 : ℂ) 1 \ {0},
      analyticOrderNatAt B z = (Finset.univ.filter (fun i ↦ a i = z)).card := by
    rintro z ⟨hz_ball, hz0⟩
    rw [Set.mem_singleton_iff] at hz0
    have hz_cl : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz_ball
    have hpow_ana : AnalyticAt ℂ (fun w : ℂ ↦ w ^ k) z := by fun_prop
    have hpow0 : analyticOrderAt (fun w : ℂ ↦ w ^ k) z = 0 :=
      hpow_ana.analyticOrderAt_eq_zero.mpr (pow_ne_zero k hz0)
    have hBz_ord : analyticOrderAt B z =
        (((Finset.univ.filter (fun i ↦ a i = z)).card : ℕ) : ℕ∞) := by
      change analyticOrderAt ((fun w : ℂ ↦ w ^ k) * P) z = _
      rw [analyticOrderAt_mul hpow_ana (hP_ana z hz_cl), hpow0, zero_add,
        hP_aord z hz_cl, Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      by_cases hiz : z = a i
      · simp [hiz]
      · have hne : a i ≠ z := fun h ↦ hiz h.symm
        simp [hiz, hne]
    simp [analyticOrderNatAt, hBz_ord]
  exact ⟨hB_is, hB_diff_cl, hB_diff_ball, hB_norm_le, hB_norm_sp, hB_zero, hB_ord0, hB_ord_nz⟩

/-- **Theorem 15.21 (Convergence and Zero Structure of Blaschke Products)**:
For `k : ℕ` and `a : ℕ → ℂ` with `∀ n, a n ∈ Metric.ball 0 1 ∧ a n ≠ 0` and
`Summable (fun n ↦ 1 - ‖a n‖)`, `B z := z ^ k * ∏' n, blaschkeFactor (a n) z` converges locally
uniformly on `Metric.ball 0 1`, is holomorphic and bounded by `1` on `Metric.ball 0 1`, has
zeros in `Metric.ball 0 1` exclusively at `{a n | n : ℕ}` (and `0` iff `0 < k`), with
`analyticOrderNatAt B 0 = k` and `analyticOrderNatAt B z = ∑' n, if z = a n then 1 else 0` for
`z ∈ Metric.ball 0 1 \ {0}`. -/
theorem theorem15_21 (k : ℕ) {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ Metric.ball (0 : ℂ) 1 ∧ a n ≠ 0)
    (hsum : Summable (fun n ↦ 1 - ‖a n‖)) :
    let P : ℂ → ℂ := fun z ↦ ∏' n, blaschkeFactor (a n) z
    let B : ℂ → ℂ := fun z ↦ z ^ k * P z
    IsBlaschkeProduct B ∧
    TendstoLocallyUniformlyOn
      (fun N z ↦ ∏ n ∈ Finset.range N, blaschkeFactor (a n) z) P
      Filter.atTop (Metric.ball (0 : ℂ) 1) ∧
    TendstoLocallyUniformlyOn
      (fun N z ↦ z ^ k * ∏ n ∈ Finset.range N, blaschkeFactor (a n) z) B
      Filter.atTop (Metric.ball (0 : ℂ) 1) ∧
    DifferentiableOn ℂ P (Metric.ball (0 : ℂ) 1) ∧
    DifferentiableOn ℂ B (Metric.ball (0 : ℂ) 1) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, ‖P z‖ ≤ 1 ∧ ‖B z‖ ≤ 1) ∧
    P 0 ≠ 0 ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, B z = 0 ↔ (z = 0 ∧ 0 < k) ∨ ∃ n, z = a n) ∧
    analyticOrderNatAt B 0 = k ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1 \ {0},
      analyticOrderAt B z ≠ ⊤ ∧
      analyticOrderNatAt B z = ∑' n, if z = a n then 1 else 0) := by
  let F : ℕ → ℂ → ℂ := fun n z ↦ blaschkeFactor (a n) z
  let P : ℂ → ℂ := fun z ↦ ∏' n, F n z
  let B : ℂ → ℂ := fun z ↦ z ^ k * P z
  have hB_is : IsBlaschkeProduct B := Or.inr ⟨k, a, ha, hsum, fun _ _ ↦ rfl⟩
  have hF_diff : ∀ n, DifferentiableOn ℂ (F n) (Metric.ball (0 : ℂ) 1) :=
    fun n ↦ differentiableOn_blaschkeFactor_ball (ha n).1
  have hF_nonzero : ∀ n z, z ∈ Metric.ball (0 : ℂ) 1 →
      ∃ w ∈ connectedComponentIn (Metric.ball (0 : ℂ) 1) z, F n w ≠ 0 := by
    intro n z hz
    have h0_mem : (0 : ℂ) ∈ connectedComponentIn (Metric.ball (0 : ℂ) 1) z :=
      (convex_ball (0 : ℂ) 1).isPreconnected.subset_connectedComponentIn hz Set.Subset.rfl
        (Metric.mem_ball_self zero_lt_one)
    refine ⟨0, h0_mem, ?_⟩
    rw [show F n 0 = (‖a n‖ : ℂ) from blaschkeFactor_zero (ha n).2]
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (ha n).2)
  -- Local uniform convergence of `∑ ‖1 - F n z‖` on `ball 0 1`
  have hseries_loc : TendstoLocallyUniformlyOn
      (fun N z ↦ ∑ n ∈ Finset.range N, ‖1 - F n z‖)
      (fun z ↦ ∑' n, ‖1 - F n z‖) Filter.atTop (Metric.ball (0 : ℂ) 1) := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball]
    intro K hK_sub hK_comp
    rcases K.eq_empty_or_nonempty with rfl | hK_ne
    · exact tendstoUniformlyOn_empty
    · obtain ⟨z₀, hz₀_K, hz₀_max⟩ := hK_comp.exists_isMaxOn hK_ne continuous_norm.continuousOn
      let r : ℝ := ‖z₀‖
      have hr0 : 0 ≤ r := norm_nonneg z₀
      have hr1 : r < 1 := mem_ball_zero_iff.mp (hK_sub hz₀_K)
      refine tendstoUniformlyOn_tsum_nat (hsum.mul_left (2 / (1 - r))) fun n z hzK ↦ ?_
      have hz_cl : z ∈ Metric.closedBall (0 : ℂ) r :=
        mem_closedBall_zero_iff.mpr (hz₀_max hzK)
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact norm_one_sub_blaschkeFactor_le (ha n).1 (ha n).2 hr0 hr1 hz_cl
  obtain ⟨hP_lim, hP_diff, hP_ord⟩ := holomorphic_product_multiplicity
    Metric.isOpen_ball hF_diff hF_nonzero ⟨_, hseries_loc⟩
  -- Local uniform convergence of `z ^ k * ∏_{n < N} F n z` to `B`
  have hB_lim : TendstoLocallyUniformlyOn
      (fun N z ↦ z ^ k * ∏ n ∈ Finset.range N, F n z) B
      Filter.atTop (Metric.ball (0 : ℂ) 1) := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball]
    intro K hK_sub hK_comp
    have hP_K :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball).mp hP_lim K hK_sub hK_comp
    rw [Metric.tendstoUniformlyOn_iff] at hP_K ⊢
    intro ε hε
    filter_upwards [hP_K ε hε] with N hN z hzK
    have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp (hK_sub hzK)).le
    have hzk1 : ‖z ^ k‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg z) hz1
    dsimp [B]
    rw [dist_eq_norm, ← mul_sub, norm_mul]
    calc
      ‖z ^ k‖ * ‖P z - ∏ n ∈ Finset.range N, F n z‖
          ≤ 1 * ‖P z - ∏ n ∈ Finset.range N, F n z‖ :=
        mul_le_mul_of_nonneg_right hzk1 (norm_nonneg _)
      _ = dist (P z) (∏ n ∈ Finset.range N, F n z) := by rw [one_mul, dist_eq_norm]
      _ < ε := hN z hzK
  have hB_diff : DifferentiableOn ℂ B (Metric.ball (0 : ℂ) 1) :=
    (differentiableOn_id.pow k).mul hP_diff
  -- Norm bounds `‖P z‖ ≤ 1` and `‖B z‖ ≤ 1` on `ball 0 1`
  have hPB_norm : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖P z‖ ≤ 1 ∧ ‖B z‖ ≤ 1 := by
    intro z hz
    have hz_cl : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz
    have hpt : Tendsto (fun N ↦ ∏ n ∈ Finset.range N, F n z) Filter.atTop (𝓝 (P z)) :=
      hP_lim.tendsto_at hz
    have hP1 : ‖P z‖ ≤ 1 := by
      refine le_of_tendsto' hpt.norm fun N ↦ ?_
      rw [norm_prod]
      exact (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
        (fun n _ ↦ norm_blaschkeFactor_le_one (ha n).1 (ha n).2 hz_cl)).trans_eq
        Finset.prod_const_one
    have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
    have hB1 : ‖B z‖ ≤ 1 := by
      dsimp [B]
      rw [norm_mul, norm_pow]
      calc
        ‖z‖ ^ k * ‖P z‖ ≤ 1 * 1 :=
          mul_le_mul (pow_le_one₀ (norm_nonneg z) hz1) hP1 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    exact ⟨hP1, hB1⟩
  -- Zeros and multiplicities of `P` and `B`
  have hP_zero_iff : ∀ z ∈ Metric.ball (0 : ℂ) 1, P z = 0 ↔ ∃ n, z = a n := by
    intro z hz
    have hz_cl : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz
    have hsz : Summable (fun n ↦ ‖1 - F n z‖) :=
      ((hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ norm_nonneg _) _).mpr
        (hseries_loc.tendsto_at hz)).summable
    constructor
    · intro hPz
      by_contra hnone
      simp only [not_exists] at hnone
      have hF_ne : ∀ n, F n z ≠ 0 := fun n ↦
        (blaschkeFactor_eq_zero_iff (ha n).1 (ha n).2 hz_cl).not.mpr (hnone n)
      have hone : ∀ n, (1 : ℂ) + (F n z - 1) = F n z := fun _ ↦ by ring
      have hnorm : Summable (fun n ↦ ‖F n z - 1‖) := by simpa only [norm_sub_rev] using hsz
      have hn := tprod_one_add_ne_zero_of_summable
        (fun n ↦ by simpa only [hone] using hF_ne n) hnorm
      exact hn (by simpa only [hone] using hPz)
    · rintro ⟨n, rfl⟩
      exact tprod_of_exists_eq_zero ⟨n, blaschkeFactor_self (a n)⟩
  have hP0_ne : P 0 ≠ 0 := by
    intro h0
    obtain ⟨n, hn⟩ := (hP_zero_iff 0 (Metric.mem_ball_self zero_lt_one)).mp h0
    exact (ha n).2 hn.symm
  have hB_zero_iff : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      B z = 0 ↔ (z = 0 ∧ 0 < k) ∨ ∃ n, z = a n := by
    intro z hz
    dsimp [B]
    rw [mul_eq_zero, pow_eq_zero_iff', hP_zero_iff z hz]
    constructor
    · rintro (⟨rfl, hk0⟩ | hex)
      · exact Or.inl ⟨rfl, Nat.pos_of_ne_zero hk0⟩
      · exact Or.inr hex
    · rintro (⟨rfl, hkpos⟩ | hex)
      · exact Or.inl ⟨rfl, hkpos.ne'⟩
      · exact Or.inr hex
  have hP_ana : AnalyticOnNhd ℂ P (Metric.ball (0 : ℂ) 1) :=
    hP_diff.analyticOnNhd Metric.isOpen_ball
  have hB_ord0 : analyticOrderNatAt B 0 = k := by
    have h0_ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self zero_lt_one
    have hP0_ord : analyticOrderAt P 0 = 0 :=
      (hP_ana 0 h0_ball).analyticOrderAt_eq_zero.mpr hP0_ne
    have hB0_ord : analyticOrderAt B 0 = (k : ℕ∞) := by
      have hpow_ana0 : AnalyticAt ℂ (fun z : ℂ ↦ z ^ k) 0 := by fun_prop
      change analyticOrderAt ((fun z : ℂ ↦ z ^ k) * P) 0 = (k : ℕ∞)
      rw [analyticOrderAt_mul hpow_ana0 (hP_ana 0 h0_ball),
        analyticOrderAt_pow_origin k, hP0_ord, add_zero]
    simp [analyticOrderNatAt, hB0_ord]
  have hB_ord_nz : ∀ z ∈ Metric.ball (0 : ℂ) 1 \ {0},
      analyticOrderAt B z ≠ ⊤ ∧
      analyticOrderNatAt B z = ∑' n, if z = a n then 1 else 0 := by
    rintro z ⟨hz_ball, hz0⟩
    rw [Set.mem_singleton_iff] at hz0
    have hz_cl : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz_ball
    obtain ⟨_, hP_fin, hP_sum, _⟩ := hP_ord z hz_ball
    have hpow_ana : AnalyticAt ℂ (fun w : ℂ ↦ w ^ k) z := by fun_prop
    have hpow0 : analyticOrderAt (fun w : ℂ ↦ w ^ k) z = 0 :=
      hpow_ana.analyticOrderAt_eq_zero.mpr (pow_ne_zero k hz0)
    have hBP_ord : analyticOrderAt B z = analyticOrderAt P z := by
      change analyticOrderAt ((fun w : ℂ ↦ w ^ k) * P) z = _
      rw [analyticOrderAt_mul hpow_ana (hP_ana z hz_ball), hpow0, zero_add]
    have hBP_nat : analyticOrderNatAt B z = analyticOrderNatAt P z := by
      simp [analyticOrderNatAt, hBP_ord]
    refine ⟨hBP_ord ▸ hP_fin, ?_⟩
    rw [hBP_nat, hP_sum]
    refine tsum_congr fun n ↦ ?_
    simp only [F, analyticOrderNatAt, analyticOrderAt_blaschkeFactor (ha n).1 (ha n).2 hz_cl]
    split_ifs <;> simp
  exact ⟨hB_is, hP_lim, hB_lim, hP_diff, hB_diff, hPB_norm, hP0_ne, hB_zero_iff,
    hB_ord0, hB_ord_nz⟩

/-! ### 15.22: Positive Logarithm and the Nevanlinna Class `N` (`posLog_eq_ite`, `NevanlinnaClass`, `theorem15_22`) -/

/-- Rudin 15.22 piecewise characterization of `log⁺ t` (`Real.posLog t`) for `t ≥ 0`:
`log⁺ t = log t` if `1 < t`, and `0` if `0 ≤ t ≤ 1`. -/
theorem posLog_eq_ite {t : ℝ} (ht : 0 ≤ t) :
    Real.posLog t = if 1 < t then Real.log t else 0 := by
  split_ifs with h
  · have h1 : 1 ≤ |t| := by
      rw [abs_of_nonneg ht]
      exact h.le
    exact Real.posLog_eq_log h1
  · have hle : |t| ≤ 1 := by
      rw [abs_of_nonneg ht]
      exact not_lt.mp h
    exact (Real.posLog_eq_zero_iff t).mpr hle

/-- Norm specialization of `posLog_eq_ite`: `Real.posLog ‖w‖ = if 1 < ‖w‖ then Real.log ‖w‖ else 0`. -/
theorem posLog_norm_eq_ite (w : ℂ) :
    Real.posLog ‖w‖ = if 1 < ‖w‖ then Real.log ‖w‖ else 0 :=
  posLog_eq_ite (norm_nonneg w)

/-- Circle-integrability of `z ↦ Real.posLog ‖f z‖` on `sphere 0 r` (`0 ≤ r < R`) for `f`
holomorphic on `ball 0 R`. -/
lemma circleIntegrable_posLog_norm_of_differentiableOn {f : ℂ → ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R)) (hr0 : 0 ≤ r) (hrR : r < R) :
    CircleIntegrable (fun z ↦ Real.posLog ‖f z‖) 0 r := by
  have hana : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) R) := hf.analyticOnNhd Metric.isOpen_ball
  have hsub : Metric.sphere (0 : ℂ) |r| ⊆ Metric.ball (0 : ℂ) R := by
    rw [abs_of_nonneg hr0]
    exact Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_ball hrR)
  exact (hana.mono hsub).meromorphicOn.circleIntegrable_posLog_norm

/-- **Definition 15.22 (`NevanlinnaClass`)**: The Nevanlinna class `N` consists of all holomorphic
functions `f` on `U = Metric.ball 0 1` whose radial `log⁺` circle averages
`circleAverage (fun z ↦ Real.posLog ‖f z‖) 0 r` are bounded for `0 < r < 1`. -/
def NevanlinnaClass : Set (ℂ → ℂ) :=
  {f | DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) ∧
    ∃ C : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      Real.circleAverage (fun z ↦ Real.posLog ‖f z‖) 0 r ≤ C}

/-- Equivalence in Definition 15.22 between bounding radial `log⁺` means over `0 < r < 1`
and over `0 ≤ r < 1`. -/
theorem mem_nevanlinnaClass_iff_Ico {f : ℂ → ℂ} :
    f ∈ NevanlinnaClass ↔
      DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) ∧
        ∃ C : ℝ, ∀ r ∈ Set.Ico (0 : ℝ) 1,
          Real.circleAverage (fun z ↦ Real.posLog ‖f z‖) 0 r ≤ C := by
  constructor
  · rintro ⟨hf, C, hC⟩
    refine ⟨hf, max C (Real.posLog ‖f 0‖), fun r hr ↦ ?_⟩
    by_cases hr0 : r = 0
    · subst r
      rw [Real.circleAverage_zero]
      exact le_max_right _ _
    · have hr_pos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
      exact (hC r ⟨hr_pos, hr.2⟩).trans (le_max_left _ _)
  · rintro ⟨hf, C, hC⟩
    exact ⟨hf, C, fun r hr ↦ hC r (Set.Ioo_subset_Ico_self hr)⟩

/-- **15.22 (`H^∞ ⊆ N`)**: Every bounded holomorphic function on `Metric.ball 0 1` belongs to
`NevanlinnaClass`; in particular, for every `f ∈ RudinRCA.Chapter11.HInfty`,
`RudinRCA.Chapter11.extendZero f ∈ NevanlinnaClass`. -/
theorem theorem15_22 :
    (∀ {f : ℂ → ℂ}, DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) →
      (∃ M : ℝ, ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ M) →
      f ∈ NevanlinnaClass) ∧
    (∀ f ∈ RudinRCA.Chapter11.HInfty,
      RudinRCA.Chapter11.extendZero f ∈ NevanlinnaClass) := by
  have hbdd_sub : ∀ {f : ℂ → ℂ}, DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) →
      (∃ M : ℝ, ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ M) →
      f ∈ NevanlinnaClass := by
    intro f hf ⟨M, hM⟩
    refine ⟨hf, Real.posLog (max M 0), fun r hr ↦ ?_⟩
    have hcint := circleIntegrable_posLog_norm_of_differentiableOn hf hr.1.le hr.2
    refine Real.circleAverage_mono_on_of_le_circle hcint fun z hz ↦ ?_
    have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, abs_of_pos hr.1] at hz
      rw [mem_ball_zero_iff, hz]
      exact hr.2
    exact Real.posLog_le_posLog (by linarith [norm_nonneg (f z)])
      ((hM z hz_ball).trans (le_max_left M 0))
  refine ⟨hbdd_sub, fun f hf ↦ hbdd_sub hf ⟨‖f‖, fun z hz ↦ ?_⟩⟩
  rw [RudinRCA.Chapter11.extendZero_apply_of_mem f hz]
  exact BoundedContinuousFunction.norm_coe_le_norm f ⟨z, hz⟩

/-! ### 15.23 & 15.16: Blaschke Condition for the Nevanlinna Class, Uniqueness Corollary, and Section 15.16 Bridge -/

/-- Helper: every `ℕ∞`-valued family is unconditionally `Summable` in the order topology. -/
private lemma enat_summable {ι : Type*} (g : ι → ℕ∞) : Summable g :=
  (hasSum_of_isLUB (⨆ s : Finset ι, ∑ i ∈ s, g i) (isLUB_ciSup ⟨⊤, fun _ _ ↦ le_top⟩)).summable

/-- Helper: finite partial sums of an `ℕ∞`-valued family are bounded by `∑' i, g i`. -/
private lemma enat_sum_le_tsum {ι : Type*} (s : Finset ι) (g : ι → ℕ∞) :
    ∑ i ∈ s, g i ≤ ∑' i, g i :=
  sum_le_hasSum s (fun _ _ ↦ bot_le) (enat_summable g).hasSum

/-- Helper: for any finite subset `s : Finset α` and family `c : α → ℝ` with `∀ x ∈ s, c x < 1`,
eventually as `r → 1⁻` we have `∀ x ∈ s, c x < r`. -/
private lemma eventually_nhdsLT_one_forall_mem_lt {α : Type*} (s : Finset α) (c : α → ℝ)
    (hc : ∀ x ∈ s, c x < 1) :
    ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ x ∈ s, c x < r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Eventually.of_forall (by simp)
  | insert x₀ t hx₀ ih =>
    have hx₀_lt : c x₀ < 1 := hc x₀ (Finset.mem_insert_self x₀ t)
    have ht_lt : ∀ x ∈ t, c x < 1 := fun x hx ↦ hc x (Finset.mem_insert_of_mem hx)
    filter_upwards [Ioo_mem_nhdsLT hx₀_lt, ih ht_lt] with r hr₀ hrt x hx
    rcases Finset.mem_insert.mp hx with rfl | hxt
    · exact hr₀.1
    · exact hrt x hxt

/-- Core uniform zero-sum estimate for Theorem 15.23: if `f ∈ NevanlinnaClass` is not identically
zero on `Metric.ball 0 1`, there exists `M ≥ 0` bounding `∑ z ∈ s, m(f, z) * (1 - ‖z‖)` over all
finite subsets `s` of `Metric.ball 0 1 \ {0}`. -/
private lemma nevanlinna_sum_zeros_le {f : ℂ → ℂ} (hfN : f ∈ NevanlinnaClass)
    (hnonzero : ∃ z₀ ∈ Metric.ball (0 : ℂ) 1, f z₀ ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ s : Finset ℂ, (∀ z ∈ s, z ∈ Metric.ball (0 : ℂ) 1 ∧ z ≠ 0) →
        ∑ z ∈ s, (analyticOrderNatAt f z : ℝ) * (1 - ‖z‖) ≤ M := by
  classical
  obtain ⟨hf, C, hC⟩ := hfN
  let k : ℕ := analyticOrderNatAt f 0
  obtain ⟨h, hh_diff, hh0, hf_fac, hh_ord⟩ := disc_remove_zero_at_origin zero_lt_one hf hnonzero
  let M : ℝ := max 0 ((k : ℝ) * Real.log 2 + C - Real.log ‖h 0‖)
  have hM_nn : 0 ≤ M := le_max_left _ _
  -- Step 1: Upper bound on `circleAverage (log ‖h ·‖) 0 r` for `1 / 2 ≤ r < 1`
  have hcavg_h_le : ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
      Real.circleAverage (fun z ↦ Real.log ‖h z‖) 0 r ≤ (k : ℝ) * Real.log 2 + C := by
    intro r hr_half hr1
    have hr_pos : 0 < r := by linarith
    have hcint_h : CircleIntegrable (fun z ↦ Real.log ‖h z‖) 0 r :=
      (theorem15_18 hr_pos hr1 hh_diff hh0).1.1
    have hcint_fpos : CircleIntegrable (fun z ↦ Real.posLog ‖f z‖) 0 r :=
      circleIntegrable_posLog_norm_of_differentiableOn hf hr_pos.le hr1
    have hcint_rhs : CircleIntegrable (fun z ↦ (k : ℝ) * Real.log 2 + Real.posLog ‖f z‖) 0 r :=
      intervalIntegrable_const.add hcint_fpos
    have hpt : ∀ z ∈ Metric.sphere (0 : ℂ) |r|,
        Real.log ‖h z‖ ≤ (k : ℝ) * Real.log 2 + Real.posLog ‖f z‖ := by
      intro z hz
      rw [abs_of_pos hr_pos] at hz
      have hzr : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
      have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff, hzr]
        exact hr1
      have hfz_norm : ‖f z‖ = r ^ k * ‖h z‖ := by
        rw [hf_fac z hz_ball, norm_mul, norm_pow, hzr]
      have hrinv_le : r⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hr_pos two_pos]
        linarith
      have hh_le_2kf : ‖h z‖ ≤ (2 : ℝ) ^ k * ‖f z‖ := by
        have h1 : ‖h z‖ = r⁻¹ ^ k * ‖f z‖ := by
          rw [hfz_norm, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hr_pos.ne', one_pow, one_mul]
        rw [h1]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (inv_nonneg.mpr hr_pos.le) hrinv_le k) (norm_nonneg _)
      have hpos2k : Real.posLog ((2 : ℝ) ^ k) = (k : ℝ) * Real.log 2 := by
        rw [Real.posLog_pow, Real.posLog_eq_log (by norm_num)]
      calc
        Real.log ‖h z‖ ≤ Real.posLog ‖h z‖ := le_max_right 0 _
        _ ≤ Real.posLog ((2 : ℝ) ^ k * ‖f z‖) :=
          Real.posLog_le_posLog (by linarith [norm_nonneg (h z)]) hh_le_2kf
        _ ≤ Real.posLog ((2 : ℝ) ^ k) + Real.posLog ‖f z‖ := Real.posLog_mul
        _ = (k : ℝ) * Real.log 2 + Real.posLog ‖f z‖ := by rw [hpos2k]
    calc
      Real.circleAverage (fun z ↦ Real.log ‖h z‖) 0 r
          ≤ Real.circleAverage (fun z ↦ (k : ℝ) * Real.log 2 + Real.posLog ‖f z‖) 0 r :=
        Real.circleAverage_mono hcint_h hcint_rhs hpt
      _ = (k : ℝ) * Real.log 2 + Real.circleAverage (fun z ↦ Real.posLog ‖f z‖) 0 r := by
        have hcint_const : CircleIntegrable (fun _ : ℂ ↦ (k : ℝ) * Real.log 2) 0 r :=
          intervalIntegrable_const
        rw [Real.circleAverage_fun_add hcint_const hcint_fpos, Real.circleAverage_const]
      _ ≤ (k : ℝ) * Real.log 2 + C := add_le_add le_rfl (hC r ⟨hr_pos, hr1⟩)
  -- Step 2: Uniform bound over finite subsets `s ⊆ ball 0 1 \ {0}`
  refine ⟨M, hM_nn, fun s hs ↦ ?_⟩
  let s' : Finset ℂ := s.filter (fun z ↦ 0 < analyticOrderNatAt f z)
  have hs' : ∀ z ∈ s', z ∈ Metric.ball (0 : ℂ) 1 ∧ z ≠ 0 ∧ 0 < analyticOrderNatAt f z := by
    intro z hz
    obtain ⟨hzs, hpos⟩ := Finset.mem_filter.mp hz
    exact ⟨(hs z hzs).1, (hs z hzs).2, hpos⟩
  have hsum_s' : ∑ z ∈ s, (analyticOrderNatAt f z : ℝ) * (1 - ‖z‖) =
      ∑ z ∈ s', (analyticOrderNatAt f z : ℝ) * (1 - ‖z‖) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    by_cases hpos : 0 < analyticOrderNatAt f z
    · simp [hpos]
    · have h0 : analyticOrderNatAt f z = 0 := Nat.eq_zero_of_not_pos hpos
      simp [h0]
  rw [hsum_s']
  have htend : Tendsto
      (fun r : ℝ ↦ ∑ z ∈ s', (analyticOrderNatAt f z : ℝ) * Real.log (r / ‖z‖))
      (𝓝[<] 1) (𝓝 (∑ z ∈ s', (analyticOrderNatAt f z : ℝ) * (-Real.log ‖z‖))) := by
    refine tendsto_finsetSum s' fun z hz ↦ ?_
    have hz0 : z ≠ 0 := (hs' z hz).2.1
    have hnorm_ne : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
    have hdiv_tend : Tendsto (fun r : ℝ ↦ r / ‖z‖) (𝓝[<] 1) (𝓝 (1 / ‖z‖)) :=
      (tendsto_id.div_const ‖z‖).mono_left nhdsWithin_le_nhds
    have hlog_tend : Tendsto (fun r : ℝ ↦ Real.log (r / ‖z‖)) (𝓝[<] 1) (𝓝 (-Real.log ‖z‖)) := by
      have h1 : Real.log (1 / ‖z‖) = -Real.log ‖z‖ := by rw [one_div, Real.log_inv]
      rw [← h1]
      exact (Real.continuousAt_log (one_div_ne_zero hnorm_ne)).tendsto.comp hdiv_tend
    exact tendsto_const_nhds.mul hlog_tend
  have hev_le_M : ∀ᶠ r : ℝ in 𝓝[<] 1,
      ∑ z ∈ s', (analyticOrderNatAt f z : ℝ) * Real.log (r / ‖z‖) ≤ M := by
    have hev_all := eventually_nhdsLT_one_forall_mem_lt s' (fun z ↦ ‖z‖)
      (fun z hz ↦ mem_ball_zero_iff.mp (hs' z hz).1)
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1), hev_all] with r hrI hzr_lt
    have hr_pos : 0 < r := by linarith [hrI.1]
    obtain ⟨_, ⟨M_r, b, hb_mem, hb_mult⟩, h18_eq⟩ := theorem15_18 hr_pos hrI.2 hh_diff hh0
    have hjensen_r := (h18_eq M_r b hb_mem hb_mult).2
    have hh0_pos : 0 < ‖h 0‖ := norm_pos_iff.mpr hh0
    have hprod_pos : 0 < ∏ j : Fin M_r, (r / ‖b j‖) :=
      Finset.prod_pos fun j _ ↦ div_pos hr_pos (norm_pos_iff.mpr (hb_mem j).2)
    have hlog_jensen : Real.log ‖h 0‖ + ∑ j : Fin M_r, Real.log (r / ‖b j‖) =
        Real.circleAverage (fun z ↦ Real.log ‖h z‖) 0 r := by
      have hl := congrArg Real.log hjensen_r
      rw [Real.log_mul hh0_pos.ne' hprod_pos.ne',
        Real.log_prod (fun j _ ↦ (div_pos hr_pos (norm_pos_iff.mpr (hb_mem j).2)).ne'),
        Real.log_exp] at hl
      exact hl
    let T : Finset ℂ := Finset.univ.image b
    have hT_sum : ∑ j : Fin M_r, Real.log (r / ‖b j‖) =
        ∑ z ∈ T, (analyticOrderNatAt h z : ℝ) * Real.log (r / ‖z‖) := by
      rw [← Finset.sum_fiberwise_of_maps_to
        (fun j _ ↦ Finset.mem_image_of_mem b (Finset.mem_univ j))]
      refine Finset.sum_congr rfl fun z hzT ↦ ?_
      obtain ⟨j₀, _, rfl⟩ := Finset.mem_image.mp hzT
      have hcongr : (∑ j ∈ Finset.univ.filter (fun j ↦ b j = b j₀), Real.log (r / ‖b j‖)) =
          ∑ _j ∈ Finset.univ.filter (fun j ↦ b j = b j₀), Real.log (r / ‖b j₀‖) :=
        Finset.sum_congr rfl fun j hj ↦ by rw [(Finset.mem_filter.mp hj).2]
      rw [hcongr, Finset.sum_const, nsmul_eq_mul, hb_mult (b j₀) (hb_mem j₀).1]
    have hs'_sub_T : s' ⊆ T := by
      intro z hz
      obtain ⟨hz_ball, hz0, hpos_f⟩ := hs' z hz
      have hord_eq : analyticOrderNatAt h z = analyticOrderNatAt f z := hh_ord z ⟨hz_ball, hz0⟩
      have hz_cl : z ∈ Metric.closedBall (0 : ℂ) r :=
        mem_closedBall_zero_iff.mpr (hzr_lt z hz).le
      have hcard_pos : 0 < (Finset.univ.filter (fun j ↦ b j = z)).card := by
        rw [hb_mult z hz_cl, hord_eq]
        exact hpos_f
      obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard_pos
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, (Finset.mem_filter.mp hj).2⟩
    have hs'_eq_h : ∑ z ∈ s', (analyticOrderNatAt f z : ℝ) * Real.log (r / ‖z‖) =
        ∑ z ∈ s', (analyticOrderNatAt h z : ℝ) * Real.log (r / ‖z‖) := by
      refine Finset.sum_congr rfl fun z hz ↦ ?_
      rw [hh_ord z ⟨(hs' z hz).1, (hs' z hz).2.1⟩]
    have hle_T : ∑ z ∈ s', (analyticOrderNatAt h z : ℝ) * Real.log (r / ‖z‖) ≤
        ∑ z ∈ T, (analyticOrderNatAt h z : ℝ) * Real.log (r / ‖z‖) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hs'_sub_T fun z hzT _ ↦ ?_
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hzT
      have hbj_pos : 0 < ‖b j‖ := norm_pos_iff.mpr (hb_mem j).2
      have hbj_le : ‖b j‖ ≤ r := mem_closedBall_zero_iff.mp (hb_mem j).1
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg ((one_le_div hbj_pos).mpr hbj_le))
    have hcavg_bound := hcavg_h_le r hrI.1.le hrI.2
    have hT_le_M : ∑ z ∈ T, (analyticOrderNatAt h z : ℝ) * Real.log (r / ‖z‖) ≤ M := by
      have h1 : ∑ z ∈ T, (analyticOrderNatAt h z : ℝ) * Real.log (r / ‖z‖) ≤
          (k : ℝ) * Real.log 2 + C - Real.log ‖h 0‖ := by
        linarith [hlog_jensen, hT_sum, hcavg_bound]
      exact h1.trans (le_max_right _ _)
    rw [hs'_eq_h]
    exact hle_T.trans hT_le_M
  have hlog_sum_le : ∑ z ∈ s', (analyticOrderNatAt f z : ℝ) * (-Real.log ‖z‖) ≤ M :=
    le_of_tendsto htend hev_le_M
  refine (Finset.sum_le_sum fun z hz ↦ ?_).trans hlog_sum_le
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr (hs' z hz).2.1
  have h1m_le : 1 - ‖z‖ ≤ -Real.log ‖z‖ := by
    linarith [Real.log_le_sub_one_of_pos hz_pos]
  exact mul_le_mul_of_nonneg_left h1m_le (Nat.cast_nonneg _)

/-- **Theorem 15.23 (Blaschke Zero Condition for the Nevanlinna Class and Uniqueness Corollary)**:
- `(a)` If `f ∈ NevanlinnaClass` is not identically zero on `Metric.ball 0 1`, then:
  1. There exists `M : ℝ` such that for every finite list `(N, a)` in `Metric.ball 0 1 \ {0}`
     bounded by multiplicity (`∀ z, (filter (a · = z)).card ≤ analyticOrderNatAt f z`),
     `∑ i : Fin N, (1 - ‖a i‖) ≤ M`;
  2. The family `u ↦ (analyticOrderNatAt f u : ℝ) * (1 - ‖u‖)` is unconditionally `Summable` on
     `{z : ℂ // z ∈ Metric.ball 0 1 ∧ z ≠ 0}`;
  3. For any sequence `a : ℕ → ℂ` in `Metric.ball 0 1 \ {0}` with
     `∀ z, (∑' n, if a n = z then (1 : ℕ∞) else 0) ≤ analyticOrderAt f z`,
     `Summable (fun n ↦ 1 - ‖a n‖)`.
- `(b)` Unnumbered uniqueness corollary: if `f ∈ NevanlinnaClass` (in particular if
  `f ∈ RudinRCA.Chapter11.HInfty`) vanishes along a sequence `a : ℕ → ℂ` in `Metric.ball 0 1 \ {0}`
  with `¬ Summable (fun n ↦ 1 - ‖a n‖)` (either pairwise distinct or with repetitions bounded by
  `analyticOrderAt f` when `f` is nonzero), then `f` vanishes identically on `Metric.ball 0 1`
  (and `f = 0` in `HInfty`). -/
theorem theorem15_23 :
    -- (a) Necessity of the Blaschke condition for nonzero `f ∈ NevanlinnaClass`
    (∀ {f : ℂ → ℂ}, f ∈ NevanlinnaClass → (∃ z₀ ∈ Metric.ball (0 : ℂ) 1, f z₀ ≠ 0) →
      (∃ M : ℝ, ∀ (N : ℕ) (a : Fin N → ℂ),
        (∀ i, a i ∈ Metric.ball (0 : ℂ) 1 ∧ a i ≠ 0) →
        (∀ z : ℂ, (Finset.univ.filter (fun i ↦ a i = z)).card ≤ analyticOrderNatAt f z) →
        ∑ i : Fin N, (1 - ‖a i‖) ≤ M) ∧
      Summable (fun u : {z : ℂ // z ∈ Metric.ball (0 : ℂ) 1 ∧ z ≠ 0} ↦
        (analyticOrderNatAt f u.1 : ℝ) * (1 - ‖u.1‖)) ∧
      (∀ (a : ℕ → ℂ),
        (∀ n, a n ∈ Metric.ball (0 : ℂ) 1 ∧ a n ≠ 0) →
        (∀ z : ℂ, (∑' n : ℕ, if a n = z then (1 : ℕ∞) else 0) ≤ analyticOrderAt f z) →
        Summable (fun n ↦ 1 - ‖a n‖))) ∧
    -- (b) Uniqueness corollary for `NevanlinnaClass` and `HInfty`
    ((∀ {f : ℂ → ℂ} {a : ℕ → ℂ},
        f ∈ NevanlinnaClass →
        (∀ n, a n ∈ Metric.ball (0 : ℂ) 1 ∧ a n ≠ 0) →
        ((∃ z₀ ∈ Metric.ball (0 : ℂ) 1, f z₀ ≠ 0) →
          ∀ z : ℂ, (∑' n : ℕ, if a n = z then (1 : ℕ∞) else 0) ≤ analyticOrderAt f z) →
        ¬ Summable (fun n ↦ 1 - ‖a n‖) →
        ∀ z ∈ Metric.ball (0 : ℂ) 1, f z = 0) ∧
      (∀ {f : ℂ → ℂ} {a : ℕ → ℂ},
        f ∈ NevanlinnaClass →
        (∀ n, a n ∈ Metric.ball (0 : ℂ) 1 ∧ a n ≠ 0) →
        Function.Injective a →
        (∀ n, f (a n) = 0) →
        ¬ Summable (fun n ↦ 1 - ‖a n‖) →
        ∀ z ∈ Metric.ball (0 : ℂ) 1, f z = 0) ∧
      (∀ {f : BoundedContinuousFunction (Metric.ball (0 : ℂ) 1) ℂ} {a : ℕ → ℂ},
        f ∈ RudinRCA.Chapter11.HInfty →
        (ha : ∀ n, a n ∈ Metric.ball (0 : ℂ) 1 ∧ a n ≠ 0) →
        Function.Injective a →
        (∀ n, f ⟨a n, (ha n).1⟩ = 0) →
        ¬ Summable (fun n ↦ 1 - ‖a n‖) →
        f = 0)) := by
  classical
  have hpart_a : ∀ {f : ℂ → ℂ}, f ∈ NevanlinnaClass → (∃ z₀ ∈ Metric.ball (0 : ℂ) 1, f z₀ ≠ 0) →
      (∃ M : ℝ, ∀ (N : ℕ) (a : Fin N → ℂ),
        (∀ i, a i ∈ Metric.ball (0 : ℂ) 1 ∧ a i ≠ 0) →
        (∀ z : ℂ, (Finset.univ.filter (fun i ↦ a i = z)).card ≤ analyticOrderNatAt f z) →
        ∑ i : Fin N, (1 - ‖a i‖) ≤ M) ∧
      Summable (fun u : {z : ℂ // z ∈ Metric.ball (0 : ℂ) 1 ∧ z ≠ 0} ↦
        (analyticOrderNatAt f u.1 : ℝ) * (1 - ‖u.1‖)) ∧
      (∀ (a : ℕ → ℂ),
        (∀ n, a n ∈ Metric.ball (0 : ℂ) 1 ∧ a n ≠ 0) →
        (∀ z : ℂ, (∑' n : ℕ, if a n = z then (1 : ℕ∞) else 0) ≤ analyticOrderAt f z) →
        Summable (fun n ↦ 1 - ‖a n‖)) := by
    intro f hfN hnonzero
    obtain ⟨M, _, hM_set⟩ := nevanlinna_sum_zeros_le hfN hnonzero
    have hfin_list : ∀ (N : ℕ) (a : Fin N → ℂ),
        (∀ i, a i ∈ Metric.ball (0 : ℂ) 1 ∧ a i ≠ 0) →
        (∀ z : ℂ, (Finset.univ.filter (fun i ↦ a i = z)).card ≤ analyticOrderNatAt f z) →
        ∑ i : Fin N, (1 - ‖a i‖) ≤ M := by
      intro N a ha hmult
      let s : Finset ℂ := Finset.univ.image a
      have hs : ∀ z ∈ s, z ∈ Metric.ball (0 : ℂ) 1 ∧ z ≠ 0 := by
        intro z hz
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
        exact ha i
      have hgroup : ∑ i : Fin N, (1 - ‖a i‖) =
          ∑ z ∈ s, ((Finset.univ.filter (fun i ↦ a i = z)).card : ℝ) * (1 - ‖z‖) := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (fun i _ ↦ Finset.mem_image_of_mem a (Finset.mem_univ i))]
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        have hcongr : (∑ i ∈ Finset.univ.filter (fun i ↦ a i = z), (1 - ‖a i‖)) =
            ∑ _i ∈ Finset.univ.filter (fun i ↦ a i = z), (1 - ‖z‖) :=
          Finset.sum_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.mp hi).2]
        rw [hcongr, Finset.sum_const, nsmul_eq_mul]
      rw [hgroup]
      refine (Finset.sum_le_sum fun z hz ↦ ?_).trans (hM_set s hs)
      have hz1 : 0 ≤ 1 - ‖z‖ := sub_nonneg.mpr (mem_ball_zero_iff.mp (hs z hz).1).le
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hmult z)) hz1
    have hsum_uncond : Summable (fun u : {z : ℂ // z ∈ Metric.ball (0 : ℂ) 1 ∧ z ≠ 0} ↦
        (analyticOrderNatAt f u.1 : ℝ) * (1 - ‖u.1‖)) := by
      refine summable_of_sum_le (c := M) (fun u ↦ ?_) (fun t ↦ ?_)
      · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (mem_ball_zero_iff.mp u.2.1).le)
      · let s : Finset ℂ := t.image Subtype.val
        have hs : ∀ z ∈ s, z ∈ Metric.ball (0 : ℂ) 1 ∧ z ≠ 0 := by
          intro z hz
          obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
          exact u.2
        have hinj : (t : Set {z : ℂ // z ∈ Metric.ball (0 : ℂ) 1 ∧ z ≠ 0}).InjOn Subtype.val :=
          fun _ _ _ _ h ↦ Subtype.ext h
        rw [← Finset.sum_image (f := fun z : ℂ ↦ (analyticOrderNatAt f z : ℝ) * (1 - ‖z‖)) hinj]
        exact hM_set s hs
    have hseq_sum : ∀ (a : ℕ → ℂ),
        (∀ n, a n ∈ Metric.ball (0 : ℂ) 1 ∧ a n ≠ 0) →
        (∀ z : ℂ, (∑' n : ℕ, if a n = z then (1 : ℕ∞) else 0) ≤ analyticOrderAt f z) →
        Summable (fun n ↦ 1 - ‖a n‖) := by
      intro a ha hmult
      obtain ⟨z₀, hz₀_ball, hfz₀⟩ := hnonzero
      refine summable_of_sum_range_le
        (fun n ↦ sub_nonneg.mpr (mem_ball_zero_iff.mp (ha n).1).le) (c := M) fun N ↦ ?_
      let a_fin : Fin N → ℂ := fun i ↦ a i.1
      have ha_fin : ∀ i : Fin N, a_fin i ∈ Metric.ball (0 : ℂ) 1 ∧ a_fin i ≠ 0 :=
        fun i ↦ ha i.1
      have hmult_fin : ∀ z : ℂ,
          (Finset.univ.filter (fun i : Fin N ↦ a_fin i = z)).card ≤ analyticOrderNatAt f z := by
        intro z
        by_cases hcard0 : (Finset.univ.filter (fun i : Fin N ↦ a_fin i = z)).card = 0
        · rw [hcard0]
          exact Nat.zero_le _
        · obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcard0)
          have hz_eq : a i₀.1 = z := (Finset.mem_filter.mp hi₀).2
          have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := hz_eq ▸ (ha i₀.1).1
          have hne_top : analyticOrderAt f z ≠ ⊤ :=
            analyticOrderAt_ne_top_on_ball hfN.1 hz₀_ball hfz₀ hz_ball
          have hcast_ord : (analyticOrderNatAt f z : ℕ∞) = analyticOrderAt f z :=
            ENat.natCast_toNat hne_top
          have hcard_enat : (((Finset.univ.filter (fun i : Fin N ↦ a_fin i = z)).card : ℕ) : ℕ∞) =
              ∑ n ∈ Finset.range N, (if a n = z then (1 : ℕ∞) else 0) := by
            rw [Finset.card_filter, Nat.cast_sum]
            refine Finset.sum_bij (fun (i : Fin N) _ ↦ i.1)
              (fun i _ ↦ Finset.mem_range.mpr i.2)
              (fun i _ j _ h ↦ Fin.ext h)
              (fun n hn ↦ ⟨⟨n, Finset.mem_range.mp hn⟩, Finset.mem_univ _, rfl⟩)
              (fun i _ ↦ by dsimp [a_fin]; split_ifs <;> simp)
          have hle_enat :
              (((Finset.univ.filter (fun i : Fin N ↦ a_fin i = z)).card : ℕ) : ℕ∞) ≤
                (analyticOrderNatAt f z : ℕ∞) := by
            rw [hcard_enat, hcast_ord]
            exact (enat_sum_le_tsum (Finset.range N) _).trans (hmult z)
          exact ENat.natCast_le_natCast.mp hle_enat
      have hsum_eq : ∑ n ∈ Finset.range N, (1 - ‖a n‖) = ∑ i : Fin N, (1 - ‖a_fin i‖) := by
        refine (Finset.sum_bij (fun (i : Fin N) _ ↦ i.1)
          (fun i _ ↦ Finset.mem_range.mpr i.2)
          (fun i _ j _ h ↦ Fin.ext h)
          (fun n hn ↦ ⟨⟨n, Finset.mem_range.mp hn⟩, Finset.mem_univ _, rfl⟩)
          (fun _ _ ↦ rfl)).symm
      rw [hsum_eq]
      exact hfin_list N a_fin ha_fin hmult_fin
    exact ⟨⟨M, hfin_list⟩, hsum_uncond, hseq_sum⟩
  have huniq_gen : ∀ {f : ℂ → ℂ} {a : ℕ → ℂ},
      f ∈ NevanlinnaClass →
      (∀ n, a n ∈ Metric.ball (0 : ℂ) 1 ∧ a n ≠ 0) →
      ((∃ z₀ ∈ Metric.ball (0 : ℂ) 1, f z₀ ≠ 0) →
        ∀ z : ℂ, (∑' n : ℕ, if a n = z then (1 : ℕ∞) else 0) ≤ analyticOrderAt f z) →
      ¬ Summable (fun n ↦ 1 - ‖a n‖) →
      ∀ z ∈ Metric.ball (0 : ℂ) 1, f z = 0 := by
    intro f a hfN ha hmult hdiv z hz
    by_contra hfz
    exact hdiv ((hpart_a hfN ⟨z, hz, hfz⟩).2.2 a ha (hmult ⟨z, hz, hfz⟩))
  have huniq_inj : ∀ {f : ℂ → ℂ} {a : ℕ → ℂ},
      f ∈ NevanlinnaClass →
      (∀ n, a n ∈ Metric.ball (0 : ℂ) 1 ∧ a n ≠ 0) →
      Function.Injective a →
      (∀ n, f (a n) = 0) →
      ¬ Summable (fun n ↦ 1 - ‖a n‖) →
      ∀ z ∈ Metric.ball (0 : ℂ) 1, f z = 0 := by
    intro f a hfN ha hinj hzero hdiv
    refine huniq_gen hfN ha (fun _ z ↦ ?_) hdiv
    by_cases hex : ∃ n₀, a n₀ = z
    · obtain ⟨n₀, rfl⟩ := hex
      have htsum_eq1 : (∑' n : ℕ, if a n = a n₀ then (1 : ℕ∞) else 0) = 1 := by
        rw [tsum_eq_single n₀]
        · simp
        · intro n hn
          have hne : a n ≠ a n₀ := fun h ↦ hn (hinj h)
          simp [hne]
      rw [htsum_eq1]
      have hana : AnalyticAt ℂ f (a n₀) :=
        (hfN.1.analyticOnNhd Metric.isOpen_ball) (a n₀) (ha n₀).1
      have hne0 : analyticOrderAt f (a n₀) ≠ 0 := hana.analyticOrderAt_ne_zero.mpr (hzero n₀)
      exact Order.one_le_iff_ne_zero.mpr hne0
    · simp only [not_exists] at hex
      have htsum0 : (∑' n : ℕ, if a n = z then (1 : ℕ∞) else 0) = 0 := by
        simp only [hex, ↓reduceIte, tsum_zero]
      rw [htsum0]
      exact bot_le
  have huniq_HInfty : ∀ {f : BoundedContinuousFunction (Metric.ball (0 : ℂ) 1) ℂ} {a : ℕ → ℂ},
      f ∈ RudinRCA.Chapter11.HInfty →
      (ha : ∀ n, a n ∈ Metric.ball (0 : ℂ) 1 ∧ a n ≠ 0) →
      Function.Injective a →
      (∀ n, f ⟨a n, (ha n).1⟩ = 0) →
      ¬ Summable (fun n ↦ 1 - ‖a n‖) →
      f = 0 := by
    intro f a hfH ha hinj hzero hdiv
    have hfN : RudinRCA.Chapter11.extendZero f ∈ NevanlinnaClass :=
      theorem15_22.2 f hfH
    have hext_zero : ∀ n, RudinRCA.Chapter11.extendZero f (a n) = 0 := by
      intro n
      rw [RudinRCA.Chapter11.extendZero_apply_of_mem f (ha n).1]
      exact hzero n
    have hall0 := huniq_inj hfN ha hinj hext_zero hdiv
    ext ⟨z, hz⟩
    change f ⟨z, hz⟩ = 0
    rw [← RudinRCA.Chapter11.extendZero_apply_of_mem f hz]
    exact hall0 z hz
  exact ⟨hpart_a, huniq_gen, huniq_inj, huniq_HInfty⟩

/-- **15.16 (Expository Bridge — Growth Conditions vs. Zero Distributions)**:
Packages Rudin's Section 15.16 transition from the purely topological isolation of interior zeros on
arbitrary regions (`zeros_have_no_accumulation` `15.1`, which imposes no quantitative boundary or
radial growth restriction) to the quantitative Jensen-formula constraints developed in `15.18`,
`15.20`, and `15.23`:
1. Interior zero isolation (`15.1`),
2. Jensen's identity (`15.18`) relating modulus growth on `sphere 0 r` to zeros in `closedBall 0 r`,
3. Entire order-growth control of `entireZeroCount` (`15.20`),
4. Nevanlinna/`H^∞` Blaschke sum restriction `∑ (1 - ‖a_n‖) < ∞` (`15.23`). -/
theorem theorem15_16 :
    -- (1) Qualitative interior zero isolation on any region (15.1)
    (∀ {Ω : Set ℂ} {f : ℂ → ℂ},
      IsOpen Ω → IsPreconnected Ω → DifferentiableOn ℂ f Ω →
      (∃ w ∈ Ω, f w ≠ 0) → ∀ {z : ℂ}, z ∈ Ω → z ∉ closure ({w | f w = 0} \ {z})) ∧
    -- (2) Jensen's quantitative zero-vs-growth formula on discs (15.18)
    (∀ {r R : ℝ} {f : ℂ → ℂ}, 0 < r → r < R →
      DifferentiableOn ℂ f (Metric.ball 0 R) → f 0 ≠ 0 →
      ∀ (N : ℕ) (a : Fin N → ℂ),
        (∀ i, a i ∈ Metric.closedBall (0 : ℂ) r ∧ a i ≠ 0) →
        (∀ z ∈ Metric.closedBall (0 : ℂ) r,
          (Finset.univ.filter (fun i ↦ a i = z)).card = analyticOrderNatAt f z) →
        ‖f 0‖ * (∏ i : Fin N, (r / ‖a i‖)) =
          Real.exp (Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 r)) ∧
    -- (3) Entire growth order bounds zero counting function (15.20)
    (∀ {f : ℂ → ℂ}, Differentiable ℂ f → f 0 = 1 → ∀ r : ℝ, 0 < r →
      (entireZeroCount f r : ℝ) * Real.log 2 ≤ Real.log (entireMaxModulus f (2 * r))) ∧
    -- (4) Nevanlinna / H^∞ radial growth forces the Blaschke condition on zeros in U (15.23)
    (∀ {f : ℂ → ℂ}, f ∈ NevanlinnaClass → (∃ z₀ ∈ Metric.ball (0 : ℂ) 1, f z₀ ≠ 0) →
      Summable (fun u : {z : ℂ // z ∈ Metric.ball (0 : ℂ) 1 ∧ z ≠ 0} ↦
        (analyticOrderNatAt f u.1 : ℝ) * (1 - ‖u.1‖))) :=
  ⟨fun hΩ hc hf hnz _ hz ↦ zeros_have_no_accumulation hΩ hc hf hnz hz,
    fun hr hrR hf hf0 N a ha hmult ↦ ((theorem15_18 hr hrR hf hf0).2.2 N a ha hmult).2,
    theorem15_20.1,
    fun hfN hnz ↦ (theorem15_23.1 hfN hnz).2.1⟩

/-! ### 15.24: Radial Limits and Mean Log-Modulus of Blaschke Products (`theorem15_24`) -/

/-- Helper for 15.24: for every finite Blaschke product `B(z) = z ^ k * ∏_{i < N} b_{a_i}(z)`,
`circleAverage (log ‖B ·‖) 0 r → 0` as `r → 1⁻`. -/
private lemma circleAverage_log_norm_finite_blaschke_tendsto (k N : ℕ) (a : Fin N → ℂ)
    (ha : ∀ i, a i ∈ Metric.ball (0 : ℂ) 1 ∧ a i ≠ 0) :
    let B : ℂ → ℂ := fun z ↦ z ^ k * ∏ i : Fin N, blaschkeFactor (a i) z
    Tendsto (fun r : ℝ ↦ Real.circleAverage (fun z ↦ Real.log ‖B z‖) 0 r) (𝓝[<] 1) (𝓝 0) := by
  let P : ℂ → ℂ := fun z ↦ ∏ i : Fin N, blaschkeFactor (a i) z
  let B : ℂ → ℂ := fun z ↦ z ^ k * P z
  have hfinP := finite_blaschke_product 0 N a ha
  have hP_diff : DifferentiableOn ℂ P (Metric.ball (0 : ℂ) 1) := by
    simpa only [pow_zero, one_mul] using hfinP.2.2.1
  have hP_zero : ∀ z ∈ Metric.ball (0 : ℂ) 1, P z = 0 ↔ ∃ i, z = a i := by
    intro z hz
    simpa using hfinP.2.2.2.2.2.1 z hz
  have hP0_ord : analyticOrderNatAt P 0 = 0 := by
    simpa only [pow_zero, one_mul] using hfinP.2.2.2.2.2.2.1
  have hP_ord_nz : ∀ z ∈ Metric.ball (0 : ℂ) 1 \ {0},
      analyticOrderNatAt P z = (Finset.univ.filter (fun i ↦ a i = z)).card := by
    intro z hz
    simpa only [pow_zero, one_mul] using hfinP.2.2.2.2.2.2.2 z hz
  have hP0_norm : ‖P 0‖ = ∏ i : Fin N, ‖a i‖ := by
    have hP0_eq : P 0 = ∏ i : Fin N, (‖a i‖ : ℂ) :=
      Finset.prod_congr rfl fun i _ ↦ blaschkeFactor_zero (ha i).2
    rw [hP0_eq, norm_prod]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  have hP0_ne : P 0 ≠ 0 := by
    rw [← norm_ne_zero_iff, hP0_norm]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ norm_ne_zero_iff.mpr (ha i).2
  have hev_eq : ∀ᶠ r : ℝ in 𝓝[<] 1,
      Real.circleAverage (fun z ↦ Real.log ‖B z‖) 0 r = ((k + N : ℕ) : ℝ) * Real.log r := by
    have hev_a := eventually_nhdsLT_one_forall_mem_lt Finset.univ (fun i : Fin N ↦ ‖a i‖)
      (fun i _ ↦ mem_ball_zero_iff.mp (ha i).1)
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one, hev_a] with r hrI hlt_a
    have ha_cl : ∀ i : Fin N, a i ∈ Metric.closedBall (0 : ℂ) r ∧ a i ≠ 0 :=
      fun i ↦ ⟨mem_closedBall_zero_iff.mpr (hlt_a i (Finset.mem_univ i)).le, (ha i).2⟩
    have ha_mult : ∀ z ∈ Metric.closedBall (0 : ℂ) r,
        (Finset.univ.filter (fun i ↦ a i = z)).card = analyticOrderNatAt P z := by
      intro z hz_cl
      by_cases hz0 : z = 0
      · subst z
        rw [hP0_ord, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _
        exact (ha i).2
      · have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 :=
          Metric.closedBall_subset_ball hrI.2 hz_cl
        exact (hP_ord_nz z ⟨hz_ball, hz0⟩).symm
    have h18_P := theorem15_18 hrI.1 hrI.2 hP_diff hP0_ne
    have hjensen := (h18_P.2.2 N a ha_cl ha_mult).2
    have hlhs : ‖P 0‖ * (∏ i : Fin N, (r / ‖a i‖)) = Real.exp ((N : ℝ) * Real.log r) := by
      rw [hP0_norm, ← Finset.prod_mul_distrib]
      have hprod_r : (∏ i : Fin N, (‖a i‖ * (r / ‖a i‖))) = ∏ _i : Fin N, r :=
        Finset.prod_congr rfl fun i _ ↦ mul_div_cancel₀ r (norm_ne_zero_iff.mpr (ha i).2)
      rw [hprod_r, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [Real.exp_nat_mul, Real.exp_log hrI.1]
    have hcavg_P : Real.circleAverage (fun z ↦ Real.log ‖P z‖) 0 r = (N : ℝ) * Real.log r :=
      Real.exp_injective (hjensen.symm.trans hlhs)
    have hcongr_sp : Set.EqOn (fun z ↦ Real.log ‖B z‖)
        (fun z ↦ (k : ℝ) * Real.log r + Real.log ‖P z‖) (Metric.sphere (0 : ℂ) |r|) := by
      intro z hz
      rw [abs_of_pos hrI.1] at hz
      have hzr : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
      have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff, hzr]
        exact hrI.2
      have hPz_ne : P z ≠ 0 := by
        intro h0
        obtain ⟨i, rfl⟩ := (hP_zero z hz_ball).mp h0
        exact (hlt_a i (Finset.mem_univ i)).ne hzr
      dsimp [B]
      rw [norm_mul, norm_pow, hzr,
        Real.log_mul (pow_pos hrI.1 k).ne' (norm_ne_zero_iff.mpr hPz_ne), Real.log_pow]
    have hcint_const : CircleIntegrable (fun _ : ℂ ↦ (k : ℝ) * Real.log r) 0 r :=
      intervalIntegrable_const
    rw [Real.circleAverage_congr_sphere hcongr_sp,
      Real.circleAverage_fun_add hcint_const h18_P.1.1,
      Real.circleAverage_const, hcavg_P]
    push_cast
    ring
  have hlog_lim : Tendsto (fun r : ℝ ↦ ((k + N : ℕ) : ℝ) * Real.log r) (𝓝[<] 1) (𝓝 0) := by
    have hl : Tendsto Real.log (𝓝[<] 1) (𝓝 0) := by
      simpa only [Real.log_one] using
        (Real.continuousAt_log one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero] using tendsto_const_nhds.mul hl
  exact hlog_lim.congr' (hev_eq.mono fun r hr ↦ hr.symm)

/-- Helper for 15.24: for every convergent infinite Blaschke product
`B(z) = z ^ k * ∏' n, b_{a_n}(z)`, `circleAverage (log ‖B ·‖) 0 r → 0` as `r → 1⁻`. -/
private lemma circleAverage_log_norm_infinite_blaschke_tendsto (k : ℕ) {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ Metric.ball (0 : ℂ) 1 ∧ a n ≠ 0)
    (hsum : Summable (fun n ↦ 1 - ‖a n‖)) :
    let B : ℂ → ℂ := fun z ↦ z ^ k * ∏' n, blaschkeFactor (a n) z
    Tendsto (fun r : ℝ ↦ Real.circleAverage (fun z ↦ Real.log ‖B z‖) 0 r) (𝓝[<] 1) (𝓝 0) := by
  let F : ℕ → ℂ → ℂ := fun n z ↦ blaschkeFactor (a n) z
  let P : ℂ → ℂ := fun z ↦ ∏' n, F n z
  let B : ℂ → ℂ := fun z ↦ z ^ k * P z
  obtain ⟨_, hP_lim, _, hP_diff, hB_diff, hPB_norm, hP0_ne, _, _, _⟩ :=
    theorem15_21 k ha hsum
  -- Upper bound `circleAverage (log ‖B ·‖) 0 r ≤ 0` for `0 < r < 1`
  have hμ_nonpos : ∀ r : ℝ, 0 < r → r < 1 →
      Real.circleAverage (fun z ↦ Real.log ‖B z‖) 0 r ≤ 0 := by
    intro r hr hr1
    have hana_B : AnalyticOnNhd ℂ B (Metric.ball (0 : ℂ) 1) :=
      hB_diff.analyticOnNhd Metric.isOpen_ball
    have hsub : Metric.sphere (0 : ℂ) |r| ⊆ Metric.ball (0 : ℂ) 1 := by
      rw [abs_of_pos hr]
      exact Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_ball hr1)
    have hcint_B : CircleIntegrable (fun z ↦ Real.log ‖B z‖) 0 r :=
      (hana_B.mono hsub).meromorphicOn.circleIntegrable_log_norm
    refine Real.circleAverage_mono_on_of_le_circle hcint_B fun z hz ↦ ?_
    have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := hsub hz
    by_cases hBz0 : B z = 0
    · simp [hBz0]
    · exact Real.log_nonpos (norm_pos_iff.mpr hBz0).le (hPB_norm z hz_ball).2
  -- Tail factorization `P z = P_M z * R_M z` on `ball 0 1`
  let P_M : ℕ → ℂ → ℂ := fun M z ↦ ∏ n ∈ Finset.range M, F n z
  let B_M : ℕ → ℂ → ℂ := fun M z ↦ z ^ k * P_M M z
  let R_M : ℕ → ℂ → ℂ := fun M z ↦ ∏' m, F (m + M) z
  have hfac_P : ∀ (M : ℕ) {z : ℂ}, z ∈ Metric.ball (0 : ℂ) 1 → P z = P_M M z * R_M M z := by
    intro M z hz
    have ha_shift : ∀ m, a (m + M) ∈ Metric.ball (0 : ℂ) 1 ∧ a (m + M) ≠ 0 :=
      fun m ↦ ha (m + M)
    have hsum_shift : Summable (fun m ↦ 1 - ‖a (m + M)‖) :=
      (summable_nat_add_iff M).mpr hsum
    obtain ⟨_, hRM_lim, _, _, _, _, _, _, _, _⟩ := theorem15_21 0 ha_shift hsum_shift
    have hadd : Tendsto (fun K : ℕ ↦ M + K) Filter.atTop Filter.atTop := by
      simpa only [add_comm M] using tendsto_add_atTop_nat M
    have h1 : Tendsto (fun K : ℕ ↦ ∏ n ∈ Finset.range (M + K), F n z)
        Filter.atTop (𝓝 (P z)) :=
      (hP_lim.tendsto_at hz).comp hadd
    have h2 : Tendsto
        (fun K : ℕ ↦ (∏ n ∈ Finset.range M, F n z) * ∏ m ∈ Finset.range K, F (m + M) z)
        Filter.atTop (𝓝 (P_M M z * R_M M z)) :=
      tendsto_const_nhds.mul (hRM_lim.tendsto_at hz)
    have hseq_eq : (fun K : ℕ ↦ ∏ n ∈ Finset.range (M + K), F n z) =
        fun K : ℕ ↦ (∏ n ∈ Finset.range M, F n z) * ∏ m ∈ Finset.range K, F (m + M) z := by
      funext K
      rw [Finset.prod_range_add]
      congr 1
      refine Finset.prod_congr rfl fun m _ ↦ ?_
      rw [add_comm M m]
    rw [hseq_eq] at h1
    exact tendsto_nhds_unique h1 h2
  -- `Real.log ‖R_M M 0‖ → 0` as `M → ∞`
  have hlog_RM0_lim : Tendsto (fun M : ℕ ↦ Real.log ‖R_M M 0‖) Filter.atTop (𝓝 0) := by
    have h0_ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self zero_lt_one
    have hPM0_lim : Tendsto (fun M : ℕ ↦ P_M M 0) Filter.atTop (𝓝 (P 0)) :=
      hP_lim.tendsto_at h0_ball
    have hRM0_eq : ∀ M : ℕ, R_M M 0 = P 0 / P_M M 0 := by
      intro M
      have h0 := hfac_P M h0_ball
      have hPM0_ne : P_M M 0 ≠ 0 := by
        intro hzero
        apply hP0_ne
        change P 0 = 0
        rw [h0, hzero, zero_mul]
      exact eq_div_of_mul_eq hPM0_ne (by rw [mul_comm]; exact h0.symm)
    have hRM0_lim : Tendsto (fun M : ℕ ↦ R_M M 0) Filter.atTop (𝓝 1) := by
      have hdiv : Tendsto (fun M : ℕ ↦ P 0 / P_M M 0) Filter.atTop (𝓝 (P 0 / P 0)) :=
        tendsto_const_nhds.div hPM0_lim hP0_ne
      rw [div_self hP0_ne] at hdiv
      exact hdiv.congr (fun M ↦ (hRM0_eq M).symm)
    have hnorm_lim : Tendsto (fun M : ℕ ↦ ‖R_M M 0‖) Filter.atTop (𝓝 1) := by
      simpa only [norm_one] using hRM0_lim.norm
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hnorm_lim
  -- Conclude `Tendsto (circleAverage (log ‖B ·‖) 0 ·) (𝓝[<] 1) (𝓝 0)`
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlog_ev := (Metric.tendsto_nhds.mp hlog_RM0_lim) (ε / 2) (half_pos hε)
  obtain ⟨M, hM_dist⟩ := hlog_ev.exists
  have hRM0_gt : -(ε / 2) < Real.log ‖R_M M 0‖ := by
    rw [Real.dist_eq, sub_zero] at hM_dist
    linarith [(abs_lt.mp hM_dist).1]
  have ha_shift : ∀ m, a (m + M) ∈ Metric.ball (0 : ℂ) 1 ∧ a (m + M) ≠ 0 :=
    fun m ↦ ha (m + M)
  have hsum_shift : Summable (fun m ↦ 1 - ‖a (m + M)‖) :=
    (summable_nat_add_iff M).mpr hsum
  obtain ⟨_, _, _, hRM_diff, _, _, hRM0_ne, _, _, _⟩ := theorem15_21 0 ha_shift hsum_shift
  obtain ⟨hRM_mono, ρ, hρ_pos, _, hRM_near0⟩ :=
    jensen_circleAverage_mono_and_near_zero zero_lt_one hRM_diff hRM0_ne
  have hRM_cavg_ge : ∀ r : ℝ, 0 < r → r < 1 →
      Real.log ‖R_M M 0‖ ≤ Real.circleAverage (fun z ↦ Real.log ‖R_M M z‖) 0 r := by
    intro r hr hr1
    let s : ℝ := min (r / 2) (ρ / 2)
    have hs_pos : 0 < s := lt_min (half_pos hr) (half_pos hρ_pos)
    have hs_lt_r : s < r := (min_le_left _ _).trans_lt (half_lt_self hr)
    have hs_lt_ρ : s < ρ := (min_le_right _ _).trans_lt (half_lt_self hρ_pos)
    rw [← hRM_near0 s hs_pos hs_lt_ρ]
    exact hRM_mono s r hs_pos hs_lt_r hr1
  -- Express `B_M M` as a `Fin M` Blaschke product to apply `circleAverage_log_norm_finite_blaschke_tendsto`
  let a_fin : Fin M → ℂ := fun i ↦ a i.1
  have ha_fin : ∀ i : Fin M, a_fin i ∈ Metric.ball (0 : ℂ) 1 ∧ a_fin i ≠ 0 :=
    fun i ↦ ha i.1
  have hBM_eq_fin : B_M M = fun z ↦ z ^ k * ∏ i : Fin M, blaschkeFactor (a_fin i) z := by
    funext z
    dsimp [B_M, P_M, F, a_fin]
    congr 1
    exact (Finset.prod_bij (fun (i : Fin M) _ ↦ i.1)
      (fun i _ ↦ Finset.mem_range.mpr i.2)
      (fun i _ j _ h ↦ Fin.ext h)
      (fun n hn ↦ ⟨⟨n, Finset.mem_range.mp hn⟩, Finset.mem_univ _, rfl⟩)
      (fun _ _ ↦ rfl)).symm
  have hBM_lim : Tendsto (fun r : ℝ ↦ Real.circleAverage (fun z ↦ Real.log ‖B_M M z‖) 0 r)
      (𝓝[<] 1) (𝓝 0) := by
    rw [hBM_eq_fin]
    exact circleAverage_log_norm_finite_blaschke_tendsto k M a_fin ha_fin
  have hBM_ev := (Metric.tendsto_nhds.mp hBM_lim) (ε / 2) (half_pos hε)
  have hev_a := eventually_nhdsLT_one_forall_mem_lt Finset.univ (fun i : Fin M ↦ ‖a_fin i‖)
    (fun i _ ↦ mem_ball_zero_iff.mp (ha_fin i).1)
  have hfin_BM := finite_blaschke_product k M a_fin ha_fin
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one, hev_a, hBM_ev] with r hrI hlt_a hBM_dist
  -- Split `circleAverage (log ‖B ·‖) 0 r = circleAverage (log ‖B_M M ·‖) 0 r + circleAverage (log ‖R_M M ·‖) 0 r`
  have hBM_nz_sp : ∀ z ∈ Metric.sphere (0 : ℂ) r, B_M M z ≠ 0 := by
    intro z hz h0
    have hzr : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
    have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, hzr]
      exact hrI.2
    rw [hBM_eq_fin] at h0
    rcases (hfin_BM.2.2.2.2.2.1 z hz_ball).mp h0 with ⟨rfl, _⟩ | ⟨i, rfl⟩
    · rw [norm_zero] at hzr
      exact hrI.1.ne hzr
    · exact (hlt_a i (Finset.mem_univ i)).ne hzr
  have hBM_diff : DifferentiableOn ℂ (B_M M) (Metric.ball (0 : ℂ) 1) := by
    rw [hBM_eq_fin]
    exact hfin_BM.2.2.1
  have hBM_cint : CircleIntegrable (fun z ↦ Real.log ‖B_M M z‖) 0 r := by
    have hsub : Metric.sphere (0 : ℂ) |r| ⊆ Metric.ball (0 : ℂ) 1 := by
      rw [abs_of_pos hrI.1]
      exact Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_ball hrI.2)
    exact ((hBM_diff.analyticOnNhd Metric.isOpen_ball).mono hsub).meromorphicOn.circleIntegrable_log_norm
  have hBM_int : IntervalIntegrable
      (fun θ : ℝ ↦ Real.log ‖B_M M ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (circleIntegrable_iff_intervalIntegrable_neg_pi_pi _ r).mp hBM_cint
  have h18_RM := (theorem15_18 hrI.1 hrI.2 hRM_diff hRM0_ne).1
  have hfin_RM := h18_RM.2.2.2.1
  have hsplit_cavg : Real.circleAverage (fun z ↦ Real.log ‖B z‖) 0 r =
      Real.circleAverage (fun z ↦ Real.log ‖B_M M z‖) 0 r +
      Real.circleAverage (fun z ↦ Real.log ‖R_M M z‖) 0 r := by
    rw [circleAverage_zero_eq_neg_pi_pi, circleAverage_zero_eq_neg_pi_pi,
      circleAverage_zero_eq_neg_pi_pi]
    have hcongr : (∫ θ in (-Real.pi)..Real.pi,
          Real.log ‖B ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) =
        ∫ θ in (-Real.pi)..Real.pi,
          (Real.log ‖B_M M ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ +
            Real.log ‖R_M M ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hfin_RM.countable.ae_notMem MeasureTheory.volume] with θ hθ_not hθ_uIoc
      have hpi_le : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
      rw [Set.uIoc_of_le hpi_le] at hθ_uIoc
      have hθ_Icc : θ ∈ Set.Icc (-Real.pi) Real.pi := Set.Ioc_subset_Icc_self hθ_uIoc
      have hRM_ne : R_M M ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 :=
        fun h0 ↦ hθ_not ⟨hθ_Icc, h0⟩
      have hz_sp : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ Metric.sphere (0 : ℂ) r := by
        rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hrI.1, Complex.norm_exp_ofReal_mul_I, mul_one]
      have hz_ball : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hz_sp]
        exact hrI.2
      have hBM_ne : B_M M ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 :=
        hBM_nz_sp _ hz_sp
      have hB_eq : B ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
          B_M M ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
            R_M M ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
        dsimp [B, B_M]
        rw [hfac_P M hz_ball, mul_assoc]
      rw [hB_eq, norm_mul,
        Real.log_mul (norm_ne_zero_iff.mpr hBM_ne) (norm_ne_zero_iff.mpr hRM_ne)]
    rw [hcongr, intervalIntegral.integral_add hBM_int h18_RM.2.2.1, mul_add]
  have hBM_gt : -(ε / 2) < Real.circleAverage (fun z ↦ Real.log ‖B_M M z‖) 0 r := by
    rw [Real.dist_eq, sub_zero] at hBM_dist
    linarith [(abs_lt.mp hBM_dist).1]
  have hRM_gt : -(ε / 2) < Real.circleAverage (fun z ↦ Real.log ‖R_M M z‖) 0 r :=
    lt_of_lt_of_le hRM0_gt (hRM_cavg_ge r hrI.1 hrI.2)
  have hB_gt : -ε < Real.circleAverage (fun z ↦ Real.log ‖B z‖) 0 r := by
    linarith [hsplit_cavg, hBM_gt, hRM_gt]
  have hB_le0 : Real.circleAverage (fun z ↦ Real.log ‖B z‖) 0 r ≤ 0 :=
    hμ_nonpos r hrI.1 hrI.2
  rw [Real.dist_eq, sub_zero, abs_of_nonpos hB_le0]
  linarith

/-- **Theorem 15.24 (Mean Log-Modulus and Unit-Modulus Radial Limits of Blaschke Products)**:
For every Blaschke product `B` (`IsBlaschkeProduct B`):
- `(a)` `circleAverage (log ‖B ·‖) 0 r → 0` and `(2π)⁻¹ ∫_{-π}^π log ‖B(r e^{iθ})‖ dθ → 0` as `r → 1⁻`;
- `(b)` There exists a `2π`-periodic, Borel measurable boundary limit function `BStar : ℝ → ℂ`
  such that `‖BStar θ‖ = 1` and `B(r e^{iθ}) → BStar θ` as `r → 1⁻` for almost every
  `θ ∈ [-π, π]` and almost every `θ ∈ ℝ` (in particular, for a.e. `θ ∈ [-π, π]` and a.e. `θ ∈ ℝ`,
  `∃ w : ℂ, ‖w‖ = 1 ∧ Tendsto (fun r : ℝ ↦ B (r * Complex.exp (θ * Complex.I))) (𝓝[<] 1) (𝓝 w)`). -/
theorem theorem15_24 {B : ℂ → ℂ} (hB : IsBlaschkeProduct B) :
    (Tendsto (fun r : ℝ ↦ Real.circleAverage (fun z ↦ Real.log ‖B z‖) 0 r) (𝓝[<] 1) (𝓝 0) ∧
      Tendsto (fun r : ℝ ↦ (2 * Real.pi)⁻¹ *
          ∫ θ in (-Real.pi)..Real.pi, Real.log ‖B ((r : ℂ) * Complex.exp (θ * Complex.I))‖)
        (𝓝[<] 1) (𝓝 0)) ∧
    (∃ BStar : ℝ → ℂ,
      Function.Periodic BStar (2 * Real.pi) ∧
      Measurable BStar ∧
      (∀ᵐ (θ : ℝ) ∂(MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)),
        ‖BStar θ‖ = 1 ∧
          Tendsto (fun r : ℝ ↦ B ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
            (𝓝[<] 1) (𝓝 (BStar θ))) ∧
      (∀ᵐ (θ : ℝ) ∂MeasureTheory.volume,
        ‖BStar θ‖ = 1 ∧
          Tendsto (fun r : ℝ ↦ B ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
            (𝓝[<] 1) (𝓝 (BStar θ)))) ∧
    ((∀ᵐ (θ : ℝ) ∂(MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)),
        ∃ w : ℂ, ‖w‖ = 1 ∧
          Tendsto (fun r : ℝ ↦ B ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
            (𝓝[<] 1) (𝓝 w)) ∧
      (∀ᵐ (θ : ℝ) ∂MeasureTheory.volume,
        ∃ w : ℂ, ‖w‖ = 1 ∧
          Tendsto (fun r : ℝ ↦ B ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
            (𝓝[<] 1) (𝓝 w))) := by
  -- Extract holomorphicity, bound `‖B z‖ ≤ 1`, non-vanishing on `ball 0 1`, and `(a)` from `hB`
  have hB_props : DifferentiableOn ℂ B (Metric.ball (0 : ℂ) 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, ‖B z‖ ≤ 1) ∧
      (∃ z₀ ∈ Metric.ball (0 : ℂ) 1, B z₀ ≠ 0) ∧
      Tendsto (fun r : ℝ ↦ Real.circleAverage (fun z ↦ Real.log ‖B z‖) 0 r) (𝓝[<] 1) (𝓝 0) := by
    rcases hB with ⟨k, N, a, ha, hBeq⟩ | ⟨k, a, ha, hsum, hBeq⟩
    · let P₀ : ℂ → ℂ := fun z ↦ ∏ i : Fin N, blaschkeFactor (a i) z
      let B₀ : ℂ → ℂ := fun z ↦ z ^ k * P₀ z
      have hfin := finite_blaschke_product k N a ha
      have hfin0 := finite_blaschke_product 0 N a ha
      have hB_diff : DifferentiableOn ℂ B (Metric.ball (0 : ℂ) 1) := hfin.2.2.1.congr hBeq
      have hB_le1 : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖B z‖ ≤ 1 := by
        intro z hz
        rw [hBeq z hz]
        exact hfin.2.2.2.1 z hz
      have hP0_ne : P₀ 0 ≠ 0 := by
        have hP0_eq : P₀ 0 = ∏ i : Fin N, (‖a i‖ : ℂ) :=
          Finset.prod_congr rfl fun i _ ↦ blaschkeFactor_zero (ha i).2
        rw [hP0_eq]
        exact Finset.prod_ne_zero_iff.mpr fun i _ ↦
          Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (ha i).2)
      have hP0_cont : ContinuousAt P₀ 0 := by
        have hd : DifferentiableOn ℂ P₀ (Metric.ball (0 : ℂ) 1) := by
          simpa only [pow_zero, one_mul] using hfin0.2.2.1
        exact (hd.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))).continuousAt
      obtain ⟨δ, hδ_pos, hδ_nz⟩ := Metric.mem_nhds_iff.mp (hP0_cont.eventually_ne hP0_ne)
      let z₀ : ℂ := ((min (δ / 2) (1 / 2) : ℝ) : ℂ)
      have hz₀_pos : 0 < min (δ / 2) (1 / 2) := lt_min (half_pos hδ_pos) (by norm_num)
      have hz₀_ball : z₀ ∈ Metric.ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hz₀_pos.le]
        exact (min_le_right _ _).trans_lt (by norm_num)
      have hz₀_δ : z₀ ∈ Metric.ball (0 : ℂ) δ := by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hz₀_pos.le]
        exact (min_le_left _ _).trans_lt (half_lt_self hδ_pos)
      have hBz₀_ne : B z₀ ≠ 0 := by
        rw [hBeq z₀ hz₀_ball]
        exact mul_ne_zero (pow_ne_zero k (Complex.ofReal_ne_zero.mpr hz₀_pos.ne')) (hδ_nz hz₀_δ)
      have hcavg_lim : Tendsto (fun r : ℝ ↦ Real.circleAverage (fun z ↦ Real.log ‖B z‖) 0 r)
          (𝓝[<] 1) (𝓝 0) := by
        refine (circleAverage_log_norm_finite_blaschke_tendsto k N a ha).congr' ?_
        filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
        refine Real.circleAverage_congr_sphere fun z hz ↦ ?_
        have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := by
          rw [mem_sphere_zero_iff_norm, abs_of_pos hr.1] at hz
          rw [mem_ball_zero_iff, hz]
          exact hr.2
        rw [hBeq z hz_ball]
      exact ⟨hB_diff, hB_le1, ⟨z₀, hz₀_ball, hBz₀_ne⟩, hcavg_lim⟩
    · let P₀ : ℂ → ℂ := fun z ↦ ∏' n, blaschkeFactor (a n) z
      let B₀ : ℂ → ℂ := fun z ↦ z ^ k * P₀ z
      obtain ⟨_, _, _, hP₀_diff, hB₀_diff, hPB₀_norm, hP₀0_ne, _, _, _⟩ :=
        theorem15_21 k ha hsum
      have hB_diff : DifferentiableOn ℂ B (Metric.ball (0 : ℂ) 1) := hB₀_diff.congr hBeq
      have hB_le1 : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖B z‖ ≤ 1 := by
        intro z hz
        rw [hBeq z hz]
        exact (hPB₀_norm z hz).2
      have hP₀_cont : ContinuousAt P₀ 0 :=
        (hP₀_diff.differentiableAt
          (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))).continuousAt
      obtain ⟨δ, hδ_pos, hδ_nz⟩ := Metric.mem_nhds_iff.mp (hP₀_cont.eventually_ne hP₀0_ne)
      let z₀ : ℂ := ((min (δ / 2) (1 / 2) : ℝ) : ℂ)
      have hz₀_pos : 0 < min (δ / 2) (1 / 2) := lt_min (half_pos hδ_pos) (by norm_num)
      have hz₀_ball : z₀ ∈ Metric.ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hz₀_pos.le]
        exact (min_le_right _ _).trans_lt (by norm_num)
      have hz₀_δ : z₀ ∈ Metric.ball (0 : ℂ) δ := by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hz₀_pos.le]
        exact (min_le_left _ _).trans_lt (half_lt_self hδ_pos)
      have hBz₀_ne : B z₀ ≠ 0 := by
        rw [hBeq z₀ hz₀_ball]
        exact mul_ne_zero (pow_ne_zero k (Complex.ofReal_ne_zero.mpr hz₀_pos.ne')) (hδ_nz hz₀_δ)
      have hcavg_lim : Tendsto (fun r : ℝ ↦ Real.circleAverage (fun z ↦ Real.log ‖B z‖) 0 r)
          (𝓝[<] 1) (𝓝 0) := by
        refine (circleAverage_log_norm_infinite_blaschke_tendsto k ha hsum).congr' ?_
        filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
        refine Real.circleAverage_congr_sphere fun z hz ↦ ?_
        have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := by
          rw [mem_sphere_zero_iff_norm, abs_of_pos hr.1] at hz
          rw [mem_ball_zero_iff, hz]
          exact hr.2
        rw [hBeq z hz_ball]
      exact ⟨hB_diff, hB_le1, ⟨z₀, hz₀_ball, hBz₀_ne⟩, hcavg_lim⟩
  obtain ⟨hB_diff, hB_le1, hB_nz, hcavg_lim⟩ := hB_props
  have hint_lim : Tendsto (fun r : ℝ ↦ (2 * Real.pi)⁻¹ *
      ∫ θ in (-Real.pi)..Real.pi, Real.log ‖B ((r : ℂ) * Complex.exp (θ * Complex.I))‖)
      (𝓝[<] 1) (𝓝 0) :=
    hcavg_lim.congr (fun r ↦ circleAverage_zero_eq_neg_pi_pi _ r)
  -- Apply Theorem 15.19 to obtain `BStar` and prove `‖BStar θ‖ = 1` a.e.
  obtain ⟨BStar, hBStar_per, hBStar_meas, _, hae_rad_Icc, hae_rad_vol, _, _, _,
      hint_BStar_neg_pi_pi, _, hae_nz_Icc, _, _, hμ_le_μStar⟩ :=
    theorem15_19 hB_diff ⟨1, hB_le1⟩ hB_nz
  have h0_le_μStar : 0 ≤ (2 * Real.pi)⁻¹ * ∫ θ in (-Real.pi)..Real.pi, Real.log ‖BStar θ‖ := by
    refine le_of_tendsto hcavg_lim ?_
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
    exact hμ_le_μStar r hr.1 hr.2
  have h0_le_int : 0 ≤ ∫ θ in (-Real.pi)..Real.pi, Real.log ‖BStar θ‖ := by
    have hmul := mul_le_mul_of_nonneg_left h0_le_μStar Real.two_pi_pos.le
    rwa [mul_zero, mul_inv_cancel_left₀ Real.two_pi_pos.ne'] at hmul
  -- On `Icc (-π) π`, `‖BStar θ‖ ≤ 1` a.e. from the radial limit of `B`
  let ν := MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)
  have hae_le1_Icc : ∀ᵐ (θ : ℝ) ∂ν, ‖BStar θ‖ ≤ 1 := by
    filter_upwards [hae_rad_Icc] with θ hθ_lim
    refine le_of_tendsto hθ_lim.norm ?_
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
    have hz_ball : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr.1, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hr.2
    exact hB_le1 _ hz_ball
  -- Nonnegativity and vanishing integral of `-Real.log ‖BStar ·‖` on `Ioc (-π) π`
  have hpi_le : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  let φ : ℝ → ℝ := fun θ ↦ -Real.log ‖BStar θ‖
  have hφ_intOn : IntegrableOn φ (Set.Ioc (-Real.pi) Real.pi) MeasureTheory.volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi_le).mp hint_BStar_neg_pi_pi.neg
  have hae_Ioc : ∀ᵐ (θ : ℝ) ∂(MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi)),
      BStar θ ≠ 0 ∧ ‖BStar θ‖ ≤ 1 :=
    ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self (hae_nz_Icc.and hae_le1_Icc)
  have hφ_nn_ae : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi)] φ := by
    filter_upwards [hae_Ioc] with θ ⟨hθ_nz, hθ_le1⟩
    change 0 ≤ -Real.log ‖BStar θ‖
    exact neg_nonneg.mpr (Real.log_nonpos (norm_pos_iff.mpr hθ_nz).le hθ_le1)
  have hφ_int_le0 : ∫ θ in Set.Ioc (-Real.pi) Real.pi, φ θ ≤ 0 := by
    rw [← intervalIntegral.integral_of_le hpi_le]
    dsimp [φ]
    rw [intervalIntegral.integral_neg]
    linarith
  have hφ_int_eq0 : ∫ θ in Set.Ioc (-Real.pi) Real.pi, φ θ = 0 :=
    le_antisymm hφ_int_le0 (integral_nonneg_of_ae hφ_nn_ae)
  have hφ_ae0_Ioc : φ =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hφ_nn_ae hφ_intOn).mp hφ_int_eq0
  have hae_norm1_Ioc :
      ∀ᵐ (θ : ℝ) ∂(MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi)),
        ‖BStar θ‖ = 1 := by
    filter_upwards [hae_Ioc, hφ_ae0_Ioc] with θ ⟨hθ_nz, _⟩ hφ0
    have hpos : 0 < ‖BStar θ‖ := norm_pos_iff.mpr hθ_nz
    have hlog0 : Real.log ‖BStar θ‖ = 0 := neg_eq_zero.mp hφ0
    rcases Real.log_eq_zero.mp hlog0 with h0 | h1 | hm1
    · linarith
    · exact h1
    · linarith
  have hae_norm1_Icc : ∀ᵐ (θ : ℝ) ∂ν, ‖BStar θ‖ = 1 := by
    rw [ae_iff] at hae_norm1_Ioc ⊢
    have hmeas : MeasurableSet {θ : ℝ | ¬ ‖BStar θ‖ = 1} :=
      (continuous_norm.measurable.comp hBStar_meas (measurableSet_singleton 1)).compl
    rw [Measure.restrict_apply hmeas] at hae_norm1_Ioc ⊢
    have hsub : {θ : ℝ | ¬ ‖BStar θ‖ = 1} ∩ Set.Icc (-Real.pi) Real.pi ⊆
        ({θ : ℝ | ¬ ‖BStar θ‖ = 1} ∩ Set.Ioc (-Real.pi) Real.pi) ∪ {-Real.pi} := by
      rintro θ ⟨hθ_ne, h1, h2⟩
      rcases eq_or_lt_of_le h1 with rfl | hlt
      · exact Or.inr rfl
      · exact Or.inl ⟨hθ_ne, hlt, h2⟩
    refine measure_mono_null hsub (measure_union_null hae_norm1_Ioc ?_)
    simp
  have hae_norm1_vol : ∀ᵐ (θ : ℝ) ∂MeasureTheory.volume, ‖BStar θ‖ = 1 := by
    rw [ae_iff]
    have hmeas : MeasurableSet {θ : ℝ | ¬ ‖BStar θ‖ = 1} :=
      (continuous_norm.measurable.comp hBStar_meas (measurableSet_singleton 1)).compl
    have hIcc_zero :
        MeasureTheory.volume ({θ : ℝ | ¬ ‖BStar θ‖ = 1} ∩ Set.Icc (-Real.pi) Real.pi) = 0 := by
      have h0_ae := ae_iff.mp hae_norm1_Icc
      rwa [Measure.restrict_apply hmeas] at h0_ae
    have hcover : {θ : ℝ | ¬ ‖BStar θ‖ = 1} ⊆
        ⋃ m : ℤ, {θ : ℝ | ¬ ‖BStar θ‖ = 1} ∩
          Set.Icc (-Real.pi + (m : ℝ) * (2 * Real.pi)) (Real.pi + (m : ℝ) * (2 * Real.pi)) := by
      intro θ hθ
      rw [Set.mem_iUnion]
      let m : ℤ := ⌊(θ + Real.pi) / (2 * Real.pi)⌋
      refine ⟨m, hθ, ?_, ?_⟩
      · have hle := Int.floor_le ((θ + Real.pi) / (2 * Real.pi))
        have hmul := (le_div_iff₀ Real.two_pi_pos).mp hle
        dsimp [m]
        linarith
      · have hlt := Int.lt_floor_add_one ((θ + Real.pi) / (2 * Real.pi))
        have hmul := (div_lt_iff₀ Real.two_pi_pos).mp hlt
        dsimp [m]
        linarith
    refine measure_mono_null hcover (measure_iUnion_null fun m ↦ ?_)
    let shift : ℝ := (m : ℝ) * (2 * Real.pi)
    have hpre : {θ : ℝ | ¬ ‖BStar θ‖ = 1} ∩ Set.Icc (-Real.pi + shift) (Real.pi + shift) =
        (fun θ : ℝ ↦ θ + (-shift)) ⁻¹'
          ({θ : ℝ | ¬ ‖BStar θ‖ = 1} ∩ Set.Icc (-Real.pi) Real.pi) := by
      ext θ
      change (¬ ‖BStar θ‖ = 1 ∧ -Real.pi + shift ≤ θ ∧ θ ≤ Real.pi + shift) ↔
        (¬ ‖BStar (θ + -shift)‖ = 1 ∧ -Real.pi ≤ θ + -shift ∧ θ + -shift ≤ Real.pi)
      have hper_m : BStar (θ + -shift) = BStar θ := by
        have hper := hBStar_per.int_mul (-m) θ
        simpa [shift, mul_comm] using hper
      rw [hper_m]
      exact ⟨fun ⟨h0, h1, h2⟩ ↦ ⟨h0, by linarith, by linarith⟩,
        fun ⟨h0, h1, h2⟩ ↦ ⟨h0, by linarith, by linarith⟩⟩
    rw [hpre, measure_preimage_add_right]
    exact hIcc_zero
  have hae_both_Icc : ∀ᵐ (θ : ℝ) ∂ν,
      ‖BStar θ‖ = 1 ∧
        Tendsto (fun r : ℝ ↦ B ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
          (𝓝[<] 1) (𝓝 (BStar θ)) :=
    hae_norm1_Icc.and hae_rad_Icc
  have hae_both_vol : ∀ᵐ (θ : ℝ) ∂MeasureTheory.volume,
      ‖BStar θ‖ = 1 ∧
        Tendsto (fun r : ℝ ↦ B ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
          (𝓝[<] 1) (𝓝 (BStar θ)) :=
    hae_norm1_vol.and hae_rad_vol
  exact ⟨⟨hcavg_lim, hint_lim⟩,
    ⟨BStar, hBStar_per, hBStar_meas, hae_both_Icc, hae_both_vol⟩,
    ⟨hae_both_Icc.mono fun θ h ↦ ⟨BStar θ, h.1, h.2⟩,
      hae_both_vol.mono fun θ h ↦ ⟨BStar θ, h.1, h.2⟩⟩⟩

/-!
## Axiom Audit
-/

#print axioms circleMap_zero_eq
#print axioms circleMap_zero_one_eq
#print axioms periodic_polar_comp
#print axioms circleIntegrable_iff_intervalIntegrable_zero_two_pi
#print axioms circleIntegrable_iff_intervalIntegrable_neg_pi_pi
#print axioms circleAverage_zero_eq_zero_two_pi
#print axioms circleAverage_zero_eq_neg_pi_pi
#print axioms theorem15_17
#print axioms eLogNorm
#print axioms eLogNorm_zero
#print axioms eLogNorm_of_ne_zero
#print axioms analyticOrderAt_ne_top_on_ball
#print axioms disc_remove_zero_at_origin
#print axioms theorem15_18
#print axioms norm_one_sub_exp_mul_I_le
#print axioms poissonKernel_nontangential_le
#print axioms poissonKernel_nontangential_le'
#print axioms poisson_radial_tendsto_of_lebesgue_pt
#print axioms poisson_nontangential_tendsto_of_lebesgue_pt
#print axioms ae_symmetric_lebesgue_pt
#print axioms ae_poisson_nontangential_tendsto
#print axioms locallyIntegrable_of_integrable_circleMeasure
#print axioms ae_poisson_nontangential_tendsto_circle
#print axioms exists_radial_limit_of_bounded_holomorphic
#print axioms jensen_circleAverage_mono_and_near_zero
#print axioms theorem15_19
#print axioms entireMaxModulus
#print axioms entireZeroCount
#print axioms le_entireMaxModulus
#print axioms entireMaxModulus_le_of_forall_closedBall
#print axioms entireMaxModulus_eq_sphere
#print axioms entireMaxModulus_le_of_forall_sphere
#print axioms entireZeroCount_cast_eq_finsum_divisor
#print axioms analyticOrderAt_pow_origin
#print axioms theorem15_20
#print axioms blaschkeFactor
#print axioms blaschkeFactor_eq_neg_mul_phi
#print axioms blaschkeFactor_zero
#print axioms blaschkeFactor_self
#print axioms norm_blaschkeFactor_eq_norm_phi
#print axioms norm_blaschkeFactor_lt_one
#print axioms norm_blaschkeFactor_le_one
#print axioms norm_blaschkeFactor_eq_one
#print axioms analyticAt_blaschkeFactor
#print axioms differentiableOn_blaschkeFactor_closedBall
#print axioms differentiableOn_blaschkeFactor_ball
#print axioms blaschkeFactor_eq_zero_iff
#print axioms analyticOrderAt_blaschkeFactor
#print axioms norm_one_sub_blaschkeFactor_le
#print axioms IsBlaschkeProduct
#print axioms isBlaschkeProduct_one
#print axioms isBlaschkeProduct_pow
#print axioms finite_blaschke_product
#print axioms theorem15_21
#print axioms posLog_eq_ite
#print axioms posLog_norm_eq_ite
#print axioms circleIntegrable_posLog_norm_of_differentiableOn
#print axioms NevanlinnaClass
#print axioms mem_nevanlinnaClass_iff_Ico
#print axioms theorem15_22
#print axioms theorem15_23
#print axioms theorem15_16
#print axioms theorem15_24


end Chapter15PartB

section Chapter15PartC
set_option autoImplicit false
open Filter Finset Set Metric
open scoped Topology BigOperators Polynomial InnerProductSpace


/-! ### Section 1: Definitions and Node `15.25` (Polynomial Density on `[0, 1]`) -/

/-- The closed real unit interval `[0, 1]`, used as the domain of `C([0, 1])` in `15.25`–`15.27`. -/
abbrev UnitInterval01 : Set ℝ := Set.Icc (0 : ℝ) 1

instance : Nonempty UnitInterval01 := ⟨⟨0, by norm_num⟩⟩

/-- For `0 ≤ α`, the continuous complex-valued power map `t ↦ t ^ α` on `[0, 1]`.
For `α = 0`, `t ^ (0 : ℝ) = 1`, so `realPowerContinuousMap 0 le_rfl = 1`. -/
def realPowerContinuousMap (α : ℝ) (hα : 0 ≤ α) : C(UnitInterval01, ℂ) :=
  ⟨fun t ↦ ((t.1 ^ α : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (continuous_subtype_val.rpow_const fun _ ↦ Or.inr hα)⟩

@[simp]
theorem realPowerContinuousMap_apply (α : ℝ) (hα : 0 ≤ α) (t : UnitInterval01) :
    realPowerContinuousMap α hα t = ((t.1 ^ α : ℝ) : ℂ) :=
  rfl

@[simp]
theorem realPowerContinuousMap_zero :
    realPowerContinuousMap 0 le_rfl = (1 : C(UnitInterval01, ℂ)) := by
  ext t
  simp

theorem realPowerContinuousMap_natCast (n : ℕ) :
    realPowerContinuousMap (n : ℝ) n.cast_nonneg =
      ⟨fun t : UnitInterval01 ↦ (t.1 : ℂ) ^ n, by fun_prop⟩ := by
  ext t
  simp [Real.rpow_natCast]

theorem realPowerContinuousMap_eval_zero_of_pos {α : ℝ} (hα : 0 < α) :
    realPowerContinuousMap α hα.le ⟨0, by norm_num⟩ = 0 := by
  simp [Real.zero_rpow hα.ne']

theorem realPowerContinuousMap_ne_one_of_pos {α : ℝ} (hα : 0 < α) :
    realPowerContinuousMap α hα.le ≠ 1 := by
  intro h
  have h0 := congr_arg (fun f : C(UnitInterval01, ℂ) ↦ f ⟨0, by norm_num⟩) h
  rw [realPowerContinuousMap_eval_zero_of_pos hα] at h0
  exact zero_ne_one h0

theorem realPowerContinuousMap_inj {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (heq : realPowerContinuousMap α hα = realPowerContinuousMap β hβ) : α = β := by
  have hhalf := congr_arg (fun f : C(UnitInterval01, ℂ) ↦ f ⟨1 / 2, by norm_num⟩) heq
  simp only [realPowerContinuousMap_apply, Complex.ofReal_inj] at hhalf
  have hlog := congr_arg Real.log hhalf
  rw [Real.log_rpow (by norm_num), Real.log_rpow (by norm_num)] at hlog
  have hne : Real.log (1 / 2 : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one <;> norm_num
  exact mul_right_cancel₀ hne hlog

/-- Rudin's spanning convention in `15.25`: a subset `F ⊆ C(X, ℂ)` *spans* `C(X, ℂ)` when the set
of finite `ℂ`-linear combinations of elements of `F` is dense in `C(X, ℂ)` with respect to the
supremum norm. -/
def UniformlySpans {X : Type*} [TopologicalSpace X] [CompactSpace X] (F : Set C(X, ℂ)) : Prop :=
  (Submodule.span ℂ F).topologicalClosure = ⊤

theorem uniformlySpans_iff_dense {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (F : Set C(X, ℂ)) :
    UniformlySpans F ↔ Dense (Submodule.span ℂ F : Set C(X, ℂ)) := by
  rw [UniformlySpans, SetLike.ext'_iff, Submodule.topologicalClosure_coe, Submodule.top_coe,
    dense_iff_closure_eq]

theorem uniformlySpans_iff_forall_approx {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (F : Set C(X, ℂ)) :
    UniformlySpans F ↔
      ∀ f : C(X, ℂ), ∀ ε : ℝ, 0 < ε → ∃ g ∈ Submodule.span ℂ F, ‖f - g‖ < ε := by
  rw [uniformlySpans_iff_dense, Metric.dense_iff]
  constructor
  · intro h f ε hε
    obtain ⟨g, hball, hg⟩ := h f ε hε
    rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hball
    exact ⟨g, hg, hball⟩
  · intro h f ε hε
    obtain ⟨g, hg, hnorm⟩ := h f ε hε
    refine ⟨g, ?_, hg⟩
    rwa [Metric.mem_ball, dist_comm, dist_eq_norm]

theorem uniformlySpans_unitInterval_iff_pointwise (F : Set C(UnitInterval01, ℂ)) :
    UniformlySpans F ↔
      ∀ f : C(UnitInterval01, ℂ), ∀ ε : ℝ, 0 < ε →
        ∃ g ∈ Submodule.span ℂ F, ∀ t : UnitInterval01, ‖f t - g t‖ < ε := by
  rw [uniformlySpans_iff_forall_approx]
  constructor
  · intro h f ε hε
    obtain ⟨g, hg, hnorm⟩ := h f ε hε
    exact ⟨g, hg, fun t ↦ ((ContinuousMap.norm_lt_iff _ hε).mp hnorm) t⟩
  · intro h f ε hε
    obtain ⟨g, hg, hpt⟩ := h f ε hε
    exact ⟨g, hg, (ContinuousMap.norm_lt_iff _ hε).mpr hpt⟩

/-- General Stone–Weierstrass helper: if `φ : C(X, ℂ)` on compact `X` is self-adjoint (`star φ = φ`,
i.e. real-valued) and injective, then `{φ ^ n | n : ℕ}` uniformly spans `C(X, ℂ)`. -/
theorem uniformlySpans_powers_of_star_eq_self_of_injective
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (φ : C(X, ℂ)) (hstar : star φ = φ) (hinj : Function.Injective φ) :
    UniformlySpans (Set.range (fun n : ℕ ↦ φ ^ n)) := by
  let F : Set C(X, ℂ) := Set.range (fun n : ℕ ↦ φ ^ n)
  let M : Submodule ℂ C(X, ℂ) := Submodule.span ℂ F
  have hpow_mem : ∀ n : ℕ, φ ^ n ∈ M := fun n ↦ Submodule.subset_span ⟨n, rfl⟩
  have hmul_gen : ∀ g₁ ∈ F, ∀ g₂ ∈ F, g₁ * g₂ ∈ M := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
    rw [← pow_add]
    exact hpow_mem (n + m)
  have hmul_left : ∀ g₁ ∈ F, ∀ f₂ ∈ M, g₁ * f₂ ∈ M := by
    intro g₁ hg₁ f₂ hf₂
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf₂
    · intro g₂ hg₂
      exact hmul_gen g₁ hg₁ g₂ hg₂
    · simp
    · intro x y _ _ hx hy
      rw [mul_add]
      exact M.add_mem hx hy
    · intro c x _ hx
      rw [mul_smul_comm]
      exact M.smul_mem c hx
  have hmul_mem : ∀ f₁ ∈ M, ∀ f₂ ∈ M, f₁ * f₂ ∈ M := by
    intro f₁ hf₁ f₂ hf₂
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf₁
    · intro g₁ hg₁
      exact hmul_left g₁ hg₁ f₂ hf₂
    · simp
    · intro x y _ _ hx hy
      rw [add_mul]
      exact M.add_mem hx hy
    · intro c x _ hx
      rw [smul_mul_assoc]
      exact M.smul_mem c hx
  have hstar_mem : ∀ f ∈ M, star f ∈ M := by
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨n, rfl⟩
      rw [star_pow, hstar]
      exact hpow_mem n
    · simp
    · intro x y _ _ hx hy
      rw [star_add]
      exact M.add_mem hx hy
    · intro c x _ hx
      rw [star_smul]
      exact M.smul_mem (star c) hx
  let A : StarSubalgebra ℂ C(X, ℂ) :=
    { toSubalgebra :=
        { carrier := M
          mul_mem' := fun {a b} ha hb ↦ hmul_mem a ha b hb
          one_mem' := by simpa using hpow_mem 0
          add_mem' := fun {a b} ha hb ↦ M.add_mem ha hb
          zero_mem' := M.zero_mem
          algebraMap_mem' := fun r ↦ by
            rw [Algebra.algebraMap_eq_smul_one]
            exact M.smul_mem r (by simpa using hpow_mem 0) }
      star_mem' := fun {a} ha ↦ hstar_mem a ha }
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    refine ⟨φ, ⟨φ, ?_, rfl⟩, fun hφ ↦ hxy (hinj hφ)⟩
    show φ ∈ M
    simpa using hpow_mem 1
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  rw [UniformlySpans, SetLike.ext'_iff, Submodule.topologicalClosure_coe, Submodule.top_coe]
  have hA_coe : (A.topologicalClosure : Set C(X, ℂ)) = closure (M : Set C(X, ℂ)) :=
    A.topologicalClosure_coe
  rw [htop] at hA_coe
  exact hA_coe.symm

/-- **15.25 (Weierstrass Polynomial Density on `[0, 1]`, RCA pp. 312–313):**
The integer monomials `t ↦ t ^ n` (`n = 0, 1, 2, …`) uniformly span `C([0, 1])`; equivalently,
every complex continuous function on `[0, 1]` is uniformly approximable on `[0, 1]` by finite
complex linear combinations of `{1, t, t², …}`. -/
theorem theorem15_25 :
    UniformlySpans
      (Set.range (fun n : ℕ ↦ (⟨fun t : UnitInterval01 ↦ (t.1 : ℂ) ^ n, by fun_prop⟩ :
        C(UnitInterval01, ℂ)))) := by
  let φ : C(UnitInterval01, ℂ) := ⟨fun t ↦ (t.1 : ℂ), by fun_prop⟩
  have hstar : star φ = φ := by
    ext t
    simp [φ]
  have hinj : Function.Injective φ := by
    intro t₁ t₂ h
    ext
    exact Complex.ofReal_inj.mp h
  have hrange :
      Set.range (fun n : ℕ ↦ (⟨fun t : UnitInterval01 ↦ (t.1 : ℂ) ^ n, by fun_prop⟩ :
        C(UnitInterval01, ℂ))) = Set.range (fun n : ℕ ↦ φ ^ n) := by
    ext f
    simp only [Set.mem_range]
    refine exists_congr fun n ↦ ?_
    rw [eq_comm]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;>
    · subst h
      ext t
      simp [φ]
  rw [hrange]
  exact uniformlySpans_powers_of_star_eq_self_of_injective φ hstar hinj

/-- Equivalence between the integer monomial family of `15.25` and `realPowerContinuousMap` at `ℕ`. -/
theorem theorem15_25_realPower :
    UniformlySpans (Set.range (fun n : ℕ ↦ realPowerContinuousMap (n : ℝ) n.cast_nonneg)) := by
  have hrange :
      Set.range (fun n : ℕ ↦ realPowerContinuousMap (n : ℝ) n.cast_nonneg) =
        Set.range (fun n : ℕ ↦ (⟨fun t : UnitInterval01 ↦ (t.1 : ℂ) ^ n, by fun_prop⟩ :
          C(UnitInterval01, ℂ))) := by
    ext f
    simp [realPowerContinuousMap_natCast]
  rw [hrange]
  exact theorem15_25

/-! ### Section 2: Exact `L²(0, 1)` Cauchy/Lagrange Partial-Fraction Distance Identity -/

/-- Auxiliary integral: `∫_0^1 t ^ r dt = 1 / (r + 1)` for `r > -1`. -/
theorem integral_zero_one_rpow {r : ℝ} (hr : -1 < r) :
    ∫ t in (0 : ℝ)..1, t ^ r = 1 / (r + 1) := by
  rw [integral_rpow (Or.inl hr), Real.one_rpow, Real.zero_rpow (by linarith), sub_zero]

/-- Elementary Cauchy–Schwarz bound on `[0, 1]`: for any continuous `f : ℝ → ℝ` and `u ∈ [0, 1]`,
`(∫_0^u f(s) ds)² ≤ ∫_0^1 f(s)² ds`. -/
theorem sq_integral_zero_le_integral_zero_one_sq {f : ℝ → ℝ} (hf : Continuous f)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∫ s in (0 : ℝ)..u, f s) ^ 2 ≤ ∫ s in (0 : ℝ)..1, (f s) ^ 2 := by
  have hf_sq : Continuous (fun s ↦ (f s) ^ 2) := hf.pow 2
  rcases hu0.eq_or_lt with rfl | hu_pos
  · simp only [intervalIntegral.integral_same, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
    exact intervalIntegral.integral_nonneg zero_le_one fun s _ ↦ sq_nonneg (f s)
  · let I : ℝ := ∫ s in (0 : ℝ)..u, f s
    have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..u, (u * f s - I) ^ 2 :=
      intervalIntegral.integral_nonneg hu_pos.le fun s _ ↦ sq_nonneg _
    have hexpand :
        (∫ s in (0 : ℝ)..u, (u * f s - I) ^ 2) =
          u ^ 2 * (∫ s in (0 : ℝ)..u, (f s) ^ 2) - (2 * u * I) * I + u * I ^ 2 := by
      have hfun :
          (fun s ↦ (u * f s - I) ^ 2) =
            fun s ↦ (u ^ 2 * (f s) ^ 2 - (2 * u * I) * f s) + I ^ 2 := by
        ext s; ring
      have hint1 : IntervalIntegrable
          (fun s ↦ u ^ 2 * (f s) ^ 2 - (2 * u * I) * f s) MeasureTheory.volume 0 u :=
        Continuous.intervalIntegrable (by fun_prop) 0 u
      have hint2 : IntervalIntegrable (fun _ : ℝ ↦ I ^ 2) MeasureTheory.volume 0 u :=
        continuous_const.intervalIntegrable 0 u
      have hint1a : IntervalIntegrable (fun s ↦ u ^ 2 * (f s) ^ 2) MeasureTheory.volume 0 u :=
        Continuous.intervalIntegrable (by fun_prop) 0 u
      have hint1b : IntervalIntegrable (fun s ↦ (2 * u * I) * f s) MeasureTheory.volume 0 u :=
        Continuous.intervalIntegrable (by fun_prop) 0 u
      rw [hfun,
        intervalIntegral.integral_add hint1 hint2,
        intervalIntegral.integral_sub hint1a hint1b,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const,
        sub_zero, smul_eq_mul]
    rw [hexpand] at hnonneg
    have h_u_le : I ^ 2 ≤ u * ∫ s in (0 : ℝ)..u, (f s) ^ 2 := by
      have : 0 ≤ u * (u * (∫ s in (0 : ℝ)..u, (f s) ^ 2) - I ^ 2) := by linarith
      have hdiv := nonneg_of_mul_nonneg_right this hu_pos
      linarith
    have h_int_u_pos : 0 ≤ ∫ s in (0 : ℝ)..u, (f s) ^ 2 :=
      intervalIntegral.integral_nonneg hu_pos.le fun s _ ↦ sq_nonneg _
    have h_int_u1_pos : 0 ≤ ∫ s in u..1, (f s) ^ 2 :=
      intervalIntegral.integral_nonneg hu1 fun s _ ↦ sq_nonneg _
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (hf_sq.intervalIntegrable (μ := MeasureTheory.volume) 0 u)
      (hf_sq.intervalIntegrable (μ := MeasureTheory.volume) u 1)
    calc
      I ^ 2 ≤ u * ∫ s in (0 : ℝ)..u, (f s) ^ 2 := h_u_le
      _ ≤ 1 * ∫ s in (0 : ℝ)..u, (f s) ^ 2 :=
        mul_le_mul_of_nonneg_right hu1 h_int_u_pos
      _ ≤ (∫ s in (0 : ℝ)..u, (f s) ^ 2) + ∫ s in u..1, (f s) ^ 2 := by linarith
      _ = ∫ s in (0 : ℝ)..1, (f s) ^ 2 := hadj

/-- Explicit Lagrange partial-fraction coefficient `d` at `-(μ + 1)`. -/
def cauchyResidueMain {N : ℕ} (ν : Fin N → ℝ) (μ : ℝ) : ℝ :=
  ∏ k : Fin N, ((μ + ν k + 1) / (μ - ν k))

/-- Explicit Lagrange partial-fraction coefficient `c k` at `-(ν k + 1)`. -/
def cauchyResidueAux {N : ℕ} (ν : Fin N → ℝ) (μ : ℝ) (k : Fin N) : ℝ :=
  (∏ j : Fin N, (-(ν k + 1) - ν j)) /
    ((-(ν k + 1) + μ + 1) * ∏ j ∈ Finset.univ.erase k, (-(ν k + 1) + ν j + 1))

theorem cauchyResidueMain_ne_zero {N : ℕ} {ν : Fin N → ℝ} {μ : ℝ}
    (hν_nonneg : ∀ k, 0 ≤ ν k) (hμ_nonneg : 0 ≤ μ) (hμ_ne : ∀ k, μ ≠ ν k) :
    cauchyResidueMain ν μ ≠ 0 := by
  unfold cauchyResidueMain
  refine Finset.prod_ne_zero_iff.mpr fun k _ ↦ div_ne_zero ?_ (sub_ne_zero.mpr (hμ_ne k))
  linarith [hν_nonneg k, hμ_nonneg]

/-- **Lagrange partial-fraction identity**:
For pairwise distinct `ν : Fin N → ℝ` and `μ ≠ ν k`, and every `z : ℝ` avoiding the poles
`-(μ + 1)` and `-(ν k + 1)`:
`(∏ k, (z - ν k)) / ((z + μ + 1) * ∏ k, (z + ν k + 1)) = d / (z + μ + 1) + ∑ k, c k / (z + ν k + 1)`. -/
theorem cauchy_partial_fraction_identity {N : ℕ} {ν : Fin N → ℝ} {μ : ℝ}
    (hν_inj : Function.Injective ν) (hμ_ne : ∀ k, μ ≠ ν k)
    {z : ℝ} (hz_μ : z + μ + 1 ≠ 0) (hz_ν : ∀ k, z + ν k + 1 ≠ 0) :
    (∏ k : Fin N, (z - ν k)) / ((z + μ + 1) * ∏ k : Fin N, (z + ν k + 1)) =
      cauchyResidueMain ν μ / (z + μ + 1) +
        ∑ k : Fin N, cauchyResidueAux ν μ k / (z + ν k + 1) := by
  classical
  let v : Option (Fin N) → ℝ
    | none => -(μ + 1)
    | some k => -(ν k + 1)
  have hv_inj : Function.Injective v := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some k =>
        dsimp [v] at hab
        exact False.elim (hμ_ne k (by linarith))
    | some j =>
      cases b with
      | none =>
        dsimp [v] at hab
        exact False.elim (hμ_ne j (by linarith))
      | some k =>
        dsimp [v] at hab
        exact congrArg some (hν_inj (by linarith))
  let P : ℝ[X] := ∏ k : Fin N, (Polynomial.X - Polynomial.C (ν k))
  have hP_deg : P.degree < #((Finset.univ : Finset (Option (Fin N)))) := by
    have hle : P.degree ≤ ∑ _k : Fin N, (1 : WithBot ℕ) := by
      refine (Polynomial.degree_prod_le _ _).trans ?_
      refine Finset.sum_le_sum fun k _ ↦ ?_
      rw [Polynomial.degree_X_sub_C]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      Fintype.card_option] at hle ⊢
    exact lt_of_le_of_lt hle (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self N))
  have hinterp := Lagrange.eq_interpolate (s := (Finset.univ : Finset (Option (Fin N))))
    hv_inj.injOn hP_deg
  have heval_P : ∀ x : ℝ, P.eval x = ∏ k : Fin N, (x - ν k) := by
    intro x
    simp [P, Polynomial.eval_prod]
  have hz_v : ∀ i : Option (Fin N), z - v i ≠ 0 := by
    rintro (_ | k)
    · dsimp [v]; intro h; exact hz_μ (by linarith)
    · dsimp [v]; intro h; exact hz_ν k (by linarith)
  let Q : ℝ := ∏ j : Option (Fin N), (z - v j)
  have hQ_eq : Q = (z + μ + 1) * ∏ k : Fin N, (z + ν k + 1) := by
    dsimp [Q]
    rw [Fintype.prod_option]
    congr 1
    · dsimp [v]; ring
    · refine Finset.prod_congr rfl fun k _ ↦ ?_
      dsimp [v]; ring
  have hQ_ne : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ hz_v i
  have hP_z := congr_arg (Polynomial.eval z) hinterp
  rw [heval_P z, Lagrange.interpolate_apply, Polynomial.eval_finsetSum] at hP_z
  have hterm : ∀ i : Option (Fin N),
      (Polynomial.eval z (Polynomial.C (Polynomial.eval (v i) P) *
        Lagrange.basis Finset.univ v i)) / Q =
        (P.eval (v i) * ∏ j ∈ Finset.univ.erase i, (v i - v j)⁻¹) / (z - v i) := by
    intro i
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    have hbasis_z :
        Polynomial.eval z (Lagrange.basis Finset.univ v i) =
          (∏ j ∈ Finset.univ.erase i, (v i - v j)⁻¹) *
            ∏ j ∈ Finset.univ.erase i, (z - v j) := by
      rw [Lagrange.basis, Polynomial.eval_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      simp [Lagrange.basisDivisor]
    rw [hbasis_z, ← mul_assoc]
    have hQ_split : Q = (z - v i) * ∏ j ∈ Finset.univ.erase i, (z - v j) :=
      (Finset.mul_prod_erase Finset.univ (fun j ↦ z - v j) (Finset.mem_univ i)).symm
    have herase_ne : (∏ j ∈ Finset.univ.erase i, (z - v j)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ ↦ hz_v j
    rw [hQ_split, mul_div_mul_right _ _ herase_ne]
  have hdiv := congr_arg (· / Q) hP_z
  rw [Finset.sum_div] at hdiv
  simp_rw [hterm] at hdiv
  rw [Fintype.sum_option, hQ_eq] at hdiv
  rw [hdiv]
  congr 1
  · have h_erase_none :
        (Finset.univ : Finset (Option (Fin N))).erase none =
          (Finset.univ : Finset (Fin N)).map ⟨Option.some, Option.some_injective _⟩ := by
      ext x
      cases x <;> simp
    have hd_eq :
        P.eval (v none) * ∏ j ∈ Finset.univ.erase none, (v none - v j)⁻¹ =
          cauchyResidueMain ν μ := by
      rw [heval_P (v none), h_erase_none, Finset.prod_map, ← Finset.prod_mul_distrib]
      unfold cauchyResidueMain
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      have hsub1 : μ - ν k ≠ 0 := sub_ne_zero.mpr (hμ_ne k)
      have hsub2 : ν k - μ ≠ 0 := sub_ne_zero.mpr (hμ_ne k).symm
      dsimp [v]
      have hdenom : -(μ + 1) - -(ν k + 1) = ν k - μ := by ring
      rw [hdenom]
      field_simp [hsub1, hsub2]
      ring
    rw [hd_eq]
    congr 1
    dsimp [v]
    ring
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    have h_erase_some :
        (Finset.univ : Finset (Option (Fin N))).erase (some k) =
          insert none ((Finset.univ.erase k).map ⟨Option.some, Option.some_injective _⟩) := by
      ext x
      cases x with
      | none => simp
      | some j => simp [eq_comm]
    have hc_eq :
        P.eval (v (some k)) * ∏ j ∈ Finset.univ.erase (some k), (v (some k) - v j)⁻¹ =
          cauchyResidueAux ν μ k := by
      rw [heval_P (v (some k)), h_erase_some,
        Finset.prod_insert (by simp), Finset.prod_map]
      unfold cauchyResidueAux
      rw [div_eq_mul_inv, mul_inv, ← Finset.prod_inv_distrib]
      dsimp [v]
      congr 1
      congr 1
      · congr 1; ring
      · refine Finset.prod_congr rfl fun j _ ↦ ?_
        congr 1; ring
    rw [hc_eq]
    congr 1
    dsimp [v]
    ring

/-- Coefficients `-(c k / d)` of the optimal real `L²(0, 1)` approximant `q(t)` to `t ^ μ`. -/
def cauchyOptCoeff {N : ℕ} (ν : Fin N → ℝ) (μ : ℝ) (k : Fin N) : ℝ :=
  -(cauchyResidueAux ν μ k / cauchyResidueMain ν μ)

/-- Optimal real `L²(0, 1)` approximant `q(t) = ∑ k, (-(c k / d)) * t ^ (ν k)` to `t ^ μ`. -/
def cauchyOptApprox {N : ℕ} (ν : Fin N → ℝ) (μ : ℝ) (t : ℝ) : ℝ :=
  ∑ k : Fin N, cauchyOptCoeff ν μ k * (t ^ (ν k))

theorem continuous_cauchyOptApprox {N : ℕ} {ν : Fin N → ℝ} (hν_nonneg : ∀ k, 0 ≤ ν k) (μ : ℝ) :
    Continuous (cauchyOptApprox ν μ) := by
  unfold cauchyOptApprox
  refine continuous_finsetSum _ fun k _ ↦ ?_
  exact continuous_const.mul (Real.continuous_rpow_const (hν_nonneg k))

/-- Key integral formula for `ψ(t) := d * (t ^ μ - q(t))`:
for every `z ≥ 0`, `∫_0^1 t ^ z * (d * (t ^ μ - q(t))) dt = (∏ k, (z - ν k)) / ((z + μ + 1) * ∏ k, (z + ν k + 1))`. -/
theorem integral_rpow_mul_sub_cauchyOptApprox {N : ℕ} {ν : Fin N → ℝ} {μ : ℝ}
    (hν_inj : Function.Injective ν) (hν_nonneg : ∀ k, 0 ≤ ν k)
    (hμ_nonneg : 0 ≤ μ) (hμ_ne : ∀ k, μ ≠ ν k)
    {z : ℝ} (hz : 0 ≤ z) :
    ∫ t in (0 : ℝ)..1,
      t ^ z * (cauchyResidueMain ν μ * (t ^ μ - cauchyOptApprox ν μ t)) =
      (∏ k : Fin N, (z - ν k)) / ((z + μ + 1) * ∏ k : Fin N, (z + ν k + 1)) := by
  let d := cauchyResidueMain ν μ
  let c := cauchyResidueAux ν μ
  have hd : d ≠ 0 := cauchyResidueMain_ne_zero hν_nonneg hμ_nonneg hμ_ne
  have hcongr :
      Set.EqOn
        (fun t : ℝ ↦ t ^ z * (d * (t ^ μ - cauchyOptApprox ν μ t)))
        (fun t : ℝ ↦ d * t ^ (z + μ) + ∑ k : Fin N, c k * t ^ (z + ν k))
        (Set.uIcc (0 : ℝ) 1) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have ht0 : 0 ≤ t := ht.1
    have hψ : d * (t ^ μ - cauchyOptApprox ν μ t) =
        d * t ^ μ + ∑ k : Fin N, c k * t ^ (ν k) := by
      unfold cauchyOptApprox cauchyOptCoeff
      rw [mul_sub, Finset.mul_sum]
      have hsum :
          (∑ k : Fin N, d * (-(c k / d) * t ^ (ν k))) =
            -(∑ k : Fin N, c k * t ^ (ν k)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        change d * (-(c k / d) * t ^ (ν k)) = -(c k * t ^ (ν k))
        field_simp [hd]
      rw [hsum, sub_neg_eq_add]
    dsimp only
    rw [hψ, mul_add, ← mul_assoc, mul_comm (t ^ z) d, mul_assoc,
      ← Real.rpow_add_of_nonneg ht0 hz hμ_nonneg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← mul_assoc, mul_comm (t ^ z) (c k), mul_assoc,
      ← Real.rpow_add_of_nonneg ht0 hz (hν_nonneg k)]
  rw [intervalIntegral.integral_congr hcongr]
  have hint_main : IntervalIntegrable (fun t : ℝ ↦ d * t ^ (z + μ)) MeasureTheory.volume 0 1 :=
    (continuous_const.mul (Real.continuous_rpow_const (by linarith))).intervalIntegrable 0 1
  have hint_sum_each : ∀ k ∈ (Finset.univ : Finset (Fin N)),
      IntervalIntegrable (fun t : ℝ ↦ c k * t ^ (z + ν k)) MeasureTheory.volume 0 1 :=
    fun k _ ↦ (continuous_const.mul
      (Real.continuous_rpow_const (by linarith [hν_nonneg k]))).intervalIntegrable 0 1
  have hint_sum : IntervalIntegrable
      (fun t : ℝ ↦ ∑ k : Fin N, c k * t ^ (z + ν k)) MeasureTheory.volume 0 1 :=
    (continuous_finsetSum _ fun k _ ↦
      continuous_const.mul (Real.continuous_rpow_const (by linarith [hν_nonneg k]))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hint_main hint_sum,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum hint_sum_each]
  rw [integral_zero_one_rpow (by linarith), mul_one_div]
  have hsum_eq :
      (∑ k : Fin N, ∫ t in (0 : ℝ)..1, c k * t ^ (z + ν k)) =
        ∑ k : Fin N, c k / (z + ν k + 1) := by
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [intervalIntegral.integral_const_mul,
      integral_zero_one_rpow (by linarith [hν_nonneg k]), mul_one_div]
  rw [hsum_eq]
  exact (cauchy_partial_fraction_identity hν_inj hμ_ne
    (by linarith) (fun k ↦ by linarith [hν_nonneg k])).symm

/-- Orthogonality: `t ^ μ - q(t)` is orthogonal in `L²(0, 1)` to `t ^ (ν j)` for every `j : Fin N`. -/
theorem integral_rpow_nu_mul_sub_cauchyOptApprox {N : ℕ} {ν : Fin N → ℝ} {μ : ℝ}
    (hν_inj : Function.Injective ν) (hν_nonneg : ∀ k, 0 ≤ ν k)
    (hμ_nonneg : 0 ≤ μ) (hμ_ne : ∀ k, μ ≠ ν k) (j : Fin N) :
    ∫ t in (0 : ℝ)..1, t ^ (ν j) * (t ^ μ - cauchyOptApprox ν μ t) = 0 := by
  have hd : cauchyResidueMain ν μ ≠ 0 := cauchyResidueMain_ne_zero hν_nonneg hμ_nonneg hμ_ne
  have hmul := integral_rpow_mul_sub_cauchyOptApprox hν_inj hν_nonneg hμ_nonneg hμ_ne (hν_nonneg j)
  have hzero : (∏ k : Fin N, (ν j - ν k)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)
  rw [hzero, zero_div] at hmul
  have hpull :
      (∫ t in (0 : ℝ)..1,
        t ^ (ν j) * (cauchyResidueMain ν μ * (t ^ μ - cauchyOptApprox ν μ t))) =
        cauchyResidueMain ν μ * ∫ t in (0 : ℝ)..1, t ^ (ν j) * (t ^ μ - cauchyOptApprox ν μ t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    ring
  rw [hpull] at hmul
  exact (mul_eq_zero.mp hmul).resolve_left hd

/-- Orthogonality of `t ^ μ - q(t)` against any real linear combination `∑ j, w j * t ^ (ν j)`. -/
theorem integral_linearComb_mul_sub_cauchyOptApprox {N : ℕ} {ν : Fin N → ℝ} {μ : ℝ}
    (hν_inj : Function.Injective ν) (hν_nonneg : ∀ k, 0 ≤ ν k)
    (hμ_nonneg : 0 ≤ μ) (hμ_ne : ∀ k, μ ≠ ν k) (w : Fin N → ℝ) :
    ∫ t in (0 : ℝ)..1,
      (∑ j : Fin N, w j * t ^ (ν j)) * (t ^ μ - cauchyOptApprox ν μ t) = 0 := by
  have hdiff_cont : Continuous (fun t : ℝ ↦ t ^ μ - cauchyOptApprox ν μ t) :=
    (Real.continuous_rpow_const hμ_nonneg).sub (continuous_cauchyOptApprox hν_nonneg μ)
  have hfun :
      (fun t : ℝ ↦ (∑ j : Fin N, w j * t ^ (ν j)) * (t ^ μ - cauchyOptApprox ν μ t)) =
        fun t : ℝ ↦ ∑ j : Fin N, w j * (t ^ (ν j) * (t ^ μ - cauchyOptApprox ν μ t)) := by
    ext t
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [hfun, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [intervalIntegral.integral_const_mul,
      integral_rpow_nu_mul_sub_cauchyOptApprox hν_inj hν_nonneg hμ_nonneg hμ_ne j, mul_zero]
  · intro j _
    exact (continuous_const.mul
      ((Real.continuous_rpow_const (hν_nonneg j)).mul hdiff_cont)).intervalIntegrable 0 1

/-- **Exact `L²(0, 1)` squared distance of `t ^ μ` to `cauchyOptApprox ν μ`**:
`∫_0^1 (t ^ μ - q(t))² dt = (1 / (2μ + 1)) * ∏ k, ((μ - ν k) / (μ + ν k + 1))²`. -/
theorem integral_sub_cauchyOptApprox_sq {N : ℕ} {ν : Fin N → ℝ} {μ : ℝ}
    (hν_inj : Function.Injective ν) (hν_nonneg : ∀ k, 0 ≤ ν k)
    (hμ_nonneg : 0 ≤ μ) (hμ_ne : ∀ k, μ ≠ ν k) :
    ∫ t in (0 : ℝ)..1, (t ^ μ - cauchyOptApprox ν μ t) ^ 2 =
      (1 / (2 * μ + 1)) * ∏ k : Fin N, ((μ - ν k) / (μ + ν k + 1)) ^ 2 := by
  let d := cauchyResidueMain ν μ
  have hd : d ≠ 0 := cauchyResidueMain_ne_zero hν_nonneg hμ_nonneg hμ_ne
  have hdiff_cont : Continuous (fun t : ℝ ↦ t ^ μ - cauchyOptApprox ν μ t) :=
    (Real.continuous_rpow_const hμ_nonneg).sub (continuous_cauchyOptApprox hν_nonneg μ)
  have horth_q :
      ∫ t in (0 : ℝ)..1, cauchyOptApprox ν μ t * (t ^ μ - cauchyOptApprox ν μ t) = 0 :=
    integral_linearComb_mul_sub_cauchyOptApprox hν_inj hν_nonneg hμ_nonneg hμ_ne
      (cauchyOptCoeff ν μ)
  have hsplit :
      (∫ t in (0 : ℝ)..1, (t ^ μ - cauchyOptApprox ν μ t) ^ 2) =
        ∫ t in (0 : ℝ)..1, t ^ μ * (t ^ μ - cauchyOptApprox ν μ t) := by
    have hfun :
        (fun t : ℝ ↦ (t ^ μ - cauchyOptApprox ν μ t) ^ 2) =
          fun t : ℝ ↦ t ^ μ * (t ^ μ - cauchyOptApprox ν μ t) -
            cauchyOptApprox ν μ t * (t ^ μ - cauchyOptApprox ν μ t) := by
      ext t; ring
    have hint1 : IntervalIntegrable
        (fun t : ℝ ↦ t ^ μ * (t ^ μ - cauchyOptApprox ν μ t)) MeasureTheory.volume 0 1 :=
      ((Real.continuous_rpow_const hμ_nonneg).mul hdiff_cont).intervalIntegrable 0 1
    have hint2 : IntervalIntegrable
        (fun t : ℝ ↦ cauchyOptApprox ν μ t * (t ^ μ - cauchyOptApprox ν μ t))
        MeasureTheory.volume 0 1 :=
      ((continuous_cauchyOptApprox hν_nonneg μ).mul hdiff_cont).intervalIntegrable 0 1
    rw [hfun, intervalIntegral.integral_sub hint1 hint2, horth_q, sub_zero]
  rw [hsplit]
  have hmu := integral_rpow_mul_sub_cauchyOptApprox hν_inj hν_nonneg hμ_nonneg hμ_ne hμ_nonneg
  have hpull :
      (∫ t in (0 : ℝ)..1, t ^ μ * (d * (t ^ μ - cauchyOptApprox ν μ t))) =
        d * ∫ t in (0 : ℝ)..1, t ^ μ * (t ^ μ - cauchyOptApprox ν μ t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    ring
  rw [hpull] at hmu
  have hd_inv : 1 / d = ∏ k : Fin N, ((μ - ν k) / (μ + ν k + 1)) := by
    unfold d cauchyResidueMain
    rw [one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [inv_div]
  have hrhs :
      (∏ k : Fin N, (μ - ν k)) / ((μ + μ + 1) * ∏ k : Fin N, (μ + ν k + 1)) =
        (1 / (2 * μ + 1)) * (1 / d) := by
    rw [hd_inv, Finset.prod_div_distrib]
    have h2m_ne : 2 * μ + 1 ≠ 0 := by linarith
    have hprod_ne : (∏ k : Fin N, (μ + ν k + 1)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ ↦ by linarith [hν_nonneg k]
    have h2m : μ + μ + 1 = 2 * μ + 1 := by ring
    rw [h2m]
    field_simp [h2m_ne, hprod_ne]
  rw [hrhs] at hmu
  have hdiv_d :
      ∫ t in (0 : ℝ)..1, t ^ μ * (t ^ μ - cauchyOptApprox ν μ t) =
        (1 / d) * ((1 / (2 * μ + 1)) * (1 / d)) := by
    field_simp [hd] at hmu ⊢
    linarith
  rw [hdiv_d]
  have hsq : (1 / d) * ((1 / (2 * μ + 1)) * (1 / d)) = (1 / (2 * μ + 1)) * (1 / d) ^ 2 := by ring
  rw [hsq, hd_inv, ← Finset.prod_pow]

/-- **Complex `L²(0, 1)` squared distance lower bound**:
For ANY complex coefficients `a : Fin N → ℂ`:
`(1 / (2μ + 1)) * ∏ k, ((μ - ν k) / (μ + ν k + 1))² ≤ ∫_0^1 ‖t ^ μ - ∑ k, a k * t ^ (ν k)‖² dt`. -/
theorem l2_dist_sq_lower_bound_complex {N : ℕ} {ν : Fin N → ℝ} {μ : ℝ}
    (hν_inj : Function.Injective ν) (hν_nonneg : ∀ k, 0 ≤ ν k)
    (hμ_nonneg : 0 ≤ μ) (hμ_ne : ∀ k, μ ≠ ν k) (a : Fin N → ℂ) :
    (1 / (2 * μ + 1)) * ∏ k : Fin N, ((μ - ν k) / (μ + ν k + 1)) ^ 2 ≤
      ∫ t in (0 : ℝ)..1,
        ‖((t ^ μ : ℝ) : ℂ) - ∑ k : Fin N, a k * ((t ^ (ν k) : ℝ) : ℂ)‖ ^ 2 := by
  rw [← integral_sub_cauchyOptApprox_sq hν_inj hν_nonneg hμ_nonneg hμ_ne]
  let h_re : ℝ → ℝ := fun t ↦ ∑ k : Fin N, (a k).re * t ^ (ν k)
  have hh_re_cont : Continuous h_re :=
    continuous_finsetSum _ fun k _ ↦
      continuous_const.mul (Real.continuous_rpow_const (hν_nonneg k))
  have hq_cont : Continuous (cauchyOptApprox ν μ) := continuous_cauchyOptApprox hν_nonneg μ
  have hdiff_q_cont : Continuous (fun t : ℝ ↦ t ^ μ - cauchyOptApprox ν μ t) :=
    (Real.continuous_rpow_const hμ_nonneg).sub hq_cont
  have hdiff_h_cont : Continuous (fun t : ℝ ↦ t ^ μ - h_re t) :=
    (Real.continuous_rpow_const hμ_nonneg).sub hh_re_cont
  have h_real_le :
      (∫ t in (0 : ℝ)..1, (t ^ μ - cauchyOptApprox ν μ t) ^ 2) ≤
        ∫ t in (0 : ℝ)..1, (t ^ μ - h_re t) ^ 2 := by
    have horth :
        ∫ t in (0 : ℝ)..1,
          (cauchyOptApprox ν μ t - h_re t) * (t ^ μ - cauchyOptApprox ν μ t) = 0 := by
      have hlin :
          (fun t : ℝ ↦ (cauchyOptApprox ν μ t - h_re t) * (t ^ μ - cauchyOptApprox ν μ t)) =
            fun t : ℝ ↦
              (∑ k : Fin N, (cauchyOptCoeff ν μ k - (a k).re) * t ^ (ν k)) *
                (t ^ μ - cauchyOptApprox ν μ t) := by
        ext t
        congr 1
        unfold cauchyOptApprox h_re
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        ring
      rw [hlin]
      exact integral_linearComb_mul_sub_cauchyOptApprox hν_inj hν_nonneg hμ_nonneg hμ_ne _
    have hexpand :
        (fun t : ℝ ↦ (t ^ μ - h_re t) ^ 2) =
          fun t : ℝ ↦
            ((t ^ μ - cauchyOptApprox ν μ t) ^ 2 +
              2 * ((cauchyOptApprox ν μ t - h_re t) * (t ^ μ - cauchyOptApprox ν μ t))) +
              (cauchyOptApprox ν μ t - h_re t) ^ 2 := by
      ext t; ring
    have hq_sub_h : Continuous (fun t : ℝ ↦ cauchyOptApprox ν μ t - h_re t) :=
      hq_cont.sub hh_re_cont
    have hint_a : IntervalIntegrable
        (fun t : ℝ ↦ (t ^ μ - cauchyOptApprox ν μ t) ^ 2 +
          2 * ((cauchyOptApprox ν μ t - h_re t) * (t ^ μ - cauchyOptApprox ν μ t)))
        MeasureTheory.volume 0 1 :=
      ((hdiff_q_cont.pow 2).add
        (continuous_const.mul (hq_sub_h.mul hdiff_q_cont))).intervalIntegrable 0 1
    have hint_b : IntervalIntegrable
        (fun t : ℝ ↦ (cauchyOptApprox ν μ t - h_re t) ^ 2) MeasureTheory.volume 0 1 :=
      (hq_sub_h.pow 2).intervalIntegrable 0 1
    have hint_a1 : IntervalIntegrable
        (fun t : ℝ ↦ (t ^ μ - cauchyOptApprox ν μ t) ^ 2) MeasureTheory.volume 0 1 :=
      (hdiff_q_cont.pow 2).intervalIntegrable 0 1
    have hint_a2 : IntervalIntegrable
        (fun t : ℝ ↦ 2 * ((cauchyOptApprox ν μ t - h_re t) * (t ^ μ - cauchyOptApprox ν μ t)))
        MeasureTheory.volume 0 1 :=
      (continuous_const.mul (hq_sub_h.mul hdiff_q_cont)).intervalIntegrable 0 1
    rw [hexpand,
      intervalIntegral.integral_add hint_a hint_b,
      intervalIntegral.integral_add hint_a1 hint_a2,
      intervalIntegral.integral_const_mul, horth, mul_zero, add_zero]
    have hsq_nonneg : 0 ≤ ∫ t in (0 : ℝ)..1, (cauchyOptApprox ν μ t - h_re t) ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one fun t _ ↦ sq_nonneg _
    linarith
  have h_cplx_cont :
      Continuous (fun t : ℝ ↦
        ‖((t ^ μ : ℝ) : ℂ) - ∑ k : Fin N, a k * ((t ^ (ν k) : ℝ) : ℂ)‖ ^ 2) := by
    refine Continuous.pow (Continuous.norm ?_) 2
    refine (Complex.continuous_ofReal.comp (Real.continuous_rpow_const hμ_nonneg)).sub ?_
    refine continuous_finsetSum _ fun k _ ↦ ?_
    exact continuous_const.mul
      (Complex.continuous_ofReal.comp (Real.continuous_rpow_const (hν_nonneg k)))
  refine h_real_le.trans (intervalIntegral.integral_mono_on zero_le_one
    ((hdiff_h_cont.pow 2).intervalIntegrable 0 1)
    (h_cplx_cont.intervalIntegrable 0 1) fun t _ ↦ ?_)
  let z_t : ℂ := ((t ^ μ : ℝ) : ℂ) - ∑ k : Fin N, a k * ((t ^ (ν k) : ℝ) : ℂ)
  have hre : z_t.re = t ^ μ - h_re t := by
    simp [z_t, h_re]
  change (t ^ μ - h_re t) ^ 2 ≤ ‖z_t‖ ^ 2
  rw [← hre, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  nlinarith

/-! ### Section 3: Node `15.26` (The Müntz–Szász Theorem) -/

/-- The generating power family `{1, t ^ (λ 0), t ^ (λ 1), …}` in `C([0, 1], ℂ)`. -/
def muntzGenerators (lam : ℕ → ℝ) (hpos : ∀ n, 0 < lam n) : Set C(UnitInterval01, ℂ) :=
  insert 1 (Set.range (fun n : ℕ ↦ realPowerContinuousMap (lam n) (hpos n).le))

/-- The closed linear span `X` of `{1, t ^ (λ 0), t ^ (λ 1), …}` in `C([0, 1], ℂ)`. -/
def muntzSpace (lam : ℕ → ℝ) (hpos : ∀ n, 0 < lam n) : Submodule ℂ C(UnitInterval01, ℂ) :=
  (Submodule.span ℂ (muntzGenerators lam hpos)).topologicalClosure

theorem uniformlySpans_muntzGenerators_iff (lam : ℕ → ℝ) (hpos : ∀ n, 0 < lam n) :
    UniformlySpans (muntzGenerators lam hpos) ↔ muntzSpace lam hpos = ⊤ :=
  Iff.rfl

/-- From Theorem `15.5` (`positive_product_one_sub_iff`): if `0 ≤ u_n < 1` and `∑ u_n = ∞`,
then `∏_{k < N} (1 - u_k) → 0` as `N → ∞`. -/
theorem tendsto_prod_one_sub_zero_of_not_summable {u : ℕ → ℝ}
    (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n < 1) (hdiv : ¬ Summable u) :
    Tendsto (fun N ↦ ∏ k ∈ Finset.range N, (1 - u k)) atTop (𝓝 0) := by
  obtain ⟨p, hp_lim⟩ := product_one_sub_converges hu0 hu1
  have hp_nonneg : 0 ≤ p :=
    ge_of_tendsto' hp_lim fun N ↦ Finset.prod_nonneg fun k _ ↦ sub_nonneg.mpr (hu1 k).le
  have hp_eq : p = 0 := by
    rcases hp_nonneg.eq_or_lt with h0 | hpos
    · exact h0.symm
    · exact False.elim (hdiv ((positive_product_one_sub_iff hu0 hu1).mp ⟨p, hpos, hp_lim⟩))
  rwa [hp_eq] at hp_lim

/-- From Theorem `15.5` (`positive_product_one_sub_iff`): if `0 ≤ u_n < 1` and `∑ u_n < ∞`,
then there is a uniform `p > 0` with `p ≤ ∏_{k < N} (1 - u_k)` for all `N`. -/
theorem exists_pos_le_prod_one_sub_of_summable {u : ℕ → ℝ}
    (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n < 1) (hsum : Summable u) :
    ∃ p : ℝ, 0 < p ∧ ∀ N : ℕ, p ≤ ∏ k ∈ Finset.range N, (1 - u k) := by
  obtain ⟨p, hp_pos, hp_lim⟩ := (positive_product_one_sub_iff hu0 hu1).mpr hsum
  have hanti : Antitone (fun N ↦ ∏ k ∈ Finset.range N, (1 - u k)) := by
    apply antitone_nat_of_succ_le
    intro N
    rw [Finset.prod_range_succ]
    exact mul_le_of_le_one_right
      (Finset.prod_nonneg fun k _ ↦ sub_nonneg.mpr (hu1 k).le) (by linarith [hu0 N])
  exact ⟨p, hp_pos, fun N ↦ hanti.le_of_tendsto hp_lim N⟩

/-- **15.26(a) (Müntz–Szász Theorem, Divergence / Density Direction, RCA pp. 313–315):**
If `0 < λ 0 < λ 1 < …` and `∑ 1 / λ n` diverges, then `{1, t ^ (λ 0), t ^ (λ 1), …}` uniformly
spans `C([0, 1], ℂ)` (`muntzSpace lam hpos = ⊤`). -/
theorem theorem15_26_dense {lam : ℕ → ℝ}
    (hpos : ∀ n, 0 < lam n) (hmono : StrictMono lam)
    (hdiv : ¬ Summable (fun n ↦ 1 / lam n)) :
    muntzSpace lam hpos = ⊤ := by
  let δ : ℝ := min 1 (lam 0 / 2)
  have hδ_pos : 0 < δ := lt_min zero_lt_one (half_pos (hpos 0))
  have hδ_le_half : δ ≤ lam 0 / 2 := min_le_right 1 (lam 0 / 2)
  let μ : ℕ → ℝ := fun k ↦ lam k / δ
  let ν : ℕ → ℝ := fun k ↦ μ k - 1
  have hμ_ge_two : ∀ k, 2 ≤ μ k := by
    intro k
    have hk0 : lam 0 ≤ lam k := hmono.monotone (Nat.zero_le k)
    have h2δ : 2 * δ ≤ lam k := by linarith
    exact (le_div_iff₀ hδ_pos).mpr h2δ
  have hμ_pos : ∀ k, 0 < μ k := fun k ↦ by linarith [hμ_ge_two k]
  have hν_ge_one : ∀ k, 1 ≤ ν k := fun k ↦ by dsimp [ν]; linarith [hμ_ge_two k]
  have hν_nonneg : ∀ k, 0 ≤ ν k := fun k ↦ by linarith [hν_ge_one k]
  have hν_mono : StrictMono ν := by
    intro a b hab
    dsimp [ν, μ]
    exact sub_lt_sub_right (div_lt_div_of_pos_right (hmono hab) hδ_pos) 1
  have hν_div : ¬ Summable (fun k ↦ 1 / ν k) := by
    intro hs
    have hμ_sum : Summable (fun k ↦ 1 / μ k) := by
      refine Summable.of_nonneg_of_le (fun k ↦ by have := hμ_pos k; positivity) (fun k ↦ ?_) hs
      exact one_div_le_one_div_of_le (by linarith [hν_ge_one k]) (by dsimp [ν]; linarith)
    have hlam_sum : Summable (fun k ↦ (1 / δ) * (1 / μ k)) := hμ_sum.mul_left (1 / δ)
    refine hdiv (hlam_sum.congr fun k ↦ ?_)
    dsimp [μ]
    field_simp [hδ_pos.ne', (hpos k).ne']
  let G : Set C(UnitInterval01, ℂ) := muntzGenerators μ hμ_pos
  let Y : Submodule ℂ C(UnitInterval01, ℂ) := muntzSpace μ hμ_pos
  -- Step 1: Every integer power u ^ m with m ≥ 2 belongs to Y.
  have hm_mem : ∀ m : ℕ, 2 ≤ m → realPowerContinuousMap (m : ℝ) m.cast_nonneg ∈ Y := by
    intro m hm
    have hm_real : (2 : ℝ) ≤ (m : ℝ) := Nat.ofNat_le_cast.mpr hm
    by_cases hex : ∃ k : ℕ, μ k = (m : ℝ)
    · obtain ⟨k, hk⟩ := hex
      have heq : realPowerContinuousMap (m : ℝ) m.cast_nonneg =
          realPowerContinuousMap (μ k) (hμ_pos k).le := by
        ext u
        simp [hk]
      rw [heq]
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inr ⟨k, rfl⟩))
    · have hex' : ∀ k : ℕ, μ k ≠ (m : ℝ) := fun k hk ↦ hex ⟨k, hk⟩
      let μ_t : ℝ := (m : ℝ) - 1
      have hμ_t_ge_one : 1 ≤ μ_t := by dsimp [μ_t]; linarith
      have hμ_t_nonneg : 0 ≤ μ_t := by linarith
      have hμ_t_ne : ∀ k, μ_t ≠ ν k := by
        intro k hk
        dsimp [μ_t, ν] at hk
        exact hex' k (by linarith)
      let ν_pre : ∀ N : ℕ, Fin N → ℝ := fun N i ↦ ν i.1
      let P_seq : ℕ → C(UnitInterval01, ℂ) := fun N ↦
        ∑ i : Fin N,
          (((m : ℝ) * cauchyOptCoeff (ν_pre N) μ_t i / μ i.1 : ℝ) : ℂ) •
            realPowerContinuousMap (μ i.1) (hμ_pos i.1).le
      have hP_mem : ∀ N : ℕ, P_seq N ∈ Submodule.span ℂ G := by
        intro N
        refine Submodule.sum_mem _ fun i _ ↦ ?_
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨i.1, rfl⟩))
      let w : ℕ → ℝ := fun k ↦ 1 - ((μ_t - ν k) / (μ_t + ν k + 1)) ^ 2
      have hw_eq : ∀ k : ℕ,
          w k = (2 * (m : ℝ) - 1) * (2 * ν k + 1) / ((m : ℝ) + ν k) ^ 2 := by
        intro k
        have hden : (m : ℝ) + ν k ≠ 0 := by linarith [hν_ge_one k]
        have hsum_eq : μ_t + ν k + 1 = (m : ℝ) + ν k := by dsimp [μ_t]; ring
        dsimp [w]
        rw [hsum_eq]
        dsimp [μ_t]
        field_simp [hden]
        ring
      have hw0 : ∀ k, 0 ≤ w k := by
        intro k
        rw [hw_eq k]
        have : 0 < 2 * (m : ℝ) - 1 := by linarith
        have : 0 < 2 * ν k + 1 := by linarith [hν_ge_one k]
        have : 0 < (m : ℝ) + ν k := by linarith [hν_ge_one k]
        positivity
      have hw1 : ∀ k, w k < 1 := by
        intro k
        dsimp [w]
        have hsq_pos : 0 < ((μ_t - ν k) / (μ_t + ν k + 1)) ^ 2 := by
          apply sq_pos_of_ne_zero
          exact div_ne_zero (sub_ne_zero.mpr (hμ_t_ne k)) (by linarith [hν_ge_one k])
        linarith
      have hw_div : ¬ Summable w := by
        intro hsw
        let C_m : ℝ := (2 * (m : ℝ) - 1) / ((m : ℝ) + 1) ^ 2
        have hCm_pos : 0 < C_m := by
          dsimp [C_m]
          have : 0 < 2 * (m : ℝ) - 1 := by linarith
          positivity
        have hcomp : Summable (fun k ↦ C_m * (1 / ν k)) := by
          refine Summable.of_nonneg_of_le
            (fun k ↦ mul_nonneg hCm_pos.le (by have := hν_ge_one k; positivity))
            (fun k ↦ ?_) hsw
          rw [hw_eq k]
          dsimp [C_m]
          have hν1 : 1 ≤ ν k := hν_ge_one k
          have hd1 : 0 < ((m : ℝ) + 1) ^ 2 * ν k := by positivity
          have hd2 : 0 < ((m : ℝ) + ν k) ^ 2 := by positivity
          rw [mul_one_div, div_div, div_le_div_iff₀ hd1 hd2]
          have hstep1 : (m : ℝ) + ν k ≤ ((m : ℝ) + 1) * ν k := by nlinarith
          have hstep2 : ((m : ℝ) + ν k) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 * (ν k) ^ 2 := by
            have := mul_self_le_mul_self (by positivity) hstep1
            nlinarith
          have hstep3 : ((m : ℝ) + 1) ^ 2 * (ν k) ^ 2 ≤
              (2 * ν k + 1) * (((m : ℝ) + 1) ^ 2 * ν k) := by nlinarith
          have h2m1 : 0 ≤ 2 * (m : ℝ) - 1 := by linarith
          nlinarith
        have hν_s : Summable (fun k ↦ (1 / C_m) * (C_m * (1 / ν k))) := hcomp.mul_left (1 / C_m)
        refine hν_div (hν_s.congr fun k ↦ ?_)
        field_simp [hCm_pos.ne']
      have hprod_zero := tendsto_prod_one_sub_zero_of_not_summable hw0 hw1 hw_div
      have hnorm_bound : ∀ N : ℕ,
          ‖realPowerContinuousMap (m : ℝ) m.cast_nonneg - P_seq N‖ ≤
            Real.sqrt (((m : ℝ) ^ 2 / (2 * (m : ℝ) - 1)) *
              ∏ k ∈ Finset.range N, (1 - w k)) := by
        intro N
        refine (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).mpr fun u ↦ ?_
        have hu0 : 0 ≤ u.1 := u.2.1
        have hu1 : u.1 ≤ 1 := u.2.2
        have hνN_inj : Function.Injective (ν_pre N) := hν_mono.injective.comp Fin.val_injective
        have hνN_nonneg : ∀ i : Fin N, 0 ≤ ν_pre N i := fun i ↦ hν_nonneg i.1
        have hμt_neN : ∀ i : Fin N, μ_t ≠ ν_pre N i := fun i ↦ hμ_t_ne i.1
        have hint_u_m :
            (m : ℝ) * (∫ s in (0 : ℝ)..u.1, s ^ μ_t) = u.1 ^ (m : ℝ) := by
          rw [integral_rpow (Or.inl (by linarith : -1 < μ_t))]
          have hadd : μ_t + 1 = (m : ℝ) := by dsimp [μ_t]; ring
          have hm_ne : (m : ℝ) ≠ 0 := by linarith
          rw [hadd, Real.zero_rpow hm_ne, sub_zero, mul_div_cancel₀ _ hm_ne]
        have hint_u_q :
            (m : ℝ) * (∫ s in (0 : ℝ)..u.1, cauchyOptApprox (ν_pre N) μ_t s) =
              ∑ i : Fin N,
                ((m : ℝ) * cauchyOptCoeff (ν_pre N) μ_t i / μ i.1) * u.1 ^ (μ i.1) := by
          unfold cauchyOptApprox
          have hint_each : ∀ i ∈ (Finset.univ : Finset (Fin N)),
              IntervalIntegrable
                (fun s : ℝ ↦ cauchyOptCoeff (ν_pre N) μ_t i * s ^ ν_pre N i)
                MeasureTheory.volume 0 u.1 :=
            fun i _ ↦ (continuous_const.mul
              (Real.continuous_rpow_const (hνN_nonneg i))).intervalIntegrable 0 u.1
          rw [intervalIntegral.integral_finsetSum hint_each, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [intervalIntegral.integral_const_mul,
            integral_rpow (Or.inl (by linarith [hν_ge_one i.1] : -1 < ν_pre N i))]
          have hadd : ν_pre N i + 1 = μ i.1 := by dsimp [ν_pre, ν]; ring
          have hμ_ne : μ i.1 ≠ 0 := (hμ_pos i.1).ne'
          rw [hadd, Real.zero_rpow hμ_ne, sub_zero]
          ring
        have hdiff_u :
            (realPowerContinuousMap (m : ℝ) m.cast_nonneg - P_seq N) u =
              (((m : ℝ) * ∫ s in (0 : ℝ)..u.1,
                (s ^ μ_t - cauchyOptApprox (ν_pre N) μ_t s) : ℝ) : ℂ) := by
          have hsub_int :
              (∫ s in (0 : ℝ)..u.1, (s ^ μ_t - cauchyOptApprox (ν_pre N) μ_t s)) =
                (∫ s in (0 : ℝ)..u.1, s ^ μ_t) -
                  ∫ s in (0 : ℝ)..u.1, cauchyOptApprox (ν_pre N) μ_t s :=
            intervalIntegral.integral_sub
              ((Real.continuous_rpow_const hμ_t_nonneg).intervalIntegrable 0 u.1)
              ((continuous_cauchyOptApprox hνN_nonneg μ_t).intervalIntegrable 0 u.1)
          rw [hsub_int, mul_sub, hint_u_m, hint_u_q]
          simp [P_seq]
        rw [hdiff_u, Complex.norm_real, Real.norm_eq_abs]
        refine Real.le_sqrt_of_sq_le ?_
        rw [sq_abs, mul_pow]
        have hcs := sq_integral_zero_le_integral_zero_one_sq
          ((Real.continuous_rpow_const hμ_t_nonneg).sub
            (continuous_cauchyOptApprox hνN_nonneg μ_t)) hu0 hu1
        have hl2 := integral_sub_cauchyOptApprox_sq hνN_inj hνN_nonneg hμ_t_nonneg hμt_neN
        have hprod_eq :
            (∏ i : Fin N, ((μ_t - ν_pre N i) / (μ_t + ν_pre N i + 1)) ^ 2) =
              ∏ k ∈ Finset.range N, (1 - w k) := by
          rw [← Fin.prod_univ_eq_prod_range]
          refine Finset.prod_congr rfl fun i _ ↦ ?_
          dsimp [w, ν_pre]
          ring
        have h2mt : 2 * μ_t + 1 = 2 * (m : ℝ) - 1 := by dsimp [μ_t]; ring
        calc
          (m : ℝ) ^ 2 * (∫ s in (0 : ℝ)..u.1,
              (s ^ μ_t - cauchyOptApprox (ν_pre N) μ_t s)) ^ 2
            ≤ (m : ℝ) ^ 2 * ∫ s in (0 : ℝ)..1,
                (s ^ μ_t - cauchyOptApprox (ν_pre N) μ_t s) ^ 2 :=
              mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
          _ = (m : ℝ) ^ 2 * ((1 / (2 * μ_t + 1)) *
                ∏ i : Fin N, ((μ_t - ν_pre N i) / (μ_t + ν_pre N i + 1)) ^ 2) := by
              rw [hl2]
          _ = ((m : ℝ) ^ 2 / (2 * (m : ℝ) - 1)) * ∏ k ∈ Finset.range N, (1 - w k) := by
              rw [hprod_eq, h2mt]
              ring
      have hrhs_tendsto :
          Tendsto (fun N ↦ Real.sqrt (((m : ℝ) ^ 2 / (2 * (m : ℝ) - 1)) *
            ∏ k ∈ Finset.range N, (1 - w k))) atTop (𝓝 0) := by
        have hmul_zero := hprod_zero.const_mul ((m : ℝ) ^ 2 / (2 * (m : ℝ) - 1))
        rw [mul_zero] at hmul_zero
        have hsqrt :
            Tendsto (fun N ↦ Real.sqrt (((m : ℝ) ^ 2 / (2 * (m : ℝ) - 1)) *
              ∏ k ∈ Finset.range N, (1 - w k))) atTop (𝓝 (Real.sqrt 0)) :=
          (Real.continuous_sqrt.tendsto 0).comp hmul_zero
        rwa [Real.sqrt_zero] at hsqrt
      have hdist_zero :
          Tendsto (fun N ↦ dist (P_seq N) (realPowerContinuousMap (m : ℝ) m.cast_nonneg))
            atTop (𝓝 0) := by
        refine squeeze_zero (fun _ ↦ dist_nonneg) (fun N ↦ ?_) hrhs_tendsto
        rw [dist_comm, dist_eq_norm]
        exact hnorm_bound N
      have hP_tendsto :
          Tendsto P_seq atTop (𝓝 (realPowerContinuousMap (m : ℝ) m.cast_nonneg)) :=
        tendsto_iff_dist_tendsto_zero.mpr hdist_zero
      show realPowerContinuousMap (m : ℝ) m.cast_nonneg ∈ Y
      dsimp [Y, muntzSpace]
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      exact mem_closure_of_tendsto hP_tendsto (Eventually.of_forall hP_mem)
  -- Step 2: Stone–Weierstrass applied to φ(u) = u² shows Y = ⊤.
  have hY_top : Y = ⊤ := by
    let φ : C(UnitInterval01, ℂ) := ⟨fun u ↦ (u.1 : ℂ) ^ 2, by fun_prop⟩
    have hstar : star φ = φ := by
      ext u
      simp [φ]
    have hinj : Function.Injective φ := by
      intro u₁ u₂ h
      ext
      have hreal : u₁.1 ^ 2 = u₂.1 ^ 2 := by
        have hc : ((u₁.1 ^ 2 : ℝ) : ℂ) = ((u₂.1 ^ 2 : ℝ) : ℂ) := by simpa [φ] using h
        exact Complex.ofReal_inj.mp hc
      exact (sq_eq_sq₀ u₁.2.1 u₂.2.1).mp hreal
    have hφ_spans := uniformlySpans_powers_of_star_eq_self_of_injective φ hstar hinj
    have hpow_in_Y : ∀ n : ℕ, φ ^ n ∈ Y := by
      intro n
      cases n with
      | zero =>
        rw [pow_zero]
        exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inl rfl))
      | succ k =>
        have h2n : 2 ≤ 2 * (k + 1) := by omega
        have heq : φ ^ (k + 1) = realPowerContinuousMap ((2 * (k + 1) : ℕ) : ℝ) (Nat.cast_nonneg _) := by
          ext u
          simp only [ContinuousMap.pow_apply, φ, ContinuousMap.coe_mk, ← pow_mul,
            realPowerContinuousMap_apply, Real.rpow_natCast, Complex.ofReal_pow]
        rw [heq]
        exact hm_mem (2 * (k + 1)) h2n
    have hsub_le : Submodule.span ℂ (Set.range (fun n : ℕ ↦ φ ^ n)) ≤ Y := by
      rw [Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      exact hpow_in_Y n
    have htop_le : (⊤ : Submodule ℂ C(UnitInterval01, ℂ)) ≤ Y := by
      rw [← hφ_spans]
      exact (Submodule.topologicalClosure_mono hsub_le).trans_eq
        (Submodule.span ℂ G).isClosed_topologicalClosure.submodule_topologicalClosure_eq
    exact top_unique htop_le
  -- Step 3: Pull back along the homeomorphism t ↦ t ^ δ of [0, 1] to obtain muntzSpace lam hpos = ⊤.
  rw [← uniformlySpans_muntzGenerators_iff, uniformlySpans_iff_forall_approx]
  intro f ε hε
  let fwd : C(UnitInterval01, UnitInterval01) :=
    ⟨fun t ↦ ⟨t.1 ^ δ, ⟨Real.rpow_nonneg t.2.1 δ, Real.rpow_le_one t.2.1 t.2.2 hδ_pos.le⟩⟩,
      Continuous.subtype_mk (continuous_subtype_val.rpow_const fun _ ↦ Or.inr hδ_pos.le) _⟩
  let bwd : C(UnitInterval01, UnitInterval01) :=
    ⟨fun u ↦ ⟨u.1 ^ (1 / δ),
        ⟨Real.rpow_nonneg u.2.1 _, Real.rpow_le_one u.2.1 u.2.2 (by positivity)⟩⟩,
      Continuous.subtype_mk (continuous_subtype_val.rpow_const fun _ ↦ Or.inr (by positivity)) _⟩
  have hbwd_fwd : ∀ t : UnitInterval01, bwd (fwd t) = t := by
    intro t
    ext
    dsimp [fwd, bwd]
    rw [← Real.rpow_mul t.2.1, mul_one_div_cancel hδ_pos.ne', Real.rpow_one]
  have hY_spans : UniformlySpans G := hY_top
  obtain ⟨g, hg_span, hg_norm⟩ :=
    (uniformlySpans_iff_forall_approx G).mp hY_spans (f.comp bwd) ε hε
  refine ⟨g.comp fwd, ?_, ?_⟩
  · refine Submodule.span_induction ?_ ?_ ?_ ?_ hg_span
    · rintro h (rfl | ⟨k, rfl⟩)
      · have hone : (1 : C(UnitInterval01, ℂ)).comp fwd = 1 := by ext; simp
        rw [hone]
        exact Submodule.subset_span (Or.inl rfl)
      · have hpow : (realPowerContinuousMap (μ k) (hμ_pos k).le).comp fwd =
            realPowerContinuousMap (lam k) (hpos k).le := by
          ext t
          simp only [ContinuousMap.comp_apply, realPowerContinuousMap_apply, fwd,
            ContinuousMap.coe_mk, Complex.ofReal_inj]
          rw [← Real.rpow_mul t.2.1]
          congr 1
          dsimp [μ]
          exact mul_div_cancel₀ (lam k) hδ_pos.ne'
        rw [hpow]
        exact Submodule.subset_span (Or.inr ⟨k, rfl⟩)
    · have hzero : (0 : C(UnitInterval01, ℂ)).comp fwd = 0 := by ext; simp
      rw [hzero]
      exact Submodule.zero_mem _
    · intro g₁ g₂ _ _ hg₁ hg₂
      have hadd : (g₁ + g₂).comp fwd = g₁.comp fwd + g₂.comp fwd := by ext; simp
      rw [hadd]
      exact Submodule.add_mem _ hg₁ hg₂
    · intro c g₁ _ hg₁
      have hsmul : (c • g₁).comp fwd = c • (g₁.comp fwd) := by ext; simp
      rw [hsmul]
      exact Submodule.smul_mem _ c hg₁
  · rw [ContinuousMap.norm_lt_iff _ hε]
    intro t
    have hft : f t = (f.comp bwd) (fwd t) := by
      simp [hbwd_fwd t]
    change ‖f t - g (fwd t)‖ < ε
    rw [hft]
    exact ((ContinuousMap.norm_lt_iff _ hε).mp hg_norm) (fwd t)

/-- Finite prefix expansion of any element in `Submodule.span ℂ (muntzGenerators lam hpos)`. -/
theorem exists_prefix_sum_of_mem_span_muntzGenerators {lam : ℕ → ℝ} (hpos : ∀ n, 0 < lam n)
    {g : C(UnitInterval01, ℂ)} (hg : g ∈ Submodule.span ℂ (muntzGenerators lam hpos)) :
    ∃ (N : ℕ) (a₀ : ℂ) (a : Fin N → ℂ),
      ∀ t : UnitInterval01,
        g t = a₀ + ∑ k : Fin N, a k * ((t.1 ^ (lam k.1) : ℝ) : ℂ) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
  · rintro f (rfl | ⟨n, rfl⟩)
    · exact ⟨0, 1, Fin.elim0, fun t ↦ by simp⟩
    · refine ⟨n + 1, 0, fun k ↦ if k.1 = n then 1 else 0, fun t ↦ ?_⟩
      dsimp only
      rw [zero_add, Finset.sum_eq_single ⟨n, Nat.lt_succ_self n⟩]
      · simp
      · intro k _ hkn
        have hval : k.1 ≠ n := fun h ↦ hkn (Fin.ext h)
        simp [hval]
      · intro hn_mem
        exact False.elim (hn_mem (Finset.mem_univ _))
  · exact ⟨0, 0, Fin.elim0, fun t ↦ by simp⟩
  · rintro g₁ g₂ - - ⟨N₁, a₀₁, a₁, h₁⟩ ⟨N₂, a₀₂, a₂, h₂⟩
    let N := max N₁ N₂
    refine ⟨N, a₀₁ + a₀₂,
      fun k ↦ (if hk₁ : k.1 < N₁ then a₁ ⟨k.1, hk₁⟩ else 0) +
        (if hk₂ : k.1 < N₂ then a₂ ⟨k.1, hk₂⟩ else 0),
      fun t ↦ ?_⟩
    have hsum1 :
        (∑ k : Fin N, (if hk₁ : k.1 < N₁ then a₁ ⟨k.1, hk₁⟩ else 0) *
          ((t.1 ^ lam k.1 : ℝ) : ℂ)) =
          ∑ k : Fin N₁, a₁ k * ((t.1 ^ lam k.1 : ℝ) : ℂ) := by
      have hle₁ : N₁ ≤ N := le_max_left N₁ N₂
      rw [Fin.sum_univ_eq_sum_range
        (fun i ↦ (if hi : i < N₁ then a₁ ⟨i, hi⟩ else 0) * ((t.1 ^ lam i : ℝ) : ℂ)) N]
      rw [← Finset.sum_range_add_sum_Ico _ hle₁]
      have htail :
          (∑ i ∈ Finset.Ico N₁ N,
            (if hi : i < N₁ then a₁ ⟨i, hi⟩ else 0) * ((t.1 ^ lam i : ℝ) : ℂ)) = 0 := by
        refine Finset.sum_eq_zero fun i hi ↦ ?_
        have hnot : ¬ i < N₁ := not_lt.mpr (Finset.mem_Ico.mp hi).1
        simp [hnot]
      rw [htail, add_zero, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp [k.2]
    have hsum2 :
        (∑ k : Fin N, (if hk₂ : k.1 < N₂ then a₂ ⟨k.1, hk₂⟩ else 0) *
          ((t.1 ^ lam k.1 : ℝ) : ℂ)) =
          ∑ k : Fin N₂, a₂ k * ((t.1 ^ lam k.1 : ℝ) : ℂ) := by
      have hle₂ : N₂ ≤ N := le_max_right N₁ N₂
      rw [Fin.sum_univ_eq_sum_range
        (fun i ↦ (if hi : i < N₂ then a₂ ⟨i, hi⟩ else 0) * ((t.1 ^ lam i : ℝ) : ℂ)) N]
      rw [← Finset.sum_range_add_sum_Ico _ hle₂]
      have htail :
          (∑ i ∈ Finset.Ico N₂ N,
            (if hi : i < N₂ then a₂ ⟨i, hi⟩ else 0) * ((t.1 ^ lam i : ℝ) : ℂ)) = 0 := by
        refine Finset.sum_eq_zero fun i hi ↦ ?_
        have hnot : ¬ i < N₂ := not_lt.mpr (Finset.mem_Ico.mp hi).1
        simp [hnot]
      rw [htail, add_zero, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp [k.2]
    simp only [ContinuousMap.add_apply, h₁ t, h₂ t, add_mul, Finset.sum_add_distrib, hsum1, hsum2]
    ring
  · rintro c g₁ - ⟨N, a₀, a, h⟩
    refine ⟨N, c * a₀, fun k ↦ c * a k, fun t ↦ ?_⟩
    simp only [ContinuousMap.smul_apply, smul_eq_mul, h t, mul_add, Finset.mul_sum, mul_assoc]

/-- **15.26(b) (Müntz–Szász Theorem, Convergence / Non-Membership Direction, RCA pp. 313–315):**
If `0 < λ 0 < λ 1 < …` and `∑ 1 / λ n < ∞`, then for every `μ > 0` with `∀ n, μ ≠ λ n`,
`t ↦ t ^ μ` does NOT belong to `muntzSpace lam hpos`. -/
theorem theorem15_26_not_mem {lam : ℕ → ℝ}
    (hpos : ∀ n, 0 < lam n) (hmono : StrictMono lam)
    (hsum : Summable (fun n ↦ 1 / lam n))
    {μ : ℝ} (hμ : 0 < μ) (hne : ∀ n, μ ≠ lam n) :
    realPowerContinuousMap μ hμ.le ∉ muntzSpace lam hpos := by
  let u : ℕ → ℝ := fun k ↦ 1 - ((μ - lam k) / (μ + lam k + 1)) ^ 2
  have hu_eq : ∀ k : ℕ,
      u k = (2 * μ + 1) * (2 * lam k + 1) / (μ + lam k + 1) ^ 2 := by
    intro k
    have hden : μ + lam k + 1 ≠ 0 := by linarith [hpos k]
    dsimp [u]
    field_simp [hden]
    ring
  have hu0 : ∀ k, 0 ≤ u k := by
    intro k
    rw [hu_eq k]
    have : 0 < 2 * μ + 1 := by linarith
    have : 0 < 2 * lam k + 1 := by linarith [hpos k]
    have : 0 < μ + lam k + 1 := by linarith [hpos k]
    positivity
  have hu1 : ∀ k, u k < 1 := by
    intro k
    dsimp [u]
    have hsq_pos : 0 < ((μ - lam k) / (μ + lam k + 1)) ^ 2 := by
      apply sq_pos_of_ne_zero
      exact div_ne_zero (sub_ne_zero.mpr (hne k)) (by linarith [hpos k])
    linarith
  have hu_sum : Summable u := by
    let C : ℝ := (2 * μ + 1) * (2 + 1 / lam 0)
    refine Summable.of_nonneg_of_le hu0 (fun k ↦ ?_) (hsum.mul_left C)
    rw [hu_eq k]
    dsimp [C]
    have hlam0_pos : 0 < lam 0 := hpos 0
    have hlamk_pos : 0 < lam k := hpos k
    have hlam0_le : lam 0 ≤ lam k := hmono.monotone (Nat.zero_le k)
    have h1_le : 1 ≤ (1 / lam 0) * lam k := by
      rw [one_div_mul_eq_div]
      exact ( one_le_div hlam0_pos ).mpr hlam0_le
    have hnum : (2 * μ + 1) * (2 * lam k + 1) ≤ (2 * μ + 1) * ((2 + 1 / lam 0) * lam k) := by
      have : 0 < 2 * μ + 1 := by linarith
      nlinarith
    have hden_le : (lam k) ^ 2 ≤ (μ + lam k + 1) ^ 2 := by nlinarith
    calc
      (2 * μ + 1) * (2 * lam k + 1) / (μ + lam k + 1) ^ 2
        ≤ (2 * μ + 1) * ((2 + 1 / lam 0) * lam k) / (μ + lam k + 1) ^ 2 :=
          div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ ≤ (2 * μ + 1) * ((2 + 1 / lam 0) * lam k) / (lam k) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hlamk_pos) hden_le
      _ = (2 * μ + 1) * (2 + 1 / lam 0) * (1 / lam k) := by
          field_simp [hlamk_pos.ne']
  obtain ⟨p, hp_pos, hp_le⟩ := exists_pos_le_prod_one_sub_of_summable hu0 hu1 hu_sum
  let c_pos : ℝ := (1 / (2 * μ + 1)) * (μ / (μ + 1)) ^ 2 * p
  have hc_pos : 0 < c_pos := by
    dsimp [c_pos]
    positivity
  have hlower_span : ∀ g ∈ Submodule.span ℂ (muntzGenerators lam hpos),
      Real.sqrt c_pos ≤ ‖realPowerContinuousMap μ hμ.le - g‖ := by
    intro g hg
    obtain ⟨N, a₀, a, hg_eq⟩ := exists_prefix_sum_of_mem_span_muntzGenerators hpos hg
    let ν_ext : Fin (N + 1) → ℝ := Fin.cases 0 (fun k : Fin N ↦ lam k.1)
    let a_ext : Fin (N + 1) → ℂ := Fin.cases a₀ a
    have hν_ext_nonneg : ∀ j : Fin (N + 1), 0 ≤ ν_ext j := by
      refine Fin.cases le_rfl fun k ↦ (hpos k.1).le
    have hν_ext_inj : Function.Injective ν_ext := by
      intro i j
      refine Fin.cases ?_ (fun k₁ ↦ ?_) i
      · refine Fin.cases (fun _ ↦ rfl) (fun k₂ hk ↦ ?_) j
        dsimp [ν_ext] at hk
        exact False.elim ((hpos k₂.1).ne hk)
      · refine Fin.cases (fun hk ↦ ?_) (fun k₂ hk ↦ ?_) j
        · dsimp [ν_ext] at hk
          exact False.elim ((hpos k₁.1).ne' hk)
        · dsimp [ν_ext] at hk
          exact congrArg Fin.succ (Fin.ext (hmono.injective hk))
    have hμ_ne_ext : ∀ j : Fin (N + 1), μ ≠ ν_ext j := by
      refine Fin.cases hμ.ne' fun k ↦ hne k.1
    have hl2 := l2_dist_sq_lower_bound_complex hν_ext_inj hν_ext_nonneg hμ.le hμ_ne_ext a_ext
    have hprod_ext :
        (∏ j : Fin (N + 1), ((μ - ν_ext j) / (μ + ν_ext j + 1)) ^ 2) =
          (μ / (μ + 1)) ^ 2 * ∏ k ∈ Finset.range N, (1 - u k) := by
      rw [Fin.prod_univ_succ]
      congr 1
      · dsimp [ν_ext]
        ring
      · rw [← Fin.prod_univ_eq_prod_range]
        refine Finset.prod_congr rfl fun k _ ↦ ?_
        dsimp [ν_ext, u]
        ring
    have hint_le_norm :
        (∫ t in (0 : ℝ)..1,
          ‖((t ^ μ : ℝ) : ℂ) - ∑ j : Fin (N + 1), a_ext j * ((t ^ (ν_ext j) : ℝ) : ℂ)‖ ^ 2) ≤
          ‖realPowerContinuousMap μ hμ.le - g‖ ^ 2 := by
      have hcplx_cont :
          Continuous (fun t : ℝ ↦
            ‖((t ^ μ : ℝ) : ℂ) - ∑ j : Fin (N + 1), a_ext j * ((t ^ (ν_ext j) : ℝ) : ℂ)‖ ^ 2) := by
        refine Continuous.pow (Continuous.norm ?_) 2
        refine (Complex.continuous_ofReal.comp (Real.continuous_rpow_const hμ.le)).sub ?_
        refine continuous_finsetSum _ fun j _ ↦ ?_
        exact continuous_const.mul
          (Complex.continuous_ofReal.comp (Real.continuous_rpow_const (hν_ext_nonneg j)))
      have hle_const :
          (∫ t in (0 : ℝ)..1,
            ‖((t ^ μ : ℝ) : ℂ) - ∑ j : Fin (N + 1), a_ext j * ((t ^ (ν_ext j) : ℝ) : ℂ)‖ ^ 2) ≤
            ∫ _t in (0 : ℝ)..1, ‖realPowerContinuousMap μ hμ.le - g‖ ^ 2 := by
        refine intervalIntegral.integral_mono_on zero_le_one
          (hcplx_cont.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
          (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) 0 1) fun t ht ↦ ?_
        let t' : UnitInterval01 := ⟨t, ht⟩
        have hsum_t :
            (∑ j : Fin (N + 1), a_ext j * ((t ^ (ν_ext j) : ℝ) : ℂ)) = g t' := by
          rw [Fin.sum_univ_succ, hg_eq t']
          dsimp [a_ext, ν_ext, t']
          simp
        rw [hsum_t]
        have hpt :
            ‖((t ^ μ : ℝ) : ℂ) - g t'‖ ≤ ‖realPowerContinuousMap μ hμ.le - g‖ :=
          ContinuousMap.norm_coe_le_norm (realPowerContinuousMap μ hμ.le - g) t'
        exact pow_le_pow_left₀ (norm_nonneg _) hpt 2
      simpa using hle_const
    have hsq_ge : c_pos ≤ ‖realPowerContinuousMap μ hμ.le - g‖ ^ 2 := by
      calc
        c_pos = (1 / (2 * μ + 1)) * ((μ / (μ + 1)) ^ 2 * p) := by dsimp [c_pos]; ring
        _ ≤ (1 / (2 * μ + 1)) * ((μ / (μ + 1)) ^ 2 * ∏ k ∈ Finset.range N, (1 - u k)) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hp_le N) (sq_nonneg _)) (by positivity)
        _ = (1 / (2 * μ + 1)) * ∏ j : Fin (N + 1), ((μ - ν_ext j) / (μ + ν_ext j + 1)) ^ 2 := by
          rw [hprod_ext]
        _ ≤ ‖realPowerContinuousMap μ hμ.le - g‖ ^ 2 := hl2.trans hint_le_norm
    exact Real.sqrt_le_iff.mpr ⟨norm_nonneg _, hsq_ge⟩
  intro hmem
  rw [muntzSpace, ← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hmem
  obtain ⟨g, hg_span, hdist⟩ := hmem (Real.sqrt c_pos) (Real.sqrt_pos.mpr hc_pos)
  rw [dist_eq_norm] at hdist
  exact not_lt_of_ge (hlower_span g hg_span) hdist

/-- Exact Müntz–Szász density criterion: `{1, t ^ (λ 0), t ^ (λ 1), …}` uniformly spans `C([0, 1], ℂ)`
if and only if `∑ 1 / λ n` diverges. -/
theorem theorem15_26_iff {lam : ℕ → ℝ}
    (hpos : ∀ n, 0 < lam n) (hmono : StrictMono lam) :
    UniformlySpans (muntzGenerators lam hpos) ↔ ¬ Summable (fun n ↦ 1 / lam n) := by
  constructor
  · intro hspan hsum
    have hμ_pos : 0 < lam 0 / 2 := half_pos (hpos 0)
    have hμ_ne : ∀ n, lam 0 / 2 ≠ lam n := by
      intro n
      have h0n : lam 0 ≤ lam n := hmono.monotone (Nat.zero_le n)
      linarith [hpos 0]
    have hnot := theorem15_26_not_mem hpos hmono hsum hμ_pos hμ_ne
    rw [uniformlySpans_muntzGenerators_iff] at hspan
    rw [hspan] at hnot
    exact hnot Submodule.mem_top
  · exact theorem15_26_dense hpos hmono

/-- **15.26 (The Müntz–Szász Theorem, RCA pp. 313–315):**
Let `0 < λ 0 < λ 1 < …`, and let `X = muntzSpace lam hpos` be the uniform closure of the linear
span of `{1, t ^ (λ 0), t ^ (λ 1), …}` in `C([0, 1], ℂ)`.
- If `∑ 1 / λ n = ∞`, then `X = ⊤` (`C([0, 1], ℂ)`).
- If `∑ 1 / λ n < ∞`, and if `μ > 0` with `μ ≠ λ n` for every `n`, then `X` does not contain the
  function `t ↦ t ^ μ`. -/
theorem theorem15_26 {lam : ℕ → ℝ}
    (hpos : ∀ n, 0 < lam n) (hmono : StrictMono lam) :
    (¬ Summable (fun n ↦ 1 / lam n) → muntzSpace lam hpos = ⊤) ∧
      (Summable (fun n ↦ 1 / lam n) →
        ∀ (μ : ℝ) (hμ : 0 < μ), (∀ n, μ ≠ lam n) →
          realPowerContinuousMap μ hμ.le ∉ muntzSpace lam hpos) :=
  ⟨theorem15_26_dense hpos hmono,
    fun hsum μ hμ hne ↦ theorem15_26_not_mem (μ := μ) hpos hmono hsum hμ hne⟩

/-! ### Section 4: Node `15.27` (Remark on Minimal Spanning Families) -/

/-- **15.27(a) (Deleting an Infinite Subcollection While Retaining the Span, RCA p. 315):**
If `{1, t ^ (λ 0), t ^ (λ 1), …}` uniformly spans `C([0, 1], ℂ)`, then the infinite subcollection
`{t ^ (λ (2k + 1)) | k : ℕ}` of odd-indexed nonconstant powers is genuinely infinite, disjoint
from the remaining subfamily `{1, t ^ (λ (2k)) | k : ℕ}`, and deleting it still uniformly spans
`C([0, 1], ℂ)`. Hence no minimal spanning power family of this form exists. -/
theorem theorem15_27_no_minimal_spanning_power_family {lam : ℕ → ℝ}
    (hpos : ∀ n, 0 < lam n) (hmono : StrictMono lam)
    (hspan : UniformlySpans (muntzGenerators lam hpos)) :
    let oddPowers : Set C(UnitInterval01, ℂ) :=
      Set.range (fun k : ℕ ↦ realPowerContinuousMap (lam (2 * k + 1)) (hpos (2 * k + 1)).le)
    oddPowers ⊆ Set.range (fun n : ℕ ↦ realPowerContinuousMap (lam n) (hpos n).le) ∧
      oddPowers.Infinite ∧
      muntzGenerators lam hpos \ oddPowers =
        muntzGenerators (fun k ↦ lam (2 * k)) (fun k ↦ hpos (2 * k)) ∧
      UniformlySpans (muntzGenerators (fun k ↦ lam (2 * k)) (fun k ↦ hpos (2 * k))) := by
  intro oddPowers
  have hdiv : ¬ Summable (fun n ↦ 1 / lam n) := (theorem15_26_iff hpos hmono).mp hspan
  have heven_mono : StrictMono (fun k : ℕ ↦ lam (2 * k)) :=
    fun a b hab ↦ hmono (by omega)
  have heven_div : ¬ Summable (fun k : ℕ ↦ 1 / lam (2 * k)) := by
    intro hseven
    have hsodd : Summable (fun k : ℕ ↦ 1 / lam (2 * k + 1)) := by
      refine Summable.of_nonneg_of_le (fun k ↦ by have := hpos (2 * k + 1); positivity)
        (fun k ↦ ?_) hseven
      exact one_div_le_one_div_of_le (hpos (2 * k)) (hmono (by omega)).le
    have hpair : Summable (fun k : ℕ ↦ 1 / lam (2 * k) + 1 / lam (2 * k + 1)) :=
      hseven.add hsodd
    have hsum_2M : ∀ M : ℕ,
        (∑ n ∈ Finset.range (2 * M), (1 / lam n)) =
          ∑ k ∈ Finset.range M, (1 / lam (2 * k) + 1 / lam (2 * k + 1)) := by
      intro M
      induction M with
      | zero => simp
      | succ M ih =>
        have h2succ : 2 * (M + 1) = 2 * M + 1 + 1 := by omega
        rw [h2succ, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
        ring
    have hfull : Summable (fun n : ℕ ↦ 1 / lam n) := by
      refine summable_of_sum_range_le
        (c := ∑' k : ℕ, (1 / lam (2 * k) + 1 / lam (2 * k + 1)))
        (fun n ↦ by have := hpos n; positivity) fun N ↦ ?_
      have hN_le : N ≤ 2 * N := by omega
      calc
        (∑ n ∈ Finset.range N, (1 / lam n))
          ≤ ∑ n ∈ Finset.range (2 * N), (1 / lam n) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN_le)
              fun i _ _ ↦ by have := hpos i; positivity
        _ = ∑ k ∈ Finset.range N, (1 / lam (2 * k) + 1 / lam (2 * k + 1)) := hsum_2M N
        _ ≤ ∑' k : ℕ, (1 / lam (2 * k) + 1 / lam (2 * k + 1)) :=
            hpair.sum_le_tsum (Finset.range N) fun k _ ↦ by
              have := hpos (2 * k); have := hpos (2 * k + 1); positivity
    exact hdiv hfull
  refine ⟨?_, ?_, ?_, theorem15_26_dense (fun k ↦ hpos (2 * k)) heven_mono heven_div⟩
  · rintro _ ⟨k, rfl⟩
    exact ⟨2 * k + 1, rfl⟩
  · refine Set.infinite_range_of_injective fun a b hab ↦ ?_
    have hlam_eq := realPowerContinuousMap_inj (hpos (2 * a + 1)).le (hpos (2 * b + 1)).le hab
    have hidx := hmono.injective hlam_eq
    omega
  · ext f
    simp only [muntzGenerators, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_range, oddPowers]
    constructor
    · rintro ⟨rfl | ⟨n, rfl⟩, hnot_odd⟩
      · exact Or.inl rfl
      · rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
        · exact Or.inr ⟨k, rfl⟩
        · exact False.elim (hnot_odd ⟨k, rfl⟩)
    · rintro (rfl | ⟨k, rfl⟩)
      · refine ⟨Or.inl rfl, ?_⟩
        rintro ⟨m, hm⟩
        exact realPowerContinuousMap_ne_one_of_pos (hpos (2 * m + 1)) hm
      · refine ⟨Or.inr ⟨2 * k, rfl⟩, ?_⟩
        rintro ⟨m, hm⟩
        have hlam_eq := realPowerContinuousMap_inj (hpos (2 * m + 1)).le (hpos (2 * k)).le hm
        have hidx := hmono.injective hlam_eq
        omega

/-- **15.27(b) (Orthonormal Contrast, RCA p. 315):**
In any complex inner product space (in particular any complex Hilbert space), for any orthonormal
family `e : ι → H` and any index `i₀ : ι`, deleting `e i₀` leaves `e i₀` outside the closed linear
span of the remaining vectors, strictly reducing the closed span. -/
theorem theorem15_27_orthonormal_contrast
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} {e : ι → H} (he : Orthonormal ℂ e) (i₀ : ι) :
    e i₀ ∉ (Submodule.span ℂ (e '' {i : ι | i ≠ i₀})).topologicalClosure ∧
      (Submodule.span ℂ (e '' {i : ι | i ≠ i₀})).topologicalClosure <
        (Submodule.span ℂ (Set.range e)).topologicalClosure := by
  have horth_span : ∀ x ∈ Submodule.span ℂ (e '' {i : ι | i ≠ i₀}), ⟪e i₀, x⟫_ℂ = 0 := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, hi, rfl⟩
      exact he.inner_eq_zero (Ne.symm hi)
    · simp
    · intro u v _ _ hu hv
      rw [inner_add_right, hu, hv, add_zero]
    · intro c u _ hu
      rw [inner_smul_right, hu, mul_zero]
  have hclosed : IsClosed {x : H | ⟪e i₀, x⟫_ℂ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have horth_closure :
      ∀ x ∈ (Submodule.span ℂ (e '' {i : ι | i ≠ i₀})).topologicalClosure, ⟪e i₀, x⟫_ℂ = 0 := by
    intro x hx
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hx
    exact closure_minimal horth_span hclosed hx
  have hnot_mem : e i₀ ∉ (Submodule.span ℂ (e '' {i : ι | i ≠ i₀})).topologicalClosure := by
    intro hmem
    have h0 := horth_closure (e i₀) hmem
    rw [inner_self_eq_norm_sq_to_K, he.norm_eq_one i₀] at h0
    norm_num at h0
  refine ⟨hnot_mem, lt_of_le_of_ne ?_ ?_⟩
  · exact Submodule.topologicalClosure_mono (Submodule.span_mono (Set.image_subset_range e _))
  · intro heq
    apply hnot_mem
    rw [heq]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i₀, rfl⟩)

/-- **15.27(c), part 1 (Non-Spanning Family: Deleting `1`, RCA p. 315):**
For any positive exponent sequence `lam`, `1` never lies in the uniform closure of the span of the
nonconstant powers `{t ^ (λ n) | n : ℕ}` (by evaluation at `0`), so deleting `1` strictly reduces
`muntzSpace lam hpos`. -/
theorem theorem15_27_delete_one {lam : ℕ → ℝ} (hpos : ∀ n, 0 < lam n) :
    (1 : C(UnitInterval01, ℂ)) ∉
        (Submodule.span ℂ
          (Set.range (fun n : ℕ ↦ realPowerContinuousMap (lam n) (hpos n).le))).topologicalClosure ∧
      (Submodule.span ℂ
          (Set.range (fun n : ℕ ↦ realPowerContinuousMap (lam n) (hpos n).le))).topologicalClosure <
        muntzSpace lam hpos := by
  let z₀ : UnitInterval01 := ⟨0, by norm_num⟩
  let S : Set C(UnitInterval01, ℂ) :=
    Set.range (fun n : ℕ ↦ realPowerContinuousMap (lam n) (hpos n).le)
  have heval_span : ∀ g ∈ Submodule.span ℂ S, g z₀ = 0 := by
    intro g hg
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨n, rfl⟩
      exact realPowerContinuousMap_eval_zero_of_pos (hpos n)
    · simp
    · intro u v _ _ hu hv
      simp [hu, hv]
    · intro c u _ hu
      simp [hu]
  have hclosed : IsClosed {g : C(UnitInterval01, ℂ) | g z₀ = 0} :=
    isClosed_eq (continuous_eval_const z₀) continuous_const
  have heval_closure : ∀ g ∈ (Submodule.span ℂ S).topologicalClosure, g z₀ = 0 := by
    intro g hg
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hg
    exact closure_minimal heval_span hclosed hg
  have hnot_mem : (1 : C(UnitInterval01, ℂ)) ∉ (Submodule.span ℂ S).topologicalClosure := by
    intro hmem
    have h0 := heval_closure 1 hmem
    simp only [ContinuousMap.one_apply] at h0
    exact one_ne_zero h0
  refine ⟨hnot_mem, lt_of_le_of_ne ?_ ?_⟩
  · exact Submodule.topologicalClosure_mono
      (Submodule.span_mono (Set.subset_insert 1 S))
  · intro heq
    apply hnot_mem
    rw [heq]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inl rfl))

/-- **15.27(c), part 2 (Non-Spanning Family: Deleting `t ^ (λ n₀)`, RCA p. 315):**
If `{1, t ^ (λ 0), t ^ (λ 1), …}` does NOT uniformly span `C([0, 1], ℂ)`, then for every `n₀ : ℕ`,
`t ^ (λ n₀)` does not belong to the closed span of the remaining generators, so deleting any power
strictly reduces `muntzSpace lam hpos`. -/
theorem theorem15_27_delete_power {lam : ℕ → ℝ}
    (hpos : ∀ n, 0 < lam n) (hmono : StrictMono lam)
    (hnot_span : ¬ UniformlySpans (muntzGenerators lam hpos)) (n₀ : ℕ) :
    let skip : ℕ → ℕ := fun k ↦ if k < n₀ then k else k + 1
    realPowerContinuousMap (lam n₀) (hpos n₀).le ∉
        muntzSpace (fun k ↦ lam (skip k)) (fun k ↦ hpos (skip k)) ∧
      muntzSpace (fun k ↦ lam (skip k)) (fun k ↦ hpos (skip k)) < muntzSpace lam hpos := by
  intro skip
  have hsum : Summable (fun n ↦ 1 / lam n) := by
    by_contra hdiv
    exact hnot_span (theorem15_26_dense hpos hmono hdiv)
  have hskip_mono : StrictMono skip := by
    intro a b hab
    dsimp [skip]
    split_ifs <;> omega
  have hlam'_mono : StrictMono (fun k ↦ lam (skip k)) := hmono.comp hskip_mono
  have hlam'_sum : Summable (fun k ↦ 1 / lam (skip k)) :=
    hsum.comp_injective hskip_mono.injective
  have hne : ∀ k : ℕ, lam n₀ ≠ lam (skip k) := by
    intro k heq
    have hidx := hmono.injective heq
    dsimp [skip] at hidx
    split_ifs at hidx <;> omega
  have hnot_mem :=
    theorem15_26_not_mem (fun k ↦ hpos (skip k)) hlam'_mono hlam'_sum (hpos n₀) hne
  refine ⟨hnot_mem, lt_of_le_of_ne ?_ ?_⟩
  · refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
    rintro f (rfl | ⟨k, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨skip k, rfl⟩
  · intro heq
    apply hnot_mem
    rw [heq]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inr ⟨n₀, rfl⟩))

/-- **15.27(c), unified set-deletion form (RCA p. 315):**
If `muntzGenerators lam hpos` does not uniformly span `C([0, 1], ℂ)`, then deleting *any* single
element `f ∈ muntzGenerators lam hpos` strictly reduces the closed linear span. -/
theorem theorem15_27_nonspanning_strict_delete {lam : ℕ → ℝ}
    (hpos : ∀ n, 0 < lam n) (hmono : StrictMono lam)
    (hnot_span : ¬ UniformlySpans (muntzGenerators lam hpos))
    {f : C(UnitInterval01, ℂ)} (hf : f ∈ muntzGenerators lam hpos) :
    f ∉ (Submodule.span ℂ (muntzGenerators lam hpos \ {f})).topologicalClosure ∧
      (Submodule.span ℂ (muntzGenerators lam hpos \ {f})).topologicalClosure <
        muntzSpace lam hpos := by
  rcases hf with rfl | ⟨n₀, rfl⟩
  · have hdiff :
        muntzGenerators lam hpos \ {(1 : C(UnitInterval01, ℂ))} =
          Set.range (fun n : ℕ ↦ realPowerContinuousMap (lam n) (hpos n).le) := by
      ext g
      simp only [muntzGenerators, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_range,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨rfl | ⟨n, rfl⟩, hne1⟩
        · exact False.elim (hne1 rfl)
        · exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨Or.inr ⟨n, rfl⟩, realPowerContinuousMap_ne_one_of_pos (hpos n)⟩
    rw [hdiff]
    exact theorem15_27_delete_one hpos
  · let skip : ℕ → ℕ := fun k ↦ if k < n₀ then k else k + 1
    have hdiff :
        muntzGenerators lam hpos \ {realPowerContinuousMap (lam n₀) (hpos n₀).le} =
          muntzGenerators (fun k ↦ lam (skip k)) (fun k ↦ hpos (skip k)) := by
      ext g
      simp only [muntzGenerators, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_range,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨rfl | ⟨n, rfl⟩, hne_n0⟩
        · exact Or.inl rfl
        · refine Or.inr ?_
          rcases lt_trichotomy n n₀ with hlt | rfl | hgt
          · refine ⟨n, ?_⟩
            ext t
            simp [skip, hlt]
          · exact False.elim (hne_n0 rfl)
          · refine ⟨n - 1, ?_⟩
            have hnot_lt : ¬ n - 1 < n₀ := by omega
            have hsucc : n - 1 + 1 = n := by omega
            ext t
            simp [skip, hnot_lt, hsucc]
      · rintro (rfl | ⟨k, rfl⟩)
        · exact ⟨Or.inl rfl, (realPowerContinuousMap_ne_one_of_pos (hpos n₀)).symm⟩
        · refine ⟨Or.inr ⟨skip k, rfl⟩, ?_⟩
          intro heq
          have hlam_eq := realPowerContinuousMap_inj (hpos (skip k)).le (hpos n₀).le heq
          have hidx := hmono.injective hlam_eq
          dsimp [skip] at hidx
          split_ifs at hidx <;> omega
    rw [hdiff]
    exact theorem15_27_delete_power hpos hmono hnot_span n₀

/-- **15.27 (Remark on Minimal Spanning Families, Orthonormal Contrast, and Non-Spanning Deletion,
RCA p. 315):**
With `0 < λ 0 < λ 1 < …` and `F_lam = {1, t ^ (λ 0), t ^ (λ 1), …}`:
1. If `F_lam` uniformly spans `C([0, 1], ℂ)`, the infinite subcollection `{t ^ (λ (2k + 1))}` of
   nonconstant powers can be deleted while retaining `UniformlySpans`.
2. In contrast, deleting any vector `e i₀` from an orthonormal family `e` in a complex Hilbert
   (or inner product) space strictly reduces its closed linear span.
3. If `F_lam` does NOT uniformly span `C([0, 1], ℂ)`, deleting any single element `f ∈ F_lam`
   strictly reduces its closed linear span (`muntzSpace lam hpos`). -/
theorem theorem15_27 {lam : ℕ → ℝ} (hpos : ∀ n, 0 < lam n) (hmono : StrictMono lam) :
    (UniformlySpans (muntzGenerators lam hpos) →
      UniformlySpans (muntzGenerators (fun k ↦ lam (2 * k)) (fun k ↦ hpos (2 * k)))) ∧
    (∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        {ι : Type*} {e : ι → H},
      Orthonormal ℂ e → ∀ i₀ : ι,
        e i₀ ∉ (Submodule.span ℂ (e '' {i : ι | i ≠ i₀})).topologicalClosure) ∧
    (¬ UniformlySpans (muntzGenerators lam hpos) →
      ((1 : C(UnitInterval01, ℂ)) ∉
          (Submodule.span ℂ
            (Set.range (fun n : ℕ ↦ realPowerContinuousMap (lam n) (hpos n).le))).topologicalClosure ∧
        ∀ n₀ : ℕ,
          realPowerContinuousMap (lam n₀) (hpos n₀).le ∉
            muntzSpace (fun k ↦ lam (if k < n₀ then k else k + 1))
              (fun k ↦ hpos (if k < n₀ then k else k + 1)))) :=
  ⟨fun hspan ↦ (theorem15_27_no_minimal_spanning_power_family hpos hmono hspan).2.2.2,
    fun he i₀ ↦ (theorem15_27_orthonormal_contrast he i₀).1,
    fun hnot ↦
      ⟨(theorem15_27_delete_one hpos).1,
        fun n₀ ↦ (theorem15_27_delete_power hpos hmono hnot n₀).1⟩⟩

#print axioms UnitInterval01
#print axioms realPowerContinuousMap
#print axioms realPowerContinuousMap_apply
#print axioms realPowerContinuousMap_zero
#print axioms realPowerContinuousMap_natCast
#print axioms realPowerContinuousMap_eval_zero_of_pos
#print axioms realPowerContinuousMap_ne_one_of_pos
#print axioms realPowerContinuousMap_inj
#print axioms UniformlySpans
#print axioms uniformlySpans_iff_dense
#print axioms uniformlySpans_iff_forall_approx
#print axioms uniformlySpans_unitInterval_iff_pointwise
#print axioms uniformlySpans_powers_of_star_eq_self_of_injective
#print axioms theorem15_25
#print axioms theorem15_25_realPower
#print axioms integral_zero_one_rpow
#print axioms sq_integral_zero_le_integral_zero_one_sq
#print axioms cauchyResidueMain
#print axioms cauchyResidueAux
#print axioms cauchyResidueMain_ne_zero
#print axioms cauchy_partial_fraction_identity
#print axioms cauchyOptCoeff
#print axioms cauchyOptApprox
#print axioms continuous_cauchyOptApprox
#print axioms integral_rpow_mul_sub_cauchyOptApprox
#print axioms integral_rpow_nu_mul_sub_cauchyOptApprox
#print axioms integral_linearComb_mul_sub_cauchyOptApprox
#print axioms integral_sub_cauchyOptApprox_sq
#print axioms l2_dist_sq_lower_bound_complex
#print axioms muntzGenerators
#print axioms muntzSpace
#print axioms uniformlySpans_muntzGenerators_iff
#print axioms tendsto_prod_one_sub_zero_of_not_summable
#print axioms exists_pos_le_prod_one_sub_of_summable
#print axioms theorem15_26_dense
#print axioms exists_prefix_sum_of_mem_span_muntzGenerators
#print axioms theorem15_26_not_mem
#print axioms theorem15_26_iff
#print axioms theorem15_26
#print axioms theorem15_27_no_minimal_spanning_power_family
#print axioms theorem15_27_orthonormal_contrast
#print axioms theorem15_27_delete_one
#print axioms theorem15_27_delete_power
#print axioms theorem15_27_nonspanning_strict_delete
#print axioms theorem15_27

/-- Real-valued power map `t ↦ t ^ α` in real `C([0, 1], ℝ)`. -/
def realPowerContinuousMapReal (α : ℝ) (hα : 0 ≤ α) : C(UnitInterval01, ℝ) :=
  ⟨fun t ↦ t.1 ^ α, continuous_subtype_val.rpow_const fun _ ↦ Or.inr hα⟩

/-- Uniform spanning in real `C(X, ℝ)`. -/
def UniformlySpansReal {X : Type*} [TopologicalSpace X] [CompactSpace X] (F : Set C(X, ℝ)) : Prop :=
  (Submodule.span ℝ F).topologicalClosure = ⊤

/-- Real Müntz–Szász generators `{1, t ^ (λ 0), t ^ (λ 1), …}` in `C([0, 1], ℝ)`. -/
def muntzGeneratorsReal (lam : ℕ → ℝ) (hpos : ∀ n, 0 < lam n) : Set C(UnitInterval01, ℝ) :=
  insert 1 (Set.range (fun n : ℕ ↦ realPowerContinuousMapReal (lam n) (hpos n).le))

/-- Uniform closure of the real linear span of `muntzGeneratorsReal` in `C([0, 1], ℝ)`. -/
def muntzSpaceReal (lam : ℕ → ℝ) (hpos : ∀ n, 0 < lam n) : Submodule ℝ C(UnitInterval01, ℝ) :=
  (Submodule.span ℝ (muntzGeneratorsReal lam hpos)).topologicalClosure

def ofRealUnitCM (f : C(UnitInterval01, ℝ)) : C(UnitInterval01, ℂ) :=
  ⟨fun t ↦ (f t : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

def reUnitCM (g : C(UnitInterval01, ℂ)) : C(UnitInterval01, ℝ) :=
  ⟨fun t ↦ (g t).re, Complex.continuous_re.comp g.continuous⟩

def imUnitCM (g : C(UnitInterval01, ℂ)) : C(UnitInterval01, ℝ) :=
  ⟨fun t ↦ (g t).im, Complex.continuous_im.comp g.continuous⟩

theorem continuous_ofRealUnitCM : Continuous ofRealUnitCM := by
  rw [Metric.continuous_iff]
  intro f ε hε
  refine ⟨ε, hε, fun f' hd ↦ ?_⟩
  rw [dist_eq_norm] at hd ⊢
  refine (ContinuousMap.norm_lt_iff _ hε).mpr fun t ↦ ?_
  have ht := ((ContinuousMap.norm_lt_iff _ hε).mp hd) t
  change ‖(f' t : ℂ) - (f t : ℂ)‖ < ε
  rwa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem ofRealUnitCM_image_muntzGenerators {lam : ℕ → ℝ} (hpos : ∀ n, 0 < lam n) :
    ofRealUnitCM '' muntzGeneratorsReal lam hpos = muntzGenerators lam hpos := by
  ext g
  simp only [muntzGeneratorsReal, muntzGenerators, Set.image_insert_eq, Set.mem_insert_iff,
    Set.mem_image, Set.mem_range]
  have h1 : ofRealUnitCM 1 = 1 := by ext t; simp [ofRealUnitCM]
  rw [h1]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, by ext t; rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨realPowerContinuousMapReal (lam n) (hpos n).le, ⟨n, rfl⟩, by ext t; rfl⟩

theorem ofRealUnitCM_mem_span_complex {F : Set C(UnitInterval01, ℝ)}
    {p : C(UnitInterval01, ℝ)} (hp : p ∈ Submodule.span ℝ F) :
    ofRealUnitCM p ∈ Submodule.span ℂ (ofRealUnitCM '' F) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
  · intro x hx
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  · have h0 : ofRealUnitCM 0 = 0 := by ext t; simp [ofRealUnitCM]
    rw [h0]; exact zero_mem _
  · intro x y _ _ hx hy
    have hadd : ofRealUnitCM (x + y) = ofRealUnitCM x + ofRealUnitCM y := by
      ext t; simp [ofRealUnitCM]
    rw [hadd]; exact add_mem hx hy
  · intro r x _ hx
    have hr : ofRealUnitCM (r • x) = (r : ℂ) • ofRealUnitCM x := by
      ext t; simp [ofRealUnitCM]
    rw [hr]; exact Submodule.smul_mem _ _ hx

theorem ofRealUnitCM_mem_closure_complex {F : Set C(UnitInterval01, ℝ)}
    {p : C(UnitInterval01, ℝ)} (hp : p ∈ (Submodule.span ℝ F).topologicalClosure) :
    ofRealUnitCM p ∈ (Submodule.span ℂ (ofRealUnitCM '' F)).topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hp ⊢
  have hpre : (Submodule.span ℝ F : Set C(UnitInterval01, ℝ)) ⊆
      ofRealUnitCM ⁻¹' closure (Submodule.span ℂ (ofRealUnitCM '' F)) :=
    fun x hx ↦ subset_closure (ofRealUnitCM_mem_span_complex hx)
  exact closure_minimal hpre (isClosed_closure.preimage continuous_ofRealUnitCM) hp

theorem reUnitCM_smul_mem_span_real {F : Set C(UnitInterval01, ℝ)}
    {w : C(UnitInterval01, ℂ)} (hw : w ∈ Submodule.span ℂ (ofRealUnitCM '' F)) :
    ∀ c : ℂ, reUnitCM (c • w) ∈ Submodule.span ℝ F := by
  refine Submodule.span_induction
    (p := fun w _ ↦ ∀ c : ℂ, reUnitCM (c • w) ∈ Submodule.span ℝ F) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨f, hf, rfl⟩ a
    have heq : reUnitCM (a • ofRealUnitCM f) = a.re • f := by
      ext t; simp [reUnitCM, ofRealUnitCM]
    rw [heq]; exact Submodule.smul_mem _ _ (Submodule.subset_span hf)
  · intro a
    have h0 : reUnitCM (a • 0) = 0 := by ext t; simp [reUnitCM]
    rw [h0]; exact zero_mem _
  · intro x y _ _ hx hy a
    have hadd : reUnitCM (a • (x + y)) = reUnitCM (a • x) + reUnitCM (a • y) := by
      ext t; simp [reUnitCM, mul_add]
    rw [hadd]; exact add_mem (hx a) (hy a)
  · intro b x _ hx a
    rw [smul_smul]; exact hx (a * b)

theorem uniformlySpansReal_iff_uniformlySpans (F : Set C(UnitInterval01, ℝ)) :
    UniformlySpansReal F ↔ UniformlySpans (ofRealUnitCM '' F) := by
  have hL : UniformlySpansReal F ↔ Dense (Submodule.span ℝ F : Set C(UnitInterval01, ℝ)) := by
    rw [UniformlySpansReal, SetLike.ext'_iff, Submodule.topologicalClosure_coe, Submodule.top_coe,
      dense_iff_closure_eq]
  have hR : UniformlySpans (ofRealUnitCM '' F) ↔
      Dense (Submodule.span ℂ (ofRealUnitCM '' F) : Set C(UnitInterval01, ℂ)) := by
    rw [UniformlySpans, SetLike.ext'_iff, Submodule.topologicalClosure_coe, Submodule.top_coe,
      dense_iff_closure_eq]
  rw [hL, hR, Metric.dense_iff, Metric.dense_iff]
  constructor
  · intro h g ε hε
    have hε2 : 0 < ε / 2 := half_pos hε
    obtain ⟨p₁, hp₁_ball, hp₁_span⟩ := h (reUnitCM g) (ε / 2) hε2
    obtain ⟨p₂, hp₂_ball, hp₂_span⟩ := h (imUnitCM g) (ε / 2) hε2
    let q : C(UnitInterval01, ℂ) := ofRealUnitCM p₁ + Complex.I • ofRealUnitCM p₂
    have hq_span : q ∈ Submodule.span ℂ (ofRealUnitCM '' F) :=
      add_mem (ofRealUnitCM_mem_span_complex hp₁_span)
        (Submodule.smul_mem _ _ (ofRealUnitCM_mem_span_complex hp₂_span))
    refine ⟨q, ?_, hq_span⟩
    rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hp₁_ball hp₂_ball ⊢
    refine (ContinuousMap.norm_lt_iff _ hε).mpr fun t ↦ ?_
    have ht1 : |((g t).re - p₁ t)| < ε / 2 :=
      ((ContinuousMap.norm_lt_iff _ hε2).mp hp₁_ball) t
    have ht2 : |((g t).im - p₂ t)| < ε / 2 :=
      ((ContinuousMap.norm_lt_iff _ hε2).mp hp₂_ball) t
    have hsplit : g t - q t = (((g t).re - p₁ t : ℝ) : ℂ) +
        Complex.I * (((g t).im - p₂ t : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [q, ofRealUnitCM]
    rw [ContinuousMap.sub_apply, hsplit]
    calc ‖(((g t).re - p₁ t : ℝ) : ℂ) + Complex.I * (((g t).im - p₂ t : ℝ) : ℂ)‖
        ≤ ‖(((g t).re - p₁ t : ℝ) : ℂ)‖ + ‖Complex.I * (((g t).im - p₂ t : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ = |((g t).re - p₁ t)| + |((g t).im - p₂ t)| := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ < ε / 2 + ε / 2 := add_lt_add ht1 ht2
      _ = ε := add_halves ε
  · intro h f ε hε
    obtain ⟨g, hg_ball, hg_span⟩ := h (ofRealUnitCM f) ε hε
    refine ⟨reUnitCM g, ?_, by simpa using reUnitCM_smul_mem_span_real hg_span 1⟩
    rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hg_ball ⊢
    refine (ContinuousMap.norm_lt_iff _ hε).mpr fun t ↦ ?_
    have ht : ‖(f t : ℂ) - g t‖ < ε := ((ContinuousMap.norm_lt_iff _ hε).mp hg_ball) t
    have hre : |f t - (g t).re| ≤ ‖(f t : ℂ) - g t‖ := by
      simpa using Complex.abs_re_le_norm ((f t : ℂ) - g t)
    exact hre.trans_lt ht

theorem theorem15_25_real_aux
    (h25 : UniformlySpans (Set.range (fun n : ℕ ↦
      (⟨fun t : UnitInterval01 ↦ (t.1 : ℂ) ^ n, by fun_prop⟩ : C(UnitInterval01, ℂ))))) :
    UniformlySpansReal
      (Set.range (fun n : ℕ ↦ (⟨fun t : UnitInterval01 ↦ t.1 ^ n, by fun_prop⟩ :
        C(UnitInterval01, ℝ)))) := by
  rw [uniformlySpansReal_iff_uniformlySpans]
  convert h25 using 1
  ext g
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, by ext t; simp [ofRealUnitCM]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨⟨fun t ↦ t.1 ^ n, by fun_prop⟩, ⟨n, rfl⟩, by ext t; simp [ofRealUnitCM]⟩

theorem theorem15_26_real_aux {lam : ℕ → ℝ} (hpos : ∀ n, 0 < lam n)
    (h26 : (¬ Summable (fun n ↦ 1 / lam n) → muntzSpace lam hpos = ⊤) ∧
      (Summable (fun n ↦ 1 / lam n) →
        ∀ (μ : ℝ) (hμ : 0 < μ), (∀ n, μ ≠ lam n) →
          realPowerContinuousMap μ hμ.le ∉ muntzSpace lam hpos)) :
    (¬ Summable (fun n ↦ 1 / lam n) → muntzSpaceReal lam hpos = ⊤) ∧
      (Summable (fun n ↦ 1 / lam n) →
        ∀ (μ : ℝ) (hμ : 0 < μ), (∀ n, μ ≠ lam n) →
          realPowerContinuousMapReal μ hμ.le ∉ muntzSpaceReal lam hpos) := by
  refine ⟨fun hdiv ↦ ?_, fun hsum μ hμ hne hmem ↦ ?_⟩
  · change UniformlySpansReal (muntzGeneratorsReal lam hpos)
    rw [uniformlySpansReal_iff_uniformlySpans, ofRealUnitCM_image_muntzGenerators]
    exact h26.1 hdiv
  · have hmem_c := ofRealUnitCM_mem_closure_complex hmem
    rw [ofRealUnitCM_image_muntzGenerators] at hmem_c
    have hpow : ofRealUnitCM (realPowerContinuousMapReal μ hμ.le) =
        realPowerContinuousMap μ hμ.le := by ext t; rfl
    rw [hpow] at hmem_c
    exact h26.2 hsum μ hμ hne hmem_c

theorem theorem15_27_real_aux {lam : ℕ → ℝ} (hpos : ∀ n, 0 < lam n)
    (h27 : (UniformlySpans (muntzGenerators lam hpos) →
        UniformlySpans (muntzGenerators (fun k ↦ lam (2 * k)) (fun k ↦ hpos (2 * k)))) ∧
      (¬ UniformlySpans (muntzGenerators lam hpos) →
        ((1 : C(UnitInterval01, ℂ)) ∉
            (Submodule.span ℂ
              (Set.range (fun n : ℕ ↦ realPowerContinuousMap (lam n) (hpos n).le))).topologicalClosure ∧
          ∀ n₀ : ℕ,
            realPowerContinuousMap (lam n₀) (hpos n₀).le ∉
              muntzSpace (fun k ↦ lam (if k < n₀ then k else k + 1))
                (fun k ↦ hpos (if k < n₀ then k else k + 1))))) :
    (UniformlySpansReal (muntzGeneratorsReal lam hpos) →
      UniformlySpansReal (muntzGeneratorsReal (fun k ↦ lam (2 * k)) (fun k ↦ hpos (2 * k)))) ∧
    (∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        {ι : Type*} {e : ι → H},
      Orthonormal ℝ e → ∀ i₀ : ι,
        e i₀ ∉ (Submodule.span ℝ (e '' {i : ι | i ≠ i₀})).topologicalClosure) ∧
    (¬ UniformlySpansReal (muntzGeneratorsReal lam hpos) →
      ((1 : C(UnitInterval01, ℝ)) ∉
          (Submodule.span ℝ
            (Set.range (fun n : ℕ ↦ realPowerContinuousMapReal (lam n) (hpos n).le))).topologicalClosure ∧
        ∀ n₀ : ℕ,
          realPowerContinuousMapReal (lam n₀) (hpos n₀).le ∉
            muntzSpaceReal (fun k ↦ lam (if k < n₀ then k else k + 1))
              (fun k ↦ hpos (if k < n₀ then k else k + 1)))) := by
  refine ⟨fun hspan ↦ ?_, fun {H} _ _ {ι} {e} he i₀ ↦ ?_, fun hnot ↦ ⟨?_, fun n₀ hmem ↦ ?_⟩⟩
  · rw [uniformlySpansReal_iff_uniformlySpans, ofRealUnitCM_image_muntzGenerators] at hspan ⊢
    exact h27.1 hspan
  · have horth_span : ∀ x ∈ Submodule.span ℝ (e '' {i : ι | i ≠ i₀}), ⟪e i₀, x⟫_ℝ = 0 := by
      intro x hx
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨i, hi, rfl⟩
        exact he.inner_eq_zero (Ne.symm hi)
      · simp
      · intro u v _ _ hu hv
        rw [inner_add_right, hu, hv, add_zero]
      · intro c u _ hu
        rw [inner_smul_right, hu, mul_zero]
    have hclosed : IsClosed {x : H | ⟪e i₀, x⟫_ℝ = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    intro hmem
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hmem
    have h0 : ⟪e i₀, e i₀⟫_ℝ = 0 := closure_minimal horth_span hclosed hmem
    rw [real_inner_self_eq_norm_sq, he.norm_eq_one i₀] at h0
    norm_num at h0
  · rw [uniformlySpansReal_iff_uniformlySpans, ofRealUnitCM_image_muntzGenerators] at hnot
    intro hmem
    have hmem_c := ofRealUnitCM_mem_closure_complex hmem
    have himg : ofRealUnitCM '' Set.range (fun n : ℕ ↦ realPowerContinuousMapReal (lam n) (hpos n).le) =
        Set.range (fun n : ℕ ↦ realPowerContinuousMap (lam n) (hpos n).le) := by
      ext g; simp only [Set.mem_image, Set.mem_range]
      exact ⟨fun ⟨_, ⟨n, rfl⟩, hg⟩ ↦ ⟨n, by rw [← hg]; ext t; rfl⟩,
        fun ⟨n, hg⟩ ↦ ⟨realPowerContinuousMapReal (lam n) (hpos n).le, ⟨n, rfl⟩,
          by rw [← hg]; ext t; rfl⟩⟩
    rw [himg] at hmem_c
    have h1 : ofRealUnitCM 1 = 1 := by ext t; simp [ofRealUnitCM]
    rw [h1] at hmem_c
    exact (h27.2 hnot).1 hmem_c
  · rw [uniformlySpansReal_iff_uniformlySpans, ofRealUnitCM_image_muntzGenerators] at hnot
    have hmem_c := ofRealUnitCM_mem_closure_complex hmem
    rw [ofRealUnitCM_image_muntzGenerators] at hmem_c
    have hpow : ofRealUnitCM (realPowerContinuousMapReal (lam n₀) (hpos n₀).le) =
        realPowerContinuousMap (lam n₀) (hpos n₀).le := by ext t; rfl
    rw [hpow] at hmem_c
    exact (h27.2 hnot).2 n₀ hmem_c


/-- **15.25 (Real-valued polynomial density on `[0, 1]`, RCA pp. 312–313):**
Monomials `{t ^ n | n : ℕ}` uniformly span real `C([0, 1], ℝ)`. -/
theorem theorem15_25_real :
    UniformlySpansReal
      (Set.range (fun n : ℕ ↦ (⟨fun t : UnitInterval01 ↦ t.1 ^ n, by fun_prop⟩ :
        C(UnitInterval01, ℝ)))) :=
  theorem15_25_real_aux theorem15_25

/-- **15.26 (Real-valued Müntz–Szász Theorem on `C([0, 1], ℝ)`, RCA pp. 313–315):**
For `0 < λ 0 < λ 1 < …`, the uniform closure of the real span of `{1, t ^ (λ 0), …}` in
`C([0, 1], ℝ)` equals `C([0, 1], ℝ)` when `∑ 1 / λ n = ∞`, and omits `t ^ μ` (`μ > 0`,
`∀ n, μ ≠ λ n`) when `∑ 1 / λ n < ∞`. -/
theorem theorem15_26_real {lam : ℕ → ℝ}
    (hpos : ∀ n, 0 < lam n) (hmono : StrictMono lam) :
    (¬ Summable (fun n ↦ 1 / lam n) → muntzSpaceReal lam hpos = ⊤) ∧
      (Summable (fun n ↦ 1 / lam n) →
        ∀ (μ : ℝ) (hμ : 0 < μ), (∀ n, μ ≠ lam n) →
          realPowerContinuousMapReal μ hμ.le ∉ muntzSpaceReal lam hpos) :=
  theorem15_26_real_aux hpos (theorem15_26 hpos hmono)

/-- **15.27 (Real-valued minimal-spanning remark on `C([0, 1], ℝ)`, RCA p. 315):** -/
theorem theorem15_27_real {lam : ℕ → ℝ}
    (hpos : ∀ n, 0 < lam n) (hmono : StrictMono lam) :
    (UniformlySpansReal (muntzGeneratorsReal lam hpos) →
      UniformlySpansReal (muntzGeneratorsReal (fun k ↦ lam (2 * k)) (fun k ↦ hpos (2 * k)))) ∧
    (∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        {ι : Type*} {e : ι → H},
      Orthonormal ℝ e → ∀ i₀ : ι,
        e i₀ ∉ (Submodule.span ℝ (e '' {i : ι | i ≠ i₀})).topologicalClosure) ∧
    (¬ UniformlySpansReal (muntzGeneratorsReal lam hpos) →
      ((1 : C(UnitInterval01, ℝ)) ∉
          (Submodule.span ℝ
            (Set.range (fun n : ℕ ↦ realPowerContinuousMapReal (lam n) (hpos n).le))).topologicalClosure ∧
        ∀ n₀ : ℕ,
          realPowerContinuousMapReal (lam n₀) (hpos n₀).le ∉
            muntzSpaceReal (fun k ↦ lam (if k < n₀ then k else k + 1))
              (fun k ↦ hpos (if k < n₀ then k else k + 1)))) :=
  theorem15_27_real_aux hpos
    ⟨fun hspan ↦ (theorem15_27_no_minimal_spanning_power_family hpos hmono hspan).2.2.2,
      fun hnot ↦ ⟨(theorem15_27_delete_one hpos).1,
        fun n₀ ↦ (theorem15_27_delete_power hpos hmono hnot n₀).1⟩⟩

#print axioms realPowerContinuousMapReal
#print axioms UniformlySpansReal
#print axioms muntzGeneratorsReal
#print axioms muntzSpaceReal
#print axioms theorem15_25_real
#print axioms theorem15_26_real
#print axioms theorem15_27_real

end Chapter15PartC

end RudinRCA.Chapter15
