import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.ENat.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Filter Finset
open scoped Topology

namespace RudinRCA.Chapter15

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

end RudinRCA.Chapter15
