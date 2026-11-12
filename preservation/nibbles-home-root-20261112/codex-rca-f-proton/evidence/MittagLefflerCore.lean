import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Abel

/- Core facts for Rudin 13.10. These prove exact finite principal parts and the
   analytic tail argument. The Runge corrections and exhaustion shell
   construction are separate prerequisites for the final existence theorem. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace RudinRCA.Chapter13

/-- A set without accumulation points in Ω meets each compact subset of Ω
    in only finitely many points. -/
theorem finite_inter_compact_of_no_accumulation {A Ω K : Set ℂ}
    (hA : ∀ z ∈ Ω, ¬AccPt z (𝓟 A)) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    (A ∩ K).Finite := by
  by_contra hfinite
  obtain ⟨z, hz, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hfinite hK inter_subset_right
  exact hA z (hKΩ hz) (hacc.mono (principal_mono.mpr inter_subset_left))

/-- The prescribed finite negative-power expression, with coefficients
    indexed by positive integers as in the printed theorem. -/
def finitePrincipalPart (m : ℕ) (c : ℕ → ℂ) (α z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range m, c (j + 1) * (z - α)⁻¹ ^ (j + 1)

theorem finitePrincipalPart_meromorphicAt (m : ℕ) (c : ℕ → ℂ) (α z : ℂ) :
    MeromorphicAt (finitePrincipalPart m c α) z := by
  apply MeromorphicAt.fun_sum
  intro j hj
  exact analyticAt_const.meromorphicAt.mul
    (((analyticAt_id.sub analyticAt_const).meromorphicAt.inv).pow (j + 1))

theorem finitePrincipalPart_analyticAt (m : ℕ) (c : ℕ → ℂ) (α : ℂ)
    {z : ℂ} (hz : z ≠ α) : AnalyticAt ℂ (finitePrincipalPart m c α) z := by
  apply Finset.analyticAt_fun_sum
  intro j hj
  exact analyticAt_const.mul
    (((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hz)).pow (j + 1))

/-- A normally convergent analytic tail differs from the full series only by
    its finite prefix, including at points where that prefix is singular. -/
theorem analyticAt_tsum_sub_prefix {g : ℕ → ℂ → ℂ} (N : ℕ)
    {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    {u : ℕ → ℝ} (hu : Summable u)
    (hdiff : ∀ n : ℕ, DifferentiableOn ℂ (g (n + N)) U)
    (hbound : ∀ n : ℕ, ∀ w ∈ U, ‖g (n + N) w‖ ≤ u n) :
    AnalyticAt ℂ (fun w ↦ (∑' n, g n w) - ∑ n ∈ Finset.range N, g n w) z := by
  have htail : DifferentiableOn ℂ (fun w ↦ ∑' n, g (n + N) w) U :=
    differentiableOn_tsum_of_summable_norm hu hdiff hU hbound
  apply (htail.analyticAt (hU.mem_nhds hz)).congr
  filter_upwards [hU.mem_nhds hz] with w hw
  have hs : Summable (fun n ↦ g n w) :=
    (summable_nat_add_iff N).mp (hu.of_norm_bounded (fun n ↦ hbound n w hw))
  have heq := hs.sum_add_tsum_nat_add N
  exact eq_sub_of_add_eq' heq

/-- An exact analytic remainder of the finite prefix gives the same exact
    principal part for the full normally convergent series. -/
theorem analyticAt_tsum_sub_of_prefix {g : ℕ → ℂ → ℂ} (N : ℕ)
    {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    {u : ℕ → ℝ} (hu : Summable u)
    (hdiff : ∀ n : ℕ, DifferentiableOn ℂ (g (n + N)) U)
    (hbound : ∀ n : ℕ, ∀ w ∈ U, ‖g (n + N) w‖ ≤ u n)
    (P : ℂ → ℂ)
    (hprefix : AnalyticAt ℂ (fun w ↦ (∑ n ∈ Finset.range N, g n w) - P w) z) :
    AnalyticAt ℂ (fun w ↦ (∑' n, g n w) - P w) z := by
  convert (analyticAt_tsum_sub_prefix N hU hz hu hdiff hbound).add hprefix using 1
  ext w
  abel

/-- A prescribed meromorphic principal part and an analytic difference imply
    meromorphicity of the realized function at that point. -/
theorem meromorphicAt_of_analytic_sub_principalPart {f : ℂ → ℂ}
    (m : ℕ) (c : ℕ → ℂ) (α : ℂ)
    (h : AnalyticAt ℂ (fun z ↦ f z - finitePrincipalPart m c α z) α) :
    MeromorphicAt f α := by
  convert h.meromorphicAt.add (finitePrincipalPart_meromorphicAt m c α α) using 1
  ext z
  simp

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.finite_inter_compact_of_no_accumulation
#print axioms RudinRCA.Chapter13.finitePrincipalPart_meromorphicAt
#print axioms RudinRCA.Chapter13.finitePrincipalPart_analyticAt
#print axioms RudinRCA.Chapter13.analyticAt_tsum_sub_prefix
#print axioms RudinRCA.Chapter13.analyticAt_tsum_sub_of_prefix
#print axioms RudinRCA.Chapter13.meromorphicAt_of_analytic_sub_principalPart
