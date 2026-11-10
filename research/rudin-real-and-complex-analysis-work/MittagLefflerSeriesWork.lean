import MittagLefflerKernelWork
import BoundaryProductGeometryWork
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
Direct Mittag-Leffler construction on a normalized plane domain. The omitted
closed set is nonempty, and the poles have chosen boundary points whose distance
tends to zero. These geometric hypotheses are supplied by domain normalization;
no Mittag-Leffler or approximation existence theorem is assumed here.

Draft: all declarations in this file still await the serialized Lean check.
-/

noncomputable section
open Filter Finset Set Metric
open scoped Topology

namespace RudinRCA.Chapter15

/-- Finite principal-part polynomials preserve meromorphicity. -/
theorem meromorphicAt_polynomial_eval {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) (P : Polynomial ℂ) :
    MeromorphicAt (fun w ↦ P.eval (f w)) z := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Polynomial.eval_add] using hP.add hQ
  | monomial n c =>
    simpa only [Polynomial.eval_monomial] using (MeromorphicAt.const c z).mul (hf.pow n)

/-- A uniformly convergent complex series remains uniformly convergent after
removing an arbitrary finite prefix. -/
theorem uniformOn_complex_series_tail {S : Type*} {K : Set S}
    (u : ℕ → S → ℂ) (A : S → ℂ)
    (hconv : TendstoUniformlyOn (fun n s ↦ ∑ i ∈ range n, u i s) A atTop K)
    (N : ℕ) :
    TendstoUniformlyOn (fun n s ↦ ∑ i ∈ range n, u (i + N) s)
      (fun s ↦ A s - ∑ i ∈ range N, u i s) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.2
  intro ε hε
  have hshift := (tendsto_add_atTop_nat N).eventually
    (Metric.tendstoUniformlyOn_iff.1 hconv ε hε)
  filter_upwards [hshift] with n hn s hs
  have hsum : (∑ i ∈ range (n + N), u i s) =
      (∑ i ∈ range N, u i s) + ∑ i ∈ range n, u (i + N) s := by
    simpa [Nat.add_comm] using sum_range_add (fun i ↦ u i s) N n
  have hdist : dist (A s - ∑ i ∈ range N, u i s)
      (∑ i ∈ range n, u (i + N) s) =
      dist (A s) (∑ i ∈ range (n + N), u i s) := by
    rw [dist_eq_norm, dist_eq_norm, hsum]
    congr 1
    ring
  rw [hdist]
  exact hn s hs

theorem locallyUniform_complex_series_tail {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (u : ℕ → ℂ → ℂ) (A : ℂ → ℂ)
    (hconv : TendstoLocallyUniformlyOn (fun n s ↦ ∑ i ∈ range n, u i s) A atTop Ω)
    (N : ℕ) :
    TendstoLocallyUniformlyOn (fun n s ↦ ∑ i ∈ range n, u (i + N) s)
      (fun s ↦ A s - ∑ i ∈ range N, u i s) atTop Ω := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).2
  intro K hKΩ hK
  exact uniformOn_complex_series_tail u A
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).1 hconv K hKΩ hK) N

/-- Uniform convergence and analyticity of all sufficiently late summands on a
neighborhood make the remainder after a finite prefix analytic there. -/
theorem analyticOnNhd_series_remainder {Ω V : Set ℂ}
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    {u : ℕ → ℂ → ℂ} {A : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn (fun n s ↦ ∑ i ∈ range n, u i s) A atTop Ω)
    (N : ℕ) (hu : ∀ n, AnalyticOnNhd ℂ (u (n + N)) V) :
    AnalyticOnNhd ℂ (fun s ↦ A s - ∑ i ∈ range N, u i s) V := by
  have hlim := (locallyUniform_complex_series_tail hΩ u A hconv N).mono hVΩ
  apply (hlim.differentiableOn _ hV).analyticOnNhd hV
  exact Eventually.of_forall fun M ↦ DifferentiableOn.fun_sum
    fun n _ ↦ (hu n).differentiableOn

/-- Every compact part of the domain eventually lies in the exterior region
on which the explicit principal-part approximation is small. -/
theorem boundary_exteriors_contain_compacts (a b : ℕ → ℂ) {C K : Set ℂ}
    (hC : IsClosed C) (hCne : C.Nonempty) (hb : ∀ n, b n ∈ C)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0))
    (hK : IsCompact K) (hKC : K ⊆ Cᶜ) :
    ∀ᶠ n in atTop, ∀ z ∈ K, 2 * ‖a n - b n‖ ≤ ‖z - b n‖ := by
  obtain ⟨δ, hδ, hδK⟩ := compact_infDist_lower_bound hC hCne hK hKC
  filter_upwards [(tendsto_order.mp hsmall).2 (δ / 2) (half_pos hδ)] with n hn z hz
  have hden : δ ≤ ‖z - b n‖ :=
    (hδK z hz).trans (by simpa only [dist_eq_norm] using infDist_le_dist_of_mem (hb n))
  linarith

def correctedPrincipalPart (P : Polynomial ℂ) (N : ℕ) (a b z : ℂ) : ℂ :=
  P.eval (1 / (z - a)) - P.eval (reciprocalExpansion N a b z)

theorem correctedPrincipalPart_analyticAt (P : Polynomial ℂ) (N : ℕ)
    {a b z : ℂ} (hza : z ≠ a) (hzb : z ≠ b) :
    AnalyticAt ℂ (correctedPrincipalPart P N a b) z := by
  have htrue : AnalyticAt ℂ (fun w : ℂ ↦ 1 / (w - a)) z :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hza)
  exact (htrue.aeval_polynomial P).sub
    ((analyticAt_reciprocalExpansion N a b hzb).aeval_polynomial P)

theorem correctedPrincipalPart_meromorphicAt (P : Polynomial ℂ) (N : ℕ)
    (a b z : ℂ) : MeromorphicAt (correctedPrincipalPart P N a b) z := by
  have htrue : MeromorphicAt (fun w : ℂ ↦ 1 / (w - a)) z :=
    (MeromorphicAt.const 1 z).div ((MeromorphicAt.id z).sub (.const a z))
  have happ : MeromorphicAt (reciprocalExpansion N a b) z := by
    apply MeromorphicAt.fun_sum
    intro k _
    exact (((MeromorphicAt.const (a - b) z).div
      ((MeromorphicAt.id z).sub (.const b z))).pow k).div
        ((MeromorphicAt.id z).sub (.const b z))
  exact (meromorphicAt_polynomial_eval htrue P).sub
    (meromorphicAt_polynomial_eval happ P)

/-- The truncation orders are chosen from the proved geometric approximation,
and the resulting series converges locally uniformly on the whole domain. -/
theorem exists_locally_uniform_principal_part_series
    (P : ℕ → Polynomial ℂ) (a b : ℕ → ℂ) {C : Set ℂ}
    (hC : IsClosed C) (hCne : C.Nonempty) (ha : ∀ n, a n ∉ C)
    (hb : ∀ n, b n ∈ C)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0)) :
    ∃ N : ℕ → ℕ,
      (∀ n z, 2 * ‖a n - b n‖ ≤ ‖z - b n‖ →
        ‖correctedPrincipalPart (P n) (N n) (a n) (b n) z‖ < (1 / 2 : ℝ) ^ n) ∧
      TendstoLocallyUniformlyOn
        (fun M z ↦ ∑ n ∈ range M, correctedPrincipalPart (P n) (N n) (a n) (b n) z)
        (fun z ↦ ∑' n, correctedPrincipalPart (P n) (N n) (a n) (b n) z)
        atTop Cᶜ := by
  have hab : ∀ n, a n ≠ b n := fun n h ↦ ha n (h.symm ▸ hb n)
  have happrox : ∀ n, ∃ k : ℕ, ∀ z : ℂ, 2 * ‖a n - b n‖ ≤ ‖z - b n‖ →
      ‖correctedPrincipalPart (P n) k (a n) (b n) z‖ < (1 / 2 : ℝ) ^ n := by
    intro n
    exact exists_polynomial_reciprocal_approximation (P n) (hab n) (by positivity)
  choose N hN using happrox
  refine ⟨N, hN, (tendstoLocallyUniformlyOn_iff_forall_isCompact hC.isOpen_compl).2 ?_⟩
  intro K hKC hK
  apply tendstoUniformlyOn_tsum_nat_eventually
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  filter_upwards [boundary_exteriors_contain_compacts a b hC hCne hb hsmall hK hKC]
    with n hn z hz
  exact (hN n z (hn z hz)).le

/-- Near any domain point all sufficiently late summands are analytic. The
finite prefix is allowed to contain actual poles. -/
theorem correctedPrincipalPart_eventually_analytic_near
    (P : ℕ → Polynomial ℂ) (N : ℕ → ℕ) (a b : ℕ → ℂ) {C : Set ℂ}
    (hC : IsClosed C) (hCne : C.Nonempty) (ha : ∀ n, a n ∉ C)
    (hb : ∀ n, b n ∈ C)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0))
    {z : ℂ} (hz : z ∉ C) :
    ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ Cᶜ ∧
      ∀ᶠ n in atTop, AnalyticOnNhd ℂ
        (correctedPrincipalPart (P n) (N n) (a n) (b n)) V := by
  obtain ⟨K, ⟨hKz, hK⟩, hKC⟩ :=
    (compact_basis_nhds z).mem_iff.mp (hC.isOpen_compl.mem_nhds hz)
  refine ⟨interior K, isOpen_interior, mem_interior_iff_mem_nhds.mpr hKz,
    interior_subset.trans hKC, ?_⟩
  filter_upwards [boundary_exteriors_contain_compacts a b hC hCne hb hsmall hK hKC]
    with n hn w hw
  have hab : a n ≠ b n := fun h ↦ ha n (h.symm ▸ hb n)
  obtain ⟨hwa, hwb, _⟩ := reciprocalExpansion_exterior_geometry hab (hn w (interior_subset hw))
  exact correctedPrincipalPart_analyticAt (P n) (N n) hwa hwb

/-- A locally uniform series with an analytic tail and meromorphic summands
has a meromorphic sum. This retains the finite principal parts. -/
theorem meromorphicAt_of_locally_uniform_series
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℕ → ℂ → ℂ} {A : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn (fun n s ↦ ∑ i ∈ range n, u i s) A atTop Ω)
    {z : ℂ} (hu : ∀ n, MeromorphicAt (u n) z)
    (htail : ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ Ω ∧
      ∀ᶠ n in atTop, AnalyticOnNhd ℂ (u n) V) : MeromorphicAt A z := by
  obtain ⟨V, hV, hzV, hVΩ, htail⟩ := htail
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  have hrem := analyticOnNhd_series_remainder hΩ hV hVΩ hconv N
    (fun n ↦ hN (n + N) (Nat.le_add_left N n)) z hzV
  have hprefix : MeromorphicAt (fun w ↦ ∑ n ∈ range N, u n w) z :=
    MeromorphicAt.fun_sum fun n _ ↦ hu n
  convert hrem.meromorphicAt.add hprefix using 1
  ext w
  exact (sub_add_cancel _ _).symm

/-- If all other summands are analytic at z, removing the selected summand
removes the whole principal part of the series there. -/
theorem analyticAt_of_locally_uniform_series
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℕ → ℂ → ℂ} {A : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn (fun n s ↦ ∑ i ∈ range n, u i s) A atTop Ω)
    {z : ℂ} (hu : ∀ n, AnalyticAt ℂ (u n) z)
    (htail : ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ Ω ∧
      ∀ᶠ n in atTop, AnalyticOnNhd ℂ (u n) V) : AnalyticAt ℂ A z := by
  obtain ⟨V, hV, hzV, hVΩ, htail⟩ := htail
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  have hrem := analyticOnNhd_series_remainder hΩ hV hVΩ hconv N
    (fun n ↦ hN (n + N) (Nat.le_add_left N n)) z hzV
  have hprefix : AnalyticAt ℂ (fun w ↦ ∑ n ∈ range N, u n w) z :=
    Finset.analyticAt_fun_sum _ fun n _ ↦ hu n
  convert hrem.add hprefix using 1
  ext w
  exact (sub_add_cancel _ _).symm

/-- Removing one term from the sum preserves every other analytic germ. -/
theorem analyticAt_series_sub_term
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℕ → ℂ → ℂ} {A : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn (fun n s ↦ ∑ i ∈ range n, u i s) A atTop Ω)
    {z : ℂ} (j : ℕ) (hu : ∀ n, n ≠ j → AnalyticAt ℂ (u n) z)
    (htail : ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ Ω ∧
      ∀ᶠ n in atTop, AnalyticOnNhd ℂ (u n) V) :
    AnalyticAt ℂ (fun w ↦ A w - u j w) z := by
  obtain ⟨V, hV, hzV, hVΩ, htail⟩ := htail
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  let M := max N (j + 1)
  have hjM : j ∈ range M := mem_range.2 (lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _))
  have hrem := analyticOnNhd_series_remainder hΩ hV hVΩ hconv M
    (fun n ↦ hN (n + M) ((le_max_left _ _).trans (Nat.le_add_left M n))) z hzV
  have hprefix : AnalyticAt ℂ (fun w ↦ ∑ n ∈ (range M).erase j, u n w) z :=
    Finset.analyticAt_fun_sum _ fun n hn ↦ hu n (mem_erase.mp hn).1
  convert hrem.add hprefix using 1
  ext w
  have hsum := sum_erase_add (range M) (fun n ↦ u n w) hjM
  dsimp only
  rw [← hsum]
  ring

/-- The normalized Mittag-Leffler conclusion, including each prescribed
principal part. Injectivity says each distinct pole is listed once; arbitrary
finite pole order is stored in its polynomial. -/
theorem exists_normalized_mittag_leffler
    (P : ℕ → Polynomial ℂ) (a b : ℕ → ℂ) {C : Set ℂ}
    (hC : IsClosed C) (hCne : C.Nonempty) (ha : ∀ n, a n ∉ C)
    (hb : ∀ n, b n ∈ C) (hainj : Function.Injective a)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0)) :
    ∃ F : ℂ → ℂ, MeromorphicOn F Cᶜ ∧
      ∀ j, AnalyticAt ℂ (fun z ↦ F z - (P j).eval (1 / (z - a j))) (a j) := by
  obtain ⟨N, _, hconv⟩ :=
    exists_locally_uniform_principal_part_series P a b hC hCne ha hb hsmall
  let u := fun n z ↦ correctedPrincipalPart (P n) (N n) (a n) (b n) z
  let F := fun z ↦ ∑' n, u n z
  have htail := fun z hz ↦
    correctedPrincipalPart_eventually_analytic_near P N a b hC hCne ha hb hsmall (z := z) hz
  refine ⟨F, ?_, ?_⟩
  · intro z hz
    exact meromorphicAt_of_locally_uniform_series hC.isOpen_compl hconv
      (fun n ↦ correctedPrincipalPart_meromorphicAt (P n) (N n) (a n) (b n) z)
      (htail z hz)
  · intro j
    have hother : ∀ n, n ≠ j → AnalyticAt ℂ (u n) (a j) := by
      intro n hnj
      exact correctedPrincipalPart_analyticAt (P n) (N n)
        (fun h ↦ hnj (hainj h.symm)) (fun h ↦ ha j (h.symm ▸ hb n))
    have hsub := analyticAt_series_sub_term hC.isOpen_compl hconv j hother (htail (a j) (ha j))
    have happ : AnalyticAt ℂ (fun z ↦ (P j).eval (reciprocalExpansion (N j) (a j) (b j) z))
        (a j) :=
      (analyticAt_reciprocalExpansion (N j) (a j) (b j)
        (fun h ↦ ha j (h.symm ▸ hb j))).aeval_polynomial (P j)
    convert hsub.sub happ using 1
    ext z
    dsimp [u, correctedPrincipalPart]
    ring

#print axioms meromorphicAt_polynomial_eval
#print axioms uniformOn_complex_series_tail
#print axioms locallyUniform_complex_series_tail
#print axioms analyticOnNhd_series_remainder
#print axioms boundary_exteriors_contain_compacts
#print axioms correctedPrincipalPart_analyticAt
#print axioms correctedPrincipalPart_meromorphicAt
#print axioms exists_locally_uniform_principal_part_series
#print axioms correctedPrincipalPart_eventually_analytic_near
#print axioms meromorphicAt_of_locally_uniform_series
#print axioms analyticAt_of_locally_uniform_series
#print axioms analyticAt_series_sub_term
#print axioms exists_normalized_mittag_leffler

end RudinRCA.Chapter15
