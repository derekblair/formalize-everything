import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.InfiniteSum.Group

open Filter Set
open scoped Topology Classical

noncomputable section

namespace RudinRCA.Chapter15

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

end RudinRCA.Chapter15
