import RudinRCA.Chapter15
import Mathlib.Analysis.Meromorphic.NormalForm

noncomputable section
open Filter Set
open scoped Topology

namespace RudinRCA.Chapter15

/-- The removable-singularity step used in 15.12: a meromorphic function with
no negative orders has a holomorphic representative of its meromorphic class. -/
theorem holomorphic_regularization_of_nonnegative_orders {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : MeromorphicOn f Ω) (hord : ∀ z ∈ Ω, 0 ≤ meromorphicOrderAt f z) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g Ω ∧ f =ᶠ[codiscreteWithin Ω] g := by
  refine ⟨toMeromorphicNFOn f Ω, ?_, toMeromorphicNFOn_eqOn_codiscrete hf⟩
  intro z hz
  apply ((meromorphicNFOn_toMeromorphicNFOn f Ω) hz)
    .meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hf hz]
  exact hord z hz

/-- Finite analytic orders exclude an identically zero component, so zeros may
be removed on a codiscrete set even when the domain is disconnected. -/
theorem holomorphic_nonzero_codiscrete {Ω : Set ℂ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g Ω) (hfinite : ∀ z ∈ Ω, analyticOrderAt g z ≠ ⊤) :
    ∀ᶠ z in codiscreteWithin Ω, g z ≠ 0 := by
  have hΩ : Ω ∈ codiscreteWithin Ω := by simp
  filter_upwards [hg.codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top, hΩ] with z hz hzΩ
  exact (hg z hzΩ).analyticOrderAt_eq_zero.mp (hz.resolve_right (hfinite z hzΩ))

/-- The denominator assembly for 15.12. The remaining existence obligation is
to construct h with exactly the pole multiplicities, using 15.11. This helper
must not itself be counted as the numbered quotient theorem. -/
theorem meromorphic_quotient_of_canceling_denominator {Ω : Set ℂ} {f h : ℂ → ℂ}
    (hf : MeromorphicOn f Ω) (hh : AnalyticOnNhd ℂ h Ω)
    (hfinite : ∀ z ∈ Ω, analyticOrderAt h z ≠ ⊤)
    (hcancel : ∀ z ∈ Ω, 0 ≤ meromorphicOrderAt f z + meromorphicOrderAt h z) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g Ω ∧
      f =ᶠ[codiscreteWithin Ω] (fun z ↦ g z / h z) := by
  have hprod : MeromorphicOn (f * h) Ω := hf.mul hh.meromorphicOn
  have hprodorder : ∀ z ∈ Ω, 0 ≤ meromorphicOrderAt (f * h) z := by
    intro z hz
    rw [meromorphicOrderAt_mul (hf z hz) (hh z hz).meromorphicAt]
    exact hcancel z hz
  obtain ⟨g, hg, heq⟩ := holomorphic_regularization_of_nonnegative_orders hprod hprodorder
  refine ⟨g, hg, ?_⟩
  filter_upwards [heq, holomorphic_nonzero_codiscrete hh hfinite] with z hz hh0
  change f z * h z = g z at hz
  rw [← hz, mul_div_cancel_right₀ _ hh0]

/-- The converse accompanying 15.12. The standard meromorphic interpretation
ignores isolated arbitrary values at poles; componentwise nonvanishing gives
finite denominator orders and is retained explicitly as in the printed text. -/
theorem quotient_holomorphic_meromorphic {Ω : Set ℂ} {g h : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (hh : DifferentiableOn ℂ h Ω)
    (hnonzero : ∀ z ∈ Ω, ∃ w ∈ connectedComponentIn Ω z, h w ≠ 0) :
    MeromorphicOn (fun z ↦ g z / h z) Ω ∧ ∀ z ∈ Ω, analyticOrderAt h z ≠ ⊤ := by
  refine ⟨?_, fun z hz ↦ analyticOrderAt_ne_top_of_component_nonzero hΩ hh hnonzero hz⟩
  intro z hz
  exact ((hg.analyticOnNhd hΩ) z hz).meromorphicAt.div
    ((hh.analyticOnNhd hΩ) z hz).meromorphicAt

#print axioms holomorphic_regularization_of_nonnegative_orders
#print axioms holomorphic_nonzero_codiscrete
#print axioms meromorphic_quotient_of_canceling_denominator
#print axioms quotient_holomorphic_meromorphic

end RudinRCA.Chapter15
