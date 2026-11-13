import RudinRCA.Chapter13
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/- Prerequisites: GridRepresentation.lean, RungeAssembly.lean,
   RungeUniformSequences.lean, OpenRungeAssembly.lean,
   MittagLefflerCore.lean, MittagLefflerSeries.lean, MittagLefflerAssembly.lean.
   These statements discharge the finite-contour input using its actual
   existence theorem. They are not validated until the complete dependency
   chain passes the aggregate check and axiom audit. -/
noncomputable section
open Set Filter
open scoped Topology OnePoint

namespace RudinRCA.Chapter13

/-- Rudin 13.6: compact rational approximation with prescribed spherical poles. -/
theorem runge_compact {K Ω : Set ℂ} (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (A : Set RiemannSphere)
    (hA : A ⊆ (((↑) : ℂ → RiemannSphere) '' K)ᶜ)
    (hcomponents : ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
      ∃ a ∈ A, a ∈ connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K)ᶜ p)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : RatFunc ℂ,
      (∀ z : ℂ, R.denom.eval z = 0 → (z : RiemannSphere) ∈ A) ∧
      ((∞ : RiemannSphere) ∉ A →
        RungeRemovableAtInfinity (fun z ↦ RatFunc.eval (RingHom.id ℂ) z R)) ∧
      ∀ z ∈ K, ‖f z - RatFunc.eval (RingHom.id ℂ) z R‖ < ε := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨C⟩ := finiteCauchyRepresentation_nonempty hK hΩ hKΩ
  exact C.exists_rational_approximation A hA hcomponents f hf hε

/-- Rudin 13.7: connected spherical complement gives a uniformly convergent
    sequence of polynomial approximations on the compact set. -/
theorem polynomial_approximation_compact {K Ω : Set ℂ}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hconn : IsConnected ((((↑) : ℂ → RiemannSphere) '' K)ᶜ))
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) :
    ∃ P : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n z ↦ (P n).eval z) f atTop K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨C⟩ := finiteCauchyRepresentation_nonempty hK hΩ hKΩ
  exact C.exists_polynomial_uniform_sequence hconn f hf

/-- Rudin 13.9: rational approximation uniformly on every compact subset of
    an arbitrary open set, preserving the chosen spherical pole set. -/
theorem runge_open {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (A : Set RiemannSphere)
    (hA : A ⊆ (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ)
    (hcomponents : ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ,
      ∃ a ∈ A, a ∈ connectedComponentIn (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ p)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) :
    ∃ R : ℕ → RatFunc ℂ,
      (∀ n z, (R n).denom.eval z = 0 → (z : RiemannSphere) ∈ A) ∧
      ((∞ : RiemannSphere) ∉ A → ∀ n,
        RungeRemovableAtInfinity (fun z ↦ RatFunc.eval (RingHom.id ℂ) z (R n))) ∧
      TendstoLocallyUniformlyOn (fun n z ↦ RatFunc.eval (RingHom.id ℂ) z (R n)) f atTop Ω := by
  let C : ∀ n : ℕ, FiniteCauchyRepresentation (exhaustionLevel Ω n) Ω :=
    fun n ↦ Classical.choice (finiteCauchyRepresentation_nonempty
      (exhaustionLevel_isCompact Ω n) hΩ (exhaustionLevel_subset Ω n))
  exact exists_rational_locally_uniform_sequence_of_finite_cauchy hΩ C A hA hcomponents f hf

/-- The polynomial form of Rudin 13.9, without a connectedness assumption on Ω. -/
theorem polynomial_approximation_open {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hconn : IsConnected ((((↑) : ℂ → RiemannSphere) '' Ω)ᶜ))
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) :
    ∃ P : ℕ → Polynomial ℂ,
      TendstoLocallyUniformlyOn (fun n z ↦ (P n).eval z) f atTop Ω := by
  let C : ∀ n : ℕ, FiniteCauchyRepresentation (exhaustionLevel Ω n) Ω :=
    fun n ↦ Classical.choice (finiteCauchyRepresentation_nonempty
      (exhaustionLevel_isCompact Ω n) hΩ (exhaustionLevel_subset Ω n))
  exact exists_polynomial_locally_uniform_sequence_of_finite_cauchy hΩ C hconn f hf

/-- Rudin 13.10: realization of arbitrary locally finite prescribed principal
    parts by a meromorphic function, with no other poles in Ω. -/
theorem mittag_leffler {Ω A : Set ℂ} (hΩ : IsOpen Ω) (hAΩ : A ⊆ Ω)
    (hacc : ∀ z ∈ Ω, ¬AccPt z (𝓟 A))
    (m : ℂ → ℕ) (hm : ∀ α ∈ A, 0 < m α) (c : ℂ → ℕ → ℂ) :
    ∃ f : ℂ → ℂ, MeromorphicOn f Ω ∧
      (∀ α ∈ A, AnalyticAt ℂ (fun z ↦ f z - finitePrincipalPart (m α) (c α) α z) α) ∧
      ∀ z ∈ Ω \ A, AnalyticAt ℂ f z :=
  mittag_leffler_of_finite_cauchy
    (fun K U hK hU hKU ↦ finiteCauchyRepresentation_nonempty hK hU hKU)
    hΩ hAΩ hacc m hm c

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.runge_compact
#print axioms RudinRCA.Chapter13.polynomial_approximation_compact
#print axioms RudinRCA.Chapter13.runge_open
#print axioms RudinRCA.Chapter13.polynomial_approximation_open
#print axioms RudinRCA.Chapter13.mittag_leffler
