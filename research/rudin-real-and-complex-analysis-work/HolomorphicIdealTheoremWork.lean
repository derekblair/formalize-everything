import HolomorphicIdealAssemblyWork
import InterpolationWork

/-!
Final 15.15 wrapper draft. This file intentionally waits for the actual
`interpolate_analytic_germs` construction in InterpolationWork and for the
checked 15.11 plane corollary in the chapter base. Those declarations are not
yet available as checked dependencies. This is not a completed node or a
conditional replacement for the printed theorem.
-/

noncomputable section

namespace RudinRCA.Chapter15

/-- Theorem 15.15: every finitely generated ideal of holomorphic functions on
an arbitrary open plane set is principal. Empty generating families,
disconnected domains, and identically zero generators are included. -/
theorem finitely_generated_holomorphic_ideals_principal {ι : Type*} [Fintype ι]
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (g : ι → ℂ → ℂ)
    (hg : ∀ i, DifferentiableOn ℂ (g i) Ω) :
    GeneratedHolomorphicIdealIsPrincipal Ω g := by
  apply generated_holomorphic_ideal_is_principal_of_pair hΩ _ g hg
  intro f g hf hg
  exact holomorphic_pair_principal_using_zero_and_jet_constructions
    (fun {Ω A} hΩ hA hno m hm ↦ prescribed_zeros_on_plane hΩ hA hno m hm)
    (fun {Ω A} hΩ hA hno m G hG ↦ interpolate_analytic_germs hΩ hA hno m G hG)
    hΩ hf hg

/-- The coefficient formulation printed in 15.15: the common generator is a
linear combination of the original generators and divides every one. -/
theorem holomorphic_finite_generator_coefficients {ι : Type*} [Fintype ι]
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (g : ι → ℂ → ℂ)
    (hg : ∀ i, DifferentiableOn ℂ (g i) Ω) :
    ∃ q : ℂ → ℂ, ∃ a b : ι → ℂ → ℂ,
      AnalyticOnNhd ℂ q Ω ∧ (∀ i, AnalyticOnNhd ℂ (a i) Ω) ∧
      (∀ i, AnalyticOnNhd ℂ (b i) Ω) ∧
      (∀ z ∈ Ω, q z = ∑ i, a i z * g i z) ∧
      (∀ i z, z ∈ Ω → g i z = b i z * q z) := by
  apply holomorphic_fintype_generators_principal_of_pair _ g
    (fun i ↦ (hg i).analyticOnNhd hΩ)
  intro f g hf hg
  exact holomorphic_pair_principal_using_zero_and_jet_constructions
    (fun {Ω A} hΩ hA hno m hm ↦ prescribed_zeros_on_plane hΩ hA hno m hm)
    (fun {Ω A} hΩ hA hno m G hG ↦ interpolate_analytic_germs hΩ hA hno m G hG)
    hΩ hf hg

#print axioms finitely_generated_holomorphic_ideals_principal
#print axioms holomorphic_finite_generator_coefficients

end RudinRCA.Chapter15
