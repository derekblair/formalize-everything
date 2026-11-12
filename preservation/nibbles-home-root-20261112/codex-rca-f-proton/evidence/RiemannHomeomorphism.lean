import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Topology.Homeomorph.Lemmas

/-! Rudin RCA 14.8 and the independent forward implication 13.11(j) → (a).
This follows RiemannMappingFull and RiemannMappingSquareRoots in the aggregate.
The copied extremal-map proofs carry their original Apache attribution there.
This wrapper is a new lane development; all statements remain pending checking.
-/

open Set Metric Function
open scoped Topology

namespace RudinRCA.Chapter13

/-- A holomorphic bijection from a region onto the disc induces a homeomorphism. -/
theorem homeomorphic_to_disc_of_holomorphic_bijection {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) {f : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f Ω) (hfbij : BijOn f Ω (ball 0 1)) :
    Nonempty (Ω ≃ₜ ball (0 : ℂ) 1) := by
  classical
  have hnonconst : ¬∃ w, ∀ z ∈ Ω, f z = w := by
    rintro ⟨w, hw⟩
    obtain ⟨x, hx, hfx⟩ := hfbij.surjOn (mem_ball_self zero_lt_one)
    obtain ⟨y, hy, hfy⟩ := hfbij.surjOn (show (1 / 2 : ℂ) ∈ ball 0 1 by norm_num)
    have heq : (0 : ℂ) = 1 / 2 :=
      hfx.symm.trans ((hw x hx).trans ((hw y hy).symm.trans hfy))
    norm_num at heq
  have hopen := ((hfd.analyticOnNhd hΩo).is_constant_or_isOpen hΩc.isPreconnected).resolve_left hnonconst
  have hfo : IsOpenMap (fun z : Ω => f z) := by
    intro s hs
    have hsopen : IsOpen ((↑) '' s : Set ℂ) := hΩo.isOpenMap_subtype_val s hs
    have himage := hopen ((↑) '' s) (by rintro _ ⟨z, hz, rfl⟩; exact z.2) hsopen
    simpa only [Set.image_image] using himage
  let e : Ω ≃ ball (0 : ℂ) 1 := hfbij.equiv f
  have hcont : Continuous e :=
    (continuousOn_iff_continuous_domRestrict.mp hfd.continuousOn).subtype_mk _
  have heopen : IsOpenMap e := hfo.subtype_mk _
  exact ⟨e.toHomeomorphOfContinuousOpen hcont heopen⟩

/-- Rudin 13.11(j) implies (a), including the whole-plane case. -/
theorem homeomorphic_to_disc_of_holomorphic_square_roots {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hroots : Complex.HasHolomorphicSquareRoots Ω) :
    Nonempty (Ω ≃ₜ ball (0 : ℂ) 1) := by
  by_cases hΩ : Ω = univ
  · subst Ω
    exact ⟨(Homeomorph.Set.univ ℂ).trans (Homeomorph.unitBall (E := ℂ))⟩
  · obtain ⟨z₀, hz₀⟩ := hΩc.nonempty
    obtain ⟨f, hfd, hfbij, _⟩ :=
      Complex.exists_bijOn_unitBall_map_eq_zero_of_square_roots hΩo hΩc hroots hΩ hz₀
    exact homeomorphic_to_disc_of_holomorphic_bijection hΩo hΩc hfd hfbij

#print axioms homeomorphic_to_disc_of_holomorphic_bijection
#print axioms homeomorphic_to_disc_of_holomorphic_square_roots
end RudinRCA.Chapter13

namespace RudinRCA.Chapter14

/-- Rudin 14.8: a proper simply connected plane region is conformally equivalent to the disc. -/
theorem riemann_mapping_theorem {Ω : Set ℂ} (hΩo : IsOpen Ω)
    (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ BijOn f Ω (ball 0 1) := by
  obtain ⟨z₀, hz₀⟩ := hΩc.nonempty
  obtain ⟨f, hfd, hfbij, _⟩ := Complex.exists_bijOn_unitBall_map_eq_zero hΩo hΩc hΩ hz₀
  exact ⟨f, hfd, hfbij⟩

#print axioms riemann_mapping_theorem
end RudinRCA.Chapter14
