import RudinRCA.Chapter13
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Tactic.Push

noncomputable section
open Set
open scoped OnePoint
namespace RudinRCA.Chapter13

/-- A disconnected closed spherical set containing infinity has a nonempty compact piece in
its finite chart, isolated from the rest by an open planar neighborhood. -/
theorem compact_piece_of_spherical_complement_disconnected {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hdisc : ¬IsConnected (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ) :
    ∃ K W : Set ℂ, K.Nonempty ∧ IsCompact K ∧ IsOpen W ∧ K ⊆ W ∧
      K ⊆ Ωᶜ ∧ W \ K ⊆ Ω := by
  let C : Set RiemannSphere := (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ
  have hC : IsClosed C := (OnePoint.isOpen_image_coe.mpr hΩ).isClosed_compl
  have h∞C : (∞ : RiemannSphere) ∈ C := by simp [C]
  have hn : ¬IsPreconnected C := fun h => hdisc ⟨⟨∞, h∞C⟩, h⟩
  simp only [IsPreconnected] at hn
  push_neg at hn
  obtain ⟨U, V, hU, hV, hcover, hUne, hVne, hdis⟩ := hn
  have isolate (U V : Set RiemannSphere) (hU : IsOpen U) (hV : IsOpen V)
      (hcover : C ⊆ U ∪ V) (hUne : (C ∩ U).Nonempty)
      (hdis : ¬(C ∩ (U ∩ V)).Nonempty) (h∞U : (∞ : RiemannSphere) ∉ U) :
      ∃ K W : Set ℂ, K.Nonempty ∧ IsCompact K ∧ IsOpen W ∧ K ⊆ W ∧
        K ⊆ Ωᶜ ∧ W \ K ⊆ Ω := by
    let K : Set ℂ := ((↑) : ℂ → RiemannSphere) ⁻¹' (C ∩ U)
    let W : Set ℂ := ((↑) : ℂ → RiemannSphere) ⁻¹' U
    have heq : C ∩ U = C \ V := by
      ext p
      constructor
      · rintro ⟨hpC, hpU⟩
        exact ⟨hpC, fun hpV => hdis ⟨p, hpC, hpU, hpV⟩⟩
      · rintro ⟨hpC, hpV⟩
        exact ⟨hpC, (hcover hpC).resolve_right hpV⟩
    have hclosed : IsClosed (C ∩ U) := by rw [heq]; exact hC.inter hV.isClosed_compl
    have himage : ((↑) : ℂ → RiemannSphere) '' K = C ∩ U := by
      apply image_preimage_eq_iff.mpr
      intro p hp
      induction p using OnePoint.rec with
      | infty => exact False.elim (h∞U hp.2)
      | coe z => exact ⟨z, rfl⟩
    have hK : IsCompact K := (OnePoint.isClosed_image_coe.mp (himage.symm ▸ hclosed)).2
    refine ⟨K, W, ?_, hK, hU.preimage OnePoint.continuous_coe, ?_, ?_, ?_⟩
    · obtain ⟨p, hp⟩ := hUne
      rw [← himage] at hp
      obtain ⟨z, hz, _⟩ := hp
      exact ⟨z, hz⟩
    · exact fun _ hz => hz.2
    · intro z hz hzΩ
      exact hz.1 ⟨z, hzΩ, rfl⟩
    · intro z hz
      by_contra hzΩ
      apply hz.2
      exact ⟨by simpa [C] using hzΩ, hz.1⟩
  by_cases h∞U : (∞ : RiemannSphere) ∈ U
  · apply isolate V U hV hU (fun p hp => (hcover hp).symm) hVne
    · rintro ⟨p, hpC, hpV, hpU⟩
      exact hdis ⟨p, hpC, hpU, hpV⟩
    · intro h∞V
      exact hdis ⟨∞, h∞C, h∞U, h∞V⟩
  · exact isolate U V hU hV hcover hUne hdis h∞U

#print axioms compact_piece_of_spherical_complement_disconnected
end RudinRCA.Chapter13
