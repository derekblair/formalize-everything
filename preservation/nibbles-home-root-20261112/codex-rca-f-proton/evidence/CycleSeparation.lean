import RudinRCA.Chapter13
import Mathlib.Analysis.Convex.Segment
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum

/-! Compile after GridRepresentation and SphericalSeparation. -/
noncomputable section
open Set Complex
open RudinRCA.Chapter13Scratch
open scoped BigOperators OnePoint
namespace RudinRCA.Chapter13

/-- Zero reciprocal integral around every finite balanced family of directed intervals.
The geometry is represented with indices, so repeated equal intervals retain multiplicity. -/
def ReciprocalBalancedCyclesVanish (Ω : Set ℂ) : Prop :=
  ∀ (E : Type) [Fintype E] (initial terminal : E → ℂ),
    (∀ v, Nat.card {e // initial e = v} = Nat.card {e // terminal e = v}) →
    (∀ e, segment ℝ (initial e) (terminal e) ⊆ Ω) →
    ∀ a ∉ Ω, (∑ e : E, complexSegmentIntegral (fun z => (z - a)⁻¹)
      (initial e) (terminal e)) = 0

/-- The nontrivial direction in the connected-complement index criterion: a separated compact
piece of the spherical complement forces a polygonal cycle of nonzero index. -/
theorem spherical_complement_connected_of_reciprocal_cycles {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hcycles : ReciprocalBalancedCyclesVanish Ω) :
    IsConnected (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ := by
  classical
  by_contra hdisc
  obtain ⟨K, W, hKne, hK, hW, hKW, hKΩ, hWK⟩ :=
    compact_piece_of_spherical_complement_disconnected hΩ hdisc
  obtain ⟨δ, hδ, S, hKint, hcover, hinside⟩ := finite_grid_neighborhood hK hW hKW
  obtain ⟨a, ha⟩ := hKne
  let E := {e : GridEdge S // ¬gridEdgeInternal e}
  have hvanish := hcycles E (fun e => complexGridInitial δ e.1)
    (fun e => complexGridTerminal δ e.1) (complexGridBoundary_balanced δ S)
    (fun e => (gridBoundary_support_subset hδ.le hcover hinside e.1.1.2 e.2).trans hWK)
    a (hKΩ ha)
  have hformula := gridBoundary_cauchy hδ S hW hKint hcover hinside
    (f := fun _ => (1 : ℂ)) differentiableOn_const ha
  have hformula' : (∑ e : E, complexSegmentIntegral (fun z => (z - a)⁻¹)
      (complexGridInitial δ e.1) (complexGridTerminal δ e.1)) =
      2 * (Real.pi : ℂ) * I := by
    simpa only [gridEdgeIntegral, one_div, mul_one] using hformula
  have hzero : 2 * (Real.pi : ℂ) * I = 0 := hformula'.symm.trans hvanish
  exact (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero) hzero

#print axioms spherical_complement_connected_of_reciprocal_cycles
end RudinRCA.Chapter13
