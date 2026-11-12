import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Complex.Basic

/-! Aggregate dependencies: PolygonalCyclePackage, PolygonalRegularity, CycleSeparation. -/

noncomputable section
open Set Complex
open RudinRCA.Chapter13Scratch
open scoped BigOperators OnePoint

namespace RudinRCA.Chapter13

/-- Passing from actual closed polygonal paths to balanced indexed edge families preserves the
zero reciprocal-integral condition, including every edge multiplicity. -/
theorem reciprocalBalancedCyclesVanish_of_polygonal_paths {Ω : Set ℂ}
    (hzero : ∀ {b : ℂ} (γ : Path b b), IsPolygonalPath γ → Set.range γ ⊆ Ω →
      ∀ a ∉ Ω, curveIntegral (fun z => ContinuousLinearMap.mul ℂ ℂ ((z - a)⁻¹)) γ = 0) :
    ReciprocalBalancedCyclesVanish Ω := by
  classical
  intro E _ initial terminal hbalanced hsupport a ha
  have hbal : ∀ v, Fintype.card {e : E // initial e = v} =
      Fintype.card {e : E // terminal e = v} := by
    simpa only [Nat.card_eq_fintype_card] using hbalanced
  obtain ⟨C, D, hpart, hD, hgeom, hint⟩ :=
    balanced_polygonal_cycle_package initial terminal hbal hsupport
  have hrec : ContinuousOn (fun z : ℂ => (z - a)⁻¹) Ω := by
    apply (continuousOn_id.sub continuousOn_const).inv₀
    intro z hz
    exact sub_ne_zero.mpr (fun heq => ha (heq ▸ hz))
  obtain ⟨hintegrable, hsum⟩ := hint (fun z => (z - a)⁻¹) hrec
  rw [← hsum]
  apply Finset.sum_eq_zero
  intro s hs
  exact hzero (D s).path (hgeom s).1 (hgeom s).2 a ha

/-- Zero reciprocal integrals on all actual closed polygonal paths force connected spherical
complement. This is the geometric path version of Rudin 13.11(c) implies (d). -/
theorem spherical_complement_connected_of_polygonal_reciprocal_integrals {Ω : Set ℂ}
    (hΩ : IsOpen Ω)
    (hzero : ∀ {b : ℂ} (γ : Path b b), IsPolygonalPath γ → Set.range γ ⊆ Ω →
      ∀ a ∉ Ω, curveIntegral (fun z => ContinuousLinearMap.mul ℂ ℂ ((z - a)⁻¹)) γ = 0) :
    IsConnected (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ :=
  spherical_complement_connected_of_reciprocal_cycles hΩ
    (reciprocalBalancedCyclesVanish_of_polygonal_paths hzero)

/-- The same conclusion for the full finite piecewise C¹ path class. -/
theorem spherical_complement_connected_of_piecewiseC1_reciprocal_integrals {Ω : Set ℂ}
    (hΩ : IsOpen Ω)
    (hzero : ∀ {b : ℂ} (γ : Path b b), IsPiecewiseC1Path γ → Set.range γ ⊆ Ω →
      ∀ a ∉ Ω, curveIntegral (fun z => ContinuousLinearMap.mul ℂ ℂ ((z - a)⁻¹)) γ = 0) :
    IsConnected (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ := by
  apply spherical_complement_connected_of_polygonal_reciprocal_integrals hΩ
  intro b γ hγ hγΩ a ha
  exact hzero γ (isPiecewiseC1Path_of_isPolygonalPath hγ) hγΩ a ha

#print axioms reciprocalBalancedCyclesVanish_of_polygonal_paths
#print axioms spherical_complement_connected_of_polygonal_reciprocal_integrals
#print axioms spherical_complement_connected_of_piecewiseC1_reciprocal_integrals

end RudinRCA.Chapter13
