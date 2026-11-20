import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Tactic.NormNum

/-! Aggregate dependencies: GridRepresentation, PolygonalCyclePackage, PolygonalRegularity. -/

noncomputable section
open Set Complex
open RudinRCA.Chapter13Scratch
open scoped BigOperators

namespace RudinRCA.Chapter13

/-- Rudin 13.5: a compact subset of an open set has a universal Cauchy representation by
finitely many actual closed polygonal paths in the open set minus the compact set.
The paths are chosen before the holomorphic function and the evaluation point. -/
theorem cauchy_formula_closed_polygonal_paths {K Ω : Set ℂ}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ (n : ℕ) (base : Fin n → ℂ) (γ : (j : Fin n) → Path (base j) (base j)),
      (∀ j, IsPolygonalPath (γ j) ∧ IsPiecewiseC1Path (γ j) ∧ Set.range (γ j) ⊆ Ω \ K) ∧
      ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω → ∀ z ∈ K,
        (∀ j, CurveIntegrable (fun w => ContinuousLinearMap.mul ℂ ℂ (f w / (w - z))) (γ j)) ∧
        (2 * (Real.pi : ℂ) * I)⁻¹ *
          (∑ j : Fin n, curveIntegral
            (fun w => ContinuousLinearMap.mul ℂ ℂ (f w / (w - z))) (γ j)) = f z := by
  classical
  obtain ⟨δ, hδ, S, hKint, hcover, hinside⟩ := finite_grid_neighborhood hK hΩ hKΩ
  let E := {e : GridEdge S // ¬gridEdgeInternal e}
  let initial : E → ℂ := fun e => complexGridInitial δ e.1
  let terminal : E → ℂ := fun e => complexGridTerminal δ e.1
  have hbalanced : ∀ v, Fintype.card {e : E // initial e = v} =
      Fintype.card {e : E // terminal e = v} := by
    intro v
    simpa only [Nat.card_eq_fintype_card] using complexGridBoundary_balanced δ S v
  have hsupport : ∀ e : E, segment ℝ (initial e) (terminal e) ⊆ Ω \ K := by
    intro e
    exact gridBoundary_support_subset hδ.le hcover hinside e.1.1.2 e.2
  obtain ⟨C, D, hpart, hD, hgeom, hint⟩ :=
    balanced_polygonal_cycle_package initial terminal hbalanced hsupport
  let enum : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  refine ⟨Fintype.card C, fun j => (D (enum j)).base, fun j => (D (enum j)).path, ?_, ?_⟩
  · intro j
    exact ⟨(hgeom (enum j)).1, (D (enum j)).path_piecewiseC1, (hgeom (enum j)).2⟩
  · intro f hf z hz
    have hker : ContinuousOn (fun w => f w / (w - z)) (Ω \ K) := by
      apply (hf.continuousOn.mono diff_subset).div (continuousOn_id.sub continuousOn_const)
      intro w hw
      apply sub_ne_zero.mpr
      intro heq
      exact hw.2 (heq.symm ▸ hz)
    obtain ⟨hintegrable, hsum⟩ := hint (fun w => f w / (w - z)) hker
    refine ⟨fun j => hintegrable (enum j), ?_⟩
    have hsum' : (∑ j : Fin (Fintype.card C), curveIntegral
        (fun w => ContinuousLinearMap.mul ℂ ℂ (f w / (w - z))) (D (enum j)).path) =
        2 * (Real.pi : ℂ) * I * f z := by
      calc
        _ = ∑ s : C, curveIntegral
            (fun w => ContinuousLinearMap.mul ℂ ℂ (f w / (w - z))) (D s).path :=
          enum.sum_comp _
        _ = ∑ e : E, complexSegmentIntegral (fun w => f w / (w - z))
            (initial e) (terminal e) := hsum
        _ = _ := gridBoundary_cauchy hδ S hΩ hKint hcover hinside hf hz
    rw [hsum', ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero

#print axioms cauchy_formula_closed_polygonal_paths

end RudinRCA.Chapter13
