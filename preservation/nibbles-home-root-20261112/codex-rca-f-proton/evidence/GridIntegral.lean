import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! Compile after GridBoundary, GridSupport, SquareKernel, and SegmentIntegralBridge. -/
noncomputable section
open Complex Set
open RudinRCA.Chapter13Scratch
open scoped BigOperators
namespace RudinRCA.Chapter13

def gridEdgeIntegral {S : Finset GridCell} (δ : ℝ) (f : ℂ → ℂ) (e : GridEdge S) : ℂ :=
  complexSegmentIntegral f (complexGridInitial δ e) (complexGridTerminal δ e)

theorem gridEdgeIntegral_reverse {S : Finset GridCell} (δ : ℝ) (f : ℂ → ℂ)
    (e : {e : GridEdge S // gridEdgeInternal e}) :
    gridEdgeIntegral δ f (gridInternalReverse S e).1 = -gridEdgeIntegral δ f e.1 := by
  change complexSegmentIntegral f
    (gridPoint δ (gridVertex (gridNeighbor e.1.1.1 e.1.2) (e.1.2 + 2)))
    (gridPoint δ (gridVertex (gridNeighbor e.1.1.1 e.1.2) (e.1.2 + 2 + 1))) = _
  rw [gridVertex_reverse_initial, gridVertex_reverse_terminal]
  exact complexSegmentIntegral_symm _ _ _

/-- Opposite orientations cancel every interior edge, with multiplicity retained. -/
theorem gridInternal_integral_sum_eq_zero (S : Finset GridCell) (δ : ℝ) (f : ℂ → ℂ) :
    ∑ e : {e : GridEdge S // gridEdgeInternal e}, gridEdgeIntegral δ f e.1 = 0 := by
  classical
  let ρ : Equiv.Perm {e : GridEdge S // gridEdgeInternal e} :=
    { toFun := gridInternalReverse S, invFun := gridInternalReverse S,
      left_inv := gridInternalReverse_involutive S,
      right_inv := gridInternalReverse_involutive S }
  have hsum := ρ.sum_comp (fun e => gridEdgeIntegral δ f e.1)
  have hrev : (∑ e : {e : GridEdge S // gridEdgeInternal e},
      gridEdgeIntegral δ f (ρ e).1) =
      -(∑ e : {e : GridEdge S // gridEdgeInternal e}, gridEdgeIntegral δ f e.1) := by
    simp only [ρ, gridEdgeIntegral_reverse, Finset.sum_neg_distrib]
  rw [hrev] at hsum
  exact CharZero.neg_eq_self_iff.mp hsum

theorem gridBoundary_integral_sum_eq_total (S : Finset GridCell) (δ : ℝ) (f : ℂ → ℂ) :
    ∑ e : {e : GridEdge S // ¬gridEdgeInternal e}, gridEdgeIntegral δ f e.1 =
      ∑ e : GridEdge S, gridEdgeIntegral δ f e := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (@gridEdgeInternal S) (gridEdgeIntegral δ f)
  rw [gridInternal_integral_sum_eq_zero, zero_add] at h
  exact h

/-- The four affine edge integrals give the ordinary counterclockwise rectangle integral. -/
theorem gridCell_integral_sum (δ : ℝ) (f : ℂ → ℂ) (c : GridCell) :
    (∑ i : Fin 4, complexSegmentIntegral f (gridPoint δ (gridVertex c i))
      (gridPoint δ (gridVertex c (i + 1)))) =
      rectangleIntegral f (δ * c.1) (δ * (c.1 + 1)) (δ * c.2) (δ * (c.2 + 1)) := by
  rw [Fin.sum_univ_four]
  simp only [gridVertex, gridCorner, gridPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceAdd, Prod.fst_add, Prod.snd_add,
    Int.cast_add, Int.cast_one, Int.cast_zero, add_zero, mul_zero]
  rw [complexSegmentIntegral_horizontal, complexSegmentIntegral_vertical,
    complexSegmentIntegral_horizontal, complexSegmentIntegral_vertical]
  simp only [intervalIntegral.integral_symm, rectangleIntegral]
  ring

theorem gridBoundary_integral_sum_eq_rectangles (S : Finset GridCell) (δ : ℝ) (f : ℂ → ℂ) :
    (∑ e : {e : GridEdge S // ¬gridEdgeInternal e}, gridEdgeIntegral δ f e.1) =
      ∑ c : S, rectangleIntegral f (δ * c.1.1) (δ * (c.1.1 + 1))
        (δ * c.1.2) (δ * (c.1.2 + 1)) := by
  rw [gridBoundary_integral_sum_eq_total]
  change (∑ e : S × Fin 4, complexSegmentIntegral f
    (gridPoint δ (gridVertex e.1.1 e.2)) (gridPoint δ (gridVertex e.1.1 (e.2 + 1)))) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c hc
  exact gridCell_integral_sum δ f c.1

#print axioms gridEdgeIntegral_reverse
#print axioms gridInternal_integral_sum_eq_zero
#print axioms gridBoundary_integral_sum_eq_total
#print axioms gridCell_integral_sum
#print axioms gridBoundary_integral_sum_eq_rectangles
end RudinRCA.Chapter13
