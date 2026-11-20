import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! Pending scratch; compile after GridBoundary.lean and GridGeometry.lean. -/
noncomputable section
open Set Function
namespace RudinRCA.Chapter13

def gridPoint (δ : ℝ) (c : ℤ × ℤ) : ℂ :=
  ((δ * c.1 : ℝ) : ℂ) + ((δ * c.2 : ℝ) : ℂ) * Complex.I

theorem gridClosedCell_convex (δ : ℝ) (c : ℤ × ℤ) : Convex ℝ (gridClosedCell δ c) :=
  ((convex_Icc (δ * c.1) (δ * (c.1 + 1))).linear_preimage Complex.reLm).inter
    ((convex_Icc (δ * c.2) (δ * (c.2 + 1))).linear_preimage Complex.imLm)

theorem gridVertex_mem_cell {δ : ℝ} (hδ : 0 ≤ δ) (c : ℤ × ℤ) (i : Fin 4) :
    gridPoint δ (gridVertex c i) ∈ gridClosedCell δ c := by
  fin_cases i <;>
    simp [gridPoint, gridVertex, gridCorner, gridClosedCell] <;>
    constructor <;> nlinarith

def gridEdgeSupport (δ : ℝ) (c : ℤ × ℤ) (i : Fin 4) : Set ℂ :=
  segment ℝ (gridPoint δ (gridVertex c i)) (gridPoint δ (gridVertex c (i + 1)))

theorem gridEdgeSupport_subset_cell {δ : ℝ} (hδ : 0 ≤ δ) (c : ℤ × ℤ) (i : Fin 4) :
    gridEdgeSupport δ c i ⊆ gridClosedCell δ c :=
  (gridClosedCell_convex δ c).segment_subset (gridVertex_mem_cell hδ c i)
    (gridVertex_mem_cell hδ c (i + 1))

theorem gridEdgeSupport_subset_neighbor {δ : ℝ} (hδ : 0 ≤ δ) (c : ℤ × ℤ) (i : Fin 4) :
    gridEdgeSupport δ c i ⊆ gridClosedCell δ (gridNeighbor c i) := by
  apply (gridClosedCell_convex δ (gridNeighbor c i)).segment_subset
  · rw [← gridVertex_reverse_terminal c i]
    exact gridVertex_mem_cell hδ _ _
  · rw [← gridVertex_reverse_initial c i]
    exact gridVertex_mem_cell hδ _ _

/-- Every uncancelled edge lies in the open domain and avoids the original compact set. -/
theorem gridBoundary_support_subset {K Ω : Set ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    {S : Finset (ℤ × ℤ)}
    (hcover : ∀ c, (gridClosedCell δ c ∩ K).Nonempty → c ∈ S)
    (hinside : ∀ c ∈ S, gridClosedCell δ c ⊆ Ω)
    {c : ℤ × ℤ} (hc : c ∈ S) {i : Fin 4} (hout : gridNeighbor c i ∉ S) :
    gridEdgeSupport δ c i ⊆ Ω \ K := by
  intro z hz
  refine ⟨hinside c hc (gridEdgeSupport_subset_cell hδ c i hz), ?_⟩
  intro hzK
  exact hout (hcover _ ⟨z, gridEdgeSupport_subset_neighbor hδ c i hz, hzK⟩)

def complexGridInitial {S : Finset (ℤ × ℤ)} (δ : ℝ) (e : GridEdge S) : ℂ :=
  gridPoint δ (gridEdgeInitial e)

def complexGridTerminal {S : Finset (ℤ × ℤ)} (δ : ℝ) (e : GridEdge S) : ℂ :=
  gridPoint δ (gridEdgeTerminal e)

/-- Balance after passing from lattice vertices to actual complex endpoints. -/
theorem complexGridBoundary_balanced (δ : ℝ) (S : Finset (ℤ × ℤ)) :
    ∀ v : ℂ, Nat.card {e : {e : GridEdge S // ¬gridEdgeInternal e} //
      complexGridInitial δ e.1 = v} =
      Nat.card {e : {e : GridEdge S // ¬gridEdgeInternal e} //
      complexGridTerminal δ e.1 = v} := by
  classical
  apply balanced_complement
  · apply balanced_of_successor _ _ ((Equiv.refl S).prodCongr (finRotate 4))
    intro e
    simp [complexGridTerminal, complexGridInitial, gridEdgeTerminal, gridEdgeInitial,
      finRotate_apply]
  · apply balanced_of_successor _ _
      ({ toFun := gridInternalReverse S, invFun := gridInternalReverse S,
         left_inv := gridInternalReverse_involutive S,
         right_inv := gridInternalReverse_involutive S } : Equiv.Perm _)
    intro e
    exact congrArg (gridPoint δ) (gridVertex_reverse_initial _ _).symm

#print axioms gridClosedCell_convex
#print axioms gridVertex_mem_cell
#print axioms gridEdgeSupport_subset_cell
#print axioms gridEdgeSupport_subset_neighbor
#print axioms gridBoundary_support_subset
#print axioms complexGridBoundary_balanced
end RudinRCA.Chapter13
