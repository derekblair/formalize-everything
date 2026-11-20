import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Logic.Equiv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases

noncomputable section
open Function
namespace RudinRCA.Chapter13

private def swapSubtypeConditions {E : Type*} (p q : E → Prop) :
    {e : {e // p e} // q e.1} ≃ {e : {e // q e} // p e.1} where
  toFun e := ⟨⟨e.1.1, e.2⟩, e.1.2⟩
  invFun e := ⟨⟨e.1.1, e.2⟩, e.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem card_fiber_complement {E V : Type*} [Fintype E] (p : E → Prop)
    (f : E → V) (v : V) :
    Nat.card {e : {e // ¬p e} // f e.1 = v} =
      Nat.card {e // f e = v} - Nat.card {e : {e // p e} // f e.1 = v} := by
  classical
  simp only [Nat.card_eq_fintype_card]
  calc
    _ = Fintype.card {e : {e // f e = v} // ¬p e.1} :=
      Fintype.card_congr (swapSubtypeConditions (fun e => ¬p e) (fun e => f e = v))
    _ = Fintype.card {e // f e = v} -
        Fintype.card {e : {e // f e = v} // p e.1} := Fintype.card_subtype_compl _
    _ = _ := congrArg (fun n => Fintype.card {e // f e = v} - n)
      (Fintype.card_congr (swapSubtypeConditions (fun e => f e = v) p))

/-- Deleting a balanced subfamily from a finite balanced directed family preserves balance. -/
theorem balanced_complement {E V : Type*} [Fintype E] (initial terminal : E → V)
    (p : E → Prop)
    (htotal : ∀ v, Nat.card {e // initial e = v} = Nat.card {e // terminal e = v})
    (hpart : ∀ v, Nat.card {e : {e // p e} // initial e.1 = v} =
      Nat.card {e : {e // p e} // terminal e.1 = v}) :
    ∀ v, Nat.card {e : {e // ¬p e} // initial e.1 = v} =
      Nat.card {e : {e // ¬p e} // terminal e.1 = v} := by
  intro v
  rw [card_fiber_complement, card_fiber_complement, htotal v, hpart v]

/-- A successor permutation certifies balance, preserving edge multiplicities. -/
theorem balanced_of_successor {E V : Type*} [Fintype E] (initial terminal : E → V)
    (σ : Equiv.Perm E) (hσ : ∀ e, terminal e = initial (σ e)) :
    ∀ v, Nat.card {e // initial e = v} = Nat.card {e // terminal e = v} := by
  intro v
  exact (Nat.card_congr (σ.subtypeEquiv
    (p := fun e => terminal e = v) (q := fun e => initial e = v)
      (fun e => by rw [hσ e]))).symm

abbrev GridCell := ℤ × ℤ

def gridCorner (i : Fin 4) : GridCell := ![(0, 0), (1, 0), (1, 1), (0, 1)] i

def gridVertex (c : GridCell) (i : Fin 4) : GridCell := c + gridCorner i

def gridNeighbor (c : GridCell) (i : Fin 4) : GridCell :=
  c + ![(0, -1), (1, 0), (0, 1), (-1, 0)] i

theorem gridNeighbor_reverse (c : GridCell) (i : Fin 4) :
    gridNeighbor (gridNeighbor c i) (i + 2) = c := by
  fin_cases i <;> ext <;> simp [gridNeighbor]

theorem gridVertex_reverse_initial (c : GridCell) (i : Fin 4) :
    gridVertex (gridNeighbor c i) (i + 2) = gridVertex c (i + 1) := by
  fin_cases i <;> ext <;> simp [gridNeighbor, gridVertex, gridCorner]

theorem gridVertex_reverse_terminal (c : GridCell) (i : Fin 4) :
    gridVertex (gridNeighbor c i) (i + 2 + 1) = gridVertex c i := by
  fin_cases i <;> ext <;> simp [gridNeighbor, gridVertex, gridCorner]

abbrev GridEdge (S : Finset GridCell) := S × Fin 4

def gridEdgeInitial {S : Finset GridCell} (e : GridEdge S) : GridCell :=
  gridVertex e.1.1 e.2

def gridEdgeTerminal {S : Finset GridCell} (e : GridEdge S) : GridCell :=
  gridVertex e.1.1 (e.2 + 1)

def gridEdgeInternal {S : Finset GridCell} (e : GridEdge S) : Prop :=
  gridNeighbor e.1.1 e.2 ∈ S

def gridInternalReverse (S : Finset GridCell)
    (e : {e : GridEdge S // gridEdgeInternal e}) :
    {e : GridEdge S // gridEdgeInternal e} :=
  ⟨(⟨gridNeighbor e.1.1.1 e.1.2, e.2⟩, e.1.2 + 2), by
    change gridNeighbor (gridNeighbor e.1.1.1 e.1.2) (e.1.2 + 2) ∈ S
    rw [gridNeighbor_reverse]
    exact e.1.1.2⟩

theorem gridInternalReverse_involutive (S : Finset GridCell) :
    Involutive (gridInternalReverse S) := by
  intro e
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact gridNeighbor_reverse _ _
  · change e.1.2 + 2 + 2 = e.1.2
    exact (show ∀ i : Fin 4, i + 2 + 2 = i from by decide) e.1.2

/-- The external edges of a finite union of grid cells form a balanced family. -/
theorem gridBoundary_balanced (S : Finset GridCell) :
    ∀ v, Nat.card {e : {e : GridEdge S // ¬gridEdgeInternal e} //
      gridEdgeInitial e.1 = v} =
      Nat.card {e : {e : GridEdge S // ¬gridEdgeInternal e} //
      gridEdgeTerminal e.1 = v} := by
  classical
  apply balanced_complement
  · apply balanced_of_successor _ _ ((Equiv.refl S).prodCongr (finRotate 4))
    intro e
    simp [gridEdgeTerminal, gridEdgeInitial, finRotate_apply]
  · apply balanced_of_successor _ _
      ({ toFun := gridInternalReverse S, invFun := gridInternalReverse S,
         left_inv := gridInternalReverse_involutive S,
         right_inv := gridInternalReverse_involutive S } : Equiv.Perm _)
    intro e
    exact (gridVertex_reverse_initial _ _).symm

#print axioms balanced_complement
#print axioms balanced_of_successor
#print axioms gridNeighbor_reverse
#print axioms gridVertex_reverse_initial
#print axioms gridVertex_reverse_terminal
#print axioms gridInternalReverse_involutive
#print axioms gridBoundary_balanced
end RudinRCA.Chapter13
