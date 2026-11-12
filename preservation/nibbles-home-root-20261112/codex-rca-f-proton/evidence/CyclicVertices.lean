import Mathlib.Topology.Subpath
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

namespace RudinRCA.Chapter13Scratch

/-- Repeat the first vertex at the end of a cyclic `Fin n` vertex list. -/
def cyclicPolygonalVertices {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  fun j => v ⟨j.val % n, Nat.mod_lt _ hn⟩

theorem cyclicPolygonalVertices_castSucc {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ) (i : Fin n) :
    cyclicPolygonalVertices hn v i.castSucc = v i := by
  apply congrArg v
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

theorem cyclicPolygonalVertices_succ {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ) (i : Fin n) :
    cyclicPolygonalVertices hn v i.succ = v ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ := rfl

theorem cyclicPolygonalVertices_zero {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ) :
    cyclicPolygonalVertices hn v 0 = v ⟨0, hn⟩ := by
  apply congrArg v
  apply Fin.ext
  exact Nat.zero_mod n

theorem cyclicPolygonalVertices_last {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ) :
    cyclicPolygonalVertices hn v (Fin.last n) = v ⟨0, hn⟩ := by
  apply congrArg v
  apply Fin.ext
  exact Nat.mod_self n

universe u
variable {E : Type u} {n : ℕ}

/-- Compatible cyclic edges determine a finite vertex sequence with exactly their original
initial and terminal endpoints, and with first vertex equal to last vertex. -/
theorem closed_vertices_of_cyclic_edges (hn : 0 < n) (initial terminal : E → ℂ)
    (edge : Fin n → E)
    (hnext : ∀ i, terminal (edge i) =
      initial (edge ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩)) :
    ∃ p : Fin (n + 1) → ℂ,
      p 0 = initial (edge ⟨0, hn⟩) ∧ p (Fin.last n) = p 0 ∧
      ∀ i, p i.castSucc = initial (edge i) ∧ p i.succ = terminal (edge i) := by
  let v := fun i => initial (edge i)
  refine ⟨cyclicPolygonalVertices hn v, cyclicPolygonalVertices_zero hn v, ?_, ?_⟩
  · rw [cyclicPolygonalVertices_last, cyclicPolygonalVertices_zero]
  · intro i
    exact ⟨cyclicPolygonalVertices_castSucc hn v i,
      (cyclicPolygonalVertices_succ hn v i).trans (hnext i).symm⟩

/-- A supplied directed edge, cast to the corresponding consecutive vertices. -/
noncomputable def cyclicPolygonalEdgePath (hn : 0 < n) (initial terminal : E → ℂ)
    (edge : Fin n → E)
    (hnext : ∀ i, terminal (edge i) =
      initial (edge ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩)) (i : Fin n) :
    Path (cyclicPolygonalVertices hn (fun j => initial (edge j)) i.castSucc)
      (cyclicPolygonalVertices hn (fun j => initial (edge j)) i.succ) :=
  (Path.segment (initial (edge i)) (terminal (edge i))).cast
    (cyclicPolygonalVertices_castSucc hn (fun j => initial (edge j)) i)
    ((cyclicPolygonalVertices_succ hn (fun j => initial (edge j)) i).trans (hnext i).symm)

/-- The actual closed polygonal path chosen from cyclic edge geometry. The definition has no
integrand parameter; it is chosen once and works simultaneously for all admissible functions. -/
noncomputable def cyclicPolygonalPath (hn : 0 < n) (initial terminal : E → ℂ)
    (edge : Fin n → E)
    (hnext : ∀ i, terminal (edge i) =
      initial (edge ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩)) :
    Path (initial (edge ⟨0, hn⟩)) (initial (edge ⟨0, hn⟩)) :=
  (Path.concat (cyclicPolygonalVertices hn (fun j => initial (edge j)))
      (cyclicPolygonalEdgePath hn initial terminal edge hnext)).cast
    (cyclicPolygonalVertices_zero hn (fun j => initial (edge j))).symm
    (cyclicPolygonalVertices_last hn (fun j => initial (edge j))).symm

theorem curveIntegral_cyclicPolygonalEdgePath (ω : ℂ → ℂ →L[ℂ] ℂ)
    (hn : 0 < n) (initial terminal : E → ℂ) (edge : Fin n → E)
    (hnext : ∀ i, terminal (edge i) =
      initial (edge ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩)) (i : Fin n) :
    curveIntegral ω (cyclicPolygonalEdgePath hn initial terminal edge hnext i) =
      curveIntegral ω (Path.segment (initial (edge i)) (terminal (edge i))) := by
  simp [cyclicPolygonalEdgePath]

#print axioms cyclicPolygonalVertices_castSucc
#print axioms cyclicPolygonalVertices_succ
#print axioms cyclicPolygonalVertices_zero
#print axioms cyclicPolygonalVertices_last
#print axioms closed_vertices_of_cyclic_edges
#print axioms curveIntegral_cyclicPolygonalEdgePath

end RudinRCA.Chapter13Scratch
