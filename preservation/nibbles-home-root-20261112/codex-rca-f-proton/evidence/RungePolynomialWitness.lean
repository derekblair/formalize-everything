import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.LinearAlgebra.Span.Basic

/-!
Scratch companion to RungeRationalWitness.lean. In an aggregate this file
follows the definitions of compactCoordinate, rungeGenerators, and rungeSpace.
It supplies the polynomial witness needed when infinity is the only permitted
pole, as in Rudin 13.7.
-/

open Set Polynomial
open scoped Topology OnePoint

namespace RudinRCA.Chapter13

/-- When infinity is the only permitted pole, every element of the Runge
generator span is the restriction of a complex polynomial. -/
theorem rungeSpace_polynomial_witness (K : Set ℂ) {g : C(K, ℂ)}
    (hg : g ∈ rungeSpace K {(∞ : OnePoint ℂ)}) :
    ∃ P : ℂ[X], ∀ x : K, P.eval x = g x := by
  classical
  apply Submodule.span_induction (p := fun g _ =>
    ∃ P : ℂ[X], ∀ x : K, P.eval x = g x) ?_ ?_ ?_ ?_ hg
  · intro g hg
    rcases hg with rfl | ⟨α, hα, n, rfl⟩ | ⟨_, n, rfl⟩
    · exact ⟨1, fun _ => by simp⟩
    · simp at hα
    · exact ⟨X ^ n, fun x => by simp [compactCoordinate]⟩
  · exact ⟨0, fun _ => by simp⟩
  · intro g h _ _ hg hh
    obtain ⟨P, hP⟩ := hg
    obtain ⟨Q, hQ⟩ := hh
    refine ⟨P + Q, ?_⟩
    intro x
    simp only [eval_add, hP, hQ, ContinuousMap.add_apply]
  · intro c g _ hg
    obtain ⟨P, hP⟩ := hg
    refine ⟨C c * P, ?_⟩
    intro x
    simp only [eval_mul, eval_C, hP, ContinuousMap.smul_apply, smul_eq_mul]

#print axioms rungeSpace_polynomial_witness

end RudinRCA.Chapter13
