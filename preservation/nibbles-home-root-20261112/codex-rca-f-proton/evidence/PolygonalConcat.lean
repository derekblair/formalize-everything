import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Topology.Subpath
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace RudinRCA.Chapter13Scratch

theorem curveIntegrable_concat (ω : ℂ → ℂ →L[ℂ] ℂ) {n : ℕ}
    (p : Fin (n + 1) → ℂ)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (hF : ∀ i, CurveIntegrable ω (F i)) : CurveIntegrable ω (Path.concat p F) := by
  induction n generalizing p with
  | zero => simpa using CurveIntegrable.refl ω (p 0)
  | succ n ih =>
    rw [Path.concat_succ]
    exact (ih (p ∘ Fin.castSucc) (fun i => F i.castSucc) (fun i => hF i.castSucc)).trans
      (hF (Fin.last n))

/-- Integration over a finite concatenation is the sum of the individual path integrals. -/
theorem curveIntegral_concat (ω : ℂ → ℂ →L[ℂ] ℂ) {n : ℕ}
    (p : Fin (n + 1) → ℂ)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (hF : ∀ i, CurveIntegrable ω (F i)) :
    curveIntegral ω (Path.concat p F) = ∑ i : Fin n, curveIntegral ω (F i) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [Path.concat_succ, curveIntegral_trans
      (curveIntegrable_concat ω (p ∘ Fin.castSucc) (fun i => F i.castSucc)
        (fun i => hF i.castSucc)) (hF (Fin.last n))]
    rw [ih (p ∘ Fin.castSucc) (fun i => F i.castSucc) (fun i => hF i.castSucc)]
    exact (Fin.sum_univ_castSucc (fun i : Fin (n + 1) => curveIntegral ω (F i))).symm

theorem concat_range_subset {n : ℕ} (p : Fin (n + 1) → ℂ)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ)) {U : Set ℂ}
    (hstart : p 0 ∈ U) (hF : ∀ i, Set.range (F i) ⊆ U) :
    Set.range (Path.concat p F) ⊆ U := by
  induction n generalizing p with
  | zero =>
    rintro x ⟨t, rfl⟩
    simpa using hstart
  | succ n ih =>
    rw [Path.concat_succ, Path.trans_range]
    exact Set.union_subset
      (ih (p ∘ Fin.castSucc) (fun i => F i.castSucc) hstart (fun i => hF i.castSucc))
      (hF (Fin.last n))

/-- A finite compatible family with equal first and last vertices gives an actual closed path,
retaining both the range restriction and the sum of the edge integrals. For polygonal paths take
each `F i` to be `Path.segment (p i.castSucc) (p i.succ)`. -/
theorem closed_concat_integral (ω : ℂ → ℂ →L[ℂ] ℂ) {n : ℕ}
    (p : Fin (n + 1) → ℂ)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (hclosed : p (Fin.last n) = p 0) {U : Set ℂ}
    (hstart : p 0 ∈ U) (hFrange : ∀ i, Set.range (F i) ⊆ U)
    (hF : ∀ i, CurveIntegrable ω (F i)) :
    ∃ γ : Path (p 0) (p 0), Set.range γ ⊆ U ∧ CurveIntegrable ω γ ∧
      curveIntegral ω γ = ∑ i : Fin n, curveIntegral ω (F i) := by
  let γ := (Path.concat p F).cast rfl hclosed.symm
  refine ⟨γ, ?_, ?_, ?_⟩
  · simpa [γ] using concat_range_subset p F hstart hFrange
  · exact (curveIntegrable_cast_iff rfl hclosed.symm).mpr (curveIntegrable_concat ω p F hF)
  · simpa [γ] using curveIntegral_concat ω p F hF

#print axioms curveIntegrable_concat
#print axioms curveIntegral_concat
#print axioms concat_range_subset
#print axioms closed_concat_integral

end RudinRCA.Chapter13Scratch
