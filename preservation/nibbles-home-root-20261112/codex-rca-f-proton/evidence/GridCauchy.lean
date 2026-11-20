import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-! Compile after GridIntegral and GridGeometry. -/
noncomputable section
open Set Complex
open RudinRCA.Chapter13Scratch
open scoped BigOperators
namespace RudinRCA.Chapter13

/-- Evaluation points outside the horizontal and vertical lattice lines. -/
def GridOffLines (δ : ℝ) (z : ℂ) : Prop :=
  (∀ n : ℤ, z.re ≠ δ * n) ∧ (∀ n : ℤ, z.im ≠ δ * n)

theorem gridClosedCell_strict_of_offLines {δ : ℝ} {z : ℂ}
    (hz : GridOffLines δ z) {c : GridCell} (hc : z ∈ gridClosedCell δ c) :
    δ * c.1 < z.re ∧ z.re < δ * (c.1 + 1) ∧
      δ * c.2 < z.im ∧ z.im < δ * (c.2 + 1) := by
  change (_ ≤ z.re ∧ z.re ≤ _) ∧ (_ ≤ z.im ∧ z.im ≤ _) at hc
  refine ⟨lt_of_le_of_ne hc.1.1 (hz.1 c.1).symm, ?_,
    lt_of_le_of_ne hc.2.1 (hz.2 c.2).symm, ?_⟩
  · exact lt_of_le_of_ne hc.1.2 (by simpa using hz.1 (c.1 + 1))
  · exact lt_of_le_of_ne hc.2.2 (by simpa using hz.2 (c.2 + 1))

theorem gridClosedCell_unique_of_offLines {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : GridOffLines δ z) {c d : GridCell}
    (hc : z ∈ gridClosedCell δ c) (hd : z ∈ gridClosedCell δ d) : c = d := by
  obtain ⟨hc₁, hc₂, hc₃, hc₄⟩ := gridClosedCell_strict_of_offLines hz hc
  obtain ⟨hd₁, hd₂, hd₃, hd₄⟩ := gridClosedCell_strict_of_offLines hz hd
  have hcR : ⌊z.re / δ⌋ = c.1 := Int.floor_eq_iff.mpr
    ⟨(le_div_iff₀ hδ).mpr (by nlinarith), (div_lt_iff₀ hδ).mpr (by nlinarith)⟩
  have hdR : ⌊z.re / δ⌋ = d.1 := Int.floor_eq_iff.mpr
    ⟨(le_div_iff₀ hδ).mpr (by nlinarith), (div_lt_iff₀ hδ).mpr (by nlinarith)⟩
  have hcI : ⌊z.im / δ⌋ = c.2 := Int.floor_eq_iff.mpr
    ⟨(le_div_iff₀ hδ).mpr (by nlinarith), (div_lt_iff₀ hδ).mpr (by nlinarith)⟩
  have hdI : ⌊z.im / δ⌋ = d.2 := Int.floor_eq_iff.mpr
    ⟨(le_div_iff₀ hδ).mpr (by nlinarith), (div_lt_iff₀ hδ).mpr (by nlinarith)⟩
  exact Prod.ext (hcR.symm.trans hdR) (hcI.symm.trans hdI)

theorem gridClosedCell_eq_uIcc {δ : ℝ} (hδ : 0 ≤ δ) (c : GridCell) :
    gridClosedCell δ c =
      uIcc (δ * c.1) (δ * (c.1 + 1)) ×ℂ uIcc (δ * c.2) (δ * (c.2 + 1)) := by
  rw [uIcc_of_le (by nlinarith : δ * (c.1 : ℝ) ≤ δ * ((c.1 : ℝ) + 1)),
    uIcc_of_le (by nlinarith : δ * (c.2 : ℝ) ≤ δ * ((c.2 : ℝ) + 1))]
  rfl

/-- Cauchy's formula for the uncancelled grid boundary, initially off the lattice lines. -/
theorem gridBoundary_cauchy_offLines {δ : ℝ} (hδ : 0 < δ) (S : Finset GridCell)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hinside : ∀ c ∈ S, gridClosedCell δ c ⊆ Ω) {z : ℂ}
    (hz : z ∈ ⋃ c ∈ S, gridClosedCell δ c) (hoff : GridOffLines δ z) :
    (∑ e : {e : GridEdge S // ¬gridEdgeInternal e},
      gridEdgeIntegral δ (fun w => f w / (w - z)) e.1) = 2 * (Real.pi : ℂ) * I * f z := by
  classical
  obtain ⟨c, hcS, hzc⟩ := mem_iUnion₂.mp hz
  let c₀ : S := ⟨c, hcS⟩
  rw [gridBoundary_integral_sum_eq_rectangles]
  rw [Finset.sum_eq_single c₀]
  · obtain ⟨ha, hb, hc, hd⟩ := gridClosedCell_strict_of_offLines hoff hzc
    apply rectangle_cauchy_formula hΩ hf _ ha hb hc hd
    exact (gridClosedCell_eq_uIcc hδ.le c).symm ▸ hinside c hcS
  · intro d hd hdc
    apply rectangle_cauchy_formula_of_not_mem hf
    · exact (gridClosedCell_eq_uIcc hδ.le d.1).symm ▸ hinside d.1 d.2
    · intro hzd
      have hzdc : z ∈ gridClosedCell δ d.1 := (gridClosedCell_eq_uIcc hδ.le d.1).symm ▸ hzd
      apply hdc
      apply Subtype.ext
      exact gridClosedCell_unique_of_offLines hδ hoff hzdc hzc
  · simp

#print axioms gridClosedCell_strict_of_offLines
#print axioms gridClosedCell_unique_of_offLines
#print axioms gridClosedCell_eq_uIcc
#print axioms gridBoundary_cauchy_offLines
end RudinRCA.Chapter13
