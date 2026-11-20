import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Separation.Hausdorff

open Set Filter
open scoped Topology

namespace RudinRCA.Chapter13Scratch

/-- Removing countably many horizontal and vertical lines leaves a dense subset of the plane.
In particular this applies to every finite grid, or to the full integer square lattice. -/
theorem dense_off_coordinate_lines {s t : Set ℝ} (hs : s.Countable) (ht : t.Countable) :
    Dense (sᶜ ×ℂ tᶜ) := by
  apply dense_iff_closure_eq.mpr
  rw [Complex.closure_reProdIm, (Set.Countable.dense_compl ℝ hs).closure_eq,
    (Set.Countable.dense_compl ℝ ht).closure_eq]
  ext z
  simp [Complex.mem_reProdIm]

/-- Off-grid points are dense in every open subset, including the interior of a union of cells. -/
theorem open_subset_closure_off_coordinate_lines {s t : Set ℝ}
    (hs : s.Countable) (ht : t.Countable) {U : Set ℂ} (hU : IsOpen U) :
    U ⊆ closure (U ∩ (sᶜ ×ℂ tᶜ)) :=
  (dense_off_coordinate_lines hs ht).open_subset_closure_inter hU

/-- Pointwise continuity extends an off-grid identity to any point of its open region of validity.
The two functions need only be continuous at this one point. -/
theorem eq_of_continuousAt_off_coordinate_lines {s t : Set ℝ}
    (hs : s.Countable) (ht : t.Countable) {U : Set ℂ} (hU : IsOpen U)
    {z : ℂ} (hz : z ∈ U) {f g : ℂ → ℂ} (hf : ContinuousAt f z) (hg : ContinuousAt g z)
    (heq : ∀ w ∈ U, w.re ∉ s → w.im ∉ t → f w = g w) : f z = g z := by
  have hzcl : z ∈ closure (U ∩ (sᶜ ×ℂ tᶜ)) :=
    open_subset_closure_off_coordinate_lines hs ht hU hz
  have hfg : EqOn f g (U ∩ (sᶜ ×ℂ tᶜ)) :=
    fun w hw => heq w hw.1 hw.2.1 hw.2.2
  have : NeBot (𝓝[U ∩ (sᶜ ×ℂ tᶜ)] z) := mem_closure_iff_clusterPt.mp hzcl
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.mono_left inf_le_left) (hg.mono_left inf_le_left)
    (hfg.eventuallyEq_of_mem self_mem_nhdsWithin)

/-- An identity between two continuous functions on an open set is determined by its off-grid
values. This is the final continuity step in the polygonal Cauchy construction. -/
theorem eqOn_of_off_coordinate_lines {s t : Set ℝ}
    (hs : s.Countable) (ht : t.Countable) {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ → ℂ} (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (heq : ∀ w ∈ U, w.re ∉ s → w.im ∉ t → f w = g w) : EqOn f g U := by
  have hfg : EqOn f g (U ∩ (sᶜ ×ℂ tᶜ)) :=
    fun w hw => heq w hw.1 hw.2.1 hw.2.2
  exact hfg.of_subset_closure hf hg inter_subset_left
    (open_subset_closure_off_coordinate_lines hs ht hU)

theorem dense_off_square_lattice (h : ℝ) :
    Dense ((Set.range (fun i : ℤ => (i : ℝ) * h))ᶜ ×ℂ
      (Set.range (fun i : ℤ => (i : ℝ) * h))ᶜ) :=
  dense_off_coordinate_lines (Set.countable_range _) (Set.countable_range _)

#print axioms dense_off_coordinate_lines
#print axioms open_subset_closure_off_coordinate_lines
#print axioms eq_of_continuousAt_off_coordinate_lines
#print axioms eqOn_of_off_coordinate_lines
#print axioms dense_off_square_lattice

end RudinRCA.Chapter13Scratch
