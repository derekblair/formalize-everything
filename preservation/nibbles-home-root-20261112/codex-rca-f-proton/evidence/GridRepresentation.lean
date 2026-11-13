import Mathlib.Topology.Algebra.Affine
import Mathlib.Analysis.Convex.Segment
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FieldSimp

/-! Compile after GridCauchy, OffGridDensity, ContourContinuity, and RungeAssembly. -/
noncomputable section
open Set Complex
open RudinRCA.Chapter13Scratch
open scoped BigOperators Topology Interval
namespace RudinRCA.Chapter13

/-- Continuous dependence of one affine edge integral on a point outside that edge. -/
theorem continuousAt_complexSegmentKernel {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : ContinuousOn f Ω) {a b z : ℂ} (hab : segment ℝ a b ⊆ Ω)
    (hz : z ∉ segment ℝ a b) :
    ContinuousAt (fun w => complexSegmentIntegral (fun ζ => f ζ / (ζ - w)) a b) z := by
  have hγ : ContinuousOn (AffineMap.lineMap a b) (uIcc (0 : ℝ) 1) :=
    AffineMap.lineMap_continuous.continuousOn
  have hmem : ∀ t ∈ uIcc (0 : ℝ) 1, AffineMap.lineMap a b t ∈ Ω := by
    intro t ht
    exact hab (lineMap_mem_segment ℝ a b (by simpa using ht))
  have hg : ContinuousOn (fun t : ℝ => f (AffineMap.lineMap a b t) * (b - a))
      (uIcc (0 : ℝ) 1) := (hf.comp hγ hmem).mul_const _
  have hz' : z ∉ AffineMap.lineMap a b '' uIcc (0 : ℝ) 1 := by
    simpa [segment_eq_image_lineMap] using hz
  have h := continuousAt_kernel_intervalIntegral hγ hg hz'
  convert h using 1
  ext w
  apply intervalIntegral.integral_congr
  intro t ht
  exact div_mul_eq_mul_div₀ _ _ _

/-- Extend the finite-grid identity through gridline points by continuity. -/
theorem gridBoundary_cauchy {K Ω : Set ℂ} {δ : ℝ} (hδ : 0 < δ) (S : Finset GridCell)
    (hΩ : IsOpen Ω) (hKint : K ⊆ interior (⋃ c ∈ S, gridClosedCell δ c))
    (hcover : ∀ c, (gridClosedCell δ c ∩ K).Nonempty → c ∈ S)
    (hinside : ∀ c ∈ S, gridClosedCell δ c ⊆ Ω)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) {z : ℂ} (hzK : z ∈ K) :
    (∑ e : {e : GridEdge S // ¬gridEdgeInternal e},
      gridEdgeIntegral δ (fun w => f w / (w - z)) e.1) = 2 * (Real.pi : ℂ) * I * f z := by
  classical
  have hUΩ : (⋃ c ∈ S, gridClosedCell δ c) ⊆ Ω := by
    rintro w hw
    obtain ⟨c, hc, hwc⟩ := mem_iUnion₂.mp hw
    exact hinside c hc hwc
  have hzΩ := hUΩ (interior_subset (hKint hzK))
  apply eq_of_continuousAt_off_coordinate_lines
    (s := Set.range (fun n : ℤ => δ * (n : ℝ)))
    (t := Set.range (fun n : ℤ => δ * (n : ℝ)))
    (Set.countable_range _) (Set.countable_range _) isOpen_interior (hKint hzK)
  · apply tendsto_finset_sum
    intro e he
    apply continuousAt_complexSegmentKernel hf.continuousOn
    · exact hinside e.1.1.1 e.1.1.2 (gridEdgeSupport_subset_cell hδ.le _ _ ·)
    · intro hzedge
      exact (gridBoundary_support_subset hδ.le hcover hinside e.1.1.2 e.2 hzedge).2 hzK
  · exact continuousAt_const.mul (hf.continuousOn.continuousAt (hΩ.mem_nhds hzΩ))
  · intro w hw hre him
    apply gridBoundary_cauchy_offLines hδ S hΩ hf hinside (interior_subset hw)
    exact ⟨fun n hn => hre ⟨n, hn.symm⟩, fun n hn => him ⟨n, hn.symm⟩⟩

/-- Existence of the universal finite contour representation, with its geometry fixed before
choosing the holomorphic function. This statement also permits an empty compact set. -/
theorem finiteCauchyRepresentation_nonempty {K Ω : Set ℂ}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    Nonempty (FiniteCauchyRepresentation K Ω) := by
  classical
  obtain ⟨δ, hδ, S, hKint, hcover, hinside⟩ := finite_grid_neighborhood hK hΩ hKΩ
  let E := {e : GridEdge S // ¬gridEdgeInternal e}
  let enum : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
  let a : Fin (Fintype.card E) → ℂ := fun i => complexGridInitial δ (enum i).1
  let b : Fin (Fintype.card E) → ℂ := fun i => complexGridTerminal δ (enum i).1
  refine ⟨{
    edgeCount := Fintype.card E
    lower := fun _ => 0
    upper := fun _ => 1
    path := fun i => AffineMap.lineMap (a i) (b i)
    density := fun i _ => b i - a i
    subset_domain := hKΩ
    path_continuous := fun _ => AffineMap.lineMap_continuous.continuousOn
    density_continuous := fun _ => continuousOn_const
    path_mem := ?_
    cauchy_identity := ?_ }⟩
  · intro i t ht
    apply gridBoundary_support_subset hδ.le hcover hinside (enum i).1.1.2 (enum i).2
    exact lineMap_mem_segment ℝ (a i) (b i) (by simpa using ht)
  · intro f hf z hz
    have hsum : (∑ i : Fin (Fintype.card E), ∫ t : ℝ in (0 : ℝ)..1,
        (f (AffineMap.lineMap (a i) (b i) t) * (b i - a i)) /
          (AffineMap.lineMap (a i) (b i) t - z)) =
        2 * (Real.pi : ℂ) * I * f z := by
      calc
        _ = ∑ i : Fin (Fintype.card E),
            gridEdgeIntegral δ (fun w => f w / (w - z)) (enum i).1 := by
          apply Finset.sum_congr rfl
          intro i hi
          apply intervalIntegral.integral_congr
          intro t ht
          exact (div_mul_eq_mul_div₀ _ _ _).symm
        _ = ∑ e : E, gridEdgeIntegral δ (fun w => f w / (w - z)) e.1 :=
          enum.sum_comp _
        _ = _ := gridBoundary_cauchy hδ S hΩ hKint hcover hinside hf hz
    rw [hsum, ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero

#print axioms continuousAt_complexSegmentKernel
#print axioms gridBoundary_cauchy
#print axioms finiteCauchyRepresentation_nonempty
end RudinRCA.Chapter13
