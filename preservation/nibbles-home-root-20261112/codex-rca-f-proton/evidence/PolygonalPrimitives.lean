import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.Clopen

/- Prerequisites: PolygonalCyclePackage.lean and PolygonalRegularity.lean,
   plus PrimitiveCurveIntegral.lean for the exact piecewise-C¹ predicate.
   This proves the converse 13.11(f)→(g) using genuine path integrals. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open RudinRCA.Chapter13Scratch

namespace RudinRCA.Chapter13

theorem isPolygonalPath_symm {a b : ℂ} {γ : Path a b} (hγ : IsPolygonalPath γ) :
    IsPolygonalPath γ.symm := by
  induction hγ with
  | refl a => simpa using IsPolygonalPath.refl a
  | segment a b => simpa using IsPolygonalPath.segment b a
  | trans hγ hδ ihγ ihδ =>
    rw [Path.trans_symm]
    exact ihδ.trans ihγ
  | cast hc hd hγ ih =>
    rw [← Path.cast_symm]
    exact IsPolygonalPath.cast hd hc ih

/-- Continuous one-forms are integrable on every finite polygonal path. -/
theorem curveIntegrable_of_isPolygonalPath {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : ContinuousOn f Ω) {a b : ℂ} {γ : Path a b}
    (hγ : IsPolygonalPath γ) (hγΩ : Set.range γ ⊆ Ω) :
    CurveIntegrable (fun z ↦ ContinuousLinearMap.mul ℂ ℂ (f z)) γ := by
  induction hγ with
  | refl a => exact CurveIntegrable.refl _ _
  | segment a b =>
    exact curveIntegrable_segment_of_continuousOn hf (by simpa using hγΩ)
  | trans hγ hδ ihγ ihδ =>
    rw [Path.trans_range] at hγΩ
    exact (ihγ (subset_union_left.trans hγΩ)).trans (ihδ (subset_union_right.trans hγΩ))
  | cast hc hd hγ ih =>
    rw [curveIntegrable_cast_iff]
    exact ih hγΩ

/-- In an open connected planar set, any two points are joined by an actual
    finite concatenation of straight segments lying in that set. -/
theorem exists_polygonal_path_in_open_connected {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) {a b : ℂ} (ha : a ∈ Ω) (hb : b ∈ Ω) :
    ∃ γ : Path a b, IsPolygonalPath γ ∧ Set.range γ ⊆ Ω := by
  let R : Set ℂ := {z | ∃ γ : Path a z, IsPolygonalPath γ ∧ Set.range γ ⊆ Ω}
  have hRΩ : R ⊆ Ω := by
    rintro z ⟨γ, hγ, hγΩ⟩
    exact hγΩ γ.target_mem_range
  have haR : a ∈ R := ⟨Path.refl a, IsPolygonalPath.refl a, by simpa using ha⟩
  have hRopen : IsOpen R := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds (hRΩ hz))
    apply Filter.mem_of_superset (Metric.ball_mem_nhds z hε)
    intro w hw
    obtain ⟨γ, hγ, hγΩ⟩ := hz
    refine ⟨γ.trans (Path.segment z w), hγ.trans (IsPolygonalPath.segment z w), ?_⟩
    rw [Path.trans_range, Path.range_segment]
    exact union_subset hγΩ (((convex_ball z ε).segment_subset (Metric.mem_ball_self hε) hw).trans hball)
  have hcompl : IsOpen (Ω \ R) := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hz.1)
    apply Filter.mem_of_superset (Metric.ball_mem_nhds z hε)
    intro w hw
    refine ⟨hball hw, ?_⟩
    rintro ⟨γ, hγ, hγΩ⟩
    apply hz.2
    refine ⟨γ.trans (Path.segment w z), hγ.trans (IsPolygonalPath.segment w z), ?_⟩
    rw [Path.trans_range, Path.range_segment]
    exact union_subset hγΩ (((convex_ball z ε).segment_subset hw (Metric.mem_ball_self hε)).trans hball)
  have hsub : Ω ⊆ R := hconn.subset_left_of_subset_union hRopen hcompl
    (disjoint_sdiff_right) (by intro z hz; by_cases h : z ∈ R <;> simp_all)
    ⟨a, ha, haR⟩
  exact hsub hb

/-- Vanishing closed polygonal integrals makes integration independent of
    the chosen polygonal path between two endpoints. -/
theorem polygonal_integral_eq_of_closed_integrals_zero {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : ContinuousOn f Ω)
    (hzero : ∀ (a : ℂ) (γ : Path a a), IsPolygonalPath γ → Set.range γ ⊆ Ω →
      curveIntegral (fun z ↦ ContinuousLinearMap.mul ℂ ℂ (f z)) γ = 0)
    {a b : ℂ} (γ δ : Path a b) (hγ : IsPolygonalPath γ) (hδ : IsPolygonalPath δ)
    (hγΩ : Set.range γ ⊆ Ω) (hδΩ : Set.range δ ⊆ Ω) :
    curveIntegral (fun z ↦ ContinuousLinearMap.mul ℂ ℂ (f z)) γ =
      curveIntegral (fun z ↦ ContinuousLinearMap.mul ℂ ℂ (f z)) δ := by
  have hloop := hzero a (γ.trans δ.symm) (hγ.trans (isPolygonalPath_symm hδ)) (by
    rw [Path.trans_range, Path.symm_range]
    exact union_subset hγΩ hδΩ)
  rw [curveIntegral_trans (curveIntegrable_of_isPolygonalPath hf hγ hγΩ)
    (curveIntegrable_of_isPolygonalPath hf (isPolygonalPath_symm hδ)
      (by simpa using hδΩ)), curveIntegral_symm] at hloop
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hloop)

/-- Path-integral construction of a primitive from vanishing closed polygonal
    integrals; only continuity of the integrand is required. -/
theorem exists_primitive_of_zero_closed_polygonal_integrals {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hconn : IsConnected Ω) {f : ℂ → ℂ} (hf : ContinuousOn f Ω)
    (hzero : ∀ (a : ℂ) (γ : Path a a), IsPolygonalPath γ → Set.range γ ⊆ Ω →
      curveIntegral (fun z ↦ ContinuousLinearMap.mul ℂ ℂ (f z)) γ = 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧ ∀ z ∈ Ω, deriv F z = f z := by
  classical
  obtain ⟨a, ha⟩ := hconn.nonempty
  have hpaths : ∀ z : Ω, ∃ γ : Path a z, IsPolygonalPath γ ∧ Set.range γ ⊆ Ω :=
    fun z ↦ exists_polygonal_path_in_open_connected hΩ hconn.isPreconnected ha z.property
  choose γ hγ hγΩ using hpaths
  let ω : ℂ → ℂ →L[ℂ] ℂ := fun z ↦ ContinuousLinearMap.mul ℂ ℂ (f z)
  let F : ℂ → ℂ := fun z ↦ if hz : z ∈ Ω then curveIntegral ω (γ ⟨z, hz⟩) else 0
  have hω : ContinuousOn ω Ω :=
    (ContinuousLinearMap.mul ℂ ℂ).continuous.comp_continuousOn hf
  have hder : ∀ z ∈ Ω, HasDerivAt F (f z) z := by
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hz)
    have hlocal : F =ᶠ[𝓝 z] (fun w ↦ F z + curveIntegral ω (Path.segment z w)) := by
      filter_upwards [Metric.ball_mem_nhds z hε] with w hw
      have hwΩ := hball hw
      have hseg : Set.range (Path.segment z w) ⊆ Ω := by
        rw [Path.range_segment]
        exact ((convex_ball z ε).segment_subset (Metric.mem_ball_self hε) hw).trans hball
      have hint := polygonal_integral_eq_of_closed_integrals_zero hf hzero
        (γ ⟨w, hwΩ⟩) ((γ ⟨z, hz⟩).trans (Path.segment z w))
        (hγ _) ((hγ _).trans (IsPolygonalPath.segment z w)) (hγΩ _) (by
          rw [Path.trans_range]
          exact union_subset (hγΩ _) hseg)
      rw [curveIntegral_trans (curveIntegrable_of_isPolygonalPath hf (hγ _) (hγΩ _))
        (curveIntegrable_of_isPolygonalPath hf (IsPolygonalPath.segment z w) hseg)] at hint
      simpa only [F, dif_pos hz, dif_pos hwΩ] using hint
    have hcont : ∀ᶠ w in 𝓝 z, ContinuousAt ω w := by
      filter_upwards [hΩ.mem_nhds hz] with w hw
      exact hω.continuousAt (hΩ.mem_nhds hw)
    have hsegder := (HasFDerivAt.curveIntegral_segment_source' hcont).hasDerivAt
    have hsumder : HasDerivAt (fun w ↦ F z + curveIntegral ω (Path.segment z w)) (f z) z := by
      simpa only [ω, ContinuousLinearMap.mul_apply', mul_one] using hsegder.const_add (F z)
    exact hsumder.congr_of_eventuallyEq hlocal
  exact ⟨F, fun z hz ↦ (hder z hz).differentiableAt.differentiableWithinAt,
    fun z hz ↦ (hder z hz).deriv⟩

/-- Rudin 13.11(f)→(g), with the full finite piecewise-C¹ path class. -/
theorem exists_primitive_of_zero_closed_piecewise_integrals {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hconn : IsConnected Ω) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hzero : ∀ (a : ℂ) (γ : Path a a), IsPiecewiseC1Path γ →
      (∀ t, γ t ∈ Ω) → curveIntegral (fun z ↦ f z • ContinuousLinearMap.id ℂ ℂ) γ = 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧ ∀ z ∈ Ω, deriv F z = f z := by
  apply exists_primitive_of_zero_closed_polygonal_integrals hΩ hconn hf.continuousOn
  intro a γ hγ hγΩ
  have heq : (fun z ↦ f z • ContinuousLinearMap.id ℂ ℂ) =
      (fun z ↦ ContinuousLinearMap.mul ℂ ℂ (f z)) := by
    funext z
    ext w
    simp
  rw [← heq]
  exact hzero a γ (isPiecewiseC1Path_of_isPolygonalPath hγ)
    (fun t ↦ hγΩ (mem_range_self t))

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.isPolygonalPath_symm
#print axioms RudinRCA.Chapter13.curveIntegrable_of_isPolygonalPath
#print axioms RudinRCA.Chapter13.exists_polygonal_path_in_open_connected
#print axioms RudinRCA.Chapter13.polygonal_integral_eq_of_closed_integrals_zero
#print axioms RudinRCA.Chapter13.exists_primitive_of_zero_closed_polygonal_integrals
#print axioms RudinRCA.Chapter13.exists_primitive_of_zero_closed_piecewise_integrals
