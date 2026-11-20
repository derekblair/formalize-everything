import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open Set Metric
namespace RudinRCA.Chapter13

/-- A closed square of the axis-parallel grid with positive mesh `δ`. -/
def gridClosedCell (δ : ℝ) (c : ℤ × ℤ) : Set ℂ :=
  Icc (δ * c.1) (δ * (c.1 + 1)) ×ℂ Icc (δ * c.2) (δ * (c.2 + 1))

theorem gridClosedCell_isCompact (δ : ℝ) (c : ℤ × ℤ) :
    IsCompact (gridClosedCell δ c) := isCompact_Icc.reProdIm isCompact_Icc

theorem exists_mem_gridClosedCell {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    ∃ c : ℤ × ℤ, z ∈ gridClosedCell δ c := by
  refine ⟨(⌊z.re / δ⌋, ⌊z.im / δ⌋), ?_⟩
  change (δ * (⌊z.re / δ⌋ : ℝ) ≤ z.re ∧ z.re ≤ δ * ((⌊z.re / δ⌋ : ℝ) + 1)) ∧
    (δ * (⌊z.im / δ⌋ : ℝ) ≤ z.im ∧ z.im ≤ δ * ((⌊z.im / δ⌋ : ℝ) + 1))
  constructor
  · exact ⟨by simpa [mul_comm] using (le_div_iff₀ hδ).mp (Int.floor_le (z.re / δ)),
      by simpa [mul_comm] using (div_le_iff₀ hδ).mp (Int.lt_floor_add_one (z.re / δ)).le⟩
  · exact ⟨by simpa [mul_comm] using (le_div_iff₀ hδ).mp (Int.floor_le (z.im / δ)),
      by simpa [mul_comm] using (div_le_iff₀ hδ).mp (Int.lt_floor_add_one (z.im / δ)).le⟩

theorem dist_le_two_mesh_of_mem_gridClosedCell {δ : ℝ} {c : ℤ × ℤ} {z w : ℂ}
    (hz : z ∈ gridClosedCell δ c) (hw : w ∈ gridClosedCell δ c) :
    dist z w ≤ 2 * δ := by
  change (_ ≤ z.re ∧ z.re ≤ _) ∧ (_ ≤ z.im ∧ z.im ≤ _) at hz
  change (_ ≤ w.re ∧ w.re ≤ _) ∧ (_ ≤ w.im ∧ w.im ≤ _) at hw
  have hre : |z.re - w.re| ≤ δ := abs_le.mpr ⟨by nlinarith [hz.1.1, hw.1.2],
    by nlinarith [hz.1.2, hw.1.1]⟩
  have him : |z.im - w.im| ≤ δ := abs_le.mpr ⟨by nlinarith [hz.2.1, hw.2.2],
    by nlinarith [hz.2.2, hw.2.1]⟩
  rw [dist_eq_norm]
  have hnorm := Complex.norm_le_abs_re_add_abs_im (z - w)
  simp only [Complex.sub_re, Complex.sub_im] at hnorm
  linarith

theorem finite_gridCells_meeting_compact {K : Set ℂ} (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ) :
    {c : ℤ × ℤ | (gridClosedCell δ c ∩ K).Nonempty}.Finite := by
  obtain ⟨M, _, hM⟩ := hK.isBounded.exists_pos_norm_le
  let lo : ℤ := ⌊-M / δ⌋ - 1
  let hi : ℤ := ⌈M / δ⌉
  apply ((Set.finite_Icc lo hi).prod (Set.finite_Icc lo hi)).subset
  rintro c ⟨z, hzc, hzK⟩
  change (_ ≤ z.re ∧ z.re ≤ _) ∧ (_ ≤ z.im ∧ z.im ≤ _) at hzc
  have hre := abs_le.mp ((Complex.abs_re_le_norm z).trans (hM z hzK))
  have him := abs_le.mp ((Complex.abs_im_le_norm z).trans (hM z hzK))
  have hcoord : ∀ (n : ℤ) (x : ℝ), -M ≤ x → x ≤ M →
      δ * n ≤ x → x ≤ δ * ((n : ℝ) + 1) → n ∈ Icc lo hi := by
    intro n x hx₁ hx₂ hn₁ hn₂
    have hu : (n : ℝ) ≤ M / δ := (le_div_iff₀ hδ).mpr (by nlinarith)
    have hl : -M / δ ≤ (n : ℝ) + 1 := (div_le_iff₀ hδ).mpr (by nlinarith)
    constructor
    · have hh := Int.floor_le (-M / δ)
      dsimp [lo]
      exact_mod_cast (show (⌊-M / δ⌋ : ℝ) - 1 ≤ (n : ℝ) by linarith)
    · exact_mod_cast hu.trans (Int.le_ceil (M / δ))
  exact ⟨hcoord c.1 z.re hre.1 hre.2 hzc.1.1 hzc.1.2,
    hcoord c.2 z.im him.1 him.2 hzc.2.1 hzc.2.2⟩

/-- A compact set has a finite grid-square cover lying inside any prescribed open neighborhood. -/
theorem finite_grid_cover {K Ω : Set ℂ} (hK : IsCompact K) (hΩ : IsOpen Ω)
    (hKΩ : K ⊆ Ω) :
    ∃ δ > 0, ∃ S : Finset (ℤ × ℤ),
      (∀ c, c ∈ S ↔ (gridClosedCell δ c ∩ K).Nonempty) ∧
      K ⊆ ⋃ c ∈ S, gridClosedCell δ c ∧
      ∀ c ∈ S, gridClosedCell δ c ⊆ Ω := by
  classical
  obtain ⟨ε, hε, hεΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let S := (finite_gridCells_meeting_compact hK hδ).toFinset
  have hS : ∀ c, c ∈ S ↔ (gridClosedCell δ c ∩ K).Nonempty := by
    intro c
    exact Set.Finite.mem_toFinset _
  refine ⟨δ, hδ, S, hS, ?_, ?_⟩
  · intro z hz
    obtain ⟨c, hc⟩ := exists_mem_gridClosedCell hδ z
    exact mem_iUnion₂.mpr ⟨c, (hS c).mpr ⟨z, hc, hz⟩, hc⟩
  · intro c hc z hz
    obtain ⟨w, hwc, hwK⟩ := (hS c).mp hc
    apply hεΩ
    apply mem_cthickening_of_dist_le z w ε K hwK
    have hd := dist_le_two_mesh_of_mem_gridClosedCell hz hwc
    dsimp [δ] at hd
    linarith

/-- The grid cover can be chosen to contain a whole neighborhood of the compact set.
The enlarged compact set used in the construction avoids any assumption that `K` has interior. -/
theorem finite_grid_neighborhood {K Ω : Set ℂ} (hK : IsCompact K) (hΩ : IsOpen Ω)
    (hKΩ : K ⊆ Ω) :
    ∃ δ > 0, ∃ S : Finset (ℤ × ℤ),
      K ⊆ interior (⋃ c ∈ S, gridClosedCell δ c) ∧
      (∀ c, (gridClosedCell δ c ∩ K).Nonempty → c ∈ S) ∧
      ∀ c ∈ S, gridClosedCell δ c ⊆ Ω := by
  obtain ⟨ε, hε, hεΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let L := cthickening ε K
  have hL : IsCompact L := hK.cthickening
  have hKL : K ⊆ interior L :=
    (self_subset_thickening hε K).trans (thickening_subset_interior_cthickening ε K)
  obtain ⟨δ, hδ, S, hS, hcover, hinside⟩ := finite_grid_cover hL hΩ hεΩ
  refine ⟨δ, hδ, S, hKL.trans (interior_mono hcover), ?_, hinside⟩
  rintro c ⟨z, hzc, hzK⟩
  exact (hS c).mpr ⟨z, hzc, interior_subset (hKL hzK)⟩

#print axioms gridClosedCell_isCompact
#print axioms exists_mem_gridClosedCell
#print axioms dist_le_two_mesh_of_mem_gridClosedCell
#print axioms finite_gridCells_meeting_compact
#print axioms finite_grid_cover
#print axioms finite_grid_neighborhood
end RudinRCA.Chapter13
