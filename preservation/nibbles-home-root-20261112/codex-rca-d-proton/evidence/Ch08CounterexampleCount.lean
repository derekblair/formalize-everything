module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Count

public section

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RudinRCA.Chapter08

/-- 8.9(b), diagonal of the unit square. Both integrals use restrictions to [0,1],
which is the ambient-real representation of integration over the book's interval. -/
def diagonalIndicator (x y : ℝ) : ℝ≥0∞ := if x = y then 1 else 0

lemma diagonalIndicator_section (x : ℝ) :
    diagonalIndicator x = ({x} : Set ℝ).indicator (fun _ => (1 : ℝ≥0∞)) := by
  funext y
  simp only [diagonalIndicator, Set.indicator_apply, Set.mem_singleton_iff]
  split_ifs <;> simp_all

lemma diagonalIndicator_symm (x y : ℝ) : diagonalIndicator x y = diagonalIndicator y x := by
  simp only [diagonalIndicator, eq_comm]

lemma diagonalIndicator_measurable : Measurable (fun z : ℝ × ℝ => diagonalIndicator z.1 z.2) := by
  change Measurable (fun z : ℝ × ℝ => if z.1 = z.2 then (1 : ℝ≥0∞) else 0)
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const measurable_const

lemma diagonal_lebesgue_section (y : ℝ) :
    ∫⁻ x, diagonalIndicator x y ∂volume.restrict (Icc (0 : ℝ) 1) = 0 := by
  simp_rw [diagonalIndicator_symm _ y, diagonalIndicator_section]
  rw [lintegral_indicator (measurableSet_singleton y)]
  simp [Measure.restrict_apply, measurableSet_singleton]

lemma diagonal_count_section {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∫⁻ y, diagonalIndicator x y ∂Measure.count.restrict (Icc (0 : ℝ) 1) = 1 := by
  rw [diagonalIndicator_section, lintegral_indicator (measurableSet_singleton x)]
  simp [Measure.restrict_apply, measurableSet_singleton, hx]

/-- 8.9(b): two finite unequal iterated integrals of a nonnegative measurable function. -/
theorem counting_measure_counterexample :
    (∫⁻ y, ∫⁻ x, diagonalIndicator x y ∂volume.restrict (Icc (0 : ℝ) 1)
      ∂Measure.count.restrict (Icc (0 : ℝ) 1)) = 0 ∧
    (∫⁻ x, ∫⁻ y, diagonalIndicator x y ∂Measure.count.restrict (Icc (0 : ℝ) 1)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = 1 := by
  constructor
  · simp_rw [diagonal_lebesgue_section, lintegral_zero]
  · calc
      _ = ∫⁻ _x, (1 : ℝ≥0∞) ∂volume.restrict (Icc (0 : ℝ) 1) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        exact diagonal_count_section hx
      _ = 1 := by simp

/-- The counting measure in 8.9(b) is not sigma-finite, as the counterexample itself proves. -/
theorem interval_count_not_sigmaFinite :
    ¬ SigmaFinite (Measure.count.restrict (Icc (0 : ℝ) 1)) := by
  intro h
  letI := h
  have heq := lintegral_lintegral_swap (f := diagonalIndicator)
    (μ := volume.restrict (Icc (0 : ℝ) 1))
    (ν := Measure.count.restrict (Icc (0 : ℝ) 1))
    diagonalIndicator_measurable.aemeasurable
  rw [counting_measure_counterexample.1, counting_measure_counterexample.2] at heq
  exact one_ne_zero heq

end RudinRCA.Chapter08
