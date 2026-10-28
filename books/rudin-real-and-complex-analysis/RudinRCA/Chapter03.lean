import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Tactic.Linarith

/-!
Chapter 3 is inventoried in `INVENTORY-CH03.md` and otherwise deferred by Stage 2.
The following declarations record a fidelity event in Definition 3.7; they are
not a claim that a numbered book item has been completed.
-/

namespace RudinRCA.Chapter03

open MeasureTheory Set
open scoped ENNReal

/-- The threshold set printed in 3.7, specialized to the zero function and zero
measure on a singleton, has no real lower bound. Thus its real infimum cannot
be used as a definition of a nonnegative norm. -/
theorem definition_3_7_zero_measure_counterexample :
    ¬ BddBelow {a : ℝ | (0 : Measure Unit) {_x | a < (0 : ℝ)} = 0} := by
  intro h
  obtain ⟨b, hb⟩ := h
  have hbad : b ≤ b - 1 := hb (by simp)
  linarith

/-- Explicit correction of 3.7: take thresholds in the complete nonnegative
extended reals. This is a correction, not a silent restatement of the book. -/
noncomputable def correctedEssentialSupremum {X : Type*} [MeasurableSpace X]
    (g : X → ℝ≥0∞) (μ : Measure X) : ℝ≥0∞ := essSup g μ

/-- The corrected threshold construction matches the measure-zero formula. -/
theorem correctedEssentialSupremum_eq_sInf {X : Type*} [MeasurableSpace X]
    (g : X → ℝ≥0∞) (μ : Measure X) :
    correctedEssentialSupremum g μ = sInf {a : ℝ≥0∞ | μ {x | a < g x} = 0} :=
  essSup_eq_sInf μ g

/-- The corrected value is the least almost-everywhere upper bound. -/
theorem correctedEssentialSupremum_le_iff {X : Type*} [MeasurableSpace X]
    (g : X → ℝ≥0∞) (μ : Measure X) (a : ℝ≥0∞) :
    correctedEssentialSupremum g μ ≤ a ↔ ∀ᵐ x ∂μ, g x ≤ a := by
  constructor
  · intro h
    filter_upwards [ENNReal.ae_le_essSup g] with x hx using hx.trans h
  · intro h
    exact essSup_le_of_ae_le a h

/-- In particular, the corrected norm convention handles zero measure. -/
theorem correctedEssentialSupremum_zero_measure {X : Type*} [MeasurableSpace X]
    (g : X → ℝ≥0∞) : correctedEssentialSupremum g (0 : Measure X) = 0 :=
  essSup_measure_zero

end RudinRCA.Chapter03
