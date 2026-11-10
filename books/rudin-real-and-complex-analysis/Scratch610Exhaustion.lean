import Scratch610Discussion

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace RCA610Discussion

variable {X : Type*} [MeasurableSpace X]

/-- The sigma-finite positive extension of 6.10 admits one increasing measurable
exhaustion that is finite for both measures; the density is integrable on every
member of that exhaustion. -/
theorem sigmaFinite_positive_decomposition_with_exhaustion (ν μ : Measure X)
    [SigmaFinite ν] [SigmaFinite μ] :
    ∃ s : Measure X, ∃ h : X → ℝ, ∃ A : ℕ → Set X,
      Measurable h ∧ (∀ x, 0 ≤ h x) ∧ s ⟂ₘ μ ∧
      ν = s + μ.withDensity (fun x ↦ ENNReal.ofReal (h x)) ∧
      Monotone A ∧ (∀ n, MeasurableSet (A n)) ∧ (⋃ n, A n) = univ ∧
      ∀ n, μ (A n) < ∞ ∧ ν (A n) < ∞ ∧ IntegrableOn h (A n) μ := by
  obtain ⟨s, h, hm, hpos, hsing, hdecomp, hlocal, _⟩ :=
    sigmaFinite_positive_decomposition ν μ
  refine ⟨s, h, spanningSets (μ + ν), hm, hpos, hsing, hdecomp,
    monotone_spanningSets _, measurableSet_spanningSets _, iUnion_spanningSets _, ?_⟩
  intro n
  have hμ : μ (spanningSets (μ + ν) n) < ∞ :=
    (self_le_add_right _ _).trans_lt (measure_spanningSets_lt_top (μ + ν) n)
  have hν : ν (spanningSets (μ + ν) n) < ∞ :=
    (self_le_add_left _ _).trans_lt (measure_spanningSets_lt_top (μ + ν) n)
  exact ⟨hμ, hν, hlocal _ hν.ne⟩

#print axioms sigmaFinite_positive_decomposition_with_exhaustion

end RCA610Discussion
