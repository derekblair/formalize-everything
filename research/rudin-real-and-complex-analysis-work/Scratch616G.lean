import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! Gluing compatible local densities along a sigma-finite exhaustion. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

/-- Uniformly Lq-bounded compatible local densities glue to a global density.
Compatibility is expressed on every pairwise overlap modulo a null set. -/
theorem sigmaFinite_glue_densities (μ : Measure X) [SigmaFinite μ] (q : ℝ≥0∞)
    (g : ℕ → X → ℂ) (hgm : ∀ n, Measurable (g n))
    (hcompat : ∀ n m, ∀ᵐ x ∂μ,
      x ∈ spanningSets μ n → x ∈ spanningSets μ m → g n x = g m x)
    (C : ℝ≥0∞)
    (hbound : ∀ n, eLpNorm ((spanningSets μ n).indicator (g n)) q μ ≤ C) :
    ∃ G : X → ℂ, Measurable G ∧ eLpNorm G q μ ≤ C ∧
      ∀ n, G =ᵐ[μ.restrict (spanningSets μ n)] g n := by
  let G : X → ℂ := fun x => g (spanningSetsIndex μ x) x
  have hGm : Measurable G := by
    have hfamily : Measurable (fun z : X × ℕ => g z.2 z.1) :=
      measurable_from_prod_countable_left hgm
    exact hfamily.comp (measurable_id.prodMk (measurableSet_spanningSetsIndex μ))
  have hlocal : ∀ n, G =ᵐ[μ.restrict (spanningSets μ n)] g n := by
    intro n
    apply (ae_restrict_iff' (measurableSet_spanningSets μ n)).mpr
    have hall : ∀ᵐ x ∂μ, ∀ m, x ∈ spanningSets μ n →
        x ∈ spanningSets μ m → g n x = g m x := ae_all_iff.mpr (hcompat n)
    filter_upwards [hall] with x hx
    intro hxn
    exact (hx (spanningSetsIndex μ x) hxn (mem_spanningSetsIndex μ x)).symm
  have hboundG : ∀ n, eLpNorm ((spanningSets μ n).indicator G) q μ ≤ C := by
    intro n
    rw [eLpNorm_congr_ae ((ae_eq_restrict_iff_indicator_ae_eq
      (measurableSet_spanningSets μ n)).mp (hlocal n))]
    exact hbound n
  have hGbound : eLpNorm G q μ ≤ C := by
    apply Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ)) (Eventually.of_forall hboundG)
      (fun n => (hGm.indicator (measurableSet_spanningSets μ n)).aestronglyMeasurable)
      hGm.aestronglyMeasurable
    apply ae_of_all
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_mem_spanningSets μ x] with n hn
    simp only [indicator_of_mem hn]
  exact ⟨G, hGm, hGbound, hlocal⟩

#print axioms sigmaFinite_glue_densities

end RudinRCA.Chapter06
