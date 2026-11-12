import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic.FieldSimp

/-! Compile after RungeRationalWitness. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RudinRCA.Chapter13

/-- Translation of the original variable corresponds to this regular change of inverse chart. -/
def translatedInverseChart (b w : ℂ) : ℂ := w / (1 + b * w)

theorem translatedInverseChart_analyticAt_zero (b : ℂ) :
    AnalyticAt ℂ (translatedInverseChart b) 0 :=
  analyticAt_id.div (analyticAt_const.add (analyticAt_const.mul analyticAt_id)) (by simp)

theorem translatedInverseChart_inv (b : ℂ) {w : ℂ} (hw : w ≠ 0)
    (hd : 1 + b * w ≠ 0) : (translatedInverseChart b w)⁻¹ = b + w⁻¹ := by
  dsimp [translatedInverseChart]
  field_simp
  ring

theorem translatedInverseChart_tendsto_nhdsNE (b : ℂ) :
    Tendsto (translatedInverseChart b) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
  have hcont := (translatedInverseChart_analyticAt_zero b).continuousAt
  have hden : ∀ᶠ w : ℂ in 𝓝 0, 1 + b * w ≠ 0 :=
    (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).eventually_ne (by simp)
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa [translatedInverseChart] using hcont.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin, hden.filter_mono inf_le_left] with w hw hd
    exact div_ne_zero hw hd

/-- Removability at infinity is unchanged by finite translation. The supplied extension agrees
with the translated inverse expression at every nonzero point, not merely as a punctured germ. -/
theorem exists_translated_inverse_extension {R : ℂ → ℂ}
    (hR : RungeRemovableAtInfinity R) (b : ℂ) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ ∀ w ≠ 0, G w = R (b + w⁻¹) := by
  obtain ⟨g, hg, hgeq⟩ := hR
  let G : ℂ → ℂ := Function.update (fun w => R (b + w⁻¹)) 0 (g 0)
  have hden : ∀ᶠ w : ℂ in 𝓝 0, 1 + b * w ≠ 0 :=
    (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).eventually_ne (by simp)
  have hcomp : AnalyticAt ℂ (g ∘ translatedInverseChart b) 0 := by
    apply hg.comp
    · exact translatedInverseChart_analyticAt_zero b
    · simp [translatedInverseChart]
  have heq : G =ᶠ[𝓝 (0 : ℂ)] g ∘ translatedInverseChart b := by
    rw [← nhdsNE_sup_pure (0 : ℂ), Filter.eventually_sup]
    constructor
    · filter_upwards [self_mem_nhdsWithin, hden.filter_mono inf_le_left,
        (translatedInverseChart_tendsto_nhdsNE b).eventually hgeq] with w hw hd hgw
      change w ≠ 0 at hw
      simpa only [G, Function.update_of_ne hw, Function.comp_apply,
        translatedInverseChart_inv b hw hd] using hgw
    · simp [G, translatedInverseChart]
  exact ⟨G, hcomp.congr_of_eventuallyEq heq,
    fun w hw => Function.update_of_ne hw _ _⟩

/-- Away from zero, the extension inherits analyticity from the rational function at the
corresponding finite point. At zero, the preceding removable-singularity lemma applies. -/
theorem translated_inverse_extension_analyticAt {R G : ℂ → ℂ} {b w : ℂ}
    (hG0 : AnalyticAt ℂ G 0) (hG : ∀ w ≠ 0, G w = R (b + w⁻¹))
    (hR : w ≠ 0 → AnalyticAt ℂ R (b + w⁻¹)) : AnalyticAt ℂ G w := by
  by_cases hw : w = 0
  · simpa [hw] using hG0
  · have hcomp : AnalyticAt ℂ (fun z => R (b + z⁻¹)) w :=
      (hR hw).comp (analyticAt_const.add (analyticAt_id.inv hw))
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hw] with z hz
    exact hG z hz

#print axioms translatedInverseChart_analyticAt_zero
#print axioms translatedInverseChart_inv
#print axioms translatedInverseChart_tendsto_nhdsNE
#print axioms exists_translated_inverse_extension
#print axioms translated_inverse_extension_analyticAt
end RudinRCA.Chapter13
