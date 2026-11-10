import Scratch616E
import Mathlib.MeasureTheory.Measure.Continuity

/-! Finite-indicator density and convergence along sigma-finite spanning sets. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology symmDiff

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
variable [ENNReal.HolderConjugate p q]

/-- Equality on finite-measure indicators determines a bounded Lp functional
for arbitrary positive measures when p is finite. -/
theorem lpFunctional_eq_of_finite_indicator (hp : p ≠ ∞)
    (Φ : Lp ℂ p μ →L[ℂ] ℂ) (G : Lp ℂ q μ)
    (hind : ∀ E (hE : MeasurableSet E) (hμE : μ E ≠ ∞),
      Φ (indicatorConstLp p hE hμE 1) = ∫ x in E, G x ∂μ) :
    ∀ f : Lp ℂ p μ, Φ f = ∫ x, f x * G x ∂μ := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  let Ψ : Lp ℂ p μ →L[ℂ] ℂ := B.lpPairing μ q p G
  have hΨ : ∀ f, Ψ f = ∫ x, f x * G x ∂μ := by
    intro f
    simpa only [Ψ, B, ContinuousLinearMap.mul_apply', mul_comm] using
      B.lpPairing_eq_integral G f
  have hmaps : ∀ f : Lp ℂ p μ, Φ f = Ψ f := by
    apply Lp.induction hp (fun f => Φ f = Ψ f)
    · intro c E hE hμE
      change Φ (indicatorConstLp p hE hμE.ne c) = Ψ (indicatorConstLp p hE hμE.ne c)
      have hsmul : indicatorConstLp p hE hμE.ne c =
          c • indicatorConstLp p hE hμE.ne (1 : ℂ) := by
        apply Lp.ext
        filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hE) (hμs := hμE.ne) (c := c),
          Lp.coeFn_smul c (indicatorConstLp p hE hμE.ne (1 : ℂ)),
          indicatorConstLp_coeFn (p := p) (hs := hE) (hμs := hμE.ne) (c := (1 : ℂ))]
          with x h₁ h₂ h₃
        rw [h₁, h₂, Pi.smul_apply, h₃]
        by_cases hx : x ∈ E <;> simp [hx]
      rw [hsmul, map_smul, map_smul, hind E hE hμE.ne, hΨ,
        integral_indicatorConstLp_mul μ p hE hμE.ne]
    · intro f g hf hg hfg hΦf hΦg
      rw [map_add, map_add, hΦf, hΦg]
    · exact isClosed_eq Φ.continuous Ψ.continuous
  intro f
  exact (hmaps f).trans (hΨ f)

variable [SigmaFinite μ]

/-- Indicators of the intersections with a sigma-finite exhaustion converge
in Lp to any fixed finite-measure indicator. -/
theorem tendsto_indicatorConstLp_spanningSets (hp : p ≠ ∞)
    {E : Set X} (hE : MeasurableSet E) (hμE : μ E ≠ ∞) :
    Tendsto (fun n => indicatorConstLp p (hE.inter (measurableSet_spanningSets μ n))
      (ne_top_of_le_ne_top hμE (measure_mono inter_subset_left)) (1 : ℂ)) atTop
      (𝓝 (indicatorConstLp p hE hμE (1 : ℂ))) := by
  let R : ℕ → Set X := fun n => E \ (E ∩ spanningSets μ n)
  have hRm : ∀ n, MeasurableSet (R n) := fun n =>
    hE.diff (hE.inter (measurableSet_spanningSets μ n))
  have hRanti : Antitone R := by
    intro n m hnm x hx
    exact ⟨hx.1, fun hy => hx.2 ⟨hy.1, spanningSets_mono hnm hy.2⟩⟩
  have hRinter : (⋂ n, R n) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxE := (mem_iInter.mp hx 0).1
    exact (mem_iInter.mp hx (spanningSetsIndex μ x)).2 ⟨hxE, mem_spanningSetsIndex μ x⟩
  have hlim : Tendsto (fun n => μ (R n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hRm n).nullMeasurableSet)
      hRanti ⟨0, ne_top_of_le_ne_top hμE (measure_mono diff_subset)⟩
    simpa only [hRinter, measure_empty, Function.comp_def] using h
  apply tendsto_indicatorConstLp_set hp
  simpa only [symmDiff_of_le (inter_subset_left : E ∩ spanningSets μ _ ⊆ E)] using hlim

#print axioms lpFunctional_eq_of_finite_indicator
#print axioms tendsto_indicatorConstLp_spanningSets

end RudinRCA.Chapter06
