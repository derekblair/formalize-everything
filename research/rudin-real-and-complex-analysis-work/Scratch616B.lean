import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Auxiliary bounded-test extension for Rudin 6.16.
The indicator identity here is intended to be supplied by the complex
Radon–Nikodym theorem applied to `finiteLpFunctionalMeasure`.
No Lp dual representation theorem is claimed by this helper.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem lpFunctional_eq_simple_of_indicator
    (Φ : Lp ℂ p μ →L[ℂ] ℂ) {g : X → ℂ} (hg : Integrable g μ)
    (hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) = ∫ x in E, g x ∂μ)
    (f : SimpleFunc X ℂ) :
    Φ ((f.memLp_of_isFiniteMeasure p μ).toLp f) = ∫ x, f x * g x ∂μ := by
  classical
  have hint : ∀ k : SimpleFunc X ℂ, Integrable (fun x => k x * g x) μ := by
    intro k
    obtain ⟨C, hC⟩ := k.exists_forall_norm_le
    exact hg.bdd_mul k.aestronglyMeasurable (ae_of_all μ hC)
  induction f using SimpleFunc.induction with
  | @const c E hE =>
      let k : SimpleFunc X ℂ :=
        SimpleFunc.piecewise E hE (SimpleFunc.const X c) (SimpleFunc.const X 0)
      have hk : (k.memLp_of_isFiniteMeasure p μ).toLp k =
          c • indicatorConstLp p hE (measure_ne_top μ E) (1 : ℂ) := by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (k.memLp_of_isFiniteMeasure p μ),
          Lp.coeFn_smul c (indicatorConstLp p hE (measure_ne_top μ E) (1 : ℂ)),
          (indicatorConstLp_coeFn (p := p) (hs := hE)
            (hμs := measure_ne_top μ E) (c := (1 : ℂ)))] with x h₁ h₂ h₃
        rw [h₁, h₂, Pi.smul_apply, h₃]
        by_cases hx : x ∈ E <;> simp [k, hx]
      change Φ ((k.memLp_of_isFiniteMeasure p μ).toLp k) = _
      rw [hk, map_smul, hind E hE, smul_eq_mul]
      have hfun : (fun x => k x * g x) = E.indicator (fun x => c * g x) := by
        funext x
        by_cases hx : x ∈ E <;> simp [k, hx]
      change c * (∫ x in E, g x ∂μ) = ∫ x, k x * g x ∂μ
      rw [hfun, integral_indicator hE, integral_const_mul]
  | @add f k hfk hf hk =>
      have hadd : ((f + k).memLp_of_isFiniteMeasure p μ).toLp (f + k) =
          (f.memLp_of_isFiniteMeasure p μ).toLp f +
            (k.memLp_of_isFiniteMeasure p μ).toLp k := by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((f + k).memLp_of_isFiniteMeasure p μ),
          Lp.coeFn_add ((f.memLp_of_isFiniteMeasure p μ).toLp f)
            ((k.memLp_of_isFiniteMeasure p μ).toLp k),
          MemLp.coeFn_toLp (f.memLp_of_isFiniteMeasure p μ),
          MemLp.coeFn_toLp (k.memLp_of_isFiniteMeasure p μ)] with x h₁ h₂ h₃ h₄
        rw [h₁, h₂, Pi.add_apply, h₃, h₄]
        rfl
      rw [hadd, map_add, hf, hk]
      have hfun : (fun x => (f + k) x * g x) =
          (fun x => f x * g x + k x * g x) := by
        funext x
        exact add_mul (f x) (k x) (g x)
      rw [hfun, integral_add (hint f) (hint k)]

/-- Extend a functional's indicator identity to bounded measurable tests.
This does not assume that the candidate density is in the conjugate Lq space. -/
theorem lpFunctional_eq_bounded_of_indicator (hp : p ≠ ∞)
    (Φ : Lp ℂ p μ →L[ℂ] ℂ) {g : X → ℂ} (hg : Integrable g μ)
    (hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) = ∫ x in E, g x ∂μ)
    {f : X → ℂ} (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (hfLp : MemLp f p μ) :
    Φ (hfLp.toLp f) = ∫ x, f x * g x ∂μ := by
  classical
  let s : Set ℂ := range f ∪ {0}
  have h0 : (0 : ℂ) ∈ s := by simp [s]
  let F : ℕ → SimpleFunc X ℂ := fun n => SimpleFunc.approxOn f hf s 0 h0 n
  have hFp : ∀ n, MemLp (F n) p μ := fun n =>
    SimpleFunc.memLp_approxOn_range hf hfLp n
  have hLp : Tendsto (fun n => (hFp n).toLp (F n)) atTop (𝓝 (hfLp.toLp f)) :=
    SimpleFunc.tendsto_approxOn_range_Lp hp hf hfLp
  have hΦ := Φ.continuous.continuousAt.tendsto.comp hLp
  have hbound : ∀ n, ∀ x, ‖F n x‖ ≤ C + C := by
    intro n x
    exact (SimpleFunc.norm_approxOn_zero_le hf h0 x n).trans (add_le_add (hC x) (hC x))
  have hIntegral : Tendsto (fun n => ∫ x, F n x * g x ∂μ) atTop
      (𝓝 (∫ x, f x * g x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => (C + C) * ‖g x‖)
    · intro n
      exact (F n).aestronglyMeasurable.mul hg.aestronglyMeasurable
    · exact hg.norm.const_mul (C + C)
    · intro n
      exact ae_of_all μ fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound n x) (norm_nonneg _)
    · apply ae_of_all
      intro x
      have hx : f x ∈ closure s := subset_closure (by simp [s])
      exact (SimpleFunc.tendsto_approxOn hf h0 hx).mul tendsto_const_nhds
  have hEq : ∀ n, Φ ((hFp n).toLp (F n)) = ∫ x, F n x * g x ∂μ := fun n =>
    lpFunctional_eq_simple_of_indicator μ p Φ hg hind (F n)
  exact tendsto_nhds_unique (hΦ.congr' (Eventually.of_forall hEq)) hIntegral

#print axioms lpFunctional_eq_simple_of_indicator
#print axioms lpFunctional_eq_bounded_of_indicator

end RudinRCA.Chapter06
