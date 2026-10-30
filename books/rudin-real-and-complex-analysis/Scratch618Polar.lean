import RudinRCA.Chapter06
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.Normed.Operator.Mul

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace RudinRCA.Chapter06
variable {X : Type*} [MeasurableSpace X]

/-- The native vector integral agrees with the polar-density definition in 6.18.
This statement works for every choice of a measurable unit polar density. -/
theorem vectorIntegral_eq_polar (c : ComplexMeasure X) (h : X → ℂ)
    (hm : Measurable h) (hn : ∀ x, ‖h x‖ = 1)
    (hi : Integrable h c.variation) (hr : c.variation.withDensityᵥ h = c)
    {f : X → ℂ} (hf : Integrable f c.variation) :
    (∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; c]) =
      ∫ x, f x * h x ∂c.variation := by
  let B := ContinuousLinearMap.mul ℝ ℂ
  have hb : ∀ᵐ x ∂c.variation, ‖h x‖ ≤ 1 := ae_of_all _ fun x ↦ (hn x).le
  have htop : MemLp h ∞ c.variation := memLp_top_of_bound hm.aestronglyMeasurable 1 hb
  let H : Lp ℂ ∞ c.variation := htop.toLp h
  have hH : (H : X → ℂ) =ᵐ[c.variation] h := htop.coeFn_toLp
  have hmul {f : X → ℂ} (hf : Integrable f c.variation) :
      Integrable (fun x ↦ f x * h x) c.variation :=
    hf.mul_bdd hm.aestronglyMeasurable hb
  have hcont : Continuous (fun f : Lp ℂ 1 c.variation ↦ ∫ x, f x * h x ∂c.variation) := by
    have heq : (fun f : Lp ℂ 1 c.variation ↦ ∫ x, f x * h x ∂c.variation) =
        fun f ↦ B.lpPairing c.variation ∞ 1 H f := by
      funext f
      rw [B.lpPairing_eq_integral]
      apply integral_congr_ae
      filter_upwards [hH] with x hx
      simp [B, hx, mul_comm]
    rw [heq]
    exact (B.lpPairing c.variation ∞ 1 H).continuous
  refine Integrable.induction
    (P := fun f ↦ (∫ᵛ x, f x ∂[B; c]) = ∫ x, f x * h x ∂c.variation)
    ?_ ?_ ?_ ?_ hf
  · intro z E hE _
    rw [VectorMeasure.integral_indicator_const z hE]
    change z * c E = _
    have hcE : c E = ∫ x in E, h x ∂c.variation := by
      calc
        c E = (c.variation.withDensityᵥ h) E :=
          congrArg (fun v : ComplexMeasure X ↦ v E) hr.symm
        _ = ∫ x in E, h x ∂c.variation := withDensityᵥ_apply hi hE
    rw [hcE]
    have hfun : (fun x ↦ E.indicator (fun _ ↦ z) x * h x) =
        E.indicator (fun x ↦ z * h x) := by
      funext x
      by_cases hx : x ∈ E <;> simp [hx]
    rw [hfun, integral_indicator hE, integral_const_mul]
  · intro f g _ hf hg hfe hge
    rw [VectorMeasure.integral_add hf hg, hfe, hge]
    simp only [Pi.add_apply, add_mul]
    exact (integral_add (hmul hf) (hmul hg)).symm
  · exact isClosed_eq VectorMeasure.continuous_integral hcont
  · intro f g hfg _ heq
    rw [← VectorMeasure.integral_congr_ae hfg, heq]
    apply integral_congr_ae
    filter_upwards [hfg] with x hx using congrArg (· * h x) hx

#print axioms vectorIntegral_eq_polar
end RudinRCA.Chapter06
