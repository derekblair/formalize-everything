import Scratch616C
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Basic.Real.ConjExponents
import Mathlib.Tactic.Positivity

/-! The finite-measure strict-exponent bound in the proof of Rudin 6.16. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ComplexConjugate

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

theorem duality_root_bound {r s A C : ℝ} (hrs : r.HolderConjugate s)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (h : A ≤ C * A ^ r⁻¹) : A ^ s⁻¹ ≤ C := by
  by_cases hA0 : A = 0
  · simpa [hA0, Real.zero_rpow hrs.symm.inv_ne_zero] using hC
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  have hrootpos : 0 < A ^ r⁻¹ := Real.rpow_pos_of_pos hApos _
  apply (mul_le_mul_iff_left₀ hrootpos).mp
  calc
    A ^ s⁻¹ * A ^ r⁻¹ = A := by
      rw [← Real.rpow_add hApos, hrs.symm.inv_add_inv_eq_one, Real.rpow_one]
    _ ≤ C * A ^ r⁻¹ := h

theorem norm_dualityPhase_of_ne_zero {z : ℂ} (hz : z ≠ 0) : ‖dualityPhase z‖ = 1 := by
  simp [dualityPhase, norm_div, norm_ne_zero_iff.mpr hz]

variable (μ : Measure X) [IsFiniteMeasure μ] (p q : ℝ≥0∞)
variable [Fact (1 ≤ p)] [ENNReal.HolderConjugate p q]

/-- The bounded-test estimate forces a finite-measure RN density into Lq
for the strict-exponent case. Both finite exponents are explicit here;
the p = 1 endpoint is handled separately. -/
theorem lpFunctional_density_eLpNorm_le_of_finite_conjugates
    (hp : p ≠ ∞) (hq : q ≠ ∞) (Φ : Lp ℂ p μ →L[ℂ] ℂ)
    {g : X → ℂ} (hgm : Measurable g) (hg : Integrable g μ)
    (hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) = ∫ x in E, g x ∂μ) :
    eLpNorm g q μ ≤ ENNReal.ofReal ‖Φ‖ := by
  classical
  have hconj : p.toReal.HolderConjugate q.toReal :=
    ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hp0 : p ≠ 0 := (one_pos.trans_le (Fact.out : 1 ≤ p)).ne'
  have hq0 : q ≠ 0 := by
    intro hz
    have hqpos := hconj.symm.pos
    simpa [hz] using hqpos
  let E : ℕ → Set X := fun n => {x | ‖g x‖ ≤ (n : ℝ)}
  have hE : ∀ n, MeasurableSet (E n) := fun n =>
    measurableSet_le hgm.norm measurable_const
  let U : ℕ → X → ℂ := fun n => (E n).indicator g
  have hUm : ∀ n, Measurable (U n) := fun n => hgm.indicator (hE n)
  have hUnorm : ∀ n x, ‖U n x‖ ≤ (n : ℝ) := by
    intro n x
    by_cases hx : x ∈ E n
    · have hx' : ‖g x‖ ≤ (n : ℝ) := hx
      simpa only [U, indicator_of_mem hx] using hx'
    · simp [U, hx]
  have hUq : ∀ n, MemLp (U n) q μ := fun n =>
    MemLp.of_bound (hUm n).aestronglyMeasurable (n : ℝ) (ae_of_all μ (hUnorm n))
  let F : ℕ → X → ℂ := fun n x =>
    Complex.ofReal (‖U n x‖ ^ (q.toReal - 1)) * dualityPhase (U n x)
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    exact ((hUm n).norm.pow_const _).complex_ofReal.mul
      (measurable_dualityPhase.comp (hUm n))
  have hFnorm : ∀ n x, ‖F n x‖ = ‖U n x‖ ^ (q.toReal - 1) := by
    intro n x
    by_cases hx : U n x = 0
    · simp [F, hx, dualityPhase, Real.zero_rpow hconj.symm.sub_one_ne_zero]
    · dsimp only [F]
      rw [norm_mul, norm_dualityPhase_of_ne_zero hx, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have hFbound : ∀ n x, ‖F n x‖ ≤ (n : ℝ) ^ (q.toReal - 1) := by
    intro n x
    rw [hFnorm]
    exact Real.rpow_le_rpow (norm_nonneg _) (hUnorm n x) hconj.symm.sub_one_pos.le
  have hFp : ∀ n, MemLp (F n) p μ := fun n =>
    MemLp.of_bound (hFm n).aestronglyMeasurable ((n : ℝ) ^ (q.toReal - 1))
      (ae_of_all μ (hFbound n))
  have hpower : ∀ n x, ‖F n x‖ ^ p.toReal = ‖U n x‖ ^ q.toReal := by
    intro n x
    rw [hFnorm, ← Real.rpow_mul (norm_nonneg _), hconj.symm.sub_one_mul_conj]
  have hprod : ∀ n x, F n x * g x = Complex.ofReal (‖U n x‖ ^ q.toReal) := by
    intro n x
    by_cases hx : x ∈ E n
    · simp only [F, U, indicator_of_mem hx]
      rw [mul_assoc, dualityPhase_mul, ← Complex.ofReal_mul]
      congr 1
      have h := Real.rpow_add_one' (norm_nonneg (g x))
        (y := q.toReal - 1) (by simpa using hconj.symm.ne_zero)
      simpa only [sub_add_cancel] using h.symm
    · simp [F, U, hx, dualityPhase, Real.zero_rpow hconj.symm.ne_zero]
  have hUbound : ∀ n, eLpNorm (U n) q μ ≤ ENNReal.ofReal ‖Φ‖ := by
    intro n
    let integralMass : ℝ := ∫ x, ‖U n x‖ ^ q.toReal ∂μ
    have hI : 0 ≤ integralMass := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
    have hPhi : Φ ((hFp n).toLp (F n)) = (integralMass : ℂ) := by
      rw [lpFunctional_eq_bounded_of_indicator μ p hp Φ hg hind (hFm n)
        ((n : ℝ) ^ (q.toReal - 1)) (hFbound n) (hFp n)]
      simp_rw [hprod n]
      exact integral_complex_ofReal
    have hFnormLp : ‖(hFp n).toLp (F n)‖ = integralMass ^ p.toReal⁻¹ := by
      rw [Lp.norm_toLp, (hFp n).eLpNorm_eq_integral_rpow_norm hp0 hp,
        ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg
          (fun x => Real.rpow_nonneg (norm_nonneg _) _)) _)]
      congr 1
      apply integral_congr_ae
      exact ae_of_all μ (hpower n)
    have hineq : integralMass ≤ ‖Φ‖ * integralMass ^ p.toReal⁻¹ := by
      have h := Φ.le_opNorm ((hFp n).toLp (F n))
      rw [hPhi, Complex.norm_real, Real.norm_of_nonneg hI, hFnormLp] at h
      exact h
    have hroot := duality_root_bound hconj hI (norm_nonneg Φ) hineq
    rw [(hUq n).eLpNorm_eq_integral_rpow_norm hq0 hq]
    exact ENNReal.ofReal_le_ofReal hroot
  apply Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ)) (Eventually.of_forall hUbound)
    (fun n => (hUm n).aestronglyMeasurable) hg.aestronglyMeasurable
  apply ae_of_all
  intro x
  have hevent : (fun n : ℕ => U n x) =ᶠ[atTop] (fun _ => g x) := by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖g x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    apply indicator_of_mem
    exact hN.le.trans (by exact_mod_cast hn)
  exact tendsto_const_nhds.congr' hevent.symm

theorem lpFunctional_density_memLp_of_finite_conjugates
    (hp : p ≠ ∞) (hq : q ≠ ∞) (Φ : Lp ℂ p μ →L[ℂ] ℂ)
    {g : X → ℂ} (hgm : Measurable g) (hg : Integrable g μ)
    (hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) = ∫ x in E, g x ∂μ) :
    MemLp g q μ :=
  (lpFunctional_density_eLpNorm_le_of_finite_conjugates μ p q hp hq Φ hgm hg hind).trans_lt
    ENNReal.ofReal_lt_top

#print axioms duality_root_bound
#print axioms norm_dualityPhase_of_ne_zero
#print axioms lpFunctional_density_eLpNorm_le_of_finite_conjugates
#print axioms lpFunctional_density_memLp_of_finite_conjugates

end RudinRCA.Chapter06
