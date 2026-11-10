import Scratch618Final
import Scratch619Density
import Scratch619Clip
import Scratch619Regular
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace RudinRCA.Chapter06

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X]

private theorem integrable_conj_polar (c : ComplexMeasure X) {h : X → ℂ}
    (hm : Measurable h) (hn : ∀ x, ‖h x‖ = 1) :
    Integrable (fun x ↦ star (h x)) c.variation := by
  apply Integrable.of_bound (continuous_star.measurable.comp hm).aestronglyMeasurable 1
  exact ae_of_all _ fun x ↦ by simp [hn]

/-- The elementary estimate used in the uniqueness and norm arguments of 6.19. -/
theorem polar_mass_le_integral_add_error (c : ComplexMeasure X) (h : X → ℂ)
    (hm : Measurable h) (hn : ∀ x, ‖h x‖ = 1)
    (hi : Integrable h c.variation) (hr : c.variation.withDensityᵥ h = c)
    {g : X → ℂ} (hg : Integrable g c.variation) :
    c.variation.real univ ≤ ‖complexIntegral c g‖ +
      ∫ x, ‖star (h x) - g x‖ ∂c.variation := by
  have hc := integrable_conj_polar c hm hn
  have hb : ∀ᵐ x ∂c.variation, ‖h x‖ ≤ 1 := ae_of_all _ fun x ↦ (hn x).le
  have he := (hc.sub hg).mul_bdd hm.aestronglyMeasurable hb
  have hgh := hg.mul_bdd hm.aestronglyMeasurable hb
  have hid : (∫ x, (star (h x) - g x) * h x ∂c.variation) +
      (∫ x, g x * h x ∂c.variation) = (c.variation.real univ : ℂ) := by
    rw [← integral_add he hgh]
    calc
      (∫ x, (star (h x) - g x) * h x + g x * h x ∂c.variation) =
          ∫ _ : X, (1 : ℂ) ∂c.variation := by
        apply integral_congr_ae
        exact ae_of_all _ fun x ↦ by
          rw [sub_mul, sub_add_cancel, Complex.conj_mul', hn]
          norm_num
      _ = _ := by simp
  have herror : ‖∫ x, (star (h x) - g x) * h x ∂c.variation‖ ≤
      ∫ x, ‖star (h x) - g x‖ ∂c.variation := by
    have := norm_integral_le_integral_norm (f := fun x ↦ (star (h x) - g x) * h x)
      (μ := c.variation)
    simpa only [norm_mul, hn, mul_one] using this
  have hnative := vectorIntegral_eq_polar c h hm hn hi hr hg
  change complexIntegral c g = _ at hnative
  calc
    c.variation.real univ = ‖(c.variation.real univ : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    _ = ‖(∫ x, (star (h x) - g x) * h x ∂c.variation) +
        (∫ x, g x * h x ∂c.variation)‖ := congrArg norm hid.symm
    _ ≤ ‖∫ x, (star (h x) - g x) * h x ∂c.variation‖ +
        ‖∫ x, g x * h x ∂c.variation‖ := norm_add_le _ _
    _ ≤ ‖complexIntegral c g‖ + ∫ x, ‖star (h x) - g x‖ ∂c.variation := by
      rw [← hnative]
      linarith

/-- The exact norm assertion of 6.19 for any regular complex measure representing
a bounded complex functional. The existence of a representing measure is separate. -/
theorem theorem_6_19_norm (c : ComplexMeasure X) [c.variation.Regular]
    (Φ : ZeroAtInftyContinuousMap X ℂ →L[ℂ] ℂ)
    (hΦ : ∀ f, Φ f = complexIntegral c f) : ‖Φ‖ = c.variation.real univ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg
    intro f
    rw [hΦ]
    simpa only [mul_comm, measureReal_def] using
      theorem_6_18_bound c f ‖f‖ (norm_nonneg f) (fun x ↦ f.toBCF.norm_coe_le_norm x)
  · obtain ⟨h, hm, hn, hi, hr⟩ := theorem_6_12 c
    have hc := integrable_conj_polar c hm hn
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨g, hgc, hgcont, hgn, hgi, hge⟩ :=
      exists_unitBounded_compactSupport_approx c.variation hc
        (fun x ↦ by simp [hn])
        (fun η hη ↦ lch_integrable_exists_hasCompactSupport_integral_sub_le hc hη) hε
    let G : ZeroAtInftyContinuousMap X ℂ :=
      { toFun := g, continuous_toFun := hgcont, zero_at_infty' := hgc.is_zero_at_infty }
    have hG : ‖G‖ ≤ 1 := (BoundedContinuousFunction.norm_le (f := G.toBCF) zero_le_one).mpr hgn
    have hval : ‖complexIntegral c g‖ ≤ ‖Φ‖ := by
      change ‖complexIntegral c G‖ ≤ ‖Φ‖
      rw [← hΦ]
      exact (Φ.le_opNorm G).trans (mul_le_of_le_one_right (norm_nonneg Φ) hG)
    have hmass := polar_mass_le_integral_add_error c h hm hn hi hr hgi
    linarith

/-- A regular complex measure vanishes if every C0 integral vanishes. -/
theorem theorem_6_19_zero (c : ComplexMeasure X) [c.variation.Regular]
    (hc : ∀ f : ZeroAtInftyContinuousMap X ℂ, complexIntegral c f = 0) : c = 0 := by
  have hmass : c.variation.real univ = 0 :=
    (theorem_6_19_norm c 0 (fun f ↦ (hc f).symm)).symm.trans
      (norm_zero : ‖(0 : ZeroAtInftyContinuousMap X ℂ →L[ℂ] ℂ)‖ = 0)
  apply VectorMeasure.variation_eq_zero.mp
  apply Measure.measure_univ_eq_zero.mp
  exact (measureReal_eq_zero_iff (measure_ne_top c.variation univ)).mp hmass

/-- Uniqueness of the regular complex Borel representing measure in 6.19. -/
theorem theorem_6_19_unique (c d : ComplexMeasure X)
    [c.variation.Regular] [d.variation.Regular]
    (h : ∀ f : ZeroAtInftyContinuousMap X ℂ, complexIntegral c f = complexIntegral d f) : c = d := by
  letI : (c - d).variation.Regular := complex_variation_sub_regular c d
  apply sub_eq_zero.mp
  apply theorem_6_19_zero (c - d)
  intro f
  have hc : c.Integrable f := Integrable.of_bound f.continuous.measurable.aestronglyMeasurable
    ‖f‖ (ae_of_all _ fun x ↦ f.toBCF.norm_coe_le_norm x)
  have hd : d.Integrable f := Integrable.of_bound f.continuous.measurable.aestronglyMeasurable
    ‖f‖ (ae_of_all _ fun x ↦ f.toBCF.norm_coe_le_norm x)
  change (∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; c - d]) = 0
  rw [VectorMeasure.integral_sub_vectorMeasure hc hd]
  exact sub_eq_zero.mpr (h f)

#print axioms polar_mass_le_integral_add_error
#print axioms theorem_6_19_norm
#print axioms theorem_6_19_zero
#print axioms theorem_6_19_unique
end RudinRCA.Chapter06
