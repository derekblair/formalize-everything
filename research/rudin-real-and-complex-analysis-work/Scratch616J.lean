import Scratch616I

/-! The linear isometric equivalence asserted after Rudin 6.16. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [SigmaFinite μ]
variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
variable [ENNReal.HolderConjugate p q]

/-- The complex bilinear integral pairing as a linear isometry into the dual. -/
def lpDualityLinearIsometry (hp : p ≠ ∞) :
    Lp ℂ q μ →ₗᵢ[ℂ] (Lp ℂ p μ →L[ℂ] ℂ) :=
  { ((ContinuousLinearMap.mul ℂ ℂ).lpPairing μ q p).toLinearMap with
    norm_map' := by
      intro G
      let B := ContinuousLinearMap.mul ℂ ℂ
      let Ψ := B.lpPairing μ q p G
      obtain ⟨H, ⟨hH, hnorm⟩, _⟩ := theorem_6_16 μ p q hp Ψ
      have hHG : H = G := by
        apply lp_integral_pairing_unique μ p q H G
        intro f
        calc
          (∫ x, f x * H x ∂μ) = Ψ f := (hH f).symm
          _ = ∫ x, f x * G x ∂μ := by
            simpa only [Ψ, B, ContinuousLinearMap.mul_apply', mul_comm] using
              B.lpPairing_eq_integral G f
      exact hnorm.trans (congrArg norm hHG) }

theorem lpDualityLinearIsometry_apply (hp : p ≠ ∞)
    (G : Lp ℂ q μ) (f : Lp ℂ p μ) :
    lpDualityLinearIsometry μ p q hp G f = ∫ x, f x * G x ∂μ := by
  change (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ q p G f = _
  simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
    (ContinuousLinearMap.mul ℂ ℂ).lpPairing_eq_integral G f

theorem lpDualityLinearIsometry_surjective (hp : p ≠ ∞) :
    Function.Surjective (lpDualityLinearIsometry μ p q hp) := by
  intro Φ
  obtain ⟨G, ⟨hrep, _⟩, _⟩ := theorem_6_16 μ p q hp Φ
  refine ⟨G, ?_⟩
  ext f
  exact (lpDualityLinearIsometry_apply μ p q hp G f).trans (hrep f).symm

omit [Fact (1 ≤ q)] in
/-- Rudin 6.16, the attached isometric-isomorphism assertion: every complex
continuous linear functional on Lp is uniquely an integral against an Lq class.
The conjugate exponent's lower bound follows from Hölder conjugacy. -/
def theorem_6_16_linearIsometryEquiv (hp : p ≠ ∞) :
    letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
    Lp ℂ q μ ≃ₗᵢ[ℂ] (Lp ℂ p μ →L[ℂ] ℂ) := by
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  exact LinearIsometryEquiv.ofSurjective (lpDualityLinearIsometry μ p q hp)
    (lpDualityLinearIsometry_surjective μ p q hp)

omit [Fact (1 ≤ q)] in
theorem theorem_6_16_linearIsometryEquiv_apply (hp : p ≠ ∞)
    (G : Lp ℂ q μ) (f : Lp ℂ p μ) :
    theorem_6_16_linearIsometryEquiv μ p q hp G f = ∫ x, f x * G x ∂μ := by
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  change lpDualityLinearIsometry μ p q hp G f = _
  exact lpDualityLinearIsometry_apply μ p q hp G f

#print axioms lpDualityLinearIsometry
#print axioms lpDualityLinearIsometry_apply
#print axioms lpDualityLinearIsometry_surjective
#print axioms theorem_6_16_linearIsometryEquiv
#print axioms theorem_6_16_linearIsometryEquiv_apply

end RudinRCA.Chapter06
