import HolomorphicBezoutWork
import HolomorphicIdealsWork

/-! Uncompiled algebraic wrapper for 15.14--15.15. -/

noncomputable section
open Finset Set

namespace RudinRCA.Chapter15

/-- The two explicit coefficient identities in printed 15.15 imply equality
of the generated ideal with the principal ideal, in the 15.14 definitions. -/
theorem generated_ideal_eq_principal_of_coefficients {ι : Type*} [Fintype ι]
    {Ω : Set ℂ} {g : ι → ℂ → ℂ} {q : ℂ → ℂ} {a b : ι → ℂ → ℂ}
    (ha : ∀ i, DifferentiableOn ℂ (a i) Ω)
    (hb : ∀ i, DifferentiableOn ℂ (b i) Ω)
    (heq : ∀ z ∈ Ω, q z = ∑ i, a i z * g i z)
    (hdiv : ∀ i z, z ∈ Ω → g i z = b i z * q z) :
    ∀ f : ℂ → ℂ,
      InGeneratedHolomorphicIdeal Ω g f ↔ InPrincipalHolomorphicIdeal Ω q f := by
  intro f
  constructor
  · rintro ⟨hf, h, hh, hsum⟩
    refine ⟨hf, (fun z ↦ ∑ i, h i z * b i z),
      DifferentiableOn.fun_sum (fun i _ ↦ (hh i).mul (hb i)), ?_⟩
    intro z hz
    rw [hsum z hz, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hdiv i z hz, mul_assoc]
  · rintro ⟨hf, h, hh, hmul⟩
    refine ⟨hf, (fun i z ↦ h z * a i z),
      (fun i ↦ hh.mul (ha i)), ?_⟩
    intro z hz
    rw [hmul z hz, heq z hz, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (mul_assoc _ _ _).symm

/-- The general finite-index ideal wrapper needs only the pair construction;
the latter's mathematical proof is the 15.11/15.13 construction assembly. -/
theorem generated_holomorphic_ideal_is_principal_of_pair {ι : Type*} [Fintype ι]
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hpair : ∀ f g : ℂ → ℂ, AnalyticOnNhd ℂ f Ω → AnalyticOnNhd ℂ g Ω →
      ∃ q H Q F G : ℂ → ℂ, AnalyticOnNhd ℂ q Ω ∧
        AnalyticOnNhd ℂ H Ω ∧ AnalyticOnNhd ℂ Q Ω ∧
        AnalyticOnNhd ℂ F Ω ∧ AnalyticOnNhd ℂ G Ω ∧
        ∀ z ∈ Ω, q z = H z * f z + Q z * g z ∧
          f z = F z * q z ∧ g z = G z * q z)
    (g : ι → ℂ → ℂ) (hg : ∀ i, DifferentiableOn ℂ (g i) Ω) :
    GeneratedHolomorphicIdealIsPrincipal Ω g := by
  obtain ⟨q, a, b, hq, ha, hb, heq, hdiv⟩ :=
    holomorphic_fintype_generators_principal_of_pair hpair g (fun i ↦ (hg i).analyticOnNhd hΩ)
  refine ⟨q, (fun z hz ↦ (hq z hz).differentiableAt.differentiableWithinAt), ?_⟩
  exact generated_ideal_eq_principal_of_coefficients
    (fun i z hz ↦ (ha i z hz).differentiableAt.differentiableWithinAt)
    (fun i z hz ↦ (hb i z hz).differentiableAt.differentiableWithinAt) heq hdiv

#print axioms generated_ideal_eq_principal_of_coefficients
#print axioms generated_holomorphic_ideal_is_principal_of_pair

end RudinRCA.Chapter15
