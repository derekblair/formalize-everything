import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Positivity

/- Prerequisites: RungeAssembly.lean and RungePolynomialWitness.lean.
   These are conditional consequences of an actual universal finite Cauchy
   representation; this file does not assert that representation exists. -/
noncomputable section
open Set Filter
open scoped Topology OnePoint

namespace RudinRCA.Chapter13

/-- With connected spherical complement the only prescribed pole can be infinity. -/
theorem FiniteCauchyRepresentation.exists_polynomial_approximation
    {K Ω : Set ℂ} [CompactSpace K] (C : FiniteCauchyRepresentation K Ω)
    (hconn : IsConnected ((((↑) : ℂ → RiemannSphere) '' K)ᶜ))
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℂ, ∀ z ∈ K, ‖f z - P.eval z‖ < ε := by
  have hA : {(∞ : RiemannSphere)} ⊆ (((↑) : ℂ → RiemannSphere) '' K)ᶜ := by
    intro p hp
    have hp' : p = ∞ := hp
    subst p
    simp
  have hcomponents : ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
      ∃ a ∈ ({∞} : Set RiemannSphere),
        a ∈ connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K)ᶜ p := by
    intro p hp
    refine ⟨∞, by simp, ?_⟩
    rw [hconn.isPreconnected.connectedComponentIn hp]
    simp
  have hfinite : ∀ α : ℂ, (α : RiemannSphere) ∈ ({∞} : Set RiemannSphere) →
      ∀ n : ℕ, resolvent (compactCoordinate K) α ^ (n + 1) ∈ rungeSpace K {∞} := by
    intro α hα
    simp at hα
  have hinfty : (∞ : RiemannSphere) ∈ ({∞} : Set RiemannSphere) →
      ∀ n : ℕ, compactCoordinate K ^ n ∈ rungeSpace K {∞} := by
    intro h∞ n
    exact Submodule.subset_span (Or.inr (Or.inr ⟨h∞, n, rfl⟩))
  obtain ⟨g, hg, herror⟩ := C.exists_submodule_approximation {∞}
    (rungeSpace K {∞}) hA hcomponents hfinite hinfty f hf hε
  obtain ⟨P, hP⟩ := rungeSpace_polynomial_witness K hg
  refine ⟨P, fun z hz ↦ ?_⟩
  simpa only [← hP ⟨z, hz⟩] using herror ⟨z, hz⟩

/-- The quantitative polynomial approximations can be chosen as a uniformly
    convergent sequence, the conclusion printed in Rudin 13.7. -/
theorem FiniteCauchyRepresentation.exists_polynomial_uniform_sequence
    {K Ω : Set ℂ} [CompactSpace K] (C : FiniteCauchyRepresentation K Ω)
    (hconn : IsConnected ((((↑) : ℂ → RiemannSphere) '' K)ᶜ))
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) :
    ∃ P : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n z ↦ (P n).eval z) f atTop K := by
  have hex : ∀ n : ℕ, ∃ P : Polynomial ℂ,
      ∀ z ∈ K, ‖f z - P.eval z‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    exact C.exists_polynomial_approximation hconn f hf (by positivity)
  choose P hP using hex
  refine ⟨P, Metric.tendstoUniformlyOn_iff.mpr ?_⟩
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall] with n hn
  intro z hz
  simpa only [dist_eq_norm] using (hP n z hz).trans hn

/-- The rational approximation conclusion of 13.6 includes a sequence with
    the prescribed spherical pole restriction at every index. -/
theorem FiniteCauchyRepresentation.exists_rational_uniform_sequence
    {K Ω : Set ℂ} [CompactSpace K] (C : FiniteCauchyRepresentation K Ω)
    (A : Set RiemannSphere)
    (hA : A ⊆ (((↑) : ℂ → RiemannSphere) '' K)ᶜ)
    (hcomponents : ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
      ∃ a ∈ A, a ∈ connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K)ᶜ p)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) :
    ∃ R : ℕ → RatFunc ℂ,
      (∀ n z, (R n).denom.eval z = 0 → (z : RiemannSphere) ∈ A) ∧
      ((∞ : RiemannSphere) ∉ A → ∀ n,
        RungeRemovableAtInfinity (fun z ↦ RatFunc.eval (RingHom.id ℂ) z (R n))) ∧
      TendstoUniformlyOn (fun n z ↦ RatFunc.eval (RingHom.id ℂ) z (R n)) f atTop K := by
  have hex : ∀ n : ℕ, ∃ R : RatFunc ℂ,
      (∀ z : ℂ, R.denom.eval z = 0 → (z : RiemannSphere) ∈ A) ∧
      ((∞ : RiemannSphere) ∉ A →
        RungeRemovableAtInfinity (fun z ↦ RatFunc.eval (RingHom.id ℂ) z R)) ∧
      ∀ z ∈ K, ‖f z - RatFunc.eval (RingHom.id ℂ) z R‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    exact C.exists_rational_approximation A hA hcomponents f hf (by positivity)
  choose R hRfinite hRinfty herror using hex
  refine ⟨R, hRfinite, fun h∞ n ↦ hRinfty n h∞,
    Metric.tendstoUniformlyOn_iff.mpr ?_⟩
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall] with n hn
  intro z hz
  simpa only [dist_eq_norm] using (herror n z hz).trans hn

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.FiniteCauchyRepresentation.exists_polynomial_approximation
#print axioms RudinRCA.Chapter13.FiniteCauchyRepresentation.exists_polynomial_uniform_sequence
#print axioms RudinRCA.Chapter13.FiniteCauchyRepresentation.exists_rational_uniform_sequence
