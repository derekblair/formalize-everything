import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity

/- Prerequisites: Exhaustion.lean, RungeAssembly.lean, RungeUniformSequences.lean.
   The finite Cauchy representations along the exhaustion are explicit input;
   the separate 13.5 existence theorem will discharge that input. -/
noncomputable section
open Set Filter
open scoped Topology OnePoint

namespace RudinRCA.Chapter13

/-- Every permitted component point for Ω is also sufficient for its special
    compact exhaustion, by the full component clause of Rudin 13.3. -/
theorem exhaustionLevel_prescribed_points {Ω : Set ℂ} (A : Set RiemannSphere)
    (hA : A ⊆ (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ)
    (hcomponents : ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ,
      ∃ a ∈ A, a ∈ connectedComponentIn (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ p)
    (n : ℕ) :
    A ⊆ (((↑) : ℂ → RiemannSphere) '' exhaustionLevel Ω n)ᶜ ∧
      ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' exhaustionLevel Ω n)ᶜ,
        ∃ a ∈ A, a ∈ connectedComponentIn
          (((↑) : ℂ → RiemannSphere) '' exhaustionLevel Ω n)ᶜ p := by
  refine ⟨hA.trans (compl_subset_compl.mpr
    (image_mono (exhaustionLevel_subset Ω n))), ?_⟩
  intro p hp
  obtain ⟨q, hq, hsub⟩ := exhaustionLevel_complement_components Ω n p hp
  obtain ⟨a, ha, haq⟩ := hcomponents q hq
  exact ⟨a, ha, hsub haq⟩

/-- A connected spherical complement is inherited by every level of the
    special exhaustion; this uses the nontrivial complement clause of 13.3. -/
theorem exhaustionLevel_connected_complement {Ω : Set ℂ}
    (hconn : IsConnected ((((↑) : ℂ → RiemannSphere) '' Ω)ᶜ)) (n : ℕ) :
    IsConnected ((((↑) : ℂ → RiemannSphere) '' exhaustionLevel Ω n)ᶜ) := by
  let D : Set RiemannSphere := (((↑) : ℂ → RiemannSphere) '' exhaustionLevel Ω n)ᶜ
  have h∞ : (∞ : RiemannSphere) ∈ D := by simp [D]
  have heq : connectedComponentIn D ∞ = D := by
    apply (connectedComponentIn_subset D ∞).antisymm
    intro p hp
    obtain ⟨a, ha, hsub⟩ := exhaustionLevel_complement_components Ω n p hp
    have h∞p : (∞ : RiemannSphere) ∈ connectedComponentIn D p := by
      apply hsub
      rw [hconn.isPreconnected.connectedComponentIn ha]
      simp
    rw [← connectedComponentIn_eq h∞p]
    exact mem_connectedComponentIn hp
  change IsConnected D
  rw [← heq]
  exact isConnected_connectedComponentIn_iff.mpr h∞

/-- Rudin 13.9 follows from the compact approximation theorem and the special
    exhaustion. The output retains the chosen spherical pole set. -/
theorem exists_rational_locally_uniform_sequence_of_finite_cauchy
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (C : ∀ n : ℕ, FiniteCauchyRepresentation (exhaustionLevel Ω n) Ω)
    (A : Set RiemannSphere)
    (hA : A ⊆ (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ)
    (hcomponents : ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ,
      ∃ a ∈ A, a ∈ connectedComponentIn (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ p)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) :
    ∃ R : ℕ → RatFunc ℂ,
      (∀ n z, (R n).denom.eval z = 0 → (z : RiemannSphere) ∈ A) ∧
      ((∞ : RiemannSphere) ∉ A → ∀ n,
        RungeRemovableAtInfinity (fun z ↦ RatFunc.eval (RingHom.id ℂ) z (R n))) ∧
      TendstoLocallyUniformlyOn (fun n z ↦ RatFunc.eval (RingHom.id ℂ) z (R n)) f atTop Ω := by
  have hex : ∀ n : ℕ, ∃ R : RatFunc ℂ,
      (∀ z : ℂ, R.denom.eval z = 0 → (z : RiemannSphere) ∈ A) ∧
      ((∞ : RiemannSphere) ∉ A →
        RungeRemovableAtInfinity (fun z ↦ RatFunc.eval (RingHom.id ℂ) z R)) ∧
      ∀ z ∈ exhaustionLevel Ω n,
        ‖f z - RatFunc.eval (RingHom.id ℂ) z R‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    let : CompactSpace (exhaustionLevel Ω n) := isCompact_iff_compactSpace.mp (exhaustionLevel_isCompact Ω n)
    obtain ⟨hAn, hCn⟩ := exhaustionLevel_prescribed_points A hA hcomponents n
    exact (C n).exists_rational_approximation A hAn hCn f hf (by positivity)
  choose R hRfinite hRinfty herror using hex
  refine ⟨R, hRfinite, fun h∞ n ↦ hRinfty n h∞,
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mpr ?_⟩
  intro K hKΩ hK
  obtain ⟨N, hN⟩ := compact_subset_exhaustionLevel hΩ hK hKΩ
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall, eventually_ge_atTop N] with n hn hNn
  intro z hz
  have hzlevel := exhaustionLevel_mono Ω hNn (hN hz)
  simpa only [dist_eq_norm] using (herror n z hzlevel).trans hn

/-- The polynomial form of Runge on open sets follows in the connected
    spherical-complement case, with convergence on every compact subset. -/
theorem exists_polynomial_locally_uniform_sequence_of_finite_cauchy
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (C : ∀ n : ℕ, FiniteCauchyRepresentation (exhaustionLevel Ω n) Ω)
    (hconn : IsConnected ((((↑) : ℂ → RiemannSphere) '' Ω)ᶜ))
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) :
    ∃ P : ℕ → Polynomial ℂ,
      TendstoLocallyUniformlyOn (fun n z ↦ (P n).eval z) f atTop Ω := by
  have hex : ∀ n : ℕ, ∃ P : Polynomial ℂ,
      ∀ z ∈ exhaustionLevel Ω n, ‖f z - P.eval z‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    let : CompactSpace (exhaustionLevel Ω n) := isCompact_iff_compactSpace.mp (exhaustionLevel_isCompact Ω n)
    exact (C n).exists_polynomial_approximation
      (exhaustionLevel_connected_complement hconn n) f hf (by positivity)
  choose P herror using hex
  refine ⟨P, (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mpr ?_⟩
  intro K hKΩ hK
  obtain ⟨N, hN⟩ := compact_subset_exhaustionLevel hΩ hK hKΩ
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall, eventually_ge_atTop N] with n hn hNn
  intro z hz
  have hzlevel := exhaustionLevel_mono Ω hNn (hN hz)
  simpa only [dist_eq_norm] using (herror n z hzlevel).trans hn

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.exhaustionLevel_prescribed_points
#print axioms RudinRCA.Chapter13.exhaustionLevel_connected_complement
#print axioms RudinRCA.Chapter13.exists_rational_locally_uniform_sequence_of_finite_cauchy
#print axioms RudinRCA.Chapter13.exists_polynomial_locally_uniform_sequence_of_finite_cauchy
