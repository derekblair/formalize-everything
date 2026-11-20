import RudinRCA.Chapter13
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Positivity

/- Prerequisites: Exhaustion, RungeAssembly, MittagLefflerCore,
   MittagLefflerSeries. The only undischarged mathematical input is the actual
   finite Cauchy representation existence theorem (13.5). -/
noncomputable section
open Set Filter
open scoped Topology BigOperators OnePoint

namespace RudinRCA.Chapter13

/-- Totalized rational evaluation is analytic at every non-pole. -/
theorem ratFuncEval_analyticAt_of_denom_ne_zero (R : RatFunc ℂ) {z : ℂ}
    (hz : R.denom.eval z ≠ 0) :
    AnalyticAt ℂ (fun w ↦ RatFunc.eval (RingHom.id ℂ) w R) z := by
  simpa only [RatFunc.eval, Polynomial.eval₂_id] using
    ((AnalyticOnNhd.eval_polynomial R.num) z (mem_univ z)).div
      ((AnalyticOnNhd.eval_polynomial R.denom) z (mem_univ z)) hz

/-- Exact Mittag-Leffler realization from the finite Cauchy representation
    theorem: all prescribed negative-power expressions are realized, and the
    function is analytic elsewhere in Ω. The coefficients may all be zero. -/
theorem mittag_leffler_of_finite_cauchy
    (hCauchy : ∀ (K U : Set ℂ), IsCompact K → IsOpen U → K ⊆ U →
      Nonempty (FiniteCauchyRepresentation K U))
    {Ω A : Set ℂ} (hΩ : IsOpen Ω) (hAΩ : A ⊆ Ω)
    (hacc : ∀ z ∈ Ω, ¬AccPt z (𝓟 A))
    (m : ℂ → ℕ) (hm : ∀ α ∈ A, 0 < m α) (c : ℂ → ℕ → ℂ) :
    ∃ f : ℂ → ℂ, MeromorphicOn f Ω ∧
      (∀ α ∈ A, AnalyticAt ℂ (fun z ↦ f z - finitePrincipalPart (m α) (c α) α z) α) ∧
      ∀ z ∈ Ω \ A, AnalyticAt ℂ f z := by
  classical
  let S : ℕ → Finset ℂ := fun n ↦
    (finite_inter_compact_of_no_accumulation hacc (exhaustionLevel_isCompact Ω n)
      (exhaustionLevel_subset Ω n)).toFinset
  have hS : ∀ n α, α ∈ S n ↔ α ∈ A ∩ exhaustionLevel Ω n := by
    intro n α
    exact Set.Finite.mem_toFinset _
  have hmono : Monotone S := by
    intro n k hnk α hα
    have hh := (hS n α).mp hα
    exact (hS k α).mpr ⟨hh.1, exhaustionLevel_mono Ω hnk hh.2⟩
  let Q : ℕ → ℂ → ℂ := fun n ↦ finitePrincipalSum (S n) m c
  let D : Set RiemannSphere := (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ
  have hex : ∀ n : ℕ, ∃ r : ℂ → ℂ, DifferentiableOn ℂ r Ω ∧
      ∀ z ∈ exhaustionLevel Ω n, ‖Q (n + 1) z - Q n z - r z‖ ≤ (1 / 2 : ℝ) ^ n := by
    intro n
    let B : Finset ℂ := S (n + 1) \ S n
    let U : Set ℂ := Ω \ (B : Set ℂ)
    have hU : IsOpen U := hΩ.sdiff B.finite_toSet.isClosed
    have hKU : exhaustionLevel Ω n ⊆ U := by
      intro z hz
      refine ⟨exhaustionLevel_subset Ω n hz, ?_⟩
      intro hzB
      obtain ⟨hznext, hznot⟩ := Finset.mem_sdiff.mp hzB
      exact hznot ((hS n z).mpr ⟨((hS (n + 1) z).mp hznext).1, hz⟩)
    have hdiff : DifferentiableOn ℂ (fun z ↦ Q (n + 1) z - Q n z) U := by
      have heq : (fun z ↦ Q (n + 1) z - Q n z) = finitePrincipalSum B m c := by
        funext z
        exact finitePrincipalSum_sub_eq_sdiff (hmono (Nat.le_succ n)) m c z
      rw [heq]
      intro z hz
      exact (finitePrincipalSum_analyticAt B m c hz.2).differentiableAt.differentiableWithinAt
    obtain ⟨C⟩ := hCauchy (exhaustionLevel Ω n) U (exhaustionLevel_isCompact Ω n) hU hKU
    let : CompactSpace (exhaustionLevel Ω n) :=
      isCompact_iff_compactSpace.mp (exhaustionLevel_isCompact Ω n)
    have hD : D ⊆ (((↑) : ℂ → RiemannSphere) '' exhaustionLevel Ω n)ᶜ :=
      compl_subset_compl.mpr (image_mono (exhaustionLevel_subset Ω n))
    have hcomponents : ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' exhaustionLevel Ω n)ᶜ,
        ∃ a ∈ D, a ∈ connectedComponentIn
          (((↑) : ℂ → RiemannSphere) '' exhaustionLevel Ω n)ᶜ p := by
      intro p hp
      obtain ⟨a, ha, hsub⟩ := exhaustionLevel_complement_components Ω n p hp
      exact ⟨a, ha, hsub (mem_connectedComponentIn ha)⟩
    obtain ⟨R, hRfinite, _, hRerror⟩ := C.exists_rational_approximation D hD hcomponents
      (fun z ↦ Q (n + 1) z - Q n z) hdiff (by positivity : 0 < (1 / 2 : ℝ) ^ n)
    refine ⟨fun z ↦ RatFunc.eval (RingHom.id ℂ) z R, ?_, fun z hz ↦ (hRerror z hz).le⟩
    intro z hz
    apply (ratFuncEval_analyticAt_of_denom_ne_zero R ?_).differentiableAt.differentiableWithinAt
    intro hdenom
    have hnot : z ∉ Ω := by simpa [D] using hRfinite z hdenom
    exact hnot hz
  choose r hr herror using hex
  exact mittag_leffler_of_exhaustion_corrections hΩ hAΩ m c S hS r hr herror

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.ratFuncEval_analyticAt_of_denom_ne_zero
#print axioms RudinRCA.Chapter13.mittag_leffler_of_finite_cauchy
