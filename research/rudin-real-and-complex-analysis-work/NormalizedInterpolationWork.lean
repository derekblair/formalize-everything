import MittagLefflerSetWork
import InterpolationLocalWork
import PrescribedZerosWork

/-!
Normalized interpolation on the complement of a compact plane set. All global
existence inputs are constructed: the prescribed zero function from 15.11 and
the explicit Mittag-Leffler series. Finite, empty, and infinite interpolation
sets use the same statement. Draft awaiting a serialized Lean check.
-/

noncomputable section
open Filter Set Metric Bornology
open scoped Topology OnePoint

namespace RudinRCA.Chapter15

def sphereRegularization (f : ComplexSphere → ℂ) (C : Set ℂ)
    (p : ComplexSphere) : ℂ :=
  p.elim (f ∞) (toMeromorphicNFOn (fun z ↦ f (↑z)) Cᶜ)

@[simp] theorem sphereRegularization_coe (f : ComplexSphere → ℂ) (C : Set ℂ) (z : ℂ) :
    sphereRegularization f C (↑z) = toMeromorphicNFOn (fun w ↦ f (↑w)) Cᶜ z := rfl

@[simp] theorem sphereRegularization_infty (f : ComplexSphere → ℂ) (C : Set ℂ) :
    sphereRegularization f C ∞ = f ∞ := rfl

/-- Altering only a bounded set of finite-plane points leaves the analytic
germ at infinity unchanged. Here regularization changes only actual singular
points from the bounded set S. -/
theorem sphereRegularization_analytic_infinity {C S : Set ℂ}
    (hCbound : IsBounded C) (hSbound : IsBounded S) {f : ComplexSphere → ℂ}
    (hf : MeromorphicOn (fun z ↦ f (↑z)) Cᶜ)
    (hfin : ∀ z ∈ Cᶜ, z ∉ S → AnalyticAt ℂ (fun w ↦ f (↑w)) z)
    (hinfty : SphereAnalyticAt f ∞) : SphereAnalyticAt (sphereRegularization f C) ∞ := by
  obtain ⟨R, hR⟩ := (hCbound.union hSbound).exists_norm_le
  have hlim : Tendsto (fun w : ℂ ↦ ‖w⁻¹‖) (𝓝[≠] 0) atTop :=
    tendsto_norm_cobounded_atTop.comp tendsto_inv₀_nhdsNE_zero
  have hlarge : ∀ᶠ w in 𝓝 0, w ≠ 0 → R < ‖w⁻¹‖ :=
    eventually_nhdsWithin_iff.mp (hlim.eventually (eventually_gt_atTop R))
  change AnalyticAt ℂ (f ∘ sphereInfinityChart) 0 at hinfty
  change AnalyticAt ℂ (sphereRegularization f C ∘ sphereInfinityChart) 0
  apply hinfty.congr
  filter_upwards [hlarge] with w hw
  by_cases hw0 : w = 0
  · subst w
    simp [Function.comp_def]
  · have hnot : w⁻¹ ∉ C ∪ S := fun h ↦ (not_le_of_gt (hw hw0)) (hR _ h)
    have hwC : w⁻¹ ∈ Cᶜ := fun h ↦ hnot (Or.inl h)
    have hwS : w⁻¹ ∉ S := fun h ↦ hnot (Or.inr h)
    simp only [Function.comp_def, sphereInfinityChart_of_ne_zero hw0, sphereRegularization_coe]
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hf hwC,
      toMeromorphicNFAt_eq_self.mpr (hfin _ hwC hwS).meromorphicNFAt]

/-- Exact finite-jet interpolation in the normalized domain, including its
infinity point. The order m counts the requested jets, so m=0 imposes no jet
condition. The construction uses a denominator of order m+1, which also covers
this edge case without deleting points from the data. -/
theorem normalized_interpolate_analytic_germs {C S : Set ℂ}
    (hC : IsCompact C) (hCne : C.Nonempty) (hS : S ⊆ Cᶜ)
    (hScount : S.Countable) (hSbound : IsBounded S)
    (hno : ∀ z ∈ Cᶜ, ¬ AccPt z (𝓟 S))
    (m : ℂ → ℕ) (G : ℂ → ℂ → ℂ) (hG : ∀ a ∈ S, AnalyticAt ℂ (G a) a) :
    ∃ H : ComplexSphere → ℂ,
      SphereHolomorphicOn H (((↑) : ℂ → ComplexSphere) '' C)ᶜ ∧
      ∀ a ∈ S, (m a : ℕ∞) ≤ analyticOrderAt (fun z ↦ H (↑z) - G a z) a := by
  classical
  obtain ⟨h, hh, _, hzeros, horder⟩ := normalized_prescribed_zeros
    hC hCne hS hScount hSbound hno (fun a ↦ m a + 1) (fun _ _ ↦ Nat.succ_pos _)
  have hhplane : AnalyticOnNhd ℂ (fun z ↦ h (↑z)) Cᶜ := by
    intro z hz
    exact hh (↑z) (by simpa only [mem_compl_iff, mem_image, OnePoint.coe_eq_coe,
      exists_eq_right] using hz)
  have hparts : ∀ a : S, ∃ P : Polynomial ℂ, ∃ R : ℂ → ℂ,
      AnalyticAt ℂ R a ∧
      (fun z ↦ G a z / h (↑z)) =ᶠ[𝓝[≠] (a : ℂ)]
        (fun z ↦ P.eval (1 / (z - a)) + R z) := by
    intro a
    exact analytic_quotient_has_polynomial_principal_part (hG a a.property)
      (hhplane a (hS a.property)) (horder a a.property)
  choose P R hR hprincipal using hparts
  obtain ⟨M, hM, hMinfty, hMoff, hMpart⟩ :=
    normalized_mittag_leffler_on_set hC hCne hS hScount hSbound hno P
  let f : ComplexSphere → ℂ := fun p ↦ h p * M p
  have hf : MeromorphicOn (fun z ↦ f (↑z)) Cᶜ := hhplane.meromorphicOn.mul hM
  have hfoff : ∀ z ∈ Cᶜ, z ∉ S → AnalyticAt ℂ (fun w ↦ f (↑w)) z :=
    fun z hz hzS ↦ (hhplane z hz).mul (hMoff z hz hzS)
  have hfinfty : SphereAnalyticAt f ∞ :=
    (hh ∞ (by simp)).mul hMinfty
  have hinterp : ∀ a : S,
      AnalyticAt ℂ (fun z ↦ sphereRegularization f C (↑z)) a ∧
      ((m a + 1 : ℕ) : ℕ∞) ≤
        analyticOrderAt (fun z ↦ sphereRegularization f C (↑z) - G a z) a := by
    intro a
    exact interpolation_from_matching_principal_part (hS a.property) (hG a a.property)
      (hhplane a (hS a.property)) hf (horder a a.property)
      (P a) (R a) (hR a) (hprincipal a) (hMpart a)
  refine ⟨sphereRegularization f C, ?_, ?_⟩
  · intro p hp
    induction p using OnePoint.rec with
    | infty =>
      exact sphereRegularization_analytic_infinity hC.isBounded hSbound hf hfoff hfinfty
    | coe z =>
      have hz : z ∈ Cᶜ := by
        simpa only [mem_compl_iff, mem_image, OnePoint.coe_eq_coe, exists_eq_right] using hp
      by_cases hzS : z ∈ S
      · exact (hinterp ⟨z, hzS⟩).1
      · have hgerm := regularization_eq_analytic_germ hf hz (hfoff z hz hzS) (EventuallyEq.rfl)
        exact (hfoff z hz hzS).congr hgerm.symm
  · intro a ha
    exact (show (m a : ℕ∞) ≤ ((m a + 1 : ℕ) : ℕ∞) by exact_mod_cast Nat.le_succ _).trans
      (hinterp ⟨a, ha⟩).2

#print axioms sphereRegularization_analytic_infinity
#print axioms sphereRegularization_coe
#print axioms sphereRegularization_infty
#print axioms normalized_interpolate_analytic_germs

end RudinRCA.Chapter15
