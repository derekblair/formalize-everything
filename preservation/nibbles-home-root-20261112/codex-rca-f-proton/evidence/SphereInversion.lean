import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Algebra.Group.Basic

/-! Spherical inversion and translation for Rudin RCA 13.8 and 14.3.
The model is the actual one-point compactification of ℂ. Inversion exchanges
zero and infinity, and agrees with z⁻¹ at every other finite point. -/

open Set Filter Function Metric
open scoped Topology OnePoint

namespace RudinRCA.Chapter13

noncomputable def sphereInv : OnePoint ℂ → OnePoint ℂ :=
  OnePoint.rec ((0 : ℂ) : OnePoint ℂ) (fun z => if z = 0 then ∞ else ((z⁻¹ : ℂ) : OnePoint ℂ))

@[simp] theorem sphereInv_infty : sphereInv ∞ = ((0 : ℂ) : OnePoint ℂ) := rfl

@[simp] theorem sphereInv_zero : sphereInv ((0 : ℂ) : OnePoint ℂ) = ∞ := by
  simp [sphereInv, OnePoint.rec]

theorem sphereInv_coe_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    sphereInv (z : OnePoint ℂ) = ((z⁻¹ : ℂ) : OnePoint ℂ) := by
  simp [sphereInv, OnePoint.rec, hz]

theorem sphereInv_involutive : Involutive sphereInv := by
  intro z
  induction z using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · subst z; simp
    · simp [sphereInv_coe_of_ne_zero hz, sphereInv_coe_of_ne_zero (inv_ne_zero hz)]

theorem sphereInv_continuousAt_infty : ContinuousAt sphereInv ∞ := by
  rw [OnePoint.continuousAt_infty', sphereInv_infty]
  have hi : Tendsto (fun z : ℂ => z⁻¹) (coclosedCompact ℂ) (𝓝 0) := by
    rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hne : ∀ᶠ z : ℂ in coclosedCompact ℂ, z ≠ 0 := by
    rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact (tendsto_norm_cobounded_atTop.eventually_gt_atTop 0).mono fun z hz => norm_pos_iff.mp hz
  apply (OnePoint.continuous_coe.continuousAt.tendsto.comp hi).congr'
  filter_upwards [hne] with z hz
  exact (sphereInv_coe_of_ne_zero hz).symm

theorem sphereInv_continuousAt_zero : ContinuousAt sphereInv ((0 : ℂ) : OnePoint ℂ) := by
  rw [OnePoint.continuousAt_coe]
  change Tendsto (fun z : ℂ => sphereInv (z : OnePoint ℂ)) (𝓝 0) (𝓝 (sphereInv (0 : ℂ)))
  rw [sphereInv_zero, ← nhdsNE_sup_pure (0 : ℂ), tendsto_sup]
  constructor
  · have hi : Tendsto (fun z : ℂ => z⁻¹) (𝓝[≠] 0) (coclosedCompact ℂ) := by
      rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_nhdsNE_zero
    apply (OnePoint.tendsto_coe_infty.comp hi).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (sphereInv_coe_of_ne_zero hz).symm
  · simpa using (tendsto_pure_nhds (fun z : ℂ => sphereInv (z : OnePoint ℂ)) (0 : ℂ))

theorem sphereInv_continuousAt_coe_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt sphereInv (z : OnePoint ℂ) := by
  rw [OnePoint.continuousAt_coe]
  have h : ContinuousAt (fun w : ℂ => ((w⁻¹ : ℂ) : OnePoint ℂ)) z :=
    OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hz] with w hw
  exact sphereInv_coe_of_ne_zero hw

theorem continuous_sphereInv : Continuous sphereInv := by
  rw [continuous_iff_continuousAt]
  intro z
  induction z using OnePoint.rec with
  | infty => exact sphereInv_continuousAt_infty
  | coe z =>
    by_cases hz : z = 0
    · subst z; exact sphereInv_continuousAt_zero
    · exact sphereInv_continuousAt_coe_of_ne_zero hz

/-- Inversion is a self-homeomorphism of the sphere, including both chart poles. -/
noncomputable def sphereInvHomeomorph : OnePoint ℂ ≃ₜ OnePoint ℂ where
  toFun := sphereInv
  invFun := sphereInv
  left_inv := sphereInv_involutive
  right_inv := sphereInv_involutive
  continuous_toFun := continuous_sphereInv
  continuous_invFun := continuous_sphereInv

@[simp] theorem sphereInvHomeomorph_apply (z : OnePoint ℂ) :
    sphereInvHomeomorph z = sphereInv z := rfl

@[simp] theorem sphereInvHomeomorph_symm : sphereInvHomeomorph.symm = sphereInvHomeomorph := rfl

/-- Translation of the sphere fixes infinity and extends z ↦ b+z. -/
noncomputable def sphereTranslation (b : ℂ) : OnePoint ℂ ≃ₜ OnePoint ℂ :=
  Homeomorph.onePointCongr {
    toFun := fun z : ℂ => b + z
    invFun := fun z : ℂ => z - b
    left_inv := by intro z; simp
    right_inv := by intro z; simp
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

@[simp] theorem sphereTranslation_infty (b : ℂ) : sphereTranslation b ∞ = ∞ := rfl

@[simp] theorem sphereTranslation_coe (b z : ℂ) :
    sphereTranslation b (z : OnePoint ℂ) = ((b + z : ℂ) : OnePoint ℂ) := rfl

@[simp] theorem sphereTranslation_symm_coe (b z : ℂ) :
    (sphereTranslation b).symm (z : OnePoint ℂ) = ((z - b : ℂ) : OnePoint ℂ) := rfl

/-- The change of chart w ↦ b+1/w, sending infinity to the chosen center b. -/
noncomputable def translatedSphereInv (b : ℂ) : OnePoint ℂ ≃ₜ OnePoint ℂ :=
  sphereInvHomeomorph.trans (sphereTranslation b)

@[simp] theorem translatedSphereInv_infty (b : ℂ) :
    translatedSphereInv b ∞ = (b : OnePoint ℂ) := by
  simp [translatedSphereInv]

@[simp] theorem translatedSphereInv_zero (b : ℂ) :
    translatedSphereInv b ((0 : ℂ) : OnePoint ℂ) = ∞ := by
  simp [translatedSphereInv]

theorem translatedSphereInv_coe_of_ne_zero (b : ℂ) {z : ℂ} (hz : z ≠ 0) :
    translatedSphereInv b (z : OnePoint ℂ) = ((b + z⁻¹ : ℂ) : OnePoint ℂ) := by
  simp [translatedSphereInv, sphereInv_coe_of_ne_zero hz]

@[simp] theorem translatedSphereInv_symm_infty (b : ℂ) :
    (translatedSphereInv b).symm ∞ = ((0 : ℂ) : OnePoint ℂ) := by
  simp [translatedSphereInv, sphereTranslation]

@[simp] theorem translatedSphereInv_symm_center (b : ℂ) :
    (translatedSphereInv b).symm (b : OnePoint ℂ) = ∞ := by
  simp [translatedSphereInv]

theorem translatedSphereInv_symm_coe_of_ne (b : ℂ) {z : ℂ} (hz : z ≠ b) :
    (translatedSphereInv b).symm (z : OnePoint ℂ) = (((z - b)⁻¹ : ℂ) : OnePoint ℂ) := by
  simp [translatedSphereInv, sphereInv_coe_of_ne_zero (sub_ne_zero.mpr hz)]

#print axioms sphereInv_involutive
#print axioms sphereInv_continuousAt_infty
#print axioms sphereInv_continuousAt_zero
#print axioms sphereInv_continuousAt_coe_of_ne_zero
#print axioms continuous_sphereInv
#print axioms sphereInvHomeomorph
#print axioms sphereTranslation
#print axioms translatedSphereInv
#print axioms translatedSphereInv_coe_of_ne_zero
#print axioms translatedSphereInv_symm_coe_of_ne
end RudinRCA.Chapter13
