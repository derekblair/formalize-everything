import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Sphere infrastructure for the full scope of Rudin 15.11.

The sphere is the one-point compactification of the complex plane. Holomorphy
and zero order at infinity are defined using the inversion chart, including
the value at its origin. This file does not yet prove the zero-set existence
theorem. In particular, an arbitrary-plane-domain product construction and
its transport through an omitted-point chart remain separate obligations.
-/

noncomputable section

open Filter Set Bornology
open scoped Topology OnePoint

namespace RudinRCA.Chapter15

abbrev ComplexSphere := OnePoint ℂ

/-- Inversion on the Riemann sphere exchanges zero and infinity. -/
def sphereInv (p : ComplexSphere) : ComplexSphere :=
  p.elim (↑(0 : ℂ)) (fun z ↦ if z = 0 then ∞ else ↑z⁻¹)

@[simp] theorem sphereInv_infty : sphereInv ∞ = (↑(0 : ℂ) : ComplexSphere) := rfl

@[simp] theorem sphereInv_zero : sphereInv (↑(0 : ℂ)) = ∞ := by simp [sphereInv]

theorem sphereInv_coe_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    sphereInv (↑z) = (↑z⁻¹ : ComplexSphere) := by simp [sphereInv, hz]

@[simp] theorem sphereInv_involutive (p : ComplexSphere) :
    sphereInv (sphereInv p) = p := by
  induction p using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · subst z; simp
    · simp [sphereInv_coe_of_ne_zero hz, sphereInv_coe_of_ne_zero (inv_ne_zero hz)]

theorem sphereInv_eventually_eq_inv {z : ℂ} (hz : z ≠ 0) :
    (fun w : ℂ ↦ sphereInv (↑w)) =ᶠ[𝓝 z] (fun w ↦ (↑w⁻¹ : ComplexSphere)) := by
  filter_upwards [eventually_ne_nhds hz] with w hw
  exact sphereInv_coe_of_ne_zero hw

theorem continuous_sphereInv : Continuous sphereInv := by
  rw [continuous_iff_continuousAt]
  intro p
  induction p using OnePoint.rec with
  | infty =>
    rw [OnePoint.continuousAt_infty', sphereInv_infty]
    have hlim : Tendsto (fun z : ℂ ↦ (↑z⁻¹ : ComplexSphere))
        (cobounded ℂ) (𝓝 (↑(0 : ℂ) : ComplexSphere)) :=
      OnePoint.continuous_coe.continuousAt.tendsto.comp tendsto_inv₀_cobounded
    have heq : (fun z : ℂ ↦ sphereInv (↑z)) =ᶠ[cobounded ℂ]
        (fun z ↦ (↑z⁻¹ : ComplexSphere)) := by
      filter_upwards [eventually_cobounded_le_norm (E := ℂ) 1] with z hz
      apply sphereInv_coe_of_ne_zero
      intro hzero
      simpa [hzero] using hz
    simpa only [Function.comp_def, coclosedCompact_eq_cocompact,
      ← Metric.cobounded_eq_cocompact] using hlim.congr' heq.symm
  | coe z =>
    rw [OnePoint.continuousAt_coe]
    by_cases hz : z = 0
    · subst z
      rw [continuousAt_iff_punctured_nhds]
      change Tendsto (fun z : ℂ ↦ sphereInv (↑z)) (𝓝[≠] 0) (𝓝 ∞)
      have hcoe : Tendsto ((↑) : ℂ → ComplexSphere) (cobounded ℂ) (𝓝 ∞) := by
        simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
          using (OnePoint.tendsto_coe_infty (X := ℂ))
      apply (hcoe.comp tendsto_inv₀_nhdsNE_zero).congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (sphereInv_coe_of_ne_zero hz).symm
    · exact (OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz))
        .congr_of_eventuallyEq (sphereInv_eventually_eq_inv hz)

/-- The sphere inversion map, including its continuity at both exceptional points. -/
def sphereInvHomeomorph : ComplexSphere ≃ₜ ComplexSphere where
  toFun := sphereInv
  invFun := sphereInv
  left_inv := sphereInv_involutive
  right_inv := sphereInv_involutive
  continuous_toFun := continuous_sphereInv
  continuous_invFun := continuous_sphereInv

/-- The infinity coordinate's inverse: zero represents infinity. -/
def sphereInfinityChart (w : ℂ) : ComplexSphere := sphereInv (↑w)

@[simp] theorem sphereInfinityChart_zero : sphereInfinityChart 0 = ∞ := sphereInv_zero

theorem sphereInfinityChart_of_ne_zero {w : ℂ} (hw : w ≠ 0) :
    sphereInfinityChart w = (↑w⁻¹ : ComplexSphere) := sphereInv_coe_of_ne_zero hw

theorem continuous_sphereInfinityChart : Continuous sphereInfinityChart :=
  continuous_sphereInv.comp OnePoint.continuous_coe

/-- Holomorphy in the standard two complex charts of the sphere. -/
def SphereAnalyticAt (f : ComplexSphere → ℂ) (p : ComplexSphere) : Prop :=
  p.elim (AnalyticAt ℂ (f ∘ sphereInfinityChart) 0)
    (fun z ↦ AnalyticAt ℂ (fun w : ℂ ↦ f (↑w)) z)

def SphereHolomorphicOn (f : ComplexSphere → ℂ) (Ω : Set ComplexSphere) : Prop :=
  ∀ p ∈ Ω, SphereAnalyticAt f p

/-- Zero order is measured in the same two charts, including at infinity. -/
def sphereAnalyticOrderAt (f : ComplexSphere → ℂ) (p : ComplexSphere) : ℕ∞ :=
  p.elim (analyticOrderAt (f ∘ sphereInfinityChart) 0)
    (fun z ↦ analyticOrderAt (fun w : ℂ ↦ f (↑w)) z)

@[simp] theorem sphereAnalyticAt_coe (f : ComplexSphere → ℂ) (z : ℂ) :
    SphereAnalyticAt f (↑z) ↔ AnalyticAt ℂ (fun w : ℂ ↦ f (↑w)) z := Iff.rfl

@[simp] theorem sphereAnalyticAt_infty (f : ComplexSphere → ℂ) :
    SphereAnalyticAt f ∞ ↔ AnalyticAt ℂ (f ∘ sphereInfinityChart) 0 := Iff.rfl

@[simp] theorem sphereAnalyticOrderAt_coe (f : ComplexSphere → ℂ) (z : ℂ) :
    sphereAnalyticOrderAt f (↑z) = analyticOrderAt (fun w : ℂ ↦ f (↑w)) z := rfl

@[simp] theorem sphereAnalyticOrderAt_infty (f : ComplexSphere → ℂ) :
    sphereAnalyticOrderAt f ∞ = analyticOrderAt (f ∘ sphereInfinityChart) 0 := rfl

/-- Holomorphy is preserved and reflected by sphere inversion. -/
theorem sphereAnalyticAt_comp_inv_iff (f : ComplexSphere → ℂ) (p : ComplexSphere) :
    SphereAnalyticAt (f ∘ sphereInv) p ↔ SphereAnalyticAt f (sphereInv p) := by
  induction p using OnePoint.rec with
  | infty =>
    simp [SphereAnalyticAt, sphereInfinityChart, Function.comp_def]
  | coe z =>
    by_cases hz : z = 0
    · subst z
      simp only [sphereInv_zero, sphereAnalyticAt_coe, sphereAnalyticAt_infty,
        sphereInfinityChart, Function.comp_def]
    · rw [sphereInv_coe_of_ne_zero hz, sphereAnalyticAt_coe, sphereAnalyticAt_coe]
      have heq : (fun w : ℂ ↦ (f ∘ sphereInv) (↑w)) =ᶠ[𝓝 z]
          ((fun w : ℂ ↦ f (↑w)) ∘ Inv.inv) :=
        (sphereInv_eventually_eq_inv hz).fun_comp f
      rw [analyticAt_congr heq]
      apply analyticAt_comp_iff_of_deriv_ne_zero (analyticAt_inv hz)
      simpa only [deriv_inv] using neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hz))

/-- The zero multiplicity is unchanged by the inversion change of coordinates. -/
theorem sphereAnalyticOrderAt_comp_inv (f : ComplexSphere → ℂ) (p : ComplexSphere) :
    sphereAnalyticOrderAt (f ∘ sphereInv) p = sphereAnalyticOrderAt f (sphereInv p) := by
  induction p using OnePoint.rec with
  | infty =>
    simp [sphereAnalyticOrderAt, sphereInfinityChart, Function.comp_def]
  | coe z =>
    by_cases hz : z = 0
    · subst z
      simp only [sphereInv_zero, sphereAnalyticOrderAt_coe, sphereAnalyticOrderAt_infty,
        sphereInfinityChart, Function.comp_def]
    · rw [sphereInv_coe_of_ne_zero hz, sphereAnalyticOrderAt_coe,
        sphereAnalyticOrderAt_coe]
      have heq : (fun w : ℂ ↦ (f ∘ sphereInv) (↑w)) =ᶠ[𝓝 z]
          ((fun w : ℂ ↦ f (↑w)) ∘ Inv.inv) :=
        (sphereInv_eventually_eq_inv hz).fun_comp f
      rw [analyticOrderAt_congr heq]
      apply analyticOrderAt_comp_of_deriv_ne_zero (analyticAt_inv hz)
      simpa only [deriv_inv] using neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hz))

theorem sphereHolomorphicOn_comp_inv_iff (f : ComplexSphere → ℂ) (Ω : Set ComplexSphere) :
    SphereHolomorphicOn (f ∘ sphereInv) (sphereInv ⁻¹' Ω) ↔ SphereHolomorphicOn f Ω := by
  constructor
  · intro h p hp
    have hi := h (sphereInv p) (by simpa using hp)
    simpa only [sphereAnalyticAt_comp_inv_iff, sphereInv_involutive] using hi
  · intro h p hp
    exact (sphereAnalyticAt_comp_inv_iff f p).2 (h _ hp)

/-- A complex translation extends over infinity. -/
def sphereTranslate (a : ℂ) : ComplexSphere ≃ₜ ComplexSphere :=
  (Homeomorph.addRight a).onePointCongr

@[simp] theorem sphereTranslate_infty (a : ℂ) : sphereTranslate a ∞ = ∞ := rfl

@[simp] theorem sphereTranslate_coe (a z : ℂ) :
    sphereTranslate a (↑z) = (↑(z + a) : ComplexSphere) := rfl

/-- Coordinate expression for translation in the infinity chart. -/
theorem sphereTranslate_infinityChart (a w : ℂ) (hw : 1 + a * w ≠ 0) :
    sphereTranslate a (sphereInfinityChart w) =
      sphereInfinityChart (w / (1 + a * w)) := by
  by_cases hw0 : w = 0
  · subst w; simp
  · rw [sphereInfinityChart_of_ne_zero hw0, sphereTranslate_coe,
      sphereInfinityChart_of_ne_zero (div_ne_zero hw0 hw)]
    congr 1
    field_simp [hw0, hw] <;> ring

theorem sphereTranslate_infinityChart_eventually (a : ℂ) :
    (fun w ↦ sphereTranslate a (sphereInfinityChart w)) =ᶠ[𝓝 (0 : ℂ)]
      (fun w ↦ sphereInfinityChart (w / (1 + a * w))) := by
  have h : ∀ᶠ w in 𝓝 (0 : ℂ), 1 + a * w ≠ 0 :=
    ((continuous_const.add (continuous_const.mul continuous_id)).continuousAt)
      .eventually_ne (by simp)
  filter_upwards [h] with w hw
  exact sphereTranslate_infinityChart a w hw

theorem analyticAt_translation_infinity_coordinate (a : ℂ) :
    AnalyticAt ℂ (fun w ↦ w / (1 + a * w)) 0 := by
  exact analyticAt_id.div (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
    (by simp)

theorem hasDerivAt_translation_infinity_coordinate (a : ℂ) :
    HasDerivAt (fun w ↦ w / (1 + a * w)) 1 0 := by
  simpa using (hasDerivAt_id (0 : ℂ)).div
    ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).add ((hasDerivAt_id (0 : ℂ)).const_mul a))
    (by simp)

/-- Holomorphy in both sphere charts is invariant under translation. -/
theorem sphereAnalyticAt_comp_translate_iff (f : ComplexSphere → ℂ) (a : ℂ)
    (p : ComplexSphere) :
    SphereAnalyticAt (f ∘ sphereTranslate a) p ↔
      SphereAnalyticAt f (sphereTranslate a p) := by
  induction p using OnePoint.rec with
  | infty =>
    rw [sphereTranslate_infty, sphereAnalyticAt_infty, sphereAnalyticAt_infty]
    have heq := (sphereTranslate_infinityChart_eventually a).fun_comp f
    rw [analyticAt_congr heq]
    have hd : deriv (fun w : ℂ ↦ w / (1 + a * w)) 0 ≠ 0 := by
      rw [(hasDerivAt_translation_infinity_coordinate a).deriv]
      exact one_ne_zero
    simpa only [zero_div] using
      (analyticAt_comp_iff_of_deriv_ne_zero (g := f ∘ sphereInfinityChart)
        (analyticAt_translation_infinity_coordinate a) hd)
  | coe z =>
    rw [sphereTranslate_coe, sphereAnalyticAt_coe, sphereAnalyticAt_coe]
    change AnalyticAt ℂ ((fun w : ℂ ↦ f (↑w)) ∘ (fun w ↦ w + a)) z ↔ _
    apply analyticAt_comp_iff_of_deriv_ne_zero (analyticAt_id.add analyticAt_const)
    rw [((hasDerivAt_id z).add_const a).deriv]
    exact one_ne_zero

/-- Zero order in both sphere charts is invariant under translation. -/
theorem sphereAnalyticOrderAt_comp_translate (f : ComplexSphere → ℂ) (a : ℂ)
    (p : ComplexSphere) :
    sphereAnalyticOrderAt (f ∘ sphereTranslate a) p =
      sphereAnalyticOrderAt f (sphereTranslate a p) := by
  induction p using OnePoint.rec with
  | infty =>
    rw [sphereTranslate_infty, sphereAnalyticOrderAt_infty, sphereAnalyticOrderAt_infty]
    have heq := (sphereTranslate_infinityChart_eventually a).fun_comp f
    rw [analyticOrderAt_congr heq]
    have hd : deriv (fun w : ℂ ↦ w / (1 + a * w)) 0 ≠ 0 := by
      rw [(hasDerivAt_translation_infinity_coordinate a).deriv]
      exact one_ne_zero
    simpa only [zero_div] using
      (analyticOrderAt_comp_of_deriv_ne_zero (f := f ∘ sphereInfinityChart)
        (analyticAt_translation_infinity_coordinate a) hd)
  | coe z =>
    rw [sphereTranslate_coe, sphereAnalyticOrderAt_coe, sphereAnalyticOrderAt_coe]
    change analyticOrderAt ((fun w : ℂ ↦ f (↑w)) ∘ (fun w ↦ w + a)) z = _
    apply analyticOrderAt_comp_of_deriv_ne_zero (analyticAt_id.add analyticAt_const)
    rw [((hasDerivAt_id z).add_const a).deriv]
    exact one_ne_zero

/-- A fractional linear map sending the selected pole to infinity. -/
def spherePoleChart (pole : ComplexSphere) : ComplexSphere ≃ₜ ComplexSphere :=
  pole.elim (Homeomorph.refl ComplexSphere)
    (fun a ↦ (sphereTranslate (-a)).trans sphereInvHomeomorph)

@[simp] theorem spherePoleChart_self (pole : ComplexSphere) :
    spherePoleChart pole pole = ∞ := by
  induction pole using OnePoint.rec with
  | infty => rfl
  | coe a => simp [spherePoleChart, sphereInvHomeomorph]

@[simp] theorem spherePoleChart_symm_infty (pole : ComplexSphere) :
    (spherePoleChart pole).symm ∞ = pole := by
  apply (spherePoleChart pole).injective
  simp

theorem sphereAnalyticAt_comp_poleChart_iff (f : ComplexSphere → ℂ)
    (pole p : ComplexSphere) :
    SphereAnalyticAt (f ∘ spherePoleChart pole) p ↔
      SphereAnalyticAt f (spherePoleChart pole p) := by
  induction pole using OnePoint.rec with
  | infty => rfl
  | coe a =>
    change SphereAnalyticAt ((f ∘ sphereInv) ∘ sphereTranslate (-a)) p ↔
      SphereAnalyticAt f (sphereInv (sphereTranslate (-a) p))
    rw [sphereAnalyticAt_comp_translate_iff, sphereAnalyticAt_comp_inv_iff]

theorem sphereAnalyticOrderAt_comp_poleChart (f : ComplexSphere → ℂ)
    (pole p : ComplexSphere) :
    sphereAnalyticOrderAt (f ∘ spherePoleChart pole) p =
      sphereAnalyticOrderAt f (spherePoleChart pole p) := by
  induction pole using OnePoint.rec with
  | infty => rfl
  | coe a =>
    change sphereAnalyticOrderAt ((f ∘ sphereInv) ∘ sphereTranslate (-a)) p =
      sphereAnalyticOrderAt f (sphereInv (sphereTranslate (-a) p))
    rw [sphereAnalyticOrderAt_comp_translate, sphereAnalyticOrderAt_comp_inv]

theorem sphereAnalyticAt_comp_poleChart_symm_iff (f : ComplexSphere → ℂ)
    (pole p : ComplexSphere) :
    SphereAnalyticAt (f ∘ (spherePoleChart pole).symm) p ↔
      SphereAnalyticAt f ((spherePoleChart pole).symm p) := by
  have h := sphereAnalyticAt_comp_poleChart_iff
    (f ∘ (spherePoleChart pole).symm) pole ((spherePoleChart pole).symm p)
  simpa only [Function.comp_def, Homeomorph.symm_apply_apply,
    Homeomorph.apply_symm_apply] using h.symm

theorem sphereAnalyticOrderAt_comp_poleChart_symm (f : ComplexSphere → ℂ)
    (pole p : ComplexSphere) :
    sphereAnalyticOrderAt (f ∘ (spherePoleChart pole).symm) p =
      sphereAnalyticOrderAt f ((spherePoleChart pole).symm p) := by
  have h := sphereAnalyticOrderAt_comp_poleChart
    (f ∘ (spherePoleChart pole).symm) pole ((spherePoleChart pole).symm p)
  simpa only [Function.comp_def, Homeomorph.symm_apply_apply,
    Homeomorph.apply_symm_apply] using h.symm

/-- A global complex coordinate parametrization of the sphere minus `pole`. -/
def spherePlaneParam (pole : ComplexSphere) (z : ℂ) : ComplexSphere :=
  (spherePoleChart pole).symm (↑z)

theorem isOpenEmbedding_spherePlaneParam (pole : ComplexSphere) :
    Topology.IsOpenEmbedding (spherePlaneParam pole) :=
  (spherePoleChart pole).symm.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe

theorem range_spherePlaneParam (pole : ComplexSphere) :
    range (spherePlaneParam pole) = {pole}ᶜ := by
  ext p
  change (∃ z, spherePlaneParam pole z = p) ↔ p ≠ pole
  constructor
  · rintro ⟨z, rfl⟩ hp
    have h := congrArg (spherePoleChart pole) hp
    have : (↑z : ComplexSphere) = ∞ := by simpa [spherePlaneParam] using h
    exact OnePoint.coe_ne_infty z this
  · intro hp
    have hne : spherePoleChart pole p ≠ ∞ := by
      intro h
      apply hp
      apply (spherePoleChart pole).injective
      simpa using h
    obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp hne
    exact ⟨z, by simp [spherePlaneParam, hz]⟩

theorem sphereAnalyticAt_iff_planeParam (f : ComplexSphere → ℂ)
    (pole : ComplexSphere) (z : ℂ) :
    SphereAnalyticAt f (spherePlaneParam pole z) ↔
      AnalyticAt ℂ (f ∘ spherePlaneParam pole) z :=
  (sphereAnalyticAt_comp_poleChart_symm_iff f pole (↑z)).symm

theorem sphereAnalyticOrderAt_planeParam (f : ComplexSphere → ℂ)
    (pole : ComplexSphere) (z : ℂ) :
    sphereAnalyticOrderAt f (spherePlaneParam pole z) =
      analyticOrderAt (f ∘ spherePlaneParam pole) z :=
  (sphereAnalyticOrderAt_comp_poleChart_symm f pole (↑z)).symm

/-- Total extension of a plane-coordinate function. The value at the omitted
pole is arbitrary and is never used in a domain omitting that point. -/
def sphereLiftFromPlane (pole : ComplexSphere) (F : ℂ → ℂ) (p : ComplexSphere) : ℂ :=
  F ((spherePoleChart pole p).elim 0 id)

@[simp] theorem sphereLiftFromPlane_param (pole : ComplexSphere) (F : ℂ → ℂ) (z : ℂ) :
    sphereLiftFromPlane pole F (spherePlaneParam pole z) = F z := by
  simp [sphereLiftFromPlane, spherePlaneParam]

theorem sphereHolomorphic_liftFromPlane {pole : ComplexSphere} {Ω : Set ComplexSphere}
    (hpole : pole ∉ Ω) {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (spherePlaneParam pole ⁻¹' Ω)) :
    SphereHolomorphicOn (sphereLiftFromPlane pole F) Ω := by
  intro p hp
  have hr : p ∈ range (spherePlaneParam pole) := by
    rw [range_spherePlaneParam]
    exact fun h ↦ hpole (h ▸ hp)
  obtain ⟨z, rfl⟩ := hr
  rw [sphereAnalyticAt_iff_planeParam]
  simpa only [Function.comp_def, sphereLiftFromPlane_param] using hF z hp

theorem sphereOrder_liftFromPlane (pole : ComplexSphere) (F : ℂ → ℂ) (z : ℂ) :
    sphereAnalyticOrderAt (sphereLiftFromPlane pole F) (spherePlaneParam pole z) =
      analyticOrderAt F z := by
  rw [sphereAnalyticOrderAt_planeParam]
  simp only [Function.comp_def, sphereLiftFromPlane_param]

/-- Transfer an actual prescribed-zero construction on an omitted-point plane
chart to the full sphere domain. The plane construction is an explicit input
to this helper; this is not the existence theorem 15.11 by itself. -/
theorem sphere_prescribed_zeros_of_plane {pole : ComplexSphere} {Ω A : Set ComplexSphere}
    (hpole : pole ∉ Ω) (hA : A ⊆ Ω) (m : ComplexSphere → ℕ) {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (spherePlaneParam pole ⁻¹' Ω))
    (hzero : ∀ z ∈ spherePlaneParam pole ⁻¹' Ω,
      F z = 0 ↔ spherePlaneParam pole z ∈ A)
    (horder : ∀ z, spherePlaneParam pole z ∈ A →
      analyticOrderAt F z = (m (spherePlaneParam pole z) : ℕ∞)) :
    ∃ f : ComplexSphere → ℂ, SphereHolomorphicOn f Ω ∧
      (∀ p ∈ Ω, f p = 0 ↔ p ∈ A) ∧
      (∀ p ∈ A, sphereAnalyticOrderAt f p = (m p : ℕ∞)) := by
  refine ⟨sphereLiftFromPlane pole F, sphereHolomorphic_liftFromPlane hpole hF, ?_, ?_⟩
  · intro p hp
    have hr : p ∈ range (spherePlaneParam pole) := by
      rw [range_spherePlaneParam]
      exact fun h ↦ hpole (h ▸ hp)
    obtain ⟨z, rfl⟩ := hr
    simpa only [sphereLiftFromPlane_param] using hzero z hp
  · intro p hp
    have hr : p ∈ range (spherePlaneParam pole) := by
      rw [range_spherePlaneParam]
      exact fun h ↦ hpole (h ▸ hA hp)
    obtain ⟨z, rfl⟩ := hr
    rw [sphereOrder_liftFromPlane]
    exact horder z hp

#print axioms sphereInv_involutive
#print axioms continuous_sphereInv
#print axioms sphereAnalyticAt_comp_inv_iff
#print axioms sphereAnalyticOrderAt_comp_inv
#print axioms sphereHolomorphicOn_comp_inv_iff
#print axioms sphereTranslate_infinityChart
#print axioms sphereAnalyticAt_comp_translate_iff
#print axioms sphereAnalyticOrderAt_comp_translate
#print axioms sphereAnalyticAt_comp_poleChart_iff
#print axioms sphereAnalyticOrderAt_comp_poleChart
#print axioms sphereAnalyticAt_iff_planeParam
#print axioms sphereAnalyticOrderAt_planeParam
#print axioms sphereHolomorphic_liftFromPlane
#print axioms sphere_prescribed_zeros_of_plane

end RudinRCA.Chapter15
