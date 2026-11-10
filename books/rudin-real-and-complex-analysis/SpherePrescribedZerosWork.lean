import RudinRCA.Chapter15
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Basic.Denumerable
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact

/- Generated assembly of isolated 15.11 drafts; no compile has yet been run. -/

-- Source draft: SphereWork.lean
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

-- Source draft: BoundaryProductGeometryWork.lean
/-!
Geometry for the normalized proof of Rudin 15.11.

After a point of the domain outside the zero set is moved to infinity, the
finite zero sequence is bounded and the omitted set C is compact. The first
lemma extracts convergence of the nearest-boundary distance from escape from
compact subsets. The remaining lemmas give one-half ratio bounds on compact
plane sets and on a fixed infinity-chart disc. These are the geometric inputs
for the elementary-factor estimate 15.8 and holomorphic product theorem 15.6.

This draft is not a completed prescribed-zero existence theorem.
-/

noncomputable section

open Filter Set Metric Bornology
open scoped Topology

namespace RudinRCA.Chapter15

/-- A bounded zero sequence escaping every compact subset of the domain must
approach its closed complement. Compactness of the complement is not needed
for this particular implication. -/
theorem infDist_tendsto_zero_of_bounded_escape (a : ℕ → ℂ) (C : Set ℂ)
    (R : ℝ) (hbound : ∀ n, ‖a n‖ ≤ R)
    (hescape : ∀ K : Set ℂ, IsCompact K → K ⊆ Cᶜ →
      ∀ᶠ n in atTop, a n ∉ K) :
    Tendsto (fun n ↦ infDist (a n) C) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro r hr
    exact Eventually.of_forall (fun n ↦ hr.trans_le infDist_nonneg)
  · intro ε hε
    let K : Set ℂ := closedBall 0 R ∩ {z | ε ≤ infDist z C}
    have hK : IsCompact K :=
      (isCompact_closedBall 0 R).inter_right
        (isClosed_le continuous_const (continuous_infDist_pt C))
    have hKC : K ⊆ Cᶜ := by
      intro z hz hzin
      have h := hz.2
      rw [infDist_zero_of_mem hzin] at h
      exact (not_le_of_gt hε) h
    filter_upwards [hescape K hK hKC] with n hn
    apply lt_of_not_ge
    intro h
    exact hn ⟨by simpa only [mem_closedBall, dist_zero_right] using hbound n, h⟩

/-- A nearest-point choice gives an actual small complex difference. -/
theorem nearest_boundary_difference_tendsto_zero (a b : ℕ → ℂ) (C : Set ℂ)
    (hnearest : ∀ n, infDist (a n) C = dist (a n) (b n))
    (h : Tendsto (fun n ↦ infDist (a n) C) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0) := by
  simpa only [hnearest, dist_eq_norm] using h

/-- Uniform positive distance from a compact set to a disjoint nonempty closed set. -/
theorem compact_infDist_lower_bound {C K : Set ℂ} (hC : IsClosed C)
    (hCne : C.Nonempty) (hK : IsCompact K) (hKC : K ⊆ Cᶜ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, δ ≤ infDist z C := by
  apply hK.exists_forall_le' (continuous_infDist_pt C).continuousOn
  intro z hz
  exact (hC.notMem_iff_infDist_pos hCne).1 (hKC hz)

/-- The pole factors' arguments eventually have norm at most one half on every
compact subset of the domain. -/
theorem boundary_ratios_small_on_compact (a b : ℕ → ℂ) {C K : Set ℂ}
    (hC : IsClosed C) (hCne : C.Nonempty) (hb : ∀ n, b n ∈ C)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0))
    (hK : IsCompact K) (hKC : K ⊆ Cᶜ) :
    ∀ᶠ n in atTop, ∀ z ∈ K, ‖(a n - b n) / (z - b n)‖ ≤ (1 / 2 : ℝ) := by
  obtain ⟨δ, hδ, hδK⟩ := compact_infDist_lower_bound hC hCne hK hKC
  filter_upwards [(tendsto_order.1 hsmall).2 (δ / 2) (half_pos hδ)] with n hn
  intro z hz
  have hden : δ ≤ ‖z - b n‖ :=
    (hδK z hz).trans (by simpa only [dist_eq_norm] using infDist_le_dist_of_mem (hb n))
  rw [norm_div, div_le_iff₀ (hδ.trans_le hden)]
  linarith

/-- A uniform pole bound supplies a single infinity-chart disc on which all
denominators are nonzero. -/
theorem exists_infinity_disc_denominator_lower_bound (b : ℕ → ℂ)
    (B : ℝ) (hB : 0 < B) (hb : ∀ n, ‖b n‖ ≤ B) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ n (w : ℂ), ‖w‖ ≤ ρ → (1 / 2 : ℝ) ≤ ‖1 - b n * w‖ := by
  let ρ : ℝ := min 1 (1 / (2 * B))
  have hρ : 0 < ρ := lt_min zero_lt_one (one_div_pos.2 (by positivity))
  refine ⟨ρ, hρ, min_le_left _ _, ?_⟩
  intro n w hw
  have hmul : ‖b n * w‖ ≤ (1 / 2 : ℝ) := by
    calc
      ‖b n * w‖ = ‖b n‖ * ‖w‖ := norm_mul _ _
      _ ≤ B * (1 / (2 * B)) :=
        mul_le_mul (hb n) (hw.trans (min_le_right _ _)) (norm_nonneg _) hB.le
      _ = 1 / 2 := by field_simp [hB.ne']
  have h := norm_sub_norm_le (1 : ℂ) (b n * w)
  norm_num only [norm_one] at h
  linarith

/-- The same one-half ratio estimate holds on a fixed neighborhood of infinity,
using its actual local coordinate w=1/z and the exact rational expression. -/
theorem boundary_ratios_small_at_infinity (a b : ℕ → ℂ)
    (B : ℝ) (hB : 0 < B) (hb : ∀ n, ‖b n‖ ≤ B)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ n (w : ℂ), ‖w‖ ≤ ρ → 1 - b n * w ≠ 0) ∧
      (∀ᶠ n in atTop, ∀ w : ℂ, ‖w‖ ≤ ρ →
        ‖(a n - b n) * w / (1 - b n * w)‖ ≤ (1 / 2 : ℝ)) := by
  obtain ⟨ρ, hρ, hρ1, hden⟩ :=
    exists_infinity_disc_denominator_lower_bound b B hB hb
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro n w hw hzero
    have h := hden n w hw
    simpa [hzero] using h
  · filter_upwards [(tendsto_order.1 hsmall).2 (1 / 4) (by norm_num)] with n hn
    intro w hw
    have hd := hden n w hw
    have hdpos : 0 < ‖1 - b n * w‖ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hd
    rw [norm_div, div_le_iff₀ hdpos, norm_mul]
    have hnum : ‖a n - b n‖ * ‖w‖ ≤ (1 / 4 : ℝ) := by
      calc
        ‖a n - b n‖ * ‖w‖ ≤ (1 / 4 : ℝ) * 1 :=
          mul_le_mul hn.le (hw.trans hρ1) (norm_nonneg _) (by norm_num)
        _ = 1 / 4 := mul_one _
    linarith

#print axioms infDist_tendsto_zero_of_bounded_escape
#print axioms nearest_boundary_difference_tendsto_zero
#print axioms boundary_ratios_small_on_compact
#print axioms exists_infinity_disc_denominator_lower_bound
#print axioms boundary_ratios_small_at_infinity

end RudinRCA.Chapter15

-- Source draft: ZeroSetNormalizationWork.lean
/-! Topological normalization of the full sphere data in Rudin 15.11. Draft. -/

noncomputable section

open Filter Set Bornology
open scoped Topology OnePoint

namespace RudinRCA.Chapter15

def NoAccumulationIn (A Ω : Set ComplexSphere) : Prop :=
  ∀ p ∈ Ω, ¬ AccPt p (𝓟 A)

/-- A nonempty open domain with a prescribed discrete zero set always contains
a point outside that set. This also works when the starting point is infinity. -/
theorem exists_domain_point_outside_zeros {Ω A : Set ComplexSphere}
    (hΩ : IsOpen Ω) (hΩne : Ω.Nonempty) (hno : NoAccumulationIn A Ω) :
    ∃ pole ∈ Ω, pole ∉ A := by
  obtain ⟨p, hp⟩ := hΩne
  have hnot : ∀ᶠ q in 𝓝[≠] p, q ∉ A := by
    simpa only [accPt_iff_frequently_nhdsNE, not_frequently] using hno p hp
  have hmem : ∀ᶠ q in 𝓝[≠] p, q ∈ Ω :=
    (hΩ.mem_nhds hp).filter_mono nhdsWithin_le_nhds
  exact (hmem.and hnot).exists

theorem normalized_complement_isCompact {Ω : Set ComplexSphere}
    (hΩ : IsOpen Ω) {pole : ComplexSphere} (hpole : pole ∈ Ω) :
    IsCompact (spherePlaneParam pole ⁻¹' Ω)ᶜ := by
  let U : Set ComplexSphere := (spherePoleChart pole).symm ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage (spherePoleChart pole).symm.continuous
  have hinfty : (∞ : ComplexSphere) ∈ U := by simpa [U] using hpole
  exact ((OnePoint.isOpen_iff_of_mem' hinfty).1 hU).1

theorem normalized_domain_eq {Ω : Set ComplexSphere} {pole : ComplexSphere}
    (hpole : pole ∈ Ω) :
    (((↑) : ℂ → ComplexSphere) '' (spherePlaneParam pole ⁻¹' Ω)ᶜ)ᶜ =
      (spherePoleChart pole).symm ⁻¹' Ω := by
  ext p
  induction p using OnePoint.rec with
  | infty => simp [hpole]
  | coe z =>
    simp only [mem_compl_iff, mem_image, OnePoint.coe_eq_coe, exists_eq_right,
      mem_preimage, not_not, spherePlaneParam]

theorem normalized_complement_nonempty {Ω : Set ComplexSphere}
    (hproper : Ω ≠ univ) {pole : ComplexSphere} (hpole : pole ∈ Ω) :
    ((spherePlaneParam pole ⁻¹' Ω)ᶜ).Nonempty := by
  obtain ⟨p, hp⟩ := ne_univ_iff_exists_notMem.mp hproper
  have hpp : p ≠ pole := fun h ↦ hp (h.symm ▸ hpole)
  have hr : p ∈ range (spherePlaneParam pole) := by
    rw [range_spherePlaneParam]
    exact hpp
  obtain ⟨z, hz⟩ := hr
  exact ⟨z, by simpa [mem_preimage, hz] using hp⟩

theorem normalized_zeros_no_accumulation {Ω A : Set ComplexSphere}
    (hno : NoAccumulationIn A Ω) (pole : ComplexSphere) :
    ∀ z ∈ spherePlaneParam pole ⁻¹' Ω,
      ¬ AccPt z (𝓟 (spherePlaneParam pole ⁻¹' A)) := by
  intro z hz hacc
  apply hno (spherePlaneParam pole z) hz
  apply (isOpenEmbedding_spherePlaneParam pole).accPt_comap_iff.mp
  simpa only [comap_principal] using hacc

theorem normalized_zeros_isDiscrete {Ω A : Set ComplexSphere}
    (hA : A ⊆ Ω) (hno : NoAccumulationIn A Ω) (pole : ComplexSphere) :
    IsDiscrete (spherePlaneParam pole ⁻¹' A) := by
  apply isDiscrete_iff_nhdsNE.2
  intro z hz
  have h := normalized_zeros_no_accumulation hno pole z (hA hz)
  simpa only [AccPt, not_neBot] using h

theorem normalized_zeros_countable {Ω A : Set ComplexSphere}
    (hA : A ⊆ Ω) (hno : NoAccumulationIn A Ω) (pole : ComplexSphere) :
    (spherePlaneParam pole ⁻¹' A).Countable :=
  (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (normalized_zeros_isDiscrete hA hno pole)

/-- Moving a domain point outside A to infinity makes the finite zero set
bounded, which is needed by the printed boundary-pole construction. -/
theorem normalized_zeros_isBounded {Ω A : Set ComplexSphere}
    (hno : NoAccumulationIn A Ω) {pole : ComplexSphere}
    (hpole : pole ∈ Ω) (hpoleA : pole ∉ A) :
    IsBounded (spherePlaneParam pole ⁻¹' A) := by
  have hpcl : pole ∉ closure A := by
    intro h
    have hcp := mem_closure_iff_clusterPt.mp h
    exact (clusterPt_principal.mp hcp).elim hpoleA (hno pole hpole)
  have hcompact : IsCompact (spherePlaneParam pole ⁻¹' (closure A)ᶜ)ᶜ :=
    normalized_complement_isCompact isClosed_closure.isOpen_compl hpcl
  apply hcompact.isBounded.subset
  intro z hz
  exact fun h ↦ h (subset_closure hz)

/-- No accumulation points in the domain implies finite intersection with
every compact subset, in any topological space. -/
theorem finite_inter_compact_of_no_accumulation {X : Type*} [TopologicalSpace X]
    {A Ω K : Set X} (hno : ∀ x ∈ Ω, ¬ AccPt x (𝓟 A))
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) : (A ∩ K).Finite := by
  by_contra hinfinite
  obtain ⟨x, hxK, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinfinite hK inter_subset_right
  exact hno x (hKΩ hxK) (hx.mono (principal_mono.2 inter_subset_left))

#print axioms exists_domain_point_outside_zeros
#print axioms normalized_complement_isCompact
#print axioms normalized_domain_eq
#print axioms normalized_complement_nonempty
#print axioms normalized_zeros_countable
#print axioms normalized_zeros_isBounded
#print axioms finite_inter_compact_of_no_accumulation

end RudinRCA.Chapter15

-- Source draft: ZeroMultiplicityEnumerationWork.lean
/-! Enumeration of a discrete set with arbitrary positive finite multiplicities. Draft. -/

noncomputable section

open Filter Set
open scoped Topology

namespace RudinRCA.Chapter15

def ZeroCopy (A : Set ℂ) (m : ℂ → ℕ) := Σ a : A, Fin (m a)

def zeroCopyValue {A : Set ℂ} {m : ℂ → ℕ} (i : ZeroCopy A m) : ℂ := i.1

def zeroCopyFiberEquiv {A : Set ℂ} {m : ℂ → ℕ} {z : ℂ} (hz : z ∈ A) :
    {i : ZeroCopy A m // zeroCopyValue i = z} ≃ Fin (m z) where
  toFun i := ⟨i.1.2, by simpa only [← i.2] using i.1.2.isLt⟩
  invFun j := ⟨⟨⟨z, hz⟩, j⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨⟨a, ha⟩, j⟩, h⟩
    change a = z at h
    subst a
    rfl
  right_inv := by intro j; rfl

theorem finite_zeroCopy_fiber (A : Set ℂ) (m : ℂ → ℕ) (z : ℂ) :
    Finite {i : ZeroCopy A m // zeroCopyValue i = z} := by
  by_cases hz : z ∈ A
  · exact Finite.of_equiv (Fin (m z)) (zeroCopyFiberEquiv hz).symm
  · haveI : IsEmpty {i : ZeroCopy A m // zeroCopyValue i = z} :=
      ⟨fun i ↦ hz (i.2 ▸ i.1.1.property)⟩
    infer_instance

theorem zeroCopy_range {A : Set ℂ} {m : ℂ → ℕ} (hm : ∀ z ∈ A, 0 < m z) :
    range (@zeroCopyValue A m) = A := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact i.1.property
  · intro hz
    exact ⟨⟨⟨z, hz⟩, ⟨0, hm z hz⟩⟩, rfl⟩

/-- Counting the finite multiplicity fiber gives an actual convergent natural
sum, without an implicit summability assumption. -/
theorem zeroCopy_indicator_hasSum {A : Set ℂ} {m : ℂ → ℕ} {z : ℂ} (hz : z ∈ A) :
    HasSum (fun i : ZeroCopy A m ↦ if z = zeroCopyValue i then (1 : ℕ) else 0) (m z) := by
  classical
  let S : Set (ZeroCopy A m) := {i | zeroCopyValue i = z}
  haveI : Finite S := finite_zeroCopy_fiber A m z
  letI : Fintype S := Fintype.ofFinite S
  have hcard : Fintype.card S = m z := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (zeroCopyFiberEquiv (m := m) hz)
  have hs : Function.support
      (fun i : ZeroCopy A m ↦ if z = zeroCopyValue i then (1 : ℕ) else 0) ⊆ S := by
    intro i hi
    by_contra h
    exact hi (if_neg (Ne.symm h))
  apply (hasSum_subtype_iff_of_support_subset hs).1
  have hone : (fun i : S ↦ if z = zeroCopyValue i.1 then (1 : ℕ) else 0) = fun _ ↦ 1 := by
    funext i
    simp only [i.2, if_pos rfl]
  simpa only [Function.comp_def, hone, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, nsmul_eq_mul, mul_one, hcard] using (hasSum_fintype (fun _ : S ↦ (1 : ℕ)))

/-- Every compact subset of the domain contains finitely many multiplicity
copies, even when the multiplicities are not uniformly bounded. -/
theorem finite_zeroCopy_preimage_compact {A Ω K : Set ℂ} {m : ℂ → ℕ}
    (hno : ∀ z ∈ Ω, ¬ AccPt z (𝓟 A)) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    {i : ZeroCopy A m | zeroCopyValue i ∈ K}.Finite := by
  have hAK := finite_inter_compact_of_no_accumulation hno hK hKΩ
  have hpre : ((@zeroCopyValue A m) ⁻¹' (A ∩ K)).Finite :=
    hAK.preimage' (fun z _ ↦ finite_zeroCopy_fiber A m z)
  apply hpre.subset
  intro i hi
  exact ⟨i.1.property, hi⟩

/-- Reindex all copies by the naturals in the infinite case. The enumeration
has exact prescribed multiplicities and escapes every compact domain subset. -/
theorem exists_zero_enumeration {A Ω : Set ℂ} {m : ℂ → ℕ}
    (hAcount : A.Countable) (hm : ∀ z ∈ A, 0 < m z)
    (hno : ∀ z ∈ Ω, ¬ AccPt z (𝓟 A)) [Infinite (ZeroCopy A m)] :
    ∃ a : ℕ → ℂ, range a = A ∧
      (∀ z ∈ A, HasSum (fun n ↦ if z = a n then (1 : ℕ) else 0) (m z)) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∀ᶠ n in atTop, a n ∉ K) := by
  classical
  haveI : Countable A := hAcount.to_subtype
  haveI : Countable (ZeroCopy A m) := by unfold ZeroCopy; infer_instance
  let e : ℕ ≃ ZeroCopy A m := Classical.choice inferInstance
  let a : ℕ → ℂ := fun n ↦ zeroCopyValue (e n)
  refine ⟨a, ?_, ?_, ?_⟩
  · change range ((@zeroCopyValue A m) ∘ e) = A
    rw [e.surjective.range_comp, zeroCopy_range hm]
  · intro z hz
    exact e.hasSum_iff.2 (zeroCopy_indicator_hasSum hz)
  · intro K hK hKΩ
    have hc := finite_zeroCopy_preimage_compact (m := m) hno hK hKΩ
    have hn : {n : ℕ | a n ∈ K}.Finite := hc.preimage e.injective.injOn
    simpa only [Nat.cofinite_eq_atTop] using hn.eventually_cofinite_notMem

#print axioms finite_zeroCopy_fiber
#print axioms zeroCopy_indicator_hasSum
#print axioms finite_zeroCopy_preimage_compact
#print axioms exists_zero_enumeration

end RudinRCA.Chapter15

-- Source draft: BoundaryProductWork.lean
/-! The normalized boundary-pole product for Rudin 15.11. Draft, not yet checked. -/

noncomputable section

open Filter Set Finset Metric
open scoped Topology OnePoint

namespace RudinRCA.Chapter15

def boundaryFactor (p : ℕ) (a b z : ℂ) : ℂ :=
  elementaryFactor p ((a - b) / (z - b))

def boundaryInfinityFactor (p : ℕ) (a b w : ℂ) : ℂ :=
  elementaryFactor p ((a - b) * w / (1 - b * w))

theorem analyticAt_boundaryFactor (p : ℕ) (a b : ℂ) {z : ℂ} (hzb : z ≠ b) :
    AnalyticAt ℂ (boundaryFactor p a b) z := by
  exact ((differentiable_elementaryFactor p).analyticAt ((a - b) / (z - b))).comp
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzb))

theorem analyticOrderAt_boundaryFactor (p : ℕ) {a b z : ℂ} (hab : a ≠ b) (hzb : z ≠ b) :
    analyticOrderAt (boundaryFactor p a b) z = if z = a then 1 else 0 := by
  have hg : AnalyticAt ℂ (fun w : ℂ ↦ (a - b) / (w - b)) z :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzb)
  have hd : HasDerivAt (fun w : ℂ ↦ (a - b) / (w - b))
      (-(a - b) / (z - b) ^ 2) z := by
    simpa using (hasDerivAt_const z (a - b)).div ((hasDerivAt_id z).sub_const b)
      (sub_ne_zero.mpr hzb)
  change analyticOrderAt (elementaryFactor p ∘ (fun w : ℂ ↦ (a - b) / (w - b))) z = _
  rw [analyticOrderAt_comp_of_deriv_ne_zero hg (by rw [hd.deriv];
    exact div_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr hab))
      (pow_ne_zero 2 (sub_ne_zero.mpr hzb))), analyticOrderAt_elementaryFactor]
  simp only [div_eq_one_iff_eq (sub_ne_zero.mpr hzb), sub_left_inj, eq_comm]

theorem boundaryFactor_eq_zero_iff (p : ℕ) (a b : ℂ) {z : ℂ} (hzb : z ≠ b) :
    boundaryFactor p a b z = 0 ↔ z = a := by
  simp only [boundaryFactor, elementaryFactor_eq_zero_iff,
    div_eq_one_iff_eq (sub_ne_zero.mpr hzb), sub_left_inj, eq_comm]

theorem component_nonzero_of_order_ne_top {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hfinite : ∀ z ∈ Ω, analyticOrderAt f z ≠ ⊤) :
    ∀ z ∈ Ω, ∃ w ∈ connectedComponentIn Ω z, f w ≠ 0 := by
  intro z hz
  by_contra hn
  push_neg at hn
  apply hfinite z hz
  apply analyticOrderAt_eq_top.mpr
  filter_upwards [hΩ.connectedComponentIn.mem_nhds (mem_connectedComponentIn hz)] with w hw
  exact hn w hw

theorem boundary_errors_locally_uniform (a b : ℕ → ℂ) {C : Set ℂ}
    (hC : IsClosed C) (hCne : C.Nonempty) (hb : ∀ n, b n ∈ C)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0)) :
    TendstoLocallyUniformlyOn
      (fun N z ↦ ∑ n ∈ range N, ‖1 - boundaryFactor n (a n) (b n) z‖)
      (fun z ↦ ∑' n, ‖1 - boundaryFactor n (a n) (b n) z‖) atTop Cᶜ := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hC.isOpen_compl).2
  intro K hKC hK
  have hgeo : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1)) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).comp_injective
      (fun n m h ↦ Nat.add_right_cancel h)
  apply tendstoUniformlyOn_tsum_nat_eventually hgeo
  filter_upwards [boundary_ratios_small_on_compact a b hC hCne hb hsmall hK hKC]
    with n hn z hz
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact (norm_one_sub_elementaryFactor_le n _ ((hn z hz).trans (by norm_num))).trans
    (pow_le_pow_left₀ (norm_nonneg _) (hn z hz))

/-- The finite-plane part of the normalized construction, with repeated zeros
counted by the exact indicator sum. -/
theorem boundary_product_on_complement (a b : ℕ → ℂ) {C : Set ℂ}
    (hC : IsClosed C) (hCne : C.Nonempty) (ha : ∀ n, a n ∉ C) (hb : ∀ n, b n ∈ C)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0)) :
    let f := fun z ↦ ∏' n, boundaryFactor n (a n) (b n) z
    TendstoLocallyUniformlyOn
      (fun N z ↦ ∏ n ∈ range N, boundaryFactor n (a n) (b n) z) f atTop Cᶜ ∧
    DifferentiableOn ℂ f Cᶜ ∧
    ∀ z ∈ Cᶜ, (f z = 0 ↔ ∃ n, z = a n) ∧ analyticOrderAt f z ≠ ⊤ ∧
      analyticOrderNatAt f z = ∑' n, if z = a n then (1 : ℕ) else 0 := by
  let F : ℕ → ℂ → ℂ := fun n z ↦ boundaryFactor n (a n) (b n) z
  have hab (n : ℕ) : a n ≠ b n := fun h ↦ ha n (h.symm ▸ hb n)
  have hzb {z : ℂ} (hz : z ∈ Cᶜ) (n : ℕ) : z ≠ b n := fun h ↦ hz (h.symm ▸ hb n)
  have hF : ∀ n, DifferentiableOn ℂ (F n) Cᶜ := by
    intro n z hz
    exact (analyticAt_boundaryFactor n (a n) (b n) (hzb hz n)).differentiableAt
      .differentiableWithinAt
  have hnonzero : ∀ n z, z ∈ Cᶜ →
      ∃ w ∈ connectedComponentIn Cᶜ z, F n w ≠ 0 := by
    intro n
    apply component_nonzero_of_order_ne_top hC.isOpen_compl
    intro z hz
    rw [show analyticOrderAt (F n) z = if z = a n then 1 else 0 from
      analyticOrderAt_boundaryFactor n (hab n) (hzb hz n)]
    split_ifs <;> simp
  have herr := boundary_errors_locally_uniform a b hC hCne hb hsmall
  obtain ⟨hlim, hhol, horder⟩ := holomorphic_product_multiplicity
    hC.isOpen_compl hF hnonzero ⟨_, herr⟩
  refine ⟨hlim, hhol, ?_⟩
  intro z hz
  obtain ⟨_, hfinite, hm, _⟩ := horder z hz
  have hsum : Summable (fun n ↦ ‖F n z - 1‖) := by
    simpa only [norm_sub_rev] using
      ((hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ norm_nonneg _) _).2
        (herr.tendsto_at hz)).summable
  have hzero : (∏' n, F n z) = 0 ↔ ∃ n, z = a n := by
    constructor
    · intro hprod
      by_contra hn
      push_neg at hn
      have hnone : ∀ n, F n z ≠ 0 := by
        intro n
        exact fun h ↦ hn n ((boundaryFactor_eq_zero_iff n (a n) (b n) (hzb hz n)).1 h)
      have hone (v : ℂ) : 1 + (v - 1) = v := by ring
      have hnz := tprod_one_add_ne_zero_of_summable
        (fun n ↦ by simpa only [hone] using hnone n) hsum
      exact hnz (by simpa only [hone] using hprod)
    · rintro ⟨n, hn⟩
      exact tprod_of_exists_eq_zero ⟨n,
        (boundaryFactor_eq_zero_iff n (a n) (b n) (hzb hz n)).2 hn⟩
  refine ⟨hzero, hfinite, ?_⟩
  rw [hm]
  apply tsum_congr
  intro n
  simp only [F, analyticOrderNatAt, analyticOrderAt_boundaryFactor n (hab n) (hzb hz n)]
  split_ifs <;> simp

theorem boundaryFactor_at_inv (p : ℕ) (a b : ℂ) {w : ℂ} (hw : w ≠ 0) :
    boundaryFactor p a b w⁻¹ = boundaryInfinityFactor p a b w := by
  unfold boundaryFactor boundaryInfinityFactor
  congr 1
  have hden : w⁻¹ - b = (1 - b * w) / w := by field_simp [hw]
  rw [hden, div_div_eq_mul_div]

@[simp] theorem boundaryInfinityFactor_zero (p : ℕ) (a b : ℂ) :
    boundaryInfinityFactor p a b 0 = 1 := by
  simp [boundaryInfinityFactor, elementaryFactor, elementaryExponent]

/-- The normalized product is analytic in a neighborhood of infinity in its
actual local coordinate, and takes value one there. -/
theorem boundary_product_analytic_infinity (a b : ℕ → ℂ)
    (B : ℝ) (hB : 0 < B) (hb : ∀ n, ‖b n‖ ≤ B)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0)) :
    AnalyticAt ℂ (fun w ↦ ∏' n, boundaryInfinityFactor n (a n) (b n) w) 0 := by
  obtain ⟨ρ, hρ, hden, hratio⟩ := boundary_ratios_small_at_infinity a b B hB hb hsmall
  let F : ℕ → ℂ → ℂ := fun n w ↦ boundaryInfinityFactor n (a n) (b n) w
  have hF : ∀ n, DifferentiableOn ℂ (F n) (ball 0 ρ) := by
    intro n w hw
    have hd : 1 - b n * w ≠ 0 := hden n w (by simpa using (mem_ball_zero_iff.mp hw).le)
    apply DifferentiableAt.differentiableWithinAt
    apply AnalyticAt.differentiableAt
    exact ((differentiable_elementaryFactor n).analyticAt
      ((a n - b n) * w / (1 - b n * w))).comp
      ((analyticAt_const.mul analyticAt_id).div
        (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) hd)
  have hgeo : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1)) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).comp_injective
      (fun n m h ↦ Nat.add_right_cancel h)
  have herr : TendstoUniformlyOn
      (fun N w ↦ ∑ n ∈ range N, ‖F n w - 1‖)
      (fun w ↦ ∑' n, ‖F n w - 1‖) atTop (ball 0 ρ) := by
    apply tendstoUniformlyOn_tsum_nat_eventually hgeo
    filter_upwards [hratio] with n hn w hw
    have hr := hn w (mem_ball_zero_iff.mp hw).le
    rw [Real.norm_of_nonneg (norm_nonneg _), norm_sub_rev]
    exact (norm_one_sub_elementaryFactor_le n _ (hr.trans (by norm_num))).trans
      (pow_le_pow_left₀ (norm_nonneg _) hr)
  have h := holomorphic_product_of_uniform_norm_series_using_15_4
    (fun _ u A hb hc ↦ uniform_product_of_uniform_norm_series u A hb hc)
    isOpen_ball hF herr.tendstoLocallyUniformlyOn
  exact h.2.1.analyticAt (isOpen_ball.mem_nhds (by simpa using hρ))

def boundarySphereProduct (a b : ℕ → ℂ) (p : ComplexSphere) : ℂ :=
  p.elim 1 (fun z ↦ ∏' n, boundaryFactor n (a n) (b n) z)

@[simp] theorem boundarySphereProduct_infty (a b : ℕ → ℂ) :
    boundarySphereProduct a b ∞ = 1 := rfl

@[simp] theorem boundarySphereProduct_coe (a b : ℕ → ℂ) (z : ℂ) :
    boundarySphereProduct a b (↑z) = ∏' n, boundaryFactor n (a n) (b n) z := rfl

theorem boundarySphereProduct_infinity_chart (a b : ℕ → ℂ) :
    boundarySphereProduct a b ∘ sphereInfinityChart =
      fun w ↦ ∏' n, boundaryInfinityFactor n (a n) (b n) w := by
  funext w
  by_cases hw : w = 0
  · subst w; simp
  · simp only [Function.comp_def, sphereInfinityChart_of_ne_zero hw,
      boundarySphereProduct_coe, boundaryFactor_at_inv _ _ _ hw]

theorem normalized_boundarySphereProduct_holomorphic (a b : ℕ → ℂ) {C : Set ℂ}
    (hC : IsCompact C) (hCne : C.Nonempty) (ha : ∀ n, a n ∉ C) (hb : ∀ n, b n ∈ C)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0)) :
    SphereHolomorphicOn (boundarySphereProduct a b)
      (((↑) : ℂ → ComplexSphere) '' C)ᶜ := by
  have hplane := (boundary_product_on_complement a b hC.isClosed hCne ha hb hsmall).2.1
  obtain ⟨B, hB, hbound⟩ := hC.isBounded.exists_pos_norm_le
  intro p hp
  induction p using OnePoint.rec with
  | infty =>
    rw [sphereAnalyticAt_infty, boundarySphereProduct_infinity_chart]
    exact boundary_product_analytic_infinity a b B hB (fun n ↦ hbound (b n) (hb n)) hsmall
  | coe z =>
    rw [sphereAnalyticAt_coe]
    have hz : z ∈ Cᶜ := by
      intro h
      exact hp ⟨z, h, rfl⟩
    exact hplane.analyticAt (hC.isClosed.isOpen_compl.mem_nhds hz)

def boundarySphereFactor (n : ℕ) (a b : ℂ) (p : ComplexSphere) : ℂ :=
  p.elim 1 (boundaryFactor n a b)

@[simp] theorem boundarySphereFactor_infty (n : ℕ) (a b : ℂ) :
    boundarySphereFactor n a b ∞ = 1 := rfl

@[simp] theorem boundarySphereFactor_coe (n : ℕ) (a b z : ℂ) :
    boundarySphereFactor n a b (↑z) = boundaryFactor n a b z := rfl

theorem boundarySphereFactor_infinity_chart (n : ℕ) (a b : ℂ) :
    boundarySphereFactor n a b ∘ sphereInfinityChart = boundaryInfinityFactor n a b := by
  funext w
  by_cases hw : w = 0
  · subst w; simp
  · simp only [Function.comp_def, sphereInfinityChart_of_ne_zero hw,
      boundarySphereFactor_coe, boundaryFactor_at_inv _ _ _ hw]

theorem boundarySphereFactor_holomorphic (n : ℕ) (a b : ℂ) {C : Set ℂ} (hb : b ∈ C) :
    SphereHolomorphicOn (boundarySphereFactor n a b) (((↑) : ℂ → ComplexSphere) '' C)ᶜ := by
  intro p hp
  induction p using OnePoint.rec with
  | infty =>
    rw [sphereAnalyticAt_infty, boundarySphereFactor_infinity_chart]
    exact ((differentiable_elementaryFactor n).analyticAt
      ((a - b) * (0 : ℂ) / (1 - b * 0))).comp
      ((analyticAt_const.mul analyticAt_id).div
        (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (by simp))
  | coe z =>
    rw [sphereAnalyticAt_coe]
    exact analyticAt_boundaryFactor n a b (fun h ↦ hp ⟨b, hb, by simp [h]⟩)

theorem sphereHolomorphicOn_finset_product {ι : Type*} (s : Finset ι)
    (F : ι → ComplexSphere → ℂ) {Ω : Set ComplexSphere}
    (hF : ∀ i ∈ s, SphereHolomorphicOn (F i) Ω) :
    SphereHolomorphicOn (fun p ↦ ∏ i ∈ s, F i p) Ω := by
  intro p hp
  induction p using OnePoint.rec with
  | infty =>
    change AnalyticAt ℂ (fun w ↦ ∏ i ∈ s, F i (sphereInfinityChart w)) 0
    exact s.analyticAt_fun_prod (fun i hi ↦ hF i hi ∞ hp)
  | coe z =>
    change AnalyticAt ℂ (fun w : ℂ ↦ ∏ i ∈ s, F i (↑w)) z
    exact s.analyticAt_fun_prod (fun i hi ↦ hF i hi (↑z) hp)

#print axioms analyticOrderAt_boundaryFactor
#print axioms boundary_product_on_complement
#print axioms boundary_product_analytic_infinity
#print axioms normalized_boundarySphereProduct_holomorphic
#print axioms boundarySphereFactor_holomorphic
#print axioms sphereHolomorphicOn_finset_product

end RudinRCA.Chapter15

-- Source draft: PrescribedZerosWork.lean
/-!
Full assembly target for Rudin 15.11, including proper open sphere domains,
arbitrary positive multiplicities, and finite and empty prescribed zero sets.
This file and its scratch prerequisites are drafts awaiting serialized checks.
-/

noncomputable section

open Filter Set Finset Metric Bornology
open scoped Topology OnePoint

namespace RudinRCA.Chapter15

/-- The normalized existence theorem. The omitted set is a nonempty compact
plane set; prescribed zeros are bounded and have no domain accumulation. -/
theorem normalized_prescribed_zeros {C S : Set ℂ}
    (hC : IsCompact C) (hCne : C.Nonempty) (hS : S ⊆ Cᶜ)
    (hScount : S.Countable) (hSbound : IsBounded S)
    (hno : ∀ z ∈ Cᶜ, ¬ AccPt z (𝓟 S)) (m : ℂ → ℕ) (hm : ∀ z ∈ S, 0 < m z) :
    ∃ g : ComplexSphere → ℂ,
      SphereHolomorphicOn g (((↑) : ℂ → ComplexSphere) '' C)ᶜ ∧ g ∞ = 1 ∧
      (∀ z ∈ Cᶜ, g (↑z) = 0 ↔ z ∈ S) ∧
      (∀ z ∈ S, sphereAnalyticOrderAt g (↑z) = (m z : ℕ∞)) := by
  classical
  cases finite_or_infinite (ZeroCopy S m) with
  | inl hfinite =>
    letI := hfinite
    letI : Fintype (ZeroCopy S m) := Fintype.ofFinite _
    obtain ⟨b, hb⟩ := hCne
    let F : ZeroCopy S m → ComplexSphere → ℂ :=
      fun i ↦ boundarySphereFactor 0 (zeroCopyValue i) b
    let g : ComplexSphere → ℂ := fun p ↦ ∏ i : ZeroCopy S m, F i p
    have hgb : SphereHolomorphicOn g (((↑) : ℂ → ComplexSphere) '' C)ᶜ :=
      sphereHolomorphicOn_finset_product univ F
        (fun i _ ↦ boundarySphereFactor_holomorphic 0 (zeroCopyValue i) b hb)
    refine ⟨g, hgb, by simp [g, F], ?_, ?_⟩
    · intro z hz
      have hzb : z ≠ b := fun h ↦ hz (h.symm ▸ hb)
      change (∏ i : ZeroCopy S m, boundaryFactor 0 (zeroCopyValue i) b z) = 0 ↔ z ∈ S
      rw [Finset.prod_eq_zero_iff]
      constructor
      · rintro ⟨i, _, hi⟩
        have heq := (boundaryFactor_eq_zero_iff 0 (zeroCopyValue i) b hzb).1 hi
        exact heq.symm ▸ i.1.property
      · intro hzS
        obtain ⟨i, hi⟩ := (zeroCopy_range (m := m) hm).symm ▸ hzS
        exact ⟨i, mem_univ _, (boundaryFactor_eq_zero_iff 0 (zeroCopyValue i) b hzb).2 hi.symm⟩
    · intro z hz
      have hzb : z ≠ b := fun h ↦ hS hz (h.symm ▸ hb)
      have hab (i : ZeroCopy S m) : zeroCopyValue i ≠ b :=
        fun h ↦ hS i.1.property (h.symm ▸ hb)
      have ho (i : ZeroCopy S m) :
          analyticOrderAt (boundaryFactor 0 (zeroCopyValue i) b) z =
            if z = zeroCopyValue i then 1 else 0 :=
        analyticOrderAt_boundaryFactor 0 (hab i) hzb
      change analyticOrderAt (fun w ↦ ∏ i : ZeroCopy S m,
        boundaryFactor 0 (zeroCopyValue i) b w) z = (m z : ℕ∞)
      rw [analyticOrderAt_finset_product univ
        (F := fun i ↦ boundaryFactor 0 (zeroCopyValue i) b) (z := z)
        (fun i _ ↦ analyticAt_boundaryFactor 0 (zeroCopyValue i) b hzb)]
      simp only [ho]
      have hsum : (∑ i : ZeroCopy S m, if z = zeroCopyValue i then (1 : ℕ) else 0) = m z :=
        (hasSum_fintype _).unique (zeroCopy_indicator_hasSum hz)
      calc
        (∑ i : ZeroCopy S m, if z = zeroCopyValue i then (1 : ℕ∞) else 0) =
            ((∑ i : ZeroCopy S m, if z = zeroCopyValue i then (1 : ℕ) else 0) : ℕ∞) := by
          rw [Nat.cast_sum]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> rfl
        _ = (m z : ℕ∞) := congrArg (fun n : ℕ ↦ (n : ℕ∞)) hsum
  | inr hinfinite =>
    letI := hinfinite
    obtain ⟨a, haS, hcount, hescape⟩ := exists_zero_enumeration hScount hm hno
    have haS' (n : ℕ) : a n ∈ S := haS ▸ mem_range_self n
    have ha (n : ℕ) : a n ∉ C := hS (haS' n)
    choose b hb hnearest using (fun n ↦ hC.exists_infDist_eq_dist hCne (a n))
    obtain ⟨R, hR⟩ := hSbound.exists_norm_le
    have hd := infDist_tendsto_zero_of_bounded_escape a C R
      (fun n ↦ hR (a n) (haS' n)) hescape
    have hsmall := nearest_boundary_difference_tendsto_zero a b C hnearest hd
    have hprod := boundary_product_on_complement a b hC.isClosed hCne ha hb hsmall
    refine ⟨boundarySphereProduct a b,
      normalized_boundarySphereProduct_holomorphic a b hC hCne ha hb hsmall, rfl, ?_, ?_⟩
    · intro z hz
      rw [boundarySphereProduct_coe, (hprod.2.2 z hz).1]
      have hr : (∃ n, z = a n) ↔ z ∈ range a := by
        simp only [mem_range, eq_comm]
      rw [hr, haS]
    · intro z hz
      obtain ⟨_, hfinite, horder⟩ := hprod.2.2 z (hS hz)
      rw [(hcount z hz).tsum_eq] at horder
      change analyticOrderAt (fun w ↦ ∏' n, boundaryFactor n (a n) (b n) w) z = (m z : ℕ∞)
      calc
        _ = (analyticOrderNatAt (fun w ↦ ∏' n, boundaryFactor n (a n) (b n) w) z : ℕ∞) :=
          (ENat.natCast_toNat hfinite).symm
        _ = (m z : ℕ∞) := congrArg (fun n : ℕ ↦ (n : ℕ∞)) horder

/-- Rudin 15.11 on its full printed domain: every positive divisor with no
accumulation in a proper open subset of the Riemann sphere is the zero divisor
of a holomorphic function. No plane-only restriction or construction premise
appears in this statement. -/
theorem prescribed_zeros_on_sphere {Ω A : Set ComplexSphere}
    (hΩ : IsOpen Ω) (hproper : Ω ≠ univ) (hA : A ⊆ Ω)
    (hno : NoAccumulationIn A Ω) (m : ComplexSphere → ℕ) (hm : ∀ p ∈ A, 0 < m p) :
    ∃ f : ComplexSphere → ℂ, SphereHolomorphicOn f Ω ∧
      (∀ p ∈ Ω, f p = 0 ↔ p ∈ A) ∧
      (∀ p ∈ A, sphereAnalyticOrderAt f p = (m p : ℕ∞)) := by
  classical
  rcases Ω.eq_empty_or_nonempty with hΩempty | hΩne
  · refine ⟨fun _ ↦ 1, ?_, ?_, ?_⟩
    · intro p hp; exfalso; simpa only [hΩempty, mem_empty_iff_false] using hp
    · intro p hp; exfalso; simpa only [hΩempty, mem_empty_iff_false] using hp
    · intro p hp; exfalso; simpa only [hΩempty, mem_empty_iff_false] using hA hp
  obtain ⟨pole, hpole, hpoleA⟩ := exists_domain_point_outside_zeros hΩ hΩne hno
  let C : Set ℂ := (spherePlaneParam pole ⁻¹' Ω)ᶜ
  let S : Set ℂ := spherePlaneParam pole ⁻¹' A
  let m' : ℂ → ℕ := fun z ↦ m (spherePlaneParam pole z)
  have hC : IsCompact C := normalized_complement_isCompact hΩ hpole
  have hCne : C.Nonempty := normalized_complement_nonempty hproper hpole
  have hS : S ⊆ Cᶜ := by
    intro z hz
    exact not_not.mpr (hA hz)
  have hScount : S.Countable := normalized_zeros_countable hA hno pole
  have hSbound : IsBounded S := normalized_zeros_isBounded hno hpole hpoleA
  have hno' : ∀ z ∈ Cᶜ, ¬ AccPt z (𝓟 S) := by
    intro z hz
    exact normalized_zeros_no_accumulation hno pole z (not_not.mp hz)
  have hm' : ∀ z ∈ S, 0 < m' z := fun z hz ↦ hm (spherePlaneParam pole z) hz
  obtain ⟨g, hg, hginfty, hgzero, hgorder⟩ :=
    normalized_prescribed_zeros hC hCne hS hScount hSbound hno' m' hm'
  let f : ComplexSphere → ℂ := g ∘ spherePoleChart pole
  have hdom : (((↑) : ℂ → ComplexSphere) '' C)ᶜ =
      (spherePoleChart pole).symm ⁻¹' Ω := normalized_domain_eq hpole
  refine ⟨f, ?_, ?_, ?_⟩
  · intro p hp
    apply (sphereAnalyticAt_comp_poleChart_iff g pole p).2
    apply hg
    rw [hdom]
    simpa using hp
  · intro p hp
    by_cases hpp : p = pole
    · subst p
      simp [f, hginfty, hpoleA]
    · have hr : p ∈ range (spherePlaneParam pole) := by
        rw [range_spherePlaneParam]
        exact hpp
      obtain ⟨z, rfl⟩ := hr
      have hz : z ∈ Cᶜ := not_not.mpr hp
      simpa only [f, Function.comp_def, spherePlaneParam, Homeomorph.apply_symm_apply]
        using hgzero z hz
  · intro p hp
    have hpp : p ≠ pole := fun h ↦ hpoleA (h ▸ hp)
    have hr : p ∈ range (spherePlaneParam pole) := by
      rw [range_spherePlaneParam]
      exact hpp
    obtain ⟨z, rfl⟩ := hr
    change sphereAnalyticOrderAt (g ∘ spherePoleChart pole) (spherePlaneParam pole z) = _
    rw [sphereAnalyticOrderAt_comp_poleChart]
    simpa only [spherePlaneParam, Homeomorph.apply_symm_apply] using hgorder z hp

/-- The plane-domain corollary used by 15.12 and later nodes. It is obtained
from the full sphere theorem, so it does not replace the printed sphere scope. -/
theorem prescribed_zeros_on_plane {Ω A : Set ℂ}
    (hΩ : IsOpen Ω) (hA : A ⊆ Ω)
    (hno : ∀ z ∈ Ω, ¬ AccPt z (𝓟 A)) (m : ℂ → ℕ) (hm : ∀ z ∈ A, 0 < m z) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧
      (∀ z ∈ Ω, f z = 0 ↔ z ∈ A) ∧
      (∀ z ∈ A, analyticOrderAt f z = (m z : ℕ∞)) := by
  let Ωs : Set ComplexSphere := ((↑) : ℂ → ComplexSphere) '' Ω
  let As : Set ComplexSphere := ((↑) : ℂ → ComplexSphere) '' A
  let ms : ComplexSphere → ℕ := fun p ↦ p.elim 0 m
  have hΩs : IsOpen Ωs := OnePoint.isOpen_image_coe.2 hΩ
  have hproper : Ωs ≠ univ := by
    intro h
    have hin : (∞ : ComplexSphere) ∈ Ωs := by rw [h]; trivial
    exact OnePoint.infty_notMem_image_coe hin
  have hAs : As ⊆ Ωs := image_mono hA
  have hnos : NoAccumulationIn As Ωs := by
    rintro p ⟨z, hz, rfl⟩ hacc
    have hacc' := OnePoint.isOpenEmbedding_coe.accPt_comap_iff.mpr hacc
    apply hno z hz
    simpa only [comap_principal, As, preimage_image_eq _ OnePoint.coe_injective] using hacc'
  have hms : ∀ p ∈ As, 0 < ms p := by
    rintro p ⟨z, hz, rfl⟩
    exact hm z hz
  obtain ⟨f, hf, hzero, horder⟩ := prescribed_zeros_on_sphere hΩs hproper hAs hnos ms hms
  refine ⟨fun z ↦ f (↑z), ?_, ?_, ?_⟩
  · intro z hz
    have ha := hf (↑z) ⟨z, hz, rfl⟩
    change AnalyticAt ℂ (fun w : ℂ ↦ f (↑w)) z at ha
    exact ha.differentiableAt.differentiableWithinAt
  · intro z hz
    simpa only [As, mem_image, OnePoint.coe_eq_coe, exists_eq_right] using
      hzero (↑z) ⟨z, hz, rfl⟩
  · intro z hz
    exact horder (↑z) ⟨z, hz, rfl⟩

#print axioms normalized_prescribed_zeros
#print axioms prescribed_zeros_on_sphere
#print axioms prescribed_zeros_on_plane

end RudinRCA.Chapter15
