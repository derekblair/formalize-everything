import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FunProp

noncomputable section
open Set Filter
open scoped Topology

namespace RudinRCA.Chapter13

/-- Hahn–Banach separation in the form needed for rational approximation. -/
theorem mem_closed_submodule_of_annihilators {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (M : Submodule ℂ E) (hM : IsClosed (M : Set E)) {x : E}
    (h : ∀ L : E →L[ℂ] ℂ, (∀ y ∈ M, L y = 0) → L x = 0) : x ∈ M := by
  let : IsClosed (M : Set E) := hM
  have hx : M.mkQL x = 0 := by
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
    intro L
    apply h (L.comp M.mkQL)
    intro y hy
    have hyq : M.mkQL y = 0 := (Submodule.Quotient.mk_eq_zero M).mpr hy
    simp [hyq]
  exact (Submodule.Quotient.mk_eq_zero M).mp hx

/-- Closure of a linear space is detected by all continuous linear annihilators. -/
theorem mem_submodule_closure_iff_annihilators {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (M : Submodule ℂ E) (x : E) :
    x ∈ M.topologicalClosure ↔
      ∀ L : E →L[ℂ] ℂ, (∀ y ∈ M, L y = 0) → L x = 0 := by
  constructor
  · intro hx L hL
    exact M.topologicalClosure_minimal (fun y hy ↦ hL y hy) L.isClosed_ker hx
  · intro h
    apply mem_closed_submodule_of_annihilators M.topologicalClosure M.isClosed_topologicalClosure
    intro L hL
    exact h L (fun y hy ↦ hL y (M.le_topologicalClosure hy))

/-- The complex coordinate viewed in the Banach algebra of continuous functions on K. -/
def compactCoordinate (K : Set ℂ) : C(K, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩

theorem spectrum_compactCoordinate (K : Set ℂ) :
    spectrum ℂ (compactCoordinate K) = K := by
  rw [ContinuousMap.spectrum_eq_range]
  exact Subtype.range_coe

/-- A continuous linear functional applied to a resolvent is holomorphic off the spectrum. -/
theorem differentiableOn_dual_resolvent {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (a : A) (L : A →L[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z ↦ L (resolvent a z)) (spectrum ℂ a)ᶜ := by
  intro z hz
  have hz' : z ∈ resolventSet ℂ a := by simpa only [spectrum, compl_compl] using hz
  exact (L.differentiableAt.comp z
    (spectrum.hasDerivAt_resolvent_const_left hz').differentiableAt).differentiableWithinAt

/-- The C(K)-valued resolvent evaluates to the usual Cauchy kernel. -/
theorem compactCoordinate_resolvent_apply (K : Set ℂ) {z : ℂ} (hz : z ∉ K) (x : K) :
    resolvent (compactCoordinate K) z x = (z - (x : ℂ))⁻¹ := by
  have hz' : z ∈ resolventSet ℂ (compactCoordinate K) := by
    apply spectrum.notMem_iff.mp
    rwa [spectrum_compactCoordinate]
  have hh := congrArg (fun g : C(K, ℂ) ↦ g x)
    (Ring.inverse_mul_cancel (algebraMap ℂ C(K, ℂ) z - compactCoordinate K) hz')
  have hm : resolvent (compactCoordinate K) z x * (z - (x : ℂ)) = 1 := by
    simpa [resolvent, compactCoordinate] using hh
  exact eq_inv_of_mul_eq_one_left hm

/-- This Cauchy transform uses a bounded linear functional directly, without a measure representation. -/
theorem differentiableOn_compact_cauchy_transform (K : Set ℂ) [CompactSpace K]
    (L : C(K, ℂ) →L[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z ↦ L (resolvent (compactCoordinate K) z)) Kᶜ := by
  simpa only [spectrum_compactCoordinate] using differentiableOn_dual_resolvent (compactCoordinate K) L

/-- Resolvent expansion around any point outside the spectrum. -/
theorem resolvent_shift {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : A) {α : ℂ} (hα : α ∈ resolventSet ℂ a) (β : ℂ) :
    resolvent a β = resolvent a α *
      Ring.inverse (1 - (α - β) • resolvent a α) := by
  have hfactor : algebraMap ℂ A β - a =
      (algebraMap ℂ A α - a) * (1 - (α - β) • resolvent a α) := by
    rw [mul_sub, mul_one, mul_smul_comm]
    rw [resolvent, Ring.mul_inverse_cancel _ hα]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, sub_smul]
    abel
  conv_lhs => rw [resolvent, hfactor]
  rw [Ring.inverse_mul (Or.inl hα)]
  exact mul_comm _ _

/-- An annihilator of all powers kills the convergent geometric resolvent expansion. -/
theorem dual_geometric_inverse_eq_zero {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (L : A →L[ℂ] ℂ) (a b : A) (w : ℂ)
    (hsmall : ‖w • a‖ < 1) (h : ∀ n : ℕ, L (b * a ^ n) = 0) :
    L (b * Ring.inverse (1 - w • a)) = 0 := by
  have hs := L.hasSum ((hasSum_geom_series_inverse (w • a) hsmall).mul_left b)
  have hz : HasSum (fun _ : ℕ ↦ (0 : ℂ)) (L (b * Ring.inverse (1 - w • a))) := by
    simpa only [smul_pow, mul_smul_comm, L.map_smul, h, smul_zero] using hs
  exact hz.unique hasSum_zero

/-- Vanishing on the principal parts at α forces the Cauchy transform to vanish near α. -/
theorem dual_resolvent_eventually_eq_zero {A : Type*} [NormedCommRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] (a : A) (L : A →L[ℂ] ℂ)
    {α : ℂ} (hα : α ∈ resolventSet ℂ a)
    (h : ∀ n : ℕ, L (resolvent a α ^ (n + 1)) = 0) :
    (fun β ↦ L (resolvent a β)) =ᶠ[𝓝 α] 0 := by
  have hc : Continuous (fun β : ℂ ↦ ‖(α - β) • resolvent a α‖) := by fun_prop
  have hsmall : ∀ᶠ β in 𝓝 α, ‖(α - β) • resolvent a α‖ < 1 :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  filter_upwards [hsmall] with β hβ
  rw [resolvent_shift a hα β]
  apply dual_geometric_inverse_eq_zero L _ _ _ hβ
  intro n
  simpa only [pow_succ, mul_comm] using h n

/-- The inverse chart gives a holomorphic extension of the Cauchy transform at infinity. -/
theorem analyticAt_dual_inverseChart_resolvent {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] (a : A) (L : A →L[ℂ] ℂ) :
    AnalyticAt ℂ (fun w : ℂ ↦ L (w • Ring.inverse (1 - w • a))) 0 := by
  have hi : AnalyticAt ℂ (fun w : ℂ ↦ Ring.inverse (1 - w • a)) 0 :=
    (spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul ℂ a).analyticAt
  exact (L.analyticAt _).comp (analyticAt_id.smul hi)

/-- The inverse-chart expression agrees with the resolvent away from its chart center. -/
theorem inverseChart_resolvent_eq {A : Type*} [Ring A] [Algebra ℂ A]
    (a : A) {w : ℂ} (hw : w ≠ 0) :
    resolvent a w⁻¹ = w • Ring.inverse (1 - w • a) := by
  have h := congrArg (fun v : A ↦ w • v)
    (spectrum.units_smul_resolvent_self (r := (Units.mk0 w hw)⁻¹) (a := a))
  simpa [resolvent, Units.smul_def, smul_smul, hw] using h

/-- Annihilation of polynomial restrictions gives local vanishing at infinity. -/
theorem dual_inverseChart_resolvent_eventually_eq_zero {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] (a : A) (L : A →L[ℂ] ℂ)
    (h : ∀ n : ℕ, L (a ^ n) = 0) :
    (fun w : ℂ ↦ L (w • Ring.inverse (1 - w • a))) =ᶠ[𝓝 0] 0 := by
  have hc : Continuous (fun w : ℂ ↦ ‖w • a‖) := by fun_prop
  have hsmall : ∀ᶠ w : ℂ in 𝓝 0, ‖w • a‖ < 1 :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  filter_upwards [hsmall] with w hw
  have hz : L (Ring.inverse (1 - w • a)) = 0 := by
    simpa only [one_mul] using
      dual_geometric_inverse_eq_zero L a 1 w hw (fun n ↦ by simpa only [one_mul] using h n)
  simp [hz]

/-- Isolated-zero dichotomy makes the set of zero germs clopen. -/
theorem isClopen_zeroGerms {X : Type*} [TopologicalSpace X] (f : X → ℂ)
    (hiso : ∀ x, (∀ᶠ y in 𝓝 x, f y = 0) ∨ ∀ᶠ y in 𝓝[≠] x, f y ≠ 0) :
    IsClopen {x | ∀ᶠ y in 𝓝 x, f y = 0} := by
  refine ⟨?_, isOpen_setOfPred_eventually_nhds⟩
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx' : ¬∀ᶠ y in 𝓝 x, f y = 0 := hx
  have hn := (hiso x).resolve_left hx'
  rw [eventually_nhdsWithin_iff] at hn
  filter_upwards [hn] with y hy
  intro hyzero
  by_cases hyx : y = x
  · exact hx' (hyx ▸ hyzero)
  · exact hy hyx hyzero.self_of_nhds

/-- Local vanishing at one point of every connected component implies global vanishing. -/
theorem eq_zero_of_zeroGerm_in_each_component {X : Type*} [TopologicalSpace X] (f : X → ℂ)
    (hiso : ∀ x, (∀ᶠ y in 𝓝 x, f y = 0) ∨ ∀ᶠ y in 𝓝[≠] x, f y ≠ 0)
    (hpoints : ∀ x, ∃ a ∈ connectedComponent x, ∀ᶠ y in 𝓝 a, f y = 0) :
    ∀ x, f x = 0 := by
  intro x
  obtain ⟨a, ha, hzero⟩ := hpoints x
  have hx : x ∈ connectedComponent a := by
    rw [← connectedComponent_eq ha]
    exact mem_connectedComponent
  exact ((isClopen_zeroGerms f hiso).connectedComponent_subset hzero hx).self_of_nhds

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.mem_submodule_closure_iff_annihilators
#print axioms RudinRCA.Chapter13.compactCoordinate_resolvent_apply
#print axioms RudinRCA.Chapter13.differentiableOn_compact_cauchy_transform
#print axioms RudinRCA.Chapter13.dual_resolvent_eventually_eq_zero
#print axioms RudinRCA.Chapter13.analyticAt_dual_inverseChart_resolvent
#print axioms RudinRCA.Chapter13.dual_inverseChart_resolvent_eventually_eq_zero
#print axioms RudinRCA.Chapter13.eq_zero_of_zeroGerm_in_each_component
