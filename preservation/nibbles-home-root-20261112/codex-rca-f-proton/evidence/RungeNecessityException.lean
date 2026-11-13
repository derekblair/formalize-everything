import RudinRCA.Chapter13
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.Positivity

/-! Literal unrestricted necessity in the last sentence of13.8 has a singleton exception.
The main disconnected-complement obstruction is unaffected. -/
noncomputable section
open Set Filter
open scoped OnePoint Topology
namespace RudinRCA.Chapter13

/-- Constants have no finite poles and extend holomorphically across infinity. -/
theorem constant_ratFunc_no_spherical_poles (c : ℂ) :
    (∀ z : ℂ, (RatFunc.C c).denom.eval z ≠ 0) ∧
      HasRemovableSingularityAtInfinity (fun z => RatFunc.eval (RingHom.id ℂ) z (RatFunc.C c)) := by
  constructor
  · simp [RatFunc.denom_C]
  · refine ⟨c, ?_⟩
    simpa only [RatFunc.eval_C, RingHom.id_apply, Function.update_eq_self] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) 0)

/-- Every function on a singleton is exactly represented there by a rational function with no
poles anywhere on the sphere; no holomorphy assumption on the function is needed. -/
theorem singleton_rational_approximation_without_allowed_poles (a : ℂ) (f : ℂ → ℂ) :
    ∃ R : RatFunc ℂ, (∀ z : ℂ, R.denom.eval z ≠ 0) ∧
      HasRemovableSingularityAtInfinity (fun z => RatFunc.eval (RingHom.id ℂ) z R) ∧
      ∀ z ∈ ({a} : Set ℂ), RatFunc.eval (RingHom.id ℂ) z R = f z := by
  exact ⟨RatFunc.C (f a), (constant_ratFunc_no_spherical_poles (f a)).1,
    (constant_ratFunc_no_spherical_poles (f a)).2, by simp⟩

/-- The singleton counterexample still has a connected spherical complement: its only
prescribed representative may be infinity, and dispensing with it leaves exact approximation. -/
theorem singleton_zero_spherical_complement_connected :
    IsConnected (((↑) : ℂ → RiemannSphere) '' ({0} : Set ℂ))ᶜ := by
  have hplane : IsConnected ({0}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by simp) 0
  have hunbounded : ∀ r > 0, ∃ z ∈ ({0}ᶜ : Set ℂ), r < ‖z‖ := by
    intro r hr
    refine ⟨((r + 1 : ℝ) : ℂ), ?_, ?_⟩
    · simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
      positivity
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < r + 1)]
      linarith
  have h := isConnected_insert_infinity hplane hunbounded
  have heq : insert (∞ : RiemannSphere) (((↑) : ℂ → RiemannSphere) '' ({0}ᶜ : Set ℂ)) =
      (((↑) : ℂ → RiemannSphere) '' ({0} : Set ℂ))ᶜ := by
    ext p
    induction p using OnePoint.rec with
    | infty => simp
    | coe z => simp
  exact heq ▸ h

/-- A concrete counterexample to an unrestricted converse asserting that approximation of all
holomorphic functions requires an allowed pole in every spherical complement component. -/
theorem runge_unrestricted_pole_necessity_counterexample :
    ∃ K : Set ℂ, IsCompact K ∧ K.Nonempty ∧
      IsConnected (((↑) : ℂ → RiemannSphere) '' K)ᶜ ∧
      (∃ p ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
        ¬∃ a ∈ (∅ : Set RiemannSphere),
          a ∈ connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K)ᶜ p) ∧
      ∀ f : ℂ → ℂ, ∃ R : RatFunc ℂ, (∀ z, R.denom.eval z ≠ 0) ∧
        HasRemovableSingularityAtInfinity (fun z => RatFunc.eval (RingHom.id ℂ) z R) ∧
        ∀ z ∈ K, RatFunc.eval (RingHom.id ℂ) z R = f z := by
  refine ⟨{0}, isCompact_singleton, singleton_nonempty 0,
    singleton_zero_spherical_complement_connected, ?_, ?_⟩
  · exact ⟨∞, by simp, by simp⟩
  · exact singleton_rational_approximation_without_allowed_poles 0

#print axioms constant_ratFunc_no_spherical_poles
#print axioms singleton_rational_approximation_without_allowed_poles
#print axioms singleton_zero_spherical_complement_connected
#print axioms runge_unrestricted_pole_necessity_counterexample
end RudinRCA.Chapter13
