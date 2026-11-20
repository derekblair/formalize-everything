import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.DiffContOnCl

/-! Compile after PolynomialObstruction and MittagLefflerAssembly (evaluation analyticity). -/
noncomputable section
open Set
namespace RudinRCA.Chapter13

/-- A rational function whose canonical denominator has no roots on a closed set is
holomorphic on a neighborhood of every point of that set. -/
theorem ratFuncEval_diffContOnCl_of_no_poles {V : Set ℂ} (R : RatFunc ℂ)
    (hR : ∀ z ∈ closure V, R.denom.eval z ≠ 0) :
    DiffContOnCl ℂ (fun z => RatFunc.eval (RingHom.id ℂ) z R) V := by
  apply DifferentiableOn.diffContOnCl
  intro z hz
  exact (ratFuncEval_analyticAt_of_denom_ne_zero R (hR z hz)).differentiableAt.differentiableWithinAt

/-- Omitting a bounded complementary component forbids uniform rational approximation of the
reciprocal with its pole there. This is the directly applicable necessity argument in13.8. -/
theorem rational_approximation_obstruction_bounded_component {K : Set ℂ}
    (hK : IsClosed K) {a : ℂ} (ha : a ∉ K)
    (hb : Bornology.IsBounded (connectedComponentIn Kᶜ a))
    {m : ℝ} (hm : 0 < m) (hbound : ∀ z ∈ K, ‖z - a‖ ≤ m) (R : RatFunc ℂ)
    (hpolesK : ∀ z ∈ K, R.denom.eval z ≠ 0)
    (hpolesV : ∀ z ∈ connectedComponentIn Kᶜ a, R.denom.eval z ≠ 0) :
    ¬ ∀ z ∈ K, ‖RatFunc.eval (RingHom.id ℂ) z R - (z - a)⁻¹‖ < m⁻¹ := by
  apply reciprocal_approximation_obstruction hb (mem_connectedComponentIn ha) ha
    (frontier_complement_component_subset hK a) hm hbound
  apply ratFuncEval_diffContOnCl_of_no_poles
  intro z hz
  rw [closure_eq_self_union_frontier] at hz
  exact hz.elim (hpolesV z)
    (fun hzf => hpolesK z (frontier_complement_component_subset hK a hzf))

/-- The allowed-pole formulation of the same obstruction, with no finiteness assumption on A. -/
theorem rational_obstruction_of_allowed_poles_omit_bounded_component {K A : Set ℂ}
    (hK : IsClosed K) {a : ℂ} (ha : a ∉ K)
    (hb : Bornology.IsBounded (connectedComponentIn Kᶜ a))
    (hAK : Disjoint A K) (hAV : Disjoint A (connectedComponentIn Kᶜ a))
    {m : ℝ} (hm : 0 < m) (hbound : ∀ z ∈ K, ‖z - a‖ ≤ m)
    (R : RatFunc ℂ) (hR : ∀ z, R.denom.eval z = 0 → z ∈ A) :
    ¬ ∀ z ∈ K, ‖RatFunc.eval (RingHom.id ℂ) z R - (z - a)⁻¹‖ < m⁻¹ :=
  rational_approximation_obstruction_bounded_component hK ha hb hm hbound R
    (fun z hz hzero => Set.disjoint_left.mp hAK (hR z hzero) hz)
    (fun z hz hzero => Set.disjoint_left.mp hAV (hR z hzero) hz)

#print axioms ratFuncEval_diffContOnCl_of_no_poles
#print axioms rational_approximation_obstruction_bounded_component
#print axioms rational_obstruction_of_allowed_poles_omit_bounded_component
end RudinRCA.Chapter13
