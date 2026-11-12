import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
Scratch development of implications in Rudin RCA 13.11:
simple connectedness gives holomorphic logarithms, and holomorphic logarithms
give holomorphic square roots. This does not establish all nine equivalences.
-/

open Set Filter
open scoped Topology

namespace RudinRCA.Chapter13

/-- A continuous local logarithm of a complex differentiable function is
itself complex differentiable. The local inverse theorem for the exponential
supplies the analytic information missing from a purely continuous lift. -/
theorem differentiableAt_of_continuousAt_exp {g : ℂ → ℂ} {a : ℂ}
    (hg : ContinuousAt g a)
    (he : DifferentiableAt ℂ (Complex.exp ∘ g) a) : DifferentiableAt ℂ g a := by
  have hx := Complex.hasStrictDerivAt_exp (g a)
  have hne := Complex.exp_ne_zero (g a)
  let L := hx.localInverse Complex.exp (Complex.exp (g a)) (g a) hne
  have hL : DifferentiableAt ℂ L (Complex.exp (g a)) :=
    (hx.to_localInverse hne).hasDerivAt.differentiableAt
  have hleft : (fun w => L (Complex.exp w)) =ᶠ[𝓝 (g a)] id :=
    hx.eventually_left_inverse hne
  have hback : g =ᶠ[𝓝 a] (L ∘ (Complex.exp ∘ g)) :=
    (hleft.comp_tendsto hg).symm
  exact (hL.comp a he).congr_of_eventuallyEq hback

/-- On an open set, every continuous logarithm of a holomorphic function is
holomorphic. -/
theorem holomorphic_of_continuous_log {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) (hg : ContinuousOn g Ω)
    (hlog : EqOn (Complex.exp ∘ g) f Ω) : DifferentiableOn ℂ g Ω := by
  intro a ha
  have hnhds := hΩ.mem_nhds ha
  have heq : (Complex.exp ∘ g) =ᶠ[𝓝 a] f := by
    filter_upwards [hnhds] with z hz
    exact hlog hz
  exact (differentiableAt_of_continuousAt_exp (hg.continuousAt hnhds)
    ((hf.differentiableAt hnhds).congr_of_eventuallyEq heq)).differentiableWithinAt

/-- Rudin 13.11, implication (b) to (h): a zero-free holomorphic function on
an open simply connected plane set admits a holomorphic logarithm. -/
theorem exists_holomorphic_log_of_simply_connected {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hsc : IsSimplyConnected Ω) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) (hzero : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ EqOn (Complex.exp ∘ g) f Ω := by
  have hnot : 0 ∉ f '' Ω := by
    rintro ⟨z, hz, heq⟩
    exact hzero z hz heq
  obtain ⟨g, hgc, hg⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hsc hΩ hf.continuousOn hnot
  exact ⟨g, holomorphic_of_continuous_log hΩ hf hgc hg, hg⟩

/-- Rudin 13.11, implication (h) to (j), for one function: exponentiating
half of a holomorphic logarithm gives a holomorphic square root. -/
theorem exists_holomorphic_sqrt_of_holomorphic_log {Ω : Set ℂ} {f g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g Ω) (hlog : EqOn (Complex.exp ∘ g) f Ω) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h Ω ∧ ∀ z ∈ Ω, (h z) ^ 2 = f z := by
  refine ⟨fun z => Complex.exp (g z / 2), (hg.div_const 2).cexp, ?_⟩
  intro z hz
  calc
    Complex.exp (g z / 2) ^ 2 = Complex.exp (2 * (g z / 2)) :=
      (Complex.exp_nat_mul (g z / 2) 2).symm
    _ = Complex.exp (g z) := by congr 1; ring
    _ = f z := hlog hz

/-- In particular, a zero-free holomorphic function on an open simply
connected plane set admits a holomorphic square root. -/
theorem exists_holomorphic_sqrt_of_simply_connected {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hsc : IsSimplyConnected Ω) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) (hzero : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h Ω ∧ ∀ z ∈ Ω, (h z) ^ 2 = f z := by
  obtain ⟨g, hg, hlog⟩ := exists_holomorphic_log_of_simply_connected hΩ hsc hf hzero
  exact exists_holomorphic_sqrt_of_holomorphic_log hg hlog

#print axioms differentiableAt_of_continuousAt_exp
#print axioms holomorphic_of_continuous_log
#print axioms exists_holomorphic_log_of_simply_connected
#print axioms exists_holomorphic_sqrt_of_holomorphic_log
#print axioms exists_holomorphic_sqrt_of_simply_connected

end RudinRCA.Chapter13
