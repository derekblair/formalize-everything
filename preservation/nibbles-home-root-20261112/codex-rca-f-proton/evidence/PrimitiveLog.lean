import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
Scratch development of Rudin RCA 13.11 (g) implies (h): if every holomorphic
function has a primitive on a plane region, every zero-free holomorphic
function has a holomorphic logarithm. This is one implication, not the full
nine-way equivalence.
-/

open Set

namespace RudinRCA.Chapter13

/-- A primitive of the logarithmic derivative determines a holomorphic
logarithm, after an additive constant is chosen. -/
theorem exists_holomorphic_log_of_primitive_logDeriv {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) (hzero : ∀ z ∈ Ω, f z ≠ 0)
    (hg : DifferentiableOn ℂ g Ω)
    (hprim : ∀ z ∈ Ω, deriv g z = deriv f z / f z) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h Ω ∧ EqOn (Complex.exp ∘ h) f Ω := by
  have he : DifferentiableOn ℂ (Complex.exp ∘ g) Ω := hg.cexp
  have hder : EqOn (logDeriv f) (logDeriv (Complex.exp ∘ g)) Ω := by
    intro z hz
    calc
      logDeriv f z = deriv g z := (hprim z hz).symm
      _ = logDeriv (Complex.exp ∘ g) z := by
        rw [logDeriv_comp Complex.differentiableAt_exp
          (hg.differentiableAt (hΩ.mem_nhds hz))]
        simp [logDeriv_apply, Complex.deriv_exp, Complex.exp_ne_zero]
  obtain ⟨c, hc, hcf⟩ := (logDeriv_eqOn_iff hf he hΩ hconn
    (fun z _ => Complex.exp_ne_zero (g z)) hzero).1 hder
  refine ⟨fun z => Complex.log c + g z,
    (differentiableOn_const (Complex.log c)).add hg, ?_⟩
  intro z hz
  change Complex.exp (Complex.log c + g z) = f z
  rw [Complex.exp_add, Complex.exp_log hc]
  simpa only [Pi.smul_apply, smul_eq_mul, Function.comp_apply] using (hcf hz).symm

/-- Rudin 13.11, implication (g) to (h), with the universal primitive
property stated explicitly. -/
theorem primitives_imply_holomorphic_logarithms {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hprimitives : ∀ k : ℂ → ℂ, DifferentiableOn ℂ k Ω →
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ Ω, deriv g z = k z)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) (hzero : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h Ω ∧ EqOn (Complex.exp ∘ h) f Ω := by
  have hquot : DifferentiableOn ℂ (fun z => deriv f z / f z) Ω :=
    (hf.deriv hΩ).div hf hzero
  obtain ⟨g, hg, hprim⟩ := hprimitives (fun z => deriv f z / f z) hquot
  exact exists_holomorphic_log_of_primitive_logDeriv hΩ hconn hf hzero hg hprim

#print axioms exists_holomorphic_log_of_primitive_logDeriv
#print axioms primitives_imply_holomorphic_logarithms

end RudinRCA.Chapter13
