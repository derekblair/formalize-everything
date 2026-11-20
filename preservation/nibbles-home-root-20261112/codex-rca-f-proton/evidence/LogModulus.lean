import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.CauchyIntegral

namespace RudinRCA.Chapter13

/-- Rudin 13.12: the logarithm of the modulus of a zero-free holomorphic
function is harmonic on its open domain. Neither connectedness nor simple
connectedness is assumed. -/
theorem harmonic_log_norm {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) (hzero : ∀ z ∈ Ω, f z ≠ 0) :
    InnerProductSpace.HarmonicOnNhd (fun z => Real.log ‖f z‖) Ω := by
  intro z hz
  exact (hf.analyticOnNhd hΩ z hz).harmonicAt_log_norm (hzero z hz)

#print axioms harmonic_log_norm

end RudinRCA.Chapter13
