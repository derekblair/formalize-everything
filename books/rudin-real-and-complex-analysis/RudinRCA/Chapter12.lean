import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Rudin, Real and Complex Analysis, Chapter 12

The number labels refer to the third edition. `DifferentiableOn ℂ` on the
open sets below is equivalent to complex differentiability at every point.
The boundary maximum portion of 12.1, all of 12.2, the definition in 12.3,
and the strip theorem and sharpness example in 12.9 are formalized here.
The radial-boundary-value assertion recalled in 12.1 is not yet formalized.
-/

open Set Metric Bornology

namespace RudinRCA.Chapter12

/-- The boundary supremum used in the first assertion of 12.1. -/
noncomputable def boundaryNorm (f : ℂ → ℂ) (Ω : Set ℂ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' frontier Ω)

/-- 12.1, the maximum estimate on a bounded region. -/
theorem theorem12_1_boundary_bound {f : ℂ → ℂ} {Ω : Set ℂ}
    (hb : IsBounded Ω) (hf : DifferentiableOn ℂ f Ω)
    (hc : ContinuousOn f (closure Ω)) {z : ℂ} (hz : z ∈ closure Ω) :
    ‖f z‖ ≤ boundaryNorm f Ω := by
  have hB : BddAbove ((fun z => ‖f z‖) '' frontier Ω) :=
    (hb.isCompact_closure.image_of_continuousOn hc.norm).bddAbove.mono
      (Set.image_mono frontier_subset_closure)
  exact Complex.norm_le_of_forall_mem_frontier_norm_le hb ⟨hf, hc⟩
    (fun w hw => le_csSup hB (mem_image_of_mem _ hw)) hz

/-- 12.1, equality at an interior point forces constancy. -/
theorem theorem12_1_boundary_equality {f : ℂ → ℂ} {Ω : Set ℂ}
    (hb : IsBounded Ω) (ho : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hf : DifferentiableOn ℂ f Ω) (hc : ContinuousOn f (closure Ω))
    {c : ℂ} (hcΩ : c ∈ Ω) (heq : ‖f c‖ = boundaryNorm f Ω) :
    ∀ z ∈ closure Ω, f z = f c := by
  apply Complex.eqOn_closure_of_isPreconnected_of_isMaxOn_norm hconn ho ⟨hf, hc⟩ hcΩ
  intro z hz
  exact (theorem12_1_boundary_bound hb hf hc (subset_closure hz)).trans_eq heq.symm

/-- 12.2 (Schwarz): both inequalities and both rigidity cases.

The pointwise bound is the supremum-norm condition of the book, expressed
without introducing the separate space `H∞`.
-/
theorem theorem12_2 {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ 1) (hzero : f 0 = 0) :
    (∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ ‖z‖) ∧
    ‖deriv f 0‖ ≤ 1 ∧
    (((∃ z ∈ ball (0 : ℂ) 1, z ≠ 0 ∧ ‖f z‖ = ‖z‖) ∨ ‖deriv f 0‖ = 1) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ ball (0 : ℂ) 1, f z = c * z) := by
  have hmaps : MapsTo f (ball (0 : ℂ) 1) (closedBall (f 0) 1) := by
    intro z hz
    simpa [hzero, mem_closedBall_zero_iff] using hb z hz
  refine ⟨?_, Complex.norm_deriv_le_one_of_mapsTo_ball hf hmaps (by norm_num), ?_⟩
  · intro z hz
    exact Complex.norm_le_norm_of_mapsTo_ball hf (by simpa [hzero] using hmaps)
      hzero (mem_ball_zero_iff.mp hz)
  · intro heq
    have hw : ∃ w ∈ ball (0 : ℂ) 1, ‖dslope f 0 w‖ = (1 : ℝ) / 1 := by
      rcases heq with ⟨w, hw, hw0, hweq⟩ | hderiv
      · refine ⟨w, hw, ?_⟩
        simp [dslope_of_ne f hw0, slope_def_module, hzero, hweq,
          norm_ne_zero_iff.mpr hw0]
      · exact ⟨0, by simp, by simpa using hderiv⟩
    obtain ⟨c, hnorm, hfl⟩ :=
      Complex.affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div' hf hmaps hw
    refine ⟨c, by simpa using hnorm, ?_⟩
    intro z hz
    simpa [hzero, mul_comm] using hfl hz

/-- 12.3: the disk transformation, with the book's sign convention. -/
noncomputable def phi (α z : ℂ) : ℂ := (z - α) / (1 - star α * z)

/-- 12.9: Phragmén–Lindelöf in the strip of height `π`.

The finite constants of the printed statement are ordinary real numbers.
The two boundary inequalities are parametrized by imaginary part, which
is equivalent to the book's `x ± π * I / 2` parametrization.
-/
theorem theorem12_9 {f : ℂ → ℂ} {α A : ℝ}
    (hf : DifferentiableOn ℂ f {z : ℂ | |z.im| < Real.pi / 2})
    (hc : ContinuousOn f {z : ℂ | |z.im| ≤ Real.pi / 2}) (hα : α < 1)
    (hg : ∀ z : ℂ, |z.im| < Real.pi / 2 →
      ‖f z‖ < Real.exp (A * Real.exp (α * |z.re|)))
    (hlo : ∀ z : ℂ, z.im = -(Real.pi / 2) → ‖f z‖ ≤ 1)
    (hhi : ∀ z : ℂ, z.im = Real.pi / 2 → ‖f z‖ ≤ 1)
    {z : ℂ} (hz : |z.im| < Real.pi / 2) : ‖f z‖ ≤ 1 := by
  let S : Set ℂ := Complex.im ⁻¹' Ioo (-(Real.pi / 2)) (Real.pi / 2)
  have hS : S = {z : ℂ | |z.im| < Real.pi / 2} := by
    ext w
    simp [S, abs_lt]
  have hdiff : DiffContOnCl ℂ f S := by
    refine ⟨by simpa [hS] using hf, hc.mono ?_⟩
    exact closure_minimal (fun w hw => (show |w.im| < Real.pi / 2 by
      simpa [hS] using hw).le) (isClosed_le Complex.continuous_im.abs continuous_const)
  apply PhragmenLindelof.horizontal_strip hdiff ?_ hlo hhi
    (abs_lt.mp hz).1.le (abs_lt.mp hz).2.le
  refine ⟨α, ?_, A, Asymptotics.IsBigO.of_bound' ?_⟩
  · convert hα using 1
    rw [show Real.pi / 2 - -(Real.pi / 2) = Real.pi by ring,
      div_self Real.pi_ne_zero]
  · apply Filter.eventually_inf_principal.mpr
    exact Filter.Eventually.of_forall fun w hw => by
      simpa only [Real.norm_eq_abs, Real.abs_exp] using (hg w (by simpa [S, abs_lt] using hw)).le

/-- 12.9, sharpness on the closed strip: `exp (exp z)` has boundary modulus
one, satisfies the growth hypothesis with `α = 1` and `A = 2`, and has
modulus greater than one at the interior point zero. -/
theorem theorem12_9_sharpness :
    let f : ℂ → ℂ := fun z => Complex.exp (Complex.exp z)
    Differentiable ℂ f ∧
    (∀ z : ℂ, z.im = -(Real.pi / 2) → ‖f z‖ = 1) ∧
    (∀ z : ℂ, z.im = Real.pi / 2 → ‖f z‖ = 1) ∧
    (∀ z : ℂ, |z.im| < Real.pi / 2 →
      ‖f z‖ < Real.exp (2 * Real.exp (1 * |z.re|))) ∧
    ‖f 0‖ = Real.exp 1 ∧ 1 < ‖f 0‖ := by
  dsimp only
  have hexp_norm (z : ℂ) :
      ‖Complex.exp (Complex.exp z)‖ =
        Real.exp (Real.exp z.re * Real.cos z.im) := by
    rw [Complex.norm_exp, Complex.exp_re]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Function.comp_def] using
      (Complex.differentiable_exp.comp Complex.differentiable_exp)
  · intro z hz
    rw [hexp_norm, hz, Real.cos_neg, Real.cos_pi_div_two, mul_zero, Real.exp_zero]
  · intro z hz
    rw [hexp_norm, hz, Real.cos_pi_div_two, mul_zero, Real.exp_zero]
  · intro z hz
    rw [hexp_norm]
    apply Real.exp_lt_exp.mpr
    calc
      Real.exp z.re * Real.cos z.im ≤ Real.exp z.re * 1 :=
        mul_le_mul_of_nonneg_left (Real.cos_le_one _) (Real.exp_pos _).le
      _ = Real.exp z.re := mul_one _
      _ ≤ Real.exp |z.re| := Real.exp_le_exp.mpr (le_abs_self _)
      _ < 2 * Real.exp (1 * |z.re|) := by
        simp only [one_mul]
        nlinarith [Real.exp_pos |z.re|]
  · rw [Complex.exp_zero]
    exact Complex.norm_exp (1 : ℂ)
  · rw [Complex.exp_zero, Complex.norm_exp]
    simpa only [Complex.one_re, Real.exp_zero] using
      (Real.exp_lt_exp.mpr (show (0 : ℝ) < 1 from zero_lt_one))

end RudinRCA.Chapter12
