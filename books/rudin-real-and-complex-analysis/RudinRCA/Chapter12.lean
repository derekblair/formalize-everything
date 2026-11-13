import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import RudinRCA.Chapter05
import RudinRCA.Chapter10
import RudinRCA.Chapter11

/-!
# Rudin, Real and Complex Analysis, Chapter 12

The number labels refer to the third edition. `DifferentiableOn ℂ` on the
open sets below is equivalent to complex differentiability at every point.
The boundary maximum portion of 12.1, all of 12.2–12.9 (Schwarz's lemma, the
disk transformations `φ_α`, their mapping/inverse/derivative theorem, the
Schwarz–Pick extremal problem, the classification of disk automorphisms, the
unbounded-strip and sublinear-entire examples, Hadamard's three-lines theorem
with its logarithmic-convexity corollary, and the Phragmén–Lindelöf strip
theorem with its sharpness witness), the `H^∞` radial-boundary-value assertion
recalled in 12.1, Lindelöf's theorem (12.10), bounded orthonormal systems and
the Hausdorff–Young theorem (12.11–12.12), the converse maximum-modulus
characterization of harmonic boundary spaces (12.13), and Radó's theorem
(12.14) are formalized here (`14/14` numbered nodes complete).
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

/-! ## Disk transformations, Schwarz–Pick, and disk automorphisms (12.4–12.6) -/

private theorem star_eq_conj (z : ℂ) : star z = (starRingEnd ℂ) z := rfl

private theorem mul_star_self_eq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [star_eq_conj, Complex.mul_conj', Complex.ofReal_pow]

private theorem star_mul_self_eq (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [star_eq_conj, Complex.conj_mul', Complex.ofReal_pow]

/-- Algebraic norm identity underlying 12.4:
`‖1 - star α * z‖ ^ 2 - ‖z - α‖ ^ 2 = (1 - ‖α‖ ^ 2) * (1 - ‖z‖ ^ 2)`. -/
theorem phi_norm_sq_sub (α z : ℂ) :
    ‖1 - star α * z‖ ^ 2 - ‖z - α‖ ^ 2 = (1 - ‖α‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, star_eq_conj,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Characterization of the pole of `phi α`: `1 - star α * z = 0 ↔ star α * z = 1`,
and when `α ≠ 0`, `1 - star α * z = 0 ↔ z = (star α)⁻¹`. -/
theorem phi_denom_eq_zero_iff (α z : ℂ) :
    (1 - star α * z = 0 ↔ star α * z = 1) ∧
    (α ≠ 0 → (1 - star α * z = 0 ↔ z = (star α)⁻¹)) := by
  refine ⟨sub_eq_zero.trans eq_comm, fun hα => ?_⟩
  have hstar : star α ≠ 0 := star_ne_zero.mpr hα
  rw [sub_eq_zero, eq_comm]
  constructor
  · intro h
    calc
      z = (star α)⁻¹ * (star α * z) := by rw [inv_mul_cancel_left₀ hstar]
      _ = (star α)⁻¹ := by rw [h, mul_one]
  · rintro rfl
    exact mul_inv_cancel₀ hstar

/-- For `α ∈ U` and `z ∈ closure U`, the denominator `1 - star α * z` is nonzero. -/
theorem phi_denom_ne_zero {α z : ℂ} (hα : α ∈ ball (0 : ℂ) 1)
    (hz : z ∈ closedBall (0 : ℂ) 1) : 1 - star α * z ≠ 0 := by
  have hα' : ‖α‖ < 1 := mem_ball_zero_iff.mp hα
  have hz' : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
  intro hzero
  have h1 : star α * z = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm : ‖star α * z‖ = 1 := by rw [h1, norm_one]
  rw [norm_mul, norm_star] at hnorm
  have hlt : ‖α‖ * ‖z‖ < 1 := by
    calc
      ‖α‖ * ‖z‖ ≤ ‖α‖ * 1 := mul_le_mul_of_nonneg_left hz' (norm_nonneg α)
      _ = ‖α‖ := mul_one _
      _ < 1 := hα'
  linarith

/-- Whenever `1 - star α * z ≠ 0`, `1 - ‖phi α z‖ ^ 2` factors cleanly. -/
theorem one_sub_norm_phi_sq {α z : ℂ} (hden : 1 - star α * z ≠ 0) :
    1 - ‖phi α z‖ ^ 2 = (1 - ‖α‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 - star α * z‖ ^ 2 := by
  have hden_pos : 0 < ‖1 - star α * z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hden)
  rw [phi, norm_div, div_pow, one_sub_div hden_pos.ne', phi_norm_sq_sub]

/-- Derivative formula for `phi α` away from its pole:
`(phi α)'(z) = (1 - ‖α‖ ^ 2) / (1 - star α * z) ^ 2`. -/
theorem hasDerivAt_phi {α z : ℂ} (hden : 1 - star α * z ≠ 0) :
    HasDerivAt (phi α) (((1 - ‖α‖ ^ 2 : ℝ) : ℂ) / (1 - star α * z) ^ 2) z := by
  have hnum : HasDerivAt (fun w : ℂ => w - α) 1 z :=
    (hasDerivAt_id z).sub_const α
  have hden_d : HasDerivAt (fun w : ℂ => 1 - star α * w) (-(star α)) z :=
    ((hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).const_mul (star α))).congr_deriv (by ring)
  have hdiv := hnum.div hden_d hden
  refine hdiv.congr_deriv ?_
  have hmul : α * star α = ((‖α‖ ^ 2 : ℝ) : ℂ) := mul_star_self_eq α
  have hnum_eq : 1 * (1 - star α * z) - (z - α) * -(star α) = ((1 - ‖α‖ ^ 2 : ℝ) : ℂ) := by
    calc
      1 * (1 - star α * z) - (z - α) * -(star α)
          = 1 - α * star α := by ring
      _ = 1 - ((‖α‖ ^ 2 : ℝ) : ℂ) := by rw [hmul]
      _ = ((1 - ‖α‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hnum_eq]

theorem phi_self (α : ℂ) : phi α α = 0 := by
  simp [phi]

theorem phi_zero (α : ℂ) : phi α 0 = -α := by
  simp [phi]

theorem mapsTo_phi_closedBall {α : ℂ} (hα : α ∈ ball (0 : ℂ) 1) :
    MapsTo (phi α) (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
  have hα' : ‖α‖ < 1 := mem_ball_zero_iff.mp hα
  have hα_pos : 0 < 1 - ‖α‖ ^ 2 := by nlinarith [norm_nonneg α]
  intro z hz
  have hz' : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
  have hz_nonneg : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hden := phi_denom_ne_zero hα hz
  have hquot : 0 ≤ 1 - ‖phi α z‖ ^ 2 := by
    rw [one_sub_norm_phi_sq hden]
    exact div_nonneg (mul_nonneg hα_pos.le hz_nonneg) (sq_nonneg _)
  rw [mem_closedBall_zero_iff]
  nlinarith [norm_nonneg (phi α z)]

theorem mapsTo_phi_ball {α : ℂ} (hα : α ∈ ball (0 : ℂ) 1) :
    MapsTo (phi α) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  have hα' : ‖α‖ < 1 := mem_ball_zero_iff.mp hα
  have hα_pos : 0 < 1 - ‖α‖ ^ 2 := by nlinarith [norm_nonneg α]
  intro z hz
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hz_pos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hden := phi_denom_ne_zero hα (ball_subset_closedBall hz)
  have hden_pos : 0 < ‖1 - star α * z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hden)
  have hquot : 0 < 1 - ‖phi α z‖ ^ 2 := by
    rw [one_sub_norm_phi_sq hden]
    exact div_pos (mul_pos hα_pos hz_pos) hden_pos
  rw [mem_ball_zero_iff]
  nlinarith [norm_nonneg (phi α z)]

theorem mapsTo_phi_sphere {α : ℂ} (hα : α ∈ ball (0 : ℂ) 1) :
    MapsTo (phi α) (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1) := by
  intro z hz
  have hz_norm : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
  have hz_cb : z ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, hz_norm]
  have hden := phi_denom_ne_zero hα hz_cb
  have hquot : 1 - ‖phi α z‖ ^ 2 = 0 := by
    rw [one_sub_norm_phi_sq hden, hz_norm]
    ring
  rw [mem_sphere_zero_iff_norm]
  nlinarith [norm_nonneg (phi α z)]

/-- Involutive inverse identity: `phi (-α) (phi α z) = z` whenever `1 - ‖α‖ ^ 2 ≠ 0`
and `1 - star α * z ≠ 0`. -/
theorem phi_neg_apply_phi {α z : ℂ} (hα : α ∈ ball (0 : ℂ) 1)
    (hz : z ∈ closedBall (0 : ℂ) 1) : phi (-α) (phi α z) = z := by
  have hden1 : 1 - star α * z ≠ 0 := phi_denom_ne_zero hα hz
  have hnegα : -α ∈ ball (0 : ℂ) 1 := by simpa using hα
  have hden2 : 1 - star (-α) * phi α z ≠ 0 :=
    phi_denom_ne_zero hnegα (mapsTo_phi_closedBall hα hz)
  dsimp only [phi] at hden2 ⊢
  simp only [star_neg, neg_mul, sub_neg_eq_add] at hden2 ⊢
  rw [div_eq_iff hden2]
  apply mul_right_cancel₀ hden1
  have hnum : ((z - α) / (1 - star α * z) + α) * (1 - star α * z) =
      z * (1 - α * star α) := by
    calc
      ((z - α) / (1 - star α * z) + α) * (1 - star α * z)
          = (z - α) / (1 - star α * z) * (1 - star α * z) + α * (1 - star α * z) := by ring
      _ = (z - α) + α * (1 - star α * z) := by rw [div_mul_cancel₀ _ hden1]
      _ = z * (1 - α * star α) := by ring
  have hden_calc : z * (1 + star α * ((z - α) / (1 - star α * z))) * (1 - star α * z) =
      z * (1 - α * star α) := by
    calc
      z * (1 + star α * ((z - α) / (1 - star α * z))) * (1 - star α * z)
          = z * ((1 - star α * z) + star α * (((z - α) / (1 - star α * z)) * (1 - star α * z))) := by
            ring
      _ = z * ((1 - star α * z) + star α * (z - α)) := by rw [div_mul_cancel₀ _ hden1]
      _ = z * (1 - α * star α) := by ring
  exact hnum.trans hden_calc.symm

/-- 12.4: For every `α ∈ U`, `phi α` is holomorphic away from `1 - star α * z = 0`
(in particular on an open neighborhood of `closure U`), maps `α` to `0`, maps `T`
bijectively onto `T` and `U` bijectively onto `U` with inverse `phi (-α)`, and
satisfies `(phi α)'(0) = 1 - ‖α‖ ^ 2` and `(phi α)'(α) = (1 - ‖α‖ ^ 2)⁻¹`. -/
theorem theorem12_4 {α : ℂ} (hα : α ∈ ball (0 : ℂ) 1) :
    DifferentiableOn ℂ (phi α) {z : ℂ | 1 - star α * z ≠ 0} ∧
    phi α α = 0 ∧
    BijOn (phi α) (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1) ∧
    BijOn (phi α) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) ∧
    (∀ z ∈ closedBall (0 : ℂ) 1, phi (-α) (phi α z) = z ∧ phi α (phi (-α) z) = z) ∧
    deriv (phi α) 0 = ((1 - ‖α‖ ^ 2 : ℝ) : ℂ) ∧
    deriv (phi α) α = (((1 - ‖α‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hnegα : -α ∈ ball (0 : ℂ) 1 := by simpa using hα
  have hinv : ∀ z ∈ closedBall (0 : ℂ) 1,
      phi (-α) (phi α z) = z ∧ phi α (phi (-α) z) = z := by
    intro z hz
    refine ⟨phi_neg_apply_phi hα hz, ?_⟩
    simpa only [neg_neg] using phi_neg_apply_phi hnegα hz
  refine ⟨?_, phi_self α, ?_, ?_, hinv, ?_, ?_⟩
  · intro z hz
    exact (hasDerivAt_phi hz).differentiableAt.differentiableWithinAt
  · refine ⟨mapsTo_phi_sphere hα, ?_, ?_⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      have hcb₁ : z₁ ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hz₁
      have hcb₂ : z₂ ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hz₂
      rw [← (hinv z₁ hcb₁).1, heq, (hinv z₂ hcb₂).1]
    · intro w hw
      refine ⟨phi (-α) w, mapsTo_phi_sphere hnegα hw, ?_⟩
      exact (hinv w (sphere_subset_closedBall hw)).2
  · refine ⟨mapsTo_phi_ball hα, ?_, ?_⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      have hcb₁ : z₁ ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hz₁
      have hcb₂ : z₂ ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hz₂
      rw [← (hinv z₁ hcb₁).1, heq, (hinv z₂ hcb₂).1]
    · intro w hw
      refine ⟨phi (-α) w, mapsTo_phi_ball hnegα hw, ?_⟩
      exact (hinv w (ball_subset_closedBall hw)).2
  · have hd0 : HasDerivAt (phi α) (((1 - ‖α‖ ^ 2 : ℝ) : ℂ) / (1 - star α * 0) ^ 2) 0 :=
      hasDerivAt_phi (by simp)
    simpa using hd0.deriv
  · have hα_cb : α ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hα
    have hdα := hasDerivAt_phi (phi_denom_ne_zero hα hα_cb)
    rw [hdα.deriv]
    have hα' : ‖α‖ < 1 := mem_ball_zero_iff.mp hα
    have hpos : (1 - ‖α‖ ^ 2 : ℝ) ≠ 0 := by nlinarith [norm_nonneg α]
    have hden_eq : (1 : ℂ) - star α * α = ((1 - ‖α‖ ^ 2 : ℝ) : ℂ) := by
      rw [star_mul_self_eq]; push_cast; ring
    rw [hden_eq]
    exact_mod_cast (show (1 - ‖α‖ ^ 2) / (1 - ‖α‖ ^ 2) ^ 2 = (1 - ‖α‖ ^ 2)⁻¹ by
      field_simp [hpos])

/-- 12.5 (Schwarz–Pick & extremal derivative problem): for `f ∈ H(U)` mapping `U` into `U`
and `α ∈ U` with `β = f α`:
1. `‖phi (f α) (f z)‖ ≤ ‖phi α z‖` for all `z ∈ U`,
2. `‖deriv f α‖ ≤ (1 - ‖f α‖ ^ 2) / (1 - ‖α‖ ^ 2)`, with equality (or pointwise equality at
   some `z ≠ α`) if and only if `f z = phi (-f α) (c * phi α z)` on `U` for some `‖c‖ = 1`,
3. Across all holomorphic `f : U → U` (without fixing `f α`), the maximum possible value of
   `‖deriv f α‖` is `(1 - ‖α‖ ^ 2)⁻¹`, attained if and only if `f z = c * phi α z` on `U`
   for some `‖c‖ = 1`. -/
theorem theorem12_5 {f : ℂ → ℂ} {α : ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hα : α ∈ ball (0 : ℂ) 1) :
    (∀ z ∈ ball (0 : ℂ) 1, ‖phi (f α) (f z)‖ ≤ ‖phi α z‖) ∧
    ‖deriv f α‖ ≤ (1 - ‖f α‖ ^ 2) / (1 - ‖α‖ ^ 2) ∧
    (((∃ z ∈ ball (0 : ℂ) 1, z ≠ α ∧ ‖phi (f α) (f z)‖ = ‖phi α z‖) ∨
        ‖deriv f α‖ = (1 - ‖f α‖ ^ 2) / (1 - ‖α‖ ^ 2)) ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ ball (0 : ℂ) 1, f z = phi (-f α) (c * phi α z)) ∧
    ‖deriv f α‖ ≤ (1 - ‖α‖ ^ 2)⁻¹ ∧
    (‖deriv f α‖ = (1 - ‖α‖ ^ 2)⁻¹ ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ ball (0 : ℂ) 1, f z = c * phi α z) := by
  set β : ℂ := f α
  have hβ : β ∈ ball (0 : ℂ) 1 := hmaps hα
  have hnegα : -α ∈ ball (0 : ℂ) 1 := by simpa using hα
  have hnegβ : -β ∈ ball (0 : ℂ) 1 := by simpa using hβ
  have hα_lt : ‖α‖ < 1 := mem_ball_zero_iff.mp hα
  have hβ_lt : ‖β‖ < 1 := mem_ball_zero_iff.mp hβ
  have h1α_pos : 0 < 1 - ‖α‖ ^ 2 := by nlinarith [norm_nonneg α]
  have h1β_pos : 0 < 1 - ‖β‖ ^ 2 := by nlinarith [norm_nonneg β]
  let g : ℂ → ℂ := fun w => phi β (f (phi (-α) w))
  have hg_maps : ∀ w ∈ ball (0 : ℂ) 1, g w ∈ ball (0 : ℂ) 1 := fun w hw =>
    mapsTo_phi_ball hβ (hmaps (mapsTo_phi_ball hnegα hw))
  have hg_bound : ∀ w ∈ ball (0 : ℂ) 1, ‖g w‖ ≤ 1 := fun w hw =>
    (mem_ball_zero_iff.mp (hg_maps w hw)).le
  have hphi_negα_zero : phi (-α) 0 = α := by simp [phi]
  have hg_zero : g 0 = 0 := by
    simp only [g, hphi_negα_zero, β, phi_self]
  have hg_diff : DifferentiableOn ℂ g (ball 0 1) := by
    intro w hw
    have hw_negα : phi (-α) w ∈ ball (0 : ℂ) 1 := mapsTo_phi_ball hnegα hw
    have hfw : f (phi (-α) w) ∈ ball (0 : ℂ) 1 := hmaps hw_negα
    have hd1 : DifferentiableAt ℂ (phi (-α)) w :=
      (hasDerivAt_phi (phi_denom_ne_zero hnegα (ball_subset_closedBall hw))).differentiableAt
    have hd2 : DifferentiableAt ℂ f (phi (-α) w) :=
      (hf _ hw_negα).differentiableAt (isOpen_ball.mem_nhds hw_negα)
    have hd3 : DifferentiableAt ℂ (phi β) (f (phi (-α) w)) :=
      (hasDerivAt_phi (phi_denom_ne_zero hβ (ball_subset_closedBall hfw))).differentiableAt
    exact (hd3.comp w (hd2.comp w hd1)).differentiableWithinAt
  have hg_deriv0 : deriv g 0 =
      (((1 - ‖β‖ ^ 2)⁻¹ : ℝ) : ℂ) * (deriv f α * ((1 - ‖α‖ ^ 2 : ℝ) : ℂ)) := by
    have hd1 : HasDerivAt (phi (-α)) (((1 - ‖α‖ ^ 2 : ℝ) : ℂ)) 0 := by
      have h := hasDerivAt_phi (α := -α) (z := 0) (by simp)
      simpa using h
    have hd2 : HasDerivAt f (deriv f α) (phi (-α) 0) := by
      rw [hphi_negα_zero]
      exact ((hf α hα).differentiableAt (isOpen_ball.mem_nhds hα)).hasDerivAt
    have hd3 : HasDerivAt (phi β) (((1 - ‖β‖ ^ 2)⁻¹ : ℝ) : ℂ) (f (phi (-α) 0)) := by
      rw [hphi_negα_zero]
      have h := (theorem12_4 hβ).2.2.2.2.2.2
      have hdβ := (hasDerivAt_phi (phi_denom_ne_zero hβ (ball_subset_closedBall hβ)))
      exact hdβ.congr_deriv (hdβ.deriv.symm.trans h)
    exact (hd3.comp 0 (hd2.comp 0 hd1)).deriv
  have hg_norm_deriv0 :
      ‖deriv g 0‖ = ‖deriv f α‖ * (1 - ‖α‖ ^ 2) / (1 - ‖β‖ ^ 2) := by
    rw [hg_deriv0, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr h1β_pos.le), Real.norm_of_nonneg h1α_pos.le]
    ring
  obtain ⟨hg_le, hg_d0_le, hg_rig⟩ := theorem12_2 hg_diff hg_bound hg_zero
  have hpt : ∀ z ∈ ball (0 : ℂ) 1, ‖phi β (f z)‖ ≤ ‖phi α z‖ := by
    intro z hz
    have hw : phi α z ∈ ball (0 : ℂ) 1 := mapsTo_phi_ball hα hz
    have hinv_z : phi (-α) (phi α z) = z :=
      phi_neg_apply_phi hα (ball_subset_closedBall hz)
    have h := hg_le (phi α z) hw
    simpa only [g, hinv_z] using h
  have hsp_deriv : ‖deriv f α‖ ≤ (1 - ‖β‖ ^ 2) / (1 - ‖α‖ ^ 2) := by
    rw [hg_norm_deriv0, div_le_one h1β_pos] at hg_d0_le
    exact (le_div_iff₀ h1α_pos).mpr hg_d0_le
  have hsp_eq_iff :
      ((∃ z ∈ ball (0 : ℂ) 1, z ≠ α ∧ ‖phi β (f z)‖ = ‖phi α z‖) ∨
        ‖deriv f α‖ = (1 - ‖β‖ ^ 2) / (1 - ‖α‖ ^ 2)) ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ ball (0 : ℂ) 1, f z = phi (-β) (c * phi α z) := by
    constructor
    · intro hcond
      have hg_cond : (∃ w ∈ ball (0 : ℂ) 1, w ≠ 0 ∧ ‖g w‖ = ‖w‖) ∨ ‖deriv g 0‖ = 1 := by
        rcases hcond with ⟨z, hz, hzne, hzeq⟩ | hdeq
        · left
          refine ⟨phi α z, mapsTo_phi_ball hα hz, ?_, ?_⟩
          · intro hw0
            apply hzne
            calc
              z = phi (-α) (phi α z) := (phi_neg_apply_phi hα (ball_subset_closedBall hz)).symm
              _ = phi (-α) 0 := by rw [hw0]
              _ = α := hphi_negα_zero
          · have hinv_z : phi (-α) (phi α z) = z :=
              phi_neg_apply_phi hα (ball_subset_closedBall hz)
            simpa only [g, hinv_z] using hzeq
        · right
          rw [hg_norm_deriv0, hdeq, div_mul_cancel₀ _ h1α_pos.ne', div_self h1β_pos.ne']
      obtain ⟨c, hc_norm, hc_eq⟩ := hg_rig hg_cond
      refine ⟨c, hc_norm, ?_⟩
      intro z hz
      have hw : phi α z ∈ ball (0 : ℂ) 1 := mapsTo_phi_ball hα hz
      have hinv_z : phi (-α) (phi α z) = z :=
        phi_neg_apply_phi hα (ball_subset_closedBall hz)
      have hgw : phi β (f z) = c * phi α z := by
        simpa only [g, hinv_z] using hc_eq (phi α z) hw
      calc
        f z = phi (-β) (phi β (f z)) :=
          (phi_neg_apply_phi hβ (ball_subset_closedBall (hmaps hz))).symm
        _ = phi (-β) (c * phi α z) := by rw [hgw]
    · rintro ⟨c, hc_norm, hfeq⟩
      right
      have hev : Filter.EventuallyEq (nhds α) f (phi (-β) ∘ fun z => c * phi α z) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨ball 0 1, isOpen_ball.mem_nhds hα, hfeq⟩
      have hd_inner : HasDerivAt (fun z => c * phi α z)
          (c * (((1 - ‖α‖ ^ 2)⁻¹ : ℝ) : ℂ)) α := by
        have hdα := hasDerivAt_phi (phi_denom_ne_zero hα (ball_subset_closedBall hα))
        have hdα' : HasDerivAt (phi α) (((1 - ‖α‖ ^ 2)⁻¹ : ℝ) : ℂ) α :=
          hdα.congr_deriv (hdα.deriv.symm.trans (theorem12_4 hα).2.2.2.2.2.2)
        exact hdα'.const_mul c
      have hd_outer : HasDerivAt (phi (-β)) (((1 - ‖β‖ ^ 2 : ℝ) : ℂ)) (c * phi α α) := by
        rw [phi_self, mul_zero]
        have hd0 := hasDerivAt_phi (α := -β) (z := 0) (by simp)
        simpa using hd0
      have hcomp_α := hd_outer.comp α hd_inner
      have hdf_α : deriv f α =
          (((1 - ‖β‖ ^ 2 : ℝ) : ℂ)) * (c * (((1 - ‖α‖ ^ 2)⁻¹ : ℝ) : ℂ)) :=
        hev.deriv_eq.trans hcomp_α.deriv
      rw [hdf_α, norm_mul, norm_mul, hc_norm, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg h1β_pos.le, Real.norm_of_nonneg (inv_nonneg.mpr h1α_pos.le),
        div_eq_mul_inv]
  have hext_le : ‖deriv f α‖ ≤ (1 - ‖α‖ ^ 2)⁻¹ := by
    have hnum_le : 1 - ‖β‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖β‖]
    calc
      ‖deriv f α‖ ≤ (1 - ‖β‖ ^ 2) / (1 - ‖α‖ ^ 2) := hsp_deriv
      _ ≤ 1 / (1 - ‖α‖ ^ 2) := div_le_div_of_nonneg_right hnum_le h1α_pos.le
      _ = (1 - ‖α‖ ^ 2)⁻¹ := one_div _
  have hext_eq_iff :
      ‖deriv f α‖ = (1 - ‖α‖ ^ 2)⁻¹ ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ ball (0 : ℂ) 1, f z = c * phi α z := by
    constructor
    · intro hmax
      have hβ_sq_zero : ‖β‖ ^ 2 = 0 := by
        have h1 : (1 - ‖α‖ ^ 2)⁻¹ ≤ (1 - ‖β‖ ^ 2) / (1 - ‖α‖ ^ 2) := hmax ▸ hsp_deriv
        rw [← one_div, div_le_div_iff_of_pos_right h1α_pos] at h1
        nlinarith [sq_nonneg ‖β‖]
      have hβ_zero : β = 0 := by
        apply norm_eq_zero.mp
        nlinarith [norm_nonneg β]
      have hsp_eq : ‖deriv f α‖ = (1 - ‖β‖ ^ 2) / (1 - ‖α‖ ^ 2) := by
        rw [hmax, hβ_zero, norm_zero, zero_pow two_ne_zero, sub_zero, one_div]
      obtain ⟨c, hc_norm, hc_eq⟩ := hsp_eq_iff.mp (Or.inr hsp_eq)
      refine ⟨c, hc_norm, fun z hz => ?_⟩
      have h := hc_eq z hz
      rw [hβ_zero] at h
      simpa [phi] using h
    · rintro ⟨c, hc_norm, hfeq⟩
      have hev : Filter.EventuallyEq (nhds α) f (fun z => c * phi α z) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨ball 0 1, isOpen_ball.mem_nhds hα, hfeq⟩
      have hdα := hasDerivAt_phi (phi_denom_ne_zero hα (ball_subset_closedBall hα))
      have hdα' : HasDerivAt (phi α) (((1 - ‖α‖ ^ 2)⁻¹ : ℝ) : ℂ) α :=
        hdα.congr_deriv (hdα.deriv.symm.trans (theorem12_4 hα).2.2.2.2.2.2)
      have hdf_α : deriv f α = c * (((1 - ‖α‖ ^ 2)⁻¹ : ℝ) : ℂ) :=
        hev.deriv_eq.trans (hdα'.const_mul c).deriv
      rw [hdf_α, norm_mul, hc_norm, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.mpr h1α_pos.le)]
  exact ⟨hpt, hsp_deriv, hsp_eq_iff, hext_le, hext_eq_iff⟩

/-- 12.6 (Classification of disk automorphisms): a map `f : ℂ → ℂ` is a holomorphic
bijection of `U = ball 0 1` onto `U` if and only if there exist `α ∈ U` and `c ∈ ℂ`
with `‖c‖ = 1` such that `f z = c * phi α z` for all `z ∈ U`; moreover, `α` and `c`
are uniquely determined by `f` on `U`. -/
theorem theorem12_6 {f : ℂ → ℂ} :
    ((DifferentiableOn ℂ f (ball 0 1) ∧ BijOn f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) ↔
      ∃ α ∈ ball (0 : ℂ) 1, ∃ c : ℂ, ‖c‖ = 1 ∧
        ∀ z ∈ ball (0 : ℂ) 1, f z = c * phi α z) ∧
    (∀ {α₁ α₂ c₁ c₂ : ℂ},
      α₁ ∈ ball (0 : ℂ) 1 → α₂ ∈ ball (0 : ℂ) 1 → ‖c₁‖ = 1 → ‖c₂‖ = 1 →
      (∀ z ∈ ball (0 : ℂ) 1, c₁ * phi α₁ z = c₂ * phi α₂ z) →
      α₁ = α₂ ∧ c₁ = c₂) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨hf, hbij⟩
    have hhol : RudinRCA.Chapter10.HolomorphicOn f (ball 0 1) := fun z hz =>
      (hf z hz).differentiableAt (isOpen_ball.mem_nhds hz)
    obtain ⟨hdf_nz, _, g, hg_hol, _, hfg, hderiv_g⟩ :=
      RudinRCA.Chapter10.theorem10_33.1 isOpen_ball hhol hbij.injOn
    have himg : f '' ball (0 : ℂ) 1 = ball (0 : ℂ) 1 := hbij.image_eq
    have hg_diff : DifferentiableOn ℂ g (ball 0 1) := fun w hw =>
      (hg_hol w (himg.symm ▸ hw)).differentiableWithinAt
    have hg_maps : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := fun w hw =>
      (hfg w (himg.symm ▸ hw)).1
    have h0_mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self zero_lt_one
    set α : ℂ := g 0
    have hα : α ∈ ball (0 : ℂ) 1 := hg_maps h0_mem
    have hfα : f α = 0 := (hfg 0 (himg.symm ▸ h0_mem)).2
    have h1α_pos : 0 < 1 - ‖α‖ ^ 2 := by
      have hα_lt : ‖α‖ < 1 := mem_ball_zero_iff.mp hα
      nlinarith [norm_nonneg α]
    have hf_ext := (theorem12_5 hf hbij.mapsTo hα)
    have hf_ub : ‖deriv f α‖ ≤ (1 - ‖α‖ ^ 2)⁻¹ := hf_ext.2.2.2.1
    have hg_sp : ‖deriv g 0‖ ≤ (1 - ‖g 0‖ ^ 2) / (1 - ‖(0 : ℂ)‖ ^ 2) :=
      (theorem12_5 hg_diff hg_maps h0_mem).2.1
    have hg_ub : ‖deriv g 0‖ ≤ 1 - ‖α‖ ^ 2 := by
      simpa [α] using hg_sp
    have hdg0 : deriv g 0 = (deriv f α)⁻¹ := by
      simpa only [hfα] using hderiv_g α hα
    have hdf_pos : 0 < ‖deriv f α‖ := norm_pos_iff.mpr (hdf_nz α hα)
    have hf_lb : (1 - ‖α‖ ^ 2)⁻¹ ≤ ‖deriv f α‖ := by
      rw [hdg0, norm_inv] at hg_ub
      exact (inv_le_comm₀ hdf_pos h1α_pos).mp hg_ub
    have hdf_eq : ‖deriv f α‖ = (1 - ‖α‖ ^ 2)⁻¹ := le_antisymm hf_ub hf_lb
    obtain ⟨c, hc_norm, hc_eq⟩ := hf_ext.2.2.2.2.mp hdf_eq
    exact ⟨α, hα, c, hc_norm, hc_eq⟩
  · rintro ⟨α, hα, c, hc_norm, hfeq⟩
    have hc_ne : c ≠ 0 := norm_ne_zero_iff.mp (hc_norm.symm ▸ one_ne_zero)
    have hphi_bij := (theorem12_4 hα).2.2.2.1
    have hg_diff : DifferentiableOn ℂ (fun z => c * phi α z) (ball 0 1) := by
      intro z hz
      exact (((hasDerivAt_phi (phi_denom_ne_zero hα (ball_subset_closedBall hz))).const_mul
        c).differentiableAt).differentiableWithinAt
    refine ⟨hg_diff.congr hfeq, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rw [hfeq z hz, mem_ball_zero_iff, norm_mul, hc_norm, one_mul]
      exact mem_ball_zero_iff.mp (hphi_bij.mapsTo hz)
    · intro z₁ hz₁ z₂ hz₂ heq
      rw [hfeq z₁ hz₁, hfeq z₂ hz₂] at heq
      exact hphi_bij.injOn hz₁ hz₂ (mul_left_cancel₀ hc_ne heq)
    · intro w hw
      have hw' : c⁻¹ * w ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff, norm_mul, norm_inv, hc_norm, inv_one, one_mul]
        exact mem_ball_zero_iff.mp hw
      obtain ⟨z, hz, hzw⟩ := hphi_bij.surjOn hw'
      refine ⟨z, hz, ?_⟩
      rw [hfeq z hz, hzw, mul_inv_cancel_left₀ hc_ne]
  · intro α₁ α₂ c₁ c₂ hα₁ hα₂ hc₁ hc₂ heq
    have hc₂_ne : c₂ ≠ 0 := norm_ne_zero_iff.mp (hc₂.symm ▸ one_ne_zero)
    have h0 : c₂ * phi α₂ α₁ = 0 := by
      have h := (heq α₁ hα₁).symm
      rwa [phi_self, mul_zero] at h
    have hphi_zero : phi α₂ α₁ = 0 := (mul_eq_zero.mp h0).resolve_left hc₂_ne
    have hα_eq : α₁ = α₂ := by
      calc
        α₁ = phi (-α₂) (phi α₂ α₁) :=
          (phi_neg_apply_phi hα₂ (ball_subset_closedBall hα₁)).symm
        _ = phi (-α₂) 0 := by rw [hphi_zero]
        _ = α₂ := by simp [phi]
    subst hα_eq
    let z₁ : ℂ := if α₁ = 0 then (1 / 2 : ℂ) else 0
    have hz₁_mem : z₁ ∈ ball (0 : ℂ) 1 := by
      by_cases h0' : α₁ = 0
      · simp only [z₁, h0', ↓reduceIte, mem_ball_zero_iff]
        norm_num
      · simp only [z₁, h0', ↓reduceIte, mem_ball_self zero_lt_one]
    have hz₁_ne : z₁ ≠ α₁ := by
      by_cases h0' : α₁ = 0
      · simp only [z₁, h0', ↓reduceIte]
        norm_num
      · simp only [z₁, h0', ↓reduceIte]
        exact Ne.symm h0'
    have hphi_ne : phi α₁ z₁ ≠ 0 := by
      intro hp0
      apply hz₁_ne
      calc
        z₁ = phi (-α₁) (phi α₁ z₁) :=
          (phi_neg_apply_phi hα₁ (ball_subset_closedBall hz₁_mem)).symm
        _ = phi (-α₁) 0 := by rw [hp0]
        _ = α₁ := by simp [phi]
    exact ⟨rfl, mul_right_cancel₀ hphi_ne (heq z₁ hz₁_mem)⟩

/-! ## Unbounded-strip example, sublinear entire rigidity, and Hadamard three-lines (12.7–12.8) -/

/-- Maximum modulus of `f` on the circle `|z| = r`, `M(r) = sup_{|z|=r} ‖f(z)‖`,
used in 12.7(b). -/
noncomputable def circleMaxNorm (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' sphere (0 : ℂ) r)

/-- 12.7(a) (Unbounded-strip counterexample to naïve maximum modulus): on the open
strip `S = {z : ℂ | |z.im| < π / 2}`, `f(z) = exp(exp z)` is entire, has `‖f(z)‖ = 1`
at every point of `frontier S = {z : ℂ | |z.im| = π / 2}` (so `boundaryNorm f S = 1`),
yet `‖f(x)‖ → +∞` as `x → +∞` along the real axis inside `S`. -/
theorem node12_7_strip_counterexample :
    let S : Set ℂ := {z : ℂ | |z.im| < Real.pi / 2}
    let f : ℂ → ℂ := fun z => Complex.exp (Complex.exp z)
    IsOpen S ∧
    ¬ IsBounded S ∧
    Differentiable ℂ f ∧
    frontier S = {z : ℂ | |z.im| = Real.pi / 2} ∧
    (∀ z ∈ frontier S, ‖f z‖ = 1) ∧
    boundaryNorm f S = 1 ∧
    Filter.Tendsto (fun x : ℝ => ‖f x‖) Filter.atTop Filter.atTop ∧
    (∀ M : ℝ, ∃ x : ℝ, (x : ℂ) ∈ S ∧ M < ‖f x‖) := by
  dsimp only
  let S : Set ℂ := {z : ℂ | |z.im| < Real.pi / 2}
  let f : ℂ → ℂ := fun z => Complex.exp (Complex.exp z)
  have hpi2 : 0 < Real.pi / 2 := half_pos Real.pi_pos
  have hS_open : IsOpen S := isOpen_lt Complex.continuous_im.abs continuous_const
  have hS_unbdd : ¬ IsBounded S := by
    intro hbdd
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbdd
    let x : ℝ := max R 0 + 1
    have hx_mem : (x : ℂ) ∈ S := by
      change |(x : ℂ).im| < Real.pi / 2
      simp only [Complex.ofReal_im, abs_zero]
      exact hpi2
    have hx_le : ‖(x : ℂ)‖ ≤ R := hR (x : ℂ) hx_mem
    have hx_pos : 0 < x := by positivity
    rw [Complex.norm_real, Real.norm_of_nonneg hx_pos.le] at hx_le
    have : R < x := lt_of_le_of_lt (le_max_left R 0) (lt_add_one _)
    linarith
  obtain ⟨hf_diff, hlo, hhi, _, _, _⟩ := theorem12_9_sharpness
  have hcl : closure S = {z : ℂ | |z.im| ≤ Real.pi / 2} := by
    apply Subset.antisymm
    · exact closure_minimal (fun z (hz : |z.im| < Real.pi / 2) => le_of_lt hz)
        (isClosed_le Complex.continuous_im.abs continuous_const)
    · intro z (hz : |z.im| ≤ Real.pi / 2)
      rw [Metric.mem_closure_iff]
      intro ε hε
      let t : ℝ := max 0 (1 - ε / (2 * (|z.im| + 1)))
      have ht_nonneg : 0 ≤ t := le_max_left _ _
      have ht_lt_one : t < 1 := by
        have hpos : 0 < ε / (2 * (|z.im| + 1)) := by positivity
        exact max_lt zero_lt_one (by linarith)
      let w : ℂ := ⟨z.re, t * z.im⟩
      refine ⟨w, ?_, ?_⟩
      · change |w.im| < Real.pi / 2
        dsimp only [w]
        rw [abs_mul, abs_of_nonneg ht_nonneg]
        calc
          t * |z.im| ≤ t * (Real.pi / 2) := mul_le_mul_of_nonneg_left hz ht_nonneg
          _ < 1 * (Real.pi / 2) := mul_lt_mul_of_pos_right ht_lt_one hpi2
          _ = Real.pi / 2 := one_mul _
      · rw [dist_eq_norm]
        have hsub : z - w = ((1 - t) * z.im : ℝ) * Complex.I := by
          apply Complex.ext <;> simp [w]; ring
        rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_mul, abs_of_pos (sub_pos.mpr ht_lt_one)]
        have h1t_le : 1 - t ≤ ε / (2 * (|z.im| + 1)) := by
          have : 1 - ε / (2 * (|z.im| + 1)) ≤ t := le_max_right _ _
          linarith
        calc
          (1 - t) * |z.im| ≤ (ε / (2 * (|z.im| + 1))) * |z.im| :=
            mul_le_mul_of_nonneg_right h1t_le (abs_nonneg _)
          _ < (ε / (2 * (|z.im| + 1))) * (2 * (|z.im| + 1)) := by
            apply mul_lt_mul_of_pos_left _ (by positivity)
            linarith [abs_nonneg z.im]
          _ = ε := div_mul_cancel₀ ε (by positivity)
  have hfr : frontier S = {z : ℂ | |z.im| = Real.pi / 2} := by
    rw [frontier, hcl, hS_open.interior_eq]
    ext z
    change (|z.im| ≤ Real.pi / 2 ∧ ¬ |z.im| < Real.pi / 2) ↔ |z.im| = Real.pi / 2
    rw [not_lt]
    exact ⟨fun ⟨h1, h2⟩ => le_antisymm h1 h2, fun h => ⟨h.le, h.ge⟩⟩
  have hfr_one : ∀ z ∈ frontier S, ‖f z‖ = 1 := by
    intro z hz
    rw [hfr] at hz
    change |z.im| = Real.pi / 2 at hz
    rcases abs_eq hpi2.le |>.mp hz with hpos | hneg
    · exact hhi z hpos
    · exact hlo z hneg
  have hbn : boundaryNorm f S = 1 := by
    have hw_mem : ((Real.pi / 2 : ℝ) : ℂ) * Complex.I ∈ frontier S := by
      rw [hfr]
      change |(((Real.pi / 2 : ℝ) : ℂ) * Complex.I).im| = Real.pi / 2
      simp [abs_of_pos hpi2]
    have himg : (fun z => ‖f z‖) '' frontier S = {1} := by
      ext y
      simp only [mem_image, mem_singleton_iff]
      exact ⟨fun ⟨z, hz, hzy⟩ => hzy.symm.trans (hfr_one z hz),
        fun hy => ⟨((Real.pi / 2 : ℝ) : ℂ) * Complex.I, hw_mem,
          (hfr_one _ hw_mem).trans hy.symm⟩⟩
    rw [boundaryNorm, himg, csSup_singleton]
  have htend : Filter.Tendsto (fun x : ℝ => ‖f x‖) Filter.atTop Filter.atTop := by
    have hfun : (fun x : ℝ => ‖f x‖) = fun x : ℝ => Real.exp (Real.exp x) := by
      ext x
      simp [f, Complex.norm_exp, Complex.exp_re]
    rw [hfun]
    exact Real.tendsto_exp_atTop.comp Real.tendsto_exp_atTop
  have hunbdd_val : ∀ M : ℝ, ∃ x : ℝ, (x : ℂ) ∈ S ∧ M < ‖f x‖ := by
    intro M
    obtain ⟨x, hx⟩ := (Filter.tendsto_atTop.mp htend (M + 1)).exists
    refine ⟨x, ?_, by linarith⟩
    change |(x : ℂ).im| < Real.pi / 2
    simp only [Complex.ofReal_im, abs_zero]
    exact hpi2
  exact ⟨hS_open, hS_unbdd, hf_diff, hfr, hfr_one, hbn, htend, hunbdd_val⟩

/-- 12.7(b) (Sublinear entire rigidity, printed `M(r) / r → 0` form): if `f` is entire
and `lim_{r → ∞} circleMaxNorm f r / r = 0`, then `f` is constant. -/
theorem node12_7_sublinear_entire_circleMax {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hlim : Filter.Tendsto (fun r : ℝ => circleMaxNorm f r / r) Filter.atTop (nhds 0)) :
    ∀ z : ℂ, f z = f 0 := by
  suffices hderiv : ∀ c : ℂ, deriv f c = 0 from
    fun z => is_const_of_deriv_eq_zero hf hderiv z 0
  intro c
  apply norm_le_zero_iff.mp
  have hbound : ∀ R : ℝ, 0 < R →
      ‖deriv f c‖ ≤ (circleMaxNorm f (R + ‖c‖) / (R + ‖c‖)) * (1 + ‖c‖ * R⁻¹) := by
    intro R hR
    let r : ℝ := R + ‖c‖
    have hr_pos : 0 < r := add_pos_of_pos_of_nonneg hR (norm_nonneg c)
    have hcb_le : ∀ z ∈ closedBall (0 : ℂ) r, ‖f z‖ ≤ circleMaxNorm f r := by
      intro z hz
      have hz_cl : z ∈ closure (ball (0 : ℂ) r) := by rwa [closure_ball 0 hr_pos.ne']
      have h := theorem12_1_boundary_bound isBounded_ball hf.differentiableOn
        hf.continuous.continuousOn hz_cl
      simpa only [boundaryNorm, circleMaxNorm, frontier_ball (0 : ℂ) hr_pos.ne'] using h
    have hsph_le : ∀ z ∈ sphere c R, ‖f z‖ ≤ circleMaxNorm f r := by
      intro z hz
      apply hcb_le z
      rw [mem_closedBall_zero_iff]
      calc
        ‖z‖ = ‖(z - c) + c‖ := by ring_nf
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
        _ = R + ‖c‖ := by rw [mem_sphere_iff_norm.mp hz]
    have hcd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hf.diffContOnCl hsph_le
    refine hcd.trans_eq ?_
    dsimp only [r]
    field_simp [hR.ne', hr_pos.ne']
  have ht1 : Filter.Tendsto (fun R : ℝ => circleMaxNorm f (R + ‖c‖) / (R + ‖c‖))
      Filter.atTop (nhds 0) :=
    hlim.comp (Filter.tendsto_atTop_add_const_right Filter.atTop ‖c‖ Filter.tendsto_id)
  have ht2 : Filter.Tendsto (fun R : ℝ => 1 + ‖c‖ * R⁻¹)
      Filter.atTop (nhds (1 + ‖c‖ * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv_atTop_zero)
  have ht_prod : Filter.Tendsto
      (fun R : ℝ => (circleMaxNorm f (R + ‖c‖) / (R + ‖c‖)) * (1 + ‖c‖ * R⁻¹))
      Filter.atTop (nhds 0) := by
    simpa using ht1.mul ht2
  exact tendsto_le_of_eventuallyLE tendsto_const_nhds ht_prod
    ((Filter.eventually_gt_atTop (0 : ℝ)).mono fun R hR => hbound R hR)

/-- 12.7(b) (Sublinear entire rigidity, `‖f z‖ / ‖z‖ → 0` as `z → ∞` form): if `f` is
entire and `‖f z‖ / ‖z‖ → 0` along `Filter.cocompact ℂ`, then `circleMaxNorm f r / r → 0`
as `r → +∞` and `f` is constant. -/
theorem node12_7_sublinear_entire {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hlim : Filter.Tendsto (fun z : ℂ => ‖f z‖ / ‖z‖) (Filter.cocompact ℂ) (nhds 0)) :
    Filter.Tendsto (fun r : ℝ => circleMaxNorm f r / r) Filter.atTop (nhds 0) ∧
    (∀ z : ℂ, f z = f 0) := by
  have hcm : Filter.Tendsto (fun r : ℝ => circleMaxNorm f r / r) Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hmem : {z : ℂ | ‖f z‖ / ‖z‖ ∈ ball (0 : ℝ) (ε / 2)} ∈ Filter.cocompact ℂ :=
      hlim (ball_mem_nhds 0 (half_pos hε))
    obtain ⟨K, hK, hKsub⟩ := Filter.mem_cocompact.mp hmem
    obtain ⟨R₀, hR₀⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
    refine ⟨max R₀ 0 + 1, fun r hr => ?_⟩
    have hr_pos : 0 < r := by
      have : 0 ≤ max R₀ 0 := le_max_right _ _
      linarith
    have hr_gt : R₀ < r := by
      have : R₀ ≤ max R₀ 0 := le_max_left _ _
      linarith
    have hpt_mem : (r : ℂ) ∈ sphere (0 : ℂ) r := by
      rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg hr_pos.le]
    have hnonempty : ((fun z => ‖f z‖) '' sphere (0 : ℂ) r).Nonempty :=
      ⟨‖f (r : ℂ)‖, (r : ℂ), hpt_mem, rfl⟩
    have hsup_le : circleMaxNorm f r ≤ (ε / 2) * r := by
      apply csSup_le hnonempty
      rintro _ ⟨z, hz, rfl⟩
      have hz_norm : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
      have hz_notK : z ∉ K := fun hzK => by linarith [hR₀ z hzK]
      have hz_ball : ‖f z‖ / ‖z‖ ∈ ball (0 : ℝ) (ε / 2) := hKsub hz_notK
      rw [mem_ball_zero_iff, Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)),
        hz_norm, div_lt_iff₀ hr_pos] at hz_ball
      exact hz_ball.le
    have hsup_nonneg : 0 ≤ circleMaxNorm f r := by
      have hbdd : BddAbove ((fun z => ‖f z‖) '' sphere (0 : ℂ) r) :=
        ((isCompact_sphere (0 : ℂ) r).image hf.continuous.norm).bddAbove
      exact le_trans (norm_nonneg (f (r : ℂ)))
        (le_csSup hbdd ⟨(r : ℂ), hpt_mem, rfl⟩)
    rw [dist_zero_right, Real.norm_of_nonneg (div_nonneg hsup_nonneg hr_pos.le)]
    have hdiv_le : circleMaxNorm f r / r ≤ ε / 2 :=
      (div_le_iff₀ hr_pos).mpr hsup_le
    linarith
  exact ⟨hcm, node12_7_sublinear_entire_circleMax hf hcm⟩

/-- 12.7 combined statement packaging both examples on p. 256. -/
theorem theorem12_7 :
    (let S : Set ℂ := {z : ℂ | |z.im| < Real.pi / 2}
     let f : ℂ → ℂ := fun z => Complex.exp (Complex.exp z)
     IsOpen S ∧ ¬ IsBounded S ∧ Differentiable ℂ f ∧
     frontier S = {z : ℂ | |z.im| = Real.pi / 2} ∧
     (∀ z ∈ frontier S, ‖f z‖ = 1) ∧ boundaryNorm f S = 1 ∧
     Filter.Tendsto (fun x : ℝ => ‖f x‖) Filter.atTop Filter.atTop) ∧
    (∀ {f : ℂ → ℂ}, Differentiable ℂ f →
      Filter.Tendsto (fun r : ℝ => circleMaxNorm f r / r) Filter.atTop (nhds 0) →
      ∀ z : ℂ, f z = f 0) ∧
    (∀ {f : ℂ → ℂ}, Differentiable ℂ f →
      Filter.Tendsto (fun z : ℂ => ‖f z‖ / ‖z‖) (Filter.cocompact ℂ) (nhds 0) →
      ∀ z : ℂ, f z = f 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _⟩ := node12_7_strip_counterexample
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩,
    fun hf hlim => node12_7_sublinear_entire_circleMax hf hlim,
    fun hf hlim => (node12_7_sublinear_entire hf hlim).2⟩

/-- Supremum of `‖f(x + i y)‖` along the vertical line `Re z = x`, used in 12.8. -/
noncomputable abbrev lineSupNorm (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  Complex.HadamardThreeLines.sSupNormIm f x

/-- Equivalence between `lineSupNorm f x` (`sSup` over `Re z = x`) and the `sSup` of
`y ↦ ‖f (x + y * I)‖` over `y : ℝ`. -/
theorem lineSupNorm_eq_sSup_im (f : ℂ → ℂ) (x : ℝ) :
    lineSupNorm f x = sSup (range fun y : ℝ => ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖) := by
  unfold lineSupNorm Complex.HadamardThreeLines.sSupNormIm
  congr 1
  ext r
  simp only [mem_image, Function.comp_apply, mem_preimage, mem_singleton_iff, mem_range]
  constructor
  · rintro ⟨z, rfl, rfl⟩
    refine ⟨z.im, ?_⟩
    rw [Complex.re_add_im z]
  · rintro ⟨y, rfl⟩
    refine ⟨(x : ℂ) + (y : ℂ) * Complex.I, ?_, rfl⟩
    simp

/-- General-strip Hadamard three-lines theorem and logarithmic-convexity corollary on
`[l, u]` (`l < u`), including the vanishing dichotomy. -/
theorem theorem12_8_general_strip {f : ℂ → ℂ} {l u : ℝ} (hul : l < u)
    (hf : DifferentiableOn ℂ f {z : ℂ | l < z.re ∧ z.re < u})
    (hc : ContinuousOn f {z : ℂ | l ≤ z.re ∧ z.re ≤ u})
    (hbdd : ∃ B : ℝ, ∀ z : ℂ, l ≤ z.re ∧ z.re ≤ u → ‖f z‖ ≤ B) :
    (∀ {M₀ M₁ : ℝ},
      (∀ y : ℝ, ‖f ((l : ℂ) + (y : ℂ) * Complex.I)‖ ≤ M₀) →
      (∀ y : ℝ, ‖f ((u : ℂ) + (y : ℂ) * Complex.I)‖ ≤ M₁) →
      ∀ z : ℂ, l ≤ z.re ∧ z.re ≤ u →
        ‖f z‖ ≤ M₀ ^ (1 - (z.re - l) / (u - l)) * M₁ ^ ((z.re - l) / (u - l))) ∧
    (∀ x ∈ Icc l u,
      lineSupNorm f x ≤
        (lineSupNorm f l) ^ (1 - (x - l) / (u - l)) *
          (lineSupNorm f u) ^ ((x - l) / (u - l))) ∧
    ((∀ z : ℂ, l ≤ z.re ∧ z.re ≤ u → f z = 0) ∨
      ((∀ x ∈ Icc l u, 0 < lineSupNorm f x) ∧
        ConvexOn ℝ (Icc l u) (fun x => Real.log (lineSupNorm f x)))) := by
  obtain ⟨B, hB_le⟩ := hbdd
  have hB : BddAbove ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip l u) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hB_le z hz
  have hd_sub : ∀ {x₁ x₂ : ℝ}, l ≤ x₁ → x₂ ≤ u →
      DiffContOnCl ℂ f (Complex.HadamardThreeLines.verticalStrip x₁ x₂) := by
    intro x₁ x₂ hx₁ hx₂
    refine ⟨hf.mono (fun z hz => ⟨lt_of_le_of_lt hx₁ hz.1, lt_of_lt_of_le hz.2 hx₂⟩),
      hc.mono ?_⟩
    have hcl_sub : closure (Complex.HadamardThreeLines.verticalStrip x₁ x₂) ⊆
        Complex.re ⁻¹' Icc x₁ x₂ :=
      closure_minimal (fun z (hz : x₁ < z.re ∧ z.re < x₂) => ⟨hz.1.le, hz.2.le⟩)
        (isClosed_Icc.preimage Complex.continuous_re)
    exact hcl_sub.trans (fun z (hz : x₁ ≤ z.re ∧ z.re ≤ x₂) => ⟨le_trans hx₁ hz.1, le_trans hz.2 hx₂⟩)
  have hB_sub : ∀ {x₁ x₂ : ℝ}, l ≤ x₁ → x₂ ≤ u →
      BddAbove ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip x₁ x₂) := by
    intro x₁ x₂ hx₁ hx₂
    refine hB.mono (Set.image_mono ?_)
    intro z (hz : x₁ ≤ z.re ∧ z.re ≤ x₂)
    exact (⟨le_trans hx₁ hz.1, le_trans hz.2 hx₂⟩ : l ≤ z.re ∧ z.re ≤ u)
  have hline_bdd : ∀ x ∈ Icc l u, BddAbove ((norm ∘ f) '' (Complex.re ⁻¹' {x})) := by
    intro x hx
    exact hB.mono (Set.image_mono fun z hz => by
      simp only [mem_preimage, mem_singleton_iff] at hz
      exact ⟨hz ▸ hx.1, hz ▸ hx.2⟩)
  have hnorm_le_line : ∀ z : ℂ, l ≤ z.re ∧ z.re ≤ u → ‖f z‖ ≤ lineSupNorm f z.re := by
    intro z hz
    exact le_csSup (hline_bdd z.re hz) (mem_image_of_mem (norm ∘ f) rfl)
  have hpt_bound : ∀ {M₀ M₁ : ℝ},
      (∀ y : ℝ, ‖f ((l : ℂ) + (y : ℂ) * Complex.I)‖ ≤ M₀) →
      (∀ y : ℝ, ‖f ((u : ℂ) + (y : ℂ) * Complex.I)‖ ≤ M₁) →
      ∀ z : ℂ, l ≤ z.re ∧ z.re ≤ u →
        ‖f z‖ ≤ M₀ ^ (1 - (z.re - l) / (u - l)) * M₁ ^ ((z.re - l) / (u - l)) := by
    intro M₀ M₁ hM₀ hM₁ z hz
    apply Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hul hz
      (hd_sub le_rfl le_rfl) hB
    · intro w hw
      simp only [mem_preimage, mem_singleton_iff] at hw
      have hw_eq : w = (l : ℂ) + (w.im : ℂ) * Complex.I := by
        simpa [hw] using (Complex.re_add_im w).symm
      rw [hw_eq]
      exact hM₀ w.im
    · intro w hw
      simp only [mem_preimage, mem_singleton_iff] at hw
      have hw_eq : w = (u : ℂ) + (w.im : ℂ) * Complex.I := by
        simpa [hw] using (Complex.re_add_im w).symm
      rw [hw_eq]
      exact hM₁ w.im
  have hsub_interp : ∀ {x₁ x₂ : ℝ}, x₁ < x₂ → l ≤ x₁ → x₂ ≤ u →
      ∀ x ∈ Icc x₁ x₂,
        lineSupNorm f x ≤
          (lineSupNorm f x₁) ^ (1 - (x - x₁) / (x₂ - x₁)) *
            (lineSupNorm f x₂) ^ ((x - x₁) / (x₂ - x₁)) := by
    intro x₁ x₂ hx₁₂ hx₁ hx₂ x hx
    have hx_mem_re : (x : ℂ) ∈ Complex.re ⁻¹' {x} := by simp
    apply csSup_le ⟨‖f (x : ℂ)‖, mem_image_of_mem (norm ∘ f) hx_mem_re⟩
    rintro _ ⟨z, hz_re, rfl⟩
    simp only [mem_preimage, mem_singleton_iff] at hz_re
    have hz_mem : z ∈ Complex.HadamardThreeLines.verticalClosedStrip x₁ x₂ :=
      ⟨hz_re ▸ hx.1, hz_re ▸ hx.2⟩
    have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      hx₁₂ hz_mem (hd_sub hx₁ hx₂) (hB_sub hx₁ hx₂)
      (fun w hw => le_csSup (hline_bdd x₁ ⟨hx₁, hx₁₂.le.trans hx₂⟩)
        (mem_image_of_mem (norm ∘ f) hw))
      (fun w hw => le_csSup (hline_bdd x₂ ⟨hx₁.trans hx₁₂.le, hx₂⟩)
        (mem_image_of_mem (norm ∘ f) hw))
    dsimp only [Function.comp_apply]
    rw [hz_re] at h
    exact h
  refine ⟨hpt_bound, hsub_interp hul le_rfl le_rfl, ?_⟩
  by_cases hall0 : ∀ z : ℂ, l ≤ z.re ∧ z.re ≤ u → f z = 0
  · exact Or.inl hall0
  · right
    push Not at hall0
    obtain ⟨z₀, hz₀, hfz₀⟩ := hall0
    have hpos : ∀ x ∈ Icc l u, 0 < lineSupNorm f x := by
      intro x₀ hx₀
      by_contra hnotpos
      have hx₀_zero : lineSupNorm f x₀ = 0 :=
        le_antisymm (not_lt.mp hnotpos) (Complex.HadamardThreeLines.sSupNormIm_nonneg f x₀)
      apply hfz₀
      rcases lt_trichotomy z₀.re x₀ with hlt | heq | hgt
      · have hlx₀ : l < x₀ := lt_of_le_of_lt hz₀.1 hlt
        have hz₀_sub : z₀ ∈ Complex.HadamardThreeLines.verticalClosedStrip l x₀ :=
          ⟨hz₀.1, hlt.le⟩
        have hle := Complex.HadamardThreeLines.norm_le_interpStrip_of_mem_verticalClosedStrip
          hlx₀ hz₀_sub (hd_sub le_rfl hx₀.2) (hB_sub le_rfl hx₀.2)
        have hzero : Complex.HadamardThreeLines.interpStrip' f l x₀ z₀ = 0 := by
          unfold Complex.HadamardThreeLines.interpStrip'
          exact ite_eq_left (Or.inr hx₀_zero)
        rw [hzero, norm_zero] at hle
        exact norm_le_zero_iff.mp hle
      · have hle : ‖f z₀‖ ≤ lineSupNorm f x₀ := heq ▸ hnorm_le_line z₀ hz₀
        rw [hx₀_zero] at hle
        exact norm_le_zero_iff.mp hle
      · have hx₀u : x₀ < u := lt_of_lt_of_le hgt hz₀.2
        have hz₀_sub : z₀ ∈ Complex.HadamardThreeLines.verticalClosedStrip x₀ u :=
          ⟨hgt.le, hz₀.2⟩
        have hle := Complex.HadamardThreeLines.norm_le_interpStrip_of_mem_verticalClosedStrip
          hx₀u hz₀_sub (hd_sub hx₀.1 le_rfl) (hB_sub hx₀.1 le_rfl)
        have hzero : Complex.HadamardThreeLines.interpStrip' f x₀ u z₀ = 0 := by
          unfold Complex.HadamardThreeLines.interpStrip'
          exact ite_eq_left (Or.inl hx₀_zero)
        rw [hzero, norm_zero] at hle
        exact norm_le_zero_iff.mp hle
    refine ⟨hpos, convex_Icc l u, ?_⟩
    have hlog_lt : ∀ {u₁ u₂ t₁ t₂ : ℝ}, u₁ < u₂ → u₁ ∈ Icc l u → u₂ ∈ Icc l u →
        0 ≤ t₁ → 0 ≤ t₂ → t₁ + t₂ = 1 →
        Real.log (lineSupNorm f (t₁ * u₁ + t₂ * u₂)) ≤
          t₁ * Real.log (lineSupNorm f u₁) + t₂ * Real.log (lineSupNorm f u₂) := by
      intro u₁ u₂ t₁ t₂ hu₁₂ hu₁ hu₂ ht₁ ht₂ ht12
      let x : ℝ := t₁ * u₁ + t₂ * u₂
      have ht₁_eq : t₁ = 1 - t₂ := by linarith
      have hx_sub : x ∈ Icc u₁ u₂ := by
        dsimp only [x]
        rw [ht₁_eq]
        refine ⟨?_, ?_⟩
        · have : 0 ≤ t₂ * (u₂ - u₁) := mul_nonneg ht₂ (sub_nonneg.mpr hu₁₂.le)
          linarith
        · have : 0 ≤ (1 - t₂) * (u₂ - u₁) := mul_nonneg (ht₁_eq ▸ ht₁) (sub_nonneg.mpr hu₁₂.le)
          linarith
      have hx_lu : x ∈ Icc l u := ⟨le_trans hu₁.1 hx_sub.1, le_trans hx_sub.2 hu₂.2⟩
      have hdiv : (x - u₁) / (u₂ - u₁) = t₂ := by
        have hne : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr hu₁₂.ne'
        have hnum : x - u₁ = t₂ * (u₂ - u₁) := by dsimp only [x]; rw [ht₁_eq]; ring
        rw [hnum, mul_div_cancel_right₀ _ hne]
      have h1div : 1 - (x - u₁) / (u₂ - u₁) = t₁ := by rw [hdiv]; linarith
      have hM_le : lineSupNorm f x ≤ (lineSupNorm f u₁) ^ t₁ * (lineSupNorm f u₂) ^ t₂ := by
        have h := hsub_interp hu₁₂ hu₁.1 hu₂.2 x hx_sub
        rwa [h1div, hdiv] at h
      have hpos₁ : 0 < lineSupNorm f u₁ := hpos u₁ hu₁
      have hpos₂ : 0 < lineSupNorm f u₂ := hpos u₂ hu₂
      calc
        Real.log (lineSupNorm f x)
            ≤ Real.log ((lineSupNorm f u₁) ^ t₁ * (lineSupNorm f u₂) ^ t₂) :=
          Real.log_le_log (hpos x hx_lu) hM_le
        _ = Real.log ((lineSupNorm f u₁) ^ t₁) + Real.log ((lineSupNorm f u₂) ^ t₂) :=
          Real.log_mul (Real.rpow_pos_of_pos hpos₁ t₁).ne' (Real.rpow_pos_of_pos hpos₂ t₂).ne'
        _ = t₁ * Real.log (lineSupNorm f u₁) + t₂ * Real.log (lineSupNorm f u₂) := by
          rw [Real.log_rpow hpos₁, Real.log_rpow hpos₂]
    intro x₁ hx₁ x₂ hx₂ a b ha hb hab
    simp only [smul_eq_mul]
    rcases lt_trichotomy x₁ x₂ with hlt | rfl | hgt
    · exact hlog_lt hlt hx₁ hx₂ ha hb hab
    · have ha_eq : a = 1 - b := by linarith
      have hcomb : a * x₁ + b * x₁ = x₁ := by rw [ha_eq]; ring
      have hcomb_log : a * Real.log (lineSupNorm f x₁) + b * Real.log (lineSupNorm f x₁) =
          Real.log (lineSupNorm f x₁) := by rw [ha_eq]; ring
      rw [hcomb, hcomb_log]
    · have h := hlog_lt hgt hx₂ hx₁ hb ha (by linarith)
      rw [add_comm (a * x₁) (b * x₂)]
      linarith

/-- 12.8 (Hadamard three-lines theorem and unnumbered logarithmic-convexity corollary):
on the strip `Ω = {z : ℂ | 0 < z.re ∧ z.re < 1}` with closure
`{z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}`, if `f` is holomorphic on `Ω`, continuous and bounded
on `closure Ω`:
1. If `‖f(i y)‖ ≤ M₀` and `‖f(1 + i y)‖ ≤ M₁` for all `y : ℝ`, then
   `‖f(z)‖ ≤ M₀ ^ (1 - z.re) * M₁ ^ z.re` for all `z ∈ closure Ω`;
2. `lineSupNorm f x ≤ (lineSupNorm f 0) ^ (1 - x) * (lineSupNorm f 1) ^ x` for all
   `x ∈ [0, 1]`;
3. (Corollary) Either `f = 0` on `closure Ω`, or `0 < lineSupNorm f x` on `[0, 1]` and
   `x ↦ log (lineSupNorm f x)` is convex on `[0, 1]`. -/
theorem theorem12_8 {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hc : ContinuousOn f {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1})
    (hbdd : ∃ B : ℝ, ∀ z : ℂ, 0 ≤ z.re ∧ z.re ≤ 1 → ‖f z‖ ≤ B) :
    (∀ {M₀ M₁ : ℝ},
      (∀ y : ℝ, ‖f ((y : ℂ) * Complex.I)‖ ≤ M₀) →
      (∀ y : ℝ, ‖f (1 + (y : ℂ) * Complex.I)‖ ≤ M₁) →
      ∀ z : ℂ, 0 ≤ z.re ∧ z.re ≤ 1 →
        ‖f z‖ ≤ M₀ ^ (1 - z.re) * M₁ ^ z.re) ∧
    (∀ x ∈ Icc (0 : ℝ) 1,
      lineSupNorm f x ≤ (lineSupNorm f 0) ^ (1 - x) * (lineSupNorm f 1) ^ x) ∧
    ((∀ z : ℂ, 0 ≤ z.re ∧ z.re ≤ 1 → f z = 0) ∨
      ((∀ x ∈ Icc (0 : ℝ) 1, 0 < lineSupNorm f x) ∧
        ConvexOn ℝ (Icc (0 : ℝ) 1) (fun x => Real.log (lineSupNorm f x)))) := by
  obtain ⟨hpt, hsup, hconv⟩ := theorem12_8_general_strip zero_lt_one hf hc hbdd
  refine ⟨?_, ?_, hconv⟩
  · intro M₀ M₁ hM₀ hM₁ z hz
    have h := hpt (by simpa using hM₀) (by simpa using hM₁) z hz
    simpa using h
  · intro x hx
    have h := hsup x hx
    simpa using h

end RudinRCA.Chapter12


noncomputable section

open Set Metric Bornology MeasureTheory Filter Topology Complex
open scoped Real Topology ENNReal NNReal ComplexConjugate

namespace RudinRCA.Chapter12

/-! ### Node 12.1 (completion): `H^∞(U)` Radial-Boundary-Value Norm Equality and Bound -/

section Node12_1

open RudinRCA.Chapter11

/-- 12.1(2) (`H^∞(U)` boundary-value norm identity, interior bound, and equality rigidity,
Rudin p. 253): for every `f ∈ H^∞(U)`, its unique radial/nontangential boundary function
`f* ∈ L^∞(T)` from Theorem 11.32 satisfies `‖f‖_∞ = ‖f*‖_∞` (both in `Lp ℂ ⊤` norm and literal
3.7 `rudinEssSup`), hence `‖f(z)‖ ≤ ‖f*‖_∞` for every `z ∈ U = ball 0 1`; moreover, if equality
`‖f(c)‖ = ‖f*‖_∞` holds at some point `c ∈ U`, then `f` is constant on `U`. -/
theorem theorem12_1_hInfty_boundary (f : HInfty) :
    ∃! f_star : Lp ℂ ⊤ unitCircleMeasure,
      (∀ z : ball (0 : ℂ) 1,
        (f : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ) z =
          unitPoissonIntegral f_star z.1) ∧
      (∀ᵐ (ζ : UnitCircle) ∂unitCircleMeasure,
        HasNontangentialLimit
          (extendZero (f : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ))
          ζ (f_star ζ)) ∧
      (∀ᵐ (ζ : UnitCircle) ∂unitCircleMeasure,
        Tendsto (fun r : ℝ =>
          extendZero (f : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ)
            ((r : ℂ) * (ζ : ℂ)))
          (𝓝[<] 1) (𝓝 (f_star ζ))) ∧
      ‖f‖ = ‖f_star‖ ∧
      ‖f‖ = rudinEssSup unitCircleMeasure f_star ∧
      (∀ z : ball (0 : ℂ) 1,
        ‖(f : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ) z‖ ≤ ‖f_star‖ ∧
        ‖(f : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ) z‖ ≤
          rudinEssSup unitCircleMeasure f_star) ∧
      (∀ c : ball (0 : ℂ) 1,
        ‖(f : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ) c‖ = ‖f_star‖ →
        ∀ z : ball (0 : ℂ) 1,
          (f : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ) z =
            (f : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ) c) := by
  obtain ⟨f_star, ⟨hf_P, hae_nt, hae_rad, hnorm_eq, hess_eq⟩, huniq⟩ :=
    exists_unique_hInfty_boundary f
  let f_bcf : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ := f.1
  let f_ext : ℂ → ℂ := extendZero f_bcf
  have hbound : ∀ z : ball (0 : ℂ) 1,
      ‖f_bcf z‖ ≤ ‖f_star‖ ∧ ‖f_bcf z‖ ≤ rudinEssSup unitCircleMeasure f_star := by
    intro z
    have hle : ‖f_bcf z‖ ≤ ‖f‖ := BoundedContinuousFunction.norm_coe_le_norm f_bcf z
    exact ⟨hle.trans_eq hnorm_eq, hle.trans_eq hess_eq⟩
  have hrig : ∀ c : ball (0 : ℂ) 1, ‖f_bcf c‖ = ‖f_star‖ →
      ∀ z : ball (0 : ℂ) 1, f_bcf z = f_bcf c := by
    intro c hc z
    have hmax : ∀ w ∈ ball (0 : ℂ) 1, ‖f_ext w‖ ≤ ‖f_ext c.1‖ := by
      intro w hw
      dsimp only [f_ext]
      rw [extendZero_apply_of_mem f_bcf hw, extendZero_apply_of_mem f_bcf c.2]
      exact (hbound ⟨w, hw⟩).1.trans_eq hc.symm
    have heq := Complex.eq_const_of_exists_max f.2 c.2 hmax z.2
    rwa [extendZero_apply_of_mem f_bcf z.2, extendZero_apply_of_mem f_bcf c.2] at heq
  refine ⟨f_star, ⟨hf_P, hae_nt, hae_rad, hnorm_eq, hess_eq, hbound, hrig⟩, ?_⟩
  intro g ⟨hg_P, hg_nt, hg_rad, hg_norm, hg_ess, _, _⟩
  exact huniq g ⟨hg_P, hg_nt, hg_rad, hg_norm, hg_ess⟩

/-- 12.1 complete package combining (1) continuous-boundary maximum modulus and rigidity on
bounded regions `Ω` with (2) radial-boundary-value `H^∞(U)` norm equality `‖f‖_∞ = ‖f*‖_∞`,
pointwise bound `|f(z)| ≤ ‖f*‖_∞`, and interior equality rigidity on `U` (Rudin p. 253). -/
theorem theorem12_1 :
    (∀ {f : ℂ → ℂ} {Ω : Set ℂ},
      IsBounded Ω → DifferentiableOn ℂ f Ω → ContinuousOn f (closure Ω) →
      (∀ z ∈ closure Ω, ‖f z‖ ≤ boundaryNorm f Ω) ∧
      (IsOpen Ω → IsPreconnected Ω → ∀ c ∈ Ω, ‖f c‖ = boundaryNorm f Ω →
        ∀ z ∈ closure Ω, f z = f c)) ∧
    (∀ f : HInfty,
      ∃! f_star : Lp ℂ ⊤ unitCircleMeasure,
        (∀ z : ball (0 : ℂ) 1,
          (f : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ) z =
            unitPoissonIntegral f_star z.1) ∧
        (∀ᵐ (ζ : UnitCircle) ∂unitCircleMeasure,
          HasNontangentialLimit
            (extendZero (f : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ))
            ζ (f_star ζ)) ∧
        (∀ᵐ (ζ : UnitCircle) ∂unitCircleMeasure,
          Tendsto (fun r : ℝ =>
            extendZero (f : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ)
              ((r : ℂ) * (ζ : ℂ)))
            (𝓝[<] 1) (𝓝 (f_star ζ))) ∧
        ‖f‖ = ‖f_star‖ ∧
        ‖f‖ = rudinEssSup unitCircleMeasure f_star ∧
        (∀ z : ball (0 : ℂ) 1,
          ‖(f : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ) z‖ ≤ ‖f_star‖ ∧
          ‖(f : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ) z‖ ≤
            rudinEssSup unitCircleMeasure f_star) ∧
        (∀ c : ball (0 : ℂ) 1,
          ‖(f : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ) c‖ = ‖f_star‖ →
          ∀ z : ball (0 : ℂ) 1,
            (f : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ) z =
              (f : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ) c)) :=
  ⟨fun hb hf hc =>
    ⟨fun _ hz => theorem12_1_boundary_bound hb hf hc hz,
     fun ho hconn _ hcΩ heq => theorem12_1_boundary_equality hb ho hconn hf hc hcΩ heq⟩,
   theorem12_1_hInfty_boundary⟩

end Node12_1

/-! ### Node 12.13: A Converse of the Maximum Modulus Theorem -/

section Node12_13

open RudinRCA.Chapter11

private theorem conjCLE_apply' (w : ℂ) : (Complex.conjCLE : ℂ →L[ℝ] ℂ) w = conj w := rfl

/-- Wirtinger `∂̄` of `z ↦ conj (K z)` for holomorphic `K` equals `conj (deriv K z)`. -/
private theorem wirtingerBar_conj_comp {K : ℂ → ℂ} {z : ℂ} (hK : DifferentiableAt ℂ K z) :
    wirtingerBar (fun w => conj (K w)) z = conj (deriv K z) := by
  have hR : HasFDerivAt K (fderiv ℝ K z) z := hK.restrictScalars ℝ |>.hasFDerivAt
  have hCR := (differentiableAt_complex_iff_differentiableAt_real.mp hK).2
  have hderiv : fderiv ℝ K z 1 = deriv K z := by
    have hf := hK.hasDerivAt.hasFDerivAt.restrictScalars ℝ
    rw [hf.fderiv]
    simp
  have hconj : HasFDerivAt (fun w => conj (K w))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ K z)) z :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z hR
  unfold wirtingerBar
  rw [hconj.fderiv]
  simp only [ContinuousLinearMap.comp_apply, conjCLE_apply', hCR, smul_eq_mul,
    hderiv, map_mul, Complex.conj_I]
  linear_combination -(conj (deriv K z) / 2) * Complex.I_sq

/-- Wirtinger `∂̄` of `z ↦ z * conj (K z)` for holomorphic `K` equals `z * conj (deriv K z)`. -/
private theorem wirtingerBar_id_mul_conj_comp {K : ℂ → ℂ} {z : ℂ} (hK : DifferentiableAt ℂ K z) :
    wirtingerBar (fun w => w * conj (K w)) z = z * conj (deriv K z) := by
  have hK_R : DifferentiableAt ℝ (fun w => conj (K w)) z :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z (hK.restrictScalars ℝ)
  have hid_R : DifferentiableAt ℝ (fun w : ℂ => w) z := differentiableAt_id
  have hprod : HasFDerivAt (fun w => w * conj (K w))
      (z • fderiv ℝ (fun w => conj (K w)) z +
        conj (K z) • fderiv ℝ (fun w : ℂ => w) z) z := by
    have := hid_R.hasFDerivAt.mul hK_R.hasFDerivAt
    refine this.congr_fderiv ?_
    ext v
    simp [smul_eq_mul, mul_comm]
  unfold wirtingerBar
  rw [hprod.fderiv]
  have hf_id : fderiv ℝ (fun w : ℂ => w) z = ContinuousLinearMap.id ℝ ℂ := fderiv_id
  have hbar := wirtingerBar_conj_comp hK
  unfold wirtingerBar at hbar
  simp only [add_apply, smul_apply, hf_id, ContinuousLinearMap.id_apply, smul_eq_mul]
  calc (z * fderiv ℝ (fun w => conj (K w)) z 1 + conj (K z) * 1 +
          Complex.I * (z * fderiv ℝ (fun w => conj (K w)) z Complex.I +
            conj (K z) * Complex.I)) / 2
      = z * ((fderiv ℝ (fun w => conj (K w)) z 1 +
          Complex.I * fderiv ℝ (fun w => conj (K w)) z Complex.I) / 2) +
        conj (K z) * ((1 + Complex.I * Complex.I) / 2) := by ring
    _ = z * conj (deriv K z) := by rw [hbar, Complex.I_mul_I]; ring

/-- Wirtinger `∂̄` of `z ↦ conj z * L z` for holomorphic `L` equals `L z`. -/
private theorem wirtingerBar_conj_id_mul {L : ℂ → ℂ} {z : ℂ} (hL : DifferentiableAt ℂ L z) :
    wirtingerBar (fun w => conj w * L w) z = L z := by
  have hL_R : DifferentiableAt ℝ L z := hL.restrictScalars ℝ
  have hCR := (differentiableAt_complex_iff_differentiableAt_real.mp hL).2
  have hc_has : HasFDerivAt (fun w : ℂ => conj w) (Complex.conjCLE : ℂ →L[ℝ] ℂ) z :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt
  have hprod : HasFDerivAt (fun w => conj w * L w)
      (conj z • fderiv ℝ L z + (Complex.conjCLE : ℂ →L[ℝ] ℂ).smulRight (L z)) z := by
    refine (hc_has.mul hL_R.hasFDerivAt).congr_fderiv ?_
    ext v
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, conjCLE_apply',
      smul_eq_mul]
    ring
  unfold wirtingerBar
  rw [hprod.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, conjCLE_apply',
    hCR, smul_eq_mul, map_one, Complex.conj_I]
  linear_combination ((conj z * fderiv ℝ L z 1 - L z) / 2) * Complex.I_sq

/-- Any complex Poisson integral `poissonIntegral φ` of a circle-integrable function `φ`
decomposes on `ball 0 1` as `G(z) + conj(H(z))` with `G, H` holomorphic on `ball 0 1`. -/
private theorem poissonIntegral_eq_holo_add_conj_holo {φ : ℂ → ℂ} (hφ : CircleIntegrable φ 0 1) :
    ∃ G H : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 1) ∧ DifferentiableOn ℂ H (ball 0 1) ∧
      ∀ z ∈ ball (0 : ℂ) 1, poissonIntegral φ z = G z + conj (H z) := by
  have hre_int : CircleIntegrable (fun ζ => (φ ζ).re) 0 1 := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hφ ⊢
    exact Complex.reCLM.integrable_comp hφ
  have him_int : CircleIntegrable (fun ζ => (φ ζ).im) 0 1 := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hφ ⊢
    exact Complex.imCLM.integrable_comp hφ
  obtain ⟨_, _, F₁, hF₁, hF₁_re⟩ := theorem11_7_real hre_int
  obtain ⟨_, _, F₂, hF₂, hF₂_re⟩ := theorem11_7_real him_int
  let G : ℂ → ℂ := fun z => (F₁ z + Complex.I * F₂ z) / 2
  let H : ℂ → ℂ := fun z => (F₁ z - Complex.I * F₂ z) / 2
  have hG : DifferentiableOn ℂ G (ball 0 1) :=
    (hF₁.add (hF₂.const_mul Complex.I)).div_const 2
  have hH : DifferentiableOn ℂ H (ball 0 1) :=
    (hF₁.sub (hF₂.const_mul Complex.I)).div_const 2
  refine ⟨G, H, hG, hH, fun z hz => ?_⟩
  have hz_not : z ∉ sphere (0 : ℂ) |(1 : ℝ)| := by
    rw [abs_of_pos zero_lt_one, mem_sphere]
    exact (mem_ball.mp hz).ne
  have hcont_k : ContinuousOn (_root_.poissonKernel 0 z) (sphere 0 |(1 : ℝ)|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hz_not)
  have hci_re : CircleIntegrable (fun ζ => _root_.poissonKernel 0 z ζ • (φ ζ).re) 0 1 :=
    hre_int.continuousOn_smul hcont_k
  have hci_im : CircleIntegrable (fun ζ => _root_.poissonKernel 0 z ζ • (φ ζ).im) 0 1 :=
    him_int.continuousOn_smul hcont_k
  have hsplit : poissonIntegral φ z =
      (poissonIntegral (E := ℝ) (fun ζ => (φ ζ).re) z : ℂ) +
        Complex.I * (poissonIntegral (E := ℝ) (fun ζ => (φ ζ).im) z : ℂ) := by
    unfold poissonIntegral Real.circleAverage
    unfold CircleIntegrable at hci_re hci_im
    rw [intervalIntegrable_iff] at hci_re hci_im
    have hci_re_c : IntervalIntegrable
        (fun θ => ((_root_.poissonKernel 0 z (circleMap 0 1 θ) • (φ (circleMap 0 1 θ)).re : ℝ) : ℂ))
        volume 0 (2 * Real.pi) := by
      rw [intervalIntegrable_iff]
      exact Complex.ofRealCLM.integrable_comp hci_re
    have hci_im_c : IntervalIntegrable
        (fun θ => Complex.I *
          ((_root_.poissonKernel 0 z (circleMap 0 1 θ) • (φ (circleMap 0 1 θ)).im : ℝ) : ℂ))
        volume 0 (2 * Real.pi) := by
      rw [intervalIntegrable_iff]
      exact (Complex.ofRealCLM.integrable_comp hci_im).const_mul Complex.I
    have hint_eq : (∫ θ in (0 : ℝ)..2 * Real.pi,
          _root_.poissonKernel 0 z (circleMap 0 1 θ) • φ (circleMap 0 1 θ)) =
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          ((_root_.poissonKernel 0 z (circleMap 0 1 θ) • (φ (circleMap 0 1 θ)).re : ℝ) : ℂ)) +
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          Complex.I * ((_root_.poissonKernel 0 z (circleMap 0 1 θ) • (φ (circleMap 0 1 θ)).im : ℝ) : ℂ)) := by
      rw [← intervalIntegral.integral_add hci_re_c hci_im_c]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      apply Complex.ext <;> simp [Complex.real_smul]
    rw [Complex.real_smul, hint_eq, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat]
    ring
  rw [hsplit, ← hF₁_re z hz, ← hF₂_re z hz]
  dsimp only [G, H]
  apply Complex.ext <;> simp [map_ofNat] <;> ring

open Classical in
/-- 12.13 (`C(UnitDisc, ℂ)` submodule formulation, Rudin pp. 262–263): if `M` is a subspace
of `C(Ū, ℂ)` containing `1`, closed under multiplication by the coordinate function `j(z) = z`,
and satisfying `‖f‖_T = ‖f‖_{Ū}` for every `f ∈ M`, then every `f ∈ M` is holomorphic in `U`. -/
theorem theorem12_13_unitDisc (M : Submodule ℂ C(RudinRCA.Chapter05.UnitDisc, ℂ))
    (hone : (1 : C(RudinRCA.Chapter05.UnitDisc, ℂ)) ∈ M)
    (hmul_j : ∀ f ∈ M,
      (⟨fun z : RudinRCA.Chapter05.UnitDisc => (z : ℂ) * f z,
        continuous_subtype_val.mul f.continuous⟩ : C(RudinRCA.Chapter05.UnitDisc, ℂ)) ∈ M)
    (hboundary : ∀ f : M,
      ‖(f : C(RudinRCA.Chapter05.UnitDisc, ℂ)).comp RudinRCA.Chapter05.discBoundary‖ =
        ‖(f : C(RudinRCA.Chapter05.UnitDisc, ℂ))‖) :
    ∀ f ∈ M, DifferentiableOn ℂ
      (fun z : ℂ => if hz : z ∈ closedBall (0 : ℂ) 1 then f ⟨z, hz⟩ else 0)
      (ball (0 : ℂ) 1) := by
  classical
  -- Step 1: By (a) and (b), `M` contains all polynomials `discPolynomial p`.
  have hmonom : ∀ n : ℕ, RudinRCA.Chapter05.discPolynomial (Polynomial.X ^ n) ∈ M := by
    intro n
    induction n with
    | zero =>
      have heq : RudinRCA.Chapter05.discPolynomial (Polynomial.X ^ 0) =
          (1 : C(RudinRCA.Chapter05.UnitDisc, ℂ)) := by
        ext z; simp
      rw [heq]; exact hone
    | succ n ih =>
      have heq : RudinRCA.Chapter05.discPolynomial (Polynomial.X ^ (n + 1)) =
          ⟨fun z : RudinRCA.Chapter05.UnitDisc =>
              (z : ℂ) * RudinRCA.Chapter05.discPolynomial (Polynomial.X ^ n) z,
            continuous_subtype_val.mul (RudinRCA.Chapter05.discPolynomial _).continuous⟩ := by
        ext z; simp [pow_succ']
      rw [heq]
      exact hmul_j _ ih
  have hpoly : ∀ p : Polynomial ℂ, RudinRCA.Chapter05.discPolynomial p ∈ M := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      have heq : RudinRCA.Chapter05.discPolynomial (p + q) =
          RudinRCA.Chapter05.discPolynomial p + RudinRCA.Chapter05.discPolynomial q := by
        ext z; simp
      rw [heq]; exact M.add_mem hp hq
    | monomial n a =>
      have heq : RudinRCA.Chapter05.discPolynomial (Polynomial.monomial n a) =
          a • RudinRCA.Chapter05.discPolynomial (Polynomial.X ^ n) := by
        ext z; simp [Polynomial.eval_monomial]
      rw [heq]; exact M.smul_mem a (hmonom n)
  -- Step 2: By Theorem 5.25 (`poisson_representation`), every `g ∈ M` equals its Poisson integral
  -- on `ball 0 1`, hence decomposes as `G + conj ∘ H` with `G, H` holomorphic on `ball 0 1`.
  have hdecomp : ∀ g ∈ M, ∃ G H : ℂ → ℂ,
      DifferentiableOn ℂ G (ball 0 1) ∧ DifferentiableOn ℂ H (ball 0 1) ∧
      ∀ z : ℂ, (hz : z ∈ ball (0 : ℂ) 1) →
        g ⟨z, ball_subset_closedBall hz⟩ = G z + conj (H z) := by
    intro g hg
    let φ : ℂ → ℂ := fun w => if hw : w ∈ closedBall (0 : ℂ) 1 then g ⟨w, hw⟩ else 0
    have hφ_cb : ContinuousOn φ (closedBall (0 : ℂ) 1) := by
      rw [continuousOn_iff_continuous_domRestrict]
      refine g.continuous.congr fun x => ?_
      have hx : (x : ℂ) ∈ closedBall (0 : ℂ) 1 := x.2
      change g x = φ x.1
      dsimp only [φ]
      exact (dite_eq_left_iff.mpr fun hnot => absurd hx hnot).symm
    have hφ_cont : ContinuousOn φ (sphere (0 : ℂ) |(1 : ℝ)|) := by
      rw [abs_of_pos zero_lt_one]
      exact hφ_cb.mono sphere_subset_closedBall
    have hφ_ci : CircleIntegrable φ 0 1 := hφ_cont.circleIntegrable'
    obtain ⟨G, H, hG, hH, hGH⟩ := poissonIntegral_eq_holo_add_conj_holo hφ_ci
    refine ⟨G, H, hG, hH, fun z hz => ?_⟩
    have hz_norm : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
    have h525 := RudinRCA.Chapter05.poisson_representation M hpoly hboundary
      ⟨z, ball_subset_closedBall hz⟩ hz_norm ⟨g, hg⟩
    have hP_eq : (∫ t, RudinRCA.Chapter05.poissonDensity z hz_norm t •
          g (RudinRCA.Chapter05.discBoundary t) ∂RudinRCA.Chapter04.circleMeasure) =
        poissonIntegral φ z := by
      have hfun : (fun t : RudinRCA.Chapter04.FourierCircle =>
            RudinRCA.Chapter05.poissonDensity z hz_norm t •
              g (RudinRCA.Chapter05.discBoundary t)) =
          (fun t : RudinRCA.Chapter04.FourierCircle =>
            (_root_.poissonKernel 0 z • φ) (RudinRCA.Chapter05.circleCoordinate t)) := by
        ext t
        rw [RudinRCA.Chapter05.poissonDensity_eq_kernel]
        have hmem : RudinRCA.Chapter05.circleCoordinate t ∈ closedBall (0 : ℂ) 1 := by
          rw [mem_closedBall_zero_iff, RudinRCA.Chapter05.circleCoordinate_norm]
        change _ = _root_.poissonKernel 0 z (RudinRCA.Chapter05.circleCoordinate t) •
          φ (RudinRCA.Chapter05.circleCoordinate t)
        have hφ_t : φ (RudinRCA.Chapter05.circleCoordinate t) =
            g (RudinRCA.Chapter05.discBoundary t) := by
          dsimp only [φ]
          split_ifs
          congr 1
        rw [hφ_t]
      rw [hfun, RudinRCA.Chapter05.circleIntegral_eq_circleAverage]
      rfl
    rw [h525, hP_eq, hGH z hz]
  -- Step 3: Apply `hdecomp` to `f` and `j * f` and differentiate via Wirtinger `∂̄`!
  intro f hf
  let jf : C(RudinRCA.Chapter05.UnitDisc, ℂ) :=
    ⟨fun z : RudinRCA.Chapter05.UnitDisc => (z : ℂ) * f z,
      continuous_subtype_val.mul f.continuous⟩
  obtain ⟨G, H, hG, hH, hf_eq⟩ := hdecomp f hf
  obtain ⟨G₁, H₁, hG₁, hH₁, hjf_eq⟩ := hdecomp jf (hmul_j f hf)
  -- On `ball 0 1`, `z * conj(H z) - conj(H₁ z) = G₁ z - z * G z` is holomorphic
  have hk_holo : DifferentiableOn ℂ (fun z : ℂ => z * conj (H z) - conj (H₁ z)) (ball 0 1) := by
    refine (hG₁.sub (differentiableOn_id.mul hG)).congr fun z hz => ?_
    have e1 := hf_eq z hz
    have e2 := hjf_eq z hz
    change z * f ⟨z, ball_subset_closedBall hz⟩ = G₁ z + conj (H₁ z) at e2
    rw [e1] at e2
    change z * conj (H z) - conj (H₁ z) = G₁ z - z * G z
    linear_combination e2
  have hrel : ∀ z ∈ ball (0 : ℂ) 1, conj z * deriv H z = deriv H₁ z := by
    intro z hz
    have hk_at : DifferentiableAt ℂ (fun w : ℂ => w * conj (H w) - conj (H₁ w)) z :=
      hk_holo.differentiableAt (isOpen_ball.mem_nhds hz)
    have hH_at : DifferentiableAt ℂ H z := hH.differentiableAt (isOpen_ball.mem_nhds hz)
    have hH₁_at : DifferentiableAt ℂ H₁ z := hH₁.differentiableAt (isOpen_ball.mem_nhds hz)
    have hbar0 : wirtingerBar (fun w : ℂ => w * conj (H w) - conj (H₁ w)) z = 0 :=
      (node11_1_complex_differentiable_iff (hk_at.restrictScalars ℝ)).mp hk_at
    -- Linearity of `wirtingerBar` on real-differentiable functions
    have hd1 : DifferentiableAt ℝ (fun w : ℂ => w * conj (H w)) z :=
      differentiableAt_id.mul ((Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z
        (hH_at.restrictScalars ℝ))
    have hd2 : DifferentiableAt ℝ (fun w : ℂ => conj (H₁ w)) z :=
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z (hH₁_at.restrictScalars ℝ)
    have hsub_bar : wirtingerBar (fun w : ℂ => w * conj (H w) - conj (H₁ w)) z =
        wirtingerBar (fun w : ℂ => w * conj (H w)) z -
          wirtingerBar (fun w : ℂ => conj (H₁ w)) z := by
      unfold wirtingerBar
      have hfd : fderiv ℝ (fun w : ℂ => w * conj (H w) - conj (H₁ w)) z =
          fderiv ℝ (fun w : ℂ => w * conj (H w)) z - fderiv ℝ (fun w : ℂ => conj (H₁ w)) z :=
        (hd1.hasFDerivAt.sub hd2.hasFDerivAt).fderiv
      rw [hfd]
      simp only [sub_apply]
      ring
    rw [hsub_bar, wirtingerBar_id_mul_conj_comp hH_at, wirtingerBar_conj_comp hH₁_at,
      sub_eq_zero] at hbar0
    have hc := congrArg conj hbar0
    simpa only [map_mul, conj_conj] using hc
  -- Now `deriv H` and `deriv H₁` are holomorphic on `ball 0 1`, so `z ↦ conj z * deriv H z`
  -- is holomorphic on `ball 0 1`, forcing `deriv H z = 0`!
  have hdH_holo : DifferentiableOn ℂ (deriv H) (ball 0 1) :=
    hH.deriv isOpen_ball
  have hdH₁_holo : DifferentiableOn ℂ (deriv H₁) (ball 0 1) :=
    hH₁.deriv isOpen_ball
  have hconj_mul_holo : DifferentiableOn ℂ (fun z : ℂ => conj z * deriv H z) (ball 0 1) :=
    hdH₁_holo.congr fun z hz => hrel z hz
  have hdH_zero : ∀ z ∈ ball (0 : ℂ) 1, deriv H z = 0 := by
    intro z hz
    have hat : DifferentiableAt ℂ (fun w : ℂ => conj w * deriv H w) z :=
      hconj_mul_holo.differentiableAt (isOpen_ball.mem_nhds hz)
    have hdH_at : DifferentiableAt ℂ (deriv H) z :=
      hdH_holo.differentiableAt (isOpen_ball.mem_nhds hz)
    have hbar0 : wirtingerBar (fun w : ℂ => conj w * deriv H w) z = 0 :=
      (node11_1_complex_differentiable_iff (hat.restrictScalars ℝ)).mp hat
    rwa [wirtingerBar_conj_id_mul hdH_at] at hbar0
  -- Deduce `H` is constant on the convex open set `ball 0 1`
  have hH_const : ∀ z ∈ ball (0 : ℂ) 1, H z = H 0 := by
    intro z hz
    refine Convex.is_const_of_fderivWithin_eq_zero (𝕜 := ℂ) (convex_ball 0 1) hH ?_ hz
      (mem_ball_self zero_lt_one)
    intro w hw
    rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hw)
      (hH.differentiableAt (isOpen_ball.mem_nhds hw))]
    ext
    have h := (hH.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt.hasFDerivAt.fderiv
    rw [h]
    simp [hdH_zero w hw]
  refine (hG.add_const (conj (H 0))).congr fun z hz => ?_
  simp only [ball_subset_closedBall hz, ↓reduceDIte]
  rw [hf_eq z hz, hH_const z hz]

/-- Supremum norm on `U = ball 0 1`, `‖f‖_U = sup_{z ∈ U} ‖f z‖`, used in 12.13(c). -/
def openDiscNorm (f : ℂ → ℂ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' ball (0 : ℂ) 1)

/-- For `f` continuous on `closedBall 0 1`, `openDiscNorm f` equals `sSup` on `closedBall 0 1`. -/
theorem openDiscNorm_eq_closedBall_sSup {f : ℂ → ℂ}
    (hf : ContinuousOn f (closedBall (0 : ℂ) 1)) :
    openDiscNorm f = sSup ((fun z => ‖f z‖) '' closedBall (0 : ℂ) 1) := by
  have hcomp : IsCompact (closedBall (0 : ℂ) 1) := isCompact_closedBall 0 1
  have hbdd_cb : BddAbove ((fun z => ‖f z‖) '' closedBall (0 : ℂ) 1) :=
    (hcomp.image_of_continuousOn hf.norm).bddAbove
  have hbdd_b : BddAbove ((fun z => ‖f z‖) '' ball (0 : ℂ) 1) :=
    hbdd_cb.mono (image_mono ball_subset_closedBall)
  apply le_antisymm
  · refine csSup_le ⟨‖f 0‖, 0, mem_ball_self zero_lt_one, rfl⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    exact le_csSup hbdd_cb ⟨z, ball_subset_closedBall hz, rfl⟩
  · refine csSup_le ⟨‖f 0‖, 0, mem_closedBall_self zero_le_one, rfl⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    have hz_cl : z ∈ closure (ball (0 : ℂ) 1) := by rwa [closure_ball 0 one_ne_zero]
    have hclosed : IsClosed {w ∈ closedBall (0 : ℂ) 1 | ‖f w‖ ≤ openDiscNorm f} :=
      ContinuousOn.preimage_isClosed_of_isClosed hf.norm isClosed_closedBall isClosed_Iic
    refine (closure_minimal ?_ hclosed hz_cl).2
    intro w hw
    exact ⟨ball_subset_closedBall hw, le_csSup hbdd_b ⟨w, hw, rfl⟩⟩

/-- 12.13 (Theorem, Rudin pp. 262–263): Suppose `M` is a `ℂ`-vector space (`Submodule ℂ (ℂ → ℂ)`)
of functions continuous on the closed unit disc `Ū = closedBall 0 1` such that:
(a) `1 ∈ M`,
(b) `f ∈ M → (fun z => z * f z) ∈ M`,
(c) `∀ f ∈ M, openDiscNorm f = boundaryNorm f (ball 0 1)` (`‖f‖_U = ‖f‖_T`).
Then every `f ∈ M` is holomorphic in `U = ball 0 1`. -/
theorem theorem12_13 (M : Submodule ℂ (ℂ → ℂ))
    (hcont : ∀ f ∈ M, ContinuousOn f (closedBall (0 : ℂ) 1))
    (hone : (fun _ : ℂ => (1 : ℂ)) ∈ M)
    (hmul_j : ∀ f ∈ M, (fun z : ℂ => z * f z) ∈ M)
    (hnorm : ∀ f ∈ M, openDiscNorm f = boundaryNorm f (ball 0 1)) :
    ∀ f ∈ M, DifferentiableOn ℂ f (ball (0 : ℂ) 1) := by
  -- Transport `M` into `Submodule ℂ C(UnitDisc, ℂ)` via restriction to `UnitDisc`
  let res : {f : ℂ → ℂ // f ∈ M} → C(RudinRCA.Chapter05.UnitDisc, ℂ) := fun f =>
    ⟨fun z => f.1 z.1, (hcont f.1 f.2).comp_continuous continuous_subtype_val fun z => z.2⟩
  let M_disc : Submodule ℂ C(RudinRCA.Chapter05.UnitDisc, ℂ) :=
    { carrier := range res
      add_mem' := by
        rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
        refine ⟨⟨f.1 + g.1, M.add_mem f.2 g.2⟩, ?_⟩
        ext z; rfl
      zero_mem' := ⟨⟨0, M.zero_mem⟩, by ext z; rfl⟩
      smul_mem' := by
        rintro c _ ⟨f, rfl⟩
        refine ⟨⟨c • f.1, M.smul_mem c f.2⟩, ?_⟩
        ext z; rfl }
  have hone_d : (1 : C(RudinRCA.Chapter05.UnitDisc, ℂ)) ∈ M_disc :=
    ⟨⟨fun _ => 1, hone⟩, by ext z; rfl⟩
  have hmul_d : ∀ g ∈ M_disc,
      (⟨fun z : RudinRCA.Chapter05.UnitDisc => (z : ℂ) * g z,
        continuous_subtype_val.mul g.continuous⟩ : C(RudinRCA.Chapter05.UnitDisc, ℂ)) ∈ M_disc := by
    rintro _ ⟨f, rfl⟩
    refine ⟨⟨fun z => z * f.1 z, hmul_j f.1 f.2⟩, ?_⟩
    ext z; rfl
  have hbd_d : ∀ g : M_disc,
      ‖(g : C(RudinRCA.Chapter05.UnitDisc, ℂ)).comp RudinRCA.Chapter05.discBoundary‖ =
        ‖(g : C(RudinRCA.Chapter05.UnitDisc, ℂ))‖ := by
    rintro ⟨_, ⟨f, rfl⟩⟩
    have hf_cont := hcont f.1 f.2
    -- Identify `‖res f‖` with `sSup` on `closedBall 0 1` (`= openDiscNorm f.1`)
    have hnorm_cb : ‖res f‖ = openDiscNorm f.1 := by
      rw [openDiscNorm_eq_closedBall_sSup hf_cont, ContinuousMap.norm_eq_iSup_norm]
      have hcomp : IsCompact (closedBall (0 : ℂ) 1) := isCompact_closedBall 0 1
      have hbdd : BddAbove ((fun z => ‖f.1 z‖) '' closedBall (0 : ℂ) 1) :=
        (hcomp.image_of_continuousOn hf_cont.norm).bddAbove
      apply le_antisymm
      · refine ciSup_le fun z => le_csSup hbdd ⟨z.1, z.2, rfl⟩
      · refine csSup_le ⟨‖f.1 0‖, 0, mem_closedBall_self zero_le_one, rfl⟩ ?_
        rintro _ ⟨z, hz, rfl⟩
        exact le_ciSup (f := fun w : RudinRCA.Chapter05.UnitDisc => ‖(res f) w‖)
          ⟨‖res f‖, by rintro _ ⟨w, rfl⟩; exact (res f).norm_coe_le_norm w⟩ ⟨z, hz⟩
    -- Identify `‖(res f).comp discBoundary‖` with `boundaryNorm f.1 (ball 0 1)`
    have hnorm_bd : ‖(res f).comp RudinRCA.Chapter05.discBoundary‖ =
        boundaryNorm f.1 (ball 0 1) := by
      unfold boundaryNorm
      rw [frontier_ball (0 : ℂ) one_ne_zero, ContinuousMap.norm_eq_iSup_norm]
      have hbdd : BddAbove ((fun z => ‖f.1 z‖) '' sphere (0 : ℂ) 1) :=
        ((isCompact_sphere (0 : ℂ) 1).image_of_continuousOn
          (hf_cont.mono sphere_subset_closedBall).norm).bddAbove
      apply le_antisymm
      · refine ciSup_le fun t => le_csSup hbdd ⟨RudinRCA.Chapter05.circleCoordinate t, ?_, rfl⟩
        rw [mem_sphere_zero_iff_norm, RudinRCA.Chapter05.circleCoordinate_norm]
      · refine csSup_le ⟨‖f.1 1‖, 1, by simp, rfl⟩ ?_
        rintro _ ⟨w, hw, rfl⟩
        let t := RudinRCA.Chapter04.fourierCircleHomeomorphism.symm ⟨w, hw⟩
        have ht : RudinRCA.Chapter05.circleCoordinate t = w := by
          rw [RudinRCA.Chapter05.circleCoordinate_homeomorphism]
          exact congrArg Subtype.val
            (RudinRCA.Chapter04.fourierCircleHomeomorphism.apply_symm_apply ⟨w, hw⟩)
        have hle := le_ciSup
          (f := fun s : RudinRCA.Chapter04.FourierCircle =>
            ‖((res f).comp RudinRCA.Chapter05.discBoundary) s‖)
          ⟨‖(res f).comp RudinRCA.Chapter05.discBoundary‖,
            by
              rintro _ ⟨s, rfl⟩
              exact ((res f).comp RudinRCA.Chapter05.discBoundary).norm_coe_le_norm s⟩ t
        have hval : ((res f).comp RudinRCA.Chapter05.discBoundary) t = f.1 w := by
          change f.1 (RudinRCA.Chapter05.discBoundary t).1 = f.1 w
          rw [RudinRCA.Chapter05.discBoundary_coe, ht]
        rwa [hval] at hle
    change ‖(res f).comp RudinRCA.Chapter05.discBoundary‖ = ‖res f‖
    rw [hnorm_bd, hnorm_cb, hnorm f.1 f.2]
  intro f hf
  classical
  have hd := theorem12_13_unitDisc M_disc hone_d hmul_d hbd_d (res ⟨f, hf⟩) ⟨⟨f, hf⟩, rfl⟩
  refine hd.congr fun z hz => ?_
  simp only [ball_subset_closedBall hz, ↓reduceDIte]
  rfl

end Node12_13

/-! ### Node 12.14: Radó's Theorem -/

section Node12_14

/-- 12.14 (Radó's Theorem, Rudin p. 263): Assume `f` is continuous on the closed unit disc
`Ū = closedBall 0 1`, `Ω = {z ∈ ball 0 1 | f z ≠ 0}`, and `f` is holomorphic in `Ω`.
Then `f` is holomorphic in `U = ball 0 1` (and in particular `U \ Ω` is countable unless `Ω = ∅`). -/
theorem theorem12_14 {f : ℂ → ℂ}
    (hcont : ContinuousOn f (closedBall (0 : ℂ) 1))
    (hholo : DifferentiableOn ℂ f {z ∈ ball (0 : ℂ) 1 | f z ≠ 0}) :
    DifferentiableOn ℂ f (ball (0 : ℂ) 1) ∧
    ({z ∈ ball (0 : ℂ) 1 | f z ≠ 0} = ∅ ∨
      (ball (0 : ℂ) 1 \ {z ∈ ball (0 : ℂ) 1 | f z ≠ 0}).Countable) := by
  let Ω : Set ℂ := {z ∈ ball (0 : ℂ) 1 | f z ≠ 0}
  have hholo_U : DifferentiableOn ℂ f (ball (0 : ℂ) 1) := by
    by_cases hΩ_empty : Ω = ∅
    · refine (differentiableOn_const (0 : ℂ)).congr fun z hz => ?_
      by_contra hne
      have : z ∈ Ω := ⟨hz, hne⟩
      rw [hΩ_empty] at this
      exact this
    · obtain ⟨α₀, hα₀⟩ := nonempty_iff_ne_empty.mpr hΩ_empty
      have hΩ_open : IsOpen Ω := by
        have hf_ball : ContinuousOn f (ball (0 : ℂ) 1) := hcont.mono ball_subset_closedBall
        exact hf_ball.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
      have hΩ_bdd : IsBounded Ω := isBounded_ball.subset fun _ hz => hz.1
      have hΩ_cl_sub : closure Ω ⊆ closedBall (0 : ℂ) 1 :=
        closure_minimal (fun _ hz => ball_subset_closedBall hz.1) isClosed_closedBall
      let M_T : ℝ := max (boundaryNorm f (ball 0 1)) 0
      have hf_T : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ M_T := by
        intro z hz
        have hbdd : BddAbove ((fun w => ‖f w‖) '' frontier (ball (0 : ℂ) 1)) := by
          rw [frontier_ball (0 : ℂ) one_ne_zero]
          exact ((isCompact_sphere (0 : ℂ) 1).image_of_continuousOn
            (hcont.mono sphere_subset_closedBall).norm).bddAbove
        have hz_fr : z ∈ frontier (ball (0 : ℂ) 1) := by
          rwa [frontier_ball (0 : ℂ) one_ne_zero]
        exact (le_csSup hbdd ⟨z, hz_fr, rfl⟩).trans (le_max_left _ _)
      -- Step 1: Prove `Ω` is dense in `ball 0 1` (`ball 0 1 ⊆ closure Ω`)
      have hdense : ball (0 : ℂ) 1 ⊆ closure Ω := by
        intro z₀ hz₀
        by_contra hz₀_not
        -- Walk along segment `γ t = (1 - t) • z₀ + t • α₀` (`t ∈ [0, 1]`)
        let γ : ℝ → ℂ := fun t => (1 - t) • z₀ + t • α₀
        let R : ℝ := max ‖z₀‖ ‖α₀‖
        have hR_lt : R < 1 := max_lt (mem_ball_zero_iff.mp hz₀) (mem_ball_zero_iff.mp hα₀.1)
        have hγ_norm : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t‖ ≤ R := by
          intro t ht
          calc ‖(1 - t) • z₀ + t • α₀‖
              ≤ ‖(1 - t) • z₀‖ + ‖t • α₀‖ := norm_add_le _ _
            _ = |1 - t| * ‖z₀‖ + |t| * ‖α₀‖ := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
            _ ≤ (1 - t) * R + t * R := by
                rw [abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
                exact add_le_add
                  (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr ht.2))
                  (mul_le_mul_of_nonneg_left (le_max_right _ _) ht.1)
            _ = R := by ring
        let S_t : Set ℝ := {t ∈ Icc (0 : ℝ) 1 | γ t ∈ closure Ω}
        have hγ_cont : Continuous γ :=
          ((continuous_const.sub continuous_id).smul continuous_const).add
            (continuous_id.smul continuous_const)
        have hS_closed : IsClosed S_t :=
          isClosed_Icc.inter (isClosed_closure.preimage hγ_cont)
        have h1_mem : (1 : ℝ) ∈ S_t := ⟨⟨zero_le_one, le_rfl⟩, by simpa [γ] using subset_closure hα₀⟩
        let t_star : ℝ := sInf S_t
        have ht_mem : t_star ∈ S_t := hS_closed.csInf_mem ⟨1, h1_mem⟩ ⟨0, fun _ ht => ht.1.1⟩
        have ht_pos : 0 < t_star := by
          refine lt_of_le_of_ne ht_mem.1.1 ?_
          intro heq
          apply hz₀_not
          have := ht_mem.2
          simpa [← heq, γ] using this
        -- Pick `t₁ < t_star` close to `t_star`
        let δ : ℝ := (1 - R) / 4
        have hδ : 0 < δ := by dsimp [δ]; linarith
        obtain ⟨η, hη_pos, hη_dist⟩ :=
          Metric.continuousAt_iff.mp hγ_cont.continuousAt δ hδ
        let t₁ : ℝ := max 0 (t_star - η / 2)
        have ht₁_lt : t₁ < t_star := max_lt ht_pos (by linarith)
        have ht₁_Icc : t₁ ∈ Icc (0 : ℝ) 1 :=
          ⟨le_max_left _ _, ht₁_lt.le.trans ht_mem.1.2⟩
        have ht₁_not : γ t₁ ∉ closure Ω := by
          intro hmem
          have : t_star ≤ t₁ := csInf_le ⟨0, fun _ ht => ht.1.1⟩ ⟨ht₁_Icc, hmem⟩
          linarith
        have ht₁_dist : dist t₁ t_star < η := by
          rw [Real.dist_eq, abs_of_neg (sub_neg.mpr ht₁_lt)]
          have : t_star - η / 2 ≤ t₁ := le_max_right _ _
          linarith
        let β : ℂ := γ t₁
        have hβ_not : β ∉ closure Ω := ht₁_not
        have hβ_norm : ‖β‖ ≤ R := hγ_norm t₁ ht₁_Icc
        have hβ_ball : β ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (hβ_norm.trans_lt hR_lt)
        have hβ_dist : ‖β - γ t_star‖ < δ := by
          simpa [dist_eq_norm] using hη_dist ht₁_dist
        obtain ⟨α, hα_Ω, hα_dist⟩ :=
          Metric.mem_closure_iff.mp ht_mem.2 δ hδ
        have h2dist : 2 * ‖β - α‖ < 1 - ‖β‖ := by
          have htri : ‖β - α‖ < 2 * δ := by
            calc ‖β - α‖ = ‖(β - γ t_star) + (γ t_star - α)‖ := by ring_nf
              _ ≤ ‖β - γ t_star‖ + ‖γ t_star - α‖ := norm_add_le _ _
              _ < δ + δ := add_lt_add hβ_dist (by simpa [dist_eq_norm] using hα_dist)
              _ = 2 * δ := by ring
          dsimp only [δ] at htri
          linarith
        have hαβ_pos : 0 < ‖α - β‖ := norm_pos_iff.mpr fun heq => by
          have h := sub_eq_zero.mp heq
          rw [← h] at hβ_not
          exact hβ_not (subset_closure hα_Ω)
        have hfα_pos : 0 < ‖f α‖ := norm_pos_iff.mpr hα_Ω.2
        obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M_T / ‖f α‖) (by norm_num : (1 : ℝ) < 2)
        have hn_gt : M_T < 2 ^ n * ‖f α‖ := (div_lt_iff₀ hfα_pos).mp hn
        let h : ℂ → ℂ := fun z => (z - β)⁻¹ ^ n * f z
        have hne_β : ∀ z ∈ closure Ω, z - β ≠ 0 := fun z hz h0 => by
          have he := sub_eq_zero.mp h0
          rw [← he] at hβ_not
          exact hβ_not hz
        have hh_holo : DifferentiableOn ℂ h Ω :=
          ((((differentiableOn_id.sub_const β).inv
            (fun z hz => hne_β z (subset_closure hz))).pow n).mul hholo)
        have hh_cont : ContinuousOn h (closure Ω) :=
          (((continuousOn_id.sub continuousOn_const).inv₀ hne_β).pow n).mul
            (hcont.mono hΩ_cl_sub)
        let C_bd : ℝ := (1 - ‖β‖)⁻¹ ^ n * M_T
        have h1β_pos : 0 < 1 - ‖β‖ := sub_pos.mpr (mem_ball_zero_iff.mp hβ_ball)
        have hh_fr : ∀ z ∈ frontier Ω, ‖h z‖ ≤ C_bd := by
          intro z hz
          have hz_cb : z ∈ closedBall (0 : ℂ) 1 := hΩ_cl_sub hz.1
          rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hz_cb) with hz_lt | hz_eq
          · have hz_not_Ω : z ∉ Ω := by
              rw [frontier, hΩ_open.interior_eq] at hz
              exact hz.2
            have hfz0 : f z = 0 := by
              by_contra hne
              exact hz_not_Ω ⟨mem_ball_zero_iff.mpr hz_lt, hne⟩
            dsimp only [h, C_bd]
            rw [hfz0, mul_zero, norm_zero]
            exact mul_nonneg (pow_nonneg (inv_nonneg.mpr h1β_pos.le) n) (le_max_right _ _)
          · have hz_sph : z ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr hz_eq
            have hzb_ge : 1 - ‖β‖ ≤ ‖z - β‖ := by
              have := norm_sub_norm_le z β
              rwa [hz_eq] at this
            dsimp only [h, C_bd]
            rw [norm_mul, norm_pow, norm_inv]
            refine mul_le_mul ?_ (hf_T z hz_sph) (norm_nonneg _)
              (pow_nonneg (inv_nonneg.mpr h1β_pos.le) n)
            exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _))
              (inv_anti₀ h1β_pos hzb_ge) n
        have hh_α_le : ‖h α‖ ≤ C_bd :=
          Complex.norm_le_of_forall_mem_frontier_norm_le hΩ_bdd ⟨hh_holo, hh_cont⟩ hh_fr
            (subset_closure hα_Ω)
        -- Yet `C_bd < ‖h α‖`, contradiction!
        have hC_lt : C_bd < ‖h α‖ := by
          have hba_eq : ‖β - α‖ = ‖α - β‖ := norm_sub_rev β α
          rw [hba_eq] at h2dist
          have hinv_le : (1 - ‖β‖)⁻¹ ≤ (2 * ‖α - β‖)⁻¹ :=
            inv_anti₀ (mul_pos zero_lt_two hαβ_pos) h2dist.le
          calc C_bd = (1 - ‖β‖)⁻¹ ^ n * M_T := rfl
            _ ≤ (2 * ‖α - β‖)⁻¹ ^ n * M_T := by
                exact mul_le_mul_of_nonneg_right
                  (pow_le_pow_left₀ (inv_nonneg.mpr h1β_pos.le) hinv_le n)
                  (le_max_right _ _)
            _ = ‖α - β‖⁻¹ ^ n * (M_T / 2 ^ n) := by
                rw [mul_inv, mul_pow, inv_pow, div_eq_mul_inv]
                ring
            _ < ‖α - β‖⁻¹ ^ n * ‖f α‖ := by
                refine mul_lt_mul_of_pos_left ?_ (pow_pos (inv_pos.mpr hαβ_pos) n)
                exact (div_lt_iff₀ (pow_pos zero_lt_two n)).mpr (by linarith)
            _ = ‖h α‖ := by
                dsimp only [h]
                rw [norm_mul, norm_pow, norm_inv]
        linarith
      -- Step 2: Apply Theorem 12.13 to `M = {g ∈ C(Ū) | DifferentiableOn ℂ g Ω}`
      let M_sub : Submodule ℂ (ℂ → ℂ) :=
        { carrier := {g : ℂ → ℂ | ContinuousOn g (closedBall (0 : ℂ) 1) ∧ DifferentiableOn ℂ g Ω}
          add_mem' := fun hg₁ hg₂ => ⟨hg₁.1.add hg₂.1, hg₁.2.add hg₂.2⟩
          zero_mem' := ⟨continuousOn_const, differentiableOn_const 0⟩
          smul_mem' := fun c _ hg => ⟨continuousOn_const.smul hg.1, hg.2.const_smul c⟩ }
      have hone_M : (fun _ : ℂ => (1 : ℂ)) ∈ M_sub :=
        ⟨continuousOn_const, differentiableOn_const 1⟩
      have hmul_M : ∀ g ∈ M_sub, (fun z : ℂ => z * g z) ∈ M_sub :=
        fun _ hg => ⟨continuousOn_id.mul hg.1, differentiableOn_id.mul hg.2⟩
      have hnorm_M : ∀ g ∈ M_sub, openDiscNorm g = boundaryNorm g (ball 0 1) := by
        intro g hg
        rw [openDiscNorm_eq_closedBall_sSup hg.1]
        have hg_bdd_cb : BddAbove ((fun z => ‖g z‖) '' closedBall (0 : ℂ) 1) :=
          ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hg.1.norm).bddAbove
        have hg_bdd_T : BddAbove ((fun z => ‖g z‖) '' frontier (ball (0 : ℂ) 1)) := by
          rw [frontier_ball (0 : ℂ) one_ne_zero]
          exact hg_bdd_cb.mono (image_mono sphere_subset_closedBall)
        have hT_nonneg : 0 ≤ boundaryNorm g (ball 0 1) := by
          have h1 : (1 : ℂ) ∈ frontier (ball (0 : ℂ) 1) := by
            rw [frontier_ball (0 : ℂ) one_ne_zero]; simp
          exact (norm_nonneg (g 1)).trans (le_csSup hg_bdd_T ⟨1, h1, rfl⟩)
        apply le_antisymm
        · -- Show `∀ α ∈ Ω, ‖g α‖ ≤ boundaryNorm g (ball 0 1)` via `f * g^n`
          have hΩ_le : ∀ α ∈ Ω, ‖g α‖ ≤ boundaryNorm g (ball 0 1) := by
            intro α hα
            by_contra hgt
            push Not at hgt
            have hfα_pos : 0 < ‖f α‖ := norm_pos_iff.mpr hα.2
            have h_fgn : ∀ n : ℕ, ‖f α‖ * ‖g α‖ ^ n ≤ M_T * boundaryNorm g (ball 0 1) ^ n := by
              intro n
              let F_n : ℂ → ℂ := fun z => f z * g z ^ n
              have hFn_holo : DifferentiableOn ℂ F_n Ω := hholo.mul (hg.2.pow n)
              have hFn_cont : ContinuousOn F_n (closure Ω) :=
                (hcont.mono hΩ_cl_sub).mul ((hg.1.mono hΩ_cl_sub).pow n)
              have hFn_fr : ∀ z ∈ frontier Ω, ‖F_n z‖ ≤ M_T * boundaryNorm g (ball 0 1) ^ n := by
                intro z hz
                have hz_cb : z ∈ closedBall (0 : ℂ) 1 := hΩ_cl_sub hz.1
                rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hz_cb) with hz_lt | hz_eq
                · have hz_not_Ω : z ∉ Ω := by
                    rw [frontier, hΩ_open.interior_eq] at hz
                    exact hz.2
                  have hfz0 : f z = 0 := by
                    by_contra hne
                    exact hz_not_Ω ⟨mem_ball_zero_iff.mpr hz_lt, hne⟩
                  dsimp only [F_n]
                  rw [hfz0, zero_mul, norm_zero]
                  exact mul_nonneg (le_max_right _ _) (pow_nonneg hT_nonneg n)
                · have hz_sph : z ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr hz_eq
                  have hz_fr : z ∈ frontier (ball (0 : ℂ) 1) := by
                    rwa [frontier_ball (0 : ℂ) one_ne_zero]
                  dsimp only [F_n]
                  rw [norm_mul, norm_pow]
                  refine mul_le_mul (hf_T z hz_sph) ?_ (pow_nonneg (norm_nonneg _) n)
                    (le_max_right _ _)
                  exact pow_le_pow_left₀ (norm_nonneg _) (le_csSup hg_bdd_T ⟨z, hz_fr, rfl⟩) n
              have hle := Complex.norm_le_of_forall_mem_frontier_norm_le hΩ_bdd
                ⟨hFn_holo, hFn_cont⟩ hFn_fr (subset_closure hα)
              simpa only [F_n, norm_mul, norm_pow] using hle
            rcases eq_or_lt_of_le hT_nonneg with hT0 | hT_pos
            · have h1 := h_fgn 1
              rw [← hT0, pow_one, pow_one, mul_zero] at h1
              have : 0 < ‖f α‖ * ‖g α‖ := mul_pos hfα_pos (by rw [← hT0] at hgt; exact hgt)
              linarith
            · have hratio : 1 < ‖g α‖ / boundaryNorm g (ball 0 1) := (one_lt_div hT_pos).mpr hgt
              obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M_T / ‖f α‖) hratio
              have hle := h_fgn n
              have hdiv : (‖g α‖ / boundaryNorm g (ball 0 1)) ^ n ≤ M_T / ‖f α‖ := by
                rw [div_pow, div_le_div_iff₀ (pow_pos hT_pos n) hfα_pos]
                linarith
              linarith
          -- Extend from `Ω` to `closedBall 0 1` by density (`closure Ω = closedBall 0 1`)
          have hcl_eq : closure Ω = closedBall (0 : ℂ) 1 := by
            apply Subset.antisymm hΩ_cl_sub
            rw [← closure_ball (0 : ℂ) one_ne_zero]
            exact closure_minimal hdense isClosed_closure
          refine csSup_le ⟨‖g 0‖, 0, mem_closedBall_self zero_le_one, rfl⟩ ?_
          rintro _ ⟨z, hz, rfl⟩
          rw [← hcl_eq] at hz
          have hclosed : IsClosed {w ∈ closedBall (0 : ℂ) 1 | ‖g w‖ ≤ boundaryNorm g (ball 0 1)} :=
            ContinuousOn.preimage_isClosed_of_isClosed hg.1.norm isClosed_closedBall isClosed_Iic
          have hsub_cl : Ω ⊆ {w ∈ closedBall (0 : ℂ) 1 | ‖g w‖ ≤ boundaryNorm g (ball 0 1)} :=
            fun w hw => ⟨ball_subset_closedBall hw.1, hΩ_le w hw⟩
          exact (closure_minimal hsub_cl hclosed hz).2
        · refine csSup_le ⟨‖g 1‖, 1, by rw [frontier_ball (0 : ℂ) one_ne_zero]; simp, rfl⟩ ?_
          rintro _ ⟨z, hz, rfl⟩
          rw [frontier_ball (0 : ℂ) one_ne_zero] at hz
          exact le_csSup hg_bdd_cb ⟨z, sphere_subset_closedBall hz, rfl⟩
      exact theorem12_13 M_sub (fun _ hg => hg.1) hone_M hmul_M hnorm_M f ⟨hcont, hholo⟩
  refine ⟨hholo_U, ?_⟩
  by_cases hΩ_empty : Ω = ∅
  · exact Or.inl hΩ_empty
  · right
    obtain ⟨α₀, hα₀⟩ := nonempty_iff_ne_empty.mpr hΩ_empty
    have hnot_eqOn : ¬ Set.EqOn f 0 (ball (0 : ℂ) 1) := fun heq => hα₀.2 (heq hα₀.1)
    have hcnt := RudinRCA.Chapter10.zeroSet_countable
      (RudinRCA.Chapter10.disc_isRegion 0 zero_lt_one)
      ((RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn isOpen_ball).mpr hholo_U)
      hnot_eqOn
    refine hcnt.mono ?_
    intro z hz
    refine ⟨hz.1, ?_⟩
    exact not_not.mp fun hne => hz.2 ⟨hz.1, hne⟩

end Node12_14

/-! ### Nodes 12.11 and 12.12: Uniformly Bounded Orthonormal Systems & Hausdorff–Young Theorem -/

section Nodes12_11_and_12_12

open RudinRCA.Chapter11

/-- Generalized Fourier coefficient `f̂(i) = ∫ x, f x * conj (ψ i x) ∂μ` of `f` with respect to
a system `ψ : ι → X → ℂ` on a positive measure space `(X, μ)` (Rudin 12.11(3), p. 260). -/
def fourierCoeffSys {X ι : Type*} [MeasurableSpace X]
    (ψ : ι → X → ℂ) (μ : Measure X) (f : X → ℂ) (i : ι) : ℂ :=
  ∫ x, f x * conj (ψ i x) ∂μ

private theorem memLp_ofReal_iff_integrable_rpow {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : X → ℂ} (hg_meas : AEStronglyMeasurable g μ) {p : ℝ} (hp : 0 < p) :
    MemLp g (ENNReal.ofReal p) μ ↔ Integrable (fun x => ‖g x‖ ^ p) μ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  constructor
  · intro hg
    simpa [ENNReal.toReal_ofReal hp.le] using hg.integrable_norm_rpow hp0 hptop
  · intro hint
    unfold MemLp
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hg_meas, ENNReal.toReal_ofReal hp.le]
    have hfin : ∫⁻ x, ‖g x‖ₑ ^ p ∂μ < ⊤ := by
      have hf := hint.hasFiniteIntegral
      unfold HasFiniteIntegral at hf
      refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hf
      dsimp only
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le,
        ← ofReal_norm, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hfin.ne

private theorem ennreal_holderConjugate_ofReal {p q : ℝ} (hpq : p.HolderConjugate q) :
    (ENNReal.ofReal p).HolderConjugate (ENNReal.ofReal q) := by
  obtain ⟨hp1, hsum⟩ := Real.holderConjugate_iff.mp hpq
  have hp_pos : 0 < p := zero_lt_one.trans hp1
  have hq_inv : 0 < q⁻¹ := by
    have hp_inv_lt : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    linarith
  have hq_pos : 0 < q := inv_pos.mp hq_inv
  rw [ENNReal.holderConjugate_iff, ← ENNReal.ofReal_inv_of_pos hp_pos,
    ← ENNReal.ofReal_inv_of_pos hq_pos,
    ← ENNReal.ofReal_add (inv_nonneg.mpr hp_pos.le) (inv_nonneg.mpr hq_pos.le),
    hsum, ENNReal.ofReal_one]

/-- A function in `L²(μ)` with a.e. bound `‖g x‖ ≤ M` (`0 ≤ M`) belongs to `L^q(μ)` for every
`2 ≤ q ≤ ∞`. -/
theorem memLp_of_memLp_two_of_ae_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : X → ℂ} (hg2 : MemLp g 2 μ) {M : ℝ} (_hM : 0 ≤ M) (hbdd : ∀ᵐ x ∂μ, ‖g x‖ ≤ M)
    {q : ℝ≥0∞} (hq2 : 2 ≤ q) :
    MemLp g q μ := by
  rcases eq_or_lt_of_le hq2 with rfl | hq_gt
  · exact hg2
  rcases eq_or_ne q ⊤ with rfl | hq_top
  · exact memLp_top_of_bound hg2.aestronglyMeasurable M hbdd
  · have hq_pos : 0 < q.toReal := ENNReal.toReal_pos (by positivity) hq_top
    have hq2_real : 2 < q.toReal :=
      (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hq_top).mpr hq_gt
    have hint_g2 : Integrable (fun x => ‖g x‖ ^ (2 : ℝ)) μ := by
      simpa using hg2.integrable_norm_rpow (by norm_num : (2 : ℝ≥0∞) ≠ 0) ENNReal.ofNat_ne_top
    have hint_gq : Integrable (fun x => ‖g x‖ ^ q.toReal) μ := by
      refine Integrable.mono' (hint_g2.const_mul (M ^ (q.toReal - 2)))
        (hg2.aestronglyMeasurable.norm.aemeasurable.pow_const q.toReal).aestronglyMeasurable ?_
      filter_upwards [hbdd] with x hx
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      by_cases gx0 : ‖g x‖ = 0
      · rw [gx0, Real.zero_rpow hq_pos.ne', Real.zero_rpow two_ne_zero, mul_zero]
      · have hpos : 0 < ‖g x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm gx0)
        have hsplit : ‖g x‖ ^ q.toReal = ‖g x‖ ^ (q.toReal - 2) * ‖g x‖ ^ (2 : ℝ) := by
          rw [← Real.rpow_add hpos, sub_add_cancel]
        rw [hsplit]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hpos.le hx (sub_nonneg.mpr hq2_real.le))
          (Real.rpow_nonneg hpos.le 2)
    rw [← ENNReal.ofReal_toReal hq_top]
    exact (memLp_ofReal_iff_integrable_rpow hg2.aestronglyMeasurable hq_pos).mpr hint_gq

/-- Orthonormal integral condition 12.11(1) is equivalent to `Orthonormal ℂ` in `Lp ℂ 2 μ`. -/
theorem orthonormal_lp2_iff_integral {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]
    {μ : Measure X} {ψ : ι → X → ℂ} (hψ : ∀ i, MemLp (ψ i) 2 μ) :
    Orthonormal ℂ (fun i => (hψ i).toLp (ψ i)) ↔
      ∀ n m : ι, ∫ x, ψ n x * conj (ψ m x) ∂μ = if m = n then 1 else 0 := by
  rw [RudinRCA.Chapter04.orthonormal_iff_rudin]
  constructor
  · intro horth n m
    have h := horth n m
    rw [L2.inner_def] at h
    have heq : (∫ a, inner ℂ (((hψ m).toLp (ψ m)) a) (((hψ n).toLp (ψ n)) a) ∂μ) =
        ∫ x, ψ n x * conj (ψ m x) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [(hψ n).coeFn_toLp, (hψ m).coeFn_toLp] with x hxn hxm
      rw [hxn, hxm]
      simp
    rw [← heq, h]
    by_cases hnm : n = m <;> simp [hnm, eq_comm]
  · intro hint i j
    rw [L2.inner_def]
    have h := hint i j
    have heq : (∫ a, inner ℂ (((hψ j).toLp (ψ j)) a) (((hψ i).toLp (ψ i)) a) ∂μ) =
        ∫ x, ψ i x * conj (ψ j x) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [(hψ i).coeFn_toLp, (hψ j).coeFn_toLp] with x hxi hxj
      rw [hxi, hxj]
      simp
    rw [heq, h]
    by_cases hij : i = j <;> simp [hij, eq_comm]

/-- 12.11 (Uniformly bounded orthonormal setup and `p = 1`, `p = 2` endpoint theorems,
Rudin p. 260): Let `(X, μ)` be a positive measure space and `{ψ_n}` an orthonormal family in
`L²(μ)` bounded a.e. by `M ≥ 0` (`∀ n, ∀ᵐ x ∂μ, ‖ψ n x‖ ≤ M`, which automatically holds if
`∀ n x, ‖ψ n x‖ ≤ M` or if `rudinEssSup μ (ψ n) ≤ M`). Then:
1. If `ι` is nonempty, `μ Set.univ ≠ 0`, `0 < M`, and `rudinEssSup μ (ψ n) ≤ M` for all `n`;
2. For every `1 ≤ p ≤ 2` and `f ∈ L^p(μ)`, the integrand `x ↦ f x * conj (ψ n x)` is
   `μ`-integrable for every `n`;
3. (`p = 1`, eq. (4)) For `f ∈ L¹(μ)`, `‖f̂(n)‖ ≤ M * ∫ x, ‖f x‖ ∂μ` for all `n`, and
   `Memℓp (fourierCoeffSys ψ μ f) ⊤` with `‖...‖_∞ ≤ M * ‖f‖₁`;
4. (`p = 2`, eq. (5)) For `f ∈ L²(μ)`, `Summable (fun n => ‖f̂(n)‖ ^ 2)` (`Memℓp ... 2`) and
   `(∑' n, ‖f̂(n)‖ ^ 2) ^ (1 / 2 : ℝ) ≤ (eLpNorm f 2 μ).toReal`. -/
theorem theorem12_11 {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]
    {μ : Measure X} {ψ : ι → X → ℂ} (hψ : ∀ n, MemLp (ψ n) 2 μ)
    (horth : ∀ n m : ι, ∫ x, ψ n x * conj (ψ m x) ∂μ = if m = n then 1 else 0)
    {M : ℝ} (hM : 0 ≤ M) (hbdd : ∀ n, ∀ᵐ x ∂μ, ‖ψ n x‖ ≤ M) :
    (Nonempty ι → μ Set.univ ≠ 0 ∧ 0 < M ∧ ∀ n, rudinEssSup μ (ψ n) ≤ M) ∧
    (∀ {p : ℝ≥0∞}, 1 ≤ p → p ≤ 2 → ∀ {f : X → ℂ}, MemLp f p μ →
      ∀ n, Integrable (fun x => f x * conj (ψ n x)) μ) ∧
    (∀ {f : X → ℂ}, Integrable f μ →
      (∀ n, ‖fourierCoeffSys ψ μ f n‖ ≤ M * ∫ x, ‖f x‖ ∂μ) ∧
      Memℓp (fourierCoeffSys ψ μ f) ⊤) ∧
    (∀ {f : X → ℂ}, MemLp f 2 μ →
      Summable (fun n => ‖fourierCoeffSys ψ μ f n‖ ^ 2) ∧
      Memℓp (fourierCoeffSys ψ μ f) 2 ∧
      (∑' n, ‖fourierCoeffSys ψ μ f n‖ ^ 2) ^ (1 / 2 : ℝ) ≤ (eLpNorm f 2 μ).toReal) := by
  have horth_lp : Orthonormal ℂ (fun n => (hψ n).toLp (ψ n)) :=
    (orthonormal_lp2_iff_integral hψ).mpr horth
  -- Part 1: Nonempty `ι` forces `μ univ ≠ 0`, `0 < M`, and literal 3.7 `rudinEssSup ≤ M`
  have hpart1 : Nonempty ι → μ Set.univ ≠ 0 ∧ 0 < M ∧ ∀ n, rudinEssSup μ (ψ n) ≤ M := by
    rintro ⟨n₀⟩
    have h1 := horth n₀ n₀
    simp only [ ↓reduceIte] at h1
    have hμ_ne : μ Set.univ ≠ 0 := by
      intro h0
      have hzero : μ = 0 := Measure.measure_univ_eq_zero.mp h0
      subst hzero
      simp at h1
    have hM_pos : 0 < M := by
      refine lt_of_le_of_ne hM ?_
      intro hM0
      subst hM0
      have hae0 : ∀ᵐ x ∂μ, ψ n₀ x * conj (ψ n₀ x) = 0 := by
        filter_upwards [hbdd n₀] with x hx
        have : ψ n₀ x = 0 := norm_le_zero_iff.mp hx
        simp [this]
      rw [integral_eq_zero_of_ae hae0] at h1
      exact zero_ne_one h1
    refine ⟨hμ_ne, hM_pos, fun n => ?_⟩
    have hmem_top : MemLp (ψ n) ⊤ μ := memLp_top_of_bound (hψ n).aestronglyMeasurable M (hbdd n)
    rw [rudinEssSup_eq_eLpNorm_top_toReal hμ_ne hmem_top, eLpNorm_exponent_top hmem_top.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal hM (essSup_le_of_ae_le _ ?_)
    filter_upwards [hbdd n] with x hx
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hx
  -- Part 2: Integrability of `f * conj(ψ n)` for `1 ≤ p ≤ 2`
  have hpart2 : ∀ {p : ℝ≥0∞}, 1 ≤ p → p ≤ 2 → ∀ {f : X → ℂ}, MemLp f p μ →
      ∀ n, Integrable (fun x => f x * conj (ψ n x)) μ := by
    intro p hp1 hp2 f hf n
    rcases eq_or_lt_of_le hp1 with rfl | hp_gt
    · have hint_f : Integrable f μ := memLp_one_iff_integrable.mp hf
      have h_conj_meas : AEStronglyMeasurable (fun x => conj (ψ n x)) μ :=
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).continuous.comp_aestronglyMeasurable (hψ n).aestronglyMeasurable
      have h_conj_bdd : ∀ᵐ x ∂μ, ‖conj (ψ n x)‖ ≤ M := by
        filter_upwards [hbdd n] with x hx using by simpa using hx
      simpa only [mul_comm (f _)] using hint_f.bdd_mul h_conj_meas h_conj_bdd
    · have hp_top : p ≠ ⊤ := (lt_of_le_of_lt hp2 ENNReal.ofNat_lt_top).ne
      let q : ℝ≥0∞ := ENNReal.ofReal (p.toReal.conjExponent)
      have hp_real : 1 < p.toReal := by
        rw [← ENNReal.toReal_one]
        exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).mpr hp_gt
      have hp2_real : p.toReal ≤ 2 := by
        have := ENNReal.toReal_mono ENNReal.ofNat_ne_top hp2
        simpa using this
      have hpq_real : p.toReal.HolderConjugate p.toReal.conjExponent :=
        Real.HolderConjugate.conjExponent hp_real
      have hp_eq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hp_top
      have hpq : p.HolderConjugate q := by
        rw [← hp_eq]
        exact ennreal_holderConjugate_ofReal hpq_real
      have hq2_real : 2 ≤ p.toReal.conjExponent := by
        rw [Real.conjExponent, le_div_iff₀ (sub_pos.mpr hp_real)]
        nlinarith
      have hq2 : 2 ≤ q := by
        dsimp only [q]
        rw [← ENNReal.ofReal_ofNat 2]
        exact ENNReal.ofReal_le_ofReal hq2_real
      have hψ_q : MemLp (ψ n) q μ := memLp_of_memLp_two_of_ae_bound (hψ n) hM (hbdd n) hq2
      have hconj_q : MemLp (fun x => conj (ψ n x)) q μ :=
        (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ).comp_memLp' hψ_q
      exact hf.integrable_mul hconj_q
  -- Part 3: `p = 1` bound
  have hpart3 : ∀ {f : X → ℂ}, Integrable f μ →
      (∀ n, ‖fourierCoeffSys ψ μ f n‖ ≤ M * ∫ x, ‖f x‖ ∂μ) ∧
      Memℓp (fourierCoeffSys ψ μ f) ⊤ := by
    intro f hf
    have hbd_n : ∀ n, ‖fourierCoeffSys ψ μ f n‖ ≤ M * ∫ x, ‖f x‖ ∂μ := by
      intro n
      unfold fourierCoeffSys
      calc ‖∫ x, f x * conj (ψ n x) ∂μ‖
          ≤ ∫ x, ‖f x * conj (ψ n x)‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ x, ‖f x‖ * M ∂μ := by
            refine integral_mono_ae ?_ (hf.norm.mul_const M) ?_
            · exact (hpart2 le_rfl (by norm_num) (memLp_one_iff_integrable.mpr hf) n).norm
            · filter_upwards [hbdd n] with x hx
              rw [norm_mul, RCLike.norm_conj]
              exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
        _ = M * ∫ x, ‖f x‖ ∂μ := by rw [integral_mul_const, mul_comm]
    refine ⟨hbd_n, memℓp_infty ⟨M * ∫ x, ‖f x‖ ∂μ, ?_⟩⟩
    rintro _ ⟨n, rfl⟩
    exact hbd_n n
  -- Part 4: `p = 2` Bessel bound
  have hpart4 : ∀ {f : X → ℂ}, MemLp f 2 μ →
      Summable (fun n => ‖fourierCoeffSys ψ μ f n‖ ^ 2) ∧
      Memℓp (fourierCoeffSys ψ μ f) 2 ∧
      (∑' n, ‖fourierCoeffSys ψ μ f n‖ ^ 2) ^ (1 / 2 : ℝ) ≤ (eLpNorm f 2 μ).toReal := by
    intro f hf
    let f_lp : Lp ℂ 2 μ := hf.toLp f
    have hcoeff_eq : ∀ n, fourierCoeffSys ψ μ f n = inner ℂ ((hψ n).toLp (ψ n)) f_lp := by
      intro n
      rw [L2.inner_def]
      unfold fourierCoeffSys
      refine integral_congr_ae ?_
      filter_upwards [hf.coeFn_toLp, (hψ n).coeFn_toLp] with x hfx hψx
      rw [hfx, hψx]
      simp
    have hsum_fin : ∀ s : Finset ι,
        ∑ n ∈ s, ‖fourierCoeffSys ψ μ f n‖ ^ 2 ≤ ‖f_lp‖ ^ 2 := by
      intro s
      simpa only [hcoeff_eq] using horth_lp.sum_inner_products_le f_lp (s := s)
    have hsumm : Summable (fun n => ‖fourierCoeffSys ψ μ f n‖ ^ 2) :=
      summable_of_sum_le (fun _ => sq_nonneg _) hsum_fin
    have hmem2 : Memℓp (fourierCoeffSys ψ μ f) 2 := by
      rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
      simpa using hsumm
    have htsum : ∑' n, ‖fourierCoeffSys ψ μ f n‖ ^ 2 ≤ ‖f_lp‖ ^ 2 := by
      simpa only [hcoeff_eq] using horth_lp.tsum_inner_products_le f_lp
    have hnorm_lp : ‖f_lp‖ = (eLpNorm f 2 μ).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp]
    have hrpow : (∑' n, ‖fourierCoeffSys ψ μ f n‖ ^ 2) ^ (1 / 2 : ℝ) ≤ ‖f_lp‖ := by
      calc (∑' n, ‖fourierCoeffSys ψ μ f n‖ ^ 2) ^ (1 / 2 : ℝ)
          ≤ (‖f_lp‖ ^ 2) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (tsum_nonneg fun _ => sq_nonneg _) htsum (by positivity)
        _ = ‖f_lp‖ := by
            rw [← Real.rpow_natCast ‖f_lp‖ 2, ← Real.rpow_mul (norm_nonneg f_lp)]
            norm_num
    rw [hnorm_lp] at hrpow
    exact ⟨hsumm, hmem2, hrpow⟩
  exact ⟨hpart1, hpart2, hpart3, hpart4⟩

/-- Reduced interpolation inequality 12.12(2) for an `L^p` simple function `s` with `‖s‖_p = 1`
and finite sequence `b` on `F : Finset ι` with `∑ n ∈ F, ‖b n‖ ^ p = 1` (`1 < p < 2`). -/
private theorem hausdorff_young_simple_normalized {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]
    {μ : Measure X} {ψ : ι → X → ℂ} (hψ : ∀ n, MemLp (ψ n) 2 μ)
    (horth : ∀ n m : ι, ∫ x, ψ n x * conj (ψ m x) ∂μ = if m = n then 1 else 0)
    {M : ℝ} (hM_pos : 0 < M) (hbdd : ∀ n, ∀ᵐ x ∂μ, ‖ψ n x‖ ≤ M)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (s : SimpleFunc X ℂ) (hs_lp : MemLp s (ENNReal.ofReal p) μ)
    (hs_norm : (eLpNorm s (ENNReal.ofReal p) μ).toReal = 1)
    (F : Finset ι) (b : ι → ℂ) (hb_sum : ∑ n ∈ F, ‖b n‖ ^ p = 1) :
    ‖∑ n ∈ F, b n * fourierCoeffSys ψ μ s n‖ ≤ M ^ ((2 - p) / p) := by
  classical
  have hp_pos : 0 < p := zero_lt_one.trans hp1
  obtain ⟨_, _, h11_p1, h11_p2⟩ := theorem12_11 hψ horth hM_pos.le hbdd
  -- Nonzero range values `V` of `s`: each fiber `E v = s ⁻¹' {v}` is measurable with `μ (E v) < ⊤`
  let V : Finset ℂ := s.range.erase 0
  let E : ℂ → Set X := fun v => s ⁻¹' {v}
  have hE_meas : ∀ v, MeasurableSet (E v) := fun v => s.measurableSet_fiber v
  have hE_disj : PairwiseDisjoint (V : Set ℂ) E := by
    intro v₁ _ v₂ _ hne
    exact Disjoint.preimage s (disjoint_singleton.mpr hne)
  have hE_fin : ∀ v ∈ V, μ (E v) < ⊤ := by
    intro v hv
    have hv_ne : v ≠ 0 := (Finset.mem_erase.mp hv).1
    have hv_pos : 0 < ‖v‖ ^ p := Real.rpow_pos_of_pos (norm_pos_iff.mpr hv_ne) p
    have hle : ENNReal.ofReal (‖v‖ ^ p) * μ (E v) ≤
        ∫⁻ x, ENNReal.ofReal (‖s x‖ ^ p) ∂μ := by
      calc ENNReal.ofReal (‖v‖ ^ p) * μ (E v)
          = ∫⁻ _ in E v, ENNReal.ofReal (‖v‖ ^ p) ∂μ := (setLIntegral_const _ _).symm
        _ = ∫⁻ x in E v, ENNReal.ofReal (‖s x‖ ^ p) ∂μ :=
            setLIntegral_congr_fun (hE_meas v) fun x hx => by
              have hsx : s x = v := hx
              rw [hsx]
        _ ≤ ∫⁻ x, ENNReal.ofReal (‖s x‖ ^ p) ∂μ := setLIntegral_le_lintegral _ _
    have hint_p : Integrable (fun x => ‖s x‖ ^ p) μ :=
      (memLp_ofReal_iff_integrable_rpow hs_lp.aestronglyMeasurable hp_pos).mp hs_lp
    have hlt_top : ∫⁻ x, ENNReal.ofReal (‖s x‖ ^ p) ∂μ < ⊤ := by
      have hf := hint_p.hasFiniteIntegral
      unfold HasFiniteIntegral at hf
      refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hf
      rw [← ofReal_norm, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)]
    have hmul_lt := lt_of_le_of_lt hle hlt_top
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hv_pos).ne'] at hmul_lt
    exact lt_irrefl _ hmul_lt
  -- Integrability of `conj ∘ ψ n` on every `E v` (`v ∈ V`)
  have hψ_intOn : ∀ n, ∀ v ∈ V, IntegrableOn (fun x => conj (ψ n x)) (E v) μ := by
    intro n v hv
    have hind_lp : MemLp (Set.indicator (E v) (1 : X → ℂ)) 2 μ :=
      memLp_indicator_const 2 (hE_meas v) (1 : ℂ) (Or.inr (hE_fin v hv).ne)
    have hconj_lp : MemLp (fun x => conj (ψ n x)) 2 μ :=
      (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ).comp_memLp' (hψ n)
    have hm := hind_lp.integrable_mul hconj_lp
    rw [← integrable_indicator_iff (hE_meas v)]
    refine hm.congr (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ E v <;> simp [hx]
  -- Pointwise decomposition of `s x`: `s x = ∑ v ∈ V, Set.indicator (E v) (fun _ => v) x`
  have hs_sum : ∀ x, s x = ∑ v ∈ V, Set.indicator (E v) (fun _ => v) x := by
    intro x
    by_cases hsx : s x = 0
    · rw [hsx, eq_comm]
      refine Finset.sum_eq_zero fun v hv => ?_
      have hv_ne : v ≠ 0 := (Finset.mem_erase.mp hv).1
      have hx_not : x ∉ E v := fun h => hv_ne (h.symm.trans hsx)
      simp [hx_not]
    · have hv_mem : s x ∈ V := Finset.mem_erase.mpr ⟨hsx, SimpleFunc.mem_range_self s x⟩
      rw [Finset.sum_eq_single (s x)]
      · simp [E]
      · intro v _ hne
        have hx_not : x ∉ E v := fun h => hne h.symm
        simp [hx_not]
      · intro hnot; exact absurd hv_mem hnot
  -- Sum of `‖v‖^p * μ.real (E v)` equals `∫ ‖s x‖^p ∂μ = 1`
  have hA_sum : ∑ v ∈ V, ‖v‖ ^ p * μ.real (E v) = 1 := by
    have hpt : (fun x => ‖s x‖ ^ p) =
        fun x => ∑ v ∈ V, Set.indicator (E v) (fun _ => ‖v‖ ^ p) x := by
      ext x
      by_cases hsx : s x = 0
      · rw [hsx, norm_zero, Real.zero_rpow hp_pos.ne', eq_comm]
        refine Finset.sum_eq_zero fun v hv => ?_
        have hv_ne : v ≠ 0 := (Finset.mem_erase.mp hv).1
        have hx_not : x ∉ E v := fun h => hv_ne (h.symm.trans hsx)
        simp [hx_not]
      · have hv_mem : s x ∈ V := Finset.mem_erase.mpr ⟨hsx, SimpleFunc.mem_range_self s x⟩
        rw [Finset.sum_eq_single (s x)]
        · simp [E]
        · intro v _ hne
          have hx_not : x ∉ E v := fun h => hne h.symm
          simp [hx_not]
        · intro hnot; exact absurd hv_mem hnot
    have hint_eq : ∫ x, ‖s x‖ ^ p ∂μ = ∑ v ∈ V, ‖v‖ ^ p * μ.real (E v) := by
      rw [hpt, integral_finsetSum _ fun v hv =>
        (integrableOn_const (hs := (hE_fin v hv).ne)).integrable_indicator (hE_meas v)]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [integral_indicator (hE_meas v), setIntegral_const, smul_eq_mul, mul_comm]
    rw [← hint_eq]
    have heLp := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) (f := s)
      (ENNReal.ofReal_pos.mpr hp_pos).ne' ENNReal.ofReal_ne_top hs_lp.aestronglyMeasurable
    rw [ENNReal.toReal_ofReal hp_pos.le] at heLp
    have h1 : (∫⁻ x, ‖s x‖ₑ ^ p ∂μ).toReal ^ (1 / p) = 1 := by
      have h := hs_norm
      rwa [heLp, ← ENNReal.toReal_rpow] at h
    have h_int_eq_lint : ∫ x, ‖s x‖ ^ p ∂μ = (∫⁻ x, ‖s x‖ₑ ^ p ∂μ).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => Real.rpow_nonneg (norm_nonneg _) p)
        (hs_lp.aestronglyMeasurable.norm.aemeasurable.pow_const p).aestronglyMeasurable]
      congr 1
      refine lintegral_congr fun x => ?_
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp_pos.le]
    rw [h_int_eq_lint]
    have hnn : 0 ≤ (∫⁻ x, ‖s x‖ₑ ^ p ∂μ).toReal := ENNReal.toReal_nonneg
    calc (∫⁻ x, ‖s x‖ₑ ^ p ∂μ).toReal
        = ((∫⁻ x, ‖s x‖ₑ ^ p ∂μ).toReal ^ (1 / p)) ^ p := by
            rw [← Real.rpow_mul hnn, one_div_mul_cancel hp_pos.ne', Real.rpow_one]
      _ = 1 := by rw [h1, Real.one_rpow]
  -- Support `F₊ = {n ∈ F | b n ≠ 0}`
  let F_pos : Finset ι := F.filter fun n => b n ≠ 0
  let B : ι → ℝ := fun n => ‖b n‖ ^ p
  let β : ι → ℂ := fun n => b n / (‖b n‖ : ℂ)
  let A_val : ℂ → ℝ := fun v => ‖v‖ ^ p
  let φ_val : ℂ → ℂ := fun v => v / (‖v‖ : ℂ)
  let I_nv : ι → ℂ → ℂ := fun n v => ∫ x in E v, φ_val v * conj (ψ n x) ∂μ
  -- Define Rudin's analytic function `Φ(z)` (eq. 12.12(6)) as an explicit finite sum of exponentials
  let Φ : ℂ → ℂ := fun z =>
    ∑ n ∈ F_pos, ∑ v ∈ V,
      Complex.exp (z * (Real.log (B n) : ℂ)) * β n *
        Complex.exp (z * (Real.log (A_val v) : ℂ)) * I_nv n v
  -- Entirety and boundedness of `Φ` on `[1/2, 1]`
  have hΦ_entire : Differentiable ℂ Φ := by
    refine Differentiable.fun_sum fun n _ => Differentiable.fun_sum fun v _ => ?_
    exact ((((differentiable_id.mul_const _).cexp.mul_const _).mul
      (differentiable_id.mul_const _).cexp).mul_const _)
  have hΦ_bdd : ∃ C_B : ℝ, ∀ z : ℂ, 1 / 2 ≤ z.re ∧ z.re ≤ 1 → ‖Φ z‖ ≤ C_B := by
    refine ⟨∑ n ∈ F_pos, ∑ v ∈ V,
      Real.exp (max (Real.log (B n)) (1 / 2 * Real.log (B n))) * ‖β n‖ *
        Real.exp (max (Real.log (A_val v)) (1 / 2 * Real.log (A_val v))) * ‖I_nv n v‖, ?_⟩
    intro z hz
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_))
    simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    have hle1 : z.re * Real.log (B n) ≤ max (Real.log (B n)) (1 / 2 * Real.log (B n)) := by
      rcases le_or_gt 0 (Real.log (B n)) with h | h
      · exact (mul_le_of_le_one_left h hz.2).trans (le_max_left _ _)
      · exact (mul_le_mul_of_nonpos_right hz.1 h.le).trans (le_max_right _ _)
    have hle2 : z.re * Real.log (A_val v) ≤ max (Real.log (A_val v)) (1 / 2 * Real.log (A_val v)) := by
      rcases le_or_gt 0 (Real.log (A_val v)) with h | h
      · exact (mul_le_of_le_one_left h hz.2).trans (le_max_left _ _)
      · exact (mul_le_mul_of_nonpos_right hz.1 h.le).trans (le_max_right _ _)
    gcongr
  -- Integral formula for inner sum `∑ v ∈ V, exp(z log A_val v) * I_nv n v`
  have hinner_eq : ∀ (z : ℂ) (n : ι),
      (∑ v ∈ V, Complex.exp (z * (Real.log (A_val v) : ℂ)) * I_nv n v) =
        fourierCoeffSys ψ μ
          (fun x => ∑ v ∈ V,
            Set.indicator (E v)
              (fun _ => Complex.exp (z * (Real.log (A_val v) : ℂ)) * φ_val v) x) n := by
    intro z n
    unfold fourierCoeffSys
    have hfun : (fun x => (∑ v ∈ V, Set.indicator (E v)
          (fun _ => Complex.exp (z * (Real.log (A_val v) : ℂ)) * φ_val v) x) * conj (ψ n x)) =
        fun x => ∑ v ∈ V, Set.indicator (E v)
          (fun y => Complex.exp (z * (Real.log (A_val v) : ℂ)) * (φ_val v * conj (ψ n y))) x := by
      ext x
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hx : x ∈ E v <;> simp [hx, mul_assoc]
    rw [hfun, integral_finsetSum _ fun v hv => by
      have hi : IntegrableOn
          (fun y => Complex.exp (z * (Real.log (A_val v) : ℂ)) * (φ_val v * conj (ψ n y)))
          (E v) μ := ((hψ_intOn n v hv).const_mul _).const_mul _
      exact hi.integrable_indicator (hE_meas v)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [integral_indicator (hE_meas v), integral_const_mul]
  -- Estimate (9): `‖Φ(1/2 + i y)‖ ≤ 1` for all `y : ℝ`
  have hΦ_half : ∀ y : ℝ, ‖Φ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ ≤ 1 := by
    intro y
    let z : ℂ := ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I
    let g_y : X → ℂ := fun x => ∑ v ∈ V,
      Set.indicator (E v) (fun _ => Complex.exp (z * (Real.log (A_val v) : ℂ)) * φ_val v) x
    have hg_y_lp2 : MemLp g_y 2 μ := by
      refine memLp_finsetSum V fun v hv => ?_
      exact memLp_indicator_const 2 (hE_meas v) _ (Or.inr (hE_fin v hv).ne)
    -- Compute `(eLpNorm g_y 2 μ).toReal ≤ 1`
    have hg_y_norm_pt : ∀ x, ‖g_y x‖ ^ 2 =
        ∑ v ∈ V, Set.indicator (E v) (fun _ => A_val v) x := by
      intro x
      by_cases hsx : s x = 0
      · have hg0 : g_y x = 0 := by
          dsimp only [g_y]
          refine Finset.sum_eq_zero fun v hv => ?_
          have hv_ne : v ≠ 0 := (Finset.mem_erase.mp hv).1
          have hx_not : x ∉ E v := fun h => hv_ne (h.symm.trans hsx)
          simp [hx_not]
        rw [hg0, norm_zero, zero_pow two_ne_zero, eq_comm]
        refine Finset.sum_eq_zero fun v hv => ?_
        have hv_ne : v ≠ 0 := (Finset.mem_erase.mp hv).1
        have hx_not : x ∉ E v := fun h => hv_ne (h.symm.trans hsx)
        simp [hx_not]
      · have hv_mem : s x ∈ V := Finset.mem_erase.mpr ⟨hsx, SimpleFunc.mem_range_self s x⟩
        have hg_val : g_y x = Complex.exp (z * (Real.log (A_val (s x)) : ℂ)) * φ_val (s x) := by
          dsimp only [g_y]
          rw [Finset.sum_eq_single (s x)]
          · simp [E]
          · intro v _ hne
            have hx_not : x ∉ E v := fun h => hne h.symm
            simp [hx_not]
          · intro hnot; exact absurd hv_mem hnot
        have hA_pos : 0 < A_val (s x) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hsx) p
        have hφ_norm : ‖φ_val (s x)‖ = 1 := by
          dsimp only [φ_val]
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
            div_self (norm_ne_zero_iff.mpr hsx)]
        rw [hg_val, norm_mul, hφ_norm, mul_one, Complex.norm_exp]
        have hre : (z * (Real.log (A_val (s x)) : ℂ)).re = Real.log (A_val (s x)) * (1 / 2) := by
          simp [z, mul_comm]
        rw [hre, ← Real.rpow_def_of_pos hA_pos, ← Real.rpow_natCast _ 2,
          ← Real.rpow_mul hA_pos.le]
        norm_num
        rw [eq_comm, Finset.sum_eq_single (s x)]
        · simp [E]
        · intro v _ hne
          have hx_not : x ∉ E v := fun h => hne h.symm
          simp [hx_not]
        · intro hnot; exact absurd hv_mem hnot
    have hg_y_l2_le : (eLpNorm g_y 2 μ).toReal ≤ 1 := by
      have heLp := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) (f := g_y)
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) ENNReal.ofNat_ne_top hg_y_lp2.aestronglyMeasurable
      simp only [ENNReal.toReal_ofNat, one_div] at heLp
      have hlint : ∫⁻ x, ‖g_y x‖ₑ ^ (2 : ℝ) ∂μ = ENNReal.ofReal 1 := by
        have hint : ∫ x, ‖g_y x‖ ^ 2 ∂μ = 1 := by
          simp_rw [hg_y_norm_pt]
          rw [integral_finsetSum _ fun v hv =>
            (integrableOn_const (hs := (hE_fin v hv).ne)).integrable_indicator (hE_meas v)]
          have : (∑ v ∈ V, ∫ x, Set.indicator (E v) (fun _ => A_val v) x ∂μ) =
              ∑ v ∈ V, A_val v * μ.real (E v) := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [integral_indicator (hE_meas v), setIntegral_const, smul_eq_mul, mul_comm]
          rw [this]
          exact hA_sum
        have hint_sq : Integrable (fun x => ‖g_y x‖ ^ 2) μ := by
          simp_rw [hg_y_norm_pt]
          exact integrable_finsetSum _ fun v hv =>
            (integrableOn_const (hs := (hE_fin v hv).ne)).integrable_indicator (hE_meas v)
        rw [← hint, ofReal_integral_eq_lintegral_ofReal hint_sq (ae_of_all _ fun _ => sq_nonneg _)]
        refine lintegral_congr fun x => ?_
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two,
          Real.rpow_two]
      rw [heLp, hlint, ENNReal.ofReal_one, ENNReal.one_rpow, ENNReal.toReal_one]
    -- Apply Bessel (`h11_p2 hg_y_lp2`) + Cauchy–Schwarz on `F_pos`
    have hbessel : ∑ n ∈ F_pos, ‖fourierCoeffSys ψ μ g_y n‖ ^ 2 ≤ 1 := by
      have ⟨hsumm, _, htsum_rpow⟩ := h11_p2 hg_y_lp2
      have htsum_le1 : ∑' n, ‖fourierCoeffSys ψ μ g_y n‖ ^ 2 ≤ 1 := by
        have hle1 := htsum_rpow.trans hg_y_l2_le
        have hnn : 0 ≤ ∑' n, ‖fourierCoeffSys ψ μ g_y n‖ ^ 2 := tsum_nonneg fun _ => sq_nonneg _
        calc ∑' n, ‖fourierCoeffSys ψ μ g_y n‖ ^ 2
            = ((∑' n, ‖fourierCoeffSys ψ μ g_y n‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
                rw [← Real.rpow_mul hnn]; norm_num
          _ ≤ 1 ^ (2 : ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hnn _) hle1 zero_le_two
          _ = 1 := Real.one_rpow 2
      exact (hsumm.sum_le_tsum F_pos fun _ _ => sq_nonneg _).trans htsum_le1
    have hΦ_eq : Φ z = ∑ n ∈ F_pos,
        (Complex.exp (z * (Real.log (B n) : ℂ)) * β n) * fourierCoeffSys ψ μ g_y n := by
      dsimp only [Φ]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← hinner_eq z n, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => by ring
    rw [hΦ_eq]
    calc ‖∑ n ∈ F_pos, (Complex.exp (z * (Real.log (B n) : ℂ)) * β n) *
            fourierCoeffSys ψ μ g_y n‖
        ≤ ∑ n ∈ F_pos, ‖Complex.exp (z * (Real.log (B n) : ℂ)) * β n‖ *
            ‖fourierCoeffSys ψ μ g_y n‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => le_of_eq (norm_mul _ _))
      _ ≤ Real.sqrt (∑ n ∈ F_pos, ‖Complex.exp (z * (Real.log (B n) : ℂ)) * β n‖ ^ 2) *
          Real.sqrt (∑ n ∈ F_pos, ‖fourierCoeffSys ψ μ g_y n‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt F_pos _ _
      _ ≤ 1 * 1 := by
          refine mul_le_mul ?_ (Real.sqrt_le_one.mpr hbessel) (Real.sqrt_nonneg _) zero_le_one
          rw [Real.sqrt_le_one]
          have hsum_B : (∑ n ∈ F_pos, ‖Complex.exp (z * (Real.log (B n) : ℂ)) * β n‖ ^ 2) =
              ∑ n ∈ F_pos, B n := by
            refine Finset.sum_congr rfl fun n hn => ?_
            have hbn_ne : b n ≠ 0 := (Finset.mem_filter.mp hn).2
            have hBn_pos : 0 < B n := Real.rpow_pos_of_pos (norm_pos_iff.mpr hbn_ne) p
            have hβ_norm : ‖β n‖ = 1 := by
              dsimp only [β]
              rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
                div_self (norm_ne_zero_iff.mpr hbn_ne)]
            rw [norm_mul, hβ_norm, mul_one, Complex.norm_exp]
            have hre : (z * (Real.log (B n) : ℂ)).re = Real.log (B n) * (1 / 2) := by
              simp [z, mul_comm]
            rw [hre, ← Real.rpow_def_of_pos hBn_pos, ← Real.rpow_natCast _ 2,
              ← Real.rpow_mul hBn_pos.le]
            norm_num
          rw [hsum_B, ← hb_sum]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ F)
            fun _ _ _ => Real.rpow_nonneg (norm_nonneg _) p
      _ = 1 := mul_one 1
  -- Estimate (10): `‖Φ(1 + i y)‖ ≤ M` for all `y : ℝ`
  have hΦ_one : ∀ y : ℝ, ‖Φ ((1 : ℂ) + (y : ℂ) * Complex.I)‖ ≤ M := by
    intro y
    let z : ℂ := (1 : ℂ) + (y : ℂ) * Complex.I
    let h_y : X → ℂ := fun x => ∑ v ∈ V,
      Set.indicator (E v) (fun _ => Complex.exp (z * (Real.log (A_val v) : ℂ)) * φ_val v) x
    have hh_y_int : Integrable h_y μ :=
      integrable_finsetSum V fun v hv =>
        (integrableOn_const (hs := (hE_fin v hv).ne)).integrable_indicator (hE_meas v)
    have hh_y_norm_pt : ∀ x, ‖h_y x‖ = ∑ v ∈ V, Set.indicator (E v) (fun _ => A_val v) x := by
      intro x
      by_cases hsx : s x = 0
      · have hh0 : h_y x = 0 := by
          dsimp only [h_y]
          refine Finset.sum_eq_zero fun v hv => ?_
          have hv_ne : v ≠ 0 := (Finset.mem_erase.mp hv).1
          have hx_not : x ∉ E v := fun h => hv_ne (h.symm.trans hsx)
          simp [hx_not]
        rw [hh0, norm_zero, eq_comm]
        refine Finset.sum_eq_zero fun v hv => ?_
        have hv_ne : v ≠ 0 := (Finset.mem_erase.mp hv).1
        have hx_not : x ∉ E v := fun h => hv_ne (h.symm.trans hsx)
        simp [hx_not]
      · have hv_mem : s x ∈ V := Finset.mem_erase.mpr ⟨hsx, SimpleFunc.mem_range_self s x⟩
        have hh_val : h_y x = Complex.exp (z * (Real.log (A_val (s x)) : ℂ)) * φ_val (s x) := by
          dsimp only [h_y]
          rw [Finset.sum_eq_single (s x)]
          · simp [E]
          · intro v _ hne
            have hx_not : x ∉ E v := fun h => hne h.symm
            simp [hx_not]
          · intro hnot; exact absurd hv_mem hnot
        have hA_pos : 0 < A_val (s x) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hsx) p
        have hφ_norm : ‖φ_val (s x)‖ = 1 := by
          dsimp only [φ_val]
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
            div_self (norm_ne_zero_iff.mpr hsx)]
        rw [hh_val, norm_mul, hφ_norm, mul_one, Complex.norm_exp]
        have hre : (z * (Real.log (A_val (s x)) : ℂ)).re = Real.log (A_val (s x)) := by simp [z]
        rw [hre, Real.exp_log hA_pos, eq_comm, Finset.sum_eq_single (s x)]
        · simp [E]
        · intro v _ hne
          have hx_not : x ∉ E v := fun h => hne h.symm
          simp [hx_not]
        · intro hnot; exact absurd hv_mem hnot
    have hh_y_l1 : ∫ x, ‖h_y x‖ ∂μ = 1 := by
      simp_rw [hh_y_norm_pt]
      rw [integral_finsetSum _ fun v hv =>
        (integrableOn_const (hs := (hE_fin v hv).ne)).integrable_indicator (hE_meas v)]
      have : (∑ v ∈ V, ∫ x, Set.indicator (E v) (fun _ => A_val v) x ∂μ) =
          ∑ v ∈ V, A_val v * μ.real (E v) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [integral_indicator (hE_meas v), setIntegral_const, smul_eq_mul, mul_comm]
      rw [this]
      exact hA_sum
    have hcoeff_le : ∀ n, ‖fourierCoeffSys ψ μ h_y n‖ ≤ M := by
      intro n
      have h := (h11_p1 hh_y_int).1 n
      rwa [hh_y_l1, mul_one] at h
    have hΦ_eq : Φ z = ∑ n ∈ F_pos,
        (Complex.exp (z * (Real.log (B n) : ℂ)) * β n) * fourierCoeffSys ψ μ h_y n := by
      dsimp only [Φ]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← hinner_eq z n, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => by ring
    rw [hΦ_eq]
    calc ‖∑ n ∈ F_pos, (Complex.exp (z * (Real.log (B n) : ℂ)) * β n) *
            fourierCoeffSys ψ μ h_y n‖
        ≤ ∑ n ∈ F_pos, ‖Complex.exp (z * (Real.log (B n) : ℂ)) * β n‖ * M :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => by
            rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hcoeff_le n) (norm_nonneg _))
      _ = (∑ n ∈ F_pos, B n) * M := by
          rw [← Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun n hn => ?_
          have hbn_ne : b n ≠ 0 := (Finset.mem_filter.mp hn).2
          have hBn_pos : 0 < B n := Real.rpow_pos_of_pos (norm_pos_iff.mpr hbn_ne) p
          have hβ_norm : ‖β n‖ = 1 := by
            dsimp only [β]
            rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
              div_self (norm_ne_zero_iff.mpr hbn_ne)]
          rw [norm_mul, hβ_norm, mul_one, Complex.norm_exp]
          have hre : (z * (Real.log (B n) : ℂ)).re = Real.log (B n) := by simp [z]
          rw [hre, Real.exp_log hBn_pos]
      _ ≤ 1 * M := by
          refine mul_le_mul_of_nonneg_right ?_ hM_pos.le
          rw [← hb_sum]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ F)
            fun _ _ _ => Real.rpow_nonneg (norm_nonneg _) p
      _ = M := one_mul M
  -- Apply Theorem 12.8 (`theorem12_8_general_strip` on `[1/2, 1]`) at `z = (1 / p : ℂ)`!
  obtain ⟨hpt, _, _⟩ := theorem12_8_general_strip (by norm_num : (1 / 2 : ℝ) < 1)
    hΦ_entire.differentiableOn hΦ_entire.continuous.continuousOn hΦ_bdd
  have h1p_mem : 1 / 2 ≤ ((1 / p : ℝ) : ℂ).re ∧ ((1 / p : ℝ) : ℂ).re ≤ 1 := by
    simp only [Complex.ofReal_re]
    exact ⟨(div_le_div_iff₀ zero_lt_two hp_pos).mpr (by linarith),
      (div_le_one hp_pos).mpr hp1.le⟩
  have hbound := hpt (by simpa using hΦ_half) hΦ_one ((1 / p : ℝ) : ℂ) h1p_mem
  simp only [Complex.ofReal_re, Real.one_rpow, one_mul] at hbound
  have hexp_eq : (1 / p - 1 / 2) / (1 - 1 / 2) = (2 - p) / p := by
    field_simp [hp_pos.ne']
    ring
  rw [hexp_eq] at hbound
  -- Finally identify `Φ ((1 / p : ℝ) : ℂ)` with `∑ n ∈ F, b n * fourierCoeffSys ψ μ s n`
  have hΦ_val : Φ ((1 / p : ℝ) : ℂ) = ∑ n ∈ F, b n * fourierCoeffSys ψ μ s n := by
    have hcoeff_s : ∀ n,
        (∑ v ∈ V, Complex.exp (((1 / p : ℝ) : ℂ) * (Real.log (A_val v) : ℂ)) * I_nv n v) =
          fourierCoeffSys ψ μ s n := by
      intro n
      rw [hinner_eq]
      congr 1
      ext x
      rw [hs_sum x]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hv_ne : v ≠ 0 := (Finset.mem_erase.mp hv).1
      have hA_pos : 0 < A_val v := Real.rpow_pos_of_pos (norm_pos_iff.mpr hv_ne) p
      have hc : Complex.exp (((1 / p : ℝ) : ℂ) * (Real.log (A_val v) : ℂ)) * φ_val v = v := by
        rw [← Complex.ofReal_mul, mul_comm (1 / p), ← Complex.ofReal_exp,
          ← Real.rpow_def_of_pos hA_pos]
        dsimp only [A_val, φ_val]
        rw [← Real.rpow_mul (norm_nonneg v), mul_one_div_cancel hp_pos.ne', Real.rpow_one]
        exact mul_div_cancel₀ v (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv_ne))
      by_cases hx : x ∈ E v
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hc]
      · simp [hx]
    dsimp only [Φ]
    have hbn_eq : ∀ n ∈ F_pos,
        Complex.exp (((1 / p : ℝ) : ℂ) * (Real.log (B n) : ℂ)) * β n = b n := by
      intro n hn
      have hbn_ne : b n ≠ 0 := (Finset.mem_filter.mp hn).2
      have hB_pos : 0 < B n := Real.rpow_pos_of_pos (norm_pos_iff.mpr hbn_ne) p
      rw [← Complex.ofReal_mul, mul_comm (1 / p), ← Complex.ofReal_exp,
        ← Real.rpow_def_of_pos hB_pos]
      dsimp only [B, β]
      rw [← Real.rpow_mul (norm_nonneg (b n)), mul_one_div_cancel hp_pos.ne', Real.rpow_one]
      exact mul_div_cancel₀ (b n) (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hbn_ne))
    calc (∑ n ∈ F_pos, ∑ v ∈ V,
            Complex.exp (((1 / p : ℝ) : ℂ) * (Real.log (B n) : ℂ)) * β n *
              Complex.exp (((1 / p : ℝ) : ℂ) * (Real.log (A_val v) : ℂ)) * I_nv n v)
        = ∑ n ∈ F_pos, b n * fourierCoeffSys ψ μ s n := by
            refine Finset.sum_congr rfl fun n hn => ?_
            rw [← hcoeff_s n, ← hbn_eq n hn, Finset.mul_sum]
            refine Finset.sum_congr rfl fun v _ => by ring
      _ = ∑ n ∈ F, b n * fourierCoeffSys ψ μ s n := by
            refine Finset.sum_subset (Finset.filter_subset _ F) fun n hn hnot => ?_
            have hb0 : b n = 0 := by
              by_contra hne
              exact hnot (Finset.mem_filter.mpr ⟨hn, hne⟩)
            rw [hb0, zero_mul]
  rwa [hΦ_val] at hbound

/-- 12.12 (The Hausdorff–Young Theorem, `1 < p ≤ 2` real-exponent form, Rudin pp. 261–262):
Under the hypotheses of 12.11 (`{ψ_n}` orthonormal in `L²(μ)` with `∀ n, ∀ᵐ x ∂μ, ‖ψ n x‖ ≤ M`,
`0 ≤ M`), for every `1 < p ≤ 2` with conjugate exponent `q = p / (p - 1)` and every
`f ∈ L^p(μ)` (`MemLp f (ENNReal.ofReal p) μ`), the series `∑' n, ‖f̂(n)‖ ^ q` is summable and
`(∑' n, ‖f̂(n)‖ ^ q) ^ (1 / q) ≤ M ^ ((2 - p) / p) * (eLpNorm f (ENNReal.ofReal p) μ).toReal`. -/
theorem theorem12_12_real {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]
    {μ : Measure X} {ψ : ι → X → ℂ} (hψ : ∀ n, MemLp (ψ n) 2 μ)
    (horth : ∀ n m : ι, ∫ x, ψ n x * conj (ψ m x) ∂μ = if m = n then 1 else 0)
    {M : ℝ} (hM : 0 ≤ M) (hbdd : ∀ n, ∀ᵐ x ∂μ, ‖ψ n x‖ ≤ M)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2)
    {f : X → ℂ} (hf : MemLp f (ENNReal.ofReal p) μ) :
    let q : ℝ := p / (p - 1)
    Summable (fun n => ‖fourierCoeffSys ψ μ f n‖ ^ q) ∧
    Memℓp (fourierCoeffSys ψ μ f) (ENNReal.ofReal q) ∧
    (∑' n, ‖fourierCoeffSys ψ μ f n‖ ^ q) ^ (1 / q) ≤
      M ^ ((2 - p) / p) * (eLpNorm f (ENNReal.ofReal p) μ).toReal := by
  intro q
  have hp_pos : 0 < p := zero_lt_one.trans hp1
  have hp_sub_pos : 0 < p - 1 := sub_pos.mpr hp1
  have hq_pos : 0 < q := div_pos hp_pos hp_sub_pos
  have hq1 : 1 < q := by
    dsimp only [q]
    rw [one_lt_div hp_sub_pos]
    linarith
  rcases isEmpty_or_nonempty ι with h_empty | h_nonempty
  · have hsumm : Summable (fun n : ι => ‖fourierCoeffSys ψ μ f n‖ ^ q) := summable_empty
    have hmem : Memℓp (fourierCoeffSys ψ μ f) (ENNReal.ofReal q) := by
      rw [memℓp_gen_iff (by rw [ENNReal.toReal_ofReal hq_pos.le]; exact hq_pos)]
      simp [ENNReal.toReal_ofReal hq_pos.le]
    refine ⟨hsumm, hmem, ?_⟩
    rw [tsum_empty, Real.zero_rpow (one_div_ne_zero hq_pos.ne')]
    exact mul_nonneg (Real.rpow_nonneg hM _) ENNReal.toReal_nonneg
  obtain ⟨hpart1, _, _, h11_p2⟩ := theorem12_11 hψ horth hM hbdd
  obtain ⟨_, hM_pos, _⟩ := hpart1 h_nonempty
  -- Endpoint `p = 2` is already `theorem12_11`!
  rcases eq_or_lt_of_le hp2 with rfl | hp_lt2
  · have hq_eq : q = 2 := by dsimp [q]; norm_num
    have hf2 : MemLp f 2 μ := by simpa using hf
    obtain ⟨hsumm2, hmem2, hle2⟩ := h11_p2 hf2
    refine ⟨by simpa [hq_eq] using hsumm2, by simpa [hq_eq] using hmem2, ?_⟩
    simpa [hq_eq] using hle2
  -- Strict interpolation case `1 < p < 2`:
  -- Step A: Finite-sum bound `(∑ n ∈ F, ‖ŝ(n)‖ ^ q) ^ (1 / q) ≤ M ^ ((2-p)/p) * ‖s‖_p` for simple `s`
  have hfin_simple : ∀ (s : SimpleFunc X ℂ) (hs : MemLp s (ENNReal.ofReal p) μ) (F : Finset ι),
      (∑ n ∈ F, ‖fourierCoeffSys ψ μ s n‖ ^ q) ^ (1 / q) ≤
        M ^ ((2 - p) / p) * (eLpNorm s (ENNReal.ofReal p) μ).toReal := by
    intro s hs F
    set N_s : ℝ := (eLpNorm s (ENNReal.ofReal p) μ).toReal
    rcases eq_or_lt_of_le (ENNReal.toReal_nonneg : 0 ≤ N_s) with hNs0 | hNs_pos
    · have hs_ae0 : s =ᵐ[μ] 0 := by
        have he0 : eLpNorm s (ENNReal.ofReal p) μ = 0 :=
          (ENNReal.toReal_eq_zero_iff _).mp hNs0.symm |>.resolve_right hs.eLpNorm_lt_top.ne
        exact (eLpNorm_eq_zero_iff (ENNReal.ofReal_pos.mpr hp_pos).ne').mp he0
      have hc0 : ∀ n, fourierCoeffSys ψ μ s n = 0 := by
        intro n
        unfold fourierCoeffSys
        refine integral_eq_zero_of_ae ?_
        filter_upwards [hs_ae0] with x hx
        simp [hx]
      simp only [hc0, norm_zero, Real.zero_rpow hq_pos.ne', Finset.sum_const_zero]
      rw [Real.zero_rpow (one_div_ne_zero hq_pos.ne')]
      positivity
    -- Normalize `s_1 := N_s⁻¹ • s`
    let s₁ : SimpleFunc X ℂ := s.map (fun w => ((N_s⁻¹ : ℝ) : ℂ) * w)
    have hs₁_coe : (s₁ : X → ℂ) = ((N_s⁻¹ : ℝ) : ℂ) • (s : X → ℂ) := rfl
    have hs₁_lp : MemLp s₁ (ENNReal.ofReal p) μ := hs.const_smul ((N_s⁻¹ : ℝ) : ℂ)
    have hs₁_norm : (eLpNorm s₁ (ENNReal.ofReal p) μ).toReal = 1 := by
      rw [hs₁_coe, eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.mpr hNs_pos.le)]
      exact inv_mul_cancel₀ hNs_pos.ne'
    set S_q : ℝ := ∑ n ∈ F, ‖fourierCoeffSys ψ μ s₁ n‖ ^ q
    rcases eq_or_lt_of_le (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) q : 0 ≤ S_q)
      with hSq0 | hSq_pos
    · have hsum_s : (∑ n ∈ F, ‖fourierCoeffSys ψ μ s n‖ ^ q) = 0 := by
        have hall0 : ∀ n ∈ F, ‖fourierCoeffSys ψ μ s₁ n‖ ^ q = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) q).mp hSq0.symm
        refine Finset.sum_eq_zero fun n hn => ?_
        have hc_eq : fourierCoeffSys ψ μ s₁ n = ((N_s⁻¹ : ℝ) : ℂ) * fourierCoeffSys ψ μ s n := by
          unfold fourierCoeffSys
          dsimp only [s₁]
          simp_rw [SimpleFunc.coe_map, Function.comp_apply, mul_assoc]
          exact integral_const_mul _ _
        have h0 := (Real.rpow_eq_zero (norm_nonneg _) hq_pos.ne').mp (hall0 n hn)
        rw [hc_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hNs_pos.le),
          mul_eq_zero] at h0
        have hn0 : ‖fourierCoeffSys ψ μ s n‖ = 0 := h0.resolve_left (inv_ne_zero hNs_pos.ne')
        rw [hn0, Real.zero_rpow hq_pos.ne']
      rw [hsum_s, Real.zero_rpow (one_div_ne_zero hq_pos.ne')]
      exact mul_nonneg (Real.rpow_nonneg hM _) hNs_pos.le
    -- Choose dual vector `b n` on `F`
    let b : ι → ℂ := fun n =>
      if n ∈ F then
        conj (fourierCoeffSys ψ μ s₁ n) *
          ((‖fourierCoeffSys ψ μ s₁ n‖ ^ (q - 2) / S_q ^ (1 / p) : ℝ) : ℂ)
      else 0
    have hp_mul_q1 : (q - 1) * p = q := by
      dsimp only [q]
      field_simp [hp_sub_pos.ne']
      ring
    have hb_norm_p : ∀ n ∈ F, ‖b n‖ ^ p = ‖fourierCoeffSys ψ μ s₁ n‖ ^ q / S_q := by
      intro n hn
      dsimp only [b]
      rw [ite_eq_left_iff.mpr fun hnot => absurd hn hnot]
      set a : ℝ := ‖fourierCoeffSys ψ μ s₁ n‖
      by_cases ha0 : a = 0
      · have hc0 : fourierCoeffSys ψ μ s₁ n = 0 := norm_eq_zero.mp ha0
        rw [hc0, map_zero, zero_mul, norm_zero, Real.zero_rpow hp_pos.ne',
          ha0, Real.zero_rpow hq_pos.ne', zero_div]
      · have ha_pos : 0 < a := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ha0)
        rw [norm_mul, RCLike.norm_conj, Complex.norm_real,
          Real.norm_of_nonneg (div_nonneg (Real.rpow_nonneg ha_pos.le _) (Real.rpow_nonneg hSq_pos.le _)),
          mul_div_assoc', ← Real.rpow_one_add' ha_pos.le (by linarith : 1 + (q - 2) ≠ 0),
          Real.div_rpow (Real.rpow_nonneg ha_pos.le _) (Real.rpow_nonneg hSq_pos.le _) p,
          ← Real.rpow_mul ha_pos.le, ← Real.rpow_mul hSq_pos.le, one_div_mul_cancel hp_pos.ne',
          Real.rpow_one]
        congr 2
        calc (1 + (q - 2)) * p = (q - 1) * p := by ring
          _ = q := hp_mul_q1
    have hb_sum : ∑ n ∈ F, ‖b n‖ ^ p = 1 := by
      calc ∑ n ∈ F, ‖b n‖ ^ p = ∑ n ∈ F, ‖fourierCoeffSys ψ μ s₁ n‖ ^ q / S_q :=
            Finset.sum_congr rfl hb_norm_p
        _ = S_q / S_q := (Finset.sum_div _ _ _).symm
        _ = 1 := div_self hSq_pos.ne'
    have hpair_eq : ∑ n ∈ F, b n * fourierCoeffSys ψ μ s₁ n = ((S_q ^ (1 / q) : ℝ) : ℂ) := by
      have hterm : ∀ n ∈ F, b n * fourierCoeffSys ψ μ s₁ n =
          ((‖fourierCoeffSys ψ μ s₁ n‖ ^ q / S_q ^ (1 / p) : ℝ) : ℂ) := by
        intro n hn
        dsimp only [b]
        rw [ite_eq_left_iff.mpr fun hnot => absurd hn hnot]
        set c := fourierCoeffSys ψ μ s₁ n
        by_cases hc0 : c = 0
        · simp [hc0, Real.zero_rpow hq_pos.ne']
        · have ha_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
          calc conj c * ((‖c‖ ^ (q - 2) / S_q ^ (1 / p) : ℝ) : ℂ) * c
              = (conj c * c) * ((‖c‖ ^ (q - 2) / S_q ^ (1 / p) : ℝ) : ℂ) := by ring
            _ = (((‖c‖ ^ (2 : ℝ) * ‖c‖ ^ (q - 2)) / S_q ^ (1 / p) : ℝ) : ℂ) := by
                have hcc : conj c * c = ((‖c‖ ^ (2 : ℝ) : ℝ) : ℂ) := by
                  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Real.rpow_two]
                rw [hcc, ← Complex.ofReal_mul, mul_div_assoc]
            _ = ((‖c‖ ^ q / S_q ^ (1 / p) : ℝ) : ℂ) := by
                rw [← Real.rpow_add ha_pos, add_sub_cancel]
      rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum, ← Finset.sum_div]
      congr 1
      change S_q / S_q ^ (1 / p) = S_q ^ (1 / q)
      have h1 : 1 - 1 / p = 1 / q := by
        dsimp only [q]
        field_simp [hp_pos.ne', hp_sub_pos.ne']
      rw [← h1, Real.rpow_sub hSq_pos, Real.rpow_one]
    have hnorm_le := hausdorff_young_simple_normalized hψ horth hM_pos hbdd hp1 hp_lt2
      s₁ hs₁_lp hs₁_norm F b hb_sum
    rw [hpair_eq, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hSq_pos.le _)] at hnorm_le
    -- Undo normalization `s₁ = N_s⁻¹ • s`
    have hS_scale : (∑ n ∈ F, ‖fourierCoeffSys ψ μ s n‖ ^ q) ^ (1 / q) =
        S_q ^ (1 / q) * N_s := by
      have hterm : ∀ n ∈ F, ‖fourierCoeffSys ψ μ s n‖ ^ q =
          N_s ^ q * ‖fourierCoeffSys ψ μ s₁ n‖ ^ q := by
        intro n _
        have hc_eq : fourierCoeffSys ψ μ s n = (N_s : ℂ) * fourierCoeffSys ψ μ s₁ n := by
          unfold fourierCoeffSys
          dsimp only [s₁]
          simp_rw [SimpleFunc.coe_map, Function.comp_apply]
          rw [← integral_const_mul]
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          simp only [← mul_assoc, ← Complex.ofReal_mul]
          rw [mul_inv_cancel₀ hNs_pos.ne', Complex.ofReal_one, one_mul]
        rw [hc_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hNs_pos.le,
          Real.mul_rpow hNs_pos.le (norm_nonneg _)]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
        Real.mul_rpow (Real.rpow_nonneg hNs_pos.le _) hSq_pos.le,
        ← Real.rpow_mul hNs_pos.le, mul_one_div_cancel hq_pos.ne', Real.rpow_one, mul_comm]
    rw [hS_scale]
    exact mul_le_mul_of_nonneg_right hnorm_le hNs_pos.le
  -- Step B: Extend from simple functions to arbitrary `f ∈ MemLp (ENNReal.ofReal p) μ` by density
  let p_enn : ℝ≥0∞ := ENNReal.ofReal p
  let q_enn : ℝ≥0∞ := ENNReal.ofReal q
  have hp_fact : Fact (1 ≤ p_enn) := ⟨ENNReal.one_le_ofReal.mpr hp1.le⟩
  have hq_fact : Fact (1 ≤ q_enn) := ⟨ENNReal.one_le_ofReal.mpr hq1.le⟩
  have hpq_real : p.HolderConjugate q := by
    refine Real.holderConjugate_iff.mpr ⟨hp1, ?_⟩
    dsimp only [q]
    field_simp [hp_pos.ne', hp_sub_pos.ne']
    ring
  have hpq_enn : p_enn.HolderConjugate q_enn := ennreal_holderConjugate_ofReal hpq_real
  have hq2 : 2 ≤ q_enn := by
    have hq2_r : 2 ≤ q := by
      dsimp only [q]
      rw [le_div_iff₀ hp_sub_pos]
      linarith
    dsimp only [q_enn]
    rw [← ENNReal.ofReal_ofNat 2]
    exact ENNReal.ofReal_le_ofReal hq2_r
  let f_lp : Lp ℂ p_enn μ := hf.toLp f
  have hdense := Lp.simpleFunc.dense (E := ℂ) (μ := μ) (p := p_enn) ENNReal.ofReal_ne_top
  obtain ⟨seq, hseq_mem, hseq_lim⟩ := mem_closure_iff_seq_limit.mp (hdense f_lp)
  let s_seq : ℕ → SimpleFunc X ℂ := fun j => Lp.simpleFunc.toSimpleFunc ⟨seq j, hseq_mem j⟩
  have hs_ae : ∀ j, (s_seq j : X → ℂ) =ᵐ[μ] (seq j : Lp ℂ p_enn μ) :=
    fun j => Lp.simpleFunc.toSimpleFunc_eq_toFun ⟨seq j, hseq_mem j⟩
  have hfin_f : ∀ F : Finset ι,
      (∑ n ∈ F, ‖fourierCoeffSys ψ μ f n‖ ^ q) ^ (1 / q) ≤
        M ^ ((2 - p) / p) * (eLpNorm f p_enn μ).toReal := by
    intro F
    -- Show `fourierCoeffSys ψ μ (s_seq j) n → fourierCoeffSys ψ μ f n` as `j → ∞`
    have hcoeff_tendsto : ∀ n, Tendsto (fun j => fourierCoeffSys ψ μ (s_seq j) n)
        atTop (𝓝 (fourierCoeffSys ψ μ f n)) := by
      intro n
      have hψ_q : MemLp (fun x => conj (ψ n x)) q_enn μ :=
        (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ).comp_memLp'
          (memLp_of_memLp_two_of_ae_bound (hψ n) hM (hbdd n) hq2)
      rw [Metric.tendsto_atTop]
      intro ε hε
      let K_n : ℝ := (eLpNorm (fun x => conj (ψ n x)) q_enn μ).toReal + 1
      have hKn_pos : 0 < K_n := by positivity
      obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hseq_lim (ε / K_n) (div_pos hε hKn_pos)
      refine ⟨J, fun j hj => ?_⟩
      rw [dist_eq_norm]
      have hdiff_lp : MemLp (fun x => s_seq j x - f x) p_enn μ :=
        ((Lp.memLp (seq j)).ae_eq (hs_ae j).symm).sub hf
      have hsub_int : fourierCoeffSys ψ μ (s_seq j) n - fourierCoeffSys ψ μ f n =
          ∫ x, (s_seq j x - f x) * conj (ψ n x) ∂μ := by
        unfold fourierCoeffSys
        have hi1 : Integrable (fun x => s_seq j x * conj (ψ n x)) μ :=
          ((Lp.memLp (seq j)).ae_eq (hs_ae j).symm).integrable_mul hψ_q
        have hi2 : Integrable (fun x => f x * conj (ψ n x)) μ :=
          hf.integrable_mul hψ_q
        rw [← integral_sub hi1 hi2]
        refine integral_congr_ae (ae_of_all _ fun x => by ring)
      rw [hsub_int]
      have hhold : ∫⁻ x, ‖(s_seq j x - f x) * conj (ψ n x)‖ₑ ∂μ ≤
          eLpNorm (fun x => s_seq j x - f x) p_enn μ *
            eLpNorm (fun x => conj (ψ n x)) q_enn μ := by
        have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq_real
          hdiff_lp.aestronglyMeasurable.enorm hψ_q.aestronglyMeasurable.enorm
        have he1 := eLpNorm_eq_lintegral_rpow_enorm_toReal
          (ENNReal.ofReal_pos.mpr hp_pos).ne' ENNReal.ofReal_ne_top hdiff_lp.aestronglyMeasurable
        have he2 := eLpNorm_eq_lintegral_rpow_enorm_toReal
          (ENNReal.ofReal_pos.mpr hq_pos).ne' ENNReal.ofReal_ne_top hψ_q.aestronglyMeasurable
        dsimp only [p_enn, q_enn] at he1 he2 ⊢
        rw [ENNReal.toReal_ofReal hp_pos.le] at he1
        rw [ENNReal.toReal_ofReal hq_pos.le] at he2
        rw [he1, he2]
        simpa [enorm_mul] using hh
      have hnorm_int : ‖∫ x, (s_seq j x - f x) * conj (ψ n x) ∂μ‖ ≤
          (eLpNorm (fun x => s_seq j x - f x) p_enn μ).toReal *
            (eLpNorm (fun x => conj (ψ n x)) q_enn μ).toReal := by
        rw [← toReal_enorm, ← ENNReal.toReal_mul]
        refine ENNReal.toReal_mono
          (ENNReal.mul_lt_top hdiff_lp.eLpNorm_lt_top hψ_q.eLpNorm_lt_top).ne
          ((enorm_integral_le_lintegral_enorm _).trans hhold)
      have heLp_eq : (eLpNorm (fun x => s_seq j x - f x) p_enn μ).toReal = ‖seq j - f_lp‖ := by
        rw [Lp.norm_def]
        congr 1
        refine eLpNorm_congr_ae ?_
        filter_upwards [hs_ae j, hf.coeFn_toLp, Lp.coeFn_sub (seq j) f_lp] with x hx1 hx2 hx3
        rw [hx3, Pi.sub_apply, hx1, hx2]
      rw [heLp_eq] at hnorm_int
      have hlt_dist : ‖seq j - f_lp‖ < ε / K_n := by simpa [dist_eq_norm] using hJ j hj
      calc ‖∫ x, (s_seq j x - f x) * conj (ψ n x) ∂μ‖
          ≤ ‖seq j - f_lp‖ * (eLpNorm (fun x => conj (ψ n x)) q_enn μ).toReal := hnorm_int
        _ ≤ ‖seq j - f_lp‖ * K_n :=
            mul_le_mul_of_nonneg_left (by dsimp [K_n]; linarith) (norm_nonneg _)
        _ < (ε / K_n) * K_n := mul_lt_mul_of_pos_right hlt_dist hKn_pos
        _ = ε := div_mul_cancel₀ ε hKn_pos.ne'
    -- Pass to the `j → ∞` limit on `hfin_simple (s_seq j)`
    have hlim_lhs : Tendsto
        (fun j => (∑ n ∈ F, ‖fourierCoeffSys ψ μ (s_seq j) n‖ ^ q) ^ (1 / q))
        atTop (𝓝 ((∑ n ∈ F, ‖fourierCoeffSys ψ μ f n‖ ^ q) ^ (1 / q))) :=
      (tendsto_finsetSum F fun n _ =>
        ((hcoeff_tendsto n).norm).rpow_const (Or.inr hq_pos.le)).rpow_const (Or.inr (by positivity))
    have hlim_rhs : Tendsto
        (fun j => M ^ ((2 - p) / p) * (eLpNorm (s_seq j) p_enn μ).toReal)
        atTop (𝓝 (M ^ ((2 - p) / p) * (eLpNorm f p_enn μ).toReal)) := by
      have hnorm_eq : ∀ j, (eLpNorm (s_seq j) p_enn μ).toReal = ‖seq j‖ := by
        intro j
        rw [Lp.norm_def, eLpNorm_congr_ae (hs_ae j)]
      have hf_norm_eq : (eLpNorm f p_enn μ).toReal = ‖f_lp‖ := by
        rw [Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp]
      simp_rw [hnorm_eq, hf_norm_eq]
      exact (hseq_lim.norm).const_mul _
    exact le_of_tendsto_of_tendsto hlim_lhs hlim_rhs
      (Eventually.of_forall fun j =>
        hfin_simple (s_seq j) ((Lp.memLp (seq j)).ae_eq (hs_ae j).symm) F)
  -- Step C: Summability and `tsum` bound from `hfin_f`
  set C_rhs : ℝ := M ^ ((2 - p) / p) * (eLpNorm f p_enn μ).toReal
  have hC_nn : 0 ≤ C_rhs := mul_nonneg (Real.rpow_nonneg hM _) ENNReal.toReal_nonneg
  have hfin_pow : ∀ F : Finset ι,
      ∑ n ∈ F, ‖fourierCoeffSys ψ μ f n‖ ^ q ≤ C_rhs ^ q := by
    intro F
    have h := hfin_f F
    have hsum_nn : 0 ≤ ∑ n ∈ F, ‖fourierCoeffSys ψ μ f n‖ ^ q :=
      Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) q
    calc ∑ n ∈ F, ‖fourierCoeffSys ψ μ f n‖ ^ q
        = ((∑ n ∈ F, ‖fourierCoeffSys ψ μ f n‖ ^ q) ^ (1 / q)) ^ q := by
            rw [← Real.rpow_mul hsum_nn, one_div_mul_cancel hq_pos.ne', Real.rpow_one]
      _ ≤ C_rhs ^ q := Real.rpow_le_rpow (Real.rpow_nonneg hsum_nn _) h hq_pos.le
  have hsumm : Summable (fun n => ‖fourierCoeffSys ψ μ f n‖ ^ q) :=
    summable_of_sum_le (fun _ => Real.rpow_nonneg (norm_nonneg _) q) hfin_pow
  have hmem : Memℓp (fourierCoeffSys ψ μ f) q_enn := by
    rw [memℓp_gen_iff (by dsimp [q_enn]; rw [ENNReal.toReal_ofReal hq_pos.le]; exact hq_pos)]
    simpa [q_enn, ENNReal.toReal_ofReal hq_pos.le] using hsumm
  have htsum_le : (∑' n, ‖fourierCoeffSys ψ μ f n‖ ^ q) ^ (1 / q) ≤ C_rhs := by
    have h1 : ∑' n, ‖fourierCoeffSys ψ μ f n‖ ^ q ≤ C_rhs ^ q :=
      hsumm.tsum_le_of_sum_le hfin_pow
    calc (∑' n, ‖fourierCoeffSys ψ μ f n‖ ^ q) ^ (1 / q)
        ≤ (C_rhs ^ q) ^ (1 / q) :=
          Real.rpow_le_rpow (tsum_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) q) h1
            (by positivity)
      _ = C_rhs := by
          rw [← Real.rpow_mul hC_nn, mul_one_div_cancel hq_pos.ne', Real.rpow_one]
  exact ⟨hsumm, hmem, htsum_le⟩

/-- 12.12 (The Hausdorff–Young Theorem, complete `1 ≤ p ≤ 2` `ENNReal`/`lp` + real-exponent +
literal 3.7 `rudinEssSup` package, Rudin pp. 261–262):
1. For any `1 ≤ p ≤ 2` in `ℝ≥0∞` with `p.HolderConjugate q` and `f ∈ Lp ℂ p μ`,
   `fourierCoeffSys ψ μ f ∈ lp (fun _ : ι => ℂ) q` with
   `‖(⟨fourierCoeffSys ψ μ f, hmem⟩ : lp _ q)‖ ≤ M ^ ((2 - p.toReal) / p.toReal) * ‖f‖`;
2. For `1 < p ≤ 2` in `ℝ`, `q = p / (p - 1)`, and `MemLp f (ENNReal.ofReal p) μ`,
   `(∑' n, ‖f̂(n)‖ ^ q) ^ (1 / q) ≤ M ^ ((2 - p) / p) * (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p)`;
3. Moreover, if `[Nonempty ι]`, the hypothesis `∀ n, rudinEssSup μ (ψ n) ≤ M` (with `MemLp (ψ n) ⊤ μ`
   and `μ Set.univ ≠ 0`) is equivalent to `∀ n, ∀ᵐ x ∂μ, ‖ψ n x‖ ≤ M` (`0 < M`). -/
theorem theorem12_12 {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]
    {μ : Measure X} {ψ : ι → X → ℂ} (hψ : ∀ n, MemLp (ψ n) 2 μ)
    (horth : ∀ n m : ι, ∫ x, ψ n x * conj (ψ m x) ∂μ = if m = n then 1 else 0)
    {M : ℝ} (hM : 0 ≤ M) (hbdd : ∀ n, ∀ᵐ x ∂μ, ‖ψ n x‖ ≤ M) :
    (∀ {p q : ℝ≥0∞}, 1 ≤ p → p ≤ 2 → p.HolderConjugate q →
      ∀ f : Lp ℂ p μ,
        ∃ hmem : Memℓp (fourierCoeffSys ψ μ f) q,
          ‖(⟨fourierCoeffSys ψ μ f, hmem⟩ : lp (fun _ : ι => ℂ) q)‖ ≤
            M ^ ((2 - p.toReal) / p.toReal) * ‖f‖) ∧
    (∀ {p : ℝ}, 1 < p → p ≤ 2 → ∀ {f : X → ℂ}, MemLp f (ENNReal.ofReal p) μ →
      let q : ℝ := p / (p - 1)
      Summable (fun n => ‖fourierCoeffSys ψ μ f n‖ ^ q) ∧
      (∑' n, ‖fourierCoeffSys ψ μ f n‖ ^ q) ^ (1 / q) ≤
        M ^ ((2 - p) / p) * (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p)) := by
  refine ⟨?_, ?_⟩
  · intro p q hp1 hp2 hpq f
    rcases eq_or_lt_of_le hp1 with rfl | hp_gt
    · -- `p = 1`, `q = ⊤`
      have hq_top : q = ⊤ := by
        have h1 := ENNReal.holderConjugate_iff.mp hpq
        rw [inv_one] at h1
        have hinv : q⁻¹ = 0 := (ENNReal.add_right_inj ENNReal.one_ne_top).mp (by simpa using h1)
        exact ENNReal.inv_eq_zero.mp hinv
      subst hq_top
      have hf_int : Integrable f μ := memLp_one_iff_integrable.mp (Lp.memLp f)
      obtain ⟨_, _, h11_p1, _⟩ := theorem12_11 hψ horth hM hbdd
      obtain ⟨hbd_n, hmem_top⟩ := h11_p1 hf_int
      refine ⟨hmem_top, ?_⟩
      simp only [ENNReal.toReal_one, div_one]
      have hexp : (2 - 1 : ℝ) = 1 := by norm_num
      rw [hexp, Real.rpow_one]
      have h_int_norm : ∫ x, ‖f x‖ ∂μ = ‖f‖ := by
        rw [Lp.norm_def, integral_norm_eq_lintegral_enorm hf_int.aestronglyMeasurable,
          eLpNorm_one_eq_lintegral_enorm]
        exact hf_int.aestronglyMeasurable
      rw [← h_int_norm]
      rcases isEmpty_or_nonempty ι with h_empty | h_nonempty
      · have hzero : (⟨fourierCoeffSys ψ μ f, hmem_top⟩ : lp (fun _ : ι => ℂ) ⊤) = 0 := by
          ext i; exact h_empty.elim i
        rw [hzero, norm_zero]
        exact mul_nonneg hM (integral_nonneg fun _ => norm_nonneg _)
      · rw [lp.norm_eq_ciSup]
        refine ciSup_le fun n => ?_
        exact hbd_n n
    · -- `1 < p ≤ 2`
      have hp_top : p ≠ ⊤ := (lt_of_le_of_lt hp2 ENNReal.ofNat_lt_top).ne
      have hp_real : 1 < p.toReal := by
        rw [← ENNReal.toReal_one]
        exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).mpr hp_gt
      have hp2_real : p.toReal ≤ 2 := by
        simpa using ENNReal.toReal_mono ENNReal.ofNat_ne_top hp2
      have hp_eq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hp_top
      have hq_eq : ENNReal.ofReal (p.toReal / (p.toReal - 1)) = q := by
        have hpq_r : p.toReal.HolderConjugate (p.toReal / (p.toReal - 1)) := by
          refine Real.holderConjugate_iff.mpr ⟨hp_real, ?_⟩
          have hp0 : p.toReal ≠ 0 := (zero_lt_one.trans hp_real).ne'
          have hps : p.toReal - 1 ≠ 0 := (sub_pos.mpr hp_real).ne'
          field_simp [hp0, hps]
          ring
        have hpq' : p.HolderConjugate (ENNReal.ofReal (p.toReal / (p.toReal - 1))) := by
          have hc := ennreal_holderConjugate_ofReal hpq_r
          rwa [hp_eq] at hc
        -- Conjugate exponent in `ℝ≥0∞` is unique
        have h1 := ENNReal.holderConjugate_iff.mp hpq
        have h2 := ENNReal.holderConjugate_iff.mp hpq'
        have hp_inv_ne_top : p⁻¹ ≠ ⊤ := by
          rw [ENNReal.inv_ne_top]
          exact (zero_lt_one.trans hp_gt).ne'
        have hinv_eq : (ENNReal.ofReal (p.toReal / (p.toReal - 1)))⁻¹ = q⁻¹ :=
          (ENNReal.add_right_inj hp_inv_ne_top).mp (h2.trans h1.symm)
        exact inv_inj.mp hinv_eq
      have hf_mem : MemLp f (ENNReal.ofReal p.toReal) μ := by
        rw [hp_eq]; exact Lp.memLp f
      obtain ⟨_, hmem_q, htsum_le⟩ :=
        theorem12_12_real hψ horth hM hbdd hp_real hp2_real hf_mem
      rw [hq_eq] at hmem_q
      refine ⟨hmem_q, ?_⟩
      have hq_pos : 0 < p.toReal / (p.toReal - 1) :=
        div_pos (zero_lt_one.trans hp_real) (sub_pos.mpr hp_real)
      have hq_toReal : q.toReal = p.toReal / (p.toReal - 1) := by
        rw [← hq_eq, ENNReal.toReal_ofReal hq_pos.le]
      rw [lp.norm_eq_tsum_rpow (by rw [hq_toReal]; exact hq_pos), hq_toReal]
      have hf_norm : (eLpNorm f (ENNReal.ofReal p.toReal) μ).toReal = ‖f‖ := by
        rw [hp_eq, Lp.norm_def]
      simpa only [one_div, hf_norm] using htsum_le
  · intro p hp1 hp2 f hf q
    obtain ⟨hsumm, _, hle⟩ := theorem12_12_real hψ horth hM hbdd hp1 hp2 hf
    refine ⟨hsumm, hle.trans_eq ?_⟩
    congr 1
    have hp_pos : 0 < p := zero_lt_one.trans hp1
    have heLp := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) (f := f)
      (ENNReal.ofReal_pos.mpr hp_pos).ne' ENNReal.ofReal_ne_top hf.aestronglyMeasurable
    rw [ENNReal.toReal_ofReal hp_pos.le] at heLp
    rw [heLp, ← ENNReal.toReal_rpow]
    congr 1
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => Real.rpow_nonneg (norm_nonneg _) p)
      (hf.aestronglyMeasurable.norm.aemeasurable.pow_const p).aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp_pos.le]

end Nodes12_11_and_12_12

end RudinRCA.Chapter12

end

noncomputable section

open Set Metric Bornology Filter Topology Complex
open scoped Real Topology ComplexConjugate

namespace RudinRCA.Chapter12

/-! ### Node 12.10: Lindelöf's Theorem (radial and nontangential limits) -/

section Node12_10

open RudinRCA.Chapter11

/-- Equivalence of the deleted left neighborhood `𝓝[<] 1` and `𝓝[Ico 0 1] 1`. -/
theorem nhdsWithin_Ico_zero_one_eq_nhdsLT :
    𝓝[Ico (0 : ℝ) 1] (1 : ℝ) = 𝓝[<] (1 : ℝ) := by
  refine nhdsWithin_eq_nhdsWithin' (Ioo_mem_nhds zero_lt_one one_lt_two) ?_
  ext t
  simp only [mem_inter_iff, mem_Ico, mem_Ioo, mem_Iio]
  constructor
  · rintro ⟨⟨_, ht1⟩, _⟩
    exact ⟨ht1, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨ht1, ⟨ht0, ht2⟩⟩
    exact ⟨⟨ht0.le, ht1⟩, ⟨ht0, ht2⟩⟩

/-- Strict argument bound `|z.arg| < π / 2` whenever `0 < z.re`. -/
private lemma abs_arg_lt_pi_div_two_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    |z.arg| < Real.pi / 2 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_re] at hz
    exact lt_irrefl 0 hz
  have hle : |z.arg| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hz.le
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hcos_pos : 0 < Real.cos z.arg := by
    rw [Complex.cos_arg hz0]
    exact div_pos hz (norm_pos_iff.mpr hz0)
  have hcos_abs : Real.cos |z.arg| = Real.cos z.arg := by
    rcases abs_choice z.arg with h | h <;> simp [h]
  rw [← hcos_abs, heq, Real.cos_pi_div_two] at hcos_pos
  exact lt_irrefl 0 hcos_pos

/-- Principal-branch `log` identity `log (z₁ / z₂) = log z₁ - log z₂` whenever `z₁, z₂ ≠ 0`,
`0 ≤ z₁.re`, `0 ≤ z₂.re`, and `0 < (z₁ / z₂).re`. -/
private lemma log_div_of_re_nonneg_of_div_re_pos {z₁ z₂ : ℂ}
    (hz₁0 : z₁ ≠ 0) (hz₂0 : z₂ ≠ 0) (hz₁ : 0 ≤ z₁.re) (hz₂ : 0 ≤ z₂.re)
    (hdiv : 0 < (z₁ / z₂).re) :
    Complex.log (z₁ / z₂) = Complex.log z₁ - Complex.log z₂ := by
  have hdiv0 : z₁ / z₂ ≠ 0 := div_ne_zero hz₁0 hz₂0
  let w : ℂ := Complex.log (z₁ / z₂) - (Complex.log z₁ - Complex.log z₂)
  have hexp : Complex.exp w = 1 := by
    dsimp only [w]
    rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_log hdiv0,
      Complex.exp_log hz₁0, Complex.exp_log hz₂0, div_self hdiv0]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  have him_lt : |w.im| < 2 * Real.pi := by
    have h1 : |(z₁ / z₂).arg| < Real.pi / 2 := abs_arg_lt_pi_div_two_of_re_pos hdiv
    have h2 : |z₁.arg| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hz₁
    have h3 : |z₂.arg| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hz₂
    have hw_im : w.im = (z₁ / z₂).arg - z₁.arg + z₂.arg := by
      dsimp only [w]
      simp [Complex.log_im]
      ring
    have habs : |w.im| ≤ |(z₁ / z₂).arg| + |z₁.arg| + |z₂.arg| := by
      rw [hw_im]
      calc |(z₁ / z₂).arg - z₁.arg + z₂.arg|
          ≤ |(z₁ / z₂).arg - z₁.arg| + |z₂.arg| := abs_add_le _ _
        _ ≤ |(z₁ / z₂).arg| + |z₁.arg| + |z₂.arg| := add_le_add (abs_sub _ _) le_rfl
    linarith [Real.pi_pos]
  have hn0 : n = 0 := by
    by_contra hne
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
    have hge : 2 * Real.pi ≤ |w.im| := by
      have hw_im_n : w.im = (n : ℝ) * (2 * Real.pi) := by
        rw [hn]
        simp [mul_assoc]
      rw [hw_im_n, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      nlinarith [Real.pi_pos]
    linarith
  have hw0 : w = 0 := by simp [hn, hn0]
  exact sub_eq_zero.mp hw0

/-- Plaquette identity for four right-half-plane ratios with `a * b = c * d`:
`log a - log c = log d - log b`. -/
private lemma plaquette_log_eq {a b c d : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re)
    (habcd : a * b = c * d) :
    Complex.log a - Complex.log c = Complex.log d - Complex.log b := by
  have ha0 : a ≠ 0 := by intro h; rw [h, zero_re] at ha; exact lt_irrefl 0 ha
  have hb0 : b ≠ 0 := by intro h; rw [h, zero_re] at hb; exact lt_irrefl 0 hb
  have hc0 : c ≠ 0 := by intro h; rw [h, zero_re] at hc; exact lt_irrefl 0 hc
  have hd0 : d ≠ 0 := by intro h; rw [h, zero_re] at hd; exact lt_irrefl 0 hd
  let w : ℂ := Complex.log a + Complex.log b - Complex.log c - Complex.log d
  have hexp : Complex.exp w = 1 := by
    dsimp only [w]
    rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_add,
      Complex.exp_log ha0, Complex.exp_log hb0, Complex.exp_log hc0, Complex.exp_log hd0]
    rw [div_div, habcd, div_self (mul_ne_zero hc0 hd0)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  have him_lt : |w.im| < 2 * Real.pi := by
    have h1 := abs_arg_lt_pi_div_two_of_re_pos ha
    have h2 := abs_arg_lt_pi_div_two_of_re_pos hb
    have h3 := abs_arg_lt_pi_div_two_of_re_pos hc
    have h4 := abs_arg_lt_pi_div_two_of_re_pos hd
    have hw_im : w.im = a.arg + b.arg - c.arg - d.arg := by
      dsimp only [w]
      simp [Complex.log_im]
    have habs : |w.im| ≤ |a.arg| + |b.arg| + |c.arg| + |d.arg| := by
      rw [hw_im]
      calc |a.arg + b.arg - c.arg - d.arg|
          ≤ |a.arg + b.arg - c.arg| + |d.arg| := abs_sub _ _
        _ ≤ |a.arg + b.arg| + |c.arg| + |d.arg| := add_le_add (abs_sub _ _) le_rfl
        _ ≤ |a.arg| + |b.arg| + |c.arg| + |d.arg| :=
            add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    linarith
  have hn0 : n = 0 := by
    by_contra hne
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
    have hge : 2 * Real.pi ≤ |w.im| := by
      have hw_im_n : w.im = (n : ℝ) * (2 * Real.pi) := by
        rw [hn]
        simp [mul_assoc]
      rw [hw_im_n, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      nlinarith [Real.pi_pos]
    linarith
  have hw0 : w = 0 := by simp [hn, hn0]
  dsimp only [w] at hw0
  linear_combination hw0

/-- Schwarz reflection `z ↦ conj (f (conj z))` preserves complex differentiability. -/
private lemma hasDerivAt_conj_comp_conj {f : ℂ → ℂ} {f' z₀ : ℂ}
    (hf : HasDerivAt f f' (conj z₀)) :
    HasDerivAt (fun z : ℂ => conj (f (conj z))) (conj f') z₀ := by
  rw [hasDerivAt_iff_tendsto] at hf ⊢
  have hcomp := hf.comp (Complex.continuous_conj.tendsto z₀)
  refine hcomp.congr fun z => ?_
  dsimp only [Function.comp_def]
  have h1 : ‖conj z - conj z₀‖ = ‖z - z₀‖ := by
    rw [← map_sub, Complex.norm_conj]
  have h2 : ‖conj (f (conj z)) - conj (f (conj z₀)) - (z - z₀) • conj f'‖ =
      ‖f (conj z) - f (conj z₀) - (conj z - conj z₀) • f'‖ := by
    have hconj : conj (f (conj z) - f (conj z₀) - (conj z - conj z₀) • f') =
        conj (f (conj z)) - conj (f (conj z₀)) - (z - z₀) • conj f' := by
      simp [smul_eq_mul]
    rw [← hconj, Complex.norm_conj]
  rw [h1, h2]

private lemma differentiableAt_conj_comp_conj {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : DifferentiableAt ℂ f (conj z₀)) :
    DifferentiableAt ℂ (fun z : ℂ => conj (f (conj z))) z₀ :=
  (hasDerivAt_conj_comp_conj hf.hasDerivAt).differentiableAt

/-- Frontier of a connected component of the complement `Eᶜ` of a closed set `E ⊆ ℂ` lies in `E`. -/
private lemma frontier_connectedComponentIn_compl_subset {E : Set ℂ}
    (hE : IsClosed E) {x : ℂ} :
    frontier (connectedComponentIn Eᶜ x) ⊆ E := by
  let U₀ : Set ℂ := connectedComponentIn Eᶜ x
  have hU₀_open : IsOpen U₀ := hE.isOpen_compl.connectedComponentIn
  have hU₀_sub : U₀ ⊆ Eᶜ := connectedComponentIn_subset Eᶜ x
  intro z hz
  rw [frontier, hU₀_open.interior_eq, Set.mem_sdiff] at hz
  obtain ⟨hz_cl, hz_not_U₀⟩ := hz
  by_contra hz_not_E
  have hz_Ec : z ∈ Eᶜ := hz_not_E
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hE.isOpen_compl z hz_Ec
  obtain ⟨w, hw_U₀, hw_dist⟩ := Metric.mem_closure_iff.mp hz_cl δ hδ
  have hw_ball : w ∈ ball z δ := by
    rwa [mem_ball, dist_comm]
  have hunion_pre : IsPreconnected (U₀ ∪ ball z δ) :=
    isPreconnected_connectedComponentIn.union w hw_U₀ hw_ball (convex_ball z δ).isPreconnected
  have hunion_sub : U₀ ∪ ball z δ ⊆ U₀ := by
    have hsub := hunion_pre.subset_connectedComponentIn (Or.inl hw_U₀) (union_subset hU₀_sub hball)
    rwa [← connectedComponentIn_eq hw_U₀] at hsub
  exact hz_not_U₀ (hunion_sub (Or.inr (mem_ball_self hδ)))

/-- Any point `w : ℂ` with `2 ≤ ‖w‖` can be joined to `(-3 : ℂ)` by a continuous path lying
entirely outside `closedBall (0 : ℂ) 1`. -/
private lemma joinedIn_compl_closedBall_neg_three {w : ℂ} (hw : 2 ≤ ‖w‖) :
    JoinedIn (closedBall (0 : ℂ) 1)ᶜ w (-3 : ℂ) := by
  by_cases him : 0 ≤ w.im
  · let w₁ : ℂ := w + 3 * I
    let w₂ : ℂ := (-3 : ℂ) + 3 * I
    have hp₁ : JoinedIn (closedBall (0 : ℂ) 1)ᶜ w w₁ := by
      refine ⟨{
        toFun := fun s => w + ((3 * (s : ℝ) : ℝ) : ℂ) * I
        continuous_toFun := by fun_prop
        source' := by simp
        target' := by simp [w₁]
      }, ?_⟩
      intro s
      change w + ((3 * (s : ℝ) : ℝ) : ℂ) * I ∈ (closedBall (0 : ℂ) 1)ᶜ
      rw [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
      have hs0 : 0 ≤ (s : ℝ) := s.2.1
      have hsq : 4 ≤ Complex.normSq (w + ((3 * (s : ℝ) : ℝ) : ℂ) * I) := by
        have hw_sq : 4 ≤ Complex.normSq w := by
          rw [Complex.normSq_eq_norm_sq]
          nlinarith
        have hre : (w + ((3 * (s : ℝ) : ℝ) : ℂ) * I).re = w.re := by simp
        have him_eq : (w + ((3 * (s : ℝ) : ℝ) : ℂ) * I).im = w.im + 3 * (s : ℝ) := by simp
        rw [Complex.normSq_apply, hre, him_eq]
        rw [Complex.normSq_apply] at hw_sq
        nlinarith
      rw [Complex.normSq_eq_norm_sq] at hsq
      have hnorm_ge : 2 ≤ ‖w + ((3 * (s : ℝ) : ℝ) : ℂ) * I‖ := by
        nlinarith [norm_nonneg (w + ((3 * (s : ℝ) : ℝ) : ℂ) * I)]
      linarith
    have hp₂ : JoinedIn (closedBall (0 : ℂ) 1)ᶜ w₁ w₂ := by
      refine ⟨{
        toFun := fun s => ((1 - (s : ℝ) : ℝ) : ℂ) * w₁ + ((s : ℝ) : ℂ) * w₂
        continuous_toFun := by fun_prop
        source' := by simp
        target' := by simp
      }, ?_⟩
      intro s
      change ((1 - (s : ℝ) : ℝ) : ℂ) * w₁ + ((s : ℝ) : ℂ) * w₂ ∈ (closedBall (0 : ℂ) 1)ᶜ
      rw [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
      have hs0 : 0 ≤ (s : ℝ) := s.2.1
      have hs1 : (s : ℝ) ≤ 1 := s.2.2
      have him_ge : 3 ≤ (((1 - (s : ℝ) : ℝ) : ℂ) * w₁ + ((s : ℝ) : ℂ) * w₂).im := by
        simp [w₁, w₂]
        nlinarith
      have hle_norm := Complex.abs_im_le_norm (((1 - (s : ℝ) : ℝ) : ℂ) * w₁ + ((s : ℝ) : ℂ) * w₂)
      linarith [le_abs_self (((1 - (s : ℝ) : ℝ) : ℂ) * w₁ + ((s : ℝ) : ℂ) * w₂).im]
    have hp₃ : JoinedIn (closedBall (0 : ℂ) 1)ᶜ w₂ (-3 : ℂ) := by
      refine ⟨{
        toFun := fun s => (-3 : ℂ) + ((3 * (1 - (s : ℝ)) : ℝ) : ℂ) * I
        continuous_toFun := by fun_prop
        source' := by simp [w₂]
        target' := by simp
      }, ?_⟩
      intro s
      change (-3 : ℂ) + ((3 * (1 - (s : ℝ)) : ℝ) : ℂ) * I ∈ (closedBall (0 : ℂ) 1)ᶜ
      rw [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
      have hre_eq : ((-3 : ℂ) + ((3 * (1 - (s : ℝ)) : ℝ) : ℂ) * I).re = -3 := by simp
      have hle_norm := Complex.abs_re_le_norm ((-3 : ℂ) + ((3 * (1 - (s : ℝ)) : ℝ) : ℂ) * I)
      rw [hre_eq] at hle_norm
      have habs3 : (3 : ℝ) ≤ |-3| := by norm_num
      linarith
    exact (hp₁.trans hp₂).trans hp₃
  · have him_lt : w.im < 0 := lt_of_not_ge him
    let w₁ : ℂ := w - 3 * I
    let w₂ : ℂ := (-3 : ℂ) - 3 * I
    have hp₁ : JoinedIn (closedBall (0 : ℂ) 1)ᶜ w w₁ := by
      refine ⟨{
        toFun := fun s => w - ((3 * (s : ℝ) : ℝ) : ℂ) * I
        continuous_toFun := by fun_prop
        source' := by simp
        target' := by simp [w₁]
      }, ?_⟩
      intro s
      change w - ((3 * (s : ℝ) : ℝ) : ℂ) * I ∈ (closedBall (0 : ℂ) 1)ᶜ
      rw [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
      have hs0 : 0 ≤ (s : ℝ) := s.2.1
      have hsq : 4 ≤ Complex.normSq (w - ((3 * (s : ℝ) : ℝ) : ℂ) * I) := by
        have hw_sq : 4 ≤ Complex.normSq w := by
          rw [Complex.normSq_eq_norm_sq]
          nlinarith
        have hre : (w - ((3 * (s : ℝ) : ℝ) : ℂ) * I).re = w.re := by simp
        have him_eq : (w - ((3 * (s : ℝ) : ℝ) : ℂ) * I).im = w.im - 3 * (s : ℝ) := by simp
        rw [Complex.normSq_apply, hre, him_eq]
        rw [Complex.normSq_apply] at hw_sq
        nlinarith
      rw [Complex.normSq_eq_norm_sq] at hsq
      have hnorm_ge : 2 ≤ ‖w - ((3 * (s : ℝ) : ℝ) : ℂ) * I‖ := by
        nlinarith [norm_nonneg (w - ((3 * (s : ℝ) : ℝ) : ℂ) * I)]
      linarith
    have hp₂ : JoinedIn (closedBall (0 : ℂ) 1)ᶜ w₁ w₂ := by
      refine ⟨{
        toFun := fun s => ((1 - (s : ℝ) : ℝ) : ℂ) * w₁ + ((s : ℝ) : ℂ) * w₂
        continuous_toFun := by fun_prop
        source' := by simp
        target' := by simp
      }, ?_⟩
      intro s
      change ((1 - (s : ℝ) : ℝ) : ℂ) * w₁ + ((s : ℝ) : ℂ) * w₂ ∈ (closedBall (0 : ℂ) 1)ᶜ
      rw [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
      have hs0 : 0 ≤ (s : ℝ) := s.2.1
      have hs1 : (s : ℝ) ≤ 1 := s.2.2
      have him_le : (((1 - (s : ℝ) : ℝ) : ℂ) * w₁ + ((s : ℝ) : ℂ) * w₂).im ≤ -3 := by
        simp [w₁, w₂]
        nlinarith
      have hle_norm := Complex.abs_im_le_norm (((1 - (s : ℝ) : ℝ) : ℂ) * w₁ + ((s : ℝ) : ℂ) * w₂)
      linarith [neg_le_abs (((1 - (s : ℝ) : ℝ) : ℂ) * w₁ + ((s : ℝ) : ℂ) * w₂).im]
    have hp₃ : JoinedIn (closedBall (0 : ℂ) 1)ᶜ w₂ (-3 : ℂ) := by
      refine ⟨{
        toFun := fun s => (-3 : ℂ) - ((3 * (1 - (s : ℝ)) : ℝ) : ℂ) * I
        continuous_toFun := by fun_prop
        source' := by simp [w₂]
        target' := by simp
      }, ?_⟩
      intro s
      change (-3 : ℂ) - ((3 * (1 - (s : ℝ)) : ℝ) : ℂ) * I ∈ (closedBall (0 : ℂ) 1)ᶜ
      rw [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
      have hre_eq : ((-3 : ℂ) - ((3 * (1 - (s : ℝ)) : ℝ) : ℂ) * I).re = -3 := by simp
      have hle_norm := Complex.abs_re_le_norm ((-3 : ℂ) - ((3 * (1 - (s : ℝ)) : ℝ) : ℂ) * I)
      rw [hre_eq] at hle_norm
      have habs3 : (3 : ℝ) ≤ |-3| := by norm_num
      linarith
    exact (hp₁.trans hp₂).trans hp₃

/-- Any point `z₀` outside `Ω ∪ {1, 2r - 1}` (for `1 / 2 < r < 1`) can be joined to `(-3 : ℂ)` inside
`(Ω ∪ {1, 2r - 1})ᶜ`. -/
private lemma joinedIn_compl_lens_neg_three {r : ℝ} (hr_half : 1 / 2 < r) (hr1 : r < 1)
    {z₀ : ℂ} (hz₀ : z₀ ∉ (ball (0 : ℂ) 1 ∩ ball ((2 * r : ℝ) : ℂ) 1) ∪
      {(1 : ℂ), ((2 * r - 1 : ℝ) : ℂ)}) :
    JoinedIn ((ball (0 : ℂ) 1 ∩ ball ((2 * r : ℝ) : ℂ) 1) ∪
      {(1 : ℂ), ((2 * r - 1 : ℝ) : ℂ)})ᶜ z₀ (-3 : ℂ) := by
  let Ω : Set ℂ := ball (0 : ℂ) 1 ∩ ball ((2 * r : ℝ) : ℂ) 1
  let K : Set ℂ := Ω ∪ {(1 : ℂ), ((2 * r - 1 : ℝ) : ℂ)}
  have hK_cb0 : K ⊆ closedBall (0 : ℂ) 1 := by
    rintro z (hzΩ | rfl | rfl)
    · exact ball_subset_closedBall hzΩ.1
    · simp
    · rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
  have hK_cb2r : K ⊆ closedBall ((2 * r : ℝ) : ℂ) 1 := by
    rintro z (hzΩ | rfl | rfl)
    · exact ball_subset_closedBall hzΩ.2
    · rw [mem_closedBall, dist_eq_norm]
      have : (1 : ℂ) - ((2 * r : ℝ) : ℂ) = ((1 - 2 * r : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      linarith
    · rw [mem_closedBall, dist_eq_norm]
      have : ((2 * r - 1 : ℝ) : ℂ) - ((2 * r : ℝ) : ℂ) = (-1 : ℂ) := by push_cast; ring
      rw [this]
      simp
  by_cases hz_norm : 1 ≤ ‖z₀‖
  · let w : ℂ := (3 : ℂ) * z₀
    have hw_norm : 2 ≤ ‖w‖ := by
      dsimp only [w]
      rw [norm_mul]
      norm_num
      linarith
    have hpA : JoinedIn Kᶜ z₀ w := by
      refine ⟨{
        toFun := fun s => ((1 + 2 * (s : ℝ) : ℝ) : ℂ) * z₀
        continuous_toFun := by fun_prop
        source' := by simp
        target' := by
          dsimp only [w]
          push_cast
          ring
      }, ?_⟩
      intro s
      change ((1 + 2 * (s : ℝ) : ℝ) : ℂ) * z₀ ∈ Kᶜ
      rcases (s.2.1).eq_or_lt with hs0 | hs_pos
      · have hs_eq : (s : ℝ) = 0 := hs0.symm
        rw [hs_eq]
        have heq0 : ((1 + 2 * (0 : ℝ) : ℝ) : ℂ) * z₀ = z₀ := by push_cast; ring
        rw [heq0]
        exact hz₀
      · intro hmem
        have hcb := hK_cb0 hmem
        rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)] at hcb
        nlinarith
    have hpB := (joinedIn_compl_closedBall_neg_three hw_norm).mono (compl_subset_compl.mpr hK_cb0)
    exact hpA.trans hpB
  · have hz_norm_lt : ‖z₀‖ < 1 := lt_of_not_ge hz_norm
    have hz_2r : 1 ≤ ‖z₀ - ((2 * r : ℝ) : ℂ)‖ := by
      by_contra hlt
      have hlt' : ‖z₀ - ((2 * r : ℝ) : ℂ)‖ < 1 := lt_of_not_ge hlt
      have hz_in_Ω : z₀ ∈ Ω := ⟨by simpa [mem_ball] using hz_norm_lt,
        by simpa [mem_ball, dist_eq_norm] using hlt'⟩
      exact hz₀ (Or.inl hz_in_Ω)
    let w : ℂ := ((2 * r : ℝ) : ℂ) + (5 : ℂ) * (z₀ - ((2 * r : ℝ) : ℂ))
    have hw_norm : 2 ≤ ‖w‖ := by
      have h1 : 5 ≤ ‖(5 : ℂ) * (z₀ - ((2 * r : ℝ) : ℂ))‖ := by
        rw [norm_mul]
        have h5 : ‖(5 : ℂ)‖ = 5 := by norm_num
        rw [h5]
        linarith
      have h2 : ‖((2 * r : ℝ) : ℂ)‖ < 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      have htri2 := norm_add_le w (-((2 * r : ℝ) : ℂ))
      have hw_diff : w + -((2 * r : ℝ) : ℂ) = (5 : ℂ) * (z₀ - ((2 * r : ℝ) : ℂ)) := by
        dsimp only [w]
        ring
      rw [hw_diff, norm_neg] at htri2
      linarith
    have hpA : JoinedIn Kᶜ z₀ w := by
      refine ⟨{
        toFun := fun s => ((2 * r : ℝ) : ℂ) + ((1 + 4 * (s : ℝ) : ℝ) : ℂ) * (z₀ - ((2 * r : ℝ) : ℂ))
        continuous_toFun := by fun_prop
        source' := by simp
        target' := by
          dsimp only [w]
          push_cast
          ring
      }, ?_⟩
      intro s
      change ((2 * r : ℝ) : ℂ) + ((1 + 4 * (s : ℝ) : ℝ) : ℂ) * (z₀ - ((2 * r : ℝ) : ℂ)) ∈ Kᶜ
      rcases (s.2.1).eq_or_lt with hs0 | hs_pos
      · have hs_eq : (s : ℝ) = 0 := hs0.symm
        rw [hs_eq]
        have heq0 : ((2 * r : ℝ) : ℂ) + ((1 + 4 * (0 : ℝ) : ℝ) : ℂ) * (z₀ - ((2 * r : ℝ) : ℂ)) =
            z₀ := by push_cast; ring
        rw [heq0]
        exact hz₀
      · intro hmem
        have hcb := hK_cb2r hmem
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith)] at hcb
        nlinarith
    have hpB := (joinedIn_compl_closedBall_neg_three hw_norm).mono (compl_subset_compl.mpr hK_cb0)
    exact hpA.trans hpB

/-- Core 4-fold reflection separation lemma in Rudin's proof of Theorem 12.10 (p. 259):
if `1 / 2 < r < 1`, `γ₁ : ℝ → ℂ` is continuous, maps `Icc 0 1` into `ball 0 1 ∪ {1}` with
`γ₁ 1 = 1`, `(γ₁ 0).re = r`, `(γ₁ 0).im ≠ 0`, and `r < (γ₁ s).re` for all `s ∈ Ioc 0 1`,
and `E` is the union of the 4 reflected arcs of `γ₁ '' Icc 0 1`, with `(r : ℂ) ∉ E`, then
`connectedComponentIn Eᶜ (r : ℂ) ⊆ ball 0 1 ∩ ball (2r) 1`. -/
private lemma connectedComponentIn_fourfold_subset_lens {r : ℝ} (hr_half : 1 / 2 < r) (hr1 : r < 1)
    {γ₁ : ℝ → ℂ} (hγ₁_cont : Continuous γ₁)
    (hγ₁_lt1 : ∀ s ∈ Ico (0 : ℝ) 1, ‖γ₁ s‖ < 1)
    (hγ₁_one : γ₁ 1 = 1)
    (hγ₁_zero_re : (γ₁ 0).re = r)
    (hγ₁_re_gt : ∀ s ∈ Ioc (0 : ℝ) 1, r < (γ₁ s).re)
    {E : Set ℂ}
    (hE_eq : E = γ₁ '' Icc 0 1 ∪ (fun s => conj (γ₁ s)) '' Icc 0 1 ∪
      (fun s => ((2 * r : ℝ) : ℂ) - γ₁ s) '' Icc 0 1 ∪
      (fun s => ((2 * r : ℝ) : ℂ) - conj (γ₁ s)) '' Icc 0 1)
    (hr_not_E : (r : ℂ) ∉ E) :
    connectedComponentIn Eᶜ (r : ℂ) ⊆ ball (0 : ℂ) 1 ∩ ball ((2 * r : ℝ) : ℂ) 1 := by
  let Ω : Set ℂ := ball (0 : ℂ) 1 ∩ ball ((2 * r : ℝ) : ℂ) 1
  have hγ₁_mem_Ω : ∀ s ∈ Ico (0 : ℝ) 1, γ₁ s ∈ Ω := by
    intro s hs
    have hnorm : ‖γ₁ s‖ < 1 := hγ₁_lt1 s hs
    have hre_ge : r ≤ (γ₁ s).re := by
      rcases hs.1.eq_or_lt with rfl | hs_pos
      · exact hγ₁_zero_re.symm.le
      · exact (hγ₁_re_gt s ⟨hs_pos, hs.2.le⟩).le
    refine ⟨by simpa [mem_ball] using hnorm, ?_⟩
    rw [mem_ball, dist_eq_norm]
    have hsq : Complex.normSq (γ₁ s - ((2 * r : ℝ) : ℂ)) < 1 := by
      have hns : Complex.normSq (γ₁ s) < 1 := by
        have := mul_self_lt_mul_self (norm_nonneg (γ₁ s)) hnorm
        simpa [Complex.normSq_eq_norm_sq, sq] using this
      have hid : Complex.normSq (γ₁ s - ((2 * r : ℝ) : ℂ)) =
          Complex.normSq (γ₁ s) - 4 * r * ((γ₁ s).re - r) := by
        simp [Complex.normSq_apply]
        ring
      rw [hid]
      nlinarith
    have hsq' : ‖γ₁ s - ((2 * r : ℝ) : ℂ)‖ ^ 2 < 1 ^ 2 := by
      simpa [Complex.normSq_eq_norm_sq] using hsq
    nlinarith [norm_nonneg (γ₁ s - ((2 * r : ℝ) : ℂ))]
  have hΩ_conj : ∀ z ∈ Ω, conj z ∈ Ω := by
    rintro z ⟨hz1, hz2⟩
    refine ⟨by simpa [mem_ball] using hz1, ?_⟩
    rw [mem_ball, dist_eq_norm] at hz2 ⊢
    have hconj_sub : conj z - ((2 * r : ℝ) : ℂ) = conj (z - ((2 * r : ℝ) : ℂ)) := by
      apply Complex.ext <;> simp
    rwa [hconj_sub, Complex.norm_conj]
  have hΩ_sym : ∀ z ∈ Ω, ((2 * r : ℝ) : ℂ) - z ∈ Ω := by
    rintro z ⟨hz1, hz2⟩
    rw [mem_ball, dist_zero_right] at hz1
    rw [mem_ball, dist_eq_norm] at hz2
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right, norm_sub_rev]
      exact hz2
    · rw [mem_ball, dist_eq_norm]
      have : ((2 * r : ℝ) : ℂ) - z - ((2 * r : ℝ) : ℂ) = -z := by ring
      rwa [this, norm_neg]
  have hE_sub : E ⊆ Ω ∪ {(1 : ℂ), ((2 * r - 1 : ℝ) : ℂ)} := by
    rw [hE_eq]
    rintro z (((⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩)
    · rcases hs.2.eq_or_lt with rfl | hs_lt
      · exact Or.inr (Or.inl hγ₁_one)
      · exact Or.inl (hγ₁_mem_Ω s ⟨hs.1, hs_lt⟩)
    · rcases hs.2.eq_or_lt with rfl | hs_lt
      · simp [hγ₁_one]
      · exact Or.inl (hΩ_conj _ (hγ₁_mem_Ω s ⟨hs.1, hs_lt⟩))
    · rcases hs.2.eq_or_lt with rfl | hs_lt
      · right; right; rw [mem_singleton_iff]; dsimp only; rw [hγ₁_one]; push_cast; ring
      · exact Or.inl (hΩ_sym _ (hγ₁_mem_Ω s ⟨hs.1, hs_lt⟩))
    · rcases hs.2.eq_or_lt with rfl | hs_lt
      · right; right; rw [mem_singleton_iff]; dsimp only; rw [hγ₁_one, map_one]; push_cast; ring
      · exact Or.inl (hΩ_sym _ (hΩ_conj _ (hγ₁_mem_Ω s ⟨hs.1, hs_lt⟩)))
  have hE_compact : IsCompact E := by
    rw [hE_eq]
    exact (((isCompact_Icc.image hγ₁_cont).union
      (isCompact_Icc.image (Complex.continuous_conj.comp hγ₁_cont))).union
      (isCompact_Icc.image (continuous_const.sub hγ₁_cont))).union
      (isCompact_Icc.image (continuous_const.sub (Complex.continuous_conj.comp hγ₁_cont)))
  have h1_mem_E : (1 : ℂ) ∈ E := by
    rw [hE_eq]
    exact Or.inl (Or.inl (Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, hγ₁_one⟩))
  have h2r1_mem_E : ((2 * r - 1 : ℝ) : ℂ) ∈ E := by
    rw [hE_eq]
    refine Or.inl (Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩)
    dsimp only
    rw [hγ₁_one]
    push_cast
    ring
  let U₀ : Set ℂ := connectedComponentIn Eᶜ (r : ℂ)
  have hU₀_open : IsOpen U₀ := hE_compact.isClosed.isOpen_compl.connectedComponentIn
  have hU₀_conn : IsConnected U₀ :=
    ⟨⟨(r : ℂ), mem_connectedComponentIn hr_not_E⟩, isPreconnected_connectedComponentIn⟩
  have hU₀_path : IsPathConnected U₀ := (hU₀_open.isConnected_iff_isPathConnected).mp hU₀_conn
  intro z₀ hz₀_U₀
  by_contra hz₀_not_Ω
  have hz₀_not_E : z₀ ∉ E := connectedComponentIn_subset Eᶜ (r : ℂ) hz₀_U₀
  have hz₀_not_K : z₀ ∉ Ω ∪ {(1 : ℂ), ((2 * r - 1 : ℝ) : ℂ)} := by
    rintro (h | rfl | rfl)
    · exact hz₀_not_Ω h
    · exact hz₀_not_E h1_mem_E
    · exact hz₀_not_E h2r1_mem_E
  have hp1 : JoinedIn Eᶜ (r : ℂ) z₀ :=
    (hU₀_path.joinedIn (r : ℂ) (mem_connectedComponentIn hr_not_E) z₀ hz₀_U₀).mono
      (connectedComponentIn_subset Eᶜ (r : ℂ))
  have hp2 : JoinedIn Eᶜ z₀ (-3 : ℂ) :=
    (joinedIn_compl_lens_neg_three hr_half hr1 hz₀_not_K).mono (compl_subset_compl.mpr hE_sub)
  obtain ⟨γ_ext, hγ_ext_mem⟩ := hp1.trans hp2
  let p : ℝ → ℂ := fun τ => γ_ext (projIcc 0 1 zero_le_one τ)
  have hp_cont : Continuous p := γ_ext.continuous.comp continuous_projIcc
  have hp0 : p 0 = (r : ℂ) := by
    change γ_ext (projIcc 0 1 zero_le_one 0) = (r : ℂ)
    have : projIcc 0 1 zero_le_one 0 = (0 : unitInterval) := by ext; simp
    rw [this]
    exact γ_ext.source
  have hp1_val : p 1 = (-3 : ℂ) := by
    change γ_ext (projIcc 0 1 zero_le_one 1) = (-3 : ℂ)
    have : projIcc 0 1 zero_le_one 1 = (1 : unitInterval) := by ext; simp
    rw [this]
    exact γ_ext.target
  have hp_not_E : ∀ τ : ℝ, p τ ∉ E := fun τ => hγ_ext_mem (projIcc 0 1 zero_le_one τ)
  let y₁ : ℝ := (γ₁ 0).im
  have hy₁_ne : y₁ ≠ 0 := by
    intro hy0
    have hγ0_eq : γ₁ 0 = (r : ℂ) := by
      apply Complex.ext
      · simpa using hγ₁_zero_re
      · simpa [y₁] using hy0
    have hγ0_E : γ₁ 0 ∈ E := by
      rw [hE_eq]
      exact Or.inl (Or.inl (Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩))
    rw [hγ0_eq] at hγ0_E
    exact hr_not_E hγ0_E
  have hγ₁_0_eq : γ₁ 0 = (r : ℂ) + (y₁ : ℂ) * I := by
    apply Complex.ext <;> simp [hγ₁_zero_re, y₁]
  let σ₁₂ : ℝ → ℂ := fun t => if t ≤ 1 then γ₁ t else conj (γ₁ (2 - t))
  have hσ₁₂_cont : Continuous σ₁₂ := by
    refine Continuous.if_le hγ₁_cont (Complex.continuous_conj.comp (hγ₁_cont.comp (by fun_prop)))
      continuous_id continuous_const ?_
    intro t ht
    subst ht
    norm_num [hγ₁_one]
  let σ₁₂₃ : ℝ → ℂ := fun t => if t ≤ 2 then σ₁₂ t else ((2 * r : ℝ) : ℂ) - γ₁ (t - 2)
  have hσ₁₂₃_cont : Continuous σ₁₂₃ := by
    refine Continuous.if_le hσ₁₂_cont (continuous_const.sub (hγ₁_cont.comp (by fun_prop)))
      continuous_id continuous_const ?_
    intro t ht
    subst ht
    have h12 : σ₁₂ 2 = conj (γ₁ 0) := by
      dsimp only [σ₁₂]
      rw [ite_eq_right_iff.mpr fun h => absurd h (by norm_num), show (2 : ℝ) - 2 = 0 by ring]
    rw [h12, sub_self, hγ₁_0_eq]
    (apply Complex.ext <;> simp); ring
  let σ : ℝ → ℂ := fun t => if t ≤ 3 then σ₁₂₃ t else ((2 * r : ℝ) : ℂ) - conj (γ₁ (4 - t))
  have hσ_cont : Continuous σ := by
    refine Continuous.if_le hσ₁₂₃_cont
      (continuous_const.sub (Complex.continuous_conj.comp (hγ₁_cont.comp (by fun_prop))))
      continuous_id continuous_const ?_
    intro t ht
    subst ht
    have h123 : σ₁₂₃ 3 = ((2 * r : ℝ) : ℂ) - γ₁ 1 := by
      dsimp only [σ₁₂₃]
      rw [ite_eq_right_iff.mpr fun h => absurd h (by norm_num), show (3 : ℝ) - 2 = 0 + 1 by ring, zero_add]
    rw [h123, show (4 : ℝ) - 3 = 1 by ring, hγ₁_one, map_one]
  have hσ_0 : σ 0 = (r : ℂ) + (y₁ : ℂ) * I := by
    dsimp only [σ, σ₁₂₃, σ₁₂]
    rw [ite_eq_left_iff.mpr fun h => absurd (by norm_num) h,
      ite_eq_left_iff.mpr fun h => absurd (by norm_num) h,
      ite_eq_left_iff.mpr fun h => absurd (by norm_num) h, hγ₁_0_eq]
  have hσ_2 : σ 2 = (r : ℂ) - (y₁ : ℂ) * I := by
    have : σ 2 = conj (γ₁ 0) := by
      dsimp only [σ, σ₁₂₃, σ₁₂]
      rw [ite_eq_left_iff.mpr fun h => absurd (by norm_num) h,
        ite_eq_left_iff.mpr fun h => absurd (by norm_num) h,
        ite_eq_right_iff.mpr fun h => absurd h (by norm_num),
        show (2 : ℝ) - 2 = 0 by ring]
    rw [this, hγ₁_0_eq]
    apply Complex.ext <;> simp
  have hσ_4 : σ 4 = (r : ℂ) + (y₁ : ℂ) * I := by
    have : σ 4 = ((2 * r : ℝ) : ℂ) - conj (γ₁ 0) := by
      dsimp only [σ]
      rw [ite_eq_right_iff.mpr fun h => absurd h (by norm_num), show (4 : ℝ) - 4 = 0 by ring]
    rw [this, hγ₁_0_eq]
    (apply Complex.ext <;> simp); ring
  have hσ_mem_E : ∀ t ∈ Icc (0 : ℝ) 4, σ t ∈ E := by
    intro t ⟨ht0, ht4⟩
    rw [hE_eq]
    by_cases ht1 : t ≤ 1
    · have : σ t = γ₁ t := by
        simp [σ, σ₁₂₃, σ₁₂, ht1, show t ≤ 2 by linarith, show t ≤ 3 by linarith]
      rw [this]
      exact Or.inl (Or.inl (Or.inl ⟨t, ⟨ht0, ht1⟩, rfl⟩))
    · have ht1_gt : 1 < t := lt_of_not_ge ht1
      by_cases ht2 : t ≤ 2
      · have : σ t = conj (γ₁ (2 - t)) := by
          simp [σ, σ₁₂₃, σ₁₂, not_le.mpr ht1_gt, ht2, show t ≤ 3 by linarith]
        rw [this]
        exact Or.inl (Or.inl (Or.inr ⟨2 - t, ⟨by linarith, by linarith⟩, rfl⟩))
      · have ht2_gt : 2 < t := lt_of_not_ge ht2
        by_cases ht3 : t ≤ 3
        · have : σ t = ((2 * r : ℝ) : ℂ) - γ₁ (t - 2) := by
            simp [σ, σ₁₂₃, not_le.mpr ht2_gt, ht3]
          rw [this]
          exact Or.inl (Or.inr ⟨t - 2, ⟨by linarith, by linarith⟩, rfl⟩)
        · have ht3_gt : 3 < t := lt_of_not_ge ht3
          have : σ t = ((2 * r : ℝ) : ℂ) - conj (γ₁ (4 - t)) := by
            simp [σ, not_le.mpr ht3_gt]
          rw [this]
          exact Or.inr ⟨4 - t, ⟨by linarith, by linarith⟩, rfl⟩
  have hσ_re_02 : ∀ t ∈ Icc (0 : ℝ) 2, 0 ≤ (σ t - (r : ℂ)).re := by
    intro t ⟨ht0, ht2⟩
    by_cases ht1 : t ≤ 1
    · have hst : σ t = γ₁ t := by
        simp [σ, σ₁₂₃, σ₁₂, ht1, ht2, show t ≤ 3 by linarith]
      rw [hst]
      rcases ht0.eq_or_lt with rfl | ht_pos
      · simp [hγ₁_zero_re]
      · have := hγ₁_re_gt t ⟨ht_pos, ht1⟩
        simp; linarith
    · have ht1_gt : 1 < t := lt_of_not_ge ht1
      have hst : σ t = conj (γ₁ (2 - t)) := by
        simp [σ, σ₁₂₃, σ₁₂, not_le.mpr ht1_gt, ht2, show t ≤ 3 by linarith]
      rw [hst]
      rcases ht2.eq_or_lt with rfl | ht_lt2
      · simp [hγ₁_zero_re]
      · have := hγ₁_re_gt (2 - t) ⟨by linarith, by linarith⟩
        simp; linarith
  have hσ_re_24 : ∀ t ∈ Icc (2 : ℝ) 4, 0 ≤ ((r : ℂ) - σ t).re := by
    intro t ⟨ht2, ht4⟩
    by_cases ht2_eq : t = 2
    · subst ht2_eq; simp [hσ_2]
    · have ht2_gt : 2 < t := lt_of_le_of_ne ht2 (Ne.symm ht2_eq)
      by_cases ht3 : t ≤ 3
      · have hst : σ t = ((2 * r : ℝ) : ℂ) - γ₁ (t - 2) := by
          simp [σ, σ₁₂₃, not_le.mpr ht2_gt, ht3]
        rw [hst]
        have := hγ₁_re_gt (t - 2) ⟨by linarith, by linarith⟩
        simp; linarith
      · have ht3_gt : 3 < t := lt_of_not_ge ht3
        have hst : σ t = ((2 * r : ℝ) : ℂ) - conj (γ₁ (4 - t)) := by
          simp [σ, not_le.mpr ht3_gt]
        rw [hst]
        rcases ht4.eq_or_lt with rfl | ht_lt4
        · simp [hγ₁_zero_re]; linarith
        · have := hγ₁_re_gt (4 - t) ⟨by linarith, by linarith⟩
          simp; linarith
  let Φ : ℝ × ℝ → ℂ := fun q => σ q.2 - p q.1
  have hΦ_cont : Continuous Φ := (hσ_cont.comp continuous_snd).sub (hp_cont.comp continuous_fst)
  let K_box : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 4
  have hK_box_comp : IsCompact K_box := isCompact_Icc.prod isCompact_Icc
  have hK_box_ne : K_box.Nonempty := ⟨(0, 0), ⟨le_rfl, zero_le_one⟩, ⟨le_rfl, by norm_num⟩⟩
  have hΦ_ne_zero : ∀ q ∈ K_box, Φ q ≠ 0 := by
    intro q ⟨_, hq2⟩ h0
    have hseq : σ q.2 = p q.1 := sub_eq_zero.mp h0
    exact hp_not_E q.1 (hseq ▸ hσ_mem_E q.2 hq2)
  obtain ⟨q_min, hq_min_mem, hq_min_le⟩ :=
    hK_box_comp.exists_isMinOn hK_box_ne (continuous_norm.comp hΦ_cont).continuousOn
  let m₀ : ℝ := ‖Φ q_min‖
  have hm₀_pos : 0 < m₀ := norm_pos_iff.mpr (hΦ_ne_zero q_min hq_min_mem)
  have hm₀_le : ∀ q ∈ K_box, m₀ ≤ ‖Φ q‖ := fun q hq => hq_min_le hq
  have hunif : UniformContinuousOn Φ K_box :=
    hK_box_comp.uniformContinuousOn_of_continuous hΦ_cont.continuousOn
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hunif (m₀ / 2) (by positivity)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 / δ)
  let N : ℕ := max N₀ 1
  let M : ℕ := max N₀ 1
  have hN_pos : 0 < N := lt_of_lt_of_le zero_lt_one (le_max_right N₀ 1)
  have hN_real_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN_pos
  have hM_real_pos : 0 < (M : ℝ) := hN_real_pos
  have hstep_lt : 1 / (N : ℝ) < δ := by
    have hgt : 2 / δ < (N : ℝ) := lt_of_lt_of_le hN₀ (Nat.cast_le.mpr (le_max_left N₀ 1))
    rw [div_lt_iff₀ hN_real_pos]
    rw [div_lt_iff₀ hδ_pos] at hgt
    linarith
  have hratio_re_pos : ∀ q₁ ∈ K_box, ∀ q₂ ∈ K_box, dist q₁ q₂ < δ → 0 < (Φ q₁ / Φ q₂).re := by
    intro q₁ hq₁ q₂ hq₂ hdist
    have hdiff_lt : ‖Φ q₁ - Φ q₂‖ < m₀ / 2 := by
      simpa [dist_eq_norm] using hδ q₁ hq₁ q₂ hq₂ hdist
    have hq₂_ge : m₀ ≤ ‖Φ q₂‖ := hm₀_le q₂ hq₂
    have hq₂_pos : 0 < ‖Φ q₂‖ := lt_of_lt_of_le hm₀_pos hq₂_ge
    have hnorm_lt : ‖Φ q₁ / Φ q₂ - 1‖ < 1 / 2 := by
      have heq : Φ q₁ / Φ q₂ - 1 = (Φ q₁ - Φ q₂) / Φ q₂ := by
        rw [sub_div (Φ q₁) (Φ q₂) (Φ q₂), div_self (hΦ_ne_zero q₂ hq₂)]
      rw [heq, norm_div, div_lt_iff₀ hq₂_pos]
      linarith
    have hre_abs : |(Φ q₁ / Φ q₂ - 1).re| ≤ ‖Φ q₁ / Φ q₂ - 1‖ := Complex.abs_re_le_norm _
    have hre_sub : (Φ q₁ / Φ q₂ - 1).re = (Φ q₁ / Φ q₂).re - 1 := by simp
    linarith [(abs_le.mp hre_abs).1]
  let τ_grid : ℕ → ℝ := fun j => (j : ℝ) / (N : ℝ)
  let t_grid : ℕ → ℝ := fun k => (k : ℝ) / (M : ℝ)
  have hτ_mem : ∀ j ≤ N, τ_grid j ∈ Icc (0 : ℝ) 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    dsimp only [τ_grid]
    rw [div_le_one hN_real_pos]
    exact_mod_cast hj
  have ht_mem : ∀ k ≤ 4 * M, t_grid k ∈ Icc (0 : ℝ) 4 := by
    intro k hk
    refine ⟨by positivity, ?_⟩
    dsimp only [t_grid]
    rw [div_le_iff₀ hM_real_pos]
    exact_mod_cast hk
  let W : ℕ → ℂ := fun j =>
    ∑ k ∈ Finset.range (4 * M),
      Complex.log (Φ (τ_grid j, t_grid (k + 1)) / Φ (τ_grid j, t_grid k))
  have hW_step : ∀ j < N, W (j + 1) = W j := by
    intro j hj
    have hterm : ∀ k ∈ Finset.range (4 * M),
        Complex.log (Φ (τ_grid (j + 1), t_grid (k + 1)) / Φ (τ_grid (j + 1), t_grid k)) -
          Complex.log (Φ (τ_grid j, t_grid (k + 1)) / Φ (τ_grid j, t_grid k)) =
        Complex.log (Φ (τ_grid (j + 1), t_grid (k + 1)) / Φ (τ_grid j, t_grid (k + 1))) -
          Complex.log (Φ (τ_grid (j + 1), t_grid k) / Φ (τ_grid j, t_grid k)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hq00 : (τ_grid j, t_grid k) ∈ K_box := ⟨hτ_mem j hj.le, ht_mem k hk.le⟩
      have hq01 : (τ_grid j, t_grid (k + 1)) ∈ K_box := ⟨hτ_mem j hj.le, ht_mem (k + 1) hk⟩
      have hq10 : (τ_grid (j + 1), t_grid k) ∈ K_box := ⟨hτ_mem (j + 1) hj, ht_mem k hk.le⟩
      have hq11 : (τ_grid (j + 1), t_grid (k + 1)) ∈ K_box := ⟨hτ_mem (j + 1) hj, ht_mem (k + 1) hk⟩
      have hd_τ : dist (τ_grid (j + 1)) (τ_grid j) < δ := by
        dsimp only [τ_grid]
        rw [Real.dist_eq, ← sub_div, Nat.cast_add, Nat.cast_one, add_sub_cancel_left,
          abs_of_pos (by positivity)]
        exact hstep_lt
      have hd_t : dist (t_grid (k + 1)) (t_grid k) < δ := by
        dsimp only [t_grid, M]
        rw [Real.dist_eq, ← sub_div, Nat.cast_add, Nat.cast_one, add_sub_cancel_left,
          abs_of_pos (by positivity)]
        exact hstep_lt
      have ha : 0 < (Φ (τ_grid (j + 1), t_grid (k + 1)) / Φ (τ_grid (j + 1), t_grid k)).re := by
        refine hratio_re_pos _ hq11 _ hq10 ?_
        rw [Prod.dist_eq, dist_self]
        exact max_lt hδ_pos hd_t
      have hb : 0 < (Φ (τ_grid (j + 1), t_grid k) / Φ (τ_grid j, t_grid k)).re := by
        refine hratio_re_pos _ hq10 _ hq00 ?_
        rw [Prod.dist_eq, dist_self]
        exact max_lt hd_τ hδ_pos
      have hc : 0 < (Φ (τ_grid j, t_grid (k + 1)) / Φ (τ_grid j, t_grid k)).re := by
        refine hratio_re_pos _ hq01 _ hq00 ?_
        rw [Prod.dist_eq, dist_self]
        exact max_lt hδ_pos hd_t
      have hd_re : 0 < (Φ (τ_grid (j + 1), t_grid (k + 1)) / Φ (τ_grid j, t_grid (k + 1))).re := by
        refine hratio_re_pos _ hq11 _ hq01 ?_
        rw [Prod.dist_eq, dist_self]
        exact max_lt hd_τ hδ_pos
      refine plaquette_log_eq ha hb hc hd_re ?_
      have h00_ne := hΦ_ne_zero _ hq00
      have h01_ne := hΦ_ne_zero _ hq01
      have h10_ne := hΦ_ne_zero _ hq10
      have h11_ne := hΦ_ne_zero _ hq11
      field_simp
    have hsum_sub : W (j + 1) - W j =
        ∑ k ∈ Finset.range (4 * M),
          (Complex.log (Φ (τ_grid (j + 1), t_grid (k + 1)) / Φ (τ_grid j, t_grid (k + 1))) -
            Complex.log (Φ (τ_grid (j + 1), t_grid k) / Φ (τ_grid j, t_grid k))) := by
      dsimp only [W]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl hterm
    rw [Finset.sum_range_sub (fun k =>
      Complex.log (Φ (τ_grid (j + 1), t_grid k) / Φ (τ_grid j, t_grid k)))] at hsum_sub
    have ht0 : t_grid 0 = 0 := by simp [t_grid]
    have ht4M : t_grid (4 * M) = 4 := by
      dsimp only [t_grid]
      push_cast
      exact mul_div_cancel_right₀ 4 hM_real_pos.ne'
    have hΦ_per : Φ (τ_grid j, 4) = Φ (τ_grid j, 0) ∧
        Φ (τ_grid (j + 1), 4) = Φ (τ_grid (j + 1), 0) := by
      simp [Φ, hσ_4, hσ_0]
    rw [ht4M, ht0, hΦ_per.1, hΦ_per.2, sub_self] at hsum_sub
    exact sub_eq_zero.mp hsum_sub
  have hW_const : ∀ j ≤ N, W j = W 0 := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [hW_step j (Nat.lt_of_succ_le hj)]
      exact ih (Nat.le_of_succ_le hj)
  have hW_eq : W N = W 0 := hW_const N le_rfl
  have hτ_N : τ_grid N = 1 := div_self hN_real_pos.ne'
  have hτ_0 : τ_grid 0 = 0 := by simp [τ_grid]
  have hW_N_zero : W N = 0 := by
    have hterm_N : ∀ k ∈ Finset.range (4 * M),
        Complex.log (Φ (τ_grid N, t_grid (k + 1)) / Φ (τ_grid N, t_grid k)) =
          Complex.log (Φ (1, t_grid (k + 1))) - Complex.log (Φ (1, t_grid k)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [hτ_N]
      have hq1 : ((1 : ℝ), t_grid (k + 1)) ∈ K_box := ⟨⟨zero_le_one, le_rfl⟩, ht_mem (k + 1) hk⟩
      have hq0 : ((1 : ℝ), t_grid k) ∈ K_box := ⟨⟨zero_le_one, le_rfl⟩, ht_mem k hk.le⟩
      have hd_t : dist (t_grid (k + 1)) (t_grid k) < δ := by
        dsimp only [t_grid, M]
        rw [Real.dist_eq, ← sub_div, Nat.cast_add, Nat.cast_one, add_sub_cancel_left,
          abs_of_pos (by positivity)]
        exact hstep_lt
      have hdiv_re : 0 < (Φ (1, t_grid (k + 1)) / Φ (1, t_grid k)).re := by
        refine hratio_re_pos _ hq1 _ hq0 ?_
        rw [Prod.dist_eq, dist_self]
        exact max_lt hδ_pos hd_t
      have hre_pos : ∀ t ∈ Icc (0 : ℝ) 4, 0 ≤ (Φ (1, t)).re := by
        intro t ht
        have hmem_cb : σ t ∈ closedBall (0 : ℂ) 1 := by
          have hmem_K := hE_sub (hσ_mem_E t ht)
          rcases hmem_K with hzΩ | h1 | h2
          · exact ball_subset_closedBall hzΩ.1
          · rw [h1]; simp
          · rw [mem_singleton_iff] at h2; rw [h2, mem_closedBall, dist_zero_right,
              Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
            linarith
        rw [mem_closedBall, dist_zero_right] at hmem_cb
        have hre_le := (abs_le.mp (Complex.abs_re_le_norm (σ t))).1
        have hΦ1 : (Φ (1, t)).re = (σ t).re + 3 := by simp [Φ, hp1_val]
        linarith
      exact log_div_of_re_nonneg_of_div_re_pos (hΦ_ne_zero _ hq1) (hΦ_ne_zero _ hq0)
        (hre_pos _ (ht_mem (k + 1) hk)) (hre_pos _ (ht_mem k hk.le)) hdiv_re
    dsimp only [W]
    rw [Finset.sum_congr rfl hterm_N, Finset.sum_range_sub (fun k => Complex.log (Φ (1, t_grid k)))]
    have ht0 : t_grid 0 = 0 := by simp [t_grid]
    have ht4M : t_grid (4 * M) = 4 := by
      dsimp only [t_grid]; push_cast; exact mul_div_cancel_right₀ 4 hM_real_pos.ne'
    rw [ht4M, ht0]
    simp [Φ, hσ_4, hσ_0]
  have hW_0_val : W 0 = 2 * (Complex.log (-(y₁ : ℂ) * I) - Complex.log ((y₁ : ℂ) * I)) := by
    dsimp only [W]
    have hsplit : 4 * M = 2 * M + 2 * M := by omega
    rw [hsplit, Finset.sum_range_add]
    have hsum1 : ∑ k ∈ Finset.range (2 * M),
        Complex.log (Φ (τ_grid 0, t_grid (k + 1)) / Φ (τ_grid 0, t_grid k)) =
          Complex.log (-(y₁ : ℂ) * I) - Complex.log ((y₁ : ℂ) * I) := by
      have hterm1 : ∀ k ∈ Finset.range (2 * M),
          Complex.log (Φ (τ_grid 0, t_grid (k + 1)) / Φ (τ_grid 0, t_grid k)) =
            Complex.log (Φ (0, t_grid (k + 1))) - Complex.log (Φ (0, t_grid k)) := by
        intro k hk
        rw [Finset.mem_range] at hk
        rw [hτ_0]
        have hk4 : k + 1 ≤ 4 * M := by omega
        have hq1 : ((0 : ℝ), t_grid (k + 1)) ∈ K_box := ⟨⟨le_rfl, zero_le_one⟩, ht_mem (k + 1) hk4⟩
        have hq0 : ((0 : ℝ), t_grid k) ∈ K_box := ⟨⟨le_rfl, zero_le_one⟩, ht_mem k (by omega)⟩
        have hd_t : dist (t_grid (k + 1)) (t_grid k) < δ := by
          dsimp only [t_grid, M]
          rw [Real.dist_eq, ← sub_div, Nat.cast_add, Nat.cast_one, add_sub_cancel_left,
            abs_of_pos (by positivity)]
          exact hstep_lt
        have hdiv_re : 0 < (Φ (0, t_grid (k + 1)) / Φ (0, t_grid k)).re := by
          refine hratio_re_pos _ hq1 _ hq0 ?_
          rw [Prod.dist_eq, dist_self]
          exact max_lt hδ_pos hd_t
        have ht_k1_02 : t_grid (k + 1) ∈ Icc (0 : ℝ) 2 := by
          refine ⟨by positivity, ?_⟩
          dsimp only [t_grid]
          rw [div_le_iff₀ hM_real_pos]
          exact_mod_cast hk
        have ht_k_02 : t_grid k ∈ Icc (0 : ℝ) 2 := by
          refine ⟨by positivity, ?_⟩
          dsimp only [t_grid]
          rw [div_le_iff₀ hM_real_pos]
          exact_mod_cast hk.le
        have hre1 : 0 ≤ (Φ (0, t_grid (k + 1))).re := by
          simpa [Φ, hp0] using hσ_re_02 _ ht_k1_02
        have hre0 : 0 ≤ (Φ (0, t_grid k)).re := by
          simpa [Φ, hp0] using hσ_re_02 _ ht_k_02
        exact log_div_of_re_nonneg_of_div_re_pos (hΦ_ne_zero _ hq1) (hΦ_ne_zero _ hq0)
          hre1 hre0 hdiv_re
      rw [Finset.sum_congr rfl hterm1,
        Finset.sum_range_sub (fun k => Complex.log (Φ (0, t_grid k)))]
      have ht0 : t_grid 0 = 0 := by simp [t_grid]
      have ht2M : t_grid (2 * M) = 2 := by
        dsimp only [t_grid]; push_cast; exact mul_div_cancel_right₀ 2 hM_real_pos.ne'
      rw [ht2M, ht0]
      simp [Φ, hp0, hσ_2, hσ_0]
    have hsum2 : ∑ k ∈ Finset.range (2 * M),
        Complex.log (Φ (τ_grid 0, t_grid (2 * M + k + 1)) / Φ (τ_grid 0, t_grid (2 * M + k))) =
          Complex.log (-(y₁ : ℂ) * I) - Complex.log ((y₁ : ℂ) * I) := by
      have hterm2 : ∀ k ∈ Finset.range (2 * M),
          Complex.log (Φ (τ_grid 0, t_grid (2 * M + k + 1)) / Φ (τ_grid 0, t_grid (2 * M + k))) =
            Complex.log (-Φ (0, t_grid (2 * M + (k + 1)))) -
              Complex.log (-Φ (0, t_grid (2 * M + k))) := by
        intro k hk
        rw [Finset.mem_range] at hk
        rw [hτ_0, show 2 * M + k + 1 = 2 * M + (k + 1) by omega]
        have hk4 : 2 * M + (k + 1) ≤ 4 * M := by omega
        have hq1 : ((0 : ℝ), t_grid (2 * M + (k + 1))) ∈ K_box :=
          ⟨⟨le_rfl, zero_le_one⟩, ht_mem _ hk4⟩
        have hq0 : ((0 : ℝ), t_grid (2 * M + k)) ∈ K_box :=
          ⟨⟨le_rfl, zero_le_one⟩, ht_mem _ (by omega)⟩
        have hd_t : dist (t_grid (2 * M + (k + 1))) (t_grid (2 * M + k)) < δ := by
          dsimp only [t_grid, M]
          rw [Real.dist_eq, ← sub_div]
          have hsub : ((2 * max N₀ 1 + (k + 1) : ℕ) : ℝ) - ((2 * max N₀ 1 + k : ℕ) : ℝ) = 1 := by
            push_cast; ring
          rw [hsub, abs_of_pos (by positivity)]
          exact hstep_lt
        have hdiv_re : 0 < (Φ (0, t_grid (2 * M + (k + 1))) / Φ (0, t_grid (2 * M + k))).re := by
          refine hratio_re_pos _ hq1 _ hq0 ?_
          rw [Prod.dist_eq, dist_self]
          exact max_lt hδ_pos hd_t
        have hneg_div : (-Φ (0, t_grid (2 * M + (k + 1)))) / (-Φ (0, t_grid (2 * M + k))) =
            Φ (0, t_grid (2 * M + (k + 1))) / Φ (0, t_grid (2 * M + k)) := neg_div_neg_eq _ _
        rw [← hneg_div] at hdiv_re ⊢
        have ht_k1_24 : t_grid (2 * M + (k + 1)) ∈ Icc (2 : ℝ) 4 := by
          refine ⟨?_, (ht_mem _ hk4).2⟩
          dsimp only [t_grid]
          rw [le_div_iff₀ hM_real_pos]
          have : 2 * M ≤ 2 * M + (k + 1) := by omega
          exact_mod_cast this
        have ht_k_24 : t_grid (2 * M + k) ∈ Icc (2 : ℝ) 4 := by
          refine ⟨?_, (ht_mem _ (by omega)).2⟩
          dsimp only [t_grid]
          rw [le_div_iff₀ hM_real_pos]
          have : 2 * M ≤ 2 * M + k := by omega
          exact_mod_cast this
        have hre1 : 0 ≤ (-Φ (0, t_grid (2 * M + (k + 1)))).re := by
          simpa [Φ, hp0] using hσ_re_24 _ ht_k1_24
        have hre0 : 0 ≤ (-Φ (0, t_grid (2 * M + k))).re := by
          simpa [Φ, hp0] using hσ_re_24 _ ht_k_24
        exact log_div_of_re_nonneg_of_div_re_pos (neg_ne_zero.mpr (hΦ_ne_zero _ hq1))
          (neg_ne_zero.mpr (hΦ_ne_zero _ hq0)) hre1 hre0 hdiv_re
      rw [Finset.sum_congr rfl hterm2,
        Finset.sum_range_sub (fun k => Complex.log (-Φ (0, t_grid (2 * M + k))))]
      have ht2M : t_grid (2 * M + 0) = 2 := by
        simp only [add_zero]
        dsimp only [t_grid]; push_cast; exact mul_div_cancel_right₀ 2 hM_real_pos.ne'
      have ht4M : t_grid (2 * M + 2 * M) = 4 := by
        rw [← hsplit]
        dsimp only [t_grid]; push_cast; exact mul_div_cancel_right₀ 4 hM_real_pos.ne'
      rw [ht4M, ht2M]
      have h1 : -Φ (0, 4) = -(y₁ : ℂ) * I := by simp [Φ, hp0, hσ_4]
      have h2 : -Φ (0, 2) = (y₁ : ℂ) * I := by simp [Φ, hp0, hσ_2]
      rw [h1, h2]
    rw [hsum1, hsum2, two_mul]
  have hd_zero : Complex.log (-(y₁ : ℂ) * I) - Complex.log ((y₁ : ℂ) * I) = 0 := by
    have h2 : 2 * (Complex.log (-(y₁ : ℂ) * I) - Complex.log ((y₁ : ℂ) * I)) = 0 := by
      rw [← hW_0_val, ← hW_eq, hW_N_zero]
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  have hy_ne : (y₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy₁_ne
  have hyI_ne : (y₁ : ℂ) * I ≠ 0 := mul_ne_zero hy_ne I_ne_zero
  have hneg_yI_ne : -(y₁ : ℂ) * I ≠ 0 := by simpa using neg_ne_zero.mpr hyI_ne
  have hexp_eq : Complex.exp (Complex.log (-(y₁ : ℂ) * I) - Complex.log ((y₁ : ℂ) * I)) = -1 := by
    rw [Complex.exp_sub, Complex.exp_log hneg_yI_ne, Complex.exp_log hyI_ne,
      neg_mul, neg_div, div_self hyI_ne]
  rw [hd_zero, Complex.exp_zero] at hexp_eq
  norm_num at hexp_eq

/-- Maximum-modulus damping bound on the connected component `U₀ = connectedComponentIn Eᶜ r`
inside the lens `Ω = ball 0 1 ∩ ball (2r) 1` using the auxiliary functions
`H_c(z) = h(z) (1 - z)^c (z - (2r - 1))^c` as `c → 0⁺` (Rudin, Theorem 12.10, p. 260). -/
private lemma norm_le_of_lens_component {r δ_f : ℝ} (hr_half : 1 / 2 < r) (hr_lt1 : r < 1)
    (hδ_f_pos : 0 < δ_f) {h : ℂ → ℂ} {E : Set ℂ} (hE_compact : IsCompact E)
    (hh_diff : DifferentiableOn ℂ h (ball (0 : ℂ) 1 ∩ ball ((2 * r : ℝ) : ℂ) 1))
    (hh_le1 : ∀ z ∈ ball (0 : ℂ) 1 ∩ ball ((2 * r : ℝ) : ℂ) 1, ‖h z‖ ≤ 1)
    (hE_bound : ∀ z ∈ E, z ≠ 1 → z ≠ ((2 * r - 1 : ℝ) : ℂ) →
      z ∈ ball (0 : ℂ) 1 ∩ ball ((2 * r : ℝ) : ℂ) 1 ∧ ‖h z‖ ≤ δ_f)
    (hr_E : (r : ℂ) ∉ E)
    (hU₀_sub_Ω : connectedComponentIn Eᶜ (r : ℂ) ⊆ ball (0 : ℂ) 1 ∩ ball ((2 * r : ℝ) : ℂ) 1) :
    ‖h (r : ℂ)‖ ≤ δ_f := by
  let Ω : Set ℂ := ball (0 : ℂ) 1 ∩ ball ((2 * r : ℝ) : ℂ) 1
  have hΩ_open : IsOpen Ω := isOpen_ball.inter isOpen_ball
  let U₀ : Set ℂ := connectedComponentIn Eᶜ (r : ℂ)
  have hU₀_bdd : IsBounded U₀ := isBounded_ball.subset (hU₀_sub_Ω.trans inter_subset_left)
  have hr_mem_U₀ : (r : ℂ) ∈ U₀ := mem_connectedComponentIn hr_E
  have hfront_U₀ : frontier U₀ ⊆ E :=
    frontier_connectedComponentIn_compl_subset hE_compact.isClosed
  have hcl_U₀ : closure U₀ ⊆ Ω ∪ {(1 : ℂ), ((2 * r - 1 : ℝ) : ℂ)} := by
    rw [closure_eq_self_union_frontier]
    rintro z (hzU | hzF)
    · exact Or.inl (hU₀_sub_Ω hzU)
    · by_cases hz1 : z = 1
      · exact Or.inr (Or.inl hz1)
      · by_cases hz2r : z = ((2 * r - 1 : ℝ) : ℂ)
        · exact Or.inr (Or.inr hz2r)
        · exact Or.inl (hE_bound z (hfront_U₀ hzF) hz1 hz2r).1
  have hlens1 : ∀ z ∈ Ω, 0 < (1 - z).re ∧ ‖1 - z‖ < 1 := by
    rintro z ⟨hz1, hz2⟩
    rw [mem_ball, dist_zero_right] at hz1
    rw [mem_ball, dist_eq_norm] at hz2
    have hre_lt1 : z.re < 1 := (le_abs_self _).trans_lt ((Complex.abs_re_le_norm z).trans_lt hz1)
    refine ⟨by simp; linarith, ?_⟩
    have hns2 : Complex.normSq (z - ((2 * r : ℝ) : ℂ)) < 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (z - ((2 * r : ℝ) : ℂ))]
    have hid : Complex.normSq (1 - z) =
        Complex.normSq (z - ((2 * r : ℝ) : ℂ)) + (2 * r - 1) * (2 * z.re - 2 * r - 1) := by
      simp [Complex.normSq_apply]; ring
    have hsq : ‖1 - z‖ ^ 2 < 1 := by
      rw [← Complex.normSq_eq_norm_sq, hid]; nlinarith
    nlinarith [norm_nonneg (1 - z)]
  have hlens2 : ∀ z ∈ Ω, 0 < (z - ((2 * r - 1 : ℝ) : ℂ)).re ∧
      ‖z - ((2 * r - 1 : ℝ) : ℂ)‖ < 1 := by
    rintro z ⟨hz1, hz2⟩
    rw [mem_ball, dist_zero_right] at hz1
    rw [mem_ball, dist_eq_norm] at hz2
    have hre_gt : 2 * r - 1 < z.re := by
      have hle := (abs_le.mp (Complex.abs_re_le_norm (z - ((2 * r : ℝ) : ℂ)))).1
      simp at hle
      push_cast at hz2
      linarith
    refine ⟨by simp; linarith, ?_⟩
    have hns1 : Complex.normSq z < 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
    have hid : Complex.normSq (z - ((2 * r - 1 : ℝ) : ℂ)) =
        Complex.normSq z + (2 * r - 1) * (2 * r - 1 - 2 * z.re) := by
      simp [Complex.normSq_apply]; ring
    have hsq : ‖z - ((2 * r - 1 : ℝ) : ℂ)‖ ^ 2 < 1 := by
      rw [← Complex.normSq_eq_norm_sq, hid]; nlinarith
    nlinarith [norm_nonneg (z - ((2 * r - 1 : ℝ) : ℂ))]
  have h1_not_Ω : (1 : ℂ) ∉ Ω := by
    intro hmem
    have := hmem.1
    simp [mem_ball] at this
  have h2r1_not_Ω : ((2 * r - 1 : ℝ) : ℂ) ∉ Ω := by
    intro hmem
    have h2 := hmem.2
    rw [mem_ball, dist_eq_norm] at h2
    have : ((2 * r - 1 : ℝ) : ℂ) - ((2 * r : ℝ) : ℂ) = -1 := by push_cast; ring
    rw [this, norm_neg, norm_one] at h2
    exact lt_irrefl 1 h2
  have hbound_c : ∀ c : ℝ, 0 < c → ‖h (r : ℂ)‖ * ((1 - r) ^ c * (1 - r) ^ c) ≤ δ_f := by
    intro c hc
    classical
    let H_core : ℂ → ℂ := fun z =>
      h z * Complex.exp ((c : ℂ) * Complex.log (1 - z)) *
        Complex.exp ((c : ℂ) * Complex.log (z - ((2 * r - 1 : ℝ) : ℂ)))
    let H_c : ℂ → ℂ := fun z => if z ∈ Ω then H_core z else 0
    have hHc_pos : ∀ {z : ℂ}, z ∈ Ω → H_c z = H_core z := fun hz =>
      ite_eq_left_iff.mpr fun h => absurd hz h
    have hHc_neg : ∀ {z : ℂ}, z ∉ Ω → H_c z = 0 := fun hz =>
      ite_eq_right_iff.mpr fun h => absurd h hz
    have hH_norm : ∀ z ∈ Ω, ‖H_core z‖ =
        ‖h z‖ * (‖1 - z‖ ^ c * ‖z - ((2 * r - 1 : ℝ) : ℂ)‖ ^ c) := by
      intro z hz
      have hw1 : 1 - z ≠ 0 := by
        intro h0; have := (hlens1 z hz).1; rw [h0, zero_re] at this; exact lt_irrefl 0 this
      have hw2 : z - ((2 * r - 1 : ℝ) : ℂ) ≠ 0 := by
        intro h0; have := (hlens2 z hz).1; rw [h0, zero_re] at this; exact lt_irrefl 0 this
      dsimp only [H_core]
      rw [norm_mul, norm_mul, mul_assoc, Complex.norm_exp, Complex.norm_exp]
      have hr1 : ((c : ℂ) * Complex.log (1 - z)).re = c * Real.log ‖1 - z‖ := by
        simp [Complex.log_re]
      have hr2 : ((c : ℂ) * Complex.log (z - ((2 * r - 1 : ℝ) : ℂ))).re =
          c * Real.log ‖z - ((2 * r - 1 : ℝ) : ℂ)‖ := by
        simp [Complex.log_re]
      rw [hr1, hr2, mul_comm c (Real.log ‖1 - z‖), mul_comm c (Real.log _),
        ← Real.rpow_def_of_pos (norm_pos_iff.mpr hw1),
        ← Real.rpow_def_of_pos (norm_pos_iff.mpr hw2)]
    have hHc_diff_Ω : DifferentiableOn ℂ H_c Ω := by
      have hcore_diff : DifferentiableOn ℂ H_core Ω := by
        intro z hz
        have hd_h : DifferentiableAt ℂ h z := hh_diff.differentiableAt (hΩ_open.mem_nhds hz)
        have hslit1 : 1 - z ∈ Complex.slitPlane :=
          Complex.mem_slitPlane_iff.mpr (Or.inl (hlens1 z hz).1)
        have hslit2 : z - ((2 * r - 1 : ℝ) : ℂ) ∈ Complex.slitPlane :=
          Complex.mem_slitPlane_iff.mpr (Or.inl (hlens2 z hz).1)
        have hd_l1 : DifferentiableAt ℂ (fun w => Complex.exp ((c : ℂ) * Complex.log (1 - w))) z :=
          Complex.differentiable_exp.differentiableAt.comp z
            (((Complex.differentiableAt_log hslit1).comp z
              ((differentiableAt_const 1).sub differentiableAt_id)).const_mul (c : ℂ))
        have hd_l2 : DifferentiableAt ℂ
            (fun w => Complex.exp ((c : ℂ) * Complex.log (w - ((2 * r - 1 : ℝ) : ℂ)))) z :=
          Complex.differentiable_exp.differentiableAt.comp z
            (((Complex.differentiableAt_log hslit2).comp z
              (differentiableAt_id.sub (differentiableAt_const _))).const_mul (c : ℂ))
        exact ((hd_h.mul hd_l1).mul hd_l2).differentiableWithinAt
      exact hcore_diff.congr fun z hz => hHc_pos hz
    have hHc_cont_cl : ContinuousOn H_c (closure U₀) := by
      intro z₀ hz₀
      rcases hcl_U₀ hz₀ with hz₀_Ω | rfl | rfl
      · exact (hHc_diff_Ω.differentiableAt (hΩ_open.mem_nhds hz₀_Ω)).continuousAt.continuousWithinAt
      · refine ContinuousAt.continuousWithinAt ?_
        rw [Metric.continuousAt_iff]
        intro η hη
        have h0c : Tendsto (fun z : ℂ => ‖1 - z‖ ^ c) (𝓝 1) (𝓝 0) := by
          have h1 : Tendsto (fun z : ℂ => ‖(1 : ℂ) - z‖) (𝓝 1) (𝓝 0) := by
            simpa using ((continuous_const (y := (1 : ℂ))).sub continuous_id).norm.tendsto 1
          have h2 := (Real.continuousAt_rpow_const 0 c (Or.inr hc.le)).tendsto.comp h1
          rwa [Real.zero_rpow hc.ne'] at h2
        obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.tendsto_nhds_nhds.mp h0c η hη
        refine ⟨δ₁, hδ₁_pos, fun {z} hz_dist => ?_⟩
        rw [hHc_neg h1_not_Ω, dist_zero_right]
        have hle_pow : ‖H_c z‖ ≤ ‖1 - z‖ ^ c := by
          by_cases hzΩ : z ∈ Ω
          · rw [hHc_pos hzΩ, hH_norm z hzΩ]
            have b_h := hh_le1 z hzΩ
            have b_2 : ‖z - ((2 * r - 1 : ℝ) : ℂ)‖ ^ c ≤ 1 :=
              Real.rpow_le_one (norm_nonneg _) (hlens2 z hzΩ).2.le hc.le
            calc ‖h z‖ * (‖1 - z‖ ^ c * ‖z - ((2 * r - 1 : ℝ) : ℂ)‖ ^ c)
                ≤ 1 * (‖1 - z‖ ^ c * 1) :=
                  mul_le_mul b_h (mul_le_mul_of_nonneg_left b_2 (by positivity))
                    (by positivity) zero_le_one
              _ = ‖1 - z‖ ^ c := by ring
          · rw [hHc_neg hzΩ, norm_zero]
            positivity
        exact lt_of_le_of_lt hle_pow (by simpa [Real.dist_eq, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) c)] using hδ₁ hz_dist)
      · refine ContinuousAt.continuousWithinAt ?_
        rw [Metric.continuousAt_iff]
        intro η hη
        let a₂ : ℂ := ((2 * r - 1 : ℝ) : ℂ)
        have h0c : Tendsto (fun z : ℂ => ‖z - a₂‖ ^ c) (𝓝 a₂) (𝓝 0) := by
          have h1 : Tendsto (fun z : ℂ => ‖z - a₂‖) (𝓝 a₂) (𝓝 0) := by
            simpa using (continuous_id.sub (continuous_const (y := a₂))).norm.tendsto a₂
          have h2 := (Real.continuousAt_rpow_const 0 c (Or.inr hc.le)).tendsto.comp h1
          rwa [Real.zero_rpow hc.ne'] at h2
        obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.tendsto_nhds_nhds.mp h0c η hη
        refine ⟨δ₁, hδ₁_pos, fun {z} hz_dist => ?_⟩
        rw [hHc_neg h2r1_not_Ω, dist_zero_right]
        have hle_pow : ‖H_c z‖ ≤ ‖z - a₂‖ ^ c := by
          by_cases hzΩ : z ∈ Ω
          · rw [hHc_pos hzΩ, hH_norm z hzΩ]
            have b_h := hh_le1 z hzΩ
            have b_1 : ‖1 - z‖ ^ c ≤ 1 :=
              Real.rpow_le_one (norm_nonneg _) (hlens1 z hzΩ).2.le hc.le
            calc ‖h z‖ * (‖1 - z‖ ^ c * ‖z - a₂‖ ^ c)
                ≤ 1 * (1 * ‖z - a₂‖ ^ c) :=
                  mul_le_mul b_h (mul_le_mul_of_nonneg_right b_1 (by positivity))
                    (by positivity) zero_le_one
              _ = ‖z - a₂‖ ^ c := by ring
          · rw [hHc_neg hzΩ, norm_zero]
            positivity
        exact lt_of_le_of_lt hle_pow (by simpa [Real.dist_eq, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) c)] using hδ₁ hz_dist)
    have hbnd_front : boundaryNorm H_c U₀ ≤ δ_f := by
      unfold boundaryNorm
      by_cases hne : (frontier U₀).Nonempty
      · refine csSup_le (hne.image _) ?_
        rintro _ ⟨z, hzF, rfl⟩
        dsimp only
        by_cases hz1 : z = 1
        · rw [hz1, hHc_neg h1_not_Ω, norm_zero]; exact hδ_f_pos.le
        · by_cases hz2r : z = ((2 * r - 1 : ℝ) : ℂ)
          · rw [hz2r, hHc_neg h2r1_not_Ω, norm_zero]; exact hδ_f_pos.le
          · obtain ⟨hzΩ, hhz_le⟩ := hE_bound z (hfront_U₀ hzF) hz1 hz2r
            rw [hHc_pos hzΩ, hH_norm z hzΩ]
            have b1 : ‖1 - z‖ ^ c ≤ 1 :=
              Real.rpow_le_one (norm_nonneg _) (hlens1 z hzΩ).2.le hc.le
            have b2 : ‖z - ((2 * r - 1 : ℝ) : ℂ)‖ ^ c ≤ 1 :=
              Real.rpow_le_one (norm_nonneg _) (hlens2 z hzΩ).2.le hc.le
            calc ‖h z‖ * (‖1 - z‖ ^ c * ‖z - ((2 * r - 1 : ℝ) : ℂ)‖ ^ c)
                ≤ δ_f * (1 * 1) :=
                  mul_le_mul hhz_le (mul_le_mul b1 b2 (by positivity) zero_le_one)
                    (by positivity) hδ_f_pos.le
              _ = δ_f := by ring
      · rw [Set.not_nonempty_iff_eq_empty.mp hne, image_empty, Real.sSup_empty]
        exact hδ_f_pos.le
    have hr_in_Ω : (r : ℂ) ∈ Ω := hU₀_sub_Ω hr_mem_U₀
    have hmax := (theorem12_1_boundary_bound hU₀_bdd (hHc_diff_Ω.mono hU₀_sub_Ω)
      hHc_cont_cl (subset_closure hr_mem_U₀)).trans hbnd_front
    rw [hHc_pos hr_in_Ω, hH_norm (r : ℂ) hr_in_Ω] at hmax
    have hn1 : ‖1 - (r : ℂ)‖ = 1 - r := by
      have : 1 - (r : ℂ) = ((1 - r : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hn2 : ‖(r : ℂ) - ((2 * r - 1 : ℝ) : ℂ)‖ = 1 - r := by
      have : (r : ℂ) - ((2 * r - 1 : ℝ) : ℂ) = ((1 - r : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rwa [hn1, hn2] at hmax
  have hseq_lim : Tendsto (fun n : ℕ =>
      ‖h (r : ℂ)‖ * ((1 - r) ^ (1 / ((n : ℝ) + 1)) * (1 - r) ^ (1 / ((n : ℝ) + 1))))
      atTop (𝓝 (‖h (r : ℂ)‖ * (1 * 1))) := by
    have h1mr_pos : 0 < 1 - r := by linarith
    have hc_tend : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hpow_tend : Tendsto (fun n : ℕ => (1 - r) ^ (1 / ((n : ℝ) + 1))) atTop (𝓝 1) := by
      have h := (Real.continuousAt_const_rpow (a := 1 - r) (b := 0) h1mr_pos.ne').tendsto.comp hc_tend
      rwa [Real.rpow_zero] at h
    exact tendsto_const_nhds.mul (hpow_tend.mul hpow_tend)
  have hle_lim := le_of_tendsto hseq_lim (Eventually.of_forall fun n =>
    hbound_c (1 / ((n : ℝ) + 1)) (by positivity))
  linarith

/-- Core Theorem 12.10 (radial limit at `1`, Rudin pp. 259–260): if `Γ : ℝ → ℂ` is continuous on
`Icc 0 1` with `‖Γ t‖ < 1` for `t ∈ Ico 0 1` and `Γ 1 = 1`, and `g : ℂ → ℂ` is bounded and
holomorphic on `ball 0 1` with `lim_{t → 1⁻} g (Γ t) = L`, then `lim_{r → 1⁻} g r = L`. -/
theorem theorem12_10_radial_unitOne {Γ : ℝ → ℂ} (hΓ_cont : ContinuousOn Γ (Icc 0 1))
    (hΓ_lt : ∀ t ∈ Ico (0 : ℝ) 1, ‖Γ t‖ < 1) (hΓ_one : Γ 1 = 1)
    {g : ℂ → ℂ} (hg_holo : DifferentiableOn ℂ g (ball (0 : ℂ) 1))
    (hg_bdd : ∃ M : ℝ, ∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ M)
    {L : ℂ} (hlim : Tendsto (fun t : ℝ => g (Γ t)) (𝓝[<] 1) (𝓝 L)) :
    Tendsto (fun r : ℝ => g r) (𝓝[<] 1) (𝓝 L) := by
  obtain ⟨M₀, hM₀⟩ := hg_bdd
  let B : ℝ := max M₀ 0 + ‖L‖ + 1
  have hB_pos : 0 < B := by positivity
  have hB_ne : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB_pos.ne'
  let f : ℂ → ℂ := fun z => (g z - L) / (B : ℂ)
  have hf_holo : DifferentiableOn ℂ f (ball (0 : ℂ) 1) :=
    (hg_holo.sub (differentiableOn_const L)).div_const (B : ℂ)
  have hf_le1 : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ 1 := by
    intro z hz
    dsimp only [f]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB_pos, div_le_one hB_pos]
    calc ‖g z - L‖ ≤ ‖g z‖ + ‖L‖ := norm_sub_le _ _
      _ ≤ max M₀ 0 + ‖L‖ := add_le_add ((hM₀ z hz).trans (le_max_left M₀ 0)) le_rfl
      _ ≤ B := by dsimp [B]; linarith
  have hf_lim : Tendsto (fun t : ℝ => f (Γ t)) (𝓝[<] 1) (𝓝 0) := by
    have h0 : (0 : ℂ) = (L - L) / (B : ℂ) := by simp
    rw [h0]
    exact (hlim.sub_const L).div_const (B : ℂ)
  suffices hf_rad : Tendsto (fun r : ℝ => f r) (𝓝[<] 1) (𝓝 0) by
    have hlin := (hf_rad.const_mul (B : ℂ)).add_const L
    simp only [mul_zero, zero_add] at hlin
    refine hlin.congr fun r => ?_
    dsimp only [f]
    rw [mul_div_cancel₀ _ hB_ne, sub_add_cancel]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  let δ_f : ℝ := min (1 / 2) ((ε / 2) ^ 4)
  have hδ_f_pos : 0 < δ_f := lt_min (by positivity) (by positivity)
  obtain ⟨η₀, hη₀_pos, hη₀⟩ := Metric.tendsto_nhdsWithin_nhds.mp hf_lim δ_f hδ_f_pos
  let t₀ : ℝ := max 0 (1 - η₀ / 2)
  have ht₀_nonneg : 0 ≤ t₀ := le_max_left _ _
  have ht₀_lt1 : t₀ < 1 := max_lt zero_lt_one (by linarith)
  have hf_lt_on_t₀ : ∀ t ∈ Ico t₀ 1, ‖f (Γ t)‖ < δ_f := by
    intro t ⟨ht_ge, ht_lt⟩
    have hdist : dist t 1 < η₀ := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      have : 1 - η₀ / 2 ≤ t := (le_max_right 0 (1 - η₀ / 2)).trans ht_ge
      linarith
    simpa [dist_zero_right] using hη₀ ht_lt hdist
  have hΓt₀_lt1 : (Γ t₀).re < 1 :=
    (le_abs_self _).trans_lt ((Complex.abs_re_le_norm _).trans_lt (hΓ_lt t₀ ⟨ht₀_nonneg, ht₀_lt1⟩))
  let r₀ : ℝ := max (1 / 2) (Γ t₀).re
  have hr₀_lt1 : r₀ < 1 := max_lt (by norm_num) hΓt₀_lt1
  refine ⟨1 - r₀, sub_pos.mpr hr₀_lt1, ?_⟩
  intro r hr_lt1 hr_dist
  rw [mem_Iio] at hr_lt1
  rw [Real.dist_eq, abs_of_neg (by linarith)] at hr_dist
  have hr_gt_r₀ : r₀ < r := by linarith
  have hr_half : 1 / 2 < r := lt_of_le_of_lt (le_max_left _ _) hr_gt_r₀
  have hr_gt_Γt₀ : (Γ t₀).re < r := lt_of_le_of_lt (le_max_right _ _) hr_gt_r₀
  let Γ_ext : ℝ → ℂ := fun t => Γ (projIcc 0 1 zero_le_one t)
  have hΓ_ext_cont : Continuous Γ_ext :=
    hΓ_cont.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun t => (projIcc 0 1 zero_le_one t).2
  have hΓ_ext_eq : ∀ t ∈ Icc (0 : ℝ) 1, Γ_ext t = Γ t := by
    intro t ht
    dsimp only [Γ_ext]
    rw [projIcc_of_mem zero_le_one ht]
  let S_r : Set ℝ := Icc t₀ 1 ∩ {t : ℝ | (Γ_ext t).re = r}
  have hS_comp : IsCompact S_r :=
    isCompact_Icc.inter_right (isClosed_eq (Complex.continuous_re.comp hΓ_ext_cont) continuous_const)
  have hS_ne : S_r.Nonempty := by
    have hivt := intermediate_value_Icc ht₀_lt1.le
      (Complex.continuous_re.comp hΓ_ext_cont).continuousOn
    have hmem : r ∈ Icc (Γ_ext t₀).re (Γ_ext 1).re := by
      rw [hΓ_ext_eq t₀ ⟨ht₀_nonneg, ht₀_lt1.le⟩, hΓ_ext_eq 1 ⟨zero_le_one, le_rfl⟩, hΓ_one]
      simp [hr_gt_Γt₀.le, hr_lt1.le]
    obtain ⟨s, hs_Icc, hs_eq⟩ := hivt hmem
    exact ⟨s, hs_Icc, hs_eq⟩
  let t₁ : ℝ := sSup S_r
  have ht₁_mem : t₁ ∈ S_r := hS_comp.sSup_mem hS_ne
  have ht₁_ge_t₀ : t₀ ≤ t₁ := ht₁_mem.1.1
  have ht₁_le1 : t₁ ≤ 1 := ht₁_mem.1.2
  have ht₁_re : (Γ_ext t₁).re = r := ht₁_mem.2
  have ht₁_lt1 : t₁ < 1 := by
    refine lt_of_le_of_ne ht₁_le1 ?_
    intro heq
    rw [heq, hΓ_ext_eq 1 ⟨zero_le_one, le_rfl⟩, hΓ_one, one_re] at ht₁_re
    exact hr_lt1.ne ht₁_re.symm
  have ht₁_re_gt : ∀ t ∈ Ioc t₁ 1, r < (Γ_ext t).re := by
    intro t ⟨ht_gt, ht_le1⟩
    by_contra hnot
    have hle : (Γ_ext t).re ≤ r := le_of_not_gt hnot
    have hivt := intermediate_value_Icc ht_le1
      (Complex.continuous_re.comp hΓ_ext_cont).continuousOn
    have hmem : r ∈ Icc (Γ_ext t).re (Γ_ext 1).re := by
      rw [hΓ_ext_eq 1 ⟨zero_le_one, le_rfl⟩, hΓ_one]
      exact ⟨hle, hr_lt1.le⟩
    obtain ⟨s, hs_Icc, hs_eq⟩ := hivt hmem
    have hs_in : s ∈ S_r := ⟨⟨ht₁_ge_t₀.trans (ht_gt.le.trans hs_Icc.1), hs_Icc.2⟩, hs_eq⟩
    have hs_le : s ≤ t₁ := le_csSup hS_comp.bddAbove hs_in
    linarith [hs_Icc.1]
  let γ₁ : ℝ → ℂ := fun s => Γ_ext (t₁ + s * (1 - t₁))
  have hγ₁_cont : Continuous γ₁ := hΓ_ext_cont.comp (by fun_prop)
  have hγ₁_eq : ∀ s ∈ Icc (0 : ℝ) 1, γ₁ s = Γ (t₁ + s * (1 - t₁)) := by
    intro s ⟨hs0, hs1⟩
    exact hΓ_ext_eq _ ⟨by nlinarith, by nlinarith⟩
  have hγ₁_lt1 : ∀ s ∈ Ico (0 : ℝ) 1, ‖γ₁ s‖ < 1 := by
    intro s ⟨hs0, hs1⟩
    rw [hγ₁_eq s ⟨hs0, hs1.le⟩]
    exact hΓ_lt _ ⟨by nlinarith, by nlinarith⟩
  have hγ₁_f_lt : ∀ s ∈ Ico (0 : ℝ) 1, ‖f (γ₁ s)‖ < δ_f := by
    intro s ⟨hs0, hs1⟩
    rw [hγ₁_eq s ⟨hs0, hs1.le⟩]
    exact hf_lt_on_t₀ _ ⟨by nlinarith, by nlinarith⟩
  have hγ₁_one : γ₁ 1 = 1 := by
    rw [hγ₁_eq 1 ⟨zero_le_one, le_rfl⟩, show t₁ + 1 * (1 - t₁) = 1 by ring, hΓ_one]
  have hγ₁_zero_re : (γ₁ 0).re = r := by
    dsimp only [γ₁]
    simpa using ht₁_re
  have hγ₁_re_gt : ∀ s ∈ Ioc (0 : ℝ) 1, r < (γ₁ s).re := by
    intro s ⟨hs0, hs1⟩
    exact ht₁_re_gt _ ⟨by nlinarith, by nlinarith⟩
  -- 4-fold reflection product `h` on `Ω = ball 0 1 ∩ ball (2r) 1`
  let Ω : Set ℂ := ball (0 : ℂ) 1 ∩ ball ((2 * r : ℝ) : ℂ) 1
  have hΩ_open : IsOpen Ω := isOpen_ball.inter isOpen_ball
  let f₁ : ℂ → ℂ := f
  let f₂ : ℂ → ℂ := fun z => conj (f (conj z))
  let f₃ : ℂ → ℂ := fun z => f (((2 * r : ℝ) : ℂ) - z)
  let f₄ : ℂ → ℂ := fun z => f₂ (((2 * r : ℝ) : ℂ) - z)
  let h : ℂ → ℂ := fun z => f₁ z * f₂ z * f₃ z * f₄ z
  have hf₂_diff : DifferentiableOn ℂ f₂ (ball (0 : ℂ) 1) := by
    intro z hz
    have hcz : conj z ∈ ball (0 : ℂ) 1 := by simpa [mem_ball] using hz
    exact (differentiableAt_conj_comp_conj (hf_holo.differentiableAt (isOpen_ball.mem_nhds hcz))).differentiableWithinAt
  have h2r_maps : MapsTo (fun z : ℂ => ((2 * r : ℝ) : ℂ) - z) Ω (ball (0 : ℂ) 1) := by
    intro z hz
    rw [mem_ball, dist_zero_right, norm_sub_rev]
    simpa [mem_ball, dist_eq_norm] using hz.2
  have hh_diff : DifferentiableOn ℂ h Ω := by
    have hd1 : DifferentiableOn ℂ f₁ Ω := hf_holo.mono inter_subset_left
    have hd2 : DifferentiableOn ℂ f₂ Ω := hf₂_diff.mono inter_subset_left
    have hd3 : DifferentiableOn ℂ f₃ Ω :=
      hf_holo.comp (differentiableOn_const _ |>.sub differentiableOn_id) h2r_maps
    have hd4 : DifferentiableOn ℂ f₄ Ω :=
      hf₂_diff.comp (differentiableOn_const _ |>.sub differentiableOn_id) h2r_maps
    exact ((hd1.mul hd2).mul hd3).mul hd4
  have hh_le1 : ∀ z ∈ Ω, ‖h z‖ ≤ 1 := by
    intro z hz
    have hcz : conj z ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball, dist_zero_right, Complex.norm_conj]
      simpa [mem_ball] using hz.1
    have hsz : ((2 * r : ℝ) : ℂ) - z ∈ ball (0 : ℂ) 1 := h2r_maps hz
    have hcsz : conj (((2 * r : ℝ) : ℂ) - z) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball, dist_zero_right, Complex.norm_conj]
      simpa [mem_ball] using hsz
    have b1 : ‖f₁ z‖ ≤ 1 := hf_le1 z hz.1
    have b2 : ‖f₂ z‖ ≤ 1 := by dsimp [f₂]; rw [Complex.norm_conj]; exact hf_le1 _ hcz
    have b3 : ‖f₃ z‖ ≤ 1 := hf_le1 _ hsz
    have b4 : ‖f₄ z‖ ≤ 1 := by dsimp [f₄, f₂]; rw [Complex.norm_conj]; exact hf_le1 _ hcsz
    dsimp only [h]
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖f₁ z‖ * ‖f₂ z‖ * ‖f₃ z‖ * ‖f₄ z‖
        ≤ 1 * 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul (mul_le_mul b1 b2 (norm_nonneg _) (by positivity)) b3
            (norm_nonneg _) (by positivity)) b4 (norm_nonneg _) (by positivity)
      _ = 1 := by ring
  have hh_at_r : ‖h (r : ℂ)‖ = ‖f (r : ℂ)‖ ^ 4 := by
    have h2r_sub : ((2 * r : ℝ) : ℂ) - (r : ℂ) = (r : ℂ) := by push_cast; ring
    have hconj_r : conj (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
    dsimp only [h, f₁, f₂, f₃, f₄]
    rw [h2r_sub, hconj_r, norm_mul, norm_mul, norm_mul, Complex.norm_conj]
    ring
  let E : Set ℂ := γ₁ '' Icc 0 1 ∪ (fun s => conj (γ₁ s)) '' Icc 0 1 ∪
    (fun s => ((2 * r : ℝ) : ℂ) - γ₁ s) '' Icc 0 1 ∪
    (fun s => ((2 * r : ℝ) : ℂ) - conj (γ₁ s)) '' Icc 0 1
  have hE_compact : IsCompact E := by
    exact (((isCompact_Icc.image hγ₁_cont).union
      (isCompact_Icc.image (Complex.continuous_conj.comp hγ₁_cont))).union
      (isCompact_Icc.image (continuous_const.sub hγ₁_cont))).union
      (isCompact_Icc.image (continuous_const.sub (Complex.continuous_conj.comp hγ₁_cont)))
  have hγ₁_mem_Ω : ∀ s ∈ Ico (0 : ℝ) 1, γ₁ s ∈ Ω := by
    intro s hs
    have hnorm : ‖γ₁ s‖ < 1 := hγ₁_lt1 s hs
    have hre_ge : r ≤ (γ₁ s).re := by
      rcases hs.1.eq_or_lt with rfl | hs_pos
      · exact hγ₁_zero_re.symm.le
      · exact (hγ₁_re_gt s ⟨hs_pos, hs.2.le⟩).le
    refine ⟨by simpa [mem_ball] using hnorm, ?_⟩
    rw [mem_ball, dist_eq_norm]
    have hns : Complex.normSq (γ₁ s) < 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (γ₁ s)]
    have hid : Complex.normSq (γ₁ s - ((2 * r : ℝ) : ℂ)) =
        Complex.normSq (γ₁ s) - 4 * r * ((γ₁ s).re - r) := by
      simp [Complex.normSq_apply]; ring
    have hsq : ‖γ₁ s - ((2 * r : ℝ) : ℂ)‖ ^ 2 < 1 := by
      rw [← Complex.normSq_eq_norm_sq, hid]; nlinarith
    nlinarith [norm_nonneg (γ₁ s - ((2 * r : ℝ) : ℂ))]
  have hΩ_conj : ∀ z ∈ Ω, conj z ∈ Ω := by
    rintro z ⟨hz1, hz2⟩
    refine ⟨by simpa [mem_ball] using hz1, ?_⟩
    rw [mem_ball, dist_eq_norm] at hz2 ⊢
    have hcs : conj z - ((2 * r : ℝ) : ℂ) = conj (z - ((2 * r : ℝ) : ℂ)) := by
      apply Complex.ext <;> simp
    rwa [hcs, Complex.norm_conj]
  have hΩ_sym : ∀ z ∈ Ω, ((2 * r : ℝ) : ℂ) - z ∈ Ω := by
    rintro z ⟨hz1, hz2⟩
    rw [mem_ball, dist_zero_right] at hz1
    rw [mem_ball, dist_eq_norm] at hz2
    refine ⟨by rwa [mem_ball, dist_zero_right, norm_sub_rev], ?_⟩
    rw [mem_ball, dist_eq_norm, show ((2 * r : ℝ) : ℂ) - z - ((2 * r : ℝ) : ℂ) = -z by ring, norm_neg]
    exact hz1
  have hE_bound : ∀ z ∈ E, z ≠ 1 → z ≠ ((2 * r - 1 : ℝ) : ℂ) → z ∈ Ω ∧ ‖h z‖ ≤ δ_f := by
    rintro z (((⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩) hz1 hz2r
    · have hs_lt : s < 1 := hs.2.lt_of_ne fun h1 => hz1 (h1 ▸ hγ₁_one)
      have hzΩ : γ₁ s ∈ Ω := hγ₁_mem_Ω s ⟨hs.1, hs_lt⟩
      refine ⟨hzΩ, ?_⟩
      have b1 : ‖f₁ (γ₁ s)‖ ≤ δ_f := (hγ₁_f_lt s ⟨hs.1, hs_lt⟩).le
      have b2 : ‖f₂ (γ₁ s)‖ ≤ 1 := by
        dsimp [f₂]; rw [Complex.norm_conj]; exact hf_le1 _ (hΩ_conj _ hzΩ).1
      have b3 : ‖f₃ (γ₁ s)‖ ≤ 1 := hf_le1 _ (h2r_maps hzΩ)
      have b4 : ‖f₄ (γ₁ s)‖ ≤ 1 := by
        dsimp [f₄, f₂]; rw [Complex.norm_conj]; exact hf_le1 _ (hΩ_conj _ (hΩ_sym _ hzΩ)).1
      dsimp only [h]; rw [norm_mul, norm_mul, norm_mul]
      calc ‖f₁ (γ₁ s)‖ * ‖f₂ (γ₁ s)‖ * ‖f₃ (γ₁ s)‖ * ‖f₄ (γ₁ s)‖
          ≤ δ_f * 1 * 1 * 1 :=
            mul_le_mul (mul_le_mul (mul_le_mul b1 b2 (norm_nonneg _) (by positivity)) b3
              (norm_nonneg _) (by positivity)) b4 (norm_nonneg _) (by positivity)
        _ = δ_f := by ring
    · have hs_lt : s < 1 := hs.2.lt_of_ne fun h1 => hz1 (by dsimp only; rw [h1, hγ₁_one, map_one])
      have hsΩ : γ₁ s ∈ Ω := hγ₁_mem_Ω s ⟨hs.1, hs_lt⟩
      have hzΩ : conj (γ₁ s) ∈ Ω := hΩ_conj _ hsΩ
      refine ⟨hzΩ, ?_⟩
      have b1 : ‖f₁ (conj (γ₁ s))‖ ≤ 1 := hf_le1 _ hzΩ.1
      have b2 : ‖f₂ (conj (γ₁ s))‖ ≤ δ_f := by
        dsimp [f₂]; rw [conj_conj, Complex.norm_conj]; exact (hγ₁_f_lt s ⟨hs.1, hs_lt⟩).le
      have b3 : ‖f₃ (conj (γ₁ s))‖ ≤ 1 := hf_le1 _ (h2r_maps hzΩ)
      have b4 : ‖f₄ (conj (γ₁ s))‖ ≤ 1 := by
        dsimp [f₄, f₂]; rw [Complex.norm_conj]; exact hf_le1 _ (hΩ_conj _ (hΩ_sym _ hzΩ)).1
      dsimp only [h]; rw [norm_mul, norm_mul, norm_mul]
      calc ‖f₁ (conj (γ₁ s))‖ * ‖f₂ (conj (γ₁ s))‖ * ‖f₃ (conj (γ₁ s))‖ * ‖f₄ (conj (γ₁ s))‖
          ≤ 1 * δ_f * 1 * 1 :=
            mul_le_mul (mul_le_mul (mul_le_mul b1 b2 (norm_nonneg _) (by positivity)) b3
              (norm_nonneg _) (by positivity)) b4 (norm_nonneg _) (by positivity)
        _ = δ_f := by ring
    · have hs_lt : s < 1 := hs.2.lt_of_ne fun h1 =>
        hz2r (by dsimp only; rw [h1, hγ₁_one]; push_cast; ring)
      have hsΩ : γ₁ s ∈ Ω := hγ₁_mem_Ω s ⟨hs.1, hs_lt⟩
      have hzΩ : ((2 * r : ℝ) : ℂ) - γ₁ s ∈ Ω := hΩ_sym _ hsΩ
      refine ⟨hzΩ, ?_⟩
      have b1 : ‖f₁ (((2 * r : ℝ) : ℂ) - γ₁ s)‖ ≤ 1 := hf_le1 _ hzΩ.1
      have b2 : ‖f₂ (((2 * r : ℝ) : ℂ) - γ₁ s)‖ ≤ 1 := by
        dsimp [f₂]; rw [Complex.norm_conj]; exact hf_le1 _ (hΩ_conj _ hzΩ).1
      have b3 : ‖f₃ (((2 * r : ℝ) : ℂ) - γ₁ s)‖ ≤ δ_f := by
        dsimp [f₃]; rw [sub_sub_cancel]; exact (hγ₁_f_lt s ⟨hs.1, hs_lt⟩).le
      have b4 : ‖f₄ (((2 * r : ℝ) : ℂ) - γ₁ s)‖ ≤ 1 := by
        dsimp [f₄, f₂]; rw [Complex.norm_conj]; exact hf_le1 _ (hΩ_conj _ (hΩ_sym _ hzΩ)).1
      dsimp only [h]; rw [norm_mul, norm_mul, norm_mul]
      calc ‖f₁ (((2 * r : ℝ) : ℂ) - γ₁ s)‖ * ‖f₂ (((2 * r : ℝ) : ℂ) - γ₁ s)‖ *
            ‖f₃ (((2 * r : ℝ) : ℂ) - γ₁ s)‖ * ‖f₄ (((2 * r : ℝ) : ℂ) - γ₁ s)‖
          ≤ 1 * 1 * δ_f * 1 :=
            mul_le_mul (mul_le_mul (mul_le_mul b1 b2 (norm_nonneg _) (by positivity)) b3
              (norm_nonneg _) (by positivity)) b4 (norm_nonneg _) (by positivity)
        _ = δ_f := by ring
    · have hs_lt : s < 1 := hs.2.lt_of_ne fun h1 =>
        hz2r (by dsimp only; rw [h1, hγ₁_one, map_one]; push_cast; ring)
      have hsΩ : γ₁ s ∈ Ω := hγ₁_mem_Ω s ⟨hs.1, hs_lt⟩
      have hzΩ : ((2 * r : ℝ) : ℂ) - conj (γ₁ s) ∈ Ω := hΩ_sym _ (hΩ_conj _ hsΩ)
      refine ⟨hzΩ, ?_⟩
      have b1 : ‖f₁ (((2 * r : ℝ) : ℂ) - conj (γ₁ s))‖ ≤ 1 := hf_le1 _ hzΩ.1
      have b2 : ‖f₂ (((2 * r : ℝ) : ℂ) - conj (γ₁ s))‖ ≤ 1 := by
        dsimp [f₂]; rw [Complex.norm_conj]; exact hf_le1 _ (hΩ_conj _ hzΩ).1
      have b3 : ‖f₃ (((2 * r : ℝ) : ℂ) - conj (γ₁ s))‖ ≤ 1 := hf_le1 _ (h2r_maps hzΩ)
      have b4 : ‖f₄ (((2 * r : ℝ) : ℂ) - conj (γ₁ s))‖ ≤ δ_f := by
        dsimp [f₄, f₂]; rw [sub_sub_cancel, conj_conj, Complex.norm_conj]
        exact (hγ₁_f_lt s ⟨hs.1, hs_lt⟩).le
      dsimp only [h]; rw [norm_mul, norm_mul, norm_mul]
      calc ‖f₁ (((2 * r : ℝ) : ℂ) - conj (γ₁ s))‖ * ‖f₂ (((2 * r : ℝ) : ℂ) - conj (γ₁ s))‖ *
            ‖f₃ (((2 * r : ℝ) : ℂ) - conj (γ₁ s))‖ * ‖f₄ (((2 * r : ℝ) : ℂ) - conj (γ₁ s))‖
          ≤ 1 * 1 * 1 * δ_f :=
            mul_le_mul (mul_le_mul (mul_le_mul b1 b2 (norm_nonneg _) (by positivity)) b3
              (norm_nonneg _) (by positivity)) b4 (norm_nonneg _) (by positivity)
        _ = δ_f := by ring
  -- Bound `‖h r‖ ≤ δ_f` in both cases (`r ∈ E` or `r ∉ E`)
  have hh_r_le : ‖h (r : ℂ)‖ ≤ δ_f := by
    by_cases hr_E : (r : ℂ) ∈ E
    · have hr_ne1 : (r : ℂ) ≠ 1 := by
        intro heq
        exact hr_lt1.ne (Complex.ofReal_injective heq)
      have hr_ne2r : (r : ℂ) ≠ ((2 * r - 1 : ℝ) : ℂ) := by
        intro heq
        have := Complex.ofReal_injective heq
        linarith
      exact (hE_bound (r : ℂ) hr_E hr_ne1 hr_ne2r).2
    · exact norm_le_of_lens_component hr_half hr_lt1 hδ_f_pos hE_compact hh_diff hh_le1 hE_bound
        hr_E (connectedComponentIn_fourfold_subset_lens hr_half hr_lt1 hγ₁_cont hγ₁_lt1 hγ₁_one
          hγ₁_zero_re hγ₁_re_gt rfl hr_E)
  -- Conclude `‖f (r : ℂ)‖ < ε` from `‖f (r : ℂ)‖ ^ 4 ≤ δ_f ≤ (ε / 2) ^ 4`
  have hf_pow4 : ‖f (r : ℂ)‖ ^ 4 ≤ (ε / 2) ^ 4 := by
    rw [← hh_at_r]
    exact hh_r_le.trans (min_le_right _ _)
  have hf_le_half : ‖f (r : ℂ)‖ ≤ ε / 2 := by
    by_contra hgt
    have hlt_half : ε / 2 < ‖f (r : ℂ)‖ := lt_of_not_ge hgt
    have hpow_lt : (ε / 2) ^ 4 < ‖f (r : ℂ)‖ ^ 4 :=
      pow_lt_pow_left₀ hlt_half (by positivity) (by norm_num)
    linarith
  rw [dist_zero_right]
  linarith

/-- Rudin Exercise 14, Chapter 14 (referenced parenthetically in Theorem 12.10, p. 259):
every bounded holomorphic function `g` on `U = ball 0 1` that has radial limit `L` at `ζ ∈ T`
actually has nontangential limit `L` at `ζ` (`HasNontangentialLimit g ζ L`). -/
theorem hasNontangentialLimit_of_radialLimit_boundedHolomorphic {g : ℂ → ℂ}
    (hg_holo : DifferentiableOn ℂ g (ball (0 : ℂ) 1))
    (hg_bdd : ∃ M : ℝ, ∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ M)
    (ζ : UnitCircle) {L : ℂ}
    (hrad : Tendsto (fun r : ℝ => g ((r : ℂ) * (ζ : ℂ))) (𝓝[<] 1) (𝓝 L)) :
    HasNontangentialLimit g ζ L := by
  -- First prove the base case `ζ = unitCircleOne` via rescaled discs + Arzelà–Ascoli (`11.28`)
  suffices hbase : ∀ {g₀ : ℂ → ℂ}, DifferentiableOn ℂ g₀ (ball (0 : ℂ) 1) →
      (∃ M : ℝ, ∀ z ∈ ball (0 : ℂ) 1, ‖g₀ z‖ ≤ M) →
      Tendsto (fun r : ℝ => g₀ r) (𝓝[<] 1) (𝓝 L) →
      HasNontangentialLimit g₀ unitCircleOne L by
    obtain ⟨M₀, hM₀⟩ := hg_bdd
    let g_rot : ℂ → ℂ := fun z => g ((ζ : ℂ) * z)
    have hrot_maps : MapsTo (fun z : ℂ => (ζ : ℂ) * z) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
      intro z hz
      rw [mem_ball, dist_zero_right, norm_mul, norm_unitCircle, one_mul]
      simpa [mem_ball] using hz
    have hrot_holo : DifferentiableOn ℂ g_rot (ball (0 : ℂ) 1) :=
      hg_holo.comp (differentiableOn_id.const_mul (ζ : ℂ)) hrot_maps
    have hrot_bdd : ∃ M : ℝ, ∀ z ∈ ball (0 : ℂ) 1, ‖g_rot z‖ ≤ M :=
      ⟨M₀, fun z hz => hM₀ _ (hrot_maps hz)⟩
    have hrot_rad : Tendsto (fun r : ℝ => g_rot r) (𝓝[<] 1) (𝓝 L) := by
      refine hrad.congr fun r => ?_
      dsimp only [g_rot]
      rw [mul_comm]
    have hnt_one := hbase hrot_holo hrot_bdd hrot_rad
    rw [hasNontangentialLimit_iff_Ioo] at hnt_one ⊢
    intro α ⟨hα0, hα1⟩ z hz hlim
    have hconj_mul : conj (ζ : ℂ) * (ζ : ℂ) = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_unitCircle]
      simp
    have hmul_conj : (ζ : ℂ) * conj (ζ : ℂ) = 1 := by rw [mul_comm, hconj_mul]
    let z' : ℕ → ℂ := fun j => conj (ζ : ℂ) * z j
    have hz'_mem : ∀ j : ℕ, z' j ∈ approachRegion α unitCircleOne := by
      intro j
      have hzj := hz j
      rw [approachRegion_eq_image_mul hα0 hα1 ζ] at hzj
      obtain ⟨u, hu, hzu⟩ := hzj
      rw [approachRegion_one]
      have hu_eq : z' j = u := by
        dsimp only [z']
        rw [← hzu, ← mul_assoc, hconj_mul, one_mul]
      rwa [hu_eq]
    have hz'_lim : Tendsto z' atTop (𝓝 (unitCircleOne : ℂ)) := by
      rw [coe_unitCircleOne, ← hconj_mul]
      exact hlim.const_mul (conj (ζ : ℂ))
    refine (hnt_one α ⟨hα0, hα1⟩ z' hz'_mem hz'_lim).congr fun j => ?_
    dsimp only [g_rot, z']
    rw [← mul_assoc, hmul_conj, one_mul]
  intro g₀ hg₀_holo hg₀_bdd hg₀_rad
  obtain ⟨M₀, hM₀⟩ := hg₀_bdd
  let M : ℝ := max M₀ 0
  have hM_nonneg : 0 ≤ M := le_max_right M₀ 0
  have hg₀_le : ∀ z ∈ ball (0 : ℂ) 1, ‖g₀ z‖ ≤ M :=
    fun z hz => (hM₀ z hz).trans (le_max_left M₀ 0)
  rw [hasNontangentialLimit_iff_Ioo]
  intro α ⟨hα0, hα1⟩ z hz hlim
  by_contra hnot_tend
  rw [Metric.tendsto_atTop] at hnot_tend
  have hex_bad : ∃ ε₀ > 0, ∀ N : ℕ, ∃ n ≥ N, ε₀ ≤ dist (g₀ (z n)) L := by
    by_contra hall
    apply hnot_tend
    intro ε hε
    by_contra hnoN
    apply hall
    refine ⟨ε, hε, fun N => ?_⟩
    by_contra hno_n
    apply hnoN
    refine ⟨N, fun n hn => ?_⟩
    by_contra hge
    exact hno_n ⟨n, hn, le_of_not_gt hge⟩
  obtain ⟨ε₀, hε₀_pos, hbad⟩ := hex_bad
  let φ : ℕ → ℕ := fun k => Nat.recOn k (Classical.choose (hbad 0))
    (fun _ prev => Classical.choose (hbad (prev + 1)))
  have hφ_mono : StrictMono φ := strictMono_nat_of_lt_succ fun k =>
    Nat.lt_of_succ_le (Classical.choose_spec (hbad (φ k + 1))).1
  have hφ_bad : ∀ k : ℕ, ε₀ ≤ ‖g₀ (z (φ k)) - L‖ := by
    intro k
    cases k with
    | zero => simpa [φ, dist_eq_norm] using (Classical.choose_spec (hbad 0)).2
    | succ k => simpa [φ, dist_eq_norm] using (Classical.choose_spec (hbad (φ k + 1))).2
  -- Extract radial centers `r k ∈ [0, 1)` and rescaled offsets `w k ∈ ball 0 α`
  have hex_rw : ∀ k : ℕ, ∃ r ∈ Ico (0 : ℝ) 1,
      z (φ k) ∈ ball (r : ℂ) ((1 - r) * α) := by
    intro k
    have hmem := hz (φ k)
    rw [approachRegion_eq_iUnion_ball hα0 hα1 unitCircleOne, coe_unitCircleOne] at hmem
    obtain ⟨r, hr, hzr⟩ := Set.mem_iUnion₂.mp hmem
    exact ⟨r, hr, by simpa using hzr⟩
  choose r hr_mem hzr_ball using hex_rw
  let w : ℕ → ℂ := fun k => (z (φ k) - (r k : ℂ)) / ((1 - r k : ℝ) : ℂ)
  have hw_lt : ∀ k : ℕ, ‖w k‖ < α := by
    intro k
    have h1mr : 0 < 1 - r k := sub_pos.mpr (hr_mem k).2
    dsimp only [w]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1mr, div_lt_iff₀ h1mr, mul_comm]
    simpa [mem_ball, dist_eq_norm] using hzr_ball k
  have hz_decomp : ∀ k : ℕ, z (φ k) = (r k : ℂ) + ((1 - r k : ℝ) : ℂ) * w k := by
    intro k
    have h1mr_ne : ((1 - r k : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sub_pos.mpr (hr_mem k).2).ne'
    dsimp only [w]
    rw [mul_div_cancel₀ _ h1mr_ne, add_sub_cancel]
  have hr_tend1 : Tendsto r atTop (𝓝 1) := by
    have hzφ_lim : Tendsto (fun k => z (φ k)) atTop (𝓝 1) := by
      have h := hlim.comp hφ_mono.tendsto_atTop
      rwa [coe_unitCircleOne] at h
    rw [Metric.tendsto_atTop] at hzφ_lim ⊢
    intro η hη
    obtain ⟨K, hK⟩ := hzφ_lim ((1 - α) * η) (mul_pos (sub_pos.mpr hα1) hη)
    refine ⟨K, fun k hk => ?_⟩
    have hzk := hK k hk
    rw [dist_eq_norm, norm_sub_rev] at hzk
    have h1mr_pos : 0 < 1 - r k := sub_pos.mpr (hr_mem k).2
    have htri : 1 - r k ≤ ‖(1 : ℂ) - z (φ k)‖ + ‖z (φ k) - (r k : ℂ)‖ := by
      have h1 : ‖(1 : ℂ) - (r k : ℂ)‖ = 1 - r k := by
        have : (1 : ℂ) - (r k : ℂ) = ((1 - r k : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1mr_pos]
      rw [← h1]
      simpa using norm_sub_le_norm_sub_add_norm_sub (1 : ℂ) (z (φ k)) (r k : ℂ)
    have hzr_lt : ‖z (φ k) - (r k : ℂ)‖ < (1 - r k) * α := by
      simpa [mem_ball, dist_eq_norm] using hzr_ball k
    have h1mr_lt : (1 - α) * (1 - r k) < (1 - α) * η := by nlinarith
    have hlt_η : 1 - r k < η := lt_of_mul_lt_mul_left h1mr_lt (sub_nonneg.mpr hα1.le)
    rw [Real.dist_eq, abs_of_neg (by linarith [(hr_mem k).2])]
    linarith
  -- Apply Arzelà–Ascoli (`theorem11_28`) to `F k u = g₀ (r k + (1 - r k) * u)` on `closedBall 0 R`
  let R : ℝ := (1 + α) / 2
  have hα_lt_R : α < R := by dsimp [R]; linarith
  have hR_lt1 : R < 1 := by dsimp [R]; linarith
  have hR_pos : 0 < R := lt_trans hα0 hα_lt_R
  let R₁ : ℝ := (1 + R) / 2
  have hR_lt_R₁ : R < R₁ := by dsimp [R₁]; linarith
  have hR₁_lt1 : R₁ < 1 := by dsimp [R₁]; linarith
  let d : ℝ := (1 - R₁) / 2
  have hd_pos : 0 < d := by dsimp [d]; linarith
  let F : ℕ → ℂ → ℂ := fun k u => g₀ ((r k : ℂ) + ((1 - r k : ℝ) : ℂ) * u)
  have hF_maps : ∀ k : ℕ, MapsTo (fun u : ℂ => (r k : ℂ) + ((1 - r k : ℝ) : ℂ) * u)
      (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro k u hu
    rw [mem_ball, dist_zero_right] at hu ⊢
    have hr0 := (hr_mem k).1
    have hr1 := (hr_mem k).2
    calc ‖(r k : ℂ) + ((1 - r k : ℝ) : ℂ) * u‖
        ≤ ‖(r k : ℂ)‖ + ‖((1 - r k : ℝ) : ℂ) * u‖ := norm_add_le _ _
      _ = r k + (1 - r k) * ‖u‖ := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hr0, abs_of_pos (sub_pos.mpr hr1)]
      _ < r k + (1 - r k) * 1 := by nlinarith
      _ = 1 := by ring
  have hF_holo : ∀ k : ℕ, DifferentiableOn ℂ (F k) (ball (0 : ℂ) 1) := fun k =>
    hg₀_holo.comp ((differentiableOn_const _).add (differentiableOn_id.const_mul _)) (hF_maps k)
  have hF_le : ∀ k : ℕ, ∀ u ∈ ball (0 : ℂ) 1, ‖F k u‖ ≤ M :=
    fun k u hu => hg₀_le _ (hF_maps k hu)
  have hF_lip : ∀ k : ℕ, ∀ u ∈ ball (0 : ℂ) R₁, ∀ v ∈ ball (0 : ℂ) R₁,
      ‖F k u - F k v‖ ≤ (M / d + 1) * ‖u - v‖ := by
    intro k
    have hderiv_le : ∀ u ∈ ball (0 : ℂ) R₁, ‖deriv (F k) u‖ ≤ M / d + 1 := by
      intro u hu
      have hcb_sub : closedBall u d ⊆ ball (0 : ℂ) 1 := by
        intro q hq
        rw [mem_closedBall] at hq
        rw [mem_ball] at hu ⊢
        have := dist_triangle q u 0
        dsimp [d] at hq
        linarith
      have hdiff_cl : DiffContOnCl ℂ (F k) (ball u d) :=
        ⟨(hF_holo k).mono (ball_subset_closedBall.trans hcb_sub),
         (hF_holo k).continuousOn.mono (closure_ball_subset_closedBall.trans hcb_sub)⟩
      have hca := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hd_pos hdiff_cl
        (fun q hq => hF_le k q (hcb_sub (sphere_subset_closedBall hq)))
      linarith
    intro u hu v hv
    exact (convex_ball (0 : ℂ) R₁).norm_image_sub_le_of_norm_deriv_le
      (fun q hq => (hF_holo k).differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball hR₁_lt1.le hq)))
      hderiv_le hv hu
  let X := closedBall (0 : ℂ) R
  have hX_comp : IsCompact (closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
  have : CompactSpace X := isCompact_iff_compactSpace.mp hX_comp
  let fX : ℕ → X → ℂ := fun k x => F k x.1
  have hfX_bdd : PointwiseBounded fX := by
    rw [(theorem11_27 fX).2.1]
    intro x
    refine ⟨M, fun k => ?_⟩
    have hx_ball : x.1 ∈ ball (0 : ℂ) 1 :=
      closedBall_subset_ball hR_lt1 x.2
    exact hF_le k x.1 hx_ball
  have hfX_equi : BookEquicontinuous fX := by
    rw [BookEquicontinuous, Metric.uniformEquicontinuous_iff]
    intro ε hε
    let L_lip : ℝ := M / d + 1
    have hL_pos : 0 < L_lip := by dsimp [L_lip]; positivity
    refine ⟨ε / L_lip, div_pos hε hL_pos, fun x y hxy k => ?_⟩
    have hx_R1 : x.1 ∈ ball (0 : ℂ) R₁ := closedBall_subset_ball hR_lt_R₁ x.2
    have hy_R1 : y.1 ∈ ball (0 : ℂ) R₁ := closedBall_subset_ball hR_lt_R₁ y.2
    rw [dist_eq_norm]
    calc ‖F k x.1 - F k y.1‖
        ≤ L_lip * ‖x.1 - y.1‖ := hF_lip k x.1 hx_R1 y.1 hy_R1
      _ < L_lip * (ε / L_lip) :=
          mul_lt_mul_of_pos_left (by simpa [Subtype.dist_eq, dist_eq_norm] using hxy) hL_pos
      _ = ε := mul_div_cancel₀ ε hL_pos.ne'
  obtain ⟨ψ, gX, hψ_mono, hgX_cont, _, hgX_pt, hgX_unif⟩ := theorem11_28 hfX_bdd hfX_equi
  have hunif_univ := hgX_unif univ isCompact_univ
  classical
  let G : ℂ → ℂ := fun u => if hu : u ∈ closedBall (0 : ℂ) R then gX ⟨u, hu⟩ else L
  have hG_pos : ∀ {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) R), G u = gX ⟨u, hu⟩ :=
    fun hu => dite_eq_left_of_eq_true (eq_true hu)
  have hunif_cb : TendstoUniformlyOn (fun m => F (ψ m)) G atTop (closedBall (0 : ℂ) R) := by
    rw [Metric.tendstoUniformlyOn_iff] at hunif_univ ⊢
    intro ε hε
    filter_upwards [hunif_univ ε hε] with m hm u hu
    rw [hG_pos hu]
    exact hm ⟨u, hu⟩ (mem_univ _)
  have hunif_ball : TendstoUniformlyOn (fun m => F (ψ m)) G atTop (ball (0 : ℂ) R) :=
    hunif_cb.mono ball_subset_closedBall
  have hG_diff : DifferentiableOn ℂ G (ball (0 : ℂ) R) :=
    hunif_ball.tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun m => (hF_holo (ψ m)).mono (ball_subset_ball hR_lt1.le)) isOpen_ball
  -- Identify `G = L` on `[0, α]`, hence on all of `ball 0 R` by `zeroSet_inter_compact_finite`
  have hG_real : ∀ s ∈ Icc (0 : ℝ) α, G (s : ℂ) = L := by
    intro s ⟨hs0, hsα⟩
    have hs_cb : (s : ℂ) ∈ closedBall (0 : ℂ) R := by
      rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
      exact hsα.trans hα_lt_R.le
    have h1 : Tendsto (fun m => F (ψ m) (s : ℂ)) atTop (𝓝 (G (s : ℂ))) := by
      rw [hG_pos hs_cb]
      exact hgX_pt ⟨(s : ℂ), hs_cb⟩
    have hρ_tend : Tendsto (fun m => r (ψ m) + (1 - r (ψ m)) * s) atTop (𝓝[<] 1) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun m => ?_⟩
      · have hsub : Tendsto (fun m => r (ψ m)) atTop (𝓝 1) :=
          hr_tend1.comp hψ_mono.tendsto_atTop
        have hcomb := hsub.add (((tendsto_const_nhds (x := (1 : ℝ))).sub hsub).mul_const s)
        simpa using hcomb
      · rw [mem_Iio]
        have hr1_lt := (hr_mem (ψ m)).2
        have hs_lt1 : s < 1 := hsα.trans_lt hα1
        nlinarith
    have h2 : Tendsto (fun m => F (ψ m) (s : ℂ)) atTop (𝓝 L) := by
      refine (hg₀_rad.comp hρ_tend).congr fun m => ?_
      dsimp only [Function.comp_def, F]
      push_cast
      rfl
    exact tendsto_nhds_unique h1 h2
  have hG_eq_L : ∀ u ∈ ball (0 : ℂ) R, G u = L := by
    by_contra hnot_eq
    have hne_zero : ¬ Set.EqOn (fun u => G u - L) 0 (ball (0 : ℂ) R) := by
      intro heq
      apply hnot_eq
      intro u hu
      exact sub_eq_zero.mp (heq hu)
    let K_seg : Set ℂ := Complex.ofReal '' Icc 0 α
    have hK_comp : IsCompact K_seg := isCompact_Icc.image Complex.continuous_ofReal
    have hK_sub : K_seg ⊆ ball (0 : ℂ) R := by
      rintro _ ⟨s, ⟨hs0, hsα⟩, rfl⟩
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
      exact hsα.trans_lt hα_lt_R
    have hreg : RudinRCA.Chapter10.IsRegion (ball (0 : ℂ) R) :=
      ⟨isOpen_ball, ⟨⟨0, mem_ball_self hR_pos⟩, (convex_ball 0 R).isPreconnected⟩⟩
    have hholo : RudinRCA.Chapter10.HolomorphicOn (fun u => G u - L) (ball (0 : ℂ) R) :=
      (RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn isOpen_ball).mpr
        (hG_diff.sub (differentiableOn_const L))
    have hfin := RudinRCA.Chapter10.zeroSet_inter_compact_finite hreg hholo hne_zero hK_comp hK_sub
    have hK_sub_zero : K_seg ⊆ RudinRCA.Chapter10.zeroSet (fun u => G u - L) (ball (0 : ℂ) R) ∩ K_seg := by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨⟨hK_sub ⟨s, hs, rfl⟩, sub_eq_zero.mpr (hG_real s hs)⟩, ⟨s, hs, rfl⟩⟩
    have hK_fin : K_seg.Finite := hfin.subset hK_sub_zero
    let seq : ℕ → ℂ := fun n => ((α / ((n : ℝ) + 2) : ℝ) : ℂ)
    have hseq_inj : Function.Injective seq := by
      intro m n hmn
      have hreal := Complex.ofReal_injective hmn
      have hm_pos : 0 < (m : ℝ) + 2 := by positivity
      have hn_pos : 0 < (n : ℝ) + 2 := by positivity
      rw [div_eq_div_iff hm_pos.ne' hn_pos.ne'] at hreal
      have : (m : ℝ) = (n : ℝ) := by nlinarith
      exact Nat.cast_injective this
    have hseq_mem : ∀ n : ℕ, seq n ∈ K_seg := by
      intro n
      refine ⟨α / ((n : ℝ) + 2), ⟨by positivity, ?_⟩, rfl⟩
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    exact (Set.infinite_of_injective_forall_mem hseq_inj hseq_mem) hK_fin
  -- Uniform convergence on `closedBall 0 R` contradicts `ε₀ ≤ ‖g₀ (z (φ (ψ m))) - L‖`
  obtain ⟨M_idx, hM_idx⟩ := (Metric.tendstoUniformlyOn_iff.mp hunif_cb (ε₀ / 2) (by positivity)).exists_forall_of_atTop
  have hw_ball_R : w (ψ M_idx) ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right]
    exact (hw_lt (ψ M_idx)).trans hα_lt_R
  have hw_cb_R : w (ψ M_idx) ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hw_ball_R
  have hdist_lt := hM_idx M_idx le_rfl (w (ψ M_idx)) hw_cb_R
  rw [hG_eq_L _ hw_ball_R, dist_eq_norm, norm_sub_rev] at hdist_lt
  have hF_eq_z : F (ψ M_idx) (w (ψ M_idx)) = g₀ (z (φ (ψ M_idx))) := by
    dsimp only [F]
    rw [← hz_decomp (ψ M_idx)]
  rw [hF_eq_z] at hdist_lt
  linarith [hφ_bad (ψ M_idx)]

/-- General Theorem 12.10 (Lindelöf's theorem at an arbitrary boundary point `ζ ∈ T` for raw
bounded holomorphic functions on `U`, giving both radial and nontangential limits, Rudin p. 259). -/
theorem theorem12_10_general {Γ : ℝ → ℂ} (hΓ_cont : ContinuousOn Γ (Icc 0 1))
    (hΓ_lt : ∀ t ∈ Ico (0 : ℝ) 1, ‖Γ t‖ < 1) {ζ : UnitCircle} (hΓ_end : Γ 1 = (ζ : ℂ))
    {g : ℂ → ℂ} (hg_holo : DifferentiableOn ℂ g (ball (0 : ℂ) 1))
    (hg_bdd : ∃ M : ℝ, ∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ M)
    {L : ℂ} (hlim : Tendsto (fun t : ℝ => g (Γ t)) (𝓝[<] 1) (𝓝 L)) :
    Tendsto (fun r : ℝ => g ((r : ℂ) * (ζ : ℂ))) (𝓝[<] 1) (𝓝 L) ∧
      HasNontangentialLimit g ζ L := by
  obtain ⟨M₀, hM₀⟩ := hg_bdd
  have hconj_mul : conj (ζ : ℂ) * (ζ : ℂ) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_unitCircle]; simp
  have hmul_conj : (ζ : ℂ) * conj (ζ : ℂ) = 1 := by rw [mul_comm, hconj_mul]
  let Γ_rot : ℝ → ℂ := fun t => conj (ζ : ℂ) * Γ t
  let g_rot : ℂ → ℂ := fun z => g ((ζ : ℂ) * z)
  have hΓ_rot_cont : ContinuousOn Γ_rot (Icc 0 1) :=
    continuousOn_const.mul hΓ_cont
  have hΓ_rot_lt : ∀ t ∈ Ico (0 : ℝ) 1, ‖Γ_rot t‖ < 1 := by
    intro t ht
    dsimp only [Γ_rot]
    rw [norm_mul, Complex.norm_conj, norm_unitCircle, one_mul]
    exact hΓ_lt t ht
  have hΓ_rot_one : Γ_rot 1 = 1 := by
    dsimp only [Γ_rot]
    rw [hΓ_end, hconj_mul]
  have hrot_maps : MapsTo (fun z : ℂ => (ζ : ℂ) * z) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    rw [mem_ball, dist_zero_right, norm_mul, norm_unitCircle, one_mul]
    simpa [mem_ball] using hz
  have hg_rot_holo : DifferentiableOn ℂ g_rot (ball (0 : ℂ) 1) :=
    hg_holo.comp (differentiableOn_id.const_mul (ζ : ℂ)) hrot_maps
  have hg_rot_bdd : ∃ M : ℝ, ∀ z ∈ ball (0 : ℂ) 1, ‖g_rot z‖ ≤ M :=
    ⟨M₀, fun z hz => hM₀ _ (hrot_maps hz)⟩
  have hlim_rot : Tendsto (fun t : ℝ => g_rot (Γ_rot t)) (𝓝[<] 1) (𝓝 L) := by
    refine hlim.congr fun t => ?_
    dsimp only [g_rot, Γ_rot]
    rw [← mul_assoc, hmul_conj, one_mul]
  have hrad_one := theorem12_10_radial_unitOne hΓ_rot_cont hΓ_rot_lt hΓ_rot_one
    hg_rot_holo hg_rot_bdd hlim_rot
  have hrad_ζ : Tendsto (fun r : ℝ => g ((r : ℂ) * (ζ : ℂ))) (𝓝[<] 1) (𝓝 L) := by
    refine hrad_one.congr fun r => ?_
    dsimp only [g_rot]
    rw [mul_comm]
  exact ⟨hrad_ζ, hasNontangentialLimit_of_radialLimit_boundedHolomorphic hg_holo ⟨M₀, hM₀⟩ ζ hrad_ζ⟩

/-- General `H^∞(U)` Lindelöf theorem at an arbitrary boundary point `ζ ∈ T` (both radial and
nontangential limits). -/
theorem theorem12_10_hInfty_general {Γ : ℝ → ℂ} (hΓ_cont : ContinuousOn Γ (Icc 0 1))
    (hΓ_lt : ∀ t ∈ Ico (0 : ℝ) 1, ‖Γ t‖ < 1) {ζ : UnitCircle} (hΓ_end : Γ 1 = (ζ : ℂ))
    (g : HInfty) {L : ℂ}
    (hlim : Tendsto (fun t : ℝ =>
      extendZero (g : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ) (Γ t)) (𝓝[<] 1) (𝓝 L)) :
    Tendsto (fun r : ℝ =>
      extendZero (g : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ) ((r : ℂ) * (ζ : ℂ)))
        (𝓝[<] 1) (𝓝 L) ∧
    HasNontangentialLimit
      (extendZero (g : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ)) ζ L := by
  let g_ext : ℂ → ℂ := extendZero (g : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ)
  have hg_bdd : ∃ M : ℝ, ∀ z ∈ ball (0 : ℂ) 1, ‖g_ext z‖ ≤ M := by
    refine ⟨‖g‖, fun z hz => ?_⟩
    dsimp only [g_ext]
    rw [extendZero_apply_of_mem _ hz]
    exact BoundedContinuousFunction.norm_coe_le_norm g.1 ⟨z, hz⟩
  exact theorem12_10_general hΓ_cont hΓ_lt hΓ_end g.2 hg_bdd hlim

/-- 12.10 (Lindelöf's Theorem, Rudin p. 259): suppose `Γ` is a curve with parameter interval
`[0, 1]` (`ContinuousOn Γ (Icc 0 1)`) such that `‖Γ(t)‖ < 1` if `0 ≤ t < 1` and `Γ(1) = 1`.
If `g ∈ H^∞` and `lim_{t → 1⁻} g(Γ(t)) = L`, then `g` has radial limit `L` at `1` and, moreover,
nontangential limit `L` at `1` (`HasNontangentialLimit`). -/
theorem theorem12_10 {Γ : ℝ → ℂ} (hΓ_cont : ContinuousOn Γ (Icc 0 1))
    (hΓ_lt : ∀ t ∈ Ico (0 : ℝ) 1, ‖Γ t‖ < 1) (hΓ_one : Γ 1 = 1)
    (g : HInfty) {L : ℂ}
    (hlim : Tendsto (fun t : ℝ =>
      extendZero (g : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ) (Γ t)) (𝓝[<] 1) (𝓝 L)) :
    Tendsto (fun r : ℝ =>
      extendZero (g : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ) (r : ℂ)) (𝓝[<] 1) (𝓝 L) ∧
    HasNontangentialLimit
      (extendZero (g : BoundedContinuousFunction (ball (0 : ℂ) 1) ℂ)) unitCircleOne L := by
  have h := theorem12_10_hInfty_general hΓ_cont hΓ_lt
    (ζ := unitCircleOne) (by simpa [coe_unitCircleOne] using hΓ_one) g hlim
  refine ⟨?_, h.2⟩
  simpa [coe_unitCircleOne] using h.1

end Node12_10
end RudinRCA.Chapter12

end
