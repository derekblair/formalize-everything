import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Liouville
import RudinRCA.Chapter10

/-!
# Rudin, Real and Complex Analysis, Chapter 12

The number labels refer to the third edition. `DifferentiableOn ℂ` on the
open sets below is equivalent to complex differentiability at every point.
The boundary maximum portion of 12.1, all of 12.2–12.9 (Schwarz's lemma, the
disk transformations `φ_α`, their mapping/inverse/derivative theorem, the
Schwarz–Pick extremal problem, the classification of disk automorphisms, the
unbounded-strip and sublinear-entire examples, Hadamard's three-lines theorem
with its logarithmic-convexity corollary, and the Phragmén–Lindelöf strip
theorem with its sharpness witness) are formalized here.
The radial-boundary-value assertion recalled in 12.1 and nodes 12.10–12.14
are not yet formalized.
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
