import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Chapter 11: Harmonic Functions

This module formalizes Chapter 11 of Rudin, *Real and Complex Analysis* (3rd ed., 1987),
retaining the weak harmonicity definition of 11.3 based on actual pure second partial
derivatives (and proving the reverse regularity equivalence in 11.10). It also records
the explicit Poisson kernel from 11.5(2), the failure of printed 11.5(4) at the
admitted endpoint `r = 0` (third edition, printed p. 233), the non-strict inequality
for `0 ≤ r < 1`, and the strict inequality with explicit `0 < r` hypothesis, together
with all remaining properties of 11.5.
-/

namespace RudinRCA.Chapter11

open Filter
open scoped Topology ComplexConjugate

/-- The operator ∂ from 11.1. Under real differentiability, the real
Fréchet derivative evaluated on `1` and `I` gives the two partial derivatives. -/
noncomputable def wirtinger (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) / 2

/-- The operator ∂̄ from 11.1, with the same partial-derivative convention. -/
noncomputable def wirtingerBar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / 2

/-- The evaluations used in 11.1 really are the directional partial derivatives. -/
theorem node11_1_partials {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    HasLineDerivAt ℝ f (fderiv ℝ f z 1) z 1 ∧
      HasLineDerivAt ℝ f (fderiv ℝ f z Complex.I) z Complex.I :=
  ⟨hf.hasFDerivAt.hasLineDerivAt 1, hf.hasFDerivAt.hasLineDerivAt Complex.I⟩

/-- The real differential in the complex-linear/antilinear coordinates of 11.1. -/
theorem node11_1_differential (f : ℂ → ℂ) (z h : ℂ) :
    fderiv ℝ f z h = wirtinger f z * h + wirtingerBar f z * conj h := by
  have he : h = h.re • (1 : ℂ) + h.im • Complex.I := by
    simp [Complex.real_smul, Complex.re_add_im]
  have hl : fderiv ℝ f z h = h.re • fderiv ℝ f z 1 +
      h.im • fderiv ℝ f z Complex.I := by
    calc
      fderiv ℝ f z h = fderiv ℝ f z (h.re • (1 : ℂ) + h.im • Complex.I) :=
        congrArg (fderiv ℝ f z) he
      _ = _ := by rw [map_add, map_smul, map_smul]
  rw [hl]
  unfold wirtinger wirtingerBar
  apply Complex.ext <;>
    simp [Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring

/-- Rudin 11.1's small-error expansion, translated to an arbitrary base point. -/
theorem node11_1_expansion {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    ∃ η : ℂ → ℂ, Tendsto η (𝓝 0) (𝓝 0) ∧
      ∀ h : ℂ, f (z + h) = f z + wirtinger f z * h +
        wirtingerBar f z * conj h + η h * h := by
  let η : ℂ → ℂ := fun h ↦ (f (z + h) - f z - fderiv ℝ f z h) / h
  refine ⟨η, ?_, ?_⟩
  · exact (hasFDerivAt_iff_isLittleO_nhds_zero.mp hf.hasFDerivAt).tendsto_div_nhds_zero
  · intro h
    by_cases hh : h = 0
    · simp [hh]
    · dsimp [η]
      rw [div_mul_cancel₀ _ hh, node11_1_differential]
      ring

/-- Conversely, the small-error representation in 11.1 supplies a real differential. -/
theorem node11_1_differentiable_iff_expansion {f : ℂ → ℂ} {z : ℂ} :
    DifferentiableAt ℝ f z ↔
      ∃ η : ℂ → ℂ, Tendsto η (𝓝 0) (𝓝 0) ∧
        ∀ h : ℂ, f (z + h) = f z + wirtinger f z * h +
          wirtingerBar f z * conj h + η h * h := by
  refine ⟨node11_1_expansion, ?_⟩
  rintro ⟨η, hη, he⟩
  apply HasFDerivAt.differentiableAt (f' := fderiv ℝ f z)
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  have heq : (fun h ↦ f (z + h) - f z - fderiv ℝ f z h) =
      (fun h ↦ η h * h) := by
    funext h
    rw [he h, node11_1_differential]
    ring
  rw [heq]
  simpa only [one_mul] using
    ((Asymptotics.isLittleO_one_iff ℂ).mpr hη).mul_isBigO
      (Asymptotics.isBigO_refl (fun h : ℂ ↦ h) (𝓝 0))

/-- The quotient identity 11.1(4), without the harmless normalization `f(z)=z=0`. -/
theorem node11_1_quotient {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    ∃ η : ℂ → ℂ, Tendsto η (𝓝 0) (𝓝 0) ∧
      ∀ h : ℂ, h ≠ 0 → (f (z + h) - f z) / h =
        wirtinger f z + wirtingerBar f z * (conj h / h) + η h := by
  obtain ⟨η, hη, he⟩ := node11_1_expansion hf
  refine ⟨η, hη, fun h hh ↦ ?_⟩
  rw [he h]
  field_simp
  ring

theorem wirtingerBar_eq_zero_iff (f : ℂ → ℂ) (z : ℂ) :
    wirtingerBar f z = 0 ↔
      fderiv ℝ f z Complex.I = Complex.I * fderiv ℝ f z 1 := by
  unfold wirtingerBar
  rw [div_eq_zero_iff]
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  simp only [htwo, or_false]
  constructor
  · intro h
    have hx := eq_neg_of_add_eq_zero_left h
    rw [hx]
    simp [← mul_assoc]
  · intro h
    rw [h]
    simp [← mul_assoc]

/-- The pointwise complex-differentiability conclusion of 11.1. -/
theorem node11_1_complex_differentiable_iff {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℂ f z ↔ wirtingerBar f z = 0 := by
  rw [wirtingerBar_eq_zero_iff, differentiableAt_complex_iff_differentiableAt_real]
  simp only [hf, true_and, smul_eq_mul]

/-- Rudin 11.2, the Cauchy–Riemann characterization on an open set. -/
theorem node11_2_holomorphic_iff {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : ∀ z ∈ Ω, DifferentiableAt ℝ f z) :
    DifferentiableOn ℂ f Ω ↔ ∀ z ∈ Ω, wirtingerBar f z = 0 := by
  constructor
  · intro h z hz
    apply (wirtingerBar_eq_zero_iff f z).2
    exact (differentiableAt_complex_iff_differentiableAt_real.mp
      (h.differentiableAt (hΩ.mem_nhds hz))).2
  · intro h z hz
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_complex_iff_differentiableAt_real.mpr
    exact ⟨hf z hz, (wirtingerBar_eq_zero_iff f z).mp (h z hz)⟩

/-- Rudin 11.2, the derivative agrees with ∂ on the holomorphic set. -/
theorem node11_2_deriv {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) {z : ℂ} (hz : z ∈ Ω) :
    deriv f z = wirtinger f z := by
  have h := differentiableAt_complex_iff_differentiableAt_real.mp
    (hf.differentiableAt (hΩ.mem_nhds hz))
  rw [complexOfReal_deriv h.1 h.2]
  unfold wirtinger
  rw [h.2]
  simp only [smul_eq_mul, ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul, sub_neg_eq_add]
  ring

section Harmonic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The `x` partial derivative, defined using a real one-variable derivative. -/
noncomputable def partialX (f : ℂ → F) (z : ℂ) : F := lineDeriv ℝ f z 1

/-- The `y` partial derivative, defined using a real one-variable derivative. -/
noncomputable def partialY (f : ℂ → F) (z : ℂ) : F := lineDeriv ℝ f z Complex.I

/-- Rudin 11.3's sum of the two pure second partial derivatives. -/
noncomputable def laplacian (f : ℂ → F) (z : ℂ) : F :=
  partialX (partialX f) z + partialY (partialY f) z

/-- Existence of the first and pure second partials, without a C² hypothesis. -/
structure HasPureSecondPartialsAt (f : ℂ → F) (z : ℂ) : Prop where
  first_x : LineDifferentiableAt ℝ f z 1
  first_y : LineDifferentiableAt ℝ f z Complex.I
  second_x : LineDifferentiableAt ℝ (partialX f) z 1
  second_y : LineDifferentiableAt ℝ (partialY f) z Complex.I

/-- The harmonicity definition of 11.3. In particular this definition does
not assume `ContDiffOn`, continuity of the partials, or existence of mixed partials. -/
structure HarmonicOn (f : ℂ → F) (Ω : Set ℂ) : Prop where
  continuousOn : ContinuousOn f Ω
  partials : ∀ z ∈ Ω, HasPureSecondPartialsAt f z
  laplacian_zero : ∀ z ∈ Ω, laplacian f z = 0

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem hasLineDerivAt_comp_clm {f : ℂ → F} {f' : F} {z v : ℂ}
    (h : HasLineDerivAt ℝ f f' z v) (L : F →L[ℝ] G) :
    HasLineDerivAt ℝ (L ∘ f) (L f') z v := by
  simpa only [HasLineDerivAt, Function.comp_def] using
    L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem secondPartial_comp_clm {f : ℂ → F} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {z v w : ℂ} (hz : z ∈ Ω)
    (hfirst : ∀ a ∈ Ω, LineDifferentiableAt ℝ f a v)
    (hsecond : LineDifferentiableAt ℝ (fun a ↦ lineDeriv ℝ f a v) z w)
    (L : F →L[ℝ] G) :
    HasLineDerivAt ℝ (fun a ↦ lineDeriv ℝ (L ∘ f) a v)
      (L (lineDeriv ℝ (fun a ↦ lineDeriv ℝ f a v) z w)) z w := by
  apply (hasLineDerivAt_comp_clm hsecond.hasLineDerivAt L).congr_of_eventuallyEq
  filter_upwards [hΩ.mem_nhds hz] with a ha
  exact (hasLineDerivAt_comp_clm (hfirst a ha).hasLineDerivAt L).lineDeriv

theorem laplacian_comp_clm {f : ℂ → F} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : ∀ a ∈ Ω, HasPureSecondPartialsAt f a) (L : F →L[ℝ] G)
    {z : ℂ} (hz : z ∈ Ω) : laplacian (L ∘ f) z = L (laplacian f z) := by
  unfold laplacian partialX partialY
  rw [(secondPartial_comp_clm hΩ hz (fun a ha ↦ (hf a ha).first_x)
    (hf z hz).second_x L).lineDeriv,
    (secondPartial_comp_clm hΩ hz (fun a ha ↦ (hf a ha).first_y)
    (hf z hz).second_y L).lineDeriv, map_add]

theorem HarmonicOn.comp_clm {f : ℂ → F} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : HarmonicOn f Ω) (L : F →L[ℝ] G) : HarmonicOn (L ∘ f) Ω where
  continuousOn := L.continuous.comp_continuousOn hf.continuousOn
  partials z hz := {
    first_x := (hasLineDerivAt_comp_clm
      (hf.partials z hz).first_x.hasLineDerivAt L).lineDifferentiableAt
    first_y := (hasLineDerivAt_comp_clm
      (hf.partials z hz).first_y.hasLineDerivAt L).lineDifferentiableAt
    second_x := (secondPartial_comp_clm hΩ hz (fun a ha ↦ (hf.partials a ha).first_x)
      (hf.partials z hz).second_x L).lineDifferentiableAt
    second_y := (secondPartial_comp_clm hΩ hz (fun a ha ↦ (hf.partials a ha).first_y)
      (hf.partials z hz).second_y L).lineDifferentiableAt }
  laplacian_zero z hz := by rw [laplacian_comp_clm hΩ hf.partials L hz, hf.laplacian_zero z hz,
    map_zero]

/-- A C² function's iterated directional partials are obtained from its
second Fréchet derivative. Only this direction of the regularity bridge is used. -/
theorem hasLineDerivAt_lineDeriv_of_contDiffAt {f : ℂ → F} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (v w : ℂ) :
    HasLineDerivAt ℝ (fun a ↦ lineDeriv ℝ f a v)
      ((fderiv ℝ (fderiv ℝ f) z w) v) z w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : (fun a ↦ lineDeriv ℝ f a v) =ᶠ[𝓝 z]
      (fun a ↦ fderiv ℝ f a v) := by
    filter_upwards [hf.eventually (by norm_num)] with a ha
    exact (ha.differentiableAt (by norm_num)).lineDeriv_eq_fderiv
  have hl := ((hd.clm_apply (differentiableAt_const v)).hasFDerivAt.hasLineDerivAt w)
  have hvalue : fderiv ℝ (fun a ↦ (fderiv ℝ f a) v) z w =
      (fderiv ℝ (fderiv ℝ f) z w) v := by
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  rw [hvalue] at hl
  exact hl.congr_of_eventuallyEq he

theorem pureSecondPartials_of_contDiffAt {f : ℂ → F} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) : HasPureSecondPartialsAt f z where
  first_x := (hf.differentiableAt (by norm_num)).lineDifferentiableAt
  first_y := (hf.differentiableAt (by norm_num)).lineDifferentiableAt
  second_x := (hasLineDerivAt_lineDeriv_of_contDiffAt hf 1 1).lineDifferentiableAt
  second_y :=
    (hasLineDerivAt_lineDeriv_of_contDiffAt hf Complex.I Complex.I).lineDifferentiableAt

/-- Agreement with Mathlib's Laplacian for C² functions, without changing
the weaker book definition of harmonicity. -/
theorem laplacian_eq_mathlib_of_contDiffAt {f : ℂ → F} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) : laplacian f z = Laplacian.laplacian f z := by
  unfold laplacian partialX partialY
  rw [(hasLineDerivAt_lineDeriv_of_contDiffAt hf 1 1).lineDeriv,
    (hasLineDerivAt_lineDeriv_of_contDiffAt hf Complex.I Complex.I).lineDeriv]
  simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply]

/-- Mathlib harmonicity implies the definition in 11.3. No converse is assumed. -/
theorem harmonicOn_of_mathlib {f : ℂ → F} {Ω : Set ℂ}
    (hf : InnerProductSpace.HarmonicOnNhd f Ω) : HarmonicOn f Ω where
  continuousOn := fun z hz ↦ (hf z hz).1.continuousAt.continuousWithinAt
  partials := fun z hz ↦ pureSecondPartials_of_contDiffAt (hf z hz).1
  laplacian_zero := fun z hz ↦ by
    rw [laplacian_eq_mathlib_of_contDiffAt (hf z hz).1]
    exact (hf z hz).2.eq_of_nhds

end Harmonic

/-- The real/imaginary characterization in 11.3, under that node's standing
assumption that the pure second partial derivatives exist throughout the open set. -/
theorem node11_3_components {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : ∀ z ∈ Ω, HasPureSecondPartialsAt f z) :
    HarmonicOn f Ω ↔ HarmonicOn (fun z ↦ (f z).re) Ω ∧
      HarmonicOn (fun z ↦ (f z).im) Ω := by
  constructor
  · intro h
    exact ⟨h.comp_clm hΩ Complex.reCLM, h.comp_clm hΩ Complex.imCLM⟩
  · rintro ⟨hr, hi⟩
    refine ⟨?_, hf, ?_⟩
    · have he : f = fun z ↦ (f z).re + (f z).im * Complex.I := by
        funext z
        exact (Complex.re_add_im (f z)).symm
      rw [he]
      exact (Complex.continuous_ofReal.comp_continuousOn hr.continuousOn).add
        ((Complex.continuous_ofReal.comp_continuousOn hi.continuousOn).mul_const Complex.I)
    · intro z hz
      apply Complex.ext
      · have he := laplacian_comp_clm hΩ hf Complex.reCLM hz
        exact he.symm.trans (hr.laplacian_zero z hz)
      · have he := laplacian_comp_clm hΩ hf Complex.imCLM hz
        exact he.symm.trans (hi.laplacian_zero z hz)

/-- The two real equations accompanying 11.2, with actual directional partials. -/
theorem node11_2_real_imag {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    wirtingerBar f z = 0 ↔
      partialX (fun a ↦ (f a).re) z = partialY (fun a ↦ (f a).im) z ∧
      partialY (fun a ↦ (f a).re) z = -partialX (fun a ↦ (f a).im) z := by
  unfold partialX partialY
  have hr (v : ℂ) : lineDeriv ℝ (fun a ↦ (f a).re) z v = (fderiv ℝ f z v).re := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      (hasLineDerivAt_comp_clm (hf.hasFDerivAt.hasLineDerivAt v) Complex.reCLM).lineDeriv
  have hi (v : ℂ) : lineDeriv ℝ (fun a ↦ (f a).im) z v = (fderiv ℝ f z v).im := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      (hasLineDerivAt_comp_clm (hf.hasFDerivAt.hasLineDerivAt v) Complex.imCLM).lineDeriv
  rw [hr, hi, hr, hi, wirtingerBar_eq_zero_iff, Complex.ext_iff]
  simp [Complex.mul_re, Complex.mul_im, eq_comm, and_comm]

/-- The operator ∂ on functions with directional partials, without assuming
a real Fréchet derivative. It agrees with the 11.1 definition where the latter is used. -/
noncomputable def wirtingerPartial (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (partialX f z - Complex.I * partialY f z) / 2

/-- The corresponding partial-derivative operator ∂̄. -/
noncomputable def wirtingerBarPartial (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (partialX f z + Complex.I * partialY f z) / 2

theorem wirtinger_eq_partial {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    wirtinger f z = wirtingerPartial f z ∧
      wirtingerBar f z = wirtingerBarPartial f z := by
  simp [wirtinger, wirtingerBar, wirtingerPartial, wirtingerBarPartial,
    partialX, partialY, hf.lineDeriv_eq_fderiv]

/-- Rudin 11.3(3). Mixed partials are assumed to exist and commute, exactly
as required by the displayed operator identity; C² regularity is not substituted. -/
theorem node11_3_laplacian_wirtinger {f : ℂ → ℂ} {z : ℂ}
    (hxx : LineDifferentiableAt ℝ (partialX f) z 1)
    (hxy : LineDifferentiableAt ℝ (partialX f) z Complex.I)
    (hyx : LineDifferentiableAt ℝ (partialY f) z 1)
    (hyy : LineDifferentiableAt ℝ (partialY f) z Complex.I)
    (hmixed : partialX (partialY f) z = partialY (partialX f) z) :
    laplacian f z = 4 * wirtingerPartial (wirtingerBarPartial f) z := by
  have hxx' : HasDerivAt (fun t : ℝ ↦ partialX f (z + t • (1 : ℂ)))
      (partialX (partialX f) z) 0 := hxx.hasLineDerivAt
  have hyx' : HasDerivAt (fun t : ℝ ↦ partialY f (z + t • (1 : ℂ)))
      (partialX (partialY f) z) 0 := hyx.hasLineDerivAt
  have hxy' : HasDerivAt (fun t : ℝ ↦ partialX f (z + t • Complex.I))
      (partialY (partialX f) z) 0 := hxy.hasLineDerivAt
  have hyy' : HasDerivAt (fun t : ℝ ↦ partialY f (z + t • Complex.I))
      (partialY (partialY f) z) 0 := hyy.hasLineDerivAt
  have hx : partialX (wirtingerBarPartial f) z =
      (partialX (partialX f) z + Complex.I * partialX (partialY f) z) / 2 :=
    ((hxx'.add (hyx'.const_mul Complex.I)).div_const 2).deriv
  have hy : partialY (wirtingerBarPartial f) z =
      (partialY (partialX f) z + Complex.I * partialY (partialY f) z) / 2 :=
    ((hxy'.add (hyy'.const_mul Complex.I)).div_const 2).deriv
  unfold laplacian wirtingerPartial
  rw [hx, hy, hmixed]
  ring_nf
  simp [Complex.I_sq]

/-- The mixed-partial commutation assertion used in 11.3 holds for C² functions. -/
theorem node11_3_mixed_partials {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) :
    partialX (partialY f) z = partialY (partialX f) z := by
  unfold partialX partialY
  rw [(hasLineDerivAt_lineDeriv_of_contDiffAt hf Complex.I 1).lineDeriv,
    (hasLineDerivAt_lineDeriv_of_contDiffAt hf 1 Complex.I).lineDeriv]
  exact hf.isSymmSndFDerivAt (by norm_num) 1 Complex.I

/-- Rudin 11.4, with exactly the weak harmonicity definition of 11.3. -/
theorem node11_4_holomorphic_harmonic {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) : HarmonicOn f Ω := by
  apply harmonicOn_of_mathlib
  intro z hz
  exact (hf.analyticAt (hΩ.mem_nhds hz)).harmonicAt

/-- The real Poisson kernel, in the closed form of 11.5(2).
The book's intended parameter range is `0 ≤ r < 1`. -/
noncomputable def poissonKernel (r t : ℝ) : ℝ :=
  (1 - r ^ 2) / (1 - 2 * r * Real.cos t + r ^ 2)

/-- At radius zero the Poisson kernel is constant. -/
@[simp] theorem poissonKernel_zero (t : ℝ) : poissonKernel 0 t = 1 := by
  simp [poissonKernel]

/-- Explicit counterexample to the strict inequality printed as 11.5(4).
All of its stated parameter constraints hold at `(r, δ, t) = (0, 1, 2)`. -/
theorem node11_5_strict_inequality_counterexample :
    (0 : ℝ) ≤ 0 ∧ (0 : ℝ) < 1 ∧
      (0 : ℝ) < 1 ∧ (1 : ℝ) < |(2 : ℝ)| ∧ |(2 : ℝ)| ≤ Real.pi ∧
      ¬ poissonKernel 0 2 < poissonKernel 0 1 := by
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2), poissonKernel_zero]
  simpa only [true_and, and_true] using Real.two_le_pi

/-- Corrected strict form of 11.5(4), with its additional hypothesis explicit.
This is a correction, not a proof of the printed endpoint claim. -/
theorem node11_5_strict_inequality_corrected {r δ t : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hδ : 0 < δ)
    (hδt : δ < |t|) (ht : |t| ≤ Real.pi) :
    poissonKernel r t < poissonKernel r δ := by
  have hcos : Real.cos t < Real.cos δ := by
    simpa only [Real.cos_abs] using
      Real.cos_lt_cos_of_nonneg_of_le_pi hδ.le ht hδt
  have hnum : 0 < 1 - r ^ 2 := by nlinarith
  have hdenδ : 0 < 1 - 2 * r * Real.cos δ + r ^ 2 := by
    have := Real.cos_le_one δ
    nlinarith [sq_pos_of_pos (sub_pos.mpr hr1)]
  have hdent : 0 < 1 - 2 * r * Real.cos t + r ^ 2 := by
    have := Real.cos_le_one t
    nlinarith [sq_pos_of_pos (sub_pos.mpr hr1)]
  unfold poissonKernel
  apply (div_lt_div_iff₀ hdent hdenδ).2
  nlinarith [mul_pos hr (sub_pos.mpr hcos)]

/-! ### Batch 11A: Nodes 11.5, 11.6, 11.7, 11.8, and 11.15 -/

section OpenCongr

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem HarmonicOn.mono {f : ℂ → F} {Ω₁ Ω₂ : Set ℂ} (hsub : Ω₁ ⊆ Ω₂)
    (hf : HarmonicOn f Ω₂) : HarmonicOn f Ω₁ where
  continuousOn := hf.continuousOn.mono hsub
  partials z hz := hf.partials z (hsub hz)
  laplacian_zero z hz := hf.laplacian_zero z (hsub hz)

theorem HarmonicOn.congr_of_isOpen {f₁ f₂ : ℂ → F} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (heq : Set.EqOn f₁ f₂ Ω) (hf₁ : HarmonicOn f₁ Ω) : HarmonicOn f₂ Ω := by
  have hline : ∀ {g₁ g₂ : ℂ → F} {z v : ℂ}, g₁ =ᶠ[nhds z] g₂ →
      (fun t : ℝ => g₁ (z + t • v)) =ᶠ[nhds (0 : ℝ)] (fun t : ℝ => g₂ (z + t • v)) := by
    intro g₁ g₂ z v hgev
    have hcont : Continuous (fun t : ℝ => z + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have h0 : z + (0 : ℝ) • v = z := by simp
    exact hcont.continuousAt.eventually (h0.symm ▸ hgev)
  have hpx_eq : ∀ z ∈ Ω, partialX f₂ z = partialX f₁ z := by
    intro z hz
    unfold partialX lineDeriv
    exact Filter.EventuallyEq.deriv_eq
      (hline (Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ω, hΩ.mem_nhds hz, fun w hw => (heq hw).symm⟩))
  have hpy_eq : ∀ z ∈ Ω, partialY f₂ z = partialY f₁ z := by
    intro z hz
    unfold partialY lineDeriv
    exact Filter.EventuallyEq.deriv_eq
      (hline (Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ω, hΩ.mem_nhds hz, fun w hw => (heq hw).symm⟩))
  refine ⟨hf₁.continuousOn.congr fun z hz => (heq hz).symm, ?_, ?_⟩
  · intro z hz
    have hf_ev : f₂ =ᶠ[nhds z] f₁ :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ω, hΩ.mem_nhds hz, fun w hw => (heq hw).symm⟩
    have hpx_ev : partialX f₂ =ᶠ[nhds z] partialX f₁ :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ω, hΩ.mem_nhds hz, hpx_eq⟩
    have hpy_ev : partialY f₂ =ᶠ[nhds z] partialY f₁ :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ω, hΩ.mem_nhds hz, hpy_eq⟩
    exact {
      first_x := ((hf₁.partials z hz).first_x.hasLineDerivAt.congr_of_eventuallyEq
        hf_ev).lineDifferentiableAt
      first_y := ((hf₁.partials z hz).first_y.hasLineDerivAt.congr_of_eventuallyEq
        hf_ev).lineDifferentiableAt
      second_x := ((hf₁.partials z hz).second_x.hasLineDerivAt.congr_of_eventuallyEq
        hpx_ev).lineDifferentiableAt
      second_y := ((hf₁.partials z hz).second_y.hasLineDerivAt.congr_of_eventuallyEq
        hpy_ev).lineDifferentiableAt }
  · intro z hz
    have hpx_ev : partialX f₂ =ᶠ[nhds z] partialX f₁ :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ω, hΩ.mem_nhds hz, hpx_eq⟩
    have hpy_ev : partialY f₂ =ᶠ[nhds z] partialY f₁ :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ω, hΩ.mem_nhds hz, hpy_eq⟩
    unfold laplacian partialX partialY lineDeriv
    have hxx : deriv (fun t : ℝ => partialX f₂ (z + t • (1 : ℂ))) 0 =
        deriv (fun t : ℝ => partialX f₁ (z + t • (1 : ℂ))) 0 :=
      Filter.EventuallyEq.deriv_eq (hline hpx_ev)
    have hyy : deriv (fun t : ℝ => partialY f₂ (z + t • Complex.I)) 0 =
        deriv (fun t : ℝ => partialY f₁ (z + t • Complex.I)) 0 :=
      Filter.EventuallyEq.deriv_eq (hline hpy_ev)
    exact (congr_arg₂ (· + ·) hxx hyy).trans (hf₁.laplacian_zero z hz)

end OpenCongr

section Node11_5

private theorem poissonKernel_den_pos {r : ℝ} (_hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    0 < 1 - 2 * r * Real.cos t + r ^ 2 := by
  have hc := Real.cos_le_one t
  nlinarith [sq_pos_of_pos (sub_pos.mpr hr1)]

theorem norm_sq_one_sub_polar (r t : ℝ) :
    ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ ^ 2 =
      1 - 2 * r * Real.cos t + r ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.exp_ofReal_mul_I]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- Bridge between Mathlib's 3-argument `_root_.poissonKernel 0 w ζ` on the unit circle and
Rudin's closed-form `poissonKernel r (θ - t)` (`w = r e^{iθ}`, `ζ = e^{it}`). -/
theorem poissonKernel_eq_mathlib {r : ℝ} (hr0 : 0 ≤ r) (θ t : ℝ) :
    _root_.poissonKernel 0 ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) (circleMap 0 1 t) =
      poissonKernel r (θ - t) := by
  rw [_root_.poissonKernel_def]
  simp only [sub_zero]
  have hcm : circleMap 0 1 t = Complex.exp ((t : ℂ) * Complex.I) := by
    simp [circleMap]
  have hnorm_cm : ‖circleMap 0 1 t‖ = 1 := by simp [circleMap]
  have hnorm_w : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hdiff : circleMap 0 1 t - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) =
      Complex.exp ((t : ℂ) * Complex.I) *
        (1 - (r : ℂ) * Complex.exp (((θ - t : ℝ) : ℂ) * Complex.I)) := by
    rw [hcm, mul_sub, mul_one, ← mul_assoc, mul_comm (Complex.exp _) (r : ℂ), mul_assoc,
      ← Complex.exp_add]
    congr 3
    push_cast
    ring
  rw [hnorm_cm, hnorm_w, one_pow, hdiff, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    norm_sq_one_sub_polar]
  rfl

/-- 11.5: Herglotz quotient real-part identity `Re ((1 + r e^{it}) / (1 - r e^{it})) = P_r(t)`. -/
theorem node11_5_herglotz_re {r : ℝ} (hr0 : 0 ≤ r) (_hr1 : r < 1) (t : ℝ) :
    ((1 + (r : ℂ) * Complex.exp (Complex.I * (t : ℂ))) /
      (1 - (r : ℂ) * Complex.exp (Complex.I * (t : ℂ)))).re = poissonKernel r t := by
  have heq : Complex.I * (t : ℂ) = (t : ℂ) * Complex.I := mul_comm _ _
  rw [heq]
  have h := congr_fun (poissonKernel_eq_re_herglotzRieszKernel
    (c := 0) (w := (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I))) 1
  simp only [Function.comp_apply, herglotzRieszKernel_def, sub_zero] at h
  have hcm0 : circleMap 0 1 0 = (1 : ℂ) := by simp [circleMap]
  rw [← h, ← hcm0, poissonKernel_eq_mathlib hr0 t 0, sub_zero]

private def intEquivNatSumNat : ℕ ⊕ ℕ ≃ ℤ where
  toFun := Sum.elim Int.ofNat Int.negSucc
  invFun
    | Int.ofNat n => Sum.inl n
    | Int.negSucc n => Sum.inr n
  left_inv := by rintro (n | n) <;> rfl
  right_inv := by rintro (n | n) <;> rfl

/-- 11.5(1): Fourier series representation `P_r(t) = ∑_{n ∈ ℤ} r^{|n|} e^{i n t}` for `0 ≤ r < 1`. -/
theorem node11_5_hasSum_fourier {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    HasSum (fun n : ℤ => (r : ℂ) ^ n.natAbs * Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)))
      (poissonKernel r t : ℂ) := by
  let q : ℂ := (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)
  let p : ℂ := (r : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)
  have hq_norm : ‖q‖ < 1 := by
    dsimp [q]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hr1
  have hp_norm : ‖p‖ < 1 := by
    dsimp [p]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hr1
  have hq_ne : 1 - q ≠ 0 := fun h => hq_norm.ne (by rw [← sub_eq_zero.mp h, norm_one])
  have hp_ne : 1 - p ≠ 0 := fun h => hp_norm.ne (by rw [← sub_eq_zero.mp h, norm_one])
  have hsum_inl : HasSum (fun n : ℕ => q ^ n) (1 - q)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hq_norm
  have hsum_inr : HasSum (fun n : ℕ => p ^ (n + 1)) (p * (1 - p)⁻¹) := by
    simpa only [pow_succ'] using (hasSum_geometric_of_norm_lt_one hp_norm).mul_left p
  let g : ℤ → ℂ := fun n => (r : ℂ) ^ n.natAbs * Complex.exp (Complex.I * (n : ℂ) * (t : ℂ))
  have hinl_eq : g ∘ intEquivNatSumNat ∘ Sum.inl = fun n : ℕ => q ^ n := by
    funext n
    change g (n : ℤ) = q ^ n
    simp only [g, q, Int.natAbs_natCast, Int.cast_natCast, mul_pow, ← Complex.exp_nat_mul]
    congr 2
    ring
  have hinr_eq : g ∘ intEquivNatSumNat ∘ Sum.inr = fun n : ℕ => p ^ (n + 1) := by
    funext n
    change g (Int.negSucc n) = p ^ (n + 1)
    simp only [g, p, Int.natAbs_negSucc, Int.cast_negSucc, mul_pow, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hsum_Z : HasSum g ((1 - q)⁻¹ + p * (1 - p)⁻¹) := by
    rw [← Equiv.hasSum_iff intEquivNatSumNat]
    exact HasSum.sum (hinl_eq.symm ▸ hsum_inl) (hinr_eq.symm ▸ hsum_inr)
  have hqp : q * p = ((r ^ 2 : ℝ) : ℂ) := by
    dsimp [q, p]
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    have h0 : (t : ℂ) * Complex.I + ((-t : ℝ) : ℂ) * Complex.I = 0 := by push_cast; ring
    rw [h0, Complex.exp_zero, mul_one]
    push_cast
    ring
  have hq_add_p : q + p = ((2 * r * Real.cos t : ℝ) : ℂ) := by
    dsimp [q, p]
    rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  have hden_eq : (1 - q) * (1 - p) = ((1 - 2 * r * Real.cos t + r ^ 2 : ℝ) : ℂ) := by
    calc (1 - q) * (1 - p) = 1 - (q + p) + q * p := by ring
      _ = 1 - ((2 * r * Real.cos t : ℝ) : ℂ) + ((r ^ 2 : ℝ) : ℂ) := by rw [hq_add_p, hqp]
      _ = ((1 - 2 * r * Real.cos t + r ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hval_eq : (1 - q)⁻¹ + p * (1 - p)⁻¹ = (poissonKernel r t : ℂ) := by
    have h1 : (1 - q)⁻¹ + p * (1 - p)⁻¹ = (1 - q * p) / ((1 - q) * (1 - p)) := by
      field_simp [hq_ne, hp_ne]
      ring
    rw [h1, hqp, hden_eq]
    unfold poissonKernel
    push_cast
    rfl
  exact hval_eq ▸ hsum_Z

/-- 11.5: positivity `0 < P_r(t)` for `0 ≤ r < 1` and all `t ∈ ℝ`. -/
theorem node11_5_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    0 < poissonKernel r t :=
  div_pos (by nlinarith) (poissonKernel_den_pos hr0 hr1 t)

/-- 11.5: parity `P_r(-t) = P_r(t)`. -/
theorem node11_5_even (r t : ℝ) : poissonKernel r (-t) = poissonKernel r t := by
  simp [poissonKernel, Real.cos_neg]

/-- 11.5: `2π`-periodicity of `P_r`. -/
theorem node11_5_periodic (r : ℝ) : Function.Periodic (poissonKernel r) (2 * Real.pi) := by
  intro t
  simp [poissonKernel, Real.cos_add_two_pi]

theorem continuous_poissonKernel {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (poissonKernel r) := by
  unfold poissonKernel
  refine continuous_const.div ?_ (fun t => (poissonKernel_den_pos hr0 hr1 t).ne')
  exact (continuous_const.sub (continuous_const.mul Real.continuous_cos)).add continuous_const

/-- 11.5: sharp radial bounds `(1 - r) / (1 + r) ≤ P_r(t) ≤ (1 + r) / (1 - r)`. -/
theorem node11_5_bounds {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    (1 - r) / (1 + r) ≤ poissonKernel r t ∧ poissonKernel r t ≤ (1 + r) / (1 - r) := by
  have hden : 0 < 1 - 2 * r * Real.cos t + r ^ 2 := poissonKernel_den_pos hr0 hr1 t
  have h1pr : 0 < 1 + r := by linarith
  have h1mr : 0 < 1 - r := by linarith
  unfold poissonKernel
  refine ⟨(div_le_div_iff₀ h1pr hden).mpr ?_, (div_le_div_iff₀ hden h1mr).mpr ?_⟩
  · nlinarith [Real.neg_one_le_cos t, mul_nonneg hr0 h1mr.le]
  · nlinarith [Real.cos_le_one t, mul_nonneg hr0 h1mr.le]

/-- 11.5(3): normalization `(2π)⁻¹ ∫_{-π}^π P_r(t) dt = 1` (and over `[0, 2π]`) for `0 ≤ r < 1`. -/
theorem node11_5_integral_eq_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (2 * Real.pi)⁻¹ * (∫ t in (-Real.pi)..Real.pi, poissonKernel r t) = 1 ∧
    (2 * Real.pi)⁻¹ * (∫ t in (0 : ℝ)..(2 * Real.pi), poissonKernel r t) = 1 := by
  have hw : (r : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hconst : DiffContOnCl ℂ (fun _ : ℂ => (1 : ℂ)) (Metric.ball (0 : ℂ) 1) :=
    ⟨differentiableOn_const 1, continuousOn_const⟩
  have hpif := hconst.circleAverage_poissonKernel_smul hw
  have hci : CircleIntegrable (_root_.poissonKernel 0 (r : ℂ) • fun _ : ℂ => (1 : ℂ)) 0 1 := by
    have hr_not : (r : ℂ) ∉ Metric.sphere (0 : ℂ) |(1 : ℝ)| := by
      rw [abs_of_pos zero_lt_one, Metric.mem_sphere, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hr0]
      exact hr1.ne
    have hcont_k : ContinuousOn (_root_.poissonKernel 0 (r : ℂ)) (Metric.sphere 0 1) := by
      have hk := Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hr_not)
      rw [← poissonKernel_eq_re_herglotzRieszKernel, abs_of_pos zero_lt_one] at hk
      exact hk
    exact (hcont_k.smul continuousOn_const).circleIntegrable zero_le_one
  have hre1 : (Real.circleAverage (_root_.poissonKernel 0 (r : ℂ) • fun _ : ℂ => (1 : ℂ)) 0 1).re = 1 := by
    rw [hpif, Complex.one_re]
  have hre : Real.circleAverage
      (Complex.reCLM ∘ (_root_.poissonKernel 0 (r : ℂ) • fun _ : ℂ => (1 : ℂ))) 0 1 = 1 :=
    (Complex.reCLM.circleAverage_comp_comm hci).trans hre1
  have h0_2pi : (2 * Real.pi)⁻¹ * (∫ t in (0 : ℝ)..(2 * Real.pi), poissonKernel r t) = 1 := by
    rw [Real.circleAverage_def, smul_eq_mul] at hre
    refine (congr_arg ((2 * Real.pi)⁻¹ * ·) (intervalIntegral.integral_congr fun t _ => ?_)).trans hre
    have hpt := poissonKernel_eq_mathlib hr0 0 t
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, zero_sub,
      node11_5_even] at hpt
    simp [Function.comp_apply, Complex.real_smul, hpt]
  have hper := (node11_5_periodic r).intervalIntegral_add_eq (-Real.pi) 0
  have hend1 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have hend2 : (0 : ℝ) + 2 * Real.pi = 2 * Real.pi := by ring
  rw [hend1, hend2] at hper
  exact ⟨by rw [hper]; exact h0_2pi, h0_2pi⟩

/-- 11.5(4) non-strict form valid on the entire range `0 ≤ r < 1` (including `r = 0`). -/
theorem node11_5_monotone_non_strict {r δ t : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hδ0 : 0 ≤ δ) (hδt : δ ≤ |t|) (ht : |t| ≤ Real.pi) :
    poissonKernel r t ≤ poissonKernel r δ := by
  have hcos : Real.cos t ≤ Real.cos δ := by
    rw [← Real.cos_abs t]
    exact Real.antitoneOn_cos (Set.mem_Icc.mpr ⟨hδ0, hδt.trans ht⟩)
      (Set.mem_Icc.mpr ⟨hδ0.trans hδt, ht⟩) hδt
  have hdenδ : 0 < 1 - 2 * r * Real.cos δ + r ^ 2 := poissonKernel_den_pos hr0 hr1 δ
  have hdent : 0 < 1 - 2 * r * Real.cos t + r ^ 2 := poissonKernel_den_pos hr0 hr1 t
  unfold poissonKernel
  rw [div_le_div_iff₀ hdent hdenδ]
  have hnum_nn : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hden_le : 1 - 2 * r * Real.cos δ + r ^ 2 ≤ 1 - 2 * r * Real.cos t + r ^ 2 := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hcos)]
  exact mul_le_mul_of_nonneg_left hden_le hnum_nn

/-- 11.5(5): uniform tail decay `lim_{r → 1⁻} sup_{δ ≤ |t| ≤ π} P_r(t) = 0` for `0 < δ ≤ π`. -/
theorem node11_5_tail_tendsto_zero {δ : ℝ} (hδ0 : 0 < δ) (hδπ : δ ≤ Real.pi) :
    Tendsto (fun r => poissonKernel r δ) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) ∧
    Tendsto (fun r => sSup (poissonKernel r '' {t : ℝ | δ ≤ |t| ∧ |t| ≤ Real.pi}))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
  have hcos_lt : Real.cos δ < 1 := by
    simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hδπ hδ0
  have hcont_at : ContinuousAt (fun r : ℝ => poissonKernel r δ) 1 := by
    unfold poissonKernel
    refine ContinuousAt.div (by fun_prop) (by fun_prop) (by linarith)
  have hval1 : poissonKernel 1 δ = 0 := by simp [poissonKernel]
  have htend_δ : Tendsto (fun r => poissonKernel r δ) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) :=
    (hval1 ▸ hcont_at.tendsto).mono_left nhdsWithin_le_nhds
  refine ⟨htend_δ, htend_δ.congr' ?_⟩
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    self_mem_nhdsWithin] with r hr0 hr1
  have hr0' : 0 ≤ r := le_of_lt hr0
  have hr1' : r < 1 := hr1
  symm
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact ⟨poissonKernel r δ, δ, ⟨by rw [abs_of_pos hδ0], by rwa [abs_of_pos hδ0]⟩, rfl⟩
  · rintro _ ⟨t, ⟨hδt, htπ⟩, rfl⟩
    exact node11_5_monotone_non_strict hr0' hr1' hδ0.le hδt htπ
  · intro w hw
    exact ⟨poissonKernel r δ, ⟨δ, ⟨by rw [abs_of_pos hδ0], by rwa [abs_of_pos hδ0]⟩, rfl⟩, hw⟩

/-- 11.5 (Complete Poisson kernel package with explicit E-11.5 fidelity disclosure):
combines the Fourier series (1), Herglotz real-part identity, normalization (3), positivity,
evenness, periodicity, radial bounds, non-strict monotonicity on `0 ≤ r < 1`, the `r = 0`
strict-inequality counterexample, the `0 < r` strict inequality (4), and uniform tail decay (5). -/
theorem theorem11_5 :
    (∀ {r : ℝ}, 0 ≤ r → r < 1 → ∀ t : ℝ,
      HasSum (fun n : ℤ => (r : ℂ) ^ n.natAbs * Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)))
        (poissonKernel r t : ℂ) ∧
      ((1 + (r : ℂ) * Complex.exp (Complex.I * (t : ℂ))) /
        (1 - (r : ℂ) * Complex.exp (Complex.I * (t : ℂ)))).re = poissonKernel r t ∧
      0 < poissonKernel r t ∧
      poissonKernel r (-t) = poissonKernel r t ∧
      poissonKernel r (t + 2 * Real.pi) = poissonKernel r t) ∧
    (∀ {r : ℝ}, 0 ≤ r → r < 1 →
      (2 * Real.pi)⁻¹ * (∫ t in (-Real.pi)..Real.pi, poissonKernel r t) = 1) ∧
    (∀ {r δ t : ℝ}, 0 ≤ r → r < 1 → 0 ≤ δ → δ ≤ |t| → |t| ≤ Real.pi →
      poissonKernel r t ≤ poissonKernel r δ) ∧
    ((0 : ℝ) ≤ 0 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) < |(2 : ℝ)| ∧ |(2 : ℝ)| ≤ Real.pi ∧
      ¬ poissonKernel 0 2 < poissonKernel 0 1) ∧
    (∀ {r δ t : ℝ}, 0 < r → r < 1 → 0 < δ → δ < |t| → |t| ≤ Real.pi →
      poissonKernel r t < poissonKernel r δ) ∧
    (∀ {δ : ℝ}, 0 < δ → δ ≤ Real.pi →
      Tendsto (fun r => sSup (poissonKernel r '' {t : ℝ | δ ≤ |t| ∧ |t| ≤ Real.pi}))
        (nhdsWithin 1 (Set.Iio 1)) (nhds 0)) :=
  ⟨fun {r} hr0 hr1 t => ⟨node11_5_hasSum_fourier hr0 hr1 t, node11_5_herglotz_re hr0 hr1 t,
      node11_5_pos hr0 hr1 t, node11_5_even r t, node11_5_periodic r t⟩,
   fun hr0 hr1 => (node11_5_integral_eq_one hr0 hr1).1,
   fun hr0 hr1 hδ0 hδt ht => node11_5_monotone_non_strict hr0 hr1 hδ0 hδt ht,
   node11_5_strict_inequality_counterexample,
   fun hr hr1 hδ hδt ht => node11_5_strict_inequality_corrected hr hr1 hδ hδt ht,
   fun hδ0 hδπ => (node11_5_tail_tendsto_zero hδ0 hδπ).2⟩

end Node11_5

section Nodes11_6_to_11_8_and_11_15

/-- 11.6 (Definition): the Poisson integral `P[f](z)` of a function `f` on the unit circle `T`
evaluated at `z ∈ U = ball 0 1` (`(2π)⁻¹ ∫_{-π}^π P_r(θ - t) f(e^{it}) dt` for `z = r e^{iθ}`). -/
noncomputable def poissonIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (z : ℂ) : E :=
  Real.circleAverage (fun ζ => _root_.poissonKernel 0 z ζ • f ζ) 0 1

/-- 11.15 (Definition): radial restriction `u_r(ζ) = u(r ζ)` (`0 ≤ r < 1`, `ζ ∈ T`). -/
def radialRestriction {E : Type*} (u : ℂ → E) (r : ℝ) (ζ : ℂ) : E :=
  u ((r : ℂ) * ζ)

/-- 11.6: exact polar/angular integral representation of `poissonIntegral f (r e^{iθ})` on both
`[0, 2π]` and `[-π, π]`. -/
theorem node11_6_angular_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) {r : ℝ} (hr0 : 0 ≤ r) (θ : ℝ) :
    poissonIntegral f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      (2 * Real.pi)⁻¹ • ∫ t in (0 : ℝ)..(2 * Real.pi),
        poissonKernel r (θ - t) • f (Complex.exp ((t : ℂ) * Complex.I)) ∧
    poissonIntegral f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      (2 * Real.pi)⁻¹ • ∫ t in (-Real.pi)..Real.pi,
        poissonKernel r (θ - t) • f (Complex.exp ((t : ℂ) * Complex.I)) := by
  have h0_2pi : poissonIntegral f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      (2 * Real.pi)⁻¹ • ∫ t in (0 : ℝ)..(2 * Real.pi),
        poissonKernel r (θ - t) • f (Complex.exp ((t : ℂ) * Complex.I)) := by
    unfold poissonIntegral
    rw [Real.circleAverage_def]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [poissonKernel_eq_mathlib hr0 θ t]
    simp [circleMap]
  have hper : Function.Periodic
      (fun t : ℝ => poissonKernel r (θ - t) • f (Complex.exp ((t : ℂ) * Complex.I)))
      (2 * Real.pi) := by
    intro t
    have h1 : poissonKernel r (θ - (t + 2 * Real.pi)) = poissonKernel r (θ - t) := by
      rw [← node11_5_even, ← node11_5_even r (θ - t)]
      have : -(θ - (t + 2 * Real.pi)) = -(θ - t) + 2 * Real.pi := by ring
      rw [this, node11_5_periodic]
    have h2 : Complex.exp (((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((t : ℂ) * Complex.I) := by
      have : ((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
          (t : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    dsimp only
    rw [h1, h2]
  have hint := hper.intervalIntegral_add_eq (-Real.pi) 0
  have hend1 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have hend2 : (0 : ℝ) + 2 * Real.pi = 2 * Real.pi := by ring
  rw [hend1, hend2] at hint
  exact ⟨h0_2pi, h0_2pi.trans (by rw [hint])⟩

/-- 11.7 (Real `L¹(T)` harmonicity & Herglotz representation): if `f : ℂ → ℝ` is `CircleIntegrable`
on the unit circle `T`, then `poissonIntegral f` is harmonic on `ball 0 1` in both Mathlib's sense
and Rudin's weak 11.3 sense, and agrees with the real part of the holomorphic Herglotz integral. -/
theorem theorem11_7_real {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1) :
    HarmonicOn (poissonIntegral f) (Metric.ball 0 1) ∧
    InnerProductSpace.HarmonicOnNhd (poissonIntegral f) (Metric.ball 0 1) ∧
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball 0 1) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1, (F z).re = poissonIntegral f z := by
  have hf_c : CircleIntegrable (fun ζ => (f ζ : ℂ)) 0 1 := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hf ⊢
    exact Complex.ofRealCLM.integrable_comp hf
  let F : ℂ → ℂ := fun w =>
    Real.circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (f ζ : ℂ)) 0 1
  have hsub : Metric.ball (0 : ℂ) 1 ⊆ (Metric.sphere (0 : ℂ) |(1 : ℝ)|)ᶜ := by
    intro w hw
    rw [abs_of_pos zero_lt_one, Set.mem_compl_iff, Metric.mem_sphere]
    exact (Metric.mem_ball.mp hw).ne
  have hF_diff : DifferentiableOn ℂ F (Metric.ball 0 1) :=
    (differentiableOn_circleAverage_herglotzRieszKernel_smul hf_c).mono hsub
  have hF_ana : AnalyticOnNhd ℂ F (Metric.ball 0 1) :=
    (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hf_c).mono hsub
  have heq : ∀ w ∈ Metric.ball (0 : ℂ) 1, (F w).re = poissonIntegral f w := by
    intro w hw
    change (Real.circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (f ζ : ℂ)) 0 1).re =
      Real.circleAverage (fun ζ => _root_.poissonKernel 0 w ζ • f ζ) 0 1
    rw [re_circleAverage_herglotzRieszKernel_smul hf (hsub hw),
      ← poissonKernel_eq_re_herglotzRieszKernel]
    rfl
  have hmath : InnerProductSpace.HarmonicOnNhd (poissonIntegral f) (Metric.ball 0 1) := by
    intro z hz
    have hev : (fun w => (F w).re) =ᶠ[nhds z] poissonIntegral f :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Metric.ball 0 1, Metric.isOpen_ball.mem_nhds hz, heq⟩
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).mp (hF_ana z hz).harmonicAt_re
  exact ⟨harmonicOn_of_mathlib hmath, hmath, F, hF_diff, heq⟩

/-- 11.7 (Complex `L¹(T)` harmonicity): if `f : ℂ → ℂ` is `CircleIntegrable` on `T`, then
`poissonIntegral f` is harmonic on `ball 0 1` in both Rudin's weak 11.3 sense and Mathlib's sense. -/
theorem theorem11_7 {f : ℂ → ℂ} (hf : CircleIntegrable f 0 1) :
    HarmonicOn (poissonIntegral f) (Metric.ball 0 1) ∧
    InnerProductSpace.HarmonicOnNhd (poissonIntegral f) (Metric.ball 0 1) := by
  have hre_int : CircleIntegrable (fun ζ => (f ζ).re) 0 1 := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hf ⊢
    exact Complex.reCLM.integrable_comp hf
  have him_int : CircleIntegrable (fun ζ => (f ζ).im) 0 1 := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hf ⊢
    exact Complex.imCLM.integrable_comp hf
  obtain ⟨_, hmath_re, _⟩ := theorem11_7_real hre_int
  obtain ⟨_, hmath_im, _⟩ := theorem11_7_real him_int
  let u_re : ℂ → ℝ := poissonIntegral (fun ζ => (f ζ).re)
  let u_im : ℂ → ℝ := poissonIntegral (fun ζ => (f ζ).im)
  have hdecomp : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      poissonIntegral f z = (u_re z : ℂ) + (u_im z : ℂ) * Complex.I := by
    intro z hz
    have hz_not : z ∉ Metric.sphere (0 : ℂ) |(1 : ℝ)| := by
      rw [abs_of_pos zero_lt_one, Metric.mem_sphere]
      exact (Metric.mem_ball.mp hz).ne
    have hcont_k : ContinuousOn (_root_.poissonKernel 0 z) (Metric.sphere 0 |(1 : ℝ)|) := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hz_not)
    have hci : CircleIntegrable (fun ζ => _root_.poissonKernel 0 z ζ • f ζ) 0 1 :=
      hf.continuousOn_smul hcont_k
    have hre_eq : (poissonIntegral f z).re = u_re z := by
      unfold poissonIntegral u_re
      exact (Complex.reCLM.circleAverage_comp_comm hci).symm.trans
        (Real.circleAverage_congr_sphere fun ζ _ => by simp [Complex.real_smul])
    have him_eq : (poissonIntegral f z).im = u_im z := by
      unfold poissonIntegral u_im
      exact (Complex.imCLM.circleAverage_comp_comm hci).symm.trans
        (Real.circleAverage_congr_sphere fun ζ _ => by simp [Complex.real_smul])
    exact (Complex.re_add_im (poissonIntegral f z)).symm.trans (by rw [hre_eq, him_eq])
  let L_I : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight Complex.I
  let g : ℂ → ℂ := (Complex.ofRealCLM ∘ u_re) + (L_I ∘ u_im)
  have hg_math : InnerProductSpace.HarmonicOnNhd g (Metric.ball 0 1) := by
    intro z hz
    exact ((hmath_re z hz).comp_CLM Complex.ofRealCLM).add ((hmath_im z hz).comp_CLM L_I)
  have hmath : InnerProductSpace.HarmonicOnNhd (poissonIntegral f) (Metric.ball 0 1) := by
    intro z hz
    have hev : g =ᶠ[nhds z] poissonIntegral f :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Metric.ball 0 1, Metric.isOpen_ball.mem_nhds hz,
        fun w hw => by
          change (u_re w : ℂ) + (u_im w) • Complex.I = poissonIntegral f w
          rw [Complex.real_smul, hdecomp w hw]⟩
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).mp (hg_math z hz)
  exact ⟨harmonicOn_of_mathlib hmath, hmath⟩

private theorem norm_exp_mul_I_sub_one_le (s : ℝ) :
    ‖Complex.exp ((s : ℂ) * Complex.I) - 1‖ ≤ |s| := by
  have hsq : ‖Complex.exp ((s : ℂ) * Complex.I) - 1‖ ^ 2 ≤ |s| ^ 2 := by
    have hre_im : ‖Complex.exp ((s : ℂ) * Complex.I) - 1‖ ^ 2 =
        (Real.cos s - 1) ^ 2 + Real.sin s ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.exp_ofReal_mul_I]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
        Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
      ring
    have htrig : (Real.cos s - 1) ^ 2 + Real.sin s ^ 2 = 4 * Real.sin (s / 2) ^ 2 := by
      have h1 := Real.sin_sq_add_cos_sq s
      have h2 : Real.cos s = 1 - 2 * Real.sin (s / 2) ^ 2 := by
        have hc := Real.cos_two_mul (s / 2)
        have hs := Real.sin_sq_add_cos_sq (s / 2)
        rw [show 2 * (s / 2) = s by ring] at hc
        linarith
      nlinarith
    rw [hre_im, htrig]
    have hsin_le : |Real.sin (s / 2)| ≤ |s / 2| := Real.abs_sin_le_abs
    have hsin_sq : Real.sin (s / 2) ^ 2 ≤ (s / 2) ^ 2 := by
      rw [← sq_abs (Real.sin (s / 2)), ← sq_abs (s / 2)]
      exact pow_le_pow_left₀ (abs_nonneg _) hsin_le 2
    rw [sq_abs]
    nlinarith
  simpa using sq_le_sq.mp hsq

/-- 11.15 (Uniform radial convergence for continuous boundary data): if `f : ℂ → E` is continuous
on the unit circle `T = sphere 0 1` (`[CompleteSpace E]`), then `u_r(ζ) = P[f](r ζ)` converges
uniformly to `f(ζ)` on `T` as `r → 1⁻`. -/
theorem tendstoUniformlyOn_poissonIntegral_radial {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} (hf : ContinuousOn f (Metric.sphere (0 : ℂ) 1)) :
    TendstoUniformlyOn (fun (r : ℝ) (ζ : ℂ) => poissonIntegral f ((r : ℂ) * ζ)) f
      (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))) (Metric.sphere (0 : ℂ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  have hcomp : IsCompact (Metric.sphere (0 : ℂ) 1) := isCompact_sphere 0 1
  have huc : UniformContinuousOn f (Metric.sphere (0 : ℂ) 1) :=
    hcomp.uniformContinuousOn_of_continuous hf
  obtain ⟨M, hM⟩ := (hcomp.image_of_continuousOn hf.norm).isBounded.exists_pos_norm_le
  rcases hM with ⟨hM_pos, hM_bound⟩
  have hf_bound : ∀ ζ ∈ Metric.sphere (0 : ℂ) 1, ‖f ζ‖ ≤ M := by
    intro ζ hζ
    simpa only [Real.norm_eq_abs, abs_norm] using hM_bound ‖f ζ‖ ⟨ζ, hζ, rfl⟩
  intro ε hε
  obtain ⟨η, hη_pos, hη⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (half_pos hε)
  let δ : ℝ := min (Real.pi / 2) (η / 2)
  have hδ_pos : 0 < δ := lt_min (by positivity) (half_pos hη_pos)
  have hδ_pi : δ ≤ Real.pi := (min_le_left _ _).trans (by linarith [Real.pi_pos])
  have hδ_lt_pi : δ < Real.pi := (min_le_left _ _).trans_lt (by linarith [Real.pi_pos])
  have htail := (node11_5_tail_tendsto_zero hδ_pos hδ_pi).1
  have hev_tail : ∀ᶠ r in nhdsWithin 1 (Set.Iio 1), poissonKernel r δ < ε / (4 * M) :=
    (Metric.tendsto_nhds.mp htail (ε / (4 * M)) (by positivity)).mono fun r hr => by
      rw [Real.dist_eq, sub_zero] at hr
      exact (le_abs_self _).trans_lt hr
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    self_mem_nhdsWithin, hev_tail] with r hr0_lt hr1 hPrδ ζ hζ
  have hr0 : 0 ≤ r := hr0_lt.le
  -- Parametrize `ζ = exp(θ * I)` using `θ = Complex.arg ζ`
  let θ : ℝ := Complex.arg ζ
  have hζ_eq : ζ = Complex.exp ((θ : ℂ) * Complex.I) := by
    have h := Complex.norm_mul_exp_arg_mul_I ζ
    have hn : ‖ζ‖ = 1 := by simpa [Metric.mem_sphere] using hζ
    rw [hn, Complex.ofReal_one, one_mul] at h
    exact h.symm
  -- Express `poissonIntegral f (r * ζ) - f ζ` as `(2π)⁻¹ • ∫_{-π}^π P_r(s) • (f(e^{i(θ - s)}) - f ζ) ds`
  have hang : poissonIntegral f ((r : ℂ) * ζ) =
      (2 * Real.pi)⁻¹ • ∫ t in (-Real.pi)..Real.pi,
        poissonKernel r (θ - t) • f (Complex.exp ((t : ℂ) * Complex.I)) := by
    rw [hζ_eq]
    exact (node11_6_angular_eq f hr0 θ).2
  have hf_rot : Continuous (fun s : ℝ => f (Complex.exp (((θ - s : ℝ) : ℂ) * Complex.I))) := by
    have hparam : Continuous (fun s : ℝ => Complex.exp (((θ - s : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    exact hf.comp_continuous hparam fun s => by
      rw [Metric.mem_sphere, dist_zero_right, Complex.norm_exp_ofReal_mul_I]
  let g_sub : ℝ → E := fun s =>
    poissonKernel r s • (f (Complex.exp (((θ - s : ℝ) : ℂ) * Complex.I)) - f ζ)
  have hg_cont : Continuous g_sub :=
    (continuous_poissonKernel hr0 hr1).smul (hf_rot.sub continuous_const)
  have hshift : (∫ t in (-Real.pi)..Real.pi,
        poissonKernel r (θ - t) • f (Complex.exp ((t : ℂ) * Complex.I))) =
      ∫ s in (-Real.pi)..Real.pi,
        poissonKernel r s • f (Complex.exp (((θ - s : ℝ) : ℂ) * Complex.I)) := by
    let φ : ℝ → E := fun s => poissonKernel r s • f (Complex.exp (((θ - s : ℝ) : ℂ) * Complex.I))
    have hφ_per : Function.Periodic φ (2 * Real.pi) := by
      intro s
      dsimp [φ]
      rw [node11_5_periodic r s]
      congr 2
      have : ((θ - (s + 2 * Real.pi) : ℝ) : ℂ) * Complex.I =
          ((θ - s : ℝ) : ℂ) * Complex.I - 2 * (Real.pi : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
    have hcongr : (∫ t in (-Real.pi)..Real.pi,
          poissonKernel r (θ - t) • f (Complex.exp ((t : ℂ) * Complex.I))) =
        ∫ t in (-Real.pi)..Real.pi, φ (θ - t) :=
      intervalIntegral.integral_congr fun t _ => by dsimp [φ]; rw [sub_sub_cancel]
    have hsub_var := intervalIntegral.integral_comp_sub_left φ θ (a := -Real.pi) (b := Real.pi)
    have hper_eq := hφ_per.intervalIntegral_add_eq (θ - Real.pi) (-Real.pi)
    have h1 : θ - -Real.pi = θ - Real.pi + 2 * Real.pi := by ring
    have h2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [h1] at hsub_var
    rw [h2] at hper_eq
    exact hcongr.trans (hsub_var.trans hper_eq)
  have hdiff_eq : poissonIntegral f ((r : ℂ) * ζ) - f ζ =
      (2 * Real.pi)⁻¹ • ∫ s in (-Real.pi)..Real.pi, g_sub s := by
    rw [hang, hshift]
    have hnorm1 : (2 * Real.pi)⁻¹ • (∫ s in (-Real.pi)..Real.pi, poissonKernel r s • f ζ) = f ζ := by
      rw [intervalIntegral.integral_smul_const, smul_smul, (node11_5_integral_eq_one hr0 hr1).1,
        one_smul]
    have hint1 : IntervalIntegrable
        (fun s => poissonKernel r s • f (Complex.exp (((θ - s : ℝ) : ℂ) * Complex.I)))
        MeasureTheory.volume (-Real.pi) Real.pi :=
      ((continuous_poissonKernel hr0 hr1).smul hf_rot).intervalIntegrable _ _
    have hint2 : IntervalIntegrable (fun s => poissonKernel r s • f ζ)
        MeasureTheory.volume (-Real.pi) Real.pi :=
      ((continuous_poissonKernel hr0 hr1).smul continuous_const).intervalIntegrable _ _
    conv_lhs => rw [← hnorm1]
    rw [← smul_sub, ← intervalIntegral.integral_sub hint1 hint2]
    congr 2
    ext s
    exact (smul_sub _ _ _).symm
  -- Split `[-π, π]` into `[-π, -δ]`, `[-δ, δ]`, `[δ, π]`
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (hg_cont.intervalIntegrable (μ := MeasureTheory.volume) (-Real.pi) (-δ))
    (hg_cont.intervalIntegrable (μ := MeasureTheory.volume) (-δ) δ)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (hg_cont.intervalIntegrable (μ := MeasureTheory.volume) (-Real.pi) δ)
    (hg_cont.intervalIntegrable (μ := MeasureTheory.volume) δ Real.pi)
  have hmid_bound : ‖∫ s in (-δ)..δ, g_sub s‖ ≤
      (ε / 2) * ∫ s in (-δ)..δ, poissonKernel r s := by
    have hle_mid : ∀ s ∈ Set.Ioc (-δ) δ, ‖g_sub s‖ ≤ (ε / 2) * poissonKernel r s := by
      intro s hs
      dsimp [g_sub]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (node11_5_pos hr0 hr1 s), mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (node11_5_pos hr0 hr1 s).le
      have habs_s : |s| ≤ δ := abs_le.mpr ⟨hs.1.le, hs.2⟩
      have hdist_ζ : dist (Complex.exp (((θ - s : ℝ) : ℂ) * Complex.I)) ζ < η := by
        rw [hζ_eq, dist_eq_norm]
        have hfac : Complex.exp (((θ - s : ℝ) : ℂ) * Complex.I) -
            Complex.exp ((θ : ℂ) * Complex.I) =
            Complex.exp ((θ : ℂ) * Complex.I) *
              (Complex.exp (((-s : ℝ) : ℂ) * Complex.I) - 1) := by
          rw [mul_sub, mul_one, ← Complex.exp_add]
          congr 2; push_cast; ring
        rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
        calc ‖Complex.exp (((-s : ℝ) : ℂ) * Complex.I) - 1‖
            ≤ |-s| := norm_exp_mul_I_sub_one_le (-s)
          _ = |s| := abs_neg s
          _ ≤ δ := habs_s
          _ ≤ η / 2 := min_le_right _ _
          _ < η := half_lt_self hη_pos
      have hmem_rot : Complex.exp (((θ - s : ℝ) : ℂ) * Complex.I) ∈ Metric.sphere (0 : ℂ) 1 := by
        rw [Metric.mem_sphere, dist_zero_right, Complex.norm_exp_ofReal_mul_I]
      simpa [dist_eq_norm] using (hη _ hmem_rot ζ hζ hdist_ζ).le
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) (by linarith)
      (Filter.Eventually.of_forall fun s => hle_mid s)
      (((continuous_poissonKernel hr0 hr1).const_mul _).intervalIntegrable _ _)
  have hmid_int_le : (∫ s in (-δ)..δ, poissonKernel r s) ≤
      ∫ s in (-Real.pi)..Real.pi, poissonKernel r s := by
    have hnonneg : ∀ s, 0 ≤ poissonKernel r s := fun s => (node11_5_pos hr0 hr1 s).le
    have hL : 0 ≤ ∫ s in (-Real.pi)..(-δ), poissonKernel r s :=
      intervalIntegral.integral_nonneg (by linarith) fun s _ => hnonneg s
    have hR : 0 ≤ ∫ s in δ..Real.pi, poissonKernel r s :=
      intervalIntegral.integral_nonneg (by linarith) fun s _ => hnonneg s
    have hp1 := intervalIntegral.integral_add_adjacent_intervals
      ((continuous_poissonKernel hr0 hr1).intervalIntegrable (μ := MeasureTheory.volume) (-Real.pi) (-δ))
      ((continuous_poissonKernel hr0 hr1).intervalIntegrable (μ := MeasureTheory.volume) (-δ) δ)
    have hp2 := intervalIntegral.integral_add_adjacent_intervals
      ((continuous_poissonKernel hr0 hr1).intervalIntegrable (μ := MeasureTheory.volume) (-Real.pi) δ)
      ((continuous_poissonKernel hr0 hr1).intervalIntegrable (μ := MeasureTheory.volume) δ Real.pi)
    linarith
  have hleft_bound : ‖∫ s in (-Real.pi)..(-δ), g_sub s‖ ≤
      (Real.pi - δ) * (2 * M * poissonKernel r δ) := by
    have hle : ∀ s ∈ Set.Ioc (-Real.pi) (-δ), ‖g_sub s‖ ≤ 2 * M * poissonKernel r δ := by
      intro s hs
      dsimp [g_sub]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (node11_5_pos hr0 hr1 s)]
      have hs_neg : s < 0 := lt_of_le_of_lt hs.2 (neg_lt_zero.mpr hδ_pos)
      have hPr : poissonKernel r s ≤ poissonKernel r δ :=
        node11_5_monotone_non_strict hr0 hr1 hδ_pos.le
          (by rw [abs_of_neg hs_neg]; linarith [hs.2])
          (by rw [abs_of_neg hs_neg]; linarith [hs.1])
      have hfnorm : ‖f (Complex.exp (((θ - s : ℝ) : ℂ) * Complex.I)) - f ζ‖ ≤ 2 * M := by
        calc ‖f (Complex.exp (((θ - s : ℝ) : ℂ) * Complex.I)) - f ζ‖
            ≤ ‖f (Complex.exp (((θ - s : ℝ) : ℂ) * Complex.I))‖ + ‖f ζ‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add
              (hf_bound _ (by rw [Metric.mem_sphere, dist_zero_right, Complex.norm_exp_ofReal_mul_I]))
              (hf_bound ζ hζ)
          _ = 2 * M := by ring
      calc poissonKernel r s * ‖f (Complex.exp (((θ - s : ℝ) : ℂ) * Complex.I)) - f ζ‖
          ≤ poissonKernel r δ * (2 * M) :=
            mul_le_mul hPr hfnorm (norm_nonneg _) (node11_5_pos hr0 hr1 δ).le
        _ = 2 * M * poissonKernel r δ := mul_comm _ _
    have hn := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) (by linarith)
      (Filter.Eventually.of_forall fun s => hle s) (continuous_const.intervalIntegrable _ _)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hn
    calc ‖∫ s in (-Real.pi)..(-δ), g_sub s‖ ≤ (-δ - -Real.pi) * (2 * M * poissonKernel r δ) := hn
      _ = (Real.pi - δ) * (2 * M * poissonKernel r δ) := by ring
  have hright_bound : ‖∫ s in δ..Real.pi, g_sub s‖ ≤
      (Real.pi - δ) * (2 * M * poissonKernel r δ) := by
    have hle : ∀ s ∈ Set.Ioc δ Real.pi, ‖g_sub s‖ ≤ 2 * M * poissonKernel r δ := by
      intro s hs
      dsimp [g_sub]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (node11_5_pos hr0 hr1 s)]
      have hPr : poissonKernel r s ≤ poissonKernel r δ :=
        node11_5_monotone_non_strict hr0 hr1 hδ_pos.le
          (by rw [abs_of_pos (hδ_pos.trans hs.1)]; exact hs.1.le)
          (by rw [abs_of_pos (hδ_pos.trans hs.1)]; exact hs.2)
      have hfnorm : ‖f (Complex.exp (((θ - s : ℝ) : ℂ) * Complex.I)) - f ζ‖ ≤ 2 * M := by
        calc ‖f (Complex.exp (((θ - s : ℝ) : ℂ) * Complex.I)) - f ζ‖
            ≤ ‖f (Complex.exp (((θ - s : ℝ) : ℂ) * Complex.I))‖ + ‖f ζ‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add
              (hf_bound _ (by rw [Metric.mem_sphere, dist_zero_right, Complex.norm_exp_ofReal_mul_I]))
              (hf_bound ζ hζ)
          _ = 2 * M := by ring
      calc poissonKernel r s * ‖f (Complex.exp (((θ - s : ℝ) : ℂ) * Complex.I)) - f ζ‖
          ≤ poissonKernel r δ * (2 * M) :=
            mul_le_mul hPr hfnorm (norm_nonneg _) (node11_5_pos hr0 hr1 δ).le
        _ = 2 * M * poissonKernel r δ := mul_comm _ _
    have hn := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) hδ_lt_pi.le
      (Filter.Eventually.of_forall fun s => hle s) (continuous_const.intervalIntegrable _ _)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hn
    exact hn
  rw [dist_comm, dist_eq_norm, hdiff_eq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * Real.pi))]
  have htot_norm : ‖∫ s in (-Real.pi)..Real.pi, g_sub s‖ ≤
      ‖∫ s in (-Real.pi)..(-δ), g_sub s‖ + ‖∫ s in (-δ)..δ, g_sub s‖ +
        ‖∫ s in δ..Real.pi, g_sub s‖ := by
    rw [← hsplit2, ← hsplit1]
    have hna1 := norm_add_le
      ((∫ x in (-Real.pi)..(-δ), g_sub x) + ∫ x in (-δ)..δ, g_sub x)
      (∫ x in δ..Real.pi, g_sub x)
    have hna2 := norm_add_le (∫ x in (-Real.pi)..(-δ), g_sub x) (∫ x in (-δ)..δ, g_sub x)
    linarith
  have hint_2pi : ∫ s in (-Real.pi)..Real.pi, poissonKernel r s = 2 * Real.pi := by
    have h1 := (node11_5_integral_eq_one hr0 hr1).1
    field_simp [Real.pi_pos.ne'] at h1
    linarith
  have hpi_sub_lt : Real.pi - δ < Real.pi := by linarith
  calc (2 * Real.pi)⁻¹ * ‖∫ s in (-Real.pi)..Real.pi, g_sub s‖
      ≤ (2 * Real.pi)⁻¹ * ((Real.pi - δ) * (2 * M * poissonKernel r δ) +
          (ε / 2) * (2 * Real.pi) + (Real.pi - δ) * (2 * M * poissonKernel r δ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hm : ‖∫ s in (-δ)..δ, g_sub s‖ ≤ (ε / 2) * (2 * Real.pi) :=
          hmid_bound.trans (mul_le_mul_of_nonneg_left (hmid_int_le.trans_eq hint_2pi) (by positivity))
        linarith
    _ = ε / 2 + ((Real.pi - δ) / Real.pi) * (2 * M * poissonKernel r δ) := by
        field_simp [Real.pi_pos.ne']
        ring
    _ ≤ ε / 2 + 1 * (2 * M * poissonKernel r δ) := by
        have hpos_rhs : 0 ≤ 2 * M * poissonKernel r δ :=
          mul_nonneg (by positivity) (node11_5_pos hr0 hr1 δ).le
        linarith [mul_le_mul_of_nonneg_right ((div_le_one Real.pi_pos).mpr hpi_sub_lt.le) hpos_rhs]
    _ < ε / 2 + 2 * M * (ε / (4 * M)) := by
        have : 2 * M * poissonKernel r δ < 2 * M * (ε / (4 * M)) :=
          mul_lt_mul_of_pos_left hPrδ (by positivity)
        linarith
    _ = ε := by
        field_simp [hM_pos.ne']
        ring

/-- Poisson Dirichlet extension of `f` on `closedBall 0 1`: equals `poissonIntegral f z` on
`ball 0 1` and `f z` on `sphere 0 1`. -/
noncomputable def poissonExtension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (z : ℂ) : E :=
  if ‖z‖ < 1 then poissonIntegral f z else f z

/-- Continuous dependence of `poissonIntegral f` on `ball 0 1` for any `CircleIntegrable` `f`. -/
theorem continuousOn_poissonIntegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} (hf : ContinuousOn f (Metric.sphere (0 : ℂ) 1)) :
    ContinuousOn (poissonIntegral f) (Metric.ball (0 : ℂ) 1) := by
  rw [Metric.continuousOn_iff]
  intro z₀ hz₀ ε hε
  obtain ⟨M, hM_pos, hM_bound⟩ :=
    ((isCompact_sphere (0 : ℂ) 1).image_of_continuousOn hf.norm).isBounded.exists_pos_norm_le
  have hf_bound : ∀ ζ ∈ Metric.sphere (0 : ℂ) 1, ‖f ζ‖ ≤ M := fun ζ hζ => by
    simpa only [Real.norm_eq_abs, abs_norm] using hM_bound ‖f ζ‖ ⟨ζ, hζ, rfl⟩
  let d : ℝ := (1 - ‖z₀‖) / 2
  have hd_pos : 0 < d := by
    dsimp [d]
    have : ‖z₀‖ < 1 := by simpa [Metric.mem_ball] using hz₀
    linarith
  -- On `closedBall z₀ d × sphere 0 1`, `(w, ζ) ↦ _root_.poissonKernel 0 w ζ` is uniformly continuous
  let Kprod : Set (ℂ × ℂ) := Metric.closedBall z₀ d ×ˢ Metric.sphere (0 : ℂ) 1
  have hK_comp : IsCompact Kprod := (isCompact_closedBall z₀ d).prod (isCompact_sphere 0 1)
  have hK_cont : ContinuousOn (fun p : ℂ × ℂ => _root_.poissonKernel 0 p.1 p.2) Kprod := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    rintro ⟨w, ζ⟩ ⟨hw, hζ⟩ h0
    have hw_lt : ‖w‖ < 1 := by
      have hw_d : ‖w - z₀‖ ≤ d := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
      have := norm_sub_norm_le w z₀
      dsimp [d] at hw_d
      have : ‖z₀‖ < 1 := by simpa [Metric.mem_ball] using hz₀
      linarith [norm_le_norm_add_norm_sub' w z₀]
    have hζ1 : ‖ζ‖ = 1 := by simpa [Metric.mem_sphere] using hζ
    have heq : ζ = w := sub_eq_zero.mp (sq_eq_zero_iff.mp (by simpa using h0))
    exact hw_lt.ne (heq ▸ hζ1)
  obtain ⟨η, hη_pos, hη⟩ :=
    Metric.uniformContinuousOn_iff.mp (hK_comp.uniformContinuousOn_of_continuous hK_cont)
      (ε / (2 * M)) (by positivity)
  refine ⟨min d η, lt_min hd_pos hη_pos, fun w hw hdist => ?_⟩
  have hw_cb : w ∈ Metric.closedBall z₀ d :=
    Metric.mem_closedBall.mpr ((lt_of_lt_of_le hdist (min_le_left _ _)).le)
  have hz₀_cb : z₀ ∈ Metric.closedBall z₀ d := Metric.mem_closedBall_self hd_pos.le
  rw [dist_eq_norm]
  unfold poissonIntegral
  have hci_w : CircleIntegrable (fun ζ => _root_.poissonKernel 0 w ζ • f ζ) 0 1 := by
    have hw_not : w ∉ Metric.sphere (0 : ℂ) |(1 : ℝ)| := by
      rw [abs_of_pos zero_lt_one, Metric.mem_sphere]
      exact (Metric.mem_ball.mp hw).ne
    have hck : ContinuousOn (_root_.poissonKernel 0 w) (Metric.sphere 0 1) := by
      have hk := Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hw_not)
      rw [← poissonKernel_eq_re_herglotzRieszKernel, abs_of_pos zero_lt_one] at hk
      exact hk
    exact (hck.smul hf).circleIntegrable zero_le_one
  have hci_z₀ : CircleIntegrable (fun ζ => _root_.poissonKernel 0 z₀ ζ • f ζ) 0 1 := by
    have hz₀_not : z₀ ∉ Metric.sphere (0 : ℂ) |(1 : ℝ)| := by
      rw [abs_of_pos zero_lt_one, Metric.mem_sphere]
      exact (Metric.mem_ball.mp hz₀).ne
    have hck : ContinuousOn (_root_.poissonKernel 0 z₀) (Metric.sphere 0 1) := by
      have hk := Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hz₀_not)
      rw [← poissonKernel_eq_re_herglotzRieszKernel, abs_of_pos zero_lt_one] at hk
      exact hk
    exact (hck.smul hf).circleIntegrable zero_le_one
  rw [Real.circleAverage_def, Real.circleAverage_def, ← smul_sub,
    ← intervalIntegral.integral_sub hci_w hci_z₀, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * Real.pi))]
  have hle_int : ∀ θ ∈ Set.Ioc (0 : ℝ) (2 * Real.pi),
      ‖_root_.poissonKernel 0 w (circleMap 0 1 θ) • f (circleMap 0 1 θ) -
        _root_.poissonKernel 0 z₀ (circleMap 0 1 θ) • f (circleMap 0 1 θ)‖ ≤ ε / 2 := by
    intro θ _
    let ζ := circleMap 0 1 θ
    have hζ : ζ ∈ Metric.sphere (0 : ℂ) 1 := circleMap_mem_sphere 0 zero_le_one θ
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    have hk_lt : |_root_.poissonKernel 0 w ζ - _root_.poissonKernel 0 z₀ ζ| < ε / (2 * M) := by
      have hp_dist : dist (w, ζ) (z₀, ζ) < η := by
        simpa [Prod.dist_eq] using lt_of_lt_of_le hdist (min_le_right _ _)
      simpa [Real.dist_eq] using hη (w, ζ) ⟨hw_cb, hζ⟩ (z₀, ζ) ⟨hz₀_cb, hζ⟩ hp_dist
    calc |_root_.poissonKernel 0 w ζ - _root_.poissonKernel 0 z₀ ζ| * ‖f ζ‖
        ≤ (ε / (2 * M)) * M :=
          mul_le_mul hk_lt.le (hf_bound ζ hζ) (norm_nonneg _) (by positivity)
      _ = ε / 2 := by field_simp [hM_pos.ne']
  have hn := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) (by positivity)
    (Filter.Eventually.of_forall fun θ => hle_int θ) (continuous_const.intervalIntegrable _ _)
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hn
  dsimp only
  calc (2 * Real.pi)⁻¹ * ‖∫ x in (0 : ℝ)..(2 * Real.pi),
        _root_.poissonKernel 0 w (circleMap 0 1 x) • f (circleMap 0 1 x) -
          _root_.poissonKernel 0 z₀ (circleMap 0 1 x) • f (circleMap 0 1 x)‖
      ≤ (2 * Real.pi)⁻¹ * ((2 * Real.pi) * (ε / 2)) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
    _ = ε / 2 := by field_simp [Real.pi_pos.ne']
    _ < ε := half_lt_self hε

/-- 11.8 (Dirichlet problem on the unit disc for continuous boundary data): if `f` is continuous on
`T = sphere 0 1`, then `poissonExtension f` (defined by `P[f](z)` on `ball 0 1` and `f(z)` on `T`)
is continuous on `closedBall 0 1` (and harmonic on `ball 0 1` when `E = ℝ` or `ℂ`). -/
theorem continuousOn_poissonExtension {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} (hf : ContinuousOn f (Metric.sphere (0 : ℂ) 1)) :
    ContinuousOn (poissonExtension f) (Metric.closedBall (0 : ℂ) 1) := by
  rw [Metric.continuousOn_iff]
  intro z₀ hz₀ ε hε
  have hz₀_le : ‖z₀‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hz₀
  rcases hz₀_le.lt_or_eq with hz₀_lt | hz₀_eq
  · -- Interior point `z₀ ∈ ball 0 1`
    have hz₀_ball : z₀ ∈ Metric.ball (0 : ℂ) 1 := by simpa [Metric.mem_ball] using hz₀_lt
    obtain ⟨δ, hδ_pos, hδ⟩ :=
      Metric.continuousOn_iff.mp (continuousOn_poissonIntegral hf) z₀ hz₀_ball ε hε
    refine ⟨min δ (1 - ‖z₀‖), lt_min hδ_pos (sub_pos.mpr hz₀_lt), fun z _ hdist => ?_⟩
    have hz_lt : ‖z‖ < 1 := by
      have h1 : dist z z₀ < 1 - ‖z₀‖ := lt_of_lt_of_le hdist (min_le_right _ _)
      rw [dist_eq_norm] at h1
      linarith [norm_le_norm_add_norm_sub' z z₀]
    have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := by simpa [Metric.mem_ball] using hz_lt
    simp only [poissonExtension, hz_lt, hz₀_lt, ↓reduceIte]
    exact hδ z hz_ball (lt_of_lt_of_le hdist (min_le_left _ _))
  · -- Boundary point `z₀ ∈ sphere 0 1`
    have hz₀_sph : z₀ ∈ Metric.sphere (0 : ℂ) 1 := by simpa [Metric.mem_sphere] using hz₀_eq
    have hunif := Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_poissonIntegral_radial hf)
      (ε / 2) (half_pos hε)
    obtain ⟨δ_r, hδ_r_pos, hδ_r⟩ := Metric.mem_nhdsWithin_iff.mp hunif
    obtain ⟨η₁, hη₁_pos, hη₁⟩ := Metric.continuousOn_iff.mp hf z₀ hz₀_sph (ε / 2) (half_pos hε)
    let δ₀ : ℝ := min (min δ_r (1 / 2)) (η₁ / 2)
    have hδ₀_pos : 0 < δ₀ := lt_min (lt_min hδ_r_pos (by positivity)) (half_pos hη₁_pos)
    refine ⟨δ₀, hδ₀_pos, fun z hz_cb hdist => ?_⟩
    have hz_le : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hz_cb
    have hz_pos : 0 < ‖z‖ := by
      have h1 : dist z z₀ < 1 / 2 :=
        lt_of_lt_of_le hdist ((min_le_left _ _).trans (min_le_right _ _))
      rw [dist_comm, dist_eq_norm] at h1
      have h2 := norm_sub_norm_le z₀ z
      rw [hz₀_eq] at h2
      linarith
    let r : ℝ := ‖z‖
    have hr_ne : r ≠ 0 := hz_pos.ne'
    let ω : ℂ := ((r⁻¹ : ℝ) : ℂ) * z
    have hω_sph : ω ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
      dsimp [ω]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hz_pos),
        inv_mul_cancel₀ hr_ne]
    have hrω : (r : ℂ) * ω = z := by
      dsimp [ω]
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hr_ne, Complex.ofReal_one, one_mul]
    have h1_sub_r : 1 - r < δ₀ := by
      have h2 := norm_sub_norm_le z₀ z
      rw [hz₀_eq, norm_sub_rev] at h2
      exact h2.trans_lt (dist_eq_norm z z₀ ▸ hdist)
    have hω_z : ‖ω - z‖ < δ₀ := by
      have hcalc : ω - z = (((r⁻¹ - 1 : ℝ)) : ℂ) * z := by
        dsimp [ω]; push_cast; ring
      rw [hcalc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hnonneg : 0 ≤ r⁻¹ - 1 := sub_nonneg.mpr (one_le_inv₀ hz_pos |>.mpr hz_le)
      rw [abs_of_nonneg hnonneg]
      have : (r⁻¹ - 1) * r = 1 - r := by field_simp [hr_ne]
      rwa [this]
    have hω_z₀ : dist ω z₀ < η₁ := by
      rw [dist_eq_norm]
      calc ‖ω - z₀‖ ≤ ‖ω - z‖ + ‖z - z₀‖ := norm_sub_le_norm_sub_add_norm_sub ω z z₀
        _ < δ₀ + δ₀ := add_lt_add hω_z (dist_eq_norm z z₀ ▸ hdist)
        _ ≤ η₁ / 2 + η₁ / 2 := add_le_add (min_le_right _ _) (min_le_right _ _)
        _ = η₁ := add_halves η₁
    have hf_close : dist (f ω) (f z₀) < ε / 2 := hη₁ ω hω_sph hω_z₀
    have hz₀_ext : poissonExtension f z₀ = f z₀ := by simp [poissonExtension, hz₀_eq]
    rw [hz₀_ext]
    rcases hz_le.lt_or_eq with hr_lt | hr_eq
    · simp only [poissonExtension, hr_lt, ↓reduceIte]
      have hr_dist : dist r 1 < δ_r := by
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hr_lt), neg_sub]
        exact h1_sub_r.trans_le ((min_le_left _ _).trans (min_le_left _ _))
      have hP_close : dist (f ω) (poissonIntegral f ((r : ℂ) * ω)) < ε / 2 :=
        hδ_r ⟨Metric.mem_ball.mpr hr_dist, hr_lt⟩ ω hω_sph
      have hf_close' : dist (f z₀) (f ω) < ε / 2 := by rwa [dist_comm]
      rw [← hrω, dist_comm (poissonIntegral f _) (f z₀)]
      exact (dist_triangle (f z₀) (f ω) _).trans_lt
        ((add_lt_add hf_close' hP_close).trans_eq (add_halves ε))
    · simp only [poissonExtension, hr_eq, lt_irrefl, ↓reduceIte]
      have hω_eq_z : ω = z := by
        dsimp [ω]; simp [r, hr_eq]
      exact (hω_eq_z ▸ hf_close).trans (half_lt_self hε)

theorem theorem11_8 {f : ℂ → ℂ} (hf : ContinuousOn f (Metric.sphere (0 : ℂ) 1)) :
    ContinuousOn (poissonExtension f) (Metric.closedBall (0 : ℂ) 1) ∧
    HarmonicOn (poissonExtension f) (Metric.ball (0 : ℂ) 1) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, poissonExtension f z = poissonIntegral f z) ∧
    (∀ ζ ∈ Metric.sphere (0 : ℂ) 1, poissonExtension f ζ = f ζ) := by
  have hci : CircleIntegrable f 0 1 := hf.circleIntegrable zero_le_one
  have hball_eq : Set.EqOn (poissonIntegral f) (poissonExtension f) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hz_lt : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
    simp [poissonExtension, hz_lt]
  refine ⟨continuousOn_poissonExtension hf,
    (theorem11_7 hci).1.congr_of_isOpen Metric.isOpen_ball hball_eq,
    fun z hz => (hball_eq hz).symm,
    fun ζ hζ => ?_⟩
  have hζ_eq : ‖ζ‖ = 1 := by simpa [Metric.mem_sphere] using hζ
  simp [poissonExtension, hζ_eq]

/-- 11.15: radial restrictions `radialRestriction (poissonIntegral f) r` converge uniformly to `f`
on `T = sphere 0 1` as `r → 1⁻` for every `f ∈ C(T)`. -/
theorem theorem11_15 {f : ℂ → ℂ} (hf : ContinuousOn f (Metric.sphere (0 : ℂ) 1)) :
    TendstoUniformlyOn (radialRestriction (poissonIntegral f)) f
      (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))) (Metric.sphere (0 : ℂ) 1) :=
  tendstoUniformlyOn_poissonIntegral_radial hf

end Nodes11_6_to_11_8_and_11_15

/-! ### Batch 11B (Part 1): Nodes 11.9 and 11.10 (Poisson representation & regularity bridge) -/

section Nodes11_9_and_11_10

private theorem second_deriv_nonpos_of_isLocalMax {g g' : ℝ → ℝ} {g'' : ℝ}
    (hmax : IsLocalMax g 0) (hd1 : ∀ᶠ t in nhds 0, HasDerivAt g (g' t) t)
    (hd2 : HasDerivAt g' g'' 0) : g'' ≤ 0 := by
  have hg'0 : g' 0 = 0 := hmax.hasDerivAt_eq_zero hd1.self_of_nhds
  by_contra! hpos
  have hev_pos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t⁻¹ * (g' (0 + t) - g' 0) := by
    simpa only [smul_eq_mul] using hd2.tendsto_slope_zero_right.eventually (Ioi_mem_nhds hpos)
  obtain ⟨δ₁, hδ₁, hb₁⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hmax hd1)
  obtain ⟨δ₂, hδ₂, hb₂⟩ := Metric.mem_nhdsWithin_iff.mp hev_pos
  let t₀ : ℝ := min δ₁ δ₂ / 2
  have ht₀_pos : 0 < t₀ := half_pos (lt_min hδ₁ hδ₂)
  have ht₀_lt₁ : t₀ < δ₁ := (half_lt_self (lt_min hδ₁ hδ₂)).trans_le (min_le_left _ _)
  have ht₀_lt₂ : t₀ < δ₂ := (half_lt_self (lt_min hδ₁ hδ₂)).trans_le (min_le_right _ _)
  have hIcc_b₁ : ∀ x ∈ Set.Icc 0 t₀, x ∈ Metric.ball (0 : ℝ) δ₁ := fun x hx => by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    exact hx.2.trans_lt ht₀_lt₁
  have hcont : ContinuousOn g (Set.Icc 0 t₀) :=
    fun x hx => (hb₁ (hIcc_b₁ x hx)).2.continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo 0 t₀, HasDerivAt g (g' x) x :=
    fun x hx => (hb₁ (hIcc_b₁ x ⟨hx.1.le, hx.2.le⟩)).2
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope g g' ht₀_pos hcont hderiv
  have hc_b₂ : c ∈ Metric.ball (0 : ℝ) δ₂ ∩ Set.Ioi 0 := by
    refine ⟨?_, hc_mem.1⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc_mem.1]
    exact hc_mem.2.trans ht₀_lt₂
  have hq_pos : 0 < c⁻¹ * (g' (0 + c) - g' 0) := hb₂ hc_b₂
  rw [zero_add, hg'0, sub_zero] at hq_pos
  have hg'c_pos : 0 < g' c := by
    have := mul_pos hc_mem.1 hq_pos
    rwa [← mul_assoc, mul_inv_cancel₀ hc_mem.1.ne', one_mul] at this
  have ht₀_le : g t₀ ≤ g 0 := (hb₁ (hIcc_b₁ t₀ ⟨ht₀_pos.le, le_rfl⟩)).1
  have hsl_nonpos : (g t₀ - g 0) / (t₀ - 0) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht₀_le) (by linarith)
  linarith

private theorem hasDerivAt_line_shift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v : ℂ → F} {z₀ e : ℂ} {t : ℝ} (h : LineDifferentiableAt ℝ v (z₀ + t • e) e) :
    HasDerivAt (fun s : ℝ => v (z₀ + s • e)) (lineDeriv ℝ v (z₀ + t • e) e) t := by
  let φ : ℝ → ℝ := fun s => s - t
  have hφ : HasDerivAt φ 1 t := (hasDerivAt_id' t).sub_const t
  have h0 : HasDerivAt (fun u : ℝ => v ((z₀ + t • e) + u • e))
      (lineDeriv ℝ v (z₀ + t • e) e) (φ t) := by
    dsimp [φ]
    rw [sub_self]
    exact h.hasLineDerivAt
  have hcomp : HasDerivAt ((fun u : ℝ => v ((z₀ + t • e) + u • e)) ∘ φ)
      (lineDeriv ℝ v (z₀ + t • e) e) t :=
    (h0.scomp t hφ).congr_deriv (one_smul ℝ (lineDeriv ℝ v (z₀ + t • e) e))
  refine hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  dsimp only [Function.comp_apply, φ]
  congr 1
  rw [add_assoc, ← add_smul, add_sub_cancel]

/-- Maximum principle on closed discs for Rudin's weak 11.3 `HarmonicOn` (no `C²` assumption). -/
theorem weak_harmonic_max_principle_closedBall {v : ℂ → ℝ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hv_harm : HarmonicOn v (Metric.ball c R)) (hv_cont : ContinuousOn v (Metric.closedBall c R))
    (hbd : ∀ ζ ∈ Metric.sphere c R, v ζ ≤ M) :
    ∀ z ∈ Metric.closedBall c R, v z ≤ M := by
  intro z hz
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  let ε : ℝ := δ / (R ^ 2 + 1)
  have hε : 0 < ε := div_pos hδ (by positivity)
  let w : ℂ → ℝ := fun x => v x + ε * ‖x - c‖ ^ 2
  have hw_cont : ContinuousOn w (Metric.closedBall c R) :=
    hv_cont.add (continuousOn_const.mul (((continuousOn_id.sub continuousOn_const).norm).pow 2))
  obtain ⟨z₀, hz₀_cb, hz₀_max⟩ :=
    (isCompact_closedBall c R).exists_isMaxOn (Metric.nonempty_closedBall.mpr hR.le) hw_cont
  have hz₀_not_ball : z₀ ∉ Metric.ball c R := by
    intro hz₀_ball
    have hloc : ∀ᶠ x in nhds z₀, w x ≤ w z₀ :=
      hz₀_max.isLocalMax (Metric.closedBall_mem_nhds_of_mem hz₀_ball)
    -- Along x-direction (`e = 1`)
    have htend_x : Tendsto (fun t : ℝ => z₀ + t • (1 : ℂ)) (nhds 0) (nhds z₀) := by
      have hca : ContinuousAt (fun t : ℝ => z₀ + t • (1 : ℂ)) 0 :=
        (by fun_prop : Continuous (fun t : ℝ => z₀ + t • (1 : ℂ))).continuousAt
      simpa using hca.tendsto
    have hloc_x : IsLocalMax (fun t : ℝ => w (z₀ + t • (1 : ℂ))) 0 := by
      simpa [IsLocalMax, IsMaxFilter] using htend_x.eventually hloc
    have hd1_x : ∀ᶠ t in nhds (0 : ℝ), HasDerivAt (fun s : ℝ => w (z₀ + s • (1 : ℂ)))
        (partialX v (z₀ + t • (1 : ℂ)) + 2 * ε * (z₀.re - c.re + t)) t := by
      refine (htend_x.eventually (Metric.isOpen_ball.mem_nhds hz₀_ball)).mono fun t ht => ?_
      have hv_t := hasDerivAt_line_shift (hv_harm.partials _ ht).first_x
      have hq_eq : (fun s : ℝ => ε * ‖(z₀ + s • (1 : ℂ)) - c‖ ^ 2) =
          fun s : ℝ => ε * ((z₀.re - c.re + s) ^ 2 + (z₀.im - c.im) ^ 2) := by
        ext s
        congr 1
        rw [← Complex.normSq_eq_norm_sq]
        simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
          Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.one_re, Complex.one_im]
        ring
      have hq_t : HasDerivAt (fun s : ℝ => ε * ‖(z₀ + s • (1 : ℂ)) - c‖ ^ 2)
          (2 * ε * (z₀.re - c.re + t)) t := by
        rw [hq_eq]
        have hp := ((((hasDerivAt_id' t).const_add (z₀.re - c.re)).pow 2).add_const
          ((z₀.im - c.im) ^ 2)).const_mul ε
        exact hp.congr_deriv (by push_cast; ring)
      exact hv_t.add hq_t
    have hd2_x : HasDerivAt (fun t : ℝ => partialX v (z₀ + t • (1 : ℂ)) +
        2 * ε * (z₀.re - c.re + t)) (partialX (partialX v) z₀ + 2 * ε) 0 := by
      have h2v : HasDerivAt (fun t : ℝ => partialX v (z₀ + t • (1 : ℂ)))
          (partialX (partialX v) z₀) 0 :=
        (hv_harm.partials z₀ hz₀_ball).second_x.hasLineDerivAt
      have h2q : HasDerivAt (fun t : ℝ => 2 * ε * (z₀.re - c.re + t)) (2 * ε) 0 :=
        (((hasDerivAt_id' (0 : ℝ)).const_add (z₀.re - c.re)).const_mul (2 * ε)).congr_deriv (by ring)
      exact h2v.add h2q
    have hle_x := second_deriv_nonpos_of_isLocalMax hloc_x hd1_x hd2_x
    -- Along y-direction (`e = I`)
    have htend_y : Tendsto (fun t : ℝ => z₀ + t • Complex.I) (nhds 0) (nhds z₀) := by
      have hca : ContinuousAt (fun t : ℝ => z₀ + t • Complex.I) 0 :=
        (by fun_prop : Continuous (fun t : ℝ => z₀ + t • Complex.I)).continuousAt
      simpa using hca.tendsto
    have hloc_y : IsLocalMax (fun t : ℝ => w (z₀ + t • Complex.I)) 0 := by
      simpa [IsLocalMax, IsMaxFilter] using htend_y.eventually hloc
    have hd1_y : ∀ᶠ t in nhds (0 : ℝ), HasDerivAt (fun s : ℝ => w (z₀ + s • Complex.I))
        (partialY v (z₀ + t • Complex.I) + 2 * ε * (z₀.im - c.im + t)) t := by
      refine (htend_y.eventually (Metric.isOpen_ball.mem_nhds hz₀_ball)).mono fun t ht => ?_
      have hv_t := hasDerivAt_line_shift (hv_harm.partials _ ht).first_y
      have hq_eq : (fun s : ℝ => ε * ‖(z₀ + s • Complex.I) - c‖ ^ 2) =
          fun s : ℝ => ε * ((z₀.re - c.re) ^ 2 + (z₀.im - c.im + s) ^ 2) := by
        ext s
        congr 1
        rw [← Complex.normSq_eq_norm_sq]
        simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
          Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      have hq_t : HasDerivAt (fun s : ℝ => ε * ‖(z₀ + s • Complex.I) - c‖ ^ 2)
          (2 * ε * (z₀.im - c.im + t)) t := by
        rw [hq_eq]
        have hp := ((((hasDerivAt_id' t).const_add (z₀.im - c.im)).pow 2).const_add
          ((z₀.re - c.re) ^ 2)).const_mul ε
        exact hp.congr_deriv (by push_cast; ring)
      exact hv_t.add hq_t
    have hd2_y : HasDerivAt (fun t : ℝ => partialY v (z₀ + t • Complex.I) +
        2 * ε * (z₀.im - c.im + t)) (partialY (partialY v) z₀ + 2 * ε) 0 := by
      have h2v : HasDerivAt (fun t : ℝ => partialY v (z₀ + t • Complex.I))
          (partialY (partialY v) z₀) 0 :=
        (hv_harm.partials z₀ hz₀_ball).second_y.hasLineDerivAt
      have h2q : HasDerivAt (fun t : ℝ => 2 * ε * (z₀.im - c.im + t)) (2 * ε) 0 :=
        (((hasDerivAt_id' (0 : ℝ)).const_add (z₀.im - c.im)).const_mul (2 * ε)).congr_deriv (by ring)
      exact h2v.add h2q
    have hle_y := second_deriv_nonpos_of_isLocalMax hloc_y hd1_y hd2_y
    have hlap := hv_harm.laplacian_zero z₀ hz₀_ball
    unfold laplacian at hlap
    linarith
  have hz₀_sph : z₀ ∈ Metric.sphere c R := by
    rw [Metric.mem_closedBall] at hz₀_cb
    rw [Metric.mem_ball, not_lt] at hz₀_not_ball
    exact Metric.mem_sphere.mpr (le_antisymm hz₀_cb hz₀_not_ball)
  have hw_z_le : w z ≤ w z₀ := hz₀_max hz
  have hz₀_norm : ‖z₀ - c‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hz₀_sph
  have hv_le : v z ≤ M + ε * R ^ 2 := by
    have hw_z₀ : w z₀ = v z₀ + ε * R ^ 2 := by dsimp [w]; rw [hz₀_norm]
    have hv_w : v z ≤ w z := le_add_of_nonneg_right (by positivity)
    linarith [hbd z₀ hz₀_sph]
  have hεR : ε * R ^ 2 ≤ δ := by
    dsimp [ε]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem HarmonicOn.sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f₁ f₂ : ℂ → F} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf₁ : HarmonicOn f₁ Ω) (hf₂ : HarmonicOn f₂ Ω) : HarmonicOn (f₁ - f₂) Ω := by
  have hpx : ∀ a ∈ Ω, HasLineDerivAt ℝ (f₁ - f₂) (partialX f₁ a - partialX f₂ a) a 1 :=
    fun a ha => HasDerivAt.sub (hf₁.partials a ha).first_x.hasLineDerivAt
      (hf₂.partials a ha).first_x.hasLineDerivAt
  have hpy : ∀ a ∈ Ω, HasLineDerivAt ℝ (f₁ - f₂) (partialY f₁ a - partialY f₂ a) a Complex.I :=
    fun a ha => HasDerivAt.sub (hf₁.partials a ha).first_y.hasLineDerivAt
      (hf₂.partials a ha).first_y.hasLineDerivAt
  have hxx : ∀ z ∈ Ω, HasLineDerivAt ℝ (partialX (f₁ - f₂))
      (partialX (partialX f₁) z - partialX (partialX f₂) z) z 1 := by
    intro z hz
    have hstep : HasLineDerivAt ℝ (partialX f₁ - partialX f₂)
        (partialX (partialX f₁) z - partialX (partialX f₂) z) z 1 :=
      HasDerivAt.sub (hf₁.partials z hz).second_x.hasLineDerivAt
        (hf₂.partials z hz).second_x.hasLineDerivAt
    refine hstep.congr_of_eventuallyEq ?_
    filter_upwards [hΩ.mem_nhds hz] with a ha
    exact (hpx a ha).lineDeriv
  have hyy : ∀ z ∈ Ω, HasLineDerivAt ℝ (partialY (f₁ - f₂))
      (partialY (partialY f₁) z - partialY (partialY f₂) z) z Complex.I := by
    intro z hz
    have hstep : HasLineDerivAt ℝ (partialY f₁ - partialY f₂)
        (partialY (partialY f₁) z - partialY (partialY f₂) z) z Complex.I :=
      HasDerivAt.sub (hf₁.partials z hz).second_y.hasLineDerivAt
        (hf₂.partials z hz).second_y.hasLineDerivAt
    refine hstep.congr_of_eventuallyEq ?_
    filter_upwards [hΩ.mem_nhds hz] with a ha
    exact (hpy a ha).lineDeriv
  refine ⟨hf₁.continuousOn.sub hf₂.continuousOn, fun z hz =>
    ⟨(hpx z hz).lineDifferentiableAt, (hpy z hz).lineDifferentiableAt,
     (hxx z hz).lineDifferentiableAt, (hyy z hz).lineDifferentiableAt⟩, fun z hz => ?_⟩
  have hx_eq : partialX (partialX (f₁ - f₂)) z =
      partialX (partialX f₁) z - partialX (partialX f₂) z := (hxx z hz).lineDeriv
  have hy_eq : partialY (partialY (f₁ - f₂)) z =
      partialY (partialY f₁) z - partialY (partialY f₂) z := (hyy z hz).lineDeriv
  unfold laplacian
  rw [hx_eq, hy_eq]
  have h1 := hf₁.laplacian_zero z hz
  have h2 := hf₂.laplacian_zero z hz
  unfold laplacian at h1 h2
  calc (partialX (partialX f₁) z - partialX (partialX f₂) z) +
        (partialY (partialY f₁) z - partialY (partialY f₂) z)
      = (partialX (partialX f₁) z + partialY (partialY f₁) z) -
        (partialX (partialX f₂) z + partialY (partialY f₂) z) := by abel
    _ = 0 := by rw [h1, h2, sub_self]

theorem weak_harmonic_eqOn_closedBall_of_eqOn_sphere {v₁ v₂ : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (h₁ : HarmonicOn v₁ (Metric.ball c R)) (hc₁ : ContinuousOn v₁ (Metric.closedBall c R))
    (h₂ : HarmonicOn v₂ (Metric.ball c R)) (hc₂ : ContinuousOn v₂ (Metric.closedBall c R))
    (hsph : Set.EqOn v₁ v₂ (Metric.sphere c R)) :
    Set.EqOn v₁ v₂ (Metric.closedBall c R) := by
  intro z hz
  have hle1 : (v₁ - v₂) z ≤ 0 :=
    weak_harmonic_max_principle_closedBall hR (h₁.sub Metric.isOpen_ball h₂) (hc₁.sub hc₂)
      (fun ζ hζ => sub_nonpos.mpr (hsph hζ).le) z hz
  have hle2 : (v₂ - v₁) z ≤ 0 :=
    weak_harmonic_max_principle_closedBall hR (h₂.sub Metric.isOpen_ball h₁) (hc₂.sub hc₁)
      (fun ζ hζ => sub_nonpos.mpr (hsph hζ).ge) z hz
  dsimp at hle1 hle2
  linarith

private theorem hasLineDerivAt_comp_affine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : ℂ → F} {L : F} {a w v : ℂ} {R : ℝ}
    (hd : HasLineDerivAt ℝ h L (a + (R : ℂ) * w) v) :
    HasLineDerivAt ℝ (fun z => h (a + (R : ℂ) * z)) (R • L) w v := by
  let φ : ℝ → ℝ := fun t => R * t
  have hφ : HasDerivAt φ R 0 :=
    ((hasDerivAt_id' (0 : ℝ)).const_mul R).congr_deriv (mul_one R)
  have h0 : HasDerivAt (fun u : ℝ => h ((a + (R : ℂ) * w) + u • v)) L (φ 0) := by
    dsimp [φ]
    rw [mul_zero]
    exact hd
  refine (h0.scomp 0 hφ).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  dsimp only [Function.comp_apply, φ]
  congr 1
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

theorem HarmonicOn.comp_affine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℂ → F} {a : ℂ} {R : ℝ} (hR : 0 < R) (hf : HarmonicOn f (Metric.ball a R)) :
    HarmonicOn (fun w => f (a + (R : ℂ) * w)) (Metric.ball 0 1) := by
  let g : ℂ → F := fun w => f (a + (R : ℂ) * w)
  have hmem : ∀ w ∈ Metric.ball (0 : ℂ) 1, a + (R : ℂ) * w ∈ Metric.ball a R := by
    intro w hw
    rw [Metric.mem_ball, dist_self_add_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR]
    have hw1 : ‖w‖ < 1 := by simpa [Metric.mem_ball] using hw
    nlinarith
  have hpx : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      HasLineDerivAt ℝ g (R • partialX f (a + (R : ℂ) * w)) w 1 :=
    fun w hw => hasLineDerivAt_comp_affine (hf.partials _ (hmem w hw)).first_x.hasLineDerivAt
  have hpy : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      HasLineDerivAt ℝ g (R • partialY f (a + (R : ℂ) * w)) w Complex.I :=
    fun w hw => hasLineDerivAt_comp_affine (hf.partials _ (hmem w hw)).first_y.hasLineDerivAt
  have hxx : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      HasLineDerivAt ℝ (partialX g) ((R * R) • partialX (partialX f) (a + (R : ℂ) * w)) w 1 := by
    intro w hw
    have hstep : HasLineDerivAt ℝ (fun z => R • partialX f (a + (R : ℂ) * z))
        ((R * R) • partialX (partialX f) (a + (R : ℂ) * w)) w 1 := by
      have hs := HasDerivAt.const_smul R
        (hasLineDerivAt_comp_affine (hf.partials _ (hmem w hw)).second_x.hasLineDerivAt)
      rw [smul_smul] at hs
      exact hs
    refine hstep.congr_of_eventuallyEq ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hw] with z hz
    exact (hpx z hz).lineDeriv
  have hyy : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      HasLineDerivAt ℝ (partialY g)
        ((R * R) • partialY (partialY f) (a + (R : ℂ) * w)) w Complex.I := by
    intro w hw
    have hstep : HasLineDerivAt ℝ (fun z => R • partialY f (a + (R : ℂ) * z))
        ((R * R) • partialY (partialY f) (a + (R : ℂ) * w)) w Complex.I := by
      have hs := HasDerivAt.const_smul R
        (hasLineDerivAt_comp_affine (hf.partials _ (hmem w hw)).second_y.hasLineDerivAt)
      rw [smul_smul] at hs
      exact hs
    refine hstep.congr_of_eventuallyEq ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hw] with z hz
    exact (hpy z hz).lineDeriv
  refine ⟨hf.continuousOn.comp (by fun_prop) hmem, fun w hw =>
    ⟨(hpx w hw).lineDifferentiableAt, (hpy w hw).lineDifferentiableAt,
     (hxx w hw).lineDifferentiableAt, (hyy w hw).lineDifferentiableAt⟩, fun w hw => ?_⟩
  have hx_eq : partialX (partialX g) w = (R * R) • partialX (partialX f) (a + (R : ℂ) * w) :=
    (hxx w hw).lineDeriv
  have hy_eq : partialY (partialY g) w = (R * R) • partialY (partialY f) (a + (R : ℂ) * w) :=
    (hyy w hw).lineDeriv
  change partialX (partialX g) w + partialY (partialY g) w = 0
  rw [hx_eq, hy_eq, ← smul_add]
  change (R * R) • laplacian f (a + (R : ℂ) * w) = 0
  rw [hf.laplacian_zero _ (hmem w hw), smul_zero]

/-- 11.9 (Real version): a real-valued function continuous on `closedBall 0 1` and weakly harmonic
(`HarmonicOn` in Rudin's 11.3 sense) on `ball 0 1` equals its Poisson integral on `ball 0 1`, is
the real part of the holomorphic Herglotz integral on `ball 0 1`, and satisfies Mathlib's
`InnerProductSpace.HarmonicOnNhd`. -/
theorem theorem11_9_real {u : ℂ → ℝ}
    (hu_cont : ContinuousOn u (Metric.closedBall 0 1))
    (hu_harm : HarmonicOn u (Metric.ball 0 1)) :
    (∀ z ∈ Metric.ball (0 : ℂ) 1, u z = poissonIntegral u z) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1,
      u z = (Real.circleAverage (fun ζ => herglotzRieszKernel 0 z ζ • (u ζ : ℂ)) 0 1).re) ∧
    DifferentiableOn ℂ
      (fun z => Real.circleAverage (fun ζ => herglotzRieszKernel 0 z ζ • (u ζ : ℂ)) 0 1)
      (Metric.ball 0 1) ∧
    InnerProductSpace.HarmonicOnNhd u (Metric.ball 0 1) := by
  have hu_sph : ContinuousOn u (Metric.sphere 0 1) :=
    hu_cont.mono Metric.sphere_subset_closedBall
  have hu_ci : CircleIntegrable u 0 1 := hu_sph.circleIntegrable zero_le_one
  obtain ⟨hP_weak, hP_math, _⟩ := theorem11_7_real hu_ci
  have hball_eq_ext : Set.EqOn (poissonIntegral u) (poissonExtension u) (Metric.ball 0 1) := by
    intro z hz
    have hz_lt : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
    simp [poissonExtension, hz_lt]
  have hext_weak : HarmonicOn (poissonExtension u) (Metric.ball 0 1) :=
    hP_weak.congr_of_isOpen Metric.isOpen_ball hball_eq_ext
  have hext_cont : ContinuousOn (poissonExtension u) (Metric.closedBall 0 1) :=
    continuousOn_poissonExtension hu_sph
  have hsph_eq : Set.EqOn u (poissonExtension u) (Metric.sphere 0 1) := by
    intro ζ hζ
    have hζ1 : ‖ζ‖ = 1 := by simpa [Metric.mem_sphere] using hζ
    simp [poissonExtension, hζ1]
  have hcb_eq := weak_harmonic_eqOn_closedBall_of_eqOn_sphere zero_lt_one
    hu_harm hu_cont hext_weak hext_cont hsph_eq
  have hu_eq_P : ∀ z ∈ Metric.ball (0 : ℂ) 1, u z = poissonIntegral u z :=
    fun z hz => (hcb_eq (Metric.ball_subset_closedBall hz)).trans (hball_eq_ext hz).symm
  have hu_math : InnerProductSpace.HarmonicOnNhd u (Metric.ball 0 1) := by
    intro z hz
    have hev : poissonIntegral u =ᶠ[nhds z] u :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Metric.ball 0 1, Metric.isOpen_ball.mem_nhds hz, fun w hw => (hu_eq_P w hw).symm⟩
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).mp (hP_math z hz)
  have hsub : Metric.ball (0 : ℂ) 1 ⊆ (Metric.sphere (0 : ℂ) |(1 : ℝ)|)ᶜ := by
    intro w hw
    rw [abs_of_pos zero_lt_one, Set.mem_compl_iff, Metric.mem_sphere]
    exact (Metric.mem_ball.mp hw).ne
  have hu_ci_c : CircleIntegrable (fun ζ => (u ζ : ℂ)) 0 1 :=
    (Complex.continuous_ofReal.comp_continuousOn hu_sph).circleIntegrable zero_le_one
  have hH_diff : DifferentiableOn ℂ
      (fun z => Real.circleAverage (fun ζ => herglotzRieszKernel 0 z ζ • (u ζ : ℂ)) 0 1)
      (Metric.ball 0 1) :=
    (differentiableOn_circleAverage_herglotzRieszKernel_smul hu_ci_c).mono hsub
  have hu_eq_H : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      u z = (Real.circleAverage (fun ζ => herglotzRieszKernel 0 z ζ • (u ζ : ℂ)) 0 1).re := by
    intro z hz
    rw [hu_eq_P z hz]
    unfold poissonIntegral
    rw [re_circleAverage_herglotzRieszKernel_smul hu_ci (hsub hz),
      ← poissonKernel_eq_re_herglotzRieszKernel]
    rfl
  exact ⟨hu_eq_P, hu_eq_H, hH_diff, hu_math⟩

/-- 11.9 (Complex version): any complex-valued function continuous on `closedBall 0 1` and weakly
harmonic on `ball 0 1` equals its Poisson integral on `ball 0 1` and satisfies Mathlib's
`InnerProductSpace.HarmonicOnNhd`. -/
theorem theorem11_9 {u : ℂ → ℂ}
    (hu_cont : ContinuousOn u (Metric.closedBall 0 1))
    (hu_harm : HarmonicOn u (Metric.ball 0 1)) :
    (∀ z ∈ Metric.ball (0 : ℂ) 1, u z = poissonIntegral u z) ∧
    InnerProductSpace.HarmonicOnNhd u (Metric.ball 0 1) := by
  have hre := theorem11_9_real (Complex.continuous_re.comp_continuousOn hu_cont)
    (hu_harm.comp_clm Metric.isOpen_ball Complex.reCLM)
  have him := theorem11_9_real (Complex.continuous_im.comp_continuousOn hu_cont)
    (hu_harm.comp_clm Metric.isOpen_ball Complex.imCLM)
  have hu_sph : ContinuousOn u (Metric.sphere 0 1) :=
    hu_cont.mono Metric.sphere_subset_closedBall
  have hu_ci : CircleIntegrable u 0 1 := hu_sph.circleIntegrable zero_le_one
  obtain ⟨_, hP_math⟩ := theorem11_7 hu_ci
  have hu_eq_P : ∀ z ∈ Metric.ball (0 : ℂ) 1, u z = poissonIntegral u z := by
    intro z hz
    have hz_not : z ∉ Metric.sphere (0 : ℂ) |(1 : ℝ)| := by
      rw [abs_of_pos zero_lt_one, Metric.mem_sphere]
      exact (Metric.mem_ball.mp hz).ne
    have hcont_k : ContinuousOn (_root_.poissonKernel 0 z) (Metric.sphere 0 |(1 : ℝ)|) := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hz_not)
    have hci : CircleIntegrable (fun ζ => _root_.poissonKernel 0 z ζ • u ζ) 0 1 :=
      hu_ci.continuousOn_smul hcont_k
    have hre_P : (poissonIntegral u z).re = (u z).re := by
      have hre_z : (u z).re = poissonIntegral (Complex.re ∘ u) z := hre.1 z hz
      rw [hre_z]
      unfold poissonIntegral
      exact (Complex.reCLM.circleAverage_comp_comm hci).symm.trans
        (Real.circleAverage_congr_sphere fun ζ _ => by simp [Complex.real_smul])
    have him_P : (poissonIntegral u z).im = (u z).im := by
      have him_z : (u z).im = poissonIntegral (Complex.im ∘ u) z := him.1 z hz
      rw [him_z]
      unfold poissonIntegral
      exact (Complex.imCLM.circleAverage_comp_comm hci).symm.trans
        (Real.circleAverage_congr_sphere fun ζ _ => by simp [Complex.real_smul])
    exact Complex.ext hre_P.symm him_P.symm
  have hu_math : InnerProductSpace.HarmonicOnNhd u (Metric.ball 0 1) := by
    intro z hz
    have hev : poissonIntegral u =ᶠ[nhds z] u :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Metric.ball 0 1, Metric.isOpen_ball.mem_nhds hz, fun w hw => (hu_eq_P w hw).symm⟩
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).mp (hP_math z hz)
  exact ⟨hu_eq_P, hu_math⟩

/-- 11.10 Regularity Bridge (Real): on any open set `Ω ⊆ ℂ`, Rudin's weak 11.3 `HarmonicOn u Ω`
is equivalent to Mathlib's `InnerProductSpace.HarmonicOnNhd u Ω` (`C²` + `Δu =ᶠ 0`), and implies
`AnalyticOnNhd ℝ u Ω` and `ContDiffOn ℝ ∞ u Ω`. -/
theorem harmonicOn_iff_harmonicOnNhd_real {u : ℂ → ℝ} {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    HarmonicOn u Ω ↔ InnerProductSpace.HarmonicOnNhd u Ω := by
  refine ⟨fun hu a ha => ?_, harmonicOn_of_mathlib⟩
  obtain ⟨δ, hδ_pos, hball_sub⟩ := Metric.isOpen_iff.mp hΩ a ha
  let R : ℝ := δ / 2
  have hR_pos : 0 < R := half_pos hδ_pos
  have hcb_sub : Metric.closedBall a R ⊆ Ω :=
    (Metric.closedBall_subset_ball (half_lt_self hδ_pos)).trans hball_sub
  let v : ℂ → ℝ := fun w => u (a + (R : ℂ) * w)
  have hv_cont : ContinuousOn v (Metric.closedBall 0 1) := by
    refine hu.continuousOn.comp (by fun_prop) fun w hw => hcb_sub ?_
    rw [Metric.mem_closedBall, dist_self_add_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR_pos]
    have hw1 : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hw
    nlinarith
  have hv_harm : HarmonicOn v (Metric.ball 0 1) :=
    (hu.mono (Metric.ball_subset_closedBall.trans hcb_sub)).comp_affine hR_pos
  have hv_math := (theorem11_9_real hv_cont hv_harm).2.2.2
  obtain ⟨G, hG_ana, hG_re⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hv_math
  let L_aff : ℂ → ℂ := fun z => (z - a) / (R : ℂ)
  let F : ℂ → ℂ := fun z => G (L_aff z)
  have hR_c_ne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR_pos.ne'
  have hmap : ∀ z ∈ Metric.ball a R, L_aff z ∈ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    dsimp [L_aff]
    rw [Metric.mem_ball, dist_zero_right, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR_pos, div_lt_one hR_pos]
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hF_ana : AnalyticAt ℂ F a := by
    have hlin : AnalyticAt ℂ L_aff a :=
      ((analyticAt_id.sub analyticAt_const).mul analyticAt_const).congr
        (Filter.Eventually.of_forall fun z => (div_eq_mul_inv (z - a) (R : ℂ)).symm)
    have hG_at : AnalyticAt ℂ G (L_aff a) := hG_ana (L_aff a) (hmap a (Metric.mem_ball_self hR_pos))
    exact hG_at.comp hlin
  have hev : (fun z => (F z).re) =ᶠ[nhds a] u := by
    filter_upwards [Metric.ball_mem_nhds a hR_pos] with z hz
    have hre_eq : (G (L_aff z)).re = v (L_aff z) := hG_re (hmap z hz)
    dsimp [F]
    rw [hre_eq]
    dsimp [v, L_aff]
    congr 1
    field_simp [hR_c_ne]
    ring
  exact (InnerProductSpace.harmonicAt_congr_nhds hev).mp hF_ana.harmonicAt_re

/-- 11.10 Regularity Bridge (Complex): on any open set `Ω ⊆ ℂ`, Rudin's weak 11.3 `HarmonicOn u Ω`
is equivalent to Mathlib's `InnerProductSpace.HarmonicOnNhd u Ω`. -/
theorem harmonicOn_iff_harmonicOnNhd_complex {u : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    HarmonicOn u Ω ↔ InnerProductSpace.HarmonicOnNhd u Ω := by
  refine ⟨fun hu z hz => ?_, harmonicOn_of_mathlib⟩
  have hre : InnerProductSpace.HarmonicOnNhd (fun w => (u w).re) Ω :=
    (harmonicOn_iff_harmonicOnNhd_real hΩ).mp (hu.comp_clm hΩ Complex.reCLM)
  have him : InnerProductSpace.HarmonicOnNhd (fun w => (u w).im) Ω :=
    (harmonicOn_iff_harmonicOnNhd_real hΩ).mp (hu.comp_clm hΩ Complex.imCLM)
  let L_I : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight Complex.I
  let g : ℂ → ℂ := (Complex.ofRealCLM ∘ fun w => (u w).re) + (L_I ∘ fun w => (u w).im)
  have hg : InnerProductSpace.HarmonicAt g z :=
    ((hre z hz).comp_CLM Complex.ofRealCLM).add ((him z hz).comp_CLM L_I)
  have hev : g =ᶠ[nhds z] u := Filter.Eventually.of_forall fun w => by
    change ((u w).re : ℂ) + (u w).im • Complex.I = u w
    rw [Complex.real_smul, Complex.re_add_im]
  exact (InnerProductSpace.harmonicAt_congr_nhds hev).mp hg

theorem HarmonicOn.analyticOnNhd_real {u : ℂ → ℝ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hu : HarmonicOn u Ω) : AnalyticOnNhd ℝ u Ω :=
  fun z hz => HarmonicAt.analyticAt ((harmonicOn_iff_harmonicOnNhd_real hΩ).mp hu z hz)

theorem HarmonicOn.contDiffOn_real {u : ℂ → ℝ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hu : HarmonicOn u Ω) : ContDiffOn ℝ ⊤ u Ω :=
  (hu.analyticOnNhd_real hΩ).contDiffOn hΩ.uniqueDiffOn

theorem HarmonicOn.analyticOnNhd_complex {u : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hu : HarmonicOn u Ω) : AnalyticOnNhd ℝ u Ω := by
  intro z hz
  have hre : AnalyticAt ℝ (fun w => (u w).re) z :=
    hu.comp_clm hΩ Complex.reCLM |>.analyticOnNhd_real hΩ z hz
  have him : AnalyticAt ℝ (fun w => (u w).im) z :=
    hu.comp_clm hΩ Complex.imCLM |>.analyticOnNhd_real hΩ z hz
  let L_I : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight Complex.I
  have hsum : AnalyticAt ℝ
      (fun w => Complex.ofRealCLM ((u w).re) + L_I ((u w).im)) z :=
    ((Complex.ofRealCLM.analyticAt _).comp hre).add ((L_I.analyticAt _).comp him)
  refine hsum.congr (Filter.Eventually.of_forall fun w => ?_)
  change ((u w).re : ℂ) + (u w).im • Complex.I = u w
  rw [Complex.real_smul, Complex.re_add_im]

theorem HarmonicOn.contDiffOn_complex {u : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hu : HarmonicOn u Ω) : ContDiffOn ℝ ⊤ u Ω :=
  (hu.analyticOnNhd_complex hΩ).contDiffOn hΩ.uniqueDiffOn

/-- 11.10 (General-disc Poisson representation, holomorphic completion on discs, and `C^∞` / real
analyticity for weak `HarmonicOn`):
(a) If `u : ℂ → ℝ` is continuous on `closedBall a R` (`0 < R`) and weakly harmonic on `ball a R`,
    then `u` is given on `ball a R` by the disc Poisson integral (in both `circleAverage` and
    Rudin's polar `(R^2 - r^2) / (R^2 - 2 R r cos(θ - t) + r^2)` form) and Herglotz real-part
    integral;
(b) Any real-valued weakly harmonic `u` on an open ball `ball a R` is the real part of a function
    `F` holomorphic (`AnalyticOnNhd ℂ` and `DifferentiableOn ℂ`) on `ball a R`;
(c) Every real- or complex-valued weakly harmonic function on any open set `Ω` is `C^∞` and
    real-analytic on `Ω`. -/
theorem theorem11_10 {a : ℂ} {R : ℝ} (hR : 0 < R) :
    (∀ {u : ℂ → ℝ}, ContinuousOn u (Metric.closedBall a R) → HarmonicOn u (Metric.ball a R) →
      (∀ z ∈ Metric.ball a R, Real.circleAverage (_root_.poissonKernel a z • u) a R = u z) ∧
      (∀ {r : ℝ}, 0 ≤ r → r < R → ∀ θ : ℝ,
        (2 * Real.pi)⁻¹ * (∫ t in (0 : ℝ)..(2 * Real.pi),
          ((R ^ 2 - r ^ 2) / (R ^ 2 - 2 * R * r * Real.cos (θ - t) + r ^ 2)) *
            u (a + (R : ℂ) * Complex.exp ((t : ℂ) * Complex.I))) =
        u (a + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))) ∧
    (∀ {u : ℂ → ℝ}, HarmonicOn u (Metric.ball a R) →
      ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball a R) ∧
        ∀ z ∈ Metric.ball a R, (F z).re = u z) := by
  refine ⟨fun {u} hu_cont hu_harm => ?_, fun {u} hu_harm => ?_⟩
  · have hu_math : InnerProductSpace.HarmonicOnNhd u (Metric.ball a R) :=
      (harmonicOn_iff_harmonicOnNhd_real Metric.isOpen_ball).mp hu_harm
    have hu_hcl : InnerProductSpace.HarmonicContOnCl u (Metric.ball a R) :=
      ⟨hu_math, by rwa [closure_ball a hR.ne']⟩
    have hca : ∀ z ∈ Metric.ball a R,
        Real.circleAverage (_root_.poissonKernel a z • u) a R = u z :=
      fun z hz => hu_hcl.circleAverage_poissonKernel_smul hz
    refine ⟨hca, fun {r} hr0 hrR θ => ?_⟩
    let v : ℂ → ℝ := fun w => u (a + (R : ℂ) * w)
    have hv_cont : ContinuousOn v (Metric.closedBall 0 1) := by
      refine hu_cont.comp (by fun_prop) fun w hw => ?_
      rw [Metric.mem_closedBall, dist_self_add_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR]
      have hw1 : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hw
      nlinarith
    have hv_harm : HarmonicOn v (Metric.ball 0 1) := hu_harm.comp_affine hR
    have hv_rep := (theorem11_9_real hv_cont hv_harm).1
    let ρ : ℝ := r / R
    have hρ0 : 0 ≤ ρ := div_nonneg hr0 hR.le
    have hρ1 : ρ < 1 := (div_lt_one hR).mpr hrR
    have hw_mem : (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hρ0, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hρ1
    have hval := (hv_rep _ hw_mem).trans (node11_6_angular_eq v hρ0 θ).1
    have hR_ne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    have hlhs : u (a + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
        v ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
      dsimp [v, ρ]
      congr 2
      push_cast
      rw [← mul_assoc, mul_div_cancel₀ _ hR_ne]
    rw [hlhs, hval, smul_eq_mul]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    dsimp [v, ρ]
    congr 1
    unfold poissonKernel
    have hR2_ne : R ^ 2 ≠ 0 := pow_ne_zero 2 hR.ne'
    field_simp [hR.ne', hR2_ne]
  · have hu_math : InnerProductSpace.HarmonicOnNhd u (Metric.ball a R) :=
      (harmonicOn_iff_harmonicOnNhd_real Metric.isOpen_ball).mp hu_harm
    obtain ⟨F, hF_ana, hF_re⟩ :=
      InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hu_math
    exact ⟨F, hF_ana.differentiableOn, fun z hz => hF_re hz⟩

end Nodes11_9_and_11_10

section Nodes11_11_to_11_14

/-- Locally uniform limits of real-valued weakly harmonic functions on an open set `Ω ⊆ ℂ` are
weakly harmonic on `Ω`. -/
theorem HarmonicOn.of_tendstoLocallyUniformlyOn_real {u : ℕ → ℂ → ℝ} {f : ℂ → ℝ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hu : ∀ n, HarmonicOn (u n) Ω)
    (hlim : TendstoLocallyUniformlyOn u f Filter.atTop Ω) :
    HarmonicOn f Ω := by
  rw [harmonicOn_iff_harmonicOnNhd_real hΩ]
  intro a ha
  obtain ⟨δ, hδ_pos, hball_sub⟩ := Metric.isOpen_iff.mp hΩ a ha
  let R : ℝ := δ / 2
  have hR_pos : 0 < R := half_pos hδ_pos
  have hcb_sub : Metric.closedBall a R ⊆ Ω :=
    (Metric.closedBall_subset_ball (half_lt_self hδ_pos)).trans hball_sub
  have hunif : TendstoUniformlyOn u f Filter.atTop (Metric.closedBall a R) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp hlim _ hcb_sub (isCompact_closedBall a R)
  have hf_cont : ContinuousOn f Ω :=
    hlim.continuousOn (Filter.Eventually.of_forall fun n => (hu n).continuousOn).frequently
  let v : ℕ → ℂ → ℝ := fun n w => u n (a + (R : ℂ) * w)
  let g : ℂ → ℝ := fun w => f (a + (R : ℂ) * w)
  have haff_mem : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, a + (R : ℂ) * w ∈ Metric.closedBall a R := by
    intro w hw
    rw [Metric.mem_closedBall, dist_self_add_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR_pos]
    have hw1 : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hw
    nlinarith
  have hv_cont : ∀ n, ContinuousOn (v n) (Metric.closedBall 0 1) :=
    fun n => (hu n).continuousOn.comp (by fun_prop) fun w hw => hcb_sub (haff_mem w hw)
  have hv_harm : ∀ n, HarmonicOn (v n) (Metric.ball 0 1) :=
    fun n => ((hu n).mono (Metric.ball_subset_closedBall.trans hcb_sub)).comp_affine hR_pos
  have hv_rep : ∀ n, ∀ w ∈ Metric.ball (0 : ℂ) 1, v n w = poissonIntegral (v n) w :=
    fun n w hw => (theorem11_9_real (hv_cont n) (hv_harm n)).1 w hw
  have hg_cont : ContinuousOn g (Metric.closedBall 0 1) :=
    hf_cont.comp (by fun_prop) fun w hw => hcb_sub (haff_mem w hw)
  have hg_ci : CircleIntegrable g 0 1 :=
    (hg_cont.mono Metric.sphere_subset_closedBall).circleIntegrable zero_le_one
  have hg_eq_P : ∀ w ∈ Metric.ball (0 : ℂ) 1, g w = poissonIntegral g w := by
    intro w hw
    have hw_norm : ‖w‖ < 1 := by simpa [Metric.mem_ball] using hw
    have hw_not : w ∉ Metric.sphere (0 : ℂ) |(1 : ℝ)| := by
      rw [abs_of_pos zero_lt_one, Metric.mem_sphere, dist_zero_right]
      exact hw_norm.ne
    have hcont_k : ContinuousOn (_root_.poissonKernel 0 w) (Metric.sphere 0 |(1 : ℝ)|) := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hw_not)
    have hpt : Filter.Tendsto (fun n => v n w) Filter.atTop (nhds (g w)) :=
      hunif.tendsto_at (haff_mem w (Metric.ball_subset_closedBall hw))
    have hP_lim : Filter.Tendsto (fun n => poissonIntegral (v n) w) Filter.atTop
        (nhds (poissonIntegral g w)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      let K_bd : ℝ := (1 + ‖w‖) / (1 - ‖w‖)
      have hK_pos : 0 < K_bd := div_pos (by linarith [norm_nonneg w]) (by linarith)
      have hδ_unif := Metric.tendstoUniformlyOn_iff.mp hunif (ε / (K_bd + 1)) (by positivity)
      filter_upwards [hδ_unif] with n hn
      have hvn_ci : CircleIntegrable (v n) 0 1 :=
        ((hv_cont n).mono Metric.sphere_subset_closedBall).circleIntegrable zero_le_one
      have hci1 : CircleIntegrable (_root_.poissonKernel 0 w • v n) 0 1 :=
        hvn_ci.continuousOn_smul hcont_k
      have hci2 : CircleIntegrable (_root_.poissonKernel 0 w • g) 0 1 :=
        hg_ci.continuousOn_smul hcont_k
      have hsub_eq : poissonIntegral (v n) w - poissonIntegral g w =
          Real.circleAverage (fun ζ => _root_.poissonKernel 0 w ζ * (v n ζ - g ζ)) 0 1 := by
        unfold poissonIntegral
        refine (Real.circleAverage_fun_sub hci1 hci2).symm.trans ?_
        refine Real.circleAverage_congr_sphere fun ζ _ => ?_
        dsimp
        ring
      rw [Real.dist_eq, hsub_eq]
      have habs_cont : ContinuousOn
          (fun ζ => |_root_.poissonKernel 0 w ζ * (v n ζ - g ζ)|) (Metric.sphere 0 1) := by
        have hk_sph : ContinuousOn (_root_.poissonKernel 0 w) (Metric.sphere 0 1) := by
          simpa [abs_of_pos zero_lt_one] using hcont_k
        exact continuous_abs.comp_continuousOn
          (hk_sph.mul (((hv_cont n).mono Metric.sphere_subset_closedBall).sub
            (hg_cont.mono Metric.sphere_subset_closedBall)))
      have habs_ci : CircleIntegrable
          |(fun ζ => _root_.poissonKernel 0 w ζ * (v n ζ - g ζ))| 0 1 :=
        habs_cont.circleIntegrable zero_le_one
      have hbd_sph : ∀ ζ ∈ Metric.sphere (0 : ℂ) |(1 : ℝ)|,
          |_root_.poissonKernel 0 w ζ * (v n ζ - g ζ)| ≤ K_bd * (ε / (K_bd + 1)) := by
        intro ζ hζ
        have hζ1 : ζ ∈ Metric.sphere (0 : ℂ) 1 := by simpa [abs_of_pos zero_lt_one] using hζ
        have hk_nonneg : 0 ≤ _root_.poissonKernel 0 w ζ := by
          have hlo := le_re_herglotzRieszKernel hζ1 hw
          have hk_eq : _root_.poissonKernel 0 w ζ =
              ((ζ - 0 + (w - 0)) / ((ζ - 0) - (w - 0))).re := by
            rw [poissonKernel_eq_re_herglotzRieszKernel]; rfl
          rw [hk_eq]
          refine le_trans ?_ hlo
          rw [sub_zero]
          exact div_nonneg (by linarith) (by linarith [norm_nonneg w])
        have hk_le : _root_.poissonKernel 0 w ζ ≤ K_bd := by
          have hhi := re_herglotzRieszKernel_le hζ1 hw
          have hk_eq : _root_.poissonKernel 0 w ζ =
              ((ζ - 0 + (w - 0)) / ((ζ - 0) - (w - 0))).re := by
            rw [poissonKernel_eq_re_herglotzRieszKernel]; rfl
          rw [hk_eq]
          simpa [K_bd, sub_zero] using hhi
        have hv_le : |v n ζ - g ζ| ≤ ε / (K_bd + 1) := by
          have hlt := hn (a + (R : ℂ) * ζ) (haff_mem ζ (Metric.sphere_subset_closedBall hζ1))
          rw [Real.dist_eq, abs_sub_comm] at hlt
          exact hlt.le
        calc |_root_.poissonKernel 0 w ζ * (v n ζ - g ζ)|
            = _root_.poissonKernel 0 w ζ * |v n ζ - g ζ| := by
              rw [abs_mul, abs_of_nonneg hk_nonneg]
          _ ≤ K_bd * (ε / (K_bd + 1)) :=
              mul_le_mul hk_le hv_le (abs_nonneg _) hK_pos.le
      have hca_le := (Real.abs_circleAverage_le_circleAverage_abs).trans
        (Real.circleAverage_mono_on_of_le_circle habs_ci hbd_sph)
      refine lt_of_le_of_lt hca_le ?_
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    exact tendsto_nhds_unique hpt (hP_lim.congr fun n => (hv_rep n w hw).symm)
  obtain ⟨_, hP_math, _⟩ := theorem11_7_real hg_ci
  have hg_math : InnerProductSpace.HarmonicOnNhd g (Metric.ball 0 1) := by
    intro w hw
    have hev : poissonIntegral g =ᶠ[nhds w] g :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Metric.ball 0 1, Metric.isOpen_ball.mem_nhds hw, fun z hz => (hg_eq_P z hz).symm⟩
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).mp (hP_math w hw)
  obtain ⟨G, hG_ana, hG_re⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hg_math
  let L_aff : ℂ → ℂ := fun z => (z - a) / (R : ℂ)
  let F : ℂ → ℂ := fun z => G (L_aff z)
  have hR_c_ne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR_pos.ne'
  have hmap : ∀ z ∈ Metric.ball a R, L_aff z ∈ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    dsimp [L_aff]
    rw [Metric.mem_ball, dist_zero_right, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR_pos, div_lt_one hR_pos]
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hF_ana : AnalyticAt ℂ F a := by
    have hlin : AnalyticAt ℂ L_aff a :=
      ((analyticAt_id.sub analyticAt_const).mul analyticAt_const).congr
        (Filter.Eventually.of_forall fun z => (div_eq_mul_inv (z - a) (R : ℂ)).symm)
    exact (hG_ana (L_aff a) (hmap a (Metric.mem_ball_self hR_pos))).comp hlin
  have hev : (fun z => (F z).re) =ᶠ[nhds a] f := by
    filter_upwards [Metric.ball_mem_nhds a hR_pos] with z hz
    have hre_eq : (G (L_aff z)).re = g (L_aff z) := hG_re (hmap z hz)
    dsimp [F]
    rw [hre_eq]
    dsimp [g, L_aff]
    congr 1
    field_simp [hR_c_ne]
    ring
  exact (InnerProductSpace.harmonicAt_congr_nhds hev).mp hF_ana.harmonicAt_re

/-- Locally uniform limits of complex-valued weakly harmonic functions on an open set `Ω ⊆ ℂ`
are weakly harmonic on `Ω`. -/
theorem HarmonicOn.of_tendstoLocallyUniformlyOn_complex {u : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hu : ∀ n, HarmonicOn (u n) Ω)
    (hlim : TendstoLocallyUniformlyOn u f Filter.atTop Ω) :
    HarmonicOn f Ω := by
  have hre_lim : TendstoLocallyUniformlyOn (fun n => Complex.reCLM ∘ u n)
      (Complex.reCLM ∘ f) Filter.atTop Ω :=
    Complex.reCLM.uniformContinuous.comp_tendstoLocallyUniformlyOn hlim
  have him_lim : TendstoLocallyUniformlyOn (fun n => Complex.imCLM ∘ u n)
      (Complex.imCLM ∘ f) Filter.atTop Ω :=
    Complex.imCLM.uniformContinuous.comp_tendstoLocallyUniformlyOn hlim
  have hre : InnerProductSpace.HarmonicOnNhd (Complex.reCLM ∘ f) Ω :=
    (harmonicOn_iff_harmonicOnNhd_real hΩ).mp <|
      HarmonicOn.of_tendstoLocallyUniformlyOn_real hΩ (fun n => (hu n).comp_clm hΩ Complex.reCLM) hre_lim
  have him : InnerProductSpace.HarmonicOnNhd (Complex.imCLM ∘ f) Ω :=
    (harmonicOn_iff_harmonicOnNhd_real hΩ).mp <|
      HarmonicOn.of_tendstoLocallyUniformlyOn_real hΩ (fun n => (hu n).comp_clm hΩ Complex.imCLM) him_lim
  rw [harmonicOn_iff_harmonicOnNhd_complex hΩ]
  intro z hz
  let L_I : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight Complex.I
  have hsum : InnerProductSpace.HarmonicAt
      (fun w => Complex.ofRealCLM ((f w).re) + L_I ((f w).im)) z :=
    ((hre z hz).comp_CLM Complex.ofRealCLM).add ((him z hz).comp_CLM L_I)
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hsum
  refine Filter.Eventually.of_forall fun w => ?_
  change ((f w).re : ℂ) + (f w).im • Complex.I = f w
  rw [Complex.real_smul, Complex.re_add_im]

/-- 11.11(a) (Harnack's inequalities): if `u : ℂ → ℝ` is weakly harmonic and nonnegative on
`Metric.ball a R` (`0 < R`), then for every `z ∈ Metric.ball a R` with `r = ‖z - a‖`,
`((R - r) / (R + r)) * u a ≤ u z` and `u z ≤ ((R + r) / (R - r)) * u a`. -/
theorem theorem11_11_harnack_ineq {a : ℂ} {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : HarmonicOn u (Metric.ball a R)) (hu_nonneg : ∀ z ∈ Metric.ball a R, 0 ≤ u z)
    {z : ℂ} (hz : z ∈ Metric.ball a R) :
    ((R - ‖z - a‖) / (R + ‖z - a‖)) * u a ≤ u z ∧
      u z ≤ ((R + ‖z - a‖) / (R - ‖z - a‖)) * u a := by
  let r : ℝ := ‖z - a‖
  have hr_nonneg : 0 ≤ r := norm_nonneg _
  have hr_lt : r < R := by simpa [r, Metric.mem_ball, dist_eq_norm] using hz
  have hstep : ∀ R' : ℝ, r < R' → R' < R →
      ((R' - r) / (R' + r)) * u a ≤ u z ∧ u z ≤ ((R' + r) / (R' - r)) * u a := by
    intro R' hrR' hR'R
    have hR'_pos : 0 < R' := lt_of_le_of_lt hr_nonneg hrR'
    have hcb_sub : Metric.closedBall a R' ⊆ Metric.ball a R :=
      Metric.closedBall_subset_ball hR'R
    have hu_cont' : ContinuousOn u (Metric.closedBall a R') :=
      hu.continuousOn.mono hcb_sub
    have hu_harm' : HarmonicOn u (Metric.ball a R') :=
      hu.mono (Metric.ball_subset_closedBall.trans hcb_sub)
    have hrep := ((theorem11_10 hR'_pos).1 hu_cont' hu_harm').1
    have hz' : z ∈ Metric.ball a R' := by simpa [Metric.mem_ball, dist_eq_norm, r] using hrR'
    have hu_math' : InnerProductSpace.HarmonicOnNhd u (Metric.ball a |R'|) := by
      rw [abs_of_pos hR'_pos]
      exact (harmonicOn_iff_harmonicOnNhd_real Metric.isOpen_ball).mp hu_harm'
    have hu_hcl' : InnerProductSpace.HarmonicContOnCl u (Metric.ball a |R'|) := by
      refine ⟨hu_math', ?_⟩
      rw [abs_of_pos hR'_pos, closure_ball a hR'_pos.ne']
      exact hu_cont'
    have hua : Real.circleAverage u a R' = u a := hu_hcl'.circleAverage_eq
    have hu_ci : CircleIntegrable u a R' :=
      (hu_cont'.mono Metric.sphere_subset_closedBall).circleIntegrable hR'_pos.le
    have hz_not : z ∉ Metric.sphere a |R'| := by
      rw [abs_of_pos hR'_pos, Metric.mem_sphere, dist_eq_norm]
      exact hrR'.ne
    have hcont_k : ContinuousOn (_root_.poissonKernel a z) (Metric.sphere a |R'|) := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hz_not)
    have hci_k : CircleIntegrable (_root_.poissonKernel a z • u) a R' :=
      hu_ci.continuousOn_smul hcont_k
    have hci_lo : CircleIntegrable (((R' - r) / (R' + r)) • u) a R' := hu_ci.smul _
    have hci_hi : CircleIntegrable (((R' + r) / (R' - r)) • u) a R' := hu_ci.smul _
    have hlo_sph : ∀ ζ ∈ Metric.sphere a |R'|,
        (((R' - r) / (R' + r)) • u) ζ ≤ (_root_.poissonKernel a z • u) ζ := by
      intro ζ hζ
      have hζ' : ζ ∈ Metric.sphere a R' := by simpa [abs_of_pos hR'_pos] using hζ
      have huζ : 0 ≤ u ζ := hu_nonneg ζ (hcb_sub (Metric.sphere_subset_closedBall hζ'))
      have hk_eq : _root_.poissonKernel a z ζ =
          ((ζ - a + (z - a)) / ((ζ - a) - (z - a))).re := by
        rw [poissonKernel_eq_re_herglotzRieszKernel]; rfl
      dsimp
      rw [hk_eq]
      exact mul_le_mul_of_nonneg_right (le_re_herglotzRieszKernel hζ' hz') huζ
    have hhi_sph : ∀ ζ ∈ Metric.sphere a |R'|,
        (_root_.poissonKernel a z • u) ζ ≤ (((R' + r) / (R' - r)) • u) ζ := by
      intro ζ hζ
      have hζ' : ζ ∈ Metric.sphere a R' := by simpa [abs_of_pos hR'_pos] using hζ
      have huζ : 0 ≤ u ζ := hu_nonneg ζ (hcb_sub (Metric.sphere_subset_closedBall hζ'))
      have hk_eq : _root_.poissonKernel a z ζ =
          ((ζ - a + (z - a)) / ((ζ - a) - (z - a))).re := by
        rw [poissonKernel_eq_re_herglotzRieszKernel]; rfl
      dsimp
      rw [hk_eq]
      exact mul_le_mul_of_nonneg_right (re_herglotzRieszKernel_le hζ' hz') huζ
    have hlo := Real.circleAverage_mono hci_lo hci_k hlo_sph
    have hhi := Real.circleAverage_mono hci_k hci_hi hhi_sph
    rw [hrep z hz', Real.circleAverage_smul, hua, smul_eq_mul] at hlo
    rw [hrep z hz', Real.circleAverage_smul, hua, smul_eq_mul] at hhi
    exact ⟨hlo, hhi⟩
  let seq : ℕ → ℝ := fun n => R - (R - r) / ((n : ℝ) + 2)
  have hseq_gt : ∀ n, r < seq n := by
    intro n
    dsimp [seq]
    have hlt : (R - r) / ((n : ℝ) + 2) < R - r :=
      div_lt_self (sub_pos.mpr hr_lt) (by linarith)
    linarith
  have hseq_lt : ∀ n, seq n < R := by
    intro n
    dsimp [seq]
    have hpos : 0 < (R - r) / ((n : ℝ) + 2) := div_pos (sub_pos.mpr hr_lt) (by positivity)
    linarith
  have hseq_lim : Filter.Tendsto seq Filter.atTop (nhds R) := by
    have h0 : Filter.Tendsto (fun n : ℕ => (R - r) / ((n : ℝ) + 2)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        (Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds)
    simpa [seq] using tendsto_const_nhds.sub h0
  have hlim_lo : Filter.Tendsto (fun n => ((seq n - r) / (seq n + r)) * u a)
      Filter.atTop (nhds (((R - r) / (R + r)) * u a)) := by
    refine Filter.Tendsto.mul ?_ tendsto_const_nhds
    exact (hseq_lim.sub tendsto_const_nhds).div (hseq_lim.add tendsto_const_nhds) (by linarith)
  have hlim_hi : Filter.Tendsto (fun n => ((seq n + r) / (seq n - r)) * u a)
      Filter.atTop (nhds (((R + r) / (R - r)) * u a)) := by
    refine Filter.Tendsto.mul ?_ tendsto_const_nhds
    exact (hseq_lim.add tendsto_const_nhds).div (hseq_lim.sub tendsto_const_nhds) (by linarith)
  exact ⟨le_of_tendsto hlim_lo (Filter.Eventually.of_forall fun n => (hstep (seq n) (hseq_gt n) (hseq_lt n)).1),
    ge_of_tendsto hlim_hi (Filter.Eventually.of_forall fun n => (hstep (seq n) (hseq_gt n) (hseq_lt n)).2)⟩

/-- 11.11(b) (Harnack's monotone convergence theorem): if `{u_n}` is a pointwise nondecreasing
sequence of real-valued weakly harmonic functions on a region (connected open set) `Ω ⊆ ℂ`, then
either `u_n → +∞` uniformly on every compact subset of `Ω`, or `{u_n}` converges uniformly on
every compact subset of `Ω` (i.e., locally uniformly on `Ω`) to a weakly harmonic function `U`
on `Ω`. -/
theorem theorem11_11 {Ω : Set ℂ} (hΩ_open : IsOpen Ω) (hΩ_conn : IsPreconnected Ω)
    {u : ℕ → ℂ → ℝ} (hu_harm : ∀ n, HarmonicOn (u n) Ω)
    (hu_mono : ∀ n, ∀ z ∈ Ω, u n z ≤ u (n + 1) z) :
    (∀ K, IsCompact K → K ⊆ Ω → ∀ M : ℝ, ∀ᶠ n in Filter.atTop, ∀ z ∈ K, M ≤ u n z) ∨
      (∃ U : ℂ → ℝ, HarmonicOn U Ω ∧ TendstoLocallyUniformlyOn u U Filter.atTop Ω ∧
        ∀ K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn u U Filter.atTop K) := by
  have hu_le : ∀ {m n : ℕ}, m ≤ n → ∀ z ∈ Ω, u m z ≤ u n z := by
    intro m n hmn z hz
    induction hmn with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hu_mono _ z hz)
  let v : ℕ → ℂ → ℝ := fun n z => u n z - u 0 z
  have hv_harm : ∀ n, HarmonicOn (v n) Ω :=
    fun n => HarmonicOn.sub hΩ_open (hu_harm n) (hu_harm 0)
  have hv_nonneg : ∀ n, ∀ z ∈ Ω, 0 ≤ v n z :=
    fun n z hz => sub_nonneg.mpr (hu_le (Nat.zero_le n) z hz)
  have hv_le : ∀ {m n : ℕ}, m ≤ n → ∀ z ∈ Ω, v m z ≤ v n z :=
    fun hmn z hz => sub_le_sub_right (hu_le hmn z hz) _
  have hhalf_ball : ∀ {a : ℂ} {R : ℝ}, 0 < R → Metric.ball a R ⊆ Ω →
      ∀ {w : ℂ → ℝ}, HarmonicOn w (Metric.ball a R) → (∀ z ∈ Metric.ball a R, 0 ≤ w z) →
      ∀ z ∈ Metric.ball a (R / 2), (1 / 3 : ℝ) * w a ≤ w z ∧ w z ≤ 3 * w a := by
    intro a R hR hsub w hw hw_nn z hz
    have hz_big : z ∈ Metric.ball a R := Metric.ball_subset_ball (by linarith) hz
    have hineq := theorem11_11_harnack_ineq hR hw hw_nn hz_big
    have hr : ‖z - a‖ < R / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hwa : 0 ≤ w a := hw_nn a (Metric.mem_ball_self hR)
    have hlo_fac : (1 / 3 : ℝ) ≤ (R - ‖z - a‖) / (R + ‖z - a‖) := by
      rw [div_le_div_iff₀ (by positivity) (by linarith [norm_nonneg (z - a)])]
      linarith
    have hhi_fac : (R + ‖z - a‖) / (R - ‖z - a‖) ≤ 3 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    exact ⟨(mul_le_mul_of_nonneg_right hlo_fac hwa).trans hineq.1,
      hineq.2.trans (mul_le_mul_of_nonneg_right hhi_fac hwa)⟩
  let S : Set ℂ := {z ∈ Ω | BddAbove (Set.range fun n => v n z)}
  let T : Set ℂ := {z ∈ Ω | ¬ BddAbove (Set.range fun n => v n z)}
  have hS_open : IsOpen S := by
    rw [Metric.isOpen_iff]
    rintro a ⟨haΩ, B, hB⟩
    obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hΩ_open a haΩ
    refine ⟨R / 2, half_pos hR, fun z hz => ⟨hball (Metric.ball_subset_ball (by linarith) hz),
      3 * B, ?_⟩⟩
    rintro _ ⟨n, rfl⟩
    have hb_n := (hhalf_ball hR hball ((hv_harm n).mono hball)
      (fun w hw => hv_nonneg n w (hball hw)) z hz).2
    have hva : v n a ≤ B := hB ⟨n, rfl⟩
    linarith
  have hT_open : IsOpen T := by
    rw [Metric.isOpen_iff]
    rintro a ⟨haΩ, hnb⟩
    obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hΩ_open a haΩ
    refine ⟨R / 2, half_pos hR, fun z hz => ⟨hball (Metric.ball_subset_ball (by linarith) hz), ?_⟩⟩
    rintro ⟨B, hB⟩
    refine hnb ⟨3 * B, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hb_n := (hhalf_ball hR hball ((hv_harm n).mono hball)
      (fun w hw => hv_nonneg n w (hball hw)) z hz).1
    have hvz : v n z ≤ B := hB ⟨n, rfl⟩
    linarith
  by_cases hS_ne : (Ω ∩ S).Nonempty
  · right
    have hΩ_sub_S : Ω ⊆ S := by
      intro z hz
      by_contra hz_not
      have hzT : z ∈ T := ⟨hz, fun hb => hz_not ⟨hz, hb⟩⟩
      have hT_ne : (Ω ∩ T).Nonempty := ⟨z, hz, hzT⟩
      have hcov : Ω ⊆ S ∪ T := fun w hw => by
        by_cases hb : BddAbove (Set.range fun n => v n w)
        · exact Or.inl ⟨hw, hb⟩
        · exact Or.inr ⟨hw, hb⟩
      obtain ⟨w, _, hwS, hwT⟩ := hΩ_conn S T hS_open hT_open hcov hS_ne hT_ne
      exact hwT.2 hwS.2
    let V : ℂ → ℝ := fun z => ⨆ n : ℕ, v n z
    let U : ℂ → ℝ := fun z => V z + u 0 z
    have hv_tendsto : ∀ z ∈ Ω, Filter.Tendsto (fun n => v n z) Filter.atTop (nhds (V z)) :=
      fun z hz => tendsto_atTop_ciSup (fun m n hmn => hv_le hmn z hz) (hΩ_sub_S hz).2
    have hloc : TendstoLocallyUniformlyOn u U Filter.atTop Ω := by
      refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun a ha => ?_
      obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hΩ_open a ha
      refine ⟨Metric.ball a (R / 2),
        nhdsWithin_le_nhds (Metric.ball_mem_nhds a (half_pos hR)), ?_⟩
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have hva_lim := Metric.tendsto_nhds.mp (hv_tendsto a ha) (ε / 4) (by positivity)
      filter_upwards [hva_lim] with m hm
      intro z hz
      have hzΩ : z ∈ Ω := hball (Metric.ball_subset_ball (by linarith) hz)
      have hdiff_le : ∀ n ≥ m, v n z - v m z ≤ 3 * (V a - v m a) := by
        intro n hmn
        have hw_harm : HarmonicOn (fun w => v n w - v m w) (Metric.ball a R) :=
          (HarmonicOn.sub hΩ_open (hv_harm n) (hv_harm m)).mono hball
        have hw_nn : ∀ w ∈ Metric.ball a R, 0 ≤ v n w - v m w :=
          fun w hw => sub_nonneg.mpr (hv_le hmn w (hball hw))
        have hb := (hhalf_ball hR hball hw_harm hw_nn z hz).2
        have hvna : v n a ≤ V a := le_ciSup (hΩ_sub_S ha).2 n
        linarith
      have hVz_sub : V z - v m z ≤ 3 * (V a - v m a) := by
        have hlim_sub : Filter.Tendsto (fun n => v n z - v m z) Filter.atTop
            (nhds (V z - v m z)) :=
          (hv_tendsto z hzΩ).sub tendsto_const_nhds
        exact le_of_tendsto hlim_sub (Filter.eventually_atTop.mpr ⟨m, hdiff_le⟩)
      have hVz_ge : v m z ≤ V z := le_ciSup (hΩ_sub_S hzΩ).2 m
      have hVa_ge : v m a ≤ V a := le_ciSup (hΩ_sub_S ha).2 m
      have hma : V a - v m a < ε / 4 := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hVa_ge), neg_sub] at hm
        exact hm
      have heq_dist : dist (U z) (u m z) = V z - v m z := by
        dsimp [U, v]
        rw [Real.dist_eq, show V z + u 0 z - u m z = V z - (u m z - u 0 z) by ring,
          abs_of_nonneg (sub_nonneg.mpr hVz_ge)]
      rw [heq_dist]
      linarith
    exact ⟨U, HarmonicOn.of_tendstoLocallyUniformlyOn_real hΩ_open hu_harm hloc, hloc,
      fun K hK hK_sub =>
        (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ_open).mp hloc K hK_sub hK⟩
  · left
    have hΩ_sub_T : Ω ⊆ T := by
      intro z hz
      refine ⟨hz, fun hb => hS_ne ⟨z, hz, hz, hb⟩⟩
    intro K hK hK_sub M
    rcases K.eq_empty_or_nonempty with rfl | hK_ne
    · exact Filter.Eventually.of_forall fun _ _ hz => False.elim hz
    obtain ⟨z_min, hz_min_mem, hz_min⟩ :=
      hK.exists_isMinOn hK_ne ((hu_harm 0).continuousOn.mono hK_sub)
    let m₀ : ℝ := u 0 z_min
    have hrad : ∀ x ∈ K, ∃ R : ℝ, 0 < R ∧ Metric.ball x R ⊆ Ω :=
      fun x hx => Metric.isOpen_iff.mp hΩ_open x (hK_sub hx)
    choose R_fn hR_pos hR_sub using fun x : K => hrad x.1 x.2
    obtain ⟨F, hF_cov⟩ := hK.elim_finite_subcover
      (fun x : K => Metric.ball x.1 (R_fn x / 2))
      (fun x => Metric.isOpen_ball)
      (fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (half_pos (hR_pos ⟨z, hz⟩))⟩)
    let B_tgt : ℝ := 3 * (|M - m₀| + 1)
    have hex_N : ∀ x : K, ∃ N : ℕ, B_tgt < v N x.1 := by
      intro x
      obtain ⟨_, ⟨N, rfl⟩, hN⟩ := not_bddAbove_iff.mp (hΩ_sub_T (hK_sub x.2)).2 B_tgt
      exact ⟨N, hN⟩
    choose N_fn hN_gt using hex_N
    refine Filter.eventually_atTop.mpr ⟨F.sup N_fn, fun n hn z hz => ?_⟩
    obtain ⟨x, hxF, hzx⟩ := Set.mem_iUnion₂.mp (hF_cov hz)
    have hNx : N_fn x ≤ n := le_trans (Finset.le_sup hxF) hn
    have hv_nx : B_tgt < v n x.1 := lt_of_lt_of_le (hN_gt x) (hv_le hNx x.1 (hK_sub x.2))
    have hlo := (hhalf_ball (hR_pos x) (hR_sub x) ((hv_harm n).mono (hR_sub x))
      (fun w hw => hv_nonneg n w (hR_sub x hw)) z hzx).1
    have hu0_ge : m₀ ≤ u 0 z := hz_min hz
    have habs : M - m₀ ≤ |M - m₀| := le_abs_self _
    have hvnz : M - m₀ ≤ v n z := by
      dsimp [B_tgt] at hv_nx
      linarith
    dsimp [v] at hvnz
    linarith

/-- 11.12 (Definition): Rudin's shrinking-radii mean-value property on an open set `Ω ⊆ ℂ`: `u` is
continuous on `Ω` and at every `z ∈ Ω` there is a positive sequence `r_n → 0` along which
`Real.circleAverage u z (r_n) = u z` (`= (2π)⁻¹ ∫_{-π}^π u(z + r_n e^{it}) dt`). -/
def HasMeanValueProperty {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℂ → F) (Ω : Set ℂ) : Prop :=
  ContinuousOn u Ω ∧
    ∀ z ∈ Ω, ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Filter.Tendsto r Filter.atTop (nhds 0) ∧
      ∀ n, Real.circleAverage u z (r n) = u z

/-- Equivalence of `Real.circleAverage u z r` with Rudin's `[-π, π]` angular integral. -/
theorem circleAverage_eq_integral_neg_pi_pi {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℂ → F) (z : ℂ) (r : ℝ) :
    Real.circleAverage u z r =
      (2 * Real.pi)⁻¹ • ∫ t in (-Real.pi)..Real.pi,
        u (z + (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) := by
  rw [Real.circleAverage_def]
  have hper : Function.Periodic (fun t : ℝ => u (circleMap z r t)) (2 * Real.pi) :=
    fun t => by dsimp only; rw [periodic_circleMap]
  have hint := hper.intervalIntegral_add_eq (-Real.pi) 0
  have hend1 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have hend2 : (0 : ℝ) + 2 * Real.pi = 2 * Real.pi := by ring
  rw [hend1, hend2] at hint
  rw [← hint]
  rfl

/-- 11.12 (Harmonic functions have the mean-value property): every real- or complex-valued weakly
harmonic function on an open set `Ω` satisfies `Real.circleAverage u z r = u z` on every closed
disc `closedBall z r ⊆ Ω` (`0 < r`), and in particular satisfies `HasMeanValueProperty u Ω`. -/
theorem theorem11_12_real {u : ℂ → ℝ} {Ω : Set ℂ} (hΩ : IsOpen Ω) (hu : HarmonicOn u Ω) :
    (∀ {z : ℂ} {r : ℝ}, 0 < r → Metric.closedBall z r ⊆ Ω → Real.circleAverage u z r = u z) ∧
      HasMeanValueProperty u Ω := by
  have hu_math : InnerProductSpace.HarmonicOnNhd u Ω :=
    (harmonicOn_iff_harmonicOnNhd_real hΩ).mp hu
  have hca : ∀ {z : ℂ} {r : ℝ}, 0 < r → Metric.closedBall z r ⊆ Ω →
      Real.circleAverage u z r = u z := by
    intro z r hr hsub
    have hnhd : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall z |r|) := by
      rw [abs_of_pos hr]
      exact hu_math.mono hsub
    exact hnhd.circleAverage_eq
  refine ⟨hca, hu.continuousOn, fun z hz => ?_⟩
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hΩ z hz
  refine ⟨fun n => R / ((n : ℝ) + 2), fun n => div_pos hR (by positivity),
    tendsto_const_nhds.div_atTop
      (Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds),
    fun n => hca (div_pos hR (by positivity)) ?_⟩
  refine (Metric.closedBall_subset_ball ?_).trans hball
  exact div_lt_self hR (by linarith)

theorem theorem11_12 {u : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω) (hu : HarmonicOn u Ω) :
    (∀ {z : ℂ} {r : ℝ}, 0 < r → Metric.closedBall z r ⊆ Ω → Real.circleAverage u z r = u z) ∧
      HasMeanValueProperty u Ω := by
  have hu_math : InnerProductSpace.HarmonicOnNhd u Ω :=
    (harmonicOn_iff_harmonicOnNhd_complex hΩ).mp hu
  have hca : ∀ {z : ℂ} {r : ℝ}, 0 < r → Metric.closedBall z r ⊆ Ω →
      Real.circleAverage u z r = u z := by
    intro z r hr hsub
    have hnhd : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall z |r|) := by
      rw [abs_of_pos hr]
      exact hu_math.mono hsub
    exact hnhd.circleAverage_eq
  refine ⟨hca, hu.continuousOn, fun z hz => ?_⟩
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hΩ z hz
  refine ⟨fun n => R / ((n : ℝ) + 2), fun n => div_pos hR (by positivity),
    tendsto_const_nhds.div_atTop
      (Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds),
    fun n => hca (div_pos hR (by positivity)) ?_⟩
  refine (Metric.closedBall_subset_ball ?_).trans hball
  exact div_lt_self hR (by linarith)

private theorem strict_circleAverage_lt_of_exists_lt {h : ℂ → ℝ} {w₀ : ℂ} {r M : ℝ}
    (hh_cont : ContinuousOn h (Metric.sphere w₀ r)) (hr : 0 < r)
    (hle : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), h (circleMap w₀ r θ) ≤ M)
    (hlt : ∃ θ₁ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), h (circleMap w₀ r θ₁) < M) :
    Real.circleAverage h w₀ r < M := by
  obtain ⟨θ₁, hθ₁_mem, hθ₁_lt⟩ := hlt
  let φ : ℝ → ℝ := fun θ => h (circleMap w₀ r θ)
  have hφ_cont : ContinuousOn φ (Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    hh_cont.comp (continuous_circleMap w₀ r).continuousOn
      fun θ _ => circleMap_mem_sphere w₀ hr.le θ
  let ε : ℝ := (M - φ θ₁) / 2
  have hε : 0 < ε := by dsimp [ε, φ]; linarith
  have hnhd := Metric.continuousWithinAt_iff.mp (hφ_cont θ₁ hθ₁_mem) ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := hnhd
  have hsub_int : ∃ a₁ b₁ : ℝ, 0 ≤ a₁ ∧ a₁ < b₁ ∧ b₁ ≤ 2 * Real.pi ∧
      ∀ θ ∈ Set.Icc a₁ b₁, ε ≤ M - φ θ := by
    by_cases hmid : θ₁ ≤ Real.pi
    · refine ⟨θ₁, min (2 * Real.pi) (θ₁ + δ / 2), hθ₁_mem.1, ?_, min_le_left _ _, ?_⟩
      · exact lt_min (by linarith [Real.pi_pos]) (by linarith)
      · intro θ hθ
        have hθ_Icc : θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) :=
          ⟨le_trans hθ₁_mem.1 hθ.1, le_trans hθ.2 (min_le_left _ _)⟩
        have hdist : dist θ θ₁ < δ := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hθ.1)]
          have hle_d : θ ≤ θ₁ + δ / 2 := le_trans hθ.2 (min_le_right _ _)
          linarith
        have hclose := hδ hθ_Icc hdist
        rw [Real.dist_eq] at hclose
        have hlt_ε := (abs_lt.mp hclose).2
        dsimp [ε] at hlt_ε ⊢
        linarith
    · push Not at hmid
      refine ⟨max 0 (θ₁ - δ / 2), θ₁, le_max_left _ _, ?_, hθ₁_mem.2, ?_⟩
      · exact max_lt (by linarith [Real.pi_pos]) (by linarith)
      · intro θ hθ
        have hθ_Icc : θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) :=
          ⟨le_trans (le_max_left _ _) hθ.1, le_trans hθ.2 hθ₁_mem.2⟩
        have hdist : dist θ θ₁ < δ := by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hθ.2), neg_sub]
          have hge_d : θ₁ - δ / 2 ≤ θ := le_trans (le_max_right _ _) hθ.1
          linarith
        have hclose := hδ hθ_Icc hdist
        rw [Real.dist_eq] at hclose
        have hlt_ε := (abs_lt.mp hclose).2
        dsimp [ε] at hlt_ε ⊢
        linarith
  obtain ⟨a₁, b₁, ha₁0, ha₁b₁, hb₁2π, hgap⟩ := hsub_int
  let ψ : ℝ → ℝ := fun θ => M - φ θ
  have hψ_cont : ContinuousOn ψ (Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    continuousOn_const.sub hφ_cont
  have hψ_int : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v → v ≤ 2 * Real.pi →
      IntervalIntegrable ψ MeasureTheory.volume u v := by
    intro u v hu huv hv
    refine (hψ_cont.mono ?_).intervalIntegrable (μ := MeasureTheory.volume)
    rw [Set.uIcc_of_le huv]
    exact fun θ hθ => ⟨le_trans hu hθ.1, le_trans hθ.2 hv⟩
  have hi1 := hψ_int le_rfl ha₁0 (le_trans ha₁b₁.le hb₁2π)
  have hi2 := hψ_int ha₁0 ha₁b₁.le hb₁2π
  have hi3 := hψ_int (le_trans ha₁0 ha₁b₁.le) hb₁2π le_rfl
  have hsplit : ∫ θ in (0 : ℝ)..(2 * Real.pi), ψ θ =
      (∫ θ in (0 : ℝ)..a₁, ψ θ) + (∫ θ in a₁..b₁, ψ θ) + (∫ θ in b₁..(2 * Real.pi), ψ θ) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
      intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3]
  have hnn1 : 0 ≤ ∫ θ in (0 : ℝ)..a₁, ψ θ :=
    intervalIntegral.integral_nonneg ha₁0 fun θ hθ =>
      sub_nonneg.mpr (hle θ ⟨hθ.1, le_trans hθ.2 (le_trans ha₁b₁.le hb₁2π)⟩)
  have hnn3 : 0 ≤ ∫ θ in b₁..(2 * Real.pi), ψ θ :=
    intervalIntegral.integral_nonneg hb₁2π fun θ hθ =>
      sub_nonneg.mpr (hle θ ⟨le_trans (le_trans ha₁0 ha₁b₁.le) hθ.1, hθ.2⟩)
  have hmid_pos : (b₁ - a₁) * ε ≤ ∫ θ in a₁..b₁, ψ θ := by
    have hconst : ∫ _ in a₁..b₁, ε = (b₁ - a₁) * ε := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [← hconst]
    exact intervalIntegral.integral_mono_on ha₁b₁.le intervalIntegrable_const hi2 hgap
  have hψ_pos : 0 < ∫ θ in (0 : ℝ)..(2 * Real.pi), ψ θ := by
    have : 0 < (b₁ - a₁) * ε := mul_pos (sub_pos.mpr ha₁b₁) hε
    linarith
  have hφ_ii : IntervalIntegrable φ MeasureTheory.volume 0 (2 * Real.pi) := by
    refine (hφ_cont.mono ?_).intervalIntegrable (μ := MeasureTheory.volume)
    rw [Set.uIcc_of_le Real.two_pi_pos.le]
  have hψ_eval : ∫ θ in (0 : ℝ)..(2 * Real.pi), ψ θ =
      (2 * Real.pi) * M - ∫ θ in (0 : ℝ)..(2 * Real.pi), φ θ := by
    dsimp [ψ]
    rw [intervalIntegral.integral_sub intervalIntegrable_const hφ_ii,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  rw [Real.circleAverage_def, smul_eq_mul]
  change (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..(2 * Real.pi), φ θ) < M
  rw [inv_mul_lt_iff₀ Real.two_pi_pos]
  linarith

private theorem nonpos_closedBall_of_shrinking_circleAverage {h : ℂ → ℝ}
    (hh_cont : ContinuousOn h (Metric.closedBall 0 1))
    (hh_bd : ∀ ζ ∈ Metric.sphere (0 : ℂ) 1, h ζ ≤ 0)
    (hh_mvp : ∀ w ∈ Metric.ball (0 : ℂ) 1, ∃ ρ : ℕ → ℝ, (∀ n, 0 < ρ n) ∧
      Filter.Tendsto ρ Filter.atTop (nhds 0) ∧
      ∀ᶠ n in Filter.atTop, Real.circleAverage h w (ρ n) = h w) :
    ∀ w ∈ Metric.closedBall (0 : ℂ) 1, h w ≤ 0 := by
  let K : Set ℂ := Metric.closedBall 0 1
  have hK_comp : IsCompact K := isCompact_closedBall 0 1
  have hK_ne : K.Nonempty := ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  obtain ⟨z_max, hz_max_mem, hz_max⟩ := hK_comp.exists_isMaxOn hK_ne hh_cont
  let M : ℝ := h z_max
  by_cases hM : M ≤ 0
  · exact fun w hw => (hz_max hw).trans hM
  push Not at hM
  exfalso
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK_comp
  let h_sub : K → ℝ := K.domRestrict h
  have hh_sub_cont : Continuous h_sub := continuousOn_iff_continuous_domRestrict.mp hh_cont
  let E_sub : Set K := {x : K | h_sub x = M}
  have hE_closed : IsClosed E_sub := isClosed_eq hh_sub_cont continuous_const
  have hE_comp : IsCompact E_sub := hE_closed.isCompact
  have hE_ne : E_sub.Nonempty := ⟨⟨z_max, hz_max_mem⟩, rfl⟩
  obtain ⟨x₀, hx₀_mem, hx₀_norm⟩ :=
    hE_comp.exists_isMaxOn hE_ne (continuous_norm.comp continuous_subtype_val).continuousOn
  let w₀ : ℂ := x₀.1
  have hw₀_K : w₀ ∈ K := x₀.2
  have hw₀_val : h w₀ = M := hx₀_mem
  have hw₀_ball : w₀ ∈ Metric.ball (0 : ℂ) 1 := by
    have hw₀_le : ‖w₀‖ ≤ 1 := by simpa [K, Metric.mem_closedBall] using hw₀_K
    rcases lt_or_eq_of_le hw₀_le with hlt | heq
    · simpa [Metric.mem_ball] using hlt
    · have hw₀_sph : w₀ ∈ Metric.sphere (0 : ℂ) 1 := by simpa [Metric.mem_sphere] using heq
      linarith [hh_bd w₀ hw₀_sph]
  have hw₀_norm_lt : ‖w₀‖ < 1 := by simpa [Metric.mem_ball] using hw₀_ball
  obtain ⟨ρ, hρ_pos, hρ_lim, hρ_eq⟩ := hh_mvp w₀ hw₀_ball
  have hρ_small : ∀ᶠ n in Filter.atTop, ρ n < 1 - ‖w₀‖ :=
    hρ_lim.eventually (gt_mem_nhds (sub_pos.mpr hw₀_norm_lt))
  obtain ⟨n, hn_eq, hn_lt⟩ := (hρ_eq.and hρ_small).exists
  let r : ℝ := ρ n
  have hr_pos : 0 < r := hρ_pos n
  have hcb_sub_K : Metric.closedBall w₀ r ⊆ K := by
    intro z hz
    have hzw : ‖z - w₀‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hzn : ‖z‖ ≤ 1 := by
      calc ‖z‖ = ‖(z - w₀) + w₀‖ := by ring_nf
        _ ≤ ‖z - w₀‖ + ‖w₀‖ := norm_add_le _ _
        _ ≤ r + ‖w₀‖ := by linarith
        _ ≤ 1 := by dsimp [r]; linarith
    simpa [K, Metric.mem_closedBall] using hzn
  have hex_out : ∃ θ₁ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖w₀‖ < ‖circleMap w₀ r θ₁‖ := by
    by_cases hw0 : w₀ = 0
    · refine ⟨0, ⟨le_rfl, Real.two_pi_pos.le⟩, ?_⟩
      simp [hw0, circleMap, abs_of_pos hr_pos, hr_pos]
    · let θ₀ : ℝ := Complex.arg w₀
      have hnorm_θ₀ : ‖circleMap w₀ r θ₀‖ = ‖w₀‖ + r := by
        have hw₀_polar : (‖w₀‖ : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I) = w₀ :=
          Complex.norm_mul_exp_arg_mul_I w₀
        have hcm : circleMap w₀ r θ₀ =
            (((‖w₀‖ + r : ℝ) : ℂ)) * Complex.exp ((θ₀ : ℂ) * Complex.I) := by
          unfold circleMap
          nth_rw 1 [← hw₀_polar]
          push_cast
          ring
        rw [hcm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith [norm_nonneg w₀]), Complex.norm_exp_ofReal_mul_I, mul_one]
      by_cases hθ₀_nn : 0 ≤ θ₀
      · refine ⟨θ₀, ⟨hθ₀_nn, le_trans (Complex.arg_le_pi w₀) (by linarith [Real.pi_pos])⟩, ?_⟩
        linarith
      · push Not at hθ₀_nn
        refine ⟨θ₀ + 2 * Real.pi, ⟨?_, by linarith⟩, ?_⟩
        · have hgt : -Real.pi < θ₀ := Complex.neg_pi_lt_arg w₀
          linarith [Real.pi_pos]
        · rw [periodic_circleMap w₀ r θ₀, hnorm_θ₀]
          linarith
  obtain ⟨θ₁, hθ₁_mem, hθ₁_gt⟩ := hex_out
  have hθ₁_K : circleMap w₀ r θ₁ ∈ K :=
    hcb_sub_K (Metric.sphere_subset_closedBall (circleMap_mem_sphere w₀ hr_pos.le θ₁))
  have hθ₁_lt_M : h (circleMap w₀ r θ₁) < M := by
    have hle_M : h (circleMap w₀ r θ₁) ≤ M := hz_max hθ₁_K
    refine lt_of_le_of_ne hle_M fun heq_M => ?_
    have hmem_E : (⟨circleMap w₀ r θ₁, hθ₁_K⟩ : K) ∈ E_sub := heq_M
    have hnorm_le : ‖circleMap w₀ r θ₁‖ ≤ ‖w₀‖ := hx₀_norm hmem_E
    linarith
  have hca_lt : Real.circleAverage h w₀ r < M :=
    strict_circleAverage_lt_of_exists_lt
      (hh_cont.mono (Metric.sphere_subset_closedBall.trans hcb_sub_K)) hr_pos
      (fun θ _ => hz_max (hcb_sub_K (Metric.sphere_subset_closedBall
        (circleMap_mem_sphere w₀ hr_pos.le θ))))
      ⟨θ₁, hθ₁_mem, hθ₁_lt_M⟩
  linarith [hn_eq, hw₀_val]

/-- 11.13 (Converse mean-value theorem, real-valued): a continuous real-valued function on an open
set `Ω ⊆ ℂ` having Rudin's shrinking-radii mean-value property (`HasMeanValueProperty u Ω`) is
weakly harmonic on `Ω` (`HarmonicOn u Ω`). -/
theorem theorem11_13_real {u : ℂ → ℝ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hu : HasMeanValueProperty u Ω) : HarmonicOn u Ω := by
  rw [harmonicOn_iff_harmonicOnNhd_real hΩ]
  intro a ha
  obtain ⟨δ, hδ_pos, hball_sub⟩ := Metric.isOpen_iff.mp hΩ a ha
  let R : ℝ := δ / 2
  have hR_pos : 0 < R := half_pos hδ_pos
  have hcb_sub : Metric.closedBall a R ⊆ Ω :=
    (Metric.closedBall_subset_ball (half_lt_self hδ_pos)).trans hball_sub
  let g : ℂ → ℝ := fun w => u (a + (R : ℂ) * w)
  have haff_mem : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, a + (R : ℂ) * w ∈ Metric.closedBall a R := by
    intro w hw
    rw [Metric.mem_closedBall, dist_self_add_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR_pos]
    have hw1 : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hw
    nlinarith
  have hg_cont : ContinuousOn g (Metric.closedBall 0 1) :=
    hu.1.comp (by fun_prop) fun w hw => hcb_sub (haff_mem w hw)
  let P : ℂ → ℝ := poissonExtension g
  have hg_sph : ContinuousOn g (Metric.sphere (0 : ℂ) 1) :=
    hg_cont.mono Metric.sphere_subset_closedBall
  have hP_cont : ContinuousOn P (Metric.closedBall (0 : ℂ) 1) :=
    continuousOn_poissonExtension hg_sph
  have hP_harm : HarmonicOn P (Metric.ball (0 : ℂ) 1) := by
    refine (theorem11_7_real (hg_sph.circleIntegrable zero_le_one)).1.congr_of_isOpen
      Metric.isOpen_ball fun z hz => ?_
    have hz_lt : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
    simp [P, poissonExtension, hz_lt]
  have hP_sph : ∀ ζ ∈ Metric.sphere (0 : ℂ) 1, P ζ = g ζ := by
    intro ζ hζ
    have hζ_eq : ‖ζ‖ = 1 := by simpa [Metric.mem_sphere] using hζ
    simp [P, poissonExtension, hζ_eq]
  obtain ⟨hP_ca, _⟩ := theorem11_12_real Metric.isOpen_ball hP_harm
  have hg_mvp : ∀ w ∈ Metric.ball (0 : ℂ) 1, ∃ ρ : ℕ → ℝ, (∀ n, 0 < ρ n) ∧
      Filter.Tendsto ρ Filter.atTop (nhds 0) ∧
      ∀ n, Real.circleAverage g w (ρ n) = g w := by
    intro w hw
    have hzΩ : a + (R : ℂ) * w ∈ Ω := hcb_sub (haff_mem w (Metric.ball_subset_closedBall hw))
    obtain ⟨r, hr_pos, hr_lim, hr_ca⟩ := hu.2 (a + (R : ℂ) * w) hzΩ
    have hR_c_ne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR_pos.ne'
    refine ⟨fun n => r n / R, fun n => div_pos (hr_pos n) hR_pos,
      by simpa using hr_lim.div_const R, fun n => ?_⟩
    have hcm_eq : ∀ θ : ℝ, g (circleMap w (r n / R) θ) =
        u (circleMap (a + (R : ℂ) * w) (r n) θ) := by
      intro θ
      dsimp [g, circleMap]
      congr 1
      push_cast
      field_simp [hR_c_ne]
      ring
    calc Real.circleAverage g w (r n / R)
        = Real.circleAverage u (a + (R : ℂ) * w) (r n) := by
          simp only [Real.circleAverage_def, hcm_eq]
      _ = u (a + (R : ℂ) * w) := hr_ca n
      _ = g w := rfl
  have hdiff1 : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, g w - P w ≤ 0 := by
    refine nonpos_closedBall_of_shrinking_circleAverage (hg_cont.sub hP_cont)
      (fun ζ hζ => by rw [hP_sph ζ hζ, sub_self]) fun w hw => ?_
    obtain ⟨ρ, hρ_pos, hρ_lim, hρ_ca⟩ := hg_mvp w hw
    have hw_lt : ‖w‖ < 1 := by simpa [Metric.mem_ball] using hw
    refine ⟨ρ, hρ_pos, hρ_lim, ?_⟩
    filter_upwards [hρ_lim.eventually (gt_mem_nhds (sub_pos.mpr hw_lt))] with n hn
    have hcb_ball : Metric.closedBall w (ρ n) ⊆ Metric.ball (0 : ℂ) 1 := by
      intro z hz
      have hzw : ‖z - w‖ ≤ ρ n := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      have hzn : ‖z‖ < 1 := by
        calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
          _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
          _ < (1 - ‖w‖) + ‖w‖ := by linarith
          _ = 1 := sub_add_cancel 1 ‖w‖
      simpa [Metric.mem_ball] using hzn
    have hg_ci : CircleIntegrable g w (ρ n) :=
      (hg_cont.mono ((Metric.sphere_subset_closedBall.trans hcb_ball).trans
        Metric.ball_subset_closedBall)).circleIntegrable (hρ_pos n).le
    have hP_ci : CircleIntegrable P w (ρ n) :=
      (hP_cont.mono ((Metric.sphere_subset_closedBall.trans hcb_ball).trans
        Metric.ball_subset_closedBall)).circleIntegrable (hρ_pos n).le
    rw [Real.circleAverage_fun_sub hg_ci hP_ci, hρ_ca n, hP_ca (hρ_pos n) hcb_ball]
  have hdiff2 : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, P w - g w ≤ 0 := by
    refine nonpos_closedBall_of_shrinking_circleAverage (hP_cont.sub hg_cont)
      (fun ζ hζ => by rw [hP_sph ζ hζ, sub_self]) fun w hw => ?_
    obtain ⟨ρ, hρ_pos, hρ_lim, hρ_ca⟩ := hg_mvp w hw
    have hw_lt : ‖w‖ < 1 := by simpa [Metric.mem_ball] using hw
    refine ⟨ρ, hρ_pos, hρ_lim, ?_⟩
    filter_upwards [hρ_lim.eventually (gt_mem_nhds (sub_pos.mpr hw_lt))] with n hn
    have hcb_ball : Metric.closedBall w (ρ n) ⊆ Metric.ball (0 : ℂ) 1 := by
      intro z hz
      have hzw : ‖z - w‖ ≤ ρ n := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      have hzn : ‖z‖ < 1 := by
        calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
          _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
          _ < (1 - ‖w‖) + ‖w‖ := by linarith
          _ = 1 := sub_add_cancel 1 ‖w‖
      simpa [Metric.mem_ball] using hzn
    have hg_ci : CircleIntegrable g w (ρ n) :=
      (hg_cont.mono ((Metric.sphere_subset_closedBall.trans hcb_ball).trans
        Metric.ball_subset_closedBall)).circleIntegrable (hρ_pos n).le
    have hP_ci : CircleIntegrable P w (ρ n) :=
      (hP_cont.mono ((Metric.sphere_subset_closedBall.trans hcb_ball).trans
        Metric.ball_subset_closedBall)).circleIntegrable (hρ_pos n).le
    rw [Real.circleAverage_fun_sub hP_ci hg_ci, hρ_ca n, hP_ca (hρ_pos n) hcb_ball]
  have hg_eq_P : ∀ w ∈ Metric.ball (0 : ℂ) 1, g w = P w := by
    intro w hw
    have hw_cb := Metric.ball_subset_closedBall hw
    linarith [hdiff1 w hw_cb, hdiff2 w hw_cb]
  have hP_math : InnerProductSpace.HarmonicOnNhd P (Metric.ball 0 1) :=
    (harmonicOn_iff_harmonicOnNhd_real Metric.isOpen_ball).mp hP_harm
  have hg_math : InnerProductSpace.HarmonicOnNhd g (Metric.ball 0 1) := by
    intro w hw
    have hev : P =ᶠ[nhds w] g :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Metric.ball 0 1, Metric.isOpen_ball.mem_nhds hw, fun z hz => (hg_eq_P z hz).symm⟩
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).mp (hP_math w hw)
  obtain ⟨G, hG_ana, hG_re⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hg_math
  let L_aff : ℂ → ℂ := fun z => (z - a) / (R : ℂ)
  let F : ℂ → ℂ := fun z => G (L_aff z)
  have hR_c_ne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR_pos.ne'
  have hmap : ∀ z ∈ Metric.ball a R, L_aff z ∈ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    dsimp [L_aff]
    rw [Metric.mem_ball, dist_zero_right, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR_pos, div_lt_one hR_pos]
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hF_ana : AnalyticAt ℂ F a := by
    have hlin : AnalyticAt ℂ L_aff a :=
      ((analyticAt_id.sub analyticAt_const).mul analyticAt_const).congr
        (Filter.Eventually.of_forall fun z => (div_eq_mul_inv (z - a) (R : ℂ)).symm)
    exact (hG_ana (L_aff a) (hmap a (Metric.mem_ball_self hR_pos))).comp hlin
  have hev : (fun z => (F z).re) =ᶠ[nhds a] u := by
    filter_upwards [Metric.ball_mem_nhds a hR_pos] with z hz
    have hre_eq : (G (L_aff z)).re = g (L_aff z) := hG_re (hmap z hz)
    dsimp [F]
    rw [hre_eq]
    dsimp [g, L_aff]
    congr 1
    field_simp [hR_c_ne]
    ring
  exact (InnerProductSpace.harmonicAt_congr_nhds hev).mp hF_ana.harmonicAt_re

/-- 11.13 (Converse mean-value theorem, complex-valued): a continuous complex-valued function on an
open set `Ω ⊆ ℂ` having Rudin's shrinking-radii mean-value property (`HasMeanValueProperty u Ω`)
is weakly harmonic on `Ω` (`HarmonicOn u Ω`). -/
theorem theorem11_13 {u : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hu : HasMeanValueProperty u Ω) : HarmonicOn u Ω := by
  have h_clm : ∀ L : ℂ →L[ℝ] ℝ, HasMeanValueProperty (L ∘ u) Ω := by
    intro L
    refine ⟨L.continuous.comp_continuousOn hu.1, fun z hz => ?_⟩
    obtain ⟨r, hr_pos, hr_lim, hr_ca⟩ := hu.2 z hz
    obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hΩ z hz
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (hr_lim.eventually (gt_mem_nhds hR))
    refine ⟨fun n => r (n + N), fun n => hr_pos (n + N),
      hr_lim.comp (Filter.tendsto_add_atTop_nat N), fun n => ?_⟩
    have hrn_lt : r (n + N) < R := hN (n + N) (Nat.le_add_left N n)
    have hci : CircleIntegrable u z (r (n + N)) :=
      (hu.1.mono ((Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_ball hrn_lt)).trans
        hball)).circleIntegrable (hr_pos (n + N)).le
    rw [L.circleAverage_comp_comm hci, hr_ca (n + N)]
    rfl
  have hre : InnerProductSpace.HarmonicOnNhd (Complex.reCLM ∘ u) Ω :=
    (harmonicOn_iff_harmonicOnNhd_real hΩ).mp (theorem11_13_real hΩ (h_clm Complex.reCLM))
  have him : InnerProductSpace.HarmonicOnNhd (Complex.imCLM ∘ u) Ω :=
    (harmonicOn_iff_harmonicOnNhd_real hΩ).mp (theorem11_13_real hΩ (h_clm Complex.imCLM))
  rw [harmonicOn_iff_harmonicOnNhd_complex hΩ]
  intro z hz
  let L_I : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight Complex.I
  have hsum : InnerProductSpace.HarmonicAt
      (fun w => Complex.ofRealCLM ((u w).re) + L_I ((u w).im)) z :=
    ((hre z hz).comp_CLM Complex.ofRealCLM).add ((him z hz).comp_CLM L_I)
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hsum
  refine Filter.Eventually.of_forall fun w => ?_
  change ((u w).re : ℂ) + (u w).im • Complex.I = u w
  rw [Complex.real_smul, Complex.re_add_im]

private theorem hasDerivAt_conj_comp_conj {f : ℂ → ℂ} {f' z : ℂ}
    (hf : HasDerivAt f f' (starRingEnd ℂ z)) :
    HasDerivAt (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) (starRingEnd ℂ f') z := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hf ⊢
  rw [Asymptotics.isLittleO_iff] at hf ⊢
  intro c hc
  have h_ev := hf hc
  have hconj_cont : Filter.Tendsto (fun h : ℂ => starRingEnd ℂ h) (nhds 0) (nhds 0) := by
    simpa using Complex.continuous_conj.tendsto (0 : ℂ)
  filter_upwards [hconj_cont.eventually h_ev] with h hh
  have heq : starRingEnd ℂ (f (starRingEnd ℂ (z + h))) - starRingEnd ℂ (f (starRingEnd ℂ z)) -
        h • starRingEnd ℂ f' =
      starRingEnd ℂ (f (starRingEnd ℂ z + starRingEnd ℂ h) - f (starRingEnd ℂ z) -
        (starRingEnd ℂ h) • f') := by
    simp only [smul_eq_mul, map_add, map_sub, map_mul, RingHomCompTriple.comp_apply,
      RingHom.id_apply]
  rw [heq, Complex.norm_conj]
  simpa [Complex.norm_conj] using hh

private theorem holomorphic_im_zero_is_const {D : Set ℂ} (hD_open : IsOpen D)
    (hD_conn : IsPreconnected D) {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h D)
    (him : ∀ z ∈ D, (h z).im = 0) {z w : ℂ} (hz : z ∈ D) (hw : w ∈ D) :
    h z = h w := by
  refine hD_open.is_const_of_deriv_eq_zero hD_conn hh (fun a ha => ?_) hz hw
  obtain ⟨hdr, hcr⟩ := differentiableAt_complex_iff_differentiableAt_real.mp
    (hh.differentiableAt (hD_open.mem_nhds ha))
  rw [complexOfReal_deriv hdr hcr]
  have him_fderiv : HasFDerivAt (fun w : ℂ => (h w).im)
      (Complex.imCLM.comp (fderiv ℝ h a)) a :=
    Complex.imCLM.hasFDerivAt.comp a hdr.hasFDerivAt
  have him_zero : HasFDerivAt (fun w : ℂ => (h w).im) (0 : ℂ →L[ℝ] ℝ) a := by
    refine (hasFDerivAt_const (0 : ℝ) a).congr_of_eventuallyEq ?_
    filter_upwards [hD_open.mem_nhds ha] with w hw
    exact him w hw
  have hclm_eq : Complex.imCLM.comp (fderiv ℝ h a) = 0 := him_fderiv.unique him_zero
  have h1_im : (fderiv ℝ h a 1).im = 0 := by
    simpa using ContinuousLinearMap.ext_iff.mp hclm_eq 1
  have hI_im : (fderiv ℝ h a Complex.I).im = 0 := by
    simpa using ContinuousLinearMap.ext_iff.mp hclm_eq Complex.I
  rw [hcr] at hI_im
  have h1_re : (fderiv ℝ h a 1).re = 0 := by
    simpa [smul_eq_mul, Complex.mul_im] using hI_im
  exact Complex.ext h1_re h1_im

/-- Canonical Schwarz reflection extension across the real axis. -/
noncomputable def schwarzReflection (f : ℂ → ℂ) (Ω : Set ℂ) (z : ℂ) : ℂ :=
  if 0 < z.im then f z
  else if z.im < 0 then starRingEnd ℂ (f (starRingEnd ℂ z))
  else limUnder (nhdsWithin z {w ∈ Ω | 0 < w.im}) f

/-- 11.14 (Schwarz Reflection Principle): let `Ω ⊆ ℂ` be an open set symmetric across the real axis
(`∀ z ∈ Ω, starRingEnd ℂ z ∈ Ω`), with `Ω₊ = {z ∈ Ω | 0 < z.im}`, `L = {z ∈ Ω | z.im = 0}`, and
`Ω₋ = {z ∈ Ω | z.im < 0}`. Suppose `f : ℂ → ℂ` is holomorphic on `Ω₊` (`DifferentiableOn ℂ f Ω₊`)
and satisfies `lim_{z → x, z ∈ Ω₊} Im f(z) = 0` for every `x ∈ L` (without assuming `f` itself is
continuous up to `L`). Then `F = schwarzReflection f Ω` extends `f` holomorphically to all of `Ω`
(`DifferentiableOn ℂ F Ω`), satisfies `F z = f z` on `Ω₊`, `F z = conj (f (conj z))` on `Ω₋`,
`(F x).im = 0` on `L`, and `F (conj z) = conj (F z)` for all `z ∈ Ω`; moreover `F` is unique among
all holomorphic extensions on connected `Ω` (when `Ω₊.Nonempty`) and among all conjugate-symmetric
holomorphic extensions on arbitrary symmetric open `Ω`. -/
theorem theorem11_14 {Ω : Set ℂ} (hΩ_open : IsOpen Ω)
    (hΩ_symm : ∀ z ∈ Ω, starRingEnd ℂ z ∈ Ω) {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f {z ∈ Ω | 0 < z.im})
    (hf_im : ∀ x ∈ Ω, x.im = 0 →
      Filter.Tendsto (fun z => (f z).im) (nhdsWithin x {z ∈ Ω | 0 < z.im}) (nhds 0)) :
    let Ω_pos := {z ∈ Ω | 0 < z.im}
    let L := {z ∈ Ω | z.im = 0}
    let Ω_neg := {z ∈ Ω | z.im < 0}
    let F := schwarzReflection f Ω
    DifferentiableOn ℂ F Ω ∧
      (∀ z ∈ Ω_pos, F z = f z) ∧
      (∀ z ∈ Ω_neg, F z = starRingEnd ℂ (f (starRingEnd ℂ z))) ∧
      (∀ x ∈ L, (F x).im = 0) ∧
      (∀ z ∈ Ω, F (starRingEnd ℂ z) = starRingEnd ℂ (F z)) ∧
      (IsPreconnected Ω → Ω_pos.Nonempty →
        ∀ G : ℂ → ℂ, DifferentiableOn ℂ G Ω → (∀ z ∈ Ω_pos, G z = f z) →
          ∀ z ∈ Ω, G z = F z) := by
  intro Ω_pos L Ω_neg F
  have hΩ_pos_open : IsOpen Ω_pos :=
    hΩ_open.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hΩ_neg_open : IsOpen Ω_neg :=
    hΩ_open.inter (isOpen_lt Complex.continuous_im continuous_const)
  let V : ℂ → ℝ := fun z =>
    if 0 < z.im then (f z).im
    else if z.im < 0 then -(f (starRingEnd ℂ z)).im
    else 0
  have hV_odd : ∀ z, V (starRingEnd ℂ z) = -V z := by
    intro z
    simp only [V, Complex.conj_im, RingHomCompTriple.comp_apply, RingHom.id_apply]
    by_cases hpos : 0 < z.im
    · have h1 : ¬ 0 < -z.im := by linarith
      have h2 : -z.im < 0 := by linarith
      simp [hpos, h1, h2]
    · by_cases hneg : z.im < 0
      · have h1 : 0 < -z.im := by linarith
        simp [hpos, hneg, h1]
      · have hz0 : z.im = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
        simp [hz0]
  have hV_cont : ContinuousOn V Ω := by
    intro z₀ hz₀
    refine ContinuousAt.continuousWithinAt ?_
    by_cases hpos : 0 < z₀.im
    · have hz₀_pos : z₀ ∈ Ω_pos := ⟨hz₀, hpos⟩
      have hf_at : ContinuousAt (fun z => (f z).im) z₀ :=
        Complex.continuous_im.continuousAt.comp
          (hf_holo.continuousOn.continuousAt (hΩ_pos_open.mem_nhds hz₀_pos))
      refine hf_at.congr ?_
      filter_upwards [hΩ_pos_open.mem_nhds hz₀_pos] with z hz
      dsimp [V]
      simp [hz.2]
    · by_cases hneg : z₀.im < 0
      · have hz₀_neg : z₀ ∈ Ω_neg := ⟨hz₀, hneg⟩
        have hcz₀ : starRingEnd ℂ z₀ ∈ Ω_pos :=
          ⟨hΩ_symm z₀ hz₀, by rw [Complex.conj_im]; linarith⟩
        have hf_at : ContinuousAt (fun z => -(f (starRingEnd ℂ z)).im) z₀ :=
          ((Complex.continuous_im.continuousAt.comp
            (hf_holo.continuousOn.continuousAt (hΩ_pos_open.mem_nhds hcz₀))).comp
            Complex.continuous_conj.continuousAt).neg
        refine hf_at.congr ?_
        filter_upwards [hΩ_neg_open.mem_nhds hz₀_neg] with z hz
        dsimp [V]
        have hn : ¬ 0 < z.im := by linarith [hz.2]
        simp [hn, hz.2]
      · have hz₀_im : z₀.im = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
        have hz₀_conj : starRingEnd ℂ z₀ = z₀ := Complex.conj_eq_iff_im.mpr hz₀_im
        have hVz₀ : V z₀ = 0 := by dsimp [V]; simp [hz₀_im]
        rw [Metric.continuousAt_iff]
        intro ε hε
        obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ :=
          Metric.tendsto_nhdsWithin_nhds.mp (hf_im z₀ hz₀ hz₀_im) ε hε
        obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.isOpen_iff.mp hΩ_open z₀ hz₀
        refine ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun z hz_dist => ?_⟩
        rw [hVz₀, Real.dist_eq, sub_zero]
        have hzΩ : z ∈ Ω := hδ₂ (lt_of_lt_of_le hz_dist (min_le_right _ _))
        have hz_d1 : dist z z₀ < δ₁ := lt_of_lt_of_le hz_dist (min_le_left _ _)
        by_cases hz_p : 0 < z.im
        · dsimp [V]
          simp only [hz_p, ↓reduceIte]
          simpa [Real.dist_eq] using hδ₁ ⟨hzΩ, hz_p⟩ hz_d1
        · by_cases hz_n : z.im < 0
          · dsimp [V]
            simp only [hz_p, hz_n, ↓reduceIte, abs_neg]
            have hcz_pos : starRingEnd ℂ z ∈ Ω_pos :=
              ⟨hΩ_symm z hzΩ, by rw [Complex.conj_im]; linarith⟩
            have hcz_d1 : dist (starRingEnd ℂ z) z₀ < δ₁ := by
              rw [← hz₀_conj, dist_eq_norm, ← map_sub, Complex.norm_conj, ← dist_eq_norm]
              exact hz_d1
            simpa [Real.dist_eq] using hδ₁ hcz_pos hcz_d1
          · have hz0 : z.im = 0 := le_antisymm (not_lt.mp hz_p) (not_lt.mp hz_n)
            dsimp [V]
            simp [hz0, hε]
  have hf_neg_holo : DifferentiableOn ℂ (fun z => starRingEnd ℂ (f (starRingEnd ℂ z))) Ω_neg := by
    intro z hz
    have hcz : starRingEnd ℂ z ∈ Ω_pos := ⟨hΩ_symm z hz.1, by rw [Complex.conj_im]; linarith [hz.2]⟩
    have hdf := (hf_holo.differentiableAt (hΩ_pos_open.mem_nhds hcz)).hasDerivAt
    exact (hasDerivAt_conj_comp_conj hdf).differentiableAt.differentiableWithinAt
  have hV_mvp : HasMeanValueProperty V Ω := by
    refine ⟨hV_cont, fun z hz => ?_⟩
    by_cases hpos : 0 < z.im
    · have hz_pos : z ∈ Ω_pos := ⟨hz, hpos⟩
      have hharm_pos : HarmonicOn (Complex.imCLM ∘ f) Ω_pos :=
        (node11_4_holomorphic_harmonic hΩ_pos_open hf_holo).comp_clm hΩ_pos_open Complex.imCLM
      obtain ⟨r, hr_pos, hr_lim, hr_ca⟩ :=
        (theorem11_12_real hΩ_pos_open hharm_pos).2.2 z hz_pos
      obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hΩ_pos_open z hz_pos
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hr_lim.eventually (gt_mem_nhds hR))
      refine ⟨fun n => r (n + N), fun n => hr_pos (n + N),
        hr_lim.comp (Filter.tendsto_add_atTop_nat N), fun n => ?_⟩
      have hrn_lt : r (n + N) < R := hN (n + N) (Nat.le_add_left N n)
      have heq_sph : Set.EqOn V (Complex.imCLM ∘ f) (Metric.sphere z |r (n + N)|) := by
        intro ζ hζ
        rw [abs_of_pos (hr_pos (n + N))] at hζ
        have hζ_pos : ζ ∈ Ω_pos :=
          hball (Metric.closedBall_subset_ball hrn_lt (Metric.sphere_subset_closedBall hζ))
        dsimp [V]
        simp [hζ_pos.2]
      rw [Real.circleAverage_congr_sphere heq_sph, hr_ca (n + N)]
      dsimp [V]
      simp [hpos]
    · by_cases hneg : z.im < 0
      · have hz_neg : z ∈ Ω_neg := ⟨hz, hneg⟩
        have hharm_neg : HarmonicOn
            (Complex.imCLM ∘ fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) Ω_neg :=
          (node11_4_holomorphic_harmonic hΩ_neg_open hf_neg_holo).comp_clm hΩ_neg_open Complex.imCLM
        obtain ⟨r, hr_pos, hr_lim, hr_ca⟩ :=
          (theorem11_12_real hΩ_neg_open hharm_neg).2.2 z hz_neg
        obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hΩ_neg_open z hz_neg
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hr_lim.eventually (gt_mem_nhds hR))
        refine ⟨fun n => r (n + N), fun n => hr_pos (n + N),
          hr_lim.comp (Filter.tendsto_add_atTop_nat N), fun n => ?_⟩
        have hrn_lt : r (n + N) < R := hN (n + N) (Nat.le_add_left N n)
        have heq_sph : Set.EqOn V
            (Complex.imCLM ∘ fun w => starRingEnd ℂ (f (starRingEnd ℂ w)))
            (Metric.sphere z |r (n + N)|) := by
          intro ζ hζ
          rw [abs_of_pos (hr_pos (n + N))] at hζ
          have hζ_neg : ζ ∈ Ω_neg :=
            hball (Metric.closedBall_subset_ball hrn_lt (Metric.sphere_subset_closedBall hζ))
          have hn : ¬ 0 < ζ.im := by linarith [hζ_neg.2]
          dsimp [V]
          simp [hn, hζ_neg.2]
        rw [Real.circleAverage_congr_sphere heq_sph, hr_ca (n + N)]
        dsimp [V]
        simp [hpos, hneg]
      · have hz_im : z.im = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
        have hz_conj : starRingEnd ℂ z = z := Complex.conj_eq_iff_im.mpr hz_im
        obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hΩ_open z hz
        let r : ℕ → ℝ := fun n => R / ((n : ℝ) + 2)
        have hr_pos : ∀ n, 0 < r n := fun n => div_pos hR (by positivity)
        refine ⟨r, hr_pos,
          tendsto_const_nhds.div_atTop
            (Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds),
          fun n => ?_⟩
        have hVz : V z = 0 := by dsimp [V]; simp [hz_im]
        rw [hVz, Real.circleAverage_def, smul_eq_mul]
        have hint_neg : ∫ θ in (0 : ℝ)..(2 * Real.pi), V (circleMap z (r n) θ) =
            -(∫ θ in (0 : ℝ)..(2 * Real.pi), V (circleMap z (r n) θ)) := by
          have hrefl := intervalIntegral.integral_comp_sub_left
            (fun θ => V (circleMap z (r n) θ)) (2 * Real.pi) (a := 0) (b := 2 * Real.pi)
          rw [sub_self, sub_zero] at hrefl
          have hcm_conj : ∀ θ : ℝ, circleMap z (r n) (2 * Real.pi - θ) =
              starRingEnd ℂ (circleMap z (r n) θ) := by
            intro θ
            unfold circleMap
            rw [map_add, hz_conj, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
            congr 2
            rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
            have hsub : ((2 * Real.pi - θ : ℝ) : ℂ) * Complex.I =
                2 * (Real.pi : ℂ) * Complex.I + (θ : ℂ) * (-Complex.I) := by push_cast; ring
            rw [hsub, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]
          calc ∫ θ in (0 : ℝ)..(2 * Real.pi), V (circleMap z (r n) θ)
              = ∫ θ in (0 : ℝ)..(2 * Real.pi), V (circleMap z (r n) (2 * Real.pi - θ)) := hrefl.symm
            _ = ∫ θ in (0 : ℝ)..(2 * Real.pi), -V (circleMap z (r n) θ) := by
                  refine intervalIntegral.integral_congr fun θ _ => ?_
                  rw [hcm_conj, hV_odd]
            _ = -(∫ θ in (0 : ℝ)..(2 * Real.pi), V (circleMap z (r n) θ)) :=
                  intervalIntegral.integral_neg
        have hint_zero : ∫ θ in (0 : ℝ)..(2 * Real.pi), V (circleMap z (r n) θ) = 0 := by
          linarith
        rw [hint_zero, mul_zero]
  have hV_harm : HarmonicOn V Ω := theorem11_13_real hΩ_open hV_mvp
  have hdisc_ext : ∀ {x₀ : ℂ} {R : ℝ}, x₀ ∈ L → 0 < R → Metric.ball x₀ R ⊆ Ω →
      ∃ P : ℂ → ℂ, DifferentiableOn ℂ P (Metric.ball x₀ R) ∧
        (∀ z ∈ Metric.ball x₀ R, P (starRingEnd ℂ z) = starRingEnd ℂ (P z)) ∧
        (∀ z ∈ Metric.ball x₀ R, F z = P z) := by
    intro x₀ R hx₀L hR hball
    have hx₀_conj : starRingEnd ℂ x₀ = x₀ := Complex.conj_eq_iff_im.mpr hx₀L.2
    obtain ⟨G, hG_diff, hG_re⟩ := (theorem11_10 hR).2 (hV_harm.mono hball)
    let g₀ : ℂ → ℂ := fun z => Complex.I * G z
    have hg₀_diff : DifferentiableOn ℂ g₀ (Metric.ball x₀ R) := hG_diff.const_mul Complex.I
    have hg₀_im : ∀ z ∈ Metric.ball x₀ R, (g₀ z).im = V z := by
      intro z hz
      simp [g₀, Complex.mul_im, hG_re z hz]
    let z₁ : ℂ := x₀ + (((R / 2 : ℝ) : ℂ)) * Complex.I
    have hz₁_ball : z₁ ∈ Metric.ball x₀ R := by
      dsimp [z₁]
      rw [Metric.mem_ball, dist_self_add_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hR), Complex.norm_I, mul_one]
      linarith
    have hz₁_im : 0 < z₁.im := by
      dsimp [z₁]
      simp [hx₀L.2, half_pos hR]
    let c : ℝ := (f z₁ - g₀ z₁).re
    let P : ℂ → ℂ := fun z => g₀ z + (c : ℂ)
    have hP_diff : DifferentiableOn ℂ P (Metric.ball x₀ R) := hg₀_diff.add_const (c : ℂ)
    have hP_im : ∀ z ∈ Metric.ball x₀ R, (P z).im = V z := by
      intro z hz
      dsimp [P]
      simp [hg₀_im z hz]
    let D_pos : Set ℂ := {z ∈ Metric.ball x₀ R | 0 < z.im}
    have hD_pos_open : IsOpen D_pos :=
      Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
    have hD_pos_conv : Convex ℝ D_pos := by
      refine (convex_ball x₀ R).inter ?_
      intro z hz w hw a b ha hb hab
      change 0 < (a • z + b • w).im
      rw [Complex.add_im, Complex.real_smul, Complex.real_smul, Complex.mul_im, Complex.mul_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      rcases eq_or_lt_of_le ha with rfl | ha_pos
      · simp only [zero_add] at hab; subst hab
        nlinarith [ (show 0 < w.im from hw) ]
      · have : 0 ≤ b * w.im := mul_nonneg hb (le_of_lt hw)
        nlinarith [ (show 0 < z.im from hz) ]
    have hP_eq_f : ∀ z ∈ D_pos, P z = f z := by
      intro z hz
      have hconst := holomorphic_im_zero_is_const hD_pos_open hD_pos_conv.isPreconnected
        ((hf_holo.mono fun w hw => ⟨hball hw.1, hw.2⟩).sub (hP_diff.mono fun w hw => hw.1))
        (fun w hw => by
          change (f w - P w).im = 0
          rw [Complex.sub_im, hP_im w hw.1]
          dsimp [V]
          simp [hw.2])
        hz ⟨hz₁_ball, hz₁_im⟩
      have hz₁_zero : f z₁ - P z₁ = 0 := by
        refine Complex.ext ?_ ?_
        · dsimp [P, c]; simp
        · rw [Complex.sub_im, hP_im z₁ hz₁_ball]
          dsimp [V]; simp [hz₁_im]
      have hsub_z : f z - P z = 0 := hconst.trans hz₁_zero
      exact (sub_eq_zero.mp hsub_z).symm
    have hball_symm : ∀ z ∈ Metric.ball x₀ R, starRingEnd ℂ z ∈ Metric.ball x₀ R := by
      intro z hz
      rw [Metric.mem_ball, ← hx₀_conj, dist_eq_norm, ← map_sub, Complex.norm_conj, ← dist_eq_norm]
      exact hz
    let Q : ℂ → ℂ := fun z => starRingEnd ℂ (P (starRingEnd ℂ z))
    have hQ_diff : DifferentiableOn ℂ Q (Metric.ball x₀ R) := by
      intro z hz
      have hcz := hball_symm z hz
      exact (hasDerivAt_conj_comp_conj
        (hP_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hcz)).hasDerivAt).differentiableAt.differentiableWithinAt
    have hP_symm : ∀ z ∈ Metric.ball x₀ R, Q z = P z := by
      intro z hz
      have hconst := holomorphic_im_zero_is_const Metric.isOpen_ball (convex_ball x₀ R).isPreconnected
        (hQ_diff.sub hP_diff)
        (fun w hw => by
          change (Q w - P w).im = 0
          rw [Complex.sub_im]
          dsimp [Q]
          rw [hP_im (starRingEnd ℂ w) (hball_symm w hw),
            hP_im w hw, hV_odd]
          ring)
        hz (Metric.mem_ball_self hR)
      have hx₀_zero : Q x₀ - P x₀ = 0 := by
        dsimp [Q]
        rw [hx₀_conj]
        have hx₀_im0 : (P x₀).im = 0 := by
          rw [hP_im x₀ (Metric.mem_ball_self hR)]
          dsimp [V]; simp [hx₀L.2]
        rw [Complex.conj_eq_iff_im.mpr hx₀_im0, sub_self]
      have hsub_z : Q z - P z = 0 := hconst.trans hx₀_zero
      exact sub_eq_zero.mp hsub_z
    refine ⟨P, hP_diff, fun z hz => ?_, fun z hz => ?_⟩
    · have h := hP_symm (starRingEnd ℂ z) (hball_symm z hz)
      dsimp [Q] at h
      rw [RingHomCompTriple.comp_apply, RingHom.id_apply] at h
      exact h.symm
    · by_cases hpos : 0 < z.im
      · simp only [F, schwarzReflection, hpos, ↓reduceIte]
        exact (hP_eq_f z ⟨hz, hpos⟩).symm
      · by_cases hneg : z.im < 0
        · simp only [F, schwarzReflection, hpos, hneg, ↓reduceIte]
          have hcz_pos : starRingEnd ℂ z ∈ D_pos :=
            ⟨hball_symm z hz, by rw [Complex.conj_im]; linarith⟩
          rw [← hP_eq_f (starRingEnd ℂ z) hcz_pos]
          exact hP_symm z hz
        · have hz_im : z.im = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
          simp only [F, schwarzReflection, hpos, hneg, ↓reduceIte]
          have : (nhdsWithin z Ω_pos).NeBot := by
            refine Filter.neBot_iff.mpr fun hbot => ?_
            have hmem_empty : (∅ : Set ℂ) ∈ nhdsWithin z Ω_pos := by rw [hbot]; exact Filter.mem_bot
            obtain ⟨δ, hδ, hδ_empty⟩ := Metric.mem_nhdsWithin_iff.mp hmem_empty
            obtain ⟨δ', hδ', hδ'Ω⟩ := Metric.isOpen_iff.mp hΩ_open z (hball hz)
            let ε : ℝ := min (δ / 2) (δ' / 2)
            have hε : 0 < ε := lt_min (half_pos hδ) (half_pos hδ')
            let w : ℂ := z + (ε : ℂ) * Complex.I
            have hw_ball : w ∈ Metric.ball z δ := by
              dsimp [w]
              rw [Metric.mem_ball, dist_self_add_left, norm_mul, Complex.norm_real,
                Real.norm_eq_abs, abs_of_pos hε, Complex.norm_I, mul_one]
              exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
            have hwΩ : w ∈ Ω_pos := ⟨hδ'Ω (by
              dsimp [w]
              rw [Metric.mem_ball, dist_self_add_left, norm_mul, Complex.norm_real,
                Real.norm_eq_abs, abs_of_pos hε, Complex.norm_I, mul_one]
              exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ')), by
              dsimp [w]; simp [hz_im, hε]⟩
            exact hδ_empty ⟨hw_ball, hwΩ⟩
          have hP_tendsto : Filter.Tendsto f (nhdsWithin z Ω_pos) (nhds (P z)) := by
            have hP_at : Filter.Tendsto P (nhdsWithin z Ω_pos) (nhds (P z)) :=
              (hP_diff.continuousOn.continuousAt
                (Metric.isOpen_ball.mem_nhds hz)).tendsto.mono_left nhdsWithin_le_nhds
            refine hP_at.congr' ?_
            filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hz),
              self_mem_nhdsWithin] with w hw_ball hw_pos
            exact hP_eq_f w ⟨hw_ball, hw_pos.2⟩
          exact hP_tendsto.limUnder_eq
  have hF_pos : ∀ z ∈ Ω_pos, F z = f z := by
    intro z hz
    simp only [F, schwarzReflection, hz.2, ↓reduceIte]
  have hF_neg : ∀ z ∈ Ω_neg, F z = starRingEnd ℂ (f (starRingEnd ℂ z)) := by
    intro z hz
    have hn : ¬ 0 < z.im := by linarith [hz.2]
    simp only [F, schwarzReflection, hn, hz.2, ↓reduceIte]
  have hF_diff : DifferentiableOn ℂ F Ω := by
    intro z hz
    by_cases hpos : 0 < z.im
    · have hz_pos : z ∈ Ω_pos := ⟨hz, hpos⟩
      have hev : f =ᶠ[nhds z] F := by
        filter_upwards [hΩ_pos_open.mem_nhds hz_pos] with w hw
        exact (hF_pos w hw).symm
      exact ((hf_holo.differentiableAt (hΩ_pos_open.mem_nhds hz_pos)).congr_of_eventuallyEq
        hev.symm).differentiableWithinAt
    · by_cases hneg : z.im < 0
      · have hz_neg : z ∈ Ω_neg := ⟨hz, hneg⟩
        have hev : (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) =ᶠ[nhds z] F := by
          filter_upwards [hΩ_neg_open.mem_nhds hz_neg] with w hw
          exact (hF_neg w hw).symm
        exact ((hf_neg_holo.differentiableAt (hΩ_neg_open.mem_nhds hz_neg)).congr_of_eventuallyEq
          hev.symm).differentiableWithinAt
      · have hz_im : z.im = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
        obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hΩ_open z hz
        obtain ⟨P, hP_diff, _, hF_eq_P⟩ := hdisc_ext ⟨hz, hz_im⟩ hR hball
        have hev : F =ᶠ[nhds z] P := by
          filter_upwards [Metric.ball_mem_nhds z hR] with w hw
          exact hF_eq_P w hw
        exact ((hP_diff.differentiableAt (Metric.ball_mem_nhds z hR)).congr_of_eventuallyEq
          hev).differentiableWithinAt
  have hF_L_im : ∀ x ∈ L, (F x).im = 0 := by
    intro x hx
    obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hΩ_open x hx.1
    obtain ⟨P, _, hP_symm, hF_eq_P⟩ := hdisc_ext hx hR hball
    have hx_ball : x ∈ Metric.ball x R := Metric.mem_ball_self hR
    rw [hF_eq_P x hx_ball]
    have hx_conj : starRingEnd ℂ x = x := Complex.conj_eq_iff_im.mpr hx.2
    have hPs := hP_symm x hx_ball
    rw [hx_conj] at hPs
    exact Complex.conj_eq_iff_im.mp hPs.symm
  have hF_symm : ∀ z ∈ Ω, F (starRingEnd ℂ z) = starRingEnd ℂ (F z) := by
    intro z hz
    by_cases hpos : 0 < z.im
    · have hcz_neg : starRingEnd ℂ z ∈ Ω_neg :=
        ⟨hΩ_symm z hz, by rw [Complex.conj_im]; linarith⟩
      rw [hF_pos z ⟨hz, hpos⟩, hF_neg (starRingEnd ℂ z) hcz_neg,
        RingHomCompTriple.comp_apply, RingHom.id_apply]
    · by_cases hneg : z.im < 0
      · have hcz_pos : starRingEnd ℂ z ∈ Ω_pos :=
          ⟨hΩ_symm z hz, by rw [Complex.conj_im]; linarith⟩
        rw [hF_neg z ⟨hz, hneg⟩, hF_pos (starRingEnd ℂ z) hcz_pos,
          RingHomCompTriple.comp_apply, RingHom.id_apply]
      · have hz_im : z.im = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
        have hz_conj : starRingEnd ℂ z = z := Complex.conj_eq_iff_im.mpr hz_im
        rw [hz_conj]
        exact (Complex.conj_eq_iff_im.mpr (hF_L_im z ⟨hz, hz_im⟩)).symm
  refine ⟨hF_diff, hF_pos, hF_neg, hF_L_im, hF_symm, fun hconn ⟨z₀, hz₀⟩ G hG_diff hG_pos => ?_⟩
  have hG_ana : AnalyticOnNhd ℂ G Ω := hG_diff.analyticOnNhd hΩ_open
  have hF_ana : AnalyticOnNhd ℂ F Ω := hF_diff.analyticOnNhd hΩ_open
  have hev : G =ᶠ[nhds z₀] F := by
    filter_upwards [hΩ_pos_open.mem_nhds hz₀] with w hw
    rw [hG_pos w hw, hF_pos w hw]
  exact fun z hz => hG_ana.eqOn_of_preconnected_of_eventuallyEq hF_ana hconn hz₀.1 hev hz

end Nodes11_11_to_11_14

section Nodes11_27_to_11_29_and_11_31

/-- 11.27 (Definition, Fidelity Constraint #3): Rudin's global `ε`–`δ` equicontinuity of a family
of functions `F : ι → β → α` corresponds to Mathlib's `UniformEquicontinuous` (not merely
pointwise `Equicontinuous`). -/
abbrev BookEquicontinuous {ι β α : Type*} [UniformSpace β] [UniformSpace α]
    (F : ι → β → α) : Prop :=
  UniformEquicontinuous F

/-- 11.27 (Relative definition): uniform equicontinuity of a family `F` on a subset `S`. -/
abbrev BookEquicontinuousOn {ι β α : Type*} [UniformSpace β] [UniformSpace α]
    (F : ι → β → α) (S : Set β) : Prop :=
  UniformEquicontinuousOn F S

/-- 11.27 (Definition): pointwise boundedness of a family `F : ι → X → E`: for every `x : X`,
the set `{F i x | i : ι}` is norm-bounded (`∃ M < ∞, ∀ i, ‖F i x‖ ≤ M`). -/
def PointwiseBounded {ι X E : Type*} [SeminormedAddCommGroup E] (F : ι → X → E) : Prop :=
  ∀ x : X, Bornology.IsBounded (Set.range fun i => F i x)

/-- 11.27 (Relative definition): pointwise boundedness of `F` on a subset `S ⊆ X`. -/
def PointwiseBoundedOn {ι X E : Type*} [SeminormedAddCommGroup E]
    (F : ι → X → E) (S : Set X) : Prop :=
  ∀ x ∈ S, Bornology.IsBounded (Set.range fun i => F i x)

/-- 11.27: exact metric `ε`–`δ` characterization of `BookEquicontinuous` (`UniformEquicontinuous`)
and norm characterization of `PointwiseBounded`, plus the implication to pointwise
`Equicontinuous`. -/
theorem theorem11_27 {ι X E : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup E]
    (F : ι → X → E) :
    (BookEquicontinuous F ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → ∀ i : ι, dist (F i x) (F i y) < ε) ∧
    (PointwiseBounded F ↔ ∀ x : X, ∃ M : ℝ, ∀ i : ι, ‖F i x‖ ≤ M) ∧
    (BookEquicontinuous F → Equicontinuous F) := by
  refine ⟨Metric.uniformEquicontinuous_iff, ?_, fun h => h.equicontinuous⟩
  constructor
  · intro h x
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp (h x)
    exact ⟨M, fun i => hM _ ⟨i, rfl⟩⟩
  · intro h x
    obtain ⟨M, hM⟩ := h x
    refine isBounded_iff_forall_norm_le.mpr ⟨M, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hM i

/-- 11.28 (Arzelà–Ascoli theorem, general proper normed target): every pointwise bounded,
equicontinuous (`BookEquicontinuous`) sequence `f : ℕ → X → E` on a separable (pseudo)metric space
`X` into a proper seminormed space `E` has a strictly increasing subsequence `φ : ℕ → ℕ` and a
uniformly continuous limit `g : X → E` such that `f (φ k) x → g x` at every `x : X` and
`f (φ k) → g` uniformly on every compact subset `K ⊆ X`. -/
theorem theorem11_28_general {X E : Type*} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [SeminormedAddCommGroup E] [ProperSpace E]
    {f : ℕ → X → E} (hf_bdd : PointwiseBounded f) (hf_equi : BookEquicontinuous f) :
    ∃ (φ : ℕ → ℕ) (g : X → E), StrictMono φ ∧ Continuous g ∧ UniformContinuous g ∧
      (∀ x : X, Filter.Tendsto (fun k => f (φ k) x) Filter.atTop (nhds (g x))) ∧
      (∀ K : Set X, IsCompact K →
        TendstoUniformlyOn (fun k => f (φ k)) g Filter.atTop K) := by
  rcases isEmpty_or_nonempty X with hX_emp | hX_ne
  · have huc_emp : UniformContinuous (isEmptyElim : X → E) :=
      Metric.uniformContinuous_iff.mpr fun _ _ => ⟨1, zero_lt_one, fun x => isEmptyElim x⟩
    refine ⟨id, isEmptyElim, strictMono_id, huc_emp.continuous, huc_emp,
      fun x => isEmptyElim x, fun K _ => ?_⟩
    rw [Metric.tendstoUniformlyOn_iff]
    exact fun _ _ => Filter.Eventually.of_forall fun _ x _ => isEmptyElim x
  obtain ⟨D, hD_count, hD_dense⟩ := TopologicalSpace.exists_countable_dense X
  have hD_ne : D.Nonempty := hD_dense.nonempty
  obtain ⟨d, rfl⟩ := hD_count.exists_eq_range hD_ne
  have hex_M : ∀ m : ℕ, ∃ M : ℝ, ∀ n : ℕ, f n (d m) ∈ Metric.closedBall (0 : E) M := by
    intro m
    obtain ⟨M, hM⟩ := (theorem11_27 f).2.1.mp hf_bdd (d m)
    exact ⟨M, fun n => by simpa [Metric.mem_closedBall, dist_zero_right] using hM n⟩
  choose M hM using hex_M
  let PiD := ∀ m : ℕ, Metric.closedBall (0 : E) (M m)
  have : ∀ m : ℕ, CompactSpace (Metric.closedBall (0 : E) (M m)) :=
    fun m => isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) (M m))
  let seq : ℕ → PiD := fun n m => ⟨f n (d m), hM m n⟩
  obtain ⟨y, _, φ, hφ_mono, hφ_lim⟩ :=
    isCompact_univ.isSeqCompact (fun n => Set.mem_univ (seq n))
  have hd_lim : ∀ m : ℕ,
      Filter.Tendsto (fun k => f (φ k) (d m)) Filter.atTop (nhds (y m).1) := by
    intro m
    have hm := (tendsto_pi_nhds.mp hφ_lim) m
    exact continuous_subtype_val.tendsto (y m) |>.comp hm
  have hcauchy : ∀ x : X, CauchySeq (fun k => f (φ k) x) := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformEquicontinuous_iff.mp hf_equi (ε / 3) (by positivity)
    obtain ⟨_, hxm, ⟨m, rfl⟩⟩ := Metric.dense_iff.mp hD_dense x δ hδ_pos
    have hdm_cauchy := Metric.cauchySeq_iff.mp (hd_lim m).cauchySeq (ε / 3) (by positivity)
    obtain ⟨N, hN⟩ := hdm_cauchy
    refine ⟨N, fun j hj k hk => ?_⟩
    have h1 : dist (f (φ j) x) (f (φ j) (d m)) < ε / 3 := by
      have hdx : dist x (d m) < δ := by rwa [Metric.mem_ball, dist_comm] at hxm
      exact hδ x (d m) hdx (φ j)
    have h2 : dist (f (φ j) (d m)) (f (φ k) (d m)) < ε / 3 := hN j hj k hk
    have h3 : dist (f (φ k) (d m)) (f (φ k) x) < ε / 3 := by
      have hdx : dist (d m) x < δ := by rwa [Metric.mem_ball] at hxm
      exact hδ (d m) x hdx (φ k)
    calc dist (f (φ j) x) (f (φ k) x)
        ≤ dist (f (φ j) x) (f (φ j) (d m)) + dist (f (φ j) (d m)) (f (φ k) (d m)) +
            dist (f (φ k) (d m)) (f (φ k) x) := dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add h1 h2) h3
      _ = ε := by ring
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  have hsub_equi : UniformEquicontinuous (fun k => f (φ k)) := by
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformEquicontinuous_iff.mp hf_equi ε hε
    exact ⟨δ, hδ_pos, fun x z hxz k => hδ x z hxz (φ k)⟩
  have hg_uc : UniformContinuous g :=
    (tendsto_pi_nhds.mpr hg).uniformContinuous_of_uniformEquicontinuous hsub_equi
  refine ⟨φ, g, hφ_mono, hg_uc.continuous, hg_uc, hg, fun K hK => ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ :=
    Metric.uniformEquicontinuous_iff.mp hsub_equi (ε / 3) (by positivity)
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.uniformContinuous_iff.mp hg_uc (ε / 3) (by positivity)
  let δ : ℝ := min δ₁ δ₂
  have hδ_pos : 0 < δ := lt_min hδ₁_pos hδ₂_pos
  obtain ⟨F, hF_cov⟩ := hK.elim_finite_subcover
    (fun z : K => Metric.ball z.1 δ)
    (fun _ => Metric.isOpen_ball)
    (fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self hδ_pos⟩)
  choose N_fn hN_fn using fun z : K =>
    Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp (hg z.1) (ε / 3) (by positivity))
  have hF_ev : ∀ᶠ k in Filter.atTop, ∀ z ∈ F, dist (f (φ k) z.1) (g z.1) < ε / 3 :=
    Filter.eventually_atTop.mpr
      ⟨F.sup N_fn, fun k hk z hzF => hN_fn z k (le_trans (Finset.le_sup hzF) hk)⟩
  filter_upwards [hF_ev] with k hk x hx
  obtain ⟨z, hzF, hxz⟩ := Set.mem_iUnion₂.mp (hF_cov hx)
  have hxz_lt : dist x z.1 < δ := by simpa [Metric.mem_ball] using hxz
  have h1 : dist (g x) (g z.1) < ε / 3 := hδ₂ (lt_of_lt_of_le hxz_lt (min_le_right _ _))
  have h2 : dist (g z.1) (f (φ k) z.1) < ε / 3 := by
    rw [dist_comm]
    exact hk z hzF
  have h3 : dist (f (φ k) z.1) (f (φ k) x) < ε / 3 := by
    have hzx : dist z.1 x < δ₁ := by
      rw [dist_comm]
      exact lt_of_lt_of_le hxz_lt (min_le_left _ _)
    exact hδ₁ z.1 x hzx k
  calc dist (g x) (f (φ k) x)
      ≤ dist (g x) (g z.1) + dist (g z.1) (f (φ k) z.1) +
          dist (f (φ k) z.1) (f (φ k) x) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add h1 h2) h3
    _ = ε := by ring

/-- 11.28 (Arzelà–Ascoli theorem for complex-valued functions, as stated on pp. 245–246). -/
theorem theorem11_28 {X : Type*} [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X]
    {f : ℕ → X → ℂ} (hf_bdd : PointwiseBounded f) (hf_equi : BookEquicontinuous f) :
    ∃ (φ : ℕ → ℕ) (g : X → ℂ), StrictMono φ ∧ Continuous g ∧ UniformContinuous g ∧
      (∀ x : X, Filter.Tendsto (fun k => f (φ k) x) Filter.atTop (nhds (g x))) ∧
      (∀ K : Set X, IsCompact K →
        TendstoUniformlyOn (fun k => f (φ k)) g Filter.atTop K) :=
  theorem11_28_general hf_bdd hf_equi

/-- 11.29 (Sequential Banach–Alaoglu theorem): every norm-bounded sequence `Λ : ℕ → StrongDual 𝕜 E`
of continuous linear functionals on a separable normed space `E` over a proper nontrivially normed
field `𝕜` (such as `ℂ` or `ℝ`) contains a strictly increasing subsequence `φ : ℕ → ℕ` converging
pointwise on `E` to a continuous linear functional `Λ_lim : StrongDual 𝕜 E` satisfying
`‖Λ_lim‖ ≤ liminf_{k → ∞} ‖Λ (φ k)‖ ≤ M`. -/
theorem theorem11_29_general {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] [TopologicalSpace.SeparableSpace E] {Λ : ℕ → StrongDual 𝕜 E} {M : ℝ}
    (hM : ∀ n, ‖Λ n‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (Λ_lim : StrongDual 𝕜 E), StrictMono φ ∧
      (∀ x : E, Filter.Tendsto (fun k => Λ (φ k) x) Filter.atTop (nhds (Λ_lim x))) ∧
      ‖Λ_lim‖ ≤ Filter.liminf (fun k => ‖Λ (φ k)‖) Filter.atTop ∧
      ‖Λ_lim‖ ≤ M := by
  let seq : ℕ → WeakDual 𝕜 E := fun n => (Λ n).toWeakDual
  have hmem : ∀ n, seq n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) M := by
    intro n
    simp [seq, Metric.mem_closedBall, dist_zero_right, hM n]
  obtain ⟨w, hw_mem, φ, hφ_mono, hφ_lim⟩ :=
    (WeakDual.isSeqCompact_closedBall 𝕜 E (0 : StrongDual 𝕜 E) M) hmem
  let Λ_lim : StrongDual 𝕜 E := w.toStrongDual
  have hΛ_M : ‖Λ_lim‖ ≤ M := by
    simpa [Λ_lim, Metric.mem_closedBall, dist_zero_right] using hw_mem
  have hpt : ∀ x : E, Filter.Tendsto (fun k => Λ (φ k) x) Filter.atTop (nhds (Λ_lim x)) := by
    intro x
    exact (WeakDual.eval_continuous x).tendsto w |>.comp hφ_lim
  let S_inf : Set ℝ := {a : ℝ | ∀ᶠ k in Filter.atTop, a ≤ ‖Λ (φ k)‖}
  have hS_bdd : BddAbove S_inf := by
    refine ⟨M, fun a ha => ?_⟩
    obtain ⟨k, hk⟩ := ha.exists
    exact hk.trans (hM (φ k))
  have h0_mem : (0 : ℝ) ∈ S_inf := Filter.Eventually.of_forall fun k => norm_nonneg _
  have hL_nn : 0 ≤ Filter.liminf (fun k => ‖Λ (φ k)‖) Filter.atTop := by
    rw [Filter.liminf_eq]
    exact le_csSup hS_bdd h0_mem
  have hΛ_liminf : ‖Λ_lim‖ ≤ Filter.liminf (fun k => ‖Λ (φ k)‖) Filter.atTop := by
    refine ContinuousLinearMap.opNorm_le_bound Λ_lim hL_nn fun x => ?_
    by_cases hx0 : ‖x‖ = 0
    · have hnorm_lim : Filter.Tendsto (fun k => ‖Λ (φ k) x‖) Filter.atTop (nhds ‖Λ_lim x‖) :=
        (hpt x).norm
      have hzero_ev : ∀ k, ‖Λ (φ k) x‖ ≤ 0 := fun k => by
        have hle := (Λ (φ k)).le_opNorm x
        rw [hx0, mul_zero] at hle
        exact hle
      have hΛx_le0 : ‖Λ_lim x‖ ≤ 0 :=
        le_of_tendsto hnorm_lim (Filter.Eventually.of_forall hzero_ev)
      rw [hx0, mul_zero]
      exact hΛx_le0
    · have hx_pos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
      rw [← div_le_iff₀ hx_pos]
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hsub_le : ‖Λ_lim x‖ / ‖x‖ - ε ≤ Filter.liminf (fun k => ‖Λ (φ k)‖) Filter.atTop := by
        rw [Filter.liminf_eq]
        refine le_csSup hS_bdd ?_
        have hnorm_lim : Filter.Tendsto (fun k => ‖Λ (φ k) x‖ / ‖x‖) Filter.atTop
            (nhds (‖Λ_lim x‖ / ‖x‖)) :=
          (hpt x).norm.div_const ‖x‖
        have hev := hnorm_lim.eventually (lt_mem_nhds (sub_lt_self (‖Λ_lim x‖ / ‖x‖) hε))
        filter_upwards [hev] with k hk
        have hdiv_le : ‖Λ (φ k) x‖ / ‖x‖ ≤ ‖Λ (φ k)‖ :=
          (div_le_iff₀ hx_pos).mpr ((Λ (φ k)).le_opNorm x)
        exact hk.le.trans hdiv_le
      linarith
  exact ⟨φ, Λ_lim, hφ_mono, hpt, hΛ_liminf, hΛ_M⟩

/-- 11.29 (Complex specialization, as printed on pp. 246–247). -/
theorem theorem11_29 {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace.SeparableSpace E] {Λ : ℕ → StrongDual ℂ E} {M : ℝ}
    (hM : ∀ n, ‖Λ n‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (Λ_lim : StrongDual ℂ E), StrictMono φ ∧
      (∀ x : E, Filter.Tendsto (fun k => Λ (φ k) x) Filter.atTop (nhds (Λ_lim x))) ∧
      ‖Λ_lim‖ ≤ Filter.liminf (fun k => ‖Λ (φ k)‖) Filter.atTop ∧
      ‖Λ_lim‖ ≤ M :=
  theorem11_29_general hM

open scoped Classical in
/-- Extension by zero outside `Ω` of a bounded continuous function on `Ω`. -/
noncomputable def extendZero {Ω : Set ℂ} (f : BoundedContinuousFunction Ω ℂ) (z : ℂ) : ℂ :=
  if hz : z ∈ Ω then f ⟨z, hz⟩ else 0

@[simp]
theorem extendZero_apply_of_mem {Ω : Set ℂ} (f : BoundedContinuousFunction Ω ℂ)
    {z : ℂ} (hz : z ∈ Ω) : extendZero f z = f ⟨z, hz⟩ := by
  simp [extendZero, hz]

/-- 11.31 (Definition): the commutative algebra `H^∞(Ω)` of bounded holomorphic functions on an
open set `Ω ⊆ ℂ`, realized as a `Subalgebra ℂ (BoundedContinuousFunction Ω ℂ)` equipped with the
supremum norm `‖f‖_∞ = sup_{z ∈ Ω} ‖f z‖`. -/
noncomputable def HInftySubalgebra (Ω : Set ℂ) :
    Subalgebra ℂ (BoundedContinuousFunction Ω ℂ) where
  carrier := {f | DifferentiableOn ℂ (extendZero f) Ω}
  mul_mem' {f g} hf hg := by
    refine (hf.mul hg).congr fun z hz => ?_
    simp [hz]
  one_mem' := by
    refine (differentiableOn_const (1 : ℂ)).congr fun z hz => ?_
    simp [hz]
  add_mem' {f g} hf hg := by
    refine (hf.add hg).congr fun z hz => ?_
    simp [hz]
  zero_mem' := by
    refine (differentiableOn_const (0 : ℂ)).congr fun z hz => ?_
    simp [hz]
  algebraMap_mem' c := by
    refine (differentiableOn_const c).congr fun z hz => ?_
    simp [hz]

/-- 11.31: `H^∞ = H^∞(U)` on the open unit disc `U = Metric.ball 0 1`. -/
noncomputable abbrev HInfty : Subalgebra ℂ (BoundedContinuousFunction (Metric.ball (0 : ℂ) 1) ℂ) :=
  HInftySubalgebra (Metric.ball (0 : ℂ) 1)

/-- `H^∞(Ω)` is a closed subset of `BoundedContinuousFunction Ω ℂ` under the supremum norm. -/
theorem isClosed_HInftySubalgebra {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    IsClosed (HInftySubalgebra Ω : Set (BoundedContinuousFunction Ω ℂ)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro seq f hseq_mem hseq_lim
  have hunif : TendstoUniformlyOn (fun n => extendZero (seq n)) (extendZero f) Filter.atTop Ω := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hseq_lim ε hε] with n hn z hz
    rw [extendZero_apply_of_mem _ hz, extendZero_apply_of_mem _ hz, dist_comm]
    exact lt_of_le_of_lt (BoundedContinuousFunction.dist_coe_le_dist (⟨z, hz⟩ : Ω)) hn
  exact hunif.tendstoLocallyUniformlyOn.differentiableOn
    (Filter.Eventually.of_forall hseq_mem) hΩ

/-- `H^∞(Ω)` is a complete space (Banach space / commutative Banach algebra) under the supremum
norm. -/
theorem completeSpace_HInftySubalgebra {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    CompleteSpace (HInftySubalgebra Ω) :=
  (isClosed_HInftySubalgebra hΩ).completeSpace_coe

instance : CompleteSpace HInfty :=
  completeSpace_HInftySubalgebra Metric.isOpen_ball

/-- 11.31 (`H^∞(Ω)` Banach space & characterization):
(a) `H^∞(Ω)` is a closed subalgebra of `BoundedContinuousFunction Ω ℂ`, hence a Banach space
    (`CompleteSpace (HInftySubalgebra Ω)`) under the supremum norm;
(b) Every bounded holomorphic function `g : ℂ → ℂ` on `Ω` (`DifferentiableOn ℂ g Ω` and
    `∀ z ∈ Ω, ‖g z‖ ≤ C`) defines a unique element `F : HInftySubalgebra Ω` with
    `∀ z : Ω, (F : BoundedContinuousFunction Ω ℂ) z = g z.1` and `‖F‖ ≤ max 0 C`. -/
theorem theorem11_31 {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    IsClosed (HInftySubalgebra Ω : Set (BoundedContinuousFunction Ω ℂ)) ∧
    CompleteSpace (HInftySubalgebra Ω) ∧
    (∀ {g : ℂ → ℂ} {C : ℝ}, DifferentiableOn ℂ g Ω → (∀ z ∈ Ω, ‖g z‖ ≤ C) →
      ∃! F : HInftySubalgebra Ω,
        ∀ z : Ω, (F : BoundedContinuousFunction Ω ℂ) z = g z.1) := by
  refine ⟨isClosed_HInftySubalgebra hΩ, completeSpace_HInftySubalgebra hΩ,
    fun {g} {C} hg_holo hg_bdd => ?_⟩
  let bcf : BoundedContinuousFunction Ω ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun z : Ω => g z.1)
      (continuousOn_iff_continuous_domRestrict.mp hg_holo.continuousOn)
      (max 0 C)
      (fun z => (hg_bdd z.1 z.2).trans (le_max_right 0 C))
  have hbcf_mem : bcf ∈ HInftySubalgebra Ω := by
    refine hg_holo.congr fun z hz => ?_
    rw [extendZero_apply_of_mem _ hz]
    rfl
  refine ⟨⟨bcf, hbcf_mem⟩, fun z => rfl, ?_⟩
  intro F hF
  ext z
  exact hF z

end Nodes11_27_to_11_29_and_11_31

end RudinRCA.Chapter11
