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
import RudinRCA.Chapter04
import RudinRCA.Chapter06
import RudinRCA.Chapter08
import RudinRCA.Chapter10

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

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate

namespace RudinRCA.Chapter11

/-! ### Stage 3 Block 1: Normalized Unit Circle, Literal 3.7 `L^∞` Bridge, and Nodes 11.16–11.17 -/

section UnitCircleFoundations

/-- The geometric unit circle `T = {z ∈ ℂ : ‖z‖ = 1}` (boundary of `U = Metric.ball 0 1`). -/
abbrev UnitCircle : Type := Metric.sphere (0 : ℂ) 1

/-- Homeomorphism between `Chapter04.FourierCircle = AddCircle (2π)` and `UnitCircle = sphere 0 1`
given by `t ↦ exp(i t)`. -/
def fourierToUnitCircle : RudinRCA.Chapter04.FourierCircle ≃ₜ UnitCircle :=
  RudinRCA.Chapter04.fourierCircleHomeomorphism.trans
    { toFun := fun u => ⟨(u : ℂ), u.2⟩
      invFun := fun z => ⟨z.1, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }

@[simp]
theorem fourierToUnitCircle_coe_apply (t : ℝ) :
    (fourierToUnitCircle (t : RudinRCA.Chapter04.FourierCircle) : ℂ) =
      Complex.exp ((t : ℂ) * Complex.I) :=
  RudinRCA.Chapter04.fourierCircleHomeomorphism_apply t

@[simp]
theorem norm_unitCircle (ζ : UnitCircle) : ‖(ζ : ℂ)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using ζ.2

theorem unitCircle_mul_conj (ζ : UnitCircle) : (ζ : ℂ) * conj (ζ : ℂ) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_unitCircle, one_pow, Complex.ofReal_one]

theorem measurableEmbedding_fourierToUnitCircle :
    MeasurableEmbedding fourierToUnitCircle :=
  fourierToUnitCircle.isClosedEmbedding.measurableEmbedding

/-- Normalized Lebesgue/Haar probability measure `σ = m / (2π)` on `T = UnitCircle`
(Rudin 11.19, p. 241: a rotation-invariant positive Borel measure on `T` with `σ(T) = 1`). -/
def unitCircleMeasure : Measure UnitCircle :=
  Measure.map fourierToUnitCircle RudinRCA.Chapter04.circleMeasure

instance : IsProbabilityMeasure unitCircleMeasure :=
  ⟨by rw [unitCircleMeasure,
        Measure.map_apply fourierToUnitCircle.continuous.measurable MeasurableSet.univ,
        Set.preimage_univ, measure_univ]⟩

theorem unitCircleMeasure_univ : unitCircleMeasure Set.univ = 1 :=
  measure_univ

theorem unitCircleMeasure_real_univ : unitCircleMeasure.real Set.univ = 1 := by
  simp [Measure.real]

theorem unitCircleMeasure_univ_ne_zero : unitCircleMeasure Set.univ ≠ 0 := by
  simp

/-- Rotation homeomorphism `η ↦ ζ₀ · η` on `UnitCircle`. -/
def unitCircleRotate (ζ₀ : UnitCircle) : UnitCircle ≃ₜ UnitCircle where
  toFun η := ⟨(ζ₀ : ℂ) * (η : ℂ), by
    rw [Metric.mem_sphere, dist_zero_right, norm_mul, norm_unitCircle, norm_unitCircle, mul_one]⟩
  invFun η := ⟨conj (ζ₀ : ℂ) * (η : ℂ), by
    rw [Metric.mem_sphere, dist_zero_right, norm_mul, RCLike.norm_conj,
      norm_unitCircle, norm_unitCircle, mul_one]⟩
  left_inv η := Subtype.ext <| by
    dsimp
    rw [← mul_assoc, mul_comm (conj (ζ₀ : ℂ)), unitCircle_mul_conj, one_mul]
  right_inv η := Subtype.ext <| by
    dsimp
    rw [← mul_assoc, unitCircle_mul_conj, one_mul]
  continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_const.mul continuous_subtype_val).subtype_mk _

@[simp]
theorem unitCircleRotate_coe (ζ₀ η : UnitCircle) :
    ((unitCircleRotate ζ₀ η : UnitCircle) : ℂ) = (ζ₀ : ℂ) * (η : ℂ) :=
  rfl

theorem fourierToUnitCircle_add (a b : RudinRCA.Chapter04.FourierCircle) :
    fourierToUnitCircle (a + b) =
      unitCircleRotate (fourierToUnitCircle a) (fourierToUnitCircle b) := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective b
  apply Subtype.ext
  rw [← QuotientAddGroup.mk_add, fourierToUnitCircle_coe_apply, unitCircleRotate_coe,
    fourierToUnitCircle_coe_apply, fourierToUnitCircle_coe_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Rotation invariance of `σ = unitCircleMeasure` on `T`: `σ(ζ₀ · E) = σ(E)` (Rudin 11.19, p. 241). -/
theorem measurePreserving_unitCircleRotate (ζ₀ : UnitCircle) :
    MeasurePreserving (unitCircleRotate ζ₀) unitCircleMeasure unitCircleMeasure := by
  let a := fourierToUnitCircle.symm ζ₀
  have hcomp : unitCircleRotate ζ₀ ∘ fourierToUnitCircle =
      fourierToUnitCircle ∘ (fun b => a + b) := by
    ext b
    simp [a, fourierToUnitCircle_add]
  refine ⟨(unitCircleRotate ζ₀).continuous.measurable, ?_⟩
  unfold unitCircleMeasure
  rw [Measure.map_map (unitCircleRotate ζ₀).continuous.measurable
      fourierToUnitCircle.continuous.measurable,
    hcomp,
    ← Measure.map_map fourierToUnitCircle.continuous.measurable (measurable_const_add a),
    (measurePreserving_add_left RudinRCA.Chapter04.circleMeasure a).map_eq]

theorem lintegral_unitCircleMeasure_eq_circleMeasure (g : UnitCircle → ℝ≥0∞) :
    (∫⁻ ζ, g ζ ∂unitCircleMeasure) =
      ∫⁻ x, g (fourierToUnitCircle x) ∂RudinRCA.Chapter04.circleMeasure :=
  measurableEmbedding_fourierToUnitCircle.lintegral_map g

theorem integral_unitCircleMeasure_eq_circleMeasure {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : UnitCircle → E) :
    (∫ ζ, g ζ ∂unitCircleMeasure) =
      ∫ x, g (fourierToUnitCircle x) ∂RudinRCA.Chapter04.circleMeasure :=
  measurableEmbedding_fourierToUnitCircle.integral_map g

theorem exp_mem_unitCircle (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) ∈ Metric.sphere (0 : ℂ) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, Complex.norm_exp_ofReal_mul_I]

/-- Angular interval-integral representation `(2π)⁻¹ ∫_{-π}^π g(e^{it}) dt` (and over `[0, 2π]`)
for `unitCircleMeasure`. -/
theorem integral_unitCircleMeasure_eq_interval {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : UnitCircle → E) :
    (∫ ζ, g ζ ∂unitCircleMeasure) =
      (2 * Real.pi)⁻¹ • ∫ t in (-Real.pi)..Real.pi,
        g ⟨Complex.exp ((t : ℂ) * Complex.I), exp_mem_unitCircle t⟩ ∧
    (∫ ζ, g ζ ∂unitCircleMeasure) =
      (2 * Real.pi)⁻¹ • ∫ t in (0 : ℝ)..(2 * Real.pi),
        g ⟨Complex.exp ((t : ℂ) * Complex.I), exp_mem_unitCircle t⟩ := by
  have h1 : (∫ ζ, g ζ ∂unitCircleMeasure) =
      (2 * Real.pi)⁻¹ • ∫ t in (-Real.pi)..Real.pi,
        g ⟨Complex.exp ((t : ℂ) * Complex.I), exp_mem_unitCircle t⟩ := by
    rw [integral_unitCircleMeasure_eq_circleMeasure, RudinRCA.Chapter04.circleIntegral_interval,
      one_div]
    rfl
  have hper : Function.Periodic
      (fun t : ℝ => g ⟨Complex.exp ((t : ℂ) * Complex.I), exp_mem_unitCircle t⟩)
      (2 * Real.pi) := by
    intro t
    dsimp only
    congr 1
    apply Subtype.ext
    dsimp only
    have : ((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
        (t : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hshift := hper.intervalIntegral_add_eq (-Real.pi) 0
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring,
    show (0 : ℝ) + 2 * Real.pi = 2 * Real.pi by ring] at hshift
  exact ⟨h1, h1.trans (by rw [← hshift])⟩

/-- Literal set of essential upper bounds from Rudin 3.7 (p. 65):
`{α ∈ ℝ | μ {x | α < ‖g x‖} = 0}`. -/
def rudinEssSupSet {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (g : X → E) : Set ℝ :=
  {α : ℝ | μ {x : X | α < ‖g x‖} = 0}

/-- Literal real-valued essential supremum `sInf (rudinEssSupSet μ g)` in the sense of Rudin 3.7.
When `μ Set.univ ≠ 0`, `0` bounds `rudinEssSupSet μ g` from below (`bddBelow_rudinEssSupSet`)
and `rudinEssSup μ g = (eLpNorm g ⊤ μ).toReal` (`rudinEssSup_eq_eLpNorm_top_toReal`), adjudicating
the 3.7 `L^∞` fidelity hold without weakening any statement. -/
def rudinEssSup {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (g : X → E) : ℝ :=
  sInf (rudinEssSupSet μ g)

theorem nonneg_of_mem_rudinEssSupSet {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} (hμ : μ Set.univ ≠ 0) {g : X → E} {α : ℝ}
    (hα : α ∈ rudinEssSupSet μ g) : 0 ≤ α := by
  by_contra hlt
  push Not at hlt
  have huniv : {x : X | α < ‖g x‖} = Set.univ :=
    Set.eq_univ_of_forall fun x => hlt.trans_le (norm_nonneg (g x))
  exact hμ (huniv ▸ hα)

theorem bddBelow_rudinEssSupSet {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} (hμ : μ Set.univ ≠ 0) (g : X → E) :
    BddBelow (rudinEssSupSet μ g) :=
  ⟨0, fun _ hα => nonneg_of_mem_rudinEssSupSet hμ hα⟩

theorem rudinEssSupSet_nonempty_iff_eLpNormEssSup {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (μ : Measure X) (g : X → E) :
    (rudinEssSupSet μ g).Nonempty ↔ eLpNormEssSup g μ < ⊤ := by
  change (rudinEssSupSet μ g).Nonempty ↔ essSup (fun x => ‖g x‖ₑ) μ < ⊤
  constructor
  · rintro ⟨α, hα⟩
    let M : ℝ := max α 0
    have hle : essSup (fun x => ‖g x‖ₑ) μ ≤ ENNReal.ofReal M := by
      refine essSup_le_of_ae_le (ENNReal.ofReal M) ?_
      change ∀ᵐ x ∂μ, ‖g x‖ₑ ≤ ENNReal.ofReal M
      rw [ae_iff]
      refine measure_mono_null (fun x hx => ?_) hα
      change ¬ ‖g x‖ₑ ≤ ENNReal.ofReal M at hx
      push Not at hx
      rw [← ofReal_norm] at hx
      exact (le_max_left α 0).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_max_right α 0)).mp hx)
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  · intro hlt
    refine ⟨(essSup (fun x => ‖g x‖ₑ) μ).toReal, ?_⟩
    have hae : ∀ᵐ x ∂μ, ‖g x‖ₑ ≤ essSup (fun x => ‖g x‖ₑ) μ := ae_le_essSup
    have hset : {x | (essSup (fun x => ‖g x‖ₑ) μ).toReal < ‖g x‖} =
        {x | ¬ ‖g x‖ ≤ (essSup (fun x => ‖g x‖ₑ) μ).toReal} := by
      ext x; simp
    change μ {x | (essSup (fun x => ‖g x‖ₑ) μ).toReal < ‖g x‖} = 0
    rw [hset, ← ae_iff]
    filter_upwards [hae] with x hx
    rw [← ofReal_norm] at hx
    exact (ENNReal.ofReal_le_iff_le_toReal hlt.ne).mp hx

theorem rudinEssSupSet_nonempty_iff {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {g : X → E} (hg : AEStronglyMeasurable g μ) :
    (rudinEssSupSet μ g).Nonempty ↔ eLpNorm g ⊤ μ < ⊤ := by
  rw [eLpNorm_exponent_top hg, rudinEssSupSet_nonempty_iff_eLpNormEssSup]

theorem rudinEssSup_eq_eLpNormEssSup_toReal {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} (hμ : μ Set.univ ≠ 0) {g : X → E}
    (hg : eLpNormEssSup g μ < ⊤) :
    rudinEssSup μ g = (eLpNormEssSup g μ).toReal := by
  have hlt : essSup (fun x => ‖g x‖ₑ) μ < ⊤ := hg
  let L : ℝ := (essSup (fun x => ‖g x‖ₑ) μ).toReal
  have hL_mem : L ∈ rudinEssSupSet μ g := by
    have hae : ∀ᵐ x ∂μ, ‖g x‖ₑ ≤ essSup (fun x => ‖g x‖ₑ) μ := ae_le_essSup
    have hset : {x | L < ‖g x‖} = {x | ¬ ‖g x‖ ≤ L} := by ext x; simp
    change μ {x | L < ‖g x‖} = 0
    rw [hset, ← ae_iff]
    filter_upwards [hae] with x hx
    rw [← ofReal_norm] at hx
    exact (ENNReal.ofReal_le_iff_le_toReal hlt.ne).mp hx
  change rudinEssSup μ g = L
  apply le_antisymm
  · exact csInf_le (bddBelow_rudinEssSupSet hμ g) hL_mem
  · refine le_csInf ⟨L, hL_mem⟩ fun α hα => ?_
    have hα0 : 0 ≤ α := nonneg_of_mem_rudinEssSupSet hμ hα
    have hle : essSup (fun x => ‖g x‖ₑ) μ ≤ ENNReal.ofReal α := by
      refine essSup_le_of_ae_le (ENNReal.ofReal α) ?_
      change ∀ᵐ x ∂μ, ‖g x‖ₑ ≤ ENNReal.ofReal α
      rw [ae_iff]
      refine measure_mono_null (fun x hx => ?_) hα
      change ¬ ‖g x‖ₑ ≤ ENNReal.ofReal α at hx
      push Not at hx
      rw [← ofReal_norm] at hx
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα0).mp hx
    change (essSup (fun x => ‖g x‖ₑ) μ).toReal ≤ α
    rw [← ENNReal.toReal_ofReal hα0]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hle

theorem rudinEssSup_eq_eLpNorm_top_toReal {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} (hμ : μ Set.univ ≠ 0) {g : X → E}
    (hg : MemLp g ⊤ μ) :
    rudinEssSup μ g = (eLpNorm g ⊤ μ).toReal := by
  have heq := eLpNorm_exponent_top hg.aestronglyMeasurable
  have hlt : eLpNormEssSup g μ < ⊤ := by
    have := hg.eLpNorm_lt_top
    rwa [heq] at this
  rw [heq, rudinEssSup_eq_eLpNormEssSup_toReal hμ hlt]

theorem rudinEssSup_lp_top_eq_norm {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} (hμ : μ Set.univ ≠ 0) (f : Lp E ⊤ μ) :
    (rudinEssSupSet μ f).Nonempty ∧
      BddBelow (rudinEssSupSet μ f) ∧
      rudinEssSup μ f = ‖f‖ := by
  have hmem : MemLp f ⊤ μ := Lp.memLp f
  refine ⟨(rudinEssSupSet_nonempty_iff hmem.aestronglyMeasurable).mpr hmem.eLpNorm_lt_top,
    bddBelow_rudinEssSupSet hμ f, ?_⟩
  rw [rudinEssSup_eq_eLpNorm_top_toReal hμ hmem, Lp.norm_def]

/-- Separability of `C(FourierCircle, ℂ)` via trigonometric polynomials with Gaussian-rational
coefficients `ℚ + i ℚ` (Rudin's remark before 11.30, p. 247). -/
instance separableSpace_continuousMap_fourierCircle :
    TopologicalSpace.SeparableSpace C(RudinRCA.Chapter04.FourierCircle, ℂ) := by
  let Idx := Σ N : ℕ, (Finset.Icc (-N : ℤ) N → ℚ × ℚ)
  let P : Idx → C(RudinRCA.Chapter04.FourierCircle, ℂ) := fun ⟨N, q⟩ =>
    ∑ n : Finset.Icc (-N : ℤ) N,
      (((q n).1 : ℂ) + ((q n).2 : ℂ) * Complex.I) • RudinRCA.Chapter04.trigMonomial n.1
  refine ⟨⟨Set.range P, Set.countable_range P, ?_⟩⟩
  rw [Metric.dense_iff]
  intro f ε hε
  obtain ⟨c, hc⟩ := RudinRCA.Chapter04.uniform_trigonometric_approximation f (ε / 2) (half_pos hε)
  let N : ℕ := c.support.sup Int.natAbs
  have hsupp_sub : c.support ⊆ Finset.Icc (-N : ℤ) N := by
    intro n hn
    rw [Finset.mem_Icc]
    have hle : Int.natAbs n ≤ N := Finset.le_sup (f := Int.natAbs) hn
    omega
  let M_card : ℝ := (Finset.Icc (-N : ℤ) N).card
  let δ : ℝ := (ε / 2) / (M_card + 1)
  have hδ : 0 < δ := div_pos (half_pos hε) (by positivity)
  have hq_exists : ∀ z : ℂ, ∃ p : ℚ × ℚ, ‖z - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ ≤ δ := by
    intro z
    obtain ⟨q₁, hq₁⟩ := exists_rat_btwn (sub_lt_self z.re (half_pos hδ))
    obtain ⟨q₂, hq₂⟩ := exists_rat_btwn (sub_lt_self z.im (half_pos hδ))
    refine ⟨(q₁, q₂), ?_⟩
    have hre : |z.re - (q₁ : ℝ)| ≤ δ / 2 := abs_sub_le_iff.mpr ⟨by linarith [hq₁.2], by linarith [hq₁.1]⟩
    have him : |z.im - (q₂ : ℝ)| ≤ δ / 2 := abs_sub_le_iff.mpr ⟨by linarith [hq₂.2], by linarith [hq₂.1]⟩
    have hsplit : z - ((q₁ : ℂ) + (q₂ : ℂ) * Complex.I) =
        ((z.re - (q₁ : ℝ) : ℝ) : ℂ) + ((z.im - (q₂ : ℝ) : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hsplit]
    calc ‖((z.re - (q₁ : ℝ) : ℝ) : ℂ) + ((z.im - (q₂ : ℝ) : ℝ) : ℂ) * Complex.I‖
        ≤ ‖((z.re - (q₁ : ℝ) : ℝ) : ℂ)‖ + ‖((z.im - (q₂ : ℝ) : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |z.re - (q₁ : ℝ)| + |z.im - (q₂ : ℝ)| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ δ / 2 + δ / 2 := add_le_add hre him
      _ = δ := add_halves δ
  choose qFn hqFn using fun n : Finset.Icc (-N : ℤ) N => hq_exists (c n.1)
  refine ⟨P ⟨N, qFn⟩, ?_, ⟨⟨N, qFn⟩, rfl⟩⟩
  have htrig_eq : RudinRCA.Chapter04.trigPolynomial c =
      ∑ n : Finset.Icc (-N : ℤ) N, c n.1 • RudinRCA.Chapter04.trigMonomial n.1 := by
    have hc_def : RudinRCA.Chapter04.trigPolynomial c =
        ∑ n ∈ c.support, c n • RudinRCA.Chapter04.trigMonomial n := rfl
    rw [hc_def, Finset.sum_subset hsupp_sub (fun n _ hnot => by simp [Finsupp.notMem_support_iff.mp hnot]),
      ← Finset.sum_coe_sort]
  have hdiff_le : ‖RudinRCA.Chapter04.trigPolynomial c - P ⟨N, qFn⟩‖ ≤ M_card * δ := by
    rw [htrig_eq]
    dsimp [P]
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ x : Finset.Icc (-N : ℤ) N,
            (c x.1 • RudinRCA.Chapter04.trigMonomial x.1 -
              (((qFn x).1 : ℂ) + ((qFn x).2 : ℂ) * Complex.I) • RudinRCA.Chapter04.trigMonomial x.1)‖
        ≤ ∑ x : Finset.Icc (-N : ℤ) N,
            ‖c x.1 • RudinRCA.Chapter04.trigMonomial x.1 -
              (((qFn x).1 : ℂ) + ((qFn x).2 : ℂ) * Complex.I) • RudinRCA.Chapter04.trigMonomial x.1‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _x : Finset.Icc (-N : ℤ) N, δ := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [← sub_smul, norm_smul]
          have hmon_le : ‖RudinRCA.Chapter04.trigMonomial x.1‖ ≤ 1 := by
            rw [RudinRCA.Chapter04.circleContinuous_norm_formula]
            refine ciSup_le fun t => (RudinRCA.Chapter04.fejerFourier_norm x.1 t).le
          calc ‖c x.1 - (((qFn x).1 : ℂ) + ((qFn x).2 : ℂ) * Complex.I)‖ *
                ‖RudinRCA.Chapter04.trigMonomial x.1‖
              ≤ δ * 1 := mul_le_mul (hqFn x) hmon_le (norm_nonneg _) hδ.le
            _ = δ := mul_one δ
      _ = M_card * δ := by simp [M_card]
  have hcard_δ : M_card * δ < ε / 2 := by
    dsimp [δ]
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    have hlt : M_card < M_card + 1 := by linarith
    have hM_nn : 0 ≤ M_card := by positivity
    nlinarith
  rw [Metric.mem_ball, dist_eq_norm']
  calc ‖f - P ⟨N, qFn⟩‖
      = ‖(f - RudinRCA.Chapter04.trigPolynomial c) +
          (RudinRCA.Chapter04.trigPolynomial c - P ⟨N, qFn⟩)‖ := by ring_nf
    _ ≤ ‖f - RudinRCA.Chapter04.trigPolynomial c‖ +
          ‖RudinRCA.Chapter04.trigPolynomial c - P ⟨N, qFn⟩‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hc (hdiff_le.trans_lt hcard_δ)
    _ = ε := add_halves ε

/-- `C(T) = C(UnitCircle, ℂ)` is a separable Banach space (Rudin p. 247). -/
instance separableSpace_continuousMap_unitCircle :
    TopologicalSpace.SeparableSpace C(UnitCircle, ℂ) := by
  let e : C(RudinRCA.Chapter04.FourierCircle, ℂ) → C(UnitCircle, ℂ) :=
    fun f => f.comp ⟨fourierToUnitCircle.symm, fourierToUnitCircle.symm.continuous⟩
  have he_surj : Function.Surjective e := by
    intro g
    refine ⟨g.comp ⟨fourierToUnitCircle, fourierToUnitCircle.continuous⟩, ?_⟩
    ext ζ
    simp [e]
  have he_lip : LipschitzWith 1 e := by
    refine LipschitzWith.of_dist_le_mul fun f₁ f₂ => ?_
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ContinuousMap.norm_le _ (norm_nonneg _)]
    intro ζ
    exact ContinuousMap.norm_coe_le_norm (f₁ - f₂) (fourierToUnitCircle.symm ζ)
  exact he_surj.denseRange.separableSpace he_lip.continuous

/-- `L^p(T)` is separable for every `1 ≤ p < ∞` (Rudin p. 247). -/
theorem separableSpace_lp_unitCircle (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    TopologicalSpace.SeparableSpace (Lp ℂ p unitCircleMeasure) :=
  (ContinuousMap.toLp_denseRange ℂ unitCircleMeasure ℂ hp).separableSpace
    (ContinuousMap.toLp p unitCircleMeasure ℂ).continuous

/-- Isometric identification `C(UnitCircle, ℂ) ≃ₗᵢ[ℂ] C₀(UnitCircle, ℂ)` on compact `T = UnitCircle`,
connecting Riesz representation (`Chapter06.theorem_6_19`) directly to `C(T)`. -/
def continuousMapEquivC0UnitCircle :
    C(UnitCircle, ℂ) ≃ₗᵢ[ℂ] ZeroAtInftyContinuousMap UnitCircle ℂ where
  toFun f :=
    { toFun := f
      continuous_toFun := f.continuous
      zero_at_infty' := by simp [Filter.cocompact_eq_bot] }
  invFun g := ⟨g, g.continuous⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := by
    change ‖(BoundedContinuousFunction.mkOfCompact f)‖ = ‖f‖
    exact BoundedContinuousFunction.norm_mkOfCompact f

end UnitCircleFoundations

/-! ### Nodes 11.16 and 11.17: `L^p` and Measure Poisson Integrals -/

section Nodes11_16_and_11_17

/-- Poisson integral `P[f](z) = ∫_T P(z, ζ) f(ζ) dσ(ζ)` of `f : UnitCircle → ℂ` on `U = ball 0 1`
with respect to normalized circle measure `σ = unitCircleMeasure`. -/
def unitPoissonIntegral (f : UnitCircle → ℂ) (z : ℂ) : ℂ :=
  ∫ η : UnitCircle, (_root_.poissonKernel 0 z (η : ℂ)) • f η ∂unitCircleMeasure

/-- Radial restriction `u_r(ζ) = u(r ζ)` on `UnitCircle` (`11.15(1)`, p. 239). -/
def unitRadialRestriction {E : Type*} (u : ℂ → E) (r : ℝ) (ζ : UnitCircle) : E :=
  u ((r : ℂ) * (ζ : ℂ))

/-- Compatibility between `unitPoissonIntegral` on `UnitCircle` and `poissonIntegral` on `ℂ`. -/
theorem unitPoissonIntegral_eq_poissonIntegral (g : ℂ → ℂ) (z : ℂ) :
    unitPoissonIntegral (fun η : UnitCircle => g (η : ℂ)) z = poissonIntegral g z := by
  unfold unitPoissonIntegral poissonIntegral
  rw [(integral_unitCircleMeasure_eq_interval _).2, Real.circleAverage_def]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp [circleMap]

theorem poissonKernel_unitCircle_nonneg {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1)
    (η : UnitCircle) :
    0 ≤ _root_.poissonKernel 0 z (η : ℂ) := by
  have hz_lt : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
  simp only [_root_.poissonKernel, sub_zero, norm_unitCircle, one_pow]
  exact div_nonneg (by nlinarith [norm_nonneg z]) (sq_nonneg _)

theorem continuous_poissonKernel_unitCircle {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    Continuous (fun η : UnitCircle => _root_.poissonKernel 0 z (η : ℂ)) := by
  have hz_lt : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
  have heq : (fun η : UnitCircle => _root_.poissonKernel 0 z (η : ℂ)) =
      fun η : UnitCircle => (1 - ‖z‖ ^ 2) / ‖(η : ℂ) - z‖ ^ 2 := by
    ext η
    simp [_root_.poissonKernel]
  rw [heq]
  refine continuous_const.div ((continuous_subtype_val.sub continuous_const).norm.pow 2) fun η => ?_
  have htri := norm_sub_norm_le (η : ℂ) z
  rw [norm_unitCircle] at htri
  exact (sq_pos_of_pos (by linarith)).ne'

theorem memLp_top_of_continuous_unitCircle {E : Type*} [NormedAddCommGroup E]
    {g : UnitCircle → E} (hg : Continuous g) :
    MemLp g ⊤ unitCircleMeasure := by
  let bcf := BoundedContinuousFunction.mkOfCompact ⟨g, hg⟩
  exact memLp_top_of_bound hg.aestronglyMeasurable ‖bcf‖
    (ae_of_all _ fun η => BoundedContinuousFunction.norm_coe_le_norm bcf η)

theorem continuous_poissonKernel_unitCircle_pair {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun p : UnitCircle × UnitCircle =>
      _root_.poissonKernel 0 ((r : ℂ) * (p.1 : ℂ)) (p.2 : ℂ)) := by
  have heq : (fun p : UnitCircle × UnitCircle =>
      _root_.poissonKernel 0 ((r : ℂ) * (p.1 : ℂ)) (p.2 : ℂ)) =
      fun p : UnitCircle × UnitCircle =>
      (1 - ‖(r : ℂ) * (p.1 : ℂ)‖ ^ 2) / ‖(p.2 : ℂ) - (r : ℂ) * (p.1 : ℂ)‖ ^ 2 := by
    ext p
    simp [_root_.poissonKernel]
  rw [heq]
  have h1 : Continuous (fun p : UnitCircle × UnitCircle => (r : ℂ) * (p.1 : ℂ)) :=
    continuous_const.mul (continuous_subtype_val.comp continuous_fst)
  have h2 : Continuous (fun p : UnitCircle × UnitCircle => (p.2 : ℂ)) :=
    continuous_subtype_val.comp continuous_snd
  refine (continuous_const.sub (h1.norm.pow 2)).div ((h2.sub h1).norm.pow 2) fun p => ?_
  have hlt1 : ‖(r : ℂ) * (p.1 : ℂ)‖ < 1 := by
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have htri := norm_sub_norm_le (p.2 : ℂ) ((r : ℂ) * (p.1 : ℂ))
  rw [norm_unitCircle] at htri
  exact (sq_pos_of_pos (by linarith)).ne'

/-- Symmetry `P(r ζ, η) = P(r η, ζ)` on `UnitCircle × UnitCircle`. -/
theorem poissonKernel_unitCircle_radial_symm (r : ℝ) (ζ η : UnitCircle) :
    _root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ) =
      _root_.poissonKernel 0 ((r : ℂ) * (η : ℂ)) (ζ : ℂ) := by
  let u : ℂ := ζ
  let v : ℂ := η
  have hid : (u * v) * conj (u - (r : ℂ) * v) = v - (r : ℂ) * u := by
    rw [map_sub, map_mul, Complex.conj_ofReal]
    calc (u * v) * (conj u - (r : ℂ) * conj v)
        = (u * conj u) * v - (r : ℂ) * u * (v * conj v) := by ring
      _ = v - (r : ℂ) * u := by
          rw [unitCircle_mul_conj ζ, unitCircle_mul_conj η]
          ring
  have hnorm_eq : ‖v - (r : ℂ) * u‖ = ‖u - (r : ℂ) * v‖ := by
    rw [← hid, norm_mul, norm_mul, RCLike.norm_conj]
    simp [u, v]
  simp only [_root_.poissonKernel, sub_zero, norm_unitCircle, one_pow, norm_mul, mul_one]
  change (1 - ‖(r : ℂ)‖ ^ 2) / ‖v - (r : ℂ) * u‖ ^ 2 =
    (1 - ‖(r : ℂ)‖ ^ 2) / ‖u - (r : ℂ) * v‖ ^ 2
  rw [hnorm_eq]

/-- Formula 11.5(3) on `UnitCircle`: `∫_T P(z, η) dσ(η) = 1` for every `z ∈ U = ball 0 1`. -/
theorem integral_poissonKernel_unitCircle {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    (∫ η : UnitCircle, _root_.poissonKernel 0 z (η : ℂ) ∂unitCircleMeasure) = 1 := by
  have hz_lt : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
  let θ : ℝ := Complex.arg z
  have hz_polar : ((‖z‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = z := by
    by_cases hz0 : z = 0
    · simp [hz0]
    · exact Complex.norm_mul_exp_arg_mul_I z
  rw [(integral_unitCircleMeasure_eq_interval _).1, smul_eq_mul]
  have hcongr : (∫ t in (-Real.pi)..Real.pi,
      _root_.poissonKernel 0 z (Complex.exp ((t : ℂ) * Complex.I))) =
      ∫ t in (-Real.pi)..Real.pi, poissonKernel ‖z‖ (θ - t) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [← hz_polar]
    simpa [circleMap] using poissonKernel_eq_mathlib (norm_nonneg z) θ t
  rw [hcongr]
  have hper : Function.Periodic (fun t : ℝ => poissonKernel ‖z‖ (θ - t)) (2 * Real.pi) := by
    intro t
    dsimp only
    rw [← node11_5_even ‖z‖ (θ - (t + 2 * Real.pi)), ← node11_5_even ‖z‖ (θ - t)]
    have : -(θ - (t + 2 * Real.pi)) = -(θ - t) + 2 * Real.pi := by ring
    rw [this, node11_5_periodic]
  have hshift := hper.intervalIntegral_add_eq (θ - Real.pi) (-Real.pi)
  rw [show θ - Real.pi + 2 * Real.pi = θ + Real.pi by ring,
    show -Real.pi + 2 * Real.pi = Real.pi by ring] at hshift
  rw [← hshift]
  have hcomp := intervalIntegral.integral_comp_sub_left
    (poissonKernel ‖z‖) θ (a := θ - Real.pi) (b := θ + Real.pi)
  rw [show θ - (θ + Real.pi) = -Real.pi by ring,
    show θ - (θ - Real.pi) = Real.pi by ring] at hcomp
  rw [hcomp]
  exact (node11_5_integral_eq_one (norm_nonneg z) hz_lt).1

theorem lintegral_poissonKernel_unitCircle {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    (∫⁻ η : UnitCircle, ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) ∂unitCircleMeasure) = 1 := by
  have hint : Integrable (fun η : UnitCircle => _root_.poissonKernel 0 z (η : ℂ)) unitCircleMeasure :=
    (continuous_poissonKernel_unitCircle hz).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ (poissonKernel_unitCircle_nonneg hz)),
    integral_poissonKernel_unitCircle hz, ENNReal.ofReal_one]

theorem radial_mem_ball_unitCircle {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ζ : UnitCircle) :
    (r : ℂ) * (ζ : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
  rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0, norm_unitCircle, mul_one]
  exact hr1

theorem integrable_real_smul_of_continuous {K : UnitCircle → ℝ} (hK : Continuous K)
    {f : UnitCircle → ℂ} (hf : Integrable f unitCircleMeasure) :
    Integrable (fun η : UnitCircle => K η • f η) unitCircleMeasure := by
  let bcf := BoundedContinuousFunction.mkOfCompact ⟨K, hK⟩
  have hmul : Integrable (fun η : UnitCircle => (K η : ℂ) * f η) unitCircleMeasure :=
    hf.bdd_mul (Complex.continuous_ofReal.comp hK).aestronglyMeasurable
      (ae_of_all _ fun η => by
        rw [Complex.norm_real]
        exact BoundedContinuousFunction.norm_coe_le_norm bcf η)
  exact hmul.congr (ae_of_all _ fun η => by simp [Complex.real_smul])

/-- Continuity of the radial slice `ζ ↦ P[f](r ζ)` on `UnitCircle` for any `f ∈ L¹(T)` (`0 ≤ r < 1`). -/
theorem continuous_unitRadialRestriction_unitPoissonIntegral
    {f : UnitCircle → ℂ} (hf : Integrable f unitCircleMeasure)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (unitRadialRestriction (unitPoissonIntegral f) r) := by
  rw [Metric.continuous_iff]
  intro ζ₀ ε hε
  let C : ℝ := ∫ η, ‖f η‖ ∂unitCircleMeasure
  have hC_nn : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have huc : UniformContinuous
      (fun p : UnitCircle × UnitCircle => _root_.poissonKernel 0 ((r : ℂ) * (p.1 : ℂ)) (p.2 : ℂ)) :=
    CompactSpace.uniformContinuous_of_continuous (continuous_poissonKernel_unitCircle_pair hr0 hr1)
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformContinuous_iff.mp huc (ε / (C + 1))
    (div_pos hε (by linarith))
  refine ⟨δ, hδ_pos, fun ζ hζ => ?_⟩
  rw [dist_eq_norm]
  unfold unitRadialRestriction unitPoissonIntegral
  have hint_z : ∀ ξ : UnitCircle,
      Integrable (fun η : UnitCircle => _root_.poissonKernel 0 ((r : ℂ) * (ξ : ℂ)) (η : ℂ) • f η)
        unitCircleMeasure :=
    fun ξ => integrable_real_smul_of_continuous
      (continuous_poissonKernel_unitCircle (radial_mem_ball_unitCircle hr0 hr1 ξ)) hf
  rw [← integral_sub (hint_z ζ) (hint_z ζ₀)]
  calc ‖∫ η : UnitCircle,
          (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ) • f η -
            _root_.poissonKernel 0 ((r : ℂ) * (ζ₀ : ℂ)) (η : ℂ) • f η) ∂unitCircleMeasure‖
      ≤ ∫ η : UnitCircle,
          ‖_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ) • f η -
            _root_.poissonKernel 0 ((r : ℂ) * (ζ₀ : ℂ)) (η : ℂ) • f η‖ ∂unitCircleMeasure :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ η : UnitCircle, (ε / (C + 1)) * ‖f η‖ ∂unitCircleMeasure := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
          (hf.norm.const_mul _) (ae_of_all _ fun η => ?_)
        dsimp only
        rw [← sub_smul, norm_smul]
        have hk : ‖_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ) -
            _root_.poissonKernel 0 ((r : ℂ) * (ζ₀ : ℂ)) (η : ℂ)‖ ≤ ε / (C + 1) := by
          have hp : dist (ζ, η) (ζ₀, η) < δ := by simpa [Prod.dist_eq] using hζ
          exact (hδ hp).le
        exact mul_le_mul_of_nonneg_right hk (norm_nonneg _)
    _ = (ε / (C + 1)) * C := integral_const_mul _ _
    _ < (ε / (C + 1)) * (C + 1) :=
        mul_lt_mul_of_pos_left (by linarith) (div_pos hε (by linarith))
    _ = ε := div_mul_cancel₀ ε (by linarith)

/-- Pointwise bound `‖P[f](z)‖ₑ ≤ ∫⁻ η, P(z, η) ‖f(η)‖ₑ dσ(η)` for `z ∈ ball 0 1`. -/
theorem enorm_unitPoissonIntegral_le {f : UnitCircle → ℂ} {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    ‖unitPoissonIntegral f z‖ₑ ≤
      ∫⁻ η : UnitCircle,
        ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) * ‖f η‖ₑ ∂unitCircleMeasure := by
  calc ‖unitPoissonIntegral f z‖ₑ
      ≤ ∫⁻ η : UnitCircle, ‖_root_.poissonKernel 0 z (η : ℂ) • f η‖ₑ ∂unitCircleMeasure :=
        enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ η : UnitCircle,
          ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) * ‖f η‖ₑ ∂unitCircleMeasure := by
        refine lintegral_congr fun η => ?_
        rw [enorm_smul, Real.enorm_of_nonneg (poissonKernel_unitCircle_nonneg hz η)]

/-- 11.16(1) (`eLpNorm` form): for `1 ≤ p ≤ ∞`, `f ∈ L^p(T)`, and `0 ≤ r < 1`,
`‖u_r‖_p ≤ ‖f‖_p` where `u = P[f]`. -/
theorem eLpNorm_unitRadialRestriction_unitPoissonIntegral_le
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) {f : UnitCircle → ℂ} (hf : MemLp f p unitCircleMeasure)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    eLpNorm (unitRadialRestriction (unitPoissonIntegral f) r) p unitCircleMeasure ≤
      eLpNorm f p unitCircleMeasure := by
  let ur := unitRadialRestriction (unitPoissonIntegral f) r
  have hur_meas : AEStronglyMeasurable ur unitCircleMeasure :=
    (continuous_unitRadialRestriction_unitPoissonIntegral (hf.integrable hp1) hr0 hr1).aestronglyMeasurable
  by_cases hp_top : p = ⊤
  · subst hp_top
    rw [eLpNorm_exponent_top hur_meas, eLpNorm_exponent_top hf.aestronglyMeasurable]
    change essSup (fun x => ‖ur x‖ₑ) unitCircleMeasure ≤
      essSup (fun x => ‖f x‖ₑ) unitCircleMeasure
    refine essSup_le_of_ae_le _ ?_
    refine ae_of_all _ fun ζ => ?_
    dsimp only [ur, unitRadialRestriction]
    have hz := radial_mem_ball_unitCircle hr0 hr1 ζ
    have hae : ∀ᵐ η ∂unitCircleMeasure,
        ‖f η‖ₑ ≤ essSup (fun x => ‖f x‖ₑ) unitCircleMeasure := ae_le_essSup
    calc ‖unitPoissonIntegral f ((r : ℂ) * (ζ : ℂ))‖ₑ
        ≤ ∫⁻ η : UnitCircle,
            ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ)) * ‖f η‖ₑ
              ∂unitCircleMeasure := enorm_unitPoissonIntegral_le hz
      _ ≤ ∫⁻ η : UnitCircle,
            ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ)) *
              essSup (fun x => ‖f x‖ₑ) unitCircleMeasure ∂unitCircleMeasure := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with η hη
          gcongr
      _ = (∫⁻ η : UnitCircle,
            ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ))
              ∂unitCircleMeasure) * essSup (fun x => ‖f x‖ₑ) unitCircleMeasure :=
          lintegral_mul_const _
            (continuous_poissonKernel_unitCircle hz).measurable.ennreal_ofReal
      _ = essSup (fun x => ‖f x‖ₑ) unitCircleMeasure := by
          rw [lintegral_poissonKernel_unitCircle hz, one_mul]
  · have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
    let p' : ℝ := p.toReal
    have hp'_ge1 : 1 ≤ p' := by
      have := ENNReal.toReal_mono hp_top hp1
      simpa [p'] using this
    have hp'_pos : 0 < p' := zero_lt_one.trans_le hp'_ge1
    -- Rudin 11.16(4): pointwise `‖u_r(ζ)‖ₑ ^ p' ≤ ∫⁻ η, P(r ζ, η) * ‖f η‖ₑ ^ p' dσ(η)`
    have h11_16_4 : ∀ ζ : UnitCircle,
        ‖ur ζ‖ₑ ^ p' ≤
          ∫⁻ η : UnitCircle,
            ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ)) *
              ‖f η‖ₑ ^ p' ∂unitCircleMeasure := by
      intro ζ
      have hz := radial_mem_ball_unitCircle hr0 hr1 ζ
      rcases hp'_ge1.eq_or_lt with hp'_eq1 | hp'_gt1
      · rw [← hp'_eq1, ENNReal.rpow_one]
        change ‖unitPoissonIntegral f ((r : ℂ) * (ζ : ℂ))‖ₑ ≤ _
        simpa only [← hp'_eq1, ENNReal.rpow_one] using enorm_unitPoissonIntegral_le hz
      · let q' : ℝ := p'.conjExponent
        have hpq : p'.HolderConjugate q' := Real.HolderConjugate.conjExponent hp'_gt1
        have hq'_gt1 : 1 < q' := hpq.symm.lt
        have hq'_pos : 0 < q' := zero_lt_one.trans hq'_gt1
        let K : UnitCircle → ℝ≥0∞ := fun η =>
          ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ))
        have hK_meas : Measurable K :=
          (continuous_poissonKernel_unitCircle hz).measurable.ennreal_ofReal
        have hf_aem : AEMeasurable (fun η => ‖f η‖ₑ) unitCircleMeasure :=
          hf.aestronglyMeasurable.enorm
        have hsplit : ∀ η : UnitCircle,
            K η * ‖f η‖ₑ = (K η ^ p'⁻¹ * ‖f η‖ₑ) * (K η ^ q'⁻¹) := by
          intro η
          have hpow : K η ^ p'⁻¹ * K η ^ q'⁻¹ = K η := by
            rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity),
              hpq.inv_add_inv_eq_one, ENNReal.rpow_one]
          calc K η * ‖f η‖ₑ = (K η ^ p'⁻¹ * K η ^ q'⁻¹) * ‖f η‖ₑ := by rw [hpow]
            _ = (K η ^ p'⁻¹ * ‖f η‖ₑ) * (K η ^ q'⁻¹) := by ac_rfl
        have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq unitCircleMeasure hpq
          ((hK_meas.pow_const p'⁻¹).aemeasurable.mul hf_aem)
          (hK_meas.pow_const q'⁻¹).aemeasurable
        have hK_p : (fun η => (K η ^ p'⁻¹ * ‖f η‖ₑ) ^ p') =
            fun η => K η * ‖f η‖ₑ ^ p' := by
          ext η
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp'_pos.le, ← ENNReal.rpow_mul,
            inv_mul_cancel₀ hp'_pos.ne', ENNReal.rpow_one]
        have hK_q : (fun η => (K η ^ q'⁻¹) ^ q') = K := by
          ext η
          rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hq'_pos.ne', ENNReal.rpow_one]
        have hK_int1 : (∫⁻ η, K η ∂unitCircleMeasure) = 1 :=
          lintegral_poissonKernel_unitCircle hz
        have hbound1 : ‖ur ζ‖ₑ ≤
            (∫⁻ η, K η * ‖f η‖ₑ ^ p' ∂unitCircleMeasure) ^ (1 / p') := by
          calc ‖ur ζ‖ₑ ≤ ∫⁻ η, K η * ‖f η‖ₑ ∂unitCircleMeasure :=
                enorm_unitPoissonIntegral_le hz
            _ = ∫⁻ η, (K η ^ p'⁻¹ * ‖f η‖ₑ) * (K η ^ q'⁻¹) ∂unitCircleMeasure :=
                lintegral_congr hsplit
            _ ≤ (∫⁻ η, (K η ^ p'⁻¹ * ‖f η‖ₑ) ^ p' ∂unitCircleMeasure) ^ (1 / p') *
                  (∫⁻ η, (K η ^ q'⁻¹) ^ q' ∂unitCircleMeasure) ^ (1 / q') := hholder
            _ = (∫⁻ η, K η * ‖f η‖ₑ ^ p' ∂unitCircleMeasure) ^ (1 / p') := by
                rw [hK_p, hK_q, hK_int1, ENNReal.one_rpow, mul_one]
        calc ‖ur ζ‖ₑ ^ p'
            ≤ ((∫⁻ η, K η * ‖f η‖ₑ ^ p' ∂unitCircleMeasure) ^ (1 / p')) ^ p' :=
              ENNReal.rpow_le_rpow hbound1 hp'_pos.le
          _ = ∫⁻ η, K η * ‖f η‖ₑ ^ p' ∂unitCircleMeasure := by
              rw [← ENNReal.rpow_mul, one_div_mul_cancel hp'_pos.ne', ENNReal.rpow_one]
    -- Integrate 11.16(4) over `T` and swap via Tonelli + kernel symmetry
    have hprod_aem : AEMeasurable
        (Function.uncurry fun ζ η : UnitCircle =>
          ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ)) * ‖f η‖ₑ ^ p')
        (unitCircleMeasure.prod unitCircleMeasure) := by
      have hK_meas : Measurable (fun q : UnitCircle × UnitCircle =>
          ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (q.1 : ℂ)) (q.2 : ℂ))) :=
        (continuous_poissonKernel_unitCircle_pair hr0 hr1).measurable.ennreal_ofReal
      have hf_aem : AEMeasurable (fun q : UnitCircle × UnitCircle => ‖f q.2‖ₑ ^ p')
          (unitCircleMeasure.prod unitCircleMeasure) :=
        (hf.aestronglyMeasurable.enorm.pow_const p').comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_snd
      exact hK_meas.aemeasurable.mul hf_aem
    have hlint_le :
        (∫⁻ ζ, ‖ur ζ‖ₑ ^ p' ∂unitCircleMeasure) ≤
          ∫⁻ η, ‖f η‖ₑ ^ p' ∂unitCircleMeasure := by
      calc (∫⁻ ζ, ‖ur ζ‖ₑ ^ p' ∂unitCircleMeasure)
          ≤ ∫⁻ ζ, ∫⁻ η,
              ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ)) *
                ‖f η‖ₑ ^ p' ∂unitCircleMeasure ∂unitCircleMeasure :=
            lintegral_mono h11_16_4
        _ = ∫⁻ η, ∫⁻ ζ,
              ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ)) *
                ‖f η‖ₑ ^ p' ∂unitCircleMeasure ∂unitCircleMeasure :=
            lintegral_lintegral_swap hprod_aem
        _ = ∫⁻ η, ‖f η‖ₑ ^ p' ∂unitCircleMeasure := by
            refine lintegral_congr fun η => ?_
            have hsymm : (fun ζ : UnitCircle =>
                ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ)) *
                  ‖f η‖ₑ ^ p') =
                fun ζ : UnitCircle =>
                  ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (η : ℂ)) (ζ : ℂ)) *
                    ‖f η‖ₑ ^ p' := by
              ext ζ
              rw [poissonKernel_unitCircle_radial_symm r ζ η]
            rw [hsymm, lintegral_mul_const _
              (continuous_poissonKernel_unitCircle (radial_mem_ball_unitCircle hr0 hr1 η)).measurable.ennreal_ofReal,
              lintegral_poissonKernel_unitCircle (radial_mem_ball_unitCircle hr0 hr1 η), one_mul]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hur_meas,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hf.aestronglyMeasurable]
    exact ENNReal.rpow_le_rpow hlint_le (by positivity)

theorem memLp_unitRadialRestriction_unitPoissonIntegral
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) {f : UnitCircle → ℂ} (hf : MemLp f p unitCircleMeasure)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    MemLp (unitRadialRestriction (unitPoissonIntegral f) r) p unitCircleMeasure :=
  lt_of_le_of_lt (eLpNorm_unitRadialRestriction_unitPoissonIntegral_le hp1 hf hr0 hr1)
    hf.eLpNorm_lt_top

/-- Theorem 3.14 on `T = UnitCircle`: continuous functions are dense in `L^p(T)` for `1 ≤ p < ∞`. -/
theorem exists_continuous_eLpNorm_sub_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp_top : p ≠ ⊤)
    {f : UnitCircle → ℂ} (hf : MemLp f p unitCircleMeasure) {δ : ℝ} (hδ_pos : 0 < δ) :
    ∃ g : C(UnitCircle, ℂ),
      eLpNorm (f - (g : UnitCircle → ℂ)) p unitCircleMeasure ≤ ENNReal.ofReal δ := by
  obtain ⟨g, hg_dist⟩ := Metric.denseRange_iff.mp
    (ContinuousMap.toLp_denseRange ℂ unitCircleMeasure ℂ hp_top) (hf.toLp f) δ hδ_pos
  refine ⟨g, ?_⟩
  let F : Lp ℂ p unitCircleMeasure := hf.toLp f
  let G : Lp ℂ p unitCircleMeasure := ContinuousMap.toLp p unitCircleMeasure ℂ g
  have hnorm : ‖F - G‖ < δ := by
    rw [← dist_eq_norm]
    simpa only [F, G, dist_comm] using hg_dist
  have hcoe : ((F - G : Lp ℂ p unitCircleMeasure) : UnitCircle → ℂ) =ᵐ[unitCircleMeasure]
      (f - (g : UnitCircle → ℂ)) := by
    filter_upwards [Lp.coeFn_sub F G, hf.coeFn_toLp,
      ContinuousMap.coeFn_toLp (p := p) (𝕜 := ℂ) unitCircleMeasure g] with ζ hsub hfζ hgζ
    dsimp only [F, G] at hsub
    rw [hsub, Pi.sub_apply, Pi.sub_apply, hfζ, hgζ]
  rw [← eLpNorm_congr_ae hcoe]
  have hlt_top := Lp.eLpNorm_lt_top (F - G)
  rw [Lp.norm_def] at hnorm
  exact (ENNReal.le_ofReal_iff_toReal_le hlt_top.ne hδ_pos.le).mpr hnorm.le

/-- Extend `g : C(UnitCircle, ℂ)` by `0` outside `Metric.sphere (0 : ℂ) 1`. -/
private def extendZeroOutsideUnitCircle (g : C(UnitCircle, ℂ)) (z : ℂ) : ℂ :=
  open Classical in
  if hz : z ∈ Metric.sphere (0 : ℂ) 1 then g ⟨z, hz⟩ else 0

private theorem extendZeroOutsideUnitCircle_apply (g : C(UnitCircle, ℂ)) (ζ : UnitCircle) :
    extendZeroOutsideUnitCircle g (ζ : ℂ) = g ζ := by
  unfold extendZeroOutsideUnitCircle
  simp

private theorem continuousOn_extendZeroOutsideUnitCircle (g : C(UnitCircle, ℂ)) :
    ContinuousOn (extendZeroOutsideUnitCircle g) (Metric.sphere (0 : ℂ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact g.continuous.congr fun ζ => (extendZeroOutsideUnitCircle_apply g ζ).symm

private theorem eLpNorm_sub_comm_le {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ℝ≥0∞} {δ : ℝ} (c d : α → E)
    (h3 : eLpNorm (d - c) p μ ≤ ENNReal.ofReal δ) :
    eLpNorm (c - d) p μ ≤ ENNReal.ofReal δ := by
  simpa only [neg_sub] using (eLpNorm_neg (d - c) p μ).le.trans h3

private theorem ofReal_add_three {δ : ℝ} (hδ : 0 ≤ δ) :
    (ENNReal.ofReal δ + ENNReal.ofReal δ) + ENNReal.ofReal δ = ENNReal.ofReal (3 * δ) := by
  rw [← ENNReal.ofReal_add hδ hδ, ← ENNReal.ofReal_add (add_nonneg hδ hδ) hδ]
  exact congrArg ENNReal.ofReal (by ring)

private theorem eLpNorm_add_three_le_of_le
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) {δ : ℝ} (hδ_pos : 0 < δ)
    (a b c d : α → E)
    (h1 : eLpNorm (a - b) p μ ≤ ENNReal.ofReal δ)
    (h2 : eLpNorm (b - c) p μ ≤ ENNReal.ofReal δ)
    (h3 : eLpNorm (d - c) p μ ≤ ENNReal.ofReal δ) :
    eLpNorm (a - d) p μ ≤ ENNReal.ofReal (3 * δ) := by
  have h3' := eLpNorm_sub_comm_le c d h3
  have hac : eLpNorm (a - c) p μ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ := by
    have heq : a - c = (a - b) + (b - c) := by ext x; simp
    rw [heq]
    exact (eLpNorm_add_le hp1).trans (add_le_add h1 h2)
  have had : eLpNorm (a - d) p μ ≤ (ENNReal.ofReal δ + ENNReal.ofReal δ) + ENNReal.ofReal δ := by
    have heq : a - d = (a - c) + (c - d) := by ext x; simp
    rw [heq]
    exact (eLpNorm_add_le hp1).trans (add_le_add hac h3')
  rwa [ofReal_add_three hδ_pos.le] at had

private theorem eLpNorm_unitRadialRestriction_sub_first
    {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    {f : UnitCircle → ℂ} (hf : MemLp f p unitCircleMeasure)
    (g : C(UnitCircle, ℂ)) {δ : ℝ}
    (hfg_lp : eLpNorm (f - (g : UnitCircle → ℂ)) p unitCircleMeasure ≤ ENNReal.ofReal δ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    eLpNorm
      (unitRadialRestriction (unitPoissonIntegral f) r -
        unitRadialRestriction (unitPoissonIntegral g) r)
      p unitCircleMeasure ≤ ENNReal.ofReal δ := by
  have hf_int : Integrable f unitCircleMeasure := hf.integrable hp1
  have hg_int : Integrable (g : UnitCircle → ℂ) unitCircleMeasure :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have huv_eq : ∀ ζ : UnitCircle,
      (unitRadialRestriction (unitPoissonIntegral f) r -
        unitRadialRestriction (unitPoissonIntegral g) r) ζ =
      unitRadialRestriction (unitPoissonIntegral (f - (g : UnitCircle → ℂ))) r ζ := by
    intro ζ
    simp only [Pi.sub_apply]
    unfold unitRadialRestriction unitPoissonIntegral
    have hz := radial_mem_ball_unitCircle hr0 hr1 ζ
    have hK_cont := continuous_poissonKernel_unitCircle hz
    rw [← integral_sub (integrable_real_smul_of_continuous hK_cont hf_int)
      (integrable_real_smul_of_continuous hK_cont hg_int)]
    exact integral_congr_ae (ae_of_all _ fun η => (smul_sub _ _ _).symm)
  have hf_sub_g_mem : MemLp (f - (g : UnitCircle → ℂ)) p unitCircleMeasure :=
    hf.sub ((memLp_top_of_continuous_unitCircle g.continuous).mono_exponent le_top)
  rw [eLpNorm_congr_ae (ae_of_all _ huv_eq)]
  exact (eLpNorm_unitRadialRestriction_unitPoissonIntegral_le hp1 hf_sub_g_mem hr0 hr1).trans hfg_lp

private theorem eLpNorm_unitRadialRestriction_sub_second
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp_top : p ≠ ⊤)
    (g : C(UnitCircle, ℂ)) {δ : ℝ}
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrunif : ∀ x ∈ Metric.sphere (0 : ℂ) 1,
      dist (extendZeroOutsideUnitCircle g x)
        (_root_.RudinRCA.Chapter11.poissonIntegral (extendZeroOutsideUnitCircle g) ((r : ℂ) * x)) < δ) :
    eLpNorm (unitRadialRestriction (unitPoissonIntegral g) r - (g : UnitCircle → ℂ))
      p unitCircleMeasure ≤ ENNReal.ofReal δ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hg_int : Integrable (g : UnitCircle → ℂ) unitCircleMeasure :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm2 : AEStronglyMeasurable
      (unitRadialRestriction (unitPoissonIntegral g) r - (g : UnitCircle → ℂ)) unitCircleMeasure :=
    (continuous_unitRadialRestriction_unitPoissonIntegral hg_int hr0 hr1).aestronglyMeasurable.sub
      g.continuous.aestronglyMeasurable
  have hvg_bound : ∀ ζ : UnitCircle,
      ‖(unitRadialRestriction (unitPoissonIntegral g) r - (g : UnitCircle → ℂ)) ζ‖ ≤ δ := by
    intro ζ
    simp only [Pi.sub_apply]
    have hvr_eq : unitRadialRestriction (unitPoissonIntegral g) r ζ =
        _root_.RudinRCA.Chapter11.poissonIntegral (extendZeroOutsideUnitCircle g)
          ((r : ℂ) * (ζ : ℂ)) := by
      unfold unitRadialRestriction
      have hcongr : (g : UnitCircle → ℂ) =
          (fun η : UnitCircle => extendZeroOutsideUnitCircle g (η : ℂ)) :=
        funext fun η => (extendZeroOutsideUnitCircle_apply g η).symm
      rw [hcongr, unitPoissonIntegral_eq_poissonIntegral]
    rw [hvr_eq, ← extendZeroOutsideUnitCircle_apply g ζ, ← dist_eq_norm']
    exact (hrunif (ζ : ℂ) ζ.2).le
  have hp'_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hm2]
  calc (∫⁻ ζ, ‖(unitRadialRestriction (unitPoissonIntegral g) r - (g : UnitCircle → ℂ)) ζ‖ₑ ^ p.toReal
          ∂unitCircleMeasure) ^ (1 / p.toReal)
      ≤ (∫⁻ _ζ, (ENNReal.ofReal δ) ^ p.toReal ∂unitCircleMeasure) ^ (1 / p.toReal) := by
        refine ENNReal.rpow_le_rpow (lintegral_mono fun ζ => ?_) (by positivity)
        refine ENNReal.rpow_le_rpow ?_ hp'_pos.le
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hvg_bound ζ)
    _ = ENNReal.ofReal δ := by
      rw [lintegral_const, unitCircleMeasure_univ, mul_one,
          ← ENNReal.rpow_mul, mul_one_div_cancel hp'_pos.ne', ENNReal.rpow_one]

private theorem eLpNorm_unitRadialRestriction_sub_le_three_mul
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp_top : p ≠ ⊤)
    {f : UnitCircle → ℂ} (hf : MemLp f p unitCircleMeasure)
    (g : C(UnitCircle, ℂ)) {δ : ℝ} (hδ_pos : 0 < δ)
    (hfg_lp : eLpNorm (f - (g : UnitCircle → ℂ)) p unitCircleMeasure ≤ ENNReal.ofReal δ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrunif : ∀ x ∈ Metric.sphere (0 : ℂ) 1,
      dist (extendZeroOutsideUnitCircle g x)
        (_root_.RudinRCA.Chapter11.poissonIntegral (extendZeroOutsideUnitCircle g) ((r : ℂ) * x)) < δ) :
    eLpNorm (unitRadialRestriction (unitPoissonIntegral f) r - f)
        p unitCircleMeasure ≤ ENNReal.ofReal (3 * δ) :=
  eLpNorm_add_three_le_of_le hp1 hδ_pos
    (unitRadialRestriction (unitPoissonIntegral f) r)
    (unitRadialRestriction (unitPoissonIntegral g) r)
    (g : UnitCircle → ℂ) f
    (eLpNorm_unitRadialRestriction_sub_first hp1 hf g hfg_lp hr0 hr1)
    (eLpNorm_unitRadialRestriction_sub_second hp1 hp_top g hr0 hr1 hrunif)
    hfg_lp

/-- 11.16(2) (`eLpNorm` form): for `1 ≤ p < ∞` and `f ∈ L^p(T)`,
`lim_{r → 1⁻} ‖u_r - f‖_p = 0` where `u = P[f]`. -/
theorem tendsto_eLpNorm_unitRadialRestriction_unitPoissonIntegral_sub
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp_top : p ≠ ⊤)
    {f : UnitCircle → ℂ} (hf : MemLp f p unitCircleMeasure) :
    Tendsto (fun r : ℝ =>
      eLpNorm (fun ζ => unitRadialRestriction (unitPoissonIntegral f) r ζ - f ζ)
        p unitCircleMeasure)
      (𝓝[<] 1) (𝓝 0) := by
  have hp1 : 1 ≤ p := Fact.out
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_lt⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal (3 * δ) ≤ ε := by
    by_cases htop : ε = ⊤
    · exact ⟨1, zero_lt_one, by simp [htop]⟩
    · have hpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
      refine ⟨ε.toReal / 4, by positivity, ?_⟩
      conv_rhs => rw [← ENNReal.ofReal_toReal htop]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨g, hfg_lp⟩ := exists_continuous_eLpNorm_sub_le hp_top hf hδ_pos
  have hunif := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_poissonIntegral_radial (continuousOn_extendZeroOutsideUnitCircle g))
    δ hδ_pos
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1)),
    self_mem_nhdsWithin, hunif] with r hr0_lt hr1 hrunif
  have hcongr : (fun ζ => unitRadialRestriction (unitPoissonIntegral f) r ζ - f ζ) =
      (unitRadialRestriction (unitPoissonIntegral f) r - f) := rfl
  rw [eLpNorm_congr_ae (ae_of_all _ fun _ => rfl)]
  exact (eLpNorm_unitRadialRestriction_sub_le_three_mul hp1 hp_top hf g hδ_pos hfg_lp
    hr0_lt.le hr1 hrunif).trans hδ_lt

/-- Radial Poisson operator `f ↦ (u_r ∈ Lp ℂ p unitCircleMeasure)` on `Lp ℂ p unitCircleMeasure`. -/
def lpRadialPoisson (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Lp ℂ p unitCircleMeasure)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : Lp ℂ p unitCircleMeasure :=
  (memLp_unitRadialRestriction_unitPoissonIntegral (Fact.out : 1 ≤ p) (Lp.memLp f) hr0 hr1).toLp
    (unitRadialRestriction (unitPoissonIntegral f) r)

/-- 11.16 (Theorem, Rudin pp. 239–240):
1. For `1 ≤ p ≤ ∞`, `f ∈ L^p(T)`, and `u = P[f]`, `‖u_r‖_p ≤ ‖f‖_p` for every `0 ≤ r < 1`
   (including the literal 3.7 essential supremum `rudinEssSup` at `p = ∞`).
2. For `1 ≤ p < ∞`, `lim_{r → 1⁻} ‖u_r - f‖_p = 0`. -/
theorem theorem11_16 (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Lp ℂ p unitCircleMeasure) :
    (∀ {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1),
      ‖lpRadialPoisson p f hr0 hr1‖ ≤ ‖f‖ ∧
      eLpNorm (unitRadialRestriction (unitPoissonIntegral f) r) p unitCircleMeasure ≤
        eLpNorm f p unitCircleMeasure) ∧
    (p = ⊤ → ∀ {r : ℝ}, 0 ≤ r → r < 1 →
      rudinEssSup unitCircleMeasure (unitRadialRestriction (unitPoissonIntegral f) r) ≤
        rudinEssSup unitCircleMeasure f) ∧
    (p ≠ ⊤ →
      Tendsto (fun r : ℝ =>
        eLpNorm (fun ζ => unitRadialRestriction (unitPoissonIntegral f) r ζ - f ζ)
          p unitCircleMeasure)
        (𝓝[<] 1) (𝓝 0)) := by
  have hp1 : 1 ≤ p := Fact.out
  refine ⟨fun {r} hr0 hr1 => ?_, fun hp_top {r} hr0 hr1 => ?_,
    fun hp_top => tendsto_eLpNorm_unitRadialRestriction_unitPoissonIntegral_sub hp_top (Lp.memLp f)⟩
  · have he := eLpNorm_unitRadialRestriction_unitPoissonIntegral_le hp1 (Lp.memLp f) hr0 hr1
    refine ⟨?_, he⟩
    rw [Lp.norm_def, Lp.norm_def]
    unfold lpRadialPoisson
    have hcoe := (memLp_unitRadialRestriction_unitPoissonIntegral hp1 (Lp.memLp f) hr0 hr1).coeFn_toLp
    rw [eLpNorm_congr_ae hcoe]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) he
  · subst hp_top
    have hf_mem : MemLp f ⊤ unitCircleMeasure := Lp.memLp f
    have hur_mem : MemLp (unitRadialRestriction (unitPoissonIntegral f) r) ⊤ unitCircleMeasure :=
      memLp_unitRadialRestriction_unitPoissonIntegral le_top hf_mem hr0 hr1
    have he := eLpNorm_unitRadialRestriction_unitPoissonIntegral_le le_top hf_mem hr0 hr1
    rw [rudinEssSup_eq_eLpNorm_top_toReal unitCircleMeasure_univ_ne_zero hur_mem,
      rudinEssSup_eq_eLpNorm_top_toReal unitCircleMeasure_univ_ne_zero hf_mem]
    exact ENNReal.toReal_mono hf_mem.eLpNorm_lt_top.ne he

/-- Also record the direct `Lp`-norm convergence `lim_{r → 1⁻} ‖u_r - f‖_{Lp} = 0` (`11.16(2)`). -/
theorem theorem11_16_lp_norm_tendsto (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p ≠ ⊤)
    (f : Lp ℂ p unitCircleMeasure) :
    Tendsto (fun r : ℝ =>
      if hr : 0 ≤ r ∧ r < 1 then ‖lpRadialPoisson p f hr.1 hr.2 - f‖ else 0)
      (𝓝[<] 1) (𝓝 0) := by
  have he := tendsto_eLpNorm_unitRadialRestriction_unitPoissonIntegral_sub hp_top (Lp.memLp f)
  have htoReal : Tendsto (fun r : ℝ =>
      (eLpNorm (fun ζ => unitRadialRestriction (unitPoissonIntegral f) r ζ - f ζ)
        p unitCircleMeasure).toReal)
      (𝓝[<] 1) (𝓝 0) := by
    have hc := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he
    simpa only [Function.comp_def, ENNReal.toReal_zero] using hc
  refine htoReal.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1)),
    self_mem_nhdsWithin] with r hr0_lt hr1
  have hr : 0 ≤ r ∧ r < 1 := ⟨hr0_lt.le, hr1⟩
  simp only [hr, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_ae
  have hmem := memLp_unitRadialRestriction_unitPoissonIntegral (Fact.out : 1 ≤ p) (Lp.memLp f) hr.1 hr.2
  filter_upwards [Lp.coeFn_sub (lpRadialPoisson p f hr.1 hr.2) f, hmem.coeFn_toLp] with ζ hsub hcoe
  rw [hsub, Pi.sub_apply]
  unfold lpRadialPoisson
  rw [hcoe]

/-- 11.17(1) (Definition, Rudin p. 240): Poisson integral `u(z) = P[dμ](z) = ∫_T P(z, ζ) dμ(ζ)`
of a complex Borel measure `μ` on `T = UnitCircle`. -/
def poissonMeasureIntegral (μ : ComplexMeasure UnitCircle) (z : ℂ) : ℂ :=
  RudinRCA.Chapter10.complexMeasureIntegral μ
    (fun η : UnitCircle => (_root_.poissonKernel 0 z (η : ℂ) : ℂ))

/-- Compatibility `P[f dσ](z) = P[f](z)` between `poissonMeasureIntegral` and `unitPoissonIntegral`
for `f ∈ L¹(T)` (`z ∈ ball 0 1`). -/
theorem poissonMeasureIntegral_withDensityᵥ {f : UnitCircle → ℂ}
    (hf : Integrable f unitCircleMeasure) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    poissonMeasureIntegral (unitCircleMeasure.withDensityᵥ f) z = unitPoissonIntegral f z := by
  obtain ⟨f₀, hf₀_smeas, hf₀_ae⟩ := hf.aestronglyMeasurable
  have hf₀_meas : Measurable f₀ := hf₀_smeas.measurable
  have hf₀_int : Integrable f₀ unitCircleMeasure := hf.congr hf₀_ae
  have hμ_eq : unitCircleMeasure.withDensityᵥ f = unitCircleMeasure.withDensityᵥ f₀ := by
    ext E hE
    rw [withDensityᵥ_apply hf hE, withDensityᵥ_apply hf₀_int hE]
    exact setIntegral_congr_ae hE (hf₀_ae.mono fun x hx _ => hx)
  have hP_eq : unitPoissonIntegral f z = unitPoissonIntegral f₀ z :=
    integral_congr_ae (hf₀_ae.mono fun η hη => by dsimp; rw [hη])
  rw [hμ_eq, hP_eq]
  let μ := unitCircleMeasure.withDensityᵥ f₀
  have hK_cont := continuous_poissonKernel_unitCircle hz
  have hK_int_var : Integrable (fun η : UnitCircle => (_root_.poissonKernel 0 z (η : ℂ) : ℂ))
      μ.variation :=
    (Complex.continuous_ofReal.comp hK_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold poissonMeasureIntegral RudinRCA.Chapter10.complexMeasureIntegral unitPoissonIntegral
  let g : UnitCircle → ℂ := fun η => (_root_.poissonKernel 0 z (η : ℂ) : ℂ)
  have hgen : ∀ k : UnitCircle → ℂ, Integrable k μ.variation →
      (∫ᵛ η, k η ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) =
        ∫ η, k η * f₀ η ∂unitCircleMeasure := by
    intro k hk_var
    have hvar_eq : μ.variation = unitCircleMeasure.withDensity (fun η => ‖f₀ η‖ₑ) :=
      RudinRCA.Chapter06.theorem_6_13 unitCircleMeasure hf₀_int
    have hfn_meas : Measurable (fun η => ‖f₀ η‖ₑ) := hf₀_meas.enorm
    have hnull_transfer : ∀ {S : Set UnitCircle}, μ.variation S = 0 →
        ∀ᵐ η ∂unitCircleMeasure, f₀ η ≠ 0 → η ∉ S := by
      intro S hS
      let N := toMeasurable μ.variation S
      have hN_meas : MeasurableSet N := measurableSet_toMeasurable _ _
      have hN_zero : (∫⁻ η in N, ‖f₀ η‖ₑ ∂unitCircleMeasure) = 0 := by
        rw [← withDensity_apply _ hN_meas, ← hvar_eq, measure_toMeasurable]
        exact hS
      have hN_ae : ∀ᵐ η ∂unitCircleMeasure.restrict N, ‖f₀ η‖ₑ = 0 :=
        (lintegral_eq_zero_iff hfn_meas).mp hN_zero
      filter_upwards [(ae_restrict_iff' hN_meas).mp hN_ae] with η hη hf_ne hmem
      exact hf_ne (by simpa using hη (subset_toMeasurable _ _ hmem))
    have hmul_int : ∀ q : UnitCircle → ℂ, Integrable q μ.variation →
        Integrable (fun η => q η * f₀ η) unitCircleMeasure := by
      intro q hq_var
      have hq := hq_var
      rw [hvar_eq, integrable_withDensity_iff_integrable_smul' hfn_meas
        (ae_of_all _ fun _ => ENNReal.coe_lt_top)] at hq
      have hae_norm : ∀ η, ‖q η * f₀ η‖ = ‖(‖f₀ η‖ₑ).toReal • q η‖ := fun η => by
        rw [norm_mul, norm_smul, Real.norm_eq_abs, toReal_enorm, abs_norm, mul_comm]
      refine ⟨?_, ?_⟩
      · obtain ⟨q₀, hq₀_smeas, hq₀_ae⟩ := hq_var.1
        refine (hq₀_smeas.aestronglyMeasurable.mul hf₀_int.aestronglyMeasurable).congr ?_
        filter_upwards [hnull_transfer hq₀_ae] with η hη
        by_cases hf0 : f₀ η = 0
        · simp [hf0]
        · have hqq : q η = q₀ η := by
            by_contra hne
            exact hη hf0 hne
          change q₀ η * f₀ η = q η * f₀ η
          rw [hqq]
      · rw [hasFiniteIntegral_iff_norm]
        have hhq := hq.2
        rw [hasFiniteIntegral_iff_norm] at hhq
        convert hhq using 1
        refine lintegral_congr fun η => ?_
        rw [hae_norm η]
    have hcont_rhs : Continuous (fun q : Lp ℂ 1 μ.variation => ∫ η, q η * f₀ η ∂unitCircleMeasure) := by
      let L_lin : Lp ℂ 1 μ.variation →ₗ[ℂ] ℂ :=
        { toFun := fun q : Lp ℂ 1 μ.variation => ∫ η, q η * f₀ η ∂unitCircleMeasure
          map_add' := fun q₁ q₂ => by
            have hcongr : (fun η => (q₁ + q₂ : Lp ℂ 1 μ.variation) η * f₀ η) =ᵐ[unitCircleMeasure]
                fun η => q₁ η * f₀ η + q₂ η * f₀ η := by
              filter_upwards [hnull_transfer (Lp.coeFn_add q₁ q₂)] with η hη
              by_cases hf0 : f₀ η = 0
              · simp [hf0]
              · have heq : (q₁ + q₂ : Lp ℂ 1 μ.variation) η = q₁ η + q₂ η := by
                  by_contra hne
                  exact hη hf0 hne
                rw [heq, add_mul]
            rw [integral_congr_ae hcongr,
              integral_add (hmul_int _ (memLp_one_iff_integrable.mp (Lp.memLp q₁)))
                (hmul_int _ (memLp_one_iff_integrable.mp (Lp.memLp q₂)))]
          map_smul' := fun c q => by
            have hcongr : (fun η => (c • q : Lp ℂ 1 μ.variation) η * f₀ η) =ᵐ[unitCircleMeasure]
                fun η => c * (q η * f₀ η) := by
              filter_upwards [hnull_transfer (Lp.coeFn_smul c q)] with η hη
              by_cases hf0 : f₀ η = 0
              · simp [hf0]
              · have heq : (c • q : Lp ℂ 1 μ.variation) η = c * q η := by
                  by_contra hne
                  exact hη hf0 hne
                rw [heq, mul_assoc]
            simp only [RingHom.id_apply, smul_eq_mul]
            rw [integral_congr_ae hcongr, integral_const_mul] }
      refine ContinuousLinearMap.continuous (L_lin.mkContinuous 1 fun q => ?_)
      rw [one_mul]
      let qf : UnitCircle → ℂ := q
      have hqf_int : Integrable qf μ.variation :=
        memLp_one_iff_integrable.mp (Lp.memLp q)
      have hvar_nn : μ.variation = unitCircleMeasure.withDensity (fun η => (‖f₀ η‖₊ : ℝ≥0∞)) :=
        hvar_eq
      have hvar_int : (∫ η, ‖qf η * f₀ η‖ ∂unitCircleMeasure) = ∫ η, ‖qf η‖ ∂μ.variation := by
        rw [hvar_nn, integral_withDensity_eq_integral_smul hf₀_meas.nnnorm]
        refine integral_congr_ae (ae_of_all _ fun η => ?_)
        simp [NNReal.smul_def, mul_comm]
      calc ‖∫ η, qf η * f₀ η ∂unitCircleMeasure‖
          ≤ ∫ η, ‖qf η * f₀ η‖ ∂unitCircleMeasure := norm_integral_le_integral_norm _
        _ = ∫ η, ‖qf η‖ ∂μ.variation := hvar_int
        _ = ‖q‖ := by
            rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm hqf_int.aestronglyMeasurable,
              integral_norm_eq_lintegral_enorm hqf_int.aestronglyMeasurable]
    refine Integrable.induction
      (P := fun q => (∫ᵛ η, q η ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) =
        ∫ η, q η * f₀ η ∂unitCircleMeasure)
      ?_ ?_ ?_ ?_ hk_var
    · intro c E hE _
      rw [VectorMeasure.integral_indicator_const c hE]
      change c * μ E = _
      rw [show μ E = ∫ η in E, f₀ η ∂unitCircleMeasure from withDensityᵥ_apply hf₀_int hE]
      have hind : (fun η => E.indicator (fun _ => c) η * f₀ η) =
          E.indicator (fun η => c * f₀ η) := by
        ext η; by_cases hη : η ∈ E <;> simp [hη]
      rw [hind, integral_indicator hE, integral_const_mul]
    · intro q₁ q₂ _ hq₁ hq₂ he₁ he₂
      rw [VectorMeasure.integral_add hq₁ hq₂, he₁, he₂]
      simp only [Pi.add_apply, add_mul]
      exact (integral_add (hmul_int q₁ hq₁) (hmul_int q₂ hq₂)).symm
    · exact isClosed_eq VectorMeasure.continuous_integral hcont_rhs
    · intro q₁ q₂ hq12 _ he₁
      rw [← VectorMeasure.integral_congr_ae hq12, he₁]
      refine integral_congr_ae ?_
      filter_upwards [hnull_transfer hq12] with η hη
      by_cases hf0 : f₀ η = 0
      · simp [hf0]
      · have heq : q₁ η = q₂ η := by
          by_contra hne
          exact hη hf0 hne
        rw [heq]
  rw [hgen g hK_int_var]
  refine integral_congr_ae (ae_of_all _ fun η => ?_)
  simp [g, Complex.real_smul]

/-- Rational decomposition of the Poisson kernel on `T` (`z ∈ ball 0 1`, `w ∈ T`):
`(P(z, w) : ℂ) = 1 + z * (w - z)⁻¹ + conj z * (conj w - conj z)⁻¹`. -/
theorem poissonKernel_unitCircle_eq_cauchy_sum {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1)
    (η : UnitCircle) :
    ((_root_.poissonKernel 0 z (η : ℂ) : ℝ) : ℂ) =
      1 + z * ((η : ℂ) - z)⁻¹ + conj z * (conj (η : ℂ) - conj z)⁻¹ := by
  have hz_lt : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
  let w : ℂ := η
  have hw_norm : ‖w‖ = 1 := norm_unitCircle η
  have hwz_ne : w - z ≠ 0 := by
    intro h0
    have heq : w = z := sub_eq_zero.mp h0
    rw [← heq, hw_norm] at hz_lt
    exact lt_irrefl 1 hz_lt
  have hcwz_ne : conj w - conj z ≠ 0 := by
    rw [← map_sub]
    intro h0
    exact hwz_ne ((RingHom.injective (starRingEnd ℂ)) (by simpa using h0))
  have hden : (w - z) * (conj w - conj z) = ((‖w - z‖ ^ 2 : ℝ) : ℂ) := by
    rw [← map_sub, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hnum : (w - z) * (conj w - conj z) + z * (conj w - conj z) + conj z * (w - z) =
      ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
    calc (w - z) * (conj w - conj z) + z * (conj w - conj z) + conj z * (w - z)
        = w * conj w - z * conj z := by ring
      _ = 1 - ((‖z‖ ^ 2 : ℝ) : ℂ) := by
          rw [unitCircle_mul_conj η, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      _ = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hrhs : 1 + z * (w - z)⁻¹ + conj z * (conj w - conj z)⁻¹ =
      ((w - z) * (conj w - conj z) + z * (conj w - conj z) + conj z * (w - z)) /
        ((w - z) * (conj w - conj z)) := by
    field_simp [hwz_ne, hcwz_ne]
  rw [hrhs, hnum, hden]
  dsimp [_root_.poissonKernel, w]
  simp only [sub_zero, norm_unitCircle, one_pow]
  push_cast
  rfl

private theorem differentiableOn_ball_of_powerSeries {g : ℂ → ℂ} {c : ℕ → ℂ} {C : ℝ}
    (hsum : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasSum (fun n : ℕ => c n * z ^ n) (g z))
    (hbound : ∀ n : ℕ, ‖c n‖ ≤ C) :
    DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1) := by
  have hC0 : 0 ≤ C := (norm_nonneg (c 0)).trans (hbound 0)
  intro z₀ hz₀
  have hz₀_lt : ‖z₀‖ < 1 := by simpa [Metric.mem_ball] using hz₀
  let r : ℝ := (‖z₀‖ + 1) / 2
  have hr_pos : 0 < r := by dsimp [r]; linarith [norm_nonneg z₀]
  have hr_lt1 : r < 1 := by dsimp [r]; linarith
  have hz₀_in : z₀ ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [r]; linarith
  have hgeom : Summable (fun n : ℕ => C * r ^ n) :=
    (summable_geometric_of_lt_one hr_pos.le hr_lt1).mul_left C
  have hterm_le : ∀ n : ℕ, ∀ z ∈ Metric.ball (0 : ℂ) r, ‖c n * z ^ n‖ ≤ C * r ^ n := by
    intro n z hz
    have hzr : ‖z‖ ≤ r := (by simpa [Metric.mem_ball] using hz : ‖z‖ < r).le
    rw [norm_mul, norm_pow]
    exact mul_le_mul (hbound n) (pow_le_pow_left₀ (norm_nonneg z) hzr n) (pow_nonneg (norm_nonneg z) n) hC0
  have hunif_tsum : TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N, c n * z ^ n)
      (fun z => ∑' n : ℕ, c n * z ^ n) atTop (Metric.ball (0 : ℂ) r) :=
    tendstoUniformlyOn_tsum_nat hgeom hterm_le
  have hunif : TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N, c n * z ^ n)
      g atTop (Metric.ball (0 : ℂ) r) := by
    refine hunif_tsum.congr_right fun z hz => ?_
    have hz1 : z ∈ Metric.ball (0 : ℂ) 1 := Metric.ball_subset_ball hr_lt1.le hz
    exact (hsum z hz1).tsum_eq
  have hpoly_diff : ∀ N : ℕ, DifferentiableOn ℂ (fun z : ℂ => ∑ n ∈ Finset.range N, c n * z ^ n)
      (Metric.ball (0 : ℂ) r) := by
    intro N
    exact fun z _ => (DifferentiableAt.fun_sum fun n _ =>
      (differentiableAt_const (c n)).mul (differentiableAt_id.pow n)).differentiableWithinAt
  have hg_diff_r : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) r) :=
    hunif.tendstoLocallyUniformlyOn.differentiableOn (Eventually.of_forall hpoly_diff)
      Metric.isOpen_ball
  exact (hg_diff_r.differentiableAt (Metric.isOpen_ball.mem_nhds hz₀_in)).differentiableWithinAt

private theorem differentiableAt_conj_comp_conj {G : ℂ → ℂ} {z : ℂ}
    (hd : DifferentiableAt ℂ G (conj z)) :
    DifferentiableAt ℂ (fun w => conj (G (conj w))) z := by
  refine HasDerivAt.differentiableAt (f' := conj (deriv G (conj z))) ?_
  rw [RudinRCA.Chapter10.hasDerivAt_iff_difference_quotient]
  have hd_lim := (RudinRCA.Chapter10.hasDerivAt_iff_difference_quotient.mp hd.hasDerivAt)
  have hconj_nhds : Tendsto (conj : ℂ → ℂ) (𝓝[≠] z) (𝓝[≠] (conj z)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨(Complex.continuous_conj.tendsto z).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw h0
    exact hw ((RingHom.injective (starRingEnd ℂ)) h0)
  have hcomp := (Complex.continuous_conj.tendsto (deriv G (conj z))).comp (hd_lim.comp hconj_nhds)
  refine hcomp.congr' (Eventually.of_forall fun w => ?_)
  dsimp only [Function.comp_apply]
  rw [map_div₀, map_sub, map_sub, starRingEnd_self_apply, starRingEnd_self_apply]

theorem isFiniteMeasure_complexMeasure_variation {X : Type*} [MeasurableSpace X]
    (μ : ComplexMeasure X) : IsFiniteMeasure μ.variation where
  measure_univ_lt_top := by
    have hle : μ.variation ≤ μ.re.totalVariation + μ.im.totalVariation := by
      apply VectorMeasure.variation_le_of_forall_enorm_le
      intro E _
      have h12 : ‖μ E‖ ≤ μ.re.totalVariation.real E + μ.im.totalVariation.real E := by
        calc ‖μ E‖ ≤ |(μ E).re| + |(μ E).im| := Complex.norm_le_abs_re_add_abs_im _
          _ ≤ μ.re.totalVariation.real E + μ.im.totalVariation.real E := by
            have h₁ := μ.re.norm_le_totalVariation E
            have h₂ := μ.im.norm_le_totalVariation E
            change ‖(μ E).re‖ ≤ _ at h₁
            change ‖(μ E).im‖ ≤ _ at h₂
            rw [Real.norm_eq_abs] at h₁ h₂
            exact add_le_add h₁ h₂
      calc ‖μ E‖ₑ = ENNReal.ofReal ‖μ E‖ := (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (μ.re.totalVariation.real E + μ.im.totalVariation.real E) :=
          ENNReal.ofReal_le_ofReal h12
        _ = (μ.re.totalVariation + μ.im.totalVariation) E := by
          rw [ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg]
          simp only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _), Measure.add_apply]
    exact lt_of_le_of_lt (hle Set.univ) (measure_lt_top _ _)

/-- 11.17 (Harmonicity of `P[dμ]`): for every complex Borel measure `μ` on `T`, `poissonMeasureIntegral μ`
is harmonic on `U = ball 0 1` in both Rudin's 11.3 sense and Mathlib's `HarmonicOnNhd` sense. -/
theorem harmonicOn_poissonMeasureIntegral (μ : ComplexMeasure UnitCircle) :
    HarmonicOn (poissonMeasureIntegral μ) (Metric.ball (0 : ℂ) 1) ∧
    InnerProductSpace.HarmonicOnNhd (poissonMeasureIntegral μ) (Metric.ball (0 : ℂ) 1) := by
  have : IsFiniteMeasure μ.variation := isFiniteMeasure_complexMeasure_variation μ
  -- Use Theorem 10.7 on `φ₁(η) = η.1` and `φ₂(η) = conj η.1`
  let φ₁ : UnitCircle → ℂ := fun η => (η : ℂ)
  let φ₂ : UnitCircle → ℂ := fun η => conj (η : ℂ)
  have hdisj₁ : Disjoint (Metric.ball (0 : ℂ) 1) (Set.range φ₁) := by
    rw [Set.disjoint_left]
    rintro z hz ⟨η, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at hz
    have hlt : ‖(η : ℂ)‖ < 1 := hz
    rw [norm_unitCircle] at hlt
    exact lt_irrefl 1 hlt
  have hdisj₂ : Disjoint (Metric.ball (0 : ℂ) 1) (Set.range φ₂) := by
    rw [Set.disjoint_left]
    rintro z hz ⟨η, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at hz
    have hlt : ‖conj (η : ℂ)‖ < 1 := hz
    rw [RCLike.norm_conj, norm_unitCircle] at hlt
    exact lt_irrefl 1 hlt
  have hC₁ := (RudinRCA.Chapter10.theorem10_7 (φ := φ₁) μ continuous_subtype_val.measurable
    Metric.isOpen_ball hdisj₁).2 0 1 zero_lt_one Subset.rfl
  have hC₂ := (RudinRCA.Chapter10.theorem10_7 (φ := φ₂) μ
    (Complex.continuous_conj.comp continuous_subtype_val).measurable
    Metric.isOpen_ball hdisj₂).2 0 1 zero_lt_one Subset.rfl
  have hdiff₁ : DifferentiableOn ℂ (RudinRCA.Chapter10.cauchyTransform μ φ₁)
      (Metric.ball (0 : ℂ) 1) :=
    differentiableOn_ball_of_powerSeries
      (fun z hz => by simpa using hC₁.1 z hz)
      (fun n => by simpa using hC₁.2 n)
  have hdiff₂ : DifferentiableOn ℂ (RudinRCA.Chapter10.cauchyTransform μ φ₂)
      (Metric.ball (0 : ℂ) 1) :=
    differentiableOn_ball_of_powerSeries
      (fun z hz => by simpa using hC₂.1 z hz)
      (fun n => by simpa using hC₂.2 n)
  let F₁ : ℂ → ℂ := fun z => μ Set.univ + z * RudinRCA.Chapter10.cauchyTransform μ φ₁ z
  let G₂ : ℂ → ℂ := fun w => w * RudinRCA.Chapter10.cauchyTransform μ φ₂ w
  let H₂ : ℂ → ℂ := fun z => conj (G₂ (conj z))
  have hF₁_holo : DifferentiableOn ℂ F₁ (Metric.ball (0 : ℂ) 1) :=
    (differentiableOn_const _).add (differentiableOn_id.mul hdiff₁)
  have hG₂_holo : DifferentiableOn ℂ G₂ (Metric.ball (0 : ℂ) 1) :=
    differentiableOn_id.mul hdiff₂
  have hH₂_holo : DifferentiableOn ℂ H₂ (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hcz : conj z ∈ Metric.ball (0 : ℂ) 1 := by simpa [Metric.mem_ball] using hz
    exact (differentiableAt_conj_comp_conj
      (hG₂_holo.differentiableAt (Metric.isOpen_ball.mem_nhds hcz))).differentiableWithinAt
  have hF₁_harm : InnerProductSpace.HarmonicOnNhd F₁ (Metric.ball (0 : ℂ) 1) :=
    fun z hz => (hF₁_holo.analyticAt (Metric.isOpen_ball.mem_nhds hz)).harmonicAt
  have hH₂_harm : InnerProductSpace.HarmonicOnNhd H₂ (Metric.ball (0 : ℂ) 1) :=
    fun z hz => (hH₂_holo.analyticAt (Metric.isOpen_ball.mem_nhds hz)).harmonicAt
  let S : ℂ → ℂ := fun z => F₁ z + Complex.conjCLE.toContinuousLinearMap (H₂ z)
  have hS_harm : InnerProductSpace.HarmonicOnNhd S (Metric.ball (0 : ℂ) 1) :=
    fun z hz => (hF₁_harm z hz).add ((hH₂_harm z hz).comp_CLM Complex.conjCLE.toContinuousLinearMap)
  -- Show `poissonMeasureIntegral μ z = S z` for all `z ∈ ball 0 1`
  obtain ⟨h, hm, hn, hi, hr⟩ := RudinRCA.Chapter06.theorem_6_12 μ
  have heq : ∀ z ∈ Metric.ball (0 : ℂ) 1, poissonMeasureIntegral μ z = S z := by
    intro z hz
    have hz_lt : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
    have hInt_polar : ∀ g : UnitCircle → ℂ, Continuous g →
        RudinRCA.Chapter10.complexMeasureIntegral μ g = ∫ η, g η * h η ∂μ.variation := by
      intro g hg
      exact RudinRCA.Chapter06.vectorIntegral_eq_polar μ h hm hn hi hr
        (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    have hq₁_cont : Continuous (fun η : UnitCircle => ((η : ℂ) - z)⁻¹) := by
      refine (continuous_subtype_val.sub continuous_const).inv₀ fun η h0 => ?_
      have : ‖(η : ℂ)‖ = ‖z‖ := congrArg norm (sub_eq_zero.mp h0)
      rw [norm_unitCircle] at this
      exact hz_lt.ne' this
    have hq₂_cont : Continuous (fun η : UnitCircle => (conj (η : ℂ) - conj z)⁻¹) := by
      refine ((Complex.continuous_conj.comp continuous_subtype_val).sub continuous_const).inv₀
        fun η h0 => ?_
      have : ‖conj (η : ℂ)‖ = ‖conj z‖ := congrArg norm (sub_eq_zero.mp h0)
      rw [RCLike.norm_conj, RCLike.norm_conj, norm_unitCircle] at this
      exact hz_lt.ne' this
    have hP_cont : Continuous (fun η : UnitCircle => (_root_.poissonKernel 0 z (η : ℂ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_poissonKernel_unitCircle hz)
    unfold poissonMeasureIntegral
    rw [hInt_polar _ hP_cont]
    have hInt1 : μ Set.univ = ∫ η : UnitCircle, (1 : ℂ) * h η ∂μ.variation := by
      calc μ Set.univ = (μ.variation.withDensityᵥ h) Set.univ := by rw [hr]
        _ = ∫ η in Set.univ, h η ∂μ.variation := withDensityᵥ_apply hi MeasurableSet.univ
        _ = ∫ η : UnitCircle, (1 : ℂ) * h η ∂μ.variation := by simp
    have hIntC1 : RudinRCA.Chapter10.cauchyTransform μ φ₁ z =
        ∫ η : UnitCircle, ((η : ℂ) - z)⁻¹ * h η ∂μ.variation :=
      hInt_polar _ hq₁_cont
    have hIntC2 : RudinRCA.Chapter10.cauchyTransform μ φ₂ (conj z) =
        ∫ η : UnitCircle, (conj (η : ℂ) - conj z)⁻¹ * h η ∂μ.variation :=
      hInt_polar _ hq₂_cont
    have hS_z : S z =
        μ Set.univ + z * RudinRCA.Chapter10.cauchyTransform μ φ₁ z +
          conj z * RudinRCA.Chapter10.cauchyTransform μ φ₂ (conj z) := by
      dsimp [S, F₁, H₂, G₂]
      simp [add_assoc]
    let i1 : UnitCircle → ℂ := fun η => (1 : ℂ) * h η
    let i2 : UnitCircle → ℂ := fun η => z * (((η : ℂ) - z)⁻¹ * h η)
    let i3 : UnitCircle → ℂ := fun η => conj z * ((conj (η : ℂ) - conj z)⁻¹ * h η)
    have hi1 : Integrable i1 μ.variation := by simpa [i1] using hi
    have hi2 : Integrable i2 μ.variation :=
      ((hq₁_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mul_bdd
        hm.aestronglyMeasurable (ae_of_all _ fun x => (hn x).le)).const_mul z
    have hi3 : Integrable i3 μ.variation :=
      ((hq₂_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mul_bdd
        hm.aestronglyMeasurable (ae_of_all _ fun x => (hn x).le)).const_mul (conj z)
    have hS_int : S z = (∫ η, i1 η ∂μ.variation) + (∫ η, i2 η ∂μ.variation) +
        (∫ η, i3 η ∂μ.variation) := by
      rw [hS_z, hInt1, hIntC1, hIntC2, ← integral_const_mul, ← integral_const_mul]
    calc (∫ η : UnitCircle, (_root_.poissonKernel 0 z (η : ℂ) : ℂ) * h η ∂μ.variation)
        = ∫ η : UnitCircle, ((i1 η + i2 η) + i3 η) ∂μ.variation := by
          refine integral_congr_ae (ae_of_all _ fun η => ?_)
          dsimp [i1, i2, i3]
          rw [poissonKernel_unitCircle_eq_cauchy_sum hz η]
          ring
      _ = (∫ η : UnitCircle, (i1 η + i2 η) ∂μ.variation) + ∫ η : UnitCircle, i3 η ∂μ.variation :=
          integral_add (hi1.add hi2) hi3
      _ = (∫ η : UnitCircle, i1 η ∂μ.variation) + (∫ η : UnitCircle, i2 η ∂μ.variation) +
            ∫ η : UnitCircle, i3 η ∂μ.variation := by
          rw [integral_add hi1 hi2]
      _ = S z := hS_int.symm
  have hmath : InnerProductSpace.HarmonicOnNhd (poissonMeasureIntegral μ) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hev : S =ᶠ[𝓝 z] poissonMeasureIntegral μ :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Metric.ball 0 1, Metric.isOpen_ball.mem_nhds hz, fun w hw => (heq w hw).symm⟩
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).mp (hS_harm z hz)
  exact ⟨harmonicOn_of_mathlib hmath, hmath⟩

/-- 11.17 (Complete package, Rudin p. 240): for every complex Borel measure `μ` on `T = UnitCircle`,
`u = P[dμ] = poissonMeasureIntegral μ` is harmonic in `U = ball 0 1`, and for every `0 ≤ r < 1`:
`‖u_r‖₁ = (1 / 2π) ∫_{-π}^π |u(r e^{iθ})| dθ ≤ ‖μ‖ = |μ|(T)`. -/
theorem theorem11_17 (μ : ComplexMeasure UnitCircle) :
    HarmonicOn (poissonMeasureIntegral μ) (Metric.ball (0 : ℂ) 1) ∧
    InnerProductSpace.HarmonicOnNhd (poissonMeasureIntegral μ) (Metric.ball (0 : ℂ) 1) ∧
    ∀ {r : ℝ}, 0 ≤ r → r < 1 →
      (∫ ζ : UnitCircle, ‖unitRadialRestriction (poissonMeasureIntegral μ) r ζ‖ ∂unitCircleMeasure) =
        (2 * Real.pi)⁻¹ * ∫ θ in (-Real.pi)..Real.pi,
          ‖poissonMeasureIntegral μ ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ∧
      (∫ ζ : UnitCircle, ‖unitRadialRestriction (poissonMeasureIntegral μ) r ζ‖ ∂unitCircleMeasure) ≤
        μ.variation.real Set.univ ∧
      eLpNorm (unitRadialRestriction (poissonMeasureIntegral μ) r) 1 unitCircleMeasure ≤
        μ.variation Set.univ := by
  obtain ⟨hharm_weak, hharm_math⟩ := harmonicOn_poissonMeasureIntegral μ
  obtain ⟨h, hm, hn, hi, hr_pol⟩ := RudinRCA.Chapter06.theorem_6_12 μ
  have : IsFiniteMeasure μ.variation := isFiniteMeasure_complexMeasure_variation μ
  refine ⟨hharm_weak, hharm_math, fun {r} hr0 hr1 => ?_⟩
  let ur := unitRadialRestriction (poissonMeasureIntegral μ) r
  have hur_cont : Continuous ur :=
    (hharm_weak.continuousOn.comp_continuous
      (continuous_const.mul continuous_subtype_val)
      (fun ζ => radial_mem_ball_unitCircle hr0 hr1 ζ))
  have hang : (∫ ζ : UnitCircle, ‖ur ζ‖ ∂unitCircleMeasure) =
      (2 * Real.pi)⁻¹ * ∫ θ in (-Real.pi)..Real.pi,
        ‖poissonMeasureIntegral μ ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ := by
    simpa [ur, unitRadialRestriction, smul_eq_mul] using
      (integral_unitCircleMeasure_eq_interval (fun ζ : UnitCircle => ‖ur ζ‖)).1
  have hpt : ∀ ζ : UnitCircle,
      ‖ur ζ‖ₑ ≤ ∫⁻ η : UnitCircle,
        ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ)) ∂μ.variation := by
    intro ζ
    have hz := radial_mem_ball_unitCircle hr0 hr1 ζ
    have hP_cont : Continuous (fun η : UnitCircle => (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_poissonKernel_unitCircle hz)
    have hpol := RudinRCA.Chapter06.vectorIntegral_eq_polar μ h hm hn hi hr_pol
      (hP_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    unfold ur unitRadialRestriction poissonMeasureIntegral RudinRCA.Chapter10.complexMeasureIntegral
    rw [hpol]
    calc ‖∫ η : UnitCircle, (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ) : ℂ) * h η ∂μ.variation‖ₑ
        ≤ ∫⁻ η : UnitCircle, ‖(_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ) : ℂ) * h η‖ₑ ∂μ.variation :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ η : UnitCircle,
            ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ)) ∂μ.variation := by
          refine lintegral_congr fun η => ?_
          rw [enorm_mul, ← ofReal_norm (h η), hn η, ENNReal.ofReal_one, mul_one,
            ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (poissonKernel_unitCircle_nonneg hz η)]
  have hprod_meas : AEMeasurable
      (Function.uncurry fun ζ η : UnitCircle =>
        ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ)))
      (unitCircleMeasure.prod μ.variation) :=
    (continuous_poissonKernel_unitCircle_pair hr0 hr1).measurable.ennreal_ofReal.aemeasurable
  have heLp : eLpNorm ur 1 unitCircleMeasure ≤ μ.variation Set.univ := by
    rw [eLpNorm_one_eq_lintegral_enorm hur_cont.aestronglyMeasurable]
    calc (∫⁻ ζ : UnitCircle, ‖ur ζ‖ₑ ∂unitCircleMeasure)
        ≤ ∫⁻ ζ : UnitCircle, ∫⁻ η : UnitCircle,
            ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ))
              ∂μ.variation ∂unitCircleMeasure := lintegral_mono hpt
      _ = ∫⁻ η : UnitCircle, ∫⁻ ζ : UnitCircle,
            ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ))
              ∂unitCircleMeasure ∂μ.variation := lintegral_lintegral_swap hprod_meas
      _ = ∫⁻ _η : UnitCircle, (1 : ℝ≥0∞) ∂μ.variation := by
          refine lintegral_congr fun η => ?_
          have hsymm : (fun ζ : UnitCircle =>
              ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ))) =
              fun ζ : UnitCircle =>
                ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (η : ℂ)) (ζ : ℂ)) := by
            ext ζ
            rw [poissonKernel_unitCircle_radial_symm r ζ η]
          rw [hsymm, lintegral_poissonKernel_unitCircle (radial_mem_ball_unitCircle hr0 hr1 η)]
      _ = μ.variation Set.univ := by simp
  have hreal_le : (∫ ζ : UnitCircle, ‖ur ζ‖ ∂unitCircleMeasure) ≤ μ.variation.real Set.univ := by
    have hur_int : Integrable (fun ζ : UnitCircle => ‖ur ζ‖) unitCircleMeasure :=
      hur_cont.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hofReal : ENNReal.ofReal (∫ ζ : UnitCircle, ‖ur ζ‖ ∂unitCircleMeasure) =
        eLpNorm ur 1 unitCircleMeasure := by
      rw [ofReal_integral_eq_lintegral_ofReal hur_int (ae_of_all _ fun _ => norm_nonneg _),
        eLpNorm_one_eq_lintegral_enorm hur_cont.aestronglyMeasurable]
      refine lintegral_congr fun ζ => ?_
      exact ofReal_norm (ur ζ)
    rw [measureReal_def, ← ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _), hofReal]
    exact ENNReal.toReal_mono (measure_ne_top _ _) heLp
  exact ⟨hang, hreal_le, heLp⟩

end Nodes11_16_and_11_17


/-! ### Stage 3 Block 2: Approach Regions, Maximal Functions, Differentiation on `T`, and Nodes 11.18–11.20 -/

section Node11_18

/-- Base point `1 ∈ T = UnitCircle`. -/
def unitCircleOne : UnitCircle :=
  ⟨(1 : ℂ), by simp⟩

@[simp]
theorem coe_unitCircleOne : ((unitCircleOne : UnitCircle) : ℂ) = 1 :=
  rfl

/-- 11.18 (Definition, Rudin p. 240): nontangential approach region `Ω_α` with vertex `1`
(`0 < α < 1`), defined as the intersection with `U = Metric.ball 0 1` of the convex hull of
`D(0; α) ∪ {1}`. -/
def approachRegionBase (α : ℝ) : Set ℂ :=
  convexHull ℝ (Metric.ball (0 : ℂ) α ∪ {(1 : ℂ)}) ∩ Metric.ball (0 : ℂ) 1

/-- 11.18 (Definition, Rudin p. 241): rotated nontangential approach region `e^{it} Ω_α`
with vertex `ζ ∈ T = UnitCircle`. -/
def approachRegion (α : ℝ) (ζ : UnitCircle) : Set ℂ :=
  convexHull ℝ (Metric.ball (0 : ℂ) α ∪ {(ζ : ℂ)}) ∩ Metric.ball (0 : ℂ) 1

@[simp]
theorem approachRegion_one (α : ℝ) :
    approachRegion α unitCircleOne = approachRegionBase α :=
  rfl

theorem approachRegion_subset_ball (α : ℝ) (ζ : UnitCircle) :
    approachRegion α ζ ⊆ Metric.ball (0 : ℂ) 1 :=
  Set.inter_subset_right

theorem approachRegionBase_subset_ball (α : ℝ) :
    approachRegionBase α ⊆ Metric.ball (0 : ℂ) 1 :=
  Set.inter_subset_right

theorem convex_approachRegion (α : ℝ) (ζ : UnitCircle) :
    Convex ℝ (approachRegion α ζ) :=
  (convex_convexHull ℝ _).inter (convex_ball 0 1)

theorem convex_approachRegionBase (α : ℝ) :
    Convex ℝ (approachRegionBase α) :=
  convex_approachRegion α unitCircleOne

/-- Explicit union-of-balls representation of `approachRegion α ζ` (`0 < α < 1`):
`e^{it} Ω_α = ⋃_{0 ≤ t < 1} D(t ζ; (1 - t) α)`. -/
theorem approachRegion_eq_iUnion_ball {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (ζ : UnitCircle) :
    approachRegion α ζ =
      ⋃ t ∈ Set.Ico (0 : ℝ) 1, Metric.ball ((t : ℂ) * (ζ : ℂ)) ((1 - t) * α) := by
  let w : ℂ := ζ
  have hw_norm : ‖w‖ = 1 := norm_unitCircle ζ
  let S : Set ℂ := Metric.ball (0 : ℂ) α ∪ {w}
  let B_union : Set ℂ := ⋃ t ∈ Set.Ico (0 : ℝ) 1, Metric.ball ((t : ℂ) * w) ((1 - t) * α)
  let C : Set ℂ := {w} ∪ B_union
  have hB_sub_ball : B_union ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    obtain ⟨t, ⟨ht0, ht1⟩, hzt⟩ := Set.mem_iUnion₂.mp hz
    rw [Metric.mem_ball, dist_eq_norm] at hzt
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖z‖ = ‖(z - (t : ℂ) * w) + (t : ℂ) * w‖ := by ring_nf
      _ ≤ ‖z - (t : ℂ) * w‖ + ‖(t : ℂ) * w‖ := norm_add_le _ _
      _ < (1 - t) * α + t := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, hw_norm, mul_one]
          linarith
      _ < (1 - t) * 1 + t := by nlinarith
      _ = 1 := by ring
  have hB_sub_hull : B_union ⊆ convexHull ℝ S := by
    intro z hz
    obtain ⟨t, ⟨ht0, ht1⟩, hzt⟩ := Set.mem_iUnion₂.mp hz
    have h1mt : 0 < 1 - t := sub_pos.mpr ht1
    let u : ℂ := ((1 - t)⁻¹ : ℝ) • (z - (t : ℂ) * w)
    have hu_ball : u ∈ Metric.ball (0 : ℂ) α := by
      rw [Metric.mem_ball, dist_zero_right]
      dsimp only [u]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h1mt), inv_mul_lt_iff₀ h1mt]
      simpa only [Metric.mem_ball, dist_eq_norm] using hzt
    have hu_hull : u ∈ convexHull ℝ S := subset_convexHull ℝ S (Or.inl hu_ball)
    have hw_hull : w ∈ convexHull ℝ S := subset_convexHull ℝ S (Or.inr rfl)
    have hcomb : (1 - t) • u + t • w = z := by
      dsimp only [u]
      rw [smul_smul, mul_inv_cancel₀ h1mt.ne', one_smul, Complex.real_smul, sub_add_cancel]
    exact hcomb ▸ (convex_convexHull ℝ S) hu_hull hw_hull h1mt.le ht0 (sub_add_cancel 1 t)
  have hC_param : ∀ z ∈ C, ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ u ∈ Metric.ball (0 : ℂ) α,
      z = (1 - t) • u + t • w := by
    intro z hz
    rcases hz with rfl | hzB
    · exact ⟨1, ⟨zero_le_one, le_rfl⟩, 0, Metric.mem_ball_self hα0, by simp⟩
    · obtain ⟨t, ⟨ht0, ht1⟩, hzt⟩ := Set.mem_iUnion₂.mp hzB
      have h1mt : 0 < 1 - t := sub_pos.mpr ht1
      let u : ℂ := ((1 - t)⁻¹ : ℝ) • (z - (t : ℂ) * w)
      have hu_ball : u ∈ Metric.ball (0 : ℂ) α := by
        rw [Metric.mem_ball, dist_zero_right]
        dsimp only [u]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h1mt), inv_mul_lt_iff₀ h1mt]
        simpa only [Metric.mem_ball, dist_eq_norm] using hzt
      refine ⟨t, ⟨ht0, ht1.le⟩, u, hu_ball, ?_⟩
      dsimp only [u]
      rw [smul_smul, mul_inv_cancel₀ h1mt.ne', one_smul, Complex.real_smul, sub_add_cancel]
  have hC_conv : Convex ℝ C := by
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    obtain ⟨t₁, ⟨ht₁0, ht₁1⟩, u₁, hu₁, rfl⟩ := hC_param z₁ hz₁
    obtain ⟨t₂, ⟨ht₂0, ht₂1⟩, u₂, hu₂, rfl⟩ := hC_param z₂ hz₂
    let t : ℝ := a * t₁ + b * t₂
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 := by nlinarith
    rcases ht1.eq_or_lt with ht_eq | ht_lt
    · left
      have h1mt_sum : a * (1 - t₁) + b * (1 - t₂) = 0 := by dsimp only [t] at ht_eq; linarith
      have ha0 : a * (1 - t₁) = 0 := by
        nlinarith [mul_nonneg ha (sub_nonneg.mpr ht₁1), mul_nonneg hb (sub_nonneg.mpr ht₂1)]
      have hb0 : b * (1 - t₂) = 0 := by linarith
      have hcomb : a • ((1 - t₁) • u₁ + t₁ • w) + b • ((1 - t₂) • u₂ + t₂ • w) =
          (a * (1 - t₁)) • u₁ + (b * (1 - t₂)) • u₂ + t • w := by
        simp only [Complex.real_smul, t]
        push_cast
        ring
      rw [hcomb, ha0, hb0, ht_eq, zero_smul, zero_smul, zero_add, zero_add, one_smul]
      rfl
    · right
      refine Set.mem_iUnion₂.mpr ⟨t, ⟨ht0, ht_lt⟩, ?_⟩
      have h1mt : 0 < 1 - t := sub_pos.mpr ht_lt
      let c₁ : ℝ := a * (1 - t₁) / (1 - t)
      let c₂ : ℝ := b * (1 - t₂) / (1 - t)
      have hc₁ : 0 ≤ c₁ := div_nonneg (mul_nonneg ha (sub_nonneg.mpr ht₁1)) h1mt.le
      have hc₂ : 0 ≤ c₂ := div_nonneg (mul_nonneg hb (sub_nonneg.mpr ht₂1)) h1mt.le
      have hc12 : c₁ + c₂ = 1 := by
        dsimp only [c₁, c₂]
        rw [← add_div, div_eq_one_iff_eq h1mt.ne']
        dsimp only [t]
        linarith
      have hu_mem : c₁ • u₁ + c₂ • u₂ ∈ Metric.ball (0 : ℂ) α :=
        (convex_ball (0 : ℂ) α) hu₁ hu₂ hc₁ hc₂ hc12
      have hlin : a • ((1 - t₁) • u₁ + t₁ • w) + b • ((1 - t₂) • u₂ + t₂ • w) - (t : ℂ) * w =
          (1 - t) • (c₁ • u₁ + c₂ • u₂) := by
        have hc1_mul : (1 - t) * c₁ = a * (1 - t₁) := mul_div_cancel₀ _ h1mt.ne'
        have hc2_mul : (1 - t) * c₂ = b * (1 - t₂) := mul_div_cancel₀ _ h1mt.ne'
        conv_rhs => rw [smul_add, smul_smul, smul_smul, hc1_mul, hc2_mul]
        simp only [Complex.real_smul, t]
        push_cast
        ring
      rw [Metric.mem_ball, dist_eq_norm, hlin, norm_smul, Real.norm_eq_abs, abs_of_pos h1mt]
      have hu_norm : ‖c₁ • u₁ + c₂ • u₂‖ < α := by simpa [Metric.mem_ball] using hu_mem
      exact mul_lt_mul_of_pos_left hu_norm h1mt
  have hS_sub_C : S ⊆ C := by
    rintro z (hz | rfl)
    · right
      refine Set.mem_iUnion₂.mpr ⟨0, ⟨le_rfl, zero_lt_one⟩, ?_⟩
      simpa using hz
    · exact Or.inl rfl
  have hhull_sub_C : convexHull ℝ S ⊆ C := convexHull_min hS_sub_C hC_conv
  ext z
  constructor
  · rintro ⟨hz_hull, hz_ball⟩
    rcases hhull_sub_C hz_hull with rfl | hzB
    · exfalso
      have : ‖w‖ < 1 := by simpa [Metric.mem_ball] using hz_ball
      linarith
    · exact hzB
  · intro hzB
    exact ⟨hB_sub_hull hzB, hB_sub_ball hzB⟩

theorem isOpen_approachRegion {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (ζ : UnitCircle) :
    IsOpen (approachRegion α ζ) := by
  rw [approachRegion_eq_iUnion_ball hα0 hα1 ζ]
  exact isOpen_biUnion fun _ _ => Metric.isOpen_ball

theorem isOpen_approachRegionBase {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IsOpen (approachRegionBase α) :=
  isOpen_approachRegion hα0 hα1 unitCircleOne

theorem ball_subset_approachRegion {α : ℝ} (hα1 : α ≤ 1) (ζ : UnitCircle) :
    Metric.ball (0 : ℂ) α ⊆ approachRegion α ζ := fun _z hz =>
  ⟨subset_convexHull ℝ _ (Or.inl hz), Metric.ball_subset_ball hα1 hz⟩

theorem radial_mem_approachRegion {α r : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ζ : UnitCircle) :
    (r : ℂ) * (ζ : ℂ) ∈ approachRegion α ζ := by
  rw [approachRegion_eq_iUnion_ball hα0 hα1 ζ]
  exact Set.mem_iUnion₂.mpr ⟨r, ⟨hr0, hr1⟩, Metric.mem_ball_self (mul_pos (sub_pos.mpr hr1) hα0)⟩

/-- Rotation formula `e^{it} Ω_α = ((ζ : ℂ) * ·) '' Ω_α`. -/
theorem approachRegion_eq_image_mul {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (ζ : UnitCircle) :
    approachRegion α ζ = (fun z : ℂ => (ζ : ℂ) * z) '' approachRegionBase α := by
  rw [approachRegion_eq_iUnion_ball hα0 hα1 ζ,
    ← approachRegion_one, approachRegion_eq_iUnion_ball hα0 hα1 unitCircleOne]
  ext z
  constructor
  · intro hz
    obtain ⟨t, ht, hzt⟩ := Set.mem_iUnion₂.mp hz
    refine ⟨conj (ζ : ℂ) * z, Set.mem_iUnion₂.mpr ⟨t, ht, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, coe_unitCircleOne, mul_one]
      have heq : conj (ζ : ℂ) * z - (t : ℂ) = conj (ζ : ℂ) * (z - (t : ℂ) * (ζ : ℂ)) := by
        calc conj (ζ : ℂ) * z - (t : ℂ)
            = conj (ζ : ℂ) * z - (t : ℂ) * ((ζ : ℂ) * conj (ζ : ℂ)) := by
                rw [unitCircle_mul_conj ζ, mul_one]
          _ = conj (ζ : ℂ) * (z - (t : ℂ) * (ζ : ℂ)) := by ring
      rw [heq, norm_mul, RCLike.norm_conj, norm_unitCircle, one_mul]
      simpa only [Metric.mem_ball, dist_eq_norm] using hzt
    · calc (ζ : ℂ) * (conj (ζ : ℂ) * z) = ((ζ : ℂ) * conj (ζ : ℂ)) * z := by ring
        _ = z := by rw [unitCircle_mul_conj ζ, one_mul]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨t, ht, hwt⟩ := Set.mem_iUnion₂.mp hw
    refine Set.mem_iUnion₂.mpr ⟨t, ht, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : (ζ : ℂ) * w - (t : ℂ) * (ζ : ℂ) = (ζ : ℂ) * (w - (t : ℂ) * 1) := by ring
    rw [heq, norm_mul, norm_unitCircle, one_mul]
    simpa only [Metric.mem_ball, dist_eq_norm, coe_unitCircleOne] using hwt

/-- Rudin 11.18 literal union-of-segments description: `Ω_α` is the union of `D(0; α)` and the
(open / punctured-at-`1`) line segments from `1` to points of `D(0; α)`. -/
theorem approachRegionBase_eq_ball_union_segments {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    approachRegionBase α =
      Metric.ball (0 : ℂ) α ∪ ⋃ w ∈ Metric.ball (0 : ℂ) α, openSegment ℝ (1 : ℂ) w ∧
    approachRegionBase α =
      (Metric.ball (0 : ℂ) α ∪ ⋃ w ∈ Metric.ball (0 : ℂ) α, segment ℝ (1 : ℂ) w) \ {(1 : ℂ)} := by
  have h1 : approachRegionBase α =
      Metric.ball (0 : ℂ) α ∪ ⋃ w ∈ Metric.ball (0 : ℂ) α, openSegment ℝ (1 : ℂ) w := by
    rw [← approachRegion_one, approachRegion_eq_iUnion_ball hα0 hα1 unitCircleOne]
    ext z
    constructor
    · intro hz
      obtain ⟨t, ⟨ht0, ht1⟩, hzt⟩ := Set.mem_iUnion₂.mp hz
      rcases ht0.eq_or_lt with rfl | ht_pos
      · left
        simpa using hzt
      · right
        have h1mt : 0 < 1 - t := sub_pos.mpr ht1
        let w : ℂ := ((1 - t)⁻¹ : ℝ) • (z - (t : ℂ))
        have hw : w ∈ Metric.ball (0 : ℂ) α := by
          rw [Metric.mem_ball, dist_zero_right]
          dsimp only [w]
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h1mt), inv_mul_lt_iff₀ h1mt]
          simpa only [Metric.mem_ball, dist_eq_norm, coe_unitCircleOne, mul_one] using hzt
        refine Set.mem_iUnion₂.mpr ⟨w, hw, t, 1 - t, ht_pos, h1mt, add_sub_cancel _ _, ?_⟩
        dsimp only [w]
        rw [smul_smul, mul_inv_cancel₀ h1mt.ne', one_smul, Complex.real_smul]
        ring
    · rintro (hz | hz)
      · refine Set.mem_iUnion₂.mpr ⟨0, ⟨le_rfl, zero_lt_one⟩, ?_⟩
        simpa using hz
      · obtain ⟨w, hw, a, b, ha, hb, hab, rfl⟩ := Set.mem_iUnion₂.mp hz
        refine Set.mem_iUnion₂.mpr ⟨a, ⟨ha.le, by linarith⟩, ?_⟩
        have hb_eq : b = 1 - a := by linarith
        rw [Metric.mem_ball, dist_eq_norm, coe_unitCircleOne, mul_one, hb_eq]
        have heq : a • (1 : ℂ) + (1 - a) • w - (a : ℂ) = (1 - a) • w := by
          simp only [Complex.real_smul]
          ring
        rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
        have hw_lt : ‖w‖ < α := by simpa [Metric.mem_ball] using hw
        exact mul_lt_mul_of_pos_left hw_lt (by linarith)
  refine ⟨h1, ?_⟩
  rw [h1]
  ext z
  constructor
  · intro hz
    have hz_ne : z ≠ (1 : ℂ) := by
      intro rfl
      have hball : (1 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := approachRegionBase_subset_ball α (h1 ▸ hz)
      simp [Metric.mem_ball] at hball
    refine ⟨?_, hz_ne⟩
    rcases hz with hz_b | hz_seg
    · exact Or.inl hz_b
    · right
      obtain ⟨w, hw, hz_open⟩ := Set.mem_iUnion₂.mp hz_seg
      exact Set.mem_iUnion₂.mpr ⟨w, hw, openSegment_subset_segment ℝ _ _ hz_open⟩
  · rintro ⟨hz_or, hz_ne⟩
    rcases hz_or with hz_b | hz_seg
    · exact Or.inl hz_b
    · obtain ⟨w, hw, a, b, ha, hb, hab, rfl⟩ := Set.mem_iUnion₂.mp hz_seg
      rcases ha.eq_or_lt with rfl | ha_pos
      · have hb1 : b = 1 := by linarith
        subst hb1
        simpa using Or.inl hw
      · rcases hb.eq_or_lt with rfl | hb_pos
        · have ha1 : a = 1 := by linarith
          subst ha1
          exact (hz_ne (by simp)).elim
        · exact Or.inr (Set.mem_iUnion₂.mpr ⟨w, hw, a, b, ha_pos, hb_pos, hab, rfl⟩)

/-- The vertex `ζ` lies in the topological boundary (`frontier`) of `approachRegion α ζ`. -/
theorem vertex_mem_frontier_approachRegion {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (ζ : UnitCircle) :
    (ζ : ℂ) ∈ frontier (approachRegion α ζ) := by
  rw [(isOpen_approachRegion hα0 hα1 ζ).frontier_eq]
  refine ⟨Metric.mem_closure_iff.mpr fun ε hε => ?_, fun hmem => ?_⟩
  · let r : ℝ := max 0 (1 - ε / 2)
    have hr0 : 0 ≤ r := le_max_left _ _
    have hr1 : r < 1 := max_lt zero_lt_one (by linarith)
    refine ⟨(r : ℂ) * (ζ : ℂ), radial_mem_approachRegion hα0 hα1 hr0 hr1 ζ, ?_⟩
    rw [dist_eq_norm]
    have heq : (ζ : ℂ) - (r : ℂ) * (ζ : ℂ) = ((1 - r : ℝ) : ℂ) * (ζ : ℂ) := by
      push_cast; ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hr1),
      norm_unitCircle, mul_one]
    have hle : 1 - ε / 2 ≤ r := le_max_right _ _
    linarith
  · have hlt : ‖(ζ : ℂ)‖ < 1 := by
      simpa [Metric.mem_ball] using approachRegion_subset_ball α ζ hmem
    rw [norm_unitCircle] at hlt
    exact lt_irrefl 1 hlt

/-- Minimality characterization (Rudin 11.18, p. 240): `Ω_α` is the smallest convex open set in `ℂ`
that contains `D(0; α)` and has `1` in its boundary (`frontier`). -/
theorem approachRegionBase_minimal {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {V : Set ℂ} (hV_conv : Convex ℝ V) (_hV_open : IsOpen V)
    (hball : Metric.ball (0 : ℂ) α ⊆ V) (hfront : (1 : ℂ) ∈ frontier V) :
    approachRegionBase α ⊆ V := by
  have h1_clos : (1 : ℂ) ∈ closure V := hfront.1
  rw [← approachRegion_one, approachRegion_eq_iUnion_ball hα0 hα1 unitCircleOne]
  intro z hz
  obtain ⟨t, ⟨ht0, ht1⟩, hzt⟩ := Set.mem_iUnion₂.mp hz
  rcases ht0.eq_or_lt with rfl | ht_pos
  · exact hball (by simpa using hzt)
  · have h1mt : 0 < 1 - t := sub_pos.mpr ht1
    let u : ℂ := ((1 - t)⁻¹ : ℝ) • (z - (t : ℂ))
    have hu_norm : ‖u‖ < α := by
      dsimp only [u]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h1mt), inv_mul_lt_iff₀ h1mt]
      simpa only [Metric.mem_ball, dist_eq_norm, coe_unitCircleOne, mul_one] using hzt
    have hru : 0 < α - ‖u‖ := sub_pos.mpr hu_norm
    obtain ⟨v, hvV, hv_dist⟩ := Metric.mem_closure_iff.mp h1_clos
      (((1 - t) / t) * (α - ‖u‖)) (by positivity)
    let u' : ℂ := u + (t / (1 - t)) • ((1 : ℂ) - v)
    have hu'_ball : u' ∈ Metric.ball (0 : ℂ) α := by
      rw [Metric.mem_ball, dist_zero_right]
      have hdiff : ‖(t / (1 - t)) • ((1 : ℂ) - v)‖ < α - ‖u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), ← dist_eq_norm]
        calc (t / (1 - t)) * dist 1 v
            < (t / (1 - t)) * (((1 - t) / t) * (α - ‖u‖)) :=
              mul_lt_mul_of_pos_left hv_dist (by positivity)
          _ = α - ‖u‖ := by field_simp
      calc ‖u'‖ ≤ ‖u‖ + ‖(t / (1 - t)) • ((1 : ℂ) - v)‖ := norm_add_le _ _
        _ < ‖u‖ + (α - ‖u‖) := by linarith
        _ = α := add_sub_cancel _ _
    have hcomb : (1 - t) • u' + t • v = z := by
      dsimp only [u', u]
      have hmul1 : (1 - t) * (1 - t)⁻¹ = 1 := mul_inv_cancel₀ h1mt.ne'
      have hmul2 : (1 - t) * (t / (1 - t)) = t := mul_div_cancel₀ t h1mt.ne'
      rw [smul_add, smul_smul, hmul1, one_smul, smul_smul, hmul2]
      simp only [Complex.real_smul]
      ring
    exact hcomb ▸ hV_conv (hball hu'_ball) hvV h1mt.le ht_pos.le (sub_add_cancel 1 t)

/-- Opening-angle cone property at `1` (`α = sin θ`, Rudin 11.18, p. 240):
every `z ∈ Ω_α` lies strictly inside the bisected sector `0 < Re(1 - z)` and
`|Im(1 - z)| < α ‖1 - z‖`. -/
theorem approachRegionBase_angle_cone {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {z : ℂ} (hz : z ∈ approachRegionBase α) :
    0 < (1 - z).re ∧ |(1 - z).im| < α * ‖1 - z‖ := by
  have hz_lt1 : ‖z‖ < 1 := by simpa [Metric.mem_ball] using approachRegionBase_subset_ball α hz
  have hre : 0 < (1 - z).re := by
    have := Complex.re_le_norm z
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  refine ⟨hre, ?_⟩
  rw [← approachRegion_one, approachRegion_eq_iUnion_ball hα0 hα1 unitCircleOne] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, hzt⟩ := Set.mem_iUnion₂.mp hz
  have h1mt : 0 < 1 - t := sub_pos.mpr ht1
  let u : ℂ := ((1 - t)⁻¹ : ℝ) • (z - (t : ℂ))
  have hu_norm : ‖u‖ < α := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h1mt), inv_mul_lt_iff₀ h1mt]
    simpa only [Metric.mem_ball, dist_eq_norm, coe_unitCircleOne, mul_one] using hzt
  have hz_eq : 1 - z = (1 - t) • (1 - u) := by
    dsimp only [u]
    simp only [Complex.real_smul]
    push_cast
    have hne : (1 - t : ℂ) ≠ 0 := by exact_mod_cast h1mt.ne'
    field_simp [hne]
    ring
  let v : ℂ := 1 - u
  have hv_ne : v ≠ 0 := by
    intro hv0
    have : u = 1 := by dsimp only [v] at hv0; exact (sub_eq_zero.mp hv0).symm
    rw [this, norm_one] at hu_norm
    linarith
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  -- Exact identity `v.im^2 + (v.re - ‖v‖^2)^2 = ‖v‖^2 * ‖u‖^2`
  have hid : v.im ^ 2 + (v.re - (v.re ^ 2 + v.im ^ 2)) ^ 2 =
      (v.re ^ 2 + v.im ^ 2) * ((1 - v.re) ^ 2 + v.im ^ 2) := by ring
  have hnorm_v_sq : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hnorm_u_sq : ‖u‖ ^ 2 = (1 - v.re) ^ 2 + v.im ^ 2 := by
    have hu_v : u = 1 - v := by dsimp only [v]; ring
    rw [← Complex.normSq_eq_norm_sq, hu_v, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    ring
  have him_sq_lt : v.im ^ 2 < (α * ‖v‖) ^ 2 := by
    calc v.im ^ 2 ≤ v.im ^ 2 + (v.re - (v.re ^ 2 + v.im ^ 2)) ^ 2 :=
          le_add_of_nonneg_right (sq_nonneg _)
      _ = ‖v‖ ^ 2 * ‖u‖ ^ 2 := by rw [hid, ← hnorm_v_sq, ← hnorm_u_sq]
      _ < ‖v‖ ^ 2 * α ^ 2 := by
          refine mul_lt_mul_of_pos_left ?_ (sq_pos_of_pos hv_pos)
          nlinarith [norm_nonneg u]
      _ = (α * ‖v‖) ^ 2 := by ring
  have him_lt : |v.im| < α * ‖v‖ := by
    have habs : |v.im| < |α * ‖v‖| := sq_lt_sq.mp him_sq_lt
    rwa [abs_of_pos (mul_pos hα0 hv_pos)] at habs
  rw [hz_eq, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, abs_mul, abs_of_pos h1mt, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos h1mt]
  nlinarith

/-- Monotonicity: `Ω_α` expands when `α` increases. -/
theorem approachRegion_mono {α₁ α₂ : ℝ} (h12 : α₁ ≤ α₂) (ζ : UnitCircle) :
    approachRegion α₁ ζ ⊆ approachRegion α₂ ζ := fun _z hz =>
  ⟨convexHull_mono (Set.union_subset_union_left _ (Metric.ball_subset_ball h12)) hz.1, hz.2⟩

/-- Union: `⋃_{0 < α < 1} e^{it} Ω_α = U = Metric.ball 0 1`. -/
theorem iUnion_approachRegion (ζ : UnitCircle) :
    (⋃ α ∈ Set.Ioo (0 : ℝ) 1, approachRegion α ζ) = Metric.ball (0 : ℂ) 1 := by
  ext z
  constructor
  · intro hz
    obtain ⟨α, _, hzα⟩ := Set.mem_iUnion₂.mp hz
    exact approachRegion_subset_ball α ζ hzα
  · intro hz
    have hz_lt : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
    let α : ℝ := (‖z‖ + 1) / 2
    have hα_mem : α ∈ Set.Ioo (0 : ℝ) 1 := ⟨by positivity, by dsimp only [α]; linarith⟩
    refine Set.mem_iUnion₂.mpr ⟨α, hα_mem, ball_subset_approachRegion hα_mem.2.le ζ ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    dsimp only [α]
    linarith

/-- Intersection: `⋂_{0 < α < 1} Ω_α = [0, 1)` (Rudin 11.18, p. 241). -/
theorem iInter_approachRegionBase :
    (⋂ α ∈ Set.Ioo (0 : ℝ) 1, approachRegionBase α) =
      (fun r : ℝ => (r : ℂ)) '' Set.Ico 0 1 := by
  ext z
  constructor
  · intro hz
    have hz_half : z ∈ approachRegionBase (1 / 2) :=
      Set.mem_iInter₂.mp hz (1 / 2) ⟨by norm_num, by norm_num⟩
    have hz_lt1 : ‖z‖ < 1 := by
      simpa [Metric.mem_ball] using approachRegionBase_subset_ball (1 / 2) hz_half
    have him0 : z.im = 0 := by
      by_contra hne
      have habs_pos : 0 < |z.im| := abs_pos.mpr hne
      let α : ℝ := min (1 / 2) (|z.im| / (2 * (‖1 - z‖ + 1)))
      have hα0 : 0 < α := lt_min (by norm_num) (by positivity)
      have hα1 : α < 1 := (min_le_left _ _).trans_lt (by norm_num)
      have hcone := (approachRegionBase_angle_cone hα0 hα1
        (Set.mem_iInter₂.mp hz α ⟨hα0, hα1⟩)).2
      simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at hcone
      have hle : α ≤ |z.im| / (2 * (‖1 - z‖ + 1)) := min_le_right _ _
      have hmul : α * ‖1 - z‖ < |z.im| := by
        calc α * ‖1 - z‖
            ≤ (|z.im| / (2 * (‖1 - z‖ + 1))) * ‖1 - z‖ :=
              mul_le_mul_of_nonneg_right hle (norm_nonneg _)
          _ < (|z.im| / (2 * (‖1 - z‖ + 1))) * (2 * (‖1 - z‖ + 1)) := by
              refine mul_lt_mul_of_pos_left ?_ (by positivity)
              linarith [norm_nonneg (1 - z)]
          _ = |z.im| := div_mul_cancel₀ _ (by positivity)
      linarith
    have hre_nn : 0 ≤ z.re := by
      by_contra hneg
      push Not at hneg
      let α : ℝ := min (1 / 2) (-z.re / 2)
      have hα0 : 0 < α := lt_min (by norm_num) (by linarith)
      have hα1 : α < 1 := (min_le_left _ _).trans_lt (by norm_num)
      have hzα := Set.mem_iInter₂.mp hz α ⟨hα0, hα1⟩
      rw [← approachRegion_one, approachRegion_eq_iUnion_ball hα0 hα1 unitCircleOne] at hzα
      obtain ⟨t, ⟨ht0, ht1⟩, hzt⟩ := Set.mem_iUnion₂.mp hzα
      rw [Metric.mem_ball, dist_eq_norm, coe_unitCircleOne, mul_one] at hzt
      have hre_diff : |(z - (t : ℂ)).re| ≤ ‖z - (t : ℂ)‖ := Complex.abs_re_le_norm _
      simp only [Complex.sub_re, Complex.ofReal_re] at hre_diff
      have h1 : t - z.re ≤ |z.re - t| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      have h2 : (1 - t) * α ≤ α := by nlinarith
      have h3 : α ≤ -z.re / 2 := min_le_right _ _
      linarith
    have hre_lt1 : z.re < 1 := (Complex.re_le_norm z).trans_lt hz_lt1
    refine ⟨z.re, ⟨hre_nn, hre_lt1⟩, ?_⟩
    apply Complex.ext
    · simp
    · simp [him0]
  · rintro ⟨r, ⟨hr0, hr1⟩, rfl⟩
    refine Set.mem_iInter₂.mpr fun α ⟨hα0, hα1⟩ => ?_
    simpa using radial_mem_approachRegion hα0 hα1 hr0 hr1 unitCircleOne

/-- Chord-to-radial ratio bound on `e^{it} Ω_α` (`0 < α < 1`):
`‖z - ζ‖ ≤ ((1 + α) / (1 - α)) * (1 - ‖z‖)`. -/
theorem norm_sub_vertex_le_of_mem_approachRegion {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ζ : UnitCircle} {z : ℂ} (hz : z ∈ approachRegion α ζ) :
    ‖z - (ζ : ℂ)‖ ≤ ((1 + α) / (1 - α)) * (1 - ‖z‖) := by
  rw [approachRegion_eq_iUnion_ball hα0 hα1 ζ] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, hzt⟩ := Set.mem_iUnion₂.mp hz
  rw [Metric.mem_ball, dist_eq_norm] at hzt
  let w : ℂ := ζ
  have hw_norm : ‖w‖ = 1 := norm_unitCircle ζ
  have h1mα : 0 < 1 - α := sub_pos.mpr hα1
  have htw_sub : ‖(t : ℂ) * w - w‖ = 1 - t := by
    have heq : (t : ℂ) * w - w = ((t - 1 : ℝ) : ℂ) * w := by push_cast; ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, hw_norm, mul_one,
      abs_of_neg (sub_neg.mpr ht1)]
    ring
  have hz_sub_w : ‖z - w‖ < (1 + α) * (1 - t) := by
    calc ‖z - w‖ = ‖(z - (t : ℂ) * w) + ((t : ℂ) * w - w)‖ := by ring_nf
      _ ≤ ‖z - (t : ℂ) * w‖ + ‖(t : ℂ) * w - w‖ := norm_add_le _ _
      _ < (1 - t) * α + (1 - t) := by rw [htw_sub]; linarith
      _ = (1 + α) * (1 - t) := by ring
  have hz_norm : ‖z‖ < t + (1 - t) * α := by
    calc ‖z‖ = ‖(z - (t : ℂ) * w) + (t : ℂ) * w‖ := by ring_nf
      _ ≤ ‖z - (t : ℂ) * w‖ + ‖(t : ℂ) * w‖ := norm_add_le _ _
      _ < (1 - t) * α + t := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, hw_norm, mul_one]
          linarith
      _ = t + (1 - t) * α := by ring
  have h1mz : (1 - α) * (1 - t) < 1 - ‖z‖ := by linarith
  have h1mt_le : 1 - t ≤ (1 - ‖z‖) / (1 - α) := (le_div_iff₀ h1mα).mpr (by linarith)
  calc ‖z - w‖ ≤ (1 + α) * (1 - t) := hz_sub_w.le
    _ ≤ (1 + α) * ((1 - ‖z‖) / (1 - α)) := mul_le_mul_of_nonneg_left h1mt_le (by linarith)
    _ = ((1 + α) / (1 - α)) * (1 - ‖z‖) := by ring

/-- 11.18 (Approach Regions, Rudin pp. 240–241): complete summary of properties of `Ω_α`
and `e^{it} Ω_α`. -/
theorem theorem11_18 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (approachRegionBase α =
      Metric.ball (0 : ℂ) α ∪ ⋃ w ∈ Metric.ball (0 : ℂ) α, openSegment ℝ (1 : ℂ) w) ∧
    (Convex ℝ (approachRegionBase α) ∧ IsOpen (approachRegionBase α) ∧
      Metric.ball (0 : ℂ) α ⊆ approachRegionBase α ∧
      (1 : ℂ) ∈ frontier (approachRegionBase α) ∧
      ∀ V : Set ℂ, Convex ℝ V → IsOpen V → Metric.ball (0 : ℂ) α ⊆ V →
        (1 : ℂ) ∈ frontier V → approachRegionBase α ⊆ V) ∧
    (∀ z ∈ approachRegionBase α, 0 < (1 - z).re ∧ |(1 - z).im| < α * ‖1 - z‖) ∧
    (∀ {β : ℝ}, α ≤ β → ∀ ζ : UnitCircle, approachRegion α ζ ⊆ approachRegion β ζ) ∧
    (∀ ζ : UnitCircle,
      approachRegion α ζ = (fun z : ℂ => (ζ : ℂ) * z) '' approachRegionBase α ∧
      (⋃ γ ∈ Set.Ioo (0 : ℝ) 1, approachRegion γ ζ) = Metric.ball (0 : ℂ) 1) ∧
    ((⋂ γ ∈ Set.Ioo (0 : ℝ) 1, approachRegionBase γ) = (fun r : ℝ => (r : ℂ)) '' Set.Ico 0 1) :=
  ⟨(approachRegionBase_eq_ball_union_segments hα0 hα1).1,
   ⟨convex_approachRegionBase α, isOpen_approachRegionBase hα0 hα1,
    ball_subset_approachRegion hα1.le unitCircleOne,
    vertex_mem_frontier_approachRegion hα0 hα1 unitCircleOne,
    fun _V hVc hVo hb hf => approachRegionBase_minimal hα0 hα1 hVc hVo hb hf⟩,
   fun _z hz => approachRegionBase_angle_cone hα0 hα1 hz,
   fun hαβ ζ => approachRegion_mono hαβ ζ,
   fun ζ => ⟨approachRegion_eq_image_mul hα0 hα1 ζ, iUnion_approachRegion ζ⟩,
   iInter_approachRegionBase⟩

end Node11_18

section Node11_19

/-- 11.19(1) (Definition, Rudin p. 241): nontangential maximal function
`(N_α u)(ζ) = sup { ‖u(z)‖ₑ : z ∈ ζ Ω_α } : [0, ∞]`. -/
def nontangentialMaximal (α : ℝ) (u : ℂ → ℂ) (ζ : UnitCircle) : ℝ≥0∞ :=
  ⨆ z ∈ approachRegion α ζ, ‖u z‖ₑ

/-- 11.19(2) (Definition, Rudin p. 241): radial maximal function
`(M_rad u)(ζ) = sup { ‖u(r ζ)‖ₑ : 0 ≤ r < 1 } : [0, ∞]`. -/
def radialMaximal (u : ℂ → ℂ) (ζ : UnitCircle) : ℝ≥0∞ :=
  ⨆ r ∈ Set.Ico (0 : ℝ) 1, ‖u ((r : ℂ) * (ζ : ℂ))‖ₑ

theorem isOpen_setOf_mem_approachRegion {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (z : ℂ) :
    IsOpen {ζ : UnitCircle | z ∈ approachRegion α ζ} := by
  have heq : {ζ : UnitCircle | z ∈ approachRegion α ζ} =
      ⋃ t ∈ Set.Ico (0 : ℝ) 1,
        {ζ : UnitCircle | dist z ((t : ℂ) * (ζ : ℂ)) < (1 - t) * α} := by
    ext ζ
    simp [approachRegion_eq_iUnion_ball hα0 hα1 ζ, Metric.mem_ball]
  rw [heq]
  exact isOpen_biUnion fun t _ =>
    isOpen_lt (continuous_const.dist (continuous_const.mul continuous_subtype_val)) continuous_const

theorem lowerSemicontinuous_nontangentialMaximal {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (u : ℂ → ℂ) :
    LowerSemicontinuous (nontangentialMaximal α u) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro y
  have heq : nontangentialMaximal α u ⁻¹' Set.Ioi y =
      ⋃ z : ℂ, ⋃ (_ : y < ‖u z‖ₑ), {ζ : UnitCircle | z ∈ approachRegion α ζ} := by
    ext ζ
    simp only [Set.mem_preimage, Set.mem_Ioi, nontangentialMaximal, lt_iSup_iff,
      Set.mem_iUnion, Set.mem_ofPred_eq]
    tauto
  rw [heq]
  exact isOpen_iUnion fun z => isOpen_iUnion fun _ => isOpen_setOf_mem_approachRegion hα0 hα1 z

theorem isClosed_nontangentialMaximal_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (u : ℂ → ℂ) (c : ℝ≥0∞) :
    IsClosed {ζ : UnitCircle | nontangentialMaximal α u ζ ≤ c} :=
  lowerSemicontinuous_iff_isClosed_preimage.mp
    (lowerSemicontinuous_nontangentialMaximal hα0 hα1 u) c

theorem measurable_nontangentialMaximal {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (u : ℂ → ℂ) :
    Measurable (nontangentialMaximal α u) :=
  (lowerSemicontinuous_nontangentialMaximal hα0 hα1 u).measurable

theorem lowerSemicontinuous_radialMaximal {u : ℂ → ℂ}
    (hu : ContinuousOn u (Metric.ball (0 : ℂ) 1)) :
    LowerSemicontinuous (radialMaximal u) := by
  unfold radialMaximal
  refine lowerSemicontinuous_biSup fun r hr => ?_
  have hcont : Continuous (fun ζ : UnitCircle => u ((r : ℂ) * (ζ : ℂ))) :=
    hu.comp_continuous (continuous_const.mul continuous_subtype_val)
      (fun ζ => radial_mem_ball_unitCircle hr.1 hr.2 ζ)
  exact hcont.enorm.lowerSemicontinuous

theorem isClosed_radialMaximal_le {u : ℂ → ℂ}
    (hu : ContinuousOn u (Metric.ball (0 : ℂ) 1)) (c : ℝ≥0∞) :
    IsClosed {ζ : UnitCircle | radialMaximal u ζ ≤ c} :=
  lowerSemicontinuous_iff_isClosed_preimage.mp (lowerSemicontinuous_radialMaximal hu) c

theorem measurable_radialMaximal {u : ℂ → ℂ}
    (hu : ContinuousOn u (Metric.ball (0 : ℂ) 1)) :
    Measurable (radialMaximal u) :=
  (lowerSemicontinuous_radialMaximal hu).measurable

theorem radialMaximal_le_nontangentialMaximal {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (u : ℂ → ℂ) (ζ : UnitCircle) :
    radialMaximal u ζ ≤ nontangentialMaximal α u ζ := by
  unfold radialMaximal nontangentialMaximal
  refine iSup₂_le fun r hr => ?_
  exact le_iSup₂_of_le ((r : ℂ) * (ζ : ℂ)) (radial_mem_approachRegion hα0 hα1 hr.1 hr.2 ζ) le_rfl

theorem nontangentialMaximal_mono {α₁ α₂ : ℝ} (h12 : α₁ ≤ α₂)
    (u : ℂ → ℂ) (ζ : UnitCircle) :
    nontangentialMaximal α₁ u ζ ≤ nontangentialMaximal α₂ u ζ := by
  unfold nontangentialMaximal
  exact iSup_le_iSup_of_subset (approachRegion_mono h12 ζ)

/-- Open arc on `T = UnitCircle` centered at `ζ` of angular half-width `δ`
(equal to `∅` for `δ ≤ 0`, a proper open arc for `0 < δ ≤ π`, and all of `T = Set.univ`
for `δ > π`, matching Rudin 11.19, p. 241). -/
def openCircleArc (ζ : UnitCircle) (δ : ℝ) : Set UnitCircle :=
  {η : UnitCircle | ∃ s : ℝ, |s| < δ ∧ (η : ℂ) = (ζ : ℂ) * Complex.exp ((s : ℂ) * Complex.I)}

theorem mem_openCircleArc_self (ζ : UnitCircle) {δ : ℝ} (hδ : 0 < δ) :
    ζ ∈ openCircleArc ζ δ :=
  ⟨0, by simpa using hδ, by simp⟩

theorem openCircleArc_eq_empty (ζ : UnitCircle) {δ : ℝ} (hδ : δ ≤ 0) :
    openCircleArc ζ δ = ∅ := by
  ext η
  simp only [openCircleArc, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists,
    not_and]
  intro s hs _
  linarith [abs_nonneg s]

theorem openCircleArc_eq_univ (ζ : UnitCircle) {δ : ℝ} (hδ : Real.pi < δ) :
    openCircleArc ζ δ = Set.univ := by
  ext η
  simp only [openCircleArc, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  let w : ℂ := (η : ℂ) * conj (ζ : ℂ)
  have hw_norm : ‖w‖ = 1 := by
    dsimp only [w]
    rw [norm_mul, RCLike.norm_conj, norm_unitCircle, norm_unitCircle, mul_one]
  refine ⟨Complex.arg w, ?_, ?_⟩
  · have h1 := Complex.neg_pi_lt_arg w
    have h2 := Complex.arg_le_pi w
    rw [abs_lt]
    exact ⟨by linarith, by linarith⟩
  · have hexp : Complex.exp ((Complex.arg w : ℂ) * Complex.I) = w := by
      have h := Complex.norm_mul_exp_arg_mul_I w
      rwa [hw_norm, Complex.ofReal_one, one_mul] at h
    rw [hexp]
    dsimp only [w]
    calc (η : ℂ) = (η : ℂ) * ((ζ : ℂ) * conj (ζ : ℂ)) := by rw [unitCircle_mul_conj ζ, mul_one]
      _ = (ζ : ℂ) * ((η : ℂ) * conj (ζ : ℂ)) := by ring

theorem openCircleArc_mono (ζ : UnitCircle) {δ₁ δ₂ : ℝ} (h12 : δ₁ ≤ δ₂) :
    openCircleArc ζ δ₁ ⊆ openCircleArc ζ δ₂ := by
  rintro η ⟨s, hs, hη⟩
  exact ⟨s, hs.trans_le h12, hη⟩

theorem openCircleArc_rotate (ζ₀ ζ : UnitCircle) (δ : ℝ) :
    openCircleArc (unitCircleRotate ζ₀ ζ) δ = unitCircleRotate ζ₀ '' openCircleArc ζ δ := by
  ext η
  constructor
  · rintro ⟨s, hs, hη⟩
    refine ⟨(unitCircleRotate ζ₀).symm η, ⟨s, hs, ?_⟩, (unitCircleRotate ζ₀).apply_symm_apply η⟩
    change conj (ζ₀ : ℂ) * (η : ℂ) = (ζ : ℂ) * Complex.exp ((s : ℂ) * Complex.I)
    change (η : ℂ) = ((ζ₀ : ℂ) * (ζ : ℂ)) * Complex.exp ((s : ℂ) * Complex.I) at hη
    rw [hη]
    calc conj (ζ₀ : ℂ) * ((ζ₀ : ℂ) * (ζ : ℂ) * Complex.exp ((s : ℂ) * Complex.I))
        = ((ζ₀ : ℂ) * conj (ζ₀ : ℂ)) * (ζ : ℂ) * Complex.exp ((s : ℂ) * Complex.I) := by ring
      _ = (ζ : ℂ) * Complex.exp ((s : ℂ) * Complex.I) := by
          rw [unitCircle_mul_conj ζ₀, one_mul]
  · rintro ⟨ξ, ⟨s, hs, hξ⟩, rfl⟩
    refine ⟨s, hs, ?_⟩
    change (ζ₀ : ℂ) * (ξ : ℂ) = ((ζ₀ : ℂ) * (ζ : ℂ)) * Complex.exp ((s : ℂ) * Complex.I)
    rw [hξ, mul_assoc]

/-- Exact chordal-ball description of `openCircleArc ζ δ` for `0 < δ ≤ π`. -/
theorem mem_openCircleArc_iff_chordal {ζ η : UnitCircle} {δ : ℝ}
    (hδ0 : 0 < δ) (hδpi : δ ≤ Real.pi) :
    η ∈ openCircleArc ζ δ ↔ ‖(η : ℂ) - (ζ : ℂ)‖ ^ 2 < 2 * (1 - Real.cos δ) := by
  have hexp_sq : ∀ s : ℝ, ‖Complex.exp ((s : ℂ) * Complex.I) - 1‖ ^ 2 = 2 * (1 - Real.cos s) := by
    intro s
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sub_zero]
    have hcs := Real.sin_sq_add_cos_sq s
    nlinarith
  constructor
  · rintro ⟨s, hs, hη⟩
    have hnorm : ‖(η : ℂ) - (ζ : ℂ)‖ ^ 2 = 2 * (1 - Real.cos s) := by
      have hfac : (η : ℂ) - (ζ : ℂ) = (ζ : ℂ) * (Complex.exp ((s : ℂ) * Complex.I) - 1) := by
        rw [hη]; ring
      rw [hfac, norm_mul, norm_unitCircle, one_mul, hexp_sq s]
    rw [hnorm, ← Real.cos_abs s]
    have hcos_lt : Real.cos δ < Real.cos |s| :=
      Real.strictAntiOn_cos ⟨abs_nonneg s, hs.le.trans hδpi⟩ ⟨hδ0.le, hδpi⟩ hs
    linarith
  · intro hlt
    let w : ℂ := (η : ℂ) * conj (ζ : ℂ)
    have hw_norm : ‖w‖ = 1 := by
      dsimp only [w]
      rw [norm_mul, RCLike.norm_conj, norm_unitCircle, norm_unitCircle, mul_one]
    let s : ℝ := Complex.arg w
    have hexp_w : Complex.exp ((s : ℂ) * Complex.I) = w := by
      have h := Complex.norm_mul_exp_arg_mul_I w
      rwa [hw_norm, Complex.ofReal_one, one_mul] at h
    have hη_eq : (η : ℂ) = (ζ : ℂ) * Complex.exp ((s : ℂ) * Complex.I) := by
      rw [hexp_w]
      dsimp only [w]
      calc (η : ℂ) = (η : ℂ) * ((ζ : ℂ) * conj (ζ : ℂ)) := by rw [unitCircle_mul_conj ζ, mul_one]
        _ = (ζ : ℂ) * ((η : ℂ) * conj (ζ : ℂ)) := by ring
    have hnorm : ‖(η : ℂ) - (ζ : ℂ)‖ ^ 2 = 2 * (1 - Real.cos |s|) := by
      have hfac : (η : ℂ) - (ζ : ℂ) = (ζ : ℂ) * (Complex.exp ((s : ℂ) * Complex.I) - 1) := by
        rw [hη_eq]; ring
      rw [hfac, norm_mul, norm_unitCircle, one_mul, hexp_sq s, Real.cos_abs]
    rw [hnorm] at hlt
    have hcos_lt : Real.cos δ < Real.cos |s| := by linarith
    have hs_le_pi : |s| ≤ Real.pi := by
      dsimp only [s]
      rw [abs_le]
      exact ⟨(Complex.neg_pi_lt_arg w).le, Complex.arg_le_pi w⟩
    have hs_lt : |s| < δ := by
      by_contra hge
      push Not at hge
      have hle := Real.strictAntiOn_cos.antitoneOn ⟨hδ0.le, hδpi⟩ ⟨abs_nonneg s, hs_le_pi⟩ hge
      linarith
    exact ⟨s, hs_lt, hη_eq⟩

theorem isOpen_openCircleArc (ζ : UnitCircle) (δ : ℝ) :
    IsOpen (openCircleArc ζ δ) := by
  rcases le_or_gt δ 0 with hδ0 | hδ0
  · rw [openCircleArc_eq_empty ζ hδ0]
    exact isOpen_empty
  · rcases le_or_gt δ Real.pi with hδpi | hδpi
    · have heq : openCircleArc ζ δ =
          {η : UnitCircle | ‖(η : ℂ) - (ζ : ℂ)‖ ^ 2 < 2 * (1 - Real.cos δ)} := by
        ext η
        exact mem_openCircleArc_iff_chordal hδ0 hδpi
      rw [heq]
      exact isOpen_lt (((continuous_subtype_val.sub continuous_const).norm).pow 2) continuous_const
    · rw [openCircleArc_eq_univ ζ hδpi]
      exact isOpen_univ

/-- Chordal distance is bounded by angular half-width: `openCircleArc ζ δ ⊆ Metric.ball ζ δ`. -/
theorem dist_lt_of_mem_openCircleArc {ζ η : UnitCircle} {δ : ℝ}
    (hη : η ∈ openCircleArc ζ δ) :
    dist η ζ < δ := by
  obtain ⟨s, hs, hη_eq⟩ := hη
  rw [Subtype.dist_eq, dist_eq_norm]
  have hfac : (η : ℂ) - (ζ : ℂ) = (ζ : ℂ) * (Complex.exp ((s : ℂ) * Complex.I) - 1) := by
    rw [hη_eq]; ring
  rw [hfac, norm_mul, norm_unitCircle, one_mul]
  have hsq : ‖Complex.exp ((s : ℂ) * Complex.I) - 1‖ ^ 2 ≤ |s| ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sub_zero]
    have h1 : 1 - Real.cos s = 2 * Real.sin (s / 2) ^ 2 := by
      have h2 := Real.cos_two_mul (s / 2)
      have h3 := Real.sin_sq_add_cos_sq (s / 2)
      rw [show 2 * (s / 2) = s by ring] at h2
      linarith
    have hcs := Real.sin_sq_add_cos_sq s
    have hsin : Real.sin (s / 2) ^ 2 ≤ (s / 2) ^ 2 := by
      have habs : |Real.sin (s / 2)| ≤ |s / 2| := Real.abs_sin_le_abs
      nlinarith [sq_abs (Real.sin (s / 2)), sq_abs (s / 2), abs_nonneg (Real.sin (s / 2))]
    nlinarith [sq_abs s]
  have hle : ‖Complex.exp ((s : ℂ) * Complex.I) - 1‖ ≤ |s| := by
    nlinarith [norm_nonneg (Complex.exp ((s : ℂ) * Complex.I) - 1), abs_nonneg s]
  exact hle.trans_lt hs

/-- Vitali 3-arc inclusion: if `openCircleArc ζ₁ δ₁` meets `openCircleArc ζ₂ δ₂` and `δ₁ ≤ δ₂`,
then `openCircleArc ζ₁ δ₁ ⊆ openCircleArc ζ₂ (3 * δ₂)`. -/
theorem openCircleArc_subset_three_mul {ζ₁ ζ₂ : UnitCircle} {δ₁ δ₂ : ℝ}
    (h12 : δ₁ ≤ δ₂) (hne : (openCircleArc ζ₁ δ₁ ∩ openCircleArc ζ₂ δ₂).Nonempty) :
    openCircleArc ζ₁ δ₁ ⊆ openCircleArc ζ₂ (3 * δ₂) := by
  obtain ⟨ξ, ⟨s₁, hs₁, hξ₁⟩, ⟨s₂, hs₂, hξ₂⟩⟩ := hne
  rintro η ⟨s, hs, hη⟩
  refine ⟨s - s₁ + s₂, ?_, ?_⟩
  · have htri1 := abs_sub s s₁
    have htri2 := abs_add_le (s - s₁) s₂
    linarith
  · have hζ₁ : (ζ₁ : ℂ) = (ζ₂ : ℂ) * Complex.exp (((s₂ - s₁ : ℝ) : ℂ) * Complex.I) := by
      have heq : (ζ₁ : ℂ) * Complex.exp ((s₁ : ℂ) * Complex.I) =
          (ζ₂ : ℂ) * Complex.exp ((s₂ : ℂ) * Complex.I) := hξ₁.symm.trans hξ₂
      calc (ζ₁ : ℂ)
          = (ζ₁ : ℂ) * Complex.exp ((s₁ : ℂ) * Complex.I) *
              Complex.exp ((-s₁ : ℂ) * Complex.I) := by
                rw [mul_assoc, ← Complex.exp_add]
                simp
        _ = (ζ₂ : ℂ) * Complex.exp ((s₂ : ℂ) * Complex.I) *
              Complex.exp ((-s₁ : ℂ) * Complex.I) := by rw [heq]
        _ = (ζ₂ : ℂ) * Complex.exp (((s₂ - s₁ : ℝ) : ℂ) * Complex.I) := by
              rw [mul_assoc, ← Complex.exp_add]
              push_cast
              ring_nf
    rw [hη, hζ₁, mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf

/-- Normalized Lebesgue/Haar measure of an open circle arc (`δ > 0`):
`σ(openCircleArc ζ δ) = min (δ / π) 1`. -/
theorem unitCircleMeasure_openCircleArc (ζ : UnitCircle) {δ : ℝ} (hδ : 0 < δ) :
    unitCircleMeasure (openCircleArc ζ δ) = ENNReal.ofReal (min (δ / Real.pi) 1) := by
  -- Reduce to `ζ = 1` via rotation invariance of `unitCircleMeasure`
  have hrot : unitCircleMeasure (openCircleArc ζ δ) =
      unitCircleMeasure (openCircleArc unitCircleOne δ) := by
    have hζ : ζ = unitCircleRotate ζ unitCircleOne := by
      ext; simp [unitCircleRotate]
    conv_lhs => rw [hζ, openCircleArc_rotate]
    have hmap := (measurePreserving_unitCircleRotate ζ).map_eq
    conv_lhs => rw [← hmap]
    rw [Measure.map_apply (unitCircleRotate ζ).continuous.measurable
      ((unitCircleRotate ζ).isOpenMap _ (isOpen_openCircleArc _ _)).measurableSet]
    congr 1
    exact (unitCircleRotate ζ).injective.preimage_image _
  rw [hrot]
  rcases lt_or_ge Real.pi δ with hgt_pi | hle_pi
  · rw [openCircleArc_eq_univ unitCircleOne hgt_pi, unitCircleMeasure_univ]
    have hge1 : 1 ≤ δ / Real.pi := (one_le_div Real.pi_pos).mpr hgt_pi.le
    rw [min_eq_right hge1, ENNReal.ofReal_one]
  · have hle1 : δ / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr hle_pi
    rw [min_eq_left hle1]
    let A : Set UnitCircle := openCircleArc unitCircleOne δ
    have hA_meas : MeasurableSet A := (isOpen_openCircleArc unitCircleOne δ).measurableSet
    have hreal : unitCircleMeasure.real A = δ / Real.pi := by
      have h1 : (∫ η : UnitCircle, A.indicator (fun _ => (1 : ℝ)) η ∂unitCircleMeasure) =
          unitCircleMeasure.real A := by
        rw [integral_indicator hA_meas, setIntegral_const, smul_eq_mul, mul_one]
      rw [← h1, (integral_unitCircleMeasure_eq_interval _).1, smul_eq_mul]
      have hae_congr : ∀ t ∈ Set.Ioo (-Real.pi) Real.pi,
          A.indicator (fun _ => (1 : ℝ)) (fourierToUnitCircle (t : RudinRCA.Chapter04.FourierCircle)) =
            (Set.Ioo (-δ) δ).indicator (fun _ => (1 : ℝ)) t := by
        intro t ht
        have ht_le_pi : |t| ≤ Real.pi := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
        have hmem_iff : fourierToUnitCircle (t : RudinRCA.Chapter04.FourierCircle) ∈ A ↔
            t ∈ Set.Ioo (-δ) δ := by
          rw [show A = openCircleArc unitCircleOne δ from rfl,
            mem_openCircleArc_iff_chordal hδ hle_pi, fourierToUnitCircle_coe_apply,
            coe_unitCircleOne]
          have hexp_sq : ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ^ 2 = 2 * (1 - Real.cos |t|) := by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Real.cos_abs]
            simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
              Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sub_zero]
            have hcs := Real.sin_sq_add_cos_sq t
            nlinarith
          rw [hexp_sq, Set.mem_Ioo, ← abs_lt]
          constructor
          · intro hlt
            by_contra hge
            push Not at hge
            have hle := Real.strictAntiOn_cos.antitoneOn ⟨hδ.le, hle_pi⟩ ⟨abs_nonneg t, ht_le_pi⟩ hge
            linarith
          · intro hlt
            have hgt := Real.strictAntiOn_cos ⟨abs_nonneg t, ht_le_pi⟩ ⟨hδ.le, hle_pi⟩ hlt
            linarith
        by_cases ht_mem : t ∈ Set.Ioo (-δ) δ
        · rw [Set.indicator_of_mem (hmem_iff.mpr ht_mem), Set.indicator_of_mem ht_mem]
        · rw [Set.indicator_of_notMem (mt hmem_iff.mp ht_mem), Set.indicator_of_notMem ht_mem]
      have hint_eq : (∫ t in (-Real.pi)..Real.pi,
          A.indicator (fun _ => (1 : ℝ)) (fourierToUnitCircle (t : RudinRCA.Chapter04.FourierCircle))) =
          ∫ t in (-Real.pi)..Real.pi, (Set.Ioo (-δ) δ).indicator (fun _ => (1 : ℝ)) t := by
        rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
          intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
          integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
        exact setIntegral_congr_fun measurableSet_Ioo hae_congr
      have hint_val : (∫ t in (-Real.pi)..Real.pi,
          (Set.Ioo (-δ) δ).indicator (fun _ => (1 : ℝ)) t) = 2 * δ := by
        rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
          integral_Ioc_eq_integral_Ioo, setIntegral_indicator measurableSet_Ioo]
        have hinter : Set.Ioo (-Real.pi) Real.pi ∩ Set.Ioo (-δ) δ = Set.Ioo (-δ) δ :=
          Set.inter_eq_self_of_subset_right (Set.Ioo_subset_Ioo (by linarith) hle_pi)
        rw [hinter, setIntegral_const, Measure.real, Real.volume_Ioo, smul_eq_mul, mul_one,
          ENNReal.toReal_ofReal (by linarith)]
        ring
      have hfourier : ∀ t : ℝ,
          A.indicator (fun _ => (1 : ℝ))
            ⟨Complex.exp ((t : ℂ) * Complex.I), by simp [Complex.norm_exp_ofReal_mul_I]⟩ =
          A.indicator (fun _ => (1 : ℝ))
            (fourierToUnitCircle (t : RudinRCA.Chapter04.FourierCircle)) := by
        intro t
        have hpt : (⟨Complex.exp ((t : ℂ) * Complex.I), by simp [Complex.norm_exp_ofReal_mul_I]⟩ :
            UnitCircle) = fourierToUnitCircle (t : RudinRCA.Chapter04.FourierCircle) := by
          ext
          exact (fourierToUnitCircle_coe_apply t).symm
        rw [hpt]
      simp_rw [hfourier]
      rw [hint_eq, hint_val]
      have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
      field_simp
    rw [← ENNReal.ofReal_toReal (measure_ne_top unitCircleMeasure A), ← measureReal_def, hreal]

theorem unitCircleMeasure_openCircleArc_pos (ζ : UnitCircle) {δ : ℝ} (hδ : 0 < δ) :
    0 < unitCircleMeasure (openCircleArc ζ δ) := by
  rw [unitCircleMeasure_openCircleArc ζ hδ]
  exact ENNReal.ofReal_pos.mpr (lt_min (div_pos hδ Real.pi_pos) zero_lt_one)

theorem unitCircleMeasure_openCircleArc_ne_zero (ζ : UnitCircle) {δ : ℝ} (hδ : 0 < δ) :
    unitCircleMeasure (openCircleArc ζ δ) ≠ 0 :=
  (unitCircleMeasure_openCircleArc_pos ζ hδ).ne'

theorem unitCircleMeasure_openCircleArc_three_mul_le (ζ : UnitCircle) {δ : ℝ} (hδ : 0 < δ) :
    unitCircleMeasure (openCircleArc ζ (3 * δ)) ≤ 3 * unitCircleMeasure (openCircleArc ζ δ) := by
  rw [unitCircleMeasure_openCircleArc ζ (by positivity), unitCircleMeasure_openCircleArc ζ hδ]
  have h3 : (3 : ℝ≥0∞) = ENNReal.ofReal 3 := by norm_num
  rw [h3, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases le_total (δ / Real.pi) 1 with hle | hge
  · rw [min_eq_left hle]
    exact (min_le_left _ _).trans (le_of_eq (by ring))
  · have hge3 : 1 ≤ 3 * δ / Real.pi := by rw [mul_div_assoc]; linarith
    rw [min_eq_right hge, min_eq_right hge3]
    norm_num

/-- 11.19(3) (Definition, Rudin p. 241): Hardy–Littlewood maximal function `M ν` of a positive
Borel measure `ν` on `T = UnitCircle`, taking the supremum over all open arcs `I ⊂ T` centered
at `ζ`, including `T` itself (`δ > π`). -/
def circleMeasureMaximal (ν : Measure UnitCircle) (ζ : UnitCircle) : ℝ≥0∞ :=
  ⨆ δ ∈ Set.Ioi (0 : ℝ), ν (openCircleArc ζ δ) / unitCircleMeasure (openCircleArc ζ δ)

/-- 11.19(3) for a complex Borel measure `μ` on `T`: `(M μ)(ζ) = (M |μ|)(ζ)`. -/
def complexCircleMeasureMaximal (μ : ComplexMeasure UnitCircle) (ζ : UnitCircle) : ℝ≥0∞ :=
  circleMeasureMaximal μ.variation ζ

/-- Equivalence of `circleMeasureMaximal` with the literal supremum over the family of all proper
open arcs centered at `ζ` together with `Set.univ = T`. -/
theorem circleMeasureMaximal_eq_sSup_arcs (ν : Measure UnitCircle) (ζ : UnitCircle) :
    circleMeasureMaximal ν ζ =
      ⨆ I ∈ {I : Set UnitCircle | (∃ δ ∈ Set.Ioc 0 Real.pi, I = openCircleArc ζ δ) ∨ I = Set.univ},
        ν I / unitCircleMeasure I := by
  apply le_antisymm
  · refine iSup₂_le fun δ hδ => ?_
    rcases le_or_gt δ Real.pi with hle | hgt
    · exact le_iSup₂_of_le (openCircleArc ζ δ) (Or.inl ⟨δ, ⟨hδ, hle⟩, rfl⟩) le_rfl
    · rw [openCircleArc_eq_univ ζ hgt]
      exact le_iSup₂_of_le Set.univ (Or.inr rfl) le_rfl
  · refine iSup₂_le fun I hI => ?_
    rcases hI with ⟨δ, ⟨hδ0, _⟩, rfl⟩ | rfl
    · exact le_iSup₂_of_le δ hδ0 le_rfl
    · have huniv : openCircleArc ζ (2 * Real.pi) = Set.univ :=
        openCircleArc_eq_univ ζ (by linarith [Real.pi_pos])
      rw [← huniv]
      exact le_iSup₂_of_le (2 * Real.pi) (Set.mem_Ioi.mpr (by positivity)) le_rfl

/-- Lower semicontinuity of `ζ ↦ ν(openCircleArc ζ δ)` for every `δ > 0`. -/
theorem lowerSemicontinuous_measure_openCircleArc (ν : Measure UnitCircle) {δ : ℝ} (hδ : 0 < δ) :
    LowerSemicontinuous (fun ζ : UnitCircle => ν (openCircleArc ζ δ)) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro y
  rw [isOpen_iff_mem_nhds]
  intro ζ₀ hζ₀
  simp only [Set.mem_preimage, Set.mem_Ioi] at hζ₀
  let seq : ℕ → Set UnitCircle := fun n => openCircleArc ζ₀ (δ - δ / ((n : ℝ) + 2))
  have hmono : Monotone seq := fun m n hmn => openCircleArc_mono ζ₀ <| by
    have hm2 : 0 < (m : ℝ) + 2 := by positivity
    have hle : δ / ((n : ℝ) + 2) ≤ δ / ((m : ℝ) + 2) :=
      div_le_div_of_nonneg_left hδ.le hm2 (by exact_mod_cast Nat.add_le_add_right hmn 2)
    linarith
  have hunion : (⋃ n : ℕ, seq n) = openCircleArc ζ₀ δ := by
    ext η
    constructor
    · intro hη
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hη
      have hsub : δ - δ / ((n : ℝ) + 2) ≤ δ := by
        have hpos : 0 < δ / ((n : ℝ) + 2) := by positivity
        linarith
      exact openCircleArc_mono ζ₀ hsub hn
    · rintro ⟨s, hs, hη⟩
      have hgap : 0 < δ - |s| := sub_pos.mpr hs
      obtain ⟨n, hn⟩ := exists_nat_gt (δ / (δ - |s|))
      refine Set.mem_iUnion.mpr ⟨n, s, ?_, hη⟩
      have hn2 : δ / (δ - |s|) < (n : ℝ) + 2 := by linarith
      have hmul : δ < ((n : ℝ) + 2) * (δ - |s|) := (div_lt_iff₀ hgap).mp hn2
      have hdiv : δ / ((n : ℝ) + 2) < δ - |s| :=
        (div_lt_iff₀ (by positivity)).mpr (by linarith)
      linarith
  rw [← hunion, hmono.measure_iUnion, lt_iSup_iff] at hζ₀
  obtain ⟨n, hn⟩ := hζ₀
  let ε : ℝ := δ / ((n : ℝ) + 2)
  have hε_pos : 0 < ε := by positivity
  refine Filter.mem_of_superset
    ((isOpen_openCircleArc ζ₀ ε).mem_nhds (mem_openCircleArc_self ζ₀ hε_pos)) ?_
  intro ζ hζ
  simp only [Set.mem_preimage, Set.mem_Ioi]
  refine hn.trans_le (measure_mono ?_)
  obtain ⟨t, ht, hζ_eq⟩ := hζ
  rintro η ⟨s, hs, hη_eq⟩
  refine ⟨s - t, ?_, ?_⟩
  · have htri := abs_sub s t
    dsimp only [ε] at ht
    linarith
  · have hζ₀_eq : (ζ₀ : ℂ) = (ζ : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I) := by
      rw [hζ_eq, mul_assoc, ← Complex.exp_add]
      simp
    rw [hη_eq, hζ₀_eq, mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf

theorem lowerSemicontinuous_circleMeasureMaximal (ν : Measure UnitCircle) :
    LowerSemicontinuous (circleMeasureMaximal ν) := by
  unfold circleMeasureMaximal
  refine lowerSemicontinuous_biSup fun δ hδ => ?_
  let m : ℝ≥0∞ := ENNReal.ofReal (min (δ / Real.pi) 1)
  have hm0 : m ≠ 0 := by
    dsimp only [m]
    rw [← unitCircleMeasure_openCircleArc unitCircleOne hδ]
    exact unitCircleMeasure_openCircleArc_ne_zero unitCircleOne hδ
  have hm_top : m ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro y
  have heq : (fun ζ : UnitCircle => ν (openCircleArc ζ δ) / unitCircleMeasure (openCircleArc ζ δ)) ⁻¹'
        Set.Ioi y =
      (fun ζ : UnitCircle => ν (openCircleArc ζ δ)) ⁻¹' Set.Ioi (y * m) := by
    ext ζ
    simp only [Set.mem_preimage, Set.mem_Ioi, unitCircleMeasure_openCircleArc ζ hδ]
    exact ENNReal.lt_div_iff_mul_lt (Or.inl hm0) (Or.inl hm_top)
  rw [heq]
  exact lowerSemicontinuous_iff_isOpen_preimage.mp
    (lowerSemicontinuous_measure_openCircleArc ν hδ) (y * m)

theorem measurable_circleMeasureMaximal (ν : Measure UnitCircle) :
    Measurable (circleMeasureMaximal ν) :=
  (lowerSemicontinuous_circleMeasureMaximal ν).measurable

theorem measurable_complexCircleMeasureMaximal (μ : ComplexMeasure UnitCircle) :
    Measurable (complexCircleMeasureMaximal μ) :=
  measurable_circleMeasureMaximal μ.variation

/-- Finite Vitali 3-arc covering lemma on `UnitCircle`. -/
theorem exists_disjoint_subfamily_openCircleArc (F : Finset UnitCircle) (δ : UnitCircle → ℝ)
    (hδ : ∀ ζ ∈ F, 0 < δ ζ) :
    ∃ G ⊆ F,
      (G : Set UnitCircle).PairwiseDisjoint (fun ζ => openCircleArc ζ (δ ζ)) ∧
      (⋃ ζ ∈ F, openCircleArc ζ (δ ζ)) ⊆ ⋃ ζ ∈ G, openCircleArc ζ (3 * δ ζ) := by
  classical
  induction F using Finset.strongInduction with
  | H F ih =>
    rcases F.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
    · obtain ⟨ζ₀, hζ₀F, hmax⟩ := F.exists_max_image δ hne
      let F' : Finset UnitCircle :=
        F.filter fun ζ => Disjoint (openCircleArc ζ (δ ζ)) (openCircleArc ζ₀ (δ ζ₀))
      have hζ₀_notMem : ζ₀ ∉ F' := by
        simp only [F', Finset.mem_filter, not_and]
        intro _ hdisj
        have hmem := mem_openCircleArc_self ζ₀ (hδ ζ₀ hζ₀F)
        exact Set.disjoint_left.mp hdisj hmem hmem
      have hF'_ssub : F' ⊂ F :=
        Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.filter_subset _ F, fun heq => hζ₀_notMem (heq ▸ hζ₀F)⟩
      obtain ⟨G', hG'F', hG'_disj, hG'_cov⟩ :=
        ih F' hF'_ssub (fun ζ hζ => hδ ζ (Finset.filter_subset _ F hζ))
      refine ⟨insert ζ₀ G', Finset.insert_subset_iff.mpr ⟨hζ₀F, hG'F'.trans (Finset.filter_subset _ F)⟩,
        ?_, ?_⟩
      · rw [Finset.coe_insert]
        refine hG'_disj.insert fun ζ hζG' _ => ?_
        exact (Finset.mem_filter.mp (hG'F' hζG')).2.symm
      · intro η hη
        obtain ⟨ζ, hζF, hηζ⟩ := Set.mem_iUnion₂.mp hη
        by_cases hdisj : Disjoint (openCircleArc ζ (δ ζ)) (openCircleArc ζ₀ (δ ζ₀))
        · have hζF' : ζ ∈ F' := Finset.mem_filter.mpr ⟨hζF, hdisj⟩
          have hcov := hG'_cov (Set.mem_iUnion₂.mpr ⟨ζ, hζF', hηζ⟩)
          obtain ⟨ξ, hξG', hηξ⟩ := Set.mem_iUnion₂.mp hcov
          exact Set.mem_iUnion₂.mpr ⟨ξ, Finset.mem_insert_of_mem hξG', hηξ⟩
        · rw [Set.not_disjoint_iff_nonempty_inter] at hdisj
          have hsub := openCircleArc_subset_three_mul (hmax ζ hζF) hdisj hηζ
          exact Set.mem_iUnion₂.mpr ⟨ζ₀, Finset.mem_insert_self ζ₀ G', hsub⟩

/-- Weak-type `(1, 1)` maximal inequality on `T = UnitCircle` (`11.19(6)` for positive finite
Borel measures): `σ{M ν > λ} ≤ (3 / λ) ν(T)` for all `0 < λ < ∞`. -/
theorem weak_type_circleMeasureMaximal (ν : Measure UnitCircle) [IsFiniteMeasure ν]
    {lam : ℝ} (hlam : 0 < lam) :
    unitCircleMeasure {ζ : UnitCircle | ENNReal.ofReal lam < circleMeasureMaximal ν ζ} ≤
      ENNReal.ofReal (3 / lam) * ν Set.univ := by
  classical
  let E : Set UnitCircle := {ζ : UnitCircle | ENNReal.ofReal lam < circleMeasureMaximal ν ζ}
  have hE_open : IsOpen E :=
    lowerSemicontinuous_iff_isOpen_preimage.mp (lowerSemicontinuous_circleMeasureMaximal ν)
      (ENNReal.ofReal lam)
  -- Bound `unitCircleMeasure K` for any compact `K ⊆ E`, then use `InnerRegular`
  have hK_bound : ∀ K : Set UnitCircle, K ⊆ E → IsCompact K →
      unitCircleMeasure K ≤ ENNReal.ofReal (3 / lam) * ν Set.univ := by
    intro K hKE hK_comp
    have hex : ∀ ζ : UnitCircle, ζ ∈ K →
        ∃ δ : ℝ, 0 < δ ∧
          ENNReal.ofReal lam * unitCircleMeasure (openCircleArc ζ δ) <
            ν (openCircleArc ζ δ) := by
      intro ζ hζK
      have hlt : ENNReal.ofReal lam < circleMeasureMaximal ν ζ := hKE hζK
      unfold circleMeasureMaximal at hlt
      rw [lt_iSup_iff] at hlt
      obtain ⟨δ, hlt⟩ := hlt
      rw [lt_iSup_iff] at hlt
      obtain ⟨hδ, hlt⟩ := hlt
      refine ⟨δ, hδ, ?_⟩
      exact (ENNReal.lt_div_iff_mul_lt
        (Or.inl (unitCircleMeasure_openCircleArc_ne_zero ζ hδ))
        (Or.inl (measure_ne_top _ _))).mp hlt
    let δ : UnitCircle → ℝ := fun ζ => if h : ζ ∈ K then (hex ζ h).choose else 1
    have hδ_pos : ∀ ζ ∈ K, 0 < δ ζ := fun ζ hζ => by
      simp only [δ, hζ, ↓reduceDIte]; exact (hex ζ hζ).choose_spec.1
    have hδ_ineq : ∀ ζ ∈ K,
        ENNReal.ofReal lam * unitCircleMeasure (openCircleArc ζ (δ ζ)) ≤
          ν (openCircleArc ζ (δ ζ)) := fun ζ hζ => by
      simp only [δ, hζ, ↓reduceDIte]; exact (hex ζ hζ).choose_spec.2.le
    obtain ⟨F, hFK_cov⟩ := hK_comp.elim_finite_subcover
      (fun ζ : K => openCircleArc ζ.1 (δ ζ.1))
      (fun ζ => isOpen_openCircleArc ζ.1 (δ ζ.1))
      (fun ζ hζ => Set.mem_iUnion.mpr ⟨⟨ζ, hζ⟩, mem_openCircleArc_self ζ (hδ_pos ζ hζ)⟩)
    let F₀ : Finset UnitCircle := F.image Subtype.val
    have hF₀_sub : (F₀ : Set UnitCircle) ⊆ K := by
      intro ζ hζ
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hζ
      exact x.2
    have hK_sub_F₀ : K ⊆ ⋃ ζ ∈ F₀, openCircleArc ζ (δ ζ) := by
      intro η hη
      have hmem := hFK_cov hη
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨hxF, hηx⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion₂.mpr ⟨x.1, Finset.mem_image_of_mem Subtype.val hxF, hηx⟩
    obtain ⟨G, hGF₀, hG_disj, hG_cov⟩ :=
      exists_disjoint_subfamily_openCircleArc F₀ δ (fun ζ hζ => hδ_pos ζ (hF₀_sub hζ))
    have hK_sub_G : K ⊆ ⋃ ζ ∈ G, openCircleArc ζ (3 * δ ζ) := hK_sub_F₀.trans hG_cov
    have hGK : ∀ ζ ∈ G, ζ ∈ K := fun ζ hζ => hF₀_sub (hGF₀ hζ)
    have hlam_ne0 : ENNReal.ofReal lam ≠ 0 := (ENNReal.ofReal_pos.mpr hlam).ne'
    have hlam_top : ENNReal.ofReal lam ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmul_le : ENNReal.ofReal lam * unitCircleMeasure K ≤ 3 * ν Set.univ := by
      calc ENNReal.ofReal lam * unitCircleMeasure K
          ≤ ENNReal.ofReal lam * unitCircleMeasure (⋃ ζ ∈ G, openCircleArc ζ (3 * δ ζ)) :=
            mul_le_mul_of_nonneg_left (measure_mono hK_sub_G) zero_le
        _ ≤ ENNReal.ofReal lam * ∑ ζ ∈ G, unitCircleMeasure (openCircleArc ζ (3 * δ ζ)) :=
            mul_le_mul_of_nonneg_left (measure_biUnion_finset_le G _) zero_le
        _ ≤ ENNReal.ofReal lam * ∑ ζ ∈ G, 3 * unitCircleMeasure (openCircleArc ζ (δ ζ)) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ζ hζ => ?_) zero_le
            exact unitCircleMeasure_openCircleArc_three_mul_le ζ (hδ_pos ζ (hGK ζ hζ))
        _ = 3 * ∑ ζ ∈ G, ENNReal.ofReal lam * unitCircleMeasure (openCircleArc ζ (δ ζ)) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun ζ _ => by ac_rfl
        _ ≤ 3 * ∑ ζ ∈ G, ν (openCircleArc ζ (δ ζ)) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ζ hζ => hδ_ineq ζ (hGK ζ hζ)) zero_le
        _ = 3 * ν (⋃ ζ ∈ G, openCircleArc ζ (δ ζ)) := by
            rw [measure_biUnion_finset hG_disj fun ζ _ => (isOpen_openCircleArc ζ (δ ζ)).measurableSet]
        _ ≤ 3 * ν Set.univ :=
            mul_le_mul_of_nonneg_left (measure_mono (Set.subset_univ _)) zero_le
    have hdiv : unitCircleMeasure K ≤ (3 * ν Set.univ) / ENNReal.ofReal lam :=
      (ENNReal.le_div_iff_mul_le (Or.inl hlam_ne0) (Or.inl hlam_top)).mpr
        (by simpa only [mul_comm] using hmul_le)
    have h3_div : (3 * ν Set.univ) / ENNReal.ofReal lam =
        ENNReal.ofReal (3 / lam) * ν Set.univ := by
      have h3 : (3 : ℝ≥0∞) = ENNReal.ofReal 3 := by norm_num
      rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv, h3,
        ← ENNReal.ofReal_div_of_pos hlam]
    rwa [h3_div] at hdiv
  rw [hE_open.measurableSet.measure_eq_iSup_isCompact_of_ne_top (measure_ne_top _ _)]
  exact iSup₂_le fun K hKE => iSup_le fun hK => hK_bound K hKE hK

/-- 11.19(6) for complex Borel measures `μ` on `T`:
`σ{M μ > λ} ≤ (3 / λ) ‖μ‖` for every `0 < λ < ∞`. -/
theorem weak_type_complexCircleMeasureMaximal (μ : ComplexMeasure UnitCircle)
    {lam : ℝ} (hlam : 0 < lam) :
    unitCircleMeasure {ζ : UnitCircle | ENNReal.ofReal lam < complexCircleMeasureMaximal μ ζ} ≤
      ENNReal.ofReal ((3 / lam) * μ.variation.real Set.univ) ∧
    unitCircleMeasure.real {ζ : UnitCircle | ENNReal.ofReal lam < complexCircleMeasureMaximal μ ζ} ≤
      (3 / lam) * μ.variation.real Set.univ := by
  have : IsFiniteMeasure μ.variation := isFiniteMeasure_complexMeasure_variation μ
  have h1 := weak_type_circleMeasureMaximal μ.variation hlam
  have hvar_eq : μ.variation Set.univ = ENNReal.ofReal (μ.variation.real Set.univ) := by
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hvar_eq, ← ENNReal.ofReal_mul (by positivity)] at h1
  refine ⟨h1, ?_⟩
  rw [measureReal_def]
  exact (ENNReal.toReal_le_of_le_ofReal (by positivity) h1)

/-- 11.19(4) (Definition, Rudin p. 241): symmetric arc derivative `(Dμ)(ζ) = L` of a complex
Borel measure `μ` on `T = UnitCircle`. -/
def HasCircleSymmetricDerivAt (μ : ComplexMeasure UnitCircle) (ζ : UnitCircle) (L : ℂ) : Prop :=
  Tendsto (fun δ : ℝ => μ (openCircleArc ζ δ) / (unitCircleMeasure.real (openCircleArc ζ δ) : ℂ))
    (𝓝[>] 0) (𝓝 L)

/-- 11.19(4) for a positive Borel measure `ν` on `T = UnitCircle` (valued in `ℝ≥0∞ = [0, ∞]`,
avoiding `.toReal` truncation on infinite measures). -/
def HasPositiveCircleSymmetricDerivAt (ν : Measure UnitCircle) (ζ : UnitCircle)
    (L : ℝ≥0∞) : Prop :=
  Tendsto (fun δ : ℝ => ν (openCircleArc ζ δ) / unitCircleMeasure (openCircleArc ζ δ))
    (𝓝[>] 0) (𝓝 L)

/-- 11.19(5) (Definition, Rudin p. 241): `ζ ∈ T` is a Lebesgue point of `f ∈ L¹(T)` if
`lim_{δ → 0⁺} (1 / σ(I_δ)) ∫_{I_δ} ‖f - f(ζ)‖ dσ = 0`. -/
def IsCircleLebesguePoint (f : UnitCircle → ℂ) (ζ : UnitCircle) : Prop :=
  Tendsto (fun δ : ℝ =>
    (unitCircleMeasure.real (openCircleArc ζ δ))⁻¹ *
      ∫ η in openCircleArc ζ δ, ‖f η - f ζ‖ ∂unitCircleMeasure)
    (𝓝[>] 0) (𝓝 0)

/-- At any Lebesgue point `ζ` of `f ∈ L¹(T)`, the absolutely continuous complex measure `f dσ`
has symmetric derivative `(D(f dσ))(ζ) = f(ζ)`. -/
theorem hasCircleSymmetricDerivAt_withDensityᵥ_of_isCircleLebesguePoint
    {f : UnitCircle → ℂ} (hf : Integrable f unitCircleMeasure) {ζ : UnitCircle}
    (hleb : IsCircleLebesguePoint f ζ) :
    HasCircleSymmetricDerivAt (unitCircleMeasure.withDensityᵥ f) ζ (f ζ) := by
  unfold HasCircleSymmetricDerivAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [self_mem_nhdsWithin, Metric.tendsto_nhds.mp hleb ε hε] with δ hδ hleb_δ
  have hδ_pos : 0 < δ := hδ
  have hA_meas : MeasurableSet (openCircleArc ζ δ) := (isOpen_openCircleArc ζ δ).measurableSet
  have hσ_pos : 0 < unitCircleMeasure.real (openCircleArc ζ δ) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (unitCircleMeasure_openCircleArc_ne_zero ζ hδ_pos) (measure_ne_top _ _)
  have happly : (unitCircleMeasure.withDensityᵥ f) (openCircleArc ζ δ) =
      ∫ η in openCircleArc ζ δ, f η ∂unitCircleMeasure :=
    withDensityᵥ_apply hf hA_meas
  have hconst_int : (∫ _η in openCircleArc ζ δ, f ζ ∂unitCircleMeasure) =
      (unitCircleMeasure.real (openCircleArc ζ δ) : ℂ) * f ζ := by
    rw [setIntegral_const, Complex.real_smul]
  have hdiff : (unitCircleMeasure.withDensityᵥ f) (openCircleArc ζ δ) /
        (unitCircleMeasure.real (openCircleArc ζ δ) : ℂ) - f ζ =
      ((unitCircleMeasure.real (openCircleArc ζ δ))⁻¹ : ℂ) *
        ∫ η in openCircleArc ζ δ, (f η - f ζ) ∂unitCircleMeasure := by
    have hne : (unitCircleMeasure.real (openCircleArc ζ δ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hσ_pos.ne'
    rw [happly, integral_sub hf.integrableOn (integrableOn_const (measure_ne_top _ _)),
      hconst_int]
    field_simp [hne]
  rw [dist_eq_norm, hdiff, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hσ_pos]
  have hle : (unitCircleMeasure.real (openCircleArc ζ δ))⁻¹ *
        ‖∫ η in openCircleArc ζ δ, (f η - f ζ) ∂unitCircleMeasure‖ ≤
      (unitCircleMeasure.real (openCircleArc ζ δ))⁻¹ *
        ∫ η in openCircleArc ζ δ, ‖f η - f ζ‖ ∂unitCircleMeasure :=
    mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.mpr hσ_pos.le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (mul_nonneg (inv_nonneg.mpr hσ_pos.le) (integral_nonneg fun _ => norm_nonneg _))] at hleb_δ
  exact hle.trans_lt hleb_δ

/-- Every continuous function on `T` has every point of `T` as a Lebesgue point. -/
theorem isCircleLebesguePoint_of_continuous (g : C(UnitCircle, ℂ)) (ζ : UnitCircle) :
    IsCircleLebesguePoint g ζ := by
  unfold IsCircleLebesguePoint
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := Metric.continuous_iff.mp g.continuous ζ (ε / 2) (half_pos hε)
  filter_upwards [Ioo_mem_nhdsGT hδ₀_pos] with δ ⟨hδ_pos, hδ_lt⟩
  have hσ_pos : 0 < unitCircleMeasure.real (openCircleArc ζ δ) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (unitCircleMeasure_openCircleArc_ne_zero ζ hδ_pos) (measure_ne_top _ _)
  have hint : IntegrableOn (fun η : UnitCircle => ‖g η - g ζ‖) (openCircleArc ζ δ) unitCircleMeasure :=
    ((g.continuous.sub continuous_const).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn
  have hbound : (∫ η in openCircleArc ζ δ, ‖g η - g ζ‖ ∂unitCircleMeasure) ≤
      (ε / 2) * unitCircleMeasure.real (openCircleArc ζ δ) := by
    calc (∫ η in openCircleArc ζ δ, ‖g η - g ζ‖ ∂unitCircleMeasure)
        ≤ ∫ _η in openCircleArc ζ δ, (ε / 2) ∂unitCircleMeasure := by
          refine setIntegral_mono_on hint (integrableOn_const (measure_ne_top _ _))
            (isOpen_openCircleArc ζ δ).measurableSet fun η hη => ?_
          rw [← dist_eq_norm]
          exact (hδ₀ η ((dist_lt_of_mem_openCircleArc hη).trans hδ_lt)).le
      _ = (ε / 2) * unitCircleMeasure.real (openCircleArc ζ δ) := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (mul_nonneg (inv_nonneg.mpr hσ_pos.le) (integral_nonneg fun _ => norm_nonneg _))]
  calc (unitCircleMeasure.real (openCircleArc ζ δ))⁻¹ *
          ∫ η in openCircleArc ζ δ, ‖g η - g ζ‖ ∂unitCircleMeasure
      ≤ (unitCircleMeasure.real (openCircleArc ζ δ))⁻¹ *
          ((ε / 2) * unitCircleMeasure.real (openCircleArc ζ δ)) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hσ_pos.le)
    _ = ε / 2 := by field_simp [hσ_pos.ne']
    _ < ε := half_lt_self hε

/-- 11.19 (Theorem 7.7 on `T`, Rudin p. 241): almost every point of `T` (`[σ]`) is a Lebesgue
point of `f ∈ L¹(T)`. -/
theorem ae_isCircleLebesguePoint {f : UnitCircle → ℂ} (hf : Integrable f unitCircleMeasure) :
    ∀ᵐ ζ ∂unitCircleMeasure, IsCircleLebesguePoint f ζ := by
  have hf_mem : MemLp f 1 unitCircleMeasure := memLp_one_iff_integrable.mpr hf
  let avg (h : UnitCircle → ℂ) (ζ : UnitCircle) (δ : ℝ) : ℝ :=
    (unitCircleMeasure.real (openCircleArc ζ δ))⁻¹ *
      ∫ η in openCircleArc ζ δ, ‖h η - h ζ‖ ∂unitCircleMeasure
  let osc (h : UnitCircle → ℂ) (ζ : UnitCircle) : ℝ≥0∞ :=
    Filter.limsup (fun δ : ℝ => ENNReal.ofReal (avg h ζ δ)) (𝓝[>] 0)
  -- Show `osc f ζ = 0` `σ`-a.e., then deduce `IsCircleLebesguePoint f ζ`
  have hosc_zero_imp : ∀ ζ : UnitCircle, osc f ζ = 0 → IsCircleLebesguePoint f ζ := by
    intro ζ h0
    have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (avg f ζ δ)) (𝓝[>] 0) (𝓝 0) :=
      tendsto_of_le_liminf_of_limsup_le zero_le (h0 ▸ le_rfl)
    have htoReal : Tendsto (fun δ : ℝ => (ENNReal.ofReal (avg f ζ δ)).toReal) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.toReal_zero] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    refine htoReal.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ_pos : 0 < δ := hδ
    have hnn : 0 ≤ avg f ζ δ := mul_nonneg
      (inv_nonneg.mpr measureReal_nonneg) (integral_nonneg fun _ => norm_nonneg _)
    exact ENNReal.toReal_ofReal hnn
  -- Pointwise oscillation bound `osc f ζ ≤ M(|f - g| dσ)(ζ) + ‖f ζ - g ζ‖ₑ` for any `g ∈ C(T)`
  have hosc_le : ∀ (g : C(UnitCircle, ℂ)) (ζ : UnitCircle),
      osc f ζ ≤ circleMeasureMaximal
        (unitCircleMeasure.withDensity fun η => ‖f η - g η‖ₑ) ζ + ‖f ζ - g ζ‖ₑ := by
    intro g ζ
    let hfg : UnitCircle → ℂ := f - (g : UnitCircle → ℂ)
    have hhfg_int : Integrable hfg unitCircleMeasure :=
      hf.sub (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    let ν_fg : Measure UnitCircle := unitCircleMeasure.withDensity fun η => ‖hfg η‖ₑ
    have hg_leb := (ENNReal.tendsto_ofReal (isCircleLebesguePoint_of_continuous g ζ))
    rw [ENNReal.ofReal_zero] at hg_leb
    have hev : ∀ᶠ δ : ℝ in 𝓝[>] 0,
        ENNReal.ofReal (avg f ζ δ) ≤
          circleMeasureMaximal ν_fg ζ + ENNReal.ofReal (avg g ζ δ) + ‖hfg ζ‖ₑ := by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hδ_pos : 0 < δ := hδ
      let I := openCircleArc ζ δ
      have hI_meas : MeasurableSet I := (isOpen_openCircleArc ζ δ).measurableSet
      have hσ_pos : 0 < unitCircleMeasure.real I := by
        rw [measureReal_def]
        exact ENNReal.toReal_pos (unitCircleMeasure_openCircleArc_ne_zero ζ hδ_pos) (measure_ne_top _ _)
      have htri_int : (∫ η in I, ‖f η - f ζ‖ ∂unitCircleMeasure) ≤
          (∫ η in I, ‖hfg η‖ ∂unitCircleMeasure) +
            (∫ η in I, ‖g η - g ζ‖ ∂unitCircleMeasure) +
            unitCircleMeasure.real I * ‖hfg ζ‖ := by
        have hint1 : IntegrableOn (fun η => ‖hfg η‖) I unitCircleMeasure := hhfg_int.norm.integrableOn
        have hint2 : IntegrableOn (fun η => ‖g η - g ζ‖) I unitCircleMeasure :=
          ((g.continuous.sub continuous_const).norm.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)).integrableOn
        have hint3 : IntegrableOn (fun _ => ‖hfg ζ‖) I unitCircleMeasure :=
          integrableOn_const (measure_ne_top _ _)
        have hsum1 := integral_add (f := fun η => ‖hfg η‖ + ‖g η - g ζ‖)
          (g := fun _ => ‖hfg ζ‖) (hint1.add hint2) hint3
        have hsum2 := integral_add hint1 hint2
        rw [hsum2, setIntegral_const, smul_eq_mul] at hsum1
        rw [← hsum1]
        refine setIntegral_mono_on ((hf.sub (integrable_const _)).norm.integrableOn)
          ((hint1.add hint2).add hint3) hI_meas fun η _ => ?_
        dsimp only [Pi.add_apply, hfg, Pi.sub_apply]
        have heq : f η - f ζ = (f η - g η) + (g η - g ζ) - (f ζ - g ζ) := by ring
        rw [heq]
        linarith [norm_sub_le ((f η - g η) + (g η - g ζ)) (f ζ - g ζ),
          norm_add_le (f η - g η) (g η - g ζ)]
      have havg_le : avg f ζ δ ≤
          (unitCircleMeasure.real I)⁻¹ * (∫ η in I, ‖hfg η‖ ∂unitCircleMeasure) +
            avg g ζ δ + ‖hfg ζ‖ := by
        dsimp only [avg]
        have hmul := mul_le_mul_of_nonneg_left htri_int (inv_nonneg.mpr hσ_pos.le)
        have hne : unitCircleMeasure.real I ≠ 0 := hσ_pos.ne'
        calc (unitCircleMeasure.real I)⁻¹ * ∫ η in I, ‖f η - f ζ‖ ∂unitCircleMeasure
            ≤ (unitCircleMeasure.real I)⁻¹ *
                ((∫ η in I, ‖hfg η‖ ∂unitCircleMeasure) +
                  (∫ η in I, ‖g η - g ζ‖ ∂unitCircleMeasure) +
                  unitCircleMeasure.real I * ‖hfg ζ‖) := hmul
          _ = (unitCircleMeasure.real I)⁻¹ * (∫ η in I, ‖hfg η‖ ∂unitCircleMeasure) +
                (unitCircleMeasure.real I)⁻¹ * (∫ η in I, ‖g η - g ζ‖ ∂unitCircleMeasure) +
                ‖hfg ζ‖ := by field_simp [hne]
      have h1_nn : 0 ≤ (unitCircleMeasure.real I)⁻¹ * (∫ η in I, ‖hfg η‖ ∂unitCircleMeasure) :=
        mul_nonneg (inv_nonneg.mpr hσ_pos.le) (integral_nonneg fun _ => norm_nonneg _)
      have h2_nn : 0 ≤ avg g ζ δ :=
        mul_nonneg (inv_nonneg.mpr hσ_pos.le) (integral_nonneg fun _ => norm_nonneg _)
      have h1_le_M : ENNReal.ofReal
            ((unitCircleMeasure.real I)⁻¹ * (∫ η in I, ‖hfg η‖ ∂unitCircleMeasure)) ≤
          circleMeasureMaximal ν_fg ζ := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hσ_pos.le),
          ENNReal.ofReal_inv_of_pos hσ_pos,
          ofReal_integral_eq_lintegral_ofReal hhfg_int.norm.integrableOn
            (ae_of_all _ fun _ => norm_nonneg _)]
        have hνI : (∫⁻ η in I, ENNReal.ofReal ‖hfg η‖ ∂unitCircleMeasure) = ν_fg I := by
          dsimp only [ν_fg]
          rw [withDensity_apply _ hI_meas]
          refine lintegral_congr fun η => ofReal_norm (hfg η)
        have hσI : ENNReal.ofReal (unitCircleMeasure.real I) = unitCircleMeasure I := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
        rw [hνI, hσI, mul_comm, ← div_eq_mul_inv]
        exact le_iSup₂_of_le δ hδ_pos le_rfl
      calc ENNReal.ofReal (avg f ζ δ)
          ≤ ENNReal.ofReal
              ((unitCircleMeasure.real I)⁻¹ * (∫ η in I, ‖hfg η‖ ∂unitCircleMeasure) +
                avg g ζ δ + ‖hfg ζ‖) := ENNReal.ofReal_le_ofReal havg_le
        _ = ENNReal.ofReal ((unitCircleMeasure.real I)⁻¹ * (∫ η in I, ‖hfg η‖ ∂unitCircleMeasure)) +
              ENNReal.ofReal (avg g ζ δ) + ‖hfg ζ‖ₑ := by
            rw [ENNReal.ofReal_add (add_nonneg h1_nn h2_nn) (norm_nonneg _),
              ENNReal.ofReal_add h1_nn h2_nn, ofReal_norm]
        _ ≤ circleMeasureMaximal ν_fg ζ + ENNReal.ofReal (avg g ζ δ) + ‖hfg ζ‖ₑ := by
            gcongr
    have hlim_rhs : Tendsto
        (fun δ : ℝ => circleMeasureMaximal ν_fg ζ + ENNReal.ofReal (avg g ζ δ) + ‖hfg ζ‖ₑ)
        (𝓝[>] 0) (𝓝 (circleMeasureMaximal ν_fg ζ + 0 + ‖hfg ζ‖ₑ)) :=
      (tendsto_const_nhds.add hg_leb).add tendsto_const_nhds
    have hls_rhs : Filter.limsup
        (fun δ : ℝ => circleMeasureMaximal ν_fg ζ + ENNReal.ofReal (avg g ζ δ) + ‖hfg ζ‖ₑ)
        (𝓝[>] 0) = circleMeasureMaximal ν_fg ζ + ‖hfg ζ‖ₑ := by
      simpa only [add_zero] using hlim_rhs.limsup_eq
    change osc f ζ ≤ circleMeasureMaximal ν_fg ζ + ‖hfg ζ‖ₑ
    rw [← hls_rhs]
    exact Filter.limsup_le_limsup hev
  -- For each `m : ℕ`, `unitCircleMeasure {ζ | osc f ζ > 1 / (m + 1)} = 0`
  have hmeas_level_zero : ∀ m : ℕ,
      unitCircleMeasure {ζ : UnitCircle | ENNReal.ofReal (1 / ((m : ℝ) + 1)) < osc f ζ} = 0 := by
    intro m
    let ε : ℝ := 1 / ((m : ℝ) + 1)
    have hε_pos : 0 < ε := by positivity
    apply le_antisymm _ zero_le
    refine le_of_forall_pos_le_add fun η hη => ?_
    rw [zero_add]
    by_cases hη_top : η = ⊤
    · simp [hη_top]
    have hη_r_pos : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hη_top
    let δ_g : ℝ := (ε / 16) * η.toReal
    have hδ_g_pos : 0 < δ_g := by positivity
    obtain ⟨g, hfg_lp⟩ := @exists_continuous_eLpNorm_sub_le 1 ⟨le_rfl⟩ ENNReal.one_ne_top
      f hf_mem δ_g hδ_g_pos
    let hfg : UnitCircle → ℂ := f - (g : UnitCircle → ℂ)
    have hhfg_int : Integrable hfg unitCircleMeasure :=
      hf.sub (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    rw [eLpNorm_one_eq_lintegral_enorm hhfg_int.aestronglyMeasurable] at hfg_lp
    let ν_fg : Measure UnitCircle := unitCircleMeasure.withDensity fun x => ‖hfg x‖ₑ
    have hν_univ : ν_fg Set.univ ≤ ENNReal.ofReal δ_g := by
      dsimp only [ν_fg]
      rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have : IsFiniteMeasure ν_fg :=
      ⟨lt_of_le_of_lt hν_univ ENNReal.ofReal_lt_top⟩
    let A₁ : Set UnitCircle := {ζ | ENNReal.ofReal (ε / 2) < circleMeasureMaximal ν_fg ζ}
    let A₂ : Set UnitCircle := {ζ | ENNReal.ofReal (ε / 2) ≤ ‖hfg ζ‖ₑ}
    have hsub : {ζ | ENNReal.ofReal ε < osc f ζ} ⊆ A₁ ∪ A₂ := by
      intro ζ hζ
      simp only [Set.mem_ofPred_eq] at hζ
      have hle := hosc_le g ζ
      by_contra hnot
      simp only [Set.mem_union, A₁, A₂, Set.mem_ofPred_eq, not_or, not_lt, not_le] at hnot
      have hsum_le : circleMeasureMaximal ν_fg ζ + ‖hfg ζ‖ₑ ≤ ENNReal.ofReal ε := by
        calc circleMeasureMaximal ν_fg ζ + ‖hfg ζ‖ₑ
            ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
              add_le_add hnot.1 hnot.2.le
          _ = ENNReal.ofReal ε := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]
      exact not_lt_of_ge (hle.trans hsum_le) hζ
    have hA₁_le : unitCircleMeasure A₁ ≤ ENNReal.ofReal ((6 / ε) * δ_g) := by
      calc unitCircleMeasure A₁
          ≤ ENNReal.ofReal (3 / (ε / 2)) * ν_fg Set.univ :=
            weak_type_circleMeasureMaximal ν_fg (half_pos hε_pos)
        _ ≤ ENNReal.ofReal (6 / ε) * ENNReal.ofReal δ_g := by
            rw [show (3 : ℝ) / (ε / 2) = 6 / ε by ring]
            exact mul_le_mul_of_nonneg_left hν_univ zero_le
        _ = ENNReal.ofReal ((6 / ε) * δ_g) :=
            (ENNReal.ofReal_mul (by positivity)).symm
    have hA₂_le : unitCircleMeasure A₂ ≤ ENNReal.ofReal ((2 / ε) * δ_g) := by
      have hmarkov := mul_meas_ge_le_lintegral₀ hhfg_int.aestronglyMeasurable.enorm
        (ENNReal.ofReal (ε / 2))
      have hlt_ne0 : ENNReal.ofReal (ε / 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (half_pos hε_pos)).ne'
      have hdiv : unitCircleMeasure A₂ ≤
          (∫⁻ x, ‖hfg x‖ₑ ∂unitCircleMeasure) / ENNReal.ofReal (ε / 2) :=
        (ENNReal.le_div_iff_mul_le (Or.inl hlt_ne0) (Or.inl ENNReal.ofReal_ne_top)).mpr
          (by simpa only [mul_comm] using hmarkov)
      calc unitCircleMeasure A₂
          ≤ ENNReal.ofReal δ_g / ENNReal.ofReal (ε / 2) :=
            hdiv.trans (ENNReal.div_le_div_right hfg_lp _)
        _ = ENNReal.ofReal ((2 / ε) * δ_g) := by
            rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (half_pos hε_pos),
              ← ENNReal.ofReal_mul hδ_g_pos.le]
            congr 1
            ring
    calc unitCircleMeasure {ζ | ENNReal.ofReal ε < osc f ζ}
        ≤ unitCircleMeasure (A₁ ∪ A₂) := measure_mono hsub
      _ ≤ unitCircleMeasure A₁ + unitCircleMeasure A₂ := measure_union_le _ _
      _ ≤ ENNReal.ofReal ((6 / ε) * δ_g) + ENNReal.ofReal ((2 / ε) * δ_g) :=
          add_le_add hA₁_le hA₂_le
      _ = ENNReal.ofReal (η.toReal / 2) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          dsimp only [δ_g]
          field_simp [hε_pos.ne']
          ring
      _ ≤ ENNReal.ofReal η.toReal := ENNReal.ofReal_le_ofReal (by linarith)
      _ = η := ENNReal.ofReal_toReal hη_top
  have hnull : unitCircleMeasure {ζ : UnitCircle | osc f ζ ≠ 0} = 0 := by
    have hsub : {ζ : UnitCircle | osc f ζ ≠ 0} ⊆
        ⋃ m : ℕ, {ζ : UnitCircle | ENNReal.ofReal (1 / ((m : ℝ) + 1)) < osc f ζ} := by
      intro ζ hζ
      simp only [Set.mem_ofPred_eq] at hζ
      by_cases htop : osc f ζ = ⊤
      · exact Set.mem_iUnion.mpr ⟨0, by simp [htop]⟩
      · have hr_pos : 0 < (osc f ζ).toReal := ENNReal.toReal_pos hζ htop
        obtain ⟨m, hm⟩ := exists_nat_gt (1 / (osc f ζ).toReal)
        refine Set.mem_iUnion.mpr ⟨m, ?_⟩
        simp only [Set.mem_ofPred_eq]
        rw [← ENNReal.ofReal_toReal htop]
        refine (ENNReal.ofReal_lt_ofReal_iff hr_pos).mpr ?_
        have hm1 : 1 / (osc f ζ).toReal < (m : ℝ) + 1 := by linarith
        exact (div_lt_iff₀ (by positivity)).mpr <| by
          have := (div_lt_iff₀ hr_pos).mp hm1
          linarith
    exact measure_mono_null hsub (measure_iUnion_null hmeas_level_zero)
  have hae : ∀ᵐ ζ ∂unitCircleMeasure, osc f ζ = 0 := by
    rw [ae_iff]
    exact hnull
  filter_upwards [hae] with ζ hζ using hosc_zero_imp ζ hζ

/-- 11.19 (Theorem 7.14 singular part on `T`, positive-measure form): if a positive finite Borel
measure `ν` on `T` satisfies `ν ⟂ₘ σ`, then `Dν = 0` a.e. `[σ]`. -/
theorem ae_hasPositiveCircleSymmetricDerivAt_zero_of_mutuallySingular
    (ν : Measure UnitCircle) [IsFiniteMeasure ν]
    (hsing : ν.MutuallySingular unitCircleMeasure) :
    ∀ᵐ ζ ∂unitCircleMeasure, HasPositiveCircleSymmetricDerivAt ν ζ 0 := by
  let S : Set UnitCircle := hsing.nullSetᶜ
  have hS_meas : MeasurableSet S := hsing.measurableSet_nullSet.compl
  have hν_Sc : ν Sᶜ = 0 := by
    dsimp only [S]
    rw [compl_compl]
    exact hsing.measure_nullSet
  have hσ_S : unitCircleMeasure S = 0 := hsing.measure_compl_nullSet
  let osc (ζ : UnitCircle) : ℝ≥0∞ :=
    Filter.limsup (fun δ : ℝ => ν (openCircleArc ζ δ) / unitCircleMeasure (openCircleArc ζ δ))
      (𝓝[>] 0)
  have hmeas_level_zero : ∀ m : ℕ,
      unitCircleMeasure {ζ : UnitCircle | ENNReal.ofReal (1 / ((m : ℝ) + 1)) < osc ζ} = 0 := by
    intro m
    let ε : ℝ := 1 / ((m : ℝ) + 1)
    have hε_pos : 0 < ε := by positivity
    apply le_antisymm _ zero_le
    refine le_of_forall_pos_le_add fun η hη => ?_
    rw [zero_add]
    let δ_ν : ℝ≥0∞ := ENNReal.ofReal (ε / 3) * η
    have hδ_ν_ne0 : δ_ν ≠ 0 :=
      mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' hη.ne'
    obtain ⟨K, hKS, hK_comp, hν_diff⟩ :=
      hS_meas.exists_isCompact_sdiff_lt (measure_ne_top ν S) hδ_ν_ne0
    let ν' : Measure UnitCircle := ν.restrict Kᶜ
    have hν'_univ : ν' Set.univ ≤ δ_ν := by
      dsimp only [ν']
      rw [Measure.restrict_apply_univ]
      have hKc_sub : Kᶜ ⊆ (S \ K) ∪ Sᶜ := fun x hx => by
        by_cases hxS : x ∈ S
        · exact Or.inl ⟨hxS, hx⟩
        · exact Or.inr hxS
      calc ν Kᶜ ≤ ν ((S \ K) ∪ Sᶜ) := measure_mono hKc_sub
        _ ≤ ν (S \ K) + ν Sᶜ := measure_union_le _ _
        _ = ν (S \ K) := by rw [hν_Sc, add_zero]
        _ ≤ δ_ν := hν_diff.le
    have hosc_le_on_Sc : ∀ ζ ∈ Sᶜ, osc ζ ≤ circleMeasureMaximal ν' ζ := by
      intro ζ hζSc
      have hζKc : ζ ∈ Kᶜ := fun hζK => hζSc (hKS hζK)
      have hKc_open : IsOpen Kᶜ := hK_comp.isClosed.isOpen_compl
      obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ := Metric.isOpen_iff.mp hKc_open ζ hζKc
      have hev : ∀ᶠ δ : ℝ in 𝓝[>] 0,
          ν (openCircleArc ζ δ) / unitCircleMeasure (openCircleArc ζ δ) ≤
            circleMeasureMaximal ν' ζ := by
        filter_upwards [Ioo_mem_nhdsGT hr₀_pos] with δ ⟨hδ_pos, hδ_lt⟩
        have harc_sub : openCircleArc ζ δ ⊆ Kᶜ := fun ξ hξ =>
          hr₀_sub ((dist_lt_of_mem_openCircleArc hξ).trans hδ_lt)
        have hν_eq : ν (openCircleArc ζ δ) = ν' (openCircleArc ζ δ) := by
          dsimp only [ν']
          rw [Measure.restrict_apply (isOpen_openCircleArc ζ δ).measurableSet,
            Set.inter_eq_self_of_subset_left harc_sub]
        rw [hν_eq]
        exact le_iSup₂_of_le δ hδ_pos le_rfl
      exact Filter.limsup_le_of_le ⟨0, fun _ _ => zero_le⟩ hev
    have hsub : {ζ | ENNReal.ofReal ε < osc ζ} ⊆
        S ∪ {ζ | ENNReal.ofReal ε < circleMeasureMaximal ν' ζ} := by
      intro ζ hζ
      by_cases hζS : ζ ∈ S
      · exact Or.inl hζS
      · exact Or.inr (hζ.trans_le (hosc_le_on_Sc ζ hζS))
    calc unitCircleMeasure {ζ | ENNReal.ofReal ε < osc ζ}
        ≤ unitCircleMeasure (S ∪ {ζ | ENNReal.ofReal ε < circleMeasureMaximal ν' ζ}) :=
          measure_mono hsub
      _ ≤ unitCircleMeasure S +
            unitCircleMeasure {ζ | ENNReal.ofReal ε < circleMeasureMaximal ν' ζ} :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (3 / ε) * ν' Set.univ := by
          rw [hσ_S, zero_add]
          exact weak_type_circleMeasureMaximal ν' hε_pos
      _ ≤ ENNReal.ofReal (3 / ε) * δ_ν :=
          mul_le_mul_of_nonneg_left hν'_univ zero_le
      _ = η := by
          dsimp only [δ_ν]
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            show (3 / ε) * (ε / 3) = 1 by field_simp [hε_pos.ne'], ENNReal.ofReal_one, one_mul]
  have hnull : unitCircleMeasure {ζ : UnitCircle | osc ζ ≠ 0} = 0 := by
    have hsub : {ζ : UnitCircle | osc ζ ≠ 0} ⊆
        ⋃ m : ℕ, {ζ : UnitCircle | ENNReal.ofReal (1 / ((m : ℝ) + 1)) < osc ζ} := by
      intro ζ hζ
      simp only [Set.mem_ofPred_eq] at hζ
      by_cases htop : osc ζ = ⊤
      · exact Set.mem_iUnion.mpr ⟨0, by simp [htop]⟩
      · have hr_pos : 0 < (osc ζ).toReal := ENNReal.toReal_pos hζ htop
        obtain ⟨m, hm⟩ := exists_nat_gt (1 / (osc ζ).toReal)
        refine Set.mem_iUnion.mpr ⟨m, ?_⟩
        simp only [Set.mem_ofPred_eq]
        rw [← ENNReal.ofReal_toReal htop]
        refine (ENNReal.ofReal_lt_ofReal_iff hr_pos).mpr ?_
        have hm1 : 1 / (osc ζ).toReal < (m : ℝ) + 1 := by linarith
        exact (div_lt_iff₀ (by positivity)).mpr <| by
          have := (div_lt_iff₀ hr_pos).mp hm1
          linarith
    exact measure_mono_null hsub (measure_iUnion_null hmeas_level_zero)
  have hae : ∀ᵐ ζ ∂unitCircleMeasure, osc ζ = 0 := by
    rw [ae_iff]
    exact hnull
  filter_upwards [hae] with ζ hζ
  exact tendsto_of_le_liminf_of_limsup_le zero_le (hζ ▸ le_rfl)

/-- Equivalence between `μ_s ⟂ᵥ σ.toENNRealVectorMeasure` and `μ_s.variation ⟂ₘ σ`. -/
theorem mutuallySingular_complexMeasure_iff_variation (μ_s : ComplexMeasure UnitCircle) :
    μ_s ⟂ᵥ unitCircleMeasure.toENNRealVectorMeasure ↔
      μ_s.variation.MutuallySingular unitCircleMeasure := by
  constructor
  · rintro ⟨S, hS, hμs, hσ⟩
    refine ⟨S, hS, ?_, ?_⟩
    · rw [RudinRCA.Chapter06.variation_eq_iSup_countablePartitions μ_s hS]
      refine ENNReal.iSup_eq_zero.mpr fun P => ENNReal.tsum_eq_zero.mpr fun i => ?_
      have hsub : P.part i ⊆ S := fun x hx => by
        have hxU : x ∈ ⋃ j, P.part j := Set.mem_iUnion.mpr ⟨i, hx⟩
        rwa [P.covers] at hxU
      simp [hμs (P.part i) hsub]
    · have h0 := hσ Sᶜ (Set.Subset.refl _)
      rwa [Measure.toENNRealVectorMeasure_apply_measurable hS.compl] at h0
  · intro hsing
    refine ⟨hsing.nullSet, hsing.measurableSet_nullSet, ?_, ?_⟩
    · intro E hE
      have hvar0 : μ_s.variation E = 0 :=
        measure_mono_null hE hsing.measure_nullSet
      have hle := μ_s.enorm_measure_le_variation E
      rw [hvar0, nonpos_iff_eq_zero, enorm_eq_zero] at hle
      exact hle
    · intro E hE
      by_cases hEm : MeasurableSet E
      · rw [Measure.toENNRealVectorMeasure_apply_measurable hEm]
        exact measure_mono_null hE hsing.measure_compl_nullSet
      · exact VectorMeasure.not_measurable _ hEm

/-- 11.19 (`Dμ_s = 0` a.e. `[σ]` for singular complex Borel measures on `T`). -/
theorem ae_hasCircleSymmetricDerivAt_zero_of_mutuallySingular
    (μ_s : ComplexMeasure UnitCircle)
    (hsing : μ_s ⟂ᵥ unitCircleMeasure.toENNRealVectorMeasure) :
    ∀ᵐ ζ ∂unitCircleMeasure, HasCircleSymmetricDerivAt μ_s ζ 0 := by
  have : IsFiniteMeasure μ_s.variation := isFiniteMeasure_complexMeasure_variation μ_s
  have hsing_var := (mutuallySingular_complexMeasure_iff_variation μ_s).mp hsing
  filter_upwards [ae_hasPositiveCircleSymmetricDerivAt_zero_of_mutuallySingular μ_s.variation hsing_var]
    with ζ hζ
  unfold HasCircleSymmetricDerivAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev := (ENNReal.tendsto_nhds_zero.mp hζ) (ENNReal.ofReal (ε / 2))
    (ENNReal.ofReal_pos.mpr (half_pos hε))
  filter_upwards [self_mem_nhdsWithin, hev] with δ hδ hle
  have hδ_pos : 0 < δ := hδ
  let I := openCircleArc ζ δ
  have hσ_pos : 0 < unitCircleMeasure.real I := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (unitCircleMeasure_openCircleArc_ne_zero ζ hδ_pos) (measure_ne_top _ _)
  have hnorm_le : ‖μ_s I / (unitCircleMeasure.real I : ℂ)‖ₑ ≤ ENNReal.ofReal (ε / 2) := by
    rw [← ofReal_norm, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ_pos,
      ENNReal.ofReal_div_of_pos hσ_pos, ofReal_norm]
    have hσ_eq : ENNReal.ofReal (unitCircleMeasure.real I) = unitCircleMeasure I := by
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [hσ_eq]
    exact (ENNReal.div_le_div_right (μ_s.enorm_measure_le_variation I) _).trans hle
  rw [dist_zero_right, ← toReal_enorm]
  have hle_real : ‖μ_s I / (unitCircleMeasure.real I : ℂ)‖ₑ.toReal ≤ ε / 2 :=
    ENNReal.toReal_le_of_le_ofReal (half_pos hε).le hnorm_le
  exact hle_real.trans_lt (half_lt_self hε)

/-- 11.19 (Summary Theorem, Rudin p. 241):
1. Semicontinuity, closed `{≤ λ}` level sets, measurability, and monotonicity of `N_α u` and
   `M_rad u` (`0 < α < 1`, `u` continuous on `U`).
2. If `dμ = f dσ + dμ_s` is the Lebesgue decomposition of a complex Borel measure `μ` on `T`
   (`f ∈ L¹(T)`, `μ_s ⟂ σ`), then:
   - `σ{M μ > λ} ≤ (3 / λ) ‖μ‖` for every `0 < λ < ∞` (`11.19(6)`),
   - `σ`-a.e. point of `T` is a Lebesgue point of `f`,
   - `Dμ_s = 0` and `Dμ = f` `σ`-a.e. -/
theorem theorem11_19 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ {u : ℂ → ℂ}, ContinuousOn u (Metric.ball (0 : ℂ) 1) →
      (∀ {lam : ℝ}, 0 < lam →
        IsClosed {ζ : UnitCircle | nontangentialMaximal α u ζ ≤ ENNReal.ofReal lam} ∧
        IsClosed {ζ : UnitCircle | radialMaximal u ζ ≤ ENNReal.ofReal lam}) ∧
      LowerSemicontinuous (nontangentialMaximal α u) ∧
      LowerSemicontinuous (radialMaximal u) ∧
      Measurable (nontangentialMaximal α u) ∧
      Measurable (radialMaximal u) ∧
      (∀ ζ : UnitCircle, radialMaximal u ζ ≤ nontangentialMaximal α u ζ)) ∧
    (∀ {β : ℝ} (u : ℂ → ℂ), α ≤ β → ∀ ζ : UnitCircle,
      nontangentialMaximal α u ζ ≤ nontangentialMaximal β u ζ) ∧
    (∀ (μ μ_s : ComplexMeasure UnitCircle) (f : UnitCircle → ℂ),
      Integrable f unitCircleMeasure →
      μ_s ⟂ᵥ unitCircleMeasure.toENNRealVectorMeasure →
      μ = unitCircleMeasure.withDensityᵥ f + μ_s →
      (∀ {lam : ℝ}, 0 < lam →
        unitCircleMeasure.real {ζ : UnitCircle |
            ENNReal.ofReal lam < complexCircleMeasureMaximal μ ζ} ≤
          (3 / lam) * μ.variation.real Set.univ) ∧
      (∀ᵐ ζ ∂unitCircleMeasure, IsCircleLebesguePoint f ζ) ∧
      (∀ᵐ ζ ∂unitCircleMeasure, HasCircleSymmetricDerivAt μ_s ζ 0) ∧
      (∀ᵐ ζ ∂unitCircleMeasure, HasCircleSymmetricDerivAt μ ζ (f ζ))) := by
  refine ⟨fun {u} hu => ⟨fun {lam} _ =>
      ⟨isClosed_nontangentialMaximal_le hα0 hα1 u _, isClosed_radialMaximal_le hu _⟩,
      lowerSemicontinuous_nontangentialMaximal hα0 hα1 u,
      lowerSemicontinuous_radialMaximal hu,
      measurable_nontangentialMaximal hα0 hα1 u,
      measurable_radialMaximal hu,
      radialMaximal_le_nontangentialMaximal hα0 hα1 u⟩,
    fun u hαβ ζ => nontangentialMaximal_mono hαβ u ζ,
    fun μ μ_s f hf hsing hdecomp => ?_⟩
  refine ⟨fun {lam} hlam => (weak_type_complexCircleMeasureMaximal μ hlam).2,
    ae_isCircleLebesguePoint hf,
    ae_hasCircleSymmetricDerivAt_zero_of_mutuallySingular μ_s hsing, ?_⟩
  filter_upwards [ae_isCircleLebesguePoint hf,
    ae_hasCircleSymmetricDerivAt_zero_of_mutuallySingular μ_s hsing] with ζ hleb hzero
  have hac := hasCircleSymmetricDerivAt_withDensityᵥ_of_isCircleLebesguePoint hf hleb
  unfold HasCircleSymmetricDerivAt at hac hzero ⊢
  have hsum := hac.add hzero
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ _
  rw [hdecomp, add_apply, add_div]

end Node11_19

section Node11_20

/-- Explicit nontangential constant `c_α = ((1 - α) / (3 - α)) ^ 2 > 0` for `0 < α < 1`
(Rudin 11.20, p. 242: `c_α = (1 + γ_α)⁻²` with `γ_α = 2 / (1 - α)`). -/
def nontangentialConstant (α : ℝ) : ℝ :=
  ((1 - α) / (3 - α)) ^ 2

theorem nontangentialConstant_pos {α : ℝ} (hα1 : α < 1) :
    0 < nontangentialConstant α := by
  unfold nontangentialConstant
  have h1 : 0 < 1 - α := sub_pos.mpr hα1
  have h3 : 0 < 3 - α := by linarith
  positivity

/-- Poisson integral `u(z) = ∫_T P(z, η) dμ(η)` of a positive Borel measure `μ` on `T`. -/
def positivePoissonIntegral (μ : Measure UnitCircle) (z : ℂ) : ℝ :=
  ∫ η : UnitCircle, _root_.poissonKernel 0 z (η : ℂ) ∂μ

/-- Compatibility between `positivePoissonIntegral μ` and `poissonMeasureIntegral (μ.withDensityᵥ 1)`
for a positive finite Borel measure `μ` on `T`. -/
theorem poissonMeasureIntegral_withDensityᵥ_one (μ : Measure UnitCircle) [IsFiniteMeasure μ]
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    poissonMeasureIntegral (μ.withDensityᵥ fun _ : UnitCircle => (1 : ℂ)) z =
      (positivePoissonIntegral μ z : ℂ) := by
  unfold poissonMeasureIntegral RudinRCA.Chapter10.complexMeasureIntegral positivePoissonIntegral
  let ν : ComplexMeasure UnitCircle := μ.withDensityᵥ fun _ : UnitCircle => (1 : ℂ)
  obtain ⟨h, hm, hn, hi, hr_pol⟩ := RudinRCA.Chapter06.theorem_6_12 ν
  have : IsFiniteMeasure ν.variation := isFiniteMeasure_complexMeasure_variation ν
  have hK_cont : Continuous (fun η : UnitCircle => (_root_.poissonKernel 0 z (η : ℂ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_poissonKernel_unitCircle hz)
  have hpol := RudinRCA.Chapter06.vectorIntegral_eq_polar ν h hm hn hi hr_pol
    (hK_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  rw [hpol]
  -- Identify `ν.variation` with `μ` via `RudinRCA.Chapter06.theorem_6_13`
  have hvar : ν.variation = μ := by
    dsimp only [ν]
    rw [RudinRCA.Chapter06.theorem_6_13 μ (integrable_const (1 : ℂ))]
    simp
  rw [hvar] at hi hr_pol ⊢
  have huniv_eq : (∫ x, h x ∂μ) = ∫ _x, (1 : ℂ) ∂μ := by
    rw [← setIntegral_univ, ← withDensityᵥ_apply hi MeasurableSet.univ, hr_pol,
      withDensityᵥ_apply (integrable_const (1 : ℂ)) MeasurableSet.univ, setIntegral_univ]
  have hi_re : Integrable (fun x => (h x).re) μ := Complex.reCLM.integrable_comp hi
  have hre_zero : (∫ x, (1 - (h x).re) ∂μ) = 0 := by
    have hre := congrArg Complex.re huniv_eq
    rw [← RCLike.re_eq_complex_re, ← integral_re hi,
      ← integral_re (integrable_const (1 : ℂ))] at hre
    simp only [RCLike.re_eq_complex_re, Complex.one_re] at hre
    rw [integral_sub (integrable_const (1 : ℝ)) hi_re, hre, sub_self]
  have hre_nn : ∀ x : UnitCircle, 0 ≤ 1 - (h x).re := fun x => by
    linarith [Complex.re_le_norm (h x), hn x]
  have hre_ae : (fun x : UnitCircle => 1 - (h x).re) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg hre_nn ((integrable_const (1 : ℝ)).sub hi_re)).mp hre_zero
  have hh1 : h =ᵐ[μ] fun _ : UnitCircle => (1 : ℂ) := by
    filter_upwards [hre_ae] with x hx
    have hx_re : (h x).re = 1 := by dsimp at hx; linarith
    have hsq : (h x).re ^ 2 + (h x).im ^ 2 = 1 := by
      have hn1 : ‖h x‖ ^ 2 = 1 := by rw [hn x, one_pow]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hn1
      linarith
    have hx_im : (h x).im = 0 := by nlinarith
    exact Complex.ext hx_re hx_im
  have hcongr : (fun η : UnitCircle => (_root_.poissonKernel 0 z (η : ℂ) : ℂ) * h η) =ᵐ[μ]
      fun η : UnitCircle => (_root_.poissonKernel 0 z (η : ℂ) : ℂ) :=
    hh1.mono fun η hη => by dsimp at hη ⊢; rw [hη, mul_one]
  rw [integral_congr_ae hcongr]
  exact integral_ofReal

/-- Kernel inequality `11.20(2)`–`11.20(3)` (Rudin p. 242):
for `z ∈ approachRegion α ζ` (`0 < α < 1`) and `η ∈ T`,
`c_α P(z, η) ≤ P(‖z‖ ζ, η)`. -/
theorem poissonKernel_nontangential_le_radial {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ζ : UnitCircle} {z : ℂ} (hz : z ∈ approachRegion α ζ) (η : UnitCircle) :
    nontangentialConstant α * _root_.poissonKernel 0 z (η : ℂ) ≤
      _root_.poissonKernel 0 ((‖z‖ : ℂ) * (ζ : ℂ)) (η : ℂ) := by
  let r : ℝ := ‖z‖
  have hr0 : 0 ≤ r := norm_nonneg z
  have hr1 : r < 1 := by simpa [r, Metric.mem_ball] using approachRegion_subset_ball α ζ hz
  have h1mα : 0 < 1 - α := sub_pos.mpr hα1
  have h3mα : 0 < 3 - α := by linarith
  have hchord := norm_sub_vertex_le_of_mem_approachRegion hα0 hα1 hz
  have hrad_sub : ‖(ζ : ℂ) - (r : ℂ) * (ζ : ℂ)‖ = 1 - r := by
    have heq : (ζ : ℂ) - (r : ℂ) * (ζ : ℂ) = ((1 - r : ℝ) : ℂ) * (ζ : ℂ) := by
      push_cast; ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hr1),
      norm_unitCircle, mul_one]
  have h1mr_le : 1 - r ≤ ‖(η : ℂ) - z‖ := by
    have htri := norm_sub_norm_le (η : ℂ) z
    rwa [norm_unitCircle] at htri
  have h1mr_pos : 0 < 1 - r := sub_pos.mpr hr1
  have hden_z_pos : 0 < ‖(η : ℂ) - z‖ := lt_of_lt_of_le h1mr_pos h1mr_le
  have hden_r_pos : 0 < ‖(η : ℂ) - (r : ℂ) * (ζ : ℂ)‖ := by
    have htri := norm_sub_norm_le (η : ℂ) ((r : ℂ) * (ζ : ℂ))
    rw [norm_unitCircle, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      norm_unitCircle, mul_one] at htri
    linarith
  have hdist_le : ‖(η : ℂ) - (r : ℂ) * (ζ : ℂ)‖ ≤ ((3 - α) / (1 - α)) * ‖(η : ℂ) - z‖ := by
    calc ‖(η : ℂ) - (r : ℂ) * (ζ : ℂ)‖
        = ‖((η : ℂ) - z) + (z - (ζ : ℂ)) + ((ζ : ℂ) - (r : ℂ) * (ζ : ℂ))‖ := by ring_nf
      _ ≤ ‖((η : ℂ) - z) + (z - (ζ : ℂ))‖ + ‖(ζ : ℂ) - (r : ℂ) * (ζ : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖(η : ℂ) - z‖ + ‖z - (ζ : ℂ)‖ + (1 - r) := by
          rw [hrad_sub]
          linarith [norm_add_le ((η : ℂ) - z) (z - (ζ : ℂ))]
      _ ≤ ‖(η : ℂ) - z‖ + ((1 + α) / (1 - α)) * (1 - r) + (1 - r) := by
          linarith [hchord]
      _ = ‖(η : ℂ) - z‖ + (2 / (1 - α)) * (1 - r) := by
          field_simp [h1mα.ne']
          ring
      _ ≤ ‖(η : ℂ) - z‖ + (2 / (1 - α)) * ‖(η : ℂ) - z‖ := by
          linarith [mul_le_mul_of_nonneg_left h1mr_le (by positivity : (0 : ℝ) ≤ 2 / (1 - α))]
      _ = ((3 - α) / (1 - α)) * ‖(η : ℂ) - z‖ := by
          field_simp [h1mα.ne']
          ring
  have hsq_le : nontangentialConstant α * ‖(η : ℂ) - (r : ℂ) * (ζ : ℂ)‖ ^ 2 ≤
      ‖(η : ℂ) - z‖ ^ 2 := by
    unfold nontangentialConstant
    have hsq : ‖(η : ℂ) - (r : ℂ) * (ζ : ℂ)‖ ^ 2 ≤
        (((3 - α) / (1 - α)) * ‖(η : ℂ) - z‖) ^ 2 :=
      pow_le_pow_left₀ hden_r_pos.le hdist_le 2
    calc ((1 - α) / (3 - α)) ^ 2 * ‖(η : ℂ) - (r : ℂ) * (ζ : ℂ)‖ ^ 2
        ≤ ((1 - α) / (3 - α)) ^ 2 * (((3 - α) / (1 - α)) * ‖(η : ℂ) - z‖) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = ‖(η : ℂ) - z‖ ^ 2 := by
          field_simp [h1mα.ne', h3mα.ne']
  have hr_norm : ‖(r : ℂ) * (ζ : ℂ)‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, norm_unitCircle, mul_one]
  simp only [_root_.poissonKernel, sub_zero, norm_unitCircle, one_pow]
  rw [hr_norm]
  change nontangentialConstant α * ((1 - r ^ 2) / ‖(η : ℂ) - z‖ ^ 2) ≤
    (1 - r ^ 2) / ‖(η : ℂ) - (r : ℂ) * (ζ : ℂ)‖ ^ 2
  rw [← mul_div_assoc, div_le_div_iff₀ (sq_pos_of_pos hden_z_pos) (sq_pos_of_pos hden_r_pos)]
  have h1mr2_nn : 0 ≤ 1 - r ^ 2 := by nlinarith
  calc (nontangentialConstant α * (1 - r ^ 2)) * ‖(η : ℂ) - (r : ℂ) * (ζ : ℂ)‖ ^ 2
      = (1 - r ^ 2) * (nontangentialConstant α * ‖(η : ℂ) - (r : ℂ) * (ζ : ℂ)‖ ^ 2) := by ring
    _ ≤ (1 - r ^ 2) * ‖(η : ℂ) - z‖ ^ 2 := mul_le_mul_of_nonneg_left hsq_le h1mr2_nn

/-- Negative derivative `- P_r'(u)` of the radial Poisson kernel (`0 ≤ r < 1`). -/
private def poissonKernelNegDeriv (r u : ℝ) : ℝ :=
  (1 - r ^ 2) * (2 * r * Real.sin u) / (1 - 2 * r * Real.cos u + r ^ 2) ^ 2

private theorem hasDerivAt_poissonKernel_real {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (u : ℝ) :
    HasDerivAt (poissonKernel r) (-poissonKernelNegDeriv r u) u := by
  have hden_pos : 0 < 1 - 2 * r * Real.cos u + r ^ 2 := by
    have hterm : 0 ≤ 2 * r * (1 - Real.cos u) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one u))
    have hid : 1 - 2 * r * Real.cos u + r ^ 2 = (1 - r) ^ 2 + 2 * r * (1 - Real.cos u) := by ring
    linarith [sq_pos_of_pos (sub_pos.mpr hr1)]
  have hden_deriv : HasDerivAt (fun x : ℝ => 1 - 2 * r * Real.cos x + r ^ 2)
      (2 * r * Real.sin u) u := by
    have hcos := (Real.hasDerivAt_cos u).const_mul (2 * r)
    have hsub := (hasDerivAt_const u (1 : ℝ)).sub hcos
    have hadd := hsub.add (hasDerivAt_const u (r ^ 2))
    convert hadd using 1
    ring
  have hquot := (hasDerivAt_const u (1 - r ^ 2)).div hden_deriv hden_pos.ne'
  refine hquot.congr_deriv ?_
  unfold poissonKernelNegDeriv
  ring

private theorem poissonKernelNegDeriv_nonneg {r u : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hu0 : 0 ≤ u) (hupi : u ≤ Real.pi) :
    0 ≤ poissonKernelNegDeriv r u := by
  unfold poissonKernelNegDeriv
  have h1mr2 : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hsin : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi hu0 hupi
  exact div_nonneg (mul_nonneg h1mr2 (by positivity)) (sq_nonneg _)

private theorem continuous_poissonKernelNegDeriv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (poissonKernelNegDeriv r) := by
  unfold poissonKernelNegDeriv
  refine Continuous.div (by fun_prop) (by fun_prop) fun u => ?_
  have hden_pos : 0 < 1 - 2 * r * Real.cos u + r ^ 2 := by
    have hterm : 0 ≤ 2 * r * (1 - Real.cos u) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one u))
    have hid : 1 - 2 * r * Real.cos u + r ^ 2 = (1 - r) ^ 2 + 2 * r * (1 - Real.cos u) := by ring
    linarith [sq_pos_of_pos (sub_pos.mpr hr1)]
  exact (sq_pos_of_pos hden_pos).ne'

private theorem poissonKernel_eq_pi_add_integral {r s : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    poissonKernel r s =
      poissonKernel r Real.pi + ∫ u in s..Real.pi, poissonKernelNegDeriv r u := by
  have hcont : Continuous (fun u : ℝ => -poissonKernelNegDeriv r u) :=
    (continuous_poissonKernelNegDeriv hr0 hr1).neg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_poissonKernel_real hr0 hr1 u) (hcont.intervalIntegrable s Real.pi)
  rw [intervalIntegral.integral_neg] at hftc
  linarith

/-- Exact Tonelli layer-cake identity on `T = UnitCircle` for any positive finite Borel measure `ν`
(`0 ≤ r < 1`):
`∫⁻ η, P(r ζ, η) dν(η) = P_r(π) ν(T) + ∫⁻_{u ∈ (0, π)} (-P_r'(u)) ν(openCircleArc ζ u) du`. -/
private theorem lintegral_poissonKernel_eq_layerCake (ν : Measure UnitCircle) [IsFiniteMeasure ν]
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ζ : UnitCircle) :
    (∫⁻ η : UnitCircle,
        ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ)) ∂ν) =
      ENNReal.ofReal (poissonKernel r Real.pi) * ν Set.univ +
        ∫⁻ u in Set.Ioo (0 : ℝ) Real.pi,
          ENNReal.ofReal (poissonKernelNegDeriv r u) * ν (openCircleArc ζ u) := by
  let μ₀ : Measure ℝ := MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) Real.pi)
  let S_pair : Set (UnitCircle × ℝ) :=
    {p : UnitCircle × ℝ | ‖(p.1 : ℂ) - (ζ : ℂ)‖ ^ 2 < 2 * (1 - Real.cos p.2)}
  have hS_open : IsOpen S_pair := isOpen_lt
    ((((continuous_subtype_val.comp continuous_fst).sub continuous_const).norm).pow 2)
    (continuous_const.mul (continuous_const.sub (Real.continuous_cos.comp continuous_snd)))
  let K_ind : UnitCircle × ℝ → ℝ≥0∞ :=
    S_pair.indicator fun p => ENNReal.ofReal (poissonKernelNegDeriv r p.2)
  have hK_meas : Measurable K_ind :=
    (((continuous_poissonKernelNegDeriv hr0 hr1).comp continuous_snd).measurable.ennreal_ofReal).indicator
      hS_open.measurableSet
  -- Pointwise layer-cake representation at every `η ∈ UnitCircle`
  have hpt : ∀ η : UnitCircle,
      ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ)) =
        ENNReal.ofReal (poissonKernel r Real.pi) + ∫⁻ u, K_ind (η, u) ∂μ₀ := by
    intro η
    let w : ℂ := (η : ℂ) * conj (ζ : ℂ)
    have hw_norm : ‖w‖ = 1 := by
      dsimp only [w]
      rw [norm_mul, RCLike.norm_conj, norm_unitCircle, norm_unitCircle, mul_one]
    let θ : ℝ := |Complex.arg w|
    have hθ0 : 0 ≤ θ := abs_nonneg _
    have hθpi : θ ≤ Real.pi :=
      abs_le.mpr ⟨(Complex.neg_pi_lt_arg w).le, Complex.arg_le_pi w⟩
    have hexp_w : Complex.exp ((Complex.arg w : ℂ) * Complex.I) = w := by
      have h := Complex.norm_mul_exp_arg_mul_I w
      rwa [hw_norm, Complex.ofReal_one, one_mul] at h
    have hPK_eq : _root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ) = poissonKernel r θ := by
      have hsub_eq : ‖(η : ℂ) - (r : ℂ) * (ζ : ℂ)‖ ^ 2 = 1 - 2 * r * Real.cos θ + r ^ 2 := by
        have hfac : (η : ℂ) - (r : ℂ) * (ζ : ℂ) = (w - (r : ℂ)) * (ζ : ℂ) := by
          dsimp only [w]
          calc (η : ℂ) - (r : ℂ) * (ζ : ℂ)
              = (η : ℂ) * ((ζ : ℂ) * conj (ζ : ℂ)) - (r : ℂ) * (ζ : ℂ) := by
                  rw [unitCircle_mul_conj ζ, mul_one]
            _ = ((η : ℂ) * conj (ζ : ℂ) - (r : ℂ)) * (ζ : ℂ) := by ring
        rw [hfac, norm_mul, norm_unitCircle, mul_one, ← hexp_w, ← Complex.normSq_eq_norm_sq,
          Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
          Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sub_zero,
          θ, Real.cos_abs]
        have hcs := Real.sin_sq_add_cos_sq (Complex.arg w)
        nlinarith
      have hr_norm : ‖(r : ℂ) * (ζ : ℂ)‖ = r := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, norm_unitCircle, mul_one]
      simp only [_root_.poissonKernel, poissonKernel, sub_zero, norm_unitCircle, one_pow]
      rw [hr_norm, hsub_eq]
    have hchord_η : ‖(η : ℂ) - (ζ : ℂ)‖ ^ 2 = 2 * (1 - Real.cos θ) := by
      have hfac : (η : ℂ) - (ζ : ℂ) = (w - 1) * (ζ : ℂ) := by
        dsimp only [w]
        calc (η : ℂ) - (ζ : ℂ)
            = (η : ℂ) * ((ζ : ℂ) * conj (ζ : ℂ)) - (ζ : ℂ) := by
                rw [unitCircle_mul_conj ζ, mul_one]
          _ = ((η : ℂ) * conj (ζ : ℂ) - 1) * (ζ : ℂ) := by ring
      rw [hfac, norm_mul, norm_unitCircle, mul_one, ← hexp_w, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sub_zero,
        θ, Real.cos_abs]
      have hcs := Real.sin_sq_add_cos_sq (Complex.arg w)
      nlinarith
    have hlint_u : (∫⁻ u, K_ind (η, u) ∂μ₀) =
        ENNReal.ofReal (∫ u in θ..Real.pi, poissonKernelNegDeriv r u) := by
      have hind_eq : (fun u : ℝ => K_ind (η, u)) =ᵐ[μ₀]
          (Set.Ioo θ Real.pi).indicator
            (fun u => ENNReal.ofReal (poissonKernelNegDeriv r u)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        have hmem_iff : (η, u) ∈ S_pair ↔ u ∈ Set.Ioo θ Real.pi := by
          dsimp only [S_pair]
          rw [Set.mem_ofPred_eq, hchord_η, Set.mem_Ioo]
          refine ⟨fun hlt => ⟨?_, hu.2⟩, fun ⟨hgt, _⟩ => ?_⟩
          · by_contra hle
            push Not at hle
            have hanti := Real.strictAntiOn_cos.antitoneOn ⟨hu.1.le, hu.2.le⟩ ⟨hθ0, hθpi⟩ hle
            linarith
          · have hgt_cos := Real.strictAntiOn_cos ⟨hθ0, hθpi⟩ ⟨hu.1.le, hu.2.le⟩ hgt
            linarith
        by_cases hmem : u ∈ Set.Ioo θ Real.pi
        · simp only [K_ind, Set.indicator_of_mem (hmem_iff.mpr hmem), Set.indicator_of_mem hmem]
        · simp only [K_ind, Set.indicator_of_notMem (mt hmem_iff.mp hmem),
            Set.indicator_of_notMem hmem]
      rw [lintegral_congr_ae hind_eq]
      dsimp only [μ₀]
      rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
      have hinter : Set.Ioo θ Real.pi ∩ Set.Ioo (0 : ℝ) Real.pi = Set.Ioo θ Real.pi :=
        Set.inter_eq_self_of_subset_left (Set.Ioo_subset_Ioo_left hθ0)
      rw [hinter]
      have hint_q : IntegrableOn (poissonKernelNegDeriv r) (Set.Ioo θ Real.pi) MeasureTheory.volume :=
        (continuous_poissonKernelNegDeriv hr0 hr1).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
      have hnn_q : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo θ Real.pi)]
          poissonKernelNegDeriv r :=
        ae_restrict_of_forall_mem measurableSet_Ioo fun u hu =>
          poissonKernelNegDeriv_nonneg hr0 hr1 (hθ0.trans hu.1.le) hu.2.le
      rw [← ofReal_integral_eq_lintegral_ofReal hint_q hnn_q,
        ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hθpi]
    have hPpi_nn : 0 ≤ poissonKernel r Real.pi := (node11_5_pos hr0 hr1 Real.pi).le
    have hint_nn : 0 ≤ ∫ u in θ..Real.pi, poissonKernelNegDeriv r u :=
      intervalIntegral.integral_nonneg hθpi fun u hu =>
        poissonKernelNegDeriv_nonneg hr0 hr1 (hθ0.trans hu.1) hu.2
    rw [hPK_eq, poissonKernel_eq_pi_add_integral hr0 hr1, ENNReal.ofReal_add hPpi_nn hint_nn,
      hlint_u]
  -- Integrate `hpt` over `ν` and swap via Tonelli
  calc (∫⁻ η : UnitCircle,
          ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ)) ∂ν)
      = ∫⁻ η : UnitCircle,
          (ENNReal.ofReal (poissonKernel r Real.pi) + ∫⁻ u, K_ind (η, u) ∂μ₀) ∂ν :=
        lintegral_congr hpt
    _ = ENNReal.ofReal (poissonKernel r Real.pi) * ν Set.univ +
          ∫⁻ η : UnitCircle, ∫⁻ u, K_ind (η, u) ∂μ₀ ∂ν := by
        rw [lintegral_add_left measurable_const, lintegral_const]
    _ = ENNReal.ofReal (poissonKernel r Real.pi) * ν Set.univ +
          ∫⁻ u, ∫⁻ η : UnitCircle, K_ind (η, u) ∂ν ∂μ₀ := by
        rw [lintegral_lintegral_swap (f := fun η u => K_ind (η, u)) hK_meas.aemeasurable]
    _ = ENNReal.ofReal (poissonKernel r Real.pi) * ν Set.univ +
          ∫⁻ u in Set.Ioo (0 : ℝ) Real.pi,
            ENNReal.ofReal (poissonKernelNegDeriv r u) * ν (openCircleArc ζ u) := by
        congr 1
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        have hind_u : (fun η : UnitCircle => K_ind (η, u)) =
            (openCircleArc ζ u).indicator
              (fun _ => ENNReal.ofReal (poissonKernelNegDeriv r u)) := by
          ext η
          have hiff : (η, u) ∈ S_pair ↔ η ∈ openCircleArc ζ u :=
            (mem_openCircleArc_iff_chordal hu.1 hu.2.le).symm
          by_cases hη : η ∈ openCircleArc ζ u
          · simp only [K_ind, Set.indicator_of_mem (hiff.mpr hη), Set.indicator_of_mem hη]
          · simp only [K_ind, Set.indicator_of_notMem (mt hiff.mp hη), Set.indicator_of_notMem hη]
        rw [hind_u, lintegral_indicator (isOpen_openCircleArc ζ u).measurableSet, lintegral_const,
          Measure.restrict_apply_univ]

/-- Radial-by-maximal domination `11.20(4)` (Rudin pp. 242–243):
for every positive Borel measure `μ` on `T`, `0 ≤ r < 1`, and `ζ ∈ T`,
`∫⁻ η, P(r ζ, η) dμ(η) ≤ (M μ)(ζ)`. -/
theorem lintegral_poissonKernel_le_circleMeasureMaximal (μ : Measure UnitCircle)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ζ : UnitCircle) :
    (∫⁻ η : UnitCircle,
        ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ)) ∂μ) ≤
      circleMeasureMaximal μ ζ := by
  let M : ℝ≥0∞ := circleMeasureMaximal μ ζ
  by_cases hM_top : M = ⊤
  · simp [M, hM_top]
  · have harc_bound : ∀ {δ : ℝ}, 0 < δ →
        μ (openCircleArc ζ δ) ≤ M * unitCircleMeasure (openCircleArc ζ δ) := by
      intro δ hδ
      have hdiv_le : μ (openCircleArc ζ δ) / unitCircleMeasure (openCircleArc ζ δ) ≤ M :=
        le_iSup₂_of_le δ hδ le_rfl
      have heq : (μ (openCircleArc ζ δ) / unitCircleMeasure (openCircleArc ζ δ)) *
          unitCircleMeasure (openCircleArc ζ δ) = μ (openCircleArc ζ δ) :=
        ENNReal.div_mul_cancel (unitCircleMeasure_openCircleArc_ne_zero ζ hδ) (measure_ne_top _ _)
      rw [← heq]
      exact mul_le_mul_of_nonneg_right hdiv_le zero_le
    have huniv_bound : μ Set.univ ≤ M * unitCircleMeasure Set.univ := by
      have huniv : openCircleArc ζ (2 * Real.pi) = Set.univ :=
        openCircleArc_eq_univ ζ (by linarith [Real.pi_pos])
      rw [← huniv]
      exact harc_bound (by linarith [Real.pi_pos])
    have : IsFiniteMeasure μ := ⟨lt_of_le_of_lt
      (by simpa [unitCircleMeasure_univ] using huniv_bound) (lt_top_iff_ne_top.mpr hM_top)⟩
    rw [lintegral_poissonKernel_eq_layerCake μ hr0 hr1 ζ]
    calc ENNReal.ofReal (poissonKernel r Real.pi) * μ Set.univ +
            ∫⁻ u in Set.Ioo (0 : ℝ) Real.pi,
              ENNReal.ofReal (poissonKernelNegDeriv r u) * μ (openCircleArc ζ u)
        ≤ ENNReal.ofReal (poissonKernel r Real.pi) * (M * unitCircleMeasure Set.univ) +
            ∫⁻ u in Set.Ioo (0 : ℝ) Real.pi,
              M * (ENNReal.ofReal (poissonKernelNegDeriv r u) *
                unitCircleMeasure (openCircleArc ζ u)) := by
          refine add_le_add (mul_le_mul_of_nonneg_left huniv_bound zero_le) ?_
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
          calc ENNReal.ofReal (poissonKernelNegDeriv r u) * μ (openCircleArc ζ u)
              ≤ ENNReal.ofReal (poissonKernelNegDeriv r u) *
                  (M * unitCircleMeasure (openCircleArc ζ u)) :=
                mul_le_mul_of_nonneg_left (harc_bound hu.1) zero_le
            _ = M * (ENNReal.ofReal (poissonKernelNegDeriv r u) *
                  unitCircleMeasure (openCircleArc ζ u)) := by ac_rfl
      _ = M * (ENNReal.ofReal (poissonKernel r Real.pi) * unitCircleMeasure Set.univ +
            ∫⁻ u in Set.Ioo (0 : ℝ) Real.pi,
              ENNReal.ofReal (poissonKernelNegDeriv r u) * unitCircleMeasure (openCircleArc ζ u)) := by
          rw [lintegral_const_mul' M _ hM_top, mul_add]
          congr 1
          ac_rfl
      _ = M := by
          rw [← lintegral_poissonKernel_eq_layerCake unitCircleMeasure hr0 hr1 ζ,
            lintegral_poissonKernel_unitCircle (radial_mem_ball_unitCircle hr0 hr1 ζ), mul_one]

/-- 11.20 (Theorem, Rudin pp. 242–243):
Assume `0 < α < 1`. Then there is a constant `c_α > 0` (`nontangentialConstant α`) such that
for every positive finite Borel measure `μ` on `T = UnitCircle`, `u = P[dμ]`, and every `ζ ∈ T`,
`c_α (N_α u)(ζ) ≤ (M_rad u)(ζ) ≤ (M μ)(ζ)`. -/
theorem theorem11_20_explicit {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (μ : Measure UnitCircle) [IsFiniteMeasure μ] (ζ : UnitCircle) :
    let u : ℂ → ℂ := poissonMeasureIntegral (μ.withDensityᵥ fun _ : UnitCircle => (1 : ℂ))
    ENNReal.ofReal (nontangentialConstant α) * nontangentialMaximal α u ζ ≤ radialMaximal u ζ ∧
    radialMaximal u ζ ≤ circleMeasureMaximal μ ζ := by
  intro u
  have hc_pos : 0 < nontangentialConstant α := nontangentialConstant_pos hα1
  have hu_enorm : ∀ {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1),
      ‖u z‖ₑ = ∫⁻ η : UnitCircle, ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) ∂μ := by
    intro z hz
    dsimp only [u]
    rw [poissonMeasureIntegral_withDensityᵥ_one μ hz, ← ofReal_norm, Complex.norm_real,
      Real.norm_eq_abs]
    have hnn : 0 ≤ positivePoissonIntegral μ z :=
      integral_nonneg (poissonKernel_unitCircle_nonneg hz)
    rw [abs_of_nonneg hnn]
    unfold positivePoissonIntegral
    have hint : Integrable (fun η : UnitCircle => _root_.poissonKernel 0 z (η : ℂ)) μ :=
      (continuous_poissonKernel_unitCircle hz).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    exact ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ (poissonKernel_unitCircle_nonneg hz))
  refine ⟨?_, ?_⟩
  · unfold nontangentialMaximal
    rw [ENNReal.mul_iSup]
    refine iSup_le fun z => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hz => ?_
    have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := approachRegion_subset_ball α ζ hz
    let r : ℝ := ‖z‖
    have hr0 : 0 ≤ r := norm_nonneg z
    have hr1 : r < 1 := by simpa [r, Metric.mem_ball] using hz_ball
    rw [hu_enorm hz_ball, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hle : (∫⁻ η : UnitCircle,
          ENNReal.ofReal (nontangentialConstant α) *
            ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) ∂μ) ≤
        ∫⁻ η : UnitCircle,
          ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ)) ∂μ := by
      refine lintegral_mono fun η => ?_
      rw [← ENNReal.ofReal_mul hc_pos.le]
      exact ENNReal.ofReal_le_ofReal (poissonKernel_nontangential_le_radial hα0 hα1 hz η)
    refine hle.trans ?_
    rw [← hu_enorm (radial_mem_ball_unitCircle hr0 hr1 ζ)]
    exact le_iSup₂_of_le r ⟨hr0, hr1⟩ le_rfl
  · unfold radialMaximal
    refine iSup₂_le fun r hr => ?_
    rw [hu_enorm (radial_mem_ball_unitCircle hr.1 hr.2 ζ)]
    exact lintegral_poissonKernel_le_circleMeasureMaximal μ hr.1 hr.2 ζ

/-- 11.20 (Existential form matching Rudin's printed statement verbatim, p. 242). -/
theorem theorem11_20 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ c_α : ℝ, 0 < c_α ∧
      ∀ (μ : Measure UnitCircle) [IsFiniteMeasure μ] (ζ : UnitCircle),
        let u : ℂ → ℂ := poissonMeasureIntegral (μ.withDensityᵥ fun _ : UnitCircle => (1 : ℂ))
        ENNReal.ofReal c_α * nontangentialMaximal α u ζ ≤ radialMaximal u ζ ∧
        radialMaximal u ζ ≤ circleMeasureMaximal μ ζ :=
  ⟨nontangentialConstant α, nontangentialConstant_pos hα1,
    fun μ _ ζ => theorem11_20_explicit hα0 hα1 μ ζ⟩

end Node11_20

/-! ### Stage 3 Block 3: Nontangential Limits, Fatou Theorems, and Maximal Inequalities (Nodes 11.21–11.25) -/

section Node11_21

/-- For `α ≤ 0`, `approachRegion α ζ = ∅` because `Metric.ball 0 α = ∅` and `ζ ∉ Metric.ball 0 1`. -/
theorem approachRegion_eq_empty_of_nonpos {α : ℝ} (hα : α ≤ 0) (ζ : UnitCircle) :
    approachRegion α ζ = ∅ := by
  unfold approachRegion
  rw [Metric.ball_eq_empty.mpr hα, Set.empty_union, convexHull_singleton]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Metric.mem_ball, dist_zero_right,
    Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl
  rw [norm_unitCircle]
  exact lt_irrefl 1

/-- 11.21 (Definition, Rudin p. 243): a function `F` has nontangential limit `L` at `ζ ∈ T` if,
for each `α < 1`, `lim_{j → ∞} F(z_j) = L` for every sequence `{z_j}` in `ζ Ω_α` converging to `ζ`. -/
def HasNontangentialLimit {E : Type*} [TopologicalSpace E]
    (F : ℂ → E) (ζ : UnitCircle) (L : E) : Prop :=
  ∀ α < (1 : ℝ), ∀ z : ℕ → ℂ,
    (∀ j : ℕ, z j ∈ approachRegion α ζ) →
    Tendsto z atTop (𝓝 (ζ : ℂ)) →
    Tendsto (fun j : ℕ => F (z j)) atTop (𝓝 L)

/-- Equivalence with restricting `α ∈ (0, 1)` (since `approachRegion α ζ = ∅` for `α ≤ 0`). -/
theorem hasNontangentialLimit_iff_Ioo {E : Type*} [TopologicalSpace E]
    (F : ℂ → E) (ζ : UnitCircle) (L : E) :
    HasNontangentialLimit F ζ L ↔
      ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ z : ℕ → ℂ,
        (∀ j : ℕ, z j ∈ approachRegion α ζ) →
        Tendsto z atTop (𝓝 (ζ : ℂ)) →
        Tendsto (fun j : ℕ => F (z j)) atTop (𝓝 L) := by
  refine ⟨fun h α hα => h α hα.2, fun h α hα1 z hz hlim => ?_⟩
  rcases le_or_gt α 0 with hα0 | hα0
  · exfalso
    have h0 := hz 0
    rw [approachRegion_eq_empty_of_nonpos hα0 ζ] at h0
    exact h0
  · exact h α ⟨hα0, hα1⟩ z hz hlim

/-- Filter characterization of `HasNontangentialLimit`: for each `0 < α < 1`, `F` tends to `L`
along the punctured/restricted neighborhood filter `𝓝[approachRegion α ζ] (ζ : ℂ)`. -/
theorem hasNontangentialLimit_iff_nhdsWithin {E : Type*} [TopologicalSpace E]
    (F : ℂ → E) (ζ : UnitCircle) (L : E) :
    HasNontangentialLimit F ζ L ↔
      ∀ α ∈ Set.Ioo (0 : ℝ) 1, Tendsto F (𝓝[approachRegion α ζ] (ζ : ℂ)) (𝓝 L) := by
  rw [hasNontangentialLimit_iff_Ioo]
  refine forall₂_congr fun α _ => ?_
  rw [Filter.tendsto_iff_seq_tendsto]
  constructor
  · intro h z hz_lim
    rw [tendsto_nhdsWithin_iff] at hz_lim
    obtain ⟨hz_nhds, hz_ev⟩ := hz_lim
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hz_ev
    let z' : ℕ → ℂ := fun j => z (j + N)
    have hz'_mem : ∀ j : ℕ, z' j ∈ approachRegion α ζ := fun j => hN (j + N) (Nat.le_add_left N j)
    have hz'_lim : Tendsto z' atTop (𝓝 (ζ : ℂ)) :=
      hz_nhds.comp (tendsto_add_atTop_nat N)
    have hF' : Tendsto (fun j : ℕ => F (z (j + N))) atTop (𝓝 L) := h z' hz'_mem hz'_lim
    exact (tendsto_add_atTop_iff_nat N).mp hF'
  · intro h z hz_mem hz_nhds
    exact h z (tendsto_nhdsWithin_iff.mpr ⟨hz_nhds, Filter.Eventually.of_forall hz_mem⟩)

/-- Congruence of `HasNontangentialLimit` for functions agreeing on `U = Metric.ball 0 1`. -/
theorem HasNontangentialLimit.congr_ball {E : Type*} [TopologicalSpace E]
    {F G : ℂ → E} {ζ : UnitCircle} {L : E}
    (hF : HasNontangentialLimit F ζ L)
    (heq : ∀ z ∈ Metric.ball (0 : ℂ) 1, F z = G z) :
    HasNontangentialLimit G ζ L := by
  intro α hα1 z hz hlim
  refine (hF α hα1 z hz hlim).congr fun j => ?_
  exact heq (z j) (approachRegion_subset_ball α ζ (hz j))

/-- Nontangential limit implies radial limit as `r → 1⁻`. -/
theorem HasNontangentialLimit.tendsto_radial {E : Type*} [TopologicalSpace E]
    {F : ℂ → E} {ζ : UnitCircle} {L : E}
    (hF : HasNontangentialLimit F ζ L) :
    Tendsto (fun r : ℝ => F ((r : ℂ) * (ζ : ℂ))) (𝓝[<] 1) (𝓝 L) := by
  have hnhds := (hasNontangentialLimit_iff_nhdsWithin F ζ L).mp hF
    (1 / 2) ⟨by norm_num, by norm_num⟩
  have hmap : Tendsto (fun r : ℝ => (r : ℂ) * (ζ : ℂ)) (𝓝[<] 1)
      (𝓝[approachRegion (1 / 2) ζ] (ζ : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Continuous (fun r : ℝ => (r : ℂ) * (ζ : ℂ)) :=
        Complex.continuous_ofReal.mul continuous_const
      simpa using hcont.tendsto 1 |>.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r ⟨hr0, hr1⟩
      exact radial_mem_approachRegion (by norm_num) (by norm_num) hr0.le hr1 ζ
  exact hnhds.comp hmap

/-- 11.21 (Summary Theorem): equivalence of sequential `α < 1`, sequential `0 < α < 1`, and
filter `𝓝[approachRegion α ζ] ζ` formulations of nontangential limits, together with implication
to the radial limit `lim_{r → 1⁻} F(r ζ) = L`. -/
theorem theorem11_21 {E : Type*} [TopologicalSpace E] (F : ℂ → E) (ζ : UnitCircle) (L : E) :
    (HasNontangentialLimit F ζ L ↔
      ∀ α ∈ Set.Ioo (0 : ℝ) 1, Tendsto F (𝓝[approachRegion α ζ] (ζ : ℂ)) (𝓝 L)) ∧
    (HasNontangentialLimit F ζ L →
      Tendsto (fun r : ℝ => F ((r : ℂ) * (ζ : ℂ))) (𝓝[<] 1) (𝓝 L)) :=
  ⟨hasNontangentialLimit_iff_nhdsWithin F ζ L, HasNontangentialLimit.tendsto_radial⟩

end Node11_21

section Node11_22

/-- Lower bound `_root_.poissonKernel 0 z η ≥ (1 - ‖z‖) / (1 + ‖z‖) > 0` on `T = UnitCircle`
for every `z ∈ Metric.ball 0 1`. -/
theorem poissonKernel_unitCircle_ge {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) (η : UnitCircle) :
    (1 - ‖z‖) / (1 + ‖z‖) ≤ _root_.poissonKernel 0 z (η : ℂ) := by
  have hz_lt : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
  have hz_nn : 0 ≤ ‖z‖ := norm_nonneg z
  have h1pz_pos : 0 < 1 + ‖z‖ := by linarith
  have h1mz_pos : 0 < 1 - ‖z‖ := sub_pos.mpr hz_lt
  have hsub_pos : 0 < ‖(η : ℂ) - z‖ := by
    have htri := norm_sub_norm_le (η : ℂ) z
    rw [norm_unitCircle] at htri
    linarith
  have hsub_le : ‖(η : ℂ) - z‖ ≤ 1 + ‖z‖ := by
    calc ‖(η : ℂ) - z‖ ≤ ‖(η : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ = 1 + ‖z‖ := by rw [norm_unitCircle]
  simp only [_root_.poissonKernel, sub_zero, norm_unitCircle, one_pow]
  rw [div_le_div_iff₀ h1pz_pos (sq_pos_of_pos hsub_pos)]
  have hsq : ‖(η : ℂ) - z‖ ^ 2 ≤ (1 + ‖z‖) ^ 2 :=
    pow_le_pow_left₀ hsub_pos.le hsub_le 2
  calc (1 - ‖z‖) * ‖(η : ℂ) - z‖ ^ 2
      ≤ (1 - ‖z‖) * (1 + ‖z‖) ^ 2 := mul_le_mul_of_nonneg_left hsq h1mz_pos.le
    _ = (1 - ‖z‖ ^ 2) * (1 + ‖z‖) := by ring

/-- Upper bound `_root_.poissonKernel 0 z η ≤ (1 - ‖z‖ ^ 2) / δ ^ 2` whenever `‖η - z‖ ≥ δ > 0`. -/
theorem poissonKernel_unitCircle_le_of_dist_ge {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1)
    {η : UnitCircle} {δ : ℝ} (hδ : 0 < δ) (hge : δ ≤ ‖(η : ℂ) - z‖) :
    _root_.poissonKernel 0 z (η : ℂ) ≤ (1 - ‖z‖ ^ 2) / δ ^ 2 := by
  have hz_lt : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
  have h1mz2 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  simp only [_root_.poissonKernel, sub_zero, norm_unitCircle, one_pow]
  exact div_le_div_of_nonneg_left h1mz2 (sq_pos_of_pos hδ) (pow_le_pow_left₀ hδ.le hge 2)

/-- Any positive Borel measure `μ` on `T` with `μ(T) = ∞` has infinite Lebesgue Poisson integral
`∫⁻ η, P(z, η) dμ(η) = ⊤` (and non-integrable kernel) at every `z ∈ U = Metric.ball 0 1`. -/
theorem lintegral_poissonKernel_eq_top_of_measure_univ_eq_top
    (μ : Measure UnitCircle) (hμ : μ Set.univ = ⊤)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    (∫⁻ η : UnitCircle, ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) ∂μ) = ⊤ ∧
    ¬ Integrable (fun η : UnitCircle => _root_.poissonKernel 0 z (η : ℂ)) μ := by
  have hz_lt : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
  let c : ℝ := (1 - ‖z‖) / (1 + ‖z‖)
  have hc_pos : 0 < c := div_pos (sub_pos.mpr hz_lt) (by linarith [norm_nonneg z])
  have hc_ne0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc_pos).ne'
  have htop : (∫⁻ η : UnitCircle, ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) ∂μ) = ⊤ := by
    apply eq_top_iff.mpr
    calc (⊤ : ℝ≥0∞)
        = ENNReal.ofReal c * μ Set.univ := by rw [hμ, ENNReal.mul_top hc_ne0]
      _ = ∫⁻ _η : UnitCircle, ENNReal.ofReal c ∂μ := (lintegral_const _).symm
      _ ≤ ∫⁻ η : UnitCircle, ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) ∂μ :=
          lintegral_mono fun η => ENNReal.ofReal_le_ofReal (poissonKernel_unitCircle_ge hz η)
  refine ⟨htop, fun hint => ?_⟩
  have hlt := hint.hasFiniteIntegral
  unfold HasFiniteIntegral at hlt
  have heq : (∫⁻ η : UnitCircle, ‖_root_.poissonKernel 0 z (η : ℂ)‖ₑ ∂μ) =
      ∫⁻ η : UnitCircle, ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) ∂μ := by
    refine lintegral_congr fun η => ?_
    rw [Real.enorm_of_nonneg (poissonKernel_unitCircle_nonneg hz η)]
  rw [heq, htop] at hlt
  exact lt_irrefl ⊤ hlt

/-- Fidelity disclosure counterexample for literal 11.22 without finiteness of `μ` (`E-11.22`):
Rudin's statement of 11.22 writes "positive Borel measure on `T`" without printing "finite"
(whereas `11.17` defines `P[dμ]` only for complex — hence finite — Borel measures, `11.20` assumes
"positive finite Borel measure", and Exercise 4 on p. 249 specifies "every finite Borel measure").
If `μ` is allowed to be an infinite positive Borel measure on `T`, e.g. counting measure restricted
to the complement of `openCircleArc 1 (π / 4)`, then `(Dμ)(1) = 0` (`μ(I_δ) = 0` for `0 < δ < π/4`),
yet `∫⁻_T P(z, η) dμ(η) = ∞` at every `z ∈ U`, so the `[0, ∞]`-valued Poisson integral does not
have nontangential limit `0` at `1`. -/
theorem node11_22_infinite_measure_counterexample :
    ∃ μ : Measure UnitCircle,
      HasPositiveCircleSymmetricDerivAt μ unitCircleOne 0 ∧
      μ Set.univ = ⊤ ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1,
        (∫⁻ η : UnitCircle, ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) ∂μ) = ⊤) ∧
      ¬ HasNontangentialLimit
          (fun z : ℂ => ∫⁻ η : UnitCircle, ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) ∂μ)
          unitCircleOne 0 := by
  let J : Set UnitCircle := (openCircleArc unitCircleOne (Real.pi / 4))ᶜ
  let μ : Measure UnitCircle := Measure.count.restrict J
  have hJ_meas : MeasurableSet J := (isOpen_openCircleArc unitCircleOne (Real.pi / 4)).measurableSet.compl
  -- Show `J` is infinite by exhibiting an injective family `n ↦ exp(i (π / 2 + 1 / (n + 4)))` in `J`
  have hJ_inf : J.Infinite := by
    let θ : ℕ → ℝ := fun n => Real.pi / 2 + 1 / ((n : ℝ) + 4)
    let φ : ℕ → UnitCircle := fun n =>
      ⟨Complex.exp ((θ n : ℂ) * Complex.I), by simp [Complex.norm_exp_ofReal_mul_I]⟩
    have hθ_bounds : ∀ n : ℕ, Real.pi / 2 < θ n ∧ θ n < Real.pi := fun n => by
      dsimp only [θ]
      have hpos : 0 < 1 / ((n : ℝ) + 4) := by positivity
      have hle : 1 / ((n : ℝ) + 4) ≤ 1 / 4 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
      exact ⟨by linarith, by linarith [Real.two_le_pi]⟩
    have hφ_mem : ∀ n : ℕ, φ n ∈ J := fun n hmem => by
      have hpi4 : 0 < Real.pi / 4 := by positivity
      have hpi4_le : Real.pi / 4 ≤ Real.pi := by linarith [Real.pi_pos]
      rw [mem_openCircleArc_iff_chordal hpi4 hpi4_le] at hmem
      have hnorm : ‖((φ n : UnitCircle) : ℂ) - (unitCircleOne : ℂ)‖ ^ 2 =
          2 * (1 - Real.cos (θ n)) := by
        dsimp only [φ]
        rw [coe_unitCircleOne, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
          Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sub_zero]
        have hcs := Real.sin_sq_add_cos_sq (θ n)
        nlinarith
      rw [hnorm] at hmem
      have hhb := hθ_bounds n
      have hcos_lt : Real.cos (θ n) < Real.cos (Real.pi / 4) :=
        Real.strictAntiOn_cos ⟨by positivity, hpi4_le⟩ ⟨by linarith, hhb.2.le⟩
          (by linarith)
      linarith
    have hφ_inj : Function.Injective φ := fun m n hmn => by
      have hexp : Complex.exp ((θ m : ℂ) * Complex.I) = Complex.exp ((θ n : ℂ) * Complex.I) :=
        congrArg Subtype.val hmn
      have hcos : Real.cos (θ m) = Real.cos (θ n) := by
        simpa [Complex.exp_ofReal_mul_I_re] using congrArg Complex.re hexp
      have hθ_eq : θ m = θ n :=
        Real.strictAntiOn_cos.injOn
          ⟨by linarith [(hθ_bounds m).1, Real.pi_pos], (hθ_bounds m).2.le⟩
          ⟨by linarith [(hθ_bounds n).1, Real.pi_pos], (hθ_bounds n).2.le⟩ hcos
      dsimp only [θ] at hθ_eq
      have hinv : (1 : ℝ) / ((m : ℝ) + 4) = 1 / ((n : ℝ) + 4) := by linarith
      have hm4 : (0 : ℝ) < (m : ℝ) + 4 := by positivity
      have hn4 : (0 : ℝ) < (n : ℝ) + 4 := by positivity
      have hden : (m : ℝ) + 4 = (n : ℝ) + 4 := by
        have hmul := congrArg (fun x => x * ((m : ℝ) + 4) * ((n : ℝ) + 4)) hinv
        field_simp [hm4.ne', hn4.ne'] at hmul
        linarith
      have hcast : (m : ℝ) = (n : ℝ) := by linarith
      exact Nat.cast_injective hcast
    exact Set.infinite_of_injective_forall_mem hφ_inj hφ_mem
  have hμ_univ : μ Set.univ = ⊤ := by
    dsimp only [μ]
    rw [Measure.restrict_apply_univ, Measure.count_apply_infinite hJ_inf]
  have hderiv0 : HasPositiveCircleSymmetricDerivAt μ unitCircleOne 0 := by
    unfold HasPositiveCircleSymmetricDerivAt
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < Real.pi / 4)] with δ ⟨hδ_pos, hδ_lt⟩
    have hsub : openCircleArc unitCircleOne δ ⊆ openCircleArc unitCircleOne (Real.pi / 4) :=
      openCircleArc_mono unitCircleOne hδ_lt.le
    have hμ0 : μ (openCircleArc unitCircleOne δ) = 0 := by
      dsimp only [μ]
      rw [Measure.restrict_apply (isOpen_openCircleArc _ _).measurableSet]
      have hinter : openCircleArc unitCircleOne δ ∩ J = ∅ := by
        ext η
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
        intro h1 h2
        exact h2 (hsub h1)
      rw [hinter, measure_empty]
    simp [hμ0]
  have htop_all : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      (∫⁻ η : UnitCircle, ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) ∂μ) = ⊤ :=
    fun z hz => (lintegral_poissonKernel_eq_top_of_measure_univ_eq_top μ hμ_univ hz).1
  refine ⟨μ, hderiv0, hμ_univ, htop_all, fun hlim => ?_⟩
  have hrad := hlim.tendsto_radial
  have hrad_top : Tendsto
      (fun r : ℝ => ∫⁻ η : UnitCircle,
        ENNReal.ofReal (_root_.poissonKernel 0 ((r : ℂ) * (unitCircleOne : ℂ)) (η : ℂ)) ∂μ)
      (𝓝[<] 1) (𝓝 (⊤ : ℝ≥0∞)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r ⟨hr0, hr1⟩
    exact (htop_all _ (radial_mem_ball_unitCircle hr0.le hr1 unitCircleOne)).symm
  have h0_eq_top : (0 : ℝ≥0∞) = ⊤ :=
    tendsto_nhds_unique_of_frequently_eq hrad hrad_top
      (Filter.Eventually.frequently (Filter.Eventually.of_forall fun _ => rfl))
  exact ENNReal.zero_ne_top h0_eq_top

/-- 11.22 (Theorem, Rudin pp. 243–244, under the implicit finite-measure hypothesis disclosed in
`node11_22_infinite_measure_counterexample`):
If `μ` is a positive finite Borel measure on `T = UnitCircle` and `(Dμ)(ζ) = 0`, then its
Poisson integral `u = P[dμ]` has nontangential limit `0` at `ζ`. -/
theorem theorem11_22 (μ : Measure UnitCircle) [IsFiniteMeasure μ] {ζ : UnitCircle}
    (hderiv : HasPositiveCircleSymmetricDerivAt μ ζ 0) :
    HasNontangentialLimit (positivePoissonIntegral μ) ζ 0 ∧
    HasNontangentialLimit (poissonMeasureIntegral (μ.withDensityᵥ fun _ : UnitCircle => (1 : ℂ))) ζ 0 ∧
    HasNontangentialLimit
      (fun z : ℂ => ∫⁻ η : UnitCircle, ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) ∂μ) ζ 0 := by
  have hreal : HasNontangentialLimit (positivePoissonIntegral μ) ζ 0 := by
    rw [hasNontangentialLimit_iff_nhdsWithin]
    intro α ⟨hα0, hα1⟩
    rw [Metric.tendsto_nhds]
    intro ε hε
    let c_α : ℝ := nontangentialConstant α
    have hc_pos : 0 < c_α := nontangentialConstant_pos hα1
    let ε' : ℝ := c_α * (ε / 3)
    have hε'_pos : 0 < ε' := by positivity
    -- Extract `δ₀ ∈ (0, π / 2)` such that `μ(I_δ) / σ(I_δ) ≤ ε'` for all `0 < δ ≤ δ₀`
    have hev_deriv := (ENNReal.tendsto_nhds_zero.mp hderiv) (ENNReal.ofReal ε')
      (ENNReal.ofReal_pos.mpr hε'_pos)
    obtain ⟨t₀, ht₀_pos, ht₀_sub⟩ := Metric.mem_nhdsWithin_iff.mp
      (Filter.inter_mem hev_deriv (Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < Real.pi / 2)))
    let δ₀ : ℝ := min (t₀ / 2) (Real.pi / 4)
    have hδ₀_pos : 0 < δ₀ := lt_min (half_pos ht₀_pos) (by positivity)
    have hδ₀_le_pi : δ₀ ≤ Real.pi := (min_le_right _ _).trans (by linarith [Real.pi_pos])
    have hδ₀_lt_pi2 : δ₀ < Real.pi / 2 := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
    have hsmall : ∀ {δ : ℝ}, 0 < δ → δ ≤ δ₀ →
        μ (openCircleArc ζ δ) ≤ ENNReal.ofReal ε' * unitCircleMeasure (openCircleArc ζ δ) := by
      intro δ hδ_pos hδ_le
      have hδ_t₀ : δ < t₀ := hδ_le.trans_lt ((min_le_left _ _).trans_lt (half_lt_self ht₀_pos))
      have hmem : δ ∈ Metric.ball (0 : ℝ) t₀ ∩ Set.Ioi 0 := by
        refine ⟨?_, hδ_pos⟩
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδ_pos]
        exact hδ_t₀
      have hdiv_le : μ (openCircleArc ζ δ) / unitCircleMeasure (openCircleArc ζ δ) ≤
          ENNReal.ofReal ε' := (ht₀_sub hmem).1
      exact (ENNReal.div_le_iff_le_mul
        (Or.inl (unitCircleMeasure_openCircleArc_ne_zero ζ hδ_pos))
        (Or.inl (measure_ne_top _ _))).mp hdiv_le
    -- Decompose `μ = μ₀ + μ₁` along `I₀ = openCircleArc ζ δ₀`
    let I₀ : Set UnitCircle := openCircleArc ζ δ₀
    have hI₀_meas : MeasurableSet I₀ := (isOpen_openCircleArc ζ δ₀).measurableSet
    let μ₀ : Measure UnitCircle := μ.restrict I₀
    let μ₁ : Measure UnitCircle := μ.restrict I₀ᶜ
    have hM_μ₀ : circleMeasureMaximal μ₀ ζ ≤ ENNReal.ofReal ε' := by
      unfold circleMeasureMaximal
      refine iSup₂_le fun δ hδ => ?_
      have hδ_pos : 0 < δ := hδ
      refine (ENNReal.div_le_iff_le_mul
        (Or.inl (unitCircleMeasure_openCircleArc_ne_zero ζ hδ_pos))
        (Or.inl (measure_ne_top _ _))).mpr ?_
      rcases le_or_gt δ δ₀ with hle | hgt
      · calc μ₀ (openCircleArc ζ δ)
            ≤ μ (openCircleArc ζ δ) := Measure.restrict_le_self _
          _ ≤ ENNReal.ofReal ε' * unitCircleMeasure (openCircleArc ζ δ) := hsmall hδ_pos hle
      · have hsub_I₀ : I₀ ⊆ openCircleArc ζ δ := openCircleArc_mono ζ hgt.le
        have hμ₀_eq : μ₀ (openCircleArc ζ δ) = μ I₀ := by
          dsimp only [μ₀]
          rw [Measure.restrict_apply (isOpen_openCircleArc ζ δ).measurableSet,
            Set.inter_eq_self_of_subset_right hsub_I₀]
        rw [hμ₀_eq]
        calc μ I₀ ≤ ENNReal.ofReal ε' * unitCircleMeasure I₀ := hsmall hδ₀_pos le_rfl
          _ ≤ ENNReal.ofReal ε' * unitCircleMeasure (openCircleArc ζ δ) :=
              mul_le_mul_of_nonneg_left (measure_mono hsub_I₀) zero_le
    -- Bound `positivePoissonIntegral μ₀ z ≤ ε / 3` on all of `approachRegion α ζ` via 11.20
    have hu₀_bound : ∀ {z : ℂ}, z ∈ approachRegion α ζ →
        positivePoissonIntegral μ₀ z ≤ ε / 3 := by
      intro z hz
      have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := approachRegion_subset_ball α ζ hz
      have h20 := theorem11_20_explicit hα0 hα1 μ₀ ζ
      let u₀_c := poissonMeasureIntegral (μ₀.withDensityᵥ fun _ : UnitCircle => (1 : ℂ))
      have hN_ge : ENNReal.ofReal (positivePoissonIntegral μ₀ z) ≤
          nontangentialMaximal α u₀_c ζ := by
        have hnn : 0 ≤ positivePoissonIntegral μ₀ z :=
          integral_nonneg (poissonKernel_unitCircle_nonneg hz_ball)
        have heq : ENNReal.ofReal (positivePoissonIntegral μ₀ z) = ‖u₀_c z‖ₑ := by
          dsimp only [u₀_c]
          rw [poissonMeasureIntegral_withDensityᵥ_one μ₀ hz_ball, ← ofReal_norm,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
        rw [heq]
        exact le_iSup₂_of_le z hz le_rfl
      have hprod : ENNReal.ofReal (c_α * positivePoissonIntegral μ₀ z) ≤
          ENNReal.ofReal (c_α * (ε / 3)) := by
        rw [ENNReal.ofReal_mul hc_pos.le]
        exact (mul_le_mul_of_nonneg_left hN_ge zero_le).trans (h20.1.trans (h20.2.trans hM_μ₀))
      have hreal_le := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ c_α * (ε / 3))).mp hprod
      exact le_of_mul_le_mul_left hreal_le hc_pos
    -- Uniform kernel decay on `I₀ᶜ` near `ζ`
    have hcos_lt1 : Real.cos δ₀ < 1 := by
      rw [← Real.cos_zero]
      exact Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩ ⟨hδ₀_pos.le, hδ₀_le_pi⟩ hδ₀_pos
    let ρ : ℝ := Real.sqrt (2 * (1 - Real.cos δ₀))
    have hρ_pos : 0 < ρ := Real.sqrt_pos.mpr (by linarith)
    have hρ_sq : ρ ^ 2 = 2 * (1 - Real.cos δ₀) := Real.sq_sqrt (by linarith)
    let M₁ : ℝ := μ₁.real Set.univ + 1
    have hM₁_pos : 0 < M₁ := by positivity
    let r_z : ℝ := min (ρ / 2) ((ε / 3) * (ρ / 2) ^ 2 / (2 * M₁))
    have hr_z_pos : 0 < r_z := lt_min (half_pos hρ_pos) (by positivity)
    refine Metric.mem_nhdsWithin_iff.mpr ⟨r_z, hr_z_pos, ?_⟩
    rintro z ⟨hz_ball_ζ, hz_app⟩
    have hz_U : z ∈ Metric.ball (0 : ℂ) 1 := approachRegion_subset_ball α ζ hz_app
    have hz_lt1 : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz_U
    have hz_dist : ‖z - (ζ : ℂ)‖ < r_z := by simpa [Metric.mem_ball, dist_eq_norm] using hz_ball_ζ
    have hz_dist_ρ : ‖z - (ζ : ℂ)‖ < ρ / 2 := hz_dist.trans_le (min_le_left _ _)
    -- Bound `positivePoissonIntegral μ₁ z ≤ ε / 3`
    have hu₁_bound : positivePoissonIntegral μ₁ z ≤ ε / 3 := by
      have hK_le : ∀ η ∈ I₀ᶜ, _root_.poissonKernel 0 z (η : ℂ) ≤
          2 * ‖z - (ζ : ℂ)‖ / (ρ / 2) ^ 2 := by
        intro η hη_compl
        have hnot_I₀ : η ∉ I₀ := hη_compl
        rw [show I₀ = openCircleArc ζ δ₀ from rfl, mem_openCircleArc_iff_chordal hδ₀_pos hδ₀_le_pi,
          ← hρ_sq, not_lt] at hnot_I₀
        have hη_ge_ρ : ρ ≤ ‖(η : ℂ) - (ζ : ℂ)‖ := by
          nlinarith [norm_nonneg ((η : ℂ) - (ζ : ℂ)), hρ_pos]
        have hηz_ge : ρ / 2 ≤ ‖(η : ℂ) - z‖ := by
          have htri : ‖(η : ℂ) - (ζ : ℂ)‖ ≤ ‖(η : ℂ) - z‖ + ‖z - (ζ : ℂ)‖ := by
            calc ‖(η : ℂ) - (ζ : ℂ)‖ = ‖((η : ℂ) - z) + (z - (ζ : ℂ))‖ := by ring_nf
              _ ≤ ‖(η : ℂ) - z‖ + ‖z - (ζ : ℂ)‖ := norm_add_le _ _
          linarith
        have h1mz2_le : 1 - ‖z‖ ^ 2 ≤ 2 * ‖z - (ζ : ℂ)‖ := by
          have h1mz : 1 - ‖z‖ ≤ ‖z - (ζ : ℂ)‖ := by
            have htri := norm_sub_norm_le (ζ : ℂ) z
            rw [norm_unitCircle, norm_sub_rev] at htri
            exact htri
          calc 1 - ‖z‖ ^ 2 = (1 + ‖z‖) * (1 - ‖z‖) := by ring
            _ ≤ 2 * ‖z - (ζ : ℂ)‖ := by nlinarith [norm_nonneg z]
        exact (poissonKernel_unitCircle_le_of_dist_ge hz_U (half_pos hρ_pos) hηz_ge).trans
          (div_le_div_of_nonneg_right h1mz2_le (sq_nonneg _))
      have hint_K : Integrable (fun η : UnitCircle => _root_.poissonKernel 0 z (η : ℂ)) μ₁ :=
        (continuous_poissonKernel_unitCircle hz_U).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hae_I₀c : ∀ᵐ η ∂μ₁, η ∈ I₀ᶜ := ae_restrict_mem hI₀_meas.compl
      calc positivePoissonIntegral μ₁ z
          ≤ ∫ _η : UnitCircle, (2 * ‖z - (ζ : ℂ)‖ / (ρ / 2) ^ 2) ∂μ₁ :=
            integral_mono_ae hint_K (integrable_const _) (hae_I₀c.mono fun η hη => hK_le η hη)
        _ = (2 * ‖z - (ζ : ℂ)‖ / (ρ / 2) ^ 2) * μ₁.real Set.univ := by
            rw [integral_const, smul_eq_mul, mul_comm]
        _ ≤ (2 * r_z / (ρ / 2) ^ 2) * M₁ := by
            have h1 : 2 * ‖z - (ζ : ℂ)‖ / (ρ / 2) ^ 2 ≤ 2 * r_z / (ρ / 2) ^ 2 :=
              div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
            have h2 : μ₁.real Set.univ ≤ M₁ := by dsimp only [M₁]; linarith
            exact mul_le_mul h1 h2 measureReal_nonneg (by positivity)
        _ ≤ (2 * ((ε / 3) * (ρ / 2) ^ 2 / (2 * M₁)) / (ρ / 2) ^ 2) * M₁ := by
            have hr_le : r_z ≤ (ε / 3) * (ρ / 2) ^ 2 / (2 * M₁) := min_le_right _ _
            gcongr
        _ = ε / 3 := by
            have hρ2_ne : (ρ / 2) ^ 2 ≠ 0 := (sq_pos_of_pos (half_pos hρ_pos)).ne'
            field_simp [hρ2_ne, hM₁_pos.ne']
    -- Combine `μ = μ₀ + μ₁`
    have hμ_split : μ = μ₀ + μ₁ := (Measure.restrict_add_restrict_compl hI₀_meas).symm
    have hu_sum : positivePoissonIntegral μ z =
        positivePoissonIntegral μ₀ z + positivePoissonIntegral μ₁ z := by
      unfold positivePoissonIntegral
      have hint0 : Integrable (fun η : UnitCircle => _root_.poissonKernel 0 z (η : ℂ)) μ₀ :=
        (continuous_poissonKernel_unitCircle hz_U).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hint1 : Integrable (fun η : UnitCircle => _root_.poissonKernel 0 z (η : ℂ)) μ₁ :=
        (continuous_poissonKernel_unitCircle hz_U).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      conv_lhs => rw [hμ_split]
      exact integral_add_measure hint0 hint1
    have hu_nn : 0 ≤ positivePoissonIntegral μ z :=
      integral_nonneg (poissonKernel_unitCircle_nonneg hz_U)
    simp only [Set.mem_ofPred_eq]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hu_nn, hu_sum]
    linarith [hu₀_bound hz_app]
  -- Deduce complex-valued and `[0, ∞]`-valued nontangential limits from `hreal`
  have hcomplex : HasNontangentialLimit
      (poissonMeasureIntegral (μ.withDensityᵥ fun _ : UnitCircle => (1 : ℂ))) ζ 0 := by
    have hcast : HasNontangentialLimit (fun z => (positivePoissonIntegral μ z : ℂ)) ζ 0 := by
      intro α hα1 z hz hlim
      simpa [Function.comp_def] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp (hreal α hα1 z hz hlim)
    exact hcast.congr_ball fun z hz => (poissonMeasureIntegral_withDensityᵥ_one μ hz).symm
  have hennreal : HasNontangentialLimit
      (fun z : ℂ => ∫⁻ η : UnitCircle, ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) ∂μ) ζ 0 := by
    have hofR : HasNontangentialLimit (fun z => ENNReal.ofReal (positivePoissonIntegral μ z)) ζ 0 := by
      intro α hα1 z hz hlim
      simpa [Function.comp_def] using ENNReal.tendsto_ofReal (hreal α hα1 z hz hlim)
    refine hofR.congr_ball fun z hz => ?_
    unfold positivePoissonIntegral
    have hint : Integrable (fun η : UnitCircle => _root_.poissonKernel 0 z (η : ℂ)) μ :=
      (continuous_poissonKernel_unitCircle hz).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    exact ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ (poissonKernel_unitCircle_nonneg hz))
  exact ⟨hreal, hcomplex, hennreal⟩

end Node11_22

section Node11_23

/-- Constant reproduction on `U`: `P[c](z) = c` for all `z ∈ Metric.ball 0 1`. -/
theorem unitPoissonIntegral_const (c : ℂ) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    unitPoissonIntegral (fun _ : UnitCircle => c) z = c := by
  unfold unitPoissonIntegral
  rw [integral_smul_const, integral_poissonKernel_unitCircle hz, one_smul]

/-- 11.23 (Fatou's Lebesgue-Point Theorem, Rudin p. 244):
If `f ∈ L¹(T)` (`Integrable f unitCircleMeasure`), then `P[f]` has nontangential limit `f(ζ)`
at every Lebesgue point `ζ ∈ T` of `f`. -/
theorem theorem11_23 {f : UnitCircle → ℂ} (hf : Integrable f unitCircleMeasure)
    {ζ : UnitCircle} (hleb : IsCircleLebesguePoint f ζ) :
    HasNontangentialLimit (unitPoissonIntegral f) ζ (f ζ) := by
  let g : UnitCircle → ℝ := fun η => ‖f η - f ζ‖
  have hg_int : Integrable g unitCircleMeasure :=
    (hf.sub (integrable_const (f ζ))).norm
  obtain ⟨g₀, hg₀_smeas, hg₀_ae⟩ := hg_int.aestronglyMeasurable
  let w : UnitCircle → ℝ≥0∞ := fun η => ENNReal.ofReal (max (g₀ η) 0)
  have hw_meas : Measurable w :=
    (hg₀_smeas.measurable.max measurable_const).ennreal_ofReal
  have hw_ae : w =ᵐ[unitCircleMeasure] fun η => ENNReal.ofReal (g η) := by
    filter_upwards [hg₀_ae] with η hη
    dsimp only [w]
    rw [← hη, max_eq_left (norm_nonneg _)]
  let μ : Measure UnitCircle := unitCircleMeasure.withDensity w
  have hμ_eq : μ = unitCircleMeasure.withDensity (fun η => ENNReal.ofReal (g η)) :=
    withDensity_congr_ae hw_ae
  have hμ_univ : μ Set.univ < ⊤ := by
    dsimp only [μ]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_congr_ae hw_ae]
    have heq : (∫⁻ η, ENNReal.ofReal (g η) ∂unitCircleMeasure) =
        ∫⁻ η, ‖f η - f ζ‖ₑ ∂unitCircleMeasure :=
      lintegral_congr fun η => ofReal_norm (f η - f ζ)
    rw [heq]
    exact (hf.sub (integrable_const (f ζ))).hasFiniteIntegral
  have : IsFiniteMeasure μ := ⟨hμ_univ⟩
  -- Show `(Dμ)(ζ) = 0` from `IsCircleLebesguePoint f ζ`
  have hderiv : HasPositiveCircleSymmetricDerivAt μ ζ 0 := by
    unfold HasPositiveCircleSymmetricDerivAt
    have hofR := ENNReal.tendsto_ofReal hleb
    rw [ENNReal.ofReal_zero] at hofR
    refine hofR.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ_pos : 0 < δ := hδ
    let I := openCircleArc ζ δ
    have hI_meas : MeasurableSet I := (isOpen_openCircleArc ζ δ).measurableSet
    have hσ_pos : 0 < unitCircleMeasure.real I := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos (unitCircleMeasure_openCircleArc_ne_zero ζ hδ_pos) (measure_ne_top _ _)
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr hσ_pos.le), ENNReal.ofReal_inv_of_pos hσ_pos,
      ofReal_integral_eq_lintegral_ofReal hg_int.integrableOn (ae_of_all _ fun _ => norm_nonneg _)]
    have hμI : μ I = ∫⁻ η in I, ENNReal.ofReal (g η) ∂unitCircleMeasure := by
      rw [hμ_eq, withDensity_apply _ hI_meas]
    have hσI : ENNReal.ofReal (unitCircleMeasure.real I) = unitCircleMeasure I := by
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [← hμI, hσI, mul_comm, ← div_eq_mul_inv]
  have h22 := (theorem11_22 μ hderiv).1
  -- Pointwise domination `‖P[f](z) - f(ζ)‖ ≤ positivePoissonIntegral μ z` on `U`
  have hdom : ∀ {z : ℂ}, z ∈ Metric.ball (0 : ℂ) 1 →
      ‖unitPoissonIntegral f z - f ζ‖ ≤ positivePoissonIntegral μ z := by
    intro z hz
    have hdiff_eq : unitPoissonIntegral f z - f ζ =
        ∫ η : UnitCircle, _root_.poissonKernel 0 z (η : ℂ) • (f η - f ζ) ∂unitCircleMeasure := by
      conv_lhs => rw [← unitPoissonIntegral_const (f ζ) hz]
      unfold unitPoissonIntegral
      have hint1 : Integrable (fun η : UnitCircle => _root_.poissonKernel 0 z (η : ℂ) • f η)
          unitCircleMeasure :=
        integrable_real_smul_of_continuous (continuous_poissonKernel_unitCircle hz) hf
      have hint2 : Integrable (fun η : UnitCircle => _root_.poissonKernel 0 z (η : ℂ) • f ζ)
          unitCircleMeasure :=
        ((continuous_poissonKernel_unitCircle hz).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)).smul_const (f ζ)
      rw [← integral_sub hint1 hint2]
      exact integral_congr_ae (ae_of_all _ fun η => (smul_sub _ _ _).symm)
    have hpos_eq : positivePoissonIntegral μ z =
        ∫ η : UnitCircle, _root_.poissonKernel 0 z (η : ℂ) * g η ∂unitCircleMeasure := by
      unfold positivePoissonIntegral
      dsimp only [μ]
      rw [integral_withDensity_eq_integral_toReal_smul hw_meas
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae ?_
      filter_upwards [hg₀_ae] with η hη
      dsimp only [w]
      rw [← hη, max_eq_left (norm_nonneg _), ENNReal.toReal_ofReal (norm_nonneg _),
        smul_eq_mul, mul_comm]
    rw [hdiff_eq, hpos_eq]
    calc ‖∫ η : UnitCircle, _root_.poissonKernel 0 z (η : ℂ) • (f η - f ζ) ∂unitCircleMeasure‖
        ≤ ∫ η : UnitCircle, ‖_root_.poissonKernel 0 z (η : ℂ) • (f η - f ζ)‖ ∂unitCircleMeasure :=
          norm_integral_le_integral_norm _
      _ = ∫ η : UnitCircle, _root_.poissonKernel 0 z (η : ℂ) * g η ∂unitCircleMeasure := by
          refine integral_congr_ae (ae_of_all _ fun η => ?_)
          dsimp only
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (poissonKernel_unitCircle_nonneg hz η)]
  intro α hα1 z hz hlim
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp (h22 α hα1 z hz hlim) ε hε] with j hj
  have hz_U : z j ∈ Metric.ball (0 : ℂ) 1 := approachRegion_subset_ball α ζ (hz j)
  have hnn : 0 ≤ positivePoissonIntegral μ (z j) :=
    integral_nonneg (poissonKernel_unitCircle_nonneg hz_U)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hj
  rw [dist_eq_norm]
  exact (hdom hz_U).trans_lt hj

/-- Almost-everywhere corollary of 11.23 + 11.19: for `f ∈ L¹(T)`, `P[f]` has nontangential limit
`f(ζ)` at `σ`-almost every `ζ ∈ T`. -/
theorem ae_hasNontangentialLimit_unitPoissonIntegral {f : UnitCircle → ℂ}
    (hf : Integrable f unitCircleMeasure) :
    ∀ᵐ ζ ∂unitCircleMeasure, HasNontangentialLimit (unitPoissonIntegral f) ζ (f ζ) := by
  filter_upwards [ae_isCircleLebesguePoint hf] with ζ hleb using theorem11_23 hf hleb

end Node11_23

section Node11_24

/-- Measure additivity of `complexMeasureIntegral` for bounded measurable functions on `X`. -/
theorem complexMeasureIntegral_measure_add {X : Type*} [MeasurableSpace X]
    (μ₁ μ₂ : ComplexMeasure X) {f : X → ℂ}
    (hf_meas : Measurable f) {C : ℝ} (hf_bdd : ∀ x : X, ‖f x‖ ≤ C) :
    RudinRCA.Chapter10.complexMeasureIntegral (μ₁ + μ₂) f =
      RudinRCA.Chapter10.complexMeasureIntegral μ₁ f +
        RudinRCA.Chapter10.complexMeasureIntegral μ₂ f := by
  have : IsFiniteMeasure μ₁.variation := isFiniteMeasure_complexMeasure_variation μ₁
  have : IsFiniteMeasure μ₂.variation := isFiniteMeasure_complexMeasure_variation μ₂
  have : IsFiniteMeasure (μ₁ + μ₂).variation := isFiniteMeasure_complexMeasure_variation (μ₁ + μ₂)
  let ν : Measure X := μ₁.variation + μ₂.variation + (μ₁ + μ₂).variation
  have hle1 : μ₁.variation ≤ ν := by
    intro s
    dsimp only [ν]
    simp only [Measure.coe_add, Pi.add_apply]
    exact le_self_add.trans le_self_add
  have hle2 : μ₂.variation ≤ ν := by
    intro s
    dsimp only [ν]
    simp only [Measure.coe_add, Pi.add_apply]
    exact le_add_self.trans le_self_add
  have hle12 : (μ₁ + μ₂).variation ≤ ν := by
    intro s
    dsimp only [ν]
    simp only [Measure.coe_add, Pi.add_apply]
    exact le_add_self
  have hf_int_ν : Integrable f ν :=
    Integrable.of_bound hf_meas.aestronglyMeasurable C (ae_of_all _ hf_bdd)
  -- Continuity of `g ↦ complexMeasureIntegral c g` with respect to `L¹(ν)` whenever `c.variation ≤ ν`
  have hcont_c : ∀ (c : ComplexMeasure X) [IsFiniteMeasure c.variation],
      c.variation ≤ ν →
      Continuous (fun g : Lp ℂ 1 ν => RudinRCA.Chapter10.complexMeasureIntegral c g) := by
    intro c _ hc_le
    obtain ⟨h, hm, hn, hi, hr_pol⟩ := RudinRCA.Chapter06.theorem_6_12_of_finite_variation c
    have hpolar_lp : ∀ g : Lp ℂ 1 ν,
        RudinRCA.Chapter10.complexMeasureIntegral c g =
          ∫ x, (g : X → ℂ) x * h x ∂c.variation := fun g =>
      RudinRCA.Chapter06.vectorIntegral_eq_polar c h hm hn hi hr_pol
        (((Lp.memLp g).integrable le_rfl).mono_measure hc_le)
    rw [Metric.continuous_iff]
    intro g₁ ε hε
    refine ⟨ε, hε, fun g₂ hg₂ => ?_⟩
    rw [dist_eq_norm, hpolar_lp g₂, hpolar_lp g₁]
    have hint1 : Integrable (fun x => (g₂ : X → ℂ) x * h x) c.variation :=
      ((((Lp.memLp g₂).integrable le_rfl).mono_measure hc_le).mul_bdd hm.aestronglyMeasurable
        (ae_of_all _ fun x => (hn x).le))
    have hint2 : Integrable (fun x => (g₁ : X → ℂ) x * h x) c.variation :=
      ((((Lp.memLp g₁).integrable le_rfl).mono_measure hc_le).mul_bdd hm.aestronglyMeasurable
        (ae_of_all _ fun x => (hn x).le))
    rw [← integral_sub hint1 hint2]
    have hnorm_sub : ‖∫ x, ((g₂ : X → ℂ) x * h x - (g₁ : X → ℂ) x * h x) ∂c.variation‖ ≤
        dist g₂ g₁ := by
      calc ‖∫ x, ((g₂ : X → ℂ) x * h x - (g₁ : X → ℂ) x * h x) ∂c.variation‖
          ≤ ∫ x, ‖(g₂ : X → ℂ) x * h x - (g₁ : X → ℂ) x * h x‖ ∂c.variation :=
            norm_integral_le_integral_norm _
        _ = ∫ x, ‖(g₂ : X → ℂ) x - (g₁ : X → ℂ) x‖ ∂c.variation := by
            refine integral_congr_ae (ae_of_all _ fun x => ?_)
            dsimp only
            rw [← sub_mul, norm_mul, hn x, mul_one]
        _ ≤ ∫ x, ‖(g₂ : X → ℂ) x - (g₁ : X → ℂ) x‖ ∂ν :=
            integral_mono_measure hc_le (ae_of_all _ fun _ => norm_nonneg _)
              (((Lp.memLp g₂).integrable le_rfl).sub ((Lp.memLp g₁).integrable le_rfl)).norm
        _ = ‖g₂ - g₁‖ := by
            have hcoe := Lp.coeFn_sub g₂ g₁
            have hint_eq : (∫ x, ‖(g₂ : X → ℂ) x - (g₁ : X → ℂ) x‖ ∂ν) =
                ∫ x, ‖((g₂ - g₁ : Lp ℂ 1 ν) : X → ℂ) x‖ ∂ν :=
              integral_congr_ae (hcoe.mono fun x hx => by
                dsimp only
                rw [hx]
                rfl)
            rw [hint_eq, Lp.norm_def,
              eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable (g₂ - g₁)),
              integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable (g₂ - g₁))]
        _ = dist g₂ g₁ := (dist_eq_norm g₂ g₁).symm
    exact hnorm_sub.trans_lt hg₂
  -- Additivity of `complexMeasureIntegral c` in the integrand via `vectorIntegral_eq_polar`
  have hadd_fn : ∀ (c : ComplexMeasure X) [IsFiniteMeasure c.variation],
      c.variation ≤ ν → ∀ {g₁ g₂ : X → ℂ}, Integrable g₁ ν → Integrable g₂ ν →
      RudinRCA.Chapter10.complexMeasureIntegral c (g₁ + g₂) =
        RudinRCA.Chapter10.complexMeasureIntegral c g₁ +
          RudinRCA.Chapter10.complexMeasureIntegral c g₂ := by
    intro c _ hc_le g₁ g₂ hg₁ hg₂
    obtain ⟨h, hm, hn, hi, hr_pol⟩ := RudinRCA.Chapter06.theorem_6_12_of_finite_variation c
    have hg₁c := hg₁.mono_measure hc_le
    have hg₂c := hg₂.mono_measure hc_le
    unfold RudinRCA.Chapter10.complexMeasureIntegral
    rw [RudinRCA.Chapter06.vectorIntegral_eq_polar c h hm hn hi hr_pol (hg₁c.add hg₂c),
      RudinRCA.Chapter06.vectorIntegral_eq_polar c h hm hn hi hr_pol hg₁c,
      RudinRCA.Chapter06.vectorIntegral_eq_polar c h hm hn hi hr_pol hg₂c]
    have h1 : Integrable (fun x => g₁ x * h x) c.variation :=
      hg₁c.mul_bdd hm.aestronglyMeasurable (ae_of_all _ fun x => (hn x).le)
    have h2 : Integrable (fun x => g₂ x * h x) c.variation :=
      hg₂c.mul_bdd hm.aestronglyMeasurable (ae_of_all _ fun x => (hn x).le)
    have heq : ∀ x : X, (g₁ + g₂) x * h x = g₁ x * h x + g₂ x * h x := fun x =>
      add_mul (g₁ x) (g₂ x) (h x)
    simp_rw [heq]
    exact integral_add h1 h2
  refine Integrable.induction
    (P := fun g => RudinRCA.Chapter10.complexMeasureIntegral (μ₁ + μ₂) g =
      RudinRCA.Chapter10.complexMeasureIntegral μ₁ g +
        RudinRCA.Chapter10.complexMeasureIntegral μ₂ g)
    ?_ ?_ ?_ ?_ hf_int_ν
  · intro z E hE _
    unfold RudinRCA.Chapter10.complexMeasureIntegral
    rw [VectorMeasure.integral_indicator_const z hE,
      VectorMeasure.integral_indicator_const z hE,
      VectorMeasure.integral_indicator_const z hE]
    change z * (μ₁ + μ₂) E = z * μ₁ E + z * μ₂ E
    rw [add_apply, mul_add]
  · intro g₁ g₂ _ hg₁ hg₂ h1 h2
    rw [hadd_fn (μ₁ + μ₂) hle12 hg₁ hg₂, hadd_fn μ₁ hle1 hg₁ hg₂, hadd_fn μ₂ hle2 hg₁ hg₂,
      h1, h2]
    ring
  · exact isClosed_eq (hcont_c (μ₁ + μ₂) hle12) ((hcont_c μ₁ hle1).add (hcont_c μ₂ hle2))
  · intro g₁ g₂ hfg _ h1
    unfold RudinRCA.Chapter10.complexMeasureIntegral at h1 ⊢
    have hae_le : ∀ {m : Measure X}, m ≤ ν → g₁ =ᵐ[m] g₂ := fun hm => by
      rw [EventuallyEq, ae_iff] at hfg ⊢
      exact nonpos_iff_eq_zero.mp ((hm _).trans (le_of_eq hfg))
    rw [← VectorMeasure.integral_congr_ae (hae_le hle12), h1,
      VectorMeasure.integral_congr_ae (hae_le hle1),
      VectorMeasure.integral_congr_ae (hae_le hle2)]

/-- Additivity of `poissonMeasureIntegral` in the measure on `U = Metric.ball 0 1`. -/
theorem poissonMeasureIntegral_add (μ₁ μ₂ : ComplexMeasure UnitCircle)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    poissonMeasureIntegral (μ₁ + μ₂) z =
      poissonMeasureIntegral μ₁ z + poissonMeasureIntegral μ₂ z := by
  unfold poissonMeasureIntegral
  have hcont : Continuous (fun η : UnitCircle => (_root_.poissonKernel 0 z (η : ℂ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_poissonKernel_unitCircle hz)
  obtain ⟨C, hC⟩ := isCompact_range hcont.norm |>.bddAbove
  exact complexMeasureIntegral_measure_add μ₁ μ₂ hcont.measurable
    (fun η => hC ⟨η, rfl⟩)

/-- Scalar multiplication `(c • μ)` for `complexMeasureIntegral` on bounded measurable functions. -/
theorem complexMeasureIntegral_measure_neg {X : Type*} [MeasurableSpace X]
    (μ : ComplexMeasure X) {f : X → ℂ}
    (hf_meas : Measurable f) {C : ℝ} (hf_bdd : ∀ x : X, ‖f x‖ ≤ C) :
    RudinRCA.Chapter10.complexMeasureIntegral (-μ) f =
      -RudinRCA.Chapter10.complexMeasureIntegral μ f := by
  have h0 : RudinRCA.Chapter10.complexMeasureIntegral (0 : ComplexMeasure X) f = 0 := by
    unfold RudinRCA.Chapter10.complexMeasureIntegral
    simp
  have hsum := complexMeasureIntegral_measure_add μ (-μ) hf_meas hf_bdd
  rw [add_neg_cancel, h0] at hsum
  exact eq_neg_of_add_eq_zero_right hsum.symm

theorem poissonMeasureIntegral_sub (μ₁ μ₂ : ComplexMeasure UnitCircle)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    poissonMeasureIntegral (μ₁ - μ₂) z =
      poissonMeasureIntegral μ₁ z - poissonMeasureIntegral μ₂ z := by
  rw [sub_eq_add_neg, poissonMeasureIntegral_add μ₁ (-μ₂) hz]
  unfold poissonMeasureIntegral
  have hcont : Continuous (fun η : UnitCircle => (_root_.poissonKernel 0 z (η : ℂ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_poissonKernel_unitCircle hz)
  obtain ⟨C, hC⟩ := isCompact_range hcont.norm |>.bddAbove
  rw [complexMeasureIntegral_measure_neg μ₂ hcont.measurable (fun η => hC ⟨η, rfl⟩),
    sub_eq_add_neg]

/-- Pointwise modulus domination `‖P[dμ](z)‖ ≤ P[d|μ|](z)` for any complex Borel measure `μ` on `T`
and `z ∈ Metric.ball 0 1`. -/
theorem norm_poissonMeasureIntegral_le_positivePoissonIntegral_variation
    (μ : ComplexMeasure UnitCircle) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    ‖poissonMeasureIntegral μ z‖ ≤ positivePoissonIntegral μ.variation z := by
  unfold poissonMeasureIntegral RudinRCA.Chapter10.complexMeasureIntegral positivePoissonIntegral
  have : IsFiniteMeasure μ.variation := isFiniteMeasure_complexMeasure_variation μ
  obtain ⟨h, hm, hn, hi, hr_pol⟩ := RudinRCA.Chapter06.theorem_6_12 μ
  have hK_cont : Continuous (fun η : UnitCircle => (_root_.poissonKernel 0 z (η : ℂ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_poissonKernel_unitCircle hz)
  rw [RudinRCA.Chapter06.vectorIntegral_eq_polar μ h hm hn hi hr_pol
    (hK_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  calc ‖∫ η : UnitCircle, (_root_.poissonKernel 0 z (η : ℂ) : ℂ) * h η ∂μ.variation‖
      ≤ ∫ η : UnitCircle, ‖(_root_.poissonKernel 0 z (η : ℂ) : ℂ) * h η‖ ∂μ.variation :=
        norm_integral_le_integral_norm _
    _ = ∫ η : UnitCircle, _root_.poissonKernel 0 z (η : ℂ) ∂μ.variation := by
        refine integral_congr_ae (ae_of_all _ fun η => ?_)
        dsimp only
        rw [norm_mul, hn η, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (poissonKernel_unitCircle_nonneg hz η)]

/-- Singular complex measures have nontangential Poisson limit `0` `σ`-almost everywhere on `T`. -/
theorem ae_hasNontangentialLimit_zero_of_mutuallySingular
    (μ_s : ComplexMeasure UnitCircle)
    (hsing : μ_s ⟂ᵥ unitCircleMeasure.toENNRealVectorMeasure) :
    ∀ᵐ ζ ∂unitCircleMeasure, HasNontangentialLimit (poissonMeasureIntegral μ_s) ζ 0 := by
  have : IsFiniteMeasure μ_s.variation := isFiniteMeasure_complexMeasure_variation μ_s
  have hsing_var := (mutuallySingular_complexMeasure_iff_variation μ_s).mp hsing
  filter_upwards [ae_hasPositiveCircleSymmetricDerivAt_zero_of_mutuallySingular μ_s.variation hsing_var]
    with ζ hderiv
  have h22 := (theorem11_22 μ_s.variation hderiv).1
  intro α hα1 z hz hlim
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp (h22 α hα1 z hz hlim) ε hε] with j hj
  have hz_U : z j ∈ Metric.ball (0 : ℂ) 1 := approachRegion_subset_ball α ζ (hz j)
  have hnn : 0 ≤ positivePoissonIntegral μ_s.variation (z j) :=
    integral_nonneg (poissonKernel_unitCircle_nonneg hz_U)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hj
  rw [dist_zero_right]
  exact (norm_poissonMeasureIntegral_le_positivePoissonIntegral_variation μ_s hz_U).trans_lt hj

/-- 11.24 (Fatou's Theorem for Complex Measures, Rudin p. 244):
If `dμ = f dσ + dμ_s` is the Lebesgue decomposition of a complex Borel measure `μ` on `T`,
where `f ∈ L¹(T)` and `μ_s ⟂ σ`, then `P[dμ]` has nontangential limit `f(ζ)` at `σ`-almost
every `ζ ∈ T`. -/
theorem theorem11_24 (μ μ_s : ComplexMeasure UnitCircle) (f : UnitCircle → ℂ)
    (hf : Integrable f unitCircleMeasure)
    (hsing : μ_s ⟂ᵥ unitCircleMeasure.toENNRealVectorMeasure)
    (hdecomp : μ = unitCircleMeasure.withDensityᵥ f + μ_s) :
    ∀ᵐ ζ ∂unitCircleMeasure, HasNontangentialLimit (poissonMeasureIntegral μ) ζ (f ζ) := by
  filter_upwards [ae_hasNontangentialLimit_unitPoissonIntegral hf,
    ae_hasNontangentialLimit_zero_of_mutuallySingular μ_s hsing] with ζ hlim_f hlim_s
  have hsum : HasNontangentialLimit
      (fun z => unitPoissonIntegral f z + poissonMeasureIntegral μ_s z) ζ (f ζ) := by
    intro α hα1 z hz hlim
    simpa only [add_zero] using (hlim_f α hα1 z hz hlim).add (hlim_s α hα1 z hz hlim)
  refine hsum.congr_ball fun z hz => ?_
  rw [hdecomp, poissonMeasureIntegral_add _ _ hz, poissonMeasureIntegral_withDensityᵥ hf hz]

/-- Unconditional form of 11.24: for any complex Borel measure `μ` on `T`, `P[dμ]` has
nontangential limit `(dμ / dσ)(ζ)` (`μ.rnDeriv unitCircleMeasure ζ`) at `σ`-almost every `ζ ∈ T`. -/
theorem theorem11_24_rnDeriv (μ : ComplexMeasure UnitCircle) :
    ∀ᵐ ζ ∂unitCircleMeasure,
      HasNontangentialLimit (poissonMeasureIntegral μ) ζ (μ.rnDeriv unitCircleMeasure ζ) := by
  have : μ.HaveLebesgueDecomposition unitCircleMeasure := ⟨inferInstance, inferInstance⟩
  have hsing : μ.singularPart unitCircleMeasure ⟂ᵥ unitCircleMeasure.toENNRealVectorMeasure := by
    obtain ⟨A, hA, hr, hμA⟩ := μ.re.mutuallySingular_singularPart unitCircleMeasure
    obtain ⟨B, hB, hi, hμB⟩ := μ.im.mutuallySingular_singularPart unitCircleMeasure
    refine VectorMeasure.MutuallySingular.mk (A ∩ B) (hA.inter hB) ?_ ?_
    · intro E hE _
      change Complex.mk (μ.re.singularPart unitCircleMeasure E)
        (μ.im.singularPart unitCircleMeasure E) = 0
      rw [hr E (hE.trans Set.inter_subset_left), hi E (hE.trans Set.inter_subset_right)]
      rfl
    · intro E hE hEm
      rw [Measure.toENNRealVectorMeasure_apply_measurable hEm]
      have hAz : unitCircleMeasure Aᶜ = 0 := by
        simpa only [Measure.toENNRealVectorMeasure_apply_measurable hA.compl] using
          hμA Aᶜ Set.Subset.rfl
      have hBz : unitCircleMeasure Bᶜ = 0 := by
        simpa only [Measure.toENNRealVectorMeasure_apply_measurable hB.compl] using
          hμB Bᶜ Set.Subset.rfl
      apply measure_mono_null hE
      rw [Set.compl_inter]
      exact measure_union_null hAz hBz
  have hdecomp : μ =
      unitCircleMeasure.withDensityᵥ (μ.rnDeriv unitCircleMeasure) +
        μ.singularPart unitCircleMeasure := by
    rw [add_comm]
    exact (ComplexMeasure.singularPart_add_withDensity_rnDeriv_eq
      (c := μ) (μ := unitCircleMeasure)).symm
  exact theorem11_24 μ (μ.singularPart unitCircleMeasure) (μ.rnDeriv unitCircleMeasure)
    (μ.integrable_rnDeriv unitCircleMeasure) hsing hdecomp

end Node11_24

section Node11_25

/-- Explicit constant `A(α, p)` for Theorem 11.25 (`0 < α < 1`, `1 ≤ p ≤ ⊤`). -/
def nontangentialLpConstant (α : ℝ) (p : ℝ≥0∞) : ℝ :=
  if p = 1 then
    3 / nontangentialConstant α
  else if p = ⊤ then
    1
  else
    ((p.toReal * 6 * (2 ^ (p.toReal - 1) / (p.toReal - 1))) ^ (p.toReal)⁻¹) /
      nontangentialConstant α

theorem nontangentialLpConstant_pos {α : ℝ} (hα1 : α < 1) {p : ℝ≥0∞} (hp1 : 1 ≤ p) :
    0 < nontangentialLpConstant α p := by
  have hc_pos : 0 < nontangentialConstant α := nontangentialConstant_pos hα1
  unfold nontangentialLpConstant
  split_ifs with hp_eq1 hp_top
  · positivity
  · norm_num
  · have hp_gt1 : 1 < p := lt_of_le_of_ne hp1 (Ne.symm hp_eq1)
    have hp'_gt1 : 1 < p.toReal := by
      have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).mpr hp_gt1
      simpa using this
    have hp'_pos : 0 < p.toReal := zero_lt_one.trans hp'_gt1
    have hp'm1_pos : 0 < p.toReal - 1 := sub_pos.mpr hp'_gt1
    have hbase_pos : 0 < p.toReal * 6 * (2 ^ (p.toReal - 1) / (p.toReal - 1)) := by
      positivity
    exact div_pos (Real.rpow_pos_of_pos hbase_pos _) hc_pos

/-- Pointwise domination `c_α (N_α P[dμ])(ζ) ≤ (M μ)(ζ)` for any complex Borel measure `μ` on `T`
and `0 < α < 1`. -/
theorem nontangentialMaximal_poissonMeasureIntegral_le
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (μ : ComplexMeasure UnitCircle) (ζ : UnitCircle) :
    ENNReal.ofReal (nontangentialConstant α) *
      nontangentialMaximal α (poissonMeasureIntegral μ) ζ ≤
    complexCircleMeasureMaximal μ ζ := by
  have : IsFiniteMeasure μ.variation := isFiniteMeasure_complexMeasure_variation μ
  let u_var : ℂ → ℂ := poissonMeasureIntegral (μ.variation.withDensityᵥ fun _ : UnitCircle => (1 : ℂ))
  have hle_u : nontangentialMaximal α (poissonMeasureIntegral μ) ζ ≤
      nontangentialMaximal α u_var ζ := by
    unfold nontangentialMaximal
    refine iSup₂_le fun z hz => ?_
    have hz_U : z ∈ Metric.ball (0 : ℂ) 1 := approachRegion_subset_ball α ζ hz
    have hdom := norm_poissonMeasureIntegral_le_positivePoissonIntegral_variation μ hz_U
    have hnn : 0 ≤ positivePoissonIntegral μ.variation z :=
      integral_nonneg (poissonKernel_unitCircle_nonneg hz_U)
    have hnorm_var : ‖u_var z‖ = positivePoissonIntegral μ.variation z := by
      dsimp only [u_var]
      rw [poissonMeasureIntegral_withDensityᵥ_one μ.variation hz_U,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    have henorm : ‖poissonMeasureIntegral μ z‖ₑ ≤ ‖u_var z‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, hnorm_var]
      exact ENNReal.ofReal_le_ofReal hdom
    exact le_iSup₂_of_le z hz henorm
  have h20 := theorem11_20_explicit hα0 hα1 μ.variation ζ
  exact (mul_le_mul_of_nonneg_left hle_u zero_le).trans (h20.1.trans h20.2)

/-- 11.25(a) (Weak `(1, 1)` Nontangential Maximal Inequality, Rudin p. 245):
If `0 < α < 1`, `μ` is a complex Borel measure on `T`, and `u = P[dμ]`, then for all `0 < λ < ∞`,
`σ{N_α u > λ} ≤ (A(α, 1) / λ) ‖μ‖`. -/
theorem theorem11_25a {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (μ : ComplexMeasure UnitCircle) {lam : ℝ} (hlam : 0 < lam) :
    unitCircleMeasure {ζ : UnitCircle |
        ENNReal.ofReal lam < nontangentialMaximal α (poissonMeasureIntegral μ) ζ} ≤
      ENNReal.ofReal ((nontangentialLpConstant α 1 / lam) * μ.variation.real Set.univ) ∧
    unitCircleMeasure.real {ζ : UnitCircle |
        ENNReal.ofReal lam < nontangentialMaximal α (poissonMeasureIntegral μ) ζ} ≤
      (nontangentialLpConstant α 1 / lam) * μ.variation.real Set.univ := by
  let c_α : ℝ := nontangentialConstant α
  have hc_pos : 0 < c_α := nontangentialConstant_pos hα1
  have hsub : {ζ : UnitCircle |
        ENNReal.ofReal lam < nontangentialMaximal α (poissonMeasureIntegral μ) ζ} ⊆
      {ζ : UnitCircle | ENNReal.ofReal (c_α * lam) < complexCircleMeasureMaximal μ ζ} := by
    intro ζ hζ
    simp only [Set.mem_ofPred_eq] at hζ ⊢
    rw [ENNReal.ofReal_mul hc_pos.le]
    have hlt : ENNReal.ofReal c_α * ENNReal.ofReal lam <
        ENNReal.ofReal c_α * nontangentialMaximal α (poissonMeasureIntegral μ) ζ := by
      have hmul := ENNReal.mul_lt_mul_left (ENNReal.ofReal_pos.mpr hc_pos).ne'
        ENNReal.ofReal_ne_top hζ
      simpa only [mul_comm] using hmul
    exact hlt.trans_le (nontangentialMaximal_poissonMeasureIntegral_le hα0 hα1 μ ζ)
  have hweak := weak_type_complexCircleMeasureMaximal μ (mul_pos hc_pos hlam)
  have hconst : (3 / (c_α * lam)) * μ.variation.real Set.univ =
      (nontangentialLpConstant α 1 / lam) * μ.variation.real Set.univ := by
    unfold nontangentialLpConstant
    simp only [↓reduceIte, c_α]
    ring
  have h1 : unitCircleMeasure {ζ : UnitCircle |
        ENNReal.ofReal lam < nontangentialMaximal α (poissonMeasureIntegral μ) ζ} ≤
      ENNReal.ofReal ((nontangentialLpConstant α 1 / lam) * μ.variation.real Set.univ) := by
    rw [← hconst]
    exact (measure_mono hsub).trans hweak.1
  refine ⟨h1, ?_⟩
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (by
    rw [← hconst]
    exact mul_nonneg (div_nonneg (by norm_num) (mul_pos hc_pos hlam).le) measureReal_nonneg) h1

/-- Truncation-tail distribution bound for `circleMeasureMaximal (unitCircleMeasure.withDensity g)`:
for `0 < t` and integrable measurable `g : UnitCircle → ℝ≥0∞`,
`σ{M(g dσ) > t} ≤ (6 / t) ∫_{g > t/2} g dσ`. -/
theorem circleMeasureMaximal_truncation_tail {g : UnitCircle → ℝ≥0∞}
    (hg : Measurable g) (hg_fin : (∫⁻ η, g η ∂unitCircleMeasure) < ⊤)
    {t : ℝ} (ht : 0 < t) :
    unitCircleMeasure
        {ζ : UnitCircle |
          ENNReal.ofReal t < circleMeasureMaximal (unitCircleMeasure.withDensity g) ζ} ≤
      ENNReal.ofReal (6 / t) *
        ∫⁻ η in {η : UnitCircle | ENNReal.ofReal (t / 2) < g η}, g η ∂unitCircleMeasure := by
  let S : Set UnitCircle := {η : UnitCircle | ENNReal.ofReal (t / 2) < g η}
  have hS_meas : MeasurableSet S := measurableSet_lt measurable_const hg
  let g₁ : UnitCircle → ℝ≥0∞ := S.indicator g
  let g₂ : UnitCircle → ℝ≥0∞ := Sᶜ.indicator g
  have hg₁_meas : Measurable g₁ := hg.indicator hS_meas
  have hg₂_meas : Measurable g₂ := hg.indicator hS_meas.compl
  let ν₁ : Measure UnitCircle := unitCircleMeasure.withDensity g₁
  have hν₁_univ : ν₁ Set.univ = ∫⁻ η in S, g η ∂unitCircleMeasure := by
    dsimp only [ν₁, g₁]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_indicator hS_meas]
  have hν₁_fin : ν₁ Set.univ < ⊤ := by
    rw [hν₁_univ]
    exact (setLIntegral_le_lintegral S g).trans_lt hg_fin
  have : IsFiniteMeasure ν₁ := ⟨hν₁_fin⟩
  -- Pointwise subadditivity + boundedness of `g₂ ≤ t / 2`
  have hM_le : ∀ ζ : UnitCircle,
      circleMeasureMaximal (unitCircleMeasure.withDensity g) ζ ≤
        circleMeasureMaximal ν₁ ζ + ENNReal.ofReal (t / 2) := by
    intro ζ
    unfold circleMeasureMaximal
    refine iSup₂_le fun δ hδ => ?_
    have hδ_pos : 0 < δ := hδ
    let I := openCircleArc ζ δ
    have hI_meas : MeasurableSet I := (isOpen_openCircleArc ζ δ).measurableSet
    have hsplit : (unitCircleMeasure.withDensity g) I ≤
        ν₁ I + ENNReal.ofReal (t / 2) * unitCircleMeasure I := by
      rw [withDensity_apply _ hI_meas]
      have hsum : ∀ η : UnitCircle, g η = g₁ η + g₂ η := fun η =>
        congrFun (Set.indicator_self_add_compl S g).symm η
      simp_rw [hsum]
      rw [lintegral_add_left hg₁_meas]
      have h1 : (∫⁻ η in I, g₁ η ∂unitCircleMeasure) = ν₁ I :=
        (withDensity_apply g₁ hI_meas).symm
      have h2 : (∫⁻ η in I, g₂ η ∂unitCircleMeasure) ≤
          ENNReal.ofReal (t / 2) * unitCircleMeasure I := by
        calc (∫⁻ η in I, g₂ η ∂unitCircleMeasure)
            ≤ ∫⁻ _η in I, ENNReal.ofReal (t / 2) ∂unitCircleMeasure := by
              refine lintegral_mono fun η => ?_
              dsimp only [g₂]
              by_cases hη : η ∈ Sᶜ
              · rw [Set.indicator_of_mem hη]
                exact not_lt.mp hη
              · rw [Set.indicator_of_notMem hη]
                exact zero_le
          _ = ENNReal.ofReal (t / 2) * unitCircleMeasure I := by
              rw [lintegral_const, Measure.restrict_apply_univ]
      rw [h1]
      exact add_le_add le_rfl h2
    have hσ0 : unitCircleMeasure I ≠ 0 := unitCircleMeasure_openCircleArc_ne_zero ζ hδ_pos
    have hσ_top : unitCircleMeasure I ≠ ⊤ := measure_ne_top _ _
    calc (unitCircleMeasure.withDensity g) I / unitCircleMeasure I
        ≤ (ν₁ I + ENNReal.ofReal (t / 2) * unitCircleMeasure I) / unitCircleMeasure I :=
          ENNReal.div_le_div_right hsplit _
      _ = ν₁ I / unitCircleMeasure I +
            (ENNReal.ofReal (t / 2) * unitCircleMeasure I) / unitCircleMeasure I :=
          ENNReal.add_div
      _ = ν₁ I / unitCircleMeasure I + ENNReal.ofReal (t / 2) := by
          rw [ENNReal.mul_div_cancel_right hσ0 hσ_top]
      _ ≤ circleMeasureMaximal ν₁ ζ + ENNReal.ofReal (t / 2) :=
          add_le_add (le_iSup₂_of_le δ hδ le_rfl) le_rfl
  have hsub : {ζ : UnitCircle |
        ENNReal.ofReal t < circleMeasureMaximal (unitCircleMeasure.withDensity g) ζ} ⊆
      {ζ : UnitCircle | ENNReal.ofReal (t / 2) < circleMeasureMaximal ν₁ ζ} := by
    intro ζ hζ
    simp only [Set.mem_ofPred_eq] at hζ ⊢
    by_contra hle
    push Not at hle
    have hle_sum : circleMeasureMaximal (unitCircleMeasure.withDensity g) ζ ≤ ENNReal.ofReal t := by
      calc circleMeasureMaximal (unitCircleMeasure.withDensity g) ζ
          ≤ circleMeasureMaximal ν₁ ζ + ENNReal.ofReal (t / 2) := hM_le ζ
        _ ≤ ENNReal.ofReal (t / 2) + ENNReal.ofReal (t / 2) := add_le_add hle le_rfl
        _ = ENNReal.ofReal t := by
            rw [← ENNReal.ofReal_add (half_pos ht).le (half_pos ht).le, add_halves]
    exact not_le_of_gt hζ hle_sum
  have hweak := weak_type_circleMeasureMaximal ν₁ (half_pos ht)
  have h6 : (3 : ℝ) / (t / 2) = 6 / t := by ring
  rw [h6, hν₁_univ] at hweak
  exact (measure_mono hsub).trans hweak

/-- Strong `(p, p)` `L^p` bound for `circleMeasureMaximal (unitCircleMeasure.withDensity g)`
(`1 < p' < ∞`), proved via `layerCake_rpow_ennreal` + `weighted_truncation_tails` (Rudin 8.18(7)). -/
theorem circleMeasureMaximal_strong_bound {g : UnitCircle → ℝ≥0∞}
    (hg : Measurable g) (hg_fin : (∫⁻ η, g η ∂unitCircleMeasure) < ⊤)
    {p' : ℝ} (hp' : 1 < p') :
    (∫⁻ ζ, circleMeasureMaximal (unitCircleMeasure.withDensity g) ζ ^ p' ∂unitCircleMeasure) ≤
      ENNReal.ofReal (p' * 6 * (2 ^ (p' - 1) / (p' - 1))) *
        ∫⁻ η, g η ^ p' ∂unitCircleMeasure := by
  let M_g := circleMeasureMaximal (unitCircleMeasure.withDensity g)
  have hM_meas : Measurable M_g :=
    measurable_circleMeasureMaximal (unitCircleMeasure.withDensity g)
  have htbound : ∀ t : ℝ, 0 < t →
      unitCircleMeasure {ζ : UnitCircle | ENNReal.ofReal t < M_g ζ} *
          ENNReal.ofReal (t ^ (p' - 1)) ≤
        6 * (ENNReal.ofReal (t ^ (p' - 2)) *
          ∫⁻ η in {η : UnitCircle | ENNReal.ofReal (t / 2) < g η}, g η ∂unitCircleMeasure) := by
    intro t ht
    have htail := mul_le_mul_of_nonneg_right
      (circleMeasureMaximal_truncation_tail hg hg_fin ht) zero_le
      (a := ENNReal.ofReal (t ^ (p' - 1)))
    have hcoeff : ENNReal.ofReal (6 / t) * ENNReal.ofReal (t ^ (p' - 1)) =
        6 * ENNReal.ofReal (t ^ (p' - 2)) := by
      have h6 : (6 : ℝ≥0∞) = ENNReal.ofReal 6 := by norm_num
      rw [h6, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      calc (6 / t) * t ^ (p' - 1)
          = 6 * (t ^ (-1 : ℝ) * t ^ (p' - 1)) := by
              rw [Real.rpow_neg_one]
              ring
        _ = 6 * t ^ ((-1 : ℝ) + (p' - 1)) := by
              rw [← Real.rpow_add ht]
        _ = 6 * t ^ (p' - 2) := by
              congr 2
              ring
    calc unitCircleMeasure {ζ : UnitCircle | ENNReal.ofReal t < M_g ζ} *
            ENNReal.ofReal (t ^ (p' - 1))
        ≤ (ENNReal.ofReal (6 / t) *
            ∫⁻ η in {η : UnitCircle | ENNReal.ofReal (t / 2) < g η}, g η ∂unitCircleMeasure) *
            ENNReal.ofReal (t ^ (p' - 1)) := htail
      _ = (ENNReal.ofReal (6 / t) * ENNReal.ofReal (t ^ (p' - 1))) *
            ∫⁻ η in {η : UnitCircle | ENNReal.ofReal (t / 2) < g η}, g η ∂unitCircleMeasure := by
          ac_rfl
      _ = 6 * (ENNReal.ofReal (t ^ (p' - 2)) *
            ∫⁻ η in {η : UnitCircle | ENNReal.ofReal (t / 2) < g η}, g η ∂unitCircleMeasure) := by
          rw [hcoeff, mul_assoc]
  rw [RudinRCA.Chapter08.layerCake_rpow_ennreal unitCircleMeasure hM_meas (by linarith : 0 < p')]
  calc ENNReal.ofReal p' *
          ∫⁻ t in Set.Ioi 0,
            unitCircleMeasure {ζ : UnitCircle | ENNReal.ofReal t < M_g ζ} *
              ENNReal.ofReal (t ^ (p' - 1))
      ≤ ENNReal.ofReal p' *
          ∫⁻ t in Set.Ioi 0,
            6 * (ENNReal.ofReal (t ^ (p' - 2)) *
              ∫⁻ η in {η : UnitCircle | ENNReal.ofReal (t / 2) < g η}, g η ∂unitCircleMeasure) := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        exact setLIntegral_mono' measurableSet_Ioi fun t ht => htbound t ht
    _ = ENNReal.ofReal p' *
          (6 * (((2 : ℝ≥0∞) ^ (p' - 1) / ENNReal.ofReal (p' - 1)) *
            ∫⁻ η, g η ^ p' ∂unitCircleMeasure)) := by
        rw [lintegral_const_mul' 6 _ (by norm_num),
          RudinRCA.Chapter08.weighted_truncation_tails unitCircleMeasure hg hp']
    _ = ENNReal.ofReal (p' * 6 * (2 ^ (p' - 1) / (p' - 1))) *
          ∫⁻ η, g η ^ p' ∂unitCircleMeasure := by
        have hp'_pos : 0 < p' := by linarith
        have hp'm1_pos : 0 < p' - 1 := by linarith
        have h2_eq : ((2 : ℝ≥0∞) ^ (p' - 1)) = ENNReal.ofReal (2 ^ (p' - 1)) := by
          have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
          rw [h2, ← ENNReal.ofReal_rpow_of_pos (by norm_num)]
        have h6_eq : (6 : ℝ≥0∞) = ENNReal.ofReal 6 := by norm_num
        rw [h2_eq, h6_eq, ← ENNReal.ofReal_div_of_pos hp'm1_pos,
          ← mul_assoc, ← mul_assoc,
          ← ENNReal.ofReal_mul hp'_pos.le,
          ← ENNReal.ofReal_mul (by positivity)]

/-- Pointwise `L^∞` bound on `nontangentialMaximal`: for every `f` and every `ζ ∈ T`,
`(N_α P[f])(ζ) ≤ ‖f‖_∞` (`eLpNorm f ⊤ unitCircleMeasure`). -/
theorem nontangentialMaximal_unitPoissonIntegral_le_eLpNorm_top
    (α : ℝ) {f : UnitCircle → ℂ} (hf : AEStronglyMeasurable f unitCircleMeasure)
    (ζ : UnitCircle) :
    nontangentialMaximal α (unitPoissonIntegral f) ζ ≤ eLpNorm f ⊤ unitCircleMeasure := by
  rw [eLpNorm_exponent_top hf]
  change nontangentialMaximal α (unitPoissonIntegral f) ζ ≤
    essSup (fun η => ‖f η‖ₑ) unitCircleMeasure
  unfold nontangentialMaximal
  refine iSup₂_le fun z hz => ?_
  have hz_U : z ∈ Metric.ball (0 : ℂ) 1 := approachRegion_subset_ball α ζ hz
  have hae : ∀ᵐ η ∂unitCircleMeasure,
      ‖f η‖ₑ ≤ essSup (fun x => ‖f x‖ₑ) unitCircleMeasure := ae_le_essSup
  calc ‖unitPoissonIntegral f z‖ₑ
      ≤ ∫⁻ η : UnitCircle,
          ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) * ‖f η‖ₑ
            ∂unitCircleMeasure := enorm_unitPoissonIntegral_le hz_U
    _ ≤ ∫⁻ η : UnitCircle,
          ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) *
            essSup (fun x => ‖f x‖ₑ) unitCircleMeasure ∂unitCircleMeasure := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with η hη
        gcongr
    _ = (∫⁻ η : UnitCircle,
          ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ))
            ∂unitCircleMeasure) * essSup (fun x => ‖f x‖ₑ) unitCircleMeasure :=
        lintegral_mul_const _
          (continuous_poissonKernel_unitCircle hz_U).measurable.ennreal_ofReal
    _ = essSup (fun x => ‖f x‖ₑ) unitCircleMeasure := by
        rw [lintegral_poissonKernel_unitCircle hz_U, one_mul]

/-- 11.25(b) (Strong `(p, p)` Nontangential Maximal Inequality, Rudin p. 245):
If `0 < α < 1`, `1 < p ≤ ⊤`, `f ∈ L^p(T)` (`MemLp f p unitCircleMeasure`), and `u = P[f]`, then
`N_α u < ⊤` `σ`-a.e., `(N_α u).toReal ∈ L^p(T)`, and `‖N_α u‖_p ≤ A(α, p) ‖f‖_p`. -/
theorem theorem11_25b {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {p : ℝ≥0∞} (hp1 : 1 < p) {f : UnitCircle → ℂ} (hf : MemLp f p unitCircleMeasure) :
    let u : ℂ → ℂ := unitPoissonIntegral f
    (∀ᵐ ζ ∂unitCircleMeasure, nontangentialMaximal α u ζ < ⊤) ∧
    MemLp (fun ζ : UnitCircle => (nontangentialMaximal α u ζ).toReal) p unitCircleMeasure ∧
    eLpNorm (fun ζ : UnitCircle => (nontangentialMaximal α u ζ).toReal) p unitCircleMeasure ≤
      ENNReal.ofReal (nontangentialLpConstant α p) * eLpNorm f p unitCircleMeasure := by
  intro u
  have hN_meas : Measurable (nontangentialMaximal α u) :=
    measurable_nontangentialMaximal hα0 hα1 u
  have hN_real_smeas : AEStronglyMeasurable
      (fun ζ : UnitCircle => (nontangentialMaximal α u ζ).toReal) unitCircleMeasure :=
    hN_meas.ennreal_toReal.aestronglyMeasurable
  by_cases hp_top : p = ⊤
  · subst hp_top
    have hle_all : ∀ ζ : UnitCircle,
        nontangentialMaximal α u ζ ≤ eLpNorm f ⊤ unitCircleMeasure :=
      nontangentialMaximal_unitPoissonIntegral_le_eLpNorm_top α hf.aestronglyMeasurable
    have hlt_top_all : ∀ ζ : UnitCircle, nontangentialMaximal α u ζ < ⊤ :=
      fun ζ => (hle_all ζ).trans_lt hf.eLpNorm_lt_top
    have hel_le : eLpNorm (fun ζ : UnitCircle => (nontangentialMaximal α u ζ).toReal) ⊤
        unitCircleMeasure ≤ eLpNorm f ⊤ unitCircleMeasure := by
      rw [eLpNorm_exponent_top hN_real_smeas]
      change essSup (fun ζ => ‖(nontangentialMaximal α u ζ).toReal‖ₑ) unitCircleMeasure ≤
        eLpNorm f ⊤ unitCircleMeasure
      refine essSup_le_of_ae_le _ (ae_of_all _ fun ζ => ?_)
      dsimp only
      rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (hlt_top_all ζ).ne]
      exact hle_all ζ
    have hA_top : nontangentialLpConstant α ⊤ = 1 := by
      unfold nontangentialLpConstant
      simp
    refine ⟨ae_of_all _ hlt_top_all, hel_le.trans_lt hf.eLpNorm_lt_top, ?_⟩
    rw [hA_top, ENNReal.ofReal_one, one_mul]
    exact hel_le
  · have hp_ne1 : p ≠ 1 := hp1.ne'
    have hp_ne0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
    let p' : ℝ := p.toReal
    have hp'_gt1 : 1 < p' := by
      have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).mpr hp1
      simpa [p'] using this
    have hp'_pos : 0 < p' := zero_lt_one.trans hp'_gt1
    let c_α : ℝ := nontangentialConstant α
    have hc_pos : 0 < c_α := nontangentialConstant_pos hα1
    -- Measurable representative `g` of `‖f ·‖ₑ`
    obtain ⟨f₀, hf₀_smeas, hf₀_ae⟩ := hf.aestronglyMeasurable
    let g : UnitCircle → ℝ≥0∞ := fun η => ‖f₀ η‖ₑ
    have hg_meas : Measurable g := hf₀_smeas.measurable.enorm
    have hg_ae : g =ᵐ[unitCircleMeasure] fun η => ‖f η‖ₑ :=
      hf₀_ae.mono fun η hη => by dsimp only [g]; rw [hη]
    have hg_fin : (∫⁻ η, g η ∂unitCircleMeasure) < ⊤ := by
      rw [lintegral_congr_ae hg_ae]
      exact (hf.integrable hp1.le).hasFiniteIntegral
    let ν : Measure UnitCircle := unitCircleMeasure.withDensity g
    have : IsFiniteMeasure ν := ⟨by
      dsimp only [ν]
      rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]⟩
    -- Pointwise domination `c_α (N_α u)(ζ) ≤ (M ν)(ζ)`
    have hN_le_M : ∀ ζ : UnitCircle,
        nontangentialMaximal α u ζ ≤
          ENNReal.ofReal (1 / c_α) * circleMeasureMaximal ν ζ := by
      intro ζ
      let u_ν := poissonMeasureIntegral (ν.withDensityᵥ fun _ : UnitCircle => (1 : ℂ))
      have hu_le : nontangentialMaximal α u ζ ≤ nontangentialMaximal α u_ν ζ := by
        unfold nontangentialMaximal
        refine iSup₂_le fun z hz => ?_
        have hz_U : z ∈ Metric.ball (0 : ℂ) 1 := approachRegion_subset_ball α ζ hz
        have hK_meas : Measurable (fun η : UnitCircle =>
            ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ))) :=
          (continuous_poissonKernel_unitCircle hz_U).measurable.ennreal_ofReal
        have hint_ν : Integrable (fun η : UnitCircle => _root_.poissonKernel 0 z (η : ℂ)) ν :=
          (continuous_poissonKernel_unitCircle hz_U).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        have hu_ν_enorm : ‖u_ν z‖ₑ =
            ∫⁻ η : UnitCircle, ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) ∂ν := by
          dsimp only [u_ν]
          have hnn_ν : 0 ≤ positivePoissonIntegral ν z :=
            integral_nonneg (poissonKernel_unitCircle_nonneg hz_U)
          rw [poissonMeasureIntegral_withDensityᵥ_one ν hz_U, ← ofReal_norm,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn_ν]
          exact ofReal_integral_eq_lintegral_ofReal hint_ν
            (ae_of_all _ (poissonKernel_unitCircle_nonneg hz_U))
        have hle_z : ‖u z‖ₑ ≤ ‖u_ν z‖ₑ := by
          rw [hu_ν_enorm]
          dsimp only [ν]
          rw [lintegral_withDensity_eq_lintegral_mul _ hg_meas hK_meas]
          refine (enorm_unitPoissonIntegral_le hz_U).trans (le_of_eq ?_)
          refine lintegral_congr_ae (hg_ae.symm.mono fun η hη => ?_)
          dsimp only [Pi.mul_apply] at hη ⊢
          rw [hη, mul_comm]
        exact le_iSup₂_of_le z hz hle_z
      have h20 := theorem11_20_explicit hα0 hα1 ν ζ
      have hprod : ENNReal.ofReal c_α * nontangentialMaximal α u ζ ≤ circleMeasureMaximal ν ζ :=
        (mul_le_mul_of_nonneg_left hu_le zero_le).trans (h20.1.trans h20.2)
      calc nontangentialMaximal α u ζ
          = ENNReal.ofReal (1 / c_α) * (ENNReal.ofReal c_α * nontangentialMaximal α u ζ) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
              one_div_mul_cancel hc_pos.ne', ENNReal.ofReal_one, one_mul]
        _ ≤ ENNReal.ofReal (1 / c_α) * circleMeasureMaximal ν ζ :=
            mul_le_mul_of_nonneg_left hprod zero_le
    -- Apply `circleMeasureMaximal_strong_bound`
    let C_p : ℝ := p' * 6 * (2 ^ (p' - 1) / (p' - 1))
    have hCp_pos : 0 < C_p := by
      dsimp only [C_p]
      have : 0 < p' - 1 := sub_pos.mpr hp'_gt1
      positivity
    have hstrong := circleMeasureMaximal_strong_bound hg_meas hg_fin hp'_gt1
    have hlint_N : (∫⁻ ζ, nontangentialMaximal α u ζ ^ p' ∂unitCircleMeasure) ≤
        ENNReal.ofReal ((1 / c_α) ^ p' * C_p) * ∫⁻ η, ‖f η‖ₑ ^ p' ∂unitCircleMeasure := by
      calc (∫⁻ ζ, nontangentialMaximal α u ζ ^ p' ∂unitCircleMeasure)
          ≤ ∫⁻ ζ, (ENNReal.ofReal (1 / c_α) * circleMeasureMaximal ν ζ) ^ p' ∂unitCircleMeasure := by
            refine lintegral_mono fun ζ => ENNReal.rpow_le_rpow (hN_le_M ζ) hp'_pos.le
        _ = ENNReal.ofReal ((1 / c_α) ^ p') *
              ∫⁻ ζ, circleMeasureMaximal ν ζ ^ p' ∂unitCircleMeasure := by
            simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp'_pos.le,
              ← ENNReal.ofReal_rpow_of_pos (one_div_pos.mpr hc_pos)]
            exact lintegral_const_mul _
              ((measurable_circleMeasureMaximal ν).pow_const p')
        _ ≤ ENNReal.ofReal ((1 / c_α) ^ p') *
              (ENNReal.ofReal C_p * ∫⁻ η, g η ^ p' ∂unitCircleMeasure) :=
            mul_le_mul_of_nonneg_left hstrong zero_le
        _ = ENNReal.ofReal ((1 / c_α) ^ p' * C_p) *
              ∫⁻ η, ‖f η‖ₑ ^ p' ∂unitCircleMeasure := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            exact lintegral_congr_ae (hg_ae.mono fun η hη => by
              dsimp only at hη ⊢
              rw [hη])
    -- Relate `∫⁻ ‖f η‖ₑ ^ p'` to `eLpNorm f p unitCircleMeasure`
    have hf_lint_eq : (∫⁻ η, ‖f η‖ₑ ^ p' ∂unitCircleMeasure) ^ (1 / p') =
        eLpNorm f p unitCircleMeasure := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne0 hp_top hf.aestronglyMeasurable]
    have hf_lint_lt_top : (∫⁻ η, ‖f η‖ₑ ^ p' ∂unitCircleMeasure) < ⊤ := by
      by_contra hge
      push Not at hge
      have htop : (∫⁻ η, ‖f η‖ₑ ^ p' ∂unitCircleMeasure) = ⊤ := top_le_iff.mp hge
      have hlt := hf.eLpNorm_lt_top
      rw [← hf_lint_eq, htop, ENNReal.top_rpow_of_pos (one_div_pos.mpr hp'_pos)] at hlt
      exact lt_irrefl ⊤ hlt
    have hN_lint_lt_top : (∫⁻ ζ, nontangentialMaximal α u ζ ^ p' ∂unitCircleMeasure) < ⊤ :=
      hlint_N.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf_lint_lt_top)
    have hae_fin : ∀ᵐ ζ ∂unitCircleMeasure, nontangentialMaximal α u ζ < ⊤ := by
      filter_upwards [ae_lt_top (hN_meas.pow_const p') hN_lint_lt_top.ne] with ζ hlt
      by_contra hge
      push Not at hge
      rw [top_le_iff.mp hge, ENNReal.top_rpow_of_pos hp'_pos] at hlt
      exact lt_irrefl ⊤ hlt
    have hel_eq : eLpNorm (fun ζ : UnitCircle => (nontangentialMaximal α u ζ).toReal) p
        unitCircleMeasure =
        (∫⁻ ζ, nontangentialMaximal α u ζ ^ p' ∂unitCircleMeasure) ^ (1 / p') := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne0 hp_top hN_real_smeas]
      congr 1
      refine lintegral_congr_ae (hae_fin.mono fun ζ hζ => ?_)
      dsimp only [p']
      rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hζ.ne]
    have hconst_eq : (((1 / c_α) ^ p' * C_p) ^ (1 / p')) = nontangentialLpConstant α p := by
      unfold nontangentialLpConstant
      simp only [hp_ne1, hp_top, ↓reduceIte]
      change (((1 / c_α) ^ p' * C_p) ^ (1 / p')) = (C_p ^ p'⁻¹) / c_α
      rw [one_div p', Real.mul_rpow (by positivity) hCp_pos.le,
        ← Real.rpow_mul (by positivity), mul_inv_cancel₀ hp'_pos.ne', Real.rpow_one]
      ring
    have hel_bound : eLpNorm (fun ζ : UnitCircle => (nontangentialMaximal α u ζ).toReal) p
        unitCircleMeasure ≤
        ENNReal.ofReal (nontangentialLpConstant α p) * eLpNorm f p unitCircleMeasure := by
      rw [hel_eq, ← hf_lint_eq, ← hconst_eq]
      calc (∫⁻ ζ, nontangentialMaximal α u ζ ^ p' ∂unitCircleMeasure) ^ (1 / p')
          ≤ (ENNReal.ofReal ((1 / c_α) ^ p' * C_p) *
              ∫⁻ η, ‖f η‖ₑ ^ p' ∂unitCircleMeasure) ^ (1 / p') :=
            ENNReal.rpow_le_rpow hlint_N (one_div_pos.mpr hp'_pos).le
        _ = ENNReal.ofReal (((1 / c_α) ^ p' * C_p) ^ (1 / p')) *
              (∫⁻ η, ‖f η‖ₑ ^ p' ∂unitCircleMeasure) ^ (1 / p') := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hp'_pos).le,
              ENNReal.ofReal_rpow_of_pos (by positivity)]
    exact ⟨hae_fin,
      hel_bound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top),
      hel_bound⟩

/-- Literal 3.7 `L^∞` (`rudinEssSup`) form of 11.25(b) at `p = ⊤`. -/
theorem theorem11_25b_rudinEssSup {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {f : UnitCircle → ℂ} (hf : MemLp f ⊤ unitCircleMeasure) :
    rudinEssSup unitCircleMeasure
      (fun ζ : UnitCircle => (nontangentialMaximal α (unitPoissonIntegral f) ζ).toReal) ≤
    nontangentialLpConstant α ⊤ * rudinEssSup unitCircleMeasure f := by
  obtain ⟨_, hMem, hel⟩ := theorem11_25b hα0 hα1 ENNReal.one_lt_top hf
  have hσ0 : unitCircleMeasure Set.univ ≠ 0 := by simp
  rw [rudinEssSup_eq_eLpNorm_top_toReal hσ0 hMem,
    rudinEssSup_eq_eLpNorm_top_toReal hσ0 hf]
  have hlt : ENNReal.ofReal (nontangentialLpConstant α ⊤) * eLpNorm f ⊤ unitCircleMeasure ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top).ne
  have htoR := ENNReal.toReal_mono hlt hel
  rwa [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (nontangentialLpConstant_pos hα1 le_top).le] at htoR

/-- 11.25 (Master Theorem, Rudin pp. 244–245):
For `0 < α < 1` and `1 ≤ p ≤ ⊤`, there exist constants `A(α, p) < ∞` (`nontangentialLpConstant α p > 0`)
such that:
(a) for every complex Borel measure `μ` on `T`, `u = P[dμ]`, and `0 < λ < ∞`,
`σ{N_α u > λ} ≤ (A(α, 1) / λ) ‖μ‖`;
(b) for `1 < p ≤ ⊤`, `f ∈ L^p(T)`, and `u = P[f]`, `N_α u < ⊤` `σ`-a.e., `(N_α u).toReal ∈ L^p(T)`,
and `‖N_α u‖_p ≤ A(α, p) ‖f‖_p` (together with the literal 3.7 `rudinEssSup` bound at `p = ⊤`). -/
theorem theorem11_25 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ A : ℝ≥0∞ → ℝ,
      (∀ p : ℝ≥0∞, 1 ≤ p → 0 < A p) ∧
      (∀ (μ : ComplexMeasure UnitCircle) {lam : ℝ}, 0 < lam →
        unitCircleMeasure.real {ζ : UnitCircle |
          ENNReal.ofReal lam < nontangentialMaximal α (poissonMeasureIntegral μ) ζ} ≤
        (A 1 / lam) * μ.variation.real Set.univ) ∧
      (∀ {p : ℝ≥0∞}, 1 < p → ∀ {f : UnitCircle → ℂ}, MemLp f p unitCircleMeasure →
        (∀ᵐ ζ ∂unitCircleMeasure, nontangentialMaximal α (unitPoissonIntegral f) ζ < ⊤) ∧
        MemLp (fun ζ : UnitCircle =>
          (nontangentialMaximal α (unitPoissonIntegral f) ζ).toReal) p unitCircleMeasure ∧
        eLpNorm (fun ζ : UnitCircle =>
          (nontangentialMaximal α (unitPoissonIntegral f) ζ).toReal) p unitCircleMeasure ≤
          ENNReal.ofReal (A p) * eLpNorm f p unitCircleMeasure) ∧
      (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → ∀ f : Lp ℂ p unitCircleMeasure,
        ∃ N_lp : Lp ℝ p unitCircleMeasure,
          (∀ᵐ ζ ∂unitCircleMeasure,
            N_lp ζ = (nontangentialMaximal α (unitPoissonIntegral f) ζ).toReal) ∧
          ‖N_lp‖ ≤ A p * ‖f‖) ∧
      (∀ {f : UnitCircle → ℂ}, MemLp f ⊤ unitCircleMeasure →
        rudinEssSup unitCircleMeasure
          (fun ζ : UnitCircle => (nontangentialMaximal α (unitPoissonIntegral f) ζ).toReal) ≤
        A ⊤ * rudinEssSup unitCircleMeasure f) := by
  refine ⟨nontangentialLpConstant α, fun _ hp => nontangentialLpConstant_pos hα1 hp,
    fun μ _ hlam => (theorem11_25a hα0 hα1 μ hlam).2,
    fun hp1 _ hf => theorem11_25b hα0 hα1 hp1 hf, ?_,
    fun hf => theorem11_25b_rudinEssSup hα0 hα1 hf⟩
  intro p _ hp1 f
  obtain ⟨_, hMem, hel⟩ := theorem11_25b hα0 hα1 hp1 (Lp.memLp f)
  refine ⟨hMem.toLp _, hMem.coeFn_toLp, ?_⟩
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hMem.coeFn_toLp]
  have hlt : ENNReal.ofReal (nontangentialLpConstant α p) *
      eLpNorm f p unitCircleMeasure ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp f).eLpNorm_lt_top).ne
  have htoR := ENNReal.toReal_mono hlt hel
  rwa [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (nontangentialLpConstant_pos hα1 hp1.le).le] at htoR

end Node11_25

end RudinRCA.Chapter11

end

/-!
# Stage 3 Block 4: Representation Theorems and `H^∞` Boundary Values (Nodes 11.30, 11.26, 11.32)
-/

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped Real Topology ENNReal NNReal ComplexConjugate

namespace RudinRCA.Chapter11

/-! ### Node 11.30: Poisson Representation of `L^p`-Bounded and Positive Harmonic Functions -/

section Node11_30

/-- Radial dilation `z ↦ u(r z)` (`0 ≤ r < 1`) of a harmonic function `u` on `U = ball 0 1`
is continuous on `closedBall 0 1`, harmonic on `ball 0 1`, and equals the Poisson integral of
its radial restriction `u_r` on `ball 0 1` (Rudin p. 247). -/
theorem harmonicOn_dilate_poisson_eq {u : ℂ → ℂ}
    (hu : HarmonicOn u (Metric.ball (0 : ℂ) 1)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    let h_r : ℂ → ℂ := fun z => u ((r : ℂ) * z)
    ContinuousOn h_r (Metric.closedBall (0 : ℂ) 1) ∧
    HarmonicOn h_r (Metric.ball (0 : ℂ) 1) ∧
    ∀ z ∈ Metric.ball (0 : ℂ) 1,
      u ((r : ℂ) * z) = unitPoissonIntegral (unitRadialRestriction u r) z := by
  intro h_r
  have hcont : ContinuousOn h_r (Metric.closedBall (0 : ℂ) 1) := by
    refine hu.continuousOn.comp (continuous_const.mul continuous_id).continuousOn fun z hz => ?_
    have hz1 : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hz
    rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    nlinarith
  have hharm : HarmonicOn h_r (Metric.ball (0 : ℂ) 1) := by
    rcases eq_or_lt_of_le hr0 with rfl | hr_pos
    · have hconst : h_r = fun _ => u 0 := by
        ext z
        simp [h_r]
      rw [hconst]
      exact harmonicOn_of_mathlib fun z hz =>
        ((differentiableOn_const (u 0)).analyticAt (Metric.isOpen_ball.mem_nhds hz)).harmonicAt
    · have hsub : Metric.ball (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) 1 :=
        Metric.ball_subset_ball hr1.le
      have hcomp := (hu.mono hsub).comp_affine hr_pos
      simpa only [zero_add] using hcomp
  refine ⟨hcont, hharm, fun z hz => ?_⟩
  have h9 := (theorem11_9 hcont hharm).1 z hz
  have hP := (unitPoissonIntegral_eq_poissonIntegral h_r z).symm
  exact h9.trans hP

private def extendZeroSphere (g : C(UnitCircle, ℂ)) (z : ℂ) : ℂ :=
  open Classical in
  if hz : z ∈ Metric.sphere (0 : ℂ) 1 then g ⟨z, hz⟩ else 0

private theorem extendZeroSphere_apply (g : C(UnitCircle, ℂ)) (ζ : UnitCircle) :
    extendZeroSphere g (ζ : ℂ) = g ζ := by
  unfold extendZeroSphere
  simp

private theorem continuousOn_extendZeroSphere (g : C(UnitCircle, ℂ)) :
    ContinuousOn (extendZeroSphere g) (Metric.sphere (0 : ℂ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact g.continuous.congr fun ζ => (extendZeroSphere_apply g ζ).symm

/-- For every `g ∈ C(T)`, the radial restrictions `u_r` of `u = P[g]` converge uniformly on `T`
to `g` as `r → 1⁻` (Rudin 11.8 / 11.30, p. 248). -/
theorem tendstoUniformly_unitRadialRestriction_unitPoissonIntegral
    (g : C(UnitCircle, ℂ)) :
    TendstoUniformly (fun r : ℝ => unitRadialRestriction (unitPoissonIntegral g) r)
      g (𝓝[<] (1 : ℝ)) := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hunif := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_poissonIntegral_radial (continuousOn_extendZeroSphere g)) ε hε
  filter_upwards [hunif] with r hr ζ
  have hcongr : (g : UnitCircle → ℂ) = fun η : UnitCircle => extendZeroSphere g (η : ℂ) :=
    funext fun η => (extendZeroSphere_apply g η).symm
  have hval : unitRadialRestriction (unitPoissonIntegral g) r ζ =
      poissonIntegral (extendZeroSphere g) ((r : ℂ) * (ζ : ℂ)) := by
    unfold unitRadialRestriction
    rw [hcongr, unitPoissonIntegral_eq_poissonIntegral]
  rw [hval, ← extendZeroSphere_apply g ζ]
  exact hr (ζ : ℂ) ζ.2

/-- Fubini symmetry identity (Rudin 11.30(5), p. 248): for `f ∈ C(T)`, `μ` a complex Borel measure
on `T`, `u = P[f]`, `v = P[dμ]`, and `0 ≤ r < 1`,
`∫_T u_r dμ = ∫_T v_r f dσ`. -/
theorem complexMeasureIntegral_unitRadialRestriction_eq
    (μ : ComplexMeasure UnitCircle) (f : C(UnitCircle, ℂ))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    RudinRCA.Chapter10.complexMeasureIntegral μ
        (unitRadialRestriction (unitPoissonIntegral f) r) =
      ∫ ζ : UnitCircle,
        unitRadialRestriction (poissonMeasureIntegral μ) r ζ * f ζ ∂unitCircleMeasure := by
  have : IsFiniteMeasure μ.variation := isFiniteMeasure_complexMeasure_variation μ
  obtain ⟨h, hm, hn, hi, hr_pol⟩ := RudinRCA.Chapter06.theorem_6_12 μ
  have hf_int : Integrable (f : UnitCircle → ℂ) unitCircleMeasure :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hur_cont : Continuous (unitRadialRestriction (unitPoissonIntegral f) r) :=
    continuous_unitRadialRestriction_unitPoissonIntegral hf_int hr0 hr1
  have hlhs_polar :
      RudinRCA.Chapter10.complexMeasureIntegral μ
          (unitRadialRestriction (unitPoissonIntegral f) r) =
        ∫ η : UnitCircle,
          unitRadialRestriction (unitPoissonIntegral f) r η * h η ∂μ.variation :=
    RudinRCA.Chapter06.vectorIntegral_eq_polar μ h hm hn hi hr_pol
      (hur_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  rw [hlhs_polar]
  -- Define the product integrand on `UnitCircle × UnitCircle`
  let K : UnitCircle × UnitCircle → ℂ := fun p =>
    (_root_.poissonKernel 0 ((r : ℂ) * (p.1 : ℂ)) (p.2 : ℂ) : ℂ) * f p.2
  have hK_cont : Continuous K :=
    (Complex.continuous_ofReal.comp (continuous_poissonKernel_unitCircle_pair hr0 hr1)).mul
      (f.continuous.comp continuous_snd)
  obtain ⟨C, hC⟩ := (isCompact_range hK_cont.norm).bddAbove
  let F : UnitCircle × UnitCircle → ℂ := fun p => K p * h p.1
  have hF_meas : AEStronglyMeasurable F (μ.variation.prod unitCircleMeasure) :=
    hK_cont.aestronglyMeasurable.mul (hm.comp measurable_fst).aestronglyMeasurable
  have hF_int : Integrable F (μ.variation.prod unitCircleMeasure) := by
    refine Integrable.of_bound hF_meas C (ae_of_all _ fun p => ?_)
    dsimp only [F]
    rw [norm_mul, hn p.1, mul_one]
    exact hC ⟨p, rfl⟩
  have hlhs_F : (∫ η : UnitCircle,
        unitRadialRestriction (unitPoissonIntegral f) r η * h η ∂μ.variation) =
      ∫ η : UnitCircle, (∫ ζ : UnitCircle, F (η, ζ) ∂unitCircleMeasure) ∂μ.variation := by
    refine integral_congr_ae (ae_of_all _ fun η => ?_)
    dsimp only [unitRadialRestriction, unitPoissonIntegral, F, K]
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
    dsimp only
    rw [Complex.real_smul]
  have hrhs_F : (∫ ζ : UnitCircle,
        (∫ η : UnitCircle, F (η, ζ) ∂μ.variation) ∂unitCircleMeasure) =
      ∫ ζ : UnitCircle,
        unitRadialRestriction (poissonMeasureIntegral μ) r ζ * f ζ ∂unitCircleMeasure := by
    refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
    dsimp only
    have hz := radial_mem_ball_unitCircle hr0 hr1 ζ
    have hP_cont : Continuous (fun η : UnitCircle =>
        (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_poissonKernel_unitCircle hz)
    have hv_polar : unitRadialRestriction (poissonMeasureIntegral μ) r ζ =
        ∫ η : UnitCircle,
          (_root_.poissonKernel 0 ((r : ℂ) * (ζ : ℂ)) (η : ℂ) : ℂ) * h η ∂μ.variation := by
      unfold unitRadialRestriction poissonMeasureIntegral
      exact RudinRCA.Chapter06.vectorIntegral_eq_polar μ h hm hn hi hr_pol
        (hP_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    rw [hv_polar, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun η => ?_)
    dsimp only [F, K]
    rw [poissonKernel_unitCircle_radial_symm r η ζ]
    ring
  rw [hlhs_F, MeasureTheory.integral_integral_swap hF_int, hrhs_F]

/-- Uniqueness core of 11.30 (Rudin p. 248, (5)–(6)): for any complex Borel measure `μ` on `T`,
`P[dμ] = 0` on `U = ball 0 1` if and only if `μ = 0`. -/
theorem poissonMeasureIntegral_eq_zero_iff (μ : ComplexMeasure UnitCircle) :
    (∀ z ∈ Metric.ball (0 : ℂ) 1, poissonMeasureIntegral μ z = 0) ↔ μ = 0 := by
  constructor
  · intro hv0
    have : IsFiniteMeasure μ.variation := isFiniteMeasure_complexMeasure_variation μ
    have : μ.variation.Regular := inferInstance
    apply RudinRCA.Chapter06.theorem_6_19_zero μ
    intro f0
    let f : C(UnitCircle, ℂ) := ⟨f0, f0.continuous⟩
    obtain ⟨h, hm, hn, hi, hr_pol⟩ := RudinRCA.Chapter06.theorem_6_12 μ
    -- For every `0 ≤ r < 1`, `complexMeasureIntegral μ u_r = 0` by (5)
    have hur_zero : ∀ {r : ℝ}, 0 ≤ r → r < 1 →
        RudinRCA.Chapter10.complexMeasureIntegral μ
          (unitRadialRestriction (unitPoissonIntegral f) r) = 0 := by
      intro r hr0 hr1
      rw [complexMeasureIntegral_unitRadialRestriction_eq μ f hr0 hr1]
      refine integral_eq_zero_of_ae (ae_of_all _ fun ζ => ?_)
      dsimp only [Pi.zero_apply]
      have hv_r : unitRadialRestriction (poissonMeasureIntegral μ) r ζ = 0 :=
        hv0 _ (radial_mem_ball_unitCircle hr0 hr1 ζ)
      rw [hv_r, zero_mul]
    -- Pass to the limit `r → 1⁻` using uniform convergence `u_r → f`
    by_contra hne
    have hpos : 0 < ‖RudinRCA.Chapter06.complexIntegral μ f0‖ := norm_pos_iff.mpr hne
    let M : ℝ := μ.variation.real Set.univ + 1
    have hM_pos : 0 < M := by dsimp only [M]; linarith [ @measureReal_nonneg _ _ μ.variation Set.univ ]
    let ε : ℝ := ‖RudinRCA.Chapter06.complexIntegral μ f0‖ / (2 * M)
    have hε_pos : 0 < ε := div_pos hpos (by positivity)
    have hunif := Metric.tendstoUniformly_iff.mp
      (tendstoUniformly_unitRadialRestriction_unitPoissonIntegral f) ε hε_pos
    have hmem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) :=
      inter_mem (nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)) self_mem_nhdsWithin
    obtain ⟨r, ⟨hr_unif, hr_Ioo⟩⟩ := (hunif.and hmem).exists
    have hr0 : 0 ≤ r := hr_Ioo.1.le
    have hr1 : r < 1 := hr_Ioo.2
    have hf_int : Integrable (f : UnitCircle → ℂ) unitCircleMeasure :=
      f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hur_cont : Continuous (unitRadialRestriction (unitPoissonIntegral f) r) :=
      continuous_unitRadialRestriction_unitPoissonIntegral hf_int hr0 hr1
    have hc_f : RudinRCA.Chapter06.complexIntegral μ f0 =
        ∫ η : UnitCircle, f η * h η ∂μ.variation :=
      RudinRCA.Chapter06.vectorIntegral_eq_polar μ h hm hn hi hr_pol
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    have hc_ur : RudinRCA.Chapter10.complexMeasureIntegral μ
          (unitRadialRestriction (unitPoissonIntegral f) r) =
        ∫ η : UnitCircle,
          unitRadialRestriction (unitPoissonIntegral f) r η * h η ∂μ.variation :=
      RudinRCA.Chapter06.vectorIntegral_eq_polar μ h hm hn hi hr_pol
        (hur_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    have h0_eq := hur_zero hr0 hr1
    rw [hc_ur] at h0_eq
    have hdiff_eq : RudinRCA.Chapter06.complexIntegral μ f0 =
        ∫ η : UnitCircle,
          (f η - unitRadialRestriction (unitPoissonIntegral f) r η) * h η ∂μ.variation := by
      have hi1 : Integrable (fun η : UnitCircle => f η * h η) μ.variation :=
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mul_bdd
          hm.aestronglyMeasurable (ae_of_all _ fun η => (hn η).le)
      have hi2 : Integrable (fun η : UnitCircle =>
          unitRadialRestriction (unitPoissonIntegral f) r η * h η) μ.variation :=
        (hur_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mul_bdd
          hm.aestronglyMeasurable (ae_of_all _ fun η => (hn η).le)
      calc RudinRCA.Chapter06.complexIntegral μ f0
          = (∫ η : UnitCircle, f η * h η ∂μ.variation) -
              ∫ η : UnitCircle,
                unitRadialRestriction (unitPoissonIntegral f) r η * h η ∂μ.variation := by
            rw [hc_f, h0_eq, sub_zero]
        _ = ∫ η : UnitCircle,
              (f η - unitRadialRestriction (unitPoissonIntegral f) r η) * h η ∂μ.variation := by
            rw [← integral_sub hi1 hi2]
            exact integral_congr_ae (ae_of_all _ fun η => (sub_mul _ _ _).symm)
    have hbound : ‖RudinRCA.Chapter06.complexIntegral μ f0‖ ≤ ε * μ.variation.real Set.univ := by
      rw [hdiff_eq]
      calc ‖∫ η : UnitCircle,
              (f η - unitRadialRestriction (unitPoissonIntegral f) r η) * h η ∂μ.variation‖
          ≤ ∫ η : UnitCircle,
              ‖(f η - unitRadialRestriction (unitPoissonIntegral f) r η) * h η‖ ∂μ.variation :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ _η : UnitCircle, ε ∂μ.variation := by
            refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
              (integrable_const ε) (ae_of_all _ fun η => ?_)
            dsimp only
            rw [norm_mul, hn η, mul_one, ← dist_eq_norm]
            exact (hr_unif η).le
        _ = ε * μ.variation.real Set.univ := by
            rw [integral_const, smul_eq_mul, mul_comm]
    have hlt : ε * μ.variation.real Set.univ < ‖RudinRCA.Chapter06.complexIntegral μ f0‖ := by
      have hvar_lt : μ.variation.real Set.univ < M := by dsimp only [M]; linarith
      calc ε * μ.variation.real Set.univ
          ≤ ε * M := mul_le_mul_of_nonneg_left hvar_lt.le hε_pos.le
        _ = ‖RudinRCA.Chapter06.complexIntegral μ f0‖ / 2 := by
            dsimp only [ε]
            field_simp [hM_pos.ne']
        _ < ‖RudinRCA.Chapter06.complexIntegral μ f0‖ := half_lt_self hpos
    exact not_lt_of_ge hbound hlt
  · rintro rfl z _
    unfold poissonMeasureIntegral RudinRCA.Chapter10.complexMeasureIntegral
    simp

/-- Injectivity of `μ ↦ P[dμ]` on all complex Borel measures on `T = UnitCircle`. -/
theorem poissonMeasureIntegral_inj {μ₁ μ₂ : ComplexMeasure UnitCircle}
    (h : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      poissonMeasureIntegral μ₁ z = poissonMeasureIntegral μ₂ z) :
    μ₁ = μ₂ := by
  apply sub_eq_zero.mp
  rw [← poissonMeasureIntegral_eq_zero_iff]
  intro z hz
  rw [poissonMeasureIntegral_sub μ₁ μ₂ hz, h z hz, sub_self]

/-- Uniqueness of `L¹(T)` boundary functions under the Poisson integral on `U = ball 0 1`. -/
theorem unitPoissonIntegral_ae_eq_of_eq_on_ball {f₁ f₂ : UnitCircle → ℂ}
    (hf₁ : Integrable f₁ unitCircleMeasure) (hf₂ : Integrable f₂ unitCircleMeasure)
    (h : ∀ z ∈ Metric.ball (0 : ℂ) 1, unitPoissonIntegral f₁ z = unitPoissonIntegral f₂ z) :
    f₁ =ᵐ[unitCircleMeasure] f₂ := by
  have hμ : unitCircleMeasure.withDensityᵥ f₁ = unitCircleMeasure.withDensityᵥ f₂ := by
    apply poissonMeasureIntegral_inj
    intro z hz
    rw [poissonMeasureIntegral_withDensityᵥ hf₁ hz,
      poissonMeasureIntegral_withDensityᵥ hf₂ hz, h z hz]
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun E _ _ => hf₁.integrableOn) (fun E _ _ => hf₂.integrableOn) fun E hE _ => ?_
  have hev := congrArg (fun c : ComplexMeasure UnitCircle => c E) hμ
  simpa only [withDensityᵥ_apply hf₁ hE, withDensityᵥ_apply hf₂ hE] using hev

/-- Uniqueness of `Lp ℂ p unitCircleMeasure` boundary classes (`1 ≤ p ≤ ⊤`) under `P[f]`. -/
theorem unitPoissonIntegral_lp_inj (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {f₁ f₂ : Lp ℂ p unitCircleMeasure}
    (h : ∀ z ∈ Metric.ball (0 : ℂ) 1, unitPoissonIntegral f₁ z = unitPoissonIntegral f₂ z) :
    f₁ = f₂ := by
  apply Lp.ext
  exact unitPoissonIntegral_ae_eq_of_eq_on_ball
    ((Lp.memLp f₁).integrable (Fact.out : 1 ≤ p))
    ((Lp.memLp f₂).integrable (Fact.out : 1 ≤ p)) h

private def radialSeq (n : ℕ) : ℝ :=
  1 - 1 / ((n : ℝ) + 2)

private theorem radialSeq_mem_Ioo (n : ℕ) : radialSeq n ∈ Set.Ioo (0 : ℝ) 1 := by
  dsimp only [radialSeq]
  have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hlt1 : 1 / ((n : ℝ) + 2) < 1 := (div_lt_one hden).mpr (by linarith)
  have hpos : 0 < 1 / ((n : ℝ) + 2) := div_pos zero_lt_one hden
  exact ⟨by linarith, by linarith⟩

private theorem tendsto_radialSeq : Tendsto radialSeq atTop (𝓝 (1 : ℝ)) := by
  unfold radialSeq
  have hdiv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds)
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hdiv

/-- 11.30(a) (Theorem, Rudin pp. 247–248):
Suppose `u` is harmonic in `U = ball 0 1` and `sup_{0 < r < 1} ‖u_r‖₁ < ∞`.
Then there is a unique complex Borel measure `μ` on `T = UnitCircle` such that `u = P[dμ]` on `U`;
moreover `‖μ‖ = |μ|(T) = sup_{0 < r < 1} ‖u_r‖₁ = sup_{0 ≤ r < 1} ‖u_r‖₁`. -/
theorem theorem11_30a {u : ℂ → ℂ} (hu : HarmonicOn u (Metric.ball (0 : ℂ) 1))
    (hsup : (⨆ r ∈ Set.Ioo (0 : ℝ) 1,
      eLpNorm (unitRadialRestriction u r) 1 unitCircleMeasure) < ⊤) :
    (∃! μ : ComplexMeasure UnitCircle,
      ∀ z ∈ Metric.ball (0 : ℂ) 1, u z = poissonMeasureIntegral μ z) ∧
    ∃ μ : ComplexMeasure UnitCircle,
      (∀ z ∈ Metric.ball (0 : ℂ) 1, u z = poissonMeasureIntegral μ z) ∧
      μ.variation Set.univ =
        (⨆ r ∈ Set.Ioo (0 : ℝ) 1,
          eLpNorm (unitRadialRestriction u r) 1 unitCircleMeasure) ∧
      μ.variation Set.univ =
        (⨆ r ∈ Set.Ico (0 : ℝ) 1,
          eLpNorm (unitRadialRestriction u r) 1 unitCircleMeasure) ∧
      μ.variation.real Set.univ =
        (⨆ r ∈ Set.Ioo (0 : ℝ) 1,
          eLpNorm (unitRadialRestriction u r) 1 unitCircleMeasure).toReal := by
  let M_enn : ℝ≥0∞ :=
    ⨆ r ∈ Set.Ioo (0 : ℝ) 1, eLpNorm (unitRadialRestriction u r) 1 unitCircleMeasure
  let M : ℝ := M_enn.toReal
  have hM_nonneg : 0 ≤ M := ENNReal.toReal_nonneg
  -- Construct `Λ_n ∈ StrongDual ℂ C(UnitCircle, ℂ)` along `r_n = radialSeq n`
  have hur_cont : ∀ n : ℕ, Continuous (unitRadialRestriction u (radialSeq n)) := fun n => by
    have hr := radialSeq_mem_Ioo n
    exact hu.continuousOn.comp_continuous (continuous_const.mul continuous_subtype_val)
      (fun ζ => radial_mem_ball_unitCircle hr.1.le hr.2 ζ)
  have hur_l1 : ∀ n : ℕ,
      (∫ ζ : UnitCircle, ‖unitRadialRestriction u (radialSeq n) ζ‖ ∂unitCircleMeasure) ≤ M := by
    intro n
    have hr := radialSeq_mem_Ioo n
    have hle : eLpNorm (unitRadialRestriction u (radialSeq n)) 1 unitCircleMeasure ≤ M_enn :=
      le_iSup₂_of_le (radialSeq n) hr le_rfl
    have hint_eq : (∫ ζ : UnitCircle,
          ‖unitRadialRestriction u (radialSeq n) ζ‖ ∂unitCircleMeasure) =
        (eLpNorm (unitRadialRestriction u (radialSeq n)) 1 unitCircleMeasure).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm (hur_cont n).aestronglyMeasurable,
        integral_norm_eq_lintegral_enorm (hur_cont n).aestronglyMeasurable]
    rw [hint_eq]
    exact ENNReal.toReal_mono hsup.ne hle
  let Λ_lin : ℕ → C(UnitCircle, ℂ) →ₗ[ℂ] ℂ := fun n =>
    { toFun := fun g => ∫ ζ : UnitCircle,
        g ζ * unitRadialRestriction u (radialSeq n) ζ ∂unitCircleMeasure
      map_add' := fun g₁ g₂ => by
        have hi₁ : Integrable (fun ζ : UnitCircle =>
            g₁ ζ * unitRadialRestriction u (radialSeq n) ζ) unitCircleMeasure :=
          (g₁.continuous.mul (hur_cont n)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        have hi₂ : Integrable (fun ζ : UnitCircle =>
            g₂ ζ * unitRadialRestriction u (radialSeq n) ζ) unitCircleMeasure :=
          (g₂.continuous.mul (hur_cont n)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        simp_rw [ContinuousMap.add_apply, add_mul]
        exact integral_add hi₁ hi₂
      map_smul' := fun c g => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
  let Λ : ℕ → StrongDual ℂ C(UnitCircle, ℂ) := fun n =>
    (Λ_lin n).mkContinuous M fun g => by
      calc ‖∫ ζ : UnitCircle,
              g ζ * unitRadialRestriction u (radialSeq n) ζ ∂unitCircleMeasure‖
          ≤ ∫ ζ : UnitCircle,
              ‖g ζ * unitRadialRestriction u (radialSeq n) ζ‖ ∂unitCircleMeasure :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ ζ : UnitCircle,
              ‖g‖ * ‖unitRadialRestriction u (radialSeq n) ζ‖ ∂unitCircleMeasure := by
            refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
              (((hur_cont n).norm.integrable_of_hasCompactSupport
                (HasCompactSupport.of_compactSpace _)).const_mul ‖g‖)
              (ae_of_all _ fun ζ => ?_)
            dsimp only
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm g ζ) (norm_nonneg _)
        _ = ‖g‖ * ∫ ζ : UnitCircle,
              ‖unitRadialRestriction u (radialSeq n) ζ‖ ∂unitCircleMeasure :=
            integral_const_mul _ _
        _ ≤ M * ‖g‖ := by
            rw [mul_comm M ‖g‖]
            exact mul_le_mul_of_nonneg_left (hur_l1 n) (norm_nonneg g)
  have hΛ_norm : ∀ n : ℕ, ‖Λ n‖ ≤ M := fun n =>
    LinearMap.mkContinuous_norm_le (Λ_lin n) hM_nonneg _
  obtain ⟨φ, Λ_lim, hφ_mono, hΛ_pt, _, hΛ_lim_le⟩ := theorem11_29 hΛ_norm
  -- Transfer `Λ_lim` to `ZeroAtInftyContinuousMap UnitCircle ℂ →L[ℂ] ℂ` and apply 6.19
  let Φ : ZeroAtInftyContinuousMap UnitCircle ℂ →L[ℂ] ℂ :=
    Λ_lim.comp continuousMapEquivC0UnitCircle.symm.toLinearIsometry.toContinuousLinearMap
  have hΦ_norm : ‖Φ‖ ≤ M := by
    refine ContinuousLinearMap.opNorm_le_bound Φ hM_nonneg fun f0 => ?_
    calc ‖Φ f0‖ = ‖Λ_lim (continuousMapEquivC0UnitCircle.symm f0)‖ := rfl
      _ ≤ ‖Λ_lim‖ * ‖continuousMapEquivC0UnitCircle.symm f0‖ := Λ_lim.le_opNorm _
      _ = ‖Λ_lim‖ * ‖f0‖ := by rw [continuousMapEquivC0UnitCircle.symm.norm_map]
      _ ≤ M * ‖f0‖ := mul_le_mul_of_nonneg_right hΛ_lim_le (norm_nonneg f0)
  obtain ⟨μ, _, hμ_rep, hμ_norm, _⟩ := RudinRCA.Chapter06.theorem_6_19 Φ
  have : IsFiniteMeasure μ.variation := isFiniteMeasure_complexMeasure_variation μ
  -- Show `u z = poissonMeasureIntegral μ z` for every `z ∈ ball 0 1`
  have hu_eq : ∀ z ∈ Metric.ball (0 : ℂ) 1, u z = poissonMeasureIntegral μ z := by
    intro z hz
    let g_z : C(UnitCircle, ℂ) :=
      ⟨fun η => (_root_.poissonKernel 0 z (η : ℂ) : ℂ),
        Complex.continuous_ofReal.comp (continuous_poissonKernel_unitCircle hz)⟩
    have hseq_eq : ∀ k : ℕ, Λ (φ k) g_z = u ((radialSeq (φ k) : ℂ) * z) := by
      intro k
      have hr := radialSeq_mem_Ioo (φ k)
      have hdil := (harmonicOn_dilate_poisson_eq hu hr.1.le hr.2).2.2 z hz
      rw [hdil]
      dsimp only [Λ, LinearMap.mkContinuous_apply, Λ_lin, LinearMap.coe_mk, AddHom.coe_mk,
        g_z, ContinuousMap.coe_mk, unitPoissonIntegral]
      refine integral_congr_ae (ae_of_all _ fun η => ?_)
      dsimp only
      rw [Complex.real_smul]
    have hr_sub : Tendsto (fun k : ℕ => radialSeq (φ k)) atTop (𝓝 1) :=
      tendsto_radialSeq.comp hφ_mono.tendsto_atTop
    have hz_sub : Tendsto (fun k : ℕ => (radialSeq (φ k) : ℂ) * z) atTop (𝓝 z) := by
      simpa only [Function.comp_def, Complex.ofReal_one, one_mul] using
        ((Complex.continuous_ofReal.tendsto 1).comp hr_sub).mul_const z
    have hu_cont_z : ContinuousAt u z :=
      hu.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hz)
    have hlim1 : Tendsto (fun k : ℕ => Λ (φ k) g_z) atTop (𝓝 (u z)) :=
      (hu_cont_z.tendsto.comp hz_sub).congr fun k => (hseq_eq k).symm
    have hlim2 : Tendsto (fun k : ℕ => Λ (φ k) g_z) atTop (𝓝 (poissonMeasureIntegral μ z)) := by
      have hval : Λ_lim g_z = poissonMeasureIntegral μ z := by
        have h1 : Φ (continuousMapEquivC0UnitCircle g_z) = Λ_lim g_z := by
          dsimp only [Φ, ContinuousLinearMap.comp_apply]
          simp
        rw [← h1, hμ_rep (continuousMapEquivC0UnitCircle g_z)]
        rfl
      rw [← hval]
      exact hΛ_pt g_z
    exact tendsto_nhds_unique hlim1 hlim2
  -- Exact total-variation norm equalities via 11.17
  have hvar_le_M : μ.variation Set.univ ≤ M_enn := by
    have hreal_le : μ.variation.real Set.univ ≤ M := hμ_norm ▸ hΦ_norm
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ.variation Set.univ)]
    exact (ENNReal.ofReal_le_ofReal hreal_le).trans
      (le_of_eq (ENNReal.ofReal_toReal hsup.ne))
  have hIco_le_var :
      (⨆ r ∈ Set.Ico (0 : ℝ) 1,
        eLpNorm (unitRadialRestriction u r) 1 unitCircleMeasure) ≤ μ.variation Set.univ := by
    refine iSup₂_le fun r hr => ?_
    have heq_r : unitRadialRestriction u r =
        unitRadialRestriction (poissonMeasureIntegral μ) r := by
      ext ζ
      exact hu_eq _ (radial_mem_ball_unitCircle hr.1 hr.2 ζ)
    rw [heq_r]
    exact ((theorem11_17 μ).2.2 hr.1 hr.2).2.2
  have hM_le_Ico : M_enn ≤
      ⨆ r ∈ Set.Ico (0 : ℝ) 1,
        eLpNorm (unitRadialRestriction u r) 1 unitCircleMeasure :=
    iSup_le_iSup_of_subset Set.Ioo_subset_Ico_self
  have hvar_eq_M : μ.variation Set.univ = M_enn :=
    le_antisymm hvar_le_M (hM_le_Ico.trans hIco_le_var)
  have hvar_eq_Ico : μ.variation Set.univ =
      ⨆ r ∈ Set.Ico (0 : ℝ) 1,
        eLpNorm (unitRadialRestriction u r) 1 unitCircleMeasure :=
    le_antisymm (hvar_eq_M ▸ hM_le_Ico) hIco_le_var
  refine ⟨⟨μ, hu_eq, fun ν hν => poissonMeasureIntegral_inj fun z hz =>
      (hν z hz).symm.trans (hu_eq z hz)⟩,
    μ, hu_eq, hvar_eq_M, hvar_eq_Ico, ?_⟩
  rw [measureReal_def, hvar_eq_M]

private theorem exists_holderConjugate_unit {p : ℝ≥0∞} (hp : 1 < p) :
    ∃ q : ℝ≥0∞, 1 ≤ q ∧ q ≠ ⊤ ∧ p.HolderConjugate q := by
  by_cases hp_top : p = ⊤
  · subst hp_top
    refine ⟨1, le_rfl, ENNReal.one_ne_top, ?_⟩
    rw [ENNReal.holderConjugate_iff]
    simp
  · let p' : ℝ := p.toReal
    have hp'_gt1 : 1 < p' := by
      have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).mpr hp
      simpa [p'] using this
    have hp'_pos : 0 < p' := zero_lt_one.trans hp'_gt1
    have hpm1_pos : 0 < p' - 1 := sub_pos.mpr hp'_gt1
    let q' : ℝ := p' / (p' - 1)
    have hq'_gt1 : 1 < q' := (one_lt_div hpm1_pos).mpr (by linarith)
    refine ⟨ENNReal.ofReal q', ?_, ENNReal.ofReal_ne_top, ?_⟩
    · rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hq'_gt1.le
    · rw [ENNReal.holderConjugate_iff]
      have hp_eq : p = ENNReal.ofReal p' := (ENNReal.ofReal_toReal hp_top).symm
      rw [hp_eq, ← ENNReal.ofReal_inv_of_pos hp'_pos,
        ← ENNReal.ofReal_inv_of_pos (zero_lt_one.trans hq'_gt1),
        ← ENNReal.ofReal_add (inv_nonneg.mpr hp'_pos.le)
          (inv_nonneg.mpr (zero_lt_one.trans hq'_gt1).le)]
      have hsum : p'⁻¹ + q'⁻¹ = 1 := by
        dsimp only [q']
        field_simp [hp'_pos.ne', hpm1_pos.ne']
        ring
      rw [hsum, ENNReal.ofReal_one]

/-- 11.30(b) (Theorem, Rudin pp. 247–248):
Suppose `u` is harmonic in `U = ball 0 1`, `1 < p ≤ ⊤`, and `sup_{0 < r < 1} ‖u_r‖_p < ∞`.
Then there is a unique `f ∈ L^p(T)` (`Lp ℂ p unitCircleMeasure`) such that `u = P[f]` on `U`;
moreover `‖f‖_p = sup_{0 < r < 1} ‖u_r‖_p = sup_{0 ≤ r < 1} ‖u_r‖_p` (and at `p = ⊤`,
`rudinEssSup unitCircleMeasure f = ‖f‖`). -/
theorem theorem11_30b {u : ℂ → ℂ} (hu : HarmonicOn u (Metric.ball (0 : ℂ) 1))
    {p : ℝ≥0∞} (hp1 : 1 < p)
    (hsup : (⨆ r ∈ Set.Ioo (0 : ℝ) 1,
      eLpNorm (unitRadialRestriction u r) p unitCircleMeasure) < ⊤) :
    have : Fact (1 ≤ p) := ⟨hp1.le⟩
    (∃! f : Lp ℂ p unitCircleMeasure,
      ∀ z ∈ Metric.ball (0 : ℂ) 1, u z = unitPoissonIntegral f z) ∧
    ∃ f : Lp ℂ p unitCircleMeasure,
      (∀ z ∈ Metric.ball (0 : ℂ) 1, u z = unitPoissonIntegral f z) ∧
      eLpNorm f p unitCircleMeasure =
        (⨆ r ∈ Set.Ioo (0 : ℝ) 1,
          eLpNorm (unitRadialRestriction u r) p unitCircleMeasure) ∧
      eLpNorm f p unitCircleMeasure =
        (⨆ r ∈ Set.Ico (0 : ℝ) 1,
          eLpNorm (unitRadialRestriction u r) p unitCircleMeasure) ∧
      ‖f‖ =
        (⨆ r ∈ Set.Ioo (0 : ℝ) 1,
          eLpNorm (unitRadialRestriction u r) p unitCircleMeasure).toReal ∧
      (p = ⊤ → rudinEssSup unitCircleMeasure f = ‖f‖) := by
  let _ : Fact (1 ≤ p) := ⟨hp1.le⟩
  obtain ⟨q, hq1, hq_top, hpq⟩ := exists_holderConjugate_unit hp1
  let _ : Fact (1 ≤ q) := ⟨hq1⟩
  let _ : q.HolderConjugate p := hpq.symm
  let _ : TopologicalSpace.SeparableSpace (Lp ℂ q unitCircleMeasure) :=
    separableSpace_lp_unitCircle q hq_top
  let M_enn : ℝ≥0∞ :=
    ⨆ r ∈ Set.Ioo (0 : ℝ) 1, eLpNorm (unitRadialRestriction u r) p unitCircleMeasure
  let M : ℝ := M_enn.toReal
  -- Construct `Λ_n ∈ StrongDual ℂ (Lp ℂ q unitCircleMeasure)` via `Chapter06.theorem_6_15`
  let ur_c : ∀ n : ℕ, C(UnitCircle, ℂ) := fun n =>
    ⟨unitRadialRestriction u (radialSeq n), by
      have hr := radialSeq_mem_Ioo n
      exact hu.continuousOn.comp_continuous (continuous_const.mul continuous_subtype_val)
        (fun ζ => radial_mem_ball_unitCircle hr.1.le hr.2 ζ)⟩
  let ur_lp : ∀ n : ℕ, Lp ℂ p unitCircleMeasure := fun n =>
    ContinuousMap.toLp p unitCircleMeasure ℂ (ur_c n)
  have hur_norm : ∀ n : ℕ, ‖ur_lp n‖ ≤ M := by
    intro n
    have hr := radialSeq_mem_Ioo n
    rw [Lp.norm_def,
      eLpNorm_congr_ae (ContinuousMap.coeFn_toLp (p := p) (𝕜 := ℂ) unitCircleMeasure (ur_c n))]
    exact ENNReal.toReal_mono hsup.ne (le_iSup₂_of_le (radialSeq n) hr le_rfl)
  choose Λ hΛ_eq hΛ_le using fun n : ℕ =>
    RudinRCA.Chapter06.theorem_6_15 unitCircleMeasure q p (ur_lp n)
  have hΛ_M : ∀ n : ℕ, ‖Λ n‖ ≤ M := fun n => (hΛ_le n).trans (hur_norm n)
  obtain ⟨φ, Λ_lim, hφ_mono, hΛ_pt, _, hΛ_lim_le⟩ := theorem11_29 hΛ_M
  -- Represent `Λ_lim` by `f ∈ Lp ℂ p unitCircleMeasure` via `Chapter06.theorem_6_16`
  obtain ⟨f, ⟨hf_rep, hf_norm_eq⟩, _⟩ :=
    RudinRCA.Chapter06.theorem_6_16 unitCircleMeasure q p hq_top Λ_lim
  have hf_le_M : ‖f‖ ≤ M := hf_norm_eq ▸ hΛ_lim_le
  -- Identify `u z = unitPoissonIntegral f z` on `ball 0 1`
  have hu_eq : ∀ z ∈ Metric.ball (0 : ℂ) 1, u z = unitPoissonIntegral f z := by
    intro z hz
    let K_z : C(UnitCircle, ℂ) :=
      ⟨fun η => (_root_.poissonKernel 0 z (η : ℂ) : ℂ),
        Complex.continuous_ofReal.comp (continuous_poissonKernel_unitCircle hz)⟩
    let g_z : Lp ℂ q unitCircleMeasure := ContinuousMap.toLp q unitCircleMeasure ℂ K_z
    have hg_coe : (g_z : UnitCircle → ℂ) =ᵐ[unitCircleMeasure] K_z :=
      ContinuousMap.coeFn_toLp (p := q) (𝕜 := ℂ) unitCircleMeasure K_z
    have hseq_eq : ∀ k : ℕ, Λ (φ k) g_z = u ((radialSeq (φ k) : ℂ) * z) := by
      intro k
      have hr := radialSeq_mem_Ioo (φ k)
      have hdil := (harmonicOn_dilate_poisson_eq hu hr.1.le hr.2).2.2 z hz
      rw [hdil, hΛ_eq (φ k) g_z]
      unfold unitPoissonIntegral
      refine integral_congr_ae ?_
      filter_upwards [hg_coe,
        ContinuousMap.coeFn_toLp (p := p) (𝕜 := ℂ) unitCircleMeasure (ur_c (φ k))] with η hη₁ hη₂
      rw [hη₁, hη₂]
      dsimp only [K_z, ur_c, ContinuousMap.coe_mk]
      rw [Complex.real_smul]
      rfl
    have hr_sub : Tendsto (fun k : ℕ => radialSeq (φ k)) atTop (𝓝 1) :=
      tendsto_radialSeq.comp hφ_mono.tendsto_atTop
    have hz_sub : Tendsto (fun k : ℕ => (radialSeq (φ k) : ℂ) * z) atTop (𝓝 z) := by
      simpa only [Function.comp_def, Complex.ofReal_one, one_mul] using
        ((Complex.continuous_ofReal.tendsto 1).comp hr_sub).mul_const z
    have hu_cont_z : ContinuousAt u z :=
      hu.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hz)
    have hlim1 : Tendsto (fun k : ℕ => Λ (φ k) g_z) atTop (𝓝 (u z)) :=
      (hu_cont_z.tendsto.comp hz_sub).congr fun k => (hseq_eq k).symm
    have hlim2 : Tendsto (fun k : ℕ => Λ (φ k) g_z) atTop (𝓝 (unitPoissonIntegral f z)) := by
      have hval : Λ_lim g_z = unitPoissonIntegral f z := by
        rw [hf_rep g_z]
        unfold unitPoissonIntegral
        refine integral_congr_ae (hg_coe.mono fun η hη => ?_)
        dsimp only
        rw [hη]
        dsimp only [K_z, ContinuousMap.coe_mk]
        rw [Complex.real_smul]
      rw [← hval]
      exact hΛ_pt g_z
    exact tendsto_nhds_unique hlim1 hlim2
  -- Exact `Lp` norm equalities via 11.16
  have hf_enn_le : eLpNorm f p unitCircleMeasure ≤ M_enn := by
    rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f), ← Lp.norm_def]
    exact (ENNReal.ofReal_le_ofReal hf_le_M).trans
      (le_of_eq (ENNReal.ofReal_toReal hsup.ne))
  have hIco_le_f :
      (⨆ r ∈ Set.Ico (0 : ℝ) 1,
        eLpNorm (unitRadialRestriction u r) p unitCircleMeasure) ≤
      eLpNorm f p unitCircleMeasure := by
    refine iSup₂_le fun r hr => ?_
    have heq_r : unitRadialRestriction u r =
        unitRadialRestriction (unitPoissonIntegral f) r := by
      ext ζ
      exact hu_eq _ (radial_mem_ball_unitCircle hr.1 hr.2 ζ)
    rw [heq_r]
    exact ((theorem11_16 p f).1 hr.1 hr.2).2
  have hM_le_Ico : M_enn ≤
      ⨆ r ∈ Set.Ico (0 : ℝ) 1,
        eLpNorm (unitRadialRestriction u r) p unitCircleMeasure :=
    iSup_le_iSup_of_subset Set.Ioo_subset_Ico_self
  have hf_eq_M : eLpNorm f p unitCircleMeasure = M_enn :=
    le_antisymm hf_enn_le (hM_le_Ico.trans hIco_le_f)
  have hf_eq_Ico : eLpNorm f p unitCircleMeasure =
      ⨆ r ∈ Set.Ico (0 : ℝ) 1,
        eLpNorm (unitRadialRestriction u r) p unitCircleMeasure :=
    le_antisymm (hf_eq_M ▸ hM_le_Ico) hIco_le_f
  refine ⟨⟨f, hu_eq, fun g hg => unitPoissonIntegral_lp_inj p fun z hz =>
      (hg z hz).symm.trans (hu_eq z hz)⟩,
    f, hu_eq, hf_eq_M, hf_eq_Ico, ?_, ?_⟩
  · rw [Lp.norm_def, hf_eq_M]
  · intro hp_top
    subst hp_top
    exact (rudinEssSup_lp_top_eq_norm unitCircleMeasure_univ_ne_zero f).2.2

/-- 11.30(c) (Herglotz Theorem, Rudin pp. 247–248):
Every positive (`≥ 0`, hence in particular every strictly positive `> 0`) real harmonic function `u`
in `U = ball 0 1` is the Poisson integral of a unique positive Borel measure `μ` on `T = UnitCircle`
(unique across *all* positive Borel measures `ν : Measure UnitCircle`, without assuming `ν(T) < ∞`
a priori). -/
theorem theorem11_30c {u : ℂ → ℝ} (hu : HarmonicOn u (Metric.ball (0 : ℂ) 1))
    (hpos : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 ≤ u z) :
    (∃! μ : Measure UnitCircle,
      ∀ z ∈ Metric.ball (0 : ℂ) 1,
        ENNReal.ofReal (u z) =
          ∫⁻ η : UnitCircle, ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) ∂μ) ∧
    ∃ μ : Measure UnitCircle, IsFiniteMeasure μ ∧
      μ Set.univ = ENNReal.ofReal (u 0) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, u z = positivePoissonIntegral μ z) ∧
      ∀ (ν : Measure UnitCircle) [IsFiniteMeasure ν],
        (∀ z ∈ Metric.ball (0 : ℂ) 1, u z = positivePoissonIntegral ν z) → ν = μ := by
  let uC : ℂ → ℂ := fun z => (u z : ℂ)
  have huC : HarmonicOn uC (Metric.ball (0 : ℂ) 1) :=
    hu.comp_clm Metric.isOpen_ball Complex.ofRealCLM
  have hu0_nn : 0 ≤ u 0 := hpos 0 (Metric.mem_ball_self zero_lt_one)
  -- Mean value property + `u ≥ 0` gives `‖u_{C, r}‖₁ = u(0)` for all `0 < r < 1` (Rudin 11.30(7))
  have hL1_eq : ∀ {r : ℝ}, 0 < r → r < 1 →
      eLpNorm (unitRadialRestriction uC r) 1 unitCircleMeasure = ENNReal.ofReal (u 0) := by
    intro r hr0 hr1
    have hur_cont : Continuous (unitRadialRestriction uC r) :=
      huC.continuousOn.comp_continuous (continuous_const.mul continuous_subtype_val)
        (fun ζ => radial_mem_ball_unitCircle hr0.le hr1 ζ)
    have hmvp := (theorem11_12_real Metric.isOpen_ball hu).1 hr0
      (Metric.closedBall_subset_ball hr1)
    have hint_u : (∫ ζ : UnitCircle, u ((r : ℂ) * (ζ : ℂ)) ∂unitCircleMeasure) = u 0 := by
      rw [(integral_unitCircleMeasure_eq_interval _).2, ← hmvp, Real.circleAverage_def]
      congr 1
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp [circleMap]
    have hur_norm_int : (∫ ζ : UnitCircle, ‖unitRadialRestriction uC r ζ‖ ∂unitCircleMeasure) =
        u 0 := by
      rw [← hint_u]
      refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
      dsimp only [unitRadialRestriction, uC]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hpos _ (radial_mem_ball_unitCircle hr0.le hr1 ζ))]
    have hur_int : Integrable (fun ζ : UnitCircle => ‖unitRadialRestriction uC r ζ‖)
        unitCircleMeasure :=
      hur_cont.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [eLpNorm_one_eq_lintegral_enorm hur_cont.aestronglyMeasurable,
      ← hur_norm_int, ofReal_integral_eq_lintegral_ofReal hur_int
        (ae_of_all _ fun _ => norm_nonneg _)]
    exact lintegral_congr fun ζ => (ofReal_norm _).symm
  have hsup_le : (⨆ r ∈ Set.Ioo (0 : ℝ) 1,
      eLpNorm (unitRadialRestriction uC r) 1 unitCircleMeasure) ≤ ENNReal.ofReal (u 0) :=
    iSup₂_le fun r hr => (hL1_eq hr.1 hr.2).le
  obtain ⟨_, c, hc_eq, hc_var_eq, _, _⟩ :=
    theorem11_30a huC (hsup_le.trans_lt ENNReal.ofReal_lt_top)
  have : IsFiniteMeasure c.variation := isFiniteMeasure_complexMeasure_variation c
  have hc_var_le : c.variation.real Set.univ ≤ u 0 := by
    rw [measureReal_def, hc_var_eq]
    exact ENNReal.toReal_le_of_le_ofReal hu0_nn hsup_le
  -- Evaluate `uC 0 = poissonMeasureIntegral c 0` to get `c Set.univ = u 0`
  have hc_univ : c Set.univ = (u 0 : ℂ) := by
    have h0 := hc_eq 0 (Metric.mem_ball_self zero_lt_one)
    have hker0 : (fun η : UnitCircle => (_root_.poissonKernel 0 0 (η : ℂ) : ℂ)) =
        (Set.univ : Set UnitCircle).indicator fun _ => (1 : ℂ) := by
      ext η
      simp [_root_.poissonKernel]
    unfold poissonMeasureIntegral RudinRCA.Chapter10.complexMeasureIntegral at h0
    rw [hker0, VectorMeasure.integral_indicator_const (1 : ℂ) MeasurableSet.univ] at h0
    have h1 : ((1 : ℂ) • c Set.univ : ℂ) = c Set.univ := one_smul ℂ _
    exact (h0.trans h1).symm
  -- Deduce `c E = c.variation.real E` for every measurable `E`, hence `c = c.variation.withDensityᵥ 1`
  have hc_set : ∀ E : Set UnitCircle, MeasurableSet E → c E = (c.variation.real E : ℂ) := by
    intro E hE
    have hunion : c E + c Eᶜ = (u 0 : ℂ) := by
      rw [← VectorMeasure.of_union disjoint_compl_right hE hE.compl, Set.union_compl_self, hc_univ]
    have hre_sum : (c E).re + (c Eᶜ).re = u 0 := by
      have := congrArg Complex.re hunion
      simpa using this
    have hnE : ‖c E‖ ≤ c.variation.real E := by
      have he := c.enorm_measure_le_variation E
      rw [← ofReal_norm] at he
      rw [measureReal_def]
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp he
    have hnEc : ‖c Eᶜ‖ ≤ c.variation.real Eᶜ := by
      have he := c.enorm_measure_le_variation Eᶜ
      rw [← ofReal_norm] at he
      rw [measureReal_def]
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp he
    have hvar_split : c.variation.real E + c.variation.real Eᶜ = c.variation.real Set.univ := by
      rw [← measureReal_union disjoint_compl_right hE.compl, Set.union_compl_self]
    have hre_le1 : (c E).re ≤ ‖c E‖ := Complex.re_le_norm (c E)
    have hre_le2 : (c Eᶜ).re ≤ ‖c Eᶜ‖ := Complex.re_le_norm (c Eᶜ)
    have hre_eq_norm : (c E).re = ‖c E‖ := by linarith
    have hnorm_eq_var : ‖c E‖ = c.variation.real E := by linarith
    have him_zero : (c E).im = 0 := by
      have hsq : (c E).re * (c E).re + (c E).im * (c E).im = ‖c E‖ * ‖c E‖ := by
        rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, sq]
      have him2 : (c E).im * (c E).im = 0 := by
        rw [hre_eq_norm] at hsq
        linarith
      exact mul_self_eq_zero.mp him2
    apply Complex.ext
    · simp [hre_eq_norm, hnorm_eq_var]
    · simp [him_zero]
  let μ : Measure UnitCircle := c.variation
  have hc_wd : c = μ.withDensityᵥ (fun _ : UnitCircle => (1 : ℂ)) := by
    ext E hE
    rw [hc_set E hE, withDensityᵥ_apply (integrable_const (1 : ℂ)) hE, setIntegral_const,
      Complex.real_smul, mul_one]
  have hu_posP : ∀ z ∈ Metric.ball (0 : ℂ) 1, u z = positivePoissonIntegral μ z := by
    intro z hz
    have h1 := hc_eq z hz
    rw [hc_wd, poissonMeasureIntegral_withDensityᵥ_one μ hz] at h1
    exact Complex.ofReal_injective h1
  have hu_lint : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal (u z) =
        ∫⁻ η : UnitCircle, ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) ∂μ := by
    intro z hz
    rw [hu_posP z hz]
    unfold positivePoissonIntegral
    have hint : Integrable (fun η : UnitCircle => _root_.poissonKernel 0 z (η : ℂ)) μ :=
      (continuous_poissonKernel_unitCircle hz).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    exact ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ (poissonKernel_unitCircle_nonneg hz))
  have hμ_univ : μ Set.univ = ENNReal.ofReal (u 0) := by
    have h0 := hu_lint 0 (Metric.mem_ball_self zero_lt_one)
    have hker0 : ∀ η : UnitCircle,
        ENNReal.ofReal (_root_.poissonKernel 0 0 (η : ℂ)) = 1 := fun η => by
      simp [_root_.poissonKernel]
    simp_rw [hker0] at h0
    simpa using h0.symm
  -- Uniqueness among finite measures with `u = positivePoissonIntegral ν`
  have huniq_fin : ∀ (ν : Measure UnitCircle) [IsFiniteMeasure ν],
      (∀ z ∈ Metric.ball (0 : ℂ) 1, u z = positivePoissonIntegral ν z) → ν = μ := by
    intro ν _ hν
    have hwd_eq : ν.withDensityᵥ (fun _ : UnitCircle => (1 : ℂ)) =
        μ.withDensityᵥ (fun _ : UnitCircle => (1 : ℂ)) := by
      apply poissonMeasureIntegral_inj
      intro z hz
      rw [poissonMeasureIntegral_withDensityᵥ_one ν hz,
        poissonMeasureIntegral_withDensityᵥ_one μ hz, ← hν z hz, ← hu_posP z hz]
    ext E hE
    have hev := congrArg (fun d : ComplexMeasure UnitCircle => (d E).re) hwd_eq
    simp only [withDensityᵥ_apply (integrable_const (1 : ℂ)) hE, setIntegral_const,
      Complex.real_smul, mul_one, Complex.ofReal_re] at hev
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν E),
      ← ENNReal.ofReal_toReal (measure_ne_top μ E)]
    exact congrArg ENNReal.ofReal hev
  -- Uniqueness among *all* positive Borel measures `ν` via `[0, ∞]` lintegral
  refine ⟨⟨μ, hu_lint, fun ν hν => ?_⟩, μ, inferInstance, hμ_univ, hu_posP, huniq_fin⟩
  have hν_univ : ν Set.univ = ENNReal.ofReal (u 0) := by
    have h0 := hν 0 (Metric.mem_ball_self zero_lt_one)
    have hker0 : ∀ η : UnitCircle,
        ENNReal.ofReal (_root_.poissonKernel 0 0 (η : ℂ)) = 1 := fun η => by
      simp [_root_.poissonKernel]
    simp_rw [hker0] at h0
    simpa using h0.symm
  have : IsFiniteMeasure ν := ⟨hν_univ ▸ ENNReal.ofReal_lt_top⟩
  refine huniq_fin ν fun z hz => ?_
  have h1 := hν z hz
  have hint_ν : Integrable (fun η : UnitCircle => _root_.poissonKernel 0 z (η : ℂ)) ν :=
    (continuous_poissonKernel_unitCircle hz).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h2 := ofReal_integral_eq_lintegral_ofReal hint_ν
    (ae_of_all _ (poissonKernel_unitCircle_nonneg hz))
  change ENNReal.ofReal (positivePoissonIntegral ν z) = _ at h2
  have heq_ofR : ENNReal.ofReal (u z) = ENNReal.ofReal (positivePoissonIntegral ν z) :=
    h1.trans h2.symm
  have hnn_P : 0 ≤ positivePoissonIntegral ν z :=
    integral_nonneg (poissonKernel_unitCircle_nonneg hz)
  have := congrArg ENNReal.toReal heq_ofR
  rwa [ENNReal.toReal_ofReal (hpos z hz), ENNReal.toReal_ofReal hnn_P] at this

/-- 11.30 (Master Theorem, Rudin pp. 247–248): bundles parts (a), (b), and (c). -/
theorem theorem11_30 :
    -- (a) p = 1
    (∀ {u : ℂ → ℂ}, HarmonicOn u (Metric.ball (0 : ℂ) 1) →
      (⨆ r ∈ Set.Ioo (0 : ℝ) 1,
        eLpNorm (unitRadialRestriction u r) 1 unitCircleMeasure) < ⊤ →
      ∃! μ : ComplexMeasure UnitCircle,
        ∀ z ∈ Metric.ball (0 : ℂ) 1, u z = poissonMeasureIntegral μ z) ∧
    -- (b) 1 < p ≤ ⊤
    (∀ {u : ℂ → ℂ} {p : ℝ≥0∞} [Fact (1 ≤ p)], 1 < p →
      HarmonicOn u (Metric.ball (0 : ℂ) 1) →
      (⨆ r ∈ Set.Ioo (0 : ℝ) 1,
        eLpNorm (unitRadialRestriction u r) p unitCircleMeasure) < ⊤ →
      ∃! f : Lp ℂ p unitCircleMeasure,
        ∀ z ∈ Metric.ball (0 : ℂ) 1, u z = unitPoissonIntegral f z) ∧
    -- (c) Positive harmonic functions in U
    (∀ {u : ℂ → ℝ}, HarmonicOn u (Metric.ball (0 : ℂ) 1) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, 0 ≤ u z) →
      ∃! μ : Measure UnitCircle,
        ∀ z ∈ Metric.ball (0 : ℂ) 1,
          ENNReal.ofReal (u z) =
            ∫⁻ η : UnitCircle, ENNReal.ofReal (_root_.poissonKernel 0 z (η : ℂ)) ∂μ) :=
  ⟨fun hu hsup => (theorem11_30a hu hsup).1,
   fun hp1 hu hsup => (theorem11_30b hu hp1 hsup).1,
   fun hu hpos => (theorem11_30c hu hpos).1⟩

end Node11_30

/-! ### Node 11.26: `L^p`-Boundedness Characterization of Poisson Integrals -/

section Node11_26

/-- 11.26 (Rudin p. 245):
For a harmonic function `u` in `U = ball 0 1`:
1. `{u_r : 0 ≤ r < 1}` is `L¹(T)`-bounded (equivalently `sup_{0 < r < 1} ‖u_r‖₁ < ∞`) if and only
   if `u = P[dμ]` for a complex Borel measure `μ` on `T`;
2. for `1 < p ≤ ⊤`, `{u_r : 0 ≤ r < 1}` is `L^p(T)`-bounded if and only if `u = P[f]` for some
   `f ∈ L^p(T)` (and at `p = ⊤`, boundedness in literal 3.7 `rudinEssSup` is equivalent as well);
3. in particular, `L¹(T)`-boundedness of `u_r` as `r → 1⁻` implies that `u` has nontangential
   limits `σ`-almost everywhere on `T`. -/
theorem theorem11_26 {u : ℂ → ℂ} (hu : HarmonicOn u (Metric.ball (0 : ℂ) 1)) :
    (((⨆ r ∈ Set.Ico (0 : ℝ) 1,
        eLpNorm (unitRadialRestriction u r) 1 unitCircleMeasure) < ⊤) ↔
      ∃ μ : ComplexMeasure UnitCircle,
        ∀ z ∈ Metric.ball (0 : ℂ) 1, u z = poissonMeasureIntegral μ z) ∧
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p →
      (((⨆ r ∈ Set.Ico (0 : ℝ) 1,
          eLpNorm (unitRadialRestriction u r) p unitCircleMeasure) < ⊤) ↔
        ∃ f : Lp ℂ p unitCircleMeasure,
          ∀ z ∈ Metric.ball (0 : ℂ) 1, u z = unitPoissonIntegral f z)) ∧
    ((∃ M : ℝ, ∀ r ∈ Set.Ico (0 : ℝ) 1,
        rudinEssSup unitCircleMeasure (unitRadialRestriction u r) ≤ M) ↔
      ∃ f : Lp ℂ ⊤ unitCircleMeasure,
        ∀ z ∈ Metric.ball (0 : ℂ) 1, u z = unitPoissonIntegral f z) ∧
    (((⨆ r ∈ Set.Ioo (0 : ℝ) 1,
        eLpNorm (unitRadialRestriction u r) 1 unitCircleMeasure) < ⊤) →
      ∃ f : UnitCircle → ℂ, Integrable f unitCircleMeasure ∧
        ∀ᵐ ζ ∂unitCircleMeasure, HasNontangentialLimit u ζ (f ζ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro hIco
      have hIoo : (⨆ r ∈ Set.Ioo (0 : ℝ) 1,
          eLpNorm (unitRadialRestriction u r) 1 unitCircleMeasure) < ⊤ :=
        (iSup_le_iSup_of_subset Set.Ioo_subset_Ico_self).trans_lt hIco
      exact (theorem11_30a hu hIoo).1.exists
    · rintro ⟨μ, hμ⟩
      have : IsFiniteMeasure μ.variation := isFiniteMeasure_complexMeasure_variation μ
      refine (iSup₂_le fun r hr => ?_).trans_lt (measure_lt_top μ.variation Set.univ)
      have heq_r : unitRadialRestriction u r =
          unitRadialRestriction (poissonMeasureIntegral μ) r :=
        funext fun ζ => hμ _ (radial_mem_ball_unitCircle hr.1 hr.2 ζ)
      rw [heq_r]
      exact ((theorem11_17 μ).2.2 hr.1 hr.2).2.2
  · intro p _ hp1
    constructor
    · intro hIco
      have hIoo : (⨆ r ∈ Set.Ioo (0 : ℝ) 1,
          eLpNorm (unitRadialRestriction u r) p unitCircleMeasure) < ⊤ :=
        (iSup_le_iSup_of_subset Set.Ioo_subset_Ico_self).trans_lt hIco
      exact (theorem11_30b hu hp1 hIoo).1.exists
    · rintro ⟨f, hf⟩
      refine (iSup₂_le fun r hr => ?_).trans_lt (Lp.memLp f).eLpNorm_lt_top
      have heq_r : unitRadialRestriction u r =
          unitRadialRestriction (unitPoissonIntegral f) r :=
        funext fun ζ => hf _ (radial_mem_ball_unitCircle hr.1 hr.2 ζ)
      rw [heq_r]
      exact ((theorem11_16 p f).1 hr.1 hr.2).2
  · constructor
    · rintro ⟨M, hM⟩
      have hIoo : (⨆ r ∈ Set.Ioo (0 : ℝ) 1,
          eLpNorm (unitRadialRestriction u r) ⊤ unitCircleMeasure) < ⊤ := by
        refine (iSup₂_le fun r hr => ?_).trans_lt (@ENNReal.ofReal_lt_top (max 0 M))
        have hc : Continuous (unitRadialRestriction u r) :=
          hu.continuousOn.comp_continuous (continuous_const.mul continuous_subtype_val)
            (fun ζ => radial_mem_ball_unitCircle hr.1.le hr.2 ζ)
        have hmem : MemLp (unitRadialRestriction u r) ⊤ unitCircleMeasure :=
          memLp_top_of_continuous_unitCircle hc
        rw [← ENNReal.ofReal_toReal hmem.eLpNorm_lt_top.ne,
          ← rudinEssSup_eq_eLpNorm_top_toReal unitCircleMeasure_univ_ne_zero hmem]
        exact ENNReal.ofReal_le_ofReal ((hM r ⟨hr.1.le, hr.2⟩).trans (le_max_right 0 M))
      exact (theorem11_30b hu ENNReal.one_lt_top hIoo).1.exists
    · rintro ⟨f, hf⟩
      refine ⟨rudinEssSup unitCircleMeasure f, fun r hr => ?_⟩
      have heq_r : unitRadialRestriction u r =
          unitRadialRestriction (unitPoissonIntegral f) r :=
        funext fun ζ => hf _ (radial_mem_ball_unitCircle hr.1 hr.2 ζ)
      rw [heq_r]
      exact (theorem11_16 ⊤ f).2.1 rfl hr.1 hr.2
  · intro hIoo
    obtain ⟨μ, hμ, _⟩ := (theorem11_30a hu hIoo).1
    have : μ.HaveLebesgueDecomposition unitCircleMeasure := ⟨inferInstance, inferInstance⟩
    refine ⟨μ.rnDeriv unitCircleMeasure, ComplexMeasure.integrable_rnDeriv μ unitCircleMeasure, ?_⟩
    filter_upwards [theorem11_24_rnDeriv μ] with ζ hlim
    exact hlim.congr_ball fun z hz => (hμ z hz).symm

end Node11_26

/-! ### Node 11.32: Boundary Values, Isometry, and Arc Uniqueness for `H^∞` -/

section Node11_32

private theorem ae_comp_unitCircleRotate (α : UnitCircle) {P : UnitCircle → Prop}
    (hP : ∀ᵐ η ∂unitCircleMeasure, P η) :
    ∀ᵐ ζ ∂unitCircleMeasure, P (unitCircleRotate α ζ) := by
  have hnull : unitCircleMeasure {η : UnitCircle | ¬ P η} = 0 := hP
  let N := toMeasurable unitCircleMeasure {η : UnitCircle | ¬ P η}
  have hN_meas : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN_zero : unitCircleMeasure N = 0 := by
    dsimp only [N]
    rw [measure_toMeasurable]
    exact hnull
  have hpre_zero : unitCircleMeasure (unitCircleRotate α ⁻¹' N) = 0 := by
    rw [← Measure.map_apply (unitCircleRotate α).continuous.measurable hN_meas,
      (measurePreserving_unitCircleRotate α).map_eq]
    exact hN_zero
  rw [ae_iff]
  refine measure_mono_null (fun ζ hζ => ?_) hpre_zero
  exact subset_toMeasurable _ _ hζ

private theorem exists_rotation_mem_openCircleArc (ζ₀ : UnitCircle) {δ : ℝ} {n : ℕ}
    (hn : 0 < n) (hδ : Real.pi / (n : ℝ) < δ) (ζ : UnitCircle) :
    ∃ k ∈ Finset.range n,
      unitCircleRotate
        ⟨Complex.exp (((2 * Real.pi * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) * Complex.I),
          exp_mem_unitCircle _⟩
        ζ ∈ openCircleArc ζ₀ δ := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  -- Choose `φ ∈ [0, 2π)` such that `ζ₀ = exp(i φ) * ζ`
  let w : ℂ := (ζ₀ : ℂ) * conj (ζ : ℂ)
  have hw_norm : ‖w‖ = 1 := by
    dsimp only [w]
    rw [norm_mul, RCLike.norm_conj, norm_unitCircle, norm_unitCircle, mul_one]
  let θ₀ : ℝ := Complex.arg w
  let φ : ℝ := if 0 ≤ θ₀ then θ₀ else θ₀ + 2 * Real.pi
  have hφ_nonneg : 0 ≤ φ := by
    dsimp only [φ]
    split_ifs with h
    · exact h
    · have := Complex.neg_pi_lt_arg w
      linarith [Real.pi_pos]
  have hφ_lt : φ < 2 * Real.pi := by
    dsimp only [φ]
    split_ifs with h
    · have := Complex.arg_le_pi w
      linarith [Real.pi_pos]
    · linarith
  have hexp_φ : Complex.exp ((φ : ℂ) * Complex.I) = w := by
    have hexp_θ₀ : Complex.exp ((θ₀ : ℂ) * Complex.I) = w := by
      have h := Complex.norm_mul_exp_arg_mul_I w
      rwa [hw_norm, Complex.ofReal_one, one_mul] at h
    dsimp only [φ]
    split_ifs with h
    · exact hexp_θ₀
    · push_cast
      rw [add_mul, Complex.exp_add, hexp_θ₀,
        show (2 : ℂ) * ↑Real.pi * Complex.I = 2 * Real.pi * Complex.I by ring,
        Complex.exp_two_pi_mul_I, mul_one]
  have hζ_eq : (ζ : ℂ) = (ζ₀ : ℂ) * Complex.exp (((-φ : ℝ) : ℂ) * Complex.I) := by
    calc (ζ : ℂ) = ((ζ₀ : ℂ) * conj (ζ : ℂ)) * (ζ : ℂ) * conj w := by
          dsimp only [w]
          calc (ζ : ℂ) = (ζ : ℂ) * ((ζ₀ : ℂ) * conj (ζ₀ : ℂ)) * ((ζ : ℂ) * conj (ζ : ℂ)) := by
                rw [unitCircle_mul_conj ζ₀, unitCircle_mul_conj ζ, mul_one, mul_one]
            _ = ((ζ₀ : ℂ) * conj (ζ : ℂ)) * (ζ : ℂ) * (conj (ζ₀ : ℂ) * (ζ : ℂ)) := by ring
            _ = ((ζ₀ : ℂ) * conj (ζ : ℂ)) * (ζ : ℂ) * conj ((ζ₀ : ℂ) * conj (ζ : ℂ)) := by
                simp [mul_comm]
      _ = (ζ₀ : ℂ) * conj w := by
          dsimp only [w]
          calc (ζ₀ : ℂ) * conj (ζ : ℂ) * (ζ : ℂ) * conj ((ζ₀ : ℂ) * conj (ζ : ℂ))
              = (ζ₀ : ℂ) * ((ζ : ℂ) * conj (ζ : ℂ)) * conj ((ζ₀ : ℂ) * conj (ζ : ℂ)) := by ring
            _ = (ζ₀ : ℂ) * conj ((ζ₀ : ℂ) * conj (ζ : ℂ)) := by
                rw [unitCircle_mul_conj ζ, mul_one]
      _ = (ζ₀ : ℂ) * Complex.exp (((-φ : ℝ) : ℂ) * Complex.I) := by
          rw [← hexp_φ, ← Complex.exp_conj]
          congr 2
          simp
  -- Partition `[0, n)` by `m = ⌊x⌋₊` where `x = φ * n / (2π)`
  let x : ℝ := φ * (n : ℝ) / (2 * Real.pi)
  have hx_nn : 0 ≤ x := by positivity
  have hx_lt_n : x < (n : ℝ) := by
    dsimp only [x]
    rw [div_lt_iff₀ h2pi_pos]
    nlinarith
  let m : ℕ := ⌊x⌋₊
  have hm_lt_n : m < n := (Nat.floor_lt hx_nn).mpr hx_lt_n
  have hm_le_x : (m : ℝ) ≤ x := Nat.floor_le hx_nn
  have hx_lt_m1 : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
  have hφ_x : φ = 2 * Real.pi * x / (n : ℝ) := by
    dsimp only [x]
    field_simp [hn_pos.ne', h2pi_pos.ne']
  by_cases hhalf : x - (m : ℝ) ≤ 1 / 2
  · refine ⟨m, Finset.mem_range.mpr hm_lt_n, ?_⟩
    refine ⟨2 * Real.pi * (m : ℝ) / (n : ℝ) - φ, ?_, ?_⟩
    · have hdiff : 2 * Real.pi * (m : ℝ) / (n : ℝ) - φ =
          -(2 * Real.pi / (n : ℝ) * (x - (m : ℝ))) := by
        rw [hφ_x]
        ring
      rw [hdiff, abs_neg, abs_of_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hm_le_x))]
      have hle : 2 * Real.pi / (n : ℝ) * (x - (m : ℝ)) ≤ Real.pi / (n : ℝ) := by
        calc 2 * Real.pi / (n : ℝ) * (x - (m : ℝ))
            ≤ 2 * Real.pi / (n : ℝ) * (1 / 2) :=
              mul_le_mul_of_nonneg_left hhalf (by positivity)
          _ = Real.pi / (n : ℝ) := by ring
      exact hle.trans_lt hδ
    · rw [unitCircleRotate_coe, hζ_eq]
      dsimp only
      calc Complex.exp (((2 * Real.pi * (m : ℝ) / (n : ℝ) : ℝ) : ℂ) * Complex.I) *
              ((ζ₀ : ℂ) * Complex.exp (((-φ : ℝ) : ℂ) * Complex.I))
          = (ζ₀ : ℂ) * (Complex.exp (((2 * Real.pi * (m : ℝ) / (n : ℝ) : ℝ) : ℂ) * Complex.I) *
              Complex.exp (((-φ : ℝ) : ℂ) * Complex.I)) := by ring
        _ = (ζ₀ : ℂ) * Complex.exp (((2 * Real.pi * (m : ℝ) / (n : ℝ) - φ : ℝ) : ℂ) * Complex.I) := by
            rw [← Complex.exp_add]
            congr 2
            push_cast
            ring
  · push Not at hhalf
    have hm1_lt_half : (m : ℝ) + 1 - x < 1 / 2 := by linarith
    by_cases hm1 : m + 1 < n
    · refine ⟨m + 1, Finset.mem_range.mpr hm1, ?_⟩
      refine ⟨2 * Real.pi * ((m + 1 : ℕ) : ℝ) / (n : ℝ) - φ, ?_, ?_⟩
      · have hdiff : 2 * Real.pi * ((m + 1 : ℕ) : ℝ) / (n : ℝ) - φ =
            2 * Real.pi / (n : ℝ) * ((m : ℝ) + 1 - x) := by
          rw [hφ_x]
          push_cast
          ring
        rw [hdiff, abs_of_nonneg (mul_nonneg (by positivity) (by linarith))]
        have hlt : 2 * Real.pi / (n : ℝ) * ((m : ℝ) + 1 - x) < Real.pi / (n : ℝ) := by
          calc 2 * Real.pi / (n : ℝ) * ((m : ℝ) + 1 - x)
              < 2 * Real.pi / (n : ℝ) * (1 / 2) :=
                mul_lt_mul_of_pos_left hm1_lt_half (by positivity)
            _ = Real.pi / (n : ℝ) := by ring
        exact hlt.trans hδ
      · rw [unitCircleRotate_coe, hζ_eq]
        dsimp only
        calc Complex.exp (((2 * Real.pi * ((m + 1 : ℕ) : ℝ) / (n : ℝ) : ℝ) : ℂ) * Complex.I) *
                ((ζ₀ : ℂ) * Complex.exp (((-φ : ℝ) : ℂ) * Complex.I))
            = (ζ₀ : ℂ) *
                (Complex.exp (((2 * Real.pi * ((m + 1 : ℕ) : ℝ) / (n : ℝ) : ℝ) : ℂ) * Complex.I) *
                Complex.exp (((-φ : ℝ) : ℂ) * Complex.I)) := by ring
          _ = (ζ₀ : ℂ) *
                Complex.exp (((2 * Real.pi * ((m + 1 : ℕ) : ℝ) / (n : ℝ) - φ : ℝ) : ℂ) * Complex.I) := by
              rw [← Complex.exp_add]
              congr 2
              push_cast
              ring
    · have hm_eq : m + 1 = n := by omega
      refine ⟨0, Finset.mem_range.mpr hn, ?_⟩
      refine ⟨2 * Real.pi - φ, ?_, ?_⟩
      · have hdiff : 2 * Real.pi - φ = 2 * Real.pi / (n : ℝ) * ((m : ℝ) + 1 - x) := by
          have hn_cast : (n : ℝ) = (m : ℝ) + 1 := by exact_mod_cast hm_eq.symm
          rw [hφ_x, ← hn_cast]
          field_simp [hn_pos.ne']
        rw [hdiff, abs_of_nonneg (mul_nonneg (by positivity) (by linarith))]
        have hlt : 2 * Real.pi / (n : ℝ) * ((m : ℝ) + 1 - x) < Real.pi / (n : ℝ) := by
          calc 2 * Real.pi / (n : ℝ) * ((m : ℝ) + 1 - x)
              < 2 * Real.pi / (n : ℝ) * (1 / 2) :=
                mul_lt_mul_of_pos_left hm1_lt_half (by positivity)
            _ = Real.pi / (n : ℝ) := by ring
        exact hlt.trans hδ
      · rw [unitCircleRotate_coe, hζ_eq]
        dsimp only
        simp only [Nat.cast_zero, mul_zero, zero_div, Complex.ofReal_zero, zero_mul,
          Complex.exp_zero, one_mul]
        congr 1
        have hsum : (((2 * Real.pi - φ : ℝ) : ℂ) * Complex.I) =
            2 * Real.pi * Complex.I + ((-φ : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [hsum, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]

private theorem not_countable_ball_unit : ¬ (Metric.ball (0 : ℂ) 1).Countable := by
  intro hcnt
  let ι : Set.Ioo (0 : ℝ) 1 → Metric.ball (0 : ℂ) 1 := fun r =>
    ⟨(r.1 : ℂ), by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos r.2.1]
      exact r.2.2⟩
  have hι_inj : Function.Injective ι := by
    intro a b hab
    ext
    exact Complex.ofReal_injective (congrArg Subtype.val hab)
  have hcard_le : Cardinal.mk (Set.Ioo (0 : ℝ) 1) ≤ Cardinal.aleph0 :=
    (Cardinal.mk_le_of_injective hι_inj).trans hcnt.le_aleph0
  rw [Cardinal.mk_Ioo_real zero_lt_one] at hcard_le
  exact not_lt_of_ge hcard_le Cardinal.aleph0_lt_continuum

/-- Boundary-value existence, Poisson representation, nontangential/radial convergence, and
isometric `L^∞` norm equality for `f ∈ H^∞` (first half of 11.32, Rudin p. 249). -/
theorem exists_unique_hInfty_boundary (f : HInfty) :
    ∃! f_star : Lp ℂ ⊤ unitCircleMeasure,
      (∀ z : Metric.ball (0 : ℂ) 1,
        (f : BoundedContinuousFunction (Metric.ball (0 : ℂ) 1) ℂ) z =
          unitPoissonIntegral f_star z.1) ∧
      (∀ᵐ (ζ : UnitCircle) ∂unitCircleMeasure,
        HasNontangentialLimit
          (extendZero (f : BoundedContinuousFunction (Metric.ball (0 : ℂ) 1) ℂ))
          ζ (f_star ζ)) ∧
      (∀ᵐ (ζ : UnitCircle) ∂unitCircleMeasure,
        Tendsto (fun r : ℝ =>
          extendZero (f : BoundedContinuousFunction (Metric.ball (0 : ℂ) 1) ℂ)
            ((r : ℂ) * (ζ : ℂ)))
          (𝓝[<] 1) (𝓝 (f_star ζ))) ∧
      ‖f‖ = ‖f_star‖ ∧
      ‖f‖ = rudinEssSup unitCircleMeasure f_star := by
  let f_bcf : BoundedContinuousFunction (Metric.ball (0 : ℂ) 1) ℂ := f.1
  let f_ext : ℂ → ℂ := extendZero f_bcf
  have hf_holo : DifferentiableOn ℂ f_ext (Metric.ball (0 : ℂ) 1) := f.2
  have hf_harm : HarmonicOn f_ext (Metric.ball (0 : ℂ) 1) :=
    harmonicOn_of_mathlib fun z hz =>
      (hf_holo.analyticAt (Metric.isOpen_ball.mem_nhds hz)).harmonicAt
  have hsup_le : (⨆ r ∈ Set.Ioo (0 : ℝ) 1,
      eLpNorm (unitRadialRestriction f_ext r) ⊤ unitCircleMeasure) ≤ ENNReal.ofReal ‖f‖ := by
    refine iSup₂_le fun r hr => ?_
    have hmem : MemLp (unitRadialRestriction f_ext r) ⊤ unitCircleMeasure := by
      refine memLp_top_of_bound
        (hf_harm.continuousOn.comp_continuous (continuous_const.mul continuous_subtype_val)
          (fun ζ => radial_mem_ball_unitCircle hr.1.le hr.2 ζ)).aestronglyMeasurable
        ‖f‖ (ae_of_all _ fun ζ => ?_)
      have hz := radial_mem_ball_unitCircle hr.1.le hr.2 ζ
      dsimp only [unitRadialRestriction, f_ext]
      rw [extendZero_apply_of_mem f_bcf hz]
      exact BoundedContinuousFunction.norm_coe_le_norm f_bcf ⟨_, hz⟩
    rw [eLpNorm_exponent_top hmem.aestronglyMeasurable]
    refine essSup_le_of_ae_le _ (ae_of_all _ fun ζ => ?_)
    have hz := radial_mem_ball_unitCircle hr.1.le hr.2 ζ
    dsimp only [unitRadialRestriction, f_ext]
    rw [extendZero_apply_of_mem f_bcf hz, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (BoundedContinuousFunction.norm_coe_le_norm f_bcf ⟨_, hz⟩)
  obtain ⟨huniq_P, f_star, hf_P, _, _, hf_star_norm_eq, hf_ess⟩ :=
    theorem11_30b hf_harm ENNReal.one_lt_top (hsup_le.trans_lt ENNReal.ofReal_lt_top)
  have hf_star_le_f : ‖f_star‖ ≤ ‖f‖ := by
    rw [hf_star_norm_eq]
    exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg f) hsup_le
  -- Opposite inequality `‖f‖ ≤ ‖f_star‖`
  have hf_le_f_star : ‖f‖ ≤ ‖f_star‖ := by
    change ‖f_bcf‖ ≤ ‖f_star‖
    refine (BoundedContinuousFunction.norm_le (norm_nonneg f_star)).mpr fun z => ?_
    have hz_P : f_bcf z = unitPoissonIntegral f_star z.1 := by
      have := hf_P z.1 z.2
      dsimp only [f_ext] at this
      rwa [extendZero_apply_of_mem f_bcf z.2] at this
    rw [hz_P]
    have hmem := Lp.memLp f_star
    have hen : ‖unitPoissonIntegral f_star z.1‖ₑ ≤ eLpNorm f_star ⊤ unitCircleMeasure := by
      calc ‖unitPoissonIntegral f_star z.1‖ₑ
          ≤ ∫⁻ η : UnitCircle,
              ENNReal.ofReal (_root_.poissonKernel 0 z.1 (η : ℂ)) * ‖f_star η‖ₑ
                ∂unitCircleMeasure := enorm_unitPoissonIntegral_le z.2
        _ ≤ ∫⁻ η : UnitCircle,
              ENNReal.ofReal (_root_.poissonKernel 0 z.1 (η : ℂ)) *
                eLpNorm f_star ⊤ unitCircleMeasure ∂unitCircleMeasure := by
            refine lintegral_mono_ae ?_
            have hae : ∀ᵐ η ∂unitCircleMeasure,
                ‖f_star η‖ₑ ≤ eLpNorm f_star ⊤ unitCircleMeasure := by
              rw [eLpNorm_exponent_top hmem.aestronglyMeasurable]
              exact ae_le_essSup
            filter_upwards [hae] with η hη
            gcongr
        _ = eLpNorm f_star ⊤ unitCircleMeasure := by
            rw [lintegral_mul_const _
              (continuous_poissonKernel_unitCircle z.2).measurable.ennreal_ofReal,
              lintegral_poissonKernel_unitCircle z.2, one_mul]
    rw [← toReal_enorm, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f_star) hen
  have hnorm_eq : ‖f‖ = ‖f_star‖ := le_antisymm hf_le_f_star hf_star_le_f
  have hess_eq : ‖f‖ = rudinEssSup unitCircleMeasure f_star :=
    hnorm_eq.trans (hf_ess rfl).symm
  -- Almost-everywhere nontangential and radial convergence (Fatou, 11.23)
  have hf_star_int : Integrable f_star unitCircleMeasure :=
    (Lp.memLp f_star).integrable le_top
  have hae_nt : ∀ᵐ (ζ : UnitCircle) ∂unitCircleMeasure, HasNontangentialLimit f_ext ζ (f_star ζ) := by
    filter_upwards [ae_hasNontangentialLimit_unitPoissonIntegral hf_star_int] with ζ hlim
    exact hlim.congr_ball fun z hz => (hf_P z hz).symm
  have hae_rad : ∀ᵐ (ζ : UnitCircle) ∂unitCircleMeasure,
      Tendsto (fun r : ℝ => f_ext ((r : ℂ) * (ζ : ℂ))) (𝓝[<] 1) (𝓝 (f_star ζ)) := by
    filter_upwards [hae_nt] with ζ hlim using hlim.tendsto_radial
  refine ⟨f_star, ⟨fun z => by
      have := hf_P z.1 z.2
      dsimp only [f_ext] at this
      rw [extendZero_apply_of_mem f_bcf z.2] at this
      exact this,
    hae_nt, hae_rad, hnorm_eq, hess_eq⟩, ?_⟩
  -- Uniqueness: even radial limit characterization (1) alone determines `f_star` in `Lp ℂ ⊤`
  intro g ⟨hg_P, _, _, _, _⟩
  refine huniq_P.unique (fun z hz => ?_) hf_P
  have := hg_P ⟨z, hz⟩
  dsimp only [f_ext]
  rw [extendZero_apply_of_mem f_bcf hz]
  exact this

/-- 11.32 (Theorem, Rudin p. 249):
1. To every `f ∈ H^∞` corresponds a unique `f* ∈ L^∞(T)` (`Lp ℂ ⊤ unitCircleMeasure`) defined
   `σ`-almost everywhere by `f*(ζ) = lim_{r → 1⁻} f(r ζ)` (and in fact nontangentially, with
   `f = P[f*]`), and the norm equality `‖f‖_∞ = ‖f*‖_∞` holds in both `Lp ℂ ⊤` norm and literal
   3.7 `rudinEssSup`;
2. Moreover, any measurable function `g : UnitCircle → ℂ` satisfying `g(ζ) = lim_{r → 1⁻} f(r ζ)`
   `σ`-almost everywhere agrees `σ`-a.e. with `f*`;
3. If `f*(ζ) = 0` for `σ`-almost every `ζ` on some nonempty open arc `I = openCircleArc ζ₀ δ ⊂ T`
   (`δ > 0`), then `f(z) = 0` for every `z ∈ U` (`f = 0`). -/
theorem theorem11_32 (f : HInfty) :
    ∃! f_star : Lp ℂ ⊤ unitCircleMeasure,
      (∀ z : Metric.ball (0 : ℂ) 1,
        (f : BoundedContinuousFunction (Metric.ball (0 : ℂ) 1) ℂ) z =
          unitPoissonIntegral f_star z.1) ∧
      (∀ᵐ (ζ : UnitCircle) ∂unitCircleMeasure,
        HasNontangentialLimit
          (extendZero (f : BoundedContinuousFunction (Metric.ball (0 : ℂ) 1) ℂ))
          ζ (f_star ζ)) ∧
      (∀ᵐ (ζ : UnitCircle) ∂unitCircleMeasure,
        Tendsto (fun r : ℝ =>
          extendZero (f : BoundedContinuousFunction (Metric.ball (0 : ℂ) 1) ℂ)
            ((r : ℂ) * (ζ : ℂ)))
          (𝓝[<] 1) (𝓝 (f_star ζ))) ∧
      ‖f‖ = ‖f_star‖ ∧
      ‖f‖ = rudinEssSup unitCircleMeasure f_star ∧
      (∀ g : UnitCircle → ℂ,
        (∀ᵐ (ζ : UnitCircle) ∂unitCircleMeasure,
          Tendsto (fun r : ℝ =>
            extendZero (f : BoundedContinuousFunction (Metric.ball (0 : ℂ) 1) ℂ)
              ((r : ℂ) * (ζ : ℂ)))
            (𝓝[<] 1) (𝓝 (g ζ))) →
        g =ᵐ[unitCircleMeasure] f_star) ∧
      (∀ (ζ₀ : UnitCircle) {δ : ℝ}, 0 < δ →
        (∀ᵐ (ζ : UnitCircle) ∂unitCircleMeasure.restrict (openCircleArc ζ₀ δ), f_star ζ = 0) →
        ∀ z : Metric.ball (0 : ℂ) 1,
          (f : BoundedContinuousFunction (Metric.ball (0 : ℂ) 1) ℂ) z = 0) := by
  obtain ⟨f_star, ⟨hf_P, hae_nt, hae_rad, hnorm_eq, hess_eq⟩, huniq⟩ :=
    exists_unique_hInfty_boundary f
  have hrad_uniq : ∀ g : UnitCircle → ℂ,
      (∀ᵐ (ζ : UnitCircle) ∂unitCircleMeasure,
        Tendsto (fun r : ℝ =>
          extendZero (f : BoundedContinuousFunction (Metric.ball (0 : ℂ) 1) ℂ)
            ((r : ℂ) * (ζ : ℂ)))
          (𝓝[<] 1) (𝓝 (g ζ))) →
      g =ᵐ[unitCircleMeasure] f_star := by
    intro g hg
    filter_upwards [hg, hae_rad] with ζ h1 h2 using tendsto_nhds_unique h1 h2
  have harc_zero : ∀ (ζ₀ : UnitCircle) {δ : ℝ}, 0 < δ →
      (∀ᵐ (ζ : UnitCircle) ∂unitCircleMeasure.restrict (openCircleArc ζ₀ δ), f_star ζ = 0) →
      ∀ z : Metric.ball (0 : ℂ) 1,
        (f : BoundedContinuousFunction (Metric.ball (0 : ℂ) 1) ℂ) z = 0 := by
    intro ζ₀ δ hδ harc
    let f_bcf : BoundedContinuousFunction (Metric.ball (0 : ℂ) 1) ℂ := f.1
    let f_ext : ℂ → ℂ := extendZero f_bcf
    -- Choose `n > 0` with `π / n < δ`
    obtain ⟨m, hm⟩ := exists_nat_gt (Real.pi / δ)
    let n : ℕ := m + 1
    have hn_pos : 0 < n := Nat.succ_pos m
    have hpi_n_lt : Real.pi / (n : ℝ) < δ := by
      have hm_lt : Real.pi / δ < (n : ℝ) := hm.trans (by exact_mod_cast Nat.lt_succ_self m)
      exact (div_lt_iff₀ (Nat.cast_pos.mpr hn_pos)).mpr
        ((div_lt_iff₀ hδ).mp hm_lt |>.trans_eq (mul_comm _ _))
    let α_rot : ℕ → UnitCircle := fun k =>
      ⟨Complex.exp (((2 * Real.pi * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) * Complex.I),
        exp_mem_unitCircle _⟩
    -- Define `G(z) = ∏_{k < n} f(α_k z)` and lift to `F ∈ H^∞` via 11.31
    let G : ℂ → ℂ := fun z => ∏ k ∈ Finset.range n, f_ext ((α_rot k : ℂ) * z)
    have hrot_ball : ∀ k : ℕ, ∀ {z : ℂ}, z ∈ Metric.ball (0 : ℂ) 1 →
        (α_rot k : ℂ) * z ∈ Metric.ball (0 : ℂ) 1 := by
      intro k z hz
      rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_unitCircle, one_mul]
      simpa [Metric.mem_ball] using hz
    have hG_holo : DifferentiableOn ℂ G (Metric.ball (0 : ℂ) 1) := by
      intro z hz
      have hterm : ∀ k ∈ Finset.range n,
          DifferentiableAt ℂ (fun w => f_ext ((α_rot k : ℂ) * w)) z := by
        intro k _
        have hdiff_at := f.2.differentiableAt (Metric.isOpen_ball.mem_nhds (hrot_ball k hz))
        exact hdiff_at.comp z ((differentiableAt_const (α_rot k : ℂ)).mul differentiableAt_id)
      exact (DifferentiableAt.fun_finsetProd hterm).differentiableWithinAt
    have hG_bdd : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖G z‖ ≤ ‖f_bcf‖ ^ n := by
      intro z hz
      dsimp only [G]
      rw [norm_prod]
      calc (∏ k ∈ Finset.range n, ‖f_ext ((α_rot k : ℂ) * z)‖)
          ≤ ∏ _k ∈ Finset.range n, ‖f_bcf‖ := by
            gcongr with k _
            have hkz := hrot_ball k hz
            dsimp only [f_ext]
            rw [extendZero_apply_of_mem f_bcf hkz]
            exact BoundedContinuousFunction.norm_coe_le_norm f_bcf ⟨_, hkz⟩
        _ = ‖f_bcf‖ ^ n := by rw [Finset.prod_const, Finset.card_range]
    obtain ⟨F, hF_eq, _⟩ := (theorem11_31 Metric.isOpen_ball).2.2 hG_holo hG_bdd
    obtain ⟨F_star, ⟨_, _, hF_rad, hF_norm, _⟩, _⟩ := exists_unique_hInfty_boundary F
    -- Show `F_star =ᵐ[unitCircleMeasure] 0`
    have harc_imp : ∀ᵐ η ∂unitCircleMeasure, η ∈ openCircleArc ζ₀ δ → f_star η = 0 :=
      (ae_restrict_iff' (isOpen_openCircleArc ζ₀ δ).measurableSet).mp harc
    have hrot_rad_all : ∀ᵐ ζ ∂unitCircleMeasure, ∀ k ∈ Finset.range n,
        Tendsto (fun r : ℝ => f_ext ((r : ℂ) * ((unitCircleRotate (α_rot k) ζ : UnitCircle) : ℂ)))
          (𝓝[<] 1) (𝓝 (f_star (unitCircleRotate (α_rot k) ζ))) := by
      simpa only [Finset.mem_coe] using
        (Finset.range n).finite_toSet.eventually_all.mpr fun k _ =>
          ae_comp_unitCircleRotate (α_rot k) hae_rad
    have hrot_zero_all : ∀ᵐ ζ ∂unitCircleMeasure, ∀ k ∈ Finset.range n,
        unitCircleRotate (α_rot k) ζ ∈ openCircleArc ζ₀ δ →
          f_star (unitCircleRotate (α_rot k) ζ) = 0 := by
      simpa only [Finset.mem_coe] using
        (Finset.range n).finite_toSet.eventually_all.mpr fun k _ =>
          ae_comp_unitCircleRotate (α_rot k) harc_imp
    have hF_star_zero : F_star =ᵐ[unitCircleMeasure] (0 : Lp ℂ ⊤ unitCircleMeasure) := by
      filter_upwards [hF_rad, hrot_rad_all, hrot_zero_all, Lp.coeFn_zero ℂ ⊤ unitCircleMeasure]
        with ζ hFl hrl hzl h0coe
      have hprod_lim : Tendsto
          (fun r : ℝ => extendZero (F : BoundedContinuousFunction (Metric.ball (0 : ℂ) 1) ℂ)
            ((r : ℂ) * (ζ : ℂ)))
          (𝓝[<] 1)
          (𝓝 (∏ k ∈ Finset.range n, f_star (unitCircleRotate (α_rot k) ζ))) := by
        have ht := tendsto_finsetProd (Finset.range n) fun k hk => hrl k hk
        refine ht.congr' ?_
        filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1)),
          self_mem_nhdsWithin] with r hr0 hr1
        have hz_r : (r : ℂ) * (ζ : ℂ) ∈ Metric.ball (0 : ℂ) 1 :=
          radial_mem_ball_unitCircle hr0.le hr1 ζ
        rw [extendZero_apply_of_mem _ hz_r, hF_eq ⟨_, hz_r⟩]
        dsimp only [G]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [unitCircleRotate_coe]
        congr 1
        ring
      obtain ⟨k₀, hk₀_mem, hk₀_arc⟩ := exists_rotation_mem_openCircleArc ζ₀ hn_pos hpi_n_lt ζ
      have hprod_eq_zero :
          (∏ k ∈ Finset.range n, f_star (unitCircleRotate (α_rot k) ζ)) = 0 :=
        Finset.prod_eq_zero hk₀_mem (hzl k₀ hk₀_mem hk₀_arc)
      rw [hprod_eq_zero] at hprod_lim
      rw [h0coe, Pi.zero_apply]
      exact tendsto_nhds_unique hFl hprod_lim
    have hF_star_eq : F_star = 0 := Lp.ext hF_star_zero
    have hF_norm_zero : ‖F‖ = 0 := by rw [hF_norm, hF_star_eq, norm_zero]
    have hG_zero : ∀ z ∈ Metric.ball (0 : ℂ) 1, G z = 0 := by
      intro z hz
      have hF0 : F = 0 := norm_eq_zero.mp hF_norm_zero
      have := hF_eq ⟨z, hz⟩
      rw [hF0] at this
      exact this.symm
    -- Deduce `f = 0` on `U` via Theorem 10.18 (`zeroSet_countable`) + uncountability of `U`
    intro z₀
    by_contra hne₀
    have hnot_eqOn : ¬ Set.EqOn f_ext 0 (Metric.ball (0 : ℂ) 1) := by
      intro heq
      have := heq z₀.2
      dsimp only [f_ext, Pi.zero_apply] at this
      rw [extendZero_apply_of_mem f_bcf z₀.2] at this
      exact hne₀ this
    have hZ_cnt : (RudinRCA.Chapter10.zeroSet f_ext (Metric.ball (0 : ℂ) 1)).Countable :=
      RudinRCA.Chapter10.zeroSet_countable
        (RudinRCA.Chapter10.disc_isRegion 0 zero_lt_one)
        ((RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn Metric.isOpen_ball).mpr f.2)
        hnot_eqOn
    let Z := RudinRCA.Chapter10.zeroSet f_ext (Metric.ball (0 : ℂ) 1)
    have hball_sub : Metric.ball (0 : ℂ) 1 ⊆
        ⋃ k ∈ Finset.range n, (fun w : ℂ => conj (α_rot k : ℂ) * w) '' Z := by
      intro z hz
      obtain ⟨k, hk_mem, hfk_zero⟩ := Finset.prod_eq_zero_iff.mp (hG_zero z hz)
      refine Set.mem_biUnion hk_mem ⟨(α_rot k : ℂ) * z, ⟨hrot_ball k hz, hfk_zero⟩, ?_⟩
      calc conj (α_rot k : ℂ) * ((α_rot k : ℂ) * z)
          = ((α_rot k : ℂ) * conj (α_rot k : ℂ)) * z := by ring
        _ = z := by rw [unitCircle_mul_conj (α_rot k), one_mul]
    have hball_cnt : (Metric.ball (0 : ℂ) 1).Countable :=
      ((Finset.range n).countable_toSet.biUnion fun k _ => hZ_cnt.image _).mono hball_sub
    exact not_countable_ball_unit hball_cnt
  refine ⟨f_star, ⟨hf_P, hae_nt, hae_rad, hnorm_eq, hess_eq, hrad_uniq, harc_zero⟩, ?_⟩
  intro g ⟨hg_P, hg_nt, hg_rad, hg_norm, hg_ess, _, _⟩
  exact huniq g ⟨hg_P, hg_nt, hg_rad, hg_norm, hg_ess⟩

end Node11_32

end RudinRCA.Chapter11

end
