import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Chapter 11: Harmonic Functions — fidelity checkpoint

This module proves nodes 11.1–11.4, retaining the weak harmonicity definition
based on actual pure second partial derivatives. It also records
the explicit kernel from 11.5(2) and the failure of
11.5(4) at the admitted endpoint `r = 0` (third edition, printed p. 233).
It does **not** claim completion of numbered node 11.5. The strict corrected
statement below explicitly assumes `0 < r`; that hypothesis is absent from
the printed assertion and is not silently inserted into a book theorem.
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

end RudinRCA.Chapter11
