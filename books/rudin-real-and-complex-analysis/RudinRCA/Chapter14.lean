import RudinRCA.Chapter10
import RudinRCA.Chapter11
import RudinRCA.Chapter12
import RudinRCA.Chapter13
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Chapter 14: Conformal Mapping

Formalization of Walter Rudin, *Real and Complex Analysis* (3rd ed., McGraw-Hill, 1987),
Chapter 14 (pp. 278–293, nodes `14.1`–`14.22`), following `SCOPING-F.md`.
-/

set_option autoImplicit false

noncomputable section

open Metric Set Filter Function Complex RudinRCA.Chapter13
open scoped Topology BigOperators OnePoint

namespace RudinRCA.Chapter14

/-! ### Nodes 14.1 and 14.2: Preservation of Angles -/

/-- **14.1 (Unit direction vector `A(z) = z / |z|`, RCA p. 278):**
For nonzero `z : ℂ`, `unitDir z = z / ‖z‖` is the unit vector in the direction of `z`. -/
def unitDir (z : ℂ) : ℂ :=
  z / (‖z‖ : ℂ)

theorem norm_unitDir {z : ℂ} (hz : z ≠ 0) : ‖unitDir z‖ = 1 := by
  unfold unitDir
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn, div_self hn.ne']

theorem unitDir_ne_zero {z : ℂ} (hz : z ≠ 0) : unitDir z ≠ 0 := by
  intro h0
  have := norm_unitDir hz
  rw [h0, norm_zero] at this
  exact zero_ne_one this

theorem unitDir_mul_pos {r : ℝ} (hr : 0 < r) (z : ℂ) :
    unitDir ((r : ℂ) * z) = unitDir z := by
  by_cases hz : z = 0
  · simp [unitDir, hz]
  · unfold unitDir
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Complex.ofReal_mul]
    have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hz_ne : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hz).ne'
    field_simp [hr_ne, hz_ne]

theorem unitDir_div_pos_exp (z : ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    unitDir (z / ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) =
      Complex.exp (-((θ : ℂ) * Complex.I)) * unitDir z := by
  unfold unitDir
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hexp_norm : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I θ
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    hexp_norm, mul_one, Complex.ofReal_div, Complex.exp_neg]
  by_cases hz : z = 0
  · simp [hz]
  · have hz_ne : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hz).ne'
    have hexp_ne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    field_simp [hr_ne, hz_ne, hexp_ne]

theorem continuousAt_unitDir {w : ℂ} (hw : w ≠ 0) : ContinuousAt unitDir w := by
  unfold unitDir
  exact continuousAt_id.div (Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt)
    (Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hw).ne')

/-- **Definition 14.1 (Preservation of oriented angles at `z₀`, RCA p. 278):**
Let `z₀ ∈ Ω` where some deleted open disc `ball z₀ δ \ {z₀}` lies in `Ω` and satisfies
`f(z) ≠ f(z₀)`. We say `f` *preserves angles at `z₀`* when
`lim_{r → 0+} e^{-iθ} A(f(z₀ + r e^{iθ}) - f(z₀))` exists and is independent of `θ ∈ ℝ`. -/
def PreservesAnglesAt (f : ℂ → ℂ) (Ω : Set ℂ) (z₀ : ℂ) : Prop :=
  z₀ ∈ Ω ∧
    (∃ δ > 0, ball z₀ δ ⊆ Ω ∧ ∀ z ∈ ball z₀ δ, z ≠ z₀ → f z ≠ f z₀) ∧
    ∃ c : ℂ, ∀ θ : ℝ,
      Tendsto
        (fun r : ℝ =>
          Complex.exp (-((θ : ℂ) * Complex.I)) *
            unitDir (f (z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - f z₀))
        (𝓝[>] 0) (𝓝 c)

theorem preservesAnglesAt_limit_norm_one {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ c : ℂ}
    (hdel : ∃ δ > 0, ball z₀ δ ⊆ Ω ∧ ∀ z ∈ ball z₀ δ, z ≠ z₀ → f z ≠ f z₀)
    (hlim : Tendsto
      (fun r : ℝ =>
        Complex.exp (-(((0 : ℝ) : ℂ) * Complex.I)) *
          unitDir (f (z₀ + (r : ℂ) * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) - f z₀))
      (𝓝[>] 0) (𝓝 c)) :
    ‖c‖ = 1 := by
  obtain ⟨δ, hδ, _, hne⟩ := hdel
  have hev : (fun r : ℝ =>
      ‖Complex.exp (-(((0 : ℝ) : ℂ) * Complex.I)) *
        unitDir (f (z₀ + (r : ℂ) * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) - f z₀)‖) =ᶠ[𝓝[>] 0]
      fun _ => (1 : ℝ) := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    have hr_pos : 0 < r := hr.1
    have hr_lt : r < δ := hr.2
    simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one, one_mul]
    have hz_ball : z₀ + (r : ℂ) ∈ ball z₀ δ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr_pos]
      exact hr_lt
    have hz_ne : z₀ + (r : ℂ) ≠ z₀ := by
      simp [Complex.ofReal_ne_zero.mpr hr_pos.ne']
    have hf_ne : f (z₀ + (r : ℂ)) - f z₀ ≠ 0 :=
      sub_ne_zero.mpr (hne _ hz_ball hz_ne)
    exact norm_unitDir hf_ne
  exact tendsto_nhds_unique hlim.norm (tendsto_const_nhds.congr' hev.symm)

/-- **Theorem 14.2 (Forward direction, RCA p. 278):**
If `Ω` is open, `z₀ ∈ Ω`, `HasDerivAt f w z₀`, and `w ≠ 0`, then `f` preserves angles at `z₀`
(with common directional limit `unitDir w = w / ‖w‖`). -/
theorem theorem14_2_of_hasDerivAt {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {z₀ w : ℂ} (hz₀ : z₀ ∈ Ω) (hd : HasDerivAt f w z₀) (hw : w ≠ 0) :
    PreservesAnglesAt f Ω z₀ ∧
      ∀ θ : ℝ, Tendsto
        (fun r : ℝ =>
          Complex.exp (-((θ : ℂ) * Complex.I)) *
            unitDir (f (z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - f z₀))
        (𝓝[>] 0) (𝓝 (unitDir w)) := by
  obtain ⟨δ₁, hδ₁, hball_Ω⟩ := Metric.isOpen_iff.mp hΩ z₀ hz₀
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hslope : Tendsto (fun z => (f z - f z₀) / (z - z₀)) (𝓝[≠] z₀) (𝓝 w) :=
    hd.tendsto_slope.congr fun z => by rw [slope_def_field]
  have hev_close : ∀ᶠ z in 𝓝[≠] z₀, ‖(f z - f z₀) / (z - z₀) - w‖ < ‖w‖ / 2 := by
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp hslope (‖w‖ / 2) (half_pos hw_pos)
  rw [eventually_nhdsWithin_iff] at hev_close
  obtain ⟨δ₂, hδ₂, hball_close⟩ := Metric.eventually_nhds_iff.mp hev_close
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hdel : ∀ z ∈ ball z₀ δ, z ≠ z₀ → f z ≠ f z₀ := by
    intro z hz hne heq
    have hlt : dist z z₀ < δ₂ := (mem_ball.mp hz).trans_le (min_le_right _ _)
    have hcl := hball_close hlt hne
    rw [heq, sub_self, zero_div, zero_sub, norm_neg] at hcl
    linarith
  have hdir : ∀ θ : ℝ, Tendsto
      (fun r : ℝ =>
        Complex.exp (-((θ : ℂ) * Complex.I)) *
          unitDir (f (z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - f z₀))
      (𝓝[>] 0) (𝓝 (unitDir w)) := by
    intro θ
    let ray : ℝ → ℂ := fun r => z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
    have hray_tendsto : Tendsto ray (𝓝[>] 0) (𝓝[≠] z₀) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hcont : Continuous ray :=
          continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
        have hray0 : ray 0 = z₀ := by simp [ray]
        exact hray0 ▸ (hcont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
        simp [ray, Complex.ofReal_ne_zero.mpr hr.ne', Complex.exp_ne_zero]
    have hq_lim : Tendsto (fun r : ℝ =>
        (f (ray r) - f z₀) / ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (𝓝[>] 0) (𝓝 w) := by
      refine (hslope.comp hray_tendsto).congr fun r => ?_
      dsimp [ray, Function.comp_def]
      rw [add_sub_cancel_left]
    have hu_lim : Tendsto (fun r : ℝ =>
        unitDir ((f (ray r) - f z₀) / ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))))
        (𝓝[>] 0) (𝓝 (unitDir w)) :=
      (continuousAt_unitDir hw).tendsto.comp hq_lim
    refine hu_lim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    exact unitDir_div_pos_exp (f (ray r) - f z₀) hr θ
  exact ⟨⟨hz₀, ⟨δ, hδ, (ball_subset_ball (min_le_left _ _)).trans hball_Ω, hdel⟩,
    ⟨unitDir w, hdir⟩⟩, hdir⟩

/-- **Theorem 14.2 (Converse direction, RCA pp. 278–279):**
Suppose `f` has a nonzero real Fréchet differential `L : ℂ →L[ℝ] ℂ` (`L ≠ 0`) at `z₀` and
preserves oriented angles at `z₀`. Then `f` is complex-differentiable at `z₀` and
`deriv f z₀ ≠ 0`. -/
theorem theorem14_2_of_hasFDerivAt_real {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ}
    {L : ℂ →L[ℝ] ℂ} (hL : HasFDerivAt f L z₀) (hL_ne : L ≠ 0)
    (hang : PreservesAnglesAt f Ω z₀) :
    DifferentiableAt ℂ f z₀ ∧ deriv f z₀ ≠ 0 := by
  have hf_real : DifferentiableAt ℝ f z₀ := hL.differentiableAt
  have hfderiv_eq : fderiv ℝ f z₀ = L := hL.fderiv
  let p : ℂ := RudinRCA.Chapter11.wirtinger f z₀
  let q : ℂ := RudinRCA.Chapter11.wirtingerBar f z₀
  have hpq_ne : ¬ (p = 0 ∧ q = 0) := by
    rintro ⟨hp0, hq0⟩
    apply hL_ne
    ext h
    rw [← hfderiv_eq, RudinRCA.Chapter11.node11_1_differential f z₀ h]
    change p * h + q * starRingEnd ℂ h = 0
    simp [hp0, hq0]
  obtain ⟨η, hη, hquot⟩ := RudinRCA.Chapter11.node11_1_quotient hf_real
  obtain ⟨_, hdel, c, hc_lim⟩ := hang
  have hc_norm : ‖c‖ = 1 := preservesAnglesAt_limit_norm_one hdel (hc_lim 0)
  have hc_ne : c ≠ 0 := fun h0 => by rw [h0, norm_zero] at hc_norm; exact zero_ne_one hc_norm
  -- Along ray `θ`, `(f(z₀ + r e^{iθ}) - f z₀) / (r e^{iθ}) → p + q * e^{-2iθ}`
  have hray_unit : ∀ θ : ℝ,
      let w := p + q * Complex.exp (((-2 * θ : ℝ) : ℂ) * Complex.I)
      w ≠ 0 → unitDir w = c := by
    intro θ w hw_ne
    let ray_h : ℝ → ℂ := fun r => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
    have hh_zero : Tendsto ray_h (𝓝[>] 0) (𝓝 0) := by
      have hcont : Continuous ray_h := Complex.continuous_ofReal.mul continuous_const
      have hray0 : ray_h 0 = 0 := by simp [ray_h]
      exact hray0 ▸ (hcont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    have hη_zero : Tendsto (fun r : ℝ => η (ray_h r)) (𝓝[>] 0) (𝓝 0) :=
      hη.comp hh_zero
    have hq_tendsto : Tendsto (fun r : ℝ => (f (z₀ + ray_h r) - f z₀) / ray_h r)
        (𝓝[>] 0) (𝓝 w) := by
      have hconst_add : Tendsto (fun r : ℝ => w + η (ray_h r)) (𝓝[>] 0) (𝓝 (w + 0)) :=
        tendsto_const_nhds.add hη_zero
      rw [add_zero] at hconst_add
      refine hconst_add.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
      have hexp_ne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
      have hh_ne : ray_h r ≠ 0 := mul_ne_zero hr_ne hexp_ne
      rw [hquot (ray_h r) hh_ne]
      dsimp only [w, ray_h]
      congr 1
      congr 1
      congr 1
      rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
        Complex.conj_I, mul_neg, mul_div_mul_left _ _ hr_ne, eq_div_iff hexp_ne, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hu_lim : Tendsto
        (fun r : ℝ =>
          Complex.exp (-((θ : ℂ) * Complex.I)) * unitDir (f (z₀ + ray_h r) - f z₀))
        (𝓝[>] 0) (𝓝 (unitDir w)) := by
      refine ((continuousAt_unitDir hw_ne).tendsto.comp hq_tendsto).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact unitDir_div_pos_exp (f (z₀ + ray_h r) - f z₀) hr θ
    exact tendsto_nhds_unique hu_lim (hc_lim θ)
  -- Helper: if `w ≠ 0` and `unitDir w = c`, then `(w / c).im = 0`
  have him_zero_of_nz : ∀ θ : ℝ,
      let w := p + q * Complex.exp (((-2 * θ : ℝ) : ℂ) * Complex.I)
      w ≠ 0 → (w / c).im = 0 := by
    intro θ w hw
    have hu := hray_unit θ hw
    unfold unitDir at hu
    have hn_ne : (‖w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hw).ne'
    have hw_eq : w = c * (‖w‖ : ℂ) := (div_eq_iff hn_ne).mp hu
    rw [hw_eq, mul_div_cancel_left₀ _ hc_ne, Complex.ofReal_im]
  -- Evaluate `exp((-2 * θ) * I)` at `θ = 0, π/2, -π/4, π/4` to obtain `1, -1, I, -I`
  have hexp0 : Complex.exp (((-2 * (0 : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by simp
  have hexp1 : Complex.exp (((-2 * (Real.pi / 2) : ℝ) : ℂ) * Complex.I) = -1 := by
    have h : ((-2 * (Real.pi / 2) : ℝ) : ℂ) * Complex.I = -(Real.pi * Complex.I) := by
      push_cast; ring
    rw [h, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
  have hexp2 : Complex.exp (((-2 * (-Real.pi / 4) : ℝ) : ℂ) * Complex.I) = Complex.I := by
    have h : ((-2 * (-Real.pi / 4) : ℝ) : ℂ) * Complex.I = Real.pi / 2 * Complex.I := by
      push_cast; ring
    rw [h, Complex.exp_pi_div_two_mul_I]
  have hexp3 : Complex.exp (((-2 * (Real.pi / 4) : ℝ) : ℂ) * Complex.I) = -Complex.I := by
    have h : ((-2 * (Real.pi / 4) : ℝ) : ℂ) * Complex.I = -(Real.pi / 2 * Complex.I) := by
      push_cast; ring
    rw [h, Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
  -- Deduce `q = 0` by contradiction: if `q ≠ 0`, `{p + q, p - q, p + I*q, p - I*q}` are pairwise distinct
  have hq0 : q = 0 := by
    by_contra hq_ne
    have h_at_most_one : ∀ {u₁ u₂ : ℂ}, u₁ ≠ u₂ → p + q * u₁ = 0 → p + q * u₂ ≠ 0 := by
      intro u₁ u₂ hne hu₁ hu₂
      apply hq_ne
      have hsub : q * (u₁ - u₂) = 0 := by linear_combination hu₁ - hu₂
      exact (mul_eq_zero.mp hsub).resolve_right (sub_ne_zero.mpr hne)
    have h1_ne_m1 : (1 : ℂ) ≠ -1 := by norm_num
    have hI_ne_mI : (Complex.I : ℂ) ≠ -Complex.I := by
      intro h; have := congrArg Complex.im h; norm_num at this
    have h1_ne_I : (1 : ℂ) ≠ Complex.I := by
      intro h; have := congrArg Complex.im h; simp at this
    have hm1_ne_I : (-1 : ℂ) ≠ Complex.I := by
      intro h; have := congrArg Complex.im h; simp at this
    by_cases hp1 : p + q * 1 = 0
    · have hm1 : p + q * (-1) ≠ 0 := h_at_most_one h1_ne_m1 hp1
      have hpI : p + q * Complex.I ≠ 0 := h_at_most_one h1_ne_I hp1
      have hmI : p + q * (-Complex.I) ≠ 0 :=
        h_at_most_one (by intro h; have := congrArg Complex.re h; simp at this) hp1
      have him1 : ((p - q) / c).im = 0 := by
        have h := him_zero_of_nz (Real.pi / 2)
        rw [hexp1] at h
        simpa [sub_eq_add_neg] using h hm1
      have him2 : ((p + Complex.I * q) / c).im = 0 := by
        have h := him_zero_of_nz (-Real.pi / 4)
        rw [hexp2] at h
        simpa [mul_comm] using h hpI
      have him3 : ((p - Complex.I * q) / c).im = 0 := by
        have h := him_zero_of_nz (Real.pi / 4)
        rw [hexp3] at h
        simpa [sub_eq_add_neg, mul_comm] using h hmI
      have hpc : (p / c).im = 0 := by
        have hsum : (p / c) = ((p + Complex.I * q) / c + (p - Complex.I * q) / c) / 2 := by
          field_simp [hc_ne]; ring
        rw [hsum]; simp [him2, him3]
      have hqc_re : (q / c).re = 0 := by
        have hdiff : Complex.I * (q / c) =
            ((p + Complex.I * q) / c - (p - Complex.I * q) / c) / 2 := by
          field_simp [hc_ne]; ring
        have him_diff : (Complex.I * (q / c)).im = 0 := by
          rw [hdiff]; simp [him2, him3]
        simpa [Complex.mul_im] using him_diff
      have hqc_im : (q / c).im = 0 := by
        have hsub : q / c = p / c - (p - q) / c := by field_simp [hc_ne]; ring
        rw [hsub, Complex.sub_im, hpc, him1, sub_self]
      have hqc0 : q / c = 0 := Complex.ext hqc_re hqc_im
      exact hq_ne ((div_eq_zero_iff.mp hqc0).resolve_right hc_ne)
    · by_cases hm1 : p + q * (-1) = 0
      · have hpI : p + q * Complex.I ≠ 0 := h_at_most_one hm1_ne_I hm1
        have hmI : p + q * (-Complex.I) ≠ 0 :=
          h_at_most_one (by intro h; have := congrArg Complex.re h; simp at this) hm1
        have him0 : ((p + q) / c).im = 0 := by
          have h := him_zero_of_nz 0
          rw [hexp0] at h
          simpa using h hp1
        have him2 : ((p + Complex.I * q) / c).im = 0 := by
          have h := him_zero_of_nz (-Real.pi / 4)
          rw [hexp2] at h
          simpa [mul_comm] using h hpI
        have him3 : ((p - Complex.I * q) / c).im = 0 := by
          have h := him_zero_of_nz (Real.pi / 4)
          rw [hexp3] at h
          simpa [sub_eq_add_neg, mul_comm] using h hmI
        have hpc : (p / c).im = 0 := by
          have hsum : (p / c) = ((p + Complex.I * q) / c + (p - Complex.I * q) / c) / 2 := by
            field_simp [hc_ne]; ring
          rw [hsum]; simp [him2, him3]
        have hqc_re : (q / c).re = 0 := by
          have hdiff : Complex.I * (q / c) =
              ((p + Complex.I * q) / c - (p - Complex.I * q) / c) / 2 := by
            field_simp [hc_ne]; ring
          have him_diff : (Complex.I * (q / c)).im = 0 := by
            rw [hdiff]; simp [him2, him3]
          simpa [Complex.mul_im] using him_diff
        have hqc_im : (q / c).im = 0 := by
          have hsub : q / c = (p + q) / c - p / c := by field_simp [hc_ne]; ring
          rw [hsub, Complex.sub_im, him0, hpc, sub_self]
        have hqc0 : q / c = 0 := Complex.ext hqc_re hqc_im
        exact hq_ne ((div_eq_zero_iff.mp hqc0).resolve_right hc_ne)
      · -- Both `p + q ≠ 0` and `p - q ≠ 0`, and at least one of `p ± I * q` is nonzero
        have him0 : ((p + q) / c).im = 0 := by
          have h := him_zero_of_nz 0
          rw [hexp0] at h
          simpa using h hp1
        have him1 : ((p - q) / c).im = 0 := by
          have h := him_zero_of_nz (Real.pi / 2)
          rw [hexp1] at h
          simpa [sub_eq_add_neg] using h hm1
        have hpc : (p / c).im = 0 := by
          have hsum : p / c = ((p + q) / c + (p - q) / c) / 2 := by field_simp [hc_ne]; ring
          rw [hsum]; simp [him0, him1]
        have hqc_im : (q / c).im = 0 := by
          have hdiff : q / c = ((p + q) / c - (p - q) / c) / 2 := by field_simp [hc_ne]; ring
          rw [hdiff]; simp [him0, him1]
        by_cases hpI : p + q * Complex.I = 0
        · have hmI : p + q * (-Complex.I) ≠ 0 := h_at_most_one hI_ne_mI hpI
          have him3 : ((p - Complex.I * q) / c).im = 0 := by
            have h := him_zero_of_nz (Real.pi / 4)
            rw [hexp3] at h
            simpa [sub_eq_add_neg, mul_comm] using h hmI
          have hqc_re : (q / c).re = 0 := by
            have hrel : (p - Complex.I * q) / c = p / c - Complex.I * (q / c) := by
              field_simp [hc_ne]
            rw [hrel, Complex.sub_im, hpc, Complex.mul_im, Complex.I_re, Complex.I_im,
              zero_mul, one_mul, zero_add, zero_sub, neg_eq_zero] at him3
            exact him3
          have hqc0 : q / c = 0 := Complex.ext hqc_re hqc_im
          exact hq_ne ((div_eq_zero_iff.mp hqc0).resolve_right hc_ne)
        · have him2 : ((p + Complex.I * q) / c).im = 0 := by
            have h := him_zero_of_nz (-Real.pi / 4)
            rw [hexp2] at h
            simpa [mul_comm] using h hpI
          have hqc_re : (q / c).re = 0 := by
            have hrel : (p + Complex.I * q) / c = p / c + Complex.I * (q / c) := by
              field_simp [hc_ne]
            rw [hrel, Complex.add_im, hpc, zero_add, Complex.mul_im, Complex.I_re,
              Complex.I_im, zero_mul, one_mul, zero_add] at him2
            exact him2
          have hqc0 : q / c = 0 := Complex.ext hqc_re hqc_im
          exact hq_ne ((div_eq_zero_iff.mp hqc0).resolve_right hc_ne)
  have hdiff_c : DifferentiableAt ℂ f z₀ :=
    (RudinRCA.Chapter11.node11_1_complex_differentiable_iff hf_real).mpr hq0
  have hp_ne : p ≠ 0 := fun hp0 => hpq_ne ⟨hp0, hq0⟩
  have hderiv_eq_p : deriv f z₀ = p := by
    have hd_real : HasFDerivAt f (ContinuousLinearMap.smulRight (1 : ℂ →L[ℝ] ℂ) (deriv f z₀)) z₀ :=
      hdiff_c.hasDerivAt.hasFDerivAt.restrictScalars ℝ
    have hf1 : fderiv ℝ f z₀ 1 = deriv f z₀ := by
      rw [hd_real.fderiv]; simp
    have hfI : fderiv ℝ f z₀ Complex.I = Complex.I * deriv f z₀ := by
      rw [hd_real.fderiv]; simp
    change deriv f z₀ = RudinRCA.Chapter11.wirtinger f z₀
    unfold RudinRCA.Chapter11.wirtinger
    rw [hf1, hfI]
    have : Complex.I * (Complex.I * deriv f z₀) = -deriv f z₀ := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    rw [this]
    ring
  exact ⟨hdiff_c, hderiv_eq_p ▸ hp_ne⟩

/-- **14.2 (Holomorphic zero-derivative exclusion, RCA p. 279):**
If `f` is holomorphic on an open set `Ω`, `z₀ ∈ Ω`, and `deriv f z₀ = 0`, then `f` cannot
preserve angles at `z₀`. -/
theorem theorem14_2_not_preservesAnglesAt_of_deriv_zero {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : RudinRCA.Chapter10.HolomorphicOn f Ω)
    {z₀ : ℂ} (_hz₀ : z₀ ∈ Ω) (hd0 : deriv f z₀ = 0) :
    ¬ PreservesAnglesAt f Ω z₀ := by
  rintro ⟨_, ⟨δ, hδ, hball_Ω, hdel⟩, c, hc_lim⟩
  have hc_norm : ‖c‖ = 1 :=
    preservesAnglesAt_limit_norm_one ⟨δ, hδ, hball_Ω, hdel⟩ (hc_lim 0)
  let D : Set ℂ := ball z₀ δ
  have hD_reg : RudinRCA.Chapter10.IsRegion D := RudinRCA.Chapter10.disc_isRegion z₀ hδ
  let g : ℂ → ℂ := fun z => f z - f z₀
  have hg_holo : RudinRCA.Chapter10.HolomorphicOn g D :=
    fun z hz => (hf z (hball_Ω hz)).sub (differentiableAt_const (f z₀))
  have hne_zero_D : ¬ Set.EqOn g 0 D := by
    intro hall
    let z₁ : ℂ := z₀ + ((δ / 2 : ℝ) : ℂ)
    have hz₁_D : z₁ ∈ D := by
      rw [mem_ball, dist_eq_norm]
      have : z₁ - z₀ = ((δ / 2 : ℝ) : ℂ) := by dsimp [z₁]; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hδ)]
      exact half_lt_self hδ
    have hz₁_ne : z₁ ≠ z₀ := by
      intro h
      have : ((δ / 2 : ℝ) : ℂ) = 0 := by dsimp [z₁] at h; linear_combination h
      exact Complex.ofReal_ne_zero.mpr (half_pos hδ).ne' this
    exact hdel z₁ hz₁_D hz₁_ne (sub_eq_zero.mp (hall hz₁_D))
  have hz₀_D : z₀ ∈ D := Metric.mem_ball_self hδ
  obtain ⟨hm_pos, h, hh_holo, hhz₀_ne, hfact⟩ :=
    RudinRCA.Chapter10.zeroOrder_spec hD_reg hg_holo hne_zero_D hz₀_D (sub_self (f z₀))
  let m : ℕ := RudinRCA.Chapter10.zeroOrder g D z₀
  have hm_ge2 : 2 ≤ m := by
    by_contra hlt2
    have hm1 : m = 1 := by omega
    have hev : f =ᶠ[𝓝 z₀] fun z => f z₀ + (z - z₀) * h z := by
      filter_upwards [Metric.ball_mem_nhds z₀ hδ] with z hz
      have hf_eq := hfact z hz
      change f z - f z₀ = (z - z₀) ^ m * h z at hf_eq
      rw [hm1, pow_one] at hf_eq
      linear_combination hf_eq
    have hd_rhs : HasDerivAt (fun z => f z₀ + (z - z₀) * h z) (h z₀) z₀ := by
      have hd_prod := ((hasDerivAt_id z₀).sub_const z₀).mul (hh_holo z₀ hz₀_D).hasDerivAt
      simpa using hd_prod.const_add (f z₀)
    have hdf : deriv f z₀ = h z₀ := (hd_rhs.congr_of_eventuallyEq hev).deriv
    exact hhz₀_ne (hdf.symm.trans hd0)
  -- Directional limit at angle `θ` equals `exp(((m - 1) * θ) * I) * unitDir (h z₀)`
  have hray_lim : ∀ θ : ℝ,
      Tendsto
        (fun r : ℝ =>
          Complex.exp (-((θ : ℂ) * Complex.I)) *
            unitDir (f (z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - f z₀))
        (𝓝[>] 0)
        (𝓝 (Complex.exp ((((m - 1 : ℕ) : ℝ) * θ : ℂ) * Complex.I) * unitDir (h z₀))) := by
    intro θ
    let ray : ℝ → ℂ := fun r => z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
    have hray_cont : Tendsto ray (𝓝[>] 0) (𝓝 z₀) := by
      have hc1 : Continuous ray :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      have hray0 : ray 0 = z₀ := by simp [ray]
      exact hray0 ▸ (hc1.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    have hh_lim : Tendsto (fun r : ℝ => unitDir (h (ray r))) (𝓝[>] 0) (𝓝 (unitDir (h z₀))) :=
      (continuousAt_unitDir hhz₀_ne).tendsto.comp
        ((hh_holo z₀ hz₀_D).continuousAt.tendsto.comp hray_cont)
    refine (hh_lim.const_mul _).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    have hr_pos : 0 < r := hr.1
    have hr_lt : r < δ := hr.2
    have hray_D : ray r ∈ D := by
      rw [mem_ball, dist_eq_norm]
      have : ray r - z₀ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by dsimp [ray]; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr_pos,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hr_lt
    have hfg := hfact (ray r) hray_D
    change f (ray r) - f z₀ = (ray r - z₀) ^ m * h (ray r) at hfg
    have hsub : ray r - z₀ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      dsimp [ray]; ring
    rw [hfg, hsub, mul_pow, ← Complex.ofReal_pow, mul_assoc ((r ^ m : ℝ) : ℂ),
      unitDir_mul_pos (pow_pos hr_pos m), ← Complex.exp_nat_mul]
    unfold unitDir
    have hexp_norm : ‖Complex.exp ((m : ℂ) * ((θ : ℂ) * Complex.I))‖ = 1 := by
      have : (m : ℂ) * ((θ : ℂ) * Complex.I) = (((m : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, hexp_norm, one_mul, mul_div_assoc, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    push_cast
    ring
  have hc0 : c = unitDir (h z₀) := by
    have h0 := hray_lim 0
    have hlim0 :
        Complex.exp ((((m - 1 : ℕ) : ℝ) * (0 : ℝ) : ℂ) * Complex.I) * unitDir (h z₀) =
          unitDir (h z₀) := by simp
    rw [hlim0] at h0
    exact tendsto_nhds_unique (hc_lim 0) h0
  let θ₁ : ℝ := Real.pi / ((m - 1 : ℕ) : ℝ)
  have hm1_pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - 1 by omega)
  have hc1 : c = -unitDir (h z₀) := by
    have h1 := hray_lim θ₁
    have hlim1 :
        Complex.exp ((((m - 1 : ℕ) : ℝ) * θ₁ : ℂ) * Complex.I) * unitDir (h z₀) =
          -unitDir (h z₀) := by
      have hmul : (((m - 1 : ℕ) : ℝ) : ℂ) * (θ₁ : ℂ) * Complex.I = Real.pi * Complex.I := by
        dsimp [θ₁]
        have hm1_ne : ((m - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast
        field_simp [hm1_ne]
      rw [hmul, Complex.exp_pi_mul_I, neg_one_mul]
    rw [hlim1] at h1
    exact tendsto_nhds_unique (hc_lim θ₁) h1
  have h2c : c = -c := hc1.trans (congrArg Neg.neg hc0.symm)
  have hc_zero : c = 0 := by linear_combination (1 / 2 : ℂ) * h2c
  rw [hc_zero, norm_zero] at hc_norm
  exact zero_ne_one hc_norm

/-- **14.2 (Counterexample `f(z) = |z| z` at `0`, RCA p. 279):**
The map `f(z) = ‖z‖ * z` preserves oriented angles at `0`, yet has zero real Fréchet differential
`HasFDerivAt f 0 0` (and is not holomorphic on any disc around `0`). -/
theorem node14_2_norm_mul_self_example :
    let f : ℂ → ℂ := fun z => (‖z‖ : ℂ) * z
    PreservesAnglesAt f Set.univ 0 ∧
      HasFDerivAt f (0 : ℂ →L[ℝ] ℂ) 0 ∧
      ∀ δ > 0, ¬ RudinRCA.Chapter10.HolomorphicOn f (ball 0 δ) := by
  intro f
  have hang : PreservesAnglesAt f Set.univ 0 := by
    refine ⟨Set.mem_univ 0, ⟨1, zero_lt_one, subset_univ _, ?_⟩, 1, ?_⟩
    · intro z _ hz_ne
      dsimp [f]
      rw [norm_zero, Complex.ofReal_zero, zero_mul]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hz_ne).ne') hz_ne
    · intro θ
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      dsimp [f]
      rw [zero_add, norm_zero, Complex.ofReal_zero, zero_mul, sub_zero, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
        Complex.norm_exp_ofReal_mul_I, mul_one, ← mul_assoc, ← Complex.ofReal_mul,
        unitDir_mul_pos (mul_pos hr hr)]
      unfold unitDir
      rw [Complex.norm_exp_ofReal_mul_I, Complex.ofReal_one, div_one, ← Complex.exp_add,
        neg_add_cancel, Complex.exp_zero]
  have hfderiv : HasFDerivAt f (0 : ℂ →L[ℝ] ℂ) 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.isLittleO_iff.mpr fun ε hε => ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with h hh
    have hh_lt : ‖h‖ < ε := by simpa [mem_ball_zero_iff] using hh
    simp only [f, zero_add, norm_zero, Complex.ofReal_zero, zero_mul, sub_zero,
      ContinuousLinearMap.zero_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_norm]
    nlinarith [norm_nonneg h]
  refine ⟨hang, hfderiv, ?_⟩
  intro δ hδ hholo
  have hdf0 : HasDerivAt f 0 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.isLittleO_iff.mpr fun ε hε => ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with h hh
    have hh_lt : ‖h‖ < ε := by simpa [mem_ball_zero_iff] using hh
    simp only [f, zero_add, norm_zero, Complex.ofReal_zero, zero_mul, sub_zero,
      smul_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    nlinarith [norm_nonneg h]
  have hdel_δ : ∀ z ∈ ball (0 : ℂ) δ, z ≠ 0 → f z ≠ f 0 := by
    intro z _ hne
    dsimp [f]
    rw [norm_zero, Complex.ofReal_zero, zero_mul]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hne).ne') hne
  exact theorem14_2_not_preservesAnglesAt_of_deriv_zero isOpen_ball hholo
    (Metric.mem_ball_self hδ) hdf0.deriv
    ⟨Metric.mem_ball_self hδ, ⟨δ, hδ, Subset.rfl, hdel_δ⟩, hang.2.2⟩

/-- **Theorem 14.2 (Combined local angle-preservation theorem, RCA pp. 278–279):**
Packages both directions of Theorem 14.2 together with the holomorphic zero-derivative exclusion
and the `f(z) = |z| z` example. -/
theorem theorem14_2 :
    (∀ {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ w : ℂ},
      IsOpen Ω → z₀ ∈ Ω → HasDerivAt f w z₀ → w ≠ 0 → PreservesAnglesAt f Ω z₀) ∧
    (∀ {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ} {L : ℂ →L[ℝ] ℂ},
      HasFDerivAt f L z₀ → L ≠ 0 → PreservesAnglesAt f Ω z₀ →
        DifferentiableAt ℂ f z₀ ∧ deriv f z₀ ≠ 0) ∧
    (∀ {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ},
      IsOpen Ω → RudinRCA.Chapter10.HolomorphicOn f Ω → z₀ ∈ Ω → deriv f z₀ = 0 →
        ¬ PreservesAnglesAt f Ω z₀) ∧
    (PreservesAnglesAt (fun z : ℂ => (‖z‖ : ℂ) * z) Set.univ 0 ∧
      HasFDerivAt (fun z : ℂ => (‖z‖ : ℂ) * z) (0 : ℂ →L[ℝ] ℂ) 0) :=
  ⟨fun hΩ hz₀ hd hw => (theorem14_2_of_hasDerivAt hΩ hz₀ hd hw).1,
    fun hL hL_ne hang => theorem14_2_of_hasFDerivAt_real hL hL_ne hang,
    fun hΩ hf hz₀ hd0 => theorem14_2_not_preservesAnglesAt_of_deriv_zero hΩ hf hz₀ hd0,
    ⟨node14_2_norm_mul_self_example.1, node14_2_norm_mul_self_example.2.1⟩⟩

/-- **14.1 (Global holomorphic characterization of angle preservation, RCA p. 278):**
For a holomorphic function `f ∈ H(Ω)` on an open set (in particular any region) `Ω`, `f` preserves
oriented angles at every point of `Ω` if and only if `deriv f z ≠ 0` for every `z ∈ Ω`. -/
theorem theorem14_1 {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ}
    (hf : RudinRCA.Chapter10.HolomorphicOn f Ω) :
    (∀ z ∈ Ω, PreservesAnglesAt f Ω z) ↔ ∀ z ∈ Ω, deriv f z ≠ 0 := by
  constructor
  · intro hang z hz hd0
    exact theorem14_2_not_preservesAnglesAt_of_deriv_zero hΩ hf hz hd0 (hang z hz)
  · intro hnz z hz
    exact (theorem14_2_of_hasDerivAt hΩ hz (hf z hz).hasDerivAt (hnz z hz)).1

/-! ### Node 14.3: Linear Fractional Transformations (Möbius Maps) -/

open Classical in
/-- **14.3 (Linear fractional / Möbius transformation on the Riemann sphere, RCA p. 279):**
For `a, b, c, d : ℂ` (with `a * d - b * c ≠ 0`), `moebiusMap a b c d` acts on `S² = OnePoint ℂ`
by `z ↦ (a * z + b) / (c * z + d)`, mapping `-d / c ↦ ∞` (when `c ≠ 0`) and `∞ ↦ a / c`
(`∞ ↦ ∞` when `c = 0`). -/
def moebiusMap (a b c d : ℂ) (p : RiemannSphere) : RiemannSphere :=
  OnePoint.rec
    (if c = 0 then ∞ else ((a / c : ℂ) : RiemannSphere))
    (fun z : ℂ => if c * z + d = 0 then ∞ else (((a * z + b) / (c * z + d) : ℂ) : RiemannSphere))
    p

@[simp] theorem moebiusMap_infty (a b c d : ℂ) :
    moebiusMap a b c d ∞ = if c = 0 then ∞ else ((a / c : ℂ) : RiemannSphere) := rfl

@[simp] theorem moebiusMap_coe (a b c d z : ℂ) :
    moebiusMap a b c d (z : RiemannSphere) =
      if c * z + d = 0 then ∞ else (((a * z + b) / (c * z + d) : ℂ) : RiemannSphere) := rfl

theorem moebiusMap_scale {k : ℂ} (hk : k ≠ 0) (a b c d : ℂ) (p : RiemannSphere) :
    moebiusMap (k * a) (k * b) (k * c) (k * d) p = moebiusMap a b c d p := by
  classical
  induction p using OnePoint.rec with
  | infty =>
    by_cases hc : c = 0
    · simp [hc]
    · simp [hc, mul_ne_zero hk hc, mul_div_mul_left _ _ hk]
  | coe z =>
    have hden : k * c * z + k * d = k * (c * z + d) := by ring
    have hnum : k * a * z + k * b = k * (a * z + b) := by ring
    by_cases h0 : c * z + d = 0
    · simp [hden, h0]
    · simp [hden, hnum, mul_ne_zero hk h0, h0, mul_div_mul_left _ _ hk]

@[simp] theorem moebiusMap_id (p : RiemannSphere) :
    moebiusMap 1 0 0 1 p = p := by
  classical
  induction p using OnePoint.rec <;> simp

theorem moebiusMap_comp {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℂ}
    (_h₁ : a₁ * d₁ - b₁ * c₁ ≠ 0) (h₂ : a₂ * d₂ - b₂ * c₂ ≠ 0) (p : RiemannSphere) :
    moebiusMap a₁ b₁ c₁ d₁ (moebiusMap a₂ b₂ c₂ d₂ p) =
      moebiusMap (a₁ * a₂ + b₁ * c₂) (a₁ * b₂ + b₁ * d₂)
        (c₁ * a₂ + d₁ * c₂) (c₁ * b₂ + d₁ * d₂) p := by
  classical
  induction p using OnePoint.rec with
  | infty =>
    by_cases hc₂ : c₂ = 0
    · have ha₂ : a₂ ≠ 0 := by
        intro ha0; apply h₂; simp [ha0, hc₂]
      simp only [moebiusMap_infty, hc₂, ↓reduceIte, mul_zero, add_zero]
      by_cases hc₁ : c₁ = 0
      · simp [hc₁]
      · simp [hc₁, mul_ne_zero hc₁ ha₂, mul_div_mul_right _ _ ha₂]
    · simp only [moebiusMap_infty, hc₂, ↓reduceIte, moebiusMap_coe]
      have hden_eq : c₁ * (a₂ / c₂) + d₁ = (c₁ * a₂ + d₁ * c₂) / c₂ := by
        rw [mul_div_assoc', div_add' _ _ _ hc₂]
      have hnum_eq : a₁ * (a₂ / c₂) + b₁ = (a₁ * a₂ + b₁ * c₂) / c₂ := by
        rw [mul_div_assoc', div_add' _ _ _ hc₂]
      rw [hden_eq, hnum_eq]
      by_cases hc₃ : c₁ * a₂ + d₁ * c₂ = 0
      · simp [hc₃]
      · simp [hc₃, div_ne_zero hc₃ hc₂, div_div_div_cancel_right₀ hc₂]
  | coe z =>
    by_cases hden₂ : c₂ * z + d₂ = 0
    · have hnum₂ : a₂ * z + b₂ ≠ 0 := by
        intro hnum0
        apply h₂
        linear_combination -c₂ * hnum0 + a₂ * hden₂
      have hc₃_eq : (c₁ * a₂ + d₁ * c₂) * z + (c₁ * b₂ + d₁ * d₂) = c₁ * (a₂ * z + b₂) := by
        linear_combination d₁ * hden₂
      have ha₃_eq : (a₁ * a₂ + b₁ * c₂) * z + (a₁ * b₂ + b₁ * d₂) = a₁ * (a₂ * z + b₂) := by
        linear_combination b₁ * hden₂
      simp only [moebiusMap_coe, hden₂, ↓reduceIte, moebiusMap_infty, hc₃_eq, ha₃_eq]
      by_cases hc₁ : c₁ = 0
      · simp [hc₁]
      · simp [hc₁, mul_ne_zero hc₁ hnum₂, mul_div_mul_right _ _ hnum₂]
    · simp only [moebiusMap_coe, hden₂, ↓reduceIte]
      have hden_eq : c₁ * ((a₂ * z + b₂) / (c₂ * z + d₂)) + d₁ =
          ((c₁ * a₂ + d₁ * c₂) * z + (c₁ * b₂ + d₁ * d₂)) / (c₂ * z + d₂) := by
        rw [mul_div_assoc', div_add' _ _ _ hden₂]
        congr 1
        ring
      have hnum_eq : a₁ * ((a₂ * z + b₂) / (c₂ * z + d₂)) + b₁ =
          ((a₁ * a₂ + b₁ * c₂) * z + (a₁ * b₂ + b₁ * d₂)) / (c₂ * z + d₂) := by
        rw [mul_div_assoc', div_add' _ _ _ hden₂]
        congr 1
        ring
      rw [hden_eq, hnum_eq]
      by_cases hden₃ : (c₁ * a₂ + d₁ * c₂) * z + (c₁ * b₂ + d₁ * d₂) = 0
      · simp [hden₃]
      · simp [hden₃, div_ne_zero hden₃ hden₂, div_div_div_cancel_right₀ hden₂]

theorem moebiusMap_inv_left {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) (p : RiemannSphere) :
    moebiusMap d (-b) (-c) a (moebiusMap a b c d p) = p := by
  have hdet' : d * a - (-b) * (-c) ≠ 0 := by
    intro h0; apply hdet; linear_combination h0
  rw [moebiusMap_comp hdet' hdet]
  have h1 : d * a + -b * c = (a * d - b * c) * 1 := by ring
  have h2 : d * b + -b * d = (a * d - b * c) * 0 := by ring
  have h3 : -c * a + a * c = (a * d - b * c) * 0 := by ring
  have h4 : -c * b + a * d = (a * d - b * c) * 1 := by ring
  rw [h1, h2, h3, h4, moebiusMap_scale hdet, moebiusMap_id]

theorem moebiusMap_inv_right {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) (p : RiemannSphere) :
    moebiusMap a b c d (moebiusMap d (-b) (-c) a p) = p := by
  have hdet' : d * a - (-b) * (-c) ≠ 0 := by
    intro h0; apply hdet; linear_combination h0
  have h := moebiusMap_inv_left hdet' p
  simpa using h

theorem moebiusMap_bijective {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) :
    Function.Bijective (moebiusMap a b c d) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨moebiusMap d (-b) (-c) a, moebiusMap_inv_left hdet, moebiusMap_inv_right hdet⟩

/-- Elementary generators of Möbius transformations in 14.3:
translations `z + β`, rotations `u * z` (`‖u‖ = 1`), positive real dilations `r * z` (`r > 0`),
and inversion `1 / z`. -/
def moebiusTrans (β : ℂ) : RiemannSphere → RiemannSphere := moebiusMap 1 β 0 1
def moebiusRot (u : ℂ) : RiemannSphere → RiemannSphere := moebiusMap u 0 0 1
def moebiusDil (r : ℝ) : RiemannSphere → RiemannSphere := moebiusMap (r : ℂ) 0 0 1
def moebiusInv : RiemannSphere → RiemannSphere := moebiusMap 0 1 1 0

/-- Inductive predicate capturing finite compositions of Rudin's four elementary generators
(translations, unit-modulus rotations, positive real dilations, and inversion `1 / z`). -/
inductive GeneratedByElementaryMoebius : (RiemannSphere → RiemannSphere) → Prop
  | id : GeneratedByElementaryMoebius id
  | trans (β : ℂ) {f : RiemannSphere → RiemannSphere} :
      GeneratedByElementaryMoebius f → GeneratedByElementaryMoebius (moebiusTrans β ∘ f)
  | rot (u : ℂ) (hu : ‖u‖ = 1) {f : RiemannSphere → RiemannSphere} :
      GeneratedByElementaryMoebius f → GeneratedByElementaryMoebius (moebiusRot u ∘ f)
  | dil (r : ℝ) (hr : 0 < r) {f : RiemannSphere → RiemannSphere} :
      GeneratedByElementaryMoebius f → GeneratedByElementaryMoebius (moebiusDil r ∘ f)
  | inv {f : RiemannSphere → RiemannSphere} :
      GeneratedByElementaryMoebius f → GeneratedByElementaryMoebius (moebiusInv ∘ f)

/-- **14.3 (Decomposition into elementary generators, RCA pp. 279–280):**
Every linear fractional transformation `moebiusMap a b c d` (`a * d - b * c ≠ 0`) is a composition
of translations, rotations, positive real dilations, and inversion. -/
theorem moebiusMap_generatedByElementary {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) :
    GeneratedByElementaryMoebius (moebiusMap a b c d) := by
  by_cases hc : c = 0
  · have hd : d ≠ 0 := fun hd0 => hdet (by simp [hc, hd0])
    have ha : a ≠ 0 := fun ha0 => hdet (by simp [ha0, hc])
    let k : ℂ := a / d
    have hk : k ≠ 0 := div_ne_zero ha hd
    let r : ℝ := ‖k‖
    have hr : 0 < r := norm_pos_iff.mpr hk
    let u : ℂ := unitDir k
    have hu : ‖u‖ = 1 := norm_unitDir hk
    have hku : u * (r : ℂ) = k := by
      dsimp [u, r]; unfold unitDir
      exact div_mul_cancel₀ k (Complex.ofReal_ne_zero.mpr hr.ne')
    have hgen : GeneratedByElementaryMoebius
        (moebiusTrans (b / d) ∘ moebiusRot u ∘ moebiusDil r ∘ id) :=
      .trans (b / d) (.rot u hu (.dil r hr .id))
    refine (?_ : _ = moebiusMap a b c d) ▸ hgen
    funext p
    dsimp [Function.comp_def, moebiusTrans, moebiusRot, moebiusDil]
    have hd_r : (r : ℂ) * 1 - 0 * 0 ≠ 0 := by simp [r, Complex.ofReal_ne_zero.mpr hr.ne']
    have hd_u : u * 1 - 0 * 0 ≠ 0 := by simp [u, unitDir_ne_zero hk]
    have hd_t : (1 : ℂ) * 1 - (b / d) * 0 ≠ 0 := by simp
    rw [moebiusMap_comp hd_u hd_r]
    simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, hku]
    have hd_k : k * 1 - 0 * 0 ≠ 0 := by simp [k, hk]
    rw [moebiusMap_comp hd_t hd_k]
    simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]
    have hsc := moebiusMap_scale hd k (b / d) 0 1 p
    have hdk : d * k = a := mul_div_cancel₀ a hd
    have hdb : d * (b / d) = b := mul_div_cancel₀ b hd
    rw [hdk, hdb, mul_zero, mul_one] at hsc
    rw [hc]
    exact hsc.symm
  · -- `c ≠ 0`: `(a z + b)/(c z + d) = a/c + ((b c - a d)/c²) / (z + d/c)`
    let k : ℂ := (b * c - a * d) / c ^ 2
    have hnum_ne : b * c - a * d ≠ 0 := fun h0 => hdet (by linear_combination -h0)
    have hk : k ≠ 0 := div_ne_zero hnum_ne (pow_ne_zero 2 hc)
    let r : ℝ := ‖k‖
    have hr : 0 < r := norm_pos_iff.mpr hk
    let u : ℂ := unitDir k
    have hu : ‖u‖ = 1 := norm_unitDir hk
    have hku : u * (r : ℂ) = k := by
      dsimp [u, r]; unfold unitDir
      exact div_mul_cancel₀ k (Complex.ofReal_ne_zero.mpr hr.ne')
    have hgen : GeneratedByElementaryMoebius
        (moebiusTrans (a / c) ∘ moebiusRot u ∘ moebiusDil r ∘ moebiusInv ∘
          moebiusTrans (d / c) ∘ id) :=
      .trans (a / c) (.rot u hu (.dil r hr (.inv (.trans (d / c) .id))))
    refine (?_ : _ = moebiusMap a b c d) ▸ hgen
    funext p
    dsimp [Function.comp_def, moebiusTrans, moebiusRot, moebiusDil, moebiusInv]
    have hd_t1 : (1 : ℂ) * 1 - (d / c) * 0 ≠ 0 := by simp
    have hd_inv : (0 : ℂ) * 0 - 1 * 1 ≠ 0 := by norm_num
    have hd_r : (r : ℂ) * 1 - 0 * 0 ≠ 0 := by simp [r, Complex.ofReal_ne_zero.mpr hr.ne']
    have hd_u : u * 1 - 0 * 0 ≠ 0 := by simp [u, unitDir_ne_zero hk]
    have hd_t2 : (1 : ℂ) * 1 - (a / c) * 0 ≠ 0 := by simp
    rw [moebiusMap_comp hd_inv hd_t1]
    simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]
    have hd_step1 : (0 : ℂ) * (d / c) - 1 * 1 ≠ 0 := by norm_num
    rw [moebiusMap_comp hd_r hd_step1]
    simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]
    have hd_step2 : (0 : ℂ) * (d / c) - (r : ℂ) * 1 ≠ 0 := by
      simp [r, Complex.ofReal_ne_zero.mpr hr.ne']
    rw [moebiusMap_comp hd_u hd_step2]
    simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, hku]
    have hd_step3 : (0 : ℂ) * (d / c) - k * 1 ≠ 0 := by simp [k, hk]
    rw [moebiusMap_comp hd_t2 hd_step3]
    simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]
    have hsc := moebiusMap_scale hc (a / c) (k + a / c * (d / c)) 1 (d / c) p
    have hc1 : c * (a / c) = a := mul_div_cancel₀ a hc
    have hc2 : c * (k + a / c * (d / c)) = b := by
      dsimp [k]; field_simp [hc]; ring
    have hc3 : c * 1 = c := mul_one c
    have hc4 : c * (d / c) = d := mul_div_cancel₀ d hc
    rw [hc1, hc2, hc3, hc4] at hsc
    exact hsc.symm

/-- **14.3 (Generalized circle equation on `S²`, RCA p. 280):**
A locus `{p ∈ S² | α z conj z + β z + conj β conj z + γ = 0}` (`∞` included iff `α = 0`),
for `α, γ : ℝ` and `β : ℂ` (with nondegeneracy condition `‖β‖ ^ 2 > α * γ` in `IsGeneralizedCircle`). -/
def generalizedCircleLocus (α : ℝ) (β : ℂ) (γ : ℝ) : Set RiemannSphere :=
  {p : RiemannSphere |
    OnePoint.rec (α = 0)
      (fun z : ℂ =>
        (α : ℂ) * z * starRingEnd ℂ z + β * z +
          starRingEnd ℂ β * starRingEnd ℂ z + (γ : ℂ) = 0)
      p}

theorem mem_generalizedCircleLocus_infty (α : ℝ) (β : ℂ) (γ : ℝ) :
    (∞ : RiemannSphere) ∈ generalizedCircleLocus α β γ ↔ α = 0 := Iff.rfl

theorem mem_generalizedCircleLocus_coe (α : ℝ) (β : ℂ) (γ : ℝ) (z : ℂ) :
    (z : RiemannSphere) ∈ generalizedCircleLocus α β γ ↔
      α * ‖z‖ ^ 2 + 2 * (β * z).re + γ = 0 := by
  change (α : ℂ) * z * starRingEnd ℂ z + β * z +
      starRingEnd ℂ β * starRingEnd ℂ z + (γ : ℂ) = 0 ↔ _
  have hzz : z * starRingEnd ℂ z = (‖z‖ ^ 2 : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hbz : β * z + starRingEnd ℂ β * starRingEnd ℂ z = ((2 * (β * z).re : ℝ) : ℂ) := by
    have : starRingEnd ℂ β * starRingEnd ℂ z = starRingEnd ℂ (β * z) := (map_mul _ _ _).symm
    rw [this, Complex.add_conj]
  have lhs_eq :
      (α : ℂ) * z * starRingEnd ℂ z + β * z + starRingEnd ℂ β * starRingEnd ℂ z + (γ : ℂ) =
        ((α * ‖z‖ ^ 2 + 2 * (β * z).re + γ : ℝ) : ℂ) := by
    calc
      (α : ℂ) * z * starRingEnd ℂ z + β * z + starRingEnd ℂ β * starRingEnd ℂ z + (γ : ℂ)
          = (α : ℂ) * (z * starRingEnd ℂ z) + (β * z + starRingEnd ℂ β * starRingEnd ℂ z) + (γ : ℂ) := by
            ring
      _ = (α : ℂ) * (‖z‖ ^ 2 : ℂ) + ((2 * (β * z).re : ℝ) : ℂ) + (γ : ℂ) := by rw [hzz, hbz]
      _ = ((α * ‖z‖ ^ 2 + 2 * (β * z).re + γ : ℝ) : ℂ) := by push_cast; ring
  rw [lhs_eq, Complex.ofReal_eq_zero]

/-- **14.3 (`IsGeneralizedCircle`, RCA p. 280):**
A subset `S ⊆ S²` is a generalized circle when it is defined by `generalizedCircleLocus α β γ`
for real `α, γ` and complex `β` satisfying `‖β‖ ^ 2 > α * γ`. -/
def IsGeneralizedCircle (S : Set RiemannSphere) : Prop :=
  ∃ (α : ℝ) (β : ℂ) (γ : ℝ), ‖β‖ ^ 2 > α * γ ∧ S = generalizedCircleLocus α β γ

/-- **14.3 (Equivalence of generalized circles with Euclidean circles and lines ∪ `{∞}`, RCA p. 280):** -/
theorem isGeneralizedCircle_iff_circle_or_line (S : Set RiemannSphere) :
    IsGeneralizedCircle S ↔
      (∃ (z₀ : ℂ) (r : ℝ), 0 < r ∧ S = ((↑) : ℂ → RiemannSphere) '' sphere z₀ r) ∨
      (∃ (β : ℂ) (γ : ℝ), β ≠ 0 ∧
        S = insert ∞ (((↑) : ℂ → RiemannSphere) ''
          {z : ℂ | 2 * (β * z).re + γ = 0})) := by
  constructor
  · rintro ⟨α, β, γ, hdisc, rfl⟩
    by_cases hα : α = 0
    · right
      have hβ_ne : β ≠ 0 := by
        intro h0
        rw [h0, hα, norm_zero, zero_pow two_ne_zero, zero_mul] at hdisc
        exact lt_irrefl 0 hdisc
      refine ⟨β, γ, hβ_ne, ?_⟩
      ext p
      induction p using OnePoint.rec with
      | infty => simp [mem_generalizedCircleLocus_infty, hα]
      | coe z =>
        rw [mem_generalizedCircleLocus_coe]
        simp [hα]
    · left
      let z₀ : ℂ := -(starRingEnd ℂ β) / (α : ℂ)
      let r : ℝ := Real.sqrt (‖β‖ ^ 2 - α * γ) / |α|
      have hpos_disc : 0 < ‖β‖ ^ 2 - α * γ := sub_pos.mpr hdisc
      have hr : 0 < r := div_pos (Real.sqrt_pos.mpr hpos_disc) (abs_pos.mpr hα)
      refine ⟨z₀, r, hr, ?_⟩
      have hz₀_re : z₀.re = -β.re / α := by
        dsimp [z₀]
        rw [div_ofReal_re, Complex.neg_re, Complex.conj_re]
      have hz₀_im : z₀.im = β.im / α := by
        dsimp [z₀]
        rw [div_ofReal_im, Complex.neg_im, Complex.conj_im, neg_neg]
      ext p
      induction p using OnePoint.rec with
      | infty =>
        simp [mem_generalizedCircleLocus_infty, hα]
      | coe z =>
        rw [mem_generalizedCircleLocus_coe, OnePoint.coe_injective.mem_set_image,
          mem_sphere, dist_eq_norm]
        have hr_sq : r ^ 2 = (‖β‖ ^ 2 - α * γ) / α ^ 2 := by
          dsimp [r]
          rw [div_pow, Real.sq_sqrt hpos_disc.le, sq_abs]
        have hnorm_z : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; ring
        have hnorm_β : ‖β‖ ^ 2 = β.re ^ 2 + β.im ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; ring
        have hnorm_diff : ‖z - z₀‖ ^ 2 = (z.re - z₀.re) ^ 2 + (z.im - z₀.im) ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]; ring
        have hbz_re : (β * z).re = β.re * z.re - β.im * z.im := Complex.mul_re β z
        have hid : ‖z - z₀‖ ^ 2 - r ^ 2 =
            (α * ‖z‖ ^ 2 + 2 * (β * z).re + γ) / α := by
          rw [hnorm_diff, hz₀_re, hz₀_im, hr_sq, hnorm_z, hnorm_β, hbz_re]
          field_simp [hα]
          ring
        constructor
        · intro heq
          have hsq0 : ‖z - z₀‖ ^ 2 = r ^ 2 := by
            have := hid
            rw [heq, zero_div] at this
            linarith
          nlinarith [norm_nonneg (z - z₀), hr]
        · intro hdist
          have hsq0 : ‖z - z₀‖ ^ 2 - r ^ 2 = 0 := by rw [hdist]; ring
          rw [hsq0] at hid
          exact (div_eq_zero_iff.mp hid.symm).resolve_right hα
  · rintro (⟨z₀, r, hr, rfl⟩ | ⟨β, γ, hβ, rfl⟩)
    · refine ⟨1, -starRingEnd ℂ z₀, ‖z₀‖ ^ 2 - r ^ 2, ?_, ?_⟩
      · rw [norm_neg, RingHomIsometric.norm_map]
        linarith [sq_pos_of_pos hr]
      · ext p
        induction p using OnePoint.rec with
        | infty =>
          simp [mem_generalizedCircleLocus_infty]
        | coe z =>
          rw [OnePoint.coe_injective.mem_set_image, mem_sphere, dist_eq_norm,
            mem_generalizedCircleLocus_coe]
          have hid : 1 * ‖z‖ ^ 2 + 2 * ((-starRingEnd ℂ z₀) * z).re + (‖z₀‖ ^ 2 - r ^ 2) =
              ‖z - z₀‖ ^ 2 - r ^ 2 := by
            rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm,
              Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply]
            simp [Complex.mul_re]
            ring
          rw [hid]
          constructor
          · intro hd; rw [hd]; ring
          · intro h0; nlinarith [norm_nonneg (z - z₀), hr]
    · refine ⟨0, β, γ, ?_, ?_⟩
      · rw [zero_mul]; exact sq_pos_of_pos (norm_pos_iff.mpr hβ)
      · ext p
        induction p using OnePoint.rec with
        | infty => simp [mem_generalizedCircleLocus_infty]
        | coe z =>
          rw [mem_generalizedCircleLocus_coe]
          simp

/-- **14.3 (Stereographic-circle characterization, RCA p. 280):**
Rudin states (omitting the proof in print) that generalized circles in `S²` correspond via
stereographic projection (`bookSphereHomeomorph`) precisely to intersections of the unit sphere
`sphere 0 1 ⊆ ℝ³` with planes `{x ∈ ℝ³ | ⟪n, x⟫ = d}` meeting the unit sphere in more than one
point (`d ^ 2 < ‖n‖ ^ 2`). We supply the full machine-checked proof here. -/
theorem theorem14_3_stereographic_circle_iff (S : Set RiemannSphere) :
    IsGeneralizedCircle S ↔
      ∃ (n : SphereAmbient) (d : ℝ), d ^ 2 < ‖n‖ ^ 2 ∧
        bookSphereHomeomorph '' S =
          {x : sphere (0 : SphereAmbient) 1 | @inner ℝ SphereAmbient _ n x.1 = d} := by
  constructor
  · rintro ⟨α, β, γ, hdisc, rfl⟩
    let n : SphereAmbient := !₂[β.re, -β.im, (α - γ) / 2]
    let d : ℝ := -(α + γ) / 2
    have hn_sq : ‖n‖ ^ 2 = β.re ^ 2 + β.im ^ 2 + ((α - γ) / 2) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [n, Fin.sum_univ_succ]
      ring
    have hβ_sq : ‖β‖ ^ 2 = β.re ^ 2 + β.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hd_lt : d ^ 2 < ‖n‖ ^ 2 := by
      rw [hn_sq]
      dsimp [d]
      nlinarith [hdisc, hβ_sq]
    refine ⟨n, d, hd_lt, ?_⟩
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      simp only [Set.mem_setOf_eq]
      induction p using OnePoint.rec with
      | infty =>
        rw [mem_generalizedCircleLocus_infty] at hp
        rw [bookSphereHomeomorph_infty]
        simp [n, d, northPole, PiLp.inner_apply, Fin.sum_univ_three, hp]
      | coe z =>
        rw [mem_generalizedCircleLocus_coe] at hp
        rw [bookSphereHomeomorph_coe]
        have hpos : 0 < ‖z‖ ^ 2 + 1 := by positivity
        rw [Complex.mul_re] at hp
        simp [n, d, PiLp.inner_apply, Fin.sum_univ_three]
        field_simp [hpos.ne']
        linear_combination 2 * hp
    · intro hx
      simp only [Set.mem_setOf_eq] at hx
      refine ⟨bookSphereHomeomorph.symm x, ?_, bookSphereHomeomorph.apply_symm_apply x⟩
      have hx_eq : bookSphereHomeomorph (bookSphereHomeomorph.symm x) = x :=
        bookSphereHomeomorph.apply_symm_apply x
      rw [← hx_eq] at hx
      generalize bookSphereHomeomorph.symm x = p at hx ⊢
      clear hx_eq
      induction p using OnePoint.rec with
      | infty =>
        rw [mem_generalizedCircleLocus_infty]
        rw [bookSphereHomeomorph_infty] at hx
        simp [n, d, northPole, PiLp.inner_apply, Fin.sum_univ_three] at hx
        linarith
      | coe z =>
        rw [mem_generalizedCircleLocus_coe, Complex.mul_re]
        rw [bookSphereHomeomorph_coe] at hx
        have hpos : 0 < ‖z‖ ^ 2 + 1 := by positivity
        simp [n, d, PiLp.inner_apply, Fin.sum_univ_three] at hx
        field_simp [hpos.ne'] at hx
        linear_combination (1 / 2 : ℝ) * hx
  · rintro ⟨n, d, hd_lt, hS_eq⟩
    let α : ℝ := n 2 - d
    let β : ℂ := ⟨n 0, -(n 1)⟩
    let γ : ℝ := -(n 2 + d)
    have hn_sq : ‖n‖ ^ 2 = (n 0) ^ 2 + (n 1) ^ 2 + (n 2) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_three]
    have hβ_sq : ‖β‖ ^ 2 = (n 0) ^ 2 + (n 1) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      dsimp [β]; ring
    have hdisc : ‖β‖ ^ 2 > α * γ := by
      rw [hβ_sq]
      dsimp [α, γ]
      nlinarith [hd_lt, hn_sq]
    refine ⟨α, β, γ, hdisc, ?_⟩
    ext p
    have hp_iff : p ∈ S ↔ bookSphereHomeomorph p ∈ bookSphereHomeomorph '' S :=
      (bookSphereHomeomorph.injective.mem_set_image).symm
    rw [hp_iff, hS_eq, Set.mem_setOf_eq]
    induction p using OnePoint.rec with
    | infty =>
      rw [mem_generalizedCircleLocus_infty, bookSphereHomeomorph_infty]
      simp [α, northPole, PiLp.inner_apply, Fin.sum_univ_three]
      constructor <;> intro h <;> linarith
    | coe z =>
      rw [mem_generalizedCircleLocus_coe, bookSphereHomeomorph_coe]
      have hpos : 0 < ‖z‖ ^ 2 + 1 := by positivity
      simp [α, β, γ, PiLp.inner_apply, Fin.sum_univ_three]
      constructor
      · intro h
        field_simp [hpos.ne'] at h
        linear_combination h
      · intro h
        field_simp [hpos.ne']
        linear_combination h

/-- Helper: every elementary generator maps generalized circles to generalized circles. -/
theorem isGeneralizedCircle_image_moebiusMap {a b c d : ℂ} (hdet : a * d - b * c ≠ 0)
    {S : Set RiemannSphere} (hS : IsGeneralizedCircle S) :
    IsGeneralizedCircle (moebiusMap a b c d '' S) := by
  -- Prove preservation for affine maps `z ↦ k * z + t` (`k ≠ 0`) and inversion `z ↦ 1 / z`
  have h_trans : ∀ (t : ℂ) {T : Set RiemannSphere},
      IsGeneralizedCircle T → IsGeneralizedCircle (moebiusTrans t '' T) := by
    rintro t T ⟨α, β, γ, hdisc, rfl⟩
    let β' : ℂ := β - (α : ℂ) * starRingEnd ℂ t
    let γ' : ℝ := α * ‖t‖ ^ 2 - 2 * (β * t).re + γ
    have hdisc' : ‖β'‖ ^ 2 > α * γ' := by
      have h1 : ‖β'‖ ^ 2 = ‖β‖ ^ 2 - 2 * α * (β * t).re + α ^ 2 * ‖t‖ ^ 2 := by
        repeat rw [Complex.sq_norm]
        repeat rw [Complex.normSq_apply]
        simp [β', Complex.mul_re]
        ring
      rw [h1]
      dsimp [γ']
      nlinarith
    refine ⟨α, β', γ', hdisc', ?_⟩
    ext p
    have hd_t : (1 : ℂ) * 1 - t * 0 ≠ 0 := by simp
    have hp_iff : p ∈ moebiusTrans t '' generalizedCircleLocus α β γ ↔
        moebiusTrans (-t) p ∈ generalizedCircleLocus α β γ := by
      constructor
      · rintro ⟨q, hq, rfl⟩
        have hinv := moebiusMap_inv_left hd_t q
        simp only [neg_zero] at hinv
        dsimp only [moebiusTrans]
        rwa [hinv]
      · intro hp_pre
        refine ⟨moebiusTrans (-t) p, hp_pre, ?_⟩
        have hinv := moebiusMap_inv_right hd_t p
        simp only [neg_zero] at hinv
        exact hinv
    rw [hp_iff]
    induction p using OnePoint.rec with
    | infty =>
      simp [moebiusTrans, mem_generalizedCircleLocus_infty]
    | coe w =>
      have hw : moebiusTrans (-t) (w : RiemannSphere) = ((w - t : ℂ) : RiemannSphere) := by
        simp [moebiusTrans, sub_eq_add_neg]
      rw [hw, mem_generalizedCircleLocus_coe, mem_generalizedCircleLocus_coe]
      have hid : α * ‖w - t‖ ^ 2 + 2 * (β * (w - t)).re + γ =
          α * ‖w‖ ^ 2 + 2 * (β' * w).re + γ' := by
        dsimp only [β', γ']
        repeat rw [Complex.sq_norm]
        repeat rw [Complex.normSq_apply]
        simp [Complex.mul_re]
        ring
      rw [hid]
  have h_mul : ∀ (k : ℂ) (_hk : k ≠ 0) {T : Set RiemannSphere},
      IsGeneralizedCircle T → IsGeneralizedCircle (moebiusMap k 0 0 1 '' T) := by
    rintro k hk T ⟨α, β, γ, hdisc, rfl⟩
    let α' : ℝ := α / ‖k‖ ^ 2
    let β' : ℂ := β / k
    have hk_pos : 0 < ‖k‖ := norm_pos_iff.mpr hk
    have hdisc' : ‖β'‖ ^ 2 > α' * γ :=
      gt_iff_lt.mpr (by
        dsimp [α', β']
        rw [norm_div, div_pow, div_mul_eq_mul_div]
        exact (div_lt_div_iff_of_pos_right (sq_pos_of_pos hk_pos)).mpr hdisc)
    refine ⟨α', β', γ, hdisc', ?_⟩
    ext p
    have hd_k : k * 1 - 0 * 0 ≠ 0 := by simp [hk]
    have hd_kinv : k⁻¹ * 1 - 0 * 0 ≠ 0 := by simp [inv_ne_zero hk]
    have hp_iff : p ∈ moebiusMap k 0 0 1 '' generalizedCircleLocus α β γ ↔
        moebiusMap k⁻¹ 0 0 1 p ∈ generalizedCircleLocus α β γ := by
      constructor
      · rintro ⟨q, hq, rfl⟩
        have hcomp := moebiusMap_comp hd_kinv hd_k q
        simp only [mul_zero, add_zero, zero_add, zero_mul, mul_one, inv_mul_cancel₀ hk,
          moebiusMap_id] at hcomp
        rwa [hcomp]
      · intro hp_pre
        refine ⟨moebiusMap k⁻¹ 0 0 1 p, hp_pre, ?_⟩
        have hcomp := moebiusMap_comp hd_k hd_kinv p
        simp only [mul_zero, add_zero, zero_add, zero_mul, mul_one, mul_inv_cancel₀ hk,
          moebiusMap_id] at hcomp
        exact hcomp
    rw [hp_iff]
    induction p using OnePoint.rec with
    | infty =>
      simp [mem_generalizedCircleLocus_infty, α', hk_pos.ne']
    | coe w =>
      have hw : moebiusMap k⁻¹ 0 0 1 (w : RiemannSphere) = ((k⁻¹ * w : ℂ) : RiemannSphere) := by
        simp
      rw [hw, mem_generalizedCircleLocus_coe, mem_generalizedCircleLocus_coe]
      have hid : α * ‖k⁻¹ * w‖ ^ 2 + 2 * (β * (k⁻¹ * w)).re + γ =
          α' * ‖w‖ ^ 2 + 2 * (β' * w).re + γ := by
        dsimp [α', β']
        rw [norm_mul, norm_inv, mul_pow, inv_pow]
        have hbw : β * (k⁻¹ * w) = (β / k) * w := by field_simp [hk]
        rw [hbw]
        ring
      rw [hid]
  have h_inv : ∀ {T : Set RiemannSphere},
      IsGeneralizedCircle T → IsGeneralizedCircle (moebiusInv '' T) := by
    rintro T ⟨α, β, γ, hdisc, rfl⟩
    have hdisc' : ‖starRingEnd ℂ β‖ ^ 2 > γ * α := by
      rw [RingHomIsometric.norm_map, mul_comm]
      exact hdisc
    refine ⟨γ, starRingEnd ℂ β, α, hdisc', ?_⟩
    ext p
    have hd_inv : (0 : ℂ) * 0 - 1 * 1 ≠ 0 := by norm_num
    have hinvol : ∀ q : RiemannSphere, moebiusInv (moebiusInv q) = q := by
      intro q
      have h := moebiusMap_comp hd_inv hd_inv q
      simpa [moebiusInv] using h
    have hp_iff : p ∈ moebiusInv '' generalizedCircleLocus α β γ ↔
        moebiusInv p ∈ generalizedCircleLocus α β γ := by
      constructor
      · rintro ⟨q, hq, rfl⟩; rwa [hinvol]
      · intro hp_pre; exact ⟨moebiusInv p, hp_pre, hinvol p⟩
    rw [hp_iff]
    induction p using OnePoint.rec with
    | infty =>
      have h0 : moebiusInv ∞ = ((0 : ℂ) : RiemannSphere) := by simp [moebiusInv]
      rw [h0, mem_generalizedCircleLocus_coe, mem_generalizedCircleLocus_infty]
      simp
    | coe w =>
      by_cases hw0 : w = 0
      · subst hw0
        have hinf : moebiusInv ((0 : ℂ) : RiemannSphere) = ∞ := by simp [moebiusInv]
        rw [hinf, mem_generalizedCircleLocus_infty, mem_generalizedCircleLocus_coe]
        simp
      · have hfin : moebiusInv (w : RiemannSphere) = ((w⁻¹ : ℂ) : RiemannSphere) := by
          simp [moebiusInv, hw0]
        rw [hfin, mem_generalizedCircleLocus_coe, mem_generalizedCircleLocus_coe]
        have hw_pos : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw0)
        have hbw : (β * w⁻¹).re = (starRingEnd ℂ β * w).re / ‖w‖ ^ 2 := by
          have hw_conj : w⁻¹ = starRingEnd ℂ w / ((‖w‖ ^ 2 : ℝ) : ℂ) := by
            have h1 : w * (starRingEnd ℂ w / ((‖w‖ ^ 2 : ℝ) : ℂ)) = 1 := by
              rw [mul_div_assoc', Complex.mul_conj, Complex.normSq_eq_norm_sq,
                div_self (Complex.ofReal_ne_zero.mpr hw_pos.ne')]
            exact inv_eq_of_mul_eq_one_right h1
          rw [hw_conj, ← mul_div_assoc, div_ofReal_re]
          have hre_conj : (β * starRingEnd ℂ w).re = (starRingEnd ℂ β * w).re := by
            have : starRingEnd ℂ (β * starRingEnd ℂ w) = starRingEnd ℂ β * w := by simp
            rw [← this, Complex.conj_re]
          rw [hre_conj]
        have hid : α * ‖w⁻¹‖ ^ 2 + 2 * (β * w⁻¹).re + γ =
            (γ * ‖w‖ ^ 2 + 2 * (starRingEnd ℂ β * w).re + α) / ‖w‖ ^ 2 := by
          rw [norm_inv, inv_pow, hbw]
          field_simp [hw_pos.ne']
          ring
        rw [hid, div_eq_zero_iff]
        exact ⟨fun h => h.resolve_right hw_pos.ne', fun h => Or.inl h⟩
  -- Induct along `GeneratedByElementaryMoebius`
  have hgen := moebiusMap_generatedByElementary hdet
  generalize moebiusMap a b c d = M at hgen ⊢
  revert S
  induction hgen with
  | id => intro S hS; simpa using hS
  | trans β _ ih =>
    intro S hS
    rw [Set.image_comp]
    exact h_trans β (ih hS)
  | rot u hu _ ih =>
    intro S hS
    rw [Set.image_comp]
    have hu_ne : u ≠ 0 := fun h0 => by rw [h0, norm_zero] at hu; exact zero_ne_one hu
    exact h_mul u hu_ne (ih hS)
  | dil r hr _ ih =>
    intro S hS
    rw [Set.image_comp]
    exact h_mul (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne') (ih hS)
  | inv _ ih =>
    intro S hS
    rw [Set.image_comp]
    exact h_inv (ih hS)

/-- Uniqueness of Möbius maps fixing `(0, 1, ∞)`: any `moebiusMap a b c d` (`a * d - b * c ≠ 0`)
sending `0 ↦ 0`, `1 ↦ 1`, and `∞ ↦ ∞` is the identity on `RiemannSphere`. -/
theorem moebiusMap_eq_id_of_fixes_zero_one_infty {a b c d : ℂ} (hdet : a * d - b * c ≠ 0)
    (h0 : moebiusMap a b c d (0 : ℂ) = (0 : ℂ))
    (h1 : moebiusMap a b c d (1 : ℂ) = (1 : ℂ))
    (hinf : moebiusMap a b c d ∞ = ∞) :
    ∀ p : RiemannSphere, moebiusMap a b c d p = p := by
  have hc : c = 0 := by
    by_contra hc_ne
    simp [hc_ne] at hinf
  have hd_ne : d ≠ 0 := fun hd0 => hdet (by simp [hc, hd0])
  have hb : b = 0 := by
    have h0' : (a * 0 + b) / (c * 0 + d) = 0 := OnePoint.coe_injective (by simpa [hc, hd_ne] using h0)
    simp [hc] at h0'
    exact h0'.resolve_right hd_ne
  have ha : a = d := by
    have h1' : (a * 1 + b) / (c * 1 + d) = 1 := OnePoint.coe_injective (by simpa [hc, hd_ne] using h1)
    simp [hc, hb] at h1'
    exact (div_eq_one_iff_eq hd_ne).mp h1'
  intro p
  subst hc hb ha
  have hsc := moebiusMap_scale hd_ne 1 0 0 1 p
  simpa using hsc

open Classical in
/-- Explicit matrix coefficients `(a, b, c, d)` carrying any ordered triple `(p₁, p₂, p₃)` of
distinct points of `RiemannSphere` to `(0, 1, ∞)`. For finite `a, b, c`, this is Rudin's exact
formula `(b - c) * (z - a) / ((b - a) * (z - c))`. -/
def moebiusToStdCoeffs (p₁ p₂ p₃ : RiemannSphere) : ℂ × ℂ × ℂ × ℂ :=
  OnePoint.rec
    (OnePoint.rec (1, 0, 0, 1)
      (fun b => OnePoint.rec (1, 0, 0, 1)
        (fun c => (0, b - c, 1, -c)) p₃) p₂)
    (fun a => OnePoint.rec
      (OnePoint.rec (1, 0, 0, 1) (fun c => (1, -a, 1, -c)) p₃)
      (fun b => OnePoint.rec (1, -a, 0, b - a)
        (fun c => (b - c, -(b - c) * a, b - a, -(b - a) * c)) p₃) p₂)
    p₁

theorem moebiusToStdCoeffs_infty_coe_coe (b c : ℂ) :
    moebiusToStdCoeffs ∞ (b : RiemannSphere) (c : RiemannSphere) = (0, b - c, 1, -c) := rfl

theorem moebiusToStdCoeffs_coe_infty_coe (a c : ℂ) :
    moebiusToStdCoeffs (a : RiemannSphere) ∞ (c : RiemannSphere) = (1, -a, 1, -c) := rfl

theorem moebiusToStdCoeffs_coe_coe_infty (a b : ℂ) :
    moebiusToStdCoeffs (a : RiemannSphere) (b : RiemannSphere) ∞ = (1, -a, 0, b - a) := rfl

theorem moebiusToStdCoeffs_coe_coe_coe (a b c : ℂ) :
    moebiusToStdCoeffs (a : RiemannSphere) (b : RiemannSphere) (c : RiemannSphere) =
      (b - c, -(b - c) * a, b - a, -(b - a) * c) := rfl

theorem moebiusToStdCoeffs_spec {p₁ p₂ p₃ : RiemannSphere}
    (h12 : p₁ ≠ p₂) (h23 : p₂ ≠ p₃) (h13 : p₁ ≠ p₃) :
    let (a, b, c, d) := moebiusToStdCoeffs p₁ p₂ p₃
    a * d - b * c ≠ 0 ∧
      moebiusMap a b c d p₁ = (0 : ℂ) ∧
      moebiusMap a b c d p₂ = (1 : ℂ) ∧
      moebiusMap a b c d p₃ = ∞ := by
  classical
  induction p₁ using OnePoint.rec with
  | infty =>
    induction p₂ using OnePoint.rec with
    | infty => exact False.elim (h12 rfl)
    | coe b =>
      induction p₃ using OnePoint.rec with
      | infty => exact False.elim (h13 rfl)
      | coe c =>
        have hbc : b - c ≠ 0 := sub_ne_zero.mpr (fun h => h23 (congrArg _ h))
        rw [moebiusToStdCoeffs_infty_coe_coe]
        dsimp only
        refine ⟨by intro h0; apply hbc; linear_combination -h0, ?_, ?_, ?_⟩
        · rw [moebiusMap_infty, if_neg one_ne_zero, zero_div]
        · rw [moebiusMap_coe]
          have hd : (1 : ℂ) * b + -c = b - c := by ring
          have hn : (0 : ℂ) * b + (b - c) = b - c := by ring
          rw [hd, hn, if_neg hbc, div_self hbc]
        · rw [moebiusMap_coe]
          have hd : (1 : ℂ) * c + -c = 0 := by ring
          rw [hd, if_pos rfl]
  | coe a =>
    induction p₂ using OnePoint.rec with
    | infty =>
      induction p₃ using OnePoint.rec with
      | infty => exact False.elim (h23 rfl)
      | coe c =>
        have hac : a - c ≠ 0 := sub_ne_zero.mpr (fun h => h13 (congrArg _ h))
        rw [moebiusToStdCoeffs_coe_infty_coe]
        dsimp only
        refine ⟨by intro h0; apply hac; linear_combination h0, ?_, ?_, ?_⟩
        · rw [moebiusMap_coe]
          have hd : (1 : ℂ) * a + -c = a - c := by ring
          have hn : (1 : ℂ) * a + -a = 0 := by ring
          rw [hd, hn, if_neg hac, zero_div]
        · rw [moebiusMap_infty, if_neg one_ne_zero, div_one]
        · rw [moebiusMap_coe]
          have hd : (1 : ℂ) * c + -c = 0 := by ring
          rw [hd, if_pos rfl]
    | coe b =>
      have hba : b - a ≠ 0 := sub_ne_zero.mpr (fun h => h12 (congrArg _ h.symm))
      induction p₃ using OnePoint.rec with
      | infty =>
        rw [moebiusToStdCoeffs_coe_coe_infty]
        dsimp only
        refine ⟨by intro h0; apply hba; linear_combination h0, ?_, ?_, ?_⟩
        · rw [moebiusMap_coe]
          have hd : (0 : ℂ) * a + (b - a) = b - a := by ring
          have hn : (1 : ℂ) * a + -a = 0 := by ring
          rw [hd, hn, if_neg hba, zero_div]
        · rw [moebiusMap_coe]
          have hd : (0 : ℂ) * b + (b - a) = b - a := by ring
          have hn : (1 : ℂ) * b + -a = b - a := by ring
          rw [hd, hn, if_neg hba, div_self hba]
        · rw [moebiusMap_infty, if_pos rfl]
      | coe c =>
        have hbc : b - c ≠ 0 := sub_ne_zero.mpr (fun h => h23 (congrArg _ h))
        have hac : a - c ≠ 0 := sub_ne_zero.mpr (fun h => h13 (congrArg _ h))
        rw [moebiusToStdCoeffs_coe_coe_coe]
        dsimp only
        have hdet : (b - c) * (-(b - a) * c) - -(b - c) * a * (b - a) ≠ 0 := by
          have hid : (b - c) * (-(b - a) * c) - -(b - c) * a * (b - a) =
              (b - c) * (b - a) * (a - c) := by ring
          rw [hid]
          exact mul_ne_zero (mul_ne_zero hbc hba) hac
        refine ⟨hdet, ?_, ?_, ?_⟩
        · rw [moebiusMap_coe]
          have hd : (b - a) * a + -(b - a) * c = (b - a) * (a - c) := by ring
          have hn : (b - c) * a + -(b - c) * a = 0 := by ring
          rw [hd, hn, if_neg (mul_ne_zero hba hac), zero_div]
        · rw [moebiusMap_coe]
          have hd : (b - a) * b + -(b - a) * c = (b - a) * (b - c) := by ring
          have hn : (b - c) * b + -(b - c) * a = (b - a) * (b - c) := by ring
          have hden_ne : (b - a) * (b - c) ≠ 0 := mul_ne_zero hba hbc
          rw [hd, hn, if_neg hden_ne, div_self hden_ne]
        · rw [moebiusMap_coe]
          have hd : (b - a) * c + -(b - a) * c = 0 := by ring
          rw [hd, if_pos rfl]

/-- **14.3 (Explicit finite cross-ratio formula carrying `(a, b, c) ↦ (0, 1, ∞)`, RCA p. 280):** -/
theorem moebius_finite_triple_to_zero_one_infty {a b c : ℂ}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    let M := moebiusMap (b - c) (-(b - c) * a) (b - a) (-(b - a) * c)
    (b - c) * (-(b - a) * c) - (-(b - c) * a) * (b - a) ≠ 0 ∧
      M (a : RiemannSphere) = (0 : ℂ) ∧
      M (b : RiemannSphere) = (1 : ℂ) ∧
      M (c : RiemannSphere) = ∞ ∧
      ∀ z : ℂ, z ≠ c →
        M (z : RiemannSphere) =
          ((((b - c) * (z - a)) / ((b - a) * (z - c)) : ℂ) : RiemannSphere) := by
  have hspec := moebiusToStdCoeffs_spec
    (p₁ := (a : RiemannSphere)) (p₂ := (b : RiemannSphere)) (p₃ := (c : RiemannSphere))
    (fun h => hab (OnePoint.coe_injective h))
    (fun h => hbc (OnePoint.coe_injective h))
    (fun h => hac (OnePoint.coe_injective h))
  rw [moebiusToStdCoeffs_coe_coe_coe] at hspec
  dsimp only at hspec
  refine ⟨hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2, ?_⟩
  intro z hzc
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hzc' : z - c ≠ 0 := sub_ne_zero.mpr hzc
  have hden : (b - a) * z + -(b - a) * c = (b - a) * (z - c) := by ring
  have hnum : (b - c) * z + -(b - c) * a = (b - c) * (z - a) := by ring
  rw [moebiusMap_coe, hden, hnum, if_neg (mul_ne_zero hba hzc')]

/-- **14.3 (Unique three-point interpolation on `RiemannSphere`, RCA p. 280):**
Given any two ordered triples `(p₁, p₂, p₃)` and `(q₁, q₂, q₃)` of pairwise distinct points in
`S²`, there exists a Möbius transformation carrying `(p₁, p₂, p₃)` to `(q₁, q₂, q₃)`, and any
two Möbius transformations doing so agree everywhere on `S²`. -/
theorem moebius_unique_three_point_interpolation
    {p₁ p₂ p₃ q₁ q₂ q₃ : RiemannSphere}
    (hp12 : p₁ ≠ p₂) (hp23 : p₂ ≠ p₃) (hp13 : p₁ ≠ p₃)
    (hq12 : q₁ ≠ q₂) (hq23 : q₂ ≠ q₃) (hq13 : q₁ ≠ q₃) :
    (∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
      moebiusMap a b c d p₁ = q₁ ∧
      moebiusMap a b c d p₂ = q₂ ∧
      moebiusMap a b c d p₃ = q₃) ∧
    (∀ (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℂ),
      a₁ * d₁ - b₁ * c₁ ≠ 0 → a₂ * d₂ - b₂ * c₂ ≠ 0 →
      moebiusMap a₁ b₁ c₁ d₁ p₁ = q₁ → moebiusMap a₁ b₁ c₁ d₁ p₂ = q₂ →
        moebiusMap a₁ b₁ c₁ d₁ p₃ = q₃ →
      moebiusMap a₂ b₂ c₂ d₂ p₁ = q₁ → moebiusMap a₂ b₂ c₂ d₂ p₂ = q₂ →
        moebiusMap a₂ b₂ c₂ d₂ p₃ = q₃ →
      ∀ p : RiemannSphere, moebiusMap a₁ b₁ c₁ d₁ p = moebiusMap a₂ b₂ c₂ d₂ p) := by
  rcases hp_eq : moebiusToStdCoeffs p₁ p₂ p₃ with ⟨ap, bp, cp, dp⟩
  have hp_spec := moebiusToStdCoeffs_spec hp12 hp23 hp13
  rw [hp_eq] at hp_spec
  obtain ⟨hdet_p, hp1, hp2, hp3⟩ := hp_spec
  rcases hq_eq : moebiusToStdCoeffs q₁ q₂ q₃ with ⟨aq, bq, cq, dq⟩
  have hq_spec := moebiusToStdCoeffs_spec hq12 hq23 hq13
  rw [hq_eq] at hq_spec
  obtain ⟨hdet_q, hq1, hq2, hq3⟩ := hq_spec
  have hdet_q_inv : dq * aq - (-bq) * (-cq) ≠ 0 := by
    intro h0; apply hdet_q; linear_combination h0
  constructor
  · -- Existence: `M_q⁻¹ ∘ M_p`
    let a := dq * ap + (-bq) * cp
    let b := dq * bp + (-bq) * dp
    let c := (-cq) * ap + aq * cp
    let d := (-cq) * bp + aq * dp
    have hdet : a * d - b * c ≠ 0 := by
      have hid : a * d - b * c = (dq * aq - (-bq) * (-cq)) * (ap * dp - bp * cp) := by
        dsimp [a, b, c, d]; ring
      rw [hid]
      exact mul_ne_zero hdet_q_inv hdet_p
    refine ⟨a, b, c, d, hdet, ?_, ?_, ?_⟩
    · rw [← moebiusMap_comp hdet_q_inv hdet_p, hp1, ← hq1, moebiusMap_inv_left hdet_q]
    · rw [← moebiusMap_comp hdet_q_inv hdet_p, hp2, ← hq2, moebiusMap_inv_left hdet_q]
    · rw [← moebiusMap_comp hdet_q_inv hdet_p, hp3, ← hq3, moebiusMap_inv_left hdet_q]
  · -- Uniqueness: `M_p ∘ M₂⁻¹ ∘ M₁ ∘ M_p⁻¹` fixes `0, 1, ∞`
    intro a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ hd₁ hd₂ hm11 hm12 hm13 hm21 hm22 hm23 p
    have hd₂_inv : d₂ * a₂ - (-b₂) * (-c₂) ≠ 0 := by
      intro h0; apply hd₂; linear_combination h0
    have hd_p_inv : dp * ap - (-bp) * (-cp) ≠ 0 := by
      intro h0; apply hdet_p; linear_combination h0
    -- Compose `M₂⁻¹ ∘ M₁` into `(u, v, w, x)`
    let u := d₂ * a₁ + (-b₂) * c₁
    let v := d₂ * b₁ + (-b₂) * d₁
    let w := (-c₂) * a₁ + a₂ * c₁
    let x := (-c₂) * b₁ + a₂ * d₁
    have hdet_u : u * x - v * w ≠ 0 := by
      have hid : u * x - v * w = (d₂ * a₂ - (-b₂) * (-c₂)) * (a₁ * d₁ - b₁ * c₁) := by
        dsimp [u, v, w, x]; ring
      rw [hid]; exact mul_ne_zero hd₂_inv hd₁
    -- Conjugate `M_p ∘ (M₂⁻¹ ∘ M₁) ∘ M_p⁻¹`
    let u' := u * dp + v * (-cp)
    let v' := u * (-bp) + v * ap
    let w' := w * dp + x * (-cp)
    let x' := w * (-bp) + x * ap
    have hdet_u' : u' * x' - v' * w' ≠ 0 := by
      have hid : u' * x' - v' * w' = (u * x - v * w) * (dp * ap - (-bp) * (-cp)) := by
        dsimp [u', v', w', x']; ring
      rw [hid]; exact mul_ne_zero hdet_u hd_p_inv
    let A := ap * u' + bp * w'
    let B := ap * v' + bp * x'
    let C := cp * u' + dp * w'
    let D := cp * v' + dp * x'
    have hdet_A : A * D - B * C ≠ 0 := by
      have hid : A * D - B * C = (ap * dp - bp * cp) * (u' * x' - v' * w') := by
        dsimp [A, B, C, D]; ring
      rw [hid]; exact mul_ne_zero hdet_p hdet_u'
    have hconj : ∀ r : RiemannSphere,
        moebiusMap A B C D r =
          moebiusMap ap bp cp dp
            (moebiusMap d₂ (-b₂) (-c₂) a₂
              (moebiusMap a₁ b₁ c₁ d₁ (moebiusMap dp (-bp) (-cp) ap r))) := by
      intro r
      rw [moebiusMap_comp hd₂_inv hd₁, moebiusMap_comp hdet_u hd_p_inv,
        moebiusMap_comp hdet_p hdet_u']
    have hfix0 : moebiusMap A B C D (0 : ℂ) = (0 : ℂ) := by
      rw [hconj, ← hp1, moebiusMap_inv_left hdet_p, hm11, ← hm21,
        moebiusMap_inv_left hd₂, hp1]
    have hfix1 : moebiusMap A B C D (1 : ℂ) = (1 : ℂ) := by
      rw [hconj, ← hp2, moebiusMap_inv_left hdet_p, hm12, ← hm22,
        moebiusMap_inv_left hd₂, hp2]
    have hfix_inf : moebiusMap A B C D ∞ = ∞ := by
      rw [hconj, ← hp3, moebiusMap_inv_left hdet_p, hm13, ← hm23,
        moebiusMap_inv_left hd₂, hp3]
    have hid_A := moebiusMap_eq_id_of_fixes_zero_one_infty hdet_A hfix0 hfix1 hfix_inf
      (moebiusMap ap bp cp dp p)
    rw [hconj, moebiusMap_inv_left hdet_p] at hid_A
    have h1 := (moebiusMap_bijective hdet_p).1 hid_A
    have h2 := congrArg (moebiusMap a₂ b₂ c₂ d₂) h1
    rwa [moebiusMap_inv_right hd₂] at h2


/-- Standard real-line generalized circle `ℝ ∪ {∞} ⊆ S²`. -/
def stdRealLineCircle : Set RiemannSphere :=
  insert ∞ (((↑) : ℂ → RiemannSphere) '' {z : ℂ | z.im = 0})

theorem isGeneralizedCircle_stdRealLineCircle : IsGeneralizedCircle stdRealLineCircle := by
  rw [isGeneralizedCircle_iff_circle_or_line]
  right
  refine ⟨-Complex.I / 2, 0, by simp [Complex.I_ne_zero], ?_⟩
  ext p
  induction p using OnePoint.rec with
  | infty => simp [stdRealLineCircle]
  | coe z =>
    simp only [stdRealLineCircle, Set.mem_insert_iff, OnePoint.coe_ne_infty, false_or,
      OnePoint.coe_injective.mem_set_image, Set.mem_setOf_eq]
    have hre : ((-Complex.I / 2) * z).re = z.im / 2 := by
      have : (-Complex.I / 2) * z = -(Complex.I * z) / ((2 : ℝ) : ℂ) := by push_cast; ring
      rw [this, div_ofReal_re, Complex.neg_re, Complex.I_mul_re, neg_neg]
    rw [hre]
    constructor <;> intro h <;> linarith

/-- Every generalized circle contains three pairwise distinct points of `RiemannSphere`. -/
theorem exists_three_distinct_mem_of_isGeneralizedCircle {S : Set RiemannSphere}
    (hS : IsGeneralizedCircle S) :
    ∃ p₁ p₂ p₃ : RiemannSphere,
      p₁ ∈ S ∧ p₂ ∈ S ∧ p₃ ∈ S ∧ p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃ := by
  rw [isGeneralizedCircle_iff_circle_or_line] at hS
  rcases hS with ⟨z₀, r, hr, rfl⟩ | ⟨β, γ, hβ, rfl⟩
  · let z₁ : ℂ := z₀ + (r : ℂ)
    let z₂ : ℂ := z₀ - (r : ℂ)
    let z₃ : ℂ := z₀ + (r : ℂ) * Complex.I
    have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hz1 : z₁ ∈ sphere z₀ r := by
      simp [z₁, mem_sphere, dist_eq_norm, Complex.norm_real, abs_of_pos hr]
    have hz2 : z₂ ∈ sphere z₀ r := by
      simp [z₂, mem_sphere, dist_eq_norm, Complex.norm_real, abs_of_pos hr]
    have hz3 : z₃ ∈ sphere z₀ r := by
      simp [z₃, mem_sphere, dist_eq_norm, Complex.norm_real, abs_of_pos hr]
    refine ⟨(z₁ : RiemannSphere), (z₂ : RiemannSphere), (z₃ : RiemannSphere),
      ⟨z₁, hz1, rfl⟩, ⟨z₂, hz2, rfl⟩, ⟨z₃, hz3, rfl⟩, ?_, ?_, ?_⟩
    · intro h
      have heq : z₁ = z₂ := OnePoint.coe_injective h
      have h2r : (2 : ℂ) * (r : ℂ) = 0 := by linear_combination heq
      exact mul_ne_zero two_ne_zero hr_ne h2r
    · intro h
      have heq : z₂ = z₃ := OnePoint.coe_injective h
      have h1I : (r : ℂ) * (1 + Complex.I) = 0 := by linear_combination -heq
      have h1I_ne : (1 : ℂ) + Complex.I ≠ 0 := by
        intro h0
        have := congrArg Complex.im h0
        simp at this
      exact mul_ne_zero hr_ne h1I_ne h1I
    · intro h
      have heq : z₁ = z₃ := OnePoint.coe_injective h
      have h1I : (r : ℂ) * (1 - Complex.I) = 0 := by linear_combination heq
      have h1I_ne : (1 : ℂ) - Complex.I ≠ 0 := by
        intro h0
        have := congrArg Complex.im h0
        simp at this
      exact mul_ne_zero hr_ne h1I_ne h1I
  · have hβ_pos : 0 < ‖β‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hβ)
    let z₁ : ℂ := ((-γ / (2 * ‖β‖ ^ 2) : ℝ) : ℂ) * starRingEnd ℂ β
    let z₂ : ℂ := z₁ + Complex.I * starRingEnd ℂ β
    have hbz₁ : β * z₁ = ((-γ / 2 : ℝ) : ℂ) := by
      dsimp [z₁]
      have hconj : β * starRingEnd ℂ β = ((‖β‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hβz : β * (((-γ / (2 * ‖β‖ ^ 2) : ℝ) : ℂ) * starRingEnd ℂ β) =
          ((-γ / (2 * ‖β‖ ^ 2) : ℝ) : ℂ) * (β * starRingEnd ℂ β) := by ring
      rw [hβz, hconj]
      have hβc : (‖β‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hβ).ne'
      push_cast
      field_simp [hβc]
    have hbz_I : (β * (Complex.I * starRingEnd ℂ β)).re = 0 := by
      have hconj : β * (Complex.I * starRingEnd ℂ β) = ((‖β‖ ^ 2 : ℝ) : ℂ) * Complex.I := by
        calc
          β * (Complex.I * starRingEnd ℂ β) = (β * starRingEnd ℂ β) * Complex.I := by ring
          _ = ((‖β‖ ^ 2 : ℝ) : ℂ) * Complex.I := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hconj, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
    have hz1_mem : 2 * (β * z₁).re + γ = 0 := by
      rw [hbz₁, Complex.ofReal_re]; ring
    have hz2_mem : 2 * (β * z₂).re + γ = 0 := by
      dsimp [z₂]
      rw [mul_add, Complex.add_re, hbz_I, add_zero]
      exact hz1_mem
    have hz12 : z₁ ≠ z₂ := by
      intro h
      have h0 : Complex.I * starRingEnd ℂ β = 0 := by linear_combination -h
      exact mul_ne_zero Complex.I_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr hβ) h0
    refine ⟨∞, (z₁ : RiemannSphere), (z₂ : RiemannSphere),
      Set.mem_insert _ _,
      Set.mem_insert_of_mem _ ⟨z₁, hz1_mem, rfl⟩,
      Set.mem_insert_of_mem _ ⟨z₂, hz2_mem, rfl⟩,
      Ne.symm (OnePoint.coe_ne_infty z₁),
      fun h => hz12 (OnePoint.coe_injective h),
      Ne.symm (OnePoint.coe_ne_infty z₂)⟩

/-- Any generalized circle containing `0`, `1`, and `∞` is `stdRealLineCircle`. -/
theorem eq_stdRealLineCircle_of_mem_zero_one_infty {S : Set RiemannSphere}
    (hS : IsGeneralizedCircle S)
    (h0 : ((0 : ℂ) : RiemannSphere) ∈ S)
    (h1 : ((1 : ℂ) : RiemannSphere) ∈ S)
    (hinf : (∞ : RiemannSphere) ∈ S) :
    S = stdRealLineCircle := by
  rcases hS with ⟨α, β, γ, hdisc, rfl⟩
  have hα : α = 0 := (mem_generalizedCircleLocus_infty α β γ).mp hinf
  have hγ : γ = 0 := by
    have := (mem_generalizedCircleLocus_coe α β γ 0).mp h0
    simpa using this
  have hβ_re : β.re = 0 := by
    have := (mem_generalizedCircleLocus_coe α β γ 1).mp h1
    simp [hα, hγ] at this
    exact this
  have hβ_im_ne : β.im ≠ 0 := by
    intro him
    have hβ0 : β = 0 := Complex.ext hβ_re him
    rw [hβ0, hα, norm_zero, zero_pow two_ne_zero, zero_mul] at hdisc
    exact lt_irrefl 0 hdisc
  ext p
  induction p using OnePoint.rec with
  | infty =>
    simp [stdRealLineCircle, mem_generalizedCircleLocus_infty, hα]
  | coe z =>
    rw [mem_generalizedCircleLocus_coe]
    simp only [stdRealLineCircle, Set.mem_insert_iff, OnePoint.coe_ne_infty, false_or,
      OnePoint.coe_injective.mem_set_image, Set.mem_setOf_eq, hα, hγ, zero_mul, zero_add, add_zero]
    rw [Complex.mul_re, hβ_re, zero_mul, zero_sub]
    constructor
    · intro h
      have hprod : β.im * z.im = 0 := by linarith
      exact (mul_eq_zero.mp hprod).resolve_left hβ_im_ne
    · intro hz; rw [hz]; ring

/-- **14.3 (Transitivity of Möbius maps on generalized circles, RCA p. 280):**
Given any two generalized circles `S₁, S₂ ⊆ S²`, some Möbius transformation carries `S₁` onto `S₂`. -/
theorem moebius_maps_generalizedCircle_to_generalizedCircle {S₁ S₂ : Set RiemannSphere}
    (hS₁ : IsGeneralizedCircle S₁) (hS₂ : IsGeneralizedCircle S₂) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ moebiusMap a b c d '' S₁ = S₂ := by
  obtain ⟨p₁, p₂, p₃, hp1, hp2, hp3, hp12, hp23, hp13⟩ :=
    exists_three_distinct_mem_of_isGeneralizedCircle hS₁
  obtain ⟨q₁, q₂, q₃, hq1, hq2, hq3, hq12, hq23, hq13⟩ :=
    exists_three_distinct_mem_of_isGeneralizedCircle hS₂
  obtain ⟨⟨a, b, c, d, hdet, hm1, hm2, hm3⟩, _⟩ :=
    moebius_unique_three_point_interpolation hp12 hp23 hp13 hq12 hq23 hq13
  refine ⟨a, b, c, d, hdet, ?_⟩
  rcases hq_eq : moebiusToStdCoeffs q₁ q₂ q₃ with ⟨aq, bq, cq, dq⟩
  have hq_spec := moebiusToStdCoeffs_spec hq12 hq23 hq13
  rw [hq_eq] at hq_spec
  obtain ⟨hdet_q, hq_0, hq_1, hq_inf⟩ := hq_spec
  have hMS₁ : IsGeneralizedCircle (moebiusMap a b c d '' S₁) :=
    isGeneralizedCircle_image_moebiusMap hdet hS₁
  have himg₁ : moebiusMap aq bq cq dq '' (moebiusMap a b c d '' S₁) = stdRealLineCircle := by
    apply eq_stdRealLineCircle_of_mem_zero_one_infty
      (isGeneralizedCircle_image_moebiusMap hdet_q hMS₁)
    · exact ⟨q₁, ⟨p₁, hp1, hm1⟩, hq_0⟩
    · exact ⟨q₂, ⟨p₂, hp2, hm2⟩, hq_1⟩
    · exact ⟨q₃, ⟨p₃, hp3, hm3⟩, hq_inf⟩
  have himg₂ : moebiusMap aq bq cq dq '' S₂ = stdRealLineCircle := by
    apply eq_stdRealLineCircle_of_mem_zero_one_infty
      (isGeneralizedCircle_image_moebiusMap hdet_q hS₂)
    · exact ⟨q₁, hq1, hq_0⟩
    · exact ⟨q₂, hq2, hq_1⟩
    · exact ⟨q₃, hq3, hq_inf⟩
  exact (moebiusMap_bijective hdet_q).1.image_injective (himg₁.trans himg₂.symm)

/-- **14.3 (Cayley map `(1 + z) / (1 - z)`, RCA p. 280):** -/
def cayleyMap (z : ℂ) : ℂ :=
  (1 + z) / (1 - z)

theorem cayleyMap_props :
    (1 : ℂ) * 1 - 1 * (-1) ≠ 0 ∧
    moebiusMap 1 1 (-1) 1 ((-1 : ℂ) : RiemannSphere) = (0 : ℂ) ∧
    moebiusMap 1 1 (-1) 1 ((0 : ℂ) : RiemannSphere) = (1 : ℂ) ∧
    moebiusMap 1 1 (-1) 1 ((1 : ℂ) : RiemannSphere) = ∞ ∧
    (∀ z : ℂ, z ≠ 1 →
      moebiusMap 1 1 (-1) 1 (z : RiemannSphere) = ((cayleyMap z : ℂ) : RiemannSphere)) ∧
    RudinRCA.Chapter10.HolomorphicOn cayleyMap (ball (0 : ℂ) 1) ∧
    BijOn cayleyMap (ball (0 : ℂ) 1) {w : ℂ | 0 < w.re} := by
  have hdet : (1 : ℂ) * 1 - 1 * (-1) ≠ 0 := by norm_num
  have hsub_ne : ∀ z : ℂ, z ≠ 1 → -1 * z + 1 ≠ 0 := by
    intro z hz h0
    apply hz
    linear_combination -h0
  refine ⟨hdet, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp
  · intro z hz
    have hd := hsub_ne z hz
    have h1 : (1 : ℂ) * z + 1 = 1 + z := by ring
    have h2 : (-1 : ℂ) * z + 1 = 1 - z := by ring
    rw [moebiusMap_coe, h1, h2, if_neg (h2 ▸ hd), cayleyMap]
  · intro z hz
    have hz1 : 1 - z ≠ 0 := by
      intro h0
      have heq : z = 1 := by linear_combination -h0
      rw [heq] at hz
      simp at hz
    exact (differentiableAt_const (1 : ℂ) |>.add differentiableAt_id).div
      (differentiableAt_const (1 : ℂ) |>.sub differentiableAt_id) hz1
  · refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rw [mem_ball_zero_iff] at hz
      have hz1 : 1 - z ≠ 0 := by
        intro h0
        have heq : z = 1 := by linear_combination -h0
        rw [heq, norm_one] at hz
        exact lt_irrefl 1 hz
      have hden_pos : 0 < ‖1 - z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz1)
      have hre_id : (cayleyMap z).re = (1 - ‖z‖ ^ 2) / ‖1 - z‖ ^ 2 := by
        have h1 : cayleyMap z = ((1 + z) * starRingEnd ℂ (1 - z)) / ((‖1 - z‖ ^ 2 : ℝ) : ℂ) := by
          dsimp [cayleyMap]
          rw [div_eq_iff hz1]
          have hconj : (1 - z) * starRingEnd ℂ (1 - z) = ((‖1 - z‖ ^ 2 : ℝ) : ℂ) := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          have hden_c : ((‖1 - z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hden_pos.ne'
          field_simp [hden_c]
          linear_combination -(1 + z) * hconj
        rw [h1, div_ofReal_re]
        have hnum_re : ((1 + z) * starRingEnd ℂ (1 - z)).re = 1 - ‖z‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp [Complex.mul_re]
          ring
        rw [hnum_re]
      simp only [Set.mem_setOf_eq, hre_id]
      exact div_pos (by nlinarith [norm_nonneg z]) hden_pos
    · intro z₁ hz₁ z₂ hz₂ heq
      rw [mem_ball_zero_iff] at hz₁ hz₂
      have h1 : 1 - z₁ ≠ 0 := by
        intro h0; have : z₁ = 1 := by linear_combination -h0
        rw [this, norm_one] at hz₁; exact lt_irrefl 1 hz₁
      have h2 : 1 - z₂ ≠ 0 := by
        intro h0; have : z₂ = 1 := by linear_combination -h0
        rw [this, norm_one] at hz₂; exact lt_irrefl 1 hz₂
      dsimp [cayleyMap] at heq
      rw [div_eq_div_iff h1 h2] at heq
      linear_combination heq / 2
    · intro w hw
      simp only [Set.mem_setOf_eq] at hw
      have hw1 : w + 1 ≠ 0 := by
        intro h0
        have := congrArg Complex.re h0
        simp at this
        linarith
      let z : ℂ := (w - 1) / (w + 1)
      have hz_ball : z ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff]
        dsimp [z]
        rw [norm_div]
        have hpos_den : 0 < ‖w + 1‖ := norm_pos_iff.mpr hw1
        rw [div_lt_one hpos_den]
        have hsq_diff : ‖w + 1‖ ^ 2 - ‖w - 1‖ ^ 2 = 4 * w.re := by
          rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
          simp
          ring
        nlinarith [norm_nonneg (w - 1)]
      refine ⟨z, hz_ball, ?_⟩
      dsimp [cayleyMap, z]
      have hz1 : 1 - (w - 1) / (w + 1) ≠ 0 := by
        have : 1 - (w - 1) / (w + 1) = 2 / (w + 1) := by field_simp [hw1]; ring
        rw [this]
        exact div_ne_zero two_ne_zero hw1
      field_simp [hw1, hz1]
      ring

/-- Open half-plane in `ℂ`: `{w : ℂ | c < Re(u * w)}` for `u ≠ 0` and `c ∈ ℝ`. -/
def IsOpenHalfPlane (H : Set ℂ) : Prop :=
  ∃ (u : ℂ) (c : ℝ), u ≠ 0 ∧ H = {w : ℂ | c < (u * w).re}

/-- **14.3 (Every open disc is conformally equivalent to every open half-plane, RCA p. 280):** -/
theorem openDisc_conformally_equiv_openHalfPlane {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    {H : Set ℂ} (hH : IsOpenHalfPlane H) :
    ∃ φ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn φ (ball z₀ r) ∧ BijOn φ (ball z₀ r) H := by
  rcases hH with ⟨u, c, hu, rfl⟩
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  obtain ⟨_, _, _, _, _, hcay_holo, hcay_bij⟩ := cayleyMap_props
  let φ : ℂ → ℂ := fun z => (cayleyMap ((z - z₀) / (r : ℂ)) + (c : ℂ)) / u
  have hlin_maps : MapsTo (fun z : ℂ => (z - z₀) / (r : ℂ)) (ball z₀ r) (ball (0 : ℂ) 1) := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact (div_lt_one hr).mpr hz
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hd_in : DifferentiableAt ℂ (fun w : ℂ => (w - z₀) / (r : ℂ)) z :=
      (differentiableAt_id.sub (differentiableAt_const z₀)).div_const (r : ℂ)
    have hcay_z : DifferentiableAt ℂ cayleyMap ((z - z₀) / (r : ℂ)) :=
      hcay_holo ((z - z₀) / (r : ℂ)) (hlin_maps hz)
    have hd_cay : DifferentiableAt ℂ (cayleyMap ∘ fun w : ℂ => (w - z₀) / (r : ℂ)) z :=
      hcay_z.comp z hd_in
    exact (hd_cay.add (differentiableAt_const (c : ℂ))).div_const u
  · intro z hz
    have hw := hcay_bij.mapsTo (hlin_maps hz)
    simp only [Set.mem_setOf_eq] at hw ⊢
    dsimp [φ]
    rw [mul_div_cancel₀ _ hu, Complex.add_re, Complex.ofReal_re]
    linarith
  · intro z₁ hz₁ z₂ hz₂ heq
    dsimp [φ] at heq
    have h1 : cayleyMap ((z₁ - z₀) / (r : ℂ)) + (c : ℂ) =
        cayleyMap ((z₂ - z₀) / (r : ℂ)) + (c : ℂ) :=
      (div_left_inj' hu).mp heq
    have h2 : cayleyMap ((z₁ - z₀) / (r : ℂ)) = cayleyMap ((z₂ - z₀) / (r : ℂ)) :=
      add_right_cancel h1
    have h3 : (z₁ - z₀) / (r : ℂ) = (z₂ - z₀) / (r : ℂ) :=
      hcay_bij.injOn (hlin_maps hz₁) (hlin_maps hz₂) h2
    have h4 : z₁ - z₀ = z₂ - z₀ := (div_left_inj' hr_ne).mp h3
    exact sub_left_injective h4
  · intro w hw
    simp only [Set.mem_setOf_eq] at hw
    let t : ℂ := u * w - (c : ℂ)
    have ht : t ∈ {ζ : ℂ | 0 < ζ.re} := by
      simp only [t, Set.mem_setOf_eq, Complex.sub_re, Complex.ofReal_re]
      exact sub_pos.mpr hw
    obtain ⟨ζ, hζ_ball, hζ_eq⟩ := hcay_bij.surjOn ht
    let z : ℂ := z₀ + (r : ℂ) * ζ
    have hz_ball : z ∈ ball z₀ r := by
      rw [mem_ball, dist_eq_norm]
      have : z - z₀ = (r : ℂ) * ζ := by dsimp [z]; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      have hζ_lt : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ_ball
      nlinarith
    refine ⟨z, hz_ball, ?_⟩
    dsimp [φ, z]
    have hsimp : (z₀ + (r : ℂ) * ζ - z₀) / (r : ℂ) = ζ := by
      field_simp [hr_ne]; ring
    rw [hsimp, hζ_eq]
    dsimp [t]
    field_simp [hu]
    ring

/-- **Node 14.3 (Linear fractional / Möbius transformations, RCA pp. 279–281):**
Combined summary of the numbered discussion `14.3`:
1. Every `M(z) = (a z + b) / (c z + d)` with `a d - b c ≠ 0` is a bijection `S² → S²` and a
   composition of translations, rotations, positive dilations, and inversion;
2. Generalized circles (`α z z̄ + β z + β̄ z̄ + γ = 0`, `‖β‖² > α γ`) are precisely Euclidean circles
   and straight lines `∪ {∞}`, correspond via stereographic projection to nondegenerate planar
   sections of `S² ⊆ ℝ³` (note: Rudin omits the proof of this stereographic characterization in
   print; `theorem14_3_stereographic_circle_iff` proves it in full), and are preserved and acted on
   transitively by Möbius transformations;
3. Unique three-point interpolation on `S²`, with finite formula
   `(b - c)(z - a) / ((b - a)(z - c))` carrying `(a, b, c) ↦ (0, 1, ∞)`;
4. Explicit Cayley map `(1 + z) / (1 - z)` bijecting `U` holomorphically onto `{w | Re w > 0}` and
   carrying `(-1, 0, 1) ↦ (0, 1, ∞)`, and conformal equivalence of every open disc with every open
   half-plane. -/
theorem theorem14_3 :
    (∀ {a b c d : ℂ}, a * d - b * c ≠ 0 →
      Function.Bijective (moebiusMap a b c d) ∧
      GeneratedByElementaryMoebius (moebiusMap a b c d) ∧
      ∀ {S : Set RiemannSphere}, IsGeneralizedCircle S →
        IsGeneralizedCircle (moebiusMap a b c d '' S)) ∧
    (∀ S : Set RiemannSphere,
      (IsGeneralizedCircle S ↔
        (∃ (z₀ : ℂ) (r : ℝ), 0 < r ∧ S = ((↑) : ℂ → RiemannSphere) '' sphere z₀ r) ∨
        (∃ (β : ℂ) (γ : ℝ), β ≠ 0 ∧
          S = insert ∞ (((↑) : ℂ → RiemannSphere) '' {z : ℂ | 2 * (β * z).re + γ = 0}))) ∧
      (IsGeneralizedCircle S ↔
        ∃ (n : SphereAmbient) (d : ℝ), d ^ 2 < ‖n‖ ^ 2 ∧
          bookSphereHomeomorph '' S =
            {x : sphere (0 : SphereAmbient) 1 | @inner ℝ SphereAmbient _ n x.1 = d})) ∧
    (∀ {p₁ p₂ p₃ q₁ q₂ q₃ : RiemannSphere},
      p₁ ≠ p₂ → p₂ ≠ p₃ → p₁ ≠ p₃ → q₁ ≠ q₂ → q₂ ≠ q₃ → q₁ ≠ q₃ →
      (∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
        moebiusMap a b c d p₁ = q₁ ∧ moebiusMap a b c d p₂ = q₂ ∧
        moebiusMap a b c d p₃ = q₃) ∧
      (∀ (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℂ),
        a₁ * d₁ - b₁ * c₁ ≠ 0 → a₂ * d₂ - b₂ * c₂ ≠ 0 →
        moebiusMap a₁ b₁ c₁ d₁ p₁ = q₁ → moebiusMap a₁ b₁ c₁ d₁ p₂ = q₂ →
          moebiusMap a₁ b₁ c₁ d₁ p₃ = q₃ →
        moebiusMap a₂ b₂ c₂ d₂ p₁ = q₁ → moebiusMap a₂ b₂ c₂ d₂ p₂ = q₂ →
          moebiusMap a₂ b₂ c₂ d₂ p₃ = q₃ →
        ∀ p : RiemannSphere, moebiusMap a₁ b₁ c₁ d₁ p = moebiusMap a₂ b₂ c₂ d₂ p)) ∧
    (∀ {S₁ S₂ : Set RiemannSphere}, IsGeneralizedCircle S₁ → IsGeneralizedCircle S₂ →
      ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ moebiusMap a b c d '' S₁ = S₂) ∧
    (RudinRCA.Chapter10.HolomorphicOn cayleyMap (ball (0 : ℂ) 1) ∧
      BijOn cayleyMap (ball (0 : ℂ) 1) {w : ℂ | 0 < w.re} ∧
      moebiusMap 1 1 (-1) 1 ((-1 : ℂ) : RiemannSphere) = (0 : ℂ) ∧
      moebiusMap 1 1 (-1) 1 ((0 : ℂ) : RiemannSphere) = (1 : ℂ) ∧
      moebiusMap 1 1 (-1) 1 ((1 : ℂ) : RiemannSphere) = ∞) ∧
    (∀ {z₀ : ℂ} {r : ℝ} {H : Set ℂ}, 0 < r → IsOpenHalfPlane H →
      ∃ φ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn φ (ball z₀ r) ∧ BijOn φ (ball z₀ r) H) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b c d hdet
    exact ⟨moebiusMap_bijective hdet, moebiusMap_generatedByElementary hdet,
      fun hS => isGeneralizedCircle_image_moebiusMap hdet hS⟩
  · intro S
    exact ⟨isGeneralizedCircle_iff_circle_or_line S, theorem14_3_stereographic_circle_iff S⟩
  · intro p₁ p₂ p₃ q₁ q₂ q₃ hp12 hp23 hp13 hq12 hq23 hq13
    exact moebius_unique_three_point_interpolation hp12 hp23 hp13 hq12 hq23 hq13
  · intro S₁ S₂ hS₁ hS₂
    exact moebius_maps_generalizedCircle_to_generalizedCircle hS₁ hS₂
  · obtain ⟨_, hm1, hm2, hm3, _, hcay_holo, hcay_bij⟩ := cayleyMap_props
    exact ⟨hcay_holo, hcay_bij, hm1, hm2, hm3⟩
  · intro z₀ r H hr hH
    exact openDisc_conformally_equiv_openHalfPlane hr hH


/-! ### Node 14.4: Circular Schwarz Reflection -/

/-- **14.4 (Transfer map `ψ(z) = (z - i) / (z + i)` from upper half-plane to `U`, RCA p. 281):** -/
def upperHalfPlaneToUnitBall (z : ℂ) : ℂ :=
  (z - Complex.I) / (z + Complex.I)

theorem upperHalfPlaneToUnitBall_props :
    RudinRCA.Chapter10.HolomorphicOn upperHalfPlaneToUnitBall {z : ℂ | z ≠ -Complex.I} ∧
    BijOn upperHalfPlaneToUnitBall {z : ℂ | 0 < z.im} (ball (0 : ℂ) 1) ∧
    BijOn upperHalfPlaneToUnitBall {z : ℂ | z.im = 0} (sphere (0 : ℂ) 1 \ {1}) ∧
    (∀ z : ℂ, z ≠ Complex.I → z ≠ -Complex.I →
      upperHalfPlaneToUnitBall (starRingEnd ℂ z) =
        (starRingEnd ℂ (upperHalfPlaneToUnitBall z))⁻¹) := by
  have hnorm_diff : ∀ z : ℂ, ‖z + Complex.I‖ ^ 2 - ‖z - Complex.I‖ ^ 2 = 4 * z.im := by
    intro z
    repeat rw [Complex.sq_norm]
    repeat rw [Complex.normSq_apply]
    simp
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    simp only [Set.mem_setOf_eq] at hz
    have hden : z + Complex.I ≠ 0 := fun h0 => hz (eq_neg_of_add_eq_zero_left h0)
    exact (differentiableAt_id.sub (differentiableAt_const Complex.I)).div
      (differentiableAt_id.add (differentiableAt_const Complex.I)) hden
  · refine ⟨?_, ?_, ?_⟩
    · intro z hz
      simp only [Set.mem_setOf_eq] at hz
      have hden : z + Complex.I ≠ 0 := by
        intro h0
        have := congrArg Complex.im h0
        simp at this
        linarith
      rw [mem_ball_zero_iff, upperHalfPlaneToUnitBall, norm_div,
        div_lt_one (norm_pos_iff.mpr hden)]
      nlinarith [hnorm_diff z, norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I)]
    · intro z₁ hz₁ z₂ hz₂ heq
      simp only [Set.mem_setOf_eq] at hz₁ hz₂
      have hd₁ : z₁ + Complex.I ≠ 0 := by
        intro h0; have := congrArg Complex.im h0; simp at this; linarith
      have hd₂ : z₂ + Complex.I ≠ 0 := by
        intro h0; have := congrArg Complex.im h0; simp at this; linarith
      dsimp [upperHalfPlaneToUnitBall] at heq
      rw [div_eq_div_iff hd₁ hd₂] at heq
      have hsub : (2 : ℂ) * Complex.I * (z₁ - z₂) = 0 := by linear_combination heq
      have h2I : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
      exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left h2I)
    · intro w hw
      rw [mem_ball_zero_iff] at hw
      have hw1 : 1 - w ≠ 0 := by
        intro h0
        have heq : w = 1 := by linear_combination -h0
        rw [heq, norm_one] at hw
        exact lt_irrefl 1 hw
      let z : ℂ := Complex.I * (1 + w) / (1 - w)
      have hz_im : 0 < z.im := by
        dsimp [z]
        have hcw := cayleyMap_props.2.2.2.2.2.2.mapsTo (mem_ball_zero_iff.mpr hw)
        simp only [Set.mem_setOf_eq] at hcw
        have heq_z : Complex.I * (1 + w) / (1 - w) = Complex.I * cayleyMap w := by
          dsimp [cayleyMap]; ring
        rw [heq_z, Complex.I_mul_im]
        exact hcw
      refine ⟨z, hz_im, ?_⟩
      have hd : z + Complex.I ≠ 0 := by
        intro h0; have := congrArg Complex.im h0; simp at this; linarith
      dsimp [upperHalfPlaneToUnitBall, z]
      field_simp [hw1, hd]
      ring
  · refine ⟨?_, ?_, ?_⟩
    · intro z hz
      simp only [Set.mem_setOf_eq] at hz
      have hd : z + Complex.I ≠ 0 := by
        intro h0; have := congrArg Complex.im h0; simp [hz] at this
      refine ⟨?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, upperHalfPlaneToUnitBall, norm_div]
        have hsq : ‖z - Complex.I‖ ^ 2 = ‖z + Complex.I‖ ^ 2 := by
          linarith [hnorm_diff z, hz]
        have heq_norm : ‖z - Complex.I‖ = ‖z + Complex.I‖ := by
          nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I)]
        rw [heq_norm, div_self (norm_pos_iff.mpr hd).ne']
      · simp only [Set.mem_singleton_iff, upperHalfPlaneToUnitBall]
        intro h1
        rw [div_eq_one_iff_eq hd] at h1
        have h2I : (-2 : ℂ) * Complex.I = 0 := by linear_combination h1
        exact mul_ne_zero (by norm_num) Complex.I_ne_zero h2I
    · intro z₁ hz₁ z₂ hz₂ heq
      simp only [Set.mem_setOf_eq] at hz₁ hz₂
      have hd₁ : z₁ + Complex.I ≠ 0 := by
        intro h0; have := congrArg Complex.im h0; simp [hz₁] at this
      have hd₂ : z₂ + Complex.I ≠ 0 := by
        intro h0; have := congrArg Complex.im h0; simp [hz₂] at this
      dsimp [upperHalfPlaneToUnitBall] at heq
      rw [div_eq_div_iff hd₁ hd₂] at heq
      have hsub : (2 : ℂ) * Complex.I * (z₁ - z₂) = 0 := by linear_combination heq
      exact sub_eq_zero.mp
        ((mul_eq_zero.mp hsub).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero))
    · rintro w ⟨hw_sph, hw_ne1⟩
      rw [mem_sphere_zero_iff_norm] at hw_sph
      simp only [Set.mem_singleton_iff] at hw_ne1
      have hw1 : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw_ne1)
      let z : ℂ := Complex.I * (1 + w) / (1 - w)
      have hz_im : z.im = 0 := by
        have hcay_re : ((1 + w) / (1 - w)).re = 0 := by
          have hden_pos : 0 < ‖1 - w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw1)
          have h1 : (1 + w) / (1 - w) =
              ((1 + w) * starRingEnd ℂ (1 - w)) / ((‖1 - w‖ ^ 2 : ℝ) : ℂ) := by
            rw [div_eq_iff hw1]
            have hconj : (1 - w) * starRingEnd ℂ (1 - w) = ((‖1 - w‖ ^ 2 : ℝ) : ℂ) := by
              rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
            have hden_c : ((‖1 - w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hden_pos.ne'
            field_simp [hden_c]
            linear_combination -(1 + w) * hconj
          rw [h1, div_ofReal_re]
          have hnum : ((1 + w) * starRingEnd ℂ (1 - w)).re = 1 - ‖w‖ ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]
            simp [Complex.mul_re]; ring
          rw [hnum, hw_sph]; ring
        have heq_z : z = Complex.I * ((1 + w) / (1 - w)) := by dsimp [z]; ring
        rw [heq_z, Complex.I_mul_im, hcay_re]
      refine ⟨z, hz_im, ?_⟩
      have hd : z + Complex.I ≠ 0 := by
        intro h0; have := congrArg Complex.im h0; simp [hz_im] at this
      dsimp [upperHalfPlaneToUnitBall, z]
      field_simp [hw1, hd]
      ring
  · intro z hzI hznI
    dsimp [upperHalfPlaneToUnitBall]
    simp only [map_div₀, map_sub, map_add, Complex.conj_I, sub_neg_eq_add, inv_div]
    rfl

/-- Helper: `w ↦ conj (f (conj w))` has complex derivative `conj f'(conj w₀)` when `f` has
complex derivative at `conj w₀`. -/
theorem hasDerivAt_conj_comp_conj {f : ℂ → ℂ} {w₀ d : ℂ}
    (hd : HasDerivAt f d (starRingEnd ℂ w₀)) :
    HasDerivAt (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) (starRingEnd ℂ d) w₀ := by
  rw [hasDerivAt_iff_tendsto_slope] at hd ⊢
  have hcont_conj : Continuous (starRingEnd ℂ) := Complex.continuous_conj
  have hmap_nhds : Tendsto (starRingEnd ℂ) (𝓝[≠] w₀) (𝓝[≠] (starRingEnd ℂ w₀)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hcont_conj.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact fun heq => hw (RingHom.injective (starRingEnd ℂ) heq)
  have h1 := (hcont_conj.continuousAt.tendsto.comp hd).comp hmap_nhds
  refine h1.congr fun w => ?_
  simp only [Function.comp_def, slope_def_field, map_div₀, map_sub,
    RingHomCompTriple.comp_apply, RingHom.id_apply]

/-- **14.4 (Reflected function across the unit circle, RCA p. 281):** -/
def circularSchwarzReflection (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if ‖z‖ ≤ 1 then f z else starRingEnd ℂ (f (starRingEnd ℂ z)⁻¹)

/-- **Theorem 14.4 (Circular Schwarz Reflection across an arc of `T`, RCA p. 281):**
Let `W ⊆ {z : ℂ | z ≠ 0}` be an open set symmetric under unit-circle inversion
(`∀ z ∈ W, (conj z)⁻¹ ∈ W`), and set `Ω_in := W ∩ U`, `L := W ∩ T`, `Ω_out := W ∩ {z | 1 < ‖z‖}`
(making explicit the reflected open neighborhood of the unit-circle boundary arc `L`, per
`SCOPING-F.md` Caution 2). If `f` is holomorphic on `Ω_in`, continuous on `Ω_in ∪ L`, and real on
`L`, then `F := circularSchwarzReflection f` is holomorphic throughout `W`, agrees with `f` on
`Ω_in ∪ L`, satisfies `F(z) = conj(f(1 / conj z))` on `Ω_out` and `F(1 / conj z) = conj(F(z))` on
`W`, and is the unique holomorphic extension of `f|_{Ω_in}` when `W` is preconnected and `Ω_in` is
nonempty. -/
theorem theorem14_4 {W : Set ℂ} (hW_open : IsOpen W) (hW_nz : ∀ z ∈ W, z ≠ 0)
    (hW_symm : ∀ z ∈ W, (starRingEnd ℂ z)⁻¹ ∈ W)
    {f : ℂ → ℂ}
    (hf_holo : RudinRCA.Chapter10.HolomorphicOn f (W ∩ ball (0 : ℂ) 1))
    (hf_cont : ContinuousOn f ((W ∩ ball (0 : ℂ) 1) ∪ (W ∩ sphere (0 : ℂ) 1)))
    (hf_real : ∀ z ∈ W ∩ sphere (0 : ℂ) 1, (f z).im = 0) :
    let Ω_in := W ∩ ball (0 : ℂ) 1
    let L := W ∩ sphere (0 : ℂ) 1
    let Ω_out := W ∩ {z : ℂ | 1 < ‖z‖}
    let F := circularSchwarzReflection f
    RudinRCA.Chapter10.HolomorphicOn F W ∧
      (∀ z ∈ Ω_in ∪ L, F z = f z) ∧
      (∀ z ∈ Ω_out, F z = starRingEnd ℂ (f (starRingEnd ℂ z)⁻¹)) ∧
      (∀ z ∈ W, F ((starRingEnd ℂ z)⁻¹) = starRingEnd ℂ (F z)) ∧
      (IsPreconnected W → Ω_in.Nonempty →
        ∀ G : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn G W →
          (∀ z ∈ Ω_in, G z = f z) → ∀ z ∈ W, G z = F z) := by
  intro Ω_in L Ω_out F
  have hF_in_L : ∀ z ∈ Ω_in ∪ L, F z = f z := by
    rintro z (⟨_, hz⟩ | ⟨_, hz⟩)
    · simp [F, circularSchwarzReflection, (mem_ball_zero_iff.mp hz).le]
    · simp [F, circularSchwarzReflection, (mem_sphere_zero_iff_norm.mp hz).le]
  have hF_out : ∀ z ∈ Ω_out, F z = starRingEnd ℂ (f (starRingEnd ℂ z)⁻¹) := by
    rintro z ⟨_, (hz : 1 < ‖z‖)⟩
    simp [F, circularSchwarzReflection, not_le.mpr hz]
  have hF_symm : ∀ z ∈ W, F ((starRingEnd ℂ z)⁻¹) = starRingEnd ℂ (F z) := by
    intro z hz
    have hz_ne : z ≠ 0 := hW_nz z hz
    have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
    have hinv_norm : ‖(starRingEnd ℂ z)⁻¹‖ = ‖z‖⁻¹ := by
      rw [norm_inv, RingHomIsometric.norm_map]
    rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
    · have hgt' : 1 < ‖(starRingEnd ℂ z)⁻¹‖ := by
        rw [hinv_norm]; exact (one_lt_inv₀ hnorm_pos).mpr hlt
      have hinvol : (starRingEnd ℂ (starRingEnd ℂ z)⁻¹)⁻¹ = z := by
        rw [map_inv₀, RingHomCompTriple.comp_apply, RingHom.id_apply, inv_inv]
      dsimp only [F, circularSchwarzReflection]
      rw [if_neg (not_le.mpr hgt'), if_pos hlt.le, hinvol]
    · have heq' : ‖(starRingEnd ℂ z)⁻¹‖ = 1 := by rw [hinv_norm, heq, inv_one]
      have hzL : z ∈ L := ⟨hz, mem_sphere_zero_iff_norm.mpr heq⟩
      have hinv_eq : (starRingEnd ℂ z)⁻¹ = z := by
        apply inv_eq_of_mul_eq_one_right
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, heq, one_pow, Complex.ofReal_one]
      dsimp only [F, circularSchwarzReflection]
      rw [if_pos heq'.le, if_pos heq.le, hinv_eq]
      exact (Complex.conj_eq_iff_im.mpr (hf_real z hzL)).symm
    · have hlt' : ‖(starRingEnd ℂ z)⁻¹‖ < 1 := by
        rw [hinv_norm]; exact inv_lt_one_of_one_lt₀ hgt
      dsimp only [F, circularSchwarzReflection]
      rw [if_pos hlt'.le, if_neg (not_le.mpr hgt), RingHomCompTriple.comp_apply, RingHom.id_apply]
  have hF_holo : RudinRCA.Chapter10.HolomorphicOn F W := by
    intro z₀ hz₀
    rcases lt_trichotomy ‖z₀‖ 1 with hlt | heq | hgt
    · -- Inside `U`: `F` agrees with `f` on `W ∩ ball 0 1`
      have hopen_in : IsOpen Ω_in := hW_open.inter isOpen_ball
      have hev : F =ᶠ[𝓝 z₀] f := by
        filter_upwards [hopen_in.mem_nhds ⟨hz₀, mem_ball_zero_iff.mpr hlt⟩] with z hz
        exact hF_in_L z (Or.inl hz)
      exact (hf_holo z₀ ⟨hz₀, mem_ball_zero_iff.mpr hlt⟩).congr_of_eventuallyEq hev
    · -- On the boundary arc `L`: transfer via `φ(ζ) = -z₀ * ψ(ζ)` to `Chapter11.theorem11_14`
      have hz₀_ne : z₀ ≠ 0 := by
        intro h0; rw [h0, norm_zero] at heq; exact zero_ne_one heq
      obtain ⟨hψ_holo, hψ_pos, hψ_real, hψ_symm⟩ := upperHalfPlaneToUnitBall_props
      let φ : ℂ → ℂ := fun ζ => -z₀ * upperHalfPlaneToUnitBall ζ
      let φ_inv : ℂ → ℂ := fun z => Complex.I * (z₀ - z) / (z₀ + z)
      have hφ0 : φ 0 = z₀ := by
        dsimp [φ, upperHalfPlaneToUnitBall]
        rw [zero_sub, zero_add, neg_div_self Complex.I_ne_zero]
        ring
      have hφ_holo_ball : RudinRCA.Chapter10.HolomorphicOn φ (ball (0 : ℂ) 1) := by
        intro ζ hζ
        have hζ_ne : ζ ≠ -Complex.I := by
          intro h; rw [h, mem_ball_zero_iff, norm_neg, Complex.norm_I] at hζ
          exact lt_irrefl 1 hζ
        exact (hψ_holo ζ hζ_ne).const_mul (-z₀)
      have hφ_cont0 : ContinuousAt φ 0 :=
        (hφ_holo_ball 0 (Metric.mem_ball_self zero_lt_one)).continuousAt
      have hW_nhds : φ ⁻¹' W ∈ 𝓝 (0 : ℂ) :=
        hφ_cont0.preimage_mem_nhds (hφ0.symm ▸ hW_open.mem_nhds hz₀)
      obtain ⟨δ₁, hδ₁, hball_sub⟩ := Metric.mem_nhds_iff.mp
        (Filter.inter_mem (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one) hW_nhds)
      let U_δ : Set ℂ := ball (0 : ℂ) δ₁
      have hU_open : IsOpen U_δ := isOpen_ball
      have hU_symm : ∀ ζ ∈ U_δ, starRingEnd ℂ ζ ∈ U_δ := by
        intro ζ hζ
        rw [mem_ball_zero_iff] at hζ ⊢
        rwa [RingHomIsometric.norm_map]
      have hconj_z₀_inv : (-starRingEnd ℂ z₀)⁻¹ = -z₀ := by
        apply inv_eq_of_mul_eq_one_right
        rw [neg_mul_neg, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          heq, one_pow, Complex.ofReal_one]
      have hφ_symm : ∀ ζ ∈ ball (0 : ℂ) 1,
          φ (starRingEnd ℂ ζ) = (starRingEnd ℂ (φ ζ))⁻¹ := by
        intro ζ hζ
        have hζ_I : ζ ≠ Complex.I := by
          intro h; rw [h, mem_ball_zero_iff, Complex.norm_I] at hζ; exact lt_irrefl 1 hζ
        have hζ_nI : ζ ≠ -Complex.I := by
          intro h; rw [h, mem_ball_zero_iff, norm_neg, Complex.norm_I] at hζ; exact lt_irrefl 1 hζ
        dsimp [φ]
        rw [hψ_symm ζ hζ_I hζ_nI, map_mul, map_neg, mul_inv, hconj_z₀_inv]
      have hφ_maps_pos : ∀ ζ ∈ U_δ, 0 < ζ.im → φ ζ ∈ Ω_in := by
        intro ζ hζ hpos
        refine ⟨(hball_sub hζ).2, ?_⟩
        rw [mem_ball_zero_iff]
        dsimp [φ]
        rw [norm_mul, norm_neg, heq, one_mul]
        exact mem_ball_zero_iff.mp (hψ_pos.mapsTo hpos)
      have hφ_maps_real : ∀ x ∈ U_δ, x.im = 0 → φ x ∈ L := by
        intro x hx hxim
        refine ⟨(hball_sub hx).2, ?_⟩
        rw [mem_sphere_zero_iff_norm]
        dsimp [φ]
        rw [norm_mul, norm_neg, heq, one_mul]
        exact mem_sphere_zero_iff_norm.mp (hψ_real.mapsTo hxim).1
      let g : ℂ → ℂ := fun ζ => f (φ ζ)
      have hg_holo : DifferentiableOn ℂ g {ζ ∈ U_δ | 0 < ζ.im} := by
        intro ζ hζ
        exact ((hf_holo (φ ζ) (hφ_maps_pos ζ hζ.1 hζ.2)).comp ζ
          (hφ_holo_ball ζ (hball_sub hζ.1).1)).differentiableWithinAt
      have hg_lim : ∀ x ∈ U_δ, x.im = 0 →
          Tendsto g (𝓝[{ζ ∈ U_δ | 0 < ζ.im}] x) (𝓝 (f (φ x))) := by
        intro x hx hxim
        have hφx_L : φ x ∈ L := hφ_maps_real x hx hxim
        have hφ_at_x : ContinuousAt φ x := (hφ_holo_ball x (hball_sub hx).1).continuousAt
        have hφ_tendsto : Tendsto φ (𝓝[{ζ ∈ U_δ | 0 < ζ.im}] x) (𝓝[Ω_in ∪ L] (φ x)) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨hφ_at_x.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
          filter_upwards [self_mem_nhdsWithin] with ζ hζ
          exact Or.inl (hφ_maps_pos ζ hζ.1 hζ.2)
        exact (hf_cont.continuousWithinAt (Or.inr hφx_L)).tendsto.comp hφ_tendsto
      have hg_im : ∀ x ∈ U_δ, x.im = 0 →
          Tendsto (fun ζ => (g ζ).im) (𝓝[{ζ ∈ U_δ | 0 < ζ.im}] x) (𝓝 0) := by
        intro x hx hxim
        have hlim := Complex.continuous_im.continuousAt.tendsto.comp (hg_lim x hx hxim)
        rwa [Function.comp_def, hf_real (φ x) (hφ_maps_real x hx hxim)] at hlim
      obtain ⟨hG_diff, hG_pos, hG_neg, _, _, _⟩ :=
        RudinRCA.Chapter11.theorem11_14 hU_open hU_symm hg_holo hg_im
      let G_δ := RudinRCA.Chapter11.schwarzReflection g U_δ
      have hG_eq_Fφ : ∀ ζ ∈ U_δ, G_δ ζ = F (φ ζ) := by
        intro ζ hζ
        rcases lt_trichotomy ζ.im 0 with hneg | hzero | hpos
        · have hc_pos : 0 < (starRingEnd ℂ ζ).im := by simp [hneg]
          have hc_in : φ (starRingEnd ℂ ζ) ∈ Ω_in := hφ_maps_pos _ (hU_symm ζ hζ) hc_pos
          have hsym := hφ_symm ζ (hball_sub hζ).1
          have hφ_out : φ ζ ∈ Ω_out := by
            refine ⟨(hball_sub hζ).2, ?_⟩
            simp only [Set.mem_setOf_eq]
            have hlt_c : ‖(starRingEnd ℂ (φ ζ))⁻¹‖ < 1 := by
              rw [← hsym]; exact mem_ball_zero_iff.mp hc_in.2
            have hφ_nz : φ ζ ≠ 0 := hW_nz (φ ζ) (hball_sub hζ).2
            rw [norm_inv, RingHomIsometric.norm_map] at hlt_c
            exact (inv_lt_one₀ (norm_pos_iff.mpr hφ_nz)).mp hlt_c
          dsimp only [G_δ]
          rw [hG_neg ζ ⟨hζ, hneg⟩, hF_out (φ ζ) hφ_out, ← hsym]
        · have hne_bot : (𝓝[{ζ ∈ U_δ | 0 < ζ.im}] ζ).NeBot := by
            rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
            intro ε hε
            have hζ_norm : ‖ζ‖ < δ₁ := mem_ball_zero_iff.mp hζ
            let t : ℝ := min (ε / 2) ((δ₁ - ‖ζ‖) / 2)
            have ht_pos : 0 < t := lt_min (half_pos hε) (half_pos (sub_pos.mpr hζ_norm))
            let w : ℂ := ζ + (t : ℂ) * Complex.I
            refine ⟨w, ⟨?_, ?_⟩, ?_⟩
            · rw [mem_ball_zero_iff]
              have ht_le : t ≤ (δ₁ - ‖ζ‖) / 2 := min_le_right _ _
              have hw_norm : ‖w‖ ≤ ‖ζ‖ + t := by
                calc
                  ‖w‖ ≤ ‖ζ‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
                  _ = ‖ζ‖ + t := by simp [Complex.norm_real, abs_of_pos ht_pos]
              linarith
            · simp [w, hzero, ht_pos]
            · rw [dist_eq_norm]
              have : ζ - w = -((t : ℂ) * Complex.I) := by dsimp [w]; ring
              rw [this, norm_neg, norm_mul, Complex.norm_I, mul_one,
                Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
              exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
          have hG_at_x : G_δ ζ = limUnder (𝓝[{w ∈ U_δ | 0 < w.im}] ζ) g := by
            dsimp [G_δ, RudinRCA.Chapter11.schwarzReflection]
            simp [hzero]
          rw [hG_at_x, (hg_lim ζ hζ hzero).limUnder_eq,
            hF_in_L (φ ζ) (Or.inr (hφ_maps_real ζ hζ hzero))]
        · dsimp only [G_δ]
          rw [hG_pos ζ ⟨hζ, hpos⟩, hF_in_L (φ ζ) (Or.inl (hφ_maps_pos ζ hζ hpos))]
      have h2z₀ : z₀ + z₀ ≠ 0 := by
        have : z₀ + z₀ = 2 * z₀ := (two_mul z₀).symm
        rw [this]
        exact mul_ne_zero two_ne_zero hz₀_ne
      have hd_φinv : DifferentiableAt ℂ φ_inv z₀ :=
        ((differentiableAt_const z₀ |>.sub differentiableAt_id).const_mul Complex.I).div
          (differentiableAt_const z₀ |>.add differentiableAt_id) h2z₀
      have hφinv_z₀ : φ_inv z₀ = 0 := by simp [φ_inv]
      have hev_F : F =ᶠ[𝓝 z₀] fun z => G_δ (φ_inv z) := by
        have hnhds1 : {z : ℂ | z₀ + z ≠ 0} ∈ 𝓝 z₀ :=
          (isOpen_compl_singleton.preimage (continuous_const.add continuous_id)).mem_nhds h2z₀
        have hnhds2 : φ_inv ⁻¹' U_δ ∈ 𝓝 z₀ :=
          hd_φinv.continuousAt.preimage_mem_nhds (hφinv_z₀.symm ▸ hU_open.mem_nhds (Metric.mem_ball_self hδ₁))
        filter_upwards [Filter.inter_mem hnhds1 hnhds2] with z ⟨hz_sum, hz_in⟩
        have hz_sum' : z₀ + z ≠ 0 := hz_sum
        rw [hG_eq_Fφ (φ_inv z) hz_in]
        have hright : φ (φ_inv z) = z := by
          have hnum : φ_inv z - Complex.I = (-2 * Complex.I * z) / (z₀ + z) := by
            dsimp [φ_inv]; field_simp [hz_sum']; ring
          have hden : φ_inv z + Complex.I = (2 * Complex.I * z₀) / (z₀ + z) := by
            dsimp [φ_inv]; field_simp [hz_sum']; ring
          dsimp only [φ, upperHalfPlaneToUnitBall]
          rw [hnum, hden, div_div_div_cancel_right₀ hz_sum']
          field_simp [hz₀_ne, Complex.I_ne_zero]
        rw [hright]
      have hd_G0 : DifferentiableAt ℂ G_δ (φ_inv z₀) := by
        rw [hφinv_z₀]
        exact hG_diff.differentiableAt (hU_open.mem_nhds (Metric.mem_ball_self hδ₁))
      exact (hd_G0.comp z₀ hd_φinv).congr_of_eventuallyEq hev_F
    · -- Outside `U`: `F(z) = conj (f (conj (z⁻¹)))`
      have hz₀_ne : z₀ ≠ 0 := hW_nz z₀ hz₀
      have hw₀_in : (starRingEnd ℂ z₀)⁻¹ ∈ Ω_in := by
        refine ⟨hW_symm z₀ hz₀, ?_⟩
        rw [mem_ball_zero_iff, norm_inv, RingHomIsometric.norm_map]
        exact inv_lt_one_of_one_lt₀ hgt
      have hconj_inv : starRingEnd ℂ (z₀⁻¹) = (starRingEnd ℂ z₀)⁻¹ := map_inv₀ _ _
      have hd_f : HasDerivAt f (deriv f (starRingEnd ℂ (z₀⁻¹))) (starRingEnd ℂ (z₀⁻¹)) := by
        rw [hconj_inv]
        exact (hf_holo _ hw₀_in).hasDerivAt
      have hd_cc := hasDerivAt_conj_comp_conj hd_f
      have hd_out := (hd_cc.differentiableAt.comp z₀ (differentiableAt_inv hz₀_ne))
      have hopen_out : IsOpen Ω_out :=
        hW_open.inter (isOpen_lt continuous_const continuous_norm)
      have hev : F =ᶠ[𝓝 z₀] fun z => starRingEnd ℂ (f (starRingEnd ℂ (z⁻¹))) := by
        filter_upwards [hopen_out.mem_nhds ⟨hz₀, hgt⟩] with z hz
        rw [hF_out z hz, map_inv₀]
      exact hd_out.congr_of_eventuallyEq hev
  refine ⟨hF_holo, hF_in_L, hF_out, hF_symm, ?_⟩
  intro hW_pre hΩ_ne G hG_holo hG_eq z hz
  obtain ⟨w₀, hw₀⟩ := hΩ_ne
  have hopen_in : IsOpen Ω_in := hW_open.inter isOpen_ball
  have hacc : AccPt w₀ (𝓟 Ω_in) := by
    rw [accPt_iff_frequently_nhdsNE, Filter.frequently_iff]
    intro U hU
    obtain ⟨V, hV_open, hw₀_V, hV_sub⟩ := mem_nhdsWithin.mp hU
    obtain ⟨r, hr, hball⟩ :=
      Metric.mem_nhds_iff.mp (Filter.inter_mem (hV_open.mem_nhds hw₀_V) (hopen_in.mem_nhds hw₀))
    let w₁ : ℂ := w₀ + ((r / 2 : ℝ) : ℂ)
    have hw₁_ne : w₁ ≠ w₀ := by
      simp [w₁, hr.ne']
    have hw₁_ball : w₁ ∈ ball w₀ r := by
      rw [mem_ball, dist_eq_norm]
      have hsub : w₁ - w₀ = ((r / 2 : ℝ) : ℂ) := by dsimp [w₁]; ring
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
      exact half_lt_self hr
    exact ⟨w₁, hV_sub ⟨(hball hw₁_ball).1, hw₁_ne⟩, (hball hw₁_ball).2⟩
  have heq_in : Set.EqOn G F Ω_in := fun w hw =>
    (hG_eq w hw).trans (hF_in_L w (Or.inl hw)).symm
  exact RudinRCA.Chapter10.eqOn_of_accumulation ⟨hW_open, ⟨⟨w₀, hw₀.1⟩, hW_pre⟩⟩
    hG_holo hF_holo heq_in hw₀.1 hacc hz


/-! ### Nodes 14.5 and 14.6: Normal Families and Montel's Theorem -/

/-- **Definition 14.5 (Normal family in `H(Ω)`, RCA pp. 281–282):**
A family `ℱ ⊆ H(Ω)` is *normal* when every sequence in `ℱ` contains a subsequence converging
uniformly on every compact subset of `Ω` to a finite complex-valued function `g`. -/
def IsNormalFamily (ℱ : Set (ℂ → ℂ)) (Ω : Set ℂ) : Prop :=
  (∀ f ∈ ℱ, RudinRCA.Chapter10.HolomorphicOn f Ω) ∧
    ∀ u : ℕ → ℂ → ℂ, (∀ n, u n ∈ ℱ) →
      ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
        RudinRCA.Chapter10.ConvergesOnCompactSubsets (fun k => u (φ k)) g Ω

/-- **14.5 (Accompanying assertions, RCA pp. 281–282):**
1. For open `Ω` and any normal family `ℱ ⊆ H(Ω)`, every subsequential compactwise uniform limit
   belongs to `H(Ω)` (by Theorem `10.28`);
2. The finite holomorphic limit need not belong to `ℱ`, witnessed on `U = ball 0 1` by
   `ℱ = {z ↦ z / (n + 1) | n : ℕ}`: `ℱ` is normal, `(z ↦ z / (n + 1)) → 0` uniformly on `U`, and
   `(fun _ => 0) ∉ ℱ`. -/
theorem theorem14_5 :
    (∀ {Ω : Set ℂ} {ℱ : Set (ℂ → ℂ)}, IsOpen Ω → IsNormalFamily ℱ Ω →
      ∀ (u : ℕ → ℂ → ℂ) (φ : ℕ → ℕ) (g : ℂ → ℂ),
        (∀ n, u n ∈ ℱ) →
        RudinRCA.Chapter10.ConvergesOnCompactSubsets (fun k => u (φ k)) g Ω →
        RudinRCA.Chapter10.HolomorphicOn g Ω) ∧
    (let ℱ : Set (ℂ → ℂ) := Set.range (fun n : ℕ => fun z : ℂ => z / ((n + 1 : ℕ) : ℂ))
     IsNormalFamily ℱ (ball (0 : ℂ) 1) ∧
       RudinRCA.Chapter10.ConvergesOnCompactSubsets
         (fun n : ℕ => fun z : ℂ => z / ((n + 1 : ℕ) : ℂ))
         (fun _ => 0) (ball (0 : ℂ) 1) ∧
       (fun _ : ℂ => (0 : ℂ)) ∉ ℱ) := by
  refine ⟨?_, ?_⟩
  · intro Ω ℱ hΩ hnorm u φ g hu hconv
    exact (RudinRCA.Chapter10.holomorphicOn_limit_and_deriv hΩ
      (fun k => hnorm.1 _ (hu (φ k))) hconv).1
  · dsimp only
    let ℱ : Set (ℂ → ℂ) := Set.range (fun n : ℕ => fun z : ℂ => z / ((n + 1 : ℕ) : ℂ))
    have hℱ_holo : ∀ f ∈ ℱ, RudinRCA.Chapter10.HolomorphicOn f (ball (0 : ℂ) 1) := by
      rintro _ ⟨n, rfl⟩ z _
      exact differentiableAt_id.div_const (((n + 1 : ℕ) : ℂ))
    have hconv0 : RudinRCA.Chapter10.ConvergesOnCompactSubsets
        (fun n : ℕ => fun z : ℂ => z / ((n + 1 : ℕ) : ℂ))
        (fun _ => 0) (ball (0 : ℂ) 1) := by
      intro K hK _
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      rw [Filter.eventually_atTop]
      refine ⟨N, fun n hn z hz => ?_⟩
      have hz_lt : ‖z‖ < 1 := mem_ball_zero_iff.mp (hK hz)
      have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [dist_eq_norm, zero_sub, norm_neg, norm_div, Complex.norm_natCast, Nat.cast_add, Nat.cast_one]
      have h1 : 1 / ((n : ℝ) + 1) < ε := by
        have hgt : 1 / ε < (n : ℝ) + 1 := lt_of_lt_of_le hN (by exact_mod_cast Nat.le_succ_of_le hn)
        exact (div_lt_iff₀ hn_pos).mpr ((div_lt_iff₀ hε).mp hgt |>.trans_eq (mul_comm _ _))
      calc
        ‖z‖ / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
          div_le_div_of_nonneg_right hz_lt.le hn_pos.le
        _ < ε := h1
    refine ⟨⟨hℱ_holo, ?_⟩, hconv0, ?_⟩
    · intro u hu
      have hbdd : ∀ K ⊆ ball (0 : ℂ) 1, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖u n z‖ ≤ M := by
        intro K hK _
        refine ⟨1, fun n z hz => ?_⟩
        obtain ⟨m, hm⟩ := hu n
        rw [← hm, norm_div, Complex.norm_natCast]
        have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
        have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp (hK hz)).le
        exact div_le_one_of_le₀ (hz1.trans hm1) (by positivity)
      obtain ⟨φ, g, hφ, _, hconv⟩ :=
        montel_locally_bounded isOpen_ball (fun n => hℱ_holo _ (hu n)) hbdd
      exact ⟨φ, g, hφ, hconv⟩
    · rintro ⟨n, hn⟩
      have hval := congrFun hn (1 : ℂ)
      dsimp at hval
      have hne : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      exact div_ne_zero one_ne_zero hne hval

/-- **Theorem 14.6 (Montel's locally bounded normality theorem, RCA p. 282):**
Suppose `ℱ ⊆ H(Ω)` (with `Ω ⊆ ℂ` open) and for each compact `K ⊆ Ω` there is a constant `M_K < ∞`
such that `‖f(z)‖ ≤ M_K` for all `f ∈ ℱ` and `z ∈ K`. Then `ℱ` is a normal family in `H(Ω)`. -/
theorem theorem14_6 {Ω : Set ℂ} (hΩ : IsOpen Ω) {ℱ : Set (ℂ → ℂ)}
    (hℱ : ∀ f ∈ ℱ, RudinRCA.Chapter10.HolomorphicOn f Ω)
    (hbdd : ∀ K ⊆ Ω, IsCompact K → ∃ M : ℝ, ∀ f ∈ ℱ, ∀ z ∈ K, ‖f z‖ ≤ M) :
    IsNormalFamily ℱ Ω := by
  refine ⟨hℱ, fun u hu => ?_⟩
  obtain ⟨φ, g, hφ, _, hconv⟩ := montel_locally_bounded hΩ (fun n => hℱ _ (hu n))
    (fun K hK hKc => by
      obtain ⟨M, hM⟩ := hbdd K hK hKc
      exact ⟨M, fun n z hz => hM (u n) (hu n) z hz⟩)
  exact ⟨φ, g, hφ, hconv⟩

/-! ### Nodes 14.7, 14.8, and 14.9: Conformal Equivalence and the Riemann Mapping Theorem -/

/-- **14.7 (Conformal equivalence of open sets / regions in `ℂ`, RCA pp. 282–283):**
`Ω₁` and `Ω₂` are *conformally equivalent* when there exists `φ ∈ H(Ω₁)` mapping `Ω₁` bijectively
onto `Ω₂`. -/
def ConformallyEquivalent (Ω₁ Ω₂ : Set ℂ) : Prop :=
  ∃ φ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn φ Ω₁ ∧ BijOn φ Ω₁ Ω₂

/-- `ℂ`-algebra `H(Ω)` of complex-valued holomorphic functions on `Ω` (represented as functions
`Ω → ℂ`). -/
def HolomorphicSubalgebra (Ω : Set ℂ) : Subalgebra ℂ (Ω → ℂ) where
  carrier := {g : Ω → ℂ | ∃ f : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn f Ω ∧ ∀ z : Ω, g z = f z.1}
  mul_mem' := by
    rintro g₁ g₂ ⟨f₁, hf₁, hg₁⟩ ⟨f₂, hf₂, hg₂⟩
    exact ⟨fun z => f₁ z * f₂ z, fun z hz => (hf₁ z hz).mul (hf₂ z hz),
      fun z => by simp [hg₁ z, hg₂ z]⟩
  one_mem' := ⟨fun _ => 1, fun _ _ => differentiableAt_const 1, fun _ => rfl⟩
  add_mem' := by
    rintro g₁ g₂ ⟨f₁, hf₁, hg₁⟩ ⟨f₂, hf₂, hg₂⟩
    exact ⟨fun z => f₁ z + f₂ z, fun z hz => (hf₁ z hz).add (hf₂ z hz),
      fun z => by simp [hg₁ z, hg₂ z]⟩
  zero_mem' := ⟨fun _ => 0, fun _ _ => differentiableAt_const 0, fun _ => rfl⟩
  algebraMap_mem' := fun c => ⟨fun _ => c, fun _ _ => differentiableAt_const c, fun _ => rfl⟩

theorem conformallyEquivalent_refl (Ω : Set ℂ) : ConformallyEquivalent Ω Ω :=
  ⟨id, fun _ _ => differentiableAt_id, bijOn_id Ω⟩

theorem conformallyEquivalent_symm {Ω₁ Ω₂ : Set ℂ} (hΩ₁ : IsOpen Ω₁)
    (h : ConformallyEquivalent Ω₁ Ω₂) : ConformallyEquivalent Ω₂ Ω₁ := by
  rcases h with ⟨φ, hφ_holo, hφ_bij⟩
  obtain ⟨ψ, hψ_holo, hleft, hright, _⟩ :=
    (RudinRCA.Chapter10.theorem10_33.1 hΩ₁ hφ_holo hφ_bij.injOn).2.2
  rw [hφ_bij.image_eq] at hψ_holo hright
  refine ⟨ψ, hψ_holo, ?_, ?_, ?_⟩
  · exact fun w hw => (hright w hw).1
  · intro w₁ hw₁ w₂ hw₂ heq
    rw [← (hright w₁ hw₁).2, ← (hright w₂ hw₂).2, heq]
  · exact fun z hz => ⟨φ z, hφ_bij.mapsTo hz, hleft z hz⟩

theorem conformallyEquivalent_trans {Ω₁ Ω₂ Ω₃ : Set ℂ}
    (h₁₂ : ConformallyEquivalent Ω₁ Ω₂) (h₂₃ : ConformallyEquivalent Ω₂ Ω₃) :
    ConformallyEquivalent Ω₁ Ω₃ := by
  rcases h₁₂ with ⟨φ₁, h₁_holo, h₁_bij⟩
  rcases h₂₃ with ⟨φ₂, h₂_holo, h₂_bij⟩
  exact ⟨φ₂ ∘ φ₁,
    fun z hz => (h₂_holo (φ₁ z) (h₁_bij.mapsTo hz)).comp z (h₁_holo z hz),
    h₂_bij.comp h₁_bij⟩

/-- **Node 14.7 (Conformal Equivalence properties, RCA pp. 282–283):**
1. Conformal equivalence is reflexive, symmetric (on open sets), and transitive;
2. Every holomorphic bijection `φ : Ω₁ → Ω₂` (`Ω₁` open) has a holomorphic inverse `ψ : Ω₂ → Ω₁`
   (by `10.33`), induces a homeomorphism `Ω₁ ≃ₜ Ω₂`, and induces a `ℂ`-algebra isomorphism
   `HolomorphicSubalgebra Ω₂ ≃ₐ[ℂ] HolomorphicSubalgebra Ω₁` via pullback `f ↦ f ∘ φ`. -/
theorem theorem14_7 {Ω₁ Ω₂ : Set ℂ} (hΩ₁ : IsOpen Ω₁) {φ : ℂ → ℂ}
    (hφ_holo : RudinRCA.Chapter10.HolomorphicOn φ Ω₁) (hφ_bij : BijOn φ Ω₁ Ω₂) :
    IsOpen Ω₂ ∧
    (∃ ψ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn ψ Ω₂ ∧ BijOn ψ Ω₂ Ω₁ ∧
      (∀ z ∈ Ω₁, ψ (φ z) = z) ∧ (∀ w ∈ Ω₂, φ (ψ w) = w)) ∧
    Nonempty (Ω₁ ≃ₜ Ω₂) ∧
    ∃ E : HolomorphicSubalgebra Ω₂ ≃ₐ[ℂ] HolomorphicSubalgebra Ω₁,
      ∀ (g : HolomorphicSubalgebra Ω₂) (z : Ω₁),
        (E g).1 z = g.1 ⟨φ z.1, hφ_bij.mapsTo z.2⟩ := by
  obtain ⟨_, hΩ₂_open, ψ, hψ_holo, hleft, hright, _⟩ :=
    RudinRCA.Chapter10.theorem10_33.1 hΩ₁ hφ_holo hφ_bij.injOn
  rw [hφ_bij.image_eq] at hΩ₂_open hψ_holo hright
  have hψ_bij : BijOn ψ Ω₂ Ω₁ := by
    refine ⟨fun w hw => (hright w hw).1, ?_, fun z hz => ⟨φ z, hφ_bij.mapsTo hz, hleft z hz⟩⟩
    intro w₁ hw₁ w₂ hw₂ heq
    rw [← (hright w₁ hw₁).2, ← (hright w₂ hw₂).2, heq]
  have hφ_cont : ContinuousOn φ Ω₁ := RudinRCA.Chapter10.continuousOn_of_holomorphicOn hφ_holo
  have hψ_cont : ContinuousOn ψ Ω₂ := RudinRCA.Chapter10.continuousOn_of_holomorphicOn hψ_holo
  let homeo : Ω₁ ≃ₜ Ω₂ := {
    toFun := fun z => ⟨φ z.1, hφ_bij.mapsTo z.2⟩
    invFun := fun w => ⟨ψ w.1, (hright w.1 w.2).1⟩
    left_inv := fun z => Subtype.ext (hleft z.1 z.2)
    right_inv := fun w => Subtype.ext (hright w.1 w.2).2
    continuous_toFun := Continuous.subtype_mk
      (hφ_cont.comp_continuous continuous_subtype_val Subtype.prop) _
    continuous_invFun := Continuous.subtype_mk
      (hψ_cont.comp_continuous continuous_subtype_val Subtype.prop) _
  }
  let toPull : HolomorphicSubalgebra Ω₂ → HolomorphicSubalgebra Ω₁ := fun g =>
    ⟨fun z => g.1 ⟨φ z.1, hφ_bij.mapsTo z.2⟩, by
      rcases g.2 with ⟨f, hf, hg⟩
      exact ⟨f ∘ φ, fun z hz => (hf (φ z) (hφ_bij.mapsTo hz)).comp z (hφ_holo z hz),
        fun z => hg ⟨φ z.1, hφ_bij.mapsTo z.2⟩⟩⟩
  let invPull : HolomorphicSubalgebra Ω₁ → HolomorphicSubalgebra Ω₂ := fun k =>
    ⟨fun w => k.1 ⟨ψ w.1, (hright w.1 w.2).1⟩, by
      rcases k.2 with ⟨f, hf, hk⟩
      exact ⟨f ∘ ψ, fun w hw => (hf (ψ w) (hright w hw).1).comp w (hψ_holo w hw),
        fun w => hk ⟨ψ w.1, (hright w.1 w.2).1⟩⟩⟩
  let algEq : HolomorphicSubalgebra Ω₂ ≃ₐ[ℂ] HolomorphicSubalgebra Ω₁ := {
    toFun := toPull
    invFun := invPull
    left_inv := fun g => by
      ext w
      have hw_eq : (⟨φ (ψ w.1), hφ_bij.mapsTo (hright w.1 w.2).1⟩ : Ω₂) = w :=
        Subtype.ext (hright w.1 w.2).2
      exact congrArg g.1 hw_eq
    right_inv := fun k => by
      ext z
      have hz_eq : (⟨ψ (φ z.1), (hright (φ z.1) (hφ_bij.mapsTo z.2)).1⟩ : Ω₁) = z :=
        Subtype.ext (hleft z.1 z.2)
      exact congrArg k.1 hz_eq
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
    commutes' := fun _ => rfl
  }
  exact ⟨hΩ₂_open,
    ⟨ψ, hψ_holo, hψ_bij, hleft, fun w hw => (hright w hw).2⟩,
    ⟨homeo⟩,
    ⟨algEq, fun _ _ => rfl⟩⟩

/-- **Theorem 14.8 (Riemann Mapping Theorem, RCA pp. 283–284):**
1. Every simply connected plane region `Ω` properly contained in `ℂ` (`Ω ≠ Set.univ`) is
   conformally equivalent to the open unit disc `U = ball 0 1`;
2. More generally (matching Rudin's proof, which also supplies `13.11(j) → 13.11(a)`), any proper
   plane region `Ω` on which every zero-free `f ∈ H(Ω)` has a holomorphic square root is
   conformally equivalent to `U`;
3. The whole plane `ℂ` (`Set.univ`) is a simply connected region homeomorphic to `U`, yet NOT
   conformally equivalent to `U` (by Liouville's theorem `10.23`). -/
theorem theorem14_8 :
    (∀ {Ω : Set ℂ}, RudinRCA.Chapter10.IsRegion Ω →
      RudinRCA.Chapter10.BookSimplyConnected Ω → Ω ≠ Set.univ →
      ConformallyEquivalent Ω (ball (0 : ℂ) 1)) ∧
    (∀ {Ω : Set ℂ}, RudinRCA.Chapter10.IsRegion Ω → Ω ≠ Set.univ →
      (∀ f : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn f Ω → (∀ z ∈ Ω, f z ≠ 0) →
        ∃ φ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn φ Ω ∧ ∀ z ∈ Ω, φ z ^ 2 = f z) →
      ConformallyEquivalent Ω (ball (0 : ℂ) 1)) ∧
    (RudinRCA.Chapter10.IsRegion (Set.univ : Set ℂ) ∧
      RudinRCA.Chapter10.BookSimplyConnected (Set.univ : Set ℂ) ∧
      Nonempty ((Set.univ : Set ℂ) ≃ₜ ball (0 : ℂ) 1) ∧
      ¬ ConformallyEquivalent (Set.univ : Set ℂ) (ball (0 : ℂ) 1)) := by
  have hsqrt_ver : ∀ {Ω : Set ℂ}, RudinRCA.Chapter10.IsRegion Ω → Ω ≠ Set.univ →
      (∀ f : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn f Ω → (∀ z ∈ Ω, f z ≠ 0) →
        ∃ φ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn φ Ω ∧ ∀ z ∈ Ω, φ z ^ 2 = f z) →
      ConformallyEquivalent Ω (ball (0 : ℂ) 1) := by
    intro Ω hΩ hproper hsqrt
    obtain ⟨z₀, hz₀⟩ := hΩ.2.nonempty
    obtain ⟨h, hh_holo, hh_bij, _⟩ := riemann_mapping_of_holomorphic_sqrt hΩ hproper hz₀ hsqrt
    exact ⟨h, hh_holo, hh_bij⟩
  refine ⟨?_, hsqrt_ver, ?_⟩
  · intro Ω hΩ hsc hproper
    have hbj : (RudinRCA.Chapter10.BookSimplyConnected Ω) →
        (∀ f : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn f Ω → (∀ z ∈ Ω, f z ≠ 0) →
          ∃ φ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn φ Ω ∧ ∀ z ∈ Ω, φ z ^ 2 = f z) :=
      ((theorem13_11 hΩ).1.out 2 9).mp
    exact hsqrt_ver hΩ hproper (hbj hsc)
  · have huniv_reg : RudinRCA.Chapter10.IsRegion (Set.univ : Set ℂ) :=
      ⟨isOpen_univ, isConnected_univ⟩
    refine ⟨huniv_reg,
      RudinRCA.Chapter10.theorem10_38 huniv_reg convex_univ,
      ⟨(Homeomorph.Set.univ ℂ).trans planeHomeomorphUnitBall⟩, ?_⟩
    rintro ⟨φ, hφ_holo, hφ_bij⟩
    have hbdd : Bornology.IsBounded (Set.range φ) := by
      refine (Metric.isBounded_ball (x := (0 : ℂ)) (r := 1)).subset ?_
      rintro _ ⟨z, rfl⟩
      exact hφ_bij.mapsTo (Set.mem_univ z)
    obtain ⟨c, hc⟩ := RudinRCA.Chapter10.liouville hφ_holo hbdd
    have h01 : (0 : ℂ) = 1 :=
      hφ_bij.injOn (Set.mem_univ 0) (Set.mem_univ 1) ((hc 0).trans (hc 1).symm)
    exact zero_ne_one h01

/-- **Remarks 14.9 (Extremal property and uniqueness of the normalized Riemann map, RCA p. 285):**
Fix `z₀ ∈ Ω` in a proper simply connected plane region `Ω` (`Ω ≠ Set.univ`). Then:
1. There exists a holomorphic bijection `h : Ω → U` normalized by `h(z₀) = 0`, `(deriv h z₀).re > 0`,
   and `(deriv h z₀).im = 0`;
2. For *every* `f ∈ H(Ω)` mapping `Ω` into `U` (not necessarily injective),
   `‖deriv f z₀‖ ≤ ‖deriv h z₀‖`, with equality if and only if `f(z) = λ * h(z)` for all `z ∈ Ω`
   for some constant `λ : ℂ` with `‖λ‖ = 1`;
3. Consequently, the normalized Riemann map (`h(z₀) = 0`, `deriv h z₀ > 0`) is unique on `Ω`. -/
theorem theorem14_9 {Ω : Set ℂ} (hΩ : RudinRCA.Chapter10.IsRegion Ω)
    (hsc : RudinRCA.Chapter10.BookSimplyConnected Ω) (hproper : Ω ≠ Set.univ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ h : ℂ → ℂ,
      RudinRCA.Chapter10.HolomorphicOn h Ω ∧
      BijOn h Ω (ball (0 : ℂ) 1) ∧
      h z₀ = 0 ∧
      0 < (deriv h z₀).re ∧ (deriv h z₀).im = 0 ∧
      (∀ f : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn f Ω → MapsTo f Ω (ball (0 : ℂ) 1) →
        ‖deriv f z₀‖ ≤ ‖deriv h z₀‖ ∧
        (‖deriv f z₀‖ = ‖deriv h z₀‖ ↔ ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ Ω, f z = c * h z)) ∧
      (∀ h₁ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn h₁ Ω →
        BijOn h₁ Ω (ball (0 : ℂ) 1) → h₁ z₀ = 0 →
        0 < (deriv h₁ z₀).re → (deriv h₁ z₀).im = 0 →
        ∀ z ∈ Ω, h₁ z = h z) := by
  have hsqrt : ∀ f : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn f Ω → (∀ z ∈ Ω, f z ≠ 0) →
      ∃ φ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn φ Ω ∧ ∀ z ∈ Ω, φ z ^ 2 = f z :=
    ((theorem13_11 hΩ).1.out 2 9).mp hsc
  obtain ⟨h, hh_holo, hh_bij, hhz₀, hdh_re, hdh_im, _, hext⟩ :=
    riemann_mapping_of_holomorphic_sqrt hΩ hproper hz₀ hsqrt
  refine ⟨h, hh_holo, hh_bij, hhz₀, hdh_re, hdh_im, hext, ?_⟩
  intro h₁ hh₁_holo hh₁_bij hh₁z₀ hdh₁_re hdh₁_im
  -- Bound `‖deriv h z₀‖ ≤ ‖deriv h₁ z₀‖` via Schwarz lemma on `h ∘ h₁⁻¹`
  obtain ⟨g₁, hg₁_holo, hg₁_left, hg₁_right, hg₁_deriv⟩ :=
    (RudinRCA.Chapter10.theorem10_33.1 hΩ.1 hh₁_holo hh₁_bij.injOn).2.2
  rw [hh₁_bij.image_eq] at hg₁_holo hg₁_right
  have hg₁0 : g₁ 0 = z₀ := by
    have := hg₁_left z₀ hz₀
    rwa [hh₁z₀] at this
  have hdg₁0 : deriv g₁ 0 = (deriv h₁ z₀)⁻¹ := by
    have := hg₁_deriv z₀ hz₀
    rwa [hh₁z₀] at this
  let F : ℂ → ℂ := fun w => h (g₁ w)
  have hF_diff : DifferentiableOn ℂ F (ball (0 : ℂ) 1) :=
    fun w hw => ((hh_holo (g₁ w) (hg₁_right w hw).1).comp w (hg₁_holo w hw)).differentiableWithinAt
  have hF_le1 : ∀ w ∈ ball (0 : ℂ) 1, ‖F w‖ ≤ 1 :=
    fun w hw => (mem_ball_zero_iff.mp (hh_bij.mapsTo (hg₁_right w hw).1)).le
  have hF0 : F 0 = 0 := by dsimp [F]; rw [hg₁0, hhz₀]
  obtain ⟨_, hF_deriv_le1, _⟩ := RudinRCA.Chapter12.theorem12_2 hF_diff hF_le1 hF0
  have hd_F0 : deriv F 0 = deriv h z₀ * (deriv h₁ z₀)⁻¹ := by
    have h1 : HasDerivAt h (deriv h z₀) (g₁ 0) := hg₁0.symm ▸ (hh_holo z₀ hz₀).hasDerivAt
    have hcomp := h1.comp 0 (hg₁_holo 0 (Metric.mem_ball_self zero_lt_one)).hasDerivAt
    change deriv (h ∘ g₁) 0 = _
    rw [hcomp.deriv, hdg₁0]
  have hdh₁_eq_re : deriv h₁ z₀ = ((deriv h₁ z₀).re : ℂ) :=
    Complex.ext rfl (by simp [hdh₁_im])
  have hdh_eq_re : deriv h z₀ = ((deriv h z₀).re : ℂ) :=
    Complex.ext rfl (by simp [hdh_im])
  have hnorm_h₁ : ‖deriv h₁ z₀‖ = (deriv h₁ z₀).re := by
    conv_lhs => rw [hdh₁_eq_re]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdh₁_re]
  have hnorm_h : ‖deriv h z₀‖ = (deriv h z₀).re := by
    conv_lhs => rw [hdh_eq_re]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdh_re]
  have hle_rev : ‖deriv h z₀‖ ≤ ‖deriv h₁ z₀‖ := by
    rw [hd_F0, norm_mul, norm_inv] at hF_deriv_le1
    exact (div_le_one (by rw [hnorm_h₁]; exact hdh₁_re)).mp
      (by rwa [div_eq_mul_inv])
  obtain ⟨hle_fwd, heq_iff⟩ := hext h₁ hh₁_holo hh₁_bij.mapsTo
  obtain ⟨c, _, hc_eq⟩ := heq_iff.mp (le_antisymm hle_fwd hle_rev)
  have hev_h₁ : h₁ =ᶠ[𝓝 z₀] fun z => c * h z := by
    filter_upwards [hΩ.1.mem_nhds hz₀] with z hz
    exact hc_eq z hz
  have hd_ch : deriv h₁ z₀ = c * deriv h z₀ := by
    rw [hev_h₁.deriv_eq, ((hh_holo z₀ hz₀).hasDerivAt.const_mul c).deriv]
  have heq_deriv : deriv h₁ z₀ = deriv h z₀ := by
    rw [hdh₁_eq_re, hdh_eq_re, ← hnorm_h₁, ← hnorm_h, le_antisymm hle_fwd hle_rev]
  have hdh_ne : deriv h z₀ ≠ 0 := by
    intro h0; rw [h0, Complex.zero_re] at hdh_re; exact lt_irrefl 0 hdh_re
  have hc1 : c = 1 := by
    apply mul_right_cancel₀ hdh_ne
    rw [← hd_ch, one_mul, heq_deriv]
  intro z hz
  rw [hc_eq z hz, hc1, one_mul]

/-! ### Nodes 14.10, 14.11, and 14.12: The Normalized Univalent Class `S` and Koebe Family -/

/-- **Definition 14.10 (The normalized univalent class `S`, RCA p. 285):**
`ClassS` consists of all holomorphic injective functions `f : U → ℂ` on the open unit disc
`U = ball 0 1` normalized by `f(0) = 0` and `f'(0) = 1`. -/
def ClassS : Set (ℂ → ℂ) :=
  {f | RudinRCA.Chapter10.HolomorphicOn f (ball (0 : ℂ) 1) ∧
    InjOn f (ball (0 : ℂ) 1) ∧ f 0 = 0 ∧ deriv f 0 = 1}

/-- Unique Taylor expansion `f(z) = z + ∑_{n ≥ 2} a_n z^n` on `U` for any `f ∈ ClassS`. -/
theorem classS_taylor_expansion {f : ℂ → ℂ} (hf : f ∈ ClassS) :
    ∃! a : ℕ → ℂ,
      a 0 = 0 ∧ a 1 = 1 ∧
      (∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n : ℕ => a n * z ^ n) (f z)) ∧
      (∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n : ℕ => a (n + 2) * z ^ (n + 2)) (f z - z)) := by
  rcases hf with ⟨hf_holo, _, hf0, hdf0⟩
  have hrep := RudinRCA.Chapter10.representableByPowerSeries_of_holomorphicOn hf_holo
  obtain ⟨a, ha⟩ := hrep 0 1 zero_lt_one Subset.rfl
  have ha' : ∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n : ℕ => a n * z ^ n) (f z) := by
    intro z hz
    simpa [sub_zero] using ha z hz
  have ha0 : a 0 = 0 := by
    have hc0 := RudinRCA.Chapter10.powerSeries_coefficient zero_lt_one ha 0
    simpa [hf0] using hc0
  have ha1 : a 1 = 1 := by
    have hc1 := RudinRCA.Chapter10.powerSeries_coefficient zero_lt_one ha 1
    simpa [iteratedDeriv_one, hdf0] using hc1
  have hshift : ∀ z ∈ ball (0 : ℂ) 1,
      HasSum (fun n : ℕ => a (n + 2) * z ^ (n + 2)) (f z - z) := by
    intro z hz
    have hs := (hasSum_nat_add_iff' 2).mpr (ha' z hz)
    simpa [Finset.sum_range_succ, ha0, ha1] using hs
  refine ⟨a, ⟨ha0, ha1, ha', hshift⟩, ?_⟩
  rintro b ⟨_, _, hb', _⟩
  have hb : ∀ z ∈ RudinRCA.Chapter10.disc 0 1, HasSum (fun n : ℕ => b n * (z - 0) ^ n) (f z) := by
    intro z hz
    simpa [sub_zero] using hb' z hz
  exact (RudinRCA.Chapter10.powerSeries_coefficients_unique zero_lt_one ha hb).symm

/-- **14.10 (Normalized univalent class `S` expansion and non-closure, RCA p. 285):**
1. Every `f ∈ ClassS` has a unique convergent expansion `f(z) = z + ∑_{n ≥ 2} a_n z^n` on `U`;
2. `ClassS` is neither closed under pointwise addition nor closed under pointwise multiplication. -/
theorem theorem14_10 :
    (∀ f ∈ ClassS, ∃! a : ℕ → ℂ,
      a 0 = 0 ∧ a 1 = 1 ∧
      (∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n : ℕ => a n * z ^ n) (f z)) ∧
      (∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n : ℕ => a (n + 2) * z ^ (n + 2)) (f z - z))) ∧
    (∃ f ∈ ClassS, ∃ g ∈ ClassS, (fun z => f z + g z) ∉ ClassS) ∧
    (∃ f ∈ ClassS, ∃ g ∈ ClassS, (fun z => f z * g z) ∉ ClassS) := by
  have hid_S : (fun z : ℂ => z) ∈ ClassS := by
    refine ⟨fun z _ => differentiableAt_id, fun _ _ _ _ h => h, rfl, ?_⟩
    exact hasDerivAt_id (0 : ℂ) |>.deriv
  refine ⟨fun f hf => classS_taylor_expansion hf,
    ⟨fun z => z, hid_S, fun z => z, hid_S, ?_⟩,
    ⟨fun z => z, hid_S, fun z => z, hid_S, ?_⟩⟩
  · intro hadd
    have hd : deriv (fun z : ℂ => z + z) 0 = 2 := by
      have := ((hasDerivAt_id (0 : ℂ)).add (hasDerivAt_id (0 : ℂ))).deriv
      simpa [one_add_one_eq_two] using this
    rw [hadd.2.2.2] at hd
    norm_num at hd
  · intro hmul
    have hd : deriv (fun z : ℂ => z * z) 0 = 0 := by
      have := ((hasDerivAt_id (0 : ℂ)).mul (hasDerivAt_id (0 : ℂ))).deriv
      simpa using this
    rw [hmul.2.2.2] at hd
    norm_num at hd

/-- **Example 14.11 (The Koebe family `f_α(z) = z / (1 - α z)^2`, RCA p. 285):** -/
def koebeFamily (α : ℂ) (z : ℂ) : ℂ :=
  z / (1 - α * z) ^ 2

/-- **14.11 (Koebe family membership in `S` and power-series expansion, RCA p. 285):**
For every `α : ℂ` with `‖α‖ ≤ 1`, `koebeFamily α` belongs to `ClassS` and satisfies
`koebeFamily α z = ∑_{n=1}^∞ n α^{n-1} z^n` (`HasSum (fun n => (n + 1) * α^n * z^{n+1})`) for all
`z ∈ ball 0 1`. -/
theorem theorem14_11 {α : ℂ} (hα : ‖α‖ ≤ 1) :
    koebeFamily α ∈ ClassS ∧
    ∀ z ∈ ball (0 : ℂ) 1,
      HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * α ^ n * z ^ (n + 1)) (koebeFamily α z) := by
  have hden_ne : ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → 1 - α * z ≠ 0 := by
    intro z hz h0
    have hlt : ‖α * z‖ < 1 := by
      rw [norm_mul]
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      calc
        ‖α‖ * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hα (norm_nonneg z)
        _ = ‖z‖ := one_mul _
        _ < 1 := hz1
    have heq1 : α * z = 1 := (sub_eq_zero.mp h0).symm
    rw [heq1, norm_one] at hlt
    exact lt_irrefl 1 hlt
  have hholo : RudinRCA.Chapter10.HolomorphicOn (koebeFamily α) (ball (0 : ℂ) 1) := by
    intro z hz
    unfold koebeFamily
    have hsub : DifferentiableAt ℂ (fun w : ℂ => (1 - α * w) ^ 2) z :=
      ((differentiableAt_const (1 : ℂ)).sub ((differentiableAt_const α).mul differentiableAt_id)).pow 2
    exact differentiableAt_id.div hsub (pow_ne_zero 2 (hden_ne hz))
  have hinj : InjOn (koebeFamily α) (ball (0 : ℂ) 1) := by
    intro z₁ hz₁ z₂ hz₂ heq
    unfold koebeFamily at heq
    have hd1 : (1 - α * z₁) ^ 2 ≠ 0 := pow_ne_zero 2 (hden_ne hz₁)
    have hd2 : (1 - α * z₂) ^ 2 ≠ 0 := pow_ne_zero 2 (hden_ne hz₂)
    have hcross : z₁ * (1 - α * z₂) ^ 2 - z₂ * (1 - α * z₁) ^ 2 = 0 := by
      have := (div_eq_div_iff hd1 hd2).mp heq
      linear_combination this
    have hfac : (z₁ - z₂) * (1 - α ^ 2 * z₁ * z₂) = 0 := by
      linear_combination hcross
    have hprod_lt : ‖α ^ 2 * z₁ * z₂‖ < 1 := by
      have hz₁1 : ‖z₁‖ < 1 := mem_ball_zero_iff.mp hz₁
      have hz₂1 : ‖z₂‖ < 1 := mem_ball_zero_iff.mp hz₂
      rw [norm_mul, norm_mul, norm_pow]
      have hα2 : ‖α‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg α, hα]
      have hz12 : ‖z₁‖ * ‖z₂‖ < 1 := by
        calc
          ‖z₁‖ * ‖z₂‖ ≤ ‖z₁‖ * 1 := mul_le_mul_of_nonneg_left hz₂1.le (norm_nonneg z₁)
          _ = ‖z₁‖ := mul_one _
          _ < 1 := hz₁1
      calc
        ‖α‖ ^ 2 * ‖z₁‖ * ‖z₂‖ = ‖α‖ ^ 2 * (‖z₁‖ * ‖z₂‖) := by ring
        _ ≤ 1 * (‖z₁‖ * ‖z₂‖) := mul_le_mul_of_nonneg_right hα2 (by positivity)
        _ < 1 := by linarith
    have hfac2_ne : 1 - α ^ 2 * z₁ * z₂ ≠ 0 := by
      intro h0
      have heq1 : α ^ 2 * z₁ * z₂ = 1 := (sub_eq_zero.mp h0).symm
      rw [heq1, norm_one] at hprod_lt
      exact lt_irrefl 1 hprod_lt
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hfac2_ne)
  have hf0 : koebeFamily α 0 = 0 := by simp [koebeFamily]
  have hdf0 : deriv (koebeFamily α) 0 = 1 := by
    have hd_num := hasDerivAt_id (0 : ℂ)
    have h1 := (hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub ((hasDerivAt_id (0 : ℂ)).const_mul α)
    have hd_den := h1.pow 2
    have hquot := hd_num.div hd_den (by norm_num)
    exact (hquot.congr_deriv (by norm_num)).deriv
  refine ⟨⟨hholo, hinj, hf0, hdf0⟩, ?_⟩
  intro z hz
  have hw_mem : α * z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul]
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    calc
      ‖α‖ * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hα (norm_nonneg z)
      _ < 1 := by linarith
  let invOneSub : ℂ → ℂ := fun w => (1 - w)⁻¹
  have hinv_holo : RudinRCA.Chapter10.HolomorphicOn invOneSub (ball (0 : ℂ) 1) := by
    intro w hw
    have hw_ne : 1 - w ≠ 0 := by
      intro h0
      have hw1 : w = 1 := (sub_eq_zero.mp h0).symm
      have := mem_ball_zero_iff.mp hw
      rw [hw1, norm_one] at this
      exact lt_irrefl 1 this
    exact ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).inv hw_ne
  have hinv_sum : ∀ w ∈ RudinRCA.Chapter10.disc 0 1,
      HasSum (fun n : ℕ => (1 : ℂ) * (w - 0) ^ n) (invOneSub w) := by
    intro w hw
    simpa [invOneSub, one_mul, sub_zero] using
      hasSum_geometric_of_norm_lt_one (mem_ball_zero_iff.mp hw)
  have hd_sum := RudinRCA.Chapter10.hasSum_deriv_powerSeries
    isOpen_ball
    (RudinRCA.Chapter10.representableByPowerSeries_of_holomorphicOn hinv_holo)
    zero_lt_one Subset.rfl hinv_sum hw_mem
  have hd_val : deriv invOneSub (α * z) = ((1 - α * z) ^ 2)⁻¹ := by
    have hw_ne : 1 - α * z ≠ 0 := hden_ne hz
    have hd1 : HasDerivAt (fun x : ℂ => 1 - x) (0 - 1) (α * z) :=
      (hasDerivAt_const (α * z) (1 : ℂ)).sub (hasDerivAt_id (α * z))
    have hd2 := hd1.inv hw_ne
    exact (hd2.congr_deriv (by rw [div_eq_mul_inv]; ring)).deriv
  rw [hd_val] at hd_sum
  have hmul := hd_sum.mul_left z
  convert hmul using 1
  · ext n
    push_cast
    rw [sub_zero, mul_pow]
    ring
  · unfold koebeFamily
    rw [div_eq_mul_inv]

/-- Explicit odd square-root lift for `f ∈ ClassS`: writes `f(z) = z * φ(z)` with `φ = dslope f 0`,
constructs `h ∈ H(U)` zero-free with `h(0) = 1` and `h(z)^2 = dslope f 0 z`, and sets
`g(z) = z * h(z^2) ∈ ClassS`. -/
theorem classS_odd_sqrt_aux {f : ℂ → ℂ} (hf : f ∈ ClassS) :
    ∃ h : ℂ → ℂ,
      RudinRCA.Chapter10.HolomorphicOn h (ball (0 : ℂ) 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, h z ≠ 0) ∧
      h 0 = 1 ∧
      (∀ z ∈ ball (0 : ℂ) 1, h z ^ 2 = dslope f 0 z) ∧
      (fun z : ℂ => z * h (z ^ 2)) ∈ ClassS ∧
      (∀ z ∈ ball (0 : ℂ) 1, (z * h (z ^ 2)) ^ 2 = f (z ^ 2)) ∧
      (∀ z : ℂ, (-z) * h ((-z) ^ 2) = -(z * h (z ^ 2))) := by
  rcases hf with ⟨hf_holo, hf_inj, hf0, hdf0⟩
  have hf_diff : DifferentiableOn ℂ f (ball (0 : ℂ) 1) :=
    (RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn isOpen_ball).mp hf_holo
  let φ : ℂ → ℂ := dslope f 0
  have hφ_diff : DifferentiableOn ℂ φ (ball (0 : ℂ) 1) :=
    (Complex.differentiableOn_dslope (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)).mpr hf_diff
  have hφ_holo : RudinRCA.Chapter10.HolomorphicOn φ (ball (0 : ℂ) 1) :=
    (RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn isOpen_ball).mpr hφ_diff
  have hφ0 : φ 0 = 1 := by
    simp [φ, dslope_same, hdf0]
  have hmul_φ : ∀ z : ℂ, z * φ z = f z := by
    intro z
    have hs := sub_smul_dslope f 0 z
    simpa [φ, hf0, smul_eq_mul] using hs
  have hφ_ne : ∀ z ∈ ball (0 : ℂ) 1, φ z ≠ 0 := by
    intro z hz h0
    by_cases hz0 : z = 0
    · rw [hz0, hφ0] at h0
      exact one_ne_zero h0
    · have hfz0 : f z = f 0 := by
        rw [← hmul_φ z, h0, mul_zero, hf0]
      exact hz0 (hf_inj hz (Metric.mem_ball_self zero_lt_one) hfz0)
  have hU_reg : RudinRCA.Chapter10.IsRegion (ball (0 : ℂ) 1) :=
    RudinRCA.Chapter10.disc_isRegion 0 zero_lt_one
  have hsqrt_U :
      ∀ ψ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn ψ (ball (0 : ℂ) 1) →
        (∀ z ∈ ball (0 : ℂ) 1, ψ z ≠ 0) →
        ∃ η : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn η (ball (0 : ℂ) 1) ∧
          ∀ z ∈ ball (0 : ℂ) 1, η z ^ 2 = ψ z :=
    (theorem13_11 hU_reg).2.2.2.2.2.2.2.2.2.mpr ⟨Homeomorph.refl _⟩
  obtain ⟨h₀, hh₀_holo, hh₀_sq⟩ := hsqrt_U φ hφ_holo hφ_ne
  have hh₀_0_sq : h₀ 0 ^ 2 = 1 := by
    rw [hh₀_sq 0 (Metric.mem_ball_self zero_lt_one), hφ0]
  let h : ℂ → ℂ := fun z => h₀ 0 * h₀ z
  have hh_holo : RudinRCA.Chapter10.HolomorphicOn h (ball (0 : ℂ) 1) :=
    fun z hz => (differentiableAt_const (h₀ 0)).mul (hh₀_holo z hz)
  have hh0 : h 0 = 1 := by
    dsimp [h]
    simpa [sq] using hh₀_0_sq
  have hh_sq : ∀ z ∈ ball (0 : ℂ) 1, h z ^ 2 = φ z := by
    intro z hz
    dsimp [h]
    rw [mul_pow, hh₀_0_sq, one_mul, hh₀_sq z hz]
  have hh_ne : ∀ z ∈ ball (0 : ℂ) 1, h z ≠ 0 := by
    intro z hz h0
    apply hφ_ne z hz
    rw [← hh_sq z hz, h0, zero_pow two_ne_zero]
  let g : ℂ → ℂ := fun z => z * h (z ^ 2)
  have hz2_mem : ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → z ^ 2 ∈ ball (0 : ℂ) 1 := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_pow]
    nlinarith [norm_nonneg z]
  have hg_holo : RudinRCA.Chapter10.HolomorphicOn g (ball (0 : ℂ) 1) := by
    intro z hz
    have hd_h : DifferentiableAt ℂ (h ∘ fun w : ℂ => w ^ 2) z :=
      (hh_holo (z ^ 2) (hz2_mem hz)).comp z (differentiableAt_id.pow 2)
    exact differentiableAt_id.mul hd_h
  have hg_sq : ∀ z ∈ ball (0 : ℂ) 1, g z ^ 2 = f (z ^ 2) := by
    intro z hz
    dsimp [g]
    rw [mul_pow, hh_sq (z ^ 2) (hz2_mem hz), hmul_φ (z ^ 2)]
  have hg_odd : ∀ z : ℂ, g (-z) = -g z := by
    intro z
    dsimp [g]
    rw [neg_sq]
    ring
  have hg0 : g 0 = 0 := by simp [g]
  have hdg0 : deriv g 0 = 1 := by
    have h1 : HasDerivAt h (deriv h 0) ((0 : ℂ) ^ 2) := by
      rw [zero_pow two_ne_zero]
      exact (hh_holo 0 (Metric.mem_ball_self zero_lt_one)).hasDerivAt
    have h2 := (hasDerivAt_id (0 : ℂ)).pow 2
    have hd_comp := h1.comp (0 : ℂ) h2
    have hd_prod := (hasDerivAt_id (0 : ℂ)).mul hd_comp
    exact (hd_prod.congr_deriv (by simp [hh0])).deriv
  have hg_inj : InjOn g (ball (0 : ℂ) 1) := by
    intro z₁ hz₁ z₂ hz₂ heq
    have hf_eq : f (z₁ ^ 2) = f (z₂ ^ 2) := by
      rw [← hg_sq z₁ hz₁, ← hg_sq z₂ hz₂, heq]
    have hsq_eq : z₁ ^ 2 = z₂ ^ 2 := hf_inj (hz2_mem hz₁) (hz2_mem hz₂) hf_eq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq_eq with rfl | rfl
    · rfl
    · have h2g : g z₂ + g z₂ = 0 := by
        calc
          g z₂ + g z₂ = g (-z₂) + g z₂ := by rw [heq]
          _ = -g z₂ + g z₂ := by rw [hg_odd]
          _ = 0 := neg_add_cancel _
      have hgz2_0 : g z₂ = 0 := by linear_combination (1 / 2 : ℂ) * h2g
      have hfz2_0 : f (z₂ ^ 2) = f 0 := by
        rw [← hg_sq z₂ hz₂, hgz2_0, zero_pow two_ne_zero, hf0]
      have hz2_sq_0 : z₂ ^ 2 = 0 := hf_inj (hz2_mem hz₂) (Metric.mem_ball_self zero_lt_one) hfz2_0
      have hz2_0 : z₂ = 0 := eq_zero_of_pow_eq_zero hz2_sq_0
      simp [hz2_0]
  exact ⟨h, hh_holo, hh_ne, hh0, hh_sq, ⟨hg_holo, hg_inj, hg0, hdg0⟩, hg_sq, hg_odd⟩

/-- **Theorem 14.12 (Rotations and odd square-root transforms in `S`, RCA pp. 285–286):**
- `(a)` If `f ∈ ClassS` and `‖α‖ = 1`, then `g(z) = conj(α) * f(α * z)` belongs to `ClassS`.
- `(b)` If `f ∈ ClassS`, there exists `g ∈ ClassS` satisfying `g(z)^2 = f(z^2)` for all `z ∈ U`. -/
theorem theorem14_12 :
    (∀ {f : ℂ → ℂ}, f ∈ ClassS → ∀ {α : ℂ}, ‖α‖ = 1 →
      (fun z : ℂ => starRingEnd ℂ α * f (α * z)) ∈ ClassS) ∧
    (∀ {f : ℂ → ℂ}, f ∈ ClassS →
      ∃ g ∈ ClassS, ∀ z ∈ ball (0 : ℂ) 1, g z ^ 2 = f (z ^ 2)) := by
  refine ⟨?_, ?_⟩
  · intro f ⟨hf_holo, hf_inj, hf0, hdf0⟩ α hα
    have hα_ne : α ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hα; exact zero_ne_one hα
    have hconj_ne : starRingEnd ℂ α ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hα_ne
    have hmap : MapsTo (fun z : ℂ => α * z) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
      intro z hz
      rw [mem_ball_zero_iff] at hz ⊢
      rw [norm_mul, hα, one_mul]
      exact hz
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz
      have hd_f : DifferentiableAt ℂ (f ∘ fun w : ℂ => α * w) z :=
        (hf_holo (α * z) (hmap hz)).comp z ((differentiableAt_const α).mul differentiableAt_id)
      exact (differentiableAt_const (starRingEnd ℂ α)).mul hd_f
    · intro z₁ hz₁ z₂ hz₂ heq
      have hfeq : f (α * z₁) = f (α * z₂) := mul_left_cancel₀ hconj_ne heq
      exact mul_left_cancel₀ hα_ne (hf_inj (hmap hz₁) (hmap hz₂) hfeq)
    · simp [hf0]
    · have hd1 : HasDerivAt f 1 (α * (0 : ℂ)) := by
        rw [mul_zero, ← hdf0]
        exact (hf_holo 0 (Metric.mem_ball_self zero_lt_one)).hasDerivAt
      have hd2 := (hasDerivAt_id (0 : ℂ)).const_mul α
      have hd3 := (hd1.comp (0 : ℂ) hd2).const_mul (starRingEnd ℂ α)
      exact (hd3.congr_deriv (by rw [one_mul, mul_one, Complex.conj_mul', hα]; norm_num)).deriv
  · intro f hf
    obtain ⟨h, _, _, _, _, hg_S, hg_sq, _⟩ := classS_odd_sqrt_aux hf
    exact ⟨fun z => z * h (z ^ 2), hg_S, hg_sq⟩

/-! ### Node 14.13: The Area Theorem and Unnumbered Corollary -/

/-- Real determinant of any `ℝ`-linear continuous endomorphism of `ℂ` in the basis `{1, i}`. -/
theorem det_complex_realCLM (L : ℂ →L[ℝ] ℂ) :
    L.det = (L 1).re * (L Complex.I).im - (L Complex.I).re * (L 1).im := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]

/-- The real Jacobian determinant of multiplication by `d : ℂ` on `ℂ` equals `‖d‖ ^ 2`. -/
theorem det_real_smulRight_complex (d : ℂ) :
    (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ) : ℂ →L[ℝ] ℂ).det =
      ‖d‖ ^ 2 := by
  rw [det_complex_realCLM, Complex.sq_norm, Complex.normSq_apply]
  simp

/-- Unit-modulus square root of the direction of any complex scalar `c`:
produces `rot : ℂ` with `‖rot‖ = 1` and `(‖c‖ : ℂ) * rot ^ 2 = c`. -/
theorem exists_unit_sq_direction (c : ℂ) :
    ∃ rot : ℂ, ‖rot‖ = 1 ∧ (‖c‖ : ℂ) * rot ^ 2 = c := by
  by_cases hc : c = 0
  · refine ⟨1, norm_one, ?_⟩
    simp [hc]
  · let u : ℂ := c / (‖c‖ : ℂ)
    have hn_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hn_ne : (‖c‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn_pos.ne'
    have hu_norm : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn_pos, div_self hn_pos.ne']
    let θ : ℝ := Complex.arg u / 2
    let rot : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
    refine ⟨rot, Complex.norm_exp_ofReal_mul_I θ, ?_⟩
    have hrot_sq : rot ^ 2 = u := by
      dsimp [rot, θ]
      rw [sq, ← Complex.exp_add]
      have harg : ((Complex.arg u / 2 : ℝ) : ℂ) * Complex.I +
          ((Complex.arg u / 2 : ℝ) : ℂ) * Complex.I =
          (Complex.arg u : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg]
      have hpolar := Complex.norm_mul_exp_arg_mul_I u
      rw [hu_norm, Complex.ofReal_one, one_mul] at hpolar
      exact hpolar
    rw [hrot_sq]
    dsimp [u]
    exact mul_div_cancel₀ c hn_ne

/-- Real-linear ellipse map `w ↦ rot * (A * Re w + B * Im w * i)` as a `ℂ ≃L[ℝ] ℂ` when
`‖rot‖ = 1`, `A > 0`, `B > 0`. -/
def ellipseLinearEquiv (rot : ℂ) (hrot : ‖rot‖ = 1) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ℂ ≃L[ℝ] ℂ :=
  let fwd : ℂ →L[ℝ] ℂ :=
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) rot).restrictScalars ℝ).comp
      ((A • (Complex.ofRealCLM.comp Complex.reCLM)) +
        (B • ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) Complex.I).restrictScalars ℝ |>.comp
          Complex.ofRealCLM |>.comp Complex.imCLM)))
  let inv : ℂ →L[ℝ] ℂ :=
    ((A⁻¹ • (Complex.ofRealCLM.comp Complex.reCLM)) +
      (B⁻¹ • ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) Complex.I).restrictScalars ℝ |>.comp
        Complex.ofRealCLM |>.comp Complex.imCLM))).comp
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (starRingEnd ℂ rot)).restrictScalars ℝ)
  have hrot_mul : starRingEnd ℂ rot * rot = 1 := by
    rw [Complex.conj_mul', hrot]; norm_num
  have hrot_mul' : rot * starRingEnd ℂ rot = 1 := by
    rw [mul_comm, hrot_mul]
  ContinuousLinearEquiv.equivOfInverse fwd inv
    (fun w => by
      dsimp [fwd, inv]
      simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply,
        ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.one_apply, Complex.ofRealCLM_apply, Complex.reCLM_apply,
        Complex.imCLM_apply, Complex.real_smul, smul_eq_mul]
      set z₀ : ℂ := (A : ℂ) * (w.re : ℂ) + (B : ℂ) * ((w.im : ℂ) * Complex.I)
      have hz₀ : z₀ * rot * starRingEnd ℂ rot = z₀ := by
        rw [mul_assoc, hrot_mul', mul_one]
      rw [hz₀]
      apply Complex.ext <;> (simp [z₀]; field_simp [hA.ne', hB.ne']))
    (fun w => by
      dsimp [fwd, inv]
      simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply,
        ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.one_apply, Complex.ofRealCLM_apply, Complex.reCLM_apply,
        Complex.imCLM_apply, Complex.real_smul, smul_eq_mul]
      set u : ℂ := w * starRingEnd ℂ rot
      trans u * rot
      · congr 1
        apply Complex.ext <;> (simp; field_simp [hA.ne', hB.ne'])
      · dsimp [u]
        rw [mul_assoc, hrot_mul, mul_one])

@[simp]
theorem ellipseLinearEquiv_apply (rot : ℂ) (hrot : ‖rot‖ = 1) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (w : ℂ) :
    ellipseLinearEquiv rot hrot hA hB w =
      rot * ((A * w.re : ℝ) + ((B * w.im : ℝ) : ℂ) * Complex.I) := by
  dsimp [ellipseLinearEquiv]
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, Complex.ofRealCLM_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, Complex.real_smul]
  push_cast
  ring

@[simp]
theorem ellipseLinearEquiv_symm_apply (rot : ℂ) (hrot : ‖rot‖ = 1) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (z : ℂ) :
    (ellipseLinearEquiv rot hrot hA hB).symm z =
      (((z * starRingEnd ℂ rot).re / A : ℝ) : ℂ) +
        (((z * starRingEnd ℂ rot).im / B : ℝ) : ℂ) * Complex.I := by
  dsimp [ellipseLinearEquiv]
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, Complex.ofRealCLM_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, Complex.real_smul]
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem volume_image_ellipseLinearEquiv_closedBall (rot : ℂ) (hrot : ‖rot‖ = 1) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) :
    MeasureTheory.volume (ellipseLinearEquiv rot hrot hA hB '' closedBall (0 : ℂ) 1) =
      ENNReal.ofReal (Real.pi * A * B) := by
  let L := ellipseLinearEquiv rot hrot hA hB
  rw [MeasureTheory.Measure.addHaar_image_continuousLinearEquiv, Complex.volume_closedBall]
  have hdet : LinearMap.det (L : ℂ →ₗ[ℝ] ℂ) = A * B := by
    have hd := det_complex_realCLM (L : ℂ →L[ℝ] ℂ)
    rw [ContinuousLinearMap.det] at hd
    change LinearMap.det ((L : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = A * B
    rw [hd]
    have hL1 : (L : ℂ →L[ℝ] ℂ) 1 = L 1 := rfl
    have hLI : (L : ℂ →L[ℝ] ℂ) Complex.I = L Complex.I := rfl
    rw [hL1, hLI, ellipseLinearEquiv_apply, ellipseLinearEquiv_apply]
    have hrot_sq : rot.re ^ 2 + rot.im ^ 2 = 1 := by
      have := Complex.sq_norm rot
      rw [hrot, one_pow, Complex.normSq_apply] at this
      linarith
    simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, Complex.ofReal_zero, zero_mul, add_zero, zero_add,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    linear_combination A * B * hrot_sq
  have hAB_pos : 0 < A * B := mul_pos hA hB
  rw [hdet, abs_of_pos hAB_pos,
    show Real.pi * A * B = (A * B) * Real.pi by ring,
    ENNReal.ofReal_mul hAB_pos.le]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

/-- Orthogonality of integer Fourier modes on `[-π, π]`. -/
theorem intervalIntegral_exp_int_mul_I (m : ℤ) :
    (∫ θ in (-Real.pi)..Real.pi, Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I)) =
      if m = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [intervalIntegral.integral_const, Complex.ofReal_mul]
    ring
  · rw [if_neg hm]
    have hmI_ne : (m : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hm) Complex.I_ne_zero
    let F : ℝ → ℂ := fun θ => Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I) / ((m : ℂ) * Complex.I)
    have hderiv : ∀ θ ∈ Set.uIcc (-Real.pi) Real.pi,
        HasDerivAt F (Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I)) θ := by
      intro θ _
      have hlin : HasDerivAt (fun t : ℝ => (m : ℂ) * (t : ℂ) * Complex.I)
          ((m : ℂ) * Complex.I) θ := by
        have h1 := ((Complex.ofRealCLM.hasDerivAt (x := θ)).const_mul (m : ℂ)).mul_const Complex.I
        exact h1.congr_deriv (by simp)
      have hexp := hlin.cexp.div_const ((m : ℂ) * Complex.I)
      exact hexp.congr_deriv (mul_div_cancel_right₀ _ hmI_ne)
    have hint : IntervalIntegrable
        (fun θ : ℝ => Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I)) MeasureTheory.volume
        (-Real.pi) Real.pi := by
      exact (Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    dsimp [F]
    have hexp_eq : Complex.exp ((m : ℂ) * (Real.pi : ℂ) * Complex.I) =
        Complex.exp ((m : ℂ) * ((-Real.pi : ℝ) : ℂ) * Complex.I) := by
      have hsplit : (m : ℂ) * (Real.pi : ℂ) * Complex.I =
          (m : ℂ) * ((-Real.pi : ℝ) : ℂ) * Complex.I +
            (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast; ring
      rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I m, mul_one]
    rw [hexp_eq, sub_self]

/-- Finite Bessel lower bound on `[-π, π]`: if `E : ℝ → ℂ` is continuous and orthogonal to each
mode `e^{i m_k θ}` (`k : Fin n`, `m` injective), then
`2π ∑_k ‖c_k‖^2 ≤ ∫_{-π}^π ‖∑_k c_k e^{i m_k θ} + E(θ)‖^2 dθ`. -/
theorem bessel_trig_poly_bound {n : ℕ} {m : Fin n → ℤ} (hm : Function.Injective m)
    (c : Fin n → ℂ) {E : ℝ → ℂ} (hE_cont : Continuous E)
    (hE_orth : ∀ i : Fin n,
      (∫ θ in (-Real.pi)..Real.pi,
        E θ * Complex.exp (-((m i : ℂ) * (θ : ℂ) * Complex.I))) = 0) :
    2 * Real.pi * (∑ i : Fin n, ‖c i‖ ^ 2) ≤
      ∫ θ in (-Real.pi)..Real.pi,
        ‖(∑ i : Fin n, c i * Complex.exp ((m i : ℂ) * (θ : ℂ) * Complex.I)) + E θ‖ ^ 2 := by
  let P : ℝ → ℂ := fun θ => ∑ i : Fin n, c i * Complex.exp ((m i : ℂ) * (θ : ℂ) * Complex.I)
  have hP_cont : Continuous P :=
    continuous_finset_sum _ fun i _ =>
      continuous_const.mul (Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const))
  have hconj_exp : ∀ (k : ℤ) (θ : ℝ),
      starRingEnd ℂ (Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)) =
        Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) := by
    intro k θ
    rw [← Complex.exp_conj]
    congr 1
    simp
  have hpt : ∀ θ : ℝ,
      ‖P θ + E θ‖ ^ 2 = ‖P θ‖ ^ 2 + ‖E θ‖ ^ 2 + 2 * (E θ * starRingEnd ℂ (P θ)).re := by
    intro θ
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hint_P2 : IntervalIntegrable (fun θ => ‖P θ‖ ^ 2) MeasureTheory.volume (-Real.pi) Real.pi :=
    (hP_cont.norm.pow 2).intervalIntegrable _ _
  have hint_E2 : IntervalIntegrable (fun θ => ‖E θ‖ ^ 2) MeasureTheory.volume (-Real.pi) Real.pi :=
    (hE_cont.norm.pow 2).intervalIntegrable _ _
  have hint_cross_C : IntervalIntegrable (fun θ => E θ * starRingEnd ℂ (P θ))
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hE_cont.mul (Complex.continuous_conj.comp hP_cont)).intervalIntegrable _ _
  have hint_cross : IntervalIntegrable (fun θ => 2 * (E θ * starRingEnd ℂ (P θ)).re)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (continuous_const.mul (Complex.continuous_re.comp
      (hE_cont.mul (Complex.continuous_conj.comp hP_cont)))).intervalIntegrable _ _
  have hcross_zero_C : (∫ θ in (-Real.pi)..Real.pi, E θ * starRingEnd ℂ (P θ)) = 0 := by
    have hexpand : (fun θ : ℝ => E θ * starRingEnd ℂ (P θ)) =
        fun θ : ℝ => ∑ i : Fin n, starRingEnd ℂ (c i) *
          (E θ * Complex.exp (-((m i : ℂ) * (θ : ℂ) * Complex.I))) := by
      ext θ
      simp only [P, map_sum, map_mul, hconj_exp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hexpand, intervalIntegral.integral_finsetSum]
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [intervalIntegral.integral_const_mul, hE_orth i, mul_zero]
    · intro i _
      exact (continuous_const.mul (hE_cont.mul (Complex.continuous_exp.comp
        (Continuous.neg ((continuous_const.mul Complex.continuous_ofReal).mul
          continuous_const))))).intervalIntegrable _ _
  have hcross_zero : (∫ θ in (-Real.pi)..Real.pi, 2 * (E θ * starRingEnd ℂ (P θ)).re) = 0 := by
    rw [intervalIntegral.integral_const_mul]
    have hre := Complex.reCLM.intervalIntegral_comp_comm hint_cross_C
    change 2 * (∫ θ in (-Real.pi)..Real.pi, Complex.reCLM (E θ * starRingEnd ℂ (P θ))) = 0
    rw [hre, hcross_zero_C]
    simp
  have hP2_eval : (∫ θ in (-Real.pi)..Real.pi, ‖P θ‖ ^ 2) =
      2 * Real.pi * (∑ i : Fin n, ‖c i‖ ^ 2) := by
    have hP2_C : (∫ θ in (-Real.pi)..Real.pi, ((‖P θ‖ ^ 2 : ℝ) : ℂ)) =
        ((2 * Real.pi * (∑ i : Fin n, ‖c i‖ ^ 2) : ℝ) : ℂ) := by
      have hpt_C : (fun θ : ℝ => ((‖P θ‖ ^ 2 : ℝ) : ℂ)) =
          fun θ : ℝ => ∑ i : Fin n, ∑ j : Fin n, (c i * starRingEnd ℂ (c j)) *
            Complex.exp (((m i - m j : ℤ) : ℂ) * (θ : ℂ) * Complex.I) := by
        ext θ
        have hmul_conj : ((‖P θ‖ ^ 2 : ℝ) : ℂ) = P θ * starRingEnd ℂ (P θ) := by
          rw [mul_comm, Complex.conj_mul']
          push_cast
          rfl
        rw [hmul_conj]
        simp only [P, map_sum, map_mul, hconj_exp]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hexp_prod : Complex.exp ((m i : ℂ) * (θ : ℂ) * Complex.I) *
            Complex.exp (-((m j : ℂ) * (θ : ℂ) * Complex.I)) =
            Complex.exp (((m i - m j : ℤ) : ℂ) * (θ : ℂ) * Complex.I) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        calc
          c i * Complex.exp ((m i : ℂ) * (θ : ℂ) * Complex.I) *
              (starRingEnd ℂ (c j) * Complex.exp (-((m j : ℂ) * (θ : ℂ) * Complex.I)))
              = (c i * starRingEnd ℂ (c j)) *
                  (Complex.exp ((m i : ℂ) * (θ : ℂ) * Complex.I) *
                    Complex.exp (-((m j : ℂ) * (θ : ℂ) * Complex.I))) := by ring
          _ = (c i * starRingEnd ℂ (c j)) *
                Complex.exp (((m i - m j : ℤ) : ℂ) * (θ : ℂ) * Complex.I) := by rw [hexp_prod]
      rw [hpt_C, intervalIntegral.integral_finsetSum]
      · have hsum_eval : ∀ i : Fin n,
            (∫ θ in (-Real.pi)..Real.pi, ∑ j : Fin n, (c i * starRingEnd ℂ (c j)) *
              Complex.exp (((m i - m j : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) =
              (2 * Real.pi : ℂ) * ((‖c i‖ ^ 2 : ℝ) : ℂ) := by
          intro i
          rw [intervalIntegral.integral_finsetSum]
          · rw [Finset.sum_eq_single i]
            · simp only [sub_self, intervalIntegral_exp_int_mul_I, ↓reduceIte,
                intervalIntegral.integral_const_mul]
              have hci : c i * starRingEnd ℂ (c i) = ((‖c i‖ ^ 2 : ℝ) : ℂ) := by
                rw [mul_comm, Complex.conj_mul']
                push_cast
                rfl
              rw [hci]
              ring
            · intro j _ hji
              rw [intervalIntegral.integral_const_mul, intervalIntegral_exp_int_mul_I,
                if_neg (sub_ne_zero.mpr (fun heq => hji (hm heq).symm)), mul_zero]
            · intro hi
              exact False.elim (hi (Finset.mem_univ i))
          · intro j _
            exact (continuous_const.mul (Complex.continuous_exp.comp
              ((continuous_const.mul Complex.continuous_ofReal).mul
                continuous_const))).intervalIntegrable _ _
        simp_rw [hsum_eval, ← Finset.mul_sum]
        push_cast
        ring
      · intro i _
        exact (continuous_finset_sum _ fun j _ =>
          continuous_const.mul (Complex.continuous_exp.comp
            ((continuous_const.mul Complex.continuous_ofReal).mul
              continuous_const))).intervalIntegrable _ _
    have hre_lhs := Complex.ofRealCLM.intervalIntegral_comp_comm hint_P2
    change (∫ θ in (-Real.pi)..Real.pi, ‖P θ‖ ^ 2) = _
    apply Complex.ofReal_injective
    rw [← hP2_C]
    exact hre_lhs.symm
  have hE2_nonneg : 0 ≤ ∫ θ in (-Real.pi)..Real.pi, ‖E θ‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun _ _ => sq_nonneg _)
  have htotal : (∫ θ in (-Real.pi)..Real.pi, ‖P θ + E θ‖ ^ 2) =
      (∫ θ in (-Real.pi)..Real.pi, ‖P θ‖ ^ 2) +
        (∫ θ in (-Real.pi)..Real.pi, ‖E θ‖ ^ 2) +
        (∫ θ in (-Real.pi)..Real.pi, 2 * (E θ * starRingEnd ℂ (P θ)).re) := by
    simp_rw [hpt]
    rw [intervalIntegral.integral_add (hint_P2.add hint_E2) hint_cross,
      intervalIntegral.integral_add hint_P2 hint_E2]
  linarith

/-- Holomorphic remainder orthogonality on `|z| = ρ` (`0 < ρ < 1`): if `K` is holomorphic on
`ball 0 1` and `m < (N : ℤ)` (`m = -2` or `m = (k : ℤ)` with `k < N`), then
`∫_{-π}^π (ρ e^{iθ})^N K(ρ e^{iθ}) e^{-i m θ} dθ = 0`. -/
theorem ortho_holomorphic_tail_on_circle {K : ℂ → ℂ}
    (hK : RudinRCA.Chapter10.HolomorphicOn K (ball (0 : ℂ) 1))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ) (q : ℕ) (m : ℤ)
    (hm : (q : ℤ) + 1 + m = (N : ℤ)) :
    (∫ θ in (-Real.pi)..Real.pi,
      (circleMap 0 ρ θ ^ N * K (circleMap 0 ρ θ)) *
        Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I))) = 0 := by
  have hclosed_sub : closedBall (0 : ℂ) ρ ⊆ ball (0 : ℂ) 1 :=
    Metric.closedBall_subset_ball hρ1
  let g : ℂ → ℂ := fun z => z ^ q * K z
  have hg_holo : RudinRCA.Chapter10.HolomorphicOn g (ball (0 : ℂ) 1) :=
    fun z hz => (differentiableAt_id.pow q).mul (hK z hz)
  have hg_cont : ContinuousOn g (closedBall (0 : ℂ) ρ) :=
    (RudinRCA.Chapter10.continuousOn_of_holomorphicOn hg_holo).mono hclosed_sub
  have hcauchy : (∮ z in C(0, ρ), g z) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hρ0.le
      Set.countable_empty hg_cont (fun z hz => hg_holo z (ball_subset_closedBall.trans hclosed_sub hz.1))
  -- Relate the `(-π)..π` integral to `circleIntegral g 0 ρ` via `2π`-periodicity
  let φ : ℝ → ℂ := fun θ =>
    (circleMap 0 ρ θ ^ N * K (circleMap 0 ρ θ)) *
      Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I))
  have hφ_per : Function.Periodic φ (2 * Real.pi) := by
    intro θ
    dsimp [φ]
    have hcm : circleMap 0 ρ (θ + 2 * Real.pi) = circleMap 0 ρ θ :=
      periodic_circleMap 0 ρ θ
    have hexp_per : Complex.exp (-((m : ℂ) * ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I)) := by
      have hsplit : -((m : ℂ) * ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
          -((m : ℂ) * (θ : ℂ) * Complex.I) + ((-m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast; ring
      rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I (-m), mul_one]
    rw [hcm, hexp_per]
  have hshift : (∫ θ in (-Real.pi)..Real.pi, φ θ) = ∫ θ in (0 : ℝ)..(2 * Real.pi), φ θ := by
    have h1 := hφ_per.intervalIntegral_add_eq (-Real.pi) 0
    have h2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
    have h3 : (0 : ℝ) + 2 * Real.pi = 2 * Real.pi := by ring
    rw [h2, h3] at h1
    exact h1
  change (∫ θ in (-Real.pi)..Real.pi, φ θ) = 0
  rw [hshift]
  have hρ_ne : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ0.ne'
  have hpt : ∀ θ : ℝ, φ θ =
      (-Complex.I * ((ρ : ℂ) ^ (N : ℤ) * ((ρ : ℂ) ^ (q + 1))⁻¹)) *
        (deriv (circleMap 0 ρ) θ * g (circleMap 0 ρ θ)) := by
    intro θ
    dsimp [φ, g]
    rw [deriv_circleMap]
    simp only [circleMap_zero]
    rw [mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    have hexp_id : Complex.exp ((N : ℂ) * ((θ : ℂ) * Complex.I)) *
        Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I)) =
        Complex.exp ((q : ℂ) * ((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      have hm_C : (q : ℂ) + 1 + (m : ℂ) = (N : ℂ) := by exact_mod_cast hm
      linear_combination -((θ : ℂ) * Complex.I) * hm_C
    have hI2 : (-Complex.I) * Complex.I = 1 := by simp
    have hρ_zpow : (ρ : ℂ) ^ (N : ℤ) = (ρ : ℂ) ^ N := zpow_natCast (ρ : ℂ) N
    rw [hρ_zpow]
    calc
      (ρ : ℂ) ^ N * Complex.exp ((N : ℂ) * ((θ : ℂ) * Complex.I)) *
          K ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I))
          = (ρ : ℂ) ^ N * (Complex.exp ((N : ℂ) * ((θ : ℂ) * Complex.I)) *
              Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I))) *
              K ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by ring
      _ = (ρ : ℂ) ^ N * (Complex.exp ((q : ℂ) * ((θ : ℂ) * Complex.I)) *
            Complex.exp ((θ : ℂ) * Complex.I)) *
            K ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by rw [hexp_id]
      _ = (-Complex.I * ((ρ : ℂ) ^ N * ((ρ : ℂ) ^ (q + 1))⁻¹)) *
            (((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) *
              ((ρ : ℂ) ^ q * Complex.exp ((q : ℂ) * ((θ : ℂ) * Complex.I)) *
                K ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))) := by
            have hρ_canc : ((ρ : ℂ) ^ (q + 1))⁻¹ * ((ρ : ℂ) * (ρ : ℂ) ^ q) = 1 := by
              rw [← pow_succ', inv_mul_cancel₀ (pow_ne_zero (q + 1) hρ_ne)]
            calc
              (ρ : ℂ) ^ N * (Complex.exp ((q : ℂ) * ((θ : ℂ) * Complex.I)) *
                  Complex.exp ((θ : ℂ) * Complex.I)) *
                  K ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
                  = ((-Complex.I) * Complex.I) * (((ρ : ℂ) ^ (q + 1))⁻¹ * ((ρ : ℂ) * (ρ : ℂ) ^ q)) *
                      ((ρ : ℂ) ^ N * (Complex.exp ((q : ℂ) * ((θ : ℂ) * Complex.I)) *
                        Complex.exp ((θ : ℂ) * Complex.I)) *
                        K ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := by
                      rw [hI2, hρ_canc, one_mul, one_mul]
              _ = (-Complex.I * ((ρ : ℂ) ^ N * ((ρ : ℂ) ^ (q + 1))⁻¹)) *
                    (((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) *
                      ((ρ : ℂ) ^ q * Complex.exp ((q : ℂ) * ((θ : ℂ) * Complex.I)) *
                        K ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))) := by ring
  simp_rw [hpt, intervalIntegral.integral_const_mul]
  change (-Complex.I * ((ρ : ℂ) ^ (N : ℤ) * ((ρ : ℂ) ^ (q + 1))⁻¹)) *
      (∮ z in C(0, ρ), g z) = 0
  rw [hcauchy, mul_zero]

/-- Any open punctured disc `{z | 0 < ‖z‖ < R}` (`R > 0`) is a plane region, and the exterior
`{w : ℂ | 1 < ‖w‖} = (closedBall 0 1)ᶜ` is connected. -/
theorem puncturedBall_isRegion {R : ℝ} (hR : 0 < R) :
    RudinRCA.Chapter10.IsRegion (ball (0 : ℂ) R \ {0}) := by
  refine ⟨isOpen_ball.sdiff isClosed_singleton, ?_⟩
  let polar : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)
  have hcont : Continuous polar :=
    (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hIoo_conn : IsConnected (Ioo (0 : ℝ) R) :=
    ⟨⟨R / 2, by constructor <;> linarith⟩, (convex_Ioo 0 R).isPreconnected⟩
  have hconn_dom : IsConnected (Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ)) :=
    hIoo_conn.prod isConnected_univ
  have himg : polar '' (Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ)) = ball (0 : ℂ) R \ {0} := by
    ext z
    constructor
    · rintro ⟨⟨r, θ⟩, ⟨⟨hr0, hrR⟩, _⟩, rfl⟩
      dsimp [polar]
      have hnorm : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      refine ⟨mem_ball_zero_iff.mpr (by rw [hnorm]; exact hrR), ?_⟩
      intro h0
      rw [Set.mem_singleton_iff] at h0
      rw [h0, norm_zero] at hnorm
      linarith
    · rintro ⟨hzR, hz0⟩
      have hz_ne : z ≠ 0 := by rwa [Set.mem_singleton_iff] at hz0
      refine ⟨(‖z‖, Complex.arg z), ⟨⟨norm_pos_iff.mpr hz_ne, mem_ball_zero_iff.mp hzR⟩, trivial⟩, ?_⟩
      exact Complex.norm_mul_exp_arg_mul_I z
  rw [← himg]
  exact hconn_dom.image polar hcont.continuousOn

theorem isConnected_compl_closedUnitBall :
    IsConnected ((closedBall (0 : ℂ) 1)ᶜ) := by
  let polar : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)
  have hcont : Continuous polar :=
    (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hIoi_conn : IsConnected (Ioi (1 : ℝ)) :=
    ⟨⟨2, by norm_num⟩, (convex_Ioi (1 : ℝ)).isPreconnected⟩
  have hconn_dom : IsConnected (Ioi (1 : ℝ) ×ˢ (univ : Set ℝ)) :=
    hIoi_conn.prod isConnected_univ
  have himg : polar '' (Ioi (1 : ℝ) ×ˢ (univ : Set ℝ)) = (closedBall (0 : ℂ) 1)ᶜ := by
    ext z
    constructor
    · rintro ⟨⟨r, θ⟩, ⟨hr1, _⟩, rfl⟩
      have hr1' : 1 < r := hr1
      dsimp [polar]
      rw [Set.mem_compl_iff, mem_closedBall_zero_iff, not_le, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith : 0 < r), Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hr1'
    · intro hz
      rw [Set.mem_compl_iff, mem_closedBall_zero_iff, not_le] at hz
      refine ⟨(‖z‖, Complex.arg z), ⟨hz, trivial⟩, Complex.norm_mul_exp_arg_mul_I z⟩
  rw [← himg]
  exact hconn_dom.image polar hcont.continuousOn

/-- **Theorem 14.13 (The Area Theorem and Unnumbered Corollary, RCA pp. 286–287):**
Let `F` be holomorphic and injective on the punctured unit disc `U \ {0}`, with Laurent expansion
`F(z) = z⁻¹ + ∑_{n=0}^∞ a_n z^n` convergent throughout `U \ {0}` (so `F(z) → ∞` in `S²` as
`z → 0`). Then:
1. `∑_{n=1}^∞ n ‖a_n‖^2` is summable and `∑' k : ℕ, ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 ≤ 1`
   (and every finite partial sum `∑_{k=0}^{N-1} (k + 1) ‖a_{k+1}‖^2 ≤ 1`);
2. *(Unnumbered Corollary, p. 287)* `‖a 1‖ ≤ 1`;
3. *(Sharpness, p. 287)* For every `α : ℂ` with `‖α‖ ≤ 1`, `F_α(z) = z⁻¹ + α z` is holomorphic
   and injective on `U \ {0}` with Laurent coefficient `a 1 = α`. -/
theorem theorem14_13 :
    (∀ {F : ℂ → ℂ} {a : ℕ → ℂ},
      RudinRCA.Chapter10.HolomorphicOn F (ball (0 : ℂ) 1 \ {0}) →
      InjOn F (ball (0 : ℂ) 1 \ {0}) →
      (∀ z ∈ ball (0 : ℂ) 1 \ {0}, HasSum (fun n : ℕ => a n * z ^ n) (F z - z⁻¹)) →
      Tendsto (fun z : ℂ => (F z : RiemannSphere)) (𝓝[≠] 0) (𝓝 (∞ : RiemannSphere)) ∧
      (∀ N : ℕ, (∑ k ∈ Finset.range N, ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2) ≤ 1) ∧
      Summable (fun k : ℕ => ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2) ∧
      (∑' k : ℕ, ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2) ≤ 1 ∧
      ‖a 1‖ ≤ 1) ∧
    (∀ {α : ℂ}, ‖α‖ ≤ 1 →
      RudinRCA.Chapter10.HolomorphicOn (fun z : ℂ => z⁻¹ + α * z) (ball (0 : ℂ) 1 \ {0}) ∧
      InjOn (fun z : ℂ => z⁻¹ + α * z) (ball (0 : ℂ) 1 \ {0}) ∧
      ∀ z ∈ ball (0 : ℂ) 1 \ {0},
        HasSum (fun n : ℕ => (if n = 1 then α else 0) * z ^ n) ((z⁻¹ + α * z) - z⁻¹)) := by
  refine ⟨?_, ?_⟩
  · intro F a hF_holo hF_inj ha_sum
    -- Step 1: Extend `F(z) - z⁻¹` holomorphically to `G₀` on `ball 0 1`, then subtract `a 0`
    let G₀ : ℂ → ℂ := fun z => if z = 0 then a 0 else F z - z⁻¹
    have hG₀_sum : ∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n : ℕ => a n * z ^ n) (G₀ z) := by
      intro z hz
      by_cases hz0 : z = 0
      · subst hz0
        simp only [G₀, ↓reduceIte]
        have hs := hasSum_single (f := fun n : ℕ => a n * (0 : ℂ) ^ n) 0
          (fun n hn => by rw [zero_pow hn, mul_zero])
        simpa using hs
      · simp only [G₀, hz0, ↓reduceIte]
        exact ha_sum z ⟨hz, hz0⟩
    have hG₀_holo : RudinRCA.Chapter10.HolomorphicOn G₀ (ball (0 : ℂ) 1) := by
      intro z hz
      by_cases hz0 : z = 0
      · subst hz0
        have hs : HasFPowerSeriesAt G₀ (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
          rw [hasFPowerSeriesAt_iff']
          filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with w hw
          simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm, sub_zero]
            using hG₀_sum w hw
        exact hs.analyticAt.differentiableAt
      · have hd : DifferentiableAt ℂ (fun w : ℂ => F w - w⁻¹) z :=
          (hF_holo z ⟨hz, hz0⟩).sub (differentiableAt_id.inv hz0)
        have hev : (fun w : ℂ => F w - w⁻¹) =ᶠ[𝓝 z] G₀ := by
          filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz, hz0⟩] with w hw
          have hw0 : w ≠ 0 := hw.2
          simp [G₀, hw0]
        exact hd.congr_of_eventuallyEq hev.symm
    -- Pole behavior `F(z) → ∞` in `S²` as `z → 0` (`z ≠ 0`)
    have hpole : Tendsto (fun z : ℂ => (F z : RiemannSphere)) (𝓝[≠] 0) (𝓝 (∞ : RiemannSphere)) := by
      rw [Filter.tendsto_iff_forall_eventually_mem]
      intro V hV
      obtain ⟨M, hM_pos, hMV⟩ := mem_nhds_infinity_iff.mp hV
      have hG₀_cont : ContinuousAt G₀ 0 :=
        (hG₀_holo 0 (Metric.mem_ball_self zero_lt_one)).continuousAt
      have hG₀_near : ∀ᶠ z in 𝓝 (0 : ℂ), ‖G₀ z - G₀ 0‖ < 1 := by
        filter_upwards [hG₀_cont.tendsto (Metric.ball_mem_nhds (G₀ 0) zero_lt_one)] with z hz
        simpa [dist_eq_norm] using hz
      let δ_p : ℝ := min (1 / 2) ((M + ‖G₀ 0‖ + 2)⁻¹)
      have hδp_pos : 0 < δ_p := by
        dsimp [δ_p]
        exact lt_min (by norm_num) (inv_pos.mpr (by positivity))
      filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hδp_pos),
        nhdsWithin_le_nhds hG₀_near, self_mem_nhdsWithin] with z hz_ball hz_G hz_ne
      apply hMV
      rw [coe_mem_infinityDisc]
      have hz_lt1 : z ∈ ball (0 : ℂ) 1 :=
        Metric.ball_subset_ball (min_le_left _ _ |>.trans (by norm_num)) hz_ball
      have hFz_eq : F z = z⁻¹ + G₀ z := by
        have hz0 : z ≠ 0 := hz_ne
        have : G₀ z = F z - z⁻¹ := by simp [G₀, hz0]
        linear_combination -this
      have hG_bound : ‖G₀ z‖ < ‖G₀ 0‖ + 1 := by
        calc
          ‖G₀ z‖ = ‖(G₀ z - G₀ 0) + G₀ 0‖ := by ring_nf
          _ ≤ ‖G₀ z - G₀ 0‖ + ‖G₀ 0‖ := norm_add_le _ _
          _ < 1 + ‖G₀ 0‖ := by linarith
          _ = ‖G₀ 0‖ + 1 := by ring
      have hz_norm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
      have hz_norm_lt : ‖z‖ < (M + ‖G₀ 0‖ + 2)⁻¹ :=
        (mem_ball_zero_iff.mp hz_ball).trans_le (min_le_right _ _)
      have hinv_gt : M + ‖G₀ 0‖ + 2 < ‖z⁻¹‖ := by
        rw [norm_inv]
        simpa only [inv_inv] using inv_strictAnti₀ hz_norm_pos hz_norm_lt
      have htri : ‖z⁻¹‖ ≤ ‖F z‖ + ‖G₀ z‖ := by
        have : z⁻¹ = F z - G₀ z := by linear_combination -hFz_eq
        calc
          ‖z⁻¹‖ = ‖F z - G₀ z‖ := by rw [this]
          _ ≤ ‖F z‖ + ‖G₀ z‖ := norm_sub_le _ _
      linarith
    -- Normalize `a 0 = 0` by replacing `F` with `F₁(z) = F(z) - a 0`
    let F₁ : ℂ → ℂ := fun z => F z - a 0
    let G : ℂ → ℂ := fun z => G₀ z - a 0
    let a₁ : ℕ → ℂ := fun n => if n = 0 then 0 else a n
    have hF₁_holo : RudinRCA.Chapter10.HolomorphicOn F₁ (ball (0 : ℂ) 1 \ {0}) :=
      fun z hz => (hF_holo z hz).sub (differentiableAt_const (a 0))
    have hF₁_inj : InjOn F₁ (ball (0 : ℂ) 1 \ {0}) := by
      intro z₁ hz₁ z₂ hz₂ heq
      dsimp [F₁] at heq
      exact hF_inj hz₁ hz₂ (sub_left_inj.mp heq)
    have hG_holo : RudinRCA.Chapter10.HolomorphicOn G (ball (0 : ℂ) 1) :=
      fun z hz => (hG₀_holo z hz).sub (differentiableAt_const (a 0))
    have hG_sum : ∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n : ℕ => a₁ n * z ^ n) (G z) := by
      intro z hz
      have h0_sum : HasSum (fun n : ℕ => (if n = 0 then a 0 else 0) * z ^ n) (a 0) := by
        have hs := hasSum_single (f := fun n : ℕ => (if n = 0 then a 0 else 0) * z ^ n) 0
          (fun n hn => by simp [hn])
        simpa using hs
      convert (hG₀_sum z hz).sub h0_sum using 1
      ext n
      by_cases hn : n = 0 <;> simp [a₁, hn] <;> ring
    have hF₁_eq : ∀ z ∈ ball (0 : ℂ) 1 \ {0}, F₁ z = z⁻¹ + G z := by
      intro z hz
      have hz0 : z ≠ 0 := hz.2
      dsimp [F₁, G, G₀]
      simp only [hz0, ↓reduceIte]
      ring
    -- Write `G(z) = a 1 * z + g(z)` with `‖g(z)‖ ≤ C * ‖z‖^2` on `closedBall 0 (1/2)`
    let g : ℂ → ℂ := fun z => G z - a 1 * z
    have hg_holo : RudinRCA.Chapter10.HolomorphicOn g (ball (0 : ℂ) 1) :=
      fun z hz => (hG_holo z hz).sub ((differentiableAt_const (a 1)).mul differentiableAt_id)
    have hg0 : g 0 = 0 := by
      dsimp [g, G, G₀]
      simp
    have hdg0 : deriv g 0 = 0 := by
      have hG_rep : ∀ z ∈ RudinRCA.Chapter10.disc 0 1,
          HasSum (fun n : ℕ => a₁ n * (z - 0) ^ n) (G z) := by
        intro z hz; simpa [sub_zero] using hG_sum z hz
      have hdG0 := RudinRCA.Chapter10.powerSeries_coefficient zero_lt_one hG_rep 1
      simp only [Nat.factorial_one, Nat.cast_one, one_mul, iteratedDeriv_one, a₁,
        one_ne_zero, ↓reduceIte] at hdG0
      have hd_sub := (hG_holo 0 (Metric.mem_ball_self zero_lt_one)).hasDerivAt.sub
        ((hasDerivAt_id (0 : ℂ)).const_mul (a 1))
      exact (hd_sub.congr_deriv (by rw [← hdG0]; ring)).deriv
    let g₁ : ℂ → ℂ := dslope g 0
    have hg₁_diff : DifferentiableOn ℂ g₁ (ball (0 : ℂ) 1) :=
      (Complex.differentiableOn_dslope (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)).mpr
        ((RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn isOpen_ball).mp hg_holo)
    have hg₁0 : g₁ 0 = 0 := by simp [g₁, dslope_same, hdg0]
    let g₂ : ℂ → ℂ := dslope g₁ 0
    have hg₂_diff : DifferentiableOn ℂ g₂ (ball (0 : ℂ) 1) :=
      (Complex.differentiableOn_dslope (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)).mpr hg₁_diff
    have hg_eq_sq : ∀ z : ℂ, g z = z ^ 2 * g₂ z := by
      intro z
      have h1 := sub_smul_dslope g 0 z
      have h2 := sub_smul_dslope g₁ 0 z
      simp only [g₁, hg0, hg₁0, sub_zero, smul_eq_mul] at h1 h2
      rw [← h1, ← h2]
      ring
    have hK_half_sub : closedBall (0 : ℂ) (1 / 2) ⊆ ball (0 : ℂ) 1 :=
      Metric.closedBall_subset_ball (by norm_num)
    have hg₂_cont : ContinuousOn (fun z => ‖g₂ z‖) (closedBall (0 : ℂ) (1 / 2)) :=
      continuous_norm.comp_continuousOn (hg₂_diff.continuousOn.mono hK_half_sub)
    obtain ⟨z_max, _, hz_max⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_isMaxOn
      ⟨0, Metric.mem_closedBall_self (by norm_num)⟩ hg₂_cont
    let C : ℝ := max (‖g₂ z_max‖) 1
    have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hg_quad : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), ‖g z‖ ≤ C * ‖z‖ ^ 2 := by
      intro z hz
      rw [hg_eq_sq z, norm_mul, norm_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right
        ((hz_max hz).trans (le_max_left _ _)) (sq_nonneg _)
    -- Step 2: Prove every finite partial sum `∑_{k < N} (k + 1) ‖a_{k+1}‖^2 ≤ 1`
    obtain ⟨rot, hrot_norm, hrot_sq⟩ := exists_unit_sq_direction (a 1)
    have hrot_ne : rot ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hrot_norm; exact zero_ne_one hrot_norm
    have hrot_conj : rot * starRingEnd ℂ rot = 1 := by
      rw [mul_comm, Complex.conj_mul', hrot_norm]; norm_num
    have hpartial : ∀ N : ℕ, (∑ k ∈ Finset.range N, ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2) ≤ 1 := by
      intro N
      -- Decompose `G(z) = ∑_{k=0}^N a₁_k z^k + z^{N+1} H_N(z)` on `ball 0 1`
      let H_N : ℂ → ℂ := fun z =>
        if z = 0 then a₁ (N + 1)
        else (G z - ∑ k ∈ Finset.range (N + 1), a₁ k * z ^ k) / z ^ (N + 1)
      have hHN_sum : ∀ z ∈ ball (0 : ℂ) 1,
          HasSum (fun k : ℕ => a₁ (k + (N + 1)) * z ^ k) (H_N z) := by
        intro z hz
        by_cases hz0 : z = 0
        · subst hz0
          simp only [H_N, ↓reduceIte]
          have hs := hasSum_single (f := fun k : ℕ => a₁ (k + (N + 1)) * (0 : ℂ) ^ k) 0
            (fun k hk => by rw [zero_pow hk, mul_zero])
          simpa using hs
        · simp only [H_N, hz0, ↓reduceIte]
          have hshift := (hasSum_nat_add_iff' (N + 1)).mpr (hG_sum z hz)
          have hmul := hshift.mul_right ((z ^ (N + 1))⁻¹)
          convert hmul using 1
          · ext k
            field_simp [pow_ne_zero (N + 1) hz0]
            rw [pow_add]
            ring
          · rw [div_eq_mul_inv]
      have hHN_holo : RudinRCA.Chapter10.HolomorphicOn H_N (ball (0 : ℂ) 1) := by
        intro z hz
        by_cases hz0 : z = 0
        · subst hz0
          have hs : HasFPowerSeriesAt H_N
              (FormalMultilinearSeries.ofScalars ℂ (fun k => a₁ (k + (N + 1)))) 0 := by
            rw [hasFPowerSeriesAt_iff']
            filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with w hw
            simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm, sub_zero]
              using hHN_sum w hw
          exact hs.analyticAt.differentiableAt
        · have hpoly_diff : DifferentiableAt ℂ
              (fun w : ℂ => ∑ k ∈ Finset.range (N + 1), a₁ k * w ^ k) z := by
            refine DifferentiableAt.fun_sum fun k _ => ?_
            exact (differentiableAt_const (a₁ k)).mul (differentiableAt_id.pow k)
          have hd : DifferentiableAt ℂ
              (fun w : ℂ => (G w - ∑ k ∈ Finset.range (N + 1), a₁ k * w ^ k) / w ^ (N + 1)) z :=
            ((hG_holo z hz).sub hpoly_diff).div (differentiableAt_id.pow (N + 1))
              (pow_ne_zero (N + 1) hz0)
          have hev : (fun w : ℂ =>
              (G w - ∑ k ∈ Finset.range (N + 1), a₁ k * w ^ k) / w ^ (N + 1)) =ᶠ[𝓝 z] H_N := by
            filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz, hz0⟩] with w hw
            have hw0 : w ≠ 0 := hw.2
            simp [H_N, hw0]
          exact hd.congr_of_eventuallyEq hev.symm
      have hG_split : ∀ z ∈ ball (0 : ℂ) 1,
          G z = (∑ k ∈ Finset.range (N + 1), a₁ k * z ^ k) + z ^ (N + 1) * H_N z := by
        intro z hz
        by_cases hz0 : z = 0
        · subst hz0
          have h0 : G 0 = 0 := by simp [G, G₀]
          rw [h0, zero_pow (Nat.succ_ne_zero N), zero_mul, add_zero, Finset.sum_range_succ']
          simp [a₁]
        · dsimp [H_N]
          simp only [hz0, ↓reduceIte]
          rw [mul_div_cancel₀ _ (pow_ne_zero (N + 1) hz0)]
          ring
      let K_N : ℂ → ℂ := fun z => ((N + 1 : ℕ) : ℂ) * H_N z + z * deriv H_N z
      have hKN_holo : RudinRCA.Chapter10.HolomorphicOn K_N (ball (0 : ℂ) 1) := by
        have hdH := RudinRCA.Chapter10.holomorphicOn_deriv isOpen_ball hHN_holo
        exact fun z hz => ((differentiableAt_const _).mul (hHN_holo z hz)).add
          (differentiableAt_id.mul (hdH z hz))
      have hderiv_F₁ : ∀ z ∈ ball (0 : ℂ) 1 \ {0},
          deriv F₁ z = -(z ^ 2)⁻¹ +
            (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℂ) * a (k + 1) * z ^ k) +
            z ^ N * K_N z := by
        intro z hz
        have hev : F₁ =ᶠ[𝓝 z] fun w =>
            w⁻¹ + (∑ k ∈ Finset.range (N + 1), a₁ k * w ^ k) + w ^ (N + 1) * H_N w := by
          filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds hz] with w hw
          rw [hF₁_eq w hw, hG_split w hw.1, add_assoc]
        rw [hev.deriv_eq]
        have hd_inv : HasDerivAt (fun w : ℂ => w⁻¹) (-(z ^ 2)⁻¹) z := hasDerivAt_inv hz.2
        have hd_sum : HasDerivAt (fun w : ℂ => ∑ k ∈ Finset.range (N + 1), a₁ k * w ^ k)
            (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℂ) * a (k + 1) * z ^ k) z := by
          have h1 := HasDerivAt.fun_sum (u := Finset.range (N + 1))
            (fun k _ => ((hasDerivAt_id z).pow k).const_mul (a₁ k))
          refine h1.congr_deriv ?_
          rw [Finset.sum_range_succ']
          simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, mul_one, id_eq]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [a₁, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
          push_cast
          ring
        have hd_tail := (((hasDerivAt_id z).pow (N + 1)).mul (hHN_holo z hz.1).hasDerivAt).congr_deriv
          (show ↑(N + 1) * id z ^ (N + 1 - 1) * 1 * H_N z + id z ^ (N + 1) * deriv H_N z =
              z ^ N * K_N z by
            dsimp [K_N]
            rw [pow_succ]
            push_cast
            ring)
        exact ((hd_inv.add hd_sum).add hd_tail).deriv
      -- Step 2a: Take `ε → 0+` then `R → 1-` on `∑_{k < N} (k + 1) ‖a_{k+1}‖^2 R^{2(k+1)} ≤ R⁻²`
      suffices hR_bound : ∀ R ∈ Ioo (0 : ℝ) 1,
          (∑ k ∈ Finset.range N, ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 * R ^ (2 * (k + 1))) ≤ R⁻¹ ^ 2 by
        have hlim_lhs : Tendsto (fun R : ℝ =>
            ∑ k ∈ Finset.range N, ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 * R ^ (2 * (k + 1)))
            (𝓝[<] (1 : ℝ))
            (𝓝 (∑ k ∈ Finset.range N, ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2)) := by
          have hc : ContinuousAt (fun R : ℝ =>
              ∑ k ∈ Finset.range N, ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 * R ^ (2 * (k + 1))) 1 :=
            Continuous.continuousAt (continuous_finset_sum _ fun k _ =>
              continuous_const.mul (continuous_pow _))
          simpa [one_pow, mul_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
        have hlim_rhs : Tendsto (fun R : ℝ => R⁻¹ ^ 2) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
          have hc : ContinuousAt (fun R : ℝ => R⁻¹ ^ 2) 1 :=
            (continuousAt_id.inv₀ one_ne_zero).pow 2
          simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
        have hev_R : ∀ᶠ R in 𝓝[<] (1 : ℝ),
            (∑ k ∈ Finset.range N, ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 * R ^ (2 * (k + 1))) ≤
              R⁻¹ ^ 2 := by
          filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with R hR
          exact hR_bound R hR
        exact le_of_tendsto_of_tendsto hlim_lhs hlim_rhs hev_R
      intro R ⟨hR0, hR1⟩
      -- Fix small `ε_max > 0` so that for all `0 < ε < ε_max`:
      -- `ε < R`, `ε ≤ 1/2`, and `(‖a 1‖ + 1) * ε ^ 2 < 1 / 2`
      let ε_max : ℝ := min R (min (1 / 2) ((2 * (‖a 1‖ + 1))⁻¹))
      have hε_max_pos : 0 < ε_max := by
        dsimp [ε_max]
        exact lt_min hR0 (lt_min (by norm_num) (inv_pos.mpr (by positivity)))
      suffices hε_bound : ∀ ε ∈ Ioo (0 : ℝ) ε_max,
          (∑ k ∈ Finset.range N,
            ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 * (R ^ (2 * (k + 1)) - ε ^ (2 * (k + 1)))) ≤
            R⁻¹ ^ 2 + 6 * C * ε + 9 * C ^ 2 * ε ^ 4 by
        have hlim_l : Tendsto (fun ε : ℝ =>
            ∑ k ∈ Finset.range N,
              ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 * (R ^ (2 * (k + 1)) - ε ^ (2 * (k + 1))))
            (𝓝[>] (0 : ℝ))
            (𝓝 (∑ k ∈ Finset.range N, ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 * R ^ (2 * (k + 1)))) := by
          have hc : ContinuousAt (fun ε : ℝ =>
              ∑ k ∈ Finset.range N,
                ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 * (R ^ (2 * (k + 1)) - ε ^ (2 * (k + 1)))) 0 :=
            Continuous.continuousAt (continuous_finset_sum _ fun k _ =>
              continuous_const.mul (continuous_const.sub (continuous_pow _)))
          have hval0 : (∑ k ∈ Finset.range N,
              ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 * (R ^ (2 * (k + 1)) - (0 : ℝ) ^ (2 * (k + 1)))) =
              ∑ k ∈ Finset.range N, ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 * R ^ (2 * (k + 1)) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [zero_pow (by omega), sub_zero]
          rw [← hval0]
          exact hc.tendsto.mono_left nhdsWithin_le_nhds
        have hlim_r : Tendsto (fun ε : ℝ => R⁻¹ ^ 2 + 6 * C * ε + 9 * C ^ 2 * ε ^ 4)
            (𝓝[>] (0 : ℝ)) (𝓝 (R⁻¹ ^ 2)) := by
          have hc : ContinuousAt (fun ε : ℝ => R⁻¹ ^ 2 + 6 * C * ε + 9 * C ^ 2 * ε ^ 4) 0 :=
            Continuous.continuousAt
              ((continuous_const.add (continuous_const.mul continuous_id)).add
                (continuous_const.mul (continuous_pow 4)))
          simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
        have hev_ε : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
            (∑ k ∈ Finset.range N,
              ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 * (R ^ (2 * (k + 1)) - ε ^ (2 * (k + 1)))) ≤
              R⁻¹ ^ 2 + 6 * C * ε + 9 * C ^ 2 * ε ^ 4 := by
          filter_upwards [Ioo_mem_nhdsGT hε_max_pos] with ε hε
          exact hε_bound ε hε
        exact le_of_tendsto_of_tendsto hlim_l hlim_r hev_ε
      intro ε ⟨hε0, hε_lt_max⟩
      have hεR : ε < R := hε_lt_max.trans_le (min_le_left _ _)
      have hε_half : ε ≤ 1 / 2 :=
        hε_lt_max.le.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hε_small : ε < (2 * (‖a 1‖ + 1))⁻¹ :=
        hε_lt_max.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      have ha1_ε : ‖a 1‖ * ε < (1 / 2) * ε⁻¹ := by
        have h1 : 2 * (‖a 1‖ + 1) * ε < 1 := by
          calc
            2 * (‖a 1‖ + 1) * ε < 2 * (‖a 1‖ + 1) * (2 * (‖a 1‖ + 1))⁻¹ :=
                mul_lt_mul_of_pos_left hε_small (by positivity)
            _ = 1 := mul_inv_cancel₀ (by positivity)
        have h2 : 2 * ‖a 1‖ * ε < 1 := by nlinarith [norm_nonneg (a 1), hε0]
        have h3 : 2 * ‖a 1‖ * ε ^ 2 < 1 := by
          have hε_le1 : ε ≤ 1 := by linarith
          nlinarith [norm_nonneg (a 1), hε0]
        have h4 : ‖a 1‖ * ε * ε < (1 / 2) := by linarith
        rw [← div_eq_mul_inv, lt_div_iff₀ hε0]
        exact h4
      -- Step 2b: Construct the bounding ellipse `ℰ_ε = L_ε '' closedBall 0 1`
      let A₀ : ℝ := ε⁻¹ + ‖a 1‖ * ε
      let B₀ : ℝ := ε⁻¹ - ‖a 1‖ * ε
      have hB₀_half : (1 / 2) * ε⁻¹ < B₀ := by dsimp [B₀]; linarith
      have hB₀_pos : 0 < B₀ := lt_trans (by positivity) hB₀_half
      have hA₀_pos : 0 < A₀ := by dsimp [A₀]; positivity
      have hB₀_le_A₀ : B₀ ≤ A₀ := by dsimp [A₀, B₀]; linarith [ mul_nonneg (norm_nonneg (a 1)) hε0.le ]
      let s_ε : ℝ := 1 + 3 * C * ε ^ 3
      have hsε_gt1 : 1 < s_ε := by dsimp [s_ε]; linarith [show 0 < 3 * C * ε ^ 3 by positivity]
      have hsε_pos : 0 < s_ε := lt_trans zero_lt_one hsε_gt1
      let A : ℝ := s_ε * A₀
      let B : ℝ := s_ε * B₀
      have hA_pos : 0 < A := mul_pos hsε_pos hA₀_pos
      have hB_pos : 0 < B := mul_pos hsε_pos hB₀_pos
      let L₀ := ellipseLinearEquiv rot hrot_norm hA₀_pos hB₀_pos
      let L_ε := ellipseLinearEquiv rot hrot_norm hA_pos hB_pos
      -- Show `F₁ '' sphere 0 ε ⊆ L_ε '' closedBall 0 1`
      have hsphere_in_ℰ : ∀ z ∈ sphere (0 : ℂ) ε,
          F₁ z ∈ L_ε '' closedBall (0 : ℂ) 1 := by
        intro z hz
        rw [mem_sphere_zero_iff_norm] at hz
        have hz_ne : z ≠ 0 := by intro h0; rw [h0, norm_zero] at hz; linarith
        have hz_ball1 : z ∈ ball (0 : ℂ) 1 := by
          rw [mem_ball_zero_iff, hz]; linarith
        have hz_half : z ∈ closedBall (0 : ℂ) (1 / 2) := by
          rw [mem_closedBall_zero_iff, hz]; exact hε_half
        refine ⟨L_ε.symm (F₁ z), ?_, L_ε.apply_symm_apply (F₁ z)⟩
        rw [mem_closedBall_zero_iff]
        -- Relate `L_ε.symm w = s_ε⁻¹ • L₀.symm w`
        have hL_rel : L_ε.symm (F₁ z) = (s_ε⁻¹ : ℝ) • L₀.symm (F₁ z) := by
          dsimp [L_ε, L₀]
          rw [ellipseLinearEquiv_symm_apply, ellipseLinearEquiv_symm_apply]
          apply Complex.ext <;> simp [A, B, div_mul_eq_div_div] <;> ring
        rw [hL_rel, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsε_pos)]
        -- Decompose `F₁ z = (z⁻¹ + a 1 * z) + g z`
        have hF₁_decomp : F₁ z = (z⁻¹ + a 1 * z) + g z := by
          rw [hF₁_eq z ⟨hz_ball1, hz_ne⟩]
          dsimp [g]; ring
        have hlin_split : L₀.symm (F₁ z) = L₀.symm (z⁻¹ + a 1 * z) + L₀.symm (g z) := by
          rw [hF₁_decomp, map_add]
        -- Compute `‖L₀.symm (z⁻¹ + a 1 * z)‖ = 1`
        let u : ℂ := z * rot / (ε : ℂ)
        have hε_ne : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε0.ne'
        have hu_norm : ‖u‖ = 1 := by
          dsimp [u]
          rw [norm_div, norm_mul, hz, hrot_norm, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hε0, div_self hε0.ne']
        have hu_ne : u ≠ 0 := by intro h0; rw [h0, norm_zero] at hu_norm; exact zero_ne_one hu_norm
        have hu_inv : u⁻¹ = starRingEnd ℂ u := by
          apply mul_left_cancel₀ hu_ne
          rw [mul_inv_cancel₀ hu_ne, Complex.mul_conj', hu_norm]
          norm_num
        have hz_u : z = (ε : ℂ) * u * starRingEnd ℂ rot := by
          dsimp [u]
          calc
            z = (z * rot / (ε : ℂ)) * (ε : ℂ) * starRingEnd ℂ rot := by
                rw [div_mul_cancel₀ _ hε_ne, mul_assoc, hrot_conj, mul_one]
            _ = (ε : ℂ) * (z * rot / (ε : ℂ)) * starRingEnd ℂ rot := by ring
        have hzinv_u : z⁻¹ = ((ε⁻¹ : ℝ) : ℂ) * starRingEnd ℂ u * rot := by
          apply mul_left_cancel₀ hz_ne
          rw [mul_inv_cancel₀ hz_ne]
          conv_rhs => rw [hz_u]
          have hε_mul : (ε : ℂ) * ((ε⁻¹ : ℝ) : ℂ) = 1 := by
            push_cast; exact mul_inv_cancel₀ hε_ne
          have hu_conj : u * starRingEnd ℂ u = 1 := by
            rw [Complex.mul_conj', hu_norm]; norm_num
          calc
            1 = ((ε : ℂ) * ((ε⁻¹ : ℝ) : ℂ)) * (u * starRingEnd ℂ u) *
                (starRingEnd ℂ rot * rot) := by
                rw [hε_mul, hu_conj, mul_comm (starRingEnd ℂ rot) rot, hrot_conj]; ring
            _ = (ε : ℂ) * u * starRingEnd ℂ rot *
                (((ε⁻¹ : ℝ) : ℂ) * starRingEnd ℂ u * rot) := by ring
        have hmain_rot : (z⁻¹ + a 1 * z) * starRingEnd ℂ rot =
            ((A₀ * u.re : ℝ) : ℂ) + (((-B₀ * u.im : ℝ) : ℂ) * Complex.I) := by
          have ha1_z : a 1 * z * starRingEnd ℂ rot = ((‖a 1‖ * ε : ℝ) : ℂ) * u := by
            conv_lhs => rw [← hrot_sq, hz_u]
            have hrr : rot ^ 2 * starRingEnd ℂ rot * starRingEnd ℂ rot = 1 := by
              calc
                rot ^ 2 * starRingEnd ℂ rot * starRingEnd ℂ rot
                    = (rot * starRingEnd ℂ rot) * (rot * starRingEnd ℂ rot) := by ring
                _ = 1 := by rw [hrot_conj, mul_one]
            calc
              (‖a 1‖ : ℂ) * rot ^ 2 * ((ε : ℂ) * u * starRingEnd ℂ rot) * starRingEnd ℂ rot
                  = ((‖a 1‖ : ℂ) * (ε : ℂ)) * u *
                      (rot ^ 2 * starRingEnd ℂ rot * starRingEnd ℂ rot) := by ring
              _ = ((‖a 1‖ * ε : ℝ) : ℂ) * u := by rw [hrr, mul_one]; push_cast; rfl
          have hzinv_rot : z⁻¹ * starRingEnd ℂ rot = ((ε⁻¹ : ℝ) : ℂ) * starRingEnd ℂ u := by
            rw [hzinv_u, mul_assoc, hrot_conj, mul_one]
          rw [add_mul, hzinv_rot, ha1_z]
          apply Complex.ext
          · simp [A₀]; ring
          · simp [B₀]; ring
        have hL₀_main : L₀.symm (z⁻¹ + a 1 * z) = starRingEnd ℂ u := by
          dsimp [L₀]
          rw [ellipseLinearEquiv_symm_apply, hmain_rot]
          apply Complex.ext <;> (simp; field_simp [hA₀_pos.ne', hB₀_pos.ne'])
        have hnorm_main : ‖L₀.symm (z⁻¹ + a 1 * z)‖ = 1 := by
          rw [hL₀_main, Complex.norm_conj, hu_norm]
        -- Bound `‖L₀.symm (g z)‖ ≤ 2 * C * ε ^ 3`
        have hnorm_err : ‖L₀.symm (g z)‖ ≤ 2 * C * ε ^ 3 := by
          dsimp [L₀]
          rw [ellipseLinearEquiv_symm_apply]
          set w : ℂ := g z * starRingEnd ℂ rot
          have hw_norm : ‖w‖ ≤ C * ε ^ 2 := by
            dsimp [w]
            rw [norm_mul, Complex.norm_conj, hrot_norm, mul_one, ← hz]
            exact hg_quad z hz_half
          have hre_div : |w.re / A₀| ≤ |w.re / B₀| := by
            rw [abs_div, abs_div, abs_of_pos hA₀_pos, abs_of_pos hB₀_pos]
            exact div_le_div_of_nonneg_left (abs_nonneg _) hB₀_pos hB₀_le_A₀
          have hsq_le : ‖(((w.re / A₀ : ℝ) : ℂ) + ((w.im / B₀ : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
              (‖w‖ / B₀) ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]
            simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
              Complex.ofReal_im, Complex.I_re, mul_zero, Complex.I_im, mul_one, sub_zero, add_zero,
              Complex.add_im, zero_add]
            have h1 : (w.re / A₀) ^ 2 ≤ (w.re / B₀) ^ 2 := sq_le_sq.mpr hre_div
            have h2 : w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 := by
              rw [Complex.sq_norm, Complex.normSq_apply]; ring
            calc
              (w.re / A₀) * (w.re / A₀) + (w.im / B₀) * (w.im / B₀)
                  = (w.re / A₀) ^ 2 + (w.im / B₀) ^ 2 := by ring
              _ ≤ (w.re / B₀) ^ 2 + (w.im / B₀) ^ 2 := by linarith
              _ = (w.re ^ 2 + w.im ^ 2) / B₀ ^ 2 := by field_simp [hB₀_pos.ne']
              _ = (‖w‖ / B₀) ^ 2 := by rw [h2, div_pow]
          have hnorm_le_div :
              ‖(((w.re / A₀ : ℝ) : ℂ) + ((w.im / B₀ : ℝ) : ℂ) * Complex.I)‖ ≤ ‖w‖ / B₀ := by
            exact ( abs_le_of_sq_le_sq' hsq_le (div_nonneg (norm_nonneg w) hB₀_pos.le) ).2
          have hB₀_inv_le : B₀⁻¹ ≤ 2 * ε := by
            have : ((1 / 2) * ε⁻¹)⁻¹ = 2 * ε := by field_simp [hε0.ne']
            rw [← this]
            exact inv_anti₀ (by positivity) hB₀_half.le
          calc
            ‖(((w.re / A₀ : ℝ) : ℂ) + ((w.im / B₀ : ℝ) : ℂ) * Complex.I)‖
                ≤ ‖w‖ * B₀⁻¹ := by rw [← div_eq_mul_inv]; exact hnorm_le_div
            _ ≤ (C * ε ^ 2) * (2 * ε) :=
                mul_le_mul hw_norm hB₀_inv_le (inv_nonneg.mpr hB₀_pos.le) (by positivity)
            _ = 2 * C * ε ^ 3 := by ring
        have hsum_le : ‖L₀.symm (F₁ z)‖ ≤ s_ε := by
          rw [hlin_split]
          calc
            ‖L₀.symm (z⁻¹ + a 1 * z) + L₀.symm (g z)‖
                ≤ ‖L₀.symm (z⁻¹ + a 1 * z)‖ + ‖L₀.symm (g z)‖ := norm_add_le _ _
            _ ≤ 1 + 2 * C * ε ^ 3 := by linarith [hnorm_main, hnorm_err]
            _ ≤ 1 + 3 * C * ε ^ 3 := by linarith [show 0 < C * ε ^ 3 by positivity]
        calc
          s_ε⁻¹ * ‖L₀.symm (F₁ z)‖ ≤ s_ε⁻¹ * s_ε :=
              mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hsε_pos.le)
          _ = 1 := inv_mul_cancel₀ hsε_pos.ne'
      -- Step 2c: Connectedness of `ℰ_εᶜ` shows `ℰ_εᶜ ⊆ F₁ '' (ball 0 ε \ {0})`, hence
      -- by injectivity `F₁ '' Ann(ε, R) ⊆ ℰ_ε`!
      let ℰ_ε : Set ℂ := L_ε '' closedBall (0 : ℂ) 1
      have hℰ_compl_eq : ℰ_εᶜ = L_ε '' (closedBall (0 : ℂ) 1)ᶜ :=
        (L_ε.toEquiv.image_compl (closedBall (0 : ℂ) 1)).symm
      have hℰ_compl_conn : IsConnected (ℰ_εᶜ) := by
        rw [hℰ_compl_eq]
        exact isConnected_compl_closedUnitBall.image L_ε L_ε.continuous.continuousOn
      let S_in : Set ℂ := F₁ '' (ball (0 : ℂ) ε \ {0})
      have hU_punc_reg : RudinRCA.Chapter10.IsRegion (ball (0 : ℂ) 1 \ {0}) :=
        puncturedBall_isRegion zero_lt_one
      have hF₁_nonconst : ¬ ∃ w : ℂ, ∀ z ∈ ball (0 : ℂ) 1 \ {0}, F₁ z = w := by
        rintro ⟨w, hw⟩
        have h1 : ((1 / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 \ {0} := by
          refine ⟨?_, ?_⟩
          · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; norm_num
          · simp
        have h2 : ((1 / 3 : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 \ {0} := by
          refine ⟨?_, ?_⟩
          · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; norm_num
          · simp
        have heq := hF₁_inj h1 h2 ((hw _ h1).trans (hw _ h2).symm)
        have : (1 / 2 : ℝ) = 1 / 3 := Complex.ofReal_injective heq
        norm_num at this
      have hSin_sub : ball (0 : ℂ) ε \ {0} ⊆ ball (0 : ℂ) 1 \ {0} :=
        sdiff_subset_sdiff (Metric.ball_subset_ball (hεR.trans hR1).le) Subset.rfl
      have hSin_open : IsOpen S_in :=
        (RudinRCA.Chapter10.theorem10_32 hU_punc_reg hF₁_holo hF₁_nonconst).1.1
          (ball (0 : ℂ) ε \ {0}) hSin_sub (isOpen_ball.sdiff isClosed_singleton)
      -- Show `ℰ_εᶜ ∩ closure S_in ⊆ S_in`
      have hSin_rel_closed : ℰ_εᶜ ∩ closure S_in ⊆ S_in := by
        intro w ⟨hw_out, hw_cl⟩
        -- Choose `0 < δ < ε` so that `‖F₁ z‖ > ‖w‖ + 1` on `0 < ‖z‖ < δ`
        have hG_bdd : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), ‖G z‖ ≤ ‖a 1‖ + C := by
          intro z hz
          have hz1 : ‖z‖ ≤ 1 := (mem_closedBall_zero_iff.mp hz).trans (by norm_num)
          have hGz : G z = a 1 * z + g z := by dsimp [g]; ring
          rw [hGz]
          calc
            ‖a 1 * z + g z‖ ≤ ‖a 1 * z‖ + ‖g z‖ := norm_add_le _ _
            _ ≤ ‖a 1‖ * 1 + C * 1 ^ 2 := by
                rw [norm_mul]
                exact add_le_add (mul_le_mul_of_nonneg_left hz1 (norm_nonneg _))
                  ((hg_quad z hz).trans (mul_le_mul_of_nonneg_left
                    (by nlinarith [norm_nonneg z, hz1]) hC_pos.le))
            _ = ‖a 1‖ + C := by ring
        let δ : ℝ := min (ε / 2) ((‖w‖ + ‖a 1‖ + C + 2)⁻¹)
        have hδ_pos : 0 < δ :=
          lt_min (half_pos hε0) (inv_pos.mpr (by positivity))
        have hδ_lt_ε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε0)
        let C_ann : Set ℂ := closedBall (0 : ℂ) ε \ ball (0 : ℂ) δ
        have hCann_comp : IsCompact C_ann := (isCompact_closedBall 0 ε).diff isOpen_ball
        have hCann_sub : C_ann ⊆ ball (0 : ℂ) 1 \ {0} := by
          rintro z ⟨hz_cl, hz_not_δ⟩
          refine ⟨?_, ?_⟩
          · rw [mem_ball_zero_iff]
            exact (mem_closedBall_zero_iff.mp hz_cl).trans_lt (hεR.trans hR1)
          · intro hz0
            rw [Set.mem_singleton_iff] at hz0
            exact hz_not_δ (hz0 ▸ Metric.mem_ball_self hδ_pos)
        have hFCann_closed : IsClosed (F₁ '' C_ann) :=
          (hCann_comp.image_of_continuousOn
            ((RudinRCA.Chapter10.continuousOn_of_holomorphicOn hF₁_holo).mono hCann_sub)).isClosed
        have hSin_cover : S_in ⊆ (F₁ '' C_ann) ∪ (ball w 1)ᶜ := by
          rintro _ ⟨z, ⟨hz_ε, hz_ne0⟩, rfl⟩
          by_cases hz_δ : z ∈ ball (0 : ℂ) δ
          · right
            rw [Set.mem_compl_iff, mem_ball, dist_eq_norm, not_lt]
            have hz_ne : z ≠ 0 := by rwa [Set.mem_singleton_iff] at hz_ne0
            have hz_norm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
            have hz_lt_inv : ‖z‖ < (‖w‖ + ‖a 1‖ + C + 2)⁻¹ :=
              (mem_ball_zero_iff.mp hz_δ).trans_le (min_le_right _ _)
            have hinv_gt : ‖w‖ + ‖a 1‖ + C + 2 < ‖z⁻¹‖ := by
              rw [norm_inv]
              simpa only [inv_inv] using inv_strictAnti₀ hz_norm_pos hz_lt_inv
            have hz_half : z ∈ closedBall (0 : ℂ) (1 / 2) :=
              mem_closedBall_zero_iff.mpr ((mem_ball_zero_iff.mp hz_ε).le.trans hε_half)
            have hG_le := hG_bdd z hz_half
            have hF₁z : z⁻¹ = F₁ z - G z := by
              have := hF₁_eq z (hSin_sub ⟨hz_ε, hz_ne0⟩)
              linear_combination -this
            have htri1 : ‖z⁻¹‖ ≤ ‖F₁ z‖ + ‖G z‖ := by
              rw [hF₁z]; exact norm_sub_le _ _
            have htri2 : ‖F₁ z‖ ≤ ‖F₁ z - w‖ + ‖w‖ := by
              have : F₁ z = (F₁ z - w) + w := by ring
              conv_lhs => rw [this]
              exact norm_add_le _ _
            linarith
          · left
            exact ⟨z, ⟨ball_subset_closedBall hz_ε, hz_δ⟩, rfl⟩
        have hw_union := closure_minimal hSin_cover (hFCann_closed.union isOpen_ball.isClosed_compl) hw_cl
        rcases hw_union with ⟨z_star, ⟨hz_cl, hz_not_δ⟩, rfl⟩ | hw_not_ball
        · have hz_ne : z_star ≠ 0 := by
            intro h0; exact hz_not_δ (h0 ▸ Metric.mem_ball_self hδ_pos)
          have hlt_or_eq : ‖z_star‖ < ε ∨ ‖z_star‖ = ε :=
            lt_or_eq_of_le (mem_closedBall_zero_iff.mp hz_cl)
          rcases hlt_or_eq with hlt | heq
          · exact ⟨z_star, ⟨mem_ball_zero_iff.mpr hlt, hz_ne⟩, rfl⟩
          · exact False.elim (hw_out (hsphere_in_ℰ z_star (mem_sphere_zero_iff_norm.mpr heq)))
        · exact False.elim (hw_not_ball (Metric.mem_ball_self zero_lt_one))
      -- Also `ℰ_εᶜ ∩ S_in` is nonempty because `F₁(z) → ∞` while `ℰ_ε` is bounded
      have hℰ_bdd : Bornology.IsBounded ℰ_ε :=
        ((isCompact_closedBall (0 : ℂ) 1).image L_ε.continuous).isBounded
      obtain ⟨M_ℰ, hMℰ_pos, hMℰ⟩ := hℰ_bdd.exists_pos_norm_le
      have hSin_meets_compl : (ℰ_εᶜ ∩ S_in).Nonempty := by
        have hG_bdd : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), ‖G z‖ ≤ ‖a 1‖ + C := by
          intro z hz
          have hz1 : ‖z‖ ≤ 1 := (mem_closedBall_zero_iff.mp hz).trans (by norm_num)
          have hGz : G z = a 1 * z + g z := by dsimp [g]; ring
          rw [hGz]
          calc
            ‖a 1 * z + g z‖ ≤ ‖a 1 * z‖ + ‖g z‖ := norm_add_le _ _
            _ ≤ ‖a 1‖ * 1 + C * 1 ^ 2 := by
                rw [norm_mul]
                exact add_le_add (mul_le_mul_of_nonneg_left hz1 (norm_nonneg _))
                  ((hg_quad z hz).trans (mul_le_mul_of_nonneg_left
                    (by nlinarith [norm_nonneg z, hz1]) hC_pos.le))
            _ = ‖a 1‖ + C := by ring
        let r₀ : ℝ := min (ε / 2) ((M_ℰ + ‖a 1‖ + C + 2)⁻¹)
        have hr₀_pos : 0 < r₀ := lt_min (half_pos hε0) (inv_pos.mpr (by positivity))
        have hr₀_lt_ε : r₀ < ε := (min_le_left _ _).trans_lt (half_lt_self hε0)
        let z₀ : ℂ := (r₀ : ℂ)
        have hz₀_mem : z₀ ∈ ball (0 : ℂ) ε \ {0} := by
          refine ⟨?_, ?_⟩
          · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₀_pos]
            exact hr₀_lt_ε
          · simp [z₀, hr₀_pos.ne']
        refine ⟨F₁ z₀, ⟨?_, ⟨z₀, hz₀_mem, rfl⟩⟩⟩
        intro hin_ℰ
        have hle_M := hMℰ (F₁ z₀) hin_ℰ
        have hz₀_half : z₀ ∈ closedBall (0 : ℂ) (1 / 2) := by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₀_pos]
          exact hr₀_lt_ε.le.trans hε_half
        have hG_le := hG_bdd z₀ hz₀_half
        have hr₀_le_inv : r₀ ≤ (M_ℰ + ‖a 1‖ + C + 2)⁻¹ := min_le_right _ _
        have hinv_ge : M_ℰ + ‖a 1‖ + C + 2 ≤ r₀⁻¹ := by
          simpa only [inv_inv] using inv_anti₀ hr₀_pos hr₀_le_inv
        have hz₀_inv_norm : ‖z₀⁻¹‖ = r₀⁻¹ := by
          simp [z₀, Complex.norm_real, abs_of_pos hr₀_pos]
        have htri : ‖z₀⁻¹‖ ≤ ‖F₁ z₀‖ + ‖G z₀‖ := by
          have := hF₁_eq z₀ (hSin_sub hz₀_mem)
          have hz_eq : z₀⁻¹ = F₁ z₀ - G z₀ := by linear_combination -this
          rw [hz_eq]; exact norm_sub_le _ _
        linarith
      have hℰ_compl_sub_Sin : ℰ_εᶜ ⊆ S_in := by
        by_contra hnot_sub
        obtain ⟨w_miss, hw_miss_compl, hw_miss_not⟩ := Set.not_subset.mp hnot_sub
        have hw_miss_not_cl : w_miss ∉ closure S_in :=
          fun hcl => hw_miss_not (hSin_rel_closed ⟨hw_miss_compl, hcl⟩)
        obtain ⟨u, hu_compl, hu_Sin, hu_out⟩ := hℰ_compl_conn.isPreconnected
          S_in (closure S_in)ᶜ hSin_open isClosed_closure.isOpen_compl
          (fun x hx => by
            by_cases hxS : x ∈ S_in
            · exact Or.inl hxS
            · exact Or.inr (fun hcl => hxS (hSin_rel_closed ⟨hx, hcl⟩)))
          hSin_meets_compl ⟨w_miss, hw_miss_compl, hw_miss_not_cl⟩
        exact hu_out (subset_closure hu_Sin)
      -- Therefore `F₁ '' Ann(ε, R) ⊆ ℰ_ε`!
      let Ann : Set ℂ := {z : ℂ | ε < ‖z‖ ∧ ‖z‖ < R}
      have hAnn_open : IsOpen Ann := by
        have h1 : Ann = ball (0 : ℂ) R \ closedBall (0 : ℂ) ε := by
          ext z; simp [Ann, mem_ball_zero_iff, mem_closedBall_zero_iff, and_comm]
        rw [h1]; exact isOpen_ball.sdiff isClosed_closedBall
      have hAnn_sub_punc : Ann ⊆ ball (0 : ℂ) 1 \ {0} := by
        rintro z ⟨hz_gt, hz_lt⟩
        refine ⟨mem_ball_zero_iff.mpr (hz_lt.trans hR1), ?_⟩
        intro hz0
        rw [Set.mem_singleton_iff] at hz0
        rw [hz0, norm_zero] at hz_gt
        linarith
      have hAnn_img_sub_ℰ : F₁ '' Ann ⊆ ℰ_ε := by
        rintro _ ⟨z, hz, rfl⟩
        by_contra hnot_ℰ
        obtain ⟨z', hz'_in, heq⟩ := hℰ_compl_sub_Sin hnot_ℰ
        have hzz' : z' = z := hF₁_inj (hSin_sub hz'_in) (hAnn_sub_punc hz) heq
        subst hzz'
        exact absurd (mem_ball_zero_iff.mp hz'_in.1) (not_lt_of_ge hz.1.le)
      -- Step 2d: Compare Lebesgue areas `volume (F₁ '' Ann) ≤ volume ℰ_ε`
      have hvol_le : MeasureTheory.volume (F₁ '' Ann) ≤ MeasureTheory.volume ℰ_ε :=
        MeasureTheory.measure_mono hAnn_img_sub_ℰ
      have hvol_ℰ : MeasureTheory.volume ℰ_ε = ENNReal.ofReal (Real.pi * A * B) :=
        volume_image_ellipseLinearEquiv_closedBall rot hrot_norm hA_pos hB_pos
      -- Change of variables on `Ann`
      let f' : ℂ → (ℂ →L[ℝ] ℂ) := fun z =>
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv F₁ z)).restrictScalars ℝ)
      have hf'_within : ∀ z ∈ Ann, HasFDerivWithinAt F₁ (f' z) Ann z := by
        intro z hz
        exact ((hF₁_holo z (hAnn_sub_punc hz)).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
      have hvol_Ann : MeasureTheory.volume (F₁ '' Ann) =
          ∫⁻ z in Ann, ENNReal.ofReal (‖deriv F₁ z‖ ^ 2) ∂MeasureTheory.volume := by
        rw [← MeasureTheory.setLIntegral_one (F₁ '' Ann),
          MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul MeasureTheory.volume
            hAnn_open.measurableSet hf'_within (hF₁_inj.mono hAnn_sub_punc)]
        refine MeasureTheory.setLIntegral_congr_fun hAnn_open.measurableSet ?_
        intro z _
        dsimp [f']
        rw [det_real_smulRight_complex, abs_of_nonneg (sq_nonneg _), mul_one]
      -- Polar coordinates + Tonelli on `Ioo ε R ×ˢ Ioo (-π) π`
      have hpolar_Ann :
          (∫⁻ z in Ann, ENNReal.ofReal (‖deriv F₁ z‖ ^ 2) ∂MeasureTheory.volume) =
          ∫⁻ ρ in Ioo ε R,
            (∫⁻ θ in Ioo (-Real.pi) Real.pi,
              ENNReal.ofReal (ρ * ‖deriv F₁ (circleMap 0 ρ θ)‖ ^ 2) ∂MeasureTheory.volume)
            ∂MeasureTheory.volume := by
        let g_int : ℂ → ENNReal := Ann.indicator (fun z => ENNReal.ofReal (‖deriv F₁ z‖ ^ 2))
        rw [← MeasureTheory.lintegral_indicator hAnn_open.measurableSet,
          ← Complex.lintegral_comp_polarCoord_symm g_int]
        have htarget_sub : Ioo ε R ×ˢ Ioo (-Real.pi) Real.pi ⊆ _root_.polarCoord.target := by
          rw [polarCoord_target]
          exact prod_mono (fun ρ hρ => lt_trans hε0 hρ.1) Subset.rfl
        let h_prod : ℝ × ℝ → ENNReal := fun p =>
          ENNReal.ofReal (p.1 * ‖deriv F₁ (circleMap 0 p.1 p.2)‖ ^ 2)
        have hpolar_eq_circle : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
          intro p
          rw [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I,
            Complex.ofReal_cos, Complex.ofReal_sin]
        have hind_target : ∀ p ∈ _root_.polarCoord.target,
            ENNReal.ofReal p.1 • g_int (Complex.polarCoord.symm p) =
              (Ioo ε R ×ˢ Ioo (-Real.pi) Real.pi).indicator h_prod p := by
          rintro ⟨ρ, θ⟩ hp
          rw [polarCoord_target] at hp
          rcases hp with ⟨hρ_pos : 0 < ρ, hθ_mem⟩
          have hnorm_symm : ‖Complex.polarCoord.symm (ρ, θ)‖ = ρ := by
            rw [Complex.norm_polarCoord_symm, abs_of_pos hρ_pos]
          have hmem_iff : Complex.polarCoord.symm (ρ, θ) ∈ Ann ↔ ρ ∈ Ioo ε R := by
            show ε < ‖Complex.polarCoord.symm (ρ, θ)‖ ∧ ‖Complex.polarCoord.symm (ρ, θ)‖ < R ↔
              ρ ∈ Ioo ε R
            rw [hnorm_symm]
            rfl
          by_cases hρ_in : ρ ∈ Ioo ε R
          · have hz_in : Complex.polarCoord.symm (ρ, θ) ∈ Ann := hmem_iff.mpr hρ_in
            have hp_in : (ρ, θ) ∈ Ioo ε R ×ˢ Ioo (-Real.pi) Real.pi := ⟨hρ_in, hθ_mem⟩
            dsimp only [g_int, h_prod]
            rw [Set.indicator_of_mem hz_in, Set.indicator_of_mem hp_in, hpolar_eq_circle,
              smul_eq_mul, ← ENNReal.ofReal_mul hρ_pos.le]
          · have hz_out : Complex.polarCoord.symm (ρ, θ) ∉ Ann := fun h => hρ_in (hmem_iff.mp h)
            have hp_out : (ρ, θ) ∉ Ioo ε R ×ˢ Ioo (-Real.pi) Real.pi := fun h => hρ_in h.1
            dsimp only [g_int]
            rw [Set.indicator_of_notMem hz_out, Set.indicator_of_notMem hp_out, smul_zero]
        have hmeas_prod : MeasurableSet (Ioo ε R ×ˢ Ioo (-Real.pi) Real.pi) :=
          measurableSet_Ioo.prod measurableSet_Ioo
        have hmeas_target : MeasurableSet _root_.polarCoord.target := by
          rw [polarCoord_target]
          exact measurableSet_Ioi.prod measurableSet_Ioo
        rw [MeasureTheory.setLIntegral_congr_fun hmeas_target hind_target,
          MeasureTheory.setLIntegral_indicator hmeas_prod,
          Set.inter_eq_left.mpr htarget_sub, MeasureTheory.Measure.volume_eq_prod]
        -- Check `AEMeasurable` on `Ioo ε R ×ˢ Ioo (-π) π` via continuity
        have hdF₁_holo := RudinRCA.Chapter10.holomorphicOn_deriv
          (isOpen_ball.sdiff isClosed_singleton) hF₁_holo
        have hh_cont : ContinuousOn h_prod (Ioo ε R ×ˢ Ioo (-Real.pi) Real.pi) := by
          have hcm_maps : MapsTo (fun p : ℝ × ℝ => circleMap 0 p.1 p.2)
              (Ioo ε R ×ˢ Ioo (-Real.pi) Real.pi) (ball (0 : ℂ) 1 \ {0}) := by
            rintro ⟨ρ, θ⟩ ⟨⟨hρ_gt, hρ_lt⟩, _⟩
            have hρ_pos : 0 < ρ := lt_trans hε0 hρ_gt
            have hn : ‖circleMap 0 ρ θ‖ = ρ := by
              rw [norm_circleMap_zero, abs_of_pos hρ_pos]
            refine ⟨mem_ball_zero_iff.mpr (by rw [hn]; exact hρ_lt.trans hR1), ?_⟩
            intro h0; dsimp at h0; rw [Set.mem_singleton_iff] at h0; rw [h0, norm_zero] at hn
            linarith
          have hcm_cont : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
            simp only [circleMap_zero]
            exact (Complex.continuous_ofReal.comp continuous_fst).mul
              (Complex.continuous_exp.comp
                ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
          have hd_cont : ContinuousOn (fun p : ℝ × ℝ => deriv F₁ (circleMap 0 p.1 p.2))
              (Ioo ε R ×ˢ Ioo (-Real.pi) Real.pi) :=
            (RudinRCA.Chapter10.continuousOn_of_holomorphicOn hdF₁_holo).comp
              hcm_cont.continuousOn hcm_maps
          exact ENNReal.continuous_ofReal.comp_continuousOn
            (continuousOn_fst.mul ((continuous_norm.comp_continuousOn hd_cont).pow 2))
        exact MeasureTheory.setLIntegral_prod h_prod
          (hh_cont.aestronglyMeasurable hmeas_prod).aemeasurable
      -- Step 2e: Lower-bound the inner `θ`-integral for each `ρ ∈ Ioo ε R` via `bessel_trig_poly_bound`
      have hinner_ge : ∀ ρ ∈ Ioo ε R,
          ENNReal.ofReal (2 * Real.pi *
            (ρ⁻¹ ^ 3 + ∑ k ∈ Finset.range N,
              ((k + 1 : ℝ)) ^ 2 * ‖a (k + 1)‖ ^ 2 * ρ ^ (2 * k + 1))) ≤
          ∫⁻ θ in Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal (ρ * ‖deriv F₁ (circleMap 0 ρ θ)‖ ^ 2) ∂MeasureTheory.volume := by
        intro ρ ⟨hρ_gt, hρ_lt⟩
        have hρ0 : 0 < ρ := lt_trans hε0 hρ_gt
        have hρ1 : ρ < 1 := hρ_lt.trans hR1
        have hdF₁_holo := RudinRCA.Chapter10.holomorphicOn_deriv
          (isOpen_ball.sdiff isClosed_singleton) hF₁_holo
        have hcm_mem : ∀ θ : ℝ, circleMap 0 ρ θ ∈ ball (0 : ℂ) 1 \ {0} := by
          intro θ
          have hn : ‖circleMap 0 ρ θ‖ = ρ := by rw [norm_circleMap_zero, abs_of_pos hρ0]
          refine ⟨mem_ball_zero_iff.mpr (by rw [hn]; exact hρ1), ?_⟩
          intro h0; rw [Set.mem_singleton_iff] at h0; rw [h0, norm_zero] at hn; linarith
        let fθ : ℝ → ℝ := fun θ => ρ * ‖deriv F₁ (circleMap 0 ρ θ)‖ ^ 2
        have hfθ_cont : Continuous fθ := by
          refine continuous_const.mul ((continuous_norm.comp ?_).pow 2)
          rw [continuous_iff_continuousAt]
          intro θ
          exact (hdF₁_holo _ (hcm_mem θ)).continuousAt.comp
            (continuous_circleMap 0 ρ).continuousAt
        have hint_Ioo : MeasureTheory.IntegrableOn fθ (Ioo (-Real.pi) Real.pi)
            MeasureTheory.volume :=
          (hfθ_cont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
        have hl_eq : (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (fθ θ) ∂MeasureTheory.volume) =
            ENNReal.ofReal (ρ * ∫ θ in (-Real.pi)..Real.pi, ‖deriv F₁ (circleMap 0 ρ θ)‖ ^ 2) := by
          rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_Ioo
            (Filter.Eventually.of_forall fun θ => mul_nonneg hρ0.le (sq_nonneg _)),
            ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
            ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
          dsimp [fθ]
          rw [intervalIntegral.integral_const_mul]
        rw [hl_eq]
        apply ENNReal.ofReal_le_ofReal
        -- Apply `bessel_trig_poly_bound` on `Fin (N + 1)`
        let m : Fin (N + 1) → ℤ := Fin.cases (-2) (fun k => (k.1 : ℤ))
        have hm_inj : Function.Injective m := by
          intro i j
          refine Fin.cases ?_ (fun i' => ?_) i
          · refine Fin.cases (fun _ => rfl) (fun j' hij => ?_) j
            simp only [m, Fin.cases_zero, Fin.cases_succ] at hij
            omega
          · refine Fin.cases (fun hij => ?_) (fun j' hij => ?_) j
            · simp only [m, Fin.cases_zero, Fin.cases_succ] at hij
              omega
            · simp only [m, Fin.cases_succ] at hij
              exact congrArg Fin.succ (Fin.ext (Int.ofNat.inj hij))
        let coeff : Fin (N + 1) → ℂ := Fin.cases (-(((ρ : ℂ) ^ 2)⁻¹))
          (fun k => ((k.1 + 1 : ℕ) : ℂ) * a (k.1 + 1) * (ρ : ℂ) ^ k.1)
        let E : ℝ → ℂ := fun θ => circleMap 0 ρ θ ^ N * K_N (circleMap 0 ρ θ)
        have hE_cont : Continuous E := by
          refine ((continuous_circleMap 0 ρ).pow N).mul ?_
          rw [continuous_iff_continuousAt]
          intro θ
          exact (hKN_holo _ (hcm_mem θ).1).continuousAt.comp
            (continuous_circleMap 0 ρ).continuousAt
        have hE_orth : ∀ i : Fin (N + 1),
            (∫ θ in (-Real.pi)..Real.pi,
              E θ * Complex.exp (-((m i : ℂ) * (θ : ℂ) * Complex.I))) = 0 := by
          intro i
          refine Fin.cases ?_ (fun k => ?_) i
          · exact ortho_holomorphic_tail_on_circle hKN_holo hρ0 hρ1 N (N + 1) (-2) (by omega)
          · exact ortho_holomorphic_tail_on_circle hKN_holo hρ0 hρ1 N (N - 1 - k.1) (k.1 : ℤ)
              (by have hk : k.1 < N := k.2; omega)
        have hbessel := bessel_trig_poly_bound hm_inj coeff hE_cont hE_orth
        -- Identify `(∑ i, coeff i * exp (m i * θ * I)) + E θ = deriv F₁ (circleMap 0 ρ θ)`
        have hident : ∀ θ : ℝ,
            (∑ i : Fin (N + 1), coeff i * Complex.exp ((m i : ℂ) * (θ : ℂ) * Complex.I)) + E θ =
              deriv F₁ (circleMap 0 ρ θ) := by
          intro θ
          rw [hderiv_F₁ (circleMap 0 ρ θ) (hcm_mem θ), Fin.sum_univ_succ]
          dsimp [coeff, m, E]
          have h0_term : -(((ρ : ℂ) ^ 2)⁻¹) *
              Complex.exp (((-2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I) =
              -((circleMap 0 ρ θ ^ 2)⁻¹) := by
            rw [circleMap_zero, mul_pow, mul_inv, ← Complex.exp_nat_mul]
            have hexp_inv : (Complex.exp ((2 : ℕ) * ((θ : ℂ) * Complex.I)))⁻¹ =
                Complex.exp (((-2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I) := by
              rw [← Complex.exp_neg]
              congr 1
              push_cast
              ring
            rw [hexp_inv]
            ring
          have hsum_terms : (∑ k : Fin N,
              (((k.1 + 1 : ℕ) : ℂ) * a (k.1 + 1) * (ρ : ℂ) ^ k.1) *
                Complex.exp (((k.1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) =
              ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℂ) * a (k + 1) * circleMap 0 ρ θ ^ k := by
            rw [← Fin.sum_univ_eq_sum_range]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [circleMap_zero, mul_pow, ← Complex.exp_nat_mul]
            push_cast
            ring
          rw [h0_term, hsum_terms]
        simp_rw [hident] at hbessel
        have hcoeff_sum : (∑ i : Fin (N + 1), ‖coeff i‖ ^ 2) =
            ρ⁻¹ ^ 4 + ∑ k ∈ Finset.range N,
              ((k + 1 : ℝ)) ^ 2 * ‖a (k + 1)‖ ^ 2 * ρ ^ (2 * k) := by
          rw [Fin.sum_univ_succ, ← Fin.sum_univ_eq_sum_range]
          have hc0 : ‖coeff 0‖ ^ 2 = ρ⁻¹ ^ 4 := by
            dsimp [coeff]
            rw [norm_neg, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hρ0]
            ring
          rw [hc0]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          dsimp [coeff]
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hρ0]
          push_cast
          ring
        rw [hcoeff_sum] at hbessel
        have hmul_ρ := mul_le_mul_of_nonneg_left hbessel hρ0.le
        have hlhs_ρ : ρ * (2 * Real.pi *
            (ρ⁻¹ ^ 4 + ∑ k ∈ Finset.range N,
              ((k + 1 : ℝ)) ^ 2 * ‖a (k + 1)‖ ^ 2 * ρ ^ (2 * k))) =
            2 * Real.pi *
              (ρ⁻¹ ^ 3 + ∑ k ∈ Finset.range N,
                ((k + 1 : ℝ)) ^ 2 * ‖a (k + 1)‖ ^ 2 * ρ ^ (2 * k + 1)) := by
          have hρ4 : ρ * ρ⁻¹ ^ 4 = ρ⁻¹ ^ 3 := by field_simp [hρ0.ne']
          have hsum_ρ : ρ * (∑ k ∈ Finset.range N,
              ((k + 1 : ℝ)) ^ 2 * ‖a (k + 1)‖ ^ 2 * ρ ^ (2 * k)) =
              ∑ k ∈ Finset.range N,
                ((k + 1 : ℝ)) ^ 2 * ‖a (k + 1)‖ ^ 2 * ρ ^ (2 * k + 1) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [pow_succ]
            ring
          calc
            ρ * (2 * Real.pi *
                (ρ⁻¹ ^ 4 + ∑ k ∈ Finset.range N,
                  ((k + 1 : ℝ)) ^ 2 * ‖a (k + 1)‖ ^ 2 * ρ ^ (2 * k)))
                = 2 * Real.pi * (ρ * ρ⁻¹ ^ 4 + ρ * ∑ k ∈ Finset.range N,
                    ((k + 1 : ℝ)) ^ 2 * ‖a (k + 1)‖ ^ 2 * ρ ^ (2 * k)) := by ring
            _ = 2 * Real.pi *
                  (ρ⁻¹ ^ 3 + ∑ k ∈ Finset.range N,
                    ((k + 1 : ℝ)) ^ 2 * ‖a (k + 1)‖ ^ 2 * ρ ^ (2 * k + 1)) := by
                  rw [hρ4, hsum_ρ]
        linarith
      -- Step 2f: Integrate `hinner_ge` over `ρ ∈ Ioo ε R` and conclude!
      let φ_rad : ℝ → ℝ := fun ρ =>
        2 * Real.pi * (ρ⁻¹ ^ 3 + ∑ k ∈ Finset.range N,
          ((k + 1 : ℝ)) ^ 2 * ‖a (k + 1)‖ ^ 2 * ρ ^ (2 * k + 1))
      have hφ_cont : ContinuousOn φ_rad (Icc ε R) := by
        refine continuousOn_const.mul (ContinuousOn.add ?_ ?_)
        · exact (continuousOn_id.inv₀ (fun ρ hρ => (lt_of_lt_of_le hε0 hρ.1).ne')).pow 3
        · exact continuousOn_finset_sum _ fun k _ =>
            continuousOn_const.mul (continuousOn_pow _)
      have hφ_int_Ioo : MeasureTheory.IntegrableOn φ_rad (Ioo ε R) MeasureTheory.volume :=
        hφ_cont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
      have hrad_lintegral :
          (∫⁻ ρ in Ioo ε R, ENNReal.ofReal (φ_rad ρ) ∂MeasureTheory.volume) =
          ENNReal.ofReal (Real.pi * ((ε⁻¹ ^ 2 - R⁻¹ ^ 2) +
            ∑ k ∈ Finset.range N,
              ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 *
                (R ^ (2 * (k + 1)) - ε ^ (2 * (k + 1))))) := by
        have hφ_ae_nonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Ioo ε R)] φ_rad := by
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with ρ hρ
          have hρ0 : 0 ≤ ρ := (lt_trans hε0 hρ.1).le
          dsimp [φ_rad]
          refine mul_nonneg (by positivity) (add_nonneg (pow_nonneg (inv_nonneg.mpr hρ0) 3) ?_)
          exact Finset.sum_nonneg fun k _ => by positivity
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hφ_int_Ioo hφ_ae_nonneg,
          ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le hεR.le]
        let anti : ℝ → ℝ := fun ρ =>
          Real.pi * (-(ρ⁻¹ ^ 2) + ∑ k ∈ Finset.range N,
            ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 * ρ ^ (2 * (k + 1)))
        have hanti_deriv : ∀ ρ ∈ Set.uIcc ε R, HasDerivAt anti (φ_rad ρ) ρ := by
          intro ρ hρ
          rw [Set.uIcc_of_le hεR.le] at hρ
          have hρ_pos : 0 < ρ := lt_of_lt_of_le hε0 hρ.1
          have hd_inv2 : HasDerivAt (fun t : ℝ => -(t⁻¹ ^ 2)) (2 * ρ⁻¹ ^ 3) ρ := by
            have h1 := ((hasDerivAt_inv hρ_pos.ne').pow 2).neg
            refine h1.congr_deriv ?_
            simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
            rw [inv_pow]
            have hinv3 : ρ⁻¹ * (ρ ^ 2)⁻¹ = (ρ ^ 3)⁻¹ := by
              rw [← mul_inv, ← pow_succ']
            linear_combination -2 * hinv3
          have hd_sum : HasDerivAt (fun t : ℝ => ∑ k ∈ Finset.range N,
              ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 * t ^ (2 * (k + 1)))
              (∑ k ∈ Finset.range N,
                2 * ((k + 1 : ℝ)) ^ 2 * ‖a (k + 1)‖ ^ 2 * ρ ^ (2 * k + 1)) ρ := by
            have hs := HasDerivAt.fun_sum (u := Finset.range N)
              (fun k _ => ((hasDerivAt_id ρ).pow (2 * (k + 1))).const_mul
                (((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2))
            refine hs.congr_deriv ?_
            refine Finset.sum_congr rfl fun k _ => ?_
            simp only [id_eq, mul_one]
            have hexp_sub : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
            rw [hexp_sub]
            push_cast
            ring
          have htot := (hd_inv2.add hd_sum).const_mul Real.pi
          refine htot.congr_deriv ?_
          dsimp [φ_rad]
          have hsum2 : Real.pi * (∑ k ∈ Finset.range N,
              2 * ((k + 1 : ℝ)) ^ 2 * ‖a (k + 1)‖ ^ 2 * ρ ^ (2 * k + 1)) =
              2 * Real.pi * (∑ k ∈ Finset.range N,
                ((k + 1 : ℝ)) ^ 2 * ‖a (k + 1)‖ ^ 2 * ρ ^ (2 * k + 1)) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => by ring
          linear_combination hsum2
        have hφ_int_seg : IntervalIntegrable φ_rad MeasureTheory.volume ε R :=
          (hφ_cont.mono (by rw [Set.uIcc_of_le hεR.le])).intervalIntegrable
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hanti_deriv hφ_int_seg]
        congr 1
        dsimp [anti]
        have hsum_diff :
            (∑ k ∈ Finset.range N, ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 * R ^ (2 * (k + 1))) -
            (∑ k ∈ Finset.range N, ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 * ε ^ (2 * (k + 1))) =
            ∑ k ∈ Finset.range N, ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 *
              (R ^ (2 * (k + 1)) - ε ^ (2 * (k + 1))) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k _ => by ring
        linear_combination Real.pi * hsum_diff
      have hmono_rad := MeasureTheory.setLIntegral_mono' (μ := MeasureTheory.volume) measurableSet_Ioo hinner_ge
      -- Combine everything!
      have hchain :
          ENNReal.ofReal (Real.pi * ((ε⁻¹ ^ 2 - R⁻¹ ^ 2) +
            ∑ k ∈ Finset.range N,
              ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 *
                (R ^ (2 * (k + 1)) - ε ^ (2 * (k + 1))))) ≤
          ENNReal.ofReal (Real.pi * A * B) := by
        calc
          ENNReal.ofReal (Real.pi * ((ε⁻¹ ^ 2 - R⁻¹ ^ 2) +
              ∑ k ∈ Finset.range N,
                ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 *
                  (R ^ (2 * (k + 1)) - ε ^ (2 * (k + 1)))))
              = ∫⁻ ρ in Ioo ε R, ENNReal.ofReal (φ_rad ρ) ∂MeasureTheory.volume :=
                  hrad_lintegral.symm
          _ ≤ ∫⁻ ρ in Ioo ε R,
                (∫⁻ θ in Ioo (-Real.pi) Real.pi,
                  ENNReal.ofReal (ρ * ‖deriv F₁ (circleMap 0 ρ θ)‖ ^ 2) ∂MeasureTheory.volume)
                ∂MeasureTheory.volume := hmono_rad
          _ = MeasureTheory.volume (F₁ '' Ann) := by rw [← hpolar_Ann, ← hvol_Ann]
          _ ≤ MeasureTheory.volume ℰ_ε := hvol_le
          _ = ENNReal.ofReal (Real.pi * A * B) := hvol_ℰ
      have hAB_pos : 0 ≤ Real.pi * A * B := by positivity
      have hreal_ineq :
          Real.pi * ((ε⁻¹ ^ 2 - R⁻¹ ^ 2) +
            ∑ k ∈ Finset.range N,
              ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 *
                (R ^ (2 * (k + 1)) - ε ^ (2 * (k + 1)))) ≤
          Real.pi * A * B :=
        (ENNReal.ofReal_le_ofReal_iff hAB_pos).mp hchain
      have hdiv_pi :
          (ε⁻¹ ^ 2 - R⁻¹ ^ 2) +
            ∑ k ∈ Finset.range N,
              ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 *
                (R ^ (2 * (k + 1)) - ε ^ (2 * (k + 1))) ≤
          A * B := by
        rw [mul_assoc] at hreal_ineq
        exact le_of_mul_le_mul_left hreal_ineq Real.pi_pos
      have hAB_expand : A * B ≤ ε⁻¹ ^ 2 + 6 * C * ε + 9 * C ^ 2 * ε ^ 4 := by
        dsimp [A, B, A₀, B₀, s_ε]
        have h1 : (1 + 3 * C * ε ^ 3) * (ε⁻¹ + ‖a 1‖ * ε) *
            ((1 + 3 * C * ε ^ 3) * (ε⁻¹ - ‖a 1‖ * ε)) =
            (1 + 6 * C * ε ^ 3 + 9 * C ^ 2 * ε ^ 6) * (ε⁻¹ ^ 2 - ‖a 1‖ ^ 2 * ε ^ 2) := by ring
        have h2 : (1 + 6 * C * ε ^ 3 + 9 * C ^ 2 * ε ^ 6) * ε⁻¹ ^ 2 =
            ε⁻¹ ^ 2 + 6 * C * ε + 9 * C ^ 2 * ε ^ 4 := by
          field_simp [hε0.ne']
        have h3 : 0 ≤ (1 + 6 * C * ε ^ 3 + 9 * C ^ 2 * ε ^ 6) * (‖a 1‖ ^ 2 * ε ^ 2) := by
          positivity
        nlinarith
      linarith
    -- Deduce `Summable`, `tsum ≤ 1`, and `‖a 1‖ ≤ 1` from `hpartial`
    have hnonneg : ∀ k : ℕ, 0 ≤ ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2 :=
      fun k => by positivity
    have hsumm : Summable (fun k : ℕ => ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2) :=
      summable_of_sum_range_le hnonneg hpartial
    have htsum_le : (∑' k : ℕ, ((k + 1 : ℝ)) * ‖a (k + 1)‖ ^ 2) ≤ 1 :=
      hsumm.tsum_le_of_sum_range_le hpartial
    have ha1_le1 : ‖a 1‖ ≤ 1 := by
      have hp1 := hpartial 1
      simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, one_mul] at hp1
      nlinarith [norm_nonneg (a 1)]
    exact ⟨hpole, hpartial, hsumm, htsum_le, ha1_le1⟩
  · -- Sharpness: `F_α(z) = z⁻¹ + α z` for `‖α‖ ≤ 1`
    intro α hα
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact (differentiableAt_id.inv (show z ≠ 0 from hz.2)).add
        ((differentiableAt_const α).mul differentiableAt_id)
    · intro z₁ hz₁ z₂ hz₂ heq
      dsimp at heq
      have hz₁0 : z₁ ≠ 0 := hz₁.2
      have hz₂0 : z₂ ≠ 0 := hz₂.2
      have hfac : (z₂ - z₁) * (1 - α * z₁ * z₂) = 0 := by
        have hclear : z₁ * z₂ * (z₁⁻¹ + α * z₁ - (z₂⁻¹ + α * z₂)) = 0 := by
          rw [sub_eq_zero.mpr heq, mul_zero]
        have hexp : z₁ * z₂ * (z₁⁻¹ + α * z₁ - (z₂⁻¹ + α * z₂)) =
            (z₂ - z₁) * (1 - α * z₁ * z₂) := by
          field_simp [hz₁0, hz₂0]
          ring
        rwa [hexp] at hclear
      have hprod_lt1 : ‖α * z₁ * z₂‖ < 1 := by
        have h1 : ‖z₁‖ < 1 := mem_ball_zero_iff.mp hz₁.1
        have h2 : ‖z₂‖ < 1 := mem_ball_zero_iff.mp hz₂.1
        rw [norm_mul, norm_mul]
        have hz12 : ‖z₁‖ * ‖z₂‖ < 1 := by
          calc
            ‖z₁‖ * ‖z₂‖ ≤ ‖z₁‖ * 1 := mul_le_mul_of_nonneg_left h2.le (norm_nonneg z₁)
            _ < 1 := by linarith
        calc
          ‖α‖ * ‖z₁‖ * ‖z₂‖ = ‖α‖ * (‖z₁‖ * ‖z₂‖) := by ring
          _ ≤ 1 * (‖z₁‖ * ‖z₂‖) := mul_le_mul_of_nonneg_right hα (by positivity)
          _ < 1 := by linarith
      have hne1 : 1 - α * z₁ * z₂ ≠ 0 := by
        intro h0
        have heq1 : α * z₁ * z₂ = 1 := (sub_eq_zero.mp h0).symm
        rw [heq1, norm_one] at hprod_lt1
        exact lt_irrefl 1 hprod_lt1
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hne1)).symm
    · intro z _
      have hsub : (z⁻¹ + α * z) - z⁻¹ = α * z := by ring
      rw [hsub]
      have hs := hasSum_single (f := fun n : ℕ => (if n = 1 then α else 0) * z ^ n) 1
        (fun n hn => by simp [hn])
      simpa using hs

/-! ### Nodes 14.14 and 14.15: Bieberbach `|a₂| ≤ 2`, Koebe `1/4` Theorem, and Omitted-Value Diameter -/

/-- Helper: for any `f ∈ ClassS` with Taylor coefficients `a` (`f z = ∑ a_n z^n` on `U`),
`deriv (dslope f 0) 0 = a 2`. -/
theorem deriv_dslope_zero_of_classS {f : ℂ → ℂ} (hf : f ∈ ClassS) {a : ℕ → ℂ}
    (ha : ∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n : ℕ => a n * z ^ n) (f z)) :
    deriv (dslope f 0) 0 = a 2 := by
  rcases hf with ⟨hf_holo, _, hf0, hdf0⟩
  have ha_disc : ∀ z ∈ RudinRCA.Chapter10.disc 0 1, HasSum (fun n : ℕ => a n * (z - 0) ^ n) (f z) :=
    fun z hz => by simpa [sub_zero] using ha z hz
  have ha0 : a 0 = 0 := by
    have := RudinRCA.Chapter10.powerSeries_coefficient zero_lt_one ha_disc 0
    simpa [hf0] using this
  have ha1 : a 1 = 1 := by
    have := RudinRCA.Chapter10.powerSeries_coefficient zero_lt_one ha_disc 1
    simpa [iteratedDeriv_one, hdf0] using this
  have hφ_holo : RudinRCA.Chapter10.HolomorphicOn (dslope f 0) (ball (0 : ℂ) 1) :=
    (RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn isOpen_ball).mpr
      ((Complex.differentiableOn_dslope (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)).mpr
        ((RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn isOpen_ball).mp hf_holo))
  have hφ_sum : ∀ z ∈ RudinRCA.Chapter10.disc 0 1,
      HasSum (fun n : ℕ => a (n + 1) * (z - 0) ^ n) (dslope f 0 z) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      simp only [dslope_same, hdf0, sub_zero, ← ha1]
      have hs := hasSum_single (f := fun n : ℕ => a (n + 1) * (0 : ℂ) ^ n) 0
        (fun n hn => by rw [zero_pow hn, mul_zero])
      simpa using hs
    · have hshift := (hasSum_nat_add_iff' 1).mpr (ha z hz)
      simp only [Finset.sum_range_one, pow_zero, mul_one, ha0, sub_zero] at hshift
      have hmul := hshift.mul_right z⁻¹
      have hdsl : dslope f 0 z = f z * z⁻¹ := by
        rw [dslope_of_ne f hz0, slope_def_field, hf0, sub_zero, sub_zero, div_eq_mul_inv]
      rw [hdsl]
      convert hmul using 1
      ext n
      field_simp [hz0]
      rw [sub_zero, pow_succ]
      ring
  have hc1 := RudinRCA.Chapter10.powerSeries_coefficient zero_lt_one hφ_sum 1
  simpa [iteratedDeriv_one] using hc1.symm

/-- **Theorem 14.14 (`|a₂| ≤ 2`, Koebe `1/4` Theorem, Sharpness, and Entire Contrast, RCA p. 288):**
1. For every `f ∈ ClassS` with expansion `f(z) = z + ∑_{n ≥ 2} a_n z^n` (`HasSum (a n * z^n) (f z)`
   on `U = ball 0 1`),
   - `(a)` `‖a 2‖ ≤ 2`, and
   - `(b)` `ball (0 : ℂ) (1 / 4) ⊆ f '' ball (0 : ℂ) 1`;
2. *(Sharpness)* `koebeFamily 1 ∈ ClassS` achieves `‖a 2‖ = 2` and omits `-1 / 4`
   (`‖(-1 / 4 : ℂ)‖ = 1 / 4`);
3. *(Entire contrast)* For every `α ≠ 0`, `E_α(z) = α * (1 - exp (-z / α))` is entire with
   `E_α(0) = 0`, `deriv E_α 0 = 1`, and omits `α` on all of `ℂ`; consequently, if `‖α‖ < 1 / 4`,
   `E_α` cannot be injective on `U`. -/
theorem theorem14_14 :
    (∀ {f : ℂ → ℂ} {a : ℕ → ℂ}, f ∈ ClassS →
      (∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n : ℕ => a n * z ^ n) (f z)) →
      ‖a 2‖ ≤ 2 ∧ ball (0 : ℂ) (1 / 4) ⊆ f '' ball (0 : ℂ) 1) ∧
    (koebeFamily 1 ∈ ClassS ∧
      (∃ a : ℕ → ℂ, (∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n : ℕ => a n * z ^ n) (koebeFamily 1 z)) ∧
        ‖a 2‖ = 2) ∧
      (-1 / 4 : ℂ) ∉ koebeFamily 1 '' ball (0 : ℂ) 1 ∧
      ‖(-1 / 4 : ℂ)‖ = 1 / 4) ∧
    (∀ {α : ℂ}, α ≠ 0 →
      let E : ℂ → ℂ := fun z => α * (1 - Complex.exp (-z / α))
      RudinRCA.Chapter10.HolomorphicOn E Set.univ ∧
      E 0 = 0 ∧
      deriv E 0 = 1 ∧
      (∀ z : ℂ, E z ≠ α) ∧
      (‖α‖ < 1 / 4 → ¬ InjOn E (ball (0 : ℂ) 1))) := by
  -- First prove part (a) (`‖a 2‖ ≤ 2`) for all `f ∈ ClassS`
  have hpartA : ∀ {f : ℂ → ℂ} {a : ℕ → ℂ}, f ∈ ClassS →
      (∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n : ℕ => a n * z ^ n) (f z)) →
      ‖a 2‖ ≤ 2 := by
    intro f a hf ha
    have hdφ0 : deriv (dslope f 0) 0 = a 2 := deriv_dslope_zero_of_classS hf ha
    obtain ⟨h, hh_holo, hh_ne, hh0, hh_sq, hg_S, _, _⟩ := classS_odd_sqrt_aux hf
    rcases hg_S with ⟨hg_holo, hg_inj, hg0, _⟩
    -- Compute `deriv h 0 = a 2 / 2` from `h(z)^2 = dslope f 0 z`
    have hdh0 : deriv h 0 = a 2 / 2 := by
      have hev : (fun z => h z ^ 2) =ᶠ[𝓝 (0 : ℂ)] dslope f 0 := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
        exact hh_sq z hz
      have hd_sq : HasDerivAt (fun z => h z ^ 2) (2 * h 0 ^ 1 * deriv h 0) 0 :=
        ((hh_holo 0 (Metric.mem_ball_self zero_lt_one)).hasDerivAt).pow 2
      have heq : 2 * h 0 ^ 1 * deriv h 0 = a 2 := by
        rw [← hd_sq.deriv, hev.deriv_eq, hdφ0]
      rw [hh0, pow_one, mul_one] at heq
      linear_combination (1 / 2 : ℂ) * heq
    -- Set `F(z) = (z * h(z^2))⁻¹` on `ball 0 1 \ {0}`
    let g : ℂ → ℂ := fun z => z * h (z ^ 2)
    have hg_ne : ∀ z ∈ ball (0 : ℂ) 1 \ {0}, g z ≠ 0 := by
      intro z hz h0
      exact hz.2 (hg_inj hz.1 (Metric.mem_ball_self zero_lt_one) (h0.trans hg0.symm))
    let F : ℂ → ℂ := fun z => (g z)⁻¹
    have hF_holo : RudinRCA.Chapter10.HolomorphicOn F (ball (0 : ℂ) 1 \ {0}) :=
      fun z hz => (hg_holo z hz.1).inv (hg_ne z hz)
    have hF_inj : InjOn F (ball (0 : ℂ) 1 \ {0}) := by
      intro z₁ hz₁ z₂ hz₂ heq
      dsimp [F] at heq
      exact hg_inj hz₁.1 hz₂.1 (inv_injective heq)
    -- Express `F(z) - z⁻¹ = -z * dslope h 0 (z^2) / h(z^2)` holomorphically on all of `ball 0 1`!
    let ψ : ℂ → ℂ := dslope h 0
    have hψ_holo : RudinRCA.Chapter10.HolomorphicOn ψ (ball (0 : ℂ) 1) :=
      (RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn isOpen_ball).mpr
        ((Complex.differentiableOn_dslope (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)).mpr
          ((RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn isOpen_ball).mp hh_holo))
    have hψ0 : ψ 0 = a 2 / 2 := by simp [ψ, dslope_same, hdh0]
    let G : ℂ → ℂ := fun z => -z * ψ (z ^ 2) / h (z ^ 2)
    have hz2_mem : ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → z ^ 2 ∈ ball (0 : ℂ) 1 := by
      intro z hz
      rw [mem_ball_zero_iff] at hz ⊢
      rw [norm_pow]; nlinarith [norm_nonneg z]
    have hG_holo : RudinRCA.Chapter10.HolomorphicOn G (ball (0 : ℂ) 1) := by
      intro z hz
      have hd_ψ : DifferentiableAt ℂ (ψ ∘ fun w : ℂ => w ^ 2) z :=
        (hψ_holo (z ^ 2) (hz2_mem hz)).comp z (differentiableAt_id.pow 2)
      have hd_h : DifferentiableAt ℂ (h ∘ fun w : ℂ => w ^ 2) z :=
        (hh_holo (z ^ 2) (hz2_mem hz)).comp z (differentiableAt_id.pow 2)
      exact ((differentiableAt_id.neg).mul hd_ψ).div hd_h (hh_ne (z ^ 2) (hz2_mem hz))
    have hFG_eq : ∀ z ∈ ball (0 : ℂ) 1 \ {0}, F z - z⁻¹ = G z := by
      intro z hz
      have hz0 : z ≠ 0 := hz.2
      have hhz2_ne : h (z ^ 2) ≠ 0 := hh_ne (z ^ 2) (hz2_mem hz.1)
      have hdsl_h : z ^ 2 * ψ (z ^ 2) = h (z ^ 2) - 1 := by
        have hs := sub_smul_dslope h 0 (z ^ 2)
        simpa [ψ, hh0, smul_eq_mul] using hs
      dsimp [F, g, G]
      field_simp [hz0, hhz2_ne]
      linear_combination hdsl_h
    obtain ⟨b, hb_disc⟩ := (RudinRCA.Chapter10.representableByPowerSeries_of_holomorphicOn hG_holo)
      0 1 zero_lt_one Subset.rfl
    have hb_punc : ∀ z ∈ ball (0 : ℂ) 1 \ {0}, HasSum (fun n : ℕ => b n * z ^ n) (F z - z⁻¹) := by
      intro z hz
      rw [hFG_eq z hz]
      simpa [sub_zero] using hb_disc z hz.1
    have hb1_norm : ‖b 1‖ ≤ 1 := (theorem14_13.1 hF_holo hF_inj hb_punc).2.2.2.2
    -- Identify `b 1 = deriv G 0 = -a 2 / 2`
    have hb1_eq : b 1 = -(a 2 / 2) := by
      have hc1 := RudinRCA.Chapter10.powerSeries_coefficient zero_lt_one hb_disc 1
      simp only [Nat.factorial_one, Nat.cast_one, one_mul, iteratedDeriv_one] at hc1
      rw [hc1]
      -- Since `G(z) = z * (-ψ(z^2) / h(z^2))`, evaluate derivative at `0`
      let Q : ℂ → ℂ := fun z => -(ψ (z ^ 2)) / h (z ^ 2)
      have h0_mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := Metric.mem_ball_self zero_lt_one
      have hQ_diff : DifferentiableAt ℂ Q 0 := by
        have hd_ψ : DifferentiableAt ℂ (ψ ∘ fun w : ℂ => w ^ 2) 0 :=
          (hψ_holo ((0 : ℂ) ^ 2) (hz2_mem h0_mem)).comp 0 (differentiableAt_id.pow 2)
        have hd_h : DifferentiableAt ℂ (h ∘ fun w : ℂ => w ^ 2) 0 :=
          (hh_holo ((0 : ℂ) ^ 2) (hz2_mem h0_mem)).comp 0 (differentiableAt_id.pow 2)
        exact hd_ψ.neg.div hd_h (hh_ne ((0 : ℂ) ^ 2) (hz2_mem h0_mem))
      have hG_prod : G = fun z => z * Q z := by
        ext z; dsimp [G, Q]; ring
      have hdG0 : deriv G 0 = -(a 2 / 2) := by
        rw [hG_prod]
        exact (((hasDerivAt_id (0 : ℂ)).mul hQ_diff.hasDerivAt).congr_deriv
          (by simp [Q, hψ0, hh0])).deriv
      exact hdG0
    rw [hb1_eq, norm_neg, norm_div, Complex.norm_ofNat] at hb1_norm
    linarith
  -- Now prove part (b) (`ball 0 (1/4) ⊆ f '' ball 0 1`) from `hpartA`
  have hpartB : ∀ {f : ℂ → ℂ}, f ∈ ClassS → ball (0 : ℂ) (1 / 4) ⊆ f '' ball (0 : ℂ) 1 := by
    intro f hf w hw_ball
    by_contra hw_not_mem
    obtain ⟨a, ⟨_, _, ha_sum, _⟩, _⟩ := classS_taylor_expansion hf
    rcases hf with ⟨hf_holo, hf_inj, hf0, hdf0⟩
    have hw_ne0 : w ≠ 0 := by
      intro h0
      subst h0
      exact hw_not_mem ⟨0, Metric.mem_ball_self zero_lt_one, hf0⟩
    have hden_ne : ∀ z ∈ ball (0 : ℂ) 1, 1 - f z / w ≠ 0 := by
      intro z hz h0
      have hfw : f z / w = 1 := (sub_eq_zero.mp h0).symm
      have heq : f z = w := by
        calc
          f z = (f z / w) * w := (div_mul_cancel₀ (f z) hw_ne0).symm
          _ = w := by rw [hfw, one_mul]
      exact hw_not_mem ⟨z, hz, heq⟩
    let f₁ : ℂ → ℂ := fun z => f z / (1 - f z / w)
    have hf₁_holo : RudinRCA.Chapter10.HolomorphicOn f₁ (ball (0 : ℂ) 1) := by
      intro z hz
      exact (hf_holo z hz).div
        ((differentiableAt_const (1 : ℂ)).sub ((hf_holo z hz).div_const w))
        (hden_ne z hz)
    have hf₁_inj : InjOn f₁ (ball (0 : ℂ) 1) := by
      intro z₁ hz₁ z₂ hz₂ heq
      dsimp [f₁] at heq
      have hcross := (div_eq_div_iff (hden_ne z₁ hz₁) (hden_ne z₂ hz₂)).mp heq
      have hfeq : f z₁ = f z₂ := by
        have hsub : f z₁ * (1 - f z₂ / w) - f z₂ * (1 - f z₁ / w) = 0 := by
          linear_combination hcross
        have hsimp : f z₁ * (1 - f z₂ / w) - f z₂ * (1 - f z₁ / w) = f z₁ - f z₂ := by ring
        rw [hsimp] at hsub
        exact sub_eq_zero.mp hsub
      exact hf_inj hz₁ hz₂ hfeq
    have hf₁_0 : f₁ 0 = 0 := by simp [f₁, hf0]
    have hdf₁_0 : deriv f₁ 0 = 1 := by
      have hdf_at0 : HasDerivAt f 1 0 := hdf0 ▸ (hf_holo 0 (Metric.mem_ball_self zero_lt_one)).hasDerivAt
      have hden_at0 := (hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hdf_at0.div_const w)
      have hq := hdf_at0.div hden_at0 (by simp [hf0])
      exact (hq.congr_deriv (by simp [hf0])).deriv
    have hf₁_S : f₁ ∈ ClassS := ⟨hf₁_holo, hf₁_inj, hf₁_0, hdf₁_0⟩
    obtain ⟨c, ⟨_, _, hc_sum, _⟩, _⟩ := classS_taylor_expansion hf₁_S
    have ha2_le : ‖a 2‖ ≤ 2 := hpartA ⟨hf_holo, hf_inj, hf0, hdf0⟩ ha_sum
    have hc2_le : ‖c 2‖ ≤ 2 := hpartA hf₁_S hc_sum
    -- Relate `c 2 - a 2 = w⁻¹` via `dslope f₁ 0 z - dslope f 0 z = dslope f 0 z * f₁ z / w`
    have hdc2 : deriv (dslope f₁ 0) 0 = c 2 := deriv_dslope_zero_of_classS hf₁_S hc_sum
    have hda2 : deriv (dslope f 0) 0 = a 2 :=
      deriv_dslope_zero_of_classS ⟨hf_holo, hf_inj, hf0, hdf0⟩ ha_sum
    have hdsl_rel : (fun z => dslope f₁ 0 z - dslope f 0 z) =ᶠ[𝓝 (0 : ℂ)]
        fun z => (dslope f 0 z * f₁ z) / w := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
      by_cases hz0 : z = 0
      · subst hz0
        simp [dslope_same, hdf₁_0, hdf0, hf₁_0]
      · have hrel : f₁ z - f z = (f z * f₁ z) / w := by
          have hmul : f₁ z * (1 - f z / w) = f z := div_mul_cancel₀ _ (hden_ne z hz)
          linear_combination hmul
        rw [dslope_of_ne f₁ hz0, dslope_of_ne f hz0, slope_def_field, slope_def_field,
          hf₁_0, hf0, sub_zero, sub_zero]
        field_simp [hz0, hw_ne0]
        have hrel' : w * (f₁ z - f z) = f z * f₁ z := by
          field_simp [hw_ne0] at hrel
          linear_combination hrel
        linear_combination hrel'
    have hd_dsl_f : DifferentiableAt ℂ (dslope f 0) 0 :=
      (((Complex.differentiableOn_dslope (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)).mpr
        ((RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn isOpen_ball).mp hf_holo)).differentiableAt
        (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one))
    have hd_dsl_f₁ : DifferentiableAt ℂ (dslope f₁ 0) 0 :=
      (((Complex.differentiableOn_dslope (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)).mpr
        ((RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn isOpen_ball).mp hf₁_holo)).differentiableAt
        (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one))
    have hd_lhs := (hd_dsl_f₁.hasDerivAt.sub hd_dsl_f.hasDerivAt).congr_deriv
      (by rw [hdc2, hda2])
    have hdf₁_at0 : HasDerivAt f₁ 1 0 :=
      hdf₁_0 ▸ (hf₁_holo 0 (Metric.mem_ball_self zero_lt_one)).hasDerivAt
    have hd_rhs : HasDerivAt (fun z => (dslope f 0 z * f₁ z) / w) w⁻¹ 0 :=
      ((hd_dsl_f.hasDerivAt.mul hdf₁_at0).div_const w).congr_deriv
        (by simp [dslope_same, hdf0, hf₁_0, div_eq_mul_inv])
    have hca_eq : c 2 - a 2 = w⁻¹ := by
      calc
        c 2 - a 2 = deriv (fun z => dslope f₁ 0 z - dslope f 0 z) 0 := hd_lhs.deriv.symm
        _ = deriv (fun z => (dslope f 0 z * f₁ z) / w) 0 := Filter.EventuallyEq.deriv_eq hdsl_rel
        _ = w⁻¹ := hd_rhs.deriv
    have hwinv_le4 : ‖w‖⁻¹ ≤ 4 := by
      rw [← norm_inv, ← hca_eq]
      calc
        ‖c 2 - a 2‖ ≤ ‖c 2‖ + ‖a 2‖ := norm_sub_le _ _
        _ ≤ 2 + 2 := add_le_add hc2_le ha2_le
        _ = 4 := by norm_num
    have hw_lt : ‖w‖ < 1 / 4 := mem_ball_zero_iff.mp hw_ball
    have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne0
    have hgt4 : 4 < ‖w‖⁻¹ := by
      have : (1 / 4 : ℝ)⁻¹ = 4 := by norm_num
      rw [← this]
      exact inv_strictAnti₀ hw_pos hw_lt
    linarith
  refine ⟨fun hf ha => ⟨hpartA hf ha, hpartB hf⟩, ?_, ?_⟩
  · -- Sharpness from `koebeFamily 1` (`α = 1`)
    obtain ⟨hk_S, hk_sum⟩ := theorem14_11 (α := 1) (by simp)
    refine ⟨hk_S, ?_, ?_, ?_⟩
    · let a_k : ℕ → ℂ := fun n => (n : ℂ)
      have hak_sum : ∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n : ℕ => a_k n * z ^ n) (koebeFamily 1 z) := by
        intro z hz
        have hs := hk_sum z hz
        rw [← hasSum_nat_add_iff' 1]
        simp only [Finset.sum_range_one, a_k, Nat.cast_zero, zero_mul, add_zero, sub_zero]
        convert hs using 1
        ext n
        simp [a_k]
      refine ⟨a_k, hak_sum, ?_⟩
      dsimp [a_k]
      norm_num
    · rintro ⟨z, hz, heq⟩
      unfold koebeFamily at heq
      rw [one_mul] at heq
      have hden_ne : 1 - z ≠ 0 := by
        intro h0
        have hz1 : z = 1 := (sub_eq_zero.mp h0).symm
        have hlt := mem_ball_zero_iff.mp hz
        rw [hz1, norm_one] at hlt
        exact lt_irrefl 1 hlt
      have hsq : (z + 1) ^ 2 = 0 := by
        field_simp [pow_ne_zero 2 hden_ne] at heq
        linear_combination heq
      have hz_neg1 : z = -1 := by
        have := eq_zero_of_pow_eq_zero hsq
        linear_combination this
      have hlt := mem_ball_zero_iff.mp hz
      rw [hz_neg1, norm_neg, norm_one] at hlt
      exact lt_irrefl 1 hlt
    · norm_num
  · -- Entire contrast `E(z) = α * (1 - exp (-z / α))`
    intro α hα E
    have hE_holo : RudinRCA.Chapter10.HolomorphicOn E Set.univ := by
      intro z _
      dsimp [E]
      exact (differentiableAt_const α).mul
        ((differentiableAt_const (1 : ℂ)).sub ((differentiableAt_id.neg.div_const α).cexp))
    have hE0 : E 0 = 0 := by simp [E]
    have hdE0 : deriv E 0 = 1 := by
      have hlin := ((hasDerivAt_id (0 : ℂ)).neg).div_const α
      have hexp := ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub hlin.cexp).const_mul α
      exact (hexp.congr_deriv (by simp; field_simp [hα])).deriv
    have hE_omit : ∀ z : ℂ, E z ≠ α := by
      intro z heq
      dsimp [E] at heq
      have h1 : 1 - Complex.exp (-z / α) = 1 :=
        mul_left_cancel₀ hα (heq.trans (mul_one α).symm)
      have hexp0 : Complex.exp (-z / α) = 0 := by linear_combination -h1
      exact Complex.exp_ne_zero _ hexp0
    refine ⟨hE_holo, hE0, hdE0, hE_omit, ?_⟩
    intro hα_lt hinj
    have hE_S : E ∈ ClassS := ⟨fun z hz => hE_holo z trivial, hinj, hE0, hdE0⟩
    have hα_in : α ∈ E '' ball (0 : ℂ) 1 := hpartB hE_S (mem_ball_zero_iff.mpr hα_lt)
    rcases hα_in with ⟨z, _, hz_eq⟩
    exact hE_omit z hz_eq

/-- **Theorem 14.15 (Omitted-Value Diameter Bound `‖w₁ - w₂‖ ≤ 4`, RCA pp. 288–289):**
1. Let `F` be holomorphic and injective on the punctured unit disc `U \ {0}` with a simple pole of
   residue `1` at `0` (`∃ c : ℂ, Tendsto (fun z => F z - z⁻¹) (𝓝[≠] 0) (𝓝 c)`, equivalently
   `F(z) = z⁻¹ + G(z)` with `G ∈ H(U)`). If `w₁, w₂ ∉ F '' (U \ {0})`, then `‖w₁ - w₂‖ ≤ 4`;
2. *(Sharpness)* `F₀(z) = z⁻¹ + z` is holomorphic and injective on `U \ {0}` with a simple pole of
   residue `1` at `0`, and omits **precisely** the real interval `[-2, 2]` (`(F₀ '' (U \ {0}))ᶜ =
   (fun x : ℝ => (x : ℂ)) '' Icc (-2) 2`), witnessing `‖(2 : ℂ) - (-2 : ℂ)‖ = 4`. -/
theorem theorem14_15 :
    (∀ {F : ℂ → ℂ},
      RudinRCA.Chapter10.HolomorphicOn F (ball (0 : ℂ) 1 \ {0}) →
      InjOn F (ball (0 : ℂ) 1 \ {0}) →
      (∃ c : ℂ, Tendsto (fun z : ℂ => F z - z⁻¹) (𝓝[≠] 0) (𝓝 c)) →
      ∀ {w₁ w₂ : ℂ}, w₁ ∉ F '' (ball (0 : ℂ) 1 \ {0}) → w₂ ∉ F '' (ball (0 : ℂ) 1 \ {0}) →
        ‖w₁ - w₂‖ ≤ 4) ∧
    (let F₀ : ℂ → ℂ := fun z => z⁻¹ + z;
      RudinRCA.Chapter10.HolomorphicOn F₀ (ball (0 : ℂ) 1 \ {0}) ∧
      InjOn F₀ (ball (0 : ℂ) 1 \ {0}) ∧
      Tendsto (fun z : ℂ => F₀ z - z⁻¹) (𝓝[≠] 0) (𝓝 0) ∧
      (F₀ '' (ball (0 : ℂ) 1 \ {0}))ᶜ = (fun x : ℝ => (x : ℂ)) '' Icc (-2 : ℝ) 2 ∧
      ‖(2 : ℂ) - (-2 : ℂ)‖ = 4) := by
  refine ⟨?_, ?_⟩
  · intro F hF_holo hF_inj ⟨c, hc_lim⟩ w₁ w₂ hw₁ hw₂
    by_cases hw_eq : w₁ = w₂
    · subst hw_eq; simp
    -- Extend `F z - z⁻¹` across `0` to `G ∈ H(ball 0 1)` by removable singularity
    let G : ℂ → ℂ := Function.update (fun z : ℂ => F z - z⁻¹) 0 c
    have hG_diff_punc : DifferentiableOn ℂ (fun z : ℂ => F z - z⁻¹) (ball (0 : ℂ) 1 \ {0}) :=
      fun z hz => ((hF_holo z hz).sub
        (differentiableAt_id.inv (show z ≠ 0 from hz.2))).differentiableWithinAt
    have hG_diff : DifferentiableOn ℂ G (ball (0 : ℂ) 1) := by
      rw [← Complex.differentiableOn_compl_singleton_and_continuousAt_iff
        (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)]
      refine ⟨?_, ?_⟩
      · refine hG_diff_punc.congr fun z hz => ?_
        have hz0 : z ≠ 0 := hz.2
        simp [G, hz0]
      · rw [continuousAt_update_same]
        exact hc_lim
    have hG_holo : RudinRCA.Chapter10.HolomorphicOn G (ball (0 : ℂ) 1) :=
      (RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn isOpen_ball).mpr hG_diff
    have hFG : ∀ z ∈ ball (0 : ℂ) 1 \ {0}, F z = z⁻¹ + G z := by
      intro z hz
      have hz0 : z ≠ 0 := hz.2
      dsimp [G]
      rw [Function.update_of_ne hz0]
      ring
    -- Define `f(z) = z / (1 + z * (G z - w₁)) ∈ ClassS`
    let f : ℂ → ℂ := fun z => z / (1 + z * (G z - w₁))
    have hden_ne : ∀ z ∈ ball (0 : ℂ) 1, 1 + z * (G z - w₁) ≠ 0 := by
      intro z hz h0
      by_cases hz0 : z = 0
      · subst hz0; simp at h0
      · have hprod : z * (F z - w₁) = 1 + z * (G z - w₁) := by
          rw [hFG z ⟨hz, hz0⟩]
          field_simp [hz0]; ring
        rw [h0] at hprod
        rcases mul_eq_zero.mp hprod with rfl | hFw₁
        · exact hz0 rfl
        · exact hw₁ ⟨z, ⟨hz, hz0⟩, sub_eq_zero.mp hFw₁⟩
    have hf_eq_inv : ∀ z ∈ ball (0 : ℂ) 1 \ {0}, f z = (F z - w₁)⁻¹ := by
      intro z hz
      have hz0 : z ≠ 0 := hz.2
      have hmul : f z * (F z - w₁) = 1 := by
        dsimp [f]
        rw [hFG z hz]
        have hden := hden_ne z hz.1
        field_simp [hz0, hden]
        ring
      exact eq_inv_of_mul_eq_one_left hmul
    have hf_holo : RudinRCA.Chapter10.HolomorphicOn f (ball (0 : ℂ) 1) := by
      intro z hz
      exact differentiableAt_id.div
        ((differentiableAt_const (1 : ℂ)).add
          (differentiableAt_id.mul ((hG_holo z hz).sub (differentiableAt_const w₁))))
        (hden_ne z hz)
    have hf0 : f 0 = 0 := by simp [f]
    have hdf0 : deriv f 0 = 1 := by
      have hg_sub : HasDerivAt (fun z => G z - w₁) (deriv (fun z => G z - w₁) 0) 0 :=
        ((hG_holo 0 (Metric.mem_ball_self zero_lt_one)).sub (differentiableAt_const w₁)).hasDerivAt
      have hd_den := (hasDerivAt_const (0 : ℂ) (1 : ℂ)).add ((hasDerivAt_id (0 : ℂ)).mul hg_sub)
      have hq := (hasDerivAt_id (0 : ℂ)).div hd_den (by simp)
      exact (hq.congr_deriv (by simp)).deriv
    have hf_inj : InjOn f (ball (0 : ℂ) 1) := by
      intro z₁ hz₁ z₂ hz₂ heq
      by_cases hz₁0 : z₁ = 0
      · subst hz₁0
        by_cases hz₂0 : z₂ = 0
        · subst hz₂0; rfl
        · rw [hf0, hf_eq_inv z₂ ⟨hz₂, hz₂0⟩] at heq
          have hne : (F z₂ - w₁)⁻¹ ≠ 0 :=
            inv_ne_zero (fun h0 => hw₁ ⟨z₂, ⟨hz₂, hz₂0⟩, sub_eq_zero.mp h0⟩)
          exact False.elim (hne heq.symm)
      · by_cases hz₂0 : z₂ = 0
        · subst hz₂0
          rw [hf0, hf_eq_inv z₁ ⟨hz₁, hz₁0⟩] at heq
          have hne : (F z₁ - w₁)⁻¹ ≠ 0 :=
            inv_ne_zero (fun h0 => hw₁ ⟨z₁, ⟨hz₁, hz₁0⟩, sub_eq_zero.mp h0⟩)
          exact False.elim (hne heq)
        · rw [hf_eq_inv z₁ ⟨hz₁, hz₁0⟩, hf_eq_inv z₂ ⟨hz₂, hz₂0⟩] at heq
          exact hF_inj ⟨hz₁, hz₁0⟩ ⟨hz₂, hz₂0⟩ (sub_left_inj.mp (inv_injective heq))
    have hf_S : f ∈ ClassS := ⟨hf_holo, hf_inj, hf0, hdf0⟩
    -- Note `(w₂ - w₁)⁻¹ ∉ f '' ball 0 1`
    have hw_diff_ne : w₂ - w₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hw_eq)
    have hinv_omit : (w₂ - w₁)⁻¹ ∉ f '' ball (0 : ℂ) 1 := by
      rintro ⟨z, hz, heq⟩
      by_cases hz0 : z = 0
      · subst hz0
        rw [hf0] at heq
        exact inv_ne_zero hw_diff_ne heq.symm
      · rw [hf_eq_inv z ⟨hz, hz0⟩] at heq
        have hFw₂ : F z = w₂ := by
          have := inv_injective heq
          linear_combination this
        exact hw₂ ⟨z, ⟨hz, hz0⟩, hFw₂⟩
    -- Apply Koebe `1/4` (`theorem14_14`)
    obtain ⟨a_f, ⟨_, _, haf_sum, _⟩, _⟩ := classS_taylor_expansion hf_S
    have hkoebe := (theorem14_14.1 hf_S haf_sum).2
    have hge_quarter : 1 / 4 ≤ ‖(w₂ - w₁)⁻¹‖ := by
      by_contra hlt
      have hlt' : ‖(w₂ - w₁)⁻¹‖ < 1 / 4 := not_le.mp hlt
      exact hinv_omit (hkoebe (mem_ball_zero_iff.mpr hlt'))
    rw [norm_inv, norm_sub_rev] at hge_quarter
    have hle : ‖w₁ - w₂‖ ≤ (1 / 4 : ℝ)⁻¹ := by
      simpa only [inv_inv] using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) hge_quarter
    norm_num at hle
    exact hle
  · -- Sharpness: `F₀(z) = z⁻¹ + z` omits precisely `[-2, 2]`
    dsimp only
    obtain ⟨hF₀_holo1, hF₀_inj1, _⟩ := theorem14_13.2 (α := 1) (by simp)
    have hF₀_holo : RudinRCA.Chapter10.HolomorphicOn (fun z : ℂ => z⁻¹ + z)
        (ball (0 : ℂ) 1 \ {0}) := by
      simpa only [one_mul] using hF₀_holo1
    have hF₀_inj : InjOn (fun z : ℂ => z⁻¹ + z) (ball (0 : ℂ) 1 \ {0}) := by
      simpa only [one_mul] using hF₀_inj1
    refine ⟨hF₀_holo, hF₀_inj, ?_, ?_, ?_⟩
    · have heq : (fun z : ℂ => (z⁻¹ + z) - z⁻¹) = fun z : ℂ => z := by ext z; ring
      rw [heq]
      exact continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
    · ext w
      constructor
      · intro hw_not
        rw [Set.mem_compl_iff] at hw_not
        -- Solve `ζ^2 - w * ζ + 1 = 0` in `ℂ` explicitly via `exists_unit_sq_direction (w^2 - 4)`
        obtain ⟨rot_w, _, hrot_w_sq⟩ := exists_unit_sq_direction (w ^ 2 - 4)
        let s : ℂ := (Real.sqrt ‖w ^ 2 - 4‖ : ℂ) * rot_w
        have hs_sq : s ^ 2 = w ^ 2 - 4 := by
          dsimp [s]
          rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (norm_nonneg _), hrot_w_sq]
        let ζ : ℂ := (w + s) / 2
        have hζ_eq : ζ ^ 2 - w * ζ + 1 = 0 := by
          dsimp [ζ]
          linear_combination (1 / 4 : ℂ) * hs_sq
        have hζ_ne0 : ζ ≠ 0 := by
          intro h0; rw [h0] at hζ_eq; norm_num at hζ_eq
        have hζ_sum : ζ⁻¹ + ζ = w := by
          have hmul : ζ * (ζ⁻¹ + ζ) = ζ * w := by
            rw [mul_add, mul_inv_cancel₀ hζ_ne0]
            linear_combination hζ_eq
          exact mul_left_cancel₀ hζ_ne0 hmul
        -- `‖ζ‖` must be `1`, otherwise either `ζ` (`‖ζ‖ < 1`) or `ζ⁻¹` (`‖ζ‖ > 1`) lies in `U \ {0}`!
        have hζ_norm1 : ‖ζ‖ = 1 := by
          rcases lt_trichotomy ‖ζ‖ 1 with hlt | heq1 | hgt
          · exact False.elim (hw_not ⟨ζ, ⟨mem_ball_zero_iff.mpr hlt, hζ_ne0⟩, hζ_sum⟩)
          · exact heq1
          · have hinv_lt : ‖ζ⁻¹‖ < 1 := by
              rw [norm_inv]
              exact inv_lt_one_of_one_lt₀ hgt
            have hinv_sum : (ζ⁻¹)⁻¹ + ζ⁻¹ = w := by
              rw [inv_inv, add_comm, hζ_sum]
            exact False.elim (hw_not ⟨ζ⁻¹, ⟨mem_ball_zero_iff.mpr hinv_lt, inv_ne_zero hζ_ne0⟩,
              hinv_sum⟩)
        have hζ_inv_conj : ζ⁻¹ = starRingEnd ℂ ζ := by
          apply mul_left_cancel₀ hζ_ne0
          rw [mul_inv_cancel₀ hζ_ne0, Complex.mul_conj', hζ_norm1]
          norm_num
        refine ⟨2 * ζ.re, ?_, ?_⟩
        · have habs : |ζ.re| ≤ 1 := by
            rw [← hζ_norm1]
            exact Complex.abs_re_le_norm ζ
          rw [abs_le] at habs
          constructor <;> linarith
        · rw [← hζ_sum, hζ_inv_conj]
          apply Complex.ext <;> simp <;> ring
      · rintro ⟨x, ⟨hx_lo, hx_hi⟩, rfl⟩
        rw [Set.mem_compl_iff]
        rintro ⟨z, ⟨hz_ball, hz_ne0⟩, heq⟩
        dsimp at heq
        have hz0 : z ≠ 0 := hz_ne0
        have hz_quad : z ^ 2 - (x : ℂ) * z + 1 = 0 := by
          have hmul : z * (z⁻¹ + z) = z * (x : ℂ) := congrArg (z * ·) heq
          rw [mul_add, mul_inv_cancel₀ hz0] at hmul
          linear_combination hmul
        have hy_nonneg : 0 ≤ 1 - (x / 2) ^ 2 := by nlinarith
        let y : ℝ := Real.sqrt (1 - (x / 2) ^ 2)
        have hy_sq : y ^ 2 = 1 - (x / 2) ^ 2 := Real.sq_sqrt hy_nonneg
        let r₁ : ℂ := ⟨x / 2, y⟩
        let r₂ : ℂ := ⟨x / 2, -y⟩
        have hfac : (z - r₁) * (z - r₂) = 0 := by
          have hprod : r₁ * r₂ = 1 := by
            apply Complex.ext
            · dsimp [r₁, r₂]
              simp only [Complex.mul_re, mul_neg, sub_neg_eq_add]
              nlinarith [hy_sq]
            · dsimp [r₁, r₂]; simp; ring
          have hsum : r₁ + r₂ = (x : ℂ) := by
            apply Complex.ext <;> dsimp [r₁, r₂] <;> simp <;> ring
          have hexp : (z - r₁) * (z - r₂) = z ^ 2 - (r₁ + r₂) * z + r₁ * r₂ := by ring
          rw [hexp, hsum, hprod, hz_quad]
        have hlt1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz_ball
        rcases mul_eq_zero.mp hfac with h1 | h2
        · have hzr₁ : z = r₁ := sub_eq_zero.mp h1
          have hsq1 : ‖z‖ ^ 2 = 1 := by
            rw [hzr₁, Complex.sq_norm, Complex.normSq_apply]
            dsimp [r₁]
            nlinarith [hy_sq]
          nlinarith [norm_nonneg z]
        · have hzr₂ : z = r₂ := sub_eq_zero.mp h2
          have hsq2 : ‖z‖ ^ 2 = 1 := by
            rw [hzr₂, Complex.sq_norm, Complex.normSq_apply]
            dsimp [r₂]
            nlinarith [hy_sq]
          nlinarith [norm_nonneg z]
    · have h4 : (2 : ℂ) - (-2 : ℂ) = ((4 : ℝ) : ℂ) := by norm_num
      rw [h4, Complex.norm_real, Real.norm_eq_abs]
      norm_num

/-! ### Nodes 14.16 and 14.17: Simple Boundary Points and Slit-Disc / Comb-Square Examples -/

/-- **Definition 14.16 (Simple boundary point, RCA p. 289):**
For a region `Ω ⊆ ℂ`, a boundary point `β ∈ frontier Ω` is **simple** if for every sequence
`α : ℕ → ℂ` in `Ω` converging to `β` (without passing to any subsequence), there exist a continuous
curve `γ : [0, 1] → ℂ` and a strictly increasing sequence `t : ℕ → ℝ` in `(0, 1)` converging to `1`
such that `γ([0, 1)) ⊆ Ω` and `γ(t_n) = α_n` for all `n`. -/
def IsSimpleBoundaryPoint (Ω : Set ℂ) (β : ℂ) : Prop :=
  β ∈ frontier Ω ∧
  ∀ α : ℕ → ℂ, (∀ n, α n ∈ Ω) → Tendsto α atTop (𝓝 β) →
    ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 1) ∧
      (∀ s ∈ Ico (0 : ℝ) 1, γ s ∈ Ω) ∧
      ∃ t : ℕ → ℝ, StrictMono t ∧ (∀ n, t n ∈ Ioo (0 : ℝ) 1) ∧
        Tendsto t atTop (𝓝 1) ∧ ∀ n, γ (t n) = α n

/-- **Node 14.16 (Endpoint continuity consequence, RCA p. 289):**
For any curve `γ : [0, 1] → ℂ` continuous on `[0, 1]` and parameter sequence `t_n ∈ (0, 1)`
tending to `1` that interpolates `α_n = γ(t_n)` where `α_n → β`, continuity forces `γ(1) = β`. -/
theorem theorem14_16 :
    (∀ {β : ℂ} {α : ℕ → ℂ} {γ : ℝ → ℂ} {t : ℕ → ℝ},
      Tendsto α atTop (𝓝 β) →
      ContinuousOn γ (Icc (0 : ℝ) 1) →
      (∀ n, t n ∈ Ioo (0 : ℝ) 1) →
      Tendsto t atTop (𝓝 1) →
      (∀ n, γ (t n) = α n) →
      γ 1 = β) ∧
    (∀ {Ω : Set ℂ} {β : ℂ}, IsSimpleBoundaryPoint Ω β →
      ∀ α : ℕ → ℂ, (∀ n, α n ∈ Ω) → Tendsto α atTop (𝓝 β) →
        ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 1) ∧
          (∀ s ∈ Ico (0 : ℝ) 1, γ s ∈ Ω) ∧
          γ 1 = β ∧
          ∃ t : ℕ → ℝ, StrictMono t ∧ (∀ n, t n ∈ Ioo (0 : ℝ) 1) ∧
            Tendsto t atTop (𝓝 1) ∧ ∀ n, γ (t n) = α n) := by
  have hforce : ∀ {β : ℂ} {α : ℕ → ℂ} {γ : ℝ → ℂ} {t : ℕ → ℝ},
      Tendsto α atTop (𝓝 β) →
      ContinuousOn γ (Icc (0 : ℝ) 1) →
      (∀ n, t n ∈ Ioo (0 : ℝ) 1) →
      Tendsto t atTop (𝓝 1) →
      (∀ n, γ (t n) = α n) →
      γ 1 = β := by
    intro β α γ t hα hγ ht_mem ht_lim hγt
    have ht_nhds : Tendsto t atTop (𝓝[Icc (0 : ℝ) 1] 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within t ht_lim
        (Filter.Eventually.of_forall fun n => Ioo_subset_Icc_self (ht_mem n))
    have hcomp : Tendsto (γ ∘ t) atTop (𝓝 (γ 1)) :=
      (hγ 1 (right_mem_Icc.mpr zero_le_one)).tendsto.comp ht_nhds
    have heq : γ ∘ t = α := funext hγt
    rw [heq] at hcomp
    exact tendsto_nhds_unique hcomp hα
  refine ⟨fun hα hγ ht_mem ht_lim hγt => hforce hα hγ ht_mem ht_lim hγt, ?_⟩
  intro Ω β hsimple α hα_mem hα_lim
  obtain ⟨γ, hγ_cont, hγ_in, t, ht_mono, ht_mem, ht_lim, hγt⟩ :=
    hsimple.2 α hα_mem hα_lim
  exact ⟨γ, hγ_cont, hγ_in, hforce hα_lim hγ_cont ht_mem ht_lim hγt,
    t, ht_mono, ht_mem, ht_lim, hγt⟩

/-- Every open subset `Ω ⊆ ℂ` star-shaped around `z₀ ∈ Ω` is a simply connected region. -/
theorem bookSimplyConnected_of_starConvex {Ω : Set ℂ} {z₀ : ℂ}
    (hopen : IsOpen Ω) (hz₀ : z₀ ∈ Ω) (hstar : StarConvex ℝ z₀ Ω) :
    RudinRCA.Chapter10.BookSimplyConnected Ω := by
  have heq : Ω = ⋃ y ∈ Ω, segment ℝ z₀ y := by
    ext w
    constructor
    · intro hw
      exact Set.mem_biUnion hw (right_mem_segment ℝ z₀ w)
    · intro hw
      rcases Set.mem_iUnion₂.mp hw with ⟨y, hy, ⟨a, b, ha, hb, hab, rfl⟩⟩
      exact hstar hy ha hb hab
  have hpre : IsPreconnected Ω := by
    rw [heq, Set.biUnion_eq_iUnion]
    exact isPreconnected_iUnion
      ⟨z₀, Set.mem_iInter.mpr fun y => left_mem_segment ℝ z₀ y.1⟩
      fun y => (convex_segment z₀ y.1).isPreconnected
  have hreg : RudinRCA.Chapter10.IsRegion Ω := ⟨hopen, ⟨z₀, hz₀⟩, hpre⟩
  refine ⟨hreg, fun γ hγc hγΩ hγcl => ?_⟩
  refine ⟨z₀, hz₀, hγc, continuousOn_const, hγΩ, ?_, hγcl, rfl,
    fun p => p.2 • z₀ + (1 - p.2 : ℝ) • γ p.1, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨_, _, rfl⟩; exact hz₀
  · exact (continuousOn_snd.smul continuousOn_const).add
      ((continuousOn_const.sub continuousOn_snd).smul
        (hγc.comp continuousOn_fst fun p hp => hp.1))
  · rintro _ ⟨p, hp, rfl⟩
    exact hstar (hγΩ ⟨p.1, hp.1, rfl⟩) hp.2.1 (sub_nonneg.mpr hp.2.2) (by ring)
  · intro s _; simp
  · intro s _; simp
  · intro t _; simp [hγcl]

/-- Example 14.17(i) domain: the slit unit disc `U \ [0, 1)`. -/
def slitUnitDisc : Set ℂ :=
  ball (0 : ℂ) 1 \ ((fun x : ℝ => (x : ℂ)) '' Ico (0 : ℝ) 1)

/-- Example 14.17(ii) ambient square `{x + i y | 0 < x < 1, 0 < y < 1}`. -/
def openUnitSquare : Set ℂ :=
  {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < 1}

/-- Example 14.17(ii) bottom vertical tooth at `x = 1 / (2 n)` from `0` to `((n - 1) / n) i`. -/
def combBottomSegment (n : ℕ) : Set ℂ :=
  segment ℝ ((1 / (2 * (n : ℝ)) : ℝ) : ℂ)
    (((1 / (2 * (n : ℝ)) : ℝ) : ℂ) + ((((n : ℝ) - 1) / (n : ℝ) : ℝ) : ℂ) * Complex.I)

/-- Example 14.17(ii) top vertical tooth at `x = 1 / (2 n + 1)` from `i / n` to `i`. -/
def combTopSegment (n : ℕ) : Set ℂ :=
  segment ℝ
    (((1 / (2 * (n : ℝ) + 1) : ℝ) : ℂ) + ((1 / (n : ℝ) : ℝ) : ℂ) * Complex.I)
    (((1 / (2 * (n : ℝ) + 1) : ℝ) : ℂ) + Complex.I)

/-- Example 14.17(ii) domain: the open unit square minus the alternating vertical teeth for `n ≥ 1`. -/
def combRegion : Set ℂ :=
  openUnitSquare \ (⋃ n ∈ Ici (1 : ℕ), combBottomSegment n ∪ combTopSegment n)

theorem mem_combBottomSegment_iff {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    z ∈ combBottomSegment n ↔
      z.re = 1 / (2 * (n : ℝ)) ∧ 0 ≤ z.im ∧ z.im ≤ ((n : ℝ) - 1) / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hhi_nonneg : 0 ≤ ((n : ℝ) - 1) / (n : ℝ) := by
    apply div_nonneg _ hn_pos.le
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one,
      sub_zero, add_zero, zero_add]
    refine ⟨?_, ?_, ?_⟩
    · linear_combination (1 / (2 * (n : ℝ))) * hab
    · exact mul_nonneg hb hhi_nonneg
    · calc
        b * (((n : ℝ) - 1) / (n : ℝ)) ≤ (a + b) * (((n : ℝ) - 1) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith) hhi_nonneg
        _ = ((n : ℝ) - 1) / (n : ℝ) := by rw [hab, one_mul]
  · rintro ⟨hre, him0, him_hi⟩
    by_cases hn1 : n = 1
    · subst hn1
      simp only [Nat.cast_one, sub_self, zero_div] at him_hi
      have him_eq0 : z.im = 0 := le_antisymm him_hi him0
      refine ⟨1, 0, zero_le_one, le_rfl, add_zero 1, ?_⟩
      apply Complex.ext
      · simp [hre]
      · simp [him_eq0]
    · have hn2 : 2 ≤ n := by omega
      have hhi_pos : 0 < ((n : ℝ) - 1) / (n : ℝ) := by
        apply div_pos _ hn_pos
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
        linarith
      let b : ℝ := z.im / (((n : ℝ) - 1) / (n : ℝ))
      have hb0 : 0 ≤ b := div_nonneg him0 hhi_pos.le
      have hb1 : b ≤ 1 := (div_le_one hhi_pos).mpr him_hi
      refine ⟨1 - b, b, sub_nonneg.mpr hb1, hb0, sub_add_cancel 1 b, ?_⟩
      apply Complex.ext
      · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, sub_zero,
          add_zero]
        rw [hre]; ring
      · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, add_zero,
          zero_add]
        dsimp [b]
        exact div_mul_cancel₀ z.im hhi_pos.ne'

theorem mem_combTopSegment_iff {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    z ∈ combTopSegment n ↔
      z.re = 1 / (2 * (n : ℝ) + 1) ∧ 1 / (n : ℝ) ≤ z.im ∧ z.im ≤ 1 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hlo_le1 : 1 / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn_pos]
    exact_mod_cast hn
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one,
      sub_zero, add_zero, zero_add]
    refine ⟨?_, ?_, ?_⟩
    · linear_combination (1 / (2 * (n : ℝ) + 1)) * hab
    · calc
        1 / (n : ℝ) = (a + b) * (1 / (n : ℝ)) := by rw [hab, one_mul]
        _ ≤ a * (1 / (n : ℝ)) + b * 1 := by nlinarith [hlo_le1]
        _ = a * (1 / (n : ℝ)) + b := by ring
    · calc
        a * (1 / (n : ℝ)) + b ≤ a * 1 + b := by nlinarith [hlo_le1]
        _ = 1 := by linarith
  · rintro ⟨hre, him_lo, him_hi⟩
    by_cases hn1 : n = 1
    · subst hn1
      simp only [Nat.cast_one, div_one] at him_lo
      have him_eq1 : z.im = 1 := le_antisymm him_hi him_lo
      refine ⟨0, 1, le_rfl, zero_le_one, zero_add 1, ?_⟩
      apply Complex.ext
      · simp [hre]; norm_num
      · simp [him_eq1]
    · have hn2 : 2 ≤ n := by omega
      have hgap_pos : 0 < 1 - 1 / (n : ℝ) := by
        have hlt : 1 / (n : ℝ) < 1 := by
          rw [div_lt_one hn_pos]
          exact_mod_cast hn2
        linarith
      let b : ℝ := (z.im - 1 / (n : ℝ)) / (1 - 1 / (n : ℝ))
      have hb0 : 0 ≤ b := div_nonneg (by linarith) hgap_pos.le
      have hb1 : b ≤ 1 := (div_le_one hgap_pos).mpr (by linarith)
      refine ⟨1 - b, b, sub_nonneg.mpr hb1, hb0, sub_add_cancel 1 b, ?_⟩
      apply Complex.ext
      · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, sub_zero,
          add_zero]
        rw [hre]; ring
      · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, add_zero,
          zero_add]
        dsimp [b]
        have hmul := div_mul_cancel₀ (z.im - 1 / (n : ℝ)) hgap_pos.ne'
        linear_combination hmul

private def combStrip (k : ℕ) : Set ℂ :=
  {z : ℂ | 1 / ((k : ℝ) + 2) < z.re ∧ z.re < 1 / ((k : ℝ) + 1) ∧ 0 < z.im ∧ z.im < 1}

private def combDoor (k : ℕ) : Set ℂ :=
  if k % 2 = 0 then
    let m : ℕ := k / 2
    {z : ℂ | 1 / ((k : ℝ) + 3) < z.re ∧ z.re < 1 / ((k : ℝ) + 1) ∧
      (m : ℝ) / ((m : ℝ) + 1) < z.im ∧ z.im < 1}
  else
    let m : ℕ := k / 2
    {z : ℂ | 1 / ((k : ℝ) + 3) < z.re ∧ z.re < 1 / ((k : ℝ) + 1) ∧
      0 < z.im ∧ z.im < 1 / ((m : ℝ) + 1)}

private theorem combRegion_eq_iUnion :
    combRegion = ⋃ k : ℕ, (combStrip k ∪ combDoor k) := by
  have hrect_open : ∀ a b c d : ℝ, 0 ≤ a → b ≤ 1 → 0 ≤ c → d ≤ 1 →
      {z : ℂ | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d} ⊆ openUnitSquare := by
    intro a b c d ha hb hc hd z hz
    exact ⟨lt_of_le_of_lt ha hz.1, lt_of_lt_of_le hz.2.1 hb,
      lt_of_le_of_lt hc hz.2.2.1, lt_of_lt_of_le hz.2.2.2 hd⟩
  ext z
  constructor
  · rintro ⟨⟨hx0, hx1, hy0, hy1⟩, hnot⟩
    have hinv_gt1 : 1 < 1 / z.re := one_lt_one_div hx0 hx1
    let N : ℕ := Nat.floor (1 / z.re)
    have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hinv_gt1.le)
    have hN_le : (N : ℝ) ≤ 1 / z.re := Nat.floor_le (by positivity)
    have hlt_N1 : 1 / z.re < (N : ℝ) + 1 := Nat.lt_floor_add_one (1 / z.re)
    by_cases heq : (N : ℝ) = 1 / z.re
    · have hN_gt1 : (1 : ℝ) < (N : ℝ) := by linarith
      have hN2 : 2 ≤ N := by exact_mod_cast hN_gt1
      let k : ℕ := N - 2
      have hNk : N = k + 2 := (Nat.sub_add_cancel hN2).symm
      have hre_eq : z.re = 1 / ((k : ℝ) + 2) := by
        have h1 : 1 / z.re = (k : ℝ) + 2 := by
          rw [← heq, hNk]; push_cast; ring
        have hpos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        rw [div_eq_iff hx0.ne'] at h1
        rw [eq_div_iff hpos.ne']
        linarith
      have hre_lo : 1 / ((k : ℝ) + 3) < z.re := by
        rw [hre_eq]
        exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
      have hre_hi : z.re < 1 / ((k : ℝ) + 1) := by
        rw [hre_eq]
        exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
      refine Set.mem_iUnion.mpr ⟨k, Or.inr ?_⟩
      by_cases hpar : k % 2 = 0
      · dsimp [combDoor]
        rw [if_pos hpar]
        refine ⟨hre_lo, hre_hi, ?_, hy1⟩
        let m : ℕ := k / 2
        have hk_eq : k = 2 * m := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hpar)).symm
        let n : ℕ := m + 1
        have hn1 : 1 ≤ n := Nat.le_add_left 1 m
        have hre_n : z.re = 1 / (2 * (n : ℝ)) := by
          rw [hre_eq]
          congr 1
          have : (k : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hk_eq
          have : (n : ℝ) = (m : ℝ) + 1 := by exact_mod_cast rfl
          linarith
        have hnot_bot : z ∉ combBottomSegment n := fun hmem =>
          hnot (Set.mem_iUnion₂.mpr ⟨n, hn1, Or.inl hmem⟩)
        rw [mem_combBottomSegment_iff hn1] at hnot_bot
        have hnot_le : ¬ z.im ≤ ((n : ℝ) - 1) / (n : ℝ) := fun hle =>
          hnot_bot ⟨hre_n, hy0.le, hle⟩
        have hfrac_eq : ((n : ℝ) - 1) / (n : ℝ) = (m : ℝ) / ((m : ℝ) + 1) := by
          have : (n : ℝ) = (m : ℝ) + 1 := by exact_mod_cast rfl
          rw [this]; ring
        linarith [lt_of_not_ge hnot_le]
      · dsimp [combDoor]
        rw [if_neg hpar]
        refine ⟨hre_lo, hre_hi, hy0, ?_⟩
        have hmod1 : k % 2 = 1 := by omega
        let m : ℕ := k / 2
        have hk_eq : k = 2 * m + 1 := by omega
        let n : ℕ := m + 1
        have hn1 : 1 ≤ n := Nat.le_add_left 1 m
        have hre_n : z.re = 1 / (2 * (n : ℝ) + 1) := by
          rw [hre_eq]
          congr 1
          have : (k : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hk_eq
          have : (n : ℝ) = (m : ℝ) + 1 := by exact_mod_cast rfl
          linarith
        have hnot_top : z ∉ combTopSegment n := fun hmem =>
          hnot (Set.mem_iUnion₂.mpr ⟨n, hn1, Or.inr hmem⟩)
        rw [mem_combTopSegment_iff hn1] at hnot_top
        have hnot_ge : ¬ 1 / (n : ℝ) ≤ z.im := fun hge =>
          hnot_top ⟨hre_n, hge, hy1.le⟩
        have hfrac_eq : 1 / (n : ℝ) = 1 / ((m : ℝ) + 1) := by
          have : (n : ℝ) = (m : ℝ) + 1 := by exact_mod_cast rfl
          rw [this]
        linarith [lt_of_not_ge hnot_ge]
    · have hN_lt : (N : ℝ) < 1 / z.re := lt_of_le_of_ne hN_le heq
      let k : ℕ := N - 1
      have hNk : N = k + 1 := (Nat.sub_add_cancel hN1).symm
      have hk1_lt : (k : ℝ) + 1 < 1 / z.re := by
        have : (N : ℝ) = (k : ℝ) + 1 := by exact_mod_cast hNk
        linarith
      have hk2_gt : 1 / z.re < (k : ℝ) + 2 := by
        have : (N : ℝ) = (k : ℝ) + 1 := by exact_mod_cast hNk
        linarith
      refine Set.mem_iUnion.mpr ⟨k, Or.inl ⟨?_, ?_, hy0, hy1⟩⟩
      · have h := one_div_lt_one_div_of_lt (div_pos one_pos hx0) hk2_gt
        rwa [one_div_one_div] at h
      · have h := one_div_lt_one_div_of_lt (by positivity) hk1_lt
        rwa [one_div_one_div] at h
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨k, hk_mem⟩
    have hsq : z ∈ openUnitSquare := by
      rcases hk_mem with hs | hd
      · refine hrect_open _ _ _ _ (by positivity) ?_ le_rfl le_rfl hs
        exact div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
      · dsimp [combDoor] at hd
        split_ifs at hd with hpar
        · refine hrect_open _ _ _ _ (by positivity) ?_ (by positivity) le_rfl hd
          exact div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
        · refine hrect_open _ _ _ _ (by positivity) ?_ le_rfl ?_ hd
          · exact div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
          · exact div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) (k / 2)]) (by positivity)
    refine ⟨hsq, ?_⟩
    intro hseg
    rcases Set.mem_iUnion₂.mp hseg with ⟨n, hn1, hbot | htop⟩
    · obtain ⟨hre, _, him_hi⟩ := (mem_combBottomSegment_iff hn1 z).mp hbot
      have hn_pos : (0 : ℝ) < 2 * (n : ℝ) := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        linarith
      rcases hk_mem with hs | hd
      · have h1 : (k : ℝ) + 1 < 2 * (n : ℝ) := by
          have := hs.2.1; rw [hre] at this
          exact (one_div_lt_one_div hn_pos (by positivity)).mp this
        have h2 : 2 * (n : ℝ) < (k : ℝ) + 2 := by
          have := hs.1; rw [hre] at this
          exact (one_div_lt_one_div (by positivity) hn_pos).mp this
        have h1_nat : k + 1 < 2 * n := by exact_mod_cast h1
        have h2_nat : 2 * n < k + 2 := by exact_mod_cast h2
        omega
      · dsimp [combDoor] at hd
        split_ifs at hd with hpar
        · have h1 : (k : ℝ) + 1 < 2 * (n : ℝ) := by
            have := hd.2.1; rw [hre] at this
            exact (one_div_lt_one_div hn_pos (by positivity)).mp this
          have h2 : 2 * (n : ℝ) < (k : ℝ) + 3 := by
            have := hd.1; rw [hre] at this
            exact (one_div_lt_one_div (by positivity) hn_pos).mp this
          have h1_nat : k + 1 < 2 * n := by exact_mod_cast h1
          have h2_nat : 2 * n < k + 3 := by exact_mod_cast h2
          have hkn : 2 * n = k + 2 := by omega
          have hmn : k / 2 + 1 = n := by omega
          have hfrac : ((k / 2 : ℕ) : ℝ) / (((k / 2 : ℕ) : ℝ) + 1) = ((n : ℝ) - 1) / (n : ℝ) := by
            have : (n : ℝ) = ((k / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hmn.symm
            rw [this]; ring
          linarith [hd.2.2.1]
        · have h1 : (k : ℝ) + 1 < 2 * (n : ℝ) := by
            have := hd.2.1; rw [hre] at this
            exact (one_div_lt_one_div hn_pos (by positivity)).mp this
          have h2 : 2 * (n : ℝ) < (k : ℝ) + 3 := by
            have := hd.1; rw [hre] at this
            exact (one_div_lt_one_div (by positivity) hn_pos).mp this
          have h1_nat : k + 1 < 2 * n := by exact_mod_cast h1
          have h2_nat : 2 * n < k + 3 := by exact_mod_cast h2
          omega
    · obtain ⟨hre, him_lo, _⟩ := (mem_combTopSegment_iff hn1 z).mp htop
      have hn_pos : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
      rcases hk_mem with hs | hd
      · have h1 : (k : ℝ) + 1 < 2 * (n : ℝ) + 1 := by
          have := hs.2.1; rw [hre] at this
          exact (one_div_lt_one_div hn_pos (by positivity)).mp this
        have h2 : 2 * (n : ℝ) + 1 < (k : ℝ) + 2 := by
          have := hs.1; rw [hre] at this
          exact (one_div_lt_one_div (by positivity) hn_pos).mp this
        have h1_nat : k + 1 < 2 * n + 1 := by exact_mod_cast h1
        have h2_nat : 2 * n + 1 < k + 2 := by exact_mod_cast h2
        omega
      · dsimp [combDoor] at hd
        split_ifs at hd with hpar
        · have h1 : (k : ℝ) + 1 < 2 * (n : ℝ) + 1 := by
            have := hd.2.1; rw [hre] at this
            exact (one_div_lt_one_div hn_pos (by positivity)).mp this
          have h2 : 2 * (n : ℝ) + 1 < (k : ℝ) + 3 := by
            have := hd.1; rw [hre] at this
            exact (one_div_lt_one_div (by positivity) hn_pos).mp this
          have h1_nat : k + 1 < 2 * n + 1 := by exact_mod_cast h1
          have h2_nat : 2 * n + 1 < k + 3 := by exact_mod_cast h2
          omega
        · have h1 : (k : ℝ) + 1 < 2 * (n : ℝ) + 1 := by
            have := hd.2.1; rw [hre] at this
            exact (one_div_lt_one_div hn_pos (by positivity)).mp this
          have h2 : 2 * (n : ℝ) + 1 < (k : ℝ) + 3 := by
            have := hd.1; rw [hre] at this
            exact (one_div_lt_one_div (by positivity) hn_pos).mp this
          have h1_nat : k + 1 < 2 * n + 1 := by exact_mod_cast h1
          have h2_nat : 2 * n + 1 < k + 3 := by exact_mod_cast h2
          have hkn : 2 * n + 1 = k + 2 := by omega
          have hmn : k / 2 + 1 = n := by omega
          have hfrac : 1 / (((k / 2 : ℕ) : ℝ) + 1) = 1 / (n : ℝ) := by
            have : (n : ℝ) = ((k / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hmn.symm
            rw [this]
          linarith [hd.2.2.2]

private theorem openRect_isOpen (a b c d : ℝ) :
    IsOpen {z : ℂ | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))

private theorem openRect_convex (a b c d : ℝ) :
    Convex ℝ {z : ℂ | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d} := by
  intro z₁ hz₁ z₂ hz₂ u v hu hv huv
  simp only [Set.mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero]
  by_cases hv0 : v = 0
  · subst hv0
    have hu1 : u = 1 := by linarith
    subst hu1
    simp [hz₁.1, hz₁.2.1, hz₁.2.2.1, hz₁.2.2.2]
  · have hv_pos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc
        a = (u + v) * a := by rw [huv, one_mul]
        _ < u * z₁.re + v * z₂.re := by nlinarith [hz₁.1, hz₂.1]
    · calc
        u * z₁.re + v * z₂.re < (u + v) * b := by nlinarith [hz₁.2.1, hz₂.2.1]
        _ = b := by rw [huv, one_mul]
    · calc
        c = (u + v) * c := by rw [huv, one_mul]
        _ < u * z₁.im + v * z₂.im := by nlinarith [hz₁.2.2.1, hz₂.2.2.1]
    · calc
        u * z₁.im + v * z₂.im < (u + v) * d := by nlinarith [hz₁.2.2.2, hz₂.2.2.2]
        _ = d := by rw [huv, one_mul]

theorem combRegion_bookSimplyConnected :
    RudinRCA.Chapter10.BookSimplyConnected combRegion := by
  have hstrip_open : ∀ k, IsOpen (combStrip k) := fun k => openRect_isOpen _ _ _ _
  have hstrip_conv : ∀ k, Convex ℝ (combStrip k) := fun k => openRect_convex _ _ _ _
  have hdoor_open : ∀ k, IsOpen (combDoor k) := by
    intro k; dsimp [combDoor]; split_ifs <;> exact openRect_isOpen _ _ _ _
  have hdoor_conv : ∀ k, Convex ℝ (combDoor k) := by
    intro k; dsimp [combDoor]; split_ifs <;> exact openRect_convex _ _ _ _
  have hcomb_open : IsOpen combRegion := by
    rw [combRegion_eq_iUnion]
    exact isOpen_iUnion fun k => (hstrip_open k).union (hdoor_open k)
  let yDoor : ℕ → ℝ := fun k =>
    if k % 2 = 0 then
      (((k / 2 : ℕ) : ℝ) / (((k / 2 : ℕ) : ℝ) + 1) + 1) / 2
    else
      1 / (2 * (((k / 2 : ℕ) : ℝ) + 1))
  have hyDoor_01 : ∀ k : ℕ, 0 < yDoor k ∧ yDoor k < 1 := by
    intro k
    dsimp [yDoor]
    split_ifs with hpar
    · let m : ℝ := ((k / 2 : ℕ) : ℝ)
      have hm : 0 ≤ m := Nat.cast_nonneg _
      have hlt1 : m / (m + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      have hge0 : 0 ≤ m / (m + 1) := by positivity
      exact ⟨by linarith, by linarith⟩
    · let m : ℝ := ((k / 2 : ℕ) : ℝ)
      have hm : 0 ≤ m := Nat.cast_nonneg _
      refine ⟨by positivity, ?_⟩
      exact (div_lt_one (by positivity)).mpr (by linarith)
  let xMid₁ : ℕ → ℝ := fun k => (1 / ((k : ℝ) + 2) + 1 / ((k : ℝ) + 1)) / 2
  let xMid₂ : ℕ → ℝ := fun k => (1 / ((k : ℝ) + 3) + 1 / ((k : ℝ) + 2)) / 2
  let w₁ : ℕ → ℂ := fun k => (xMid₁ k : ℂ) + (yDoor k : ℂ) * Complex.I
  let w₂ : ℕ → ℂ := fun k => (xMid₂ k : ℂ) + (yDoor k : ℂ) * Complex.I
  have hxMid₁_bounds : ∀ k : ℕ, 1 / ((k : ℝ) + 2) < xMid₁ k ∧ xMid₁ k < 1 / ((k : ℝ) + 1) := by
    intro k
    have hlt : 1 / ((k : ℝ) + 2) < 1 / ((k : ℝ) + 1) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    dsimp [xMid₁]; exact ⟨by linarith, by linarith⟩
  have hxMid₂_bounds : ∀ k : ℕ, 1 / ((k : ℝ) + 3) < xMid₂ k ∧ xMid₂ k < 1 / ((k : ℝ) + 2) := by
    intro k
    have hlt : 1 / ((k : ℝ) + 3) < 1 / ((k : ℝ) + 2) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    dsimp [xMid₂]; exact ⟨by linarith, by linarith⟩
  have hw₁_strip : ∀ k : ℕ, w₁ k ∈ combStrip k := by
    intro k
    have hx := hxMid₁_bounds k
    have hy := hyDoor_01 k
    dsimp [combStrip, w₁]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, add_zero, zero_add]
    exact ⟨hx.1, hx.2, hy.1, hy.2⟩
  have hw₂_strip : ∀ k : ℕ, w₂ k ∈ combStrip (k + 1) := by
    intro k
    have hx := hxMid₂_bounds k
    have hy := hyDoor_01 k
    have hcast1 : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
    have hcast2 : ((k + 1 : ℕ) : ℝ) + 2 = (k : ℝ) + 3 := by push_cast; ring
    dsimp [combStrip, w₂]
    rw [hcast1, hcast2]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, add_zero, zero_add]
    exact ⟨hx.1, hx.2, hy.1, hy.2⟩
  have hyDoor_door : ∀ (k : ℕ) (x : ℝ),
      1 / ((k : ℝ) + 3) < x → x < 1 / ((k : ℝ) + 1) →
      (x : ℂ) + (yDoor k : ℂ) * Complex.I ∈ combDoor k := by
    intro k x hx_lo hx_hi
    dsimp [combDoor, yDoor]
    split_ifs with hpar
    · let m : ℝ := ((k / 2 : ℕ) : ℝ)
      have hm : 0 ≤ m := Nat.cast_nonneg _
      have hlt1 : m / (m + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      simp only [Set.mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        sub_zero, add_zero, zero_add]
      exact ⟨hx_lo, hx_hi, by linarith, by linarith⟩
    · let m : ℝ := ((k / 2 : ℕ) : ℝ)
      have hm : 0 ≤ m := Nat.cast_nonneg _
      have hpos : 0 < 1 / (m + 1) := by positivity
      simp only [Set.mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        sub_zero, add_zero, zero_add]
      refine ⟨hx_lo, hx_hi, by positivity, ?_⟩
      change 1 / (2 * (m + 1)) < 1 / (m + 1)
      have : 1 / (2 * (m + 1)) = (1 / (m + 1)) / 2 := by rw [div_div, mul_comm (m + 1) 2]
      linarith
  have hw₁_door : ∀ k : ℕ, w₁ k ∈ combDoor k := by
    intro k
    have hx := hxMid₁_bounds k
    have hlo : 1 / ((k : ℝ) + 3) < 1 / ((k : ℝ) + 2) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    exact hyDoor_door k (xMid₁ k) (lt_trans hlo hx.1) hx.2
  have hw₂_door : ∀ k : ℕ, w₂ k ∈ combDoor k := by
    intro k
    have hx := hxMid₂_bounds k
    have hhi : 1 / ((k : ℝ) + 2) < 1 / ((k : ℝ) + 1) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    exact hyDoor_door k (xMid₂ k) hx.1 (lt_trans hx.2 hhi)
  let U : ℕ → Set ℂ := fun k => combStrip k ∪ combDoor k
  have hU_pre : ∀ k, IsPreconnected (U k) := fun k =>
    (hstrip_conv k).isPreconnected.union (w₁ k) (hw₁_strip k) (hw₁_door k)
      (hdoor_conv k).isPreconnected
  let V : ℕ → Set ℂ := fun K => ⋃ k ≤ K, U k
  have hV_pre : ∀ K, IsPreconnected (V K) := by
    intro K
    induction K with
    | zero =>
      have hV0 : V 0 = U 0 := by
        ext z; simp [V]
      rw [hV0]
      exact hU_pre 0
    | succ K ih =>
      have hVK : V (K + 1) = V K ∪ U (K + 1) := by
        ext z
        simp only [V, Set.mem_iUnion, Set.mem_union]
        constructor
        · rintro ⟨k, hk, hzk⟩
          rcases Nat.of_le_succ hk with hle | rfl
          · exact Or.inl ⟨k, hle, hzk⟩
          · exact Or.inr hzk
        · rintro (⟨k, hk, hzk⟩ | hzk)
          · exact ⟨k, Nat.le_succ_of_le hk, hzk⟩
          · exact ⟨K + 1, le_rfl, hzk⟩
      rw [hVK]
      exact ih.union (w₂ K) (Set.mem_iUnion₂.mpr ⟨K, le_rfl, Or.inr (hw₂_door K)⟩)
        (Or.inl (hw₂_strip K)) (hU_pre (K + 1))
  have hcomb_eq_V : combRegion = ⋃ K : ℕ, V K := by
    rw [combRegion_eq_iUnion]
    ext z
    simp only [Set.mem_iUnion, V, U]
    constructor
    · rintro ⟨k, hzk⟩; exact ⟨k, k, le_rfl, hzk⟩
    · rintro ⟨K, k, _, hzk⟩; exact ⟨k, hzk⟩
  have hcomb_pre : IsPreconnected combRegion := by
    rw [hcomb_eq_V]
    exact isPreconnected_iUnion
      ⟨w₁ 0, Set.mem_iInter.mpr fun K => Set.mem_iUnion₂.mpr ⟨0, Nat.zero_le K, Or.inl (hw₁_strip 0)⟩⟩
      hV_pre
  have hw₁0_comb : w₁ 0 ∈ combRegion := by
    rw [combRegion_eq_iUnion]
    exact Set.mem_iUnion.mpr ⟨0, Or.inl (hw₁_strip 0)⟩
  have hcomb_reg : RudinRCA.Chapter10.IsRegion combRegion :=
    ⟨hcomb_open, ⟨w₁ 0, hw₁0_comb⟩, hcomb_pre⟩
  -- Connectedness of `sphericalCompl combRegion` via `openUnitSquare` and the teeth
  have hsq_reg : RudinRCA.Chapter10.IsRegion openUnitSquare :=
    ⟨openRect_isOpen 0 1 0 1,
      ⟨(1 / 2 : ℂ) + (1 / 2 : ℂ) * Complex.I, by simp [openUnitSquare]; norm_num⟩,
      (openRect_convex 0 1 0 1).isPreconnected⟩
  have hsq_sc : RudinRCA.Chapter10.BookSimplyConnected openUnitSquare :=
    RudinRCA.Chapter10.theorem10_38 hsq_reg (openRect_convex 0 1 0 1)
  have hS₀_conn : IsConnected (RudinRCA.Chapter13.sphericalCompl openUnitSquare) :=
    (((RudinRCA.Chapter13.theorem13_11 hsq_reg).2.2.1).trans
      (RudinRCA.Chapter13.theorem13_11 hsq_reg).2.2.2.1).mp hsq_sc
  let S₀ : Set RudinRCA.Chapter13.RiemannSphere := RudinRCA.Chapter13.sphericalCompl openUnitSquare
  let coeS : ℂ → RudinRCA.Chapter13.RiemannSphere := (↑)
  let C : ℕ → Set RudinRCA.Chapter13.RiemannSphere := fun m =>
    (S₀ ∪ coeS '' combBottomSegment (m + 1)) ∪ (S₀ ∪ coeS '' combTopSegment (m + 1))
  have hC_pre : ∀ m : ℕ, IsPreconnected (C m) := by
    intro m
    let n : ℕ := m + 1
    let p_bot : ℂ := ((1 / (2 * (n : ℝ)) : ℝ) : ℂ)
    have hp_bot_S₀ : coeS p_bot ∈ S₀ := by
      rw [RudinRCA.Chapter13.coe_mem_sphericalCompl]
      intro hmem
      have : (0 : ℝ) < p_bot.im := hmem.2.2.1
      simp [p_bot] at this
    have hp_bot_seg : coeS p_bot ∈ coeS '' combBottomSegment n :=
      ⟨p_bot, left_mem_segment ℝ _ _, rfl⟩
    have hbot_conv : Convex ℝ (combBottomSegment n) := convex_segment _ _
    have hpre_bot : IsPreconnected (S₀ ∪ coeS '' combBottomSegment n) :=
      hS₀_conn.isPreconnected.union (coeS p_bot) hp_bot_S₀ hp_bot_seg
        (hbot_conv.isPreconnected.image _ OnePoint.continuous_coe.continuousOn)
    let p_top : ℂ := ((1 / (2 * (n : ℝ) + 1) : ℝ) : ℂ) + Complex.I
    have hp_top_S₀ : coeS p_top ∈ S₀ := by
      rw [RudinRCA.Chapter13.coe_mem_sphericalCompl]
      intro hmem
      have : p_top.im < 1 := hmem.2.2.2
      simp [p_top] at this
    have hp_top_seg : coeS p_top ∈ coeS '' combTopSegment n :=
      ⟨p_top, right_mem_segment ℝ _ _, rfl⟩
    have htop_conv : Convex ℝ (combTopSegment n) := convex_segment _ _
    have hpre_top : IsPreconnected (S₀ ∪ coeS '' combTopSegment n) :=
      hS₀_conn.isPreconnected.union (coeS p_top) hp_top_S₀ hp_top_seg
        (htop_conv.isPreconnected.image _ OnePoint.continuous_coe.continuousOn)
    have hinf_S₀ : (∞ : RudinRCA.Chapter13.RiemannSphere) ∈ S₀ :=
      RudinRCA.Chapter13.infinity_mem_sphericalCompl openUnitSquare
    exact hpre_bot.union ∞ (Or.inl hinf_S₀) (Or.inl hinf_S₀) hpre_top
  have hS_comb_eq : RudinRCA.Chapter13.sphericalCompl combRegion = ⋃ m : ℕ, C m := by
    ext p
    induction p using OnePoint.rec with
    | infty =>
      simp only [RudinRCA.Chapter13.infinity_mem_sphericalCompl, true_iff, Set.mem_iUnion]
      exact ⟨0, Or.inl (Or.inl (RudinRCA.Chapter13.infinity_mem_sphericalCompl _))⟩
    | coe z =>
      simp only [RudinRCA.Chapter13.coe_mem_sphericalCompl, Set.mem_iUnion, C, S₀, coeS,
        Set.mem_union, OnePoint.coe_injective.mem_set_image]
      constructor
      · intro hnot
        by_cases hsq : z ∈ openUnitSquare
        · have hseg : z ∈ ⋃ n ∈ Ici (1 : ℕ), combBottomSegment n ∪ combTopSegment n := by
            by_contra hnot_seg
            exact hnot ⟨hsq, hnot_seg⟩
          rcases Set.mem_iUnion₂.mp hseg with ⟨n, hn1, hbot | htop⟩
          · have hnm : n - 1 + 1 = n := Nat.sub_add_cancel hn1
            exact ⟨n - 1, Or.inl (Or.inr (by rwa [hnm]))⟩
          · have hnm : n - 1 + 1 = n := Nat.sub_add_cancel hn1
            exact ⟨n - 1, Or.inr (Or.inr (by rwa [hnm]))⟩
        · exact ⟨0, Or.inl (Or.inl hsq)⟩
      · rintro ⟨m, (hsq | hbot) | (hsq | htop)⟩ ⟨hz_sq, hz_not⟩
        · exact hsq hz_sq
        · exact hz_not (Set.mem_iUnion₂.mpr ⟨m + 1, Nat.le_add_left 1 m, Or.inl hbot⟩)
        · exact hsq hz_sq
        · exact hz_not (Set.mem_iUnion₂.mpr ⟨m + 1, Nat.le_add_left 1 m, Or.inr htop⟩)
  have hS_comb_conn : IsConnected (RudinRCA.Chapter13.sphericalCompl combRegion) := by
    refine ⟨⟨∞, RudinRCA.Chapter13.infinity_mem_sphericalCompl combRegion⟩, ?_⟩
    rw [hS_comb_eq]
    exact isPreconnected_iUnion
      ⟨∞, Set.mem_iInter.mpr fun m => Or.inl (Or.inl (RudinRCA.Chapter13.infinity_mem_sphericalCompl _))⟩
      hC_pre
  exact (((RudinRCA.Chapter13.theorem13_11 hcomb_reg).2.2.1).trans
    (RudinRCA.Chapter13.theorem13_11 hcomb_reg).2.2.2.1).mpr hS_comb_conn

/-- **Examples 14.17 (Nonsimple boundary points on simply connected regions, RCA p. 289):**
1. **Slit unit disc (`14.17(i)`):** `slitUnitDisc = U \ [0, 1)` is a simply connected region, and
   every real `β ∈ (0, 1]` lies in `frontier slitUnitDisc` and fails `IsSimpleBoundaryPoint`.
2. **Comb region (`14.17(ii)`):** `combRegion`, obtained from the open unit square
   `{x + i y | 0 < x < 1, 0 < y < 1}` by removing for each integer `n ≥ 1` the closed vertical
   segments `[1/(2n), 1/(2n) + ((n - 1)/n) i]` and `[1/(2n + 1) + i/n, 1/(2n + 1) + i]`, is a
   simply connected region, and every point `i y` (`0 ≤ y ≤ 1`) lies in `frontier combRegion`
   and fails `IsSimpleBoundaryPoint`. -/
theorem theorem14_17 :
    (RudinRCA.Chapter10.BookSimplyConnected slitUnitDisc ∧
      ∀ β ∈ Ioc (0 : ℝ) 1,
        (β : ℂ) ∈ frontier slitUnitDisc ∧ ¬ IsSimpleBoundaryPoint slitUnitDisc (β : ℂ)) ∧
    (RudinRCA.Chapter10.BookSimplyConnected combRegion ∧
      ∀ y ∈ Icc (0 : ℝ) 1,
        Complex.I * (y : ℂ) ∈ frontier combRegion ∧
          ¬ IsSimpleBoundaryPoint combRegion (Complex.I * (y : ℂ))) := by
  have hslit_eq : slitUnitDisc = ball (0 : ℂ) 1 \ ((fun x : ℝ => (x : ℂ)) '' Icc (0 : ℝ) 1) := by
    ext z
    simp only [slitUnitDisc, Set.mem_diff, Metric.mem_ball, dist_zero_right, Set.mem_image]
    refine and_congr_right fun hnorm => not_congr ⟨?_, ?_⟩
    · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
      exact ⟨x, ⟨hx0, hx1.le⟩, rfl⟩
    · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
      refine ⟨x, ⟨hx0, ?_⟩, rfl⟩
      rcases hx1.eq_or_lt with rfl | hlt
      · norm_num at hnorm
      · exact hlt
  have hslit_open : IsOpen slitUnitDisc := by
    rw [hslit_eq]
    exact isOpen_ball.sdiff (isCompact_Icc.image Complex.continuous_ofReal).isClosed
  have hmhalf_mem : (-1 / 2 : ℂ) ∈ slitUnitDisc := by
    refine ⟨by simp [Metric.mem_ball, dist_zero_right]; norm_num, ?_⟩
    rintro ⟨x, ⟨hx0, _⟩, heq⟩
    have hre := congr_arg Complex.re heq
    simp only [Complex.ofReal_re] at hre
    have hval : (-1 / 2 : ℂ).re = -1 / 2 := by norm_num
    linarith
  have hslit_re_neg_of_im_zero : ∀ {z : ℂ}, z ∈ slitUnitDisc → z.im = 0 → z.re < 0 := by
    intro z hz him
    by_contra hnot_lt
    have hge0 : 0 ≤ z.re := le_of_not_gt hnot_lt
    have hz_eq : ((z.re : ℝ) : ℂ) = z := by
      apply Complex.ext <;> simp [him]
    have hnorm : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz.1
    have hre_lt1 : z.re < 1 := by
      have : |z.re| < 1 := by
        rw [← Real.norm_eq_abs, ← Complex.norm_real, hz_eq]
        exact hnorm
      exact (abs_lt.mp this).2
    exact hz.2 ⟨z.re, ⟨hge0, hre_lt1⟩, hz_eq⟩
  have hslit_sc : RudinRCA.Chapter10.BookSimplyConnected slitUnitDisc := by
    refine bookSimplyConnected_of_starConvex hslit_open hmhalf_mem ?_
    intro z hz a b ha hb hab
    let w : ℂ := a • (-1 / 2 : ℂ) + b • z
    have hnorm_z : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz.1
    have hw_ball : w ∈ ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      have htri : ‖w‖ ≤ ‖a • (-1 / 2 : ℂ)‖ + ‖b • z‖ := norm_add_le _ _
      have ha_norm : ‖a • (-1 / 2 : ℂ)‖ = a * (1 / 2) := by
        rw [norm_smul, Real.norm_of_nonneg ha]
        norm_num
      have hb_norm : ‖b • z‖ = b * ‖z‖ := by
        rw [norm_smul, Real.norm_of_nonneg hb]
      by_cases hb0 : b = 0
      · subst hb0
        have ha1 : a = 1 := by linarith
        subst ha1
        linarith
      · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        nlinarith
    refine ⟨hw_ball, ?_⟩
    rintro ⟨x, ⟨hx0, _⟩, hwx⟩
    have him_w : w.im = b * z.im := by
      dsimp [w]
      simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im]
      have : (-1 / 2 : ℂ).im = 0 := by norm_num
      rw [this]; ring
    have hx_im : w.im = 0 := by
      have h1 := congr_arg Complex.im hwx
      simp only [Complex.ofReal_im] at h1
      exact h1.symm
    have hbz_im : b * z.im = 0 := by linarith
    have hre_w : w.re = a * (-1 / 2) + b * z.re := by
      dsimp [w]
      simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
      have : (-1 / 2 : ℂ).re = -1 / 2 := by norm_num
      rw [this]; ring
    have hx_re : x = w.re := by
      have h1 := congr_arg Complex.re hwx
      simp only [Complex.ofReal_re] at h1
      exact h1
    rcases mul_eq_zero.mp hbz_im with hb0 | hzim0
    · subst hb0
      have ha1 : a = 1 := by linarith
      subst ha1
      linarith
    · have hb_pos : 0 < b := by
        by_contra hnot_pos
        have hb0 : b = 0 := le_antisymm (le_of_not_gt hnot_pos) hb
        subst hb0
        have ha1 : a = 1 := by linarith
        subst ha1
        linarith
      have hzre_neg : z.re < 0 := hslit_re_neg_of_im_zero hz hzim0
      nlinarith
  refine ⟨⟨hslit_sc, ?_⟩, ⟨combRegion_bookSimplyConnected, ?_⟩⟩
  -- Part (i) boundary points `β ∈ (0, 1]`
  · intro β ⟨hβ0, hβ1⟩
    let x : ℕ → ℝ := fun n => β * (1 - 1 / ((n : ℝ) + 3))
    let y : ℕ → ℝ := fun n => (-1 : ℝ) ^ n / (((n : ℝ) + 3) ^ 2)
    let α : ℕ → ℂ := fun n => (x n : ℂ) + (y n : ℂ) * Complex.I
    have hα_mem : ∀ n, α n ∈ slitUnitDisc := by
      intro n
      let u : ℝ := (n : ℝ) + 3
      have hu3 : 3 ≤ u := by dsimp [u]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hu_pos : 0 < u := by linarith
      have hx_nonneg : 0 ≤ x n := by
        dsimp [x]
        apply mul_nonneg hβ0.le
        have : 1 / u ≤ 1 := div_le_one_of_le₀ (by linarith) hu_pos.le
        linarith
      have hx_le : x n ≤ 1 - 1 / u := by
        dsimp [x]
        have hnonneg : 0 ≤ 1 - 1 / u := by
          have : 1 / u ≤ 1 := div_le_one_of_le₀ (by linarith) hu_pos.le
          linarith
        nlinarith
      have hy_sq : y n ^ 2 = 1 / u ^ 4 := by
        dsimp [y]
        rw [div_pow, ← pow_mul, mul_comm n 2, pow_mul]
        norm_num
        ring
      have hnorm_sq : ‖α n‖ ^ 2 = x n ^ 2 + y n ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp [α, pow_two]
      have hsq_lt1 : x n ^ 2 + y n ^ 2 < 1 := by
        have hxcmp : x n ^ 2 ≤ (1 - 1 / u) ^ 2 :=
          pow_le_pow_left₀ hx_nonneg hx_le 2
        have hpoly : u ^ 4 * ((1 - 1 / u) ^ 2 + 1 / u ^ 4) < u ^ 4 * 1 := by
          have hu_ne : u ≠ 0 := hu_pos.ne'
          have hident : u ^ 4 * ((1 - 1 / u) ^ 2 + 1 / u ^ 4) = u ^ 4 - 2 * u ^ 3 + u ^ 2 + 1 := by
            field_simp [hu_ne]
            ring
          rw [hident]
          nlinarith [sq_nonneg (u - 3)]
        have hsum_lt : (1 - 1 / u) ^ 2 + 1 / u ^ 4 < 1 :=
          lt_of_mul_lt_mul_left hpoly (by positivity)
        linarith [hy_sq]
      have hnorm_lt1 : ‖α n‖ < 1 := by
        nlinarith [norm_nonneg (α n)]
      refine ⟨by simpa [Metric.mem_ball, dist_zero_right] using hnorm_lt1, ?_⟩
      rintro ⟨r, _, hr_eq⟩
      have him_eq := congr_arg Complex.im hr_eq
      simp only [Complex.ofReal_im, α, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add] at him_eq
      have hy_ne : y n ≠ 0 := div_ne_zero (pow_ne_zero n (by norm_num)) (by positivity)
      exact hy_ne him_eq.symm
    have hinv_u : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 3)) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hx_lim : Tendsto x atTop (𝓝 β) := by
      have h1 : Tendsto (fun n : ℕ => β * (1 - 1 / ((n : ℝ) + 3))) atTop (𝓝 (β * (1 - 0))) :=
        tendsto_const_nhds.mul (tendsto_const_nhds.sub hinv_u)
      simpa [x] using h1
    have hy_lim : Tendsto y atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hnorm_y : (fun n : ℕ => ‖y n‖) = fun n : ℕ => (1 / ((n : ℝ) + 3)) ^ 2 := by
        ext n
        dsimp [y]
        simp only [Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow,
          abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 3)]
        rw [div_pow, one_pow]
      rw [hnorm_y]
      simpa using hinv_u.pow 2
    have hα_lim : Tendsto α atTop (𝓝 (β : ℂ)) := by
      have h := (Complex.continuous_ofReal.tendsto β |>.comp hx_lim).add
        ((Complex.continuous_ofReal.tendsto 0 |>.comp hy_lim).mul
          (tendsto_const_nhds (x := Complex.I)))
      simpa [α] using h
    have hβ_cl : (β : ℂ) ∈ closure slitUnitDisc :=
      mem_closure_of_tendsto hα_lim (Filter.Eventually.of_forall hα_mem)
    have hβ_not : (β : ℂ) ∉ slitUnitDisc := by
      rw [hslit_eq]
      intro hmem
      exact hmem.2 ⟨β, ⟨hβ0.le, hβ1⟩, rfl⟩
    have hβ_front : (β : ℂ) ∈ frontier slitUnitDisc := by
      change (β : ℂ) ∈ closure slitUnitDisc \ interior slitUnitDisc
      rw [hslit_open.interior_eq]
      exact ⟨hβ_cl, hβ_not⟩
    refine ⟨hβ_front, ?_⟩
    intro hsimple
    obtain ⟨γ, hγ_cont, hγ_in, hγ1, t, ht_mono, ht_mem, ht_lim, hγt⟩ :=
      theorem14_16.2 hsimple α hα_mem hα_lim
    have hex_s : ∀ m : ℕ, ∃ s ∈ Icc (t (2 * m)) (t (2 * m + 1)), (γ s).im = 0 := by
      intro m
      have hlt_t : t (2 * m) < t (2 * m + 1) := ht_mono (Nat.lt_succ_self (2 * m))
      have hsub : Icc (t (2 * m)) (t (2 * m + 1)) ⊆ Icc (0 : ℝ) 1 := by
        intro s hs
        exact ⟨le_trans (ht_mem (2 * m)).1.le hs.1,
          le_trans hs.2 (ht_mem (2 * m + 1)).2.le⟩
      have hg_cont : ContinuousOn (fun s => (γ s).im) (Icc (t (2 * m)) (t (2 * m + 1))) :=
        Complex.continuous_im.comp_continuousOn (hγ_cont.mono hsub)
      have him_even : (γ (t (2 * m))).im > 0 := by
        rw [hγt (2 * m)]
        simp only [α, y, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
        have hev : (-1 : ℝ) ^ (2 * m) = 1 := Even.neg_one_pow ⟨m, by ring⟩
        rw [hev]
        positivity
      have him_odd : (γ (t (2 * m + 1))).im < 0 := by
        rw [hγt (2 * m + 1)]
        simp only [α, y, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
        have hodd : (-1 : ℝ) ^ (2 * m + 1) = -1 := Odd.neg_one_pow ⟨m, rfl⟩
        rw [hodd, neg_div]
        exact neg_lt_zero.mpr (by positivity)
      exact intermediate_value_Icc' hlt_t.le hg_cont ⟨him_odd.le, him_even.le⟩
    choose s hs_mem hs_im using hex_s
    have hs_lim : Tendsto s atTop (𝓝 1) := by
      have ht_even : Tendsto (fun m => t (2 * m)) atTop (𝓝 1) :=
        ht_lim.comp (StrictMono.tendsto_atTop fun a b hab => by omega)
      have ht_odd : Tendsto (fun m => t (2 * m + 1)) atTop (𝓝 1) :=
        ht_lim.comp (StrictMono.tendsto_atTop fun a b hab => by omega)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le ht_even ht_odd
        (fun m => (hs_mem m).1) (fun m => (hs_mem m).2)
    have hs_Ico : ∀ m, s m ∈ Ico (0 : ℝ) 1 := fun m =>
      ⟨lt_of_lt_of_le (ht_mem (2 * m)).1 (hs_mem m).1 |>.le,
        lt_of_le_of_lt (hs_mem m).2 (ht_mem (2 * m + 1)).2⟩
    have hre_neg : ∀ m, (γ (s m)).re < 0 := fun m =>
      hslit_re_neg_of_im_zero (hγ_in (s m) (hs_Ico m)) (hs_im m)
    have hs_nhds : Tendsto s atTop (𝓝[Icc (0 : ℝ) 1] 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within s hs_lim
        (Filter.Eventually.of_forall fun m => Ico_subset_Icc_self (hs_Ico m))
    have hγs_lim : Tendsto (fun m => (γ (s m)).re) atTop (𝓝 β) := by
      have h1 : Tendsto (γ ∘ s) atTop (𝓝 (γ 1)) :=
        (hγ_cont 1 (right_mem_Icc.mpr zero_le_one)).tendsto.comp hs_nhds
      rw [hγ1] at h1
      have h2 := (Complex.continuous_re.tendsto (β : ℂ)).comp h1
      rw [Complex.ofReal_re] at h2
      exact h2
    have hβ_le0 : β ≤ 0 :=
      le_of_tendsto hγs_lim (Filter.Eventually.of_forall fun m => (hre_neg m).le)
    linarith
  -- Part (ii) boundary points `i y` (`0 ≤ y ≤ 1`) of `combRegion`
  · intro y ⟨hy0, hy1⟩
    have hcomb_open : IsOpen combRegion := combRegion_bookSimplyConnected.1.1
    let x : ℕ → ℝ := fun m => (1 / ((m : ℝ) + 3) + 1 / ((m : ℝ) + 2)) / 2
    let ym : ℕ → ℝ := fun m => min (max y (1 / ((m : ℝ) + 3))) (1 - 1 / ((m : ℝ) + 3))
    let α : ℕ → ℂ := fun m => (x m : ℂ) + (ym m : ℂ) * Complex.I
    have hα_mem : ∀ m, α m ∈ combRegion := by
      intro m
      rw [combRegion_eq_iUnion]
      refine Set.mem_iUnion.mpr ⟨m + 1, Or.inl ?_⟩
      have hlt_x : 1 / ((m : ℝ) + 3) < 1 / ((m : ℝ) + 2) :=
        one_div_lt_one_div_of_lt (by positivity) (by linarith)
      have hcast1 : ((m + 1 : ℕ) : ℝ) + 1 = (m : ℝ) + 2 := by push_cast; ring
      have hcast2 : ((m + 1 : ℕ) : ℝ) + 2 = (m : ℝ) + 3 := by push_cast; ring
      have hu3 : 3 ≤ (m : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) m]
      have hinv_le : 1 / ((m : ℝ) + 3) ≤ 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num) hu3
      have hym_pos : 0 < ym m := by
        dsimp [ym]
        refine lt_min (lt_of_lt_of_le (by positivity) (le_max_right _ _)) ?_
        linarith
      have hym_lt1 : ym m < 1 := by
        dsimp [ym]
        refine lt_of_le_of_lt (min_le_right _ _) ?_
        have : 0 < 1 / ((m : ℝ) + 3) := by positivity
        linarith
      simp only [combStrip, Set.mem_setOf_eq, hcast1, hcast2, α, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
      dsimp [x]
      exact ⟨by linarith, by linarith, hym_pos, hym_lt1⟩
    have hinv3 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 3)) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hinv2 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 2)) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hx_lim : Tendsto x atTop (𝓝 0) := by
      have h := (hinv3.add hinv2).div_const 2
      simpa [x] using h
    have hym_lim : Tendsto ym atTop (𝓝 y) := by
      have hmax : Tendsto (fun m : ℕ => max y (1 / ((m : ℝ) + 3))) atTop (𝓝 (max y 0)) :=
        tendsto_const_nhds.max hinv3
      have hmin : Tendsto ym atTop (𝓝 (min (max y 0) (1 - 0))) :=
        hmax.min (tendsto_const_nhds.sub hinv3)
      have heval : min (max y 0) (1 - 0) = y := by
        rw [max_eq_left hy0, sub_zero, min_eq_left hy1]
      rwa [heval] at hmin
    have hα_lim : Tendsto α atTop (𝓝 (Complex.I * (y : ℂ))) := by
      have h := (Complex.continuous_ofReal.tendsto 0 |>.comp hx_lim).add
        ((Complex.continuous_ofReal.tendsto y |>.comp hym_lim).mul
          (tendsto_const_nhds (x := Complex.I)))
      have htarget : ((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I = Complex.I * (y : ℂ) := by
        simp [mul_comm]
      rw [htarget] at h
      exact h
    have hβ_cl : Complex.I * (y : ℂ) ∈ closure combRegion :=
      mem_closure_of_tendsto hα_lim (Filter.Eventually.of_forall hα_mem)
    have hβ_not : Complex.I * (y : ℂ) ∉ combRegion := by
      intro hmem
      have : 0 < (Complex.I * (y : ℂ)).re := hmem.1.1
      simp at this
    have hβ_front : Complex.I * (y : ℂ) ∈ frontier combRegion := by
      change Complex.I * (y : ℂ) ∈ closure combRegion \ interior combRegion
      rw [hcomb_open.interior_eq]
      exact ⟨hβ_cl, hβ_not⟩
    refine ⟨hβ_front, ?_⟩
    intro hsimple
    obtain ⟨γ, hγ_cont, hγ_in, hγ1, _, _, _, _, _⟩ :=
      theorem14_16.2 hsimple α hα_mem hα_lim
    let a : ℕ → ℝ := fun k => 1 - 1 / ((k : ℝ) + 2)
    have ha_Ico : ∀ k, a k ∈ Ico (0 : ℝ) 1 := by
      intro k
      dsimp [a]
      have hpos : 0 < 1 / ((k : ℝ) + 2) := by positivity
      have hle : 1 / ((k : ℝ) + 2) ≤ 1 :=
        div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
      exact ⟨by linarith, by linarith⟩
    have hex_uv : ∀ k : ℕ,
        (∃ u ∈ Icc (a k) 1, 1 - 1 / ((k : ℝ) + 2) ≤ (γ u).im) ∧
        (∃ v ∈ Icc (a k) 1, (γ v).im ≤ 1 / ((k : ℝ) + 2)) := by
      intro k
      have hrk_pos : 0 < (γ (a k)).re := (hγ_in (a k) (ha_Ico k)).1.1
      let m : ℕ := max (k + 2) (Nat.floor (1 / (γ (a k)).re) + 1)
      have hm_ge : k + 2 ≤ m := le_max_left _ _
      have hm1 : 1 ≤ m := by omega
      have hm_gt : 1 / (γ (a k)).re < (m : ℝ) := by
        have hlt_fl : 1 / (γ (a k)).re < (Nat.floor (1 / (γ (a k)).re) : ℝ) + 1 :=
          Nat.lt_floor_add_one _
        have hle_m : (Nat.floor (1 / (γ (a k)).re) : ℝ) + 1 ≤ (m : ℝ) := by
          exact_mod_cast le_max_right (k + 2) (Nat.floor (1 / (γ (a k)).re) + 1)
        linarith
      have h1m_lt : 1 / (m : ℝ) < (γ (a k)).re := by
        have h := one_div_lt_one_div_of_lt (div_pos one_pos hrk_pos) hm_gt
        rwa [one_div_one_div] at h
      have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
      have hsub_Icc : Icc (a k) 1 ⊆ Icc (0 : ℝ) 1 := fun s hs =>
        ⟨le_trans (ha_Ico k).1 hs.1, hs.2⟩
      have hre_cont : ContinuousOn (fun s => (γ s).re) (Icc (a k) 1) :=
        Complex.continuous_re.comp_continuousOn (hγ_cont.mono hsub_Icc)
      have hre_1 : (γ 1).re = 0 := by rw [hγ1]; simp
      have hbot_lt : 1 / (2 * (m : ℝ)) < (γ (a k)).re := by
        have : 1 / (2 * (m : ℝ)) < 1 / (m : ℝ) :=
          one_div_lt_one_div_of_lt hm_pos (by linarith)
        linarith
      have htop_lt : 1 / (2 * (m : ℝ) + 1) < (γ (a k)).re := by
        have : 1 / (2 * (m : ℝ) + 1) < 1 / (m : ℝ) :=
          one_div_lt_one_div_of_lt hm_pos (by linarith)
        linarith
      obtain ⟨u, hu_mem, hu_re⟩ := intermediate_value_Icc' (ha_Ico k).2.le hre_cont
        ⟨by rw [hre_1]; positivity, hbot_lt.le⟩
      obtain ⟨v, hv_mem, hv_re⟩ := intermediate_value_Icc' (ha_Ico k).2.le hre_cont
        ⟨by rw [hre_1]; positivity, htop_lt.le⟩
      have hu_ne1 : u ≠ 1 := by
        intro hu1; subst hu1; dsimp at hu_re; rw [hre_1] at hu_re
        have : (0 : ℝ) < 1 / (2 * (m : ℝ)) := by positivity
        linarith
      have hv_ne1 : v ≠ 1 := by
        intro hv1; subst hv1; dsimp at hv_re; rw [hre_1] at hv_re
        have : (0 : ℝ) < 1 / (2 * (m : ℝ) + 1) := by positivity
        linarith
      have hu_comb : γ u ∈ combRegion :=
        hγ_in u ⟨le_trans (ha_Ico k).1 hu_mem.1, lt_of_le_of_ne hu_mem.2 hu_ne1⟩
      have hv_comb : γ v ∈ combRegion :=
        hγ_in v ⟨le_trans (ha_Ico k).1 hv_mem.1, lt_of_le_of_ne hv_mem.2 hv_ne1⟩
      have hu_not_bot : γ u ∉ combBottomSegment m := fun hseg =>
        hu_comb.2 (Set.mem_iUnion₂.mpr ⟨m, hm1, Or.inl hseg⟩)
      rw [mem_combBottomSegment_iff hm1] at hu_not_bot
      have hu_im_gt : ((m : ℝ) - 1) / (m : ℝ) < (γ u).im := by
        by_contra hnot
        exact hu_not_bot ⟨hu_re, hu_comb.1.2.2.1.le, le_of_not_gt hnot⟩
      have hv_not_top : γ v ∉ combTopSegment m := fun hseg =>
        hv_comb.2 (Set.mem_iUnion₂.mpr ⟨m, hm1, Or.inr hseg⟩)
      rw [mem_combTopSegment_iff hm1] at hv_not_top
      have hv_im_lt : (γ v).im < 1 / (m : ℝ) := by
        by_contra hnot
        exact hv_not_top ⟨hv_re, le_of_not_gt hnot, hv_comb.1.2.2.2.le⟩
      have hinv_le_m : 1 / (m : ℝ) ≤ 1 / ((k : ℝ) + 2) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : ((k + 2 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge
        push_cast at this; linarith
      have hm_eq : ((m : ℝ) - 1) / (m : ℝ) = 1 - 1 / (m : ℝ) := by
        field_simp [hm_pos.ne']
      refine ⟨⟨u, hu_mem, by linarith⟩, ⟨v, hv_mem, by linarith⟩⟩
    choose u hu_mem hu_im using fun k => (hex_uv k).1
    choose v hv_mem hv_im using fun k => (hex_uv k).2
    have ha_lim : Tendsto a atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hinv2
      simpa [a] using h
    have hu_lim : Tendsto u atTop (𝓝 1) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le ha_lim tendsto_const_nhds
        (fun k => (hu_mem k).1) (fun k => (hu_mem k).2)
    have hv_lim : Tendsto v atTop (𝓝 1) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le ha_lim tendsto_const_nhds
        (fun k => (hv_mem k).1) (fun k => (hv_mem k).2)
    have hu_Icc : ∀ k, u k ∈ Icc (0 : ℝ) 1 := fun k =>
      ⟨le_trans (ha_Ico k).1 (hu_mem k).1, (hu_mem k).2⟩
    have hv_Icc : ∀ k, v k ∈ Icc (0 : ℝ) 1 := fun k =>
      ⟨le_trans (ha_Ico k).1 (hv_mem k).1, (hv_mem k).2⟩
    have him1 : (γ 1).im = y := by rw [hγ1]; simp
    have hγu_lim : Tendsto (fun k => (γ (u k)).im) atTop (𝓝 y) := by
      have hnhds : Tendsto u atTop (𝓝[Icc (0 : ℝ) 1] 1) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hu_lim
          (Filter.Eventually.of_forall hu_Icc)
      have h1 := (Complex.continuous_im.tendsto (γ 1)).comp
        ((hγ_cont 1 (right_mem_Icc.mpr zero_le_one)).tendsto.comp hnhds)
      rwa [him1] at h1
    have hγv_lim : Tendsto (fun k => (γ (v k)).im) atTop (𝓝 y) := by
      have hnhds : Tendsto v atTop (𝓝[Icc (0 : ℝ) 1] 1) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within v hv_lim
          (Filter.Eventually.of_forall hv_Icc)
      have h1 := (Complex.continuous_im.tendsto (γ 1)).comp
        ((hγ_cont 1 (right_mem_Icc.mpr zero_le_one)).tendsto.comp hnhds)
      rwa [him1] at h1
    have h1_le_y : 1 ≤ y :=
      le_of_tendsto_of_tendsto ha_lim hγu_lim (Filter.Eventually.of_forall hu_im)
    have hy_le_0 : y ≤ 0 :=
      le_of_tendsto_of_tendsto hγv_lim hinv2 (Filter.Eventually.of_forall hv_im)
    linarith

/-! ### Node 14.18: Boundary Extension and Distinctness at Simple Boundary Points -/

theorem eq_of_isPreconnected_forall_int {S : Set ℝ} (hS : IsPreconnected S) {g : ℝ → ℝ}
    (hg : ContinuousOn g S) (hint : ∀ x ∈ S, ∃ k : ℤ, g x = k)
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : g x = g y := by
  by_contra hne
  obtain ⟨kx, hkx⟩ := hint x hx
  obtain ⟨ky, hky⟩ := hint y hy
  have hkne : kx ≠ ky := fun h => hne (by rw [hkx, hky, h])
  have himg_pre : IsPreconnected (g '' S) := hS.image g hg
  by_cases hlt : kx < ky
  · have hmid_in : ((kx : ℝ) + 1 / 2) ∈ Icc (g x) (g y) := by
      rw [hkx, hky]
      have h1 : (kx : ℝ) + 1 ≤ (ky : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hlt
      exact ⟨by linarith, by linarith⟩
    have hsub := himg_pre.ordConnected.out (⟨x, hx, rfl⟩ : g x ∈ g '' S) (⟨y, hy, rfl⟩ : g y ∈ g '' S)
    rcases hsub hmid_in with ⟨z, hz, hgz⟩
    obtain ⟨kz, hkz⟩ := hint z hz
    have h2 : (2 : ℝ) * (kz : ℝ) = 2 * (kx : ℝ) + 1 := by linarith
    have h2z : (2 * kz : ℤ) = 2 * kx + 1 := by exact_mod_cast h2
    omega
  · have hgt : ky < kx := lt_of_le_of_ne (not_lt.mp hlt) hkne.symm
    have hmid_in : ((ky : ℝ) + 1 / 2) ∈ Icc (g y) (g x) := by
      rw [hkx, hky]
      have h1 : (ky : ℝ) + 1 ≤ (kx : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hgt
      exact ⟨by linarith, by linarith⟩
    have hsub := himg_pre.ordConnected.out (⟨y, hy, rfl⟩ : g y ∈ g '' S) (⟨x, hx, rfl⟩ : g x ∈ g '' S)
    rcases hsub hmid_in with ⟨z, hz, hgz⟩
    obtain ⟨kz, hkz⟩ := hint z hz
    have h2 : (2 : ℝ) * (kz : ℝ) = 2 * (ky : ℝ) + 1 := by linarith
    have h2z : (2 * kz : ℤ) = 2 * ky + 1 := by exact_mod_cast h2
    omega

/-- If `f : ℝ → ℂ` is continuous and nonzero on `Icc a b` (`a ≤ b`), there exists a continuous
real-valued angle lift `ϑ : ℝ → ℝ` on `Icc a b` such that `f t = ‖f t‖ * exp (ϑ t * I)` on `Icc a b`. -/
theorem exists_continuousOn_angle_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ}
    (hf_cont : ContinuousOn f (Icc a b)) (hf_ne : ∀ t ∈ Icc a b, f t ≠ 0) :
    ∃ ϑ : ℝ → ℝ, ContinuousOn ϑ (Icc a b) ∧
      ∀ t ∈ Icc a b, f t = (‖f t‖ : ℂ) * Complex.exp ((ϑ t : ℂ) * Complex.I) := by
  let u : ℝ → ℂ := fun t => f t / (‖f t‖ : ℂ)
  have hu_cont : ContinuousOn u (Icc a b) := by
    refine hf_cont.div (Complex.continuous_ofReal.comp_continuousOn (continuous_norm.comp_continuousOn hf_cont)) ?_
    intro t ht
    exact Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr (hf_ne t ht)).ne'
  have hu_norm : ∀ t ∈ Icc a b, ‖u t‖ = 1 := by
    intro t ht
    dsimp [u]
    have hp : 0 < ‖f t‖ := norm_pos_iff.mpr (hf_ne t ht)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp, div_self hp.ne']
  have huc : UniformContinuousOn u (Icc a b) := isCompact_Icc.uniformContinuousOn_of_continuous hu_cont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ_pos, hδ⟩ := huc 1 zero_lt_one
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  have hN_pos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | hp
    · have hge : 0 ≤ (b - a) / δ := div_nonneg (sub_nonneg.mpr hab) hδ_pos.le
      simp at hN
      linarith
    · exact hp
  have hstep : ∀ k : ℕ, k ≤ N →
      ∃ ϑ : ℝ → ℝ, ContinuousOn ϑ (Icc a (a + (k : ℝ) * ((b - a) / (N : ℝ)))) ∧
        ∀ t ∈ Icc a (a + (k : ℝ) * ((b - a) / (N : ℝ))),
          u t = Complex.exp ((ϑ t : ℂ) * Complex.I) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [Nat.cast_zero, zero_mul, add_zero, Icc_self]
      refine ⟨fun _ => Complex.arg (u a), continuousOn_const, ?_⟩
      intro t ht
      rw [mem_singleton_iff] at ht
      rw [ht]
      have hpolar := Complex.norm_mul_exp_arg_mul_I (u a)
      rw [hu_norm a (left_mem_Icc.mpr hab), Complex.ofReal_one, one_mul] at hpolar
      exact hpolar.symm
    | succ k ih =>
      intro hk1
      obtain ⟨ϑ₀, hϑ₀_cont, hϑ₀_eq⟩ := ih (Nat.le_of_succ_le hk1)
      set x_k : ℝ := a + (k : ℝ) * ((b - a) / (N : ℝ))
      set x_k1 : ℝ := a + ((k + 1 : ℕ) : ℝ) * ((b - a) / (N : ℝ))
      have hstep_nonneg : 0 ≤ (b - a) / (N : ℝ) :=
        div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg (α := ℝ) N)
      have ha_le_xk : a ≤ x_k := by
        dsimp [x_k]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
      have hxk_le_xk1 : x_k ≤ x_k1 := by
        dsimp [x_k, x_k1]; push_cast; linarith
      have hxk1_le_b : x_k1 ≤ b := by
        dsimp [x_k1]
        have hkN : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk1
        have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN_pos.ne'
        calc
          a + ((k + 1 : ℕ) : ℝ) * ((b - a) / (N : ℝ))
              ≤ a + (N : ℝ) * ((b - a) / (N : ℝ)) := by nlinarith
          _ = b := by field_simp [hN_ne]; ring
      have hlen_lt : x_k1 - x_k < δ := by
        have h1 : x_k1 - x_k = (b - a) / (N : ℝ) := by dsimp [x_k, x_k1]; push_cast; ring
        rw [h1]
        by_cases hab_eq : a = b
        · rw [hab_eq, sub_self, zero_div]; exact hδ_pos
        · rw [div_lt_iff₀ (Nat.cast_pos.mpr hN_pos)]
          have := (div_lt_iff₀ hδ_pos).mp hN
          linarith
      have hxk_in : x_k ∈ Icc a b := ⟨ha_le_xk, hxk_le_xk1.trans hxk1_le_b⟩
      let ψ : ℝ → ℝ := fun t => ϑ₀ x_k + Complex.arg (u t / u x_k)
      have hre_pos : ∀ t ∈ Icc x_k x_k1, 0 < (u t / u x_k).re := by
        intro t ht
        have ht_in : t ∈ Icc a b := ⟨ha_le_xk.trans ht.1, ht.2.trans hxk1_le_b⟩
        have hdist : dist t x_k < δ := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
          exact (sub_le_sub_right ht.2 x_k).trans_lt hlen_lt
        have hudist : ‖u t - u x_k‖ < 1 := by
          simpa [dist_eq_norm] using hδ t ht_in x_k hxk_in hdist
        have hnorm_xk : ‖u x_k‖ = 1 := hu_norm x_k hxk_in
        have huxk_ne : u x_k ≠ 0 := by intro h0; rw [h0, norm_zero] at hnorm_xk; norm_num at hnorm_xk
        have hq : ‖u t / u x_k - 1‖ < 1 := by
          have hsub : u t / u x_k - 1 = (u t - u x_k) / u x_k := by field_simp [huxk_ne]
          rw [hsub, norm_div, hnorm_xk, div_one]
          exact hudist
        have hre1 : |(u t / u x_k - 1).re| ≤ ‖u t / u x_k - 1‖ :=
          Complex.abs_re_le_norm (u t / u x_k - 1)
        rw [Complex.sub_re, Complex.one_re] at hre1
        linarith [abs_lt.mp (lt_of_le_of_lt hre1 hq)]
      have hψ_cont : ContinuousOn ψ (Icc x_k x_k1) := by
        refine continuousOn_const.add ?_
        intro t ht
        have hc_div : ContinuousWithinAt (fun s => u s / u x_k) (Icc x_k x_k1) t :=
          (hu_cont.mono (Icc_subset_Icc ha_le_xk hxk1_le_b) t ht).div_const (u x_k)
        exact ContinuousAt.comp_continuousWithinAt (f := fun s => u s / u x_k)
          (Complex.continuousAt_arg (Or.inl (hre_pos t ht))) hc_div
      have hψ_xk : ψ x_k = ϑ₀ x_k := by
        dsimp [ψ]
        have hnorm_xk : ‖u x_k‖ = 1 := hu_norm x_k hxk_in
        have huxk_ne : u x_k ≠ 0 := by intro h0; rw [h0, norm_zero] at hnorm_xk; norm_num at hnorm_xk
        rw [div_self huxk_ne, Complex.arg_one, add_zero]
      have hψ_eq : ∀ t ∈ Icc x_k x_k1, u t = Complex.exp ((ψ t : ℂ) * Complex.I) := by
        intro t ht
        have ht_in : t ∈ Icc a b := ⟨ha_le_xk.trans ht.1, ht.2.trans hxk1_le_b⟩
        have hnorm_xk : ‖u x_k‖ = 1 := hu_norm x_k hxk_in
        have huxk_ne : u x_k ≠ 0 := by intro h0; rw [h0, norm_zero] at hnorm_xk; norm_num at hnorm_xk
        have hnorm_q : ‖u t / u x_k‖ = 1 := by
          rw [norm_div, hu_norm t ht_in, hnorm_xk, div_one]
        have hpolar := Complex.norm_mul_exp_arg_mul_I (u t / u x_k)
        rw [hnorm_q, Complex.ofReal_one, one_mul] at hpolar
        have hxk_eq : u x_k = Complex.exp ((ϑ₀ x_k : ℂ) * Complex.I) :=
          hϑ₀_eq x_k ⟨ha_le_xk, le_rfl⟩
        dsimp [ψ]
        rw [Complex.ofReal_add, add_mul, Complex.exp_add, ← hxk_eq, hpolar,
          mul_comm (u x_k), div_mul_cancel₀ (u t) huxk_ne]
      let ϑ₁ : ℝ → ℝ := fun t => if t ≤ x_k then ϑ₀ t else ψ t
      refine ⟨ϑ₁, ?_, ?_⟩
      · have hcov : Icc a x_k1 = Icc a x_k ∪ Icc x_k x_k1 :=
          (Icc_union_Icc_eq_Icc ha_le_xk hxk_le_xk1).symm
        rw [hcov]
        refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
        · refine hϑ₀_cont.congr fun t ht => ?_
          simp [ϑ₁, ht.2]
        · refine hψ_cont.congr fun t ht => ?_
          dsimp [ϑ₁]
          split_ifs with hle
          · have heq : t = x_k := le_antisymm hle ht.1
            subst heq
            exact hψ_xk.symm
          · rfl
      · intro t ht
        dsimp [ϑ₁]
        split_ifs with hle
        · exact hϑ₀_eq t ⟨ht.1, hle⟩
        · exact hψ_eq t ⟨le_of_not_ge hle, ht.2⟩
  obtain ⟨ϑ, hϑ_cont, hϑ_eq⟩ := hstep N le_rfl
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN_pos.ne'
  have hend : a + (N : ℝ) * ((b - a) / (N : ℝ)) = b := by field_simp [hN_ne]; ring
  rw [hend] at hϑ_cont hϑ_eq
  refine ⟨ϑ, hϑ_cont, ?_⟩
  intro t ht
  have hp : (‖f t‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr (hf_ne t ht)).ne'
  have hu_t := hϑ_eq t ht
  dsimp [u] at hu_t
  rw [← hu_t]
  exact (mul_div_cancel₀ (f t) hp).symm

/-- Continuous angle lift on `Ico T₀ 1` for a nonzero continuous curve `Γ : ℝ → ℂ`. -/
theorem exists_continuousOn_angle_Ico {T₀ : ℝ} (hT₀ : T₀ < 1) {Γ : ℝ → ℂ}
    (hΓ_cont : ContinuousOn Γ (Ico T₀ 1)) (hΓ_ne : ∀ t ∈ Ico T₀ 1, Γ t ≠ 0) :
    ∃ ϑ : ℝ → ℝ, ContinuousOn ϑ (Ico T₀ 1) ∧
      ∀ t ∈ Ico T₀ 1, Γ t = (‖Γ t‖ : ℂ) * Complex.exp ((ϑ t : ℂ) * Complex.I) := by
  let b_seq : ℕ → ℝ := fun n => 1 - (1 - T₀) / ((n : ℝ) + 2)
  have hb_lt1 : ∀ n, b_seq n < 1 := by
    intro n; dsimp [b_seq]
    have : 0 < (1 - T₀) / ((n : ℝ) + 2) := div_pos (sub_pos.mpr hT₀) (by positivity)
    linarith
  have hb_ge : ∀ n, T₀ ≤ b_seq n := by
    intro n; dsimp [b_seq]
    have h1 : (1 - T₀) / ((n : ℝ) + 2) ≤ 1 - T₀ :=
      div_le_self (sub_nonneg.mpr hT₀.le) (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  have hb_mono : Monotone b_seq := by
    intro m n hmn; dsimp [b_seq]
    have hmn_r : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by
      have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
      linarith
    have hsub : (1 - T₀) / ((n : ℝ) + 2) ≤ (1 - T₀) / ((m : ℝ) + 2) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hT₀.le) (by positivity) hmn_r
    linarith
  have hex_n : ∀ n : ℕ, ∃ ϑ : ℝ → ℝ, ContinuousOn ϑ (Icc T₀ (b_seq n)) ∧
      ϑ T₀ = Complex.arg (Γ T₀) ∧
      ∀ t ∈ Icc T₀ (b_seq n), Γ t = (‖Γ t‖ : ℂ) * Complex.exp ((ϑ t : ℂ) * Complex.I) := by
    intro n
    have hsub : Icc T₀ (b_seq n) ⊆ Ico T₀ 1 := fun t ht => ⟨ht.1, ht.2.trans_lt (hb_lt1 n)⟩
    obtain ⟨ϑ₀, hϑ₀_c, hϑ₀_eq⟩ := exists_continuousOn_angle_Icc (hb_ge n)
      (hΓ_cont.mono hsub) (fun t ht => hΓ_ne t (hsub ht))
    have hT₀_mem : T₀ ∈ Icc T₀ (b_seq n) := ⟨le_rfl, hb_ge n⟩
    have h1 := hϑ₀_eq T₀ hT₀_mem
    have hpolar := (Complex.norm_mul_exp_arg_mul_I (Γ T₀)).symm
    have hnorm_ne : (‖Γ T₀‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr (hΓ_ne T₀ ⟨le_rfl, hT₀⟩)).ne'
    have hexp_eq : Complex.exp ((ϑ₀ T₀ : ℂ) * Complex.I) =
        Complex.exp ((Complex.arg (Γ T₀) : ℂ) * Complex.I) :=
      mul_left_cancel₀ hnorm_ne (h1.symm.trans hpolar)
    rw [Complex.exp_eq_exp_iff_exists_int] at hexp_eq
    obtain ⟨k, hk⟩ := hexp_eq
    have hshift : ϑ₀ T₀ - Complex.arg (Γ T₀) = (k : ℝ) * (2 * Real.pi) := by
      have hc : ((ϑ₀ T₀ - Complex.arg (Γ T₀) : ℝ) : ℂ) * Complex.I =
          (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
        push_cast; linear_combination hk
      exact Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero hc)
    refine ⟨fun t => ϑ₀ t - (k : ℝ) * (2 * Real.pi), hϑ₀_c.sub continuousOn_const, by linarith, ?_⟩
    intro t ht
    have hexp_k : Complex.exp ((((ϑ₀ t - (k : ℝ) * (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((ϑ₀ t : ℂ) * Complex.I) := by
      have harg : (((ϑ₀ t - (k : ℝ) * (2 * Real.pi)) : ℝ) : ℂ) * Complex.I =
          (ϑ₀ t : ℂ) * Complex.I - (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast; ring
      rw [harg, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I k, div_one]
    rw [hexp_k, ← hϑ₀_eq t ht]
  choose ϑ_seq hϑ_cont hϑ_T₀ hϑ_eq using hex_n
  have hagree : ∀ (m n : ℕ) {t : ℝ}, t ∈ Icc T₀ (b_seq m) → t ∈ Icc T₀ (b_seq n) →
      ϑ_seq m t = ϑ_seq n t := by
    intro m n t htm htn
    wlog hmn : m ≤ n generalizing m n
    · exact (this n m htn htm (Nat.le_of_not_le hmn)).symm
    let diff : ℝ → ℝ := fun s => (ϑ_seq m s - ϑ_seq n s) / (2 * Real.pi)
    have hdiff_cont : ContinuousOn diff (Icc T₀ (b_seq m)) :=
      (hϑ_cont m |>.sub ((hϑ_cont n).mono (Icc_subset_Icc_right (hb_mono hmn)))).div_const _
    have hdiff_int : ∀ s ∈ Icc T₀ (b_seq m), ∃ k : ℤ, diff s = k := by
      intro s hs
      have hsn : s ∈ Icc T₀ (b_seq n) := ⟨hs.1, hs.2.trans (hb_mono hmn)⟩
      have hs_ico : s ∈ Ico T₀ 1 := ⟨hs.1, hs.2.trans_lt (hb_lt1 m)⟩
      have hnorm_ne : (‖Γ s‖ : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr (hΓ_ne s hs_ico)).ne'
      have hexp : Complex.exp ((ϑ_seq m s : ℂ) * Complex.I) =
          Complex.exp ((ϑ_seq n s : ℂ) * Complex.I) :=
        mul_left_cancel₀ hnorm_ne ((hϑ_eq m s hs).symm.trans (hϑ_eq n s hsn))
      rw [Complex.exp_eq_exp_iff_exists_int] at hexp
      obtain ⟨k, hk⟩ := hexp
      refine ⟨k, ?_⟩
      have hc : ((ϑ_seq m s - ϑ_seq n s : ℝ) : ℂ) * Complex.I =
          (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
        push_cast; linear_combination hk
      have hr : ϑ_seq m s - ϑ_seq n s = (k : ℝ) * (2 * Real.pi) :=
        Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero hc)
      dsimp [diff]
      rw [hr, mul_div_cancel_right₀ _ (by positivity)]
    have heq_diff := eq_of_isPreconnected_forall_int (convex_Icc T₀ (b_seq m)).isPreconnected
      hdiff_cont hdiff_int htm ⟨le_rfl, hb_ge m⟩
    have hdiff_T₀ : diff T₀ = 0 := by
      dsimp [diff]; rw [hϑ_T₀ m, hϑ_T₀ n, sub_self, zero_div]
    rw [hdiff_T₀] at heq_diff
    dsimp [diff] at heq_diff
    have hsub0 : ϑ_seq m t - ϑ_seq n t = 0 :=
      (div_eq_zero_iff.mp heq_diff).resolve_right (by positivity)
    linarith
  have hex_idx : ∀ t : ℝ, t < 1 → ∃ n : ℕ, t < b_seq n := by
    intro t ht
    obtain ⟨n, hn⟩ := exists_nat_gt ((1 - T₀) / (1 - t))
    refine ⟨n, ?_⟩
    dsimp [b_seq]
    have hpos : 0 < 1 - t := sub_pos.mpr ht
    have hlt : (1 - T₀) / (1 - t) < (n : ℝ) + 2 := by linarith
    have h1 : (1 - T₀) / ((n : ℝ) + 2) < 1 - t :=
      (div_lt_iff₀ (by positivity)).mpr ((div_lt_iff₀ hpos).mp hlt |>.trans_eq (mul_comm _ _))
    linarith
  let idx : ℝ → ℕ := fun t => if h : t < 1 then Nat.find (hex_idx t h) else 0
  let ϑ : ℝ → ℝ := fun t => ϑ_seq (idx t) t
  refine ⟨ϑ, ?_, ?_⟩
  · intro t ht
    obtain ⟨n, htn⟩ := hex_idx t ht.2
    have hsub_nhd : Ioo (T₀ - 1) (b_seq n) ∈ 𝓝[Ico T₀ 1] t :=
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith [ht.1]) htn)
    have hev : EqOn ϑ (ϑ_seq n) (Ico T₀ 1 ∩ Ioo (T₀ - 1) (b_seq n)) := by
      intro s ⟨hs_ico, hs_ioo⟩
      dsimp [ϑ]
      have hs_lt : s < b_seq (idx s) := by
        simp only [idx, hs_ico.2, ↓reduceDIte]
        exact Nat.find_spec (hex_idx s hs_ico.2)
      exact hagree (idx s) n ⟨hs_ico.1, hs_lt.le⟩ ⟨hs_ico.1, hs_ioo.2.le⟩
    have hc_n : ContinuousWithinAt (ϑ_seq n) (Ico T₀ 1) t := by
      have hc1 := (hϑ_cont n t ⟨ht.1, htn.le⟩).mono
        (show Ico T₀ 1 ∩ Ioo (T₀ - 1) (b_seq n) ⊆ Icc T₀ (b_seq n) from
          fun s hs => ⟨hs.1.1, hs.2.2.le⟩)
      exact continuousWithinAt_inter' hsub_nhd |>.mp hc1
    exact hc_n.congr_of_eventuallyEq
      (eventually_nhdsWithin_iff.mpr
        (eventually_of_mem (Ioo_mem_nhds (by linarith [ht.1]) htn) fun s hs hs_ico =>
          hev ⟨hs_ico, hs⟩))
      (hev ⟨ht, by linarith [ht.1], htn⟩)
  · intro t ht
    have hidx : idx t = Nat.find (hex_idx t ht.2) := by simp only [idx, ht.2, ↓reduceDIte]
    dsimp [ϑ]
    rw [hidx]
    exact hϑ_eq _ t ⟨ht.1, (Nat.find_spec (hex_idx t ht.2)).le⟩

/-! ### Polar area bound and a.e. radial limits of bounded univalent maps on `U` -/

theorem lintegral_polar_deriv_sq_le_of_injOn {D : Set ℂ} (hD_open : IsOpen D)
    {g : ℂ → ℂ} (hg_holo : RudinRCA.Chapter10.HolomorphicOn g D) (hg_inj : InjOn g D)
    {M : ℝ} (hM : 0 < M) (hg_bdd : ∀ w ∈ D, ‖g w‖ ≤ M) :
    (∫⁻ p in _root_.polarCoord.target,
      (D \ {0}).indicator (fun z => ENNReal.ofReal (‖deriv g z‖ ^ 2)) (Complex.polarCoord.symm p) *
        ENNReal.ofReal p.1 ∂MeasureTheory.volume) ≤
      ENNReal.ofReal (Real.pi * M ^ 2) := by
  let D₀ : Set ℂ := D \ {0}
  have hD₀_open : IsOpen D₀ := hD_open.sdiff isClosed_singleton
  have hD₀_sub : D₀ ⊆ D := Set.sdiff_subset
  let f' : ℂ → (ℂ →L[ℝ] ℂ) := fun z =>
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv g z)).restrictScalars ℝ)
  have hf'_within : ∀ z ∈ D₀, HasFDerivWithinAt g (f' z) D₀ z := by
    intro z hz
    exact ((hg_holo z (hD₀_sub hz)).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hvol_D₀ : MeasureTheory.volume (g '' D₀) =
      ∫⁻ z in D₀, ENNReal.ofReal (‖deriv g z‖ ^ 2) ∂MeasureTheory.volume := by
    rw [← MeasureTheory.setLIntegral_one (g '' D₀),
      MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul MeasureTheory.volume
        hD₀_open.measurableSet hf'_within (hg_inj.mono hD₀_sub)]
    refine MeasureTheory.setLIntegral_congr_fun hD₀_open.measurableSet ?_
    intro z _
    dsimp [f']
    rw [det_real_smulRight_complex, abs_of_nonneg (sq_nonneg _), mul_one]
  have himg_sub : g '' D₀ ⊆ closedBall (0 : ℂ) M := by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_closedBall_zero_iff.mpr (hg_bdd z (hD₀_sub hz))
  have hvol_closed : MeasureTheory.volume (closedBall (0 : ℂ) M) = ENNReal.ofReal (Real.pi * M ^ 2) := by
    rw [Complex.volume_closedBall, ENNReal.ofReal_mul Real.pi_pos.le,
      ENNReal.ofReal_pow hM.le, ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal, mul_comm]
  have hbound : (∫⁻ z in D₀, ENNReal.ofReal (‖deriv g z‖ ^ 2) ∂MeasureTheory.volume) ≤
      ENNReal.ofReal (Real.pi * M ^ 2) := by
    rw [← hvol_D₀, ← hvol_closed]
    exact MeasureTheory.measure_mono himg_sub
  let g_int : ℂ → ENNReal := D₀.indicator (fun z => ENNReal.ofReal (‖deriv g z‖ ^ 2))
  have hpolar : (∫⁻ z in D₀, ENNReal.ofReal (‖deriv g z‖ ^ 2) ∂MeasureTheory.volume) =
      ∫⁻ p in _root_.polarCoord.target,
        ENNReal.ofReal p.1 • g_int (Complex.polarCoord.symm p) ∂MeasureTheory.volume := by
    rw [← MeasureTheory.lintegral_indicator hD₀_open.measurableSet,
      ← Complex.lintegral_comp_polarCoord_symm g_int]
  rw [hpolar] at hbound
  refine le_trans ?_ hbound
  refine MeasureTheory.setLIntegral_mono' (by rw [polarCoord_target]; exact measurableSet_Ioi.prod measurableSet_Ioo) ?_
  intro p _
  dsimp [g_int, D₀]
  exact le_of_eq (mul_comm _ _)

theorem ae_radial_limit_of_injOn_ball {g : ℂ → ℂ}
    (hg_holo : RudinRCA.Chapter10.HolomorphicOn g (ball (0 : ℂ) 1))
    (hg_inj : InjOn g (ball (0 : ℂ) 1)) {M : ℝ} (hM : 0 < M)
    (hg_bdd : ∀ w ∈ ball (0 : ℂ) 1, ‖g w‖ ≤ M) :
    ∀ᵐ θ ∂MeasureTheory.volume,
      ∃ L : ℂ, Tendsto (fun ρ : ℝ => g (circleMap 0 ρ θ)) (𝓝[<] 1) (𝓝 L) := by
  -- First prove for a.e. `θ ∈ Ioo (-π) π` for ANY rotated version `w ↦ g (exp (α * I) * w)`
  have hae_core : ∀ α : ℝ, ∀ᵐ θ ∂MeasureTheory.volume, θ ∈ Ioo (-Real.pi) Real.pi →
      ∃ L : ℂ, Tendsto (fun ρ : ℝ => g (circleMap 0 ρ (θ + α))) (𝓝[<] 1) (𝓝 L) := by
    intro α
    let uα : ℂ := Complex.exp ((α : ℂ) * Complex.I)
    have huα_norm : ‖uα‖ = 1 := Complex.norm_exp_ofReal_mul_I α
    have huα_ne : uα ≠ 0 := Complex.exp_ne_zero _
    let gα : ℂ → ℂ := fun w => g (uα * w)
    have hmaps : MapsTo (fun w : ℂ => uα * w) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
      intro w hw
      rw [mem_ball_zero_iff] at hw ⊢
      rw [norm_mul, huα_norm, one_mul]; exact hw
    have hgα_holo : RudinRCA.Chapter10.HolomorphicOn gα (ball (0 : ℂ) 1) :=
      fun w hw => (hg_holo _ (hmaps hw)).comp w (differentiableAt_id.const_mul uα)
    have hgα_inj : InjOn gα (ball (0 : ℂ) 1) := by
      intro w₁ hw₁ w₂ hw₂ heq
      exact mul_left_cancel₀ huα_ne (hg_inj (hmaps hw₁) (hmaps hw₂) heq)
    have hgα_bdd : ∀ w ∈ ball (0 : ℂ) 1, ‖gα w‖ ≤ M := fun w hw => hg_bdd _ (hmaps hw)
    have harea := lintegral_polar_deriv_sq_le_of_injOn isOpen_ball hgα_holo hgα_inj hM hgα_bdd
    have hpolar_eq_circle : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
      intro p
      rw [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I,
        Complex.ofReal_cos, Complex.ofReal_sin]
    let S : Set (ℝ × ℝ) := Ioo (1 / 2 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi
    have hS_sub : S ⊆ _root_.polarCoord.target := by
      rw [polarCoord_target]
      exact prod_mono (fun ρ hρ => lt_trans (by norm_num) hρ.1) Subset.rfl
    have hS_meas : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
    let h_prod : ℝ × ℝ → ENNReal := fun p =>
      ENNReal.ofReal (p.1 * ‖deriv gα (circleMap 0 p.1 p.2)‖ ^ 2)
    have hdgα_holo := RudinRCA.Chapter10.holomorphicOn_deriv isOpen_ball hgα_holo
    have hh_cont : ContinuousOn h_prod S := by
      have hcm_maps : MapsTo (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) S (ball (0 : ℂ) 1) := by
        rintro ⟨ρ, θ⟩ ⟨hρ, _⟩
        rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos (by linarith [hρ.1])]
        exact hρ.2
      have hcm_cont : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
        simp only [circleMap_zero]
        exact (Complex.continuous_ofReal.comp continuous_fst).mul
          (Complex.continuous_exp.comp
            ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
      have hd_cont : ContinuousOn (fun p : ℝ × ℝ => deriv gα (circleMap 0 p.1 p.2)) S :=
        (RudinRCA.Chapter10.continuousOn_of_holomorphicOn hdgα_holo).comp
          hcm_cont.continuousOn hcm_maps
      exact ENNReal.continuous_ofReal.comp_continuousOn
        (continuousOn_fst.mul ((continuous_norm.comp_continuousOn hd_cont).pow 2))
    have hprod_le : (∫⁻ p in S, h_prod p ∂MeasureTheory.volume) ≤ ENNReal.ofReal (Real.pi * M ^ 2) := by
      refine le_trans ?_ harea
      refine le_trans ?_ (MeasureTheory.lintegral_mono' (MeasureTheory.Measure.restrict_mono hS_sub le_rfl) le_rfl)
      refine MeasureTheory.setLIntegral_mono' hS_meas ?_
      rintro ⟨ρ, θ⟩ ⟨hρ, _⟩
      have hρ_pos : 0 < ρ := by linarith [hρ.1]
      have hz_in : Complex.polarCoord.symm (ρ, θ) ∈ ball (0 : ℂ) 1 \ {0} := by
        rw [hpolar_eq_circle]
        have hn : ‖circleMap 0 ρ θ‖ = ρ := by rw [norm_circleMap_zero, abs_of_pos hρ_pos]
        refine ⟨mem_ball_zero_iff.mpr (by rw [hn]; exact hρ.2), ?_⟩
        intro h0; rw [mem_singleton_iff] at h0; rw [h0, norm_zero] at hn; linarith
      dsimp [h_prod]
      rw [Set.indicator_of_mem hz_in, hpolar_eq_circle, ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
    -- Apply Tonelli (`setLIntegral_prod_symm`) on `S = Ioo (1/2) 1 ×ˢ Ioo (-π) π`
    have htonelli : (∫⁻ p in S, h_prod p ∂MeasureTheory.volume) =
        ∫⁻ θ in Ioo (-Real.pi) Real.pi,
          (∫⁻ ρ in Ioo (1 / 2 : ℝ) 1, h_prod (ρ, θ) ∂MeasureTheory.volume) ∂MeasureTheory.volume := by
      dsimp [S]
      rw [MeasureTheory.Measure.volume_eq_prod]
      exact MeasureTheory.setLIntegral_prod_symm h_prod
        (hh_cont.aestronglyMeasurable hS_meas).aemeasurable
    have hlt_top : (∫⁻ θ in Ioo (-Real.pi) Real.pi,
        (∫⁻ ρ in Ioo (1 / 2 : ℝ) 1, h_prod (ρ, θ) ∂MeasureTheory.volume) ∂MeasureTheory.volume) < ⊤ := by
      rw [← htonelli]
      exact lt_of_le_of_lt hprod_le ENNReal.ofReal_lt_top
    have hae_fin : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Ioo (-Real.pi) Real.pi)),
        (∫⁻ ρ in Ioo (1 / 2 : ℝ) 1, h_prod (ρ, θ) ∂MeasureTheory.volume) < ⊤ := by
      have hm_prod : AEMeasurable h_prod
          ((MeasureTheory.volume.restrict (Ioo (1 / 2 : ℝ) 1)).prod
            (MeasureTheory.volume.restrict (Ioo (-Real.pi) Real.pi))) := by
        rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
        exact (hh_cont.aestronglyMeasurable hS_meas).aemeasurable
      exact MeasureTheory.ae_lt_top' hm_prod.lintegral_prod_left' hlt_top.ne
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo] at hae_fin
    filter_upwards [hae_fin] with θ hθ_imp hθ_in
    have hfin := hθ_imp hθ_in
    -- Bound `∫⁻ ρ in Ioo (1/2) 1, ofReal ‖deriv gα (circleMap 0 ρ θ)‖ < ⊤` via `x ≤ 1/2 + ρ x^2`
    let v_fn : ℝ → ℂ := fun ρ => deriv gα (circleMap 0 ρ θ) * Complex.exp ((θ : ℂ) * Complex.I)
    have hv_cont : ContinuousOn v_fn (Ioo (1 / 2 : ℝ) 1) := by
      refine ContinuousOn.mul ?_ continuousOn_const
      intro ρ hρ
      have hρ_pos : 0 < ρ := by linarith [hρ.1]
      have hcm_in : circleMap 0 ρ θ ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hρ_pos]; exact hρ.2
      have hc_cm : ContinuousAt (fun r : ℝ => circleMap 0 r θ) ρ := by
        simp only [circleMap_zero]
        exact (Complex.continuous_ofReal.mul continuous_const).continuousAt
      exact (ContinuousAt.comp (g := deriv gα) (f := fun r : ℝ => circleMap 0 r θ)
        (hdgα_holo _ hcm_in).continuousAt hc_cm).continuousWithinAt
    have hv_norm : ∀ ρ : ℝ, ‖v_fn ρ‖ = ‖deriv gα (circleMap 0 ρ θ)‖ := by
      intro ρ; dsimp [v_fn]
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hv_lint : (∫⁻ ρ in Ioo (1 / 2 : ℝ) 1, ENNReal.ofReal ‖v_fn ρ‖ ∂MeasureTheory.volume) < ⊤ := by
      have hle_sum : ∀ ρ ∈ Ioo (1 / 2 : ℝ) 1,
          ENNReal.ofReal ‖v_fn ρ‖ ≤ ENNReal.ofReal (1 / 2 : ℝ) + h_prod (ρ, θ) := by
        intro ρ hρ
        rw [hv_norm]
        dsimp [h_prod]
        rw [← ENNReal.ofReal_add (by norm_num) (mul_nonneg (by linarith [hρ.1]) (sq_nonneg _))]
        apply ENNReal.ofReal_le_ofReal
        set x : ℝ := ‖deriv gα (circleMap 0 ρ θ)‖
        have hx_sq : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
        have hρ_ge : (1 / 2 : ℝ) * x ^ 2 ≤ ρ * x ^ 2 :=
          mul_le_mul_of_nonneg_right hρ.1.le (sq_nonneg x)
        linarith
      have hmono := MeasureTheory.setLIntegral_mono' (μ := MeasureTheory.volume) measurableSet_Ioo hle_sum
      have hadd := MeasureTheory.lintegral_add_left'
        (aemeasurable_const (b := ENNReal.ofReal (1 / 2 : ℝ)))
        (μ := MeasureTheory.volume.restrict (Ioo (1 / 2 : ℝ) 1)) (fun ρ => h_prod (ρ, θ))
      have hconst_lt : (∫⁻ _ in Ioo (1 / 2 : ℝ) 1, ENNReal.ofReal (1 / 2 : ℝ) ∂MeasureTheory.volume) < ⊤ := by
        rw [MeasureTheory.setLIntegral_const, Real.volume_Ioo]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
      exact lt_of_le_of_lt hmono (by rw [hadd]; exact ENNReal.add_lt_top.mpr ⟨hconst_lt, hfin⟩)
    have hv_int : MeasureTheory.IntegrableOn v_fn (Ioo (1 / 2 : ℝ) 1) MeasureTheory.volume := by
      refine ⟨hv_cont.aestronglyMeasurable measurableSet_Ioo, ?_⟩
      rw [MeasureTheory.hasFiniteIntegral_iff_norm]
      exact hv_lint
    have hv_int34 : MeasureTheory.IntegrableOn v_fn (Ioo (3 / 4 : ℝ) 1) MeasureTheory.volume :=
      hv_int.mono_set (Ioo_subset_Ioo (by norm_num) le_rfl)
    -- Express `gα (circleMap 0 r θ)` for `r ∈ Ioo (3/4) 1` via FTC + Dominated Convergence
    let L : ℂ := gα (circleMap 0 (3 / 4 : ℝ) θ) +
      ∫ ρ in Ioo (3 / 4 : ℝ) 1, v_fn ρ ∂MeasureTheory.volume
    refine ⟨L, ?_⟩
    have hshift_eq : ∀ ρ : ℝ, g (circleMap 0 ρ (θ + α)) = gα (circleMap 0 ρ θ) := by
      intro ρ
      dsimp [gα, uα]
      congr 1
      simp only [circleMap_zero, Complex.ofReal_add, add_mul, Complex.exp_add]
      ring
    simp_rw [hshift_eq]
    have hlim_int : Tendsto
        (fun r : ℝ => ∫ ρ in Ioo (3 / 4 : ℝ) 1, (Ioc (3 / 4 : ℝ) r).indicator v_fn ρ ∂MeasureTheory.volume)
        (𝓝[<] (1 : ℝ))
        (𝓝 (∫ ρ in Ioo (3 / 4 : ℝ) 1, v_fn ρ ∂MeasureTheory.volume)) := by
      refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (fun ρ => ‖v_fn ρ‖) ?_ ?_ hv_int34.norm ?_
      · refine Filter.Eventually.of_forall fun r => ?_
        exact hv_int34.aestronglyMeasurable.indicator measurableSet_Ioc
      · refine Filter.Eventually.of_forall fun r => Filter.Eventually.of_forall fun ρ => ?_
        by_cases h : ρ ∈ Ioc (3 / 4 : ℝ) r
        · simp [h]
        · simp [h]
      · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hev : (fun r : ℝ => (Ioc (3 / 4 : ℝ) r).indicator v_fn ρ) =ᶠ[𝓝[<] (1 : ℝ)]
            fun _ => v_fn ρ := by
          filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hρ.2)] with r hr
          have hmem : ρ ∈ Ioc (3 / 4 : ℝ) r := ⟨hρ.1, le_of_lt hr⟩
          simp only [Set.indicator_of_mem hmem]
        exact tendsto_const_nhds.congr' hev.symm
    have hftc_ev : (fun r : ℝ => gα (circleMap 0 (3 / 4 : ℝ) θ) +
        ∫ ρ in Ioo (3 / 4 : ℝ) 1, (Ioc (3 / 4 : ℝ) r).indicator v_fn ρ ∂MeasureTheory.volume) =ᶠ[𝓝[<] (1 : ℝ)]
        fun r : ℝ => gα (circleMap 0 r θ) := by
      filter_upwards [Ioo_mem_nhdsLT (by norm_num : (3 / 4 : ℝ) < 1)] with r hr
      have hind_eq : (∫ ρ in Ioo (3 / 4 : ℝ) 1, (Ioc (3 / 4 : ℝ) r).indicator v_fn ρ ∂MeasureTheory.volume) =
          ∫ ρ in (3 / 4 : ℝ)..r, v_fn ρ := by
        have hinter : Ioc (3 / 4 : ℝ) r ∩ Ioo (3 / 4 : ℝ) 1 = Ioc (3 / 4 : ℝ) r :=
          Set.inter_eq_left.mpr fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hr.2⟩
        rw [MeasureTheory.integral_indicator measurableSet_Ioc,
          MeasureTheory.Measure.restrict_restrict measurableSet_Ioc,
          hinter, ← intervalIntegral.integral_of_le hr.1.le]
      rw [hind_eq]
      have hderiv_r : ∀ ρ ∈ Set.uIcc (3 / 4 : ℝ) r,
          HasDerivAt (fun s : ℝ => gα (circleMap 0 s θ)) (v_fn ρ) ρ := by
        intro ρ hρ_u
        rw [Set.uIcc_of_le hr.1.le] at hρ_u
        have hρ_pos : 0 < ρ := by linarith [hρ_u.1]
        have hcm_in : circleMap 0 ρ θ ∈ ball (0 : ℂ) 1 := by
          rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hρ_pos]
          exact lt_of_le_of_lt hρ_u.2 hr.2
        have hd_cm : HasDerivAt (fun s : ℝ => circleMap 0 s θ) (Complex.exp ((θ : ℂ) * Complex.I)) ρ := by
          simp only [circleMap_zero]
          simpa using (Complex.ofRealCLM.hasDerivAt (x := ρ)).mul_const (Complex.exp ((θ : ℂ) * Complex.I))
        exact HasDerivAt.comp (h₂ := gα) (h := fun s : ℝ => circleMap 0 s θ) ρ
          (hgα_holo _ hcm_in).hasDerivAt hd_cm
      have hint_iv : IntervalIntegrable v_fn MeasureTheory.volume (3 / 4 : ℝ) r := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.1.le]
        exact hv_int.mono_set (fun ρ hρ => ⟨by linarith [hρ.1], lt_of_le_of_lt hρ.2 hr.2⟩)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_r hint_iv]
      ring
    exact (tendsto_const_nhds.add hlim_int).congr' hftc_ev
  -- Cover `ℝ` by countably many shifted intervals `(k - π, k + π)` for `k : ℤ`
  have hae_z : ∀ k : ℤ, ∀ᵐ φ ∂MeasureTheory.volume, φ ∈ Ioo ((k : ℝ) - Real.pi) ((k : ℝ) + Real.pi) →
      ∃ L : ℂ, Tendsto (fun ρ : ℝ => g (circleMap 0 ρ φ)) (𝓝[<] 1) (𝓝 L) := by
    intro k
    have hk := hae_core (k : ℝ)
    -- Transport along translation `θ ↦ θ + k`
    have hmp : MeasureTheory.MeasurePreserving (fun φ : ℝ => φ - (k : ℝ))
        MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.measurePreserving_sub_right MeasureTheory.volume (k : ℝ)
    have hpull := hmp.quasiMeasurePreserving.ae hk
    filter_upwards [hpull] with φ hφ hφ_in
    have hsub_in : φ - (k : ℝ) ∈ Ioo (-Real.pi) Real.pi := ⟨by linarith [hφ_in.1], by linarith [hφ_in.2]⟩
    simpa [sub_add_cancel] using hφ hsub_in
  rw [← MeasureTheory.ae_all_iff] at hae_z
  filter_upwards [hae_z] with φ hφ
  let k : ℤ := ⌊φ⌋
  have hk1 : (k : ℝ) ≤ φ := Int.floor_le φ
  have hk2 : φ < (k : ℝ) + 1 := Int.lt_floor_add_one φ
  exact hφ k ⟨by linarith [Real.two_le_pi], by linarith [Real.two_le_pi]⟩

/-- If `h` is holomorphic and bounded on `ball 0 1`, `a < b`, and `h (circleMap 0 ρ φ) → 0` as
`ρ → 1⁻` for a.e. `φ ∈ Ioo a b`, then `h 0 = 0`. -/
theorem holomorphic_zero_at_zero_of_ae_radial_zero_arc {h : ℂ → ℂ}
    (hh_holo : RudinRCA.Chapter10.HolomorphicOn h (ball (0 : ℂ) 1))
    {B : ℝ} (hB : 0 ≤ B) (hh_bdd : ∀ w ∈ ball (0 : ℂ) 1, ‖h w‖ ≤ B)
    {a b : ℝ} (hab : a < b)
    (hae : ∀ᵐ φ ∂(MeasureTheory.volume.restrict (Ioo a b)),
      Tendsto (fun ρ : ℝ => h (circleMap 0 ρ φ)) (𝓝[<] 1) (𝓝 0)) :
    h 0 = 0 := by
  have hba_pos : 0 < b - a := sub_pos.mpr hab
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * Real.pi / (b - a))
  have hN_pos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | hp
    · have : 0 < 2 * Real.pi / (b - a) := div_pos (by positivity) hba_pos
      simp at hN; linarith
    · exact hp
  let s : ℝ := 2 * Real.pi / (N : ℝ)
  have hs_pos : 0 < s := div_pos (by positivity) (Nat.cast_pos.mpr hN_pos)
  have hs_lt : s < b - a := by
    dsimp [s]
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hN_pos)]
    have := (div_lt_iff₀ hba_pos).mp hN
    linarith
  let ω : ℂ := Complex.exp ((s : ℂ) * Complex.I)
  have hω_norm : ‖ω‖ = 1 := Complex.norm_exp_ofReal_mul_I s
  let P : ℂ → ℂ := fun w => ∏ j ∈ Finset.range N, h (ω ^ j * w)
  have hP_holo : RudinRCA.Chapter10.HolomorphicOn P (ball (0 : ℂ) 1) := by
    intro w hw
    dsimp [P]
    have hdiff_prod : ∀ S : Finset ℕ,
        (∀ j ∈ S, DifferentiableAt ℂ (fun z => h (ω ^ j * z)) w) →
        DifferentiableAt ℂ (fun z => ∏ j ∈ S, h (ω ^ j * z)) w := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro _; simp only [Finset.prod_empty]; exact differentiableAt_const (1 : ℂ)
      | @insert k s' hk ih =>
        intro hfac
        have h_eq : (fun z => ∏ j ∈ insert k s', h (ω ^ j * z)) =
            fun z => h (ω ^ k * z) * ∏ j ∈ s', h (ω ^ j * z) := by
          ext z; exact Finset.prod_insert hk
        rw [h_eq]
        exact (hfac k (Finset.mem_insert_self k s')).mul
          (ih fun j hj => hfac j (Finset.mem_insert_of_mem hj))
    refine hdiff_prod (Finset.range N) fun j _ => ?_
    have hm : ω ^ j * w ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff] at hw ⊢
      rw [norm_mul, norm_pow, hω_norm, one_pow, one_mul]; exact hw
    exact (hh_holo _ hm).comp w (differentiableAt_id.const_mul (ω ^ j))
  let B₁ : ℝ := max B 1
  have hB₁_pos : 0 < B₁ := lt_max_of_lt_right zero_lt_one
  have _ := hB
  have hP_bdd : ∀ w ∈ ball (0 : ℂ) 1, ‖P w‖ ≤ B₁ ^ N := by
    intro w hw
    dsimp [P]
    rw [norm_prod]
    calc
      (∏ j ∈ Finset.range N, ‖h (ω ^ j * w)‖)
          ≤ ∏ _j ∈ Finset.range N, B₁ := by
            gcongr with j _
            have hm : ω ^ j * w ∈ ball (0 : ℂ) 1 := by
              rw [mem_ball_zero_iff] at hw ⊢
              rw [norm_mul, norm_pow, hω_norm, one_pow, one_mul]; exact hw
            exact (hh_bdd _ hm).trans (le_max_left B 1)
      _ = B₁ ^ N := by simp
  -- Show `P (circleMap 0 ρ θ) → 0` as `ρ → 1⁻` for a.e. `θ ∈ ℝ`
  let Z : Set ℝ := {φ : ℝ | Tendsto (fun ρ : ℝ => h (circleMap 0 ρ φ)) (𝓝[<] 1) (𝓝 0)}
  have hZ_per : ∀ (φ : ℝ) (m : ℤ), φ - 2 * Real.pi * (m : ℝ) ∈ Z → φ ∈ Z := by
    intro φ m hm
    dsimp [Z] at hm ⊢
    refine hm.congr fun ρ => ?_
    congr 1
    simp only [circleMap_zero]
    congr 1
    have harg : (φ : ℂ) * Complex.I =
        ((φ - 2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I +
          (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I m, mul_one]
  have hae_imp : ∀ᵐ φ ∂MeasureTheory.volume, φ ∈ Ioo a b → φ ∈ Z := by
    rwa [MeasureTheory.ae_restrict_iff' measurableSet_Ioo] at hae
  have hae_pair : ∀ (j : Fin N) (m : ℤ),
      ∀ᵐ θ ∂MeasureTheory.volume,
        θ + (j.1 : ℝ) * s - 2 * Real.pi * (m : ℝ) ∈ Ioo a b →
          θ + (j.1 : ℝ) * s ∈ Z := by
    intro j m
    let c : ℝ := (j.1 : ℝ) * s - 2 * Real.pi * (m : ℝ)
    have hmp : MeasureTheory.MeasurePreserving (fun θ : ℝ => θ + c)
        MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.measurePreserving_add_right MeasureTheory.volume c
    filter_upwards [hmp.quasiMeasurePreserving.ae hae_imp] with θ hθ hin
    have hc_eq : θ + c = θ + (j.1 : ℝ) * s - 2 * Real.pi * (m : ℝ) := by dsimp [c]; ring
    rw [← hc_eq] at hin
    have hz : θ + c ∈ Z := hθ hin
    rw [hc_eq] at hz
    exact hZ_per (θ + (j.1 : ℝ) * s) m hz
  have hae_all : ∀ᵐ θ ∂MeasureTheory.volume, ∀ (j : Fin N) (m : ℤ),
      θ + (j.1 : ℝ) * s - 2 * Real.pi * (m : ℝ) ∈ Ioo a b → θ + (j.1 : ℝ) * s ∈ Z := by
    rw [MeasureTheory.ae_all_iff]
    intro j
    rw [MeasureTheory.ae_all_iff]
    exact hae_pair j
  have hae_P0 : ∀ᵐ θ ∂MeasureTheory.volume,
      Tendsto (fun ρ : ℝ => P (circleMap 0 ρ θ)) (𝓝[<] 1) (𝓝 0) := by
    filter_upwards [hae_all] with θ hθ
    -- Find `q = ⌊(a - θ) / s⌋ + 1`, write `q = N * (q / N) + (q % N)`
    let q : ℤ := ⌊(a - θ) / s⌋ + 1
    have hq_lo : a < θ + (q : ℝ) * s := by
      have h1 : (a - θ) / s < (q : ℝ) := by
        dsimp [q]; push_cast; exact Int.lt_floor_add_one _
      have := (div_lt_iff₀ hs_pos).mp h1
      linarith
    have hq_hi : θ + (q : ℝ) * s < b := by
      have h1 : (q : ℝ) - 1 ≤ (a - θ) / s := by
        dsimp [q]; push_cast; linarith [Int.floor_le ((a - θ) / s)]
      have h2 : ((q : ℝ) - 1) * s ≤ a - θ := (le_div_iff₀ hs_pos).mp h1
      nlinarith
    have hN_int_pos : (0 : ℤ) < (N : ℤ) := Int.natCast_pos.mpr hN_pos
    let r_int : ℤ := q % (N : ℤ)
    have hr_nonneg : 0 ≤ r_int := Int.emod_nonneg q hN_int_pos.ne'
    have hr_lt : r_int < (N : ℤ) := Int.emod_lt_of_pos q hN_int_pos
    let j_nat : ℕ := r_int.toNat
    have hj_lt : j_nat < N := by
      have : (j_nat : ℤ) = r_int := Int.toNat_of_nonneg hr_nonneg
      omega
    let m : ℤ := -(q / (N : ℤ))
    have hq_decomp : (q : ℝ) * s = (j_nat : ℝ) * s - 2 * Real.pi * (m : ℝ) := by
      have hdiv : q = (N : ℤ) * (q / (N : ℤ)) + r_int := by
        dsimp [r_int]
        rw [Int.emod_def]
        ring
      have hr_eq : (j_nat : ℤ) = r_int := Int.toNat_of_nonneg hr_nonneg
      have hq_r : (q : ℝ) = (N : ℝ) * (-(m : ℝ)) + (j_nat : ℝ) := by
        have hdiv_r : (q : ℝ) = ((N : ℤ) : ℝ) * ((q / (N : ℤ) : ℤ) : ℝ) + (r_int : ℝ) := by
          exact_mod_cast hdiv
        push_cast at hdiv_r
        have hm_r : (m : ℝ) = -((q / (N : ℤ) : ℤ) : ℝ) := by dsimp [m]; push_cast; ring
        have hj_r : (j_nat : ℝ) = (r_int : ℝ) := by exact_mod_cast hr_eq
        nlinarith
      have hNs : (N : ℝ) * s = 2 * Real.pi := by
        dsimp [s]; exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hN_pos.ne')
      calc
        (q : ℝ) * s = ((N : ℝ) * (-(m : ℝ)) + (j_nat : ℝ)) * s := by rw [hq_r]
        _ = -((N : ℝ) * s) * (m : ℝ) + (j_nat : ℝ) * s := by ring
        _ = (j_nat : ℝ) * s - 2 * Real.pi * (m : ℝ) := by rw [hNs]; ring
    have hin_ab : θ + (j_nat : ℝ) * s - 2 * Real.pi * (m : ℝ) ∈ Ioo a b :=
      ⟨by linarith [hq_lo, hq_decomp], by linarith [hq_hi, hq_decomp]⟩
    have hj_Z : θ + (j_nat : ℝ) * s ∈ Z := hθ ⟨j_nat, hj_lt⟩ m hin_ab
    -- Factor `P (circleMap 0 ρ θ)` into `h (circleMap 0 ρ (θ + j_nat * s))` times bounded rest
    let rest : ℝ → ℂ := fun ρ => ∏ k ∈ (Finset.range N).erase j_nat, h (ω ^ k * circleMap 0 ρ θ)
    have hfact : ∀ ρ : ℝ, P (circleMap 0 ρ θ) =
        h (circleMap 0 ρ (θ + (j_nat : ℝ) * s)) * rest ρ := by
      intro ρ
      dsimp [P, rest]
      rw [← Finset.mul_prod_erase (Finset.range N) (fun k => h (ω ^ k * circleMap 0 ρ θ))
        (Finset.mem_range.mpr hj_lt)]
      congr 2
      dsimp [ω]
      rw [circleMap_zero, circleMap_zero, ← Complex.exp_nat_mul]
      have hexp : Complex.exp ((j_nat : ℂ) * ((s : ℂ) * Complex.I)) *
          ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
          (ρ : ℂ) * Complex.exp (((θ + (j_nat : ℝ) * s : ℝ) : ℂ) * Complex.I) := by
        rw [mul_left_comm, ← Complex.exp_add]
        congr 2
        push_cast; ring
      exact hexp
    simp_rw [hfact]
    -- `h (...) → 0` and `‖rest ρ‖ ≤ B₁ ^ (N - 1)` eventually for `ρ ∈ (0, 1)`
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hB_pow_pos : 0 < B₁ ^ N := pow_pos hB₁_pos N
    have hlim0 := Metric.tendsto_nhds.mp hj_Z (ε / B₁ ^ N) (div_pos hε hB_pow_pos)
    filter_upwards [hlim0, Ioo_mem_nhdsLT zero_lt_one] with ρ hρ_small hρ_in
    rw [dist_zero_right] at hρ_small ⊢
    have hrest_le : ‖rest ρ‖ ≤ B₁ ^ N := by
      dsimp [rest]
      rw [norm_prod]
      calc
        (∏ k ∈ (Finset.range N).erase j_nat, ‖h (ω ^ k * circleMap 0 ρ θ)‖)
            ≤ ∏ _k ∈ (Finset.range N).erase j_nat, B₁ := by
              gcongr with k _
              have hm : ω ^ k * circleMap 0 ρ θ ∈ ball (0 : ℂ) 1 := by
                rw [mem_ball_zero_iff, norm_mul, norm_pow, hω_norm, one_pow, one_mul,
                  norm_circleMap_zero, abs_of_pos hρ_in.1]
                exact hρ_in.2
              exact (hh_bdd _ hm).trans (le_max_left B 1)
        _ = B₁ ^ ((Finset.range N).erase j_nat).card := by simp
        _ ≤ B₁ ^ N := pow_le_pow_right₀ (le_max_right B 1) (Finset.card_erase_le.trans (by simp))
    rw [norm_mul]
    calc
      ‖h (circleMap 0 ρ (θ + (j_nat : ℝ) * s))‖ * ‖rest ρ‖
          ≤ ‖h (circleMap 0 ρ (θ + (j_nat : ℝ) * s))‖ * B₁ ^ N :=
            mul_le_mul_of_nonneg_left hrest_le (norm_nonneg _)
      _ < (ε / B₁ ^ N) * B₁ ^ N :=
            mul_lt_mul_of_pos_right hρ_small hB_pow_pos
      _ = ε := div_mul_cancel₀ ε hB_pow_pos.ne'
  -- Mean value property on `circleMap 0 r θ` + Dominated Convergence as `r → 1⁻`
  have hmvp : ∀ r ∈ Ioo (0 : ℝ) 1, P 0 = Real.circleAverage P 0 r := by
    intro r hr
    have habs : |r| = r := abs_of_pos hr.1
    have hcont_cl : ContinuousOn P (closedBall (0 : ℂ) |r|) := by
      rw [habs]
      exact (RudinRCA.Chapter10.continuousOn_of_holomorphicOn hP_holo).mono
        (Metric.closedBall_subset_ball hr.2)
    have hdiff_in : ∀ z ∈ ball (0 : ℂ) |r| \ (∅ : Set ℂ), DifferentiableAt ℂ P z := by
      rw [habs]
      exact fun z hz => hP_holo z (Metric.ball_subset_ball hr.2.le hz.1)
    exact (circleAverage_of_differentiable_on_off_countable Set.countable_empty hcont_cl hdiff_in).symm
  have hlim_avg : Tendsto (fun r : ℝ => Real.circleAverage P 0 r) (𝓝[<] 1) (𝓝 0) := by
    have hdef : ∀ r : ℝ, Real.circleAverage P 0 r =
        (2 * Real.pi)⁻¹ • ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), P (circleMap 0 r θ) ∂MeasureTheory.volume := by
      intro r
      rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity)]
    simp_rw [hdef]
    have hlim_int0 : Tendsto
        (fun r : ℝ => ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), P (circleMap 0 r θ) ∂MeasureTheory.volume)
        (𝓝[<] 1)
        (𝓝 (∫ _θ in Ioc (0 : ℝ) (2 * Real.pi), (0 : ℂ) ∂MeasureTheory.volume)) := by
      refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (fun _ => B₁ ^ N) ?_ ?_ ?_ ?_
      · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
        have hcP : ContinuousOn P (ball (0 : ℂ) 1) :=
          RudinRCA.Chapter10.continuousOn_of_holomorphicOn hP_holo
        have hc : Continuous (fun θ : ℝ => P (circleMap 0 r θ)) := by
          refine hcP.comp_continuous (continuous_circleMap 0 r) fun θ => ?_
          rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr.1]
          exact hr.2
        exact hc.aestronglyMeasurable
      · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
        refine Filter.Eventually.of_forall fun θ => hP_bdd _ ?_
        rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr.1]
        exact hr.2
      · exact MeasureTheory.integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top.ne)
      · exact MeasureTheory.ae_restrict_of_ae hae_P0
    simpa using hlim_int0.const_smul (2 * Real.pi)⁻¹
  have hev_const : (fun r : ℝ => Real.circleAverage P 0 r) =ᶠ[𝓝[<] 1] fun _ => P 0 := by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
    exact (hmvp r hr).symm
  have hP0_eq_0 : P 0 = 0 := tendsto_nhds_unique tendsto_const_nhds (hlim_avg.congr' hev_const)
  have hP0_pow : P 0 = h 0 ^ N := by
    dsimp [P]
    simp [mul_zero]
  rw [hP0_pow] at hP0_eq_0
  exact (pow_eq_zero_iff hN_pos.ne').mp hP0_eq_0

/-! ### Boundary modulus 1, Lindelöf curve convergence, and Theorem 14.18 -/

/-- Properness of a holomorphic bijection `f : Ω → ball 0 1`: as `z ∈ Ω` approaches any boundary
point `β ∈ frontier Ω`, `‖f z‖ → 1`. -/
theorem tendsto_norm_one_nhdsWithin {Ω : Set ℂ} (hΩ_open : IsOpen Ω)
    {f : ℂ → ℂ} (hf_holo : RudinRCA.Chapter10.HolomorphicOn f Ω)
    (hf_bij : BijOn f Ω (ball (0 : ℂ) 1)) {β : ℂ} (hβ : β ∈ frontier Ω) :
    Tendsto (fun z => ‖f z‖) (𝓝[Ω] β) (𝓝 1) := by
  obtain ⟨g, hg_holo, hg_bij, hgf, _⟩ := (theorem14_7 hΩ_open hf_holo hf_bij).2.1
  have hβ_notΩ : β ∉ Ω := by
    have hint : interior Ω = Ω := hΩ_open.interior_eq
    intro hmem
    exact hβ.2 (hint.symm ▸ hmem)
  rw [Metric.tendsto_nhds]
  intro ε hε
  let r : ℝ := max 0 (1 - ε / 2)
  have hr_lt : r < 1 := max_lt zero_lt_one (by linarith)
  let K : Set ℂ := g '' closedBall (0 : ℂ) r
  have hK_compact : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) r).image_of_continuousOn
      ((RudinRCA.Chapter10.continuousOn_of_holomorphicOn hg_holo).mono
        (Metric.closedBall_subset_ball hr_lt))
  have hK_sub : K ⊆ Ω := by
    rintro _ ⟨w, hw, rfl⟩
    exact hg_bij.mapsTo (Metric.closedBall_subset_ball hr_lt hw)
  have hβ_notK : β ∉ K := fun h => hβ_notΩ (hK_sub h)
  have hKc_nhds : Kᶜ ∈ 𝓝[Ω] β :=
    nhdsWithin_le_nhds (hK_compact.isClosed.isOpen_compl.mem_nhds hβ_notK)
  filter_upwards [self_mem_nhdsWithin, hKc_nhds] with z hzΩ hzKc
  have hfz_lt : ‖f z‖ < 1 := mem_ball_zero_iff.mp (hf_bij.mapsTo hzΩ)
  have hfz_gt : r < ‖f z‖ := by
    by_contra hle
    have hmemK : z ∈ K := ⟨f z, mem_closedBall_zero_iff.mpr (not_lt.mp hle), hgf z hzΩ⟩
    exact hzKc hmemK
  have hge : 1 - ε / 2 ≤ r := le_max_right 0 (1 - ε / 2)
  rw [Real.dist_eq, abs_of_neg (by linarith)]
  linarith

/-- Helper: a curve `γ : [0, 1] → ℂ` continuous on `[0, 1]` mapping `[0, 1)` into `Ω` with
`γ 1 = β` tends to `β` within `Ω` along `𝓝[<] 1`. -/
theorem tendsto_nhdsWithin_of_curve_Icc {Ω : Set ℂ} {γ : ℝ → ℂ} {β : ℂ}
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγ_in : ∀ s ∈ Ico (0 : ℝ) 1, γ s ∈ Ω) (hγ1 : γ 1 = β) :
    Tendsto γ (𝓝[<] (1 : ℝ)) (𝓝[Ω] β) := by
  have h_icc : Tendsto (fun t : ℝ => t) (𝓝[<] (1 : ℝ)) (𝓝[Icc (0 : ℝ) 1] 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_id.mono_left nhdsWithin_le_nhds)
      (by
        filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with t ht
        exact ⟨ht.1.le, ht.2.le⟩)
  have hγ_nhds : Tendsto γ (𝓝[<] (1 : ℝ)) (𝓝 β) := by
    rw [← hγ1]
    exact (hγ_cont 1 (right_mem_Icc.mpr zero_le_one)).tendsto.comp h_icc
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hγ_nhds ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  exact hγ_in t ⟨ht.1.le, ht.2⟩

/-- Along any continuous curve `γ : [0, 1] → ℂ` mapping `[0, 1)` into a bounded open set `Ω` and
ending at `γ 1 = β ∈ frontier Ω`, a holomorphic bijection `f : Ω → ball 0 1` converges as `t → 1⁻`
to a point `w₀` of norm `1`. -/
theorem lindelof_curve_tendsto {Ω : Set ℂ} (hΩ_open : IsOpen Ω)
    (hΩ_bdd : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf_holo : RudinRCA.Chapter10.HolomorphicOn f Ω)
    (hf_bij : BijOn f Ω (ball (0 : ℂ) 1)) {β : ℂ} (hβ : β ∈ frontier Ω)
    {γ : ℝ → ℂ} (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγ_in : ∀ s ∈ Ico (0 : ℝ) 1, γ s ∈ Ω) (hγ1 : γ 1 = β) :
    ∃ w₀ : ℂ, ‖w₀‖ = 1 ∧ Tendsto (fun t => f (γ t)) (𝓝[<] 1) (𝓝 w₀) := by
  obtain ⟨g, hg_holo, hg_bij, hgf, _⟩ := (theorem14_7 hΩ_open hf_holo hf_bij).2.1
  have hβ_notΩ : β ∉ Ω := by
    have hint : interior Ω = Ω := hΩ_open.interior_eq
    intro hmem
    exact hβ.2 (hint.symm ▸ hmem)
  obtain ⟨M₀, hM₀⟩ := hΩ_bdd.subset_closedBall (0 : ℂ)
  let M : ℝ := max M₀ 1
  have hM_pos : 0 < M := lt_max_of_lt_right zero_lt_one
  have hg_bdd : ∀ w ∈ ball (0 : ℂ) 1, ‖g w‖ ≤ M := by
    intro w hw
    have hz : g w ∈ closedBall (0 : ℂ) M₀ := hM₀ (hg_bij.mapsTo hw)
    exact (mem_closedBall_zero_iff.mp hz).trans (le_max_left M₀ 1)
  have hγ_tendsto_Ω : Tendsto γ (𝓝[<] (1 : ℝ)) (𝓝[Ω] β) :=
    tendsto_nhdsWithin_of_curve_Icc hγ_cont hγ_in hγ1
  let Γ : ℝ → ℂ := fun t => f (γ t)
  have hnorm_lim : Tendsto (fun t => ‖Γ t‖) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
    (tendsto_norm_one_nhdsWithin hΩ_open hf_holo hf_bij hβ).comp hγ_tendsto_Ω
  -- Choose `T₀ ∈ (0, 1)` such that `1 / 2 < ‖Γ t‖` for all `t ∈ [T₀, 1)`
  have hev_half : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1 ∧ (1 / 2 : ℝ) < ‖Γ t‖ := by
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1),
      hnorm_lim.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with t ht₁ ht₂
    exact ⟨ht₁, ht₂⟩
  obtain ⟨l₀, hl₀_lt_mem, hl₀_sub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).mp hev_half
  have hl₀_lt : l₀ < 1 := hl₀_lt_mem
  let T₀ : ℝ := (max l₀ 0 + 1) / 2
  have hT₀_in : T₀ ∈ Ioo (0 : ℝ) 1 := by
    have h1 : max l₀ 0 < 1 := max_lt hl₀_lt zero_lt_one
    exact ⟨by positivity, by dsimp [T₀]; linarith⟩
  have hΓ_half : ∀ t ∈ Ico T₀ 1, (1 / 2 : ℝ) < ‖Γ t‖ := by
    intro t ht
    have hmax_lt : max l₀ 0 < T₀ := by
      dsimp [T₀]; linarith [max_lt hl₀_lt zero_lt_one]
    have ht_ioo : t ∈ Ioo l₀ 1 := ⟨lt_of_le_of_lt (le_max_left l₀ 0) (lt_of_lt_of_le hmax_lt ht.1), ht.2⟩
    exact (hl₀_sub ht_ioo).2
  have hΓ_ne : ∀ t ∈ Ico T₀ 1, Γ t ≠ 0 := by
    intro t ht h0
    have := hΓ_half t ht
    rw [h0, norm_zero] at this
    linarith
  have hΓ_cont : ContinuousOn Γ (Ico T₀ 1) := by
    refine (RudinRCA.Chapter10.continuousOn_of_holomorphicOn hf_holo).comp
      (hγ_cont.mono (fun t ht => ⟨le_trans hT₀_in.1.le ht.1, ht.2.le⟩)) ?_
    intro t ht
    exact hγ_in t ⟨le_trans hT₀_in.1.le ht.1, ht.2⟩
  -- Lift `Γ` on `[T₀, 1)` to a continuous angle `ϑ`
  obtain ⟨ϑ, hϑ_cont, hϑ_eq⟩ := exists_continuousOn_angle_Ico hT₀_in.2 hΓ_cont hΓ_ne
  -- Show `ϑ` satisfies the Cauchy criterion as `t → 1⁻`
  have hϑ_cauchy : ∀ ε > 0, ∃ T ∈ Ico T₀ 1, ∀ u ∈ Ico T 1, ∀ v ∈ Ico T 1, |ϑ v - ϑ u| < ε := by
    by_contra hnot_cauchy
    -- Derive an open interval `Ioo a b` (`a < b`) swept mod `2π` for all `T ∈ [T₀, 1)`
    have hex_arc : ∃ a b : ℝ, a < b ∧ ∀ φ ∈ Ioo a b, ∀ T ∈ Ico T₀ 1,
        ∃ t ∈ Ico T 1, ∃ m : ℤ, ϑ t = φ + 2 * Real.pi * (m : ℝ) := by
      by_cases hub_hi : ∀ B : ℝ, ∃ t ∈ Ico T₀ 1, B < ϑ t
      · -- Subcase 1: `ϑ` is unbounded above on `[T₀, 1)`
        refine ⟨0, 2 * Real.pi, by positivity, ?_⟩
        intro φ _ T hT
        -- `ϑ` is bounded on compact `[T₀, T]`, hence unbounded above on `[T, 1)`
        have hcomp : IsCompact (ϑ '' Icc T₀ T) :=
          (isCompact_Icc).image_of_continuousOn
            (hϑ_cont.mono (fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 hT.2⟩))
        obtain ⟨B₀, hB₀⟩ := hcomp.bddAbove
        let m : ℤ := ⌊(max B₀ (ϑ T) - φ) / (2 * Real.pi)⌋ + 1
        have hm_gt : max B₀ (ϑ T) < φ + 2 * Real.pi * (m : ℝ) := by
          have h1 : (max B₀ (ϑ T) - φ) / (2 * Real.pi) < (m : ℝ) := by
            dsimp [m]; push_cast; exact Int.lt_floor_add_one _
          have h2 := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp h1
          linarith
        obtain ⟨t₁, ht₁_in, ht₁_gt⟩ := hub_hi (φ + 2 * Real.pi * (m : ℝ))
        have ht₁_ge_T : T ≤ t₁ := by
          by_contra hlt
          have hle_B₀ : ϑ t₁ ≤ B₀ := hB₀ ⟨t₁, ⟨ht₁_in.1, (not_le.mp hlt).le⟩, rfl⟩
          have : B₀ ≤ max B₀ (ϑ T) := le_max_left _ _
          linarith
        have hivt : φ + 2 * Real.pi * (m : ℝ) ∈ ϑ '' Icc T t₁ := by
          apply intermediate_value_Icc ht₁_ge_T
            (hϑ_cont.mono (fun s hs => ⟨le_trans hT.1 hs.1, lt_of_le_of_lt hs.2 ht₁_in.2⟩))
          exact ⟨le_trans (le_max_right B₀ (ϑ T)) hm_gt.le, ht₁_gt.le⟩
        rcases hivt with ⟨t, ht_icc, ht_eq⟩
        exact ⟨t, ⟨ht_icc.1, lt_of_le_of_lt ht_icc.2 ht₁_in.2⟩, m, ht_eq⟩
      · by_cases hub_lo : ∀ B : ℝ, ∃ t ∈ Ico T₀ 1, ϑ t < B
        · -- Subcase 2: `ϑ` is unbounded below on `[T₀, 1)`
          refine ⟨0, 2 * Real.pi, by positivity, ?_⟩
          intro φ _ T hT
          have hcomp : IsCompact (ϑ '' Icc T₀ T) :=
            (isCompact_Icc).image_of_continuousOn
              (hϑ_cont.mono (fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 hT.2⟩))
          obtain ⟨B₀, hB₀⟩ := hcomp.bddBelow
          let m : ℤ := -(⌊(φ - min B₀ (ϑ T)) / (2 * Real.pi)⌋ + 1)
          have hm_lt : φ + 2 * Real.pi * (m : ℝ) < min B₀ (ϑ T) := by
            have h1 : (φ - min B₀ (ϑ T)) / (2 * Real.pi) < -(m : ℝ) := by
              dsimp [m]; push_cast; linarith [Int.lt_floor_add_one ((φ - min B₀ (ϑ T)) / (2 * Real.pi))]
            have h2 := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp h1
            linarith
          obtain ⟨t₁, ht₁_in, ht₁_lt⟩ := hub_lo (φ + 2 * Real.pi * (m : ℝ))
          have ht₁_ge_T : T ≤ t₁ := by
            by_contra hlt
            have hge_B₀ : B₀ ≤ ϑ t₁ := hB₀ ⟨t₁, ⟨ht₁_in.1, (not_le.mp hlt).le⟩, rfl⟩
            have : min B₀ (ϑ T) ≤ B₀ := min_le_left _ _
            linarith
          have hivt : φ + 2 * Real.pi * (m : ℝ) ∈ ϑ '' Icc T t₁ := by
            apply intermediate_value_Icc' ht₁_ge_T
              (hϑ_cont.mono (fun s hs => ⟨le_trans hT.1 hs.1, lt_of_le_of_lt hs.2 ht₁_in.2⟩))
            exact ⟨ht₁_lt.le, le_trans hm_lt.le (min_le_right B₀ (ϑ T))⟩
          rcases hivt with ⟨t, ht_icc, ht_eq⟩
          exact ⟨t, ⟨ht_icc.1, lt_of_le_of_lt ht_icc.2 ht₁_in.2⟩, m, ht_eq⟩
        · -- Subcase 3: `ϑ` is bounded on `[T₀, 1)` and fails Cauchy at `1⁻`
          have hex_hi : ∃ B_hi : ℝ, ∀ t ∈ Ico T₀ 1, ϑ t ≤ B_hi := by
            by_contra hno
            apply hub_hi
            intro B
            by_contra hnoB
            exact hno ⟨B, fun t ht => le_of_not_gt fun hgt => hnoB ⟨t, ht, hgt⟩⟩
          have hex_lo : ∃ B_lo : ℝ, ∀ t ∈ Ico T₀ 1, B_lo ≤ ϑ t := by
            by_contra hno
            apply hub_lo
            intro B
            by_contra hnoB
            exact hno ⟨B, fun t ht => le_of_not_gt fun hlt => hnoB ⟨t, ht, hlt⟩⟩
          obtain ⟨B_hi, hB_hi⟩ := hex_hi
          obtain ⟨B_lo, hB_lo⟩ := hex_lo
          have hex_eps : ∃ ε₀ > 0, ∀ T ∈ Ico T₀ 1, ∃ u ∈ Ico T 1, ∃ v ∈ Ico T 1, ε₀ ≤ ϑ v - ϑ u := by
            by_contra hno
            apply hnot_cauchy
            intro ε hε
            by_contra hnoT
            apply hno ⟨ε, hε, fun T hT => ?_⟩
            have hex_uv : ∃ u ∈ Ico T 1, ∃ v ∈ Ico T 1, ε ≤ |ϑ v - ϑ u| := by
              by_contra hall
              exact hnoT ⟨T, hT, fun u hu v hv => lt_of_not_ge fun hge => hall ⟨u, hu, v, hv, hge⟩⟩
            rcases hex_uv with ⟨u, hu, v, hv, hge⟩
            rcases le_total (ϑ u) (ϑ v) with huv | hvu
            · exact ⟨u, hu, v, hv, by rwa [abs_of_nonneg (sub_nonneg.mpr huv)] at hge⟩
            · exact ⟨v, hv, u, hu, by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hvu)] at hge; exact hge⟩
          obtain ⟨ε₀, hε₀_pos, hosc⟩ := hex_eps
          let δ : ℝ := ε₀ / 4
          have hδ_pos : 0 < δ := by positivity
          let k_lo : ℤ := ⌊B_lo / δ⌋ + 1
          let k_hi : ℤ := ⌊B_hi / δ⌋ + 1
          have hk_le : k_lo ≤ k_hi := by
            have : B_lo / δ ≤ B_hi / δ :=
              div_le_div_of_nonneg_right
                (le_trans (hB_lo T₀ ⟨le_rfl, hT₀_in.2⟩) (hB_hi T₀ ⟨le_rfl, hT₀_in.2⟩)) hδ_pos.le
            have := Int.floor_mono this
            dsimp [k_lo, k_hi]; omega
          let S_grid : Finset ℤ := Finset.Icc k_lo k_hi
          have hS_ne : S_grid.Nonempty := ⟨k_lo, Finset.mem_Icc.mpr ⟨le_rfl, hk_le⟩⟩
          -- Some `k ∈ S_grid` has `(k * δ, (k + 1) * δ)` straddled for EVERY `T ∈ [T₀, 1)`
          have hex_k : ∃ k ∈ S_grid, ∀ T ∈ Ico T₀ 1,
              ∃ u ∈ Ico T 1, ∃ v ∈ Ico T 1, ϑ u < (k : ℝ) * δ ∧ ((k : ℝ) + 1) * δ < ϑ v := by
            by_contra hno_k
            have hall_bad : ∀ k ∈ S_grid, ∃ T ∈ Ico T₀ 1, ∀ u ∈ Ico T 1, ∀ v ∈ Ico T 1,
                ¬ (ϑ u < (k : ℝ) * δ ∧ ((k : ℝ) + 1) * δ < ϑ v) := by
              intro k hk
              by_contra hk_good
              exact hno_k ⟨k, hk, fun T hT => by
                by_contra hT_bad
                exact hk_good ⟨T, hT, fun u hu v hv hstrad => hT_bad ⟨u, hu, v, hv, hstrad⟩⟩⟩
            choose T_bad hT_bad_in hT_bad_prop using fun (k : S_grid) => hall_bad k.1 k.2
            let S_sub : Finset S_grid := Finset.univ
            have hS_sub_ne : S_sub.Nonempty := ⟨⟨k_lo, Finset.mem_Icc.mpr ⟨le_rfl, hk_le⟩⟩, Finset.mem_univ _⟩
            let T_max : ℝ := S_sub.sup' hS_sub_ne T_bad
            have hT_max_in : T_max ∈ Ico T₀ 1 := by
              refine ⟨?_, ?_⟩
              · exact le_trans (hT_bad_in ⟨k_lo, Finset.mem_Icc.mpr ⟨le_rfl, hk_le⟩⟩).1
                  (Finset.le_sup' T_bad (Finset.mem_univ _))
              · exact (Finset.sup'_lt_iff hS_sub_ne).mpr fun k _ => (hT_bad_in k).2
            obtain ⟨u, hu, v, hv, huv⟩ := hosc T_max hT_max_in
            let k₀ : ℤ := ⌊ϑ u / δ⌋ + 1
            have hk₀_mem : k₀ ∈ S_grid := by
              refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
              · have := Int.floor_mono (div_le_div_of_nonneg_right (hB_lo u ⟨le_trans hT_max_in.1 hu.1, hu.2⟩) hδ_pos.le)
                dsimp [k_lo, k₀]; omega
              · have := Int.floor_mono (div_le_div_of_nonneg_right (hB_hi u ⟨le_trans hT_max_in.1 hu.1, hu.2⟩) hδ_pos.le)
                dsimp [k_hi, k₀]; omega
            have hT_le : T_bad ⟨k₀, hk₀_mem⟩ ≤ T_max := Finset.le_sup' T_bad (Finset.mem_univ _)
            have hu' : u ∈ Ico (T_bad ⟨k₀, hk₀_mem⟩) 1 := ⟨le_trans hT_le hu.1, hu.2⟩
            have hv' : v ∈ Ico (T_bad ⟨k₀, hk₀_mem⟩) 1 := ⟨le_trans hT_le hv.1, hv.2⟩
            have hlt1 : ϑ u < (k₀ : ℝ) * δ := by
              have h1 : ϑ u / δ < (k₀ : ℝ) := by dsimp [k₀]; push_cast; exact Int.lt_floor_add_one _
              exact (div_lt_iff₀ hδ_pos).mp h1
            have hlt2 : ((k₀ : ℝ) + 1) * δ < ϑ v := by
              have h1 : (k₀ : ℝ) - 1 ≤ ϑ u / δ := by
                dsimp [k₀]; push_cast; linarith [Int.floor_le (ϑ u / δ)]
              have h2 : ((k₀ : ℝ) - 1) * δ ≤ ϑ u := (le_div_iff₀ hδ_pos).mp h1
              dsimp [δ] at h2 ⊢
              nlinarith
            exact hT_bad_prop ⟨k₀, hk₀_mem⟩ u hu' v hv' ⟨hlt1, hlt2⟩
          rcases hex_k with ⟨k, _, hk_prop⟩
          refine ⟨(k : ℝ) * δ, ((k : ℝ) + 1) * δ, by linarith, ?_⟩
          intro φ hφ T hT
          obtain ⟨u, hu, v, hv, hu_lt, hv_gt⟩ := hk_prop T hT
          have hivt : φ ∈ ϑ '' Set.uIcc u v := by
            apply intermediate_value_uIcc
              (hϑ_cont.mono (fun s hs => by
                rw [Set.mem_uIcc] at hs
                rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · exact ⟨le_trans hT.1 (le_trans hu.1 h1), lt_of_le_of_lt h2 hv.2⟩
                · exact ⟨le_trans hT.1 (le_trans hv.1 h1), lt_of_le_of_lt h2 hu.2⟩))
            rw [Set.mem_uIcc]
            exact Or.inl ⟨(lt_trans hu_lt hφ.1).le, (lt_trans hφ.2 hv_gt).le⟩
          rcases hivt with ⟨t, ht_uicc, ht_eq⟩
          have ht_in : t ∈ Ico T 1 := by
            rw [Set.mem_uIcc] at ht_uicc
            rcases ht_uicc with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact ⟨le_trans hu.1 h1, lt_of_le_of_lt h2 hv.2⟩
            · exact ⟨le_trans hv.1 h1, lt_of_le_of_lt h2 hu.2⟩
          exact ⟨t, ht_in, 0, by simp [ht_eq]⟩
    -- Now use `hex_arc` + `ae_radial_limit_of_injOn_ball` + `holomorphic_zero_at_zero_of_ae_radial_zero_arc`
    rcases hex_arc with ⟨a, b, hab, harc⟩
    have hae_rad := ae_radial_limit_of_injOn_ball hg_holo hg_bij.injOn hM_pos hg_bdd
    have hae_sub : ∀ᵐ φ ∂(MeasureTheory.volume.restrict (Ioo a b)),
        Tendsto (fun ρ : ℝ => g (circleMap 0 ρ φ) - β) (𝓝[<] 1) (𝓝 0) := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hae_rad] with φ ⟨L, hL⟩ hφ_in
      -- Construct sequence `t_n ∈ [T_n, 1)` with `Γ (t_n) = circleMap 0 ‖Γ (t_n)‖ φ`
      let T_seq : ℕ → ℝ := fun n => 1 - (1 - T₀) / ((n : ℝ) + 1)
      have hT_seq_in : ∀ n : ℕ, T_seq n ∈ Ico T₀ 1 := by
        intro n
        have hpos : 0 < (1 - T₀) / ((n : ℝ) + 1) := div_pos (by linarith [hT₀_in.2]) (by positivity)
        have hle : (1 - T₀) / ((n : ℝ) + 1) ≤ 1 - T₀ :=
          div_le_self (by linarith [hT₀_in.2]) (by linarith [Nat.cast_nonneg (α := ℝ) n])
        exact ⟨by dsimp [T_seq]; linarith, by dsimp [T_seq]; linarith⟩
      choose t_seq ht_seq_in m_seq hm_seq using fun n => harc φ hφ_in (T_seq n) (hT_seq_in n)
      have hT_seq_lim : Tendsto T_seq atTop (𝓝 1) := by
        have hdiv : Tendsto (fun n : ℕ => (1 - T₀) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa [T_seq] using (tendsto_const_nhds (x := (1 : ℝ))).sub hdiv
      have ht_seq_lim : Tendsto t_seq atTop (𝓝 1) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le hT_seq_lim tendsto_const_nhds
          (fun n => (ht_seq_in n).1) (fun n => (ht_seq_in n).2.le)
      have ht_seq_lt : Tendsto t_seq atTop (𝓝[<] (1 : ℝ)) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ht_seq_lim
          (Filter.Eventually.of_forall fun n => (ht_seq_in n).2)
      let ρ_seq : ℕ → ℝ := fun n => ‖Γ (t_seq n)‖
      have hρ_seq_lim : Tendsto ρ_seq atTop (𝓝 1) := hnorm_lim.comp ht_seq_lt
      have hρ_seq_lt : Tendsto ρ_seq atTop (𝓝[<] (1 : ℝ)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hρ_seq_lim
          (Filter.Eventually.of_forall fun n => ?_)
        have ht_in01 : t_seq n ∈ Ico (0 : ℝ) 1 :=
          ⟨le_trans hT₀_in.1.le (le_trans (hT_seq_in n).1 (ht_seq_in n).1), (ht_seq_in n).2⟩
        exact mem_ball_zero_iff.mp (hf_bij.mapsTo (hγ_in (t_seq n) ht_in01))
      have hg_eq : ∀ n : ℕ, g (circleMap 0 (ρ_seq n) φ) = γ (t_seq n) := by
        intro n
        have ht_T₀ : t_seq n ∈ Ico T₀ 1 :=
          ⟨le_trans (hT_seq_in n).1 (ht_seq_in n).1, (ht_seq_in n).2⟩
        have ht_01 : t_seq n ∈ Ico (0 : ℝ) 1 := ⟨le_trans hT₀_in.1.le ht_T₀.1, ht_T₀.2⟩
        have hΓ_cm : Γ (t_seq n) = circleMap 0 (ρ_seq n) φ := by
          rw [hϑ_eq (t_seq n) ht_T₀, hm_seq n, circleMap_zero]
          dsimp [ρ_seq]
          congr 1
          have hexp_arg : (((φ + 2 * Real.pi * (m_seq n : ℝ) : ℝ) : ℂ) * Complex.I) =
              (φ : ℂ) * Complex.I + (m_seq n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
            push_cast; ring
          rw [hexp_arg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
        rw [← hΓ_cm]
        exact hgf (γ (t_seq n)) (hγ_in (t_seq n) ht_01)
      have hlim_L : Tendsto (fun n => g (circleMap 0 (ρ_seq n) φ)) atTop (𝓝 L) :=
        hL.comp hρ_seq_lt
      have hlim_β : Tendsto (fun n => g (circleMap 0 (ρ_seq n) φ)) atTop (𝓝 β) := by
        simp_rw [hg_eq]
        exact (hγ_tendsto_Ω.mono_right nhdsWithin_le_nhds).comp ht_seq_lt
      have hL_eq : L = β := tendsto_nhds_unique hlim_L hlim_β
      subst hL_eq
      simpa using hL.sub_const L
    have hh_holo : RudinRCA.Chapter10.HolomorphicOn (fun w => g w - β) (ball (0 : ℂ) 1) :=
      fun w hw => (hg_holo w hw).sub (differentiableAt_const β)
    have hh_bdd : ∀ w ∈ ball (0 : ℂ) 1, ‖g w - β‖ ≤ M + ‖β‖ :=
      fun w hw => (norm_sub_le _ _).trans (add_le_add_left (hg_bdd w hw) ‖β‖)
    have h0_eq : g 0 - β = 0 :=
      holomorphic_zero_at_zero_of_ae_radial_zero_arc hh_holo (by positivity) hh_bdd hab hae_sub
    have hg0_eq : g 0 = β := sub_eq_zero.mp h0_eq
    exact hβ_notΩ (hg0_eq ▸ hg_bij.mapsTo (mem_ball_self zero_lt_one))
  -- Deduce `∃ θ₀ : ℝ, Tendsto ϑ (𝓝[<] 1) (𝓝 θ₀)` from `hϑ_cauchy`
  let s_seq : ℕ → ℝ := fun n => 1 - (1 - T₀) / ((n : ℝ) + 2)
  have hs_in : ∀ n : ℕ, s_seq n ∈ Ico T₀ 1 := by
    intro n
    have hpos : 0 < (1 - T₀) / ((n : ℝ) + 2) := div_pos (by linarith [hT₀_in.2]) (by positivity)
    have hle : (1 - T₀) / ((n : ℝ) + 2) ≤ 1 - T₀ :=
      div_le_self (by linarith [hT₀_in.2]) (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact ⟨by dsimp [s_seq]; linarith, by dsimp [s_seq]; linarith⟩
  have hs_lim : Tendsto s_seq atTop (𝓝 1) := by
    have hdiv : Tendsto (fun n : ℕ => (1 - T₀) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa [s_seq] using (tendsto_const_nhds (x := (1 : ℝ))).sub hdiv
  have hcauchy_seq : CauchySeq (fun n => ϑ (s_seq n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨T, hT, hT_prop⟩ := hϑ_cauchy ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hs_lim (1 - T) (by linarith [hT.2])
    refine ⟨N, fun m hm n hn => ?_⟩
    have hm_in : s_seq m ∈ Ico T 1 := by
      have := hN m hm
      rw [Real.dist_eq, abs_of_neg (by linarith [(hs_in m).2])] at this
      exact ⟨by linarith, (hs_in m).2⟩
    have hn_in : s_seq n ∈ Ico T 1 := by
      have := hN n hn
      rw [Real.dist_eq, abs_of_neg (by linarith [(hs_in n).2])] at this
      exact ⟨by linarith, (hs_in n).2⟩
    rw [Real.dist_eq]
    exact hT_prop (s_seq n) hn_in (s_seq m) hm_in
  obtain ⟨θ₀, hθ₀_seq⟩ := cauchySeq_tendsto_of_complete hcauchy_seq
  have hϑ_lim : Tendsto ϑ (𝓝[<] (1 : ℝ)) (𝓝 θ₀) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨T, hT, hT_prop⟩ := hϑ_cauchy (ε / 2) (half_pos hε)
    obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hs_lim (1 - T) (by linarith [hT.2])
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hθ₀_seq (ε / 2) (half_pos hε)
    let N := max N₁ N₂
    have hsN_in : s_seq N ∈ Ico T 1 := by
      have := hN₁ N (le_max_left N₁ N₂)
      rw [Real.dist_eq, abs_of_neg (by linarith [(hs_in N).2])] at this
      exact ⟨by linarith, (hs_in N).2⟩
    have hsN_close : |ϑ (s_seq N) - θ₀| < ε / 2 := by
      simpa [Real.dist_eq] using hN₂ N (le_max_right N₁ N₂)
    filter_upwards [Ioo_mem_nhdsLT hT.2] with t ht
    have ht_in : t ∈ Ico T 1 := ⟨ht.1.le, ht.2⟩
    have ht_close : |ϑ t - ϑ (s_seq N)| < ε / 2 := hT_prop (s_seq N) hsN_in t ht_in
    rw [Real.dist_eq]
    calc
      |ϑ t - θ₀| = |(ϑ t - ϑ (s_seq N)) + (ϑ (s_seq N) - θ₀)| := by ring_nf
      _ ≤ |ϑ t - ϑ (s_seq N)| + |ϑ (s_seq N) - θ₀| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add ht_close hsN_close
      _ = ε := add_halves ε
  refine ⟨Complex.exp ((θ₀ : ℂ) * Complex.I), Complex.norm_exp_ofReal_mul_I θ₀, ?_⟩
  have hΓ_ev : (fun t : ℝ => ((‖Γ t‖ : ℂ) * Complex.exp ((ϑ t : ℂ) * Complex.I))) =ᶠ[𝓝[<] (1 : ℝ)] Γ := by
    filter_upwards [Ioo_mem_nhdsLT hT₀_in.2] with t ht
    exact (hϑ_eq t ⟨ht.1.le, ht.2⟩).symm
  have hlim_prod : Tendsto (fun t : ℝ => ((‖Γ t‖ : ℂ) * Complex.exp ((ϑ t : ℂ) * Complex.I)))
      (𝓝[<] (1 : ℝ)) (𝓝 (Complex.exp ((θ₀ : ℂ) * Complex.I))) := by
    have h1 : Tendsto (fun t : ℝ => ((‖Γ t‖ : ℝ) : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
      have hc := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hnorm_lim
      rwa [Complex.ofReal_one] at hc
    have h2 : Tendsto (fun t : ℝ => Complex.exp ((ϑ t : ℂ) * Complex.I)) (𝓝[<] (1 : ℝ))
        (𝓝 (Complex.exp ((θ₀ : ℂ) * Complex.I))) :=
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).continuousAt.tendsto.comp hϑ_lim
    simpa using h1.mul h2
  exact hlim_prod.congr' hΓ_ev

/-- **Theorem 14.18(a) (Continuous norm-1 extension at a simple boundary point, RCA pp. 289–290):**
If `Ω` is a bounded open set, `f : Ω → ball 0 1` is a holomorphic bijection, and `β` is a simple
boundary point of `Ω`, then `f` has a unique limit `w_β` of norm `1` along `𝓝[Ω] β` and extends
continuously to `Ω ∪ {β}`. -/
theorem theorem14_18_part_a {Ω : Set ℂ} (hΩ_open : IsOpen Ω)
    (hΩ_bdd : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf_holo : RudinRCA.Chapter10.HolomorphicOn f Ω)
    (hf_bij : BijOn f Ω (ball (0 : ℂ) 1)) {β : ℂ}
    (hsimple : IsSimpleBoundaryPoint Ω β) :
    ∃! w_β : ℂ, ‖w_β‖ = 1 ∧ Tendsto f (𝓝[Ω] β) (𝓝 w_β) ∧
      ∃ F : ℂ → ℂ, EqOn F f Ω ∧ ContinuousOn F (Ω ∪ {β}) ∧ F β = w_β := by
  have hβ_notΩ : β ∉ Ω := by
    have hint : interior Ω = Ω := hΩ_open.interior_eq
    intro hmem
    exact hsimple.1.2 (hint.symm ▸ hmem)
  obtain ⟨α₀, hα₀_in, hα₀_lim⟩ := mem_closure_iff_seq_limit.mp hsimple.1.1
  obtain ⟨γ₀, hγ₀_cont, hγ₀_in, hγ₀_1, t₀, _, ht₀_mem, ht₀_lim, hγ₀_t⟩ :=
    theorem14_16.2 hsimple α₀ hα₀_in hα₀_lim
  obtain ⟨w_β, hw_norm, hw_curve⟩ :=
    lindelof_curve_tendsto hΩ_open hΩ_bdd hf_holo hf_bij hsimple.1 hγ₀_cont hγ₀_in hγ₀_1
  have ht₀_lt : Tendsto t₀ atTop (𝓝[<] (1 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ht₀_lim
      (Filter.Eventually.of_forall fun n => (ht₀_mem n).2)
  have hα₀_f : Tendsto (fun n => f (α₀ n)) atTop (𝓝 w_β) := by
    have heq : (fun n => f (γ₀ (t₀ n))) = fun n => f (α₀ n) := funext fun n => by rw [hγ₀_t n]
    rw [← heq]
    exact hw_curve.comp ht₀_lt
  -- Sequential convergence along ANY sequence `z_n ∈ Ω → β` via interleaving with `α₀`
  have hseq_lim : ∀ z : ℕ → ℂ, (∀ n, z n ∈ Ω) → Tendsto z atTop (𝓝 β) →
      Tendsto (fun n => f (z n)) atTop (𝓝 w_β) := by
    intro z hz_in hz_lim
    let ξ : ℕ → ℂ := fun n => if Even n then α₀ (n / 2) else z (n / 2)
    have hξ_in : ∀ n, ξ n ∈ Ω := by
      intro n; dsimp [ξ]; split_ifs <;> [exact hα₀_in _; exact hz_in _]
    have hξ_lim : Tendsto ξ atTop (𝓝 β) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hα₀_lim ε hε
      obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hz_lim ε hε
      refine ⟨2 * max N₁ N₂ + 2, fun n hn => ?_⟩
      have hdiv : max N₁ N₂ ≤ n / 2 := by omega
      dsimp [ξ]
      split_ifs
      · exact hN₁ (n / 2) (le_trans (le_max_left N₁ N₂) hdiv)
      · exact hN₂ (n / 2) (le_trans (le_max_right N₁ N₂) hdiv)
    obtain ⟨γ, hγ_cont, hγ_in, hγ1, t, _, ht_mem, ht_lim, hγt⟩ :=
      theorem14_16.2 hsimple ξ hξ_in hξ_lim
    obtain ⟨w', _, hw'_curve⟩ :=
      lindelof_curve_tendsto hΩ_open hΩ_bdd hf_holo hf_bij hsimple.1 hγ_cont hγ_in hγ1
    have ht_lt : Tendsto t atTop (𝓝[<] (1 : ℝ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ht_lim
        (Filter.Eventually.of_forall fun n => (ht_mem n).2)
    have hξ_f : Tendsto (fun n => f (ξ n)) atTop (𝓝 w') := by
      have heq : (fun n => f (γ (t n))) = fun n => f (ξ n) := funext fun n => by rw [hγt n]
      rw [← heq]
      exact hw'_curve.comp ht_lt
    have heven_sub : Tendsto (fun k : ℕ => f (ξ (2 * k))) atTop (𝓝 w') :=
      hξ_f.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
    have heven_eq : (fun k : ℕ => f (ξ (2 * k))) = fun k => f (α₀ k) := by
      ext k
      have hev : Even (2 * k) := even_two_mul k
      have hdv : (2 * k) / 2 = k := by omega
      simp [ξ, hev, hdv]
    rw [heven_eq] at heven_sub
    have hw_eq : w' = w_β := tendsto_nhds_unique heven_sub hα₀_f
    subst hw_eq
    have hodd_idx : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
      Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun k hk => by omega⟩
    have hodd_sub : Tendsto (fun k : ℕ => f (ξ (2 * k + 1))) atTop (𝓝 w') :=
      hξ_f.comp hodd_idx
    have hodd_eq : (fun k : ℕ => f (ξ (2 * k + 1))) = fun k => f (z k) := by
      ext k
      have hnev : ¬ Even (2 * k + 1) := by rw [Even]; omega
      have hdv : (2 * k + 1) / 2 = k := by omega
      simp [ξ, hnev, hdv]
    rwa [hodd_eq] at hodd_sub
  -- Upgrade sequential convergence to `Tendsto f (𝓝[Ω] β) (𝓝 w_β)`
  have hnhds_lim : Tendsto f (𝓝[Ω] β) (𝓝 w_β) := by
    by_contra hnot
    rw [Metric.tendsto_nhdsWithin_nhds] at hnot
    have hex_bad : ∃ ε > 0, ∀ δ > 0, ∃ x ∈ Ω, dist x β < δ ∧ ε ≤ dist (f x) w_β := by
      by_contra hno
      apply hnot
      intro ε hε
      by_contra hnoδ
      exact hno ⟨ε, hε, fun δ hδ => by
        by_contra hnox
        exact hnoδ ⟨δ, hδ, fun x hx hdist => lt_of_not_ge fun hge => hnox ⟨x, hx, hdist, hge⟩⟩⟩
    rcases hex_bad with ⟨ε, hε, hbad⟩
    choose z hz_in hz_dist hz_far using fun n : ℕ =>
      hbad (1 / ((n : ℝ) + 1)) (by positivity)
    have hz_lim : Tendsto z atTop (𝓝 β) := by
      rw [Metric.tendsto_atTop]
      intro δ hδ
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
      refine ⟨N, fun n hn => ?_⟩
      refine lt_trans (hz_dist n) ?_
      rw [one_div_lt (by positivity) hδ]
      have : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
      linarith
    have hlim_z := hseq_lim z hz_in hz_lim
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim_z ε hε
    exact not_lt_of_ge (hz_far N) (hN N le_rfl)
  -- Construct explicit continuous extension `F = Function.update f β w_β`
  let F : ℂ → ℂ := Function.update f β w_β
  have hEqOn : EqOn F f Ω := fun z hz =>
    Function.update_of_ne (fun h => hβ_notΩ (by rwa [← h])) w_β f
  have hFβ : F β = w_β := Function.update_self β w_β f
  have hF_cont : ContinuousOn F (Ω ∪ {β}) := by
    intro z hz
    rcases hz with hzΩ | hzβ
    · have h_ev : F =ᶠ[𝓝 z] f := by
        filter_upwards [hΩ_open.mem_nhds hzΩ] with y hy
        exact hEqOn hy
      exact (((hf_holo z hzΩ).continuousAt.congr h_ev.symm)).continuousWithinAt
    · rw [Set.mem_singleton_iff] at hzβ
      subst hzβ
      rw [ContinuousWithinAt, hFβ, Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨δ, hδ_pos, hδ⟩ := Metric.tendsto_nhdsWithin_nhds.mp hnhds_lim ε hε
      refine ⟨δ, hδ_pos, fun y hy hy_dist => ?_⟩
      rcases hy with hyΩ | hyβ
      · rw [hEqOn hyΩ]
        exact hδ hyΩ hy_dist
      · rw [Set.mem_singleton_iff] at hyβ
        rw [hyβ, hFβ, dist_self]
        exact hε
  refine ⟨w_β, ⟨hw_norm, hnhds_lim, F, hEqOn, hF_cont, hFβ⟩, ?_⟩
  intro w' ⟨_, hw'_lim, _⟩
  have : Filter.NeBot (𝓝[Ω] β) := mem_closure_iff_nhdsWithin_neBot.mp hsimple.1.1
  exact tendsto_nhds_unique hw'_lim hnhds_lim

/-- **Theorem 14.18(b) (Distinct simple boundary points have distinct extension values,
RCA p. 290):**
If `Ω` is a bounded open set, `f : Ω → ball 0 1` is a holomorphic bijection, and `β₁, β₂` are
simple boundary points of `Ω` whose extension values agree, then `β₁ = β₂`. -/
theorem theorem14_18_part_b {Ω : Set ℂ} (hΩ_open : IsOpen Ω)
    (hΩ_bdd : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf_holo : RudinRCA.Chapter10.HolomorphicOn f Ω)
    (hf_bij : BijOn f Ω (ball (0 : ℂ) 1)) {β₁ β₂ w₀ : ℂ}
    (hsimple₁ : IsSimpleBoundaryPoint Ω β₁) (hsimple₂ : IsSimpleBoundaryPoint Ω β₂)
    (hw₁ : Tendsto f (𝓝[Ω] β₁) (𝓝 w₀)) (hw₂ : Tendsto f (𝓝[Ω] β₂) (𝓝 w₀)) :
    β₁ = β₂ := by
  by_contra hne
  have hw₀_norm : ‖w₀‖ = 1 := by
    obtain ⟨w₁, ⟨hw₁_norm, hw₁_lim, _⟩, _⟩ :=
      theorem14_18_part_a hΩ_open hΩ_bdd hf_holo hf_bij hsimple₁
    have : Filter.NeBot (𝓝[Ω] β₁) := mem_closure_iff_nhdsWithin_neBot.mp hsimple₁.1.1
    rw [tendsto_nhds_unique hw₁ hw₁_lim]
    exact hw₁_norm
  have hw₀_ne : w₀ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hw₀_norm; norm_num at hw₀_norm
  obtain ⟨g, hg_holo, hg_bij, hgf, _⟩ := (theorem14_7 hΩ_open hf_holo hf_bij).2.1
  obtain ⟨M₀, hM₀⟩ := hΩ_bdd.subset_closedBall (0 : ℂ)
  let M : ℝ := max M₀ 1
  have hM_pos : 0 < M := lt_max_of_lt_right zero_lt_one
  have hg_bdd : ∀ w ∈ ball (0 : ℂ) 1, ‖g w‖ ≤ M := by
    intro w hw
    exact (mem_closedBall_zero_iff.mp (hM₀ (hg_bij.mapsTo hw))).trans (le_max_left M₀ 1)
  -- Pick curves `γ₁ → β₁` and `γ₂ → β₂` in `Ω`
  obtain ⟨α₁, hα₁_in, hα₁_lim⟩ := mem_closure_iff_seq_limit.mp hsimple₁.1.1
  obtain ⟨γ₁, hγ₁_cont, hγ₁_in, hγ₁_1, _⟩ := theorem14_16.2 hsimple₁ α₁ hα₁_in hα₁_lim
  obtain ⟨α₂, hα₂_in, hα₂_lim⟩ := mem_closure_iff_seq_limit.mp hsimple₂.1.1
  obtain ⟨γ₂, hγ₂_cont, hγ₂_in, hγ₂_1, _⟩ := theorem14_16.2 hsimple₂ α₂ hα₂_in hα₂_lim
  have hγ₁_Ω : Tendsto γ₁ (𝓝[<] (1 : ℝ)) (𝓝[Ω] β₁) :=
    tendsto_nhdsWithin_of_curve_Icc hγ₁_cont hγ₁_in hγ₁_1
  have hγ₂_Ω : Tendsto γ₂ (𝓝[<] (1 : ℝ)) (𝓝[Ω] β₂) :=
    tendsto_nhdsWithin_of_curve_Icc hγ₂_cont hγ₂_in hγ₂_1
  have hΓ₁_lim : Tendsto (fun t => f (γ₁ t)) (𝓝[<] (1 : ℝ)) (𝓝 w₀) := hw₁.comp hγ₁_Ω
  have hΓ₂_lim : Tendsto (fun t => f (γ₂ t)) (𝓝[<] (1 : ℝ)) (𝓝 w₀) := hw₂.comp hγ₂_Ω
  -- Choose `T₀ ∈ (0, 1)` separating `γ₁([T₀, 1))` and `γ₂([T₀, 1))` by `ε₀ = ‖β₁ - β₂‖ / 2`
  let ε₀ : ℝ := ‖β₁ - β₂‖ / 2
  have hε₀_pos : 0 < ε₀ := div_pos (norm_sub_pos_iff.mpr hne) two_pos
  have hev_sep : ∀ᶠ t in 𝓝[<] (1 : ℝ),
      t ∈ Ioo (0 : ℝ) 1 ∧ ‖γ₁ t - β₁‖ < ε₀ / 2 ∧ ‖γ₂ t - β₂‖ < ε₀ / 2 := by
    have hc₁ : Tendsto γ₁ (𝓝[<] (1 : ℝ)) (𝓝 β₁) := hγ₁_Ω.mono_right nhdsWithin_le_nhds
    have hc₂ : Tendsto γ₂ (𝓝[<] (1 : ℝ)) (𝓝 β₂) := hγ₂_Ω.mono_right nhdsWithin_le_nhds
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1),
      Metric.tendsto_nhds.mp hc₁ (ε₀ / 2) (half_pos hε₀_pos),
      Metric.tendsto_nhds.mp hc₂ (ε₀ / 2) (half_pos hε₀_pos)] with t ht h₁ h₂
    rw [Complex.dist_eq] at h₁ h₂
    exact ⟨ht, h₁, h₂⟩
  obtain ⟨l₀, hl₀_lt_mem, hl₀_sub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev_sep
  have hl₀_lt : l₀ < 1 := hl₀_lt_mem
  let T₀ : ℝ := (max l₀ 0 + 1) / 2
  have hT₀_in : T₀ ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by dsimp [T₀]; linarith [max_lt hl₀_lt zero_lt_one]⟩
  have hsep : ∀ t₁ ∈ Ico T₀ 1, ∀ t₂ ∈ Ico T₀ 1, ε₀ < ‖γ₁ t₁ - γ₂ t₂‖ := by
    intro t₁ ht₁ t₂ ht₂
    have hmax_lt : max l₀ 0 < T₀ := by dsimp [T₀]; linarith [max_lt hl₀_lt zero_lt_one]
    have h₁ := (hl₀_sub ⟨lt_of_le_of_lt (le_max_left l₀ 0) (lt_of_lt_of_le hmax_lt ht₁.1), ht₁.2⟩).2.1
    have h₂ := (hl₀_sub ⟨lt_of_le_of_lt (le_max_left l₀ 0) (lt_of_lt_of_le hmax_lt ht₂.1), ht₂.2⟩).2.2
    have htri : ‖β₁ - β₂‖ ≤ ‖β₁ - γ₁ t₁‖ + ‖γ₁ t₁ - γ₂ t₂‖ + ‖γ₂ t₂ - β₂‖ := by
      calc
        ‖β₁ - β₂‖ = ‖(β₁ - γ₁ t₁) + (γ₁ t₁ - γ₂ t₂) + (γ₂ t₂ - β₂)‖ := by ring_nf
        _ ≤ ‖(β₁ - γ₁ t₁) + (γ₁ t₁ - γ₂ t₂)‖ + ‖γ₂ t₂ - β₂‖ := norm_add_le _ _
        _ ≤ ‖β₁ - γ₁ t₁‖ + ‖γ₁ t₁ - γ₂ t₂‖ + ‖γ₂ t₂ - β₂‖ :=
          add_le_add_left (norm_add_le _ _) _
    rw [norm_sub_rev β₁ (γ₁ t₁)] at htri
    dsimp [ε₀] at h₁ h₂ ⊢
    linarith
  -- Radius bound `d₀` for circular arcs around `w₀`
  let d₁ : ℝ := ‖f (γ₁ T₀) - w₀‖
  let d₂ : ℝ := ‖f (γ₂ T₀) - w₀‖
  have hd₁_pos : 0 < d₁ := by
    apply norm_sub_pos_iff.mpr
    intro heq
    have hlt : ‖f (γ₁ T₀)‖ < 1 :=
      mem_ball_zero_iff.mp (hf_bij.mapsTo (hγ₁_in T₀ ⟨hT₀_in.1.le, hT₀_in.2⟩))
    rw [heq, hw₀_norm] at hlt
    exact lt_irrefl 1 hlt
  have hd₂_pos : 0 < d₂ := by
    apply norm_sub_pos_iff.mpr
    intro heq
    have hlt : ‖f (γ₂ T₀)‖ < 1 :=
      mem_ball_zero_iff.mp (hf_bij.mapsTo (hγ₂_in T₀ ⟨hT₀_in.1.le, hT₀_in.2⟩))
    rw [heq, hw₀_norm] at hlt
    exact lt_irrefl 1 hlt
  let d₀ : ℝ := min (min d₁ d₂) 1
  have hd₀_pos : 0 < d₀ := lt_min (lt_min hd₁_pos hd₂_pos) zero_lt_one
  have hd₀_le1 : d₀ ≤ 1 := min_le_right _ _
  -- Shift `w₀` to `0` via `g̃(z) = g(w₀ * (1 - z))` on `D = {z | ‖1 - z‖ < 1}`
  let D : Set ℂ := {z : ℂ | ‖1 - z‖ < 1}
  have hD_open : IsOpen D :=
    isOpen_lt (continuous_norm.comp (continuous_const.sub continuous_id)) continuous_const
  let g_shift : ℂ → ℂ := fun z => g (w₀ * (1 - z))
  have hmaps_D : MapsTo (fun z : ℂ => w₀ * (1 - z)) D (ball (0 : ℂ) 1) := by
    intro z hz
    rw [mem_ball_zero_iff, norm_mul, hw₀_norm, one_mul]
    exact hz
  have hg_shift_holo : RudinRCA.Chapter10.HolomorphicOn g_shift D :=
    fun z hz => (hg_holo _ (hmaps_D hz)).comp z
      ((differentiableAt_const (1 : ℂ) |>.sub differentiableAt_id).const_mul w₀)
  have hg_shift_inj : InjOn g_shift D := by
    intro z₁ hz₁ z₂ hz₂ heq
    have hw_eq := hg_bij.injOn (hmaps_D hz₁) (hmaps_D hz₂) heq
    have hsub_eq := mul_left_cancel₀ hw₀_ne hw_eq
    linear_combination -hsub_eq
  have hg_shift_bdd : ∀ z ∈ D, ‖g_shift z‖ ≤ M := fun z hz => hg_bdd _ (hmaps_D hz)
  have harea := lintegral_polar_deriv_sq_le_of_injOn hD_open hg_shift_holo hg_shift_inj hM_pos hg_shift_bdd
  -- Key circular-arc lower bound for every `ρ ∈ (0, d₀)`
  have harc_lower : ∀ ρ ∈ Ioo (0 : ℝ) d₀,
      ENNReal.ofReal (ε₀ ^ 2 / (Real.pi * ρ)) ≤
        ∫⁻ θ in Ioo (-Real.pi) Real.pi,
          (D \ {0}).indicator (fun z => ENNReal.ofReal (‖deriv g_shift z‖ ^ 2))
            (Complex.polarCoord.symm (ρ, θ)) * ENNReal.ofReal ρ ∂MeasureTheory.volume := by
    intro ρ hρ
    have hρ_pos : 0 < ρ := hρ.1
    have hρ_lt1 : ρ < 1 := lt_of_lt_of_le hρ.2 hd₀_le1
    let φ_ρ : ℝ := Real.arccos (ρ / 2)
    have hφ_pos : 0 < φ_ρ := Real.arccos_pos.mpr (by linarith)
    have hφ_lt_half : φ_ρ < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr (by positivity)
    -- `circleMap 0 ρ θ ∈ D` iff `ρ / 2 < Real.cos θ`
    have hcm_norm_sq : ∀ θ : ℝ, ‖1 - circleMap 0 ρ θ‖ ^ 2 = 1 + ρ ^ 2 - 2 * ρ * Real.cos θ := by
      intro θ
      rw [circleMap_zero, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Complex.sq_norm, Complex.normSq_apply]
      have hsc : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      nlinarith
    have hcm_in_D : ∀ θ ∈ Ioo (-φ_ρ) φ_ρ, circleMap 0 ρ θ ∈ D \ {0} := by
      intro θ hθ
      have habs_lt : |θ| < φ_ρ := abs_lt.mpr hθ
      have hcos_gt : ρ / 2 < Real.cos θ := by
        have h1 : Real.cos φ_ρ < Real.cos |θ| :=
          Real.strictAntiOn_cos ⟨abs_nonneg θ, le_trans habs_lt.le (by linarith [Real.pi_pos])⟩
            ⟨hφ_pos.le, by linarith [Real.pi_pos]⟩ habs_lt
        rw [Real.cos_abs] at h1
        rwa [Real.cos_arccos (by linarith) (by linarith)] at h1
      have hsq_lt : ‖1 - circleMap 0 ρ θ‖ ^ 2 < 1 := by
        rw [hcm_norm_sq]; nlinarith
      have hlt1 : ‖1 - circleMap 0 ρ θ‖ < 1 := by
        nlinarith [norm_nonneg (1 - circleMap 0 ρ θ)]
      refine ⟨hlt1, ?_⟩
      intro h0
      rw [Set.mem_singleton_iff] at h0
      have hn : ‖circleMap 0 ρ θ‖ = ρ := by rw [norm_circleMap_zero, abs_of_pos hρ_pos]
      rw [h0, norm_zero] at hn
      linarith
    -- Find `t₁, t₂ ∈ [T₀, 1)` where `‖f (γ_i t_i) - w₀‖ = ρ`
    have hex_hit : ∀ (γ : ℝ → ℂ), ContinuousOn γ (Icc (0 : ℝ) 1) →
        (∀ s ∈ Ico (0 : ℝ) 1, γ s ∈ Ω) →
        Tendsto (fun t => f (γ t)) (𝓝[<] (1 : ℝ)) (𝓝 w₀) →
        ρ < ‖f (γ T₀) - w₀‖ →
        ∃ t ∈ Ico T₀ 1, ∃ θ ∈ Ioo (-φ_ρ) φ_ρ, g_shift (circleMap 0 ρ θ) = γ t := by
      intro γ hγ_c hγ_Ω hΓ_w₀ hgt_T₀
      have hev_lt : ∀ᶠ s in 𝓝[<] (1 : ℝ), s ∈ Ioo T₀ 1 ∧ ‖f (γ s) - w₀‖ < ρ := by
        filter_upwards [Ioo_mem_nhdsLT hT₀_in.2, Metric.tendsto_nhds.mp hΓ_w₀ ρ hρ_pos] with s hs₁ hs₂
        rw [Complex.dist_eq] at hs₂
        exact ⟨hs₁, hs₂⟩
      obtain ⟨s₁, hs₁_in, hs₁_lt⟩ := hev_lt.exists
      have hcont_dist : ContinuousOn (fun s => ‖f (γ s) - w₀‖) (Icc T₀ s₁) := by
        have hfγ_cont : ContinuousOn (fun s => f (γ s)) (Icc T₀ s₁) :=
          (RudinRCA.Chapter10.continuousOn_of_holomorphicOn hf_holo).comp
            (hγ_c.mono (fun s hs => ⟨le_trans hT₀_in.1.le hs.1, le_trans hs.2 hs₁_in.2.le⟩))
            (fun s hs => hγ_Ω s ⟨le_trans hT₀_in.1.le hs.1, lt_of_le_of_lt hs.2 hs₁_in.2⟩)
        exact continuous_norm.comp_continuousOn (hfγ_cont.sub continuousOn_const)
      have hivt : ρ ∈ (fun s => ‖f (γ s) - w₀‖) '' Icc T₀ s₁ :=
        intermediate_value_Icc' hs₁_in.1.le hcont_dist ⟨hs₁_lt.le, hgt_T₀.le⟩
      rcases hivt with ⟨t, ht_icc, ht_eq⟩
      have ht_in : t ∈ Ico T₀ 1 := ⟨ht_icc.1, lt_of_le_of_lt ht_icc.2 hs₁_in.2⟩
      let w : ℂ := f (γ t)
      have hw_ball : w ∈ ball (0 : ℂ) 1 :=
        hf_bij.mapsTo (hγ_Ω t ⟨le_trans hT₀_in.1.le ht_in.1, ht_in.2⟩)
      let z : ℂ := 1 - w / w₀
      have hmul_z : w₀ * (1 - z) = w := by
        dsimp [z]; field_simp [hw₀_ne]; ring
      have hz_norm : ‖z‖ = ρ := by
        have : w₀ * z = w₀ - w := by dsimp [z]; field_simp [hw₀_ne]
        have hn : ‖w₀ * z‖ = ‖w - w₀‖ := (congrArg norm this).trans (norm_sub_rev w₀ w)
        rw [norm_mul, hw₀_norm, one_mul] at hn
        exact hn.trans ht_eq
      have h1z_lt : ‖1 - z‖ < 1 := by
        have : 1 - z = w / w₀ := by dsimp [z]; ring
        rw [this, norm_div, hw₀_norm, div_one]
        exact mem_ball_zero_iff.mp hw_ball
      let θ : ℝ := Complex.arg z
      have hcm_z : circleMap 0 ρ θ = z := by
        rw [circleMap_zero, ← hz_norm]
        exact Complex.norm_mul_exp_arg_mul_I z
      have hθ_in : θ ∈ Ioo (-φ_ρ) φ_ρ := by
        have hsq_lt : ‖1 - circleMap 0 ρ θ‖ ^ 2 < 1 := by
          rw [hcm_z]; nlinarith [norm_nonneg (1 - z)]
        rw [hcm_norm_sq] at hsq_lt
        have hcos_gt : ρ / 2 < Real.cos θ := by nlinarith
        have habs_le : |θ| ≤ Real.pi := abs_le.mpr ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
        have habs_lt : |θ| < φ_ρ := by
          by_contra hge
          have hcos_le : Real.cos |θ| ≤ Real.cos φ_ρ :=
            Real.strictAntiOn_cos.antitoneOn ⟨hφ_pos.le, by linarith [Real.pi_pos]⟩
              ⟨abs_nonneg θ, habs_le⟩ (not_lt.mp hge)
          rw [Real.cos_abs, Real.cos_arccos (by linarith) (by linarith)] at hcos_le
          linarith
        exact abs_lt.mp habs_lt
      refine ⟨t, ht_in, θ, hθ_in, ?_⟩
      dsimp [g_shift]
      rw [hcm_z, hmul_z]
      exact hgf (γ t) (hγ_Ω t ⟨le_trans hT₀_in.1.le ht_in.1, ht_in.2⟩)
    have hd₁_gt : ρ < d₁ := lt_of_lt_of_le hρ.2 (le_trans (min_le_left _ _) (min_le_left _ _))
    have hd₂_gt : ρ < d₂ := lt_of_lt_of_le hρ.2 (le_trans (min_le_left _ _) (min_le_right _ _))
    obtain ⟨t₁, ht₁, θ₁, hθ₁, hg₁⟩ := hex_hit γ₁ hγ₁_cont hγ₁_in hΓ₁_lim hd₁_gt
    obtain ⟨t₂, ht₂, θ₂, hθ₂, hg₂⟩ := hex_hit γ₂ hγ₂_cont hγ₂_in hΓ₂_lim hd₂_gt
    -- Bound `ε₀` by the arc-length integral over `[min θ₁ θ₂, max θ₁ θ₂] ⊆ (-φ_ρ, φ_ρ)`
    let a_θ : ℝ := min θ₁ θ₂
    let b_θ : ℝ := max θ₁ θ₂
    have hab_le : a_θ ≤ b_θ := min_le_max
    have hab_sub : Icc a_θ b_θ ⊆ Ioo (-φ_ρ) φ_ρ := fun θ hθ =>
      ⟨lt_of_lt_of_le (lt_min hθ₁.1 hθ₂.1) hθ.1, lt_of_le_of_lt hθ.2 (max_lt hθ₁.2 hθ₂.2)⟩
    have hsep_ab : ε₀ < ‖g_shift (circleMap 0 ρ b_θ) - g_shift (circleMap 0 ρ a_θ)‖ := by
      dsimp [a_θ, b_θ]
      rcases le_total θ₁ θ₂ with hle | hle
      · rw [min_eq_left hle, max_eq_right hle, hg₁, hg₂, norm_sub_rev]
        exact hsep t₁ ht₁ t₂ ht₂
      · rw [min_eq_right hle, max_eq_left hle, hg₁, hg₂]
        exact hsep t₁ ht₁ t₂ ht₂
    let u_arc : ℝ → ℂ := fun θ =>
      deriv g_shift (circleMap 0 ρ θ) * (deriv (circleMap 0 ρ) θ)
    have hderiv_arc : ∀ θ ∈ Set.uIcc a_θ b_θ,
        HasDerivAt (fun s => g_shift (circleMap 0 ρ s)) (u_arc θ) θ := by
      intro θ hθ_u
      rw [Set.uIcc_of_le hab_le] at hθ_u
      have hcm_in : circleMap 0 ρ θ ∈ D := (hcm_in_D θ (hab_sub hθ_u)).1
      have hd_cm : HasDerivAt (circleMap 0 ρ) (deriv (circleMap 0 ρ) θ) θ := by
        rw [deriv_circleMap]
        exact hasDerivAt_circleMap 0 ρ θ
      exact HasDerivAt.comp (h₂ := g_shift) (h := circleMap 0 ρ) θ
        (hg_shift_holo _ hcm_in).hasDerivAt hd_cm
    have hnorm_u : ∀ θ : ℝ, ‖u_arc θ‖ = ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖ := by
      intro θ
      dsimp [u_arc]
      rw [norm_mul, deriv_circleMap, norm_mul, norm_circleMap_zero, abs_of_pos hρ_pos,
        Complex.norm_I, mul_one, mul_comm]
    have hdg_holo := RudinRCA.Chapter10.holomorphicOn_deriv hD_open hg_shift_holo
    have hcont_norm_u : ContinuousOn (fun θ => ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖) (Icc a_θ b_θ) := by
      refine continuousOn_const.mul (continuous_norm.comp_continuousOn ?_)
      exact (RudinRCA.Chapter10.continuousOn_of_holomorphicOn hdg_holo).comp
        (continuous_circleMap 0 ρ).continuousOn fun θ hθ => (hcm_in_D θ (hab_sub hθ)).1
    have hint_u : IntervalIntegrable u_arc MeasureTheory.volume a_θ b_θ := by
      apply ContinuousOn.intervalIntegrable_of_Icc hab_le
      refine ContinuousOn.mul ?_ ?_
      · exact (RudinRCA.Chapter10.continuousOn_of_holomorphicOn hdg_holo).comp
          (continuous_circleMap 0 ρ).continuousOn fun θ hθ => (hcm_in_D θ (hab_sub hθ)).1
      · have h_eq : deriv (circleMap 0 ρ) = fun θ => circleMap 0 ρ θ * Complex.I :=
          funext (deriv_circleMap 0 ρ)
        rw [h_eq]
        exact ((continuous_circleMap 0 ρ).mul continuous_const).continuousOn
    have hε₀_le_int : ε₀ ≤ ∫ θ in a_θ..b_θ, ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖ := by
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_arc hint_u
      calc
        ε₀ ≤ ‖g_shift (circleMap 0 ρ b_θ) - g_shift (circleMap 0 ρ a_θ)‖ := hsep_ab.le
        _ = ‖∫ θ in a_θ..b_θ, u_arc θ‖ := by rw [hftc]
        _ ≤ ∫ θ in a_θ..b_θ, ‖u_arc θ‖ := intervalIntegral.norm_integral_le_integral_norm hab_le
        _ = ∫ θ in a_θ..b_θ, ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖ := by simp_rw [hnorm_u]
    have hε₀_le_lint : ENNReal.ofReal ε₀ ≤
        ∫⁻ θ in Ioo (-φ_ρ) φ_ρ,
          ENNReal.ofReal (ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖) ∂MeasureTheory.volume := by
      have hint_on : MeasureTheory.IntegrableOn (fun θ => ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖)
          (Ioc a_θ b_θ) MeasureTheory.volume :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hab_le).mp
          (hcont_norm_u.intervalIntegrable_of_Icc hab_le)
      have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Ioc a_θ b_θ)]
          fun θ => ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖ :=
        Filter.Eventually.of_forall fun _ => mul_nonneg hρ_pos.le (norm_nonneg _)
      calc
        ENNReal.ofReal ε₀
            ≤ ENNReal.ofReal (∫ θ in a_θ..b_θ, ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖) :=
              ENNReal.ofReal_le_ofReal hε₀_le_int
        _ = ∫⁻ θ in Ioc a_θ b_θ,
              ENNReal.ofReal (ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖) ∂MeasureTheory.volume := by
              rw [intervalIntegral.integral_of_le hab_le,
                MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_on hnonneg]
        _ ≤ ∫⁻ θ in Ioo (-φ_ρ) φ_ρ,
              ENNReal.ofReal (ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖) ∂MeasureTheory.volume :=
              MeasureTheory.lintegral_mono'
                (MeasureTheory.Measure.restrict_mono
                  (fun θ hθ => hab_sub ⟨hθ.1.le, hθ.2⟩) le_rfl) le_rfl
    -- Apply pointwise `2 c (ρ x) ≤ ρ c^2 + ρ x^2` with `c = ε₀ / (π * ρ)` on `Ioo (-φ_ρ) φ_ρ`
    let c : ℝ := ε₀ / (Real.pi * ρ)
    have hc_pos : 0 < c := div_pos hε₀_pos (mul_pos Real.pi_pos hρ_pos)
    have hpt_amgm : ∀ θ ∈ Ioo (-φ_ρ) φ_ρ,
        ENNReal.ofReal (2 * c) * ENNReal.ofReal (ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖) ≤
          ENNReal.ofReal (ρ * c ^ 2) +
            ENNReal.ofReal (ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖ ^ 2) := by
      intro θ _
      rw [← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (mul_nonneg hρ_pos.le (sq_nonneg _))]
      apply ENNReal.ofReal_le_ofReal
      set x : ℝ := ‖deriv g_shift (circleMap 0 ρ θ)‖
      have hsq : 0 ≤ ρ * (x - c) ^ 2 := mul_nonneg hρ_pos.le (sq_nonneg _)
      linarith
    have hsum_ineq : ENNReal.ofReal (2 * ε₀ ^ 2 / (Real.pi * ρ)) ≤
        ENNReal.ofReal (ε₀ ^ 2 / (Real.pi * ρ)) +
          ∫⁻ θ in Ioo (-φ_ρ) φ_ρ,
            ENNReal.ofReal (ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖ ^ 2) ∂MeasureTheory.volume := by
      have h1 : ENNReal.ofReal (2 * ε₀ ^ 2 / (Real.pi * ρ)) =
          ENNReal.ofReal (2 * c) * ENNReal.ofReal ε₀ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1; dsimp [c]; field_simp [Real.pi_pos.ne', hρ_pos.ne']
      have hconst_eval : (∫⁻ _θ in Ioo (-φ_ρ) φ_ρ, ENNReal.ofReal (ρ * c ^ 2) ∂MeasureTheory.volume) ≤
          ENNReal.ofReal (ε₀ ^ 2 / (Real.pi * ρ)) := by
        rw [MeasureTheory.setLIntegral_const, Real.volume_Ioo, sub_neg_eq_add,
          ← two_mul, mul_comm, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hlen : 2 * φ_ρ ≤ Real.pi := by linarith
        calc
          2 * φ_ρ * (ρ * c ^ 2) ≤ Real.pi * (ρ * c ^ 2) :=
            mul_le_mul_of_nonneg_right hlen (by positivity)
          _ = ε₀ ^ 2 / (Real.pi * ρ) := by
            dsimp [c]; field_simp [Real.pi_pos.ne', hρ_pos.ne']
      calc
        ENNReal.ofReal (2 * ε₀ ^ 2 / (Real.pi * ρ))
            = ENNReal.ofReal (2 * c) * ENNReal.ofReal ε₀ := h1
        _ ≤ ENNReal.ofReal (2 * c) *
              ∫⁻ θ in Ioo (-φ_ρ) φ_ρ,
                ENNReal.ofReal (ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖) ∂MeasureTheory.volume :=
              mul_le_mul_right hε₀_le_lint _
        _ = ∫⁻ θ in Ioo (-φ_ρ) φ_ρ,
              ENNReal.ofReal (2 * c) *
                ENNReal.ofReal (ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖) ∂MeasureTheory.volume := by
              rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
        _ ≤ ∫⁻ θ in Ioo (-φ_ρ) φ_ρ,
              (ENNReal.ofReal (ρ * c ^ 2) +
                ENNReal.ofReal (ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖ ^ 2)) ∂MeasureTheory.volume :=
              MeasureTheory.setLIntegral_mono' (μ := MeasureTheory.volume) measurableSet_Ioo hpt_amgm
        _ = (∫⁻ _θ in Ioo (-φ_ρ) φ_ρ, ENNReal.ofReal (ρ * c ^ 2) ∂MeasureTheory.volume) +
              ∫⁻ θ in Ioo (-φ_ρ) φ_ρ,
                ENNReal.ofReal (ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖ ^ 2) ∂MeasureTheory.volume :=
              MeasureTheory.lintegral_add_left'
                (aemeasurable_const (b := ENNReal.ofReal (ρ * c ^ 2))) _
        _ ≤ ENNReal.ofReal (ε₀ ^ 2 / (Real.pi * ρ)) +
              ∫⁻ θ in Ioo (-φ_ρ) φ_ρ,
                ENNReal.ofReal (ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖ ^ 2) ∂MeasureTheory.volume :=
              add_le_add_left hconst_eval _
    have h2_split : ENNReal.ofReal (2 * ε₀ ^ 2 / (Real.pi * ρ)) =
        ENNReal.ofReal (ε₀ ^ 2 / (Real.pi * ρ)) + ENNReal.ofReal (ε₀ ^ 2 / (Real.pi * ρ)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring
    rw [h2_split] at hsum_ineq
    have hsq_lower : ENNReal.ofReal (ε₀ ^ 2 / (Real.pi * ρ)) ≤
        ∫⁻ θ in Ioo (-φ_ρ) φ_ρ,
          ENNReal.ofReal (ρ * ‖deriv g_shift (circleMap 0 ρ θ)‖ ^ 2) ∂MeasureTheory.volume :=
      (ENNReal.add_le_add_iff_left ENNReal.ofReal_lt_top.ne).mp hsum_ineq
    refine hsq_lower.trans ?_
    have hφ_sub : Ioo (-φ_ρ) φ_ρ ⊆ Ioo (-Real.pi) Real.pi :=
      Ioo_subset_Ioo (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    refine le_trans ?_
      (MeasureTheory.lintegral_mono' (MeasureTheory.Measure.restrict_mono hφ_sub le_rfl) le_rfl)
    refine MeasureTheory.setLIntegral_mono' (μ := MeasureTheory.volume) measurableSet_Ioo fun θ hθ => ?_
    have hpolar_eq : Complex.polarCoord.symm (ρ, θ) = circleMap 0 ρ θ := by
      rw [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I,
        Complex.ofReal_cos, Complex.ofReal_sin]
    rw [hpolar_eq, Set.indicator_of_mem (hcm_in_D θ hθ), ENNReal.ofReal_mul hρ_pos.le, mul_comm]
  -- Integrate `harc_lower` over `ρ ∈ Ioo δ d₀` for an explicit small `δ > 0` to exceed `π M^2`
  let K_exp : ℝ := Real.pi ^ 2 * M ^ 2 / ε₀ ^ 2 + 1
  have hK_pos : 0 < K_exp := by positivity
  let δ : ℝ := d₀ * Real.exp (-K_exp)
  have hδ_pos : 0 < δ := mul_pos hd₀_pos (Real.exp_pos _)
  have hδ_lt : δ < d₀ := by
    have hexp_lt : Real.exp (-K_exp) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    nlinarith
  have hlog_eval : (∫⁻ ρ in Ioo δ d₀, ENNReal.ofReal (ε₀ ^ 2 / (Real.pi * ρ)) ∂MeasureTheory.volume) =
      ENNReal.ofReal ((ε₀ ^ 2 / Real.pi) * K_exp) := by
    have hcont_inv : ContinuousOn (fun ρ : ℝ => ε₀ ^ 2 / (Real.pi * ρ)) (Icc δ d₀) :=
      continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun ρ hρ =>
        (mul_pos Real.pi_pos (lt_of_lt_of_le hδ_pos hρ.1)).ne'
    have hint_on : MeasureTheory.IntegrableOn (fun ρ : ℝ => ε₀ ^ 2 / (Real.pi * ρ))
        (Ioc δ d₀) MeasureTheory.volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ_lt.le).mp
        (hcont_inv.intervalIntegrable_of_Icc hδ_lt.le)
    have hnonneg' : 0 ≤ᵐ[MeasureTheory.volume.restrict (Ioc δ d₀)]
        fun ρ : ℝ => ε₀ ^ 2 / (Real.pi * ρ) := by
      rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun ρ hρ => ?_
      have hρ0 : 0 < ρ := lt_trans hδ_pos hρ.1
      exact div_nonneg (sq_nonneg _) (mul_nonneg Real.pi_pos.le hρ0.le)
    have hftc : (∫ ρ in δ..d₀, ε₀ ^ 2 / (Real.pi * ρ)) = (ε₀ ^ 2 / Real.pi) * K_exp := by
      have hderiv_log : ∀ ρ ∈ Set.uIcc δ d₀,
          HasDerivAt (fun s : ℝ => (ε₀ ^ 2 / Real.pi) * Real.log s) (ε₀ ^ 2 / (Real.pi * ρ)) ρ := by
        intro ρ hρ
        rw [Set.uIcc_of_le hδ_lt.le] at hρ
        have hρ0 : 0 < ρ := lt_of_lt_of_le hδ_pos hρ.1
        have hd := (Real.hasDerivAt_log hρ0.ne').const_mul (ε₀ ^ 2 / Real.pi)
        refine hd.congr_deriv ?_
        field_simp [Real.pi_pos.ne', hρ0.ne']
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_log
        (hcont_inv.intervalIntegrable_of_Icc hδ_lt.le)]
      have hlog_δ : Real.log δ = Real.log d₀ - K_exp := by
        dsimp [δ]
        rw [Real.log_mul hd₀_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
        ring
      rw [hlog_δ]; ring
    rw [MeasureTheory.setLIntegral_congr MeasureTheory.Ioo_ae_eq_Ioc,
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_on hnonneg',
      ← intervalIntegral.integral_of_le hδ_lt.le, hftc]
  -- Compare with `harea` via Tonelli on `Ioo δ d₀ ×ˢ Ioo (-π) π ⊆ polarCoord.target`
  let f_polar : ℝ × ℝ → ENNReal := fun p =>
    (D \ {0}).indicator (fun z => ENNReal.ofReal (‖deriv g_shift z‖ ^ 2))
      (Complex.polarCoord.symm p) * ENNReal.ofReal p.1
  have hf_polar_meas : Measurable f_polar := by
    let q : ℂ → ENNReal := fun z => ENNReal.ofReal (‖deriv g_shift z‖ ^ 2)
    have hq_cont : ContinuousOn q (D \ {0}) :=
      ENNReal.continuous_ofReal.comp_continuousOn
        ((continuous_norm.comp_continuousOn
          ((RudinRCA.Chapter10.continuousOn_of_holomorphicOn
            (RudinRCA.Chapter10.holomorphicOn_deriv hD_open hg_shift_holo)).mono
              Set.sdiff_subset)).pow 2)
    have hind_meas : Measurable ((D \ {0}).indicator q) := by
      rw [← Set.piecewise_eq_indicator]
      exact hq_cont.measurable_piecewise continuousOn_const
        (hD_open.sdiff isClosed_singleton).measurableSet
    have hsymm_cont : Continuous (fun p : ℝ × ℝ => (Complex.polarCoord.symm p : ℂ)) := by
      have h_eq : (fun p : ℝ × ℝ => (Complex.polarCoord.symm p : ℂ)) =
          fun p => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) :=
        funext Complex.polarCoord_symm_apply
      rw [h_eq]
      exact (Complex.continuous_ofReal.comp continuous_fst).mul
        ((Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_snd)).add
          ((Complex.continuous_ofReal.comp (Real.continuous_sin.comp continuous_snd)).mul
            continuous_const))
    exact (hind_meas.comp hsymm_cont.measurable).mul
      (ENNReal.continuous_ofReal.comp continuous_fst).measurable
  have hsub_target : Ioo δ d₀ ×ˢ Ioo (-Real.pi) Real.pi ⊆ _root_.polarCoord.target := by
    rw [polarCoord_target]
    exact prod_mono (fun ρ hρ => lt_trans hδ_pos hρ.1) Subset.rfl
  have hiter_le : ENNReal.ofReal ((ε₀ ^ 2 / Real.pi) * K_exp) ≤ ENNReal.ofReal (Real.pi * M ^ 2) := by
    rw [← hlog_eval]
    calc
      (∫⁻ ρ in Ioo δ d₀, ENNReal.ofReal (ε₀ ^ 2 / (Real.pi * ρ)) ∂MeasureTheory.volume)
          ≤ ∫⁻ ρ in Ioo δ d₀,
              (∫⁻ θ in Ioo (-Real.pi) Real.pi, f_polar (ρ, θ) ∂MeasureTheory.volume)
              ∂MeasureTheory.volume := by
            refine MeasureTheory.setLIntegral_mono' (μ := MeasureTheory.volume) measurableSet_Ioo
              fun ρ hρ => harc_lower ρ ⟨lt_trans hδ_pos hρ.1, hρ.2⟩
      _ = ∫⁻ p in Ioo δ d₀ ×ˢ Ioo (-Real.pi) Real.pi, f_polar p ∂MeasureTheory.volume := by
            rw [MeasureTheory.Measure.volume_eq_prod]
            exact (MeasureTheory.setLIntegral_prod f_polar hf_polar_meas.aemeasurable).symm
      _ ≤ ∫⁻ p in _root_.polarCoord.target, f_polar p ∂MeasureTheory.volume :=
            MeasureTheory.lintegral_mono'
              (MeasureTheory.Measure.restrict_mono hsub_target le_rfl) le_rfl
      _ ≤ ENNReal.ofReal (Real.pi * M ^ 2) := harea
  have hreal_le : (ε₀ ^ 2 / Real.pi) * K_exp ≤ Real.pi * M ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hiter_le
  have hreal_gt : Real.pi * M ^ 2 < (ε₀ ^ 2 / Real.pi) * K_exp := by
    have hcalc : (ε₀ ^ 2 / Real.pi) * K_exp = Real.pi * M ^ 2 + ε₀ ^ 2 / Real.pi := by
      dsimp [K_exp]
      field_simp [Real.pi_pos.ne', hε₀_pos.ne']
    rw [hcalc]
    linarith [div_pos (sq_pos_of_pos hε₀_pos) Real.pi_pos]
  linarith

/-- **Theorem 14.18 (Continuous norm-1 boundary extension and injectivity at simple boundary
points, RCA pp. 289–290):**
Let `Ω` be a bounded simply connected region and `f : Ω → ball 0 1` a holomorphic bijection.
1. **(a)** At each simple boundary point `β` of `Ω`, `f` extends continuously to `Ω ∪ {β}` (and
   equivalently has a limit `w_β` along `𝓝[Ω] β`), and its extension value at `β` has norm `1`.
2. **(b)** If `β₁, β₂` are distinct simple boundary points of `Ω`, the extension values of `f` at
   `β₁` and `β₂` are distinct. -/
theorem theorem14_18 {Ω : Set ℂ} (hΩ_sc : RudinRCA.Chapter10.BookSimplyConnected Ω)
    (hΩ_bdd : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf_holo : RudinRCA.Chapter10.HolomorphicOn f Ω)
    (hf_bij : BijOn f Ω (ball (0 : ℂ) 1)) :
    (∀ {β : ℂ}, IsSimpleBoundaryPoint Ω β →
      ∃! w_β : ℂ, ‖w_β‖ = 1 ∧ Tendsto f (𝓝[Ω] β) (𝓝 w_β) ∧
        ∃ F : ℂ → ℂ, EqOn F f Ω ∧ ContinuousOn F (Ω ∪ {β}) ∧ F β = w_β) ∧
    (∀ {β₁ β₂ : ℂ} {F₁ F₂ : ℂ → ℂ},
      IsSimpleBoundaryPoint Ω β₁ → IsSimpleBoundaryPoint Ω β₂ → β₁ ≠ β₂ →
      EqOn F₁ f Ω → ContinuousOn F₁ (Ω ∪ {β₁}) →
      EqOn F₂ f Ω → ContinuousOn F₂ (Ω ∪ {β₂}) →
      F₁ β₁ ≠ F₂ β₂) := by
  have hΩ_open : IsOpen Ω := hΩ_sc.1.1
  refine ⟨fun hsimple => theorem14_18_part_a hΩ_open hΩ_bdd hf_holo hf_bij hsimple, ?_⟩
  intro β₁ β₂ F₁ F₂ hs₁ hs₂ hne hEq₁ hCont₁ hEq₂ hCont₂ heq_val
  have hlim₁ : Tendsto f (𝓝[Ω] β₁) (𝓝 (F₁ β₁)) := by
    have hc := (hCont₁ β₁ (Or.inr (Set.mem_singleton β₁))).mono (Set.subset_union_left)
    exact hc.tendsto.congr' (eventually_nhdsWithin_of_forall fun z hz => hEq₁ hz)
  have hlim₂ : Tendsto f (𝓝[Ω] β₂) (𝓝 (F₁ β₁)) := by
    rw [heq_val]
    have hc := (hCont₂ β₂ (Or.inr (Set.mem_singleton β₂))).mono (Set.subset_union_left)
    exact hc.tendsto.congr' (eventually_nhdsWithin_of_forall fun z hz => hEq₂ hz)
  exact hne (theorem14_18_part_b hΩ_open hΩ_bdd hf_holo hf_bij hs₁ hs₂ hlim₁ hlim₂)

/-! ### Node 14.19: Homeomorphic Extension to the Closure -/

open Classical in
/-- Canonical boundary extension of `f : ℂ → ℂ` from `Ω` by its within-domain limit
`limUnder (𝓝[Ω] z) f` outside `Ω`. -/
def caratheodoryExtension (f : ℂ → ℂ) (Ω : Set ℂ) (z : ℂ) : ℂ :=
  if z ∈ Ω then f z else limUnder (𝓝[Ω] z) f

theorem caratheodoryExtension_eq_of_mem {f : ℂ → ℂ} {Ω : Set ℂ} {z : ℂ} (hz : z ∈ Ω) :
    caratheodoryExtension f Ω z = f z := by
  simp [caratheodoryExtension, hz]

theorem caratheodoryExtension_frontier_spec {Ω : Set ℂ} (hΩ_open : IsOpen Ω)
    (hΩ_bdd : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf_holo : RudinRCA.Chapter10.HolomorphicOn f Ω)
    (hf_bij : BijOn f Ω (ball (0 : ℂ) 1)) {β : ℂ}
    (hsimple : IsSimpleBoundaryPoint Ω β) :
    caratheodoryExtension f Ω β ∈ sphere (0 : ℂ) 1 ∧
      Tendsto f (𝓝[Ω] β) (𝓝 (caratheodoryExtension f Ω β)) := by
  have hβ_not_mem : β ∉ Ω := by
    have hβ_fr : β ∈ frontier Ω := hsimple.1
    rw [frontier, hΩ_open.interior_eq] at hβ_fr
    exact hβ_fr.2
  obtain ⟨w_β, ⟨hw_norm, hw_lim, _⟩, _⟩ :=
    theorem14_18_part_a hΩ_open hΩ_bdd hf_holo hf_bij hsimple
  have _hneBot : (𝓝[Ω] β).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp hsimple.1.1
  have heq : caratheodoryExtension f Ω β = w_β := by
    simp only [caratheodoryExtension, hβ_not_mem, ↓reduceIte]
    exact hw_lim.limUnder_eq
  rw [heq]
  exact ⟨by simp [hw_norm], hw_lim⟩

/-- Every continuous extension of `f` from `Ω` to `closure Ω` agrees on `closure Ω`
with `caratheodoryExtension f Ω` when `f` has continuous extensions on `closure Ω`. -/
theorem eqOn_of_continuousOn_closure_eqOn {Ω : Set ℂ} {F G : ℂ → ℂ}
    (hF : ContinuousOn F (closure Ω)) (hG : ContinuousOn G (closure Ω))
    (hEq : EqOn F G Ω) :
    EqOn F G (closure Ω) := by
  intro z hz
  have hneBot : (𝓝[Ω] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz
  have hF_lim : Tendsto F (𝓝[Ω] z) (𝓝 (F z)) :=
    ((hF z hz).mono subset_closure).tendsto
  have hG_lim : Tendsto G (𝓝[Ω] z) (𝓝 (G z)) :=
    ((hG z hz).mono subset_closure).tendsto
  have hFG_lim : Tendsto F (𝓝[Ω] z) (𝓝 (G z)) :=
    hG_lim.congr' (eventually_nhdsWithin_of_forall fun w hw => (hEq hw).symm)
  exact tendsto_nhds_unique hF_lim hFG_lim

/-- Core package for Theorem 14.19: `caratheodoryExtension f Ω` extends `f` to a continuous
bijection of `closure Ω` onto `closure (ball 0 1) = closedBall 0 1`, mapping `frontier Ω`
bijectively onto `sphere 0 1`, and inducing homeomorphisms `closure Ω ≃ₜ closure (ball 0 1)`,
`closure Ω ≃ₜ closedBall 0 1`, and `frontier Ω ≃ₜ sphere 0 1`. -/
theorem caratheodoryExtension_homeomorph_package {Ω : Set ℂ}
    (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    (hΩ_simple : ∀ β ∈ frontier Ω, IsSimpleBoundaryPoint Ω β)
    {f : ℂ → ℂ} (hf_holo : RudinRCA.Chapter10.HolomorphicOn f Ω)
    (hf_bij : BijOn f Ω (ball (0 : ℂ) 1)) :
    let F := caratheodoryExtension f Ω
    EqOn F f Ω ∧
    ContinuousOn F (closure Ω) ∧
    BijOn F (closure Ω) (closure (ball (0 : ℂ) 1)) ∧
    BijOn F (closure Ω) (closedBall (0 : ℂ) 1) ∧
    BijOn F (frontier Ω) (sphere (0 : ℂ) 1) ∧
    (∃ e : closure Ω ≃ₜ closure (ball (0 : ℂ) 1), ∀ z : closure Ω, (e z : ℂ) = F z) ∧
    (∃ e_cb : closure Ω ≃ₜ closedBall (0 : ℂ) 1, ∀ z : closure Ω, (e_cb z : ℂ) = F z) ∧
    (∃ e_bd : frontier Ω ≃ₜ sphere (0 : ℂ) 1, ∀ z : frontier Ω, (e_bd z : ℂ) = F z) := by
  intro F
  have hEq : EqOn F f Ω := fun z hz => caratheodoryExtension_eq_of_mem hz
  have mem_frontier_of_mem_closure_not_mem :
      ∀ {z : ℂ}, z ∈ closure Ω → z ∉ Ω → z ∈ frontier Ω := by
    intro z hz hnot
    rw [frontier, hΩ_open.interior_eq]
    exact ⟨hz, hnot⟩
  have hfr_spec : ∀ β ∈ frontier Ω, F β ∈ sphere (0 : ℂ) 1 ∧ Tendsto f (𝓝[Ω] β) (𝓝 (F β)) :=
    fun β hβ => caratheodoryExtension_frontier_spec hΩ_open hΩ_bdd hf_holo hf_bij (hΩ_simple β hβ)
  have hCont : ContinuousOn F (closure Ω) := by
    intro z₀ hz₀
    by_cases hz₀_in : z₀ ∈ Ω
    · have hf_cont : ContinuousAt f z₀ := (hf_holo z₀ hz₀_in).continuousAt
      have hev : F =ᶠ[𝓝 z₀] f :=
        Filter.eventuallyEq_of_mem (hΩ_open.mem_nhds hz₀_in) fun z hz => (hEq hz)
      exact (hf_cont.congr hev.symm).continuousWithinAt
    · have hz₀_fr : z₀ ∈ frontier Ω := mem_frontier_of_mem_closure_not_mem hz₀ hz₀_in
      have hlim₀ : Tendsto f (𝓝[Ω] z₀) (𝓝 (F z₀)) := (hfr_spec z₀ hz₀_fr).2
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ, hδ_pos, hδ⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim₀ (ε / 2) (half_pos hε)
      refine ⟨δ / 2, half_pos hδ_pos, ?_⟩
      intro z hz_cl hdist_z
      by_cases hz_in : z ∈ Ω
      · rw [hEq hz_in]
        exact lt_trans (hδ hz_in (lt_trans hdist_z (half_lt_self hδ_pos))) (half_lt_self hε)
      · have hz_fr : z ∈ frontier Ω := mem_frontier_of_mem_closure_not_mem hz_cl hz_in
        have hlim_z : Tendsto f (𝓝[Ω] z) (𝓝 (F z)) := (hfr_spec z hz_fr).2
        obtain ⟨δ_z, hδz_pos, hδz⟩ :=
          Metric.tendsto_nhdsWithin_nhds.mp hlim_z (ε / 2) (half_pos hε)
        obtain ⟨w, hw_Ω, hw_dist⟩ :=
          Metric.mem_closure_iff.mp hz_cl (min (δ / 2) δ_z) (lt_min (half_pos hδ_pos) hδz_pos)
        have hfw_z : dist (f w) (F z) < ε / 2 := by
          apply hδz hw_Ω
          rw [dist_comm]
          exact lt_of_lt_of_le hw_dist (min_le_right _ _)
        have hfw_z₀ : dist (f w) (F z₀) < ε / 2 := by
          apply hδ hw_Ω
          calc
            dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle w z z₀
            _ = dist z w + dist z z₀ := by rw [dist_comm w z]
            _ < δ / 2 + δ / 2 := add_lt_add (lt_of_lt_of_le hw_dist (min_le_left _ _)) hdist_z
            _ = δ := add_halves δ
        calc
          dist (F z) (F z₀) ≤ dist (F z) (f w) + dist (f w) (F z₀) := dist_triangle _ (f w) _
          _ = dist (f w) (F z) + dist (f w) (F z₀) := by rw [dist_comm (F z) (f w)]
          _ < ε / 2 + ε / 2 := add_lt_add hfw_z hfw_z₀
          _ = ε := add_halves ε
  have hInj : InjOn F (closure Ω) := by
    intro z₁ hz₁ z₂ hz₂ heq
    by_cases h₁ : z₁ ∈ Ω <;> by_cases h₂ : z₂ ∈ Ω
    · exact hf_bij.injOn h₁ h₂ ((hEq h₁).symm.trans (heq.trans (hEq h₂)))
    · exfalso
      have hn₁ : ‖F z₁‖ < 1 := by
        rw [hEq h₁]; exact mem_ball_zero_iff.mp (hf_bij.mapsTo h₁)
      have hn₂ : ‖F z₂‖ = 1 := by
        simpa using (hfr_spec z₂ (mem_frontier_of_mem_closure_not_mem hz₂ h₂)).1
      rw [heq, hn₂] at hn₁
      exact lt_irrefl 1 hn₁
    · exfalso
      have hn₂ : ‖F z₂‖ < 1 := by
        rw [hEq h₂]; exact mem_ball_zero_iff.mp (hf_bij.mapsTo h₂)
      have hn₁ : ‖F z₁‖ = 1 := by
        simpa using (hfr_spec z₁ (mem_frontier_of_mem_closure_not_mem hz₁ h₁)).1
      rw [← heq, hn₁] at hn₂
      exact lt_irrefl 1 hn₂
    · have hfr₁ := mem_frontier_of_mem_closure_not_mem hz₁ h₁
      have hfr₂ := mem_frontier_of_mem_closure_not_mem hz₂ h₂
      have hlim₁ := (hfr_spec z₁ hfr₁).2
      have hlim₂ : Tendsto f (𝓝[Ω] z₂) (𝓝 (F z₁)) := heq ▸ (hfr_spec z₂ hfr₂).2
      exact theorem14_18_part_b hΩ_open hΩ_bdd hf_holo hf_bij
        (hΩ_simple z₁ hfr₁) (hΩ_simple z₂ hfr₂) hlim₁ hlim₂
  have hcl_ball : closure (ball (0 : ℂ) 1) = closedBall (0 : ℂ) 1 :=
    closure_ball (0 : ℂ) one_ne_zero
  have hMaps_cb : MapsTo F (closure Ω) (closedBall (0 : ℂ) 1) := by
    intro z hz
    by_cases h : z ∈ Ω
    · rw [hEq h]; exact ball_subset_closedBall (hf_bij.mapsTo h)
    · exact sphere_subset_closedBall (hfr_spec z (mem_frontier_of_mem_closure_not_mem hz h)).1
  have hSurj_cb : SurjOn F (closure Ω) (closedBall (0 : ℂ) 1) := by
    have hcomp : IsCompact (F '' closure Ω) := hΩ_bdd.isCompact_closure.image_of_continuousOn hCont
    have hball_sub : ball (0 : ℂ) 1 ⊆ F '' closure Ω := by
      rw [← hf_bij.image_eq]
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, subset_closure hz, hEq hz⟩
    rw [← hcl_ball]
    exact closure_minimal hball_sub hcomp.isClosed
  have hBij_cb : BijOn F (closure Ω) (closedBall (0 : ℂ) 1) := ⟨hMaps_cb, hInj, hSurj_cb⟩
  have hBij_cl : BijOn F (closure Ω) (closure (ball (0 : ℂ) 1)) := by
    rwa [hcl_ball]
  have hBij_fr : BijOn F (frontier Ω) (sphere (0 : ℂ) 1) := by
    refine ⟨fun β hβ => (hfr_spec β hβ).1, hInj.mono frontier_subset_closure, ?_⟩
    intro w hw
    obtain ⟨z, hz_cl, hFz⟩ := hSurj_cb (sphere_subset_closedBall hw)
    have hz_not_Ω : z ∉ Ω := by
      intro hz_in
      have hn : ‖F z‖ < 1 := by
        rw [hEq hz_in]; exact mem_ball_zero_iff.mp (hf_bij.mapsTo hz_in)
      have hw1 : ‖w‖ = 1 := by simpa using hw
      rw [hFz, hw1] at hn
      exact lt_irrefl 1 hn
    exact ⟨z, mem_frontier_of_mem_closure_not_mem hz_cl hz_not_Ω, hFz⟩
  have : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp hΩ_bdd.isCompact_closure
  have hfr_comp : IsCompact (frontier Ω) :=
    hΩ_bdd.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have : CompactSpace (frontier Ω) := isCompact_iff_compactSpace.mp hfr_comp
  let e : closure Ω ≃ₜ closure (ball (0 : ℂ) 1) :=
    Continuous.homeoOfEquivCompactToT2 (f := hBij_cl.equiv)
      (hCont.domRestrict.codRestrict fun z => hBij_cl.mapsTo z.2)
  let e_cb : closure Ω ≃ₜ closedBall (0 : ℂ) 1 :=
    Continuous.homeoOfEquivCompactToT2 (f := hBij_cb.equiv)
      (hCont.domRestrict.codRestrict fun z => hBij_cb.mapsTo z.2)
  let e_bd : frontier Ω ≃ₜ sphere (0 : ℂ) 1 :=
    Continuous.homeoOfEquivCompactToT2 (f := hBij_fr.equiv)
      ((hCont.mono frontier_subset_closure).domRestrict.codRestrict fun z => hBij_fr.mapsTo z.2)
  exact ⟨hEq, hCont, hBij_cl, hBij_cb, hBij_fr,
    ⟨e, fun _ => rfl⟩, ⟨e_cb, fun _ => rfl⟩, ⟨e_bd, fun _ => rfl⟩⟩

/-- **Theorem 14.19 (Carathéodory–Osgood–Taylor homeomorphic extension to the closure,
RCA pp. 290–291):**
If `Ω` is a bounded simply connected region in `ℂ` and every boundary point of `Ω` is simple,
then every holomorphic bijection `f` of `Ω` onto `U = ball 0 1` extends uniquely to a
homeomorphism of `closure Ω` onto `closure U` (`= closedBall 0 1`), carrying `frontier Ω`
homeomorphically onto `sphere 0 1`. -/
theorem theorem14_19 {Ω : Set ℂ} (hΩ_sc : RudinRCA.Chapter10.BookSimplyConnected Ω)
    (hΩ_bdd : Bornology.IsBounded Ω)
    (hΩ_simple : ∀ β ∈ frontier Ω, IsSimpleBoundaryPoint Ω β)
    {f : ℂ → ℂ} (hf_holo : RudinRCA.Chapter10.HolomorphicOn f Ω)
    (hf_bij : BijOn f Ω (ball (0 : ℂ) 1)) :
    (∃ e : closure Ω ≃ₜ closure (ball (0 : ℂ) 1),
      (∀ z : Ω, (e ⟨z.1, subset_closure z.2⟩ : ℂ) = f z.1) ∧
      (∀ β : frontier Ω, (e ⟨β.1, frontier_subset_closure β.2⟩ : ℂ) ∈ sphere (0 : ℂ) 1)) ∧
    (∃ F : ℂ → ℂ, EqOn F f Ω ∧ ContinuousOn F (closure Ω) ∧
      BijOn F (closure Ω) (closure (ball (0 : ℂ) 1)) ∧
      BijOn F (frontier Ω) (sphere (0 : ℂ) 1) ∧
      (∀ z : closure Ω, ∀ e : closure Ω ≃ₜ closure (ball (0 : ℂ) 1),
        (∀ w : Ω, (e ⟨w.1, subset_closure w.2⟩ : ℂ) = f w.1) →
        (e z : ℂ) = F z.1)) := by
  have hΩ_open : IsOpen Ω := hΩ_sc.1.1
  obtain ⟨hEq, hCont, hBij_cl, _, hBij_fr, ⟨e, he⟩, _, _⟩ :=
    caratheodoryExtension_homeomorph_package hΩ_open hΩ_bdd hΩ_simple hf_holo hf_bij
  refine ⟨⟨e, ?_, ?_⟩, ⟨caratheodoryExtension f Ω, hEq, hCont, hBij_cl, hBij_fr, ?_⟩⟩
  · intro z
    rw [he]
    exact hEq z.2
  · intro β
    rw [he]
    exact hBij_fr.mapsTo β.2
  · classical
    intro z e' he'
    let G : ℂ → ℂ := fun w => if hw : w ∈ closure Ω then (e' ⟨w, hw⟩ : ℂ) else 0
    have hG_cont : ContinuousOn G (closure Ω) := by
      have h_sub : Continuous (fun p : closure Ω => (e' p : ℂ)) :=
        continuous_subtype_val.comp e'.continuous
      rw [continuousOn_iff_continuous_domRestrict]
      refine h_sub.congr fun p => ?_
      simp [G]
    have hG_eq : EqOn G (caratheodoryExtension f Ω) Ω := by
      intro w hw
      have hw_cl : w ∈ closure Ω := subset_closure hw
      simp only [G, hw_cl, ↓reduceDIte]
      rw [he' ⟨w, hw⟩, hEq hw]
    have hGF := eqOn_of_continuousOn_closure_eqOn hG_cont hCont hG_eq z.2
    simpa [G, z.2] using hGF

/-! ### Node 14.20: Jordan-Curve Converse, Three-Point Normalization, and Spherical/Half-Plane Extensions -/

/-- A subset `J ⊆ ℂ` is a Jordan curve if it is homeomorphic to the unit circle `sphere 0 1`. -/
def IsJordanCurve (J : Set ℂ) : Prop :=
  Nonempty (J ≃ₜ sphere (0 : ℂ) 1)

/-- A subset `A ⊆ ℂ` is a Jordan arc if it is homeomorphic to `[0, 1]`. -/
def IsJordanArc (A : Set ℂ) : Prop :=
  Nonempty (A ≃ₜ Icc (0 : ℝ) 1)

theorem isCompact_of_isJordanCurve {J : Set ℂ} (hJ : IsJordanCurve J) : IsCompact J := by
  rcases hJ with ⟨e⟩
  have : CompactSpace (sphere (0 : ℂ) 1) := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  have : CompactSpace J := e.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

theorem nonempty_of_isJordanCurve {J : Set ℂ} (hJ : IsJordanCurve J) : J.Nonempty := by
  rcases hJ with ⟨e⟩
  exact ⟨(e.symm ⟨1, by simp⟩ : ℂ), (e.symm ⟨1, by simp⟩).2⟩

theorem isCompact_of_isJordanArc {A : Set ℂ} (hA : IsJordanArc A) : IsCompact A := by
  rcases hA with ⟨e⟩
  have : CompactSpace (Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  have : CompactSpace A := e.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

theorem isConnected_of_isJordanArc {A : Set ℂ} (hA : IsJordanArc A) : IsConnected A := by
  rcases hA with ⟨e⟩
  have hrange : Set.range (fun p : Icc (0 : ℝ) 1 => (e.symm p : ℂ)) = A := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩; exact (e.symm p).2
    · intro hz; exact ⟨e ⟨z, hz⟩, by simp⟩
  rw [← hrange]
  have : ConnectedSpace (Icc (0 : ℝ) 1) :=
    Subtype.connectedSpace (isConnected_Icc zero_le_one)
  exact isConnected_range (continuous_subtype_val.comp e.symm.continuous)

/-- Integer-valued continuous functions on preconnected sets are constant. -/
theorem eq_of_isPreconnected_int_cast {α : Type*} [TopologicalSpace α] {S : Set α}
    (hS : IsPreconnected S) {q : α → ℂ} (hq : ContinuousOn q S)
    (hint : ∀ x ∈ S, ∃ k : ℤ, q x = k) {x y : α} (hx : x ∈ S) (hy : y ∈ S) :
    q x = q y := by
  let g : α → ℝ := fun z => (q z).re
  have hg : ContinuousOn g S := Complex.continuous_re.comp_continuousOn hq
  have hg_int : ∀ z ∈ S, ∃ k : ℤ, g z = k := by
    intro z hz
    obtain ⟨k, hk⟩ := hint z hz
    exact ⟨k, by simp [g, hk]⟩
  have hgx_eq_gy : g x = g y := by
    by_contra hne
    obtain ⟨kx, hkx⟩ := hg_int x hx
    obtain ⟨ky, hky⟩ := hg_int y hy
    have hkne : kx ≠ ky := fun h => hne (by rw [hkx, hky, h])
    have himg_pre : IsPreconnected (g '' S) := hS.image g hg
    by_cases hlt : kx < ky
    · have hmid_in : ((kx : ℝ) + 1 / 2) ∈ Icc (g x) (g y) := by
        rw [hkx, hky]
        have h1 : (kx : ℝ) + 1 ≤ (ky : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hlt
        exact ⟨by linarith, by linarith⟩
      have hsub := himg_pre.ordConnected.out
        (⟨x, hx, rfl⟩ : g x ∈ g '' S) (⟨y, hy, rfl⟩ : g y ∈ g '' S)
      rcases hsub hmid_in with ⟨z, hz, hgz⟩
      obtain ⟨kz, hkz⟩ := hg_int z hz
      have h2 : (2 : ℝ) * (kz : ℝ) = 2 * (kx : ℝ) + 1 := by linarith
      have h2z : (2 * kz : ℤ) = 2 * kx + 1 := by exact_mod_cast h2
      omega
    · have hgt : ky < kx := lt_of_le_of_ne (not_lt.mp hlt) hkne.symm
      have hmid_in : ((ky : ℝ) + 1 / 2) ∈ Icc (g y) (g x) := by
        rw [hkx, hky]
        have h1 : (ky : ℝ) + 1 ≤ (kx : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hgt
        exact ⟨by linarith, by linarith⟩
      have hsub := himg_pre.ordConnected.out
        (⟨y, hy, rfl⟩ : g y ∈ g '' S) (⟨x, hx, rfl⟩ : g x ∈ g '' S)
      rcases hsub hmid_in with ⟨z, hz, hgz⟩
      obtain ⟨kz, hkz⟩ := hg_int z hz
      have h2 : (2 : ℝ) * (kz : ℝ) = 2 * (ky : ℝ) + 1 := by linarith
      have h2z : (2 * kz : ℤ) = 2 * ky + 1 := by exact_mod_cast h2
      omega
  obtain ⟨kx, hkx⟩ := hint x hx
  obtain ⟨ky, hky⟩ := hint y hy
  have hk_eq : (kx : ℝ) = (ky : ℝ) := by simpa [g, hkx, hky] using hgx_eq_gy
  have hkz_eq : kx = ky := Int.cast_injective hk_eq
  rw [hkx, hky, hkz_eq]

/-- Borsuk–Eilenberg continuous-logarithm relation for `(z - a) / (z - b)` on `X ⊆ ℂ`. -/
def HasContLogRatio (X : Set ℂ) (a b : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, ContinuousOn g X ∧ ∀ z ∈ X, Complex.exp (g z) = (z - a) / (z - b)

theorem hasContLogRatio_refl {X : Set ℂ} {a : ℂ} (ha : a ∉ X) :
    HasContLogRatio X a a := by
  refine ⟨fun _ => 0, continuousOn_const, fun z hz => ?_⟩
  have hne : z - a ≠ 0 := sub_ne_zero.mpr (fun h => ha (h ▸ hz))
  rw [Complex.exp_zero, div_self hne]

theorem hasContLogRatio_symm {X : Set ℂ} {a b : ℂ} (_ha : a ∉ X) (_hb : b ∉ X)
    (h : HasContLogRatio X a b) : HasContLogRatio X b a := by
  rcases h with ⟨g, hg_cont, hg_exp⟩
  refine ⟨fun z => -g z, hg_cont.neg, fun z hz => ?_⟩
  rw [Complex.exp_neg, hg_exp z hz, inv_div]

theorem hasContLogRatio_trans {X : Set ℂ} {a b c : ℂ} (hb : b ∉ X)
    (hab : HasContLogRatio X a b) (hbc : HasContLogRatio X b c) :
    HasContLogRatio X a c := by
  rcases hab with ⟨g₁, hg₁_cont, hg₁_exp⟩
  rcases hbc with ⟨g₂, hg₂_cont, hg₂_exp⟩
  refine ⟨fun z => g₁ z + g₂ z, hg₁_cont.add hg₂_cont, fun z hz => ?_⟩
  have hzb : z - b ≠ 0 := sub_ne_zero.mpr (fun h0 => hb (h0 ▸ hz))
  rw [Complex.exp_add, hg₁_exp z hz, hg₂_exp z hz]
  field_simp [hzb]

theorem hasContLogRatio_mono {X Y : Set ℂ} (hsub : Y ⊆ X) {a b : ℂ}
    (h : HasContLogRatio X a b) : HasContLogRatio Y a b := by
  rcases h with ⟨g, hg_cont, hg_exp⟩
  exact ⟨g, hg_cont.mono hsub, fun z hz => hg_exp z (hsub hz)⟩

theorem hasContLogRatio_ball_step {X : Set ℂ} {a b : ℂ} {δ : ℝ}
    (hball : ball a δ ⊆ Xᶜ) (hb : b ∈ ball a (δ / 2)) :
    HasContLogRatio X a b := by
  have hδ_pos : 0 < δ := by
    by_contra hle
    have hgt := mem_ball.mp hb
    have hnn : 0 ≤ dist b a := dist_nonneg
    linarith
  have hz_dist_a : ∀ z ∈ X, δ ≤ ‖z - a‖ := by
    intro z hz
    by_contra hlt
    have hmem : z ∈ ball a δ := by
      rw [mem_ball, dist_eq_norm]; exact not_le.mp hlt
    exact hball hmem hz
  have hba_lt : ‖b - a‖ < δ / 2 := by simpa [mem_ball, dist_eq_norm] using hb
  have hz_dist_b : ∀ z ∈ X, δ / 2 < ‖z - b‖ := by
    intro z hz
    have htri : ‖z - a‖ ≤ ‖z - b‖ + ‖b - a‖ := by
      simpa using norm_add_le (z - b) (b - a)
    linarith [hz_dist_a z hz]
  let u : ℂ → ℂ := fun z => (z - a) / (z - b)
  have hu_cont : ContinuousOn u X := by
    refine (continuousOn_id.sub continuousOn_const).div
      (continuousOn_id.sub continuousOn_const) fun z hz => ?_
    exact norm_ne_zero_iff.mp (lt_trans (half_pos hδ_pos) (hz_dist_b z hz)).ne'
  have hu_slit : ∀ z ∈ X, u z ∈ Complex.slitPlane := by
    intro z hz
    have hzb_pos : 0 < ‖z - b‖ := lt_trans (half_pos hδ_pos) (hz_dist_b z hz)
    have hzb_ne : z - b ≠ 0 := norm_ne_zero_iff.mp hzb_pos.ne'
    have hu_sub : u z - 1 = (b - a) / (z - b) := by
      dsimp [u]; field_simp [hzb_ne]; ring
    have hnorm_lt : ‖u z - 1‖ < 1 := by
      rw [hu_sub, norm_div, div_lt_one hzb_pos]
      exact lt_trans hba_lt (hz_dist_b z hz)
    have hre_pos : 0 < (u z).re := by
      have habs : |(u z).re - 1| ≤ ‖u z - 1‖ := by
        simpa [Complex.sub_re, Complex.one_re] using Complex.abs_re_le_norm (u z - 1)
      linarith [(abs_le.mp habs).1, hnorm_lt]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl hre_pos)
  refine ⟨fun z => Complex.log (u z), hu_cont.clog hu_slit, fun z hz => ?_⟩
  have hre_pos : (u z).re > 0 ∨ (u z).im ≠ 0 := Complex.mem_slitPlane_iff.mp (hu_slit z hz)
  have hne : u z ≠ 0 := by
    intro h0; simp [h0] at hre_pos
  exact Complex.exp_log hne

theorem hasContLogRatio_of_mem_connectedComponentIn {X : Set ℂ} (hX : IsClosed X)
    {a b : ℂ} (ha : a ∈ Xᶜ) (hb : b ∈ connectedComponentIn Xᶜ a) :
    HasContLogRatio X a b := by
  let S : Set ℂ := {w ∈ Xᶜ | HasContLogRatio X a w}
  have hS_open : IsOpen S := by
    rw [Metric.isOpen_iff]
    rintro w ⟨hw_c, haw⟩
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.isOpen_iff.mp hX.isOpen_compl w hw_c
    refine ⟨δ / 2, half_pos hδ_pos, fun w' hw' => ?_⟩
    have hw'_c : w' ∈ Xᶜ := hball (lt_trans hw' (half_lt_self hδ_pos))
    exact ⟨hw'_c, hasContLogRatio_trans hw_c haw (hasContLogRatio_ball_step hball hw')⟩
  have hSc_open : IsOpen (Xᶜ \ S) := by
    rw [Metric.isOpen_iff]
    rintro w ⟨hw_c, hnaw⟩
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.isOpen_iff.mp hX.isOpen_compl w hw_c
    refine ⟨δ / 2, half_pos hδ_pos, fun w' hw' => ?_⟩
    have hw'_c : w' ∈ Xᶜ := hball (lt_trans hw' (half_lt_self hδ_pos))
    refine ⟨hw'_c, fun ⟨_, haw'⟩ => hnaw ⟨hw_c, ?_⟩⟩
    exact hasContLogRatio_trans hw'_c haw'
      (hasContLogRatio_symm hw_c hw'_c (hasContLogRatio_ball_step hball hw'))
  have hconn : IsConnected (connectedComponentIn Xᶜ a) :=
    isConnected_connectedComponentIn_iff.mpr ha
  let C : Set ℂ := connectedComponentIn Xᶜ a
  have hC_sub : C ⊆ S ∪ (Xᶜ \ S) := fun z hz => by
    have hzc : z ∈ Xᶜ := connectedComponentIn_subset Xᶜ a hz
    by_cases h : z ∈ S
    · exact Or.inl h
    · exact Or.inr ⟨hzc, h⟩
  have ha_in : a ∈ C ∩ S :=
    ⟨mem_connectedComponentIn ha, ha, hasContLogRatio_refl ha⟩
  by_contra hnotS
  have hb_c : b ∈ Xᶜ := connectedComponentIn_subset Xᶜ a hb
  have hb_in : b ∈ C ∩ (Xᶜ \ S) := ⟨hb, hb_c, fun hS => hnotS hS.2⟩
  rcases hconn.isPreconnected S (Xᶜ \ S) hS_open hSc_open hC_sub ⟨a, ha_in⟩ ⟨b, hb_in⟩ with
    ⟨w, _, hwS, _, hnwS⟩
  exact hnwS hwS

/-- Key Tietze-extension obstruction: if `V` is bounded and open with `frontier V ⊆ X`,
`a ∈ V`, and `b ∉ V ∪ X`, then `(z - a) / (z - b)` cannot have a continuous logarithm on `X`. -/
theorem not_hasContLogRatio_of_bounded_open_frontier_subset {X V : Set ℂ}
    (hX : IsClosed X) (hV_open : IsOpen V) (hV_bdd : Bornology.IsBounded V)
    (hfr : frontier V ⊆ X) {a b : ℂ} (ha : a ∈ V) (hbV : b ∉ V) (hbX : b ∉ X) :
    ¬ HasContLogRatio X a b := by
  rintro ⟨g, hg_cont, hg_exp⟩
  let g_sub : C(X, ℂ) := ⟨X.domRestrict g, continuousOn_iff_continuous_domRestrict.mp hg_cont⟩
  obtain ⟨g_ext, hg_ext⟩ := ContinuousMap.exists_restrict_eq hX g_sub
  have hg_eq : ∀ z ∈ X, g_ext z = g z := by
    intro z hz
    have h := congrFun (congrArg DFunLike.coe hg_ext) ⟨z, hz⟩
    simpa [g_sub] using h
  classical
  let F : ℂ → ℂ := fun z => if z ∈ V then (z - b) * Complex.exp (g_ext z) else z - a
  have hF_cont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro z₀
    by_cases hz₀ : z₀ ∈ V
    · have hev : F =ᶠ[𝓝 z₀] fun z => (z - b) * Complex.exp (g_ext z) :=
        Filter.eventuallyEq_of_mem (hV_open.mem_nhds hz₀) fun z hz => by simp [F, hz]
      exact (((continuous_id.sub continuous_const).mul
        (Complex.continuous_exp.comp g_ext.continuous)).continuousAt).congr hev.symm
    · by_cases hcl : z₀ ∈ closure V
      · have hz₀_fr : z₀ ∈ frontier V := by
          rw [frontier, hV_open.interior_eq]
          exact ⟨hcl, hz₀⟩
        have hz₀_X : z₀ ∈ X := hfr hz₀_fr
        have hzb_ne : z₀ - b ≠ 0 := sub_ne_zero.mpr (fun h0 => hbX (h0 ▸ hz₀_X))
        let f₁ : ℂ → ℂ := fun z => (z - b) * Complex.exp (g_ext z)
        let f₂ : ℂ → ℂ := fun z => z - a
        have hf₁_z₀ : f₁ z₀ = z₀ - a := by
          dsimp [f₁]
          rw [hg_eq z₀ hz₀_X, hg_exp z₀ hz₀_X, mul_div_cancel₀ _ hzb_ne]
        have hf₁_c : ContinuousAt f₁ z₀ :=
          ((continuous_id.sub continuous_const).mul
            (Complex.continuous_exp.comp g_ext.continuous)).continuousAt
        have hf₂_c : ContinuousAt f₂ z₀ := (continuous_id.sub continuous_const).continuousAt
        have hF_z₀ : F z₀ = z₀ - a := by simp [F, hz₀]
        rw [Metric.continuousAt_iff]
        intro ε hε
        obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.continuousAt_iff.mp hf₁_c ε hε
        obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.continuousAt_iff.mp hf₂_c ε hε
        refine ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun z hz => ?_⟩
        by_cases hzv : z ∈ V
        · have : F z = f₁ z := by simp [F, f₁, hzv]
          rw [this, hF_z₀, ← hf₁_z₀]
          exact hδ₁ (lt_of_lt_of_le hz (min_le_left _ _))
        · have : F z = f₂ z := by simp [F, f₂, hzv]
          rw [this, hF_z₀]
          exact hδ₂ (lt_of_lt_of_le hz (min_le_right _ _))
      · have hev : F =ᶠ[𝓝 z₀] fun z => z - a := by
          filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl] with z hz
          have hzv : z ∉ V := fun h => hz (subset_closure h)
          simp [F, hzv]
        exact ((continuous_id.sub continuous_const).continuousAt).congr hev.symm
  have hF_ne : ∀ z : ℂ, F z ≠ 0 := by
    intro z
    by_cases hzv : z ∈ V
    · simp only [F, hzv, ↓reduceIte]
      exact mul_ne_zero (sub_ne_zero.mpr fun h0 => hbV (h0 ▸ hzv)) (Complex.exp_ne_zero _)
    · simp only [F, hzv, ↓reduceIte]
      exact sub_ne_zero.mpr fun h0 => hzv (h0 ▸ ha)
  have h0_not_img : (0 : ℂ) ∉ F '' Set.univ := by
    rintro ⟨z, _, hz0⟩
    exact hF_ne z hz0
  have hsc_univ : IsSimplyConnected (Set.univ : Set ℂ) := by
    have : ContractibleSpace (Set.univ : Set ℂ) :=
      convex_univ.contractibleSpace Set.univ_nonempty
    change SimplyConnectedSpace (Set.univ : Set ℂ)
    exact inferInstance
  obtain ⟨L, hL_cont, hL_exp⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hsc_univ isOpen_univ
      hF_cont.continuousOn h0_not_img
  obtain ⟨R₀, hR₀⟩ := hV_bdd.subset_ball a
  let R : ℝ := max R₀ 1
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hV_sub_R : V ⊆ ball a R := hR₀.trans (ball_subset_ball (le_max_left _ _))
  let γ : ℝ → ℂ := fun θ => a + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  have hγ_not_V : ∀ θ : ℝ, γ θ ∉ V := by
    intro θ hmem
    have hlt : ‖γ θ - a‖ < R := by simpa [mem_ball, dist_eq_norm] using hV_sub_R hmem
    have heq : ‖γ θ - a‖ = R := by
      dsimp [γ]
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hR_pos, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact lt_irrefl R (heq ▸ hlt)
  let c₀ : ℂ := (2 * Real.pi : ℂ) * Complex.I
  have hc₀_ne : c₀ ≠ 0 := mul_ne_zero
    (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) Complex.I_ne_zero
  let q : ℝ → ℂ := fun θ =>
    (L (γ θ) - ((Real.log R : ℂ) + (θ : ℂ) * Complex.I)) / c₀
  have hγ_cont : Continuous γ :=
    continuous_const.add (continuous_const.mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)))
  have hL_c : Continuous L := continuousOn_univ.mp hL_cont
  have hq_cont : ContinuousOn q (Icc (0 : ℝ) (2 * Real.pi)) :=
    (((hL_c.comp hγ_cont).sub
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))).div_const c₀).continuousOn
  have hq_int : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), ∃ k : ℤ, q θ = k := by
    intro θ _
    have hexp_L : Complex.exp (L (γ θ)) = (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      have h1 : Complex.exp (L (γ θ)) = F (γ θ) := hL_exp (Set.mem_univ (γ θ))
      rw [h1]
      simp [F, hγ_not_V θ, γ]
    have hexp_rhs : Complex.exp ((Real.log R : ℂ) + (θ : ℂ) * Complex.I) =
        (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [Complex.exp_add, Complex.ofReal_log hR_pos.le,
        Complex.exp_log (Complex.ofReal_ne_zero.mpr hR_pos.ne')]
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hexp_L.trans hexp_rhs.symm)
    refine ⟨k, ?_⟩
    dsimp [q, c₀]
    have hsub_k : L (γ θ) - ((Real.log R : ℂ) + (θ : ℂ) * Complex.I) =
        (k : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) := by
      rw [hk]; ring
    rw [hsub_k, mul_div_cancel_right₀ _ hc₀_ne]
  have hq_eq : q 0 = q (2 * Real.pi) :=
    eq_of_isPreconnected_int_cast isPreconnected_Icc hq_cont hq_int
      (left_mem_Icc.mpr (by positivity)) (right_mem_Icc.mpr (by positivity))
  have hγ_per : γ (2 * Real.pi) = γ 0 := by
    dsimp [γ]
    have h2pi : ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I := by
      push_cast; ring
    rw [h2pi, Complex.exp_two_pi_mul_I]
    simp
  dsimp [q] at hq_eq
  rw [hγ_per] at hq_eq
  have hnum_eq := (div_left_inj' hc₀_ne).mp hq_eq
  apply hc₀_ne
  dsimp [c₀]
  push_cast at hnum_eq ⊢
  linear_combination hnum_eq

/-- Exterior `{z : ℂ | R < ‖z‖}` is connected for every `R ≥ 0`. -/
theorem isConnected_exterior_closedBall {R : ℝ} (hR : 0 ≤ R) :
    IsConnected {z : ℂ | R < ‖z‖} := by
  let E : Set ℂ := {z : ℂ | R < ‖z‖}
  have hbase : ((R + 1 : ℝ) : ℂ) ∈ E := by
    change R < ‖((R + 1 : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < R + 1)]
    linarith
  have h_to_base : ∀ z ∈ E, JoinedIn E z ((R + 1 : ℝ) : ℂ) := by
    intro z hz
    change R < ‖z‖ at hz
    have hz_pos : 0 < ‖z‖ := lt_of_le_of_lt hR hz
    let θ : ℝ := Complex.arg z
    have hj1 : JoinedIn E ((‖z‖ : ℂ)) z := by
      refine ⟨{
        toFun := fun t : unitInterval => circleMap 0 ‖z‖ ((t : ℝ) * θ)
        continuous_toFun := (continuous_circleMap 0 ‖z‖).comp
          (continuous_subtype_val.mul continuous_const)
        source' := by simp [circleMap]
        target' := by
          simp only [Icc.coe_one, one_mul, circleMap_zero]
          exact Complex.norm_mul_exp_arg_mul_I z }, ?_⟩
      intro t
      change R < ‖circleMap 0 ‖z‖ ((t : ℝ) * θ)‖
      rw [norm_circleMap_zero, abs_of_pos hz_pos]
      exact hz
    have hj2 : JoinedIn E ((‖z‖ : ℂ)) ((R + 1 : ℝ) : ℂ) := by
      refine ⟨{
        toFun := fun t : unitInterval =>
          (((1 - (t : ℝ)) * ‖z‖ + (t : ℝ) * (R + 1) : ℝ) : ℂ)
        continuous_toFun := Complex.continuous_ofReal.comp
          (((continuous_const.sub continuous_subtype_val).mul continuous_const).add
            (continuous_subtype_val.mul continuous_const))
        source' := by simp
        target' := by simp }, ?_⟩
      intro t
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      have hprod : 0 ≤ (1 - (t : ℝ)) * (‖z‖ - R) :=
        mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hz.le)
      have hval_gt : R < (1 - (t : ℝ)) * ‖z‖ + (t : ℝ) * (R + 1) := by
        by_cases ht0' : (t : ℝ) = 0
        · rw [ht0']; linarith
        · have ht_pos : 0 < (t : ℝ) := lt_of_le_of_ne ht0 (Ne.symm ht0')
          linarith
      have hval_pos : 0 < (1 - (t : ℝ)) * ‖z‖ + (t : ℝ) * (R + 1) := lt_of_le_of_lt hR hval_gt
      change R < ‖(((1 - (t : ℝ)) * ‖z‖ + (t : ℝ) * (R + 1) : ℝ) : ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hval_pos]
      exact hval_gt
    exact hj1.symm.trans hj2
  exact IsPathConnected.isConnected
    ⟨((R + 1 : ℝ) : ℂ), hbase, fun {z} hz => (h_to_base z hz).symm⟩

/-- Every connected component `V` of `Xᶜ` (for closed `X ⊆ ℂ`) is open and has `frontier V ⊆ X`. -/
theorem isOpen_and_frontier_subset_of_connectedComponentIn_compl {X : Set ℂ} (hX : IsClosed X)
    {a : ℂ} :
    IsOpen (connectedComponentIn Xᶜ a) ∧ frontier (connectedComponentIn Xᶜ a) ⊆ X := by
  have hV_open : IsOpen (connectedComponentIn Xᶜ a) := hX.isOpen_compl.connectedComponentIn
  refine ⟨hV_open, fun z hz => ?_⟩
  rw [frontier, hV_open.interior_eq] at hz
  by_contra hzX
  have ha : a ∈ Xᶜ := by
    rcases (connectedComponentIn Xᶜ a).eq_empty_or_nonempty with hemp | ⟨w, hw⟩
    · rw [hemp, closure_empty] at hz; exact False.elim hz.1
    · exact by_contra fun hna => by
        rw [connectedComponentIn_eq_empty hna] at hw; exact hw
  have hconn : IsConnected (connectedComponentIn Xᶜ a) :=
    isConnected_connectedComponentIn_iff.mpr ha
  let W : Set ℂ := insert z (connectedComponentIn Xᶜ a)
  have hW_conn : IsConnected W := by
    refine hconn.subset_closure (Set.subset_insert z _) ?_
    intro y hy
    rcases eq_or_mem_of_mem_insert hy with rfl | hy'
    · exact hz.1
    · exact subset_closure hy'
  have hW_sub : W ⊆ Xᶜ := by
    intro y hy
    rcases eq_or_mem_of_mem_insert hy with rfl | hy'
    · exact hzX
    · exact connectedComponentIn_subset Xᶜ a hy'
  have hz_mem : z ∈ connectedComponentIn Xᶜ a :=
    hW_conn.isPreconnected.subset_connectedComponentIn (Set.mem_insert_of_mem z (mem_connectedComponentIn ha))
      hW_sub (Set.mem_insert z _)
  exact hz.2 hz_mem

/-- For compact `X ⊆ ℂ`, at most one connected component of `Xᶜ` is unbounded; every other
component of `Xᶜ` is bounded. -/
theorem bounded_or_eq_unbounded_component_of_isCompact {X : Set ℂ} (hX : IsCompact X) :
    ∃ u₀ ∈ Xᶜ, ¬ Bornology.IsBounded (connectedComponentIn Xᶜ u₀) ∧
      ∀ a ∈ Xᶜ, a ∉ connectedComponentIn Xᶜ u₀ →
        Bornology.IsBounded (connectedComponentIn Xᶜ a) := by
  obtain ⟨R₀, hR₀⟩ := hX.isBounded.subset_ball (0 : ℂ)
  let R : ℝ := max R₀ 0
  have hR_nn : 0 ≤ R := le_max_right _ _
  have hX_sub : X ⊆ closedBall (0 : ℂ) R :=
    hR₀.trans ((ball_subset_ball (le_max_left _ _)).trans ball_subset_closedBall)
  let E : Set ℂ := {z : ℂ | R < ‖z‖}
  have hE_sub : E ⊆ Xᶜ := by
    intro z hz hzX
    have hle : ‖z‖ ≤ R := by simpa using hX_sub hzX
    exact not_lt_of_ge hle hz
  let u₀ : ℂ := ((R + 1 : ℝ) : ℂ)
  have hu₀_E : u₀ ∈ E := by
    change R < ‖((R + 1 : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < R + 1)]
    linarith
  have hu₀_c : u₀ ∈ Xᶜ := hE_sub hu₀_E
  have hE_in_U : E ⊆ connectedComponentIn Xᶜ u₀ :=
    (isConnected_exterior_closedBall hR_nn).isPreconnected.subset_connectedComponentIn hu₀_E hE_sub
  refine ⟨u₀, hu₀_c, ?_, ?_⟩
  · intro hbdd
    obtain ⟨M, hM⟩ := hbdd.subset_ball (0 : ℂ)
    let M' : ℝ := max (max R M) 0 + 1
    have hM'_pos : 0 < M' := by positivity
    have hmem_E : ((M' : ℝ) : ℂ) ∈ E := by
      change R < ‖((M' : ℝ) : ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM'_pos]
      have : R ≤ max (max R M) 0 := le_trans (le_max_left R M) (le_max_left _ _)
      linarith
    have hlt_M : ‖((M' : ℝ) : ℂ)‖ < M := by
      simpa using hM (hE_in_U hmem_E)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM'_pos] at hlt_M
    have : M ≤ max (max R M) 0 := le_trans (le_max_right R M) (le_max_left _ _)
    linarith
  · intro a ha hnot_mem
    refine (isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset ?_
    intro z hz
    simp only [mem_closedBall_zero_iff]
    by_contra hgt
    have hz_E : z ∈ E := not_le.mp hgt
    have hz_u₀ : z ∈ connectedComponentIn Xᶜ u₀ := hE_in_U hz_E
    have h1 : connectedComponentIn Xᶜ a = connectedComponentIn Xᶜ z :=
      connectedComponentIn_eq hz
    have h2 : connectedComponentIn Xᶜ u₀ = connectedComponentIn Xᶜ z :=
      connectedComponentIn_eq hz_u₀
    have heq_comp : connectedComponentIn Xᶜ a = connectedComponentIn Xᶜ u₀ :=
      h1.trans h2.symm
    exact hnot_mem (heq_comp ▸ mem_connectedComponentIn ha)

/-- **Borsuk–Eilenberg Theorem:** For compact `X ⊆ ℂ` and `a, b ∈ Xᶜ`, `a` and `b` lie in the
same connected component of `Xᶜ` if and only if `(z - a) / (z - b)` possesses a continuous
logarithm on `X`. -/
theorem borsuk_eilenberg_iff {X : Set ℂ} (hX : IsCompact X) {a b : ℂ}
    (ha : a ∈ Xᶜ) (hb : b ∈ Xᶜ) :
    b ∈ connectedComponentIn Xᶜ a ↔ HasContLogRatio X a b := by
  constructor
  · exact hasContLogRatio_of_mem_connectedComponentIn hX.isClosed ha
  · intro hlog
    by_contra hnot
    obtain ⟨u₀, hu₀_c, _, h_bdd_other⟩ := bounded_or_eq_unbounded_component_of_isCompact hX
    by_cases ha_u₀ : a ∈ connectedComponentIn Xᶜ u₀
    · have hb_not_u₀ : b ∉ connectedComponentIn Xᶜ u₀ := by
        intro hb_u₀
        have heq := connectedComponentIn_eq ha_u₀
        rw [heq] at hb_u₀
        exact hnot hb_u₀
      have hVb_bdd := h_bdd_other b hb hb_not_u₀
      obtain ⟨hVb_open, hVb_fr⟩ :=
        isOpen_and_frontier_subset_of_connectedComponentIn_compl hX.isClosed (a := b)
      have ha_not_Vb : a ∉ connectedComponentIn Xᶜ b := fun ha_b =>
        hnot ((connectedComponentIn_eq ha_b).symm ▸ mem_connectedComponentIn hb)
      exact not_hasContLogRatio_of_bounded_open_frontier_subset hX.isClosed hVb_open hVb_bdd
        hVb_fr (mem_connectedComponentIn hb) ha_not_Vb ha
        (hasContLogRatio_symm ha hb hlog)
    · have hVa_bdd := h_bdd_other a ha ha_u₀
      obtain ⟨hVa_open, hVa_fr⟩ :=
        isOpen_and_frontier_subset_of_connectedComponentIn_compl hX.isClosed (a := a)
      exact not_hasContLogRatio_of_bounded_open_frontier_subset hX.isClosed hVa_open hVa_bdd
        hVa_fr (mem_connectedComponentIn ha) hnot hb hlog

/-- **Janiszewski's Theorem:** If `K₁, K₂ ⊆ ℂ` are compact with `K₁ ∩ K₂` connected, and
`a, b ∈ (K₁ ∪ K₂)ᶜ` connect in `K₁ᶜ` and in `K₂ᶜ`, then `a, b` connect in `(K₁ ∪ K₂)ᶜ`. -/
theorem janiszewski_connectedComponentIn {K₁ K₂ : Set ℂ}
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) (hinter : IsConnected (K₁ ∩ K₂))
    {a b : ℂ} (ha : a ∈ (K₁ ∪ K₂)ᶜ) (hb : b ∈ (K₁ ∪ K₂)ᶜ)
    (h1 : b ∈ connectedComponentIn K₁ᶜ a) (h2 : b ∈ connectedComponentIn K₂ᶜ a) :
    b ∈ connectedComponentIn (K₁ ∪ K₂)ᶜ a := by
  have ha1 : a ∈ K₁ᶜ := fun h => ha (Or.inl h)
  have hb1 : b ∈ K₁ᶜ := fun h => hb (Or.inl h)
  have ha2 : a ∈ K₂ᶜ := fun h => ha (Or.inr h)
  have hb2 : b ∈ K₂ᶜ := fun h => hb (Or.inr h)
  obtain ⟨g₁, hg₁_c, hg₁_e⟩ := (borsuk_eilenberg_iff hK₁ ha1 hb1).mp h1
  obtain ⟨g₂, hg₂_c, hg₂_e⟩ := (borsuk_eilenberg_iff hK₂ ha2 hb2).mp h2
  obtain ⟨z₀, hz₀⟩ := hinter.nonempty
  let c₀ : ℂ := (2 * Real.pi : ℂ) * Complex.I
  have hc₀_ne : c₀ ≠ 0 := mul_ne_zero
    (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) Complex.I_ne_zero
  let q : ℂ → ℂ := fun z => (g₁ z - g₂ z) / c₀
  have hq_cont : ContinuousOn q (K₁ ∩ K₂) :=
    ((hg₁_c.mono Set.inter_subset_left).sub (hg₂_c.mono Set.inter_subset_right)).div_const c₀
  have hq_int : ∀ z ∈ K₁ ∩ K₂, ∃ k : ℤ, q z = k := by
    intro z hz
    have hexp_eq : Complex.exp (g₁ z) = Complex.exp (g₂ z) :=
      (hg₁_e z hz.1).trans (hg₂_e z hz.2).symm
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp_eq
    refine ⟨k, ?_⟩
    dsimp [q, c₀]
    have hsub : g₁ z - g₂ z = (k : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) := by
      rw [hk]; ring
    rw [hsub, mul_div_cancel_right₀ _ hc₀_ne]
  let Δ : ℂ := g₁ z₀ - g₂ z₀
  have hdiff_const : ∀ z ∈ K₁ ∩ K₂, g₁ z = g₂ z + Δ := by
    intro z hz
    have hq_eq := eq_of_isPreconnected_int_cast hinter.isPreconnected hq_cont hq_int hz hz₀
    have hnum := (div_left_inj' hc₀_ne).mp hq_eq
    dsimp [Δ]
    linear_combination hnum
  have hexp_Δ : Complex.exp Δ = 1 := by
    have hza : z₀ - a ≠ 0 := sub_ne_zero.mpr (fun h0 => ha1 (h0 ▸ hz₀.1))
    have hzb : z₀ - b ≠ 0 := sub_ne_zero.mpr (fun h0 => hb1 (h0 ▸ hz₀.1))
    dsimp [Δ]
    rw [Complex.exp_sub, hg₁_e z₀ hz₀.1, hg₂_e z₀ hz₀.2, div_self (div_ne_zero hza hzb)]
  classical
  let g : ℂ → ℂ := fun z => if z ∈ K₁ then g₁ z else g₂ z + Δ
  have hg_on_K₂ : ∀ z ∈ K₂, g z = g₂ z + Δ := by
    intro z hz
    by_cases hz1 : z ∈ K₁
    · simp only [g, hz1, ↓reduceIte]
      exact hdiff_const z ⟨hz1, hz⟩
    · simp [g, hz1]
  have hg_cont : ContinuousOn g (K₁ ∪ K₂) := by
    intro z₀' hz₀'
    by_cases h_in1 : z₀' ∈ K₁
    · by_cases h_in2 : z₀' ∈ K₂
      · rw [Metric.continuousWithinAt_iff]
        intro ε hε
        obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.continuousWithinAt_iff.mp (hg₁_c z₀' h_in1) ε hε
        obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ :=
          Metric.continuousWithinAt_iff.mp ((hg₂_c.add continuousOn_const) z₀' h_in2) ε hε
        refine ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun w hw hdist => ?_⟩
        rcases hw with hw1 | hw2
        · simp only [g, hw1, h_in1, ↓reduceIte]
          exact hδ₁ hw1 (lt_of_lt_of_le hdist (min_le_left _ _))
        · rw [hg_on_K₂ w hw2, hg_on_K₂ z₀' h_in2]
          exact hδ₂ hw2 (lt_of_lt_of_le hdist (min_le_right _ _))
      · have hev : g =ᶠ[𝓝[K₁ ∪ K₂] z₀'] g₁ := by
          rw [eventuallyEq_nhdsWithin_iff]
          filter_upwards [hK₂.isClosed.isOpen_compl.mem_nhds h_in2] with w hw2 hw_u
          rcases hw_u with hw1 | hw2'
          · simp [g, hw1]
          · exact False.elim (hw2 hw2')
        have hc1 : ContinuousWithinAt g₁ (K₁ ∪ K₂) z₀' := by
          rw [Metric.continuousWithinAt_iff]
          intro ε hε
          obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.continuousWithinAt_iff.mp (hg₁_c z₀' h_in1) ε hε
          obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ :=
            Metric.isOpen_iff.mp hK₂.isClosed.isOpen_compl z₀' h_in2
          refine ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun w hw hdist => ?_⟩
          rcases hw with hw1 | hw2
          · exact hδ₁ hw1 (lt_of_lt_of_le hdist (min_le_left _ _))
          · exact False.elim (hδ₂ (lt_of_lt_of_le hdist (min_le_right _ _)) hw2)
        exact hc1.congr_of_eventuallyEq hev (by simp [g, h_in1])
    · have h_in2 : z₀' ∈ K₂ := hz₀'.resolve_left h_in1
      have hev : g =ᶠ[𝓝[K₁ ∪ K₂] z₀'] fun w => g₂ w + Δ := by
        rw [eventuallyEq_nhdsWithin_iff]
        filter_upwards [hK₁.isClosed.isOpen_compl.mem_nhds h_in1] with w hw1 _
        have hnot1 : w ∉ K₁ := hw1
        simp [g, hnot1]
      have hc2 : ContinuousWithinAt (fun w => g₂ w + Δ) (K₁ ∪ K₂) z₀' := by
        rw [Metric.continuousWithinAt_iff]
        intro ε hε
        obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ :=
          Metric.continuousWithinAt_iff.mp ((hg₂_c.add continuousOn_const) z₀' h_in2) ε hε
        obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ :=
          Metric.isOpen_iff.mp hK₁.isClosed.isOpen_compl z₀' h_in1
        refine ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun w hw hdist => ?_⟩
        rcases hw with hw1 | hw2
        · exact False.elim (hδ₁ (lt_of_lt_of_le hdist (min_le_left _ _)) hw1)
        · exact hδ₂ hw2 (lt_of_lt_of_le hdist (min_le_right _ _))
      exact hc2.congr_of_eventuallyEq hev (by simp [g, h_in1])
  have hg_exp : ∀ z ∈ K₁ ∪ K₂, Complex.exp (g z) = (z - a) / (z - b) := by
    rintro z (hz1 | hz2)
    · simp [g, hz1, hg₁_e z hz1]
    · rw [hg_on_K₂ z hz2, Complex.exp_add, hexp_Δ, mul_one, hg₂_e z hz2]
  exact (borsuk_eilenberg_iff (hK₁.union hK₂) ha hb).mpr ⟨g, hg_cont, hg_exp⟩

/-- **Jordan Arc Non-Separation:** The complement `Aᶜ` of every Jordan arc `A ⊆ ℂ` is connected. -/
theorem isConnected_compl_of_isJordanArc {A : Set ℂ} (hA : IsJordanArc A) :
    IsConnected Aᶜ := by
  have hA_comp : IsCompact A := isCompact_of_isJordanArc hA
  obtain ⟨R, hR⟩ := hA_comp.isBounded.subset_ball (0 : ℂ)
  let a₀ : ℂ := ((max R 0 + 1 : ℝ) : ℂ)
  have ha₀ : a₀ ∈ Aᶜ := by
    intro hmem
    have hlt : ‖a₀‖ < R := by simpa using hR hmem
    have hpos : 0 < max R 0 + 1 := by positivity
    simp only [a₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hlt
    linarith [le_max_left R 0]
  refine ⟨⟨a₀, ha₀⟩, ?_⟩
  rcases hA with ⟨e⟩
  have hall_comp : ∀ b ∈ Aᶜ, b ∈ connectedComponentIn Aᶜ a₀ := by
    intro b hb
    rw [borsuk_eilenberg_iff hA_comp ha₀ hb]
    let p : ℂ → A := fun w => e.symm (Set.projIcc 0 1 zero_le_one w.re)
    have hp_cont : Continuous (fun w : ℂ => (p w : ℂ)) :=
      continuous_subtype_val.comp (e.symm.continuous.comp
        ((continuous_projIcc).comp Complex.continuous_re))
    let U_map : ℂ → ℂ := fun w => ((p w : ℂ) - a₀) / ((p w : ℂ) - b)
    have hU_cont : Continuous U_map := by
      refine (hp_cont.sub continuous_const).div (hp_cont.sub continuous_const) fun w => ?_
      exact sub_ne_zero.mpr (fun h0 => hb (h0 ▸ (p w).2))
    have hU_ne0 : (0 : ℂ) ∉ U_map '' Set.univ := by
      rintro ⟨w, _, hw0⟩
      have hza : (p w : ℂ) - a₀ ≠ 0 := sub_ne_zero.mpr (fun h0 => ha₀ (h0 ▸ (p w).2))
      have hzb : (p w : ℂ) - b ≠ 0 := sub_ne_zero.mpr (fun h0 => hb (h0 ▸ (p w).2))
      exact div_ne_zero hza hzb hw0
    have hsc_univ : IsSimplyConnected (Set.univ : Set ℂ) := by
      have : ContractibleSpace (Set.univ : Set ℂ) :=
        convex_univ.contractibleSpace Set.univ_nonempty
      change SimplyConnectedSpace (Set.univ : Set ℂ)
      exact inferInstance
    obtain ⟨L, hL_cont, hL_exp⟩ :=
      Complex.exists_continuousOn_eqOn_exp_comp hsc_univ isOpen_univ
        hU_cont.continuousOn hU_ne0
    have hL_c : Continuous L := continuousOn_univ.mp hL_cont
    classical
    let g : ℂ → ℂ := fun z => if hz : z ∈ A then L (((e ⟨z, hz⟩ : Icc (0 : ℝ) 1) : ℝ) : ℂ) else 0
    refine ⟨g, ?_, ?_⟩
    · rw [continuousOn_iff_continuous_domRestrict]
      have hsub : Continuous (fun q : A => L (((e q : Icc (0 : ℝ) 1) : ℝ) : ℂ)) :=
        hL_c.comp (Complex.continuous_ofReal.comp (continuous_subtype_val.comp e.continuous))
      refine hsub.congr fun q => ?_
      simp [g]
    · intro z hz
      simp only [g, hz, ↓reduceDIte]
      have hexp := hL_exp (Set.mem_univ (((e ⟨z, hz⟩ : Icc (0 : ℝ) 1) : ℝ) : ℂ))
      dsimp [Function.comp_def, U_map, p] at hexp
      have hproj : Set.projIcc 0 1 zero_le_one (e ⟨z, hz⟩ : ℝ) = e ⟨z, hz⟩ :=
        Set.projIcc_of_mem zero_le_one (e ⟨z, hz⟩).2
      rw [hproj, Homeomorph.symm_apply_apply] at hexp
      exact hexp
  have heq : connectedComponentIn Aᶜ a₀ = Aᶜ :=
    Set.Subset.antisymm (connectedComponentIn_subset Aᶜ a₀) hall_comp
  rw [← heq]
  exact (isConnected_connectedComponentIn_iff.mpr ha₀).isPreconnected

/-! ### Subsection 20.1B: Circle Arcs, Component Frontier, Simple Connectedness, and Simplicity -/

/-- Any proper closed arc `exp(t i)` (`t ∈ [a, b]`, `a < b`, `b - a < 2π`) on `sphere 0 1` is a
Jordan arc. -/
theorem circleArc_isJordanArc {a b : ℝ} (hab : a < b) (hlen : b - a < 2 * Real.pi) :
    let S : Set ℂ := (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) '' Icc a b
    S ⊆ sphere (0 : ℂ) 1 ∧ IsJordanArc S := by
  intro S
  have hsub : S ⊆ sphere (0 : ℂ) 1 := by
    rintro _ ⟨t, _, rfl⟩
    simp [Complex.norm_exp_ofReal_mul_I]
  refine ⟨hsub, ?_⟩
  let φ : Icc (0 : ℝ) 1 → ℂ := fun t =>
    Complex.exp ((((1 - (t : ℝ)) * a + (t : ℝ) * b : ℝ) : ℂ) * Complex.I)
  have hφ_cont : Continuous φ :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
        (((continuous_const.sub continuous_subtype_val).mul continuous_const).add
          (continuous_subtype_val.mul continuous_const))).mul continuous_const)
  have hφ_maps : ∀ t : Icc (0 : ℝ) 1, φ t ∈ S := by
    intro t
    refine ⟨(1 - (t : ℝ)) * a + (t : ℝ) * b, ?_, rfl⟩
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    exact ⟨by nlinarith, by nlinarith⟩
  have hφ_inj : Function.Injective φ := by
    intro t₁ t₂ heq
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
    have hk_im : ((1 - (t₁ : ℝ)) * a + (t₁ : ℝ) * b) =
        ((1 - (t₂ : ℝ)) * a + (t₂ : ℝ) * b) + (k : ℝ) * (2 * Real.pi) := by
      have hmul : ((((1 - (t₁ : ℝ)) * a + (t₁ : ℝ) * b : ℝ) : ℂ) -
          (((1 - (t₂ : ℝ)) * a + (t₂ : ℝ) * b + (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ)) * Complex.I = 0 := by
        push_cast at hk ⊢; linear_combination hk
      have h0 := (mul_eq_zero.mp hmul).resolve_right Complex.I_ne_zero
      have hreal : ((1 - (t₁ : ℝ)) * a + (t₁ : ℝ) * b) -
          (((1 - (t₂ : ℝ)) * a + (t₂ : ℝ) * b + (k : ℝ) * (2 * Real.pi))) = 0 := by
        exact_mod_cast h0
      linarith
    have ht₁_0 : 0 ≤ (t₁ : ℝ) := t₁.2.1
    have ht₁_1 : (t₁ : ℝ) ≤ 1 := t₁.2.2
    have ht₂_0 : 0 ≤ (t₂ : ℝ) := t₂.2.1
    have ht₂_1 : (t₂ : ℝ) ≤ 1 := t₂.2.2
    have hdiff_lt : |(k : ℝ) * (2 * Real.pi)| < 2 * Real.pi := by
      have h1 : (t₁ : ℝ) - (t₂ : ℝ) ≤ 1 := by linarith
      have h2 : -1 ≤ (t₁ : ℝ) - (t₂ : ℝ) := by linarith
      have h3 : (k : ℝ) * (2 * Real.pi) = ((t₁ : ℝ) - (t₂ : ℝ)) * (b - a) := by linarith
      rw [h3, abs_mul]
      have habs_t : |(t₁ : ℝ) - (t₂ : ℝ)| ≤ 1 := abs_le.mpr ⟨h2, h1⟩
      have habs_ba : |b - a| = b - a := abs_of_pos (sub_pos.mpr hab)
      rw [habs_ba]
      nlinarith
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at hdiff_lt
    have hk_lt1 : |(k : ℝ)| < 1 := by nlinarith [Real.pi_pos]
    have hkz_lt1 : |k| < 1 := by exact_mod_cast hk_lt1
    have hkz_bounds := abs_lt.mp hkz_lt1
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [Int.cast_zero, zero_mul, add_zero] at hk_im
    have hba_ne : b - a ≠ 0 := (sub_pos.mpr hab).ne'
    have ht_eq : (t₁ : ℝ) = (t₂ : ℝ) := by nlinarith
    exact Subtype.ext ht_eq
  have hφ_surj : ∀ w : S, ∃ t : Icc (0 : ℝ) 1, ⟨φ t, hφ_maps t⟩ = w := by
    rintro ⟨w, s, hs, rfl⟩
    let t₀ : ℝ := (s - a) / (b - a)
    have hba_pos : 0 < b - a := sub_pos.mpr hab
    have ht₀_mem : t₀ ∈ Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg (sub_nonneg.mpr hs.1) hba_pos.le, (div_le_one hba_pos).mpr ?_⟩
      linarith [hs.2]
    refine ⟨⟨t₀, ht₀_mem⟩, Subtype.ext ?_⟩
    dsimp [φ, t₀]
    congr 2
    have : (1 - (s - a) / (b - a)) * a + (s - a) / (b - a) * b = s := by
      field_simp [hba_pos.ne']; ring
    exact_mod_cast this
  let f_sub : Icc (0 : ℝ) 1 → S := fun t => ⟨φ t, hφ_maps t⟩
  have hf_bij : Function.Bijective f_sub :=
    ⟨fun t₁ t₂ h => hφ_inj (congrArg Subtype.val h), hφ_surj⟩
  have : CompactSpace (Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  let e : Icc (0 : ℝ) 1 ≃ₜ S :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f_sub hf_bij)
      (hφ_cont.codRestrict hφ_maps)
  exact ⟨e.symm⟩

/-- Splitting `sphere 0 1` into two closed Jordan arcs meeting at `{exp(θ₁ i), exp(θ₂ i)}`. -/
theorem sphere_split_two_arcs {θ₁ θ₂ : ℝ} (h12 : θ₁ < θ₂) (h21 : θ₂ < θ₁ + 2 * Real.pi) :
    let S₁ : Set ℂ := (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) '' Icc θ₁ θ₂
    let S₂ : Set ℂ := (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) '' Icc θ₂ (θ₁ + 2 * Real.pi)
    S₁ ∪ S₂ = sphere (0 : ℂ) 1 ∧
      S₁ ∩ S₂ = {Complex.exp ((θ₁ : ℂ) * Complex.I), Complex.exp ((θ₂ : ℂ) * Complex.I)} ∧
      IsJordanArc S₁ ∧ IsJordanArc S₂ := by
  intro S₁ S₂
  have hlen1 : θ₂ - θ₁ < 2 * Real.pi := by linarith
  have hlen2 : (θ₁ + 2 * Real.pi) - θ₂ < 2 * Real.pi := by linarith
  obtain ⟨hS₁_sub, hS₁_arc⟩ := circleArc_isJordanArc h12 hlen1
  obtain ⟨hS₂_sub, hS₂_arc⟩ := circleArc_isJordanArc h21 hlen2
  refine ⟨?_, ?_, hS₁_arc, hS₂_arc⟩
  · refine Set.Subset.antisymm (Set.union_subset hS₁_sub hS₂_sub) ?_
    intro w hw
    have hw_norm : ‖w‖ = 1 := by simpa using hw
    let z : ℂ := w * Complex.exp (-(θ₁ : ℂ) * Complex.I)
    have hz_norm : ‖z‖ = 1 := by
      dsimp [z]
      have hneg : -(θ₁ : ℂ) * Complex.I = ((-θ₁ : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [norm_mul, hw_norm, one_mul, hneg, Complex.norm_exp_ofReal_mul_I]
    let φ : ℝ := if Complex.arg z < 0 then Complex.arg z + 2 * Real.pi else Complex.arg z
    have hφ_mem : φ ∈ Ico (0 : ℝ) (2 * Real.pi) := by
      have hgt := Complex.neg_pi_lt_arg z
      have hle := Complex.arg_le_pi z
      dsimp [φ]
      split_ifs with hlt
      · exact ⟨by linarith, by linarith⟩
      · exact ⟨not_lt.mp hlt, by linarith [Real.pi_pos]⟩
    have hexp_φ : Complex.exp ((φ : ℂ) * Complex.I) = z := by
      have harg_z : Complex.exp ((Complex.arg z : ℂ) * Complex.I) = z := by
        have h := Complex.norm_mul_exp_arg_mul_I z
        simpa [hz_norm] using h
      dsimp [φ]
      split_ifs with hlt
      · have hsplit : ((Complex.arg z + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
            (Complex.arg z : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by
          push_cast; ring
        rw [hsplit, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one, harg_z]
      · exact harg_z
    let θ : ℝ := θ₁ + φ
    have hexp_θ : Complex.exp ((θ : ℂ) * Complex.I) = w := by
      have hsplit : ((θ₁ + φ : ℝ) : ℂ) * Complex.I =
          (θ₁ : ℂ) * Complex.I + (φ : ℂ) * Complex.I := by push_cast; ring
      dsimp [θ]
      rw [hsplit, Complex.exp_add, hexp_φ]
      dsimp [z]
      rw [mul_comm w _, ← mul_assoc, ← Complex.exp_add]
      have h0 : (θ₁ : ℂ) * Complex.I + -(θ₁ : ℂ) * Complex.I = 0 := by ring
      rw [h0, Complex.exp_zero, one_mul]
    rcases le_or_gt θ θ₂ with hle | hgt
    · left; exact ⟨θ, ⟨by linarith [hφ_mem.1], hle⟩, hexp_θ⟩
    · right; exact ⟨θ, ⟨hgt.le, by linarith [hφ_mem.2]⟩, hexp_θ⟩
  · refine Set.Subset.antisymm ?_ ?_
    · rintro w ⟨⟨t₁, ht₁, rfl⟩, ⟨t₂, ht₂, heq⟩⟩
      obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
      have hrel : t₂ = t₁ + (k : ℝ) * (2 * Real.pi) := by
        have hmul : (((t₂ : ℝ) : ℂ) - (((t₁ + (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ))) * Complex.I = 0 := by
          push_cast; linear_combination hk
        have h0 := (mul_eq_zero.mp hmul).resolve_right Complex.I_ne_zero
        have hreal : t₂ - (t₁ + (k : ℝ) * (2 * Real.pi)) = 0 := by exact_mod_cast h0
        linarith
      have hdiff_nn : 0 ≤ (k : ℝ) * (2 * Real.pi) := by linarith [ht₁.2, ht₂.1]
      have hdiff_le : (k : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi := by linarith [ht₁.1, ht₂.2]
      have hk_nn : (0 : ℝ) ≤ (k : ℝ) := by nlinarith [Real.pi_pos]
      have hk_le1 : (k : ℝ) ≤ 1 := by nlinarith [Real.pi_pos]
      have hkz_nn : 0 ≤ k := by exact_mod_cast hk_nn
      have hkz_le1 : k ≤ 1 := by exact_mod_cast hk_le1
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · right
        have ht_eq : t₁ = θ₂ := by
          simp only [Int.cast_zero, zero_mul, add_zero] at hrel
          linarith [ht₁.2, ht₂.1]
        rw [ht_eq]; rfl
      · left
        have ht_eq : t₁ = θ₁ := by
          simp only [Int.cast_one, one_mul] at hrel
          linarith [ht₁.1, ht₂.2]
        rw [ht_eq]
    · intro w hw
      rcases hw with rfl | rfl
      · refine ⟨⟨θ₁, ⟨le_rfl, h12.le⟩, rfl⟩, ⟨θ₁ + 2 * Real.pi, ⟨h21.le, le_rfl⟩, ?_⟩⟩
        dsimp only
        have hsplit : ((θ₁ + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
            (θ₁ : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by push_cast; ring
        rw [hsplit, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      · exact ⟨⟨θ₂, ⟨h12.le, le_rfl⟩, rfl⟩, ⟨θ₂, ⟨le_rfl, h21.le⟩, rfl⟩⟩

/-- Image of a Jordan arc subset of `sphere 0 1` under `sphere 0 1 ≃ₜ J` is a Jordan arc in `ℂ`. -/
theorem isJordanArc_image_of_homeomorph {J S : Set ℂ} (φ : sphere (0 : ℂ) 1 ≃ₜ J)
    (hS_sub : S ⊆ sphere (0 : ℂ) 1) (hS_arc : IsJordanArc S) :
    IsJordanArc (Subtype.val '' (φ '' {w : sphere (0 : ℂ) 1 | w.1 ∈ S})) := by
  rcases hS_arc with ⟨eS⟩
  let A : Set ℂ := Subtype.val '' (φ '' {w : sphere (0 : ℂ) 1 | w.1 ∈ S})
  let f : Icc (0 : ℝ) 1 → A := fun t =>
    let wS := eS.symm t
    let w_sph : sphere (0 : ℂ) 1 := ⟨wS.1, hS_sub wS.2⟩
    ⟨(φ w_sph : ℂ), ⟨φ w_sph, ⟨w_sph, wS.2, rfl⟩, rfl⟩⟩
  have hf_cont : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp (φ.continuous.comp
      (Continuous.subtype_mk (continuous_subtype_val.comp eS.symm.continuous) _))
  have hf_inj : Function.Injective f := by
    intro t₁ t₂ heq
    have hval := congrArg Subtype.val heq
    dsimp [f] at hval
    have hφ_eq := φ.injective (Subtype.ext hval)
    have hw_eq := congrArg Subtype.val hφ_eq
    exact eS.symm.injective (Subtype.ext hw_eq)
  have hf_surj : Function.Surjective f := by
    rintro ⟨z, ⟨p, ⟨w_sph, hw_in_S, rfl⟩, rfl⟩⟩
    refine ⟨eS ⟨w_sph.1, hw_in_S⟩, Subtype.ext ?_⟩
    dsimp [f]
    have hsymm : (eS.symm (eS ⟨w_sph.1, hw_in_S⟩)).1 = w_sph.1 :=
      congrArg Subtype.val (eS.symm_apply_apply _)
    have hw_eq : (⟨(eS.symm (eS ⟨w_sph.1, hw_in_S⟩)).1,
        hS_sub (eS.symm (eS ⟨w_sph.1, hw_in_S⟩)).2⟩ : sphere (0 : ℂ) 1) = w_sph :=
      Subtype.ext hsymm
    rw [hw_eq]
  have : CompactSpace (Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  let eA : Icc (0 : ℝ) 1 ≃ₜ A :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩) hf_cont
  exact ⟨eA.symm⟩

/-- Local arc decomposition of a Jordan curve `J` near any point `β ∈ J`: for every `ε > 0`,
`J = A₁ ∪ A₂` where `A₁ ⊆ ball β ε`, `β ∈ A₁ \ A₂`, and `A₁, A₂` are Jordan arcs. -/
theorem jordanCurve_arc_decomposition {J : Set ℂ} (hJ : IsJordanCurve J)
    {β : ℂ} (hβ : β ∈ J) {ε : ℝ} (hε : 0 < ε) :
    ∃ A₁ A₂ : Set ℂ, A₁ ∪ A₂ = J ∧ A₁ ⊆ ball β ε ∧ β ∈ A₁ ∧ β ∉ A₂ ∧
      IsJordanArc A₁ ∧ IsJordanArc A₂ := by
  rcases hJ with ⟨e⟩
  let φ : sphere (0 : ℂ) 1 ≃ₜ J := e.symm
  let w₀ : sphere (0 : ℂ) 1 := e ⟨β, hβ⟩
  have hφ_w₀ : (φ w₀ : ℂ) = β := by
    have : φ w₀ = ⟨β, hβ⟩ := e.symm_apply_apply ⟨β, hβ⟩
    exact congrArg Subtype.val this
  have hφ_cont : ContinuousAt (fun w : sphere (0 : ℂ) 1 => (φ w : ℂ)) w₀ :=
    (continuous_subtype_val.comp φ.continuous).continuousAt
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hφ_cont ε hε
  let θ₀ : ℝ := Complex.arg w₀.1
  have hw₀_exp : Complex.exp ((θ₀ : ℂ) * Complex.I) = w₀.1 := by
    have hn : ‖w₀.1‖ = 1 := by simp
    have h := Complex.norm_mul_exp_arg_mul_I w₀.1
    simpa [hn] using h
  have hexp_cont : ContinuousAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) θ₀ :=
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).continuousAt
  obtain ⟨η, hη_pos, hη⟩ := Metric.continuousAt_iff.mp hexp_cont δ hδ_pos
  let α : ℝ := min (η / 2) (Real.pi / 2)
  have hα_pos : 0 < α := lt_min (half_pos hη_pos) (by positivity)
  have hα_lt_pi : α < Real.pi :=
    lt_of_le_of_lt (min_le_right _ _) (half_lt_self Real.pi_pos)
  have h12 : θ₀ - α < θ₀ + α := by linarith
  have h21 : θ₀ + α < (θ₀ - α) + 2 * Real.pi := by linarith
  obtain ⟨hS_union, hS_inter, hS₁_arc, hS₂_arc⟩ := sphere_split_two_arcs h12 h21
  let S₁ : Set ℂ := (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) '' Icc (θ₀ - α) (θ₀ + α)
  let S₂ : Set ℂ :=
    (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) '' Icc (θ₀ + α) ((θ₀ - α) + 2 * Real.pi)
  have hS₁_sub : S₁ ⊆ sphere (0 : ℂ) 1 := by
    rw [← hS_union]; exact Set.subset_union_left
  have hS₂_sub : S₂ ⊆ sphere (0 : ℂ) 1 := by
    rw [← hS_union]; exact Set.subset_union_right
  let A₁ : Set ℂ := Subtype.val '' (φ '' {w : sphere (0 : ℂ) 1 | w.1 ∈ S₁})
  let A₂ : Set ℂ := Subtype.val '' (φ '' {w : sphere (0 : ℂ) 1 | w.1 ∈ S₂})
  refine ⟨A₁, A₂, ?_, ?_, ?_, ?_,
    isJordanArc_image_of_homeomorph φ hS₁_sub hS₁_arc,
    isJordanArc_image_of_homeomorph φ hS₂_sub hS₂_arc⟩
  · ext z
    constructor
    · rintro (⟨_, ⟨w, _, rfl⟩, rfl⟩ | ⟨_, ⟨w, _, rfl⟩, rfl⟩) <;> exact (φ w).2
    · intro hz
      let w : sphere (0 : ℂ) 1 := φ.symm ⟨z, hz⟩
      have hw_mem : w.1 ∈ S₁ ∪ S₂ := hS_union.symm ▸ w.2
      rcases hw_mem with hw1 | hw2
      · left; exact ⟨⟨z, hz⟩, ⟨w, hw1, φ.apply_symm_apply _⟩, rfl⟩
      · right; exact ⟨⟨z, hz⟩, ⟨w, hw2, φ.apply_symm_apply _⟩, rfl⟩
  · rintro z ⟨_, ⟨w, ⟨t, ht, htw⟩, rfl⟩, rfl⟩
    have ht_dist : dist t θ₀ < η := by
      rw [Real.dist_eq, abs_lt]
      have hα_le : α ≤ η / 2 := min_le_left _ _
      exact ⟨by linarith [ht.1, hη_pos], by linarith [ht.2, hη_pos]⟩
    have hw_dist : dist w w₀ < δ := by
      change dist w.1 w₀.1 < δ
      rw [← htw, ← hw₀_exp]
      exact hη ht_dist
    rw [mem_ball, ← hφ_w₀]
    exact hδ hw_dist
  · refine ⟨φ w₀, ⟨w₀, ⟨θ₀, ⟨by linarith, by linarith⟩, hw₀_exp⟩, rfl⟩, hφ_w₀⟩
  · rintro ⟨q, ⟨w, hw2, hw_eq⟩, hval_eq⟩
    have hp_eq : φ w = φ w₀ := by
      rw [hw_eq]
      exact Subtype.ext (hval_eq.trans hφ_w₀.symm)
    have hw_w₀ : w = w₀ := φ.injective hp_eq
    rw [hw_w₀] at hw2
    have hw₀_in1 : w₀.1 ∈ S₁ := ⟨θ₀, ⟨by linarith, by linarith⟩, hw₀_exp⟩
    have hw₀_inter : w₀.1 ∈ S₁ ∩ S₂ := ⟨hw₀_in1, hw2⟩
    rw [hS_inter] at hw₀_inter
    rcases hw₀_inter with hleft | hright
    · rw [← hw₀_exp] at hleft
      obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hleft
      have hrel : θ₀ = (θ₀ - α) + (k : ℝ) * (2 * Real.pi) := by
        have hmul : (((θ₀ : ℝ) : ℂ) - ((((θ₀ - α) + (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ))) * Complex.I = 0 := by
          push_cast at hk ⊢; linear_combination hk
        have h0 := (mul_eq_zero.mp hmul).resolve_right Complex.I_ne_zero
        have hreal : θ₀ - ((θ₀ - α) + (k : ℝ) * (2 * Real.pi)) = 0 := by exact_mod_cast h0
        linarith
      have hk_val : (k : ℝ) * (2 * Real.pi) = α := by linarith
      have hk_pos : (0 : ℝ) < (k : ℝ) := by nlinarith [Real.pi_pos]
      have hk_lt1 : (k : ℝ) < 1 := by nlinarith [Real.pi_pos]
      have hkz_pos : 0 < k := by exact_mod_cast hk_pos
      have hkz_lt1 : k < 1 := by exact_mod_cast hk_lt1
      omega
    · have hright' : w₀.1 = Complex.exp (((θ₀ + α : ℝ) : ℂ) * Complex.I) := hright
      rw [← hw₀_exp] at hright'
      obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hright'
      have hrel : θ₀ = (θ₀ + α) + (k : ℝ) * (2 * Real.pi) := by
        have hmul : (((θ₀ : ℝ) : ℂ) - ((((θ₀ + α) + (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ))) * Complex.I = 0 := by
          push_cast at hk ⊢; linear_combination hk
        have h0 := (mul_eq_zero.mp hmul).resolve_right Complex.I_ne_zero
        have hreal : θ₀ - ((θ₀ + α) + (k : ℝ) * (2 * Real.pi)) = 0 := by exact_mod_cast h0
        linarith
      have hk_val : (-(k : ℝ)) * (2 * Real.pi) = α := by linarith
      have hk_pos : (0 : ℝ) < -(k : ℝ) := by nlinarith [Real.pi_pos]
      have hk_lt1 : -(k : ℝ) < 1 := by nlinarith [Real.pi_pos]
      have hkz_pos : 0 < -k := by exact_mod_cast hk_pos
      have hkz_lt1 : -k < 1 := by exact_mod_cast hk_lt1
      omega

/-- Every connected component `U` of `Jᶜ` (for a Jordan curve `J`) has `frontier U = J`. -/
theorem jordanCurve_component_frontier_eq {J : Set ℂ} (hJ : IsJordanCurve J)
    {a : ℂ} (ha : a ∈ Jᶜ) :
    frontier (connectedComponentIn Jᶜ a) = J := by
  have hJ_comp : IsCompact J := isCompact_of_isJordanCurve hJ
  let U : Set ℂ := connectedComponentIn Jᶜ a
  obtain ⟨hU_open, hfr_sub⟩ := isOpen_and_frontier_subset_of_connectedComponentIn_compl hJ_comp.isClosed (a := a)
  refine Set.Subset.antisymm hfr_sub ?_
  intro β hβ
  by_contra hnot_fr
  have hβ_not_U : β ∉ U := fun h => (connectedComponentIn_subset Jᶜ a h) hβ
  have hβ_not_cl : β ∉ closure U := by
    intro hcl
    apply hnot_fr
    rw [frontier, hU_open.interior_eq]
    exact ⟨hcl, hβ_not_U⟩
  obtain ⟨ε, hε_pos, hball_disj⟩ :=
    Metric.isOpen_iff.mp isClosed_closure.isOpen_compl β hβ_not_cl
  obtain ⟨A₁, A₂, hA_union, hA₁_ball, hβ_A₁, hβ_not_A₂, _, hA₂_arc⟩ :=
    jordanCurve_arc_decomposition hJ hβ hε_pos
  have hfr_sub_A₂ : frontier U ⊆ A₂ := by
    intro z hz
    have hz_J : z ∈ J := hfr_sub hz
    rw [← hA_union] at hz_J
    rcases hz_J with hz1 | hz2
    · exfalso
      have hz_cl : z ∈ closure U := hz.1
      exact hball_disj (hA₁_ball hz1) hz_cl
    · exact hz2
  have hU_sub_A₂c : U ⊆ A₂ᶜ := by
    intro z hz hzA₂
    have hzJ : z ∈ J := hA_union ▸ Or.inr hzA₂
    exact connectedComponentIn_subset Jᶜ a hz hzJ
  have hA₂_closed : IsClosed A₂ := (isCompact_of_isJordanArc hA₂_arc).isClosed
  have hA₂c_conn : IsConnected A₂ᶜ := isConnected_compl_of_isJordanArc hA₂_arc
  -- `U` and `A₂ᶜ \ U` disconnect `A₂ᶜ`, contradicting `β ∈ A₂ᶜ \ U` and `a ∈ U`!
  have hA₂c_diff_open : IsOpen (A₂ᶜ \ U) := by
    have heq : A₂ᶜ \ U = A₂ᶜ \ closure U := by
      ext z
      constructor
      · rintro ⟨hz_c, hz_nU⟩
        refine ⟨hz_c, fun hcl => ?_⟩
        have hz_fr : z ∈ frontier U := by
          rw [frontier, hU_open.interior_eq]; exact ⟨hcl, hz_nU⟩
        exact hz_c (hfr_sub_A₂ hz_fr)
      · rintro ⟨hz_c, hz_ncl⟩
        exact ⟨hz_c, fun hzU => hz_ncl (subset_closure hzU)⟩
    rw [heq]
    exact hA₂_closed.isOpen_compl.sdiff isClosed_closure
  have ha_U : a ∈ A₂ᶜ ∩ U := ⟨hU_sub_A₂c (mem_connectedComponentIn ha), mem_connectedComponentIn ha⟩
  have hβ_diff : β ∈ A₂ᶜ ∩ (A₂ᶜ \ U) := ⟨hβ_not_A₂, hβ_not_A₂, hβ_not_U⟩
  have hcover : A₂ᶜ ⊆ U ∪ (A₂ᶜ \ U) := fun z hz => by
    by_cases h : z ∈ U
    · exact Or.inl h
    · exact Or.inr ⟨hz, h⟩
  rcases hA₂c_conn.isPreconnected U (A₂ᶜ \ U) hU_open hA₂c_diff_open hcover
    ⟨a, ha_U⟩ ⟨β, hβ_diff⟩ with ⟨w, _, hwU, _, hnwU⟩
  exact hnwU hwU

/-- Every bounded connected component `U` of `Jᶜ` is `BookSimplyConnected`. -/
theorem jordanCurve_bounded_component_simplyConnected {J : Set ℂ} (hJ : IsJordanCurve J)
    {a : ℂ} (ha : a ∈ Jᶜ) (hbdd : Bornology.IsBounded (connectedComponentIn Jᶜ a)) :
    RudinRCA.Chapter10.BookSimplyConnected (connectedComponentIn Jᶜ a) := by
  let U : Set ℂ := connectedComponentIn Jᶜ a
  have hJ_comp : IsCompact J := isCompact_of_isJordanCurve hJ
  obtain ⟨hU_open, _⟩ := isOpen_and_frontier_subset_of_connectedComponentIn_compl hJ_comp.isClosed (a := a)
  have hU_conn : IsConnected U := isConnected_connectedComponentIn_iff.mpr ha
  have hU_reg : RudinRCA.Chapter10.IsRegion U := ⟨hU_open, hU_conn⟩
  -- By Theorem 13.11 (`condB ↔ condD`), it suffices to prove `IsConnected (sphericalCompl U)`
  have h13_11 := RudinRCA.Chapter13.theorem13_11 hU_reg
  have hB_iff_D : RudinRCA.Chapter10.BookSimplyConnected U ↔ IsConnected (sphericalCompl U) :=
    h13_11.2.2.1.trans h13_11.2.2.2.1
  rw [hB_iff_D]
  obtain ⟨R₀, hR₀⟩ := hJ_comp.isBounded.subset_ball (0 : ℂ)
  let R : ℝ := max R₀ 0
  have hR_nn : 0 ≤ R := le_max_right _ _
  have hJ_sub : J ⊆ closedBall (0 : ℂ) R :=
    hR₀.trans ((ball_subset_ball (le_max_left _ _)).trans ball_subset_closedBall)
  let E : Set ℂ := {z : ℂ | R < ‖z‖}
  have hE_sub : E ⊆ Jᶜ := by
    intro z hz hzJ
    have hle : ‖z‖ ≤ R := by simpa using hJ_sub hzJ
    exact not_lt_of_ge hle hz
  let u₀ : ℂ := ((R + 1 : ℝ) : ℂ)
  have hu₀_E : u₀ ∈ E := by
    change R < ‖((R + 1 : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < R + 1)]
    linarith
  have hu₀_Jc : u₀ ∈ Jᶜ := hE_sub hu₀_E
  let U_inf : Set ℂ := connectedComponentIn Jᶜ u₀
  have hE_sub_Uinf : E ⊆ U_inf :=
    (isConnected_exterior_closedBall hR_nn).isPreconnected.subset_connectedComponentIn hu₀_E hE_sub
  have hU_ne_Uinf : Disjoint U U_inf := by
    refine Set.disjoint_left.mpr fun z hzU hzUinf => ?_
    have heq : U = U_inf :=
      (connectedComponentIn_eq hzU).trans (connectedComponentIn_eq hzUinf).symm
    obtain ⟨M, hM⟩ := hbdd.subset_ball (0 : ℂ)
    let M' : ℝ := max (max R M) 0 + 1
    have hM'_pos : 0 < M' := by positivity
    have hmem_E : ((M' : ℝ) : ℂ) ∈ E := by
      change R < ‖((M' : ℝ) : ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM'_pos]
      have : R ≤ max (max R M) 0 := le_trans (le_max_left R M) (le_max_left _ _)
      linarith
    have hmem_U : ((M' : ℝ) : ℂ) ∈ U := heq ▸ hE_sub_Uinf hmem_E
    have hlt_M : ‖((M' : ℝ) : ℂ)‖ < M := by simpa using hM hmem_U
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM'_pos] at hlt_M
    have : M ≤ max (max R M) 0 := le_trans (le_max_right R M) (le_max_left _ _)
    linarith
  -- Step 1: `S_inf := insert ∞ ((↑) '' U_inf ∪ (↑) '' J)` is connected
  let coeC : ℂ → RiemannSphere := fun z => (z : RiemannSphere)
  have hcoe_cont : Continuous coeC := OnePoint.continuous_coe
  have hUinf_conn : IsConnected (coeC '' U_inf) :=
    (isConnected_connectedComponentIn_iff.mpr hu₀_Jc).image coeC hcoe_cont.continuousOn
  have h_infty_cl : (∞ : RiemannSphere) ∈ closure (coeC '' U_inf) := by
    rw [mem_closure_iff_nhds_basis OnePoint.hasBasis_nhds_infty]
    intro K ⟨hK_closed, hK_comp⟩
    obtain ⟨M, hM⟩ := hK_comp.isBounded.subset_ball (0 : ℂ)
    let M' : ℝ := max (max R M) 0 + 1
    have hM'_pos : 0 < M' := by positivity
    have hmem_E : ((M' : ℝ) : ℂ) ∈ E := by
      change R < ‖((M' : ℝ) : ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM'_pos]
      have : R ≤ max (max R M) 0 := le_trans (le_max_left R M) (le_max_left _ _)
      linarith
    have hnot_K : ((M' : ℝ) : ℂ) ∉ K := by
      intro hK
      have hlt : ‖((M' : ℝ) : ℂ)‖ < M := by simpa using hM hK
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM'_pos] at hlt
      have : M ≤ max (max R M) 0 := le_trans (le_max_right R M) (le_max_left _ _)
      linarith
    refine ⟨coeC ((M' : ℝ) : ℂ), ⟨((M' : ℝ) : ℂ), hE_sub_Uinf hmem_E, rfl⟩,
      Or.inl ⟨((M' : ℝ) : ℂ), hnot_K, rfl⟩⟩
  have hJ_cl_Uinf : coeC '' J ⊆ closure (coeC '' U_inf) := by
    have hJ_sub_cl : J ⊆ closure U_inf := by
      rw [← jordanCurve_component_frontier_eq hJ hu₀_Jc]
      exact frontier_subset_closure
    exact (Set.image_mono hJ_sub_cl).trans (image_closure_subset_closure_image hcoe_cont)
  let S_base : Set RiemannSphere := insert ∞ (coeC '' U_inf ∪ coeC '' J)
  have hS_base_conn : IsConnected S_base := by
    refine hUinf_conn.subset_closure ?_ ?_
    · intro p hp; exact Set.mem_insert_of_mem _ (Or.inl hp)
    · intro p hp
      rcases eq_or_mem_of_mem_insert hp with rfl | (hp1 | hp2)
      · exact h_infty_cl
      · exact subset_closure hp1
      · exact hJ_cl_Uinf hp2
  -- Step 2: For every `z ∈ Jᶜ \ U`, `T z := S_base ∪ coeC '' connectedComponentIn Jᶜ z` is connected
  let D_out : Set ℂ := Jᶜ \ U
  let T : D_out → Set RiemannSphere := fun z =>
    S_base ∪ coeC '' connectedComponentIn Jᶜ z.1
  obtain ⟨β₀, hβ₀⟩ := nonempty_of_isJordanCurve hJ
  have hβ₀_base : coeC β₀ ∈ S_base := Set.mem_insert_of_mem _ (Or.inr ⟨β₀, hβ₀, rfl⟩)
  have hT_conn : ∀ z : D_out, IsConnected (T z) := by
    intro z
    have hz_Jc : z.1 ∈ Jᶜ := z.2.1
    let Vz : Set ℂ := connectedComponentIn Jᶜ z.1
    have hVz_conn : IsConnected (coeC '' Vz) :=
      (isConnected_connectedComponentIn_iff.mpr hz_Jc).image coeC hcoe_cont.continuousOn
    have hJ_cl_Vz : coeC '' J ⊆ closure (coeC '' Vz) := by
      have hJ_sub_cl : J ⊆ closure Vz := by
        rw [← jordanCurve_component_frontier_eq hJ hz_Jc]
        exact frontier_subset_closure
      exact (Set.image_mono hJ_sub_cl).trans (image_closure_subset_closure_image hcoe_cont)
    let Vz_J : Set RiemannSphere := coeC '' Vz ∪ coeC '' J
    have hVz_J_conn : IsConnected Vz_J := by
      refine hVz_conn.subset_closure Set.subset_union_left ?_
      rintro p (hp1 | hp2)
      · exact subset_closure hp1
      · exact hJ_cl_Vz hp2
    have heq_Tz : T z = S_base ∪ Vz_J := by
      ext p
      constructor
      · rintro (hpS | hpVz)
        · exact Or.inl hpS
        · exact Or.inr (Or.inl hpVz)
      · rintro (hpS | hpVz | hpJ)
        · exact Or.inl hpS
        · exact Or.inr hpVz
        · exact Or.inl (Set.mem_insert_of_mem _ (Or.inr hpJ))
    rw [heq_Tz]
    exact IsConnected.union ⟨coeC β₀, hβ₀_base, Or.inr ⟨β₀, hβ₀, rfl⟩⟩ hS_base_conn hVz_J_conn
  -- Step 3: `sphericalCompl U = S_base ∪ ⋃ z, T z`
  have hsc_eq : sphericalCompl U = S_base ∪ ⋃ z : D_out, T z := by
    ext p
    induction p using OnePoint.rec with
    | infty =>
      simp only [infinity_mem_sphericalCompl, S_base, Set.mem_union, Set.mem_insert_iff, true_or]
    | coe w =>
      simp only [coe_mem_sphericalCompl, Set.mem_union, Set.mem_iUnion]
      constructor
      · intro hw_nU
        by_cases hwJ : w ∈ J
        · left; exact Set.mem_insert_of_mem _ (Or.inr ⟨w, hwJ, rfl⟩)
        · right
          refine ⟨⟨w, hwJ, hw_nU⟩, Or.inr ⟨w, mem_connectedComponentIn hwJ, rfl⟩⟩
      · rintro (hbase | ⟨z, hz_mem⟩)
        · rcases eq_or_mem_of_mem_insert hbase with h_eq | (⟨x, hx, hxc⟩ | ⟨x, hx, hxc⟩)
          · exact False.elim (OnePoint.coe_ne_infty w h_eq)
          · have hwx : x = w := OnePoint.coe_injective hxc
            subst hwx
            exact fun hwU => Set.disjoint_left.mp hU_ne_Uinf hwU hx
          · have hwx : x = w := OnePoint.coe_injective hxc
            subst hwx
            exact fun hwU => connectedComponentIn_subset Jᶜ a hwU hx
        · rcases hz_mem with hbase | ⟨x, hx, hxc⟩
          · rcases eq_or_mem_of_mem_insert hbase with h_eq | (⟨y, hy, hyc⟩ | ⟨y, hy, hyc⟩)
            · exact False.elim (OnePoint.coe_ne_infty w h_eq)
            · have hwy : y = w := OnePoint.coe_injective hyc
              subst hwy
              exact fun hwU => Set.disjoint_left.mp hU_ne_Uinf hwU hy
            · have hwy : y = w := OnePoint.coe_injective hyc
              subst hwy
              exact fun hwU => connectedComponentIn_subset Jᶜ a hwU hy
          · have hwx : x = w := OnePoint.coe_injective hxc
            subst hwx
            intro hwU
            have heq_comp : connectedComponentIn Jᶜ z.1 = U :=
              (connectedComponentIn_eq hx).trans (connectedComponentIn_eq hwU).symm
            exact z.2.2 (heq_comp ▸ mem_connectedComponentIn z.2.1)
  rw [hsc_eq]
  let W : Set RiemannSphere := S_base ∪ ⋃ z : D_out, T z
  have hinf_S : (∞ : RiemannSphere) ∈ S_base := Set.mem_insert ∞ _
  refine ⟨⟨∞, Or.inl hinf_S⟩, fun u v hu hv hcov ⟨p₁, hp₁W, hp₁u⟩ ⟨p₂, hp₂W, hp₂v⟩ => ?_⟩
  have hS_cov : S_base ⊆ u ∪ v := Set.subset_union_left.trans hcov
  have hinf_uv : (∞ : RiemannSphere) ∈ u ∪ v := hS_cov hinf_S
  rcases hinf_uv with hinf_u | hinf_v
  · rcases hp₂W with hp₂S | hp₂U
    · obtain ⟨q, hqS, hquv⟩ := hS_base_conn.isPreconnected u v hu hv hS_cov
        ⟨∞, hinf_S, hinf_u⟩ ⟨p₂, hp₂S, hp₂v⟩
      exact ⟨q, Or.inl hqS, hquv⟩
    · rcases Set.mem_iUnion.mp hp₂U with ⟨z, hp₂Tz⟩
      have hTz_cov : T z ⊆ u ∪ v :=
        (Set.subset_iUnion T z).trans (Set.subset_union_right.trans hcov)
      obtain ⟨q, hqTz, hquv⟩ := (hT_conn z).isPreconnected u v hu hv hTz_cov
        ⟨∞, Or.inl hinf_S, hinf_u⟩ ⟨p₂, hp₂Tz, hp₂v⟩
      exact ⟨q, Or.inr (Set.mem_iUnion.mpr ⟨z, hqTz⟩), hquv⟩
  · rcases hp₁W with hp₁S | hp₁U
    · obtain ⟨q, hqS, hquv⟩ := hS_base_conn.isPreconnected u v hu hv hS_cov
        ⟨p₁, hp₁S, hp₁u⟩ ⟨∞, hinf_S, hinf_v⟩
      exact ⟨q, Or.inl hqS, hquv⟩
    · rcases Set.mem_iUnion.mp hp₁U with ⟨z, hp₁Tz⟩
      have hTz_cov : T z ⊆ u ∪ v :=
        (Set.subset_iUnion T z).trans (Set.subset_union_right.trans hcov)
      obtain ⟨q, hqTz, hquv⟩ := (hT_conn z).isPreconnected u v hu hv hTz_cov
        ⟨p₁, hp₁Tz, hp₁u⟩ ⟨∞, Or.inl hinf_S, hinf_v⟩
      exact ⟨q, Or.inr (Set.mem_iUnion.mpr ⟨z, hqTz⟩), hquv⟩

/-- Local path-connectedness of a bounded connected component `U` of `Jᶜ` at every `β ∈ J`:
for every `ε > 0`, there is `δ > 0` such that any two points of `U ∩ ball β δ` are joined by a
continuous path inside `U ∩ ball β ε`. -/
theorem jordanCurve_bounded_component_locally_joined {J : Set ℂ} (hJ : IsJordanCurve J)
    {a : ℂ} (_ha : a ∈ Jᶜ) (hbdd : Bornology.IsBounded (connectedComponentIn Jᶜ a))
    {β : ℂ} (hβ : β ∈ J) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z₁ ∈ connectedComponentIn Jᶜ a ∩ ball β δ,
      ∀ z₂ ∈ connectedComponentIn Jᶜ a ∩ ball β δ,
        JoinedIn (connectedComponentIn Jᶜ a ∩ ball β ε) z₁ z₂ := by
  let U : Set ℂ := connectedComponentIn Jᶜ a
  have hJ_comp : IsCompact J := isCompact_of_isJordanCurve hJ
  obtain ⟨A₁, A₂, hA_union, hA₁_ball, _, hβ_not_A₂, _, hA₂_arc⟩ :=
    jordanCurve_arc_decomposition hJ hβ hε
  have hA₂_comp : IsCompact A₂ := isCompact_of_isJordanArc hA₂_arc
  have hA₂_conn : IsConnected A₂ := isConnected_of_isJordanArc hA₂_arc
  obtain ⟨R₀, hR₀⟩ := hbdd.isCompact_closure.isBounded.subset_ball β
  let R : ℝ := max R₀ (ε + 1)
  have hR_gt_ε : ε < R := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hclU_sub : closure U ⊆ ball β R := hR₀.trans (ball_subset_ball (le_max_left _ _))
  let C_ann : Set ℂ := closedBall β R \ ball β ε
  have hC_comp : IsCompact C_ann :=
    (isCompact_closedBall β R).inter_right isOpen_ball.isClosed_compl
  let K₁ : Set ℂ := J
  let K₂ : Set ℂ := A₂ ∪ C_ann
  have hK₂_comp : IsCompact K₂ := hA₂_comp.union hC_comp
  have hinter_eq : K₁ ∩ K₂ = A₂ := by
    ext z
    simp only [K₁, K₂, C_ann]
    constructor
    · rintro ⟨hzJ, hzA₂ | ⟨_, hnot_ball⟩⟩
      · exact hzA₂
      · rw [← hA_union] at hzJ
        rcases hzJ with hz1 | hz2
        · exact False.elim (hnot_ball (hA₁_ball hz1))
        · exact hz2
    · intro hzA₂
      exact ⟨hA_union ▸ Or.inr hzA₂, Or.inl hzA₂⟩
  have hinter_conn : IsConnected (K₁ ∩ K₂) := hinter_eq.symm ▸ hA₂_conn
  have hd_pos : 0 < Metric.infDist β A₂ :=
    (hA₂_comp.isClosed.notMem_iff_infDist_pos hA₂_conn.nonempty).mp hβ_not_A₂
  let δ : ℝ := min ε (Metric.infDist β A₂)
  have hδ_pos : 0 < δ := lt_min hε hd_pos
  have hball_sub_K₂c : ball β δ ⊆ K₂ᶜ := by
    intro w hw
    have hw_ε : w ∈ ball β ε := ball_subset_ball (min_le_left _ _) hw
    have hw_d : dist β w < Metric.infDist β A₂ := by
      rw [dist_comm]
      exact lt_of_lt_of_le (mem_ball.mp hw) (min_le_right _ _)
    rintro (hwA₂ | ⟨_, hnot_ε⟩)
    · exact not_lt_of_ge (Metric.infDist_le_dist_of_mem hwA₂) hw_d
    · exact hnot_ε hw_ε
  refine ⟨δ, hδ_pos, ?_⟩
  rintro z₁ ⟨hz₁U, hz₁_δ⟩ z₂ ⟨hz₂U, hz₂_δ⟩
  have hz₁_K₁c : z₁ ∈ K₁ᶜ := connectedComponentIn_subset Jᶜ a hz₁U
  have hz₂_K₁c : z₂ ∈ K₁ᶜ := connectedComponentIn_subset Jᶜ a hz₂U
  have hz₁_K₂c : z₁ ∈ K₂ᶜ := hball_sub_K₂c hz₁_δ
  have hz₂_K₂c : z₂ ∈ K₂ᶜ := hball_sub_K₂c hz₂_δ
  have hz₁_union_c : z₁ ∈ (K₁ ∪ K₂)ᶜ := fun h => h.elim hz₁_K₁c hz₁_K₂c
  have hz₂_union_c : z₂ ∈ (K₁ ∪ K₂)ᶜ := fun h => h.elim hz₂_K₁c hz₂_K₂c
  have hcomp1 : z₂ ∈ connectedComponentIn K₁ᶜ z₁ := by
    have heq := connectedComponentIn_eq hz₁U
    change z₂ ∈ connectedComponentIn Jᶜ z₁
    rwa [← heq]
  have hcomp2 : z₂ ∈ connectedComponentIn K₂ᶜ z₁ :=
    (convex_ball β δ).isPreconnected.subset_connectedComponentIn hz₁_δ hball_sub_K₂c hz₂_δ
  have hcomp12 : z₂ ∈ connectedComponentIn (K₁ ∪ K₂)ᶜ z₁ :=
    janiszewski_connectedComponentIn hJ_comp hK₂_comp hinter_conn
      hz₁_union_c hz₂_union_c hcomp1 hcomp2
  let W : Set ℂ := connectedComponentIn (K₁ ∪ K₂)ᶜ z₁
  have hW_open : IsOpen W := (hJ_comp.union hK₂_comp).isClosed.isOpen_compl.connectedComponentIn
  have hW_conn : IsConnected W := isConnected_connectedComponentIn_iff.mpr hz₁_union_c
  have hW_pc : IsPathConnected W := hW_open.isConnected_iff_isPathConnected.mp hW_conn
  obtain ⟨γ_path, hγ_in_W⟩ := hW_pc.joinedIn z₁ (mem_connectedComponentIn hz₁_union_c) z₂ hcomp12
  have hW_sub_U : W ⊆ U := by
    have hW_sub_Jc : W ⊆ Jᶜ :=
      (connectedComponentIn_subset (K₁ ∪ K₂)ᶜ z₁).trans
        (Set.compl_subset_compl.mpr Set.subset_union_left)
    have heq := connectedComponentIn_eq hz₁U
    change W ⊆ connectedComponentIn Jᶜ a
    rw [heq]
    exact hW_conn.isPreconnected.subset_connectedComponentIn
      (mem_connectedComponentIn hz₁_union_c) hW_sub_Jc
  have hW_sub_ball : W ⊆ ball β ε := by
    intro w hw
    have hw_U : w ∈ U := hW_sub_U hw
    have hw_cb : w ∈ closedBall β R :=
      ball_subset_closedBall (hclU_sub (subset_closure hw_U))
    have hw_not_K₂ : w ∉ K₂ := fun h =>
      connectedComponentIn_subset (K₁ ∪ K₂)ᶜ z₁ hw (Or.inr h)
    by_contra hnot_ε
    exact hw_not_K₂ (Or.inr ⟨hw_cb, hnot_ε⟩)
  exact ⟨γ_path, fun t => ⟨hW_sub_U (hγ_in_W t), hW_sub_ball (hγ_in_W t)⟩⟩

/-- Every boundary point `β ∈ J` of a bounded connected component `U` of `Jᶜ` is simple in
Rudin's whole-sequence interpolation sense (`14.16`). -/
theorem jordanCurve_bounded_component_all_simple {J : Set ℂ} (hJ : IsJordanCurve J)
    {a : ℂ} (ha : a ∈ Jᶜ) (hbdd : Bornology.IsBounded (connectedComponentIn Jᶜ a)) :
    ∀ β ∈ frontier (connectedComponentIn Jᶜ a),
      IsSimpleBoundaryPoint (connectedComponentIn Jᶜ a) β := by
  let U : Set ℂ := connectedComponentIn Jᶜ a
  have hfr_eq : frontier U = J := jordanCurve_component_frontier_eq hJ ha
  have hJ_comp : IsCompact J := isCompact_of_isJordanCurve hJ
  obtain ⟨hU_open, _⟩ := isOpen_and_frontier_subset_of_connectedComponentIn_compl hJ_comp.isClosed (a := a)
  have hU_conn : IsConnected U := isConnected_connectedComponentIn_iff.mpr ha
  have hU_pc : IsPathConnected U := hU_open.isConnected_iff_isPathConnected.mp hU_conn
  intro β hβ_fr
  have hβ_J : β ∈ J := hfr_eq ▸ hβ_fr
  refine ⟨hβ_fr, fun α hα_in hα_lim => ?_⟩
  -- For each `m : ℕ`, get `δ m > 0` for radius `1 / (m + 1 : ℝ)`
  have hex_δ : ∀ m : ℕ, ∃ δ > 0, ∀ z₁ ∈ U ∩ ball β δ, ∀ z₂ ∈ U ∩ ball β δ,
      JoinedIn (U ∩ ball β (1 / ((m : ℝ) + 1))) z₁ z₂ :=
    fun m => jordanCurve_bounded_component_locally_joined hJ ha hbdd hβ_J (by positivity)
  choose δ hδ_pos hδ_join using hex_δ
  -- For each `n : ℕ`, choose a path `p n : Path (α n) (α (n + 1))` in `U`, staying inside the
  -- smallest `ball β (1 / (m + 1))` (`m ≤ n`) whose `δ m`-ball contains both `α n` and `α (n + 1)`
  classical
  let goodSet : ℕ → Finset ℕ := fun n =>
    (Finset.range (n + 1)).filter fun m => α n ∈ ball β (δ m) ∧ α (n + 1) ∈ ball β (δ m)
  have hex_path : ∀ n : ℕ, ∃ p : Path (α n) (α (n + 1)),
      (∀ s, p s ∈ U) ∧
      ∀ m ≤ n, α n ∈ ball β (δ m) → α (n + 1) ∈ ball β (δ m) →
        ∀ s, p s ∈ ball β (1 / ((m : ℝ) + 1)) := by
    intro n
    by_cases hne : (goodSet n).Nonempty
    · let m_max : ℕ := (goodSet n).max' hne
      have hm_mem : m_max ∈ goodSet n := Finset.max'_mem (goodSet n) hne
      simp only [goodSet, Finset.mem_filter, Finset.mem_range] at hm_mem
      obtain ⟨p, hp_in⟩ :=
        hδ_join m_max (α n) ⟨hα_in n, hm_mem.2.1⟩ (α (n + 1)) ⟨hα_in (n + 1), hm_mem.2.2⟩
      refine ⟨p, fun s => (hp_in s).1, fun m hm h1 h2 s => ?_⟩
      have hm_good : m ∈ goodSet n := by
        simp only [goodSet, Finset.mem_filter, Finset.mem_range]
        exact ⟨Nat.lt_succ_of_le hm, h1, h2⟩
      have hm_le_max : m ≤ m_max := Finset.le_max' (goodSet n) m hm_good
      have hrad_le : 1 / ((m_max : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right hm_le_max 1
      exact ball_subset_ball hrad_le (hp_in s).2
    · obtain ⟨p, hp_in⟩ := hU_pc.joinedIn (α n) (hα_in n) (α (n + 1)) (hα_in (n + 1))
      refine ⟨p, hp_in, fun m hm h1 h2 _ => ?_⟩
      exfalso
      apply hne
      refine ⟨m, ?_⟩
      simp only [goodSet, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le hm, h1, h2⟩
  choose p hp_U hp_ball using hex_path
  -- Parameterize `t n := 1 - (1 / 2) ^ (n + 1)` (`t 0 = 1 / 2`, strictly increasing to `1`)
  let t : ℕ → ℝ := fun n => 1 - (1 / 2 : ℝ) ^ (n + 1)
  have ht_mono : StrictMono t := by
    intro n₁ n₂ hlt
    dsimp [t]
    have hpow : (1 / 2 : ℝ) ^ (n₂ + 1) < (1 / 2 : ℝ) ^ (n₁ + 1) := by
      rw [one_div, inv_pow, inv_pow]
      exact (inv_lt_inv₀ (by positivity) (by positivity)).mpr
        (pow_lt_pow_right₀ one_lt_two (Nat.add_lt_add_right hlt 1))
    linarith
  have ht_in : ∀ n : ℕ, t n ∈ Ioo (0 : ℝ) 1 := by
    intro n
    dsimp [t]
    have hpos : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity
    have hle : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 / 2 := by
      have h1 : (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ (1 : ℕ) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      simpa using h1
    exact ⟨by linarith, by linarith⟩
  have ht_lim : Tendsto t atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_add_atTop_nat 1)
    have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
    simpa [t, one_div] using h1
  -- Define `γ s`: constant `α 0` on `s ≤ 1/2`, `p n` on `[t n, t (n + 1)]`, and `β` on `s ≥ 1`
  let segParam : ℕ → ℝ → unitInterval := fun n s =>
    Set.projIcc 0 1 zero_le_one ((s - t n) / (t (n + 1) - t n))
  let γ : ℝ → ℂ := fun s =>
    if s ≤ t 0 then α 0
    else if hs1 : s < 1 then
      let n := Nat.find (show ∃ k : ℕ, s ≤ t (k + 1) by
        obtain ⟨k, hk⟩ := (ht_lim.eventually (Ioi_mem_nhds hs1)).exists
        exact ⟨k, le_trans (Set.mem_Ioi.mp hk).le (ht_mono (Nat.lt_succ_self k)).le⟩)
      p n (segParam n s)
    else β
  have ht_step_pos : ∀ n : ℕ, 0 < t (n + 1) - t n := fun n => sub_pos.mpr (ht_mono (Nat.lt_succ_self n))
  -- Show `γ = p n ∘ segParam n` on `[t n, t (n + 1)]`!
  have hγ_on_seg : ∀ (n : ℕ) {s : ℝ}, s ∈ Icc (t n) (t (n + 1)) → γ s = p n (segParam n s) := by
    intro n s hs
    by_cases hs_t0 : s ≤ t 0
    · have hn0 : n = 0 := by
        by_contra hne0
        have ht0_lt : t 0 < t n := ht_mono (Nat.pos_of_ne_zero hne0)
        linarith [hs.1]
      subst hn0
      have hs_eq : s = t 0 := le_antisymm hs_t0 hs.1
      rw [hs_eq]
      simp only [γ, le_rfl, ↓reduceIte, segParam, sub_self, zero_div]
      have hproj0 : Set.projIcc 0 1 zero_le_one 0 = (0 : unitInterval) := by
        ext; simp
      rw [hproj0, Path.source]
    · have hs_lt1 : s < 1 := lt_of_le_of_lt hs.2 (ht_in (n + 1)).2
      simp only [γ, hs_t0, ↓reduceIte, hs_lt1, ↓reduceDIte]
      set k := Nat.find (show ∃ k : ℕ, s ≤ t (k + 1) from ⟨n, hs.2⟩)
      have hk_spec : s ≤ t (k + 1) := Nat.find_spec (⟨n, hs.2⟩ : ∃ k : ℕ, s ≤ t (k + 1))
      have hk_le_n : k ≤ n := Nat.find_min' _ hs.2
      by_cases hkn : k = n
      · rw [hkn]
      · have hk_lt_n : k + 1 ≤ n := Nat.succ_le_of_lt (lt_of_le_of_ne hk_le_n hkn)
        have htk1_le_tn : t (k + 1) ≤ t n :=
          if h_eq : k + 1 = n then h_eq ▸ le_rfl else (ht_mono (lt_of_le_of_ne hk_lt_n h_eq)).le
        have hs_eq : s = t (k + 1) := le_antisymm hk_spec (le_trans htk1_le_tn hs.1)
        have hkn1 : k + 1 = n := by
          by_contra hne
          have hlt := ht_mono (lt_of_le_of_ne hk_lt_n hne)
          linarith [hs.1, hk_spec]
        rw [← hkn1, hs_eq]
        have hproj1 : segParam k (t (k + 1)) = (1 : unitInterval) := by
          ext
          dsimp [segParam]
          rw [div_self (ht_step_pos k).ne']
          exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one (right_mem_Icc.mpr zero_le_one))
        have hproj0 : segParam (k + 1) (t (k + 1)) = (0 : unitInterval) := by
          ext
          dsimp [segParam]
          rw [sub_self, zero_div]
          exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one (left_mem_Icc.mpr zero_le_one))
        rw [hproj1, hproj0, Path.target, Path.source]
  -- Evaluate `γ (t n) = α n`
  have hγ_tn : ∀ n : ℕ, γ (t n) = α n := by
    intro n
    rw [hγ_on_seg n ⟨le_rfl, (ht_mono (Nat.lt_succ_self n)).le⟩]
    have hproj0 : segParam n (t n) = (0 : unitInterval) := by
      ext
      dsimp [segParam]
      rw [sub_self, zero_div]
      exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one (left_mem_Icc.mpr zero_le_one))
    rw [hproj0, Path.source]
  -- Membership `γ s ∈ U` for `s ∈ [0, 1)`
  have hγ_in_U : ∀ s ∈ Ico (0 : ℝ) 1, γ s ∈ U := by
    intro s hs
    by_cases hs0 : s ≤ t 0
    · simp only [γ, hs0, ↓reduceIte]; exact hα_in 0
    · simp only [γ, hs0, ↓reduceIte, hs.2, ↓reduceDIte]
      exact hp_U _ _
  -- Continuity of `γ` on `[0, 1)`
  have hseg_cont : ∀ n : ℕ, Continuous (fun s : ℝ => p n (segParam n s)) := fun n =>
    (p n).continuous.comp (continuous_projIcc.comp ((continuous_id.sub continuous_const).div_const _))
  have hγ_cont_Ico : ContinuousOn γ (Ico (0 : ℝ) 1) := by
    intro s₀ hs₀
    by_cases hs₀_lt0 : s₀ < t 0
    · have hev : γ =ᶠ[𝓝 s₀] fun _ => α 0 := by
        filter_upwards [Iio_mem_nhds hs₀_lt0] with s hs
        have hslt : s ≤ t 0 := le_of_lt (Set.mem_Iio.mp hs)
        simp only [γ, hslt, ↓reduceIte]
      exact (continuousAt_const.congr hev.symm).continuousWithinAt
    · obtain ⟨N, hN⟩ := (ht_lim.eventually (Ioi_mem_nhds hs₀.2)).exists
      have hN_le : s₀ ≤ t (N + 1) :=
        le_trans (Set.mem_Ioi.mp hN).le (ht_mono (Nat.lt_succ_self N)).le
      -- On `Iio (t (N + 1))`, check continuity at `s₀`
      by_cases hs₀_eq0 : s₀ = t 0
      · rw [hs₀_eq0, Metric.continuousWithinAt_iff]
        intro ε hε
        obtain ⟨η, hη_pos, hη⟩ :=
          Metric.continuousAt_iff.mp ((hseg_cont 0).continuousAt (x := t 0)) ε hε
        let δ' := min η (t 1 - t 0)
        refine ⟨δ', lt_min hη_pos (ht_step_pos 0), fun s _ hdist => ?_⟩
        by_cases hs_le : s ≤ t 0
        · simp [γ, hs_le, hε]
        · have hs_icc : s ∈ Icc (t 0) (t 1) := by
            have hd := Real.dist_eq s (t 0) ▸ lt_of_lt_of_le hdist (min_le_right _ _)
            exact ⟨le_of_not_ge hs_le, by linarith [(abs_lt.mp hd).2]⟩
          rw [hγ_on_seg 0 hs_icc, hγ_on_seg 0 ⟨le_rfl, (ht_mono zero_lt_one).le⟩]
          exact hη (lt_of_lt_of_le hdist (min_le_left _ _))
      · have hs₀_gt0 : t 0 < s₀ := lt_of_le_of_ne (not_lt.mp hs₀_lt0) (Ne.symm hs₀_eq0)
        -- Pick unique `k` with `t k < s₀ ≤ t (k + 1)`
        let k := Nat.find (⟨N, hN_le⟩ : ∃ m : ℕ, s₀ ≤ t (m + 1))
        have hk_le : s₀ ≤ t (k + 1) := Nat.find_spec (⟨N, hN_le⟩ : ∃ m : ℕ, s₀ ≤ t (m + 1))
        have htk_lt : t k < s₀ := by
          rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
          · rw [hk0]; exact hs₀_gt0
          · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk_pos.ne'
            have hjk : j < k := by omega
            rw [hj]
            exact not_le.mp (Nat.find_min (⟨N, hN_le⟩ : ∃ m : ℕ, s₀ ≤ t (m + 1)) hjk)
        by_cases hs₀_lt_k1 : s₀ < t (k + 1)
        · have hev : γ =ᶠ[𝓝 s₀] fun s => p k (segParam k s) := by
            filter_upwards [Ioo_mem_nhds htk_lt hs₀_lt_k1] with s hs
            exact hγ_on_seg k ⟨hs.1.le, hs.2.le⟩
          exact ((hseg_cont k).continuousAt.congr hev.symm).continuousWithinAt
        · have hs₀_eq : s₀ = t (k + 1) := le_antisymm hk_le (not_lt.mp hs₀_lt_k1)
          rw [hs₀_eq, Metric.continuousWithinAt_iff]
          intro ε hε
          obtain ⟨η₁, hη₁_pos, hη₁⟩ := Metric.continuousAt_iff.mp (hseg_cont k).continuousAt ε hε
          obtain ⟨η₂, hη₂_pos, hη₂⟩ :=
            Metric.continuousAt_iff.mp (hseg_cont (k + 1)).continuousAt ε hε
          let δ' := min (min η₁ η₂) (min (t (k + 1) - t k) (t (k + 2) - t (k + 1)))
          have hδ'_pos : 0 < δ' := lt_min (lt_min hη₁_pos hη₂_pos)
            (lt_min (ht_step_pos k) (ht_step_pos (k + 1)))
          refine ⟨δ', hδ'_pos, fun s _ hdist => ?_⟩
          rcases le_or_gt s (t (k + 1)) with hs_le | hs_gt
          · have hd : |s - t (k + 1)| < t (k + 1) - t k := by
              rw [← Real.dist_eq]
              exact lt_of_lt_of_le hdist (le_trans (min_le_right _ _) (min_le_left _ _))
            have hs_icc : s ∈ Icc (t k) (t (k + 1)) :=
              ⟨by linarith [(abs_lt.mp hd).1], hs_le⟩
            rw [hγ_on_seg k hs_icc, hγ_on_seg k ⟨(ht_mono (Nat.lt_succ_self k)).le, le_rfl⟩]
            exact hη₁ (lt_of_lt_of_le hdist (le_trans (min_le_left _ _) (min_le_left _ _)))
          · have hd : |s - t (k + 1)| < t (k + 2) - t (k + 1) := by
              rw [← Real.dist_eq]
              exact lt_of_lt_of_le hdist (le_trans (min_le_right _ _) (min_le_right _ _))
            have hs_icc : s ∈ Icc (t (k + 1)) (t (k + 2)) :=
              ⟨hs_gt.le, by linarith [(abs_lt.mp hd).2]⟩
            rw [hγ_on_seg (k + 1) hs_icc,
              hγ_on_seg (k + 1) ⟨le_rfl, (ht_mono (Nat.lt_succ_self (k + 1))).le⟩]
            exact hη₂ (lt_of_lt_of_le hdist (le_trans (min_le_left _ _) (min_le_right _ _)))
  -- Continuity of `γ` at `s = 1`
  have hγ_1 : γ 1 = β := by
    have hnot0 : ¬ (1 : ℝ) ≤ t 0 := not_le.mpr (ht_in 0).2
    simp [γ, hnot0]
  have hγ_lim1 : Tendsto γ (𝓝[<] (1 : ℝ)) (𝓝 β) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
    have hrad_lt : 1 / ((m : ℝ) + 1) < ε := by
      have hm_pos : 0 < (m : ℝ) + 1 := by positivity
      rw [div_lt_iff₀ hm_pos]
      have h1 : 1 < (m : ℝ) * ε := (div_lt_iff₀ hε).mp hm
      linarith
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hα_lim (δ m) (hδ_pos m)
    let N : ℕ := max N₀ m
    refine ⟨1 - t N, sub_pos.mpr (ht_in N).2, fun s hs_lt1 hdist => ?_⟩
    rw [Set.mem_Iio] at hs_lt1
    have hs_gt_tN : t N < s := by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hs_lt1)] at hdist
      linarith
    have hs_gt_t0 : ¬ s ≤ t 0 := not_le.mpr (lt_of_le_of_lt
      (if h0 : N = 0 then h0 ▸ le_rfl else (ht_mono (Nat.pos_of_ne_zero h0)).le) hs_gt_tN)
    obtain ⟨k_ex, hk_ex⟩ := (ht_lim.eventually (Ioi_mem_nhds hs_lt1)).exists
    have hk_ex_le : s ≤ t (k_ex + 1) :=
      le_trans (Set.mem_Ioi.mp hk_ex).le (ht_mono (Nat.lt_succ_self k_ex)).le
    let k := Nat.find (⟨k_ex, hk_ex_le⟩ : ∃ j : ℕ, s ≤ t (j + 1))
    have hk_spec : s ≤ t (k + 1) := Nat.find_spec (⟨k_ex, hk_ex_le⟩ : ∃ j : ℕ, s ≤ t (j + 1))
    have hN_le_k : N ≤ k := by
      by_contra hlt
      have hk1_le_N : k + 1 ≤ N := Nat.succ_le_of_lt (not_le.mp hlt)
      have htk1_le_tN : t (k + 1) ≤ t N :=
        if heq : k + 1 = N then heq ▸ le_rfl else (ht_mono (lt_of_le_of_ne hk1_le_N heq)).le
      linarith
    have hγs_eq : γ s = p k (segParam k s) := by
      simp only [γ, hs_gt_t0, ↓reduceIte, hs_lt1, ↓reduceDIte]
      rfl
    rw [hγs_eq]
    have hm_le_k : m ≤ k := le_trans (le_max_right _ _) hN_le_k
    have hN₀_le_k : N₀ ≤ k := le_trans (le_max_left _ _) hN_le_k
    have hαk : α k ∈ ball β (δ m) := hN₀ k hN₀_le_k
    have hαk1 : α (k + 1) ∈ ball β (δ m) := hN₀ (k + 1) (Nat.le_succ_of_le hN₀_le_k)
    have hp_in_ball := hp_ball k m hm_le_k hαk hαk1 (segParam k s)
    exact lt_trans (mem_ball.mp hp_in_ball) hrad_lt
  have hγ_cont_Icc : ContinuousOn γ (Icc (0 : ℝ) 1) := by
    intro s hs
    rcases eq_or_lt_of_le hs.2 with rfl | hslt
    · rw [ContinuousWithinAt, hγ_1, Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨δ', hδ'_pos, hδ'⟩ := Metric.tendsto_nhdsWithin_nhds.mp hγ_lim1 ε hε
      refine ⟨δ', hδ'_pos, fun x hx hdist => ?_⟩
      rcases eq_or_lt_of_le hx.2 with rfl | hxlt
      · simp [hγ_1, hε]
      · exact hδ' hxlt hdist
    · have hc := hγ_cont_Ico s ⟨hs.1, hslt⟩
      have hnhds_eq : 𝓝[Icc (0 : ℝ) 1] s = 𝓝[Ico (0 : ℝ) 1] s := by
        apply nhdsWithin_eq_nhdsWithin' (Iio_mem_nhds hslt)
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_Ico]
        exact ⟨fun ⟨⟨h1, _⟩, h3⟩ => ⟨⟨h1, h3⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h2.le⟩, h3⟩⟩
      rw [ContinuousWithinAt, hnhds_eq]
      exact hc
  exact ⟨γ, hγ_cont_Icc, hγ_in_U, t, ht_mono, ht_in, ht_lim, hγ_tn⟩

/-- **Theorem (14.20(a) Jordan-Boundary Converse for Bounded Regions):**
If `Ω ⊆ ℂ` is a bounded region whose boundary `frontier Ω` is a Jordan curve, then `Ω` is
automatically simply connected (`BookSimplyConnected Ω`) and **every** boundary point
`β ∈ frontier Ω` is simple (`IsSimpleBoundaryPoint Ω β`). -/
theorem jordanBoundary_region_converse {Ω : Set ℂ}
    (hΩ_reg : RudinRCA.Chapter10.IsRegion Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    (hJ : IsJordanCurve (frontier Ω)) :
    RudinRCA.Chapter10.BookSimplyConnected Ω ∧
      ∀ β ∈ frontier Ω, IsSimpleBoundaryPoint Ω β := by
  let J : Set ℂ := frontier Ω
  obtain ⟨z₀, hz₀⟩ := hΩ_reg.2.nonempty
  have hΩ_sub_Jc : Ω ⊆ Jᶜ := by
    intro z hz hzJ
    dsimp [J] at hzJ
    rw [frontier, hΩ_reg.1.interior_eq] at hzJ
    exact hzJ.2 hz
  have hz₀_Jc : z₀ ∈ Jᶜ := hΩ_sub_Jc hz₀
  -- Show `Ω = connectedComponentIn Jᶜ z₀` (since `Ω` is connected and clopen in `Jᶜ`)
  have hΩ_eq_comp : Ω = connectedComponentIn Jᶜ z₀ := by
    refine Set.Subset.antisymm
      (hΩ_reg.2.isPreconnected.subset_connectedComponentIn hz₀ hΩ_sub_Jc) ?_
    let U : Set ℂ := connectedComponentIn Jᶜ z₀
    have hU_conn : IsConnected U := isConnected_connectedComponentIn_iff.mpr hz₀_Jc
    have hdiff_open : IsOpen (Jᶜ \ Ω) := by
      have heq : Jᶜ \ Ω = Jᶜ \ closure Ω := by
        ext w
        constructor
        · rintro ⟨hwJc, hwnΩ⟩
          refine ⟨hwJc, fun hwcl => hwJc ?_⟩
          dsimp [J]
          rw [frontier, hΩ_reg.1.interior_eq]
          exact ⟨hwcl, hwnΩ⟩
        · rintro ⟨hwJc, hwncl⟩
          exact ⟨hwJc, fun hwΩ => hwncl (subset_closure hwΩ)⟩
      rw [heq]
      exact (isCompact_of_isJordanCurve hJ).isClosed.isOpen_compl.sdiff isClosed_closure
    intro w hwU
    by_contra hwnΩ
    have hwJc : w ∈ Jᶜ := connectedComponentIn_subset Jᶜ z₀ hwU
    have hcov : U ⊆ Ω ∪ (Jᶜ \ Ω) := fun y hy => by
      by_cases h : y ∈ Ω
      · exact Or.inl h
      · exact Or.inr ⟨connectedComponentIn_subset Jᶜ z₀ hy, h⟩
    rcases hU_conn.isPreconnected Ω (Jᶜ \ Ω) hΩ_reg.1 hdiff_open hcov
      ⟨z₀, mem_connectedComponentIn hz₀_Jc, hz₀⟩ ⟨w, hwU, hwJc, hwnΩ⟩ with
      ⟨q, _, hqΩ, _, hqnΩ⟩
    exact hqnΩ hqΩ
  have hcomp_bdd : Bornology.IsBounded (connectedComponentIn Jᶜ z₀) := hΩ_eq_comp ▸ hΩ_bdd
  have hsc := jordanCurve_bounded_component_simplyConnected hJ hz₀_Jc hcomp_bdd
  have hsimp := jordanCurve_bounded_component_all_simple hJ hz₀_Jc hcomp_bdd
  rw [← hΩ_eq_comp] at hsc hsimp
  exact ⟨hsc, hsimp⟩

/-! ### Part 14.20(b) Core: Positive Cyclic Order on `sphere 0 1` and Disk Automorphism 3-Transitivity -/

/-- Positive (counterclockwise) cyclic order of three points `(w₁, w₂, w₃)` on the unit circle
`sphere (0 : ℂ) 1`: all three lie on `sphere 0 1` and possess real arguments `θ₁ < θ₂ < θ₃ < θ₁ + 2π`
with `w_k = exp(i θ_k)`. -/
def UnitCirclePosCyclic (w₁ w₂ w₃ : ℂ) : Prop :=
  w₁ ∈ sphere (0 : ℂ) 1 ∧ w₂ ∈ sphere (0 : ℂ) 1 ∧ w₃ ∈ sphere (0 : ℂ) 1 ∧
  ∃ θ₁ θ₂ θ₃ : ℝ, θ₁ < θ₂ ∧ θ₂ < θ₃ ∧ θ₃ < θ₁ + 2 * Real.pi ∧
    w₁ = Complex.exp ((θ₁ : ℂ) * Complex.I) ∧
    w₂ = Complex.exp ((θ₂ : ℂ) * Complex.I) ∧
    w₃ = Complex.exp ((θ₃ : ℂ) * Complex.I)

/-- Continuous real-valued cyclic orientation determinant on `sphere (0 : ℂ) 1`:
`Im ((w₃ / w₁ - 1) * conj (w₂ / w₁ - 1))`. -/
def unitCircleCyclicDet (w₁ w₂ w₃ : ℂ) : ℝ :=
  ((w₃ / w₁ - 1) * starRingEnd ℂ (w₂ / w₁ - 1)).im

/-- Trigonometric factorization of `unitCircleCyclicDet`:
for `u₂ = exp(i φ₂)` and `u₃ = exp(i φ₃)`,
`Im ((u₃ - 1) * conj (u₂ - 1)) = 4 * sin(φ₂ / 2) * sin(φ₃ / 2) * sin((φ₃ - φ₂) / 2)`. -/
theorem unitCircleCyclicDet_exp_formula (φ₂ φ₃ : ℝ) :
    ((Complex.exp ((φ₃ : ℂ) * Complex.I) - 1) *
      starRingEnd ℂ (Complex.exp ((φ₂ : ℂ) * Complex.I) - 1)).im =
    4 * Real.sin (φ₂ / 2) * Real.sin (φ₃ / 2) * Real.sin ((φ₃ - φ₂) / 2) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [map_sub, map_add, map_mul, map_one, Complex.conj_ofReal, Complex.conj_I,
    Complex.mul_im, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.sub_im, Complex.add_im,
    Complex.ofReal_im, Complex.one_im, Complex.neg_re, Complex.neg_im]
  set a : ℝ := φ₂ / 2
  set b : ℝ := φ₃ / 2
  have hφ₂ : φ₂ = 2 * a := by dsimp [a]; ring
  have hφ₃ : φ₃ = 2 * b := by dsimp [b]; ring
  have hdiff : (2 * b - 2 * a) / 2 = b - a := by ring
  rw [hφ₂, hφ₃, hdiff, Real.sin_two_mul, Real.sin_two_mul,
    Real.cos_two_mul, Real.cos_two_mul, Real.sin_sub]
  have ha_sq : Real.cos a ^ 2 = 1 - Real.sin a ^ 2 := by linarith [Real.sin_sq_add_cos_sq a]
  have hb_sq : Real.cos b ^ 2 = 1 - Real.sin b ^ 2 := by linarith [Real.sin_sq_add_cos_sq b]
  rw [ha_sq, hb_sq]
  ring

/-- Every `u ∈ sphere (0 : ℂ) 1` with `u ≠ 1` has a representation `u = exp(i φ)` with
`φ ∈ Ioo 0 (2 * π)`. -/
theorem exists_angle_Ioo_two_pi_of_mem_sphere_ne_one {u : ℂ}
    (hu : u ∈ sphere (0 : ℂ) 1) (hne : u ≠ 1) :
    ∃ φ ∈ Ioo (0 : ℝ) (2 * Real.pi), u = Complex.exp ((φ : ℂ) * Complex.I) := by
  have hu_norm : ‖u‖ = 1 := by simpa using hu
  have hneg_norm : ‖-u‖ = 1 := by rw [norm_neg, hu_norm]
  have hexp_neg : Complex.exp ((Complex.arg (-u) : ℂ) * Complex.I) = -u := by
    have h := Complex.norm_mul_exp_arg_mul_I (-u)
    rwa [hneg_norm, Complex.ofReal_one, one_mul] at h
  have harg_gt : -Real.pi < Complex.arg (-u) := Complex.neg_pi_lt_arg (-u)
  have harg_lt : Complex.arg (-u) < Real.pi := by
    refine lt_of_le_of_ne (Complex.arg_le_pi (-u)) fun heq => hne ?_
    rw [heq, Complex.exp_pi_mul_I] at hexp_neg
    exact neg_injective hexp_neg.symm
  refine ⟨Complex.arg (-u) + Real.pi, ⟨by linarith, by linarith⟩, ?_⟩
  push_cast
  rw [add_mul, Complex.exp_add, hexp_neg, Complex.exp_pi_mul_I]
  ring

/-- Algebraic-sign characterization of `UnitCirclePosCyclic`:
for any `w₁, w₂, w₃ : ℂ`, `UnitCirclePosCyclic w₁ w₂ w₃` holds if and only if all three lie on
`sphere 0 1` and `0 < unitCircleCyclicDet w₁ w₂ w₃`. -/
theorem unitCirclePosCyclic_iff_det_pos {w₁ w₂ w₃ : ℂ} :
    UnitCirclePosCyclic w₁ w₂ w₃ ↔
      w₁ ∈ sphere (0 : ℂ) 1 ∧ w₂ ∈ sphere (0 : ℂ) 1 ∧ w₃ ∈ sphere (0 : ℂ) 1 ∧
      0 < unitCircleCyclicDet w₁ w₂ w₃ := by
  constructor
  · rintro ⟨hw₁, hw₂, hw₃, θ₁, θ₂, θ₃, h12, h23, h31, rfl, rfl, rfl⟩
    refine ⟨hw₁, hw₂, hw₃, ?_⟩
    dsimp [unitCircleCyclicDet]
    have hdiv₂ : Complex.exp ((θ₂ : ℂ) * Complex.I) / Complex.exp ((θ₁ : ℂ) * Complex.I) =
        Complex.exp (((θ₂ - θ₁ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_sub]; congr 1; push_cast; ring
    have hdiv₃ : Complex.exp ((θ₃ : ℂ) * Complex.I) / Complex.exp ((θ₁ : ℂ) * Complex.I) =
        Complex.exp (((θ₃ - θ₁ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_sub]; congr 1; push_cast; ring
    rw [hdiv₂, hdiv₃, unitCircleCyclicDet_exp_formula]
    have hs₁ : 0 < Real.sin ((θ₂ - θ₁) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hs₂ : 0 < Real.sin ((θ₃ - θ₁) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hdiff_eq : (θ₃ - θ₁ - (θ₂ - θ₁)) / 2 = (θ₃ - θ₂) / 2 := by ring
    rw [hdiff_eq]
    have hs₃ : 0 < Real.sin ((θ₃ - θ₂) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    positivity
  · rintro ⟨hw₁, hw₂, hw₃, hdet⟩
    have hw₁_norm : ‖w₁‖ = 1 := by simpa using hw₁
    have hw₂_norm : ‖w₂‖ = 1 := by simpa using hw₂
    have hw₃_norm : ‖w₃‖ = 1 := by simpa using hw₃
    have hw₁_ne : w₁ ≠ 0 := by intro h0; simp [h0] at hw₁_norm
    have hne12 : w₂ / w₁ ≠ 1 := by
      intro h1
      dsimp [unitCircleCyclicDet] at hdet
      rw [h1, sub_self, map_zero, mul_zero, Complex.zero_im] at hdet
      exact lt_irrefl 0 hdet
    have hne13 : w₃ / w₁ ≠ 1 := by
      intro h1
      dsimp [unitCircleCyclicDet] at hdet
      rw [h1, sub_self, zero_mul, Complex.zero_im] at hdet
      exact lt_irrefl 0 hdet
    have hu₂_sph : w₂ / w₁ ∈ sphere (0 : ℂ) 1 := by simp [hw₁_norm, hw₂_norm]
    have hu₃_sph : w₃ / w₁ ∈ sphere (0 : ℂ) 1 := by simp [hw₁_norm, hw₃_norm]
    obtain ⟨φ₂, hφ₂_in, hu₂_eq⟩ := exists_angle_Ioo_two_pi_of_mem_sphere_ne_one hu₂_sph hne12
    obtain ⟨φ₃, hφ₃_in, hu₃_eq⟩ := exists_angle_Ioo_two_pi_of_mem_sphere_ne_one hu₃_sph hne13
    dsimp [unitCircleCyclicDet] at hdet
    rw [hu₂_eq, hu₃_eq, unitCircleCyclicDet_exp_formula] at hdet
    have hs₁ : 0 < Real.sin (φ₂ / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ₂_in.1]) (by linarith [hφ₂_in.2])
    have hs₂ : 0 < Real.sin (φ₃ / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ₃_in.1]) (by linarith [hφ₃_in.2])
    have hprod_pos : 0 < 4 * Real.sin (φ₂ / 2) * Real.sin (φ₃ / 2) := by positivity
    have hs₃ : 0 < Real.sin ((φ₃ - φ₂) / 2) := by
      by_contra hle
      have hle' : Real.sin ((φ₃ - φ₂) / 2) ≤ 0 := not_lt.mp hle
      have : 4 * Real.sin (φ₂ / 2) * Real.sin (φ₃ / 2) * Real.sin ((φ₃ - φ₂) / 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hprod_pos.le hle'
      linarith
    have hφ₂_lt_φ₃ : φ₂ < φ₃ := by
      by_contra hge
      have hge' : φ₃ ≤ φ₂ := not_lt.mp hge
      rcases eq_or_lt_of_le hge' with rfl | hlt
      · simp at hs₃
      · have hpos_neg : 0 < Real.sin ((φ₂ - φ₃) / 2) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hφ₂_in.2, hφ₃_in.1])
        have hneg_eq : (φ₃ - φ₂) / 2 = -((φ₂ - φ₃) / 2) := by ring
        rw [hneg_eq, Real.sin_neg] at hs₃
        linarith
    let θ₁ : ℝ := Complex.arg w₁
    have hw₁_exp : w₁ = Complex.exp ((θ₁ : ℂ) * Complex.I) := by
      have h := Complex.norm_mul_exp_arg_mul_I w₁
      rw [hw₁_norm, Complex.ofReal_one, one_mul] at h
      exact h.symm
    refine ⟨hw₁, hw₂, hw₃, θ₁, θ₁ + φ₂, θ₁ + φ₃,
      by linarith [hφ₂_in.1], by linarith, by linarith [hφ₃_in.2], hw₁_exp, ?_, ?_⟩
    · calc
        w₂ = (w₂ / w₁) * w₁ := (div_mul_cancel₀ w₂ hw₁_ne).symm
        _ = Complex.exp ((φ₂ : ℂ) * Complex.I) * Complex.exp ((θ₁ : ℂ) * Complex.I) := by
          rw [hu₂_eq, ← hw₁_exp]
        _ = Complex.exp (((θ₁ + φ₂ : ℝ) : ℂ) * Complex.I) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring
    · calc
        w₃ = (w₃ / w₁) * w₁ := (div_mul_cancel₀ w₃ hw₁_ne).symm
        _ = Complex.exp ((φ₃ : ℂ) * Complex.I) * Complex.exp ((θ₁ : ℂ) * Complex.I) := by
          rw [hu₃_eq, ← hw₁_exp]
        _ = Complex.exp (((θ₁ + φ₃ : ℝ) : ℂ) * Complex.I) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem unitCircleCyclicDet_swap (w₁ w₂ w₃ : ℂ) :
    unitCircleCyclicDet w₁ w₃ w₂ = -unitCircleCyclicDet w₁ w₂ w₃ := by
  dsimp [unitCircleCyclicDet]
  have hconj : (w₂ / w₁ - 1) * (starRingEnd ℂ) (w₃ / w₁ - 1) =
      (starRingEnd ℂ) ((w₃ / w₁ - 1) * (starRingEnd ℂ) (w₂ / w₁ - 1)) := by
    simp [mul_comm]
  rw [hconj, Complex.conj_im]

theorem unitCirclePosCyclic_pairwise_ne {w₁ w₂ w₃ : ℂ} (h : UnitCirclePosCyclic w₁ w₂ w₃) :
    w₁ ≠ w₂ ∧ w₂ ≠ w₃ ∧ w₁ ≠ w₃ := by
  obtain ⟨_, _, _, hdet⟩ := unitCirclePosCyclic_iff_det_pos.mp h
  refine ⟨?_, ?_, ?_⟩
  · intro heq; subst heq
    dsimp [unitCircleCyclicDet] at hdet
    by_cases h0 : w₁ = 0 <;> simp [h0] at hdet
  · intro heq; subst heq
    dsimp [unitCircleCyclicDet] at hdet
    have hreal : ((w₂ / w₁ - 1) * (starRingEnd ℂ) (w₂ / w₁ - 1)).im = 0 := by
      rw [Complex.mul_conj]; exact Complex.ofReal_im _
    linarith
  · intro heq; subst heq
    dsimp [unitCircleCyclicDet] at hdet
    by_cases h0 : w₁ = 0 <;> simp [h0] at hdet

/-- Exclusive dichotomy for pairwise distinct triples on `sphere (0 : ℂ) 1`:
exactly one of `(w₁, w₂, w₃)` and `(w₁, w₃, w₂)` is positively cyclically ordered. -/
theorem unitCirclePosCyclic_dichotomy {w₁ w₂ w₃ : ℂ}
    (hw₁ : w₁ ∈ sphere (0 : ℂ) 1) (hw₂ : w₂ ∈ sphere (0 : ℂ) 1) (hw₃ : w₃ ∈ sphere (0 : ℂ) 1)
    (h12 : w₁ ≠ w₂) (h23 : w₂ ≠ w₃) (h13 : w₁ ≠ w₃) :
    UnitCirclePosCyclic w₁ w₂ w₃ ↔ ¬ UnitCirclePosCyclic w₁ w₃ w₂ := by
  rw [unitCirclePosCyclic_iff_det_pos, unitCirclePosCyclic_iff_det_pos,
    unitCircleCyclicDet_swap w₁ w₂ w₃]
  simp only [hw₁, hw₂, hw₃, true_and, Left.neg_pos_iff, not_lt]
  constructor
  · exact le_of_lt
  · intro hge
    refine lt_of_le_of_ne hge fun h0 => ?_
    have hw₁_norm : ‖w₁‖ = 1 := by simpa using hw₁
    have hw₂_norm : ‖w₂‖ = 1 := by simpa using hw₂
    have hw₃_norm : ‖w₃‖ = 1 := by simpa using hw₃
    have hw₁_ne : w₁ ≠ 0 := by intro hz; simp [hz] at hw₁_norm
    have hne12 : w₂ / w₁ ≠ 1 := fun h => h12 (by rw [div_eq_one_iff_eq hw₁_ne] at h; exact h.symm)
    have hne13 : w₃ / w₁ ≠ 1 := fun h => h13 (by rw [div_eq_one_iff_eq hw₁_ne] at h; exact h.symm)
    obtain ⟨φ₂, hφ₂_in, hu₂_eq⟩ := exists_angle_Ioo_two_pi_of_mem_sphere_ne_one
      (by simp [hw₁_norm, hw₂_norm]) hne12
    obtain ⟨φ₃, hφ₃_in, hu₃_eq⟩ := exists_angle_Ioo_two_pi_of_mem_sphere_ne_one
      (by simp [hw₁_norm, hw₃_norm]) hne13
    dsimp [unitCircleCyclicDet] at h0
    rw [hu₂_eq, hu₃_eq, unitCircleCyclicDet_exp_formula] at h0
    have hs₁ : Real.sin (φ₂ / 2) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ₂_in.1]) (by linarith [hφ₂_in.2])).ne'
    have hs₂ : Real.sin (φ₃ / 2) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ₃_in.1]) (by linarith [hφ₃_in.2])).ne'
    have hs₃_zero : Real.sin ((φ₃ - φ₂) / 2) = 0 := by
      have hprod : 4 * Real.sin (φ₂ / 2) * Real.sin (φ₃ / 2) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) hs₁) hs₂
      exact (mul_eq_zero.mp h0.symm).resolve_left hprod
    have hφ_eq : φ₂ = φ₃ := by
      by_contra hne_φ
      rcases lt_or_gt_of_ne hne_φ with hlt | hgt
      · exact (Real.sin_pos_of_pos_of_lt_pi (by linarith)
          (by linarith [hφ₂_in.1, hφ₃_in.2])).ne' hs₃_zero
      · have hpos := Real.sin_pos_of_pos_of_lt_pi (x := (φ₂ - φ₃) / 2) (by linarith)
          (by linarith [hφ₂_in.2, hφ₃_in.1])
        have hneg : (φ₃ - φ₂) / 2 = -((φ₂ - φ₃) / 2) := by ring
        rw [hneg, Real.sin_neg, neg_eq_zero] at hs₃_zero
        exact hpos.ne' hs₃_zero
    apply h23
    calc
      w₂ = (w₂ / w₁) * w₁ := (div_mul_cancel₀ w₂ hw₁_ne).symm
      _ = (w₃ / w₁) * w₁ := by rw [hu₂_eq, hu₃_eq, hφ_eq]
      _ = w₃ := div_mul_cancel₀ w₃ hw₁_ne

theorem unitCirclePosCyclic_rotate_triple {w₁ w₂ w₃ : ℂ} (h : UnitCirclePosCyclic w₁ w₂ w₃) :
    UnitCirclePosCyclic w₂ w₃ w₁ := by
  rcases h with ⟨hw₁, hw₂, hw₃, θ₁, θ₂, θ₃, h12, h23, h31, rfl, rfl, rfl⟩
  refine ⟨hw₂, hw₃, hw₁, θ₂, θ₃, θ₁ + 2 * Real.pi, h23, h31, by linarith, rfl, rfl, ?_⟩
  push_cast
  rw [add_mul, Complex.exp_add,
    show (2 : ℂ) * ↑Real.pi * Complex.I = 2 * Real.pi * Complex.I by ring,
    Complex.exp_two_pi_mul_I, mul_one]

theorem unitCirclePosCyclic_std : UnitCirclePosCyclic (-1) (-Complex.I) 1 := by
  refine ⟨by simp, by simp, by simp, -Real.pi, -(Real.pi / 2), 0,
    by linarith [Real.pi_pos], by linarith [Real.pi_pos], by linarith [Real.pi_pos], ?_, ?_, ?_⟩
  · rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  · rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  · simp

/-- Standard disk automorphism `ψ_{α, c}(z) = c * RudinRCA.Chapter12.phi α z` (`α ∈ ball 0 1`, `‖c‖ = 1`). -/
def diskAut (α c z : ℂ) : ℂ :=
  c * RudinRCA.Chapter12.phi α z

theorem diskAut_props {α c : ℂ} (hα : α ∈ ball (0 : ℂ) 1) (hc : ‖c‖ = 1) :
    ContinuousOn (diskAut α c) (closedBall (0 : ℂ) 1) ∧
    DifferentiableOn ℂ (diskAut α c) (ball (0 : ℂ) 1) ∧
    BijOn (diskAut α c) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) ∧
    BijOn (diskAut α c) (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1) ∧
    BijOn (diskAut α c) (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) ∧
    ∀ z ∈ closedBall (0 : ℂ) 1,
      RudinRCA.Chapter12.phi (-α) (c⁻¹ * diskAut α c z) = z ∧
      diskAut α c (RudinRCA.Chapter12.phi (-α) (c⁻¹ * z)) = z := by
  have hc_ne : c ≠ 0 := by intro h0; simp [h0] at hc
  obtain ⟨hphi_diff, _, hphi_sph, hphi_ball, hphi_inv, _, _⟩ := RudinRCA.Chapter12.theorem12_4 hα
  have hden_cb : closedBall (0 : ℂ) 1 ⊆ {z : ℂ | 1 - star α * z ≠ 0} := by
    intro z hz h0
    have hα_lt : ‖α‖ < 1 := mem_ball_zero_iff.mp hα
    have hz_le : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    have h1 : (1 : ℂ) = star α * z := sub_eq_zero.mp h0
    have hnorm : (1 : ℝ) = ‖α‖ * ‖z‖ := by
      have := congrArg norm h1; simpa [norm_mul] using this
    nlinarith [norm_nonneg α, norm_nonneg z]
  have hdiff_cb : DifferentiableOn ℂ (diskAut α c) {z : ℂ | 1 - star α * z ≠ 0} :=
    hphi_diff.const_mul c
  have hcont_cb : ContinuousOn (diskAut α c) (closedBall (0 : ℂ) 1) :=
    hdiff_cb.continuousOn.mono hden_cb
  have hdiff_ball : DifferentiableOn ℂ (diskAut α c) (ball (0 : ℂ) 1) :=
    hdiff_cb.mono (ball_subset_closedBall.trans hden_cb)
  have hinv : ∀ z ∈ closedBall (0 : ℂ) 1,
      RudinRCA.Chapter12.phi (-α) (c⁻¹ * diskAut α c z) = z ∧
      diskAut α c (RudinRCA.Chapter12.phi (-α) (c⁻¹ * z)) = z := by
    intro z hz
    have h1 : c⁻¹ * diskAut α c z = RudinRCA.Chapter12.phi α z := by
      dsimp [diskAut]; exact inv_mul_cancel_left₀ hc_ne _
    have hcz_cb : c⁻¹ * z ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff, norm_mul, norm_inv, hc, inv_one, one_mul]
      exact mem_closedBall_zero_iff.mp hz
    refine ⟨by rw [h1, (hphi_inv z hz).1], ?_⟩
    dsimp [diskAut]
    rw [(hphi_inv (c⁻¹ * z) hcz_cb).2, mul_inv_cancel_left₀ hc_ne]
  have hbij_ball : BijOn (diskAut α c) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    refine ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ heq => ?_, fun w hw => ?_⟩
    · rw [mem_ball_zero_iff]; dsimp [diskAut]; rw [norm_mul, hc, one_mul]
      exact mem_ball_zero_iff.mp (hphi_ball.mapsTo hz)
    · rw [← (hinv z₁ (ball_subset_closedBall hz₁)).1, heq,
        (hinv z₂ (ball_subset_closedBall hz₂)).1]
    · have hcw : c⁻¹ * w ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff, norm_mul, norm_inv, hc, inv_one, one_mul]
        exact mem_ball_zero_iff.mp hw
      obtain ⟨z, hz, hzw⟩ := hphi_ball.surjOn hcw
      refine ⟨z, hz, ?_⟩
      dsimp [diskAut]; rw [hzw, mul_inv_cancel_left₀ hc_ne]
  have hbij_sph : BijOn (diskAut α c) (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1) := by
    refine ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ heq => ?_, fun w hw => ?_⟩
    · rw [mem_sphere_zero_iff_norm]; dsimp [diskAut]; rw [norm_mul, hc, one_mul]
      exact mem_sphere_zero_iff_norm.mp (hphi_sph.mapsTo hz)
    · rw [← (hinv z₁ (sphere_subset_closedBall hz₁)).1, heq,
        (hinv z₂ (sphere_subset_closedBall hz₂)).1]
    · have hcw : c⁻¹ * w ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_mul, norm_inv, hc, inv_one, one_mul]
        exact mem_sphere_zero_iff_norm.mp hw
      obtain ⟨z, hz, hzw⟩ := hphi_sph.surjOn hcw
      refine ⟨z, hz, ?_⟩
      dsimp [diskAut]; rw [hzw, mul_inv_cancel_left₀ hc_ne]
  have hbij_cb : BijOn (diskAut α c) (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
    have hcb_eq : closedBall (0 : ℂ) 1 = ball (0 : ℂ) 1 ∪ sphere (0 : ℂ) 1 :=
      ball_union_sphere.symm
    refine ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ heq => ?_, fun w hw => ?_⟩
    · rw [hcb_eq] at hz ⊢
      exact hz.imp (fun h => hbij_ball.mapsTo h) (fun h => hbij_sph.mapsTo h)
    · rw [← (hinv z₁ hz₁).1, heq, (hinv z₂ hz₂).1]
    · rw [hcb_eq] at hw ⊢
      rcases hw with hw_b | hw_s
      · obtain ⟨z, hz, hzw⟩ := hbij_ball.surjOn hw_b
        exact ⟨z, Or.inl hz, hzw⟩
      · obtain ⟨z, hz, hzw⟩ := hbij_sph.surjOn hw_s
        exact ⟨z, Or.inr hz, hzw⟩
  exact ⟨hcont_cb, hdiff_ball, hbij_ball, hbij_sph, hbij_cb, hinv⟩

/-- Every disk automorphism `diskAut α c` (`α ∈ ball 0 1`, `‖c‖ = 1`) preserves
`UnitCirclePosCyclic`. -/
theorem diskAut_preserves_posCyclic {α c w₁ w₂ w₃ : ℂ}
    (hα : α ∈ ball (0 : ℂ) 1) (hc : ‖c‖ = 1) (hcyc : UnitCirclePosCyclic w₁ w₂ w₃) :
    UnitCirclePosCyclic (diskAut α c w₁) (diskAut α c w₂) (diskAut α c w₃) := by
  obtain ⟨_, _, _, hbij_sph, _, _⟩ := diskAut_props hα hc
  obtain ⟨h12, h23, h13⟩ := unitCirclePosCyclic_pairwise_ne hcyc
  obtain ⟨hw₁, hw₂, hw₃, hdet_pos⟩ := unitCirclePosCyclic_iff_det_pos.mp hcyc
  rw [unitCirclePosCyclic_iff_det_pos]
  refine ⟨hbij_sph.mapsTo hw₁, hbij_sph.mapsTo hw₂, hbij_sph.mapsTo hw₃, ?_⟩
  have hc_ne : c ≠ 0 := by intro h0; simp [h0] at hc
  have hdet_rot : ∀ β : ℂ,
      unitCircleCyclicDet (diskAut β c w₁) (diskAut β c w₂) (diskAut β c w₃) =
      unitCircleCyclicDet (RudinRCA.Chapter12.phi β w₁)
        (RudinRCA.Chapter12.phi β w₂) (RudinRCA.Chapter12.phi β w₃) := by
    intro β
    dsimp [unitCircleCyclicDet, diskAut]
    rw [mul_div_mul_left _ _ hc_ne, mul_div_mul_left _ _ hc_ne]
  rw [hdet_rot α]
  let g : ℂ → ℝ := fun β =>
    unitCircleCyclicDet (RudinRCA.Chapter12.phi β w₁)
      (RudinRCA.Chapter12.phi β w₂) (RudinRCA.Chapter12.phi β w₃)
  have hphi_cont : ∀ w ∈ sphere (0 : ℂ) 1,
      ContinuousOn (fun β : ℂ => RudinRCA.Chapter12.phi β w) (ball (0 : ℂ) 1) := by
    intro w hw
    have hw_norm : ‖w‖ = 1 := by simpa using hw
    have hden_ne : ∀ β ∈ ball (0 : ℂ) 1, 1 - star β * w ≠ 0 := by
      intro β hβ h0
      have hβ_lt : ‖β‖ < 1 := mem_ball_zero_iff.mp hβ
      have h1 : (1 : ℂ) = star β * w := sub_eq_zero.mp h0
      have hn : (1 : ℝ) = ‖β‖ := by
        have := congrArg norm h1; simpa [norm_mul, hw_norm] using this
      linarith
    dsimp only [RudinRCA.Chapter12.phi]
    exact (continuousOn_const.sub continuousOn_id).div
      (continuousOn_const.sub ((continuous_star.comp_continuousOn continuousOn_id).mul
        continuousOn_const)) hden_ne
  have hphi_ne_zero : ∀ β ∈ ball (0 : ℂ) 1, RudinRCA.Chapter12.phi β w₁ ≠ 0 := by
    intro β hβ h0
    have hs := (RudinRCA.Chapter12.theorem12_4 hβ).2.2.1.mapsTo hw₁
    rw [h0] at hs; simp at hs
  have hg_cont : ContinuousOn g (ball (0 : ℂ) 1) := by
    dsimp [g, unitCircleCyclicDet]
    have hc₂ : ContinuousOn (fun β => RudinRCA.Chapter12.phi β w₂ /
        RudinRCA.Chapter12.phi β w₁ - 1) (ball (0 : ℂ) 1) :=
      ((hphi_cont w₂ hw₂).div (hphi_cont w₁ hw₁) hphi_ne_zero).sub continuousOn_const
    have hc₃ : ContinuousOn (fun β => RudinRCA.Chapter12.phi β w₃ /
        RudinRCA.Chapter12.phi β w₁ - 1) (ball (0 : ℂ) 1) :=
      ((hphi_cont w₃ hw₃).div (hphi_cont w₁ hw₁) hphi_ne_zero).sub continuousOn_const
    exact Complex.continuous_im.comp_continuousOn
      (hc₃.mul (Complex.continuous_conj.comp_continuousOn hc₂))
  have hg_nz : ∀ β ∈ ball (0 : ℂ) 1, g β ≠ 0 := by
    intro β hβ h0
    obtain ⟨_, _, hβ_sph, _, _, _, _⟩ := RudinRCA.Chapter12.theorem12_4 hβ
    have hw₁' := hβ_sph.mapsTo hw₁
    have hw₂' := hβ_sph.mapsTo hw₂
    have hw₃' := hβ_sph.mapsTo hw₃
    have h12' : RudinRCA.Chapter12.phi β w₁ ≠ RudinRCA.Chapter12.phi β w₂ :=
      fun heq => h12 (hβ_sph.injOn hw₁ hw₂ heq)
    have h23' : RudinRCA.Chapter12.phi β w₂ ≠ RudinRCA.Chapter12.phi β w₃ :=
      fun heq => h23 (hβ_sph.injOn hw₂ hw₃ heq)
    have h13' : RudinRCA.Chapter12.phi β w₁ ≠ RudinRCA.Chapter12.phi β w₃ :=
      fun heq => h13 (hβ_sph.injOn hw₁ hw₃ heq)
    have hdich := unitCirclePosCyclic_dichotomy hw₁' hw₂' hw₃' h12' h23' h13'
    rw [unitCirclePosCyclic_iff_det_pos, unitCirclePosCyclic_iff_det_pos,
      unitCircleCyclicDet_swap (RudinRCA.Chapter12.phi β w₁)
        (RudinRCA.Chapter12.phi β w₂) (RudinRCA.Chapter12.phi β w₃)] at hdich
    simp only [hw₁', hw₂', hw₃', true_and, Left.neg_pos_iff] at hdich
    dsimp [g] at h0
    rw [h0] at hdich
    simp at hdich
  have hg0 : 0 < g 0 := by
    have hp0 : ∀ w : ℂ, RudinRCA.Chapter12.phi 0 w = w := fun w => by
      simp [RudinRCA.Chapter12.phi]
    simpa [g, hp0] using hdet_pos
  by_contra hle
  have hlt : g α < 0 := lt_of_le_of_ne (not_lt.mp hle) (hg_nz α hα)
  have himg_conn : IsPreconnected (g '' ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).isPreconnected.image g hg_cont
  have hcov : g '' ball (0 : ℂ) 1 ⊆ Iio (0 : ℝ) ∪ Ioi (0 : ℝ) := by
    rintro y ⟨β, hβ, rfl⟩
    exact (lt_or_gt_of_ne (hg_nz β hβ)).imp Set.mem_Iio.mpr Set.mem_Ioi.mpr
  rcases himg_conn (Iio 0) (Ioi 0) isOpen_Iio isOpen_Ioi hcov
    ⟨g α, ⟨α, hα, rfl⟩, hlt⟩ ⟨g 0, ⟨0, mem_ball_self zero_lt_one, rfl⟩, hg0⟩ with
    ⟨y, _, hy_lt, hy_gt⟩
  exact lt_asymm (Set.mem_Iio.mp hy_lt) (Set.mem_Ioi.mp hy_gt)

/-- Uniqueness of disk automorphisms fixing three distinct boundary points on `sphere 0 1`:
if `diskAut α c` fixes three pairwise distinct points `w₁, w₂, w₃ ∈ sphere 0 1`, then `α = 0`
and `c = 1`. -/
theorem diskAut_eq_id_of_three_fixed {α c w₁ w₂ w₃ : ℂ}
    (hα : α ∈ ball (0 : ℂ) 1) (_hc : ‖c‖ = 1)
    (hw₁ : w₁ ∈ sphere (0 : ℂ) 1) (hw₂ : w₂ ∈ sphere (0 : ℂ) 1) (hw₃ : w₃ ∈ sphere (0 : ℂ) 1)
    (h12 : w₁ ≠ w₂) (h23 : w₂ ≠ w₃) (h13 : w₁ ≠ w₃)
    (hf₁ : diskAut α c w₁ = w₁) (hf₂ : diskAut α c w₂ = w₂) (hf₃ : diskAut α c w₃ = w₃) :
    α = 0 ∧ c = 1 := by
  have hquad : ∀ w ∈ sphere (0 : ℂ) 1, diskAut α c w = w →
      star α * w ^ 2 + (c - 1) * w - c * α = 0 := by
    intro w hw hfw
    have hden : 1 - star α * w ≠ 0 := by
      intro h0
      have hα_lt : ‖α‖ < 1 := mem_ball_zero_iff.mp hα
      have hw_norm : ‖w‖ = 1 := by simpa using hw
      have h1 : (1 : ℂ) = star α * w := sub_eq_zero.mp h0
      have hn : (1 : ℝ) = ‖α‖ := by
        have := congrArg norm h1; simpa [norm_mul, hw_norm] using this
      linarith
    change c * ((w - α) / (1 - star α * w)) = w at hfw
    rw [mul_div_assoc', div_eq_iff hden] at hfw
    linear_combination hfw
  have hq₁ := hquad w₁ hw₁ hf₁
  have hq₂ := hquad w₂ hw₂ hf₂
  have hq₃ := hquad w₃ hw₃ hf₃
  have hd12 : (w₁ - w₂) * (star α * (w₁ + w₂) + (c - 1)) = 0 := by
    linear_combination hq₁ - hq₂
  have hd23 : (w₂ - w₃) * (star α * (w₂ + w₃) + (c - 1)) = 0 := by
    linear_combination hq₂ - hq₃
  have hl12 : star α * (w₁ + w₂) + (c - 1) = 0 :=
    (mul_eq_zero.mp hd12).resolve_left (sub_ne_zero.mpr h12)
  have hl23 : star α * (w₂ + w₃) + (c - 1) = 0 :=
    (mul_eq_zero.mp hd23).resolve_left (sub_ne_zero.mpr h23)
  have hα_diff : (w₁ - w₃) * star α = 0 := by
    linear_combination hl12 - hl23
  have hstar_α : star α = 0 := (mul_eq_zero.mp hα_diff).resolve_left (sub_ne_zero.mpr h13)
  have hα0 : α = 0 := star_eq_zero.mp hstar_α
  have hc1 : c = 1 := by
    rw [hstar_α, zero_mul, zero_add] at hl12
    exact sub_eq_zero.mp hl12
  exact ⟨hα0, hc1⟩

/-- Two functions continuous on `closedBall (0 : ℂ) 1` that agree on `ball (0 : ℂ) 1` agree on
`closedBall (0 : ℂ) 1`. -/
theorem eqOn_closedBall_of_eqOn_ball {f₁ f₂ : ℂ → ℂ}
    (h₁ : ContinuousOn f₁ (closedBall (0 : ℂ) 1))
    (h₂ : ContinuousOn f₂ (closedBall (0 : ℂ) 1))
    (heq : Set.EqOn f₁ f₂ (ball (0 : ℂ) 1)) :
    Set.EqOn f₁ f₂ (closedBall (0 : ℂ) 1) := by
  intro z hz
  have hz_cl : z ∈ closure (ball (0 : ℂ) 1) := by
    rwa [closure_ball (0 : ℂ) one_ne_zero]
  obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp hz_cl
  have hu_cb : ∀ n, u n ∈ closedBall (0 : ℂ) 1 := fun n => ball_subset_closedBall (hu_mem n)
  have hlim₁ : Tendsto (fun n => f₁ (u n)) atTop (𝓝 (f₁ z)) :=
    (h₁ z hz).tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hu_lim
      (Filter.Eventually.of_forall hu_cb))
  have hlim₂ : Tendsto (fun n => f₂ (u n)) atTop (𝓝 (f₂ z)) :=
    (h₂ z hz).tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hu_lim
      (Filter.Eventually.of_forall hu_cb))
  have hfun : (fun n => f₁ (u n)) = (fun n => f₂ (u n)) := funext fun n => heq (hu_mem n)
  exact tendsto_nhds_unique hlim₁ (hfun ▸ hlim₂)

/-- Inverse of `diskAut α c` (`z ↦ RudinRCA.Chapter12.phi (-α) (c⁻¹ * z)`) is continuous on `closedBall 0 1`,
differentiable on `ball 0 1`, and maps `ball 0 1` bijectively onto `ball 0 1`. -/
theorem diskAutInv_props {α c : ℂ} (hα : α ∈ ball (0 : ℂ) 1) (hc : ‖c‖ = 1) :
    let inv : ℂ → ℂ := fun ζ => RudinRCA.Chapter12.phi (-α) (c⁻¹ * ζ)
    ContinuousOn inv (closedBall (0 : ℂ) 1) ∧
    DifferentiableOn ℂ inv (ball (0 : ℂ) 1) ∧
    BijOn inv (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  intro inv
  obtain ⟨_, _, hAut_ball, _, _, hAut_inv⟩ := diskAut_props hα hc
  have hnegα : -α ∈ ball (0 : ℂ) 1 := by simpa using hα
  have hc_inv : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc, inv_one]
  obtain ⟨hphi_neg_diff, _, _, hphi_neg_ball, _, _, _⟩ := RudinRCA.Chapter12.theorem12_4 hnegα
  have hden_cb : closedBall (0 : ℂ) 1 ⊆ {ζ : ℂ | 1 - star (-α) * ζ ≠ 0} := by
    intro ζ hζ h0
    have hlt : ‖-α‖ < 1 := mem_ball_zero_iff.mp hnegα
    have hle : ‖ζ‖ ≤ 1 := mem_closedBall_zero_iff.mp hζ
    have h1 : (1 : ℂ) = star (-α) * ζ := sub_eq_zero.mp h0
    have hn : (1 : ℝ) = ‖-α‖ * ‖ζ‖ := by
      have := congrArg norm h1; simpa [norm_mul] using this
    nlinarith [norm_nonneg (-α), norm_nonneg ζ]
  refine ⟨?_, ?_, ?_⟩
  · refine hphi_neg_diff.continuousOn.comp (continuous_const.mul continuous_id).continuousOn ?_
    intro ζ hζ; apply hden_cb
    rw [mem_closedBall_zero_iff, norm_mul, hc_inv, one_mul]
    exact mem_closedBall_zero_iff.mp hζ
  · refine hphi_neg_diff.comp (differentiable_id.const_mul c⁻¹).differentiableOn ?_
    intro ζ hζ; apply hden_cb
    rw [mem_closedBall_zero_iff, norm_mul, hc_inv, one_mul]
    exact le_of_lt (mem_ball_zero_iff.mp hζ)
  · refine ⟨fun ζ hζ => ?_, fun u₁ hu₁ u₂ hu₂ heq => ?_, fun v hv => ?_⟩
    · apply hphi_neg_ball.mapsTo
      rw [mem_ball_zero_iff, norm_mul, hc_inv, one_mul]
      exact mem_ball_zero_iff.mp hζ
    · dsimp [inv] at heq
      rw [← (hAut_inv u₁ (ball_subset_closedBall hu₁)).2, heq,
        (hAut_inv u₂ (ball_subset_closedBall hu₂)).2]
    · exact ⟨diskAut α c v, hAut_ball.mapsTo hv, (hAut_inv v (ball_subset_closedBall hv)).1⟩

/-- Every positively ordered triple `(z₁, z₂, z₃)` on `sphere (0 : ℂ) 1` is mapped to the standard
positively ordered triple `(-1, -I, 1)` by a disk automorphism `diskAut α c`. -/
theorem exists_diskAut_to_std {z₁ z₂ z₃ : ℂ} (hcyc : UnitCirclePosCyclic z₁ z₂ z₃) :
    ∃ α ∈ ball (0 : ℂ) 1, ∃ c : ℂ, ‖c‖ = 1 ∧
      diskAut α c z₁ = -1 ∧ diskAut α c z₂ = -Complex.I ∧ diskAut α c z₃ = 1 := by
  obtain ⟨h12, h23, h13⟩ := unitCirclePosCyclic_pairwise_ne hcyc
  obtain ⟨hz₁, hz₂, hz₃, _⟩ := unitCirclePosCyclic_iff_det_pos.mp hcyc
  have hz₁_norm : ‖z₁‖ = 1 := by simpa using hz₁
  have hz₂_norm : ‖z₂‖ = 1 := by simpa using hz₂
  have hz₃_norm : ‖z₃‖ = 1 := by simpa using hz₃
  have hz₁_ne : z₁ ≠ 0 := by intro h0; simp [h0] at hz₁_norm
  have hz₂_ne : z₂ ≠ 0 := by intro h0; simp [h0] at hz₂_norm
  have hz₃_ne : z₃ ≠ 0 := by intro h0; simp [h0] at hz₃_norm
  have hconj₁ : starRingEnd ℂ z₁ = 1 / z₁ := by
    rw [eq_div_iff hz₁_ne, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz₁_norm]; norm_num
  have hconj₂ : starRingEnd ℂ z₂ = 1 / z₂ := by
    rw [eq_div_iff hz₂_ne, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz₂_norm]; norm_num
  have hconj₃ : starRingEnd ℂ z₃ = 1 / z₃ := by
    rw [eq_div_iff hz₃_ne, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz₃_norm]; norm_num
  let L : ℂ → ℂ := fun z => ((z₂ - z₃) * (z - z₁)) / ((z₂ - z₁) * (z - z₃))
  have h21_ne : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  have h23_ne : z₂ - z₃ ≠ 0 := sub_ne_zero.mpr h23
  have h31_ne : z₃ - z₁ ≠ 0 := sub_ne_zero.mpr h13.symm
  have hcyc_rot : UnitCirclePosCyclic z₂ z₃ z₁ := unitCirclePosCyclic_rotate_triple hcyc
  obtain ⟨_, _, _, hdet_rot_pos⟩ := unitCirclePosCyclic_iff_det_pos.mp hcyc_rot
  have hL0_det : L 0 * ((‖z₂ - z₁‖ ^ 2 : ℝ) : ℂ) =
      (z₁ / z₂ - 1) * starRingEnd ℂ (z₃ / z₂ - 1) := by
    have hnsq : ((‖z₂ - z₁‖ ^ 2 : ℝ) : ℂ) = (z₂ - z₁) * starRingEnd ℂ (z₂ - z₁) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hnsq]
    dsimp [L]
    simp only [map_sub, map_div₀, map_one, zero_sub, hconj₁, hconj₂, hconj₃]
    field_simp [hz₁_ne, hz₂_ne, hz₃_ne, h21_ne]
  have hL0_im_pos : 0 < (L 0).im := by
    have hpos_sq : 0 < ‖z₂ - z₁‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr h21_ne)
    have him := congrArg Complex.im hL0_det
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at him
    dsimp [unitCircleCyclicDet] at hdet_rot_pos
    nlinarith
  have hL_im_id : ∀ z : ℂ, z ≠ z₃ →
      (L z).im * ‖z - z₃‖ ^ 2 = (L 0).im * (1 - ‖z‖ ^ 2) := by
    intro z hzz₃
    have hsub3 : z - z₃ ≠ 0 := sub_ne_zero.mpr hzz₃
    have hcsub3 : starRingEnd ℂ z - 1 / z₃ ≠ 0 := by
      rw [← hconj₃, ← map_sub]
      exact fun h0 => hsub3 (starRingEnd_self_apply (z - z₃) ▸ by rw [h0, map_zero])
    have hcsub3' : z₃ * starRingEnd ℂ z - 1 ≠ 0 := fun h0 => hcsub3 (by
      rw [sub_eq_zero, eq_div_iff hz₃_ne, mul_comm]; exact sub_eq_zero.mp h0)
    have halg : (L z - starRingEnd ℂ (L z)) * (((‖z - z₃‖ ^ 2 : ℝ) : ℂ)) =
        (L 0 - starRingEnd ℂ (L 0)) * (((1 - ‖z‖ ^ 2 : ℝ) : ℂ)) := by
      have hn_z3 : ((‖z - z₃‖ ^ 2 : ℝ) : ℂ) = (z - z₃) * ((z₃ * starRingEnd ℂ z - 1) / z₃) := by
        have h1 : starRingEnd ℂ z - 1 / z₃ = (z₃ * starRingEnd ℂ z - 1) / z₃ := by
          field_simp [hz₃_ne]
        rw [← h1, ← hconj₃, ← map_sub, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hn_z : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) = 1 - z * starRingEnd ℂ z := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
      rw [hn_z3, hn_z]
      dsimp [L]
      simp only [map_div₀, map_mul, map_sub, zero_sub, map_neg, hconj₁, hconj₂, hconj₃, one_div]
      field_simp [hz₁_ne, hz₂_ne, hz₃_ne, h21_ne, hsub3, hcsub3']
      ring
    have him_eq := congrArg Complex.im halg
    have hsub_im : ∀ w : ℂ, (w - starRingEnd ℂ w).im = 2 * w.im := fun w => by
      simp [Complex.sub_im, Complex.conj_im]; ring
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
      hsub_im] at him_eq
    linarith
  let N : ℂ → ℂ := fun z => (z₂ - z₃) * (z - z₁) - Complex.I * (z₂ - z₁) * (z - z₃)
  let D : ℂ → ℂ := fun z => (z₂ - z₃) * (z - z₁) + Complex.I * (z₂ - z₁) * (z - z₃)
  let M : ℂ → ℂ := fun z => N z / D z
  have hD_ne_on_cb : ∀ z ∈ closedBall (0 : ℂ) 1, D z ≠ 0 := by
    intro z hz hD0
    by_cases hzz₃ : z = z₃
    · subst hzz₃
      dsimp [D] at hD0
      simp only [sub_self, mul_zero, add_zero] at hD0
      exact mul_ne_zero h23_ne h31_ne hD0
    · have hsub3 : z - z₃ ≠ 0 := sub_ne_zero.mpr hzz₃
      have hLz_eq : L z = -Complex.I := by
        dsimp [L]
        rw [div_eq_iff (mul_ne_zero h21_ne hsub3)]
        dsimp [D] at hD0
        linear_combination hD0
      have him := hL_im_id z hzz₃
      rw [hLz_eq, Complex.neg_im, Complex.I_im] at him
      have hpos3 : 0 < ‖z - z₃‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hsub3)
      have hz_le : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
      have h1z_nn : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      have hrhs_nn : 0 ≤ (L 0).im * (1 - ‖z‖ ^ 2) := mul_nonneg hL0_im_pos.le h1z_nn
      linarith
  have hM_cont_cb : ContinuousOn M (closedBall (0 : ℂ) 1) := by
    dsimp [M, N, D]
    have hcN : ContinuousOn N (closedBall (0 : ℂ) 1) :=
      ((continuousOn_const.mul (continuousOn_id.sub continuousOn_const)).sub
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)))
    have hcD : ContinuousOn D (closedBall (0 : ℂ) 1) :=
      ((continuousOn_const.mul (continuousOn_id.sub continuousOn_const)).add
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)))
    exact hcN.div hcD hD_ne_on_cb
  have hM_diff_ball : DifferentiableOn ℂ M (ball (0 : ℂ) 1) := by
    have hdiffN : Differentiable ℂ N :=
      ((differentiable_const _).mul (differentiable_id.sub (differentiable_const _))).sub
        ((differentiable_const _).mul (differentiable_id.sub (differentiable_const _)))
    have hdiffD : Differentiable ℂ D :=
      ((differentiable_const _).mul (differentiable_id.sub (differentiable_const _))).add
        ((differentiable_const _).mul (differentiable_id.sub (differentiable_const _)))
    exact (hdiffN.differentiableOn.div hdiffD.differentiableOn
      fun z hz => hD_ne_on_cb z (ball_subset_closedBall hz))
  have hM_eq_cayley : ∀ z : ℂ, z ≠ z₃ → D z ≠ 0 → M z = (L z - Complex.I) / (L z + Complex.I) := by
    intro z hzz₃ hDz
    have hdenL : (z₂ - z₁) * (z - z₃) ≠ 0 := mul_ne_zero h21_ne (sub_ne_zero.mpr hzz₃)
    have hLI : L z + Complex.I ≠ 0 := by
      dsimp [L]
      rw [div_add' _ _ _ hdenL]
      refine div_ne_zero ?_ hdenL
      simpa [D, mul_assoc] using hDz
    dsimp [M, N, D, L]
    field_simp [hdenL, hDz, hLI]
  have hM_bij_ball : BijOn M (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    refine ⟨fun z hz => ?_, fun u₁ hu₁ u₂ hu₂ heq => ?_, fun w hw => ?_⟩
    · have hzz₃ : z ≠ z₃ := by
        intro heq; rw [heq] at hz
        have hlt : ‖z₃‖ < 1 := mem_ball_zero_iff.mp hz
        linarith [hz₃_norm]
      rw [hM_eq_cayley z hzz₃ (hD_ne_on_cb z (ball_subset_closedBall hz)), mem_ball_zero_iff]
      have him_pos : 0 < (L z).im := by
        have hid := hL_im_id z hzz₃
        have hz_lt : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
        have h1z_pos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
        have hpos3 : 0 < ‖z - z₃‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzz₃))
        nlinarith
      have hLI_ne : L z + Complex.I ≠ 0 := by
        intro h0; have := congrArg Complex.im h0; simp at this; linarith
      rw [norm_div, div_lt_one (norm_pos_iff.mpr hLI_ne)]
      have hsq : ‖L z + Complex.I‖ ^ 2 - ‖L z - Complex.I‖ ^ 2 = 4 * (L z).im := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp; ring
      nlinarith [norm_nonneg (L z - Complex.I), norm_nonneg (L z + Complex.I)]
    · have hu₁_ne : u₁ ≠ z₃ := fun h => by
        rw [h] at hu₁; linarith [mem_ball_zero_iff.mp hu₁, hz₃_norm]
      have hu₂_ne : u₂ ≠ z₃ := fun h => by
        rw [h] at hu₂; linarith [mem_ball_zero_iff.mp hu₂, hz₃_norm]
      rw [hM_eq_cayley u₁ hu₁_ne (hD_ne_on_cb u₁ (ball_subset_closedBall hu₁)),
        hM_eq_cayley u₂ hu₂_ne (hD_ne_on_cb u₂ (ball_subset_closedBall hu₂))] at heq
      have him₁ : 0 < (L u₁).im := by
        have hid := hL_im_id u₁ hu₁_ne
        have hlt : ‖u₁‖ < 1 := mem_ball_zero_iff.mp hu₁
        have h1u : 0 < 1 - ‖u₁‖ ^ 2 := by nlinarith [norm_nonneg u₁]
        have hp3 : 0 < ‖u₁ - z₃‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hu₁_ne))
        nlinarith
      have him₂ : 0 < (L u₂).im := by
        have hid := hL_im_id u₂ hu₂_ne
        have hlt : ‖u₂‖ < 1 := mem_ball_zero_iff.mp hu₂
        have h1u : 0 < 1 - ‖u₂‖ ^ 2 := by nlinarith [norm_nonneg u₂]
        have hp3 : 0 < ‖u₂ - z₃‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hu₂_ne))
        nlinarith
      have hLI₁ : L u₁ + Complex.I ≠ 0 := fun h0 => by have := congrArg Complex.im h0; simp at this; linarith
      have hLI₂ : L u₂ + Complex.I ≠ 0 := fun h0 => by have := congrArg Complex.im h0; simp at this; linarith
      rw [div_eq_div_iff hLI₁ hLI₂] at heq
      have hL_eq : L u₁ = L u₂ := by
        have hI2 : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
        apply mul_left_cancel₀ hI2
        linear_combination heq
      dsimp [L] at hL_eq
      have hd1 : (z₂ - z₁) * (u₁ - z₃) ≠ 0 := mul_ne_zero h21_ne (sub_ne_zero.mpr hu₁_ne)
      have hd2 : (z₂ - z₁) * (u₂ - z₃) ≠ 0 := mul_ne_zero h21_ne (sub_ne_zero.mpr hu₂_ne)
      rw [div_eq_div_iff hd1 hd2] at hL_eq
      have hprod_ne : (z₂ - z₃) * (z₂ - z₁) * (z₃ - z₁) ≠ 0 :=
        mul_ne_zero (mul_ne_zero h23_ne h21_ne) h31_ne
      apply sub_eq_zero.mp
      apply mul_left_cancel₀ hprod_ne
      linear_combination -hL_eq
    · have hw_lt : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
      have h1w : 1 - w ≠ 0 := fun h0 => by
        have hw1 : w = 1 := (sub_eq_zero.mp h0).symm
        rw [hw1, norm_one] at hw_lt; exact lt_irrefl 1 hw_lt
      let ζ : ℂ := Complex.I * (1 + w) / (1 - w)
      have hζ_im : 0 < ζ.im := by
        have hmul : ζ * ((‖1 - w‖ ^ 2 : ℝ) : ℂ) = Complex.I * (1 + w) * starRingEnd ℂ (1 - w) := by
          have hnsq : ((‖1 - w‖ ^ 2 : ℝ) : ℂ) = (1 - w) * starRingEnd ℂ (1 - w) := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          rw [hnsq]; dsimp [ζ]; field_simp [h1w]
        have him := congrArg Complex.im hmul
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at him
        have hrhs : (Complex.I * (1 + w) * starRingEnd ℂ (1 - w)).im = 1 - ‖w‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp [Complex.mul_im, Complex.mul_re]; ring
        rw [hrhs] at him
        have hpos_den : 0 < ‖1 - w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr h1w)
        have h1w_pos : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
        nlinarith
      have hden_z : (z₂ - z₃) - (z₂ - z₁) * ζ ≠ 0 := by
        intro h0
        have hζ_eq : ζ = (z₂ - z₃) / (z₂ - z₁) := by
          rw [eq_div_iff h21_ne, mul_comm]; exact (sub_eq_zero.mp h0).symm
        have hsum_zero : ((z₂ - z₃) / (z₂ - z₁) - starRingEnd ℂ ((z₂ - z₃) / (z₂ - z₁))) +
            (L 0 - starRingEnd ℂ (L 0)) = 0 := by
          dsimp [L]
          simp only [map_div₀, map_mul, map_sub, zero_sub, map_neg, hconj₁, hconj₂, hconj₃]
          field_simp [hz₁_ne, hz₂_ne, hz₃_ne, h21_ne]
          ring
        have him_sum := congrArg Complex.im hsum_zero
        simp only [Complex.add_im, Complex.sub_im, Complex.conj_im, Complex.zero_im] at him_sum
        rw [← hζ_eq] at him_sum
        linarith
      let z : ℂ := (z₁ * (z₂ - z₃) - z₃ * (z₂ - z₁) * ζ) / ((z₂ - z₃) - (z₂ - z₁) * ζ)
      have hzz₃ : z ≠ z₃ := by
        intro heq
        dsimp [z] at heq
        rw [div_eq_iff hden_z] at heq
        have : (z₁ - z₃) * (z₂ - z₃) = 0 := by linear_combination heq
        exact mul_ne_zero (sub_ne_zero.mpr h13) h23_ne this
      have hLz : L z = ζ := by
        have hsub3 : z - z₃ = (z₁ - z₃) * (z₂ - z₃) / ((z₂ - z₃) - (z₂ - z₁) * ζ) := by
          dsimp [z]; field_simp [hden_z]; ring
        have hsub1 : z - z₁ = (z₁ - z₃) * (z₂ - z₁) * ζ / ((z₂ - z₃) - (z₂ - z₁) * ζ) := by
          dsimp [z]; field_simp [hden_z]; ring
        dsimp [L]
        rw [hsub1, hsub3]
        have h13_ne : z₁ - z₃ ≠ 0 := sub_ne_zero.mpr h13
        field_simp [hden_z, h21_ne, h23_ne, h13_ne]
      have hz_ball : z ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff]
        have hid := hL_im_id z hzz₃
        rw [hLz] at hid
        have hpos_lhs : 0 < ζ.im * ‖z - z₃‖ ^ 2 :=
          mul_pos hζ_im (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzz₃)))
        have h1z_pos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith
        by_contra hge
        have hge' : 1 ≤ ‖z‖ := not_lt.mp hge
        nlinarith [norm_nonneg z]
      refine ⟨z, hz_ball, ?_⟩
      rw [hM_eq_cayley z hzz₃ (hD_ne_on_cb z (ball_subset_closedBall hz_ball)), hLz]
      dsimp [ζ]
      have hden_cay : Complex.I * (1 + w) / (1 - w) + Complex.I ≠ 0 := by
        rw [div_add' _ _ _ h1w]
        refine div_ne_zero ?_ h1w
        have : Complex.I * (1 + w) + Complex.I * (1 - w) = 2 * Complex.I := by ring
        rw [this]
        exact mul_ne_zero two_ne_zero Complex.I_ne_zero
      field_simp [h1w, hden_cay, Complex.I_ne_zero]
      ring
  obtain ⟨α, hα, c, hc, hM_eq⟩ :=
    RudinRCA.Chapter12.theorem12_6.1.mp ⟨hM_diff_ball, hM_bij_ball⟩
  obtain ⟨hAut_cont, _, _, _, _, _⟩ := diskAut_props hα hc
  have hM_eq_cb : Set.EqOn M (diskAut α c) (closedBall (0 : ℂ) 1) :=
    eqOn_closedBall_of_eqOn_ball hM_cont_cb hAut_cont hM_eq
  refine ⟨α, hα, c, hc, ?_, ?_, ?_⟩
  · rw [← hM_eq_cb (sphere_subset_closedBall hz₁)]
    dsimp [M, N, D]
    have hne : z₁ - z₃ ≠ 0 := sub_ne_zero.mpr h13
    have hI : Complex.I * (z₂ - z₁) * (z₁ - z₃) ≠ 0 :=
      mul_ne_zero (mul_ne_zero Complex.I_ne_zero h21_ne) hne
    simp only [sub_self, mul_zero, zero_sub, zero_add]
    exact neg_div_self hI
  · rw [← hM_eq_cb (sphere_subset_closedBall hz₂)]
    dsimp [M, N, D]
    have hprod : (z₂ - z₃) * (z₂ - z₁) ≠ 0 := mul_ne_zero h23_ne h21_ne
    have h1I : (1 + Complex.I : ℂ) ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this
    have hnum : (z₂ - z₃) * (z₂ - z₁) - Complex.I * (z₂ - z₁) * (z₂ - z₃) =
        (-Complex.I) * ((1 + Complex.I) * ((z₂ - z₃) * (z₂ - z₁))) := by
      linear_combination Complex.I_sq * ((z₂ - z₃) * (z₂ - z₁))
    have hden : (z₂ - z₃) * (z₂ - z₁) + Complex.I * (z₂ - z₁) * (z₂ - z₃) =
        (1 + Complex.I) * ((z₂ - z₃) * (z₂ - z₁)) := by ring
    rw [hnum, hden, mul_div_cancel_right₀ _ (mul_ne_zero h1I hprod)]
  · rw [← hM_eq_cb (sphere_subset_closedBall hz₃)]
    dsimp [M, N, D]
    simp only [sub_self, mul_zero, sub_zero, add_zero]
    exact div_self (mul_ne_zero h23_ne h31_ne)

/-- Full 3-point transitivity and uniqueness of disk automorphisms on positively ordered boundary
triples on `sphere (0 : ℂ) 1`. -/
theorem exists_unique_diskAut_three_points {z₁ z₂ z₃ w₁ w₂ w₃ : ℂ}
    (hz : UnitCirclePosCyclic z₁ z₂ z₃) (hw : UnitCirclePosCyclic w₁ w₂ w₃) :
    ∃ α ∈ ball (0 : ℂ) 1, ∃ c : ℂ, ‖c‖ = 1 ∧
      diskAut α c z₁ = w₁ ∧ diskAut α c z₂ = w₂ ∧ diskAut α c z₃ = w₃ ∧
      ∀ α' ∈ ball (0 : ℂ) 1, ∀ c' : ℂ, ‖c'‖ = 1 →
        diskAut α' c' z₁ = w₁ → diskAut α' c' z₂ = w₂ → diskAut α' c' z₃ = w₃ →
        α' = α ∧ c' = c := by
  obtain ⟨α₁, hα₁, c₁, hc₁, hz₁_eq, hz₂_eq, hz₃_eq⟩ := exists_diskAut_to_std hz
  obtain ⟨α₂, hα₂, c₂, hc₂, hw₁_eq, hw₂_eq, hw₃_eq⟩ := exists_diskAut_to_std hw
  obtain ⟨hAut₁_cont, hAut₁_diff, hAut₁_ball, _, hAut₁_cb, _⟩ := diskAut_props hα₁ hc₁
  obtain ⟨_, _, _, _, _, hAut₂_inv⟩ := diskAut_props hα₂ hc₂
  obtain ⟨hinv₂_cont, hinv₂_diff, hinv₂_bij⟩ := diskAutInv_props hα₂ hc₂
  let inv₂ : ℂ → ℂ := fun ζ => RudinRCA.Chapter12.phi (-α₂) (c₂⁻¹ * ζ)
  let g : ℂ → ℂ := inv₂ ∘ diskAut α₁ c₁
  obtain ⟨α, hα, c, hc, hg_eq⟩ := RudinRCA.Chapter12.theorem12_6.1.mp
    ⟨hinv₂_diff.comp hAut₁_diff hAut₁_ball.mapsTo, hinv₂_bij.comp hAut₁_ball⟩
  obtain ⟨hAut_cont, _, _, _, _, hAut_inv⟩ := diskAut_props hα hc
  have hg_eq_cb : Set.EqOn g (diskAut α c) (closedBall (0 : ℂ) 1) :=
    eqOn_closedBall_of_eqOn_ball (hinv₂_cont.comp hAut₁_cont hAut₁_cb.mapsTo) hAut_cont hg_eq
  obtain ⟨hz₁_s, hz₂_s, hz₃_s, _⟩ := unitCirclePosCyclic_iff_det_pos.mp hz
  obtain ⟨hw₁_s, hw₂_s, hw₃_s, _⟩ := unitCirclePosCyclic_iff_det_pos.mp hw
  have h_val₁ : diskAut α c z₁ = w₁ := by
    rw [← hg_eq_cb (sphere_subset_closedBall hz₁_s)]
    dsimp [g, inv₂]; rw [hz₁_eq, ← hw₁_eq, (hAut₂_inv w₁ (sphere_subset_closedBall hw₁_s)).1]
  have h_val₂ : diskAut α c z₂ = w₂ := by
    rw [← hg_eq_cb (sphere_subset_closedBall hz₂_s)]
    dsimp [g, inv₂]; rw [hz₂_eq, ← hw₂_eq, (hAut₂_inv w₂ (sphere_subset_closedBall hw₂_s)).1]
  have h_val₃ : diskAut α c z₃ = w₃ := by
    rw [← hg_eq_cb (sphere_subset_closedBall hz₃_s)]
    dsimp [g, inv₂]; rw [hz₃_eq, ← hw₃_eq, (hAut₂_inv w₃ (sphere_subset_closedBall hw₃_s)).1]
  refine ⟨α, hα, c, hc, h_val₁, h_val₂, h_val₃, ?_⟩
  intro α' hα' c' hc' h₁' h₂' h₃'
  obtain ⟨hAut'_cont, hAut'_diff, hAut'_ball, _, hAut'_cb, _⟩ := diskAut_props hα' hc'
  obtain ⟨hinv₀_cont, hinv₀_diff, hinv₀_bij⟩ := diskAutInv_props hα hc
  let inv₀ : ℂ → ℂ := fun ζ => RudinRCA.Chapter12.phi (-α) (c⁻¹ * ζ)
  let q : ℂ → ℂ := inv₀ ∘ diskAut α' c'
  obtain ⟨β₀, hβ₀, d₀, hd₀, hq_eq⟩ := RudinRCA.Chapter12.theorem12_6.1.mp
    ⟨hinv₀_diff.comp hAut'_diff hAut'_ball.mapsTo, hinv₀_bij.comp hAut'_ball⟩
  obtain ⟨hAutβ_cont, _, _, _, _, _⟩ := diskAut_props hβ₀ hd₀
  have hq_eq_cb : Set.EqOn q (diskAut β₀ d₀) (closedBall (0 : ℂ) 1) :=
    eqOn_closedBall_of_eqOn_ball (hinv₀_cont.comp hAut'_cont hAut'_cb.mapsTo) hAutβ_cont hq_eq
  obtain ⟨hz12, hz23, hz13⟩ := unitCirclePosCyclic_pairwise_ne hz
  have hf_z₁ : diskAut β₀ d₀ z₁ = z₁ := by
    rw [← hq_eq_cb (sphere_subset_closedBall hz₁_s)]
    dsimp [q, inv₀]; rw [h₁', ← h_val₁, (hAut_inv z₁ (sphere_subset_closedBall hz₁_s)).1]
  have hf_z₂ : diskAut β₀ d₀ z₂ = z₂ := by
    rw [← hq_eq_cb (sphere_subset_closedBall hz₂_s)]
    dsimp [q, inv₀]; rw [h₂', ← h_val₂, (hAut_inv z₂ (sphere_subset_closedBall hz₂_s)).1]
  have hf_z₃ : diskAut β₀ d₀ z₃ = z₃ := by
    rw [← hq_eq_cb (sphere_subset_closedBall hz₃_s)]
    dsimp [q, inv₀]; rw [h₃', ← h_val₃, (hAut_inv z₃ (sphere_subset_closedBall hz₃_s)).1]
  obtain ⟨hβ0, hd1⟩ := diskAut_eq_id_of_three_fixed hβ₀ hd₀ hz₁_s hz₂_s hz₃_s hz12 hz23 hz13
    hf_z₁ hf_z₂ hf_z₃
  refine (RudinRCA.Chapter12.theorem12_6 (f := id)).2 hα' hα hc' hc fun z hz_b => ?_
  have hqz : q z = z := by
    rw [hq_eq_cb (ball_subset_closedBall hz_b), hβ0, hd1]
    simp [diskAut, RudinRCA.Chapter12.phi]
  calc
    c' * RudinRCA.Chapter12.phi α' z = diskAut α' c' z := rfl
    _ = diskAut α c (inv₀ (diskAut α' c' z)) :=
      (hAut_inv (diskAut α' c' z) (ball_subset_closedBall (hAut'_ball.mapsTo hz_b))).2.symm
    _ = diskAut α c (q z) := rfl
    _ = c * RudinRCA.Chapter12.phi α z := by rw [hqz]; rfl

/-- For `w ∈ ball (0 : ℂ) 1`, `z ↦ z - w` possesses no continuous logarithm on `sphere (0 : ℂ) 1`. -/
theorem not_exists_continuousOn_exp_eq_sub_on_sphere {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ¬ ∃ M : ℂ → ℂ, ContinuousOn M (sphere (0 : ℂ) 1) ∧
        ∀ y ∈ sphere (0 : ℂ) 1, Complex.exp (M y) = y - w := by
  rintro ⟨M, hM_cont, hM_exp⟩
  have hw_lt : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  let γ : ℝ → ℂ := fun θ => Complex.exp ((θ : ℂ) * Complex.I)
  have hγ_sph : ∀ θ : ℝ, γ θ ∈ sphere (0 : ℂ) 1 := fun θ => by
    simp [γ, Complex.norm_exp_ofReal_mul_I]
  have hγ_cont : Continuous γ :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  let u : ℝ → ℂ := fun θ => 1 - w * Complex.exp (-(θ : ℂ) * Complex.I)
  have hu_cont : Continuous u :=
    continuous_const.sub (continuous_const.mul
      (Complex.continuous_exp.comp ((Complex.continuous_ofReal.neg).mul continuous_const)))
  have hu_slit : ∀ θ : ℝ, u θ ∈ Complex.slitPlane := by
    intro θ
    refine Or.inl ?_
    have hnorm : ‖w * Complex.exp (-(θ : ℂ) * Complex.I)‖ = ‖w‖ := by
      have hexp : -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [norm_mul, hexp, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hle : (w * Complex.exp (-(θ : ℂ) * Complex.I)).re ≤
        ‖w * Complex.exp (-(θ : ℂ) * Complex.I)‖ := Complex.re_le_norm _
    simp only [u, Complex.sub_re, Complex.one_re]
    linarith
  let h : ℝ → ℂ := fun θ => Complex.log (u θ)
  have hh_cont : Continuous h := hu_cont.clog hu_slit
  let c₀ : ℂ := (2 * Real.pi : ℂ) * Complex.I
  have hc₀_ne : c₀ ≠ 0 := mul_ne_zero
    (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) Complex.I_ne_zero
  let q : ℝ → ℂ := fun θ => (M (γ θ) - ((θ : ℂ) * Complex.I + h θ)) / c₀
  have hq_cont : ContinuousOn q (Icc (0 : ℝ) (2 * Real.pi)) := by
    have hMc : Continuous (fun θ => M (γ θ)) :=
      hM_cont.comp_continuous hγ_cont hγ_sph
    exact ((hMc.sub ((Complex.continuous_ofReal.mul continuous_const).add hh_cont)).div_const
      c₀).continuousOn
  have hq_int : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), ∃ k : ℤ, q θ = k := by
    intro θ _
    have hexp1 : Complex.exp (M (γ θ)) = γ θ - w := hM_exp (γ θ) (hγ_sph θ)
    have hu_ne : u θ ≠ 0 := Complex.slitPlane_ne_zero (hu_slit θ)
    have hexp2 : Complex.exp ((θ : ℂ) * Complex.I + h θ) = γ θ - w := by
      rw [Complex.exp_add, Complex.exp_log hu_ne]
      dsimp [γ, u]
      rw [mul_sub, mul_one, mul_left_comm, ← Complex.exp_add]
      simp
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hexp1.trans hexp2.symm)
    refine ⟨k, ?_⟩
    dsimp [q, c₀]
    have hsub : M (γ θ) - ((θ : ℂ) * Complex.I + h θ) =
        (k : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) := by rw [hk]; ring
    rw [hsub, mul_div_cancel_right₀ _ hc₀_ne]
  have hq_eq := eq_of_isPreconnected_int_cast isPreconnected_Icc hq_cont hq_int
    (left_mem_Icc.mpr (by positivity)) (right_mem_Icc.mpr (by positivity))
  have hγ_per : γ (2 * Real.pi) = γ 0 := by
    dsimp [γ]
    have h2pi : ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I := by
      push_cast; ring
    rw [h2pi, Complex.exp_two_pi_mul_I]; simp
  have hh_per : h (2 * Real.pi) = h 0 := by
    dsimp [h, u]
    have h2pi : -((2 * Real.pi : ℝ) : ℂ) * Complex.I = -(2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [h2pi, Complex.exp_neg, Complex.exp_two_pi_mul_I]; simp
  dsimp [q] at hq_eq
  rw [hγ_per, hh_per] at hq_eq
  have hnum := (div_left_inj' hc₀_ne).mp hq_eq
  apply hc₀_ne
  dsimp [c₀]
  push_cast at hnum ⊢
  linear_combination hnum

/-- Every homeomorphism `H : closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1` maps `sphere (0 : ℂ) 1`
into `sphere (0 : ℂ) 1` and `ball (0 : ℂ) 1` into `ball (0 : ℂ) 1` (hence bijects both). -/
theorem homeomorph_closedBall_preserves_sphere_and_ball
    (H : closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1) :
    (∀ ζ (hζ : ζ ∈ sphere (0 : ℂ) 1),
      (H ⟨ζ, sphere_subset_closedBall hζ⟩ : ℂ) ∈ sphere (0 : ℂ) 1) ∧
    (∀ z (hz : z ∈ ball (0 : ℂ) 1),
      (H ⟨z, ball_subset_closedBall hz⟩ : ℂ) ∈ ball (0 : ℂ) 1) := by
  have h_sph : ∀ (E : closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1) ζ
      (hζ : ζ ∈ sphere (0 : ℂ) 1),
      (E ⟨ζ, sphere_subset_closedBall hζ⟩ : ℂ) ∈ sphere (0 : ℂ) 1 := by
    intro E ζ hζ
    by_contra hnot_sph
    let pζ : closedBall (0 : ℂ) 1 := ⟨ζ, sphere_subset_closedBall hζ⟩
    let w : ℂ := (E pζ : ℂ)
    have hw_cb : w ∈ closedBall (0 : ℂ) 1 := (E pζ).2
    have hw_ball : w ∈ ball (0 : ℂ) 1 := by
      rw [← ball_union_sphere] at hw_cb
      exact hw_cb.resolve_right hnot_sph
    have hζ_norm : ‖ζ‖ = 1 := by simpa using hζ
    let rad : ℂ → closedBall (0 : ℂ) 1 := fun z =>
      ⟨z / ((max (1 : ℝ) ‖z‖ : ℝ) : ℂ), by
        rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖z‖))]
        exact div_le_one_of_le₀ (le_max_right 1 ‖z‖) (le_trans zero_le_one (le_max_left 1 ‖z‖))⟩
    have hrad_cont : Continuous rad := by
      refine Continuous.subtype_mk ?_ _
      exact continuous_id.div
        (Complex.continuous_ofReal.comp (continuous_const.max continuous_norm))
        fun z => Complex.ofReal_ne_zero.mpr
          (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖z‖)).ne'
    have hrad_id : ∀ x : closedBall (0 : ℂ) 1, rad x.1 = x := by
      intro x
      ext
      dsimp [rad]
      have hx_le : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
      rw [max_eq_left hx_le, Complex.ofReal_one, div_one]
    let W : Set ℂ := {z : ℂ | (z * starRingEnd ℂ ζ).re < 1}
    have hW_open : IsOpen W :=
      isOpen_lt (Complex.continuous_re.comp (continuous_id.mul continuous_const)) continuous_const
    have hW_conv : Convex ℝ W := by
      intro x hx y hy a b ha hb hab
      change ((a • x + b • y) * starRingEnd ℂ ζ).re < 1
      have hx' : (x * starRingEnd ℂ ζ).re < 1 := hx
      have hy' : (y * starRingEnd ℂ ζ).re < 1 := hy
      have hlin : ((a • x + b • y) * starRingEnd ℂ ζ).re =
          a * (x * starRingEnd ℂ ζ).re + b * (y * starRingEnd ℂ ζ).re := by
        simp [Complex.real_smul, add_mul, mul_assoc, Complex.add_re, Complex.mul_re]
      rw [hlin]
      rcases eq_or_lt_of_le ha with rfl | ha_pos
      · simp at hab; subst hab; simpa using hy'
      · nlinarith
    have h0_W : (0 : ℂ) ∈ W := by simp [W]
    have hW_sc : IsSimplyConnected W := by
      have : ContractibleSpace W := hW_conv.contractibleSpace ⟨0, h0_W⟩
      change SimplyConnectedSpace W
      exact inferInstance
    have hrad_ne_pζ : ∀ z ∈ W, rad z ≠ pζ := by
      intro z hz heq
      have hval : z / ((max (1 : ℝ) ‖z‖ : ℝ) : ℂ) = ζ := congrArg Subtype.val heq
      let m : ℝ := max 1 ‖z‖
      have hm_pos : 0 < m := lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖z‖)
      have hz_eq : z = (m : ℂ) * ζ := by
        rw [mul_comm]; exact (div_eq_iff (Complex.ofReal_ne_zero.mpr hm_pos.ne')).mp hval
      have hre : (z * starRingEnd ℂ ζ).re = m := by
        rw [hz_eq, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ_norm]
        simp only [one_pow, Complex.ofReal_one, mul_one, Complex.ofReal_re]
      have hz' : (z * starRingEnd ℂ ζ).re < 1 := hz
      linarith [le_max_left (1 : ℝ) ‖z‖]
    let F : ℂ → ℂ := fun z => (E (rad z) : ℂ) - w
    have hF_cont : Continuous F :=
      (continuous_subtype_val.comp (E.continuous.comp hrad_cont)).sub continuous_const
    have h0_not_img : (0 : ℂ) ∉ F '' W := by
      rintro ⟨z, hz, hFz⟩
      have heqE : E (rad z) = E pζ := Subtype.ext (sub_eq_zero.mp hFz)
      exact hrad_ne_pζ z hz (E.injective heqE)
    obtain ⟨L, hL_cont, hL_exp⟩ :=
      Complex.exists_continuousOn_eqOn_exp_comp hW_sc hW_open hF_cont.continuousOn h0_not_img
    have hcb_diff_sub_W : ∀ x : closedBall (0 : ℂ) 1, x ≠ pζ → x.1 ∈ W := by
      intro x hx_ne
      have hx_le : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
      have hne_val : x.1 ≠ ζ := fun h => hx_ne (Subtype.ext h)
      have hpos : 0 < ‖x.1 - ζ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne_val))
      have hexpand : ‖x.1 - ζ‖ ^ 2 = ‖x.1‖ ^ 2 + ‖ζ‖ ^ 2 - 2 * (x.1 * starRingEnd ℂ ζ).re := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
          Complex.normSq_apply, Complex.normSq_apply]
        simp [Complex.mul_re]; ring
      rw [hζ_norm] at hexpand
      have hx_sq : ‖x.1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x.1]
      change (x.1 * starRingEnd ℂ ζ).re < 1
      linarith
    have hinv_in_W : ∀ y ∈ sphere (0 : ℂ) 1, (E.symm (rad y) : ℂ) ∈ W := by
      intro y hy
      refine hcb_diff_sub_W _ fun heq => ?_
      have hy_eq_w : y = w := by
        have h1 := congrArg (fun p => (E p : ℂ)) heq
        have h2 : rad y = ⟨y, sphere_subset_closedBall hy⟩ := hrad_id ⟨y, sphere_subset_closedBall hy⟩
        rw [h2, E.apply_symm_apply] at h1
        exact h1
      rw [← hy_eq_w] at hw_ball
      have h1 : ‖y‖ = 1 := by simpa using hy
      have h2 : ‖y‖ < 1 := mem_ball_zero_iff.mp hw_ball
      linarith
    let M : ℂ → ℂ := fun y => L (E.symm (rad y) : ℂ)
    have hM_cont : ContinuousOn M (sphere (0 : ℂ) 1) :=
      hL_cont.comp (continuous_subtype_val.comp (E.symm.continuous.comp hrad_cont)).continuousOn
        hinv_in_W
    refine not_exists_continuousOn_exp_eq_sub_on_sphere hw_ball ⟨M, hM_cont, fun y hy => ?_⟩
    have hexp : Complex.exp (M y) = F (E.symm (rad y) : ℂ) := hL_exp (hinv_in_W y hy)
    rw [hexp]
    dsimp [F]
    have hrad_y : rad y = ⟨y, sphere_subset_closedBall hy⟩ := hrad_id ⟨y, sphere_subset_closedBall hy⟩
    rw [hrad_id (E.symm (rad y)), E.apply_symm_apply, hrad_y]
  refine ⟨h_sph H, fun z hz => ?_⟩
  by_contra hnot_ball
  let pz : closedBall (0 : ℂ) 1 := ⟨z, ball_subset_closedBall hz⟩
  have h_cb : ((H pz : ℂ)) ∈ ball (0 : ℂ) 1 ∪ sphere (0 : ℂ) 1 := by
    rw [ball_union_sphere]; exact (H pz).2
  have h_in_sph : (H pz : ℂ) ∈ sphere (0 : ℂ) 1 := h_cb.resolve_left hnot_ball
  have hz_sph := h_sph H.symm (H pz : ℂ) h_in_sph
  have heq : (⟨(H pz : ℂ), sphere_subset_closedBall h_in_sph⟩ : closedBall (0 : ℂ) 1) = H pz :=
    Subtype.ext rfl
  rw [heq, H.symm_apply_apply] at hz_sph
  have h1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have h2 : ‖z‖ = 1 := by simpa using hz_sph
  linarith

/-! ### Part 2: Continuity, Homeomorphism, and Spherical Holomorphicity of Möbius Maps -/

theorem continuous_moebiusAffine {a b : ℂ} (ha : a ≠ 0) :
    Continuous (moebiusMap a b 0 1) := by
  rw [continuous_iff_continuousAt]
  intro p
  induction p using OnePoint.rec with
  | infty =>
    have hinf : moebiusMap a b 0 1 ∞ = ∞ := by simp
    rw [ContinuousAt, hinf, (OnePoint.hasBasis_nhds_infty).tendsto_right_iff]
    rintro K ⟨_, hK_compact⟩
    let K' : Set ℂ := (fun w : ℂ => a⁻¹ * (w - b)) '' K
    have hK'_compact : IsCompact K' :=
      hK_compact.image (continuous_const.mul (continuous_id.sub continuous_const))
    have hK'_closed : IsClosed K' := hK'_compact.isClosed
    have hmem : (((↑) : ℂ → RiemannSphere) '' K'ᶜ ∪ {∞}) ∈ 𝓝 (∞ : RiemannSphere) :=
      OnePoint.hasBasis_nhds_infty.mem_of_mem ⟨hK'_closed, hK'_compact⟩
    filter_upwards [hmem] with q hq
    induction q using OnePoint.rec with
    | infty =>
      simp only [moebiusMap_infty, ↓reduceIte]
      exact Or.inr rfl
    | coe z =>
      simp only [moebiusMap_coe, zero_mul, zero_add, one_ne_zero, ↓reduceIte, div_one]
      refine Or.inl ⟨a * z + b, fun hmemK => ?_, rfl⟩
      rcases hq with ⟨w, hw_not_K', hwz⟩ | hinf_eq
      · apply hw_not_K'
        rw [OnePoint.coe_injective hwz]
        refine ⟨a * z + b, hmemK, ?_⟩
        field_simp [ha]; ring
      · exact OnePoint.coe_ne_infty z hinf_eq
  | coe z =>
    let g : RiemannSphere → RiemannSphere :=
      OnePoint.rec ∞ (fun w : ℂ => ((a * w + b : ℂ) : RiemannSphere))
    have hev : moebiusMap a b 0 1 =ᶠ[𝓝 (z : RiemannSphere)] g := by
      filter_upwards [OnePoint.isOpenEmbedding_coe.isOpen_range.mem_nhds ⟨z, rfl⟩] with q hq
      rcases hq with ⟨w, rfl⟩
      simp only [moebiusMap_coe, zero_mul, zero_add, one_ne_zero, ↓reduceIte, div_one]
      rfl
    refine ContinuousAt.congr ?_ hev.symm
    have hc : Continuous (fun w : ℂ => ((a * w + b : ℂ) : RiemannSphere)) :=
      OnePoint.continuous_coe.comp ((continuous_const.mul continuous_id).add continuous_const)
    rw [ContinuousAt, Tendsto]
    have hmap : map g (𝓝 (z : RiemannSphere)) =
        map (fun w : ℂ => ((a * w + b : ℂ) : RiemannSphere)) (𝓝 z) := by
      rw [← OnePoint.isOpenEmbedding_coe.map_nhds_eq z, Filter.map_map]
      rfl
    rw [hmap]
    exact hc.continuousAt

theorem continuous_moebiusInv : Continuous moebiusInv := by
  rw [continuous_iff_continuousAt]
  intro p
  induction p using OnePoint.rec with
  | infty =>
    have hinf : moebiusInv ∞ = ((0 : ℂ) : RiemannSphere) := by simp [moebiusInv]
    rw [ContinuousAt, hinf, tendsto_iff_forall_eventually_mem]
    intro V hV
    have hpre : ((↑) : ℂ → RiemannSphere) ⁻¹' V ∈ 𝓝 (0 : ℂ) :=
      OnePoint.continuous_coe.continuousAt.preimage_mem_nhds hV
    obtain ⟨ε, hε_pos, hball⟩ := Metric.mem_nhds_iff.mp hpre
    let K : Set ℂ := closedBall (0 : ℂ) (1 / ε)
    have hmem : (((↑) : ℂ → RiemannSphere) '' Kᶜ ∪ {∞}) ∈ 𝓝 (∞ : RiemannSphere) :=
      OnePoint.hasBasis_nhds_infty.mem_of_mem ⟨isClosed_closedBall, isCompact_closedBall 0 (1 / ε)⟩
    filter_upwards [hmem] with q hq
    induction q using OnePoint.rec with
    | infty =>
      simpa [moebiusInv] using hball (mem_ball_self hε_pos)
    | coe z =>
      have hz_not_K : z ∉ K := by
        rcases hq with ⟨w, hw, hwz⟩ | hinf_eq
        · exact OnePoint.coe_injective hwz ▸ hw
        · exact False.elim (OnePoint.coe_ne_infty z hinf_eq)
      have hz_gt : 1 / ε < ‖z‖ := not_le.mp (by simpa [K] using hz_not_K)
      have hz_ne : z ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hz_gt; linarith [one_div_pos.mpr hε_pos]
      have hinv : moebiusInv (z : RiemannSphere) = ((z⁻¹ : ℂ) : RiemannSphere) := by
        simp [moebiusInv, hz_ne]
      rw [hinv]
      apply hball
      rw [mem_ball_zero_iff, norm_inv]
      exact inv_lt_of_inv_lt₀ hε_pos (by simpa [one_div] using hz_gt)
  | coe z =>
    by_cases hz : z = 0
    · subst hz
      have h0 : moebiusInv ((0 : ℂ) : RiemannSphere) = ∞ := by simp [moebiusInv]
      rw [ContinuousAt, h0, (OnePoint.hasBasis_nhds_infty).tendsto_right_iff]
      rintro K ⟨_, hK_compact⟩
      obtain ⟨R, hR_pos, hK_sub⟩ : ∃ R > 0, K ⊆ closedBall (0 : ℂ) R := by
        obtain ⟨R₀, hR₀⟩ := hK_compact.isBounded.subset_closedBall 0
        exact ⟨max R₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
          hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))⟩
      have hU_open : IsOpen (((↑) : ℂ → RiemannSphere) '' ball (0 : ℂ) (1 / R)) :=
        OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_ball
      have hU_nhds : ((↑) : ℂ → RiemannSphere) '' ball (0 : ℂ) (1 / R) ∈
          𝓝 ((0 : ℂ) : RiemannSphere) :=
        hU_open.mem_nhds ⟨0, mem_ball_self (one_div_pos.mpr hR_pos), rfl⟩
      filter_upwards [hU_nhds] with q hq
      rcases hq with ⟨w, hw_ball, rfl⟩
      by_cases hw0 : w = 0
      · subst hw0
        simp only [moebiusInv, moebiusMap_coe, mul_zero, add_zero, ↓reduceIte]
        exact Or.inr rfl
      · have hinv : moebiusInv (w : RiemannSphere) = ((w⁻¹ : ℂ) : RiemannSphere) := by
          simp [moebiusInv, hw0]
        rw [hinv]
        refine Or.inl ⟨w⁻¹, fun hwK => ?_, rfl⟩
        have hw_le : ‖w⁻¹‖ ≤ R := mem_closedBall_zero_iff.mp (hK_sub hwK)
        have hw_lt : ‖w‖ < 1 / R := mem_ball_zero_iff.mp hw_ball
        have hgt : R < ‖w⁻¹‖ := by
          rw [norm_inv]
          exact lt_inv_of_lt_inv₀ (norm_pos_iff.mpr hw0) (by simpa [one_div] using hw_lt)
        linarith
    · have hU_open : IsOpen (((↑) : ℂ → RiemannSphere) '' {w : ℂ | w ≠ 0}) :=
        OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_ne
      have hU_nhds : ((↑) : ℂ → RiemannSphere) '' {w : ℂ | w ≠ 0} ∈
          𝓝 (z : RiemannSphere) := hU_open.mem_nhds ⟨z, hz, rfl⟩
      let g : RiemannSphere → RiemannSphere :=
        OnePoint.rec ∞ (fun w : ℂ => ((w⁻¹ : ℂ) : RiemannSphere))
      have hev : moebiusInv =ᶠ[𝓝 (z : RiemannSphere)] g := by
        filter_upwards [hU_nhds] with q hq
        rcases hq with ⟨w, hw, rfl⟩
        have hw' : w ≠ 0 := hw
        simp only [moebiusInv, moebiusMap_coe, zero_mul, zero_add, one_mul, add_zero, hw',
          ↓reduceIte, one_div]
        rfl
      refine ContinuousAt.congr ?_ hev.symm
      rw [ContinuousAt, Tendsto]
      have hmap : map g (𝓝 (z : RiemannSphere)) =
          map (fun w : ℂ => ((w⁻¹ : ℂ) : RiemannSphere)) (𝓝 z) := by
        rw [← OnePoint.isOpenEmbedding_coe.map_nhds_eq z, Filter.map_map]; rfl
      rw [hmap]
      exact OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)

/-- Every Möbius transformation `moebiusMap a b c d` (`a * d - b * c ≠ 0`) is continuous on
`RiemannSphere`. -/
theorem moebiusMap_continuous {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) :
    Continuous (moebiusMap a b c d) := by
  have hgen : ∀ {f : RiemannSphere → RiemannSphere},
      GeneratedByElementaryMoebius f → Continuous f := by
    intro f hf
    induction hf with
    | id => exact continuous_id
    | trans β _ ih =>
      exact (continuous_moebiusAffine one_ne_zero).comp ih
    | rot u hu _ ih =>
      have hu_ne : u ≠ 0 := by intro h0; simp [h0] at hu
      exact (continuous_moebiusAffine hu_ne).comp ih
    | dil r hr _ ih =>
      exact (continuous_moebiusAffine (Complex.ofReal_ne_zero.mpr hr.ne')).comp ih
    | inv _ ih =>
      exact continuous_moebiusInv.comp ih
  exact hgen (moebiusMap_generatedByElementary hdet)

/-- Every Möbius transformation `moebiusMap a b c d` (`a * d - b * c ≠ 0`) as a homeomorphism
`RiemannSphere ≃ₜ RiemannSphere`. -/
def moebiusHomeomorph {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) :
    RiemannSphere ≃ₜ RiemannSphere where
  toFun := moebiusMap a b c d
  invFun := moebiusMap d (-b) (-c) a
  left_inv := moebiusMap_inv_left hdet
  right_inv := moebiusMap_inv_right hdet
  continuous_toFun := moebiusMap_continuous hdet
  continuous_invFun := moebiusMap_continuous (by intro h0; apply hdet; linear_combination h0)

/-- Retraction extracting the finite complex coordinate (`0` at `∞`, `z` at `↑z`). -/
def sphereFinitePart (p : RiemannSphere) : ℂ :=
  OnePoint.rec 0 id p

@[simp] theorem sphereFinitePart_infty : sphereFinitePart ∞ = 0 := rfl
@[simp] theorem sphereFinitePart_coe (z : ℂ) : sphereFinitePart (z : RiemannSphere) = z := rfl

/-- Standard local chart center on `RiemannSphere`: `0` at `∞`, `z` at `↑z`. -/
def sphereChartCenter (p : RiemannSphere) : ℂ :=
  sphereFinitePart p

@[simp] theorem sphereChartCenter_infty : sphereChartCenter ∞ = 0 := rfl
@[simp] theorem sphereChartCenter_coe (z : ℂ) : sphereChartCenter (z : RiemannSphere) = z := rfl

/-- Standard local incoming chart `ℂ → RiemannSphere`: `moebiusInv ∘ coe` near `∞`, `coe` near `↑z`. -/
def sphereChartIn (p : RiemannSphere) (ζ : ℂ) : RiemannSphere :=
  OnePoint.rec (moebiusInv (ζ : RiemannSphere)) (fun _ => (ζ : RiemannSphere)) p

@[simp] theorem sphereChartIn_infty (ζ : ℂ) :
    sphereChartIn ∞ ζ = moebiusInv (ζ : RiemannSphere) := rfl
@[simp] theorem sphereChartIn_coe (z ζ : ℂ) :
    sphereChartIn (z : RiemannSphere) ζ = (ζ : RiemannSphere) := rfl

/-- Standard local outgoing chart `RiemannSphere → ℂ`: `sphereFinitePart ∘ moebiusInv` near `∞`,
`sphereFinitePart` near `↑w`. -/
def sphereChartOut (q : RiemannSphere) (r : RiemannSphere) : ℂ :=
  OnePoint.rec (sphereFinitePart (moebiusInv r)) (fun _ => sphereFinitePart r) q

@[simp] theorem sphereChartOut_infty (r : RiemannSphere) :
    sphereChartOut ∞ r = sphereFinitePart (moebiusInv r) := rfl
@[simp] theorem sphereChartOut_coe (w : ℂ) (r : RiemannSphere) :
    sphereChartOut (w : RiemannSphere) r = sphereFinitePart r := rfl

theorem moebiusInv_involutive (p : RiemannSphere) :
    moebiusInv (moebiusInv p) = p := by
  have hdet_inv : (0 : ℂ) * 0 - 1 * 1 ≠ 0 := by norm_num
  have hscale : ∀ q : RiemannSphere, moebiusMap 0 (-1) (-1) 0 q = moebiusInv q := fun q => by
    have := moebiusMap_scale (neg_ne_zero.mpr one_ne_zero) 0 1 1 0 q
    simpa [moebiusInv] using this
  rw [← hscale (moebiusInv p)]
  exact moebiusMap_inv_left hdet_inv p

@[simp] theorem sphereChartIn_center (p : RiemannSphere) :
    sphereChartIn p (sphereChartCenter p) = p := by
  induction p using OnePoint.rec <;> simp [moebiusInv]

@[simp] theorem sphereChartOut_self (q : RiemannSphere) :
    sphereChartOut q q = sphereChartCenter q := by
  induction q using OnePoint.rec <;> simp [moebiusInv]

theorem continuous_sphereChartIn (p : RiemannSphere) :
    Continuous (sphereChartIn p) := by
  induction p using OnePoint.rec with
  | infty => exact continuous_moebiusInv.comp OnePoint.continuous_coe
  | coe _ => exact OnePoint.continuous_coe

theorem eventually_sphereChartIn_out (q : RiemannSphere) :
    ∀ᶠ r in 𝓝 q, sphereChartIn q (sphereChartOut q r) = r := by
  induction q using OnePoint.rec with
  | infty =>
    have hmem : ({((0 : ℂ) : RiemannSphere)}ᶜ : Set RiemannSphere) ∈ 𝓝 (∞ : RiemannSphere) :=
      isClosed_singleton.isOpen_compl.mem_nhds (OnePoint.coe_ne_infty 0).symm
    filter_upwards [hmem] with r hr
    induction r using OnePoint.rec with
    | infty => simp [moebiusInv]
    | coe w =>
      have hw : w ≠ 0 := fun h0 => hr (by simp [h0])
      have h1 : moebiusInv (w : RiemannSphere) = ((w⁻¹ : ℂ) : RiemannSphere) := by
        simp [moebiusInv, hw]
      simp only [sphereChartOut_infty, sphereChartIn_infty, h1, sphereFinitePart_coe]
      rw [← h1]
      exact moebiusInv_involutive (w : RiemannSphere)
  | coe w =>
    filter_upwards [OnePoint.isOpenEmbedding_coe.isOpen_range.mem_nhds ⟨w, rfl⟩] with r hr
    rcases hr with ⟨u, rfl⟩
    simp

/-- Holomorphicity of a map `f : RiemannSphere → RiemannSphere` on a subset `Ω ⊆ RiemannSphere`,
expressed in the standard local complex charts `(ℂ, id)` on `ℂ` and `(ℂ, 1/z)` near `∞`. -/
def SphericalHolomorphicOn (f : RiemannSphere → RiemannSphere) (Ω : Set RiemannSphere) : Prop :=
  ContinuousOn f Ω ∧
  ∀ p ∈ Ω, DifferentiableAt ℂ (fun ζ : ℂ => sphereChartOut (f p) (f (sphereChartIn p ζ)))
    (sphereChartCenter p)

theorem sphericalHolomorphicOn_id (Ω : Set RiemannSphere) :
    SphericalHolomorphicOn id Ω := by
  refine ⟨continuousOn_id, fun p _ => ?_⟩
  induction p using OnePoint.rec with
  | infty =>
    have hfun : (fun ζ : ℂ => sphereChartOut (id ∞) (id (sphereChartIn ∞ ζ))) = id := by
      ext ζ; simp [moebiusInv_involutive]
    rw [hfun]; exact differentiableAt_id
  | coe z =>
    have hfun : (fun ζ : ℂ => sphereChartOut (id (z : RiemannSphere))
        (id (sphereChartIn (z : RiemannSphere) ζ))) = id := by
      ext ζ; simp
    rw [hfun]; exact differentiableAt_id

theorem SphericalHolomorphicOn.mono {f : RiemannSphere → RiemannSphere}
    {Ω₁ Ω₂ : Set RiemannSphere} (hf : SphericalHolomorphicOn f Ω₂) (hsub : Ω₁ ⊆ Ω₂) :
    SphericalHolomorphicOn f Ω₁ :=
  ⟨hf.1.mono hsub, fun p hp => hf.2 p (hsub hp)⟩

theorem SphericalHolomorphicOn.congr {f g : RiemannSphere → RiemannSphere}
    {Ω : Set RiemannSphere} (hΩ : IsOpen Ω) (hf : SphericalHolomorphicOn f Ω)
    (heq : Set.EqOn f g Ω) : SphericalHolomorphicOn g Ω := by
  refine ⟨hf.1.congr heq.symm, fun p hp => ?_⟩
  rw [← heq hp]
  refine (hf.2 p hp).congr_of_eventuallyEq ?_
  have h_in : ∀ᶠ ζ in 𝓝 (sphereChartCenter p), sphereChartIn p ζ ∈ Ω := by
    have hc : ContinuousAt (sphereChartIn p) (sphereChartCenter p) :=
      (continuous_sphereChartIn p).continuousAt
    refine hc.preimage_mem_nhds ?_
    rw [sphereChartIn_center]
    exact hΩ.mem_nhds hp
  filter_upwards [h_in] with ζ hζ
  rw [heq hζ]

theorem SphericalHolomorphicOn.comp {f g : RiemannSphere → RiemannSphere}
    {Ω₁ Ω₂ : Set RiemannSphere} (hΩ₁ : IsOpen Ω₁)
    (hg : SphericalHolomorphicOn g Ω₂) (hf : SphericalHolomorphicOn f Ω₁)
    (hmaps : MapsTo f Ω₁ Ω₂) :
    SphericalHolomorphicOn (g ∘ f) Ω₁ := by
  refine ⟨hg.1.comp hf.1 hmaps, fun p hp => ?_⟩
  have hfp : f p ∈ Ω₂ := hmaps hp
  have hf_at : ContinuousAt f p := hf.1.continuousAt (hΩ₁.mem_nhds hp)
  have hd_f := hf.2 p hp
  have hd_g := hg.2 (f p) hfp
  have hcenter : sphereChartOut (f p) (f (sphereChartIn p (sphereChartCenter p))) =
      sphereChartCenter (f p) := by
    rw [sphereChartIn_center, sphereChartOut_self]
  rw [← hcenter] at hd_g
  have hd_comp := hd_g.comp (sphereChartCenter p) hd_f
  refine hd_comp.congr_of_eventuallyEq ?_
  have hc_in : ContinuousAt (fun ζ => f (sphereChartIn p ζ)) (sphereChartCenter p) := by
    have h1 := (continuous_sphereChartIn p).continuousAt (x := sphereChartCenter p)
    have h2 : ContinuousAt f (sphereChartIn p (sphereChartCenter p)) := by
      rwa [sphereChartIn_center]
    exact h2.comp h1
  have hev_q : ∀ᶠ r in 𝓝 (f (sphereChartIn p (sphereChartCenter p))),
      sphereChartIn (f p) (sphereChartOut (f p) r) = r := by
    rw [sphereChartIn_center]
    exact eventually_sphereChartIn_out (f p)
  filter_upwards [hc_in.preimage_mem_nhds hev_q] with ζ hζ
  dsimp [Function.comp_def] at hζ ⊢
  rw [hζ]

theorem sphericalHolomorphicOn_moebiusAffine {a b : ℂ} (ha : a ≠ 0) :
    SphericalHolomorphicOn (moebiusMap a b 0 1) Set.univ := by
  refine ⟨(continuous_moebiusAffine ha).continuousOn, fun p _ => ?_⟩
  induction p using OnePoint.rec with
  | infty =>
    have hinf : moebiusMap a b 0 1 ∞ = ∞ := by simp
    rw [hinf, sphereChartCenter_infty]
    let φ : ℂ → ℂ := fun ζ => ζ / (a + b * ζ)
    have hφ_diff : DifferentiableAt ℂ φ 0 :=
      differentiableAt_id.div
        ((differentiableAt_const a).add ((differentiableAt_const b).mul differentiableAt_id))
        (by simp [ha])
    refine hφ_diff.congr_of_eventuallyEq ?_
    have hopen : IsOpen {ζ : ℂ | a + b * ζ ≠ 0} :=
      isOpen_ne_fun (continuous_const.add (continuous_const.mul continuous_id)) continuous_const
    filter_upwards [hopen.mem_nhds (by simp [ha] : a + b * 0 ≠ 0)] with ζ hζ
    by_cases hζ0 : ζ = 0
    · subst hζ0; simp [φ, moebiusInv]
    · have h1 : sphereChartIn ∞ ζ = ((ζ⁻¹ : ℂ) : RiemannSphere) := by
        simp [moebiusInv, hζ0]
      have h2 : moebiusMap a b 0 1 ((ζ⁻¹ : ℂ) : RiemannSphere) =
          (((a * ζ⁻¹ + b : ℂ)) : RiemannSphere) := by simp
      have hnz : a * ζ⁻¹ + b ≠ 0 := by
        have heq : a * ζ⁻¹ + b = (a + b * ζ) / ζ := by field_simp [hζ0]
        rw [heq]; exact div_ne_zero hζ hζ0
      have h3 : sphereChartOut ∞ (((a * ζ⁻¹ + b : ℂ)) : RiemannSphere) = (a * ζ⁻¹ + b)⁻¹ := by
        simp [moebiusInv, hnz]
      rw [h1, h2, h3]
      dsimp [φ]
      field_simp [hζ0, hζ]
  | coe z =>
    have hfun : (fun ζ : ℂ => sphereChartOut (moebiusMap a b 0 1 (z : RiemannSphere))
        (moebiusMap a b 0 1 (sphereChartIn (z : RiemannSphere) ζ))) =
        fun ζ => a * ζ + b := by
      ext ζ; simp
    rw [hfun]
    exact ((differentiableAt_const a).mul differentiableAt_id).add (differentiableAt_const b)

theorem sphericalHolomorphicOn_moebiusInv :
    SphericalHolomorphicOn moebiusInv Set.univ := by
  refine ⟨continuous_moebiusInv.continuousOn, fun p _ => ?_⟩
  induction p using OnePoint.rec with
  | infty =>
    have hfun : (fun ζ : ℂ => sphereChartOut (moebiusInv ∞)
        (moebiusInv (sphereChartIn ∞ ζ))) = id := by
      ext ζ
      have hinf : moebiusInv ∞ = ((0 : ℂ) : RiemannSphere) := by simp [moebiusInv]
      rw [hinf]
      simp [moebiusInv_involutive]
    rw [hfun]; exact differentiableAt_id
  | coe z =>
    by_cases hz : z = 0
    · subst hz
      have hfun : (fun ζ : ℂ => sphereChartOut (moebiusInv ((0 : ℂ) : RiemannSphere))
          (moebiusInv (sphereChartIn ((0 : ℂ) : RiemannSphere) ζ))) = id := by
        ext ζ
        have h0 : moebiusInv ((0 : ℂ) : RiemannSphere) = ∞ := by simp [moebiusInv]
        rw [h0]
        simp [moebiusInv_involutive]
      rw [hfun]; exact differentiableAt_id
    · rw [sphereChartCenter_coe]
      have hval : moebiusInv (z : RiemannSphere) = ((z⁻¹ : ℂ) : RiemannSphere) := by
        simp [moebiusInv, hz]
      rw [hval]
      refine (differentiableAt_inv hz).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ne.mem_nhds hz] with ζ hζ
      simp [moebiusInv, hζ]

/-- Every Möbius transformation `moebiusMap a b c d` (`a * d - b * c ≠ 0`) is globally
spherical-holomorphic on `RiemannSphere`. -/
theorem moebiusMap_sphericalHolomorphicOn {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) :
    SphericalHolomorphicOn (moebiusMap a b c d) Set.univ := by
  have hgen : ∀ {f : RiemannSphere → RiemannSphere},
      GeneratedByElementaryMoebius f → SphericalHolomorphicOn f Set.univ := by
    intro f hf
    induction hf with
    | id => exact sphericalHolomorphicOn_id Set.univ
    | trans β _ ih =>
      exact (sphericalHolomorphicOn_moebiusAffine one_ne_zero).comp isOpen_univ ih (mapsTo_univ _ _)
    | rot u hu _ ih =>
      have hu_ne : u ≠ 0 := by intro h0; simp [h0] at hu
      exact (sphericalHolomorphicOn_moebiusAffine hu_ne).comp isOpen_univ ih (mapsTo_univ _ _)
    | dil r hr _ ih =>
      exact (sphericalHolomorphicOn_moebiusAffine
        (Complex.ofReal_ne_zero.mpr hr.ne')).comp isOpen_univ ih (mapsTo_univ _ _)
    | inv _ ih =>
      exact sphericalHolomorphicOn_moebiusInv.comp isOpen_univ ih (mapsTo_univ _ _)
  exact hgen (moebiusMap_generatedByElementary hdet)

/-- Compatibility between `SphericalHolomorphicOn` and planar `HolomorphicOn` on open sets `Ω₀ ⊆ ℂ`
whose image avoids `∞`. -/
theorem sphericalHolomorphicOn_coe_iff {Ω₀ : Set ℂ} (hΩ₀ : IsOpen Ω₀)
    {f : RiemannSphere → RiemannSphere}
    (hfin : ∀ z ∈ Ω₀, f (z : RiemannSphere) ≠ ∞) :
    SphericalHolomorphicOn f (((↑) : ℂ → RiemannSphere) '' Ω₀) ↔
    RudinRCA.Chapter10.HolomorphicOn
      (fun z : ℂ => sphereFinitePart (f (z : RiemannSphere))) Ω₀ := by
  let g : ℂ → ℂ := fun z => sphereFinitePart (f (z : RiemannSphere))
  have hfg : ∀ z ∈ Ω₀, f (z : RiemannSphere) = (g z : RiemannSphere) := by
    intro z hz
    generalize hq : f (z : RiemannSphere) = q
    induction q using OnePoint.rec with
    | infty => exact False.elim (hfin z hz hq)
    | coe w => simp [g, hq]
  constructor
  · intro hf z hz
    have hd := hf.2 (z : RiemannSphere) ⟨z, hz, rfl⟩
    rw [hfg z hz] at hd
    simpa [g] using hd
  · intro hg
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases hp with ⟨z, hz, rfl⟩
      have hopen_img : IsOpen (((↑) : ℂ → RiemannSphere) '' Ω₀) :=
        OnePoint.isOpenEmbedding_coe.isOpenMap _ hΩ₀
      let F : RiemannSphere → RiemannSphere := OnePoint.rec ∞ (fun w : ℂ => (g w : RiemannSphere))
      refine ContinuousAt.continuousWithinAt ?_
      have hev : f =ᶠ[𝓝 (z : RiemannSphere)] F := by
        filter_upwards [hopen_img.mem_nhds ⟨z, hz, rfl⟩] with q hq
        rcases hq with ⟨w, hw, rfl⟩
        exact hfg w hw
      refine ContinuousAt.congr ?_ hev.symm
      rw [ContinuousAt, Tendsto]
      have hmap : map F (𝓝 (z : RiemannSphere)) =
          map (fun w : ℂ => (g w : RiemannSphere)) (𝓝 z) := by
        rw [← OnePoint.isOpenEmbedding_coe.map_nhds_eq z, Filter.map_map]; rfl
      rw [hmap]
      exact OnePoint.continuous_coe.continuousAt.comp (hg z hz).continuousAt
    · rintro p ⟨z, hz, rfl⟩
      rw [hfg z hz]
      simpa [g] using hg z hz

/-! ### Part 3: Spherical Regions, Simple Connectedness, Simple Boundary Points, and Half-Plane Möbius Maps -/

/-- A region in `RiemannSphere` is a nonempty connected open subset. -/
def IsSphericalRegion (Ω : Set RiemannSphere) : Prop :=
  IsOpen Ω ∧ IsConnected Ω

/-- Simple connectedness for a spherical region `Ω ⊆ RiemannSphere` (exact `RiemannSphere`
analog of `RudinRCA.Chapter10.BookSimplyConnected`). -/
def SphericalSimplyConnected (Ω : Set RiemannSphere) : Prop :=
  IsSphericalRegion Ω ∧ ∀ γ : ℝ → RiemannSphere,
    ContinuousOn γ (Icc (0 : ℝ) 1) → γ '' Icc (0 : ℝ) 1 ⊆ Ω → γ 0 = γ 1 →
    RudinRCA.Chapter10.IsNullHomotopicIn Ω γ

/-- Simple boundary point for a region `Ω ⊆ RiemannSphere` (exact `RiemannSphere` analog of
`IsSimpleBoundaryPoint` in Definition `14.16`). -/
def IsSphericalSimpleBoundaryPoint (Ω : Set RiemannSphere) (β : RiemannSphere) : Prop :=
  β ∈ frontier Ω ∧
  ∀ α : ℕ → RiemannSphere, (∀ n, α n ∈ Ω) → Tendsto α atTop (𝓝 β) →
    ∃ γ : ℝ → RiemannSphere, ContinuousOn γ (Icc (0 : ℝ) 1) ∧
      (∀ s ∈ Ico (0 : ℝ) 1, γ s ∈ Ω) ∧
      ∃ t : ℕ → ℝ, StrictMono t ∧ (∀ n, t n ∈ Ioo (0 : ℝ) 1) ∧
        Tendsto t atTop (𝓝 1) ∧ ∀ n, γ (t n) = α n

theorem isSphericalRegion_image_homeomorph (e : RiemannSphere ≃ₜ RiemannSphere)
    {Ω : Set RiemannSphere} (hΩ : IsSphericalRegion Ω) :
    IsSphericalRegion (e '' Ω) :=
  ⟨e.isOpenMap _ hΩ.1, hΩ.2.image e e.continuous.continuousOn⟩

theorem sphericalSimplyConnected_image_homeomorph (e : RiemannSphere ≃ₜ RiemannSphere)
    {Ω : Set RiemannSphere} (h : SphericalSimplyConnected Ω) :
    SphericalSimplyConnected (e '' Ω) := by
  refine ⟨isSphericalRegion_image_homeomorph e h.1, fun γ hγc hγΩ hγcl => ?_⟩
  let γ₀ : ℝ → RiemannSphere := fun t => e.symm (γ t)
  have hγ₀_c : ContinuousOn γ₀ (Icc (0 : ℝ) 1) := e.symm.continuous.comp_continuousOn hγc
  have hγ₀_Ω : γ₀ '' Icc (0 : ℝ) 1 ⊆ Ω := by
    rintro _ ⟨t, ht, rfl⟩
    rcases hγΩ ⟨t, ht, rfl⟩ with ⟨p, hp, hp_eq⟩
    dsimp [γ₀]; rw [← hp_eq, e.symm_apply_apply]; exact hp
  have hγ₀_cl : γ₀ 0 = γ₀ 1 := by dsimp [γ₀]; rw [hγcl]
  rcases h.2 γ₀ hγ₀_c hγ₀_Ω hγ₀_cl with
    ⟨c₀, hc₀, _, _, _, _, _, _, H₀, hH₀_cont, hH₀_in, hH₀_0, hH₀_1, hH₀_loop⟩
  refine ⟨e c₀, ⟨c₀, hc₀, rfl⟩, hγc, continuousOn_const, hγΩ, ?_, hγcl, rfl,
    e ∘ H₀, e.continuous.comp_continuousOn hH₀_cont, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨_, _, rfl⟩; exact ⟨c₀, hc₀, rfl⟩
  · rintro _ ⟨q, hq, rfl⟩; exact ⟨H₀ q, hH₀_in ⟨q, hq, rfl⟩, rfl⟩
  · intro s hs; dsimp only [Function.comp_def]; rw [hH₀_0 s hs]; exact e.apply_symm_apply (γ s)
  · intro s hs; dsimp only [Function.comp_def]; rw [hH₀_1 s hs]
  · intro t ht; dsimp only [Function.comp_def]; rw [hH₀_loop t ht]

theorem isSphericalSimpleBoundaryPoint_image_homeomorph (e : RiemannSphere ≃ₜ RiemannSphere)
    {Ω : Set RiemannSphere} {β : RiemannSphere}
    (hβ : IsSphericalSimpleBoundaryPoint Ω β) :
    IsSphericalSimpleBoundaryPoint (e '' Ω) (e β) := by
  refine ⟨by rw [← e.image_frontier]; exact ⟨β, hβ.1, rfl⟩, fun α hα_mem hα_lim => ?_⟩
  let α₀ : ℕ → RiemannSphere := e.symm ∘ α
  have hα₀_mem : ∀ n, α₀ n ∈ Ω := fun n => by
    rcases hα_mem n with ⟨p, hp, hp_eq⟩
    dsimp [α₀]; rw [← hp_eq, e.symm_apply_apply]; exact hp
  have hα₀_lim : Tendsto α₀ atTop (𝓝 β) := by
    simpa [α₀] using (e.symm.continuous.tendsto (e β)).comp hα_lim
  obtain ⟨γ₀, hγ₀_c, hγ₀_in, t, ht_mono, ht_mem, ht_lim, hγ₀_t⟩ := hβ.2 α₀ hα₀_mem hα₀_lim
  refine ⟨e ∘ γ₀, e.continuous.comp_continuousOn hγ₀_c,
    fun s hs => ⟨γ₀ s, hγ₀_in s hs, rfl⟩, t, ht_mono, ht_mem, ht_lim, fun n => ?_⟩
  dsimp only [Function.comp_def]
  rw [hγ₀_t n]; exact e.apply_symm_apply (α n)

/-- Closure and frontier of `((↑) : ℂ → RiemannSphere) '' S` for a bounded set `S ⊆ ℂ`. -/
theorem closure_and_frontier_coe_of_isBounded {S : Set ℂ} (hS_open : IsOpen S)
    (hS_bdd : Bornology.IsBounded S) :
    closure (((↑) : ℂ → RiemannSphere) '' S) = ((↑) : ℂ → RiemannSphere) '' closure S ∧
    frontier (((↑) : ℂ → RiemannSphere) '' S) = ((↑) : ℂ → RiemannSphere) '' frontier S := by
  have hcl_compact : IsCompact (closure S) := hS_bdd.isCompact_closure
  have himg_closed : IsClosed (((↑) : ℂ → RiemannSphere) '' closure S) :=
    (hcl_compact.image OnePoint.continuous_coe).isClosed
  have hcl_eq : closure (((↑) : ℂ → RiemannSphere) '' S) =
      ((↑) : ℂ → RiemannSphere) '' closure S := by
    refine Subset.antisymm ?_ ?_
    · exact closure_minimal (Set.image_mono subset_closure) himg_closed
    · exact image_closure_subset_closure_image OnePoint.continuous_coe
  refine ⟨hcl_eq, ?_⟩
  have hopen_img : IsOpen (((↑) : ℂ → RiemannSphere) '' S) :=
    OnePoint.isOpenEmbedding_coe.isOpenMap _ hS_open
  rw [frontier, hcl_eq, hopen_img.interior_eq]
  ext p
  constructor
  · rintro ⟨⟨z, hz_cl, rfl⟩, hnot⟩
    exact ⟨z, ⟨hz_cl, by rw [hS_open.interior_eq]; exact fun hz => hnot ⟨z, hz, rfl⟩⟩, rfl⟩
  · rintro ⟨z, ⟨hz_cl, hz_not⟩, rfl⟩
    rw [hS_open.interior_eq] at hz_not
    refine ⟨⟨z, hz_cl, rfl⟩, ?_⟩
    rintro ⟨w, hw, heq⟩
    exact hz_not (OnePoint.coe_injective heq ▸ hw)

/-- If `Ω₀ ⊆ ℂ` is a bounded region and `((↑) : ℂ → RiemannSphere) '' Ω₀` satisfies
`SphericalSimplyConnected` and all spherical boundary points are simple, then `Ω₀` satisfies
`BookSimplyConnected Ω₀` and all planar boundary points are simple (and conversely). -/
theorem bounded_plane_region_spherical_iff {Ω₀ : Set ℂ}
    (hΩ₀_open : IsOpen Ω₀) (hΩ₀_bdd : Bornology.IsBounded Ω₀) :
    (IsSphericalRegion (((↑) : ℂ → RiemannSphere) '' Ω₀) ↔ RudinRCA.Chapter10.IsRegion Ω₀) ∧
    (SphericalSimplyConnected (((↑) : ℂ → RiemannSphere) '' Ω₀) ↔
      RudinRCA.Chapter10.BookSimplyConnected Ω₀) ∧
    ((∀ β ∈ frontier (((↑) : ℂ → RiemannSphere) '' Ω₀),
        IsSphericalSimpleBoundaryPoint (((↑) : ℂ → RiemannSphere) '' Ω₀) β) ↔
      (∀ β₀ ∈ frontier Ω₀, IsSimpleBoundaryPoint Ω₀ β₀)) := by
  let S : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' Ω₀
  obtain ⟨_, hfr_eq⟩ := closure_and_frontier_coe_of_isBounded hΩ₀_open hΩ₀_bdd
  have hreg_iff : IsSphericalRegion S ↔ RudinRCA.Chapter10.IsRegion Ω₀ := by
    constructor
    · rintro ⟨_, hconn⟩
      refine ⟨hΩ₀_open, ?_⟩
      have hpre : Ω₀ = ((↑) : ℂ → RiemannSphere) ⁻¹' S :=
        (Set.preimage_image_eq Ω₀ OnePoint.coe_injective).symm
      rcases hconn.nonempty with ⟨_, z₀, hz₀, rfl⟩
      refine ⟨⟨z₀, hz₀⟩, ?_⟩
      intro U V hU hV hsub hU_ne hV_ne
      have hU' : IsOpen (((↑) : ℂ → RiemannSphere) '' U) :=
        OnePoint.isOpenEmbedding_coe.isOpenMap _ hU
      have hV' : IsOpen (((↑) : ℂ → RiemannSphere) '' V) :=
        OnePoint.isOpenEmbedding_coe.isOpenMap _ hV
      have hsub' : S ⊆ ((↑) : ℂ → RiemannSphere) '' U ∪ ((↑) : ℂ → RiemannSphere) '' V := by
        rintro _ ⟨z, hz, rfl⟩
        exact (hsub hz).imp (fun h => ⟨z, h, rfl⟩) (fun h => ⟨z, h, rfl⟩)
      rcases hU_ne with ⟨z₁, hz₁, hz₁U⟩
      rcases hV_ne with ⟨z₂, hz₂, hz₂V⟩
      rcases hconn.isPreconnected _ _ hU' hV' hsub'
        ⟨z₁, ⟨z₁, hz₁, rfl⟩, z₁, hz₁U, rfl⟩ ⟨z₂, ⟨z₂, hz₂, rfl⟩, z₂, hz₂V, rfl⟩ with
        ⟨_, ⟨z, hz, rfl⟩, ⟨u, hu, hu_eq⟩, ⟨v, hv, hv_eq⟩⟩
      exact ⟨z, hz, OnePoint.coe_injective hu_eq ▸ hu, OnePoint.coe_injective hv_eq ▸ hv⟩
    · rintro ⟨hopen, hconn⟩
      exact ⟨OnePoint.isOpenEmbedding_coe.isOpenMap _ hopen,
        hconn.image _ OnePoint.continuous_coe.continuousOn⟩
  have hret_at : ∀ z : ℂ, ContinuousAt sphereFinitePart (z : RiemannSphere) := by
    intro z
    rw [ContinuousAt, Tendsto]
    have hmap : map sphereFinitePart (𝓝 (z : RiemannSphere)) = 𝓝 z := by
      rw [← OnePoint.isOpenEmbedding_coe.map_nhds_eq z, Filter.map_map]
      simp [Function.comp_def]
    rw [hmap, sphereFinitePart_coe]
  have hret_cont_on_range : ContinuousOn sphereFinitePart
      (Set.range ((↑) : ℂ → RiemannSphere)) := by
    rintro p ⟨z, rfl⟩
    exact (hret_at z).continuousWithinAt
  refine ⟨hreg_iff, ?_, ?_⟩
  · constructor
    · rintro ⟨hS_reg, hS_sc⟩
      refine ⟨hreg_iff.mp hS_reg, fun γ hγc hγΩ hγcl => ?_⟩
      let γS : ℝ → RiemannSphere := fun t => (γ t : RiemannSphere)
      have hγSc : ContinuousOn γS (Icc (0 : ℝ) 1) :=
        OnePoint.continuous_coe.comp_continuousOn hγc
      have hγS_in : γS '' Icc (0 : ℝ) 1 ⊆ S := by
        rintro _ ⟨t, ht, rfl⟩; exact ⟨γ t, hγΩ ⟨t, ht, rfl⟩, rfl⟩
      have hγS_cl : γS 0 = γS 1 := by dsimp [γS]; rw [hγcl]
      rcases hS_sc γS hγSc hγS_in hγS_cl with
        ⟨_, ⟨z₀, hz₀, rfl⟩, _, _, _, _, _, _, HS, hHS_c, hHS_in, hHS_0, hHS_1, hHS_loop⟩
      have hHS_range : Set.MapsTo HS (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
          (Set.range ((↑) : ℂ → RiemannSphere)) := by
        intro q hq
        rcases hHS_in ⟨q, hq, rfl⟩ with ⟨z, _, hzq⟩
        exact ⟨z, hzq⟩
      refine ⟨z₀, hz₀, hγc, continuousOn_const, hγΩ, ?_, hγcl, rfl,
        sphereFinitePart ∘ HS, hret_cont_on_range.comp hHS_c hHS_range,
        ?_, ?_, ?_, ?_⟩
      · rintro _ ⟨_, _, rfl⟩; exact hz₀
      · rintro _ ⟨q, hq, rfl⟩
        rcases hHS_in ⟨q, hq, rfl⟩ with ⟨z, hz, hzq⟩
        dsimp only [Function.comp_def]; rw [← hzq, sphereFinitePart_coe]; exact hz
      · intro s hs; dsimp only [Function.comp_def]; rw [hHS_0 s hs]; rfl
      · intro s hs; dsimp only [Function.comp_def]; rw [hHS_1 s hs]; rfl
      · intro t ht; dsimp only [Function.comp_def]; rw [hHS_loop t ht]
    · rintro ⟨hΩ₀_reg, hΩ₀_sc⟩
      refine ⟨hreg_iff.mpr hΩ₀_reg, fun γS hγSc hγS_in hγS_cl => ?_⟩
      have hγS_range : Set.MapsTo γS (Icc (0 : ℝ) 1) (Set.range ((↑) : ℂ → RiemannSphere)) := by
        intro t ht
        rcases hγS_in ⟨t, ht, rfl⟩ with ⟨z, _, hzt⟩
        exact ⟨z, hzt⟩
      let γ : ℝ → ℂ := sphereFinitePart ∘ γS
      have hγc : ContinuousOn γ (Icc (0 : ℝ) 1) := hret_cont_on_range.comp hγSc hγS_range
      have hγ_coe : ∀ t ∈ Icc (0 : ℝ) 1, (γ t : RiemannSphere) = γS t := by
        intro t ht
        rcases hγS_in ⟨t, ht, rfl⟩ with ⟨z, _, hzt⟩
        dsimp [γ]; rw [← hzt, sphereFinitePart_coe]
      have hγΩ : γ '' Icc (0 : ℝ) 1 ⊆ Ω₀ := by
        rintro _ ⟨t, ht, rfl⟩
        rcases hγS_in ⟨t, ht, rfl⟩ with ⟨z, hz, hzt⟩
        dsimp [γ]; rw [← hzt, sphereFinitePart_coe]; exact hz
      have hγcl : γ 0 = γ 1 := by
        dsimp [γ]; rw [hγS_cl]
      rcases hΩ₀_sc γ hγc hγΩ hγcl with
        ⟨z₀, hz₀, _, _, _, _, _, _, H₀, hH₀_c, hH₀_in, hH₀_0, hH₀_1, hH₀_loop⟩
      refine ⟨(z₀ : RiemannSphere), ⟨z₀, hz₀, rfl⟩, hγSc, continuousOn_const, hγS_in, ?_,
        hγS_cl, rfl, ((↑) : ℂ → RiemannSphere) ∘ H₀,
        OnePoint.continuous_coe.comp_continuousOn hH₀_c, ?_, ?_, ?_, ?_⟩
      · rintro _ ⟨_, _, rfl⟩; exact ⟨z₀, hz₀, rfl⟩
      · rintro _ ⟨q, hq, rfl⟩; exact ⟨H₀ q, hH₀_in ⟨q, hq, rfl⟩, rfl⟩
      · intro s hs; dsimp only [Function.comp_def]; rw [hH₀_0 s hs]; exact hγ_coe s hs
      · intro s hs; dsimp only [Function.comp_def]; rw [hH₀_1 s hs]
      · intro t ht; dsimp only [Function.comp_def]; rw [hH₀_loop t ht]
  · constructor
    · intro hall β₀ hβ₀
      refine ⟨hβ₀, fun α hα_mem hα_lim => ?_⟩
      have hβS : (β₀ : RiemannSphere) ∈ frontier S := by
        rw [hfr_eq]; exact ⟨β₀, hβ₀, rfl⟩
      obtain ⟨γS, hγS_c, hγS_in, t, ht_mono, ht_mem, ht_lim, hγS_t⟩ :=
        (hall (β₀ : RiemannSphere) hβS).2 (fun n => (α n : RiemannSphere))
          (fun n => ⟨α n, hα_mem n, rfl⟩)
          (OnePoint.continuous_coe.continuousAt.tendsto.comp hα_lim)
      have hγS_1 : γS 1 = (β₀ : RiemannSphere) := by
        have ht_nhds : Tendsto t atTop (𝓝[Icc (0 : ℝ) 1] 1) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within t ht_lim
            (Filter.Eventually.of_forall fun n => Ioo_subset_Icc_self (ht_mem n))
        have hlim1 : Tendsto (γS ∘ t) atTop (𝓝 (γS 1)) :=
          (hγS_c 1 (right_mem_Icc.mpr zero_le_one)).tendsto.comp ht_nhds
        have hlim2 : Tendsto (γS ∘ t) atTop (𝓝 (β₀ : RiemannSphere)) := by
          have heq : γS ∘ t = fun n => (α n : RiemannSphere) := funext hγS_t
          rw [heq]
          exact OnePoint.continuous_coe.continuousAt.tendsto.comp hα_lim
        exact tendsto_nhds_unique hlim1 hlim2
      have hγS_range : Set.MapsTo γS (Icc (0 : ℝ) 1) (Set.range ((↑) : ℂ → RiemannSphere)) := by
        intro s hs
        by_cases hs1 : s = 1
        · rw [hs1, hγS_1]; exact ⟨β₀, rfl⟩
        · have hs_lt : s < 1 := lt_of_le_of_ne hs.2 hs1
          rcases hγS_in s ⟨hs.1, hs_lt⟩ with ⟨z, _, hzs⟩
          exact ⟨z, hzs⟩
      refine ⟨sphereFinitePart ∘ γS, hret_cont_on_range.comp hγS_c hγS_range,
        fun s hs => ?_, t, ht_mono, ht_mem, ht_lim, fun n => ?_⟩
      · rcases hγS_in s hs with ⟨z, hz, hzs⟩
        dsimp only [Function.comp_def]; rw [← hzs, sphereFinitePart_coe]; exact hz
      · dsimp only [Function.comp_def]; rw [hγS_t n, sphereFinitePart_coe]
    · intro hall β hβ
      rw [hfr_eq] at hβ
      rcases hβ with ⟨β₀, hβ₀, rfl⟩
      refine ⟨by rw [hfr_eq]; exact ⟨β₀, hβ₀, rfl⟩, fun αS hαS_mem hαS_lim => ?_⟩
      have hαS_fin : ∀ n, ∃ z ∈ Ω₀, αS n = (z : RiemannSphere) := fun n => by
        rcases hαS_mem n with ⟨z, hz, hzn⟩
        exact ⟨z, hz, hzn.symm⟩
      let α : ℕ → ℂ := sphereFinitePart ∘ αS
      have hα_coe : ∀ n, (α n : RiemannSphere) = αS n := fun n => by
        rcases hαS_fin n with ⟨z, _, hzn⟩
        dsimp [α]; rw [hzn, sphereFinitePart_coe]
      have hα_mem : ∀ n, α n ∈ Ω₀ := fun n => by
        rcases hαS_fin n with ⟨z, hz, hzn⟩
        dsimp [α]; rw [hzn, sphereFinitePart_coe]; exact hz
      have hα_lim : Tendsto α atTop (𝓝 β₀) :=
        (hret_at β₀).tendsto.comp hαS_lim
      obtain ⟨γ, hγ_c, hγ_in, t, ht_mono, ht_mem, ht_lim, hγ_t⟩ :=
        (hall β₀ hβ₀).2 α hα_mem hα_lim
      refine ⟨((↑) : ℂ → RiemannSphere) ∘ γ, OnePoint.continuous_coe.comp_continuousOn hγ_c,
        fun s hs => ⟨γ s, hγ_in s hs, rfl⟩, t, ht_mono, ht_mem, ht_lim, fun n => ?_⟩
      dsimp only [Function.comp_def]; rw [hγ_t n, hα_coe n]

/-- Reduction of any spherical region `Ω ⊆ RiemannSphere` whose complement has nonempty interior
to a **bounded** planar region `Ω₀ ⊆ ℂ` via an invertible Möbius transformation `moebiusMap a b c d`. -/
theorem spherical_region_moebius_to_bounded_plane {Ω : Set RiemannSphere}
    (hΩ_sc : SphericalSimplyConnected Ω)
    (hcompl_int : (interior Ωᶜ).Nonempty)
    (hsimple : ∀ β ∈ frontier Ω, IsSphericalSimpleBoundaryPoint Ω β) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ ∃ Ω₀ : Set ℂ,
      RudinRCA.Chapter10.IsRegion Ω₀ ∧
      Bornology.IsBounded Ω₀ ∧
      RudinRCA.Chapter10.BookSimplyConnected Ω₀ ∧
      (∀ β₀ ∈ frontier Ω₀, IsSimpleBoundaryPoint Ω₀ β₀) ∧
      moebiusMap a b c d '' Ω = ((↑) : ℂ → RiemannSphere) '' Ω₀ := by
  obtain ⟨p₀, hp₀⟩ := hcompl_int
  obtain ⟨a, b, c, d, hdet, hMp₀⟩ :
      ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ moebiusMap a b c d p₀ = ∞ := by
    induction p₀ using OnePoint.rec with
    | infty => exact ⟨1, 0, 0, 1, by norm_num, by simp⟩
    | coe z₀ => exact ⟨0, 1, 1, -z₀, by norm_num, by simp⟩
  let e := moebiusHomeomorph hdet
  have he_fun : (e : RiemannSphere → RiemannSphere) = moebiusMap a b c d := rfl
  have hinf_int : (∞ : RiemannSphere) ∈ interior ((e '' Ω)ᶜ) := by
    have hcompl_eq : (e '' Ω)ᶜ = e '' (Ωᶜ) := (e.image_compl Ω).symm
    rw [hcompl_eq, ← e.image_interior]
    exact ⟨p₀, hp₀, hMp₀⟩
  have hnhds_inf : (e '' Ω)ᶜ ∈ 𝓝 (∞ : RiemannSphere) :=
    mem_interior_iff_mem_nhds.mp hinf_int
  obtain ⟨K, ⟨_, hK_compact⟩, hK_sub⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hnhds_inf
  let Ω₀ : Set ℂ := ((↑) : ℂ → RiemannSphere) ⁻¹' (e '' Ω)
  have hΩ₀_open : IsOpen Ω₀ :=
    (e.isOpenMap _ hΩ_sc.1.1).preimage OnePoint.continuous_coe
  have hΩ₀_sub_K : Ω₀ ⊆ K := by
    intro z hz
    by_contra hzK
    have hmem_compl : (z : RiemannSphere) ∈ ((↑) : ℂ → RiemannSphere) '' Kᶜ ∪ {∞} :=
      Or.inl ⟨z, hzK, rfl⟩
    exact hK_sub hmem_compl hz
  have hΩ₀_bdd : Bornology.IsBounded Ω₀ := hK_compact.isBounded.subset hΩ₀_sub_K
  have hinf_not : (∞ : RiemannSphere) ∉ e '' Ω :=
    fun hmem => mem_of_mem_nhds hnhds_inf hmem
  have himg_eq : e '' Ω = ((↑) : ℂ → RiemannSphere) '' Ω₀ := by
    ext q
    induction q using OnePoint.rec with
    | infty =>
      constructor
      · intro h; exact False.elim (hinf_not h)
      · rintro ⟨z, _, hz⟩; exact False.elim (OnePoint.coe_ne_infty z hz)
    | coe z =>
      constructor
      · intro hz; exact ⟨z, hz, rfl⟩
      · rintro ⟨w, hw, hwz⟩; exact OnePoint.coe_injective hwz ▸ hw
  have hS_sc : SphericalSimplyConnected (((↑) : ℂ → RiemannSphere) '' Ω₀) := by
    rw [← himg_eq]
    exact sphericalSimplyConnected_image_homeomorph e hΩ_sc
  have hS_simple : ∀ β ∈ frontier (((↑) : ℂ → RiemannSphere) '' Ω₀),
      IsSphericalSimpleBoundaryPoint (((↑) : ℂ → RiemannSphere) '' Ω₀) β := by
    rw [← himg_eq]
    intro β hβ
    rw [← e.image_frontier] at hβ
    rcases hβ with ⟨β', hβ', rfl⟩
    exact isSphericalSimpleBoundaryPoint_image_homeomorph e (hsimple β' hβ')
  obtain ⟨hreg_iff, hsc_iff, hsimp_iff⟩ := bounded_plane_region_spherical_iff hΩ₀_open hΩ₀_bdd
  have hΩ₀_sc : RudinRCA.Chapter10.BookSimplyConnected Ω₀ := hsc_iff.mp hS_sc
  exact ⟨a, b, c, d, hdet, Ω₀, hΩ₀_sc.1, hΩ₀_bdd, hΩ₀_sc, hsimp_iff.mp hS_simple, himg_eq⟩

/-- Explicit Möbius transformation `moebiusMap (1 - c) (1 + c) (-u) u` (`det = 2 * u ≠ 0`)
carrying `((↑) : ℂ → RiemannSphere) '' ball (0 : ℂ) 1` bijectively onto
`((↑) : ℂ → RiemannSphere) '' H` for every open half-plane `H = {w : ℂ | c < (u * w).re}` (`u ≠ 0`). -/
theorem openHalfPlane_moebius_bij {H : Set ℂ} (hH : IsOpenHalfPlane H) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
      BijOn (moebiusMap a b c d)
        (((↑) : ℂ → RiemannSphere) '' ball (0 : ℂ) 1)
        (((↑) : ℂ → RiemannSphere) '' H) := by
  rcases hH with ⟨u, r, hu, rfl⟩
  let a : ℂ := 1 - (r : ℂ)
  let b : ℂ := 1 + (r : ℂ)
  let c : ℂ := -u
  let d : ℂ := u
  have hdet : a * d - b * c ≠ 0 := by
    have heq : a * d - b * c = 2 * u := by dsimp [a, b, c, d]; ring
    rw [heq]; exact mul_ne_zero two_ne_zero hu
  obtain ⟨_, _, _, _, _, _, hcay_bij⟩ := cayleyMap_props
  have hval : ∀ z : ℂ, z ≠ 1 →
      moebiusMap a b c d (z : RiemannSphere) =
        (((cayleyMap z + (r : ℂ)) / u : ℂ) : RiemannSphere) := by
    intro z hz1
    have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
    have hden_eq : c * z + d = u * (1 - z) := by dsimp [c, d]; ring
    have hden : c * z + d ≠ 0 := by rw [hden_eq]; exact mul_ne_zero hu h1z
    simp only [moebiusMap_coe, hden, ↓reduceIte, OnePoint.coe_eq_coe]
    rw [hden_eq]
    dsimp [a, b, cayleyMap]
    field_simp [hu, h1z]
    ring
  refine ⟨a, b, c, d, hdet, ?_, (moebiusMap_bijective hdet).1.injOn, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hz1 : z ≠ 1 := by
      intro h1; rw [h1] at hz; simp at hz
    rw [hval z hz1]
    refine ⟨(cayleyMap z + (r : ℂ)) / u, ?_, rfl⟩
    have hw : 0 < (cayleyMap z).re := hcay_bij.mapsTo hz
    change r < (u * ((cayleyMap z + (r : ℂ)) / u)).re
    rw [mul_div_cancel₀ _ hu, Complex.add_re, Complex.ofReal_re]
    linarith
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : r < (u * w).re := hw
    let t : ℂ := u * w - (r : ℂ)
    have ht : t ∈ {ζ : ℂ | 0 < ζ.re} := by
      change 0 < (u * w - (r : ℂ)).re
      rw [Complex.sub_re, Complex.ofReal_re]
      exact sub_pos.mpr hw'
    obtain ⟨z, hz, hzt⟩ := hcay_bij.surjOn ht
    have hz1 : z ≠ 1 := by
      intro h1; rw [h1] at hz; simp at hz
    refine ⟨(z : RiemannSphere), ⟨z, hz, rfl⟩, ?_⟩
    rw [hval z hz1, hzt, OnePoint.coe_eq_coe]
    dsimp [t]
    field_simp [hu]; ring

/-! ### Final Glue: Public Theorems `14.20(a)`, `14.20(b)`, `14.20(c)`, `14.20(d)`, and `14.20` -/

private theorem mem_frontier_of_mem_closure_not_mem {α : Type*} [TopologicalSpace α]
    {s : Set α} {x : α} (hx : x ∈ closure s) (hnot : x ∉ s) : x ∈ frontier s :=
  ⟨hx, fun h => hnot (interior_subset h)⟩

theorem bounded_subset_ne_univ {S : Set ℂ} (hS : Bornology.IsBounded S) :
    S ≠ Set.univ := by
  intro hall
  obtain ⟨R, hR⟩ := hS.subset_ball (0 : ℂ)
  let z : ℂ := ((max R 0 + 1 : ℝ) : ℂ)
  have hz_mem : z ∈ ball (0 : ℂ) R := hR (hall ▸ Set.mem_univ z)
  have hz_lt : ‖z‖ < R := mem_ball_zero_iff.mp hz_mem
  have hz_pos : 0 < max R 0 + 1 := by linarith [le_max_right R 0]
  have hz_norm : ‖z‖ = max R 0 + 1 := by
    dsimp [z]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz_pos]
  linarith [le_max_left R 0]

theorem exists_riemann_map_of_bounded {Ω : Set ℂ}
    (hΩ_sc : RudinRCA.Chapter10.BookSimplyConnected Ω) (hΩ_bdd : Bornology.IsBounded Ω) :
    ∃ f₀ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn f₀ Ω ∧ BijOn f₀ Ω (ball (0 : ℂ) 1) :=
  theorem14_8.1 hΩ_sc.1 hΩ_sc (bounded_subset_ne_univ hΩ_bdd)

theorem unitDisc_all_simple :
    RudinRCA.Chapter10.BookSimplyConnected (ball (0 : ℂ) 1) ∧
    ∀ β ∈ frontier (ball (0 : ℂ) 1), IsSimpleBoundaryPoint (ball (0 : ℂ) 1) β := by
  refine jordanBoundary_region_converse
    (RudinRCA.Chapter10.disc_isRegion 0 zero_lt_one) isBounded_ball ?_
  rw [frontier_ball (0 : ℂ) one_ne_zero]
  exact ⟨Homeomorph.refl _⟩

/-- **14.20(a) (Jordan-curve boundary characterization and closed-disc homeomorphism,
RCA p. 291):**
1. *(Forward)* Under `14.19`'s hypotheses (`Ω` bounded simply connected region, every boundary point
   simple), `frontier Ω` is a Jordan curve and `closure Ω` is homeomorphic to `closedBall 0 1`.
2. *(Converse — stated without proof in Rudin; proved in full here)* Every bounded region `Ω ⊆ ℂ`
   whose boundary `frontier Ω` is a Jordan curve is simply connected (`BookSimplyConnected Ω`) and
   has only simple boundary points (`∀ β ∈ frontier Ω, IsSimpleBoundaryPoint Ω β`).
3. *(Equivalence)* For every bounded region `Ω ⊆ ℂ`,
   `(BookSimplyConnected Ω ∧ ∀ β ∈ frontier Ω, IsSimpleBoundaryPoint Ω β) ↔
     IsJordanCurve (frontier Ω)`. -/
theorem theorem14_20_part_a :
    (∀ {Ω : Set ℂ}, RudinRCA.Chapter10.BookSimplyConnected Ω →
      Bornology.IsBounded Ω →
      (∀ β ∈ frontier Ω, IsSimpleBoundaryPoint Ω β) →
      IsJordanCurve (frontier Ω) ∧ Nonempty (closure Ω ≃ₜ closedBall (0 : ℂ) 1)) ∧
    (∀ {Ω : Set ℂ}, RudinRCA.Chapter10.IsRegion Ω →
      Bornology.IsBounded Ω →
      IsJordanCurve (frontier Ω) →
      RudinRCA.Chapter10.BookSimplyConnected Ω ∧
        ∀ β ∈ frontier Ω, IsSimpleBoundaryPoint Ω β) ∧
    (∀ {Ω : Set ℂ}, RudinRCA.Chapter10.IsRegion Ω →
      Bornology.IsBounded Ω →
      ((RudinRCA.Chapter10.BookSimplyConnected Ω ∧
          ∀ β ∈ frontier Ω, IsSimpleBoundaryPoint Ω β) ↔
        IsJordanCurve (frontier Ω))) := by
  have hfwd : ∀ {Ω : Set ℂ}, RudinRCA.Chapter10.BookSimplyConnected Ω →
      Bornology.IsBounded Ω →
      (∀ β ∈ frontier Ω, IsSimpleBoundaryPoint Ω β) →
      IsJordanCurve (frontier Ω) ∧ Nonempty (closure Ω ≃ₜ closedBall (0 : ℂ) 1) := by
    intro Ω hΩ_sc hΩ_bdd hΩ_simple
    obtain ⟨f₀, hf₀_holo, hf₀_bij⟩ := exists_riemann_map_of_bounded hΩ_sc hΩ_bdd
    obtain ⟨_, _, _, _, _, _, ⟨e_cb, _⟩, ⟨e_bd, _⟩⟩ :=
      caratheodoryExtension_homeomorph_package hΩ_sc.1.1 hΩ_bdd hΩ_simple hf₀_holo hf₀_bij
    exact ⟨⟨e_bd⟩, ⟨e_cb⟩⟩
  refine ⟨hfwd, fun hΩ_reg hΩ_bdd hJ => jordanBoundary_region_converse hΩ_reg hΩ_bdd hJ,
    fun hΩ_reg hΩ_bdd => ⟨fun ⟨hsc, hsimp⟩ => (hfwd hsc hΩ_bdd hsimp).1,
      fun hJ => jordanBoundary_region_converse hΩ_reg hΩ_bdd hJ⟩⟩

/-- Any continuous bijection `G : closure Ω → closedBall (0 : ℂ) 1` that is holomorphic on `Ω`
(where `Ω` is a bounded simply connected region with simple boundary points) automatically maps `Ω`
bijectively onto `ball 0 1`, maps `frontier Ω` bijectively onto `sphere 0 1`, and factors on
`closure Ω` as `diskAut α c ∘ caratheodoryExtension f₀ Ω` for any reference Riemann map `f₀`. -/
theorem closure_bijOn_closedBall_factorization {Ω : Set ℂ}
    (hΩ_sc : RudinRCA.Chapter10.BookSimplyConnected Ω)
    (hΩ_bdd : Bornology.IsBounded Ω)
    (hΩ_simple : ∀ β ∈ frontier Ω, IsSimpleBoundaryPoint Ω β)
    {f₀ : ℂ → ℂ} (hf₀_holo : RudinRCA.Chapter10.HolomorphicOn f₀ Ω)
    (hf₀_bij : BijOn f₀ Ω (ball (0 : ℂ) 1))
    {G : ℂ → ℂ} (hG_cont : ContinuousOn G (closure Ω))
    (hG_holo : RudinRCA.Chapter10.HolomorphicOn G Ω)
    (hG_bij_cb : BijOn G (closure Ω) (closedBall (0 : ℂ) 1)) :
    BijOn G Ω (ball (0 : ℂ) 1) ∧
    BijOn G (frontier Ω) (sphere (0 : ℂ) 1) ∧
    ∃ α ∈ ball (0 : ℂ) 1, ∃ c : ℂ, ‖c‖ = 1 ∧
      Set.EqOn G (diskAut α c ∘ caratheodoryExtension f₀ Ω) (closure Ω) := by
  have hΩ_open : IsOpen Ω := hΩ_sc.1.1
  let F₀ : ℂ → ℂ := caratheodoryExtension f₀ Ω
  obtain ⟨hF₀_eq, hF₀_cont, _, hF₀_bij_cb, hF₀_bij_fr, _, ⟨e₀, he₀⟩, _⟩ :=
    caratheodoryExtension_homeomorph_package hΩ_open hΩ_bdd hΩ_simple hf₀_holo hf₀_bij
  have : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp hΩ_bdd.isCompact_closure
  let eG : closure Ω ≃ₜ closedBall (0 : ℂ) 1 :=
    Continuous.homeoOfEquivCompactToT2 (f := hG_bij_cb.equiv)
      (hG_cont.domRestrict.codRestrict fun z => hG_bij_cb.mapsTo z.2)
  have heG : ∀ z : closure Ω, (eG z : ℂ) = G z.1 := fun _ => rfl
  let H : closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1 := e₀.symm.trans eG
  obtain ⟨hH_sph, hH_ball⟩ := homeomorph_closedBall_preserves_sphere_and_ball H
  obtain ⟨hHinv_sph, hHinv_ball⟩ := homeomorph_closedBall_preserves_sphere_and_ball H.symm
  have hHG : ∀ z : closure Ω, (H (e₀ z) : ℂ) = G z.1 := fun z => by
    simp [H, heG]
  have hG_maps_ball : MapsTo G Ω (ball (0 : ℂ) 1) := by
    intro z hz
    have hz_cl : z ∈ closure Ω := subset_closure hz
    have hF₀_z : F₀ z ∈ ball (0 : ℂ) 1 := by dsimp [F₀]; rw [hF₀_eq hz]; exact hf₀_bij.mapsTo hz
    have he₀_eq : e₀ ⟨z, hz_cl⟩ = ⟨F₀ z, ball_subset_closedBall hF₀_z⟩ :=
      Subtype.ext (he₀ ⟨z, hz_cl⟩)
    have := hH_ball (F₀ z) hF₀_z
    rwa [← he₀_eq, hHG ⟨z, hz_cl⟩] at this
  have hG_maps_sph : MapsTo G (frontier Ω) (sphere (0 : ℂ) 1) := by
    intro β hβ
    have hβ_cl : β ∈ closure Ω := frontier_subset_closure hβ
    have hF₀_β : F₀ β ∈ sphere (0 : ℂ) 1 := hF₀_bij_fr.mapsTo hβ
    have he₀_eq : e₀ ⟨β, hβ_cl⟩ = ⟨F₀ β, sphere_subset_closedBall hF₀_β⟩ :=
      Subtype.ext (he₀ ⟨β, hβ_cl⟩)
    have := hH_sph (F₀ β) hF₀_β
    rwa [← he₀_eq, hHG ⟨β, hβ_cl⟩] at this
  have hcl_decomp : ∀ z ∈ closure Ω, z ∈ Ω ∨ z ∈ frontier Ω := by
    intro z hz
    by_cases h : z ∈ Ω
    · exact Or.inl h
    · exact Or.inr (mem_frontier_of_mem_closure_not_mem hz h)
  have hG_bij_ball : BijOn G Ω (ball (0 : ℂ) 1) := by
    refine ⟨hG_maps_ball, hG_bij_cb.injOn.mono subset_closure, fun w hw => ?_⟩
    obtain ⟨z, hz_cl, hGz⟩ := hG_bij_cb.surjOn (ball_subset_closedBall hw)
    rcases hcl_decomp z hz_cl with hz_Ω | hz_fr
    · exact ⟨z, hz_Ω, hGz⟩
    · exfalso
      have h1 : ‖w‖ = 1 := by rw [← hGz]; simpa using hG_maps_sph hz_fr
      have h2 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
      linarith
  have hG_bij_sph : BijOn G (frontier Ω) (sphere (0 : ℂ) 1) := by
    refine ⟨hG_maps_sph, hG_bij_cb.injOn.mono frontier_subset_closure, fun w hw => ?_⟩
    obtain ⟨z, hz_cl, hGz⟩ := hG_bij_cb.surjOn (sphere_subset_closedBall hw)
    rcases hcl_decomp z hz_cl with hz_Ω | hz_fr
    · exfalso
      have h1 : ‖w‖ < 1 := by rw [← hGz]; exact mem_ball_zero_iff.mp (hG_maps_ball hz_Ω)
      have h2 : ‖w‖ = 1 := by simpa using hw
      linarith
    · exact ⟨z, hz_fr, hGz⟩
  obtain ⟨ψ₀, hψ₀_holo, hψ₀_bij, hψ₀_left, hψ₀_right⟩ :=
    (theorem14_7 hΩ_open hf₀_holo hf₀_bij).2.1
  have hcomp_diff : DifferentiableOn ℂ (G ∘ ψ₀) (ball (0 : ℂ) 1) := by
    intro w hw
    exact ((hG_holo (ψ₀ w) (hψ₀_bij.mapsTo hw)).comp w (hψ₀_holo w hw)).differentiableWithinAt
  have hcomp_bij : BijOn (G ∘ ψ₀) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    hG_bij_ball.comp hψ₀_bij
  obtain ⟨α, hα, c, hc, hcomp_aut⟩ :=
    RudinRCA.Chapter12.theorem12_6.1.mp ⟨hcomp_diff, hcomp_bij⟩
  obtain ⟨hAut_cont, _, _, _, _, _⟩ := diskAut_props hα hc
  have heq_Ω : Set.EqOn G (diskAut α c ∘ F₀) Ω := by
    intro z hz
    have h1 := hcomp_aut (f₀ z) (hf₀_bij.mapsTo hz)
    dsimp [Function.comp_def] at h1 ⊢
    rw [hψ₀_left z hz] at h1
    dsimp [F₀]
    rw [h1, hF₀_eq hz]
    rfl
  have heq_cl : Set.EqOn G (diskAut α c ∘ F₀) (closure Ω) :=
    eqOn_of_continuousOn_closure_eqOn hG_cont (hAut_cont.comp hF₀_cont hF₀_bij_cb.mapsTo) heq_Ω
  exact ⟨hG_bij_ball, hG_bij_sph, α, hα, c, hc, heq_cl⟩

/-- Positive (conformal / counterclockwise) cyclic order of three boundary points
`β₁, β₂, β₃ ∈ frontier Ω` of a planar region `Ω ⊆ ℂ`: `β₁, β₂, β₃` lie on `frontier Ω` and are
mapped to a positively cyclically ordered triple on `sphere (0 : ℂ) 1` by some (equivalently, every)
closure homeomorphism `closure Ω → closedBall (0 : ℂ) 1` holomorphic on `Ω`. -/
def BoundaryPosCyclic (Ω : Set ℂ) (β₁ β₂ β₃ : ℂ) : Prop :=
  β₁ ∈ frontier Ω ∧ β₂ ∈ frontier Ω ∧ β₃ ∈ frontier Ω ∧
  ∃ F : ℂ → ℂ, ContinuousOn F (closure Ω) ∧ RudinRCA.Chapter10.HolomorphicOn F Ω ∧
    BijOn F (closure Ω) (closedBall (0 : ℂ) 1) ∧
    UnitCirclePosCyclic (F β₁) (F β₂) (F β₃)

/-- Conformal invariance and exclusive dichotomy of `BoundaryPosCyclic` on `frontier Ω`. -/
theorem boundaryPosCyclic_invariance_and_dichotomy {Ω : Set ℂ}
    (hΩ_sc : RudinRCA.Chapter10.BookSimplyConnected Ω)
    (hΩ_bdd : Bornology.IsBounded Ω)
    (hΩ_simple : ∀ β ∈ frontier Ω, IsSimpleBoundaryPoint Ω β) :
    (∀ {β₁ β₂ β₃ : ℂ} {F : ℂ → ℂ},
      β₁ ∈ frontier Ω → β₂ ∈ frontier Ω → β₃ ∈ frontier Ω →
      ContinuousOn F (closure Ω) → RudinRCA.Chapter10.HolomorphicOn F Ω →
      BijOn F (closure Ω) (closedBall (0 : ℂ) 1) →
      (BoundaryPosCyclic Ω β₁ β₂ β₃ ↔ UnitCirclePosCyclic (F β₁) (F β₂) (F β₃))) ∧
    (∀ {β₁ β₂ β₃ : ℂ},
      β₁ ∈ frontier Ω → β₂ ∈ frontier Ω → β₃ ∈ frontier Ω →
      β₁ ≠ β₂ → β₂ ≠ β₃ → β₁ ≠ β₃ →
      (BoundaryPosCyclic Ω β₁ β₂ β₃ ↔ ¬ BoundaryPosCyclic Ω β₁ β₃ β₂)) := by
  obtain ⟨f₀, hf₀_holo, hf₀_bij⟩ := exists_riemann_map_of_bounded hΩ_sc hΩ_bdd
  have hinv : ∀ {β₁ β₂ β₃ : ℂ} {F : ℂ → ℂ},
      β₁ ∈ frontier Ω → β₂ ∈ frontier Ω → β₃ ∈ frontier Ω →
      ContinuousOn F (closure Ω) → RudinRCA.Chapter10.HolomorphicOn F Ω →
      BijOn F (closure Ω) (closedBall (0 : ℂ) 1) →
      (BoundaryPosCyclic Ω β₁ β₂ β₃ ↔ UnitCirclePosCyclic (F β₁) (F β₂) (F β₃)) := by
    intro β₁ β₂ β₃ F hβ₁ hβ₂ hβ₃ hF_cont hF_holo hF_bij
    constructor
    · rintro ⟨_, _, _, G, hG_cont, hG_holo, hG_bij, hG_cyc⟩
      obtain ⟨_, _, α₁, hα₁, c₁, hc₁, hF_eq⟩ :=
        closure_bijOn_closedBall_factorization hΩ_sc hΩ_bdd hΩ_simple hf₀_holo hf₀_bij
          hF_cont hF_holo hF_bij
      obtain ⟨_, _, α₂, hα₂, c₂, hc₂, hG_eq⟩ :=
        closure_bijOn_closedBall_factorization hΩ_sc hΩ_bdd hΩ_simple hf₀_holo hf₀_bij
          hG_cont hG_holo hG_bij
      obtain ⟨_, _, _, _, _, hAut₂_inv⟩ := diskAut_props hα₂ hc₂
      obtain ⟨hinv₂_cont, hinv₂_diff, hinv₂_bij⟩ := diskAutInv_props hα₂ hc₂
      obtain ⟨_, _, _, _, hF₀_bij_fr, _, _, _⟩ :=
        caratheodoryExtension_homeomorph_package hΩ_sc.1.1 hΩ_bdd hΩ_simple hf₀_holo hf₀_bij
      let inv₂ : ℂ → ℂ := fun ζ => RudinRCA.Chapter12.phi (-α₂) (c₂⁻¹ * ζ)
      obtain ⟨α₃, hα₃, c₃, hc₃, hinv₂_eq⟩ :=
        RudinRCA.Chapter12.theorem12_6.1.mp ⟨hinv₂_diff, hinv₂_bij⟩
      obtain ⟨hAut₃_cont, _, _, _, _, _⟩ := diskAut_props hα₃ hc₃
      have hinv₂_cb : Set.EqOn inv₂ (diskAut α₃ c₃) (closedBall (0 : ℂ) 1) :=
        eqOn_closedBall_of_eqOn_ball hinv₂_cont hAut₃_cont hinv₂_eq
      let F₀ : ℂ → ℂ := caratheodoryExtension f₀ Ω
      have hF₀_cyc : UnitCirclePosCyclic (F₀ β₁) (F₀ β₂) (F₀ β₃) := by
        have h1 : diskAut α₃ c₃ (G β₁) = F₀ β₁ := by
          rw [← hinv₂_cb (hG_bij.mapsTo (frontier_subset_closure hβ₁)),
            hG_eq (frontier_subset_closure hβ₁)]
          exact (hAut₂_inv (F₀ β₁) (sphere_subset_closedBall (hF₀_bij_fr.mapsTo hβ₁))).1
        have h2 : diskAut α₃ c₃ (G β₂) = F₀ β₂ := by
          rw [← hinv₂_cb (hG_bij.mapsTo (frontier_subset_closure hβ₂)),
            hG_eq (frontier_subset_closure hβ₂)]
          exact (hAut₂_inv (F₀ β₂) (sphere_subset_closedBall (hF₀_bij_fr.mapsTo hβ₂))).1
        have h3 : diskAut α₃ c₃ (G β₃) = F₀ β₃ := by
          rw [← hinv₂_cb (hG_bij.mapsTo (frontier_subset_closure hβ₃)),
            hG_eq (frontier_subset_closure hβ₃)]
          exact (hAut₂_inv (F₀ β₃) (sphere_subset_closedBall (hF₀_bij_fr.mapsTo hβ₃))).1
        rw [← h1, ← h2, ← h3]
        exact diskAut_preserves_posCyclic hα₃ hc₃ hG_cyc
      rw [hF_eq (frontier_subset_closure hβ₁), hF_eq (frontier_subset_closure hβ₂),
        hF_eq (frontier_subset_closure hβ₃)]
      exact diskAut_preserves_posCyclic hα₁ hc₁ hF₀_cyc
    · intro hcyc
      exact ⟨hβ₁, hβ₂, hβ₃, F, hF_cont, hF_holo, hF_bij, hcyc⟩
  refine ⟨hinv, fun {β₁ β₂ β₃} hβ₁ hβ₂ hβ₃ h12 h23 h13 => ?_⟩
  let F₀ : ℂ → ℂ := caratheodoryExtension f₀ Ω
  obtain ⟨hF₀_eq, hF₀_cont, _, hF₀_bij_cb, hF₀_bij_fr, _, _, _⟩ :=
    caratheodoryExtension_homeomorph_package hΩ_sc.1.1 hΩ_bdd hΩ_simple hf₀_holo hf₀_bij
  have hF₀_holo : RudinRCA.Chapter10.HolomorphicOn F₀ Ω :=
    fun z hz => (hf₀_holo z hz).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hΩ_sc.1.1.mem_nhds hz) fun w hw => hF₀_eq hw)
  rw [hinv hβ₁ hβ₂ hβ₃ hF₀_cont hF₀_holo hF₀_bij_cb,
    hinv hβ₁ hβ₃ hβ₂ hF₀_cont hF₀_holo hF₀_bij_cb]
  exact unitCirclePosCyclic_dichotomy
    (hF₀_bij_fr.mapsTo hβ₁) (hF₀_bij_fr.mapsTo hβ₂) (hF₀_bij_fr.mapsTo hβ₃)
    (fun h => h12 (hF₀_bij_fr.injOn hβ₁ hβ₂ h))
    (fun h => h23 (hF₀_bij_fr.injOn hβ₂ hβ₃ h))
    (fun h => h13 (hF₀_bij_fr.injOn hβ₁ hβ₃ h))

/-- **14.20(b) (Unique three-point boundary normalization in compatible cyclic order,
RCA p. 291):**
Let `Ω` be a bounded simply connected region in `ℂ` whose boundary points are all simple, let
`β₁, β₂, β₃ ∈ frontier Ω` be three distinct boundary points, and let `w₁, w₂, w₃ ∈ sphere 0 1` be
three distinct points on the unit circle.
1. If `(β₁, β₂, β₃)` and `(w₁, w₂, w₃)` have compatible cyclic order
   (`BoundaryPosCyclic Ω β₁ β₂ β₃ ↔ UnitCirclePosCyclic w₁ w₂ w₃`), there exists a unique closure
   homeomorphism `F : closure Ω → closedBall 0 1` holomorphic in `Ω` satisfying
   `F β₁ = w₁`, `F β₂ = w₂`, and `F β₃ = w₃` (moreover `F` maps `Ω` bijectively onto `ball 0 1`
   and `frontier Ω` bijectively onto `sphere 0 1`).
2. Conversely, the existence of such a map implies compatible cyclic order
   (`BoundaryPosCyclic Ω β₁ β₂ β₃ ↔ UnitCirclePosCyclic w₁ w₂ w₃`). -/
theorem theorem14_20_part_b {Ω : Set ℂ}
    (hΩ_sc : RudinRCA.Chapter10.BookSimplyConnected Ω)
    (hΩ_bdd : Bornology.IsBounded Ω)
    (hΩ_simple : ∀ β ∈ frontier Ω, IsSimpleBoundaryPoint Ω β)
    {β₁ β₂ β₃ w₁ w₂ w₃ : ℂ}
    (hβ₁ : β₁ ∈ frontier Ω) (hβ₂ : β₂ ∈ frontier Ω) (hβ₃ : β₃ ∈ frontier Ω)
    (hβ12 : β₁ ≠ β₂) (hβ23 : β₂ ≠ β₃) (hβ13 : β₁ ≠ β₃)
    (hw₁ : w₁ ∈ sphere (0 : ℂ) 1) (hw₂ : w₂ ∈ sphere (0 : ℂ) 1) (hw₃ : w₃ ∈ sphere (0 : ℂ) 1)
    (hw12 : w₁ ≠ w₂) (hw23 : w₂ ≠ w₃) (hw13 : w₁ ≠ w₃) :
    ((BoundaryPosCyclic Ω β₁ β₂ β₃ ↔ UnitCirclePosCyclic w₁ w₂ w₃) →
      ∃ F : ℂ → ℂ,
        ContinuousOn F (closure Ω) ∧
        RudinRCA.Chapter10.HolomorphicOn F Ω ∧
        BijOn F Ω (ball (0 : ℂ) 1) ∧
        BijOn F (frontier Ω) (sphere (0 : ℂ) 1) ∧
        BijOn F (closure Ω) (closedBall (0 : ℂ) 1) ∧
        (∃ e : closure Ω ≃ₜ closedBall (0 : ℂ) 1, ∀ z : closure Ω, (e z : ℂ) = F z.1) ∧
        F β₁ = w₁ ∧ F β₂ = w₂ ∧ F β₃ = w₃ ∧
        ∀ G : ℂ → ℂ,
          ContinuousOn G (closure Ω) →
          RudinRCA.Chapter10.HolomorphicOn G Ω →
          BijOn G (closure Ω) (closedBall (0 : ℂ) 1) →
          G β₁ = w₁ → G β₂ = w₂ → G β₃ = w₃ →
          Set.EqOn G F (closure Ω)) ∧
    ((∃ F : ℂ → ℂ,
        ContinuousOn F (closure Ω) ∧
        RudinRCA.Chapter10.HolomorphicOn F Ω ∧
        BijOn F (closure Ω) (closedBall (0 : ℂ) 1) ∧
        F β₁ = w₁ ∧ F β₂ = w₂ ∧ F β₃ = w₃) →
      (BoundaryPosCyclic Ω β₁ β₂ β₃ ↔ UnitCirclePosCyclic w₁ w₂ w₃)) := by
  obtain ⟨hinv, hdich_β⟩ := boundaryPosCyclic_invariance_and_dichotomy hΩ_sc hΩ_bdd hΩ_simple
  refine ⟨fun hcompat => ?_, ?_⟩
  · obtain ⟨f₀, hf₀_holo, hf₀_bij⟩ := exists_riemann_map_of_bounded hΩ_sc hΩ_bdd
    let F₀ : ℂ → ℂ := caratheodoryExtension f₀ Ω
    obtain ⟨hF₀_eq, hF₀_cont, _, hF₀_bij_cb, hF₀_bij_fr, _, ⟨e₀, he₀⟩, _⟩ :=
      caratheodoryExtension_homeomorph_package hΩ_sc.1.1 hΩ_bdd hΩ_simple hf₀_holo hf₀_bij
    have hF₀_holo : RudinRCA.Chapter10.HolomorphicOn F₀ Ω :=
      fun z hz => (hf₀_holo z hz).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hΩ_sc.1.1.mem_nhds hz) fun w hw => hF₀_eq hw)
    have hz₁_s : F₀ β₁ ∈ sphere (0 : ℂ) 1 := hF₀_bij_fr.mapsTo hβ₁
    have hz₂_s : F₀ β₂ ∈ sphere (0 : ℂ) 1 := hF₀_bij_fr.mapsTo hβ₂
    have hz₃_s : F₀ β₃ ∈ sphere (0 : ℂ) 1 := hF₀_bij_fr.mapsTo hβ₃
    obtain ⟨α, hα, c, hc, hv₁, hv₂, hv₃, huniq_aut⟩ :
        ∃ α ∈ ball (0 : ℂ) 1, ∃ c : ℂ, ‖c‖ = 1 ∧
          diskAut α c (F₀ β₁) = w₁ ∧ diskAut α c (F₀ β₂) = w₂ ∧ diskAut α c (F₀ β₃) = w₃ ∧
          ∀ α' ∈ ball (0 : ℂ) 1, ∀ c' : ℂ, ‖c'‖ = 1 →
            diskAut α' c' (F₀ β₁) = w₁ → diskAut α' c' (F₀ β₂) = w₂ →
            diskAut α' c' (F₀ β₃) = w₃ → α' = α ∧ c' = c := by
      by_cases hpos : UnitCirclePosCyclic w₁ w₂ w₃
      · have hβ_pos : BoundaryPosCyclic Ω β₁ β₂ β₃ := hcompat.mpr hpos
        have hF₀_pos : UnitCirclePosCyclic (F₀ β₁) (F₀ β₂) (F₀ β₃) :=
          (hinv hβ₁ hβ₂ hβ₃ hF₀_cont hF₀_holo hF₀_bij_cb).mp hβ_pos
        exact exists_unique_diskAut_three_points hF₀_pos hpos
      · have hw_swap : UnitCirclePosCyclic w₁ w₃ w₂ := by
          by_contra hnot
          exact hpos ((unitCirclePosCyclic_dichotomy hw₁ hw₂ hw₃ hw12 hw23 hw13).mpr hnot)
        have hnot_β : ¬ BoundaryPosCyclic Ω β₁ β₂ β₃ := fun hb => hpos (hcompat.mp hb)
        have hβ_swap : BoundaryPosCyclic Ω β₁ β₃ β₂ := by
          by_contra hnot
          exact hnot_β ((hdich_β hβ₁ hβ₂ hβ₃ hβ12 hβ23 hβ13).mpr hnot)
        have hF₀_swap : UnitCirclePosCyclic (F₀ β₁) (F₀ β₃) (F₀ β₂) :=
          (hinv hβ₁ hβ₃ hβ₂ hF₀_cont hF₀_holo hF₀_bij_cb).mp hβ_swap
        obtain ⟨α, hα, c, hc, hv₁, hv₃, hv₂, hu⟩ :=
          exists_unique_diskAut_three_points hF₀_swap hw_swap
        exact ⟨α, hα, c, hc, hv₁, hv₂, hv₃,
          fun α' hα' c' hc' h₁' h₂' h₃' => hu α' hα' c' hc' h₁' h₃' h₂'⟩
    obtain ⟨hAut_cont, hAut_diff, hAut_ball, hAut_sph, hAut_cb, _⟩ := diskAut_props hα hc
    let F : ℂ → ℂ := diskAut α c ∘ F₀
    have hF_cont : ContinuousOn F (closure Ω) := hAut_cont.comp hF₀_cont hF₀_bij_cb.mapsTo
    have hF₀_bij_Ω : BijOn F₀ Ω (ball (0 : ℂ) 1) := by
      refine ⟨fun z hz => by dsimp [F₀]; rw [hF₀_eq hz]; exact hf₀_bij.mapsTo hz,
        fun z₁ hz₁ z₂ hz₂ h => hf₀_bij.injOn hz₁ hz₂
          (by dsimp [F₀] at h; rwa [← hF₀_eq hz₁, ← hF₀_eq hz₂]),
        fun w hw => ?_⟩
      obtain ⟨z, hz, hzw⟩ := hf₀_bij.surjOn hw
      exact ⟨z, hz, by dsimp [F₀]; rw [hF₀_eq hz, hzw]⟩
    have hF_holo : RudinRCA.Chapter10.HolomorphicOn F Ω := by
      intro z hz
      exact (hAut_diff (F₀ z) (hF₀_bij_Ω.mapsTo hz)).differentiableAt
        (isOpen_ball.mem_nhds (hF₀_bij_Ω.mapsTo hz)) |>.comp z (hF₀_holo z hz)
    have hF_bij_ball : BijOn F Ω (ball (0 : ℂ) 1) := hAut_ball.comp hF₀_bij_Ω
    have hF_bij_sph : BijOn F (frontier Ω) (sphere (0 : ℂ) 1) := hAut_sph.comp hF₀_bij_fr
    have hF_bij_cb : BijOn F (closure Ω) (closedBall (0 : ℂ) 1) := hAut_cb.comp hF₀_bij_cb
    have : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp hΩ_bdd.isCompact_closure
    let eF : closure Ω ≃ₜ closedBall (0 : ℂ) 1 :=
      Continuous.homeoOfEquivCompactToT2 (f := hF_bij_cb.equiv)
        (hF_cont.domRestrict.codRestrict fun z => hF_bij_cb.mapsTo z.2)
    refine ⟨F, hF_cont, hF_holo, hF_bij_ball, hF_bij_sph, hF_bij_cb, ⟨eF, fun _ => rfl⟩,
      hv₁, hv₂, hv₃, ?_⟩
    intro G hG_cont hG_holo hG_bij_cb hG₁ hG₂ hG₃
    obtain ⟨_, _, α', hα', c', hc', hG_eq⟩ :=
      closure_bijOn_closedBall_factorization hΩ_sc hΩ_bdd hΩ_simple hf₀_holo hf₀_bij
        hG_cont hG_holo hG_bij_cb
    have ha₁ : diskAut α' c' (F₀ β₁) = w₁ := by
      rw [← hG₁]; exact (hG_eq (frontier_subset_closure hβ₁)).symm
    have ha₂ : diskAut α' c' (F₀ β₂) = w₂ := by
      rw [← hG₂]; exact (hG_eq (frontier_subset_closure hβ₂)).symm
    have ha₃ : diskAut α' c' (F₀ β₃) = w₃ := by
      rw [← hG₃]; exact (hG_eq (frontier_subset_closure hβ₃)).symm
    obtain ⟨rfl, rfl⟩ := huniq_aut α' hα' c' hc' ha₁ ha₂ ha₃
    exact hG_eq
  · rintro ⟨F, hF_cont, hF_holo, hF_bij, rfl, rfl, rfl⟩
    exact hinv hβ₁ hβ₂ hβ₃ hF_cont hF_holo hF_bij

/-- Target region `T ⊆ RiemannSphere` Möbius-equivalent to the open unit disc
`((↑) : ℂ → RiemannSphere) '' ball (0 : ℂ) 1` (covering both `U` itself and every open half-plane
`H ⊆ ℂ` via `openHalfPlane_moebius_bij`). -/
def IsMoebiusDiscTarget (T : Set RiemannSphere) : Prop :=
  ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
    BijOn (moebiusMap a b c d) T (((↑) : ℂ → RiemannSphere) '' ball (0 : ℂ) 1)

/-- Positive cyclic order on `frontier Ω` for a spherical region `Ω ⊆ RiemannSphere`:
`β₁, β₂, β₃ ∈ frontier Ω` are mapped to a positively cyclically ordered triple on `sphere 0 1` by
some (equivalently, every) closure homeomorphism `closure Ω → closure (((↑) '' ball 0 1))` that is
spherical-holomorphic on `Ω`. -/
def SphericalBoundaryPosCyclic (Ω : Set RiemannSphere) (β₁ β₂ β₃ : RiemannSphere) : Prop :=
  β₁ ∈ frontier Ω ∧ β₂ ∈ frontier Ω ∧ β₃ ∈ frontier Ω ∧
  ∃ F : RiemannSphere → RiemannSphere,
    ContinuousOn F (closure Ω) ∧ SphericalHolomorphicOn F Ω ∧
    BijOn F (closure Ω) (closure (((↑) : ℂ → RiemannSphere) '' ball (0 : ℂ) 1)) ∧
    UnitCirclePosCyclic (sphereFinitePart (F β₁)) (sphereFinitePart (F β₂))
      (sphereFinitePart (F β₃))

theorem isMoebiusDiscTarget_unitDisc :
    IsMoebiusDiscTarget (((↑) : ℂ → RiemannSphere) '' ball (0 : ℂ) 1) := by
  refine ⟨1, 0, 0, 1, by norm_num, ?_⟩
  have hid : moebiusMap 1 0 0 1 = id := funext moebiusMap_id
  rw [hid]
  exact bijOn_id _

theorem isMoebiusDiscTarget_openHalfPlane {H : Set ℂ} (hH : IsOpenHalfPlane H) :
    IsMoebiusDiscTarget (((↑) : ℂ → RiemannSphere) '' H) := by
  obtain ⟨a, b, c, d, hdet, hbij⟩ := openHalfPlane_moebius_bij hH
  have hdet' : d * a - (-b) * (-c) ≠ 0 := by intro h0; apply hdet; linear_combination h0
  refine ⟨d, -b, -c, a, hdet', ?_, (moebiusMap_bijective hdet').1.injOn, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := hbij.surjOn hq
    rw [moebiusMap_inv_left hdet]
    exact hp
  · intro p hp
    exact ⟨moebiusMap a b c d p, hbij.mapsTo hp, moebiusMap_inv_left hdet p⟩

/-- Two continuous maps `F₁, F₂ : RiemannSphere → RiemannSphere` on `closure Ω` that agree on `Ω`
agree on `closure Ω`. -/
theorem eqOn_closure_riemannSphere {Ω : Set RiemannSphere}
    {F₁ F₂ : RiemannSphere → RiemannSphere}
    (h₁ : ContinuousOn F₁ (closure Ω)) (h₂ : ContinuousOn F₂ (closure Ω))
    (heq : Set.EqOn F₁ F₂ Ω) : Set.EqOn F₁ F₂ (closure Ω) := by
  have hsub : Ω ⊆ {p ∈ closure Ω | F₁ p = F₂ p} := fun p hp => ⟨subset_closure hp, heq hp⟩
  have hclosed_eq : IsClosed {p ∈ closure Ω | F₁ p = F₂ p} := by
    let S : Set (closure Ω) := {q : closure Ω | F₁ q.1 = F₂ q.1}
    have hS_closed : IsClosed S :=
      isClosed_eq h₁.domRestrict h₂.domRestrict
    obtain ⟨C, hC_closed, hCS⟩ := isClosed_induced_iff.mp hS_closed
    have heq_set : {p ∈ closure Ω | F₁ p = F₂ p} = closure Ω ∩ C := by
      ext p
      constructor
      · rintro ⟨hp_cl, hp_eq⟩
        have hmemS : (⟨p, hp_cl⟩ : closure Ω) ∈ S := hp_eq
        rw [← hCS] at hmemS
        exact ⟨hp_cl, hmemS⟩
      · rintro ⟨hp_cl, hp_C⟩
        have hmemS : (⟨p, hp_cl⟩ : closure Ω) ∈ S := by rw [← hCS]; exact hp_C
        exact ⟨hp_cl, hmemS⟩
    rw [heq_set]
    exact isClosed_closure.inter hC_closed
  intro p hp
  exact (closure_minimal hsub hclosed_eq hp).2

/-- **14.20(c) (Riemann-sphere & open half-plane Carathéodory extension and three-point
normalization, RCA p. 291):**
Let `Ω ⊆ RiemannSphere` be a simply connected spherical region whose complement has nonempty
interior and whose boundary points are all simple, and let `T ⊆ RiemannSphere` be any Möbius-disc
target (`IsMoebiusDiscTarget T`, which holds in particular for the open unit disc
`((↑) : ℂ → RiemannSphere) '' ball 0 1` and for every open half-plane
`((↑) : ℂ → RiemannSphere) '' H` with `IsOpenHalfPlane H`):
1. Every spherical holomorphic bijection `f : Ω → T` extends uniquely to a continuous map
   `F : closure Ω → closure T` inducing a homeomorphism `closure Ω ≃ₜ closure T` and carrying
   `frontier Ω` bijectively onto `frontier T`.
2. Given three distinct `β₁, β₂, β₃ ∈ frontier Ω` and three distinct `q₁, q₂, q₃ ∈ frontier T` in
   compatible cyclic order (`SphericalBoundaryPosCyclic Ω β₁ β₂ β₃ ↔ SphericalBoundaryPosCyclic T q₁ q₂ q₃`),
   there is a unique closure homeomorphism `F : closure Ω → closure T` spherical-holomorphic in `Ω`
   taking `F β₁ = q₁`, `F β₂ = q₂`, `F β₃ = q₃` (and conversely, existence of such `F` implies
   compatible cyclic order). -/
theorem theorem14_20_part_c :
    IsMoebiusDiscTarget (((↑) : ℂ → RiemannSphere) '' ball (0 : ℂ) 1) ∧
    (∀ {H : Set ℂ}, IsOpenHalfPlane H →
      IsMoebiusDiscTarget (((↑) : ℂ → RiemannSphere) '' H)) ∧
    (∀ {Ω T : Set RiemannSphere},
      SphericalSimplyConnected Ω →
      (interior Ωᶜ).Nonempty →
      (∀ β ∈ frontier Ω, IsSphericalSimpleBoundaryPoint Ω β) →
      IsMoebiusDiscTarget T →
      (∀ {f : RiemannSphere → RiemannSphere},
        SphericalHolomorphicOn f Ω → BijOn f Ω T →
        ∃ F : RiemannSphere → RiemannSphere,
          Set.EqOn F f Ω ∧
          ContinuousOn F (closure Ω) ∧
          SphericalHolomorphicOn F Ω ∧
          BijOn F (closure Ω) (closure T) ∧
          BijOn F (frontier Ω) (frontier T) ∧
          (∃ e : closure Ω ≃ₜ closure T, ∀ p : closure Ω, (e p : RiemannSphere) = F p.1) ∧
          ∀ G : RiemannSphere → RiemannSphere,
            ContinuousOn G (closure Ω) → Set.EqOn G f Ω →
            Set.EqOn G F (closure Ω)) ∧
      (∀ {β₁ β₂ β₃ q₁ q₂ q₃ : RiemannSphere},
        β₁ ∈ frontier Ω → β₂ ∈ frontier Ω → β₃ ∈ frontier Ω →
        β₁ ≠ β₂ → β₂ ≠ β₃ → β₁ ≠ β₃ →
        q₁ ∈ frontier T → q₂ ∈ frontier T → q₃ ∈ frontier T →
        q₁ ≠ q₂ → q₂ ≠ q₃ → q₁ ≠ q₃ →
        ((SphericalBoundaryPosCyclic Ω β₁ β₂ β₃ ↔ SphericalBoundaryPosCyclic T q₁ q₂ q₃) →
          ∃ F : RiemannSphere → RiemannSphere,
            ContinuousOn F (closure Ω) ∧
            SphericalHolomorphicOn F Ω ∧
            BijOn F Ω T ∧
            BijOn F (frontier Ω) (frontier T) ∧
            BijOn F (closure Ω) (closure T) ∧
            (∃ e : closure Ω ≃ₜ closure T, ∀ p : closure Ω, (e p : RiemannSphere) = F p.1) ∧
            F β₁ = q₁ ∧ F β₂ = q₂ ∧ F β₃ = q₃ ∧
            ∀ G : RiemannSphere → RiemannSphere,
              ContinuousOn G (closure Ω) →
              SphericalHolomorphicOn G Ω →
              BijOn G (closure Ω) (closure T) →
              G β₁ = q₁ → G β₂ = q₂ → G β₃ = q₃ →
              Set.EqOn G F (closure Ω)) ∧
        ((∃ F : RiemannSphere → RiemannSphere,
            ContinuousOn F (closure Ω) ∧
            SphericalHolomorphicOn F Ω ∧
            BijOn F (closure Ω) (closure T) ∧
            F β₁ = q₁ ∧ F β₂ = q₂ ∧ F β₃ = q₃) →
          (SphericalBoundaryPosCyclic Ω β₁ β₂ β₃ ↔
            SphericalBoundaryPosCyclic T q₁ q₂ q₃)))) := by
  refine ⟨isMoebiusDiscTarget_unitDisc, fun hH => isMoebiusDiscTarget_openHalfPlane hH, ?_⟩
  intro Ω T hΩ_sc hcompl_int hΩ_simple hT
  obtain ⟨a₁, b₁, c₁, d₁, hdet₁, Ω₀, hΩ₀_reg, hΩ₀_bdd, hΩ₀_sc, hΩ₀_simple, himg_Ω⟩ :=
    spherical_region_moebius_to_bounded_plane hΩ_sc hcompl_int hΩ_simple
  rcases hT with ⟨a₂, b₂, c₂, d₂, hdet₂, hbij_T⟩
  let e₁ := moebiusHomeomorph hdet₁
  let e₂ := moebiusHomeomorph hdet₂
  have hdet₁' : d₁ * a₁ - (-b₁) * (-c₁) ≠ 0 := by intro h0; apply hdet₁; linear_combination h0
  have hdet₂' : d₂ * a₂ - (-b₂) * (-c₂) ≠ 0 := by intro h0; apply hdet₂; linear_combination h0
  let US : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' ball (0 : ℂ) 1
  obtain ⟨hcl_US, hfr_US⟩ := closure_and_frontier_coe_of_isBounded isOpen_ball isBounded_ball
  rw [closure_ball (0 : ℂ) one_ne_zero] at hcl_US
  rw [frontier_ball (0 : ℂ) one_ne_zero] at hfr_US
  obtain ⟨hcl_Ω₀, hfr_Ω₀⟩ := closure_and_frontier_coe_of_isBounded hΩ₀_reg.1 hΩ₀_bdd
  have he₁_cl : e₁ '' closure Ω = ((↑) : ℂ → RiemannSphere) '' closure Ω₀ := by
    rw [e₁.image_closure, show (e₁ : RiemannSphere → RiemannSphere) = moebiusMap a₁ b₁ c₁ d₁ from rfl,
      himg_Ω, hcl_Ω₀]
  have he₁_fr : e₁ '' frontier Ω = ((↑) : ℂ → RiemannSphere) '' frontier Ω₀ := by
    rw [e₁.image_frontier, show (e₁ : RiemannSphere → RiemannSphere) = moebiusMap a₁ b₁ c₁ d₁ from rfl,
      himg_Ω, hfr_Ω₀]
  have he₂_img : e₂ '' T = US := hbij_T.image_eq
  have he₂_cl : e₂ '' closure T = ((↑) : ℂ → RiemannSphere) '' closedBall (0 : ℂ) 1 := by
    rw [e₂.image_closure, he₂_img, hcl_US]
  have he₂_fr : e₂ '' frontier T = ((↑) : ℂ → RiemannSphere) '' sphere (0 : ℂ) 1 := by
    rw [e₂.image_frontier, he₂_img, hfr_US]
  have hret_at : ∀ z : ℂ, ContinuousAt sphereFinitePart (z : RiemannSphere) := by
    intro z
    rw [ContinuousAt, Tendsto]
    have hmap : map sphereFinitePart (𝓝 (z : RiemannSphere)) = 𝓝 z := by
      rw [← OnePoint.isOpenEmbedding_coe.map_nhds_eq z, Filter.map_map]
      simp [Function.comp_def]
    rw [hmap, sphereFinitePart_coe]
  have hret_cont : ContinuousOn sphereFinitePart (Set.range ((↑) : ℂ → RiemannSphere)) := by
    rintro p ⟨z, rfl⟩; exact (hret_at z).continuousWithinAt
  have he₁_cl_maps : MapsTo (sphereFinitePart ∘ e₁) (closure Ω) (closure Ω₀) := by
    intro p hp
    have hp' : e₁ p ∈ ((↑) : ℂ → RiemannSphere) '' closure Ω₀ := by
      rw [← he₁_cl]; exact ⟨p, hp, rfl⟩
    rcases hp' with ⟨z, hz, hzp⟩
    dsimp [Function.comp_def]; rw [← hzp, sphereFinitePart_coe]; exact hz
  have he₁_cl_range : MapsTo e₁ (closure Ω) (Set.range ((↑) : ℂ → RiemannSphere)) := by
    intro p hp
    have hp' : e₁ p ∈ ((↑) : ℂ → RiemannSphere) '' closure Ω₀ := by
      rw [← he₁_cl]; exact ⟨p, hp, rfl⟩
    rcases hp' with ⟨z, _, hzp⟩; exact ⟨z, hzp⟩
  -- Transport bridge: any `G` with `ContinuousOn G (closure Ω)`, `SphericalHolomorphicOn G Ω`,
  -- `BijOn G (closure Ω) (closure T)` induces `G₀ : closure Ω₀ → closedBall 0 1`!
  have hbridge_to_plane : ∀ {G : RiemannSphere → RiemannSphere},
      ContinuousOn G (closure Ω) →
      SphericalHolomorphicOn G Ω →
      BijOn G (closure Ω) (closure T) →
      let G₀ : ℂ → ℂ := fun z => sphereFinitePart (e₂ (G (e₁.symm (z : RiemannSphere))))
      ContinuousOn G₀ (closure Ω₀) ∧
      RudinRCA.Chapter10.HolomorphicOn G₀ Ω₀ ∧
      BijOn G₀ (closure Ω₀) (closedBall (0 : ℂ) 1) ∧
      ∀ p ∈ closure Ω, G p = e₂.symm ((G₀ (sphereFinitePart (e₁ p)) : ℂ) : RiemannSphere) := by
    intro G hG_cont hG_holo hG_bij G₀
    have he₁_symm_cl : MapsTo (fun z : ℂ => e₁.symm (z : RiemannSphere)) (closure Ω₀) (closure Ω) := by
      intro z hz
      have hmem : (z : RiemannSphere) ∈ e₁ '' closure Ω := by rw [he₁_cl]; exact ⟨z, hz, rfl⟩
      rcases hmem with ⟨p, hp, hpz⟩
      dsimp; rw [← hpz, e₁.symm_apply_apply]; exact hp
    have he₂G_range : MapsTo (fun z : ℂ => e₂ (G (e₁.symm (z : RiemannSphere))))
        (closure Ω₀) (Set.range ((↑) : ℂ → RiemannSphere)) := by
      intro z hz
      have hmem : e₂ (G (e₁.symm (z : RiemannSphere))) ∈ e₂ '' closure T :=
        ⟨G (e₁.symm (z : RiemannSphere)), hG_bij.mapsTo (he₁_symm_cl hz), rfl⟩
      rw [he₂_cl] at hmem
      rcases hmem with ⟨w, _, hw⟩; exact ⟨w, hw⟩
    have hG₀_cont : ContinuousOn G₀ (closure Ω₀) := by
      have hc_in : ContinuousOn (fun z : ℂ => e₂ (G (e₁.symm (z : RiemannSphere)))) (closure Ω₀) :=
        e₂.continuous.comp_continuousOn
          (hG_cont.comp (e₁.symm.continuous.comp OnePoint.continuous_coe).continuousOn he₁_symm_cl)
      exact hret_cont.comp hc_in he₂G_range
    have hG₀_holo : RudinRCA.Chapter10.HolomorphicOn G₀ Ω₀ := by
      let S₀ : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' Ω₀
      have hS₀_open : IsOpen S₀ := OnePoint.isOpenEmbedding_coe.isOpenMap _ hΩ₀_reg.1
      have he₁_symm_Ω₀ : MapsTo e₁.symm S₀ Ω := by
        rintro _ ⟨z, hz, rfl⟩
        have hmem : (z : RiemannSphere) ∈ e₁ '' Ω := by
          rw [show (e₁ : RiemannSphere → RiemannSphere) = moebiusMap a₁ b₁ c₁ d₁ from rfl, himg_Ω]
          exact ⟨z, hz, rfl⟩
        rcases hmem with ⟨p, hp, hpz⟩
        rw [← hpz, e₁.symm_apply_apply]; exact hp
      have hcomp_sph : SphericalHolomorphicOn (e₂ ∘ G ∘ e₁.symm) S₀ := by
        have h1 : SphericalHolomorphicOn e₁.symm S₀ :=
          (moebiusMap_sphericalHolomorphicOn hdet₁').mono (subset_univ _)
        have h2 : SphericalHolomorphicOn (G ∘ e₁.symm) S₀ :=
          hG_holo.comp hS₀_open h1 he₁_symm_Ω₀
        have h3 : SphericalHolomorphicOn e₂ Set.univ :=
          moebiusMap_sphericalHolomorphicOn hdet₂
        exact h3.comp hS₀_open h2 (mapsTo_univ _ _)
      have hfin : ∀ z ∈ Ω₀, (e₂ ∘ G ∘ e₁.symm) (z : RiemannSphere) ≠ ∞ := by
        intro z hz hinf
        rcases he₂G_range (subset_closure hz) with ⟨w, hw⟩
        exact OnePoint.coe_ne_infty w (hw.trans hinf)
      exact (sphericalHolomorphicOn_coe_iff hΩ₀_reg.1 hfin).mp hcomp_sph
    have hG₀_bij : BijOn G₀ (closure Ω₀) (closedBall (0 : ℂ) 1) := by
      refine ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ heq => ?_, fun w hw => ?_⟩
      · have hmem : e₂ (G (e₁.symm (z : RiemannSphere))) ∈ e₂ '' closure T :=
          ⟨G (e₁.symm (z : RiemannSphere)), hG_bij.mapsTo (he₁_symm_cl hz), rfl⟩
        rw [he₂_cl] at hmem
        rcases hmem with ⟨w, hw_cb, hw_eq⟩
        dsimp [G₀]; rw [← hw_eq, sphereFinitePart_coe]; exact hw_cb
      · rcases he₂G_range hz₁ with ⟨w₁, hw₁⟩
        rcases he₂G_range hz₂ with ⟨w₂, hw₂⟩
        dsimp at hw₁ hw₂
        have hw12 : w₁ = w₂ := by
          have h1 : G₀ z₁ = w₁ := by dsimp [G₀]; rw [← hw₁, sphereFinitePart_coe]
          have h2 : G₀ z₂ = w₂ := by dsimp [G₀]; rw [← hw₂, sphereFinitePart_coe]
          rw [← h1, ← h2, heq]
        have he₂_eq : e₂ (G (e₁.symm (z₁ : RiemannSphere))) =
            e₂ (G (e₁.symm (z₂ : RiemannSphere))) := by rw [← hw₁, ← hw₂, hw12]
        have hG_eq := e₂.injective he₂_eq
        have he₁_eq := hG_bij.injOn (he₁_symm_cl hz₁) (he₁_symm_cl hz₂) hG_eq
        exact OnePoint.coe_injective (e₁.symm.injective he₁_eq)
      · have hw_in : (w : RiemannSphere) ∈ e₂ '' closure T := by
          rw [he₂_cl]; exact ⟨w, hw, rfl⟩
        rcases hw_in with ⟨q, hq_cl, hqw⟩
        obtain ⟨p, hp_cl, hGp⟩ := hG_bij.surjOn hq_cl
        have hp_e₁ : e₁ p ∈ ((↑) : ℂ → RiemannSphere) '' closure Ω₀ := by
          rw [← he₁_cl]; exact ⟨p, hp_cl, rfl⟩
        rcases hp_e₁ with ⟨z, hz_cl, hzp⟩
        refine ⟨z, hz_cl, ?_⟩
        dsimp [G₀]
        have hsymm : e₁.symm (z : RiemannSphere) = p := by rw [hzp, e₁.symm_apply_apply]
        rw [hsymm, hGp, hqw, sphereFinitePart_coe]
    refine ⟨hG₀_cont, hG₀_holo, hG₀_bij, fun p hp => ?_⟩
    have hp_e₁ : e₁ p ∈ ((↑) : ℂ → RiemannSphere) '' closure Ω₀ := by
      rw [← he₁_cl]; exact ⟨p, hp, rfl⟩
    rcases hp_e₁ with ⟨z, hz_cl, hzp⟩
    rcases he₂G_range hz_cl with ⟨w, hw⟩
    dsimp at hw
    have hsymm : e₁.symm (z : RiemannSphere) = p := by rw [hzp, e₁.symm_apply_apply]
    rw [hsymm] at hw
    dsimp [G₀]
    rw [← hzp, sphereFinitePart_coe, hsymm, ← hw, sphereFinitePart_coe, hw, e₂.symm_apply_apply]
  -- Also characterize `SphericalBoundaryPosCyclic` on `Ω` via `BoundaryPosCyclic Ω₀` and on `T` via `UnitCirclePosCyclic`!
  have hcyc_Ω_iff : ∀ {β₁ β₂ β₃ : RiemannSphere},
      β₁ ∈ frontier Ω → β₂ ∈ frontier Ω → β₃ ∈ frontier Ω →
      (SphericalBoundaryPosCyclic Ω β₁ β₂ β₃ ↔
        BoundaryPosCyclic Ω₀ (sphereFinitePart (e₁ β₁)) (sphereFinitePart (e₁ β₂))
          (sphereFinitePart (e₁ β₃))) := by
    intro β₁ β₂ β₃ hβ₁ hβ₂ hβ₃
    have hβᵢ_fr₀ : ∀ {β : RiemannSphere}, β ∈ frontier Ω → sphereFinitePart (e₁ β) ∈ frontier Ω₀ := by
      intro β hβ
      have hm : e₁ β ∈ ((↑) : ℂ → RiemannSphere) '' frontier Ω₀ := by
        rw [← he₁_fr]; exact ⟨β, hβ, rfl⟩
      rcases hm with ⟨z, hz, hzb⟩
      rw [← hzb, sphereFinitePart_coe]; exact hz
    constructor
    · rintro ⟨_, _, _, F, hF_cont, hF_holo, hF_bij, hF_cyc⟩
      -- Apply `hbridge_to_plane` with `T := US`, `e₂ := id` (`moebiusHomeomorph (1*1 - 0*0 ≠ 0)`)
      have he₁_symm_cl : MapsTo (fun z : ℂ => e₁.symm (z : RiemannSphere)) (closure Ω₀) (closure Ω) := by
        intro z hz
        have hmem : (z : RiemannSphere) ∈ e₁ '' closure Ω := by rw [he₁_cl]; exact ⟨z, hz, rfl⟩
        rcases hmem with ⟨p, hp, hpz⟩
        dsimp; rw [← hpz, e₁.symm_apply_apply]; exact hp
      let F₀ : ℂ → ℂ := fun z => sphereFinitePart (F (e₁.symm (z : RiemannSphere)))
      have hF_range : MapsTo (fun z : ℂ => F (e₁.symm (z : RiemannSphere))) (closure Ω₀)
          (Set.range ((↑) : ℂ → RiemannSphere)) := by
        intro z hz
        have hm := hF_bij.mapsTo (he₁_symm_cl hz)
        rw [hcl_US] at hm; rcases hm with ⟨w, _, hw⟩; exact ⟨w, hw⟩
      have hF₀_cont : ContinuousOn F₀ (closure Ω₀) :=
        hret_cont.comp (hF_cont.comp (e₁.symm.continuous.comp OnePoint.continuous_coe).continuousOn
          he₁_symm_cl) hF_range
      have hF₀_holo : RudinRCA.Chapter10.HolomorphicOn F₀ Ω₀ := by
        let S₀ : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' Ω₀
        have hS₀_open : IsOpen S₀ := OnePoint.isOpenEmbedding_coe.isOpenMap _ hΩ₀_reg.1
        have he₁_symm_Ω₀ : MapsTo e₁.symm S₀ Ω := by
          rintro _ ⟨z, hz, rfl⟩
          have hm : (z : RiemannSphere) ∈ e₁ '' Ω := by
            rw [show (e₁ : RiemannSphere → RiemannSphere) = moebiusMap a₁ b₁ c₁ d₁ from rfl, himg_Ω]
            exact ⟨z, hz, rfl⟩
          rcases hm with ⟨p, hp, hpz⟩; rw [← hpz, e₁.symm_apply_apply]; exact hp
        have hcomp_sph : SphericalHolomorphicOn (F ∘ e₁.symm) S₀ :=
          hF_holo.comp hS₀_open ((moebiusMap_sphericalHolomorphicOn hdet₁').mono (subset_univ _))
            he₁_symm_Ω₀
        have hfin : ∀ z ∈ Ω₀, (F ∘ e₁.symm) (z : RiemannSphere) ≠ ∞ := by
          intro z hz hinf
          rcases hF_range (subset_closure hz) with ⟨w, hw⟩
          exact OnePoint.coe_ne_infty w (hw.trans hinf)
        exact (sphericalHolomorphicOn_coe_iff hΩ₀_reg.1 hfin).mp hcomp_sph
      have hF₀_bij : BijOn F₀ (closure Ω₀) (closedBall (0 : ℂ) 1) := by
        refine ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ heq => ?_, fun w hw => ?_⟩
        · have hm := hF_bij.mapsTo (he₁_symm_cl hz)
          rw [hcl_US] at hm; rcases hm with ⟨w, hw_cb, hw_eq⟩
          dsimp [F₀]; rw [← hw_eq, sphereFinitePart_coe]; exact hw_cb
        · rcases hF_range hz₁ with ⟨w₁, hw₁⟩
          rcases hF_range hz₂ with ⟨w₂, hw₂⟩
          dsimp at hw₁ hw₂
          have hw12 : w₁ = w₂ := by
            have h1 : F₀ z₁ = w₁ := by dsimp [F₀]; rw [← hw₁, sphereFinitePart_coe]
            have h2 : F₀ z₂ = w₂ := by dsimp [F₀]; rw [← hw₂, sphereFinitePart_coe]
            rw [← h1, ← h2, heq]
          have hFeq : F (e₁.symm (z₁ : RiemannSphere)) = F (e₁.symm (z₂ : RiemannSphere)) := by
            rw [← hw₁, ← hw₂, hw12]
          exact OnePoint.coe_injective
            (e₁.symm.injective (hF_bij.injOn (he₁_symm_cl hz₁) (he₁_symm_cl hz₂) hFeq))
        · have hw_cl : (w : RiemannSphere) ∈ closure US := by rw [hcl_US]; exact ⟨w, hw, rfl⟩
          obtain ⟨p, hp_cl, hFp⟩ := hF_bij.surjOn hw_cl
          have hp_e₁ : e₁ p ∈ ((↑) : ℂ → RiemannSphere) '' closure Ω₀ := by
            rw [← he₁_cl]; exact ⟨p, hp_cl, rfl⟩
          rcases hp_e₁ with ⟨z, hz_cl, hzp⟩
          refine ⟨z, hz_cl, ?_⟩
          dsimp [F₀]; rw [hzp, e₁.symm_apply_apply, hFp, sphereFinitePart_coe]
      have hval : ∀ {β : RiemannSphere}, β ∈ frontier Ω → F₀ (sphereFinitePart (e₁ β)) = sphereFinitePart (F β) := by
        intro β hβ
        have hm : e₁ β ∈ ((↑) : ℂ → RiemannSphere) '' frontier Ω₀ := by
          rw [← he₁_fr]; exact ⟨β, hβ, rfl⟩
        rcases hm with ⟨z, _, hzb⟩
        dsimp [F₀]; rw [← hzb, sphereFinitePart_coe, hzb, e₁.symm_apply_apply]
      refine ⟨hβᵢ_fr₀ hβ₁, hβᵢ_fr₀ hβ₂, hβᵢ_fr₀ hβ₃, F₀, hF₀_cont, hF₀_holo, hF₀_bij, ?_⟩
      rwa [hval hβ₁, hval hβ₂, hval hβ₃]
    · rintro ⟨_, _, _, F₀, hF₀_cont, hF₀_holo, hF₀_bij, hF₀_cyc⟩
      let F : RiemannSphere → RiemannSphere :=
        fun p => ((F₀ (sphereFinitePart (e₁ p)) : ℂ) : RiemannSphere)
      have hF_cont : ContinuousOn F (closure Ω) :=
        OnePoint.continuous_coe.comp_continuousOn
          (hF₀_cont.comp (hret_cont.comp e₁.continuous.continuousOn he₁_cl_range) he₁_cl_maps)
      have hF_holo : SphericalHolomorphicOn F Ω := by
        let G_mid : RiemannSphere → RiemannSphere :=
          fun r => ((F₀ (sphereFinitePart r) : ℂ) : RiemannSphere)
        let S₀ : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' Ω₀
        have hfin : ∀ z ∈ Ω₀, G_mid (z : RiemannSphere) ≠ ∞ := fun z _ => OnePoint.coe_ne_infty _
        have hG_mid : SphericalHolomorphicOn G_mid S₀ := by
          refine (sphericalHolomorphicOn_coe_iff hΩ₀_reg.1 hfin).mpr ?_
          simpa [G_mid] using hF₀_holo
        have he₁_maps : MapsTo e₁ Ω S₀ := by
          intro p hp
          dsimp [S₀]
          change moebiusMap a₁ b₁ c₁ d₁ p ∈ _
          rw [← himg_Ω]; exact ⟨p, hp, rfl⟩
        exact hG_mid.comp hΩ_sc.1.1 ((moebiusMap_sphericalHolomorphicOn hdet₁).mono (subset_univ _))
          he₁_maps
      have hF_bij : BijOn F (closure Ω) (closure US) := by
        rw [hcl_US]
        refine ⟨fun p hp => ⟨F₀ (sphereFinitePart (e₁ p)), hF₀_bij.mapsTo (he₁_cl_maps hp), rfl⟩,
          fun p₁ hp₁ p₂ hp₂ heq => ?_, ?_⟩
        · have hF₀_eq := OnePoint.coe_injective heq
          have hfin_eq := hF₀_bij.injOn (he₁_cl_maps hp₁) (he₁_cl_maps hp₂) hF₀_eq
          dsimp [Function.comp_def] at hfin_eq
          rcases he₁_cl_range hp₁ with ⟨z₁, hz₁⟩
          rcases he₁_cl_range hp₂ with ⟨z₂, hz₂⟩
          rw [← hz₁, ← hz₂, sphereFinitePart_coe, sphereFinitePart_coe] at hfin_eq
          exact e₁.injective (by rw [← hz₁, ← hz₂, hfin_eq])
        · rintro _ ⟨w, hw_cb, rfl⟩
          obtain ⟨z, hz_cl, hF₀z⟩ := hF₀_bij.surjOn hw_cb
          have hz_in : (z : RiemannSphere) ∈ e₁ '' closure Ω := by rw [he₁_cl]; exact ⟨z, hz_cl, rfl⟩
          rcases hz_in with ⟨p, hp_cl, hpz⟩
          refine ⟨p, hp_cl, ?_⟩
          dsimp [F]; rw [hpz, sphereFinitePart_coe, hF₀z]
      refine ⟨hβ₁, hβ₂, hβ₃, F, hF_cont, hF_holo, hF_bij, ?_⟩
      simpa [F] using hF₀_cyc
  have hcyc_T_iff : ∀ {q₁ q₂ q₃ : RiemannSphere},
      q₁ ∈ frontier T → q₂ ∈ frontier T → q₃ ∈ frontier T →
      (SphericalBoundaryPosCyclic T q₁ q₂ q₃ ↔
        UnitCirclePosCyclic (sphereFinitePart (e₂ q₁)) (sphereFinitePart (e₂ q₂))
          (sphereFinitePart (e₂ q₃))) := by
    intro q₁ q₂ q₃ hq₁ hq₂ hq₃
    have he₂_bij_cl : BijOn e₂ (closure T) (closure US) := by
      rw [hcl_US]
      refine ⟨fun p hp => by rw [← he₂_cl]; exact ⟨p, hp, rfl⟩, e₂.injective.injOn, fun r hr => ?_⟩
      rw [← he₂_cl] at hr; rcases hr with ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
    have he₂_holo : SphericalHolomorphicOn e₂ T :=
      (moebiusMap_sphericalHolomorphicOn hdet₂).mono (subset_univ _)
    constructor
    · rintro ⟨_, _, _, F, hF_cont, hF_holo, hF_bij, hF_cyc⟩
      -- `G₀(z) := sphereFinitePart (F (e₂.symm ↑z))` is a closure homeomorphism of `closedBall 0 1` holomorphic on `ball 0 1`!
      have he₂_symm_cl : MapsTo (fun z : ℂ => e₂.symm (z : RiemannSphere))
          (closedBall (0 : ℂ) 1) (closure T) := by
        intro z hz
        have hm : (z : RiemannSphere) ∈ e₂ '' closure T := by rw [he₂_cl]; exact ⟨z, hz, rfl⟩
        rcases hm with ⟨p, hp, hpz⟩; dsimp; rw [← hpz, e₂.symm_apply_apply]; exact hp
      let G₀ : ℂ → ℂ := fun z => sphereFinitePart (F (e₂.symm (z : RiemannSphere)))
      have hF_range : MapsTo (fun z : ℂ => F (e₂.symm (z : RiemannSphere)))
          (closedBall (0 : ℂ) 1) (Set.range ((↑) : ℂ → RiemannSphere)) := by
        intro z hz
        have hm := hF_bij.mapsTo (he₂_symm_cl hz)
        rw [hcl_US] at hm; rcases hm with ⟨w, _, hw⟩; exact ⟨w, hw⟩
      have hG₀_cont : ContinuousOn G₀ (closure (ball (0 : ℂ) 1)) := by
        rw [closure_ball (0 : ℂ) one_ne_zero]
        exact hret_cont.comp (hF_cont.comp (e₂.symm.continuous.comp OnePoint.continuous_coe).continuousOn
          he₂_symm_cl) hF_range
      have hG₀_holo : RudinRCA.Chapter10.HolomorphicOn G₀ (ball (0 : ℂ) 1) := by
        have hUS_open : IsOpen US := OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_ball
        have he₂_symm_US : MapsTo e₂.symm US T := by
          rintro _ ⟨z, hz, rfl⟩
          have hm : (z : RiemannSphere) ∈ e₂ '' T := by rw [he₂_img]; exact ⟨z, hz, rfl⟩
          rcases hm with ⟨p, hp, hpz⟩; rw [← hpz, e₂.symm_apply_apply]; exact hp
        have hT_open : IsOpen T := by
          have : T = e₂ ⁻¹' US := by
            ext p; constructor
            · intro hp; rw [← he₂_img]; exact ⟨p, hp, rfl⟩
            · intro hp; rw [← he₂_img] at hp; rcases hp with ⟨q, hq, hqp⟩
              exact e₂.injective hqp ▸ hq
          rw [this]; exact hUS_open.preimage e₂.continuous
        have hcomp_sph : SphericalHolomorphicOn (F ∘ e₂.symm) US :=
          hF_holo.comp hUS_open ((moebiusMap_sphericalHolomorphicOn hdet₂').mono (subset_univ _))
            he₂_symm_US
        have hfin : ∀ z ∈ ball (0 : ℂ) 1, (F ∘ e₂.symm) (z : RiemannSphere) ≠ ∞ := by
          intro z hz hinf
          rcases hF_range (ball_subset_closedBall hz) with ⟨w, hw⟩
          exact OnePoint.coe_ne_infty w (hw.trans hinf)
        exact (sphericalHolomorphicOn_coe_iff isOpen_ball hfin).mp hcomp_sph
      have hG₀_bij : BijOn G₀ (closure (ball (0 : ℂ) 1)) (closedBall (0 : ℂ) 1) := by
        rw [closure_ball (0 : ℂ) one_ne_zero]
        refine ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ heq => ?_, fun w hw => ?_⟩
        · have hm := hF_bij.mapsTo (he₂_symm_cl hz)
          rw [hcl_US] at hm; rcases hm with ⟨w, hw_cb, hw_eq⟩
          dsimp [G₀]; rw [← hw_eq, sphereFinitePart_coe]; exact hw_cb
        · rcases hF_range hz₁ with ⟨w₁, hw₁⟩
          rcases hF_range hz₂ with ⟨w₂, hw₂⟩
          dsimp at hw₁ hw₂
          have hw12 : w₁ = w₂ := by
            have h1 : G₀ z₁ = w₁ := by dsimp [G₀]; rw [← hw₁, sphereFinitePart_coe]
            have h2 : G₀ z₂ = w₂ := by dsimp [G₀]; rw [← hw₂, sphereFinitePart_coe]
            rw [← h1, ← h2, heq]
          have hFeq : F (e₂.symm (z₁ : RiemannSphere)) = F (e₂.symm (z₂ : RiemannSphere)) := by
            rw [← hw₁, ← hw₂, hw12]
          exact OnePoint.coe_injective
            (e₂.symm.injective (hF_bij.injOn (he₂_symm_cl hz₁) (he₂_symm_cl hz₂) hFeq))
        · have hw_cl : (w : RiemannSphere) ∈ closure US := by rw [hcl_US]; exact ⟨w, hw, rfl⟩
          obtain ⟨p, hp_cl, hFp⟩ := hF_bij.surjOn hw_cl
          have hp_e₂ : e₂ p ∈ ((↑) : ℂ → RiemannSphere) '' closedBall (0 : ℂ) 1 := by
            rw [← he₂_cl]; exact ⟨p, hp_cl, rfl⟩
          rcases hp_e₂ with ⟨z, hz_cb, hzp⟩
          refine ⟨z, hz_cb, ?_⟩
          dsimp [G₀]; rw [hzp, e₂.symm_apply_apply, hFp, sphereFinitePart_coe]
      obtain ⟨hU_sc, hU_simple⟩ := unitDisc_all_simple
      obtain ⟨_, _, α, hα, c, hc, hG₀_aut⟩ :=
        closure_bijOn_closedBall_factorization hU_sc isBounded_ball hU_simple
          (fun _ _ => differentiableAt_id) (bijOn_id _) hG₀_cont hG₀_holo hG₀_bij
      have hF₀_id : Set.EqOn (caratheodoryExtension id (ball (0 : ℂ) 1)) id
          (closure (ball (0 : ℂ) 1)) := by
        obtain ⟨hEq, hCont, _, _, _, _, _, _⟩ :=
          caratheodoryExtension_homeomorph_package isOpen_ball isBounded_ball hU_simple
            (fun _ _ => differentiableAt_id) (bijOn_id _)
        exact eqOn_of_continuousOn_closure_eqOn hCont continuousOn_id hEq
      obtain ⟨_, _, _, _, _, hAut_inv⟩ := diskAut_props hα hc
      obtain ⟨hinv_cont, hinv_diff, hinv_bij⟩ := diskAutInv_props hα hc
      obtain ⟨α', hα', c', hc', hinv_eq⟩ :=
        RudinRCA.Chapter12.theorem12_6.1.mp ⟨hinv_diff, hinv_bij⟩
      obtain ⟨hAut'_cont, _, _, _, _, _⟩ := diskAut_props hα' hc'
      have hinv_cb : Set.EqOn (fun ζ => RudinRCA.Chapter12.phi (-α) (c⁻¹ * ζ))
          (diskAut α' c') (closedBall (0 : ℂ) 1) :=
        eqOn_closedBall_of_eqOn_ball hinv_cont hAut'_cont hinv_eq
      have hval : ∀ {q : RiemannSphere}, q ∈ frontier T →
          diskAut α' c' (sphereFinitePart (F q)) = sphereFinitePart (e₂ q) := by
        intro q hq
        have hm : e₂ q ∈ ((↑) : ℂ → RiemannSphere) '' sphere (0 : ℂ) 1 := by
          rw [← he₂_fr]; exact ⟨q, hq, rfl⟩
        rcases hm with ⟨z, hz_sph, hzq⟩
        have hz_cb : z ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hz_sph
        have hz_cl : z ∈ closure (ball (0 : ℂ) 1) := by
          rwa [closure_ball (0 : ℂ) one_ne_zero]
        have hG₀_z : G₀ z = sphereFinitePart (F q) := by
          dsimp [G₀]; rw [hzq, e₂.symm_apply_apply]
        have hG₀_aut_z : G₀ z = diskAut α c z := by
          have := hG₀_aut hz_cl
          dsimp [Function.comp_def] at this
          rw [this, hF₀_id hz_cl]; rfl
        rw [← hzq, sphereFinitePart_coe, ← hG₀_z, hG₀_aut_z,
          ← hinv_cb ((diskAut_props hα hc).2.2.2.2.1.mapsTo hz_cb)]
        exact (hAut_inv z hz_cb).1
      rw [← hval hq₁, ← hval hq₂, ← hval hq₃]
      exact diskAut_preserves_posCyclic hα' hc' hF_cyc
    · intro hcyc
      exact ⟨hq₁, hq₂, hq₃, e₂, e₂.continuous.continuousOn, he₂_holo, he₂_bij_cl, hcyc⟩
  -- Now prove both parts of `14.20(c)`:
  refine ⟨?_, ?_⟩
  · -- Part 1: Extension of any spherical holomorphic bijection `f : Ω → T`
    intro f hf_holo hf_bij
    let S₀ : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' Ω₀
    have hS₀_open : IsOpen S₀ := OnePoint.isOpenEmbedding_coe.isOpenMap _ hΩ₀_reg.1
    have he₁_symm_Ω₀ : MapsTo e₁.symm S₀ Ω := by
      rintro _ ⟨z, hz, rfl⟩
      have hm : (z : RiemannSphere) ∈ e₁ '' Ω := by
        rw [show (e₁ : RiemannSphere → RiemannSphere) = moebiusMap a₁ b₁ c₁ d₁ from rfl, himg_Ω]
        exact ⟨z, hz, rfl⟩
      rcases hm with ⟨p, hp, hpz⟩; rw [← hpz, e₁.symm_apply_apply]; exact hp
    have he₂f_maps : ∀ z ∈ Ω₀, e₂ (f (e₁.symm (z : RiemannSphere))) ∈ US := by
      intro z hz
      have h1 : e₁.symm (z : RiemannSphere) ∈ Ω := he₁_symm_Ω₀ ⟨z, hz, rfl⟩
      exact hbij_T.mapsTo (hf_bij.mapsTo h1)
    let f₀ : ℂ → ℂ := fun z => sphereFinitePart (e₂ (f (e₁.symm (z : RiemannSphere))))
    have hf₀_holo : RudinRCA.Chapter10.HolomorphicOn f₀ Ω₀ := by
      have hcomp_sph : SphericalHolomorphicOn (e₂ ∘ f ∘ e₁.symm) S₀ := by
        have h1 : SphericalHolomorphicOn e₁.symm S₀ :=
          (moebiusMap_sphericalHolomorphicOn hdet₁').mono (subset_univ _)
        have h2 : SphericalHolomorphicOn (f ∘ e₁.symm) S₀ := hf_holo.comp hS₀_open h1 he₁_symm_Ω₀
        exact (moebiusMap_sphericalHolomorphicOn hdet₂).comp hS₀_open h2 (mapsTo_univ _ _)
      have hfin : ∀ z ∈ Ω₀, (e₂ ∘ f ∘ e₁.symm) (z : RiemannSphere) ≠ ∞ := by
        intro z hz hinf
        rcases he₂f_maps z hz with ⟨w, _, hw⟩
        exact OnePoint.coe_ne_infty w (hw.trans hinf)
      exact (sphericalHolomorphicOn_coe_iff hΩ₀_reg.1 hfin).mp hcomp_sph
    have hf₀_bij : BijOn f₀ Ω₀ (ball (0 : ℂ) 1) := by
      refine ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ heq => ?_, fun w hw => ?_⟩
      · rcases he₂f_maps z hz with ⟨w, hw, hw_eq⟩
        dsimp [f₀]; rw [← hw_eq, sphereFinitePart_coe]; exact hw
      · rcases he₂f_maps z₁ hz₁ with ⟨w₁, _, hw₁⟩
        rcases he₂f_maps z₂ hz₂ with ⟨w₂, _, hw₂⟩
        have hw12 : w₁ = w₂ := by
          have h1 : f₀ z₁ = w₁ := by dsimp [f₀]; rw [← hw₁, sphereFinitePart_coe]
          have h2 : f₀ z₂ = w₂ := by dsimp [f₀]; rw [← hw₂, sphereFinitePart_coe]
          rw [← h1, ← h2, heq]
        have he₂_eq : e₂ (f (e₁.symm (z₁ : RiemannSphere))) =
            e₂ (f (e₁.symm (z₂ : RiemannSphere))) := by rw [← hw₁, ← hw₂, hw12]
        exact OnePoint.coe_injective (e₁.symm.injective
          (hf_bij.injOn (he₁_symm_Ω₀ ⟨z₁, hz₁, rfl⟩) (he₁_symm_Ω₀ ⟨z₂, hz₂, rfl⟩)
            (e₂.injective he₂_eq)))
      · obtain ⟨q, hq_T, hqw⟩ := hbij_T.surjOn ⟨w, hw, rfl⟩
        obtain ⟨p, hp_Ω, hfp⟩ := hf_bij.surjOn hq_T
        have hp_e₁ : e₁ p ∈ S₀ := by
          dsimp [S₀]
          rw [show (e₁ : RiemannSphere → RiemannSphere) = moebiusMap a₁ b₁ c₁ d₁ from rfl,
            ← himg_Ω]
          exact ⟨p, hp_Ω, rfl⟩
        rcases hp_e₁ with ⟨z, hz_Ω₀, hzp⟩
        refine ⟨z, hz_Ω₀, ?_⟩
        dsimp [f₀]
        have hsymm : e₁.symm (z : RiemannSphere) = p := by rw [hzp, e₁.symm_apply_apply]
        rw [hsymm, hfp]
        change sphereFinitePart (moebiusMap a₂ b₂ c₂ d₂ q) = w
        rw [hqw, sphereFinitePart_coe]
    obtain ⟨hF₀_eq, hF₀_cont, _, hF₀_bij_cb, hF₀_bij_fr, _, _, _⟩ :=
      caratheodoryExtension_homeomorph_package hΩ₀_reg.1 hΩ₀_bdd hΩ₀_simple hf₀_holo hf₀_bij
    let F₀ : ℂ → ℂ := caratheodoryExtension f₀ Ω₀
    let F : RiemannSphere → RiemannSphere :=
      fun p => e₂.symm ((F₀ (sphereFinitePart (e₁ p)) : ℂ) : RiemannSphere)
    have hF_eq_f : Set.EqOn F f Ω := by
      intro p hp
      have hp_e₁ : e₁ p ∈ S₀ := by
        dsimp [S₀]
        rw [show (e₁ : RiemannSphere → RiemannSphere) = moebiusMap a₁ b₁ c₁ d₁ from rfl, ← himg_Ω]
        exact ⟨p, hp, rfl⟩
      rcases hp_e₁ with ⟨z, hz, hzp⟩
      dsimp [F, F₀]
      rw [← hzp, sphereFinitePart_coe, hF₀_eq hz]
      dsimp [f₀]
      have hsymm : e₁.symm (z : RiemannSphere) = p := by rw [hzp, e₁.symm_apply_apply]
      rw [hsymm]
      rcases he₂f_maps z hz with ⟨w, _, hw⟩
      rw [hsymm] at hw
      rw [← hw, sphereFinitePart_coe, hw, e₂.symm_apply_apply]
    have hF_cont : ContinuousOn F (closure Ω) :=
      e₂.symm.continuous.comp_continuousOn (OnePoint.continuous_coe.comp_continuousOn
        (hF₀_cont.comp (hret_cont.comp e₁.continuous.continuousOn he₁_cl_range) he₁_cl_maps))
    have hF_holo : SphericalHolomorphicOn F Ω := hf_holo.congr hΩ_sc.1.1 hF_eq_f.symm
    have hF_bij_cl : BijOn F (closure Ω) (closure T) := by
      refine ⟨fun p hp => ?_, fun p₁ hp₁ p₂ hp₂ heq => ?_, fun q hq => ?_⟩
      · have hw_cb : F₀ (sphereFinitePart (e₁ p)) ∈ closedBall (0 : ℂ) 1 :=
          hF₀_bij_cb.mapsTo (he₁_cl_maps hp)
        have hm : ((F₀ (sphereFinitePart (e₁ p)) : ℂ) : RiemannSphere) ∈ e₂ '' closure T := by
          rw [he₂_cl]; exact ⟨_, hw_cb, rfl⟩
        rcases hm with ⟨q, hq, hq_eq⟩
        dsimp [F]; rw [← hq_eq, e₂.symm_apply_apply]; exact hq
      · have h1 := OnePoint.coe_injective (e₂.symm.injective heq)
        have h2 := hF₀_bij_cb.injOn (he₁_cl_maps hp₁) (he₁_cl_maps hp₂) h1
        dsimp [Function.comp_def] at h2
        rcases he₁_cl_range hp₁ with ⟨z₁, hz₁⟩
        rcases he₁_cl_range hp₂ with ⟨z₂, hz₂⟩
        rw [← hz₁, ← hz₂, sphereFinitePart_coe, sphereFinitePart_coe] at h2
        exact e₁.injective (by rw [← hz₁, ← hz₂, h2])
      · have hm : e₂ q ∈ ((↑) : ℂ → RiemannSphere) '' closedBall (0 : ℂ) 1 := by
          rw [← he₂_cl]; exact ⟨q, hq, rfl⟩
        rcases hm with ⟨w, hw_cb, hwq⟩
        obtain ⟨z, hz_cl, hF₀z⟩ := hF₀_bij_cb.surjOn hw_cb
        have hz_in : (z : RiemannSphere) ∈ e₁ '' closure Ω := by rw [he₁_cl]; exact ⟨z, hz_cl, rfl⟩
        rcases hz_in with ⟨p, hp_cl, hpz⟩
        refine ⟨p, hp_cl, ?_⟩
        dsimp [F, F₀]; rw [hpz, sphereFinitePart_coe, hF₀z, hwq, e₂.symm_apply_apply]
    have hF_bij_fr : BijOn F (frontier Ω) (frontier T) := by
      refine ⟨fun p hp => ?_, hF_bij_cl.injOn.mono frontier_subset_closure, fun q hq => ?_⟩
      · have hp_e₁ : e₁ p ∈ ((↑) : ℂ → RiemannSphere) '' frontier Ω₀ := by
          rw [← he₁_fr]; exact ⟨p, hp, rfl⟩
        rcases hp_e₁ with ⟨z, hz_fr, hzp⟩
        have hw_sph : F₀ (sphereFinitePart (e₁ p)) ∈ sphere (0 : ℂ) 1 := by
          rw [← hzp, sphereFinitePart_coe]; exact hF₀_bij_fr.mapsTo hz_fr
        have hm : ((F₀ (sphereFinitePart (e₁ p)) : ℂ) : RiemannSphere) ∈ e₂ '' frontier T := by
          rw [he₂_fr]; exact ⟨_, hw_sph, rfl⟩
        rcases hm with ⟨q, hq, hq_eq⟩
        dsimp [F]; rw [← hq_eq, e₂.symm_apply_apply]; exact hq
      · have hm : e₂ q ∈ ((↑) : ℂ → RiemannSphere) '' sphere (0 : ℂ) 1 := by
          rw [← he₂_fr]; exact ⟨q, hq, rfl⟩
        rcases hm with ⟨w, hw_sph, hwq⟩
        obtain ⟨z, hz_fr, hF₀z⟩ := hF₀_bij_fr.surjOn hw_sph
        have hz_in : (z : RiemannSphere) ∈ e₁ '' frontier Ω := by rw [he₁_fr]; exact ⟨z, hz_fr, rfl⟩
        rcases hz_in with ⟨p, hp_fr, hpz⟩
        refine ⟨p, hp_fr, ?_⟩
        dsimp [F, F₀]; rw [hpz, sphereFinitePart_coe, hF₀z, hwq, e₂.symm_apply_apply]
    have : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
    let e_cl : closure Ω ≃ₜ closure T :=
      Continuous.homeoOfEquivCompactToT2 (f := hF_bij_cl.equiv)
        (hF_cont.domRestrict.codRestrict fun p => hF_bij_cl.mapsTo p.2)
    refine ⟨F, hF_eq_f, hF_cont, hF_holo, hF_bij_cl, hF_bij_fr, ⟨e_cl, fun _ => rfl⟩,
      fun G hG_cont hG_eq => eqOn_closure_riemannSphere hG_cont hF_cont (hG_eq.trans hF_eq_f.symm)⟩
  · -- Part 2: 3-point boundary normalization on `(Ω, T)` via `14.20(b)` on `Ω₀`!
    intro β₁ β₂ β₃ q₁ q₂ q₃ hβ₁ hβ₂ hβ₃ hβ12 hβ23 hβ13 hq₁ hq₂ hq₃ hq12 hq23 hq13
    let z₁ : ℂ := sphereFinitePart (e₁ β₁)
    let z₂ : ℂ := sphereFinitePart (e₁ β₂)
    let z₃ : ℂ := sphereFinitePart (e₁ β₃)
    let w₁ : ℂ := sphereFinitePart (e₂ q₁)
    let w₂ : ℂ := sphereFinitePart (e₂ q₂)
    let w₃ : ℂ := sphereFinitePart (e₂ q₃)
    have hz_coe : ∀ {β : RiemannSphere}, β ∈ frontier Ω →
        ((sphereFinitePart (e₁ β) : ℂ) : RiemannSphere) = e₁ β ∧
        sphereFinitePart (e₁ β) ∈ frontier Ω₀ := by
      intro β hβ
      have hm : e₁ β ∈ ((↑) : ℂ → RiemannSphere) '' frontier Ω₀ := by
        rw [← he₁_fr]; exact ⟨β, hβ, rfl⟩
      rcases hm with ⟨z, hz, hzb⟩
      rw [← hzb, sphereFinitePart_coe]; exact ⟨rfl, hz⟩
    have hw_coe : ∀ {q : RiemannSphere}, q ∈ frontier T →
        ((sphereFinitePart (e₂ q) : ℂ) : RiemannSphere) = e₂ q ∧
        sphereFinitePart (e₂ q) ∈ sphere (0 : ℂ) 1 := by
      intro q hq
      have hm : e₂ q ∈ ((↑) : ℂ → RiemannSphere) '' sphere (0 : ℂ) 1 := by
        rw [← he₂_fr]; exact ⟨q, hq, rfl⟩
      rcases hm with ⟨w, hw, hwq⟩
      rw [← hwq, sphereFinitePart_coe]; exact ⟨rfl, hw⟩
    have hz₁ : z₁ ∈ frontier Ω₀ := (hz_coe hβ₁).2
    have hz₂ : z₂ ∈ frontier Ω₀ := (hz_coe hβ₂).2
    have hz₃ : z₃ ∈ frontier Ω₀ := (hz_coe hβ₃).2
    have hw₁_s : w₁ ∈ sphere (0 : ℂ) 1 := (hw_coe hq₁).2
    have hw₂_s : w₂ ∈ sphere (0 : ℂ) 1 := (hw_coe hq₂).2
    have hw₃_s : w₃ ∈ sphere (0 : ℂ) 1 := (hw_coe hq₃).2
    have hz12 : z₁ ≠ z₂ := fun h => hβ12 (e₁.injective (by
      rw [← (hz_coe hβ₁).1, ← (hz_coe hβ₂).1]; exact congrArg ((↑) : ℂ → RiemannSphere) h))
    have hz23 : z₂ ≠ z₃ := fun h => hβ23 (e₁.injective (by
      rw [← (hz_coe hβ₂).1, ← (hz_coe hβ₃).1]; exact congrArg ((↑) : ℂ → RiemannSphere) h))
    have hz13 : z₁ ≠ z₃ := fun h => hβ13 (e₁.injective (by
      rw [← (hz_coe hβ₁).1, ← (hz_coe hβ₃).1]; exact congrArg ((↑) : ℂ → RiemannSphere) h))
    have hw12 : w₁ ≠ w₂ := fun h => hq12 (e₂.injective (by
      rw [← (hw_coe hq₁).1, ← (hw_coe hq₂).1]; exact congrArg ((↑) : ℂ → RiemannSphere) h))
    have hw23 : w₂ ≠ w₃ := fun h => hq23 (e₂.injective (by
      rw [← (hw_coe hq₂).1, ← (hw_coe hq₃).1]; exact congrArg ((↑) : ℂ → RiemannSphere) h))
    have hw13 : w₁ ≠ w₃ := fun h => hq13 (e₂.injective (by
      rw [← (hw_coe hq₁).1, ← (hw_coe hq₃).1]; exact congrArg ((↑) : ℂ → RiemannSphere) h))
    obtain ⟨hb_fwd, hb_rev⟩ := theorem14_20_part_b hΩ₀_sc hΩ₀_bdd hΩ₀_simple
      hz₁ hz₂ hz₃ hz12 hz23 hz13 hw₁_s hw₂_s hw₃_s hw12 hw23 hw13
    rw [hcyc_Ω_iff hβ₁ hβ₂ hβ₃, hcyc_T_iff hq₁ hq₂ hq₃]
    refine ⟨fun hcompat => ?_, ?_⟩
    · obtain ⟨F₀, hF₀_cont, hF₀_holo, hF₀_bij_ball, hF₀_bij_sph, hF₀_bij_cb, _,
        hF₀_1, hF₀_2, hF₀_3, hF₀_uniq⟩ := hb_fwd hcompat
      let F : RiemannSphere → RiemannSphere :=
        fun p => e₂.symm ((F₀ (sphereFinitePart (e₁ p)) : ℂ) : RiemannSphere)
      have hF_cont : ContinuousOn F (closure Ω) :=
        e₂.symm.continuous.comp_continuousOn (OnePoint.continuous_coe.comp_continuousOn
          (hF₀_cont.comp (hret_cont.comp e₁.continuous.continuousOn he₁_cl_range) he₁_cl_maps))
      have hF_holo : SphericalHolomorphicOn F Ω := by
        let G_mid : RiemannSphere → RiemannSphere :=
          fun r => ((F₀ (sphereFinitePart r) : ℂ) : RiemannSphere)
        let S₀ : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' Ω₀
        have hS₀_open : IsOpen S₀ := OnePoint.isOpenEmbedding_coe.isOpenMap _ hΩ₀_reg.1
        have hfin : ∀ z ∈ Ω₀, G_mid (z : RiemannSphere) ≠ ∞ := fun _ _ => OnePoint.coe_ne_infty _
        have hG_mid : SphericalHolomorphicOn G_mid S₀ :=
          (sphericalHolomorphicOn_coe_iff hΩ₀_reg.1 hfin).mpr (by simpa [G_mid] using hF₀_holo)
        have he₁_maps : MapsTo e₁ Ω S₀ := fun p hp => by
          dsimp [S₀]
          change moebiusMap a₁ b₁ c₁ d₁ p ∈ _
          rw [← himg_Ω]; exact ⟨p, hp, rfl⟩
        have hcomp1 : SphericalHolomorphicOn (G_mid ∘ e₁) Ω :=
          hG_mid.comp hΩ_sc.1.1 ((moebiusMap_sphericalHolomorphicOn hdet₁).mono (subset_univ _))
            he₁_maps
        exact (moebiusMap_sphericalHolomorphicOn hdet₂').comp hΩ_sc.1.1 hcomp1 (mapsTo_univ _ _)
      have hF_bij_Ω : BijOn F Ω T := by
        refine ⟨fun p hp => ?_, fun p₁ hp₁ p₂ hp₂ heq => ?_, fun q hq => ?_⟩
        · have hp_e₁ : e₁ p ∈ ((↑) : ℂ → RiemannSphere) '' Ω₀ := by
            change moebiusMap a₁ b₁ c₁ d₁ p ∈ _
            rw [← himg_Ω]; exact ⟨p, hp, rfl⟩
          rcases hp_e₁ with ⟨z, hz, hzp⟩
          have hw_ball : F₀ (sphereFinitePart (e₁ p)) ∈ ball (0 : ℂ) 1 := by
            rw [← hzp, sphereFinitePart_coe]; exact hF₀_bij_ball.mapsTo hz
          have hm : ((F₀ (sphereFinitePart (e₁ p)) : ℂ) : RiemannSphere) ∈ e₂ '' T := by
            rw [he₂_img]; exact ⟨_, hw_ball, rfl⟩
          rcases hm with ⟨q, hq, hq_eq⟩
          dsimp [F]; rw [← hq_eq, e₂.symm_apply_apply]; exact hq
        · have h1 := OnePoint.coe_injective (e₂.symm.injective heq)
          have h2 := hF₀_bij_cb.injOn (he₁_cl_maps (subset_closure hp₁))
            (he₁_cl_maps (subset_closure hp₂)) h1
          dsimp [Function.comp_def] at h2
          rcases he₁_cl_range (subset_closure hp₁) with ⟨u₁, hu₁⟩
          rcases he₁_cl_range (subset_closure hp₂) with ⟨u₂, hu₂⟩
          rw [← hu₁, ← hu₂, sphereFinitePart_coe, sphereFinitePart_coe] at h2
          exact e₁.injective (by rw [← hu₁, ← hu₂, h2])
        · have hm : e₂ q ∈ US := hbij_T.mapsTo hq
          rcases hm with ⟨w, hw_ball, hwq⟩
          obtain ⟨z, hz_Ω₀, hF₀z⟩ := hF₀_bij_ball.surjOn hw_ball
          have hz_in : (z : RiemannSphere) ∈ e₁ '' Ω := by
            rw [show (e₁ : RiemannSphere → RiemannSphere) = moebiusMap a₁ b₁ c₁ d₁ from rfl, himg_Ω]
            exact ⟨z, hz_Ω₀, rfl⟩
          rcases hz_in with ⟨p, hp_Ω, hpz⟩
          refine ⟨p, hp_Ω, ?_⟩
          dsimp [F]; rw [hpz, sphereFinitePart_coe, hF₀z, hwq, e₂.symm_apply_apply]
      have hF_bij_cl : BijOn F (closure Ω) (closure T) := by
        refine ⟨fun p hp => ?_, fun p₁ hp₁ p₂ hp₂ heq => ?_, fun q hq => ?_⟩
        · have hw_cb := hF₀_bij_cb.mapsTo (he₁_cl_maps hp)
          have hm : ((F₀ (sphereFinitePart (e₁ p)) : ℂ) : RiemannSphere) ∈ e₂ '' closure T := by
            rw [he₂_cl]; exact ⟨_, hw_cb, rfl⟩
          rcases hm with ⟨q, hq, hq_eq⟩
          dsimp [F]; rw [← hq_eq, e₂.symm_apply_apply]; exact hq
        · have h1 := OnePoint.coe_injective (e₂.symm.injective heq)
          have h2 := hF₀_bij_cb.injOn (he₁_cl_maps hp₁) (he₁_cl_maps hp₂) h1
          dsimp [Function.comp_def] at h2
          rcases he₁_cl_range hp₁ with ⟨u₁, hu₁⟩
          rcases he₁_cl_range hp₂ with ⟨u₂, hu₂⟩
          rw [← hu₁, ← hu₂, sphereFinitePart_coe, sphereFinitePart_coe] at h2
          exact e₁.injective (by rw [← hu₁, ← hu₂, h2])
        · have hm : e₂ q ∈ ((↑) : ℂ → RiemannSphere) '' closedBall (0 : ℂ) 1 := by
            rw [← he₂_cl]; exact ⟨q, hq, rfl⟩
          rcases hm with ⟨w, hw_cb, hwq⟩
          obtain ⟨z, hz_cl, hF₀z⟩ := hF₀_bij_cb.surjOn hw_cb
          have hz_in : (z : RiemannSphere) ∈ e₁ '' closure Ω := by rw [he₁_cl]; exact ⟨z, hz_cl, rfl⟩
          rcases hz_in with ⟨p, hp_cl, hpz⟩
          refine ⟨p, hp_cl, ?_⟩
          dsimp [F]; rw [hpz, sphereFinitePart_coe, hF₀z, hwq, e₂.symm_apply_apply]
      have hF_bij_fr : BijOn F (frontier Ω) (frontier T) := by
        refine ⟨fun p hp => ?_, hF_bij_cl.injOn.mono frontier_subset_closure, fun q hq => ?_⟩
        · have hw_sph := hF₀_bij_sph.mapsTo (hz_coe hp).2
          have hm : ((F₀ (sphereFinitePart (e₁ p)) : ℂ) : RiemannSphere) ∈ e₂ '' frontier T := by
            rw [he₂_fr]; exact ⟨_, hw_sph, rfl⟩
          rcases hm with ⟨q, hq, hq_eq⟩
          dsimp [F]; rw [← hq_eq, e₂.symm_apply_apply]; exact hq
        · have hm : e₂ q ∈ ((↑) : ℂ → RiemannSphere) '' sphere (0 : ℂ) 1 := by
            rw [← he₂_fr]; exact ⟨q, hq, rfl⟩
          rcases hm with ⟨w, hw_sph, hwq⟩
          obtain ⟨z, hz_fr, hF₀z⟩ := hF₀_bij_sph.surjOn hw_sph
          have hz_in : (z : RiemannSphere) ∈ e₁ '' frontier Ω := by rw [he₁_fr]; exact ⟨z, hz_fr, rfl⟩
          rcases hz_in with ⟨p, hp_fr, hpz⟩
          refine ⟨p, hp_fr, ?_⟩
          dsimp [F]; rw [hpz, sphereFinitePart_coe, hF₀z, hwq, e₂.symm_apply_apply]
      have : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
      let e_cl : closure Ω ≃ₜ closure T :=
        Continuous.homeoOfEquivCompactToT2 (f := hF_bij_cl.equiv)
          (hF_cont.domRestrict.codRestrict fun p => hF_bij_cl.mapsTo p.2)
      have hv₁ : F β₁ = q₁ := by dsimp [F]; rw [hF₀_1, (hw_coe hq₁).1, e₂.symm_apply_apply]
      have hv₂ : F β₂ = q₂ := by dsimp [F]; rw [hF₀_2, (hw_coe hq₂).1, e₂.symm_apply_apply]
      have hv₃ : F β₃ = q₃ := by dsimp [F]; rw [hF₀_3, (hw_coe hq₃).1, e₂.symm_apply_apply]
      refine ⟨F, hF_cont, hF_holo, hF_bij_Ω, hF_bij_fr, hF_bij_cl, ⟨e_cl, fun _ => rfl⟩,
        hv₁, hv₂, hv₃, ?_⟩
      intro G hG_cont hG_holo hG_bij hG₁ hG₂ hG₃
      obtain ⟨hG₀_cont, hG₀_holo, hG₀_bij, hG_rep⟩ := hbridge_to_plane hG_cont hG_holo hG_bij
      let G₀ : ℂ → ℂ := fun z => sphereFinitePart (e₂ (G (e₁.symm (z : RiemannSphere))))
      have hG₀_1 : G₀ z₁ = w₁ := by
        dsimp [G₀, z₁, w₁]; rw [(hz_coe hβ₁).1, e₁.symm_apply_apply, hG₁]
      have hG₀_2 : G₀ z₂ = w₂ := by
        dsimp [G₀, z₂, w₂]; rw [(hz_coe hβ₂).1, e₁.symm_apply_apply, hG₂]
      have hG₀_3 : G₀ z₃ = w₃ := by
        dsimp [G₀, z₃, w₃]; rw [(hz_coe hβ₃).1, e₁.symm_apply_apply, hG₃]
      have hGF₀ := hF₀_uniq G₀ hG₀_cont hG₀_holo hG₀_bij hG₀_1 hG₀_2 hG₀_3
      intro p hp
      rw [hG_rep p hp]
      dsimp [F]
      congr 2
      exact hGF₀ (he₁_cl_maps hp)
    · rintro ⟨F, hF_cont, hF_holo, hF_bij, hF₁, hF₂, hF₃⟩
      obtain ⟨hF₀_cont, hF₀_holo, hF₀_bij, _⟩ := hbridge_to_plane hF_cont hF_holo hF_bij
      let F₀ : ℂ → ℂ := fun z => sphereFinitePart (e₂ (F (e₁.symm (z : RiemannSphere))))
      refine hb_rev ⟨F₀, hF₀_cont, hF₀_holo, hF₀_bij, ?_, ?_, ?_⟩
      · dsimp [F₀, z₁, w₁]; rw [(hz_coe hβ₁).1, e₁.symm_apply_apply, hF₁]
      · dsimp [F₀, z₂, w₂]; rw [(hz_coe hβ₂).1, e₁.symm_apply_apply, hF₂]
      · dsimp [F₀, z₃, w₃]; rw [(hz_coe hβ₃).1, e₁.symm_apply_apply, hF₃]

/-- **14.20(d) (Conformal homeomorphism between closures of two bounded Jordan domains,
RCA p. 291):**
Let `Ω₁` and `Ω₂` be bounded simply connected regions in `ℂ` whose boundary points are all simple.
1. Composing a Riemann map `f₁ : Ω₁ → U` with the inverse of a Riemann map `f₂ : Ω₂ → U` and their
   `14.19` extensions yields a holomorphic bijection `Ω₁ → Ω₂` extending to a homeomorphism
   `closure Ω₁ ≃ₜ closure Ω₂` (carrying `frontier Ω₁` bijectively onto `frontier Ω₂`).
2. More generally, **every** holomorphic bijection `h : Ω₁ → Ω₂` extends uniquely to a continuous
   bijection `H : closure Ω₁ → closure Ω₂` inducing a homeomorphism `closure Ω₁ ≃ₜ closure Ω₂` and
   carrying `frontier Ω₁` bijectively onto `frontier Ω₂`. -/
theorem theorem14_20_part_d {Ω₁ Ω₂ : Set ℂ}
    (hΩ₁_sc : RudinRCA.Chapter10.BookSimplyConnected Ω₁)
    (hΩ₁_bdd : Bornology.IsBounded Ω₁)
    (hΩ₁_simple : ∀ β ∈ frontier Ω₁, IsSimpleBoundaryPoint Ω₁ β)
    (hΩ₂_sc : RudinRCA.Chapter10.BookSimplyConnected Ω₂)
    (hΩ₂_bdd : Bornology.IsBounded Ω₂)
    (hΩ₂_simple : ∀ β ∈ frontier Ω₂, IsSimpleBoundaryPoint Ω₂ β) :
    (∀ {h : ℂ → ℂ}, RudinRCA.Chapter10.HolomorphicOn h Ω₁ → BijOn h Ω₁ Ω₂ →
      ∃ H : ℂ → ℂ,
        Set.EqOn H h Ω₁ ∧
        ContinuousOn H (closure Ω₁) ∧
        RudinRCA.Chapter10.HolomorphicOn H Ω₁ ∧
        BijOn H (closure Ω₁) (closure Ω₂) ∧
        BijOn H (frontier Ω₁) (frontier Ω₂) ∧
        (∃ e : closure Ω₁ ≃ₜ closure Ω₂, ∀ z : closure Ω₁, (e z : ℂ) = H z.1) ∧
        ∀ K : ℂ → ℂ, ContinuousOn K (closure Ω₁) → Set.EqOn K h Ω₁ →
          Set.EqOn K H (closure Ω₁)) ∧
    (∃ H : ℂ → ℂ,
      ContinuousOn H (closure Ω₁) ∧
      RudinRCA.Chapter10.HolomorphicOn H Ω₁ ∧
      BijOn H Ω₁ Ω₂ ∧
      BijOn H (closure Ω₁) (closure Ω₂) ∧
      BijOn H (frontier Ω₁) (frontier Ω₂) ∧
      ∃ e : closure Ω₁ ≃ₜ closure Ω₂, ∀ z : closure Ω₁, (e z : ℂ) = H z.1) := by
  have hext : ∀ {h : ℂ → ℂ}, RudinRCA.Chapter10.HolomorphicOn h Ω₁ → BijOn h Ω₁ Ω₂ →
      ∃ H : ℂ → ℂ,
        Set.EqOn H h Ω₁ ∧
        ContinuousOn H (closure Ω₁) ∧
        RudinRCA.Chapter10.HolomorphicOn H Ω₁ ∧
        BijOn H (closure Ω₁) (closure Ω₂) ∧
        BijOn H (frontier Ω₁) (frontier Ω₂) ∧
        (∃ e : closure Ω₁ ≃ₜ closure Ω₂, ∀ z : closure Ω₁, (e z : ℂ) = H z.1) ∧
        ∀ K : ℂ → ℂ, ContinuousOn K (closure Ω₁) → Set.EqOn K h Ω₁ →
          Set.EqOn K H (closure Ω₁) := by
    intro h hh_holo hh_bij
    obtain ⟨f₂, hf₂_holo, hf₂_bij⟩ := exists_riemann_map_of_bounded hΩ₂_sc hΩ₂_bdd
    let f₁ : ℂ → ℂ := f₂ ∘ h
    have hf₁_holo : RudinRCA.Chapter10.HolomorphicOn f₁ Ω₁ :=
      fun z hz => (hf₂_holo (h z) (hh_bij.mapsTo hz)).comp z (hh_holo z hz)
    have hf₁_bij : BijOn f₁ Ω₁ (ball (0 : ℂ) 1) := hf₂_bij.comp hh_bij
    obtain ⟨hF₁_eq, hF₁_cont, _, hF₁_bij_cb, hF₁_bij_fr, _, ⟨e₁, he₁⟩, _⟩ :=
      caratheodoryExtension_homeomorph_package hΩ₁_sc.1.1 hΩ₁_bdd hΩ₁_simple hf₁_holo hf₁_bij
    obtain ⟨hF₂_eq, hF₂_cont, _, hF₂_bij_cb, hF₂_bij_fr, _, ⟨e₂, he₂⟩, _⟩ :=
      caratheodoryExtension_homeomorph_package hΩ₂_sc.1.1 hΩ₂_bdd hΩ₂_simple hf₂_holo hf₂_bij
    let e : closure Ω₁ ≃ₜ closure Ω₂ := e₁.trans e₂.symm
    classical
    let H : ℂ → ℂ := fun z => if hz : z ∈ closure Ω₁ then (e ⟨z, hz⟩ : ℂ) else 0
    have hH_val : ∀ z (hz : z ∈ closure Ω₁), H z = (e ⟨z, hz⟩ : ℂ) := fun z hz => by
      simp only [H, hz, ↓reduceDIte]
    have hH_eq : Set.EqOn H h Ω₁ := by
      intro z hz
      have hz_cl : z ∈ closure Ω₁ := subset_closure hz
      have hhz_cl : h z ∈ closure Ω₂ := subset_closure (hh_bij.mapsTo hz)
      have he₁₂ : e₁ ⟨z, hz_cl⟩ = e₂ ⟨h z, hhz_cl⟩ := by
        ext
        rw [he₁, he₂, hF₁_eq hz, hF₂_eq (hh_bij.mapsTo hz)]
        rfl
      rw [hH_val z hz_cl]
      dsimp [e]
      rw [he₁₂, e₂.symm_apply_apply]
    have hH_cont : ContinuousOn H (closure Ω₁) := by
      rw [continuousOn_iff_continuous_domRestrict]
      refine (continuous_subtype_val.comp e.continuous).congr fun p => ?_
      dsimp [Set.domRestrict]
      exact (hH_val p.1 p.2).symm
    have hH_holo : RudinRCA.Chapter10.HolomorphicOn H Ω₁ :=
      fun z hz => (hh_holo z hz).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hΩ₁_sc.1.1.mem_nhds hz) fun w hw => hH_eq hw)
    have hH_bij_cl : BijOn H (closure Ω₁) (closure Ω₂) := by
      refine ⟨fun z hz => by rw [hH_val z hz]; exact (e ⟨z, hz⟩).2,
        fun z₁ hz₁ z₂ hz₂ heq => ?_, fun w hw => ?_⟩
      · rw [hH_val z₁ hz₁, hH_val z₂ hz₂] at heq
        exact congrArg Subtype.val (e.injective (Subtype.ext heq))
      · refine ⟨(e.symm ⟨w, hw⟩ : ℂ), (e.symm ⟨w, hw⟩).2, ?_⟩
        rw [hH_val _ (e.symm ⟨w, hw⟩).2]
        simp
    have hH_bij_fr : BijOn H (frontier Ω₁) (frontier Ω₂) := by
      refine ⟨fun β hβ => ?_, hH_bij_cl.injOn.mono frontier_subset_closure, fun γ hγ => ?_⟩
      · have hβ_cl : β ∈ closure Ω₁ := frontier_subset_closure hβ
        refine mem_frontier_of_mem_closure_not_mem (hH_bij_cl.mapsTo hβ_cl) ?_
        intro hmem₂
        have he₁_sph : (e₁ ⟨β, hβ_cl⟩ : ℂ) ∈ sphere (0 : ℂ) 1 := by
          rw [he₁]; exact hF₁_bij_fr.mapsTo hβ
        have he₂_eq : e₂ ⟨H β, subset_closure hmem₂⟩ = e₁ ⟨β, hβ_cl⟩ := by
          have : ⟨H β, subset_closure hmem₂⟩ = e ⟨β, hβ_cl⟩ :=
            Subtype.ext (hH_val β hβ_cl)
          rw [this]; dsimp [e]; exact e₂.apply_symm_apply _
        have hball : (e₂ ⟨H β, subset_closure hmem₂⟩ : ℂ) ∈ ball (0 : ℂ) 1 := by
          rw [he₂, hF₂_eq hmem₂]; exact hf₂_bij.mapsTo hmem₂
        rw [he₂_eq] at hball
        have h1 : ‖(e₁ ⟨β, hβ_cl⟩ : ℂ)‖ = 1 := by simpa using he₁_sph
        have h2 : ‖(e₁ ⟨β, hβ_cl⟩ : ℂ)‖ < 1 := mem_ball_zero_iff.mp hball
        linarith
      · obtain ⟨z, hz_cl, hHz⟩ := hH_bij_cl.surjOn (frontier_subset_closure hγ)
        refine ⟨z, mem_frontier_of_mem_closure_not_mem hz_cl fun hz_in => ?_, hHz⟩
        rw [hH_eq hz_in] at hHz
        have hγ_not_Ω₂ : γ ∉ Ω₂ := by
          rw [frontier, hΩ₂_sc.1.1.interior_eq] at hγ; exact hγ.2
        exact hγ_not_Ω₂ (hHz ▸ hh_bij.mapsTo hz_in)
    refine ⟨H, hH_eq, hH_cont, hH_holo, hH_bij_cl, hH_bij_fr,
      ⟨e, fun z => (hH_val z.1 z.2).symm⟩,
      fun K hK_cont hK_eq => eqOn_of_continuousOn_closure_eqOn hK_cont hH_cont
        (hK_eq.trans hH_eq.symm)⟩
  refine ⟨hext, ?_⟩
  obtain ⟨f₁, hf₁_holo, hf₁_bij⟩ := exists_riemann_map_of_bounded hΩ₁_sc hΩ₁_bdd
  obtain ⟨f₂, hf₂_holo, hf₂_bij⟩ := exists_riemann_map_of_bounded hΩ₂_sc hΩ₂_bdd
  obtain ⟨ψ₂, hψ₂_holo, hψ₂_bij, _, _⟩ := (theorem14_7 hΩ₂_sc.1.1 hf₂_holo hf₂_bij).2.1
  let h : ℂ → ℂ := ψ₂ ∘ f₁
  have hh_holo : RudinRCA.Chapter10.HolomorphicOn h Ω₁ :=
    fun z hz => (hψ₂_holo (f₁ z) (hf₁_bij.mapsTo hz)).comp z (hf₁_holo z hz)
  have hh_bij : BijOn h Ω₁ Ω₂ := hψ₂_bij.comp hf₁_bij
  obtain ⟨H, hH_eq, hH_cont, hH_holo, hH_bij_cl, hH_bij_fr, he, _⟩ := hext hh_holo hh_bij
  have hH_bij_Ω : BijOn H Ω₁ Ω₂ := by
    refine ⟨fun z hz => by rw [hH_eq hz]; exact hh_bij.mapsTo hz,
      fun z₁ hz₁ z₂ hz₂ heq => hh_bij.injOn hz₁ hz₂ (by rwa [← hH_eq hz₁, ← hH_eq hz₂]),
      fun w hw => ?_⟩
    obtain ⟨z, hz, hzw⟩ := hh_bij.surjOn hw
    exact ⟨z, hz, by rw [hH_eq hz, hzw]⟩
  exact ⟨H, hH_cont, hH_holo, hH_bij_Ω, hH_bij_cl, hH_bij_fr, he⟩

/-- **Node 14.20 (Remarks on Carathéodory boundary correspondence, Jordan curves, three-point
normalization, Riemann-sphere / half-plane domains, and two-region composition, RCA p. 291):**
Combined package of all four printed subclaims `(a)`–`(d)`:
- `(a)` Forward Jordan-curve boundary + closed-disc homeomorphism under `14.19`, **and** the full
  converse that every bounded region with Jordan-curve boundary is simply connected with all
  boundary points simple (`theorem14_20_part_a`);
- `(b)` Unique three-point boundary normalization in compatible cyclic order (`theorem14_20_part_b`);
- `(c)` Extension of both `14.19` and three-point normalization to simply connected spherical
  regions `Ω ⊆ RiemannSphere` with `(interior Ωᶜ).Nonempty` and simple boundary points, with `U`
  replaceable by any open half-plane `IsOpenHalfPlane H` (`theorem14_20_part_c`);
- `(d)` Holomorphic interior correspondence extending to a closure homeomorphism between any two
  such bounded regions (`theorem14_20_part_d`). -/
theorem theorem14_20 :
    ((∀ {Ω : Set ℂ}, RudinRCA.Chapter10.BookSimplyConnected Ω →
        Bornology.IsBounded Ω →
        (∀ β ∈ frontier Ω, IsSimpleBoundaryPoint Ω β) →
        IsJordanCurve (frontier Ω) ∧ Nonempty (closure Ω ≃ₜ closedBall (0 : ℂ) 1)) ∧
      (∀ {Ω : Set ℂ}, RudinRCA.Chapter10.IsRegion Ω →
        Bornology.IsBounded Ω →
        IsJordanCurve (frontier Ω) →
        RudinRCA.Chapter10.BookSimplyConnected Ω ∧
          ∀ β ∈ frontier Ω, IsSimpleBoundaryPoint Ω β)) ∧
    (∀ {Ω : Set ℂ},
      RudinRCA.Chapter10.BookSimplyConnected Ω →
      Bornology.IsBounded Ω →
      (∀ β ∈ frontier Ω, IsSimpleBoundaryPoint Ω β) →
      ∀ {β₁ β₂ β₃ w₁ w₂ w₃ : ℂ},
        β₁ ∈ frontier Ω → β₂ ∈ frontier Ω → β₃ ∈ frontier Ω →
        β₁ ≠ β₂ → β₂ ≠ β₃ → β₁ ≠ β₃ →
        w₁ ∈ sphere (0 : ℂ) 1 → w₂ ∈ sphere (0 : ℂ) 1 → w₃ ∈ sphere (0 : ℂ) 1 →
        w₁ ≠ w₂ → w₂ ≠ w₃ → w₁ ≠ w₃ →
        ((BoundaryPosCyclic Ω β₁ β₂ β₃ ↔ UnitCirclePosCyclic w₁ w₂ w₃) ↔
          ∃ F : ℂ → ℂ,
            ContinuousOn F (closure Ω) ∧
            RudinRCA.Chapter10.HolomorphicOn F Ω ∧
            BijOn F (closure Ω) (closedBall (0 : ℂ) 1) ∧
            F β₁ = w₁ ∧ F β₂ = w₂ ∧ F β₃ = w₃ ∧
            ∀ G : ℂ → ℂ,
              ContinuousOn G (closure Ω) →
              RudinRCA.Chapter10.HolomorphicOn G Ω →
              BijOn G (closure Ω) (closedBall (0 : ℂ) 1) →
              G β₁ = w₁ → G β₂ = w₂ → G β₃ = w₃ →
              Set.EqOn G F (closure Ω))) ∧
    (IsMoebiusDiscTarget (((↑) : ℂ → RiemannSphere) '' ball (0 : ℂ) 1) ∧
      (∀ {H : Set ℂ}, IsOpenHalfPlane H →
        IsMoebiusDiscTarget (((↑) : ℂ → RiemannSphere) '' H)) ∧
      ∀ {Ω T : Set RiemannSphere},
        SphericalSimplyConnected Ω →
        (interior Ωᶜ).Nonempty →
        (∀ β ∈ frontier Ω, IsSphericalSimpleBoundaryPoint Ω β) →
        IsMoebiusDiscTarget T →
        (∀ {f : RiemannSphere → RiemannSphere},
          SphericalHolomorphicOn f Ω → BijOn f Ω T →
          ∃ e : closure Ω ≃ₜ closure T,
            ∀ p : Ω, (e ⟨p.1, subset_closure p.2⟩ : RiemannSphere) = f p.1) ∧
        (∀ {β₁ β₂ β₃ q₁ q₂ q₃ : RiemannSphere},
          β₁ ∈ frontier Ω → β₂ ∈ frontier Ω → β₃ ∈ frontier Ω →
          β₁ ≠ β₂ → β₂ ≠ β₃ → β₁ ≠ β₃ →
          q₁ ∈ frontier T → q₂ ∈ frontier T → q₃ ∈ frontier T →
          q₁ ≠ q₂ → q₂ ≠ q₃ → q₁ ≠ q₃ →
          (SphericalBoundaryPosCyclic Ω β₁ β₂ β₃ ↔ SphericalBoundaryPosCyclic T q₁ q₂ q₃) →
          ∃ F : RiemannSphere → RiemannSphere,
            ContinuousOn F (closure Ω) ∧
            SphericalHolomorphicOn F Ω ∧
            BijOn F Ω T ∧
            BijOn F (closure Ω) (closure T) ∧
            F β₁ = q₁ ∧ F β₂ = q₂ ∧ F β₃ = q₃ ∧
            ∀ G : RiemannSphere → RiemannSphere,
              ContinuousOn G (closure Ω) →
              SphericalHolomorphicOn G Ω →
              BijOn G (closure Ω) (closure T) →
              G β₁ = q₁ → G β₂ = q₂ → G β₃ = q₃ →
              Set.EqOn G F (closure Ω))) ∧
    (∀ {Ω₁ Ω₂ : Set ℂ},
      RudinRCA.Chapter10.BookSimplyConnected Ω₁ →
      Bornology.IsBounded Ω₁ →
      (∀ β ∈ frontier Ω₁, IsSimpleBoundaryPoint Ω₁ β) →
      RudinRCA.Chapter10.BookSimplyConnected Ω₂ →
      Bornology.IsBounded Ω₂ →
      (∀ β ∈ frontier Ω₂, IsSimpleBoundaryPoint Ω₂ β) →
      ∃ H : ℂ → ℂ,
        ContinuousOn H (closure Ω₁) ∧
        RudinRCA.Chapter10.HolomorphicOn H Ω₁ ∧
        BijOn H Ω₁ Ω₂ ∧
        BijOn H (closure Ω₁) (closure Ω₂) ∧
        BijOn H (frontier Ω₁) (frontier Ω₂) ∧
        ∃ e : closure Ω₁ ≃ₜ closure Ω₂, ∀ z : closure Ω₁, (e z : ℂ) = H z.1) := by
  refine ⟨⟨theorem14_20_part_a.1, theorem14_20_part_a.2.1⟩, ?_, ?_, ?_⟩
  · intro Ω hΩ_sc hΩ_bdd hΩ_simple β₁ β₂ β₃ w₁ w₂ w₃
      hβ₁ hβ₂ hβ₃ hβ12 hβ23 hβ13 hw₁ hw₂ hw₃ hw12 hw23 hw13
    obtain ⟨hfwd, hrev⟩ := theorem14_20_part_b hΩ_sc hΩ_bdd hΩ_simple
      hβ₁ hβ₂ hβ₃ hβ12 hβ23 hβ13 hw₁ hw₂ hw₃ hw12 hw23 hw13
    constructor
    · intro hcompat
      obtain ⟨F, hFc, hFh, _, _, hFcb, _, h1, h2, h3, hu⟩ := hfwd hcompat
      exact ⟨F, hFc, hFh, hFcb, h1, h2, h3, hu⟩
    · rintro ⟨F, hFc, hFh, hFcb, h1, h2, h3, _⟩
      exact hrev ⟨F, hFc, hFh, hFcb, h1, h2, h3⟩
  · obtain ⟨hU, hH, hmain⟩ := theorem14_20_part_c
    refine ⟨hU, hH, fun hΩ_sc hcompl hsimp hT => ?_⟩
    obtain ⟨hext, h3pt⟩ := hmain hΩ_sc hcompl hsimp hT
    refine ⟨fun hf_holo hf_bij => ?_,
      fun hβ₁ hβ₂ hβ₃ hβ12 hβ23 hβ13 hq₁ hq₂ hq₃ hq12 hq23 hq13 hcompat => ?_⟩
    · obtain ⟨F, hFeq, _, _, _, _, ⟨e, he⟩, _⟩ := hext hf_holo hf_bij
      exact ⟨e, fun p => by rw [he]; exact hFeq p.2⟩
    · obtain ⟨F, hFc, hFh, hFΩ, _, hFcl, _, h1, h2, h3, hu⟩ :=
        (h3pt hβ₁ hβ₂ hβ₃ hβ12 hβ23 hβ13 hq₁ hq₂ hq₃ hq12 hq23 hq13).1 hcompat
      exact ⟨F, hFc, hFh, hFΩ, hFcl, h1, h2, h3, hu⟩
  · intro Ω₁ Ω₂ h1_sc h1_bdd h1_simp h2_sc h2_bdd h2_simp
    exact (theorem14_20_part_d h1_sc h1_bdd h1_simp h2_sc h2_bdd h2_simp).2

/-! ### Nodes 14.21 and 14.22: Annuli and Conformal Classification by Radius Ratio -/

/-- **Definition 14.21 (Open annulus `A(r, R)`, RCA pp. 291–292):**
`annulus r R = {z ∈ ℂ | r < ‖z‖ < R}`. -/
def annulus (r R : ℝ) : Set ℂ :=
  {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R}

theorem annulus_isOpen (r R : ℝ) : IsOpen (annulus r R) :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

theorem annulus_isRegion {r R : ℝ} (hr : 0 ≤ r) (hlt : r < R) :
    RudinRCA.Chapter10.IsRegion (annulus r R) := by
  have hmid_pos : 0 < (r + R) / 2 := by linarith
  have hmid_mem : (((r + R) / 2 : ℝ) : ℂ) ∈ annulus r R := by
    simp only [annulus, Set.mem_setOf_eq, Complex.norm_real, Real.norm_of_nonneg hmid_pos.le]
    exact ⟨by linarith, by linarith⟩
  refine ⟨annulus_isOpen r R, ⟨(((r + R) / 2 : ℝ) : ℂ), hmid_mem⟩, ?_⟩
  let g : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)
  have hg_cont : Continuous g :=
    (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hS_pre : IsPreconnected (Ioo r R ×ˢ (Set.univ : Set ℝ)) :=
    ((convex_Ioo r R).prod convex_univ).isPreconnected
  have himg : g '' (Ioo r R ×ˢ (Set.univ : Set ℝ)) = annulus r R := by
    ext z
    constructor
    · rintro ⟨⟨ρ, θ⟩, ⟨⟨hρ_lo, hρ_hi⟩, _⟩, rfl⟩
      have hρ_pos : 0 < ρ := lt_of_le_of_lt hr hρ_lo
      have hnorm : ‖g (ρ, θ)‖ = ρ := by
        dsimp [g]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ_pos.le, Complex.norm_exp]
        simp
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hz_lo, hz_hi⟩
      refine ⟨(‖z‖, Complex.arg z), ⟨⟨hz_lo, hz_hi⟩, trivial⟩, ?_⟩
      dsimp [g]
      exact Complex.norm_mul_exp_arg_mul_I z
  rw [← himg]
  exact hS_pre.image g hg_cont.continuousOn

theorem annulus_not_simplyConnected {r R : ℝ} (hr : 0 < r) (hlt : r < R) :
    ¬ RudinRCA.Chapter10.BookSimplyConnected (annulus r R) := by
  intro hsc
  have hreg := annulus_isRegion hr.le hlt
  have hconn : IsConnected (RudinRCA.Chapter13.sphericalCompl (annulus r R)) :=
    (((RudinRCA.Chapter13.theorem13_11 hreg).2.2.1).trans
      (RudinRCA.Chapter13.theorem13_11 hreg).2.2.2.1).mp hsc
  let S : Set RudinRCA.Chapter13.RiemannSphere := RudinRCA.Chapter13.sphericalCompl (annulus r R)
  let U₁ : Set RudinRCA.Chapter13.RiemannSphere :=
    ((↑) : ℂ → RudinRCA.Chapter13.RiemannSphere) '' ball (0 : ℂ) R
  let U₂ : Set RudinRCA.Chapter13.RiemannSphere := RudinRCA.Chapter13.infinityDisc r
  have hU₁_open : IsOpen U₁ :=
    RudinRCA.Chapter13.finite_chart_open_embedding.isOpenMap _ isOpen_ball
  have hU₂_open : IsOpen U₂ := RudinRCA.Chapter13.isOpen_infinityDisc r
  have hcov : S ⊆ U₁ ∪ U₂ := by
    intro p hp
    induction p using OnePoint.rec with
    | infty =>
      exact Or.inr (RudinRCA.Chapter13.infinity_mem_infinityDisc r)
    | coe z =>
      have hnot : z ∉ annulus r R := (RudinRCA.Chapter13.coe_mem_sphericalCompl z _).mp hp
      by_cases hzR : ‖z‖ < R
      · exact Or.inl ⟨z, by simpa [Metric.mem_ball, dist_zero_right] using hzR, rfl⟩
      · have hgt : r < ‖z‖ := lt_of_lt_of_le hlt (le_of_not_gt hzR)
        exact Or.inr ((RudinRCA.Chapter13.coe_mem_infinityDisc z r).mpr hgt)
  have hne₁ : (S ∩ U₁).Nonempty := by
    refine ⟨((0 : ℂ) : RudinRCA.Chapter13.RiemannSphere), ?_, ?_⟩
    · rw [RudinRCA.Chapter13.coe_mem_sphericalCompl]
      intro h0
      have : r < ‖(0 : ℂ)‖ := h0.1
      simp at this; linarith
    · exact ⟨0, mem_ball_self (lt_trans hr hlt), rfl⟩
  have hne₂ : (S ∩ U₂).Nonempty :=
    ⟨∞, RudinRCA.Chapter13.infinity_mem_sphericalCompl _,
      RudinRCA.Chapter13.infinity_mem_infinityDisc r⟩
  obtain ⟨p, hpS, hp₁, hp₂⟩ := hconn.isPreconnected U₁ U₂ hU₁_open hU₂_open hcov hne₁ hne₂
  rcases hp₁ with ⟨z, hz_ball, rfl⟩
  have hz_gt : r < ‖z‖ := (RudinRCA.Chapter13.coe_mem_infinityDisc z r).mp hp₂
  have hz_lt : ‖z‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hz_ball
  exact ((RudinRCA.Chapter13.coe_mem_sphericalCompl z _).mp hpS) ⟨hz_gt, hz_lt⟩

/-- **Node 14.21 (Conformal equivalence of proper simply connected regions and dilation of annuli,
RCA pp. 291–292):**
1. Any two proper simply connected plane regions `Ω₁, Ω₂ ⊊ ℂ` are conformally equivalent.
2. For `0 < r < R` and `0 < c`, positive real dilation `z ↦ c z` is holomorphic and maps
   `annulus r R` bijectively onto `annulus (c * r) (c * R)`.
3. Consequently, for `0 < r₁ < R₁` and `0 < r₂ < R₂`, `R₁ / r₁ = R₂ / r₂` implies that
   `annulus r₁ R₁` and `annulus r₂ R₂` are conformally equivalent. -/
theorem theorem14_21 :
    (∀ {Ω₁ Ω₂ : Set ℂ},
      RudinRCA.Chapter10.BookSimplyConnected Ω₁ → Ω₁ ≠ Set.univ →
      RudinRCA.Chapter10.BookSimplyConnected Ω₂ → Ω₂ ≠ Set.univ →
      ConformallyEquivalent Ω₁ Ω₂) ∧
    (∀ {r R c : ℝ}, 0 < r → r < R → 0 < c →
      RudinRCA.Chapter10.HolomorphicOn (fun z : ℂ => (c : ℂ) * z) (annulus r R) ∧
        BijOn (fun z : ℂ => (c : ℂ) * z) (annulus r R) (annulus (c * r) (c * R))) ∧
    (∀ {r₁ R₁ r₂ R₂ : ℝ}, 0 < r₁ → r₁ < R₁ → 0 < r₂ → r₂ < R₂ →
      R₁ / r₁ = R₂ / r₂ → ConformallyEquivalent (annulus r₁ R₁) (annulus r₂ R₂)) := by
  have hdil : ∀ {r R c : ℝ}, 0 < r → r < R → 0 < c →
      RudinRCA.Chapter10.HolomorphicOn (fun z : ℂ => (c : ℂ) * z) (annulus r R) ∧
        BijOn (fun z : ℂ => (c : ℂ) * z) (annulus r R) (annulus (c * r) (c * R)) := by
    intro r R c _ _ hc
    have hc_ne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    refine ⟨fun _ _ => differentiableAt_id.const_mul (c : ℂ), ?_, ?_, ?_⟩
    · intro z hz
      simp only [annulus, Set.mem_setOf_eq, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hc.le]
      exact ⟨mul_lt_mul_of_pos_left hz.1 hc, mul_lt_mul_of_pos_left hz.2 hc⟩
    · intro z₁ _ z₂ _ heq
      exact mul_left_cancel₀ hc_ne heq
    · intro w hw
      refine ⟨w / (c : ℂ), ?_, mul_div_cancel₀ w hc_ne⟩
      simp only [annulus, Set.mem_setOf_eq, norm_div, Complex.norm_real,
        Real.norm_of_nonneg hc.le]
      exact ⟨(lt_div_iff₀ hc).mpr (by linarith [hw.1]),
        (div_lt_iff₀ hc).mpr (by linarith [hw.2])⟩
  refine ⟨?_, @hdil, ?_⟩
  · intro Ω₁ Ω₂ hsc₁ hne₁ hsc₂ hne₂
    exact conformallyEquivalent_trans
      (theorem14_8.1 hsc₁.1 hsc₁ hne₁)
      (conformallyEquivalent_symm hsc₂.1.1 (theorem14_8.1 hsc₂.1 hsc₂ hne₂))
  · intro r₁ R₁ r₂ R₂ hr₁ hlt₁ hr₂ _ hratio
    let c : ℝ := r₂ / r₁
    have hc : 0 < c := div_pos hr₂ hr₁
    obtain ⟨hholo, hbij⟩ := hdil hr₁ hlt₁ hc
    have hcr : c * r₁ = r₂ := div_mul_cancel₀ r₂ hr₁.ne'
    have hcR : c * R₁ = R₂ := by
      dsimp [c]
      have h1 : (r₂ / r₁) * R₁ = r₂ * (R₁ / r₁) := by ring
      rw [h1, hratio, mul_div_cancel₀ R₂ hr₂.ne']
    rw [hcr, hcR] at hbij
    exact ⟨fun z => (c : ℂ) * z, hholo, hbij⟩

private theorem localRe_nonpos_of_compact_bdry {Ω K : Set ℂ} {u : ℂ → ℝ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hK_ne : K.Nonempty) (hsub : Ω ⊆ K)
    (hu_cont : ContinuousOn u K)
    (hu_local : ∀ x₀ : ℂ, ∀ r > 0, ball x₀ r ⊆ Ω →
      ∃ F : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn F (ball x₀ r) ∧
        ∀ w ∈ ball x₀ r, u w = (F w).re)
    (hu_bdry : ∀ z ∈ K \ Ω, u z ≤ 0) :
    ∀ z ∈ Ω, u z ≤ 0 := by
  obtain ⟨z_max, hz_max_K, hz_max⟩ := hK.exists_isMaxOn hK_ne hu_cont
  let M : ℝ := u z_max
  by_cases hM : M ≤ 0
  · intro z hz
    exact le_trans (hz_max (hsub hz)) hM
  · exfalso
    have hM_pos : 0 < M := lt_of_not_ge hM
    let S : Set ℂ := {x ∈ K | u x = M}
    have hS_ne : S.Nonempty := ⟨z_max, hz_max_K, rfl⟩
    have hS_compact : IsCompact S := by
      haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
      let T : Set K := {p : K | u p.1 = M}
      have hT_closed : IsClosed T :=
        isClosed_eq (hu_cont.comp_continuous continuous_subtype_val Subtype.prop) continuous_const
      have hS_eq : S = Subtype.val '' T := by
        ext x
        constructor
        · rintro ⟨hxK, hux⟩; exact ⟨⟨x, hxK⟩, hux, rfl⟩
        · rintro ⟨⟨y, hyK⟩, huy, rfl⟩; exact ⟨hyK, huy⟩
      rw [hS_eq]
      exact hT_closed.isCompact.image continuous_subtype_val
    obtain ⟨x₀, hx₀_S, hx₀_max⟩ := hS_compact.exists_isMaxOn hS_ne Complex.continuous_re.continuousOn
    have hx₀_Ω : x₀ ∈ Ω := by
      by_contra hx₀_not
      have hle0 : u x₀ ≤ 0 := hu_bdry x₀ ⟨hx₀_S.1, hx₀_not⟩
      linarith [hx₀_S.2]
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀_Ω
    obtain ⟨F, hF_holo, hF_re⟩ := hu_local x₀ r hr hball
    have hF_const : ∃ c : ℂ, ∀ w ∈ ball x₀ r, F w = c := by
      by_contra hnonconst
      have hopen_img : IsOpen (F '' ball x₀ r) :=
        (RudinRCA.Chapter10.theorem10_32
          (RudinRCA.Chapter10.disc_isRegion x₀ hr) hF_holo hnonconst).1.1
          (ball x₀ r) Set.Subset.rfl isOpen_ball
      have hFx₀_mem : F x₀ ∈ F '' ball x₀ r := ⟨x₀, mem_ball_self hr, rfl⟩
      obtain ⟨ε, hε, hε_sub⟩ := Metric.isOpen_iff.mp hopen_img (F x₀) hFx₀_mem
      have hpt_mem : F x₀ + ((ε / 2 : ℝ) : ℂ) ∈ ball (F x₀) ε := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
        linarith
      rcases hε_sub hpt_mem with ⟨w, hw_ball, hw_eq⟩
      have hu_le : u w ≤ M := hz_max (hsub (hball hw_ball))
      have hu_eq : u w = M + ε / 2 := by
        rw [hF_re w hw_ball, hw_eq, Complex.add_re, Complex.ofReal_re,
          ← hF_re x₀ (mem_ball_self hr), hx₀_S.2]
      linarith
    obtain ⟨c, hc⟩ := hF_const
    let w₁ : ℂ := x₀ + ((r / 2 : ℝ) : ℂ)
    have hw₁_ball : w₁ ∈ ball x₀ r := by
      dsimp [w₁]
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      linarith
    have hw₁_S : w₁ ∈ S := by
      refine ⟨hsub (hball hw₁_ball), ?_⟩
      rw [hF_re w₁ hw₁_ball, hc w₁ hw₁_ball, ← hc x₀ (mem_ball_self hr),
        ← hF_re x₀ (mem_ball_self hr), hx₀_S.2]
    have hre_le : w₁.re ≤ x₀.re := hx₀_max hw₁_S
    have hre_w₁ : w₁.re = x₀.re + r / 2 := by simp [w₁]
    linarith

/-- **Theorem 14.22 (Conformal classification of annuli by radius ratio, RCA pp. 292–293):**
For `0 < r₁ < R₁` and `0 < r₂ < R₂`, `annulus r₁ R₁` and `annulus r₂ R₂` are conformally
equivalent if and only if `R₁ / r₁ = R₂ / r₂`. -/
theorem theorem14_22 {r₁ R₁ r₂ R₂ : ℝ}
    (hr₁ : 0 < r₁) (hR₁ : r₁ < R₁) (hr₂ : 0 < r₂) (hR₂ : r₂ < R₂) :
    ConformallyEquivalent (annulus r₁ R₁) (annulus r₂ R₂) ↔ R₁ / r₁ = R₂ / r₂ := by
  refine ⟨?_, theorem14_21.2.2 hr₁ hR₁ hr₂ hR₂⟩
  intro hconf
  -- Step 1: Normalize inner radii to `1`
  let Q₁ : ℝ := R₁ / r₁
  let Q₂ : ℝ := R₂ / r₂
  have hQ₁ : 1 < Q₁ := (one_lt_div hr₁).mpr hR₁
  have hQ₂ : 1 < Q₂ := (one_lt_div hr₂).mpr hR₂
  have hQ₂_pos : 0 < Q₂ := lt_trans zero_lt_one hQ₂
  have h1_to_r1 : ConformallyEquivalent (annulus 1 Q₁) (annulus r₁ R₁) :=
    theorem14_21.2.2 zero_lt_one hQ₁ hr₁ hR₁ (by dsimp [Q₁]; ring)
  have hr2_to_1 : ConformallyEquivalent (annulus r₂ R₂) (annulus 1 Q₂) :=
    theorem14_21.2.2 hr₂ hR₂ zero_lt_one hQ₂ (by dsimp [Q₂]; ring)
  obtain ⟨φ₀, hφ₀_holo, hφ₀_bij⟩ :=
    conformallyEquivalent_trans h1_to_r1 (conformallyEquivalent_trans hconf hr2_to_1)
  -- Helper: any holomorphic bijection `g : annulus 1 Q₁ → annulus 1 Q₂` sends thin boundary collars into boundary collars
  have hcollar : ∀ (g : ℂ → ℂ), RudinRCA.Chapter10.HolomorphicOn g (annulus 1 Q₁) →
      BijOn g (annulus 1 Q₁) (annulus 1 Q₂) →
      ∀ δ : ℝ, 0 < δ → 1 + δ < Q₂ - δ →
      ∃ η : ℝ, 0 < η ∧ η ≤ (Q₁ - 1) / 3 ∧
        ((∀ z ∈ annulus 1 (1 + η), ‖g z‖ < 1 + δ) ∨
          (∀ z ∈ annulus 1 (1 + η), Q₂ - δ < ‖g z‖)) ∧
        ((∀ z ∈ annulus (Q₁ - η) Q₁, ‖g z‖ < 1 + δ) ∨
          (∀ z ∈ annulus (Q₁ - η) Q₁, Q₂ - δ < ‖g z‖)) := by
    intro g hg_holo hg_bij δ hδ hδ_mid
    obtain ⟨ψ, hψ_holo, hleft, hright, _⟩ :=
      (RudinRCA.Chapter10.theorem10_33.1 (annulus_isOpen 1 Q₁) hg_holo hg_bij.injOn).2.2
    rw [hg_bij.image_eq] at hψ_holo hright
    have hψ_cont : ContinuousOn ψ (annulus 1 Q₂) :=
      RudinRCA.Chapter10.continuousOn_of_holomorphicOn hψ_holo
    let L : Set ℂ := closedBall (0 : ℂ) (Q₂ - δ) \ ball (0 : ℂ) (1 + δ)
    have hL_sub : L ⊆ annulus 1 Q₂ := by
      intro w ⟨hw_hi, hw_lo⟩
      have hhi : ‖w‖ ≤ Q₂ - δ := by simpa [Metric.mem_closedBall, dist_zero_right] using hw_hi
      have hlo : 1 + δ ≤ ‖w‖ := by
        have : ¬ ‖w‖ < 1 + δ := by simpa [Metric.mem_ball, dist_zero_right] using hw_lo
        exact le_of_not_gt this
      exact ⟨by linarith, by linarith⟩
    have hL_compact : IsCompact L := (isCompact_closedBall 0 (Q₂ - δ)).diff isOpen_ball
    have hL_ne : L.Nonempty := by
      refine ⟨Complex.ofReal (1 + δ), ?_, ?_⟩
      · simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real]
        rw [Real.norm_of_nonneg (by positivity)]
        linarith
      · simp only [Metric.mem_ball, dist_zero_right, Complex.norm_real]
        rw [Real.norm_of_nonneg (by positivity)]
        exact lt_irrefl _
    let M : Set ℂ := ψ '' L
    have hM_compact : IsCompact M := hL_compact.image_of_continuousOn (hψ_cont.mono hL_sub)
    have hM_ne : M.Nonempty := hL_ne.image ψ
    have hM_sub : M ⊆ annulus 1 Q₁ := by
      rintro _ ⟨w, hwL, rfl⟩
      exact (hright w (hL_sub hwL)).1
    obtain ⟨z₁, hz₁M, hz₁_min⟩ := hM_compact.exists_isMinOn hM_ne
      (continuous_norm.sub continuous_const).continuousOn
    obtain ⟨z₂, hz₂M, hz₂_min⟩ := hM_compact.exists_isMinOn hM_ne
      (continuous_const.sub continuous_norm).continuousOn
    let η : ℝ := min ((Q₁ - 1) / 3) (min ((‖z₁‖ - 1) / 2) ((Q₁ - ‖z₂‖) / 2))
    have hz₁_gt : 1 < ‖z₁‖ := (hM_sub hz₁M).1
    have hz₂_lt : ‖z₂‖ < Q₁ := (hM_sub hz₂M).2
    have hη_pos : 0 < η := by
      dsimp [η]
      refine lt_min (by linarith) (lt_min (by linarith) (by linarith))
    have hη_le : η ≤ (Q₁ - 1) / 3 := min_le_left _ _
    have hgap : ∀ z ∈ annulus 1 Q₁, (‖z‖ < 1 + η ∨ Q₁ - η < ‖z‖) →
        ‖g z‖ < 1 + δ ∨ Q₂ - δ < ‖g z‖ := by
      intro z hz hside
      by_contra hnot_or
      push Not at hnot_or
      have hgz_L : g z ∈ L := by
        refine ⟨?_, ?_⟩
        · simpa [Metric.mem_closedBall, dist_zero_right] using hnot_or.2
        · simpa [Metric.mem_ball, dist_zero_right] using hnot_or.1
      have hz_M : z ∈ M := ⟨g z, hgz_L, hleft z hz⟩
      have h1 : ‖z₁‖ - 1 ≤ ‖z‖ - 1 := hz₁_min hz_M
      have h2 : Q₁ - ‖z₂‖ ≤ Q₁ - ‖z‖ := hz₂_min hz_M
      have hη1 : η ≤ (‖z₁‖ - 1) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
      have hη2 : η ≤ (Q₁ - ‖z₂‖) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
      rcases hside with hlo | hhi <;> linarith
    have hdichot : ∀ {a b : ℝ}, 0 < a → a < b → annulus a b ⊆ annulus 1 Q₁ →
        (∀ z ∈ annulus a b, ‖g z‖ < 1 + δ ∨ Q₂ - δ < ‖g z‖) →
        (∀ z ∈ annulus a b, ‖g z‖ < 1 + δ) ∨ (∀ z ∈ annulus a b, Q₂ - δ < ‖g z‖) := by
      intro a b ha hab hsub hside_ab
      by_contra hboth
      push Not at hboth
      rcases hboth with ⟨⟨u₁, hu₁_ab, hu₁_ge⟩, ⟨u₂, hu₂_ab, hu₂_le⟩⟩
      have hu₁_gt : Q₂ - δ < ‖g u₁‖ := (hside_ab u₁ hu₁_ab).resolve_left (not_lt.mpr hu₁_ge)
      have hu₂_lt : ‖g u₂‖ < 1 + δ := (hside_ab u₂ hu₂_ab).resolve_right (not_lt.mpr hu₂_le)
      have hg_cont_ab : ContinuousOn (fun z => ‖g z‖) (annulus a b) :=
        continuous_norm.comp_continuousOn
          ((RudinRCA.Chapter10.continuousOn_of_holomorphicOn hg_holo).mono hsub)
      have himg_pre : IsPreconnected ((fun z => ‖g z‖) '' annulus a b) :=
        (annulus_isRegion ha.le hab).2.isPreconnected.image _ hg_cont_ab
      obtain ⟨t, _, ht₁, ht₂⟩ := himg_pre {t : ℝ | t < 1 + δ} {t : ℝ | Q₂ - δ < t}
        (isOpen_lt continuous_id continuous_const) (isOpen_lt continuous_const continuous_id)
        (by rintro _ ⟨z, hz, rfl⟩; exact hside_ab z hz)
        ⟨‖g u₂‖, ⟨u₂, hu₂_ab, rfl⟩, hu₂_lt⟩
        ⟨‖g u₁‖, ⟨u₁, hu₁_ab, rfl⟩, hu₁_gt⟩
      dsimp at ht₁ ht₂
      linarith
    refine ⟨η, hη_pos, hη_le, ?_, ?_⟩
    · refine hdichot zero_lt_one (by linarith)
        (fun z hz => ⟨hz.1, by linarith [hz.2]⟩)
        (fun z hz => hgap z ⟨hz.1, by linarith [hz.2]⟩ (Or.inl hz.2))
    · refine hdichot (by linarith) (by linarith)
        (fun z hz => ⟨by linarith [hz.1], hz.2⟩)
        (fun z hz => hgap z ⟨by linarith [hz.1], hz.2⟩ (Or.inr hz.1))
  -- Step 2: Post-compose with `w ↦ Q₂ / w` if needed so inner boundary maps to inner boundary
  let δ₀ : ℝ := (Q₂ - 1) / 3
  have hδ₀_pos : 0 < δ₀ := by dsimp [δ₀]; linarith
  have hδ₀_mid : 1 + δ₀ < Q₂ - δ₀ := by dsimp [δ₀]; linarith
  obtain ⟨η₀, hη₀_pos, hη₀_le, hφ₀_in, _⟩ := hcollar φ₀ hφ₀_holo hφ₀_bij δ₀ hδ₀_pos hδ₀_mid
  have hex_norm : ∃ φ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn φ (annulus 1 Q₁) ∧
      BijOn φ (annulus 1 Q₁) (annulus 1 Q₂) ∧
      (∀ z ∈ annulus 1 (1 + η₀), ‖φ z‖ < 1 + δ₀) := by
    rcases hφ₀_in with hlo | hhi
    · exact ⟨φ₀, hφ₀_holo, hφ₀_bij, hlo⟩
    · let invA : ℂ → ℂ := fun w => (Q₂ : ℂ) / w
      have hinvA_holo : RudinRCA.Chapter10.HolomorphicOn invA (annulus 1 Q₂) := by
        intro w hw
        have hw_ne : w ≠ 0 := by
          intro h0; subst h0; have := hw.1; simp at this; linarith
        exact (differentiableAt_const (Q₂ : ℂ)).div differentiableAt_id hw_ne
      have hinvA_bij : BijOn invA (annulus 1 Q₂) (annulus 1 Q₂) := by
        refine ⟨?_, ?_, ?_⟩
        · intro w hw
          have hw_pos : 0 < ‖w‖ := lt_trans zero_lt_one hw.1
          simp only [invA, annulus, Set.mem_setOf_eq, norm_div, Complex.norm_real,
            Real.norm_of_nonneg hQ₂_pos.le]
          exact ⟨(one_lt_div hw_pos).mpr hw.2,
            (div_lt_iff₀ hw_pos).mpr (by nlinarith [hw.1])⟩
        · intro w₁ hw₁ w₂ hw₂ heq
          have hw₁_ne : w₁ ≠ 0 := by
            intro h0; subst h0; have := hw₁.1; simp at this; linarith
          have hw₂_ne : w₂ ≠ 0 := by
            intro h0; subst h0; have := hw₂.1; simp at this; linarith
          have hQ₂_ne : (Q₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ₂_pos.ne'
          dsimp [invA] at heq
          rw [div_eq_div_iff hw₁_ne hw₂_ne] at heq
          exact mul_left_cancel₀ hQ₂_ne heq.symm
        · intro w hw
          have hw_pos : 0 < ‖w‖ := lt_trans zero_lt_one hw.1
          have hw_ne : w ≠ 0 := norm_ne_zero_iff.mp hw_pos.ne'
          have hQ₂_ne : (Q₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ₂_pos.ne'
          have hmem : invA w ∈ annulus 1 Q₂ := by
            simp only [invA, annulus, Set.mem_setOf_eq, norm_div, Complex.norm_real,
              Real.norm_of_nonneg hQ₂_pos.le]
            exact ⟨(one_lt_div hw_pos).mpr hw.2,
              (div_lt_iff₀ hw_pos).mpr (by nlinarith [hw.1])⟩
          refine ⟨invA w, hmem, ?_⟩
          dsimp [invA]
          field_simp [hw_ne, hQ₂_ne]
      refine ⟨invA ∘ φ₀,
        fun z hz => (hinvA_holo _ (hφ₀_bij.mapsTo hz)).comp z (hφ₀_holo z hz),
        hinvA_bij.comp hφ₀_bij, ?_⟩
      intro z hz
      have hgt : Q₂ - δ₀ < ‖φ₀ z‖ := hhi z hz
      have hpos_den : 0 < Q₂ - δ₀ := by dsimp [δ₀]; linarith
      have hpos_φ : 0 < ‖φ₀ z‖ := lt_trans hpos_den hgt
      simp only [Function.comp_apply, invA, norm_div, Complex.norm_real,
        Real.norm_of_nonneg hQ₂_pos.le]
      rw [div_lt_iff₀ hpos_φ]
      have hprod : Q₂ < (1 + δ₀) * (Q₂ - δ₀) := by
        dsimp [δ₀]
        nlinarith [sq_pos_of_pos (sub_pos.mpr hQ₂)]
      nlinarith
  obtain ⟨φ, hφ_holo, hφ_bij, hφ_in₀⟩ := hex_norm
  have hφ_cont : ContinuousOn φ (annulus 1 Q₁) :=
    RudinRCA.Chapter10.continuousOn_of_holomorphicOn hφ_holo
  -- Outer collar of `φ` cannot also go to the inner collar by surjectivity onto `annulus 1 Q₂`
  obtain ⟨η₁, hη₁_pos, hη₁_le, _, hφ_out₁_or⟩ := hcollar φ hφ_holo hφ_bij δ₀ hδ₀_pos hδ₀_mid
  let η_star : ℝ := min η₀ η₁
  have hη_star_pos : 0 < η_star := lt_min hη₀_pos hη₁_pos
  have hη_star_le : η_star ≤ (Q₁ - 1) / 3 := le_trans (min_le_left _ _) hη₀_le
  have hφ_out₀ : ∀ z ∈ annulus (Q₁ - η_star) Q₁, Q₂ - δ₀ < ‖φ z‖ := by
    rcases hφ_out₁_or with hall_lo | hall_hi
    · exfalso
      let Core : Set ℂ := closedBall (0 : ℂ) (Q₁ - η_star) \ ball (0 : ℂ) (1 + η_star)
      have hCore_sub : Core ⊆ annulus 1 Q₁ := by
        intro z ⟨hhi, hlo⟩
        have h1 : ‖z‖ ≤ Q₁ - η_star := by simpa [Metric.mem_closedBall, dist_zero_right] using hhi
        have h2 : 1 + η_star ≤ ‖z‖ :=
          le_of_not_gt (by simpa [Metric.mem_ball, dist_zero_right] using hlo)
        exact ⟨by linarith, by linarith⟩
      have hCore_comp : IsCompact Core :=
        (isCompact_closedBall 0 (Q₁ - η_star)).diff isOpen_ball
      have hCore_ne : Core.Nonempty := by
        refine ⟨Complex.ofReal (1 + η_star), ?_, ?_⟩
        · simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real]
          rw [Real.norm_of_nonneg (by positivity)]
          linarith
        · simp only [Metric.mem_ball, dist_zero_right, Complex.norm_real]
          rw [Real.norm_of_nonneg (by positivity)]
          exact lt_irrefl _
      obtain ⟨zM, hzM_core, hzM_max⟩ := hCore_comp.exists_isMaxOn hCore_ne
        (continuous_norm.comp_continuousOn (hφ_cont.mono hCore_sub))
      let B : ℝ := max (1 + δ₀) ‖φ zM‖
      have hB_lt : B < Q₂ := max_lt (by dsimp [δ₀]; linarith) (hφ_bij.mapsTo (hCore_sub hzM_core)).2
      have hB_gt1 : 1 < B := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      let w_bad : ℂ := Complex.ofReal ((B + Q₂) / 2)
      have hw_bad : w_bad ∈ annulus 1 Q₂ := by
        simp only [w_bad, annulus, Set.mem_setOf_eq, Complex.norm_real]
        rw [Real.norm_of_nonneg (by positivity)]
        exact ⟨by linarith, by linarith⟩
      rcases hφ_bij.surjOn hw_bad with ⟨z, hz_ann, hz_eq⟩
      have hz_bound : ‖φ z‖ ≤ B := by
        by_cases h1 : ‖z‖ < 1 + η_star
        · have : ‖z‖ < 1 + η₀ := lt_of_lt_of_le h1 (by linarith [min_le_left η₀ η₁])
          exact le_trans (hφ_in₀ z ⟨hz_ann.1, this⟩).le (le_max_left _ _)
        · by_cases h2 : Q₁ - η_star < ‖z‖
          · have : Q₁ - η₁ < ‖z‖ := lt_of_le_of_lt (by linarith [min_le_right η₀ η₁]) h2
            exact le_trans (hall_lo z ⟨this, hz_ann.2⟩).le (le_max_left _ _)
          · have hz_core : z ∈ Core := by
              refine ⟨?_, ?_⟩
              · simpa [Metric.mem_closedBall, dist_zero_right] using le_of_not_gt h2
              · simpa [Metric.mem_ball, dist_zero_right] using h1
            exact le_trans (hzM_max hz_core) (le_max_right _ _)
      have hw_norm : ‖w_bad‖ = (B + Q₂) / 2 := by
        simp only [w_bad, Complex.norm_real]
        exact Real.norm_of_nonneg (by positivity)
      rw [hz_eq, hw_norm] at hz_bound
      linarith
    · intro z hz
      exact hall_hi z ⟨lt_of_le_of_lt (by linarith [min_le_right η₀ η₁]) hz.1, hz.2⟩
  -- Upgrade to arbitrary `δ ∈ (0, δ₀]`
  have hφ_bdry : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ η : ℝ, 0 < η ∧
        (∀ z ∈ annulus 1 Q₁, ‖z‖ < 1 + η → ‖φ z‖ < 1 + δ) ∧
        (∀ z ∈ annulus 1 Q₁, Q₁ - η < ‖z‖ → Q₂ - δ < ‖φ z‖) := by
    intro δ hδ hδ_le
    obtain ⟨η_d, hηd_pos, _, hin_or, hout_or⟩ :=
      hcollar φ hφ_holo hφ_bij δ hδ (by linarith)
    let η : ℝ := min η_star η_d
    have hη_pos : 0 < η := lt_min hη_star_pos hηd_pos
    refine ⟨η, hη_pos, ?_, ?_⟩
    · rcases hin_or with hlo | hhi
      · intro z hz hz_lt
        exact hlo z ⟨hz.1, lt_of_lt_of_le hz_lt (by linarith [min_le_right η_star η_d])⟩
      · exfalso
        let z_test : ℂ := Complex.ofReal (1 + η / 2)
        have hz_norm : ‖z_test‖ = 1 + η / 2 := by
          simp only [z_test, Complex.norm_real]
          exact Real.norm_of_nonneg (by positivity)
        have h1 : ‖φ z_test‖ < 1 + δ₀ := by
          apply hφ_in₀ z_test
          refine ⟨by rw [hz_norm]; linarith, ?_⟩
          rw [hz_norm]
          have : η ≤ η₀ := le_trans (min_le_left _ _) (min_le_left _ _)
          linarith
        have h2 : Q₂ - δ < ‖φ z_test‖ := by
          apply hhi z_test
          refine ⟨by rw [hz_norm]; linarith, ?_⟩
          rw [hz_norm]
          have : η ≤ η_d := min_le_right _ _
          linarith
        linarith
    · rcases hout_or with hlo | hhi
      · exfalso
        let z_test : ℂ := Complex.ofReal (Q₁ - η / 2)
        have hpos_t : 0 < Q₁ - η / 2 := by
          have : η ≤ (Q₁ - 1) / 3 := le_trans (min_le_left _ _) hη_star_le
          linarith
        have hz_norm : ‖z_test‖ = Q₁ - η / 2 := by
          simp only [z_test, Complex.norm_real]
          exact Real.norm_of_nonneg hpos_t.le
        have h1 : Q₂ - δ₀ < ‖φ z_test‖ := by
          apply hφ_out₀ z_test
          refine ⟨?_, by rw [hz_norm]; linarith⟩
          rw [hz_norm]
          have : η ≤ η_star := min_le_left _ _
          linarith
        have h2 : ‖φ z_test‖ < 1 + δ := by
          apply hlo z_test
          refine ⟨?_, by rw [hz_norm]; linarith⟩
          rw [hz_norm]
          have : η ≤ η_d := min_le_right _ _
          linarith
        linarith
      · intro z hz hz_gt
        exact hhi z ⟨lt_of_le_of_lt (by linarith [min_le_right η_star η_d]) hz_gt, hz.2⟩
  -- Step 3: Harmonic difference `u(z) = log ‖φ(z)‖ - α log ‖z‖` vanishes on `annulus 1 Q₁`
  have hlogQ₁_pos : 0 < Real.log Q₁ := Real.log_pos hQ₁
  have hlogQ₂_pos : 0 < Real.log Q₂ := Real.log_pos hQ₂
  let α : ℝ := Real.log Q₂ / Real.log Q₁
  have hα_pos : 0 < α := div_pos hlogQ₂_pos hlogQ₁_pos
  let K : Set ℂ := closedBall (0 : ℂ) Q₁ \ ball (0 : ℂ) 1
  have hK_compact : IsCompact K := (isCompact_closedBall 0 Q₁).diff isOpen_ball
  have hK_ne : K.Nonempty := by
    refine ⟨(1 : ℂ), ?_, ?_⟩
    · simp [Metric.mem_closedBall, dist_zero_right, hQ₁.le]
    · simp [Metric.mem_ball, dist_zero_right]
  have hann_sub_K : annulus 1 Q₁ ⊆ K := by
    intro z hz
    refine ⟨?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_zero_right] using hz.2.le
    · simpa [Metric.mem_ball, dist_zero_right] using not_lt.mpr hz.1.le
  classical
  let u : ℂ → ℝ := fun z =>
    if z ∈ annulus 1 Q₁ then Real.log ‖φ z‖ - α * Real.log ‖z‖ else 0
  have hu_cont : ContinuousOn u K := by
    intro z₀ hz₀
    have hz₀_lo : 1 ≤ ‖z₀‖ :=
      le_of_not_gt (by simpa [Metric.mem_ball, dist_zero_right] using hz₀.2)
    have hz₀_hi : ‖z₀‖ ≤ Q₁ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz₀.1
    by_cases hz₀_ann : z₀ ∈ annulus 1 Q₁
    · have hφz₀_ne : ‖φ z₀‖ ≠ 0 := (lt_trans zero_lt_one (hφ_bij.mapsTo hz₀_ann).1).ne'
      have hz₀_ne : ‖z₀‖ ≠ 0 := (lt_trans zero_lt_one hz₀_ann.1).ne'
      have hφ_cat : ContinuousAt φ z₀ :=
        (hφ_cont z₀ hz₀_ann).continuousAt ((annulus_isOpen 1 Q₁).mem_nhds hz₀_ann)
      have hcat : ContinuousAt (fun z : ℂ => Real.log ‖φ z‖ - α * Real.log ‖z‖) z₀ :=
        (ContinuousAt.comp (f := fun z : ℂ => ‖φ z‖) (Real.continuousAt_log hφz₀_ne) hφ_cat.norm).sub
          (continuousAt_const.mul ((Real.continuousAt_log hz₀_ne).comp continuousAt_id.norm))
      have hev : u =ᶠ[𝓝 z₀] (fun z => Real.log ‖φ z‖ - α * Real.log ‖z‖) := by
        filter_upwards [(annulus_isOpen 1 Q₁).mem_nhds hz₀_ann] with z hz
        simp [u, hz]
      exact (hcat.congr hev.symm).continuousWithinAt
    · have huz₀ : u z₀ = 0 := by simp [u, hz₀_ann]
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      have hb_cases : ‖z₀‖ = 1 ∨ ‖z₀‖ = Q₁ := by
        by_contra hneither
        push Not at hneither
        exact hz₀_ann ⟨lt_of_le_of_ne hz₀_lo (Ne.symm hneither.1),
          lt_of_le_of_ne hz₀_hi hneither.2⟩
      rcases hb_cases with hnorm1 | hnormQ₁
      · obtain ⟨δ₁, hδ₁_pos, hδ₁_log⟩ :=
          Metric.continuousAt_iff.mp (Real.continuousAt_log one_ne_zero) (ε / 2) (half_pos hε)
        let δ : ℝ := min δ₀ δ₁
        obtain ⟨η, hη_pos, hη_in, _⟩ := hφ_bdry δ (lt_min hδ₀_pos hδ₁_pos) (min_le_left _ _)
        have hcont_term2 : ContinuousAt (fun z : ℂ => α * Real.log ‖z‖) z₀ :=
          continuousAt_const.mul
            ((Real.continuousAt_log (by rw [hnorm1]; exact one_ne_zero)).comp
              continuousAt_id.norm)
        obtain ⟨η₂, hη₂_pos, hη₂⟩ :=
          Metric.continuousAt_iff.mp hcont_term2 (ε / 2) (half_pos hε)
        refine ⟨min η η₂, lt_min hη_pos hη₂_pos, ?_⟩
        intro z hzK hdist
        rw [huz₀, Real.dist_eq, sub_zero]
        by_cases hz_ann : z ∈ annulus 1 Q₁
        · simp only [u, hz_ann, ↓reduceIte]
          have hnorm_lt : ‖z‖ < 1 + η := by
            have htri : ‖z‖ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_le_insert' z z₀
            have hd1 : dist z z₀ < η := lt_of_lt_of_le hdist (min_le_left _ _)
            rw [← dist_eq_norm, hnorm1] at htri
            linarith
          have hφ_lt : ‖φ z‖ < 1 + δ := hη_in z hz_ann hnorm_lt
          have hφ_gt : 1 < ‖φ z‖ := (hφ_bij.mapsTo hz_ann).1
          have hdist_φ : dist ‖φ z‖ 1 < δ₁ := by
            rw [Real.dist_eq, abs_of_pos (by linarith)]
            exact lt_of_lt_of_le (by linarith) (min_le_right δ₀ δ₁)
          have hlog1 := hδ₁_log hdist_φ
          rw [Real.log_one, Real.dist_eq, sub_zero] at hlog1
          have hlog2 := hη₂ (lt_of_lt_of_le hdist (min_le_right _ _))
          rw [hnorm1, Real.log_one, mul_zero, Real.dist_eq, sub_zero] at hlog2
          have htri_abs := abs_sub (Real.log ‖φ z‖) (α * Real.log ‖z‖)
          linarith
        · simp [u, hz_ann, hε]
      · obtain ⟨δ₁, hδ₁_pos, hδ₁_log⟩ :=
          Metric.continuousAt_iff.mp (Real.continuousAt_log hQ₂_pos.ne') (ε / 2) (half_pos hε)
        let δ : ℝ := min δ₀ δ₁
        obtain ⟨η, hη_pos, _, hη_out⟩ := hφ_bdry δ (lt_min hδ₀_pos hδ₁_pos) (min_le_left _ _)
        have hQ₁_pos : 0 < Q₁ := lt_trans zero_lt_one hQ₁
        have hcont_term2 : ContinuousAt (fun z : ℂ => α * Real.log ‖z‖) z₀ :=
          continuousAt_const.mul
            ((Real.continuousAt_log (by rw [hnormQ₁]; exact hQ₁_pos.ne')).comp
              continuousAt_id.norm)
        obtain ⟨η₂, hη₂_pos, hη₂⟩ :=
          Metric.continuousAt_iff.mp hcont_term2 (ε / 2) (half_pos hε)
        refine ⟨min η η₂, lt_min hη_pos hη₂_pos, ?_⟩
        intro z hzK hdist
        rw [huz₀, Real.dist_eq, sub_zero]
        by_cases hz_ann : z ∈ annulus 1 Q₁
        · simp only [u, hz_ann, ↓reduceIte]
          have hnorm_gt : Q₁ - η < ‖z‖ := by
            have htri : ‖z₀‖ ≤ ‖z‖ + ‖z₀ - z‖ := norm_le_insert' z₀ z
            have hd1 : dist z z₀ < η := lt_of_lt_of_le hdist (min_le_left _ _)
            rw [← dist_eq_norm, dist_comm, hnormQ₁] at htri
            linarith
          have hφ_gt : Q₂ - δ < ‖φ z‖ := hη_out z hz_ann hnorm_gt
          have hφ_lt : ‖φ z‖ < Q₂ := (hφ_bij.mapsTo hz_ann).2
          have hdist_φ : dist ‖φ z‖ Q₂ < δ₁ := by
            rw [Real.dist_eq, abs_of_neg (by linarith)]
            linarith [min_le_right δ₀ δ₁]
          have hlog1 := hδ₁_log hdist_φ
          rw [Real.dist_eq] at hlog1
          have hlog2 := hη₂ (lt_of_lt_of_le hdist (min_le_right _ _))
          have hαQ₁ : α * Real.log ‖z₀‖ = Real.log Q₂ := by
            dsimp [α]
            rw [hnormQ₁, div_mul_cancel₀ _ hlogQ₁_pos.ne']
          rw [hαQ₁, Real.dist_eq] at hlog2
          have hrewrite : Real.log ‖φ z‖ - α * Real.log ‖z‖ =
              (Real.log ‖φ z‖ - Real.log Q₂) - (α * Real.log ‖z‖ - Real.log Q₂) := by ring
          rw [hrewrite]
          have htri_abs := abs_sub (Real.log ‖φ z‖ - Real.log Q₂) (α * Real.log ‖z‖ - Real.log Q₂)
          linarith
        · simp [u, hz_ann, hε]
  have hφ_nz : ∀ z ∈ annulus 1 Q₁, φ z ≠ 0 := by
    intro z hz
    exact norm_ne_zero_iff.mp (lt_trans zero_lt_one (hφ_bij.mapsTo hz).1).ne'
  have hid_nz : ∀ z ∈ annulus 1 Q₁, z ≠ 0 := by
    intro z hz
    exact norm_ne_zero_iff.mp (lt_trans zero_lt_one hz.1).ne'
  have hu_local : ∀ x₀ : ℂ, ∀ r > 0, ball x₀ r ⊆ annulus 1 Q₁ →
      ∃ F : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn F (ball x₀ r) ∧
        ∀ w ∈ ball x₀ r, u w = (F w).re := by
    intro x₀ r hr hball
    obtain ⟨L₁, hL₁_holo, _, hL₁_re⟩ :=
      (RudinRCA.Chapter13.theorem13_12 (annulus_isOpen 1 Q₁) hφ_holo hφ_nz).1 x₀ r hr hball
    obtain ⟨L₂, hL₂_holo, _, hL₂_re⟩ :=
      (RudinRCA.Chapter13.theorem13_12 (annulus_isOpen 1 Q₁)
        (fun _ _ => differentiableAt_id) hid_nz).1 x₀ r hr hball
    dsimp only [id_eq] at hL₂_re
    refine ⟨fun w => L₁ w - (α : ℂ) * L₂ w,
      fun w hw => (hL₁_holo w hw).sub ((hL₂_holo w hw).const_mul (α : ℂ)), ?_⟩
    intro w hw
    simp only [u, hball hw, ↓reduceIte, hL₁_re w hw, hL₂_re w hw, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hu_le0 : ∀ z ∈ annulus 1 Q₁, u z ≤ 0 :=
    localRe_nonpos_of_compact_bdry (annulus_isOpen 1 Q₁) hK_compact hK_ne hann_sub_K hu_cont
      hu_local (fun z hz => by simp [u, hz.2])
  have hneg_u_le0 : ∀ z ∈ annulus 1 Q₁, -u z ≤ 0 :=
    localRe_nonpos_of_compact_bdry (annulus_isOpen 1 Q₁) hK_compact hK_ne hann_sub_K hu_cont.neg
      (fun x₀ r hr hball => by
        obtain ⟨F, hF_holo, hF_re⟩ := hu_local x₀ r hr hball
        exact ⟨fun w => -F w, fun w hw => (hF_holo w hw).neg,
          fun w hw => by rw [hF_re w hw, Complex.neg_re]⟩)
      (fun z hz => by simp [u, hz.2])
  have hu_eq0 : ∀ z ∈ annulus 1 Q₁, Real.log ‖φ z‖ = α * Real.log ‖z‖ := by
    intro z hz
    have h1 := hu_le0 z hz
    have h2 := hneg_u_le0 z hz
    simp only [u, hz, ↓reduceIte] at h1 h2
    linarith
  -- Step 4: Differentiate on a subdisc and propagate `z * deriv φ z = α * φ z` across `annulus 1 Q₁`
  let r₀ : ℝ := (1 + Q₁) / 2
  let δ₁ : ℝ := (Q₁ - 1) / 4
  have hr₀_pos : 0 < r₀ := by dsimp [r₀]; linarith
  have hδ₁_pos : 0 < δ₁ := by dsimp [δ₁]; linarith
  let z_mid : ℂ := (r₀ : ℂ)
  have hball_mid : ball z_mid δ₁ ⊆ annulus 1 Q₁ := by
    intro z hz
    have hdist : ‖z - z_mid‖ < δ₁ := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hz_mid_norm : ‖z_mid‖ = r₀ := by
      simp [z_mid, Complex.norm_real, Real.norm_of_nonneg hr₀_pos.le]
    have htri1 : ‖z_mid‖ ≤ ‖z‖ + ‖z_mid - z‖ := norm_le_insert' z_mid z
    have htri2 : ‖z‖ ≤ ‖z_mid‖ + ‖z - z_mid‖ := norm_le_insert' z z_mid
    rw [norm_sub_rev] at htri1
    rw [hz_mid_norm] at htri1 htri2
    dsimp [r₀, δ₁] at hdist htri1 htri2
    exact ⟨by linarith, by linarith⟩
  obtain ⟨L₁, hL₁_holo, hL₁_exp, hL₁_re⟩ :=
    (RudinRCA.Chapter13.theorem13_12 (annulus_isOpen 1 Q₁) hφ_holo hφ_nz).1
      z_mid δ₁ hδ₁_pos hball_mid
  obtain ⟨L₂, hL₂_holo, hL₂_exp, hL₂_re⟩ :=
    (RudinRCA.Chapter13.theorem13_12 (annulus_isOpen 1 Q₁)
      (fun _ _ => differentiableAt_id) hid_nz).1 z_mid δ₁ hδ₁_pos hball_mid
  dsimp only [id_eq] at hL₂_exp hL₂_re
  let F_mid : ℂ → ℂ := fun z => L₁ z - (α : ℂ) * L₂ z
  have hF_mid_holo : RudinRCA.Chapter10.HolomorphicOn F_mid (ball z_mid δ₁) :=
    fun z hz => (hL₁_holo z hz).sub ((hL₂_holo z hz).const_mul (α : ℂ))
  have hF_mid_re0 : ∀ z ∈ ball z_mid δ₁, (F_mid z).re = 0 := by
    intro z hz
    dsimp [F_mid]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, ← hL₁_re z hz, ← hL₂_re z hz, hu_eq0 z (hball_mid hz), sub_self]
  have hF_mid_const : ∃ c : ℂ, ∀ z ∈ ball z_mid δ₁, F_mid z = c := by
    by_contra hnonconst
    have hopen_img : IsOpen (F_mid '' ball z_mid δ₁) :=
      (RudinRCA.Chapter10.theorem10_32
        (RudinRCA.Chapter10.disc_isRegion z_mid hδ₁_pos) hF_mid_holo hnonconst).1.1
        (ball z_mid δ₁) Set.Subset.rfl isOpen_ball
    obtain ⟨ε, hε, hε_sub⟩ := Metric.isOpen_iff.mp hopen_img (F_mid z_mid)
      ⟨z_mid, mem_ball_self hδ₁_pos, rfl⟩
    have hpt : F_mid z_mid + ((ε / 2 : ℝ) : ℂ) ∈ ball (F_mid z_mid) ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      linarith
    rcases hε_sub hpt with ⟨w, hw_ball, hw_eq⟩
    have hre1 := hF_mid_re0 w hw_ball
    rw [hw_eq, Complex.add_re, hF_mid_re0 z_mid (mem_ball_self hδ₁_pos), Complex.ofReal_re] at hre1
    linarith
  obtain ⟨c_mid, hc_mid⟩ := hF_mid_const
  let G : ℂ → ℂ := fun z => z * deriv φ z - (α : ℂ) * φ z
  have hG_holo : RudinRCA.Chapter10.HolomorphicOn G (annulus 1 Q₁) := by
    have hd_holo := RudinRCA.Chapter10.holomorphicOn_deriv (annulus_isOpen 1 Q₁) hφ_holo
    exact fun z hz => (differentiableAt_id.mul (hd_holo z hz)).sub
      ((hφ_holo z hz).const_mul (α : ℂ))
  have hG_ball0 : ∀ z ∈ ball z_mid δ₁, G z = 0 := by
    intro z hz
    have hnhds : ball z_mid δ₁ ∈ 𝓝 z := isOpen_ball.mem_nhds hz
    have hd1 : HasDerivAt φ (Complex.exp (L₁ z) * deriv L₁ z) z := by
      have h := (Complex.hasDerivAt_exp (L₁ z)).comp z (hL₁_holo z hz).hasDerivAt
      refine h.congr_of_eventuallyEq ?_
      filter_upwards [hnhds] with w hw
      exact (hL₁_exp w hw).symm
    have hd2 : HasDerivAt (fun w : ℂ => w) (Complex.exp (L₂ z) * deriv L₂ z) z := by
      have h := (Complex.hasDerivAt_exp (L₂ z)).comp z (hL₂_holo z hz).hasDerivAt
      refine h.congr_of_eventuallyEq ?_
      filter_upwards [hnhds] with w hw
      exact (hL₂_exp w hw).symm
    have hdF : HasDerivAt F_mid 0 z := by
      refine (hasDerivAt_const z c_mid).congr_of_eventuallyEq ?_
      filter_upwards [hnhds] with w hw
      exact hc_mid w hw
    have hdF' : HasDerivAt F_mid (deriv L₁ z - (α : ℂ) * deriv L₂ z) z :=
      (hL₁_holo z hz).hasDerivAt.sub ((hL₂_holo z hz).hasDerivAt.const_mul (α : ℂ))
    have hL_rel : deriv L₁ z = (α : ℂ) * deriv L₂ z :=
      sub_eq_zero.mp (hdF'.unique hdF)
    have hφ_der : deriv φ z = φ z * deriv L₁ z := by
      rw [hd1.deriv, hL₁_exp z hz]
    have hz_der : (1 : ℂ) = z * deriv L₂ z := by
      have := hd2.unique (hasDerivAt_id z)
      rw [hL₂_exp z hz] at this
      exact this.symm
    dsimp [G]
    rw [hφ_der, hL_rel]
    calc
      z * (φ z * ((α : ℂ) * deriv L₂ z)) - (α : ℂ) * φ z
          = (α : ℂ) * φ z * (z * deriv L₂ z) - (α : ℂ) * φ z := by ring
      _ = (α : ℂ) * φ z * 1 - (α : ℂ) * φ z := by rw [← hz_der]
      _ = 0 := by ring
  have hG_eq0 : ∀ z ∈ annulus 1 Q₁, z * deriv φ z = (α : ℂ) * φ z := by
    rcases RudinRCA.Chapter10.theorem10_18 (annulus_isRegion zero_le_one hQ₁) hG_holo with
        hzero_all | ⟨hno_acc, _⟩
    · intro z hz
      have hz_zero : z ∈ RudinRCA.Chapter10.zeroSet G (annulus 1 Q₁) := by
        rwa [hzero_all]
      exact sub_eq_zero.mp hz_zero.2
    · exfalso
      apply hno_acc z_mid (hball_mid (mem_ball_self hδ₁_pos))
      rw [accPt_iff_nhds]
      intro U hU
      obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
      let s : ℝ := min (r / 2) (δ₁ / 2)
      have hs_pos : 0 < s := lt_min (half_pos hr) (half_pos hδ₁_pos)
      let w : ℂ := z_mid + (s : ℂ)
      have hw_dist : dist w z_mid = s := by
        dsimp [w]
        rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hs_pos.le]
      have hw_ball : w ∈ ball z_mid δ₁ := by
        rw [Metric.mem_ball, hw_dist]
        exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hw_U : w ∈ U := hrU (by rw [Metric.mem_ball, hw_dist]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith))
      have hw_ne : w ≠ z_mid := by
        intro heq
        have : dist w z_mid = 0 := by rw [heq, dist_self]
        linarith
      exact ⟨w, ⟨hw_U, ⟨hball_mid hw_ball, hG_ball0 w hw_ball⟩⟩, hw_ne⟩
  -- Step 5: Winding-number integrality + injectivity around the circle `θ ↦ r₀ * exp(i θ)`
  let γ : ℝ → ℂ := fun θ => (r₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  have hγ_mem : ∀ θ : ℝ, γ θ ∈ annulus 1 Q₁ := by
    intro θ
    have hnorm : ‖γ θ‖ = r₀ := by
      dsimp [γ]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr₀_pos.le, Complex.norm_exp]
      simp
    dsimp [annulus]
    rw [hnorm]
    dsimp [r₀]
    exact ⟨by linarith, by linarith⟩
  let h : ℝ → ℂ := fun θ => φ (γ θ) * Complex.exp (-((α : ℂ) * (θ : ℂ) * Complex.I))
  have hh_deriv : ∀ θ : ℝ, HasDerivAt h 0 θ := by
    intro θ
    have hd_θ : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 θ := Complex.ofRealCLM.hasDerivAt
    have hd_γ : HasDerivAt γ (γ θ * Complex.I) θ := by
      have h1 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
          (Complex.exp ((θ : ℂ) * Complex.I) * (1 * Complex.I)) θ :=
        ((Complex.hasDerivAt_exp _).scomp θ (hd_θ.mul_const Complex.I)).congr_deriv
          (by simp [smul_eq_mul, mul_comm])
      have h2 := h1.const_mul (r₀ : ℂ)
      refine h2.congr_deriv ?_
      dsimp [γ]; ring
    have hd_φγ : HasDerivAt (fun t : ℝ => φ (γ t)) ((γ θ * Complex.I) * deriv φ (γ θ)) θ :=
      (hφ_holo (γ θ) (hγ_mem θ)).hasDerivAt.scomp θ hd_γ
    have hd_exp : HasDerivAt (fun t : ℝ => Complex.exp (-((α : ℂ) * (t : ℂ) * Complex.I)))
        (Complex.exp (-((α : ℂ) * (θ : ℂ) * Complex.I)) * (-((α : ℂ) * Complex.I))) θ := by
      have hlin : HasDerivAt (fun t : ℝ => -((α : ℂ) * (t : ℂ) * Complex.I))
          (-((α : ℂ) * 1 * Complex.I)) θ :=
        ((hd_θ.const_mul (α : ℂ)).mul_const Complex.I).neg
      have h1 := (Complex.hasDerivAt_exp _).scomp θ hlin
      refine h1.congr_deriv ?_
      simp [smul_eq_mul]; ring
    have hd_prod := hd_φγ.mul hd_exp
    refine hd_prod.congr_deriv ?_
    have hode := hG_eq0 (γ θ) (hγ_mem θ)
    linear_combination Complex.I * Complex.exp (-((α : ℂ) * (θ : ℂ) * Complex.I)) * hode
  have hh_const : ∀ θ : ℝ, h θ = h 0 := by
    intro θ
    exact is_const_of_deriv_eq_zero (fun t => (hh_deriv t).differentiableAt)
      (fun t => (hh_deriv t).deriv) θ 0
  have hφγ_eq : ∀ θ : ℝ, φ (γ θ) = φ (r₀ : ℂ) * Complex.exp ((α : ℂ) * (θ : ℂ) * Complex.I) := by
    intro θ
    have h0_eq : h 0 = φ (r₀ : ℂ) := by
      dsimp [h, γ]; simp
    have hθ := hh_const θ
    rw [h0_eq] at hθ
    dsimp [h] at hθ
    calc
      φ (γ θ) = φ (γ θ) * Complex.exp (-((α : ℂ) * (θ : ℂ) * Complex.I)) *
          Complex.exp ((α : ℂ) * (θ : ℂ) * Complex.I) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = φ (r₀ : ℂ) * Complex.exp ((α : ℂ) * (θ : ℂ) * Complex.I) := by rw [hθ]
  have hγ_2pi : γ (2 * Real.pi) = (r₀ : ℂ) := by
    dsimp [γ]
    rw [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.exp_two_pi_mul_I, mul_one]
  have hγ_0 : γ 0 = (r₀ : ℂ) := by dsimp [γ]; simp
  have hexp_1 : Complex.exp ((α : ℂ) * Complex.ofReal (2 * Real.pi) * Complex.I) = 1 := by
    have h2pi := hφγ_eq (2 * Real.pi)
    rw [hγ_2pi] at h2pi
    have hnz : φ (r₀ : ℂ) ≠ 0 := hφ_nz (r₀ : ℂ) (by rw [← hγ_0]; exact hγ_mem 0)
    exact mul_left_cancel₀ hnz (by rw [← h2pi, mul_one])
  obtain ⟨n, hn_eq⟩ := Complex.exp_eq_one_iff.mp hexp_1
  have h2piI_ne : (2 * Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hα_int_c : (α : ℂ) = (n : ℂ) := by
    apply mul_right_cancel₀ h2piI_ne
    have h1 : (α : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) =
        (α : ℂ) * Complex.ofReal (2 * Real.pi) * Complex.I := by push_cast; ring
    have h2 : (n : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) =
        (n : ℂ) * (2 * ↑Real.pi * Complex.I) := by ring
    rw [h1, h2, hn_eq]
  have hα_int : α = (n : ℝ) := by
    have := congr_arg Complex.re hα_int_c
    simpa using this
  have hn_pos_real : (0 : ℝ) < (n : ℝ) := by linarith [hα_pos]
  have hn_ge1 : 1 ≤ n := by
    have : (0 : ℤ) < n := by exact_mod_cast hn_pos_real
    omega
  have hn_eq1 : n = 1 := by
    by_contra hne1
    have hn_ge2 : 2 ≤ n := by omega
    let θ₁ : ℝ := 2 * Real.pi / (n : ℝ)
    have hθ₁_pos : 0 < θ₁ := div_pos (by positivity) hn_pos_real
    have hθ₁_lt : θ₁ < 2 * Real.pi := by
      dsimp [θ₁]
      rw [div_lt_iff₀ hn_pos_real]
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge2
      nlinarith [Real.pi_pos]
    have hφ_eq : φ (γ θ₁) = φ (γ 0) := by
      rw [hφγ_eq θ₁, hγ_0, hα_int]
      have hexp_θ₁ : ((n : ℝ) : ℂ) * (θ₁ : ℂ) * Complex.I = (2 * Real.pi : ℂ) * Complex.I := by
        dsimp [θ₁]
        have hn_c : (n : ℂ) ≠ 0 := by exact_mod_cast hn_pos_real.ne'
        push_cast
        rw [mul_div_cancel₀ _ hn_c]
      rw [hexp_θ₁, Complex.exp_two_pi_mul_I, mul_one]
    have hγ_eq : γ θ₁ = γ 0 := hφ_bij.injOn (hγ_mem θ₁) (hγ_mem 0) hφ_eq
    have hexp_θ₁_1 : Complex.exp ((θ₁ : ℂ) * Complex.I) = 1 := by
      dsimp [γ] at hγ_eq
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero] at hγ_eq
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr₀_pos.ne') hγ_eq
    obtain ⟨k, hk_eq⟩ := Complex.exp_eq_one_iff.mp hexp_θ₁_1
    have hθ₁_k_c : (θ₁ : ℂ) = (k : ℂ) * (2 * Real.pi : ℂ) := by
      apply mul_right_cancel₀ Complex.I_ne_zero
      linear_combination hk_eq
    have hθ₁_k : θ₁ = (k : ℝ) * (2 * Real.pi) := by
      have := congr_arg Complex.re hθ₁_k_c
      simpa using this
    have hk_pos : (0 : ℝ) < (k : ℝ) := by nlinarith [Real.pi_pos]
    have hk_lt1 : (k : ℝ) < 1 := by nlinarith [Real.pi_pos]
    have hk_ge1 : (1 : ℤ) ≤ k := by
      have : (0 : ℤ) < k := by exact_mod_cast hk_pos
      omega
    have hk_lt1_int : k < 1 := by exact_mod_cast hk_lt1
    omega
  have hα_1 : α = 1 := by rw [hα_int, hn_eq1]; simp
  have hlog_eq : Real.log Q₂ = Real.log Q₁ := by
    dsimp [α] at hα_1
    exact (div_eq_one_iff_eq hlogQ₁_pos.ne').mp hα_1
  exact (Real.log_injOn_pos hQ₂_pos (lt_trans zero_lt_one hQ₁) hlog_eq).symm

#print axioms unitDir
#print axioms norm_unitDir
#print axioms unitDir_ne_zero
#print axioms unitDir_mul_pos
#print axioms unitDir_div_pos_exp
#print axioms continuousAt_unitDir
#print axioms PreservesAnglesAt
#print axioms preservesAnglesAt_limit_norm_one
#print axioms theorem14_2_of_hasDerivAt
#print axioms theorem14_2_of_hasFDerivAt_real
#print axioms theorem14_2_not_preservesAnglesAt_of_deriv_zero
#print axioms node14_2_norm_mul_self_example
#print axioms theorem14_2
#print axioms theorem14_1
#print axioms moebiusMap
#print axioms moebiusMap_scale
#print axioms moebiusMap_comp
#print axioms moebiusMap_inv_left
#print axioms moebiusMap_inv_right
#print axioms moebiusMap_bijective
#print axioms moebiusTrans
#print axioms moebiusRot
#print axioms moebiusDil
#print axioms moebiusInv
#print axioms moebiusMap_generatedByElementary
#print axioms generalizedCircleLocus
#print axioms mem_generalizedCircleLocus_infty
#print axioms mem_generalizedCircleLocus_coe
#print axioms IsGeneralizedCircle
#print axioms isGeneralizedCircle_iff_circle_or_line
#print axioms theorem14_3_stereographic_circle_iff
#print axioms isGeneralizedCircle_image_moebiusMap
#print axioms moebiusMap_eq_id_of_fixes_zero_one_infty
#print axioms moebiusToStdCoeffs
#print axioms moebiusToStdCoeffs_infty_coe_coe
#print axioms moebiusToStdCoeffs_coe_infty_coe
#print axioms moebiusToStdCoeffs_coe_coe_infty
#print axioms moebiusToStdCoeffs_coe_coe_coe
#print axioms moebiusToStdCoeffs_spec
#print axioms moebius_finite_triple_to_zero_one_infty
#print axioms moebius_unique_three_point_interpolation
#print axioms stdRealLineCircle
#print axioms isGeneralizedCircle_stdRealLineCircle
#print axioms exists_three_distinct_mem_of_isGeneralizedCircle
#print axioms eq_stdRealLineCircle_of_mem_zero_one_infty
#print axioms moebius_maps_generalizedCircle_to_generalizedCircle
#print axioms cayleyMap
#print axioms cayleyMap_props
#print axioms IsOpenHalfPlane
#print axioms openDisc_conformally_equiv_openHalfPlane
#print axioms theorem14_3
#print axioms upperHalfPlaneToUnitBall
#print axioms upperHalfPlaneToUnitBall_props
#print axioms hasDerivAt_conj_comp_conj
#print axioms circularSchwarzReflection
#print axioms theorem14_4
#print axioms IsNormalFamily
#print axioms theorem14_5
#print axioms theorem14_6
#print axioms ConformallyEquivalent
#print axioms HolomorphicSubalgebra
#print axioms conformallyEquivalent_refl
#print axioms conformallyEquivalent_symm
#print axioms conformallyEquivalent_trans
#print axioms theorem14_7
#print axioms theorem14_8
#print axioms theorem14_9
#print axioms ClassS
#print axioms classS_taylor_expansion
#print axioms theorem14_10
#print axioms koebeFamily
#print axioms theorem14_11
#print axioms classS_odd_sqrt_aux
#print axioms theorem14_12
#print axioms det_complex_realCLM
#print axioms det_real_smulRight_complex
#print axioms exists_unit_sq_direction
#print axioms ellipseLinearEquiv
#print axioms ellipseLinearEquiv_apply
#print axioms ellipseLinearEquiv_symm_apply
#print axioms volume_image_ellipseLinearEquiv_closedBall
#print axioms intervalIntegral_exp_int_mul_I
#print axioms bessel_trig_poly_bound
#print axioms ortho_holomorphic_tail_on_circle
#print axioms puncturedBall_isRegion
#print axioms isConnected_compl_closedUnitBall
#print axioms theorem14_13
#print axioms deriv_dslope_zero_of_classS
#print axioms theorem14_14
#print axioms theorem14_15
#print axioms IsSimpleBoundaryPoint
#print axioms theorem14_16
#print axioms bookSimplyConnected_of_starConvex
#print axioms slitUnitDisc
#print axioms openUnitSquare
#print axioms combBottomSegment
#print axioms combTopSegment
#print axioms combRegion
#print axioms mem_combBottomSegment_iff
#print axioms mem_combTopSegment_iff
#print axioms combRegion_bookSimplyConnected
#print axioms theorem14_17
#print axioms eq_of_isPreconnected_forall_int
#print axioms exists_continuousOn_angle_Icc
#print axioms exists_continuousOn_angle_Ico
#print axioms lintegral_polar_deriv_sq_le_of_injOn
#print axioms ae_radial_limit_of_injOn_ball
#print axioms holomorphic_zero_at_zero_of_ae_radial_zero_arc
#print axioms tendsto_norm_one_nhdsWithin
#print axioms tendsto_nhdsWithin_of_curve_Icc
#print axioms lindelof_curve_tendsto
#print axioms theorem14_18_part_a
#print axioms theorem14_18_part_b
#print axioms theorem14_18
#print axioms caratheodoryExtension
#print axioms caratheodoryExtension_eq_of_mem
#print axioms caratheodoryExtension_frontier_spec
#print axioms eqOn_of_continuousOn_closure_eqOn
#print axioms caratheodoryExtension_homeomorph_package
#print axioms theorem14_19
#print axioms IsJordanCurve
#print axioms IsJordanArc
#print axioms isCompact_of_isJordanCurve
#print axioms nonempty_of_isJordanCurve
#print axioms isCompact_of_isJordanArc
#print axioms isConnected_of_isJordanArc
#print axioms eq_of_isPreconnected_int_cast
#print axioms HasContLogRatio
#print axioms hasContLogRatio_refl
#print axioms hasContLogRatio_symm
#print axioms hasContLogRatio_trans
#print axioms hasContLogRatio_mono
#print axioms hasContLogRatio_ball_step
#print axioms hasContLogRatio_of_mem_connectedComponentIn
#print axioms not_hasContLogRatio_of_bounded_open_frontier_subset
#print axioms isConnected_exterior_closedBall
#print axioms isOpen_and_frontier_subset_of_connectedComponentIn_compl
#print axioms bounded_or_eq_unbounded_component_of_isCompact
#print axioms borsuk_eilenberg_iff
#print axioms janiszewski_connectedComponentIn
#print axioms isConnected_compl_of_isJordanArc
#print axioms circleArc_isJordanArc
#print axioms sphere_split_two_arcs
#print axioms isJordanArc_image_of_homeomorph
#print axioms jordanCurve_arc_decomposition
#print axioms jordanCurve_component_frontier_eq
#print axioms jordanCurve_bounded_component_simplyConnected
#print axioms jordanCurve_bounded_component_locally_joined
#print axioms jordanCurve_bounded_component_all_simple
#print axioms jordanBoundary_region_converse
#print axioms UnitCirclePosCyclic
#print axioms unitCircleCyclicDet
#print axioms unitCircleCyclicDet_exp_formula
#print axioms exists_angle_Ioo_two_pi_of_mem_sphere_ne_one
#print axioms unitCirclePosCyclic_iff_det_pos
#print axioms unitCircleCyclicDet_swap
#print axioms unitCirclePosCyclic_pairwise_ne
#print axioms unitCirclePosCyclic_dichotomy
#print axioms unitCirclePosCyclic_rotate_triple
#print axioms unitCirclePosCyclic_std
#print axioms diskAut
#print axioms diskAut_props
#print axioms diskAut_preserves_posCyclic
#print axioms diskAut_eq_id_of_three_fixed
#print axioms eqOn_closedBall_of_eqOn_ball
#print axioms diskAutInv_props
#print axioms exists_diskAut_to_std
#print axioms exists_unique_diskAut_three_points
#print axioms not_exists_continuousOn_exp_eq_sub_on_sphere
#print axioms homeomorph_closedBall_preserves_sphere_and_ball
#print axioms continuous_moebiusAffine
#print axioms continuous_moebiusInv
#print axioms moebiusMap_continuous
#print axioms moebiusHomeomorph
#print axioms sphereFinitePart
#print axioms sphereFinitePart_infty
#print axioms sphereFinitePart_coe
#print axioms sphereChartCenter
#print axioms sphereChartCenter_infty
#print axioms sphereChartCenter_coe
#print axioms sphereChartIn
#print axioms sphereChartIn_infty
#print axioms sphereChartIn_coe
#print axioms sphereChartOut
#print axioms sphereChartOut_infty
#print axioms sphereChartOut_coe
#print axioms moebiusInv_involutive
#print axioms sphereChartIn_center
#print axioms sphereChartOut_self
#print axioms continuous_sphereChartIn
#print axioms eventually_sphereChartIn_out
#print axioms SphericalHolomorphicOn
#print axioms sphericalHolomorphicOn_id
#print axioms SphericalHolomorphicOn.mono
#print axioms SphericalHolomorphicOn.congr
#print axioms SphericalHolomorphicOn.comp
#print axioms sphericalHolomorphicOn_moebiusAffine
#print axioms sphericalHolomorphicOn_moebiusInv
#print axioms moebiusMap_sphericalHolomorphicOn
#print axioms sphericalHolomorphicOn_coe_iff
#print axioms IsSphericalRegion
#print axioms SphericalSimplyConnected
#print axioms IsSphericalSimpleBoundaryPoint
#print axioms isSphericalRegion_image_homeomorph
#print axioms sphericalSimplyConnected_image_homeomorph
#print axioms isSphericalSimpleBoundaryPoint_image_homeomorph
#print axioms closure_and_frontier_coe_of_isBounded
#print axioms bounded_plane_region_spherical_iff
#print axioms spherical_region_moebius_to_bounded_plane
#print axioms openHalfPlane_moebius_bij
#print axioms bounded_subset_ne_univ
#print axioms exists_riemann_map_of_bounded
#print axioms unitDisc_all_simple
#print axioms theorem14_20_part_a
#print axioms closure_bijOn_closedBall_factorization
#print axioms BoundaryPosCyclic
#print axioms boundaryPosCyclic_invariance_and_dichotomy
#print axioms theorem14_20_part_b
#print axioms IsMoebiusDiscTarget
#print axioms SphericalBoundaryPosCyclic
#print axioms isMoebiusDiscTarget_unitDisc
#print axioms isMoebiusDiscTarget_openHalfPlane
#print axioms eqOn_closure_riemannSphere
#print axioms theorem14_20_part_c
#print axioms theorem14_20_part_d
#print axioms theorem14_20
#print axioms annulus
#print axioms annulus_isOpen
#print axioms annulus_isRegion
#print axioms annulus_not_simplyConnected
#print axioms theorem14_21
#print axioms theorem14_22

end RudinRCA.Chapter14
