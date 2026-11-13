import RudinRCA.Chapter10
import RudinRCA.Chapter11
import RudinRCA.Chapter12
import RudinRCA.Chapter13
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

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
#print axioms annulus
#print axioms annulus_isOpen
#print axioms annulus_isRegion
#print axioms annulus_not_simplyConnected
#print axioms theorem14_21
#print axioms theorem14_22

end RudinRCA.Chapter14
