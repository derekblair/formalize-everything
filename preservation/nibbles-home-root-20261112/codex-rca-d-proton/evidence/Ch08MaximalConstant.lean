module
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public section
open Filter Set
open scoped Topology
namespace RudinRCA.Chapter08

/-- The elementary exponential estimate used in Rudin's optimized maximal bound. -/
theorem conjugateExponent_rpow_le_exp {p : ℝ} (hp : 1 < p) :
    (p / (p - 1)) ^ (p - 1) ≤ Real.exp 1 := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hd : 0 < p - 1 := sub_pos.mpr hp
  have hq : 0 < p / (p - 1) := div_pos hp0 hd
  rw [Real.rpow_def_of_pos hq, Real.exp_le_exp]
  have hlog := mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos hq) hd.le
  have he : (p / (p - 1) - 1) * (p - 1) = 1 := by
    field_simp [hd.ne']
    ring
  exact hlog.trans_eq he

/-- Bounding the optimized p-th-power coefficient by the one printed in 8.18. -/
theorem maximalLpCoefficient_le {A p : ℝ} (hA : 0 ≤ A) (hp : 1 < p) :
    A * p * (p / (p - 1)) ^ p ≤ A * Real.exp 1 * p * (p / (p - 1)) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq : 0 < p / (p - 1) := div_pos hp0 (sub_pos.mpr hp)
  have hpow : (p / (p - 1)) ^ p =
      (p / (p - 1)) * (p / (p - 1)) ^ (p - 1) := by
    calc
      _ = (p / (p - 1)) ^ (1 + (p - 1)) := by congr 1; ring
      _ = (p / (p - 1)) ^ (1 : ℝ) * (p / (p - 1)) ^ (p - 1) := Real.rpow_add hq _ _
      _ = _ := by rw [Real.rpow_one]
  calc
    _ = (A * p * (p / (p - 1))) * (p / (p - 1)) ^ (p - 1) := by rw [hpow]; ring
    _ ≤ (A * p * (p / (p - 1))) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (conjugateExponent_rpow_le_exp hp) (by positivity)
    _ = _ := by ring

/-- Scalar form of the optimized truncation coefficient, with cutoff t/q. -/
theorem maximalLpParameterizedCoefficient_le {A p : ℝ} (hA : 0 ≤ A) (hp : 1 < p) :
    p * (1 / (1 - 1 / (p / (p - 1)))) * A *
        ((p / (p - 1)) ^ (p - 1) / (p - 1)) ≤
      A * Real.exp 1 * p * (p / (p - 1)) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hd : 0 < p - 1 := sub_pos.mpr hp
  have hq : 0 < p / (p - 1) := div_pos hp0 hd
  have hden : 1 - 1 / (p / (p - 1)) = 1 / p := by
    field_simp [hp0.ne', hd.ne']
    ring
  have hpow : (p / (p - 1)) ^ p =
      (p / (p - 1)) * (p / (p - 1)) ^ (p - 1) := by
    calc
      _ = (p / (p - 1)) ^ (1 + (p - 1)) := by congr 1; ring
      _ = (p / (p - 1)) ^ (1 : ℝ) * (p / (p - 1)) ^ (p - 1) := Real.rpow_add hq _ _
      _ = _ := by rw [Real.rpow_one]
  calc
    _ = A * p * (p / (p - 1)) ^ p := by
      rw [hden, one_div_one_div, hpow]
      ring
    _ ≤ _ := maximalLpCoefficient_le hA hp

/-- The constant displayed after the proof of 8.18, for weak-type constant A. -/
noncomputable def maximalLpConstant (A p : ℝ) : ℝ :=
  (A * Real.exp 1 * p * (p / (p - 1))) ^ (1 / p)

/-- The optimized constant approaches one as p increases without bound. -/
theorem maximalLpConstant_tendsto_atTop {A : ℝ} (hA : 0 < A) :
    Tendsto (maximalLpConstant A) atTop (𝓝 1) := by
  have hi : Tendsto (fun p : ℝ => 1 / p) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hq : Tendsto (fun p : ℝ => p / (p - 1)) atTop (𝓝 1) := by
    have hdtop : Tendsto (fun p : ℝ => p - 1) atTop atTop := by
      apply Filter.tendsto_atTop.mpr
      intro b
      filter_upwards [eventually_ge_atTop (b + 1)] with p hp
      linarith
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_inv_atTop_zero.comp hdtop)
    apply (show Tendsto (fun p : ℝ => 1 + (p - 1)⁻¹) atTop (𝓝 1) by simpa using h).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with p hp
    field_simp [(sub_pos.mpr hp).ne'] <;> ring
  have hc : Tendsto (fun p : ℝ => (A * Real.exp 1) ^ (1 / p)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := A * Real.exp 1)).rpow hi
      (Or.inl (ne_of_gt (mul_pos hA (Real.exp_pos _))))
  have hqp : Tendsto (fun p : ℝ => (p / (p - 1)) ^ (1 / p)) atTop (𝓝 1) := by
    simpa using hq.rpow hi (Or.inl one_ne_zero)
  have hprod : Tendsto (fun p : ℝ => (A * Real.exp 1) ^ (1 / p) *
      p ^ (1 / p) * (p / (p - 1)) ^ (1 / p)) atTop (𝓝 1) := by
    simpa [Pi.mul_apply] using (hc.mul tendsto_rpow_div).mul hqp
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with p hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < p / (p - 1) := div_pos hp0 (sub_pos.mpr hp)
  dsimp [maximalLpConstant]
  rw [Real.mul_rpow (by positivity : 0 ≤ A * Real.exp 1 * p) hq0.le,
    Real.mul_rpow (by positivity : 0 ≤ A * Real.exp 1) hp0.le]

/-- The optimized constant diverges as p decreases to one from above. -/
theorem maximalLpConstant_tendsto_one_right {A : ℝ} (hA : 0 < A) :
    Tendsto (maximalLpConstant A) (𝓝[>] 1) atTop := by
  have hid : Tendsto (fun p : ℝ => p) (𝓝[>] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hd : Tendsto (fun p : ℝ => p - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using hid.sub_const 1
    · filter_upwards [self_mem_nhdsWithin] with p hp
      exact sub_pos.mpr hp
  have hq : Tendsto (fun p : ℝ => p / (p - 1)) (𝓝[>] 1) atTop := by
    simpa only [div_eq_mul_inv, Function.comp_def] using
      hid.pos_mul_atTop zero_lt_one (tendsto_inv_nhdsGT_zero.comp hd)
  have hb : Tendsto (fun p : ℝ => A * Real.exp 1 * p * (p / (p - 1)))
      (𝓝[>] 1) atTop := by
    have hc : Tendsto (fun p : ℝ => A * Real.exp 1 * p) (𝓝[>] 1)
        (𝓝 (A * Real.exp 1)) := by simpa using hid.const_mul (A * Real.exp 1)
    exact hc.pos_mul_atTop (mul_pos hA (Real.exp_pos _)) hq
  have hi : Tendsto (fun p : ℝ => 1 / p) (𝓝[>] 1) (𝓝 1) := by
    simpa only [one_div, inv_one] using hid.inv₀ one_ne_zero
  have h := Real.tendsto_exp_atTop.comp
    ((Real.tendsto_log_atTop.comp hb).atTop_mul_pos zero_lt_one hi)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < p / (p - 1) := div_pos hp0 (sub_pos.mpr hp)
  exact (Real.rpow_def_of_pos (by positivity : 0 < A * Real.exp 1 * p * (p / (p - 1))) _).symm

end RudinRCA.Chapter08
