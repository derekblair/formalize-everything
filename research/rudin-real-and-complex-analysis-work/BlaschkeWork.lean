import RudinRCA.Chapter15
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic.FieldSimp

noncomputable section
open Filter Finset
open scoped Topology ComplexConjugate

namespace RudinRCA.Chapter15

/-- The normalized zero factor in Rudin 15.21. -/
def blaschkeFactor (a z : ℂ) : ℂ :=
  (‖a‖ : ℂ) / a * (a - z) / (1 - conj a * z)

theorem blaschke_denominator_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj a * z ≠ 0 := by
  apply sub_ne_zero.mpr
  intro heq
  have hlt : ‖conj a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_of_le_one_right (norm_nonneg a) hz).trans_lt ha
  rw [← heq, norm_one] at hlt
  exact (lt_irrefl (1 : ℝ)) hlt

theorem norm_blaschke_phase {a : ℂ} (ha : a ≠ 0) : ‖(‖a‖ : ℂ) / a‖ = 1 := by
  rw [norm_div, Complex.norm_of_nonneg (norm_nonneg a), div_self (norm_ne_zero_iff.mpr ha)]

theorem blaschkeFactor_zero {a : ℂ} (ha : a ≠ 0) :
    blaschkeFactor a 0 = (‖a‖ : ℂ) := by
  simp [blaschkeFactor, ha]

theorem blaschkeFactor_eq_zero_iff {a z : ℂ} (ha0 : a ≠ 0) (ha : ‖a‖ < 1)
    (hz : ‖z‖ < 1) : blaschkeFactor a z = 0 ↔ z = a := by
  have hnorm : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ha0
  simp only [blaschkeFactor, div_eq_zero_iff, mul_eq_zero, hnorm, ha0,
    blaschke_denominator_ne_zero ha hz.le, or_false, false_or, sub_eq_zero]
  exact eq_comm

theorem differentiableOn_blaschkeFactor {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (blaschkeFactor a) (Metric.ball 0 1) := by
  intro z hz
  have hz' : ‖z‖ < 1 := by simpa using hz
  have hden := blaschke_denominator_ne_zero ha hz'.le
  unfold blaschkeFactor
  fun_prop

/-- The elementary disk-automorphism identity, valid also on the boundary. -/
theorem blaschke_norm_difference (a z : ℂ) :
    ‖1 - conj a * z‖ ^ 2 - ‖a - z‖ ^ 2 =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_one,
    Complex.normSq_mul, Complex.normSq_conj, one_mul, Complex.conj_re,
    Complex.mul_re, Complex.conj_im]
  ring

theorem norm_blaschkeFactor_le_one {a z : ℂ} (ha0 : a ≠ 0) (ha : ‖a‖ < 1)
    (hz : ‖z‖ ≤ 1) : ‖blaschkeFactor a z‖ ≤ 1 := by
  have ha2 : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hz2 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hsq := blaschke_norm_difference a z
  have hle : ‖a - z‖ ≤ ‖1 - conj a * z‖ := by
    nlinarith [mul_nonneg ha2 hz2, norm_nonneg (a - z), norm_nonneg (1 - conj a * z)]
  rw [blaschkeFactor, norm_div, norm_mul, norm_blaschke_phase ha0, one_mul]
  exact (div_le_one (norm_pos_iff.mpr (blaschke_denominator_ne_zero ha hz))).2 hle

theorem one_sub_blaschkeFactor {a z : ℂ} (ha0 : a ≠ 0)
    (hden : 1 - conj a * z ≠ 0) :
    1 - blaschkeFactor a z =
      ((1 - ‖a‖ : ℝ) : ℂ) * (1 + ((‖a‖ : ℂ) / a) * z) / (1 - conj a * z) := by
  have haa : conj a * a = (‖a‖ : ℂ) ^ 2 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  unfold blaschkeFactor
  push_cast
  field_simp
  linear_combination z * haa

/-- The compact-disk majorant for the infinite Blaschke product. -/
theorem norm_one_sub_blaschkeFactor_le {a z : ℂ} (ha0 : a ≠ 0) (ha : ‖a‖ < 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hz : ‖z‖ ≤ r) :
    ‖1 - blaschkeFactor a z‖ ≤ (1 - ‖a‖) * ((1 + r) / (1 - r)) := by
  have hden := blaschke_denominator_ne_zero ha (hz.trans hr.le)
  have hdpos : 0 < 1 - r := sub_pos.mpr hr
  have hd : 1 - r ≤ ‖1 - conj a * z‖ := by
    have hrev := norm_sub_norm_le (1 : ℂ) (conj a * z)
    simp only [norm_one, norm_mul, Complex.norm_conj] at hrev
    have hamul : ‖a‖ * ‖z‖ ≤ r :=
      (mul_le_mul_of_nonneg_right ha.le (norm_nonneg z)).trans (by simpa using hz)
    linarith
  rw [one_sub_blaschkeFactor ha0 hden, norm_div, norm_mul,
    Complex.norm_of_nonneg (sub_nonneg.mpr ha.le)]
  have hnum : ‖1 + (‖a‖ : ℂ) / a * z‖ ≤ 1 + r := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖(‖a‖ : ℂ) / a * z‖ := norm_add_le _ _
      _ = 1 + ‖z‖ := by rw [norm_one, norm_mul, norm_blaschke_phase ha0, one_mul]
      _ ≤ 1 + r := add_le_add_left hz _
  calc
    _ ≤ ((1 - ‖a‖) * (1 + r)) / (1 - r) :=
      div_le_div₀ (mul_nonneg (sub_nonneg.mpr ha.le) (by positivity))
        (mul_le_mul_of_nonneg_left hnum (sub_nonneg.mpr ha.le)) hdpos hd
    _ = _ := by ring

theorem analyticOrderAt_blaschkeFactor {a z : ℂ} (ha0 : a ≠ 0) (ha : ‖a‖ < 1)
    (hz : ‖z‖ < 1) :
    analyticOrderAt (blaschkeFactor a) z = if z = a then 1 else 0 := by
  have hden := blaschke_denominator_ne_zero ha hz.le
  have hc : (‖a‖ : ℂ) / a ≠ 0 := by
    apply div_ne_zero _ ha0
    exact_mod_cast norm_ne_zero_iff.mpr ha0
  let q : ℂ → ℂ := fun w ↦ ((‖a‖ : ℂ) / a) / (1 - conj a * w)
  have hq : AnalyticAt ℂ q z := by dsimp [q]; fun_prop
  have hq0 : q z ≠ 0 := div_ne_zero hc hden
  have hlin : AnalyticAt ℂ (fun w : ℂ ↦ a - w) z := by fun_prop
  have heq : blaschkeFactor a = q * (fun w ↦ a - w) := by
    funext w
    simp only [blaschkeFactor, q, Pi.mul_apply]
    ring
  rw [heq, analyticOrderAt_mul hq hlin, hq.analyticOrderAt_eq_zero.mpr hq0, zero_add]
  have hneg : (fun w : ℂ ↦ a - w) = -(fun w : ℂ ↦ w - a) := by
    funext w
    simp
  rw [hneg, analyticOrderAt_neg]
  by_cases he : z = a
  · subst z
    simp
  · simp [he, analyticOrderAt_id_sub_const_of_ne he]

/-- Uniform convergence of the norm-error series on compact subsets of the disk. -/
theorem blaschke_errors_locally_uniform {a : ℕ → ℂ}
    (ha0 : ∀ n, a n ≠ 0) (ha : ∀ n, ‖a n‖ < 1)
    (hsum : Summable (fun n ↦ 1 - ‖a n‖)) :
    TendstoLocallyUniformlyOn
      (fun N z ↦ ∑ n ∈ range N, ‖1 - blaschkeFactor (a n) z‖)
      (fun z ↦ ∑' n, ‖1 - blaschkeFactor (a n) z‖) atTop (Metric.ball 0 1) := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball).2
  intro K hKU hK
  by_cases hne : K.Nonempty
  · obtain ⟨w, hw, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
    have hw1 : ‖w‖ < 1 := by simpa using hKU hw
    apply tendstoUniformlyOn_tsum_nat_eventually
      (hsum.mul_right ((1 + ‖w‖) / (1 - ‖w‖)))
    apply Filter.Eventually.of_forall
    intro n z hz
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact norm_one_sub_blaschkeFactor_le (ha0 n) (ha n) (norm_nonneg w) hw1 (hmax hz)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact tendstoUniformlyOn_empty

/-- The product assertion of 15.21 away from the optional zero at the origin. -/
theorem infinite_blaschke_product {a : ℕ → ℂ}
    (ha0 : ∀ n, a n ≠ 0) (ha : ∀ n, ‖a n‖ < 1)
    (hsum : Summable (fun n ↦ 1 - ‖a n‖)) :
    let B := fun z ↦ ∏' n, blaschkeFactor (a n) z
    TendstoLocallyUniformlyOn
      (fun N z ↦ ∏ n ∈ range N, blaschkeFactor (a n) z) B atTop (Metric.ball 0 1) ∧
    DifferentiableOn ℂ B (Metric.ball 0 1) ∧
    ∀ z ∈ Metric.ball 0 1, ‖B z‖ ≤ 1 ∧
      (B z = 0 ↔ ∃ n, z = a n) ∧ analyticOrderAt B z ≠ ⊤ ∧
      analyticOrderNatAt B z = ∑' n, if z = a n then (1 : ℕ) else 0 := by
  have hF : ∀ n, DifferentiableOn ℂ (blaschkeFactor (a n)) (Metric.ball 0 1) :=
    fun n ↦ differentiableOn_blaschkeFactor (ha n)
  have hnonzero : ∀ n z, z ∈ Metric.ball (0 : ℂ) 1 →
      ∃ w ∈ connectedComponentIn (Metric.ball 0 1) z, blaschkeFactor (a n) w ≠ 0 := by
    intro n z hz
    refine ⟨0, ?_, ?_⟩
    · rw [(convex_ball (0 : ℂ) 1).isPreconnected.connectedComponentIn hz]
      exact Metric.mem_ball_self zero_lt_one
    · rw [blaschkeFactor_zero (ha0 n)]
      exact_mod_cast norm_ne_zero_iff.mpr (ha0 n)
  have herr := blaschke_errors_locally_uniform ha0 ha hsum
  obtain ⟨hlim, hhol, horder⟩ := holomorphic_product_multiplicity
    Metric.isOpen_ball hF hnonzero ⟨_, herr⟩
  refine ⟨hlim, hhol, ?_⟩
  intro z hz
  have hz1 : ‖z‖ < 1 := by simpa using hz
  have hbound : ‖∏' n, blaschkeFactor (a n) z‖ ≤ 1 := by
    apply le_of_tendsto (continuous_norm.tendsto _ |>.comp (hlim.tendsto_at hz))
    apply Filter.Eventually.of_forall
    intro N
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun n _ ↦ norm_nonneg _) (fun n _ ↦
      norm_blaschkeFactor_le_one (ha0 n) (ha n) hz1.le)
  have hsz : Summable (fun n ↦ ‖1 - blaschkeFactor (a n) z‖) :=
    ((hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ norm_nonneg _) _).2
      (herr.tendsto_at hz)).summable
  have hzero : (∏' n, blaschkeFactor (a n) z) = 0 ↔ ∃ n, z = a n := by
    constructor
    · intro hb
      by_contra h
      push_neg at h
      have hnone : ∀ n, blaschkeFactor (a n) z ≠ 0 := by
        intro n
        exact mt (blaschkeFactor_eq_zero_iff (ha0 n) (ha n) hz1).mp (h n)
      have hone : ∀ n, 1 + (blaschkeFactor (a n) z - 1) = blaschkeFactor (a n) z :=
        fun n ↦ by ring
      have hnorm : Summable (fun n ↦ ‖blaschkeFactor (a n) z - 1‖) := by
        simpa only [norm_sub_rev] using hsz
      have hn := tprod_one_add_ne_zero_of_summable
        (fun n ↦ by simpa only [hone] using hnone n) hnorm
      exact hn (by simpa only [hone] using hb)
    · rintro ⟨n, hn⟩
      exact tprod_of_exists_eq_zero ⟨n, (blaschkeFactor_eq_zero_iff (ha0 n) (ha n) hz1).2 hn⟩
  obtain ⟨_, hfinite, hm, _⟩ := horder z hz
  refine ⟨hbound, hzero, hfinite, ?_⟩
  rw [hm]
  apply tsum_congr
  intro n
  simp only [analyticOrderNatAt, analyticOrderAt_blaschkeFactor (ha0 n) (ha n) hz1]
  split_ifs <;> simp

/-- Definition 15.21, including a zero of prescribed order at the origin. -/
def blaschkeProduct (k : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  z ^ k * ∏' n, blaschkeFactor (a n) z

theorem analyticOrderAt_power (k : ℕ) (z : ℂ) :
    analyticOrderAt (fun w : ℂ ↦ w ^ k) z = if z = 0 then (k : ℕ∞) else 0 := by
  by_cases hz : z = 0
  · subst z
    simpa using analyticOrderAt_pow (f := id) (z₀ := (0 : ℂ)) analyticAt_id k
  · rw [if_neg hz]
    exact (analyticAt_id.pow k).analyticOrderAt_eq_zero.mpr (pow_ne_zero k hz)

/-- Rudin 15.21, including the zero at the origin and its exact multiplicity. -/
theorem blaschke_product_properties (k : ℕ) {a : ℕ → ℂ}
    (ha0 : ∀ n, a n ≠ 0) (ha : ∀ n, ‖a n‖ < 1)
    (hsum : Summable (fun n ↦ 1 - ‖a n‖)) :
    DifferentiableOn ℂ (blaschkeProduct k a) (Metric.ball 0 1) ∧
    ∀ z ∈ Metric.ball 0 1, ‖blaschkeProduct k a z‖ ≤ 1 ∧
      (blaschkeProduct k a z = 0 ↔ (z = 0 ∧ 0 < k) ∨ ∃ n, z = a n) ∧
      analyticOrderAt (blaschkeProduct k a) z ≠ ⊤ ∧
      analyticOrderNatAt (blaschkeProduct k a) z =
        (if z = 0 then k else 0) + ∑' n, if z = a n then (1 : ℕ) else 0 := by
  obtain ⟨_, hB, hprop⟩ := infinite_blaschke_product ha0 ha hsum
  have hp : Differentiable ℂ (fun z : ℂ ↦ z ^ k) := differentiable_id.pow k
  refine ⟨hp.differentiableOn.mul hB, ?_⟩
  intro z hz
  have hz1 : ‖z‖ < 1 := by simpa using hz
  obtain ⟨hbound, hzero, hfinite, hm⟩ := hprop z hz
  have hpa := hp.analyticAt z
  have hBa := (hB.analyticOnNhd Metric.isOpen_ball) z hz
  have hpf : analyticOrderAt (fun w : ℂ ↦ w ^ k) z ≠ ⊤ := by
    rw [analyticOrderAt_power]
    split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [blaschkeProduct, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg z) hz1.le)
      (norm_nonneg _) hbound
  · change z ^ k * _ = 0 ↔ _
    rw [mul_eq_zero, hzero]
    by_cases hk : k = 0
    · simp [hk]
    · simp [pow_eq_zero_iff hk, Nat.pos_iff_ne_zero, hk]
  · change analyticOrderAt ((fun w : ℂ ↦ w ^ k) * (fun w ↦ ∏' n, blaschkeFactor (a n) w)) z ≠ ⊤
    rw [analyticOrderAt_mul hpa hBa]
    simp [ENat.add_eq_top, hpf, hfinite]
  · change analyticOrderNatAt ((fun w : ℂ ↦ w ^ k) * (fun w ↦ ∏' n, blaschkeFactor (a n) w)) z = _
    rw [analyticOrderNatAt_mul hpa hBa hpf hfinite, hm]
    congr 1
    simp only [analyticOrderNatAt, analyticOrderAt_power]
    split_ifs <;> simp

/-- The finite-list convention in Definition 15.21; the empty list yields z^k. -/
def finiteBlaschkeProduct {ι : Type*} (k : ℕ) (s : Finset ι) (a : ι → ℂ) (z : ℂ) : ℂ :=
  z ^ k * ∏ n ∈ s, blaschkeFactor (a n) z

/-- Finite and empty Blaschke products, including exact multiplicities. -/
theorem finite_blaschke_product_properties {ι : Type*} (k : ℕ) (s : Finset ι) (a : ι → ℂ)
    (ha0 : ∀ n ∈ s, a n ≠ 0) (ha : ∀ n ∈ s, ‖a n‖ < 1) :
    DifferentiableOn ℂ (finiteBlaschkeProduct k s a) (Metric.ball 0 1) ∧
    ∀ z ∈ Metric.ball 0 1, ‖finiteBlaschkeProduct k s a z‖ ≤ 1 ∧
      (finiteBlaschkeProduct k s a z = 0 ↔
        (z = 0 ∧ 0 < k) ∨ ∃ n ∈ s, z = a n) ∧
      analyticOrderAt (finiteBlaschkeProduct k s a) z =
        (if z = 0 then (k : ℕ∞) else 0) + ∑ n ∈ s, if z = a n then (1 : ℕ∞) else 0 := by
  classical
  have hF : ∀ n ∈ s, DifferentiableOn ℂ (blaschkeFactor (a n)) (Metric.ball 0 1) :=
    fun n hn ↦ differentiableOn_blaschkeFactor (ha n hn)
  have hp : Differentiable ℂ (fun z : ℂ ↦ z ^ k) := differentiable_id.pow k
  have hprod : DifferentiableOn ℂ (fun z ↦ ∏ n ∈ s, blaschkeFactor (a n) z)
      (Metric.ball 0 1) := DifferentiableOn.fun_finsetProd hF
  refine ⟨hp.differentiableOn.mul hprod, ?_⟩
  intro z hz
  have hz1 : ‖z‖ < 1 := by simpa using hz
  have hbound : ‖∏ n ∈ s, blaschkeFactor (a n) z‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun n _ ↦ norm_nonneg _)
      (fun n hn ↦ norm_blaschkeFactor_le_one (ha0 n hn) (ha n hn) hz1.le)
  have hzero : (∏ n ∈ s, blaschkeFactor (a n) z) = 0 ↔ ∃ n ∈ s, z = a n := by
    rw [Finset.prod_eq_zero_iff]
    constructor
    · rintro ⟨n, hn, he⟩
      exact ⟨n, hn, (blaschkeFactor_eq_zero_iff (ha0 n hn) (ha n hn) hz1).mp he⟩
    · rintro ⟨n, hn, he⟩
      exact ⟨n, hn, (blaschkeFactor_eq_zero_iff (ha0 n hn) (ha n hn) hz1).mpr he⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [finiteBlaschkeProduct, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg z) hz1.le) (norm_nonneg _) hbound
  · change z ^ k * _ = 0 ↔ _
    rw [mul_eq_zero, hzero]
    by_cases hk : k = 0
    · simp [hk]
    · simp [pow_eq_zero_iff hk, Nat.pos_iff_ne_zero, hk]
  · change analyticOrderAt ((fun w : ℂ ↦ w ^ k) *
      (fun w ↦ ∏ n ∈ s, blaschkeFactor (a n) w)) z = _
    rw [analyticOrderAt_mul (hp.analyticAt z) ((hprod.analyticOnNhd Metric.isOpen_ball) z hz),
      analyticOrderAt_power, analyticOrderAt_finset_product s
        (fun n hn ↦ ((hF n hn).analyticOnNhd Metric.isOpen_ball) z hz)]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    exact analyticOrderAt_blaschkeFactor (ha0 n hn) (ha n hn) hz1

#print axioms finite_blaschke_product_properties

#print axioms analyticOrderAt_power
#print axioms blaschke_product_properties

#print axioms blaschke_errors_locally_uniform
#print axioms infinite_blaschke_product

#print axioms blaschke_denominator_ne_zero
#print axioms norm_blaschke_phase
#print axioms blaschkeFactor_zero
#print axioms blaschkeFactor_eq_zero_iff
#print axioms differentiableOn_blaschkeFactor
#print axioms blaschke_norm_difference
#print axioms norm_blaschkeFactor_le_one
#print axioms one_sub_blaschkeFactor
#print axioms norm_one_sub_blaschkeFactor_le
#print axioms analyticOrderAt_blaschkeFactor

end RudinRCA.Chapter15
