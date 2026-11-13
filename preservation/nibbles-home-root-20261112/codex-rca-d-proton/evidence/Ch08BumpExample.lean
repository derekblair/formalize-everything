module
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace RudinRCA.Chapter08

/-- The subdivisions in 8.9(a), indexed from zero. -/
noncomputable def bumpDivision (n : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ n

@[simp] lemma bumpDivision_zero : bumpDivision 0 = 0 := by
  norm_num [bumpDivision]

lemma bumpDivision_strictMono : StrictMono bumpDivision := by
  intro m n hmn
  have h := pow_right_strictAnti₀ (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hmn
  exact sub_lt_sub_left h 1

lemma bumpDivision_lt_one (n : ℕ) : bumpDivision n < 1 := by
  have h := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n
  dsimp [bumpDivision]
  linarith

lemma bumpDivision_nonneg (n : ℕ) : 0 ≤ bumpDivision n := by
  have h := bumpDivision_strictMono.monotone (Nat.zero_le n)
  simpa [bumpDivision] using h

lemma bumpDivision_tendsto : Tendsto bumpDivision atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => (1 : ℝ) - (1 / 2 : ℝ) ^ n) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
  change Tendsto (fun n : ℕ => (1 : ℝ) - (1 / 2 : ℝ) ^ n) atTop (𝓝 1)
  simpa only [sub_zero] using h

noncomputable def rudinBump (n : ℕ) :
    ContDiffBump ((bumpDivision n + bumpDivision (n + 1)) / 2) where
  rIn := (bumpDivision (n + 1) - bumpDivision n) / 8
  rOut := (bumpDivision (n + 1) - bumpDivision n) / 4
  rIn_pos := by
    have h := bumpDivision_strictMono (Nat.lt_succ_self n)
    linarith
  rIn_lt_rOut := by
    have h := bumpDivision_strictMono (Nat.lt_succ_self n)
    linarith

/-- A concrete choice of Rudin's continuous bumps, with integral one. -/
noncomputable def rudinBumpFunction (n : ℕ) : ℝ → ℝ :=
  (rudinBump n).normed volume

lemma rudinBumpFunction_continuous (n : ℕ) : Continuous (rudinBumpFunction n) :=
  (rudinBump n).continuous_normed

lemma rudinBumpFunction_support (n : ℕ) :
    Function.support (rudinBumpFunction n) ⊆ Ioo (bumpDivision n) (bumpDivision (n + 1)) := by
  intro x hx
  rw [rudinBumpFunction, (rudinBump n).support_normed_eq] at hx
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
  have hd := bumpDivision_strictMono (Nat.lt_succ_self n)
  change -( (bumpDivision (n + 1) - bumpDivision n) / 4) <
      x - (bumpDivision n + bumpDivision (n + 1)) / 2 ∧
    x - (bumpDivision n + bumpDivision (n + 1)) / 2 <
      (bumpDivision (n + 1) - bumpDivision n) / 4 at hx
  constructor <;> linarith [hx.1, hx.2]

/-- The topological support also lies strictly inside its assigned interval. -/
lemma rudinBumpFunction_tsupport (n : ℕ) :
    tsupport (rudinBumpFunction n) ⊆ Ioo (bumpDivision n) (bumpDivision (n + 1)) := by
  intro x hx
  rw [rudinBumpFunction, (rudinBump n).tsupport_normed_eq] at hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  have hd := bumpDivision_strictMono (Nat.lt_succ_self n)
  change -((bumpDivision (n + 1) - bumpDivision n) / 4) ≤
      x - (bumpDivision n + bumpDivision (n + 1)) / 2 ∧
    x - (bumpDivision n + bumpDivision (n + 1)) / 2 ≤
      (bumpDivision (n + 1) - bumpDivision n) / 4 at hx
  constructor <;> linarith [hx.1, hx.2]

lemma rudinBumpFunction_zero_of_outside (n : ℕ) {x : ℝ}
    (hx : x ∉ Ioo (bumpDivision n) (bumpDivision (n + 1))) :
    rudinBumpFunction n x = 0 := by
  by_contra hn
  exact hx (rudinBumpFunction_support n hn)

lemma rudinBumpFunction_pairwise (x : ℝ) {n m : ℕ}
    (hn : rudinBumpFunction n x ≠ 0) (hm : rudinBumpFunction m x ≠ 0) : n = m := by
  have hnx := rudinBumpFunction_support n hn
  have hmx := rudinBumpFunction_support m hm
  rcases lt_trichotomy n m with h | h | h
  · have hd := bumpDivision_strictMono.monotone (Nat.succ_le_of_lt h)
    exact False.elim (not_lt_of_ge hd (hmx.1.trans hnx.2))
  · exact h
  · have hd := bumpDivision_strictMono.monotone (Nat.succ_le_of_lt h)
    exact False.elim (not_lt_of_ge hd (hnx.1.trans hmx.2))

lemma rudinBumpFunction_local_cutoff {x : ℝ} (hx : x ≠ 1) :
    ∃ N : ℕ, ∀ᶠ y in 𝓝 x, ∀ n ≥ N, rudinBumpFunction n y = 0 := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (bumpDivision_tendsto.eventually (eventually_gt_nhds hx))
    refine ⟨N, ?_⟩
    filter_upwards [eventually_lt_nhds (hN N le_rfl)] with y hy
    intro n hn
    apply rudinBumpFunction_zero_of_outside
    intro hmem
    have hd := bumpDivision_strictMono.monotone hn
    exact (not_lt_of_ge hd) (hmem.1.trans hy)
  · refine ⟨0, ?_⟩
    filter_upwards [eventually_gt_nhds hx] with y hy
    intro n _
    apply rudinBumpFunction_zero_of_outside
    intro hmem
    exact (not_lt_of_ge hy.le) (hmem.2.trans (bumpDivision_lt_one (n + 1)))

lemma rudinBumpFunction_cutoff (x : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, rudinBumpFunction n x = 0 := by
  by_cases hx : x = 1
  · subst x
    refine ⟨0, fun n _ => rudinBumpFunction_zero_of_outside n ?_⟩
    intro hmem
    exact (not_lt_of_ge (bumpDivision_lt_one (n + 1)).le) hmem.2
  · obtain ⟨N, hN⟩ := rudinBumpFunction_local_cutoff hx
    exact ⟨N, Filter.Eventually.self_of_nhds hN⟩

noncomputable abbrev bumpIntervalMeasure : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

lemma rudinBumpFunction_integrable (n : ℕ) :
    Integrable (rudinBumpFunction n) bumpIntervalMeasure :=
  (rudinBump n).integrable_normed.restrict

lemma rudinBumpFunction_integral (n : ℕ) :
    (∫ x, rudinBumpFunction n x ∂bumpIntervalMeasure) = 1 := by
  have h : (∫ x, rudinBumpFunction n x ∂bumpIntervalMeasure) =
      ∫ x, rudinBumpFunction n x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply rudinBumpFunction_zero_of_outside
    intro hmem
    exact hx ⟨(bumpDivision_nonneg n).trans hmem.1.le,
      hmem.2.le.trans (bumpDivision_lt_one (n + 1)).le⟩
  rw [h]
  exact (rudinBump n).integral_normed

/-- Rudin's exact series in 8.9(a), with the first bump indexed by zero. -/
noncomputable def rudinBumpSeries (x y : ℝ) : ℝ :=
  ∑' n : ℕ, (rudinBumpFunction n x - rudinBumpFunction (n + 1) x) * rudinBumpFunction n y


/-- There is at most one nonzero summand at every point, as observed in 8.9(a). -/
lemma rudinBumpSeries_unique_nonzero_term (x y : ℝ) {n m : ℕ}
    (hn : (rudinBumpFunction n x - rudinBumpFunction (n + 1) x) * rudinBumpFunction n y ≠ 0)
    (hm : (rudinBumpFunction m x - rudinBumpFunction (m + 1) x) * rudinBumpFunction m y ≠ 0) :
    n = m :=
  rudinBumpFunction_pairwise y (mul_ne_zero_iff.mp hn).2 (mul_ne_zero_iff.mp hm).2

lemma rudinBumpSeries_measurable : Measurable (Function.uncurry rudinBumpSeries) := by
  apply Measurable.tsum
  intro n
  exact (((rudinBumpFunction_continuous n).measurable.comp measurable_fst).sub
    ((rudinBumpFunction_continuous (n + 1)).measurable.comp measurable_fst)).mul
    ((rudinBumpFunction_continuous n).measurable.comp measurable_snd)

lemma rudinBumpSeries_finite_left (x : ℝ) :
    ∃ N : ℕ, ∀ y, rudinBumpSeries x y =
      ∑ n ∈ Finset.range N,
        (rudinBumpFunction n x - rudinBumpFunction (n + 1) x) * rudinBumpFunction n y := by
  obtain ⟨N, hN⟩ := rudinBumpFunction_cutoff x
  refine ⟨N, fun y => tsum_eq_sum (fun n hn => ?_)⟩
  have hn' : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
  rw [hN n hn', hN (n + 1) (hn'.trans (Nat.le_succ n)), sub_self, zero_mul]

lemma rudinBumpSeries_finite_right (y : ℝ) :
    ∃ N : ℕ, ∀ x, rudinBumpSeries x y =
      ∑ n ∈ Finset.range N,
        (rudinBumpFunction n x - rudinBumpFunction (n + 1) x) * rudinBumpFunction n y := by
  obtain ⟨N, hN⟩ := rudinBumpFunction_cutoff y
  refine ⟨N, fun x => tsum_eq_sum (fun n hn => ?_)⟩
  rw [hN n (Nat.le_of_not_gt (by simpa using hn)), mul_zero]

lemma rudinBumpSeries_sections_integrable :
    (∀ x, Integrable (rudinBumpSeries x) bumpIntervalMeasure) ∧
    (∀ y, Integrable (fun x => rudinBumpSeries x y) bumpIntervalMeasure) := by
  constructor
  · intro x
    obtain ⟨N, hN⟩ := rudinBumpSeries_finite_left x
    change Integrable (fun y => rudinBumpSeries x y) bumpIntervalMeasure
    simp_rw [hN]
    exact integrable_finsetSum _ (fun n _ => (rudinBumpFunction_integrable n).const_mul _)
  · intro y
    obtain ⟨N, hN⟩ := rudinBumpSeries_finite_right y
    simp_rw [hN]
    exact integrable_finsetSum _ (fun n _ =>
      ((rudinBumpFunction_integrable n).sub (rudinBumpFunction_integrable (n + 1))).mul_const _)

lemma rudinBumpSeries_integral_right (x : ℝ) :
    (∫ y, rudinBumpSeries x y ∂bumpIntervalMeasure) = rudinBumpFunction 0 x := by
  obtain ⟨N, hN⟩ := rudinBumpFunction_cutoff x
  have heq (y : ℝ) : rudinBumpSeries x y =
      ∑ n ∈ Finset.range N,
        (rudinBumpFunction n x - rudinBumpFunction (n + 1) x) * rudinBumpFunction n y := by
    apply tsum_eq_sum
    intro n hn
    have hn' : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
    rw [hN n hn', hN (n + 1) (hn'.trans (Nat.le_succ n)), sub_self, zero_mul]
  simp_rw [heq]
  rw [integral_finsetSum _ (fun n _ => (rudinBumpFunction_integrable n).const_mul _)]
  simp_rw [integral_const_mul, rudinBumpFunction_integral, mul_one]
  have htel (M : ℕ) :
      (∑ n ∈ Finset.range M, (rudinBumpFunction n x - rudinBumpFunction (n + 1) x)) =
      rudinBumpFunction 0 x - rudinBumpFunction M x := by
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ, ih]; ring
  rw [htel, hN N le_rfl, sub_zero]

lemma rudinBumpSeries_integral_left (y : ℝ) :
    (∫ x, rudinBumpSeries x y ∂bumpIntervalMeasure) = 0 := by
  obtain ⟨N, hN⟩ := rudinBumpSeries_finite_right y
  simp_rw [hN]
  rw [integral_finsetSum (Finset.range N)
    (f := fun n x => (rudinBumpFunction n x - rudinBumpFunction (n + 1) x) * rudinBumpFunction n y)
    (fun n _ => ((rudinBumpFunction_integrable n).sub
      (rudinBumpFunction_integrable (n + 1))).mul_const (rudinBumpFunction n y))]
  simp_rw [integral_mul_const, integral_sub (rudinBumpFunction_integrable _)
    (rudinBumpFunction_integrable _), rudinBumpFunction_integral, sub_self, zero_mul]
  exact Finset.sum_const_zero

lemma rudinBumpSeries_continuousAt {p : ℝ × ℝ} (hp : p ≠ (1, 1)) :
    ContinuousAt (Function.uncurry rudinBumpSeries) p := by
  have hp' : p.1 ≠ 1 ∨ p.2 ≠ 1 := by
    by_contra h
    push Not at h
    exact hp (Prod.ext h.1 h.2)
  rcases hp' with hx | hy
  · obtain ⟨N, hN⟩ := rudinBumpFunction_local_cutoff hx
    have hc : Continuous (fun q : ℝ × ℝ => ∑ n ∈ Finset.range N,
        (rudinBumpFunction n q.1 - rudinBumpFunction (n + 1) q.1) * rudinBumpFunction n q.2) := by
      apply continuous_finsetSum
      intro n _
      exact (((rudinBumpFunction_continuous n).comp continuous_fst).sub
        ((rudinBumpFunction_continuous (n + 1)).comp continuous_fst)).mul
        ((rudinBumpFunction_continuous n).comp continuous_snd)
    apply hc.continuousAt.congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.eventually hN] with q hq
    apply tsum_eq_sum
    intro n hn
    have hn' : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
    rw [hq n hn', hq (n + 1) (hn'.trans (Nat.le_succ n)), sub_self, zero_mul]
  · obtain ⟨N, hN⟩ := rudinBumpFunction_local_cutoff hy
    have hc : Continuous (fun q : ℝ × ℝ => ∑ n ∈ Finset.range N,
        (rudinBumpFunction n q.1 - rudinBumpFunction (n + 1) q.1) * rudinBumpFunction n q.2) := by
      apply continuous_finsetSum
      intro n _
      exact (((rudinBumpFunction_continuous n).comp continuous_fst).sub
        ((rudinBumpFunction_continuous (n + 1)).comp continuous_fst)).mul
        ((rudinBumpFunction_continuous n).comp continuous_snd)
    apply hc.continuousAt.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.eventually hN] with q hq
    apply tsum_eq_sum
    intro n hn
    rw [hq n (Nat.le_of_not_gt (by simpa using hn)), mul_zero]

/-- 8.9(a): both iterated integrals exist and differ, although the exact printed
bump series is continuous away from the corner. Its absolute double integral is infinite. -/
theorem rudin_bump_counterexample :
    (∀ x, Integrable (rudinBumpSeries x) bumpIntervalMeasure) ∧
    (∀ y, Integrable (fun x => rudinBumpSeries x y) bumpIntervalMeasure) ∧
    Integrable (fun x => ∫ y, rudinBumpSeries x y ∂bumpIntervalMeasure) bumpIntervalMeasure ∧
    Integrable (fun y => ∫ x, rudinBumpSeries x y ∂bumpIntervalMeasure) bumpIntervalMeasure ∧
    (∫ x, ∫ y, rudinBumpSeries x y ∂bumpIntervalMeasure ∂bumpIntervalMeasure) = 1 ∧
    (∫ y, ∫ x, rudinBumpSeries x y ∂bumpIntervalMeasure ∂bumpIntervalMeasure) = 0 ∧
    (∀ p : ℝ × ℝ, p ≠ (1, 1) → ContinuousAt (Function.uncurry rudinBumpSeries) p) ∧
    (∫⁻ p, ‖rudinBumpSeries p.1 p.2‖ₑ
      ∂bumpIntervalMeasure.prod bumpIntervalMeasure) = ∞ := by
  have hi : (∫ x, ∫ y, rudinBumpSeries x y ∂bumpIntervalMeasure ∂bumpIntervalMeasure) = 1 := by
    simp_rw [rudinBumpSeries_integral_right]
    exact rudinBumpFunction_integral 0
  have hj : (∫ y, ∫ x, rudinBumpSeries x y ∂bumpIntervalMeasure ∂bumpIntervalMeasure) = 0 := by
    simp_rw [rudinBumpSeries_integral_left, integral_zero]
  refine ⟨rudinBumpSeries_sections_integrable.1, rudinBumpSeries_sections_integrable.2,
    ?_, ?_, hi, hj, fun _ hp => rudinBumpSeries_continuousAt hp, ?_⟩
  · simp_rw [rudinBumpSeries_integral_right]
    exact rudinBumpFunction_integrable 0
  · simp_rw [rudinBumpSeries_integral_left]
    exact integrable_zero _ _ _
  · by_contra h
    have hint : Integrable (Function.uncurry rudinBumpSeries)
        (bumpIntervalMeasure.prod bumpIntervalMeasure) :=
      ⟨rudinBumpSeries_measurable.aestronglyMeasurable,
        hasFiniteIntegral_iff_enorm.mpr (lt_top_iff_ne_top.mpr h)⟩
    have he := integral_integral_swap hint
    rw [hi, hj] at he
    exact one_ne_zero he

/-- The divergent iterated absolute integral displayed in 8.9(a). -/
theorem rudin_bump_absolute_iterated :
    (∫⁻ x, ∫⁻ y, ‖rudinBumpSeries x y‖ₑ ∂bumpIntervalMeasure ∂bumpIntervalMeasure) = ∞ := by
  rw [← lintegral_prod (fun p : ℝ × ℝ => ‖rudinBumpSeries p.1 p.2‖ₑ)
    rudinBumpSeries_measurable.enorm.aemeasurable]
  exact rudin_bump_counterexample.2.2.2.2.2.2.2

/-- The exceptional corner really is a discontinuity; all other points are covered above. -/
theorem rudin_bump_not_continuousAt_corner :
    ¬ ContinuousAt (Function.uncurry rudinBumpSeries) (1, 1) := by
  intro hc
  have hcont : Continuous (Function.uncurry rudinBumpSeries) :=
    continuous_iff_continuousAt.mpr (fun p => by
      by_cases hp : p = (1, 1)
      · simpa [hp] using hc
      · exact rudinBumpSeries_continuousAt hp)
  have hi : IntegrableOn (Function.uncurry rudinBumpSeries)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ((volume : Measure ℝ).prod volume) :=
    hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  change Integrable (Function.uncurry rudinBumpSeries)
    (((volume : Measure ℝ).prod volume).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) at hi
  rw [← Measure.prod_restrict] at hi
  have h := integral_integral_swap hi
  have h₁ := rudin_bump_counterexample.2.2.2.2.1
  have h₀ := rudin_bump_counterexample.2.2.2.2.2.1
  rw [h₁, h₀] at h
  exact one_ne_zero h

end RudinRCA.Chapter08
