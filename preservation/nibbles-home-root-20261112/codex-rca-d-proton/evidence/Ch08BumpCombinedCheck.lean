module
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public section

-- SOURCE: Ch08BumpExample.lean


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

-- SOURCE: Ch08Sierpinski.lean


open Set MeasureTheory
open scoped ENNReal

namespace RudinRCA.Chapter08

variable {X W : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
  [LinearOrder W] (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- The set in 8.9(c), using the well-order supplied in Rudin's conditional construction. -/
def sierpinskiSet (j : X ≃ W) : Set (X × X) := {p | j p.1 < j p.2}

/-- 8.9(c), conditional form with precisely the countable-predecessor well-order that
Rudin takes from CH. No continuum-hypothesis axiom is introduced. Instantiating `X`
with the unit interval and its Lebesgue probability measure gives the printed example.
The additional CH-to-existence implication is not asserted by this theorem. -/
theorem sierpinski_counterexample (j : X ≃ W)
    (_hw : WellFounded ((· < ·) : W → W → Prop))
    (hcount : ∀ w : W, (Set.Iio w).Countable) :
    (∀ x : X, MeasurableSet {y | (x, y) ∈ sierpinskiSet j} ∧
      μ {y | (x, y) ∈ sierpinskiSet j} = 1) ∧
    (∀ y : X, MeasurableSet {x | (x, y) ∈ sierpinskiSet j} ∧
      μ {x | (x, y) ∈ sierpinskiSet j} = 0) ∧
    (∫⁻ x, μ {y | (x, y) ∈ sierpinskiSet j} ∂μ) = 1 ∧
    (∫⁻ y, μ {x | (x, y) ∈ sierpinskiSet j} ∂μ) = 0 ∧
    ¬ MeasurableSet (sierpinskiSet j) := by
  classical
  have hpred (y : X) : {x : X | j x < j y}.Countable :=
    (hcount (j y)).preimage j.injective
  have hsucc (x : X) : ({y : X | j x < j y}ᶜ).Countable := by
    have heq : {y : X | j x < j y}ᶜ = {y : X | j y < j x} ∪ {x} := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union,
        Set.mem_singleton_iff, not_lt, le_iff_lt_or_eq, j.injective.eq_iff]
    rw [heq]
    exact (hpred x).union (Set.countable_singleton x)
  have hx (x : X) : MeasurableSet {y | (x, y) ∈ sierpinskiSet j} ∧
      μ {y | (x, y) ∈ sierpinskiSet j} = 1 := by
    constructor
    · simpa only [compl_compl, sierpinskiSet, Set.mem_ofPred_eq] using (hsucc x).measurableSet.compl
    · have h := measure_compl (hsucc x).measurableSet
        (measure_ne_top μ ({y : X | j x < j y}ᶜ))
      simpa only [compl_compl, (hsucc x).measure_zero μ, measure_univ, tsub_zero, sierpinskiSet, Set.mem_ofPred_eq] using h
  have hy (y : X) : MeasurableSet {x | (x, y) ∈ sierpinskiSet j} ∧
      μ {x | (x, y) ∈ sierpinskiSet j} = 0 :=
    ⟨(hpred y).measurableSet, (hpred y).measure_zero μ⟩
  have hxint : (∫⁻ x, μ {y | (x, y) ∈ sierpinskiSet j} ∂μ) = 1 := by
    calc
      _ = ∫⁻ _ : X, (1 : ℝ≥0∞) ∂μ := lintegral_congr (fun x => (hx x).2)
      _ = 1 := by simp
  have hyint : (∫⁻ y, μ {x | (x, y) ∈ sierpinskiSet j} ∂μ) = 0 := by
    calc
      _ = ∫⁻ _ : X, (0 : ℝ≥0∞) ∂μ := lintegral_congr (fun y => (hy y).2)
      _ = 0 := by simp
  refine ⟨hx, hy, hxint, hyint, ?_⟩
  intro hQ
  have h := (Measure.prod_apply (μ := μ) (ν := μ) hQ).symm.trans
    (Measure.prod_apply_symm (μ := μ) (ν := μ) hQ)
  change (∫⁻ x, μ {y | (x, y) ∈ sierpinskiSet j} ∂μ) =
    (∫⁻ y, μ {x | (x, y) ∈ sierpinskiSet j} ∂μ) at h
  rw [hxint, hyint] at h
  exact one_ne_zero h


/-- A concrete well-order of first uncountable cardinality. -/
abbrev SierpinskiOrder := (Cardinal.aleph 1 : Cardinal.{0}).ord.ToType

/-- The set-theoretic step used in 8.9(c), explicitly conditional on CH.
The hypothesis is a proposition, never an added axiom. -/
theorem ch_unitInterval_wellOrder
    (hCH : Cardinal.continuum = (Cardinal.aleph 1 : Cardinal.{0})) :
    Nonempty ((Set.Icc (0 : ℝ) 1) ≃ SierpinskiOrder) ∧
    WellFounded ((· < ·) : SierpinskiOrder → SierpinskiOrder → Prop) ∧
    (∀ w : SierpinskiOrder, (Set.Iio w).Countable) := by
  constructor
  · apply Cardinal.eq.mp
    rw [Cardinal.mk_Icc_real zero_lt_one]
    exact hCH.trans (Cardinal.mk_ord_toType _).symm
  · constructor
    · exact wellFounded_lt
    · intro w
      apply Cardinal.le_aleph0_iff_set_countable.mp
      apply Cardinal.lt_aleph_one_iff.mp
      have ho : (Cardinal.mk SierpinskiOrder).ord = Ordinal.type ((· < ·) : SierpinskiOrder → SierpinskiOrder → Prop) := by
        simp only [SierpinskiOrder, Cardinal.mk_ord_toType, Ordinal.type_toType]
      have h := Cardinal.mk_Iio_lt w ho
      simpa only [SierpinskiOrder, Cardinal.mk_ord_toType] using h

/-- The literal unit interval used in the printed counterexample. -/
abbrev SierpinskiInterval := Set.Icc (0 : ℝ) 1

/-- Lebesgue measure restricted to the unit interval and regarded as a measure on it. -/
noncomputable def sierpinskiIntervalMeasure : Measure SierpinskiInterval :=
  (volume : Measure ℝ).comap Subtype.val

instance sierpinskiInterval_probability : IsProbabilityMeasure sierpinskiIntervalMeasure where
  measure_univ := by
    change ((volume : Measure ℝ).comap (Subtype.val : SierpinskiInterval → ℝ)) Set.univ = 1
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply]
    simp only [Set.image_univ, Subtype.range_coe_subtype, ofPred_mem_eq]
    change volume (Set.Icc (0 : ℝ) 1) = 1
    simp only [Real.volume_Icc, sub_zero, ENNReal.ofReal_one]

instance sierpinskiInterval_nullSingletons : NullSingletonClass sierpinskiIntervalMeasure where
  measure_singleton x := by
    change ((volume : Measure ℝ).comap (Subtype.val : SierpinskiInterval → ℝ)) {x} = 0
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply]
    simp

/-- The unit interval with the completed Lebesgue σ-algebra, as in Rudin. -/
abbrev CompletedSierpinskiInterval :=
  NullMeasurableSpace SierpinskiInterval sierpinskiIntervalMeasure

noncomputable abbrev completeSierpinskiIntervalMeasure : Measure CompletedSierpinskiInterval :=
  sierpinskiIntervalMeasure.completion

instance completedSierpinskiInterval_probability :
    IsProbabilityMeasure completeSierpinskiIntervalMeasure where
  measure_univ := by
    change sierpinskiIntervalMeasure Set.univ = 1
    exact measure_univ

instance completedSierpinskiInterval_nullSingletons :
    NullSingletonClass completeSierpinskiIntervalMeasure where
  measure_singleton x := by
    change sierpinskiIntervalMeasure {x} = 0
    exact @measure_singleton SierpinskiInterval _ sierpinskiIntervalMeasure
      sierpinskiInterval_nullSingletons x

/-- 8.9(c) on the unit square, with CH as an explicit hypothesis. The section integrals
are those of the characteristic function of `Q`, because each section is measurable. -/
theorem unit_square_sierpinski_under_CH
    (hCH : Cardinal.continuum = (Cardinal.aleph 1 : Cardinal.{0})) :
    ∃ Q : Set (CompletedSierpinskiInterval × CompletedSierpinskiInterval),
      (∀ x : CompletedSierpinskiInterval, MeasurableSet {y | (x, y) ∈ Q} ∧
        completeSierpinskiIntervalMeasure {y | (x, y) ∈ Q} = 1) ∧
      (∀ y : CompletedSierpinskiInterval, MeasurableSet {x | (x, y) ∈ Q} ∧
        completeSierpinskiIntervalMeasure {x | (x, y) ∈ Q} = 0) ∧
      (∫⁻ x, completeSierpinskiIntervalMeasure {y | (x, y) ∈ Q} ∂completeSierpinskiIntervalMeasure) = 1 ∧
      (∫⁻ y, completeSierpinskiIntervalMeasure {x | (x, y) ∈ Q} ∂completeSierpinskiIntervalMeasure) = 0 ∧
      ¬ MeasurableSet Q := by
  obtain ⟨⟨j⟩, hw, hc⟩ := ch_unitInterval_wellOrder hCH
  exact ⟨sierpinskiSet j, sierpinski_counterexample completeSierpinskiIntervalMeasure j hw hc⟩

/-- The sections in Sierpinski's construction are Borel sets in the literal unit
interval, which is stronger than measurability in its Lebesgue completion. This
companion retains the Borel statement explicitly alongside the completed endpoint. -/
theorem unit_square_sierpinski_borel_sections_under_CH
    (hCH : Cardinal.continuum = (Cardinal.aleph 1 : Cardinal.{0})) :
    ∃ Q : Set (SierpinskiInterval × SierpinskiInterval),
      (∀ x : SierpinskiInterval,
        @MeasurableSet SierpinskiInterval (borel SierpinskiInterval) {y | (x, y) ∈ Q} ∧
          sierpinskiIntervalMeasure {y | (x, y) ∈ Q} = 1) ∧
      (∀ y : SierpinskiInterval,
        @MeasurableSet SierpinskiInterval (borel SierpinskiInterval) {x | (x, y) ∈ Q} ∧
          sierpinskiIntervalMeasure {x | (x, y) ∈ Q} = 0) ∧
      (∫⁻ x, sierpinskiIntervalMeasure {y | (x, y) ∈ Q} ∂sierpinskiIntervalMeasure) = 1 ∧
      (∫⁻ y, sierpinskiIntervalMeasure {x | (x, y) ∈ Q} ∂sierpinskiIntervalMeasure) = 0 ∧
      ¬ MeasurableSet Q := by
  obtain ⟨⟨j⟩, hw, hc⟩ := ch_unitInterval_wellOrder hCH
  have H := sierpinski_counterexample sierpinskiIntervalMeasure j hw hc
  have hb : (inferInstance : MeasurableSpace SierpinskiInterval) = borel SierpinskiInterval :=
    BorelSpace.measurable_eq
  refine ⟨sierpinskiSet j, ?_, ?_, H.2.2.1, H.2.2.2.1, H.2.2.2.2⟩
  · intro x
    refine ⟨?_, (H.1 x).2⟩
    rw [← hb]
    exact (H.1 x).1
  · intro y
    refine ⟨?_, (H.2.1 y).2⟩
    rw [← hb]
    exact (H.2.1 y).1

end RudinRCA.Chapter08

-- SOURCE: Ch08MaximalConstant.lean

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
    have h := tendsto_const_nhds.add
      (tendsto_inv_atTop_zero.comp (tendsto_id.atTop_sub_const (1 : ℝ)))
    apply (show Tendsto (fun p : ℝ => 1 + (p - 1)⁻¹) atTop (𝓝 1) by simpa using h).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with p hp
    field_simp [(sub_pos.mpr hp).ne']
    ring
  have hc : Tendsto (fun p : ℝ => (A * Real.exp 1) ^ (1 / p)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := A * Real.exp 1)).rpow hi
      (Or.inl (ne_of_gt (mul_pos hA (Real.exp_pos _))))
  have hqp : Tendsto (fun p : ℝ => (p / (p - 1)) ^ (1 / p)) atTop (𝓝 1) := by
    simpa using hq.rpow hi (Or.inl one_ne_zero)
  apply (by simpa using (hc.mul Real.tendsto_rpow_div).mul hqp).congr'
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
    simpa only [div_eq_mul_inv] using
      hid.pos_mul_atTop zero_lt_one (tendsto_inv_nhdsGT_zero.comp hd)
  have hb : Tendsto (fun p : ℝ => A * Real.exp 1 * p * (p / (p - 1)))
      (𝓝[>] 1) atTop := by
    have hc : Tendsto (fun p : ℝ => A * Real.exp 1 * p) (𝓝[>] 1)
        (𝓝 (A * Real.exp 1)) := by simpa using hid.const_mul (A * Real.exp 1)
    exact hc.pos_mul_atTop (mul_pos hA (Real.exp_pos _)) hq
  have hi : Tendsto (fun p : ℝ => 1 / p) (𝓝[>] 1) (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).div hid one_ne_zero
  have h := Real.tendsto_exp_atTop.comp
    ((Real.tendsto_log_atTop.comp hb).atTop_mul_pos zero_lt_one hi)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < p / (p - 1) := div_pos hp0 (sub_pos.mpr hp)
  exact (Real.rpow_def_of_pos (by positivity : 0 < A * Real.exp 1 * p * (p / (p - 1))) _).symm

end RudinRCA.Chapter08
