import RudinRCA.Chapter01
import RudinRCA.Chapter02
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Basic.ENNReal.Holder
import Mathlib.Basic.Real.ConjExponents
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.Linarith
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.UniformSpace.Completion

/-!
# Chapter 3: $L^p$-Spaces

Formalization of Chapter 3 (nodes `3.1`–`3.17`, printed pp. 61–71) of Walter Rudin,
*Real and Complex Analysis* (3rd ed., McGraw-Hill, 1987), inventoried in
`INVENTORY-CH03.md`.

Fidelity disclosures:
* **Definition 3.7 (`E-3.7`, `QUEUE.md` §3.7):** Rudin's printed threshold set ranges
  over all real `α` without a nonnegativity floor, making it unbounded below on the
  identically zero measure (`definition_3_7_zero_measure_counterexample`). We retain
  the scaffolded counterexample and explicitly repaired `ℝ≥0∞`-threshold definition
  (`correctedEssentialSupremum`, `correctedLinftyNorm`, `CorrectedBookMemLinfty`),
  prove agreement with the literal real-threshold infimum on every nonzero measure,
  and reference the repaired convention explicitly in every downstream $L^\infty$
  statement (`3.8`–`3.12`, `3.15`).
* **Theorem 3.14:** Because the Riesz representation package `2.14` remains pending in
  `Chapter02.lean`, `3.14` is proved directly from Urysohn's lemma (`Chapter02.lemma_2_12`)
  and simple-function density (`3.13`) under the explicit `2.14(a–d)` Borel/regularity
  hypotheses already formalized in `Chapter02.lean` (together with completion transfer
  to `Chapter01.completedMeasure` and specialization to `Chapter02.BookRegularBorelMeasure`
  and `[μ.Regular]`).
-/

namespace RudinRCA.Chapter03

open MeasureTheory Set
open scoped ENNReal

/-- The threshold set printed in 3.7, specialized to the zero function and zero
measure on a singleton, has no real lower bound. Thus its real infimum cannot
be used as a definition of a nonnegative norm. -/
theorem definition_3_7_zero_measure_counterexample :
    ¬ BddBelow {a : ℝ | (0 : Measure Unit) {_x | a < (0 : ℝ)} = 0} := by
  intro h
  obtain ⟨b, hb⟩ := h
  have hbad : b ≤ b - 1 := hb (by simp)
  linarith

/-- Explicit correction of 3.7: take thresholds in the complete nonnegative
extended reals. This is a correction, not a silent restatement of the book. -/
noncomputable def correctedEssentialSupremum {X : Type*} [MeasurableSpace X]
    (g : X → ℝ≥0∞) (μ : Measure X) : ℝ≥0∞ := essSup g μ

/-- The corrected threshold construction matches the measure-zero formula. -/
theorem correctedEssentialSupremum_eq_sInf {X : Type*} [MeasurableSpace X]
    (g : X → ℝ≥0∞) (μ : Measure X) :
    correctedEssentialSupremum g μ = sInf {a : ℝ≥0∞ | μ {x | a < g x} = 0} :=
  essSup_eq_sInf μ g

/-- The corrected value is the least almost-everywhere upper bound. -/
theorem correctedEssentialSupremum_le_iff {X : Type*} [MeasurableSpace X]
    (g : X → ℝ≥0∞) (μ : Measure X) (a : ℝ≥0∞) :
    correctedEssentialSupremum g μ ≤ a ↔ ∀ᵐ x ∂μ, g x ≤ a := by
  constructor
  · intro h
    filter_upwards [ENNReal.ae_le_essSup g] with x hx using hx.trans h
  · intro h
    exact essSup_le_of_ae_le a h

/-- In particular, the corrected norm convention handles zero measure. -/
theorem correctedEssentialSupremum_zero_measure {X : Type*} [MeasurableSpace X]
    (g : X → ℝ≥0∞) : correctedEssentialSupremum g (0 : Measure X) = 0 :=
  essSup_measure_zero

open Filter TopologicalSpace
open scoped NNReal Topology CompactlySupported ZeroAtInfty

/-! ## Section 3.1: Interval Convexity (printed p. 61) -/

/-- Rudin's open segment `(a, b) = {x ∈ ℝ | a < x < b}` for `-∞ ≤ a < b ≤ ∞`,
represented uniformly via endpoints `a b : EReal`. -/
def OpenSegment (a b : EReal) : Set ℝ :=
  {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}

theorem mem_openSegment_iff {a b : EReal} {x : ℝ} :
    x ∈ OpenSegment a b ↔ a < (x : EReal) ∧ (x : EReal) < b := Iff.rfl

theorem openSegment_coe_coe (a₀ b₀ : ℝ) :
    OpenSegment (a₀ : EReal) (b₀ : EReal) = Set.Ioo a₀ b₀ := by
  ext x
  simp [OpenSegment, EReal.coe_lt_coe_iff]

theorem openSegment_bot_coe (b₀ : ℝ) :
    OpenSegment ⊥ (b₀ : EReal) = Set.Iio b₀ := by
  ext x
  simp [OpenSegment, EReal.coe_lt_coe_iff, EReal.bot_lt_coe]

theorem openSegment_coe_top (a₀ : ℝ) :
    OpenSegment (a₀ : EReal) ⊤ = Set.Ioi a₀ := by
  ext x
  simp [OpenSegment, EReal.coe_lt_coe_iff, EReal.coe_lt_top]

theorem openSegment_bot_top :
    OpenSegment ⊥ ⊤ = Set.univ := by
  ext x
  simp [OpenSegment, EReal.bot_lt_coe, EReal.coe_lt_top]

theorem isOpen_openSegment (a b : EReal) : IsOpen (OpenSegment a b) := by
  have h1 : IsOpen {x : ℝ | a < (x : EReal)} := by
    induction a using EReal.rec with
    | bot =>
      convert isOpen_univ
      ext x
      simp [EReal.bot_lt_coe]
    | coe a₀ =>
      convert isOpen_Ioi (a := a₀)
      ext x
      simp [EReal.coe_lt_coe_iff]
    | top =>
      convert isOpen_empty
      ext x
      simp
  have h2 : IsOpen {x : ℝ | (x : EReal) < b} := by
    induction b using EReal.rec with
    | bot =>
      convert isOpen_empty
      ext x
      simp
    | coe b₀ =>
      convert isOpen_Iio (a := b₀)
      ext x
      simp [EReal.coe_lt_coe_iff]
    | top =>
      convert isOpen_univ
      ext x
      simp [EReal.coe_lt_top]
  exact h1.inter h2

theorem openSegment_ordConnected (a b : EReal) : (OpenSegment a b).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ⟨?_, ?_⟩⟩
  · exact hx.1.trans_le (EReal.coe_le_coe_iff.mpr hz.1)
  · exact (EReal.coe_le_coe_iff.mpr hz.2).trans_lt hy.2

theorem convex_openSegment (a b : EReal) : Convex ℝ (OpenSegment a b) :=
  (openSegment_ordConnected a b).convex

theorem nonempty_openSegment {a b : EReal} (hab : a < b) :
    (OpenSegment a b).Nonempty := by
  induction a using EReal.rec with
  | bot =>
    induction b using EReal.rec with
    | bot => exact absurd hab (lt_irrefl _)
    | coe b₀ =>
      refine ⟨b₀ - 1, ?_⟩
      rw [openSegment_bot_coe]
      simp
    | top =>
      refine ⟨0, ?_⟩
      rw [openSegment_bot_top]
      trivial
  | coe a₀ =>
    induction b using EReal.rec with
    | bot => exact absurd hab (not_lt_of_gt (EReal.bot_lt_coe a₀))
    | coe b₀ =>
      have hab₀ : a₀ < b₀ := EReal.coe_lt_coe_iff.mp hab
      refine ⟨(a₀ + b₀) / 2, ?_⟩
      rw [openSegment_coe_coe]
      exact ⟨by linarith, by linarith⟩
    | top =>
      refine ⟨a₀ + 1, ?_⟩
      rw [openSegment_coe_top]
      simp
  | top =>
    exact absurd hab (not_lt_of_ge le_top)

/-- RCA Definition 3.1 (printed p. 61): convexity of a real-valued function `φ` on `(a, b)`
(`-∞ ≤ a < b ≤ ∞`), written literally as
`φ ((1 - l) x + l y) ≤ (1 - l) φ x + l φ y` for `x, y ∈ (a, b)` and `0 ≤ l ≤ 1`. -/
def BookConvexOnSegment (a b : EReal) (φ : ℝ → ℝ) : Prop :=
  ∀ x ∈ OpenSegment a b, ∀ y ∈ OpenSegment a b, ∀ l : ℝ,
    0 ≤ l → l ≤ 1 → φ ((1 - l) * x + l * y) ≤ (1 - l) * φ x + l * φ y

/-- Exact bridge from Definition 3.1 to Mathlib's `ConvexOn ℝ (OpenSegment a b) φ`. -/
theorem definition_3_1_convexOn_iff (a b : EReal) (φ : ℝ → ℝ) :
    BookConvexOnSegment a b φ ↔ ConvexOn ℝ (OpenSegment a b) φ := by
  constructor
  · intro h
    refine ⟨convex_openSegment a b, ?_⟩
    intro x hx y hy u v hu hv huv
    have hv1 : v ≤ 1 := by linarith
    have hu_eq : u = 1 - v := by linarith
    subst hu_eq
    simpa [smul_eq_mul] using h x hx y hy v hv hv1
  · intro h x hx y hy l hl0 hl1
    have h1l : 0 ≤ 1 - l := sub_nonneg.mpr hl1
    have hsum : (1 - l) + l = 1 := sub_add_cancel 1 l
    simpa [smul_eq_mul] using h.2 hx hy h1l hl0 hsum

/-- RCA 3.1(2) (printed p. 61): convexity on `(a, b)` is equivalent to the adjacent
chord-slope inequality `(φ t - φ s) / (t - s) ≤ (φ u - φ t) / (u - t)` whenever
`a < s < t < u < b`. -/
theorem definition_3_1_chord_slope_iff (a b : EReal) (φ : ℝ → ℝ) :
    BookConvexOnSegment a b φ ↔
      ∀ s ∈ OpenSegment a b, ∀ t ∈ OpenSegment a b, ∀ u ∈ OpenSegment a b,
        s < t → t < u → (φ t - φ s) / (t - s) ≤ (φ u - φ t) / (u - t) := by
  rw [definition_3_1_convexOn_iff, convexOn_iff_slope_mono_adjacent]
  constructor
  · intro h s hs t _ht u hu hst htu
    exact h.2 hs hu hst htu
  · intro h
    refine ⟨convex_openSegment a b, fun x y z hx hz hxy hyz => ?_⟩
    have hy : y ∈ OpenSegment a b :=
      (openSegment_ordConnected a b).out hx hz ⟨hxy.le, hyz.le⟩
    exact h x hx y hy z hz hxy hyz

/-- RCA 3.1 derivative characterization (printed p. 61): if `φ` is differentiable at every
point of `(a, b)`, then `φ` is convex on `(a, b)` if and only if `φ'(s) ≤ φ'(t)` whenever
`a < s < t < b`. -/
theorem definition_3_1_deriv_monotone_iff (a b : EReal) (φ : ℝ → ℝ)
    (hdiff : ∀ x ∈ OpenSegment a b, DifferentiableAt ℝ φ x) :
    BookConvexOnSegment a b φ ↔
      ∀ s ∈ OpenSegment a b, ∀ t ∈ OpenSegment a b, s < t → deriv φ s ≤ deriv φ t := by
  rw [definition_3_1_convexOn_iff]
  constructor
  · intro hconv s hs t ht hst
    exact hconv.monotoneOn_deriv hdiff hs ht hst.le
  · intro hmono
    have hmonoOn : MonotoneOn (deriv φ) (OpenSegment a b) := by
      intro s hs t ht hst
      rcases eq_or_lt_of_le hst with rfl | hlt
      · exact le_rfl
      · exact hmono s hs t ht hlt
    exact MonotoneOn.convexOn_of_deriv (convex_openSegment a b)
      (fun x hx => (hdiff x hx).continuousAt.continuousWithinAt)
      (by
        rw [(isOpen_openSegment a b).interior_eq]
        exact fun x hx => (hdiff x hx).differentiableWithinAt)
      (by
        rw [(isOpen_openSegment a b).interior_eq]
        exact hmonoOn)

/-- RCA 3.1 second-derivative sufficiency (printed p. 61): nonnegative second derivative on
`(a, b)` implies convexity on `(a, b)`. -/
theorem definition_3_1_of_deriv2_nonneg (a b : EReal) (φ : ℝ → ℝ)
    (hdiff1 : ∀ x ∈ OpenSegment a b, DifferentiableAt ℝ φ x)
    (hdiff2 : ∀ x ∈ OpenSegment a b, DifferentiableAt ℝ (deriv φ) x)
    (hnonneg : ∀ x ∈ OpenSegment a b, 0 ≤ deriv (deriv φ) x) :
    BookConvexOnSegment a b φ := by
  rw [definition_3_1_deriv_monotone_iff a b φ hdiff1]
  have hmonoOn : MonotoneOn (deriv φ) (OpenSegment a b) :=
    monotoneOn_of_deriv_nonneg (convex_openSegment a b)
      (fun x hx => (hdiff2 x hx).continuousAt.continuousWithinAt)
      (by
        rw [(isOpen_openSegment a b).interior_eq]
        exact fun x hx => (hdiff2 x hx).differentiableWithinAt)
      (by
        rw [(isOpen_openSegment a b).interior_eq]
        exact hnonneg)
  intro s hs t ht hst
  exact hmonoOn hs ht hst.le

/-- RCA 3.1 exponential example (printed p. 61): `t ↦ exp t` is convex on `(-∞, ∞)`. -/
theorem definition_3_1_exp_convex : BookConvexOnSegment ⊥ ⊤ Real.exp := by
  rw [definition_3_1_convexOn_iff, openSegment_bot_top]
  exact convexOn_exp

/-- Canonical summary declaration for RCA 3.1 (printed p. 61). -/
theorem node3_1 (a b : EReal) (φ : ℝ → ℝ) :
    (BookConvexOnSegment a b φ ↔ ConvexOn ℝ (OpenSegment a b) φ) ∧
    (BookConvexOnSegment a b φ ↔
      ∀ s ∈ OpenSegment a b, ∀ t ∈ OpenSegment a b, ∀ u ∈ OpenSegment a b,
        s < t → t < u → (φ t - φ s) / (t - s) ≤ (φ u - φ t) / (u - t)) ∧
    ((∀ x ∈ OpenSegment a b, DifferentiableAt ℝ φ x) →
      (BookConvexOnSegment a b φ ↔
        ∀ s ∈ OpenSegment a b, ∀ t ∈ OpenSegment a b, s < t → deriv φ s ≤ deriv φ t)) ∧
    BookConvexOnSegment ⊥ ⊤ Real.exp :=
  ⟨definition_3_1_convexOn_iff a b φ,
    definition_3_1_chord_slope_iff a b φ,
    definition_3_1_deriv_monotone_iff a b φ,
    definition_3_1_exp_convex⟩

/-! ## Section 3.2: Convexity Implies Continuity (printed pp. 61–62) -/

/-- RCA Theorem 3.2 (printed pp. 61–62): if `φ` is convex on `(a, b)` (`-∞ ≤ a < b ≤ ∞`),
then `φ` is continuous on `(a, b)`. -/
theorem theorem_3_2 {a b : EReal} {φ : ℝ → ℝ} (hφ : BookConvexOnSegment a b φ) :
    ContinuousOn φ (OpenSegment a b) :=
  ((definition_3_1_convexOn_iff a b φ).mp hφ).continuousOn (isOpen_openSegment a b)

/-- Specialization of Theorem 3.2 to finite open intervals `(a₀, b₀)`. -/
theorem theorem_3_2_Ioo {a₀ b₀ : ℝ} {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ (Set.Ioo a₀ b₀) φ) :
    ContinuousOn φ (Set.Ioo a₀ b₀) :=
  hφ.continuousOn isOpen_Ioo

/-- RCA 3.2 closing remark (printed p. 62): Theorem 3.2 fails on closed intervals `[a, b]`;
for instance `φ(x) = 0` on `[0, 1)` and `φ(1) = 1` is convex on `[0, 1]` but discontinuous at `1`. -/
theorem theorem_3_2_closed_interval_counterexample :
    ∃ φ : ℝ → ℝ, ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ ∧ ¬ ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
  let φ : ℝ → ℝ := fun x => if x < 1 then 0 else 1
  refine ⟨φ, ⟨convex_Icc 0 1, ?_⟩, ?_⟩
  · intro x hx y hy u v hu hv huv
    simp only [φ, smul_eq_mul]
    by_cases hxy : u * x + v * y < 1
    · rw [ite_eq_left hxy]
      have h1 : 0 ≤ (if x < 1 then (0 : ℝ) else 1) := by split_ifs <;> norm_num
      have h2 : 0 ≤ (if y < 1 then (0 : ℝ) else 1) := by split_ifs <;> norm_num
      positivity
    · rw [ite_eq_right hxy]
      have hge1 : 1 ≤ u * x + v * y := not_lt.mp hxy
      by_cases hx1 : x < 1
      · by_cases hy1 : y < 1
        · exfalso
          rcases eq_or_lt_of_le hu with rfl | hu_pos
          · have hv1 : v = 1 := by linarith
            subst hv1
            linarith
          · have hlt1 : u * x < u * 1 := mul_lt_mul_of_pos_left hx1 hu_pos
            have hle2 : v * y ≤ v * 1 := mul_le_mul_of_nonneg_left hy.2 hv
            linarith
        · rw [ite_eq_left hx1, ite_eq_right hy1]
          have hy_eq : y = 1 := le_antisymm hy.2 (not_lt.mp hy1)
          subst hy_eq
          have hu0 : u = 0 := by
            by_contra hne
            have hu_pos : 0 < u := lt_of_le_of_ne hu (Ne.symm hne)
            have hlt1 : u * x < u * 1 := mul_lt_mul_of_pos_left hx1 hu_pos
            linarith
          linarith
      · by_cases hy1 : y < 1
        · rw [ite_eq_right hx1, ite_eq_left hy1]
          have hx_eq : x = 1 := le_antisymm hx.2 (not_lt.mp hx1)
          subst hx_eq
          have hv0 : v = 0 := by
            by_contra hne
            have hv_pos : 0 < v := lt_of_le_of_ne hv (Ne.symm hne)
            have hlt2 : v * y < v * 1 := mul_lt_mul_of_pos_left hy1 hv_pos
            linarith
          linarith
        · rw [ite_eq_right hx1, ite_eq_right hy1]
          linarith
  · intro hcont
    have h1 : ContinuousWithinAt φ (Set.Icc 0 1) 1 := hcont 1 ⟨by norm_num, le_rfl⟩
    have hseq : Tendsto (fun n : ℕ => 1 - (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝[Set.Icc 0 1] 1) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun n => ⟨?_, ?_⟩⟩
      · simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
      · have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
          rw [div_le_one hpos]
          linarith
        linarith
      · have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have : 0 < (1 : ℝ) / ((n : ℝ) + 1) := div_pos zero_lt_one hpos
        linarith
    have hval : (fun n : ℕ => φ (1 - (1 : ℝ) / ((n : ℝ) + 1))) = fun _ => 0 := by
      ext n
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hdiv : 0 < (1 : ℝ) / ((n : ℝ) + 1) := div_pos zero_lt_one hpos
      have hlt : 1 - (1 : ℝ) / ((n : ℝ) + 1) < 1 := by linarith
      exact ite_eq_left hlt
    have ht1 : Tendsto (fun n : ℕ => φ (1 - (1 : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 (φ 1)) :=
      h1.tendsto.comp hseq
    rw [hval] at ht1
    have h01 : (0 : ℝ) = φ 1 := tendsto_nhds_unique tendsto_const_nhds ht1
    simp [φ] at h01

/-- Canonical summary declaration for RCA Theorem 3.2 (printed pp. 61–62). -/
theorem theorem3_2 {a b : EReal} {φ : ℝ → ℝ} (hφ : BookConvexOnSegment a b φ) :
    ContinuousOn φ (OpenSegment a b) :=
  theorem_3_2 hφ

/-! ## Section 3.4: Conjugate Exponents (printed p. 63) -/

/-- RCA Definition 3.4 (printed p. 63): finite real conjugate exponents `p, q > 0` satisfying
`p + q = p * q`. -/
def BookRealConjugateExponents (p q : ℝ) : Prop :=
  0 < p ∧ 0 < q ∧ p + q = p * q

theorem definition_3_4_inv_iff {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    p + q = p * q ↔ 1 / p + 1 / q = 1 := by
  have hp0 : p ≠ 0 := hp.ne'
  have hq0 : q ≠ 0 := hq.ne'
  constructor
  · intro h
    field_simp [hp0, hq0]
    linarith
  · intro h
    field_simp [hp0, hq0] at h
    linarith

theorem definition_3_4_bounds {p q : ℝ} (hpq : BookRealConjugateExponents p q) :
    1 < p ∧ 1 < q ∧ q = p / (p - 1) := by
  rcases hpq with ⟨hp, hq, heq⟩
  have hinv : 1 / p + 1 / q = 1 := (definition_3_4_inv_iff hp hq).mp heq
  have hp1 : 1 < p := by
    by_contra hle
    have hp_le : p ≤ 1 := not_lt.mp hle
    have hge1 : 1 ≤ 1 / p := one_le_one_div hp hp_le
    have hqpos : 0 < 1 / q := div_pos zero_lt_one hq
    linarith
  have hq1 : 1 < q := by
    by_contra hle
    have hq_le : q ≤ 1 := not_lt.mp hle
    have hge1 : 1 ≤ 1 / q := one_le_one_div hq hq_le
    have hppos : 0 < 1 / p := div_pos zero_lt_one hp
    linarith
  refine ⟨hp1, hq1, ?_⟩
  have hp_sub : p - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
  apply eq_div_of_mul_eq hp_sub
  linarith

/-- Exact bridge from Definition 3.4's finite real conjugate exponents to Mathlib's
`Real.HolderConjugate`. -/
theorem definition_3_4_holderConjugate_iff (p q : ℝ) :
    BookRealConjugateExponents p q ↔ p.HolderConjugate q := by
  constructor
  · intro hpq
    obtain ⟨hp1, _hq1, _⟩ := definition_3_4_bounds hpq
    have hinv : p⁻¹ + q⁻¹ = 1 := by
      simpa [one_div] using (definition_3_4_inv_iff hpq.1 hpq.2.1).mp hpq.2.2
    exact (Real.holderConjugate_iff).mpr ⟨hp1, hinv⟩
  · intro h
    have hinv : 1 / p + 1 / q = 1 := by
      simpa [one_div] using h.inv_add_inv_eq_one
    exact ⟨h.pos, h.symm.pos, (definition_3_4_inv_iff h.pos h.symm.pos).mpr hinv⟩

theorem definition_3_4_symm {p q : ℝ} (h : BookRealConjugateExponents p q) :
    BookRealConjugateExponents q p :=
  ⟨h.2.1, h.1, by linarith [h.2.2]⟩

/-- RCA 3.4 remark (printed p. 63): `2` is self-conjugate (`p = 2 ↔ q = 2`). -/
theorem definition_3_4_self_conjugate :
    BookRealConjugateExponents 2 2 ∧
      ∀ {p q : ℝ}, BookRealConjugateExponents p q → (p = 2 ↔ q = 2) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, ?_⟩
  intro p q ⟨_hp, _hq, heq⟩
  constructor <;> rintro rfl <;> linarith

/-- RCA 3.4 limiting remark (printed p. 63): as `p → 1⁺`, `q = p / (p - 1) → +∞`. -/
theorem definition_3_4_tendsto_infty :
    Tendsto (fun p : ℝ => p / (p - 1)) (𝓝[>] 1) atTop := by
  have hsub0 : Tendsto (fun p : ℝ => p - 1) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) - 1)) :=
    tendsto_id.sub tendsto_const_nhds
  have hsub : Tendsto (fun p : ℝ => p - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, eventually_nhdsWithin_of_forall fun p (hp : 1 < p) => sub_pos.mpr hp⟩
    simpa using hsub0.mono_left nhdsWithin_le_nhds
  have hinv : Tendsto (fun p : ℝ => (p - 1)⁻¹) (𝓝[>] 1) atTop :=
    tendsto_inv_nhdsGT_zero.comp hsub
  have hadd : Tendsto (fun p : ℝ => (1 : ℝ) + (p - 1)⁻¹) (𝓝[>] 1) atTop :=
    tendsto_atTop_add_const_left _ 1 hinv
  refine hadd.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p (hp : 1 < p)
  have hp0 : p - 1 ≠ 0 := sub_ne_zero.mpr hp.ne'
  field_simp [hp0]
  ring

/-- RCA 3.4 extended conjugate exponents in `[1, ∞]` (`ℝ≥0∞`), combining finite pairs
`(p, q)` with the limiting endpoint pairs `(1, ∞)` and `(∞, 1)`. -/
def BookConjugateExponents (p q : ℝ≥0∞) : Prop :=
  (p = 1 ∧ q = ∞) ∨ (p = ∞ ∧ q = 1) ∨
    ∃ p₀ q₀ : ℝ, BookRealConjugateExponents p₀ q₀ ∧ p = ENNReal.ofReal p₀ ∧ q = ENNReal.ofReal q₀

/-- Exact equivalence between `BookConjugateExponents`, `ENNReal.HolderConjugate`, and
`1 / p + 1 / q = 1` in `ℝ≥0∞`. -/
theorem definition_3_4_extended_iff (p q : ℝ≥0∞) :
    BookConjugateExponents p q ↔ ENNReal.HolderConjugate p q := by
  rw [ENNReal.holderConjugate_iff]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨p₀, q₀, hpq, rfl, rfl⟩)
    · simp
    · simp
    · obtain ⟨hp1, hq1, _⟩ := definition_3_4_bounds hpq
      have hp0 : 0 < p₀ := by linarith
      have hq0 : 0 < q₀ := by linarith
      have hinv : 1 / p₀ + 1 / q₀ = 1 := (definition_3_4_inv_iff hp0 hq0).mp hpq.2.2
      rw [← ENNReal.ofReal_inv_of_pos hp0, ← ENNReal.ofReal_inv_of_pos hq0,
        ← ENNReal.ofReal_add (inv_nonneg.mpr hp0.le) (inv_nonneg.mpr hq0.le)]
      simpa [one_div] using congrArg ENNReal.ofReal hinv
  · intro h
    have hpq_inst : ENNReal.HolderConjugate p q := ENNReal.holderConjugate_iff.mpr h
    by_cases hp_top : p = ∞
    · exact Or.inr (Or.inl ⟨hp_top, (ENNReal.HolderConjugate.eq_top_iff_eq_one p q).mp hp_top⟩)
    · by_cases hq_top : q = ∞
      · exact Or.inl ⟨(ENNReal.HolderConjugate.eq_top_iff_eq_one q p).mp hq_top, hq_top⟩
      · right; right
        have hp1 : 1 < p :=
          (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mp (lt_top_iff_ne_top.mpr hq_top)
        have hq1 : 1 < q :=
          (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp (lt_top_iff_ne_top.mpr hp_top)
        have hp_ne0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
        have hq_ne0 : q ≠ 0 := (zero_lt_one.trans hq1).ne'
        refine ⟨p.toReal, q.toReal, ?_, (ENNReal.ofReal_toReal hp_top).symm,
          (ENNReal.ofReal_toReal hq_top).symm⟩
        have hp0 : 0 < p.toReal := ENNReal.toReal_pos hp_ne0 hp_top
        have hq0 : 0 < q.toReal := ENNReal.toReal_pos hq_ne0 hq_top
        refine ⟨hp0, hq0, (definition_3_4_inv_iff hp0 hq0).mpr ?_⟩
        have hto : (p⁻¹ + q⁻¹).toReal = (1 : ℝ≥0∞).toReal := congrArg ENNReal.toReal h
        rw [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hp_ne0) (ENNReal.inv_ne_top.mpr hq_ne0),
          ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_one] at hto
        simpa [one_div] using hto

/-- Canonical summary declaration for RCA Definition 3.4 (printed p. 63). -/
theorem node3_4 (p q : ℝ) (pe qe : ℝ≥0∞) :
    (BookRealConjugateExponents p q ↔ p.HolderConjugate q) ∧
    (BookRealConjugateExponents p q → 1 < p ∧ 1 < q ∧ q = p / (p - 1)) ∧
    BookRealConjugateExponents 2 2 ∧
    Tendsto (fun r : ℝ => r / (r - 1)) (𝓝[>] 1) atTop ∧
    (BookConjugateExponents pe qe ↔ ENNReal.HolderConjugate pe qe) :=
  ⟨definition_3_4_holderConjugate_iff p q,
    definition_3_4_bounds,
    definition_3_4_self_conjugate.1,
    definition_3_4_tendsto_infty,
    definition_3_4_extended_iff pe qe⟩

/-! ## Section 3.6: Finite-Exponent $L^p$ Norm and Space (printed p. 65) -/

/-- RCA Definition 3.6 (printed p. 65): for `0 < p < ∞` and `f : X → ℂ`,
`‖f‖_p = (∫_X |f|^p dμ)^{1/p}` valued in `[0, ∞]` (`ℝ≥0∞`). -/
noncomputable def bookELpNormFinite {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : ℝ) (f : X → ℂ) : ℝ≥0∞ :=
  (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1 / p)

/-- RCA Definition 3.6 (printed p. 65): `f` belongs to the book's function-level class
`L^p(μ)` (`0 < p < ∞`) when `f` is genuinely `Measurable` and `‖f‖_p < ∞`. -/
def BookMemLpFinite {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : ℝ) (f : X → ℂ) : Prop :=
  Measurable f ∧ bookELpNormFinite μ p f < ∞

/-- Real-valued finite-exponent `L^p` norm `(‖f‖_p).toReal`. -/
noncomputable def bookLpNormFiniteReal {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : ℝ) (f : X → ℂ) : ℝ :=
  (bookELpNormFinite μ p f).toReal

/-- For genuinely `Measurable` `f` and `0 < p < ∞`, `bookELpNormFinite μ p f` coincides
with Mathlib's `eLpNorm f (ENNReal.ofReal p) μ`. -/
theorem definition_3_6_eq_eLpNorm {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {p : ℝ} (hp : 0 < p) {f : X → ℂ} (hf : Measurable f) :
    bookELpNormFinite μ p f = eLpNorm f (ENNReal.ofReal p) μ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le]
  rfl

/-- Bridge between Rudin's ordinary-measurability `BookMemLpFinite` and Mathlib's `MemLp`
(which uses `AEStronglyMeasurable`). -/
theorem definition_3_6_memLp_iff {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {p : ℝ} (hp : 0 < p) (f : X → ℂ) :
    BookMemLpFinite μ p f ↔ Measurable f ∧ MemLp f (ENNReal.ofReal p) μ := by
  constructor
  · rintro ⟨hf, hfin⟩
    rw [definition_3_6_eq_eLpNorm μ hp hf] at hfin
    exact ⟨hf, hfin⟩
  · rintro ⟨hf, hmem⟩
    refine ⟨hf, ?_⟩
    rw [definition_3_6_eq_eLpNorm μ hp hf]
    exact hmem

/-- Every `MemLp` function (`AEStronglyMeasurable`) is a.e. equal to a genuine `Measurable`
representative in `BookMemLpFinite`. -/
theorem definition_3_6_ae_representative_iff {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {p : ℝ} (hp : 0 < p) (f : X → ℂ) :
    MemLp f (ENNReal.ofReal p) μ ↔ ∃ g : X → ℂ, BookMemLpFinite μ p g ∧ f =ᵐ[μ] g := by
  constructor
  · intro hf
    have hae : AEMeasurable f μ := hf.aemeasurable
    refine ⟨hae.mk f, ?_, hae.ae_eq_mk⟩
    rw [definition_3_6_memLp_iff μ hp]
    exact ⟨hae.measurable_mk, hf.ae_eq hae.ae_eq_mk⟩
  · rintro ⟨g, hg, hfg⟩
    have hg' := ((definition_3_6_memLp_iff μ hp g).mp hg).2
    exact hg'.ae_eq hfg.symm

/-- Under a complete measure `μ.IsComplete` (Rudin 1.36–1.37), `BookMemLpFinite` and
Mathlib's `MemLp` coincide directly without passing to a modified representative. -/
theorem definition_3_6_complete_measure_iff {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [μ.IsComplete] {p : ℝ} (hp : 0 < p) (f : X → ℂ) :
    BookMemLpFinite μ p f ↔ MemLp f (ENNReal.ofReal p) μ := by
  rw [definition_3_6_memLp_iff μ hp]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  have hae : AEMeasurable f μ := h.aemeasurable
  exact hae.measurable_mk.congr_ae hae.ae_eq_mk.symm

/-- Explicit witness that on an incomplete measure space, `MemLp` is strictly broader than
`BookMemLpFinite`: on `Bool` with the indiscrete `σ`-algebra `⊥` and zero measure,
the indicator of `true` is `AEStronglyMeasurable` (`MemLp`) but not `Measurable`. -/
theorem definition_3_6_measurable_strictly_stronger :
    ∃ (m : MeasurableSpace Bool) (μ : @Measure Bool m) (f : Bool → ℂ),
      @MemLp Bool ℂ m _ _ f 1 μ ∧ ¬ @BookMemLpFinite Bool m μ 1 f := by
  let : MeasurableSpace Bool := ⊥
  let f : Bool → ℂ := fun b => if b then 1 else 0
  have hnotmeas : ¬ Measurable f := by
    intro hm
    have hs : MeasurableSet (f ⁻¹' ({1} : Set ℂ)) := hm (measurableSet_singleton 1)
    have hpre : f ⁻¹' ({1} : Set ℂ) = {true} := by
      ext b
      cases b <;> simp [f]
    rw [hpre] at hs
    rcases MeasurableSpace.measurableSet_bot_iff.mp hs with hemp | huniv
    · exact Set.singleton_ne_empty true hemp
    · have hf_mem : false ∈ ({true} : Set Bool) := by
        rw [huniv]
        trivial
      simp at hf_mem
  have hmem : MemLp f 1 (0 : Measure Bool) := memLp_measure_zero
  exact ⟨⊥, (0 : Measure Bool), f, hmem, fun hbook => hnotmeas hbook.1⟩

/-- Compatibility of Definition 3.6 at `p = 1` with `Chapter01.BookL1` (RCA 1.30). -/
theorem definition_3_6_one_iff_bookL1 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) :
    BookMemLpFinite μ 1 f ↔ Chapter01.BookL1 μ f := by
  have heq : bookELpNormFinite μ 1 f = ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ := by
    simp [bookELpNormFinite, ofReal_norm]
  simp [BookMemLpFinite, Chapter01.BookL1, heq]

/-- Canonical summary declaration for RCA Definition 3.6 (printed p. 65). -/
theorem node3_6 {X : Type*} [MeasurableSpace X] (μ : Measure X) {p : ℝ} (hp : 0 < p)
    (f : X → ℂ) :
    ((Measurable f → bookELpNormFinite μ p f = eLpNorm f (ENNReal.ofReal p) μ) ∧
      (BookMemLpFinite μ p f ↔ Measurable f ∧ MemLp f (ENNReal.ofReal p) μ) ∧
      (MemLp f (ENNReal.ofReal p) μ ↔ ∃ g : X → ℂ, BookMemLpFinite μ p g ∧ f =ᵐ[μ] g) ∧
      (BookMemLpFinite μ 1 f ↔ Chapter01.BookL1 μ f)) :=
  ⟨definition_3_6_eq_eLpNorm μ hp,
    definition_3_6_memLp_iff μ hp f,
    definition_3_6_ae_representative_iff μ hp f,
    definition_3_6_one_iff_bookL1 μ f⟩

/-! ## Section 3.7: Essential Supremum and $L^\infty(\mu)$ — Fidelity Repair & Bridges (pp. 65–66) -/

/-- Rudin's literal real-threshold set `S = {α ∈ ℝ | μ({x | α < g(x)}) = 0}` from printed
Definition 3.7 (p. 65), for `g : X → [0, ∞]`. -/
def printedRealThresholdSet {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (g : X → ℝ≥0∞) : Set ℝ :=
  {α : ℝ | μ {x | (α : EReal) < (g x : EReal)} = 0}

/-- Rudin's literal real-threshold set `{α ∈ ℝ | μ({x | α < ‖f(x)‖}) = 0}` for `|f|`. -/
def printedNormThresholdSet {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) : Set ℝ :=
  {α : ℝ | μ {x | α < ‖f x‖} = 0}

/-- On the identically zero measure on ANY measurable space `X` and for ANY `g : X → ℝ≥0∞`,
Rudin's literal real-threshold set equals `ℝ` and is unbounded below (`E-3.7`). -/
theorem definition_3_7_printed_zero_measure_unbounded {X : Type*} [MeasurableSpace X]
    (g : X → ℝ≥0∞) :
    printedRealThresholdSet (0 : Measure X) g = Set.univ ∧
      ¬ BddBelow (printedRealThresholdSet (0 : Measure X) g) := by
  have heq : printedRealThresholdSet (0 : Measure X) g = Set.univ := by
    ext α
    simp [printedRealThresholdSet]
  refine ⟨heq, ?_⟩
  rw [heq]
  rintro ⟨b, hb⟩
  linarith [hb (mem_univ (b - 1))]

/-- RCA 3.7(2) countable-union identity (printed p. 65): for any finite threshold `β < ∞`,
`{x | β < g(x)} = ⋃_{n=0}^∞ {x | β + 1/(n + 1) < g(x)}`. -/
theorem correctedEssentialSupremum_gt_eq_iUnion {X : Type*}
    (g : X → ℝ≥0∞) {β : ℝ≥0∞} (hβ : β ≠ ∞) :
    {x : X | β < g x} = ⋃ n : ℕ, {x : X | β + 1 / ((n : ℝ≥0∞) + 1) < g x} := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · intro hlt
    have hpos : 0 < g x - β := tsub_pos_iff_lt.mpr hlt
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hpos.ne'
    refine ⟨n, ?_⟩
    have hn' : ((n : ℝ≥0∞) + 1)⁻¹ < g x - β := by
      rcases eq_or_ne n 0 with rfl | hn0
      · exfalso
        simp at hn
      · have hle : ((n : ℝ≥0∞) + 1)⁻¹ ≤ (n : ℝ≥0∞)⁻¹ :=
          ENNReal.inv_le_inv.mpr (le_self_add)
        exact hle.trans_lt hn
    have hadd := ENNReal.add_lt_add_left hβ hn'
    rw [add_tsub_cancel_of_le hlt.le] at hadd
    simpa [one_div] using hadd
  · rintro ⟨n, hn⟩
    exact (le_self_add).trans_lt hn

/-- Attainment of the infimum in repaired Definition 3.7 (printed p. 65):
`β = correctedEssentialSupremum g μ` itself satisfies `μ {x | β < g x} = 0` (i.e. `g ≤ β` a.e.). -/
theorem correctedEssentialSupremum_mem_thresholdSet {X : Type*} [MeasurableSpace X]
    (g : X → ℝ≥0∞) (μ : Measure X) :
    μ {x | correctedEssentialSupremum g μ < g x} = 0 ∧
      (∀ᵐ x ∂μ, g x ≤ correctedEssentialSupremum g μ) := by
  have hae : ∀ᵐ x ∂μ, g x ≤ correctedEssentialSupremum g μ :=
    (correctedEssentialSupremum_le_iff g μ _).mp le_rfl
  refine ⟨?_, hae⟩
  rw [ae_iff] at hae
  simpa [not_le] using hae

/-- Explicitly repaired `L^∞(μ)` norm `‖f‖_∞` valued in `ℝ≥0∞`, defined via
`correctedEssentialSupremum (fun x => ‖f x‖ₑ) μ` (`QUEUE.md` §3.7). -/
noncomputable def correctedLinftyNorm {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) : ℝ≥0∞ :=
  correctedEssentialSupremum (fun x => ‖f x‖ₑ) μ

/-- Explicitly repaired function-level `L^∞(μ)` predicate: `f` is genuinely `Measurable`
and `correctedLinftyNorm μ f < ∞`. -/
def CorrectedBookMemLinfty {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) : Prop :=
  Measurable f ∧ correctedLinftyNorm μ f < ∞

theorem correctedLinftyNorm_eq_eLpNorm_top {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℂ} (hf : Measurable f) :
    correctedLinftyNorm μ f = eLpNorm f ∞ μ := by
  rw [eLpNorm_exponent_top hf.aestronglyMeasurable]
  rfl

theorem correctedBookMemLinfty_iff_memLp_top {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) :
    CorrectedBookMemLinfty μ f ↔ Measurable f ∧ MemLp f ∞ μ := by
  constructor
  · rintro ⟨hf, hfin⟩
    rw [correctedLinftyNorm_eq_eLpNorm_top μ hf] at hfin
    exact ⟨hf, hfin⟩
  · rintro ⟨hf, hmem⟩
    refine ⟨hf, ?_⟩
    rw [correctedLinftyNorm_eq_eLpNorm_top μ hf]
    exact hmem

/-- RCA 3.7 closing characterization (printed p. 66, under the explicit 3.7 repair):
for measurable `f`, `f ∈ L^∞(μ)` iff there exists `M < ∞` (`0 ≤ M`) with `‖f(x)‖ ≤ M` a.e.,
and `(correctedLinftyNorm μ f).toReal` is the least such `M`. -/
theorem definition_3_7_corrected_ae_bound_iff {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℂ} (hf : Measurable f) :
    (CorrectedBookMemLinfty μ f ↔ ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂μ, ‖f x‖ ≤ M) ∧
      (CorrectedBookMemLinfty μ f →
        (∀ᵐ x ∂μ, ‖f x‖ ≤ (correctedLinftyNorm μ f).toReal) ∧
          ∀ M : ℝ, 0 ≤ M → (∀ᵐ x ∂μ, ‖f x‖ ≤ M) → (correctedLinftyNorm μ f).toReal ≤ M) := by
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨_, hfin⟩
      refine ⟨(correctedLinftyNorm μ f).toReal, ENNReal.toReal_nonneg, ?_⟩
      have hae := (correctedEssentialSupremum_le_iff (fun x => ‖f x‖ₑ) μ
        (correctedLinftyNorm μ f)).mp le_rfl
      filter_upwards [hae] with x hx
      have hx' := ENNReal.toReal_mono hfin.ne hx
      simpa [toReal_enorm] using hx'
    · rintro ⟨M, hM0, hae⟩
      refine ⟨hf, ?_⟩
      have hae' : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ENNReal.ofReal M := by
        filter_upwards [hae] with x hx
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hx
      have hle : correctedLinftyNorm μ f ≤ ENNReal.ofReal M :=
        (correctedEssentialSupremum_le_iff _ μ _).mpr hae'
      exact hle.trans_lt ENNReal.ofReal_lt_top
  · rintro ⟨_, hfin⟩
    refine ⟨?_, ?_⟩
    · have hae := (correctedEssentialSupremum_le_iff (fun x => ‖f x‖ₑ) μ
        (correctedLinftyNorm μ f)).mp le_rfl
      filter_upwards [hae] with x hx
      simpa [toReal_enorm] using ENNReal.toReal_mono hfin.ne hx
    · intro M hM0 hae
      have hae' : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ENNReal.ofReal M := by
        filter_upwards [hae] with x hx
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hx
      have hle : correctedLinftyNorm μ f ≤ ENNReal.ofReal M :=
        (correctedEssentialSupremum_le_iff _ μ _).mpr hae'
      simpa [ENNReal.toReal_ofReal hM0] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hle

/-- On every nonzero measure `μ ≠ 0` (`μ Set.univ ≠ 0`), Rudin's literal real-threshold set
`printedNormThresholdSet μ f` IS bounded below by `0`, is nonempty iff `correctedLinftyNorm μ f < ∞`,
and its real infimum `sInf (printedNormThresholdSet μ f)` equals `(correctedLinftyNorm μ f).toReal`. -/
theorem definition_3_7_nonzero_measure_agreement {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (hμ : μ ≠ 0) (f : X → ℂ) :
    BddBelow (printedNormThresholdSet μ f) ∧
      ((printedNormThresholdSet μ f).Nonempty ↔ correctedLinftyNorm μ f < ∞) ∧
      (correctedLinftyNorm μ f < ∞ →
        sInf (printedNormThresholdSet μ f) = (correctedLinftyNorm μ f).toReal ∧
          sInf (printedNormThresholdSet μ f) ∈ printedNormThresholdSet μ f) := by
  have huniv : μ Set.univ ≠ 0 := by
    intro h0
    exact hμ (Measure.measure_univ_eq_zero.mp h0)
  have hnonneg : ∀ α ∈ printedNormThresholdSet μ f, 0 ≤ α := by
    intro α hα
    by_contra hlt
    have hlt' : α < 0 := not_le.mp hlt
    have heq : {x : X | α < ‖f x‖} = Set.univ := by
      ext x
      simp [hlt'.trans_le (norm_nonneg (f x))]
    rw [printedNormThresholdSet, mem_ofPred_eq, heq] at hα
    exact huniv hα
  have hbdd : BddBelow (printedNormThresholdSet μ f) := ⟨0, hnonneg⟩
  have hmem_iff : ∀ {α : ℝ}, 0 ≤ α →
      (α ∈ printedNormThresholdSet μ f ↔ correctedLinftyNorm μ f ≤ ENNReal.ofReal α) := by
    intro α hα0
    rw [printedNormThresholdSet, mem_ofPred_eq, correctedLinftyNorm,
      correctedEssentialSupremum_le_iff, ae_iff]
    suffices {x : X | α < ‖f x‖} = {x : X | ¬ ‖f x‖ₑ ≤ ENNReal.ofReal α} by rw [this]
    ext x
    simp only [mem_ofPred_eq, not_le, ← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα0).symm
  have hne_iff : (printedNormThresholdSet μ f).Nonempty ↔ correctedLinftyNorm μ f < ∞ := by
    constructor
    · rintro ⟨α, hα⟩
      exact ((hmem_iff (hnonneg α hα)).mp hα).trans_lt ENNReal.ofReal_lt_top
    · intro hfin
      refine ⟨(correctedLinftyNorm μ f).toReal, ?_⟩
      rw [hmem_iff ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne]
  refine ⟨hbdd, hne_iff, ?_⟩
  intro hfin
  set c := (correctedLinftyNorm μ f).toReal
  have hc_mem : c ∈ printedNormThresholdSet μ f := by
    rw [hmem_iff ENNReal.toReal_nonneg]
    simp [ENNReal.ofReal_toReal hfin.ne]
  have hc_lb : ∀ α ∈ printedNormThresholdSet μ f, c ≤ α := by
    intro α hα
    have hα0 := hnonneg α hα
    have hle := (hmem_iff hα0).mp hα
    simpa [c, ENNReal.toReal_ofReal hα0] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  have hsInf_eq : sInf (printedNormThresholdSet μ f) = c :=
    le_antisymm (csInf_le hbdd hc_mem) (le_csInf ⟨c, hc_mem⟩ hc_lb)
  exact ⟨hsInf_eq, hsInf_eq ▸ hc_mem⟩

/-- Unified `L^p(μ)` norm `‖f‖_p` valued in `ℝ≥0∞` for `0 < p ≤ ∞`, combining
Definition 3.6 (`0 < p < ∞`) with the explicitly repaired Definition 3.7 (`p = ∞`). -/
noncomputable def correctedBookLpNorm {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : ℝ≥0∞) (f : X → ℂ) : ℝ≥0∞ :=
  if p = 0 then 0
  else if p = ∞ then correctedLinftyNorm μ f
  else bookELpNormFinite μ p.toReal f

/-- Unified function-level `L^p(μ)` membership predicate (`0 < p ≤ ∞`) under the
explicit Definition 3.7 repair at `p = ∞`: `f` is genuinely `Measurable`, `p ≠ 0`,
and `correctedBookLpNorm μ p f < ∞`. -/
def CorrectedBookMemLp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : ℝ≥0∞) (f : X → ℂ) : Prop :=
  Measurable f ∧ p ≠ 0 ∧ correctedBookLpNorm μ p f < ∞

theorem correctedBookLpNorm_ofReal {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {p : ℝ} (hp : 0 < p) (f : X → ℂ) :
    correctedBookLpNorm μ (ENNReal.ofReal p) f = bookELpNormFinite μ p f := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  simp [correctedBookLpNorm, hp0, ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]

theorem correctedBookLpNorm_top {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) :
    correctedBookLpNorm μ ∞ f = correctedLinftyNorm μ f := by
  simp [correctedBookLpNorm]

theorem correctedBookLpNorm_eq_eLpNorm {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {p : ℝ≥0∞} (hp0 : p ≠ 0) {f : X → ℂ} (hf : Measurable f) :
    correctedBookLpNorm μ p f = eLpNorm f p μ := by
  by_cases hp_top : p = ∞
  · subst hp_top
    rw [correctedBookLpNorm_top, correctedLinftyNorm_eq_eLpNorm_top μ hf]
  · simp only [correctedBookLpNorm, hp0, hp_top, ↓reduceIte]
    have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
    rw [definition_3_6_eq_eLpNorm μ hpos hf, ENNReal.ofReal_toReal hp_top]

theorem correctedBookMemLp_iff_memLp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : ℝ≥0∞) (f : X → ℂ) :
    CorrectedBookMemLp μ p f ↔ p ≠ 0 ∧ Measurable f ∧ MemLp f p μ := by
  constructor
  · rintro ⟨hf, hp0, hfin⟩
    rw [correctedBookLpNorm_eq_eLpNorm μ hp0 hf] at hfin
    exact ⟨hp0, hf, hfin⟩
  · rintro ⟨hp0, hf, hmem⟩
    refine ⟨hf, hp0, ?_⟩
    rw [correctedBookLpNorm_eq_eLpNorm μ hp0 hf]
    exact hmem

theorem correctedBookMemLp_ofReal_iff {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {p : ℝ} (hp : 0 < p) (f : X → ℂ) :
    CorrectedBookMemLp μ (ENNReal.ofReal p) f ↔ BookMemLpFinite μ p f := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  simp [CorrectedBookMemLp, BookMemLpFinite, hp0, correctedBookLpNorm_ofReal μ hp]

theorem correctedBookMemLp_top_iff {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) :
    CorrectedBookMemLp μ ∞ f ↔ CorrectedBookMemLinfty μ f := by
  simp [CorrectedBookMemLp, CorrectedBookMemLinfty, correctedBookLpNorm_top]

theorem correctedBookMemLp_one_iff_bookL1 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) :
    CorrectedBookMemLp μ 1 f ↔ Chapter01.BookL1 μ f := by
  simpa using (correctedBookMemLp_ofReal_iff μ zero_lt_one f).trans
    (definition_3_6_one_iff_bookL1 μ f)

/-- Canonical summary declaration for RCA Definition 3.7 (printed pp. 65–66), combining
both the zero-measure defect counterexample (`definition_3_7_zero_measure_counterexample`)
and the explicitly repaired `ℝ≥0∞`-threshold essential supremum / `L^∞` properties,
attainment of the infimum, and nonzero-measure agreement. -/
theorem node3_7 {X : Type*} [MeasurableSpace X] (μ : Measure X) (g : X → ℝ≥0∞) (f : X → ℂ) :
    (¬ BddBelow {a : ℝ | (0 : Measure Unit) {_x | a < (0 : ℝ)} = 0}) ∧
    (correctedEssentialSupremum g (0 : Measure X) = 0) ∧
    (∀ a : ℝ≥0∞, correctedEssentialSupremum g μ ≤ a ↔ ∀ᵐ x ∂μ, g x ≤ a) ∧
    (μ {x | correctedEssentialSupremum g μ < g x} = 0) ∧
    (Measurable f →
      (CorrectedBookMemLinfty μ f ↔ ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂μ, ‖f x‖ ≤ M)) ∧
    (μ ≠ 0 → correctedLinftyNorm μ f < ∞ →
      sInf (printedNormThresholdSet μ f) = (correctedLinftyNorm μ f).toReal) :=
  ⟨definition_3_7_zero_measure_counterexample,
    correctedEssentialSupremum_zero_measure g,
    correctedEssentialSupremum_le_iff g μ,
    (correctedEssentialSupremum_mem_thresholdSet g μ).1,
    fun hf => (definition_3_7_corrected_ae_bound_iff μ hf).1,
    fun hμ hfin => ((definition_3_7_nonzero_measure_agreement hμ f).2.2 hfin).1⟩

/-! ## Section 3.16: Continuous Functions Vanishing at Infinity $C_0(X)$ (printed p. 70) -/

/-- RCA Definition 3.16 (printed p. 70): `f : X → ℂ` vanishes at infinity if for every
`ε > 0` there is a compact set `K ⊆ X` such that `‖f(x)‖ < ε` for all `x ∉ K`. -/
def BookVanishesAtInfinity {X : Type*} [TopologicalSpace X] (f : X → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : Set X, IsCompact K ∧ ∀ x, x ∉ K → ‖f x‖ < ε

/-- RCA Definition 3.16 (printed p. 70): `C_0(X)` consists of all continuous `f : X → ℂ`
which vanish at infinity. -/
def BookC0 {X : Type*} [TopologicalSpace X] (f : X → ℂ) : Prop :=
  Continuous f ∧ BookVanishesAtInfinity f

/-- Equivalence between `BookVanishesAtInfinity` and `Tendsto f (cocompact X) (𝓝 0)`. -/
theorem definition_3_16_cocompact_iff {X : Type*} [TopologicalSpace X] (f : X → ℂ) :
    BookVanishesAtInfinity f ↔ Tendsto f (Filter.cocompact X) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  constructor
  · intro hf ε hε
    obtain ⟨K, hK, hbound⟩ := hf ε hε
    rw [Filter.Eventually, Filter.mem_cocompact]
    refine ⟨K, hK, fun x hx => ?_⟩
    simpa [dist_zero_right] using hbound x hx
  · intro hf ε hε
    have hev := hf ε hε
    rw [Filter.Eventually, Filter.mem_cocompact] at hev
    obtain ⟨K, hK, hbound⟩ := hev
    refine ⟨K, hK, fun x hx => ?_⟩
    simpa [dist_zero_right] using hbound hx

/-- Exact bridge between `BookC0` and Mathlib's bundled `ZeroAtInftyContinuousMap` (`C₀(X, ℂ)`). -/
theorem definition_3_16_zeroAtInfty_iff {X : Type*} [TopologicalSpace X] (f : X → ℂ) :
    BookC0 f ↔ ∃ g : C₀(X, ℂ), (g : X → ℂ) = f := by
  constructor
  · rintro ⟨hcont, hvan⟩
    exact ⟨⟨⟨f, hcont⟩, (definition_3_16_cocompact_iff f).mp hvan⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g.continuous, (definition_3_16_cocompact_iff g).mpr (zero_at_infty g)⟩

/-- Construct a bundled element of `C₀(X, ℂ)` from a proof of `BookC0 f`. -/
def BookC0.toZeroAtInfty {X : Type*} [TopologicalSpace X] {f : X → ℂ} (hf : BookC0 f) :
    C₀(X, ℂ) :=
  ⟨⟨f, hf.1⟩, (definition_3_16_cocompact_iff f).mp hf.2⟩

@[simp]
theorem BookC0.coe_toZeroAtInfty {X : Type*} [TopologicalSpace X] {f : X → ℂ} (hf : BookC0 f) :
    (hf.toZeroAtInfty : X → ℂ) = f := rfl

/-- RCA 3.16 inclusion (printed p. 70): `C_c(X) ⊆ C_0(X)`. -/
theorem definition_3_16_cc_subset_c0 {X : Type*} [TopologicalSpace X] {f : X → ℂ}
    (hf : Chapter02.BookCc f) : BookC0 f := by
  refine ⟨hf.1, fun ε hε => ⟨Chapter02.BookSupport f, hf.2, fun x hx => ?_⟩⟩
  have hx0 : f x = 0 := by
    by_contra hne
    exact hx (subset_closure hne)
  simp [hx0, hε]

/-- Bundled canonical inclusion `C_c(X, ℂ) → C₀(X, ℂ)`. -/
def ccToC0 {X : Type*} [TopologicalSpace X] (f : C_c(X, ℂ)) : C₀(X, ℂ) :=
  (definition_3_16_cc_subset_c0
    ((Chapter02.definition_2_9_cc (f : X → ℂ)).mpr ⟨f, rfl⟩)).toZeroAtInfty

@[simp]
theorem coe_ccToC0 {X : Type*} [TopologicalSpace X] (f : C_c(X, ℂ)) :
    (ccToC0 f : X → ℂ) = f := rfl

/-- RCA 3.16 compact-space coincidence (printed p. 70): if `X` is compact, then
`C_c(X) = C_0(X) = C(X)`. -/
theorem definition_3_16_compact_coincide {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : X → ℂ) :
    (Chapter02.BookCc f ↔ BookC0 f) ∧ (BookC0 f ↔ Continuous f) := by
  have hc0_iff : BookC0 f ↔ Continuous f := by
    refine ⟨And.left, fun hf => ⟨hf, fun ε hε => ⟨Set.univ, isCompact_univ, fun x hx => ?_⟩⟩⟩
    exact False.elim (hx trivial)
  have hcc_iff : Chapter02.BookCc f ↔ Continuous f := by
    refine ⟨And.left, fun hf => ⟨hf, isClosed_closure.isCompact⟩⟩
  exact ⟨hcc_iff.trans hc0_iff.symm, hc0_iff⟩

/-- Canonical summary declaration for RCA Definition 3.16 (printed p. 70). -/
theorem node3_16 {X : Type*} [TopologicalSpace X] (f : X → ℂ) :
    (BookC0 f ↔ ∃ g : C₀(X, ℂ), (g : X → ℂ) = f) ∧
    (Chapter02.BookCc f → BookC0 f) ∧
    (CompactSpace X → (Chapter02.BookCc f ↔ BookC0 f) ∧ (BookC0 f ↔ Continuous f)) :=
  ⟨definition_3_16_zeroAtInfty_iff f,
    definition_3_16_cc_subset_c0,
    fun hK => @definition_3_16_compact_coincide X _ hK f⟩

/-! ## Section 3.3: Jensen's Inequality (printed pp. 62–63) -/

/-- If `μ(Ω) = 1` and `g : Ω → ℝ` is integrable with `0 < g(x)` for all `x ∈ Ω`,
then `0 < ∫ x, g x ∂μ`. -/
private theorem integral_pos_of_forall_pos {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (hμ : μ Set.univ = 1) {g : Ω → ℝ}
    (hg_int : Integrable g μ) (hg_pos : ∀ x, 0 < g x) :
    0 < ∫ x, g x ∂μ := by
  have heq : ∫ x, g x ∂μ = (∫⁻ x, ENNReal.ofReal (g x) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (hg_pos x).le)
      hg_int.aestronglyMeasurable
  rw [heq]
  have hfin : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) < ∞ := by
    refine (lintegral_mono fun x => ?_).trans_lt hg_int.2
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (le_abs_self (g x))
  have hne0 : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≠ 0 := by
    intro h0
    have hae := (lintegral_eq_zero_iff' (hg_int.aemeasurable.ennreal_ofReal)).mp h0
    have hemp : ∀ᵐ x ∂μ, False := by
      filter_upwards [hae] with x hx
      have hle : g x ≤ 0 := ENNReal.ofReal_eq_zero.mp hx
      linarith [hg_pos x]
    rw [ae_iff] at hemp
    simp [hμ] at hemp
  exact ENNReal.toReal_pos hne0 hfin.ne

/-- First step of Rudin's proof of Theorem 3.3 (printed p. 62): if `μ(Ω) = 1`,
`f : Ω → ℝ` is integrable, and `a < f(x) < b` for all `x ∈ Ω` (`-∞ ≤ a < b ≤ ∞`),
then `a < ∫_Ω f dμ < b`. -/
theorem theorem_3_3_integral_mem_openSegment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (hμ : μ Set.univ = 1) {a b : EReal} {f : Ω → ℝ}
    (hf_int : Integrable f μ) (hf_mem : ∀ x, f x ∈ OpenSegment a b) :
    (∫ x, f x ∂μ) ∈ OpenSegment a b := by
  let : IsProbabilityMeasure μ := ⟨hμ⟩
  have hne : Nonempty Ω := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have h0 : Set.univ = (∅ : Set Ω) := Set.eq_empty_of_isEmpty Set.univ
    rw [h0, measure_empty] at hμ
    exact zero_ne_one hμ
  obtain ⟨x₀⟩ := hne
  refine ⟨?_, ?_⟩
  · induction a using EReal.rec with
    | bot => exact EReal.bot_lt_coe _
    | coe a₀ =>
      rw [EReal.coe_lt_coe_iff]
      have hpos : 0 < ∫ x, (f x - a₀) ∂μ :=
        integral_pos_of_forall_pos hμ (hf_int.sub (integrable_const a₀))
          (fun x => sub_pos.mpr (EReal.coe_lt_coe_iff.mp (hf_mem x).1))
      have hint_sub : ∫ x, (f x - a₀) ∂μ = (∫ x, f x ∂μ) - a₀ := by
        rw [integral_sub hf_int (integrable_const a₀), integral_const]
        simp [Measure.real, hμ]
      linarith
    | top => exact absurd (hf_mem x₀).1 (not_lt_of_ge le_top)
  · induction b using EReal.rec with
    | bot => exact absurd (hf_mem x₀).2 (not_lt_of_gt (EReal.bot_lt_coe _))
    | coe b₀ =>
      rw [EReal.coe_lt_coe_iff]
      have hpos : 0 < ∫ x, (b₀ - f x) ∂μ :=
        integral_pos_of_forall_pos hμ ((integrable_const b₀).sub hf_int)
          (fun x => sub_pos.mpr (EReal.coe_lt_coe_iff.mp (hf_mem x).2))
      have hint_sub : ∫ x, (b₀ - f x) ∂μ = b₀ - ∫ x, f x ∂μ := by
        rw [integral_sub (integrable_const b₀) hf_int, integral_const]
        simp [Measure.real, hμ]
      linarith
    | top => exact EReal.coe_lt_top _

/-- Supporting-line step of Rudin's proof of Theorem 3.3 (printed p. 62, eq. (2)):
if `φ` is convex on `(a, b)` and `t ∈ (a, b)`, there exists `β ∈ ℝ` such that
`φ s ≥ φ t + β * (s - t)` for all `s ∈ (a, b)`. -/
theorem theorem_3_3_supporting_line {a b : EReal} {φ : ℝ → ℝ}
    (hφ : BookConvexOnSegment a b φ) {t : ℝ} (ht : t ∈ OpenSegment a b) :
    ∃ β : ℝ, ∀ s ∈ OpenSegment a b, φ t + β * (s - t) ≤ φ s := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (isOpen_openSegment a b) t ht
  have hs₀_mem : t - δ / 2 ∈ OpenSegment a b := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have : |t - δ / 2 - t| = δ / 2 := by
      rw [show t - δ / 2 - t = -(δ / 2) by ring, abs_neg, abs_of_pos (half_pos hδ)]
    linarith
  have hu₀_mem : t + δ / 2 ∈ OpenSegment a b := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have : |t + δ / 2 - t| = δ / 2 := by
      rw [show t + δ / 2 - t = δ / 2 by ring, abs_of_pos (half_pos hδ)]
    linarith
  let S : Set ℝ := {m : ℝ | ∃ s ∈ OpenSegment a b, s < t ∧ m = (φ t - φ s) / (t - s)}
  have hS_ne : S.Nonempty := ⟨(φ t - φ (t - δ / 2)) / (t - (t - δ / 2)),
    t - δ / 2, hs₀_mem, by linarith, rfl⟩
  have hslope := (definition_3_1_chord_slope_iff a b φ).mp hφ
  have hS_upper : ∀ u ∈ OpenSegment a b, t < u → ∀ m ∈ S, m ≤ (φ u - φ t) / (u - t) := by
    rintro u hu htu m ⟨s, hs, hst, rfl⟩
    exact hslope s hs t ht u hu hst htu
  have hS_bdd : BddAbove S := ⟨(φ (t + δ / 2) - φ t) / (t + δ / 2 - t),
    hS_upper (t + δ / 2) hu₀_mem (by linarith)⟩
  refine ⟨sSup S, fun s hs => ?_⟩
  rcases lt_trichotomy s t with hst | rfl | hts
  · have hm : (φ t - φ s) / (t - s) ≤ sSup S :=
      le_csSup hS_bdd ⟨s, hs, hst, rfl⟩
    have hpos : 0 < t - s := sub_pos.mpr hst
    have hmul := (div_le_iff₀ hpos).mp hm
    linarith
  · simp
  · have hm : sSup S ≤ (φ s - φ t) / (s - t) :=
      csSup_le hS_ne (hS_upper s hs hts)
    have hpos : 0 < s - t := sub_pos.mpr hts
    have hmul := (le_div_iff₀ hpos).mp hm
    linarith

/-- Measurability of `φ ∘ f` when `φ` is convex on `(a, b)` and `f : Ω → ℝ` is measurable
with values in `(a, b)` (by Theorem 3.2 continuity of `φ` on `(a, b)`). -/
theorem theorem_3_3_comp_measurable {Ω : Type*} [MeasurableSpace Ω]
    {a b : EReal} {φ : ℝ → ℝ} (hφ : BookConvexOnSegment a b φ)
    {f : Ω → ℝ} (hf_meas : Measurable f) (hf_mem : ∀ x, f x ∈ OpenSegment a b) :
    Measurable (fun x => φ (f x)) := by
  have hcont : ContinuousOn φ (OpenSegment a b) := theorem_3_2 hφ
  refine measurable_of_isOpen fun V hV => ?_
  obtain ⟨U, hU_open, hU_eq⟩ := continuousOn_iff'.mp hcont V hV
  have hpre : (fun x => φ (f x)) ⁻¹' V = f ⁻¹' (U ∩ OpenSegment a b) := by
    ext x
    have hx : f x ∈ OpenSegment a b := hf_mem x
    have hiff : f x ∈ φ ⁻¹' V ∩ OpenSegment a b ↔ f x ∈ U ∩ OpenSegment a b := by
      rw [hU_eq]
    simpa [hx] using hiff
  rw [hpre]
  exact hf_meas (hU_open.inter (isOpen_openSegment a b)).measurableSet

/-- RCA Theorem 3.3 (Jensen's Inequality, printed pp. 62–63), retaining BOTH open/unbounded
intervals `-∞ ≤ a < b ≤ ∞` AND the extended integral case of Section 1.31 when `φ ∘ f` is
not in `L¹(μ)`:
1. `∫_Ω f dμ ∈ (a, b)`;
2. `φ ∘ f` is measurable and its Section 1.31 extended integral
   `hExt : Chapter01.ExtendedIntegralDefined μ univ (fun x => (φ (f x) : EReal))` ALWAYS
   exists (its negative part has finite integral);
3. `(φ (∫_Ω f dμ) : EReal) ≤ Chapter01.BookExtendedIntegral μ univ (fun x => (φ (f x) : EReal)) hExt`;
4. If `Integrable (φ ∘ f) μ`, the extended integral equals `(∫_Ω φ(f(x)) dμ : EReal)` and
   `φ (∫_Ω f dμ) ≤ ∫_Ω φ(f(x)) dμ`;
5. If `¬ Integrable (φ ∘ f) μ`, the extended integral equals `+∞` (`⊤`), as stated in
   Rudin's note on p. 62. -/
theorem theorem_3_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (hμ : μ Set.univ = 1) {a b : EReal} {φ : ℝ → ℝ} (hφ : BookConvexOnSegment a b φ)
    {f : Ω → ℝ} (hf_meas : Measurable f) (hf_int : Integrable f μ)
    (hf_mem : ∀ x, f x ∈ OpenSegment a b) :
    (∫ x, f x ∂μ) ∈ OpenSegment a b ∧
    Measurable (fun x => φ (f x)) ∧
    ∃ hExt : Chapter01.ExtendedIntegralDefined μ Set.univ (fun x => ((φ (f x) : ℝ) : EReal)),
      (((φ (∫ x, f x ∂μ) : ℝ) : EReal) ≤
        Chapter01.BookExtendedIntegral μ Set.univ (fun x => ((φ (f x) : ℝ) : EReal)) hExt) ∧
      (Integrable (fun x => φ (f x)) μ →
        Chapter01.BookExtendedIntegral μ Set.univ (fun x => ((φ (f x) : ℝ) : EReal)) hExt =
          ((∫ x, φ (f x) ∂μ : ℝ) : EReal) ∧
        φ (∫ x, f x ∂μ) ≤ ∫ x, φ (f x) ∂μ) ∧
      (¬ Integrable (fun x => φ (f x)) μ →
        Chapter01.BookExtendedIntegral μ Set.univ (fun x => ((φ (f x) : ℝ) : EReal)) hExt = ⊤) := by
  let : IsProbabilityMeasure μ := ⟨hμ⟩
  set t : ℝ := ∫ x, f x ∂μ
  have ht_mem : t ∈ OpenSegment a b := theorem_3_3_integral_mem_openSegment hμ hf_int hf_mem
  have hcomp_meas : Measurable (fun x => φ (f x)) := theorem_3_3_comp_measurable hφ hf_meas hf_mem
  obtain ⟨β, hβ⟩ := theorem_3_3_supporting_line hφ ht_mem
  let L : Ω → ℝ := fun x => φ t + β * (f x - t)
  have hL_le : ∀ x, L x ≤ φ (f x) := fun x => hβ (f x) (hf_mem x)
  have hf_sub_int : Integrable (fun x => f x - t) μ := hf_int.sub (integrable_const t)
  have hβ_int : Integrable (fun x => β * (f x - t)) μ := hf_sub_int.const_mul β
  have hL_int : Integrable L μ := (integrable_const (φ t)).add hβ_int
  have hL_integral : ∫ x, L x ∂μ = φ t := by
    change ∫ x, ((fun _ => φ t) x + (fun x => β * (f x - t)) x) ∂μ = φ t
    rw [integral_add (integrable_const (φ t)) hβ_int,
      integral_const, integral_const_mul, integral_sub hf_int (integrable_const t), integral_const]
    simp [Measure.real, hμ, t]
  have htoENN_pos : ∀ r : ℝ, ((r : EReal)).toENNReal = ENNReal.ofReal r := fun r => by
    simp [EReal.toENNReal]
  have htoENN_neg : ∀ r : ℝ, (-(r : EReal)).toENNReal = ENNReal.ofReal (-r) := fun r => by
    rw [← EReal.coe_neg]
    simp [EReal.toENNReal]
  have hL_neg_fin : (∫⁻ x in Set.univ, ENNReal.ofReal (-L x) ∂μ) < ∞ := by
    rw [Measure.restrict_univ]
    exact hL_int.neg.lintegral_lt_top
  have hL_pos_fin : (∫⁻ x in Set.univ, ENNReal.ofReal (L x) ∂μ) < ∞ := by
    rw [Measure.restrict_univ]
    exact hL_int.lintegral_lt_top
  have hφ_neg_le_L_neg :
      (∫⁻ x in Set.univ, (-(φ (f x) : EReal)).toENNReal ∂μ) ≤
        ∫⁻ x in Set.univ, ENNReal.ofReal (-L x) ∂μ := by
    refine lintegral_mono fun x => ?_
    rw [htoENN_neg]
    exact ENNReal.ofReal_le_ofReal (neg_le_neg (hL_le x))
  have hφ_neg_fin : (∫⁻ x in Set.univ, (-(φ (f x) : EReal)).toENNReal ∂μ) < ∞ :=
    hφ_neg_le_L_neg.trans_lt hL_neg_fin
  have hereal_meas : Measurable (fun x => ((φ (f x) : ℝ) : EReal)) :=
    measurable_coe_real_ereal.comp hcomp_meas
  have hExt : Chapter01.ExtendedIntegralDefined μ Set.univ (fun x => ((φ (f x) : ℝ) : EReal)) :=
    ⟨hereal_meas, Or.inr hφ_neg_fin⟩
  have hL_pos_le_φ_pos :
      (∫⁻ x in Set.univ, ENNReal.ofReal (L x) ∂μ) ≤
        ∫⁻ x in Set.univ, ((φ (f x) : EReal)).toENNReal ∂μ := by
    refine lintegral_mono fun x => ?_
    rw [htoENN_pos]
    exact ENNReal.ofReal_le_ofReal (hL_le x)
  have hL_decomp : ((φ t : ℝ) : EReal) =
      (((∫⁻ x in Set.univ, ENNReal.ofReal (L x) ∂μ) : EReal) -
        ((∫⁻ x in Set.univ, ENNReal.ofReal (-L x) ∂μ) : EReal)) := by
    have h1 := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hL_int
    rw [hL_integral] at h1
    rw [h1, EReal.coe_sub]
    simp_rw [Measure.restrict_univ]
    rw [EReal.coe_ennreal_toReal (by simpa [Measure.restrict_univ] using hL_pos_fin.ne),
      EReal.coe_ennreal_toReal (by simpa [Measure.restrict_univ] using hL_neg_fin.ne)]
  have hjensen : ((φ t : ℝ) : EReal) ≤
      Chapter01.BookExtendedIntegral μ Set.univ (fun x => ((φ (f x) : ℝ) : EReal)) hExt := by
    rw [hL_decomp]
    unfold Chapter01.BookExtendedIntegral
    exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hL_pos_le_φ_pos)
      (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hφ_neg_le_L_neg)
  refine ⟨ht_mem, hcomp_meas, hExt, hjensen, ?_, ?_⟩
  · intro hφ_int
    have hpos_fin : (∫⁻ x in Set.univ, ((φ (f x) : EReal)).toENNReal ∂μ) < ∞ := by
      simp_rw [htoENN_pos, Measure.restrict_univ]
      exact hφ_int.lintegral_lt_top
    have heq_ext :
        Chapter01.BookExtendedIntegral μ Set.univ (fun x => ((φ (f x) : ℝ) : EReal)) hExt =
          ((∫ x, φ (f x) ∂μ : ℝ) : EReal) := by
      unfold Chapter01.BookExtendedIntegral
      have h1 := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hφ_int
      rw [h1, EReal.coe_sub]
      simp_rw [htoENN_pos, htoENN_neg, Measure.restrict_univ]
      rw [EReal.coe_ennreal_toReal (by simpa [htoENN_pos, Measure.restrict_univ] using hpos_fin.ne),
        EReal.coe_ennreal_toReal (by simpa [htoENN_neg, Measure.restrict_univ] using hφ_neg_fin.ne)]
    refine ⟨heq_ext, ?_⟩
    rw [heq_ext, EReal.coe_le_coe_iff] at hjensen
    exact hjensen
  · intro hnot_int
    unfold Chapter01.BookExtendedIntegral
    have hpos_top : (∫⁻ x in Set.univ, ((φ (f x) : EReal)).toENNReal ∂μ) = ∞ := by
      by_contra hne_top
      apply hnot_int
      refine ⟨hcomp_meas.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_norm]
      have hpos' : (∫⁻ x, ENNReal.ofReal (φ (f x)) ∂μ) < ∞ := by
        simpa [htoENN_pos, Measure.restrict_univ] using lt_top_iff_ne_top.mpr hne_top
      have hneg' : (∫⁻ x, ENNReal.ofReal (-φ (f x)) ∂μ) < ∞ := by
        simpa [htoENN_neg, Measure.restrict_univ] using hφ_neg_fin
      calc
        (∫⁻ x, ENNReal.ofReal ‖φ (f x)‖ ∂μ)
            ≤ ∫⁻ x, (ENNReal.ofReal (φ (f x)) + ENNReal.ofReal (-φ (f x))) ∂μ := by
          refine lintegral_mono fun x => ?_
          rw [Real.norm_eq_abs]
          rcases le_total 0 (φ (f x)) with h0 | h0
          · simp [abs_of_nonneg h0]
          · simp [abs_of_nonpos h0]
        _ = (∫⁻ x, ENNReal.ofReal (φ (f x)) ∂μ) + ∫⁻ x, ENNReal.ofReal (-φ (f x)) ∂μ :=
          lintegral_add_left hcomp_meas.ennreal_ofReal _
        _ < ∞ := ENNReal.add_lt_top.mpr ⟨hpos', hneg'⟩
    rw [hpos_top, EReal.coe_ennreal_top]
    exact EReal.top_sub (EReal.coe_ennreal_eq_top_iff.not.mpr hφ_neg_fin.ne)

/-- Integrable specialization of Theorem 3.3: when `φ ∘ f` is integrable,
`φ (∫_Ω f dμ) ≤ ∫_Ω φ(f(x)) dμ` (extending also to any `Integrable f μ` without
ordinary measurability via `f.aemeasurable.mk`). -/
theorem theorem_3_3_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (hμ : μ Set.univ = 1) {a b : EReal} {φ : ℝ → ℝ} (hφ : BookConvexOnSegment a b φ)
    {f : Ω → ℝ} (hf_meas : Measurable f) (hf_int : Integrable f μ)
    (hf_mem : ∀ x, f x ∈ OpenSegment a b)
    (hcomp_int : Integrable (fun x => φ (f x)) μ) :
    φ (∫ x, f x ∂μ) ≤ ∫ x, φ (f x) ∂μ := by
  obtain ⟨_, _, _, _, hint, _⟩ := theorem_3_3 μ hμ hφ hf_meas hf_int hf_mem
  exact (hint hcomp_int).2

/-- RCA 3.3 exponential corollary (printed p. 63): if `μ(Ω) = 1` and `f : Ω → ℝ` is in
`L¹(μ)`, then `exp(∫_Ω f dμ) ≤ ∫_Ω exp(f) dμ` in `[0, ∞]` (and in `ℝ` when `exp ∘ f` is
integrable). -/
theorem theorem_3_3_exp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (hμ : μ Set.univ = 1) {f : Ω → ℝ} (hf_meas : Measurable f) (hf_int : Integrable f μ) :
    ENNReal.ofReal (Real.exp (∫ x, f x ∂μ)) ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂μ ∧
      (Integrable (fun x => Real.exp (f x)) μ →
        Real.exp (∫ x, f x ∂μ) ≤ ∫ x, Real.exp (f x) ∂μ) := by
  have hf_mem : ∀ x, f x ∈ OpenSegment ⊥ ⊤ := fun x => by
    rw [openSegment_bot_top]; trivial
  obtain ⟨_, _, hExt, hjensen, hint, hnot⟩ :=
    theorem_3_3 μ hμ definition_3_1_exp_convex hf_meas hf_int hf_mem
  refine ⟨?_, fun hi => (hint hi).2⟩
  by_cases hi : Integrable (fun x => Real.exp (f x)) μ
  · have hreal := (hint hi).2
    have hle := ENNReal.ofReal_le_ofReal hreal
    rwa [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun x => (Real.exp_pos _).le) hi.aestronglyMeasurable,
      ENNReal.ofReal_toReal hi.lintegral_lt_top.ne] at hle
  · have htop : (∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂μ) = ∞ := by
      have htop_ext := hnot hi
      unfold Chapter01.BookExtendedIntegral at htop_ext
      have hneg0 : (∫⁻ x in Set.univ, (-(Real.exp (f x) : EReal)).toENNReal ∂μ) = 0 := by
        refine (lintegral_eq_zero_iff' ?_).mpr (Eventually.of_forall fun x => ?_)
        · exact (measurable_coe_real_ereal.comp (Real.measurable_exp.comp hf_meas)).neg.ereal_toENNReal.aemeasurable
        · dsimp
          rw [← EReal.coe_neg]
          simp [EReal.toENNReal, (Real.exp_pos (f x)).le]
      rw [hneg0, EReal.coe_ennreal_zero, sub_zero] at htop_ext
      have hpos_top : (∫⁻ x in Set.univ, ((Real.exp (f x) : EReal)).toENNReal ∂μ) = ∞ :=
        EReal.coe_ennreal_eq_top_iff.mp htop_ext
      simpa [EReal.toENNReal, Measure.restrict_univ] using hpos_top
    rw [htop]
    exact le_top

/-- RCA 3.3 weighted arithmetic-geometric mean inequality (printed p. 63):
for positive reals `y_i > 0` and nonnegative weights `α_i ≥ 0` summing to `1`,
`∏ i, y_i ^ α_i ≤ ∑ i, α_i * y_i`. -/
theorem theorem_3_3_weighted_am_gm {ι : Type*} (s : Finset ι) (y α : ι → ℝ)
    (hy : ∀ i ∈ s, 0 < y i) (hα : ∀ i ∈ s, 0 ≤ α i) (hsum : ∑ i ∈ s, α i = 1) :
    ∏ i ∈ s, y i ^ α i ≤ ∑ i ∈ s, α i * y i :=
  Real.geom_mean_le_arith_mean_weighted s α y hα hsum fun i hi => (hy i hi).le

/-- RCA 3.3 equal-weight arithmetic-geometric mean inequality (printed p. 63):
for `n ≥ 1` and `y_0, ..., y_{n-1} > 0`, `(∏ i, y_i) ^ (1 / n) ≤ (1 / n) * ∑ i, y_i`. -/
theorem theorem_3_3_am_gm {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ) (hy : ∀ i, 0 < y i) :
    (∏ i : Fin n, y i) ^ ((1 : ℝ) / n) ≤ ((1 : ℝ) / n) * ∑ i : Fin n, y i := by
  let α : Fin n → ℝ := fun _ => (1 : ℝ) / n
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hα : ∀ i ∈ Finset.univ, 0 ≤ α i := fun _ _ => div_nonneg zero_le_one hn_pos.le
  have hsum : ∑ i ∈ Finset.univ, α i = 1 := by
    simp [α, hn_pos.ne']
  have hw := theorem_3_3_weighted_am_gm Finset.univ y α (fun i _ => hy i) hα hsum
  have hprod : (∏ i : Fin n, y i) ^ ((1 : ℝ) / n) = ∏ i ∈ Finset.univ, y i ^ α i := by
    simpa [α] using
      (Real.finsetProd_rpow Finset.univ y (fun i _ => (hy i).le) ((1 : ℝ) / n)).symm
  dsimp [α] at hw
  rw [hprod, Finset.mul_sum]
  dsimp [α]
  exact hw

/-- Canonical summary declaration for RCA Theorem 3.3 (printed pp. 62–63). -/
theorem theorem3_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (hμ : μ Set.univ = 1) {a b : EReal} {φ : ℝ → ℝ} (hφ : BookConvexOnSegment a b φ)
    {f : Ω → ℝ} (hf_meas : Measurable f) (hf_int : Integrable f μ)
    (hf_mem : ∀ x, f x ∈ OpenSegment a b) :
    (∫ x, f x ∂μ) ∈ OpenSegment a b ∧
    ∃ hExt : Chapter01.ExtendedIntegralDefined μ Set.univ (fun x => ((φ (f x) : ℝ) : EReal)),
      (((φ (∫ x, f x ∂μ) : ℝ) : EReal) ≤
        Chapter01.BookExtendedIntegral μ Set.univ (fun x => ((φ (f x) : ℝ) : EReal)) hExt) ∧
      (Integrable (fun x => φ (f x)) μ → φ (∫ x, f x ∂μ) ≤ ∫ x, φ (f x) ∂μ) ∧
      (¬ Integrable (fun x => φ (f x)) μ →
        Chapter01.BookExtendedIntegral μ Set.univ (fun x => ((φ (f x) : ℝ) : EReal)) hExt = ⊤) := by
  obtain ⟨ht, _, hExt, hj, hint, hnot⟩ := theorem_3_3 μ hμ hφ hf_meas hf_int hf_mem
  exact ⟨ht, hExt, hj, fun hi => (hint hi).2, hnot⟩

/-! ## Section 3.5: Hölder's and Minkowski's Inequalities on $[0, \infty]$ (printed pp. 63–65) -/

/-- RCA Theorem 3.5(1) (Hölder's inequality for `[0, ∞]`-valued measurable functions,
printed pp. 63–64): for finite conjugate exponents `p, q` (`1 < p < ∞`) and measurable
`f, g : X → [0, ∞]`, `∫_X f g dμ ≤ (∫_X f^p dμ)^{1/p} (∫_X g^q dμ)^{1/q}`. -/
theorem theorem_3_5_holder {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p q : ℝ} (hpq : BookRealConjugateExponents p q)
    {f g : X → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * g x ∂μ) ≤
      (∫⁻ x, f x ^ p ∂μ) ^ (1 / p) * (∫⁻ x, g x ^ q ∂μ) ^ (1 / q) :=
  ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    ((definition_3_4_holderConjugate_iff p q).mp hpq) hf.aemeasurable hg.aemeasurable

/-- RCA Theorem 3.5(2) (Minkowski's inequality for `[0, ∞]`-valued measurable functions,
printed p. 64): for `1 ≤ p < ∞` (in particular `1 < p < ∞`) and measurable `f, g : X → [0, ∞]`,
`(∫_X (f + g)^p dμ)^{1/p} ≤ (∫_X f^p dμ)^{1/p} + (∫_X g^p dμ)^{1/p}`. -/
theorem theorem_3_5_minkowski {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ} (hp : 1 ≤ p)
    {f g : X → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, (f x + g x) ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ x, f x ^ p ∂μ) ^ (1 / p) + (∫⁻ x, g x ^ p ∂μ) ^ (1 / p) :=
  ENNReal.lintegral_Lp_add_le hf.aemeasurable hg.aemeasurable hp

/-- RCA 3.5 Schwarz inequality specialization (`p = q = 2`, printed p. 64). -/
theorem theorem_3_5_schwarz {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f g : X → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * g x ∂μ) ≤
      (∫⁻ x, f x ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
        (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) :=
  theorem_3_5_holder μ definition_3_4_self_conjugate.1 hf hg

/-- Canonical summary declaration for RCA Theorem 3.5 (printed pp. 63–65). -/
theorem theorem3_5 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p q : ℝ} (hpq : BookRealConjugateExponents p q)
    {f g : X → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ((∫⁻ x, f x * g x ∂μ) ≤
      (∫⁻ x, f x ^ p ∂μ) ^ (1 / p) * (∫⁻ x, g x ^ q ∂μ) ^ (1 / q)) ∧
    ((∫⁻ x, (f x + g x) ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ x, f x ^ p ∂μ) ^ (1 / p) + (∫⁻ x, g x ^ p ∂μ) ^ (1 / p)) :=
  ⟨theorem_3_5_holder μ hpq hf hg,
    theorem_3_5_minkowski μ (definition_3_4_bounds hpq).1.le hf hg⟩

/-! ## Section 3.8: Product in $L^1(\mu)$ and Hölder Including Endpoints (printed p. 66) -/

/-- RCA Theorem 3.8 (printed p. 66, stated explicitly with the repaired `L^∞` convention
`CorrectedBookMemLp` / `correctedBookLpNorm` per the Definition 3.7 fidelity hold):
for extended conjugate exponents `p, q` (`1 ≤ p ≤ ∞`), if `f ∈ L^p(μ)` and `g ∈ L^q(μ)`,
then `f * g ∈ L^1(μ)` (`Chapter01.BookL1 μ (f * g)`),
`‖f * g‖₁ ≤ ‖f‖_p ‖g‖_q` (in both `ℝ≥0∞` and `ℝ`), and
`‖∫_X f(x) g(x) dμ‖ ≤ ‖f‖_p ‖g‖_q`. -/
theorem theorem_3_8 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p q : ℝ≥0∞} (hpq : BookConjugateExponents p q)
    {f g : X → ℂ} (hf : CorrectedBookMemLp μ p f) (hg : CorrectedBookMemLp μ q g) :
    CorrectedBookMemLp μ 1 (f * g) ∧
    Chapter01.BookL1 μ (f * g) ∧
    correctedBookLpNorm μ 1 (f * g) ≤
      correctedBookLpNorm μ p f * correctedBookLpNorm μ q g ∧
    (correctedBookLpNorm μ 1 (f * g)).toReal ≤
      (correctedBookLpNorm μ p f).toReal * (correctedBookLpNorm μ q g).toReal ∧
    ‖∫ x, f x * g x ∂μ‖ ≤
      (correctedBookLpNorm μ p f).toReal * (correctedBookLpNorm μ q g).toReal := by
  let : ENNReal.HolderConjugate p q := (definition_3_4_extended_iff p q).mp hpq
  obtain ⟨hp0, hf_meas, hf_mem⟩ := (correctedBookMemLp_iff_memLp μ p f).mp hf
  obtain ⟨hq0, hg_meas, hg_mem⟩ := (correctedBookMemLp_iff_memLp μ q g).mp hg
  have hfg_meas : Measurable (f * g) := hf_meas.mul hg_meas
  have hfg_mem : MemLp (f * g) 1 μ := hf_mem.mul hg_mem
  have hfg_book : CorrectedBookMemLp μ 1 (f * g) :=
    (correctedBookMemLp_iff_memLp μ 1 (f * g)).mpr ⟨one_ne_zero, hfg_meas, hfg_mem⟩
  have hfg_L1 : Chapter01.BookL1 μ (f * g) :=
    (correctedBookMemLp_one_iff_bookL1 μ (f * g)).mp hfg_book
  have hnorm_enn : correctedBookLpNorm μ 1 (f * g) ≤
      correctedBookLpNorm μ p f * correctedBookLpNorm μ q g := by
    rw [correctedBookLpNorm_eq_eLpNorm μ one_ne_zero hfg_meas,
      correctedBookLpNorm_eq_eLpNorm μ hp0 hf_meas,
      correctedBookLpNorm_eq_eLpNorm μ hq0 hg_meas]
    exact eLpNorm_smul_le_mul_eLpNorm hf_meas.aestronglyMeasurable hg_meas.aestronglyMeasurable
  have hmul_ne_top : correctedBookLpNorm μ p f * correctedBookLpNorm μ q g ≠ ∞ :=
    ENNReal.mul_ne_top hf.2.2.ne hg.2.2.ne
  have hnorm_real : (correctedBookLpNorm μ 1 (f * g)).toReal ≤
      (correctedBookLpNorm μ p f).toReal * (correctedBookLpNorm μ q g).toReal := by
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono hmul_ne_top hnorm_enn
  have hint_bound : ‖∫ x, f x * g x ∂μ‖ ≤
      (correctedBookLpNorm μ p f).toReal * (correctedBookLpNorm μ q g).toReal := by
    have hfg_int : Integrable (f * g) μ := ((Chapter01.definition_1_30 μ (f * g)).mp hfg_L1).2
    calc
      ‖∫ x, f x * g x ∂μ‖ ≤ ∫ x, ‖(f * g) x‖ ∂μ := norm_integral_le_integral_norm (f * g)
      _ = (eLpNorm (f * g) 1 μ).toReal := by
        rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => norm_nonneg _)
          hfg_int.norm.aestronglyMeasurable, eLpNorm_one_eq_lintegral_enorm]
        · simp [ofReal_norm]
        · exact hfg_meas.aestronglyMeasurable
      _ = (correctedBookLpNorm μ 1 (f * g)).toReal := by
        rw [correctedBookLpNorm_eq_eLpNorm μ one_ne_zero hfg_meas]
      _ ≤ (correctedBookLpNorm μ p f).toReal * (correctedBookLpNorm μ q g).toReal := hnorm_real
  exact ⟨hfg_book, hfg_L1, hnorm_enn, hnorm_real, hint_bound⟩

/-- Nonzero-measure endpoint bridge for Theorem 3.8 (`p = 1, q = ∞`): when `μ ≠ 0`,
`‖f * g‖₁ ≤ ‖f‖₁ * sInf (printedNormThresholdSet μ g)` using Rudin's literal 3.7 threshold set. -/
theorem theorem_3_8_nonzero_measure_printed_endpoint {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (hμ : μ ≠ 0) {f g : X → ℂ}
    (hf : CorrectedBookMemLp μ 1 f) (hg : CorrectedBookMemLinfty μ g) :
    (correctedBookLpNorm μ 1 (f * g)).toReal ≤
      (correctedBookLpNorm μ 1 f).toReal * sInf (printedNormThresholdSet μ g) := by
  have hg' : CorrectedBookMemLp μ ∞ g := (correctedBookMemLp_top_iff μ g).mpr hg
  have h8 := (theorem_3_8 μ (Or.inl ⟨rfl, rfl⟩) hf hg').2.2.2.1
  have hsInf := ((definition_3_7_nonzero_measure_agreement hμ g).2.2 hg.2).1
  rwa [correctedBookLpNorm_top, ← hsInf] at h8

/-- Canonical summary declaration for RCA Theorem 3.8 (printed p. 66). -/
theorem theorem3_8 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p q : ℝ≥0∞} (hpq : BookConjugateExponents p q)
    {f g : X → ℂ} (hf : CorrectedBookMemLp μ p f) (hg : CorrectedBookMemLp μ q g) :
    CorrectedBookMemLp μ 1 (f * g) ∧
    correctedBookLpNorm μ 1 (f * g) ≤
      correctedBookLpNorm μ p f * correctedBookLpNorm μ q g ∧
    ‖∫ x, f x * g x ∂μ‖ ≤
      (correctedBookLpNorm μ p f).toReal * (correctedBookLpNorm μ q g).toReal := by
  obtain ⟨h1, _, h3, _, h5⟩ := theorem_3_8 μ hpq hf hg
  exact ⟨h1, h3, h5⟩

/-! ## Section 3.9: $L^p$ Addition and Triangle Inequality (printed p. 66) -/

/-- RCA Theorem 3.9 (printed p. 66, stated explicitly with `CorrectedBookMemLp` /
`correctedBookLpNorm` per the Definition 3.7 fidelity hold at `p = ∞`):
for `1 ≤ p ≤ ∞` and `f, g ∈ L^p(μ)`, we have `f + g ∈ L^p(μ)` and
`‖f + g‖_p ≤ ‖f‖_p + ‖g‖_p` (in both `ℝ≥0∞` and `ℝ`). -/
theorem theorem_3_9 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f g : X → ℂ} (hf : CorrectedBookMemLp μ p f) (hg : CorrectedBookMemLp μ p g) :
    CorrectedBookMemLp μ p (f + g) ∧
    correctedBookLpNorm μ p (f + g) ≤
      correctedBookLpNorm μ p f + correctedBookLpNorm μ p g ∧
    (correctedBookLpNorm μ p (f + g)).toReal ≤
      (correctedBookLpNorm μ p f).toReal + (correctedBookLpNorm μ p g).toReal := by
  obtain ⟨hp0, hf_meas, hf_mem⟩ := (correctedBookMemLp_iff_memLp μ p f).mp hf
  obtain ⟨_, hg_meas, hg_mem⟩ := (correctedBookMemLp_iff_memLp μ p g).mp hg
  have hfg_meas : Measurable (f + g) := hf_meas.add hg_meas
  have hfg_mem : MemLp (f + g) p μ := hf_mem.add hg_mem
  have hfg_book : CorrectedBookMemLp μ p (f + g) :=
    (correctedBookMemLp_iff_memLp μ p (f + g)).mpr ⟨hp0, hfg_meas, hfg_mem⟩
  have htri : correctedBookLpNorm μ p (f + g) ≤
      correctedBookLpNorm μ p f + correctedBookLpNorm μ p g := by
    rw [correctedBookLpNorm_eq_eLpNorm μ hp0 hfg_meas,
      correctedBookLpNorm_eq_eLpNorm μ hp0 hf_meas,
      correctedBookLpNorm_eq_eLpNorm μ hp0 hg_meas]
    exact eLpNorm_add_le hp
  have hadd_ne_top : correctedBookLpNorm μ p f + correctedBookLpNorm μ p g ≠ ∞ :=
    (ENNReal.add_lt_top.mpr ⟨hf.2.2, hg.2.2⟩).ne
  have htri_real : (correctedBookLpNorm μ p (f + g)).toReal ≤
      (correctedBookLpNorm μ p f).toReal + (correctedBookLpNorm μ p g).toReal := by
    rw [← ENNReal.toReal_add hf.2.2.ne hg.2.2.ne]
    exact ENNReal.toReal_mono hadd_ne_top htri
  exact ⟨hfg_book, htri, htri_real⟩

/-- Nonzero-measure `p = ∞` bridge for Theorem 3.9: when `μ ≠ 0`, Rudin's literal 3.7
real-threshold infimum satisfies the triangle inequality. -/
theorem theorem_3_9_nonzero_measure_printed_top {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (hμ : μ ≠ 0) {f g : X → ℂ}
    (hf : CorrectedBookMemLinfty μ f) (hg : CorrectedBookMemLinfty μ g) :
    sInf (printedNormThresholdSet μ (f + g)) ≤
      sInf (printedNormThresholdSet μ f) + sInf (printedNormThresholdSet μ g) := by
  have hf' : CorrectedBookMemLp μ ∞ f := (correctedBookMemLp_top_iff μ f).mpr hf
  have hg' : CorrectedBookMemLp μ ∞ g := (correctedBookMemLp_top_iff μ g).mpr hg
  obtain ⟨hfg', _, htri_real⟩ := theorem_3_9 μ le_top hf' hg'
  have hfg : CorrectedBookMemLinfty μ (f + g) := (correctedBookMemLp_top_iff μ (f + g)).mp hfg'
  rw [((definition_3_7_nonzero_measure_agreement hμ (f + g)).2.2 hfg.2).1,
    ((definition_3_7_nonzero_measure_agreement hμ f).2.2 hf.2).1,
    ((definition_3_7_nonzero_measure_agreement hμ g).2.2 hg.2).1]
  simpa [correctedBookLpNorm_top] using htri_real

/-- Canonical summary declaration for RCA Theorem 3.9 (printed p. 66). -/
theorem theorem3_9 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f g : X → ℂ} (hf : CorrectedBookMemLp μ p f) (hg : CorrectedBookMemLp μ p g) :
    CorrectedBookMemLp μ p (f + g) ∧
    correctedBookLpNorm μ p (f + g) ≤
      correctedBookLpNorm μ p f + correctedBookLpNorm μ p g ∧
    (correctedBookLpNorm μ p (f + g)).toReal ≤
      (correctedBookLpNorm μ p f).toReal + (correctedBookLpNorm μ p g).toReal :=
  theorem_3_9 μ hp hf hg

/-! ## Section 3.10: Remarks — Complex Vector Space and AE Quotient Metric (printed pp. 66–67) -/

/-- RCA Remarks 3.10 scalar homogeneity (`0 < p ≤ ∞`, using `correctedBookLpNorm` per the
explicit Definition 3.7 repair): `‖α f‖_p = |α| ‖f‖_p` for measurable `f : X → ℂ` and `α : ℂ`. -/
theorem remarks_3_10_smul_norm {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (c : ℂ) {f : X → ℂ} (hf : Measurable f) :
    correctedBookLpNorm μ p (c • f) = ‖c‖ₑ * correctedBookLpNorm μ p f := by
  have hcf : Measurable (c • f) := measurable_const.mul hf
  rw [correctedBookLpNorm_eq_eLpNorm μ hp0 hcf,
    correctedBookLpNorm_eq_eLpNorm μ hp0 hf, eLpNorm_const_smul]

/-- RCA Remarks 3.10 scalar closure and real-valued homogeneity (`0 < p ≤ ∞`): if `f ∈ L^p(μ)`,
then `c • f ∈ L^p(μ)` and `‖c • f‖_p = ‖c‖ ‖f‖_p`. -/
theorem remarks_3_10_smul {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ≥0∞} (c : ℂ) {f : X → ℂ} (hf : CorrectedBookMemLp μ p f) :
    CorrectedBookMemLp μ p (c • f) ∧
    (correctedBookLpNorm μ p (c • f)).toReal = ‖c‖ * (correctedBookLpNorm μ p f).toReal := by
  obtain ⟨hp0, hf_meas, hf_mem⟩ := (correctedBookMemLp_iff_memLp μ p f).mp hf
  have hcf_meas : Measurable (c • f) := measurable_const.mul hf_meas
  have hcf_book : CorrectedBookMemLp μ p (c • f) :=
    (correctedBookMemLp_iff_memLp μ p (c • f)).mpr ⟨hp0, hcf_meas, hf_mem.const_smul c⟩
  refine ⟨hcf_book, ?_⟩
  rw [remarks_3_10_smul_norm μ hp0 c hf_meas, ENNReal.toReal_mul,
    ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg c)]

/-- RCA Remarks 3.10 complex vector space structure on function-level `L^p(μ)` (`1 ≤ p ≤ ∞`),
as a `ℂ`-submodule of `X → ℂ` under the explicit Definition 3.7 repair (`CorrectedBookMemLp`). -/
def correctedBookLpSubmodule {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) (hp : 1 ≤ p) : Submodule ℂ (X → ℂ) where
  carrier := {f : X → ℂ | CorrectedBookMemLp μ p f}
  zero_mem' := (correctedBookMemLp_iff_memLp μ p 0).mpr
    ⟨(zero_lt_one.trans_le hp).ne', measurable_const, MemLp.zero⟩
  add_mem' hf hg := (theorem_3_9 μ hp hf hg).1
  smul_mem' c _ hf := (remarks_3_10_smul μ c hf).1

/-- RCA Remarks 3.10 function-level pseudometric `d(f, g) = ‖f - g‖_p` (`1 ≤ p ≤ ∞`, printed p. 67),
explicitly adopting `correctedBookLpNorm` per the Definition 3.7 repair. -/
noncomputable def correctedBookLpDist {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) (f g : X → ℂ) : ℝ :=
  (correctedBookLpNorm μ p (f - g)).toReal

/-- RCA Remarks 3.10 pseudometric axioms and AE-degeneracy characterization on `L^p(μ)`
(`1 ≤ p ≤ ∞`, printed pp. 66–67):
`0 ≤ d(f, g)`, `d(f, f) = 0`, `d(f, g) = d(g, f)`, `d(f, h) ≤ d(f, g) + d(g, h)`, and
`d(f, g) = 0 ↔ ‖f - g‖_p = 0 ↔ f =ᵐ[μ] g`. -/
theorem remarks_3_10_pseudometric {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f g h : X → ℂ} (hf : CorrectedBookMemLp μ p f)
    (hg : CorrectedBookMemLp μ p g) (hh : CorrectedBookMemLp μ p h) :
    0 ≤ correctedBookLpDist μ p f g ∧
    correctedBookLpDist μ p f f = 0 ∧
    correctedBookLpDist μ p f g = correctedBookLpDist μ p g f ∧
    correctedBookLpDist μ p f h ≤
      correctedBookLpDist μ p f g + correctedBookLpDist μ p g h ∧
    (correctedBookLpDist μ p f g = 0 ↔ correctedBookLpNorm μ p (f - g) = 0) ∧
    (correctedBookLpNorm μ p (f - g) = 0 ↔ f =ᵐ[μ] g) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  obtain ⟨_, hf_meas, hf_mem⟩ := (correctedBookMemLp_iff_memLp μ p f).mp hf
  obtain ⟨_, hg_meas, hg_mem⟩ := (correctedBookMemLp_iff_memLp μ p g).mp hg
  obtain ⟨_, hh_meas, hh_mem⟩ := (correctedBookMemLp_iff_memLp μ p h).mp hh
  have hfg_book : CorrectedBookMemLp μ p (f - g) :=
    (correctedBookMemLp_iff_memLp μ p (f - g)).mpr ⟨hp0, hf_meas.sub hg_meas, hf_mem.sub hg_mem⟩
  have hgh_book : CorrectedBookMemLp μ p (g - h) :=
    (correctedBookMemLp_iff_memLp μ p (g - h)).mpr ⟨hp0, hg_meas.sub hh_meas, hg_mem.sub hh_mem⟩
  refine ⟨ENNReal.toReal_nonneg, ?_, ?_, ?_, ?_, ?_⟩
  · unfold correctedBookLpDist
    rw [sub_self, correctedBookLpNorm_eq_eLpNorm μ hp0 measurable_zero,
      eLpNorm_zero, ENNReal.toReal_zero]
  · unfold correctedBookLpDist
    rw [correctedBookLpNorm_eq_eLpNorm μ hp0 (hf_meas.sub hg_meas),
      correctedBookLpNorm_eq_eLpNorm μ hp0 (hg_meas.sub hf_meas),
      show f - g = -(g - f) by abel, eLpNorm_neg]
  · unfold correctedBookLpDist
    have hsplit : f - h = (f - g) + (g - h) := by abel
    rw [hsplit]
    exact (theorem_3_9 μ hp hfg_book hgh_book).2.2
  · unfold correctedBookLpDist
    rw [ENNReal.toReal_eq_zero_iff]
    exact ⟨fun h0 => h0.resolve_right hfg_book.2.2.ne, Or.inl⟩
  · rw [correctedBookLpNorm_eq_eLpNorm μ hp0 (hf_meas.sub hg_meas), eLpNorm_eq_zero_iff hp0]
    refine ⟨fun hae => ?_, fun hae => ?_⟩
    · filter_upwards [hae] with x hx
      exact sub_eq_zero.mp hx
    · filter_upwards [hae] with x hx
      exact sub_eq_zero.mpr hx

@[simp]
theorem mem_correctedBookLpSubmodule_iff {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (f : X → ℂ) :
    f ∈ correctedBookLpSubmodule μ p hp ↔ CorrectedBookMemLp μ p f :=
  Iff.rfl

/-- Submodule of `μ`-almost-everywhere zero functions inside `correctedBookLpSubmodule μ p hp`
(printed p. 67). -/
def aeZeroSubmodule {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) (hp : 1 ≤ p) : Submodule ℂ (correctedBookLpSubmodule μ p hp) where
  carrier := {f | (f : X → ℂ) =ᵐ[μ] 0}
  zero_mem' := by
    change (0 : X → ℂ) =ᵐ[μ] 0
    exact EventuallyEq.rfl
  add_mem' {f g} hf hg := by
    have hf' : (f : X → ℂ) =ᵐ[μ] 0 := hf
    have hg' : (g : X → ℂ) =ᵐ[μ] 0 := hg
    change (f : X → ℂ) + (g : X → ℂ) =ᵐ[μ] 0
    simpa using hf'.add hg'
  smul_mem' c {f} hf := by
    have hf' : (f : X → ℂ) =ᵐ[μ] 0 := hf
    change c • (f : X → ℂ) =ᵐ[μ] 0
    simpa using hf'.const_smul c

/-- Canonical `ℂ`-linear quotient map from Rudin's function-level `L^p(μ)`
(`correctedBookLpSubmodule μ p hp`) onto Mathlib's AE-equivalence-class space `Lp ℂ p μ`. -/
noncomputable def correctedBookToLp {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) (hp : 1 ≤ p) : correctedBookLpSubmodule μ p hp →ₗ[ℂ] Lp ℂ p μ where
  toFun f := (((correctedBookMemLp_iff_memLp μ p f.1).mp f.2).2.2).toLp f.1
  map_add' _ _ := MemLp.toLp_add _ _
  map_smul' c _ := MemLp.toLp_const_smul c _

/-- Two measurable `L^p` representatives map to the same element of `Lp ℂ p μ` if and only if
they agree `μ`-almost everywhere (`MemLp.toLp_eq_toLp_iff`). -/
theorem remarks_3_10_toLp_eq_iff {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (f g : correctedBookLpSubmodule μ p hp) :
    correctedBookToLp μ p hp f = correctedBookToLp μ p hp g ↔
      (f : X → ℂ) =ᵐ[μ] (g : X → ℂ) :=
  MemLp.toLp_eq_toLp_iff
    (((correctedBookMemLp_iff_memLp μ p f.1).mp f.2).2.2)
    (((correctedBookMemLp_iff_memLp μ p g.1).mp g.2).2.2)

/-- Kernel of `correctedBookToLp`: `[f] = 0` in `Lp ℂ p μ` iff `f = 0` `μ`-a.e. -/
theorem remarks_3_10_ker_toLp {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    LinearMap.ker (correctedBookToLp μ p hp) = aeZeroSubmodule μ p hp := by
  ext f
  rw [LinearMap.mem_ker, ← MemLp.toLp_zero (α := X) (E := ℂ) (p := p) (μ := μ) MemLp.zero]
  exact MemLp.toLp_eq_toLp_iff (((correctedBookMemLp_iff_memLp μ p f.1).mp f.2).2.2) MemLp.zero

/-- Surjectivity of `correctedBookToLp`: every AE class `F : Lp ℂ p μ` has an honest
`Measurable` representative in `correctedBookLpSubmodule μ p hp` (because `ℂ` is second-countable
Borel, so `Lp.stronglyMeasurable F` implies `Measurable (F : X → ℂ)`). -/
theorem remarks_3_10_toLp_surjective {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Function.Surjective (correctedBookToLp μ p hp) := by
  intro F
  let g : X → ℂ := ⇑F
  have hg_meas : Measurable g := (Lp.stronglyMeasurable F).measurable
  have hg_mem : MemLp g p μ := Lp.memLp F
  have hg_book : CorrectedBookMemLp μ p g :=
    (correctedBookMemLp_iff_memLp μ p g).mpr ⟨(zero_lt_one.trans_le hp).ne', hg_meas, hg_mem⟩
  refine ⟨⟨g, hg_book⟩, ?_⟩
  exact Lp.toLp_coeFn F hg_mem

/-- Explicit `ℂ`-linear isomorphism between Rudin's quotient of `L^p(μ)` by `μ`-a.e. equality
and Mathlib's `Lp ℂ p μ` (`1 ≤ p ≤ ∞`, printed p. 67). -/
noncomputable def correctedBookQuotientEquivLp {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    (correctedBookLpSubmodule μ p hp ⧸ aeZeroSubmodule μ p hp) ≃ₗ[ℂ] Lp ℂ p μ :=
  LinearEquiv.ofBijective
    ((aeZeroSubmodule μ p hp).liftQ (correctedBookToLp μ p hp)
      (le_of_eq (remarks_3_10_ker_toLp μ p hp).symm))
    ⟨by
      intro q₁ q₂ hq
      induction q₁ using Submodule.Quotient.induction_on with | _ f₁ =>
      induction q₂ using Submodule.Quotient.induction_on with | _ f₂ =>
      rw [Submodule.Quotient.eq]
      have hsub : correctedBookToLp μ p hp (f₁ - f₂) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact hq
      rw [← remarks_3_10_ker_toLp μ p hp]
      exact hsub,
     by
      intro F
      obtain ⟨f, rfl⟩ := remarks_3_10_toLp_surjective μ p hp F
      exact ⟨Submodule.Quotient.mk f, rfl⟩⟩

/-- Distance compatibility directly on `correctedBookToLp`. -/
theorem remarks_3_10_toLp_dist {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (f g : correctedBookLpSubmodule μ p hp.out) :
    dist (correctedBookToLp μ p hp.out f) (correctedBookToLp μ p hp.out g) =
      correctedBookLpDist μ p f.1 g.1 := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp.out).ne'
  obtain ⟨_, hf_meas, hf_mem⟩ := (correctedBookMemLp_iff_memLp μ p f.1).mp f.2
  obtain ⟨_, hg_meas, hg_mem⟩ := (correctedBookMemLp_iff_memLp μ p g.1).mp g.2
  change dist (hf_mem.toLp f.1) (hg_mem.toLp g.1) = correctedBookLpDist μ p f.1 g.1
  rw [Lp.dist_edist, Lp.edist_toLp_toLp]
  unfold correctedBookLpDist
  rw [correctedBookLpNorm_eq_eLpNorm μ hp0 (hf_meas.sub hg_meas)]

/-- RCA Remarks 3.10 metric & norm compatibility between function representatives and the
quotient metric space `Lp ℂ p μ` (`[Fact (1 ≤ p)]`, printed p. 67). -/
theorem remarks_3_10_quotient_metric_bridge {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (f g : correctedBookLpSubmodule μ p hp.out) :
    ‖correctedBookQuotientEquivLp μ p hp.out (Submodule.Quotient.mk f)‖ =
      (correctedBookLpNorm μ p f.1).toReal ∧
    dist (correctedBookQuotientEquivLp μ p hp.out (Submodule.Quotient.mk f))
        (correctedBookQuotientEquivLp μ p hp.out (Submodule.Quotient.mk g)) =
      correctedBookLpDist μ p f.1 g.1 := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp.out).ne'
  obtain ⟨_, hf_meas, hf_mem⟩ := (correctedBookMemLp_iff_memLp μ p f.1).mp f.2
  refine ⟨?_, remarks_3_10_toLp_dist μ p f g⟩
  change ‖hf_mem.toLp f.1‖ = (correctedBookLpNorm μ p f.1).toReal
  rw [Lp.norm_toLp, correctedBookLpNorm_eq_eLpNorm μ hp0 hf_meas]

/-- RCA Remarks 3.10 `L^p` convergence bridge (`1 ≤ p ≤ ∞`, printed p. 67):
`d(f_n, f) = ‖f_n - f‖_p → 0` in `ℝ` iff `‖f_n - f‖_p → 0` in `ℝ≥0∞` iff `[f_n] → [f]` in
`Lp ℂ p μ`. -/
theorem remarks_3_10_tendsto_iff {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) [hp : Fact (1 ≤ p)]
    {f : ℕ → X → ℂ} (hf : ∀ n, CorrectedBookMemLp μ p (f n))
    {g : X → ℂ} (hg : CorrectedBookMemLp μ p g) :
    (Tendsto (fun n => correctedBookLpDist μ p (f n) g) atTop (𝓝 0) ↔
      Tendsto (fun n => correctedBookLpNorm μ p (f n - g)) atTop (𝓝 0)) ∧
    (Tendsto (fun n => correctedBookLpDist μ p (f n) g) atTop (𝓝 0) ↔
      Tendsto (fun n => correctedBookToLp μ p hp.out ⟨f n, hf n⟩) atTop
        (𝓝 (correctedBookToLp μ p hp.out ⟨g, hg⟩))) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp.out).ne'
  have hdist_eq : ∀ n, dist (correctedBookToLp μ p hp.out ⟨f n, hf n⟩)
      (correctedBookToLp μ p hp.out ⟨g, hg⟩) = correctedBookLpDist μ p (f n) g :=
    fun n => remarks_3_10_toLp_dist μ p ⟨f n, hf n⟩ ⟨g, hg⟩
  have hlp : Tendsto (fun n => correctedBookLpDist μ p (f n) g) atTop (𝓝 0) ↔
      Tendsto (fun n => correctedBookToLp μ p hp.out ⟨f n, hf n⟩) atTop
        (𝓝 (correctedBookToLp μ p hp.out ⟨g, hg⟩)) :=
    (tendsto_iff_dist_tendsto_zero.trans (Filter.tendsto_congr hdist_eq)).symm
  refine ⟨?_, hlp⟩
  rw [hlp]
  change Tendsto (fun n => (((correctedBookMemLp_iff_memLp μ p (f n)).mp (hf n)).2.2).toLp (f n))
      atTop (𝓝 ((((correctedBookMemLp_iff_memLp μ p g).mp hg).2.2).toLp g)) ↔ _
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
  refine Filter.tendsto_congr fun n => ?_
  have hfn_meas := ((correctedBookMemLp_iff_memLp μ p (f n)).mp (hf n)).2.1
  have hg_meas := ((correctedBookMemLp_iff_memLp μ p g).mp hg).2.1
  exact (correctedBookLpNorm_eq_eLpNorm μ hp0 (hfn_meas.sub hg_meas)).symm

/-- Canonical summary declaration for RCA Remarks 3.10 (printed pp. 66–67). -/
theorem node3_10 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] :
    Function.Bijective (correctedBookQuotientEquivLp μ p hp.out) ∧
    (∀ f g : correctedBookLpSubmodule μ p hp.out,
      dist (correctedBookQuotientEquivLp μ p hp.out (Submodule.Quotient.mk f))
        (correctedBookQuotientEquivLp μ p hp.out (Submodule.Quotient.mk g)) =
          correctedBookLpDist μ p f.1 g.1) ∧
    (∀ f g : X → ℂ, CorrectedBookMemLp μ p f → CorrectedBookMemLp μ p g →
      (correctedBookLpDist μ p f g = 0 ↔ f =ᵐ[μ] g)) :=
  ⟨(correctedBookQuotientEquivLp μ p hp.out).bijective,
    fun f g => (remarks_3_10_quotient_metric_bridge μ p f g).2,
    fun _ _ hf hg =>
      ((remarks_3_10_pseudometric μ hp.out hf hg hf).2.2.2.2.1).trans
        ((remarks_3_10_pseudometric μ hp.out hf hg hf).2.2.2.2.2)⟩

/-! ## Section 3.11: Completeness of $L^p(\mu)$ (printed pp. 67–68) -/

/-- RCA Theorem 3.11 quotient metric completeness (`1 ≤ p ≤ ∞`, printed pp. 67–68):
`Lp ℂ p μ` is a complete metric space (Banach space over `ℂ`). -/
theorem theorem_3_11_quotient_complete {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    CompleteSpace (Lp ℂ p μ) :=
  inferInstance

/-- RCA Theorem 3.11 (Riesz–Fischer completeness of `L^p(μ)` for `1 ≤ p ≤ ∞`, printed pp. 67–68,
stated explicitly with `CorrectedBookMemLp` / `correctedBookLpDist` per the Definition 3.7
fidelity hold): every Cauchy sequence `{f_n}` in `L^p(μ)` converges in `L^p`-metric (`‖f_n - f‖_p → 0`)
to a measurable function `f ∈ L^p(μ)`, unique up to `μ`-almost-everywhere equality. -/
theorem theorem_3_11 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : ℕ → X → ℂ} (hf : ∀ n, CorrectedBookMemLp μ p (f n))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      correctedBookLpDist μ p (f n) (f m) < ε) :
    ∃ g : X → ℂ,
      CorrectedBookMemLp μ p g ∧
      Tendsto (fun n => correctedBookLpDist μ p (f n) g) atTop (𝓝 0) ∧
      Tendsto (fun n => correctedBookLpNorm μ p (f n - g)) atTop (𝓝 0) ∧
      (∀ h : X → ℂ, CorrectedBookMemLp μ p h →
        Tendsto (fun n => correctedBookLpDist μ p (f n) h) atTop (𝓝 0) → h =ᵐ[μ] g) := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let F : ℕ → Lp ℂ p μ := fun n => correctedBookToLp μ p hp ⟨f n, hf n⟩
  have hF_dist : ∀ n m, dist (F n) (F m) = correctedBookLpDist μ p (f n) (f m) := fun n m =>
    remarks_3_10_toLp_dist μ p ⟨f n, hf n⟩ ⟨f m, hf m⟩
  have hF_cauchy : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    exact ⟨N, fun n hn m hm => (hF_dist n m).trans_lt (hN n m hn hm)⟩
  obtain ⟨G, hFG⟩ := cauchySeq_tendsto_of_complete hF_cauchy
  obtain ⟨⟨g, hg_book⟩, hg_eq⟩ := remarks_3_10_toLp_surjective μ p hp G
  have hFG' : Tendsto F atTop (𝓝 (correctedBookToLp μ p hp ⟨g, hg_book⟩)) := by
    rwa [hg_eq]
  have hdist_zero : Tendsto (fun n => correctedBookLpDist μ p (f n) g) atTop (𝓝 0) :=
    ((remarks_3_10_tendsto_iff μ p hf hg_book).2).mpr hFG'
  have hnorm_zero : Tendsto (fun n => correctedBookLpNorm μ p (f n - g)) atTop (𝓝 0) :=
    ((remarks_3_10_tendsto_iff μ p hf hg_book).1).mp hdist_zero
  refine ⟨g, hg_book, hdist_zero, hnorm_zero, ?_⟩
  intro h hh_book hh_tendsto
  have hFH : Tendsto F atTop (𝓝 (correctedBookToLp μ p hp ⟨h, hh_book⟩)) :=
    ((remarks_3_10_tendsto_iff μ p hf hh_book).2).mp hh_tendsto
  have heq_lp : correctedBookToLp μ p hp ⟨h, hh_book⟩ = correctedBookToLp μ p hp ⟨g, hg_book⟩ :=
    tendsto_nhds_unique hFH hFG'
  exact (remarks_3_10_toLp_eq_iff μ p hp ⟨h, hh_book⟩ ⟨g, hg_book⟩).mp heq_lp

/-- Nonzero-measure `p = ∞` bridge for Theorem 3.11: when `μ ≠ 0`, Cauchy completeness at
`p = ∞` holds directly in terms of Rudin's literal printed real-threshold infimum `sInf (printedNormThresholdSet μ ·)`. -/
theorem theorem_3_11_nonzero_measure_printed_top {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (hμ : μ ≠ 0)
    {f : ℕ → X → ℂ} (hf : ∀ n, CorrectedBookMemLinfty μ (f n))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      sInf (printedNormThresholdSet μ (f n - f m)) < ε) :
    ∃ g : X → ℂ,
      CorrectedBookMemLinfty μ g ∧
      Tendsto (fun n => sInf (printedNormThresholdSet μ (f n - g))) atTop (𝓝 0) := by
  have hf' : ∀ n, CorrectedBookMemLp μ ∞ (f n) :=
    fun n => (correctedBookMemLp_top_iff μ (f n)).mpr (hf n)
  have hsub_fin : ∀ {u v : X → ℂ}, CorrectedBookMemLp μ ∞ u → CorrectedBookMemLp μ ∞ v →
      correctedLinftyNorm μ (u - v) < ∞ := by
    intro u v hu hv
    have huv := (theorem_3_9 μ le_top hu ((remarks_3_10_smul μ (-1 : ℂ) hv).1)).1
    have heq : u + (-1 : ℂ) • v = u - v := by ext x; simp [sub_eq_add_neg]
    rw [heq] at huv
    exact ((correctedBookMemLp_top_iff μ (u - v)).mp huv).2
  have hcauchy' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      correctedBookLpDist μ ∞ (f n) (f m) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, fun n m hn hm => ?_⟩
    unfold correctedBookLpDist
    rw [correctedBookLpNorm_top,
      ← ((definition_3_7_nonzero_measure_agreement hμ (f n - f m)).2.2
        (hsub_fin (hf' n) (hf' m))).1]
    exact hN n m hn hm
  obtain ⟨g, hg', hdist, _, _⟩ := theorem_3_11 μ le_top hf' hcauchy'
  refine ⟨g, (correctedBookMemLp_top_iff μ g).mp hg', ?_⟩
  refine hdist.congr fun n => ?_
  unfold correctedBookLpDist
  rw [correctedBookLpNorm_top,
    ((definition_3_7_nonzero_measure_agreement hμ (f n - g)).2.2 (hsub_fin (hf' n) hg')).1]

/-- Canonical summary declaration for RCA Theorem 3.11 (printed pp. 67–68). -/
theorem theorem3_11 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    (haveI : Fact (1 ≤ p) := ⟨hp⟩; CompleteSpace (Lp ℂ p μ)) ∧
    (∀ f : ℕ → X → ℂ, (∀ n, CorrectedBookMemLp μ p (f n)) →
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        correctedBookLpDist μ p (f n) (f m) < ε) →
      ∃ g : X → ℂ, CorrectedBookMemLp μ p g ∧
        Tendsto (fun n => correctedBookLpDist μ p (f n) g) atTop (𝓝 0)) := by
  refine ⟨by let : Fact (1 ≤ p) := ⟨hp⟩; infer_instance, ?_⟩
  intro f hf hcauchy
  obtain ⟨g, hg, hdist, _, _⟩ := theorem_3_11 μ hp hf hcauchy
  exact ⟨g, hg, hdist⟩

/-! ## Section 3.12: AE Convergent Subsequence (printed p. 68) -/

/-- General `0 < p ≤ ∞` `eLpNorm`-convergence-to-AE-subsequence theorem underlying RCA 3.12:
if `f_n` and `g` are measurable and `correctedBookLpNorm μ p (f_n - g) → 0`, then `{f_n}` has a
strictly increasing subsequence converging pointwise `μ`-almost everywhere to `g`. -/
theorem theorem_3_12_of_norm_tendsto {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ≥0∞} (hp0 : p ≠ 0)
    {f : ℕ → X → ℂ} (hf_meas : ∀ n, Measurable (f n))
    {g : X → ℂ} (hg_meas : Measurable g)
    (hconv : Tendsto (fun n => correctedBookLpNorm μ p (f n - g)) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun k => f (ns k) x) atTop (𝓝 (g x)) := by
  have heLp : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
    refine hconv.congr fun n => ?_
    exact correctedBookLpNorm_eq_eLpNorm μ hp0 ((hf_meas n).sub hg_meas)
  exact (tendstoInMeasure_of_tendsto_eLpNorm hp0 heLp).exists_seq_tendsto_ae

/-- RCA Theorem 3.12 (printed p. 68, stated explicitly with `CorrectedBookMemLp` /
`correctedBookLpDist` per the Definition 3.7 fidelity hold): if `1 ≤ p ≤ ∞` and `{f_n}` is a
Cauchy sequence in `L^p(μ)` with limit `g ∈ L^p(μ)`, then `{f_n}` has a subsequence `{f_{n_k}}`
which converges pointwise `μ`-almost everywhere to `g(x)`. -/
theorem theorem_3_12 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : ℕ → X → ℂ} (hf : ∀ n, CorrectedBookMemLp μ p (f n))
    {g : X → ℂ} (hg : CorrectedBookMemLp μ p g)
    (hlim : Tendsto (fun n => correctedBookLpDist μ p (f n) g) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun k => f (ns k) x) atTop (𝓝 (g x)) := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hnorm : Tendsto (fun n => correctedBookLpNorm μ p (f n - g)) atTop (𝓝 0) :=
    ((remarks_3_10_tendsto_iff μ p hf hg).1).mp hlim
  exact theorem_3_12_of_norm_tendsto μ hp0
    (fun n => ((correctedBookMemLp_iff_memLp μ p (f n)).mp (hf n)).2.1)
    (((correctedBookMemLp_iff_memLp μ p g).mp hg).2.1) hnorm

/-- Quotient-space form of Theorem 3.12 (`Lp ℂ p μ`, `1 ≤ p ≤ ∞`). -/
theorem theorem_3_12_lp {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {F : ℕ → Lp ℂ p μ} {G : Lp ℂ p μ} (hFG : Tendsto F atTop (𝓝 G)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun k => F (ns k) x) atTop (𝓝 (G x)) :=
  (tendstoInMeasure_of_tendsto_Lp hFG).exists_seq_tendsto_ae

/-- Canonical summary declaration for RCA Theorem 3.12 (printed p. 68). -/
theorem theorem3_12 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : ℕ → X → ℂ} (hf : ∀ n, CorrectedBookMemLp μ p (f n))
    {g : X → ℂ} (hg : CorrectedBookMemLp μ p g)
    (hlim : Tendsto (fun n => correctedBookLpDist μ p (f n) g) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun k => f (ns k) x) atTop (𝓝 (g x)) :=
  theorem_3_12 μ hp hf hg hlim

/-! ## Section 3.13: Density of Simple Functions of Finite-Measure Support (printed p. 69) -/

/-- RCA 3.13 class `S` (printed p. 69): complex measurable simple functions `s : X → ℂ`
such that `μ({x : s(x) ≠ 0}) < ∞`. -/
def BookSimpleFiniteSupport {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : X → ℂ) : Prop :=
  Chapter01.IsSimple s ∧ Measurable s ∧ μ {x : X | s x ≠ 0} < ∞

/-- Bridge from `BookSimpleFiniteSupport μ s` to Mathlib's `SimpleFunc X ℂ`. -/
def BookSimpleFiniteSupport.toSimpleFunc {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {s : X → ℂ} (hs : BookSimpleFiniteSupport μ s) : SimpleFunc X ℂ where
  toFun := s
  measurableSet_fiber' a := hs.2.1 (measurableSet_singleton a)
  finite_range' := hs.1

/-- First part of Rudin's proof of Theorem 3.13 (printed p. 69): `S ⊂ L^p(μ)` for every
`0 < p ≤ ∞` (and in particular for `0 < p < ∞`). -/
theorem theorem_3_13_subset_lp {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {s : X → ℂ} (hs : BookSimpleFiniteSupport μ s) :
    (∀ {p : ℝ}, 0 < p → BookMemLpFinite μ p s) ∧
    (∀ {p : ℝ≥0∞}, p ≠ 0 → CorrectedBookMemLp μ p s) := by
  let g : SimpleFunc X ℂ := hs.toSimpleFunc
  have hmem_all : ∀ p : ℝ≥0∞, MemLp s p μ := fun p => by
    have hpre : ∀ y : ℂ, y ≠ 0 → μ (g ⁻¹' {y}) < ∞ := fun y hy => by
      refine (measure_mono ?_).trans_lt hs.2.2
      intro x hx
      change s x = y at hx
      change s x ≠ 0
      rw [hx]
      exact hy
    exact SimpleFunc.memLp_of_finite_measure_preimage (f := g) p hpre
  refine ⟨fun {p} hp => (definition_3_6_memLp_iff μ hp s).mpr ⟨hs.2.1, hmem_all _⟩,
    fun {p} hp0 => (correctedBookMemLp_iff_memLp μ p s).mpr ⟨hp0, hs.2.1, hmem_all p⟩⟩

/-- RCA Theorem 3.13 (printed p. 69, retaining Rudin's full exponent range `0 < p < ∞`,
including `0 < p < 1`): let `S` (`BookSimpleFiniteSupport μ`) be the class of complex measurable
simple functions `s` on `X` with `μ({x : s(x) ≠ 0}) < ∞`. If `0 < p < ∞`, then `S ⊆ L^p(μ)` and
`S` is dense in `L^p(μ)` (`∀ f ∈ L^p(μ), ∀ ε > 0, ∃ s ∈ S, ‖f - s‖_p < ε`). -/
theorem theorem_3_13 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ} (hp : 0 < p) :
    (∀ s : X → ℂ, BookSimpleFiniteSupport μ s → BookMemLpFinite μ p s) ∧
    (∀ f : X → ℂ, BookMemLpFinite μ p f → ∀ ε : ℝ, 0 < ε →
      ∃ s : X → ℂ, BookSimpleFiniteSupport μ s ∧
        BookMemLpFinite μ p (f - s) ∧
        bookELpNormFinite μ p (f - s) < ENNReal.ofReal ε ∧
        (bookELpNormFinite μ p (f - s)).toReal < ε) := by
  refine ⟨fun s hs => (theorem_3_13_subset_lp μ hs).1 hp, ?_⟩
  intro f hf ε hε
  obtain ⟨hf_meas, hf_mem⟩ := (definition_3_6_memLp_iff μ hp f).mp hf
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hp_top : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hδ0 : ENNReal.ofReal (ε / 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
  obtain ⟨g, hg_lt, hg_mem⟩ := hf_mem.exists_simpleFunc_eLpNorm_sub_lt hp_top hδ0
  let s : X → ℂ := ⇑g
  have hs_supp : μ {x : X | s x ≠ 0} < ∞ :=
    SimpleFunc.measure_support_lt_top_of_memLp g hg_mem hp0 hp_top
  have hs_class : BookSimpleFiniteSupport μ s := ⟨g.finite_range, g.measurable, hs_supp⟩
  have hfs_book : BookMemLpFinite μ p (f - s) :=
    (definition_3_6_memLp_iff μ hp (f - s)).mpr ⟨hf_meas.sub g.measurable, hf_mem.sub hg_mem⟩
  have hnorm_eq : bookELpNormFinite μ p (f - s) = eLpNorm (f - s) (ENNReal.ofReal p) μ :=
    definition_3_6_eq_eLpNorm μ hp (hf_meas.sub g.measurable)
  have hlt_half : bookELpNormFinite μ p (f - s) < ENNReal.ofReal (ε / 2) := by
    rwa [hnorm_eq]
  have hlt_enn : bookELpNormFinite μ p (f - s) < ENNReal.ofReal ε :=
    hlt_half.trans (ENNReal.ofReal_lt_ofReal_iff hε |>.mpr (half_lt_self hε))
  have hlt_real : (bookELpNormFinite μ p (f - s)).toReal < ε := by
    have hle : (bookELpNormFinite μ p (f - s)).toReal ≤ (ENNReal.ofReal (ε / 2)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hlt_half.le
    rw [ENNReal.toReal_ofReal (half_pos hε).le] at hle
    linarith
  exact ⟨s, hs_class, hfs_book, hlt_enn, hlt_real⟩

/-- Topological density specialization of Theorem 3.13 in the normed space `Lp ℂ p μ`
for `1 ≤ p < ∞`. -/
theorem theorem_3_13_dense_lp {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (hp_top : p ≠ ∞) :
    Dense {F : Lp ℂ p μ | ∃ s : X → ℂ, BookSimpleFiniteSupport μ s ∧
      ∃ hs : CorrectedBookMemLp μ p s, correctedBookToLp μ p hp.out ⟨s, hs⟩ = F} := by
  rw [Metric.dense_iff]
  intro F ε hε
  obtain ⟨⟨f, hf_book⟩, rfl⟩ := remarks_3_10_toLp_surjective μ p hp.out F
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp.out).ne' hp_top
  have hp_eq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hp_top
  obtain ⟨_, hf_meas, hf_mem⟩ := (correctedBookMemLp_iff_memLp μ p f).mp hf_book
  have hf_fin : BookMemLpFinite μ p.toReal f := by
    rw [definition_3_6_memLp_iff μ hp_pos, hp_eq]
    exact ⟨hf_meas, hf_mem⟩
  obtain ⟨s, hs_class, _, _, hlt_real⟩ := (theorem_3_13 μ hp_pos).2 f hf_fin ε hε
  have hs_book : CorrectedBookMemLp μ p s :=
    (theorem_3_13_subset_lp μ hs_class).2 (zero_lt_one.trans_le hp.out).ne'
  refine ⟨correctedBookToLp μ p hp.out ⟨s, hs_book⟩, ?_,
    ⟨s, hs_class, hs_book, rfl⟩⟩
  rw [Metric.mem_ball, dist_comm,
    remarks_3_10_toLp_dist μ p ⟨f, hf_book⟩ ⟨s, hs_book⟩]
  unfold correctedBookLpDist
  rw [correctedBookLpNorm_eq_eLpNorm μ (zero_lt_one.trans_le hp.out).ne' (hf_meas.sub hs_class.2.1),
    ← hp_eq, ← definition_3_6_eq_eLpNorm μ hp_pos (hf_meas.sub hs_class.2.1)]
  exact hlt_real

/-- Canonical summary declaration for RCA Theorem 3.13 (printed p. 69). -/
theorem theorem3_13 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ} (hp : 0 < p) :
    (∀ s : X → ℂ, BookSimpleFiniteSupport μ s → BookMemLpFinite μ p s) ∧
    (∀ f : X → ℂ, BookMemLpFinite μ p f → ∀ ε : ℝ, 0 < ε →
      ∃ s : X → ℂ, BookSimpleFiniteSupport μ s ∧
        BookMemLpFinite μ p (f - s) ∧
        (bookELpNormFinite μ p (f - s)).toReal < ε) := by
  obtain ⟨hsub, hdense⟩ := theorem_3_13 μ hp
  exact ⟨hsub, fun f hf ε hε =>
    let ⟨s, hs, hfs, _, hlt⟩ := hdense f hf ε hε
    ⟨s, hs, hfs, hlt⟩⟩

/-! ## General Metric Completion Helper (used in Sections 3.17 and 3.15) -/

/-- Any isometric embedding `ι : α → β` with dense range into a complete metric space `β`
extends to an isometric bijection `UniformSpace.Completion α ≃ᵢ β` commuting with `ι`. -/
noncomputable def completionIsometryEquivOfDenseIsometry {α β : Type*}
    [MetricSpace α] [MetricSpace β] [CompleteSpace β]
    {ι : α → β} (hiso : Isometry ι) (hdense : DenseRange ι) :
    UniformSpace.Completion α ≃ᵢ β := by
  let extFn : UniformSpace.Completion α → β := UniformSpace.Completion.extension ι
  have hext_iso : Isometry extFn := hiso.completion_extension
  have hext_coe : ∀ x : α, extFn x = ι x :=
    UniformSpace.Completion.extension_coe hiso.uniformContinuous
  have hsurj : Function.Surjective extFn := by
    intro y
    have hex : ∀ n : ℕ, ∃ x : α, dist y (ι x) < 1 / ((n : ℝ) + 1) := fun n =>
      Metric.denseRange_iff.mp hdense y (1 / ((n : ℝ) + 1)) (by positivity)
    choose x hx using hex
    have hconv_y : Tendsto (fun n => ι (x n)) atTop (𝓝 y) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      refine ⟨N, fun n hn => ?_⟩
      rw [dist_comm]
      refine (hx n).trans (lt_of_le_of_lt ?_ hN)
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    have hcauchy_x : CauchySeq (fun n => (x n : UniformSpace.Completion α)) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hconv_y.cauchySeq ε hε
      refine ⟨N, fun m hm n hn => ?_⟩
      rw [UniformSpace.Completion.dist_eq, ← hiso.dist_eq]
      exact hN m hm n hn
    obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcauchy_x
    have hext_z : Tendsto (fun n => extFn (x n)) atTop (𝓝 (extFn z)) :=
      (hext_iso.continuous.tendsto z).comp hz
    simp_rw [hext_coe] at hext_z
    exact ⟨z, tendsto_nhds_unique hext_z hconv_y⟩
  exact
    { toEquiv := Equiv.ofBijective extFn ⟨hext_iso.injective, hsurj⟩
      isometry_toFun := hext_iso }

theorem completionIsometryEquivOfDenseIsometry_coe {α β : Type*}
    [MetricSpace α] [MetricSpace β] [CompleteSpace β]
    {ι : α → β} (hiso : Isometry ι) (hdense : DenseRange ι) (x : α) :
    completionIsometryEquivOfDenseIsometry hiso hdense x = ι x :=
  UniformSpace.Completion.extension_coe hiso.uniformContinuous x

/-! ## Section 3.14: Density of $C_c(X)$ in $L^p(\mu)$ for $1 \le p < \infty$ (printed p. 69) -/

/-- Explicit measure-regularity hypotheses from RCA Theorem 2.14(a–d) referenced on p. 69
before Theorem 3.14, stated using the exact Chapter 2 regularity predicates
(`Chapter02.BookOuterRegularSet`, `Chapter02.BookInnerRegularSet`) without assuming the
out-of-scope Riesz existence theorem 2.14:
1. the `σ`-algebra contains `borel X`;
2. `μ(K) < ∞` for every compact `K ⊆ X` (2.14(b));
3. outer regularity `μ(E) = inf {μ(V) : E ⊆ V, V open}` for every measurable `E` (2.14(c));
4. inner regularity `μ(U) = sup {μ(K) : K ⊆ U, K compact}` for every open `U` (2.14(d));
5. inner regularity `μ(E) = sup {μ(K) : K ⊆ E, K compact}` for every measurable `E` with
   `μ(E) < ∞` (2.14(d)). -/
def Book214RegularityHypotheses {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) : Prop :=
  borel X ≤ ‹MeasurableSpace X› ∧
  (∀ K : Set X, IsCompact K → μ K < ∞) ∧
  (∀ E : Set X, MeasurableSet E → Chapter02.BookOuterRegularSet μ E) ∧
  (∀ U : Set X, IsOpen U → Chapter02.BookInnerRegularSet μ U) ∧
  (∀ E : Set X, MeasurableSet E → μ E < ∞ → Chapter02.BookInnerRegularSet μ E)

theorem Book214RegularityHypotheses.measurableSet_of_isOpen {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X} (hreg : Book214RegularityHypotheses μ)
    {U : Set X} (hU : IsOpen U) : MeasurableSet U :=
  hreg.1 _ (MeasurableSpace.measurableSet_generateFrom hU)

theorem Book214RegularityHypotheses.measurableSet_of_isClosed {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X} (hreg : Book214RegularityHypotheses μ)
    {F : Set X} (hF : IsClosed F) : MeasurableSet F := by
  simpa using (hreg.measurableSet_of_isOpen hF.isOpen_compl).compl

/-- Every regular Borel measure in Rudin's Definition 2.15 (`Chapter02.BookRegularBorelMeasure`)
that is finite on compact sets satisfies `Book214RegularityHypotheses`. -/
theorem theorem_3_14_regularBorel_satisfies {X : Type*} [TopologicalSpace X]
    (μ : Chapter02.BookPositiveBorelMeasure X)
    (hreg : Chapter02.BookRegularBorelMeasure μ)
    (hcompact : ∀ K : Set X, IsCompact K → μ K < ∞) :
    @Book214RegularityHypotheses X _ (borel X) μ := by
  let : MeasurableSpace X := borel X
  have hb : BorelSpace X := ⟨rfl⟩
  refine ⟨le_rfl, hcompact, fun E hE => (hreg E hE).1, ?_, fun E hE _ => (hreg E hE).2⟩
  intro U hU
  exact (hreg U hU.measurableSet).2

/-- Every Mathlib regular Borel measure `[BorelSpace X] [μ.Regular]` satisfies
`Book214RegularityHypotheses` (without requiring `NormalSpace X`). -/
theorem theorem_3_14_mathlib_regular_satisfies {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.Regular] :
    Book214RegularityHypotheses μ := by
  refine ⟨le_of_eq BorelSpace.measurable_eq.symm,
    fun _ hK => hK.measure_lt_top,
    fun E _ => Set.measure_eq_iInf_isOpen E μ, ?_, ?_⟩
  · intro U hU
    unfold Chapter02.BookInnerRegularSet
    refine le_antisymm ?_
      (iSup_le fun K => iSup_le fun hKU => iSup_le fun _ => measure_mono hKU)
    refine le_of_forall_lt fun r hr => ?_
    obtain ⟨K, hKU, hKc, hrK⟩ := Measure.Regular.innerRegular hU r hr
    exact lt_iSup_iff.mpr ⟨K, lt_iSup_iff.mpr ⟨hKU, lt_iSup_iff.mpr ⟨hKc, hrK⟩⟩⟩
  · intro E hE hE_fin
    unfold Chapter02.BookInnerRegularSet
    refine le_antisymm ?_
      (iSup_le fun K => iSup_le fun hKE => iSup_le fun _ => measure_mono hKE)
    refine le_of_forall_lt fun r hr => ?_
    obtain ⟨K, hKE, hKc, hrK⟩ :=
      Measure.InnerRegularCompactLTTop.innerRegular ⟨hE, hE_fin.ne⟩ r hr
    exact lt_iSup_iff.mpr ⟨K, lt_iSup_iff.mpr ⟨hKE, lt_iSup_iff.mpr ⟨hKc, hrK⟩⟩⟩

/-- Completion transfer (`Chapter01.completedMeasure`, RCA 1.36 / 2.14): if `μ` satisfies
`Book214RegularityHypotheses`, then its completion `(Chapter01.completionSigma μ, Chapter01.completedMeasure μ)`
also satisfies `Book214RegularityHypotheses`. -/
theorem theorem_3_14_completedMeasure_preserves {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X} (hreg : Book214RegularityHypotheses μ) :
    @Book214RegularityHypotheses X _ (Chapter01.completionSigma μ)
      (Chapter01.completedMeasure μ) := by
  obtain ⟨hborel, hK_fin, houter, hopen_inner, hfin_inner⟩ := hreg
  have hle_comp : ‹MeasurableSpace X› ≤ Chapter01.completionSigma μ :=
    fun _ hs => hs.nullMeasurableSet
  have happly : ∀ S : Set X, Chapter01.completedMeasure μ S = μ S :=
    fun S => Measure.completion_apply μ S
  refine ⟨hborel.trans hle_comp, fun K hK => by rw [happly]; exact hK_fin K hK, ?_, ?_, ?_⟩
  · intro E hE
    unfold Chapter02.BookOuterRegularSet
    obtain ⟨A, B, hA, hB, hAE, hEB, hnull⟩ := ((Chapter01.theorem_1_36 μ).1 E).mp hE
    have hμE : Chapter01.completedMeasure μ E = μ A :=
      (Chapter01.theorem_1_36 μ).2.1 E A B hA hB hAE hEB hnull
    have hμBA : μ B = μ A := by
      refine le_antisymm ?_ (measure_mono (hAE.trans hEB))
      calc
        μ B ≤ μ (A ∪ (B \ A)) := measure_mono (fun x hx => by by_cases hxA : x ∈ A <;> simp [hx, hxA])
        _ ≤ μ A + μ (B \ A) := measure_union_le A (B \ A)
        _ = μ A := by rw [hnull, add_zero]
    refine le_antisymm
      (le_iInf fun V => le_iInf fun hEV => le_iInf fun _ => by
        rw [happly, happly]
        exact measure_mono hEV) ?_
    calc
      (⨅ (V : Set X) (_ : E ⊆ V) (_ : IsOpen V), Chapter01.completedMeasure μ V)
          ≤ ⨅ (V : Set X) (_ : B ⊆ V) (_ : IsOpen V), μ V := by
        refine le_iInf fun V => le_iInf fun hBV => le_iInf fun hV => ?_
        rw [← happly V]
        exact iInf_le_of_le V (iInf_le_of_le (hEB.trans hBV) (iInf_le_of_le hV le_rfl))
      _ = μ B := (houter B hB).symm
      _ = Chapter01.completedMeasure μ E := by rw [hμBA, hμE]
  · intro U hU
    unfold Chapter02.BookInnerRegularSet
    simp_rw [happly]
    exact hopen_inner U hU
  · intro E hE hE_fin
    unfold Chapter02.BookInnerRegularSet
    obtain ⟨A, B, hA, hB, hAE, hEB, hnull⟩ := ((Chapter01.theorem_1_36 μ).1 E).mp hE
    have hμE : Chapter01.completedMeasure μ E = μ A :=
      (Chapter01.theorem_1_36 μ).2.1 E A B hA hB hAE hEB hnull
    have hμA_fin : μ A < ∞ := by rwa [← hμE]
    refine le_antisymm ?_
      (iSup_le fun K => iSup_le fun hKE => iSup_le fun _ => by
        rw [happly, happly]
        exact measure_mono hKE)
    calc
      Chapter01.completedMeasure μ E = μ A := hμE
      _ = ⨆ (K : Set X) (_ : K ⊆ A) (_ : IsCompact K), μ K := hfin_inner A hA hμA_fin
      _ ≤ ⨆ (K : Set X) (_ : K ⊆ E) (_ : IsCompact K), Chapter01.completedMeasure μ K := by
        refine iSup_le fun K => iSup_le fun hKA => iSup_le fun hKc => ?_
        rw [← happly K]
        exact le_iSup_of_le K (le_iSup_of_le (hKA.trans hAE) (le_iSup_of_le hKc le_rfl))

/-- Every `g : C_c(X, ℂ)` lies in `L^p(μ)` for all `0 < p ≤ ∞` whenever `μ` is Borel-measurable
on open sets and finite on compact sets. -/
theorem theorem_3_14_cc_memLp {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] {μ : Measure X} (hreg : Book214RegularityHypotheses μ)
    (g : C_c(X, ℂ)) :
    (∀ {p : ℝ}, 0 < p → BookMemLpFinite μ p g) ∧
    (∀ {p : ℝ≥0∞}, p ≠ 0 → CorrectedBookMemLp μ p g) := by
  have hg_meas : Measurable (g : X → ℂ) := g.continuous.borel_measurable.mono hreg.1 le_rfl
  let K : Set X := tsupport (g : X → ℂ)
  have hK : IsCompact K := g.hasCompactSupport
  have hK_meas : MeasurableSet K := hreg.measurableSet_of_isClosed hK.isClosed
  have hK_fin : μ K < ∞ := hreg.2.1 K hK
  let f0 : C₀(X, ℂ) := ccToC0 g
  let s : X → ℂ := K.indicator (fun _ => (‖f0‖ : ℂ))
  have hs_simple : Chapter01.IsSimple s := by
    refine ({0, (‖f0‖ : ℂ)} : Set ℂ).toFinite.subset ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ K <;> simp [s, hx]
  have hs_meas : Measurable s := measurable_const.indicator hK_meas
  have hs_supp : μ {x : X | s x ≠ 0} < ∞ := by
    refine (measure_mono ?_).trans_lt hK_fin
    intro x hx
    by_contra hxK
    exact hx (by simp [s, hxK])
  have hs_class : BookSimpleFiniteSupport μ s := ⟨hs_simple, hs_meas, hs_supp⟩
  have hbound : ∀ x : X, ‖g x‖ ≤ ‖s x‖ := by
    intro x
    by_cases hx : x ∈ K
    · simp only [s, indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg f0)]
      exact BoundedContinuousFunction.norm_coe_le_norm (f := f0.toBCF) x
    · have hg0 : g x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hg0]
  have hmem_all : ∀ p : ℝ≥0∞, MemLp (g : X → ℂ) p μ := fun p => by
    have hs_mem : MemLp s p μ := by
      by_cases hp0 : p = 0
      · subst hp0
        exact memLp_zero_iff_aestronglyMeasurable.mpr hs_meas.aestronglyMeasurable
      · exact ((correctedBookMemLp_iff_memLp μ p s).mp
          ((theorem_3_13_subset_lp μ hs_class).2 hp0)).2.2
    exact (eLpNorm_mono hg_meas.aestronglyMeasurable hbound).trans_lt hs_mem
  refine ⟨fun {p} hp => (definition_3_6_memLp_iff μ hp g).mpr ⟨hg_meas, hmem_all _⟩,
    fun {p} hp0 => (correctedBookMemLp_iff_memLp μ p g).mpr ⟨hp0, hg_meas, hmem_all p⟩⟩

/-- Key Urysohn indicator-approximation step of Rudin's proof of Theorem 3.14 (printed p. 69):
on a locally compact Hausdorff space `X` under `Book214RegularityHypotheses μ`, for any `0 < p < ∞`,
measurable `E` with `μ(E) < ∞`, and `ε > 0`, there exists a cutoff `φ : C_c(X, ℂ)` with
`‖1_E - φ‖_p < ε`. -/
theorem theorem_3_14_indicator_approx {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] {μ : Measure X}
    (hreg : Book214RegularityHypotheses μ) {p : ℝ} (hp : 0 < p)
    {E : Set X} (hE : MeasurableSet E) (hE_fin : μ E < ∞)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : C_c(X, ℂ),
      (bookELpNormFinite μ p (E.indicator (1 : X → ℂ) - φ)).toReal < ε := by
  let rReal : ℝ := (ε / 2) ^ p / 2
  have hrReal_pos : 0 < rReal := by positivity
  let r : ℝ≥0∞ := ENNReal.ofReal rReal
  have hr_pos : 0 < r := ENNReal.ofReal_pos.mpr hrReal_pos
  have hexK : ∃ K : Set X, K ⊆ E ∧ IsCompact K ∧ μ (E \ K) ≤ r := by
    by_cases hle : μ E ≤ r
    · exact ⟨∅, Set.empty_subset E, isCompact_empty, by simpa using hle⟩
    · have hlt : r < μ E := not_le.mp hle
      have hsub_lt : μ E - r < ⨆ (K : Set X) (_ : K ⊆ E) (_ : IsCompact K), μ K := by
        rw [← hreg.2.2.2.2 E hE hE_fin]
        exact ENNReal.sub_lt_self hE_fin.ne (hr_pos.trans hlt).ne' hr_pos.ne'
      obtain ⟨K, h1⟩ := lt_iSup_iff.mp hsub_lt
      obtain ⟨hKE, h2⟩ := lt_iSup_iff.mp h1
      obtain ⟨hK, hμK⟩ := lt_iSup_iff.mp h2
      have hK_meas : MeasurableSet K := hreg.measurableSet_of_isClosed hK.isClosed
      have hK_fin : μ K < ∞ := hreg.2.1 K hK
      have hunion : μ (E \ K) + μ K = μ E := by
        rw [← measure_union disjoint_sdiff_left hK_meas, sdiff_union_of_subset hKE]
      have hsum_le : μ (E \ K) + μ K ≤ r + μ K := by
        rw [hunion, add_comm r (μ K)]
        calc
          μ E = (μ E - r) + r := (tsub_add_cancel_of_le hlt.le).symm
          _ ≤ μ K + r := add_le_add hμK.le le_rfl
      exact ⟨K, hKE, hK, (ENNReal.add_le_add_iff_right hK_fin.ne).mp hsum_le⟩
  obtain ⟨K, hKE, hK, hEK_le⟩ := hexK
  have hexV : ∃ V : Set X, E ⊆ V ∧ IsOpen V ∧ μ (V \ E) ≤ r := by
    have hlt : (⨅ (V : Set X) (_ : E ⊆ V) (_ : IsOpen V), μ V) < μ E + r := by
      rw [← hreg.2.2.1 E hE]
      exact ENNReal.lt_add_right hE_fin.ne hr_pos.ne'
    obtain ⟨V, h1⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hEV, h2⟩ := iInf_lt_iff.mp h1
    obtain ⟨hV, hμV⟩ := iInf_lt_iff.mp h2
    have hunion : μ (V \ E) + μ E = μ V := by
      rw [← measure_union disjoint_sdiff_left hE, sdiff_union_of_subset hEV]
    have hsum_le : μ (V \ E) + μ E ≤ r + μ E := by
      rw [hunion, add_comm r (μ E)]
      exact hμV.le
    exact ⟨V, hEV, hV, (ENNReal.add_le_add_iff_right hE_fin.ne).mp hsum_le⟩
  obtain ⟨V, hEV, hV, hVE_le⟩ := hexV
  obtain ⟨φ, ⟨_, hφ_cut, hφ_K⟩, ⟨_, _, hφ_V⟩⟩ :=
    Chapter02.lemma_2_12 hK hV (hKE.trans hEV)
  refine ⟨φ, ?_⟩
  have hVK_meas : MeasurableSet (V \ K) :=
    (hreg.measurableSet_of_isOpen hV).diff (hreg.measurableSet_of_isClosed hK.isClosed)
  have hVK_le : μ (V \ K) ≤ ENNReal.ofReal ((ε / 2) ^ p) := by
    have hsub : V \ K ⊆ (V \ E) ∪ (E \ K) := by
      intro x ⟨hxV, hxK⟩
      by_cases hxE : x ∈ E
      · exact Or.inr ⟨hxE, hxK⟩
      · exact Or.inl ⟨hxV, hxE⟩
    calc
      μ (V \ K) ≤ μ ((V \ E) ∪ (E \ K)) := measure_mono hsub
      _ ≤ μ (V \ E) + μ (E \ K) := measure_union_le _ _
      _ ≤ r + r := add_le_add hVE_le hEK_le
      _ = ENNReal.ofReal ((ε / 2) ^ p) := by
        dsimp [r]
        rw [← ENNReal.ofReal_add hrReal_pos.le hrReal_pos.le]
        congr 1
        dsimp [rReal]
        ring
  have hpt : ∀ x : X,
      ‖(E.indicator (1 : X → ℂ) - (φ : X → ℂ)) x‖ ≤ (V \ K).indicator (1 : X → ℝ) x := by
    intro x
    by_cases hxK : x ∈ K
    · have hxE : x ∈ E := hKE hxK
      have hφ1 : φ x = 1 := hφ_K hxK
      have hxVK : x ∉ V \ K := fun h => h.2 hxK
      simp [hxE, hφ1, hxVK]
    · by_cases hxV : x ∈ V
      · have hxVK : x ∈ V \ K := ⟨hxV, hxK⟩
        obtain ⟨t, ⟨ht0, ht1⟩, hφt⟩ := hφ_cut x
        rw [Pi.sub_apply, hφt, indicator_of_mem hxVK, Pi.one_apply]
        by_cases hxE : x ∈ E
        · rw [indicator_of_mem hxE, Pi.one_apply, ← Complex.ofReal_one, ← Complex.ofReal_sub,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          linarith
        · rw [indicator_of_notMem hxE, ← Complex.ofReal_zero, ← Complex.ofReal_sub,
            Complex.norm_real, Real.norm_eq_abs, zero_sub, abs_neg, abs_of_nonneg ht0]
          exact ht1
      · have hxE : x ∉ E := fun h => hxV (hEV h)
        have hx_supp : x ∉ tsupport (φ : X → ℂ) := fun h => hxV (hφ_V h)
        have hφ0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx_supp
        have hxVK : x ∉ V \ K := fun h => hxV h.1
        simp [hxE, hφ0, hxVK]
  have hlint :
      (∫⁻ x, ‖(E.indicator (1 : X → ℂ) - (φ : X → ℂ)) x‖ₑ ^ p ∂μ) ≤
        ENNReal.ofReal ((ε / 2) ^ p) := by
    calc
      (∫⁻ x, ‖(E.indicator (1 : X → ℂ) - (φ : X → ℂ)) x‖ₑ ^ p ∂μ)
          ≤ ∫⁻ x, (V \ K).indicator (1 : X → ℝ≥0∞) x ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_norm]
        have h1 := ENNReal.ofReal_le_ofReal (hpt x)
        have h2 := ENNReal.rpow_le_rpow h1 hp.le
        refine h2.trans ?_
        by_cases hx : x ∈ V \ K
        · simp [hx]
        · simp [hx, ENNReal.zero_rpow_of_pos hp]
      _ = μ (V \ K) := lintegral_indicator_one hVK_meas
      _ ≤ ENNReal.ofReal ((ε / 2) ^ p) := hVK_le
  have hnorm_le :
      bookELpNormFinite μ p (E.indicator (1 : X → ℂ) - φ) ≤ ENNReal.ofReal (ε / 2) := by
    unfold bookELpNormFinite
    calc
      (∫⁻ x, ‖(E.indicator (1 : X → ℂ) - (φ : X → ℂ)) x‖ₑ ^ p ∂μ) ^ (1 / p)
          ≤ (ENNReal.ofReal ((ε / 2) ^ p)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hlint (one_div_nonneg.mpr hp.le)
      _ = ENNReal.ofReal (ε / 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (one_div_nonneg.mpr hp.le),
          one_div, Real.rpow_rpow_inv (half_pos hε).le hp.ne']
  have hreal_le :
      (bookELpNormFinite μ p (E.indicator (1 : X → ℂ) - φ)).toReal ≤ ε / 2 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm_le
    rwa [ENNReal.toReal_ofReal (half_pos hε).le] at h
  linarith

/-- Approximation of any `s ∈ BookSimpleFiniteSupport μ` by `C_c(X, ℂ)` in `L^p(μ)` for `1 ≤ p < ∞`. -/
private theorem theorem_3_14_simple_approx {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] {μ : Measure X}
    (hreg : Book214RegularityHypotheses μ) {p : ℝ} (hp : 1 ≤ p)
    {s : X → ℂ} (hs : BookSimpleFiniteSupport μ s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C_c(X, ℂ), (bookELpNormFinite μ p (s - g)).toReal < ε := by
  classical
  have hp_pos : 0 < p := zero_lt_one.trans_le hp
  have hp_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp_pos).ne'
  have hto_corr : ∀ {u : X → ℂ}, BookMemLpFinite μ p u →
      CorrectedBookMemLp μ (ENNReal.ofReal p) u ∧
      (bookELpNormFinite μ p u).toReal =
        (correctedBookLpNorm μ (ENNReal.ofReal p) u).toReal := by
    intro u hu
    obtain ⟨hu_meas, hu_mem⟩ := (definition_3_6_memLp_iff μ hp_pos u).mp hu
    refine ⟨(correctedBookMemLp_iff_memLp μ _ u).mpr ⟨hp0, hu_meas, hu_mem⟩, ?_⟩
    rw [definition_3_6_eq_eLpNorm μ hp_pos hu_meas,
      correctedBookLpNorm_eq_eLpNorm μ hp0 hu_meas]
  let A : Finset ℂ := hs.1.toFinset.erase 0
  have hs_decomp : s = ∑ a ∈ A, a • (s ⁻¹' {a}).indicator (1 : X → ℂ) := by
    ext x
    rw [Finset.sum_apply]
    by_cases hx0 : s x = 0
    · refine hx0.trans (Finset.sum_eq_zero fun a ha => ?_).symm
      have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
      have hx_not : x ∉ s ⁻¹' {a} := by simp [hx0, ha0.symm]
      simp [hx_not]
    · have hxA : s x ∈ A :=
        Finset.mem_erase.mpr ⟨hx0, hs.1.mem_toFinset.mpr ⟨x, rfl⟩⟩
      rw [Finset.sum_eq_single (s x)]
      · simp
      · intro a _ hne
        have hx_not : x ∉ s ⁻¹' {a} := by simp [hne.symm]
        simp [hx_not]
      · intro hnot
        exact absurd hxA hnot
  have hterm_valid : ∀ a ∈ A, a ≠ 0 ∧ MeasurableSet (s ⁻¹' {a}) ∧ μ (s ⁻¹' {a}) < ∞ := by
    intro a ha
    have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
    refine ⟨ha0, hs.2.1 (measurableSet_singleton a), (measure_mono ?_).trans_lt hs.2.2⟩
    intro x hx
    change s x = a at hx
    change s x ≠ 0
    rw [hx]
    exact ha0
  suffices hfinset : ∀ (B : Finset ℂ),
      (∀ a ∈ B, a ≠ 0 ∧ MeasurableSet (s ⁻¹' {a}) ∧ μ (s ⁻¹' {a}) < ∞) →
      ∀ δ : ℝ, 0 < δ →
      ∃ g : C_c(X, ℂ),
        BookMemLpFinite μ p ((∑ a ∈ B, a • (s ⁻¹' {a}).indicator (1 : X → ℂ)) - g) ∧
        (bookELpNormFinite μ p
          ((∑ a ∈ B, a • (s ⁻¹' {a}).indicator (1 : X → ℂ)) - g)).toReal < δ by
    obtain ⟨g, _, hlt⟩ := hfinset A hterm_valid ε hε
    rw [← hs_decomp] at hlt
    exact ⟨g, hlt⟩
  intro B
  refine Finset.induction_on B ?_ ?_
  · intro _ δ hδ
    refine ⟨0, ?_, ?_⟩
    · have h0 : ((0 : X → ℂ) - ((0 : C_c(X, ℂ)) : X → ℂ)) = 0 := by ext; simp
      simpa [h0] using (theorem_3_14_cc_memLp hreg 0).1 hp_pos
    · have h0 : ((0 : X → ℂ) - ((0 : C_c(X, ℂ)) : X → ℂ)) = 0 := by ext; simp
      rw [Finset.sum_empty, h0, definition_3_6_eq_eLpNorm μ hp_pos measurable_zero,
        eLpNorm_zero, ENNReal.toReal_zero]
      exact hδ
  · intro a B ha_notMem ih hB δ hδ
    obtain ⟨ha0, ha_meas, ha_fin⟩ := hB a (Finset.mem_insert_self a B)
    have hnorm_a : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    obtain ⟨φ, hφ_lt⟩ := theorem_3_14_indicator_approx hreg hp_pos ha_meas ha_fin
      (div_pos (half_pos hδ) hnorm_a)
    obtain ⟨ψ, hψ_mem, hψ_lt⟩ :=
      ih (fun b hb => hB b (Finset.mem_insert_of_mem hb)) (δ / 2) (half_pos hδ)
    refine ⟨a • φ + ψ, ?_, ?_⟩
    · have hind_class : BookSimpleFiniteSupport μ ((s ⁻¹' {a}).indicator (1 : X → ℂ)) := by
        refine ⟨({0, 1} : Set ℂ).toFinite.subset ?_, measurable_const.indicator ha_meas, ?_⟩
        · rintro _ ⟨x, rfl⟩; by_cases hx : x ∈ s ⁻¹' {a} <;> simp [hx]
        · refine (measure_mono fun x hx => ?_).trans_lt ha_fin
          by_contra hxA; exact hx (by simp [hxA])
      have hind_mem : CorrectedBookMemLp μ (ENNReal.ofReal p)
          ((s ⁻¹' {a}).indicator (1 : X → ℂ) - φ) := by
        have h1 := (theorem_3_13_subset_lp μ hind_class).2 hp0
        have h2 := (remarks_3_10_smul μ (-1 : ℂ) ((theorem_3_14_cc_memLp hreg φ).2 hp0)).1
        simpa [sub_eq_add_neg] using (theorem_3_9 μ hp_one h1 h2).1
      have hsmul_mem := (remarks_3_10_smul μ a hind_mem).1
      have hψ_corr := (hto_corr hψ_mem).1
      have hsum_corr := (theorem_3_9 μ hp_one hsmul_mem hψ_corr).1
      have heq : a • ((s ⁻¹' {a}).indicator (1 : X → ℂ) - (φ : X → ℂ)) +
          ((∑ b ∈ B, b • (s ⁻¹' {b}).indicator (1 : X → ℂ)) - (ψ : X → ℂ)) =
          (∑ b ∈ insert a B, b • (s ⁻¹' {b}).indicator (1 : X → ℂ)) -
            ((a • φ + ψ : C_c(X, ℂ)) : X → ℂ) := by
        ext x
        simp [Finset.sum_insert ha_notMem, smul_sub]
        ring
      rw [heq] at hsum_corr
      obtain ⟨_, hm1, hm2⟩ := (correctedBookMemLp_iff_memLp μ _ _).mp hsum_corr
      exact (definition_3_6_memLp_iff μ hp_pos _).mpr ⟨hm1, hm2⟩
    · have hind_class : BookSimpleFiniteSupport μ ((s ⁻¹' {a}).indicator (1 : X → ℂ)) := by
        refine ⟨({0, 1} : Set ℂ).toFinite.subset ?_, measurable_const.indicator ha_meas, ?_⟩
        · rintro _ ⟨x, rfl⟩; by_cases hx : x ∈ s ⁻¹' {a} <;> simp [hx]
        · refine (measure_mono fun x hx => ?_).trans_lt ha_fin
          by_contra hxA; exact hx (by simp [hxA])
      have hind_mem : CorrectedBookMemLp μ (ENNReal.ofReal p)
          ((s ⁻¹' {a}).indicator (1 : X → ℂ) - φ) := by
        have h1 := (theorem_3_13_subset_lp μ hind_class).2 hp0
        have h2 := (remarks_3_10_smul μ (-1 : ℂ) ((theorem_3_14_cc_memLp hreg φ).2 hp0)).1
        simpa [sub_eq_add_neg] using (theorem_3_9 μ hp_one h1 h2).1
      obtain ⟨hsmul_corr, hsmul_norm⟩ := remarks_3_10_smul μ a hind_mem
      obtain ⟨hψ_corr, hψ_norm⟩ := hto_corr hψ_mem
      have htri := (theorem_3_9 μ hp_one hsmul_corr hψ_corr).2.2
      have heq : a • ((s ⁻¹' {a}).indicator (1 : X → ℂ) - (φ : X → ℂ)) +
          ((∑ b ∈ B, b • (s ⁻¹' {b}).indicator (1 : X → ℂ)) - (ψ : X → ℂ)) =
          (∑ b ∈ insert a B, b • (s ⁻¹' {b}).indicator (1 : X → ℂ)) -
            ((a • φ + ψ : C_c(X, ℂ)) : X → ℂ) := by
        ext x
        simp [Finset.sum_insert ha_notMem, smul_sub]
        ring
      have hφ_eq : (correctedBookLpNorm μ (ENNReal.ofReal p)
          ((s ⁻¹' {a}).indicator (1 : X → ℂ) - φ)).toReal =
          (bookELpNormFinite μ p ((s ⁻¹' {a}).indicator (1 : X → ℂ) - φ)).toReal := by
        have hφ_meas : Measurable (φ : X → ℂ) := ((theorem_3_14_cc_memLp hreg φ).1 hp_pos).1
        have hm : Measurable ((s ⁻¹' {a}).indicator (1 : X → ℂ) - (φ : X → ℂ)) :=
          hind_class.2.1.sub hφ_meas
        rw [correctedBookLpNorm_eq_eLpNorm μ hp0 hm, definition_3_6_eq_eLpNorm μ hp_pos hm]
      have hsmul_lt : (correctedBookLpNorm μ (ENNReal.ofReal p)
          (a • ((s ⁻¹' {a}).indicator (1 : X → ℂ) - (φ : X → ℂ)))).toReal < δ / 2 := by
        rw [hsmul_norm, hφ_eq]
        have hmul := mul_lt_mul_of_pos_left hφ_lt hnorm_a
        rwa [mul_div_cancel₀ _ hnorm_a.ne'] at hmul
      have htotal_meas : Measurable
          ((∑ b ∈ insert a B, b • (s ⁻¹' {b}).indicator (1 : X → ℂ)) -
            ((a • φ + ψ : C_c(X, ℂ)) : X → ℂ)) :=
        ((correctedBookMemLp_iff_memLp μ _ _).mp (by
          have h := (theorem_3_9 μ hp_one hsmul_corr hψ_corr).1
          rwa [heq] at h)).2.1
      rw [definition_3_6_eq_eLpNorm μ hp_pos htotal_meas,
        ← correctedBookLpNorm_eq_eLpNorm μ hp0 htotal_meas, ← heq]
      linarith

/-- RCA Theorem 3.14 (printed p. 69): on a locally compact Hausdorff space `X` equipped with a
measure `μ` satisfying the explicit 2.14(a–d) regularity hypotheses (`Book214RegularityHypotheses μ`),
for `1 ≤ p < ∞`, `C_c(X)` embeds into `L^p(μ)` and is dense in `L^p(μ)`. -/
theorem theorem_3_14 {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] (μ : Measure X)
    (hreg : Book214RegularityHypotheses μ) {p : ℝ} (hp : 1 ≤ p) :
    (∀ g : C_c(X, ℂ), BookMemLpFinite μ p g) ∧
    (∀ f : X → ℂ, BookMemLpFinite μ p f → ∀ ε : ℝ, 0 < ε →
      ∃ g : C_c(X, ℂ),
        BookMemLpFinite μ p (f - g) ∧
        (bookELpNormFinite μ p (f - g)).toReal < ε) := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp
  have hp_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp_pos).ne'
  refine ⟨fun g => (theorem_3_14_cc_memLp hreg g).1 hp_pos, ?_⟩
  intro f hf ε hε
  obtain ⟨s, hs_class, hfs_mem, _, hfs_lt⟩ := (theorem_3_13 μ hp_pos).2 f hf (ε / 2) (half_pos hε)
  obtain ⟨g, hsg_lt⟩ := theorem_3_14_simple_approx hreg hp hs_class (half_pos hε)
  have hfs_corr : CorrectedBookMemLp μ (ENNReal.ofReal p) (f - s) := by
    obtain ⟨hm, hlp⟩ := (definition_3_6_memLp_iff μ hp_pos (f - s)).mp hfs_mem
    exact (correctedBookMemLp_iff_memLp μ _ _).mpr ⟨hp0, hm, hlp⟩
  have hsg_corr : CorrectedBookMemLp μ (ENNReal.ofReal p) (s - g) := by
    have h1 := (theorem_3_13_subset_lp μ hs_class).2 hp0
    have h2 := (remarks_3_10_smul μ (-1 : ℂ) ((theorem_3_14_cc_memLp hreg g).2 hp0)).1
    simpa [sub_eq_add_neg] using (theorem_3_9 μ hp_one h1 h2).1
  obtain ⟨hf_g_corr, _, htri⟩ := theorem_3_9 μ hp_one hfs_corr hsg_corr
  have hsplit : (f - s) + (s - (g : X → ℂ)) = f - (g : X → ℂ) := by abel
  rw [hsplit] at hf_g_corr htri
  obtain ⟨_, hfg_meas, hfg_lp⟩ := (correctedBookMemLp_iff_memLp μ _ _).mp hf_g_corr
  refine ⟨g, (definition_3_6_memLp_iff μ hp_pos _).mpr ⟨hfg_meas, hfg_lp⟩, ?_⟩
  have h1_eq : (correctedBookLpNorm μ (ENNReal.ofReal p) (f - s)).toReal =
      (bookELpNormFinite μ p (f - s)).toReal := by
    have hm := ((correctedBookMemLp_iff_memLp μ _ _).mp hfs_corr).2.1
    rw [correctedBookLpNorm_eq_eLpNorm μ hp0 hm, definition_3_6_eq_eLpNorm μ hp_pos hm]
  have h2_eq : (correctedBookLpNorm μ (ENNReal.ofReal p) (s - g)).toReal =
      (bookELpNormFinite μ p (s - g)).toReal := by
    have hm := ((correctedBookMemLp_iff_memLp μ _ _).mp hsg_corr).2.1
    rw [correctedBookLpNorm_eq_eLpNorm μ hp0 hm, definition_3_6_eq_eLpNorm μ hp_pos hm]
  have h3_eq : (bookELpNormFinite μ p (f - g)).toReal =
      (correctedBookLpNorm μ (ENNReal.ofReal p) (f - g)).toReal := by
    rw [definition_3_6_eq_eLpNorm μ hp_pos hfg_meas, correctedBookLpNorm_eq_eLpNorm μ hp0 hfg_meas]
  rw [h3_eq]
  linarith

/-- Specialization of Theorem 3.14 to Mathlib's `[BorelSpace X] [μ.Regular]` setting as
topological `Dense` in `Lp ℂ p μ` (`1 ≤ p < ∞`, without `NormalSpace X`). -/
theorem theorem_3_14_mathlib_regular_dense {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.Regular]
    (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (hp_top : p ≠ ∞) :
    Dense {F : Lp ℂ p μ | ∃ g : C_c(X, ℂ),
      ∃ hg : CorrectedBookMemLp μ p g, correctedBookToLp μ p hp.out ⟨g, hg⟩ = F} := by
  have hreg : Book214RegularityHypotheses μ := theorem_3_14_mathlib_regular_satisfies μ
  have hp_real : 1 ≤ p.toReal := by
    have h1 : (1 : ℝ) = (1 : ℝ≥0∞).toReal := by simp
    rw [h1]
    exact ENNReal.toReal_mono hp_top hp.out
  have hp_pos : 0 < p.toReal := zero_lt_one.trans_le hp_real
  have hp_eq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hp_top
  rw [Metric.dense_iff]
  intro F ε hε
  obtain ⟨⟨f, hf_book⟩, rfl⟩ := remarks_3_10_toLp_surjective μ p hp.out F
  obtain ⟨_, hf_meas, hf_mem⟩ := (correctedBookMemLp_iff_memLp μ p f).mp hf_book
  have hf_fin : BookMemLpFinite μ p.toReal f := by
    rw [definition_3_6_memLp_iff μ hp_pos, hp_eq]
    exact ⟨hf_meas, hf_mem⟩
  obtain ⟨g, _, hlt⟩ := (theorem_3_14 μ hreg hp_real).2 f hf_fin ε hε
  have hg_book : CorrectedBookMemLp μ p g :=
    (theorem_3_14_cc_memLp hreg g).2 (zero_lt_one.trans_le hp.out).ne'
  refine ⟨correctedBookToLp μ p hp.out ⟨g, hg_book⟩, ?_, ⟨g, hg_book, rfl⟩⟩
  rw [Metric.mem_ball, dist_comm, remarks_3_10_toLp_dist μ p ⟨f, hf_book⟩ ⟨g, hg_book⟩]
  unfold correctedBookLpDist
  have hg_meas : Measurable (g : X → ℂ) := g.continuous.borel_measurable.mono hreg.1 le_rfl
  rw [correctedBookLpNorm_eq_eLpNorm μ (zero_lt_one.trans_le hp.out).ne' (hf_meas.sub hg_meas),
    ← hp_eq, ← definition_3_6_eq_eLpNorm μ hp_pos (hf_meas.sub hg_meas)]
  exact hlt

/-- Canonical summary declaration for RCA Theorem 3.14 (printed p. 69), recording density under
both `Book214RegularityHypotheses μ` and its Section 1.36 completion `Chapter01.completedMeasure μ`. -/
theorem theorem3_14 {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] (μ : Measure X)
    (hreg : Book214RegularityHypotheses μ) {p : ℝ} (hp : 1 ≤ p) :
    ((∀ g : C_c(X, ℂ), BookMemLpFinite μ p g) ∧
      (∀ f : X → ℂ, BookMemLpFinite μ p f → ∀ ε : ℝ, 0 < ε →
        ∃ g : C_c(X, ℂ), BookMemLpFinite μ p (f - g) ∧
          (bookELpNormFinite μ p (f - g)).toReal < ε)) ∧
    @Book214RegularityHypotheses X _ (Chapter01.completionSigma μ)
      (Chapter01.completedMeasure μ) :=
  ⟨theorem_3_14 μ hreg hp, theorem_3_14_completedMeasure_preserves hreg⟩

/-! ## Section 3.17: $C_0(X)$ as the Uniform-Norm Completion of $C_c(X)$ (printed pp. 70–71) -/

/-- Boundedness and least-upper-bound characterization of the supremum norm on `C₀(X, ℂ)`
(printed p. 70): `‖f‖ = sup_{x ∈ X} |f(x)|`. -/
theorem theorem_3_17_sup_norm_characterization {X : Type*} [TopologicalSpace X]
    (f : C₀(X, ℂ)) :
    0 ≤ ‖f‖ ∧
    (∀ x : X, ‖f x‖ ≤ ‖f‖) ∧
    (∀ C : ℝ, 0 ≤ C → (∀ x : X, ‖f x‖ ≤ C) → ‖f‖ ≤ C) :=
  ⟨norm_nonneg f,
    fun x => BoundedContinuousFunction.norm_coe_le_norm (f := f.toBCF) x,
    fun _ hC hbound => (BoundedContinuousFunction.norm_le (f := f.toBCF) hC).mpr hbound⟩

/-- Injectivity of `ccToC0 : C_c(X, ℂ) → C₀(X, ℂ)`. -/
theorem ccToC0_injective {X : Type*} [TopologicalSpace X] :
    Function.Injective (ccToC0 : C_c(X, ℂ) → C₀(X, ℂ)) := by
  intro f g hfg
  ext x
  exact DFunLike.congr_fun hfg x

/-- Type wrapper equipping `C_c(X, ℂ)` with the uniform supremum metric
`d(f, g) = sup_{x ∈ X} ‖f x - g x‖ = ‖ccToC0 f - ccToC0 g‖` of RCA Theorem 3.17 (printed p. 70). -/
structure CcSupMetric (X : Type*) [TopologicalSpace X] where
  val : C_c(X, ℂ)

noncomputable instance {X : Type*} [TopologicalSpace X] : MetricSpace (CcSupMetric X) :=
  MetricSpace.induced (fun f : CcSupMetric X => ccToC0 f.val)
    (fun f g h => by cases f; cases g; congr; exact ccToC0_injective h)
    inferInstance

/-- Canonical isometric inclusion `CcSupMetric X → C₀(X, ℂ)`. -/
def ccSupMetricToC0 {X : Type*} [TopologicalSpace X] (f : CcSupMetric X) : C₀(X, ℂ) :=
  ccToC0 f.val

theorem ccSupMetricToC0_isometry {X : Type*} [TopologicalSpace X] :
    Isometry (ccSupMetricToC0 : CcSupMetric X → C₀(X, ℂ)) :=
  Isometry.of_dist_eq fun _ _ => rfl

/-- Core Urysohn cutoff approximation of RCA Theorem 3.17 (printed pp. 70–71):
on a locally compact Hausdorff space `X`, given `f ∈ C₀(X, ℂ)` and `ε > 0`, pick compact `K`
with `|f(x)| < ε / 2` outside `K`, construct a cutoff `K ≺ φ` via `Chapter02.lemma_2_12`, and
set `g = f • φ ∈ C_c(X, ℂ)`; then `‖f - ccToC0 g‖ < ε` and `∀ x, ‖f x - g x‖ < ε`. -/
theorem theorem_3_17_urysohn_approx {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (f : C₀(X, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C_c(X, ℂ),
      ‖f - ccToC0 g‖ < ε ∧ ∀ x : X, ‖f x - g x‖ < ε := by
  have hf_c0 : BookC0 (f : X → ℂ) := (definition_3_16_zeroAtInfty_iff _).mpr ⟨f, rfl⟩
  obtain ⟨K, hK, hK_small⟩ := hf_c0.2 (ε / 2) (half_pos hε)
  obtain ⟨φ, ⟨_, hφ_cut, hφ_K⟩, _⟩ :=
    Chapter02.lemma_2_12 hK isOpen_univ (Set.subset_univ K)
  let g : C_c(X, ℂ) := f • φ
  have hpt_le : ∀ x : X, ‖(f - ccToC0 g) x‖ ≤ ε / 2 := by
    intro x
    have happly : (f - ccToC0 g) x = f x * (1 - φ x) := by
      change f x - f x * φ x = f x * (1 - φ x)
      ring
    rw [happly, norm_mul]
    by_cases hxK : x ∈ K
    · have hφ1 : (φ x : ℂ) = 1 := hφ_K hxK
      rw [hφ1, sub_self, norm_zero, mul_zero]
      exact (half_pos hε).le
    · obtain ⟨r, ⟨hr0, hr1⟩, hφr⟩ := hφ_cut x
      have h1_sub : ‖(1 : ℂ) - φ x‖ ≤ 1 := by
        rw [hφr, ← Complex.ofReal_one, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        linarith
      calc
        ‖f x‖ * ‖(1 : ℂ) - φ x‖ ≤ (ε / 2) * 1 :=
          mul_le_mul (hK_small x hxK).le h1_sub (norm_nonneg _) (half_pos hε).le
        _ = ε / 2 := mul_one _
  have hnorm_le : ‖f - ccToC0 g‖ ≤ ε / 2 :=
    (theorem_3_17_sup_norm_characterization (f - ccToC0 g)).2.2 (ε / 2) (half_pos hε).le hpt_le
  have hnorm_lt : ‖f - ccToC0 g‖ < ε := by linarith
  refine ⟨g, hnorm_lt, fun x => ?_⟩
  exact (theorem_3_17_sup_norm_characterization (f - ccToC0 g)).2.1 x |>.trans_lt hnorm_lt

/-- Dense range of `ccToC0 : C_c(X, ℂ) → C₀(X, ℂ)` in the supremum norm on any locally compact
Hausdorff space `X`. -/
theorem theorem_3_17_denseRange {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] :
    DenseRange (ccToC0 : C_c(X, ℂ) → C₀(X, ℂ)) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  obtain ⟨g, hlt, _⟩ := theorem_3_17_urysohn_approx f hε
  refine ⟨g, ?_⟩
  rwa [dist_eq_norm]

/-- Function-level uniform-limit characterization of `BookC0` (printed pp. 70–71):
on a locally compact Hausdorff space `X`, `f ∈ C_0(X)` if and only if `f` is the uniform limit
of a sequence of functions in `C_c(X)`. -/
theorem theorem_3_17_uniform_closure_iff {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (f : X → ℂ) :
    BookC0 f ↔ ∃ g : ℕ → X → ℂ, (∀ n, Chapter02.BookCc (g n)) ∧ TendstoUniformly g f atTop := by
  constructor
  · intro hf
    obtain ⟨F, rfl⟩ := (definition_3_16_zeroAtInfty_iff f).mp hf
    have hex : ∀ n : ℕ, ∃ G : C_c(X, ℂ), ‖F - ccToC0 G‖ < 1 / ((n : ℝ) + 1) := fun n => by
      obtain ⟨G, hlt, _⟩ := theorem_3_17_urysohn_approx F (by positivity : 0 < 1 / ((n : ℝ) + 1))
      exact ⟨G, hlt⟩
    choose G hG using hex
    refine ⟨fun n x => G n x,
      fun n => (Chapter02.definition_2_9_cc _).mpr ⟨G n, rfl⟩, ?_⟩
    have hconv : Tendsto (fun n => ccToC0 (G n)) atTop (𝓝 F) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      refine ⟨N, fun n hn => ?_⟩
      rw [dist_comm, dist_eq_norm]
      refine (hG n).trans (lt_of_le_of_lt ?_ hN)
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    exact ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly.mp hconv
  · rintro ⟨g, hg_cc, hg_unif⟩
    have hf_cont : Continuous f :=
      hg_unif.continuous (Eventually.of_forall fun n => (hg_cc n).1).frequently
    refine ⟨hf_cont, fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (Metric.tendstoUniformly_iff.mp hg_unif (ε / 2) (half_pos hε))
    refine ⟨Chapter02.BookSupport (g N), (hg_cc N).2, fun x hx => ?_⟩
    have hg0 : g N x = 0 := image_eq_zero_of_notMem_tsupport hx
    have hdist : dist (f x) (g N x) < ε / 2 := hN N le_rfl x
    rw [hg0, dist_zero_right] at hdist
    linarith

/-- Explicit isometric bijection between the metric completion of `(C_c(X, ℂ), ‖·‖_∞)` and
`C₀(X, ℂ)` on a locally compact Hausdorff space `X` (RCA Theorem 3.17, printed pp. 70–71). -/
noncomputable def theorem_3_17_completionEquiv (X : Type*) [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] :
    UniformSpace.Completion (CcSupMetric X) ≃ᵢ C₀(X, ℂ) :=
  completionIsometryEquivOfDenseIsometry ccSupMetricToC0_isometry (by
    rw [Metric.denseRange_iff]
    intro f ε hε
    obtain ⟨g, hlt, _⟩ := theorem_3_17_urysohn_approx f hε
    refine ⟨⟨g⟩, ?_⟩
    simpa [ccSupMetricToC0, dist_eq_norm] using hlt)

/-- RCA Theorem 3.17 (printed pp. 70–71): if `X` is a locally compact Hausdorff space, then
`C₀(X, ℂ)` is complete in the supremum norm, `C_c(X, ℂ)` embeds isometrically with dense range
into `C₀(X, ℂ)`, `BookC0` equals the uniform-convergence closure of `BookCc`, and the metric
completion of `(C_c(X, ℂ), ‖·‖_∞)` is isometrically isomorphic to `C₀(X, ℂ)`. -/
theorem theorem_3_17 (X : Type*) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] :
    CompleteSpace C₀(X, ℂ) ∧
    Isometry (ccSupMetricToC0 : CcSupMetric X → C₀(X, ℂ)) ∧
    DenseRange (ccToC0 : C_c(X, ℂ) → C₀(X, ℂ)) ∧
    (∀ f : C₀(X, ℂ), ∀ ε : ℝ, 0 < ε → ∃ g : C_c(X, ℂ), ‖f - ccToC0 g‖ < ε) ∧
    (∀ f : X → ℂ, BookC0 f ↔
      ∃ g : ℕ → X → ℂ, (∀ n, Chapter02.BookCc (g n)) ∧ TendstoUniformly g f atTop) ∧
    Nonempty (UniformSpace.Completion (CcSupMetric X) ≃ᵢ C₀(X, ℂ)) :=
  ⟨inferInstance,
    ccSupMetricToC0_isometry,
    theorem_3_17_denseRange,
    fun f _ hε => let ⟨g, hlt, _⟩ := theorem_3_17_urysohn_approx f hε; ⟨g, hlt⟩,
    theorem_3_17_uniform_closure_iff,
    ⟨theorem_3_17_completionEquiv X⟩⟩

/-- Canonical summary declaration for RCA Theorem 3.17 (printed pp. 70–71). -/
theorem theorem3_17 (X : Type*) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] :
    CompleteSpace C₀(X, ℂ) ∧
    DenseRange (ccToC0 : C_c(X, ℂ) → C₀(X, ℂ)) ∧
    (∀ f : C₀(X, ℂ), ∀ ε : ℝ, 0 < ε → ∃ g : C_c(X, ℂ), ‖f - ccToC0 g‖ < ε) ∧
    (∀ f : X → ℂ, BookC0 f ↔
      ∃ g : ℕ → X → ℂ, (∀ n, Chapter02.BookCc (g n)) ∧ TendstoUniformly g f atTop) ∧
    Nonempty (UniformSpace.Completion (CcSupMetric X) ≃ᵢ C₀(X, ℂ)) := by
  obtain ⟨h1, _, h3, h4, h5, h6⟩ := theorem_3_17 X
  exact ⟨h1, h3, h4, h5, h6⟩

/-! ## Section 3.15: Remarks — Euclidean $L^p(\mathbb{R}^k)$ Completions (printed pp. 69–70) -/

/-- Euclidean `k`-space `ℝ^k` used in RCA Remarks 3.15. -/
abbrev EuclideanRk (k : ℕ) : Type := EuclideanSpace ℝ (Fin k)

/-- Every `f ∈ C_c(ℝ^k)` belongs to `CorrectedBookMemLp volume p` (`1 ≤ p ≤ ∞`). -/
theorem remarks_3_15_cc_memLp (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f : C_c(EuclideanRk k, ℂ)) :
    CorrectedBookMemLp (volume : Measure (EuclideanRk k)) p f :=
  (theorem_3_14_cc_memLp
    (theorem_3_14_mathlib_regular_satisfies (volume : Measure (EuclideanRk k))) f).2
    (zero_lt_one.trans_le hp).ne'

/-- Canonical `ℂ`-linear map `C_c(ℝ^k, ℂ) →ₗ[ℂ] Lp ℂ p (volume : Measure (ℝ^k))` (`1 ≤ p ≤ ∞`,
using `CorrectedBookMemLp` per the explicit Definition 3.7 repair). -/
noncomputable def ccToLpRk (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    C_c(EuclideanRk k, ℂ) →ₗ[ℂ] Lp ℂ p (volume : Measure (EuclideanRk k)) where
  toFun f := correctedBookToLp (volume : Measure (EuclideanRk k)) p hp
    ⟨f, remarks_3_15_cc_memLp k hp f⟩
  map_add' f g := by
    change correctedBookToLp _ p hp ⟨(f : EuclideanRk k → ℂ) + (g : EuclideanRk k → ℂ), _⟩ =
      correctedBookToLp _ p hp ⟨f, _⟩ + correctedBookToLp _ p hp ⟨g, _⟩
    exact (correctedBookToLp (volume : Measure (EuclideanRk k)) p hp).map_add ⟨f, _⟩ ⟨g, _⟩
  map_smul' c f := by
    change correctedBookToLp _ p hp ⟨c • (f : EuclideanRk k → ℂ), _⟩ =
      c • correctedBookToLp _ p hp ⟨f, _⟩
    exact (correctedBookToLp (volume : Measure (EuclideanRk k)) p hp).map_smul c ⟨f, _⟩

/-- RCA Remarks 3.15 nondegeneracy on continuous functions (printed p. 69): because every
nonempty open subset of `ℝ^k` has positive Lebesgue measure (`[IsOpenPosMeasure volume]`), two
continuous functions on `ℝ^k` agree Lebesgue-a.e. iff they are identically equal; hence
`ccToLpRk` is injective and `d_p(f, g) = ‖f - g‖_p` is a genuine metric on `C_c(ℝ^k, ℂ)` for
all `1 ≤ p ≤ ∞`. -/
theorem remarks_3_15_continuous_ae_eq_iff (k : ℕ) {f g : EuclideanRk k → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    (f =ᵐ[volume] g) ↔ f = g :=
  hf.ae_eq_iff_eq volume hg

theorem remarks_3_15_ccToLpRk_injective (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Function.Injective (ccToLpRk k p hp) := by
  intro f g hfg
  have hae : (f : EuclideanRk k → ℂ) =ᵐ[volume] (g : EuclideanRk k → ℂ) :=
    (remarks_3_10_toLp_eq_iff (volume : Measure (EuclideanRk k)) p hp
      ⟨f, remarks_3_15_cc_memLp k hp f⟩ ⟨g, remarks_3_15_cc_memLp k hp g⟩).mp hfg
  have heq : (f : EuclideanRk k → ℂ) = (g : EuclideanRk k → ℂ) :=
    (remarks_3_15_continuous_ae_eq_iff k f.continuous g.continuous).mp hae
  ext x
  exact congr_fun heq x

/-- Type wrapper equipping `C_c(ℝ^k, ℂ)` with the genuine `L^p`-metric
`d_p(f, g) = ‖ccToLpRk k p hp (f - g)‖` (`1 ≤ p ≤ ∞`, printed pp. 69–70). -/
structure CcLpMetric (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) where
  val : C_c(EuclideanRk k, ℂ)

noncomputable instance (k : ℕ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] :
    MetricSpace (CcLpMetric k p hp.out) :=
  MetricSpace.induced (fun f : CcLpMetric k p hp.out => ccToLpRk k p hp.out f.val)
    (fun f g h => by cases f; cases g; congr; exact remarks_3_15_ccToLpRk_injective k p hp.out h)
    inferInstance

/-- Isometric inclusion `(C_c(ℝ^k, ℂ), d_p) → Lp ℂ p (volume : Measure ℝ^k)`. -/
noncomputable def ccLpMetricToLp (k : ℕ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)]
    (f : CcLpMetric k p hp.out) : Lp ℂ p (volume : Measure (EuclideanRk k)) :=
  ccToLpRk k p hp.out f.val

theorem ccLpMetricToLp_isometry (k : ℕ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] :
    Isometry (ccLpMetricToLp k p : CcLpMetric k p hp.out → Lp ℂ p (volume : Measure (EuclideanRk k))) :=
  Isometry.of_dist_eq fun _ _ => rfl

/-- RCA Remarks 3.15 (`1 ≤ p < ∞`, printed pp. 69–70): by Theorems 3.11 and 3.14, `ccToLpRk`
has dense range in the complete space `Lp ℂ p (volume : Measure ℝ^k)`, so `L^p(ℝ^k)` is the
metric completion of `(C_c(ℝ^k, ℂ), d_p)`. -/
theorem remarks_3_15_denseRange_finite (k : ℕ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (hp_top : p ≠ ∞) :
    DenseRange (ccToLpRk k p hp.out) := by
  have hdense := theorem_3_14_mathlib_regular_dense
    (volume : Measure (EuclideanRk k)) p hp_top
  refine hdense.mono ?_
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, rfl⟩

noncomputable def remarks_3_15_completionEquiv_finite (k : ℕ) (p : ℝ≥0∞)
    [hp : Fact (1 ≤ p)] (hp_top : p ≠ ∞) :
    UniformSpace.Completion (CcLpMetric k p hp.out) ≃ᵢ
      Lp ℂ p (volume : Measure (EuclideanRk k)) :=
  completionIsometryEquivOfDenseIsometry (ccLpMetricToLp_isometry k p) (by
    rw [Metric.denseRange_iff]
    intro F ε hε
    obtain ⟨g, hg⟩ := Metric.denseRange_iff.mp (remarks_3_15_denseRange_finite k p hp_top) F ε hε
    exact ⟨⟨g⟩, hg⟩)

/-- RCA Remarks 3.15 (`p = ∞`, printed p. 70): on `C_c(ℝ^k, ℂ)`, the `L^∞(ℝ^k)` norm coincides
identically with the uniform supremum norm `‖ccToC0 f‖ = sup_{x ∈ ℝ^k} |f(x)|`. -/
theorem remarks_3_15_top_norm_eq_sup (k : ℕ) (f : C_c(EuclideanRk k, ℂ)) :
    ‖ccToLpRk k ∞ le_top f‖ = ‖ccToC0 f‖ := by
  have hf_book := remarks_3_15_cc_memLp k le_top f
  obtain ⟨_, hf_meas, hf_mem⟩ :=
    (correctedBookMemLp_iff_memLp (volume : Measure (EuclideanRk k)) ∞ f).mp hf_book
  change ‖hf_mem.toLp (f : EuclideanRk k → ℂ)‖ = ‖ccToC0 f‖
  rw [Lp.norm_toLp, eLpNorm_exponent_top hf_meas.aestronglyMeasurable]
  refine le_antisymm ?_ ?_
  · have hae : ∀ᵐ x ∂(volume : Measure (EuclideanRk k)),
        ‖f x‖ₑ ≤ ENNReal.ofReal ‖ccToC0 f‖ := by
      refine Eventually.of_forall fun x => ?_
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal
        ((theorem_3_17_sup_norm_characterization (ccToC0 f)).2.1 x)
    have hle : eLpNormEssSup (f : EuclideanRk k → ℂ) volume ≤ ENNReal.ofReal ‖ccToC0 f‖ := by
      rw [eLpNormEssSup_eq_essSup_enorm]
      exact essSup_le_of_ae_le _ hae
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at hreal
  · refine (theorem_3_17_sup_norm_characterization (ccToC0 f)).2.2 _ ENNReal.toReal_nonneg ?_
    intro x₀
    by_contra hlt
    replace hlt : (eLpNormEssSup (f : EuclideanRk k → ℂ) volume).toReal < ‖f x₀‖ :=
      not_le.mp hlt
    let M : ℝ := (eLpNormEssSup (f : EuclideanRk k → ℂ) volume).toReal
    have hM_nonneg : 0 ≤ M := ENNReal.toReal_nonneg
    have hU_open : IsOpen {x : EuclideanRk k | M < ‖f x‖} :=
      isOpen_lt continuous_const f.continuous.norm
    have hU_ne : ({x : EuclideanRk k | M < ‖f x‖}).Nonempty := ⟨x₀, hlt⟩
    have hμ_pos : 0 < (volume : Measure (EuclideanRk k)) {x : EuclideanRk k | M < ‖f x‖} :=
      hU_open.measure_pos volume hU_ne
    have hess_fin : eLpNormEssSup (f : EuclideanRk k → ℂ) volume ≠ ∞ := by
      rw [← eLpNorm_exponent_top hf_meas.aestronglyMeasurable]
      exact hf_mem.ne
    have hae_le : ∀ᵐ x ∂(volume : Measure (EuclideanRk k)), ‖f x‖ₑ ≤ ENNReal.ofReal M := by
      rw [ENNReal.ofReal_toReal hess_fin, eLpNormEssSup_eq_essSup_enorm]
      exact ENNReal.ae_le_essSup _
    have hzero : (volume : Measure (EuclideanRk k)) {x : EuclideanRk k | M < ‖f x‖} = 0 := by
      rw [← nonpos_iff_eq_zero]
      refine (measure_mono ?_).trans (le_of_eq (ae_iff.mp hae_le))
      intro x hx
      change ¬ ‖f x‖ₑ ≤ ENNReal.ofReal M
      rw [← ofReal_norm]
      exact not_le.mpr ((ENNReal.ofReal_lt_ofReal_iff (hM_nonneg.trans_lt hx)).mpr hx)
    exact hμ_pos.ne' hzero

/-- RCA Remarks 3.15 (`p = ∞`, printed p. 70): the metric completion of `(C_c(ℝ^k, ℂ), d_∞)` is
isometrically isomorphic to `C₀(ℝ^k, ℂ)` (via Theorem 3.17). -/
noncomputable def remarks_3_15_completionEquiv_top (k : ℕ) :
    UniformSpace.Completion (CcLpMetric k ∞ le_top) ≃ᵢ C₀(EuclideanRk k, ℂ) :=
  completionIsometryEquivOfDenseIsometry
    (ι := fun f : CcLpMetric k ∞ le_top => ccToC0 f.val)
    (Isometry.of_dist_eq fun f g => by
      change dist (ccToC0 f.val) (ccToC0 g.val) = dist (ccToLpRk k ∞ le_top f.val) (ccToLpRk k ∞ le_top g.val)
      have hlin_c0 : ccToC0 f.val - ccToC0 g.val = ccToC0 (f.val - g.val) := by
        ext x; rfl
      rw [dist_eq_norm, hlin_c0, dist_eq_norm, ← map_sub,
        remarks_3_15_top_norm_eq_sup k (f.val - g.val)])
    (by
      rw [Metric.denseRange_iff]
      intro f ε hε
      obtain ⟨g, hg⟩ := Metric.denseRange_iff.mp
        (theorem_3_17_denseRange (X := EuclideanRk k)) f ε hε
      exact ⟨⟨g⟩, hg⟩)

/-- RCA Remarks 3.15 contrast (`p = ∞`, `k ≥ 1`, printed p. 70): `C_c(ℝ^k, ℂ)` is NOT dense in
`L^∞(ℝ^k)` — in fact the unit-ball indicator `1_{B(0, 1)} ∈ L^∞(ℝ^k)` has `L^∞`-distance at
least `1 / 4` from every continuous function on `ℝ^k`. -/
theorem remarks_3_15_top_not_dense {k : ℕ} (hk : 1 ≤ k) :
    ¬ DenseRange (ccToLpRk k ∞ le_top) := by
  intro hdense
  let B : Set (EuclideanRk k) := Metric.ball (0 : EuclideanRk k) 1
  let χ : EuclideanRk k → ℂ := B.indicator 1
  have hχ_meas : Measurable χ := measurable_const.indicator Metric.isOpen_ball.measurableSet
  have hχ_mem : MemLp χ ∞ (volume : Measure (EuclideanRk k)) := by
    refine memLp_top_of_bound hχ_meas.aestronglyMeasurable 1 (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ B <;> simp [χ, hx]
  obtain ⟨g, hg_dist⟩ :=
    Metric.denseRange_iff.mp hdense (hχ_mem.toLp χ) (1 / 4) (by norm_num)
  have hg_mem := ((correctedBookMemLp_iff_memLp (volume : Measure (EuclideanRk k)) ∞ g).mp
    (remarks_3_15_cc_memLp k le_top g)).2.2
  have hdist_eq : dist (hχ_mem.toLp χ) (ccToLpRk k ∞ le_top g) =
      (eLpNorm (χ - (g : EuclideanRk k → ℂ)) ∞ volume).toReal := by
    change dist (hχ_mem.toLp χ) (hg_mem.toLp g) = _
    rw [Lp.dist_edist, Lp.edist_toLp_toLp]
  rw [hdist_eq] at hg_dist
  let i₀ : Fin k := ⟨0, hk⟩
  let e : EuclideanRk k := EuclideanSpace.single i₀ (1 : ℝ)
  have he_norm : ‖e‖ = 1 := by simp [e]
  obtain ⟨r, hr_pos, hr_ball⟩ :=
    Metric.continuousAt_iff.mp (g.continuous.continuousAt (x := e)) (1 / 4) (by norm_num)
  have hex_open : ∃ U : Set (EuclideanRk k), IsOpen U ∧ U.Nonempty ∧
      ∀ y ∈ U, (1 / 4 : ℝ) ≤ ‖(χ - (g : EuclideanRk k → ℂ)) y‖ := by
    by_cases hge : (1 / 2 : ℝ) ≤ ‖g e‖
    · let U : Set (EuclideanRk k) := Metric.ball e r ∩ (Metric.closedBall (0 : EuclideanRk k) 1)ᶜ
      have hU_open : IsOpen U := Metric.isOpen_ball.inter Metric.isClosed_closedBall.isOpen_compl
      let t : ℝ := r / 2
      have ht_pos : 0 < t := half_pos hr_pos
      let y₀ : EuclideanRk k := (1 + t) • e
      have hy₀_ball : y₀ ∈ Metric.ball e r := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : y₀ - e = t • e := by simp [y₀, add_smul]
        rw [hsub, norm_smul, he_norm, mul_one, Real.norm_eq_abs, abs_of_pos ht_pos]
        exact half_lt_self hr_pos
      have hy₀_out : y₀ ∉ Metric.closedBall (0 : EuclideanRk k) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, he_norm, mul_one,
          Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      refine ⟨U, hU_open, ⟨y₀, hy₀_ball, hy₀_out⟩, fun y ⟨hy_e, hy_out⟩ => ?_⟩
      have hy_notB : y ∉ B := fun hB => hy_out (Metric.ball_subset_closedBall hB)
      have hgy_close : ‖g y - g e‖ < 1 / 4 := by
        simpa [dist_eq_norm] using hr_ball hy_e
      have htri : ‖g e‖ ≤ ‖g y‖ + ‖g e - g y‖ := norm_le_insert' (g e) (g y)
      rw [norm_sub_rev (g e) (g y)] at htri
      have hgy_ge : (1 / 4 : ℝ) ≤ ‖g y‖ := by linarith
      simpa [χ, hy_notB] using hgy_ge
    · replace hge : ‖g e‖ < 1 / 2 := not_le.mp hge
      let U : Set (EuclideanRk k) := Metric.ball e r ∩ B
      have hU_open : IsOpen U := Metric.isOpen_ball.inter Metric.isOpen_ball
      let t : ℝ := min (r / 2) (1 / 2)
      have ht_pos : 0 < t := lt_min (half_pos hr_pos) (by norm_num)
      have ht_le_half : t ≤ 1 / 2 := min_le_right _ _
      have ht_lt_r : t < r := (min_le_left _ _).trans_lt (half_lt_self hr_pos)
      let y₀ : EuclideanRk k := (1 - t) • e
      have hy₀_ball : y₀ ∈ Metric.ball e r := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : y₀ - e = (-t) • e := by
          simp [y₀, sub_smul]
        rw [hsub, norm_smul, he_norm, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos ht_pos]
        exact ht_lt_r
      have hy₀_B : y₀ ∈ B := by
        rw [Metric.mem_ball, dist_zero_right, norm_smul, he_norm, mul_one,
          Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        linarith
      refine ⟨U, hU_open, ⟨y₀, hy₀_ball, hy₀_B⟩, fun y ⟨hy_e, hy_B⟩ => ?_⟩
      have hgy_close : ‖g y - g e‖ < 1 / 4 := by
        simpa [dist_eq_norm] using hr_ball hy_e
      have hgy_le : ‖g y‖ ≤ ‖g e‖ + ‖g y - g e‖ := norm_le_insert' (g y) (g e)
      have h1_le : ‖(1 : ℂ)‖ ≤ ‖(1 : ℂ) - g y‖ + ‖g y‖ := by
        have h := norm_add_le ((1 : ℂ) - g y) (g y)
        simpa using h
      rw [norm_one] at h1_le
      have hdiff_ge : (1 / 4 : ℝ) ≤ ‖(1 : ℂ) - g y‖ := by linarith
      simpa [χ, hy_B] using hdiff_ge
  obtain ⟨U, hU_open, hU_ne, hU_ge⟩ := hex_open
  have hμ_pos : 0 < (volume : Measure (EuclideanRk k)) U := hU_open.measure_pos volume hU_ne
  have hsub_fin : eLpNorm (χ - (g : EuclideanRk k → ℂ)) ∞ volume ≠ ∞ :=
    (hχ_mem.sub hg_mem).ne
  have hae : ∀ᵐ y ∂(volume : Measure (EuclideanRk k)),
      ‖(χ - (g : EuclideanRk k → ℂ)) y‖ₑ ≤ eLpNorm (χ - (g : EuclideanRk k → ℂ)) ∞ volume := by
    rw [eLpNorm_exponent_top (hχ_mem.sub hg_mem).aestronglyMeasurable,
      eLpNormEssSup_eq_essSup_enorm]
    exact ENNReal.ae_le_essSup _
  have hquarter_le : ENNReal.ofReal (1 / 4) ≤ eLpNorm (χ - (g : EuclideanRk k → ℂ)) ∞ volume := by
    by_contra hlt
    replace hlt := not_le.mp hlt
    have hzero : (volume : Measure (EuclideanRk k)) U = 0 := by
      rw [← nonpos_iff_eq_zero]
      refine (measure_mono ?_).trans (le_of_eq (ae_iff.mp hae))
      intro y hyU
      change ¬ ‖(χ - (g : EuclideanRk k → ℂ)) y‖ₑ ≤ eLpNorm (χ - (g : EuclideanRk k → ℂ)) ∞ volume
      refine not_le.mpr (hlt.trans_le ?_)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hU_ge y hyU)
    exact hμ_pos.ne' hzero
  have hreal_ge : (1 / 4 : ℝ) ≤ (eLpNorm (χ - (g : EuclideanRk k → ℂ)) ∞ volume).toReal := by
    have h := ENNReal.toReal_mono hsub_fin hquarter_le
    rwa [ENNReal.toReal_ofReal (by norm_num)] at h
  linarith

/-- Canonical summary declaration for RCA Remarks 3.15 (printed pp. 69–70). -/
theorem node3_15 (k : ℕ) :
    (∀ p : ℝ≥0∞, ∀ hp : 1 ≤ p, Function.Injective (ccToLpRk k p hp)) ∧
    (∀ p : ℝ≥0∞, [hp : Fact (1 ≤ p)] → p ≠ ∞ →
      DenseRange (ccToLpRk k p hp.out) ∧
      Nonempty (UniformSpace.Completion (CcLpMetric k p hp.out) ≃ᵢ
        Lp ℂ p (volume : Measure (EuclideanRk k)))) ∧
    (∀ f : C_c(EuclideanRk k, ℂ), ‖ccToLpRk k ∞ le_top f‖ = ‖ccToC0 f‖) ∧
    Nonempty (UniformSpace.Completion (CcLpMetric k ∞ le_top) ≃ᵢ C₀(EuclideanRk k, ℂ)) ∧
    (1 ≤ k → ¬ DenseRange (ccToLpRk k ∞ le_top)) :=
  ⟨fun p hp => remarks_3_15_ccToLpRk_injective k p hp,
    fun p _ hp_top =>
      ⟨remarks_3_15_denseRange_finite k p hp_top,
        ⟨remarks_3_15_completionEquiv_finite k p hp_top⟩⟩,
    remarks_3_15_top_norm_eq_sup k,
    ⟨remarks_3_15_completionEquiv_top k⟩,
    remarks_3_15_top_not_dense⟩

end RudinRCA.Chapter03
