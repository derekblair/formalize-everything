import RudinRCA.Chapter06
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.GroupTheory.Perm.Fin

/-!
# Chapter 7: Differentiation

Numbered declarations follow Walter Rudin, *Real and Complex Analysis*, third edition
(McGraw-Hill, 1987), Chapter 7 (printed pp. 135–156, nodes `7.1`–`7.26`).
Pinned Mathlib claims checks and printed subclause obligations are recorded in `SCOPING-C.md`.
-/

noncomputable section

open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter07

open RudinRCA.Chapter06

/-! ## §7.1–7.3: Symmetric derivatives, maximal functions, and the 3r covering lemma -/

section Node7_1

/-- Continuity from below for a complex measure along an increasing sequence of measurable sets. -/
private theorem complexMeasure_tendsto_iUnion {X : Type*} [MeasurableSpace X]
    (μ : ComplexMeasure X) {E : ℕ → Set X}
    (hmeas : ∀ n, MeasurableSet (E n)) (hmono : Monotone E) :
    Tendsto (fun n => μ (E n)) atTop (𝓝 (μ (⋃ k, E k))) := by
  have hU : MeasurableSet (⋃ k, E k) := MeasurableSet.iUnion hmeas
  let D : ℕ → Set X := fun n => (⋃ k, E k) \ E n
  have hDmeas : ∀ n, MeasurableSet (D n) := fun n => hU.diff (hmeas n)
  have hDanti : Antitone D := fun m n hmn x hx => ⟨hx.1, fun h => hx.2 (hmono hmn h)⟩
  have hDinter : (⋂ n, D n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp (mem_iInter.mp hx 0).1
    exact (mem_iInter.mp hx k).2 hk
  have hvar : Tendsto (fun n => μ.variation (D n)) atTop (𝓝 0) := by
    have h1 := tendsto_measure_iInter_atTop (μ := μ.variation)
      (fun n => (hDmeas n).nullMeasurableSet) hDanti ⟨0, measure_ne_top μ.variation (D 0)⟩
    simpa [hDinter, Function.comp_def] using h1
  have hvar_real : Tendsto (fun n => μ.variation.real (D n)) atTop (𝓝 0) := by
    simpa [measureReal_def, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hvar
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hvar_real
  have hsplit : E n ∪ D n = ⋃ k, E k :=
    Set.union_sdiff_cancel (subset_iUnion E n)
  have hdisj : Disjoint (E n) (D n) := disjoint_sdiff_self_right
  have hadd : μ (⋃ k, E k) = μ (E n) + μ (D n) := by
    rw [← hsplit, μ.of_union hdisj (hmeas n) (hDmeas n)]
  have hsub : μ (E n) - μ (⋃ k, E k) = -μ (D n) := by
    rw [hadd]
    abel
  rw [hsub, norm_neg]
  exact VectorMeasure.norm_measure_le_variation

/-- Continuity from above for a complex measure along a decreasing sequence of measurable sets. -/
private theorem complexMeasure_tendsto_iInter {X : Type*} [MeasurableSpace X]
    (μ : ComplexMeasure X) {E : ℕ → Set X}
    (hmeas : ∀ n, MeasurableSet (E n)) (hanti : Antitone E) :
    Tendsto (fun n => μ (E n)) atTop (𝓝 (μ (⋂ k, E k))) := by
  have hI : MeasurableSet (⋂ k, E k) := MeasurableSet.iInter hmeas
  let D : ℕ → Set X := fun n => E n \ ⋂ k, E k
  have hDmeas : ∀ n, MeasurableSet (D n) := fun n => (hmeas n).diff hI
  have hDanti : Antitone D := fun m n hmn x hx => ⟨hanti hmn hx.1, hx.2⟩
  have hDinter : (⋂ n, D n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (mem_iInter.mp hx 0).2 (mem_iInter.mpr fun k => (mem_iInter.mp hx k).1)
  have hvar : Tendsto (fun n => μ.variation (D n)) atTop (𝓝 0) := by
    have h1 := tendsto_measure_iInter_atTop (μ := μ.variation)
      (fun n => (hDmeas n).nullMeasurableSet) hDanti ⟨0, measure_ne_top μ.variation (D 0)⟩
    simpa [hDinter, Function.comp_def] using h1
  have hvar_real : Tendsto (fun n => μ.variation.real (D n)) atTop (𝓝 0) := by
    simpa [measureReal_def, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hvar
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hvar_real
  have hsplit : (⋂ k, E k) ∪ D n = E n :=
    Set.union_sdiff_cancel (iInter_subset E n)
  have hdisj : Disjoint (⋂ k, E k) (D n) := disjoint_sdiff_self_right
  have hadd : μ (E n) = μ (⋂ k, E k) + μ (D n) := by
    rw [← hsplit, μ.of_union hdisj hI (hDmeas n)]
  have hsub : μ (E n) - μ (⋂ k, E k) = μ (D n) := by
    rw [hadd]
    abel
  rw [hsub]
  exact VectorMeasure.norm_measure_le_variation

/-- 7.1: cumulative distribution function `f(x) = μ((-∞, x))` of a complex Borel measure on `ℝ`. -/
def complexMeasureCDF (μ : ComplexMeasure ℝ) (x : ℝ) : ℂ :=
  μ (Iio x)

/-- 7.1: an open segment (bounded nonempty open interval `(a, b)`) in `ℝ`. -/
def IsOpenSegment (I : Set ℝ) : Prop :=
  ∃ a b : ℝ, a < b ∧ I = Ioo a b

private theorem complexMeasureCDF_sub_of_le (μ : ComplexMeasure ℝ) {a b : ℝ} (hab : a ≤ b) :
    complexMeasureCDF μ b - complexMeasureCDF μ a = μ (Ico a b) := by
  have hsplit : Iio a ∪ Ico a b = Iio b := Iio_union_Ico_eq_Iio hab
  have hdisj : Disjoint (Iio a) (Ico a b) :=
    Set.disjoint_left.mpr fun _ hx1 hx2 => not_lt_of_ge hx2.1 hx1
  have hadd : μ (Iio b) = μ (Iio a) + μ (Ico a b) := by
    rw [← hsplit, μ.of_union hdisj measurableSet_Iio measurableSet_Ico]
  unfold complexMeasureCDF
  rw [hadd]
  abel

/-- 7.1 (explicit endpoint form): `f'(x) = A` for `f(x) = μ((-∞, x))` is equivalent to uniform
convergence of `μ((a, b)) / (b - a)` to `A` over all open intervals `(a, b)` containing `x`
of length `< δ`. -/
theorem theorem_7_1_Ioo (μ : ComplexMeasure ℝ) (x : ℝ) (A : ℂ) :
    HasDerivAt (complexMeasureCDF μ) A x ↔
      ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ a b : ℝ, a < x → x < b → b - a < δ →
        ‖μ (Ioo a b) / ((b - a : ℝ) : ℂ) - A‖ < ε := by
  constructor
  · intro hderiv ε hε
    have hε2 : 0 < ε / 2 := half_pos hε
    have h_littleo := hderiv.isLittleO.def hε2
    rw [Metric.eventually_nhds_iff] at h_littleo
    obtain ⟨δ, hδpos, hδ⟩ := h_littleo
    refine ⟨δ, hδpos, fun a b hax hxb hba => ?_⟩
    have hab : a < b := hax.trans hxb
    let t : ℕ → ℝ := fun n => a + (x - a) / ((n : ℝ) + 2)
    have ht_gt (n : ℕ) : a < t n := by
      have hpos : 0 < (x - a) / ((n : ℝ) + 2) := div_pos (sub_pos.mpr hax) (by positivity)
      linarith
    have ht_lt (n : ℕ) : t n < x := by
      have hdiv : (x - a) / ((n : ℝ) + 2) < x - a :=
        div_lt_self (sub_pos.mpr hax) (by linarith)
      linarith
    have ht_anti : Antitone t := by
      intro m n hmn
      dsimp [t]
      gcongr
    have ht_tendsto : Tendsto t atTop (𝓝 a) := by
      have h0 : Tendsto (fun n : ℕ => (x - a) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
      simpa using tendsto_const_nhds.add h0
    let E : ℕ → Set ℝ := fun n => Ico (t n) b
    have hEmono : Monotone E := fun m n hmn y hy => ⟨(ht_anti hmn).trans hy.1, hy.2⟩
    have hEunion : (⋃ n, E n) = Ioo a b := by
      ext y
      simp only [E, mem_iUnion, mem_Ico, mem_Ioo]
      constructor
      · rintro ⟨n, htn, hyb⟩
        exact ⟨(ht_gt n).trans_le htn, hyb⟩
      · rintro ⟨hay, hyb⟩
        have hev : ∀ᶠ n in atTop, t n < y := (tendsto_order.mp ht_tendsto).2 y hay
        obtain ⟨n, hn⟩ := hev.exists
        exact ⟨n, hn.le, hyb⟩
    have hμ_lim : Tendsto (fun n => μ (E n)) atTop (𝓝 (μ (Ioo a b))) := by
      rw [← hEunion]
      exact complexMeasure_tendsto_iUnion μ (fun _ => measurableSet_Ico) hEmono
    have hbound_n (n : ℕ) :
        ‖μ (E n) - ((b - t n : ℝ) : ℂ) * A‖ ≤ (ε / 2) * (b - t n) := by
      have hEn : μ (E n) = (complexMeasureCDF μ b - complexMeasureCDF μ x) +
          (complexMeasureCDF μ x - complexMeasureCDF μ (t n)) := by
        rw [complexMeasureCDF_sub_of_le μ hxb.le, complexMeasureCDF_sub_of_le μ (ht_lt n).le]
        have hsplit : Ico (t n) x ∪ Ico x b = Ico (t n) b :=
          Ico_union_Ico_eq_Ico (ht_lt n).le hxb.le
        have hdisj : Disjoint (Ico (t n) x) (Ico x b) :=
          Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h2.1 h1.2
        dsimp [E]
        rw [← hsplit, μ.of_union hdisj measurableSet_Ico measurableSet_Ico, add_comm]
      have hdist_b : dist b x < δ := by
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hxb)]
        linarith
      have hdist_t : dist (t n) x < δ := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.mpr (ht_lt n))]
        linarith [ht_gt n]
      have hb_est := hδ hdist_b
      have ht_est := hδ hdist_t
      simp only [Real.norm_eq_abs, Complex.real_smul] at hb_est ht_est
      rw [abs_of_pos (sub_pos.mpr hxb)] at hb_est
      have ht_est' :
          ‖complexMeasureCDF μ x - complexMeasureCDF μ (t n) - ((x - t n : ℝ) : ℂ) * A‖ ≤
            ε / 2 * (x - t n) := by
        have hrew :
            complexMeasureCDF μ x - complexMeasureCDF μ (t n) - ((x - t n : ℝ) : ℂ) * A =
              -(complexMeasureCDF μ (t n) - complexMeasureCDF μ x - ((t n - x : ℝ) : ℂ) * A) := by
          push_cast
          ring
        rw [hrew, norm_neg]
        simpa [abs_sub_comm, abs_of_pos (sub_pos.mpr (ht_lt n))] using ht_est
      have hcomb :
          μ (E n) - ((b - t n : ℝ) : ℂ) * A =
            (complexMeasureCDF μ b - complexMeasureCDF μ x - ((b - x : ℝ) : ℂ) * A) +
              (complexMeasureCDF μ x - complexMeasureCDF μ (t n) - ((x - t n : ℝ) : ℂ) * A) := by
        rw [hEn]
        push_cast
        ring
      rw [hcomb]
      calc
        ‖(complexMeasureCDF μ b - complexMeasureCDF μ x - ((b - x : ℝ) : ℂ) * A) +
            (complexMeasureCDF μ x - complexMeasureCDF μ (t n) - ((x - t n : ℝ) : ℂ) * A)‖
          ≤ ‖complexMeasureCDF μ b - complexMeasureCDF μ x - ((b - x : ℝ) : ℂ) * A‖ +
              ‖complexMeasureCDF μ x - complexMeasureCDF μ (t n) - ((x - t n : ℝ) : ℂ) * A‖ :=
            norm_add_le _ _
        _ ≤ ε / 2 * (b - x) + ε / 2 * (x - t n) := add_le_add hb_est ht_est'
        _ = ε / 2 * (b - t n) := by ring
    have hlhs : Tendsto (fun n => ‖μ (E n) - ((b - t n : ℝ) : ℂ) * A‖) atTop
        (𝓝 ‖μ (Ioo a b) - ((b - a : ℝ) : ℂ) * A‖) := by
      refine Continuous.tendsto continuous_norm _ |>.comp ?_
      refine hμ_lim.sub ?_
      have hsub_t : Tendsto (fun n => ((b - t n : ℝ) : ℂ)) atTop (𝓝 ((b - a : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.sub ht_tendsto)
      exact hsub_t.mul tendsto_const_nhds
    have hrhs : Tendsto (fun n => ε / 2 * (b - t n)) atTop (𝓝 (ε / 2 * (b - a))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.sub ht_tendsto)
    have hlim_le : ‖μ (Ioo a b) - ((b - a : ℝ) : ℂ) * A‖ ≤ ε / 2 * (b - a) :=
      le_of_tendsto_of_tendsto hlhs hrhs (Eventually.of_forall hbound_n)
    have hpos_ba : 0 < b - a := sub_pos.mpr hab
    have hba_ne : ((b - a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos_ba.ne'
    have hdiv_eq :
        μ (Ioo a b) / ((b - a : ℝ) : ℂ) - A =
          (μ (Ioo a b) - ((b - a : ℝ) : ℂ) * A) / ((b - a : ℝ) : ℂ) := by
      rw [sub_div, mul_div_cancel_left₀ A hba_ne]
    rw [hdiv_eq, norm_div, Complex.norm_real, Real.norm_of_nonneg hpos_ba.le]
    calc
      ‖μ (Ioo a b) - ((b - a : ℝ) : ℂ) * A‖ / (b - a)
        ≤ (ε / 2 * (b - a)) / (b - a) := by gcongr
      _ = ε / 2 := mul_div_cancel_right₀ (ε / 2) hpos_ba.ne'
      _ < ε := half_lt_self hε
  · intro hquot
    -- First show `μ {x} = 0`.
    have hsingleton : μ {x} = 0 := by
      obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hquot 1 zero_lt_one
      let r : ℕ → ℝ := fun n => min (δ₀ / 4) 1 / ((n : ℝ) + 1)
      have hr_pos (n : ℕ) : 0 < r n := div_pos (lt_min (by positivity) zero_lt_one) (by positivity)
      have hr_anti : Antitone r := fun m n hmn => by dsimp [r]; gcongr
      have hr_tendsto : Tendsto r atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
      let E : ℕ → Set ℝ := fun n => Ioo (x - r n) (x + r n)
      have hEanti : Antitone E := fun m n hmn y hy =>
        ⟨by linarith [hr_anti hmn, hy.1], by linarith [hr_anti hmn, hy.2]⟩
      have hEinter : (⋂ n, E n) = {x} := by
        ext y
        simp only [E, mem_iInter, mem_Ioo, mem_singleton_iff]
        constructor
        · intro hy
          by_contra hne
          have hdist : 0 < |y - x| := abs_pos.mpr (sub_ne_zero.mpr hne)
          obtain ⟨n, hn⟩ := ((tendsto_order.mp hr_tendsto).2 |y - x| hdist).exists
          have hy_n := hy n
          have habs : |y - x| < r n := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
          linarith
        · rintro rfl n
          exact ⟨by linarith [hr_pos n], by linarith [hr_pos n]⟩
      have hμE_tendsto : Tendsto (fun n => μ (E n)) atTop (𝓝 (μ {x})) := by
        rw [← hEinter]
        exact complexMeasure_tendsto_iInter μ (fun _ => measurableSet_Ioo) hEanti
      have hμE_zero : Tendsto (fun n => μ (E n)) atTop (𝓝 0) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
          ((tendsto_const_nhds (x := (‖A‖ + 1) * 2)).mul hr_tendsto |>.trans (by simp))
        simp only [sub_zero]
        have hlen : (x + r n) - (x - r n) = 2 * r n := by ring
        have h2r_lt : 2 * r n < δ₀ := by
          have hr_le : r n ≤ min (δ₀ / 4) 1 :=
            div_le_self (le_min (by positivity) zero_le_one) (by linarith)
          have hmin : min (δ₀ / 4) 1 ≤ δ₀ / 4 := min_le_left _ _
          linarith
        have hq := hδ₀ (x - r n) (x + r n) (by linarith [hr_pos n]) (by linarith [hr_pos n])
          (by linarith)
        rw [hlen] at hq
        have h2r_pos : 0 < 2 * r n := by linarith [hr_pos n]
        have hnorm_div : ‖μ (E n) / ((2 * r n : ℝ) : ℂ)‖ < ‖A‖ + 1 := by
          dsimp [E]
          calc
            ‖μ (Ioo (x - r n) (x + r n)) / ((2 * r n : ℝ) : ℂ)‖
              = ‖(μ (Ioo (x - r n) (x + r n)) / ((2 * r n : ℝ) : ℂ) - A) + A‖ := by ring_nf
            _ ≤ ‖μ (Ioo (x - r n) (x + r n)) / ((2 * r n : ℝ) : ℂ) - A‖ + ‖A‖ := norm_add_le _ _
            _ < 1 + ‖A‖ := by gcongr
            _ = ‖A‖ + 1 := add_comm _ _
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg h2r_pos.le,
          div_lt_iff₀ h2r_pos] at hnorm_div
        linarith
      exact tendsto_nhds_unique hμE_tendsto hμE_zero
    -- Now verify `HasDerivAt` via `Asymptotics.isLittleO_iff`.
    rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := hquot ε hε
    rw [Metric.eventually_nhds_iff]
    refine ⟨δ / 2, half_pos hδpos, fun y hy => ?_⟩
    simp only [Real.norm_eq_abs, Complex.real_smul]
    rcases lt_trichotomy y x with hyx | rfl | hxy
    · -- Left side: `y < x`. Approximate `[y, x]` from outside by `(y - η_n, x + η_n)`.
      have hxy_pos : 0 < x - y := sub_pos.mpr hyx
      have hxy_lt : x - y < δ / 2 := by
        simpa [Real.dist_eq, abs_of_neg (sub_neg.mpr hyx)] using hy
      let η : ℕ → ℝ := fun n => (δ / 4) / ((n : ℝ) + 2)
      have hη_pos (n : ℕ) : 0 < η n := div_pos (by positivity) (by positivity)
      have hη_anti : Antitone η := fun m n hmn => by dsimp [η]; gcongr
      have hη_tendsto : Tendsto η atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
      let E : ℕ → Set ℝ := fun n => Ioo (y - η n) (x + η n)
      have hEanti : Antitone E := fun m n hmn z hz =>
        ⟨by linarith [hη_anti hmn, hz.1], by linarith [hη_anti hmn, hz.2]⟩
      have hEinter : (⋂ n, E n) = Icc y x := by
        ext z
        simp only [E, mem_iInter, mem_Ioo, mem_Icc]
        constructor
        · intro hz
          constructor
          · by_contra hzy
            have hzy' : z < y := not_le.mp hzy
            obtain ⟨n, hn⟩ := ((tendsto_order.mp hη_tendsto).2 (y - z) (sub_pos.mpr hzy')).exists
            linarith [(hz n).1]
          · by_contra hzx
            have hzx' : x < z := not_le.mp hzx
            obtain ⟨n, hn⟩ := ((tendsto_order.mp hη_tendsto).2 (z - x) (sub_pos.mpr hzx')).exists
            linarith [(hz n).2]
        · rintro ⟨hyz, hzx⟩ n
          exact ⟨by linarith [hη_pos n], by linarith [hη_pos n]⟩
      have hμ_Icc : μ (Icc y x) = complexMeasureCDF μ x - complexMeasureCDF μ y := by
        rw [complexMeasureCDF_sub_of_le μ hyx.le]
        have hsplit : Ico y x ∪ {x} = Icc y x := Ico_union_right hyx.le
        have hdisj : Disjoint (Ico y x) {x} := by simp
        rw [← hsplit, μ.of_union hdisj measurableSet_Ico (measurableSet_singleton x),
          hsingleton, add_zero]
      have hμE_lim :
          Tendsto (fun n => μ (E n)) atTop (𝓝 (complexMeasureCDF μ x - complexMeasureCDF μ y)) := by
        rw [← hμ_Icc, ← hEinter]
        exact complexMeasure_tendsto_iInter μ (fun _ => measurableSet_Ioo) hEanti
      have hbound_n (n : ℕ) :
          ‖μ (E n) - ((x - y + 2 * η n : ℝ) : ℂ) * A‖ ≤ ε * (x - y + 2 * η n) := by
        have hlen : (x + η n) - (y - η n) = x - y + 2 * η n := by ring
        have h2η : 2 * η n ≤ δ / 2 := by
          dsimp [η]
          have hdiv : (δ / 4) / ((n : ℝ) + 2) ≤ δ / 4 :=
            div_le_self (by positivity) (by linarith)
          linarith
        have hq := hδ (y - η n) (x + η n) (by linarith [hη_pos n]) (by linarith [hη_pos n])
          (by linarith)
        rw [hlen] at hq
        have hpos_L : 0 < x - y + 2 * η n := by linarith [hη_pos n]
        have hne_L : ((x - y + 2 * η n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos_L.ne'
        have hrew :
            μ (E n) / ((x - y + 2 * η n : ℝ) : ℂ) - A =
              (μ (E n) - ((x - y + 2 * η n : ℝ) : ℂ) * A) / ((x - y + 2 * η n : ℝ) : ℂ) := by
          rw [sub_div, mul_div_cancel_left₀ A hne_L]
        rw [hrew, norm_div, Complex.norm_real, Real.norm_of_nonneg hpos_L.le,
          div_lt_iff₀ hpos_L] at hq
        exact hq.le
      have hlhs : Tendsto (fun n => ‖μ (E n) - ((x - y + 2 * η n : ℝ) : ℂ) * A‖) atTop
          (𝓝 ‖complexMeasureCDF μ x - complexMeasureCDF μ y - ((x - y : ℝ) : ℂ) * A‖) := by
        refine Continuous.tendsto continuous_norm _ |>.comp ?_
        refine hμE_lim.sub ?_
        have h1 : Tendsto (fun n => ((x - y + 2 * η n : ℝ) : ℂ)) atTop (𝓝 ((x - y : ℝ) : ℂ)) := by
          refine Complex.continuous_ofReal.continuousAt.tendsto.comp ?_
          simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hη_tendsto)
        exact h1.mul tendsto_const_nhds
      have hrhs : Tendsto (fun n => ε * (x - y + 2 * η n)) atTop (𝓝 (ε * (x - y))) := by
        simpa using tendsto_const_nhds.mul
          (tendsto_const_nhds.add (tendsto_const_nhds.mul hη_tendsto))
      have hlim_le := le_of_tendsto_of_tendsto hlhs hrhs (Eventually.of_forall hbound_n)
      have hneg :
          complexMeasureCDF μ y - complexMeasureCDF μ x - ((y - x : ℝ) : ℂ) * A =
            -(complexMeasureCDF μ x - complexMeasureCDF μ y - ((x - y : ℝ) : ℂ) * A) := by
        push_cast
        ring
      rw [hneg, norm_neg, abs_of_neg (sub_neg.mpr hyx)]
      simpa using hlim_le
    · -- `y = x`.
      simp
    · -- Right side: `x < y`. Approximate `[x, y)` from outside by `(x - η_n, y)`.
      have hyx_pos : 0 < y - x := sub_pos.mpr hxy
      have hyx_lt : y - x < δ / 2 := by
        simpa [Real.dist_eq, abs_of_pos hyx_pos] using hy
      let η : ℕ → ℝ := fun n => (δ / 2) / ((n : ℝ) + 2)
      have hη_pos (n : ℕ) : 0 < η n := div_pos (by positivity) (by positivity)
      have hη_anti : Antitone η := fun m n hmn => by dsimp [η]; gcongr
      have hη_tendsto : Tendsto η atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
      let E : ℕ → Set ℝ := fun n => Ioo (x - η n) y
      have hEanti : Antitone E := fun m n hmn z hz =>
        ⟨by linarith [hη_anti hmn, hz.1], hz.2⟩
      have hEinter : (⋂ n, E n) = Ico x y := by
        ext z
        simp only [E, mem_iInter, mem_Ioo, mem_Ico]
        constructor
        · intro hz
          refine ⟨?_, (hz 0).2⟩
          by_contra hzx
          have hzx' : z < x := not_le.mp hzx
          obtain ⟨n, hn⟩ := ((tendsto_order.mp hη_tendsto).2 (x - z) (sub_pos.mpr hzx')).exists
          linarith [(hz n).1]
        · rintro ⟨hxz, hzy⟩ n
          exact ⟨by linarith [hη_pos n], hzy⟩
      have hμE_lim :
          Tendsto (fun n => μ (E n)) atTop (𝓝 (complexMeasureCDF μ y - complexMeasureCDF μ x)) := by
        rw [complexMeasureCDF_sub_of_le μ hxy.le, ← hEinter]
        exact complexMeasure_tendsto_iInter μ (fun _ => measurableSet_Ioo) hEanti
      have hbound_n (n : ℕ) :
          ‖μ (E n) - ((y - x + η n : ℝ) : ℂ) * A‖ ≤ ε * (y - x + η n) := by
        have hlen : y - (x - η n) = y - x + η n := by ring
        have hη_lt : η n < δ / 2 :=
          div_lt_self (half_pos hδpos) (by linarith)
        have hq := hδ (x - η n) y (by linarith [hη_pos n]) hxy (by linarith)
        rw [hlen] at hq
        have hpos_L : 0 < y - x + η n := by linarith [hη_pos n]
        have hne_L : ((y - x + η n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos_L.ne'
        have hrew :
            μ (E n) / ((y - x + η n : ℝ) : ℂ) - A =
              (μ (E n) - ((y - x + η n : ℝ) : ℂ) * A) / ((y - x + η n : ℝ) : ℂ) := by
          rw [sub_div, mul_div_cancel_left₀ A hne_L]
        rw [hrew, norm_div, Complex.norm_real, Real.norm_of_nonneg hpos_L.le,
          div_lt_iff₀ hpos_L] at hq
        exact hq.le
      have hlhs : Tendsto (fun n => ‖μ (E n) - ((y - x + η n : ℝ) : ℂ) * A‖) atTop
          (𝓝 ‖complexMeasureCDF μ y - complexMeasureCDF μ x - ((y - x : ℝ) : ℂ) * A‖) := by
        refine Continuous.tendsto continuous_norm _ |>.comp ?_
        refine hμE_lim.sub ?_
        have h1 : Tendsto (fun n => ((y - x + η n : ℝ) : ℂ)) atTop (𝓝 ((y - x : ℝ) : ℂ)) := by
          refine Complex.continuous_ofReal.continuousAt.tendsto.comp ?_
          simpa using tendsto_const_nhds.add hη_tendsto
        exact h1.mul tendsto_const_nhds
      have hrhs : Tendsto (fun n => ε * (y - x + η n)) atTop (𝓝 (ε * (y - x))) := by
        simpa using tendsto_const_nhds.mul (tendsto_const_nhds.add hη_tendsto)
      have hlim_le := le_of_tendsto_of_tendsto hlhs hrhs (Eventually.of_forall hbound_n)
      rw [abs_of_pos hyx_pos]
      exact hlim_le

/-- 7.1: Rudin's printed equivalence over arbitrary open segments `I` containing `x`
with `m(I) < δ`. -/
theorem theorem_7_1 (μ : ComplexMeasure ℝ) (x : ℝ) (A : ℂ) :
    (DifferentiableAt ℝ (complexMeasureCDF μ) x ∧ deriv (complexMeasureCDF μ) x = A) ↔
      ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ I : Set ℝ, IsOpenSegment I → x ∈ I →
        volume.real I < δ → ‖μ I / (volume.real I : ℂ) - A‖ < ε := by
  have hhas : (DifferentiableAt ℝ (complexMeasureCDF μ) x ∧ deriv (complexMeasureCDF μ) x = A) ↔
      HasDerivAt (complexMeasureCDF μ) A x := by
    constructor
    · rintro ⟨hd, rfl⟩
      exact hd.hasDerivAt
    · intro h
      exact ⟨h.differentiableAt, h.deriv⟩
  rw [hhas, theorem_7_1_Ioo]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδpos, hδ⟩ := h ε hε
    refine ⟨δ, hδpos, ?_⟩
    rintro I ⟨a, b, hab, rfl⟩ hx hlen
    have hvol : volume.real (Ioo a b) = b - a := by
      rw [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_pos.mpr hab).le]
    rw [hvol] at hlen ⊢
    exact hδ a b hx.1 hx.2 hlen
  · intro h ε hε
    obtain ⟨δ, hδpos, hδ⟩ := h ε hε
    refine ⟨δ, hδpos, fun a b hax hxb hba => ?_⟩
    have hab : a < b := hax.trans hxb
    have hvol : volume.real (Ioo a b) = b - a := by
      rw [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_pos.mpr hab).le]
    have hlen : volume.real (Ioo a b) < δ := by rwa [hvol]
    have hq := hδ (Ioo a b) ⟨a, b, hab, rfl⟩ ⟨hax, hxb⟩ hlen
    rwa [hvol] at hq

end Node7_1

section Node7_2

/-- 7.2: open-ball quotient `Q_r μ(x) = μ(B(x, r)) / m(B(x, r))` for a positive Borel measure
on `ℝ^k`, valued in `[0, ∞]`. -/
def ballQuotientPos {k : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin k))) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin k)) : ℝ≥0∞ :=
  μ (Metric.ball x r) / volume (Metric.ball x r)

/-- 7.2: open-ball quotient `Q_r μ(x) = μ(B(x, r)) / m(B(x, r))` for a complex Borel measure
on `ℝ^k`. -/
def ballQuotient {k : ℕ} (μ : ComplexMeasure (EuclideanSpace ℝ (Fin k))) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin k)) : ℂ :=
  μ (Metric.ball x r) / (volume.real (Metric.ball x r) : ℂ)

/-- 7.2: existence of the symmetric derivative `Dμ(x) = lim_{r → 0⁺} Q_r μ(x)` for a positive
Borel measure (allowing `+∞`). -/
def HasSymmetricDerivPos {k : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin k)))
    (x : EuclideanSpace ℝ (Fin k)) (L : ℝ≥0∞) : Prop :=
  Tendsto (fun r => ballQuotientPos μ r x) (𝓝[>] 0) (𝓝 L)

/-- 7.2: symmetric derivative `Dμ(x)` of a positive Borel measure where the limit exists. -/
def symmetricDerivPos {k : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin k)))
    (x : EuclideanSpace ℝ (Fin k)) : ℝ≥0∞ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun r => ballQuotientPos μ r x)

theorem HasSymmetricDerivPos.symmetricDerivPos_eq {k : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin k))} {x : EuclideanSpace ℝ (Fin k)} {L : ℝ≥0∞}
    (h : HasSymmetricDerivPos μ x L) : symmetricDerivPos μ x = L :=
  h.limUnder_eq

/-- 7.2: existence of the symmetric derivative `Dμ(x) = lim_{r → 0⁺} Q_r μ(x)` for a complex
Borel measure. -/
def HasSymmetricDeriv {k : ℕ} (μ : ComplexMeasure (EuclideanSpace ℝ (Fin k)))
    (x : EuclideanSpace ℝ (Fin k)) (A : ℂ) : Prop :=
  Tendsto (fun r => ballQuotient μ r x) (𝓝[>] 0) (𝓝 A)

/-- 7.2: symmetric derivative `Dμ(x)` of a complex Borel measure where the limit exists. -/
def symmetricDeriv {k : ℕ} (μ : ComplexMeasure (EuclideanSpace ℝ (Fin k)))
    (x : EuclideanSpace ℝ (Fin k)) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun r => ballQuotient μ r x)

theorem HasSymmetricDeriv.symmetricDeriv_eq {k : ℕ}
    {μ : ComplexMeasure (EuclideanSpace ℝ (Fin k))} {x : EuclideanSpace ℝ (Fin k)} {A : ℂ}
    (h : HasSymmetricDeriv μ x A) : symmetricDeriv μ x = A :=
  h.limUnder_eq

/-- 7.2 (1D link to 7.1): on `ℝ`, differentiability of `f(x) = μ((-∞, x))` implies convergence
of centered open-ball quotients `μ(B(x, r)) / m(B(x, r)) → A` as `r → 0⁺`. -/
theorem hasDerivAt_complexMeasureCDF_imp_ball_tendsto
    (μ : ComplexMeasure ℝ) (x : ℝ) (A : ℂ)
    (h : HasDerivAt (complexMeasureCDF μ) A x) :
    Tendsto (fun r : ℝ => μ (Metric.ball x r) / (volume.real (Metric.ball x r) : ℂ))
      (𝓝[>] 0) (𝓝 A) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := (theorem_7_1_Ioo μ x A).mp h ε hε
  filter_upwards [Ioo_mem_nhdsGT (half_pos hδpos)] with r hr
  have hball : Metric.ball x r = Ioo (x - r) (x + r) := Real.ball_eq_Ioo x r
  have hvol : volume.real (Ioo (x - r) (x + r)) = (x + r) - (x - r) := by
    have hab : x - r < x + r := by linarith [hr.1]
    rw [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_pos.mpr hab).le]
  rw [dist_eq_norm, hball, hvol]
  exact hδ (x - r) (x + r) (by linarith [hr.1]) (by linarith [hr.1]) (by linarith [hr.2])

/-- 7.2: maximal function `Mμ(x) = sup_{r > 0} Q_r μ(x)` of a positive Borel measure on `ℝ^k`. -/
def maximalFunctionPos {k : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin k)))
    (x : EuclideanSpace ℝ (Fin k)) : ℝ≥0∞ :=
  ⨆ r : ℝ, ⨆ (_ : 0 < r), ballQuotientPos μ r x

/-- 7.2: maximal function `Mμ = M|μ|` of a complex Borel measure on `ℝ^k`. -/
def maximalFunctionComplex {k : ℕ} (μ : ComplexMeasure (EuclideanSpace ℝ (Fin k)))
    (x : EuclideanSpace ℝ (Fin k)) : ℝ≥0∞ :=
  maximalFunctionPos μ.variation x

theorem maximalFunctionComplex_eq_variation {k : ℕ}
    (μ : ComplexMeasure (EuclideanSpace ℝ (Fin k))) :
    maximalFunctionComplex μ = maximalFunctionPos μ.variation := rfl

/-- For fixed `r > 0`, `x ↦ μ(B(x, r))` is lower semicontinuous for any positive Borel measure `μ`
(no finiteness or regularity hypotheses needed). -/
theorem lowerSemicontinuous_measure_ball {k : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin k))) {r : ℝ} (hr : 0 < r) :
    LowerSemicontinuous (fun x => μ (Metric.ball x r)) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro t
  rw [Metric.isOpen_iff]
  intro x hx
  simp only [mem_preimage, mem_Ioi] at hx
  let δ : ℕ → ℝ := fun n => r / ((n : ℝ) + 2)
  have hδ_pos (n : ℕ) : 0 < δ n := div_pos hr (by positivity)
  have hδ_anti : Antitone δ := fun m n hmn => by dsimp [δ]; gcongr
  have hδ_tendsto : Tendsto δ atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
  let B : ℕ → Set (EuclideanSpace ℝ (Fin k)) := fun n => Metric.ball x (r - δ n)
  have hB_mono : Monotone B := fun m n hmn =>
    Metric.ball_subset_ball (by linarith [hδ_anti hmn])
  have hB_union : (⋃ n, B n) = Metric.ball x r := by
    ext z
    simp only [B, mem_iUnion, Metric.mem_ball]
    constructor
    · rintro ⟨n, hz⟩
      linarith [hδ_pos n]
    · intro hz
      obtain ⟨n, hn⟩ := ((tendsto_order.mp hδ_tendsto).2 (r - dist z x) (sub_pos.mpr hz)).exists
      exact ⟨n, by linarith⟩
  have hsup : μ (Metric.ball x r) = ⨆ n, μ (B n) := by
    rw [← hB_union, hB_mono.measure_iUnion]
  rw [hsup, lt_iSup_iff] at hx
  obtain ⟨n, hn⟩ := hx
  refine ⟨δ n, hδ_pos n, fun y hy => ?_⟩
  simp only [mem_preimage, mem_Ioi]
  refine hn.trans_le (measure_mono ?_)
  intro z hz
  simp only [B, Metric.mem_ball] at hz hy ⊢
  calc
    dist z y ≤ dist z x + dist x y := dist_triangle z x y
    _ = dist z x + dist y x := by rw [dist_comm x y]
    _ < (r - δ n) + δ n := add_lt_add hz hy
    _ = r := sub_add_cancel r (δ n)

/-- 7.2: for each `r > 0`, `Q_r μ` is lower semicontinuous. -/
theorem lowerSemicontinuous_ballQuotientPos {k : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin k))) {r : ℝ} (hr : 0 < r) :
    LowerSemicontinuous (ballQuotientPos μ r) := by
  have hvol_eq : ∀ x : EuclideanSpace ℝ (Fin k),
      volume (Metric.ball x r) = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) r) :=
    fun x => Measure.addHaar_ball_center volume x r
  have hRewrite : ballQuotientPos μ r =
      fun x => (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) r))⁻¹ * μ (Metric.ball x r) := by
    ext x
    simp [ballQuotientPos, hvol_eq x, div_eq_mul_inv, mul_comm]
  rw [hRewrite]
  have hne_zero : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) r))⁻¹ ≠ ∞ := by
    simp [(measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin k)) hr).ne']
  exact (ENNReal.continuous_const_mul hne_zero).comp_lowerSemicontinuous
    (lowerSemicontinuous_measure_ball μ hr)
    (fun _ _ hle => mul_le_mul_of_nonneg_left hle bot_le)

/-- 7.2: maximal functions of positive Borel measures are lower semicontinuous. -/
theorem lowerSemicontinuous_maximalFunctionPos {k : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin k))) :
    LowerSemicontinuous (maximalFunctionPos μ) := by
  unfold maximalFunctionPos
  refine lowerSemicontinuous_iSup fun r => ?_
  by_cases hr : 0 < r
  · simpa [ciSup_pos hr] using lowerSemicontinuous_ballQuotientPos μ hr
  · simpa [hr] using lowerSemicontinuous_const

/-- 7.2: superlevel sets `{x : Mμ(x) > λ}` are open, and `Mμ` is Borel measurable. -/
theorem isOpen_maximalFunctionPos_gt {k : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin k))) (t : ℝ≥0∞) :
    IsOpen {x | t < maximalFunctionPos μ x} :=
  (lowerSemicontinuous_maximalFunctionPos μ).isOpen_preimage t

theorem measurable_maximalFunctionPos {k : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin k))) :
    Measurable (maximalFunctionPos μ) :=
  (lowerSemicontinuous_maximalFunctionPos μ).measurable

/-- 7.2: maximal functions of complex Borel measures are lower semicontinuous and measurable. -/
theorem lowerSemicontinuous_maximalFunctionComplex {k : ℕ}
    (μ : ComplexMeasure (EuclideanSpace ℝ (Fin k))) :
    LowerSemicontinuous (maximalFunctionComplex μ) :=
  lowerSemicontinuous_maximalFunctionPos μ.variation

theorem isOpen_maximalFunctionComplex_gt {k : ℕ}
    (μ : ComplexMeasure (EuclideanSpace ℝ (Fin k))) (t : ℝ≥0∞) :
    IsOpen {x | t < maximalFunctionComplex μ x} :=
  isOpen_maximalFunctionPos_gt μ.variation t

theorem measurable_maximalFunctionComplex {k : ℕ}
    (μ : ComplexMeasure (EuclideanSpace ℝ (Fin k))) :
    Measurable (maximalFunctionComplex μ) :=
  measurable_maximalFunctionPos μ.variation

end Node7_2

section Node7_3

private theorem volume_ball_three_mul {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) (r : ℝ) :
    volume (Metric.ball x (3 * r)) = (3 : ℝ≥0∞) ^ k * volume (Metric.ball x r) := by
  rw [volume.addHaar_ball_mul_of_pos x (by norm_num : (0 : ℝ) < 3) r,
    volume.addHaar_ball_center x r, finrank_euclideanSpace_fin]
  norm_num

/-- 7.3: Rudin's finite covering lemma on `ℝ^k` with exact dilation `3` and constant `3^k`. -/
theorem lemma_7_3 {k : ℕ} {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (c : ι → EuclideanSpace ℝ (Fin k)) (r : ι → ℝ) (hr : ∀ i ∈ I, 0 < r i) :
    ∃ S : Finset ι,
      S ⊆ I ∧
      (S : Set ι).PairwiseDisjoint (fun i => Metric.ball (c i) (r i)) ∧
      (⋃ i ∈ I, Metric.ball (c i) (r i)) ⊆ (⋃ i ∈ S, Metric.ball (c i) (3 * r i)) ∧
      volume (⋃ i ∈ I, Metric.ball (c i) (r i)) ≤
        (3 : ℝ≥0∞) ^ k * ∑ i ∈ S, volume (Metric.ball (c i) (r i)) := by
  classical
  suffices hcore :
      ∀ J : Finset ι, (∀ i ∈ J, 0 < r i) →
        ∃ S : Finset ι,
          S ⊆ J ∧
          (S : Set ι).PairwiseDisjoint (fun i => Metric.ball (c i) (r i)) ∧
          (⋃ i ∈ J, Metric.ball (c i) (r i)) ⊆ (⋃ i ∈ S, Metric.ball (c i) (3 * r i)) by
    obtain ⟨S, hSI, hdisj, hcov⟩ := hcore I hr
    refine ⟨S, hSI, hdisj, hcov, ?_⟩
    calc
      volume (⋃ i ∈ I, Metric.ball (c i) (r i))
        ≤ volume (⋃ i ∈ S, Metric.ball (c i) (3 * r i)) := measure_mono hcov
      _ ≤ ∑ i ∈ S, volume (Metric.ball (c i) (3 * r i)) := measure_biUnion_finset_le S _
      _ = ∑ i ∈ S, (3 : ℝ≥0∞) ^ k * volume (Metric.ball (c i) (r i)) := by
          refine Finset.sum_congr rfl fun i _ => volume_ball_three_mul (c i) (r i)
      _ = (3 : ℝ≥0∞) ^ k * ∑ i ∈ S, volume (Metric.ball (c i) (r i)) := by
          rw [Finset.mul_sum]
  intro J
  induction J using Finset.strongInduction with
  | H J ih =>
    intro hrJ
    rcases J.eq_empty_or_nonempty with rfl | hJne
    · exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
    · obtain ⟨i₀, hi₀J, hmax⟩ := J.exists_max_image r hJne
      let J' : Finset ι :=
        J.filter fun j => Disjoint (Metric.ball (c i₀) (r i₀)) (Metric.ball (c j) (r j))
      have hi₀_not_J' : i₀ ∉ J' := by
        simp only [J', Finset.mem_filter, not_and]
        intro _ hdisj
        exact Set.disjoint_left.mp hdisj
          (Metric.mem_ball_self (hrJ i₀ hi₀J)) (Metric.mem_ball_self (hrJ i₀ hi₀J))
      have hJ'_ssub : J' ⊂ J :=
        Finset.ssubset_iff_of_subset (Finset.filter_subset _ J) |>.mpr ⟨i₀, hi₀J, hi₀_not_J'⟩
      have hrJ' : ∀ j ∈ J', 0 < r j := fun j hj => hrJ j (Finset.filter_subset _ J hj)
      obtain ⟨S', hS'J', hS'disj, hS'cov⟩ := ih J' hJ'_ssub hrJ'
      refine ⟨insert i₀ S', ?_, ?_, ?_⟩
      · exact Finset.insert_subset hi₀J (hS'J'.trans (Finset.filter_subset _ J))
      · rw [Finset.coe_insert]
        refine hS'disj.insert fun j hj _ => ?_
        exact (Finset.mem_filter.mp (hS'J' hj)).2
      · intro y hy
        simp only [mem_iUnion, exists_prop] at hy ⊢
        obtain ⟨j, hjJ, hyj⟩ := hy
        by_cases hjJ' : j ∈ J'
        · have hy' : y ∈ ⋃ s ∈ S', Metric.ball (c s) (3 * r s) :=
            hS'cov (mem_iUnion₂.mpr ⟨j, hjJ', hyj⟩)
          simp only [mem_iUnion, exists_prop] at hy'
          obtain ⟨s, hsS', hys⟩ := hy'
          exact ⟨s, Finset.mem_insert_of_mem hsS', hys⟩
        · have hnotdisj : ¬ Disjoint (Metric.ball (c i₀) (r i₀)) (Metric.ball (c j) (r j)) := by
            intro hd
            exact hjJ' (Finset.mem_filter.mpr ⟨hjJ, hd⟩)
          obtain ⟨z, hzi₀, hzj⟩ := Set.not_disjoint_iff.mp hnotdisj
          refine ⟨i₀, Finset.mem_insert_self i₀ S', ?_⟩
          simp only [Metric.mem_ball] at hyj hzi₀ hzj ⊢
          have hr_le : r j ≤ r i₀ := hmax j hjJ
          have htri1 : dist y (c i₀) ≤ dist y z + dist z (c i₀) := dist_triangle y z (c i₀)
          have htri2 : dist y z ≤ dist y (c j) + dist (c j) z := dist_triangle y (c j) z
          have hsym : dist (c j) z = dist z (c j) := dist_comm (c j) z
          linarith

end Node7_3

/-! ## §7.4–7.5: The maximal theorem and weak L¹ -/

section Node7_4

/-- 7.4 (positive Borel measure form): for any positive Borel measure `μ` on `ℝ^k` and any
threshold `t : ℝ≥0∞`, `t * m{x : Mμ(x) > t} ≤ 3^k * μ(ℝ^k)`, proved from Lemma 7.3 and
compact inner regularity of Lebesgue measure on open sets. -/
theorem theorem_7_4_pos_mul {k : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin k))) (t : ℝ≥0∞) :
    t * volume {x | t < maximalFunctionPos μ x} ≤ (3 : ℝ≥0∞) ^ k * μ univ := by
  classical
  rcases eq_or_ne t 0 with rfl | ht0
  · simp
  rcases eq_or_ne t ∞ with rfl | httop
  · simp
  let U : Set (EuclideanSpace ℝ (Fin k)) := {x | t < maximalFunctionPos μ x}
  have hUopen : IsOpen U := isOpen_maximalFunctionPos_gt μ t
  have hcompact_bound :
      ∀ K : Set (EuclideanSpace ℝ (Fin k)), K ⊆ U → IsCompact K →
        t * volume K ≤ (3 : ℝ≥0∞) ^ k * μ univ := by
    intro K hKU hK
    have hwit : ∀ x : K, ∃ r : ℝ, 0 < r ∧
        t * volume (Metric.ball (x : EuclideanSpace ℝ (Fin k)) r) ≤
          μ (Metric.ball (x : EuclideanSpace ℝ (Fin k)) r) := by
      intro x
      have hxU : (x : EuclideanSpace ℝ (Fin k)) ∈ U := hKU x.property
      simp only [U, mem_ofPred_eq, maximalFunctionPos, lt_iSup_iff] at hxU
      obtain ⟨r, hrpos, hrq⟩ := hxU
      have hv0 : volume (Metric.ball (x : EuclideanSpace ℝ (Fin k)) r) ≠ 0 :=
        (measure_ball_pos volume (x : EuclideanSpace ℝ (Fin k)) hrpos).ne'
      have hvtop : volume (Metric.ball (x : EuclideanSpace ℝ (Fin k)) r) ≠ ∞ :=
        measure_ball_ne_top
      refine ⟨r, hrpos, ?_⟩
      exact ((ENNReal.lt_div_iff_mul_lt (Or.inl hv0) (Or.inl hvtop)).mp hrq).le
    choose r hrpos hrint using hwit
    have hKcov : K ⊆ ⋃ x : K, Metric.ball (x : EuclideanSpace ℝ (Fin k)) (r x) := by
      intro y hy
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (hrpos ⟨y, hy⟩)⟩
    obtain ⟨I, hIcov⟩ := hK.elim_finite_subcover
      (fun x : K => Metric.ball (x : EuclideanSpace ℝ (Fin k)) (r x))
      (fun _ => Metric.isOpen_ball) hKcov
    obtain ⟨S, _, hSdisj, _, hSvol⟩ :=
      lemma_7_3 I (fun x : K => (x : EuclideanSpace ℝ (Fin k))) r (fun x _ => hrpos x)
    have hdisj_sum :
        (∑ x ∈ S, μ (Metric.ball (x : EuclideanSpace ℝ (Fin k)) (r x))) =
          μ (⋃ x ∈ S, Metric.ball (x : EuclideanSpace ℝ (Fin k)) (r x)) := by
      exact (measure_biUnion_finset hSdisj (fun _ _ => measurableSet_ball)).symm
    calc
      t * volume K
        ≤ t * volume (⋃ x ∈ I, Metric.ball (x : EuclideanSpace ℝ (Fin k)) (r x)) :=
          mul_le_mul_of_nonneg_left (measure_mono hIcov) bot_le
      _ ≤ t * ((3 : ℝ≥0∞) ^ k * ∑ x ∈ S, volume (Metric.ball (x : EuclideanSpace ℝ (Fin k)) (r x))) :=
          mul_le_mul_of_nonneg_left hSvol bot_le
      _ = (3 : ℝ≥0∞) ^ k * ∑ x ∈ S, t * volume (Metric.ball (x : EuclideanSpace ℝ (Fin k)) (r x)) := by
          rw [← mul_assoc, mul_comm t ((3 : ℝ≥0∞) ^ k), mul_assoc, Finset.mul_sum]
      _ ≤ (3 : ℝ≥0∞) ^ k * ∑ x ∈ S, μ (Metric.ball (x : EuclideanSpace ℝ (Fin k)) (r x)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hrint x) bot_le
      _ = (3 : ℝ≥0∞) ^ k * μ (⋃ x ∈ S, Metric.ball (x : EuclideanSpace ℝ (Fin k)) (r x)) := by
          rw [hdisj_sum]
      _ ≤ (3 : ℝ≥0∞) ^ k * μ univ :=
          mul_le_mul_of_nonneg_left (measure_mono (subset_univ _)) bot_le
  have hU_eq : volume U = ⨆ (K : Set (EuclideanSpace ℝ (Fin k))) (_ : K ⊆ U) (_ : IsCompact K),
      volume K := hUopen.measure_eq_iSup_isCompact volume
  change t * volume U ≤ _
  rw [hU_eq, ENNReal.mul_iSup]
  refine iSup_le fun K => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun hKU => ?_
  rw [ENNReal.mul_iSup]
  exact iSup_le fun hK => hcompact_bound K hKU hK

/-- 7.4: Maximal theorem for complex Borel measures on `ℝ^k`, with exact constant `3^k`:
for every `λ > 0`, `m{x : Mμ(x) > λ} ≤ 3^k * λ⁻¹ * ‖μ‖`, where `‖μ‖ = |μ|(ℝ^k)`. -/
theorem theorem_7_4 {k : ℕ} (μ : ComplexMeasure (EuclideanSpace ℝ (Fin k)))
    {lam : ℝ} (hlam : 0 < lam) :
    volume {x | ENNReal.ofReal lam < maximalFunctionComplex μ x} ≤
      ENNReal.ofReal ((3 : ℝ) ^ k * lam⁻¹ * ‖μ‖) := by
  have hmul := theorem_7_4_pos_mul μ.variation (ENNReal.ofReal lam)
  have hlam0 : ENNReal.ofReal lam ≠ 0 := (ENNReal.ofReal_pos.mpr hlam).ne'
  have hlamtop : ENNReal.ofReal lam ≠ ∞ := ENNReal.ofReal_ne_top
  have hdiv :
      volume {x | ENNReal.ofReal lam < maximalFunctionComplex μ x} ≤
        ((3 : ℝ≥0∞) ^ k * μ.variation univ) / ENNReal.ofReal lam := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hlam0) (Or.inl hlamtop), mul_comm]
    exact hmul
  have hrhs :
      ((3 : ℝ≥0∞) ^ k * μ.variation univ) / ENNReal.ofReal lam =
        ENNReal.ofReal ((3 : ℝ) ^ k * lam⁻¹ * ‖μ‖) := by
    have hnorm : μ.variation univ = ENNReal.ofReal ‖μ‖ := by
      rw [complex_norm_eq_variation, measureReal_def,
        ENNReal.ofReal_toReal (measure_ne_top μ.variation univ)]
    have h3 : (3 : ℝ≥0∞) ^ k = ENNReal.ofReal ((3 : ℝ) ^ k) := by
      rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    rw [hnorm, h3, div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos hlam,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rwa [hrhs] at hdiv

/-- 7.4 (variation form in `ℝ≥0∞`): `m{x : Mμ(x) > λ} ≤ 3^k / λ * |μ|(ℝ^k)` for `λ > 0`. -/
theorem theorem_7_4_variation {k : ℕ} (μ : ComplexMeasure (EuclideanSpace ℝ (Fin k)))
    {lam : ℝ} (hlam : 0 < lam) :
    volume {x | ENNReal.ofReal lam < maximalFunctionComplex μ x} ≤
      (3 : ℝ≥0∞) ^ k / ENNReal.ofReal lam * μ.variation univ := by
  have hmul := theorem_7_4_pos_mul μ.variation (ENNReal.ofReal lam)
  have hlam0 : ENNReal.ofReal lam ≠ 0 := (ENNReal.ofReal_pos.mpr hlam).ne'
  have hlamtop : ENNReal.ofReal lam ≠ ∞ := ENNReal.ofReal_ne_top
  rw [div_eq_mul_inv, mul_assoc, mul_comm (ENNReal.ofReal lam)⁻¹, ← mul_assoc,
    ← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl hlam0) (Or.inl hlamtop), mul_comm]
  exact hmul

end Node7_4

section Node7_5

/-- 7.5: Chebyshev / Markov inequality for `f ∈ L¹(μ)`:
`μ{x : |f(x)| > λ} ≤ λ⁻¹ * ∫ |f| dμ` for every `λ > 0`. -/
theorem chebyshev_L1 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : Integrable f μ) {lam : ℝ} (hlam : 0 < lam) :
    μ {x | lam < ‖f x‖} ≤ ENNReal.ofReal (lam⁻¹ * ∫ x, ‖f x‖ ∂μ) := by
  have hsub : {x | lam < ‖f x‖} ⊆ {x | ENNReal.ofReal lam ≤ ‖f x‖ₑ} := by
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hx.le
  have hmarkov := mul_meas_ge_le_lintegral₀ hf.aestronglyMeasurable.enorm (ENNReal.ofReal lam)
  have hlam0 : ENNReal.ofReal lam ≠ 0 := (ENNReal.ofReal_pos.mpr hlam).ne'
  have hlamtop : ENNReal.ofReal lam ≠ ∞ := ENNReal.ofReal_ne_top
  have hdiv : μ {x | ENNReal.ofReal lam ≤ ‖f x‖ₑ} ≤
      (∫⁻ x, ‖f x‖ₑ ∂μ) / ENNReal.ofReal lam := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hlam0) (Or.inl hlamtop), mul_comm]
    exact hmarkov
  have hrhs : (∫⁻ x, ‖f x‖ₑ ∂μ) / ENNReal.ofReal lam =
      ENNReal.ofReal (lam⁻¹ * ∫ x, ‖f x‖ ∂μ) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hf, div_eq_mul_inv,
      ← ENNReal.ofReal_inv_of_pos hlam,
      ← ENNReal.ofReal_mul (integral_nonneg fun _ => norm_nonneg _), mul_comm]
  exact (measure_mono hsub).trans (hrhs ▸ hdiv)

/-- 7.5: Rudin's weak `L¹(μ)` space for complex-valued functions: measurable (up to null sets)
functions whose distribution function satisfies `λ · μ{|f| > λ} ≤ C` for some `C < ∞` and all `λ > 0`. -/
def IsWeakL1 {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℂ) : Prop :=
  AEMeasurable f μ ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam →
      ENNReal.ofReal lam * μ {x | lam < ‖f x‖} ≤ ENNReal.ofReal C

/-- 7.5: equivalent division formulation `μ{|f| > λ} ≤ C / λ` of weak `L¹`. -/
theorem isWeakL1_iff_div {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℂ) :
    IsWeakL1 μ f ↔ AEMeasurable f μ ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam →
        μ {x | lam < ‖f x‖} ≤ ENNReal.ofReal (C / lam) := by
  refine and_congr_right fun _ => exists_congr fun C => and_congr_right fun hC => ?_
  refine forall_congr' fun lam => imp_congr_right fun hlam => ?_
  have hlam0 : ENNReal.ofReal lam ≠ 0 := (ENNReal.ofReal_pos.mpr hlam).ne'
  have hlamtop : ENNReal.ofReal lam ≠ ∞ := ENNReal.ofReal_ne_top
  have hdiv : ENNReal.ofReal (C / lam) = ENNReal.ofReal C / ENNReal.ofReal lam := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul hC, ENNReal.ofReal_inv_of_pos hlam, ← div_eq_mul_inv]
  rw [hdiv, ENNReal.le_div_iff_mul_le (Or.inl hlam0) (Or.inl hlamtop), mul_comm]

/-- 7.5: every `L¹(μ)` function belongs to weak `L¹(μ)`. -/
theorem integrable_mem_weakL1 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : Integrable f μ) : IsWeakL1 μ f := by
  rw [isWeakL1_iff_div]
  refine ⟨hf.aemeasurable, ∫ x, ‖f x‖ ∂μ, integral_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro lam hlam
  simpa [div_eq_mul_inv, mul_comm] using chebyshev_L1 hf hlam

/-- 7.5: the printed counterexample `f(x) = 1/x` on `(0, 1)` belongs to weak `L¹` (with bound `1/λ`)
but is not in `L¹`, proving `L¹` is a proper subset of weak `L¹`. -/
def invOnUnitIoo (x : ℝ) : ℂ :=
  (Ioo (0 : ℝ) 1).indicator (fun t => ((t⁻¹ : ℝ) : ℂ)) x

theorem invOnUnitIoo_weakL1_bound {lam : ℝ} (hlam : 0 < lam) :
    volume {x : ℝ | lam < ‖invOnUnitIoo x‖} ≤ ENNReal.ofReal (1 / lam) := by
  by_cases h1 : lam < 1
  · have hsub : {x : ℝ | lam < ‖invOnUnitIoo x‖} ⊆ Ioo 0 1 := by
      intro x hx
      simp only [mem_ofPred_eq, invOnUnitIoo] at hx
      by_contra hxmem
      simp only [Set.indicator_of_notMem hxmem, norm_zero] at hx
      linarith
    calc
      volume {x : ℝ | lam < ‖invOnUnitIoo x‖}
        ≤ volume (Ioo (0 : ℝ) 1) := measure_mono hsub
      _ = ENNReal.ofReal 1 := by simp [Real.volume_Ioo]
      _ ≤ ENNReal.ofReal (1 / lam) := by
          apply ENNReal.ofReal_le_ofReal
          rw [le_div_iff₀ hlam, one_mul]
          exact h1.le
  · have hsub : {x : ℝ | lam < ‖invOnUnitIoo x‖} ⊆ Ioo 0 (1 / lam) := by
      intro x hx
      simp only [mem_ofPred_eq, invOnUnitIoo] at hx
      by_cases hxmem : x ∈ Ioo (0 : ℝ) 1
      · simp only [Set.indicator_of_mem hxmem, Complex.norm_real, Real.norm_eq_abs,
          abs_inv, abs_of_pos hxmem.1] at hx
        refine ⟨hxmem.1, ?_⟩
        rw [lt_div_iff₀ hlam]
        have hmul := mul_lt_mul_of_pos_right hx hxmem.1
        rw [inv_mul_cancel₀ hxmem.1.ne'] at hmul
        linarith
      · simp only [Set.indicator_of_notMem hxmem, norm_zero] at hx
        linarith
    calc
      volume {x : ℝ | lam < ‖invOnUnitIoo x‖}
        ≤ volume (Ioo 0 (1 / lam)) := measure_mono hsub
      _ = ENNReal.ofReal (1 / lam) := by simp [Real.volume_Ioo]

theorem invOnUnitIoo_isWeakL1 : IsWeakL1 volume invOnUnitIoo := by
  rw [isWeakL1_iff_div]
  have hmeas : Measurable invOnUnitIoo := by
    unfold invOnUnitIoo
    exact (Complex.continuous_ofReal.measurable.comp measurable_inv).indicator measurableSet_Ioo
  exact ⟨hmeas.aemeasurable, 1, zero_le_one, fun _ hlam => invOnUnitIoo_weakL1_bound hlam⟩

theorem invOnUnitIoo_not_integrable : ¬ Integrable invOnUnitIoo volume := by
  intro hint
  let J : ℕ → Set ℝ := fun n => Ioc ((1 / 2 : ℝ) ^ (n + 2)) ((1 / 2 : ℝ) ^ (n + 1))
  have hJsub (n : ℕ) : J n ⊆ Ioo 0 1 := by
    intro x hx
    simp only [J, mem_Ioc] at hx
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 2) := pow_pos (by norm_num) (n + 2)
    refine ⟨hpos.trans hx.1, lt_of_le_of_lt hx.2 ?_⟩
    have hpow : (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  have hJdisj : Pairwise (Function.onFun Disjoint J) := by
    intro m n hmn
    wlog hlt : m < n generalizing m n
    · exact (this hmn.symm (by omega)).symm
    refine Set.disjoint_left.mpr fun x hxm hxn => ?_
    simp only [J, mem_Ioc] at hxm hxn
    have hpow : (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ (m + 2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  have hJlower (n : ℕ) : (1 / 2 : ℝ≥0∞) ≤ ∫⁻ x in J n, ‖invOnUnitIoo x‖ₑ ∂volume := by
    have hpoint : ∀ x ∈ J n, ENNReal.ofReal ((2 : ℝ) ^ (n + 1)) ≤ ‖invOnUnitIoo x‖ₑ := by
      intro x hx
      have hxIoo : x ∈ Ioo (0 : ℝ) 1 := hJsub n hx
      simp only [invOnUnitIoo, Set.indicator_of_mem hxIoo, ← ofReal_norm,
        Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hxIoo.1]
      apply ENNReal.ofReal_le_ofReal
      rw [le_inv_comm₀ (by positivity) hxIoo.1]
      simpa [one_div, inv_pow] using hx.2
    have hvol : volume (J n) = ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 2)) := by
      dsimp [J]
      rw [Real.volume_Ioc]
      congr 1
      ring
    calc
      (1 / 2 : ℝ≥0∞)
        = ENNReal.ofReal ((2 : ℝ) ^ (n + 1) * (1 / 2 : ℝ) ^ (n + 2)) := by
          have hprod : (2 : ℝ) ^ (n + 1) * (1 / 2 : ℝ) ^ (n + 2) = 1 / 2 := by
            rw [pow_succ (1 / 2 : ℝ) (n + 1), ← mul_assoc]
            have hcancel : (2 : ℝ) ^ (n + 1) * (1 / 2 : ℝ) ^ (n + 1) = 1 := by
              rw [← mul_pow]
              norm_num
            rw [hcancel, one_mul]
          rw [hprod, ENNReal.ofReal_div_of_pos zero_lt_two, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
      _ = ENNReal.ofReal ((2 : ℝ) ^ (n + 1)) * volume (J n) := by
          rw [hvol, ENNReal.ofReal_mul (by positivity)]
      _ = ∫⁻ _ in J n, ENNReal.ofReal ((2 : ℝ) ^ (n + 1)) ∂volume := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ x in J n, ‖invOnUnitIoo x‖ₑ ∂volume :=
          setLIntegral_mono' measurableSet_Ioc hpoint
  have hsum : (∑' n : ℕ, ∫⁻ x in J n, ‖invOnUnitIoo x‖ₑ ∂volume) ≤
      ∫⁻ x, ‖invOnUnitIoo x‖ₑ ∂volume := by
    rw [← lintegral_iUnion (fun _ => measurableSet_Ioc) hJdisj]
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  have hinf : (∞ : ℝ≥0∞) ≤ ∑' n : ℕ, ∫⁻ x in J n, ‖invOnUnitIoo x‖ₑ ∂volume := by
    calc
      (∞ : ℝ≥0∞) = ∑' _ : ℕ, (1 / 2 : ℝ≥0∞) := by
        rw [ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)]
      _ ≤ ∑' n : ℕ, ∫⁻ x in J n, ‖invOnUnitIoo x‖ₑ ∂volume :=
        ENNReal.tsum_le_tsum hJlower
  exact hint.2.ne (top_unique (hinf.trans hsum))

/-- 7.5: on `(0, 1)` equipped with restricted Lebesgue measure, `x ↦ 1/x` is in weak `L¹`
but not in `L¹`, witnessing strict inclusion `L¹ ⊂ weak L¹`. -/
theorem weakL1_strict_inclusion_unitIoo :
    IsWeakL1 (volume.restrict (Ioo (0 : ℝ) 1)) (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ)) ∧
      ¬ IntegrableOn (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ)) (Ioo (0 : ℝ) 1) volume := by
  constructor
  · rw [isWeakL1_iff_div]
    refine ⟨(Complex.continuous_ofReal.measurable.comp measurable_inv).aemeasurable,
      1, zero_le_one, fun lam hlam => ?_⟩
    have heq :
        (volume.restrict (Ioo (0 : ℝ) 1)) {x : ℝ | lam < ‖((x⁻¹ : ℝ) : ℂ)‖} =
          volume {x : ℝ | lam < ‖invOnUnitIoo x‖} := by
      rw [Measure.restrict_apply' measurableSet_Ioo]
      congr 1
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, invOnUnitIoo]
      constructor
      · rintro ⟨hx, hmem⟩
        simpa [Set.indicator_of_mem hmem] using hx
      · intro hx
        by_cases hmem : x ∈ Ioo (0 : ℝ) 1
        · exact ⟨by simpa [Set.indicator_of_mem hmem] using hx, hmem⟩
        · simp only [Set.indicator_of_notMem hmem, norm_zero] at hx
          linarith
    rw [heq]
    exact invOnUnitIoo_weakL1_bound hlam
  · intro hint
    exact invOnUnitIoo_not_integrable ((integrable_indicator_iff measurableSet_Ioo).mpr hint)

/-- 7.5: Hardy–Littlewood maximal function `Mf(x) = sup_{r > 0} m(B(x, r))⁻¹ ∫_{B(x, r)} |f| dm`
of a complex-valued function on `ℝ^k`. -/
def maximalFunctionFun {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → ℂ)
    (x : EuclideanSpace ℝ (Fin k)) : ℝ≥0∞ :=
  ⨆ r : ℝ, ⨆ (_ : 0 < r),
    (∫⁻ y in Metric.ball x r, ‖f y‖ₑ ∂volume) / volume (Metric.ball x r)

/-- 7.5: for `f ∈ L¹(ℝ^k)` and `dμ = f dm` (`μ = volume.withDensityᵥ f`), `Mf = Mμ` everywhere. -/
theorem maximalFunctionFun_eq_maximalFunctionComplex {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℂ} (hf : Integrable f volume) :
    maximalFunctionFun f = maximalFunctionComplex (volume.withDensityᵥ f) := by
  ext x
  unfold maximalFunctionFun maximalFunctionComplex maximalFunctionPos ballQuotientPos
  rw [Measure.variation_withDensityᵥ hf]
  refine iSup_congr fun r => iSup_congr fun _ => ?_
  rw [withDensity_apply _ measurableSet_ball]

/-- 7.5: `Mf` is lower semicontinuous and Borel measurable for every `f ∈ L¹(ℝ^k)`. -/
theorem lowerSemicontinuous_maximalFunctionFun {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℂ} (hf : Integrable f volume) :
    LowerSemicontinuous (maximalFunctionFun f) := by
  rw [maximalFunctionFun_eq_maximalFunctionComplex hf]
  exact lowerSemicontinuous_maximalFunctionComplex (volume.withDensityᵥ f)

theorem measurable_maximalFunctionFun {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℂ} (hf : Integrable f volume) :
    Measurable (maximalFunctionFun f) :=
  (lowerSemicontinuous_maximalFunctionFun hf).measurable

/-- 7.5: weak-(1,1) maximal inequality for `f ∈ L¹(ℝ^k)` with exact constant `3^k`:
`m{x : (Mf)(x) > λ} ≤ 3^k * λ⁻¹ * ‖f‖₁` for every `λ > 0`. -/
theorem theorem_7_5_maximal_weak_L1 {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℂ} (hf : Integrable f volume)
    {lam : ℝ} (hlam : 0 < lam) :
    volume {x | ENNReal.ofReal lam < maximalFunctionFun f x} ≤
      ENNReal.ofReal ((3 : ℝ) ^ k * lam⁻¹ * ∫ x, ‖f x‖ ∂volume) := by
  rw [maximalFunctionFun_eq_maximalFunctionComplex hf]
  have h74 := theorem_7_4 (volume.withDensityᵥ f) hlam
  have hnorm : ‖volume.withDensityᵥ f‖ = ∫ x, ‖f x‖ ∂volume := by
    rw [complex_norm_eq_variation, Measure.variation_withDensityᵥ hf, measureReal_def,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_norm_eq_lintegral_enorm hf,
      ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]
  rwa [hnorm] at h74

end Node7_5

/-! ## §7.6–7.12: Lebesgue points, differentiation of integrals, and metric density -/

section BallBridges

private theorem ball_ae_eq_closedBall_of_pos {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (x : E) {r : ℝ} (hr : 0 < r) :
    Metric.ball x r =ᵐ[μ] Metric.closedBall x r := by
  refine ae_eq_set.mpr ⟨?_, ?_⟩
  · simp [Set.sdiff_eq_empty.mpr Metric.ball_subset_closedBall]
  · rw [Metric.closedBall_sdiff_ball]
    exact μ.addHaar_sphere_of_ne_zero x hr.ne'

private theorem measure_closedBall_eq_ball_of_pos {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (x : E) {r : ℝ} (hr : 0 < r) :
    μ (Metric.closedBall x r) = μ (Metric.ball x r) :=
  measure_congr (ball_ae_eq_closedBall_of_pos μ x hr).symm

private theorem measureReal_closedBall_eq_ball_of_pos {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (x : E) {r : ℝ} (hr : 0 < r) :
    μ.real (Metric.closedBall x r) = μ.real (Metric.ball x r) := by
  simp [measureReal_def, measure_closedBall_eq_ball_of_pos μ x hr]

private theorem setAverage_closedBall_eq_ball_of_pos {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (x : E) {r : ℝ} (hr : 0 < r) :
    ⨍ y in Metric.closedBall x r, g y ∂μ =
      (μ.real (Metric.ball x r))⁻¹ • ∫ y in Metric.ball x r, g y ∂μ := by
  rw [setAverage_eq, measureReal_closedBall_eq_ball_of_pos μ x hr,
    setIntegral_congr_set (ball_ae_eq_closedBall_of_pos μ x hr).symm]

private theorem continuousAt_tendsto_ball_oscillation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {f : E → ℂ} (hf : LocallyIntegrable f μ) {x : E} (hcont : ContinuousAt f x) :
    Tendsto (fun r => (μ.real (Metric.ball x r))⁻¹ * ∫ y in Metric.ball x r, ‖f y - f x‖ ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hcont (ε / 2) (half_pos hε)
  filter_upwards [Ioc_mem_nhdsGT hδ] with r hr
  have hint_f : IntegrableOn f (Metric.ball x r) μ :=
    (hf.integrableOn_isCompact (isCompact_closedBall x r)).mono_set Metric.ball_subset_closedBall
  have hint_c : IntegrableOn (fun _ => f x) (Metric.ball x r) μ :=
    integrableOn_const measure_ball_ne_top
  have hint_norm : IntegrableOn (fun y => ‖f y - f x‖) (Metric.ball x r) μ :=
    (hint_f.sub hint_c).norm
  have hnonneg : 0 ≤ (μ.real (Metric.ball x r))⁻¹ * ∫ y in Metric.ball x r, ‖f y - f x‖ ∂μ :=
    mul_nonneg (inv_nonneg.mpr measureReal_nonneg) (integral_nonneg fun _ => norm_nonneg _)
  have hvpos : 0 < μ.real (Metric.ball x r) :=
    ENNReal.toReal_pos (measure_ball_pos μ x hr.1).ne' measure_ball_ne_top
  have hbound : ∫ y in Metric.ball x r, ‖f y - f x‖ ∂μ ≤
      ∫ _ in Metric.ball x r, (ε / 2) ∂μ := by
    refine setIntegral_mono_on hint_norm (integrableOn_const measure_ball_ne_top)
      measurableSet_ball fun y hy => ?_
    rw [← dist_eq_norm]
    exact (hclose (lt_of_lt_of_le (mem_ball.mp hy) hr.2)).le
  rw [setIntegral_const, smul_eq_mul] at hbound
  have hprod : (μ.real (Metric.ball x r))⁻¹ * ∫ y in Metric.ball x r, ‖f y - f x‖ ∂μ ≤ ε / 2 := by
    calc
      (μ.real (Metric.ball x r))⁻¹ * ∫ y in Metric.ball x r, ‖f y - f x‖ ∂μ
        ≤ (μ.real (Metric.ball x r))⁻¹ * (μ.real (Metric.ball x r) * (ε / 2)) :=
          mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hvpos.le)
      _ = ε / 2 := by rw [← mul_assoc, inv_mul_cancel₀ hvpos.ne', one_mul]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith

private theorem ae_tendsto_ball_oscillation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {f : E → ℂ} (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ,
      Tendsto (fun r => (μ.real (Metric.ball x r))⁻¹ * ∫ y in Metric.ball x r, ‖f y - f x‖ ∂μ)
        (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (μ := μ) hf 0] with x hx
  have hclosed : Tendsto (fun r : ℝ => ⨍ y in Metric.closedBall x r, ‖f y - f x‖ ∂μ)
      (𝓝[>] 0) (𝓝 0) :=
    hx (fun _ => x) id tendsto_id (Eventually.of_forall fun r => by simp)
  refine hclosed.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  simpa [smul_eq_mul] using setAverage_closedBall_eq_ball_of_pos μ (fun y => ‖f y - f x‖) x hr

end BallBridges

section Node7_6

/-- 7.6: A point `x ∈ ℝ^k` is a *Lebesgue point* of `f : ℝ^k → ℂ` if the open-ball average
oscillation `m(B(x, r))⁻¹ ∫_{B(x, r)} |f(y) - f(x)| dm(y)` tends to `0` as `r → 0⁺`. -/
def IsLebesguePoint {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → ℂ)
    (x : EuclideanSpace ℝ (Fin k)) : Prop :=
  Tendsto (fun r => (volume.real (Metric.ball x r))⁻¹ *
      ∫ y in Metric.ball x r, ‖f y - f x‖ ∂volume)
    (𝓝[>] 0) (𝓝 0)

/-- 7.6 (1D specialization on `ℝ` for 7.11): `x ∈ ℝ` is a Lebesgue point of `f : ℝ → ℂ`. -/
def IsLebesguePointReal (f : ℝ → ℂ) (x : ℝ) : Prop :=
  Tendsto (fun r => (volume.real (Metric.ball x r))⁻¹ *
      ∫ y in Metric.ball x r, ‖f y - f x‖ ∂volume)
    (𝓝[>] 0) (𝓝 0)

/-- 7.6: `IsLebesguePoint` is equivalent to open-ball `setAverage` oscillation tending to `0`. -/
theorem isLebesguePoint_iff_tendsto_average {k : ℕ}
    (f : EuclideanSpace ℝ (Fin k) → ℂ) (x : EuclideanSpace ℝ (Fin k)) :
    IsLebesguePoint f x ↔
      Tendsto (fun r => ⨍ y in Metric.ball x r, ‖f y - f x‖ ∂volume) (𝓝[>] 0) (𝓝 0) := by
  simp [IsLebesguePoint, setAverage_eq]

/-- 7.6: If `f` is locally integrable on `ℝ^k` and continuous at `x`, then `x` is a Lebesgue point
of `f`. -/
theorem theorem_7_6_continuousAt_locallyIntegrable {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℂ} (hf : LocallyIntegrable f volume)
    {x : EuclideanSpace ℝ (Fin k)} (hcont : ContinuousAt f x) :
    IsLebesguePoint f x :=
  continuousAt_tendsto_ball_oscillation volume hf hcont

/-- 7.6: If `f ∈ L¹(ℝ^k)` is continuous at `x`, then `x` is a Lebesgue point of `f`. -/
theorem theorem_7_6_continuousAt {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℂ} (hf : Integrable f volume)
    {x : EuclideanSpace ℝ (Fin k)} (hcont : ContinuousAt f x) :
    IsLebesguePoint f x :=
  theorem_7_6_continuousAt_locallyIntegrable hf.locallyIntegrable hcont

/-- 7.6 (1D): If `f ∈ L¹(ℝ)` is continuous at `x`, then `x` is a Lebesgue point of `f`. -/
theorem continuousAt_isLebesguePointReal {f : ℝ → ℂ} (hf : Integrable f volume)
    {x : ℝ} (hcont : ContinuousAt f x) :
    IsLebesguePointReal f x :=
  continuousAt_tendsto_ball_oscillation volume hf.locallyIntegrable hcont

/-- 7.6: At every Lebesgue point `x` of a locally integrable `f : ℝ^k → ℂ`, the open-ball averages
`m(B(x, r))⁻¹ ∫_{B(x, r)} f dm` converge to `f(x)` as `r → 0⁺`. -/
theorem IsLebesguePoint.tendsto_ball_average {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℂ} (hf : LocallyIntegrable f volume)
    {x : EuclideanSpace ℝ (Fin k)} (hx : IsLebesguePoint f x) :
    Tendsto (fun r => (volume.real (Metric.ball x r))⁻¹ •
        ∫ y in Metric.ball x r, f y ∂volume)
      (𝓝[>] 0) (𝓝 (f x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hx
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hvpos : 0 < volume.real (Metric.ball x r) :=
    ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_ne_top
  have hint_f : IntegrableOn f (Metric.ball x r) volume :=
    (hf.integrableOn_isCompact (isCompact_closedBall x r)).mono_set Metric.ball_subset_closedBall
  have hint_c : IntegrableOn (fun _ => f x) (Metric.ball x r) volume :=
    integrableOn_const measure_ball_ne_top
  have hconst : f x = (volume.real (Metric.ball x r))⁻¹ •
      ∫ _ in Metric.ball x r, f x ∂volume := by
    rw [setIntegral_const, smul_smul, inv_mul_cancel₀ hvpos.ne', one_smul]
  calc
    ‖(volume.real (Metric.ball x r))⁻¹ • ∫ y in Metric.ball x r, f y ∂volume - f x‖
      = ‖(volume.real (Metric.ball x r))⁻¹ •
          (∫ y in Metric.ball x r, f y ∂volume - ∫ _ in Metric.ball x r, f x ∂volume)‖ := by
        conv_lhs => rw [hconst, ← smul_sub]
    _ = (volume.real (Metric.ball x r))⁻¹ *
          ‖∫ y in Metric.ball x r, (f y - f x) ∂volume‖ := by
        rw [← integral_sub hint_f hint_c, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr hvpos.le)]
    _ ≤ (volume.real (Metric.ball x r))⁻¹ *
          ∫ y in Metric.ball x r, ‖f y - f x‖ ∂volume :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.mpr hvpos.le)

end Node7_6

section Node7_7

/-- 7.7 (locally integrable form): If `f : ℝ^k → ℂ` is locally integrable with respect to Lebesgue
measure, then almost every `x ∈ ℝ^k` is a Lebesgue point of `f`. -/
theorem theorem_7_7_locallyIntegrable {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℂ}
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume, IsLebesguePoint f x :=
  ae_tendsto_ball_oscillation volume hf

/-- 7.7: Lebesgue differentiation theorem — if `f ∈ L¹(ℝ^k)`, then almost every `x ∈ ℝ^k` is a
Lebesgue point of `f`. -/
theorem theorem_7_7 {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℂ}
    (hf : Integrable f volume) :
    ∀ᵐ x ∂volume, IsLebesguePoint f x :=
  theorem_7_7_locallyIntegrable hf.locallyIntegrable

/-- 7.7 (1D specialization on `ℝ` for 7.11): if `f ∈ L¹(ℝ)`, almost every `x ∈ ℝ` is a Lebesgue
point of `f`. -/
theorem ae_isLebesguePointReal {f : ℝ → ℂ} (hf : Integrable f volume) :
    ∀ᵐ x ∂volume, IsLebesguePointReal f x :=
  ae_tendsto_ball_oscillation volume hf.locallyIntegrable

end Node7_7

section ComplexDecompositionBridges

/-- Every complex measure has a Lebesgue decomposition with respect to any σ-finite positive
measure (bridging the missing instance noted in `SCOPING-C.md`). -/
instance complexMeasure_haveLebesgueDecomposition {X : Type*} [MeasurableSpace X]
    (μ : ComplexMeasure X) (ν : Measure X) [SigmaFinite ν] :
    μ.HaveLebesgueDecomposition ν where
  rePart := inferInstance
  imPart := inferInstance

/-- The singular part `μ.singularPart ν` of a complex measure is mutually singular with respect to
`ν`. -/
theorem complexMeasure_singularPart_mutuallySingular {X : Type*} [MeasurableSpace X]
    (μ : ComplexMeasure X) (ν : Measure X) :
    μ.singularPart ν ⟂ᵥ ν.toENNRealVectorMeasure := by
  obtain ⟨A₁, hA₁, hreA₁, hνA₁⟩ := SignedMeasure.mutuallySingular_singularPart μ.re ν
  obtain ⟨A₂, hA₂, himA₂, hνA₂⟩ := SignedMeasure.mutuallySingular_singularPart μ.im ν
  refine ⟨A₁ ∩ A₂, hA₁.inter hA₂, ?_, ?_⟩
  · intro E hE
    rw [ComplexMeasure.singularPart, SignedMeasure.toComplexMeasure_apply]
    have h1 : μ.re.singularPart ν E = 0 := hreA₁ E (hE.trans inter_subset_left)
    have h2 : μ.im.singularPart ν E = 0 := himA₂ E (hE.trans inter_subset_right)
    exact Complex.ext (by simpa [ComplexMeasure.re] using h1)
      (by simpa [ComplexMeasure.im] using h2)
  · intro E hE
    by_cases hEm : MeasurableSet E
    · rw [Measure.toENNRealVectorMeasure_apply_measurable hEm]
      have hν1 : ν A₁ᶜ = 0 := by
        simpa [Measure.toENNRealVectorMeasure_apply_measurable hA₁.compl] using hνA₁ A₁ᶜ subset_rfl
      have hν2 : ν A₂ᶜ = 0 := by
        simpa [Measure.toENNRealVectorMeasure_apply_measurable hA₂.compl] using hνA₂ A₂ᶜ subset_rfl
      have hcov : E ⊆ A₁ᶜ ∪ A₂ᶜ := by
        intro y hy
        simpa [compl_inter] using hE hy
      exact le_antisymm
        ((measure_mono hcov).trans ((measure_union_le _ _).trans (by simp [hν1, hν2]))) bot_le
    · exact ν.toENNRealVectorMeasure.not_measurable hEm

/-- Complex Radon–Nikodym representation: if `μ ≪ᵥ ν` with `ν` σ-finite, then
`ν.withDensityᵥ (μ.rnDeriv ν) = μ`. -/
theorem complexMeasure_withDensityᵥ_rnDeriv_eq {X : Type*} [MeasurableSpace X]
    (μ : ComplexMeasure X) (ν : Measure X) [SigmaFinite ν]
    (hμ : μ ≪ᵥ ν.toENNRealVectorMeasure) :
    ν.withDensityᵥ (μ.rnDeriv ν) = μ := by
  have hdecomp := μ.singularPart_add_withDensity_rnDeriv_eq (μ := ν)
  have hsing_eq : μ.singularPart ν = μ + -(ν.withDensityᵥ (μ.rnDeriv ν)) := by
    calc
      μ.singularPart ν
        = (μ.singularPart ν + ν.withDensityᵥ (μ.rnDeriv ν)) +
            -(ν.withDensityᵥ (μ.rnDeriv ν)) := by
          rw [add_assoc, add_neg_cancel, add_zero]
      _ = μ + -(ν.withDensityᵥ (μ.rnDeriv ν)) := by rw [hdecomp]
  have hac_wd : ν.withDensityᵥ (μ.rnDeriv ν) ≪ᵥ ν.toENNRealVectorMeasure := by
    intro E hE
    by_cases hEm : MeasurableSet E
    · rw [withDensityᵥ_apply (μ.integrable_rnDeriv ν) hEm]
      have hνE : ν E = 0 := by
        simpa [Measure.toENNRealVectorMeasure_apply_measurable hEm] using hE
      exact setIntegral_measure_zero _ hνE
    · exact (ν.withDensityᵥ (μ.rnDeriv ν)).not_measurable hEm
  have hac_neg : -(ν.withDensityᵥ (μ.rnDeriv ν)) ≪ᵥ ν.toENNRealVectorMeasure := by
    intro E hE
    simp [hac_wd hE]
  have hsing_zero : μ.singularPart ν = 0 :=
    eq_zero_of_ac_of_singular (hsing_eq ▸ hμ.add hac_neg)
      (complexMeasure_singularPart_mutuallySingular μ ν)
  simpa [hsing_zero] using hdecomp

end ComplexDecompositionBridges

section Node7_8

/-- 7.8 (pointwise at every Lebesgue point): for `f ∈ L¹(ℝ^k)` and `dμ = f dm`, `(Dμ)(x) = f(x)`
at every Lebesgue point `x` of `f`. -/
theorem hasSymmetricDeriv_withDensityᵥ_of_isLebesguePoint {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℂ} (hf : Integrable f volume)
    {x : EuclideanSpace ℝ (Fin k)} (hx : IsLebesguePoint f x) :
    HasSymmetricDeriv (volume.withDensityᵥ f) x (f x) := by
  refine (hx.tendsto_ball_average hf.locallyIntegrable).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r _
  rw [ballQuotient, withDensityᵥ_apply hf measurableSet_ball, Complex.real_smul,
    Complex.ofReal_inv, div_eq_mul_inv, mul_comm]

/-- 7.8: Let `μ` be a complex Borel measure on `ℝ^k` with `μ ≪ m`, and let `f` be the
Radon–Nikodym derivative `μ.rnDeriv volume`. Then `(Dμ)(x) = f(x)` for `m`-a.e. `x`, `Dμ ∈ L¹(m)`,
and `μ(E) = ∫_E (Dμ) dm` for every Borel set `E ⊆ ℝ^k`. -/
theorem theorem_7_8 {k : ℕ} (μ : ComplexMeasure (EuclideanSpace ℝ (Fin k)))
    (hμ : μ ≪ᵥ volume.toENNRealVectorMeasure) :
    (∀ᵐ x ∂volume, HasSymmetricDeriv μ x (μ.rnDeriv volume x)) ∧
      symmetricDeriv μ =ᵐ[volume] μ.rnDeriv volume ∧
      Integrable (symmetricDeriv μ) volume ∧
      ∀ E : Set (EuclideanSpace ℝ (Fin k)), MeasurableSet E →
        μ E = ∫ x in E, symmetricDeriv μ x ∂volume := by
  have hf : Integrable (μ.rnDeriv volume) volume := μ.integrable_rnDeriv volume
  have hrep : volume.withDensityᵥ (μ.rnDeriv volume) = μ :=
    complexMeasure_withDensityᵥ_rnDeriv_eq μ volume hμ
  have hae_deriv : ∀ᵐ x ∂volume, HasSymmetricDeriv μ x (μ.rnDeriv volume x) := by
    filter_upwards [theorem_7_7 hf] with x hx
    have h := hasSymmetricDeriv_withDensityᵥ_of_isLebesguePoint hf hx
    rwa [hrep] at h
  have hae_eq : symmetricDeriv μ =ᵐ[volume] μ.rnDeriv volume := by
    filter_upwards [hae_deriv] with x hx using hx.symmetricDeriv_eq
  refine ⟨hae_deriv, hae_eq, hf.congr hae_eq.symm, ?_⟩
  intro E hE
  calc
    μ E = (volume.withDensityᵥ (μ.rnDeriv volume)) E := by rw [hrep]
    _ = ∫ x in E, μ.rnDeriv volume x ∂volume := withDensityᵥ_apply hf hE
    _ = ∫ x in E, symmetricDeriv μ x ∂volume :=
      integral_congr_ae (ae_restrict_of_ae hae_eq.symm)

end Node7_8

section Node7_9

/-- 7.9: A sequence `E : ℕ → Set (ℝ^k)` of Borel sets *shrinks nicely* to `x ∈ ℝ^k` if there exist
`α > 0` and positive radii `r_i → 0` such that `E_i ⊆ B(x, r_i)` and
`m(E_i) ≥ α · m(B(x, r_i))` for all `i`. Note that `x ∈ E_i` is NOT required. -/
def ShrinksNicelyTo {k : ℕ} (E : ℕ → Set (EuclideanSpace ℝ (Fin k)))
    (x : EuclideanSpace ℝ (Fin k)) : Prop :=
  (∀ i, MeasurableSet (E i)) ∧
    ∃ α : ℝ, 0 < α ∧ ∃ r : ℕ → ℝ, (∀ i, 0 < r i) ∧ Tendsto r atTop (𝓝 0) ∧
      ∀ i, E i ⊆ Metric.ball x (r i) ∧
        ENNReal.ofReal α * volume (Metric.ball x (r i)) ≤ volume (E i)

/-- 7.9: Centered open balls `B(x, r_i)` with `r_i > 0` and `r_i → 0` shrink nicely to `x`. -/
theorem shrinksNicelyTo_balls {k : ℕ} (x : EuclideanSpace ℝ (Fin k))
    {r : ℕ → ℝ} (hrpos : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0)) :
    ShrinksNicelyTo (fun i => Metric.ball x (r i)) x := by
  refine ⟨fun _ => measurableSet_ball, 1, zero_lt_one, r, hrpos, hrlim, fun i => ⟨subset_rfl, ?_⟩⟩
  simp

/-- 7.9 (printed non-containment remark): in `ℝ^(k+1)`, there exist sequences of open balls
shrinking nicely to `x` such that `x ∉ E_i` for every `i`. -/
theorem exists_shrinksNicelyTo_notMem (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 1))) :
    ∃ E : ℕ → Set (EuclideanSpace ℝ (Fin (k + 1))),
      ShrinksNicelyTo E x ∧ ∀ i, x ∉ E i := by
  let e0 : EuclideanSpace ℝ (Fin (k + 1)) := EuclideanSpace.single 0 1
  have he0 : ‖e0‖ = 1 := by simp [e0]
  let r : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 1)
  have hrpos : ∀ i, 0 < r i := fun i => by dsimp [r]; positivity
  have hrlim : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let E : ℕ → Set (EuclideanSpace ℝ (Fin (k + 1))) :=
    fun i => Metric.ball (x + ((2 / 3 : ℝ) * r i) • e0) ((1 / 3 : ℝ) * r i)
  refine ⟨E, ⟨fun _ => measurableSet_ball, (1 / 3 : ℝ) ^ (k + 1), by positivity, r, hrpos, hrlim,
    fun i => ⟨?_, ?_⟩⟩, ?_⟩
  · intro y hy
    rw [mem_ball] at hy ⊢
    calc
      dist y x ≤ dist y (x + ((2 / 3 : ℝ) * r i) • e0) +
          dist (x + ((2 / 3 : ℝ) * r i) • e0) x := dist_triangle _ _ _
      _ < (1 / 3 : ℝ) * r i + (2 / 3 : ℝ) * r i := by
        have hd : dist (x + ((2 / 3 : ℝ) * r i) • e0) x = (2 / 3 : ℝ) * r i := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he0, mul_one, Real.norm_eq_abs,
            abs_of_pos (by positivity)]
        linarith
      _ = r i := by ring
  · have hscale : volume (E i) =
        ENNReal.ofReal ((1 / 3 : ℝ) ^ (k + 1)) * volume (Metric.ball x (r i)) := by
      dsimp [E]
      rw [volume.addHaar_ball_mul_of_pos _ (by norm_num : (0 : ℝ) < 1 / 3) (r i),
        volume.addHaar_ball_center x (r i), finrank_euclideanSpace_fin]
    exact hscale.ge
  · intro i hxmem
    dsimp [E] at hxmem
    rw [mem_ball, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, he0, mul_one,
      Real.norm_eq_abs, abs_of_pos (by positivity)] at hxmem
    linarith [hrpos i]

/-- 7.9 (printed non-example in `ℝ²`): nested open rectangles `(0, 1/(n+1)) × (0, 1/(n+1)²)` have
diameter tending to `0`, yet do NOT shrink nicely to `0`. -/
def thinRectanglesR2 (n : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  (WithLp.ofLp : EuclideanSpace ℝ (Fin 2) → (Fin 2 → ℝ)) ⁻¹'
    Set.pi univ ![(Ioo 0 (1 / ((n : ℝ) + 1))), (Ioo 0 ((1 / ((n : ℝ) + 1)) ^ 2))]

theorem not_shrinksNicelyTo_thinRectanglesR2 :
    ¬ ShrinksNicelyTo thinRectanglesR2 0 := by
  rintro ⟨_, α, hα, r, hrpos, _, hcond⟩
  have hαpi : 0 < α * Real.pi := mul_pos hα Real.pi_pos
  obtain ⟨N, hN⟩ := exists_nat_gt ((16 / 9 : ℝ) / (α * Real.pi))
  have h1 : 0 < (N : ℝ) + 1 := by positivity
  let δ : ℝ := 1 / ((N : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨hsub, hvol_le⟩ := hcond N
  let p : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![(3 / 4 : ℝ) * δ, (1 / 2 : ℝ) * δ ^ 2]
  have hp_mem : p ∈ thinRectanglesR2 N := by
    simp only [thinRectanglesR2, mem_preimage, mem_univ_pi, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, mem_Ioo]
    have hp0 : p.ofLp 0 = (3 / 4 : ℝ) * δ := rfl
    have hp1 : p.ofLp 1 = (1 / 2 : ℝ) * δ ^ 2 := rfl
    rw [hp0, hp1]
    have hδ_eq : 1 / ((N : ℝ) + 1) = δ := rfl
    rw [hδ_eq]
    exact ⟨⟨by positivity, by linarith⟩, ⟨by positivity, by linarith [sq_pos_of_pos hδ]⟩⟩
  have hp_ball : p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (r N) := hsub hp_mem
  have hr_lower : (3 / 4 : ℝ) * δ ≤ r N := by
    have hcoord : ‖p.ofLp 0‖ ≤ ‖p‖ := PiLp.norm_apply_le p 0
    have hp0 : ‖p.ofLp 0‖ = (3 / 4 : ℝ) * δ := by
      have hp0_eq : p.ofLp 0 = (3 / 4 : ℝ) * δ := rfl
      rw [hp0_eq, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hnorm : ‖p‖ < r N := by simpa [mem_ball, dist_zero_right] using hp_ball
    linarith
  have hrect_vol : volume (thinRectanglesR2 N) = ENNReal.ofReal (δ ^ 3) := by
    have hmp := (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
      (s := thinRectanglesR2 N)
    have hmeas : MeasurableSet (thinRectanglesR2 N) := by
      have hopen : IsOpen (Set.pi univ ![(Ioo 0 δ), (Ioo 0 (δ ^ 2))]) :=
        isOpen_set_pi finite_univ fun i _ => by fin_cases i <;> exact isOpen_Ioo
      exact hopen.measurableSet.preimage (PiLp.continuous_ofLp 2 _).measurable
    rw [← hmp hmeas.nullMeasurableSet]
    have hpre : (WithLp.toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2)) ⁻¹' thinRectanglesR2 N =
        Set.pi univ ![(Ioo 0 δ), (Ioo 0 (δ ^ 2))] := rfl
    rw [hpre, MeasureTheory.volume_pi_pi, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.volume_Ioo, sub_zero]
    rw [← ENNReal.ofReal_mul hδ.le]
    congr 1
    ring
  have hball_lower :
      ENNReal.ofReal (((3 / 4 : ℝ) * δ) ^ 2 * Real.pi) ≤
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (r N)) := by
    have hb1 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ((3 / 4 : ℝ) * δ)) ≤
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (r N)) :=
      measure_mono (Metric.ball_subset_ball hr_lower)
    rw [EuclideanSpace.volume_ball_fin_two] at hb1
    have h2 : ENNReal.ofReal ((3 / 4 : ℝ) * δ) ^ 2 * ENNReal.ofReal Real.pi =
        ENNReal.ofReal (((3 / 4 : ℝ) * δ) ^ 2 * Real.pi) := by
      rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    rwa [h2] at hb1
  have hineq :
      ENNReal.ofReal (α * (((3 / 4 : ℝ) * δ) ^ 2 * Real.pi)) ≤ ENNReal.ofReal (δ ^ 3) := by
    rw [ENNReal.ofReal_mul hα.le, ← hrect_vol]
    exact (mul_le_mul_of_nonneg_left hball_lower bot_le).trans hvol_le
  have hreal : α * (((3 / 4 : ℝ) * δ) ^ 2 * Real.pi) ≤ δ ^ 3 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hineq
  have hcancel : (α * Real.pi) * (9 / 16 : ℝ) ≤ δ := by
    have hpos_sq : 0 < δ ^ 2 := by positivity
    have hstep : ((α * Real.pi) * (9 / 16 : ℝ)) * δ ^ 2 ≤ δ * δ ^ 2 := by
      have hrew1 : ((α * Real.pi) * (9 / 16 : ℝ)) * δ ^ 2 =
          α * (((3 / 4 : ℝ) * δ) ^ 2 * Real.pi) := by ring
      have hrew2 : δ * δ ^ 2 = δ ^ 3 := by ring
      linarith
    exact le_of_mul_le_mul_right hstep hpos_sq
  have hcontr : (N : ℝ) + 1 ≤ (16 / 9 : ℝ) / (α * Real.pi) := by
    rw [le_div_iff₀ hαpi]
    have hmul := mul_le_mul_of_nonneg_left hcancel
      (by positivity : (0 : ℝ) ≤ (16 / 9) * ((N : ℝ) + 1))
    dsimp [δ] at hmul
    have h1ne : (N : ℝ) + 1 ≠ 0 := h1.ne'
    have hlhs : (16 / 9 : ℝ) * ((N : ℝ) + 1) * ((α * Real.pi) * (9 / 16 : ℝ)) =
        ((N : ℝ) + 1) * (α * Real.pi) := by ring
    have hrhs : (16 / 9 : ℝ) * ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1)) = 16 / 9 := by
      field_simp [h1ne]
    linarith
  linarith

end Node7_9

section Node7_10

/-- 7.10 (pointwise at every Lebesgue point): if `x` is a Lebesgue point of a locally integrable
`f : ℝ^k → ℂ` and `E` shrinks nicely to `x`, then both `m(E_i)⁻¹ ∫_{E_i} |f(y) - f(x)| dm(y) → 0`
and `m(E_i)⁻¹ ∫_{E_i} f dm → f(x)` as `i → ∞`. -/
theorem theorem_7_10_lebesguePoint {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℂ} (hf : LocallyIntegrable f volume)
    {x : EuclideanSpace ℝ (Fin k)} (hx : IsLebesguePoint f x)
    {E : ℕ → Set (EuclideanSpace ℝ (Fin k))} (hE : ShrinksNicelyTo E x) :
    Tendsto (fun i => (volume.real (E i))⁻¹ * ∫ y in E i, ‖f y - f x‖ ∂volume) atTop (𝓝 0) ∧
      Tendsto (fun i => (volume.real (E i))⁻¹ • ∫ y in E i, f y ∂volume) atTop (𝓝 (f x)) := by
  obtain ⟨hEmeas, α, hα, r, hrpos, hrlim, hcond⟩ := hE
  have hr_gt : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrlim, Eventually.of_forall hrpos⟩
  have hball_osc : Tendsto (fun i => α⁻¹ * ((volume.real (Metric.ball x (r i)))⁻¹ *
      ∫ y in Metric.ball x (r i), ‖f y - f x‖ ∂volume)) atTop (𝓝 0) := by
    simpa using (hx.comp hr_gt).const_mul α⁻¹
  have hE_osc : Tendsto (fun i => (volume.real (E i))⁻¹ *
      ∫ y in E i, ‖f y - f x‖ ∂volume) atTop (𝓝 0) := by
    refine squeeze_zero
      (fun _ => mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
        (integral_nonneg fun _ => norm_nonneg _))
      (fun i => ?_) hball_osc
    obtain ⟨hsub, hvol⟩ := hcond i
    have hvball_pos : 0 < volume.real (Metric.ball x (r i)) :=
      ENNReal.toReal_pos (measure_ball_pos volume x (hrpos i)).ne' measure_ball_ne_top
    have hE_top : volume (E i) ≠ ∞ :=
      ne_top_of_le_ne_top measure_ball_ne_top (measure_mono hsub)
    have hvol_real : α * volume.real (Metric.ball x (r i)) ≤ volume.real (E i) := by
      have h1 := ENNReal.toReal_mono hE_top hvol
      simpa [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hα.le] using h1
    have hvE_pos : 0 < volume.real (E i) :=
      lt_of_lt_of_le (mul_pos hα hvball_pos) hvol_real
    have hinv_le : (volume.real (E i))⁻¹ ≤ α⁻¹ * (volume.real (Metric.ball x (r i)))⁻¹ := by
      rw [← mul_inv]
      exact inv_anti₀ (mul_pos hα hvball_pos) hvol_real
    have hint_ball : IntegrableOn (fun y => ‖f y - f x‖) (Metric.ball x (r i)) volume := by
      have hf_b : IntegrableOn f (Metric.ball x (r i)) volume :=
        (hf.integrableOn_isCompact (isCompact_closedBall x (r i))).mono_set
          Metric.ball_subset_closedBall
      exact (hf_b.sub (integrableOn_const measure_ball_ne_top)).norm
    have hint_mono : ∫ y in E i, ‖f y - f x‖ ∂volume ≤
        ∫ y in Metric.ball x (r i), ‖f y - f x‖ ∂volume :=
      setIntegral_mono_set hint_ball (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall hsub)
    calc
      (volume.real (E i))⁻¹ * ∫ y in E i, ‖f y - f x‖ ∂volume
        ≤ (α⁻¹ * (volume.real (Metric.ball x (r i)))⁻¹) *
            ∫ y in Metric.ball x (r i), ‖f y - f x‖ ∂volume :=
          mul_le_mul hinv_le hint_mono (integral_nonneg fun _ => norm_nonneg _) (by positivity)
      _ = α⁻¹ * ((volume.real (Metric.ball x (r i)))⁻¹ *
            ∫ y in Metric.ball x (r i), ‖f y - f x‖ ∂volume) := by ring
  refine ⟨hE_osc, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) hE_osc
  obtain ⟨hsub, hvol⟩ := hcond i
  have hvball_pos : 0 < volume.real (Metric.ball x (r i)) :=
    ENNReal.toReal_pos (measure_ball_pos volume x (hrpos i)).ne' measure_ball_ne_top
  have hE_top : volume (E i) ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_ne_top (measure_mono hsub)
  have hvol_real : α * volume.real (Metric.ball x (r i)) ≤ volume.real (E i) := by
    have h1 := ENNReal.toReal_mono hE_top hvol
    simpa [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hα.le] using h1
  have hvE_pos : 0 < volume.real (E i) :=
    lt_of_lt_of_le (mul_pos hα hvball_pos) hvol_real
  have hint_f : IntegrableOn f (E i) volume :=
    (hf.integrableOn_isCompact (isCompact_closedBall x (r i))).mono_set
      (hsub.trans Metric.ball_subset_closedBall)
  have hint_c : IntegrableOn (fun _ => f x) (E i) volume := integrableOn_const hE_top
  have hconst : f x = (volume.real (E i))⁻¹ • ∫ _ in E i, f x ∂volume := by
    rw [setIntegral_const, smul_smul, inv_mul_cancel₀ hvE_pos.ne', one_smul]
  calc
    ‖(volume.real (E i))⁻¹ • ∫ y in E i, f y ∂volume - f x‖
      = ‖(volume.real (E i))⁻¹ • (∫ y in E i, f y ∂volume - ∫ _ in E i, f x ∂volume)‖ := by
        conv_lhs => rw [hconst, ← smul_sub]
    _ = (volume.real (E i))⁻¹ * ‖∫ y in E i, (f y - f x) ∂volume‖ := by
        rw [← integral_sub hint_f hint_c, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr hvE_pos.le)]
    _ ≤ (volume.real (E i))⁻¹ * ∫ y in E i, ‖f y - f x‖ ∂volume :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.mpr hvE_pos.le)

/-- 7.10: Associate to each `x ∈ ℝ^k` an arbitrary sequence `{E_i(x)}` that shrinks nicely to `x`
(with no cross-`x` compatibility required). If `f ∈ L¹(ℝ^k)`, then
`m(E_i(x))⁻¹ ∫_{E_i(x)} f dm → f(x)` at every Lebesgue point `x` of `f`, hence `m`-a.e. -/
theorem theorem_7_10 {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℂ} (hf : Integrable f volume)
    (E : EuclideanSpace ℝ (Fin k) → ℕ → Set (EuclideanSpace ℝ (Fin k)))
    (hE : ∀ x, ShrinksNicelyTo (E x) x) :
    (∀ x, IsLebesguePoint f x →
        Tendsto (fun i => (volume.real (E x i))⁻¹ • ∫ y in E x i, f y ∂volume)
          atTop (𝓝 (f x))) ∧
      ∀ᵐ x ∂volume,
        Tendsto (fun i => (volume.real (E x i))⁻¹ • ∫ y in E x i, f y ∂volume)
          atTop (𝓝 (f x)) := by
  have hpt : ∀ x, IsLebesguePoint f x →
      Tendsto (fun i => (volume.real (E x i))⁻¹ • ∫ y in E x i, f y ∂volume)
        atTop (𝓝 (f x)) :=
    fun x hx => (theorem_7_10_lebesguePoint hf.locallyIntegrable hx (hE x)).2
  refine ⟨hpt, ?_⟩
  filter_upwards [theorem_7_7 hf] with x hx using hpt x hx

end Node7_10

section Node7_11

/-- 7.11: Indefinite integral `F(x) = ∫_{(-∞, x)} f(t) dt` of `f ∈ L¹(ℝ; ℂ)`. -/
def indefiniteIntegralIio (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in Iio x, f t ∂volume

/-- 7.11 (every-Lebesgue-point form): if `f ∈ L¹(ℝ; ℂ)`, then `F(x) = ∫_{(-∞, x)} f(t) dt` has
derivative `F'(x) = f(x)` at *every* Lebesgue point `x` of `f`. -/
theorem theorem_7_11_lebesguePoint {f : ℝ → ℂ} (hf : Integrable f volume)
    {x : ℝ} (hx : IsLebesguePointReal f x) :
    HasDerivAt (indefiniteIntegralIio f) (f x) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2r_lim : Tendsto (fun y : ℝ => 2 * |y - x|) (𝓝[≠] x) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h1 : Tendsto (fun y : ℝ => 2 * |y - x|) (𝓝 x) (𝓝 (2 * |x - x|)) :=
        ((continuous_id.sub continuous_const).abs.const_mul 2).tendsto x
      simpa using h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y (hy : y ≠ x)
      exact mul_pos zero_lt_two (abs_pos.mpr (sub_ne_zero.mpr hy))
  have hosc : Tendsto (fun y : ℝ => 4 * ((volume.real (Metric.ball x (2 * |y - x|)))⁻¹ *
      ∫ t in Metric.ball x (2 * |y - x|), ‖f t - f x‖ ∂volume)) (𝓝[≠] x) (𝓝 0) := by
    simpa using (hx.comp h2r_lim).const_mul 4
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hosc
  filter_upwards [self_mem_nhdsWithin] with y (hy : y ≠ x)
  set r : ℝ := |y - x|
  have hr : 0 < r := abs_pos.mpr (sub_ne_zero.mpr hy)
  have hball_vol : volume.real (Metric.ball x (2 * r)) = 4 * r := by
    rw [Real.ball_eq_Ioo, Real.volume_real_Ioo,
      max_eq_left (by linarith : 0 ≤ x + 2 * r - (x - 2 * r))]
    ring
  have hint_ball : IntegrableOn (fun t => ‖f t - f x‖) (Metric.ball x (2 * r)) volume :=
    (hf.integrableOn.sub (integrableOn_const measure_ball_ne_top)).norm
  rcases lt_or_gt_of_ne hy with hlt | hgt
  · have hr_eq : r = x - y := by
      dsimp [r]
      rw [abs_of_neg (sub_neg.mpr hlt)]
      ring
    have hdiff : indefiniteIntegralIio f x - indefiniteIntegralIio f y =
        ∫ t in Ico y x, f t ∂volume := by
      unfold indefiniteIntegralIio
      have hunion : Iio y ∪ Ico y x = Iio x := Iio_union_Ico_eq_Iio hlt.le
      have hdisj : Disjoint (Iio y) (Ico y x) :=
        Set.disjoint_left.mpr fun t ht1 ht2 => not_le_of_gt ht1 ht2.1
      have hsplit : ∫ t in Iio x, f t ∂volume =
          ∫ t in Iio y, f t ∂volume + ∫ t in Ico y x, f t ∂volume := by
        rw [← hunion, setIntegral_union hdisj measurableSet_Ico hf.integrableOn hf.integrableOn]
      rw [hsplit, add_sub_cancel_left]
    have hslope : slope (indefiniteIntegralIio f) x y - f x =
        r⁻¹ • ∫ t in Ico y x, (f t - f x) ∂volume := by
      have hyx : y - x = -r := by linarith
      have hFy : indefiniteIntegralIio f y - indefiniteIntegralIio f x =
          -∫ t in Ico y x, f t ∂volume := by
        rw [← neg_sub, hdiff]
      have hconst : f x = r⁻¹ • ∫ _ in Ico y x, f x ∂volume := by
        rw [setIntegral_const, Real.volume_real_Ico, max_eq_left (sub_nonneg.mpr hlt.le),
          ← hr_eq, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
      rw [slope_def_module, hFy, hyx, inv_neg, neg_smul_neg]
      conv_lhs => rw [hconst, ← smul_sub]
      rw [← integral_sub hf.integrableOn
        (integrableOn_const (by simp [Real.volume_Ico]))]
    have hsub_ball : Ico y x ⊆ Metric.ball x (2 * r) := by
      intro t ht
      rw [Real.ball_eq_Ioo, mem_Ioo]
      simp only [mem_Ico] at ht
      exact ⟨by linarith, by linarith⟩
    calc
      ‖slope (indefiniteIntegralIio f) x y - f x‖
        = r⁻¹ * ‖∫ t in Ico y x, (f t - f x) ∂volume‖ := by
          rw [hslope, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      _ ≤ r⁻¹ * ∫ t in Ico y x, ‖f t - f x‖ ∂volume :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.mpr hr.le)
      _ ≤ r⁻¹ * ∫ t in Metric.ball x (2 * r), ‖f t - f x‖ ∂volume :=
          mul_le_mul_of_nonneg_left
            (setIntegral_mono_set hint_ball (Eventually.of_forall fun _ => norm_nonneg _)
              (Eventually.of_forall hsub_ball))
            (inv_nonneg.mpr hr.le)
      _ = 4 * ((volume.real (Metric.ball x (2 * r)))⁻¹ *
            ∫ t in Metric.ball x (2 * r), ‖f t - f x‖ ∂volume) := by
          rw [hball_vol]
          field_simp [hr.ne']
  · have hr_eq : r = y - x := abs_of_pos (sub_pos.mpr hgt)
    have hdiff : indefiniteIntegralIio f y - indefiniteIntegralIio f x =
        ∫ t in Ico x y, f t ∂volume := by
      unfold indefiniteIntegralIio
      have hunion : Iio x ∪ Ico x y = Iio y := Iio_union_Ico_eq_Iio hgt.le
      have hdisj : Disjoint (Iio x) (Ico x y) :=
        Set.disjoint_left.mpr fun t ht1 ht2 => not_le_of_gt ht1 ht2.1
      have hsplit : ∫ t in Iio y, f t ∂volume =
          ∫ t in Iio x, f t ∂volume + ∫ t in Ico x y, f t ∂volume := by
        rw [← hunion, setIntegral_union hdisj measurableSet_Ico hf.integrableOn hf.integrableOn]
      rw [hsplit, add_sub_cancel_left]
    have hslope : slope (indefiniteIntegralIio f) x y - f x =
        r⁻¹ • ∫ t in Ico x y, (f t - f x) ∂volume := by
      have hconst : f x = r⁻¹ • ∫ _ in Ico x y, f x ∂volume := by
        rw [setIntegral_const, Real.volume_real_Ico, max_eq_left (sub_nonneg.mpr hgt.le),
          ← hr_eq, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
      rw [slope_def_module, hdiff, ← hr_eq]
      conv_lhs => rw [hconst, ← smul_sub]
      rw [← integral_sub hf.integrableOn
        (integrableOn_const (by simp [Real.volume_Ico]))]
    have hsub_ball : Ico x y ⊆ Metric.ball x (2 * r) := by
      intro t ht
      rw [Real.ball_eq_Ioo, mem_Ioo]
      simp only [mem_Ico] at ht
      exact ⟨by linarith, by linarith⟩
    calc
      ‖slope (indefiniteIntegralIio f) x y - f x‖
        = r⁻¹ * ‖∫ t in Ico x y, (f t - f x) ∂volume‖ := by
          rw [hslope, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      _ ≤ r⁻¹ * ∫ t in Ico x y, ‖f t - f x‖ ∂volume :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.mpr hr.le)
      _ ≤ r⁻¹ * ∫ t in Metric.ball x (2 * r), ‖f t - f x‖ ∂volume :=
          mul_le_mul_of_nonneg_left
            (setIntegral_mono_set hint_ball (Eventually.of_forall fun _ => norm_nonneg _)
              (Eventually.of_forall hsub_ball))
            (inv_nonneg.mpr hr.le)
      _ = 4 * ((volume.real (Metric.ball x (2 * r)))⁻¹ *
            ∫ t in Metric.ball x (2 * r), ‖f t - f x‖ ∂volume) := by
          rw [hball_vol]
          field_simp [hr.ne']

/-- 7.11: If `f ∈ L¹(ℝ; ℂ)` and `F(x) = ∫_{(-∞, x)} f(t) dt`, then `F'(x) = f(x)` at every
Lebesgue point of `f`, hence almost everywhere on `ℝ`. -/
theorem theorem_7_11 {f : ℝ → ℂ} (hf : Integrable f volume) :
    (∀ x, IsLebesguePointReal f x → HasDerivAt (indefiniteIntegralIio f) (f x) x) ∧
      (∀ᵐ x ∂volume, HasDerivAt (indefiniteIntegralIio f) (f x) x) ∧
      deriv (indefiniteIntegralIio f) =ᵐ[volume] f := by
  have hpt : ∀ x, IsLebesguePointReal f x → HasDerivAt (indefiniteIntegralIio f) (f x) x :=
    fun _ hx => theorem_7_11_lebesguePoint hf hx
  have hae : ∀ᵐ x ∂volume, HasDerivAt (indefiniteIntegralIio f) (f x) x := by
    filter_upwards [ae_isLebesguePointReal hf] with x hx using hpt x hx
  refine ⟨hpt, hae, ?_⟩
  filter_upwards [hae] with x hx using hx.deriv

end Node7_11

section Node7_12

/-- 7.12: Metric density of a set `E ⊆ ℝ^k` at `x ∈ ℝ^k` equals `d` if
`m(E ∩ B(x, r)) / m(B(x, r)) → d` as `r → 0⁺`. -/
def HasMetricDensity {k : ℕ} (E : Set (EuclideanSpace ℝ (Fin k)))
    (x : EuclideanSpace ℝ (Fin k)) (d : ℝ) : Prop :=
  Tendsto (fun r => volume.real (E ∩ Metric.ball x r) / volume.real (Metric.ball x r))
    (𝓝[>] 0) (𝓝 d)

/-- 7.12 (1D metric density on `ℝ`). -/
def HasMetricDensityReal (E : Set ℝ) (x : ℝ) (d : ℝ) : Prop :=
  Tendsto (fun r => volume.real (E ∩ Metric.ball x r) / volume.real (Metric.ball x r))
    (𝓝[>] 0) (𝓝 d)

private theorem ae_tendsto_metricDensity_nullMeasurable {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasureSpace X] [BorelSpace X] [SecondCountableTopology X]
    [Measure.IsAddHaarMeasure (volume : Measure X)]
    {E : Set X} (hE : NullMeasurableSet E volume) :
    ∀ᵐ x ∂(volume : Measure X),
      Tendsto (fun r => volume.real (E ∩ Metric.ball x r) / volume.real (Metric.ball x r))
        (𝓝[>] 0) (𝓝 (E.indicator 1 x)) := by
  let B : Set X := toMeasurable volume E
  have hBm : MeasurableSet B := measurableSet_toMeasurable volume E
  have hBE : B =ᵐ[volume] E := hE.toMeasurable_ae_eq
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hBm,
    hBE] with x hx hxeq
  have hind : B.indicator (1 : X → ℝ≥0∞) x = ENNReal.ofReal (E.indicator (1 : X → ℝ) x) := by
    have hmem : x ∈ B ↔ x ∈ E := Eq.to_iff hxeq
    by_cases hxE : x ∈ E
    · have hxB : x ∈ B := hmem.mpr hxE
      simp [hxE, hxB]
    · have hxB : x ∉ B := fun h => hxE (hmem.mp h)
      simp [hxE, hxB]
  rw [hind] at hx
  have hreal := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hx
  have hnonneg : 0 ≤ E.indicator (1 : X → ℝ) x := by
    by_cases hxE : x ∈ E <;> simp [hxE]
  rw [ENNReal.toReal_ofReal hnonneg] at hreal
  refine hreal.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hball_ae : Metric.ball x r =ᵐ[volume] Metric.closedBall x r :=
    ball_ae_eq_closedBall_of_pos volume x hr
  have hinter_ae : (B ∩ Metric.closedBall x r : Set X) =ᵐ[volume] E ∩ Metric.ball x r :=
    hBE.inter hball_ae.symm
  simp only [Function.comp_apply, ENNReal.toReal_div, measureReal_def,
    measure_congr hinter_ae, measure_congr hball_ae.symm]

/-- 7.12: Lebesgue's metric density theorem — for every Lebesgue-measurable set `E ⊆ ℝ^k`
(`NullMeasurableSet E volume`, with no finite-measure assumption), the metric density of `E`
equals `1` at `m`-a.e. point of `E` and `0` at `m`-a.e. point of `Eᶜ`. -/
theorem theorem_7_12 {k : ℕ} {E : Set (EuclideanSpace ℝ (Fin k))}
    (hE : NullMeasurableSet E volume) :
    (∀ᵐ x ∂volume, HasMetricDensity E x (E.indicator 1 x)) ∧
      (∀ᵐ x ∂volume.restrict E, HasMetricDensity E x 1) ∧
      ∀ᵐ x ∂volume.restrict Eᶜ, HasMetricDensity E x 0 := by
  have hae : ∀ᵐ x ∂volume, HasMetricDensity E x (E.indicator 1 x) :=
    ae_tendsto_metricDensity_nullMeasurable hE
  refine ⟨hae, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae hae, self_mem_ae_restrict (μ := volume)
      (s := toMeasurable volume E) (measurableSet_toMeasurable _ _) |> fun _ =>
        ae_restrict_iff'₀ hE |>.mpr (Eventually.of_forall fun _ hx => hx)] with x hx hxE
    simpa [hxE] using hx
  · filter_upwards [ae_restrict_of_ae hae,
      (ae_restrict_iff'₀ hE.compl).mpr (Eventually.of_forall fun _ hx => hx)] with x hx hxEc
    have hnot : x ∉ E := hxEc
    simpa [hnot] using hx

/-- 7.12 (interval-density impossibility on `ℝ`): for every `ε > 0`, there is NO Lebesgue-measurable
set `E ⊆ ℝ` whose relative measure `m(E ∩ I) / m(I)` lies in `[ε, 1 - ε]` (let alone `(ε, 1 - ε)`)
for every nonempty bounded open interval `I = (a, b)`. -/
theorem theorem_7_12_no_uniform_interval_density {E : Set ℝ} (hE : NullMeasurableSet E volume)
    {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ a b : ℝ, a < b →
      ε ≤ volume.real (E ∩ Ioo a b) / (b - a) ∧
        volume.real (E ∩ Ioo a b) / (b - a) ≤ 1 - ε) :
    False := by
  by_cases hzero : volume E = 0
  · obtain ⟨hlow, _⟩ := hbound 0 1 zero_lt_one
    have hinter0 : volume (E ∩ Ioo 0 1) = 0 := measure_mono_null inter_subset_left hzero
    simp only [measureReal_def, hinter0, ENNReal.toReal_zero, sub_zero, div_one] at hlow
    linarith
  · have hae : ∀ᵐ x ∂volume.restrict E,
        Tendsto (fun r => volume.real (E ∩ Metric.ball x r) / volume.real (Metric.ball x r))
          (𝓝[>] 0) (𝓝 1) := by
      filter_upwards [ae_restrict_of_ae (ae_tendsto_metricDensity_nullMeasurable hE),
        (ae_restrict_iff'₀ hE).mpr (Eventually.of_forall fun _ hx => hx)] with x hx hxE
      simpa [hxE] using hx
    have : (ae (volume.restrict E)).NeBot := by
      rw [ae_neBot]
      simpa using hzero
    obtain ⟨x, hx⟩ := hae.exists
    have hgt : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        1 - ε < volume.real (E ∩ Metric.ball x r) / volume.real (Metric.ball x r) :=
      hx.eventually (Ioi_mem_nhds (by linarith))
    obtain ⟨r, hrpos, (hrx : 0 < r)⟩ := (hgt.and self_mem_nhdsWithin).exists
    have hball_eq : Metric.ball x r = Ioo (x - r) (x + r) := Real.ball_eq_Ioo x r
    have hv_eq : volume.real (Metric.ball x r) = (x + r) - (x - r) := by
      rw [hball_eq, Real.volume_real_Ioo, max_eq_left (by linarith)]
    rw [hv_eq, hball_eq] at hrpos
    have hhi := (hbound (x - r) (x + r) (by linarith)).2
    linarith

/-- 7.12 (strict printed display form): no Lebesgue-measurable `E ⊆ ℝ` satisfies
`ε < m(E ∩ I) / m(I) < 1 - ε` on every nonempty bounded open interval `I = (a, b)` (`ε > 0`). -/
theorem theorem_7_12_no_strict_interval_density {E : Set ℝ} (hE : NullMeasurableSet E volume)
    {ε : ℝ} (hε : 0 < ε) :
    ¬ ∀ a b : ℝ, a < b →
      ε < volume.real (E ∩ Ioo a b) / (b - a) ∧
        volume.real (E ∩ Ioo a b) / (b - a) < 1 - ε := by
  intro h
  exact theorem_7_12_no_uniform_interval_density hE hε fun a b hab =>
    ⟨(h a b hab).1.le, (h a b hab).2.le⟩

end Node7_12

/-! ## §7.13–7.15: Differentiation of singular and general Borel measures -/

section Node7_13

/-- Helper: if a locally finite positive Borel measure `ρ` on `ℝ^k` is singular with respect to
Lebesgue measure, then `ρ(B(x, r)) / m(B(x, r)) → 0` as `r → 0⁺` for `m`-a.e. `x`. -/
private theorem ae_tendsto_openBall_ratio_zero_of_singular {k : ℕ}
    {ρ : Measure (EuclideanSpace ℝ (Fin k))} [IsLocallyFiniteMeasure ρ]
    (hρ : ρ ⟂ₘ volume) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin k))),
      Tendsto (fun r => ρ (Metric.ball x r) / volume (Metric.ball x r)) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (EuclideanSpace ℝ (Fin k))))
    |>.ae_eventually_measure_zero_of_singular hρ] with x hx
  have hclosed : Tendsto (fun r => ρ (Metric.closedBall x r) / volume (Metric.closedBall x r))
      (𝓝[>] 0) (𝓝 0) :=
    hx.comp (Besicovitch.tendsto_filterAt volume x)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hclosed
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [← measure_closedBall_eq_ball_of_pos volume x hr]
  exact ENNReal.div_le_div_right (measure_mono Metric.ball_subset_closedBall) _

/-- 7.13: Let `μ` be a complex Borel measure on `ℝ^k` with `μ ⊥ m`. Then there is a Borel-null
exceptional set outside which `μ(E_i(x)) / m(E_i(x)) → 0` along *every* sequence `{E_i(x)}`
shrinking nicely to `x`; in particular `(Dμ)(x) = 0` for `m`-a.e. `x`. -/
theorem theorem_7_13 {k : ℕ} (μ : ComplexMeasure (EuclideanSpace ℝ (Fin k)))
    (hμ : μ ⟂ᵥ volume.toENNRealVectorMeasure) :
    (∀ᵐ x ∂volume, ∀ E : ℕ → Set (EuclideanSpace ℝ (Fin k)), ShrinksNicelyTo E x →
        Tendsto (fun i => (volume.real (E i))⁻¹ • μ (E i)) atTop (𝓝 0)) ∧
      (∀ E : EuclideanSpace ℝ (Fin k) → ℕ → Set (EuclideanSpace ℝ (Fin k)),
        (∀ x, ShrinksNicelyTo (E x) x) →
          ∀ᵐ x ∂volume,
            Tendsto (fun i => (volume.real (E x i))⁻¹ • μ (E x i)) atTop (𝓝 0)) ∧
      (∀ᵐ x ∂volume, HasSymmetricDeriv μ x 0) ∧
      symmetricDeriv μ =ᵐ[volume] 0 := by
  have hvar_sing : μ.variation ⟂ₘ volume := by
    have h := variations_mutuallySingular hμ
    rwa [variation_positive_extended volume] at h
  have hae_ball : ∀ᵐ x ∂volume,
      Tendsto (fun r => μ.variation.real (Metric.ball x r) / volume.real (Metric.ball x r))
        (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [ae_tendsto_openBall_ratio_zero_of_singular hvar_sing] with x hx
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hx
    simp only [ENNReal.toReal_zero] at hreal
    refine hreal.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r _
    simp [Function.comp_apply, ENNReal.toReal_div, measureReal_def]
  have hae_nice : ∀ᵐ x ∂volume, ∀ E : ℕ → Set (EuclideanSpace ℝ (Fin k)), ShrinksNicelyTo E x →
      Tendsto (fun i => (volume.real (E i))⁻¹ • μ (E i)) atTop (𝓝 0) := by
    filter_upwards [hae_ball] with x hx E hE
    obtain ⟨_, α, hα, r, hrpos, hrlim, hcond⟩ := hE
    have hr_gt : Tendsto r atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hrlim, Eventually.of_forall hrpos⟩
    have hdom : Tendsto (fun i => α⁻¹ *
        (μ.variation.real (Metric.ball x (r i)) / volume.real (Metric.ball x (r i))))
        atTop (𝓝 0) := by
      simpa using (hx.comp hr_gt).const_mul α⁻¹
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) hdom
    obtain ⟨hsub, hvol⟩ := hcond i
    have hvball_pos : 0 < volume.real (Metric.ball x (r i)) :=
      ENNReal.toReal_pos (measure_ball_pos volume x (hrpos i)).ne' measure_ball_ne_top
    have hE_top : volume (E i) ≠ ∞ :=
      ne_top_of_le_ne_top measure_ball_ne_top (measure_mono hsub)
    have hvol_real : α * volume.real (Metric.ball x (r i)) ≤ volume.real (E i) := by
      have h1 := ENNReal.toReal_mono hE_top hvol
      simpa [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hα.le] using h1
    have hvE_pos : 0 < volume.real (E i) :=
      lt_of_lt_of_le (mul_pos hα hvball_pos) hvol_real
    have hinv_le : (volume.real (E i))⁻¹ ≤ α⁻¹ * (volume.real (Metric.ball x (r i)))⁻¹ := by
      rw [← mul_inv]
      exact inv_anti₀ (mul_pos hα hvball_pos) hvol_real
    have hmu_le : ‖μ (E i)‖ ≤ μ.variation.real (Metric.ball x (r i)) := by
      have hen : ‖μ (E i)‖ₑ ≤ μ.variation (Metric.ball x (r i)) :=
        (μ.enorm_measure_le_variation (E i)).trans (measure_mono hsub)
      rw [← ofReal_norm] at hen
      have htr := ENNReal.toReal_mono (measure_ne_top μ.variation _) hen
      simpa [measureReal_def, ENNReal.toReal_ofReal (norm_nonneg _)] using htr
    simp only [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvE_pos)]
    calc
      (volume.real (E i))⁻¹ * ‖μ (E i)‖
        ≤ (α⁻¹ * (volume.real (Metric.ball x (r i)))⁻¹) *
            μ.variation.real (Metric.ball x (r i)) :=
          mul_le_mul hinv_le hmu_le (norm_nonneg _) (by positivity)
      _ = α⁻¹ * (μ.variation.real (Metric.ball x (r i)) /
            volume.real (Metric.ball x (r i))) := by
          rw [div_eq_mul_inv]
          ring
  have hae_symm : ∀ᵐ x ∂volume, HasSymmetricDeriv μ x 0 := by
    filter_upwards [hae_ball] with x hx
    rw [HasSymmetricDeriv, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hx
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have hvpos : 0 < volume.real (Metric.ball x r) :=
      ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_ne_top
    have hmu_le : ‖μ (Metric.ball x r)‖ ≤ μ.variation.real (Metric.ball x r) := by
      have hen : ‖μ (Metric.ball x r)‖ₑ ≤ μ.variation (Metric.ball x r) :=
        μ.enorm_measure_le_variation (Metric.ball x r)
      rw [← ofReal_norm] at hen
      have htr := ENNReal.toReal_mono (measure_ne_top μ.variation _) hen
      simpa [measureReal_def, ENNReal.toReal_ofReal (norm_nonneg _)] using htr
    rw [ballQuotient, sub_zero, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hvpos, div_eq_inv_mul, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hmu_le (inv_nonneg.mpr hvpos.le)
  refine ⟨hae_nice, ?_, hae_symm, ?_⟩
  · intro E hE
    filter_upwards [hae_nice] with x hx using hx (E x) (hE x)
  · filter_upwards [hae_symm] with x hx using hx.symmetricDeriv_eq

end Node7_13

section Node7_14

/-- 7.14: General complex Borel measure differentiation theorem on `ℝ^k`. Let
`dμ = dμ_s + f dm` be the Lebesgue decomposition of `μ` (`μ_s = μ.singularPart volume`,
`f = μ.rnDeriv volume ∈ L¹(m)`). Then:
1. For any assignment `x ↦ {E_i(x)}` of sequences shrinking nicely to `x`,
   `μ(E_i(x)) / m(E_i(x)) → f(x)` for `m`-a.e. `x`;
2. `(Dμ)(x) = f(x)` for `m`-a.e. `x`;
3. `μ ⊥ m` if and only if `Dμ = 0` `m`-a.e. -/
theorem theorem_7_14 {k : ℕ} (μ : ComplexMeasure (EuclideanSpace ℝ (Fin k))) :
    (∀ E : EuclideanSpace ℝ (Fin k) → ℕ → Set (EuclideanSpace ℝ (Fin k)),
        (∀ x, ShrinksNicelyTo (E x) x) →
          ∀ᵐ x ∂volume,
            Tendsto (fun i => (volume.real (E x i))⁻¹ • μ (E x i)) atTop
              (𝓝 (μ.rnDeriv volume x))) ∧
      (∀ᵐ x ∂volume, HasSymmetricDeriv μ x (μ.rnDeriv volume x)) ∧
      symmetricDeriv μ =ᵐ[volume] μ.rnDeriv volume ∧
      (μ ⟂ᵥ volume.toENNRealVectorMeasure ↔ symmetricDeriv μ =ᵐ[volume] 0) := by
  have hf : Integrable (μ.rnDeriv volume) volume := μ.integrable_rnDeriv volume
  have hsing : μ.singularPart volume ⟂ᵥ volume.toENNRealVectorMeasure :=
    complexMeasure_singularPart_mutuallySingular μ volume
  have hdecomp : μ.singularPart volume + volume.withDensityᵥ (μ.rnDeriv volume) = μ :=
    μ.singularPart_add_withDensity_rnDeriv_eq
  obtain ⟨h13_all, _, h13_symm, _⟩ := theorem_7_13 (μ.singularPart volume) hsing
  have hae_nice : ∀ E : EuclideanSpace ℝ (Fin k) → ℕ → Set (EuclideanSpace ℝ (Fin k)),
      (∀ x, ShrinksNicelyTo (E x) x) →
        ∀ᵐ x ∂volume,
          Tendsto (fun i => (volume.real (E x i))⁻¹ • μ (E x i)) atTop
            (𝓝 (μ.rnDeriv volume x)) := by
    intro E hE
    filter_upwards [h13_all, theorem_7_7 hf] with x hx_sing hx_leb
    obtain ⟨hEmeas, _⟩ := hE x
    have h_s := hx_sing (E x) (hE x)
    have h_ac := (theorem_7_10_lebesguePoint hf.locallyIntegrable hx_leb (hE x)).2
    have hsum := h_s.add h_ac
    rw [zero_add] at hsum
    refine hsum.congr fun i => ?_
    rw [← smul_add, ← withDensityᵥ_apply hf (hEmeas i), ← add_apply, hdecomp]
  have hae_symm : ∀ᵐ x ∂volume, HasSymmetricDeriv μ x (μ.rnDeriv volume x) := by
    filter_upwards [h13_symm, theorem_7_7 hf] with x hx_sing hx_leb
    have h_ac := hasSymmetricDeriv_withDensityᵥ_of_isLebesguePoint hf hx_leb
    have hsum := hx_sing.add h_ac
    rw [zero_add] at hsum
    refine hsum.congr fun r => ?_
    rw [ballQuotient, ballQuotient, ← add_div, ← add_apply, hdecomp, ballQuotient]
  have hae_eq : symmetricDeriv μ =ᵐ[volume] μ.rnDeriv volume := by
    filter_upwards [hae_symm] with x hx using hx.symmetricDeriv_eq
  refine ⟨hae_nice, hae_symm, hae_eq, ?_⟩
  constructor
  · intro hμsing
    exact (theorem_7_13 μ hμsing).2.2.2
  · intro hzero
    have hrn_zero : μ.rnDeriv volume =ᵐ[volume] 0 := hae_eq.symm.trans hzero
    have hwd_zero : volume.withDensityᵥ (μ.rnDeriv volume) = 0 := by
      have hcongr : volume.withDensityᵥ (μ.rnDeriv volume) =
          volume.withDensityᵥ (0 : EuclideanSpace ℝ (Fin k) → ℂ) :=
        WithDensityᵥEq.congr_ae hrn_zero
      simpa using hcongr
    have hmu_eq : μ = μ.singularPart volume := by
      simpa [hwd_zero] using hdecomp.symm
    exact hmu_eq ▸ hsing

end Node7_14

section Node7_15

/-- 7.15: If `μ` is *any* positive Borel measure on `ℝ^k` mutually singular with respect to
Lebesgue measure (`μ ⊥ m`, with no finiteness, σ-finiteness, or local-finiteness hypothesis added),
then `(Dμ)(x) = +∞` for `μ`-almost every `x ∈ ℝ^k`. -/
theorem theorem_7_15 {k : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin k)))
    (hμ : μ ⟂ₘ volume) :
    (∀ᵐ x ∂μ, HasSymmetricDerivPos μ x ∞) ∧
      symmetricDerivPos μ =ᵐ[μ] (fun _ => ∞) := by
  classical
  let U : Set (EuclideanSpace ℝ (Fin k)) :=
    {x | ∃ r : ℝ, 0 < r ∧ μ (Metric.ball x r) < ∞}
  have hUc : ∀ x ∉ U, HasSymmetricDerivPos μ x ∞ := by
    intro x hxU
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have htop : μ (Metric.ball x r) = ∞ := by
      by_contra hne
      exact hxU ⟨r, hr, lt_top_iff_ne_top.mpr hne⟩
    have hvtop : volume (Metric.ball x r) ≠ ∞ := measure_ball_ne_top
    rw [ballQuotientPos, htop, ENNReal.top_div_of_ne_top hvtop]
  have hwit : ∀ z : U, ∃ r : ℝ, 0 < r ∧ μ (Metric.ball (z : EuclideanSpace ℝ (Fin k)) r) < ∞ :=
    fun z => z.property
  choose rad hrad_pos hrad_fin using hwit
  let B : U → Set (EuclideanSpace ℝ (Fin k)) :=
    fun z => Metric.ball (z : EuclideanSpace ℝ (Fin k)) (rad z)
  have hU_eq : U = ⋃ z : U, B z := by
    apply Subset.antisymm
    · intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hrad_pos ⟨x, hx⟩)⟩
    · intro x hx
      obtain ⟨z, hxz⟩ := mem_iUnion.mp hx
      have hsub := Metric.mem_ball.mp hxz
      refine ⟨rad z - dist x z, sub_pos.mpr hsub, ?_⟩
      exact lt_of_le_of_lt (measure_mono (Metric.ball_subset_ball' (by linarith))) (hrad_fin z)
  obtain ⟨T, hTcount, hTcov⟩ :=
    TopologicalSpace.isOpen_iUnion_countable B (fun _ => Metric.isOpen_ball)
  have hU_T : U = ⋃ z ∈ T, B z := hU_eq.trans hTcov.symm
  have hB_null : ∀ z ∈ T, μ {x ∈ B z | ¬ HasSymmetricDerivPos μ x ∞} = 0 := by
    intro z _
    let μz : Measure (EuclideanSpace ℝ (Fin k)) := μ.restrict (B z)
    have : IsFiniteMeasure μz := ⟨by
      dsimp [μz, B]
      rw [Measure.restrict_apply_univ]
      exact hrad_fin z⟩
    have hvol_sing : (volume : Measure (EuclideanSpace ℝ (Fin k))) ⟂ₘ μz := by
      obtain ⟨S, hS, hμS, hvolS⟩ := hμ
      exact ⟨Sᶜ, hS.compl, hvolS,
        le_antisymm ((Measure.restrict_apply_le _ _).trans (by simp [hμS])) bot_le⟩
    have hae_zero : ∀ᵐ x ∂μz,
        Tendsto (fun s => volume (Metric.closedBall x s) / μz (Metric.closedBall x s))
          (𝓝[>] 0) (𝓝 0) := by
      filter_upwards [(Besicovitch.vitaliFamily μz).ae_eventually_measure_zero_of_singular
        hvol_sing] with x hx
      exact hx.comp (Besicovitch.tendsto_filterAt μz x)
    have hae_inf : ∀ᵐ x ∂μz, x ∈ B z → HasSymmetricDerivPos μ x ∞ := by
      filter_upwards [hae_zero] with x hx hxBz
      obtain ⟨δ, hδ, hball_sub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball x hxBz
      have hhalf : Tendsto (fun r : ℝ => r / 2) (𝓝[>] 0) (𝓝[>] 0) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · simpa using ((continuous_id.div_const (2 : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r) using half_pos hr
      have hscaled : Tendsto (fun r : ℝ => (2 : ℝ≥0∞) ^ k *
          (volume (Metric.closedBall x (r / 2)) / μz (Metric.closedBall x (r / 2))))
          (𝓝[>] 0) (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul (hx.comp hhalf)
          (Or.inr (ENNReal.pow_ne_top (by norm_num)))
      have hratio_zero : Tendsto (fun r : ℝ => volume (Metric.ball x r) / μ (Metric.ball x r))
          (𝓝[>] 0) (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscaled
          (Eventually.of_forall fun _ => bot_le) ?_
        filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
        have hr2 : 0 < r / 2 := half_pos hr.1
        have hcb_ball : Metric.closedBall x (r / 2) ⊆ Metric.ball x r :=
          Metric.closedBall_subset_ball (by linarith)
        have hball_Bz : Metric.ball x r ⊆ B z :=
          (Metric.ball_subset_ball hr.2.le).trans hball_sub
        have hμz_eq : μz (Metric.closedBall x (r / 2)) = μ (Metric.closedBall x (r / 2)) := by
          rw [Measure.restrict_apply measurableSet_closedBall,
            inter_eq_left.mpr (hcb_ball.trans hball_Bz)]
        have hμ_le : μz (Metric.closedBall x (r / 2)) ≤ μ (Metric.ball x r) := by
          rw [hμz_eq]
          exact measure_mono hcb_ball
        have hvol_eq : volume (Metric.ball x r) =
            (2 : ℝ≥0∞) ^ k * volume (Metric.closedBall x (r / 2)) := by
          have hr_two : r = 2 * (r / 2) := by ring
          conv_lhs => rw [hr_two]
          rw [measure_closedBall_eq_ball_of_pos volume x hr2,
            volume.addHaar_ball_mul_of_pos x (by norm_num : (0 : ℝ) < 2) (r / 2),
            volume.addHaar_ball_center x (r / 2), finrank_euclideanSpace_fin,
            ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
        calc
          volume (Metric.ball x r) / μ (Metric.ball x r)
            = ((2 : ℝ≥0∞) ^ k * volume (Metric.closedBall x (r / 2))) / μ (Metric.ball x r) := by
              rw [hvol_eq]
          _ ≤ ((2 : ℝ≥0∞) ^ k * volume (Metric.closedBall x (r / 2))) /
                μz (Metric.closedBall x (r / 2)) :=
              ENNReal.div_le_div_left hμ_le _
          _ = (2 : ℝ≥0∞) ^ k *
                (volume (Metric.closedBall x (r / 2)) / μz (Metric.closedBall x (r / 2))) := by
              simp only [div_eq_mul_inv, mul_assoc]
      have hinv : Tendsto (fun r : ℝ => (volume (Metric.ball x r) / μ (Metric.ball x r))⁻¹)
          (𝓝[>] 0) (𝓝 ∞) :=
        ENNReal.inv_zero ▸ tendsto_inv_iff.2 hratio_zero
      refine hinv.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      have hv0 : volume (Metric.ball x r) ≠ 0 := (measure_ball_pos volume x hr).ne'
      have hvtop : volume (Metric.ball x r) ≠ ∞ := measure_ball_ne_top
      simp only [ballQuotientPos, div_eq_mul_inv]
      rw [ENNReal.mul_inv (Or.inl hv0) (Or.inl hvtop), inv_inv, mul_comm]
    have hnull_μz : μz {x | x ∈ B z ∧ ¬ HasSymmetricDerivPos μ x ∞} = 0 := by
      have hae_not : ∀ᵐ x ∂μz, ¬ (x ∈ B z ∧ ¬ HasSymmetricDerivPos μ x ∞) := by
        filter_upwards [hae_inf] with x hx hcontr
        exact hcontr.2 (hx hcontr.1)
      simpa [ae_iff] using hae_not
    have hrestr : μ {x ∈ B z | ¬ HasSymmetricDerivPos μ x ∞} ≤
        μz {x | x ∈ B z ∧ ¬ HasSymmetricDerivPos μ x ∞} := by
      dsimp [μz]
      rw [Measure.restrict_apply' measurableSet_ball]
      apply measure_mono
      intro x hx
      exact ⟨⟨hx.1, hx.2⟩, hx.1⟩
    exact le_antisymm (hrestr.trans (le_of_eq hnull_μz)) bot_le
  have hae : ∀ᵐ x ∂μ, HasSymmetricDerivPos μ x ∞ := by
    rw [ae_iff]
    have hsub : {x | ¬ HasSymmetricDerivPos μ x ∞} ⊆
        ⋃ z ∈ T, {x ∈ B z | ¬ HasSymmetricDerivPos μ x ∞} := by
      intro x hx
      by_cases hxU : x ∈ U
      · rw [hU_T] at hxU
        obtain ⟨z, hzT, hxz⟩ := mem_iUnion₂.mp hxU
        exact mem_iUnion₂.mpr ⟨z, hzT, hxz, hx⟩
      · exact False.elim (hx (hUc x hxU))
    exact measure_mono_null hsub ((measure_biUnion_null_iff hTcount).mpr hB_null)
  refine ⟨hae, ?_⟩
  filter_upwards [hae] with x hx using hx.symmetricDerivPos_eq

end Node7_15

/-! ## §7.16–7.21: Absolute continuity and the Fundamental Theorem of Calculus -/

section Node7_16

/-- **Example 7.16(a)** (Rudin, p. 144): `f(x) = x^2 sin(x⁻²)` for `x ≠ 0` and `f(0) = 0`. -/
def oscillatingFTCExample (x : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ 2 * Real.sin (x⁻¹ ^ 2)

theorem oscillatingFTCExample_eq (x : ℝ) :
    oscillatingFTCExample x = x ^ 2 * Real.sin ((x ^ 2)⁻¹) := by
  by_cases hx : x = 0 <;> simp [oscillatingFTCExample, hx, inv_pow]

theorem hasDerivAt_oscillatingFTCExample_zero :
    HasDerivAt oscillatingFTCExample 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hcongr :
      (fun t : ℝ => t⁻¹ • (oscillatingFTCExample (0 + t) - oscillatingFTCExample 0)) =ᶠ[𝓝[≠] 0]
        fun t : ℝ => t * Real.sin ((t ^ 2)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    simp only [zero_add, oscillatingFTCExample_eq, sq, zero_mul, sub_zero, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ ht, one_mul]
  rw [tendsto_congr' hcongr, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_)
    (tendsto_norm_zero.mono_left nhdsWithin_le_nhds)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg t)
    (by simpa [Real.norm_eq_abs] using Real.abs_sin_le_one ((t ^ 2)⁻¹))

theorem hasDerivAt_oscillatingFTCExample_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt oscillatingFTCExample
      (2 * x * Real.sin ((x ^ 2)⁻¹) - 2 * x⁻¹ * Real.cos ((x ^ 2)⁻¹)) x := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x)
  have hinv : HasDerivAt (fun t : ℝ => (t ^ 2)⁻¹) (-(2 * x) / (x ^ 2) ^ 2) x :=
    hpow.fun_inv (pow_ne_zero 2 hx)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin ((t ^ 2)⁻¹))
      (Real.cos ((x ^ 2)⁻¹) * (-(2 * x) / (x ^ 2) ^ 2)) x := hinv.sin
  have hmul : HasDerivAt (fun t : ℝ => t ^ 2 * Real.sin ((t ^ 2)⁻¹))
      (2 * x * Real.sin ((x ^ 2)⁻¹) +
        x ^ 2 * (Real.cos ((x ^ 2)⁻¹) * (-(2 * x) / (x ^ 2) ^ 2))) x :=
    hpow.mul hsin
  have hsimp :
      2 * x * Real.sin ((x ^ 2)⁻¹) +
          x ^ 2 * (Real.cos ((x ^ 2)⁻¹) * (-(2 * x) / (x ^ 2) ^ 2)) =
        2 * x * Real.sin ((x ^ 2)⁻¹) - 2 * x⁻¹ * Real.cos ((x ^ 2)⁻¹) := by
    field_simp [hx]
    ring
  rw [hsimp] at hmul
  exact hmul.congr_of_eventuallyEq (Filter.Eventually.of_forall oscillatingFTCExample_eq)

theorem differentiable_oscillatingFTCExample :
    Differentiable ℝ oscillatingFTCExample := by
  intro x
  by_cases hx : x = 0
  · exact hx ▸ hasDerivAt_oscillatingFTCExample_zero.differentiableAt
  · exact (hasDerivAt_oscillatingFTCExample_of_ne_zero hx).differentiableAt

private theorem continuousOn_deriv_oscillatingFTCExample_Icc {α β : ℝ} (hα : 0 < α) :
    ContinuousOn (deriv oscillatingFTCExample) (Icc α β) := by
  have hcont : ContinuousOn
      (fun x : ℝ => 2 * x * Real.sin ((x ^ 2)⁻¹) - 2 * x⁻¹ * Real.cos ((x ^ 2)⁻¹)) (Icc α β) := by
    intro x hx
    have hx0 : x ≠ 0 := (hα.trans_le hx.1).ne'
    have hpow0 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
    refine ContinuousAt.continuousWithinAt ?_
    refine (((continuousAt_const.mul continuousAt_id).mul ?_).sub
      ((continuousAt_const.mul (continuousAt_inv₀ hx0)).mul ?_))
    · exact Real.continuous_sin.continuousAt.comp ((continuous_pow 2).continuousAt.inv₀ hpow0)
    · exact Real.continuous_cos.continuousAt.comp ((continuous_pow 2).continuousAt.inv₀ hpow0)
  refine hcont.congr fun x hx => ?_
  exact (hasDerivAt_oscillatingFTCExample_of_ne_zero (hα.trans_le hx.1).ne').deriv

/-- **Example 7.16(a)** (Rudin, p. 144): `oscillatingFTCExample` is differentiable at every point
of `ℝ`, yet `deriv oscillatingFTCExample` fails to be Lebesgue integrable on `[0, δ]` for every
`δ > 0` (in particular on `[0, 1]`). -/
theorem example_7_16a :
    Differentiable ℝ oscillatingFTCExample ∧
      (∀ δ : ℝ, 0 < δ → ¬ IntegrableOn (deriv oscillatingFTCExample) (Icc 0 δ) volume) ∧
      ¬ IntegrableOn (deriv oscillatingFTCExample) (Icc 0 1) volume ∧
      ¬ IntervalIntegrable (deriv oscillatingFTCExample) volume 0 1 := by
  have hnot : ∀ δ : ℝ, 0 < δ → ¬ IntegrableOn (deriv oscillatingFTCExample) (Icc 0 δ) volume := by
    intro δ hδ hint
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((2 * Real.pi * δ ^ 2)⁻¹)
    have hpi : 0 < Real.pi := Real.pi_pos
    have h2pi : 0 < 2 * Real.pi := by positivity
    let aPt : ℕ → ℝ := fun m => Real.sqrt ((2 * Real.pi * ((m : ℝ) + 1) + Real.pi / 2)⁻¹)
    let bPt : ℕ → ℝ := fun m => Real.sqrt ((2 * Real.pi * ((m : ℝ) + 1))⁻¹)
    have hden_b_pos : ∀ m : ℕ, 0 < 2 * Real.pi * ((m : ℝ) + 1) := fun m => by positivity
    have hden_a_pos : ∀ m : ℕ, 0 < 2 * Real.pi * ((m : ℝ) + 1) + Real.pi / 2 := fun m => by
      positivity
    have ha_pos : ∀ m : ℕ, 0 < aPt m := fun m => Real.sqrt_pos.mpr (inv_pos.mpr (hden_a_pos m))
    have ha_lt_b : ∀ m : ℕ, aPt m < bPt m := by
      intro m
      apply Real.sqrt_lt_sqrt (by positivity)
      exact inv_strictAnti₀ (hden_b_pos m) (by linarith)
    have hb_succ_lt_a : ∀ m : ℕ, bPt (m + 1) < aPt m := by
      intro m
      apply Real.sqrt_lt_sqrt (by positivity)
      apply inv_strictAnti₀ (hden_a_pos m)
      push_cast
      linarith
    have hb_anti : ∀ {m₁ m₂ : ℕ}, m₁ < m₂ → bPt m₂ ≤ aPt m₁ := by
      intro m₁ m₂ hm
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hm
      clear hm
      induction d with
      | zero => exact (hb_succ_lt_a m₁).le
      | succ d ih =>
          have hstep : bPt (m₁ + (d + 1) + 1) ≤ bPt (m₁ + d + 1) :=
            ((hb_succ_lt_a (m₁ + d + 1)).trans (ha_lt_b (m₁ + d + 1))).le
          exact hstep.trans ih
    have hb_le_δ : ∀ k : ℕ, bPt (n₀ + k) ≤ δ := by
      intro k
      have h1 : (2 * Real.pi * δ ^ 2)⁻¹ ≤ (n₀ : ℝ) + (k : ℝ) + 1 := by
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      have h4 : (2 * Real.pi * (((n₀ + k : ℕ) : ℝ) + 1))⁻¹ ≤ δ ^ 2 := by
        rw [inv_le_comm₀ (hden_b_pos (n₀ + k)) (sq_pos_of_pos hδ)]
        calc
          (δ ^ 2)⁻¹ = 2 * Real.pi * (2 * Real.pi * δ ^ 2)⁻¹ := by
            field_simp [h2pi.ne', pow_ne_zero 2 hδ.ne']
          _ ≤ 2 * Real.pi * (((n₀ + k : ℕ) : ℝ) + 1) := by
            refine mul_le_mul_of_nonneg_left ?_ h2pi.le
            push_cast
            exact h1
      simpa [bPt, Real.sqrt_sq hδ.le] using Real.sqrt_le_sqrt h4
    have hIoc_sub : ∀ k : ℕ, Ioc (aPt (n₀ + k)) (bPt (n₀ + k)) ⊆ Icc 0 δ := by
      intro k x hx
      exact ⟨((ha_pos (n₀ + k)).trans hx.1).le, hx.2.trans (hb_le_δ k)⟩
    have hdisj : Pairwise fun k₁ k₂ : ℕ =>
        Disjoint (Ioc (aPt (n₀ + k₁)) (bPt (n₀ + k₁)))
          (Ioc (aPt (n₀ + k₂)) (bPt (n₀ + k₂))) := by
      intro k₁ k₂ hk
      rw [Set.disjoint_left]
      intro x hx1 hx2
      rcases lt_or_gt_of_ne hk with hlt | hgt
      · exact not_lt.mpr (hx2.2.trans (hb_anti (Nat.add_lt_add_left hlt n₀))) hx1.1
      · exact not_lt.mpr (hx1.2.trans (hb_anti (Nat.add_lt_add_left hgt n₀))) hx2.1
    have hval_b : ∀ m : ℕ, oscillatingFTCExample (bPt m) = 0 := by
      intro m
      rw [oscillatingFTCExample_eq]
      have hsq : bPt m ^ 2 = (2 * Real.pi * ((m : ℝ) + 1))⁻¹ :=
        Real.sq_sqrt (inv_nonneg.mpr (hden_b_pos m).le)
      have hsin : Real.sin ((bPt m ^ 2)⁻¹) = 0 := by
        rw [hsq, inv_inv]
        have heq : 2 * Real.pi * ((m : ℝ) + 1) = 0 + ((m + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
          push_cast; ring
        rw [heq, Real.sin_add_nat_mul_two_pi, Real.sin_zero]
      rw [hsin, mul_zero]
    have hval_a : ∀ m : ℕ,
        oscillatingFTCExample (aPt m) = (2 * Real.pi * ((m : ℝ) + 1) + Real.pi / 2)⁻¹ := by
      intro m
      rw [oscillatingFTCExample_eq]
      have hsq : aPt m ^ 2 = (2 * Real.pi * ((m : ℝ) + 1) + Real.pi / 2)⁻¹ :=
        Real.sq_sqrt (inv_nonneg.mpr (hden_a_pos m).le)
      have hsin : Real.sin ((aPt m ^ 2)⁻¹) = 1 := by
        rw [hsq, inv_inv]
        have heq : 2 * Real.pi * ((m : ℝ) + 1) + Real.pi / 2 =
            Real.pi / 2 + ((m + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
          push_cast; ring
        rw [heq, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
      rw [hsin, hsq, mul_one]
    have hpiece : ∀ m : ℕ,
        ENNReal.ofReal ((2 * Real.pi * ((m : ℝ) + 1) + Real.pi / 2)⁻¹) ≤
          ∫⁻ x in Ioc (aPt m) (bPt m), ‖deriv oscillatingFTCExample x‖ₑ ∂volume := by
      intro m
      have hab : aPt m ≤ bPt m := (ha_lt_b m).le
      have hftc : ∫ x in aPt m..bPt m, deriv oscillatingFTCExample x =
          oscillatingFTCExample (bPt m) - oscillatingFTCExample (aPt m) :=
        intervalIntegral.integral_deriv_eq_sub' oscillatingFTCExample rfl
          (fun x _ => differentiable_oscillatingFTCExample x)
          (uIcc_of_le hab ▸ continuousOn_deriv_oscillatingFTCExample_Icc (ha_pos m))
      rw [intervalIntegral.integral_of_le hab, hval_b m, hval_a m, zero_sub] at hftc
      have hnorm :
          ENNReal.ofReal ((2 * Real.pi * ((m : ℝ) + 1) + Real.pi / 2)⁻¹) =
            ‖∫ x in Ioc (aPt m) (bPt m), deriv oscillatingFTCExample x‖ₑ := by
        rw [hftc, enorm_neg, Real.enorm_eq_ofReal_abs,
          abs_of_pos (inv_pos.mpr (hden_a_pos m))]
      rw [hnorm]
      exact enorm_integral_le_lintegral_enorm _
    let C : ℝ≥0∞ := ∫⁻ x in Icc 0 δ, ‖deriv oscillatingFTCExample x‖ₑ ∂volume
    have hC_lt_top : C < ∞ := hint.2
    have hsum_le : ∀ N : ℕ,
        ∑ k ∈ Finset.range N,
            (2 * Real.pi * (((n₀ + k : ℕ) : ℝ) + 1) + Real.pi / 2)⁻¹ ≤ C.toReal := by
      intro N
      have henn :
          ENNReal.ofReal
              (∑ k ∈ Finset.range N,
                (2 * Real.pi * (((n₀ + k : ℕ) : ℝ) + 1) + Real.pi / 2)⁻¹) ≤ C := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => inv_nonneg.mpr (hden_a_pos (n₀ + k)).le)]
        calc
          ∑ k ∈ Finset.range N,
              ENNReal.ofReal ((2 * Real.pi * (((n₀ + k : ℕ) : ℝ) + 1) + Real.pi / 2)⁻¹)
            ≤ ∑ k ∈ Finset.range N,
                ∫⁻ x in Ioc (aPt (n₀ + k)) (bPt (n₀ + k)),
                  ‖deriv oscillatingFTCExample x‖ₑ ∂volume :=
              Finset.sum_le_sum fun k _ => hpiece (n₀ + k)
          _ = ∫⁻ x in ⋃ k ∈ Finset.range N, Ioc (aPt (n₀ + k)) (bPt (n₀ + k)),
                ‖deriv oscillatingFTCExample x‖ₑ ∂volume := by
              symm
              exact lintegral_biUnion_finset
                (fun k₁ _ k₂ _ hk => hdisj hk) (fun _ _ => measurableSet_Ioc) _
          _ ≤ C := lintegral_mono_set (iUnion₂_subset fun k _ => hIoc_sub k)
      exact (ENNReal.ofReal_le_iff_le_toReal hC_lt_top.ne).mp henn
    have hsumm : Summable
        (fun k : ℕ => (2 * Real.pi * (((n₀ + k : ℕ) : ℝ) + 1) + Real.pi / 2)⁻¹) :=
      summable_of_sum_range_le (fun k => inv_nonneg.mpr (hden_a_pos (n₀ + k)).le) hsum_le
    have hcomp : Summable (fun k : ℕ => (2 * Real.pi)⁻¹ * (1 / ((k + (n₀ + 2) : ℕ) : ℝ))) := by
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hsumm
      have hden_le :
          2 * Real.pi * (((n₀ + k : ℕ) : ℝ) + 1) + Real.pi / 2 ≤
            2 * Real.pi * ((k + (n₀ + 2) : ℕ) : ℝ) := by
        push_cast; linarith
      have hinv_le := inv_anti₀ (hden_a_pos (n₀ + k)) hden_le
      simpa [one_div, mul_inv_rev, mul_comm] using hinv_le
    have hshift : Summable (fun k : ℕ => 1 / ((k + (n₀ + 2) : ℕ) : ℝ)) := by
      have h1 := hcomp.mul_left (2 * Real.pi)
      refine h1.congr fun k => ?_
      field_simp [h2pi.ne']
    exact Real.not_summable_one_div_natCast ((_root_.summable_nat_add_iff (n₀ + 2)).mp hshift)
  refine ⟨differentiable_oscillatingFTCExample, hnot, hnot 1 zero_lt_one, ?_⟩
  intro hint
  exact hnot 1 zero_lt_one
    ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hint)

/-- Stage-`n` piecewise-linear approximation to the Cantor–Lebesgue staircase on `ℝ`. -/
def cantorApprox : ℕ → ℝ → ℝ
  | 0, x => max 0 (min 1 x)
  | n + 1, x =>
      if x ≤ 1 / 3 then (1 / 2) * cantorApprox n (3 * x)
      else if x ≤ 2 / 3 then 1 / 2
      else 1 / 2 + (1 / 2) * cantorApprox n (3 * x - 2)

private theorem cantorApprox_succ (n : ℕ) (x : ℝ) :
    cantorApprox (n + 1) x =
      if x ≤ 1 / 3 then (1 / 2) * cantorApprox n (3 * x)
      else if x ≤ 2 / 3 then 1 / 2
      else 1 / 2 + (1 / 2) * cantorApprox n (3 * x - 2) := rfl

private theorem cantorApprox_of_nonpos (n : ℕ) {x : ℝ} (hx : x ≤ 0) :
    cantorApprox n x = 0 := by
  induction n generalizing x with
  | zero =>
      simp [cantorApprox, min_eq_right (hx.trans zero_le_one), max_eq_left hx]
  | succ n ih =>
      have h1 : x ≤ 1 / 3 := by linarith
      have h3 : 3 * x ≤ 0 := by linarith
      rw [cantorApprox_succ, ite_eq_left h1, ih h3, mul_zero]

private theorem cantorApprox_of_one_le (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    cantorApprox n x = 1 := by
  induction n generalizing x with
  | zero =>
      simp [cantorApprox, min_eq_left hx]
  | succ n ih =>
      have h1 : ¬ x ≤ 1 / 3 := by linarith
      have h2 : ¬ x ≤ 2 / 3 := by linarith
      have h3 : 1 ≤ 3 * x - 2 := by linarith
      rw [cantorApprox_succ, ite_eq_right h1, ite_eq_right h2, ih h3]
      norm_num

private theorem cantorApprox_mem_Icc (n : ℕ) (x : ℝ) :
    cantorApprox n x ∈ Icc (0 : ℝ) 1 := by
  induction n generalizing x with
  | zero =>
      refine ⟨le_max_left 0 _, max_le zero_le_one (min_le_left 1 x)⟩
  | succ n ih =>
      simp only [cantorApprox]
      split_ifs with h1 h2
      · obtain ⟨hlo, hhi⟩ := ih (3 * x)
        exact ⟨by linarith, by linarith⟩
      · exact ⟨by norm_num, by norm_num⟩
      · obtain ⟨hlo, hhi⟩ := ih (3 * x - 2)
        exact ⟨by linarith, by linarith⟩

private theorem monotone_cantorApprox (n : ℕ) : Monotone (cantorApprox n) := by
  induction n with
  | zero =>
      intro x y hxy
      exact max_le_max_left 0 (min_le_min_left 1 hxy)
  | succ n ih =>
      intro x y hxy
      simp only [cantorApprox]
      split_ifs with hx1 hy1 hy2 hx2 hy2'
      · exact mul_le_mul_of_nonneg_left (ih (by linarith)) (by norm_num)
      · have hhi := (cantorApprox_mem_Icc n (3 * x)).2
        linarith
      · have hhi := (cantorApprox_mem_Icc n (3 * x)).2
        have hlo := (cantorApprox_mem_Icc n (3 * y - 2)).1
        linarith
      · linarith
      · exact le_rfl
      · have hlo := (cantorApprox_mem_Icc n (3 * y - 2)).1
        linarith
      · linarith
      · linarith
      · linarith [ih (show 3 * x - 2 ≤ 3 * y - 2 by linarith)]

private theorem continuous_cantorApprox (n : ℕ) : Continuous (cantorApprox n) := by
  induction n with
  | zero =>
      exact continuous_const.max (continuous_const.min continuous_id)
  | succ n ih =>
      let g : ℝ → ℝ := fun x =>
        if x ≤ 2 / 3 then (1 / 2 : ℝ) else 1 / 2 + (1 / 2) * cantorApprox n (3 * x - 2)
      have hg : Continuous g := by
        refine continuous_const.if_le
          (continuous_const.add
            (continuous_const.mul (ih.comp ((continuous_const.mul continuous_id).sub continuous_const))))
          continuous_id continuous_const fun x hx => ?_
        rw [hx]
        have h0 : (3 : ℝ) * (2 / 3) - 2 ≤ 0 := by norm_num
        rw [cantorApprox_of_nonpos n h0]
        norm_num
      refine (continuous_const.mul (ih.comp (continuous_const.mul continuous_id))).if_le
        hg continuous_id continuous_const fun x hx => ?_
      have hle : (1 / 3 : ℝ) ≤ 2 / 3 := by norm_num
      have h1 : (1 : ℝ) ≤ 3 * (1 / 3) := by norm_num
      change (1 / 2 : ℝ) * cantorApprox n (3 * x) = g x
      rw [hx, cantorApprox_of_one_le n h1]
      dsimp only [g]
      rw [ite_eq_left hle]
      norm_num

private theorem dist_cantorApprox_succ_le (n : ℕ) (x : ℝ) :
    dist (cantorApprox n x) (cantorApprox (n + 1) x) ≤ (1 : ℝ) / 2 / 2 ^ n := by
  induction n generalizing x with
  | zero =>
      rw [Real.dist_eq, pow_zero, div_one]
      by_cases hx0 : x ≤ 0
      · rw [cantorApprox_of_nonpos 0 hx0, cantorApprox_of_nonpos 1 hx0]
        norm_num
      push Not at hx0
      by_cases hx1 : x ≤ 1 / 3
      · have hc0 : cantorApprox 0 x = x := by
          simp [cantorApprox, min_eq_right (by linarith : x ≤ 1), max_eq_right hx0.le]
        have hc1 : cantorApprox 1 x = (1 / 2) * cantorApprox 0 (3 * x) := by
          rw [cantorApprox_succ, ite_eq_left hx1]
        obtain ⟨hlo, hhi⟩ := cantorApprox_mem_Icc 0 (3 * x)
        rw [hc0, hc1, abs_le]
        exact ⟨by linarith, by linarith⟩
      push Not at hx1
      by_cases hx2 : x ≤ 2 / 3
      · have hc0 : cantorApprox 0 x = x := by
          simp [cantorApprox, min_eq_right (by linarith : x ≤ 1), max_eq_right hx0.le]
        have hc1 : cantorApprox 1 x = 1 / 2 := by
          rw [cantorApprox_succ, ite_eq_right (not_le.mpr hx1), ite_eq_left hx2]
        rw [hc0, hc1, abs_le]
        exact ⟨by linarith, by linarith⟩
      push Not at hx2
      by_cases hx3 : x ≤ 1
      · have hc0 : cantorApprox 0 x = x := by
          simp [cantorApprox, min_eq_right hx3, max_eq_right hx0.le]
        have hc1 : cantorApprox 1 x = 1 / 2 + (1 / 2) * cantorApprox 0 (3 * x - 2) := by
          rw [cantorApprox_succ, ite_eq_right (by linarith), ite_eq_right (not_le.mpr hx2)]
        obtain ⟨hlo, hhi⟩ := cantorApprox_mem_Icc 0 (3 * x - 2)
        rw [hc0, hc1, abs_le]
        exact ⟨by linarith, by linarith⟩
      · push Not at hx3
        rw [cantorApprox_of_one_le 0 hx3.le, cantorApprox_of_one_le 1 hx3.le]
        norm_num
  | succ n ih =>
      rw [Real.dist_eq, cantorApprox_succ n x, cantorApprox_succ (n + 1) x]
      split_ifs with h1 h2
      · have hsub :
            |(1 / 2 : ℝ) * cantorApprox n (3 * x) - (1 / 2) * cantorApprox (n + 1) (3 * x)| =
              (1 / 2) * dist (cantorApprox n (3 * x)) (cantorApprox (n + 1) (3 * x)) := by
          rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), Real.dist_eq]
        rw [hsub]
        calc
          (1 / 2 : ℝ) * dist (cantorApprox n (3 * x)) (cantorApprox (n + 1) (3 * x))
            ≤ (1 / 2) * ((1 / 2) / 2 ^ n) :=
              mul_le_mul_of_nonneg_left (ih (3 * x)) (by norm_num)
          _ = 1 / 2 / 2 ^ (n + 1) := by ring
      · rw [sub_self, abs_zero]
        positivity
      · have hsub :
            |(1 / 2 + (1 / 2 : ℝ) * cantorApprox n (3 * x - 2)) -
                (1 / 2 + (1 / 2) * cantorApprox (n + 1) (3 * x - 2))| =
              (1 / 2) * dist (cantorApprox n (3 * x - 2)) (cantorApprox (n + 1) (3 * x - 2)) := by
          have heq :
              (1 / 2 + (1 / 2 : ℝ) * cantorApprox n (3 * x - 2)) -
                (1 / 2 + (1 / 2) * cantorApprox (n + 1) (3 * x - 2)) =
              (1 / 2) * (cantorApprox n (3 * x - 2) - cantorApprox (n + 1) (3 * x - 2)) := by ring
          rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), Real.dist_eq]
        rw [hsub]
        calc
          (1 / 2 : ℝ) * dist (cantorApprox n (3 * x - 2)) (cantorApprox (n + 1) (3 * x - 2))
            ≤ (1 / 2) * ((1 / 2) / 2 ^ n) :=
              mul_le_mul_of_nonneg_left (ih (3 * x - 2)) (by norm_num)
          _ = 1 / 2 / 2 ^ (n + 1) := by ring

/-- **Example 7.16(b)** (Rudin, pp. 144–145): the Cantor–Lebesgue singular function on `ℝ`,
extended by `0` on `(-∞, 0]` and `1` on `[1, ∞)`. -/
def cantorFun (x : ℝ) : ℝ :=
  limUnder atTop (fun n => cantorApprox n x)

private theorem tendsto_cantorApprox (x : ℝ) :
    Tendsto (fun n => cantorApprox n x) atTop (𝓝 (cantorFun x)) := by
  have hcau : CauchySeq (fun n => cantorApprox n x) :=
    cauchySeq_of_le_geometric_two (C := 1) (fun n => dist_cantorApprox_succ_le n x)
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcau
  simpa [cantorFun, hy.limUnder_eq] using hy

private theorem dist_cantorApprox_cantorFun_le (n : ℕ) (x : ℝ) :
    dist (cantorApprox n x) (cantorFun x) ≤ 1 / 2 ^ n := by
  simpa using dist_le_of_le_geometric_two_of_tendsto (C := 1)
    (fun k => dist_cantorApprox_succ_le k x) (tendsto_cantorApprox x) n

theorem continuous_cantorFun : Continuous cantorFun := by
  have hunif : TendstoUniformly cantorApprox cantorFun atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hpow : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
      simpa [one_div, inv_pow] using
        tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    filter_upwards [(tendsto_order.mp hpow).2 ε hε] with n hn x
    rw [dist_comm]
    exact (dist_cantorApprox_cantorFun_le n x).trans_lt hn
  exact hunif.continuous (Filter.Eventually.of_forall continuous_cantorApprox).frequently

theorem monotone_cantorFun : Monotone cantorFun := by
  intro x y hxy
  exact le_of_tendsto_of_tendsto (tendsto_cantorApprox x) (tendsto_cantorApprox y)
    (Filter.Eventually.of_forall fun n => monotone_cantorApprox n hxy)

theorem cantorFun_of_nonpos {x : ℝ} (hx : x ≤ 0) : cantorFun x = 0 := by
  have h := tendsto_cantorApprox x
  simp_rw [cantorApprox_of_nonpos _ hx] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem cantorFun_of_one_le {x : ℝ} (hx : 1 ≤ x) : cantorFun x = 1 := by
  have h := tendsto_cantorApprox x
  simp_rw [cantorApprox_of_one_le _ hx] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

@[simp] theorem cantorFun_zero : cantorFun 0 = 0 := cantorFun_of_nonpos le_rfl
@[simp] theorem cantorFun_one : cantorFun 1 = 1 := cantorFun_of_one_le le_rfl

private theorem cantorFun_left {x : ℝ} (hx : x ≤ 1 / 3) :
    cantorFun x = (1 / 2) * cantorFun (3 * x) := by
  have h1 : Tendsto (fun n => cantorApprox (n + 1) x) atTop (𝓝 (cantorFun x)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_cantorApprox x)
  have h2 : Tendsto (fun n => (1 / 2 : ℝ) * cantorApprox n (3 * x)) atTop
      (𝓝 ((1 / 2) * cantorFun (3 * x))) :=
    tendsto_const_nhds.mul (tendsto_cantorApprox (3 * x))
  have heq : (fun n => cantorApprox (n + 1) x) = fun n => (1 / 2 : ℝ) * cantorApprox n (3 * x) := by
    ext n; rw [cantorApprox_succ, ite_eq_left hx]
  exact tendsto_nhds_unique h1 (heq ▸ h2)

private theorem cantorFun_mid {x : ℝ} (hx1 : 1 / 3 < x) (hx2 : x ≤ 2 / 3) :
    cantorFun x = 1 / 2 := by
  have h1 : Tendsto (fun n => cantorApprox (n + 1) x) atTop (𝓝 (cantorFun x)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_cantorApprox x)
  have hnot : ¬ x ≤ 1 / 3 := not_le.mpr hx1
  have heq : (fun n => cantorApprox (n + 1) x) = fun _ => (1 / 2 : ℝ) := by
    ext n; rw [cantorApprox_succ, ite_eq_right hnot, ite_eq_left hx2]
  exact tendsto_nhds_unique h1 (heq ▸ tendsto_const_nhds)

private theorem cantorFun_right {x : ℝ} (hx : 2 / 3 < x) :
    cantorFun x = 1 / 2 + (1 / 2) * cantorFun (3 * x - 2) := by
  have h1 : Tendsto (fun n => cantorApprox (n + 1) x) atTop (𝓝 (cantorFun x)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_cantorApprox x)
  have h2 : Tendsto (fun n => (1 / 2 : ℝ) + (1 / 2) * cantorApprox n (3 * x - 2)) atTop
      (𝓝 (1 / 2 + (1 / 2) * cantorFun (3 * x - 2))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_cantorApprox (3 * x - 2)))
  have hnot1 : ¬ x ≤ 1 / 3 := by linarith
  have hnot2 : ¬ x ≤ 2 / 3 := not_le.mpr hx
  have heq : (fun n => cantorApprox (n + 1) x) =
      fun n => (1 / 2 : ℝ) + (1 / 2) * cantorApprox n (3 * x - 2) := by
    ext n; rw [cantorApprox_succ, ite_eq_right hnot1, ite_eq_right hnot2]
  exact tendsto_nhds_unique h1 (heq ▸ h2)

/-- Stage-`n` closed middle-thirds Cantor stage `E_n ⊆ [0, 1]`. -/
def cantorStage : ℕ → Set ℝ
  | 0 => Icc 0 1
  | n + 1 =>
      ((fun x : ℝ => 3 * x) ⁻¹' cantorStage n) ∪
        ((fun x : ℝ => 3 * x - 2) ⁻¹' cantorStage n)

/-- The middle-thirds Cantor compact null set `C = ⋂_n E_n ⊆ [0, 1]`. -/
def cantorSet : Set ℝ :=
  ⋂ n : ℕ, cantorStage n

private theorem cantorStage_subset_Icc (n : ℕ) : cantorStage n ⊆ Icc (0 : ℝ) 1 := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih =>
      intro x hx
      rcases hx with hL | hR
      · obtain ⟨h0, h1⟩ := ih hL
        exact ⟨by linarith, by linarith⟩
      · obtain ⟨h0, h1⟩ := ih hR
        exact ⟨by linarith, by linarith⟩

private theorem cantorStage_antitone : Antitone cantorStage := by
  refine antitone_nat_of_succ_le fun n => ?_
  induction n with
  | zero => exact cantorStage_subset_Icc 1
  | succ n ih =>
      intro x hx
      rcases hx with hL | hR
      · exact Or.inl (ih hL)
      · exact Or.inr (ih hR)

private theorem isClosed_cantorStage (n : ℕ) : IsClosed (cantorStage n) := by
  induction n with
  | zero => exact isClosed_Icc
  | succ n ih =>
      exact (ih.preimage (continuous_const.mul continuous_id)).union
        (ih.preimage ((continuous_const.mul continuous_id).sub continuous_const))

private theorem zero_mem_cantorStage (n : ℕ) : (0 : ℝ) ∈ cantorStage n := by
  induction n with
  | zero => exact ⟨le_rfl, zero_le_one⟩
  | succ n ih =>
      refine Or.inl ?_
      change (3 : ℝ) * 0 ∈ cantorStage n
      simpa using ih

private theorem one_mem_cantorStage (n : ℕ) : (1 : ℝ) ∈ cantorStage n := by
  induction n with
  | zero => exact ⟨zero_le_one, le_rfl⟩
  | succ n ih =>
      refine Or.inr ?_
      change (3 : ℝ) * 1 - 2 ∈ cantorStage n
      norm_num
      exact ih

private theorem volume_cantorStage (n : ℕ) :
    volume (cantorStage n) = ((2 : ℝ≥0∞) / 3) ^ n := by
  induction n with
  | zero => simp [cantorStage, Real.volume_Icc]
  | succ n ih =>
      let L : Set ℝ := (fun x : ℝ => 3 * x) ⁻¹' cantorStage n
      let R : Set ℝ := (fun x : ℝ => 3 * x - 2) ⁻¹' cantorStage n
      have hdisj : Disjoint L R := by
        rw [Set.disjoint_left]
        intro x hxL hxR
        have h1 : x ≤ 1 / 3 := by
          have := (cantorStage_subset_Icc n hxL).2
          linarith
        have h2 : 2 / 3 ≤ x := by
          have := (cantorStage_subset_Icc n hxR).1
          linarith
        linarith
      have hR_meas : MeasurableSet R :=
        (isClosed_cantorStage n).measurableSet.preimage
          ((continuous_const.mul continuous_id).sub continuous_const).measurable
      have hvolL : volume L = ((1 : ℝ≥0∞) / 3) * volume (cantorStage n) := by
        have h := Real.volume_preimage_mul_left (by norm_num : (3 : ℝ) ≠ 0) (cantorStage n)
        have h13 : ENNReal.ofReal |(3 : ℝ)⁻¹| = (1 : ℝ≥0∞) / 3 := by
          rw [abs_of_pos (by norm_num : (0 : ℝ) < 3⁻¹), ← one_div, ENNReal.ofReal_div_of_pos] <;>
            norm_num
        rw [h13] at h
        exact h
      have hvolR : volume R = ((1 : ℝ≥0∞) / 3) * volume (cantorStage n) := by
        have hEq : R = (fun x : ℝ => 3 * x) ⁻¹' ((fun y : ℝ => y + (-2)) ⁻¹' cantorStage n) := by
          ext x; simp [R, sub_eq_add_neg]
        rw [hEq, Real.volume_preimage_mul_left (by norm_num : (3 : ℝ) ≠ 0),
          measure_preimage_add_right]
        have h13 : ENNReal.ofReal |(3 : ℝ)⁻¹| = (1 : ℝ≥0∞) / 3 := by
          rw [abs_of_pos (by norm_num : (0 : ℝ) < 3⁻¹), ← one_div, ENNReal.ofReal_div_of_pos] <;>
            norm_num
        rw [h13]
      change volume (L ∪ R) = ((2 : ℝ≥0∞) / 3) ^ (n + 1)
      rw [measure_union hdisj hR_meas, hvolL, hvolR, ← add_mul, ih, pow_succ']
      congr 1
      rw [← ENNReal.add_div]
      norm_num

theorem isCompact_cantorSet : IsCompact cantorSet :=
  isCompact_Icc.of_isClosed_subset
    (isClosed_iInter isClosed_cantorStage)
    (iInter_subset cantorStage 0)

theorem cantorSet_subset_Icc : cantorSet ⊆ Icc (0 : ℝ) 1 :=
  iInter_subset cantorStage 0

theorem zero_mem_cantorSet : (0 : ℝ) ∈ cantorSet :=
  mem_iInter.mpr zero_mem_cantorStage

theorem one_mem_cantorSet : (1 : ℝ) ∈ cantorSet :=
  mem_iInter.mpr one_mem_cantorStage

theorem volume_cantorSet : volume cantorSet = 0 := by
  have htend : Tendsto (fun n => volume (cantorStage n)) atTop (𝓝 (volume cantorSet)) :=
    tendsto_measure_iInter_atTop (fun n => (isClosed_cantorStage n).measurableSet.nullMeasurableSet)
      cantorStage_antitone ⟨0, by simp [volume_cantorStage]⟩
  have hzero : Tendsto (fun n : ℕ => ((2 : ℝ≥0∞) / 3) ^ n) atTop (𝓝 0) := by
    refine ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ?_
    rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num)), one_mul]
    norm_num
  simp_rw [volume_cantorStage] at htend
  exact tendsto_nhds_unique htend hzero

private theorem eventuallyEq_const_cantorFun_of_notMem_stage :
    ∀ n : ℕ, ∀ {x : ℝ}, x ∉ cantorStage n → cantorFun =ᶠ[𝓝 x] fun _ => cantorFun x
  | 0, x, hx => by
      simp only [cantorStage, mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx0 | hx1
      · filter_upwards [Iio_mem_nhds hx0] with y hy
        rw [cantorFun_of_nonpos hy.le, cantorFun_of_nonpos hx0.le]
      · filter_upwards [Ioi_mem_nhds hx1] with y hy
        rw [cantorFun_of_one_le hy.le, cantorFun_of_one_le hx1.le]
  | n + 1, x, hx => by
      have hxL : 3 * x ∉ cantorStage n := fun h => hx (Or.inl h)
      have hxR : 3 * x - 2 ∉ cantorStage n := fun h => hx (Or.inr h)
      have hx_ne_third : x ≠ 1 / 3 := by
        rintro rfl
        apply hxL
        norm_num
        exact one_mem_cantorStage n
      have hx_ne_twothirds : x ≠ 2 / 3 := by
        rintro rfl
        apply hxR
        norm_num
        exact zero_mem_cantorStage n
      rcases lt_or_gt_of_ne hx_ne_third with hx1 | hx1
      · have hpull : ∀ᶠ y in 𝓝 x, cantorFun (3 * y) = cantorFun (3 * x) :=
          (continuous_const.mul continuous_id : Continuous fun y : ℝ => 3 * y).continuousAt.eventually
            (eventuallyEq_const_cantorFun_of_notMem_stage n hxL)
        filter_upwards [Iio_mem_nhds hx1, hpull] with y hy1 hy2
        rw [cantorFun_left hy1.le, cantorFun_left hx1.le, hy2]
      · rcases lt_or_gt_of_ne hx_ne_twothirds with hx2 | hx2
        · filter_upwards [Ioo_mem_nhds hx1 hx2] with y hy
          rw [cantorFun_mid hy.1 hy.2.le, cantorFun_mid hx1 hx2.le]
        · have hpull : ∀ᶠ y in 𝓝 x, cantorFun (3 * y - 2) = cantorFun (3 * x - 2) :=
            ((continuous_const.mul continuous_id).sub continuous_const :
              Continuous fun y : ℝ => 3 * y - 2).continuousAt.eventually
              (eventuallyEq_const_cantorFun_of_notMem_stage n hxR)
          filter_upwards [Ioi_mem_nhds hx2, hpull] with y hy1 hy2
          rw [cantorFun_right hy1, cantorFun_right hx2, hy2]

theorem hasDerivAt_cantorFun_of_notMem {x : ℝ} (hx : x ∉ cantorSet) :
    HasDerivAt cantorFun 0 x := by
  rw [cantorSet, mem_iInter, not_forall] at hx
  obtain ⟨n, hn⟩ := hx
  exact (hasDerivAt_const x (cantorFun x)).congr_of_eventuallyEq
    (eventuallyEq_const_cantorFun_of_notMem_stage n hn)

theorem image_cantorSet_cantorFun : cantorFun '' cantorSet = Icc (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hx0, hx1⟩ := cantorSet_subset_Icc hx
    exact ⟨cantorFun_zero ▸ monotone_cantorFun hx0, cantorFun_one ▸ monotone_cantorFun hx1⟩
  · intro y hy
    let K : Set ℝ := Icc 0 1 ∩ cantorFun ⁻¹' {y}
    have hK_compact : IsCompact K :=
      isCompact_Icc.inter_right (isClosed_singleton.preimage continuous_cantorFun)
    have hK_ne : K.Nonempty := by
      have hmem : y ∈ cantorFun '' Icc 0 1 := by
        have hivt := intermediate_value_Icc (zero_le_one : (0 : ℝ) ≤ 1)
          continuous_cantorFun.continuousOn
        rw [cantorFun_zero, cantorFun_one] at hivt
        exact hivt hy
      obtain ⟨x, hxIcc, rfl⟩ := hmem
      exact ⟨x, hxIcc, rfl⟩
    obtain ⟨x₀, hx₀⟩ := hK_compact.exists_isLeast hK_ne
    have hx₀_Icc : x₀ ∈ Icc (0 : ℝ) 1 := hx₀.1.1
    have hx₀_val : cantorFun x₀ = y := hx₀.1.2
    refine ⟨x₀, ?_, hx₀_val⟩
    by_contra hx₀_not
    have hx₀_pos : 0 < x₀ :=
      lt_of_le_of_ne hx₀_Icc.1 (fun h => hx₀_not (h ▸ zero_mem_cantorSet))
    rw [cantorSet, mem_iInter, not_forall] at hx₀_not
    obtain ⟨n, hn⟩ := hx₀_not
    obtain ⟨r, hr_pos, hr⟩ := Metric.eventually_nhds_iff.mp
      (eventuallyEq_const_cantorFun_of_notMem_stage n hn)
    let z : ℝ := max 0 (x₀ - r / 2)
    have hz_lt : z < x₀ := max_lt hx₀_pos (by linarith)
    have hz_Icc : z ∈ Icc (0 : ℝ) 1 := ⟨le_max_left 0 _, hz_lt.le.trans hx₀_Icc.2⟩
    have hz_dist : dist z x₀ < r := by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hz_lt)]
      have hle : x₀ - r / 2 ≤ z := le_max_right 0 _
      linarith
    have hz_val : cantorFun z = y := (hr hz_dist).trans hx₀_val
    exact not_lt.mpr (hx₀.2 ⟨hz_Icc, hz_val⟩) hz_lt

/-- **Example 7.16(b)** (Rudin, pp. 144–145): `cantorFun` is continuous and nondecreasing on `ℝ`,
satisfies `cantorFun 0 = 0` and `cantorFun 1 = 1`, has `deriv cantorFun = 0` almost everywhere
(hence `deriv cantorFun ∈ L¹([0, 1])` with `∫_0^1 f' = 0 ≠ f(1) - f(0)`), and maps the compact
Lebesgue-null set `cantorSet` onto `[0, 1]`. -/
theorem example_7_16b :
    Continuous cantorFun ∧
      Monotone cantorFun ∧
      cantorFun 0 = 0 ∧
      cantorFun 1 = 1 ∧
      (∀ᵐ x ∂volume, HasDerivAt cantorFun 0 x) ∧
      deriv cantorFun =ᵐ[volume] 0 ∧
      IntegrableOn (deriv cantorFun) (Icc 0 1) volume ∧
      (∫ x in (0 : ℝ)..1, deriv cantorFun x) = 0 ∧
      (∫ x in (0 : ℝ)..1, deriv cantorFun x) ≠ cantorFun 1 - cantorFun 0 ∧
      IsCompact cantorSet ∧
      volume cantorSet = 0 ∧
      cantorFun '' cantorSet = Icc 0 1 := by
  have hae_hasDeriv : ∀ᵐ x ∂volume, HasDerivAt cantorFun 0 x := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) volume_cantorSet
    by_contra hxC
    exact hx (hasDerivAt_cantorFun_of_notMem hxC)
  have hae_deriv : deriv cantorFun =ᵐ[volume] 0 := by
    filter_upwards [hae_hasDeriv] with x hx using hx.deriv
  have hint : IntegrableOn (deriv cantorFun) (Icc 0 1) volume := by
    refine (integrableOn_zero : IntegrableOn (0 : ℝ → ℝ) (Icc 0 1) volume).congr_fun_ae ?_
    exact ae_restrict_of_ae hae_deriv.symm
  have hint_eq : (∫ x in (0 : ℝ)..1, deriv cantorFun x) = 0 := by
    have hcongr : ∫ x in (0 : ℝ)..1, deriv cantorFun x = ∫ x in (0 : ℝ)..1, (0 : ℝ) :=
      intervalIntegral.integral_congr_ae (hae_deriv.mono fun _ hx _ => hx)
    simpa using hcongr
  refine ⟨continuous_cantorFun, monotone_cantorFun, cantorFun_zero, cantorFun_one,
    hae_hasDeriv, hae_deriv, hint, hint_eq, ?_,
    isCompact_cantorSet, volume_cantorSet, image_cantorSet_cantorFun⟩
  rw [hint_eq, cantorFun_one, cantorFun_zero]
  norm_num

end Node7_16

section Node7_17

/-- **Definition 7.17** (Rudin, p. 145): a complex function `f` on `[a, b]` is absolutely
continuous (*AC*) on `[a, b]` if for every `ε > 0` there exists `δ > 0` such that every finite
pairwise-disjoint family of open subintervals `(α_i, β_i)` of `[a, b]` with `∑ (β_i - α_i) < δ`
satisfies `∑ ‖f(β_i) - f(α_i)‖ < ε`. -/
def BookAbsolutelyContinuousOn (f : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (m : ℕ) (α β : Fin m → ℝ),
      (∀ i, a ≤ α i ∧ α i < β i ∧ β i ≤ b) →
      Pairwise (fun i j => Disjoint (Ioo (α i) (β i)) (Ioo (α j) (β j))) →
      (∑ i, (β i - α i)) < δ →
      (∑ i, ‖f (β i) - f (α i)‖) < ε

/-- Real-valued counterpart of **Definition 7.17** on `[a, b]`. -/
def BookAbsolutelyContinuousOnReal (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (m : ℕ) (α β : Fin m → ℝ),
      (∀ i, a ≤ α i ∧ α i < β i ∧ β i ≤ b) →
      Pairwise (fun i j => Disjoint (Ioo (α i) (β i)) (Ioo (α j) (β j))) →
      (∑ i, (β i - α i)) < δ →
      (∑ i, |f (β i) - f (α i)|) < ε

private theorem disjoint_Ioc_of_disjoint_Ioo {u₁ v₁ u₂ v₂ : ℝ}
    (_h1 : u₁ < v₁) (_h2 : u₂ < v₂) (hd : Disjoint (Ioo u₁ v₁) (Ioo u₂ v₂)) :
    Disjoint (Ioc u₁ v₁) (Ioc u₂ v₂) := by
  rw [Set.disjoint_left] at hd ⊢
  intro x hx1 hx2
  let y : ℝ := (max u₁ u₂ + x) / 2
  have hy1 : y ∈ Ioo u₁ v₁ := by
    have hlt : u₁ < max u₁ u₂ + x - u₁ := by
      have : u₁ ≤ max u₁ u₂ := le_max_left _ _
      linarith [hx1.1]
    have hgt : max u₁ u₂ < x := max_lt hx1.1 hx2.1
    exact ⟨by dsimp [y]; linarith, by dsimp [y]; linarith [hx1.2]⟩
  have hy2 : y ∈ Ioo u₂ v₂ := by
    have hgt : max u₁ u₂ < x := max_lt hx1.1 hx2.1
    have : u₂ ≤ max u₁ u₂ := le_max_right _ _
    exact ⟨by dsimp [y]; linarith, by dsimp [y]; linarith [hx2.2]⟩
  exact hd hy1 hy2

private theorem bookAC_iff_mathlibAC_normed {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (m : ℕ) (α β : Fin m → ℝ),
        (∀ i, a ≤ α i ∧ α i < β i ∧ β i ≤ b) →
        Pairwise (fun i j => Disjoint (Ioo (α i) (β i)) (Ioo (α j) (β j))) →
        (∑ i, (β i - α i)) < δ →
        (∑ i, ‖f (β i) - f (α i)‖) < ε) ↔
      AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff]
  constructor
  · intro hbook ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ := hbook ε hε
    refine ⟨δ, hδ_pos, ?_⟩
    rintro ⟨n, I⟩ ⟨hmem, hdisj⟩ hlen
    let S : Finset (Fin n) := Finset.univ.filter fun i : Fin n => (I i.1).1 ≠ (I i.1).2
    let m : ℕ := S.card
    let e : Fin m ≃ S := S.equivFin.symm
    let α : Fin m → ℝ := fun k => min (I (e k).1.1).1 (I (e k).1.1).2
    let β : Fin m → ℝ := fun k => max (I (e k).1.1).1 (I (e k).1.1).2
    have hsub : ∀ k : Fin m, a ≤ α k ∧ α k < β k ∧ β k ≤ b := by
      intro k
      have hk_lt : (e k).1.1 < n := (e k).1.2
      have hk_mem := hmem (e k).1.1 (Finset.mem_range.mpr hk_lt)
      rw [uIcc_of_le hab] at hk_mem
      have hne : (I (e k).1.1).1 ≠ (I (e k).1.1).2 := (Finset.mem_filter.mp (e k).2).2
      refine ⟨le_min hk_mem.1.1 hk_mem.2.1, ?_, max_le hk_mem.1.2 hk_mem.2.2⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · simp [α, β, min_eq_left hlt.le, max_eq_right hlt.le, hlt]
      · simp [α, β, min_eq_right hgt.le, max_eq_left hgt.le, hgt]
    have hpdisj : Pairwise fun k₁ k₂ : Fin m => Disjoint (Ioo (α k₁) (β k₁)) (Ioo (α k₂) (β k₂)) := by
      intro k₁ k₂ hk
      have he_ne : (e k₁).1.1 ≠ (e k₂).1.1 := by
        intro heq
        apply hk
        exact e.injective (Subtype.ext (Fin.ext heq))
      have hd_uIoc := hdisj
        (Finset.mem_range.mpr (e k₁).1.2)
        (Finset.mem_range.mpr (e k₂).1.2)
        he_ne
      exact hd_uIoc.mono Ioo_subset_Ioc_self Ioo_subset_Ioc_self
    have hlen_m : (∑ k : Fin m, (β k - α k)) < δ := by
      have heq : (∑ k : Fin m, (β k - α k)) = ∑ i ∈ Finset.range n, dist (I i).1 (I i).2 := by
        calc
          ∑ k : Fin m, (β k - α k)
            = ∑ s : S, (max (I s.1.1).1 (I s.1.1).2 - min (I s.1.1).1 (I s.1.1).2) :=
              Equiv.sum_comp e fun s : S => max (I s.1.1).1 (I s.1.1).2 - min (I s.1.1).1 (I s.1.1).2
          _ = ∑ i ∈ S, dist (I i.1).1 (I i.1).2 := by
              rw [Finset.sum_coe_sort S
                (fun i : Fin n => max (I i.1).1 (I i.1).2 - min (I i.1).1 (I i.1).2)]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Real.dist_eq, max_sub_min_eq_abs']
          _ = ∑ i : Fin n, dist (I i.1).1 (I i.1).2 := by
              refine Finset.sum_subset (Finset.subset_univ S) fun i _ hi => ?_
              simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
              simp [hi]
          _ = ∑ i ∈ Finset.range n, dist (I i).1 (I i).2 :=
              Fin.sum_univ_eq_sum_range (fun i => dist (I i).1 (I i).2) n
      exact heq.trans_lt hlen
    have hval := hδ m α β hsub hpdisj hlen_m
    have hval_eq :
        (∑ i ∈ Finset.range n, dist (f (I i).1) (f (I i).2)) =
          ∑ k : Fin m, ‖f (β k) - f (α k)‖ := by
      calc
        ∑ i ∈ Finset.range n, dist (f (I i).1) (f (I i).2)
          = ∑ i : Fin n, dist (f (I i.1).1) (f (I i.1).2) :=
            (Fin.sum_univ_eq_sum_range (fun i => dist (f (I i).1) (f (I i).2)) n).symm
        _ = ∑ i ∈ S, dist (f (I i.1).1) (f (I i.1).2) := by
            symm
            refine Finset.sum_subset (Finset.subset_univ S) fun i _ hi => ?_
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
            simp [hi]
        _ = ∑ s : S, dist (f (I s.1.1).1) (f (I s.1.1).2) :=
            (Finset.sum_coe_sort S (fun i : Fin n => dist (f (I i.1).1) (f (I i.1).2))).symm
        _ = ∑ k : Fin m, dist (f (I (e k).1.1).1) (f (I (e k).1.1).2) :=
            (Equiv.sum_comp e _).symm
        _ = ∑ k : Fin m, ‖f (β k) - f (α k)‖ := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rcases le_total (I (e k).1.1).1 (I (e k).1.1).2 with hle | hge
            · simp [α, β, min_eq_left hle, max_eq_right hle, dist_eq_norm, norm_sub_rev]
            · simp [α, β, min_eq_right hge, max_eq_left hge, dist_eq_norm]
    exact hval_eq.trans_lt hval
  · intro hmath ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ := hmath ε hε
    refine ⟨δ, hδ_pos, ?_⟩
    intro m α β hsub hpdisj hlen
    let I : ℕ → ℝ × ℝ := fun i =>
      if h : i < m then (α ⟨i, h⟩, β ⟨i, h⟩) else (a, a)
    have hdisj_in : (m, I) ∈ AbsolutelyContinuousOnInterval.disjWithin a b := by
      refine ⟨?_, ?_⟩
      · intro i hi
        have hi_lt : i < m := Finset.mem_range.mp hi
        obtain ⟨ha_le, hlt, hb_le⟩ := hsub ⟨i, hi_lt⟩
        rw [uIcc_of_le hab]
        simp [I, hi_lt, ha_le, hb_le, ha_le.trans hlt.le, hlt.le.trans hb_le]
      · intro i hi j hj hij
        have hi_lt : i < m := Finset.mem_range.mp hi
        have hj_lt : j < m := Finset.mem_range.mp hj
        have hne_fin : (⟨i, hi_lt⟩ : Fin m) ≠ ⟨j, hj_lt⟩ := fun h => hij (congrArg Fin.val h)
        have hlt_i : α ⟨i, hi_lt⟩ < β ⟨i, hi_lt⟩ := (hsub ⟨i, hi_lt⟩).2.1
        have hlt_j : α ⟨j, hj_lt⟩ < β ⟨j, hj_lt⟩ := (hsub ⟨j, hj_lt⟩).2.1
        change Disjoint (uIoc (I i).1 (I i).2) (uIoc (I j).1 (I j).2)
        simp only [I, hi_lt, hj_lt, ↓reduceDIte, uIoc_of_le hlt_i.le, uIoc_of_le hlt_j.le]
        exact disjoint_Ioc_of_disjoint_Ioo hlt_i hlt_j (hpdisj hne_fin)
    have hlen_I : (∑ i ∈ Finset.range m, dist (I i).1 (I i).2) < δ := by
      have heq : (∑ i ∈ Finset.range m, dist (I i).1 (I i).2) = ∑ k : Fin m, (β k - α k) := by
        rw [← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hlt := (hsub k).2.1
        simp only [I, k.2, ↓reduceDIte, Real.dist_eq]
        rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hlt)]
      exact heq.trans_lt hlen
    have hval := hδ (m, I) hdisj_in hlen_I
    have hval_eq :
        (∑ k : Fin m, ‖f (β k) - f (α k)‖) =
          ∑ i ∈ Finset.range m, dist (f (I i).1) (f (I i).2) := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [I, k.2, dist_eq_norm, norm_sub_rev]
    exact hval_eq.trans_lt hval

theorem bookAbsolutelyContinuousOn_iff {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) :
    BookAbsolutelyContinuousOn f a b ↔ AbsolutelyContinuousOnInterval f a b :=
  bookAC_iff_mathlibAC_normed f hab

theorem bookAbsolutelyContinuousOnReal_iff {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    BookAbsolutelyContinuousOnReal f a b ↔ AbsolutelyContinuousOnInterval f a b := by
  simpa [BookAbsolutelyContinuousOnReal, Real.norm_eq_abs] using
    bookAC_iff_mathlibAC_normed f hab

/-- **Assertion 7.17** (Rudin, p. 146): every complex function that is absolutely continuous on
`[a, b]` is continuous on `[a, b]`. -/
theorem BookAbsolutelyContinuousOn.continuousOn {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : BookAbsolutelyContinuousOn f a b) :
    ContinuousOn f (Icc a b) :=
  uIcc_of_le hab ▸ ((bookAbsolutelyContinuousOn_iff hab).mp hf).continuousOn

/-- Real-valued continuity consequence in **7.17**. -/
theorem BookAbsolutelyContinuousOnReal.continuousOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BookAbsolutelyContinuousOnReal f a b) :
    ContinuousOn f (Icc a b) :=
  uIcc_of_le hab ▸ ((bookAbsolutelyContinuousOnReal_iff hab).mp hf).continuousOn

private theorem absolutelyContinuousOnInterval_const {E : Type*} [PseudoMetricSpace E]
    (c : E) (a b : ℝ) : AbsolutelyContinuousOnInterval (fun _ => c) a b := by
  rw [absolutelyContinuousOnInterval_iff]
  exact fun ε hε => ⟨1, zero_lt_one, fun _ _ _ => by simpa using hε⟩

/-- **Discussion 7.16 / 7.17** (Rudin, pp. 145–146): absolute continuity on `[a, b]` is necessary
for integral reconstruction `f(x) = f(a) + ∫_a^x g(t) dt` with `g ∈ L¹([a, b])`. -/
theorem theorem_7_16_indefiniteIntegral_ac {f g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntegrableOn g (Icc a b) volume)
    (hf : ∀ x ∈ Icc a b, f x = f a + ∫ t in a..x, g t) :
    BookAbsolutelyContinuousOn f a b := by
  rw [bookAbsolutelyContinuousOn_iff hab]
  have ha : a ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨le_rfl, hab⟩
  have hg_re : IntervalIntegrable (fun t => (g t).re) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (Complex.reCLM.integrable_comp hg)
  have hg_im : IntervalIntegrable (fun t => (g t).im) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (Complex.imCLM.integrable_comp hg)
  have hac_re : AbsolutelyContinuousOnInterval
      (fun x => (Complex.ofRealLI (∫ t in a..x, (g t).re) : ℂ)) a b :=
    Complex.ofRealLI.lipschitz.comp_absolutelyContinuousOnInterval
      (hg_re.absolutelyContinuousOnInterval_intervalIntegral ha)
  have hac_im : AbsolutelyContinuousOnInterval
      (fun x => Complex.I • (Complex.ofRealLI (∫ t in a..x, (g t).im) : ℂ)) a b :=
    (Complex.ofRealLI.lipschitz.comp_absolutelyContinuousOnInterval
      (hg_im.absolutelyContinuousOnInterval_intervalIntegral ha)).const_smul Complex.I
  have hac_const : AbsolutelyContinuousOnInterval (fun _ : ℝ => f a) a b :=
    absolutelyContinuousOnInterval_const (f a) a b
  have hac_sum : AbsolutelyContinuousOnInterval
      (fun x => f a + ((Complex.ofRealLI (∫ t in a..x, (g t).re) : ℂ) +
        Complex.I • (Complex.ofRealLI (∫ t in a..x, (g t).im) : ℂ))) a b :=
    hac_const.add (hac_re.add hac_im)
  refine hac_sum.congr ?_
  rw [uIcc_of_le hab]
  intro x hx
  have hg_ax : IntervalIntegrable g volume a x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx.1).mpr
      (hg.mono_set (Icc_subset_Icc_right hx.2))
  have hre_eq : (∫ t in a..x, (g t).re) = (∫ t in a..x, g t).re :=
    Complex.reCLM.intervalIntegral_comp_comm hg_ax
  have him_eq : (∫ t in a..x, (g t).im) = (∫ t in a..x, g t).im :=
    Complex.imCLM.intervalIntegral_comp_comm hg_ax
  simp only [Complex.ofRealLI_apply, smul_eq_mul, hre_eq, him_eq]
  rw [mul_comm Complex.I _, Complex.re_add_im, ← hf x hx]

end Node7_17

section Node7_18

private theorem Icc_subset_biUnion_Ico_monotone {g : ℕ → ℝ} {i₁ i₂ : ℕ} (hi : i₁ < i₂)
    (hmono : ∀ j ∈ Finset.Ico i₁ i₂, g j ≤ g (j + 1)) :
    Icc (g i₁) (g i₂) ⊆ ⋃ j ∈ Finset.Ico i₁ i₂, Icc (g j) (g (j + 1)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hi
  clear hi
  induction d with
  | zero =>
      intro y hy
      rw [Nat.add_zero] at hy ⊢
      exact mem_iUnion₂.mpr ⟨i₁, Finset.mem_Ico.mpr ⟨le_rfl, Nat.lt_succ_self i₁⟩, hy⟩
  | succ d ih =>
      have hle_left : g i₁ ≤ g (i₁ + d + 1) := by
        clear ih
        induction d with
        | zero =>
            exact hmono i₁ (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
        | succ k ihk =>
            have hk1 := ihk (fun j hj => hmono j (Finset.Ico_subset_Ico_right (by omega) hj))
            have hk2 := hmono (i₁ + k + 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
            exact hk1.trans hk2
      have hsub : Finset.Ico i₁ (i₁ + d + 1) ⊆ Finset.Ico i₁ (i₁ + (d + 1) + 1) :=
        Finset.Ico_subset_Ico_right (by omega)
      have hprev := ih (fun j hj => hmono j (hsub hj))
      have hle_right : g (i₁ + d + 1) ≤ g (i₁ + (d + 1) + 1) :=
        hmono (i₁ + d + 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
      have hunion : Icc (g i₁) (g (i₁ + (d + 1) + 1)) =
          Icc (g i₁) (g (i₁ + d + 1)) ∪ Icc (g (i₁ + d + 1)) (g (i₁ + (d + 1) + 1)) :=
        (Icc_union_Icc_eq_Icc hle_left hle_right).symm
      rw [hunion]
      intro y hy
      rcases hy with hyL | hyR
      · obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp (hprev hyL)
        exact mem_iUnion₂.mpr ⟨j, hsub hj, hyj⟩
      · exact mem_iUnion₂.mpr ⟨i₁ + d + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hyR⟩

private theorem bookAC_maps_null_to_null_of_monotoneOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b)) (hmono : MonotoneOn f (Icc a b))
    (hac : BookAbsolutelyContinuousOnReal f a b) :
    ∀ E : Set ℝ, E ⊆ Icc a b → volume E = 0 → volume (f '' E) = 0 := by
  intro E hE hEnull
  rcases hab.eq_or_lt with rfl | hab_lt
  · have hsub : f '' E ⊆ {f a} := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Icc_self] at hE
      rw [mem_singleton_iff.mp (hE hx)]
      exact mem_singleton _
    exact measure_mono_null hsub (measure_singleton (f a))
  let E' : Set ℝ := E ∩ Ioo a b
  have hE'_sub : E' ⊆ Ioo a b := inter_subset_right
  have hE'_null : volume E' = 0 := measure_mono_null inter_subset_left hEnull
  have hsplit : E ⊆ ({a, b} : Set ℝ) ∪ E' := by
    intro x hx
    obtain ⟨hax, hxb⟩ := hE hx
    rcases hax.eq_or_lt with hax_eq | hax_lt
    · subst hax_eq
      exact Or.inl (mem_insert a {b})
    · rcases hxb.eq_or_lt with hxb_eq | hxb_lt
      · subst hxb_eq
        exact Or.inl (mem_insert_of_mem a (mem_singleton x))
      · exact Or.inr ⟨hx, hax_lt, hxb_lt⟩
  have hends_null : volume (f '' ({a, b} : Set ℝ)) = 0 :=
    ((Set.toFinite ({a, b} : Set ℝ)).image f).measure_zero volume
  suffices hE'_img : volume (f '' E') = 0 by
    have himg_sub : f '' E ⊆ f '' ({a, b} : Set ℝ) ∪ f '' E' := by
      rw [← image_union]
      exact image_mono hsplit
    exact le_antisymm
      ((measure_mono himg_sub).trans
        ((measure_union_le _ _).trans (by rw [hends_null, hE'_img, add_zero])))
      zero_le
  suffices hforall : ∀ ε : ℝ, 0 < ε → volume (f '' E') ≤ ENNReal.ofReal ε by
    apply le_antisymm _ zero_le
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    rw [zero_add]
    exact (hforall (ε : ℝ) (NNReal.coe_pos.mpr hε)).trans (by simp)
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := hac ε hε
  have hlt_δ : volume E' < ENNReal.ofReal δ := by
    rw [hE'_null]
    exact ENNReal.ofReal_pos.mpr hδ_pos
  obtain ⟨U₀, hE'U₀, hU₀_open, hU₀_vol⟩ := E'.exists_isOpen_lt_of_lt (ENNReal.ofReal δ) hlt_δ
  let U : Set ℝ := U₀ ∩ Ioo a b
  have hU_open : IsOpen U := hU₀_open.inter isOpen_Ioo
  have hE'U : E' ⊆ U := subset_inter hE'U₀ hE'_sub
  have hU_sub : U ⊆ Ioo a b := inter_subset_right
  have hU_vol : volume U < ENNReal.ofReal δ := (measure_mono inter_subset_left).trans_lt hU₀_vol
  let S : Set (ℚ × ℚ) := {pq | (pq.1 : ℝ) < (pq.2 : ℝ) ∧ Icc (pq.1 : ℝ) (pq.2 : ℝ) ⊆ U}
  have hU_cover : U ⊆ ⋃ pq ∈ S, Icc (pq.1 : ℝ) (pq.2 : ℝ) := by
    intro x hx
    obtain ⟨r, hr_pos, hball⟩ := Metric.isOpen_iff.mp hU_open x hx
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show x - r / 2 < x by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x < x + r / 2 by linarith)
    have hpq_lt : (p : ℝ) < (q : ℝ) := hp2.trans hq1
    have hpq_sub : Icc (p : ℝ) (q : ℝ) ⊆ U := by
      intro z hz
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    exact mem_iUnion₂.mpr ⟨(p, q), ⟨hpq_lt, hpq_sub⟩, hp2.le, hq1.le⟩
  by_cases hSne : S.Nonempty
  · obtain ⟨c, hc_range⟩ := S.to_countable.exists_eq_range hSne
    have hc_mem : ∀ k : ℕ, c k ∈ S := fun k => hc_range ▸ mem_range_self k
    let A : ℕ → Set ℝ := fun M =>
      ⋃ k ∈ Finset.range M, f '' Icc ((c k).1 : ℝ) ((c k).2 : ℝ)
    have hA_mono : Monotone A := fun M₁ M₂ hM =>
      biUnion_subset_biUnion_left (Finset.range_mono hM)
    have hA_le : ∀ M : ℕ, volume (A M) ≤ ENNReal.ofReal ε := by
      intro M
      classical
      let P : Finset ℝ :=
        ({a, b} : Finset ℝ) ∪
          (Finset.range M).image (fun k => ((c k).1 : ℝ)) ∪
          (Finset.range M).image (fun k => ((c k).2 : ℝ))
      have haP : a ∈ P := by simp [P]
      have hbP : b ∈ P := by simp [P]
      have hP_sub : ∀ z ∈ P, z ∈ Icc a b := by
        intro z hz
        simp only [P, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          Finset.mem_image, Finset.mem_range] at hz
        rcases hz with ((rfl | rfl) | ⟨k, _, rfl⟩) | ⟨k, _, rfl⟩
        · exact ⟨le_rfl, hab_lt.le⟩
        · exact ⟨hab_lt.le, le_rfl⟩
        · have hk := ((hc_mem k).2 (left_mem_Icc.mpr (hc_mem k).1.le))
          exact Ioo_subset_Icc_self (hU_sub hk)
        · have hk := ((hc_mem k).2 (right_mem_Icc.mpr (hc_mem k).1.le))
          exact Ioo_subset_Icc_self (hU_sub hk)
      have hcard_ge : 2 ≤ P.card := by
        have hsub_ab : ({a, b} : Finset ℝ) ⊆ P := by
          intro z hz; simp only [P, Finset.mem_union]; exact Or.inl (Or.inl hz)
        calc
          2 = ({a, b} : Finset ℝ).card := (Finset.card_pair hab_lt.ne).symm
          _ ≤ P.card := Finset.card_le_card hsub_ab
      let e := P.orderEmbOfFin rfl
      let g : ℕ → ℝ := fun j => if hj : j < P.card then e ⟨j, hj⟩ else b
      have hg_strict : ∀ {j₁ j₂ : ℕ}, j₁ < j₂ → j₂ < P.card → g j₁ < g j₂ := by
        intro j₁ j₂ hj₁₂ hj₂
        have hj₁ : j₁ < P.card := hj₁₂.trans hj₂
        simp only [g, hj₁, hj₂, ↓reduceDIte]
        exact e.strictMono hj₁₂
      have hg_mem : ∀ {j : ℕ}, j < P.card → g j ∈ Icc a b := by
        intro j hj
        simp only [g, hj, ↓reduceDIte]
        exact hP_sub _ (P.orderEmbOfFin_mem rfl ⟨j, hj⟩)
      let W_M : Set ℝ := ⋃ k ∈ Finset.range M, Ioo ((c k).1 : ℝ) ((c k).2 : ℝ)
      have hW_M_sub_U : W_M ⊆ U :=
        iUnion₂_subset fun k _ => Ioo_subset_Icc_self.trans (hc_mem k).2
      let Good : Finset (Fin (P.card - 1)) :=
        Finset.univ.filter fun j => Ioo (g j.1) (g (j.1 + 1)) ⊆ W_M
      let m : ℕ := Good.card
      let eqv : Fin m ≃ Good := Good.equivFin.symm
      let α : Fin m → ℝ := fun idx => g (eqv idx).1.1
      let β : Fin m → ℝ := fun idx => g ((eqv idx).1.1 + 1)
      have hsub_ab_idx : ∀ idx : Fin m, a ≤ α idx ∧ α idx < β idx ∧ β idx ≤ b := by
        intro idx
        have hj_lt : (eqv idx).1.1 + 1 < P.card := by omega
        have hj0 : (eqv idx).1.1 < P.card := by omega
        exact ⟨(hg_mem hj0).1, hg_strict (Nat.lt_succ_self _) hj_lt, (hg_mem hj_lt).2⟩
      have hpdisj : Pairwise fun i₁ i₂ : Fin m =>
          Disjoint (Ioo (α i₁) (β i₁)) (Ioo (α i₂) (β i₂)) := by
        intro i₁ i₂ hne
        have hj_ne : (eqv i₁).1.1 ≠ (eqv i₂).1.1 := by
          intro heq
          apply hne
          exact eqv.injective (Subtype.ext (Fin.ext heq))
        rw [Set.disjoint_left]
        intro x hx1 hx2
        rcases lt_or_gt_of_ne hj_ne with hlt | hgt
        · have hsucc : (eqv i₁).1.1 + 1 ≤ (eqv i₂).1.1 := hlt
          have hle : β i₁ ≤ α i₂ := by
            rcases hsucc.eq_or_lt with heq | hlt2
            · dsimp only [α, β]; rw [heq]
            · exact (hg_strict hlt2 (by omega)).le
          linarith [hx1.2, hx2.1]
        · have hsucc : (eqv i₂).1.1 + 1 ≤ (eqv i₁).1.1 := hgt
          have hle : β i₂ ≤ α i₁ := by
            rcases hsucc.eq_or_lt with heq | hlt2
            · dsimp only [α, β]; rw [heq]
            · exact (hg_strict hlt2 (by omega)).le
          linarith [hx2.2, hx1.1]
      have hlen_lt : (∑ idx : Fin m, (β idx - α idx)) < δ := by
        have hvol_eq :
            ENNReal.ofReal (∑ idx : Fin m, (β idx - α idx)) =
              volume (⋃ idx : Fin m, Ioo (α idx) (β idx)) := by
          rw [measure_iUnion hpdisj (fun _ => measurableSet_Ioo), tsum_fintype,
            ENNReal.ofReal_sum_of_nonneg (fun idx _ => sub_nonneg.mpr (hsub_ab_idx idx).2.1.le)]
          refine Finset.sum_congr rfl fun idx _ => ?_
          rw [Real.volume_Ioo]
        have hvol_lt : volume (⋃ idx : Fin m, Ioo (α idx) (β idx)) < ENNReal.ofReal δ := by
          refine (measure_mono ?_).trans_lt hU_vol
          refine iUnion_subset fun idx => ?_
          exact ((Finset.mem_filter.mp (eqv idx).2).2).trans hW_M_sub_U
        exact (ENNReal.ofReal_lt_ofReal_iff hδ_pos).mp (hvol_eq.trans_lt hvol_lt)
      have hac_sum := hδ m α β hsub_ab_idx hpdisj hlen_lt
      have hA_cov : A M ⊆ ⋃ idx : Fin m, Icc (f (α idx)) (f (β idx)) := by
        refine iUnion₂_subset fun k hk => ?_
        have hk_lt : k < M := Finset.mem_range.mp hk
        have hp_mem : ((c k).1 : ℝ) ∈ P := by
          simp only [P, Finset.mem_union, Finset.mem_image, Finset.mem_range]
          exact Or.inl (Or.inr ⟨k, hk_lt, rfl⟩)
        have hq_mem : ((c k).2 : ℝ) ∈ P := by
          simp only [P, Finset.mem_union, Finset.mem_image, Finset.mem_range]
          exact Or.inr ⟨k, hk_lt, rfl⟩
        have hp_rng : ((c k).1 : ℝ) ∈ Set.range e := by
          rw [Finset.range_orderEmbOfFin P rfl]
          exact hp_mem
        have hq_rng : ((c k).2 : ℝ) ∈ Set.range e := by
          rw [Finset.range_orderEmbOfFin P rfl]
          exact hq_mem
        obtain ⟨i₁, hi₁⟩ := hp_rng
        obtain ⟨i₂, hi₂⟩ := hq_rng
        have hi₁₂ : i₁ < i₂ := by
          by_contra hnot
          have hle : e i₂ ≤ e i₁ := e.monotone (not_lt.mp hnot)
          rw [hi₁, hi₂] at hle
          exact not_lt.mpr hle (hc_mem k).1
        have hg_i₁ : g i₁.1 = ((c k).1 : ℝ) := by simp [g, i₁.2, hi₁]
        have hg_i₂ : g i₂.1 = ((c k).2 : ℝ) := by simp [g, i₂.2, hi₂]
        have hf_step_mono : ∀ j ∈ Finset.Ico i₁.1 i₂.1, f (g j) ≤ f (g (j + 1)) := by
          intro j hj
          have hj2 : j + 1 < P.card :=
            (Nat.succ_le_of_lt (Finset.mem_Ico.mp hj).2).trans_lt i₂.2
          have hj1 : j < P.card := (Nat.lt_succ_self j).trans hj2
          exact hmono (hg_mem hj1) (hg_mem hj2) (hg_strict (Nat.lt_succ_self j) hj2).le
        rintro _ ⟨x, hx, rfl⟩
        have hfx_mem : f x ∈ Icc (f (g i₁.1)) (f (g i₂.1)) := by
          rw [hg_i₁, hg_i₂]
          have hsub_k : Icc ((c k).1 : ℝ) ((c k).2 : ℝ) ⊆ Icc a b :=
            ((hc_mem k).2.trans hU_sub).trans Ioo_subset_Icc_self
          exact ⟨hmono (hsub_k ⟨le_rfl, (hc_mem k).1.le⟩) (hsub_k hx) hx.1,
            hmono (hsub_k hx) (hsub_k ⟨(hc_mem k).1.le, le_rfl⟩) hx.2⟩
        have hfx_u := Icc_subset_biUnion_Ico_monotone (g := fun j => f (g j)) hi₁₂ hf_step_mono hfx_mem
        obtain ⟨j, hj_Ico, hfx_j⟩ := mem_iUnion₂.mp hfx_u
        have hj_lt_sub : j < P.card - 1 := by
          have := (Finset.mem_Ico.mp hj_Ico).2
          have := i₂.2
          omega
        let jfin : Fin (P.card - 1) := ⟨j, hj_lt_sub⟩
        have hj_good : jfin ∈ Good := by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          intro z hz
          refine mem_iUnion₂.mpr ⟨k, hk, ?_⟩
          have hlo : g i₁.1 ≤ g j := by
            rcases (Finset.mem_Ico.mp hj_Ico).1.eq_or_lt with heq | hlt
            · rw [heq]
            · exact (hg_strict hlt (by omega)).le
          have hhi : g (j + 1) ≤ g i₂.1 := by
            rcases (Nat.succ_le_of_lt (Finset.mem_Ico.mp hj_Ico).2).eq_or_lt with heq | hlt
            · change j + 1 = i₂.1 at heq
              rw [heq]
            · exact (hg_strict hlt i₂.2).le
          rw [← hg_i₁, ← hg_i₂]
          exact ⟨hlo.trans_lt hz.1, hz.2.trans_le hhi⟩
        let idx : Fin m := eqv.symm ⟨jfin, hj_good⟩
        have hidx_eq : eqv idx = ⟨jfin, hj_good⟩ := eqv.apply_symm_apply _
        refine mem_iUnion.mpr ⟨idx, ?_⟩
        simpa [α, β, hidx_eq, jfin] using hfx_j
      calc
        volume (A M) ≤ volume (⋃ idx : Fin m, Icc (f (α idx)) (f (β idx))) :=
          measure_mono hA_cov
        _ ≤ ∑ idx : Fin m, volume (Icc (f (α idx)) (f (β idx))) :=
          measure_iUnion_fintype_le volume _
        _ = ENNReal.ofReal (∑ idx : Fin m, |f (β idx) - f (α idx)|) := by
          have hnonneg : ∀ idx : Fin m, 0 ≤ f (β idx) - f (α idx) := fun idx =>
            sub_nonneg.mpr (hmono ⟨(hsub_ab_idx idx).1, (hsub_ab_idx idx).2.1.le.trans (hsub_ab_idx idx).2.2⟩
              ⟨(hsub_ab_idx idx).1.trans (hsub_ab_idx idx).2.1.le, (hsub_ab_idx idx).2.2⟩
              (hsub_ab_idx idx).2.1.le)
          rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
          refine Finset.sum_congr rfl fun idx _ => ?_
          rw [Real.volume_Icc, abs_of_nonneg (hnonneg idx)]
        _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hac_sum.le
    have hE'_sub_A : f '' E' ⊆ ⋃ M : ℕ, A M := by
      rintro _ ⟨x, hxE', rfl⟩
      obtain ⟨pq, hpqS, hxpq⟩ := mem_iUnion₂.mp (hU_cover (hE'U hxE'))
      obtain ⟨k, rfl⟩ := hc_range ▸ hpqS
      exact mem_iUnion.mpr ⟨k + 1, mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k),
        ⟨x, hxpq, rfl⟩⟩⟩
    calc
      volume (f '' E') ≤ volume (⋃ M : ℕ, A M) := measure_mono hE'_sub_A
      _ = ⨆ M : ℕ, volume (A M) := hA_mono.measure_iUnion
      _ ≤ ENNReal.ofReal ε := iSup_le hA_le
  · rw [Set.not_nonempty_iff_eq_empty] at hSne
    have hE'_emp : E' = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxU := hU_cover (hE'U hx)
      simp [hSne] at hxU
    simp [hE'_emp]

private theorem bookAC_of_maps_null_to_null_monotoneOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b)) (hmono : MonotoneOn f (Icc a b))
    (hlusin : ∀ E : Set ℝ, E ⊆ Icc a b → volume E = 0 → volume (f '' E) = 0) :
    BookAbsolutelyContinuousOnReal f a b := by
  rcases hab.eq_or_lt with rfl | hab_lt
  · intro ε hε
    refine ⟨1, zero_lt_one, fun m α β hsub _ _ => ?_⟩
    cases m with
    | zero => simpa using hε
    | succ k =>
        obtain ⟨ha1, hlt, hb1⟩ := hsub 0
        linarith
  have hint : IntegrableOn (deriv f) (Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
      ((uIcc_of_le hab ▸ hmono).intervalIntegrable_deriv)
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let g : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (deriv f x)
  have hg_lt_top : ∫⁻ x, g x ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top hint.2.ne ?_
    refine lintegral_mono fun x => ?_
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  let Bbad : Set ℝ := {x ∈ Ioo a b | ¬ DifferentiableAt ℝ f x}
  have hBbad_null : volume Bbad = 0 := by
    have hae := hmono.ae_differentiableWithinAt_of_mem
    rw [ae_iff] at hae
    refine measure_mono_null (fun x hx => ?_) hae
    intro hdiff
    exact hx.2 ((hdiff (Ioo_subset_Icc_self hx.1)).differentiableAt
      (Icc_mem_nhds hx.1.1 hx.1.2))
  let N₀ : Set ℝ := toMeasurable volume Bbad ∩ Ioo a b
  have hN₀_meas : MeasurableSet N₀ := (measurableSet_toMeasurable volume Bbad).inter measurableSet_Ioo
  have hN₀_null : volume N₀ = 0 :=
    measure_mono_null inter_subset_left (by rw [measure_toMeasurable, hBbad_null])
  let D₀ : Set ℝ := Ioo a b \ N₀
  have hD₀_meas : MeasurableSet D₀ := measurableSet_Ioo.diff hN₀_meas
  have hD₀_diff : ∀ x ∈ D₀, DifferentiableAt ℝ f x := by
    intro x hx
    by_contra hnd
    exact hx.2 ⟨subset_toMeasurable volume Bbad ⟨hx.1, hnd⟩, hx.1⟩
  intro ε hε
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := exists_pos_setLIntegral_lt_of_measure_lt (μ := μ) hg_lt_top
    (ENNReal.ofReal_pos.mpr hε).ne'
  obtain ⟨δ_nn, hδ_nn_pos, hδ_nn_lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hδ₀_pos
  have hδ_real_pos : 0 < (δ_nn : ℝ) := NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hδ_nn_pos)
  refine ⟨(δ_nn : ℝ), hδ_real_pos, ?_⟩
  intro m α β hsub hpdisj hlen
  let W : Set ℝ := ⋃ i : Fin m, Ioo (α i) (β i)
  have hW_meas : MeasurableSet W := MeasurableSet.iUnion fun _ => measurableSet_Ioo
  have hW_sub_Ioo : W ⊆ Ioo a b :=
    iUnion_subset fun i x hx => ⟨(hsub i).1.trans_lt hx.1, hx.2.trans_le (hsub i).2.2⟩
  have hW_vol_lt : μ W < δ₀ := by
    have hμW : μ W = volume W := by
      dsimp [μ]
      rw [Measure.restrict_apply hW_meas,
        inter_eq_left.mpr (hW_sub_Ioo.trans Ioo_subset_Icc_self)]
    have hvW : volume W = ENNReal.ofReal (∑ i : Fin m, (β i - α i)) := by
      rw [measure_iUnion hpdisj (fun _ => measurableSet_Ioo), tsum_fintype,
        ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.mpr (hsub i).2.1.le)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.volume_Ioo]
    rw [hμW, hvW]
    exact (ENNReal.ofReal_lt_ofReal_iff hδ_real_pos).mpr hlen |>.trans
      (by simpa [ENNReal.ofReal_coe_nnreal] using hδ_nn_lt)
  have himg_disj : Pairwise fun i j : Fin m =>
      Disjoint (Ioo (f (α i)) (f (β i))) (Ioo (f (α j)) (f (β j))) := by
    intro i j hij
    have hd := hpdisj hij
    have horder : β i ≤ α j ∨ β j ≤ α i := by
      by_contra hnot
      push Not at hnot
      let z : ℝ := (max (α i) (α j) + min (β i) (β j)) / 2
      have hlt_mm : max (α i) (α j) < min (β i) (β j) :=
        max_lt (lt_min (hsub i).2.1 hnot.2) (lt_min hnot.1 (hsub j).2.1)
      have hz_i : z ∈ Ioo (α i) (β i) :=
        ⟨by dsimp [z]; linarith [le_max_left (α i) (α j)],
          by dsimp [z]; linarith [min_le_left (β i) (β j)]⟩
      have hz_j : z ∈ Ioo (α j) (β j) :=
        ⟨by dsimp [z]; linarith [le_max_right (α i) (α j)],
          by dsimp [z]; linarith [min_le_right (β i) (β j)]⟩
      exact Set.disjoint_left.mp hd hz_i hz_j
    rw [Set.disjoint_left]
    intro y hyi hyj
    rcases horder with hle | hle
    · have hf_le : f (β i) ≤ f (α j) :=
        hmono ⟨(hsub i).1.trans (hsub i).2.1.le, (hsub i).2.2⟩
          ⟨(hsub j).1, (hsub j).2.1.le.trans (hsub j).2.2⟩ hle
      linarith [hyi.2, hyj.1]
    · have hf_le : f (β j) ≤ f (α i) :=
        hmono ⟨(hsub j).1.trans (hsub j).2.1.le, (hsub j).2.2⟩
          ⟨(hsub i).1, (hsub i).2.1.le.trans (hsub i).2.2⟩ hle
      linarith [hyj.2, hyi.1]
  have himg_sub : (⋃ i : Fin m, Ioo (f (α i)) (f (β i))) ⊆ f '' W := by
    refine iUnion_subset fun i y hy => ?_
    have hsub_i : Icc (α i) (β i) ⊆ Icc a b :=
      Icc_subset_Icc (hsub i).1 (hsub i).2.2
    have hivt : Icc (f (α i)) (f (β i)) ⊆ f '' Icc (α i) (β i) :=
      intermediate_value_Icc (hsub i).2.1.le (hcont.mono hsub_i)
    obtain ⟨x, hxIcc, rfl⟩ := hivt (Ioo_subset_Icc_self hy)
    have hx_ne_a : x ≠ α i := fun h => by subst h; exact hy.1.ne rfl
    have hx_ne_b : x ≠ β i := fun h => by subst h; exact hy.2.ne rfl
    exact ⟨x, mem_iUnion.mpr ⟨i, lt_of_le_of_ne hxIcc.1 hx_ne_a.symm,
      lt_of_le_of_ne hxIcc.2 hx_ne_b⟩, rfl⟩
  have hsum_le_img : ENNReal.ofReal (∑ i : Fin m, |f (β i) - f (α i)|) ≤ volume (f '' W) := by
    have hnonneg : ∀ i : Fin m, 0 ≤ f (β i) - f (α i) := fun i =>
      sub_nonneg.mpr (hmono ⟨(hsub i).1, (hsub i).2.1.le.trans (hsub i).2.2⟩
        ⟨(hsub i).1.trans (hsub i).2.1.le, (hsub i).2.2⟩ (hsub i).2.1.le)
    calc
      ENNReal.ofReal (∑ i : Fin m, |f (β i) - f (α i)|)
        = ∑ i : Fin m, volume (Ioo (f (α i)) (f (β i))) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Real.volume_Ioo, abs_of_nonneg (hnonneg i)]
      _ = volume (⋃ i : Fin m, Ioo (f (α i)) (f (β i))) := by
          rw [measure_iUnion himg_disj (fun _ => measurableSet_Ioo), tsum_fintype]
      _ ≤ volume (f '' W) := measure_mono himg_sub
  have hW_decomp : W = (W ∩ N₀) ∪ (W ∩ D₀) := by
    ext x
    constructor
    · intro hx
      by_cases hxN : x ∈ N₀
      · exact Or.inl ⟨hx, hxN⟩
      · exact Or.inr ⟨hx, hW_sub_Ioo hx, hxN⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hWN_null : volume (f '' (W ∩ N₀)) = 0 :=
    hlusin (W ∩ N₀) (inter_subset_left.trans (hW_sub_Ioo.trans Ioo_subset_Icc_self))
      (measure_mono_null inter_subset_right hN₀_null)
  have hWD_eq : volume (f '' (W ∩ D₀)) = ∫⁻ x in W ∩ D₀, g x ∂volume := by
    symm
    exact MeasureTheory.lintegral_deriv_eq_volume_image_of_monotoneOn
      (hW_meas.inter hD₀_meas)
      (fun x hx => (hD₀_diff x hx.2).hasDerivAt.hasDerivWithinAt)
      (hmono.mono (inter_subset_left.trans (hW_sub_Ioo.trans Ioo_subset_Icc_self)))
  have hWD_lt : volume (f '' (W ∩ D₀)) < ENNReal.ofReal ε := by
    rw [hWD_eq]
    have hle_μ : ∫⁻ x in W ∩ D₀, g x ∂volume ≤ ∫⁻ x in W, g x ∂μ := by
      have h1 : ∫⁻ x in W ∩ D₀, g x ∂volume ≤ ∫⁻ x in W, g x ∂volume :=
        lintegral_mono_set inter_subset_left
      have h2 : ∫⁻ x in W, g x ∂volume = ∫⁻ x in W, g x ∂μ := by
        dsimp [μ]
        rw [Measure.restrict_restrict hW_meas,
          inter_eq_left.mpr (hW_sub_Ioo.trans Ioo_subset_Icc_self)]
      exact h2 ▸ h1
    exact hle_μ.trans_lt (hδ₀ W hW_vol_lt)
  have himg_lt : volume (f '' W) < ENNReal.ofReal ε := by
    have h1 : volume (f '' W) ≤ volume (f '' (W ∩ N₀)) + volume (f '' (W ∩ D₀)) := by
      conv_lhs => rw [hW_decomp, image_union]
      exact measure_union_le _ _
    rw [hWN_null, zero_add] at h1
    exact h1.trans_lt hWD_lt
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp (hsum_le_img.trans_lt himg_lt)

/-- **Theorem 7.18** (Rudin, pp. 146–147): for a continuous nondecreasing real function `f` on
`[a, b]`, the following properties are pairwise equivalent:
(a) `f` is absolutely continuous on `[a, b]`;
(b) `f` maps every Lebesgue-null subset of `[a, b]` to a Lebesgue-null set;
(c) `f` is differentiable a.e. on `[a, b]`, `f' ∈ L¹([a, b])`, and
    `f(x) - f(a) = ∫_a^x f'(t) dt` for every `x ∈ [a, b]`. -/
theorem theorem_7_18 {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b)) (hmono : MonotoneOn f (Icc a b)) :
    (BookAbsolutelyContinuousOnReal f a b ↔
        (∀ E : Set ℝ, E ⊆ Icc a b → volume E = 0 → volume (f '' E) = 0)) ∧
      ((∀ E : Set ℝ, E ⊆ Icc a b → volume E = 0 → volume (f '' E) = 0) ↔
        ((∀ᵐ x ∂(volume.restrict (Icc a b)), DifferentiableAt ℝ f x) ∧
          IntegrableOn (deriv f) (Icc a b) volume ∧
          ∀ x ∈ Icc a b, f x - f a = ∫ t in a..x, deriv f t)) ∧
      (BookAbsolutelyContinuousOnReal f a b ↔
        ((∀ᵐ x ∂(volume.restrict (Icc a b)), DifferentiableAt ℝ f x) ∧
          IntegrableOn (deriv f) (Icc a b) volume ∧
          ∀ x ∈ Icc a b, f x - f a = ∫ t in a..x, deriv f t)) := by
  have hab_iff_ab :
      BookAbsolutelyContinuousOnReal f a b ↔
        (∀ E : Set ℝ, E ⊆ Icc a b → volume E = 0 → volume (f '' E) = 0) :=
    ⟨bookAC_maps_null_to_null_of_monotoneOn hab hcont hmono,
      bookAC_of_maps_null_to_null_monotoneOn hab hcont hmono⟩
  have hab_iff_ac :
      BookAbsolutelyContinuousOnReal f a b ↔
        ((∀ᵐ x ∂(volume.restrict (Icc a b)), DifferentiableAt ℝ f x) ∧
          IntegrableOn (deriv f) (Icc a b) volume ∧
          ∀ x ∈ Icc a b, f x - f a = ∫ t in a..x, deriv f t) := by
    constructor
    · intro hac
      have hmath : AbsolutelyContinuousOnInterval f a b :=
        (bookAbsolutelyContinuousOnReal_iff hab).mp hac
      have hae : ∀ᵐ x ∂(volume.restrict (Icc a b)), DifferentiableAt ℝ f x := by
        rw [ae_restrict_iff' measurableSet_Icc]
        filter_upwards [hmath.ae_differentiableAt] with x hx hxIcc
        exact hx (uIcc_of_le hab ▸ hxIcc)
      have hint : IntegrableOn (deriv f) (Icc a b) volume :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hmath.intervalIntegrable_deriv
      refine ⟨hae, hint, ?_⟩
      intro x hx
      have hax : AbsolutelyContinuousOnInterval f a x :=
        hmath.mono (by rw [uIcc_of_le hab, uIcc_of_le hx.1]; exact Icc_subset_Icc_right hx.2)
      exact hax.integral_deriv_eq_sub.symm
    · rintro ⟨_, hint, hftc⟩
      rw [bookAbsolutelyContinuousOnReal_iff hab]
      have hint_iv : IntervalIntegrable (deriv f) volume a b :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hint
      have ha : a ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨le_rfl, hab⟩
      have hac_int : AbsolutelyContinuousOnInterval
          (fun x => f a + ∫ t in a..x, deriv f t) a b :=
        (absolutelyContinuousOnInterval_const (f a) a b).add
          (hint_iv.absolutelyContinuousOnInterval_intervalIntegral ha)
      refine hac_int.congr ?_
      rw [uIcc_of_le hab]
      intro x hx
      linarith [hftc x hx]
  exact ⟨hab_iff_ab, hab_iff_ab.symm.trans hab_iff_ac, hab_iff_ac⟩

/-- **Remark in 7.18** (Rudin, p. 147): the Cantor–Lebesgue singular function `cantorFun` is not
absolutely continuous on `[0, 1]` because it maps the compact null set `cantorSet` onto `[0, 1]`. -/
theorem not_bookAbsolutelyContinuousOnReal_cantorFun :
    ¬ BookAbsolutelyContinuousOnReal cantorFun 0 1 := by
  intro hac
  have hnull := (theorem_7_18 (zero_le_one : (0 : ℝ) ≤ 1)
    continuous_cantorFun.continuousOn (monotone_cantorFun.monotoneOn _)).1.mp hac
    cantorSet cantorSet_subset_Icc volume_cantorSet
  rw [image_cantorSet_cantorFun, Real.volume_Icc] at hnull
  norm_num at hnull

end Node7_18

section Node7_19

/-- Rudin's strict-partition total variation on `[a, x]` in `[0, ∞]`: for `a < x`, the supremum of
`∑_{i=0}^{N-1} edist(f(t_{i+1}), f(t_i))` over strict partitions `a = t_0 < t_1 < ⋯ < t_N = x`
(`N ≥ 1`), and `0` when `x ≤ a`. -/
def strictPartitionVariationENNReal {E : Type*} [PseudoEMetricSpace E]
    (f : ℝ → E) (a x : ℝ) : ℝ≥0∞ :=
  if a < x then
    ⨆ p : { pair : ℕ × (ℕ → ℝ) //
        1 ≤ pair.1 ∧ pair.2 0 = a ∧ pair.2 pair.1 = x ∧ StrictMonoOn pair.2 (Iic pair.1) },
      ∑ i ∈ Finset.range p.1.1, edist (f (p.1.2 (i + 1))) (f (p.1.2 i))
  else 0

theorem strictPartitionVariationENNReal_eq_eVariationOn {E : Type*} [PseudoEMetricSpace E]
    (f : ℝ → E) {a x : ℝ} (hax : a ≤ x) :
    strictPartitionVariationENNReal f a x = eVariationOn f (Icc a x) := by
  rcases hax.eq_or_lt with rfl | hlt
  · simp [strictPartitionVariationENNReal]
  simp only [strictPartitionVariationENNReal, hlt, ↓reduceIte]
  rw [eVariationOn.eVariationOn_eq_strictMonoOn]
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨⟨N, t⟩, _, ht0, htN, hstrict⟩ := p
    have hmem : ∀ i ∈ Iic N, t i ∈ Icc a x := by
      intro i hi
      refine ⟨?_, ?_⟩
      · rw [← ht0]
        rcases (Nat.zero_le i).eq_or_lt with heq | hpos
        · rw [← heq]
        · exact (hstrict (mem_Iic.mpr (Nat.zero_le N)) hi hpos).le
      · rw [← htN]
        rcases (mem_Iic.mp hi).eq_or_lt with heq | hlt_i
        · rw [heq]
        · exact (hstrict hi (mem_Iic.mpr le_rfl) hlt_i).le
    exact le_iSup
      (fun q : (n : ℕ) × { u : ℕ → ℝ // StrictMonoOn u (Iic n) ∧ ∀ i ∈ Iic n, u i ∈ Icc a x } =>
        ∑ i ∈ Finset.range q.1, edist (f (q.2.1 (i + 1))) (f (q.2.1 i)))
      ⟨N, ⟨t, hstrict, hmem⟩⟩
  · refine iSup_le ?_
    rintro ⟨n, ⟨u, u_strict, u_mem⟩⟩
    have hu0_ge : a ≤ u 0 := (u_mem 0 (mem_Iic.mpr (Nat.zero_le n))).1
    have hun_le : u n ≤ x := (u_mem n (mem_Iic.mpr le_rfl)).2
    have hstep1 : ∃ (n₁ : ℕ) (u₁ : ℕ → ℝ),
        u₁ 0 = a ∧ u₁ n₁ ≤ x ∧ StrictMonoOn u₁ (Iic n₁) ∧
        (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤
          ∑ i ∈ Finset.range n₁, edist (f (u₁ (i + 1))) (f (u₁ i)) := by
      rcases hu0_ge.eq_or_lt with hu0_eq | hu0_lt
      · exact ⟨n, u, hu0_eq.symm, hun_le, u_strict, le_rfl⟩
      · let u₁ : ℕ → ℝ := fun k => if k = 0 then a else u (k - 1)
        refine ⟨n + 1, u₁, rfl, by simp [u₁, hun_le], ?_, ?_⟩
        · intro i hi j hj hij
          rcases Nat.eq_zero_or_pos i with rfl | hipos
          · have hjpos : 0 < j := hij
            simp only [u₁, ↓reduceIte, hjpos.ne']
            rcases Nat.eq_zero_or_pos (j - 1) with hj1 | hj1
            · simp [hj1, hu0_lt]
            · exact hu0_lt.trans (u_strict (mem_Iic.mpr (Nat.zero_le n))
                (mem_Iic.mpr (by have := mem_Iic.mp hj; omega)) hj1)
          · have hjpos : 0 < j := hipos.trans hij
            simp only [u₁, hipos.ne', hjpos.ne', ↓reduceIte]
            exact u_strict (mem_Iic.mpr (by have := mem_Iic.mp hi; omega))
              (mem_Iic.mpr (by have := mem_Iic.mp hj; omega)) (by omega)
        · rw [Finset.sum_range_succ']
          have htail :
              (∑ k ∈ Finset.range n, edist (f (u₁ (k + 1 + 1))) (f (u₁ (k + 1)))) =
                ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            simp [u₁]
          rw [htail]
          exact le_self_add
    obtain ⟨n₁, u₁, hu₁0, hu₁n, hu₁_strict, hle1⟩ := hstep1
    have hstep2 : ∃ (N : ℕ) (t : ℕ → ℝ),
        1 ≤ N ∧ t 0 = a ∧ t N = x ∧ StrictMonoOn t (Iic N) ∧
        (∑ i ∈ Finset.range n₁, edist (f (u₁ (i + 1))) (f (u₁ i))) ≤
          ∑ i ∈ Finset.range N, edist (f (t (i + 1))) (f (t i)) := by
      rcases hu₁n.eq_or_lt with hu₁_eq | hu₁_lt
      · have hNpos : 1 ≤ n₁ := by
          by_contra h0
          have hn0 : n₁ = 0 := by omega
          rw [hn0, hu₁0] at hu₁_eq
          exact hlt.ne hu₁_eq
        exact ⟨n₁, u₁, hNpos, hu₁0, hu₁_eq, hu₁_strict, le_rfl⟩
      · let t : ℕ → ℝ := fun k => if k ≤ n₁ then u₁ k else x
        refine ⟨n₁ + 1, t, by omega, by simp [t, hu₁0], by simp [t], ?_, ?_⟩
        · intro i hi j hj hij
          by_cases hjn : j ≤ n₁
          · have hin : i ≤ n₁ := hij.le.trans hjn
            simp only [t, hin, hjn, ↓reduceIte]
            exact hu₁_strict (mem_Iic.mpr hin) (mem_Iic.mpr hjn) hij
          · have hj_eq : j = n₁ + 1 := by have := mem_Iic.mp hj; omega
            have hin : i ≤ n₁ := by omega
            simp only [t, hin, hjn, ↓reduceIte]
            rcases hin.eq_or_lt with rfl | hilt
            · exact hu₁_lt
            · exact (hu₁_strict (mem_Iic.mpr hin) (mem_Iic.mpr le_rfl) hilt).trans hu₁_lt
        · rw [Finset.sum_range_succ]
          have hinit :
              (∑ i ∈ Finset.range n₁, edist (f (t (i + 1))) (f (t i))) =
                ∑ i ∈ Finset.range n₁, edist (f (u₁ (i + 1))) (f (u₁ i)) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have hi_lt : i < n₁ := Finset.mem_range.mp hi
            have hi1 : i + 1 ≤ n₁ := hi_lt
            have hi0 : i ≤ n₁ := hi_lt.le
            simp [t, hi0, hi1]
          rw [hinit]
          exact le_self_add
    obtain ⟨N, t, hN1, ht0, htN, ht_strict, hle2⟩ := hstep2
    exact (hle1.trans hle2).trans (le_iSup
      (fun p : { pair : ℕ × (ℕ → ℝ) //
          1 ≤ pair.1 ∧ pair.2 0 = a ∧ pair.2 pair.1 = x ∧ StrictMonoOn pair.2 (Iic pair.1) } =>
        ∑ i ∈ Finset.range p.1.1, edist (f (p.1.2 (i + 1))) (f (p.1.2 i)))
      ⟨(N, t), hN1, ht0, htN, ht_strict⟩)

/-- **Definition 7.19** (Rudin, pp. 147–148): the real-valued total variation function
`F(x) = sup_{a = t_0 < ⋯ < t_N = x} ∑ |f(t_i) - f(t_{i-1})|` on `[a, b]` (for functions of bounded
variation). -/
def bookVariationReal (f : ℝ → ℝ) (a x : ℝ) : ℝ :=
  (strictPartitionVariationENNReal f a x).toReal

theorem bookVariationReal_eq_toReal_eVariationOn (f : ℝ → ℝ) {a x : ℝ} (hax : a ≤ x) :
    bookVariationReal f a x = (eVariationOn f (Icc a x)).toReal := by
  rw [bookVariationReal, strictPartitionVariationENNReal_eq_eVariationOn f hax]

/-- **Definition 7.19** (Rudin, p. 148): a complex function `f` on `[a, b]` is of *bounded
variation* (`BV`) on `[a, b]` if its strict-partition total variation `F(b)` on `[a, b]` is finite. -/
def BookBoundedVariationOn (f : ℝ → ℂ) (a b : ℝ) : Prop :=
  strictPartitionVariationENNReal f a b < ∞

theorem bookBoundedVariationOn_iff {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) :
    BookBoundedVariationOn f a b ↔ BoundedVariationOn f (Icc a b) := by
  rw [BookBoundedVariationOn, strictPartitionVariationENNReal_eq_eVariationOn f hab,
    BoundedVariationOn, lt_top_iff_ne_top]

private theorem bookVariationReal_sub_eq {f : ℝ → ℝ} {a x y : ℝ} (_hab : a ≤ b)
    (hbv : BoundedVariationOn f (Icc a b)) (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    bookVariationReal f a y - bookVariationReal f a x = (eVariationOn f (Icc x y)).toReal := by
  rw [bookVariationReal_eq_toReal_eVariationOn f (hax.trans hxy),
    bookVariationReal_eq_toReal_eVariationOn f hax]
  have hadd : eVariationOn f (Icc a x) + eVariationOn f (Icc x y) = eVariationOn f (Icc a y) := by
    have h := eVariationOn.Icc_add_Icc f (s := Icc a y) hax hxy ⟨hax, hxy⟩
    have h1 : Icc a y ∩ Icc a x = Icc a x := inter_eq_right.mpr (Icc_subset_Icc_right hxy)
    have h2 : Icc a y ∩ Icc x y = Icc x y := inter_eq_right.mpr (Icc_subset_Icc_left hax)
    simpa [h1, h2] using h
  have hfin_ax : eVariationOn f (Icc a x) ≠ ∞ :=
    hbv.mono (Icc_subset_Icc_right (hxy.trans hyb))
  have hfin_xy : eVariationOn f (Icc x y) ≠ ∞ :=
    hbv.mono (Icc_subset_Icc hax hyb)
  rw [← hadd, ENNReal.toReal_add hfin_ax hfin_xy, add_sub_cancel_left]

/-- **Theorem 7.19** (Rudin, pp. 147–148): if a real function `f` is absolutely continuous on
`[a, b]`, and `F(x)` is its total variation on `[a, x]`, then **all three** functions `F`, `F + f`,
and `F - f` are nondecreasing and absolutely continuous on `[a, b]`. -/
theorem theorem_7_19 {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BookAbsolutelyContinuousOnReal f a b) :
    let F : ℝ → ℝ := bookVariationReal f a
    MonotoneOn F (Icc a b) ∧
      MonotoneOn (F + f) (Icc a b) ∧
      MonotoneOn (F - f) (Icc a b) ∧
      BookAbsolutelyContinuousOnReal F a b ∧
      BookAbsolutelyContinuousOnReal (F + f) a b ∧
      BookAbsolutelyContinuousOnReal (F - f) a b := by
  intro F
  have hmath : AbsolutelyContinuousOnInterval f a b :=
    (bookAbsolutelyContinuousOnReal_iff hab).mp hf
  have hbv : BoundedVariationOn f (Icc a b) := uIcc_of_le hab ▸ hmath.boundedVariationOn
  have hF_mono : MonotoneOn F (Icc a b) := by
    intro x hx y hy hxy
    have hdiff := bookVariationReal_sub_eq hab hbv hx.1 hxy hy.2
    linarith [ENNReal.toReal_nonneg (a := eVariationOn f (Icc x y))]
  have hFf_add_mono : MonotoneOn (F + f) (Icc a b) := by
    intro x hx y hy hxy
    change F x + f x ≤ F y + f y
    have hdiff := bookVariationReal_sub_eq hab hbv hx.1 hxy hy.2
    have hsub : f x - f y ≤ (eVariationOn f (Icc x y)).toReal :=
      (hbv.mono (Icc_subset_Icc hx.1 hy.2)).sub_le ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩
    linarith
  have hFf_sub_mono : MonotoneOn (F - f) (Icc a b) := by
    intro x hx y hy hxy
    change F x - f x ≤ F y - f y
    have hdiff := bookVariationReal_sub_eq hab hbv hx.1 hxy hy.2
    have hsub : f y - f x ≤ (eVariationOn f (Icc x y)).toReal :=
      (hbv.mono (Icc_subset_Icc hx.1 hy.2)).sub_le ⟨hxy, le_rfl⟩ ⟨le_rfl, hxy⟩
    linarith
  have hF_ac : BookAbsolutelyContinuousOnReal F a b := by
    intro ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ := hf (ε / 2) (by positivity)
    refine ⟨δ, hδ_pos, ?_⟩
    intro m α β hsub hpdisj hlen
    cases m with
    | zero => simpa using hε
    | succ m' =>
        let η : ℝ := ε / (2 * ((m' + 1 : ℕ) : ℝ))
        have hη_pos : 0 < η := by positivity
        have hex_part : ∀ k : Fin (m' + 1),
            ∃ (n : ℕ) (u : ℕ → ℝ),
              StrictMonoOn u (Iic n) ∧ (∀ j ∈ Iic n, u j ∈ Icc (α k) (β k)) ∧
              (eVariationOn f (Icc (α k) (β k))).toReal - η ≤
                ∑ j : Fin n, |f (u (j.1 + 1)) - f (u j.1)| := by
          intro k
          have hfin_k : eVariationOn f (Icc (α k) (β k)) ≠ ∞ :=
            hbv.mono (Icc_subset_Icc (hsub k).1 (hsub k).2.2)
          by_cases hle : (eVariationOn f (Icc (α k) (β k))).toReal ≤ η
          · refine ⟨0, fun _ => α k, ?_, fun _ _ => ⟨le_rfl, (hsub k).2.1.le⟩, ?_⟩
            · intro i hi j hj hij
              have hi0 : i = 0 := Nat.le_zero.mp (mem_Iic.mp hi)
              have hj0 : j = 0 := Nat.le_zero.mp (mem_Iic.mp hj)
              omega
            · simp; linarith
          · push Not at hle
            have hv_pos : 0 < (eVariationOn f (Icc (α k) (β k))).toReal := hη_pos.trans hle
            have hlt_sup :
                ENNReal.ofReal ((eVariationOn f (Icc (α k) (β k))).toReal - η) <
                  eVariationOn f (Icc (α k) (β k)) := by
              conv_rhs => rw [← ENNReal.ofReal_toReal hfin_k]
              exact (ENNReal.ofReal_lt_ofReal_iff hv_pos).mpr (by linarith)
            conv_rhs at hlt_sup => rw [eVariationOn.eVariationOn_eq_strictMonoOn]
            obtain ⟨⟨n, ⟨u, u_strict, u_mem⟩⟩, hsum_gt⟩ := lt_iSup_iff.mp hlt_sup
            refine ⟨n, u, u_strict, u_mem, ?_⟩
            have hsum_eq :
                ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) =
                  ENNReal.ofReal (∑ j : Fin n, |f (u (j.1 + 1)) - f (u j.1)|) := by
              rw [← Fin.sum_univ_eq_sum_range,
                ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [edist_dist, Real.dist_eq]
            rw [hsum_eq] at hsum_gt
            have hsum_pos : 0 < ∑ j : Fin n, |f (u (j.1 + 1)) - f (u j.1)| := by
              by_contra hnp
              push Not at hnp
              rw [ENNReal.ofReal_of_nonpos hnp] at hsum_gt
              exact not_lt_zero hsum_gt
            exact ((ENNReal.ofReal_lt_ofReal_iff hsum_pos).mp hsum_gt).le
        choose n u hu_strict hu_mem hu_sum using hex_part
        classical
        let Idx := Σ k : Fin (m' + 1), Fin (n k)
        let M : ℕ := Fintype.card Idx
        let eqv : Fin M ≃ Idx := (Fintype.equivFin Idx).symm
        let α' : Fin M → ℝ := fun idx => u (eqv idx).1 (eqv idx).2.1
        let β' : Fin M → ℝ := fun idx => u (eqv idx).1 ((eqv idx).2.1 + 1)
        have hsub' : ∀ idx : Fin M, a ≤ α' idx ∧ α' idx < β' idx ∧ β' idx ≤ b := by
          intro idx
          let k := (eqv idx).1
          let j := (eqv idx).2
          have hj0 : j.1 ∈ Iic (n k) := mem_Iic.mpr j.2.le
          have hj1 : j.1 + 1 ∈ Iic (n k) := mem_Iic.mpr j.2
          have hm0 := hu_mem k j.1 hj0
          have hm1 := hu_mem k (j.1 + 1) hj1
          exact ⟨(hsub k).1.trans hm0.1,
            hu_strict k hj0 hj1 (Nat.lt_succ_self j.1),
            hm1.2.trans (hsub k).2.2⟩
        have hpdisj' : Pairwise fun i₁ i₂ : Fin M =>
            Disjoint (Ioo (α' i₁) (β' i₁)) (Ioo (α' i₂) (β' i₂)) := by
          intro i₁ i₂ hne
          have hsigma_ne : eqv i₁ ≠ eqv i₂ := fun h => hne (eqv.injective h)
          by_cases hk : (eqv i₁).1 = (eqv i₂).1
          · let k := (eqv i₁).1
            let j₁ : ℕ := (eqv i₁).2.1
            let j₂ : ℕ := (eqv i₂).2.1
            have hj₁_lt : j₁ < n k := (eqv i₁).2.2
            have hj₂_lt : j₂ < n k := by
              dsimp [j₂, k]
              rw [hk]
              exact (eqv i₂).2.2
            have hj_ne : j₁ ≠ j₂ := by
              intro hjeq
              apply hsigma_ne
              rcases h1 : eqv i₁ with ⟨k₁, idx₁⟩
              rcases h2 : eqv i₂ with ⟨k₂, idx₂⟩
              have hk' : k₁ = k₂ := by simpa [h1, h2] using hk
              have hj' : idx₁.1 = idx₂.1 := by
                dsimp only [j₁, j₂] at hjeq
                rw [h1, h2] at hjeq
                exact hjeq
              subst hk'
              exact congrArg (Sigma.mk k₁) (Fin.ext hj')
            have hα₁ : α' i₁ = u k j₁ := rfl
            have hβ₁ : β' i₁ = u k (j₁ + 1) := rfl
            have hα₂ : α' i₂ = u k j₂ := by dsimp [α', k, j₂]; rw [hk]
            have hβ₂ : β' i₂ = u k (j₂ + 1) := by dsimp [β', k, j₂]; rw [hk]
            rw [Set.disjoint_left]
            intro x hx1 hx2
            rw [hα₁, hβ₁] at hx1
            rw [hα₂, hβ₂] at hx2
            rcases lt_or_gt_of_ne hj_ne with hlt | hgt
            · have hsucc : j₁ + 1 ≤ j₂ := hlt
              have hle : u k (j₁ + 1) ≤ u k j₂ := by
                rcases hsucc.eq_or_lt with heq | hlt2
                · rw [heq]
                · exact (hu_strict k (mem_Iic.mpr hj₁_lt) (mem_Iic.mpr hj₂_lt.le) hlt2).le
              linarith [hx1.2, hx2.1]
            · have hsucc : j₂ + 1 ≤ j₁ := hgt
              have hle : u k (j₂ + 1) ≤ u k j₁ := by
                rcases hsucc.eq_or_lt with heq | hlt2
                · rw [heq]
                · exact (hu_strict k (mem_Iic.mpr hj₂_lt) (mem_Iic.mpr hj₁_lt.le) hlt2).le
              linarith [hx2.2, hx1.1]
          · refine (hpdisj hk).mono ?_ ?_
            · intro x hx
              have hm0 := hu_mem (eqv i₁).1 (eqv i₁).2.1 (mem_Iic.mpr (eqv i₁).2.2.le)
              have hm1 := hu_mem (eqv i₁).1 ((eqv i₁).2.1 + 1) (mem_Iic.mpr (eqv i₁).2.2)
              exact ⟨hm0.1.trans_lt hx.1, hx.2.trans_le hm1.2⟩
            · intro x hx
              have hm0 := hu_mem (eqv i₂).1 (eqv i₂).2.1 (mem_Iic.mpr (eqv i₂).2.2.le)
              have hm1 := hu_mem (eqv i₂).1 ((eqv i₂).2.1 + 1) (mem_Iic.mpr (eqv i₂).2.2)
              exact ⟨hm0.1.trans_lt hx.1, hx.2.trans_le hm1.2⟩
        have hlen' : (∑ idx : Fin M, (β' idx - α' idx)) < δ := by
          have hle_sum : (∑ idx : Fin M, (β' idx - α' idx)) ≤ ∑ k : Fin (m' + 1), (β k - α k) := by
            calc
              ∑ idx : Fin M, (β' idx - α' idx)
                = ∑ s : Idx, (u s.1 (s.2.1 + 1) - u s.1 s.2.1) :=
                  Equiv.sum_comp eqv fun s : Idx => u s.1 (s.2.1 + 1) - u s.1 s.2.1
              _ = ∑ k : Fin (m' + 1), ∑ j : Fin (n k), (u k (j.1 + 1) - u k j.1) :=
                  Fintype.sum_sigma fun s : Idx => u s.1 (s.2.1 + 1) - u s.1 s.2.1
              _ ≤ ∑ k : Fin (m' + 1), (β k - α k) := by
                  refine Finset.sum_le_sum fun k _ => ?_
                  rw [Fin.sum_univ_eq_sum_range (fun j => u k (j + 1) - u k j) (n k),
                    Finset.sum_range_sub (fun j => u k j) (n k)]
                  have hm0 := hu_mem k 0 (mem_Iic.mpr (Nat.zero_le _))
                  have hmn := hu_mem k (n k) (mem_Iic.mpr le_rfl)
                  linarith [hm0.1, hmn.2]
          exact hle_sum.trans_lt hlen
        have hsum_f := hδ M α' β' hsub' hpdisj' hlen'
        have hsigma_eq :
            (∑ k : Fin (m' + 1), ∑ j : Fin (n k), |f (u k (j.1 + 1)) - f (u k j.1)|) =
              ∑ idx : Fin M, |f (β' idx) - f (α' idx)| := by
          symm
          calc
            ∑ idx : Fin M, |f (β' idx) - f (α' idx)|
              = ∑ s : Idx, |f (u s.1 (s.2.1 + 1)) - f (u s.1 s.2.1)| :=
                Equiv.sum_comp eqv fun s : Idx => |f (u s.1 (s.2.1 + 1)) - f (u s.1 s.2.1)|
            _ = ∑ k : Fin (m' + 1), ∑ j : Fin (n k), |f (u k (j.1 + 1)) - f (u k j.1)| :=
                Fintype.sum_sigma fun s : Idx => |f (u s.1 (s.2.1 + 1)) - f (u s.1 s.2.1)|
        calc
          ∑ k : Fin (m' + 1), |F (β k) - F (α k)|
            = ∑ k : Fin (m' + 1), (eVariationOn f (Icc (α k) (β k))).toReal := by
                refine Finset.sum_congr rfl fun k _ => ?_
                have hdiff := bookVariationReal_sub_eq hab hbv
                  (hsub k).1 (hsub k).2.1.le (hsub k).2.2
                change |F (β k) - F (α k)| = _
                rw [hdiff, abs_of_nonneg ENNReal.toReal_nonneg]
          _ ≤ ∑ k : Fin (m' + 1),
                (η + ∑ j : Fin (n k), |f (u k (j.1 + 1)) - f (u k j.1)|) := by
                refine Finset.sum_le_sum fun k _ => ?_
                linarith [hu_sum k]
          _ = ((m' + 1 : ℕ) : ℝ) * η +
                ∑ idx : Fin M, |f (β' idx) - f (α' idx)| := by
                rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                  nsmul_eq_mul, hsigma_eq]
          _ = ε / 2 + ∑ idx : Fin M, |f (β' idx) - f (α' idx)| := by
                have hne : ((m' + 1 : ℕ) : ℝ) ≠ 0 := by positivity
                congr 1
                dsimp [η]
                field_simp [hne]
          _ < ε / 2 + ε / 2 := by linarith [hsum_f]
          _ = ε := add_halves ε
  have hF_ac_math : AbsolutelyContinuousOnInterval F a b :=
    (bookAbsolutelyContinuousOnReal_iff hab).mp hF_ac
  have hFf_add_ac : BookAbsolutelyContinuousOnReal (F + f) a b :=
    (bookAbsolutelyContinuousOnReal_iff hab).mpr (hF_ac_math.add hmath)
  have hFf_sub_ac : BookAbsolutelyContinuousOnReal (F - f) a b :=
    (bookAbsolutelyContinuousOnReal_iff hab).mpr (hF_ac_math.sub hmath)
  exact ⟨hF_mono, hFf_add_mono, hFf_sub_mono, hF_ac, hFf_add_ac, hFf_sub_ac⟩

end Node7_19

section Node7_20

/-- **Theorem 7.20** (Rudin, p. 148): if a complex function `f` is absolutely continuous on
`[a, b]`, then `f` is differentiable almost everywhere on `[a, b]`, `f' ∈ L¹([a, b])`, and
`f(x) - f(a) = ∫_a^x f'(t) dt` for **every** `x ∈ [a, b]`. -/
theorem theorem_7_20 {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : BookAbsolutelyContinuousOn f a b) :
    (∀ᵐ x ∂(volume.restrict (Icc a b)), DifferentiableAt ℝ f x) ∧
      IntegrableOn (deriv f) (Icc a b) volume ∧
      ∀ x ∈ Icc a b, f x - f a = ∫ t in a..x, deriv f t := by
  have hmath : AbsolutelyContinuousOnInterval f a b :=
    (bookAbsolutelyContinuousOn_iff hab).mp hf
  have hae_uIcc : ∀ᵐ x ∂volume, x ∈ uIcc a b → DifferentiableAt ℝ f x :=
    hmath.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  have hae_restr : ∀ᵐ x ∂(volume.restrict (Icc a b)), DifferentiableAt ℝ f x := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hae_uIcc] with x hx hxIcc
    exact hx (uIcc_of_le hab ▸ hxIcc)
  let fre : ℝ → ℝ := fun t => (f t).re
  let fim : ℝ → ℝ := fun t => (f t).im
  have hac_re : AbsolutelyContinuousOnInterval fre a b :=
    Complex.reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hmath
  have hac_im : AbsolutelyContinuousOnInterval fim a b :=
    Complex.imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hmath
  have hint_re : IntegrableOn (deriv fre) (Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hac_re.intervalIntegrable_deriv
  have hint_im : IntegrableOn (deriv fim) (Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hac_im.intervalIntegrable_deriv
  have hae_deriv_decomp :
      ∀ᵐ x ∂(volume.restrict (Icc a b)),
        deriv f x = Complex.ofReal (deriv fre x) + Complex.ofReal (deriv fim x) * Complex.I := by
    filter_upwards [hae_restr] with x hx
    have hre_d : HasDerivAt fre (deriv f x).re x :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hx.hasDerivAt
    have him_d : HasDerivAt fim (deriv f x).im x :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hx.hasDerivAt
    rw [hre_d.deriv, him_d.deriv]
    exact (Complex.re_add_im (deriv f x)).symm
  have hint_comb : IntegrableOn
      (fun x : ℝ => Complex.ofReal (deriv fre x) + Complex.ofReal (deriv fim x) * Complex.I)
      (Icc a b) volume :=
    (Complex.ofRealCLM.integrable_comp hint_re).add
      ((Complex.ofRealCLM.integrable_comp hint_im).mul_const Complex.I)
  have hint_f : IntegrableOn (deriv f) (Icc a b) volume :=
    hint_comb.congr_fun_ae (Filter.EventuallyEq.symm hae_deriv_decomp)
  refine ⟨hae_restr, hint_f, ?_⟩
  intro x hx
  have hsub_ax : uIcc a x ⊆ uIcc a b := by
    rw [uIcc_of_le hx.1, uIcc_of_le hab]
    exact Icc_subset_Icc_right hx.2
  have hftc_re : ∫ t in a..x, deriv fre t = fre x - fre a :=
    (hac_re.mono hsub_ax).integral_deriv_eq_sub
  have hftc_im : ∫ t in a..x, deriv fim t = fim x - fim a :=
    (hac_im.mono hsub_ax).integral_deriv_eq_sub
  have hint_ax : IntervalIntegrable (deriv f) volume a x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx.1).mpr
      (hint_f.mono_set (Icc_subset_Icc_right hx.2))
  have hae_uIoc_ax : ∀ᵐ t ∂volume, t ∈ uIoc a x → DifferentiableAt ℝ f t := by
    filter_upwards [hae_uIcc] with t ht ht_ax
    exact ht (hsub_ax (uIoc_subset_uIcc ht_ax))
  have hre_int : (∫ t in a..x, deriv f t).re = ∫ t in a..x, deriv fre t := by
    change Complex.reCLM (∫ t in a..x, deriv f t) = _
    rw [← Complex.reCLM.intervalIntegral_comp_comm hint_ax]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae_uIoc_ax] with t ht ht_mem
    have hd : HasDerivAt fre (deriv f t).re t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (ht ht_mem).hasDerivAt
    exact hd.deriv.symm
  have him_int : (∫ t in a..x, deriv f t).im = ∫ t in a..x, deriv fim t := by
    change Complex.imCLM (∫ t in a..x, deriv f t) = _
    rw [← Complex.imCLM.intervalIntegral_comp_comm hint_ax]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae_uIoc_ax] with t ht ht_mem
    have hd : HasDerivAt fim (deriv f t).im t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (ht ht_mem).hasDerivAt
    exact hd.deriv.symm
  apply Complex.ext
  · simp [Complex.sub_re, fre, hre_int, hftc_re]
  · simp [Complex.sub_im, fim, him_int, hftc_im]

end Node7_20

section Node7_21

/-- **Theorem 7.21** (Rudin, pp. 149–150, explicit domain/endpoint derivative form): if a real
function `f` has derivative `f'(t)` relative to `[a, b]` at **every** point `t ∈ [a, b]` (the
natural one-sided derivative at `a` and `b`) and `f' ∈ L¹([a, b])`, then
`f(x) - f(a) = ∫_a^x f'(t) dt` for every `x ∈ [a, b]`. -/
theorem theorem_7_21_hasDerivWithinAt {f f' : ℝ → ℝ} {a b : ℝ} (_hab : a ≤ b)
    (hderiv : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t)
    (hint : IntegrableOn f' (Icc a b) volume) :
    ∀ x ∈ Icc a b, f x - f a = ∫ t in a..x, f' t := by
  intro x hx
  rcases hx.1.eq_or_lt with rfl | hax_lt
  · simp
  have hcont_ab : ContinuousOn f (Icc a b) := fun t ht => (hderiv t ht).continuousWithinAt
  have hcont_ax : ContinuousOn f (Icc a x) := hcont_ab.mono (Icc_subset_Icc_right hx.2)
  have hderiv_Ioo : ∀ t ∈ Ioo a x, HasDerivAt f (f' t) t := by
    intro t ht
    have ht_Ioo_ab : t ∈ Ioo a b := ⟨ht.1, ht.2.trans_le hx.2⟩
    exact (hderiv t (Ioo_subset_Icc_self ht_Ioo_ab)).hasDerivAt
      (Icc_mem_nhds ht_Ioo_ab.1 ht_Ioo_ab.2)
  have hint_ax : IntervalIntegrable f' volume a x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hax_lt.le).mpr
      (hint.mono_set (Icc_subset_Icc_right hx.2))
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hax_lt.le hcont_ax hderiv_Ioo hint_ax).symm

/-- **Theorem 7.21** (Rudin, pp. 149–150): if `f : ℝ → ℝ` is differentiable relative to `[a, b]`
at **every** point of `[a, b]` and `derivWithin f (Icc a b) ∈ L¹([a, b])`, then
`f(x) - f(a) = ∫_a^x derivWithin f (Icc a b) t dt` for every `x ∈ [a, b]`. -/
theorem theorem_7_21 {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hdiff : ∀ t ∈ Icc a b, DifferentiableWithinAt ℝ f (Icc a b) t)
    (hint : IntegrableOn (derivWithin f (Icc a b)) (Icc a b) volume) :
    ∀ x ∈ Icc a b, f x - f a = ∫ t in a..x, derivWithin f (Icc a b) t :=
  theorem_7_21_hasDerivWithinAt hab (fun t ht => (hdiff t ht).hasDerivWithinAt) hint

/-- **Theorem 7.21** (two-sided everywhere-differentiable specialization): if `f : ℝ → ℝ` is
differentiable at every `t ∈ [a, b]` and `deriv f ∈ L¹([a, b])`, then
`f(x) - f(a) = ∫_a^x f'(t) dt` for every `x ∈ [a, b]`. -/
theorem theorem_7_21_everywhere {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hdiff : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hint : IntegrableOn (deriv f) (Icc a b) volume) :
    ∀ x ∈ Icc a b, f x - f a = ∫ t in a..x, deriv f t :=
  theorem_7_21_hasDerivWithinAt hab (fun t ht => (hdiff t ht).hasDerivAt.hasDerivWithinAt) hint

end Node7_21

/-! ## §7.22–7.26: Differentiable transformations on `ℝ^k` and change of variables -/

section Node7_22

/-- **Definition 7.22** (Rudin, p. 150): a mapping `T` into `ℝ^k` is differentiable at `x ∈ ℝ^k`
with linear derivative `A : ℝ^k →ₗ[ℝ] ℝ^k` if
`lim_{h → 0, h ≠ 0} ‖T(x + h) - T(x) - A h‖ / ‖h‖ = 0`. -/
def BookHasFDerivAt {k : ℕ}
    (T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
    (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (x : EuclideanSpace ℝ (Fin k)) : Prop :=
  Tendsto (fun h : EuclideanSpace ℝ (Fin k) => ‖T (x + h) - T x - A h‖ / ‖h‖) (𝓝[≠] 0) (𝓝 0)

/-- Bridge between Rudin's Euclidean difference-quotient derivative `BookHasFDerivAt` and Mathlib's
`HasFDerivAt`. -/
theorem bookHasFDerivAt_iff_hasFDerivAt {k : ℕ}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)}
    {x : EuclideanSpace ℝ (Fin k)} :
    BookHasFDerivAt T A x ↔ HasFDerivAt T A.toContinuousLinearMap x := by
  let φ : EuclideanSpace ℝ (Fin k) → ℝ := fun h => ‖T (x + h) - T x - A h‖ / ‖h‖
  have hφ0 : φ 0 = 0 := by simp [φ]
  have hpunc : Tendsto φ (𝓝[≠] 0) (𝓝 0) ↔ Tendsto φ (𝓝 0) (𝓝 0) := by
    rw [← hφ0]
    exact continuousAt_iff_punctured_nhds.symm
  rw [BookHasFDerivAt, show (fun h => ‖T (x + h) - T x - A h‖ / ‖h‖) = φ from rfl,
    hpunc, hasFDerivAt_iff_isLittleO_nhds_zero]
  change Tendsto φ (𝓝 0) (𝓝 0) ↔ (fun h => T (x + h) - T x - A h) =o[𝓝 0] fun h => h
  rw [← Asymptotics.isLittleO_norm_norm,
    Asymptotics.isLittleO_iff_tendsto (fun h hh => by
      rw [norm_eq_zero.mp hh]; simp)]

/-- On an open set `V ⊆ ℝ^k`, `BookHasFDerivAt T A x` at `x ∈ V` depends only on `T` near `x` in `V`
and coincides with `HasFDerivWithinAt T A.toContinuousLinearMap V x`. -/
theorem bookHasFDerivAt_iff_hasFDerivWithinAt_open {k : ℕ}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)}
    {V : Set (EuclideanSpace ℝ (Fin k))} {x : EuclideanSpace ℝ (Fin k)}
    (hV : IsOpen V) (hx : x ∈ V) :
    BookHasFDerivAt T A x ↔ HasFDerivWithinAt T A.toContinuousLinearMap V x := by
  rw [bookHasFDerivAt_iff_hasFDerivAt]
  exact ⟨fun h => h.hasFDerivWithinAt, fun h => h.hasFDerivAt (hV.mem_nhds hx)⟩

/-- **Assertion 7.22 (uniqueness)** (Rudin, p. 150): there is at most one linear operator `A`
satisfying `BookHasFDerivAt T A x`. -/
theorem BookHasFDerivAt.unique {k : ℕ}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {A₁ A₂ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)}
    {x : EuclideanSpace ℝ (Fin k)}
    (h₁ : BookHasFDerivAt T A₁ x) (h₂ : BookHasFDerivAt T A₂ x) :
    A₁ = A₂ := by
  have hclm : A₁.toContinuousLinearMap = A₂.toContinuousLinearMap :=
    (bookHasFDerivAt_iff_hasFDerivAt.mp h₁).unique (bookHasFDerivAt_iff_hasFDerivAt.mp h₂)
  exact LinearMap.ext fun v => DFunLike.congr_fun hclm v

/-- **Assertion 7.22 (`T'(x) = A`)** (Rudin, p. 150): when `BookHasFDerivAt T A x` holds, the Fréchet
derivative `fderiv ℝ T x` equals `A`. -/
theorem BookHasFDerivAt.fderiv_eq {k : ℕ}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)}
    {x : EuclideanSpace ℝ (Fin k)} (h : BookHasFDerivAt T A x) :
    (fderiv ℝ T x).toLinearMap = A :=
  LinearMap.ext fun v => DFunLike.congr_fun (bookHasFDerivAt_iff_hasFDerivAt.mp h).fderiv v

/-- Canonical continuous linear equivalence identifying `ℝ^1` (`EuclideanSpace ℝ (Fin 1)`) with `ℝ`. -/
def euclideanFin1Equiv : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 1 => ℝ)).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)

/-- **Assertion 7.22 (one-variable agreement)** (Rudin, p. 150): for `k = 1`, `BookHasFDerivAt`
agrees with the ordinary one-variable derivative `HasDerivAt`. -/
theorem bookHasFDerivAt_fin1_iff_hasDerivAt {g : ℝ → ℝ} {c x : ℝ} :
    BookHasFDerivAt (euclideanFin1Equiv.symm ∘ g ∘ euclideanFin1Equiv)
      (c • LinearMap.id) (euclideanFin1Equiv.symm x) ↔ HasDerivAt g c x := by
  rw [bookHasFDerivAt_iff_hasFDerivAt, hasDerivAt_iff_hasFDerivAt]
  constructor
  · intro h
    have hcomp :
        HasFDerivAt
          ((euclideanFin1Equiv : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) ∘
            (euclideanFin1Equiv.symm ∘ g ∘ euclideanFin1Equiv) ∘
            (euclideanFin1Equiv.symm : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)))
          ((euclideanFin1Equiv : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).comp
            (((c • LinearMap.id :
                EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)).toContinuousLinearMap).comp
              (euclideanFin1Equiv.symm : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)))) x := by
      have h1 :
          HasFDerivAt
            ((euclideanFin1Equiv.symm ∘ g ∘ euclideanFin1Equiv) ∘
              (euclideanFin1Equiv.symm : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)))
            (((c • LinearMap.id :
                EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)).toContinuousLinearMap).comp
              (euclideanFin1Equiv.symm : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1))) x :=
        h.comp x (euclideanFin1Equiv.symm : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).hasFDerivAt
      exact (euclideanFin1Equiv : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).hasFDerivAt.comp x h1
    have hfun :
        ((euclideanFin1Equiv : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) ∘
          (euclideanFin1Equiv.symm ∘ g ∘ euclideanFin1Equiv) ∘
          (euclideanFin1Equiv.symm : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1))) = g := by
      ext t
      simp
    have hlin :
        ((euclideanFin1Equiv : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).comp
          (((c • LinearMap.id :
              EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)).toContinuousLinearMap).comp
            (euclideanFin1Equiv.symm : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)))) =
          ContinuousLinearMap.toSpanSingleton ℝ c := by
      refine ContinuousLinearMap.ext fun t => ?_
      change euclideanFin1Equiv (c • euclideanFin1Equiv.symm t) = t • c
      rw [map_smul, euclideanFin1Equiv.apply_symm_apply, smul_eq_mul, smul_eq_mul, mul_comm]
    rwa [hfun, hlin] at hcomp
  · intro h
    have hx_eq : euclideanFin1Equiv (euclideanFin1Equiv.symm x) = x :=
      euclideanFin1Equiv.apply_symm_apply x
    have h1 :
        HasFDerivAt (g ∘ (euclideanFin1Equiv : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ))
          ((ContinuousLinearMap.toSpanSingleton ℝ c).comp
            (euclideanFin1Equiv : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ))
          (euclideanFin1Equiv.symm x) :=
      (hx_eq ▸ h).comp (euclideanFin1Equiv.symm x)
        (euclideanFin1Equiv : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).hasFDerivAt
    have hcomp :
        HasFDerivAt (euclideanFin1Equiv.symm ∘ g ∘ euclideanFin1Equiv)
          ((euclideanFin1Equiv.symm : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).comp
            ((ContinuousLinearMap.toSpanSingleton ℝ c).comp
              (euclideanFin1Equiv : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)))
          (euclideanFin1Equiv.symm x) :=
      (euclideanFin1Equiv.symm : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).hasFDerivAt.comp
        (euclideanFin1Equiv.symm x) h1
    have hlin :
        ((euclideanFin1Equiv.symm : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).comp
          ((ContinuousLinearMap.toSpanSingleton ℝ c).comp
            (euclideanFin1Equiv : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ))) =
          (c • LinearMap.id :
            EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)).toContinuousLinearMap := by
      refine ContinuousLinearMap.ext fun p => ?_
      change euclideanFin1Equiv.symm ((euclideanFin1Equiv p) • c) = c • p
      have hsc : (euclideanFin1Equiv p) • c = euclideanFin1Equiv (c • p) := by
        rw [map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
      rw [hsc, euclideanFin1Equiv.symm_apply_apply]
    rwa [hlin] at hcomp

/-- **Assertion 7.22 (linear operator derivative)** (Rudin, p. 150): every linear operator `A` on
`ℝ^k` has `A'(x) = A` at every `x ∈ ℝ^k`. -/
theorem bookHasFDerivAt_linearMap {k : ℕ}
    (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (x : EuclideanSpace ℝ (Fin k)) :
    BookHasFDerivAt A A x :=
  bookHasFDerivAt_iff_hasFDerivAt.mpr A.toContinuousLinearMap.hasFDerivAt

theorem fderiv_linearMap_eq {k : ℕ}
    (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (x : EuclideanSpace ℝ (Fin k)) :
    (fderiv ℝ A x).toLinearMap = A :=
  (bookHasFDerivAt_linearMap A x).fderiv_eq

/-- Half-open unit cube `[0, 1)^k ⊆ ℝ^k` of Lebesgue measure `1`. -/
def unitCube (k : ℕ) : Set (EuclideanSpace ℝ (Fin k)) :=
  {x | ∀ i : Fin k, x.ofLp i ∈ Ico (0 : ℝ) 1}

theorem measurableSet_unitCube (k : ℕ) : MeasurableSet (unitCube k) := by
  have heq : unitCube k =
      (@WithLp.ofLp 2 (Fin k → ℝ)) ⁻¹' Set.pi univ (fun _ : Fin k => Ico (0 : ℝ) 1) := by
    ext x
    simp [unitCube]
  rw [heq]
  exact (MeasurableSet.univ_pi fun _ => measurableSet_Ico).preimage
    (PiLp.volume_preserving_ofLp (Fin k)).measurable

theorem volume_unitCube (k : ℕ) : volume (unitCube k) = 1 := by
  have heq : (@WithLp.toLp 2 (Fin k → ℝ)) ⁻¹' unitCube k =
      Set.pi univ (fun _ : Fin k => Ico (0 : ℝ) 1) := by
    ext x
    simp [unitCube]
  rw [← (PiLp.volume_preserving_toLp (Fin k)).measure_preimage
      (measurableSet_unitCube k).nullMeasurableSet,
    heq, volume_pi_pi]
  simp [Real.volume_Ico]

/-- **Definition 7.22 (`Δ(A)`)** (Rudin, p. 150): the modulus `Δ(A) = |det A|` of a linear operator
`A` on `ℝ^k`. -/
def linearModulus {k : ℕ}
    (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) : ℝ :=
  |LinearMap.det A|

/-- **Assertion 7.22 (`m(A(E)) = Δ(A) m(E)`)** (Rudin, p. 150): for every linear operator `A` on
`ℝ^k` and every subset `E ⊆ ℝ^k`, `m(A(E)) = Δ(A) m(E)` with `Δ(A) = |det A|`. -/
theorem volume_image_linearMap_eq_linearModulus {k : ℕ}
    (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (E : Set (EuclideanSpace ℝ (Fin k))) :
    volume (A '' E) = ENNReal.ofReal (linearModulus A) * volume E :=
  volume.addHaar_image_linearMap A E

/-- On the unit cube `Q = [0, 1)^k` of volume `1`, `m(A(Q)) = Δ(A) = |det A|`. -/
theorem volume_image_linearMap_unitCube {k : ℕ}
    (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) :
    volume (A '' unitCube k) = ENNReal.ofReal (linearModulus A) := by
  rw [volume_image_linearMap_eq_linearModulus, volume_unitCube, mul_one]

/-- **Definition 7.22 (Jacobian)** (Rudin, p. 150): the Jacobian `J_T(x) = det T'(x)` of a
mapping `T : ℝ^k → ℝ^k` at `x`. -/
def jacobian {k : ℕ}
    (T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
    (x : EuclideanSpace ℝ (Fin k)) : ℝ :=
  (fderiv ℝ T x).det

/-- **Assertion 7.22 (`Δ(T'(x)) = |J_T(x)|`)** (Rudin, p. 150). -/
theorem abs_jacobian_eq_linearModulus {k : ℕ}
    (T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
    (x : EuclideanSpace ℝ (Fin k)) :
    |jacobian T x| = linearModulus (fderiv ℝ T x).toLinearMap :=
  rfl

theorem BookHasFDerivAt.jacobian_eq_det {k : ℕ}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)}
    {x : EuclideanSpace ℝ (Fin k)} (h : BookHasFDerivAt T A x) :
    jacobian T x = LinearMap.det A ∧ |jacobian T x| = linearModulus A := by
  have hd : jacobian T x = LinearMap.det A := by
    change LinearMap.det (fderiv ℝ T x).toLinearMap = LinearMap.det A
    rw [h.fderiv_eq]
  exact ⟨hd, by rw [hd, linearModulus]⟩

end Node7_22

section Node7_23

open Classical
open scoped RealInnerProductSpace

/-! ### Part 1: Kuhn's cubical Sperner lemma -/

abbrev CubeVertex (k N : ℕ) := Fin k → Fin (N + 2)

abbrev KuhnSimplex (k N : ℕ) := (Fin k → Fin (N + 1)) × Equiv.Perm (Fin k)

def kuhnVertex {k N : ℕ} (s : KuhnSimplex k N) (m : Fin (k + 1)) (i : Fin k) : Fin (N + 2) :=
  ⟨(s.1 i).val + if (s.2.symm i).val < m.val then 1 else 0, by
    have hi := (s.1 i).isLt
    split_ifs <;> omega⟩

def IsCubicalSperner {k N : ℕ} (c : CubeVertex k N → Fin (k + 1)) : Prop :=
  (∀ v (i : Fin k), (v i).val = 0 → c v ≠ i.castSucc) ∧
  (∀ v (i : Fin k), (v i).val = N + 1 → (c v).val ≤ i.val)

def IsSubPan {d : ℕ} (f : Fin (d + 2) → Fin (d + 2)) (m : Fin (d + 2)) : Prop :=
  ∀ j : Fin (d + 1), ∃ r ≠ m, f r = j.castSucc

private theorem even_card_of_involution {α : Type*} [DecidableEq α] :
    ∀ (n : ℕ) (S : Finset α) (τ : α → α),
      S.card = n →
      (∀ x ∈ S, τ x ∈ S) →
      (∀ x ∈ S, τ (τ x) = x) →
      (∀ x ∈ S, τ x ≠ x) →
      S.card % 2 = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S τ hcard hmem hinv hne
    by_cases hS : S = ∅
    · subst hS; simp
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      have hτx : τ x ∈ S := hmem x hx
      have hτx_ne : τ x ≠ x := hne x hx
      have hτx_erase : τ x ∈ S.erase x := Finset.mem_erase.mpr ⟨hτx_ne, hτx⟩
      let S' := (S.erase x).erase (τ x)
      have hcard1 : (S.erase x).card + 1 = S.card := Finset.card_erase_add_one hx
      have hcard2 : S'.card + 1 = (S.erase x).card := Finset.card_erase_add_one hτx_erase
      have hlt : S'.card < n := by omega
      have hS'_even : S'.card % 2 = 0 := by
        apply ih S'.card hlt S' τ rfl
        · intro y hy
          have hy1 : y ≠ τ x ∧ y ∈ S.erase x := Finset.mem_erase.mp hy
          have hy2 : y ≠ x ∧ y ∈ S := Finset.mem_erase.mp hy1.2
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hmem y hy2.2⟩⟩
          · intro heq
            apply hy2.1
            calc
              y = τ (τ y) := (hinv y hy2.2).symm
              _ = τ (τ x) := by rw [heq]
              _ = x := hinv x hx
          · intro heq
            apply hy1.1
            calc
              y = τ (τ y) := (hinv y hy2.2).symm
              _ = τ x := by rw [heq]
        · intro y hy
          exact hinv y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
        · intro y hy
          exact hne y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
      omega

private theorem subPan_card_mod_two {d : ℕ} (f : Fin (d + 2) → Fin (d + 2)) :
    (Finset.univ.filter (fun m => IsSubPan f m)).card % 2 =
      if Function.Surjective f then 1 else 0 := by
  by_cases hsurj : Function.Surjective f
  · simp only [hsurj, ↓reduceIte]
    have hbij : Function.Bijective f := Finite.surjective_iff_bijective.mp hsurj
    obtain ⟨m₀, hm₀⟩ := hsurj (Fin.last (d + 1))
    have hset : Finset.univ.filter (fun m => IsSubPan f m) = {m₀} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hm
        by_cases hlast : f m = Fin.last (d + 1)
        · exact hbij.1 (hlast.trans hm₀.symm)
        · let j : Fin (d + 1) := (f m).castPred hlast
          obtain ⟨r, hrm, hfr⟩ := hm j
          have hfm : j.castSucc = f m := Fin.castSucc_castPred (f m) hlast
          exact False.elim (hrm (hbij.1 (hfr.trans hfm)))
      · rintro rfl j
        obtain ⟨r, hr⟩ := hsurj j.castSucc
        refine ⟨r, ?_, hr⟩
        intro hrm
        rw [hrm, hm₀] at hr
        exact Fin.castSucc_ne_last j hr.symm
    rw [hset, Finset.card_singleton]
  · simp only [hsurj, ↓reduceIte]
    by_cases hall : ∀ j : Fin (d + 1), ∃ r, f r = j.castSucc
    · have hne_last : ∀ r : Fin (d + 2), f r ≠ Fin.last (d + 1) := by
        intro r hr
        apply hsurj
        intro y
        refine Fin.lastCases ⟨r, hr⟩ (fun j => hall j) y
      let g : Fin (d + 2) → Fin (d + 1) := fun r => (f r).castPred (hne_last r)
      have hg_cast : ∀ r, (g r).castSucc = f r := fun r => Fin.castSucc_castPred (f r) (hne_last r)
      have hg_surj : Function.Surjective g := by
        intro j
        obtain ⟨r, hr⟩ := hall j
        exact ⟨r, Fin.castSucc_inj.mp ((hg_cast r).trans hr)⟩
      have hnot_inj : ¬ Function.Injective g := by
        intro hinj
        have hcard := Fintype.card_le_of_injective g hinj
        simp only [Fintype.card_fin] at hcard
        omega
      obtain ⟨m₁, m₂, hgm, hm₁₂⟩ : ∃ m₁ m₂, g m₁ = g m₂ ∧ m₁ ≠ m₂ := by
        simpa [Function.Injective] using hnot_inj
      have hset : Finset.univ.filter (fun m => IsSubPan f m) = {m₁, m₂} := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro hm
          by_contra hnot
          push Not at hnot
          rcases hnot with ⟨h1, h2⟩
          let restrictG : {r : Fin (d + 2) // r ≠ m} → Fin (d + 1) := fun r => g r.1
          have hrsurj : Function.Surjective restrictG := by
            intro j
            obtain ⟨r, hrm, hfr⟩ := hm j
            exact ⟨⟨r, hrm⟩, Fin.castSucc_inj.mp ((hg_cast r).trans hfr)⟩
          have hcard_dom : Fintype.card {r : Fin (d + 2) // r ≠ m} = Fintype.card (Fin (d + 1)) := by
            rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin,
              Fintype.card_fin]
            omega
          have hrbij : Function.Bijective restrictG :=
            (Fintype.bijective_iff_surjective_and_card restrictG).mpr ⟨hrsurj, hcard_dom⟩
          have heq : (⟨m₁, h1.symm⟩ : {r : Fin (d + 2) // r ≠ m}) = ⟨m₂, h2.symm⟩ :=
            hrbij.1 hgm
          exact hm₁₂ (Subtype.ext_iff.mp heq)
        · intro hmem j
          rcases hmem with rfl | rfl
          · obtain ⟨r, hr⟩ := hg_surj j
            by_cases hrm : r = m
            · refine ⟨m₂, hm₁₂.symm, ?_⟩
              rw [← hg_cast m₂, ← hgm, ← hrm, hr]
            · exact ⟨r, hrm, (hg_cast r).symm.trans (congrArg Fin.castSucc hr)⟩
          · obtain ⟨r, hr⟩ := hg_surj j
            by_cases hrm : r = m
            · refine ⟨m₁, hm₁₂, ?_⟩
              rw [← hg_cast m₁, hgm, ← hrm, hr]
            · exact ⟨r, hrm, (hg_cast r).symm.trans (congrArg Fin.castSucc hr)⟩
      rw [hset, Finset.card_pair hm₁₂]
    · have hset : Finset.univ.filter (fun m => IsSubPan f m) = ∅ := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hm
        apply hall
        intro j
        obtain ⟨r, -, hr⟩ := hm j
        exact ⟨r, hr⟩
      rw [hset, Finset.card_empty]

private def rotRight (d : ℕ) : Equiv.Perm (Fin (d + 1)) where
  toFun := Fin.lastCases 0 Fin.succ
  invFun := Fin.cases (Fin.last d) Fin.castSucc
  left_inv x := by
    refine Fin.lastCases ?_ (fun j => ?_) x
    · simp
    · simp
  right_inv x := by
    refine Fin.cases ?_ (fun j => ?_) x
    · simp
    · simp

private def liftPerm {d : ℕ} (e : Equiv.Perm (Fin d)) : Equiv.Perm (Fin (d + 1)) where
  toFun := Fin.cases (Fin.last d) (fun x => (e x).castSucc)
  invFun := Fin.lastCases 0 (fun y => (e.symm y).succ)
  left_inv x := by
    refine Fin.cases ?_ (fun j => ?_) x
    · simp
    · simp
  right_inv x := by
    refine Fin.lastCases ?_ (fun j => ?_) x
    · simp
    · simp

private def isBdryPair {d N : ℕ} (p : KuhnSimplex (d + 1) N × Fin (d + 2)) : Prop :=
  p.2 = 0 ∧ p.1.1 (p.1.2 0) = Fin.last N ∧ p.1.2 0 = Fin.last d

private def kuhnPartner {d N : ℕ}
    (p : KuhnSimplex (d + 1) N × Fin (d + 2)) :
    KuhnSimplex (d + 1) N × Fin (d + 2) :=
  if hm0 : p.2 = 0 then
    if hb : (p.1.1 (p.1.2 0)).val < N then
      ((Function.update p.1.1 (p.1.2 0) ⟨(p.1.1 (p.1.2 0)).val + 1, by omega⟩,
        p.1.2 * rotRight d), Fin.last (d + 1))
    else p
  else if hml : p.2 = Fin.last (d + 1) then
    if hb : 0 < (p.1.1 (p.1.2 (Fin.last d))).val then
      ((Function.update p.1.1 (p.1.2 (Fin.last d)) ⟨(p.1.1 (p.1.2 (Fin.last d))).val - 1, by omega⟩,
        p.1.2 * (rotRight d).symm), 0)
    else p
  else
    have hm_pos : 0 < p.2.val := Nat.pos_of_ne_zero fun h => hm0 (Fin.ext h)
    have hm_lt : p.2.val < d + 1 := by
      have := p.2.isLt
      have hne : p.2.val ≠ d + 1 := fun h => hml (Fin.ext h)
      omega
    let j₁ : Fin (d + 1) := ⟨p.2.val - 1, by omega⟩
    let j₂ : Fin (d + 1) := ⟨p.2.val, hm_lt⟩
    ((p.1.1, p.1.2 * Equiv.swap j₁ j₂), p.2)

private theorem kuhnVertex_left_shift {d N : ℕ} (b : Fin (d + 1) → Fin (N + 1))
    (σ : Equiv.Perm (Fin (d + 1))) (hb : (b (σ 0)).val < N) (r : Fin (d + 1)) :
    let b' := Function.update b (σ 0) ⟨(b (σ 0)).val + 1, by omega⟩
    let σ' := σ * rotRight d
    kuhnVertex (b', σ') r.castSucc = kuhnVertex (b, σ) r.succ := by
  intro b' σ'
  ext i
  dsimp only [kuhnVertex]
  have hsymm : σ'.symm i = (rotRight d).symm (σ.symm i) := rfl
  by_cases hi : i = σ 0
  · subst hi
    have h0 : σ.symm (σ 0) = 0 := σ.symm_apply_apply 0
    have hrot : (rotRight d).symm 0 = Fin.last d := by simp [rotRight]
    have hup : (b' (σ 0)).val = (b (σ 0)).val + 1 := by simp [b']
    have hr : ¬ (d < r.val) := Nat.not_lt.mpr (Nat.le_of_lt_succ r.isLt)
    simp [hsymm, h0, hrot, hup, hr]
  · have hup : b' i = b i := Function.update_of_ne hi _ b
    have hne0 : σ.symm i ≠ 0 := fun h =>
      hi ((σ.apply_symm_apply i).symm.trans (congrArg σ h))
    obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero hne0
    have hrot : (rotRight d).symm j.succ = j.castSucc := by simp [rotRight]
    rw [hsymm, hj, hrot, hup]
    simp only [Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega

private theorem kuhnVertex_mid_swap {d N : ℕ} (b : Fin (d + 1) → Fin (N + 1))
    (σ : Equiv.Perm (Fin (d + 1))) (m : Fin (d + 2))
    (hm0 : m ≠ 0) (hml : m ≠ Fin.last (d + 1))
    (r : Fin (d + 2)) (hrm : r ≠ m) :
    have hm_pos : 0 < m.val := Nat.pos_of_ne_zero fun h => hm0 (Fin.ext h)
    have hm_lt : m.val < d + 1 := by
      have := m.isLt
      have hne : m.val ≠ d + 1 := fun h => hml (Fin.ext h)
      omega
    let j₁ : Fin (d + 1) := ⟨m.val - 1, by omega⟩
    let j₂ : Fin (d + 1) := ⟨m.val, hm_lt⟩
    kuhnVertex (b, σ * Equiv.swap j₁ j₂) r = kuhnVertex (b, σ) r := by
  intro hm_pos hm_lt j₁ j₂
  ext i
  simp only [kuhnVertex]
  have hsymm : (σ * Equiv.swap j₁ j₂).symm i = Equiv.swap j₁ j₂ (σ.symm i) := by
    change (Equiv.swap j₁ j₂).symm (σ.symm i) = _
    rw [Equiv.symm_swap]
  rw [hsymm]
  have hrm_val : r.val ≠ m.val := fun h => hrm (Fin.ext h)
  by_cases hu1 : σ.symm i = j₁
  · rw [hu1, Equiv.swap_apply_left]
    change _ + (if m.val < r.val then 1 else 0) = _ + (if m.val - 1 < r.val then 1 else 0)
    split_ifs <;> omega
  · by_cases hu2 : σ.symm i = j₂
    · rw [hu2, Equiv.swap_apply_right]
      change _ + (if m.val - 1 < r.val then 1 else 0) = _ + (if m.val < r.val then 1 else 0)
      split_ifs <;> omega
    · rw [Equiv.swap_apply_of_ne_of_ne hu1 hu2]

/-- **Kuhn's Cubical Sperner Lemma**: for any cubical Sperner coloring of `{0, ..., N + 1}^k`,
the number of panchromatic Kuhn `k`-simplices is odd. -/
theorem sperner_kuhn_cube :
    ∀ (k N : ℕ) (c : CubeVertex k N → Fin (k + 1)),
      IsCubicalSperner c →
      (Finset.univ.filter (fun s : KuhnSimplex k N =>
        Function.Surjective (fun m => c (kuhnVertex s m)))).card % 2 = 1 := by
  intro k
  induction k with
  | zero =>
    intro N c _
    have hsurj : ∀ s : KuhnSimplex 0 N, Function.Surjective (fun m => c (kuhnVertex s m)) := by
      intro s y
      exact ⟨0, (Fin.eq_zero _).trans (Fin.eq_zero y).symm⟩
    have hcard : Fintype.card (KuhnSimplex 0 N) = 1 := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_perm, Fintype.card_fin]
      simp
    simp [hsurj, Finset.filter_true_of_mem, hcard]
  | succ d ih =>
    intro N c hc
    let pan := Finset.univ.filter (fun s : KuhnSimplex (d + 1) N =>
      Function.Surjective (fun m => c (kuhnVertex s m)))
    let pairs := Finset.univ.filter (fun p : KuhnSimplex (d + 1) N × Fin (d + 2) =>
      IsSubPan (fun r => c (kuhnVertex p.1 r)) p.2)
    have hpairs_mod : pairs.card % 2 = pan.card % 2 := by
      have hprod : pairs.card =
          ∑ s : KuhnSimplex (d + 1) N,
            (Finset.univ.filter (fun m : Fin (d + 2) =>
              IsSubPan (fun r => c (kuhnVertex s r)) m)).card := by
        simp only [pairs, Finset.card_filter, Fintype.sum_prod_type]
      rw [hprod, Finset.sum_nat_mod]
      have hcongr :
          (∑ s : KuhnSimplex (d + 1) N,
            (Finset.univ.filter (fun m : Fin (d + 2) =>
              IsSubPan (fun r => c (kuhnVertex s r)) m)).card % 2) =
          ∑ s : KuhnSimplex (d + 1) N,
            if Function.Surjective (fun m => c (kuhnVertex s m)) then 1 else 0 := by
        refine Finset.sum_congr rfl fun s _ => subPan_card_mod_two _
      rw [hcongr, Finset.sum_boole, Nat.cast_id]
    let bdry := pairs.filter isBdryPair
    let paired := pairs.filter (fun p => ¬ isBdryPair p)
    have hsplit_card : pairs.card = bdry.card + paired.card :=
      (Finset.card_filter_add_card_filter_not isBdryPair).symm
    have hnot_dead_right : ∀ p ∈ pairs, p.2 = Fin.last (d + 1) →
        0 < (p.1.1 (p.1.2 (Fin.last d))).val := by
      intro p hp hml
      have hsub : IsSubPan (fun r => c (kuhnVertex p.1 r)) p.2 := (Finset.mem_filter.mp hp).2
      by_contra hle
      have hz : (p.1.1 (p.1.2 (Fin.last d))).val = 0 := by omega
      let i := p.1.2 (Fin.last d)
      obtain ⟨r, hrm, hcr⟩ := hsub i
      dsimp only at hcr
      have hr_lt : r.val < d + 1 := by
        have := r.isLt
        have hne : r.val ≠ d + 1 := fun h => hrm ((Fin.ext h).trans hml.symm)
        omega
      have hv0 : (kuhnVertex p.1 r i).val = 0 := by
        simp only [kuhnVertex, i, p.1.2.symm_apply_apply, Fin.val_last]
        split_ifs <;> omega
      exact hc.1 (kuhnVertex p.1 r) i hv0 hcr
    have hnot_dead_left : ∀ p ∈ paired, p.2 = 0 →
        (p.1.1 (p.1.2 0)).val < N := by
      intro p hp hm0
      have hp_pairs : p ∈ pairs := (Finset.mem_filter.mp hp).1
      have hnbdry : ¬ isBdryPair p := (Finset.mem_filter.mp hp).2
      have hsub : IsSubPan (fun r => c (kuhnVertex p.1 r)) p.2 := (Finset.mem_filter.mp hp_pairs).2
      by_contra hge
      have hN : (p.1.1 (p.1.2 0)).val = N := by
        have := (p.1.1 (p.1.2 0)).isLt
        omega
      have hb_last : p.1.1 (p.1.2 0) = Fin.last N := Fin.ext hN
      have hσ_ne : p.1.2 0 ≠ Fin.last d := fun hσ => hnbdry ⟨hm0, hb_last, hσ⟩
      have hi_lt : (p.1.2 0).val < d := by
        have := (p.1.2 0).isLt
        have hne : (p.1.2 0).val ≠ d := fun h => hσ_ne (Fin.ext h)
        omega
      obtain ⟨r, hrm, hcr⟩ := hsub (Fin.last d)
      dsimp only at hcr
      have hr_pos : 0 < r.val := Nat.pos_of_ne_zero fun h => hrm ((Fin.ext h).trans hm0.symm)
      have hvN : (kuhnVertex p.1 r (p.1.2 0)).val = N + 1 := by
        simp only [kuhnVertex, p.1.2.symm_apply_apply, Fin.val_zero, hN]
        split_ifs <;> omega
      have hle := hc.2 (kuhnVertex p.1 r) (p.1.2 0) hvN
      rw [hcr, Fin.val_castSucc, Fin.val_last] at hle
      omega
    have hpaired_even : paired.card % 2 = 0 := by
      refine even_card_of_involution paired.card paired kuhnPartner rfl ?_ ?_ ?_
      · intro p hp
        have hp_pairs : p ∈ pairs := (Finset.mem_filter.mp hp).1
        have hsub : IsSubPan (fun r => c (kuhnVertex p.1 r)) p.2 := (Finset.mem_filter.mp hp_pairs).2
        by_cases hm0 : p.2 = 0
        · have hb : (p.1.1 (p.1.2 0)).val < N := hnot_dead_left p hp hm0
          have hpart : kuhnPartner p =
              ((Function.update p.1.1 (p.1.2 0) ⟨(p.1.1 (p.1.2 0)).val + 1, by omega⟩,
                p.1.2 * rotRight d), Fin.last (d + 1)) := by
            simp [kuhnPartner, hm0, hb]
          rw [hpart]
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · intro j
            obtain ⟨r, hrm, hcr⟩ := hsub j
            dsimp only at hcr
            have hr0 : r ≠ 0 := fun h => hrm (h.trans hm0.symm)
            obtain ⟨r', rfl⟩ := Fin.eq_succ_of_ne_zero hr0
            refine ⟨r'.castSucc, Fin.castSucc_ne_last r', ?_⟩
            dsimp only
            rw [kuhnVertex_left_shift p.1.1 p.1.2 hb r']
            exact hcr
          · intro hbdry
            exact Fin.last_pos.ne' hbdry.1
        · by_cases hml : p.2 = Fin.last (d + 1)
          · have hb : 0 < (p.1.1 (p.1.2 (Fin.last d))).val := hnot_dead_right p hp_pairs hml
            let b0 := Function.update p.1.1 (p.1.2 (Fin.last d))
              ⟨(p.1.1 (p.1.2 (Fin.last d))).val - 1, by omega⟩
            let σ0 := p.1.2 * (rotRight d).symm
            have hpart : kuhnPartner p = ((b0, σ0), 0) := by
              simp [kuhnPartner, hml, hb, b0, σ0]
            have hσ0_zero : σ0 0 = p.1.2 (Fin.last d) := by
              change p.1.2 ((rotRight d).symm 0) = _
              simp [rotRight]
            have hb0_lt : (b0 (σ0 0)).val < N := by
              rw [hσ0_zero]
              simp only [b0, Function.update_self]
              have := (p.1.1 (p.1.2 (Fin.last d))).isLt
              omega
            have hb_back : Function.update b0 (σ0 0) ⟨(b0 (σ0 0)).val + 1, by omega⟩ = p.1.1 := by
              ext x
              by_cases hx : x = σ0 0
              · subst hx
                rw [Function.update_self]
                dsimp only
                rw [hσ0_zero]
                simp only [b0, Function.update_self]
                omega
              · rw [Function.update_of_ne hx]
                have hx' : x ≠ p.1.2 (Fin.last d) := fun h => hx (h.trans hσ0_zero.symm)
                simp [b0, hx']
            have hσ_back : σ0 * rotRight d = p.1.2 := by
              change p.1.2 * (rotRight d)⁻¹ * rotRight d = p.1.2
              exact inv_mul_cancel_right p.1.2 (rotRight d)
            rw [hpart]
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
            · intro j
              obtain ⟨r, hrm, hcr⟩ := hsub j
              dsimp only at hcr
              have hrl : r ≠ Fin.last (d + 1) := fun h => hrm (h.trans hml.symm)
              let r' : Fin (d + 1) := r.castPred hrl
              have hr'_eq : r'.castSucc = r := Fin.castSucc_castPred r hrl
              refine ⟨r'.succ, Fin.succ_ne_zero r', ?_⟩
              dsimp only
              have hv := kuhnVertex_left_shift b0 σ0 hb0_lt r'
              dsimp only at hv
              rw [hb_back, hσ_back, hr'_eq] at hv
              rw [← hv]
              exact hcr
            · intro hbdry
              have hlast : (b0 (σ0 0)).val = N := congrArg Fin.val hbdry.2.1
              omega
          · have hm_pos : 0 < p.2.val := Nat.pos_of_ne_zero fun h => hm0 (Fin.ext h)
            have hm_lt : p.2.val < d + 1 := by
              have := p.2.isLt
              have hne : p.2.val ≠ d + 1 := fun h => hml (Fin.ext h)
              omega
            let j₁ : Fin (d + 1) := ⟨p.2.val - 1, by omega⟩
            let j₂ : Fin (d + 1) := ⟨p.2.val, hm_lt⟩
            have hpart : kuhnPartner p = ((p.1.1, p.1.2 * Equiv.swap j₁ j₂), p.2) := by
              simp [kuhnPartner, hm0, hml, j₁, j₂]
            rw [hpart]
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
            · intro j
              obtain ⟨r, hrm, hcr⟩ := hsub j
              dsimp only at hcr
              refine ⟨r, hrm, ?_⟩
              dsimp only
              rw [kuhnVertex_mid_swap p.1.1 p.1.2 p.2 hm0 hml r hrm]
              exact hcr
            · intro hbdry
              exact hm0 hbdry.1
      · intro p hp
        have hp_pairs : p ∈ pairs := (Finset.mem_filter.mp hp).1
        rcases p with ⟨⟨b, σ⟩, m⟩
        by_cases hm0 : m = 0
        · have hb : (b (σ 0)).val < N := hnot_dead_left ((b, σ), m) hp hm0
          subst hm0
          let b' := Function.update b (σ 0) ⟨(b (σ 0)).val + 1, by omega⟩
          let σ' := σ * rotRight d
          have h1 : kuhnPartner ((b, σ), 0) = ((b', σ'), Fin.last (d + 1)) := by
            simp [kuhnPartner, hb, b', σ']
          rw [h1]
          have hne0 : (Fin.last (d + 1) : Fin (d + 2)) ≠ 0 := Fin.last_pos.ne'
          have hσ'_last : σ' (Fin.last d) = σ 0 := by
            change σ (rotRight d (Fin.last d)) = σ 0
            simp [rotRight]
          have hb'_pos : 0 < (b' (σ' (Fin.last d))).val := by
            rw [hσ'_last]
            simp [b']
          simp only [kuhnPartner, hne0, ↓reduceDIte, hb'_pos]
          refine Prod.ext (Prod.ext ?_ ?_) rfl
          · ext x
            dsimp only
            by_cases hx : x = σ' (Fin.last d)
            · subst hx
              rw [Function.update_self]
              dsimp only
              rw [hσ'_last]
              simp [b']
            · rw [Function.update_of_ne hx]
              have hx' : x ≠ σ 0 := fun h => hx (h.trans hσ'_last.symm)
              simp [b', hx']
          · change σ * rotRight d * (rotRight d)⁻¹ = σ
            exact mul_inv_cancel_right σ (rotRight d)
        · by_cases hml : m = Fin.last (d + 1)
          · have hb : 0 < (b (σ (Fin.last d))).val := hnot_dead_right ((b, σ), m) hp_pairs hml
            subst hml
            let b' := Function.update b (σ (Fin.last d)) ⟨(b (σ (Fin.last d))).val - 1, by omega⟩
            let σ' := σ * (rotRight d).symm
            have h1 : kuhnPartner ((b, σ), Fin.last (d + 1)) = ((b', σ'), 0) := by
              simp [kuhnPartner, hb, b', σ']
            rw [h1]
            have hσ'_zero : σ' 0 = σ (Fin.last d) := by
              change σ ((rotRight d).symm 0) = σ (Fin.last d)
              simp [rotRight]
            have hb'_lt : (b' (σ' 0)).val < N := by
              rw [hσ'_zero]
              simp only [b', Function.update_self]
              have := (b (σ (Fin.last d))).isLt
              omega
            simp only [kuhnPartner, ↓reduceDIte, hb'_lt]
            refine Prod.ext (Prod.ext ?_ ?_) rfl
            · ext x
              dsimp only
              by_cases hx : x = σ' 0
              · subst hx
                rw [Function.update_self]
                dsimp only
                rw [hσ'_zero]
                simp only [b', Function.update_self]
                omega
              · rw [Function.update_of_ne hx]
                have hx' : x ≠ σ (Fin.last d) := fun h => hx (h.trans hσ'_zero.symm)
                simp [b', hx']
            · change σ * (rotRight d)⁻¹ * rotRight d = σ
              exact inv_mul_cancel_right σ (rotRight d)
          · have hm_pos : 0 < m.val := Nat.pos_of_ne_zero fun h => hm0 (Fin.ext h)
            have hm_lt : m.val < d + 1 := by
              have := m.isLt
              have hne : m.val ≠ d + 1 := fun h => hml (Fin.ext h)
              omega
            let j₁ : Fin (d + 1) := ⟨m.val - 1, by omega⟩
            let j₂ : Fin (d + 1) := ⟨m.val, hm_lt⟩
            have h1 : kuhnPartner ((b, σ), m) = ((b, σ * Equiv.swap j₁ j₂), m) := by
              simp [kuhnPartner, hm0, hml, j₁, j₂]
            rw [h1]
            simp [kuhnPartner, hm0, hml, j₁, j₂, mul_assoc]
      · intro p hp
        have hp_pairs : p ∈ pairs := (Finset.mem_filter.mp hp).1
        rcases p with ⟨⟨b, σ⟩, m⟩
        by_cases hm0 : m = 0
        · have hb : (b (σ 0)).val < N := hnot_dead_left ((b, σ), m) hp hm0
          subst hm0
          simp only [kuhnPartner, ↓reduceDIte, hb, ne_eq, Prod.mk.injEq]
          intro h
          exact Fin.last_pos.ne' h.2
        · by_cases hml : m = Fin.last (d + 1)
          · have hb : 0 < (b (σ (Fin.last d))).val := hnot_dead_right ((b, σ), m) hp_pairs hml
            subst hml
            simp only [kuhnPartner, hm0, ↓reduceDIte, hb, ne_eq, Prod.mk.injEq]
            intro h
            exact Fin.last_pos.ne h.2
          · have hm_pos : 0 < m.val := Nat.pos_of_ne_zero fun h => hm0 (Fin.ext h)
            have hm_lt : m.val < d + 1 := by
              have := m.isLt
              have hne : m.val ≠ d + 1 := fun h => hml (Fin.ext h)
              omega
            let j₁ : Fin (d + 1) := ⟨m.val - 1, by omega⟩
            let j₂ : Fin (d + 1) := ⟨m.val, hm_lt⟩
            intro h
            have hpart : kuhnPartner ((b, σ), m) = ((b, σ * Equiv.swap j₁ j₂), m) := by
              simp [kuhnPartner, hm0, hml, j₁, j₂]
            have hσ : σ * Equiv.swap j₁ j₂ = σ :=
              congrArg (fun q => q.1.2) (hpart.symm.trans h)
            have hsw : Equiv.swap j₁ j₂ = 1 := mul_left_cancel (hσ.trans (mul_one σ).symm)
            have hj12 : j₁ = j₂ := by
              have := Equiv.Perm.ext_iff.mp hsw j₁
              simpa using this.symm
            have hval : m.val - 1 = m.val := congrArg Fin.val hj12
            omega
    -- Step B: `bdry` bijects with panchromatic `d`-simplices for the face coloring `c'`
    let faceVert (w : CubeVertex d N) : CubeVertex (d + 1) N :=
      Fin.snoc w (Fin.last (N + 1))
    have hface_BN : ∀ w : CubeVertex d N, (c (faceVert w)).val < d + 1 := by
      intro w
      have hv : (faceVert w (Fin.last d)).val = N + 1 := by
        simp [faceVert, Fin.snoc_last]
      have hle := hc.2 (faceVert w) (Fin.last d) hv
      rw [Fin.val_last] at hle
      omega
    let c' (w : CubeVertex d N) : Fin (d + 1) := ⟨(c (faceVert w)).val, hface_BN w⟩
    have hc'_cast : ∀ w, (c' w).castSucc = c (faceVert w) := by
      intro w
      ext
      rfl
    have hc'_sperner : IsCubicalSperner c' := by
      refine ⟨?_, ?_⟩
      · intro w y hy hc'y
        have hv : (faceVert w y.castSucc).val = 0 := by
          simpa [faceVert, Fin.snoc_castSucc] using hy
        apply hc.1 (faceVert w) y.castSucc hv
        rw [← hc'_cast w, hc'y]
      · intro w y hy
        have hv : (faceVert w y.castSucc).val = N + 1 := by
          simpa [faceVert, Fin.snoc_castSucc] using hy
        simpa [c', Fin.val_castSucc] using hc.2 (faceVert w) y.castSucc hv
    let pan_d := Finset.univ.filter (fun s' : KuhnSimplex d N =>
      Function.Surjective (fun r => c' (kuhnVertex s' r)))
    have hbdry_vertex : ∀ (s' : KuhnSimplex d N) (r : Fin (d + 1)),
        kuhnVertex (Fin.snoc s'.1 (Fin.last N), liftPerm s'.2) r.succ =
          faceVert (kuhnVertex s' r) := by
      intro s' r
      funext i
      refine Fin.lastCases ?_ (fun y => ?_) i
      · dsimp only [faceVert]
        rw [Fin.snoc_last]
        apply Fin.ext
        have hsymm : (liftPerm s'.2).symm (Fin.last d) = 0 := by simp [liftPerm]
        simp [kuhnVertex, hsymm]
      · dsimp only [faceVert]
        rw [Fin.snoc_castSucc]
        apply Fin.ext
        have hsymm : (liftPerm s'.2).symm y.castSucc = (s'.2.symm y).succ := by simp [liftPerm]
        simp only [kuhnVertex, Fin.snoc_castSucc, hsymm, Fin.val_succ]
        split_ifs <;> omega
    have hbdry_card : bdry.card = pan_d.card := by
      symm
      refine Finset.card_bij
        (fun s' _ => ((Fin.snoc s'.1 (Fin.last N), liftPerm s'.2), (0 : Fin (d + 2))))
        ?_ ?_ ?_
      · intro s' hs'
        have hsurj : Function.Surjective (fun r => c' (kuhnVertex s' r)) :=
          (Finset.mem_filter.mp hs').2
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · intro j
          obtain ⟨r, hr⟩ := hsurj j
          dsimp only at hr
          refine ⟨r.succ, Fin.succ_ne_zero r, ?_⟩
          dsimp only
          rw [hbdry_vertex s' r, ← hc'_cast, hr]
        · refine ⟨rfl, ?_, ?_⟩
          · dsimp only
            have h0 : liftPerm s'.2 0 = Fin.last d := by simp [liftPerm]
            rw [h0, Fin.snoc_last]
          · simp [liftPerm]
      · intro s₁ _ s₂ _ heq
        have h1 : (Fin.snoc s₁.1 (Fin.last N) : Fin (d + 1) → Fin (N + 1)) =
            Fin.snoc s₂.1 (Fin.last N) :=
          congrArg (fun q => q.1.1) heq
        have h2 : liftPerm s₁.2 = liftPerm s₂.2 :=
          congrArg (fun q => q.1.2) heq
        refine Prod.ext ?_ ?_
        · funext y
          have hy := congrFun h1 y.castSucc
          simpa [Fin.snoc_castSucc] using hy
        · refine Equiv.ext fun y => ?_
          have hy := Equiv.Perm.ext_iff.mp h2 y.succ
          simp only [liftPerm] at hy
          exact Fin.castSucc_inj.mp hy
      · rintro ⟨⟨b, σ⟩, m⟩ hp
        have hp_pairs : ((b, σ), m) ∈ pairs := (Finset.mem_filter.mp hp).1
        have hbd : isBdryPair ((b, σ), m) := (Finset.mem_filter.mp hp).2
        rcases hbd with ⟨hm0, hb_last, hσ0⟩
        dsimp only at hm0 hb_last hσ0
        subst hm0
        rw [hσ0] at hb_last
        let b' : Fin d → Fin (N + 1) := Fin.init b
        let e : Equiv.Perm (Fin d) :=
          { toFun := fun x => (σ x.succ).castPred fun h =>
              Fin.succ_ne_zero x (σ.injective (h.trans hσ0.symm))
            invFun := fun y => (σ.symm y.castSucc).pred fun h =>
              Fin.castSucc_ne_last y
                ((σ.apply_symm_apply y.castSucc).symm.trans ((congrArg σ h).trans hσ0))
            left_inv := fun x => by simp
            right_inv := fun y => by simp }
        have hb_eq : Fin.snoc b' (Fin.last N) = b := by
          rw [← hb_last]
          exact Fin.snoc_init_self b
        have he_eq : liftPerm e = σ := by
          ext i
          refine Fin.cases ?_ (fun x => ?_) i
          · simp [liftPerm, hσ0]
          · simp [liftPerm, e]
        refine ⟨(b', e), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · intro j
          have hsub : IsSubPan (fun r => c (kuhnVertex (b, σ) r)) 0 :=
            (Finset.mem_filter.mp hp_pairs).2
          obtain ⟨r, hr0, hcr⟩ := hsub j
          dsimp only at hcr ⊢
          obtain ⟨r', rfl⟩ := Fin.eq_succ_of_ne_zero hr0
          refine ⟨r', ?_⟩
          have hv := hbdry_vertex (b', e) r'
          rw [hb_eq, he_eq] at hv
          rw [hv, ← hc'_cast] at hcr
          exact Fin.castSucc_inj.mp hcr
        · rw [hb_eq, he_eq]
    have hpan_d_odd : pan_d.card % 2 = 1 := ih N c' hc'_sperner
    change pan.card % 2 = 1
    omega

/-! ### Part 2: Brouwer's fixed-point theorem and Rudin Lemma 7.23 -/

/-- Closed unit cube `[0, 1]^k` in coordinate space `Fin k → ℝ`. -/
def closedUnitCubePi (k : ℕ) : Set (Fin k → ℝ) :=
  Set.pi univ (fun _ : Fin k => Icc (0 : ℝ) 1)

private theorem isCompact_closedUnitCubePi (k : ℕ) : IsCompact (closedUnitCubePi k) :=
  isCompact_univ_pi fun _ => isCompact_Icc

/-- Embedding of cubical grid vertices `{0, …, N + 1}^k` into `[0, 1]^k`. -/
def gridPoint {k N : ℕ} (v : CubeVertex k N) (i : Fin k) : ℝ :=
  ((v i).val : ℝ) / ((N : ℝ) + 1)

private theorem gridPoint_mem_closedUnitCubePi {k N : ℕ} (v : CubeVertex k N) :
    gridPoint v ∈ closedUnitCubePi k := by
  intro i _
  dsimp only [gridPoint]
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  refine ⟨div_nonneg (Nat.cast_nonneg _) hN.le, ?_⟩
  rw [div_le_one hN]
  have hi : (v i).val ≤ N + 1 := Nat.lt_succ_iff.mp (v i).isLt
  exact_mod_cast hi

private theorem gridPoint_kuhnVertex_dist {k N : ℕ} (s : KuhnSimplex k N)
    (m₁ m₂ : Fin (k + 1)) (i : Fin k) :
    |gridPoint (kuhnVertex s m₁) i - gridPoint (kuhnVertex s m₂) i| ≤ 1 / ((N : ℝ) + 1) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hval : |((kuhnVertex s m₁ i).val : ℝ) - ((kuhnVertex s m₂ i).val : ℝ)| ≤ 1 := by
    dsimp only [kuhnVertex]
    split_ifs <;> push_cast <;> ring_nf <;> norm_num
  have hsub :
      gridPoint (kuhnVertex s m₁) i - gridPoint (kuhnVertex s m₂) i =
        (((kuhnVertex s m₁ i).val : ℝ) - ((kuhnVertex s m₂ i).val : ℝ)) / ((N : ℝ) + 1) := by
    dsimp only [gridPoint]
    ring
  rw [hsub, abs_div, abs_of_pos hN]
  exact div_le_div_of_nonneg_right hval hN.le

/-- Strict-interior Brouwer fixed-point theorem on `[0, 1]^k`: a continuous map sending `[0, 1]^k`
into `[δ, 1 - δ]^k` (`0 < δ < 1/2`) has a fixed point via Kuhn's cubical Sperner lemma. -/
theorem brouwer_fixed_point_cube_strict {k : ℕ} {g : (Fin k → ℝ) → (Fin k → ℝ)} {δ : ℝ}
    (hδ0 : 0 < δ) (_hδ1 : δ < 1 / 2)
    (hg_cont : ContinuousOn g (closedUnitCubePi k))
    (hg_maps : ∀ x ∈ closedUnitCubePi k, ∀ i : Fin k, g x i ∈ Icc δ (1 - δ)) :
    ∃ x ∈ closedUnitCubePi k, g x = x := by
  let S : ∀ N : ℕ, CubeVertex k N → Finset (Fin k) := fun N v =>
    Finset.univ.filter (fun j : Fin k => g (gridPoint v) j < gridPoint v j)
  let c : ∀ N : ℕ, CubeVertex k N → Fin (k + 1) := fun N v =>
    if h : (S N v).Nonempty then ((S N v).min' h).castSucc else Fin.last k
  have hc_sperner : ∀ N : ℕ, IsCubicalSperner (c N) := by
    intro N
    refine ⟨?_, ?_⟩
    · intro v i hvi hcv
      have hgp0 : gridPoint v i = 0 := by simp [gridPoint, hvi]
      have hgi : δ ≤ g (gridPoint v) i := (hg_maps (gridPoint v) (gridPoint_mem_closedUnitCubePi v) i).1
      have hnotS : i ∉ S N v := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hgp0, not_lt]
        linarith
      by_cases hne : (S N v).Nonempty
      · have hmin_eq : ((S N v).min' hne).castSucc = i.castSucc := by
          simpa [c, hne] using hcv
        have hmin : (S N v).min' hne = i := Fin.castSucc_inj.mp hmin_eq
        exact hnotS (hmin ▸ Finset.min'_mem (S N v) hne)
      · have hlast : Fin.last k = i.castSucc := by simpa [c, hne] using hcv
        exact (Fin.castSucc_ne_last i hlast.symm).elim
    · intro v i hvi
      have hgp1 : gridPoint v i = 1 := by
        dsimp only [gridPoint]
        rw [hvi]
        push_cast
        exact div_self (by positivity)
      have hgi : g (gridPoint v) i ≤ 1 - δ :=
        (hg_maps (gridPoint v) (gridPoint_mem_closedUnitCubePi v) i).2
      have hiS : i ∈ S N v := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hgp1]
        linarith
      have hne : (S N v).Nonempty := ⟨i, hiS⟩
      dsimp only [c]
      split_ifs
      simp only [Fin.val_castSucc]
      exact Finset.min'_le (S N v) i hiS
  have hex_pan : ∀ N : ℕ, ∃ s : KuhnSimplex k N,
      Function.Surjective (fun r => c N (kuhnVertex s r)) := by
    intro N
    have hodd := sperner_kuhn_cube k N (c N) (hc_sperner N)
    have hpos : 0 < (Finset.univ.filter (fun s : KuhnSimplex k N =>
        Function.Surjective (fun r => c N (kuhnVertex s r)))).card := by omega
    obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
    exact ⟨s, (Finset.mem_filter.mp hs).2⟩
  choose s hs using hex_pan
  let xseq : ℕ → (Fin k → ℝ) := fun N => gridPoint (kuhnVertex (s N) 0)
  have hxseq_mem : ∀ N : ℕ, xseq N ∈ closedUnitCubePi k :=
    fun N => gridPoint_mem_closedUnitCubePi (kuhnVertex (s N) 0)
  obtain ⟨xstar, hxstar_mem, φ, hφ_mono, hx_lim⟩ :=
    (isCompact_closedUnitCubePi k).tendsto_subseq hxseq_mem
  have hmesh_zero : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hφ_mono.tendsto_atTop).atTop_add
      tendsto_const_nhds
  have vertex_tendsto : ∀ r : ℕ → Fin (k + 1),
      Tendsto (fun n => gridPoint (kuhnVertex (s (φ n)) (r n))) atTop (𝓝 xstar) := by
    intro r
    rw [tendsto_pi_nhds]
    intro i
    have hxi : Tendsto (fun n => xseq (φ n) i) atTop (𝓝 (xstar i)) := by
      have h := (tendsto_pi_nhds.mp hx_lim) i
      simpa only [Function.comp_def] using h
    have hdiff : Tendsto (fun n =>
        gridPoint (kuhnVertex (s (φ n)) (r n)) i - xseq (φ n) i) atTop (𝓝 0) := by
      refine squeeze_zero_norm ?_ hmesh_zero
      intro n
      rw [Real.norm_eq_abs]
      exact gridPoint_kuhnVertex_dist (s (φ n)) (r n) 0 i
    simpa using hdiff.add hxi
  refine ⟨xstar, hxstar_mem, ?_⟩
  funext j
  apply le_antisymm
  · choose r_lo hr_lo using fun n : ℕ => hs (φ n) j.castSucc
    let y : ℕ → (Fin k → ℝ) := fun n => gridPoint (kuhnVertex (s (φ n)) (r_lo n))
    have hy_lim : Tendsto y atTop (𝓝 xstar) := vertex_tendsto r_lo
    have hy_mem : ∀ n, y n ∈ closedUnitCubePi k := fun _ => gridPoint_mem_closedUnitCubePi _
    have hgy_lim : Tendsto (fun n => g (y n) j) atTop (𝓝 (g xstar j)) := by
      have hg_all : Tendsto (g ∘ y) atTop (𝓝 (g xstar)) :=
        (hg_cont xstar hxstar_mem).tendsto.comp
          (tendsto_nhdsWithin_iff.mpr ⟨hy_lim, Eventually.of_forall hy_mem⟩)
      exact (tendsto_pi_nhds.mp hg_all) j
    have hyj_lim : Tendsto (fun n => y n j) atTop (𝓝 (xstar j)) :=
      (tendsto_pi_nhds.mp hy_lim) j
    refine le_of_tendsto_of_tendsto hgy_lim hyj_lim (Eventually.of_forall fun n => ?_)
    have hc_eq : c (φ n) (kuhnVertex (s (φ n)) (r_lo n)) = j.castSucc := hr_lo n
    by_cases hne : (S (φ n) (kuhnVertex (s (φ n)) (r_lo n))).Nonempty
    · have hmin_eq :
          ((S (φ n) (kuhnVertex (s (φ n)) (r_lo n))).min' hne).castSucc = j.castSucc := by
        simpa [c, hne] using hc_eq
      have hmin : (S (φ n) (kuhnVertex (s (φ n)) (r_lo n))).min' hne = j :=
        Fin.castSucc_inj.mp hmin_eq
      have hjS : j ∈ S (φ n) (kuhnVertex (s (φ n)) (r_lo n)) :=
        hmin ▸ Finset.min'_mem _ hne
      exact le_of_lt (Finset.mem_filter.mp hjS).2
    · have hlast : Fin.last k = j.castSucc := by simpa [c, hne] using hc_eq
      exact (Fin.castSucc_ne_last j hlast.symm).elim
  · choose r_hi hr_hi using fun n : ℕ => hs (φ n) (Fin.last k)
    let z : ℕ → (Fin k → ℝ) := fun n => gridPoint (kuhnVertex (s (φ n)) (r_hi n))
    have hz_lim : Tendsto z atTop (𝓝 xstar) := vertex_tendsto r_hi
    have hz_mem : ∀ n, z n ∈ closedUnitCubePi k := fun _ => gridPoint_mem_closedUnitCubePi _
    have hgz_lim : Tendsto (fun n => g (z n) j) atTop (𝓝 (g xstar j)) := by
      have hg_all : Tendsto (g ∘ z) atTop (𝓝 (g xstar)) :=
        (hg_cont xstar hxstar_mem).tendsto.comp
          (tendsto_nhdsWithin_iff.mpr ⟨hz_lim, Eventually.of_forall hz_mem⟩)
      exact (tendsto_pi_nhds.mp hg_all) j
    have hzj_lim : Tendsto (fun n => z n j) atTop (𝓝 (xstar j)) :=
      (tendsto_pi_nhds.mp hz_lim) j
    refine le_of_tendsto_of_tendsto hzj_lim hgz_lim (Eventually.of_forall fun n => ?_)
    have hc_eq : c (φ n) (kuhnVertex (s (φ n)) (r_hi n)) = Fin.last k := hr_hi n
    have hnot_ne : ¬ (S (φ n) (kuhnVertex (s (φ n)) (r_hi n))).Nonempty := by
      intro hne
      simp only [c, hne, ↓reduceDIte] at hc_eq
      exact Fin.castSucc_ne_last _ hc_eq
    have hj_not : j ∉ S (φ n) (kuhnVertex (s (φ n)) (r_hi n)) := fun hj => hnot_ne ⟨j, hj⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj_not
    exact hj_not

/-- Brouwer's fixed-point theorem on `[0, 1]^k`. -/
theorem brouwer_fixed_point_cube {k : ℕ} {f : (Fin k → ℝ) → (Fin k → ℝ)}
    (hf_cont : ContinuousOn f (closedUnitCubePi k))
    (hf_maps : MapsTo f (closedUnitCubePi k) (closedUnitCubePi k)) :
    ∃ x ∈ closedUnitCubePi k, f x = x := by
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 3)
  have hδ0 : ∀ n, 0 < δ n := fun n => by dsimp [δ]; positivity
  have hδ1 : ∀ n, δ n < 1 / 2 := by
    intro n
    dsimp [δ]
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  let g : ℕ → (Fin k → ℝ) → (Fin k → ℝ) :=
    fun n x i => (1 - 2 * δ n) * f x i + δ n
  have hex : ∀ n : ℕ, ∃ x ∈ closedUnitCubePi k, g n x = x := by
    intro n
    refine brouwer_fixed_point_cube_strict (hδ0 n) (hδ1 n) ?_ ?_
    · rw [continuousOn_pi]
      intro i
      exact ((continuousOn_const.mul ((continuousOn_pi.mp hf_cont) i)).add continuousOn_const)
    · intro x hx i
      have hfi : f x i ∈ Icc (0 : ℝ) 1 := hf_maps hx i (mem_univ i)
      have h12 : 0 < 1 - 2 * δ n := by linarith [hδ1 n]
      exact ⟨by nlinarith [hfi.1], by nlinarith [hfi.2]⟩
  choose xseq hxseq_mem hxseq_fix using hex
  obtain ⟨xstar, hxstar_mem, φ, hφ_mono, hx_lim⟩ :=
    (isCompact_closedUnitCubePi k).tendsto_subseq hxseq_mem
  have hδ_lim : Tendsto (fun m => δ (φ m)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hφ_mono.tendsto_atTop).atTop_add
      tendsto_const_nhds
  have hf_lim : Tendsto (fun m => f (xseq (φ m))) atTop (𝓝 (f xstar)) :=
    (hf_cont xstar hxstar_mem).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hx_lim, Eventually.of_forall (fun m => hxseq_mem (φ m))⟩)
  refine ⟨xstar, hxstar_mem, ?_⟩
  funext i
  have hgi_lim : Tendsto (fun m => g (φ m) (xseq (φ m)) i) atTop (𝓝 (f xstar i)) := by
    have hfi_lim : Tendsto (fun m => f (xseq (φ m)) i) atTop (𝓝 (f xstar i)) :=
      (tendsto_pi_nhds.mp hf_lim) i
    have hcoef : Tendsto (fun m => 1 - 2 * δ (φ m)) atTop (𝓝 (1 - 2 * (0 : ℝ))) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hδ_lim)
    simpa using (hcoef.mul hfi_lim).add hδ_lim
  have hxi_lim : Tendsto (fun m => g (φ m) (xseq (φ m)) i) atTop (𝓝 (xstar i)) := by
    have h := (tendsto_pi_nhds.mp hx_lim) i
    dsimp only [Function.comp_def] at h
    simpa only [hxseq_fix] using h
  exact tendsto_nhds_unique hgi_lim hxi_lim

/-- **Brouwer's fixed-point theorem** on the closed Euclidean unit ball `closedBall 0 1 ⊆ ℝ^k`:
every continuous map `F : closedBall 0 1 → closedBall 0 1` has at least one fixed point. -/
theorem brouwer_fixed_point_closedBall {k : ℕ}
    {F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    (hF_cont : ContinuousOn F (closedBall 0 1))
    (hF_maps : MapsTo F (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1, F x = x := by
  let R : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) :=
    fun y => (max (1 : ℝ) ‖y‖)⁻¹ • y
  have hR_pos : ∀ y : EuclideanSpace ℝ (Fin k), 0 < max (1 : ℝ) ‖y‖ :=
    fun y => lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖y‖)
  have hR_cont : Continuous R :=
    ((continuous_const.max continuous_norm).inv₀ (fun y => (hR_pos y).ne')).smul continuous_id
  have hR_mem : ∀ y, R y ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 := by
    intro y
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hR_pos y))]
    calc
      (max (1 : ℝ) ‖y‖)⁻¹ * ‖y‖ ≤ (max (1 : ℝ) ‖y‖)⁻¹ * max (1 : ℝ) ‖y‖ :=
        mul_le_mul_of_nonneg_left (le_max_right 1 ‖y‖) (inv_nonneg.mpr (hR_pos y).le)
      _ = 1 := inv_mul_cancel₀ (hR_pos y).ne'
  have hR_id : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1, R y = y := by
    intro y hy
    rw [mem_closedBall_zero_iff] at hy
    simp [R, max_eq_left hy]
  let ι : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k) :=
    fun u => WithLp.toLp 2 (fun i => 2 * u i - 1)
  let π : EuclideanSpace ℝ (Fin k) → (Fin k → ℝ) :=
    fun y i => (y.ofLp i + 1) / 2
  have hι_cont : Continuous ι :=
    (PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)).comp
      (continuous_pi fun i => (continuous_const.mul (continuous_apply i)).sub continuous_const)
  have hπ_cont : Continuous π :=
    continuous_pi fun i =>
      (((continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin k => ℝ))).add
        continuous_const).div_const 2
  have hιπ : ∀ y : EuclideanSpace ℝ (Fin k), ι (π y) = y := by
    intro y
    ext i
    simp [ι, π]
    ring
  have hπ_mem : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1, π y ∈ closedUnitCubePi k := by
    intro y hy i _
    rw [mem_closedBall_zero_iff] at hy
    have hcoord : |y.ofLp i| ≤ 1 := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le y i).trans hy
    rcases abs_le.mp hcoord with ⟨hlo, hhi⟩
    dsimp [π]
    exact ⟨by linarith, by linarith⟩
  let f : (Fin k → ℝ) → (Fin k → ℝ) := fun u => π (F (R (ι u)))
  have hf_cont : ContinuousOn f (closedUnitCubePi k) := by
    have hFR : ContinuousOn (fun u => F (R (ι u))) (closedUnitCubePi k) :=
      hF_cont.comp (hR_cont.comp hι_cont).continuousOn (fun u _ => hR_mem (ι u))
    exact hπ_cont.comp_continuousOn hFR
  have hf_maps : MapsTo f (closedUnitCubePi k) (closedUnitCubePi k) :=
    fun u _ => hπ_mem _ (hF_maps (hR_mem (ι u)))
  obtain ⟨ustar, _, hustar⟩ := brouwer_fixed_point_cube hf_cont hf_maps
  let xstar : EuclideanSpace ℝ (Fin k) := ι ustar
  have hxstar_eq : F (R xstar) = xstar := by
    calc
      F (R xstar) = ι (π (F (R xstar))) := (hιπ _).symm
      _ = ι (f ustar) := rfl
      _ = xstar := by rw [hustar]
  have hxstar_mem : xstar ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 := by
    rw [← hxstar_eq]
    exact hF_maps (hR_mem xstar)
  refine ⟨xstar, hxstar_mem, ?_⟩
  calc
    F xstar = F (R xstar) := by rw [hR_id xstar hxstar_mem]
    _ = xstar := hxstar_eq

/-- Unrestricted-`ε` version of **Lemma 7.23**: holds for all `ε : ℝ` (when `1 - ε ≤ 0`,
`ball 0 (1 - ε) = ∅` automatically). -/
theorem lemma_7_23_unrestricted {k : ℕ}
    {F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)} {ε : ℝ}
    (hF_cont : ContinuousOn F (closedBall 0 1))
    (hF_sphere : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin k)) 1, ‖F x - x‖ < ε) :
    ball (0 : EuclideanSpace ℝ (Fin k)) (1 - ε) ⊆ F '' ball 0 1 := by
  intro a ha
  by_contra ha_not
  rw [mem_ball_zero_iff] at ha
  have hne : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1, a - F x ≠ 0 := by
    intro x hx hsub
    have hFx : F x = a := (sub_eq_zero.mp hsub).symm
    rw [mem_closedBall_zero_iff] at hx
    rcases hx.lt_or_eq with hlt | heq
    · exact ha_not ⟨x, mem_ball_zero_iff.mpr hlt, hFx⟩
    · have hxS : x ∈ sphere (0 : EuclideanSpace ℝ (Fin k)) 1 := mem_sphere_zero_iff_norm.mpr heq
      have hsp := hF_sphere x hxS
      have htri : ‖x‖ - ‖F x - x‖ ≤ ‖F x‖ := by
        have := norm_sub_norm_le x (x - F x)
        simpa [norm_sub_rev] using this
      rw [heq, hFx] at htri
      rw [hFx] at hsp
      linarith
  let G : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) :=
    fun x => (‖a - F x‖)⁻¹ • (a - F x)
  have hG_cont : ContinuousOn G (closedBall 0 1) := by
    have hsub : ContinuousOn (fun x => a - F x) (closedBall 0 1) :=
      continuousOn_const.sub hF_cont
    have hnorm : ContinuousOn (fun x => (‖a - F x‖)⁻¹) (closedBall 0 1) :=
      (continuous_norm.comp_continuousOn hsub).inv₀
        (fun x hx => norm_ne_zero_iff.mpr (hne x hx))
    exact hnorm.smul hsub
  have hG_sphere : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1,
      G x ∈ sphere (0 : EuclideanSpace ℝ (Fin k)) 1 := by
    intro x hx
    have hpos : 0 < ‖a - F x‖ := norm_pos_iff.mpr (hne x hx)
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
  have hG_maps : MapsTo G (closedBall 0 1) (closedBall 0 1) :=
    fun x hx => sphere_subset_closedBall (hG_sphere x hx)
  obtain ⟨x, hx_mem, hx_fix⟩ := brouwer_fixed_point_closedBall hG_cont hG_maps
  have hxS : x ∈ sphere (0 : EuclideanSpace ℝ (Fin k)) 1 := by
    rw [← hx_fix]
    exact hG_sphere x hx_mem
  have hx_norm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hxS
  have hpos : 0 < ‖a - F x‖ := norm_pos_iff.mpr (hne x hx_mem)
  have haFx_eq : a - F x = ‖a - F x‖ • x := by
    calc
      a - F x = ‖a - F x‖ • G x := by
        dsimp [G]
        rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
      _ = ‖a - F x‖ • x := by rw [hx_fix]
  have hinner_pos : 0 < ⟪x, a - F x⟫ := by
    rw [haFx_eq, real_inner_smul_right, real_inner_self_eq_norm_sq, hx_norm, one_pow, mul_one]
    exact hpos
  have hdecomp : a - F x = a + (x - F x) - x := by abel
  have hinner_neg : ⟪x, a - F x⟫ < 0 := by
    have h1 : ⟪x, a - F x⟫ = ⟪x, a⟫ + ⟪x, x - F x⟫ - ⟪x, x⟫ := by
      rw [hdecomp, inner_sub_right, inner_add_right]
    have hxa : ⟪x, a⟫ ≤ ‖a‖ := by
      have := real_inner_le_norm x a
      rwa [hx_norm, one_mul] at this
    have hxxF : ⟪x, x - F x⟫ ≤ ‖F x - x‖ := by
      have := real_inner_le_norm x (x - F x)
      rwa [hx_norm, one_mul, norm_sub_rev] at this
    have hxx : ⟪x, x⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hx_norm, one_pow]
    have hsp := hF_sphere x hxS
    linarith
  linarith

/-- **Lemma 7.23** (Rudin, p. 151): Let `S = {x : ‖x‖ = 1}` be the boundary sphere of the open unit
ball `B = ball 0 1` in `ℝ^k`, with closure `B̄ = closedBall 0 1`. If `F : B̄ → ℝ^k` is continuous,
`0 < ε < 1`, and `‖F x - x‖ < ε` for all `x ∈ S`, then `ball 0 (1 - ε) ⊆ F '' ball 0 1`. -/
theorem lemma_7_23 {k : ℕ}
    {F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)} {ε : ℝ}
    (_hε0 : 0 < ε) (_hε1 : ε < 1)
    (hF_cont : ContinuousOn F (closedBall 0 1))
    (hF_sphere : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin k)) 1, ‖F x - x‖ < ε) :
    ball (0 : EuclideanSpace ℝ (Fin k)) (1 - ε) ⊆ F '' ball 0 1 :=
  lemma_7_23_unrestricted hF_cont hF_sphere

end Node7_23

section Node7_24

/-- Open Euclidean balls in `ℝ^k` are `σ`-compact. -/
theorem isSigmaCompact_ball {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) (r : ℝ) :
    IsSigmaCompact (ball x r) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [Metric.ball_eq_empty.mpr hr]
    exact isSigmaCompact_empty
  · have heq : ball x r = ⋃ n : ℕ, closedBall x (r * ((n : ℝ) / ((n : ℝ) + 1))) := by
      ext y
      simp only [mem_ball, mem_iUnion, mem_closedBall]
      constructor
      · intro hy
        have hpos : 0 < r - dist y x := sub_pos.mpr hy
        obtain ⟨n, hn⟩ := exists_nat_gt (dist y x / (r - dist y x))
        refine ⟨n, ?_⟩
        have hn' : dist y x < (n : ℝ) * (r - dist y x) := (div_lt_iff₀ hpos).mp hn
        have hn1 : dist y x * ((n : ℝ) + 1) ≤ r * (n : ℝ) := by linarith
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        exact hn1
      · rintro ⟨n, hn⟩
        have hfrac : (n : ℝ) / ((n : ℝ) + 1) < 1 := by
          rw [div_lt_one (by positivity)]
          linarith
        exact hn.trans_lt (by nlinarith)
    rw [heq]
    exact isSigmaCompact_iUnion_of_isCompact _ (fun n => ProperSpace.isCompact_closedBall x _)

/-- **Assertion 7.24 (measurability / `σ`-compactness note)** (Rudin, p. 151): when `T` is
continuous on `V` and `ball x r ⊆ V`, `T '' ball x r` is `σ`-compact, hence Borel measurable
(and Lebesgue measurable). -/
theorem isSigmaCompact_image_ball {k : ℕ}
    {V : Set (EuclideanSpace ℝ (Fin k))}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {x : EuclideanSpace ℝ (Fin k)} {r : ℝ}
    (hT_cont : ContinuousOn T V) (hrV : ball x r ⊆ V) :
    IsSigmaCompact (T '' ball x r) :=
  (isSigmaCompact_ball x r).image_of_continuousOn (hT_cont.mono hrV)

theorem measurableSet_image_ball {k : ℕ}
    {V : Set (EuclideanSpace ℝ (Fin k))}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {x : EuclideanSpace ℝ (Fin k)} {r : ℝ}
    (hT_cont : ContinuousOn T V) (hrV : ball x r ⊆ V) :
    MeasurableSet (T '' ball x r) := by
  rcases isSigmaCompact_image_ball hT_cont hrV with ⟨K, hK, hcov⟩
  rw [← hcov]
  exact MeasurableSet.iUnion fun n => (hK n).isClosed.measurableSet

theorem nullMeasurableSet_image_ball {k : ℕ}
    {V : Set (EuclideanSpace ℝ (Fin k))}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {x : EuclideanSpace ℝ (Fin k)} {r : ℝ}
    (hT_cont : ContinuousOn T V) (hrV : ball x r ⊆ V) :
    NullMeasurableSet (T '' ball x r) volume :=
  (measurableSet_image_ball hT_cont hrV).nullMeasurableSet

private theorem volume_image_add_left {k : ℕ}
    (w : EuclideanSpace ℝ (Fin k)) (S : Set (EuclideanSpace ℝ (Fin k))) :
    volume ((fun z => w + z) '' S) = volume S := by
  have heq : (fun z => w + z) '' S = (fun z => -w + z) ⁻¹' S := by
    ext y
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hy
      exact ⟨-w + y, hy, by abel⟩
  rw [heq, measure_preimage_add volume (-w) S]

private theorem volume_image_smul_nonneg {k : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (S : Set (EuclideanSpace ℝ (Fin k))) :
    volume ((fun z => r • z) '' S) = ENNReal.ofReal (r ^ k) * volume S := by
  let L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) := r • LinearMap.id
  have hfun : (fun z : EuclideanSpace ℝ (Fin k) => r • z) = L := rfl
  have hdet : linearModulus L = r ^ k := by
    dsimp [linearModulus, L]
    rw [LinearMap.det_smul, finrank_euclideanSpace_fin, LinearMap.det_id, mul_one,
      abs_of_nonneg (pow_nonneg hr k)]
  rw [hfun, volume_image_linearMap_eq_linearModulus, hdet]

private theorem volume_ball_eq_pow_mul {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) {r : ℝ}
    (hr : 0 < r) :
    volume (ball x r) =
      ENNReal.ofReal (r ^ k) * volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) := by
  have heq : ball x r = (fun z => x + z) '' ((fun z => r • z) '' ball 0 1) := by
    ext y
    simp only [mem_ball, mem_image, dist_zero_right]
    constructor
    · intro hy
      refine ⟨r • (r⁻¹ • (y - x)), ⟨r⁻¹ • (y - x), ?_, rfl⟩, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
        rw [inv_mul_lt_iff₀ hr, mul_one]
        simpa [dist_eq_norm] using hy
      · rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rw [dist_self_add_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      nlinarith
  rw [heq, volume_image_add_left, volume_image_smul_nonneg hr.le]

private theorem volumeReal_ball_eq_pow_mul {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) {r : ℝ}
    (hr : 0 < r) :
    volume.real (ball x r) =
      r ^ k * volume.real (ball (0 : EuclideanSpace ℝ (Fin k)) 1) := by
  rw [measureReal_def, volume_ball_eq_pow_mul x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le k), ← measureReal_def]

/-- **Theorem 7.24 (explicit linear derivative form)** (Rudin, pp. 151–153): If `V ⊆ ℝ^k` is open,
`T : V → ℝ^k` is continuous, and `T` is differentiable at `x ∈ V` with `T'(x) = A` (no assumption
of differentiability anywhere else on `V`), then
`lim_{r → 0⁺} m(T(B(x, r))) / m(B(x, r)) = Δ(A) = |det A|`. -/
theorem theorem_7_24_bookHasFDerivAt {k : ℕ}
    {V : Set (EuclideanSpace ℝ (Fin k))}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)}
    {x : EuclideanSpace ℝ (Fin k)}
    (hV : IsOpen V) (hx : x ∈ V)
    (hT_cont : ContinuousOn T V)
    (hT_diff : BookHasFDerivAt T A x) :
    Tendsto (fun r => volume.real (T '' ball x r) / volume.real (ball x r))
      (𝓝[>] (0 : ℝ)) (𝓝 (linearModulus A)) := by
  have hT_fderiv : HasFDerivAt T A.toContinuousLinearMap x :=
    bookHasFDerivAt_iff_hasFDerivAt.mp hT_diff
  have hv0_pos : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin k)) 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 zero_lt_one).ne' measure_ball_lt_top.ne
  obtain ⟨δV, hδV_pos, hδV_sub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hx)
  by_cases hdet : LinearMap.det A ≠ 0
  · -- Case I: `A` is invertible (`det A ≠ 0`).
    let e : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
      LinearMap.equivOfDetNeZero A hdet
    let eL : EuclideanSpace ℝ (Fin k) ≃L[ℝ] EuclideanSpace ℝ (Fin k) :=
      e.toContinuousLinearEquiv
    let F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) := fun y => eL.symm (T y)
    have hAF : ∀ y, A (F y) = T y := fun y => e.apply_symm_apply (T y)
    have hFA : ∀ v, eL.symm (A v) = v := fun v => e.symm_apply_apply v
    have hF_cont : ContinuousOn F V := eL.symm.continuous.comp_continuousOn hT_cont
    have hF_fderiv : HasFDerivAt F (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k))) x := by
      have hcomp := (eL.symm : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)).hasFDerivAt.comp
        x hT_fderiv
      have hid :
          (eL.symm : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)).comp
              A.toContinuousLinearMap =
            ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k)) :=
        ContinuousLinearMap.ext fun v => hFA v
      rwa [hid] at hcomp
    have hF_ratio :
        Tendsto (fun r => volume.real (F '' ball x r) / volume.real (ball x r))
          (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      rw [Metric.tendsto_nhds]
      intro η hη
      have hpow_cont : ContinuousAt (fun t : ℝ => t ^ k) 1 := (continuous_pow k).continuousAt
      rw [Metric.continuousAt_iff] at hpow_cont
      obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hpow_cont η hη
      let ε : ℝ := min (δ₁ / 2) (1 / 2)
      have hε_pos : 0 < ε := lt_min (half_pos hδ₁_pos) (by norm_num)
      have hε_lt_one : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hε_lt_δ₁ : ε < δ₁ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ₁_pos)
      have hpow_lo : 1 - η < (1 - ε) ^ k := by
        have hd : dist (1 - ε) 1 < δ₁ := by
          rw [Real.dist_eq, show (1 - ε) - 1 = -ε by ring, abs_neg, abs_of_pos hε_pos]
          exact hε_lt_δ₁
        have h := @hδ₁ (1 - ε) hd
        rw [one_pow, Real.dist_eq, abs_lt] at h
        linarith
      have hpow_hi : (1 + ε) ^ k < 1 + η := by
        have hd : dist (1 + ε) 1 < δ₁ := by
          rw [Real.dist_eq, show (1 + ε) - 1 = ε by ring, abs_of_pos hε_pos]
          exact hε_lt_δ₁
        have h := @hδ₁ (1 + ε) hd
        rw [one_pow, Real.dist_eq, abs_lt] at h
        linarith
      have hlo_fderiv :=
        (hasFDerivAt_iff_isLittleO_nhds_zero.mp hF_fderiv).def (half_pos hε_pos)
      obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.eventually_nhds_iff.mp hlo_fderiv
      let δ : ℝ := min δ₂ δV
      have hδ_pos : 0 < δ := lt_min hδ₂_pos hδV_pos
      filter_upwards [Ioo_mem_nhdsGT hδ_pos] with r ⟨hr_pos, hr_lt⟩
      have hr_lt_δ₂ : r < δ₂ := hr_lt.trans_le (min_le_left _ _)
      have hr_le_δV : r ≤ δV := (hr_lt.trans_le (min_le_right _ _)).le
      have hcb_sub_V : closedBall x r ⊆ V :=
        (closedBall_subset_closedBall hr_le_δV).trans hδV_sub
      have hfderiv_bound : ∀ h : EuclideanSpace ℝ (Fin k), ‖h‖ ≤ r →
          ‖F (x + h) - F x - h‖ ≤ (ε / 2) * ‖h‖ := by
        intro h hh
        have hh_lt : dist h 0 < δ₂ := by
          rw [dist_zero_right]
          exact hh.trans_lt hr_lt_δ₂
        simpa using hδ₂ hh_lt
      have hsub_hi : F '' ball x r ⊆ ball (F x) ((1 + ε) * r) := by
        rintro _ ⟨y, hy, rfl⟩
        let h := y - x
        have hy_eq : y = x + h := (add_sub_cancel x y).symm
        have hh_lt : ‖h‖ < r := by simpa [h, dist_eq_norm] using mem_ball.mp hy
        have hbd := hfderiv_bound h hh_lt.le
        rw [mem_ball, dist_eq_norm, hy_eq]
        have htri : ‖F (x + h) - F x‖ ≤ ‖F (x + h) - F x - h‖ + ‖h‖ := by
          simpa using norm_add_le (F (x + h) - F x - h) h
        nlinarith [norm_nonneg h]
      have hsub_lo : ball (F x) ((1 - ε) * r) ⊆ F '' ball x r := by
        let Φ : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) :=
          fun u => r⁻¹ • (F (x + r • u) - F x)
        have hΦ_cont : ContinuousOn Φ (closedBall 0 1) := by
          have haff : Continuous (fun u : EuclideanSpace ℝ (Fin k) => x + r • u) :=
            continuous_const.add (continuous_id.const_smul r)
          have hmaps : MapsTo (fun u => x + r • u) (closedBall 0 1) V := by
            intro u hu
            apply hcb_sub_V
            rw [mem_closedBall, dist_self_add_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr_pos]
            rw [mem_closedBall_zero_iff] at hu
            nlinarith
          exact ((hF_cont.comp haff.continuousOn hmaps).sub continuousOn_const).const_smul r⁻¹
        have hΦ_sphere : ∀ u ∈ sphere (0 : EuclideanSpace ℝ (Fin k)) 1, ‖Φ u - u‖ < ε := by
          intro u hu
          have hu_norm : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
          have hru_norm : ‖r • u‖ = r := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr_pos, hu_norm, mul_one]
          have hbd := hfderiv_bound (r • u) hru_norm.le
          have hrew : Φ u - u = r⁻¹ • (F (x + r • u) - F x - r • u) := by
            dsimp [Φ]
            rw [smul_sub (r⁻¹) (F (x + r • u) - F x) (r • u),
              smul_smul, inv_mul_cancel₀ hr_pos.ne', one_smul]
          rw [hrew, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr_pos)]
          rw [hru_norm] at hbd
          have hle : r⁻¹ * ‖F (x + r • u) - F x - r • u‖ ≤ ε / 2 := by
            calc
              r⁻¹ * ‖F (x + r • u) - F x - r • u‖ ≤ r⁻¹ * ((ε / 2) * r) :=
                mul_le_mul_of_nonneg_left hbd (inv_nonneg.mpr hr_pos.le)
              _ = ε / 2 := by field_simp [hr_pos.ne']
          linarith
        have h723 := lemma_7_23 hε_pos hε_lt_one hΦ_cont hΦ_sphere
        intro z hz
        rw [mem_ball, dist_eq_norm] at hz
        let w : EuclideanSpace ℝ (Fin k) := r⁻¹ • (z - F x)
        have hw : w ∈ ball (0 : EuclideanSpace ℝ (Fin k)) (1 - ε) := by
          rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr_pos)]
          exact (inv_mul_lt_iff₀ hr_pos).mpr (by linarith)
        obtain ⟨u, hu_ball, hΦu⟩ := h723 hw
        refine ⟨x + r • u, ?_, ?_⟩
        · rw [mem_ball, dist_self_add_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr_pos]
          rw [mem_ball_zero_iff] at hu_ball
          nlinarith
        · have h1 : r • Φ u = F (x + r • u) - F x := by
            dsimp [Φ]
            rw [smul_smul, mul_inv_cancel₀ hr_pos.ne', one_smul]
          have h2 : r • w = z - F x := by
            dsimp [w]
            rw [smul_smul, mul_inv_cancel₀ hr_pos.ne', one_smul]
          have h3 : F (x + r • u) - F x = z - F x := by rw [← h1, hΦu, h2]
          exact sub_left_inj.mp h3
      have h1mε_pos : 0 < (1 - ε) * r := mul_pos (sub_pos.mpr hε_lt_one) hr_pos
      have h1pε_pos : 0 < (1 + ε) * r := mul_pos (by linarith) hr_pos
      have hhi_fin : volume (ball (F x) ((1 + ε) * r)) ≠ ⊤ := measure_ball_lt_top.ne
      have hF_fin : volume (F '' ball x r) ≠ ⊤ :=
        ((measure_mono hsub_hi).trans_lt measure_ball_lt_top).ne
      have hvol_hi : volume.real (F '' ball x r) ≤ volume.real (ball (F x) ((1 + ε) * r)) :=
        measureReal_mono hsub_hi hhi_fin
      have hvol_lo : volume.real (ball (F x) ((1 - ε) * r)) ≤ volume.real (F '' ball x r) :=
        measureReal_mono hsub_lo hF_fin
      have hball_r_pos : 0 < volume.real (ball x r) := by
        rw [volumeReal_ball_eq_pow_mul x hr_pos]
        exact mul_pos (pow_pos hr_pos k) hv0_pos
      have hratio_lo :
          (1 - ε) ^ k ≤ volume.real (F '' ball x r) / volume.real (ball x r) := by
        rw [le_div_iff₀ hball_r_pos]
        calc
          (1 - ε) ^ k * volume.real (ball x r)
            = ((1 - ε) * r) ^ k * volume.real (ball (0 : EuclideanSpace ℝ (Fin k)) 1) := by
                rw [volumeReal_ball_eq_pow_mul x hr_pos, mul_pow]
                ring
          _ = volume.real (ball (F x) ((1 - ε) * r)) :=
                (volumeReal_ball_eq_pow_mul (F x) h1mε_pos).symm
          _ ≤ volume.real (F '' ball x r) := hvol_lo
      have hratio_hi :
          volume.real (F '' ball x r) / volume.real (ball x r) ≤ (1 + ε) ^ k := by
        rw [div_le_iff₀ hball_r_pos]
        calc
          volume.real (F '' ball x r)
            ≤ volume.real (ball (F x) ((1 + ε) * r)) := hvol_hi
          _ = ((1 + ε) * r) ^ k * volume.real (ball (0 : EuclideanSpace ℝ (Fin k)) 1) :=
                volumeReal_ball_eq_pow_mul (F x) h1pε_pos
          _ = (1 + ε) ^ k * volume.real (ball x r) := by
                rw [volumeReal_ball_eq_pow_mul x hr_pos, mul_pow]
                ring
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith, by linarith⟩
    have hscale : ∀ r : ℝ,
        volume.real (T '' ball x r) / volume.real (ball x r) =
          linearModulus A * (volume.real (F '' ball x r) / volume.real (ball x r)) := by
      intro r
      have himg : T '' ball x r = A '' (F '' ball x r) := by
        ext z
        simp only [mem_image]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨F y, ⟨y, hy, rfl⟩, hAF y⟩
        · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
          exact ⟨y, hy, (hAF y).symm⟩
      have hmod_nonneg : 0 ≤ linearModulus A := abs_nonneg _
      have hvol : volume.real (T '' ball x r) = linearModulus A * volume.real (F '' ball x r) := by
        rw [himg, measureReal_def, volume_image_linearMap_eq_linearModulus,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal hmod_nonneg, ← measureReal_def]
      rw [hvol, mul_div_assoc]
    simpa [hscale, mul_one] using tendsto_const_nhds.mul hF_ratio
  · -- Case II: `A` is singular (`det A = 0`).
    have hdet0 : LinearMap.det A = 0 := not_not.mp hdet
    have hmod0 : linearModulus A = 0 := by simp [linearModulus, hdet0]
    rw [hmod0, Metric.tendsto_nhds]
    intro η hη
    let K : Set (EuclideanSpace ℝ (Fin k)) := A '' closedBall 0 1
    have hK_compact : IsCompact K :=
      (ProperSpace.isCompact_closedBall 0 1).image A.toContinuousLinearMap.continuous
    have hK_vol : volume K = 0 := by
      rw [volume_image_linearMap_eq_linearModulus, hmod0, ENNReal.ofReal_zero, zero_mul]
    let v₀ : ℝ := volume.real (ball (0 : EuclideanSpace ℝ (Fin k)) 1)
    have htarget_pos : 0 < ENNReal.ofReal ((η / 2) * v₀) :=
      ENNReal.ofReal_pos.mpr (mul_pos (half_pos hη) hv0_pos)
    have hK_lt : volume K < ENNReal.ofReal ((η / 2) * v₀) := hK_vol ▸ htarget_pos
    obtain ⟨U, hKU, hU_open, hU_vol⟩ :=
      Set.exists_isOpen_lt_of_lt (μ := volume) K (ENNReal.ofReal ((η / 2) * v₀)) hK_lt
    obtain ⟨ε, hε_pos, hthick_sub⟩ := hK_compact.exists_thickening_subset_open hU_open hKU
    have hlo_fderiv :=
      (hasFDerivAt_iff_isLittleO_nhds_zero.mp hT_fderiv).def (half_pos hε_pos)
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp hlo_fderiv
    filter_upwards [Ioo_mem_nhdsGT hδ_pos] with r ⟨hr_pos, hr_lt⟩
    have hsub : T '' ball x r ⊆ (fun z => T x + z) '' ((fun z => r • z) '' U) := by
      rintro _ ⟨y, hy, rfl⟩
      let h := y - x
      have hy_eq : y = x + h := (add_sub_cancel x y).symm
      have hh_lt : ‖h‖ < r := by simpa [h, dist_eq_norm] using mem_ball.mp hy
      have hh_δ : dist h 0 < δ := by
        rw [dist_zero_right]
        exact hh_lt.trans hr_lt
      have hbd : ‖T (x + h) - T x - A h‖ ≤ (ε / 2) * ‖h‖ := by
        simpa using hδ hh_δ
      let u : EuclideanSpace ℝ (Fin k) := r⁻¹ • h
      have hu_mem : u ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 := by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr_pos)]
        calc
          r⁻¹ * ‖h‖ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hh_lt.le (inv_nonneg.mpr hr_pos.le)
          _ = 1 := inv_mul_cancel₀ hr_pos.ne'
      let z : EuclideanSpace ℝ (Fin k) := r⁻¹ • (T (x + h) - T x)
      have hz_thick : z ∈ Metric.thickening ε K := by
        rw [Metric.mem_thickening_iff]
        refine ⟨A u, ⟨u, hu_mem, rfl⟩, ?_⟩
        have hzu : z - A u = r⁻¹ • (T (x + h) - T x - A h) := by
          dsimp [z, u]
          rw [map_smul, ← smul_sub]
        rw [dist_eq_norm, hzu, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr_pos)]
        have hle : r⁻¹ * ‖T (x + h) - T x - A h‖ ≤ ε / 2 := by
          calc
            r⁻¹ * ‖T (x + h) - T x - A h‖
              ≤ r⁻¹ * ((ε / 2) * ‖h‖) :=
                  mul_le_mul_of_nonneg_left hbd (inv_nonneg.mpr hr_pos.le)
            _ ≤ r⁻¹ * ((ε / 2) * r) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left hh_lt.le (half_pos hε_pos).le)
                    (inv_nonneg.mpr hr_pos.le)
            _ = ε / 2 := by field_simp [hr_pos.ne']
        linarith
      have hzU : z ∈ U := hthick_sub hz_thick
      refine ⟨r • z, ⟨z, hzU, rfl⟩, ?_⟩
      dsimp [z]
      rw [smul_smul, mul_inv_cancel₀ hr_pos.ne', one_smul, add_sub_cancel, ← hy_eq]
    have hvol_le : volume (T '' ball x r) ≤ ENNReal.ofReal (r ^ k) * volume U := by
      calc
        volume (T '' ball x r)
          ≤ volume ((fun z => T x + z) '' ((fun z => r • z) '' U)) := measure_mono hsub
        _ = ENNReal.ofReal (r ^ k) * volume U := by
              rw [volume_image_add_left, volume_image_smul_nonneg hr_pos.le]
    have hU_fin : volume U ≠ ⊤ := (hU_vol.trans_le le_top).ne
    have hrhs_fin : ENNReal.ofReal (r ^ k) * volume U ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hU_fin
    have hreal_le : volume.real (T '' ball x r) ≤ r ^ k * ((η / 2) * v₀) := by
      have h1 : volume.real (T '' ball x r) ≤ (ENNReal.ofReal (r ^ k) * volume U).toReal := by
        rw [measureReal_def]
        exact ENNReal.toReal_mono hrhs_fin hvol_le
      have hU_real : volume.real U ≤ (η / 2) * v₀ := by
        rw [measureReal_def]
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hU_vol.le
        rwa [ENNReal.toReal_ofReal (mul_nonneg (half_pos hη).le hv0_pos.le)] at this
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr_pos.le k), ← measureReal_def] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hU_real (pow_nonneg hr_pos.le k))
    have hball_r_pos : 0 < volume.real (ball x r) := by
      rw [volumeReal_ball_eq_pow_mul x hr_pos]
      exact mul_pos (pow_pos hr_pos k) hv0_pos
    have hratio_le : volume.real (T '' ball x r) / volume.real (ball x r) ≤ η / 2 := by
      rw [div_le_iff₀ hball_r_pos]
      calc
        volume.real (T '' ball x r)
          ≤ r ^ k * ((η / 2) * v₀) := hreal_le
        _ = (η / 2) * volume.real (ball x r) := by
              rw [volumeReal_ball_eq_pow_mul x hr_pos]
              ring
    have hratio_nonneg : 0 ≤ volume.real (T '' ball x r) / volume.real (ball x r) :=
      div_nonneg measureReal_nonneg hball_r_pos.le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hratio_nonneg]
    linarith

/-- **Theorem 7.24** (Rudin, pp. 151–153): If `V` is open in `ℝ^k`, `T : V → ℝ^k` is continuous,
and `T` is differentiable at some point `x ∈ V`, then
`lim_{r → 0⁺} m(T(B(x, r))) / m(B(x, r)) = Δ(T'(x)) = |J_T(x)|`. -/
theorem theorem_7_24 {k : ℕ}
    {V : Set (EuclideanSpace ℝ (Fin k))}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {x : EuclideanSpace ℝ (Fin k)}
    (hV : IsOpen V) (hx : x ∈ V)
    (hT_cont : ContinuousOn T V)
    (hT_diff : DifferentiableAt ℝ T x) :
    Tendsto (fun r => volume.real (T '' ball x r) / volume.real (ball x r))
      (𝓝[>] (0 : ℝ)) (𝓝 |jacobian T x|) := by
  have hclm : (fderiv ℝ T x).toLinearMap.toContinuousLinearMap = fderiv ℝ T x :=
    ContinuousLinearMap.ext fun _ => rfl
  have hbook : BookHasFDerivAt T (fderiv ℝ T x).toLinearMap x :=
    bookHasFDerivAt_iff_hasFDerivAt.mpr (hclm.symm ▸ hT_diff.hasFDerivAt)
  simpa [jacobian, linearModulus] using theorem_7_24_bookHasFDerivAt hV hx hT_cont hbook

/-- `ℝ≥0∞`-valued companion to **Theorem 7.24**:
`lim_{r → 0⁺} volume (T '' ball x r) / volume (ball x r) = ENNReal.ofReal |J_T(x)|`. -/
theorem theorem_7_24_ennreal {k : ℕ}
    {V : Set (EuclideanSpace ℝ (Fin k))}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {x : EuclideanSpace ℝ (Fin k)}
    (hV : IsOpen V) (hx : x ∈ V)
    (hT_cont : ContinuousOn T V)
    (hT_diff : DifferentiableAt ℝ T x) :
    Tendsto (fun r => volume (T '' ball x r) / volume (ball x r))
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal |jacobian T x|)) := by
  have hreal := theorem_7_24 hV hx hT_cont hT_diff
  have hofReal :
      Tendsto (fun r => ENNReal.ofReal (volume.real (T '' ball x r) / volume.real (ball x r)))
        (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal |jacobian T x|)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  obtain ⟨δV, hδV_pos, hδV_sub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hx)
  have hK_fin : volume (T '' closedBall x δV) < ⊤ :=
    ((ProperSpace.isCompact_closedBall x δV).image_of_continuousOn
      (hT_cont.mono hδV_sub)).isBounded.measure_lt_top
  refine hofReal.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδV_pos] with r ⟨hr_pos, hr_lt⟩
  have hball_pos : volume (ball x r) ≠ 0 := (Metric.measure_ball_pos volume x hr_pos).ne'
  have hball_fin : volume (ball x r) ≠ ⊤ := measure_ball_lt_top.ne
  have himg_fin : volume (T '' ball x r) ≠ ⊤ := by
    have hsub : T '' ball x r ⊆ T '' closedBall x δV :=
      image_mono ((ball_subset_closedBall).trans (closedBall_subset_closedBall hr_lt.le))
    exact ((measure_mono hsub).trans_lt hK_fin).ne
  rw [measureReal_def, measureReal_def,
    ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hball_pos hball_fin),
    ENNReal.ofReal_toReal himg_fin, ENNReal.ofReal_toReal hball_fin]

end Node7_24

section Node7_25

open scoped Pointwise

/-- **Lemma 7.25 hypothesis** (Rudin, p. 153): finite pointwise upper limit of difference-quotient
norms `limsup_{y → x, y ∈ E \ {x}} ‖T(y) - T(x)‖ / ‖y - x‖ < ∞` along `E`. -/
def HasFiniteSlopeLimsupOn {k : ℕ}
    (T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
    (E : Set (EuclideanSpace ℝ (Fin k)))
    (x : EuclideanSpace ℝ (Fin k)) : Prop :=
  Filter.limsup (fun y => (‖T y - T x‖ₑ / ‖y - x‖ₑ : ℝ≥0∞)) (𝓝[E \ {x}] x) < ∞

/-- Equivalence between `HasFiniteSlopeLimsupOn` and an eventual real difference-quotient bound on
`E \ {x}` near `x`. -/
theorem hasFiniteSlopeLimsupOn_iff_exists_bound {k : ℕ}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {x : EuclideanSpace ℝ (Fin k)} :
    HasFiniteSlopeLimsupOn T E x ↔
      ∃ M : ℝ, ∀ᶠ y in 𝓝[E \ {x}] x, ‖T y - T x‖ / ‖y - x‖ ≤ M := by
  constructor
  · intro h
    let M₀ : ℝ := (Filter.limsup (fun y => (‖T y - T x‖ₑ / ‖y - x‖ₑ : ℝ≥0∞)) (𝓝[E \ {x}] x)).toReal
    have hlt :
        Filter.limsup (fun y => (‖T y - T x‖ₑ / ‖y - x‖ₑ : ℝ≥0∞)) (𝓝[E \ {x}] x) <
          ENNReal.ofReal (M₀ + 1) := by
      have heq :
          ENNReal.ofReal M₀ =
            Filter.limsup (fun y => (‖T y - T x‖ₑ / ‖y - x‖ₑ : ℝ≥0∞)) (𝓝[E \ {x}] x) :=
        ENNReal.ofReal_toReal h.ne
      rw [← heq]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [ENNReal.toReal_nonneg (a :=
        Filter.limsup (fun y => (‖T y - T x‖ₑ / ‖y - x‖ₑ : ℝ≥0∞)) (𝓝[E \ {x}] x))])).mpr
        (by linarith)
    refine ⟨M₀ + 1, ?_⟩
    filter_upwards [Filter.eventually_lt_of_limsup_lt hlt, self_mem_nhdsWithin] with y hy hy_mem
    have hy_ne : y ≠ x := hy_mem.2
    have hnorm_pos : 0 < ‖y - x‖ := norm_sub_pos_iff.mpr hy_ne
    have hquot :
        (‖T y - T x‖ₑ / ‖y - x‖ₑ : ℝ≥0∞) = ENNReal.ofReal (‖T y - T x‖ / ‖y - x‖) := by
      rw [ENNReal.ofReal_div_of_pos hnorm_pos, ofReal_norm, ofReal_norm]
    rw [hquot] at hy
    have hM_pos : 0 < M₀ + 1 := by
      linarith [ENNReal.toReal_nonneg (a :=
        Filter.limsup (fun y => (‖T y - T x‖ₑ / ‖y - x‖ₑ : ℝ≥0∞)) (𝓝[E \ {x}] x))]
    exact ((ENNReal.ofReal_lt_ofReal_iff hM_pos).mp hy).le
  · rintro ⟨M, hM⟩
    let M' : ℝ := max M 0
    have hle :
        ∀ᶠ y in 𝓝[E \ {x}] x,
          (‖T y - T x‖ₑ / ‖y - x‖ₑ : ℝ≥0∞) ≤ ENNReal.ofReal M' := by
      filter_upwards [hM, self_mem_nhdsWithin] with y hy hy_mem
      have hnorm_pos : 0 < ‖y - x‖ := norm_sub_pos_iff.mpr hy_mem.2
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_div_of_pos hnorm_pos]
      exact ENNReal.ofReal_le_ofReal (hy.trans (le_max_left M 0))
    exact (Filter.limsup_le_of_le (by isBoundedDefault) hle).trans_lt ENNReal.ofReal_lt_top

private theorem volume_image_eq_zero_of_lipschitz_piece {k : ℕ}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {t : Set (EuclideanSpace ℝ (Fin k))} (ht_null : volume t = 0)
    {L : ℝ} (hL : 0 < L)
    (hlip : ∀ x ∈ t, ∀ y ∈ t, ‖T x - T y‖ ≤ L * ‖x - y‖) :
    volume (T '' t) = 0 := by
  let Z : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) := 0
  let m₀ : ℝ≥0 := Real.toNNReal |Z.det| + 1
  have hm₀ : ENNReal.ofReal |Z.det| < (m₀ : ℝ≥0∞) := by
    simp only [m₀, ENNReal.ofReal, ENNReal.coe_lt_coe, lt_add_iff_pos_right, zero_lt_one]
  have hev := MeasureTheory.addHaar_image_le_mul_of_det_lt volume Z hm₀
  obtain ⟨r, hr_pos, hr⟩ :=
    Metric.mem_nhdsWithin_iff.mp (Filter.inter_mem hev self_mem_nhdsWithin)
  let δ : ℝ≥0 := ⟨r / 2, by positivity⟩
  have hδ_pos_nn : (0 : ℝ≥0) < δ := Subtype.mk_lt_mk.mpr (half_pos hr_pos)
  have hδ_pos : (0 : ℝ) < (δ : ℝ) := hδ_pos_nn
  have hδ_ball : δ ∈ ball (0 : ℝ≥0) r := by
    rw [mem_ball, NNReal.dist_eq]
    change |r / 2 - 0| < r
    rw [sub_zero, abs_of_pos (half_pos hr_pos)]
    exact half_lt_self hr_pos
  have hbound := (hr ⟨hδ_ball, hδ_pos_nn⟩).1
  let c : ℝ := (δ : ℝ) / L
  have hc_pos : 0 < c := div_pos hδ_pos hL
  let g : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) := fun x => c • T x
  have happrox : ApproximatesLinearOn g Z t δ := by
    intro x hx y hy
    simp only [g, Z, zero_apply, sub_zero, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos hc_pos]
    calc
      c * ‖T x - T y‖ ≤ c * (L * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (hlip x hx y hy) hc_pos.le
      _ = (c * L) * ‖x - y‖ := (mul_assoc c L _).symm
      _ = (δ : ℝ) * ‖x - y‖ := by dsimp [c]; rw [div_mul_cancel₀ _ hL.ne']
  have hg_zero : volume (g '' t) = 0 := by
    refine le_antisymm ?_ zero_le
    calc
      volume (g '' t) ≤ (m₀ : ℝ≥0∞) * volume t := hbound t g happrox
      _ = 0 := by rw [ht_null, mul_zero]
  have himg_smul : g '' t = c • (T '' t) := by
    ext z
    simp [g, Set.mem_smul_set]
  rw [himg_smul, volume.addHaar_smul_of_nonneg hc_pos.le] at hg_zero
  have hc_pow_pos : 0 < c ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) := pow_pos hc_pos _
  have hc_ne_zero :
      ENNReal.ofReal (c ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hc_pow_pos).ne'
  exact (mul_eq_zero.mp hg_zero).resolve_left hc_ne_zero

/-- **Lemma 7.25** (Rudin, p. 153): if `E ⊆ ℝ^k` has `m(E) = 0` and `T : ℝ^k → ℝ^k` has finite
pointwise slope `limsup` along `E` at every `x ∈ E`, then `m(T(E)) = 0`. -/
theorem lemma_7_25 {k : ℕ}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    (hEnull : volume E = 0)
    (hslope : ∀ x ∈ E, HasFiniteSlopeLimsupOn T E x) :
    volume (T '' E) = 0 := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq (EuclideanSpace ℝ (Fin k))
  let piece : ℕ → ℕ → ℕ → Set (EuclideanSpace ℝ (Fin k)) := fun N m p =>
    {x ∈ E | x ∈ ball (d p) (1 / (2 * ((m : ℝ) + 1))) ∧
      ∀ y ∈ E, dist y x < 1 / ((m : ℝ) + 1) → ‖T y - T x‖ ≤ ((N : ℝ) + 1) * ‖y - x‖}
  have hpiece_null : ∀ N m p : ℕ, volume (T '' piece N m p) = 0 := by
    intro N m p
    have ht_null : volume (piece N m p) = 0 :=
      measure_mono_null (fun x hx => hx.1) hEnull
    refine volume_image_eq_zero_of_lipschitz_piece ht_null (L := (N : ℝ) + 1) (by positivity) ?_
    intro x hx y hy
    have hdist : dist y x < 1 / ((m : ℝ) + 1) := by
      calc
        dist y x ≤ dist y (d p) + dist (d p) x := dist_triangle y (d p) x
        _ = dist y (d p) + dist x (d p) := by rw [dist_comm (d p) x]
        _ < 1 / (2 * ((m : ℝ) + 1)) + 1 / (2 * ((m : ℝ) + 1)) :=
          add_lt_add hy.2.1 hx.2.1
        _ = 1 / ((m : ℝ) + 1) := by
          have hm_ne : ((m : ℝ) + 1) ≠ 0 := by positivity
          field_simp [hm_ne]
          ring
    rw [norm_sub_rev (T x) (T y), norm_sub_rev x y]
    exact hx.2.2 y hy.1 hdist
  have hcover : E ⊆ ⋃ N : ℕ, ⋃ m : ℕ, ⋃ p : ℕ, piece N m p := by
    intro x hx
    obtain ⟨M, hM⟩ := hasFiniteSlopeLimsupOn_iff_exists_bound.mp (hslope x hx)
    obtain ⟨N, hN⟩ := exists_nat_ge M
    obtain ⟨r, hr_pos, hr⟩ := Metric.mem_nhdsWithin_iff.mp hM
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / r)
    have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hmr : 1 / ((m : ℝ) + 1) ≤ r := by
      have hlt : 1 / r < (m : ℝ) + 1 := by linarith
      exact (div_le_iff₀ hm1_pos).mpr
        ((le_of_lt ((div_lt_iff₀ hr_pos).mp hlt)).trans_eq (mul_comm _ _))
    have hrad_pos : (0 : ℝ) < 1 / (2 * ((m : ℝ) + 1)) := by positivity
    obtain ⟨p, hp⟩ := hd.exists_dist_lt x hrad_pos
    refine mem_iUnion.mpr ⟨N, mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨p, hx, ?_, ?_⟩⟩⟩
    · exact mem_ball.mpr hp
    · intro y hy hdist
      by_cases hyx : y = x
      · simp [hyx]
      · have hquot : ‖T y - T x‖ / ‖y - x‖ ≤ M :=
          hr ⟨lt_of_lt_of_le hdist hmr, hy, hyx⟩
        have hnorm_pos : 0 < ‖y - x‖ := norm_sub_pos_iff.mpr hyx
        have hle1 : ‖T y - T x‖ ≤ M * ‖y - x‖ := (div_le_iff₀ hnorm_pos).mp hquot
        have hle2 : M * ‖y - x‖ ≤ ((N : ℝ) + 1) * ‖y - x‖ :=
          mul_le_mul_of_nonneg_right (by linarith) hnorm_pos.le
        exact hle1.trans hle2
  have himg_sub : T '' E ⊆ ⋃ N : ℕ, ⋃ m : ℕ, ⋃ p : ℕ, T '' piece N m p := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨N, hN⟩ := mem_iUnion.mp (hcover hx)
    obtain ⟨m, hm⟩ := mem_iUnion.mp hN
    obtain ⟨p, hp⟩ := mem_iUnion.mp hm
    exact mem_iUnion.mpr ⟨N, mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨p, x, hp, rfl⟩⟩⟩
  exact measure_mono_null himg_sub
    (measure_iUnion_null fun N => measure_iUnion_null fun m => measure_iUnion_null (hpiece_null N m))

/-- **Lemma 7.25 (everywhere-differentiable special case)** (Rudin, p. 153): if `V ⊆ ℝ^k` is open,
`T : ℝ^k → ℝ^k` is differentiable at every point of `V`, and `E ⊆ V` has `m(E) = 0`, then
`m(T(E)) = 0`. -/
theorem lemma_7_25_differentiable {k : ℕ}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {V E : Set (EuclideanSpace ℝ (Fin k))}
    (_hV : IsOpen V) (hdiff : ∀ x ∈ V, DifferentiableAt ℝ T x)
    (hEV : E ⊆ V) (hEnull : volume E = 0) :
    volume (T '' E) = 0 := by
  refine lemma_7_25 hEnull fun x hx => hasFiniteSlopeLimsupOn_iff_exists_bound.mpr ?_
  have hd : HasFDerivAt T (fderiv ℝ T x) x := (hdiff x (hEV hx)).hasFDerivAt
  have ho := Asymptotics.isLittleO_iff.mp (hasFDerivAt_iff_isLittleO.mp hd) zero_lt_one
  refine ⟨‖fderiv ℝ T x‖ + 1, ?_⟩
  filter_upwards [nhdsWithin_le_nhds ho, self_mem_nhdsWithin] with y hy hy_mem
  have hnorm_pos : 0 < ‖y - x‖ := norm_sub_pos_iff.mpr hy_mem.2
  rw [div_le_iff₀ hnorm_pos]
  calc
    ‖T y - T x‖
      ≤ ‖T y - T x - fderiv ℝ T x (y - x)‖ + ‖fderiv ℝ T x (y - x)‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le (T y - T x - fderiv ℝ T x (y - x)) (fderiv ℝ T x (y - x))
    _ ≤ 1 * ‖y - x‖ + ‖fderiv ℝ T x‖ * ‖y - x‖ :=
        add_le_add hy ((fderiv ℝ T x).le_opNorm (y - x))
    _ = (‖fderiv ℝ T x‖ + 1) * ‖y - x‖ := by ring

end Node7_25

section Node7_26

/-- **Theorem 7.26 (Lebesgue-measurable image claim)** (Rudin, pp. 153–155): under hypotheses
(i)–(iii) of Theorem 7.26, `T(E)` is Lebesgue measurable (`NullMeasurableSet (T '' E) volume`) for
every Lebesgue-measurable subset `E ⊆ V`. -/
theorem theorem_7_26_nullMeasurable_image {k : ℕ}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {V X E : Set (EuclideanSpace ℝ (Fin k))}
    (_hV : IsOpen V) (_hcont : ContinuousOn T V)
    (_hXV : X ⊆ V) (hX : NullMeasurableSet X volume)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ T x) (hinj : InjOn T X)
    (hnull_compl : volume (T '' (V \ X)) = 0)
    (hEV : E ⊆ V) (hE : NullMeasurableSet E volume) :
    NullMeasurableSet (T '' E) volume := by
  have hdecomp : E = (E ∩ X) ∪ (E \ X) := (inter_union_sdiff E X).symm
  rw [hdecomp, image_union]
  have hEX_meas : NullMeasurableSet (T '' (E ∩ X)) volume :=
    MeasureTheory.nullMeasurable_image_of_fderivWithin volume
      (f' := fun x => fderiv ℝ T x)
      (hE.inter hX)
      (fun x hx => (hdiff x hx.2).hasFDerivAt.hasFDerivWithinAt)
      (hinj.mono inter_subset_right)
  have hEdiff_null : volume (T '' (E \ X)) = 0 :=
    measure_mono_null (image_mono (sdiff_subset_sdiff_left hEV)) hnull_compl
  exact hEX_meas.union (NullMeasurableSet.of_null hEdiff_null)

/-- **Theorem 7.26** (Rudin, pp. 153–155, Change of Variables): assume
(i) `X ⊆ V ⊆ ℝ^k`, `V` is open, and `T : V → ℝ^k` is continuous on `V`;
(ii) `X` is Lebesgue measurable (`NullMeasurableSet X volume`), `T` is injective on `X`, and `T` is
differentiable at every point of `X`;
(iii) `m(T(V \ X)) = 0`.
Put `Y = T(X)`. Then:
1. `T(E)` is Lebesgue measurable for every Lebesgue-measurable `E ⊆ V` (in particular `Y = T(X)` and
   `T(V)` are Lebesgue measurable, and `m(T(V) \ Y) = 0`);
2. for every Lebesgue-measurable `f : ℝ^k → [0, ∞]` (`NullMeasurable f volume`), the weighted
   product `x ↦ f(T(x)) |J_T(x)|` is Lebesgue measurable (`NullMeasurable` / `AEMeasurable`) on `X`;
3. `∫_Y f dm = ∫_X (f ∘ T) |J_T| dm` (and both equal `∫_{T(V)} f dm`). -/
theorem theorem_7_26 {k : ℕ}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {V X : Set (EuclideanSpace ℝ (Fin k))}
    (hV : IsOpen V) (hcont : ContinuousOn T V)
    (hXV : X ⊆ V) (hX : NullMeasurableSet X volume)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ T x) (hinj : InjOn T X)
    (hnull_compl : volume (T '' (V \ X)) = 0)
    {f : EuclideanSpace ℝ (Fin k) → ℝ≥0∞}
    (hf : NullMeasurable f volume) :
    (∀ E : Set (EuclideanSpace ℝ (Fin k)), E ⊆ V → NullMeasurableSet E volume →
        NullMeasurableSet (T '' E) volume) ∧
      NullMeasurableSet (T '' X) volume ∧
      NullMeasurableSet (T '' V) volume ∧
      NullMeasurable (fun x => f (T x) * ENNReal.ofReal |jacobian T x|) (volume.restrict X) ∧
      AEMeasurable (fun x => f (T x) * ENNReal.ofReal |jacobian T x|) (volume.restrict X) ∧
      (∫⁻ y in T '' X, f y ∂volume) =
        (∫⁻ x in X, f (T x) * ENNReal.ofReal |jacobian T x| ∂volume) ∧
      (∫⁻ y in T '' V, f y ∂volume) =
        (∫⁻ x in X, f (T x) * ENNReal.ofReal |jacobian T x| ∂volume) := by
  have himg_all : ∀ E : Set (EuclideanSpace ℝ (Fin k)), E ⊆ V → NullMeasurableSet E volume →
      NullMeasurableSet (T '' E) volume :=
    fun E hEV hE => theorem_7_26_nullMeasurable_image hV hcont hXV hX hdiff hinj hnull_compl hEV hE
  have hY_meas : NullMeasurableSet (T '' X) volume := himg_all X hXV hX
  have hTV_meas : NullMeasurableSet (T '' V) volume :=
    himg_all V Subset.rfl hV.measurableSet.nullMeasurableSet
  obtain ⟨B, hBX, hB_meas, hB_ae⟩ := hX.exists_measurable_subset_ae_eq
  have hTB_ae : T '' B =ᵐ[volume] T '' X := by
    have hsplit : X = B ∪ (X \ B) := (union_sdiff_cancel hBX).symm
    have hXB_null : volume (X \ B) = 0 := (ae_eq_set.mp hB_ae).2
    have hTXB_null : volume (T '' (X \ B)) = 0 :=
      MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        (fun x hx => (hdiff x hx.1).differentiableWithinAt) hXB_null
    rw [hsplit, image_union]
    exact Filter.EventuallyEq.symm
      (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr hTXB_null))
  have hTV_ae : T '' X =ᵐ[volume] T '' V := by
    have hsplit : V = X ∪ (V \ X) := (union_sdiff_cancel hXV).symm
    rw [hsplit, image_union]
    exact Filter.EventuallyEq.symm
      (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr hnull_compl))
  have hJ_meas : Measurable (fun x => ENNReal.ofReal |jacobian T x|) :=
    ENNReal.measurable_ofReal.comp
      (continuous_abs.measurable.comp
        (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ T)))
  let f₀ : EuclideanSpace ℝ (Fin k) → ℝ≥0∞ := hf.aemeasurable.mk f
  have hf₀_meas : Measurable f₀ := hf.aemeasurable.measurable_mk
  have hff₀_ae : f =ᵐ[volume] f₀ := hf.aemeasurable.ae_eq_mk
  let M : Set (EuclideanSpace ℝ (Fin k)) := toMeasurable volume {y | f y ≠ f₀ y}
  have hM_meas : MeasurableSet M := measurableSet_toMeasurable volume _
  have hM_null : volume M = 0 := by
    rw [measure_toMeasurable]
    exact hff₀_ae
  classical
  let T₀ : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) := B.piecewise T 0
  have hT₀_meas : Measurable T₀ :=
    (hcont.mono (hBX.trans hXV)).measurable_piecewise continuous_zero.continuousOn hB_meas
  let B₁ : Set (EuclideanSpace ℝ (Fin k)) := B ∩ T₀ ⁻¹' M
  have hB₁_meas : MeasurableSet B₁ := hB_meas.inter (hM_meas.preimage hT₀_meas)
  have hTB₁_null : volume (T '' B₁) = 0 := by
    refine measure_mono_null ?_ hM_null
    rintro _ ⟨x, ⟨hxB, hxM⟩, rfl⟩
    have hT₀_eq : T₀ x = T x := Set.piecewise_eq_of_mem _ _ _ hxB
    change T₀ x ∈ M at hxM
    rwa [hT₀_eq] at hxM
  have hlint_B₁ : (∫⁻ x in B₁, ENNReal.ofReal |(fderiv ℝ T x).det| ∂volume) = 0 := by
    rw [MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image volume hB₁_meas
      (fun x hx => (hdiff x (hBX hx.1)).hasFDerivAt.hasFDerivWithinAt)
      (hinj.mono (inter_subset_left.trans hBX)), hTB₁_null]
  have hae_B₁_zero : ∀ᵐ x ∂(volume.restrict B₁), ENNReal.ofReal |jacobian T x| = 0 :=
    (lintegral_eq_zero_iff hJ_meas).mp hlint_B₁
  have hae_B_B₁ : ∀ᵐ x ∂(volume.restrict B), x ∈ B₁ → ENNReal.ofReal |jacobian T x| = 0 := by
    have hrestr : volume.restrict B₁ = (volume.restrict B).restrict B₁ := by
      rw [Measure.restrict_restrict hB₁_meas, inter_eq_left.mpr inter_subset_left]
    rw [← ae_restrict_iff' hB₁_meas, ← hrestr]
    exact hae_B₁_zero
  have hae_eq_B :
      (fun x => f (T x) * ENNReal.ofReal |jacobian T x|) =ᵐ[volume.restrict B]
        (fun x => f₀ (T₀ x) * ENNReal.ofReal |jacobian T x|) := by
    filter_upwards [ae_restrict_mem hB_meas, hae_B_B₁] with x hxB hxB₁
    by_cases hxM : x ∈ B₁
    · rw [hxB₁ hxM, mul_zero, mul_zero]
    · have hT₀_eq : T₀ x = T x := Set.piecewise_eq_of_mem _ _ _ hxB
      have hnotM : T x ∉ M := by
        intro hmem
        exact hxM ⟨hxB, by simpa [hT₀_eq] using hmem⟩
      have hnot_ne : ¬ f (T x) ≠ f₀ (T x) :=
        fun hne => hnotM (subset_toMeasurable volume _ hne)
      push Not at hnot_ne
      rw [hnot_ne, hT₀_eq]
  have haemeas_B :
      AEMeasurable (fun x => f (T x) * ENNReal.ofReal |jacobian T x|) (volume.restrict B) :=
    ((hf₀_meas.comp hT₀_meas).mul hJ_meas).aemeasurable.congr hae_eq_B.symm
  have hrestr_BX : volume.restrict B = volume.restrict X :=
    Measure.restrict_congr_set hB_ae
  have haemeas_X :
      AEMeasurable (fun x => f (T x) * ENNReal.ofReal |jacobian T x|) (volume.restrict X) :=
    hrestr_BX ▸ haemeas_B
  have hlint_B :
      (∫⁻ y in T '' B, f y ∂volume) =
        (∫⁻ x in B, f (T x) * ENNReal.ofReal |jacobian T x| ∂volume) := by
    calc
      (∫⁻ y in T '' B, f y ∂volume)
        = ∫⁻ x in B, ENNReal.ofReal |(fderiv ℝ T x).det| * f (T x) ∂volume :=
          MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hB_meas
            (fun x hx => (hdiff x (hBX hx)).hasFDerivAt.hasFDerivWithinAt)
            (hinj.mono hBX) f
      _ = ∫⁻ x in B, f (T x) * ENNReal.ofReal |jacobian T x| ∂volume := by
          refine setLIntegral_congr_fun hB_meas fun x _ => ?_
          rw [mul_comm]; rfl
  have hlint_X :
      (∫⁻ y in T '' X, f y ∂volume) =
        (∫⁻ x in X, f (T x) * ENNReal.ofReal |jacobian T x| ∂volume) := by
    rw [← setLIntegral_congr hTB_ae, hlint_B, setLIntegral_congr hB_ae]
  have hlint_V :
      (∫⁻ y in T '' V, f y ∂volume) =
        (∫⁻ x in X, f (T x) * ENNReal.ofReal |jacobian T x| ∂volume) := by
    rw [← setLIntegral_congr hTV_ae, hlint_X]
  exact ⟨himg_all, hY_meas, hTV_meas, haemeas_X.nullMeasurable, haemeas_X, hlint_X, hlint_V⟩

/-- **Theorem 7.26 (equation (8) when `m(V \ X) = 0`)** (Rudin, p. 154): if in addition
`m(V \ X) = 0`, then `∫_{T(V)} f dm = ∫_V (f ∘ T) |J_T| dm`. -/
theorem theorem_7_26_ae_open {k : ℕ}
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {V X : Set (EuclideanSpace ℝ (Fin k))}
    (hV : IsOpen V) (hcont : ContinuousOn T V)
    (hXV : X ⊆ V) (hX : NullMeasurableSet X volume)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ T x) (hinj : InjOn T X)
    (hnull_compl_dom : volume (V \ X) = 0)
    (hnull_compl_img : volume (T '' (V \ X)) = 0)
    {f : EuclideanSpace ℝ (Fin k) → ℝ≥0∞}
    (hf : NullMeasurable f volume) :
    (∫⁻ y in T '' V, f y ∂volume) =
      (∫⁻ x in V, f (T x) * ENNReal.ofReal |jacobian T x| ∂volume) := by
  have hmain := (theorem_7_26 hV hcont hXV hX hdiff hinj hnull_compl_img hf).2.2.2.2.2.2
  have hXV_ae : X =ᵐ[volume] V := by
    rw [ae_eq_set]
    exact ⟨measure_mono_null (sdiff_eq_empty.mpr hXV ▸ Subset.rfl) measure_empty, hnull_compl_dom⟩
  rw [hmain, setLIntegral_congr hXV_ae]

/-- **Theorem 7.26 (`L¹` / Bochner integral corollary)** (Rudin, p. 155): under hypotheses
(i)–(iii), a Banach-valued function `g` is integrable on `Y = T(X)` (or `T(V)`) iff
`x ↦ |J_T(x)| • g(T(x))` is integrable on `X`, and `∫_Y g dm = ∫_X |J_T| • (g ∘ T) dm`. -/
theorem theorem_7_26_integrable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {V X : Set (EuclideanSpace ℝ (Fin k))}
    (_hV : IsOpen V) (_hcont : ContinuousOn T V)
    (_hXV : X ⊆ V) (hX : NullMeasurableSet X volume)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ T x) (hinj : InjOn T X)
    (_hnull_compl : volume (T '' (V \ X)) = 0)
    (g : EuclideanSpace ℝ (Fin k) → E) :
    (IntegrableOn g (T '' X) volume ↔
        IntegrableOn (fun x => |jacobian T x| • g (T x)) X volume) ∧
      (∫ y in T '' X, g y ∂volume) =
        (∫ x in X, |jacobian T x| • g (T x) ∂volume) := by
  obtain ⟨B, hBX, hB_meas, hB_ae⟩ := hX.exists_measurable_subset_ae_eq
  have hTB_ae : T '' B =ᵐ[volume] T '' X := by
    have hsplit : X = B ∪ (X \ B) := (union_sdiff_cancel hBX).symm
    have hXB_null : volume (X \ B) = 0 := (ae_eq_set.mp hB_ae).2
    have hTXB_null : volume (T '' (X \ B)) = 0 :=
      MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        (fun x hx => (hdiff x hx.1).differentiableWithinAt) hXB_null
    rw [hsplit, image_union]
    exact Filter.EventuallyEq.symm
      (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr hTXB_null))
  have hint_B :
      IntegrableOn g (T '' B) volume ↔
        IntegrableOn (fun x => |jacobian T x| • g (T x)) B volume :=
    MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hB_meas
      (fun x hx => (hdiff x (hBX hx)).hasFDerivAt.hasFDerivWithinAt) (hinj.mono hBX) g
  have heq_B :
      (∫ y in T '' B, g y ∂volume) =
        (∫ x in B, |jacobian T x| • g (T x) ∂volume) :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume hB_meas
      (fun x hx => (hdiff x (hBX hx)).hasFDerivAt.hasFDerivWithinAt) (hinj.mono hBX) g
  exact ⟨by rw [← integrableOn_congr_set_ae hTB_ae, hint_B, integrableOn_congr_set_ae hB_ae],
    by rw [← setIntegral_congr_set hTB_ae, heq_B, setIntegral_congr_set hB_ae]⟩

/-! #### Non-measurability of unweighted `f ∘ T` under the full hypotheses of Theorem 7.26 -/

private def rationalSetoid7 : Setoid ℝ where
  r x y := ∃ q : ℚ, x - y = (q : ℝ)
  iseqv :=
    ⟨fun x => ⟨0, by simp⟩,
      by rintro x y ⟨q, hq⟩; exact ⟨-q, by push_cast; linarith⟩,
      by rintro x y z ⟨q, hq⟩ ⟨r, hr⟩; exact ⟨q + r, by push_cast; linarith⟩⟩

private def vitaliTransversal7 : Set ℝ :=
  Set.range (Quotient.out : Quotient rationalSetoid7 → ℝ)

private theorem vitaliTransversal7_unique {x y : ℝ}
    (hx : x ∈ vitaliTransversal7) (hy : y ∈ vitaliTransversal7)
    {q : ℚ} (hxy : x - y = (q : ℝ)) : x = y := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hab : a = b := by
    simpa only [Quotient.out_eq] using (Quotient.sound (s := rationalSetoid7) ⟨q, hxy⟩)
  rw [hab]

private theorem bounded_vitaliTransversal7_null {W : Set ℝ}
    (hW : W ⊆ vitaliTransversal7) (hm : NullMeasurableSet W volume)
    {n : ℝ} (hb : W ⊆ Icc (-n) n) : volume W = 0 := by
  classical
  let Q01 := {q : ℚ // q ∈ Icc (0 : ℚ) 1}
  have : Infinite Q01 := (Set.Icc_infinite (by norm_num : (0 : ℚ) < 1)).to_subtype
  let F : Q01 → Set ℝ := fun q => {x : ℝ | x - (q.1 : ℝ) ∈ W}
  have hdisj : Pairwise fun q r : Q01 => Disjoint (F q) (F r) := by
    intro q r hqr
    refine Set.disjoint_left.mpr fun x hx hy => ?_
    have heq : x - (q.1 : ℝ) = x - (r.1 : ℝ) :=
      vitaliTransversal7_unique (hW hx) (hW hy) (q := r.1 - q.1) (by push_cast; ring)
    have hcast : (q.1 : ℝ) = (r.1 : ℝ) := by linarith
    exact hqr (Subtype.ext (Rat.cast_injective hcast))
  have hFm (q : Q01) : NullMeasurableSet (F q) volume :=
    hm.preimage (measurePreserving_sub_right volume (q.1 : ℝ)).quasiMeasurePreserving
  have hvol (q : Q01) : volume (F q) = volume W := by
    change volume ((fun x : ℝ => x - (q.1 : ℝ)) ⁻¹' W) = volume W
    simpa only [sub_eq_add_neg] using measure_preimage_add_right volume (-(q.1 : ℝ)) W
  have hbound : (⋃ q : Q01, F q) ⊆ Icc (-n) (n + 1) := by
    intro x hx
    obtain ⟨q, hq⟩ := mem_iUnion.mp hx
    have hw := hb hq
    have hq0 : (0 : ℝ) ≤ (q.1 : ℝ) := by exact_mod_cast q.2.1
    have hq1 : (q.1 : ℝ) ≤ (1 : ℝ) := by exact_mod_cast q.2.2
    exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  by_contra hne
  have htop : volume (⋃ q : Q01, F q) = ∞ := by
    rw [measure_iUnion₀ (fun i j hij => (hdisj hij).aedisjoint) hFm]
    simp_rw [hvol]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hne
  have hle : volume (⋃ q : Q01, F q) ≤ volume (Icc (-n) (n + 1)) := measure_mono hbound
  rw [htop] at hle
  exact isCompact_Icc.measure_lt_top.ne (top_unique hle)

private theorem exists_nonNullMeasurable_subset_of_pos_volume_Icc01
    {K : Set ℝ} (hK_sub : K ⊆ Icc (0 : ℝ) 1) (hK_pos : 0 < volume K) :
    ∃ N : Set ℝ, N ⊆ K ∧ ¬ NullMeasurableSet N volume := by
  by_contra hall
  push Not at hall
  let piece : ℚ → Set ℝ := fun q => K ∩ {x : ℝ | x - (q : ℝ) ∈ vitaliTransversal7}
  have hnull : ∀ q : ℚ, volume (piece q) = 0 := by
    intro q
    have hmeas : NullMeasurableSet (piece q) volume := hall (piece q) inter_subset_left
    let W : Set ℝ := (fun x : ℝ => x + (q : ℝ)) ⁻¹' piece q
    have hW_sub : W ⊆ vitaliTransversal7 := by
      intro y hy
      change y + (q : ℝ) ∈ K ∧ (y + (q : ℝ)) - (q : ℝ) ∈ vitaliTransversal7 at hy
      simpa using hy.2
    have hW_meas : NullMeasurableSet W volume :=
      hmeas.preimage (measurePreserving_add_right volume (q : ℝ)).quasiMeasurePreserving
    have hW_bdd : W ⊆ Icc (-(|(q : ℝ)| + 1)) (|(q : ℝ)| + 1) := by
      intro y hy
      have hyK : y + (q : ℝ) ∈ Icc (0 : ℝ) 1 := hK_sub hy.1
      have hq_abs := le_abs_self (q : ℝ)
      have hq_neg := neg_abs_le (q : ℝ)
      exact ⟨by linarith [hyK.1], by linarith [hyK.2]⟩
    have hW_zero : volume W = 0 := bounded_vitaliTransversal7_null hW_sub hW_meas hW_bdd
    have hvol_eq : volume W = volume (piece q) :=
      measure_preimage_add_right volume (q : ℝ) (piece q)
    exact hvol_eq.symm.trans hW_zero
  have hcover : K ⊆ ⋃ q : ℚ, piece q := by
    intro x hx
    let r : ℝ := Quotient.out (Quotient.mk rationalSetoid7 x)
    have hr_mem : r ∈ vitaliTransversal7 := ⟨Quotient.mk rationalSetoid7 x, rfl⟩
    have hrel : rationalSetoid7.r x r :=
      Quotient.exact (Quotient.out_eq (Quotient.mk rationalSetoid7 x)).symm
    obtain ⟨q, hq⟩ := hrel
    refine mem_iUnion.mpr ⟨q, hx, ?_⟩
    change x - (q : ℝ) ∈ vitaliTransversal7
    have hxr : x - (q : ℝ) = r := by linarith
    rwa [hxr]
  have hK_zero : volume K = 0 := measure_mono_null hcover (measure_iUnion_null hnull)
  exact hK_pos.ne' hK_zero

/-- **Theorem 7.26 (unweighted `f ∘ T` non-measurability witness)** (Rudin, p. 154 / `SCOPING-C.md`
row 7.26): even when `V = X = ℝ^1`, `T : ℝ^1 → ℝ^1` is everywhere differentiable and **globally
injective** on `ℝ^1` (`m(V \ X) = 0` and `m(T(V \ X)) = 0`), there exists a Lebesgue-measurable
function `f : ℝ^1 → [0, ∞]` (`NullMeasurable f volume`) such that the unweighted composition
`f ∘ T` is **not** Lebesgue measurable (`¬ NullMeasurable (f ∘ T) (volume.restrict X)` and
`¬ NullMeasurable (f ∘ T) volume`), whereas the Jacobian-weighted product
`x ↦ f(T(x)) |J_T(x)|` is Lebesgue measurable (`NullMeasurable`). -/
theorem theorem_7_26_unweighted_not_nullMeasurable :
    ∃ (T : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
      (f : EuclideanSpace ℝ (Fin 1) → ℝ≥0∞),
      Differentiable ℝ T ∧
      Function.Injective T ∧
      NullMeasurable f volume ∧
      NullMeasurable (fun x => f (T x) * ENNReal.ofReal |jacobian T x|) volume ∧
      ¬ NullMeasurable (f ∘ T) volume := by
  obtain ⟨qseq, hqseq⟩ := exists_surjective_nat ℚ
  let U : Set ℝ := ⋃ n : ℕ, ball ((qseq n : ℚ) : ℝ) (1 / (8 * (2 : ℝ) ^ n))
  have hU_open : IsOpen U := isOpen_iUnion fun _ => Metric.isOpen_ball
  have hU_vol : volume U ≤ ENNReal.ofReal (1 / 2) := by
    calc
      volume U
        ≤ ∑' n : ℕ, volume (ball ((qseq n : ℚ) : ℝ) (1 / (8 * (2 : ℝ) ^ n))) :=
          measure_iUnion_le _
      _ = ∑' n : ℕ, ENNReal.ofReal (1 / 4 * ((1 / 2 : ℝ) ^ n)) := by
          congr 1; ext n
          rw [Real.volume_ball]
          congr 1
          rw [one_div_pow]
          ring
      _ = ENNReal.ofReal (∑' n : ℕ, (1 / 4 : ℝ) * ((1 / 2 : ℝ) ^ n)) := by
          refine (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) ?_).symm
          exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (1 / 4)
      _ = ENNReal.ofReal (1 / 2) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          norm_num
  let K : Set ℝ := Icc (0 : ℝ) 1 \ U
  have hK_closed : IsClosed K := isClosed_Icc.sdiff hU_open
  have hK_pos : 0 < volume K := by
    have hcov : Icc (0 : ℝ) 1 ⊆ K ∪ U := fun x hx =>
      by_cases (fun hxU : x ∈ U => Or.inr hxU) (fun hxU => Or.inl ⟨hx, hxU⟩)
    have h1 : (1 : ℝ≥0∞) ≤ volume K + volume U := by
      calc
        (1 : ℝ≥0∞) = volume (Icc (0 : ℝ) 1) := by simp [Real.volume_Icc]
        _ ≤ volume (K ∪ U) := measure_mono hcov
        _ ≤ volume K + volume U := measure_union_le K U
    by_contra h0
    have hK0 : volume K = 0 := nonpos_iff_eq_zero.mp (not_lt.mp h0)
    rw [hK0, zero_add] at h1
    have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / 2) := h1.trans hU_vol
    have hlt : ENNReal.ofReal (1 / 2) < (1 : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (by norm_num)
    exact (not_le_of_gt hlt) hle
  have hK_nonempty : K.Nonempty := nonempty_of_measure_ne_zero hK_pos.ne'
  let g : ℝ → ℝ := fun t => Metric.infDist t K
  have hg_cont : Continuous g := Metric.continuous_infDist_pt K
  have hg_nonneg : ∀ t : ℝ, 0 ≤ g t := fun t => Metric.infDist_nonneg
  let φ : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, g t
  have hφ_deriv : ∀ x : ℝ, HasDerivAt φ (g x) x := fun x =>
    (hg_cont.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hφ_strict : StrictMono φ := by
    intro a b hab
    obtain ⟨q, hqa, hqb⟩ := exists_rat_btwn hab
    obtain ⟨n, hn⟩ := hqseq q
    have hq_mem_U : (q : ℝ) ∈ U := mem_iUnion.mpr ⟨n, hn ▸ mem_ball_self (by positivity)⟩
    have hq_not_K : (q : ℝ) ∉ K := fun h => h.2 hq_mem_U
    have hgq_pos : 0 < g (q : ℝ) :=
      (hK_closed.notMem_iff_infDist_pos hK_nonempty).mp hq_not_K
    obtain ⟨δ, hδ_pos, hδ⟩ :=
      Metric.continuousAt_iff.mp (hg_cont.continuousAt (x := (q : ℝ))) (g (q : ℝ) / 2)
        (half_pos hgq_pos)
    let c := max a ((q : ℝ) - δ / 2)
    let d := min b ((q : ℝ) + δ / 2)
    have hcd : c < d :=
      lt_min (max_lt hab (by linarith)) (max_lt (by linarith) (by linarith))
    have hac : a ≤ c := le_max_left _ _
    have hdb : d ≤ b := min_le_left _ _
    have hsub_add :
        φ b - φ a =
          (∫ t in a..c, g t) + (∫ t in c..d, g t) + (∫ t in d..b, g t) := by
      have h1 := intervalIntegral.integral_add_adjacent_intervals
        (hg_cont.intervalIntegrable (μ := volume) 0 a)
        (hg_cont.intervalIntegrable (μ := volume) a b)
      have hsub : φ b - φ a = ∫ t in a..b, g t := by dsimp [φ]; linarith
      have h2 := intervalIntegral.integral_add_adjacent_intervals
        (hg_cont.intervalIntegrable (μ := volume) a c)
        (hg_cont.intervalIntegrable (μ := volume) c b)
      have h3 := intervalIntegral.integral_add_adjacent_intervals
        (hg_cont.intervalIntegrable (μ := volume) c d)
        (hg_cont.intervalIntegrable (μ := volume) d b)
      linarith
    have hnonneg_ac : 0 ≤ ∫ t in a..c, g t :=
      intervalIntegral.integral_nonneg hac fun t _ => hg_nonneg t
    have hnonneg_db : 0 ≤ ∫ t in d..b, g t :=
      intervalIntegral.integral_nonneg hdb fun t _ => hg_nonneg t
    have hpos_cd : 0 < ∫ t in c..d, g t := by
      have hlow : ∀ t ∈ Icc c d, g (q : ℝ) / 2 ≤ g t := by
        intro t ht
        have hdist : dist t (q : ℝ) < δ := by
          rw [Real.dist_eq, abs_lt]
          have hc_ge : (q : ℝ) - δ / 2 ≤ c := le_max_right _ _
          have hd_le : d ≤ (q : ℝ) + δ / 2 := min_le_right _ _
          exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
        have hlt := hδ hdist
        rw [Real.dist_eq, abs_lt] at hlt
        linarith
      calc
        0 < (d - c) * (g (q : ℝ) / 2) := mul_pos (sub_pos.mpr hcd) (half_pos hgq_pos)
        _ = ∫ _ in c..d, (g (q : ℝ) / 2) := by simp [mul_div_assoc]
        _ ≤ ∫ t in c..d, g t :=
            intervalIntegral.integral_mono_on hcd.le
              (intervalIntegrable_const) (hg_cont.intervalIntegrable c d) hlow
    linarith
  have hφK_null : volume (φ '' K) = 0 := by
    rw [← MeasureTheory.lintegral_deriv_eq_volume_image_of_monotoneOn hK_closed.measurableSet
      (fun x _ => (hφ_deriv x).hasDerivWithinAt) (hφ_strict.monotone.monotoneOn K)]
    have h0 : ∀ x ∈ K, ENNReal.ofReal (g x) = 0 := by
      intro x hx
      rw [show g x = 0 from Metric.infDist_zero_of_mem hx, ENNReal.ofReal_zero]
    exact setLIntegral_eq_zero hK_closed.measurableSet h0
  obtain ⟨N, hNK, hN_not_meas⟩ :=
    exists_nonNullMeasurable_subset_of_pos_volume_Icc01 sdiff_subset hK_pos
  have hφN_null : volume (φ '' N) = 0 := measure_mono_null (image_mono hNK) hφK_null
  let me : EuclideanSpace ℝ (Fin 1) ≃ᵐ ℝ :=
    (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)
  have hme_mp : MeasurePreserving me volume volume :=
    (volume_preserving_funUnique (Fin 1) ℝ).comp
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1))
  have hme_eq_e1 : (me : EuclideanSpace ℝ (Fin 1) → ℝ) = euclideanFin1Equiv := by
    ext p; rfl
  have hme_symm_eq_e1 : (me.symm : ℝ → EuclideanSpace ℝ (Fin 1)) = euclideanFin1Equiv.symm := by
    ext t; rfl
  let T : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) :=
    euclideanFin1Equiv.symm ∘ φ ∘ euclideanFin1Equiv
  have hT_diff : Differentiable ℝ T := by
    intro p
    refine (euclideanFin1Equiv.symm : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).differentiableAt.comp p ?_
    exact (hφ_deriv (euclideanFin1Equiv p)).differentiableAt.comp p
      (euclideanFin1Equiv : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).differentiableAt
  have hT_inj : Function.Injective T :=
    euclideanFin1Equiv.symm.injective.comp (hφ_strict.injective.comp euclideanFin1Equiv.injective)
  let Y₀ : Set (EuclideanSpace ℝ (Fin 1)) := me.symm '' (φ '' N)
  have hY₀_null : volume Y₀ = 0 := by
    have hpre : me ⁻¹' (φ '' N) = Y₀ := by
      ext p
      simp only [Y₀, mem_preimage, mem_image]
      constructor
      · rintro ⟨t, ht, htp⟩
        exact ⟨φ t, ⟨t, ht, rfl⟩, by rw [htp, me.symm_apply_apply]⟩
      · rintro ⟨_, ⟨t, ht, rfl⟩, htp⟩
        exact ⟨t, ht, by rw [← htp, me.apply_symm_apply]⟩
    rw [← hpre, hme_mp.measure_preimage (NullMeasurableSet.of_null hφN_null)]
    exact hφN_null
  let f : EuclideanSpace ℝ (Fin 1) → ℝ≥0∞ := Set.indicator Y₀ 1
  have hf_nullMeas : NullMeasurable f volume := by
    have hae : f =ᵐ[volume] 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null (fun y hy => ?_) hY₀_null
      by_contra hy_not
      exact hy (Set.indicator_of_notMem hy_not 1)
    exact aemeasurable_zero.congr hae.symm |>.nullMeasurable
  have hw_nullMeas :
      NullMeasurable (fun x => f (T x) * ENNReal.ofReal |jacobian T x|) volume := by
    have hmain := theorem_7_26 (V := univ) (X := univ) isOpen_univ hT_diff.continuous.continuousOn
      Subset.rfl MeasurableSet.univ.nullMeasurableSet (fun x _ => hT_diff x) hT_inj.injOn
      (by simp) hf_nullMeas
    simpa [Measure.restrict_univ] using hmain.2.2.2.1
  have hcomp_not : ¬ NullMeasurable (f ∘ T) volume := by
    intro hnm
    have hpre_meas : NullMeasurableSet ((f ∘ T) ⁻¹' {(1 : ℝ≥0∞)}) volume :=
      hnm (measurableSet_singleton 1)
    have hpre_eq : (f ∘ T) ⁻¹' {(1 : ℝ≥0∞)} = me ⁻¹' N := by
      ext p
      simp only [Function.comp_apply, mem_preimage, mem_singleton_iff, f, Y₀]
      by_cases hp : T p ∈ me.symm '' (φ '' N)
      · simp only [Set.indicator_of_mem hp, Pi.one_apply, true_iff]
        obtain ⟨u, ⟨t, htN, rfl⟩, hu⟩ := hp
        have hTp : T p = me.symm (φ (me p)) := by
          simp [T, ← hme_eq_e1, ← hme_symm_eq_e1]
        rw [hTp] at hu
        have hφeq : φ t = φ (me p) := me.symm.injective hu
        have hteq : t = me p := hφ_strict.injective hφeq
        exact hteq ▸ htN
      · simp only [Set.indicator_of_notMem hp, zero_ne_one, false_iff]
        intro hpN
        apply hp
        refine ⟨φ (me p), ⟨me p, hpN, rfl⟩, ?_⟩
        simp [T, ← hme_eq_e1, ← hme_symm_eq_e1]
    rw [hpre_eq] at hpre_meas
    have hN_meas : NullMeasurableSet N volume := by
      have hsymm_pre : me.symm ⁻¹' (me ⁻¹' N) = N := by
        ext t; simp
      rw [← hsymm_pre]
      exact hpre_meas.preimage hme_mp.symm.quasiMeasurePreserving
    exact hN_not_meas hN_meas
  exact ⟨T, f, hT_diff, hT_inj, hf_nullMeas, hw_nullMeas, hcomp_not⟩

/-! #### Closing one-dimensional absolutely continuous nondecreasing special case of `7.26` -/

/-- **Theorem 7.26 (one-variable AC nondecreasing special case)** (Rudin, pp. 155–156): if
`φ : ℝ → ℝ` is nondecreasing and absolutely continuous on `[a, b]` (`a ≤ b`) with `φ(a) = α` and
`φ(b) = β`, then for every nonnegative **Lebesgue-measurable** function `f : ℝ → [0, ∞]`
(`NullMeasurable f volume`), the product `x ↦ f(φ(x)) φ'(x)` is Lebesgue measurable on `[a, b]` and
`∫_{[α, β]} f(t) dt = ∫_{[a, b]} f(φ(x)) φ'(x) dx`. -/
theorem theorem_7_26_oneDim_ac_monotone {φ : ℝ → ℝ} {a b α β : ℝ}
    (hab : a ≤ b) (hmono : MonotoneOn φ (Icc a b))
    (hac : BookAbsolutelyContinuousOnReal φ a b)
    (hφa : φ a = α) (hφb : φ b = β)
    {f : ℝ → ℝ≥0∞} (hf : NullMeasurable f volume) :
    NullMeasurable (fun x => f (φ x) * ENNReal.ofReal (deriv φ x)) (volume.restrict (Icc a b)) ∧
      (∫⁻ t in Icc α β, f t ∂volume) =
        (∫⁻ x in Icc a b, f (φ x) * ENNReal.ofReal (deriv φ x) ∂volume) := by
  have hcont : ContinuousOn φ (Icc a b) := hac.continuousOn hab
  rcases hab.eq_or_lt with rfl | hab_lt
  · have hαβ : α = β := hφa.symm.trans hφb
    subst hαβ
    have ha_null : volume (Icc a a) = 0 := by rw [Icc_self]; exact measure_singleton a
    have hα_null : volume (Icc α α) = 0 := by rw [Icc_self]; exact measure_singleton α
    have hrestr_zero : volume.restrict (Icc a a) = 0 :=
      Measure.restrict_eq_zero.mpr ha_null
    refine ⟨?_, ?_⟩
    · rw [hrestr_zero]
      exact aemeasurable_zero_measure.nullMeasurable
    · rw [setLIntegral_measure_zero _ _ hα_null, setLIntegral_measure_zero _ _ ha_null]
  have h18 := theorem_7_18 hab hcont hmono
  have hlusin : ∀ E : Set ℝ, E ⊆ Icc a b → volume E = 0 → volume (φ '' E) = 0 :=
    h18.1.mp hac
  have hae_diff : ∀ᵐ x ∂(volume.restrict (Icc a b)), DifferentiableAt ℝ φ x :=
    (h18.2.1.mp hlusin).1
  let Z₀ : Set ℝ := {x ∈ Ioo a b | ¬ DifferentiableAt ℝ φ x}
  have hZ₀_null : volume Z₀ = 0 := by
    have hae_unres := (ae_restrict_iff' measurableSet_Icc).mp hae_diff
    rw [ae_iff] at hae_unres
    refine measure_mono_null (fun x hx => ?_) hae_unres
    intro himp
    exact hx.2 (himp (Ioo_subset_Icc_self hx.1))
  let Z : Set ℝ := toMeasurable volume Z₀ ∩ Ioo a b
  have hZ_meas : MeasurableSet Z := (measurableSet_toMeasurable volume Z₀).inter measurableSet_Ioo
  have hZ_null : volume Z = 0 :=
    measure_mono_null inter_subset_left (by rw [measure_toMeasurable]; exact hZ₀_null)
  let S : Set ℝ := Ioo a b \ Z
  have hS_meas : MeasurableSet S := measurableSet_Ioo.diff hZ_meas
  have hS_sub_Icc : S ⊆ Icc a b := sdiff_subset.trans Ioo_subset_Icc_self
  have hIcc_diff_S_null : volume (Icc a b \ S) = 0 := by
    have hsub : Icc a b \ S ⊆ ({a, b} : Set ℝ) ∪ Z := by
      intro x ⟨hxIcc, hxnotS⟩
      rcases hxIcc.1.eq_or_lt with hax_eq | hax
      · rw [← hax_eq]
        exact Or.inl (mem_insert a {b})
      · rcases hxIcc.2.eq_or_lt with hxb_eq | hxb
        · rw [hxb_eq]
          exact Or.inl (mem_insert_of_mem a (mem_singleton b))
        · refine Or.inr ?_
          by_contra hxnotZ
          exact hxnotS ⟨⟨hax, hxb⟩, hxnotZ⟩
    have hends_null : volume ({a, b} : Set ℝ) = 0 :=
      (Set.toFinite ({a, b} : Set ℝ)).measure_zero volume
    exact le_antisymm
      ((measure_mono hsub).trans ((measure_union_le _ _).trans (by rw [hends_null, hZ_null, add_zero])))
      zero_le
  have hS_ae_Icc : S =ᵐ[volume] Icc a b := by
    rw [ae_eq_set]
    exact ⟨measure_mono_null (sdiff_eq_empty.mpr hS_sub_Icc ▸ Subset.rfl) measure_empty,
      hIcc_diff_S_null⟩
  have hderiv_S : ∀ x ∈ S, HasDerivWithinAt φ (deriv φ x) S x := by
    intro x ⟨hxIoo, hxnotZ⟩
    have hd : DifferentiableAt ℝ φ x := by
      by_contra hnd
      exact hxnotZ ⟨subset_toMeasurable volume Z₀ ⟨hxIoo, hnd⟩, hxIoo⟩
    exact hd.hasDerivAt.hasDerivWithinAt
  have himg_Icc : φ '' Icc a b = Icc α β := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨hφa ▸ hmono (left_mem_Icc.mpr hab) hx hx.1,
        hφb ▸ hmono hx (right_mem_Icc.mpr hab) hx.2⟩
    · have hsub : Icc (φ a) (φ b) ⊆ φ '' Icc a b := intermediate_value_Icc hab hcont
      rwa [hφa, hφb] at hsub
  have himg_S_ae : φ '' S =ᵐ[volume] Icc α β := by
    rw [← himg_Icc, ae_eq_set]
    refine ⟨?_, ?_⟩
    · exact measure_mono_null (sdiff_eq_empty.mpr (image_mono hS_sub_Icc) ▸ Subset.rfl) measure_empty
    · have hdiff_sub : φ '' Icc a b \ φ '' S ⊆ φ '' (Icc a b \ S) := by
        rintro _ ⟨⟨x, hxIcc, rfl⟩, hnot⟩
        exact ⟨x, ⟨hxIcc, fun hxS => hnot ⟨x, hxS, rfl⟩⟩, rfl⟩
      refine measure_mono_null hdiff_sub ?_
      exact hlusin (Icc a b \ S) sdiff_subset hIcc_diff_S_null
  have hlint :
      (∫⁻ t in Icc α β, f t ∂volume) =
        (∫⁻ x in Icc a b, f (φ x) * ENNReal.ofReal (deriv φ x) ∂volume) := by
    calc
      (∫⁻ t in Icc α β, f t ∂volume)
        = ∫⁻ t in φ '' S, f t ∂volume := (setLIntegral_congr himg_S_ae).symm
      _ = ∫⁻ x in S, ENNReal.ofReal (deriv φ x) * f (φ x) ∂volume :=
          MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hS_meas
            hderiv_S (hmono.mono hS_sub_Icc) f
      _ = ∫⁻ x in S, f (φ x) * ENNReal.ofReal (deriv φ x) ∂volume :=
          setLIntegral_congr_fun hS_meas fun _ _ => mul_comm _ _
      _ = ∫⁻ x in Icc a b, f (φ x) * ENNReal.ofReal (deriv φ x) ∂volume :=
          setLIntegral_congr hS_ae_Icc
  let f₀ : ℝ → ℝ≥0∞ := hf.aemeasurable.mk f
  have hf₀_meas : Measurable f₀ := hf.aemeasurable.measurable_mk
  let M : Set ℝ := toMeasurable volume {t | f t ≠ f₀ t}
  have hM_meas : MeasurableSet M := measurableSet_toMeasurable volume _
  have hM_null : volume M = 0 := by
    rw [measure_toMeasurable]
    exact hf.aemeasurable.ae_eq_mk
  classical
  let φ₀ : ℝ → ℝ := S.piecewise φ 0
  have hφ₀_meas : Measurable φ₀ :=
    (hcont.mono hS_sub_Icc).measurable_piecewise continuous_zero.continuousOn hS_meas
  let S₁ : Set ℝ := S ∩ φ₀ ⁻¹' M
  have hS₁_meas : MeasurableSet S₁ := hS_meas.inter (hM_meas.preimage hφ₀_meas)
  have hφS₁_null : volume (φ '' S₁) = 0 := by
    refine measure_mono_null ?_ hM_null
    rintro _ ⟨x, ⟨hxS, hxM⟩, rfl⟩
    have hφ₀_eq : φ₀ x = φ x := Set.piecewise_eq_of_mem _ _ _ hxS
    change φ₀ x ∈ M at hxM
    rwa [hφ₀_eq] at hxM
  have hlint_S₁ : (∫⁻ x in S₁, ENNReal.ofReal (deriv φ x) ∂volume) = 0 := by
    rw [MeasureTheory.lintegral_deriv_eq_volume_image_of_monotoneOn hS₁_meas
      (fun x hx => (hderiv_S x hx.1).mono inter_subset_left)
      (hmono.mono (inter_subset_left.trans hS_sub_Icc)), hφS₁_null]
  have hd_meas : Measurable (fun x => ENNReal.ofReal (deriv φ x)) :=
    ENNReal.measurable_ofReal.comp (measurable_deriv φ)
  have hae_S₁_zero : ∀ᵐ x ∂(volume.restrict S₁), ENNReal.ofReal (deriv φ x) = 0 :=
    (lintegral_eq_zero_iff hd_meas).mp hlint_S₁
  have hae_S_S₁ : ∀ᵐ x ∂(volume.restrict S), x ∈ S₁ → ENNReal.ofReal (deriv φ x) = 0 := by
    have hrestr : volume.restrict S₁ = (volume.restrict S).restrict S₁ := by
      rw [Measure.restrict_restrict hS₁_meas, inter_eq_left.mpr inter_subset_left]
    rw [← ae_restrict_iff' hS₁_meas, ← hrestr]
    exact hae_S₁_zero
  have hae_eq_S :
      (fun x => f (φ x) * ENNReal.ofReal (deriv φ x)) =ᵐ[volume.restrict S]
        (fun x => f₀ (φ₀ x) * ENNReal.ofReal (deriv φ x)) := by
    filter_upwards [ae_restrict_mem hS_meas, hae_S_S₁] with x hxS hxS₁
    by_cases hxM : x ∈ S₁
    · rw [hxS₁ hxM, mul_zero, mul_zero]
    · have hφ₀_eq : φ₀ x = φ x := Set.piecewise_eq_of_mem _ _ _ hxS
      have hnotM : φ x ∉ M := by
        intro hmem
        exact hxM ⟨hxS, by simpa [hφ₀_eq] using hmem⟩
      have hnot_ne : ¬ f (φ x) ≠ f₀ (φ x) :=
        fun hne => hnotM (subset_toMeasurable volume _ hne)
      push Not at hnot_ne
      rw [hnot_ne, hφ₀_eq]
  have haemeas_S :
      AEMeasurable (fun x => f (φ x) * ENNReal.ofReal (deriv φ x)) (volume.restrict S) :=
    ((hf₀_meas.comp hφ₀_meas).mul hd_meas).aemeasurable.congr hae_eq_S.symm
  have hrestr_SIcc : volume.restrict S = volume.restrict (Icc a b) :=
    Measure.restrict_congr_set hS_ae_Icc
  exact ⟨(hrestr_SIcc ▸ haemeas_S).nullMeasurable, hlint⟩

/-- **Theorem 7.26 (one-variable AC nondecreasing `L¹` / interval-integral form)** (Rudin,
pp. 155–156): under the same hypotheses on `φ : [a, b] → [α, β]`, a Banach-valued `g` is
integrable on `[α, β]` iff `x ↦ φ'(x) • g(φ(x))` is integrable on `[a, b]`, and
`∫_α^β g(t) dt = ∫_a^b φ'(x) • g(φ(x)) dx`. -/
theorem theorem_7_26_oneDim_ac_monotone_intervalIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ → ℝ} {a b α β : ℝ}
    (hab : a ≤ b) (hmono : MonotoneOn φ (Icc a b))
    (hac : BookAbsolutelyContinuousOnReal φ a b)
    (hφa : φ a = α) (hφb : φ b = β)
    (g : ℝ → E) :
    (IntegrableOn g (Icc α β) volume ↔
        IntegrableOn (fun x => deriv φ x • g (φ x)) (Icc a b) volume) ∧
      (∫ t in α..β, g t) = (∫ x in a..b, deriv φ x • g (φ x)) := by
  have hcont : ContinuousOn φ (Icc a b) := hac.continuousOn hab
  have hαβ_le : α ≤ β := by
    rw [← hφa, ← hφb]
    exact hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  rcases hab.eq_or_lt with rfl | hab_lt
  · have hαβ : α = β := hφa.symm.trans hφb
    subst hαβ
    have ha_ae : (Icc a a : Set ℝ) =ᵐ[volume] (∅ : Set ℝ) :=
      ae_eq_empty.mpr (by rw [Icc_self]; exact measure_singleton a)
    have hα_ae : (Icc α α : Set ℝ) =ᵐ[volume] (∅ : Set ℝ) :=
      ae_eq_empty.mpr (by rw [Icc_self]; exact measure_singleton α)
    refine ⟨?_, by simp⟩
    rw [integrableOn_congr_set_ae hα_ae, integrableOn_congr_set_ae ha_ae]
    simp
  have h18 := theorem_7_18 hab hcont hmono
  have hlusin : ∀ s : Set ℝ, s ⊆ Icc a b → volume s = 0 → volume (φ '' s) = 0 :=
    h18.1.mp hac
  have hae_diff : ∀ᵐ x ∂(volume.restrict (Icc a b)), DifferentiableAt ℝ φ x :=
    (h18.2.1.mp hlusin).1
  let Z₀ : Set ℝ := {x ∈ Ioo a b | ¬ DifferentiableAt ℝ φ x}
  have hZ₀_null : volume Z₀ = 0 := by
    have hae_unres := (ae_restrict_iff' measurableSet_Icc).mp hae_diff
    rw [ae_iff] at hae_unres
    refine measure_mono_null (fun x hx => ?_) hae_unres
    intro himp
    exact hx.2 (himp (Ioo_subset_Icc_self hx.1))
  let Z : Set ℝ := toMeasurable volume Z₀ ∩ Ioo a b
  have hZ_meas : MeasurableSet Z := (measurableSet_toMeasurable volume Z₀).inter measurableSet_Ioo
  have hZ_null : volume Z = 0 :=
    measure_mono_null inter_subset_left (by rw [measure_toMeasurable]; exact hZ₀_null)
  let S : Set ℝ := Ioo a b \ Z
  have hS_meas : MeasurableSet S := measurableSet_Ioo.diff hZ_meas
  have hS_sub_Icc : S ⊆ Icc a b := sdiff_subset.trans Ioo_subset_Icc_self
  have hIcc_diff_S_null : volume (Icc a b \ S) = 0 := by
    have hsub : Icc a b \ S ⊆ ({a, b} : Set ℝ) ∪ Z := by
      intro x ⟨hxIcc, hxnotS⟩
      rcases hxIcc.1.eq_or_lt with hax_eq | hax
      · rw [← hax_eq]
        exact Or.inl (mem_insert a {b})
      · rcases hxIcc.2.eq_or_lt with hxb_eq | hxb
        · rw [hxb_eq]
          exact Or.inl (mem_insert_of_mem a (mem_singleton b))
        · refine Or.inr ?_
          by_contra hxnotZ
          exact hxnotS ⟨⟨hax, hxb⟩, hxnotZ⟩
    have hends_null : volume ({a, b} : Set ℝ) = 0 :=
      (Set.toFinite ({a, b} : Set ℝ)).measure_zero volume
    exact le_antisymm
      ((measure_mono hsub).trans ((measure_union_le _ _).trans (by rw [hends_null, hZ_null, add_zero])))
      zero_le
  have hS_ae_Icc : S =ᵐ[volume] Icc a b := by
    rw [ae_eq_set]
    exact ⟨measure_mono_null (sdiff_eq_empty.mpr hS_sub_Icc ▸ Subset.rfl) measure_empty,
      hIcc_diff_S_null⟩
  have hderiv_S : ∀ x ∈ S, HasDerivWithinAt φ (deriv φ x) S x := by
    intro x ⟨hxIoo, hxnotZ⟩
    have hd : DifferentiableAt ℝ φ x := by
      by_contra hnd
      exact hxnotZ ⟨subset_toMeasurable volume Z₀ ⟨hxIoo, hnd⟩, hxIoo⟩
    exact hd.hasDerivAt.hasDerivWithinAt
  have himg_Icc : φ '' Icc a b = Icc α β := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨hφa ▸ hmono (left_mem_Icc.mpr hab) hx hx.1,
        hφb ▸ hmono hx (right_mem_Icc.mpr hab) hx.2⟩
    · have hsub : Icc (φ a) (φ b) ⊆ φ '' Icc a b := intermediate_value_Icc hab hcont
      rwa [hφa, hφb] at hsub
  have himg_S_ae : φ '' S =ᵐ[volume] Icc α β := by
    rw [← himg_Icc, ae_eq_set]
    refine ⟨?_, ?_⟩
    · exact measure_mono_null (sdiff_eq_empty.mpr (image_mono hS_sub_Icc) ▸ Subset.rfl) measure_empty
    · have hdiff_sub : φ '' Icc a b \ φ '' S ⊆ φ '' (Icc a b \ S) := by
        rintro _ ⟨⟨x, hxIcc, rfl⟩, hnot⟩
        exact ⟨x, ⟨hxIcc, fun hxS => hnot ⟨x, hxS, rfl⟩⟩, rfl⟩
      refine measure_mono_null hdiff_sub ?_
      exact hlusin (Icc a b \ S) sdiff_subset hIcc_diff_S_null
  have hint_iff :
      IntegrableOn g (Icc α β) volume ↔
        IntegrableOn (fun x => deriv φ x • g (φ x)) (Icc a b) volume := by
    rw [← integrableOn_congr_set_ae himg_S_ae,
      MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn hS_meas
        hderiv_S (hmono.mono hS_sub_Icc) g,
      integrableOn_congr_set_ae hS_ae_Icc]
  have hint_eq : (∫ t in α..β, g t) = (∫ x in a..b, deriv φ x • g (φ x)) := by
    rw [intervalIntegral.integral_of_le hαβ_le, intervalIntegral.integral_of_le hab,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← setIntegral_congr_set himg_S_ae,
      MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn hS_meas
        hderiv_S (hmono.mono hS_sub_Icc) g,
      setIntegral_congr_set hS_ae_Icc]
  exact ⟨hint_iff, hint_eq⟩

end Node7_26

end RudinRCA.Chapter07
