import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.UrysohnsLemma

/-
The approximation proofs below adapt Mathlib.MeasureTheory.Function.ContinuousMapDense.
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under the Apache 2.0 license; see Mathlib's LICENSE.
Original author: Heather Macbeth.
Modification: use compact inner approximation and the compact/closed Urysohn lemma
to prove the density statements on arbitrary locally compact Hausdorff spaces.
-/

noncomputable section
open MeasureTheory TopologicalSpace ContinuousMap Set Bornology
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace RudinRCA.Chapter06
variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [MeasurableSpace α] [BorelSpace α]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {p : ℝ≥0∞}

/- Adapted from pinned Mathlib ContinuousMapDense.lean. Compact inner approximation
allows the compact/closed Urysohn lemma, avoiding any NormalSpace hypothesis. -/
theorem lch_exists_continuous_eLpNorm_sub_le_of_compact [μ.OuterRegular] (hp : p ≠ ∞) {s u : Set α}
    (s_compact : IsCompact s) (u_open : IsOpen u) (hsu : s ⊆ u) (hs : μ s ≠ ∞) (c : E) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) :
    ∃ f : α → E,
      Continuous f ∧
        eLpNorm (fun x => f x - s.indicator (fun _y => c) x) p μ ≤ ε ∧
          (∀ x, ‖f x‖ ≤ ‖c‖) ∧ Function.support f ⊆ u ∧ MemLp f p μ := by
  have s_closed := s_compact.isClosed
  obtain ⟨η, η_pos, hη⟩ :
      ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set α, μ s ≤ η → NullMeasurableSet s μ →
          eLpNorm (s.indicator fun _x => c) p μ ≤ ε :=
    exists_eLpNorm_indicator_le hp c hε
  have ηpos : (0 : ℝ≥0∞) < η := ENNReal.coe_lt_coe.2 η_pos
  obtain ⟨V, sV, V_open, h'V, hV⟩ : ∃ (V : Set α), V ⊇ s ∧ IsOpen V ∧ μ V < ∞ ∧ μ (V \ s) < η :=
    s_closed.measurableSet.exists_isOpen_sdiff_lt hs ηpos.ne'
  let v := u ∩ V
  have hsv : s ⊆ v := subset_inter hsu sV
  have hμv : μ v < ∞ := (measure_mono inter_subset_right).trans_lt h'V
  obtain ⟨g, hgv, hgs, hg_range⟩ :=
    exists_continuous_zero_one_of_isCompact' s_compact (u_open.inter V_open).isClosed_compl
      (disjoint_compl_left_iff.2 hsv).symm
  -- Multiply this by `c` to get a continuous approximation to the function `f`; the key point is
  -- that this is pointwise bounded by the indicator of the set `v \ s`, which has small measure.
  have g_norm : ∀ x, ‖g x‖ = g x := fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hg_range x).1]
  have gc_bd0 : ∀ x, ‖g x • c‖ ≤ ‖c‖ := by
    intro x
    simp only [norm_smul, g_norm x]
    apply mul_le_of_le_one_left (norm_nonneg _)
    exact (hg_range x).2
  have gc_bd :
      ∀ x, ‖g x • c - s.indicator (fun _x => c) x‖ ≤ ‖(v \ s).indicator (fun _x => c) x‖ := by
    intro x
    by_cases hv : x ∈ v
    · rw [← Set.sdiff_union_of_subset hsv] at hv
      rcases hv with hsv | hs
      · simpa only [hsv.2, Set.indicator_of_notMem, not_false_iff, sub_zero, hsv,
          Set.indicator_of_mem] using gc_bd0 x
      · simp [hgs hs, hs]
    · simp [hgv hv, show x ∉ s from fun h => hv (hsv h)]
  have gc_support : (Function.support fun x : α => g x • c) ⊆ v := by
    refine Function.support_subset_iff'.2 fun x hx => ?_
    simp only [hgv hx, Pi.zero_apply, zero_smul]
  have gc_mem : MemLp (fun x => g x • c) p μ := by
    refine MemLp.smul ?_ (memLp_top_const _) (p := p) (q := ∞)
    have hv : MeasurableSet v := u_open.measurableSet.inter V_open.measurableSet
    have : eLpNorm (v.indicator fun _x => (1 : ℝ)) p μ < ∞ :=
      (eLpNorm_indicator_const_le _ _ hv.nullMeasurableSet).trans_lt <| by
        simp [lt_top_iff_ne_top, hμv.ne]
    refine (eLpNorm_mono g.continuous.aestronglyMeasurable fun x => ?_).trans_lt this
    by_cases hx : x ∈ v
    · simp only [hx, abs_of_nonneg (hg_range x).1, (hg_range x).2, Real.norm_eq_abs,
        indicator_of_mem, CStarRing.norm_one]
    · simp only [hgv hx, Pi.zero_apply, Real.norm_eq_abs, abs_zero, abs_nonneg]
  refine ⟨fun x ↦ g x • c, by fun_prop,
    (eLpNorm_mono (gc_mem.aestronglyMeasurable.sub
      (aestronglyMeasurable_const.indicator s_closed.measurableSet)) gc_bd).trans ?_, gc_bd0,
      gc_support.trans inter_subset_left, gc_mem⟩
  exact hη _ ((measure_mono (sdiff_subset_sdiff inter_subset_right Subset.rfl)).trans hV.le)
    ((u_open.measurableSet.inter V_open.measurableSet).diff
      s_closed.measurableSet).nullMeasurableSet

theorem lch_memLp_exists_hasCompactSupport_eLpNorm_sub_le
    [μ.Regular]
    (hp : p ≠ ∞) {f : α → E} (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : α → E, HasCompactSupport g ∧ eLpNorm (f - g) p μ ≤ ε ∧ Continuous g ∧ MemLp g p μ := by
  suffices H :
      ∃ g : α → E, eLpNorm (f - g) p μ ≤ ε ∧ Continuous g ∧ MemLp g p μ ∧ HasCompactSupport g by
    rcases H with ⟨g, hg, g_cont, g_mem, g_support⟩
    exact ⟨g, g_support, hg, g_cont, g_mem⟩
  -- It suffices to check that the set of functions we consider approximates characteristic
  -- functions, is stable under addition and consists of ae strongly measurable functions.
  -- First check the latter easy facts.
  apply hf.induction_dense hp _ _ _ hε
  rotate_left
  -- stability under addition
  · rintro f g ⟨f_cont, f_mem, hf⟩ ⟨g_cont, g_mem, hg⟩
    exact ⟨f_cont.add g_cont, f_mem.add g_mem, hf.add hg⟩
  -- We are left with approximating characteristic functions.
  -- This follows from `exists_continuous_eLpNorm_sub_le_of_closed`.
  intro c t ht htμ ε hε
  rcases exists_Lp_half E μ p hε with ⟨δ, δpos, hδ⟩
  obtain ⟨η, ηpos, hη⟩ :
      ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set α, μ s ≤ η → NullMeasurableSet s μ →
          eLpNorm (s.indicator fun _x => c) p μ ≤ δ :=
    exists_eLpNorm_indicator_le hp c δpos.ne'
  have hη_pos' : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.2 ηpos
  obtain ⟨s, st, s_compact, s_closed, μs⟩ :
      ∃ s, s ⊆ t ∧ IsCompact s ∧ IsClosed s ∧ μ (t \ s) < η :=
    ht.exists_isCompact_isClosed_sdiff_lt htμ.ne hη_pos'.ne'
  have hsμ : μ s < ∞ := (measure_mono st).trans_lt htμ
  have I1 : eLpNorm ((s.indicator fun _y => c) - t.indicator fun _y => c) p μ ≤ δ := by
    rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff st]
    exact hη _ μs.le (ht.diff s_closed.measurableSet).nullMeasurableSet
  obtain ⟨k, k_compact, sk⟩ : ∃ k : Set α, IsCompact k ∧ s ⊆ interior k :=
    exists_compact_superset s_compact
  rcases lch_exists_continuous_eLpNorm_sub_le_of_compact hp s_compact isOpen_interior sk hsμ.ne c δpos.ne'
    with ⟨f, f_cont, I2, _f_bound, f_support, f_mem⟩
  have I3 : eLpNorm (f - t.indicator fun _y => c) p μ ≤ ε := by
    convert! (hδ _ _ I2 I1).le using 2
    ext x
    simp
  refine ⟨f, I3, f_cont, f_mem, HasCompactSupport.intro k_compact fun x hx => ?_⟩
  rw [← Function.notMem_support]
  contrapose hx
  exact interior_subset (f_support hx)



/-- L1 density of compactly supported continuous functions on every locally
compact Hausdorff space with a regular measure, without normality. -/
theorem lch_integrable_exists_hasCompactSupport_integral_sub_le [μ.Regular]
    {f : α → E} (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : α → E, HasCompactSupport g ∧ (∫ x, ‖f x - g x‖ ∂μ) ≤ ε ∧
      Continuous g ∧ Integrable g μ := by
  obtain ⟨g, hg_support, hg, hg_cont, hg_mem⟩ :=
    lch_memLp_exists_hasCompactSupport_eLpNorm_sub_le ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr hf) (ENNReal.ofReal_ne_zero_iff.mpr hε)
  have hgi : Integrable g μ := memLp_one_iff_integrable.mp hg_mem
  refine ⟨g, hg_support, ?_, hg_cont, hgi⟩
  have hfg := (hf.sub hgi).aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm hfg] at hg
  change (∫ x, ‖(f - g) x‖ ∂μ) ≤ ε
  rw [integral_norm_eq_lintegral_enorm hfg]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg
  simpa only [ENNReal.toReal_ofReal hε.le, Pi.sub_apply] using hh

#print axioms lch_exists_continuous_eLpNorm_sub_le_of_compact
#print axioms lch_memLp_exists_hasCompactSupport_eLpNorm_sub_le
#print axioms lch_integrable_exists_hasCompactSupport_integral_sub_le
end RudinRCA.Chapter06
