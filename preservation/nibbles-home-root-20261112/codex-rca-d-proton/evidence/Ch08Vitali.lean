module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RudinRCA.Chapter08

/-- Rational translation equivalence used to construct a Lebesgue nonmeasurable set. -/
def rationalTranslationSetoid : Setoid ℝ where
  r x y := ∃ q : ℚ, x - y = (q : ℝ)
  iseqv := ⟨fun x => ⟨0, by simp⟩,
    by
      rintro x y ⟨q, hq⟩
      exact ⟨-q, by push_cast; linarith⟩,
    by
      rintro x y z ⟨q, hq⟩ ⟨r, hr⟩
      exact ⟨q + r, by push_cast; linarith⟩⟩

/-- Choose one representative of each rational translation class. -/
def vitaliRepresentatives : Set ℝ :=
  range (Quotient.out : Quotient rationalTranslationSetoid → ℝ)

lemma vitali_representatives_unique {x y : ℝ} (hx : x ∈ vitaliRepresentatives)
    (hy : y ∈ vitaliRepresentatives) {q : ℚ} (hxy : x - y = (q : ℝ)) : x = y := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have h : a = b := by
    simpa only [Quotient.out_eq] using (Quotient.sound (s := rationalTranslationSetoid) ⟨q, hxy⟩)
  rw [h]

lemma rational_translate_disjoint {W : Set ℝ} (hW : W ⊆ vitaliRepresentatives) :
    Pairwise (fun q r : ℚ => Disjoint {x : ℝ | x - (q : ℝ) ∈ W}
      {x : ℝ | x - (r : ℝ) ∈ W}) := by
  intro q r hqr
  apply Set.disjoint_left.mpr
  intro x hx hy
  have he : x - (q : ℝ) = x - (r : ℝ) :=
    vitali_representatives_unique (hW hx) (hW hy)
      (q := r - q) (by push_cast; ring)
  have hc : (q : ℝ) = (r : ℝ) := by linarith
  exact hqr (Rat.cast_injective hc)

lemma volume_rational_translate (W : Set ℝ) (q : ℚ) :
    volume {x : ℝ | x - (q : ℝ) ∈ W} = volume W := by
  change volume ((fun x : ℝ => x - (q : ℝ)) ⁻¹' W) = volume W
  simpa only [sub_eq_add_neg] using measure_preimage_add_right volume (-(q : ℝ)) W

/-- Every bounded Lebesgue-measurable subset of a rational transversal is null. -/
lemma bounded_vitali_subset_null {W : Set ℝ} (hW : W ⊆ vitaliRepresentatives)
    (hm : NullMeasurableSet W volume) {n : ℝ} (hb : W ⊆ Icc (-n) n) : volume W = 0 := by
  classical
  let T := {q : ℚ // q ∈ Icc (0 : ℚ) 1}
  haveI : Infinite T := (Set.Icc_infinite (by norm_num : (0 : ℚ) < 1)).to_subtype
  let F : T → Set ℝ := fun q => {x | x - (q.1 : ℝ) ∈ W}
  have hFd : Pairwise (fun q r : T => Disjoint (F q) (F r)) := by
    intro q r hqr
    exact rational_translate_disjoint hW (fun h => hqr (Subtype.ext h))
  have hFm (q : T) : NullMeasurableSet (F q) volume := by
    exact hm.preimage (measurePreserving_sub_right volume (q.1 : ℝ)).quasiMeasurePreserving
  have hbound : (⋃ q, F q) ⊆ Icc (-n) (n + 1) := by
    intro x hx
    obtain ⟨q, hq⟩ := mem_iUnion.mp hx
    have hw := hb hq
    have hq0 : (0 : ℝ) ≤ (q.1 : ℝ) := by exact_mod_cast q.2.1
    have hq1 : (q.1 : ℝ) ≤ (1 : ℝ) := by exact_mod_cast q.2.2
    constructor <;> linarith [hw.1, hw.2]
  by_contra hn
  have hi : volume (⋃ q, F q) = ∞ := by
    rw [measure_iUnion₀ (fun i j hij => (hFd hij).aedisjoint) hFm]
    simp only [F, volume_rational_translate]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hn
  have hle : volume (⋃ q, F q) ≤ volume (Icc (-n) (n + 1)) := measure_mono hbound
  rw [hi] at hle
  have hfinite : volume (Icc (-n) (n + 1)) < ∞ := isCompact_Icc.measure_lt_top
  exact hfinite.ne (top_unique hle)

/-- Existence of a non-Lebesgue-measurable set, used by the concrete example in 8.10. -/
theorem exists_not_lebesgue_measurable : ∃ B : Set ℝ, ¬ NullMeasurableSet B volume := by
  refine ⟨vitaliRepresentatives, ?_⟩
  intro hm
  have hw (n : ℕ) : volume (vitaliRepresentatives ∩ Icc (-(n : ℝ)) n) = 0 :=
    bounded_vitali_subset_null inter_subset_left (hm.inter measurableSet_Icc.nullMeasurableSet)
      inter_subset_right
  have hv : volume vitaliRepresentatives = 0 := by
    apply measure_mono_null (t := ⋃ n : ℕ, vitaliRepresentatives ∩ Icc (-(n : ℝ)) n) ?_
      (measure_iUnion_null hw)
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    apply mem_iUnion.mpr
    refine ⟨n, hx, ?_, ?_⟩
    · have hh := neg_abs_le x
      linarith
    · exact (le_abs_self x).trans hn
  have hcover : (⋃ q : ℚ, {x : ℝ | x - (q : ℝ) ∈ vitaliRepresentatives}) = univ := by
    apply eq_univ_of_forall
    intro x
    let a : Quotient rationalTranslationSetoid := Quotient.mk _ x
    have hr : rationalTranslationSetoid x a.out := Quotient.exact (Quotient.out_eq a).symm
    obtain ⟨q, hq⟩ := hr
    apply mem_iUnion.mpr
    refine ⟨q, ?_⟩
    have he : x - (q : ℝ) = a.out := by linarith
    change x - (q : ℝ) ∈ vitaliRepresentatives
    rw [he]
    exact ⟨a, rfl⟩
  have hnull := measure_iUnion_null (fun q : ℚ => (volume_rational_translate vitaliRepresentatives q).trans hv)
  rw [hcover] at hnull
  simpa using hnull

/-- 8.10's concrete Lebesgue example: even the product of two complete one-dimensional
Lebesgue measures is not complete. This uses the actual Vitali construction above. -/
theorem completed_lebesgue_product_not_complete :
    ¬ ((volume : Measure ℝ).completion.prod (volume : Measure ℝ).completion).IsComplete := by
  letI : SigmaFinite (volume : Measure ℝ).completion := sigmaFinite_completion volume
  obtain ⟨B, hB⟩ := exists_not_lebesgue_measurable
  let z : NullMeasurableSpace ℝ (volume : Measure ℝ) := (0 : ℝ)
  apply product_not_complete (volume : Measure ℝ).completion (volume : Measure ℝ).completion
    (A := {z}) (B := B) (singleton_nonempty z)
  · change (volume : Measure ℝ) ({0} : Set ℝ) = 0
    simp
  · exact hB

end RudinRCA.Chapter08
