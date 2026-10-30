import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Relations

/-!
Auxiliary construction for Rudin 6.16, for a finite positive measure.
This file proves only the construction of the absolutely continuous complex
measure E ↦ Φ(χ_E); it does not assert the Lp dual representation theorem.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology symmDiff Function Classical

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The indicator of a measurable set in `Lp`, extended by zero on
nonmeasurable sets to conform to the vector-measure convention. -/
def finiteLpIndicator (E : Set X) : Lp ℂ p μ :=
  if hE : MeasurableSet E then
    indicatorConstLp p hE (measure_ne_top μ E) 1
  else 0

theorem finiteLpIndicator_measurable {E : Set X} (hE : MeasurableSet E) :
    finiteLpIndicator μ p E = indicatorConstLp p hE (measure_ne_top μ E) 1 := by
  simp only [finiteLpIndicator, dite_eq_left hE]

@[simp] theorem finiteLpIndicator_empty : finiteLpIndicator μ p ∅ = 0 := by
  rw [finiteLpIndicator_measurable μ p MeasurableSet.empty]
  exact indicatorConstLp_empty

theorem finiteLpIndicator_disjoint_union {E F : Set X}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hEF : Disjoint E F) :
    finiteLpIndicator μ p (E ∪ F) =
      finiteLpIndicator μ p E + finiteLpIndicator μ p F := by
  rw [finiteLpIndicator_measurable μ p (hE.union hF),
    finiteLpIndicator_measurable μ p hE, finiteLpIndicator_measurable μ p hF]
  exact indicatorConstLp_disjoint_union hE hF (measure_ne_top μ E)
    (measure_ne_top μ F) hEF 1

theorem finiteLpIndicator_finset_iUnion {E : ℕ → Set X}
    (hE : ∀ i, MeasurableSet (E i)) (hdisj : Pairwise (Disjoint on E)) (F : Finset ℕ) :
    finiteLpIndicator μ p (⋃ i ∈ F, E i) = ∑ i ∈ F, finiteLpIndicator μ p (E i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
      have hU : MeasurableSet (⋃ j ∈ F, E j) :=
        MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hE j
      have hd : Disjoint (E i) (⋃ j ∈ F, E j) := by
        apply disjoint_iUnion_right.mpr
        intro j
        apply disjoint_iUnion_right.mpr
        intro hj
        exact hdisj (by intro hij; subst j; exact hi hj)
      have hset : (⋃ j ∈ insert i F, E j) = E i ∪ ⋃ j ∈ F, E j := by
        ext x
        simp only [mem_iUnion, Finset.mem_insert, mem_union]
        constructor
        · rintro ⟨j, hj, hxj⟩
          rcases hj with rfl | hj
          · exact Or.inl hxj
          · exact Or.inr ⟨j, hj, hxj⟩
        · rintro (hxi | ⟨j, hj, hxj⟩)
          · exact ⟨i, Or.inl rfl, hxi⟩
          · exact ⟨j, Or.inr hj, hxj⟩
      rw [hset, finiteLpIndicator_disjoint_union μ p (hE i) hU hd, ih,
        Finset.sum_insert hi]

/-- Countable additivity of `Lp` indicators when `p < ∞`.
The proof uses convergence over all finite subsets, so the conclusion is
unconditional summability, as required by `VectorMeasure`. -/
theorem finiteLpIndicator_hasSum (hp : p ≠ ∞) {E : ℕ → Set X}
    (hE : ∀ i, MeasurableSet (E i)) (hdisj : Pairwise (Disjoint on E)) :
    HasSum (fun i => finiteLpIndicator μ p (E i))
      (finiteLpIndicator μ p (⋃ i, E i)) := by
  classical
  let U : Finset ℕ → Set X := fun F => ⋃ i ∈ F, E i
  let A : Set X := ⋃ i, E i
  have hA : MeasurableSet A := MeasurableSet.iUnion hE
  have hU : ∀ F, MeasurableSet (U F) := fun F =>
    MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hE i
  have hsub : ∀ F, U F ⊆ A := fun F =>
    iUnion₂_subset fun i _ => subset_iUnion E i
  have hmono : Monotone U := by
    intro F G hFG
    exact biUnion_subset_biUnion_left hFG
  have hanti : Antitone (fun F => A \ U F) := by
    intro F G hFG x hx
    exact ⟨hx.1, fun hxF => hx.2 (hmono hFG hxF)⟩
  have hinter : (⋂ F : Finset ℕ, A \ U F) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxA := (mem_iInter.mp hx ∅).1
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxA
    exact (mem_iInter.mp hx {i}).2 (by simpa [U] using hxi)
  have hlim : Tendsto (fun F : Finset ℕ => μ (A \ U F)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop
      (μ := μ) (fun F => (hA.diff (hU F)).nullMeasurableSet) hanti
      ⟨∅, measure_ne_top μ _⟩
    simpa only [hinter, measure_empty, Function.comp_def] using h
  have hsymm : Tendsto (fun F : Finset ℕ => μ (U F ∆ A)) atTop (𝓝 0) := by
    simpa only [symmDiff_of_le (hsub _)] using hlim
  have hind := tendsto_indicatorConstLp_set
    (p := p) (μ := μ) (c := (1 : ℂ)) (hs := hA)
    (hμs := measure_ne_top μ A) (ht := hU)
    (hμt := fun F => measure_ne_top μ (U F)) hp hsymm
  change Tendsto (fun F : Finset ℕ => ∑ i ∈ F, finiteLpIndicator μ p (E i))
    atTop (𝓝 (finiteLpIndicator μ p A))
  have hsum : (fun F : Finset ℕ => ∑ i ∈ F, finiteLpIndicator μ p (E i)) =
      fun F => indicatorConstLp p (hU F) (measure_ne_top μ (U F)) (1 : ℂ) := by
    funext F
    rw [← finiteLpIndicator_finset_iUnion μ p hE hdisj F]
    exact finiteLpIndicator_measurable μ p (hU F)
  rw [hsum, finiteLpIndicator_measurable μ p hA]
  exact hind

/-- The vector measure taking a measurable set to its `Lp` indicator. -/
def finiteLpIndicatorVectorMeasure (hp : p ≠ ∞) : VectorMeasure X (Lp ℂ p μ) where
  measureOf' := finiteLpIndicator μ p
  empty' := finiteLpIndicator_empty μ p
  not_measurable' E hE := by simp only [finiteLpIndicator, dite_eq_right hE]
  m_iUnion' E hE hd := finiteLpIndicator_hasSum μ p hp hE hd

/-- The auxiliary complex measure in the finite-measure proof of Rudin 6.16. -/
def finiteLpFunctionalMeasure (hp : p ≠ ∞) (Φ : Lp ℂ p μ →L[ℂ] ℂ) : ComplexMeasure X :=
  VectorMeasure.mapRangeL Φ (finiteLpIndicatorVectorMeasure μ p hp)

theorem finiteLpFunctionalMeasure_apply (hp : p ≠ ∞) (Φ : Lp ℂ p μ →L[ℂ] ℂ)
    {E : Set X} (hE : MeasurableSet E) :
    finiteLpFunctionalMeasure μ p hp Φ E =
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) := by
  change Φ (finiteLpIndicator μ p E) = _
  rw [finiteLpIndicator_measurable μ p hE]

theorem finiteLpFunctionalMeasure_norm_le (hp : p ≠ ∞) (Φ : Lp ℂ p μ →L[ℂ] ℂ)
    {E : Set X} (hE : MeasurableSet E) :
    ‖finiteLpFunctionalMeasure μ p hp Φ E‖ ≤ ‖Φ‖ * μ.real E ^ (1 / p.toReal) := by
  rw [finiteLpFunctionalMeasure_apply μ p hp Φ hE]
  have hp0 : p ≠ 0 := (one_pos.trans_le (Fact.out : 1 ≤ p)).ne'
  calc
    ‖Φ (indicatorConstLp p hE (measure_ne_top μ E) 1)‖ ≤
        ‖Φ‖ * ‖indicatorConstLp p hE (measure_ne_top μ E) (1 : ℂ)‖ := Φ.le_opNorm _
    _ = ‖Φ‖ * μ.real E ^ (1 / p.toReal) := by rw [norm_indicatorConstLp hp0 hp]; simp

theorem finiteLpIndicator_eq_zero_of_measure_zero {E : Set X}
    (hE : MeasurableSet E) (hμE : μ E = 0) : finiteLpIndicator μ p E = 0 := by
  rw [finiteLpIndicator_measurable μ p hE]
  have heq := (indicatorConstLp_inj (p := p) hE (measure_ne_top μ E)
    MeasurableSet.empty (by simp : μ ∅ ≠ ∞) (one_ne_zero : (1 : ℂ) ≠ 0)).mpr
    (ae_eq_empty.mpr hμE)
  exact heq.trans indicatorConstLp_empty

theorem finiteLpFunctionalMeasure_absolutelyContinuous (hp : p ≠ ∞)
    (Φ : Lp ℂ p μ →L[ℂ] ℂ) :
    finiteLpFunctionalMeasure μ p hp Φ ≪ᵥ μ.toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro E hE hμE
  rw [Measure.toENNRealVectorMeasure_apply_measurable hE] at hμE
  change Φ (finiteLpIndicator μ p E) = 0
  rw [finiteLpIndicator_eq_zero_of_measure_zero μ p hE hμE, map_zero]

#print axioms finiteLpIndicator_hasSum
#print axioms finiteLpFunctionalMeasure_norm_le
#print axioms finiteLpFunctionalMeasure_absolutelyContinuous

end RudinRCA.Chapter06
