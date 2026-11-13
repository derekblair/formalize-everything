import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Scratch dependencies, supplied earlier in the aggregate:
BalancedCycles, PolygonalConcat, CyclicVertices, SegmentIntegralBridge.
The geometry is chosen before, and independently of, the integrand.
-/

open Set Function
open scoped BigOperators

namespace RudinRCA.Chapter13Scratch

universe u

/-- Finite polygonal paths, with the actual parametrization obtained by concatenating segments.
Endpoint casts change only the types of endpoints, not the underlying path. -/
inductive IsPolygonalPath : {a b : ℂ} → Path a b → Prop
  | refl (a : ℂ) : IsPolygonalPath (Path.refl a)
  | segment (a b : ℂ) : IsPolygonalPath (Path.segment a b)
  | trans {a b c : ℂ} {γ : Path a b} {δ : Path b c} :
      IsPolygonalPath γ → IsPolygonalPath δ → IsPolygonalPath (γ.trans δ)
  | cast {a b c d : ℂ} {γ : Path a b} (hc : c = a) (hd : d = b) :
      IsPolygonalPath γ → IsPolygonalPath (γ.cast hc hd)

theorem isPolygonalPath_concat {n : ℕ} (p : Fin (n + 1) → ℂ)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (hF : ∀ i, IsPolygonalPath (F i)) : IsPolygonalPath (Path.concat p F) := by
  induction n generalizing p with
  | zero => simpa using IsPolygonalPath.refl (p 0)
  | succ n ih =>
    rw [Path.concat_succ]
    exact (ih (p ∘ Fin.castSucc) (fun i => F i.castSucc)
      (fun i => hF i.castSucc)).trans (hF (Fin.last n))

/-- A nonempty cyclic list of indexed edges. Distinct edge indices may have identical geometry. -/
structure IndexedPolygonalCycle {E : Type u} (initial terminal : E → ℂ) where
  length : ℕ
  positive : 0 < length
  edge : Fin length → E
  next : ∀ i, terminal (edge i) =
    initial (edge ⟨(i.val + 1) % length, Nat.mod_lt _ positive⟩)

namespace IndexedPolygonalCycle

variable {E : Type u} {initial terminal : E → ℂ}

def base (D : IndexedPolygonalCycle initial terminal) : ℂ :=
  initial (D.edge ⟨0, D.positive⟩)

noncomputable def path (D : IndexedPolygonalCycle initial terminal) : Path D.base D.base :=
  cyclicPolygonalPath D.positive initial terminal D.edge D.next

theorem path_polygonal (D : IndexedPolygonalCycle initial terminal) :
    IsPolygonalPath D.path := by
  apply IsPolygonalPath.cast
  apply isPolygonalPath_concat
  intro i
  exact IsPolygonalPath.cast _ _ (IsPolygonalPath.segment _ _)

theorem path_range_subset (D : IndexedPolygonalCycle initial terminal) {U : Set ℂ}
    (hsupport : ∀ i, segment ℝ (initial (D.edge i)) (terminal (D.edge i)) ⊆ U) :
    Set.range D.path ⊆ U := by
  change Set.range (Path.concat _ _) ⊆ U
  apply concat_range_subset
  · rw [cyclicPolygonalVertices_zero]
    exact hsupport ⟨0, D.positive⟩ (left_mem_segment ℝ _ _)
  · intro i
    change Set.range (Path.segment (initial (D.edge i)) (terminal (D.edge i))) ⊆ U
    simpa only [Path.range_segment] using hsupport i

theorem path_curveIntegrable (D : IndexedPolygonalCycle initial terminal)
    (ω : ℂ → ℂ →L[ℂ] ℂ)
    (hseg : ∀ i, CurveIntegrable ω (Path.segment (initial (D.edge i)) (terminal (D.edge i)))) :
    CurveIntegrable ω D.path := by
  unfold path cyclicPolygonalPath
  rw [curveIntegrable_cast_iff]
  apply curveIntegrable_concat
  intro i
  simpa only [cyclicPolygonalEdgePath, curveIntegrable_cast_iff] using hseg i

theorem path_integral (D : IndexedPolygonalCycle initial terminal)
    (ω : ℂ → ℂ →L[ℂ] ℂ)
    (hseg : ∀ i, CurveIntegrable ω (Path.segment (initial (D.edge i)) (terminal (D.edge i)))) :
    curveIntegral ω D.path =
      ∑ i : Fin D.length, curveIntegral ω
        (Path.segment (initial (D.edge i)) (terminal (D.edge i))) := by
  unfold path cyclicPolygonalPath
  rw [curveIntegral_cast]
  have hedges : ∀ i, CurveIntegrable ω
      (cyclicPolygonalEdgePath D.positive initial terminal D.edge D.next i) := by
    intro i
    simpa only [cyclicPolygonalEdgePath, curveIntegrable_cast_iff] using hseg i
  rw [curveIntegral_concat ω _ _ hedges]
  apply Finset.sum_congr rfl
  intro i hi
  exact curveIntegral_cyclicPolygonalEdgePath ω D.positive initial terminal D.edge D.next i

end IndexedPolygonalCycle

theorem curveIntegrable_segment_of_continuousOn {f : ℂ → ℂ} {U : Set ℂ}
    (hf : ContinuousOn f U) {a b : ℂ} (hsupport : segment ℝ a b ⊆ U) :
    CurveIntegrable (fun z => ContinuousLinearMap.mul ℂ ℂ (f z)) (Path.segment a b) := by
  rw [curveIntegrable_segment]
  have hc : ContinuousOn (fun t : ℝ => f (AffineMap.lineMap a b t)) (uIcc 0 1) := by
    apply hf.comp (by fun_prop)
    intro t ht
    apply hsupport
    exact lineMap_mem_segment ℝ a b (by simpa only [uIcc_of_le zero_le_one] using ht)
  simpa only [ContinuousLinearMap.mul_apply'] using
    (hc.mul_const (b - a)).intervalIntegrable (μ := MeasureTheory.volume)

theorem sum_edge_enumeration {E : Type u} [DecidableEq E] {s : Finset E} {n : ℕ}
    (edge : Fin n → E) (hinj : Injective edge)
    (hcover : ∀ e, e ∈ s ↔ ∃ i, edge i = e) (g : E → ℂ) :
    ∑ i : Fin n, g (edge i) = ∑ e ∈ s, g e := by
  apply Finset.sum_bij (fun i _ => edge i)
  · intro i hi
    exact (hcover (edge i)).mpr ⟨i, rfl⟩
  · intro i hi j hj hij
    exact hinj hij
  · intro e he
    obtain ⟨i, rfl⟩ := (hcover e).mp he
    exact ⟨i, Finset.mem_univ _, rfl⟩
  · intro i hi
    rfl

theorem sum_unique_edge_partition {E : Type u} [Fintype E] [DecidableEq E]
    (C : Finset (Finset E))
    (hpart : ∀ e : E, ∃! s : Finset E, s ∈ C ∧ e ∈ s) (g : E → ℂ) :
    ∑ s ∈ C, ∑ e ∈ s, g e = ∑ e : E, g e := by
  have hdisj : Set.PairwiseDisjoint (↑C) (fun s : Finset E => s) := by
    intro s hs t ht hst
    apply Finset.disjoint_left.mpr
    intro e hes het
    obtain ⟨u, hu, huniq⟩ := hpart e
    exact hst ((huniq s ⟨hs, hes⟩).trans (huniq t ⟨ht, het⟩).symm)
  have hunion : C.biUnion (fun s => s) = Finset.univ := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
    obtain ⟨s, hs, _⟩ := hpart e
    exact ⟨s, hs.1, hs.2⟩
  rw [← Finset.sum_biUnion hdisj, hunion]

/-- A balanced finite collection of supported edges determines actual closed polygonal paths,
chosen once, preserving each edge index exactly once. For every continuous integrand, all paths
are integrable and the sum of their integrals is exactly the original sum of segment integrals. -/
theorem balanced_polygonal_cycle_package {E : Type u} [Fintype E] [DecidableEq E]
    (initial terminal : E → ℂ)
    (hbalanced : ∀ v, Fintype.card {e // initial e = v} =
      Fintype.card {e // terminal e = v})
    {U : Set ℂ} (hsupport : ∀ e, segment ℝ (initial e) (terminal e) ⊆ U) :
    ∃ C : Finset (Finset E), ∃ D : C → IndexedPolygonalCycle initial terminal,
      (∀ e : E, ∃! s : Finset E, s ∈ C ∧ e ∈ s) ∧
      (∀ s : C, Injective (D s).edge ∧
        (∀ e, e ∈ s.val ↔ ∃ i, (D s).edge i = e)) ∧
      (∀ s : C, IsPolygonalPath (D s).path ∧ Set.range (D s).path ⊆ U) ∧
      ∀ f : ℂ → ℂ, ContinuousOn f U →
        (∀ s : C, CurveIntegrable (fun z => ContinuousLinearMap.mul ℂ ℂ (f z)) (D s).path) ∧
        (∑ s : C, curveIntegral (fun z => ContinuousLinearMap.mul ℂ ℂ (f z)) (D s).path) =
          ∑ e : E, complexSegmentIntegral f (initial e) (terminal e) := by
  classical
  obtain ⟨C, hpart, hcycles⟩ := balanced_closed_cycle_partition initial terminal hbalanced
  have hex : ∀ s : C, ∃ D : IndexedPolygonalCycle initial terminal,
      Injective D.edge ∧ (∀ e, e ∈ s.val ↔ ∃ i, D.edge i = e) := by
    intro s
    obtain ⟨hp, edge, hinj, hcover, hnext⟩ := hcycles s.val s.property
    exact ⟨⟨s.val.card, hp, edge, hnext⟩, hinj, hcover⟩
  choose D hD using hex
  refine ⟨C, D, hpart, hD, ?_, ?_⟩
  · intro s
    exact ⟨(D s).path_polygonal, (D s).path_range_subset (fun i => hsupport _)⟩
  · intro f hf
    have hseg (e : E) : CurveIntegrable (fun z => ContinuousLinearMap.mul ℂ ℂ (f z))
        (Path.segment (initial e) (terminal e)) :=
      curveIntegrable_segment_of_continuousOn hf (hsupport e)
    refine ⟨fun s => (D s).path_curveIntegrable _ (fun i => hseg _), ?_⟩
    calc
      _ = ∑ s : C, ∑ e ∈ s.val, complexSegmentIntegral f (initial e) (terminal e) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [(D s).path_integral _ (fun i => hseg _)]
        simp_rw [curveIntegral_segment_eq_complexSegmentIntegral]
        exact sum_edge_enumeration (D s).edge (hD s).1 (hD s).2 _
      _ = ∑ s ∈ C, ∑ e ∈ s, complexSegmentIntegral f (initial e) (terminal e) :=
        Finset.sum_coe_sort C (fun s => ∑ e ∈ s, complexSegmentIntegral f (initial e) (terminal e))
      _ = _ := sum_unique_edge_partition C hpart _

#print axioms isPolygonalPath_concat
#print axioms IndexedPolygonalCycle.path_polygonal
#print axioms IndexedPolygonalCycle.path_range_subset
#print axioms IndexedPolygonalCycle.path_curveIntegrable
#print axioms IndexedPolygonalCycle.path_integral
#print axioms curveIntegrable_segment_of_continuousOn
#print axioms sum_edge_enumeration
#print axioms sum_unique_edge_partition
#print axioms balanced_polygonal_cycle_package

end RudinRCA.Chapter13Scratch
