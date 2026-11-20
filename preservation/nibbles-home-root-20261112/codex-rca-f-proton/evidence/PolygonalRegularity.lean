import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Subpath
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Aggregate dependencies: PrimitiveCurveIntegral and PolygonalCyclePackage. -/

open Set

namespace RudinRCA.Chapter13Scratch

open RudinRCA.Chapter13 (IsPiecewiseC1Path)

theorem piecewiseC1Path_of_contDiffOn {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) : IsPiecewiseC1Path γ := by
  refine ⟨1, fun k => min (k : ℝ) 1, ?_, by simp, by simp, ?_⟩
  · intro i j hij
    exact min_le_min_right 1 (Nat.cast_le.mpr hij)
  · intro k hk
    have hk0 : k = 0 := by omega
    simpa [hk0] using hγ

theorem piecewiseC1Path_refl (a : ℂ) : IsPiecewiseC1Path (Path.refl a) := by
  apply piecewiseC1Path_of_contDiffOn
  simpa only [Path.refl_extend, ContinuousMap.coe_const] using
    (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ => a) (Icc 0 1))

theorem piecewiseC1Path_segment (a b : ℂ) : IsPiecewiseC1Path (Path.segment a b) := by
  apply piecewiseC1Path_of_contDiffOn
  exact (AffineMap.contDiff_lineMap a b).contDiffOn.congr (Path.eqOn_extend_segment a b)

theorem piecewiseC1Path_cast {a b c d : ℂ} {γ : Path a b}
    (hc : c = a) (hd : d = b) (hγ : IsPiecewiseC1Path γ) :
    IsPiecewiseC1Path (γ.cast hc hd) := by
  simpa only [IsPiecewiseC1Path, Path.extend_cast] using hγ

/-- The partition for a binary path concatenation: halve the left partition and translate and
halve the right partition. The common knot is exactly `1/2`. -/
def transPartition (n : ℕ) (t u : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k ≤ n then t k / 2 else (1 + u (k - n)) / 2

theorem transPartition_left {n k : ℕ} (t u : ℕ → ℝ) (hk : k ≤ n) :
    transPartition n t u k = t k / 2 := if_pos hk

theorem transPartition_right {n k : ℕ} (t u : ℕ → ℝ) (htn : t n = 1) (hu0 : u 0 = 0)
    (hk : n ≤ k) : transPartition n t u k = (1 + u (k - n)) / 2 := by
  by_cases hkn : k ≤ n
  · have heq : k = n := Nat.le_antisymm hkn hk
    simp [transPartition, heq, htn, hu0]
  · exact if_neg hkn

theorem monotone_transPartition {n : ℕ} {t u : ℕ → ℝ}
    (ht : Monotone t) (hu : Monotone u) (htn : t n = 1) (hu0 : u 0 = 0) :
    Monotone (transPartition n t u) := by
  intro i j hij
  by_cases hj : j ≤ n
  · rw [transPartition_left t u (hij.trans hj), transPartition_left t u hj]
    exact div_le_div_of_nonneg_right (ht hij) (by norm_num)
  · have hnj : n ≤ j := by omega
    rw [transPartition_right t u htn hu0 hnj]
    by_cases hi : i ≤ n
    · rw [transPartition_left t u hi]
      have hti : t i ≤ 1 := htn ▸ ht hi
      have huj : 0 ≤ u (j - n) := hu0 ▸ hu (Nat.zero_le _)
      linarith
    · have hni : n ≤ i := by omega
      rw [transPartition_right t u htn hu0 hni]
      have hsub : u (i - n) ≤ u (j - n) := hu (Nat.sub_le_sub_right hij n)
      linarith

theorem piecewiseC1Path_trans {a b c : ℂ} {γ : Path a b} {δ : Path b c}
    (hγ : IsPiecewiseC1Path γ) (hδ : IsPiecewiseC1Path δ) :
    IsPiecewiseC1Path (γ.trans δ) := by
  obtain ⟨n, t, ht, ht0, htn, hpieces⟩ := hγ
  obtain ⟨m, u, hu, hu0, hum, hpieces'⟩ := hδ
  refine ⟨n + m, transPartition n t u,
    monotone_transPartition ht hu htn hu0, ?_, ?_, ?_⟩
  · rw [transPartition_left t u (Nat.zero_le n), ht0]
    norm_num
  · rw [transPartition_right t u htn hu0 (Nat.le_add_right n m)]
    simp [hum]
  · intro k hk
    by_cases hkn : k < n
    · rw [transPartition_left t u (Nat.le_of_lt hkn),
        transPartition_left t u (by omega)]
      have hcomp : ContDiffOn ℝ 1 (fun x : ℝ => γ.extend (2 * x))
          (Icc (t k / 2) (t (k + 1) / 2)) := by
        apply (hpieces k hkn).comp (by fun_prop)
        intro x hx
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      apply hcomp.congr
      intro x hx
      apply Path.extend_trans_of_le_half
      have htk : t (k + 1) ≤ 1 := htn ▸ ht (by omega)
      linarith [hx.2]
    · have hnk : n ≤ k := by omega
      rw [transPartition_right t u htn hu0 hnk,
        transPartition_right t u htn hu0 (by omega)]
      have hkm : k - n < m := by omega
      have hsucc : k + 1 - n = (k - n) + 1 := by omega
      rw [hsucc]
      have hcomp : ContDiffOn ℝ 1 (fun x : ℝ => δ.extend (2 * x - 1))
          (Icc ((1 + u (k - n)) / 2) ((1 + u ((k - n) + 1)) / 2)) := by
        apply (hpieces' (k - n) hkm).comp (by fun_prop)
        intro x hx
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      apply hcomp.congr
      intro x hx
      apply Path.extend_trans_of_half_le
      have huk : 0 ≤ u (k - n) := hu0 ▸ hu (Nat.zero_le _)
      linarith [hx.1]

/-- Every path built by finitely concatenating line segments has a finite C¹ partition in the
chapter's exact path class, including the parametrization at every concatenation knot. -/
theorem isPiecewiseC1Path_of_isPolygonalPath {a b : ℂ} {γ : Path a b}
    (hγ : IsPolygonalPath γ) : IsPiecewiseC1Path γ := by
  induction hγ with
  | refl a => exact piecewiseC1Path_refl a
  | segment a b => exact piecewiseC1Path_segment a b
  | trans hγ hδ ihγ ihδ => exact piecewiseC1Path_trans ihγ ihδ
  | cast hc hd hγ ih => exact piecewiseC1Path_cast hc hd ih

theorem IndexedPolygonalCycle.path_piecewiseC1 {E : Type*} {initial terminal : E → ℂ}
    (D : IndexedPolygonalCycle initial terminal) : IsPiecewiseC1Path D.path :=
  isPiecewiseC1Path_of_isPolygonalPath D.path_polygonal

#print axioms piecewiseC1Path_of_contDiffOn
#print axioms piecewiseC1Path_refl
#print axioms piecewiseC1Path_segment
#print axioms piecewiseC1Path_cast
#print axioms transPartition_left
#print axioms transPartition_right
#print axioms monotone_transPartition
#print axioms piecewiseC1Path_trans
#print axioms isPiecewiseC1Path_of_isPolygonalPath
#print axioms IndexedPolygonalCycle.path_piecewiseC1

end RudinRCA.Chapter13Scratch
