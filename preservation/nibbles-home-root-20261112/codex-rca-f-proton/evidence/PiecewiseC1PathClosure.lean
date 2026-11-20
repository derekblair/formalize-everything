import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Topology.Subpath

/-! SUPERSEDED DRAFT: exclude from aggregates; use PolygonalRegularity.lean.
Retained as an independent reference, without a compilation claim.

Closure of the finite C¹ path class under finite concatenation.
This follows PrimitiveCurveIntegral.lean in the aggregate. -/

open Set Function
open scoped Topology

namespace RudinRCA.Chapter13

theorem IsPiecewiseC1Path.of_contDiffOn {a b : ℂ} {γ : Path a b}
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) : IsPiecewiseC1Path γ := by
  refine ⟨1, fun k => min (k : ℝ) 1, ?_, by simp, by simp, ?_⟩
  · intro i j hij
    exact min_le_min (by exact_mod_cast hij) le_rfl
  · intro k hk
    have : k = 0 := by omega
    simpa [this] using hγ

theorem IsPiecewiseC1Path.refl (a : ℂ) : IsPiecewiseC1Path (Path.refl a) := by
  apply IsPiecewiseC1Path.of_contDiffOn
  change ContDiffOn ℝ 1 (fun _ : ℝ => a) (Icc 0 1)
  exact contDiffOn_const

theorem IsPiecewiseC1Path.segment (a b : ℂ) : IsPiecewiseC1Path (Path.segment a b) := by
  apply IsPiecewiseC1Path.of_contDiffOn
  exact (AffineMap.contDiff_lineMap a b).contDiffOn.congr (Path.eqOn_extend_segment a b)

theorem IsPiecewiseC1Path.cast {a b a' b' : ℂ} {γ : Path a b}
    (hγ : IsPiecewiseC1Path γ) (ha : a' = a) (hb : b' = b) :
    IsPiecewiseC1Path (γ.cast ha hb) := by
  simpa only [IsPiecewiseC1Path, Path.extend_cast] using hγ

/-- Concatenate the first partition, scaled to [0,1/2], and the second,
translated and scaled to [1/2,1]. No derivative matching is imposed at the join. -/
theorem IsPiecewiseC1Path.trans {a b c : ℂ} {γ : Path a b} {δ : Path b c}
    (hγ : IsPiecewiseC1Path γ) (hδ : IsPiecewiseC1Path δ) :
    IsPiecewiseC1Path (γ.trans δ) := by
  obtain ⟨n, t, ht, ht0, htn, hγpieces⟩ := hγ
  obtain ⟨m, u, hu, hu0, hum, hδpieces⟩ := hδ
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    simp [hm0, hu0] at hum
  let v : ℕ → ℝ := fun k => if k ≤ n then t k / 2 else (1 + u (k - n)) / 2
  have hleft (k : ℕ) (hk : k ≤ n) : v k = t k / 2 := by simp [v, hk]
  have hright (k : ℕ) (hk : n ≤ k) : v k = (1 + u (k - n)) / 2 := by
    rcases hk.eq_or_lt with rfl | hk
    · simp [v, htn, hu0]
    · simp [v, not_le.mpr hk]
  refine ⟨n + m, v, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    by_cases hin : i ≤ n
    · by_cases hjn : j ≤ n
      · rw [hleft i hin, hleft j hjn]
        exact div_le_div_of_nonneg_right (ht hij) (by norm_num)
      · rw [hleft i hin, hright j (by omega)]
        have hti : t i ≤ 1 := htn ▸ ht hin
        have huj : 0 ≤ u (j - n) := hu0 ▸ hu (Nat.zero_le _)
        linarith
    · rw [hright i (by omega), hright j (by omega)]
      have hui := hu (show i - n ≤ j - n by omega)
      linarith
  · simp [v, ht0]
  · rw [hright (n + m) (by omega)]
    simp [hum]
  · intro k hk
    by_cases hkn : k < n
    · rw [hleft k (by omega), hleft (k + 1) (by omega)]
      have hcomp : ContDiffOn ℝ 1 (fun s => γ.extend (2 * s))
          (Icc (t k / 2) (t (k + 1) / 2)) :=
        (hγpieces k hkn).comp (by fun_prop) (by
          intro s hs
          constructor <;> linarith [hs.1, hs.2])
      apply hcomp.congr
      intro s hs
      apply Path.extend_trans_of_le_half
      have htk : t (k + 1) ≤ 1 := htn ▸ ht (by omega)
      linarith [hs.2]
    · have hnk : n ≤ k := by omega
      rw [hright k hnk, hright (k + 1) (by omega)]
      have hidx : k + 1 - n = (k - n) + 1 := by omega
      rw [hidx]
      have hcomp : ContDiffOn ℝ 1 (fun s => δ.extend (2 * s - 1))
          (Icc ((1 + u (k - n)) / 2) ((1 + u ((k - n) + 1)) / 2)) :=
        (hδpieces (k - n) (by omega)).comp (by fun_prop) (by
          intro s hs
          constructor <;> linarith [hs.1, hs.2])
      apply hcomp.congr
      intro s hs
      apply Path.extend_trans_of_half_le
      have huk : 0 ≤ u (k - n) := hu0 ▸ hu (Nat.zero_le _)
      linarith [hs.1]

/-- Every finite concatenation of finitely piecewise C¹ paths is finitely piecewise C¹. -/
theorem piecewiseC1_concat {n : ℕ} (p : Fin (n + 1) → ℂ)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (hF : ∀ i, IsPiecewiseC1Path (F i)) : IsPiecewiseC1Path (Path.concat p F) := by
  induction n generalizing p with
  | zero => simpa using IsPiecewiseC1Path.refl (p 0)
  | succ n ih =>
    rw [Path.concat_succ]
    exact (ih (p ∘ Fin.castSucc) (fun i => F i.castSucc) (fun i => hF i.castSucc)).trans
      (hF (Fin.last n))

#print axioms IsPiecewiseC1Path.of_contDiffOn
#print axioms IsPiecewiseC1Path.refl
#print axioms IsPiecewiseC1Path.segment
#print axioms IsPiecewiseC1Path.cast
#print axioms IsPiecewiseC1Path.trans
#print axioms piecewiseC1_concat
end RudinRCA.Chapter13
