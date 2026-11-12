import RudinRCA.Chapter13
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Tactic.Abel

/- Prerequisites: Exhaustion.lean and MittagLefflerCore.lean.
   This is the exact series construction from finite cumulative principal
   parts and Runge correction functions. It preserves the complete principal
   part at every prescribed point and proves analyticity at all other points. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace RudinRCA.Chapter13

def finitePrincipalSum (S : Finset ℂ) (m : ℂ → ℕ) (c : ℂ → ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ α ∈ S, finitePrincipalPart (m α) (c α) α z

theorem finitePrincipalSum_meromorphicAt (S : Finset ℂ) (m : ℂ → ℕ)
    (c : ℂ → ℕ → ℂ) (z : ℂ) : MeromorphicAt (finitePrincipalSum S m c) z := by
  exact MeromorphicAt.fun_sum (fun α _ ↦ finitePrincipalPart_meromorphicAt (m α) (c α) α z)

theorem finitePrincipalSum_analyticAt (S : Finset ℂ) (m : ℂ → ℕ)
    (c : ℂ → ℕ → ℂ) {z : ℂ} (hz : z ∉ S) :
    AnalyticAt ℂ (finitePrincipalSum S m c) z := by
  apply Finset.analyticAt_fun_sum
  intro α hα
  exact finitePrincipalPart_analyticAt (m α) (c α) α (fun h ↦ hz (h.symm ▸ hα))

theorem finitePrincipalSum_sub_principal_analyticAt (S : Finset ℂ) (m : ℂ → ℕ)
    (c : ℂ → ℕ → ℂ) {α : ℂ} (hα : α ∈ S) :
    AnalyticAt ℂ (fun z ↦ finitePrincipalSum S m c z -
      finitePrincipalPart (m α) (c α) α z) α := by
  classical
  have h : AnalyticAt ℂ (finitePrincipalSum (S.erase α) m c) α :=
    finitePrincipalSum_analyticAt _ _ _ (by simp)
  convert h using 1
  ext z
  exact (Finset.sum_erase_eq_sub hα).symm

theorem finitePrincipalSum_sub_eq_sdiff {S T : Finset ℂ} (hST : S ⊆ T)
    (m : ℂ → ℕ) (c : ℂ → ℕ → ℂ) (z : ℂ) :
    finitePrincipalSum T m c z - finitePrincipalSum S m c z =
      finitePrincipalSum (T \ S) m c z := by
  classical
  exact (Finset.sum_sdiff_eq_sub hST).symm

/-- Given the cumulative principal parts over A∩Kₙ and holomorphic Runge
    corrections bounded by 2⁻ⁿ on Kₙ, their normally convergent difference
    series realizes all prescribed principal parts. -/
theorem mittag_leffler_of_exhaustion_corrections {Ω A : Set ℂ} (hΩ : IsOpen Ω)
    (hAΩ : A ⊆ Ω) (m : ℂ → ℕ) (c : ℂ → ℕ → ℂ)
    (S : ℕ → Finset ℂ)
    (hS : ∀ n α, α ∈ S n ↔ α ∈ A ∩ exhaustionLevel Ω n)
    (r : ℕ → ℂ → ℂ) (hr : ∀ n, DifferentiableOn ℂ (r n) Ω)
    (herror : ∀ n z, z ∈ exhaustionLevel Ω n →
      ‖finitePrincipalSum (S (n + 1)) m c z - finitePrincipalSum (S n) m c z - r n z‖ ≤
        (1 / 2 : ℝ) ^ n) :
    ∃ f : ℂ → ℂ, MeromorphicOn f Ω ∧
      (∀ α ∈ A, AnalyticAt ℂ (fun z ↦ f z - finitePrincipalPart (m α) (c α) α z) α) ∧
      ∀ z ∈ Ω \ A, AnalyticAt ℂ f z := by
  classical
  let Q : ℕ → ℂ → ℂ := fun n ↦ finitePrincipalSum (S n) m c
  let g : ℕ → ℂ → ℂ := fun n z ↦ Q (n + 1) z - Q n z - r n z
  let f : ℂ → ℂ := fun z ↦ Q 0 z + ∑' n, g n z
  have hmono : Monotone S := by
    intro n k hnk α hα
    have hh := (hS n α).mp hα
    exact (hS k α).mpr ⟨hh.1, exhaustionLevel_mono Ω hnk hh.2⟩
  have hgeom : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hrem : ∀ N z, z ∈ interior (exhaustionLevel Ω N) →
      AnalyticAt ℂ (fun w ↦ f w - Q N w) z := by
    intro N z hz
    have hUΩ : interior (exhaustionLevel Ω N) ⊆ Ω :=
      interior_subset.trans (exhaustionLevel_subset Ω N)
    have htailDiff : ∀ n : ℕ, DifferentiableOn ℂ (g (n + N))
        (interior (exhaustionLevel Ω N)) := by
      intro n w hw
      have hwN : w ∈ exhaustionLevel Ω N := interior_subset hw
      have hwk : w ∈ exhaustionLevel Ω (n + N) :=
        exhaustionLevel_mono Ω (Nat.le_add_left N n) hwN
      have hnot : w ∉ S (n + N + 1) \ S (n + N) := by
        intro hh
        obtain ⟨hwnext, hwnot⟩ := Finset.mem_sdiff.mp hh
        exact hwnot ((hS (n + N) w).mpr ⟨((hS _ w).mp hwnext).1, hwk⟩)
      have ha := finitePrincipalSum_analyticAt
        (S (n + N + 1) \ S (n + N)) m c hnot
      have hdiff : DifferentiableAt ℂ (fun v ↦ Q (n + N + 1) v - Q (n + N) v) w := by
        have heq : (fun v ↦ Q (n + N + 1) v - Q (n + N) v) =
            finitePrincipalSum (S (n + N + 1) \ S (n + N)) m c := by
          funext v
          exact finitePrincipalSum_sub_eq_sdiff (hmono (Nat.le_succ _)) m c v
        rw [heq]
        exact ha.differentiableAt
      exact (hdiff.sub ((hr (n + N)).differentiableAt (hΩ.mem_nhds (hUΩ hw)))).differentiableWithinAt
    have htailBound : ∀ n : ℕ, ∀ w ∈ interior (exhaustionLevel Ω N),
        ‖g (n + N) w‖ ≤ (1 / 2 : ℝ) ^ (n + N) := by
      intro n w hw
      exact herror (n + N) w (exhaustionLevel_mono Ω (Nat.le_add_left N n) (interior_subset hw))
    have htail := analyticAt_tsum_sub_prefix N isOpen_interior hz
      ((summable_nat_add_iff N).mpr hgeom) htailDiff htailBound
    have hrc : AnalyticAt ℂ (fun w ↦ ∑ n ∈ Finset.range N, r n w) z := by
      exact Finset.analyticAt_fun_sum _ (fun n _ ↦ (hr n).analyticAt (hΩ.mem_nhds (hUΩ hz)))
    convert htail.sub hrc using 1
    ext w
    dsimp [f, g]
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub]
    abel
  have hlocal : ∀ z ∈ Ω, ∃ N, z ∈ interior (exhaustionLevel Ω N) := by
    intro z hz
    obtain ⟨n, hn⟩ := exists_mem_exhaustionLevel hΩ hz
    exact ⟨n + 1, exhaustionLevel_subset_interior_succ Ω n hn⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨N, hN⟩ := hlocal z hz
    convert (hrem N z hN).meromorphicAt.add
      (finitePrincipalSum_meromorphicAt (S N) m c z) using 1
    ext w
    simp [Q]
  · intro α hα
    obtain ⟨N, hN⟩ := hlocal α (hAΩ hα)
    have hαS : α ∈ S N := (hS N α).mpr ⟨hα, interior_subset hN⟩
    convert (hrem N α hN).add (finitePrincipalSum_sub_principal_analyticAt (S N) m c hαS) using 1
    ext w
    dsimp [Q]
    abel
  · intro z hz
    obtain ⟨N, hN⟩ := hlocal z hz.1
    have hzS : z ∉ S N := fun h ↦ hz.2 (((hS N z).mp h).1)
    convert (hrem N z hN).add (finitePrincipalSum_analyticAt (S N) m c hzS) using 1
    ext w
    simp [Q]

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.finitePrincipalSum_sub_principal_analyticAt
#print axioms RudinRCA.Chapter13.mittag_leffler_of_exhaustion_corrections
