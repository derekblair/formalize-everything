import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Tactic.Linarith

open Set Filter
open scoped Topology ZeroAtInfty

noncomputable section

namespace RCA618

variable (X : Type*) [TopologicalSpace X]

/-- The compactly supported continuous functions, equipped with their inherited supremum norm. -/
def compactSupportSubmodule : Submodule ℂ C₀(X, ℂ) where
  carrier := {f | HasCompactSupport (f : X → ℂ)}
  zero_mem' := by
    change HasCompactSupport (fun _ : X => (0 : ℂ))
    exact HasCompactSupport.zero
  add_mem' := by
    intro f g hf hg
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change HasCompactSupport (fun x : X => c • f x)
    exact HasCompactSupport.smul_left (f := fun _ : X => c) hf

local instance compactSupportSubmoduleNormedAddCommGroup :
    NormedAddCommGroup (compactSupportSubmodule X) :=
  Submodule.normedAddCommGroup _

local instance compactSupportSubmoduleNormedSpace :
    NormedSpace ℂ (compactSupportSubmodule X) :=
  Submodule.normedSpace _

variable [LocallyCompactSpace X] [T2Space X]

set_option maxHeartbeats 800000 in
/-- Cutoff approximation does not require sigma compactness or a countable basis. -/
theorem exists_compactSupport_approx (f : C₀(X, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C₀(X, ℂ), HasCompactSupport (g : X → ℂ) ∧ dist f g < ε := by
  have hev : ∀ᶠ x in cocompact X, dist (f x) 0 < ε / 2 :=
    Metric.tendsto_nhds.mp (zero_at_infty f) (ε / 2) (half_pos hε)
  obtain ⟨K, hK, hKf⟩ := mem_cocompact.mp hev
  obtain ⟨φ, hφK, hφcomp, _, hφrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ
      (subset_univ K)
  have hgcomp : HasCompactSupport (fun x : X => φ x • f x) :=
    HasCompactSupport.smul_right hφcomp
  let g : C₀(X, ℂ) :=
    ⟨⟨fun x => φ x • f x, (map_continuous φ).smul (map_continuous f)⟩,
      hgcomp.is_zero_at_infty⟩
  refine ⟨g, hgcomp, ?_⟩
  have hbound (x : X) : ‖((f - g) : C₀(X, ℂ)) x‖ ≤ ε / 2 := by
    change ‖f x - φ x • f x‖ ≤ ε / 2
    by_cases hx : x ∈ K
    · have hφx : φ x = 1 := hφK hx
      simp only [hφx, one_smul, sub_self, norm_zero]
      exact (half_pos hε).le
    · have hfsmall : ‖f x‖ < ε / 2 := by
        simpa only [dist_zero_right, Set.mem_setOf_eq] using hKf hx
      have hφx := hφrange x
      have heq : f x - φ x • f x = (1 - φ x) • f x := by
        rw [sub_smul, one_smul]
      rw [heq, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hφx.2)]
      exact (mul_le_of_le_one_left (norm_nonneg (f x)) (by linarith [hφx.1])).trans
        hfsmall.le
  have hn : ‖f - g‖ ≤ ε / 2 := by
    change ‖(f - g).toBCF‖ ≤ ε / 2
    exact (BoundedContinuousFunction.norm_le (half_pos hε).le).mpr hbound
  rw [dist_eq_norm]
  exact hn.trans_lt (half_lt_self hε)

theorem dense_compactSupport :
    Dense {f : C₀(X, ℂ) | HasCompactSupport (f : X → ℂ)} := by
  rw [Metric.dense_iff]
  intro f ε hε
  obtain ⟨g, hg, hfg⟩ := exists_compactSupport_approx X f hε
  refine ⟨g, ?_, hg⟩
  simpa only [Metric.mem_ball, dist_comm] using hfg

/-- The extension assertion at the start of Rudin 6.18, with uniqueness and norm equality. -/
theorem exists_unique_extension
    (F : (compactSupportSubmodule X) →L[ℂ] ℂ) :
    ∃! G : C₀(X, ℂ) →L[ℂ] ℂ,
      (∀ f : compactSupportSubmodule X, G f = F f) ∧ ‖G‖ = ‖F‖ := by
  obtain ⟨G, hG, hnorm⟩ := exists_extension_norm_eq (compactSupportSubmodule X) F
  refine ⟨G, ⟨hG, hnorm⟩, ?_⟩
  intro H hH
  apply DFunLike.ext'
  apply H.continuous.ext_on (dense_compactSupport X) G.continuous
  intro f hf
  exact (hH.1 ⟨f, hf⟩).trans (hG ⟨f, hf⟩).symm

#print axioms exists_unique_extension
end RCA618
