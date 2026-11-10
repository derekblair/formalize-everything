import MittagLefflerInfinityWork
import ZeroSetNormalizationWork
import Mathlib.Basic.Denumerable

/-! Set-indexed normalized Mittag-Leffler construction, including finite and
empty sets and regularity at infinity. Draft awaiting a serialized Lean check. -/

noncomputable section
open Filter Set Finset Metric Bornology
open scoped Topology OnePoint

namespace RudinRCA.Chapter15

def principalPartOnSphere (P : Polynomial ℂ) (a : ℂ) (p : ComplexSphere) : ℂ :=
  p.elim (P.eval 0) (fun z ↦ P.eval (1 / (z - a)))

theorem principalPartOnSphere_infinity_chart (P : Polynomial ℂ) (a : ℂ) :
    principalPartOnSphere P a ∘ sphereInfinityChart =
      fun w ↦ P.eval (w / (1 - a * w)) := by
  funext w
  by_cases hw : w = 0
  · subst w; simp [principalPartOnSphere]
  · simp only [Function.comp_def, sphereInfinityChart_of_ne_zero hw, principalPartOnSphere,
      OnePoint.elim_some, ← one_div, ← reciprocal_at_infinity_eq hw]

theorem principalPartOnSphere_analytic_infinity (P : Polynomial ℂ) (a : ℂ) :
    SphereAnalyticAt (principalPartOnSphere P a) ∞ := by
  rw [sphereAnalyticAt_infty, principalPartOnSphere_infinity_chart]
  exact (analyticAt_id.div
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (by simp)).aeval_polynomial P

/-- The normalized Mittag-Leffler theorem for a bounded discrete set. The
function is analytic at infinity and away from the specified finite poles. -/
theorem normalized_mittag_leffler_on_set {C S : Set ℂ}
    (hC : IsCompact C) (hCne : C.Nonempty) (hS : S ⊆ Cᶜ)
    (hScount : S.Countable) (hSbound : IsBounded S)
    (hno : ∀ z ∈ Cᶜ, ¬ AccPt z (𝓟 S)) (P : S → Polynomial ℂ) :
    ∃ F : ComplexSphere → ℂ,
      MeromorphicOn (fun z ↦ F (↑z)) Cᶜ ∧
      SphereAnalyticAt F ∞ ∧
      (∀ z ∈ Cᶜ, z ∉ S → AnalyticAt ℂ (fun w ↦ F (↑w)) z) ∧
      ∀ a : S, AnalyticAt ℂ
        (fun z ↦ F (↑z) - (P a).eval (1 / (z - a))) a := by
  classical
  cases finite_or_infinite S with
  | inl hfinite =>
    letI := hfinite
    letI : Fintype S := Fintype.ofFinite S
    let F : ComplexSphere → ℂ := fun p ↦ ∑ a : S, principalPartOnSphere (P a) a p
    refine ⟨F, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact MeromorphicAt.fun_sum fun a _ ↦ meromorphicAt_polynomial_eval
        ((MeromorphicAt.const 1 z).div ((MeromorphicAt.id z).sub (.const a z))) (P a)
    · change AnalyticAt ℂ (fun w ↦ ∑ a : S, principalPartOnSphere (P a) a (sphereInfinityChart w)) 0
      exact Finset.analyticAt_fun_sum _ fun a _ ↦ principalPartOnSphere_analytic_infinity (P a) a
    · intro z hz hzS
      apply Finset.analyticAt_fun_sum
      intro a _
      have hza : z ≠ a := fun h ↦ hzS (h.symm ▸ a.property)
      exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr hza)).aeval_polynomial (P a)
    · intro a
      have hsum : AnalyticAt ℂ
          (fun z ↦ ∑ b ∈ (univ : Finset S).erase a, (P b).eval (1 / (z - b))) a := by
        apply Finset.analyticAt_fun_sum
        intro b hb
        have hab : (a : ℂ) ≠ b := fun h ↦ (mem_erase.mp hb).1 (Subtype.ext h).symm
        exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const)
          (sub_ne_zero.mpr hab)).aeval_polynomial (P b)
      convert hsum using 1
      ext z
      dsimp [F, principalPartOnSphere]
      exact (sub_eq_iff_eq_add).2 (sum_erase_add univ
        (fun b : S ↦ (P b).eval (1 / (z - b))) (mem_univ a)).symm
  | inr hinfinite =>
    letI := hinfinite
    haveI : Countable S := hScount.to_subtype
    let e : ℕ ≃ S := Classical.choice inferInstance
    let a : ℕ → ℂ := fun n ↦ e n
    have haS (n : ℕ) : a n ∈ S := (e n).property
    have ha (n : ℕ) : a n ∉ C := hS (haS n)
    have hainj : Function.Injective a := Subtype.val_injective.comp e.injective
    have hescape : ∀ K : Set ℂ, IsCompact K → K ⊆ Cᶜ →
        ∀ᶠ n in atTop, a n ∉ K := by
      intro K hK hKC
      have hSK := finite_inter_compact_of_no_accumulation hno hK hKC
      have hpre : (a ⁻¹' (S ∩ K)).Finite := hSK.preimage hainj.injOn
      have hpre' : {n : ℕ | a n ∈ K}.Finite := hpre.subset fun n hn ↦ ⟨haS n, hn⟩
      simpa only [Nat.cofinite_eq_atTop] using hpre'.eventually_cofinite_notMem
    choose b hb hnearest using (fun n ↦ hC.exists_infDist_eq_dist hCne (a n))
    obtain ⟨Ra, hRa, hbounda⟩ := hSbound.exists_pos_norm_le
    obtain ⟨Rb, hRb, hboundb⟩ := hC.isBounded.exists_pos_norm_le
    have hd := infDist_tendsto_zero_of_bounded_escape a C Ra
      (fun n ↦ hbounda (a n) (haS n)) hescape
    have hsmall := nearest_boundary_difference_tendsto_zero a b C hnearest hd
    let Q : ℕ → Polynomial ℂ := fun n ↦ P (e n)
    obtain ⟨N, happrox, hconv⟩ :=
      exists_locally_uniform_principal_part_series Q a b hC.isClosed hCne ha hb hsmall
    let u := fun n z ↦ correctedPrincipalPart (Q n) (N n) (a n) (b n) z
    let F : ComplexSphere → ℂ := fun p ↦ p.elim 0 (fun z ↦ ∑' n, u n z)
    have htail := fun z hz ↦ correctedPrincipalPart_eventually_analytic_near Q N a b
      hC.isClosed hCne ha hb hsmall (z := z) hz
    have hinfty := principal_part_series_analytic_at_infinity Q N a b (max Ra Rb)
      (hRa.trans_le (le_max_left _ _))
      (fun n ↦ (hbounda (a n) (haS n)).trans (le_max_left _ _))
      (fun n ↦ (hboundb (b n) (hb n)).trans (le_max_right _ _)) hsmall happrox
    refine ⟨F, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact meromorphicAt_of_locally_uniform_series hC.isClosed.isOpen_compl hconv
        (fun n ↦ correctedPrincipalPart_meromorphicAt (Q n) (N n) (a n) (b n) z)
        (htail z hz)
    · change AnalyticAt ℂ (F ∘ sphereInfinityChart) 0
      have heq : F ∘ sphereInfinityChart = fun w ↦
          ∑' n, correctedPrincipalPartAtInfinity (Q n) (N n) (a n) (b n) w := by
        funext w
        by_cases hw : w = 0
        · subst w; simp [F]
        · simp only [Function.comp_def, sphereInfinityChart_of_ne_zero hw, F, OnePoint.elim_some]
          simpa only [one_div] using (hinfty.2.2 w hw).symm
      rw [heq]
      exact hinfty.1
    · intro z hz hzS
      apply analyticAt_of_locally_uniform_series hC.isClosed.isOpen_compl hconv _ (htail z hz)
      intro n
      exact correctedPrincipalPart_analyticAt (Q n) (N n)
        (fun h ↦ hzS (h.symm ▸ haS n)) (fun h ↦ hz (h.symm ▸ hb n))
    · intro aj
      obtain ⟨j, rfl⟩ := e.surjective aj
      have hother : ∀ n, n ≠ j → AnalyticAt ℂ (u n) (a j) := by
        intro n hnj
        exact correctedPrincipalPart_analyticAt (Q n) (N n)
          (fun h ↦ hnj (hainj h.symm)) (fun h ↦ ha j (h.symm ▸ hb n))
      have hsub := analyticAt_series_sub_term hC.isClosed.isOpen_compl hconv j hother
        (htail (a j) (ha j))
      have happ : AnalyticAt ℂ (fun z ↦ (Q j).eval (reciprocalExpansion (N j) (a j) (b j) z))
          (a j) :=
        (analyticAt_reciprocalExpansion (N j) (a j) (b j)
          (fun h ↦ ha j (h.symm ▸ hb j))).aeval_polynomial (Q j)
      convert hsub.sub happ using 1
      ext z
      dsimp [F, u, Q, a, correctedPrincipalPart]
      ring

#print axioms principalPartOnSphere_infinity_chart
#print axioms principalPartOnSphere_analytic_infinity
#print axioms normalized_mittag_leffler_on_set

end RudinRCA.Chapter15
