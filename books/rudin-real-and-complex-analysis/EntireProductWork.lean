import RudinRCA.Chapter15
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed

open Filter Finset
open scoped Topology
noncomputable section

namespace RudinRCA.Chapter15

/-- The admissibility assertion in 15.9: with zero-based indexing, `p n = n`
always works for a sequence of nonzero points escaping to infinity. -/
theorem summable_primary_majorant_nat {a : ℕ → ℂ}
    (ha : ∀ n, a n ≠ 0) (hinfty : Tendsto (fun n ↦ ‖a n‖) atTop atTop)
    {r : ℝ} (hr : 0 < r) :
    Summable (fun n ↦ (r / ‖a n‖) ^ (n + 1)) := by
  have hgeo : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1)) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).comp_injective
      (fun n m h ↦ Nat.add_right_cancel h)
  apply hgeo.of_norm_bounded_eventually_nat
  filter_upwards [hinfty.eventually (eventually_ge_atTop (2 * r))] with n hn
  have hapos : 0 < ‖a n‖ := norm_pos_iff.mpr (ha n)
  have hnonneg : 0 ≤ r / ‖a n‖ := div_nonneg hr.le hapos.le
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hnonneg _)]
  apply pow_le_pow_left₀ hnonneg
  apply (div_le_iff₀ hapos).2
  linarith

/-- Local uniform summability of the primary-factor errors in 15.9. -/
theorem primary_errors_locally_uniform {a : ℕ → ℂ} {p : ℕ → ℕ}
    (ha : ∀ n, a n ≠ 0) (hinfty : Tendsto (fun n ↦ ‖a n‖) atTop atTop)
    (hsum : ∀ r : ℝ, 0 < r → Summable (fun n ↦ (r / ‖a n‖) ^ (p n + 1))) :
    TendstoLocallyUniformlyOn
      (fun N z ↦ ∑ n ∈ range N, ‖1 - elementaryFactor (p n) (z / a n)‖)
      (fun z ↦ ∑' n, ‖1 - elementaryFactor (p n) (z / a n)‖) atTop Set.univ := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).2
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (f := fun z : ℂ ↦ z) continuousOn_id
  let r : ℝ := max R 1
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  apply tendstoUniformlyOn_tsum_nat_eventually (hsum r hr)
  filter_upwards [hinfty.eventually (eventually_ge_atTop r)] with n hn z hz
  have hapos : 0 < ‖a n‖ := norm_pos_iff.mpr (ha n)
  have hzr : ‖z‖ ≤ r := (hR z hz).trans (le_max_left _ _)
  have hz1 : ‖z / a n‖ ≤ 1 := by
    rw [norm_div, div_le_one hapos]
    exact hzr.trans hn
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact (norm_one_sub_elementaryFactor_le (p n) (z / a n) hz1).trans
    (pow_le_pow_left₀ (norm_nonneg (z / a n))
      (by rw [norm_div]; exact div_le_div_of_nonneg_right hzr hapos.le) (p n + 1))

/-- The entire product and multiplicities in 15.9, with repetitions of the
sequence counted by the natural sum of their indicator functions. -/
theorem entire_primary_product {a : ℕ → ℂ} {p : ℕ → ℕ}
    (ha : ∀ n, a n ≠ 0) (hinfty : Tendsto (fun n ↦ ‖a n‖) atTop atTop)
    (hsum : ∀ r : ℝ, 0 < r → Summable (fun n ↦ (r / ‖a n‖) ^ (p n + 1))) :
    let f := fun z ↦ ∏' n, elementaryFactor (p n) (z / a n)
    TendstoLocallyUniformlyOn
      (fun N z ↦ ∏ n ∈ range N, elementaryFactor (p n) (z / a n)) f atTop Set.univ ∧
    Differentiable ℂ f ∧
    ∀ z, (f z = 0 ↔ ∃ n, z = a n) ∧
      analyticOrderAt f z ≠ ⊤ ∧
      analyticOrderNatAt f z = ∑' n, if z = a n then (1 : ℕ) else 0 := by
  let F : ℕ → ℂ → ℂ := fun n z ↦ elementaryFactor (p n) (z / a n)
  have hF : ∀ n, DifferentiableOn ℂ (F n) Set.univ := by
    intro n
    exact ((differentiable_elementaryFactor (p n)).comp
      (differentiable_id.div_const (a n))).differentiableOn
  have hnonzero : ∀ n z, z ∈ (Set.univ : Set ℂ) →
      ∃ w ∈ connectedComponentIn Set.univ z, F n w ≠ 0 := by
    intro n z _
    refine ⟨0, by simp [connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ], ?_⟩
    simp [F, elementaryFactor, elementaryExponent]
  have herr := primary_errors_locally_uniform ha hinfty hsum
  obtain ⟨hlim, hhol, horder⟩ := holomorphic_product_multiplicity
    isOpen_univ hF hnonzero ⟨_, herr⟩
  refine ⟨hlim, differentiableOn_univ.mp hhol, ?_⟩
  intro z
  obtain ⟨_, hfinite, hm, _⟩ := horder z (Set.mem_univ z)
  have hsz : Summable (fun n ↦ ‖1 - F n z‖) :=
    ((hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ norm_nonneg _) _).2
      (herr.tendsto_at (Set.mem_univ z))).summable
  have hzero : (∏' n, F n z) = 0 ↔ ∃ n, z = a n := by
    constructor
    · intro hz
      by_contra h
      push_neg at h
      have hnone : ∀ n, F n z ≠ 0 := by
        intro n
        simpa [F, elementaryFactor_eq_zero_iff, div_eq_one_iff_eq (ha n)] using h n
      have hone : ∀ n, 1 + (F n z - 1) = F n z := by intro n; ring
      have hnorm : Summable (fun n ↦ ‖F n z - 1‖) := by simpa only [norm_sub_rev] using hsz
      have hn := tprod_one_add_ne_zero_of_summable
        (fun n ↦ by simpa only [hone] using hnone n) hnorm
      exact hn (by simpa only [hone] using hz)
    · rintro ⟨n, hz⟩
      exact tprod_of_exists_eq_zero ⟨n, by simp [F, hz, ha n]⟩
  refine ⟨hzero, hfinite, ?_⟩
  rw [hm]
  apply tsum_congr
  intro n
  simp only [F, analyticOrderNatAt, analyticOrderAt_scaled_elementaryFactor (p n) (ha n)]
  split_ifs <;> simp

/-- Finite and empty products obey the same entire-function and zero-count
conventions used in 15.9–15.10. -/
theorem finite_primary_product {ι : Type*} (s : Finset ι) (a : ι → ℂ) (p : ι → ℕ)
    (ha : ∀ n ∈ s, a n ≠ 0) :
    let f := fun z ↦ ∏ n ∈ s, elementaryFactor (p n) (z / a n)
    Differentiable ℂ f ∧ f 0 = 1 ∧
      ∀ z, (f z = 0 ↔ ∃ n ∈ s, z = a n) ∧
        analyticOrderAt f z = ∑ n ∈ s, if z = a n then (1 : ℕ∞) else 0 := by
  classical
  have hd (n : ι) : Differentiable ℂ (fun z ↦ elementaryFactor (p n) (z / a n)) :=
    (differentiable_elementaryFactor (p n)).comp (differentiable_id.div_const (a n))
  refine ⟨Differentiable.fun_finsetProd (fun n _ ↦ hd n), ?_, ?_⟩
  · simp [elementaryFactor, elementaryExponent]
  · intro z
    constructor
    · rw [Finset.prod_eq_zero_iff]
      constructor
      · rintro ⟨n, hn, hz⟩
        exact ⟨n, hn, (div_eq_one_iff_eq (ha n hn)).1
          ((elementaryFactor_eq_zero_iff (p n) (z / a n)).1 hz)⟩
      · rintro ⟨n, hn, hz⟩
        refine ⟨n, hn, (elementaryFactor_eq_zero_iff (p n) (z / a n)).2 ?_⟩
        exact (div_eq_one_iff_eq (ha n hn)).2 hz
    · rw [analyticOrderAt_finset_product s (fun n _ ↦ (hd n).analyticAt z)]
      apply Finset.sum_congr rfl
      intro n hn
      exact analyticOrderAt_scaled_elementaryFactor (p n) (ha n hn) z

#print axioms finite_primary_product
#print axioms summable_primary_majorant_nat
#print axioms primary_errors_locally_uniform
#print axioms entire_primary_product

end RudinRCA.Chapter15
