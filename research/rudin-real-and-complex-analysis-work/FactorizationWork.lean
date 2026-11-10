import RudinRCA.Chapter15

/-!
Assembly of 15.10 after the separately checked EntireLogWork and EntireProductWork
prerequisites have been integrated into Chapter15. This draft intentionally imports
the final module interface rather than copying those proofs.
-/

open Filter Finset
open scoped Topology
noncomputable section

namespace RudinRCA.Chapter15

/-- The convention following 15.10: remove the finite-order zero at the origin
before applying the nonvanishing-at-zero factorization statement. -/
theorem entire_remove_zero_at_origin {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ h 0 ≠ 0 ∧
      ∀ z, f z = z ^ analyticOrderNatAt f 0 * h z := by
  have hfinite : analyticOrderAt f 0 ≠ ⊤ := by
    intro htop
    exact hne ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0 hf.analyticAt).mp htop)
  obtain ⟨g, hga, hg0, heq⟩ := (hf.analyticAt 0).analyticOrderAt_ne_top.mp hfinite
  let k := analyticOrderNatAt f 0
  let h : ℂ → ℂ := fun z ↦ if z = 0 then g 0 else f z / z ^ k
  have heq' : f =ᶠ[𝓝 0] fun z ↦ z ^ k * g z := by
    simpa only [sub_zero, smul_eq_mul] using heq
  have hnear : h =ᶠ[𝓝 0] g := by
    filter_upwards [heq'] with z hz
    by_cases hz0 : z = 0
    · simp [h, hz0]
    · simp [h, hz0, hz, mul_div_cancel_left₀, pow_ne_zero _ hz0]
  have hh : Differentiable ℂ h := by
    intro z
    by_cases hz0 : z = 0
    · subst z
      exact (hga.congr hnear.symm).differentiableAt
    · apply AnalyticAt.differentiableAt
      apply ((hf.analyticAt z).div (analyticAt_id.pow k) (pow_ne_zero _ hz0)).congr
      filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
      simp [h, hw]
  refine ⟨h, hh, by simpa [h] using hg0, ?_⟩
  intro z
  by_cases hz0 : z = 0
  · subst z
    simpa only [h, if_pos rfl] using heq'.eq_of_nhds
  · dsimp only [h]
    rw [if_neg hz0]
    exact (mul_div_cancel₀ (f z) (pow_ne_zero k hz0)).symm

/-- Theorem 15.10 for an infinite sequence listing all zeros with multiplicity.
`HasSum` records actual finite multiplicities, and escape to infinity is derived.
With zero-based indexing the admissible choice is `p n = n`. -/
theorem entire_function_factorization_infinite {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (ha : ∀ n, f (a n) = 0)
    (hcount : ∀ z, HasSum (fun n ↦ if a n = z then (1 : ℕ) else 0)
      (analyticOrderNatAt f z)) :
    ∃ p : ℕ → ℕ, ∃ g : ℂ → ℂ,
      p = (fun n ↦ n) ∧ Differentiable ℂ g ∧
      TendstoLocallyUniformlyOn
        (fun N z ↦ ∏ n ∈ range N, elementaryFactor (p n) (z / a n))
        (fun z ↦ ∏' n, elementaryFactor (p n) (z / a n)) atTop Set.univ ∧
      ∀ z, f z = Complex.exp (g z) * ∏' n, elementaryFactor (p n) (z / a n) := by
  obtain ⟨ha0, hinfty⟩ := zero_enumeration_norm_tendsto_atTop hf h0 ha hcount
  obtain ⟨hlim, hP, hprop⟩ := entire_primary_product (p := fun n ↦ n) ha0 hinfty
    (fun r hr ↦ summable_primary_majorant_nat ha0 hinfty hr)
  have hP0 : (∏' n, elementaryFactor n (0 / a n)) ≠ 0 := by
    intro hz
    obtain ⟨n, hn⟩ := (hprop 0).1.mp hz
    exact ha0 n hn.symm
  have hm : ∀ z, analyticOrderNatAt f z =
      analyticOrderNatAt (fun w ↦ ∏' n, elementaryFactor n (w / a n)) z := by
    intro z
    rw [(hprop z).2.2]
    simpa only [eq_comm] using (hcount z).tsum_eq.symm
  obtain ⟨g, hg, heq⟩ :=
    exists_entire_exponential_factor_of_nat_order_eq hf hP h0 hP0 hm
  exact ⟨(fun n ↦ n), g, rfl, hg, hlim, heq⟩

/-- The finite and empty zero-list cases of 15.10. The primary factors may all
have genus zero, and an empty list gives the entire logarithm theorem. The finite
sum hypothesis counts every zero exactly with its multiplicity. -/
theorem entire_function_factorization_finite {ι : Type*} {f : ℂ → ℂ}
    (s : Finset ι) (a : ι → ℂ) (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (ha : ∀ n ∈ s, f (a n) = 0)
    (hcount : ∀ z, (∑ n ∈ s, if a n = z then (1 : ℕ) else 0) =
      analyticOrderNatAt f z) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ z, f z = Complex.exp (g z) * ∏ n ∈ s, elementaryFactor 0 (z / a n) := by
  classical
  have ha0 : ∀ n ∈ s, a n ≠ 0 := by
    intro n hn hzero
    exact h0 (hzero ▸ ha n hn)
  obtain ⟨hP, hP0, hprop⟩ := finite_primary_product s a (fun _ ↦ 0) ha0
  have hPne : (∏ n ∈ s, elementaryFactor 0 (0 / a n)) ≠ 0 := by
    exact hP0.trans_ne one_ne_zero
  have hfinite := analyticOrderAt_ne_top_of_entire_nonzero hP hPne
  have hfinitef := analyticOrderAt_ne_top_of_entire_nonzero hf h0
  apply exists_entire_exponential_factor_of_order_eq hf hP hfinite
  intro z
  rw [(hprop z).2, ← Nat.cast_analyticOrderNatAt (hfinitef z), ← hcount z,
    Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hz : a n = z
  · simp [hz]
  · simp [hz, Ne.symm hz]

#print axioms entire_function_factorization_infinite
#print axioms entire_function_factorization_finite
#print axioms entire_remove_zero_at_origin

end RudinRCA.Chapter15
