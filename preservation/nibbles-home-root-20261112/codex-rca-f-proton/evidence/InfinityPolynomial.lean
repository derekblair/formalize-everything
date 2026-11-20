import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set Metric Filter
open scoped Topology

namespace RudinRCA.Chapter13

/-- Cauchy's estimates show that every Taylor coefficient above an exterior polynomial
    growth bound vanishes. -/
theorem iteratedDeriv_zero_of_exterior_growth {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (n : ℕ) (C R : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ n)
    (k : ℕ) (hk : n < k) : iteratedDeriv k f 0 = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, hr⟩ := exists_gt (max (max R 1) ((k.factorial : ℝ) * C / ε))
  have hrR : R < r := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hr
  have hr1 : 1 < r := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hr
  have hr0 : 0 < r := lt_trans zero_lt_one hr1
  have hrε : (k.factorial : ℝ) * C / ε < r := lt_of_le_of_lt (le_max_right _ _) hr
  have hce := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    k hr0 hf.diffContOnCl (C := C * r ^ n) (c := 0) (fun z hz ↦ by
      have hz' : ‖z‖ = r := by simpa [mem_sphere_iff_norm] using hz
      simpa [hz'] using hbound z (by rw [hz']; exact hrR.le))
  have hpow : r ^ n ≤ r ^ (k - 1) := pow_le_pow_right₀ hr1.le (by omega)
  have hk1 : k - 1 + 1 = k := by omega
  have hratio : (k.factorial : ℝ) * (C * r ^ n) / r ^ k ≤
      (k.factorial : ℝ) * C / r := by
    apply (div_le_div_iff₀ (pow_pos hr0 k) hr0).2
    calc
      (k.factorial : ℝ) * (C * r ^ n) * r ≤
          (k.factorial : ℝ) * (C * r ^ (k - 1)) * r :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hC)
            (Nat.cast_nonneg _)) hr0.le
      _ = (k.factorial : ℝ) * C * (r ^ (k - 1) * r) := by ring
      _ = (k.factorial : ℝ) * C * r ^ k := by rw [← pow_succ, hk1]
  have hsmall : (k.factorial : ℝ) * C / r < ε := by
    apply (div_lt_iff₀ hr0).2
    have := (div_lt_iff₀ hε).1 hrε
    linarith
  simpa only [zero_add] using le_of_lt (lt_of_le_of_lt (hce.trans hratio) hsmall)

/-- An entire function with an exterior polynomial growth bound is a polynomial. -/
theorem exists_polynomial_of_exterior_growth {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (n : ℕ) (C R : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ n) :
    ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z := by
  classical
  let p : Polynomial ℂ := ∑ k ∈ Finset.range (n + 1),
    Polynomial.C ((k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0) * Polynomial.X ^ k
  refine ⟨p, fun z ↦ ?_⟩
  have ht := Complex.taylorSeries_eq_of_entire' 0 z hf
  rw [tsum_eq_sum (s := Finset.range (n + 1))] at ht
  · simpa [p, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] using ht.symm
  · intro k hk
    have hnk : n < k := by simpa using hk
    rw [iteratedDeriv_zero_of_exterior_growth hf n C R hC hbound k hnk]
    simp

/-- Meromorphic behavior in the inverted coordinate bounds an entire function by
    a polynomial outside a sufficiently large circle. -/
theorem exterior_growth_of_meromorphicAt_inversion {f : ℂ → ℂ}
    (hm : MeromorphicAt (fun z ↦ f z⁻¹) 0) :
    ∃ (n : ℕ) (C R : ℝ), 0 ≤ C ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ n := by
  obtain ⟨n, hn⟩ := hm
  let g : ℂ → ℂ := fun z ↦ z ^ n * f z⁻¹
  have hg : AnalyticAt ℂ g 0 := by simpa [g, sub_zero, smul_eq_mul] using hn
  have hb : ∀ᶠ z in 𝓝 (0 : ℂ), ‖g z‖ < ‖g 0‖ + 1 :=
    hg.continuousAt.norm.tendsto.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨δ, hδ, hδg⟩ := Metric.eventually_nhds_iff.mp hb
  refine ⟨n, ‖g 0‖ + 1, 2 / δ, by positivity, ?_⟩
  intro z hz
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (div_pos (by norm_num) hδ) hz
  have hzi : dist z⁻¹ 0 < δ := by
    rw [dist_zero_right, norm_inv, inv_eq_one_div, div_lt_iff₀ hzpos]
    have := (div_le_iff₀ hδ).1 hz
    nlinarith
  have hi : ‖z‖⁻¹ ^ n * ‖f z‖ ≤ ‖g 0‖ + 1 := by
    simpa only [g, norm_mul, norm_pow, norm_inv, inv_inv] using (hδg hzi).le
  have hi' := mul_le_mul_of_nonneg_left hi (le_of_lt (pow_pos hzpos n))
  simpa [← mul_assoc, ← mul_pow, ne_of_gt hzpos, mul_comm] using hi'

/-- An entire function which is meromorphic at infinity is a polynomial. -/
theorem exists_polynomial_of_entire_meromorphicAt_inversion {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hm : MeromorphicAt (fun z ↦ f z⁻¹) 0) :
    ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z := by
  obtain ⟨n, C, R, hC, hbound⟩ := exterior_growth_of_meromorphicAt_inversion hm
  exact exists_polynomial_of_exterior_growth hf n C R hC hbound

/-- Every entire nonpolynomial has an essential singularity at infinity, where
    essential means that the inverted coordinate is not meromorphic at zero. -/
theorem not_meromorphicAt_inversion_of_entire_nonpolynomial {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hnp : ¬∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) :
    ¬ MeromorphicAt (fun z ↦ f z⁻¹) 0 := by
  intro hm
  exact hnp (exists_polynomial_of_entire_meromorphicAt_inversion hf hm)

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.exists_polynomial_of_entire_meromorphicAt_inversion
#print axioms RudinRCA.Chapter13.not_meromorphicAt_inversion_of_entire_nonpolynomial
