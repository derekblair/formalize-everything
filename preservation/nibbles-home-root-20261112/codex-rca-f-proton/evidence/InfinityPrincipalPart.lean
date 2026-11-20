import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Piecewise
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring

open Filter Set Function
open scoped Topology BigOperators

namespace RudinRCA.Chapter13Scratch

noncomputable def inversePrincipalPolynomial (m : ℕ) (a : ℕ → ℂ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range m, Polynomial.monomial (m - i) (a i)

theorem inversePrincipalPolynomial_natDegree {m : ℕ} (hm : 0 < m)
    {a : ℕ → ℂ} (ha : a 0 ≠ 0) :
    (inversePrincipalPolynomial m a).natDegree = m := by
  have hle : (inversePrincipalPolynomial m a).natDegree ≤ m := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_monomial_le (a i)).trans (Nat.sub_le m i)
  have hc : (inversePrincipalPolynomial m a).coeff m = a 0 := by
    simp only [inversePrincipalPolynomial, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i hi hi0
      have hne : m - i ≠ m := by omega
      simp [Polynomial.coeff_monomial, hne]
    · simp [hm]
  exact hle.antisymm (Polynomial.le_natDegree_of_ne_zero (by rwa [hc]))

theorem inversePrincipalPolynomial_coeff_zero (m : ℕ) (a : ℕ → ℂ) :
    (inversePrincipalPolynomial m a).coeff 0 = 0 := by
  simp only [inversePrincipalPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i < m := Finset.mem_range.mp hi
  have hne : m - i ≠ 0 := by omega
  simp [Polynomial.coeff_monomial, hne]

theorem inversePrincipalPolynomial_eval {m : ℕ} {a : ℕ → ℂ}
    {z : ℂ} (hz : z ≠ 0) :
    z ^ m * (inversePrincipalPolynomial m a).eval z⁻¹ =
      ∑ i ∈ Finset.range m, a i * z ^ i := by
  simp only [inversePrincipalPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inv_pow_sub₀ hz (Nat.le_of_lt (Finset.mem_range.mp hi))]
  calc
    z ^ m * (a i * ((z ^ m)⁻¹ * z ^ i)) =
        a i * (z ^ m * ((z ^ m)⁻¹ * z ^ i)) := by ring
    _ = a i * z ^ i := by rw [mul_inv_cancel_left₀ (pow_ne_zero m hz)]

/-- Exact principal-part degree for a pole at infinity, RCA 13.1.
The removable remainder is represented in the inverse coordinate with an explicit value update. -/
theorem polynomial_principal_part_at_infinity
    {f : ℂ → ℂ} {m : ℕ} (hm : 0 < m)
    (hf : MeromorphicAt (fun z : ℂ => f z⁻¹) 0)
    (ho : meromorphicOrderAt (fun z : ℂ => f z⁻¹) 0 = ((-(m : ℤ)) : WithTop ℤ)) :
    ∃ p : Polynomial ℂ, p.natDegree = m ∧ p.coeff 0 = 0 ∧
      ∃ c : ℂ, AnalyticAt ℂ
        (Function.update (fun z : ℂ => f z⁻¹ - p.eval z⁻¹) 0 c) 0 := by
  classical
  obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp ho
  obtain ⟨F, hF, hTaylor⟩ := hg.exists_eq_sum_add_pow_mul m
  let a : ℕ → ℂ := fun i => iteratedDeriv i g 0 / (i.factorial : ℂ)
  let p := inversePrincipalPolynomial m a
  have ha0 : a 0 ≠ 0 := by simpa [a] using hg0
  refine ⟨p, inversePrincipalPolynomial_natDegree hm ha0,
    inversePrincipalPolynomial_coeff_zero m a, F 0, ?_⟩
  have hrem : (fun z : ℂ => f z⁻¹ - p.eval z⁻¹) =ᶠ[𝓝[≠] 0] F := by
    filter_upwards [hfg, self_mem_nhdsWithin] with z hz hz0
    have hpoly : z ^ m * p.eval z⁻¹ =
        ∑ i ∈ Finset.range m, (z ^ i / (i.factorial : ℂ)) * iteratedDeriv i g 0 := by
      rw [inversePrincipalPolynomial_eval hz0]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [a]
      ring
    have hT := hTaylor z
    simp only [smul_eq_mul] at hT
    rw [← hpoly] at hT
    simp only [sub_zero, smul_eq_mul, zpow_neg, zpow_natCast] at hz
    rw [hz, hT, ← mul_add, inv_mul_cancel_left₀ (pow_ne_zero m hz0), add_sub_cancel_left]
  apply hF.congr
  filter_upwards [eventually_nhdsWithin_iff.mp hrem] with z hz
  by_cases hz0 : z = 0
  · simp [hz0]
  · rw [Function.update_of_ne hz0]
    exact (hz hz0).symm

/-- The same principal part also gives a finite limit for the remainder at infinity. -/
theorem polynomial_principal_part_at_infinity_with_limit
    {f : ℂ → ℂ} {m : ℕ} (hm : 0 < m)
    (hf : MeromorphicAt (fun z : ℂ => f z⁻¹) 0)
    (ho : meromorphicOrderAt (fun z : ℂ => f z⁻¹) 0 = ((-(m : ℤ)) : WithTop ℤ)) :
    ∃ p : Polynomial ℂ, p.natDegree = m ∧ p.coeff 0 = 0 ∧
      ∃ c : ℂ, AnalyticAt ℂ
        (Function.update (fun z : ℂ => f z⁻¹ - p.eval z⁻¹) 0 c) 0 ∧
        Tendsto (fun z : ℂ => f z - p.eval z) (cocompact ℂ) (𝓝 c) := by
  obtain ⟨p, hdegree, hzero, c, hA⟩ := polynomial_principal_part_at_infinity hm hf ho
  refine ⟨p, hdegree, hzero, c, hA, ?_⟩
  have hlim := continuousAt_update_same.mp hA.continuousAt
  have h := hlim.comp (tendsto_inv₀_cobounded' (α := ℂ))
  simpa only [Function.comp_def, inv_inv, Metric.cobounded_eq_cocompact] using h

#print axioms inversePrincipalPolynomial_natDegree
#print axioms inversePrincipalPolynomial_coeff_zero
#print axioms inversePrincipalPolynomial_eval
#print axioms polynomial_principal_part_at_infinity
#print axioms polynomial_principal_part_at_infinity_with_limit

end RudinRCA.Chapter13Scratch
