import MittagLefflerInfinityWork
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
Local algebra for 15.13. Taylor's theorem extracts the finite principal part of
an analytic germ divided by a finite-order analytic denominator. Realizing these
principal parts by the constructed Mittag-Leffler series then gives interpolation
after holomorphic regularization. No global interpolation premise is used here.

Draft: awaiting the serialized Lean check.
-/

noncomputable section
open Filter Finset Set
open scoped Topology

namespace RudinRCA.Chapter15

/-- The polynomial obtained by reversing the first k Taylor coefficients. -/
def reciprocalTaylorPolynomial (v : ℂ → ℂ) (k : ℕ) : Polynomial ℂ :=
  ∑ i ∈ range k, Polynomial.monomial (k - i) (iteratedDeriv i v 0 / i.factorial)

theorem reciprocalTaylorPolynomial_mul_pow (v : ℂ → ℂ) (k : ℕ)
    {x : ℂ} (hx : x ≠ 0) :
    x ^ k * (reciprocalTaylorPolynomial v k).eval (1 / x) =
      ∑ i ∈ range k, (x ^ i / i.factorial) * iteratedDeriv i v 0 := by
  simp only [reciprocalTaylorPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := (mem_range.mp hi).le
  have hp : x ^ k * (1 / x) ^ (k - i) = x ^ i := by
    rw [one_div, inv_pow, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ hx)]
    rw [← pow_add, Nat.add_sub_of_le hik]
  calc
    x ^ k * (iteratedDeriv i v 0 / i.factorial * (1 / x) ^ (k - i)) =
        (x ^ k * (1 / x) ^ (k - i)) * (iteratedDeriv i v 0 / i.factorial) := by ring
    _ = (x ^ i / i.factorial) * iteratedDeriv i v 0 := by rw [hp]; ring

/-- Every quotient of analytic germs by a finite-order denominator has a finite
polynomial principal part and an analytic remainder. Equality is on a punctured
neighborhood, so no arbitrary scalar value at the pole is misinterpreted. -/
theorem analytic_quotient_has_polynomial_principal_part
    {G h : ℂ → ℂ} {a : ℂ} {k : ℕ}
    (hG : AnalyticAt ℂ G a) (hh : AnalyticAt ℂ h a)
    (horder : analyticOrderAt h a = (k : ℕ∞)) :
    ∃ P : Polynomial ℂ, ∃ R : ℂ → ℂ, AnalyticAt ℂ R a ∧
      (fun z ↦ G z / h z) =ᶠ[𝓝[≠] a]
        (fun z ↦ P.eval (1 / (z - a)) + R z) := by
  obtain ⟨u, hua, hua0, hhu⟩ := hh.analyticOrderAt_eq_natCast.mp horder
  let v : ℂ → ℂ := fun w ↦ G (w + a) / u (w + a)
  have hva : AnalyticAt ℂ v 0 := by
    exact (hG.div hua hua0).comp_of_eq (analyticAt_id.add analyticAt_const) (by simp)
  obtain ⟨r, hra, hTaylor⟩ := hva.exists_eventuallyEq_sum_add_pow_mul k
  let R : ℂ → ℂ := fun z ↦ r (z - a)
  have hRa : AnalyticAt ℂ R a :=
    hra.comp_of_eq (analyticAt_id.sub analyticAt_const) (by simp)
  refine ⟨reciprocalTaylorPolynomial v k, R, hRa, ?_⟩
  have hTaylor' : ∀ᶠ z in 𝓝 a,
      G z / u z =
        (∑ i ∈ range k, ((z - a) ^ i / i.factorial) * iteratedDeriv i v 0) +
          (z - a) ^ k * R z := by
    have htrans : Tendsto (fun z : ℂ ↦ z - a) (𝓝 a) (𝓝 0) := by
      simpa using (continuousAt_id.sub_const a : ContinuousAt (fun z : ℂ ↦ z - a) a).tendsto
    simpa only [v, R, sub_add_cancel, smul_eq_mul] using htrans.eventually hTaylor
  filter_upwards [self_mem_nhdsWithin,
    hhu.filter_mono nhdsWithin_le_nhds,
    hTaylor'.filter_mono nhdsWithin_le_nhds,
    (hua.continuousAt.eventually_ne hua0).filter_mono nhdsWithin_le_nhds]
      with z hza hhz ht huz
  have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
  change h z = (z - a) ^ k * u z at hhz
  have hhz0 : h z ≠ 0 := by rw [hhz]; exact mul_ne_zero (pow_ne_zero _ hza') huz
  have hv : G z / u z = (z - a) ^ k *
      ((reciprocalTaylorPolynomial v k).eval (1 / (z - a)) + R z) := by
    rw [mul_add, reciprocalTaylorPolynomial_mul_pow v k hza']
    exact ht
  apply (div_eq_iff hhz0).2
  rw [hhz, (div_eq_iff huz).1 hv]
  ring

/-- Normal-form regularization agrees in an ordinary neighborhood with any
analytic germ representing the same meromorphic function there. -/
theorem regularization_eq_analytic_germ {Ω : Set ℂ} {f V : ℂ → ℂ} {a : ℂ}
    (hf : MeromorphicOn f Ω) (ha : a ∈ Ω) (hV : AnalyticAt ℂ V a)
    (heq : f =ᶠ[𝓝[≠] a] V) :
    toMeromorphicNFOn f Ω =ᶠ[𝓝 a] V := by
  have h := (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf ha).trans
    (toMeromorphicNFAt_eventuallyEq_nhds_congr heq)
  rwa [toMeromorphicNFAt_eq_self.mpr hV.meromorphicNFAt] at h

/-- If M has the principal part of G/h, then regularizing h*M produces an
analytic germ whose error from G is divisible by h. This is the local step that
turns the actual Mittag-Leffler construction into arbitrary finite jets. -/
theorem interpolation_from_matching_principal_part
    {Ω : Set ℂ} {G h M : ℂ → ℂ} {a : ℂ} {k : ℕ}
    (ha : a ∈ Ω) (hG : AnalyticAt ℂ G a) (hh : AnalyticAt ℂ h a)
    (hprod : MeromorphicOn (fun z ↦ h z * M z) Ω)
    (horder : analyticOrderAt h a = (k : ℕ∞))
    (P : Polynomial ℂ) (R : ℂ → ℂ) (hR : AnalyticAt ℂ R a)
    (hprincipal : (fun z ↦ G z / h z) =ᶠ[𝓝[≠] a]
      (fun z ↦ P.eval (1 / (z - a)) + R z))
    (hM : AnalyticAt ℂ (fun z ↦ M z - P.eval (1 / (z - a))) a) :
    let H := toMeromorphicNFOn (fun z ↦ h z * M z) Ω
    AnalyticAt ℂ H a ∧
      (k : ℕ∞) ≤ analyticOrderAt (fun z ↦ H z - G z) a := by
  let D : ℂ → ℂ := fun z ↦ M z - P.eval (1 / (z - a)) - R z
  have hD : AnalyticAt ℂ D a := hM.sub hR
  let V : ℂ → ℂ := fun z ↦ G z + h z * D z
  have hV : AnalyticAt ℂ V a := hG.add (hh.mul hD)
  obtain ⟨u, hua, hua0, hhu⟩ := hh.analyticOrderAt_eq_natCast.mp horder
  have hnonzero : ∀ᶠ z in 𝓝[≠] a, h z ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, hhu.filter_mono nhdsWithin_le_nhds,
      (hua.continuousAt.eventually_ne hua0).filter_mono nhdsWithin_le_nhds]
      with z hza hhz huz
    simpa only [hhz, smul_eq_mul] using mul_ne_zero (pow_ne_zero k (sub_ne_zero.mpr hza)) huz
  have heq : (fun z ↦ h z * M z) =ᶠ[𝓝[≠] a] V := by
    filter_upwards [hprincipal, hnonzero] with z hz hhz
    have hGz := (div_eq_iff hhz).1 hz
    dsimp [V, D]
    rw [hGz]
    ring
  have hHV := regularization_eq_analytic_germ hprod ha hV heq
  have hH := hV.congr hHV.symm
  refine ⟨hH, (natCast_le_analyticOrderAt (hH.sub hG)).2 ?_⟩
  refine ⟨fun z ↦ u z * D z, hua.mul hD, ?_⟩
  filter_upwards [hHV, hhu] with z hz hhz
  rw [hz]
  dsimp only [V]
  rw [hhz]
  simp only [smul_eq_mul]
  ring

#print axioms reciprocalTaylorPolynomial_mul_pow
#print axioms analytic_quotient_has_polynomial_principal_part
#print axioms regularization_eq_analytic_germ
#print axioms interpolation_from_matching_principal_part

end RudinRCA.Chapter15
