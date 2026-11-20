import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
Scratch development of Rudin RCA 13.11 (e) implies (f).
In the aggregate, this file follows PrimitiveCurveIntegral.lean.
The path class permits arbitrary finite C¹ partitions of [0,1].
-/

open Set Polynomial Filter MeasureTheory
open scoped Topology

namespace RudinRCA.Chapter13

theorem intervalIntegrable_deriv_of_piecewiseC1Path {a b : ℂ} {γ : Path a b}
    (hγ : IsPiecewiseC1Path γ) : IntervalIntegrable (deriv γ.extend) volume 0 1 := by
  obtain ⟨n, t, ht, ht0, htn, hpieces⟩ := hγ
  have h := IntervalIntegrable.trans_iterate fun k hk =>
    intervalIntegrable_deriv_of_contDiffOn_interval (hpieces k hk) (ht (Nat.le_succ k))
  simpa only [ht0, htn] using h

/-- Every complex polynomial has zero integral over a closed piecewise C¹ path. -/
theorem polynomial_curveIntegral_closed_eq_zero (P : ℂ[X]) {a : ℂ} (γ : Path a a)
    (hγ : IsPiecewiseC1Path γ) :
    curveIntegral (fun z => P.eval z • ContinuousLinearMap.id ℂ ℂ) γ = 0 := by
  obtain ⟨F, hF⟩ := (convex_univ : Convex ℝ (Set.univ : Set ℂ)).exists_forall_hasDerivWithinAt
    P.differentiable.differentiableOn
  have hder (z : ℂ) : HasDerivAt F (P.eval z) z := (hF z (Set.mem_univ z)).hasDerivAt univ_mem
  have hFD : DifferentiableOn ℂ F Set.univ :=
    fun z _ => (hder z).differentiableAt.differentiableWithinAt
  rw [curveIntegral_eq_sub_of_primitive isOpen_univ hFD
    (fun z _ => (hder z).deriv) γ (fun z => Set.mem_univ _) hγ]
  exact sub_self _

/-- Uniform approximation just on the compact trace of a closed path is
sufficient to force its integral to vanish. -/
theorem curveIntegral_closed_eq_zero_of_polynomial_approximation {a : ℂ}
    (γ : Path a a) (hγ : IsPiecewiseC1Path γ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.range γ))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ P : ℂ[X],
      ∀ z ∈ Set.range γ, ‖f z - P.eval z‖ < ε) :
    curveIntegral (fun z => f z • ContinuousLinearMap.id ℂ ℂ) γ = 0 := by
  have htrace (s : ℝ) : γ.extend s ∈ Set.range γ := by
    rw [← γ.extend_range]
    exact Set.mem_range_self s
  have hγint := intervalIntegrable_deriv_of_piecewiseC1Path hγ
  have hfint : IntervalIntegrable (fun t => f (γ.extend t) * deriv γ.extend t) volume 0 1 :=
    hγint.continuousOn_mul (hf.comp γ.extend.continuous.continuousOn (fun t _ => htrace t))
  let L : ℝ := ∫ t in (0 : ℝ)..1, ‖deriv γ.extend t‖
  have hL : 0 ≤ L := intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => norm_nonneg _)
  let I : ℂ := curveIntegral (fun z => f z • ContinuousLinearMap.id ℂ ℂ) γ
  by_contra hI
  have hIpos : 0 < ‖I‖ := norm_pos_iff.mpr hI
  let ε : ℝ := ‖I‖ / (L + 1)
  have hε : 0 < ε := div_pos hIpos (by linarith)
  obtain ⟨P, hP⟩ := happrox ε hε
  have hPint : IntervalIntegrable (fun t => P.eval (γ.extend t) * deriv γ.extend t) volume 0 1 :=
    hγint.continuousOn_mul (P.continuous.comp γ.extend.continuous).continuousOn
  have hPzero : (∫ t in (0 : ℝ)..1, P.eval (γ.extend t) * deriv γ.extend t) = 0 := by
    simpa only [curveIntegral_eq_intervalIntegral_deriv, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul] using polynomial_curveIntegral_closed_eq_zero P γ hγ
  have hsub : (∫ t in (0 : ℝ)..1, (f (γ.extend t) - P.eval (γ.extend t)) * deriv γ.extend t) = I := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub hfint hPint, hPzero, sub_zero]
    simp only [I, curveIntegral_eq_intervalIntegral_deriv, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
  have hbound : ‖I‖ ≤ ε * L := by
    rw [← hsub]
    calc
      ‖∫ t in (0 : ℝ)..1, (f (γ.extend t) - P.eval (γ.extend t)) * deriv γ.extend t‖ ≤
          ∫ t in (0 : ℝ)..1, ε * ‖deriv γ.extend t‖ := by
        apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
        · exact Filter.Eventually.of_forall fun t _ => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (hP (γ.extend t) (htrace t)).le (norm_nonneg _)
        · exact hγint.norm.const_mul ε
      _ = ε * L := by rw [intervalIntegral.integral_const_mul]; rfl
  have heq : ε * (L + 1) = ‖I‖ := div_mul_cancel₀ _ (by linarith : L + 1 ≠ 0)
  nlinarith

/-- Rudin 13.11 (e) implies (f): compactwise uniform polynomial approximation
of a holomorphic function makes every closed piecewise C¹ path integral zero. -/
theorem compact_polynomial_approximation_implies_zero_closed_integrals {Ω : Set ℂ}
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (happrox : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ P : ℕ → ℂ[X], TendstoUniformlyOn (fun n z => (P n).eval z) f atTop K)
    {a : ℂ} (γ : Path a a) (hγΩ : ∀ t, γ t ∈ Ω) (hγ : IsPiecewiseC1Path γ) :
    curveIntegral (fun z => f z • ContinuousLinearMap.id ℂ ℂ) γ = 0 := by
  have hsubset : Set.range γ ⊆ Ω := by
    rintro z ⟨t, rfl⟩
    exact hγΩ t
  apply curveIntegral_closed_eq_zero_of_polynomial_approximation γ hγ (hf.continuousOn.mono hsubset)
  intro ε hε
  obtain ⟨P, hP⟩ := happrox (Set.range γ) (isCompact_range γ.continuous) hsubset
  obtain ⟨n, hn⟩ := ((Metric.tendstoUniformlyOn_iff.mp hP) ε hε).exists
  refine ⟨P n, fun z hz => ?_⟩
  simpa only [dist_eq_norm] using hn z hz

#print axioms intervalIntegrable_deriv_of_piecewiseC1Path
#print axioms polynomial_curveIntegral_closed_eq_zero
#print axioms curveIntegral_closed_eq_zero_of_polynomial_approximation
#print axioms compact_polynomial_approximation_implies_zero_closed_integrals

end RudinRCA.Chapter13
