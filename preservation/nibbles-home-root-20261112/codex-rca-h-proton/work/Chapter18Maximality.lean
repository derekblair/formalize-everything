import Chapter18Ideals
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

noncomputable section

open Set MeasureTheory
open scoped Topology ComplexOrder Polynomial

namespace RudinRCA.Chapter18

variable {T : ℝ} [Fact (0 < T)]

/-- Normalized Haar integration, with the sup norm on continuous functions. -/
def definition18_20_meanCLM (T : ℝ) [Fact (0 < T)] :
    C(AddCircle T, ℂ) →L[ℂ] ℂ :=
  (MeasureTheory.L1.integralCLM' ℂ).comp
    (ContinuousMap.toLp 1 AddCircle.haarAddCircle ℂ)

theorem theorem18_20_meanCLM_apply (f : C(AddCircle T, ℂ)) :
    definition18_20_meanCLM T f = ∫ x, f x ∂AddCircle.haarAddCircle := by
  rw [definition18_20_meanCLM, ContinuousLinearMap.comp_apply,
    ← MeasureTheory.L1.integral_eq', MeasureTheory.L1.integral_eq_integral]
  exact integral_congr_ae
    (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 1) AddCircle.haarAddCircle f)

theorem theorem18_20_meanCLM_fourier (n : ℤ) :
    definition18_20_meanCLM T (fourier n) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := T) n) 0
  simpa [theorem18_20_meanCLM_apply, fourierCoeff,
    fourier_zero, Pi.single_apply, eq_comm] using h

theorem theorem18_20_fourier_nat (n : ℕ) :
    (fourier (n : ℤ) : C(AddCircle T, ℂ)) = fourier 1 ^ n := by
  induction n with
  | zero => ext x; simp [fourier_zero]
  | succ n ih =>
      ext x
      simp only [Nat.cast_add, Nat.cast_one, fourier_add,
        ContinuousMap.pow_apply, pow_succ]
      exact congrArg (fun f : C(AddCircle T, ℂ) => f x) ih |> fun h => congrArg (· * _) h

theorem theorem18_20_fourier_neg_nat (n : ℕ) :
    (fourier (-(n : ℤ)) : C(AddCircle T, ℂ)) = fourier (-1) ^ n := by
  induction n with
  | zero => ext x; simp [fourier_zero]
  | succ n ih =>
      have heq : -((n + 1 : ℕ) : ℤ) = -(n : ℤ) + (-1) := by omega
      ext x
      simp only [heq, fourier_add, ContinuousMap.pow_apply, pow_succ]
      exact congrArg (fun f : C(AddCircle T, ℂ) => f x) ih |> fun h => congrArg (· * _) h

/-- Both the coordinate and its inverse generate a dense algebra. -/
theorem theorem18_20_eq_top_of_fourier_one_neg_one
    (B : Subalgebra ℂ C(AddCircle T, ℂ)) (hclosed : IsClosed (B : Set C(AddCircle T, ℂ)))
    (hpos : fourier 1 ∈ B) (hneg : fourier (-1) ∈ B) : B = ⊤ := by
  have hall : ∀ n : ℤ, fourier n ∈ B := by
    intro n
    rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
    · rw [theorem18_20_fourier_nat]
      exact B.pow_mem hpos k
    · rw [theorem18_20_fourier_neg_nat]
      exact B.pow_mem hneg k
  have hspan : Submodule.span ℂ (Set.range (fourier (T := T))) ≤ B.toSubmodule :=
    Submodule.span_le.mpr (by rintro f ⟨n, rfl⟩; exact hall n)
  have htop := Submodule.topologicalClosure_minimal _ hspan hclosed
  rw [span_fourier_closure_eq_top] at htop
  exact top_unique htop

/-- The coordinate cannot be invertible in a proper closed subalgebra containing it. -/
theorem theorem18_20_coordinate_nonunit
    (B : Subalgebra ℂ C(AddCircle T, ℂ)) (hclosed : IsClosed (B : Set C(AddCircle T, ℂ)))
    (hproper : B ≠ ⊤) (hpos : fourier 1 ∈ B) :
    ¬IsUnit (⟨fourier 1, hpos⟩ : B) := by
  intro hu
  have hinv : fourier (-1) ∈ B := by
    have hprod : fourier 1 * (↑(↑hu.unit⁻¹ : B) : C(AddCircle T, ℂ)) = 1 :=
      congrArg (fun x : B => (x : C(AddCircle T, ℂ))) hu.mul_val_inv
    have hcancel : (fourier (-1) : C(AddCircle T, ℂ)) * fourier 1 = 1 := by
      ext x
      rw [ContinuousMap.mul_apply, ← fourier_add]
      simp [fourier_zero]
    have heq : fourier (-1) = (↑(↑hu.unit⁻¹ : B) : C(AddCircle T, ℂ)) := by
      calc
        fourier (-1) = fourier (-1) * 1 := (mul_one _).symm
        _ = fourier (-1) *
            (fourier 1 * (↑(↑hu.unit⁻¹ : B) : C(AddCircle T, ℂ))) := by rw [hprod]
        _ = (fourier (-1) * fourier 1) *
            (↑(↑hu.unit⁻¹ : B) : C(AddCircle T, ℂ)) := (mul_assoc _ _ _).symm
        _ = (↑(↑hu.unit⁻¹ : B) : C(AddCircle T, ℂ)) := by rw [hcancel, one_mul]
    rw [heq]
    exact (↑hu.unit⁻¹ : B).property
  exact hproper (theorem18_20_eq_top_of_fourier_one_neg_one B hclosed hpos hinv)

/-- The normalized integral is the unique norm-one functional taking 1 to 1
and killing the positive Fourier modes. -/
theorem theorem18_20_state_eq_mean
    (L : C(AddCircle T, ℂ) →L[ℂ] ℂ) (hLnorm : ‖L‖ = 1) (hLone : L 1 = 1)
    (hpos : ∀ n : ℕ, 0 < n → L (fourier (n : ℤ)) = 0) :
    L = definition18_20_meanCLM T := by
  have hmono : Monotone L := ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.mpr
    (by simp [hLnorm, hLone])
  let P : C(AddCircle T, ℂ) →P[ℂ] ℂ := { __ := L, monotone' := hmono }
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top)
  rintro f ⟨n, rfl⟩
  rw [theorem18_20_meanCLM_fourier]
  by_cases hn : n = 0
  · subst n
    have hz : (fourier 0 : C(AddCircle T, ℂ)) = 1 := by
      ext x; exact fourier_zero
    simp [hz, hLone]
  · rw [if_neg hn]
    rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
    · exact hpos k (by omega)
    · have hstar : (fourier (-(k : ℤ)) : C(AddCircle T, ℂ)) =
          star (fourier (k : ℤ)) := by
        ext x; exact fourier_neg
      rw [hstar]
      change P (star (fourier (k : ℤ))) = 0
      rw [map_star]
      change star (L (fourier (k : ℤ))) = 0
      rw [hpos k (by omega), star_zero]

/-- Core of 18.20: every member of a proper closed algebra containing the
coordinate has all its negative Fourier coefficients equal to zero. -/
theorem theorem18_20_proper_subalgebra_negative_coeff
    (B : Subalgebra ℂ C(AddCircle T, ℂ)) (hclosed : IsClosed (B : Set C(AddCircle T, ℂ)))
    (hproper : B ≠ ⊤) (hpos : fourier 1 ∈ B)
    (g : B) (n : ℤ) (hn : n < 0) : fourierCoeff (g : C(AddCircle T, ℂ)) n = 0 := by
  letI : CompleteSpace B := hclosed.isComplete.completeSpace_coe
  letI : NormOneClass B :=
    ⟨show ‖(1 : C(AddCircle T, ℂ))‖ = 1 from norm_one⟩
  let z : B := ⟨fourier 1, hpos⟩
  obtain ⟨χ, hχz⟩ := theorem18_17_nonunit_character
    (theorem18_20_coordinate_nonunit B hclosed hproper hpos)
  let χa := definition18_16_characterAlgHom χ
  let χL : B.toSubmodule →L[ℂ] ℂ := χa.toContinuousLinearMap
  obtain ⟨L, hL, hLnorm⟩ := exists_extension_norm_eq B.toSubmodule χL
  have hnorm : ‖L‖ = 1 := hLnorm.trans (theorem18_17_character_norm χ)
  have hone : L 1 = 1 := by
    simpa [χL, χa] using hL (1 : B)
  have hpositive : ∀ k : ℕ, 0 < k → L (fourier (k : ℤ)) = 0 := by
    intro k hk
    rw [theorem18_20_fourier_nat]
    have hh := hL (z ^ k)
    change L (fourier 1 ^ k) = χa (z ^ k) at hh
    rw [hh, map_pow]
    change χ.val z ^ k = 0
    rw [hχz, zero_pow (Nat.ne_of_gt hk)]
  have hmean := theorem18_20_state_eq_mean L hnorm hone hpositive
  obtain ⟨k, hk⟩ : ∃ k : ℕ, -n = (k : ℤ) := ⟨(-n).toNat, by omega⟩
  have hkpos : 0 < k := by omega
  have hcoeff : fourierCoeff (g : C(AddCircle T, ℂ)) n =
      definition18_20_meanCLM T ((g : C(AddCircle T, ℂ)) * fourier (k : ℤ)) := by
    rw [theorem18_20_meanCLM_apply, fourierCoeff, hk]
    apply integral_congr_ae
    filter_upwards [] with x
    simp [mul_comm]
  rw [hcoeff, ← hmean, theorem18_20_fourier_nat]
  have hh := hL (g * z ^ k)
  change L ((g : C(AddCircle T, ℂ)) * fourier 1 ^ k) = χa (g * z ^ k) at hh
  rw [hh, map_mul, map_pow]
  change χa g * χ.val z ^ k = 0
  rw [hχz, zero_pow (Nat.ne_of_gt hkpos), mul_zero]

/-- 18.20: adjoining any continuous function with one nonzero negative
Fourier coefficient to the coordinate generates a dense algebra. -/
theorem theorem18_20_dense_adjoin (g : C(AddCircle T, ℂ))
    (hg : ∃ n : ℤ, n < 0 ∧ fourierCoeff g n ≠ 0) :
    (Algebra.adjoin ℂ {fourier 1, g}).topologicalClosure = ⊤ := by
  by_contra hproper
  let B := (Algebra.adjoin ℂ {fourier 1, g}).topologicalClosure
  have hpos : fourier 1 ∈ B :=
    Subalgebra.le_topologicalClosure _ (Algebra.subset_adjoin (by simp))
  have hgm : g ∈ B := Subalgebra.le_topologicalClosure _ (Algebra.subset_adjoin (by simp))
  obtain ⟨n, hn, hgn⟩ := hg
  exact hgn (theorem18_20_proper_subalgebra_negative_coeff B
    (Subalgebra.isClosed_topologicalClosure _) hproper hpos ⟨g, hgm⟩ n hn)

/-- Nested polynomial evaluation: coefficients are ordinary coordinate polynomials,
and the outer variable is evaluated at `g`. -/
def definition18_20_polynomialEval (g : C(AddCircle T, ℂ)) :
    ℂ[X][X] →ₐ[ℂ] C(AddCircle T, ℂ) :=
  Polynomial.aevalTower (Polynomial.aeval (fourier 1)) g

theorem theorem18_20_polynomialEval_sum (g : C(AddCircle T, ℂ)) (p : ℂ[X][X]) :
    definition18_20_polynomialEval g p =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        Polynomial.aeval (fourier 1) (p.coeff i) * g ^ i := by
  exact Polynomial.eval₂_eq_sum_range _ _

/-- 18.20 in the book's finite-polynomial form, with uniform approximation measured
by the supremum norm. The coefficient polynomials are `p.coeff i`. -/
theorem theorem18_20_polynomial_approximation (g : C(AddCircle T, ℂ))
    (hg : ∃ n : ℤ, n < 0 ∧ fourierCoeff g n ≠ 0)
    (f : C(AddCircle T, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X][X], ‖f - ∑ i ∈ Finset.range (p.natDegree + 1),
      Polynomial.aeval (fourier 1) (p.coeff i) * g ^ i‖ < ε := by
  let E := definition18_20_polynomialEval g
  have hpos : fourier 1 ∈ E.range := by
    refine ⟨Polynomial.C Polynomial.X, ?_⟩
    simp [E, definition18_20_polynomialEval]
  have hgm : g ∈ E.range := by
    refine ⟨Polynomial.X, ?_⟩
    simp [E, definition18_20_polynomialEval]
  have hle : Algebra.adjoin ℂ {fourier 1, g} ≤ E.range := by
    apply Algebra.adjoin_le
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact hpos
    · rcases Set.mem_singleton_iff.mp hy with rfl
      exact hgm
  have htop : E.range.topologicalClosure = ⊤ := by
    apply top_unique
    rw [← theorem18_20_dense_adjoin g hg]
    exact Subalgebra.topologicalClosure_mono hle
  have hdense : Dense (E.range : Set C(AddCircle T, ℂ)) := by
    rw [dense_iff_closure_eq]
    change (E.range.topologicalClosure : Set C(AddCircle T, ℂ)) = Set.univ
    rw [htop]
    rfl
  obtain ⟨q, hq, hdist⟩ := hdense.exists_dist_lt f hε
  obtain ⟨p, rfl⟩ := hq
  refine ⟨p, ?_⟩
  simpa [dist_eq_norm, E, theorem18_20_polynomialEval_sum] using hdist

/-- 18.20 in pointwise notation: one finite family of coordinate polynomials
approximates the requested function at every point of the circle. -/
theorem theorem18_20 (g : C(AddCircle T, ℂ))
    (hg : ∃ n : ℤ, n < 0 ∧ fourierCoeff g n ≠ 0)
    (f : C(AddCircle T, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (P : ℕ → ℂ[X]), ∀ x : AddCircle T,
      ‖f x - ∑ i ∈ Finset.range (N + 1),
        (P i).eval (fourier 1 x) * g x ^ i‖ < ε := by
  obtain ⟨p, hp⟩ := theorem18_20_polynomial_approximation g hg f ε hε
  refine ⟨p.natDegree, p.coeff, ?_⟩
  intro x
  have heval (q : ℂ[X]) :
      (Polynomial.aeval (fourier 1) q : C(AddCircle T, ℂ)) x = q.eval (fourier 1 x) := by
    exact (Polynomial.aeval_algHom_apply (ContinuousMap.evalAlgHom ℂ ℂ x)
      (fourier 1) q).symm
  have hbound := (f - ∑ i ∈ Finset.range (p.natDegree + 1),
    Polynomial.aeval (fourier 1) (p.coeff i) * g ^ i).norm_coe_le_norm x
  apply lt_of_le_of_lt _ hp
  simpa only [ContinuousMap.sub_apply, ContinuousMap.sum_apply,
    ContinuousMap.mul_apply, ContinuousMap.pow_apply, heval] using hbound

/-- The normalization agrees with Rudin's `1/(2π)` integral over a full period
when `T = 2π`; any starting point `a` may be used. -/
theorem theorem18_20_fourierCoeff_interval (g : C(AddCircle T, ℂ)) (n : ℤ) (a : ℝ) :
    fourierCoeff g n =
      (1 / T) • ∫ x in a..a + T,
        fourier (-n) (x : AddCircle T) * g (x : AddCircle T) := by
  simpa only [smul_eq_mul] using fourierCoeff_eq_intervalIntegral g n a

end RudinRCA.Chapter18

#print axioms RudinRCA.Chapter18.theorem18_20_proper_subalgebra_negative_coeff
#print axioms RudinRCA.Chapter18.theorem18_20_dense_adjoin
#print axioms RudinRCA.Chapter18.theorem18_20_polynomial_approximation
#print axioms RudinRCA.Chapter18.theorem18_20
#print axioms RudinRCA.Chapter18.theorem18_20_fourierCoeff_interval
#print axioms RudinRCA.Chapter18.theorem18_20_meanCLM_apply
#print axioms RudinRCA.Chapter18.theorem18_20_polynomialEval_sum
