import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

noncomputable section
open Set Filter MeasureTheory Finset
open scoped Topology ComplexConjugate
namespace RudinRCA.Chapter18.Fejer

variable {T : ℝ} [Fact (0 < T)]

/-- Normalized integration on the circle. -/
def mean (T : ℝ) [Fact (0 < T)] : C(AddCircle T, ℂ) →L[ℂ] ℂ :=
  (MeasureTheory.L1.integralCLM' ℂ).comp
    (ContinuousMap.toLp 1 AddCircle.haarAddCircle ℂ)

theorem mean_apply (f : C(AddCircle T, ℂ)) :
    mean T f = ∫ x, f x ∂AddCircle.haarAddCircle := by
  rw [mean, ContinuousLinearMap.comp_apply,
    ← MeasureTheory.L1.integral_eq', MeasureTheory.L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 1) AddCircle.haarAddCircle f)

def coefficient (n : ℤ) : C(AddCircle T, ℂ) →L[ℂ] ℂ :=
  (mean T).comp (ContinuousLinearMap.mul ℂ C(AddCircle T, ℂ) (fourier (-n)))

theorem coefficient_apply (n : ℤ) (f : C(AddCircle T, ℂ)) :
    coefficient n f = fourierCoeff f n := by
  rw [coefficient, ContinuousLinearMap.comp_apply, mean_apply]
  rfl

def projection (n : ℤ) : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ) :=
  (coefficient n).smulRight (fourier n)

theorem projection_apply (n : ℤ) (f : C(AddCircle T, ℂ)) :
    projection n f = fourierCoeff f n • fourier n := by
  simp only [projection, ContinuousLinearMap.smulRight_apply, coefficient_apply]

theorem projection_fourier (m n : ℤ) :
    projection (T := T) n (fourier m) = if n = m then fourier m else 0 := by
  rw [projection_apply, fourierCoeff_fourier]
  by_cases h : n = m
  · subst n; simp
  · simp [Pi.single_apply, h, eq_comm]

/-- Symmetric Fourier partial sums. -/
def dirichlet (N : ℕ) : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ) :=
  projection 0 + ∑ k ∈ range N, (projection (k+1) + projection (-(k+1)))

/-- Cesàro means of the Fourier partial sums. -/
def operator (N : ℕ) : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ) :=
  (N⁻¹ : ℝ) • ∑ k ∈ range N, dirichlet k

/-- The finite triangular-sum identity underlying the positivity of Fejér's kernel. -/
theorem square_sum {E : Type*} [AddCommGroup E] (a : ℤ → E) (N : ℕ) :
    (∑ i ∈ range N, ∑ j ∈ range N, a ((i : ℤ)-j)) =
      ∑ k ∈ range N, (a 0 + ∑ i ∈ range k, (a (i+1) + a (-(i+1)))) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hp : (∑ j ∈ range N, a ((N : ℤ)-j)) =
          ∑ j ∈ range N, a (j+1) := by
        rw [← Finset.sum_range_reflect]
        apply sum_congr rfl
        intro j hj
        congr 1
        have hj' := mem_range.mp hj
        omega
      have hn : (∑ i ∈ range N, a ((i : ℤ)-N)) =
          ∑ i ∈ range N, a (-(i+1)) := by
        rw [← Finset.sum_range_reflect]
        apply sum_congr rfl
        intro j hj
        congr 1
        have hj' := mem_range.mp hj
        omega
      simp only [sum_range_succ, sum_add_distrib]
      rw [ih, hp, hn]
      simp only [sub_self, sum_add_distrib]
      abel

/-- The same means as a square sum of Fourier projections. -/
theorem operator_square (N : ℕ) :
    operator (T := T) N = (N⁻¹ : ℝ) •
      ∑ i ∈ range N, ∑ j ∈ range N, projection ((i : ℤ)-j) := by
  rw [square_sum]
  rfl

/-- The complex kernel is a nonnegative real square. -/
theorem kernel_square (N : ℕ) (x y : AddCircle T) :
    (∑ i ∈ range N, ∑ j ∈ range N,
      fourier ((i : ℤ)-j) x * fourier (-((i : ℤ)-j)) y) =
      ((‖∑ i ∈ range N, fourier (i : ℤ) x * fourier (-(i : ℤ)) y‖ ^ 2 : ℝ) : ℂ) := by
  let u : ℤ → ℂ := fun i => fourier i x * fourier (-i) y
  have hmul (i j : ℤ) :
      fourier (i-j) x * fourier (-(i-j)) y = u i * conj (u j) := by
    simp only [u, sub_eq_add_neg, fourier_add, neg_add_rev, neg_neg,
      fourier_neg, map_mul, Complex.conj_conj]
    ring
  simp_rw [hmul]
  rw [← Finset.sum_mul_sum, ← map_sum, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The Fejér operator has an integral representation with a positive kernel. -/
theorem operator_integral (N : ℕ) (f : C(AddCircle T, ℂ)) (x : AddCircle T) :
    operator N f x =
      ∫ y, ((N⁻¹ : ℝ) * ‖∑ i ∈ range N,
        fourier (i : ℤ) x * fourier (-(i : ℤ)) y‖ ^ 2 : ℝ) • f y
        ∂AddCircle.haarAddCircle := by
  have hi (n : ℤ) : Integrable (fun y : AddCircle T =>
      (fourier n x * fourier (-n) y) * f y) AddCircle.haarAddCircle :=
    (by fun_prop : Continuous (fun y : AddCircle T =>
      (fourier n x * fourier (-n) y) * f y)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hp (n : ℤ) : projection n f x = ∫ y,
      (fourier n x * fourier (-n) y) * f y ∂AddCircle.haarAddCircle := by
    rw [projection_apply, ContinuousMap.smul_apply, smul_eq_mul, fourierCoeff]
    simp only [smul_eq_mul]
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  calc
    operator N f x = (N⁻¹ : ℝ) • ∑ i ∈ range N, ∑ j ∈ range N,
        ∫ y, (fourier ((i : ℤ)-j) x * fourier (-((i : ℤ)-j)) y) * f y
          ∂AddCircle.haarAddCircle := by
      rw [operator_square]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
        ContinuousMap.smul_apply, ContinuousMap.sum_apply, hp]
    _ = (N⁻¹ : ℝ) • ∫ y, ∑ i ∈ range N, ∑ j ∈ range N,
        (fourier ((i : ℤ)-j) x * fourier (-((i : ℤ)-j)) y) * f y
          ∂AddCircle.haarAddCircle := by
      congr 1
      rw [integral_finsetSum _ (fun i hi' => integrable_finsetSum _ (fun j hj => hi _))]
      apply sum_congr rfl
      intro i hi'
      exact (integral_finsetSum _ (fun j hj => hi _)).symm
    _ = ∫ y, (N⁻¹ : ℝ) • ((∑ i ∈ range N, ∑ j ∈ range N,
        fourier ((i : ℤ)-j) x * fourier (-((i : ℤ)-j)) y) * f y)
          ∂AddCircle.haarAddCircle := by
      rw [integral_smul]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [sum_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [kernel_square]
      simp [Complex.real_smul, Complex.ofReal_mul, mul_assoc]

/-- Every Fejér kernel has normalized integral one (for a nonzero index). -/
theorem operator_one (N : ℕ) (hN : N ≠ 0) :
    operator (T := T) N 1 = 1 := by
  have hproj (n : ℤ) : projection (T := T) n 1 = if n = 0 then 1 else 0 := by
    have hzero : (fourier 0 : C(AddCircle T, ℂ)) = 1 := by ext x; exact fourier_zero
    rw [← hzero, projection_fourier]
  have hdir (k : ℕ) : dirichlet (T := T) k 1 = 1 := by
    have hp (i : ℕ) : (i : ℤ) + 1 ≠ 0 := by omega
    have hn (i : ℕ) : -((i : ℤ) + 1) ≠ 0 := by omega
    simp only [dirichlet, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
      hproj, hp, hn, if_false, if_true, zero_add, add_zero, Finset.sum_const_zero]
  simp only [operator, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, hdir,
    sum_const, card_range]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN), one_smul]

/-- A uniform contraction estimate, including the zero index. -/
theorem operator_norm_le (N : ℕ) (f : C(AddCircle T, ℂ)) :
    ‖operator N f‖ ≤ ‖f‖ := by
  by_cases hN : N = 0
  · subst N; simp [operator]
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  let K : AddCircle T → ℝ := fun y => (N⁻¹ : ℝ) *
    ‖∑ i ∈ range N, fourier (i : ℤ) x * fourier (-(i : ℤ)) y‖ ^ 2
  have hK : Continuous K := by fun_prop
  have hKi : Integrable K AddCircle.haarAddCircle := hK.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace K)
  have hK0 (y) : 0 ≤ K y := by dsimp [K]; positivity
  have hmass : ∫ y, K y ∂AddCircle.haarAddCircle = 1 := by
    have h := congrArg (fun g : C(AddCircle T, ℂ) => g x) (operator_one (T := T) N hN)
    rw [operator_integral] at h
    simp only [ContinuousMap.one_apply, Complex.real_smul, mul_one] at h
    rw [integral_complex_ofReal] at h
    exact_mod_cast h
  rw [operator_integral]
  have hbound := norm_integral_le_of_norm_le (hKi.mul_const ‖f‖)
    (ae_of_all _ (fun y => (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hK0 y)]
      exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm f y) (hK0 y) :
        ‖K y • f y‖ ≤ K y * ‖f‖)))
  simpa only [integral_mul_const, hmass, one_mul] using hbound


/-- Each fixed Fourier mode is eventually reproduced by the partial sums. -/
theorem dirichlet_fourier_tendsto (m : ℤ) :
    Tendsto (fun N => dirichlet (T := T) N (fourier m)) atTop (𝓝 (fourier m)) := by
  have hz (N : ℕ) : dirichlet (T := T) N (fourier 0) = fourier 0 := by
    have hp (i : ℕ) : (i : ℤ) + 1 ≠ 0 := by omega
    have hn (i : ℕ) : -((i : ℤ) + 1) ≠ 0 := by omega
    simp only [dirichlet, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
      projection_fourier, hp, hn, if_false, if_true, zero_add, add_zero,
      Finset.sum_const_zero]
  have hp (n N : ℕ) (h : n < N) :
      dirichlet (T := T) N (fourier ((n : ℤ)+1)) = fourier ((n : ℤ)+1) := by
    have h0 : (0 : ℤ) ≠ (n : ℤ)+1 := by omega
    have hn (i : ℕ) : -((i : ℤ)+1) ≠ (n : ℤ)+1 := by omega
    have he (i : ℕ) : ((i : ℤ)+1 = (n : ℤ)+1) ↔ i = n := by omega
    simp only [dirichlet, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
      projection_fourier, h0, hn, he, if_false, zero_add, add_zero]
    simp [h]
  have hn (n N : ℕ) (h : n < N) :
      dirichlet (T := T) N (fourier (-((n : ℤ)+1))) = fourier (-((n : ℤ)+1)) := by
    have h0 : (0 : ℤ) ≠ -((n : ℤ)+1) := by omega
    have hp (i : ℕ) : (i : ℤ)+1 ≠ -((n : ℤ)+1) := by omega
    have he (i : ℕ) : (-((i : ℤ)+1) = -((n : ℤ)+1)) ↔ i = n := by omega
    simp only [dirichlet, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
      projection_fourier, h0, hp, he, if_false, zero_add, add_zero]
    simp [h]
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · cases n with
    | zero => simpa only [Nat.cast_zero, hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        (fourier 0 : C(AddCircle T, ℂ))) atTop (𝓝 (fourier 0)))
    | succ n =>
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop (n+1)] with N hN
        simpa using (hp n N (by omega)).symm
  · cases n with
    | zero => simpa only [Nat.cast_zero, neg_zero, hz] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
          (fourier 0 : C(AddCircle T, ℂ))) atTop (𝓝 (fourier 0)))
    | succ n =>
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop (n+1)] with N hN
        simpa using (hn n N (by omega)).symm

/-- Fejér means converge on each Fourier mode by Cesàro's lemma. -/
theorem operator_fourier_tendsto (m : ℤ) :
    Tendsto (fun N => operator (T := T) N (fourier m)) atTop (𝓝 (fourier m)) := by
  simpa only [operator, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
    using (dirichlet_fourier_tendsto (T := T) m).cesaro_smul

/-- The uniform contraction bound makes the family equicontinuous. -/
theorem operator_equicontinuous :
    Equicontinuous (fun N : ℕ => (operator (T := T) N : C(AddCircle T, ℂ) →
      C(AddCircle T, ℂ))) := by
  apply Metric.equicontinuous_of_continuity_modulus id tendsto_id
  intro f g N
  simpa only [id_eq, dist_eq_norm, ← map_sub] using operator_norm_le N (f-g)

/-- Continuous functions whose Fejér means converge in the uniform norm. -/
def convergent : Submodule ℂ C(AddCircle T, ℂ) where
  carrier := {f | Tendsto (fun N => operator N f) atTop (𝓝 f)}
  zero_mem' := by simpa only [Set.mem_setOf_eq, map_zero] using (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (0 : C(AddCircle T, ℂ))) atTop (𝓝 0))
  add_mem' := by
    intro f g hf hg
    simpa only [Set.mem_setOf_eq, map_add] using hf.add hg
  smul_mem' := by
    intro c f hf
    simpa only [Set.mem_setOf_eq, map_smul] using hf.const_smul c

/-- Fejér's uniform approximation theorem for continuous functions on the circle. -/
theorem operator_tendsto (f : C(AddCircle T, ℂ)) :
    Tendsto (fun N => operator N f) atTop (𝓝 f) := by
  have hclosed : IsClosed (convergent (T := T) : Set C(AddCircle T, ℂ)) :=
    operator_equicontinuous.isClosed_setOfPred_tendsto continuous_id
  have hspan : Submodule.span ℂ (Set.range (fourier (T := T))) ≤ convergent :=
    Submodule.span_le.mpr (by rintro f ⟨n, rfl⟩; exact operator_fourier_tendsto n)
  have htop := Submodule.topologicalClosure_minimal _ hspan hclosed
  rw [span_fourier_closure_eq_top] at htop
  exact htop (by trivial : f ∈ (⊤ : Submodule ℂ C(AddCircle T, ℂ)))

/-- Closed linear span of the nonnegative Fourier modes. -/
def positiveClosure : Submodule ℂ C(AddCircle T, ℂ) :=
  (Submodule.span ℂ (Set.range (fun n : ℕ => (fourier (n : ℤ) :
    C(AddCircle T, ℂ))))).topologicalClosure

theorem coefficient_zero_of_mem_positiveClosure (f : C(AddCircle T, ℂ))
    (hf : f ∈ positiveClosure) (m : ℤ) (hm : m < 0) : fourierCoeff f m = 0 := by
  let K := (coefficient (T := T) m).ker
  have hspan : Submodule.span ℂ (Set.range (fun n : ℕ =>
      (fourier (n : ℤ) : C(AddCircle T, ℂ)))) ≤ K := by
    apply Submodule.span_le.mpr
    rintro g ⟨n, rfl⟩
    change coefficient m (fourier (n : ℤ)) = 0
    rw [coefficient_apply, fourierCoeff_fourier]
    have hn : m ≠ (n : ℤ) := by omega
    simp [Pi.single_apply, hn, eq_comm]
  have hclosed : IsClosed (K : Set C(AddCircle T, ℂ)) :=
    (coefficient (T := T) m).isClosed_ker
  have hle := Submodule.topologicalClosure_minimal _ hspan hclosed
  have h := hle hf
  change coefficient m f = 0 at h
  simpa only [coefficient_apply] using h

/-- Vanishing negative coefficients give uniform approximation by analytic polynomials. -/
theorem mem_positiveClosure_of_coefficient_zero (f : C(AddCircle T, ℂ))
    (hf : ∀ m : ℤ, m < 0 → fourierCoeff f m = 0) : f ∈ positiveClosure := by
  let P : Submodule ℂ C(AddCircle T, ℂ) :=
    Submodule.span ℂ (Set.range (fun n : ℕ => (fourier (n : ℤ) : C(AddCircle T, ℂ))))
  have hp (m : ℤ) : projection m f ∈ P := by
    rw [projection_apply]
    by_cases hm : m < 0
    · rw [hf m hm, zero_smul]; exact P.zero_mem
    · have hm0 : 0 ≤ m := le_of_not_gt hm
      apply P.smul_mem
      exact Submodule.subset_span ⟨m.toNat, by
        change fourier ((m.toNat : ℕ) : ℤ) = fourier m
        rw [Int.toNat_of_nonneg hm0]⟩
  have hall (N : ℕ) : operator N f ∈ P := by
    rw [operator_square]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
    exact P.smul_of_tower_mem _ (P.sum_mem (fun i hi => P.sum_mem (fun j hj => hp _)))
  apply P.isClosed_topologicalClosure.mem_of_tendsto (operator_tendsto f)
  exact Filter.Eventually.of_forall (fun N => Submodule.le_topologicalClosure _ (hall N))

/-- The full Fourier characterization used in printed 18.19. -/
theorem fourier_negative_vanish_iff_mem_positive_closure (f : C(AddCircle T, ℂ)) :
    (∀ m : ℤ, m < 0 → fourierCoeff f m = 0) ↔
      f ∈ (Submodule.span ℂ (Set.range (fun n : ℕ =>
        (fourier (n : ℤ) : C(AddCircle T, ℂ))))).topologicalClosure := by
  exact ⟨mem_positiveClosure_of_coefficient_zero f,
    fun h m hm => coefficient_zero_of_mem_positiveClosure f h m hm⟩

end RudinRCA.Chapter18.Fejer

#print axioms RudinRCA.Chapter18.Fejer.coefficient_apply
#print axioms RudinRCA.Chapter18.Fejer.square_sum
#print axioms RudinRCA.Chapter18.Fejer.operator_square
#print axioms RudinRCA.Chapter18.Fejer.kernel_square
#print axioms RudinRCA.Chapter18.Fejer.operator_integral
#print axioms RudinRCA.Chapter18.Fejer.operator_one
#print axioms RudinRCA.Chapter18.Fejer.operator_norm_le

#print axioms RudinRCA.Chapter18.Fejer.dirichlet_fourier_tendsto
#print axioms RudinRCA.Chapter18.Fejer.operator_fourier_tendsto
#print axioms RudinRCA.Chapter18.Fejer.operator_tendsto
#print axioms RudinRCA.Chapter18.Fejer.coefficient_zero_of_mem_positiveClosure
#print axioms RudinRCA.Chapter18.Fejer.mem_positiveClosure_of_coefficient_zero
#print axioms RudinRCA.Chapter18.Fejer.fourier_negative_vanish_iff_mem_positive_closure
