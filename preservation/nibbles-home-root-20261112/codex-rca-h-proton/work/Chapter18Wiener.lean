import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Operator.Bilinear
import Chapter18Ideals

/-! Supporting construction for Rudin RCA 18.21 (Wiener's theorem).

This file constructs convolution directly in the complete coefficient space ℓ¹(ℤ,ℂ),
so absolute summability of the output is built into its type. It does not assert
the reciprocal theorem until the convolution ring and its characters are established.
No `sorry`, additional axiom, or missing spectral-invariance hypothesis is introduced.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped lp

namespace RudinRCA.Chapter18.Wiener

abbrev Coefficients : Type := ℓ¹(ℤ, ℂ)

lemma summable_norm (a : Coefficients) : Summable (fun n : ℤ => ‖a n‖) := by
  simpa using (lp.memℓp a).summable (by norm_num : 0 < (1 : ENNReal).toReal)

lemma norm_eq_tsum (a : Coefficients) : ‖a‖ = ∑' n : ℤ, ‖a n‖ := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal) a

abbrev single (n : ℤ) (c : ℂ) : Coefficients :=
  lp.single (E := fun _ : ℤ => ℂ) 1 n c

@[simp] lemma norm_single (n : ℤ) (c : ℂ) : ‖single n c‖ = ‖c‖ :=
  lp.norm_single (E := fun _ : ℤ => ℂ) (p := 1) zero_lt_one n c

lemma hasSum_single (a : Coefficients) : HasSum (fun n : ℤ => single n (a n)) a :=
  lp.hasSum_single (by simp) a

lemma summable_eval_norm (a : Coefficients) (z : Circle) :
    Summable (fun n : ℤ => ‖a n * (z : ℂ) ^ n‖) := by
  simpa only [norm_mul, norm_zpow, Circle.norm_coe, one_zpow, mul_one] using summable_norm a

lemma summable_eval (a : Coefficients) (z : Circle) :
    Summable (fun n : ℤ => a n * (z : ℂ) ^ n) :=
  (summable_eval_norm a z).of_norm

/-- Evaluate an absolutely summable Laurent series at a point of the circle. -/
def eval (z : Circle) : Coefficients →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun a => ∑' n : ℤ, a n * (z : ℂ) ^ n
      map_add' := by
        intro a b
        simpa only [lp.coeFn_add, Pi.add_apply, add_mul] using
          (summable_eval a z).tsum_add (summable_eval b z)
      map_smul' := by
        intro c a
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact (summable_eval a z).tsum_mul_left c }
    1 (fun a => by
      change ‖∑' n : ℤ, a n * (z : ℂ) ^ n‖ ≤ 1 * ‖a‖
      simpa only [one_mul, norm_eq_tsum, norm_mul, norm_zpow, Circle.norm_coe,
        one_zpow, mul_one] using norm_tsum_le_tsum_norm (summable_eval_norm a z))

@[simp] lemma eval_apply (z : Circle) (a : Coefficients) :
    eval z a = ∑' n : ℤ, a n * (z : ℂ) ^ n := rfl

@[simp] lemma eval_single (z : Circle) (n : ℤ) (c : ℂ) :
    eval z (single n c) = c * (z : ℂ) ^ n := by
  classical
  rw [eval_apply, tsum_eq_single n]
  · simp [single]
  · intro k hk
    simp [single, hk]

lemma summable_convolution_terms_norm (a b : Coefficients) :
    Summable (fun p : ℤ × ℤ => ‖single (p.1 + p.2) (a p.1 * b p.2)‖) := by
  simpa only [norm_single] using (summable_norm a).mul_norm (summable_norm b)

lemma summable_convolution_terms (a b : Coefficients) :
    Summable (fun p : ℤ × ℤ => single (p.1 + p.2) (a p.1 * b p.2)) :=
  (summable_convolution_terms_norm a b).of_norm

/-- Convolution defined by a convergent series in ℓ¹, rather than a merely pointwise sum. -/
def convolution (a b : Coefficients) : Coefficients :=
  ∑' p : ℤ × ℤ, single (p.1 + p.2) (a p.1 * b p.2)

lemma norm_convolution_le (a b : Coefficients) :
    ‖convolution a b‖ ≤ ‖a‖ * ‖b‖ := by
  calc
    ‖convolution a b‖ ≤ ∑' p : ℤ × ℤ, ‖single (p.1 + p.2) (a p.1 * b p.2)‖ :=
      norm_tsum_le_tsum_norm (summable_convolution_terms_norm a b)
    _ = ∑' p : ℤ × ℤ, ‖a p.1‖ * ‖b p.2‖ := by simp only [norm_single, norm_mul]
    _ = (∑' n : ℤ, ‖a n‖) * ∑' n : ℤ, ‖b n‖ := by
      symm
      apply tsum_mul_tsum_of_summable_norm
      · simpa only [norm_norm] using summable_norm a
      · simpa only [norm_norm] using summable_norm b
    _ = ‖a‖ * ‖b‖ := by rw [← norm_eq_tsum, ← norm_eq_tsum]

/-- Fourier evaluation converts coefficient convolution into pointwise multiplication. -/
lemma eval_convolution (z : Circle) (a b : Coefficients) :
    eval z (convolution a b) = eval z a * eval z b := by
  rw [convolution, (eval z).map_tsum (summable_convolution_terms a b)]
  simp only [eval_single]
  calc
    (∑' p : ℤ × ℤ, (a p.1 * b p.2) * (z : ℂ) ^ (p.1 + p.2)) =
        ∑' p : ℤ × ℤ, (a p.1 * (z : ℂ) ^ p.1) * (b p.2 * (z : ℂ) ^ p.2) := by
      apply tsum_congr
      intro p
      rw [zpow_add₀ z.coe_ne_zero]
      ring
    _ = eval z a * eval z b :=
      (tsum_mul_tsum_of_summable_norm (summable_eval_norm a z) (summable_eval_norm b z)).symm

lemma convolution_single_single (i j : ℤ) (a b : ℂ) :
    convolution (single i a) (single j b) = single (i + j) (a * b) := by
  classical
  rw [convolution, tsum_eq_single (i, j)]
  · simp [single]
  · intro p hp
    have hp' : p.1 ≠ i ∨ p.2 ≠ j := by
      contrapose! hp
      exact Prod.ext hp.1 hp.2
    rcases hp' with h | h
    · simp [single, h]
    · simp [single, h]

lemma convolution_add_left (a b c : Coefficients) :
    convolution (a + b) c = convolution a c + convolution b c := by
  simp only [convolution, lp.coeFn_add, Pi.add_apply, add_mul, single, lp.single_add]
  exact (summable_convolution_terms a c).tsum_add (summable_convolution_terms b c)

lemma convolution_add_right (a b c : Coefficients) :
    convolution a (b + c) = convolution a b + convolution a c := by
  simp only [convolution, lp.coeFn_add, Pi.add_apply, mul_add, single, lp.single_add]
  exact (summable_convolution_terms a b).tsum_add (summable_convolution_terms a c)

lemma convolution_smul_left (r : ℂ) (a b : Coefficients) :
    convolution (r • a) b = r • convolution a b := by
  simp only [convolution, lp.coeFn_smul, Pi.smul_apply, smul_mul_assoc,
    single, lp.single_smul]
  exact (summable_convolution_terms a b).tsum_const_smul r

lemma convolution_smul_right (r : ℂ) (a b : Coefficients) :
    convolution a (r • b) = r • convolution a b := by
  simp only [convolution, lp.coeFn_smul, Pi.smul_apply, mul_smul_comm,
    single, lp.single_smul]
  exact (summable_convolution_terms a b).tsum_const_smul r

def convolutionCLM : Coefficients →L[ℂ] Coefficients →L[ℂ] Coefficients :=
  (LinearMap.mk₂ ℂ convolution convolution_add_left convolution_smul_left
    convolution_add_right convolution_smul_right).mkContinuous₂ 1
    (fun a b => by
      change ‖convolution a b‖ ≤ 1 * ‖a‖ * ‖b‖
      simpa only [one_mul] using norm_convolution_le a b)

@[simp] lemma convolutionCLM_apply (a b : Coefficients) :
    convolutionCLM a b = convolution a b := rfl

private lemma eq_of_eq_on_single {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : Coefficients →L[ℂ] E)
    (h : ∀ n : ℤ, ∀ c : ℂ, f (single n c) = g (single n c))
    (a : Coefficients) : f a = g a := by
  have heq : f = g := by
    apply lp.ext_continuousLinearMap (E := fun _ : ℤ => ℂ) (p := 1) (by simp)
    intro n
    apply ContinuousLinearMap.ext
    intro c
    exact h n c
  exact congrArg (fun k : Coefficients →L[ℂ] E => k a) heq

lemma convolution_comm (a b : Coefficients) : convolution a b = convolution b a := by
  refine eq_of_eq_on_single (convolutionCLM.flip b) (convolutionCLM b) ?_ a
  intro i x
  refine eq_of_eq_on_single (convolutionCLM (single i x))
    (convolutionCLM.flip (single i x)) ?_ b
  intro j y
  simp only [convolutionCLM_apply, ContinuousLinearMap.flip_apply,
    convolution_single_single, add_comm i j, mul_comm x y]

lemma convolution_assoc (a b c : Coefficients) :
    convolution (convolution a b) c = convolution a (convolution b c) := by
  refine eq_of_eq_on_single
    ((convolutionCLM.flip c).comp (convolutionCLM.flip b))
    (convolutionCLM.flip (convolution b c)) ?_ a
  intro i x
  refine eq_of_eq_on_single
    ((convolutionCLM.flip c).comp (convolutionCLM (single i x)))
    ((convolutionCLM (single i x)).comp (convolutionCLM.flip c)) ?_ b
  intro j y
  refine eq_of_eq_on_single
    (convolutionCLM (convolution (single i x) (single j y)))
    ((convolutionCLM (single i x)).comp (convolutionCLM (single j y))) ?_ c
  intro k z
  simp only [ContinuousLinearMap.comp_apply, convolutionCLM_apply,
    convolution_single_single, add_assoc, mul_assoc]

lemma convolution_one_left (a : Coefficients) : convolution (single 0 1) a = a := by
  refine eq_of_eq_on_single (convolutionCLM (single 0 1))
    (ContinuousLinearMap.id ℂ Coefficients) ?_ a
  intro n c
  simp only [convolutionCLM_apply, convolution_single_single, zero_add, one_mul,
    ContinuousLinearMap.id_apply]

lemma convolution_one_right (a : Coefficients) : convolution a (single 0 1) = a := by
  rw [convolution_comm, convolution_one_left]

/-- The Wiener algebra's multiplication is convolution, and its norm is the ℓ¹ norm. -/
instance coefficientCommRing : CommRing Coefficients :=
  { (inferInstance : AddCommGroup Coefficients) with
    one := single 0 1
    mul := convolution
    mul_assoc := convolution_assoc
    mul_comm := convolution_comm
    one_mul := convolution_one_left
    mul_one := convolution_one_right
    left_distrib := convolution_add_right
    right_distrib := convolution_add_left
    zero_mul := fun a => by
      change convolutionCLM 0 a = 0
      rw [map_zero]
      rfl
    mul_zero := fun a => (convolutionCLM a).map_zero }

@[simp] lemma mul_def (a b : Coefficients) : a * b = convolution a b := rfl
@[simp] lemma one_def : (1 : Coefficients) = single 0 1 := rfl

instance coefficientNormedCommRing : NormedCommRing Coefficients :=
  { (inferInstance : NormedAddCommGroup Coefficients), coefficientCommRing with
    norm_mul_le := norm_convolution_le }

instance coefficientAlgebra : Algebra ℂ Coefficients :=
  Algebra.ofModule convolution_smul_left convolution_smul_right

instance coefficientNormedAlgebra : NormedAlgebra ℂ Coefficients where
  norm_smul_le := norm_smul_le

instance coefficientNormOneClass : NormOneClass Coefficients where
  norm_one := by simp only [one_def, norm_single, norm_one]

@[simp] lemma single_mul_single (i j : ℤ) (a b : ℂ) :
    single i a * single j b = single (i + j) (a * b) :=
  convolution_single_single i j a b

@[simp] lemma eval_one (z : Circle) : eval z (1 : Coefficients) = 1 := by
  simp only [one_def, eval_single, zpow_zero, mul_one]

lemma single_eq_smul (i : ℤ) (c : ℂ) : single i c = c • single i 1 := by
  simpa using lp.single_smul (E := fun _ : ℤ => ℂ) 1 i c (1 : ℂ)

/-- Every character of the convolution algebra is evaluation at a unit-circle point. -/
theorem character_eq_eval (φ : Coefficients →ₐ[ℂ] ℂ) :
    ∃ z : Circle, ∀ a : Coefficients, φ a = eval z a := by
  let v : ℂ := φ (single 1 1)
  have hvle : ‖v‖ ≤ 1 := by
    simpa only [v, norm_single, norm_one] using AlgHom.norm_apply_le_self φ (single 1 1)
  have hwle : ‖φ (single (-1) 1)‖ ≤ 1 := by
    simpa only [norm_single, norm_one] using AlgHom.norm_apply_le_self φ (single (-1) 1)
  have hvw : v * φ (single (-1) 1) = 1 := by
    change φ (single 1 1) * φ (single (-1) 1) = 1
    rw [← map_mul]
    simpa only [single_mul_single, Int.reduceAdd, one_mul, ← one_def] using map_one φ
  have hnorm : ‖v‖ = 1 := by
    have hmul : ‖v‖ * ‖φ (single (-1) 1)‖ = 1 := by
      simpa only [norm_mul, norm_one] using congrArg norm hvw
    have hprodle : ‖v‖ * ‖φ (single (-1) 1)‖ ≤ ‖v‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hwle (norm_nonneg v)
    linarith
  let z : Circle := ⟨v, by
    change v ∈ Metric.sphere (0 : ℂ) 1
    exact mem_sphere_zero_iff_norm.mpr hnorm⟩
  have hvne : v ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hnorm]
    exact one_ne_zero
  have hnat (n : ℕ) : φ (single (n : ℤ) 1) = v ^ n := by
    induction n with
    | zero => simpa only [Nat.cast_zero, ← one_def, pow_zero] using map_one φ
    | succ n ih =>
      have hs : single ((n + 1 : ℕ) : ℤ) 1 = single (n : ℤ) 1 * single 1 1 := by
        simp only [single_mul_single, one_mul, Nat.cast_add, Nat.cast_one]
      rw [hs, map_mul, ih, pow_succ]
  have hint (n : ℤ) : φ (single n 1) = v ^ n := by
    cases n with
    | ofNat n =>
      change φ (single (n : ℤ) 1) = v ^ (n : ℤ)
      rw [zpow_natCast]
      exact hnat n
    | negSucc n =>
      have hm : φ (single (-((n + 1 : ℕ) : ℤ)) 1) * v ^ (n + 1) = 1 := by
        rw [← hnat, ← map_mul, single_mul_single, neg_add_cancel, one_mul, ← one_def,
          map_one]
      have hp : v ^ (n + 1) ≠ 0 := pow_ne_zero _ hvne
      have heq : φ (single (-((n + 1 : ℕ) : ℤ)) 1) = (v ^ (n + 1))⁻¹ := by
        apply mul_right_cancel₀ hp
        rw [hm, inv_mul_cancel₀ hp]
      rw [zpow_negSucc]
      exact heq
  refine ⟨z, fun a => ?_⟩
  calc
    φ a = ∑' n : ℤ, φ (single n (a n)) :=
      ((hasSum_single a).mapL φ.toContinuousLinearMap).tsum_eq.symm
    _ = ∑' n : ℤ, a n * (z : ℂ) ^ n := by
      apply tsum_congr
      intro n
      rw [single_eq_smul, map_smul, hint]
      rfl
    _ = eval z a := rfl

theorem isUnit_of_nowhere_zero (a : Coefficients) (ha : ∀ z : Circle, eval z a ≠ 0) :
    IsUnit a := by
  by_contra h
  obtain ⟨φ, hφ⟩ := theorem18_17_nonunit_character h
  obtain ⟨z, hz⟩ := character_eq_eval (definition18_16_characterAlgHom φ)
  exact ha z ((hz a).symm.trans hφ)

/-- Rudin 18.21: an absolutely summable Laurent series without zeros on the circle
has a reciprocal that is again an absolutely summable Laurent series. -/
theorem reciprocal (c : ℤ → ℂ) (hc : Summable (fun n => ‖c n‖))
    (hf : ∀ z : Circle, (∑' n : ℤ, c n * (z : ℂ) ^ n) ≠ 0) :
    ∃ b : ℤ → ℂ, Summable (fun n => ‖b n‖) ∧
      ∀ z : Circle, (∑' n : ℤ, b n * (z : ℂ) ^ n) =
        (∑' n : ℤ, c n * (z : ℂ) ^ n)⁻¹ := by
  let a : Coefficients := ⟨c, memℓp_gen (by simpa using hc)⟩
  obtain ⟨b, hab⟩ := (isUnit_of_nowhere_zero a hf).exists_right_inv
  refine ⟨b, summable_norm b, fun z => ?_⟩
  have hmul : eval z a * eval z b = 1 := by
    rw [← eval_convolution, ← mul_def, hab, eval_one]
  change eval z b = (eval z a)⁻¹
  have ha0 : eval z a ≠ 0 := hf z
  apply mul_left_cancel₀ ha0
  rw [hmul, mul_inv_cancel₀ ha0]

#print axioms reciprocal

end RudinRCA.Chapter18.Wiener

namespace RudinRCA.Chapter18

/-- 18.21 (Wiener), with the unit circle represented by `Circle`.
The coefficients of both the given series and its reciprocal are absolutely summable. -/
theorem theorem18_21 (f : Circle → ℂ) (c : ℤ → ℂ)
    (hc : Summable (fun n => ‖c n‖))
    (hseries : ∀ z : Circle, f z = ∑' n : ℤ, c n * (z : ℂ) ^ n)
    (hf : ∀ z : Circle, f z ≠ 0) :
    ∃ b : ℤ → ℂ, Summable (fun n => ‖b n‖) ∧
      ∀ z : Circle, (f z)⁻¹ = ∑' n : ℤ, b n * (z : ℂ) ^ n := by
  obtain ⟨b, hb, hbval⟩ := Wiener.reciprocal c hc (fun z => by
    rw [← hseries z]
    exact hf z)
  refine ⟨b, hb, fun z => ?_⟩
  rw [hseries z]
  exact (hbval z).symm

#print axioms theorem18_21

end RudinRCA.Chapter18
