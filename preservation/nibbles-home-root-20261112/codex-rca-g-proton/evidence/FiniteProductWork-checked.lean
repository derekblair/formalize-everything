import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
Rudin, Real and Complex Analysis, third edition, Theorem 15.3.

The finite set formulation includes the printed products indexed from 1 to N.
-/

namespace RudinRCA.Chapter15

/-- Theorem 15.3, first estimate: the product of `1 + |uᵢ|` is at most the
exponential of the sum of the absolute values. -/
theorem finite_product_majorant_le_exp {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    (∏ i ∈ s, (1 + ‖u i‖)) ≤ Real.exp (∑ i ∈ s, ‖u i‖) :=
  Real.prod_one_add_le_exp_sum s (fun i ↦ norm_nonneg (u i))

/-- Theorem 15.3, second estimate: subtracting one from the product is bounded
by subtracting one from its nonnegative majorant. -/
theorem norm_finite_product_sub_one_le {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    ‖(∏ i ∈ s, (1 + u i)) - 1‖ ≤ (∏ i ∈ s, (1 + ‖u i‖)) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    calc
      ‖(1 + u a) * (∏ i ∈ s, (1 + u i)) - 1‖ =
          ‖(1 + u a) * ((∏ i ∈ s, (1 + u i)) - 1) + u a‖ := by
            congr 1
            ring
      _ ≤ ‖(1 + u a) * ((∏ i ∈ s, (1 + u i)) - 1)‖ + ‖u a‖ :=
        norm_add_le _ _
      _ = ‖1 + u a‖ * ‖(∏ i ∈ s, (1 + u i)) - 1‖ + ‖u a‖ := by
        rw [Complex.norm_mul]
      _ ≤ (1 + ‖u a‖) * ‖(∏ i ∈ s, (1 + u i)) - 1‖ + ‖u a‖ := by
        apply add_le_add _ le_rfl
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa using norm_add_le (1 : ℂ) (u a)
      _ ≤ (1 + ‖u a‖) * ((∏ i ∈ s, (1 + ‖u i‖)) - 1) + ‖u a‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_left ih (add_nonneg zero_le_one (norm_nonneg _))) le_rfl
      _ = (1 + ‖u a‖) * (∏ i ∈ s, (1 + ‖u i‖)) - 1 := by ring

/-- Theorem 15.3, with the two printed estimates stated together. -/
theorem finite_product_estimates {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    (∏ i ∈ s, (1 + ‖u i‖)) ≤ Real.exp (∑ i ∈ s, ‖u i‖) ∧
      ‖(∏ i ∈ s, (1 + u i)) - 1‖ ≤ (∏ i ∈ s, (1 + ‖u i‖)) - 1 :=
  ⟨finite_product_majorant_le_exp s u, norm_finite_product_sub_one_le s u⟩

#print axioms finite_product_majorant_le_exp
#print axioms norm_finite_product_sub_one_le
#print axioms finite_product_estimates

end RudinRCA.Chapter15
