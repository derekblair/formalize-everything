import RudinRCA.Chapter04
import RudinRCA.Chapter05
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Chapter 18: Elementary Theory of Banach Algebras (`18.1`–`18.21`)

Complete formalization of Walter Rudin, *Real and Complex Analysis* (3rd ed., McGraw-Hill, 1987),
Chapter 18: *Elementary Theory of Banach Algebras* (printed pp. 356–368, top-level nodes
`18.1`–`18.21` together with the three local corollaries following `18.4`), following
`SCOPING-H.md`.

In accordance with Rudin's standing assumptions (`SCOPING-H.md` §Statement fidelity notes):
* Nodes `18.1`–`18.10` (and `18.4` Corollaries 1–3) are formalized for arbitrary (not necessarily
  commutative) complex Banach algebras with unit of norm `1`
  (`[NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]`).
* Node `18.11` constructs the concrete disc algebra `DiscAlgebra` and its isometric boundary image
  `DiscAlgebraCircle ⊆ C(FourierCircle, ℂ)` and computes the coordinate spectra on both algebras.
* Nodes `18.12`–`18.21` work in commutative complex Banach algebras (`[NormedCommRing A]`),
  culminating in the disc-algebra Bezout theorem (`18.18`), Wermer's maximality theorem and the
  Fourier characterization of the disc algebra (`18.19`–`18.20`), and Wiener's reciprocal theorem
  for absolutely convergent Fourier series (`18.21`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric Topology
open scoped ENNReal NNReal Ring ComplexConjugate Classical

namespace RudinRCA.Chapter18

/-! ## Section 1: Invertible Elements and Spectra (`18.1`–`18.11`) -/

section NonCommutativeBanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- `18.1`: The set `G(A)` of invertible elements (two-sided units) of a ring or algebra `A`. -/
def invertibleElements (R : Type*) [Monoid R] : Set R :=
  {x : R | IsUnit x}

@[simp]
theorem mem_invertibleElements {R : Type*} [Monoid R] (x : R) :
    x ∈ invertibleElements R ↔ IsUnit x :=
  Iff.rfl

omit [CompleteSpace A] in
/-- **18.1 (Definitions: Complex Banach algebras, unit, inverses, and spectrum):**
In a complex Banach algebra `A` with unit `1` of norm `1`:
1. Multiplication is submultiplicative (`‖x * y‖ ≤ ‖x‖ * ‖y‖`), `‖(1 : A)‖ = 1`, `(1 : A) ≠ 0`,
   and scalar embedding is isometric (`‖algebraMap ℂ A z‖ = ‖z‖`);
2. `x ∈ invertibleElements A` iff `x` has a two-sided inverse (`∃ y, x * y = 1 ∧ y * x = 1`),
   which is unique and equals `x⁻¹ʳ`; `1` is invertible, `0` is not invertible, and
   `invertibleElements A` is closed under inversion and multiplication with
   `(x * y)⁻¹ʳ = y⁻¹ʳ * x⁻¹ʳ`;
3. For `x : A` and `z : ℂ`, `z ∈ spectrum ℂ x` iff `algebraMap ℂ A z - x` is not invertible
   (equivalently `x - algebraMap ℂ A z` is not invertible), and `(spectrum ℂ x)ᶜ = resolventSet ℂ x`. -/
theorem theorem18_1 :
    (∀ x y : A, ‖x * y‖ ≤ ‖x‖ * ‖y‖) ∧
    ‖(1 : A)‖ = 1 ∧
    (1 : A) ≠ 0 ∧
    (∀ z : ℂ, ‖algebraMap ℂ A z‖ = ‖z‖) ∧
    (∀ x : A, x ∈ invertibleElements A ↔ ∃ y : A, x * y = 1 ∧ y * x = 1) ∧
    (∀ x y₁ y₂ : A, (x * y₁ = 1 ∧ y₁ * x = 1) → (x * y₂ = 1 ∧ y₂ * x = 1) → y₁ = y₂) ∧
    (1 : A) ∈ invertibleElements A ∧
    (0 : A) ∉ invertibleElements A ∧
    (∀ x : A, IsUnit x → IsUnit (x⁻¹ʳ) ∧ (x⁻¹ʳ)⁻¹ʳ = x) ∧
    (∀ x y : A, IsUnit x → IsUnit y → IsUnit (x * y) ∧ (x * y)⁻¹ʳ = y⁻¹ʳ * x⁻¹ʳ) ∧
    (∀ (x : A) (z : ℂ),
      (z ∈ spectrum ℂ x ↔ ¬ IsUnit (algebraMap ℂ A z - x)) ∧
      (z ∈ spectrum ℂ x ↔ ¬ IsUnit (x - algebraMap ℂ A z)) ∧
      (spectrum ℂ x)ᶜ = resolventSet ℂ x) := by
  have : Nontrivial A := NormOneClass.nontrivial
  refine ⟨norm_mul_le, norm_one, one_ne_zero, ?_, ?_, ?_, isUnit_one, not_isUnit_zero, ?_, ?_, ?_⟩
  · intro z
    rw [Algebra.algebraMap_eq_smul_one, norm_smul, norm_one, mul_one]
  · intro x
    simp only [mem_invertibleElements, isUnit_iff_exists]
  · intro x y₁ y₂ hy₁ hy₂
    calc
      y₁ = y₁ * (x * y₂) := by rw [hy₂.1, mul_one]
      _ = (y₁ * x) * y₂ := (mul_assoc y₁ x y₂).symm
      _ = y₂ := by rw [hy₁.2, one_mul]
  · intro x hx
    rcases hx with ⟨u, rfl⟩
    simp only [Ring.inverse_unit]
    exact ⟨u⁻¹.isUnit, by simp⟩
  · intro x y hx hy
    refine ⟨hx.mul hy, ?_⟩
    rcases hx with ⟨u, rfl⟩
    rcases hy with ⟨v, rfl⟩
    simp only [← Units.val_mul, Ring.inverse_unit, mul_inv_rev]
  · intro x z
    refine ⟨spectrum.mem_iff, ?_, compl_compl (resolventSet ℂ x)⟩
    rw [spectrum.mem_iff]
    have hneg : algebraMap ℂ A z - x = -(x - algebraMap ℂ A z) := by abel
    have hiff : IsUnit (algebraMap ℂ A z - x) ↔ IsUnit (x - algebraMap ℂ A z) :=
      ⟨fun h => by have h' := h.neg; rwa [hneg, neg_neg] at h', fun h => hneg ▸ h.neg⟩
    rw [hiff]

omit [CompleteSpace A] [NormOneClass A] in
/-- **18.2 (Algebra, topology, and holomorphy connections):**
In a complex Banach algebra `A`, addition, scalar multiplication, and ring multiplication are
jointly continuous, multiplication satisfies the quantitative difference bound
`‖x * y - x₀ * y₀‖ ≤ ‖x - x₀‖ * ‖y‖ + ‖x₀‖ * ‖y - y₀‖`, every continuous linear functional
`Φ : StrongDual ℂ A` is continuous and `ℂ`-linear, and composing any `A`-valued holomorphic map
`g : ℂ → A` on `Ω` with `Φ` yields a complex-holomorphic scalar function on `Ω`. -/
theorem theorem18_2 :
    Continuous (fun p : A × A => p.1 + p.2) ∧
    Continuous (fun p : ℂ × A => p.1 • p.2) ∧
    Continuous (fun p : A × A => p.1 * p.2) ∧
    (∀ x y x₀ y₀ : A, ‖x * y - x₀ * y₀‖ ≤ ‖x - x₀‖ * ‖y‖ + ‖x₀‖ * ‖y - y₀‖) ∧
    (∀ Φ : StrongDual ℂ A,
      Continuous Φ ∧ ∀ (c : ℂ) (x y : A), Φ (c • x + y) = c * Φ x + Φ y) ∧
    (∀ (Φ : StrongDual ℂ A) {Ω : Set ℂ} {g : ℂ → A},
      DifferentiableOn ℂ g Ω → DifferentiableOn ℂ (fun z => Φ (g z)) Ω) := by
  refine ⟨continuous_add, continuous_smul, continuous_mul, ?_, ?_, ?_⟩
  · intro x y x₀ y₀
    have hsplit : x * y - x₀ * y₀ = (x - x₀) * y + x₀ * (y - y₀) := by noncomm_ring
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
  · intro Φ
    exact ⟨Φ.continuous, fun c x y => by simp [map_add, map_smul]⟩
  · intro Φ Ω g hg
    exact Φ.differentiable.comp_differentiableOn hg

omit [NormedAlgebra ℂ A] in
/-- Companion form of `18.3` for `1 - x` under `‖x‖ < 1`: Neumann series convergence and
quadratic remainder bound `‖(1 - x)⁻¹ʳ - 1 - x‖ ≤ ‖x‖ ^ 2 / (1 - ‖x‖)`. -/
theorem theorem18_3_one_sub {x : A} (hx : ‖x‖ < 1) :
    IsUnit (1 - x) ∧
    Summable (fun n : ℕ => ‖x ^ n‖) ∧
    HasSum (fun n : ℕ => x ^ n) ((1 - x)⁻¹ʳ) ∧
    ((1 - x) * (1 - x)⁻¹ʳ = 1 ∧ (1 - x)⁻¹ʳ * (1 - x) = 1) ∧
    ‖(1 - x)⁻¹ʳ‖ ≤ (1 - ‖x‖)⁻¹ ∧
    ‖(1 - x)⁻¹ʳ - 1 - x‖ ≤ ‖x‖ ^ 2 / (1 - ‖x‖) := by
  have hgeom : Summable (fun n : ℕ => ‖x‖ ^ n) :=
    summable_geometric_of_lt_one (norm_nonneg x) hx
  have hnorm_sum : Summable (fun n : ℕ => ‖x ^ n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_pow_le x n) hgeom
  have hsum_x : Summable (fun n : ℕ => x ^ n) := hnorm_sum.of_norm
  let u : Aˣ := Units.oneSub x hx
  have hu : IsUnit (1 - x) := u.isUnit
  have hinv_eq : (1 - x)⁻¹ʳ = ∑' n : ℕ, x ^ n := NormedRing.inverse_one_sub x hx
  have hhasSum : HasSum (fun n : ℕ => x ^ n) ((1 - x)⁻¹ʳ) := hinv_eq ▸ hsum_x.hasSum
  have hmul : (1 - x) * (1 - x)⁻¹ʳ = 1 ∧ (1 - x)⁻¹ʳ * (1 - x) = 1 := by
    have hu_inv : (1 - x)⁻¹ʳ = ↑u⁻¹ := by
      rw [← Ring.inverse_unit u, Units.val_oneSub]
    rw [hu_inv]
    exact ⟨u.val_inv, u.inv_val⟩
  have hnorm_inv : ‖(1 - x)⁻¹ʳ‖ ≤ (1 - ‖x‖)⁻¹ := by
    rw [hinv_eq]
    calc
      ‖∑' n : ℕ, x ^ n‖ ≤ ∑' n : ℕ, ‖x ^ n‖ := norm_tsum_le_tsum_norm hnorm_sum
      _ ≤ ∑' n : ℕ, ‖x‖ ^ n := hnorm_sum.tsum_le_tsum (fun n => norm_pow_le x n) hgeom
      _ = (1 - ‖x‖)⁻¹ := tsum_geometric_of_lt_one (norm_nonneg x) hx
  have hrem : (1 - x)⁻¹ʳ - 1 - x = x ^ 2 * (1 - x)⁻¹ʳ := by
    have h2 := NormedRing.inverse_one_sub_nth_order' (R := A) 2 hx
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at h2
    calc
      (1 - x)⁻¹ʳ - 1 - x = ((1 + x) + x ^ 2 * (1 - x)⁻¹ʳ) - 1 - x := by rw [← h2]
      _ = x ^ 2 * (1 - x)⁻¹ʳ := by abel
  have hrem_bound : ‖(1 - x)⁻¹ʳ - 1 - x‖ ≤ ‖x‖ ^ 2 / (1 - ‖x‖) := by
    rw [hrem, div_eq_mul_inv]
    calc
      ‖x ^ 2 * (1 - x)⁻¹ʳ‖ ≤ ‖x ^ 2‖ * ‖(1 - x)⁻¹ʳ‖ := norm_mul_le _ _
      _ ≤ ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ :=
        mul_le_mul (norm_pow_le x 2) hnorm_inv (norm_nonneg _) (pow_nonneg (norm_nonneg x) 2)
  exact ⟨hu, hnorm_sum, hhasSum, hmul, hnorm_inv, hrem_bound⟩

omit [NormedAlgebra ℂ A] in
/-- **18.3 (Theorem: Neumann expansion and quadratic remainder):**
If `x : A` satisfies `‖x‖ < 1`, then `1 + x` is invertible, the Neumann series
`∑_{n=0}^∞ (-x)^n` converges absolutely to `(1 + x)⁻¹ʳ`, and
`‖(1 + x)⁻¹ʳ - 1 + x‖ ≤ ‖x‖ ^ 2 / (1 - ‖x‖)`. -/
theorem theorem18_3 {x : A} (hx : ‖x‖ < 1) :
    IsUnit (1 + x) ∧
    Summable (fun n : ℕ => ‖(-x) ^ n‖) ∧
    HasSum (fun n : ℕ => (-x) ^ n) ((1 + x)⁻¹ʳ) ∧
    ((1 + x) * (1 + x)⁻¹ʳ = 1 ∧ (1 + x)⁻¹ʳ * (1 + x) = 1) ∧
    ‖(1 + x)⁻¹ʳ‖ ≤ (1 - ‖x‖)⁻¹ ∧
    ‖(1 + x)⁻¹ʳ - 1 + x‖ ≤ ‖x‖ ^ 2 / (1 - ‖x‖) := by
  have hnx : ‖-x‖ < 1 := by simpa only [norm_neg] using hx
  obtain ⟨hu, hsum_norm, hhasSum, hmul, hnorm_inv, hrem⟩ := theorem18_3_one_sub hnx
  have heq : 1 - (-x) = 1 + x := sub_neg_eq_add 1 x
  have hsub_eq : (1 + x)⁻¹ʳ - 1 - (-x) = (1 + x)⁻¹ʳ - 1 + x := sub_neg_eq_add _ x
  rw [heq] at hu hhasSum hmul hnorm_inv hrem
  rw [norm_neg] at hnorm_inv hrem
  rw [hsub_eq] at hrem
  exact ⟨hu, hsum_norm, hhasSum, hmul, hnorm_inv, hrem⟩

omit [NormedAlgebra ℂ A] in
/-- Perturbation bound of `18.4` under the inequality `‖x⁻¹ʳ‖ ≤ 1 / α`. -/
theorem theorem18_4_le {x h : A} (hx : IsUnit x) {α : ℝ} (hα : 0 < α)
    (hxinv : ‖x⁻¹ʳ‖ ≤ 1 / α) (hh : ‖h‖ < α) :
    IsUnit (x + h) ∧
    ‖(x + h)⁻¹ʳ - x⁻¹ʳ + x⁻¹ʳ * h * x⁻¹ʳ‖ ≤ ‖h‖ ^ 2 / (α ^ 2 * (α - ‖h‖)) := by
  rcases hx with ⟨ux, rfl⟩
  have hux_inv : (ux : A)⁻¹ʳ = ↑ux⁻¹ := Ring.inverse_unit ux
  let u : A := (ux : A)⁻¹ʳ * h
  have hu_le : ‖u‖ ≤ ‖h‖ / α := by
    calc
      ‖u‖ ≤ ‖(ux : A)⁻¹ʳ‖ * ‖h‖ := norm_mul_le _ _
      _ ≤ (1 / α) * ‖h‖ := mul_le_mul_of_nonneg_right hxinv (norm_nonneg h)
      _ = ‖h‖ / α := one_div_mul_eq_div α ‖h‖
  have hdiv_lt : ‖h‖ / α < 1 := (div_lt_one hα).mpr hh
  have hu_lt : ‖u‖ < 1 := hu_le.trans_lt hdiv_lt
  obtain ⟨hu_unit, -, -, hu_mul, -, hu_rem⟩ := theorem18_3 hu_lt
  have hfac : (ux : A) + h = (ux : A) * (1 + u) := by
    dsimp [u]
    rw [mul_add, mul_one, hux_inv, ← mul_assoc, ux.mul_inv, one_mul]
  have hxh_unit : IsUnit ((ux : A) + h) := by
    rw [hfac]
    exact ux.isUnit.mul hu_unit
  rcases hu_unit with ⟨uu, huu⟩
  have huu_inv : (1 + u)⁻¹ʳ = ↑uu⁻¹ := by
    rw [← huu, Ring.inverse_unit]
  have hxh_inv : ((ux : A) + h)⁻¹ʳ = (1 + u)⁻¹ʳ * (ux : A)⁻¹ʳ := by
    have hprod : ((ux * uu : Aˣ) : A) = (ux : A) + h := by
      rw [Units.val_mul, huu, ← hfac]
    rw [← hprod, Ring.inverse_unit, mul_inv_rev, Units.val_mul, ← huu_inv, ← hux_inv]
  have hdiff_id :
      ((ux : A) + h)⁻¹ʳ - (ux : A)⁻¹ʳ + (ux : A)⁻¹ʳ * h * (ux : A)⁻¹ʳ =
        ((1 + u)⁻¹ʳ - 1 + u) * (ux : A)⁻¹ʳ := by
    rw [hxh_inv]
    dsimp [u]
    noncomm_ring
  refine ⟨hxh_unit, ?_⟩
  have hsub_pos : 0 < α - ‖h‖ := sub_pos.mpr hh
  have h1_sub_div_pos : 0 < 1 - ‖h‖ / α := sub_pos.mpr hdiv_lt
  have h1_sub_u_pos : 0 < 1 - ‖u‖ := sub_pos.mpr hu_lt
  have hquot_mono : ‖u‖ ^ 2 / (1 - ‖u‖) ≤ (‖h‖ / α) ^ 2 / (1 - ‖h‖ / α) := by
    have hnum : ‖u‖ ^ 2 ≤ (‖h‖ / α) ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hu_le 2
    have hden : 1 - ‖h‖ / α ≤ 1 - ‖u‖ := sub_le_sub_left hu_le 1
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul hnum ((inv_le_inv₀ h1_sub_u_pos h1_sub_div_pos).mpr hden)
      (inv_nonneg.mpr h1_sub_u_pos.le) (sq_nonneg _)
  have halg : ((‖h‖ / α) ^ 2 / (1 - ‖h‖ / α)) * (1 / α) = ‖h‖ ^ 2 / (α ^ 2 * (α - ‖h‖)) := by
    have hα_ne : α ≠ 0 := hα.ne'
    have hsub_ne : α - ‖h‖ ≠ 0 := hsub_pos.ne'
    field_simp [hα_ne, hsub_ne]
  rw [hdiff_id]
  calc
    ‖((1 + u)⁻¹ʳ - 1 + u) * (ux : A)⁻¹ʳ‖
        ≤ ‖(1 + u)⁻¹ʳ - 1 + u‖ * ‖(ux : A)⁻¹ʳ‖ := norm_mul_le _ _
    _ ≤ (‖u‖ ^ 2 / (1 - ‖u‖)) * (1 / α) :=
        mul_le_mul hu_rem hxinv (norm_nonneg _) (div_nonneg (sq_nonneg _) h1_sub_u_pos.le)
    _ ≤ ((‖h‖ / α) ^ 2 / (1 - ‖h‖ / α)) * (1 / α) :=
        mul_le_mul_of_nonneg_right hquot_mono (by positivity)
    _ = ‖h‖ ^ 2 / (α ^ 2 * (α - ‖h‖)) := halg

omit [NormedAlgebra ℂ A] in
/-- **18.4 (Theorem: Invertibility under perturbation and remainder bound):**
Suppose `x : A` is invertible, `0 < α`, `‖x⁻¹ʳ‖ = 1 / α`, and `h : A` satisfies `β = ‖h‖ < α`.
Then `x + h` is invertible and
`‖(x + h)⁻¹ʳ - x⁻¹ʳ + x⁻¹ʳ * h * x⁻¹ʳ‖ ≤ ‖h‖ ^ 2 / (α ^ 2 * (α - ‖h‖))`. -/
theorem theorem18_4 {x h : A} (hx : IsUnit x) {α : ℝ} (hα : 0 < α)
    (hxinv : ‖x⁻¹ʳ‖ = 1 / α) (hh : ‖h‖ < α) :
    IsUnit (x + h) ∧
    ‖(x + h)⁻¹ʳ - x⁻¹ʳ + x⁻¹ʳ * h * x⁻¹ʳ‖ ≤ ‖h‖ ^ 2 / (α ^ 2 * (α - ‖h‖)) :=
  theorem18_4_le hx hα hxinv.le hh

omit [NormedAlgebra ℂ A] in
/-- Specialization of `18.4` with `α = ‖x⁻¹ʳ‖⁻¹` (always positive since `x⁻¹ʳ` is a unit in a
nontrivial normed algebra). -/
theorem theorem18_4_inv_norm {x h : A} (hx : IsUnit x) (hh : ‖h‖ < ‖x⁻¹ʳ‖⁻¹) :
    0 < ‖x⁻¹ʳ‖⁻¹ ∧
    IsUnit (x + h) ∧
    ‖(x + h)⁻¹ʳ - x⁻¹ʳ + x⁻¹ʳ * h * x⁻¹ʳ‖ ≤
      ‖h‖ ^ 2 / ((‖x⁻¹ʳ‖⁻¹) ^ 2 * (‖x⁻¹ʳ‖⁻¹ - ‖h‖)) := by
  have : Nontrivial A := NormOneClass.nontrivial
  rcases hx with ⟨ux, rfl⟩
  have hpos_norm : 0 < ‖((ux : A)⁻¹ʳ)‖ := by
    rw [Ring.inverse_unit]
    exact Units.norm_pos ux⁻¹
  have hα : 0 < ‖((ux : A)⁻¹ʳ)‖⁻¹ := inv_pos.mpr hpos_norm
  have hxinv : ‖((ux : A)⁻¹ʳ)‖ = 1 / ‖((ux : A)⁻¹ʳ)‖⁻¹ := by
    rw [one_div, inv_inv]
  exact ⟨hα, theorem18_4 ux.isUnit hα hxinv hh⟩

/-- Self-homeomorphism of `invertibleElements A` given by two-sided inversion (`18.4` Corollary 1). -/
def invertibleHomeomorph (R : Type*) [NormedRing R] [CompleteSpace R] :
    invertibleElements R ≃ₜ invertibleElements R where
  toFun x := ⟨(x : R)⁻¹ʳ, by
    rcases x with ⟨_, ⟨u, rfl⟩⟩
    simp⟩
  invFun x := ⟨(x : R)⁻¹ʳ, by
    rcases x with ⟨_, ⟨u, rfl⟩⟩
    simp⟩
  left_inv x := by
    rcases x with ⟨_, ⟨u, rfl⟩⟩
    ext
    simp
  right_inv x := by
    rcases x with ⟨_, ⟨u, rfl⟩⟩
    ext
    simp
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    rw [continuous_iff_continuousAt]
    intro x
    have hc : ContinuousAt Ring.inverse (x : R) := by
      rcases x with ⟨_, ⟨u, rfl⟩⟩
      exact NormedRing.inverse_continuousAt u
    exact hc.comp continuous_subtype_val.continuousAt
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    rw [continuous_iff_continuousAt]
    intro x
    have hc : ContinuousAt Ring.inverse (x : R) := by
      rcases x with ⟨_, ⟨u, rfl⟩⟩
      exact NormedRing.inverse_continuousAt u
    exact hc.comp continuous_subtype_val.continuousAt

omit [NormedAlgebra ℂ A] [NormOneClass A] in
/-- **18.4 Corollary 1:** `invertibleElements A` is an open subset of `A`, `Ring.inverse` is
continuous at every invertible element, and `x ↦ x⁻¹ʳ` is a self-homeomorphism of
`invertibleElements A`. -/
theorem corollary18_4_1 :
    IsOpen (invertibleElements A) ∧
    (∀ x : A, IsUnit x → ContinuousAt Ring.inverse x) ∧
    (∀ x : invertibleElements A, (invertibleHomeomorph A x : A) = (x : A)⁻¹ʳ ∧
      invertibleHomeomorph A (invertibleHomeomorph A x) = x) := by
  refine ⟨Units.isOpen, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    exact NormedRing.inverse_continuousAt u
  · intro x
    exact ⟨rfl, (invertibleHomeomorph A).left_inv x⟩

omit [NormOneClass A] in
/-- **18.4 Corollary 2:** At every invertible element `x ∈ invertibleElements A`, inversion is
Fréchet differentiable over `ℂ` and its differential sends `h : A` to `- (x⁻¹ʳ * h * x⁻¹ʳ)`. -/
theorem corollary18_4_2 {x : A} (hx : IsUnit x) :
    HasFDerivAt Ring.inverse (- ContinuousLinearMap.mulLeftRight ℂ A (x⁻¹ʳ) (x⁻¹ʳ)) x ∧
    ∀ h : A, (- ContinuousLinearMap.mulLeftRight ℂ A (x⁻¹ʳ) (x⁻¹ʳ)) h = - (x⁻¹ʳ * h * x⁻¹ʳ) := by
  rcases hx with ⟨u, rfl⟩
  rw [Ring.inverse_unit]
  refine ⟨hasFDerivAt_ringInverse (𝕜 := ℂ) u, fun h => ?_⟩
  simp [ContinuousLinearMap.mulLeftRight_apply, mul_assoc]

private theorem ring_inverse_neg {R : Type*} [Ring R] (a : R) : (-a)⁻¹ʳ = - (a⁻¹ʳ) := by
  by_cases ha : IsUnit a
  · rcases ha with ⟨u, rfl⟩
    change ((-u : Rˣ) : R)⁻¹ʳ = - ((u : R)⁻¹ʳ)
    rw [Ring.inverse_unit, Ring.inverse_unit]
    have hneg : (-u)⁻¹ = -(u⁻¹) := Units.ext (by simp)
    rw [hneg]
    rfl
  · have hna : ¬ IsUnit (-a) := fun h => ha (by simpa using h.neg)
    rw [Ring.inverse_non_unit a ha, Ring.inverse_non_unit (-a) hna, neg_zero]

/-- **18.4 Corollary 3:** If `‖x‖ < ‖z‖`, then `z ∉ spectrum ℂ x` and the resolvent has the
convergent Neumann–Laurent expansion `(algebraMap ℂ A z - x)⁻¹ʳ = ∑_{n=0}^∞ z^{-(n+1)} x^n`
(equivalently `(x - algebraMap ℂ A z)⁻¹ʳ = - ∑_{n=0}^∞ z^{-(n+1)} x^n`); consequently
`∀ z ∈ spectrum ℂ x, ‖z‖ ≤ ‖x‖`, and `spectrum ℂ x` is closed, bounded, and compact in `ℂ`. -/
theorem corollary18_4_3 (x : A) :
    (∀ z : ℂ, ‖x‖ < ‖z‖ →
      z ∉ spectrum ℂ x ∧
      IsUnit (algebraMap ℂ A z - x) ∧
      IsUnit (x - algebraMap ℂ A z) ∧
      HasSum (fun n : ℕ => (z⁻¹ ^ (n + 1)) • x ^ n) ((algebraMap ℂ A z - x)⁻¹ʳ) ∧
      HasSum (fun n : ℕ => - ((z⁻¹ ^ (n + 1)) • x ^ n)) ((x - algebraMap ℂ A z)⁻¹ʳ)) ∧
    (∀ z ∈ spectrum ℂ x, ‖z‖ ≤ ‖x‖) ∧
    IsClosed (spectrum ℂ x) ∧
    Bornology.IsBounded (spectrum ℂ x) ∧
    IsCompact (spectrum ℂ x) := by
  refine ⟨?_, fun z hz => spectrum.norm_le_norm_of_mem hz,
    spectrum.isClosed x, spectrum.isBounded x, spectrum.isCompact x⟩
  intro z hz
  have hz_pos : 0 < ‖z‖ := (norm_nonneg x).trans_lt hz
  have hz_ne : z ≠ 0 := norm_ne_zero_iff.mp hz_pos.ne'
  have hres : z ∈ resolventSet ℂ x := spectrum.mem_resolventSet_of_norm_lt hz
  have hnot_mem : z ∉ spectrum ℂ x := by rwa [spectrum.notMem_iff]
  have hu1 : IsUnit (algebraMap ℂ A z - x) := hres
  have hneg_eq : x - algebraMap ℂ A z = -(algebraMap ℂ A z - x) := by abel
  have hu2 : IsUnit (x - algebraMap ℂ A z) := by rw [hneg_eq]; exact hu1.neg
  have hnorm_smul : ‖z⁻¹ • x‖ < 1 := by
    rw [norm_smul, norm_inv]
    exact (inv_mul_lt_iff₀' hz_pos).mpr (by simpa using hz)
  obtain ⟨hu_sub, -, hhas_sub, -, -, -⟩ := theorem18_3_one_sub hnorm_smul
  have hfac : algebraMap ℂ A z - x = z • (1 - z⁻¹ • x) := by
    rw [Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul, mul_inv_cancel₀ hz_ne, one_smul]
  let uz : Aˣ := Units.map (algebraMap ℂ A).toMonoidHom (Units.mk0 z hz_ne)
  rcases hu_sub with ⟨usub, husub⟩
  have hprod_val : ((uz * usub : Aˣ) : A) = algebraMap ℂ A z - x := by
    rw [Units.val_mul, husub]
    change algebraMap ℂ A z * (1 - z⁻¹ • x) = algebraMap ℂ A z - x
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← hfac,
      Algebra.algebraMap_eq_smul_one]
  have hinv_id : (algebraMap ℂ A z - x)⁻¹ʳ = z⁻¹ • (1 - z⁻¹ • x)⁻¹ʳ := by
    have huz_inv : (↑uz⁻¹ : A) = algebraMap ℂ A z⁻¹ := by
      simp [uz]
    have husub_inv : (1 - z⁻¹ • x)⁻¹ʳ = ↑usub⁻¹ := by
      rw [← husub, Ring.inverse_unit]
    rw [← hprod_val, Ring.inverse_unit, mul_inv_rev, Units.val_mul, huz_inv, ← husub_inv,
      ← Algebra.commutes z⁻¹ ((1 - z⁻¹ • x)⁻¹ʳ), Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul]
  have hhas1 : HasSum (fun n : ℕ => (z⁻¹ ^ (n + 1)) • x ^ n) ((algebraMap ℂ A z - x)⁻¹ʳ) := by
    rw [hinv_id]
    have hsmul := hhas_sub.const_smul z⁻¹
    refine hsmul.congr_fun fun n => ?_
    rw [smul_pow, smul_smul, ← pow_succ']
  have hhas2 : HasSum (fun n : ℕ => - ((z⁻¹ ^ (n + 1)) • x ^ n)) ((x - algebraMap ℂ A z)⁻¹ʳ) := by
    rw [hneg_eq, ring_inverse_neg]
    exact hhas1.neg
  exact ⟨hnot_mem, hu1, hu2, hhas1, hhas2⟩

/-- **18.5 (Theorem: Scalarized resolvent holomorphy and decay at infinity):**
For every `x : A` and every continuous linear functional `Φ : StrongDual ℂ A`:
1. On the open set `Ω = (spectrum ℂ x)ᶜ = resolventSet ℂ x`, both scalarized resolvents
   `z ↦ Φ ((algebraMap ℂ A z - x)⁻¹ʳ)` and `z ↦ Φ ((x - algebraMap ℂ A z)⁻¹ʳ)` are holomorphic
   (`DifferentiableOn ℂ`), with derivatives `- Φ (((algebraMap ℂ A z - x)⁻¹ʳ) ^ 2)` and
   `Φ (((x - algebraMap ℂ A z)⁻¹ʳ) ^ 2)` respectively;
2. For `‖x‖ < ‖z‖`, `‖(algebraMap ℂ A z - x)⁻¹ʳ‖ ≤ (‖z‖ - ‖x‖)⁻¹` and
   `‖(x - algebraMap ℂ A z)⁻¹ʳ‖ ≤ (‖z‖ - ‖x‖)⁻¹`;
3. Both scalarized resolvents tend to `0` as `z → ∞` (`Bornology.cobounded ℂ`). -/
theorem theorem18_5 (x : A) (Φ : StrongDual ℂ A) :
    IsOpen (spectrum ℂ x)ᶜ ∧
    DifferentiableOn ℂ (fun z : ℂ => Φ ((algebraMap ℂ A z - x)⁻¹ʳ)) (spectrum ℂ x)ᶜ ∧
    DifferentiableOn ℂ (fun z : ℂ => Φ ((x - algebraMap ℂ A z)⁻¹ʳ)) (spectrum ℂ x)ᶜ ∧
    (∀ z ∈ (spectrum ℂ x)ᶜ,
      HasDerivAt (fun w : ℂ => Φ ((algebraMap ℂ A w - x)⁻¹ʳ))
        (- Φ (((algebraMap ℂ A z - x)⁻¹ʳ) ^ 2)) z ∧
      HasDerivAt (fun w : ℂ => Φ ((x - algebraMap ℂ A w)⁻¹ʳ))
        (Φ (((x - algebraMap ℂ A z)⁻¹ʳ) ^ 2)) z) ∧
    (∀ z : ℂ, ‖x‖ < ‖z‖ →
      ‖(algebraMap ℂ A z - x)⁻¹ʳ‖ ≤ (‖z‖ - ‖x‖)⁻¹ ∧
      ‖(x - algebraMap ℂ A z)⁻¹ʳ‖ ≤ (‖z‖ - ‖x‖)⁻¹ ∧
      ‖Φ ((x - algebraMap ℂ A z)⁻¹ʳ)‖ ≤ ‖Φ‖ * (‖z‖ - ‖x‖)⁻¹) ∧
    Tendsto (fun z : ℂ => Φ ((algebraMap ℂ A z - x)⁻¹ʳ)) (Bornology.cobounded ℂ) (𝓝 0) ∧
    Tendsto (fun z : ℂ => Φ ((x - algebraMap ℂ A z)⁻¹ʳ)) (Bornology.cobounded ℂ) (𝓝 0) := by
  have hcompl : (spectrum ℂ x)ᶜ = resolventSet ℂ x := compl_compl (resolventSet ℂ x)
  have hopen : IsOpen (spectrum ℂ x)ᶜ := hcompl.symm ▸ spectrum.isOpen_resolventSet x
  have hneg_inv : ∀ w : ℂ, (x - algebraMap ℂ A w)⁻¹ʳ = - (algebraMap ℂ A w - x)⁻¹ʳ := by
    intro w
    have hsub : x - algebraMap ℂ A w = -(algebraMap ℂ A w - x) := by abel
    rw [hsub, ring_inverse_neg]
  have hderiv : ∀ z ∈ (spectrum ℂ x)ᶜ,
      HasDerivAt (fun w : ℂ => Φ ((algebraMap ℂ A w - x)⁻¹ʳ))
        (- Φ (((algebraMap ℂ A z - x)⁻¹ʳ) ^ 2)) z ∧
      HasDerivAt (fun w : ℂ => Φ ((x - algebraMap ℂ A w)⁻¹ʳ))
        (Φ (((x - algebraMap ℂ A z)⁻¹ʳ) ^ 2)) z := by
    intro z hz
    have hz' : z ∈ resolventSet ℂ x := hcompl ▸ hz
    have hd0 : HasDerivAt (resolvent x) (- resolvent x z ^ 2) z :=
      spectrum.hasDerivAt_resolvent_const_left hz'
    have hd1 : HasDerivAt (fun w : ℂ => Φ ((algebraMap ℂ A w - x)⁻¹ʳ))
        (- Φ (((algebraMap ℂ A z - x)⁻¹ʳ) ^ 2)) z := by
      simpa only [resolvent, Function.comp_def, map_neg] using Φ.hasFDerivAt.comp_hasDerivAt z hd0
    have hd2 : HasDerivAt (fun w : ℂ => Φ ((x - algebraMap ℂ A w)⁻¹ʳ))
        (Φ (((x - algebraMap ℂ A z)⁻¹ʳ) ^ 2)) z := by
      have hfun : (fun w : ℂ => Φ ((x - algebraMap ℂ A w)⁻¹ʳ)) =
          fun w : ℂ => - Φ ((algebraMap ℂ A w - x)⁻¹ʳ) := by
        ext w
        rw [hneg_inv w, map_neg]
      have hval : Φ (((x - algebraMap ℂ A z)⁻¹ʳ) ^ 2) =
          - (- Φ (((algebraMap ℂ A z - x)⁻¹ʳ) ^ 2)) := by
        rw [neg_neg, hneg_inv z, neg_sq]
      rw [hfun, hval]
      exact hd1.neg
    exact ⟨hd1, hd2⟩
  have hdiff1 : DifferentiableOn ℂ (fun z : ℂ => Φ ((algebraMap ℂ A z - x)⁻¹ʳ)) (spectrum ℂ x)ᶜ :=
    fun z hz => (hderiv z hz).1.differentiableAt.differentiableWithinAt
  have hdiff2 : DifferentiableOn ℂ (fun z : ℂ => Φ ((x - algebraMap ℂ A z)⁻¹ʳ)) (spectrum ℂ x)ᶜ :=
    fun z hz => (hderiv z hz).2.differentiableAt.differentiableWithinAt
  have hbound : ∀ z : ℂ, ‖x‖ < ‖z‖ →
      ‖(algebraMap ℂ A z - x)⁻¹ʳ‖ ≤ (‖z‖ - ‖x‖)⁻¹ ∧
      ‖(x - algebraMap ℂ A z)⁻¹ʳ‖ ≤ (‖z‖ - ‖x‖)⁻¹ ∧
      ‖Φ ((x - algebraMap ℂ A z)⁻¹ʳ)‖ ≤ ‖Φ‖ * (‖z‖ - ‖x‖)⁻¹ := by
    intro z hz
    have hz_pos : 0 < ‖z‖ := (norm_nonneg x).trans_lt hz
    obtain ⟨-, -, -, hhas1, -⟩ := (corollary18_4_3 x).1 z hz
    have hgeom : Summable (fun n : ℕ => (‖z‖⁻¹ * ‖x‖) ^ n) := by
      apply summable_geometric_of_lt_one (by positivity)
      exact (inv_mul_lt_iff₀' hz_pos).mpr (by simpa using hz)
    have hterm_le : ∀ n : ℕ, ‖(z⁻¹ ^ (n + 1)) • x ^ n‖ ≤ ‖z‖⁻¹ * (‖z‖⁻¹ * ‖x‖) ^ n := by
      intro n
      rw [norm_smul, norm_pow, norm_inv, pow_succ', mul_pow, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_pow_le x n) (pow_nonneg (inv_nonneg.mpr hz_pos.le) n))
        (inv_nonneg.mpr hz_pos.le)
    have hsum_maj : Summable (fun n : ℕ => ‖z‖⁻¹ * (‖z‖⁻¹ * ‖x‖) ^ n) := hgeom.mul_left ‖z‖⁻¹
    have hsum_norm : Summable (fun n : ℕ => ‖(z⁻¹ ^ (n + 1)) • x ^ n‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le hsum_maj
    have hb1 : ‖(algebraMap ℂ A z - x)⁻¹ʳ‖ ≤ (‖z‖ - ‖x‖)⁻¹ := by
      rw [← hhas1.tsum_eq]
      calc
        ‖∑' n : ℕ, (z⁻¹ ^ (n + 1)) • x ^ n‖
            ≤ ∑' n : ℕ, ‖(z⁻¹ ^ (n + 1)) • x ^ n‖ := norm_tsum_le_tsum_norm hsum_norm
        _ ≤ ∑' n : ℕ, ‖z‖⁻¹ * (‖z‖⁻¹ * ‖x‖) ^ n := hsum_norm.tsum_le_tsum hterm_le hsum_maj
        _ = ‖z‖⁻¹ * (1 - ‖z‖⁻¹ * ‖x‖)⁻¹ := by
            rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity)
              ((inv_mul_lt_iff₀' hz_pos).mpr (by simpa using hz))]
        _ = (‖z‖ - ‖x‖)⁻¹ := by
            have hsub_ne : ‖z‖ - ‖x‖ ≠ 0 := (sub_pos.mpr hz).ne'
            field_simp [hz_pos.ne', hsub_ne]
    have hb2 : ‖(x - algebraMap ℂ A z)⁻¹ʳ‖ ≤ (‖z‖ - ‖x‖)⁻¹ := by
      rwa [hneg_inv z, norm_neg]
    exact ⟨hb1, hb2, (Φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb2 (norm_nonneg Φ))⟩
  have htend0 : Tendsto (resolvent x) (Bornology.cobounded ℂ) (𝓝 0) :=
    spectrum.resolvent_tendsto_cobounded x
  have htend1 : Tendsto (fun z : ℂ => Φ ((algebraMap ℂ A z - x)⁻¹ʳ))
      (Bornology.cobounded ℂ) (𝓝 0) := by
    simpa only [resolvent, Function.comp_def, map_zero] using
      (Φ.continuous.tendsto 0).comp htend0
  have htend2 : Tendsto (fun z : ℂ => Φ ((x - algebraMap ℂ A z)⁻¹ʳ))
      (Bornology.cobounded ℂ) (𝓝 0) := by
    simpa only [hneg_inv, map_neg, neg_zero] using htend1.neg
  exact ⟨hopen, hdiff1, hdiff2, hderiv, hbound, htend1, htend2⟩

/-- **18.6 (Theorem: Spectrum compactness and nonemptiness):**
For every element `x` of a complex Banach algebra `A`, `spectrum ℂ x` is a nonempty compact
subset of `ℂ` contained in `{z : ℂ | ‖z‖ ≤ ‖x‖}`, and `1 - z • x` is invertible whenever
`‖z‖ * sup_{w ∈ σ(x)} ‖w‖ < 1` (in particular for `‖z‖ < (sup_{w ∈ σ(x)} ‖w‖)⁻¹` when that
supremum is positive). -/
theorem theorem18_6 (x : A) :
    IsCompact (spectrum ℂ x) ∧
    (spectrum ℂ x).Nonempty ∧
    (∀ z ∈ spectrum ℂ x, ‖z‖ ≤ ‖x‖) ∧
    (∀ z : ℂ, ‖z‖ * sSup ((fun w : ℂ => ‖w‖) '' spectrum ℂ x) < 1 → IsUnit (1 - z • x)) ∧
    (0 < sSup ((fun w : ℂ => ‖w‖) '' spectrum ℂ x) →
      ∀ z : ℂ, ‖z‖ < (sSup ((fun w : ℂ => ‖w‖) '' spectrum ℂ x))⁻¹ → IsUnit (1 - z • x)) := by
  have : Nontrivial A := NormOneClass.nontrivial
  have hcomp : IsCompact (spectrum ℂ x) := spectrum.isCompact x
  have hbdd : BddAbove ((fun w : ℂ => ‖w‖) '' spectrum ℂ x) :=
    (hcomp.image continuous_norm).bddAbove
  have hunit : ∀ z : ℂ,
      ‖z‖ * sSup ((fun w : ℂ => ‖w‖) '' spectrum ℂ x) < 1 → IsUnit (1 - z • x) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      simp [isUnit_one]
    · have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hnot : z⁻¹ ∉ spectrum ℂ x := by
        intro hmem
        have hle : ‖z⁻¹‖ ≤ sSup ((fun w : ℂ => ‖w‖) '' spectrum ℂ x) :=
          le_csSup hbdd ⟨z⁻¹, hmem, rfl⟩
        have hmul : 1 ≤ ‖z‖ * sSup ((fun w : ℂ => ‖w‖) '' spectrum ℂ x) := by
          calc
            (1 : ℝ) = ‖z‖ * ‖z⁻¹‖ := by rw [norm_inv, mul_inv_cancel₀ hz_pos.ne']
            _ ≤ ‖z‖ * sSup ((fun w : ℂ => ‖w‖) '' spectrum ℂ x) :=
              mul_le_mul_of_nonneg_left hle hz_pos.le
        exact (hmul.trans_lt hz).false
      have hu_res : IsUnit (algebraMap ℂ A z⁻¹ - x) := by
        rwa [spectrum.notMem_iff] at hnot
      have hu_z : IsUnit (algebraMap ℂ A z) := (Units.mk0 z hz0).isUnit.map (algebraMap ℂ A)
      have hprod_eq : algebraMap ℂ A z * (algebraMap ℂ A z⁻¹ - x) = 1 - z • x := by
        rw [mul_sub, ← map_mul, mul_inv_cancel₀ hz0, map_one, Algebra.algebraMap_eq_smul_one,
          smul_mul_assoc, one_mul]
      exact hprod_eq ▸ hu_z.mul hu_res
  refine ⟨hcomp, spectrum.nonempty x, fun _ hz => spectrum.norm_le_norm_of_mem hz, hunit, ?_⟩
  intro hpos z hz
  apply hunit
  calc
    ‖z‖ * sSup ((fun w : ℂ => ‖w‖) '' spectrum ℂ x)
        < (sSup ((fun w : ℂ => ‖w‖) '' spectrum ℂ x))⁻¹ *
          sSup ((fun w : ℂ => ‖w‖) '' spectrum ℂ x) :=
      mul_lt_mul_of_pos_right hz hpos
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- Canonical `ℂ`-algebra isomorphism `ℂ ≃ₐ[ℂ] A` in the Gelfand–Mazur theorem (`18.7`). -/
def gelfandMazurAlgEquiv (hdiv : ∀ x : A, x ≠ 0 → IsUnit x) : ℂ ≃ₐ[ℂ] A :=
  have : Nontrivial A := NormOneClass.nontrivial
  NormedRing.algEquivComplexOfComplete fun {a} =>
    ⟨fun ha h0 => not_isUnit_zero (h0 ▸ ha), hdiv a⟩

/-- **18.7 (Theorem: Complex Banach division algebra isometric classification — Gelfand–Mazur):**
If `A` is a complex Banach algebra (not assumed commutative) in which every nonzero element is
invertible, then for every `x : A` there is a unique `z : ℂ` with `x = algebraMap ℂ A z`, one has
`‖x‖ = ‖z‖`, and `algebraMap ℂ A` induces an **isometric** `ℂ`-algebra isomorphism `ℂ ≃ₐ[ℂ] A`. -/
theorem theorem18_7 (hdiv : ∀ x : A, x ≠ 0 → IsUnit x) :
    (∀ x : A, ∃! z : ℂ, x = algebraMap ℂ A z) ∧
    (∀ (x : A) (z : ℂ), x = algebraMap ℂ A z → ‖x‖ = ‖z‖) ∧
    (∀ z : ℂ, gelfandMazurAlgEquiv hdiv z = algebraMap ℂ A z) ∧
    Isometry (gelfandMazurAlgEquiv hdiv) ∧
    (∀ z : ℂ, ‖gelfandMazurAlgEquiv hdiv z‖ = ‖z‖) ∧
    (∀ x : A, ‖(gelfandMazurAlgEquiv hdiv).symm x‖ = ‖x‖) := by
  let e := gelfandMazurAlgEquiv hdiv
  have he_apply : ∀ z : ℂ, e z = algebraMap ℂ A z := fun _ => rfl
  have hnorm_map : ∀ z : ℂ, ‖e z‖ = ‖z‖ := by
    intro z
    rw [he_apply, Algebra.algebraMap_eq_smul_one, norm_smul, norm_one, mul_one]
  have hiso : Isometry e := AddMonoidHomClass.isometry_of_norm e hnorm_map
  refine ⟨?_, ?_, he_apply, hiso, hnorm_map, ?_⟩
  · intro x
    refine ⟨e.symm x, (e.apply_symm_apply x).symm, ?_⟩
    intro z hz
    apply e.injective
    rw [e.apply_symm_apply, he_apply, ← hz]
  · intro x z hxz
    rw [hxz, ← he_apply, hnorm_map]
  · intro x
    calc
      ‖e.symm x‖ = ‖e (e.symm x)‖ := (hnorm_map (e.symm x)).symm
      _ = ‖x‖ := by rw [e.apply_symm_apply]

/-- **18.8 (Definition: Real spectral radius):**
For `x : A`, `rudinSpectralRadius x = sup { ‖z‖ : z ∈ spectrum ℂ x }`. -/
def rudinSpectralRadius {R : Type*} [Ring R] [Algebra ℂ R] (x : R) : ℝ :=
  sSup ((fun z : ℂ => ‖z‖) '' spectrum ℂ x)

/-- **18.8 (Properties of the spectral radius and bridge to Mathlib's `spectralRadius`):**
For every `x : A`, `0 ≤ rudinSpectralRadius x ≤ ‖x‖`, `∀ z ∈ spectrum ℂ x, ‖z‖ ≤ rudinSpectralRadius x`,
the supremum is attained on `spectrum ℂ x`, and `ENNReal.ofReal (rudinSpectralRadius x) = spectralRadius ℂ x`. -/
theorem theorem18_8 (x : A) :
    0 ≤ rudinSpectralRadius x ∧
    rudinSpectralRadius x ≤ ‖x‖ ∧
    (∀ z ∈ spectrum ℂ x, ‖z‖ ≤ rudinSpectralRadius x) ∧
    (∃ z ∈ spectrum ℂ x, ‖z‖ = rudinSpectralRadius x) ∧
    ENNReal.ofReal (rudinSpectralRadius x) = spectralRadius ℂ x ∧
    (spectralRadius ℂ x).toReal = rudinSpectralRadius x := by
  have : Nontrivial A := NormOneClass.nontrivial
  have hcomp : IsCompact (spectrum ℂ x) := spectrum.isCompact x
  have hne : (spectrum ℂ x).Nonempty := spectrum.nonempty x
  have himg_comp : IsCompact ((fun z : ℂ => ‖z‖) '' spectrum ℂ x) :=
    hcomp.image continuous_norm
  have himg_ne : ((fun z : ℂ => ‖z‖) '' spectrum ℂ x).Nonempty := hne.image _
  have hbdd : BddAbove ((fun z : ℂ => ‖z‖) '' spectrum ℂ x) := himg_comp.bddAbove
  have hmem_le : ∀ z ∈ spectrum ℂ x, ‖z‖ ≤ rudinSpectralRadius x :=
    fun z hz => le_csSup hbdd ⟨z, hz, rfl⟩
  obtain ⟨z₀, hz₀⟩ := hne
  have hnonneg : 0 ≤ rudinSpectralRadius x :=
    (norm_nonneg z₀).trans (hmem_le z₀ hz₀)
  have hle_norm : rudinSpectralRadius x ≤ ‖x‖ :=
    csSup_le himg_ne (by rintro _ ⟨z, hz, rfl⟩; exact spectrum.norm_le_norm_of_mem hz)
  obtain ⟨r, ⟨z_max, hz_max, rfl⟩, hmax⟩ :=
    himg_comp.exists_isMaxOn himg_ne continuousOn_id
  have hattain : ‖z_max‖ = rudinSpectralRadius x :=
    le_antisymm (hmem_le z_max hz_max) (csSup_le himg_ne fun y hy => hmax hy)
  have hbridge : ENNReal.ofReal (rudinSpectralRadius x) = spectralRadius ℂ x := by
    rw [spectralRadius_eq_of_unital]
    apply le_antisymm
    · rw [← hattain]
      have h1 : ENNReal.ofReal ‖z_max‖ = (‖z_max‖₊ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg z_max)]
        congr 1
      rw [h1]
      exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ x) => (‖k‖₊ : ℝ≥0∞)) z_max hz_max
    · refine iSup₂_le fun z hz => ?_
      have h1 : (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ := by
        rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg z)]
        congr 1
      rw [h1]
      exact ENNReal.ofReal_le_ofReal (hmem_le z hz)
  have htoReal : (spectralRadius ℂ x).toReal = rudinSpectralRadius x := by
    rw [← hbridge, ENNReal.toReal_ofReal hnonneg]
  exact ⟨hnonneg, hle_norm, hmem_le, ⟨z_max, hz_max, hattain⟩, hbridge, htoReal⟩

/-- **18.9 (Theorem: Spectral-radius limit formula — Gelfand's formula):**
For every `x : A`:
1. `rudinSpectralRadius x ≤ ‖x ^ n‖ ^ (1 / (n : ℝ))` for every integer `n ≥ 1`;
2. `lim_{n → ∞} ‖x ^ n‖ ^ (1 / n) = rudinSpectralRadius x`;
3. `rudinSpectralRadius x = inf_{n ≥ 1} ‖x ^ n‖ ^ (1 / n)`. -/
theorem theorem18_9 (x : A) :
    (∀ n : ℕ, 1 ≤ n → rudinSpectralRadius x ≤ ‖x ^ n‖ ^ (1 / (n : ℝ))) ∧
    Tendsto (fun n : ℕ => ‖x ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 (rudinSpectralRadius x)) ∧
    rudinSpectralRadius x = ⨅ n : {n : ℕ // 1 ≤ n}, ‖x ^ n.1‖ ^ (1 / (n.1 : ℝ)) := by
  have : Nontrivial A := NormOneClass.nontrivial
  obtain ⟨hnonneg, -, -, ⟨z_max, hz_max, hattain⟩, hbridge, -⟩ := theorem18_8 x
  have hle_pow : ∀ n : ℕ, 1 ≤ n → rudinSpectralRadius x ≤ ‖x ^ n‖ ^ (1 / (n : ℝ)) := by
    intro n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hz_pow : z_max ^ n ∈ spectrum ℂ (x ^ n) := by
      rw [spectrum.map_pow x n]
      exact ⟨z_max, hz_max, rfl⟩
    have hnorm_pow : ‖z_max‖ ^ n ≤ ‖x ^ n‖ := by
      simpa only [norm_pow] using spectrum.norm_le_norm_of_mem hz_pow
    rw [← hattain]
    calc
      ‖z_max‖ = (‖z_max‖ ^ (n : ℝ)) ^ (1 / (n : ℝ)) := by
        rw [← Real.rpow_mul (norm_nonneg z_max), mul_one_div_cancel hn_pos.ne', Real.rpow_one]
      _ = (‖z_max‖ ^ n) ^ (1 / (n : ℝ)) := by rw [Real.rpow_natCast]
      _ ≤ ‖x ^ n‖ ^ (1 / (n : ℝ)) :=
        Real.rpow_le_rpow (pow_nonneg (norm_nonneg z_max) n) hnorm_pow (by positivity)
  have htend : Tendsto (fun n : ℕ => ‖x ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 (rudinSpectralRadius x)) := by
    have henn := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius x
    rw [← hbridge] at henn
    have hto := (ENNReal.continuousAt_toReal ENNReal.ofReal_ne_top).tendsto.comp henn
    rw [ENNReal.toReal_ofReal hnonneg] at hto
    refine hto.congr' (Eventually.of_forall fun n => ?_)
    simp only [Function.comp_apply]
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)
  have hinf : rudinSpectralRadius x = ⨅ n : {n : ℕ // 1 ≤ n}, ‖x ^ n.1‖ ^ (1 / (n.1 : ℝ)) := by
    have : Nonempty {n : ℕ // 1 ≤ n} := ⟨⟨1, le_rfl⟩⟩
    have hbdd_below : BddBelow (Set.range fun n : {n : ℕ // 1 ≤ n} => ‖x ^ n.1‖ ^ (1 / (n.1 : ℝ))) :=
      ⟨rudinSpectralRadius x, by rintro _ ⟨n, rfl⟩; exact hle_pow n.1 n.2⟩
    apply le_antisymm
    · exact le_ciInf fun n => hle_pow n.1 n.2
    · by_contra! hlt
      have hev := (tendsto_order.mp htend).2 _ hlt
      obtain ⟨N, hN⟩ := eventually_atTop.mp hev
      let M : ℕ := max N 1
      have hM1 : 1 ≤ M := le_max_right N 1
      have hMN : N ≤ M := le_max_left N 1
      have hle_inf : (⨅ n : {n : ℕ // 1 ≤ n}, ‖x ^ n.1‖ ^ (1 / (n.1 : ℝ))) ≤
          ‖x ^ M‖ ^ (1 / (M : ℝ)) :=
        ciInf_le hbdd_below ⟨M, hM1⟩
      exact (hle_inf.trans_lt (hN M hMN)).false
  exact ⟨hle_pow, htend, hinf⟩

/-- **18.10 (Remarks: Ambient-algebra spectrum comparison and spectral-radius invariance):**
Let `S` be a closed subalgebra of a complex Banach algebra `A` (carrying the inherited norm,
making `S` a complex Banach algebra with unit of norm `1`). For every `x : S`:
1. `(a)` Every unit in `S` is a unit in `A`, `spectrum ℂ (x : A) ⊆ spectrum ℂ x`,
   `frontier (spectrum ℂ x) ⊆ frontier (spectrum ℂ (x : A))`, and if `(spectrum ℂ (x : A))ᶜ` is
   connected (`IsPreconnected`), then `spectrum ℂ x = spectrum ℂ (x : A)`;
2. `(b)` Under the shared norm `‖(y : S)‖ = ‖(y : A)‖`, the spectral radius is unchanged:
   `rudinSpectralRadius x = rudinSpectralRadius (x : A)`. -/
theorem theorem18_10 (S : Subalgebra ℂ A) [hS : IsClosed (S : Set A)] (x : S) :
    (∀ y : S, IsUnit y → IsUnit (y : A)) ∧
    spectrum ℂ (x : A) ⊆ spectrum ℂ x ∧
    frontier (spectrum ℂ x) ⊆ frontier (spectrum ℂ (x : A)) ∧
    (IsPreconnected (spectrum ℂ (x : A))ᶜ → spectrum ℂ x = spectrum ℂ (x : A)) ∧
    rudinSpectralRadius x = rudinSpectralRadius (x : A) := by
  have : CompleteSpace S := hS.completeSpace_coe
  have : NormOneClass S := ⟨show ‖(1 : S)‖ = 1 from norm_one (α := A)⟩
  refine ⟨fun y hy => hy.map S.val,
    spectrum.subset_subalgebra x,
    Subalgebra.frontier_subset_frontier S x,
    Subalgebra.spectrum_eq_of_isPreconnected_compl S x,
    ?_⟩
  have htS := (theorem18_9 (A := S) x).2.1
  have htA := (theorem18_9 (A := A) (x : A)).2.1
  have heq : (fun n : ℕ => ‖x ^ n‖ ^ (1 / (n : ℝ))) =
      (fun n : ℕ => ‖(x : A) ^ n‖ ^ (1 / (n : ℝ))) := by
    ext n
    rfl
  rw [heq] at htS
  exact tendsto_nhds_unique htS htA

end NonCommutativeBanachAlgebra

/-! ## Section 1b: Example `18.11` — Circle Functions vs. the Disc Algebra -/

section DiscAlgebraExample

open RudinRCA.Chapter04 RudinRCA.Chapter05

/-- Zero-extension of `f : C(UnitDisc, ℂ)` to `ℂ`, used to express holomorphy on the open unit
disc `ball (0 : ℂ) 1`. -/
def discExtend (f : C(UnitDisc, ℂ)) (z : ℂ) : ℂ :=
  if hz : z ∈ UnitDisc then f ⟨z, hz⟩ else 0

@[simp]
theorem discExtend_of_mem (f : C(UnitDisc, ℂ)) {z : ℂ} (hz : z ∈ UnitDisc) :
    discExtend f z = f ⟨z, hz⟩ := by
  simp [discExtend, hz]

@[simp]
theorem discExtend_coe (f : C(UnitDisc, ℂ)) (z : UnitDisc) :
    discExtend f (z : ℂ) = f z :=
  discExtend_of_mem f z.property

/-- **18.11 (`DiscAlgebra`):** The disc algebra `A(D̄) ⊆ C(UnitDisc, ℂ)` consisting of continuous
functions on the closed unit disc `UnitDisc = closedBall (0 : ℂ) 1` that are holomorphic on the
open unit disc `ball (0 : ℂ) 1`. -/
def DiscAlgebra : Subalgebra ℂ C(UnitDisc, ℂ) where
  carrier := {f : C(UnitDisc, ℂ) | DifferentiableOn ℂ (discExtend f) (ball (0 : ℂ) 1)}
  mul_mem' {f g} hf hg :=
    (hf.mul hg).congr fun z hz => by
      have hzd : z ∈ UnitDisc := ball_subset_closedBall hz
      simp [hzd]
  one_mem' :=
    (differentiableOn_const (1 : ℂ)).congr fun z hz => by
      have hzd : z ∈ UnitDisc := ball_subset_closedBall hz
      simp [hzd]
  add_mem' {f g} hf hg :=
    (hf.add hg).congr fun z hz => by
      have hzd : z ∈ UnitDisc := ball_subset_closedBall hz
      simp [hzd]
  zero_mem' :=
    (differentiableOn_const (0 : ℂ)).congr fun z hz => by
      have hzd : z ∈ UnitDisc := ball_subset_closedBall hz
      simp [hzd]
  algebraMap_mem' c :=
    (differentiableOn_const c).congr fun z hz => by
      have hzd : z ∈ UnitDisc := ball_subset_closedBall hz
      simp [Algebra.algebraMap_eq_smul_one, hzd]

@[simp]
theorem mem_discAlgebra_iff (f : C(UnitDisc, ℂ)) :
    f ∈ DiscAlgebra ↔ DifferentiableOn ℂ (discExtend f) (ball (0 : ℂ) 1) :=
  Iff.rfl

/-- `DiscAlgebra` is uniformly closed in `C(UnitDisc, ℂ)` because uniform convergence on `UnitDisc`
implies locally uniform convergence on `ball (0 : ℂ) 1`, preserving holomorphy. -/
instance isClosed_discAlgebra : IsClosed (DiscAlgebra : Set C(UnitDisc, ℂ)) := by
  rw [← closure_subset_iff_isClosed]
  intro f hf
  have hne : (𝓝[(DiscAlgebra : Set C(UnitDisc, ℂ))] f).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp hf
  have hF : ∀ᶠ g in 𝓝[(DiscAlgebra : Set C(UnitDisc, ℂ))] f,
      DifferentiableOn ℂ (discExtend g) (ball (0 : ℂ) 1) :=
    self_mem_nhdsWithin
  have hunif : TendstoUniformlyOn discExtend (discExtend f)
      (𝓝[(DiscAlgebra : Set C(UnitDisc, ℂ))] f) (ball (0 : ℂ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds f hε)] with g hg z hz
    have hzd : z ∈ UnitDisc := ball_subset_closedBall hz
    rw [discExtend_of_mem f hzd, discExtend_of_mem g hzd, dist_eq_norm]
    have hle : ‖(f - g) ⟨z, hzd⟩‖ ≤ ‖f - g‖ := (f - g).norm_coe_le_norm ⟨z, hzd⟩
    have hdist : ‖f - g‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hg
    simpa only [ContinuousMap.sub_apply, norm_sub_rev] using hle.trans_lt hdist
  exact hunif.tendstoLocallyUniformlyOn.differentiableOn hF isOpen_ball

instance instCompleteSpaceDiscAlgebra : CompleteSpace DiscAlgebra :=
  isClosed_discAlgebra.completeSpace_coe

instance instNormOneClassDiscAlgebra : NormOneClass DiscAlgebra :=
  ⟨show ‖(1 : DiscAlgebra)‖ = 1 from norm_one (α := C(UnitDisc, ℂ))⟩

/-- Every `f ∈ DiscAlgebra` satisfies `DiffContOnCl ℂ (discExtend f) (ball (0 : ℂ) 1)`. -/
theorem discAlgebra_diffContOnCl (f : DiscAlgebra) :
    DiffContOnCl ℂ (discExtend (f : C(UnitDisc, ℂ))) (ball (0 : ℂ) 1) := by
  refine ⟨f.property, ?_⟩
  rw [closure_ball (0 : ℂ) one_ne_zero, continuousOn_iff_continuous_domRestrict]
  have hrestr :
      (closedBall (0 : ℂ) 1).domRestrict (discExtend (f : C(UnitDisc, ℂ))) =
        (f : C(UnitDisc, ℂ)) := by
    ext z
    exact discExtend_coe (f : C(UnitDisc, ℂ)) z
  rw [hrestr]
  exact (f : C(UnitDisc, ℂ)).continuous

/-- Boundary restriction homomorphism `DiscAlgebra →ₐ[ℂ] C(FourierCircle, ℂ)` sending `f` to
`t ↦ f(e^{it})`. -/
def discBoundaryHom : DiscAlgebra →ₐ[ℂ] C(FourierCircle, ℂ) where
  toFun f := (f : C(UnitDisc, ℂ)).comp discBoundary
  map_one' := by ext t; simp
  map_mul' f g := by ext t; simp
  map_zero' := by ext t; simp
  map_add' f g := by ext t; simp
  commutes' c := by ext t; simp [Algebra.algebraMap_eq_smul_one]

@[simp]
theorem discBoundaryHom_apply (f : DiscAlgebra) (t : FourierCircle) :
    discBoundaryHom f t = (f : C(UnitDisc, ℂ)) (discBoundary t) :=
  rfl

/-- By the maximum modulus principle on `ball (0 : ℂ) 1`, boundary restriction `discBoundaryHom`
is norm-preserving: `‖discBoundaryHom f‖ = ‖f‖` for all `f ∈ DiscAlgebra`. -/
theorem discBoundaryHom_norm (f : DiscAlgebra) :
    ‖discBoundaryHom f‖ = ‖f‖ := by
  change ‖((f : C(UnitDisc, ℂ)).comp discBoundary)‖ = ‖(f : C(UnitDisc, ℂ))‖
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro t
    exact (f : C(UnitDisc, ℂ)).norm_coe_le_norm (discBoundary t)
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro z
    have hle := Complex.norm_le_of_forall_mem_frontier_norm_le
      (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) 1))
      (discAlgebra_diffContOnCl f)
      (by
        intro w hw
        rw [frontier_ball (0 : ℂ) one_ne_zero] at hw
        let c : Circle := ⟨w, hw⟩
        let t : FourierCircle := fourierCircleHomeomorphism.symm c
        have ht : circleCoordinate t = w := by
          rw [circleCoordinate_homeomorphism]
          exact congrArg (fun u : Circle => (u : ℂ))
            (fourierCircleHomeomorphism.apply_symm_apply c)
        have hwd : w ∈ UnitDisc := by
          rw [← ht]
          exact (discBoundary t).property
        have hval : discExtend (f : C(UnitDisc, ℂ)) w = discBoundaryHom f t := by
          rw [discExtend_of_mem _ hwd, discBoundaryHom_apply]
          congr 1
          ext
          exact ht.symm
        rw [hval]
        exact (discBoundaryHom f).norm_coe_le_norm t)
      (by simpa only [closure_ball (0 : ℂ) one_ne_zero] using z.property)
    rw [discExtend_coe] at hle
    exact hle

theorem discBoundaryHom_isometry : Isometry discBoundaryHom :=
  AddMonoidHomClass.isometry_of_norm discBoundaryHom discBoundaryHom_norm

/-- **18.11 (`DiscAlgebraCircle`):** The boundary disc algebra `A ⊆ C(FourierCircle, ℂ)`, defined
as the image of `DiscAlgebra` under `discBoundaryHom` (as in Rudin `18.11`). -/
def DiscAlgebraCircle : Subalgebra ℂ C(FourierCircle, ℂ) :=
  discBoundaryHom.range

/-- Because `discBoundaryHom` is an isometry on the complete space `DiscAlgebra`, its image
`DiscAlgebraCircle` is a closed subalgebra of `C(FourierCircle, ℂ)`. -/
instance isClosed_discAlgebraCircle : IsClosed (DiscAlgebraCircle : Set C(FourierCircle, ℂ)) := by
  have heq : (DiscAlgebraCircle : Set C(FourierCircle, ℂ)) = Set.range discBoundaryHom := rfl
  rw [heq]
  exact discBoundaryHom_isometry.isUniformInducing.isComplete_range.isClosed

instance instCompleteSpaceDiscAlgebraCircle : CompleteSpace DiscAlgebraCircle :=
  isClosed_discAlgebraCircle.completeSpace_coe

instance instNormOneClassDiscAlgebraCircle : NormOneClass DiscAlgebraCircle :=
  ⟨show ‖(1 : DiscAlgebraCircle)‖ = 1 from norm_one (α := C(FourierCircle, ℂ))⟩

/-- Canonical isometric `ℂ`-algebra isomorphism `DiscAlgebra ≃ₐ[ℂ] DiscAlgebraCircle`. -/
def discBoundaryEquiv : DiscAlgebra ≃ₐ[ℂ] DiscAlgebraCircle :=
  AlgEquiv.ofInjective discBoundaryHom discBoundaryHom_isometry.injective

@[simp]
theorem discBoundaryEquiv_coe (f : DiscAlgebra) :
    (discBoundaryEquiv f : C(FourierCircle, ℂ)) = discBoundaryHom f :=
  rfl

theorem discBoundaryEquiv_norm (f : DiscAlgebra) :
    ‖discBoundaryEquiv f‖ = ‖f‖ :=
  discBoundaryHom_norm f

/-- Every complex polynomial defines an element of `DiscAlgebra`. -/
def discPolyAlg (p : Polynomial ℂ) : DiscAlgebra :=
  ⟨discPolynomial p, p.differentiableOn.congr fun z hz => by
    have hzd : z ∈ UnitDisc := ball_subset_closedBall hz
    simp [hzd]⟩

@[simp]
theorem discPolyAlg_coe (p : Polynomial ℂ) :
    (discPolyAlg p : C(UnitDisc, ℂ)) = discPolynomial p :=
  rfl

/-- Coordinate function `z ↦ z` as an element of `DiscAlgebra`. -/
def discCoord : DiscAlgebra :=
  discPolyAlg Polynomial.X

@[simp]
theorem discCoord_apply (z : UnitDisc) :
    (discCoord : C(UnitDisc, ℂ)) z = (z : ℂ) := by
  simp [discCoord]

/-- Boundary coordinate `t ↦ e^{it}` as an element of `DiscAlgebraCircle`. -/
def discCoordCircle : DiscAlgebraCircle :=
  discBoundaryEquiv discCoord

@[simp]
theorem discCoordCircle_coe :
    (discCoordCircle : C(FourierCircle, ℂ)) = circleCoordinate := by
  ext t
  simp [discCoordCircle, discBoundaryHom_apply, discCoord]

/-- **18.11 (Example: Circle functions vs. the disc algebra and coordinate spectra):**
1. `DiscAlgebra` is a closed unital subalgebra of `C(UnitDisc, ℂ)`, and boundary restriction
   `discBoundaryEquiv` is an isometric `ℂ`-algebra isomorphism onto the closed subalgebra
   `DiscAlgebraCircle ≤ C(FourierCircle, ℂ)`;
2. In `C(FourierCircle, ℂ)`, the coordinate `circleCoordinate` has spectrum equal to the unit
   circle `sphere (0 : ℂ) 1`;
3. In `DiscAlgebra` (and `DiscAlgebraCircle`), the coordinate `discCoord` (resp. `discCoordCircle`)
   has spectrum equal to the closed unit disc `closedBall (0 : ℂ) 1`, so
   `spectrum ℂ (discCoordCircle : C(FourierCircle, ℂ)) ⊂ spectrum ℂ discCoordCircle` strictly,
   while `rudinSpectralRadius` equals `1` in both algebras. -/
theorem theorem18_11 :
    IsClosed (DiscAlgebra : Set C(UnitDisc, ℂ)) ∧
    IsClosed (DiscAlgebraCircle : Set C(FourierCircle, ℂ)) ∧
    Isometry discBoundaryEquiv ∧
    (∀ f : DiscAlgebra, ‖discBoundaryEquiv f‖ = ‖f‖) ∧
    spectrum ℂ circleCoordinate = sphere (0 : ℂ) 1 ∧
    spectrum ℂ discCoord = closedBall (0 : ℂ) 1 ∧
    spectrum ℂ discCoordCircle = closedBall (0 : ℂ) 1 ∧
    spectrum ℂ (discCoordCircle : C(FourierCircle, ℂ)) ⊂ spectrum ℂ discCoordCircle ∧
    rudinSpectralRadius circleCoordinate = 1 ∧
    rudinSpectralRadius discCoord = 1 ∧
    rudinSpectralRadius discCoordCircle = 1 := by
  have hiso : Isometry discBoundaryEquiv :=
    AddMonoidHomClass.isometry_of_norm discBoundaryEquiv discBoundaryEquiv_norm
  have hspec_circle : spectrum ℂ circleCoordinate = sphere (0 : ℂ) 1 := by
    rw [ContinuousMap.spectrum_eq_range]
    ext w
    simp only [Set.mem_range]
    constructor
    · rintro ⟨t, rfl⟩
      rw [mem_sphere_zero_iff_norm]
      exact circleCoordinate_norm t
    · intro hw
      let c : Circle := ⟨w, hw⟩
      refine ⟨fourierCircleHomeomorphism.symm c, ?_⟩
      rw [circleCoordinate_homeomorphism]
      exact congrArg (fun u : Circle => (u : ℂ))
        (fourierCircleHomeomorphism.apply_symm_apply c)
  have hcoord_norm : ‖discCoord‖ = 1 := by
    rw [← discBoundaryEquiv_norm, show ‖discBoundaryEquiv discCoord‖ =
      ‖(discCoordCircle : C(FourierCircle, ℂ))‖ from rfl, discCoordCircle_coe]
    exact trigMonomial_norm 1
  have hspec_disc : spectrum ℂ discCoord = closedBall (0 : ℂ) 1 := by
    ext w
    constructor
    · intro hw
      rw [mem_closedBall_zero_iff]
      exact (spectrum.norm_le_norm_of_mem hw).trans_eq hcoord_norm
    · intro hw
      rw [spectrum.mem_iff]
      intro hu
      have huC : IsUnit ((algebraMap ℂ DiscAlgebra w - discCoord : DiscAlgebra) : C(UnitDisc, ℂ)) :=
        hu.map DiscAlgebra.val
      have hne := (ContinuousMap.isUnit_iff_forall_ne_zero _).mp huC ⟨w, hw⟩
      simp [Algebra.algebraMap_eq_smul_one] at hne
  have hspec_disc_circle : spectrum ℂ discCoordCircle = closedBall (0 : ℂ) 1 := by
    rw [discCoordCircle, AlgEquiv.spectrum_eq discBoundaryEquiv discCoord, hspec_disc]
  have hstrict :
      spectrum ℂ (discCoordCircle : C(FourierCircle, ℂ)) ⊂ spectrum ℂ discCoordCircle := by
    rw [discCoordCircle_coe, hspec_circle, hspec_disc_circle, ssubset_iff_subset_ne]
    refine ⟨sphere_subset_closedBall, ?_⟩
    intro heq
    have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) 1 := mem_closedBall_self zero_le_one
    rw [← heq, mem_sphere_zero_iff_norm, norm_zero] at h0
    exact zero_ne_one h0
  have hrad_disc_circle : rudinSpectralRadius discCoordCircle = 1 := by
    obtain ⟨_, hle, hmem, -⟩ := theorem18_8 discCoordCircle
    have hnorm1 : ‖discCoordCircle‖ = 1 := by
      change ‖(discCoordCircle : C(FourierCircle, ℂ))‖ = 1
      rw [discCoordCircle_coe]
      exact trigMonomial_norm 1
    apply le_antisymm (hle.trans_eq hnorm1)
    have h1_mem : (1 : ℂ) ∈ spectrum ℂ discCoordCircle := by
      rw [hspec_disc_circle, mem_closedBall_zero_iff, norm_one]
    simpa only [norm_one] using hmem 1 h1_mem
  have hrad_circle : rudinSpectralRadius circleCoordinate = 1 := by
    have hinv := (theorem18_10 DiscAlgebraCircle discCoordCircle).2.2.2.2
    rw [discCoordCircle_coe, hrad_disc_circle] at hinv
    exact hinv.symm
  have hrad_disc : rudinSpectralRadius discCoord = 1 := by
    unfold rudinSpectralRadius at hrad_disc_circle ⊢
    rwa [hspec_disc, ← hspec_disc_circle]
  exact ⟨isClosed_discAlgebra, isClosed_discAlgebraCircle, hiso, discBoundaryEquiv_norm,
    hspec_circle, hspec_disc, hspec_disc_circle, hstrict, hrad_circle, hrad_disc,
    hrad_disc_circle⟩

end DiscAlgebraExample

/-! ## Section 2: Ideals, Quotients, and Homomorphisms (`18.12`–`18.17`) -/

section CommutativeBanachAlgebra

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

omit [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A] in
/-- **18.12 (Definitions: Ideals, maximality, algebra homomorphisms, and kernels):**
In a commutative `ℂ`-algebra `A`:
1. An ideal `I : Ideal A` is proper (`I ≠ ⊤`) iff `(1 : A) ∉ I`, iff `I` contains no unit of `A`;
2. An ideal `M : Ideal A` is maximal (`M.IsMaximal`) iff `M ≠ ⊤` and there is no proper ideal
   strictly between `M` and `⊤`;
3. For any unital `ℂ`-algebra homomorphism `φ : A →ₐ[ℂ] B` into a nontrivial algebra `B`,
   `RingHom.ker φ` is a proper ideal of `A`. -/
theorem theorem18_12 {R B : Type*} [CommRing R] [Algebra ℂ R] [Ring B] [Algebra ℂ B]
    [Nontrivial B] (I M : Ideal R) (φ : R →ₐ[ℂ] B) :
    (I ≠ ⊤ ↔ (1 : R) ∉ I) ∧
    (I ≠ ⊤ ↔ ∀ x ∈ I, ¬ IsUnit x) ∧
    (M.IsMaximal ↔ M ≠ ⊤ ∧ ∀ J : Ideal R, M < J → J = ⊤) ∧
    RingHom.ker φ ≠ ⊤ ∧
    ((1 : R) ∉ RingHom.ker φ) := by
  have h1 : I ≠ ⊤ ↔ (1 : R) ∉ I := by
    rw [Ne, Ideal.eq_top_iff_one]
  have h2 : I ≠ ⊤ ↔ ∀ x ∈ I, ¬ IsUnit x := by
    rw [h1]
    constructor
    · rintro h1not x hx ⟨u, rfl⟩
      exact h1not (by simpa only [Units.mul_inv] using I.mul_mem_right (↑u⁻¹) hx)
    · intro hno h1mem
      exact hno 1 h1mem isUnit_one
  have h3 : M.IsMaximal ↔ M ≠ ⊤ ∧ ∀ J : Ideal R, M < J → J = ⊤ :=
    ⟨fun h => ⟨h.ne_top, fun J hJ => h.out.2 J hJ⟩, fun ⟨hne, hmax⟩ => ⟨⟨hne, hmax⟩⟩⟩
  have hker1 : (1 : R) ∉ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_one]
    exact one_ne_zero
  have hker_ne : RingHom.ker φ ≠ ⊤ := by
    rwa [Ne, Ideal.eq_top_iff_one]
  exact ⟨h1, h2, h3, hker_ne, hker1⟩

omit [NormedAlgebra ℂ A] [NormOneClass A] in
/-- **18.13 (Theorem: Properties of proper ideals; existence and closedness of maximal ideals):**
In a commutative complex Banach algebra `A`:
1. `(a)` No proper ideal `I ≠ ⊤` contains any invertible element, and `∀ x ∈ I, 1 ≤ ‖(1 : A) - x‖`;
2. `(b)` The topological closure `I.closure` of every proper ideal `I ≠ ⊤` is a proper ideal;
3. `(c)` Every proper ideal `I ≠ ⊤` is contained in a maximal ideal `M`;
4. `(d)` Every maximal ideal `M` of `A` is closed (`IsClosed (M : Set A)`). -/
theorem theorem18_13 :
    (∀ I : Ideal A, I ≠ ⊤ →
      Disjoint (I : Set A) (invertibleElements A) ∧ ∀ x ∈ I, 1 ≤ ‖(1 : A) - x‖) ∧
    (∀ I : Ideal A, I ≠ ⊤ → I.closure ≠ ⊤ ∧ (I.closure : Set A) = closure (I : Set A)) ∧
    (∀ I : Ideal A, I ≠ ⊤ → ∃ M : Ideal A, M.IsMaximal ∧ I ≤ M) ∧
    (∀ M : Ideal A, M.IsMaximal → IsClosed (M : Set A)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I hI
    refine ⟨Set.disjoint_left.mpr fun x hx hu => ?_, fun x hx => ?_⟩
    · rcases hu with ⟨u, rfl⟩
      exact hI (I.eq_top_iff_one.mpr (by simpa only [Units.mul_inv] using I.mul_mem_right (↑u⁻¹) hx))
    · by_contra! hlt
      exact hI (I.eq_top_of_norm_lt_one hx hlt)
  · intro I hI
    exact ⟨I.closure_ne_top hI, Ideal.coe_closure I⟩
  · intro I hI
    exact Ideal.exists_le_maximal I hI
  · intro M hM
    have : M.IsMaximal := hM
    exact inferInstance

omit [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A] in
/-- **18.14 (Quotient algebras, kernels, and maximal ideals vs. quotient fields):**
For every ideal `J` of a commutative `ℂ`-algebra `R`, the canonical quotient algebra map
`π = Ideal.Quotient.mkₐ ℂ J : R →ₐ[ℂ] R ⧸ J` is surjective with kernel `J`, and a proper ideal `J`
is maximal if and only if the quotient `R ⧸ J` is a field (`IsField (R ⧸ J)`). -/
theorem theorem18_14 {R : Type*} [CommRing R] [Algebra ℂ R] (J : Ideal R) :
    Function.Surjective (Ideal.Quotient.mkₐ ℂ J) ∧
    RingHom.ker (Ideal.Quotient.mkₐ ℂ J) = J ∧
    (J.IsMaximal ↔ IsField (R ⧸ J)) := by
  refine ⟨Ideal.Quotient.mkₐ_surjective ℂ J, ?_, Ideal.Quotient.maximal_ideal_iff_isField_quotient J⟩
  ext x
  simp [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]

omit [NormedAlgebra ℂ A] in
/-- For a closed proper ideal `J ≠ ⊤` in a commutative Banach algebra `A` with `‖(1 : A)‖ = 1`,
the quotient norm of the unit `(1 : A ⧸ J)` is `1`. -/
theorem quotient_norm_one_of_ne_top (J : Ideal A) [IsClosed (J : Set A)] (hJ : J ≠ ⊤) :
    ‖(1 : A ⧸ J)‖ = 1 := by
  apply le_antisymm
  · simpa only [map_one, norm_one] using Ideal.Quotient.norm_mk_le J (1 : A)
  · by_contra! hlt
    have hε : 0 < 1 - ‖(1 : A ⧸ J)‖ := sub_pos.mpr hlt
    obtain ⟨r, hr_mk, hr_norm⟩ := Ideal.Quotient.norm_mk_lt (1 : A ⧸ J) hε
    have hr_norm' : ‖r‖ < 1 := by linarith
    have hmem : 1 - r ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, hr_mk, sub_self]
    have hlt' : ‖(1 : A) - (1 - r)‖ < 1 := by
      simpa only [sub_sub_cancel] using hr_norm'
    exact hJ (J.eq_top_of_norm_lt_one hmem hlt')

omit [NormedAlgebra ℂ A] in
theorem quotient_normOneClass (J : Ideal A) [IsClosed (J : Set A)] (hJ : J ≠ ⊤) :
    NormOneClass (A ⧸ J) :=
  ⟨quotient_norm_one_of_ne_top J hJ⟩

omit [NormedAlgebra ℂ A] in
/-- **18.15 (Quotient norm, completeness, and quotient Banach algebra structure):**
Let `J` be a closed proper ideal of a commutative complex Banach algebra `A` (`J ≠ ⊤`). Then:
1. For every `x : A`, the quotient norm on `A ⧸ J` satisfies
   `‖Ideal.Quotient.mk J x‖ = inf_{y ∈ J} ‖x + y‖ = inf_{y ∈ J} ‖x - y‖`;
2. `A ⧸ J` is a complete commutative complex Banach algebra with submultiplicative norm
   `‖q₁ * q₂‖ ≤ ‖q₁‖ * ‖q₂‖`, contractive projection `‖Ideal.Quotient.mk J x‖ ≤ ‖x‖`, and
   unit norm `‖(1 : A ⧸ J)‖ = 1`;
3. If `J` is maximal, every nonzero element of `A ⧸ J` is invertible (`∀ q : A ⧸ J, q ≠ 0 → IsUnit q`). -/
theorem theorem18_15 (J : Ideal A) [IsClosed (J : Set A)] (hJ : J ≠ ⊤) :
    (∀ x : A,
      ‖Ideal.Quotient.mk J x‖ = sInf ((fun y : A => ‖x + y‖) '' (J : Set A)) ∧
      ‖Ideal.Quotient.mk J x‖ = sInf ((fun y : A => ‖x - y‖) '' (J : Set A))) ∧
    (∀ q₁ q₂ : A ⧸ J, ‖q₁ * q₂‖ ≤ ‖q₁‖ * ‖q₂‖) ∧
    (∀ x : A, ‖Ideal.Quotient.mk J x‖ ≤ ‖x‖) ∧
    CompleteSpace (A ⧸ J) ∧
    ‖(1 : A ⧸ J)‖ = 1 ∧
    (J.IsMaximal → ∀ q : A ⧸ J, q ≠ 0 → IsUnit q) := by
  refine ⟨?_, norm_mul_le, Ideal.Quotient.norm_mk_le J, inferInstance,
    quotient_norm_one_of_ne_top J hJ, ?_⟩
  · intro x
    have hne_plus : ((fun y : A => ‖x + y‖) '' (J : Set A)).Nonempty :=
      ⟨‖x + 0‖, 0, J.zero_mem, rfl⟩
    have hbdd_plus : BddBelow ((fun y : A => ‖x + y‖) '' (J : Set A)) :=
      ⟨0, by rintro _ ⟨y, -, rfl⟩; exact norm_nonneg _⟩
    have hplus : ‖Ideal.Quotient.mk J x‖ = sInf ((fun y : A => ‖x + y‖) '' (J : Set A)) := by
      apply le_antisymm
      · refine le_csInf hne_plus ?_
        rintro _ ⟨y, hy, rfl⟩
        have hmk : Ideal.Quotient.mk J (x + y) = Ideal.Quotient.mk J x := by
          rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero]
        rw [← hmk]
        exact Ideal.Quotient.norm_mk_le J (x + y)
      · refine le_of_forall_pos_lt_add fun ε hε => ?_
        obtain ⟨r, hr_mk, hr_lt⟩ := Ideal.Quotient.norm_mk_lt (Ideal.Quotient.mk J x) hε
        have hy : r - x ∈ J := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hr_mk, sub_self]
        have hle_r : sInf ((fun y : A => ‖x + y‖) '' (J : Set A)) ≤ ‖r‖ := by
          simpa only [add_sub_cancel] using csInf_le hbdd_plus ⟨r - x, hy, rfl⟩
        exact hle_r.trans_lt hr_lt
    have hset_eq :
        ((fun y : A => ‖x + y‖) '' (J : Set A)) = ((fun y : A => ‖x - y‖) '' (J : Set A)) := by
      ext t
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨-y, J.neg_mem hy, by simp [sub_eq_add_neg]⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨-y, J.neg_mem hy, by simp [sub_eq_add_neg]⟩
    exact ⟨hplus, hset_eq ▸ hplus⟩
  · intro hmax q hq
    have hfield : IsField (A ⧸ J) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient J).mp hmax
    exact isUnit_iff_exists_inv.mpr (hfield.mul_inv_cancel hq)

/-- **18.16 (`ComplexHom`):** A *complex homomorphism* on a commutative `ℂ`-algebra `R` is a
nonzero `ℂ`-linear functional `h : R →ₗ[ℂ] ℂ` satisfying `h (x * y) = h x * h y` for all `x, y : R`.
Following Rudin `18.16` and `SCOPING-H.md` §Statement fidelity notes, neither `h 1 = 1` nor
topological continuity is built into the structure; both are proved as theorems (`18.16` and
`18.17(e)`). -/
@[ext]
structure ComplexHom (R : Type*) [CommRing R] [Algebra ℂ R] where
  toLinearMap : R →ₗ[ℂ] ℂ
  ne_zero : toLinearMap ≠ 0
  map_mul' : ∀ x y : R, toLinearMap (x * y) = toLinearMap x * toLinearMap y

namespace ComplexHom

section Algebraic

variable {R : Type*} [CommRing R] [Algebra ℂ R]

instance instFunLike : FunLike (ComplexHom R) R ℂ where
  coe h := h.toLinearMap
  coe_injective h₁ h₂ H := by
    ext x
    exact congrFun H x

@[simp]
theorem coe_toLinearMap (h : ComplexHom R) (x : R) : h.toLinearMap x = h x :=
  rfl

@[simp]
theorem map_zero (h : ComplexHom R) : h 0 = 0 :=
  h.toLinearMap.map_zero

@[simp]
theorem map_add (h : ComplexHom R) (x y : R) : h (x + y) = h x + h y :=
  h.toLinearMap.map_add x y

@[simp]
theorem map_sub (h : ComplexHom R) (x y : R) : h (x - y) = h x - h y :=
  h.toLinearMap.map_sub x y

@[simp]
theorem map_neg (h : ComplexHom R) (x : R) : h (-x) = - h x :=
  h.toLinearMap.map_neg x

@[simp]
theorem map_smul (h : ComplexHom R) (c : ℂ) (x : R) : h (c • x) = c * h x := by
  change h.toLinearMap (c • x) = c * h.toLinearMap x
  simpa only [smul_eq_mul] using h.toLinearMap.map_smul c x

@[simp]
theorem map_mul (h : ComplexHom R) (x y : R) : h (x * y) = h x * h y :=
  h.map_mul' x y

/-- Every nonzero multiplicative linear functional automatically maps `1` to `1` (`18.16`). -/
@[simp]
theorem map_one (h : ComplexHom R) : h 1 = 1 := by
  have hex : ∃ x : R, h x ≠ 0 := by
    by_contra! hall
    apply h.ne_zero
    ext x
    exact hall x
  obtain ⟨x, hx⟩ := hex
  have hmul : h x * (h 1 - 1) = 0 := by
    rw [mul_sub, mul_one, ← h.map_mul, mul_one, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hx)

@[simp]
theorem map_pow (h : ComplexHom R) (x : R) (n : ℕ) : h (x ^ n) = h x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, h.map_mul, ih, pow_succ]

@[simp]
theorem map_algebraMap (h : ComplexHom R) (c : ℂ) : h (algebraMap ℂ R c) = c := by
  rw [Algebra.algebraMap_eq_smul_one, h.map_smul, h.map_one, mul_one]

/-- Promoted unital `ℂ`-algebra homomorphism `R →ₐ[ℂ] ℂ` associated to `h : ComplexHom R`. -/
def toAlgHom (h : ComplexHom R) : R →ₐ[ℂ] ℂ where
  toFun := h
  map_one' := h.map_one
  map_mul' := h.map_mul
  map_zero' := h.map_zero
  map_add' := h.map_add
  commutes' := h.map_algebraMap

@[simp]
theorem toAlgHom_apply (h : ComplexHom R) (x : R) : h.toAlgHom x = h x :=
  rfl

/-- Canonical bijection `ComplexHom R ≃ (R →ₐ[ℂ] ℂ)`. -/
def equivAlgHom (R : Type*) [CommRing R] [Algebra ℂ R] : ComplexHom R ≃ (R →ₐ[ℂ] ℂ) where
  toFun := toAlgHom
  invFun φ :=
    { toLinearMap := φ.toLinearMap
      ne_zero := fun h0 => by
        have h1 : φ 1 = 0 := congrArg (fun L : R →ₗ[ℂ] ℂ => L 1) h0
        rw [_root_.map_one] at h1
        exact one_ne_zero h1
      map_mul' := φ.map_mul }
  left_inv h := by ext x; rfl
  right_inv φ := by ext x; rfl

theorem map_isUnit_ne_zero (h : ComplexHom R) {x : R} (hx : IsUnit x) :
    h x ≠ 0 ∧ h (x⁻¹ʳ) = (h x)⁻¹ := by
  rcases hx with ⟨u, rfl⟩
  have hprod : h (u : R) * h (↑u⁻¹ : R) = 1 := by
    rw [← h.map_mul, Units.mul_inv, h.map_one]
  have hne : h (u : R) ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  refine ⟨hne, ?_⟩
  rw [Ring.inverse_unit]
  exact eq_inv_of_mul_eq_one_right hprod

end Algebraic

end ComplexHom

omit [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A] in
/-- **18.16 (Setup: Nonzero multiplicative linear functionals / complex homomorphisms):**
Every nonzero multiplicative `ℂ`-linear functional `h : ComplexHom R` on a commutative `ℂ`-algebra
`R` automatically satisfies `h 1 = 1`, `h (algebraMap ℂ R c) = c`, sends every invertible element
`x` to a nonzero complex number with `h (x⁻¹ʳ) = (h x)⁻¹`, and corresponds bijectively to unital
`ℂ`-algebra homomorphisms `R →ₐ[ℂ] ℂ`. -/
theorem theorem18_16 {R : Type*} [CommRing R] [Algebra ℂ R] (h : ComplexHom R) :
    h 1 = 1 ∧
    (∀ c : ℂ, h (algebraMap ℂ R c) = c) ∧
    (∀ x : R, IsUnit x → h x ≠ 0 ∧ h (x⁻¹ʳ) = (h x)⁻¹) ∧
    Function.Bijective (ComplexHom.equivAlgHom R) :=
  ⟨h.map_one, h.map_algebraMap, fun _ hx => h.map_isUnit_ne_zero hx,
    (ComplexHom.equivAlgHom R).bijective⟩

/-- **18.17(a):** Every maximal ideal `M` of a commutative complex Banach algebra `A` is the kernel
of a unique complex homomorphism `h : ComplexHom A`, and conversely the kernel of every
`h : ComplexHom A` is a maximal ideal of `A`. -/
theorem theorem18_17_a :
    (∀ M : Ideal A, M.IsMaximal → ∃! h : ComplexHom A, RingHom.ker h.toAlgHom = M) ∧
    (∀ h : ComplexHom A, (RingHom.ker h.toAlgHom).IsMaximal) := by
  have hker_max : ∀ h : ComplexHom A, (RingHom.ker h.toAlgHom).IsMaximal := by
    intro h
    rw [Ideal.isMaximal_iff]
    refine ⟨?_, ?_⟩
    · rw [RingHom.mem_ker, ComplexHom.toAlgHom_apply, h.map_one]
      exact one_ne_zero
    · intro J x hKJ hxK hxJ
      have hne : h x ≠ 0 := by rwa [RingHom.mem_ker, ComplexHom.toAlgHom_apply] at hxK
      have huK : 1 - algebraMap ℂ A (h x)⁻¹ * x ∈ RingHom.ker h.toAlgHom := by
        rw [RingHom.mem_ker, ComplexHom.toAlgHom_apply, h.map_sub, h.map_one, h.map_mul,
          h.map_algebraMap, inv_mul_cancel₀ hne, sub_self]
      have huJ : 1 - algebraMap ℂ A (h x)⁻¹ * x ∈ J := hKJ huK
      have hxJ' : algebraMap ℂ A (h x)⁻¹ * x ∈ J := J.mul_mem_left (algebraMap ℂ A (h x)⁻¹) hxJ
      simpa only [sub_add_cancel] using J.add_mem huJ hxJ'
  have huniq : ∀ h₁ h₂ : ComplexHom A,
      RingHom.ker h₁.toAlgHom = RingHom.ker h₂.toAlgHom → h₁ = h₂ := by
    intro h₁ h₂ heq
    ext x
    have hmem : x - algebraMap ℂ A (h₁ x) ∈ RingHom.ker h₁.toAlgHom := by
      rw [RingHom.mem_ker, ComplexHom.toAlgHom_apply, h₁.map_sub, h₁.map_algebraMap, sub_self]
    rw [heq, RingHom.mem_ker, ComplexHom.toAlgHom_apply, h₂.map_sub, h₂.map_algebraMap] at hmem
    exact (sub_eq_zero.mp hmem).symm
  refine ⟨?_, hker_max⟩
  intro M hM
  have : M.IsMaximal := hM
  have : IsClosed (M : Set A) := inferInstance
  have : NormOneClass (A ⧸ M) := quotient_normOneClass M hM.ne_top
  have hdiv : ∀ q : A ⧸ M, q ≠ 0 → IsUnit q := (theorem18_15 M hM.ne_top).2.2.2.2.2 hM
  let e : ℂ ≃ₐ[ℂ] (A ⧸ M) := gelfandMazurAlgEquiv hdiv
  let φ : A →ₐ[ℂ] ℂ := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ M)
  let h : ComplexHom A := (ComplexHom.equivAlgHom A).symm φ
  have hker : RingHom.ker h.toAlgHom = M := by
    ext x
    have h_eq : h.toAlgHom x = e.symm (Ideal.Quotient.mk M x) := rfl
    rw [RingHom.mem_ker, h_eq]
    constructor
    · intro h0
      have hmk0 : Ideal.Quotient.mk M x = 0 := by
        simpa only [map_zero, AlgEquiv.apply_symm_apply] using congrArg e h0
      exact Ideal.Quotient.eq_zero_iff_mem.mp hmk0
    · intro hxM
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hxM, map_zero]
  exact ⟨h, hker, fun h' hh' => huniq h' h (hh'.trans hker.symm)⟩

/-- **18.17(b):** An element `x` of a commutative complex Banach algebra `A` is invertible if and
only if `h x ≠ 0` for every `h : ComplexHom A` (equivalently, `x` lies in no maximal ideal of `A`). -/
theorem theorem18_17_b (x : A) :
    (IsUnit x ↔ ∀ h : ComplexHom A, h x ≠ 0) ∧
    (IsUnit x ↔ ∀ M : Ideal A, M.IsMaximal → x ∉ M) := by
  have h1 : IsUnit x ↔ ∀ M : Ideal A, M.IsMaximal → x ∉ M := by
    constructor
    · rintro ⟨u, rfl⟩ M hM hxM
      exact hM.ne_top (M.eq_top_iff_one.mpr
        (by simpa only [Units.mul_inv] using M.mul_mem_right (↑u⁻¹) hxM))
    · intro hnomax
      by_contra hnotu
      have hproper : Ideal.span ({x} : Set A) ≠ ⊤ := by
        intro htop
        rw [Ideal.span_singleton_eq_top] at htop
        exact hnotu htop
      obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal _ hproper
      exact hnomax M hM (hxM (Ideal.subset_span (Set.mem_singleton x)))
  refine ⟨?_, h1⟩
  rw [h1]
  constructor
  · intro hnomax h hh0
    have hmax := (theorem18_17_a (A := A)).2 h
    exact hnomax (RingHom.ker h.toAlgHom) hmax hh0
  · intro hnoh M hM hxM
    obtain ⟨h, rfl, -⟩ := (theorem18_17_a (A := A)).1 M hM
    exact hnoh h hxM

/-- **18.17(c):** For every `x : A` and `z : ℂ`, `z ∈ spectrum ℂ x` if and only if `h x = z` for
some complex homomorphism `h : ComplexHom A`; equivalently `spectrum ℂ x = Set.range (fun h => h x)`. -/
theorem theorem18_17_c (x : A) :
    (∀ z : ℂ, z ∈ spectrum ℂ x ↔ ∃ h : ComplexHom A, h x = z) ∧
    spectrum ℂ x = Set.range (fun h : ComplexHom A => h x) := by
  have hiff : ∀ z : ℂ, z ∈ spectrum ℂ x ↔ ∃ h : ComplexHom A, h x = z := by
    intro z
    rw [spectrum.mem_iff, (theorem18_17_b (algebraMap ℂ A z - x)).1]
    push Not
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨h, ?_⟩
      rw [h.map_sub, h.map_algebraMap, sub_eq_zero] at hh
      exact hh.symm
    · rintro ⟨h, rfl⟩
      exact ⟨h, by rw [h.map_sub, h.map_algebraMap, sub_self]⟩
  refine ⟨hiff, ?_⟩
  ext z
  simp only [hiff, Set.mem_range]

/-- **18.17(d):** `ComplexHom A` is nonempty, every `h : ComplexHom A` and `x : A` satisfy
`‖h x‖ ≤ rudinSpectralRadius x ≤ ‖x‖`, and
`rudinSpectralRadius x = sSup (Set.range fun h : ComplexHom A => ‖h x‖)`. -/
theorem theorem18_17_d :
    Nonempty (ComplexHom A) ∧
    (∀ (h : ComplexHom A) (x : A),
      ‖h x‖ ≤ rudinSpectralRadius x ∧ rudinSpectralRadius x ≤ ‖x‖) ∧
    (∀ x : A, rudinSpectralRadius x = sSup (Set.range fun h : ComplexHom A => ‖h x‖)) := by
  have : Nontrivial A := NormOneClass.nontrivial
  obtain ⟨z₀, hz₀⟩ := (theorem18_6 (0 : A)).2.1
  obtain ⟨h₀, -⟩ := ((theorem18_17_c (0 : A)).1 z₀).mp hz₀
  refine ⟨⟨h₀⟩, ?_, ?_⟩
  · intro h x
    obtain ⟨_, hrad_le, hmem_le, -⟩ := theorem18_8 x
    have hspec : h x ∈ spectrum ℂ x := ((theorem18_17_c x).1 (h x)).mpr ⟨h, rfl⟩
    exact ⟨hmem_le (h x) hspec, hrad_le⟩
  · intro x
    unfold rudinSpectralRadius
    rw [(theorem18_17_c x).2]
    congr 1
    ext r
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
      exact ⟨h, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h x, ⟨h, rfl⟩, rfl⟩

/-- Promoted continuous linear functional `h.toCLM : StrongDual ℂ A` of an algebraic complex
homomorphism `h : ComplexHom A` (`18.17(e)`). -/
def ComplexHom.toCLM (h : ComplexHom A) : StrongDual ℂ A :=
  h.toLinearMap.mkContinuous 1 fun x => by
    have hb := (theorem18_17_d (A := A)).2.1 h x
    simpa only [ComplexHom.coe_toLinearMap, one_mul] using hb.1.trans hb.2

@[simp]
theorem ComplexHom.toCLM_apply (h : ComplexHom A) (x : A) :
    h.toCLM x = h x :=
  rfl

/-- **18.17(e):** Every (initially algebraic) complex homomorphism `h : ComplexHom A` on a
commutative complex Banach algebra `A` is continuous, and its continuous linear functional
`h.toCLM : StrongDual ℂ A` has operator norm `‖h.toCLM‖ = 1`. -/
theorem theorem18_17_e (h : ComplexHom A) :
    Continuous h ∧
    (∀ x : A, ‖h x‖ ≤ ‖x‖) ∧
    ‖h.toCLM‖ = 1 := by
  have hcont : Continuous h := by
    change Continuous (fun x : A => h.toCLM x)
    exact h.toCLM.continuous
  have hbound : ∀ x : A, ‖h x‖ ≤ ‖x‖ := fun x => by
    have hb := (theorem18_17_d (A := A)).2.1 h x
    exact hb.1.trans hb.2
  have hnorm : ‖h.toCLM‖ = 1 := by
    apply le_antisymm
    · exact LinearMap.mkContinuous_norm_le h.toLinearMap zero_le_one _
    · have h1 : (1 : ℝ) = ‖h.toCLM 1‖ := by simp
      calc
        (1 : ℝ) = ‖h.toCLM 1‖ := h1
        _ ≤ ‖h.toCLM‖ * ‖(1 : A)‖ := h.toCLM.le_opNorm 1
        _ = ‖h.toCLM‖ := by rw [norm_one, mul_one]
  exact ⟨hcont, hbound, hnorm⟩

/-- **18.17 (Theorem: Five-part fundamental theorem of commutative complex Banach algebras):**
Combines all five parts `(a)`–`(e)` of Rudin `18.17`. -/
theorem theorem18_17 :
    ((∀ M : Ideal A, M.IsMaximal → ∃! h : ComplexHom A, RingHom.ker h.toAlgHom = M) ∧
      (∀ h : ComplexHom A, (RingHom.ker h.toAlgHom).IsMaximal)) ∧
    (∀ x : A, (IsUnit x ↔ ∀ h : ComplexHom A, h x ≠ 0) ∧
      (IsUnit x ↔ ∀ M : Ideal A, M.IsMaximal → x ∉ M)) ∧
    (∀ x : A, (∀ z : ℂ, z ∈ spectrum ℂ x ↔ ∃ h : ComplexHom A, h x = z) ∧
      spectrum ℂ x = Set.range (fun h : ComplexHom A => h x)) ∧
    (Nonempty (ComplexHom A) ∧
      (∀ (h : ComplexHom A) (x : A),
        ‖h x‖ ≤ rudinSpectralRadius x ∧ rudinSpectralRadius x ≤ ‖x‖) ∧
      (∀ x : A, rudinSpectralRadius x = sSup (Set.range fun h : ComplexHom A => ‖h x‖))) ∧
    (∀ h : ComplexHom A, Continuous h ∧ (∀ x : A, ‖h x‖ ≤ ‖x‖) ∧ ‖h.toCLM‖ = 1) :=
  ⟨theorem18_17_a, theorem18_17_b, theorem18_17_c, theorem18_17_d, theorem18_17_e⟩

end CommutativeBanachAlgebra

/-! ## Section 3: Applications to the Disc Algebra (`18.18`–`18.20`) -/

section DiscAlgebraApplications

open RudinRCA.Chapter04 RudinRCA.Chapter05

/-- Uniform density of polynomials in `DiscAlgebra` (via radial dilation `z ↦ f(rz)` for
`0 < r < 1` and uniform convergence of Taylor partial sums on `UnitDisc`). -/
theorem discPolyAlg_approx (f : DiscAlgebra) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ‖discPolyAlg p - f‖ < ε := by
  have huc : UniformContinuous (f : C(UnitDisc, ℂ)) :=
    CompactSpace.uniformContinuous_of_continuous (f : C(UnitDisc, ℂ)).continuous
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformContinuous_iff.mp huc (ε / 2) (half_pos hε)
  let r : ℝ := max (1 / 2) (1 - δ / 2)
  have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hr_lt_one : r < 1 := max_lt (by norm_num) (by linarith)
  have h1_sub_r_lt : 1 - r < δ := by
    have hle : 1 - δ / 2 ≤ r := le_max_right _ _
    linarith
  have hrad_mem : ∀ z : UnitDisc, (r : ℂ) * (z : ℂ) ∈ UnitDisc := by
    intro z
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr_pos.le]
    have hz1 : ‖(z : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.property
    nlinarith [norm_nonneg (z : ℂ)]
  have hrad_close : ∀ z : UnitDisc,
      ‖(f : C(UnitDisc, ℂ)) ⟨(r : ℂ) * (z : ℂ), hrad_mem z⟩ - (f : C(UnitDisc, ℂ)) z‖ < ε / 2 := by
    intro z
    have hdist_z : dist (⟨(r : ℂ) * (z : ℂ), hrad_mem z⟩ : UnitDisc) z < δ := by
      rw [Subtype.dist_eq, dist_eq_norm]
      have hsub : (r : ℂ) * (z : ℂ) - (z : ℂ) = ((r - 1 : ℝ) : ℂ) * (z : ℂ) := by push_cast; ring
      rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith), neg_sub]
      have hz1 : ‖(z : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.property
      have hle1 : (1 - r) * ‖(z : ℂ)‖ ≤ 1 - r := by
        nlinarith [norm_nonneg (z : ℂ)]
      exact hle1.trans_lt h1_sub_r_lt
    simpa only [dist_eq_norm] using hδ hdist_z
  let g : ℂ → ℂ := fun z => discExtend (f : C(UnitDisc, ℂ)) ((r : ℂ) * z)
  have hr_inv_gt : 1 < r⁻¹ := one_lt_inv₀ hr_pos |>.mpr hr_lt_one
  let R : ℝ := (1 + r⁻¹) / 2
  let r' : ℝ := (1 + R) / 2
  have hR_gt_one : 1 < R := by dsimp [R]; linarith
  have hR_lt_inv : R < r⁻¹ := by dsimp [R]; linarith
  have hr'_gt_one : 1 < r' := by dsimp [r']; linarith
  have hr'_lt_R : r' < R := by dsimp [r']; linarith
  have hR_pos : 0 < R := zero_lt_one.trans hR_gt_one
  have hr'_pos : 0 < r' := zero_lt_one.trans hr'_gt_one
  let R_nn : ℝ≥0 := ⟨R, hR_pos.le⟩
  let r'_nn : ℝ≥0 := ⟨r', hr'_pos.le⟩
  have hR_nn_pos : 0 < R_nn := by exact_mod_cast hR_pos
  have hr'_lt_R_enn : (r'_nn : ℝ≥0∞) < (R_nn : ℝ≥0∞) := by exact_mod_cast hr'_lt_R
  have hg_diff : DifferentiableOn ℂ g (closedBall (0 : ℂ) R_nn) := by
    have hmaps : MapsTo (fun z : ℂ => (r : ℂ) * z) (closedBall (0 : ℂ) R_nn) (ball (0 : ℂ) 1) := by
      intro z hz
      rw [mem_closedBall_zero_iff] at hz
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr_pos.le]
      have hmul_le : r * ‖z‖ ≤ r * R := mul_le_mul_of_nonneg_left hz hr_pos.le
      have hrR_lt : r * R < 1 := by
        calc
          r * R < r * r⁻¹ := mul_lt_mul_of_pos_left hR_lt_inv hr_pos
          _ = 1 := mul_inv_cancel₀ hr_pos.ne'
      exact hmul_le.trans_lt hrR_lt
    exact f.property.comp ((differentiable_id.const_mul (r : ℂ)).differentiableOn) hmaps
  let ps := cauchyPowerSeries g 0 R_nn
  have hps : HasFPowerSeriesOnBall g ps 0 R_nn := hg_diff.hasFPowerSeriesOnBall hR_nn_pos
  have hunif : TendstoUniformlyOn (fun n y => ps.partialSum n y) (fun y => g (0 + y))
      atTop (ball (0 : ℂ) r'_nn) :=
    hps.tendstoUniformlyOn hr'_lt_R_enn
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.mp hunif (ε / 2) (half_pos hε)).exists
  let p : Polynomial ℂ :=
    ∑ k ∈ Finset.range N, Polynomial.C (ps k (fun _ => 1)) * Polynomial.X ^ k
  have hp_eval : ∀ y : ℂ, p.eval y = ps.partialSum N y := by
    intro y
    simp only [p, FormalMultilinearSeries.partialSum, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hsmul := (ps k).map_smul_univ (fun _ : Fin k => y) (fun _ : Fin k => (1 : ℂ))
    simp only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_fin] at hsmul
    rw [hsmul, mul_comm]
  refine ⟨p, ?_⟩
  change ‖(discPolyAlg p - f : DiscAlgebra).1‖ < ε
  rw [ContinuousMap.norm_lt_iff _ hε]
  intro z
  have hz_ball : (z : ℂ) ∈ ball (0 : ℂ) r'_nn := by
    rw [mem_ball_zero_iff]
    exact (mem_closedBall_zero_iff.mp z.property).trans_lt hr'_gt_one
  have hps_close : ‖p.eval (z : ℂ) - g (z : ℂ)‖ < ε / 2 := by
    have hNz := hN (z : ℂ) hz_ball
    rw [zero_add, ← hp_eval (z : ℂ), dist_eq_norm, norm_sub_rev] at hNz
    exact hNz
  have hg_eq : g (z : ℂ) = (f : C(UnitDisc, ℂ)) ⟨(r : ℂ) * (z : ℂ), hrad_mem z⟩ := by
    dsimp [g]
    rw [discExtend_of_mem _ (hrad_mem z)]
  have hrad_close' : ‖g (z : ℂ) - (f : C(UnitDisc, ℂ)) z‖ < ε / 2 := by
    rw [hg_eq]
    exact hrad_close z
  change ‖p.eval (z : ℂ) - (f : C(UnitDisc, ℂ)) z‖ < ε
  calc
    ‖p.eval (z : ℂ) - (f : C(UnitDisc, ℂ)) z‖
        ≤ ‖p.eval (z : ℂ) - g (z : ℂ)‖ + ‖g (z : ℂ) - (f : C(UnitDisc, ℂ)) z‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hps_close hrad_close'
    _ = ε := add_halves ε

theorem discPolyAlg_denseRange : DenseRange discPolyAlg := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  obtain ⟨p, hp⟩ := discPolyAlg_approx f hε
  exact ⟨p, by simpa only [dist_eq_norm, norm_sub_rev] using hp⟩

/-- Point-evaluation character `f ↦ f(α)` on `DiscAlgebra` for `α ∈ UnitDisc`. -/
def discEvalHom (α : UnitDisc) : ComplexHom DiscAlgebra where
  toLinearMap :=
    { toFun := fun f => (f : C(UnitDisc, ℂ)) α
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }
  ne_zero := fun h0 => by
    have h1 : (1 : ℂ) = 0 := congrArg (fun L : DiscAlgebra →ₗ[ℂ] ℂ => L 1) h0
    exact one_ne_zero h1
  map_mul' _ _ := rfl

@[simp]
theorem discEvalHom_apply (α : UnitDisc) (f : DiscAlgebra) :
    discEvalHom α f = (f : C(UnitDisc, ℂ)) α :=
  rfl

/-- **18.18 (Auxiliary character and maximal-ideal classification on `DiscAlgebra`):**
Every complex homomorphism `h : ComplexHom DiscAlgebra` is point evaluation at a unique point
`α ∈ UnitDisc` (`α = h discCoord`), and consequently the maximal ideals of `DiscAlgebra` are
precisely the vanishing ideals `{f ∈ DiscAlgebra | f(α) = 0}` for unique `α ∈ UnitDisc`. -/
theorem discAlgebra_characters_eq_eval :
    (∀ h : ComplexHom DiscAlgebra,
      ∃! α : UnitDisc, ∀ f : DiscAlgebra, h f = (f : C(UnitDisc, ℂ)) α) ∧
    (∀ M : Ideal DiscAlgebra,
      M.IsMaximal ↔ ∃! α : UnitDisc, (M : Set DiscAlgebra) = {f : DiscAlgebra | (f : C(UnitDisc, ℂ)) α = 0}) := by
  have hchar : ∀ h : ComplexHom DiscAlgebra,
      ∃! α : UnitDisc, ∀ f : DiscAlgebra, h f = (f : C(UnitDisc, ℂ)) α := by
    intro h
    have hspec : h discCoord ∈ spectrum ℂ discCoord :=
      ((theorem18_17_c discCoord).1 (h discCoord)).mpr ⟨h, rfl⟩
    have hmem : h discCoord ∈ UnitDisc := by
      rwa [theorem18_11.2.2.2.2.2.1] at hspec
    let α : UnitDisc := ⟨h discCoord, hmem⟩
    have hpoly : ∀ p : Polynomial ℂ, h (discPolyAlg p) = discEvalHom α (discPolyAlg p) := by
      intro p
      induction p using Polynomial.induction_on' with
      | add p q hp hq =>
        have hadd : discPolyAlg (p + q) = discPolyAlg p + discPolyAlg q := by
          ext z
          simp [discPolyAlg]
        rw [hadd, h.map_add, (discEvalHom α).map_add, hp, hq]
      | monomial n c =>
        have hmon : discPolyAlg (Polynomial.monomial n c) =
            algebraMap ℂ DiscAlgebra c * discCoord ^ n := by
          ext z
          simp [discPolyAlg, discCoord, Algebra.algebraMap_eq_smul_one, Polynomial.eval_monomial]
        rw [hmon, h.map_mul, h.map_algebraMap, h.map_pow,
          (discEvalHom α).map_mul, (discEvalHom α).map_algebraMap, (discEvalHom α).map_pow,
          discEvalHom_apply, discCoord_apply]
    have heq_fun : (h : DiscAlgebra → ℂ) = (discEvalHom α : DiscAlgebra → ℂ) :=
      discPolyAlg_denseRange.equalizer (theorem18_17_e h).1 (theorem18_17_e (discEvalHom α)).1
        (funext hpoly)
    refine ⟨α, fun f => congrFun heq_fun f, ?_⟩
    intro β hβ
    ext
    have hc := hβ discCoord
    simpa only [discCoord_apply] using hc.symm
  refine ⟨hchar, ?_⟩
  intro M
  constructor
  · intro hM
    obtain ⟨h, rfl, huniq⟩ := (theorem18_17_a (A := DiscAlgebra)).1 M hM
    obtain ⟨α, hα, hα_uniq⟩ := hchar h
    refine ⟨α, ?_, ?_⟩
    · ext f
      simp only [SetLike.mem_coe, RingHom.mem_ker, ComplexHom.toAlgHom_apply, hα f, mem_ofPred_eq]
    · intro β hβ
      apply hα_uniq
      have hker_eq : RingHom.ker (discEvalHom β).toAlgHom = RingHom.ker h.toAlgHom := by
        ext f
        change (f : C(UnitDisc, ℂ)) β = 0 ↔ f ∈ (RingHom.ker h.toAlgHom : Set DiscAlgebra)
        rw [hβ]
        rfl
      have hh_eq : discEvalHom β = h := huniq (discEvalHom β) hker_eq
      intro f
      exact (congrArg (fun k : ComplexHom DiscAlgebra => k f) hh_eq).symm
  · rintro ⟨α, hα, -⟩
    have hker : M = RingHom.ker (discEvalHom α).toAlgHom := by
      ext f
      change f ∈ (M : Set DiscAlgebra) ↔ (f : C(UnitDisc, ℂ)) α = 0
      rw [hα]
      rfl
    rw [hker]
    exact (theorem18_17_a (A := DiscAlgebra)).2 (discEvalHom α)

/-- **18.18 (Theorem: Finite disc-algebra Bezout identity):**
Let `f₁, …, fₙ ∈ DiscAlgebra`. There exist `g₁, …, gₙ ∈ DiscAlgebra` such that
`∑_{i=1}^n fᵢ(z) gᵢ(z) = 1` for every `z ∈ UnitDisc` (the closed unit disc) if and only if
`f₁, …, fₙ` have no common zero in `UnitDisc`. -/
theorem theorem18_18 {n : ℕ} (f : Fin n → DiscAlgebra) :
    (∀ z : UnitDisc, ∃ i : Fin n, (f i : C(UnitDisc, ℂ)) z ≠ 0) ↔
    ∃ g : Fin n → DiscAlgebra,
      ∀ z : UnitDisc, ∑ i : Fin n, (f i : C(UnitDisc, ℂ)) z * (g i : C(UnitDisc, ℂ)) z = 1 := by
  constructor
  · intro hnozero
    have htop : Ideal.span (Set.range f) = ⊤ := by
      by_contra hproper
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hproper
      obtain ⟨α, hα, -⟩ := (discAlgebra_characters_eq_eval.2 M).mp hM
      obtain ⟨i, hi⟩ := hnozero α
      have hmem : f i ∈ (M : Set DiscAlgebra) := hle (Ideal.subset_span ⟨i, rfl⟩)
      rw [hα] at hmem
      exact hi hmem
    have h1 : (1 : DiscAlgebra) ∈ Ideal.span (Set.range f) := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
    refine ⟨g, fun z => ?_⟩
    have heval := congrArg (discEvalHom z).toAlgHom hg
    simp only [map_sum, map_mul, map_one, ComplexHom.toAlgHom_apply, discEvalHom_apply] at heval
    simpa only [mul_comm] using heval
  · rintro ⟨g, hg⟩ z
    by_contra! hall
    have h0 := hg z
    simp only [hall, zero_mul, Finset.sum_const_zero] at h0
    exact zero_ne_one h0

private theorem fourier_mul_eq (a b : ℤ) :
    (fourier a * fourier b : C(FourierCircle, ℂ)) = fourier (a + b) := by
  ext t
  exact fourier_add.symm

private theorem fourier_zero_eq : (fourier (0 : ℤ) : C(FourierCircle, ℂ)) = 1 := by
  ext t
  exact fourier_zero

private theorem fourier_star_eq (a : ℤ) :
    star (fourier a : C(FourierCircle, ℂ)) = fourier (-a) := by
  ext t
  change conj (fourier a t) = fourier (-a) t
  rw [fourier_neg]

/-- Expresses `fourierCoeff φ n` on `C(FourierCircle, ℂ)` as a continuous linear functional via
`continuousIntegral circleMeasure`. -/
theorem fourierCoeff_eq_continuousIntegral (φ : C(FourierCircle, ℂ)) (n : ℤ) :
    fourierCoeff φ n = continuousIntegral circleMeasure (fourier (-n) * φ) := by
  rw [fourierCoeff, continuousIntegral_apply]
  rfl

theorem continuous_fourierCoeff_eval (n : ℤ) :
    Continuous (fun φ : C(FourierCircle, ℂ) => fourierCoeff φ n) := by
  simp_rw [fourierCoeff_eq_continuousIntegral]
  exact (continuousIntegral circleMeasure).continuous.comp (continuous_const.mul continuous_id)

/-- Every nonnegative trigonometric monomial `fourier (k : ℤ)` (`k : ℕ`) belongs to
`DiscAlgebraCircle`. -/
theorem fourier_nat_mem_discAlgebraCircle (k : ℕ) :
    (fourier (k : ℤ) : C(FourierCircle, ℂ)) ∈ DiscAlgebraCircle := by
  have heq : (fourier (k : ℤ) : C(FourierCircle, ℂ)) =
      (discCoordCircle ^ k : DiscAlgebraCircle) := by
    ext t
    simp only [Subalgebra.coe_pow, ContinuousMap.pow_apply, discCoordCircle_coe]
    exact circleCoordinate_pow k t
  rw [heq]
  exact (discCoordCircle ^ k).property

/-- **18.19 (Part 1 — Fourier characterization of the boundary disc algebra `DiscAlgebraCircle`):**
A continuous function `φ ∈ C(FourierCircle, ℂ)` belongs to `DiscAlgebraCircle` if and only if
`fourierCoeff φ n = 0` for every negative integer `n < 0`. -/
theorem discAlgebraCircle_iff_fourierCoeff_neg_eq_zero (φ : C(FourierCircle, ℂ)) :
    φ ∈ DiscAlgebraCircle ↔ ∀ n : ℤ, n < 0 → fourierCoeff φ n = 0 := by
  constructor
  · intro hφ n hn
    obtain ⟨f, rfl⟩ : ∃ f : DiscAlgebra, discBoundaryHom f = φ := hφ
    have hpoly_zero : ∀ p : Polynomial ℂ, fourierCoeff (discBoundaryHom (discPolyAlg p)) n = 0 := by
      intro p
      induction p using Polynomial.induction_on' with
      | add p q hp hq =>
        have hadd : discBoundaryHom (discPolyAlg (p + q)) =
            discBoundaryHom (discPolyAlg p) + discBoundaryHom (discPolyAlg q) := by
          ext t
          simp [discPolyAlg]
        rw [hadd, fourierCoeff_eq_continuousIntegral, mul_add, map_add,
          ← fourierCoeff_eq_continuousIntegral, ← fourierCoeff_eq_continuousIntegral, hp, hq,
          add_zero]
      | monomial k c =>
        have hmon : discBoundaryHom (discPolyAlg (Polynomial.monomial k c)) =
            c • fourier (k : ℤ) := by
          ext t
          simp only [discBoundaryHom_apply, discPolyAlg_coe, discPolynomial_apply,
            Polynomial.eval_monomial, discBoundary_coe, ContinuousMap.smul_apply, smul_eq_mul]
          rw [circleCoordinate_pow k t]
        rw [hmon, fourierCoeff_eq_continuousIntegral, mul_smul_comm, map_smul,
          fourier_mul_eq, continuousIntegral_apply]
        have hkne : -n + (k : ℤ) ≠ 0 := by omega
        have hint : (∫ t : FourierCircle, fourier (-n + (k : ℤ)) t ∂circleMeasure) = 0 := by
          rw [circleMeasure, integral_fourier_monomial]
          simp [hkne]
        rw [hint, smul_zero]
    by_contra hne
    have hpos : 0 < ‖fourierCoeff (discBoundaryHom f) n‖ := norm_pos_iff.mpr hne
    obtain ⟨p, hp⟩ := discPolyAlg_approx f hpos
    have hdiff_eq : fourierCoeff (discBoundaryHom f) n =
        continuousIntegral circleMeasure
          ((fourier (-n) : C(FourierCircle, ℂ)) *
            (discBoundaryHom f - discBoundaryHom (discPolyAlg p))) := by
      rw [mul_sub, map_sub, ← fourierCoeff_eq_continuousIntegral,
        ← fourierCoeff_eq_continuousIntegral, hpoly_zero p, sub_zero]
    have hle : ‖fourierCoeff (discBoundaryHom f) n‖ ≤
        ‖discBoundaryHom f - discBoundaryHom (discPolyAlg p)‖ := by
      rw [hdiff_eq, continuousIntegral_apply]
      have hpt : ∀ t : FourierCircle,
          ‖((fourier (-n) : C(FourierCircle, ℂ)) *
              (discBoundaryHom f - discBoundaryHom (discPolyAlg p))) t‖ ≤
            ‖discBoundaryHom f - discBoundaryHom (discPolyAlg p)‖ := by
        intro t
        rw [ContinuousMap.mul_apply, norm_mul, fejerFourier_norm, one_mul]
        exact (discBoundaryHom f - discBoundaryHom (discPolyAlg p)).norm_coe_le_norm t
      simpa using MeasureTheory.norm_integral_le_of_norm_le_const (μ := circleMeasure)
        (Eventually.of_forall hpt)
    have hiso_norm : ‖discBoundaryHom f - discBoundaryHom (discPolyAlg p)‖ =
        ‖discPolyAlg p - f‖ := by
      rw [← map_sub, discBoundaryHom_norm, norm_sub_rev]
    rw [hiso_norm] at hle
    exact (hle.trans_lt hp).false
  · intro hneg
    have hpartial_mem : ∀ k : ℕ, fejerFourierPartialSum φ k ∈ DiscAlgebraCircle := by
      intro k
      unfold fejerFourierPartialSum
      refine DiscAlgebraCircle.sum_mem fun n _ => ?_
      by_cases hn : n < 0
      · rw [hneg n hn, zero_smul]
        exact DiscAlgebraCircle.zero_mem
      · push Not at hn
        have hn_eq : n = (n.toNat : ℤ) := (Int.toNat_of_nonneg hn).symm
        rw [hn_eq]
        exact DiscAlgebraCircle.smul_mem (fourier_nat_mem_discAlgebraCircle n.toNat) _
    have hmean_mem : ∀ N : ℕ, fejerMean φ N ∈ DiscAlgebraCircle := by
      intro N
      unfold fejerMean
      exact DiscAlgebraCircle.smul_mem
        (DiscAlgebraCircle.sum_mem fun k _ => hpartial_mem k) _
    exact isClosed_discAlgebraCircle.mem_of_tendsto (fejerMean_tendsto φ)
      (Eventually.of_forall hmean_mem)

/-- Bohnenblust–Karlin / Gleason–Kahane–Żelazko real-part lemma: any continuous linear functional
`Φ : StrongDual ℂ C(FourierCircle, ℂ)` with `‖Φ‖ ≤ 1` and `Φ 1 = 1` maps real-valued functions to
real numbers and respects pointwise complex conjugation `star`. -/
private theorem normOne_unital_map_star (Φ : StrongDual ℂ C(FourierCircle, ℂ))
    (hΦ_norm : ‖Φ‖ ≤ 1) (hΦ_one : Φ 1 = 1) :
    ∀ ψ : C(FourierCircle, ℂ), Φ (star ψ) = conj (Φ ψ) := by
  have hreal : ∀ u : C(FourierCircle, ℂ), (∀ t : FourierCircle, (u t).im = 0) → (Φ u).im = 0 := by
    intro u hu
    let α : ℝ := (Φ u).re
    let β : ℝ := (Φ u).im
    have hΦu : Φ u = (α : ℂ) + (β : ℂ) * Complex.I := (Complex.re_add_im (Φ u)).symm
    have hbound : ∀ R : ℝ, α ^ 2 + β ^ 2 + 2 * β * R ≤ ‖u‖ ^ 2 := by
      intro R
      let v : C(FourierCircle, ℂ) := u + ((R : ℂ) * Complex.I) • (1 : C(FourierCircle, ℂ))
      have hv_norm_le : ‖v‖ ≤ Real.sqrt (‖u‖ ^ 2 + R ^ 2) := by
        apply (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).mpr
        intro t
        have hut : u t = ((u t).re : ℂ) := Complex.ext rfl (hu t)
        have hvt : v t = ((u t).re : ℂ) + (R : ℂ) * Complex.I := by
          change u t + (R : ℂ) * Complex.I * 1 = _
          rw [mul_one, ← hut]
        have hsq : ‖v t‖ ^ 2 ≤ ‖u‖ ^ 2 + R ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, hvt]
          have hns : Complex.normSq (((u t).re : ℂ) + (R : ℂ) * Complex.I) =
              (u t).re ^ 2 + R ^ 2 := by
            simp [Complex.normSq_apply]
            ring
          rw [hns]
          have hre_le : |(u t).re| ≤ ‖u‖ :=
            (Complex.abs_re_le_norm (u t)).trans (u.norm_coe_le_norm t)
          have hre_sq : (u t).re ^ 2 ≤ ‖u‖ ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) hre_le 2
          linarith
        calc
          ‖v t‖ = Real.sqrt (‖v t‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (‖u‖ ^ 2 + R ^ 2) := Real.sqrt_le_sqrt hsq
      have hΦv_le : ‖Φ v‖ ≤ Real.sqrt (‖u‖ ^ 2 + R ^ 2) := by
        calc
          ‖Φ v‖ ≤ ‖Φ‖ * ‖v‖ := Φ.le_opNorm v
          _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hΦ_norm (norm_nonneg v)
          _ = ‖v‖ := one_mul _
          _ ≤ Real.sqrt (‖u‖ ^ 2 + R ^ 2) := hv_norm_le
      have hΦv_eq : Φ v = (α : ℂ) + ((β + R : ℝ) : ℂ) * Complex.I := by
        simp only [v, map_add, map_smul, hΦ_one, smul_eq_mul, mul_one, hΦu, Complex.ofReal_add]
        ring
      have hΦv_sq : α ^ 2 + (β + R) ^ 2 = ‖Φ v‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, hΦv_eq]
        simp [Complex.normSq_apply]
        ring
      have hsq_le : ‖Φ v‖ ^ 2 ≤ ‖u‖ ^ 2 + R ^ 2 := by
        calc
          ‖Φ v‖ ^ 2 ≤ (Real.sqrt (‖u‖ ^ 2 + R ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hΦv_le 2
          _ = ‖u‖ ^ 2 + R ^ 2 := Real.sq_sqrt (by positivity)
      linarith
    by_contra hβ
    have hβ' : β ≠ 0 := hβ
    have hspec := hbound ((‖u‖ ^ 2 + 1) / (2 * β))
    have hmul : 2 * β * ((‖u‖ ^ 2 + 1) / (2 * β)) = ‖u‖ ^ 2 + 1 := by
      field_simp [hβ']
    rw [hmul] at hspec
    nlinarith [sq_nonneg α, sq_nonneg β]
  intro ψ
  let u : C(FourierCircle, ℂ) := ((2 : ℂ)⁻¹) • (ψ + star ψ)
  let w : C(FourierCircle, ℂ) := (-(2 : ℂ)⁻¹ * Complex.I) • (ψ - star ψ)
  have hu_im : ∀ t : FourierCircle, (u t).im = 0 := by
    intro t
    simp [u]
  have hw_im : ∀ t : FourierCircle, (w t).im = 0 := by
    intro t
    simp [w]
  have hψ_eq : ψ = u + Complex.I • w := by
    ext t
    simp only [u, w, ContinuousMap.add_apply, ContinuousMap.sub_apply,
      ContinuousMap.smul_apply, ContinuousMap.star_apply, smul_eq_mul]
    apply Complex.ext <;> simp <;> ring
  have hstar_eq : star ψ = u - Complex.I • w := by
    ext t
    simp only [u, w, ContinuousMap.add_apply, ContinuousMap.sub_apply,
      ContinuousMap.smul_apply, ContinuousMap.star_apply, smul_eq_mul]
    apply Complex.ext <;> simp <;> ring
  have hconj_u : conj (Φ u) = Φ u := Complex.conj_eq_iff_im.mpr (hreal u hu_im)
  have hconj_w : conj (Φ w) = Φ w := Complex.conj_eq_iff_im.mpr (hreal w hw_im)
  have h1 : Φ (star ψ) = Φ u - Complex.I * Φ w := by
    calc
      Φ (star ψ) = Φ (u - Complex.I • w) := congrArg Φ hstar_eq
      _ = Φ u - Φ (Complex.I • w) := Φ.map_sub u (Complex.I • w)
      _ = Φ u - Complex.I * Φ w := by rw [Φ.map_smul Complex.I w, smul_eq_mul]
  have h2 : conj (Φ ψ) = Φ u - Complex.I * Φ w := by
    calc
      conj (Φ ψ) = conj (Φ (u + Complex.I • w)) := congrArg (fun z => conj (Φ z)) hψ_eq
      _ = conj (Φ u + Complex.I * Φ w) := by rw [Φ.map_add, Φ.map_smul Complex.I w, smul_eq_mul]
      _ = conj (Φ u) + conj Complex.I * conj (Φ w) := by rw [map_add, map_mul]
      _ = Φ u - Complex.I * Φ w := by rw [Complex.conj_I, hconj_u, hconj_w]; ring
  exact h1.trans h2.symm

/-- **18.20 (Theorem: Uniform density after adjoining a function with a nonzero negative Fourier
mode):**
Suppose `f ∈ C(FourierCircle, ℂ)` has at least one nonzero negative Fourier coefficient
(`∃ n < 0, fourierCoeff f n ≠ 0`). Then the `ℂ`-subalgebra generated by `DiscAlgebraCircle` and `f`
is uniformly dense in `C(FourierCircle, ℂ)`: every `g ∈ C(FourierCircle, ℂ)` can be uniformly
approximated on `FourierCircle` by polynomials in `f` with coefficients in `DiscAlgebraCircle`. -/
theorem theorem18_20 (f : C(FourierCircle, ℂ))
    (hf : ∃ n : ℤ, n < 0 ∧ fourierCoeff f n ≠ 0) :
    (Algebra.adjoin ℂ ((DiscAlgebraCircle : Set C(FourierCircle, ℂ)) ∪ {f})).topologicalClosure = ⊤ ∧
    ∀ g : C(FourierCircle, ℂ), ∀ ε : ℝ, 0 < ε →
      ∃ p ∈ Algebra.adjoin ℂ ((DiscAlgebraCircle : Set C(FourierCircle, ℂ)) ∪ {f}), ‖p - g‖ < ε := by
  let S₀ : Subalgebra ℂ C(FourierCircle, ℂ) :=
    Algebra.adjoin ℂ ((DiscAlgebraCircle : Set C(FourierCircle, ℂ)) ∪ {f})
  let B : Subalgebra ℂ C(FourierCircle, ℂ) := S₀.topologicalClosure
  have hB_closed : IsClosed (B : Set C(FourierCircle, ℂ)) := S₀.isClosed_topologicalClosure
  have : CompleteSpace B := hB_closed.completeSpace_coe
  have : NormOneClass B := ⟨show ‖(1 : B)‖ = 1 from norm_one (α := C(FourierCircle, ℂ))⟩
  have hle_S₀ : S₀ ≤ B := S₀.le_topologicalClosure
  have hdisc_le : DiscAlgebraCircle ≤ B := by
    intro g hg
    exact hle_S₀ (Algebra.subset_adjoin (Or.inl hg))
  have hf_mem : f ∈ B := hle_S₀ (Algebra.subset_adjoin (Or.inr (Set.mem_singleton f)))
  let zB : B := ⟨circleCoordinate, hdisc_le (fourier_nat_mem_discAlgebraCircle 1)⟩
  have hzB_unit : IsUnit zB := by
    by_contra hnotu
    have hex_h : ∃ h : ComplexHom B, h zB = 0 := by
      by_contra! hall
      exact hnotu ((theorem18_17_b zB).1.mpr hall)
    obtain ⟨h, hhz⟩ := hex_h
    have hh_norm : ‖h.toCLM‖ = 1 := (theorem18_17_e h).2.2
    obtain ⟨Φ, hΦ_ext, hΦ_norm⟩ := exists_extension_norm_eq B.toSubmodule h.toCLM
    have hΦ_norm1 : ‖Φ‖ = 1 := hΦ_norm.trans hh_norm
    have hΦ_one : Φ 1 = 1 := by
      have h1 := hΦ_ext (1 : B)
      simpa only [Subalgebra.coe_one, Submodule.coe_mk, ComplexHom.toCLM_apply, h.map_one] using h1
    have hΦ_star := normOne_unital_map_star Φ hΦ_norm1.le hΦ_one
    have hΦ_pos : ∀ k : ℕ, 1 ≤ k → Φ (fourier (k : ℤ)) = 0 := by
      intro k hk
      have hzk_coe : ((zB ^ k : B) : C(FourierCircle, ℂ)) = fourier (k : ℤ) := by
        ext t
        simp only [Subalgebra.coe_pow, ContinuousMap.pow_apply, zB]
        exact (circleCoordinate_pow k t).symm
      rw [← hzk_coe]
      have hext_k := hΦ_ext (zB ^ k)
      change Φ ((zB ^ k : B) : C(FourierCircle, ℂ)) = h (zB ^ k) at hext_k
      rw [hext_k, h.map_pow, hhz, zero_pow (by omega)]
    have hΦ_monomial : ∀ n : ℤ,
        Φ (fourier n) = continuousIntegral circleMeasure (fourier n) := by
      intro n
      rw [continuousIntegral_apply, circleMeasure, integral_fourier_monomial]
      rcases lt_trichotomy n 0 with hn | rfl | hn
      · let k : ℕ := (-n).toNat
        have hk1 : 1 ≤ k := by omega
        have hn_eq : n = -(k : ℤ) := by omega
        have hite : (if n = 0 then (1 : ℂ) else 0) = 0 := by simp [hn.ne]
        rw [hite, hn_eq, ← fourier_star_eq, hΦ_star, hΦ_pos k hk1, map_zero]
      · simp [fourier_zero_eq, hΦ_one]
      · let k : ℕ := n.toNat
        have hk1 : 1 ≤ k := by omega
        have hn_eq : n = (k : ℤ) := (Int.toNat_of_nonneg hn.le).symm
        have hite : (if n = 0 then (1 : ℂ) else 0) = 0 := by simp [hn.ne']
        rw [hite, hn_eq, hΦ_pos k hk1]
    have hd : Dense (Submodule.span ℂ (Set.range (trigMonomial : ℤ → C(FourierCircle, ℂ))) :
        Set C(FourierCircle, ℂ)) := by
      rw [dense_iff_closure_eq]
      change ((Submodule.span ℂ (Set.range (trigMonomial : ℤ → C(FourierCircle, ℂ)))).topologicalClosure :
        Set C(FourierCircle, ℂ)) = Set.univ
      rw [span_fourier_closure_eq_top]
      rfl
    have hΦ_eq_int : Φ = continuousIntegral circleMeasure :=
      ContinuousLinearMap.ext_on hd (by rintro _ ⟨n, rfl⟩; exact hΦ_monomial n)
    obtain ⟨n₀, hn₀_neg, hn₀_ne⟩ := hf
    let m : ℕ := (-n₀).toNat
    have hm1 : 1 ≤ m := by omega
    have hn₀_eq : n₀ = -(m : ℤ) := by omega
    let fB : B := ⟨f, hf_mem⟩
    have hzero_lhs : h (zB ^ m * fB) = 0 := by
      rw [h.map_mul, h.map_pow, hhz, zero_pow (by omega), zero_mul]
    have hcoe_prod : ((zB ^ m * fB : B) : C(FourierCircle, ℂ)) = fourier (m : ℤ) * f := by
      ext t
      simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, ContinuousMap.mul_apply,
        ContinuousMap.pow_apply, zB, fB]
      rw [circleCoordinate_pow m t]
    have hval_rhs : h (zB ^ m * fB) = fourierCoeff f n₀ := by
      have hext_prod := hΦ_ext (zB ^ m * fB)
      change Φ ((zB ^ m * fB : B) : C(FourierCircle, ℂ)) = h (zB ^ m * fB) at hext_prod
      rw [← hext_prod, hcoe_prod, hΦ_eq_int, hn₀_eq, fourierCoeff_eq_continuousIntegral, neg_neg]
    exact hn₀_ne (hval_rhs ▸ hzero_lhs)
  rcases hzB_unit with ⟨uz, huz⟩
  have hinv_mem : fourier (-1 : ℤ) ∈ B := by
    have hmul1 : circleCoordinate * ((↑uz⁻¹ : B) : C(FourierCircle, ℂ)) = 1 := by
      have h1 : ((uz * uz⁻¹ : Bˣ) : B) = 1 := by simp
      have hcoe := congrArg (fun x : B => (x : C(FourierCircle, ℂ))) h1
      simpa only [Units.val_mul, Subalgebra.coe_mul, Subalgebra.coe_one, huz, zB] using hcoe
    have hmul2 : circleCoordinate * fourier (-1 : ℤ) = 1 := by
      change fourier (1 : ℤ) * fourier (-1 : ℤ) = 1
      rw [fourier_mul_eq]
      simpa using fourier_zero_eq
    have heq_inv : (fourier (-1 : ℤ) : C(FourierCircle, ℂ)) = ((↑uz⁻¹ : B) : C(FourierCircle, ℂ)) := by
      calc
        fourier (-1 : ℤ) = fourier (-1 : ℤ) * (circleCoordinate * ((↑uz⁻¹ : B) : C(FourierCircle, ℂ))) := by
          rw [hmul1, mul_one]
        _ = (circleCoordinate * fourier (-1 : ℤ)) * ((↑uz⁻¹ : B) : C(FourierCircle, ℂ)) := by ring
        _ = ((↑uz⁻¹ : B) : C(FourierCircle, ℂ)) := by rw [hmul2, one_mul]
    rw [heq_inv]
    exact (↑uz⁻¹ : B).property
  have hall_monomial : ∀ n : ℤ, (trigMonomial n : C(FourierCircle, ℂ)) ∈ B := by
    intro n
    rcases le_or_gt 0 n with hn | hn
    · have hn_eq : n = (n.toNat : ℤ) := (Int.toNat_of_nonneg hn).symm
      rw [trigMonomial, hn_eq]
      exact hdisc_le (fourier_nat_mem_discAlgebraCircle n.toNat)
    · let k : ℕ := (-n).toNat
      have hn_eq : n = -(k : ℤ) := by omega
      have hpow : (fourier (-(k : ℤ)) : C(FourierCircle, ℂ)) = fourier (-1 : ℤ) ^ k := by
        induction k with
        | zero =>
          simpa using fourier_zero_eq
        | succ k ih =>
          have hstep : -(((k + 1 : ℕ) : ℤ)) = -(k : ℤ) + (-1 : ℤ) := by omega
          rw [hstep, pow_succ, ← fourier_mul_eq, ih]
      rw [trigMonomial, hn_eq, hpow]
      exact B.pow_mem hinv_mem k
  have hspan_le : Submodule.span ℂ (Set.range (trigMonomial : ℤ → C(FourierCircle, ℂ))) ≤
      B.toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    exact hall_monomial n
  have htop_sub : B.toSubmodule = ⊤ := by
    apply top_unique
    rw [← span_fourier_closure_eq_top]
    exact Submodule.topologicalClosure_minimal _ hspan_le hB_closed
  have hB_top : B = ⊤ := by
    ext g
    have hmem : g ∈ B.toSubmodule := by
      rw [htop_sub]
      exact Submodule.mem_top
    simpa using hmem
  refine ⟨hB_top, fun g ε hε => ?_⟩
  have hg_cl : g ∈ closure (S₀ : Set C(FourierCircle, ℂ)) := by
    change g ∈ (B : Set C(FourierCircle, ℂ))
    rw [hB_top]
    trivial
  obtain ⟨p, hp_mem, hp_dist⟩ := Metric.mem_closure_iff.mp hg_cl ε hε
  exact ⟨p, hp_mem, by simpa only [dist_eq_norm, norm_sub_rev] using hp_dist⟩

/-- **18.19 (Exposition with claims: Fourier characterization of `DiscAlgebraCircle` and Wermer's
maximality theorem):**
1. A function `φ ∈ C(FourierCircle, ℂ)` belongs to `DiscAlgebraCircle` iff `fourierCoeff φ n = 0`
   for all `n < 0`;
2. `DiscAlgebraCircle` is a proper closed subalgebra of `C(FourierCircle, ℂ)` (`DiscAlgebraCircle ≠ ⊤`),
   and it is **maximal** among closed subalgebras: for every closed subalgebra
   `B : Subalgebra ℂ C(FourierCircle, ℂ)` with `DiscAlgebraCircle ≤ B`, either
   `B = DiscAlgebraCircle` or `B = ⊤`. -/
theorem theorem18_19 :
    (∀ φ : C(FourierCircle, ℂ),
      φ ∈ DiscAlgebraCircle ↔ ∀ n : ℤ, n < 0 → fourierCoeff φ n = 0) ∧
    DiscAlgebraCircle ≠ ⊤ ∧
    (∀ B : Subalgebra ℂ C(FourierCircle, ℂ),
      IsClosed (B : Set C(FourierCircle, ℂ)) → DiscAlgebraCircle ≤ B →
        B = DiscAlgebraCircle ∨ B = ⊤) := by
  refine ⟨discAlgebraCircle_iff_fourierCoeff_neg_eq_zero, ?_, ?_⟩
  · intro htop
    have hmem : (fourier (-1 : ℤ) : C(FourierCircle, ℂ)) ∈ DiscAlgebraCircle := by
      rw [htop]
      trivial
    have hzero := (discAlgebraCircle_iff_fourierCoeff_neg_eq_zero _).mp hmem (-1) (by omega)
    have hone : fourierCoeff (fourier (-1 : ℤ) : C(FourierCircle, ℂ)) (-1) = 1 := by
      rw [fourierCoeff_eq_continuousIntegral, neg_neg, continuousIntegral_apply]
      have hprod : (fourier (1 : ℤ) * fourier (-1 : ℤ) : C(FourierCircle, ℂ)) = fourier 0 := by
        rw [fourier_mul_eq]
        norm_num
      rw [hprod, circleMeasure, integral_fourier_monomial]
      simp
    exact one_ne_zero (hone ▸ hzero)
  · intro B hB_closed hle
    by_cases hsub : B ≤ DiscAlgebraCircle
    · exact Or.inl (le_antisymm hsub hle)
    · refine Or.inr ?_
      have hex : ∃ f ∈ B, f ∉ DiscAlgebraCircle := by
        by_contra! hall
        exact hsub fun f hf => hall f hf
      obtain ⟨f, hfB, hf_not⟩ := hex
      have hneg_ne : ∃ n : ℤ, n < 0 ∧ fourierCoeff f n ≠ 0 := by
        by_contra! hall_zero
        exact hf_not ((discAlgebraCircle_iff_fourierCoeff_neg_eq_zero f).mpr hall_zero)
      have hadj_le :
          Algebra.adjoin ℂ ((DiscAlgebraCircle : Set C(FourierCircle, ℂ)) ∪ {f}) ≤ B := by
        rw [Algebra.adjoin_le_iff]
        rintro g (hg | rfl)
        · exact hle hg
        · exact hfB
      have hcl_le :
          (Algebra.adjoin ℂ ((DiscAlgebraCircle : Set C(FourierCircle, ℂ)) ∪ {f})).topologicalClosure ≤
            B :=
        Subalgebra.topologicalClosure_minimal hadj_le hB_closed
      rw [(theorem18_20 f hneg_ne).1] at hcl_le
      exact top_unique hcl_le

end DiscAlgebraApplications

/-! ## Section 4: Wiener's Theorem on Absolutely Convergent Fourier Series (`18.21`) -/

section WienerTheorem

open RudinRCA.Chapter04 RudinRCA.Chapter05
open scoped lp

private theorem wienerHasSum_norm (u : ℓ¹(ℤ, ℂ)) :
    HasSum (fun n : ℤ => ‖u n‖) ‖u‖ := by
  simpa using lp.hasSum_norm (by simp : 0 < (1 : ℝ≥0∞).toReal) u

private theorem wienerSummable_norm (u : ℓ¹(ℤ, ℂ)) :
    Summable (fun n : ℤ => ‖u n‖) :=
  (wienerHasSum_norm u).summable

private theorem wienerSummable_fourier (u : ℓ¹(ℤ, ℂ)) :
    Summable (fun n : ℤ => u n • (fourier n : C(FourierCircle, ℂ))) := by
  refine Summable.of_norm_bounded (wienerSummable_norm u) fun n => ?_
  rw [norm_smul, show ‖(fourier n : C(FourierCircle, ℂ))‖ = 1 from trigMonomial_norm n, mul_one]

/-- Continuous linear map `ℓ¹(ℤ, ℂ) →L[ℂ] C(FourierCircle, ℂ)` summing an absolutely convergent
Fourier series `u ↦ ∑' n : ℤ, u n • fourier n`. -/
def wienerSeriesCLM : ℓ¹(ℤ, ℂ) →L[ℂ] C(FourierCircle, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun u => ∑' n : ℤ, u n • fourier n
      map_add' := fun u v => by
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact ((wienerSummable_fourier u).hasSum.add (wienerSummable_fourier v).hasSum).tsum_eq
      map_smul' := fun c u => by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_assoc, RingHom.id_apply]
        exact ((wienerSummable_fourier u).hasSum.const_smul c).tsum_eq }
    1
    (fun u => by
      rw [one_mul]
      have hnorm_sum : Summable (fun n : ℤ => ‖u n • (fourier n : C(FourierCircle, ℂ))‖) :=
        (wienerSummable_norm u).congr fun n => by
          rw [norm_smul, show ‖(fourier n : C(FourierCircle, ℂ))‖ = 1 from trigMonomial_norm n,
            mul_one]
      calc
        ‖∑' n : ℤ, u n • (fourier n : C(FourierCircle, ℂ))‖
            ≤ ∑' n : ℤ, ‖u n • (fourier n : C(FourierCircle, ℂ))‖ :=
          norm_tsum_le_tsum_norm hnorm_sum
        _ = ∑' n : ℤ, ‖u n‖ := by
          congr 1; ext n
          rw [norm_smul, show ‖(fourier n : C(FourierCircle, ℂ))‖ = 1 from trigMonomial_norm n,
            mul_one]
        _ = ‖u‖ := (wienerHasSum_norm u).tsum_eq)

theorem wienerHasSum_fourier (u : ℓ¹(ℤ, ℂ)) :
    HasSum (fun n : ℤ => u n • (fourier n : C(FourierCircle, ℂ))) (wienerSeriesCLM u) :=
  (wienerSummable_fourier u).hasSum

theorem wienerHasSum_eval (u : ℓ¹(ℤ, ℂ)) (t : FourierCircle) :
    HasSum (fun n : ℤ => u n * trigMonomial n t) (wienerSeriesCLM u t) := by
  let evalHom : AddMonoidHom C(FourierCircle, ℂ) ℂ :=
    { toFun := fun φ => φ t
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hcont : Continuous evalHom :=
    (LipschitzWith.mk_one fun φ ψ => by
      change dist (φ t) (ψ t) ≤ dist φ ψ
      rw [dist_eq_norm, dist_eq_norm]
      exact ContinuousMap.norm_coe_le_norm (φ - ψ) t).continuous
  have hterm : ∀ n : ℤ,
      u n * trigMonomial n t =
        (evalHom ∘ fun k : ℤ => u k • (fourier k : C(FourierCircle, ℂ))) n := by
    intro n
    change u n * trigMonomial n t = ((u n • (fourier n : C(FourierCircle, ℂ))) t)
    rw [ContinuousMap.smul_apply, smul_eq_mul]
  exact ((wienerHasSum_fourier u).map evalHom hcont).congr_fun hterm

theorem wienerSeriesCLM_apply_eval (u : ℓ¹(ℤ, ℂ)) (t : FourierCircle) :
    wienerSeriesCLM u t = ∑' n : ℤ, u n * trigMonomial n t :=
  (wienerHasSum_eval u t).tsum_eq.symm

theorem wienerSeriesCLM_single (m : ℤ) (c : ℂ) :
    wienerSeriesCLM (lp.single 1 m c) = c • (fourier m : C(FourierCircle, ℂ)) := by
  let f : ℤ → C(FourierCircle, ℂ) := fun n =>
    (lp.single (E := fun _ : ℤ => ℂ) 1 m c n) • (fourier n : C(FourierCircle, ℂ))
  have h1 : HasSum f (wienerSeriesCLM (lp.single 1 m c)) :=
    wienerHasSum_fourier (lp.single 1 m c)
  have h2 : HasSum f (f m) := hasSum_single m fun n hn => by
    dsimp [f]
    rw [Pi.single_eq_of_ne hn, zero_smul]
  have hfm : f m = c • (fourier m : C(FourierCircle, ℂ)) := by
    dsimp [f]
    rw [Pi.single_eq_same]
  rw [← hfm]
  exact h1.unique h2

/-- The `k`-th Fourier coefficient of `wienerSeriesCLM u` recovers `u k`. -/
theorem fourierCoeff_wienerSeriesCLM (u : ℓ¹(ℤ, ℂ)) (k : ℤ) :
    fourierCoeff (wienerSeriesCLM u) k = u k := by
  let fk : AddMonoidHom C(FourierCircle, ℂ) ℂ :=
    { toFun := fun φ => fourierCoeff φ k
      map_zero' := by
        rw [fourierCoeff_eq_continuousIntegral (0 : C(FourierCircle, ℂ)) k, mul_zero, map_zero]
      map_add' := fun φ ψ => by
        rw [fourierCoeff_eq_continuousIntegral (φ + ψ) k,
          fourierCoeff_eq_continuousIntegral φ k,
          fourierCoeff_eq_continuousIntegral ψ k, mul_add, map_add] }
  have hsum := (wienerHasSum_fourier u).map fk (continuous_fourierCoeff_eval k)
  have hterm : ∀ n : ℤ,
      (if n = k then u k else 0) =
        (fk ∘ fun m : ℤ => u m • (fourier m : C(FourierCircle, ℂ))) n := by
    intro n
    symm
    change fourierCoeff (u n • (fourier n : C(FourierCircle, ℂ))) k = _
    rw [fourierCoeff_eq_continuousIntegral, mul_smul_comm, fourier_mul_eq,
      (continuousIntegral circleMeasure).map_smul, continuousIntegral_apply,
      circleMeasure, integral_fourier_monomial, smul_eq_mul]
    by_cases hnk : n = k
    · subst hnk
      simp
    · have hadd : -k + n ≠ 0 := by omega
      simp [hnk, hadd]
  exact (hsum.congr_fun hterm).unique (hasSum_ite_eq k (u k))

theorem wienerSeriesCLM_injective : Function.Injective wienerSeriesCLM := by
  intro u v huv
  ext k
  rw [← fourierCoeff_wienerSeriesCLM u k, ← fourierCoeff_wienerSeriesCLM v k, huv]

/-- Right-shift operator `(wienerShift m v) n = v (n - m)` on `ℓ¹(ℤ, ℂ)`. -/
def wienerShift (m : ℤ) (v : ℓ¹(ℤ, ℂ)) : ℓ¹(ℤ, ℂ) :=
  ⟨fun n => v (n - m),
    memℓp_gen (by
      simpa [Function.comp_def] using
        ((Equiv.subRight m).hasSum_iff.mpr (wienerHasSum_norm v)).summable)⟩

@[simp]
theorem wienerShift_apply (m : ℤ) (v : ℓ¹(ℤ, ℂ)) (n : ℤ) :
    wienerShift m v n = v (n - m) :=
  rfl

theorem wienerShift_norm (m : ℤ) (v : ℓ¹(ℤ, ℂ)) :
    ‖wienerShift m v‖ = ‖v‖ :=
  (wienerHasSum_norm (wienerShift m v)).unique
    ((Equiv.subRight m).hasSum_iff.mpr (wienerHasSum_norm v))

theorem wienerSeriesCLM_shift (m : ℤ) (v : ℓ¹(ℤ, ℂ)) :
    wienerSeriesCLM (wienerShift m v) = fourier m * wienerSeriesCLM v := by
  let mulL : AddMonoidHom C(FourierCircle, ℂ) C(FourierCircle, ℂ) :=
    { toFun := fun φ => fourier m * φ
      map_zero' := mul_zero _
      map_add' := mul_add _ }
  have hmul : HasSum (fun k : ℤ => v k • (fourier (m + k) : C(FourierCircle, ℂ)))
      (fourier m * wienerSeriesCLM v) := by
    have h1 := (wienerHasSum_fourier v).map mulL (continuous_const.mul continuous_id)
    have hterm : ∀ k : ℤ,
        v k • (fourier (m + k) : C(FourierCircle, ℂ)) =
          (mulL ∘ fun n : ℤ => v n • (fourier n : C(FourierCircle, ℂ))) k := by
      intro k
      symm
      change fourier m * (v k • fourier k) = v k • fourier (m + k)
      rw [mul_smul_comm, fourier_mul_eq]
    exact h1.congr_fun hterm
  have hreidx : HasSum (fun n : ℤ => v (n - m) • (fourier n : C(FourierCircle, ℂ)))
      (fourier m * wienerSeriesCLM v) := by
    have h2 := (Equiv.subRight m).hasSum_iff.mpr hmul
    simpa only [Function.comp_def, Equiv.subRight_apply, add_sub_cancel] using h2
  exact (wienerHasSum_fourier (wienerShift m v)).unique hreidx

private theorem wienerConv_summable (u v : ℓ¹(ℤ, ℂ)) :
    Summable (fun m : ℤ => u m • wienerShift m v) := by
  refine Summable.of_norm_bounded ((wienerSummable_norm u).mul_right ‖v‖) fun m => ?_
  rw [norm_smul, wienerShift_norm]

/-- Discrete `ℓ¹(ℤ)` convolution `(u * v)_n = ∑' m : ℤ, u m * v (n - m)`. -/
def wienerConv (u v : ℓ¹(ℤ, ℂ)) : ℓ¹(ℤ, ℂ) :=
  ∑' m : ℤ, u m • wienerShift m v

theorem wienerConv_hasSum_apply (u v : ℓ¹(ℤ, ℂ)) (n : ℤ) :
    HasSum (fun m : ℤ => u m * v (n - m)) (wienerConv u v n) := by
  rw [wienerConv]
  have heval := (wienerConv_summable u v).hasSum.mapL (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 n)
  exact heval.congr_fun fun m => by
    simp [lp.evalCLM]

theorem wienerConv_norm_le (u v : ℓ¹(ℤ, ℂ)) :
    ‖wienerConv u v‖ ≤ ‖u‖ * ‖v‖ := by
  have hnorm_sum : Summable (fun m : ℤ => ‖u m • wienerShift m v‖) :=
    ((wienerSummable_norm u).mul_right ‖v‖).congr fun m => by
      rw [norm_smul, wienerShift_norm]
  calc
    ‖wienerConv u v‖
        ≤ ∑' m : ℤ, ‖u m • wienerShift m v‖ :=
      norm_tsum_le_tsum_norm hnorm_sum
    _ = ∑' m : ℤ, ‖u m‖ * ‖v‖ := by
      congr 1; ext m
      rw [norm_smul, wienerShift_norm]
    _ = ‖u‖ * ‖v‖ := ((wienerHasSum_norm u).mul_right ‖v‖).tsum_eq

theorem wienerSeriesCLM_conv (u v : ℓ¹(ℤ, ℂ)) :
    wienerSeriesCLM (wienerConv u v) = wienerSeriesCLM u * wienerSeriesCLM v := by
  have h1 := (wienerConv_summable u v).hasSum.mapL wienerSeriesCLM
  have h1' : HasSum (fun m : ℤ => (u m • (fourier m : C(FourierCircle, ℂ))) * wienerSeriesCLM v)
      (wienerSeriesCLM (wienerConv u v)) := by
    refine h1.congr_fun fun m => ?_
    rw [wienerSeriesCLM.map_smul, wienerSeriesCLM_shift, smul_mul_assoc]
  let mulR : AddMonoidHom C(FourierCircle, ℂ) C(FourierCircle, ℂ) :=
    { toFun := fun φ => φ * wienerSeriesCLM v
      map_zero' := zero_mul _
      map_add' := fun a b => add_mul a b _ }
  have h2 := (wienerHasSum_fourier u).map mulR (continuous_id.mul continuous_const)
  exact h1'.unique h2

/-- **18.21 (`WienerAlgebra`):** The Wiener algebra `A(T) ≅ ℓ¹(ℤ, ℂ)` of absolutely convergent
Fourier series, equipped with the `ℓ¹` norm `‖u‖ = ∑' n : ℤ, ‖u n‖` and convolution multiplication
`(u * v)_n = ∑' m : ℤ, u m * v (n - m)`. -/
@[ext]
structure WienerAlgebra where
  ofLp ::
  toLp : ℓ¹(ℤ, ℂ)

instance : Zero WienerAlgebra := ⟨⟨0⟩⟩
instance : One WienerAlgebra := ⟨⟨lp.single 1 0 1⟩⟩
instance : Add WienerAlgebra := ⟨fun u v => ⟨u.toLp + v.toLp⟩⟩
instance : Neg WienerAlgebra := ⟨fun u => ⟨-u.toLp⟩⟩
instance : Sub WienerAlgebra := ⟨fun u v => ⟨u.toLp - v.toLp⟩⟩
instance : Mul WienerAlgebra := ⟨fun u v => ⟨wienerConv u.toLp v.toLp⟩⟩
instance : SMul ℂ WienerAlgebra := ⟨fun c u => ⟨c • u.toLp⟩⟩

/-- Realization of an element of `WienerAlgebra` as its continuous sum function in
`C(FourierCircle, ℂ)`. -/
def wienerEval (u : WienerAlgebra) : C(FourierCircle, ℂ) :=
  wienerSeriesCLM u.toLp

private theorem wienerEval_injective : Function.Injective wienerEval :=
  fun _ _ h => WienerAlgebra.ext (wienerSeriesCLM_injective h)

@[simp]
private theorem wienerEval_zero : wienerEval 0 = 0 :=
  wienerSeriesCLM.map_zero

@[simp]
private theorem wienerEval_one : wienerEval 1 = 1 := by
  change wienerSeriesCLM (lp.single 1 0 1) = 1
  rw [wienerSeriesCLM_single, one_smul, fourier_zero_eq]

@[simp]
private theorem wienerEval_add (u v : WienerAlgebra) :
    wienerEval (u + v) = wienerEval u + wienerEval v :=
  wienerSeriesCLM.map_add u.toLp v.toLp

@[simp]
private theorem wienerEval_neg (u : WienerAlgebra) :
    wienerEval (-u) = -wienerEval u :=
  wienerSeriesCLM.map_neg u.toLp

@[simp]
private theorem wienerEval_sub (u v : WienerAlgebra) :
    wienerEval (u - v) = wienerEval u - wienerEval v :=
  wienerSeriesCLM.map_sub u.toLp v.toLp

@[simp]
private theorem wienerEval_mul (u v : WienerAlgebra) :
    wienerEval (u * v) = wienerEval u * wienerEval v :=
  wienerSeriesCLM_conv u.toLp v.toLp

@[simp]
private theorem wienerEval_smul (c : ℂ) (u : WienerAlgebra) :
    wienerEval (c • u) = c • wienerEval u :=
  wienerSeriesCLM.map_smul c u.toLp

instance instNormedCommRingWienerAlgebra : NormedCommRing WienerAlgebra :=
  { MetricSpace.induced WienerAlgebra.toLp (fun _ _ h => WienerAlgebra.ext h) inferInstance with
    norm := fun u => ‖u.toLp‖
    add := (· + ·)
    zero := 0
    neg := Neg.neg
    sub := Sub.sub
    nsmul := fun n u => ⟨n • u.toLp⟩
    zsmul := fun n u => ⟨n • u.toLp⟩
    mul := (· * ·)
    one := 1
    add_assoc := fun a b c => WienerAlgebra.ext (add_assoc a.toLp b.toLp c.toLp)
    zero_add := fun a => WienerAlgebra.ext (zero_add a.toLp)
    add_zero := fun a => WienerAlgebra.ext (add_zero a.toLp)
    nsmul_zero := fun a => WienerAlgebra.ext (zero_smul ℕ a.toLp)
    nsmul_succ := fun n a => WienerAlgebra.ext (succ_nsmul a.toLp n)
    sub_eq_add_neg := fun a b => WienerAlgebra.ext (sub_eq_add_neg a.toLp b.toLp)
    zsmul_zero' := fun a => WienerAlgebra.ext (zero_smul ℤ a.toLp)
    zsmul_succ' := fun n a => WienerAlgebra.ext (SubNegMonoid.zsmul_succ' n a.toLp)
    zsmul_neg' := fun n a => WienerAlgebra.ext (SubNegMonoid.zsmul_neg' n a.toLp)
    neg_add_cancel := fun a => WienerAlgebra.ext (neg_add_cancel a.toLp)
    add_comm := fun a b => WienerAlgebra.ext (add_comm a.toLp b.toLp)
    left_distrib := fun a b c => wienerEval_injective (by simp [mul_add])
    right_distrib := fun a b c => wienerEval_injective (by simp [add_mul])
    zero_mul := fun a => wienerEval_injective (by simp)
    mul_zero := fun a => wienerEval_injective (by simp)
    mul_assoc := fun a b c => wienerEval_injective (by simp [mul_assoc])
    one_mul := fun a => wienerEval_injective (by simp)
    mul_one := fun a => wienerEval_injective (by simp)
    mul_comm := fun a b => wienerEval_injective (by simp [mul_comm])
    dist_eq := fun a b => SeminormedAddCommGroup.dist_eq a.toLp b.toLp
    norm_mul_le := fun a b => wienerConv_norm_le a.toLp b.toLp }

instance instAlgebraWienerAlgebra : Algebra ℂ WienerAlgebra where
  algebraMap :=
    { toFun := fun c => ⟨lp.single (E := fun _ : ℤ => ℂ) 1 0 c⟩
      map_one' := rfl
      map_mul' := fun a b => wienerEval_injective (by
        change wienerSeriesCLM (lp.single (E := fun _ : ℤ => ℂ) 1 0 (a * b)) =
          wienerSeriesCLM (wienerConv (lp.single (E := fun _ : ℤ => ℂ) 1 0 a)
            (lp.single (E := fun _ : ℤ => ℂ) 1 0 b))
        rw [wienerSeriesCLM_conv, wienerSeriesCLM_single, wienerSeriesCLM_single,
          wienerSeriesCLM_single, fourier_zero_eq, smul_mul_smul_comm, one_mul])
      map_zero' := WienerAlgebra.ext (lp.single_zero (E := fun _ : ℤ => ℂ) 1 0)
      map_add' := fun a b => WienerAlgebra.ext (by
        change lp.single (E := fun _ : ℤ => ℂ) 1 0 (a + b) =
          lp.single (E := fun _ : ℤ => ℂ) 1 0 a + lp.single (E := fun _ : ℤ => ℂ) 1 0 b
        exact lp.single_add (E := fun _ : ℤ => ℂ) 1 0 a b) }
  commutes' _ _ := mul_comm _ _
  smul_def' c u := wienerEval_injective (by
    change wienerEval (c • u) = wienerEval (⟨lp.single (E := fun _ : ℤ => ℂ) 1 0 c⟩ * u)
    rw [wienerEval_smul, wienerEval_mul]
    change c • wienerEval u = wienerSeriesCLM (lp.single (E := fun _ : ℤ => ℂ) 1 0 c) * wienerEval u
    rw [wienerSeriesCLM_single, fourier_zero_eq, smul_mul_assoc, one_mul])

instance instNormedAlgebraWienerAlgebra : NormedAlgebra ℂ WienerAlgebra where
  norm_smul_le c u := by
    change ‖c • u.toLp‖ ≤ ‖c‖ * ‖u.toLp‖
    exact (norm_smul c u.toLp).le

instance instNormOneClassWienerAlgebra : NormOneClass WienerAlgebra where
  norm_one := by
    change ‖lp.single (E := fun _ : ℤ => ℂ) 1 0 (1 : ℂ)‖ = 1
    rw [lp.norm_single zero_lt_one, norm_one]

instance instCompleteSpaceWienerAlgebra : CompleteSpace WienerAlgebra :=
  Metric.complete_of_cauchySeq_tendsto fun u hu => by
    have hu' : CauchySeq (fun n => (u n).toLp) :=
      Metric.cauchySeq_iff.mpr fun ε hε => Metric.cauchySeq_iff.mp hu ε hε
    obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hu'
    exact ⟨⟨v⟩, Metric.tendsto_atTop.mpr fun ε hε => Metric.tendsto_atTop.mp hv ε hε⟩

/-- The `ℂ`-algebra homomorphism sending `u : WienerAlgebra` to its continuous Fourier sum in
`C(FourierCircle, ℂ)`. -/
def wienerEvalAlgHom : WienerAlgebra →ₐ[ℂ] C(FourierCircle, ℂ) where
  toFun := wienerEval
  map_one' := wienerEval_one
  map_mul' := wienerEval_mul
  map_zero' := wienerEval_zero
  map_add' := wienerEval_add
  commutes' c := by
    change wienerSeriesCLM (lp.single (E := fun _ : ℤ => ℂ) 1 0 c) =
      algebraMap ℂ C(FourierCircle, ℂ) c
    rw [wienerSeriesCLM_single, Algebra.algebraMap_eq_smul_one, fourier_zero_eq]

@[simp]
theorem wienerEvalAlgHom_apply (u : WienerAlgebra) :
    wienerEvalAlgHom u = wienerSeriesCLM u.toLp :=
  rfl

/-- Point-evaluation character `u ↦ (∑' n : ℤ, u n * e^{int})` on `WienerAlgebra`. -/
def wienerEvalHom (t : FourierCircle) : ComplexHom WienerAlgebra where
  toLinearMap :=
    { toFun := fun u => wienerEvalAlgHom u t
      map_add' := fun u v => by rw [map_add, ContinuousMap.add_apply]
      map_smul' := fun c u => by
        rw [wienerEvalAlgHom_apply, wienerEvalAlgHom_apply]
        change wienerSeriesCLM (c • u.toLp) t = _
        rw [wienerSeriesCLM.map_smul, ContinuousMap.smul_apply, RingHom.id_apply] }
  ne_zero := fun h0 => by
    have h1 : (wienerEvalAlgHom (1 : WienerAlgebra)) t =
        (0 : WienerAlgebra →ₗ[ℂ] ℂ) 1 :=
      congrArg (fun L : WienerAlgebra →ₗ[ℂ] ℂ => L 1) h0
    rw [map_one, ContinuousMap.one_apply, LinearMap.zero_apply] at h1
    exact one_ne_zero h1
  map_mul' u v := by
    change wienerEvalAlgHom (u * v) t = wienerEvalAlgHom u t * wienerEvalAlgHom v t
    rw [map_mul wienerEvalAlgHom u v, ContinuousMap.mul_apply]

@[simp]
theorem wienerEvalHom_apply (t : FourierCircle) (u : WienerAlgebra) :
    wienerEvalHom t u = wienerSeriesCLM u.toLp t :=
  rfl

/-- The `n`-th standard basis element `eₙ` of `WienerAlgebra`, corresponding to `fourier n`. -/
def wienerBasis (n : ℤ) : WienerAlgebra :=
  ⟨lp.single 1 n 1⟩

@[simp]
theorem wienerEvalAlgHom_basis (n : ℤ) :
    wienerEvalAlgHom (wienerBasis n) = fourier n := by
  change wienerSeriesCLM (lp.single 1 n 1) = fourier n
  rw [wienerSeriesCLM_single, one_smul]

theorem wienerBasis_norm (n : ℤ) : ‖wienerBasis n‖ = 1 := by
  change ‖lp.single (E := fun _ : ℤ => ℂ) 1 n (1 : ℂ)‖ = 1
  rw [lp.norm_single zero_lt_one, norm_one]

theorem wienerBasis_add (a b : ℤ) :
    wienerBasis (a + b) = wienerBasis a * wienerBasis b := by
  apply wienerEval_injective
  change wienerEvalAlgHom (wienerBasis (a + b)) = wienerEvalAlgHom (wienerBasis a * wienerBasis b)
  rw [map_mul, wienerEvalAlgHom_basis, wienerEvalAlgHom_basis, wienerEvalAlgHom_basis,
    fourier_mul_eq]

private theorem wienerBasis_natCast (k : ℕ) :
    wienerBasis (k : ℤ) = wienerBasis 1 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.cast_succ, add_comm, wienerBasis_add, ih, pow_succ']

private theorem wienerBasis_neg_natCast (k : ℕ) :
    wienerBasis (-(k : ℤ)) = wienerBasis (-1) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hstep : -(((k + 1 : ℕ) : ℤ)) = (-1 : ℤ) + -(k : ℤ) := by omega
    rw [hstep, wienerBasis_add, ih, pow_succ']

private theorem wienerBasis_hasSum (u : WienerAlgebra) :
    HasSum (fun n : ℤ => (u.toLp n) • wienerBasis n) u := by
  let ofLpHom : AddMonoidHom ℓ¹(ℤ, ℂ) WienerAlgebra :=
    { toFun := WienerAlgebra.ofLp
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hcont : Continuous ofLpHom := Isometry.continuous fun _ _ => rfl
  have hsingle := (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) u.toLp).map ofLpHom hcont
  have hterm : ∀ n : ℤ,
      (u.toLp n) • wienerBasis n =
        (ofLpHom ∘ fun i : ℤ => lp.single (E := fun _ : ℤ => ℂ) 1 i (u.toLp i)) n := by
    intro n
    apply WienerAlgebra.ext
    change (u.toLp n) • lp.single (E := fun _ : ℤ => ℂ) 1 n (1 : ℂ) =
      lp.single (E := fun _ : ℤ => ℂ) 1 n (u.toLp n)
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  exact hsingle.congr_fun hterm

/-- **18.21 (Character classification for `WienerAlgebra`):**
Every complex homomorphism `h : ComplexHom WienerAlgebra` is point evaluation at a unique point
`t₀ : FourierCircle`: `h u = ∑' n : ℤ, u.toLp n * trigMonomial n t₀`. -/
theorem wienerAlgebra_characters_eq_eval (h : ComplexHom WienerAlgebra) :
    ∃! t₀ : FourierCircle, ∀ u : WienerAlgebra, h u = wienerSeriesCLM u.toLp t₀ := by
  let w : ℂ := h (wienerBasis 1)
  let w' : ℂ := h (wienerBasis (-1))
  have hmul_one : wienerBasis 1 * wienerBasis (-1) = 1 := by
    rw [← wienerBasis_add]
    rfl
  have hww' : w * w' = 1 := by
    dsimp [w, w']
    rw [← h.map_mul, hmul_one, h.map_one]
  have hw_le : ‖w‖ ≤ 1 := by
    calc
      ‖w‖ ≤ ‖wienerBasis 1‖ := (theorem18_17_e h).2.1 (wienerBasis 1)
      _ = 1 := wienerBasis_norm 1
  have hw'_le : ‖w'‖ ≤ 1 := by
    calc
      ‖w'‖ ≤ ‖wienerBasis (-1)‖ := (theorem18_17_e h).2.1 (wienerBasis (-1))
      _ = 1 := wienerBasis_norm (-1)
  have hnorm_prod : ‖w‖ * ‖w'‖ = 1 := by
    rw [← norm_mul, hww', norm_one]
  have hw_norm : ‖w‖ = 1 := by
    nlinarith [norm_nonneg w, norm_nonneg w']
  have hw_sphere : w ∈ sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm]
    exact hw_norm
  let t₀ : FourierCircle := fourierCircleHomeomorphism.symm ⟨w, hw_sphere⟩
  have ht₀_one : fourier 1 t₀ = w := by
    change circleCoordinate t₀ = w
    rw [circleCoordinate_homeomorphism]
    exact congrArg (fun c : Circle => (c : ℂ))
      (fourierCircleHomeomorphism.apply_symm_apply ⟨w, hw_sphere⟩)
  have ht₀_neg_one : fourier (-1 : ℤ) t₀ = w' := by
    have hprod_t₀ : fourier 1 t₀ * fourier (-1 : ℤ) t₀ = 1 := by
      change (fourier 1 * fourier (-1 : ℤ) : C(FourierCircle, ℂ)) t₀ = 1
      rw [fourier_mul_eq]
      simp [fourier_zero_eq]
    rw [ht₀_one] at hprod_t₀
    have hw_ne : w ≠ 0 := left_ne_zero_of_mul_eq_one hww'
    exact mul_left_cancel₀ hw_ne (hprod_t₀.trans hww'.symm)
  have hbasis_eq : ∀ n : ℤ, h (wienerBasis n) = wienerEvalHom t₀ (wienerBasis n) := by
    intro n
    rcases le_or_gt 0 n with hn | hn
    · let k : ℕ := n.toNat
      have hn_eq : n = (k : ℤ) := by omega
      rw [hn_eq, wienerBasis_natCast, h.map_pow, (wienerEvalHom t₀).map_pow]
      congr 1
      rw [wienerEvalHom_apply, ← wienerEvalAlgHom_apply, wienerEvalAlgHom_basis, ht₀_one]
    · let k : ℕ := (-n).toNat
      have hn_eq : n = -(k : ℤ) := by omega
      rw [hn_eq, wienerBasis_neg_natCast, h.map_pow, (wienerEvalHom t₀).map_pow]
      congr 1
      rw [wienerEvalHom_apply, ← wienerEvalAlgHom_apply, wienerEvalAlgHom_basis, ht₀_neg_one]
  refine ⟨t₀, ?_, ?_⟩
  · intro u
    have hsum1 := (wienerBasis_hasSum u).mapL h.toCLM
    have hsum2 := (wienerBasis_hasSum u).mapL (wienerEvalHom t₀).toCLM
    have hterm1 : ∀ n : ℤ,
        u.toLp n * wienerEvalHom t₀ (wienerBasis n) =
          h.toCLM ((u.toLp n) • wienerBasis n) := by
      intro n
      rw [ComplexHom.toCLM_apply, h.map_smul, hbasis_eq n]
    have hterm2 : ∀ n : ℤ,
        u.toLp n * wienerEvalHom t₀ (wienerBasis n) =
          (wienerEvalHom t₀).toCLM ((u.toLp n) • wienerBasis n) := by
      intro n
      rw [ComplexHom.toCLM_apply, (wienerEvalHom t₀).map_smul]
    exact (hsum1.congr_fun hterm1).unique (hsum2.congr_fun hterm2)
  · intro t₁ ht₁
    have h1 := ht₁ (wienerBasis 1)
    change w = wienerEvalAlgHom (wienerBasis 1) t₁ at h1
    rw [wienerEvalAlgHom_basis] at h1
    have hcoord : circleCoordinate t₁ = circleCoordinate t₀ := by
      change fourier 1 t₁ = fourier 1 t₀
      rw [← h1, ht₀_one]
    rw [circleCoordinate_homeomorphism, circleCoordinate_homeomorphism] at hcoord
    exact fourierCircleHomeomorphism.injective (Subtype.ext hcoord)

/-- **18.21 (Wiener's Reciprocal Theorem on `FourierCircle`):**
Suppose `c : ℤ → ℂ` satisfies `∑' n : ℤ, ‖c n‖ < ∞` (`Summable (fun n => ‖c n‖)`), and suppose
`f(t) = ∑' n : ℤ, c n * trigMonomial n t ≠ 0` for every `t : FourierCircle`. Then there exists a
unique sequence `γ : ℤ → ℂ` with `Summable (fun n => ‖γ n‖)` whose Fourier series converges
uniformly and pointwise to `(f(t))⁻¹`:
1. `Summable (fun n : ℤ => ‖γ n‖)`;
2. `∀ t : FourierCircle, HasSum (fun n : ℤ => γ n * trigMonomial n t) ((∑' n : ℤ, c n * trigMonomial n t)⁻¹)`
   and `(∑' n : ℤ, γ n * trigMonomial n t) = (∑' n : ℤ, c n * trigMonomial n t)⁻¹`;
3. `∀ k : ℤ, HasSum (fun m : ℤ => c m * γ (k - m)) (if k = 0 then 1 else 0)`;
4. `∀ n : ℤ, γ n = fourierCoeff (fun t : FourierCircle => (∑' k : ℤ, c k * trigMonomial k t)⁻¹) n`. -/
theorem theorem18_21 (c : ℤ → ℂ) (hc : Summable (fun n : ℤ => ‖c n‖))
    (hf_ne : ∀ t : FourierCircle, (∑' n : ℤ, c n * trigMonomial n t) ≠ 0) :
    ∃! γ : ℤ → ℂ,
      Summable (fun n : ℤ => ‖γ n‖) ∧
      (∀ t : FourierCircle,
        HasSum (fun n : ℤ => γ n * trigMonomial n t)
          ((∑' n : ℤ, c n * trigMonomial n t)⁻¹)) ∧
      (∀ t : FourierCircle,
        (∑' n : ℤ, γ n * trigMonomial n t) = (∑' n : ℤ, c n * trigMonomial n t)⁻¹) ∧
      (∀ k : ℤ, HasSum (fun m : ℤ => c m * γ (k - m)) (if k = 0 then 1 else 0)) ∧
      (∀ n : ℤ,
        γ n = fourierCoeff (fun t : FourierCircle => (∑' k : ℤ, c k * trigMonomial k t)⁻¹) n) := by
  let u : WienerAlgebra := ⟨⟨c, memℓp_gen (by simpa using hc)⟩⟩
  have hu_eval : ∀ t : FourierCircle,
      wienerSeriesCLM u.toLp t = ∑' n : ℤ, c n * trigMonomial n t :=
    fun t => wienerSeriesCLM_apply_eval u.toLp t
  have hu_unit : IsUnit u := by
    rw [(theorem18_17_b u).1]
    intro h
    obtain ⟨t₀, ht₀, -⟩ := wienerAlgebra_characters_eq_eval h
    rw [ht₀ u, hu_eval t₀]
    exact hf_ne t₀
  let v : WienerAlgebra := u⁻¹ʳ
  have huv : u * v = 1 := Ring.mul_inverse_cancel u hu_unit
  let γ : ℤ → ℂ := fun n => v.toLp n
  have hγ_sum : Summable (fun n : ℤ => ‖γ n‖) := wienerSummable_norm v.toLp
  have hprod_eval : ∀ t : FourierCircle,
      wienerSeriesCLM v.toLp t = (∑' n : ℤ, c n * trigMonomial n t)⁻¹ := by
    intro t
    have hm : wienerEvalAlgHom u t * wienerEvalAlgHom v t = 1 := by
      rw [← ContinuousMap.mul_apply, ← map_mul, huv, map_one, ContinuousMap.one_apply]
    rw [wienerEvalAlgHom_apply, wienerEvalAlgHom_apply, hu_eval t] at hm
    exact eq_inv_of_mul_eq_one_right hm
  have hγ_hasSum : ∀ t : FourierCircle,
      HasSum (fun n : ℤ => γ n * trigMonomial n t) ((∑' n : ℤ, c n * trigMonomial n t)⁻¹) := by
    intro t
    rw [← hprod_eval t]
    exact wienerHasSum_eval v.toLp t
  have hγ_tsum : ∀ t : FourierCircle,
      (∑' n : ℤ, γ n * trigMonomial n t) = (∑' n : ℤ, c n * trigMonomial n t)⁻¹ :=
    fun t => (hγ_hasSum t).tsum_eq
  have hγ_conv : ∀ k : ℤ, HasSum (fun m : ℤ => c m * γ (k - m)) (if k = 0 then 1 else 0) := by
    intro k
    have hc_eq : wienerConv u.toLp v.toLp = (1 : WienerAlgebra).toLp :=
      congrArg WienerAlgebra.toLp huv
    have hsum_k := wienerConv_hasSum_apply u.toLp v.toLp k
    rw [hc_eq] at hsum_k
    have hone_k : ((1 : WienerAlgebra).toLp k) = if k = 0 then 1 else 0 := by
      change lp.single (E := fun _ : ℤ => ℂ) 1 0 (1 : ℂ) k = _
      by_cases hk : k = 0
      · subst hk; simp
      · rw [lp.single_apply_ne 1 0 1 hk]; simp [hk]
    rwa [hone_k] at hsum_k
  have hγ_coeff : ∀ n : ℤ,
      γ n = fourierCoeff (fun t : FourierCircle => (∑' k : ℤ, c k * trigMonomial k t)⁻¹) n := by
    intro n
    have hfn_eq : (fun t : FourierCircle => (∑' k : ℤ, c k * trigMonomial k t)⁻¹) =
        ⇑(wienerSeriesCLM v.toLp) := by
      ext t
      exact (hprod_eval t).symm
    rw [hfn_eq, fourierCoeff_wienerSeriesCLM v.toLp n]
  refine ⟨γ, ⟨hγ_sum, hγ_hasSum, hγ_tsum, hγ_conv, hγ_coeff⟩, ?_⟩
  intro γ' hγ'
  ext n
  rw [hγ'.2.2.2.2 n, hγ_coeff n]

/-- **18.21 (Wiener's Reciprocal Theorem, verbatim real-line formulation):**
Suppose `f(e^{it}) = ∑' n : ℤ, c n * exp(i n t)` with `∑' n : ℤ, ‖c n‖ < ∞`, and suppose
`f(e^{it}) ≠ 0` for every `t : ℝ`. Then there exists a unique sequence `γ : ℤ → ℂ` with
`∑' n : ℤ, ‖γ n‖ < ∞` such that `(f(e^{it}))⁻¹ = ∑' n : ℤ, γ n * exp(i n t)` (with unconditional
pointwise `HasSum` convergence) for every `t : ℝ`. -/
theorem theorem18_21_real (c : ℤ → ℂ) (hc : Summable (fun n : ℤ => ‖c n‖))
    (hf_ne : ∀ t : ℝ, (∑' n : ℤ, c n * Complex.exp (n * t * Complex.I)) ≠ 0) :
    ∃! γ : ℤ → ℂ,
      Summable (fun n : ℤ => ‖γ n‖) ∧
      (∀ t : ℝ,
        HasSum (fun n : ℤ => γ n * Complex.exp (n * t * Complex.I))
          ((∑' n : ℤ, c n * Complex.exp (n * t * Complex.I))⁻¹)) ∧
      (∀ t : ℝ,
        (∑' n : ℤ, γ n * Complex.exp (n * t * Complex.I)) =
          (∑' n : ℤ, c n * Complex.exp (n * t * Complex.I))⁻¹) := by
  have hf_circle : ∀ x : FourierCircle, (∑' n : ℤ, c n * trigMonomial n x) ≠ 0 := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H t =>
      simp_rw [trigMonomial_apply_real]
      exact hf_ne t
  obtain ⟨γ, ⟨hγ_sum, hγ_hasSum, hγ_tsum, _, _⟩, _⟩ := theorem18_21 c hc hf_circle
  refine ⟨γ, ⟨hγ_sum, ?_, ?_⟩, ?_⟩
  · intro t
    simpa only [trigMonomial_apply_real] using hγ_hasSum (t : FourierCircle)
  · intro t
    simpa only [trigMonomial_apply_real] using hγ_tsum (t : FourierCircle)
  · rintro γ' ⟨hγ'_sum, -, hγ'_tsum⟩
    let v : ℓ¹(ℤ, ℂ) := ⟨γ, memℓp_gen (by simpa using hγ_sum)⟩
    let v' : ℓ¹(ℤ, ℂ) := ⟨γ', memℓp_gen (by simpa using hγ'_sum)⟩
    have hv_eq : wienerSeriesCLM v' = wienerSeriesCLM v := by
      ext x
      induction x using QuotientAddGroup.induction_on with
      | H t =>
        rw [wienerSeriesCLM_apply_eval, wienerSeriesCLM_apply_eval]
        change (∑' n : ℤ, γ' n * trigMonomial n (t : FourierCircle)) =
          ∑' n : ℤ, γ n * trigMonomial n (t : FourierCircle)
        simp_rw [trigMonomial_apply_real]
        rw [hγ'_tsum t]
        simpa only [trigMonomial_apply_real] using (hγ_tsum (t : FourierCircle)).symm
    have hlp_eq : v' = v := wienerSeriesCLM_injective hv_eq
    ext n
    exact congrArg (fun u : ℓ¹(ℤ, ℂ) => u n) hlp_eq

end WienerTheorem

end RudinRCA.Chapter18

#print axioms RudinRCA.Chapter18.theorem18_1
#print axioms RudinRCA.Chapter18.theorem18_2
#print axioms RudinRCA.Chapter18.theorem18_3
#print axioms RudinRCA.Chapter18.theorem18_3_one_sub
#print axioms RudinRCA.Chapter18.theorem18_4_le
#print axioms RudinRCA.Chapter18.theorem18_4
#print axioms RudinRCA.Chapter18.theorem18_4_inv_norm
#print axioms RudinRCA.Chapter18.corollary18_4_1
#print axioms RudinRCA.Chapter18.corollary18_4_2
#print axioms RudinRCA.Chapter18.corollary18_4_3
#print axioms RudinRCA.Chapter18.theorem18_5
#print axioms RudinRCA.Chapter18.theorem18_6
#print axioms RudinRCA.Chapter18.theorem18_7
#print axioms RudinRCA.Chapter18.theorem18_8
#print axioms RudinRCA.Chapter18.theorem18_9
#print axioms RudinRCA.Chapter18.theorem18_10
#print axioms RudinRCA.Chapter18.theorem18_11
#print axioms RudinRCA.Chapter18.theorem18_12
#print axioms RudinRCA.Chapter18.theorem18_13
#print axioms RudinRCA.Chapter18.theorem18_14
#print axioms RudinRCA.Chapter18.theorem18_15
#print axioms RudinRCA.Chapter18.theorem18_16
#print axioms RudinRCA.Chapter18.theorem18_17_a
#print axioms RudinRCA.Chapter18.theorem18_17_b
#print axioms RudinRCA.Chapter18.theorem18_17_c
#print axioms RudinRCA.Chapter18.theorem18_17_d
#print axioms RudinRCA.Chapter18.theorem18_17_e
#print axioms RudinRCA.Chapter18.theorem18_17
#print axioms RudinRCA.Chapter18.discAlgebra_characters_eq_eval
#print axioms RudinRCA.Chapter18.theorem18_18
#print axioms RudinRCA.Chapter18.discAlgebraCircle_iff_fourierCoeff_neg_eq_zero
#print axioms RudinRCA.Chapter18.theorem18_19
#print axioms RudinRCA.Chapter18.theorem18_20
#print axioms RudinRCA.Chapter18.wienerAlgebra_characters_eq_eval
#print axioms RudinRCA.Chapter18.theorem18_21
#print axioms RudinRCA.Chapter18.theorem18_21_real
