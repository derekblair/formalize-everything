import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.Omega
import Mathlib.Tactic.Positivity


/-!
Rudin, Real and Complex Analysis, third edition, Chapter 18 (pp. 356–369).
The printed chapter is Elementary Theory of Banach Algebras; the cluster ticket's
chapter title is inaccurate. This development follows the printed numbering.

The unital complex Banach algebras in the text are represented by `NormedRing`,
`NormedAlgebra ℂ`, `CompleteSpace`, and `NormOneClass`. Multiplication need not
commute. `Ring.inverse` agrees with the inverse on invertible elements.

Printed 18.2 is an expository discussion connecting algebra, topology, and
holomorphy. It has no separate proposition; its mathematical connections are
represented by the resolvent and spectral theorems 18.5–18.9 below.
-/

noncomputable section

open Filter Set Topology
open scoped Ring ENNReal NNReal

namespace RudinRCA.Chapter18

section Definitions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- 18.1: invertibility means existence of a two-sided inverse. -/
theorem isUnit_iff_two_sided_inverse (x : A) :
    IsUnit x ↔ ∃ y : A, x * y = 1 ∧ y * x = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨↑u⁻¹, u.val_inv, u.inv_val⟩
  · rintro ⟨y, hxy, hyx⟩
    exact ⟨⟨x, y, hxy, hyx⟩, rfl⟩

/-- 18.1: a left inverse and a right inverse coincide. -/
theorem inverse_unique {x y z : A} (hy : y * x = 1) (hz : x * z = 1) : y = z := by
  calc
    y = y * (x * z) := by rw [hz, mul_one]
    _ = (y * x) * z := (mul_assoc _ _ _).symm
    _ = z := by rw [hy, one_mul]

/-- 18.1: a two-sided multiplicative identity is unique. -/
theorem unit_unique {e : A} (he : ∀ x : A, e * x = x) : e = 1 := by
  simpa using he 1

/-- 18.1: inversion reverses the order of multiplication. -/
theorem units_mul_inverse (x y : Aˣ) :
    ((x * y)⁻¹ : Aˣ) = y⁻¹ * x⁻¹ := mul_inv_rev x y

/-- 18.1: multiplication is continuous jointly, hence preserves convergent pairs. -/
theorem multiplication_continuous : Continuous (fun p : A × A => p.1 * p.2) :=
  continuous_fst.mul continuous_snd

theorem multiplication_tendsto {x y : ℕ → A} {a b : A}
    (hx : Tendsto x atTop (𝓝 a)) (hy : Tendsto y atTop (𝓝 b)) :
    Tendsto (fun n => x n * y n) atTop (𝓝 (a * b)) := hx.mul hy

/-- 18.1: the book's sign convention for the spectrum. -/
def bookSpectrum (x : A) : Set ℂ := {z | ¬ IsUnit (x - z • (1 : A))}

/-- The two signs used in definitions of spectrum give the same set. -/
theorem bookSpectrum_eq_spectrum (x : A) : bookSpectrum x = spectrum ℂ x := by
  ext z
  simp only [bookSpectrum, mem_ofPred_eq, spectrum.mem_iff,
    Algebra.algebraMap_eq_smul_one]
  constructor
  · intro hn hu
    exact hn (by simpa only [neg_sub] using hu.neg)
  · intro hn hu
    exact hn (by simpa only [neg_sub] using hu.neg)

end Definitions

section BanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
  [CompleteSpace A] [NormOneClass A]

/-- 18.3: the Neumann series, including norm convergence and invertibility. -/
theorem neumann_series {x : A} (hx : ‖x‖ < 1) :
    IsUnit (1 + x) ∧ HasSum (fun n : ℕ => (-x) ^ n) (1 + x)⁻¹ʳ := by
  have hn : ‖-x‖ < 1 := by simpa using hx
  constructor
  · simpa using isUnit_one_sub_of_norm_lt_one hn
  · simpa using hasSum_geom_series_inverse (-x) hn

/-- 18.3(1), also written with the book's explicit alternating coefficients. -/
theorem neumann_series_alternating {x : A} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => (-1 : A) ^ n * x ^ n) (1 + x)⁻¹ʳ := by
  convert (neumann_series hx).2 using 1
  funext n
  exact (neg_pow x n).symm

/-- The norm bound needed for the quantitative part of 18.3. -/
theorem inverse_one_add_norm_le {x : A} (hx : ‖x‖ < 1) :
    ‖(1 + x)⁻¹ʳ‖ ≤ (1 - ‖x‖)⁻¹ := by
  rw [← (neumann_series hx).2.tsum_eq]
  simpa using tsum_geometric_le_of_norm_lt_one (-x) (by simpa using hx)

/-- 18.3(2): the complete quadratic remainder estimate. -/
theorem neumann_series_remainder {x : A} (hx : ‖x‖ < 1) :
    ‖(1 + x)⁻¹ʳ - 1 + x‖ ≤ ‖x‖ ^ 2 / (1 - ‖x‖) := by
  have he := NormedRing.inverse_one_sub_nth_order' 2 (t := -x) (by simpa using hx)
  have he' : (1 + x)⁻¹ʳ - 1 + x = x ^ 2 * (1 + x)⁻¹ʳ := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one, sub_neg_eq_add, neg_sq] at he
    conv_lhs => rw [he]
    abel
  rw [he', div_eq_mul_inv]
  exact (norm_mul_le _ _).trans
    (mul_le_mul (norm_pow_le x 2) (inverse_one_add_norm_le hx) (norm_nonneg _)
      (sq_nonneg ‖x‖))

/-- 18.4, the invertibility assertion. -/
theorem perturbation_isUnit (x : Aˣ) {h : A}
    (hh : ‖h‖ < ‖(↑x⁻¹ : A)‖⁻¹) : IsUnit ((x : A) + h) :=
  (x.add h hh).isUnit

/-- 18.4(1): the printed quantitative estimate, with its parameters retained. -/
theorem perturbation_remainder (x : Aˣ) (h : A) {α β : ℝ}
    (hα : ‖(↑x⁻¹ : A)‖ = 1 / α) (hβ : ‖h‖ = β) (hβα : β < α) :
    IsUnit ((x : A) + h) ∧
      ‖((x : A) + h)⁻¹ʳ - (↑x⁻¹ : A) + (↑x⁻¹ : A) * h * (↑x⁻¹ : A)‖ ≤
        β ^ 2 / (α ^ 2 * (α - β)) := by
  have hβ0 : 0 ≤ β := hβ ▸ norm_nonneg h
  have hα0 : 0 < α := lt_of_le_of_lt hβ0 hβα
  have hratio0 : 0 ≤ β / α := div_nonneg hβ0 hα0.le
  have hratio1 : β / α < 1 := (div_lt_one hα0).2 hβα
  let t : A := (↑x⁻¹ : A) * h
  have ht_bound : ‖t‖ ≤ β / α := by
    calc
      ‖t‖ ≤ ‖(↑x⁻¹ : A)‖ * ‖h‖ := norm_mul_le _ _
      _ = β / α := by rw [hα, hβ]; ring
  have ht : ‖t‖ < 1 := ht_bound.trans_lt hratio1
  have hfactor : (x : A) + h = (x : A) * (1 + t) := by
    simp [t, mul_add, ← mul_assoc]
  have hi : ((x : A) + h)⁻¹ʳ = (1 + t)⁻¹ʳ * (↑x⁻¹ : A) := by
    rw [hfactor, Ring.inverse_mul (Or.inl x.isUnit), Ring.inverse_unit]
  refine ⟨?_, ?_⟩
  · rw [hfactor]
    exact x.isUnit.mul (neumann_series ht).1
  have he : ((x : A) + h)⁻¹ʳ - (↑x⁻¹ : A) + (↑x⁻¹ : A) * h * (↑x⁻¹ : A) =
      ((1 + t)⁻¹ʳ - 1 + t) * (↑x⁻¹ : A) := by
    rw [hi]
    simp [t, sub_mul, add_mul]
  have hmono : ‖t‖ ^ 2 / (1 - ‖t‖) ≤ (β / α) ^ 2 / (1 - β / α) := by
    gcongr
  rw [he]
  calc
    ‖((1 + t)⁻¹ʳ - 1 + t) * (↑x⁻¹ : A)‖ ≤
        ‖(1 + t)⁻¹ʳ - 1 + t‖ * ‖(↑x⁻¹ : A)‖ := norm_mul_le _ _
    _ ≤ ((β / α) ^ 2 / (1 - β / α)) * (1 / α) :=
      mul_le_mul ((neumann_series_remainder ht).trans hmono) hα.le
        (norm_nonneg _) (by positivity)
    _ = β ^ 2 / (α ^ 2 * (α - β)) := by
      field_simp

/-- 18.4 Corollary 1: invertible elements form an open set. -/
theorem units_isOpen : IsOpen {x : A | IsUnit x} := Units.isOpen

/-- 18.4 Corollary 1: inversion on the group of units is a homeomorphism.
`Units.isOpenEmbedding_val` identifies its topology with the subspace topology. -/
def inversionHomeomorph : Aˣ ≃ₜ Aˣ := Homeomorph.inv Aˣ

theorem units_subspace_topology : IsOpenEmbedding (Units.val : Aˣ → A) :=
  Units.isOpenEmbedding_val

/-- 18.4 Corollary 2: the full noncommutative differential of inversion. -/
theorem inversion_hasFDerivAt (x : Aˣ) :
    HasFDerivAt (Ring.inverse : A → A)
      (-ContinuousLinearMap.mulLeftRight ℂ A (↑x⁻¹) (↑x⁻¹)) (x : A) :=
  hasFDerivAt_ringInverse x

/-- 18.4 Corollary 3, with the printed spectrum convention. -/
theorem spectrum_compact_and_bound (x : A) :
    IsCompact (bookSpectrum x) ∧ ∀ z ∈ bookSpectrum x, ‖z‖ ≤ ‖x‖ := by
  rw [bookSpectrum_eq_spectrum]
  exact ⟨spectrum.isCompact x, fun _ hz => spectrum.norm_le_norm_of_mem hz⟩

/-- Negation commutes with the total ring inverse. -/
theorem ringInverse_neg (x : A) : (-x)⁻¹ʳ = -x⁻¹ʳ := by
  by_cases hx : IsUnit x
  · apply inverse_unique (x := -x)
    · exact Ring.inverse_mul_cancel _ hx.neg
    · simpa using Ring.mul_inverse_cancel x hx
  · have hn : ¬ IsUnit (-x) := by simpa using hx
    simp [Ring.inverse_non_unit _ hx, Ring.inverse_non_unit _ hn]

/-- The book's resolvent has the opposite sign to Mathlib's resolvent. -/
theorem book_resolvent_eq (x : A) (z : ℂ) :
    (x - z • (1 : A))⁻¹ʳ = -resolvent x z := by
  rw [resolvent, Algebra.algebraMap_eq_smul_one, ← ringInverse_neg, neg_sub]

/-- 18.5: scalarized resolvents are holomorphic off the spectrum and decay
at infinity. Both clauses use the book's `x - z e` sign convention. -/
theorem scalarized_resolvent (Φ : A →L[ℂ] ℂ) (x : A) :
    DifferentiableOn ℂ (fun z : ℂ => Φ ((x - z • (1 : A))⁻¹ʳ))
      (bookSpectrum x)ᶜ ∧
    Tendsto (fun z : ℂ => Φ ((x - z • (1 : A))⁻¹ʳ))
      (Bornology.cobounded ℂ) (𝓝 0) := by
  constructor
  · intro z hz
    have hz' : z ∈ resolventSet ℂ x := by
      simpa [bookSpectrum_eq_spectrum, spectrum] using hz
    have hd := (spectrum.hasDerivAt_resolvent_const_left hz').neg.differentiableAt
    simpa only [book_resolvent_eq] using
      (Φ.differentiableAt.comp z hd).differentiableWithinAt
  · have ht := Φ.continuous.continuousAt.tendsto.comp
      (spectrum.resolvent_tendsto_cobounded (𝕜 := ℂ) x).neg
    simpa [Function.comp_def, book_resolvent_eq] using ht

/-- 18.6: no commutativity hypothesis is required. -/
theorem spectrum_nonempty_compact [Nontrivial A] (x : A) :
    (bookSpectrum x).Nonempty ∧ IsCompact (bookSpectrum x) := by
  rw [bookSpectrum_eq_spectrum]
  exact ⟨spectrum.nonempty x, spectrum.isCompact x⟩

/-- 18.7: the Gelfand–Mazur algebra isomorphism. The norm remains merely
submultiplicative; a multiplicative-norm division ring is not assumed. -/
def gelfandMazur (h : ∀ x : A, x ≠ 0 → IsUnit x) [Nontrivial A] : ℂ ≃ₐ[ℂ] A :=
  NormedRing.algEquivComplexOfComplete
    (fun {x} => ⟨fun hx => hx.ne_zero, h x⟩)

/-- 18.7 also asserts that this isomorphism is isometric. -/
theorem gelfandMazur_isometry (h : ∀ x : A, x ≠ 0 → IsUnit x) [Nontrivial A] :
    Isometry (gelfandMazur h : ℂ → A) := by
  change Isometry (algebraMap ℂ A)
  exact algebraMap_isometry ℂ A

/-- 18.8: the real-valued spectral radius in the printed convention. -/
def bookSpectralRadius (x : A) : ℝ := sSup (norm '' bookSpectrum x)

/-- 18.8: identification of the printed real supremum with Mathlib's
extended nonnegative spectral radius. -/
theorem bookSpectralRadius_eq [Nontrivial A] (x : A) :
    bookSpectralRadius x = (spectralRadius ℂ x).toReal := by
  obtain ⟨z, hz, he⟩ := spectrum.exists_nnnorm_eq_spectralRadius x
  have hg : IsGreatest (norm '' spectrum ℂ x) ‖z‖ := by
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro r ⟨w, hw, rfl⟩
    have hw' : (‖w‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ x := by
      rw [spectralRadius_eq_of_unital]
      exact le_iSup₂ w hw
    rw [← he] at hw'
    exact_mod_cast hw'
  rw [bookSpectralRadius, bookSpectrum_eq_spectrum, hg.csSup_eq, ← he]
  simp

/-- 18.9: Gelfand's formula in the printed real-valued form. -/
theorem spectral_radius_formula [Nontrivial A] (x : A) :
    Tendsto (fun n : ℕ => ‖x ^ n‖ ^ (1 / (n : ℝ))) atTop
      (𝓝 (bookSpectralRadius x)) := by
  have hf : spectralRadius ℂ x ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm x)
  have ht := (ENNReal.tendsto_toReal hf).comp
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius x)
  simpa only [Function.comp_def, ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _),
    ← bookSpectralRadius_eq] using ht

/-- 18.10(b): passing to an ambient algebra can only shrink the spectrum. -/
theorem ambient_spectrum_subset {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]
    (φ : A →ₐ[ℂ] B) (x : A) : bookSpectrum (φ x) ⊆ bookSpectrum x := by
  simp only [bookSpectrum_eq_spectrum]
  exact AlgHom.spectrum_apply_subset φ x

/-- 18.10(a): an algebra isomorphism preserves the spectrum without a
continuity or isometry assumption on the isomorphism. -/
theorem algebraic_spectrum_invariant {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]
    (φ : A ≃ₐ[ℂ] B) (x : A) : bookSpectrum (φ x) = bookSpectrum x := by
  simp only [bookSpectrum_eq_spectrum]
  exact AlgEquiv.spectrum_eq φ x

/-- 18.10(b): for the inherited norm, the spectral radius is unchanged. -/
theorem ambient_spectralRadius_eq [Nontrivial A] {B : Type*} [NormedRing B]
    [NormedAlgebra ℂ B] [CompleteSpace B] [NormOneClass B] [Nontrivial B]
    (φ : A →ₐ[ℂ] B) (hφ : Isometry φ) (x : A) :
    bookSpectralRadius (φ x) = bookSpectralRadius x := by
  have hnorm (n : ℕ) : ‖(φ x) ^ n‖ = ‖x ^ n‖ := by
    rw [← map_pow]
    exact hφ.norm_map_of_map_zero (map_zero φ) _
  have hb := spectral_radius_formula (φ x)
  simp only [hnorm] at hb
  exact tendsto_nhds_unique hb (spectral_radius_formula x)

end BanachAlgebra

end RudinRCA.Chapter18

#print axioms RudinRCA.Chapter18.isUnit_iff_two_sided_inverse
#print axioms RudinRCA.Chapter18.inverse_unique
#print axioms RudinRCA.Chapter18.unit_unique
#print axioms RudinRCA.Chapter18.units_mul_inverse
#print axioms RudinRCA.Chapter18.multiplication_continuous
#print axioms RudinRCA.Chapter18.multiplication_tendsto
#print axioms RudinRCA.Chapter18.bookSpectrum_eq_spectrum
#print axioms RudinRCA.Chapter18.neumann_series
#print axioms RudinRCA.Chapter18.neumann_series_alternating
#print axioms RudinRCA.Chapter18.inverse_one_add_norm_le
#print axioms RudinRCA.Chapter18.neumann_series_remainder
#print axioms RudinRCA.Chapter18.perturbation_isUnit
#print axioms RudinRCA.Chapter18.perturbation_remainder
#print axioms RudinRCA.Chapter18.units_isOpen
#print axioms RudinRCA.Chapter18.inversionHomeomorph
#print axioms RudinRCA.Chapter18.units_subspace_topology
#print axioms RudinRCA.Chapter18.inversion_hasFDerivAt
#print axioms RudinRCA.Chapter18.spectrum_compact_and_bound
#print axioms RudinRCA.Chapter18.ringInverse_neg
#print axioms RudinRCA.Chapter18.book_resolvent_eq
#print axioms RudinRCA.Chapter18.scalarized_resolvent
#print axioms RudinRCA.Chapter18.spectrum_nonempty_compact
#print axioms RudinRCA.Chapter18.gelfandMazur
#print axioms RudinRCA.Chapter18.gelfandMazur_isometry
#print axioms RudinRCA.Chapter18.bookSpectralRadius_eq
#print axioms RudinRCA.Chapter18.spectral_radius_formula
#print axioms RudinRCA.Chapter18.ambient_spectrum_subset
#print axioms RudinRCA.Chapter18.algebraic_spectrum_invariant
#print axioms RudinRCA.Chapter18.ambient_spectralRadius_eq


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
  · simp [Pi.single_apply, h, h.symm]

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
      simp only [sub_self]
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
      fourier_neg, map_mul, conj_conj]
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
    simp only [dirichlet, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply, hproj]
    have hp (i : ℕ) : (i : ℤ) + 1 ≠ 0 := by omega
    simp [hp]
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
    simp [dirichlet, projection_fourier, hp]
  have hp (n N : ℕ) (h : n < N) :
      dirichlet (T := T) N (fourier ((n : ℤ)+1)) = fourier ((n : ℤ)+1) := by
    have h0 : (0 : ℤ) ≠ (n : ℤ)+1 := by omega
    have hn (i : ℕ) : -((i : ℤ)+1) ≠ (n : ℤ)+1 := by omega
    have he (i : ℕ) : ((i : ℤ)+1 = (n : ℤ)+1) ↔ i = n := by omega
    simp [dirichlet, projection_fourier, h0, hn, he, h]
  have hn (n N : ℕ) (h : n < N) :
      dirichlet (T := T) N (fourier (-((n : ℤ)+1))) = fourier (-((n : ℤ)+1)) := by
    have h0 : (0 : ℤ) ≠ -((n : ℤ)+1) := by omega
    have hp (i : ℕ) : (i : ℤ)+1 ≠ -((n : ℤ)+1) := by omega
    have he (i : ℕ) : (-((i : ℤ)+1) = -((n : ℤ)+1)) ↔ i = n := by omega
    simp [dirichlet, projection_fourier, h0, hp, he, h]
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · cases n with
    | zero => simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
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
  zero_mem' := by simpa only [map_zero] using (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (0 : C(AddCircle T, ℂ))) atTop (𝓝 0))
  add_mem' := by
    intro f g hf hg
    simpa only [map_add] using hf.add hg
  smul_mem' := by
    intro c f hf
    simpa only [map_smul] using hf.const_smul c

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
    simp [Pi.single_apply, hn, hn.symm]
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
      exact Submodule.subset_span ⟨m.toNat, by rw [Int.toNat_of_nonneg hm0]⟩
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
