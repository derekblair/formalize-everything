import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

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

set_option backward.isDefEq.respectTransparency.types false in
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
    have hd : DifferentiableAt ℂ (fun w : ℂ => -resolvent x w) z :=
      (spectrum.hasDerivAt_resolvent_const_left hz').neg.differentiableAt
    have hc : DifferentiableAt ℂ (fun w : ℂ => Φ (-resolvent x w)) z :=
      Φ.differentiableAt.comp z hd
    simpa only [book_resolvent_eq] using hc.differentiableWithinAt
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
      exact le_iSup₂ (f := fun z : ℂ => fun _ : z ∈ spectrum ℂ x =>
        (‖z‖₊ : ℝ≥0∞)) w hw
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
