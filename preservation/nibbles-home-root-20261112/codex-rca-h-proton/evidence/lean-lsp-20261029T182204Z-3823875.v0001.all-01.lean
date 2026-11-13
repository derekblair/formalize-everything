import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Topology.MetricSpace.Equicontinuity

/- Scratch integration: validation in progress. -/

/- BEGIN Chapter18Core.lean -/








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
/- END Chapter18Core.lean -/

/- BEGIN Chapter18Ideals.lean -/







/-! Faithful supporting fragment for Rudin RCA, printed third edition, 18.12–18.17.
General homomorphisms are not assumed to preserve the unit; characters are initially
nonzero multiplicative linear maps, without a continuity hypothesis. -/

noncomputable section

open Set
open scoped Topology NNReal ENNReal

namespace RudinRCA.Chapter18

section AlgebraicIdeals

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

/-- 18.12: the book's homomorphisms preserve addition, scalar multiplication and
multiplication, and may be zero. -/
abbrev RudinHom (A B : Type*) [CommRing A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] := A →ₙₐ[ℂ] B

/-- 18.12: ideals are also complex linear subspaces. -/
def definition18_12_idealSubspace (I : Ideal A) : Submodule ℂ A :=
  I.restrictScalars ℂ

/-- 18.12: no proper ideal contains an invertible element. -/
theorem definition18_12_no_unit_in_proper_ideal (I : Ideal A) (hI : I ≠ ⊤)
    {x : A} (hx : x ∈ I) : ¬IsUnit x :=
  fun hu => hI (I.eq_top_of_isUnit_mem hx hu)

/-- 18.12: the kernel of a homomorphism, including a zero homomorphism, is an ideal. -/
def definition18_12_kernel (φ : RudinHom A B) : Ideal A where
  carrier := {x | φ x = 0}
  zero_mem' := map_zero φ
  add_mem' := by
    intro x y hx hy
    change φ x = 0 at hx
    change φ y = 0 at hy
    change φ (x + y) = 0
    simp [map_add, hx, hy]
  smul_mem' := by
    intro a x hx
    change φ x = 0 at hx
    change φ (a * x) = 0
    simp [map_mul, hx]

@[simp] theorem definition18_12_mem_kernel (φ : RudinHom A B) (x : A) :
    x ∈ definition18_12_kernel φ ↔ φ x = 0 := Iff.rfl

/-- 18.13, algebraic part. -/
theorem theorem18_13_maximal_containment (I : Ideal A) (hI : I ≠ ⊤) :
    ∃ M : Ideal A, M.IsMaximal ∧ I ≤ M :=
  I.exists_le_maximal hI

/-- 18.14: the quotient projection is a surjective algebra homomorphism. -/
theorem theorem18_14_quotient_surjective (I : Ideal A) :
    Function.Surjective (Ideal.Quotient.mkₐ ℂ I) :=
  Ideal.Quotient.mkₐ_surjective ℂ I

/-- 18.14: multiplication and the unit descend to the quotient. -/
theorem theorem18_14_quotient_operations (I : Ideal A) (x y : A) :
    Ideal.Quotient.mkₐ ℂ I (x * y) =
      Ideal.Quotient.mkₐ ℂ I x * Ideal.Quotient.mkₐ ℂ I y ∧
    Ideal.Quotient.mkₐ ℂ I 1 = 1 :=
  ⟨map_mul _ _ _, map_one _⟩

/-- 18.14: every ideal is the kernel of its quotient homomorphism. -/
theorem theorem18_14_quotient_kernel (I : Ideal A) :
    RingHom.ker (Ideal.Quotient.mkₐ ℂ I : A →+* A ⧸ I) = I :=
  Ideal.Quotient.mkₐ_ker ℂ I

/-- 18.14: the quotient is a field exactly when the ideal is maximal. -/
theorem theorem18_14_quotient_isField_iff (I : Ideal A) :
    IsField (A ⧸ I) ↔ I.IsMaximal :=
  (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).symm

end AlgebraicIdeals

section VectorSpaceQuotient

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- 18.14: the coset `x + J`, as a subset of the original vector space. -/
def definition18_14_coset (J : Submodule ℂ E) (x : E) : Set E :=
  (fun y => x + y) '' (J : Set E)

theorem theorem18_14_mem_coset (J : Submodule ℂ E) (x z : E) :
    z ∈ definition18_14_coset J x ↔ z - x ∈ J := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hz
    exact ⟨z - x, hz, by abel⟩

/-- 18.14: the zero coset is exactly the subspace being quotiented out. -/
theorem theorem18_14_zero_coset (J : Submodule ℂ E) :
    definition18_14_coset J 0 = (J : Set E) := by
  ext z
  simp [theorem18_14_mem_coset]

/-- 18.14: equal cosets correspond exactly to a difference in the subspace. -/
theorem theorem18_14_coset_eq_iff (J : Submodule ℂ E) (x y : E) :
    definition18_14_coset J x = definition18_14_coset J y ↔ x - y ∈ J := by
  constructor
  · intro h
    have hx : x ∈ definition18_14_coset J x := ⟨0, J.zero_mem, add_zero x⟩
    rw [h, theorem18_14_mem_coset] at hx
    exact hx
  · intro h
    ext z
    rw [theorem18_14_mem_coset, theorem18_14_mem_coset]
    constructor
    · intro hz
      convert J.add_mem hz h using 1 <;> abel
    · intro hz
      convert J.sub_mem hz h using 1 <;> abel

/-- 18.14: distinct cosets are disjoint. -/
theorem theorem18_14_cosets_disjoint (J : Submodule ℂ E) {x y : E}
    (h : x - y ∉ J) :
    Disjoint (definition18_14_coset J x) (definition18_14_coset J y) := by
  rw [Set.disjoint_left]
  intro z hx hy
  rw [theorem18_14_mem_coset] at hx hy
  apply h
  convert J.sub_mem hy hx using 1 <;> abel

/-- 18.14: the quotient map identifies exactly equal cosets. -/
theorem theorem18_14_quotient_eq_iff (J : Submodule ℂ E) (x y : E) :
    J.mkQ x = J.mkQ y ↔ x - y ∈ J :=
  Submodule.Quotient.eq J

/-- 18.14: the canonical quotient map is linear and surjective. -/
theorem theorem18_14_linear_quotient_surjective (J : Submodule ℂ E) :
    Function.Surjective J.mkQ := J.mkQ_surjective

theorem theorem18_14_linear_quotient_operations (J : Submodule ℂ E)
    (x y : E) (c : ℂ) :
    J.mkQ (x + y) = J.mkQ x + J.mkQ y ∧
    J.mkQ (c • x) = c • J.mkQ x ∧ J.mkQ 0 = 0 :=
  ⟨map_add _ _ _, map_smul _ _ _, map_zero _⟩

theorem theorem18_14_linear_quotient_kernel (J : Submodule ℂ E) :
    LinearMap.ker J.mkQ = J := J.ker_mkQ

end VectorSpaceQuotient

section QuotientNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- 18.15: the quotient norm is the infimum of the norms in the coset. -/
theorem theorem18_15_quotient_norm_inf (J : Submodule ℂ E) (x : E) :
    ‖J.mkQ x‖ = sInf ((fun y => ‖x + y‖) '' (J : Set E)) :=
  quotient_norm_mk_eq J.toAddSubgroup x

/-- 18.15: the same quotient norm is the distance to the subspace. -/
theorem theorem18_15_quotient_norm_distance (J : Submodule ℂ E) (x : E) :
    ‖J.mkQ x‖ = Metric.infDist x (J : Set E) :=
  QuotientAddGroup.norm_mk x

/-- 18.15(a): closedness makes the quotient seminorm a genuine norm. -/
theorem theorem18_15_quotient_norm_zero_iff (J : Submodule ℂ E)
    [IsClosed (J : Set E)] (x : E) : ‖J.mkQ x‖ = 0 ↔ x ∈ J := by
  rw [norm_eq_zero]
  exact Submodule.Quotient.mk_eq_zero J

/-- 18.15(a): a quotient by a closed subspace is a normed vector space. -/
abbrev definition18_15_quotientNormedGroup (J : Submodule ℂ E) [IsClosed (J : Set E)] :
    NormedAddCommGroup (E ⧸ J) := inferInstance

abbrev definition18_15_quotientNormedSpace (J : Submodule ℂ E) :
    NormedSpace ℂ (E ⧸ J) := inferInstance

/-- 18.15(b): a quotient of a Banach space by a closed subspace is complete. -/
theorem theorem18_15_quotient_complete (J : Submodule ℂ E) [CompleteSpace E] :
    CompleteSpace (E ⧸ J) := inferInstance

end QuotientNorm

section BanachAlgebraQuotient

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- 18.13, topological part: maximal ideals are closed. -/
theorem theorem18_13_maximal_closed (I : Ideal A) (hI : I.IsMaximal) :
    IsClosed (I : Set A) := by
  letI := hI
  infer_instance

/-- 18.15(c): the quotient by a closed ideal is a normed commutative algebra. -/
abbrev definition18_15_quotientNormedRing (I : Ideal A) [IsClosed (I : Set A)] :
    NormedCommRing (A ⧸ I) := inferInstance

abbrev definition18_15_quotientNormedAlgebra (I : Ideal A) :
    NormedAlgebra ℂ (A ⧸ I) := inferInstance

theorem theorem18_15_ideal_quotient_complete (I : Ideal A) :
    CompleteSpace (A ⧸ I) := inferInstance

theorem theorem18_15_quotient_norm_mul (I : Ideal A) (x y : A ⧸ I) :
    ‖x * y‖ ≤ ‖x‖ * ‖y‖ := norm_mul_le x y

/-- 18.15(c): the unit has norm one in the quotient by a proper closed ideal. -/
theorem theorem18_15_quotient_norm_one [NormOneClass A] (I : Ideal A)
    [IsClosed (I : Set A)] (hI : I ≠ ⊤) : ‖(1 : A ⧸ I)‖ = 1 := by
  letI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  apply le_antisymm
  · simpa using Ideal.Quotient.norm_mk_le I (1 : A)
  · exact one_le_norm_one (A ⧸ I)

end BanachAlgebraQuotient

section Characters

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- 18.16: a character is a nonzero multiplicative complex linear functional.
Continuity and preservation of 1 are conclusions below, not assumptions. -/
def RudinCharacter (A : Type*) [CommRing A] [Algebra ℂ A] :=
  {h : RudinHom A ℂ // h ≠ 0}

/-- Every nonzero multiplicative linear functional preserves the unit. -/
theorem definition18_16_character_map_one (h : RudinCharacter A) : h.val 1 = 1 := by
  have hn : ∃ a : A, h.val a ≠ 0 := by
    by_contra! hn
    apply h.property
    ext a
    exact hn a
  obtain ⟨a, ha⟩ := hn
  apply mul_right_cancel₀ ha
  rw [← map_mul, one_mul, one_mul]

/-- The book's initially nonunital character determines a unital algebra homomorphism. -/
def definition18_16_characterAlgHom (h : RudinCharacter A) : A →ₐ[ℂ] ℂ where
  toFun := h.val
  map_zero' := map_zero h.val
  map_add' := map_add h.val
  map_one' := definition18_16_character_map_one h
  map_mul' := map_mul h.val
  commutes' := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, map_smul, definition18_16_character_map_one]
    simp

/-- Conversely, a unital algebra homomorphism to ℂ is a character in Rudin's sense. -/
def definition18_16_algHomCharacter (h : A →ₐ[ℂ] ℂ) : RudinCharacter A :=
  ⟨h.toNonUnitalAlgHom, by
    intro hz
    have hh := DFunLike.congr_fun hz 1
    change h 1 = 0 at hh
    simpa using hh⟩

/-- 18.16: the equivalent description as homomorphisms onto ℂ. -/
theorem definition18_16_character_surjective (h : RudinCharacter A) :
    Function.Surjective h.val := by
  intro c
  exact ⟨algebraMap ℂ A c, (definition18_16_characterAlgHom h).commutes c⟩

/-- 18.16: a multiplicative linear functional is nonzero exactly when it is onto. -/
theorem definition18_16_nonzero_iff_surjective (h : RudinHom A ℂ) :
    h ≠ 0 ↔ Function.Surjective h := by
  constructor
  · intro hn
    exact definition18_16_character_surjective ⟨h, hn⟩
  · intro hs hz
    obtain ⟨a, ha⟩ := hs 1
    have hzero := DFunLike.congr_fun hz a
    simp [ha] at hzero

end Characters

section BanachCharacters

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The quotient by a maximal ideal, followed by the Gelfand–Mazur isomorphism.
This gives the general Banach-algebra argument without importing the C-star
Gelfand-duality development. -/
def definition18_17_quotientCharacter (I : Ideal A) [I.IsMaximal] : A →ₐ[ℂ] ℂ :=
  ((NormedRing.algEquivComplexOfComplete
    (letI := Ideal.Quotient.field I; isUnit_iff_ne_zero (G₀ := A ⧸ I))).symm.toAlgHom).comp
      (Ideal.Quotient.mkₐ ℂ I)

theorem theorem18_17_quotientCharacter_zero (I : Ideal A) [I.IsMaximal]
    {a : A} (ha : a ∈ I) : definition18_17_quotientCharacter I a = 0 := by
  unfold definition18_17_quotientCharacter
  rw [AlgHom.comp_apply]
  have hmk : (Ideal.Quotient.mkₐ ℂ I) a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
  rw [hmk, map_zero]

/-- 18.17(a): every maximal ideal is the kernel of a character. -/
theorem theorem18_17_a (I : Ideal A) (hI : I.IsMaximal) :
    ∃ h : RudinCharacter A, definition18_12_kernel h.val = I := by
  letI := hI
  let h : A →ₐ[ℂ] ℂ := definition18_17_quotientCharacter I
  refine ⟨definition18_16_algHomCharacter h, ?_⟩
  have hle : I ≤ RingHom.ker h := by
    intro a ha
    exact theorem18_17_quotientCharacter_zero I ha
  have heq : I = RingHom.ker h := hI.eq_of_le (RingHom.ker_ne_top h) hle
  exact heq.symm

/-- The proper principal ideal generated by a nonunit lies in the kernel of a character. -/
theorem theorem18_17_nonunit_character {a : A} (ha : ¬IsUnit a) :
    ∃ h : RudinCharacter A, h.val a = 0 := by
  obtain ⟨I, hI, haI⟩ :=
    (Ideal.span {a}).exists_le_maximal (Ideal.span_singleton_ne_top ha)
  obtain ⟨h, hker⟩ := theorem18_17_a I hI
  refine ⟨h, ?_⟩
  change a ∈ definition18_12_kernel h.val
  rw [hker]
  exact haI (Ideal.subset_span (by simp))

/-- 18.17(b): the spectrum consists exactly of character values. -/
theorem theorem18_17_b (a : A) (z : ℂ) :
    z ∈ spectrum ℂ a ↔ ∃ h : RudinCharacter A, h.val a = z := by
  constructor
  · intro hz
    obtain ⟨h, hh⟩ := theorem18_17_nonunit_character (spectrum.mem_iff.mp hz)
    have hh' : (definition18_16_characterAlgHom h) (algebraMap ℂ A z - a) = 0 := hh
    simp only [map_sub, AlgHom.commutes, sub_eq_zero] at hh'
    exact ⟨h, hh'.symm⟩
  · rintro ⟨h, rfl⟩
    exact AlgHom.apply_mem_spectrum (definition18_16_characterAlgHom h) a

/-- 18.17(c): invertibility is equivalent to nonvanishing under every character. -/
theorem theorem18_17_c (a : A) :
    IsUnit a ↔ ∀ h : RudinCharacter A, h.val a ≠ 0 := by
  constructor
  · intro ha h hz
    have hu := ha.map (definition18_16_characterAlgHom h).toMonoidHom
    exact not_isUnit_zero (hz ▸ hu)
  · intro h
    by_contra ha
    obtain ⟨φ, hφ⟩ := theorem18_17_nonunit_character ha
    exact h φ hφ

/-- 18.17(d): each character value belongs to the spectrum. -/
theorem theorem18_17_d (h : RudinCharacter A) (a : A) :
    h.val a ∈ spectrum ℂ a :=
  AlgHom.apply_mem_spectrum (definition18_16_characterAlgHom h) a

/-- 18.17(e): character values are bounded by spectral radius, which is bounded by norm. -/
theorem theorem18_17_e [NormOneClass A] (h : RudinCharacter A) (a : A) :
    ‖h.val a‖ ≤ (spectralRadius ℂ a).toReal ∧
      (spectralRadius ℂ a).toReal ≤ ‖a‖ := by
  have hupper : spectralRadius ℂ a ≤ (‖a‖₊ : ℝ≥0∞) := spectralRadius_le_nnnorm a
  have hfinite : spectralRadius ℂ a ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hupper
  have hlower : (‖h.val a‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ a := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup_of_le (h.val a) (le_iSup_of_le (theorem18_17_d h a) le_rfl)
  constructor
  · simpa using ENNReal.toReal_mono hfinite hlower
  · simpa using ENNReal.toReal_mono ENNReal.coe_ne_top hupper

/-- Following 18.17: continuity of every initially algebraic character is automatic. -/
theorem theorem18_17_character_continuous (h : RudinCharacter A) : Continuous h.val :=
  (definition18_16_characterAlgHom h).toContinuousLinearMap.continuous

/-- Following 18.17: in fact the functional norm is exactly one. -/
theorem theorem18_17_character_norm [NormOneClass A] (h : RudinCharacter A) :
    ‖(definition18_16_characterAlgHom h).toContinuousLinearMap‖ = 1 :=
  AlgHom.toContinuousLinearMap_norm _

end BanachCharacters

end RudinRCA.Chapter18

#print axioms RudinRCA.Chapter18.definition18_12_no_unit_in_proper_ideal
#print axioms RudinRCA.Chapter18.definition18_12_mem_kernel
#print axioms RudinRCA.Chapter18.theorem18_13_maximal_containment
#print axioms RudinRCA.Chapter18.theorem18_13_maximal_closed
#print axioms RudinRCA.Chapter18.theorem18_14_coset_eq_iff
#print axioms RudinRCA.Chapter18.theorem18_14_cosets_disjoint
#print axioms RudinRCA.Chapter18.theorem18_14_quotient_kernel
#print axioms RudinRCA.Chapter18.theorem18_14_quotient_isField_iff
#print axioms RudinRCA.Chapter18.theorem18_15_quotient_norm_inf
#print axioms RudinRCA.Chapter18.theorem18_15_quotient_norm_distance
#print axioms RudinRCA.Chapter18.theorem18_15_quotient_complete
#print axioms RudinRCA.Chapter18.theorem18_15_quotient_norm_one
#print axioms RudinRCA.Chapter18.definition18_16_character_map_one
#print axioms RudinRCA.Chapter18.definition18_16_character_surjective
#print axioms RudinRCA.Chapter18.definition18_16_nonzero_iff_surjective
#print axioms RudinRCA.Chapter18.theorem18_17_a
#print axioms RudinRCA.Chapter18.theorem18_17_quotientCharacter_zero
#print axioms RudinRCA.Chapter18.theorem18_17_nonunit_character
#print axioms RudinRCA.Chapter18.theorem18_17_b
#print axioms RudinRCA.Chapter18.theorem18_17_c
#print axioms RudinRCA.Chapter18.theorem18_17_d
#print axioms RudinRCA.Chapter18.theorem18_17_e
#print axioms RudinRCA.Chapter18.theorem18_17_character_continuous
#print axioms RudinRCA.Chapter18.theorem18_17_character_norm
#print axioms RudinRCA.Chapter18.theorem18_14_quotient_surjective
#print axioms RudinRCA.Chapter18.theorem18_14_quotient_operations
#print axioms RudinRCA.Chapter18.theorem18_14_mem_coset
#print axioms RudinRCA.Chapter18.theorem18_14_zero_coset
#print axioms RudinRCA.Chapter18.theorem18_14_quotient_eq_iff
#print axioms RudinRCA.Chapter18.theorem18_14_linear_quotient_surjective
#print axioms RudinRCA.Chapter18.theorem18_14_linear_quotient_operations
#print axioms RudinRCA.Chapter18.theorem18_14_linear_quotient_kernel
#print axioms RudinRCA.Chapter18.theorem18_15_ideal_quotient_complete
#print axioms RudinRCA.Chapter18.theorem18_15_quotient_norm_mul
#print axioms RudinRCA.Chapter18.theorem18_15_quotient_norm_zero_iff
/- END Chapter18Ideals.lean -/

/- BEGIN Chapter18Disc.lean -/










noncomputable section

open Set Metric Filter
open scoped Topology NNReal ENNReal

namespace RudinRCA.Chapter18

abbrev DiscClosed := ↥(closedBall (0 : ℂ) 1)
abbrev DiscCircle := ↥(sphere (0 : ℂ) 1)

instance discClosedNonempty : Nonempty DiscClosed := ⟨⟨0, by simp⟩⟩
instance discCircleNonempty : Nonempty DiscCircle := ⟨⟨1, by simp⟩⟩

/-- The values outside the closed disc only totalize a function on a subtype. -/
def discExtend (f : C(DiscClosed, ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ closedBall (0 : ℂ) 1 then f ⟨z, hz⟩ else 0

@[simp] theorem discExtend_apply (f : C(DiscClosed, ℂ)) (z : DiscClosed) :
    discExtend f z = f z := by simp [discExtend, z.property]

theorem discExtend_continuousOn (f : C(DiscClosed, ℂ)) :
    ContinuousOn (discExtend f) (closedBall (0 : ℂ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (closedBall (0 : ℂ) 1).domRestrict (discExtend f) = f :=
    funext (fun z => discExtend_apply f z)
  rw [heq]
  exact f.continuous

/-- The disc algebra: continuous on the closed disc and holomorphic in its interior. -/
def discSubalgebra : Subalgebra ℂ C(DiscClosed, ℂ) where
  carrier := {f | DifferentiableOn ℂ (discExtend f) (ball (0 : ℂ) 1)}
  algebraMap_mem' c := by
    apply (differentiableOn_const c).congr
    intro z hz
    simp [discExtend, ball_subset_closedBall hz]
  add_mem' hf hg := by
    apply (hf.add hg).congr
    intro z hz
    simp [discExtend, ball_subset_closedBall hz]
  mul_mem' hf hg := by
    apply (hf.mul hg).congr
    intro z hz
    simp [discExtend, ball_subset_closedBall hz]

abbrev DiscAlgebra := ↥discSubalgebra

instance discNormOneClass : NormOneClass DiscAlgebra where
  norm_one := show ‖(1 : C(DiscClosed, ℂ))‖ = 1 from norm_one

theorem disc_diffContOnCl (f : DiscAlgebra) :
    DiffContOnCl ℂ (discExtend f.val) (ball (0 : ℂ) 1) :=
  DiffContOnCl.mk_ball f.property (discExtend_continuousOn f.val)

theorem discSubalgebra_isClosed : IsClosed (discSubalgebra : Set C(DiscClosed, ℂ)) := by
  apply IsSeqClosed.isClosed
  intro F f hF ht
  have hu : TendstoUniformlyOn (fun n => discExtend (F n)) (discExtend f)
      atTop (ball (0 : ℂ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp ht ε hε] with n hn z hz
    simpa [discExtend, ball_subset_closedBall hz, dist_comm] using
      (ContinuousMap.dist_apply_le_dist (f := F n) (g := f)
        ⟨z, ball_subset_closedBall hz⟩).trans_lt hn
  exact hu.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall hF) isOpen_ball

instance discCompleteSpace : CompleteSpace DiscAlgebra :=
  discSubalgebra_isClosed.isComplete.completeSpace_coe

def discEval (z : DiscClosed) : DiscAlgebra →ₐ[ℂ] ℂ :=
  (ContinuousMap.evalAlgHom ℂ ℂ z).comp discSubalgebra.val

@[simp] theorem discEval_apply (z : DiscClosed) (f : DiscAlgebra) :
    discEval z f = f.val z := rfl

/-- Reciprocal of a nowhere-zero disc-algebra function, with its full holomorphy proof. -/
def discReciprocal (f : DiscAlgebra) (hf : ∀ z : DiscClosed, f.val z ≠ 0) :
    DiscAlgebra := by
  let g : C(DiscClosed, ℂ) := ⟨fun z => (f.val z)⁻¹, f.val.continuous.inv₀ hf⟩
  refine ⟨g, ?_⟩
  have hn : ∀ z ∈ ball (0 : ℂ) 1, discExtend f.val z ≠ 0 := by
    intro z hz
    simpa [discExtend, ball_subset_closedBall hz] using hf ⟨z, ball_subset_closedBall hz⟩
  apply (f.property.inv hn).congr
  intro z hz
  simp [discExtend, ball_subset_closedBall hz, g]

@[simp] theorem discReciprocal_apply (f : DiscAlgebra)
    (hf : ∀ z : DiscClosed, f.val z ≠ 0) (z : DiscClosed) :
    (discReciprocal f hf).val z = (f.val z)⁻¹ := rfl

theorem disc_isUnit_iff (f : DiscAlgebra) :
    IsUnit f ↔ ∀ z : DiscClosed, f.val z ≠ 0 := by
  constructor
  · intro hf z
    exact isUnit_iff_ne_zero.mp (hf.map (discEval z))
  · intro hf
    refine ⟨⟨f, discReciprocal f hf, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      apply ContinuousMap.ext
      intro z
      exact mul_inv_cancel₀ (hf z)
    · apply Subtype.ext
      apply ContinuousMap.ext
      intro z
      exact inv_mul_cancel₀ (hf z)

theorem disc_spectrum_eq_range (f : DiscAlgebra) :
    spectrum ℂ f = Set.range f.val := by
  ext c
  simp only [spectrum.mem_iff, disc_isUnit_iff, not_forall, Classical.not_not,
    Set.mem_range]
  change (∃ z : DiscClosed, c - f.val z = 0) ↔ ∃ z : DiscClosed, f.val z = c
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, (sub_eq_zero.mp hz).symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, sub_eq_zero.mpr hz.symm⟩

def discCoordinate : DiscAlgebra :=
  ⟨⟨Subtype.val, continuous_subtype_val⟩, by
    apply differentiableOn_id.congr
    intro z hz
    simp [discExtend, ball_subset_closedBall hz]⟩

@[simp] theorem discCoordinate_apply (z : DiscClosed) :
    discCoordinate.val z = (z : ℂ) := rfl

/-- The coordinate function's spectrum in the disc algebra is the closed unit disc. -/
theorem discCoordinate_spectrum :
    spectrum ℂ discCoordinate = closedBall (0 : ℂ) 1 := by
  rw [disc_spectrum_eq_range]
  exact Subtype.range_coe

def discBoundaryInclusion : C(DiscCircle, DiscClosed) :=
  ⟨fun z => ⟨z.val, sphere_subset_closedBall z.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def discBoundary : DiscAlgebra →ₐ[ℂ] C(DiscCircle, ℂ) where
  toFun f := f.val.comp discBoundaryInclusion
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem discBoundary_apply (f : DiscAlgebra) (z : DiscCircle) :
    discBoundary f z = f.val ⟨z.val, sphere_subset_closedBall z.property⟩ := rfl

theorem discBoundary_norm (f : DiscAlgebra) : ‖discBoundary f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro z
    exact f.val.norm_coe_le_norm _
  · change ‖f.val‖ ≤ ‖discBoundary f‖
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro z
    have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (disc_diffContOnCl f) (C := ‖discBoundary f‖)
    have hz : (z : ℂ) ∈ closure (ball (0 : ℂ) 1) := by
      simpa only [closure_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0)] using z.property
    rw [← discExtend_apply f.val z]
    apply hmax _ hz
    intro w hw
    rw [frontier_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0)] at hw
    simpa [discExtend, sphere_subset_closedBall hw] using
      (discBoundary f).norm_coe_le_norm ⟨w, hw⟩

theorem discBoundary_isometry : Isometry discBoundary := by
  exact AddMonoidHomClass.isometry_of_norm discBoundary discBoundary_norm

def discBoundarySubalgebra : Subalgebra ℂ C(DiscCircle, ℂ) := discBoundary.range

theorem discBoundarySubalgebra_isClosed :
    IsClosed (discBoundarySubalgebra : Set C(DiscCircle, ℂ)) :=
  discBoundary_isometry.isClosedEmbedding.isClosed_range

def discBoundaryEquiv : DiscAlgebra ≃ₐ[ℂ] discBoundarySubalgebra :=
  AlgEquiv.ofInjective discBoundary discBoundary_isometry.injective

def discBoundaryCoordinate : discBoundarySubalgebra := discBoundaryEquiv discCoordinate

/-- Passing to boundary values preserves the disc-algebra spectrum. -/
theorem discBoundaryCoordinate_subalgebra_spectrum :
    spectrum ℂ discBoundaryCoordinate = closedBall (0 : ℂ) 1 := by
  rw [discBoundaryCoordinate, AlgEquiv.spectrum_eq, discCoordinate_spectrum]

/-- In the full circle-function algebra, the same coordinate has only the circle as spectrum. -/
theorem discBoundaryCoordinate_spectrum :
    spectrum ℂ (discBoundary discCoordinate) = sphere (0 : ℂ) 1 := by
  rw [ContinuousMap.spectrum_eq_range]
  exact Subtype.range_coe

/-- The printed example exhibits genuinely different spectra in the two algebras. -/
theorem discCoordinate_spectra_differ :
    spectrum ℂ discBoundaryCoordinate ≠ spectrum ℂ (discBoundary discCoordinate) := by
  rw [discBoundaryCoordinate_subalgebra_spectrum, discBoundaryCoordinate_spectrum]
  intro h
  have hz : (0 : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp
  rw [h] at hz
  simpa using hz

theorem disc_radius_eq_one_of_spectrum {A : Type*} [Ring A] [Algebra ℂ A] (a : A)
    (h1 : (1 : ℂ) ∈ spectrum ℂ a)
    (hb : ∀ z ∈ spectrum ℂ a, ‖z‖ ≤ 1) : spectralRadius ℂ a = 1 := by
  rw [spectralRadius_eq_of_unital]
  apply le_antisymm
  · apply iSup₂_le
    intro z hz
    exact_mod_cast hb z hz
  · simpa using le_iSup₂ (f := fun z (_ : z ∈ spectrum ℂ a) => (‖z‖₊ : ℝ≥0∞)) 1 h1

theorem discBoundaryCoordinate_subalgebra_radius :
    spectralRadius ℂ discBoundaryCoordinate = 1 := by
  apply disc_radius_eq_one_of_spectrum
  · simp [discBoundaryCoordinate_subalgebra_spectrum]
  · intro z hz
    simpa only [discBoundaryCoordinate_subalgebra_spectrum, mem_closedBall_zero_iff] using hz

theorem discBoundaryCoordinate_radius :
    spectralRadius ℂ (discBoundary discCoordinate) = 1 := by
  apply disc_radius_eq_one_of_spectrum
  · simp [discBoundaryCoordinate_spectrum]
  · intro z hz
    exact le_of_eq (by simpa only [discBoundaryCoordinate_spectrum, mem_sphere_zero_iff_norm] using hz)

/-- Although the spectra in Rudin 18.11 differ, both spectral radii are one. -/
theorem discCoordinate_spectralRadii_equal :
    spectralRadius ℂ discBoundaryCoordinate =
      spectralRadius ℂ (discBoundary discCoordinate) :=
  discBoundaryCoordinate_subalgebra_radius.trans discBoundaryCoordinate_radius.symm

/-- A polynomial in the disc coordinate, represented by finitely many coefficients. -/
def discPolynomial (c : ℕ → ℂ) (n : ℕ) : DiscAlgebra :=
  ∑ k ∈ Finset.range n, c k • discCoordinate ^ k

@[simp] theorem discPolynomial_apply (c : ℕ → ℂ) (n : ℕ) (z : DiscClosed) :
    (discPolynomial c n).val z = ∑ k ∈ Finset.range n, c k * (z : ℂ) ^ k := by
  simp [discPolynomial]

theorem discPolynomial_partialSum (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (r : ℝ) (n : ℕ) (z : DiscClosed) :
    (discPolynomial (fun k => (r : ℂ) ^ k * p.coeff k) n).val z =
      p.partialSum n ((r : ℂ) * z) := by
  rw [discPolynomial_apply, FormalMultilinearSeries.partialSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp only [smul_eq_mul, mul_pow]
  ring

set_option maxHeartbeats 1000000 in
/-- Polynomial density in the disc algebra, including boundary-continuous functions. -/
theorem disc_polynomial_approx (f : DiscAlgebra) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ → ℂ, ∃ n : ℕ, ‖f - discPolynomial c n‖ < ε := by
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨δ, hδ, huc⟩ := f.val.uniform_continuity (ε / 3) hthird
  obtain ⟨r, hr, hr1⟩ := exists_between
    (max_lt (sub_lt_self (1 : ℝ) hδ) zero_lt_one)
  have hr0 : 0 < r := (le_max_right (1 - δ) 0).trans_lt hr
  have hnear : 1 - r < δ := by
    have := (le_max_left (1 - δ) 0).trans_lt hr
    linarith
  obtain ⟨s, hrs, hs1⟩ := exists_between hr1
  have hs0 : 0 ≤ s := le_of_lt (hr0.trans hrs)
  let s' : ℝ≥0 := ⟨s, hs0⟩
  let p := cauchyPowerSeries (discExtend f.val) 0 1
  have hp : HasFPowerSeriesOnBall (discExtend f.val) p 0 (1 : ℝ≥0∞) :=
    (disc_diffContOnCl f).hasFPowerSeriesOnBall (by norm_num)
  have hs' : (s' : ℝ≥0∞) < (1 : ℝ≥0∞) := by exact_mod_cast hs1
  have hu := hp.tendstoUniformlyOn hs'
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hu (ε / 3) hthird).exists
  let c : ℕ → ℂ := fun k => (r : ℂ) ^ k * p.coeff k
  refine ⟨c, n, lt_of_le_of_lt ?_ (by linarith : 2 * (ε / 3) < ε)⟩
  change ‖(f - discPolynomial c n).val‖ ≤ 2 * (ε / 3)
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro z
  have hz : ‖(z : ℂ)‖ ≤ 1 := by simpa only [mem_closedBall_zero_iff] using z.property
  have hrnorm : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr0]
  have hrz : ‖(r : ℂ) * z‖ ≤ r := by
    rw [norm_mul, hrnorm]
    exact (mul_le_mul_of_nonneg_left hz hr0.le).trans_eq (mul_one r)
  have hrzclosed : (r : ℂ) * z ∈ closedBall (0 : ℂ) 1 :=
    mem_closedBall_zero_iff.mpr (hrz.trans hr1.le)
  let rz : DiscClosed := ⟨(r : ℂ) * z, hrzclosed⟩
  have hdist : dist rz z < δ := by
    change ‖(r : ℂ) * (z : ℂ) - z‖ < δ
    rw [← sub_one_mul, norm_mul]
    have hrminus : ‖(r : ℂ) - 1‖ = 1 - r := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real]
      exact abs_of_nonpos (sub_nonpos.mpr hr1.le) |>.trans (by ring)
    rw [hrminus]
    exact ((mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr hr1.le)).trans_eq
      (mul_one (1 - r))).trans_lt hnear
  have hclose : dist (f.val z) (f.val rz) < ε / 3 := by
    simpa only [dist_comm] using huc hdist
  have hseries := hn ((r : ℂ) * z) (mem_ball_zero_iff.mpr (hrz.trans_lt hrs))
  have happrox : dist (f.val rz) ((discPolynomial c n).val z) < ε / 3 := by
    simpa only [zero_add, discPolynomial_partialSum, c,
      discExtend, dif_pos hrzclosed] using hseries
  have htri := (dist_triangle (f.val z) (f.val rz) ((discPolynomial c n).val z)).trans
    (add_le_add hclose.le happrox.le)
  simpa only [ContinuousMap.sub_apply, dist_eq_norm, two_mul] using htri

set_option maxHeartbeats 1000000 in
/-- Every complex algebra character of the disc algebra is evaluation at one closed-disc point. -/
theorem disc_character_evaluation (h : DiscAlgebra →ₐ[ℂ] ℂ) :
    ∃ z : DiscClosed, ∀ f : DiscAlgebra, h f = f.val z := by
  have hc : h discCoordinate ∈ closedBall (0 : ℂ) 1 := by
    simpa only [discCoordinate_spectrum] using AlgHom.apply_mem_spectrum h discCoordinate
  let z : DiscClosed := ⟨h discCoordinate, hc⟩
  refine ⟨z, fun f => ?_⟩
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨c, n, hn⟩ := disc_polynomial_approx f (half_pos hε)
  let q := discPolynomial c n
  have hq : h q = q.val z := by
    simp [q, discPolynomial, z]
  have hleft : dist (h f) (h q) ≤ ‖f - q‖ := by
    simpa only [dist_eq_norm, map_sub] using AlgHom.norm_apply_le_self h (f - q)
  have hright : dist (q.val z) (f.val z) ≤ ‖f - q‖ := by
    rw [dist_eq_norm, norm_sub_rev]
    exact (f - q).val.norm_coe_le_norm z
  calc
    dist (h f) (f.val z) ≤ dist (h f) (h q) + dist (h q) (f.val z) :=
      dist_triangle _ _ _
    _ ≤ ‖f - q‖ + ‖f - q‖ := add_le_add hleft (by simpa only [hq] using hright)
    _ ≤ ε := by dsimp [q]; linarith

/-- The maximal-ideal quotient supplies a complex character vanishing on that ideal. -/
theorem disc_maximal_character {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (I : Ideal A) [I.IsMaximal] :
    ∃ h : A →ₐ[ℂ] ℂ, ∀ a ∈ I, h a = 0 := by
  let h : A →ₐ[ℂ] ℂ :=
    ((NormedRing.algEquivComplexOfComplete
      (letI := Ideal.Quotient.field I; isUnit_iff_ne_zero (G₀ := A ⧸ I))).symm.toAlgHom).comp
        (Ideal.Quotient.mkₐ ℂ I)
  refine ⟨h, fun a ha => ?_⟩
  dsimp only [h]
  rw [AlgHom.comp_apply]
  have hmk : (Ideal.Quotient.mkₐ ℂ I) a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
  rw [hmk, map_zero]

theorem discEval_surjective (z : DiscClosed) : Function.Surjective (discEval z) := by
  intro c
  exact ⟨algebraMap ℂ DiscAlgebra c, (discEval z).commutes c⟩

theorem discEval_kernel_isMaximal (z : DiscClosed) :
    (RingHom.ker (discEval z)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (discEval z) (discEval_surjective z)

/-- The note following 18.18: the maximal ideals are exactly point-evaluation kernels. -/
theorem disc_maximal_iff_evaluation_kernel (I : Ideal DiscAlgebra) :
    I.IsMaximal ↔ ∃ z : DiscClosed, I = RingHom.ker (discEval z) := by
  constructor
  · intro hI
    letI := hI
    obtain ⟨h, hh⟩ := disc_maximal_character I
    obtain ⟨z, hz⟩ := disc_character_evaluation h
    refine ⟨z, hI.eq_of_le (RingHom.ker_ne_top (discEval z)) ?_⟩
    intro f hf
    change f.val z = 0
    rw [← hz f]
    exact hh f hf
  · rintro ⟨z, rfl⟩
    exact discEval_kernel_isMaximal z

/-- Rudin 18.18: a finite family with no common closed-disc zero has a Bezout identity. -/
theorem disc_bezout {ι : Type*} [Fintype ι] (f : ι → DiscAlgebra)
    (hf : ∀ z : DiscClosed, ∃ i, (f i).val z ≠ 0) :
    ∃ g : ι → DiscAlgebra, ∑ i, f i * g i = 1 := by
  have htop : Ideal.span (Set.range f) = ⊤ := by
    by_contra hproper
    obtain ⟨I, hI, hle⟩ := (Ideal.span (Set.range f)).exists_le_maximal hproper
    letI := hI
    obtain ⟨h, hh⟩ := disc_maximal_character I
    obtain ⟨z, hz⟩ := disc_character_evaluation h
    obtain ⟨i, hi⟩ := hf z
    apply hi
    rw [← hz (f i)]
    have hmem : f i ∈ I := hle (Ideal.subset_span ⟨i, rfl⟩)
    exact hh _ hmem
  have hone : (1 : DiscAlgebra) ∈ Ideal.span (Set.range f) := by rw [htop]; trivial
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.mp hone
  exact ⟨g, by simpa only [mul_comm] using hg⟩

/-- The printed positive-sum hypothesis and pointwise conclusion of Rudin 18.18. -/
theorem disc_bezout_positive {n : ℕ} (f : Fin n → DiscAlgebra)
    (hf : ∀ z : DiscClosed, 0 < ∑ i, ‖(f i).val z‖) :
    ∃ g : Fin n → DiscAlgebra, ∀ z : DiscClosed,
      ∑ i, (f i).val z * (g i).val z = 1 := by
  have hnonzero : ∀ z : DiscClosed, ∃ i, (f i).val z ≠ 0 := by
    intro z
    by_contra h
    push_neg at h
    have hsum : ∑ i, ‖(f i).val z‖ = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [h i, norm_zero])
    have := hf z
    rw [hsum] at this
    exact (lt_irrefl 0) this
  obtain ⟨g, hg⟩ := disc_bezout f hnonzero
  refine ⟨g, fun z => ?_⟩
  have := congrArg (discEval z) hg
  simpa using this

theorem discBoundary_eq_closure_adjoin :
    discBoundarySubalgebra =
      (Algebra.adjoin ℂ {discBoundary discCoordinate}).topologicalClosure := by
  apply le_antisymm
  · rintro y ⟨f, rfl⟩
    change discBoundary f ∈ closure
      (Algebra.adjoin ℂ {discBoundary discCoordinate} : Set C(DiscCircle, ℂ))
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨c, n, hn⟩ := disc_polynomial_approx f hε
    refine ⟨discBoundary (discPolynomial c n), ?_, ?_⟩
    · let B := Algebra.adjoin ℂ {discBoundary discCoordinate}
      have hx : discBoundary discCoordinate ∈ B := Algebra.self_mem_adjoin_singleton _ _
      have hsum : ∑ k ∈ Finset.range n, c k • (discBoundary discCoordinate) ^ k ∈ B :=
        B.sum_mem (fun k _ => B.smul_mem (B.pow_mem hx k) (c k))
      simpa [discPolynomial] using hsum
    · simpa only [dist_eq_norm, ← map_sub, discBoundary_norm] using hn
  · apply Subalgebra.topologicalClosure_minimal _ discBoundarySubalgebra_isClosed
    apply Algebra.adjoin_le
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact ⟨discCoordinate, rfl⟩

instance discAnglePositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The standard angular parameterization, with values in the printed unit circle. -/
def discAngleHomeomorph : AddCircle (2 * Real.pi) ≃ₜ DiscCircle :=
  AddCircle.homeomorphCircle (by positivity)

def discAngleTransport : C(DiscCircle, ℂ) →ₐ[ℂ] C(AddCircle (2 * Real.pi), ℂ) :=
  ContinuousMap.compRightAlgHom ℂ ℂ (discAngleHomeomorph : C(AddCircle (2 * Real.pi), DiscCircle))

theorem discAngleTransport_norm (f : C(DiscCircle, ℂ)) :
    ‖discAngleTransport f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro t
    exact f.norm_coe_le_norm _
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro z
    obtain ⟨t, rfl⟩ := discAngleHomeomorph.surjective z
    exact (discAngleTransport f).norm_coe_le_norm t

def discAngleBoundary : DiscAlgebra →ₐ[ℂ] C(AddCircle (2 * Real.pi), ℂ) :=
  discAngleTransport.comp discBoundary

theorem discAngleBoundary_norm (f : DiscAlgebra) : ‖discAngleBoundary f‖ = ‖f‖ :=
  (discAngleTransport_norm (discBoundary f)).trans (discBoundary_norm f)

theorem discAngleBoundary_isometry : Isometry discAngleBoundary :=
  AddMonoidHomClass.isometry_of_norm discAngleBoundary discAngleBoundary_norm

theorem discAngleBoundary_coordinate :
    discAngleBoundary discCoordinate = @fourier (2 * Real.pi) 1 := by
  apply ContinuousMap.ext
  intro t
  change ((AddCircle.homeomorphCircle (by positivity) t : Circle) : ℂ) = fourier 1 t
  rw [AddCircle.homeomorphCircle_apply, fourier_one]

def discAngleSubalgebra : Subalgebra ℂ C(AddCircle (2 * Real.pi), ℂ) :=
  discAngleBoundary.range

theorem discAngleSubalgebra_isClosed :
    IsClosed (discAngleSubalgebra : Set C(AddCircle (2 * Real.pi), ℂ)) :=
  discAngleBoundary_isometry.isClosedEmbedding.isClosed_range

theorem discAngleBoundary_power (n : ℕ) :
    discAngleBoundary (discCoordinate ^ n) = @fourier (2 * Real.pi) (n : ℤ) := by
  induction n with
  | zero => ext t; simp [fourier_zero]
  | succ n ih =>
    rw [pow_succ, map_mul, ih, discAngleBoundary_coordinate]
    ext t
    simp only [ContinuousMap.mul_apply, Nat.cast_add, Nat.cast_one]
    exact fourier_add.symm

/-- Bridge from disc-algebra boundary values to the closed span of nonnegative Fourier modes. -/
theorem discAngleSubalgebra_eq_positive_closure :
    discAngleSubalgebra.toSubmodule =
      (Submodule.span ℂ (Set.range
        (fun n : ℕ => @fourier (2 * Real.pi) (n : ℤ)))).topologicalClosure := by
  let S := Submodule.span ℂ (Set.range
    (fun n : ℕ => @fourier (2 * Real.pi) (n : ℤ)))
  apply le_antisymm
  · rintro y ⟨f, rfl⟩
    change discAngleBoundary f ∈ closure (S : Set C(AddCircle (2 * Real.pi), ℂ))
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨c, n, hn⟩ := disc_polynomial_approx f hε
    refine ⟨discAngleBoundary (discPolynomial c n), ?_, ?_⟩
    · have hsum : ∑ k ∈ Finset.range n, c k • @fourier (2 * Real.pi) (k : ℤ) ∈ S := by
        apply S.sum_mem
        intro k hk
        exact S.smul_mem (c k) (Submodule.subset_span ⟨k, rfl⟩)
      change discAngleBoundary (discPolynomial c n) ∈ S
      simpa only [discPolynomial, map_sum, map_smul, discAngleBoundary_power] using hsum
    · simpa only [dist_eq_norm, ← map_sub, discAngleBoundary_norm] using hn
  · apply Submodule.topologicalClosure_minimal S _ discAngleSubalgebra_isClosed
    apply Submodule.span_le.mpr
    rintro y ⟨n, rfl⟩
    exact ⟨discCoordinate ^ n, discAngleBoundary_power n⟩

#print axioms discSubalgebra_isClosed
#print axioms disc_isUnit_iff
#print axioms disc_spectrum_eq_range
#print axioms discCoordinate_spectrum
#print axioms discBoundary_norm
#print axioms discBoundarySubalgebra_isClosed
#print axioms discBoundaryCoordinate_subalgebra_spectrum
#print axioms discBoundaryCoordinate_spectrum
#print axioms discCoordinate_spectra_differ
#print axioms discCoordinate_spectralRadii_equal
#print axioms disc_polynomial_approx
#print axioms disc_character_evaluation
#print axioms disc_maximal_iff_evaluation_kernel
#print axioms disc_bezout
#print axioms disc_bezout_positive
#print axioms discBoundary_eq_closure_adjoin
#print axioms discAngleBoundary_coordinate
#print axioms discAngleSubalgebra_eq_positive_closure

end RudinRCA.Chapter18
/- END Chapter18Disc.lean -/

/- BEGIN Chapter18Fejer.lean -/










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
/- END Chapter18Fejer.lean -/

/- BEGIN Chapter18Maximality.lean -/









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
    (B : Subalgebra ℂ C(AddCircle T, ℂ)) (hclosed : IsClosed (B : Set _))
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
    (B : Subalgebra ℂ C(AddCircle T, ℂ)) (hclosed : IsClosed (B : Set _))
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
    (B : Subalgebra ℂ C(AddCircle T, ℂ)) (hclosed : IsClosed (B : Set _))
    (hproper : B ≠ ⊤) (hpos : fourier 1 ∈ B)
    (g : B) (n : ℤ) (hn : n < 0) : fourierCoeff (g : C(AddCircle T, ℂ)) n = 0 := by
  letI : IsClosed (B : Set _) := hclosed
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
    apply Algebra.adjoin_le.mpr
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
/- END Chapter18Maximality.lean -/

/- BEGIN Chapter18BoundaryCharacterization.lean -/





noncomputable section
open Set
open scoped Polynomial

namespace RudinRCA.Chapter18

/-- The angular Fourier coefficient uses exactly the normalization and
exponential appearing in printed18.19(1). -/
theorem theorem18_19_circle_coefficient_integral (f : C(DiscCircle, ℂ)) (n : ℤ) :
    fourierCoeff (discAngleTransport f) n =
      (1 / (2 * Real.pi) : ℝ) • ∫ θ in -Real.pi..Real.pi,
        f (Circle.exp θ) * Complex.exp (-((n : ℂ) * θ * Complex.I)) := by
  rw [fourierCoeff_eq_intervalIntegral (discAngleTransport f) n (-Real.pi)]
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  have hangle : discAngleHomeomorph (θ : AddCircle (2 * Real.pi)) = Circle.exp θ := by
    rw [discAngleHomeomorph, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
    simp [Real.pi_ne_zero]
  have hfourier : @fourier (2 * Real.pi) (-n) θ =
      Complex.exp (-((n : ℂ) * θ * Complex.I)) := by
    rw [fourier_coe_apply]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
    <;> ring
  change fourier (-n) (θ : AddCircle (2 * Real.pi)) *
    f (discAngleHomeomorph (θ : AddCircle (2 * Real.pi))) = _
  rw [hangle, hfourier, mul_comm]

/-- Printed18.19: continuous boundary functions of the disc algebra are exactly
the continuous functions with vanishing negative Fourier coefficients. -/
theorem theorem18_19_fourier_iff (f : C(AddCircle (2 * Real.pi), ℂ)) :
    f ∈ discAngleSubalgebra ↔ ∀ n : ℤ, n < 0 → fourierCoeff f n = 0 := by
  change f ∈ discAngleSubalgebra.toSubmodule ↔ _
  rw [discAngleSubalgebra_eq_positive_closure]
  exact (Fejer.fourier_negative_vanish_iff_mem_positive_closure f).symm

theorem theorem18_19_transport_injective : Function.Injective discAngleTransport := by
  intro f g hfg
  ext z
  obtain ⟨t, rfl⟩ := discAngleHomeomorph.surjective z
  exact congrArg (fun h : C(AddCircle (2 * Real.pi), ℂ) => h t) hfg

/-- The characterization is stated here on the printed unit circle itself;
`discAngleTransport` is the standard angular parameterization. -/
theorem theorem18_19_circle_fourier_iff (f : C(DiscCircle, ℂ)) :
    f ∈ discBoundarySubalgebra ↔
      ∀ n : ℤ, n < 0 → fourierCoeff (discAngleTransport f) n = 0 := by
  rw [← theorem18_19_fourier_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, theorem18_19_transport_injective hg⟩

/-- The analytic boundary algebra is proper: the conjugate coordinate has
a nonzero Fourier coefficient of index minus one. -/
theorem theorem18_19_proper : discAngleSubalgebra ≠ ⊤ := by
  intro htop
  have hf : (@fourier (2 * Real.pi) (-1)) ∈ discAngleSubalgebra := by
    rw [htop]
    trivial
  have h := (theorem18_19_fourier_iff _).mp hf (-1) (by norm_num)
  simpa [fourierCoeff_fourier] using h

theorem theorem18_19_circle_proper : discBoundarySubalgebra ≠ ⊤ := by
  intro htop
  have hcoord : discAngleTransport (star (discBoundary discCoordinate)) =
      @fourier (2 * Real.pi) (-1) := by
    ext t
    change star ((discAngleBoundary discCoordinate) t) = fourier (-1) t
    rw [discAngleBoundary_coordinate]
    exact (fourier_neg (n := 1) (x := t)).symm
  have hf : star (discBoundary discCoordinate) ∈ discBoundarySubalgebra := by
    rw [htop]
    trivial
  have h := (theorem18_19_circle_fourier_iff _).mp hf (-1) (by norm_num)
  rw [hcoord, fourierCoeff_fourier] at h
  simpa using h

/-- Printed18.19 maximality: a closed algebra containing the analytic boundary
algebra equals it or equals all continuous functions on the circle. -/
theorem theorem18_19_maximal
    (B : Subalgebra ℂ C(AddCircle (2 * Real.pi), ℂ))
    (hclosed : IsClosed (B : Set _)) (hcontains : discAngleSubalgebra ≤ B) :
    B = discAngleSubalgebra ∨ B = ⊤ := by
  by_cases htop : B = ⊤
  · exact Or.inr htop
  · apply Or.inl
    apply le_antisymm _ hcontains
    intro f hf
    apply (theorem18_19_fourier_iff f).mpr
    intro n hn
    have hcoordinate : @fourier (2 * Real.pi) 1 ∈ B :=
      hcontains ⟨discCoordinate, discAngleBoundary_coordinate⟩
    exact theorem18_20_proper_subalgebra_negative_coeff B hclosed htop hcoordinate ⟨f, hf⟩ n hn

/-- The same maximality assertion on the printed unit circle, before angular
parameterization. -/
theorem theorem18_19_circle_maximal (B : Subalgebra ℂ C(DiscCircle, ℂ))
    (hclosed : IsClosed (B : Set _)) (hcontains : discBoundarySubalgebra ≤ B) :
    B = discBoundarySubalgebra ∨ B = ⊤ := by
  let B' := B.map discAngleTransport
  have hisometry : Isometry discAngleTransport :=
    AddMonoidHomClass.isometry_of_norm discAngleTransport discAngleTransport_norm
  have hclosed' : IsClosed (B' : Set C(AddCircle (2 * Real.pi), ℂ)) :=
    hisometry.isClosedEmbedding.isClosedMap _ hclosed
  have hcontains' : discAngleSubalgebra ≤ B' := by
    rintro f ⟨g, rfl⟩
    exact ⟨discBoundary g, hcontains ⟨g, rfl⟩, rfl⟩
  rcases theorem18_19_maximal B' hclosed' hcontains' with hB | hB
  · apply Or.inl
    apply le_antisymm _ hcontains
    intro f hf
    apply (theorem18_19_circle_fourier_iff f).mpr
    apply (theorem18_19_fourier_iff (discAngleTransport f)).mp
    rw [← hB]
    exact ⟨f, hf, rfl⟩
  · apply Or.inr
    apply top_unique
    intro f _
    have htf : discAngleTransport f ∈ B' := by rw [hB]; trivial
    rcases htf with ⟨g, hg, hgf⟩
    have hgf' : g = f := theorem18_19_transport_injective hgf
    simpa only [hgf'] using hg

/-- Printed18.20 on the original unit circle: the coefficient polynomials use
the complex coordinate `z`, and one finite family works uniformly on the circle. -/
theorem theorem18_20_circle (g : C(DiscCircle, ℂ))
    (hg : ∃ n : ℤ, n < 0 ∧ fourierCoeff (discAngleTransport g) n ≠ 0)
    (f : C(DiscCircle, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (P : ℕ → ℂ[X]), ∀ z : DiscCircle,
      ‖f z - ∑ i ∈ Finset.range (N + 1), (P i).eval (z : ℂ) * g z ^ i‖ < ε := by
  obtain ⟨N, P, hP⟩ := theorem18_20 (discAngleTransport g) hg
    (discAngleTransport f) ε hε
  refine ⟨N, P, ?_⟩
  intro z
  let t := discAngleHomeomorph.symm z
  have ht : discAngleHomeomorph t = z := discAngleHomeomorph.apply_symm_apply z
  have hcoordinate : fourier 1 t = (z : ℂ) := by
    have h := congrArg (fun h : C(AddCircle (2 * Real.pi), ℂ) => h t)
      discAngleBoundary_coordinate
    change (discAngleHomeomorph t : ℂ) = fourier 1 t at h
    rw [ht] at h
    exact h.symm
  have h := hP t
  change ‖f (discAngleHomeomorph t) - ∑ i ∈ Finset.range (N + 1),
    (P i).eval (fourier 1 t) * g (discAngleHomeomorph t) ^ i‖ < ε at h
  simpa only [ht, hcoordinate] using h

end RudinRCA.Chapter18

#print axioms RudinRCA.Chapter18.theorem18_19_fourier_iff
#print axioms RudinRCA.Chapter18.theorem18_19_circle_coefficient_integral
#print axioms RudinRCA.Chapter18.theorem18_19_circle_fourier_iff
#print axioms RudinRCA.Chapter18.theorem18_19_proper
#print axioms RudinRCA.Chapter18.theorem18_19_circle_proper
#print axioms RudinRCA.Chapter18.theorem18_19_maximal
#print axioms RudinRCA.Chapter18.theorem18_19_circle_maximal
#print axioms RudinRCA.Chapter18.theorem18_20_circle
/- END Chapter18BoundaryCharacterization.lean -/

/- BEGIN Chapter18Wiener.lean -/






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
/- END Chapter18Wiener.lean -/

