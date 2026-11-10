import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported ENNReal

namespace RCA619PositivePart

variable {X : Type*} [TopologicalSpace X]

abbrev Values (L : C_c(X, ℝ) →ₗ[ℝ] ℝ) (f : C_c(X, ℝ≥0)) : Set ℝ :=
  L '' Icc 0 f.toReal

theorem values_nonempty (L : C_c(X, ℝ) →ₗ[ℝ] ℝ) (f : C_c(X, ℝ≥0)) :
    (Values L f).Nonempty :=
  ⟨0, 0, ⟨le_rfl, CompactlySupportedContinuousMap.toReal_nonneg⟩, map_zero L⟩

/-- The upper positive part on the cone of nonnegative compactly supported functions. -/
def posSup (L : C_c(X, ℝ) →ₗ[ℝ] ℝ) (f : C_c(X, ℝ≥0)) : ℝ := sSup (Values L f)

variable (L : C_c(X, ℝ) →ₗ[ℝ] ℝ)
variable (hbdd : ∀ f : C_c(X, ℝ≥0), BddAbove (Values L f))

include hbdd in
theorem le_posSup {f : C_c(X, ℝ≥0)} {g : C_c(X, ℝ)}
    (hg0 : 0 ≤ g) (hgf : g ≤ f.toReal) : L g ≤ posSup L f :=
  le_csSup (hbdd f) ⟨g, ⟨hg0, hgf⟩, rfl⟩

include hbdd in
theorem posSup_nonneg (f : C_c(X, ℝ≥0)) : 0 ≤ posSup L f := by
  simpa only [map_zero] using le_posSup L hbdd (f := f) (g := 0)
    le_rfl CompactlySupportedContinuousMap.toReal_nonneg

theorem posSup_le {f : C_c(X, ℝ≥0)} {B : ℝ}
    (hB : ∀ g : C_c(X, ℝ), 0 ≤ g → g ≤ f.toReal → L g ≤ B) : posSup L f ≤ B := by
  apply csSup_le (values_nonempty L f)
  rintro _ ⟨g, ⟨hg0, hgf⟩, rfl⟩
  exact hB g hg0 hgf

include hbdd in
theorem posSup_zero : posSup L 0 = 0 := by
  apply le_antisymm
  · apply posSup_le
    intro g hg0 hg
    have hg' : g ≤ 0 := by
      intro x
      simpa using hg x
    rw [le_antisymm hg' hg0, map_zero]
  · exact posSup_nonneg L hbdd 0

include hbdd in
theorem posSup_add (f h : C_c(X, ℝ≥0)) :
    posSup L (f + h) = posSup L f + posSup L h := by
  apply le_antisymm
  · apply posSup_le
    intro g hg0 hgf
    let g₁ : C_c(X, ℝ) := g ⊓ f.toReal
    let g₂ : C_c(X, ℝ) := g - g₁
    have hg₁0 : 0 ≤ g₁ := le_inf hg0 CompactlySupportedContinuousMap.toReal_nonneg
    have hg₁f : g₁ ≤ f.toReal := inf_le_right
    have hg₂0 : 0 ≤ g₂ := by
      intro x
      change 0 ≤ g x - min (g x) (f.toReal x)
      exact sub_nonneg.mpr (min_le_left _ _)
    have hg₂h : g₂ ≤ h.toReal := by
      intro x
      have hgfx := hgf x
      have hh0 : 0 ≤ (h.toReal x) := CompactlySupportedContinuousMap.toReal_nonneg x
      rw [CompactlySupportedContinuousMap.toReal_add,
        CompactlySupportedContinuousMap.add_apply] at hgfx
      change g x - min (g x) (f.toReal x) ≤ h.toReal x
      rcases le_total (g x) (f.toReal x) with hx | hx
      · rw [min_eq_left hx, sub_self]
        exact hh0
      · rw [min_eq_right hx]
        linarith
    have h₁ := le_posSup L hbdd hg₁0 hg₁f
    have h₂ := le_posSup L hbdd hg₂0 hg₂h
    have hsplit : L g₂ = L g - L g₁ := map_sub L g g₁
    linarith
  · have hfirst : posSup L f ≤ posSup L (f + h) - posSup L h := by
      apply posSup_le
      intro g hg0 hgf
      have hsecond : posSup L h ≤ posSup L (f + h) - L g := by
        apply posSup_le
        intro k hk0 hkh
        have hsum0 : 0 ≤ g + k := fun x ↦ add_nonneg (hg0 x) (hk0 x)
        have hsum : g + k ≤ (f + h).toReal := by
          intro x
          rw [CompactlySupportedContinuousMap.toReal_add,
            CompactlySupportedContinuousMap.add_apply,
            CompactlySupportedContinuousMap.add_apply]
          exact add_le_add (hgf x) (hkh x)
        have hle := le_posSup L hbdd hsum0 hsum
        rw [map_add] at hle
        linarith
      linarith
    linarith

include hbdd in
theorem posSup_smul (r : ℝ≥0) (f : C_c(X, ℝ≥0)) :
    posSup L (r • f) = (r : ℝ) * posSup L f := by
  by_cases hr : r = 0
  · subst r
    simp only [zero_smul, posSup_zero L hbdd, NNReal.coe_zero, zero_mul]
  have hrpos : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrpos
  apply le_antisymm
  · apply posSup_le
    intro g hg0 hgf
    let k : C_c(X, ℝ) := (r : ℝ)⁻¹ • g
    have hk0 : 0 ≤ k := fun x ↦ mul_nonneg (inv_nonneg.mpr hrpos.le) (hg0 x)
    have hkf : k ≤ f.toReal := by
      intro x
      have hx : g x ≤ (r : ℝ) * f.toReal x := by
        simpa only [CompactlySupportedContinuousMap.toReal_apply,
          CompactlySupportedContinuousMap.smul_apply, smul_eq_mul,
          NNReal.coe_mul] using hgf x
      change (r : ℝ)⁻¹ * g x ≤ f.toReal x
      exact (inv_mul_le_iff₀ hrpos).mpr hx
    have hle := le_posSup L hbdd hk0 hkf
    have hmap : L k = (r : ℝ)⁻¹ * L g := map_smul L _ g
    rw [hmap] at hle
    exact (inv_mul_le_iff₀ hrpos).mp hle
  · have hle : posSup L f ≤ (r : ℝ)⁻¹ * posSup L (r • f) := by
      apply posSup_le
      intro g hg0 hgf
      have hrg0 : 0 ≤ (r : ℝ) • g := fun x ↦ mul_nonneg hrpos.le (hg0 x)
      have hrgf : (r : ℝ) • g ≤ (r • f).toReal := by
        intro x
        simpa only [CompactlySupportedContinuousMap.toReal_apply,
          CompactlySupportedContinuousMap.smul_apply, smul_eq_mul,
          NNReal.coe_mul] using mul_le_mul_of_nonneg_left (hgf x) hrpos.le
      have hbound := le_posSup L hbdd hrg0 hrgf
      rw [map_smul] at hbound
      change (r : ℝ) * L g ≤ posSup L (r • f) at hbound
      exact (le_inv_mul_iff₀ hrpos).mpr hbound
    exact (le_inv_mul_iff₀ hrpos).mp hle

/-- The additive, homogeneous positive part on the nonnegative cone. -/
def positiveConeLinear : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 where
  toFun f := ⟨posSup L f, posSup_nonneg L hbdd f⟩
  map_add' f g := by
    apply NNReal.eq
    exact posSup_add L hbdd f g
  map_smul' r f := by
    apply NNReal.eq
    exact posSup_smul L hbdd r f

/-- Extending the cone map by positive and negative parts gives a positive
real-linear functional on all real-valued compactly supported functions. -/
def positivePart : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  CompactlySupportedContinuousMap.toRealPositiveLinear (positiveConeLinear L hbdd)

theorem positivePart_toReal (f : C_c(X, ℝ≥0)) :
    positivePart L hbdd f.toReal = posSup L f :=
  CompactlySupportedContinuousMap.eq_toRealPositiveLinear_toReal _ _

theorem le_positivePart {f : C_c(X, ℝ)} (hf : 0 ≤ f) : L f ≤ positivePart L hbdd f := by
  have hfreal : f.nnrealPart.toReal = f := by
    ext x
    simp only [CompactlySupportedContinuousMap.toReal_apply,
      CompactlySupportedContinuousMap.nnrealPart_apply, Real.coe_toNNReal' ]
    exact max_eq_left (hf x)
  rw [← hfreal, positivePart_toReal]
  apply le_posSup L hbdd
  · exact CompactlySupportedContinuousMap.toReal_nonneg
  · exact le_rfl

/-- The complementary positive functional. -/
def negativePart : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ ((positivePart L hbdd).toLinearMap - L)
    (fun f hf ↦ sub_nonneg.mpr (le_positivePart L hbdd hf))

theorem positivePart_sub_negativePart (f : C_c(X, ℝ)) :
    positivePart L hbdd f - negativePart L hbdd f = L f := by
  change positivePart L hbdd f - (positivePart L hbdd f - L f) = L f
  linarith

theorem norm_le_of_nonneg_le {g f : C_c(X, ℝ)} (hg : 0 ≤ g) (hgf : g ≤ f) :
    ‖g.toBoundedContinuousFunction‖ ≤ ‖f.toBoundedContinuousFunction‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f.toBoundedContinuousFunction)).mpr
  intro x
  change ‖g x‖ ≤ ‖f.toBoundedContinuousFunction‖
  rw [Real.norm_eq_abs, abs_of_nonneg (hg x)]
  exact (hgf x).trans (BoundedContinuousFunction.apply_le_norm f.toBoundedContinuousFunction x)

/-- A uniform bound for the original functional supplies the order boundedness
needed by the supremum construction. -/
theorem values_bddAbove_of_bound {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ g : C_c(X, ℝ), |L g| ≤ C * ‖g.toBoundedContinuousFunction‖)
    (f : C_c(X, ℝ≥0)) : BddAbove (Values L f) := by
  refine ⟨C * ‖f.toReal.toBoundedContinuousFunction‖, ?_⟩
  rintro _ ⟨g, ⟨hg0, hgf⟩, rfl⟩
  exact (le_abs_self _).trans ((hL g).trans
    (mul_le_mul_of_nonneg_left (norm_le_of_nonneg_le hg0 hgf) hC))

theorem positivePart_bound {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ g : C_c(X, ℝ), |L g| ≤ C * ‖g.toBoundedContinuousFunction‖)
    {f : C_c(X, ℝ)} (hf : 0 ≤ f) :
    positivePart L hbdd f ≤ C * ‖f.toBoundedContinuousFunction‖ := by
  have hfreal : f.nnrealPart.toReal = f := by
    ext x
    simp only [CompactlySupportedContinuousMap.toReal_apply,
      CompactlySupportedContinuousMap.nnrealPart_apply, Real.coe_toNNReal']
    exact max_eq_left (hf x)
  conv_lhs => rw [← hfreal, positivePart_toReal]
  apply posSup_le
  intro g hg0 hgf
  rw [hfreal] at hgf
  exact (le_abs_self _).trans ((hL g).trans
    (mul_le_mul_of_nonneg_left (norm_le_of_nonneg_le hg0 hgf) hC))

/-- Every bounded real linear functional on compactly supported functions is
the difference of two positive linear functionals. Their bounds on positive
functions make both representing RMK measures finite on arbitrary LCH spaces. -/
theorem exists_positive_decomposition {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ g : C_c(X, ℝ), |L g| ≤ C * ‖g.toBoundedContinuousFunction‖) :
    ∃ P Q : C_c(X, ℝ) →ₚ[ℝ] ℝ,
      (∀ f : C_c(X, ℝ), L f = P f - Q f) ∧
      (∀ f : C_c(X, ℝ), 0 ≤ f → P f ≤ C * ‖f.toBoundedContinuousFunction‖) ∧
      (∀ f : C_c(X, ℝ), 0 ≤ f → Q f ≤ (2 * C) * ‖f.toBoundedContinuousFunction‖) := by
  let hb : ∀ f : C_c(X, ℝ≥0), BddAbove (Values L f) := values_bddAbove_of_bound L hC hL
  refine ⟨positivePart L hb, negativePart L hb, ?_, ?_, ?_⟩
  · intro f
    exact (positivePart_sub_negativePart L hb f).symm
  · intro f hf
    exact positivePart_bound L hb hC hL hf
  · intro f hf
    change positivePart L hb f - L f ≤ (2 * C) * ‖f.toBoundedContinuousFunction‖
    have hP := positivePart_bound L hb hC hL hf
    have hF := (abs_le.mp (hL f)).1
    linarith

#print axioms posSup_add
#print axioms posSup_smul
#print axioms exists_positive_decomposition

section FiniteRMK

variable [LocallyCompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

/-- The positive RMK measure of a bounded functional is finite even when the
locally compact Hausdorff space is not sigma compact. -/
theorem rieszMeasure_univ_le (P : C_c(X, ℝ) →ₚ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ f : C_c(X, ℝ), 0 ≤ f → P f ≤ C * ‖f.toBoundedContinuousFunction‖) :
    RealRMK.rieszMeasure P univ ≤ ENNReal.ofReal C := by
  rw [isOpen_univ.measure_eq_iSup_isCompact (RealRMK.rieszMeasure P)]
  refine iSup_le fun K ↦ iSup_le fun _ ↦ iSup_le fun hK ↦ ?_
  obtain ⟨φ, hφK, hφcomp, _, hφrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
  let f : C_c(X, ℝ) := ⟨φ, hφcomp⟩
  have hf0 : 0 ≤ f := fun x ↦ (hφrange x).1
  have hfnorm : ‖f.toBoundedContinuousFunction‖ ≤ 1 := by
    apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
    intro x
    change ‖φ x‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (hφrange x).1]
    exact (hφrange x).2
  have hPf : P f ≤ C := (hP f hf0).trans (by nlinarith)
  exact (RealRMK.rieszMeasure_le_of_eq_one P hf0 hK hφK).trans
    (ENNReal.ofReal_le_ofReal hPf)

theorem rieszMeasure_isFiniteMeasure (P : C_c(X, ℝ) →ₚ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ f : C_c(X, ℝ), 0 ≤ f → P f ≤ C * ‖f.toBoundedContinuousFunction‖) :
    MeasureTheory.IsFiniteMeasure (RealRMK.rieszMeasure P) := by
  constructor
  exact (rieszMeasure_univ_le P hC hP).trans_lt ENNReal.ofReal_lt_top

/-- The two finite positive measures representing a bounded real functional,
stated with ordinary Bochner integrals for complex-measure assembly. -/
theorem exists_finite_measure_representation {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ g : C_c(X, ℝ), |L g| ≤ C * ‖g.toBoundedContinuousFunction‖) :
    ∃ μ ν : Measure X, IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧ μ.Regular ∧ ν.Regular ∧
      ∀ f : C_c(X, ℝ), L f = (∫ x, f x ∂μ) - ∫ x, f x ∂ν := by
  obtain ⟨P, Q, hdiff, hP, hQ⟩ := exists_positive_decomposition L hC hL
  let μ : Measure X := RealRMK.rieszMeasure P
  let ν : Measure X := RealRMK.rieszMeasure Q
  letI : IsFiniteMeasure μ := rieszMeasure_isFiniteMeasure P hC hP
  letI : IsFiniteMeasure ν := rieszMeasure_isFiniteMeasure Q (by linarith) hQ
  refine ⟨μ, ν, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro f
  simpa only [μ, ν, RealRMK.integral_rieszMeasure] using hdiff f

/-- Real representation assembled from the positive parts. The accompanying
finite regular measures dominate the signed measure's variation, allowing the
general regularity-under-domination lemma to establish its regularity. -/
theorem exists_signed_representation {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ g : C_c(X, ℝ), |L g| ≤ C * ‖g.toBoundedContinuousFunction‖) :
    ∃ s : SignedMeasure X, ∃ μ ν : Measure X,
      IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧ μ.Regular ∧ ν.Regular ∧
      s.variation ≤ μ + ν ∧
      ∀ f : C_c(X, ℝ), L f = ∫ᵛ x, f x ∂<•s := by
  obtain ⟨P, Q, hdiff, hP, hQ⟩ := exists_positive_decomposition L hC hL
  let μ : Measure X := RealRMK.rieszMeasure P
  let ν : Measure X := RealRMK.rieszMeasure Q
  letI : IsFiniteMeasure μ := rieszMeasure_isFiniteMeasure P hC hP
  letI : IsFiniteMeasure ν := rieszMeasure_isFiniteMeasure Q (by linarith) hQ
  let s : SignedMeasure X := μ.toSignedMeasure - ν.toSignedMeasure
  refine ⟨s, μ, ν, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · simpa only [s, Measure.variation_toSignedMeasure] using
      (VectorMeasure.variation_sub_le (μ := μ.toSignedMeasure) (ν := ν.toSignedMeasure))
  · intro f
    have hfμ : μ.toSignedMeasure.Integrable f := by
      simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using
        ((map_continuous f).integrable_of_hasCompactSupport f.hasCompactSupport : Integrable f μ)
    have hfν : ν.toSignedMeasure.Integrable f := by
      simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using
        ((map_continuous f).integrable_of_hasCompactSupport f.hasCompactSupport : Integrable f ν)
    rw [show s = μ.toSignedMeasure - ν.toSignedMeasure from rfl,
      VectorMeasure.integral_sub_vectorMeasure hfμ hfν,
      VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure]
    exact (hdiff f).trans (by
      rw [show μ = RealRMK.rieszMeasure P from rfl,
        show ν = RealRMK.rieszMeasure Q from rfl,
        RealRMK.integral_rieszMeasure, RealRMK.integral_rieszMeasure])

#print axioms rieszMeasure_univ_le
#print axioms rieszMeasure_isFiniteMeasure
#print axioms exists_finite_measure_representation
#print axioms exists_signed_representation

end FiniteRMK

end RCA619PositivePart
