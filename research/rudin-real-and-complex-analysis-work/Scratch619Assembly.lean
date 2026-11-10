import Scratch619PositivePart
import Scratch619Uniqueness
import Scratch618Extension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal CompactlySupported

namespace RudinRCA.Chapter06

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X]

/-- A positive measure with a constant complex density of modulus one. -/
def unitComplexMeasure (μ : Measure X) (z : ℂ) : ComplexMeasure X :=
  μ.withDensityᵥ (fun _ ↦ z)

theorem unitComplexMeasure_variation (μ : Measure X) [IsFiniteMeasure μ]
    (z : ℂ) (hz : ‖z‖ = 1) : (unitComplexMeasure μ z).variation = μ := by
  rw [unitComplexMeasure, Measure.variation_withDensityᵥ (integrable_const z)]
  have hn : (fun _ : X ↦ ‖z‖ₑ) = (1 : X → ℝ≥0∞) := by
    funext x
    rw [← ofReal_norm, hz]
    simp
  rw [hn, withDensity_one]

theorem unitComplexMeasure_integral (μ : Measure X) [IsFiniteMeasure μ]
    (z : ℂ) (hz : ‖z‖ = 1) (f : ZeroAtInftyContinuousMap X ℂ) :
    complexIntegral (unitComplexMeasure μ z) f = (∫ x, f x ∂μ) * z := by
  let c := unitComplexMeasure μ z
  have hv : c.variation = μ := unitComplexMeasure_variation μ z hz
  have hi : Integrable (fun _ : X ↦ z) c.variation := by rw [hv]; exact integrable_const z
  have hr : c.variation.withDensityᵥ (fun _ : X ↦ z) = c := by rw [hv]; rfl
  have hf : Integrable (fun x ↦ f x) c.variation :=
    Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
      (ae_of_all _ fun x ↦ f.toBCF.norm_coe_le_norm x)
  calc
    complexIntegral c f = ∫ x, f x * z ∂c.variation :=
      vectorIntegral_eq_polar c (fun _ ↦ z) measurable_const (fun _ ↦ hz) hi hr hf
    _ = (∫ x, f x ∂μ) * z := by rw [hv, integral_mul_const]

private theorem complexIntegral_sub_C0 (a b : ComplexMeasure X)
    (f : ZeroAtInftyContinuousMap X ℂ) :
    complexIntegral (a - b) f = complexIntegral a f - complexIntegral b f := by
  have ha : a.Integrable f := Integrable.of_bound f.continuous.measurable.aestronglyMeasurable
    ‖f‖ (ae_of_all _ fun x ↦ f.toBCF.norm_coe_le_norm x)
  have hb : b.Integrable f := Integrable.of_bound f.continuous.measurable.aestronglyMeasurable
    ‖f‖ (ae_of_all _ fun x ↦ f.toBCF.norm_coe_le_norm x)
  exact VectorMeasure.integral_sub_vectorMeasure ha hb

/-- Inclusion of real compactly supported functions into complex C0. -/
def realCcToComplexC0 : C_c(X, ℝ) →ₗ[ℝ] ZeroAtInftyContinuousMap X ℂ where
  toFun g :=
    { toFun := fun x ↦ (g x : ℂ)
      continuous_toFun := Complex.continuous_ofReal.comp g.continuous
      zero_at_infty' := (g.hasCompactSupport.comp_left (map_zero Complex.ofRealHom)).is_zero_at_infty }
  map_add' f g := by ext x; simp
  map_smul' r f := by ext x; simp

theorem realCcToComplexC0_norm_le (g : C_c(X, ℝ)) :
    ‖realCcToComplexC0 g‖ ≤ ‖g.toBoundedContinuousFunction‖ := by
  change ‖(realCcToComplexC0 g).toBCF‖ ≤ _
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
  intro x
  change ‖(g x : ℂ)‖ ≤ _
  rw [Complex.norm_real]
  exact g.toBoundedContinuousFunction.norm_coe_le_norm x

/-- Rudin 6.19: existence, uniqueness, and exact norm, for every locally compact
Hausdorff space. No sigma-compactness, normality, or countability is assumed. -/
theorem theorem_6_19 (Φ : ZeroAtInftyContinuousMap X ℂ →L[ℂ] ℂ) :
    ∃ c : ComplexMeasure X, IsRegularComplexMeasure c ∧
      (∀ f, Φ f = complexIntegral c f) ∧ ‖Φ‖ = c.variation.real univ ∧
      ∀ d : ComplexMeasure X, IsRegularComplexMeasure d →
        (∀ f, Φ f = complexIntegral d f) → d = c := by
  let J := realCcToComplexC0 (X := X)
  let Lr : C_c(X, ℝ) →ₗ[ℝ] ℝ :=
    Complex.reCLM.toLinearMap.comp ((Φ.restrictScalars ℝ).toLinearMap.comp J)
  let Li : C_c(X, ℝ) →ₗ[ℝ] ℝ :=
    Complex.imCLM.toLinearMap.comp ((Φ.restrictScalars ℝ).toLinearMap.comp J)
  have hLr (g : C_c(X, ℝ)) : |Lr g| ≤ ‖Φ‖ * ‖g.toBoundedContinuousFunction‖ := by
    change |(Φ (J g)).re| ≤ _
    exact (Complex.abs_re_le_norm _).trans ((Φ.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (realCcToComplexC0_norm_le g) (norm_nonneg Φ)))
  have hLi (g : C_c(X, ℝ)) : |Li g| ≤ ‖Φ‖ * ‖g.toBoundedContinuousFunction‖ := by
    change |(Φ (J g)).im| ≤ _
    exact (Complex.abs_im_le_norm _).trans ((Φ.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (realCcToComplexC0_norm_le g) (norm_nonneg Φ)))
  obtain ⟨μr, νr, hμrf, hνrf, hμrr, hνrr, hR⟩ :=
    RCA619PositivePart.exists_finite_measure_representation Lr (norm_nonneg Φ) hLr
  obtain ⟨μi, νi, hμif, hνif, hμir, hνir, hI⟩ :=
    RCA619PositivePart.exists_finite_measure_representation Li (norm_nonneg Φ) hLi
  letI : IsFiniteMeasure μr := hμrf
  letI : IsFiniteMeasure νr := hνrf
  letI : IsFiniteMeasure μi := hμif
  letI : IsFiniteMeasure νi := hνif
  letI : μr.Regular := hμrr
  letI : νr.Regular := hνrr
  letI : μi.Regular := hμir
  letI : νi.Regular := hνir
  let a := unitComplexMeasure μr 1
  let b := unitComplexMeasure νr 1
  let d := unitComplexMeasure μi Complex.I
  let e := unitComplexMeasure νi Complex.I
  let c := (a - b) + (d - e)
  have ha : a.variation = μr := unitComplexMeasure_variation μr 1 (by simp)
  have hb : b.variation = νr := unitComplexMeasure_variation νr 1 (by simp)
  have hd : d.variation = μi := unitComplexMeasure_variation μi Complex.I (by simp)
  have he : e.variation = νi := unitComplexMeasure_variation νi Complex.I (by simp)
  have hdom : c.variation ≤ (μr + νr) + (μi + νi) := by
    calc
      c.variation ≤ (a - b).variation + (d - e).variation := VectorMeasure.variation_add_le
      _ ≤ (a.variation + b.variation) + (d.variation + e.variation) :=
        add_le_add VectorMeasure.variation_sub_le VectorMeasure.variation_sub_le
      _ = _ := by rw [ha, hb, hd, he]
  letI : c.variation.Regular := regular_of_le_finite_regular ((μr + νr) + (μi + νi)) _ hdom
  obtain ⟨Ψ, hΨ, _⟩ := theorem_6_18_functional c
  have hreal (g : C_c(X, ℝ)) : Φ (J g) = Ψ (J g) := by
    rw [hΨ]
    change Φ (J g) = complexIntegral ((a - b) + (d - e)) (J g)
    rw [theorem_6_18_add (a - b) (d - e) (J g) (J g).continuous.measurable
      ‖J g‖ (fun x ↦ (J g).toBCF.norm_coe_le_norm x),
      complexIntegral_sub_C0, complexIntegral_sub_C0]
    rw [show a = unitComplexMeasure μr 1 from rfl,
      show b = unitComplexMeasure νr 1 from rfl,
      show d = unitComplexMeasure μi Complex.I from rfl,
      show e = unitComplexMeasure νi Complex.I from rfl,
      unitComplexMeasure_integral μr 1 (by simp), unitComplexMeasure_integral νr 1 (by simp),
      unitComplexMeasure_integral μi Complex.I (by simp),
      unitComplexMeasure_integral νi Complex.I (by simp)]
    have hexp : Φ (J g) = (Lr g : ℂ) + (Li g : ℂ) * Complex.I :=
      (Complex.re_add_im (Φ (J g))).symm
    rw [hexp, hR, hI]
    have hJ : (J g : X → ℂ) = fun x ↦ (g x : ℂ) := rfl
    simp only [hJ, integral_ofReal, mul_one, Complex.ofReal_sub, sub_mul]
  have hΦΨ : Φ = Ψ := by
    apply DFunLike.ext'
    apply Φ.continuous.ext_on (RCA618.dense_compactSupport X) Ψ.continuous
    intro f hf
    let fr : C_c(X, ℝ) :=
      ⟨⟨fun x ↦ (f x).re, Complex.continuous_re.comp f.continuous⟩,
        hf.comp_left (by simp)⟩
    let fi : C_c(X, ℝ) :=
      ⟨⟨fun x ↦ (f x).im, Complex.continuous_im.comp f.continuous⟩,
        hf.comp_left (by simp)⟩
    have hsplit : f = J fr + Complex.I • J fi := by
      ext x
      change f x = ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ)
      simpa only [mul_comm] using (Complex.re_add_im (f x)).symm
    rw [hsplit, map_add, map_smul, map_add, map_smul, hreal fr, hreal fi]
  have hrep (f) : Φ f = complexIntegral c f := by rw [hΦΨ]; exact hΨ f
  refine ⟨c, (show IsRegularComplexMeasure c from (inferInstance : c.variation.Regular)),
    hrep, theorem_6_19_norm c Φ hrep, ?_⟩
  intro d hd hrepd
  letI : d.variation.Regular := hd
  exact theorem_6_19_unique d c (fun f ↦ (hrepd f).symm.trans (hrep f))

#print axioms unitComplexMeasure_variation
#print axioms unitComplexMeasure_integral
#print axioms realCcToComplexC0_norm_le
#print axioms theorem_6_19
end RudinRCA.Chapter06
