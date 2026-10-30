import RudinRCA.Chapter06
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal MeasureTheory

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

/-- Rudin 6.9: strict bounds are pointwise, not only almost everywhere. -/
theorem lemma_6_9 (μ : Measure X) [SigmaFinite μ] :
    ∃ w : X → ℝ, Measurable w ∧ Integrable w μ ∧ ∀ x, 0 < w x ∧ w x < 1 := by
  obtain ⟨g, hgpos, hgmeas, hgint⟩ :=
    exists_pos_lintegral_lt_of_sigmaFinite μ (ε := ∞) (by simp)
  have hgi : Integrable (fun x ↦ (g x : ℝ)) μ := by
    simpa using integrable_toReal_of_lintegral_ne_top
      hgmeas.coe_nnreal_ennreal.aemeasurable hgint.ne
  refine ⟨fun x ↦ min (g x : ℝ) (1 / 2), hgmeas.coe_nnreal_real.min measurable_const, ?_, ?_⟩
  · apply hgi.mono' (hgmeas.coe_nnreal_real.min measurable_const).aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (g x).coe_nonneg (by norm_num))]
    exact min_le_left _ _
  · intro x
    exact ⟨lt_min (hgpos x) (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩

/-- The consequence following 6.9: a finite measure with exactly the same null sets. -/
theorem lemma_6_9_equivalent_finite_measure (μ : Measure X) [SigmaFinite μ] :
    ∃ ν : Measure X, IsFiniteMeasure ν ∧ ∀ E, ν E = 0 ↔ μ E = 0 := by
  obtain ⟨w, hwm, hwi, hw⟩ := lemma_6_9 μ
  let ν := μ.withDensity (fun x ↦ ENNReal.ofReal (w x))
  have hfinite : IsFiniteMeasure ν := isFiniteMeasure_withDensity (by
    rw [← ofReal_integral_eq_lintegral_ofReal hwi (ae_of_all μ fun x ↦ (hw x).1.le)]
    exact ENNReal.ofReal_ne_top)
  have hac : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have hrev : μ ≪ ν := withDensity_absolutelyContinuous' hwm.ennreal_ofReal.aemeasurable
    (ae_of_all μ fun x ↦ ENNReal.ofReal_ne_zero_iff.mpr (hw x).1)
  exact ⟨ν, hfinite, fun E ↦ ⟨fun hz ↦ hrev hz, fun hz ↦ hac hz⟩⟩

private theorem complexDensity_ac (μ : Measure X) {f : X → ℂ} (hf : Integrable f μ) :
    μ.withDensityᵥ f ≪ᵥ μ.toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro s hs hzero
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hzero
  rw [withDensityᵥ_apply hf hs, Measure.restrict_zero_set hzero, integral_zero_measure]

private theorem complex_rn_measurable (c : ComplexMeasure X) (μ : Measure X) :
    Measurable (c.rnDeriv μ) :=
  Complex.equivRealProdCLM.symm.continuous.measurable.comp
    ((c.re.measurable_rnDeriv μ).prodMk (c.im.measurable_rnDeriv μ))

/-- Complex Radon–Nikodym reconstruction, used in Rudin 6.10 and 6.12. -/
theorem complex_rn_reconstruction (c : ComplexMeasure X) (μ : Measure X) [SigmaFinite μ]
    (hc : c ≪ᵥ μ.toENNRealVectorMeasure) : μ.withDensityᵥ (c.rnDeriv μ) = c := by
  obtain ⟨hr, hi⟩ := (c.absolutelyContinuous_ennreal_iff μ.toENNRealVectorMeasure).mp hc
  have hfr := SignedMeasure.withDensityᵥ_rnDeriv_eq c.re μ hr
  have hfi := SignedMeasure.withDensityᵥ_rnDeriv_eq c.im μ hi
  ext s hs
  apply Complex.ext
  · rw [withDensityᵥ_apply (c.integrable_rnDeriv μ) hs,
      ← RCLike.re_eq_complex_re, ← integral_re (c.integrable_rnDeriv μ).integrableOn]
    change (∫ x in s, c.re.rnDeriv μ x ∂μ) = c.re s
    rw [← withDensityᵥ_apply (c.re.integrable_rnDeriv μ) hs, hfr]
  · rw [withDensityᵥ_apply (c.integrable_rnDeriv μ) hs,
      ← RCLike.im_eq_complex_im, ← integral_im (c.integrable_rnDeriv μ).integrableOn]
    change (∫ x in s, c.im.rnDeriv μ x ∂μ) = c.im s
    rw [← withDensityᵥ_apply (c.im.integrable_rnDeriv μ) hs, hfi]

private theorem complex_singularPart_singular (c : ComplexMeasure X) (μ : Measure X) :
    c.singularPart μ ⟂ᵥ μ.toENNRealVectorMeasure := by
  obtain ⟨A, hA, hr, hμA⟩ := c.re.mutuallySingular_singularPart μ
  obtain ⟨B, hB, hi, hμB⟩ := c.im.mutuallySingular_singularPart μ
  apply VectorMeasure.MutuallySingular.mk (A ∩ B) (hA.inter hB)
  · intro E hE _
    change Complex.mk (c.re.singularPart μ E) (c.im.singularPart μ E) = 0
    rw [hr E (hE.trans inter_subset_left), hi E (hE.trans inter_subset_right)]
    rfl
  · intro E hE hEm
    rw [Measure.toENNRealVectorMeasure_apply_measurable hEm]
    have hAz : μ Aᶜ = 0 := by
      simpa only [Measure.toENNRealVectorMeasure_apply_measurable hA.compl] using
        hμA Aᶜ Subset.rfl
    have hBz : μ Bᶜ = 0 := by
      simpa only [Measure.toENNRealVectorMeasure_apply_measurable hB.compl] using
        hμB Bᶜ Subset.rfl
    apply measure_mono_null hE
    rw [compl_inter]
    exact measure_union_null hAz hBz

private theorem complex_ac_singular_zero (c : ComplexMeasure X) (μ : Measure X)
    (hac : c ≪ᵥ μ.toENNRealVectorMeasure) (hsing : c ⟂ᵥ μ.toENNRealVectorMeasure) :
    c = 0 := eq_zero_of_ac_of_singular hac hsing

/-- The unique pair in the complex Lebesgue decomposition of Rudin 6.10(a). -/
theorem theorem_6_10_lebesgue (c : ComplexMeasure X) (μ : Measure X) [SigmaFinite μ] :
    ∃! d : ComplexMeasure X × ComplexMeasure X,
      d.1 + d.2 = c ∧ d.1 ≪ᵥ μ.toENNRealVectorMeasure ∧
        d.2 ⟂ᵥ μ.toENNRealVectorMeasure := by
  letI : c.HaveLebesgueDecomposition μ := ⟨inferInstance, inferInstance⟩
  let a := μ.withDensityᵥ (c.rnDeriv μ)
  let s := c.singularPart μ
  have ha : a ≪ᵥ μ.toENNRealVectorMeasure := complexDensity_ac μ (c.integrable_rnDeriv μ)
  have hs : s ⟂ᵥ μ.toENNRealVectorMeasure := complex_singularPart_singular c μ
  have heq : a + s = c := by
    rw [add_comm]
    exact ComplexMeasure.singularPart_add_withDensity_rnDeriv_eq (c := c) (μ := μ)
  refine ⟨(a, s), ⟨heq, ha, hs⟩, ?_⟩
  rintro ⟨a', s'⟩ ⟨heq', ha', hs'⟩
  have hdiff : a' - a = s - s' := by
    have := heq'.trans heq.symm
    dsimp at this
    exact sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm] using this)
  have hz : a' - a = 0 := complex_ac_singular_zero (a' - a) μ
    (ha'.sub ha) (by rw [hdiff]; exact hs.add_left hs'.neg_left)
  have haa : a' = a := sub_eq_zero.mp hz
  apply Prod.ext haa
  dsimp at heq'
  rw [haa, heq.symm] at heq'
  exact add_left_cancel heq'

/-- The positive finite clause of 6.10(a), stated in the positive-measure type. -/
theorem theorem_6_10_positive (ρ μ : Measure X) [IsFiniteMeasure ρ] [SigmaFinite μ] :
    ∃! d : Measure X × Measure X,
      IsFiniteMeasure d.1 ∧ IsFiniteMeasure d.2 ∧ d.1 + d.2 = ρ ∧
        d.1 ≪ μ ∧ d.2.MutuallySingular μ := by
  refine ⟨(μ.withDensity (ρ.rnDeriv μ), ρ.singularPart μ),
    ⟨inferInstance, inferInstance, ρ.rnDeriv_add_singularPart μ,
      withDensity_absolutelyContinuous _ _, ρ.mutuallySingular_singularPart μ⟩, ?_⟩
  rintro ⟨a, s⟩ ⟨ha, hs, heq, hac, hsing⟩
  letI : IsFiniteMeasure a := ha
  have haeq : μ.withDensity (a.rnDeriv μ) = a := Measure.withDensity_rnDeriv_eq a μ hac
  have hdecomp : ρ = s + μ.withDensity (a.rnDeriv μ) := by
    rw [haeq, add_comm]
    exact heq.symm
  apply Prod.ext
  · rw [← haeq]
    exact Measure.eq_withDensity_rnDeriv (a.measurable_rnDeriv μ) hsing hdecomp
  · exact Measure.eq_singularPart (a.measurable_rnDeriv μ) hsing hdecomp

/-- The Radon–Nikodym part of 6.10, including uniqueness modulo null sets. -/
theorem theorem_6_10_radon_nikodym (c : ComplexMeasure X) (μ : Measure X) [SigmaFinite μ]
    (hc : c ≪ᵥ μ.toENNRealVectorMeasure) :
    ∃ h : X → ℂ, Measurable h ∧ Integrable h μ ∧
      (∀ E, MeasurableSet E → c E = ∫ x in E, h x ∂μ) ∧
      ∀ g : X → ℂ, Integrable g μ →
        (∀ E, MeasurableSet E → c E = ∫ x in E, g x ∂μ) → g =ᵐ[μ] h := by
  refine ⟨c.rnDeriv μ, complex_rn_measurable c μ, c.integrable_rnDeriv μ, ?_, ?_⟩
  · intro E hE
    calc
      c E = (μ.withDensityᵥ (c.rnDeriv μ)) E :=
        congrArg (fun v : ComplexMeasure X ↦ v E) (complex_rn_reconstruction c μ hc).symm
      _ = ∫ x in E, c.rnDeriv μ x ∂μ := withDensityᵥ_apply (c.integrable_rnDeriv μ) hE
  · intro g hg hge
    apply hg.ae_eq_of_withDensityᵥ_eq (c.integrable_rnDeriv μ)
    rw [complex_rn_reconstruction c μ hc]
    ext E hE
    rw [withDensityᵥ_apply hg hE, ← hge E hE]

private theorem finite_measure_uniform_ac (ν μ : Measure X) [IsFiniteMeasure ν]
    (hac : ∀ E, MeasurableSet E → μ E = 0 → ν E = 0)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ δ : ℝ≥0∞, δ ≠ 0 ∧ ∀ E, MeasurableSet E → μ E < δ → ν E < ε := by
  classical
  by_contra h
  push_neg at h
  have hseq : ∀ n : ℕ, ∃ E : Set X, MeasurableSet E ∧
      μ E < (2 : ℝ≥0∞)⁻¹ ^ n ∧ ε ≤ ν E := by
    intro n
    exact h ((2 : ℝ≥0∞)⁻¹ ^ n) (pow_ne_zero _ (by simp))
  choose E hEm hEμ hEν using hseq
  let A : ℕ → Set X := fun n ↦ ⋃ k ≥ n, E k
  have hAm : ∀ n, MeasurableSet (A n) := fun n ↦ .iUnion fun k ↦ .iUnion fun _ ↦ hEm k
  have hanti : Antitone A := by
    intro n m hnm x hx
    obtain ⟨k, hk, hx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨k, hnm.trans hk, hx⟩
  have hμzero : μ (⋂ n, A n) = 0 := by
    have hs : ∑' n, μ (E n) ≠ ∞ :=
      ne_top_of_le_ne_top (by
        simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using
          (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ ∞))
        (ENNReal.tsum_le_tsum fun n ↦ (hEμ n).le)
    simpa only [limsup_eq_iInf_iSup_of_nat, iSup_eq_iUnion, iInf_eq_iInter, A] using
      (measure_limsup_atTop_eq_zero (μ := μ) hs)
  have hνzero := hac (⋂ n, A n) (.iInter hAm) hμzero
  have heps : ε ≤ ν (⋂ n, A n) := by
    rw [hanti.measure_iInter (fun n ↦ (hAm n).nullMeasurableSet)
      ⟨0, measure_ne_top ν (A 0)⟩]
    apply le_iInf
    intro n
    exact (hEν n).trans (measure_mono (fun x hx ↦ mem_iUnion₂.mpr ⟨n, le_rfl, hx⟩))
  exact hε (le_zero_iff.mp (hνzero ▸ heps))

/-- Rudin 6.11. ENNReal epsilon/delta is equivalent to the usual positive-real form;
the positive reference measure is arbitrary and need not be sigma-finite. -/
theorem theorem_6_11_of_finite_variation (c : ComplexMeasure X)
    [IsFiniteMeasure c.variation] (μ : Measure X) :
    c ≪ᵥ μ.toENNRealVectorMeasure ↔
      ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
        ∀ E, MeasurableSet E → μ E < δ → ‖c E‖ₑ < ε := by
  constructor
  · intro hac ε hε
    have hvac : ∀ E, MeasurableSet E → μ E = 0 → c.variation E = 0 := by
      intro E hE hz
      apply (VectorMeasure.variation_apply_eq_zero (μ := c) hE).mpr
      intro F hFE hF
      apply hac
      rw [Measure.toENNRealVectorMeasure_apply_measurable hF]
      exact measure_mono_null hFE hz
    obtain ⟨δ, hδ, hbound⟩ := finite_measure_uniform_ac c.variation μ hvac ε hε
    refine ⟨δ, hδ, fun E hE hμE ↦ ?_⟩
    exact (c.enorm_measure_le_variation E).trans_lt (hbound E hE hμE)
  · intro h
    apply VectorMeasure.AbsolutelyContinuous.mk
    intro E hE hz
    rw [Measure.toENNRealVectorMeasure_apply_measurable hE] at hz
    by_contra hc
    obtain ⟨δ, hδ, hbound⟩ := h ‖c E‖ₑ (by simpa using hc)
    exact (lt_irrefl ‖c E‖ₑ) (hbound E hE (hz ▸ bot_lt_iff_ne_bot.mpr hδ))

/-- The literal positive-real epsilon/delta formulation of Rudin 6.11. -/
theorem theorem_6_11_real_of_finite_variation (c : ComplexMeasure X)
    [IsFiniteMeasure c.variation] (μ : Measure X) :
    c ≪ᵥ μ.toENNRealVectorMeasure ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E, MeasurableSet E → μ E < ENNReal.ofReal δ → ‖c E‖ < ε := by
  constructor
  · intro hac ε hε
    obtain ⟨δ, hδ, hbound⟩ := (theorem_6_11_of_finite_variation c μ).mp hac
      (ENNReal.ofReal ε) (ENNReal.ofReal_ne_zero_iff.mpr hε)
    let d := min δ 1
    have hd0 : d ≠ 0 := ne_of_gt (lt_min (bot_lt_iff_ne_bot.mpr hδ) zero_lt_one)
    have hdt : d ≠ ∞ := ne_top_of_le_ne_top (by simp) (min_le_right _ _)
    refine ⟨d.toReal, ENNReal.toReal_pos hd0 hdt, ?_⟩
    intro E hE hμE
    rw [ENNReal.ofReal_toReal hdt] at hμE
    have hb := hbound E hE (hμE.trans_le (min_le_left _ _))
    rw [← ofReal_norm] at hb
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp hb
  · intro h
    apply VectorMeasure.AbsolutelyContinuous.mk
    intro E hE hz
    rw [Measure.toENNRealVectorMeasure_apply_measurable hE] at hz
    by_contra hc
    obtain ⟨δ, hδ, hbound⟩ := h ‖c E‖ (norm_pos_iff.mpr hc)
    exact (lt_irrefl ‖c E‖) (hbound E hE (hz ▸ ENNReal.ofReal_pos.mpr hδ))

/-- Rudin 6.13 as equality of positive measures; applies without sigma-finiteness. -/
theorem theorem_6_13 (μ : Measure X) {g : X → ℂ} (hg : Integrable g μ) :
    (μ.withDensityᵥ g).variation = μ.withDensity (fun x ↦ ‖g x‖ₑ) :=
  Measure.variation_withDensityᵥ hg

/-- The setwise real-integral formula printed in 6.13. -/
theorem theorem_6_13_apply (μ : Measure X) {g : X → ℂ} (hg : Integrable g μ)
    (E : Set X) (hE : MeasurableSet E) :
    (μ.withDensityᵥ g).variation.real E = ∫ x in E, ‖g x‖ ∂μ := by
  rw [theorem_6_13 μ hg, measureReal_def, withDensity_apply _ hE]
  exact (integral_norm_eq_lintegral_enorm hg.aestronglyMeasurable.restrict).symm

/-- Polar decomposition; the finite-variation instance is discharged by 6.4 at integration. -/
theorem theorem_6_12_of_finite_variation (c : ComplexMeasure X) [IsFiniteMeasure c.variation] :
    ∃ h : X → ℂ, Measurable h ∧ (∀ x, ‖h x‖ = 1) ∧
      Integrable h c.variation ∧ c.variation.withDensityᵥ h = c := by
  classical
  let f := c.rnDeriv c.variation
  have hf : Measurable f := complex_rn_measurable c c.variation
  have hfi : Integrable f c.variation := c.integrable_rnDeriv c.variation
  have hrep : c.variation.withDensityᵥ f = c :=
    complex_rn_reconstruction c c.variation c.absolutelyContinuous
  have heq : c.variation.withDensity (fun x ↦ ‖f x‖ₑ) = c.variation.withDensity 1 := by
    rw [withDensity_one, ← theorem_6_13 c.variation hfi, hrep]
  have heqae : (fun x ↦ ‖f x‖ₑ) =ᵐ[c.variation] (1 : X → ℝ≥0∞) :=
    (withDensity_eq_iff_of_sigmaFinite hf.enorm.aemeasurable measurable_const.aemeasurable).mp heq
  have hnorm : ∀ᵐ x ∂c.variation, ‖f x‖ = 1 := by
    filter_upwards [heqae] with x hx
    have hx' := congrArg ENNReal.toReal hx
    simpa using hx'
  let h : X → ℂ := fun x ↦ if ‖f x‖ = 1 then f x else 1
  have hmeas : Measurable h := Measurable.ite
    (measurableSet_eq_fun hf.norm measurable_const) hf measurable_const
  have hhae : h =ᵐ[c.variation] f := by
    filter_upwards [hnorm] with x hx
    simp [h, hx]
  refine ⟨h, hmeas, ?_, hfi.congr hhae.symm, ?_⟩
  · intro x
    by_cases hx : ‖f x‖ = 1 <;> simp [h, hx]
  · rw [WithDensityᵥEq.congr_ae hhae, hrep]

/-- Rudin 6.11, with finite variation supplied by the proved theorem 6.4. -/
theorem theorem_6_11 (c : ComplexMeasure X) (μ : Measure X) :
    c ≪ᵥ μ.toENNRealVectorMeasure ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E, MeasurableSet E → μ E < ENNReal.ofReal δ → ‖c E‖ < ε :=
  theorem_6_11_real_of_finite_variation c μ

/-- Rudin 6.12, for every complex measure, with modulus one everywhere. -/
theorem theorem_6_12 (c : ComplexMeasure X) :
    ∃ h : X → ℂ, Measurable h ∧ (∀ x, ‖h x‖ = 1) ∧
      Integrable h c.variation ∧ c.variation.withDensityᵥ h = c :=
  theorem_6_12_of_finite_variation c

/-- Rudin 6.14: the partition realizes the canonical positive/negative variations. -/
theorem theorem_6_14 (s : SignedMeasure X) :
    ∃ A B : Set X, MeasurableSet A ∧ MeasurableSet B ∧ A ∪ B = univ ∧ Disjoint A B ∧
      ∀ E, MeasurableSet E →
        s.toJordanDecomposition.posPart.real E = s (E ∩ A) ∧
        s.toJordanDecomposition.negPart.real E = -s (E ∩ B) := by
  obtain ⟨A, hA, hpos, hneg, hP, hN⟩ := s.toJordanDecomposition_spec
  refine ⟨A, Aᶜ, hA, hA.compl, union_compl_self A, disjoint_compl_right, ?_⟩
  intro E hE
  rw [hP, hN, s.toMeasureOfZeroLE_real_apply hpos hA hE,
    s.toMeasureOfLEZero_real_apply hneg hA.compl hE]
  simp [inter_comm]

/-- The minimum property in the corollary to 6.14. -/
theorem theorem_6_14_minimal (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : SignedMeasure X) (hs : s = μ.toSignedMeasure - ν.toSignedMeasure) :
    s.toJordanDecomposition.posPart ≤ μ ∧ s.toJordanDecomposition.negPart ≤ ν := by
  rw [hs, Measure.toJordanDecomposition_toSignedMeasure_sub]
  exact ⟨Measure.sub_le, Measure.sub_le⟩

/-- Rudin 6.15: the integral pairing gives a bounded functional, with the Hölder norm bound. -/
theorem theorem_6_15 (μ : Measure X) (p q : ℝ≥0∞) [ENNReal.HolderConjugate p q]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (g : Lp ℂ q μ) :
    ∃ Φ : Lp ℂ p μ →L[ℂ] ℂ,
      (∀ f, Φ f = ∫ x, f x * g x ∂μ) ∧ ‖Φ‖ ≤ ‖g‖ := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  let Φ := B.lpPairing μ q p g
  refine ⟨Φ, ?_, ?_⟩
  · intro f
    simpa only [B, ContinuousLinearMap.mul_apply', mul_comm] using
      B.lpPairing_eq_integral g f
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
    intro f
    have hvalue : Φ f = L1.integral (B.holder 1 g f) := by
      change L1.integralCLM' ℂ (B.holder 1 g f) = L1.integral (B.holder 1 g f)
      exact (L1.integral_eq' ℂ _).symm
    rw [hvalue]
    calc
      ‖L1.integral (B.holder 1 g f)‖ ≤ ‖B.holder 1 g f‖ := L1.norm_integral_le _
      _ ≤ ‖B‖ * ‖g‖ * ‖f‖ := B.norm_holder_apply_apply_le g f
      _ ≤ 1 * ‖g‖ * ‖f‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℂ ℂ) (norm_nonneg g))
          (norm_nonneg f)
      _ = ‖g‖ * ‖f‖ := by rw [one_mul]

/-- The standard vector-measure integral specialized to complex multiplication.
The remaining 6.18 obligation is to identify this with Rudin's polar-density definition. -/
def complexIntegral (c : ComplexMeasure X) (f : X → ℂ) : ℂ :=
  ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; c]

/-- The indicator identity in 6.18, for the standard complex vector integral. -/
theorem theorem_6_18_indicator (c : ComplexMeasure X) [IsFiniteMeasure c.variation]
    (E : Set X) (hE : MeasurableSet E) :
    complexIntegral c (E.indicator (fun _ ↦ (1 : ℂ))) = c E := by
  simpa only [complexIntegral, ContinuousLinearMap.mul_apply', one_mul] using
    (VectorMeasure.integral_indicator_const (μ := c) (B := ContinuousLinearMap.mul ℝ ℂ) 1 hE)

/-- The measure-addition identity in 6.18 for every bounded measurable function. -/
theorem theorem_6_18_add (c d : ComplexMeasure X)
    [IsFiniteMeasure c.variation] [IsFiniteMeasure d.variation]
    (f : X → ℂ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    complexIntegral (c + d) f = complexIntegral c f + complexIntegral d f := by
  have hc : c.Integrable f := Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have hd : d.Integrable f := Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  exact VectorMeasure.integral_add_vectorMeasure hc hd

/-- The total-variation bound underlying 6.18's bounded-functional assertion. -/
theorem theorem_6_18_bound (c : ComplexMeasure X) [IsFiniteMeasure c.variation]
    (f : X → ℂ) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖f x‖ ≤ C) :
    ‖complexIntegral c f‖ ≤ C * c.variation.real univ := by
  calc
    ‖complexIntegral c f‖ ≤
        C * ‖ContinuousLinearMap.mul ℝ ℂ‖ * c.variation.real univ :=
      VectorMeasure.norm_integral_le_of_norm_le_const (ae_of_all _ hC)
    _ ≤ C * 1 * c.variation.real univ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_mul_le ℝ ℂ) hC0)
        ENNReal.toReal_nonneg
    _ = C * c.variation.real univ := by rw [mul_one]

/-- The bounded complex functional in 6.18, expressed using the printed polar integral. -/
theorem theorem_6_18_polar_functional [TopologicalSpace X] [BorelSpace X]
    (c : ComplexMeasure X) (h : X → ℂ) (hm : Measurable h) (hn : ∀ x, ‖h x‖ = 1) :
    ∃ Φ : ZeroAtInftyContinuousMap X ℂ →L[ℂ] ℂ,
      (∀ f, Φ f = ∫ x, f x * h x ∂c.variation) ∧ ‖Φ‖ ≤ c.variation.real univ := by
  have hnorm (f : ZeroAtInftyContinuousMap X ℂ) (x : X) : ‖f x * h x‖ ≤ ‖f‖ := by
    rw [norm_mul, hn, mul_one]
    exact f.toBCF.norm_coe_le_norm x
  have hi (f : ZeroAtInftyContinuousMap X ℂ) :
      Integrable (fun x ↦ f x * h x) c.variation :=
    Integrable.of_bound (f.continuous.measurable.mul hm).aestronglyMeasurable ‖f‖
      (ae_of_all _ (hnorm f))
  let L : ZeroAtInftyContinuousMap X ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ ∫ x, f x * h x ∂c.variation
      map_add' := by
        intro f g
        change (∫ x, (f x + g x) * h x ∂c.variation) = _
        simp_rw [add_mul]
        exact integral_add (hi f) (hi g)
      map_smul' := by
        intro z f
        change (∫ x, (z * f x) * h x ∂c.variation) = z * _
        simp_rw [mul_assoc]
        exact integral_const_mul z _ }
  have hbound (f : ZeroAtInftyContinuousMap X ℂ) :
      ‖L f‖ ≤ c.variation.real univ * ‖f‖ := by
    change ‖∫ x, f x * h x ∂c.variation‖ ≤ _
    simpa only [mul_comm] using
      (norm_integral_le_of_norm_le_const (ae_of_all c.variation (hnorm f)))
  exact ⟨L.mkContinuous (c.variation.real univ) hbound, fun _ ↦ rfl,
    L.mkContinuous_norm_le ENNReal.toReal_nonneg hbound⟩

end RudinRCA.Chapter06

#print axioms RudinRCA.Chapter06.lemma_6_9
#print axioms RudinRCA.Chapter06.lemma_6_9_equivalent_finite_measure
#print axioms RudinRCA.Chapter06.complex_rn_reconstruction
#print axioms RudinRCA.Chapter06.theorem_6_10_lebesgue
#print axioms RudinRCA.Chapter06.theorem_6_10_positive
#print axioms RudinRCA.Chapter06.theorem_6_10_radon_nikodym
#print axioms RudinRCA.Chapter06.theorem_6_11_of_finite_variation
#print axioms RudinRCA.Chapter06.theorem_6_11_real_of_finite_variation
#print axioms RudinRCA.Chapter06.theorem_6_11
#print axioms RudinRCA.Chapter06.theorem_6_12_of_finite_variation
#print axioms RudinRCA.Chapter06.theorem_6_12
#print axioms RudinRCA.Chapter06.theorem_6_13
#print axioms RudinRCA.Chapter06.theorem_6_13_apply
#print axioms RudinRCA.Chapter06.theorem_6_14
#print axioms RudinRCA.Chapter06.theorem_6_14_minimal
#print axioms RudinRCA.Chapter06.theorem_6_15
#print axioms RudinRCA.Chapter06.theorem_6_18_indicator
#print axioms RudinRCA.Chapter06.theorem_6_18_add
#print axioms RudinRCA.Chapter06.theorem_6_18_bound
#print axioms RudinRCA.Chapter06.theorem_6_18_polar_functional
