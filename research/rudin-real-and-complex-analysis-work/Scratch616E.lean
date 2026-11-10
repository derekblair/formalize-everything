import Scratch616
import Scratch616D
import RudinRCA.Chapter06
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Mul

/-!
Finite-measure assembly of Rudin 6.16, plus uniqueness for sigma-finite measures.
The sigma-finite existence reduction remains a separate required step.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

theorem integral_indicatorConstLp_mul (μ : Measure X) (p : ℝ≥0∞)
    {E : Set X} (hE : MeasurableSet E) (hμE : μ E ≠ ∞) (g : X → ℂ) :
    (∫ x, indicatorConstLp p hE hμE (1 : ℂ) x * g x ∂μ) = ∫ x in E, g x ∂μ := by
  have hfun : (fun x => indicatorConstLp p hE hμE (1 : ℂ) x * g x) =ᵐ[μ]
      E.indicator g := by
    filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hE) (hμs := hμE)
      (c := (1 : ℂ))] with x hx
    rw [hx]
    by_cases hxE : x ∈ E <;> simp [hxE]
  rw [integral_congr_ae hfun, integral_indicator hE]

/-- Injectivity of the bilinear Lp–Lq integral pairing, including q = ∞. -/
theorem lp_integral_pairing_unique (μ : Measure X) [SigmaFinite μ]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (g h : Lp ℂ q μ)
    (heq : ∀ f : Lp ℂ p μ, (∫ x, f x * g x ∂μ) = ∫ x, f x * h x ∂μ) : g = h := by
  have hint : ∀ k : Lp ℂ q μ, ∀ E, MeasurableSet E → μ E < ∞ → IntegrableOn k E μ := by
    intro k E hE hμE
    letI : IsFiniteMeasure (μ.restrict E) := ⟨by simpa using hμE⟩
    exact ((Lp.memLp k).restrict E).integrable (Fact.out : 1 ≤ q)
  apply Lp.ext
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (hint g) (hint h)
  intro E hE hμE
  have ht := heq (indicatorConstLp p hE hμE.ne (1 : ℂ))
  simpa only [integral_indicatorConstLp_mul μ p hE hμE.ne] using ht

variable (μ : Measure X) [IsFiniteMeasure μ]
variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

/-- Once the RN density lies in Lq, density of simple functions extends the
identity from indicators to every Lp class. -/
theorem lpFunctional_eq_of_indicator (hp : p ≠ ∞)
    (Φ : Lp ℂ p μ →L[ℂ] ℂ) (G : Lp ℂ q μ)
    (hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) = ∫ x in E, G x ∂μ) :
    ∀ f : Lp ℂ p μ, Φ f = ∫ x, f x * G x ∂μ := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  let Ψ : Lp ℂ p μ →L[ℂ] ℂ := B.lpPairing μ q p G
  have hΨ : ∀ f, Ψ f = ∫ x, f x * G x ∂μ := by
    intro f
    simpa only [Ψ, B, ContinuousLinearMap.mul_apply', mul_comm] using
      B.lpPairing_eq_integral G f
  have hGint : Integrable G μ := (Lp.memLp G).integrable (Fact.out : 1 ≤ q)
  have hsimple : (fun f : Lp.simpleFunc ℂ p μ => Φ (f : Lp ℂ p μ)) =
      (fun f : Lp.simpleFunc ℂ p μ => Ψ (f : Lp ℂ p μ)) := by
    funext f
    let s := Lp.simpleFunc.toSimpleFunc f
    have hs : (s.memLp_of_isFiniteMeasure p μ).toLp s = (f : Lp ℂ p μ) := by
      apply Lp.ext
      exact (MemLp.coeFn_toLp (s.memLp_of_isFiniteMeasure p μ)).trans
        (Lp.simpleFunc.toSimpleFunc_eq_toFun f)
    have h := lpFunctional_eq_simple_of_indicator μ p Φ hGint hind s
    rw [hs] at h
    rw [h, hΨ]
    apply integral_congr_ae
    filter_upwards [Lp.simpleFunc.toSimpleFunc_eq_toFun f] with x hx
    rw [hx]
  have hmaps : (Φ : Lp ℂ p μ → ℂ) = Ψ :=
    (Lp.simpleFunc.denseRange (E := ℂ) (μ := μ) hp).equalizer Φ.continuous Ψ.continuous hsimple
  intro f
  rw [congr_fun hmaps f, hΨ]

theorem finiteLpFunctional_density_memLp_and_norm (hp : p ≠ ∞)
    (Φ : Lp ℂ p μ →L[ℂ] ℂ) {g : X → ℂ} (hgm : Measurable g) (hg : Integrable g μ)
    (hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) = ∫ x in E, g x ∂μ) :
    ∃ hqg : MemLp g q μ, ‖hqg.toLp g‖ ≤ ‖Φ‖ := by
  by_cases hq : q = ∞
  · have hp1 : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one q p).mp hq
    subst p
    subst q
    have hbound := lpOneFunctional_density_ae_bound μ Φ hgm hg hind
    have hmem := lpOneFunctional_density_memLp_top μ Φ hgm hg hind
    refine ⟨hmem, ?_⟩
    have hbound' : ∀ᵐ x ∂μ, ‖hmem.toLp g x‖ ≤ ‖Φ‖ := by
      filter_upwards [MemLp.coeFn_toLp hmem, hbound] with x hx hb
      simpa only [hx] using hb
    simpa using Lp.norm_le_of_ae_bound (p := ∞) (norm_nonneg Φ) hbound'
  · have hbound := lpFunctional_density_eLpNorm_le_of_finite_conjugates μ p q hp hq
      Φ hgm hg hind
    have hmem := lpFunctional_density_memLp_of_finite_conjugates μ p q hp hq Φ hgm hg hind
    refine ⟨hmem, ?_⟩
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg Φ) hbound

/-- The finite-positive-measure case of Rudin 6.16, with uniqueness and exact norm.
This is explicitly not yet the sigma-finite theorem printed in the book. -/
theorem theorem_6_16_finite (hp : p ≠ ∞) (Φ : Lp ℂ p μ →L[ℂ] ℂ) :
    ∃! G : Lp ℂ q μ, (∀ f : Lp ℂ p μ, Φ f = ∫ x, f x * G x ∂μ) ∧ ‖Φ‖ = ‖G‖ := by
  let c := finiteLpFunctionalMeasure μ p hp Φ
  obtain ⟨g, hgm, hgi, hsets, huniq⟩ := theorem_6_10_radon_nikodym c μ
    (finiteLpFunctionalMeasure_absolutelyContinuous μ p hp Φ)
  have hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) = ∫ x in E, g x ∂μ := by
    intro E hE
    rw [← finiteLpFunctionalMeasure_apply μ p hp Φ hE]
    exact hsets E hE
  obtain ⟨hgp, hgnorm⟩ := finiteLpFunctional_density_memLp_and_norm μ p q hp Φ hgm hgi hind
  let G : Lp ℂ q μ := hgp.toLp g
  have hindG : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) = ∫ x in E, G x ∂μ := by
    intro E hE
    rw [hind E hE]
    apply setIntegral_congr_ae hE
    exact (MemLp.coeFn_toLp hgp).symm.mono fun x hx _ => hx
  have hrep := lpFunctional_eq_of_indicator μ p q hp Φ G hindG
  obtain ⟨Ψ, hΨ, hΨnorm⟩ := theorem_6_15 μ p q G
  have hΦΨ : Φ = Ψ := by
    ext f
    exact (hrep f).trans (hΨ f).symm
  have hnorm : ‖Φ‖ = ‖G‖ := le_antisymm (by rw [hΦΨ]; exact hΨnorm) hgnorm
  refine ⟨G, ⟨hrep, hnorm⟩, ?_⟩
  intro H hH
  exact lp_integral_pairing_unique μ p q H G fun f => (hH.1 f).symm.trans (hrep f)

#print axioms lp_integral_pairing_unique
#print axioms lpFunctional_eq_of_indicator
#print axioms finiteLpFunctional_density_memLp_and_norm
#print axioms theorem_6_16_finite

end RudinRCA.Chapter06
