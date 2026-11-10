import Scratch616F
import Scratch616G
import Scratch616H

/-! Sigma-finite assembly of the Lp dual representation theorem. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

/-- Rudin 6.16: the complex bilinear integral pairing identifies Lq
isometrically with the continuous dual of Lp for sigma-finite measures,
including p = 1 and q = ∞. -/
theorem theorem_6_16 (μ : Measure X) [SigmaFinite μ]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ∞) (Φ : Lp ℂ p μ →L[ℂ] ℂ) :
    ∃! G : Lp ℂ q μ, (∀ f : Lp ℂ p μ, Φ f = ∫ x, f x * G x ∂μ) ∧ ‖Φ‖ = ‖G‖ := by
  classical
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let S := spanningSets μ
  have hS : ∀ n, MeasurableSet (S n) := measurableSet_spanningSets μ
  let ρ : ℕ → Measure X := fun n => μ.restrict (S n)
  have hρ : ∀ n, IsFiniteMeasure (ρ n) := fun n =>
    ⟨by simpa [ρ] using measure_spanningSets_lt_top μ n⟩
  let Φn : ∀ n, Lp ℂ p (ρ n) →L[ℂ] ℂ := fun n => lpFunctionalOnRestriction μ p Φ (hS n)
  have hlocalExists : ∀ n, ∃ G : Lp ℂ q (ρ n),
      (∀ f : Lp ℂ p (ρ n), Φn n f = ∫ x, f x * G x ∂ρ n) ∧ ‖Φn n‖ = ‖G‖ := by
    intro n
    letI := hρ n
    exact (theorem_6_16_finite (ρ n) p q hp (Φn n)).exists
  choose gn hgn using hlocalExists
  have hgnm : ∀ n, Measurable (gn n : X → ℂ) := fun n => (Lp.stronglyMeasurable (gn n)).measurable
  have hgnint : ∀ n, IntegrableOn (gn n : X → ℂ) (S n) μ := by
    intro n
    letI := hρ n
    exact (Lp.memLp (gn n)).integrable (Fact.out : 1 ≤ q)
  have hfinite : ∀ n E, E ⊆ S n → μ E ≠ ∞ := by
    intro n E hES
    exact ne_top_of_le_ne_top (measure_spanningSets_lt_top μ n).ne (measure_mono hES)
  have hsets : ∀ n E (hE : MeasurableSet E) (hES : E ⊆ S n),
      Φ (indicatorConstLp p hE (hfinite n E hES) 1) = ∫ x in E, gn n x ∂μ := by
    intro n E hE hES
    letI := hρ n
    have hr := (hgn n).1 (indicatorConstLp p hE (measure_ne_top (ρ n) E) (1 : ℂ))
    change Φ (lpZeroExtend μ p (hS n)
      (indicatorConstLp p hE (measure_ne_top (ρ n) E) (1 : ℂ))) = _ at hr
    rw [lpZeroExtend_indicatorConstLp μ p (hS n) hE hES (hfinite n E hES) 1,
      integral_indicatorConstLp_mul (ρ n) p hE (measure_ne_top (ρ n) E)] at hr
    simpa only [ρ, Measure.restrict_restrict hE, inter_eq_left.mpr hES] using hr
  have hcompat : ∀ n m, ∀ᵐ x ∂μ, x ∈ S n → x ∈ S m → gn n x = gn m x := by
    intro n m
    let H := S n ∩ S m
    have hH : MeasurableSet H := (hS n).inter (hS m)
    have hnH : Integrable (gn n : X → ℂ) (μ.restrict H) :=
      (hgnint n).mono_set inter_subset_left
    have hmH : Integrable (gn m : X → ℂ) (μ.restrict H) :=
      (hgnint m).mono_set inter_subset_right
    have hEq : (gn n : X → ℂ) =ᵐ[μ.restrict H] gn m := by
      apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hnH hmH
      intro E hE hμE
      rw [Measure.restrict_restrict hE]
      have hEn : E ∩ H ⊆ S n := fun x hx => hx.2.1
      have hEm : E ∩ H ⊆ S m := fun x hx => hx.2.2
      exact (hsets n (E ∩ H) (hE.inter hH) hEn).symm.trans
        (hsets m (E ∩ H) (hE.inter hH) hEm)
    have hEq' := (ae_restrict_iff' hH).mp hEq
    filter_upwards [hEq'] with x hx
    intro hxn hxm
    exact hx ⟨hxn, hxm⟩
  have hbound : ∀ n, eLpNorm ((S n).indicator (gn n : X → ℂ)) q μ ≤ ENNReal.ofReal ‖Φ‖ := by
    intro n
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hS n)]
    change eLpNorm (gn n) q (ρ n) ≤ ENNReal.ofReal ‖Φ‖
    rw [← Lp.enorm_def, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    calc
      ‖gn n‖ = ‖Φn n‖ := (hgn n).2.symm
      _ ≤ ‖Φ‖ := lpFunctionalOnRestriction_norm_le μ p Φ (hS n)
  obtain ⟨g, hgm, hgbound, hglocal⟩ := sigmaFinite_glue_densities μ q
    (fun n => (gn n : X → ℂ)) hgnm hcompat (ENNReal.ofReal ‖Φ‖) hbound
  have hgp : MemLp g q μ := hgbound.trans_lt ENNReal.ofReal_lt_top
  let G : Lp ℂ q μ := hgp.toLp g
  have hGlocal : ∀ n, (G : X → ℂ) =ᵐ[μ.restrict (S n)] gn n := by
    intro n
    have hGae : (G : X → ℂ) =ᵐ[μ.restrict (S n)] g :=
      ae_restrict_of_ae (MemLp.coeFn_toLp hgp)
    exact hGae.trans (hglocal n)
  have hGnorm : ‖G‖ ≤ ‖Φ‖ := by
    change ‖hgp.toLp g‖ ≤ ‖Φ‖
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg Φ) hgbound
  obtain ⟨Ψ, hΨ, hΨnorm⟩ := theorem_6_15 μ p q G
  have hagree : ∀ n E (hE : MeasurableSet E) (hES : E ⊆ S n),
      Φ (indicatorConstLp p hE (hfinite n E hES) 1) =
        Ψ (indicatorConstLp p hE (hfinite n E hES) 1) := by
    intro n E hE hES
    rw [hsets n E hE hES, hΨ,
      integral_indicatorConstLp_mul μ p hE (hfinite n E hES)]
    apply setIntegral_congr_ae hE
    have hl := (ae_restrict_iff' (hS n)).mp (hGlocal n)
    filter_upwards [hl] with x hx
    intro hxE
    exact (hx (hES hxE)).symm
  have hind : ∀ E (hE : MeasurableSet E) (hμE : μ E ≠ ∞),
      Φ (indicatorConstLp p hE hμE 1) = ∫ x in E, G x ∂μ := by
    intro E hE hμE
    have hlim := tendsto_indicatorConstLp_spanningSets μ p hp hE hμE
    have hΦlim := Φ.continuous.continuousAt.tendsto.comp hlim
    have hΨlim := Ψ.continuous.continuousAt.tendsto.comp hlim
    have hvals : ∀ n, Φ (indicatorConstLp p (hE.inter (hS n))
        (ne_top_of_le_ne_top hμE (measure_mono inter_subset_left)) (1 : ℂ)) =
        Ψ (indicatorConstLp p (hE.inter (hS n))
        (ne_top_of_le_ne_top hμE (measure_mono inter_subset_left)) (1 : ℂ)) := by
      intro n
      exact hagree n (E ∩ S n) (hE.inter (hS n)) inter_subset_right
    have heq := tendsto_nhds_unique (hΦlim.congr' (Eventually.of_forall hvals)) hΨlim
    exact heq.trans ((hΨ _).trans (integral_indicatorConstLp_mul μ p hE hμE G))
  have hrep := lpFunctional_eq_of_finite_indicator μ p q hp Φ G hind
  have hΦΨ : Φ = Ψ := by
    ext f
    exact (hrep f).trans (hΨ f).symm
  have hnorm : ‖Φ‖ = ‖G‖ := le_antisymm (by rw [hΦΨ]; exact hΨnorm) hGnorm
  refine ⟨G, ⟨hrep, hnorm⟩, ?_⟩
  intro H hH
  exact lp_integral_pairing_unique μ p q H G fun f => (hH.1 f).symm.trans (hrep f)

#print axioms theorem_6_16

end RudinRCA.Chapter06
