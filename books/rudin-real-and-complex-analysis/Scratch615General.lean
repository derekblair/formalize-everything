import Scratch615GeneralSupport

/-! The unrestricted-positive-measure duality assertion in the discussion 6.15.
The endpoint p = 1 is intentionally excluded here; theorem 6.16 includes it
under its printed sigma-finiteness hypothesis. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

theorem integral_lpZeroExtend_mul (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {S : Set X} (hS : MeasurableSet S) (F : Lp ℂ p (μ.restrict S)) (g : X → ℂ) :
    (∫ x, lpZeroExtend μ p hS F x * g x ∂μ) = ∫ x in S, F x * g x ∂μ := by
  have heq : (fun x => lpZeroExtend μ p hS F x * g x) =ᵐ[μ]
      S.indicator (fun x => F x * g x) := by
    filter_upwards [lpZeroExtend_coeFn μ p hS F] with x hx
    rw [hx]
    by_cases hxS : x ∈ S <;> simp [hxS]
  rw [integral_congr_ae heq, integral_indicator hS]

theorem integral_mul_lpZeroExtend (μ : Measure X) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    {S : Set X} (hS : MeasurableSet S) (f : X → ℂ) (G : Lp ℂ q (μ.restrict S)) :
    (∫ x, f x * lpZeroExtend μ q hS G x ∂μ) = ∫ x in S, f x * G x ∂μ := by
  simpa only [mul_comm] using integral_lpZeroExtend_mul μ q hS G f

/-- Extend the representing density of a sigma-finite restriction by zero.
It represents the functional on all Lp classes supported on that restriction. -/
theorem lpFunctional_density_on_sigmaFinite_restriction (μ : Measure X)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ∞) (Φ : Lp ℂ p μ →L[ℂ] ℂ) {S : Set X} (hS : MeasurableSet S)
    [SigmaFinite (μ.restrict S)] :
    ∃ G : Lp ℂ q μ,
      (∀ f : Lp ℂ p μ, (f : X → ℂ) =ᵐ[μ.restrict Sᶜ] 0 →
        Φ f = ∫ x, f x * G x ∂μ) ∧
      ‖G‖ = ‖lpFunctionalOnRestriction μ p Φ hS‖ ∧
      (G : X → ℂ) =ᵐ[μ.restrict Sᶜ] 0 := by
  obtain ⟨Glocal, ⟨hrep, hnorm⟩, _⟩ := theorem_6_16 (μ.restrict S) p q hp
    (lpFunctionalOnRestriction μ p Φ hS)
  let G := lpZeroExtend μ q hS Glocal
  refine ⟨G, ?_, ?_, lpZeroExtend_ae_zero_compl μ q hS Glocal⟩
  · intro f hfzero
    let F := ((Lp.memLp f).restrict S).toLp f
    have hext : lpZeroExtend μ p hS F = f := lpZeroExtend_restrict_eq μ p hS f hfzero
    calc
      Φ f = lpFunctionalOnRestriction μ p Φ hS F := by
        change Φ f = Φ (lpZeroExtend μ p hS F)
        rw [hext]
      _ = ∫ x in S, F x * Glocal x ∂μ := hrep F
      _ = ∫ x in S, f x * Glocal x ∂μ := by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp f).restrict S)] with x hx
        rw [hx]
      _ = ∫ x, f x * G x ∂μ := (integral_mul_lpZeroExtend μ q hS f Glocal).symm
  · exact ((lpZeroExtend μ q hS).norm_map Glocal).trans hnorm.symm

/-- Two global densities representing the same functional on a sigma-finite
restriction agree as Lq classes on that restriction. -/
theorem lp_density_restrictions_eq (μ : Measure X) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (Φ : Lp ℂ p μ →L[ℂ] ℂ)
    {S : Set X} (hS : MeasurableSet S) [SigmaFinite (μ.restrict S)]
    (G H : Lp ℂ q μ)
    (hG : ∀ f : Lp ℂ p μ, (f : X → ℂ) =ᵐ[μ.restrict Sᶜ] 0 →
      Φ f = ∫ x, f x * G x ∂μ)
    (hH : ∀ f : Lp ℂ p μ, (f : X → ℂ) =ᵐ[μ.restrict Sᶜ] 0 →
      Φ f = ∫ x, f x * H x ∂μ) :
    ((Lp.memLp G).restrict S).toLp G = ((Lp.memLp H).restrict S).toLp H := by
  apply lp_integral_pairing_unique (μ.restrict S) p q
  intro F
  have hzero := lpZeroExtend_ae_zero_compl μ p hS F
  have hvalue := (hG (lpZeroExtend μ p hS F) hzero).symm.trans
    (hH (lpZeroExtend μ p hS F) hzero)
  rw [integral_lpZeroExtend_mul μ p hS F G,
    integral_lpZeroExtend_mul μ p hS F H] at hvalue
  calc
    (∫ x in S, F x * ((Lp.memLp G).restrict S).toLp G x ∂μ) =
        ∫ x in S, F x * G x ∂μ := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp ((Lp.memLp G).restrict S)] with x hx
      rw [hx]
    _ = ∫ x in S, F x * H x ∂μ := hvalue
    _ = ∫ x in S, F x * ((Lp.memLp H).restrict S).toLp H x ∂μ := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp ((Lp.memLp H).restrict S)] with x hx
      rw [hx]

/-- The affirmative answer for 1 < p < ∞ stated in Rudin 6.15 holds for
arbitrary positive measures, without sigma-finiteness or completeness assumptions. -/
theorem theorem_6_15_duality_arbitrary_measure (μ : Measure X)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [ENNReal.HolderConjugate p q]
    (hp1 : 1 < p) (hp : p ≠ ∞) (Φ : Lp ℂ p μ →L[ℂ] ℂ) :
    ∃! G : Lp ℂ q μ, (∀ f : Lp ℂ p μ, Φ f = ∫ x, f x * G x ∂μ) ∧ ‖Φ‖ = ‖G‖ := by
  classical
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hq : q ≠ ∞ := by
    intro htop
    exact hp1.ne' ((ENNReal.HolderConjugate.eq_top_iff_eq_one q p).mp htop)
  obtain ⟨S, hS, hSF, hnormS⟩ := lpFunctional_exists_sigmaFinite_norm_support μ p hp Φ
  letI : SigmaFinite (μ.restrict S) := hSF
  obtain ⟨G, hGrep, hGnorm, hGzero⟩ :=
    lpFunctional_density_on_sigmaFinite_restriction μ p q hp Φ hS
  have hnormG : ‖G‖ = ‖Φ‖ := hGnorm.trans hnormS
  have hrep : ∀ f : Lp ℂ p μ, Φ f = ∫ x, f x * G x ∂μ := by
    intro f
    obtain ⟨T, hT, hfzero, hTF⟩ := ((Lp.memLp f).aefinStronglyMeasurable
      (one_pos.trans_le hp1.le).ne' hp).exists_set_sigmaFinite
    letI : SigmaFinite (μ.restrict T) := hTF
    let U := S ∪ T
    have hU : MeasurableSet U := hS.union hT
    letI : SigmaFinite (μ.restrict U) := by dsimp [U]; infer_instance
    obtain ⟨H, hHrep, hHnorm, hHzero⟩ :=
      lpFunctional_density_on_sigmaFinite_restriction μ p q hp Φ hU
    have hHrepS : ∀ k : Lp ℂ p μ, (k : X → ℂ) =ᵐ[μ.restrict Sᶜ] 0 →
        Φ k = ∫ x, k x * H x ∂μ := by
      intro k hk
      apply hHrep k
      exact ae_restrict_of_ae_restrict_of_subset
        (compl_subset_compl.mpr subset_union_left) hk
    have hrestr := lp_density_restrictions_eq μ p q Φ hS H G hHrepS hGrep
    have hGrestrictNorm : ‖((Lp.memLp G).restrict S).toLp G‖ = ‖G‖ := by
      rw [← (lpZeroExtend μ q hS).norm_map (((Lp.memLp G).restrict S).toLp G),
        lpZeroExtend_restrict_eq μ q hS G hGzero]
    have hHnormLe : ‖H‖ ≤ ‖((Lp.memLp H).restrict S).toLp H‖ := by
      rw [hrestr, hGrestrictNorm, hnormG]
      exact hHnorm.le.trans (lpFunctionalOnRestriction_norm_le μ p Φ hU)
    have hHzeroS := lp_ae_zero_compl_of_norm_le_restrict μ q hq H hS hHnormLe
    have hHG : H = G := by
      calc
        H = lpZeroExtend μ q hS (((Lp.memLp H).restrict S).toLp H) :=
          (lpZeroExtend_restrict_eq μ q hS H hHzeroS).symm
        _ = lpZeroExtend μ q hS (((Lp.memLp G).restrict S).toLp G) :=
          congrArg (lpZeroExtend μ q hS) hrestr
        _ = G := lpZeroExtend_restrict_eq μ q hS G hGzero
    have hfzeroU : (f : X → ℂ) =ᵐ[μ.restrict Uᶜ] 0 :=
      ae_restrict_of_ae_restrict_of_subset (compl_subset_compl.mpr subset_union_right) hfzero
    exact (hHrep f hfzeroU).trans (congrArg (fun K : Lp ℂ q μ => ∫ x, f x * K x ∂μ) hHG)
  refine ⟨G, ⟨hrep, hnormG.symm⟩, ?_⟩
  intro H hH
  exact lp_integral_pairing_unique_finite_exponent μ p q hq H G fun f =>
    (hH.1 f).symm.trans (hrep f)

#print axioms integral_lpZeroExtend_mul
#print axioms integral_mul_lpZeroExtend
#print axioms lpFunctional_density_on_sigmaFinite_restriction
#print axioms lp_density_restrictions_eq
#print axioms theorem_6_15_duality_arbitrary_measure

end RudinRCA.Chapter06
