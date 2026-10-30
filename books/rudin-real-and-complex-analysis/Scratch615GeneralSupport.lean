import Scratch616J
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! Sigma-finite supports and finite-exponent norm rigidity for the unrestricted
measure assertion in Rudin 6.15. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

theorem lpZeroExtend_restrict_eq (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {S : Set X} (hS : MeasurableSet S) (f : Lp ℂ p μ)
    (hfzero : (f : X → ℂ) =ᵐ[μ.restrict Sᶜ] 0) :
    lpZeroExtend μ p hS (((Lp.memLp f).restrict S).toLp f) = f := by
  apply Lp.ext
  have hr := (ae_eq_restrict_iff_indicator_ae_eq hS).mp
    (MemLp.coeFn_toLp ((Lp.memLp f).restrict S))
  have hz := (ae_restrict_iff' hS.compl).mp hfzero
  filter_upwards [lpZeroExtend_coeFn μ p hS (((Lp.memLp f).restrict S).toLp f), hr, hz]
    with x h₁ h₂ h₃
  rw [h₁, h₂]
  by_cases hx : x ∈ S
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx, h₃ hx]

theorem lpZeroExtend_ae_zero_compl (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {S : Set X} (hS : MeasurableSet S) (f : Lp ℂ p (μ.restrict S)) :
    (lpZeroExtend μ p hS f : X → ℂ) =ᵐ[μ.restrict Sᶜ] 0 := by
  apply (ae_restrict_iff' hS.compl).mpr
  filter_upwards [lpZeroExtend_coeFn μ p hS f] with x hx
  intro hxS
  rw [hx, indicator_of_notMem hxS]

theorem lp_integral_pairing_unique_finite_exponent (μ : Measure X)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hq : q ≠ ∞)
    (g h : Lp ℂ q μ)
    (heq : ∀ f : Lp ℂ p μ, (∫ x, f x * g x ∂μ) = ∫ x, f x * h x ∂μ) : g = h := by
  have hint : ∀ k : Lp ℂ q μ, ∀ E, MeasurableSet E → μ E < ∞ → IntegrableOn k E μ := by
    intro k E hE hμE
    letI : IsFiniteMeasure (μ.restrict E) := ⟨by simpa using hμE⟩
    exact ((Lp.memLp k).restrict E).integrable (Fact.out : 1 ≤ q)
  apply Lp.ext
  apply Lp.ae_eq_of_forall_setIntegral_eq g h
    (one_pos.trans_le (Fact.out : 1 ≤ q)).ne' hq (hint g) (hint h)
  intro E hE hμE
  have ht := heq (indicatorConstLp p hE hμE.ne (1 : ℂ))
  simpa only [integral_indicatorConstLp_mul μ p hE hμE.ne] using ht

/-- A bounded functional on finite-exponent Lp captures its whole norm on a
sigma-finite measurable restriction, even when the ambient measure is arbitrary. -/
theorem lpFunctional_exists_sigmaFinite_norm_support (μ : Measure X)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (Φ : Lp ℂ p μ →L[ℂ] ℂ) :
    ∃ S, ∃ hS : MeasurableSet S, SigmaFinite (μ.restrict S) ∧
      ‖lpFunctionalOnRestriction μ p Φ hS‖ = ‖Φ‖ := by
  classical
  have happrox : ∀ n : ℕ, ∃ f : Lp ℂ p μ,
      ‖f‖ < 1 ∧ ‖Φ‖ - 1 / ((n : ℝ) + 1) < ‖Φ f‖ := by
    intro n
    apply Φ.exists_lt_apply_of_lt_opNorm
    exact sub_lt_self _ (by positivity)
  choose fn hfn hval using happrox
  have hsupp : ∀ n, ∃ S, MeasurableSet S ∧
      (fn n : X → ℂ) =ᵐ[μ.restrict Sᶜ] 0 ∧ SigmaFinite (μ.restrict S) := by
    intro n
    exact ((Lp.memLp (fn n)).aefinStronglyMeasurable
      (one_pos.trans_le (Fact.out : 1 ≤ p)).ne' hp).exists_set_sigmaFinite
  choose Sn hSn hzero hsig using hsupp
  let S : Set X := ⋃ n, Sn n
  have hS : MeasurableSet S := MeasurableSet.iUnion hSn
  letI : ∀ n, SigmaFinite (μ.restrict (Sn n)) := hsig
  have hSF : SigmaFinite (μ.restrict S) := by
    let cover : ℕ × ℕ → Set X := fun nk =>
      Sn nk.1 ∩ spanningSets (μ.restrict (Sn nk.1)) nk.2
    apply Measure.sigmaFinite_of_countable
      ((countable_range cover).insert Sᶜ) (S := insert Sᶜ (range cover))
    · intro E hE
      rcases hE with rfl | ⟨⟨n, k⟩, rfl⟩
      · simp [Measure.restrict_apply hS.compl]
      · calc
          (μ.restrict S) (cover (n, k)) ≤ μ (cover (n, k)) := Measure.restrict_le_self _
          _ = (μ.restrict (Sn n)) (spanningSets (μ.restrict (Sn n)) k) := by
            rw [Measure.restrict_apply' (hSn n)]
            exact congrArg μ (inter_comm _ _)
          _ < ∞ := measure_spanningSets_lt_top (μ.restrict (Sn n)) k
    · apply eq_univ_of_forall
      intro x
      apply mem_sUnion.mpr
      by_cases hxS : x ∈ S
      · obtain ⟨n, hxn⟩ := mem_iUnion.mp hxS
        let k := spanningSetsIndex (μ.restrict (Sn n)) x
        exact ⟨cover (n, k), mem_insert_of_mem _ ⟨(n, k), rfl⟩,
          hxn, mem_spanningSetsIndex (μ.restrict (Sn n)) x⟩
      · exact ⟨Sᶜ, mem_insert _ _, hxS⟩
  let Ψ := lpFunctionalOnRestriction μ p Φ hS
  have hnormLower : ∀ n, ‖Φ‖ - 1 / ((n : ℝ) + 1) < ‖Ψ‖ := by
    intro n
    let fS := ((Lp.memLp (fn n)).restrict S).toLp (fn n)
    have hz : (fn n : X → ℂ) =ᵐ[μ.restrict Sᶜ] 0 :=
      ae_restrict_of_ae_restrict_of_subset
        (compl_subset_compl.mpr (subset_iUnion Sn n)) (hzero n)
    have hext : lpZeroExtend μ p hS fS = fn n := lpZeroExtend_restrict_eq μ p hS (fn n) hz
    have hfSnorm : ‖fS‖ = ‖fn n‖ := by
      rw [← (lpZeroExtend μ p hS).norm_map fS, hext]
    have hΦeq : Ψ fS = Φ (fn n) := by
      change Φ (lpZeroExtend μ p hS fS) = _
      rw [hext]
    have hbound : ‖Φ (fn n)‖ ≤ ‖Ψ‖ := by
      rw [← hΦeq]
      calc
        ‖Ψ fS‖ ≤ ‖Ψ‖ * ‖fS‖ := Ψ.le_opNorm fS
        _ ≤ ‖Ψ‖ * 1 := mul_le_mul_of_nonneg_left
          (by rw [hfSnorm]; exact (hfn n).le) (norm_nonneg Ψ)
        _ = ‖Ψ‖ := mul_one _
    exact (hval n).trans_le hbound
  refine ⟨S, hS, hSF, le_antisymm (lpFunctionalOnRestriction_norm_le μ p Φ hS) ?_⟩
  by_contra h
  have hpos : 0 < ‖Φ‖ - ‖Ψ‖ := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
  have hlt := hnormLower n
  linarith

/-- For a finite nonzero exponent, a restriction can retain the full Lq norm
only if the function vanishes almost everywhere on the complement. -/
theorem memLp_ae_zero_compl_of_eLpNorm_le_restrict (μ : Measure X)
    (q : ℝ≥0∞) (hq0 : q ≠ 0) (hq : q ≠ ∞) {g : X → ℂ} (hg : MemLp g q μ)
    {S : Set X} (hS : MeasurableSet S)
    (hnorm : eLpNorm g q μ ≤ eLpNorm g q (μ.restrict S)) :
    g =ᵐ[μ.restrict Sᶜ] 0 := by
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have heq : eLpNorm g q (μ.restrict S) = eLpNorm g q μ :=
    le_antisymm (eLpNorm_restrict_le g q μ S) hnorm
  have hmass : (∫⁻ x in S, ‖g x‖ₑ ^ q.toReal ∂μ) = ∫⁻ x, ‖g x‖ₑ ^ q.toReal ∂μ := by
    have hpow := congrArg (fun z : ℝ≥0∞ => z ^ q.toReal) heq
    rw [eLpNorm_eq_eLpNorm' hq0 hq hg.aestronglyMeasurable.restrict,
      eLpNorm_eq_eLpNorm' hq0 hq hg.aestronglyMeasurable,
      ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hqr,
      ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hqr] at hpow
    exact hpow
  have hfinite : (∫⁻ x in S, ‖g x‖ₑ ^ q.toReal ∂μ) ≠ ∞ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hq0 hq ((hg.restrict S))).ne
  have hcompl : (∫⁻ x in Sᶜ, ‖g x‖ₑ ^ q.toReal ∂μ) = 0 := by
    rw [setLIntegral_compl hS hfinite, hmass, tsub_self]
  apply (eLpNorm_eq_zero_iff hq0).mp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq hg.aestronglyMeasurable.restrict,
    hcompl, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hqr)]

theorem lp_ae_zero_compl_of_norm_le_restrict (μ : Measure X)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q ≠ ∞) (g : Lp ℂ q μ)
    {S : Set X} (hS : MeasurableSet S)
    (hnorm : ‖g‖ ≤ ‖((Lp.memLp g).restrict S).toLp g‖) :
    (g : X → ℂ) =ᵐ[μ.restrict Sᶜ] 0 := by
  apply memLp_ae_zero_compl_of_eLpNorm_le_restrict μ q
    (one_pos.trans_le (Fact.out : 1 ≤ q)).ne' hq (Lp.memLp g) hS
  rw [Lp.norm_def, Lp.norm_toLp] at hnorm
  exact (ENNReal.toReal_le_toReal (Lp.memLp g).ne ((Lp.memLp g).restrict S).ne).mp hnorm

#print axioms lpZeroExtend_restrict_eq
#print axioms lpZeroExtend_ae_zero_compl
#print axioms lp_integral_pairing_unique_finite_exponent
#print axioms lpFunctional_exists_sigmaFinite_norm_support
#print axioms memLp_ae_zero_compl_of_eLpNorm_le_restrict
#print axioms lp_ae_zero_compl_of_norm_le_restrict

end RudinRCA.Chapter06
