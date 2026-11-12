import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/- This scratch file depends on RungeFunctional.lean. It is intended for the
   aggregate check after that source; it does not postulate a contour formula. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval BigOperators

namespace RudinRCA.Chapter13

/-- A weighted Cauchy kernel as a C(K)-valued function of the contour parameter. -/
def contourResolventKernel (K : Set ℂ) [CompactSpace K] (γ w : ℝ → ℂ) (t : ℝ) : C(K, ℂ) :=
  w t • resolvent (compactCoordinate K) (γ t)

/-- The C(K)-valued kernel is continuous wherever the contour stays off K. -/
theorem continuousOn_contourResolventKernel (K : Set ℂ) [CompactSpace K]
    (γ w : ℝ → ℂ) {a b : ℝ}
    (hγ : ContinuousOn γ [[a, b]]) (hw : ContinuousOn w [[a, b]])
    (havoid : ∀ t ∈ [[a, b]], γ t ∉ K) :
    ContinuousOn (contourResolventKernel K γ w) [[a, b]] := by
  have hr : ContinuousOn (resolvent (compactCoordinate K)) Kᶜ := by
    intro z hz
    have hz' : z ∈ resolventSet ℂ (compactCoordinate K) := by
      apply spectrum.notMem_iff.mp
      rwa [spectrum_compactCoordinate]
    exact (spectrum.hasDerivAt_resolvent_const_left hz').continuousAt.continuousWithinAt
  exact hw.smul (hr.comp hγ havoid)

/-- Compact contour parameter intervals give Bochner integrability in C(K). -/
theorem intervalIntegrable_contourResolventKernel (K : Set ℂ) [CompactSpace K]
    (γ w : ℝ → ℂ) {a b : ℝ}
    (hγ : ContinuousOn γ [[a, b]]) (hw : ContinuousOn w [[a, b]])
    (havoid : ∀ t ∈ [[a, b]], γ t ∉ K) :
    IntervalIntegrable (contourResolventKernel K γ w) volume a b :=
  (continuousOn_contourResolventKernel K γ w hγ hw havoid).intervalIntegrable

/-- Evaluating a C(K)-valued contour integral gives the ordinary scalar Cauchy integral. -/
theorem contourResolventKernel_integral_apply (K : Set ℂ) [CompactSpace K]
    (γ w : ℝ → ℂ) {a b : ℝ}
    (hγ : ContinuousOn γ [[a, b]]) (hw : ContinuousOn w [[a, b]])
    (havoid : ∀ t ∈ [[a, b]], γ t ∉ K) (x : K) :
    (∫ t in a..b, contourResolventKernel K γ w t) x =
      ∫ t in a..b, w t / (γ t - (x : ℂ)) := by
  have hi := intervalIntegrable_contourResolventKernel K γ w hγ hw havoid
  calc
    (∫ t in a..b, contourResolventKernel K γ w t) x =
        ∫ t in a..b, (contourResolventKernel K γ w t) x :=
      ((ContinuousMap.evalCLM ℂ x).intervalIntegral_comp_comm hi).symm
    _ = ∫ t in a..b, w t / (γ t - (x : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [contourResolventKernel, ContinuousMap.smul_apply, smul_eq_mul,
        compactCoordinate_resolvent_apply K (havoid t ht) x, div_eq_mul_inv]

/-- An annihilator of all off-K resolvents annihilates every weighted contour integral. -/
theorem dual_contourResolventKernel_integral_eq_zero (K : Set ℂ) [CompactSpace K]
    (L : C(K, ℂ) →L[ℂ] ℂ) (γ w : ℝ → ℂ) {a b : ℝ}
    (hγ : ContinuousOn γ [[a, b]]) (hw : ContinuousOn w [[a, b]])
    (havoid : ∀ t ∈ [[a, b]], γ t ∉ K)
    (hL : ∀ z ∉ K, L (resolvent (compactCoordinate K) z) = 0) :
    L (∫ t in a..b, contourResolventKernel K γ w t) = 0 := by
  have hi := intervalIntegrable_contourResolventKernel K γ w hγ hw havoid
  rw [← L.intervalIntegral_comp_comm hi]
  calc
    (∫ t in a..b, L (contourResolventKernel K γ w t)) = ∫ _ in a..b, (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [contourResolventKernel, L.map_smul, hL (γ t) (havoid t ht), smul_zero]
    _ = 0 := by simp

/-- A genuine finite contour representation implies annihilation of F.
    The representation is an explicit hypothesis to be supplied by 13.5. -/
theorem dual_eq_zero_of_finite_contour_representation {ι : Type*} [Fintype ι]
    (K : Set ℂ) [CompactSpace K] (F : C(K, ℂ)) (L : C(K, ℂ) →L[ℂ] ℂ)
    (γ w : ι → ℝ → ℂ) (a b : ι → ℝ) (c : ℂ)
    (hγ : ∀ i, ContinuousOn (γ i) [[a i, b i]])
    (hw : ∀ i, ContinuousOn (w i) [[a i, b i]])
    (havoid : ∀ i t, t ∈ [[a i, b i]] → γ i t ∉ K)
    (hrepresentation : ∀ x : K,
      F x = c * ∑ i, ∫ t in a i..b i, w i t / (γ i t - (x : ℂ)))
    (hL : ∀ z ∉ K, L (resolvent (compactCoordinate K) z) = 0) :
    L F = 0 := by
  classical
  have hval : ∀ i (x : K),
      (∫ t in a i..b i, contourResolventKernel K (γ i) (w i) t) x =
        ∫ t in a i..b i, w i t / (γ i t - (x : ℂ)) :=
    fun i x ↦ contourResolventKernel_integral_apply K _ _ (hγ i) (hw i) (havoid i) x
  have hF : F = c • ∑ i, ∫ t in a i..b i, contourResolventKernel K (γ i) (w i) t := by
    ext x
    simpa only [ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.sum_apply, hval] using
      hrepresentation x
  rw [hF, L.map_smul, map_sum]
  have hz : ∀ i, L (∫ t in a i..b i, contourResolventKernel K (γ i) (w i) t) = 0 :=
    fun i ↦ dual_contourResolventKernel_integral_eq_zero K L _ _ (hγ i) (hw i) (havoid i) hL
  simp only [hz, Finset.sum_const_zero, smul_zero]

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.contourResolventKernel_integral_apply
#print axioms RudinRCA.Chapter13.dual_eq_zero_of_finite_contour_representation
