import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Chapter 10: elementary properties of holomorphic functions

This is a partial chapter, not a claim that all 44 numbered items are proved.
The inventory records every item, subclaim, dependency and outstanding bridge.
In particular, general paths/cycles and their integral-defined index must not be
silently replaced by circles. All functions below are total representatives;
theorems restrict their hypotheses and conclusions to the specified open set.
-/

noncomputable section

open Set Filter Topology

namespace RudinRCA.Chapter10

/-- 10.1: the open disc. Radii in book statements are positive. -/
def disc (a : ℂ) (r : ℝ) : Set ℂ := Metric.ball a r

/-- 10.1: the punctured disc. -/
def puncturedDisc (a : ℂ) (r : ℝ) : Set ℂ := disc a r \ {a}

/-- 10.1: a region is nonempty, connected, and open. -/
def IsRegion (Ω : Set ℂ) : Prop := IsOpen Ω ∧ IsConnected Ω

theorem mem_disc {a z : ℂ} {r : ℝ} : z ∈ disc a r ↔ ‖z - a‖ < r :=
  mem_ball_iff_norm

theorem mem_puncturedDisc {a z : ℂ} {r : ℝ} :
    z ∈ puncturedDisc a r ↔ 0 < ‖z - a‖ ∧ ‖z - a‖ < r := by
  simp only [puncturedDisc, Set.mem_sdiff, mem_disc, mem_singleton_iff,
    norm_pos_iff, sub_ne_zero]
  exact and_comm

/-- 10.2: complex differentiability at every point of the open domain. -/
def HolomorphicOn (f : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  ∀ z ∈ Ω, DifferentiableAt ℂ f z

theorem holomorphicOn_iff_differentiableOn {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) : HolomorphicOn f Ω ↔ DifferentiableOn ℂ f Ω := by
  constructor
  · exact fun hf z hz => (hf z hz).differentiableWithinAt
  · exact fun hf z hz => hf.differentiableAt (hΩ.mem_nhds hz)

/-- The derivative in 10.2 is exactly the limit of complex difference quotients. -/
theorem hasDerivAt_iff_difference_quotient {f : ℂ → ℂ} {a d : ℂ} :
    HasDerivAt f d a ↔
      Tendsto (fun z => (f z - f a) / (z - a)) (𝓝[≠] a) (𝓝 d) := by
  have hs : slope f a = fun z => (f z - f a) / (z - a) :=
    funext (slope_def_field f a)
  rw [hasDerivAt_iff_tendsto_slope, hs]

/-- 10.2: as a real-linear operator, the derivative multiplies by the complex derivative. -/
theorem hasFDerivAt_real_of_hasDerivAt {f : ℂ → ℂ} {a d : ℂ}
    (hf : HasDerivAt f d a) :
    HasFDerivAt f ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ) a :=
  hf.hasFDerivAt.restrictScalars ℝ

/-- 10.3: addition in the ring of holomorphic functions. -/
theorem holomorphicOn_add {f g : ℂ → ℂ} {Ω : Set ℂ}
    (hf : HolomorphicOn f Ω) (hg : HolomorphicOn g Ω) :
    HolomorphicOn (fun z => f z + g z) Ω :=
  fun z hz => (hf z hz).add (hg z hz)

theorem holomorphicOn_mul {f g : ℂ → ℂ} {Ω : Set ℂ}
    (hf : HolomorphicOn f Ω) (hg : HolomorphicOn g Ω) :
    HolomorphicOn (fun z => f z * g z) Ω :=
  fun z hz => (hf z hz).mul (hg z hz)

theorem holomorphicOn_const (c : ℂ) (Ω : Set ℂ) : HolomorphicOn (fun _ => c) Ω :=
  fun _ _ => differentiableAt_const c

theorem holomorphicOn_neg {f : ℂ → ℂ} {Ω : Set ℂ} (hf : HolomorphicOn f Ω) :
    HolomorphicOn (fun z => -f z) Ω := fun z hz => (hf z hz).neg

theorem holomorphicOn_comp {f g : ℂ → ℂ} {Ω Ω₁ : Set ℂ}
    (hf : HolomorphicOn f Ω) (hg : HolomorphicOn g Ω₁) (hmap : MapsTo f Ω Ω₁) :
    HolomorphicOn (g ∘ f) Ω := fun z hz => (hg (f z) (hmap hz)).comp z (hf z hz)

theorem deriv_add {f g : ℂ → ℂ} {Ω : Set ℂ}
    (hf : HolomorphicOn f Ω) (hg : HolomorphicOn g Ω) {z : ℂ} (hz : z ∈ Ω) :
    deriv (fun w => f w + g w) z = deriv f z + deriv g z :=
  ((hf z hz).hasDerivAt.add (hg z hz).hasDerivAt).deriv

theorem deriv_mul {f g : ℂ → ℂ} {Ω : Set ℂ}
    (hf : HolomorphicOn f Ω) (hg : HolomorphicOn g Ω) {z : ℂ} (hz : z ∈ Ω) :
    deriv (fun w => f w * g w) z = deriv f z * g z + f z * deriv g z :=
  ((hf z hz).hasDerivAt.mul (hg z hz).hasDerivAt).deriv

theorem deriv_comp {f g : ℂ → ℂ} {Ω Ω₁ : Set ℂ}
    (hf : HolomorphicOn f Ω) (hg : HolomorphicOn g Ω₁) (hmap : MapsTo f Ω Ω₁)
    {z : ℂ} (hz : z ∈ Ω) :
    deriv (g ∘ f) z = deriv g (f z) * deriv f z :=
  ((hg (f z) (hmap hz)).hasDerivAt.comp z (hf z hz).hasDerivAt).deriv

theorem continuousOn_of_holomorphicOn {f : ℂ → ℂ} {Ω : Set ℂ}
    (hf : HolomorphicOn f Ω) : ContinuousOn f Ω :=
  fun z hz => (hf z hz).continuousAt.continuousWithinAt

/-- 10.4: powers and polynomial functions are entire. -/
theorem holomorphicOn_pow (n : ℕ) : HolomorphicOn (fun z : ℂ => z ^ n) univ :=
  fun _ _ => differentiableAt_id.pow n

theorem holomorphicOn_polynomial (p : Polynomial ℂ) : HolomorphicOn p.eval univ :=
  fun _ _ => p.differentiableAt

theorem holomorphicOn_inv : HolomorphicOn (fun z : ℂ => z⁻¹) {z | z ≠ 0} :=
  fun _ hz => differentiableAt_id.inv hz

theorem holomorphicOn_div {f g : ℂ → ℂ} {Ω Ω₀ : Set ℂ}
    (hf : HolomorphicOn f Ω) (hg : HolomorphicOn g Ω) (hsub : Ω₀ ⊆ Ω)
    (hne : ∀ z ∈ Ω₀, g z ≠ 0) : HolomorphicOn (fun z => f z / g z) Ω₀ :=
  fun z hz => (hf z (hsub hz)).div (hg z (hsub hz)) (hne z hz)

theorem holomorphicOn_exp : HolomorphicOn Complex.exp univ :=
  fun _ _ => Complex.differentiableAt_exp

theorem deriv_exp (z : ℂ) : deriv Complex.exp z = Complex.exp z :=
  (Complex.hasDerivAt_exp z).deriv

/-- 10.5's definition uses every contained disc, not just some neighborhood. -/
def RepresentableByPowerSeries (f : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  ∀ (a : ℂ) (r : ℝ), 0 < r → disc a r ⊆ Ω →
    ∃ c : ℕ → ℂ, ∀ z ∈ disc a r, HasSum (fun n => c n * (z - a) ^ n) (f z)

/-- 10.16: a power series represents a holomorphic function on every contained disc.
Mathlib supplies the Cauchy/integration argument, independently of Chapters 1–9. -/
theorem representableByPowerSeries_of_holomorphicOn {f : ℂ → ℂ} {Ω : Set ℂ}
    (hf : HolomorphicOn f Ω) : RepresentableByPowerSeries f Ω := by
  intro a r _hr hsub
  refine ⟨fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n f a, ?_⟩
  intro z hz
  have hd : DifferentiableOn ℂ f (Metric.ball a r) :=
    fun w hw => (hf w (hsub hw)).differentiableWithinAt
  convert Complex.hasSum_taylorSeries_on_ball hd hz using 1
  funext n
  simp only [smul_eq_mul]
  ring

/-- The unnumbered corollary to 10.16. -/
theorem holomorphicOn_deriv {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : HolomorphicOn f Ω) : HolomorphicOn (deriv f) Ω := by
  have ha := ((holomorphicOn_iff_differentiableOn hΩ).mp hf).analyticOnNhd hΩ
  exact fun z hz => (ha.deriv z hz).differentiableAt

/-- 10.19: an isolated singularity, including the domain and openness convention. -/
def HasIsolatedSingularity (f : ℂ → ℂ) (Ω : Set ℂ) (a : ℂ) : Prop :=
  IsOpen Ω ∧ a ∈ Ω ∧ HolomorphicOn f (Ω \ {a})

/-- 10.19: removability means extension by changing only the value at `a`. -/
def HasRemovableSingularity (f : ℂ → ℂ) (Ω : Set ℂ) (a : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, HolomorphicOn g Ω ∧ EqOn g f (Ω \ {a})

/-- 10.20: boundedness on a punctured disc makes an isolated singularity removable. -/
theorem removable_of_bounded {f : ℂ → ℂ} {Ω : Set ℂ} {a : ℂ}
    (hiso : HasIsolatedSingularity f Ω a) {r : ℝ} (hr : 0 < r)
    (hb : ∃ M : ℝ, ∀ z ∈ puncturedDisc a r, ‖f z‖ ≤ M) :
    HasRemovableSingularity f Ω a := by
  rcases hiso with ⟨hΩ, ha, hf⟩
  rcases hb with ⟨M, hM⟩
  have hbounded : IsBoundedUnder (· ≤ ·) (𝓝[≠] a) (fun z => ‖f z - f a‖) := by
    refine ⟨M + ‖f a‖, ?_⟩
    apply eventually_map.mpr
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds a hr)]
      with z hza hzr
    exact norm_sub_le_of_le (hM z ⟨hzr, hza⟩) le_rfl
  have hd : ∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℂ f z := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hΩ.mem_nhds ha)] with z hza hz
    exact hf z ⟨hz, hza⟩
  have ht := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
    hd hbounded
  let g := Function.update f a (limUnder (𝓝[≠] a) f)
  have heq : ∀ z, z ≠ a → g =ᶠ[𝓝 z] f := by
    intro z hza
    filter_upwards [isOpen_ne.mem_nhds hza] with w hw
    exact Function.update_of_ne hw _ _
  have hg : DifferentiableOn ℂ g (Ω \ {a}) := by
    intro z hz
    exact ((hf z hz).congr_of_eventuallyEq (heq z hz.2)).differentiableWithinAt
  have hgc : ContinuousAt g a := continuousAt_update_same.mpr ht
  have hgd := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
    (hΩ.mem_nhds ha)).mp ⟨hg, hgc⟩
  refine ⟨g, (holomorphicOn_iff_differentiableOn hΩ).mpr hgd, ?_⟩
  intro z hz
  exact Function.update_of_ne hz.2 _ _

/-- 10.23: every bounded entire function is constant. -/
theorem liouville {f : ℂ → ℂ} (hf : HolomorphicOn f univ)
    (hb : Bornology.IsBounded (range f)) : ∃ c : ℂ, ∀ z, f z = c :=
  (show Differentiable ℂ f from fun z => hf z (mem_univ z)).exists_const_forall_eq_of_bounded hb

section MaximumModulus
open Metric

/-- The maximum in 10.24, written on the geometric boundary circle. -/
def circleMaximum (f : ℂ → ℂ) (a : ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' sphere a r)

/-- The minimum in the corollary to 10.24. -/
def circleMinimum (f : ℂ → ℂ) (a : ℂ) (r : ℝ) : ℝ :=
  sInf ((fun z => ‖f z‖) '' sphere a r)

/-- The geometric-circle maximum is precisely the supremum over Rudin's
angular parametrization, `a + r * exp (θ * I)`. -/
theorem circleMaximum_eq_angular_sup (f : ℂ → ℂ) (a : ℂ) {r : ℝ} (hr : 0 < r) :
    circleMaximum f a r = sSup (range (fun θ : ℝ => ‖f (circleMap a r θ)‖)) := by
  have hcircle : range (circleMap a r) = sphere a r := by
    simp [abs_of_pos hr]
  unfold circleMaximum
  rw [← hcircle, ← range_comp]
  rfl

theorem circleMinimum_eq_angular_inf (f : ℂ → ℂ) (a : ℂ) {r : ℝ} (hr : 0 < r) :
    circleMinimum f a r = sInf (range (fun θ : ℝ => ‖f (circleMap a r θ)‖)) := by
  have hcircle : range (circleMap a r) = sphere a r := by
    simp [abs_of_pos hr]
  unfold circleMinimum
  rw [← hcircle, ← range_comp]
  rfl

/-- Compactness ensures that `circleMaximum` really is an attained maximum. -/
theorem circleMaximum_attained {f : ℂ → ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn f (sphere a r)) :
    ∃ w ∈ sphere a r, circleMaximum f a r = ‖f w‖ := by
  obtain ⟨w, hw, hmax⟩ := (isCompact_sphere a r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hc.norm
  refine ⟨w, hw, le_antisymm ?_ ?_⟩
  · apply csSup_le (Nonempty.image _ (NormedSpace.sphere_nonempty.mpr hr.le))
    rintro _ ⟨z, hz, rfl⟩
    exact hmax hz
  · exact le_csSup ((isCompact_sphere a r).image_of_continuousOn hc.norm).bddAbove
      (mem_image_of_mem _ hw)

/-- Compactness likewise ensures that `circleMinimum` is attained. -/
theorem circleMinimum_attained {f : ℂ → ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn f (sphere a r)) :
    ∃ w ∈ sphere a r, circleMinimum f a r = ‖f w‖ := by
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere a r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hc.norm
  refine ⟨w, hw, le_antisymm ?_ ?_⟩
  · exact csInf_le ((isCompact_sphere a r).image_of_continuousOn hc.norm).bddBelow
      (mem_image_of_mem _ hw)
  · apply le_csInf (Nonempty.image _ (NormedSpace.sphere_nonempty.mpr hr.le))
    rintro _ ⟨z, hz, rfl⟩
    exact hmin hz

/-- 10.24: a local maximum of the modulus forces constancy throughout the region. -/
theorem constant_of_local_maximum {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsRegion Ω) (hf : HolomorphicOn f Ω) {a : ℂ} (ha : a ∈ Ω)
    (hm : IsLocalMax (fun z => ‖f z‖) a) : ∀ z ∈ Ω, f z = f a := by
  have hd : ∀ᶠ z in 𝓝 a, DifferentiableAt ℂ f z := by
    filter_upwards [hΩ.1.mem_nhds ha] with z hz using hf z hz
  have heq := Complex.eventually_eq_of_isLocalMax_norm hd hm
  have hA := ((holomorphicOn_iff_differentiableOn hΩ.1).mp hf).analyticOnNhd hΩ.1
  exact hA.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hΩ.2.isPreconnected ha heq

/-- 10.24: the value at the center is bounded by the boundary maximum. -/
theorem maximum_modulus {f : ℂ → ℂ} {Ω : Set ℂ} (hf : HolomorphicOn f Ω)
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hsub : closedBall a r ⊆ Ω) :
    ‖f a‖ ≤ circleMaximum f a r := by
  have hc : ContinuousOn f (closedBall a r) :=
    (continuousOn_of_holomorphicOn hf).mono hsub
  have hd : DiffContOnCl ℂ f (ball a r) :=
    ⟨fun z hz => (hf z (hsub (ball_subset_closedBall hz))).differentiableWithinAt,
      by simpa [closure_ball a hr.ne'] using hc⟩
  have hB := ((isCompact_sphere a r).image_of_continuousOn
    (hc.mono sphere_subset_closedBall).norm).bddAbove
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
    (fun z hz => le_csSup hB (mem_image_of_mem _ ?_)) (subset_closure (mem_ball_self hr))
  simpa [frontier_ball a hr.ne'] using hz

/-- 10.24: equality is equivalent to constancy on the entire region. -/
theorem maximum_modulus_eq_iff {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsRegion Ω) (hf : HolomorphicOn f Ω) {a : ℂ} {r : ℝ}
    (hr : 0 < r) (hsub : closedBall a r ⊆ Ω) :
    ‖f a‖ = circleMaximum f a r ↔ ∀ z ∈ Ω, f z = f a := by
  have hc : ContinuousOn f (closedBall a r) :=
    (continuousOn_of_holomorphicOn hf).mono hsub
  have hd : DiffContOnCl ℂ f (ball a r) :=
    ⟨fun z hz => (hf z (hsub (ball_subset_closedBall hz))).differentiableWithinAt,
      by simpa [closure_ball a hr.ne'] using hc⟩
  have hB := ((isCompact_sphere a r).image_of_continuousOn
    (hc.mono sphere_subset_closedBall).norm).bddAbove
  constructor
  · intro heq
    apply constant_of_local_maximum hΩ hf (hsub (mem_closedBall_self hr.le))
    filter_upwards [ball_mem_nhds a hr] with z hz
    apply (Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
      (fun w hw => le_csSup hB (mem_image_of_mem _ ?_)))
      (subset_closure hz) |>.trans_eq heq.symm
    simpa [frontier_ball a hr.ne'] using hw
  · intro heq
    obtain ⟨w, hw, hmax⟩ := circleMaximum_attained hr (hc.mono sphere_subset_closedBall)
    rw [hmax, heq w (hsub (sphere_subset_closedBall hw))]

/-- The minimum-modulus corollary to 10.24 needs no boundary nonvanishing. -/
theorem minimum_modulus {f : ℂ → ℂ} {Ω : Set ℂ} (hf : HolomorphicOn f Ω)
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hsub : closedBall a r ⊆ Ω)
    (hne : ∀ z ∈ disc a r, f z ≠ 0) : circleMinimum f a r ≤ ‖f a‖ := by
  have hc : ContinuousOn f (closedBall a r) :=
    (continuousOn_of_holomorphicOn hf).mono hsub
  have hB := ((isCompact_sphere a r).image_of_continuousOn
    (hc.mono sphere_subset_closedBall).norm).bddBelow
  by_cases hzero : ∃ w ∈ sphere a r, f w = 0
  · obtain ⟨w, hw, hfw⟩ := hzero
    exact (csInf_le hB (mem_image_of_mem _ hw)).trans (by simp [hfw])
  · have hnz : ∀ z ∈ closedBall a r, f z ≠ 0 := by
      intro z hz
      rcases lt_or_eq_of_le (mem_closedBall.mp hz) with hlt | heq
      · exact hne z hlt
      · exact fun h => hzero ⟨z, heq, h⟩
    have hdinv : DiffContOnCl ℂ (fun z => (f z)⁻¹) (ball a r) :=
      ⟨fun z hz => ((hf z (hsub (ball_subset_closedBall hz))).inv
        (hnz z (ball_subset_closedBall hz))).differentiableWithinAt,
        by
          intro z hz
          have hz' : z ∈ closedBall a r := closure_ball_subset_closedBall hz
          exact ((hf z (hsub hz')).continuousAt.inv₀ (hnz z hz')).continuousWithinAt⟩
    obtain ⟨w, hw, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm isBounded_ball
      (nonempty_ball.mpr hr) hdinv
    have hws : w ∈ sphere a r := by simpa [frontier_ball a hr.ne'] using hw
    have hbound : ‖(f a)⁻¹‖ ≤ ‖(f w)⁻¹‖ :=
      hmax (subset_closure (mem_ball_self hr))
    have hle : ‖f w‖ ≤ ‖f a‖ :=
      (inv_le_inv₀ (norm_pos_iff.mpr (hnz a (mem_closedBall_self hr.le)))
        (norm_pos_iff.mpr (hnz w (sphere_subset_closedBall hws)))).mp (by
        simpa only [norm_inv] using hbound)
    exact (csInf_le hB (mem_image_of_mem _ hws)).trans hle


end MaximumModulus

/-- 10.25: the multiset counts zeros with their multiplicities. The theorem is
stated for every complex polynomial of degree `n`, and in particular for the
monic polynomial displayed in Rudin. -/
theorem number_of_polynomial_zeros (p : Polynomial ℂ) {n : ℕ}
    (_hn : 0 < n) (hdegree : p.natDegree = n) : p.roots.card = n := by
  rw [← Polynomial.Splits.natDegree_eq_card_roots (IsAlgClosed.splits p), hdegree]

theorem nonconstant_polynomial_has_zero {p : Polynomial ℂ} (hp : 0 < p.degree) :
    ∃ z : ℂ, p.eval z = 0 := Complex.exists_root hp

/-- 10.26: the estimate uses an open disc and requires no boundary extension. -/
theorem cauchy_estimate {f : ℂ → ℂ} {a : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : HolomorphicOn f (disc a R)) (hM : ∀ z ∈ disc a R, ‖f z‖ ≤ M)
    (n : ℕ) : ‖iteratedDeriv n f a‖ ≤ n.factorial * M / R ^ n := by
  have hd := (holomorphicOn_iff_differentiableOn Metric.isOpen_ball).mp hf
  have he : ∀ᶠ r in 𝓝[<] R, ‖iteratedDeriv n f a‖ ≤ n.factorial * M / r ^ n := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hR)] with r hrR hr
    have hs : Metric.closedBall a r ⊆ Metric.ball a R := Metric.closedBall_subset_ball hrR
    apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
      (hd.diffContOnCl_ball hs)
    exact fun z hz => hM z (hs (Metric.sphere_subset_closedBall hz))
  have hc : ContinuousAt (fun r : ℝ => (n.factorial : ℝ) * M / r ^ n) R :=
    continuousAt_const.div (continuousAt_id.pow n) (pow_ne_zero n hR.ne')
  exact ge_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds) he

/-- The sharpness example following 10.26. -/
theorem cauchy_estimate_sharp (n : ℕ) :
    (∀ z ∈ disc (0 : ℂ) 1, ‖z ^ n‖ ≤ 1) ∧
    iteratedDeriv n (fun z : ℂ => z ^ n) 0 = (n.factorial : ℂ) := by
  constructor
  · intro z hz
    have hz' : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
    simpa only [norm_pow, one_pow] using pow_le_pow_left₀ (norm_nonneg z) hz' n
  · simp [Nat.descFactorial_self]

/-- 10.27: uniform convergence on every compact subset of the domain. -/
def ConvergesOnCompactSubsets (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  ∀ K ⊆ Ω, IsCompact K → TendstoUniformlyOn F f atTop K

theorem convergesOnCompactSubsets_iff {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) :
    ConvergesOnCompactSubsets F f Ω ↔ TendstoLocallyUniformlyOn F f atTop Ω :=
  (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).symm

/-- 10.28: compact uniform limits preserve holomorphy and commute with differentiation. -/
theorem holomorphicOn_limit_and_deriv {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hF : ∀ n, HolomorphicOn (F n) Ω)
    (hlim : ConvergesOnCompactSubsets F f Ω) :
    HolomorphicOn f Ω ∧ ConvergesOnCompactSubsets (fun n => deriv (F n)) (deriv f) Ω := by
  have hc := (convergesOnCompactSubsets_iff hΩ).mp hlim
  have hd : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) Ω :=
    Eventually.of_forall fun n => (holomorphicOn_iff_differentiableOn hΩ).mp (hF n)
  exact ⟨(holomorphicOn_iff_differentiableOn hΩ).mpr (hc.differentiableOn hd hΩ),
    (convergesOnCompactSubsets_iff hΩ).mpr (hc.deriv hd hΩ)⟩

/-- The unnumbered corollary to 10.28 includes every order of derivative. -/
theorem convergesOnCompactSubsets_iteratedDeriv {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hF : ∀ j, HolomorphicOn (F j) Ω)
    (hlim : ConvergesOnCompactSubsets F f Ω) (n : ℕ) :
    ConvergesOnCompactSubsets (fun j => iteratedDeriv n (F j)) (iteratedDeriv n f) Ω := by
  have hhol (n : ℕ) (j : ℕ) : HolomorphicOn (iteratedDeriv n (F j)) Ω := by
    induction n with
    | zero => simpa using hF j
    | succ n ih => simpa only [iteratedDeriv_succ] using holomorphicOn_deriv hΩ ih
  induction n with
  | zero => simpa using hlim
  | succ n ih =>
    simpa only [iteratedDeriv_succ] using
      (holomorphicOn_limit_and_deriv hΩ (hhol n) ih).2


/-- 10.6: power-series representability gives holomorphy. -/
theorem holomorphicOn_of_representableByPowerSeries {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : RepresentableByPowerSeries f Ω) : HolomorphicOn f Ω := by
  intro a ha
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ a ha
  obtain ⟨c, hc⟩ := hf a r hr hsub
  have hs : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ c) a := by
    rw [hasFPowerSeriesAt_iff']
    filter_upwards [Metric.ball_mem_nhds a hr] with z hz
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using hc z hz
  exact hs.analyticAt.differentiableAt

/-- 10.6: the derivative is again representable on every contained disc. -/
theorem representableByPowerSeries_deriv {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : RepresentableByPowerSeries f Ω) :
    RepresentableByPowerSeries (deriv f) Ω :=
  representableByPowerSeries_of_holomorphicOn
    (holomorphicOn_deriv hΩ (holomorphicOn_of_representableByPowerSeries hΩ hf))

/-- The coefficient/derivative equality in the corollary to 10.6. -/
theorem powerSeries_coefficient {f : ℂ → ℂ} {c : ℕ → ℂ} {a : ℂ} {r : ℝ}
    (hr : 0 < r) (hc : ∀ z ∈ disc a r, HasSum (fun n => c n * (z - a) ^ n) (f z))
    (n : ℕ) : (n.factorial : ℂ) * c n = iteratedDeriv n f a := by
  have hs : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ c) a := by
    rw [hasFPowerSeriesAt_iff']
    filter_upwards [Metric.ball_mem_nhds a hr] with z hz
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using hc z hz
  obtain ⟨ρ, hρ⟩ := hs
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    ← iteratedDeriv_eq_iteratedFDeriv] using hρ.factorial_smul (1 : ℂ) n

/-- Uniqueness in the unnumbered corollary to 10.6. -/
theorem powerSeries_coefficients_unique {f : ℂ → ℂ} {c d : ℕ → ℂ} {a : ℂ} {r : ℝ}
    (hr : 0 < r) (hc : ∀ z ∈ disc a r, HasSum (fun n => c n * (z - a) ^ n) (f z))
    (hd : ∀ z ∈ disc a r, HasSum (fun n => d n * (z - a) ^ n) (f z)) : c = d := by
  funext n
  apply mul_left_cancel₀ (show (n.factorial : ℂ) ≠ 0 by exact_mod_cast n.factorial_ne_zero)
  exact (powerSeries_coefficient hr hc n).trans (powerSeries_coefficient hr hd n).symm

/-- All derivatives remain representable, as stated in the corollary to 10.6. -/
theorem representableByPowerSeries_iteratedDeriv {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : RepresentableByPowerSeries f Ω) (k : ℕ) :
    RepresentableByPowerSeries (iteratedDeriv k f) Ω := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    simpa only [iteratedDeriv_succ] using representableByPowerSeries_deriv hΩ ih

/-- The corollary to 10.6, with the summation index shifted from `n ≥ k` to
`n ≥ 0`; the factorial ratio is the printed falling factorial. -/
theorem hasSum_iteratedDeriv_powerSeries {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : RepresentableByPowerSeries f Ω)
    {c : ℕ → ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r) (hsub : disc a r ⊆ Ω)
    (hc : ∀ z ∈ disc a r, HasSum (fun n => c n * (z - a) ^ n) (f z))
    (k : ℕ) {z : ℂ} (hz : z ∈ disc a r) :
    HasSum (fun n => ((n + k).factorial : ℂ) / n.factorial * c (n + k) * (z - a) ^ n)
      (iteratedDeriv k f z) := by
  have hk : HolomorphicOn (iteratedDeriv k f) Ω :=
    holomorphicOn_of_representableByPowerSeries hΩ
      (representableByPowerSeries_iteratedDeriv hΩ hf k)
  have hd : DifferentiableOn ℂ (iteratedDeriv k f) (Metric.ball a r) :=
    fun w hw => (hk w (hsub hw)).differentiableWithinAt
  convert Complex.hasSum_taylorSeries_on_ball hd hz using 1
  funext n
  have hi : iteratedDeriv n (iteratedDeriv k f) = iteratedDeriv (n + k) f := by
    simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]
  rw [hi, ← powerSeries_coefficient hr hc (n + k)]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

/-- 10.6's first derivative formula, with its summation index shifted by one. -/
theorem hasSum_deriv_powerSeries {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : RepresentableByPowerSeries f Ω)
    {c : ℕ → ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r) (hsub : disc a r ⊆ Ω)
    (hc : ∀ z ∈ disc a r, HasSum (fun n => c n * (z - a) ^ n) (f z))
    {z : ℂ} (hz : z ∈ disc a r) :
    HasSum (fun n : ℕ => ((n : ℂ) + 1) * c (n + 1) * (z - a) ^ n) (deriv f z) := by
  convert hasSum_iteratedDeriv_powerSeries hΩ hf hr hsub hc 1 hz using 1
  · funext n
    have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    simp only [Nat.factorial_succ, Nat.cast_mul, mul_div_cancel_right₀ _ hn,
      Nat.cast_add, Nat.cast_one]
  · simp


end RudinRCA.Chapter10
