import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope
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

/-- 10.25: the multiset counts zeros with their multiplicities. The theorem is
stated for every complex polynomial of degree `n`, and in particular for the
monic polynomial displayed in Rudin. -/
theorem number_of_polynomial_zeros (p : Polynomial ℂ) {n : ℕ}
    (_hn : 0 < n) (hdegree : p.natDegree = n) : p.roots.card = n := by
  rw [← Polynomial.Splits.natDegree_eq_card_roots (IsAlgClosed.splits p), hdegree]

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

end RudinRCA.Chapter10
