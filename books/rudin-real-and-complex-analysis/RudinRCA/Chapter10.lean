import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.RCLike
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

/-- 10.1: the closed disc is the closure of the open disc. -/
def closedDisc (a : ℂ) (r : ℝ) : Set ℂ := closure (disc a r)

theorem closedDisc_eq_closedBall (a : ℂ) {r : ℝ} (hr : 0 < r) :
    closedDisc a r = Metric.closedBall a r := by
  simp [closedDisc, disc, closure_ball, hr.ne']

theorem mem_closedDisc {a z : ℂ} {r : ℝ} (hr : 0 < r) :
    z ∈ closedDisc a r ↔ ‖z - a‖ ≤ r := by
  rw [closedDisc_eq_closedBall a hr]
  exact mem_closedBall_iff_norm

section ConnectedSets
variable {X : Type*} [TopologicalSpace X]

/-- 10.1: Rudin's connectedness convention permits the empty set. -/
def BookConnected (E : Set X) : Prop :=
  ¬ ∃ A B : Set X, E = A ∪ B ∧ A.Nonempty ∧ B.Nonempty ∧
    Disjoint (closure A) B ∧ Disjoint A (closure B)

theorem bookConnected_iff_isPreconnected (E : Set X) :
    BookConnected E ↔ IsPreconnected E := by
  classical
  constructor
  · intro h U V hU hV hcover hEU hEV
    by_contra hnone
    have hdisj : Disjoint (E ∩ U) V := by
      refine Set.disjoint_left.mpr ?_
      intro x hx hxV
      exact hnone ⟨x, hx.1, hx.2, hxV⟩
    have hdisj' : Disjoint U (E ∩ V) := by
      refine Set.disjoint_left.mpr ?_
      intro x hxU hx
      exact hnone ⟨x, hx.1, hxU, hx.2⟩
    apply h
    refine ⟨E ∩ U, E ∩ V, ?_, hEU, hEV,
      (hdisj.closure_left hV).mono_right inter_subset_right,
      (hdisj'.closure_right hU).mono_left inter_subset_right⟩
    exact (inter_union_distrib_left E U V).symm.trans (inter_eq_left.mpr hcover) |>.symm
  · intro h
    rintro ⟨A, B, rfl, hA, hB, hAB, hAB'⟩
    have hAsub : A ⊆ (closure B)ᶜ := by
      intro x hx hxB
      exact Set.disjoint_left.mp hAB' hx hxB
    have hBsub : B ⊆ (closure A)ᶜ := by
      intro x hx hxA
      exact Set.disjoint_left.mp hAB hxA hx
    obtain ⟨x, hx, hxU, hxV⟩ := h (closure B)ᶜ (closure A)ᶜ
      isClosed_closure.isOpen_compl isClosed_closure.isOpen_compl
      (union_subset_union hAsub hBsub)
      (hA.mono (fun _ hx ↦ ⟨Or.inl hx, hAsub hx⟩))
      (hB.mono (fun _ hx ↦ ⟨Or.inr hx, hBsub hx⟩))
    rcases hx with hx | hx
    · exact hxV (subset_closure hx)
    · exact hxU (subset_closure hx)

theorem not_bookConnected_iff_open_separation (E : Set X) :
    ¬ BookConnected E ↔ ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ E ⊆ U ∪ V ∧
      (E ∩ U).Nonempty ∧ (E ∩ V).Nonempty ∧ E ∩ (U ∩ V) = ∅ := by
  classical
  rw [bookConnected_iff_isPreconnected]
  simp only [IsPreconnected, not_forall, exists_prop, Set.not_nonempty_iff_eq_empty]

theorem closed_disconnected_decomposition {E : Set X} (hE : IsClosed E)
    (h : ¬ BookConnected E) :
    ∃ A B : Set X, IsClosed A ∧ IsClosed B ∧ A.Nonempty ∧ B.Nonempty ∧
      Disjoint A B ∧ E = A ∪ B := by
  classical
  obtain ⟨A, B, hEq, hA, hB, hAB, hAB'⟩ := not_not.mp h
  have hclA : closure A ⊆ E := closure_minimal (hEq ▸ subset_union_left) hE
  have hclB : closure B ⊆ E := closure_minimal (hEq ▸ subset_union_right) hE
  have hAc : IsClosed A := by
    apply closure_subset_iff_isClosed.mp
    intro x hx
    rcases hEq ▸ hclA hx with hxa | hxb
    · exact hxa
    · exact (Set.disjoint_left.mp hAB hx hxb).elim
  have hBc : IsClosed B := by
    apply closure_subset_iff_isClosed.mp
    intro x hx
    rcases hEq ▸ hclB hx with hxa | hxb
    · exact (Set.disjoint_left.mp hAB' hxa hx).elim
    · exact hxb
  exact ⟨A, B, hAc, hBc, hA, hB, hAB.mono_left subset_closure, hEq⟩

theorem open_disconnected_decomposition {E : Set X} (hE : IsOpen E)
    (h : ¬ BookConnected E) :
    ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ A.Nonempty ∧ B.Nonempty ∧
      Disjoint A B ∧ E = A ∪ B := by
  obtain ⟨U, V, hU, hV, hcover, hEU, hEV, hempty⟩ :=
    (not_bookConnected_iff_open_separation E).mp h
  refine ⟨E ∩ U, E ∩ V, hE.inter hU, hE.inter hV, hEU, hEV, ?_, ?_⟩
  · refine Set.disjoint_left.mpr ?_
    intro x hx hy
    have : x ∈ E ∩ (U ∩ V) := ⟨hx.1, hx.2, hy.2⟩
    rw [hempty] at this
    exact this
  · exact (inter_union_distrib_left E U V).symm.trans (inter_eq_left.mpr hcover) |>.symm

theorem bookConnected_empty : BookConnected (∅ : Set X) :=
  (bookConnected_iff_isPreconnected _).mpr isPreconnected_empty

theorem bookConnected_singleton (x : X) : BookConnected ({x} : Set X) :=
  (bookConnected_iff_isPreconnected _).mpr isPreconnected_singleton

/-- The component in 10.1 is the union of all connected subsets containing the point. -/
def bookComponent (E : Set X) (x : X) : Set X :=
  ⋃₀ {C : Set X | C ⊆ E ∧ BookConnected C ∧ x ∈ C}

theorem connectedSubsets_containing_nonempty {E : Set X} {x : X} (hx : x ∈ E) :
    {C : Set X | C ⊆ E ∧ BookConnected C ∧ x ∈ C}.Nonempty := by
  exact ⟨{x}, singleton_subset_iff.mpr hx, bookConnected_singleton x, mem_singleton x⟩

theorem bookComponent_eq_connectedComponentIn (E : Set X) (x : X) :
    bookComponent E x = connectedComponentIn E x := by
  apply Set.Subset.antisymm
  · rintro y ⟨C, ⟨hCE, hC, hxC⟩, hyC⟩
    exact ((bookConnected_iff_isPreconnected C).mp hC).subset_connectedComponentIn
      hxC hCE hyC
  · intro y hy
    have hxE : x ∈ E := connectedComponentIn_nonempty_iff.mp ⟨y, hy⟩
    exact Set.mem_sUnion.mpr ⟨connectedComponentIn E x,
      ⟨connectedComponentIn_subset E x,
        (bookConnected_iff_isPreconnected _).mpr isPreconnected_connectedComponentIn,
        mem_connectedComponentIn hxE⟩, hy⟩

theorem bookComponent_connected (E : Set X) (x : X) :
    BookConnected (bookComponent E x) := by
  rw [bookComponent_eq_connectedComponentIn, bookConnected_iff_isPreconnected]
  exact isPreconnected_connectedComponentIn

theorem bookComponent_maximal {E C : Set X} {x : X} (hCE : C ⊆ E)
    (hC : BookConnected C) (hxC : x ∈ C) : C ⊆ bookComponent E x := by
  intro y hy
  exact Set.mem_sUnion.mpr ⟨C, ⟨hCE, hC, hxC⟩, hy⟩

theorem mem_bookComponent {E : Set X} {x : X} (hx : x ∈ E) : x ∈ bookComponent E x := by
  rw [bookComponent_eq_connectedComponentIn]
  exact mem_connectedComponentIn hx

theorem bookComponent_subset (E : Set X) (x : X) : bookComponent E x ⊆ E := by
  rw [bookComponent_eq_connectedComponentIn]
  exact connectedComponentIn_subset E x

theorem bookComponent_maximal_connected_subset {E : Set X} {x : X} (hx : x ∈ E) :
    BookConnected (bookComponent E x) ∧ bookComponent E x ⊆ E ∧
      ∀ C, C ⊆ E → BookConnected C → bookComponent E x ⊆ C → C = bookComponent E x := by
  refine ⟨bookComponent_connected E x, bookComponent_subset E x, ?_⟩
  intro C hCE hC hcompC
  exact Set.Subset.antisymm (bookComponent_maximal hCE hC (hcompC (mem_bookComponent hx)))
    hcompC

/-- The set of components, without duplicate indexing by points. -/
def bookComponents (E : Set X) : Set (Set X) :=
  {C | ∃ x ∈ E, C = bookComponent E x}

theorem sUnion_bookComponents (E : Set X) : ⋃₀ bookComponents E = E := by
  apply Set.Subset.antisymm
  · rintro y ⟨C, ⟨x, hx, rfl⟩, hy⟩
    rw [bookComponent_eq_connectedComponentIn] at hy
    exact connectedComponentIn_subset E x hy
  · intro y hy
    refine Set.mem_sUnion.mpr ⟨bookComponent E y, ⟨y, hy, rfl⟩, ?_⟩
    rw [bookComponent_eq_connectedComponentIn]
    exact mem_connectedComponentIn hy

theorem bookComponents_pairwise_disjoint (E : Set X) :
    (bookComponents E).Pairwise Disjoint := by
  rintro C ⟨x, hx, rfl⟩ D ⟨y, hy, rfl⟩ hne
  refine Set.disjoint_left.mpr ?_
  intro z hzx hzy
  apply hne
  simp only [bookComponent_eq_connectedComponentIn] at hzx hzy ⊢
  exact (connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm

end ConnectedSets

theorem disc_isRegion (a : ℂ) {r : ℝ} (hr : 0 < r) : IsRegion (disc a r) := by
  exact ⟨Metric.isOpen_ball, (convex_ball a r).isConnected ⟨a, Metric.mem_ball_self hr⟩⟩

theorem isRegion_iff_bookConnected (Ω : Set ℂ) :
    IsRegion Ω ↔ Ω.Nonempty ∧ BookConnected Ω ∧ IsOpen Ω := by
  simp only [IsRegion, IsConnected, bookConnected_iff_isPreconnected]
  tauto

/-- 10.1: the open discs contained in an open set cover that set. -/
theorem open_eq_sUnion_discs {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    Ω = ⋃₀ {D : Set ℂ | ∃ a r, 0 < r ∧ D = disc a r ∧ D ⊆ Ω} := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ z hz
    exact Set.mem_sUnion.mpr ⟨disc z r, ⟨z, r, hr, rfl, hsub⟩,
      Metric.mem_ball_self hr⟩
  · rintro z ⟨D, ⟨a, r, hr, rfl, hsub⟩, hz⟩
    exact hsub hz

theorem bookComponent_isRegion {Ω : Set ℂ} (hΩ : IsOpen Ω) {z : ℂ} (hz : z ∈ Ω) :
    IsRegion (bookComponent Ω z) := by
  rw [bookComponent_eq_connectedComponentIn]
  exact ⟨hΩ.connectedComponentIn, isConnected_connectedComponentIn_iff.mpr hz⟩

/-- 10.1: every open plane set is the union of pairwise disjoint regions. -/
theorem open_eq_sUnion_disjoint_regions {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    ∃ ℛ : Set (Set ℂ), (∀ R ∈ ℛ, IsRegion R) ∧ ℛ.Pairwise Disjoint ∧ Ω = ⋃₀ ℛ := by
  refine ⟨bookComponents Ω, ?_, bookComponents_pairwise_disjoint Ω,
    (sUnion_bookComponents Ω).symm⟩
  rintro R ⟨z, hz, rfl⟩
  exact bookComponent_isRegion hΩ hz

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

/-- 10.18: the zeros in the stated domain. -/
def zeroSet (f : ℂ → ℂ) (Ω : Set ℂ) : Set ℂ := {z ∈ Ω | f z = 0}

/-- 10.18: a holomorphic function on a region is identically zero or its zero set has
no limit point in that region. -/
theorem zeroSet_eq_or_no_accumulation {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsRegion Ω) (hf : HolomorphicOn f Ω) :
    zeroSet f Ω = Ω ∨ ∀ z ∈ Ω, ¬ AccPt z (𝓟 (zeroSet f Ω)) := by
  have ha : AnalyticOnNhd ℂ f Ω :=
    ((holomorphicOn_iff_differentiableOn hΩ.1).mp hf).analyticOnNhd hΩ.1
  rcases ha.eqOn_zero_or_eventually_ne_zero_of_preconnected hΩ.2.isPreconnected with hzero | hne
  · left
    ext z
    simp only [zeroSet, mem_ofPred_eq, and_iff_left_iff_imp]
    exact fun hz => hzero hz
  · right
    have hcod : {z | f z ≠ 0} ∈ codiscreteWithin Ω := hne
    have heq : Ω \ {z | f z ≠ 0} = zeroSet f Ω := by ext z; simp [zeroSet]
    rw [mem_codiscreteWithin_accPt, heq] at hcod
    exact hcod

/-- 10.18: the nontrivial zero set is at most countable. -/
theorem zeroSet_countable {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsRegion Ω) (hf : HolomorphicOn f Ω) (hne : ¬ Set.EqOn f 0 Ω) :
    (zeroSet f Ω).Countable := by
  have ha : AnalyticOnNhd ℂ f Ω :=
    ((holomorphicOn_iff_differentiableOn hΩ.1).mp hf).analyticOnNhd hΩ.1
  have hcod := (ha.eqOn_zero_or_eventually_ne_zero_of_preconnected
    hΩ.2.isPreconnected).resolve_left hne
  have hd : IsDiscrete (zeroSet f Ω) := by
    have hd' := isDiscrete_of_codiscreteWithin (s := {z | f z = 0}) hcod
    simpa only [zeroSet, Set.inter_comm, Set.inter_ofPred_eq_sep] using hd'
  exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hd

/-- 10.18: each compact subset of the region contains only finitely many zeros
of a holomorphic function which is not identically zero. -/
theorem zeroSet_inter_compact_finite {f : ℂ → ℂ} {Ω K : Set ℂ}
    (hΩ : IsRegion Ω) (hf : HolomorphicOn f Ω) (hne : ¬ Set.EqOn f 0 Ω)
    (hK : IsCompact K) (hsub : K ⊆ Ω) :
    (zeroSet f Ω ∩ K).Finite := by
  have ha : AnalyticOnNhd ℂ f Ω :=
    ((holomorphicOn_iff_differentiableOn hΩ.1).mp hf).analyticOnNhd hΩ.1
  have hcod := (ha.eqOn_zero_or_eventually_ne_zero_of_preconnected
    hΩ.2.isPreconnected).resolve_left hne
  have hfin := hK.finite_sdiff_of_mem_codiscreteWithin
    (Filter.codiscreteWithin_mono hsub hcod)
  have heq : K \ {z | f z ≠ 0} = zeroSet f Ω ∩ K := by
    ext z
    simp only [Set.mem_sdiff, mem_ofPred_eq, not_not, zeroSet, mem_inter_iff]
    exact ⟨fun hz => ⟨⟨hsub hz.1, hz.2⟩, hz.1⟩, fun hz => ⟨hz.2, hz.1.2⟩⟩
  rwa [heq] at hfin

/-- 10.18: a zero of a nonzero holomorphic function has a unique positive order,
with its holomorphic factor defined on the whole original region. -/
theorem existsUnique_zero_order {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsRegion Ω) (hf : HolomorphicOn f Ω) (hne : ¬ Set.EqOn f 0 Ω)
    {a : ℂ} (ha : a ∈ Ω) (hfa : f a = 0) :
    ∃! m : ℕ, 0 < m ∧ ∃ g : ℂ → ℂ, HolomorphicOn g Ω ∧ g a ≠ 0 ∧
      ∀ z ∈ Ω, f z = (z - a) ^ m * g z := by
  have han : AnalyticOnNhd ℂ f Ω :=
    ((holomorphicOn_iff_differentiableOn hΩ.1).mp hf).analyticOnNhd hΩ.1
  obtain ⟨p, hp⟩ := han a ha
  have hpne : p ≠ 0 := by
    intro hp0
    exact hne (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩ.2.isPreconnected ha
      (hp.locally_zero_iff.mpr hp0))
  let g : ℂ → ℂ := (Function.swap dslope a)^[p.order] f
  have hga : g a ≠ 0 := hp.iterate_dslope_fslope_ne_zero hpne
  have hfg : ∀ z : ℂ, f z = (z - a) ^ p.order * g z := by
    intro z
    simpa only [smul_eq_mul] using hp.eq_pow_order_mul_iterate_dslope z
  have hg : HolomorphicOn g Ω := by
    have hi : ∀ n : ℕ, DifferentiableOn ℂ ((Function.swap dslope a)^[n] f) Ω := by
      intro n
      induction n with
      | zero => exact (holomorphicOn_iff_differentiableOn hΩ.1).mp hf
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (Complex.differentiableOn_dslope (hΩ.1.mem_nhds ha)).mpr ih
    exact (holomorphicOn_iff_differentiableOn hΩ.1).mpr (hi p.order)
  have hpos : 0 < p.order := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have he := hfg a
    simp only [hfa, hzero, pow_zero, one_mul] at he
    exact hga he.symm
  refine ⟨p.order, ⟨hpos, g, hg, hga, fun z _ => hfg z⟩, ?_⟩
  rintro m ⟨_, j, hj, hja, hjf⟩
  apply AnalyticAt.unique_eventuallyEq_pow_smul_nonzero (f := f) (z₀ := a)
  · refine ⟨j, ((holomorphicOn_iff_differentiableOn hΩ.1).mp hj).analyticOnNhd hΩ.1 a ha,
      hja, ?_⟩
    filter_upwards [hΩ.1.mem_nhds ha] with z hz
    simpa only [smul_eq_mul] using hjf z hz
  · refine ⟨g, ((holomorphicOn_iff_differentiableOn hΩ.1).mp hg).analyticOnNhd hΩ.1 a ha,
      hga, ?_⟩
    exact Filter.Eventually.of_forall fun z => by simpa only [smul_eq_mul] using hfg z

/-- The identity-theorem corollary to 10.18, with an arbitrary agreement set
having a limit point in the region. -/
theorem eqOn_of_accumulation {f g : ℂ → ℂ} {Ω E : Set ℂ}
    (hΩ : IsRegion Ω) (hf : HolomorphicOn f Ω) (hg : HolomorphicOn g Ω)
    (hE : Set.EqOn f g E) {a : ℂ} (ha : a ∈ Ω) (hacc : AccPt a (𝓟 E)) :
    Set.EqOn f g Ω := by
  have hfan : AnalyticOnNhd ℂ f Ω :=
    ((holomorphicOn_iff_differentiableOn hΩ.1).mp hf).analyticOnNhd hΩ.1
  have hgan : AnalyticOnNhd ℂ g Ω :=
    ((holomorphicOn_iff_differentiableOn hΩ.1).mp hg).analyticOnNhd hΩ.1
  apply hfan.eqOn_of_preconnected_of_frequently_eq hgan hΩ.2.isPreconnected ha
  rw [accPt_iff_frequently_nhdsNE] at hacc
  exact hacc.mono hE


/-- Rudin 10.18, gathering the zero-set dichotomy, global factorization with unique
positive order, and countability in the printed statement. -/
theorem theorem10_18 {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsRegion Ω) (hf : HolomorphicOn f Ω) :
    zeroSet f Ω = Ω ∨
      (∀ z ∈ Ω, ¬ AccPt z (𝓟 (zeroSet f Ω))) ∧
      (∀ a ∈ zeroSet f Ω, ∃! m : ℕ, 0 < m ∧
        ∃ g : ℂ → ℂ, HolomorphicOn g Ω ∧ g a ≠ 0 ∧
          ∀ z ∈ Ω, f z = (z - a) ^ m * g z) ∧
      (zeroSet f Ω).Countable := by
  by_cases hzero : Set.EqOn f 0 Ω
  · left
    ext z
    simp only [zeroSet, mem_ofPred_eq, and_iff_left_iff_imp]
    exact fun hz => hzero hz
  · right
    have hnot : zeroSet f Ω ≠ Ω := by
      intro h
      apply hzero
      intro z hz
      have hz' : z ∈ zeroSet f Ω := h.symm ▸ hz
      exact hz'.2
    refine ⟨(zeroSet_eq_or_no_accumulation hΩ hf).resolve_left hnot, ?_,
      zeroSet_countable hΩ hf hzero⟩
    intro a ha
    exact existsUnique_zero_order hΩ hf hzero ha.1 ha.2

/-- 10.18's observation for arbitrary values: apply the zero-set theorem to `f - c`. -/
theorem theorem10_18_levelSet {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsRegion Ω) (hf : HolomorphicOn f Ω) (c : ℂ) :
    {z ∈ Ω | f z = c} = Ω ∨
      (∀ z ∈ Ω, ¬ AccPt z (𝓟 {w ∈ Ω | f w = c})) ∧
      (∀ a ∈ {z ∈ Ω | f z = c}, ∃! m : ℕ, 0 < m ∧
        ∃ g : ℂ → ℂ, HolomorphicOn g Ω ∧ g a ≠ 0 ∧
          ∀ z ∈ Ω, f z - c = (z - a) ^ m * g z) ∧
      {z ∈ Ω | f z = c}.Countable := by
  simpa only [zeroSet, sub_eq_zero] using
    theorem10_18 (f := fun z => f z - c) hΩ
      (fun z hz => (hf z hz).sub_const c)

/-- The note after 10.18: on a disjoint union of two nonempty open sets, the
function which is zero on the first and one on the second is holomorphic and
has zeros accumulating in its domain without being identically zero. -/
theorem disconnected_open_zeroSet_example {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hUne : U.Nonempty) (hVne : V.Nonempty)
    (hdis : Disjoint U V) :
    ∃ f : ℂ → ℂ, HolomorphicOn f (U ∪ V) ∧ zeroSet f (U ∪ V) = U ∧
      (∃ a ∈ U ∪ V, AccPt a (𝓟 (zeroSet f (U ∪ V)))) ∧
      ¬ Set.EqOn f 0 (U ∪ V) := by
  classical
  let f : ℂ → ℂ := fun z => if z ∈ U then 0 else 1
  have hfu : ∀ z ∈ U, f z = 0 := by intro z hz; simp [f, hz]
  have hfv : ∀ z ∈ V, f z = 1 := by
    intro z hz
    have hzU : z ∉ U := fun hzu => Set.disjoint_left.mp hdis hzu hz
    simp [f, hzU]
  have heq : zeroSet f (U ∪ V) = U := by
    ext z
    constructor
    · intro hz
      rcases hz.1 with hzu | hzv
      · exact hzu
      · have : (1 : ℂ) = 0 := (hfv z hzv).symm.trans hz.2
        exact (one_ne_zero this).elim
    · exact fun hz => ⟨Or.inl hz, hfu z hz⟩
  refine ⟨f, ?_, heq, ?_, ?_⟩
  · intro z hz
    rcases hz with hzu | hzv
    · apply (differentiableAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hzu] with w hw
      exact hfu w hw
    · apply (differentiableAt_const (c := (1 : ℂ))).congr_of_eventuallyEq
      filter_upwards [hV.mem_nhds hzv] with w hw
      exact hfv w hw
  · obtain ⟨a, ha⟩ := hUne
    exact ⟨a, Or.inl ha, heq.symm ▸ hU.preperfect a ha⟩
  · intro hz
    obtain ⟨b, hb⟩ := hVne
    exact one_ne_zero ((hfv b hb).symm.trans (hz (Or.inr hb)))

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


section CompactConvergence
open Metric

/-- 10.27: the compact-uniform definition in the book's epsilon/N form,
including the strict index inequality `j > N`. -/
theorem convergesOnCompactSubsets_iff_epsilon {F : ℕ → ℂ → ℂ}
    {f : ℂ → ℂ} {Ω : Set ℂ} :
    ConvergesOnCompactSubsets F f Ω ↔
      ∀ K ⊆ Ω, IsCompact K → ∀ ε > 0, ∃ N : ℕ,
        ∀ j > N, ∀ z ∈ K, ‖F j z - f z‖ < ε := by
  constructor
  · intro h K hK hcompact ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (Metric.tendstoUniformlyOn_iff.mp (h K hK hcompact) ε hε)
    refine ⟨N, fun j hj z hz => ?_⟩
    have hbound := hN j hj.le z hz
    rwa [dist_eq_norm, norm_sub_rev] at hbound
  · intro h K hK hcompact
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := h K hK hcompact ε hε
    apply eventually_atTop.mpr
    refine ⟨N + 1, fun j hj z hz => ?_⟩
    have hbound := hN j (Nat.lt_of_succ_le hj) z hz
    rwa [dist_eq_norm, norm_sub_rev]

/-- 10.27's example: the powers converge uniformly on every compact subset
of the open unit disk. -/
theorem powers_convergeOnCompactSubsets :
    ConvergesOnCompactSubsets (fun n (z : ℂ) => z ^ n) (fun _ => 0) (disc 0 1) := by
  intro K hK hcompact
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  · obtain ⟨w, hw, hmax⟩ := hcompact.exists_isMaxOn hne continuous_norm.continuousOn
    have hnorm : ‖w‖ < 1 := mem_ball_zero_iff.mp (hK hw)
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg w) hnorm
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
    intro z hz
    have hbound := (pow_le_pow_left₀ (norm_nonneg z) (hmax hz) n).trans_lt hn
    simpa only [dist_zero_left, norm_pow] using hbound

/-- 10.27's example: convergence is not uniform on the whole open disk. -/
theorem powers_not_uniform_on_unitDisc :
    ¬ TendstoUniformlyOn (fun n (z : ℂ) => z ^ n) (fun _ => 0) atTop (disc 0 1) := by
  intro h
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp h (1 / 2) (by norm_num)).exists
  have hclosed : IsClosed {z : ℂ | ‖z ^ n‖ ≤ (1 : ℝ) / 2} :=
    isClosed_le (continuous_pow n).norm continuous_const
  have hsub : closure (disc (0 : ℂ) 1) ⊆ {z : ℂ | ‖z ^ n‖ ≤ (1 : ℝ) / 2} := by
    apply closure_minimal ?_ hclosed
    intro z hz
    exact le_of_lt (by simpa only [dist_zero_left] using hn z hz)
  have h1 : (1 : ℂ) ∈ closure (disc (0 : ℂ) 1) := by
    simp [disc, closure_ball]
  have hbad := hsub h1
  norm_num at hbad


end CompactConvergence

/-- 10.29: the divided difference is the derivative on the diagonal. -/
def dividedDifference (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  if z = w then deriv f z else (f z - f w) / (z - w)

@[simp] theorem dividedDifference_self (f : ℂ → ℂ) (z : ℂ) :
    dividedDifference f z z = deriv f z := by
  simp [dividedDifference]

theorem dividedDifference_of_ne {f : ℂ → ℂ} {z w : ℂ} (h : z ≠ w) :
    dividedDifference f z w = (f z - f w) / (z - w) := by
  simp [dividedDifference, h]

private theorem continuousAt_dividedDifference_diagonal {f : ℂ → ℂ} {a : ℂ}
    (hs : HasStrictDerivAt f (deriv f a) a)
    (hc : ContinuousAt (deriv f) a) :
    ContinuousAt (fun p : ℂ × ℂ ↦ dividedDifference f p.1 p.2) (a, a) := by
  have hr := (hasDerivAtFilter_iff_isLittleO.mp hs).tendsto_div_nhds_zero
  have hr' : Tendsto (fun p : ℂ × ℂ ↦
      (f p.1 - f p.2 - (p.1 - p.2) * deriv f a) / (p.1 - p.2) + deriv f a)
      (𝓝 (a, a)) (𝓝 (deriv f a)) := by
    simpa only [smul_eq_mul, zero_add] using hr.add_const (deriv f a)
  have hd : Tendsto (fun p : ℂ × ℂ ↦ deriv f p.1) (𝓝 (a, a)) (𝓝 (deriv f a)) :=
    hc.tendsto.comp continuousAt_fst.tendsto
  have hlim := hd.if' (p := fun p : ℂ × ℂ ↦ p.1 = p.2) hr'
  simp only [ContinuousAt, dividedDifference_self]
  convert hlim using 1
  funext p
  dsimp [dividedDifference]
  split_ifs with hp
  · rfl
  · have hn : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
    field_simp
    ring

/-- Rudin 10.29: continuity is joint on the product of the open domain with itself. -/
theorem node10_29_jointly_continuous {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : HolomorphicOn f Ω) :
    ContinuousOn (fun p : ℂ × ℂ ↦ dividedDifference f p.1 p.2) (Ω ×ˢ Ω) := by
  rintro ⟨z, w⟩ ⟨hz, hw⟩
  apply ContinuousAt.continuousWithinAt
  by_cases hzw : z = w
  · subst w
    apply continuousAt_dividedDifference_diagonal
    · have ha := ((holomorphicOn_iff_differentiableOn hΩ).mp hf).analyticAt (hΩ.mem_nhds hz)
      exact (ha.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
    · exact (holomorphicOn_deriv hΩ hf z hz).continuousAt
  · have hc : ContinuousAt (fun p : ℂ × ℂ ↦
        (f p.1 - f p.2) / (p.1 - p.2)) (z, w) :=
      ((hf z hz).continuousAt.comp continuousAt_fst).sub
        ((hf w hw).continuousAt.comp continuousAt_snd) |>.div
        (continuousAt_fst.sub continuousAt_snd) (sub_ne_zero.mpr hzw)
    apply hc.congr_of_eventuallyEq
    filter_upwards [(isOpen_ne_fun continuous_fst continuous_snd).mem_nhds hzw] with p hp
    exact dividedDifference_of_ne hp

/-- The literal free-`z` conclusion printed in 10.37 cannot hold: choose `z = w`.
This obstruction is independent of any properties of the index map. It does not
supply the path geometry or prove the intended corrected geometric theorem. -/
theorem node10_37_literal_conclusion_counterexample
    (index : ℂ → ℂ) {Dplus Dminus : Set ℂ}
    (hplus : Dplus.Nonempty) (hminus : Dminus.Nonempty) :
    ∃ x ∈ Dplus, ∃ w ∈ Dminus, ∃ z : ℂ, index z ≠ 1 + index w := by
  obtain ⟨x, hx⟩ := hplus
  obtain ⟨w, hw⟩ := hminus
  refine ⟨x, hx, w, hw, w, ?_⟩
  intro h
  have hzero : (0 : ℂ) = 1 := add_right_cancel (by simpa only [zero_add] using h)
  exact zero_ne_one hzero

end RudinRCA.Chapter10
