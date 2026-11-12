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
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.LogDeriv
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Chapter 10: elementary properties of holomorphic functions

All 44 numbered nodes (10.1–10.44) of Chapter 10 of Rudin, *Real and Complex Analysis*
(3rd ed., 1987) are formalized here, using general piecewise-`C¹` paths/chains/cycles and
their integral-defined index `Ind` rather than circles. For 10.37, both the literal
printed variable-mismatch counterexamples (`node10_37_literal_conclusion_counterexample`,
`node10_37_literal_geometric_counterexample`) and the explicitly repaired crosscut
index-jump theorem (`theorem10_37_corrected`, with `z ∈ D₊` and `w ∈ D₋`) are proved;
see `CHAPTER10-COVERAGE.md` for full node-by-node accounting. All functions below are
total representatives; theorems restrict their hypotheses and conclusions to the
specified open set.
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

/-! ### 10.8–10.11, 10.34, 10.37: Paths, chains, cycles, index, and the index-jump theorem -/

/-- 10.8: a curve on an arbitrary compact parameter interval `[α, β]` with `α < β`. -/
structure BookCurve (X : Type*) [TopologicalSpace X] where
  α : ℝ
  β : ℝ
  lt_endpoints : α < β
  toFun : ℝ → X
  continuousOn : ContinuousOn toFun (Icc α β)

namespace BookCurve

variable {X : Type*} [TopologicalSpace X]

/-- 10.8: the range (trace) `γ*` of a curve `γ`. -/
def trace (γ : BookCurve X) : Set X := γ.toFun '' Icc γ.α γ.β

/-- 10.8: a curve is closed when its start and end points coincide. -/
def IsClosed (γ : BookCurve X) : Prop := γ.toFun γ.α = γ.toFun γ.β

theorem le_endpoints (γ : BookCurve X) : γ.α ≤ γ.β := γ.lt_endpoints.le

theorem isCompact_trace (γ : BookCurve X) : IsCompact γ.trace :=
  isCompact_Icc.image_of_continuousOn γ.continuousOn

theorem trace_nonempty (γ : BookCurve X) : γ.trace.Nonempty :=
  ⟨γ.toFun γ.α, mem_image_of_mem _ (left_mem_Icc.mpr γ.le_endpoints)⟩

theorem mem_trace_of_mem_Icc (γ : BookCurve X) {t : ℝ} (ht : t ∈ Icc γ.α γ.β) :
    γ.toFun t ∈ γ.trace :=
  mem_image_of_mem _ ht

theorem start_mem_trace (γ : BookCurve X) : γ.toFun γ.α ∈ γ.trace :=
  γ.mem_trace_of_mem_Icc (left_mem_Icc.mpr γ.le_endpoints)

theorem end_mem_trace (γ : BookCurve X) : γ.toFun γ.β ∈ γ.trace :=
  γ.mem_trace_of_mem_Icc (right_mem_Icc.mpr γ.le_endpoints)

end BookCurve

/-- 10.8: a complex curve is piecewise continuously differentiable (a path) if `[α, β]` has a
finite strictly increasing partition `α = s₀ < s₁ < ⋯ < sₙ = β` such that on each `(sᵢ, sᵢ₊₁)`
`γ` has a derivative extending continuously to `[sᵢ, sᵢ₊₁]` (equivalently, finite one-sided
limits at `sᵢ⁺` and `sᵢ₊₁⁻`). -/
def IsPiecewiseC1 (γ : BookCurve ℂ) : Prop :=
  ∃ (n : ℕ) (s : Fin (n + 1) → ℝ) (d : Fin n → ℝ → ℂ),
    StrictMono s ∧ s 0 = γ.α ∧ s (Fin.last n) = γ.β ∧
    (∀ i : Fin n, ContinuousOn (d i) (Icc (s i.castSucc) (s i.succ))) ∧
    (∀ i : Fin n, ∀ t ∈ Ioo (s i.castSucc) (s i.succ),
      HasDerivWithinAt γ.toFun (d i t) (Icc γ.α γ.β) t)

/-- 10.8: equivalence between `IsPiecewiseC1` and existence of continuous derivatives on open
partition subintervals with finite one-sided limits at subinterval endpoints. -/
theorem isPiecewiseC1_iff_one_sided_limits (γ : BookCurve ℂ) :
    IsPiecewiseC1 γ ↔
      ∃ (n : ℕ) (s : Fin (n + 1) → ℝ),
        StrictMono s ∧ s 0 = γ.α ∧ s (Fin.last n) = γ.β ∧
        (∀ i : Fin n, ContinuousOn (derivWithin γ.toFun (Icc γ.α γ.β))
          (Ioo (s i.castSucc) (s i.succ))) ∧
        (∀ i : Fin n, ∀ t ∈ Ioo (s i.castSucc) (s i.succ),
          HasDerivWithinAt γ.toFun (derivWithin γ.toFun (Icc γ.α γ.β) t) (Icc γ.α γ.β) t) ∧
        (∀ i : Fin n, ∃ LR LL : ℂ,
          Tendsto (derivWithin γ.toFun (Icc γ.α γ.β)) (𝓝[>] (s i.castSucc)) (𝓝 LR) ∧
          Tendsto (derivWithin γ.toFun (Icc γ.α γ.β)) (𝓝[<] (s i.succ)) (𝓝 LL)) := by
  constructor
  · rintro ⟨n, s, d, hs, hs0, hsn, hdcont, hd⟩
    refine ⟨n, s, hs, hs0, hsn, ?_, ?_, ?_⟩
    · intro i
      have heq : EqOn (derivWithin γ.toFun (Icc γ.α γ.β)) (d i) (Ioo (s i.castSucc) (s i.succ)) := by
        intro t ht
        have hsub : Ioo (s i.castSucc) (s i.succ) ⊆ Ioo γ.α γ.β :=
          Ioo_subset_Ioo (hs0 ▸ hs.monotone (Fin.zero_le _)) (hsn ▸ hs.monotone (Fin.le_last _))
        have hnhds : Icc γ.α γ.β ∈ 𝓝 t := Icc_mem_nhds (hsub ht).1 (hsub ht).2
        rw [derivWithin_of_mem_nhds hnhds]
        exact ((hd i t ht).hasDerivAt hnhds).deriv
      exact (hdcont i).mono Ioo_subset_Icc_self |>.congr (fun t ht => heq ht)
    · intro i t ht
      have hsub : Ioo (s i.castSucc) (s i.succ) ⊆ Ioo γ.α γ.β :=
        Ioo_subset_Ioo (hs0 ▸ hs.monotone (Fin.zero_le _)) (hsn ▸ hs.monotone (Fin.le_last _))
      have hnhds : Icc γ.α γ.β ∈ 𝓝 t := Icc_mem_nhds (hsub ht).1 (hsub ht).2
      have hval : derivWithin γ.toFun (Icc γ.α γ.β) t = d i t := by
        rw [derivWithin_of_mem_nhds hnhds]
        exact ((hd i t ht).hasDerivAt hnhds).deriv
      rw [hval]
      exact hd i t ht
    · intro i
      have hlt : s i.castSucc < s i.succ := hs i.castSucc_lt_succ
      have hsub : Ioo (s i.castSucc) (s i.succ) ⊆ Ioo γ.α γ.β :=
        Ioo_subset_Ioo (hs0 ▸ hs.monotone (Fin.zero_le _)) (hsn ▸ hs.monotone (Fin.le_last _))
      have heq : EqOn (derivWithin γ.toFun (Icc γ.α γ.β)) (d i) (Ioo (s i.castSucc) (s i.succ)) := by
        intro t ht
        have hnhds : Icc γ.α γ.β ∈ 𝓝 t := Icc_mem_nhds (hsub ht).1 (hsub ht).2
        rw [derivWithin_of_mem_nhds hnhds]
        exact ((hd i t ht).hasDerivAt hnhds).deriv
      refine ⟨d i (s i.castSucc), d i (s i.succ), ?_, ?_⟩
      · have htend := ((hdcont i (s i.castSucc) (left_mem_Icc.mpr hlt.le)).mono Ioo_subset_Icc_self).congr'
          (eventuallyEq_nhdsWithin_of_eqOn heq.symm)
        rwa [nhdsWithin_Ioo_eq_nhdsGT hlt] at htend
      · have htend := ((hdcont i (s i.succ) (right_mem_Icc.mpr hlt.le)).mono Ioo_subset_Icc_self).congr'
          (eventuallyEq_nhdsWithin_of_eqOn heq.symm)
        rwa [nhdsWithin_Ioo_eq_nhdsLT hlt] at htend
  · rintro ⟨n, s, hs, hs0, hsn, hdcont, hd, hlim⟩
    choose LR LL hLR hLL using hlim
    let d : Fin n → ℝ → ℂ := fun i t =>
      if t = s i.castSucc then LR i
      else if t = s i.succ then LL i
      else derivWithin γ.toFun (Icc γ.α γ.β) t
    refine ⟨n, s, d, hs, hs0, hsn, ?_, ?_⟩
    · intro i t ht
      have hlt : s i.castSucc < s i.succ := hs i.castSucc_lt_succ
      by_cases h1 : t = s i.castSucc
      · subst h1
        have hd0 : d i (s i.castSucc) = LR i := by simp [d]
        rw [ContinuousWithinAt, hd0]
        have hIcc : 𝓝[Icc (s i.castSucc) (s i.succ)] (s i.castSucc) =
            pure (s i.castSucc) ⊔ 𝓝[Ioo (s i.castSucc) (s i.succ)] (s i.castSucc) := by
          rw [← Ioc_insert_left hlt.le, nhdsWithin_insert,
            nhdsWithin_Ioc_eq_nhdsGT hlt, nhdsWithin_Ioo_eq_nhdsGT hlt]
        rw [hIcc, tendsto_sup]
        refine ⟨hd0 ▸ tendsto_pure_nhds (d i) (s i.castSucc), ?_⟩
        rw [nhdsWithin_Ioo_eq_nhdsGT hlt]
        apply (hLR i).congr'
        filter_upwards [Ioo_mem_nhdsGT hlt] with u hu
        simp [d, hu.1.ne', hu.2.ne]
      · by_cases h2 : t = s i.succ
        · subst h2
          have hd1 : d i (s i.succ) = LL i := by simp [d, hlt.ne']
          rw [ContinuousWithinAt, hd1]
          have hIcc : 𝓝[Icc (s i.castSucc) (s i.succ)] (s i.succ) =
              pure (s i.succ) ⊔ 𝓝[Ioo (s i.castSucc) (s i.succ)] (s i.succ) := by
            rw [← Ico_insert_right hlt.le, nhdsWithin_insert,
              nhdsWithin_Ico_eq_nhdsLT hlt, nhdsWithin_Ioo_eq_nhdsLT hlt]
          rw [hIcc, tendsto_sup]
          refine ⟨hd1 ▸ tendsto_pure_nhds (d i) (s i.succ), ?_⟩
          rw [nhdsWithin_Ioo_eq_nhdsLT hlt]
          apply (hLL i).congr'
          filter_upwards [Ioo_mem_nhdsLT hlt] with u hu
          simp [d, hu.1.ne', hu.2.ne]
        · have hmem : t ∈ Ioo (s i.castSucc) (s i.succ) :=
            ⟨lt_of_le_of_ne ht.1 (Ne.symm h1), lt_of_le_of_ne ht.2 h2⟩
          have hc := (hdcont i t hmem).continuousAt (Ioo_mem_nhds hmem.1 hmem.2)
          apply ContinuousAt.continuousWithinAt
          apply hc.congr_of_eventuallyEq
          filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with u hu
          simp [d, hu.1.ne', hu.2.ne]
    · intro i t ht
      have hval : d i t = derivWithin γ.toFun (Icc γ.α γ.β) t := by
        simp [d, ht.1.ne', ht.2.ne]
      rw [hval]
      exact hd i t ht

/-- Build `IsPiecewiseC1` from any finite break set `S ⊆ [α, β]` containing `α` and `β`. -/
private theorem isPiecewiseC1_of_finset (γ : BookCurve ℂ) (S : Finset ℝ)
    (hα : γ.α ∈ S) (hβ : γ.β ∈ S) (hsub : (S : Set ℝ) ⊆ Icc γ.α γ.β)
    (hpiece : ∀ a b : ℝ, γ.α ≤ a → a < b → b ≤ γ.β → Disjoint (S : Set ℝ) (Ioo a b) →
      ∃ d : ℝ → ℂ, ContinuousOn d (Icc a b) ∧
        ∀ t ∈ Ioo a b, HasDerivWithinAt γ.toFun (d t) (Icc γ.α γ.β) t) :
    IsPiecewiseC1 γ := by
  have hcard_gt1 : 1 < S.card :=
    Finset.one_lt_card.mpr ⟨γ.α, hα, γ.β, hβ, γ.lt_endpoints.ne⟩
  let n : ℕ := S.card - 1
  have hcard : S.card = n + 1 := (Nat.sub_add_cancel (Nat.le_of_lt hcard_gt1)).symm
  let s : Fin (n + 1) → ℝ := S.orderEmbOfFin hcard
  have hs : StrictMono s := (S.orderEmbOfFin hcard).strictMono
  have hs0 : s 0 = γ.α := by
    have h0 : s ⟨0, Nat.succ_pos n⟩ = S.min' (Finset.card_pos.mp (by omega)) :=
      Finset.orderEmbOfFin_zero hcard (Nat.succ_pos n)
    exact h0.trans (le_antisymm (Finset.min'_le S γ.α hα)
      (Finset.le_min' S _ _ fun x hx => (hsub hx).1))
  have hsn : s (Fin.last n) = γ.β := by
    have hl : s ⟨(n + 1) - 1, Nat.sub_lt (Nat.succ_pos n) (Nat.succ_pos 0)⟩ =
        S.max' (Finset.card_pos.mp (by omega)) :=
      Finset.orderEmbOfFin_last hcard (Nat.succ_pos n)
    exact hl.trans (le_antisymm (Finset.max'_le S _ _ fun x hx => (hsub hx).2)
      (Finset.le_max' S γ.β hβ))
  have hex : ∀ i : Fin n, ∃ d : ℝ → ℂ, ContinuousOn d (Icc (s i.castSucc) (s i.succ)) ∧
      ∀ t ∈ Ioo (s i.castSucc) (s i.succ), HasDerivWithinAt γ.toFun (d t) (Icc γ.α γ.β) t := by
    intro i
    apply hpiece (s i.castSucc) (s i.succ)
      (hs0 ▸ hs.monotone (Fin.zero_le _))
      (hs i.castSucc_lt_succ)
      (hsn ▸ hs.monotone (Fin.le_last _))
    rw [Set.disjoint_left]
    intro x hxS hxIoo
    have hxrange : x ∈ Set.range s := by
      simpa [s, Finset.range_orderEmbOfFin] using hxS
    obtain ⟨k, rfl⟩ := hxrange
    have hk1 : i.castSucc < k := hs.lt_iff_lt.mp hxIoo.1
    have hk2 : k < i.succ := hs.lt_iff_lt.mp hxIoo.2
    change (i : ℕ) < (k : ℕ) at hk1
    change (k : ℕ) < (i : ℕ) + 1 at hk2
    omega
  choose d hdcont hd using hex
  exact ⟨n, s, d, hs, hs0, hsn, hdcont, hd⟩

/-- An open interval `(a, b) ⊆ [s 0, s (last n)]` avoiding `range s` lies inside one `[s i, s (i+1)]`. -/
private theorem exists_piece_containing_interval {n : ℕ} {s : Fin (n + 1) → ℝ}
    (_hs : StrictMono s) {a b : ℝ} (ha : s 0 ≤ a) (hab : a < b) (hb : b ≤ s (Fin.last n))
    (hdisj : Disjoint (Set.range s) (Ioo a b)) :
    ∃ i : Fin n, s i.castSucc ≤ a ∧ b ≤ s i.succ := by
  set m := (a + b) / 2 with hm_def
  have hmIoo : m ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hmnot : m ∉ Set.range s := Set.disjoint_right.mp hdisj hmIoo
  let T : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => s j ≤ m)
  have hTne : T.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith [hmIoo.1]⟩⟩
  let j := T.max' hTne
  have hjle : s j ≤ m := (Finset.mem_filter.mp (T.max'_mem hTne)).2
  have hjlt : s j < m := lt_of_le_of_ne hjle fun heq => hmnot ⟨j, heq⟩
  have hjne : j ≠ Fin.last n := fun h => by
    have : s (Fin.last n) < m := h ▸ hjlt
    linarith [hmIoo.2]
  obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hjne
  rw [← hi] at hjlt
  have hsucc : m < s i.succ := by
    by_contra hge
    have hmax : i.succ ≤ j :=
      T.le_max' i.succ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hge⟩)
    rw [← hi] at hmax
    exact not_le.mpr i.castSucc_lt_succ hmax
  refine ⟨i, ?_, ?_⟩
  · by_contra hgt
    exact Set.disjoint_left.mp hdisj ⟨i.castSucc, rfl⟩ ⟨not_le.mp hgt, by linarith [hmIoo.2]⟩
  · by_contra hlt
    exact Set.disjoint_left.mp hdisj ⟨i.succ, rfl⟩ ⟨by linarith [hmIoo.1], not_le.mp hlt⟩

/-- 10.8: a path in `ℂ` is a piecewise continuously differentiable curve. -/
structure BookPath extends BookCurve ℂ where
  piecewiseC1 : IsPiecewiseC1 toBookCurve

/-- 10.8: path integral `∫_γ f(z) dz = ∫_α^β f(γ(t)) γ'(t) dt`. Using `derivWithin` on `[α, β]`
makes the integral independent of values of `γ.toFun` outside `[α, β]` while agreeing with the
ordinary derivative on every open partition subinterval. -/
def pathIntegral (f : ℂ → ℂ) (γ : BookCurve ℂ) : ℂ :=
  ∫ t in γ.α..γ.β, f (γ.toFun t) * derivWithin γ.toFun (Icc γ.α γ.β) t

/-- 10.8: length `∫_α^β |γ'(t)| dt` of a path. -/
def pathLength (γ : BookCurve ℂ) : ℝ :=
  ∫ t in γ.α..γ.β, ‖derivWithin γ.toFun (Icc γ.α γ.β) t‖

namespace BookPath

/-- Trace `γ*` of a path. -/
def trace (γ : BookPath) : Set ℂ := γ.toBookCurve.trace

/-- Closedness of a path (`γ(α) = γ(β)`). -/
def IsClosed (γ : BookPath) : Prop := γ.toBookCurve.IsClosed

theorem isCompact_trace (γ : BookPath) : IsCompact γ.trace := γ.toBookCurve.isCompact_trace

theorem trace_nonempty (γ : BookPath) : γ.trace.Nonempty := γ.toBookCurve.trace_nonempty

/-- Construct a single-piece `C¹` path on `[α, β]`. -/
def ofC1 {α β : ℝ} (hlt : α < β) (g d : ℝ → ℂ)
    (hg : ContinuousOn g (Icc α β)) (hd : ContinuousOn d (Icc α β))
    (hderiv : ∀ t ∈ Ioo α β, HasDerivWithinAt g (d t) (Icc α β) t) : BookPath where
  α := α
  β := β
  lt_endpoints := hlt
  toFun := g
  continuousOn := hg
  piecewiseC1 := by
    refine isPiecewiseC1_of_finset ⟨α, β, hlt, g, hg⟩ {α, β} (by simp) (by simp) ?_ ?_
    · intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact left_mem_Icc.mpr hlt.le
      · exact right_mem_Icc.mpr hlt.le
    · intro a b ha hab hb _
      exact ⟨d, hd.mono (Icc_subset_Icc ha hb), fun t ht =>
        hderiv t ⟨lt_of_le_of_lt ha ht.1, lt_of_lt_of_le ht.2 hb⟩⟩

/-- DerivWithin agrees with the piece derivative `d i` on `(s i, s (i+1))`. -/
private theorem derivWithin_eq_piece {γ : BookCurve ℂ} {n : ℕ} {s : Fin (n + 1) → ℝ}
    {d : Fin n → ℝ → ℂ} (hs : StrictMono s) (hs0 : s 0 = γ.α) (hsn : s (Fin.last n) = γ.β)
    (hd : ∀ i : Fin n, ∀ t ∈ Ioo (s i.castSucc) (s i.succ),
      HasDerivWithinAt γ.toFun (d i t) (Icc γ.α γ.β) t)
    (i : Fin n) {t : ℝ} (ht : t ∈ Ioo (s i.castSucc) (s i.succ)) :
    derivWithin γ.toFun (Icc γ.α γ.β) t = d i t := by
  have hsub : Ioo (s i.castSucc) (s i.succ) ⊆ Ioo γ.α γ.β :=
    Ioo_subset_Ioo (hs0 ▸ hs.monotone (Fin.zero_le _)) (hsn ▸ hs.monotone (Fin.le_last _))
  have hnhds : Icc γ.α γ.β ∈ 𝓝 t := Icc_mem_nhds (hsub ht).1 (hsub ht).2
  rw [derivWithin_of_mem_nhds hnhds]
  exact ((hd i t ht).hasDerivAt hnhds).deriv

/-- Subinterval integrability and equality with the continuous piece derivative. -/
private theorem piece_intervalIntegrable_and_eq {γ : BookCurve ℂ} {n : ℕ} {s : Fin (n + 1) → ℝ}
    {d : Fin n → ℝ → ℂ} (hs : StrictMono s) (hs0 : s 0 = γ.α) (hsn : s (Fin.last n) = γ.β)
    (hdcont : ∀ i : Fin n, ContinuousOn (d i) (Icc (s i.castSucc) (s i.succ)))
    (hd : ∀ i : Fin n, ∀ t ∈ Ioo (s i.castSucc) (s i.succ),
      HasDerivWithinAt γ.toFun (d i t) (Icc γ.α γ.β) t)
    {f : ℂ → ℂ} (hf : ContinuousOn f γ.trace) (i : Fin n) :
    IntervalIntegrable (fun t => f (γ.toFun t) * derivWithin γ.toFun (Icc γ.α γ.β) t)
      MeasureTheory.volume (s i.castSucc) (s i.succ) ∧
    (∫ t in s i.castSucc..s i.succ, f (γ.toFun t) * derivWithin γ.toFun (Icc γ.α γ.β) t) =
      ∫ t in s i.castSucc..s i.succ, f (γ.toFun t) * d i t := by
  have hlt : s i.castSucc < s i.succ := hs i.castSucc_lt_succ
  have hsub : Icc (s i.castSucc) (s i.succ) ⊆ Icc γ.α γ.β :=
    Icc_subset_Icc (hs0 ▸ hs.monotone (Fin.zero_le _)) (hsn ▸ hs.monotone (Fin.le_last _))
  have hcont : ContinuousOn (fun t => f (γ.toFun t) * d i t) (Icc (s i.castSucc) (s i.succ)) := by
    refine (hf.comp (γ.continuousOn.mono hsub) ?_).mul (hdcont i)
    intro t ht
    exact γ.mem_trace_of_mem_Icc (hsub ht)
  have hint_d : IntervalIntegrable (fun t => f (γ.toFun t) * d i t)
      MeasureTheory.volume (s i.castSucc) (s i.succ) :=
    hcont.intervalIntegrable_of_Icc hlt.le
  have hae : (fun t => f (γ.toFun t) * d i t) =ᵐ[MeasureTheory.volume.restrict
      (Set.uIoc (s i.castSucc) (s i.succ))]
      (fun t => f (γ.toFun t) * derivWithin γ.toFun (Icc γ.α γ.β) t) := by
    rw [Set.uIoc_of_le hlt.le, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    rw [derivWithin_eq_piece hs hs0 hsn hd i ht]
  exact ⟨hint_d.congr_ae hae, (intervalIntegral.integral_congr_ae_restrict hae).symm⟩

private theorem intervalIntegrable_fin_partition {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} : ∀ {n : ℕ} (s : Fin (n + 1) → ℝ),
    (∀ i : Fin n, IntervalIntegrable f MeasureTheory.volume (s i.castSucc) (s i.succ)) →
    IntervalIntegrable f MeasureTheory.volume (s 0) (s (Fin.last n))
  | 0, _, _ => IntervalIntegrable.refl
  | n + 1, s, hint => by
    have hstep := intervalIntegrable_fin_partition (fun j : Fin (n + 1) => s j.castSucc)
      (fun j => by
        have h := hint j.castSucc
        rwa [show j.castSucc.succ = j.succ.castSucc from Fin.ext (by simp)] at h)
    simpa using hstep.trans (hint (Fin.last n))

private theorem sum_integral_fin_partition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} : ∀ {n : ℕ} (s : Fin (n + 1) → ℝ),
    (∀ i : Fin n, IntervalIntegrable f MeasureTheory.volume (s i.castSucc) (s i.succ)) →
    (∑ i : Fin n, ∫ t in s i.castSucc..s i.succ, f t) = ∫ t in s 0..s (Fin.last n), f t
  | 0, _, _ => by simp
  | n + 1, s, hint => by
    let s' : Fin (n + 1) → ℝ := fun j => s j.castSucc
    have hint' : ∀ j : Fin n, IntervalIntegrable f MeasureTheory.volume (s' j.castSucc) (s' j.succ) :=
      fun j => by
        have h := hint j.castSucc
        rwa [show j.castSucc.succ = j.succ.castSucc from Fin.ext (by simp)] at h
    rw [Fin.sum_univ_castSucc]
    have hsum : (∑ i : Fin n, ∫ t in s i.castSucc.castSucc..s i.castSucc.succ, f t) =
        ∑ i : Fin n, ∫ t in s' i.castSucc..s' i.succ, f t := by
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp [s']
    rw [hsum, sum_integral_fin_partition s' hint']
    exact intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_fin_partition s' hint')
      (hint (Fin.last n))

/-- 10.8: for any continuous `f` on `γ*`, the path integrand is interval-integrable on `[α, β]`. -/
theorem intervalIntegrable_pathIntegral (γ : BookPath) {f : ℂ → ℂ} (hf : ContinuousOn f γ.trace) :
    IntervalIntegrable (fun t => f (γ.toFun t) * derivWithin γ.toFun (Icc γ.α γ.β) t)
      MeasureTheory.volume γ.α γ.β := by
  obtain ⟨n, s, d, hs, hs0, hsn, hdcont, hd⟩ := γ.piecewiseC1
  let g := fun t => f (γ.toFun t) * derivWithin γ.toFun (Icc γ.α γ.β) t
  change IntervalIntegrable g MeasureTheory.volume γ.α γ.β
  rw [← hs0, ← hsn]
  exact intervalIntegrable_fin_partition s
    (fun i => (piece_intervalIntegrable_and_eq hs hs0 hsn hdcont hd hf i).1)

/-- 10.8: partition sum formula for `pathIntegral`. -/
theorem pathIntegral_eq_sum_pieces (γ : BookPath) {f : ℂ → ℂ} (hf : ContinuousOn f γ.trace)
    {n : ℕ} {s : Fin (n + 1) → ℝ} {d : Fin n → ℝ → ℂ}
    (hs : StrictMono s) (hs0 : s 0 = γ.α) (hsn : s (Fin.last n) = γ.β)
    (hdcont : ∀ i : Fin n, ContinuousOn (d i) (Icc (s i.castSucc) (s i.succ)))
    (hd : ∀ i : Fin n, ∀ t ∈ Ioo (s i.castSucc) (s i.succ),
      HasDerivWithinAt γ.toFun (d i t) (Icc γ.α γ.β) t) :
    pathIntegral f γ.toBookCurve =
      ∑ i : Fin n, ∫ t in s i.castSucc..s i.succ, f (γ.toFun t) * d i t := by
  let g := fun t => f (γ.toFun t) * derivWithin γ.toFun (Icc γ.α γ.β) t
  change (∫ t in γ.α..γ.β, g t) = _
  rw [← hs0, ← hsn, ← sum_integral_fin_partition s
    (fun i => (piece_intervalIntegrable_and_eq hs hs0 hsn hdcont hd hf i).1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (piece_intervalIntegrable_and_eq hs hs0 hsn hdcont hd hf i).2

/-- 10.8: `‖γ'(t)‖` is interval-integrable on `[α, β]` and `0 ≤ pathLength γ`. -/
theorem intervalIntegrable_norm_deriv (γ : BookPath) :
    IntervalIntegrable (fun t => ‖derivWithin γ.toFun (Icc γ.α γ.β) t‖)
      MeasureTheory.volume γ.α γ.β := by
  have h := γ.intervalIntegrable_pathIntegral (f := fun _ => 1) continuousOn_const
  simpa only [one_mul] using h.norm

theorem pathLength_nonneg (γ : BookPath) : 0 ≤ pathLength γ.toBookCurve :=
  intervalIntegral.integral_nonneg γ.le_endpoints (fun _ _ => norm_nonneg _)

/-- 10.8: `|∫_γ f(z) dz| ≤ M · length(γ)` whenever `|f(z)| ≤ M` on `γ*`. -/
theorem norm_pathIntegral_le (γ : BookPath) {f : ℂ → ℂ} (_hf : ContinuousOn f γ.trace)
    {M : ℝ} (hM : ∀ z ∈ γ.trace, ‖f z‖ ≤ M) :
    ‖pathIntegral f γ.toBookCurve‖ ≤ M * pathLength γ.toBookCurve := by
  unfold pathIntegral pathLength
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le γ.le_endpoints ?_
    (γ.intervalIntegrable_norm_deriv.const_mul M)
  filter_upwards with t ht
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (hM _ (γ.mem_trace_of_mem_Icc (Ioc_subset_Icc_self ht))) (norm_nonneg _)

theorem pathIntegral_congr {f g : ℂ → ℂ} (γ : BookCurve ℂ) (hfg : EqOn f g γ.trace) :
    pathIntegral f γ = pathIntegral g γ := by
  unfold pathIntegral
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le γ.le_endpoints] at ht
  rw [hfg (γ.mem_trace_of_mem_Icc ht)]

theorem pathIntegral_add (γ : BookPath) {f g : ℂ → ℂ}
    (hf : ContinuousOn f γ.trace) (hg : ContinuousOn g γ.trace) :
    pathIntegral (fun z => f z + g z) γ.toBookCurve =
      pathIntegral f γ.toBookCurve + pathIntegral g γ.toBookCurve := by
  unfold pathIntegral
  simp only [add_mul]
  exact intervalIntegral.integral_add (γ.intervalIntegrable_pathIntegral hf)
    (γ.intervalIntegrable_pathIntegral hg)

theorem pathIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (γ : BookCurve ℂ) :
    pathIntegral (fun z => c * f z) γ = c * pathIntegral f γ := by
  unfold pathIntegral
  simp only [mul_assoc, intervalIntegral.integral_const_mul]

theorem pathIntegral_sub (γ : BookPath) {f g : ℂ → ℂ}
    (hf : ContinuousOn f γ.trace) (hg : ContinuousOn g γ.trace) :
    pathIntegral (fun z => f z - g z) γ.toBookCurve =
      pathIntegral f γ.toBookCurve - pathIntegral g γ.toBookCurve := by
  unfold pathIntegral
  simp only [sub_mul]
  exact intervalIntegral.integral_sub (γ.intervalIntegrable_pathIntegral hf)
    (γ.intervalIntegrable_pathIntegral hg)

private theorem fin_rev_castSucc {n : ℕ} (i : Fin n) : (Fin.rev i).castSucc = Fin.rev i.succ := by
  ext; simp [Fin.rev]; try omega

private theorem fin_rev_succ {n : ℕ} (i : Fin n) : (Fin.rev i).succ = Fin.rev i.castSucc := by
  ext; simp [Fin.rev]; try omega

/-- 10.8: opposite (reversed) path `γ⁻` on `[α, β]`, defined by `t ↦ γ(α + β - t)`. -/
def reverse (γ : BookPath) : BookPath where
  α := γ.α
  β := γ.β
  lt_endpoints := γ.lt_endpoints
  toFun := fun t => γ.toFun (γ.α + γ.β - t)
  continuousOn := γ.continuousOn.comp (continuous_const.sub continuous_id).continuousOn
    (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  piecewiseC1 := by
    obtain ⟨n, s, d, hs, hs0, hsn, hdcont, hd⟩ := γ.piecewiseC1
    let s' : Fin (n + 1) → ℝ := fun i => γ.α + γ.β - s (Fin.rev i)
    let d' : Fin n → ℝ → ℂ := fun i t => -d (Fin.rev i) (γ.α + γ.β - t)
    refine ⟨n, s', d', ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      dsimp [s']
      have hrev : Fin.rev j < Fin.rev i := Fin.rev_lt_rev.mpr hij
      linarith [hs hrev]
    · simp [s', hsn]
    · simp [s', hs0]
    · intro i
      refine ((hdcont (Fin.rev i)).comp (continuousOn_const.sub continuousOn_id) ?_).neg
      intro t ht
      dsimp [s'] at ht
      rw [fin_rev_castSucc, fin_rev_succ]
      simp only [Pi.sub_apply, id_eq]
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · intro i t ht
      dsimp [s'] at ht
      have ht' : γ.α + γ.β - t ∈ Ioo (s (Fin.rev i).castSucc) (s (Fin.rev i).succ) := by
        rw [fin_rev_castSucc, fin_rev_succ]
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hsub : Ioo (s (Fin.rev i).castSucc) (s (Fin.rev i).succ) ⊆ Ioo γ.α γ.β :=
        Ioo_subset_Ioo (hs0 ▸ hs.monotone (Fin.zero_le _)) (hsn ▸ hs.monotone (Fin.le_last _))
      have huIoo := hsub ht'
      have hg : HasDerivAt γ.toFun (d (Fin.rev i) (γ.α + γ.β - t)) (γ.α + γ.β - t) :=
        (hd (Fin.rev i) _ ht').hasDerivAt (Icc_mem_nhds huIoo.1 huIoo.2)
      have hlin : HasDerivAt (fun u : ℝ => γ.α + γ.β - u) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (γ.α + γ.β)
      simpa [d', Function.comp_def] using (hg.scomp t hlin).hasDerivWithinAt

@[simp] theorem reverse_trace (γ : BookPath) : γ.reverse.trace = γ.trace := by
  ext z
  simp only [trace, BookCurve.trace, reverse, mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨γ.α + γ.β - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨γ.α + γ.β - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by ring_nf⟩

@[simp] theorem reverse_start (γ : BookPath) : γ.reverse.toFun γ.reverse.α = γ.toFun γ.β := by
  simp [reverse]

@[simp] theorem reverse_end (γ : BookPath) : γ.reverse.toFun γ.reverse.β = γ.toFun γ.α := by
  simp [reverse]

theorem reverse_isClosed {γ : BookPath} (h : γ.IsClosed) : γ.reverse.IsClosed := by
  simpa [IsClosed, BookCurve.IsClosed, reverse] using h.symm

/-- 10.8: reversing orientation negates the path integral. -/
theorem pathIntegral_reverse (γ : BookPath) {f : ℂ → ℂ} (hf : ContinuousOn f γ.trace) :
    pathIntegral f γ.reverse.toBookCurve = -pathIntegral f γ.toBookCurve := by
  obtain ⟨n, s, d, hs, hs0, hsn, hdcont, hd⟩ := γ.piecewiseC1
  let s' : Fin (n + 1) → ℝ := fun i => γ.α + γ.β - s (Fin.rev i)
  let d' : Fin n → ℝ → ℂ := fun i t => -d (Fin.rev i) (γ.α + γ.β - t)
  have hs' : StrictMono s' := fun i j hij => by
    dsimp [s']; linarith [hs (Fin.rev_lt_rev.mpr hij)]
  have hs0' : s' 0 = γ.reverse.α := by simp [s', reverse, hsn]
  have hsn' : s' (Fin.last n) = γ.reverse.β := by simp [s', reverse, hs0]
  have hdcont' : ∀ i : Fin n, ContinuousOn (d' i) (Icc (s' i.castSucc) (s' i.succ)) := by
    intro i
    refine ((hdcont (Fin.rev i)).comp (continuousOn_const.sub continuousOn_id) ?_).neg
    intro t ht
    dsimp [s'] at ht
    rw [fin_rev_castSucc, fin_rev_succ]
    simp only [Pi.sub_apply, id_eq]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hd' : ∀ i : Fin n, ∀ t ∈ Ioo (s' i.castSucc) (s' i.succ),
      HasDerivWithinAt γ.reverse.toFun (d' i t) (Icc γ.reverse.α γ.reverse.β) t := by
    intro i t ht
    dsimp [s'] at ht
    have ht' : γ.α + γ.β - t ∈ Ioo (s (Fin.rev i).castSucc) (s (Fin.rev i).succ) := by
      rw [fin_rev_castSucc, fin_rev_succ]
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hsub : Ioo (s (Fin.rev i).castSucc) (s (Fin.rev i).succ) ⊆ Ioo γ.α γ.β :=
      Ioo_subset_Ioo (hs0 ▸ hs.monotone (Fin.zero_le _)) (hsn ▸ hs.monotone (Fin.le_last _))
    have huIoo := hsub ht'
    have hg : HasDerivAt γ.toFun (d (Fin.rev i) (γ.α + γ.β - t)) (γ.α + γ.β - t) :=
      (hd (Fin.rev i) _ ht').hasDerivAt (Icc_mem_nhds huIoo.1 huIoo.2)
    have hlin : HasDerivAt (fun u : ℝ => γ.α + γ.β - u) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (γ.α + γ.β)
    simpa [reverse, d', Function.comp_def] using (hg.scomp t hlin).hasDerivWithinAt
  have hf' : ContinuousOn f γ.reverse.trace := by rwa [reverse_trace]
  rw [γ.reverse.pathIntegral_eq_sum_pieces hf' hs' hs0' hsn' hdcont' hd',
    γ.pathIntegral_eq_sum_pieces hf hs hs0 hsn hdcont hd, ← Finset.sum_neg_distrib,
    ← Equiv.sum_comp Fin.revPerm (fun j => -∫ t in s j.castSucc..s j.succ, f (γ.toFun t) * d j t)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply, reverse, d', mul_neg, intervalIntegral.integral_neg]
  congr 1
  have hsub_eq := intervalIntegral.integral_comp_sub_left
    (f := fun u => f (γ.toFun u) * d (Fin.rev i) u)
    (a := s' i.castSucc) (b := s' i.succ) (γ.α + γ.β)
  dsimp [s'] at hsub_eq ⊢
  rw [hsub_eq, ← fin_rev_castSucc, ← fin_rev_succ]
  have ha : γ.α + γ.β - (γ.α + γ.β - s (Fin.rev i).succ) = s (Fin.rev i).succ := by ring
  have hb : γ.α + γ.β - (γ.α + γ.β - s (Fin.rev i).castSucc) = s (Fin.rev i).castSucc := by ring
  rw [ha, hb, intervalIntegral.integral_symm]

/-- 10.8: reversing orientation preserves path length. -/
theorem pathLength_reverse (γ : BookPath) :
    pathLength γ.reverse.toBookCurve = pathLength γ.toBookCurve := by
  unfold pathLength
  have hsub := intervalIntegral.integral_comp_sub_left
    (f := fun u => ‖derivWithin γ.toFun (Icc γ.α γ.β) u‖)
    (a := γ.α) (b := γ.β) (γ.α + γ.β)
  have ha : γ.α + γ.β - γ.α = γ.β := by ring
  have hb : γ.α + γ.β - γ.β = γ.α := by ring
  rw [hb, ha] at hsub
  refine (intervalIntegral.integral_congr_ae_restrict ?_).trans hsub
  change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc γ.α γ.β)] _
  rw [Set.uIoc_of_le γ.le_endpoints, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  obtain ⟨n, s, d, hs, hs0, hsn, _, hd⟩ := γ.piecewiseC1
  have hfin : ((fun t => γ.α + γ.β - t) ⁻¹' Set.range s).Finite := by
    refine (Set.finite_range s).preimage ?_
    intro x _ y _ hxy; linarith
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo,
    hfin.countable.ae_notMem _] with t ht hnot
  dsimp [reverse]
  have hu : γ.α + γ.β - t ∈ Ioo γ.α γ.β := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hex : ∃ i : Fin n, γ.α + γ.β - t ∈ Ioo (s i.castSucc) (s i.succ) := by
    let T : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => s j ≤ γ.α + γ.β - t)
    have hTne : T.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith [hu.1, hs0]⟩⟩
    let j := T.max' hTne
    have hjle : s j ≤ γ.α + γ.β - t := (Finset.mem_filter.mp (T.max'_mem hTne)).2
    have hjlt : s j < γ.α + γ.β - t := lt_of_le_of_ne hjle fun heq => hnot ⟨j, heq⟩
    have hjne : j ≠ Fin.last n := fun h => by
      have : s (Fin.last n) < γ.α + γ.β - t := h ▸ hjlt
      linarith [hu.2, hsn]
    obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hjne
    rw [← hi] at hjlt
    refine ⟨i, hjlt, ?_⟩
    by_contra hge
    have hmax : i.succ ≤ j :=
      T.le_max' i.succ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hge⟩)
    rw [← hi] at hmax
    exact not_le.mpr i.castSucc_lt_succ hmax
  obtain ⟨i, hi⟩ := hex
  have hg : HasDerivAt γ.toFun (d i (γ.α + γ.β - t)) (γ.α + γ.β - t) :=
    (hd i _ hi).hasDerivAt (Icc_mem_nhds hu.1 hu.2)
  have hlin : HasDerivAt (fun u : ℝ => γ.α + γ.β - u) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub (γ.α + γ.β)
  have hrev_deriv : derivWithin (fun u => γ.toFun (γ.α + γ.β - u)) (Icc γ.α γ.β) t =
      -d i (γ.α + γ.β - t) := by
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    simpa [Function.comp_def] using (hg.scomp t hlin).deriv
  rw [hrev_deriv, derivWithin_eq_piece hs hs0 hsn hd i hi, norm_neg]

/-- Shift parameter interval of a path by `+ c`. -/
def shift (γ : BookPath) (c : ℝ) : BookPath where
  α := γ.α + c
  β := γ.β + c
  lt_endpoints := by linarith [γ.lt_endpoints]
  toFun := fun t => γ.toFun (t - c)
  continuousOn := γ.continuousOn.comp (continuousOn_id.sub continuousOn_const)
    (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  piecewiseC1 := by
    obtain ⟨n, s, d, hs, hs0, hsn, hdcont, hd⟩ := γ.piecewiseC1
    refine ⟨n, fun i => s i + c, fun i t => d i (t - c),
      fun i j hij => by dsimp; linarith [hs hij],
      by simp [hs0], by simp [hsn], ?_, ?_⟩
    · intro i
      exact (hdcont i).comp (continuousOn_id.sub continuousOn_const)
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    · intro i t ht
      dsimp at ht
      have ht' : t - c ∈ Ioo (s i.castSucc) (s i.succ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hsub : Ioo (s i.castSucc) (s i.succ) ⊆ Ioo γ.α γ.β :=
        Ioo_subset_Ioo (hs0 ▸ hs.monotone (Fin.zero_le _)) (hsn ▸ hs.monotone (Fin.le_last _))
      have hg : HasDerivAt γ.toFun (d i (t - c)) (t - c) :=
        (hd i _ ht').hasDerivAt (Icc_mem_nhds (hsub ht').1 (hsub ht').2)
      simpa [Function.comp_def] using
        (hg.scomp t ((hasDerivAt_id t).sub_const c)).hasDerivWithinAt

/-- Glue two piecewise-`C¹` paths sharing the same underlying function at `m` (`α < m < β`). -/
private def glue {α m β : ℝ} (g : ℝ → ℂ) (p₁ : BookPath) (p₂ : BookPath)
    (h1α : p₁.α = α) (h1β : p₁.β = m) (h2α : p₂.α = m) (h2β : p₂.β = β)
    (hg1 : EqOn g p₁.toFun (Icc α m)) (hg2 : EqOn g p₂.toFun (Icc m β)) : BookPath where
  α := α
  β := β
  lt_endpoints := by linarith [p₁.lt_endpoints, p₂.lt_endpoints]
  toFun := g
  continuousOn := by
    have hlt1 : α < m := h1α ▸ h1β ▸ p₁.lt_endpoints
    have hlt2 : m < β := h2α ▸ h2β ▸ p₂.lt_endpoints
    have hc1 : ContinuousOn g (Icc α m) := (h1α ▸ h1β ▸ p₁.continuousOn).congr hg1
    have hc2 : ContinuousOn g (Icc m β) := (h2α ▸ h2β ▸ p₂.continuousOn).congr hg2
    have hunion : Icc α β = Icc α m ∪ Icc m β := (Icc_union_Icc_eq_Icc hlt1.le hlt2.le).symm
    rw [hunion]
    exact hc1.union_of_isClosed hc2 isClosed_Icc isClosed_Icc
  piecewiseC1 := by
    have hlt1 : α < m := h1α ▸ h1β ▸ p₁.lt_endpoints
    have hlt2 : m < β := h2α ▸ h2β ▸ p₂.lt_endpoints
    have hc_all : ContinuousOn g (Icc α β) := by
      rw [(Icc_union_Icc_eq_Icc hlt1.le hlt2.le).symm]
      exact ((h1α ▸ h1β ▸ p₁.continuousOn).congr hg1).union_of_isClosed
        ((h2α ▸ h2β ▸ p₂.continuousOn).congr hg2) isClosed_Icc isClosed_Icc
    obtain ⟨n₁, s₁, d₁, hs₁, hs₁0, hs₁n, hdcont₁, hd₁⟩ := p₁.piecewiseC1
    obtain ⟨n₂, s₂, d₂, hs₂, hs₂0, hs₂n, hdcont₂, hd₂⟩ := p₂.piecewiseC1
    let S : Finset ℝ := Finset.univ.image s₁ ∪ Finset.univ.image s₂
    have hmS : m ∈ S := Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨Fin.last n₁, Finset.mem_univ _, hs₁n.trans h1β⟩)
    refine isPiecewiseC1_of_finset ⟨α, β, lt_trans hlt1 hlt2, g, hc_all⟩ S
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hs₁0.trans h1α⟩))
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨Fin.last n₂, Finset.mem_univ _, hs₂n.trans h2β⟩))
      ?_ ?_
    · intro x hx
      simp only [S, Finset.coe_union, Finset.coe_image, Finset.coe_univ, image_univ,
        mem_union, mem_range] at hx
      rcases hx with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · exact ⟨h1α ▸ hs₁0 ▸ hs₁.monotone (Fin.zero_le i),
          le_trans (h1β ▸ hs₁n ▸ hs₁.monotone (Fin.le_last i)) hlt2.le⟩
      · exact ⟨le_trans hlt1.le (h2α ▸ hs₂0 ▸ hs₂.monotone (Fin.zero_le j)),
          h2β ▸ hs₂n ▸ hs₂.monotone (Fin.le_last j)⟩
    · intro a b ha hab hb hdisj
      have hmnot : m ∉ Ioo a b := Set.disjoint_left.mp hdisj hmS
      by_cases hbm : b ≤ m
      · have hdisj₁ : Disjoint (Set.range s₁) (Ioo a b) :=
          hdisj.mono_left (by simp [S])
        obtain ⟨i, hia, hib⟩ := exists_piece_containing_interval hs₁
          (hs₁0.trans h1α ▸ ha) hab (hs₁n.trans h1β ▸ hbm) hdisj₁
        refine ⟨d₁ i, (hdcont₁ i).mono (Icc_subset_Icc hia hib), fun t ht => ?_⟩
        have ht1 : t ∈ Ioo α m := ⟨lt_of_le_of_lt ha ht.1, lt_of_lt_of_le ht.2 hbm⟩
        have hp := (hd₁ i t ⟨lt_of_le_of_lt hia ht.1, lt_of_lt_of_le ht.2 hib⟩).hasDerivAt
          (Icc_mem_nhds (h1α.symm ▸ ht1.1) (h1β.symm ▸ ht1.2))
        have hev : g =ᶠ[𝓝 t] p₁.toFun := by
          filter_upwards [Ioo_mem_nhds ht1.1 ht1.2] with u hu
          exact hg1 (Ioo_subset_Icc_self hu)
        exact (hp.congr_of_eventuallyEq hev).hasDerivWithinAt
      · have hma : m ≤ a := by
          by_contra ham
          exact hmnot ⟨not_le.mp ham, not_le.mp hbm⟩
        have hdisj₂ : Disjoint (Set.range s₂) (Ioo a b) :=
          hdisj.mono_left (by simp [S])
        obtain ⟨j, hja, hjb⟩ := exists_piece_containing_interval hs₂
          (hs₂0.trans h2α ▸ hma) hab (hs₂n.trans h2β ▸ hb) hdisj₂
        refine ⟨d₂ j, (hdcont₂ j).mono (Icc_subset_Icc hja hjb), fun t ht => ?_⟩
        have ht2 : t ∈ Ioo m β := ⟨lt_of_le_of_lt hma ht.1, lt_of_lt_of_le ht.2 hb⟩
        have hp := (hd₂ j t ⟨lt_of_le_of_lt hja ht.1, lt_of_lt_of_le ht.2 hjb⟩).hasDerivAt
          (Icc_mem_nhds (h2α.symm ▸ ht2.1) (h2β.symm ▸ ht2.2))
        have hev : g =ᶠ[𝓝 t] p₂.toFun := by
          filter_upwards [Ioo_mem_nhds ht2.1 ht2.2] with u hu
          exact hg2 (Ioo_subset_Icc_self hu)
        exact (hp.congr_of_eventuallyEq hev).hasDerivWithinAt

/-- 10.8: concatenation of two paths `γ₁` and `γ₂` with `γ₁(β₁) = γ₂(α₂)`, parametrized on
`[α₁, β₁ + (β₂ - α₂)]`. -/
def concat (γ₁ γ₂ : BookPath) (hjoin : γ₁.toFun γ₁.β = γ₂.toFun γ₂.α) : BookPath :=
  let g : ℝ → ℂ := fun t => if t ≤ γ₁.β then γ₁.toFun t else γ₂.toFun (t - γ₁.β + γ₂.α)
  glue (α := γ₁.α) (m := γ₁.β) (β := γ₁.β + (γ₂.β - γ₂.α))
    g γ₁ (γ₂.shift (γ₁.β - γ₂.α)) rfl rfl
    (by dsimp [shift]; ring) (by dsimp [shift]; ring)
    (fun t ht => by simp [g, ht.2])
    (fun t ht => by
      dsimp [g, shift]
      split_ifs with hteq
      · have htm : t = γ₁.β := le_antisymm hteq ht.1
        subst htm
        simpa using hjoin
      · congr 1; ring)

@[simp] theorem concat_start (γ₁ γ₂ : BookPath) (h : γ₁.toFun γ₁.β = γ₂.toFun γ₂.α) :
    (γ₁.concat γ₂ h).toFun (γ₁.concat γ₂ h).α = γ₁.toFun γ₁.α := by
  simp [concat, glue, γ₁.le_endpoints]

@[simp] theorem concat_end (γ₁ γ₂ : BookPath) (h : γ₁.toFun γ₁.β = γ₂.toFun γ₂.α) :
    (γ₁.concat γ₂ h).toFun (γ₁.concat γ₂ h).β = γ₂.toFun γ₂.β := by
  have hnle : ¬ (γ₁.β + (γ₂.β - γ₂.α) ≤ γ₁.β) := by linarith [γ₂.lt_endpoints]
  simp only [concat, glue, hnle, ↓reduceIte]
  congr 1; ring

theorem concat_trace (γ₁ γ₂ : BookPath) (h : γ₁.toFun γ₁.β = γ₂.toFun γ₂.α) :
    (γ₁.concat γ₂ h).trace = γ₁.trace ∪ γ₂.trace := by
  ext z
  simp only [trace, BookCurve.trace, concat, glue, mem_image, mem_union]
  constructor
  · rintro ⟨t, ht, rfl⟩
    split_ifs with hle
    · exact Or.inl ⟨t, ⟨ht.1, hle⟩, rfl⟩
    · exact Or.inr ⟨t - γ₁.β + γ₂.α, ⟨by linarith, by linarith [ht.2]⟩, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨t, ⟨ht.1, by linarith [ht.2, γ₂.lt_endpoints]⟩, by simp [ht.2]⟩
    · refine ⟨t - γ₂.α + γ₁.β, ⟨by linarith [ht.1, γ₁.lt_endpoints], by linarith [ht.2]⟩, ?_⟩
      by_cases hteq : t = γ₂.α
      · subst hteq; simp [h]
      · have hnle : ¬ (t - γ₂.α + γ₁.β ≤ γ₁.β) := by
          have : γ₂.α < t := lt_of_le_of_ne ht.1 (Ne.symm hteq)
          linarith
        simp only [hnle, ↓reduceIte]
        congr 1; ring

/-- 10.8: `∫_{γ₁ + γ₂} f = ∫_{γ₁} f + ∫_{γ₂} f`. -/
theorem pathIntegral_concat (γ₁ γ₂ : BookPath) (h : γ₁.toFun γ₁.β = γ₂.toFun γ₂.α)
    {f : ℂ → ℂ} (hf : ContinuousOn f ((γ₁.concat γ₂ h).trace)) :
    pathIntegral f (γ₁.concat γ₂ h).toBookCurve =
      pathIntegral f γ₁.toBookCurve + pathIntegral f γ₂.toBookCurve := by
  let γ := γ₁.concat γ₂ h
  have hγ_α : γ.α = γ₁.α := rfl
  have hγ_β : γ.β = γ₁.β + (γ₂.β - γ₂.α) := rfl
  have h1 : IntervalIntegrable (fun t => f (γ.toFun t) * derivWithin γ.toFun (Icc γ.α γ.β) t)
      MeasureTheory.volume γ₁.α γ₁.β := by
    refine (γ.intervalIntegrable_pathIntegral hf).mono_set ?_
    rw [Set.uIcc_of_le γ₁.le_endpoints, Set.uIcc_of_le γ.le_endpoints, hγ_α, hγ_β]
    exact Icc_subset_Icc le_rfl (by linarith [γ₂.lt_endpoints])
  have h2 : IntervalIntegrable (fun t => f (γ.toFun t) * derivWithin γ.toFun (Icc γ.α γ.β) t)
      MeasureTheory.volume γ₁.β γ.β := by
    refine (γ.intervalIntegrable_pathIntegral hf).mono_set ?_
    rw [Set.uIcc_of_le (by rw [hγ_β]; linarith [γ₂.lt_endpoints]),
      Set.uIcc_of_le γ.le_endpoints, hγ_α]
    exact Icc_subset_Icc γ₁.le_endpoints le_rfl
  change (∫ t in γ₁.α..γ.β, f (γ.toFun t) * derivWithin γ.toFun (Icc γ.α γ.β) t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  congr 1
  · apply intervalIntegral.integral_congr_ae_restrict
    rw [Set.uIoc_of_le γ₁.le_endpoints, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    have hval : γ.toFun t = γ₁.toFun t := by simp [γ, concat, glue, ht.2.le]
    have hev : γ.toFun =ᶠ[𝓝 t] γ₁.toFun := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      simp [γ, concat, glue, hu.2.le]
    have hd1 : derivWithin γ.toFun (Icc γ.α γ.β) t = deriv γ₁.toFun t := by
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds (by rw [hγ_α]; exact ht.1) (by rw [hγ_β]; linarith [ht.2, γ₂.lt_endpoints]))]
      exact hev.deriv_eq
    have hd2 : derivWithin γ₁.toFun (Icc γ₁.α γ₁.β) t = deriv γ₁.toFun t :=
      derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
    rw [hval, hd1, hd2]
  · have hshift := intervalIntegral.integral_comp_add_right
      (f := fun u => f (γ₂.toFun u) * derivWithin γ₂.toFun (Icc γ₂.α γ₂.β) u)
      (a := γ₁.β) (b := γ.β) (γ₂.α - γ₁.β)
    have ha : γ₁.β + (γ₂.α - γ₁.β) = γ₂.α := by ring
    have hb : γ.β + (γ₂.α - γ₁.β) = γ₂.β := by rw [hγ_β]; ring
    rw [ha, hb] at hshift
    refine (intervalIntegral.integral_congr_ae_restrict ?_).trans hshift
    have hle : γ₁.β ≤ γ.β := by rw [hγ_β]; linarith [γ₂.lt_endpoints]
    change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc γ₁.β γ.β)] _
    rw [Set.uIoc_of_le hle, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    have hnle : ¬ t ≤ γ₁.β := not_le.mpr ht.1
    have hval : γ.toFun t = γ₂.toFun (t + (γ₂.α - γ₁.β)) := by
      simp only [γ, concat, glue, hnle, ↓reduceIte]; congr 1; ring
    have hev : γ.toFun =ᶠ[𝓝 t] (fun u => γ₂.toFun (u + (γ₂.α - γ₁.β))) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      have hnleu : ¬ u ≤ γ₁.β := not_le.mpr hu.1
      simp only [γ, concat, glue, hnleu, ↓reduceIte]; congr 1; ring
    have hd1 : derivWithin γ.toFun (Icc γ.α γ.β) t = deriv γ₂.toFun (t + (γ₂.α - γ₁.β)) := by
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds (by rw [hγ_α]; exact lt_trans γ₁.lt_endpoints ht.1) ht.2),
        hev.deriv_eq, deriv_comp_add_const]
    have hd2 : derivWithin γ₂.toFun (Icc γ₂.α γ₂.β) (t + (γ₂.α - γ₁.β)) =
        deriv γ₂.toFun (t + (γ₂.α - γ₁.β)) :=
      derivWithin_of_mem_nhds (Icc_mem_nhds (by linarith [ht.1]) (by rw [hγ_β] at ht; linarith [ht.2]))
    rw [hval, hd1, hd2]

/-- 10.8: length is additive under concatenation. -/
theorem pathLength_concat (γ₁ γ₂ : BookPath) (h : γ₁.toFun γ₁.β = γ₂.toFun γ₂.α) :
    pathLength (γ₁.concat γ₂ h).toBookCurve =
      pathLength γ₁.toBookCurve + pathLength γ₂.toBookCurve := by
  let γ := γ₁.concat γ₂ h
  have hγ_α : γ.α = γ₁.α := rfl
  have hγ_β : γ.β = γ₁.β + (γ₂.β - γ₂.α) := rfl
  have h1 : IntervalIntegrable (fun t => ‖derivWithin γ.toFun (Icc γ.α γ.β) t‖)
      MeasureTheory.volume γ₁.α γ₁.β := by
    refine γ.intervalIntegrable_norm_deriv.mono_set ?_
    rw [Set.uIcc_of_le γ₁.le_endpoints, Set.uIcc_of_le γ.le_endpoints, hγ_α, hγ_β]
    exact Icc_subset_Icc le_rfl (by linarith [γ₂.lt_endpoints])
  have h2 : IntervalIntegrable (fun t => ‖derivWithin γ.toFun (Icc γ.α γ.β) t‖)
      MeasureTheory.volume γ₁.β γ.β := by
    refine γ.intervalIntegrable_norm_deriv.mono_set ?_
    rw [Set.uIcc_of_le (by rw [hγ_β]; linarith [γ₂.lt_endpoints]),
      Set.uIcc_of_le γ.le_endpoints, hγ_α]
    exact Icc_subset_Icc γ₁.le_endpoints le_rfl
  change (∫ t in γ₁.α..γ.β, ‖derivWithin γ.toFun (Icc γ.α γ.β) t‖) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  congr 1
  · apply intervalIntegral.integral_congr_ae_restrict
    rw [Set.uIoc_of_le γ₁.le_endpoints, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    have hev : γ.toFun =ᶠ[𝓝 t] γ₁.toFun := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      simp [γ, concat, glue, hu.2.le]
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds (by rw [hγ_α]; exact ht.1) (by rw [hγ_β]; linarith [ht.2, γ₂.lt_endpoints])),
      hev.deriv_eq, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  · have hshift := intervalIntegral.integral_comp_add_right
      (f := fun u => ‖derivWithin γ₂.toFun (Icc γ₂.α γ₂.β) u‖)
      (a := γ₁.β) (b := γ.β) (γ₂.α - γ₁.β)
    have ha : γ₁.β + (γ₂.α - γ₁.β) = γ₂.α := by ring
    have hb : γ.β + (γ₂.α - γ₁.β) = γ₂.β := by rw [hγ_β]; ring
    rw [ha, hb] at hshift
    refine (intervalIntegral.integral_congr_ae_restrict ?_).trans hshift
    have hle : γ₁.β ≤ γ.β := by rw [hγ_β]; linarith [γ₂.lt_endpoints]
    change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc γ₁.β γ.β)] _
    rw [Set.uIoc_of_le hle, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    have hev : γ.toFun =ᶠ[𝓝 t] (fun u => γ₂.toFun (u + (γ₂.α - γ₁.β))) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      have hnleu : ¬ u ≤ γ₁.β := not_le.mpr hu.1
      simp only [γ, concat, glue, hnleu, ↓reduceIte]; congr 1; ring
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds (by rw [hγ_α]; exact lt_trans γ₁.lt_endpoints ht.1) ht.2),
      hev.deriv_eq, deriv_comp_add_const,
      derivWithin_of_mem_nhds (Icc_mem_nhds (by linarith [ht.1]) (by rw [hγ_β] at ht; linarith [ht.2]))]

/-- Restrict a path `γ` on `[α, β]` to a subinterval `[u, v]` (`α ≤ u < v ≤ β`). -/
def restrict (γ : BookPath) {u v : ℝ} (hαu : γ.α ≤ u) (huv : u < v) (hvβ : v ≤ γ.β) : BookPath where
  α := u
  β := v
  lt_endpoints := huv
  toFun := γ.toFun
  continuousOn := γ.continuousOn.mono (Icc_subset_Icc hαu hvβ)
  piecewiseC1 := by
    obtain ⟨n, s, d, hs, hs0, hsn, hdcont, hd⟩ := γ.piecewiseC1
    let S : Finset ℝ := insert u (insert v ((Finset.univ.image s).filter (fun x => u ≤ x ∧ x ≤ v)))
    refine isPiecewiseC1_of_finset
      ⟨u, v, huv, γ.toFun, γ.continuousOn.mono (Icc_subset_Icc hαu hvβ)⟩ S
      (Finset.mem_insert_self _ _)
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      ?_ ?_
    · intro x hx
      simp only [S, Finset.coe_insert, Finset.coe_filter, mem_insert_iff, Set.mem_ofPred] at hx
      rcases hx with rfl | rfl | ⟨_, hux, hxv⟩
      · exact left_mem_Icc.mpr huv.le
      · exact right_mem_Icc.mpr huv.le
      · exact ⟨hux, hxv⟩
    · intro a b ha hab hb hdisj
      have hdisj_s : Disjoint (Set.range s) (Ioo a b) := by
        rw [Set.disjoint_left]
        intro x hxrange hxIoo
        rcases hxrange with ⟨k, rfl⟩
        refine Set.disjoint_left.mp hdisj ?_ hxIoo
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
            le_trans ha hxIoo.1.le, le_trans hxIoo.2.le hb⟩))
      obtain ⟨i, hia, hib⟩ := exists_piece_containing_interval hs
        (hs0 ▸ le_trans hαu ha) hab (hsn ▸ le_trans hb hvβ) hdisj_s
      refine ⟨d i, (hdcont i).mono (Icc_subset_Icc hia hib), fun t ht => ?_⟩
      have htIoo : t ∈ Ioo γ.α γ.β :=
        ⟨lt_of_le_of_lt (le_trans hαu ha) ht.1, lt_of_lt_of_le ht.2 (le_trans hb hvβ)⟩
      exact ((hd i t ⟨lt_of_le_of_lt hia ht.1, lt_of_lt_of_le ht.2 hib⟩).hasDerivAt
        (Icc_mem_nhds htIoo.1 htIoo.2)).hasDerivWithinAt

theorem restrict_trace_subset (γ : BookPath) {u v : ℝ}
    (hαu : γ.α ≤ u) (huv : u < v) (hvβ : v ≤ γ.β) :
    (γ.restrict hαu huv hvβ).trace ⊆ γ.trace :=
  Set.image_mono (Icc_subset_Icc hαu hvβ)

theorem pathIntegral_restrict (γ : BookPath) {u v : ℝ}
    (hαu : γ.α ≤ u) (huv : u < v) (hvβ : v ≤ γ.β) (f : ℂ → ℂ) :
    pathIntegral f (γ.restrict hαu huv hvβ).toBookCurve =
      ∫ t in u..v, f (γ.toFun t) * derivWithin γ.toFun (Icc γ.α γ.β) t := by
  unfold pathIntegral
  apply intervalIntegral.integral_congr_ae_restrict
  change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc u v)] _
  rw [Set.uIoc_of_le huv.le, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
  dsimp [restrict]
  have htIoo : t ∈ Ioo γ.α γ.β := ⟨lt_of_le_of_lt hαu ht.1, lt_of_lt_of_le ht.2 hvβ⟩
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),
    derivWithin_of_mem_nhds (Icc_mem_nhds htIoo.1 htIoo.2)]

/-- 10.8: orientation-preserving `C¹` reparametrization of a path. -/
def reparam (γ : BookPath) {α₁ β₁ : ℝ} (hlt₁ : α₁ < β₁) (φ dφ : ℝ → ℝ)
    (hφcont : ContinuousOn φ (Icc α₁ β₁))
    (hdφcont : ContinuousOn dφ (Icc α₁ β₁))
    (hφderiv : ∀ t ∈ Ioo α₁ β₁, HasDerivWithinAt φ (dφ t) (Icc α₁ β₁) t)
    (hdφnonneg : ∀ t ∈ Ioo α₁ β₁, 0 ≤ dφ t)
    (hφα : φ α₁ = γ.α) (hφβ : φ β₁ = γ.β) : BookPath where
  α := α₁
  β := β₁
  lt_endpoints := hlt₁
  toFun := γ.toFun ∘ φ
  continuousOn := by
    have hmono : MonotoneOn φ (Icc α₁ β₁) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc α₁ β₁) hφcont
      · rw [interior_Icc]
        exact fun t ht => ((hφderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro t ht
        rw [((hφderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
        exact hdφnonneg t ht
    refine γ.continuousOn.comp hφcont fun t ht => ?_
    exact ⟨hφα ▸ hmono (left_mem_Icc.mpr hlt₁.le) ht ht.1,
           hφβ ▸ hmono ht (right_mem_Icc.mpr hlt₁.le) ht.2⟩
  piecewiseC1 := by
    have hmono : MonotoneOn φ (Icc α₁ β₁) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc α₁ β₁) hφcont
      · rw [interior_Icc]
        exact fun t ht => ((hφderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro t ht
        rw [((hφderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
        exact hdφnonneg t ht
    have hc_comp : ContinuousOn (γ.toFun ∘ φ) (Icc α₁ β₁) :=
      γ.continuousOn.comp hφcont fun t ht =>
        ⟨hφα ▸ hmono (left_mem_Icc.mpr hlt₁.le) ht ht.1,
         hφβ ▸ hmono ht (right_mem_Icc.mpr hlt₁.le) ht.2⟩
    obtain ⟨n, s, d, hs, hs0, hsn, hdcont, hd⟩ := γ.piecewiseC1
    let K : Fin (n + 1) → Set ℝ := fun i => Icc α₁ β₁ ∩ φ ⁻¹' {s i}
    have hKcomp (i : Fin (n + 1)) : IsCompact (K i) :=
      IsCompact.of_isClosed_subset isCompact_Icc
        (hφcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
    have hKne (i : Fin (n + 1)) : (K i).Nonempty :=
      intermediate_value_Icc hlt₁.le hφcont
        ⟨hφα.symm ▸ hs0 ▸ hs.monotone (Fin.zero_le i),
         hφβ.symm ▸ hsn ▸ hs.monotone (Fin.le_last i)⟩
    let a : Fin (n + 1) → ℝ := fun i => sInf (K i)
    let b : Fin (n + 1) → ℝ := fun i => sSup (K i)
    have ha_mem (i : Fin (n + 1)) : a i ∈ K i :=
      (hKcomp i).isClosed.csInf_mem (hKne i) (hKcomp i).bddBelow
    have hb_mem (i : Fin (n + 1)) : b i ∈ K i :=
      (hKcomp i).isClosed.csSup_mem (hKne i) (hKcomp i).bddAbove
    have ha0 : a 0 = α₁ := le_antisymm
      (csInf_le (hKcomp 0).bddBelow ⟨left_mem_Icc.mpr hlt₁.le, by simp [hφα, hs0]⟩)
      (ha_mem 0).1.1
    have hbn : b (Fin.last n) = β₁ := le_antisymm (hb_mem (Fin.last n)).1.2
      (le_csSup (hKcomp (Fin.last n)).bddAbove ⟨right_mem_Icc.mpr hlt₁.le, by simp [hφβ, hsn]⟩)
    let S : Finset ℝ := Finset.univ.image a ∪ Finset.univ.image b
    refine isPiecewiseC1_of_finset ⟨α₁, β₁, hlt₁, γ.toFun ∘ φ, hc_comp⟩ S
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, ha0⟩))
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨Fin.last n, Finset.mem_univ _, hbn⟩))
      ?_ ?_
    · intro x hx
      simp only [S, Finset.coe_union, Finset.coe_image, Finset.coe_univ, image_univ,
        mem_union, mem_range] at hx
      rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact (ha_mem i).1
      · exact (hb_mem i).1
    · intro x y hx hxy hy hdisj
      change α₁ ≤ x at hx
      change y ≤ β₁ at hy
      set mid := (x + y) / 2 with hmid_def
      have hmidIoo : mid ∈ Ioo x y := ⟨by linarith, by linarith⟩
      have hmidIcc : mid ∈ Icc α₁ β₁ := ⟨le_trans hx hmidIoo.1.le, le_trans hmidIoo.2.le hy⟩
      by_cases hφs : φ mid ∈ Set.range s
      · obtain ⟨i, hi⟩ := hφs
        have hmidK : mid ∈ K i := ⟨hmidIcc, hi.symm⟩
        have hax : a i ≤ x := by
          by_contra hlt
          exact Set.disjoint_left.mp hdisj
            (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
            ⟨not_le.mp hlt, lt_of_le_of_lt (csInf_le (hKcomp i).bddBelow hmidK) hmidIoo.2⟩
        have hyb : y ≤ b i := by
          by_contra hlt
          exact Set.disjoint_left.mp hdisj
            (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
            ⟨lt_of_lt_of_le hmidIoo.1 (le_csSup (hKcomp i).bddAbove hmidK), not_le.mp hlt⟩
        refine ⟨fun _ => 0, continuousOn_const, fun t ht => ?_⟩
        have hev : (γ.toFun ∘ φ) =ᶠ[𝓝 t] fun _ => γ.toFun (s i) := by
          filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
          have huIcc : u ∈ Icc α₁ β₁ := ⟨le_trans hx hu.1.le, le_trans hu.2.le hy⟩
          have h1 : s i ≤ φ u :=
            (ha_mem i).2 ▸ hmono (ha_mem i).1 huIcc (le_trans hax hu.1.le)
          have h2 : φ u ≤ s i :=
            (hb_mem i).2 ▸ hmono huIcc (hb_mem i).1 (le_trans hu.2.le hyb)
          simp [le_antisymm h2 h1]
        exact ((hasDerivAt_const t (γ.toFun (s i))).congr_of_eventuallyEq hev).hasDerivWithinAt
      · have hφIcc : φ mid ∈ Icc γ.α γ.β :=
          ⟨hφα ▸ hmono (left_mem_Icc.mpr hlt₁.le) hmidIcc hmidIcc.1,
           hφβ ▸ hmono hmidIcc (right_mem_Icc.mpr hlt₁.le) hmidIcc.2⟩
        let T : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => s j ≤ φ mid)
        have hTne : T.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs0 ▸ hφIcc.1⟩⟩
        let j := T.max' hTne
        have hjlt : s j < φ mid := lt_of_le_of_ne (Finset.mem_filter.mp (T.max'_mem hTne)).2
          fun h => hφs ⟨j, h⟩
        have hjne : j ≠ Fin.last n := fun h => by
          have : s (Fin.last n) < φ mid := h ▸ hjlt
          linarith [hsn, hφIcc.2]
        obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hjne
        rw [← hi] at hjlt
        have hsucc : φ mid < s i.succ := by
          by_contra hge
          have hmax : i.succ ≤ j :=
            T.le_max' i.succ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hge⟩)
          rw [← hi] at hmax
          exact not_le.mpr i.castSucc_lt_succ hmax
        have hbx : b i.castSucc ≤ x := by
          have hb_lt_mid : b i.castSucc < mid := by
            by_contra hge
            have := hmono hmidIcc (hb_mem i.castSucc).1 (not_lt.mp hge)
            rw [(hb_mem i.castSucc).2] at this
            linarith
          by_contra hlt
          exact Set.disjoint_left.mp hdisj
            (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
            ⟨not_le.mp hlt, lt_trans hb_lt_mid hmidIoo.2⟩
        have hya : y ≤ a i.succ := by
          have hmid_lt_a : mid < a i.succ := by
            by_contra hge
            have := hmono (ha_mem i.succ).1 hmidIcc (not_lt.mp hge)
            rw [(ha_mem i.succ).2] at this
            linarith
          by_contra hlt
          exact Set.disjoint_left.mp hdisj
            (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
            ⟨lt_trans hmidIoo.1 hmid_lt_a, not_le.mp hlt⟩
        have hmaps : MapsTo φ (Icc x y) (Icc (s i.castSucc) (s i.succ)) := fun t ht => by
          have htIcc : t ∈ Icc α₁ β₁ := ⟨le_trans hx ht.1, le_trans ht.2 hy⟩
          exact ⟨(hb_mem i.castSucc).2 ▸ hmono (hb_mem i.castSucc).1 htIcc (le_trans hbx ht.1),
                 (ha_mem i.succ).2 ▸ hmono htIcc (ha_mem i.succ).1 (le_trans ht.2 hya)⟩
        refine ⟨fun t => dφ t • d i (φ t),
          (hdφcont.mono (Icc_subset_Icc hx hy)).smul
            ((hdcont i).comp (hφcont.mono (Icc_subset_Icc hx hy)) hmaps),
          fun t ht => ?_⟩
        have htIoo : t ∈ Ioo α₁ β₁ := ⟨lt_of_le_of_lt hx ht.1, lt_of_lt_of_le ht.2 hy⟩
        have hφt_gt : s i.castSucc < φ t := by
          have hle := (hmaps (Ioo_subset_Icc_self ht)).1
          exact lt_of_le_of_ne hle fun heq =>
            not_le.mpr (lt_of_le_of_lt hbx ht.1)
              (le_csSup (hKcomp i.castSucc).bddAbove ⟨Ioo_subset_Icc_self htIoo, heq.symm⟩)
        have hφt_lt : φ t < s i.succ := by
          have hle := (hmaps (Ioo_subset_Icc_self ht)).2
          exact lt_of_le_of_ne hle fun heq =>
            not_le.mpr (lt_of_lt_of_le ht.2 hya)
              (csInf_le (hKcomp i.succ).bddBelow ⟨Ioo_subset_Icc_self htIoo, heq⟩)
        have hφt_outer : φ t ∈ Ioo γ.α γ.β :=
          ⟨lt_of_le_of_lt (hs0 ▸ hs.monotone (Fin.zero_le _)) hφt_gt,
           lt_of_lt_of_le hφt_lt (hsn ▸ hs.monotone (Fin.le_last _))⟩
        have hg : HasDerivAt γ.toFun (d i (φ t)) (φ t) :=
          (hd i (φ t) ⟨hφt_gt, hφt_lt⟩).hasDerivAt (Icc_mem_nhds hφt_outer.1 hφt_outer.2)
        have hφd : HasDerivAt φ (dφ t) t :=
          (hφderiv t htIoo).hasDerivAt (Icc_mem_nhds htIoo.1 htIoo.2)
        exact (hg.scomp t hφd).hasDerivWithinAt

/-- 10.8: reparametrization preserves trace. -/
theorem reparam_trace (γ : BookPath) {α₁ β₁ : ℝ} (hlt₁ : α₁ < β₁) (φ dφ : ℝ → ℝ)
    (hφcont : ContinuousOn φ (Icc α₁ β₁))
    (hdφcont : ContinuousOn dφ (Icc α₁ β₁))
    (hφderiv : ∀ t ∈ Ioo α₁ β₁, HasDerivWithinAt φ (dφ t) (Icc α₁ β₁) t)
    (hdφnonneg : ∀ t ∈ Ioo α₁ β₁, 0 ≤ dφ t)
    (hφα : φ α₁ = γ.α) (hφβ : φ β₁ = γ.β) :
    (γ.reparam hlt₁ φ dφ hφcont hdφcont hφderiv hdφnonneg hφα hφβ).trace = γ.trace := by
  have hmono : MonotoneOn φ (Icc α₁ β₁) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc α₁ β₁) hφcont
    · rw [interior_Icc]
      exact fun t ht => ((hφderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [((hφderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
      exact hdφnonneg t ht
  have himg : φ '' Icc α₁ β₁ = Icc γ.α γ.β := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨hφα ▸ hmono (left_mem_Icc.mpr hlt₁.le) ht ht.1,
             hφβ ▸ hmono ht (right_mem_Icc.mpr hlt₁.le) ht.2⟩
    · intro u hu
      exact intermediate_value_Icc hlt₁.le hφcont (by rwa [hφα, hφβ])
  simp [trace, BookCurve.trace, reparam, ← image_image, himg]

/-- 10.8: orientation-preserving `C¹` reparametrization preserves path integrals. -/
theorem pathIntegral_reparam (γ : BookPath) {α₁ β₁ : ℝ} (hlt₁ : α₁ < β₁) (φ dφ : ℝ → ℝ)
    (hφcont : ContinuousOn φ (Icc α₁ β₁))
    (hdφcont : ContinuousOn dφ (Icc α₁ β₁))
    (hφderiv : ∀ t ∈ Ioo α₁ β₁, HasDerivWithinAt φ (dφ t) (Icc α₁ β₁) t)
    (hdφnonneg : ∀ t ∈ Ioo α₁ β₁, 0 ≤ dφ t)
    (hφα : φ α₁ = γ.α) (hφβ : φ β₁ = γ.β) (f : ℂ → ℂ) :
    pathIntegral f (γ.reparam hlt₁ φ dφ hφcont hdφcont hφderiv hdφnonneg hφα hφβ).toBookCurve =
      pathIntegral f γ.toBookCurve := by
  have hmono : MonotoneOn φ (Icc α₁ β₁) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc α₁ β₁) hφcont
    · rw [interior_Icc]
      exact fun t ht => ((hφderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [((hφderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
      exact hdφnonneg t ht
  have hchg := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := α₁) (b := β₁) (f := φ) (f' := dφ)
    (g := fun u => f (γ.toFun u) * derivWithin γ.toFun (Icc γ.α γ.β) u)
    (by rwa [Set.uIcc_of_le hlt₁.le])
    (fun t ht => by
      rw [min_eq_left hlt₁.le, max_eq_right hlt₁.le] at ht
      exact (hφderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun t ht => by
      rw [min_eq_left hlt₁.le, max_eq_right hlt₁.le] at ht
      exact hdφnonneg t ht)
  rw [hφα, hφβ] at hchg
  unfold pathIntegral
  rw [← hchg]
  apply intervalIntegral.integral_congr_ae_restrict
  change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc α₁ β₁)] _
  rw [Set.uIoc_of_le hlt₁.le, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  obtain ⟨n, s, d, hs, hs0, hsn, _, hd⟩ := γ.piecewiseC1
  let K : Fin (n + 1) → Set ℝ := fun i => Icc α₁ β₁ ∩ φ ⁻¹' {s i}
  have hKcomp (i : Fin (n + 1)) : IsCompact (K i) :=
    IsCompact.of_isClosed_subset isCompact_Icc
      (hφcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  have hKne (i : Fin (n + 1)) : (K i).Nonempty :=
    intermediate_value_Icc hlt₁.le hφcont
      ⟨hφα.symm ▸ hs0 ▸ hs.monotone (Fin.zero_le i),
       hφβ.symm ▸ hsn ▸ hs.monotone (Fin.le_last i)⟩
  let a : Fin (n + 1) → ℝ := fun i => sInf (K i)
  let b : Fin (n + 1) → ℝ := fun i => sSup (K i)
  have ha_mem (i : Fin (n + 1)) : a i ∈ K i := (hKcomp i).isClosed.csInf_mem (hKne i) (hKcomp i).bddBelow
  have hb_mem (i : Fin (n + 1)) : b i ∈ K i := (hKcomp i).isClosed.csSup_mem (hKne i) (hKcomp i).bddAbove
  have hfin : (Set.range a ∪ Set.range b).Finite := (Set.finite_range a).union (Set.finite_range b)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo,
    hfin.countable.ae_notMem _] with t ht hnot
  dsimp [reparam]
  by_cases hφs : φ t ∈ Set.range s
  · obtain ⟨i, hi⟩ := hφs
    have htK : t ∈ K i := ⟨Ioo_subset_Icc_self ht, hi.symm⟩
    have hta : a i < t := lt_of_le_of_ne (csInf_le (hKcomp i).bddBelow htK)
      fun heq => hnot (Or.inl ⟨i, heq⟩)
    have htb : t < b i := lt_of_le_of_ne (le_csSup (hKcomp i).bddAbove htK)
      fun heq => hnot (Or.inr ⟨i, heq.symm⟩)
    have hevφ : φ =ᶠ[𝓝 t] fun _ => s i := by
      filter_upwards [Ioo_mem_nhds hta htb] with u hu
      have huIcc : u ∈ Icc α₁ β₁ := ⟨le_trans (ha_mem i).1.1 hu.1.le, le_trans hu.2.le (hb_mem i).1.2⟩
      exact le_antisymm ((hb_mem i).2 ▸ hmono huIcc (hb_mem i).1 hu.2.le)
        ((ha_mem i).2 ▸ hmono (ha_mem i).1 huIcc hu.1.le)
    have hdφ0 : dφ t = 0 := by
      have hd1 := (hφderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
      have hd2 := (hasDerivAt_const t (s i)).congr_of_eventuallyEq hevφ
      exact hd1.unique hd2
    have hcomp0 : derivWithin (γ.toFun ∘ φ) (Icc α₁ β₁) t = 0 := by
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
      have hevc : (γ.toFun ∘ φ) =ᶠ[𝓝 t] fun _ => γ.toFun (s i) :=
        hevφ.mono fun u hu => by simp [hu]
      exact ((hasDerivAt_const t (γ.toFun (s i))).congr_of_eventuallyEq hevc).deriv
    simp [hdφ0, hcomp0]
  · have hφIcc : φ t ∈ Icc γ.α γ.β :=
      ⟨hφα ▸ hmono (left_mem_Icc.mpr hlt₁.le) (Ioo_subset_Icc_self ht) ht.1.le,
       hφβ ▸ hmono (Ioo_subset_Icc_self ht) (right_mem_Icc.mpr hlt₁.le) ht.2.le⟩
    have hφIoo : φ t ∈ Ioo γ.α γ.β :=
      ⟨lt_of_le_of_ne hφIcc.1 fun h => hφs ⟨0, hs0.trans h⟩,
       lt_of_le_of_ne hφIcc.2 fun h => hφs ⟨Fin.last n, hsn.trans h.symm⟩⟩
    let T : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => s j ≤ φ t)
    have hTne : T.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs0 ▸ hφIcc.1⟩⟩
    let j := T.max' hTne
    have hjle : s j ≤ φ t := (Finset.mem_filter.mp (T.max'_mem hTne)).2
    have hjlt : s j < φ t := lt_of_le_of_ne hjle fun h => hφs ⟨j, h⟩
    have hjne : j ≠ Fin.last n := fun h => by
      have : s (Fin.last n) < φ t := h ▸ hjlt
      linarith [hsn, hφIoo.2]
    obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hjne
    rw [← hi] at hjlt
    have hsucc : φ t < s i.succ := by
      by_contra hge
      have hmax : i.succ ≤ j :=
        T.le_max' i.succ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hge⟩)
      rw [← hi] at hmax
      exact not_le.mpr i.castSucc_lt_succ hmax
    have hg : HasDerivAt γ.toFun (d i (φ t)) (φ t) :=
      (hd i (φ t) ⟨hjlt, hsucc⟩).hasDerivAt (Icc_mem_nhds hφIoo.1 hφIoo.2)
    have hφd : HasDerivAt φ (dφ t) t :=
      (hφderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hcomp_deriv : derivWithin (γ.toFun ∘ φ) (Icc α₁ β₁) t = dφ t • d i (φ t) := by
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
      exact (hg.scomp t hφd).deriv
    rw [hcomp_deriv, derivWithin_eq_piece hs hs0 hsn hd i ⟨hjlt, hsucc⟩]
    simp [Complex.real_smul]
    ring

/-- 10.8: orientation-preserving `C¹` reparametrization preserves path length. -/
theorem pathLength_reparam (γ : BookPath) {α₁ β₁ : ℝ} (hlt₁ : α₁ < β₁) (φ dφ : ℝ → ℝ)
    (hφcont : ContinuousOn φ (Icc α₁ β₁))
    (hdφcont : ContinuousOn dφ (Icc α₁ β₁))
    (hφderiv : ∀ t ∈ Ioo α₁ β₁, HasDerivWithinAt φ (dφ t) (Icc α₁ β₁) t)
    (hdφnonneg : ∀ t ∈ Ioo α₁ β₁, 0 ≤ dφ t)
    (hφα : φ α₁ = γ.α) (hφβ : φ β₁ = γ.β) :
    pathLength (γ.reparam hlt₁ φ dφ hφcont hdφcont hφderiv hdφnonneg hφα hφβ).toBookCurve =
      pathLength γ.toBookCurve := by
  have hmono : MonotoneOn φ (Icc α₁ β₁) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc α₁ β₁) hφcont
    · rw [interior_Icc]
      exact fun t ht => ((hφderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [((hφderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
      exact hdφnonneg t ht
  have hchg := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := α₁) (b := β₁) (f := φ) (f' := dφ)
    (g := fun u => ‖derivWithin γ.toFun (Icc γ.α γ.β) u‖)
    (by rwa [Set.uIcc_of_le hlt₁.le])
    (fun t ht => by
      rw [min_eq_left hlt₁.le, max_eq_right hlt₁.le] at ht
      exact (hφderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun t ht => by
      rw [min_eq_left hlt₁.le, max_eq_right hlt₁.le] at ht
      exact hdφnonneg t ht)
  rw [hφα, hφβ] at hchg
  unfold pathLength
  rw [← hchg]
  apply intervalIntegral.integral_congr_ae_restrict
  change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc α₁ β₁)] _
  rw [Set.uIoc_of_le hlt₁.le, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  obtain ⟨n, s, d, hs, hs0, hsn, _, hd⟩ := γ.piecewiseC1
  let K : Fin (n + 1) → Set ℝ := fun i => Icc α₁ β₁ ∩ φ ⁻¹' {s i}
  have hKcomp (i : Fin (n + 1)) : IsCompact (K i) :=
    IsCompact.of_isClosed_subset isCompact_Icc
      (hφcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  have hKne (i : Fin (n + 1)) : (K i).Nonempty :=
    intermediate_value_Icc hlt₁.le hφcont
      ⟨hφα.symm ▸ hs0 ▸ hs.monotone (Fin.zero_le i),
       hφβ.symm ▸ hsn ▸ hs.monotone (Fin.le_last i)⟩
  let a : Fin (n + 1) → ℝ := fun i => sInf (K i)
  let b : Fin (n + 1) → ℝ := fun i => sSup (K i)
  have ha_mem (i : Fin (n + 1)) : a i ∈ K i := (hKcomp i).isClosed.csInf_mem (hKne i) (hKcomp i).bddBelow
  have hb_mem (i : Fin (n + 1)) : b i ∈ K i := (hKcomp i).isClosed.csSup_mem (hKne i) (hKcomp i).bddAbove
  have hfin : (Set.range a ∪ Set.range b).Finite := (Set.finite_range a).union (Set.finite_range b)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo,
    hfin.countable.ae_notMem _] with t ht hnot
  dsimp [reparam]
  by_cases hφs : φ t ∈ Set.range s
  · obtain ⟨i, hi⟩ := hφs
    have htK : t ∈ K i := ⟨Ioo_subset_Icc_self ht, hi.symm⟩
    have hta : a i < t := lt_of_le_of_ne (csInf_le (hKcomp i).bddBelow htK)
      fun heq => hnot (Or.inl ⟨i, heq⟩)
    have htb : t < b i := lt_of_le_of_ne (le_csSup (hKcomp i).bddAbove htK)
      fun heq => hnot (Or.inr ⟨i, heq.symm⟩)
    have hevφ : φ =ᶠ[𝓝 t] fun _ => s i := by
      filter_upwards [Ioo_mem_nhds hta htb] with u hu
      have huIcc : u ∈ Icc α₁ β₁ := ⟨le_trans (ha_mem i).1.1 hu.1.le, le_trans hu.2.le (hb_mem i).1.2⟩
      exact le_antisymm ((hb_mem i).2 ▸ hmono huIcc (hb_mem i).1 hu.2.le)
        ((ha_mem i).2 ▸ hmono (ha_mem i).1 huIcc hu.1.le)
    have hdφ0 : dφ t = 0 :=
      ((hφderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).unique
        ((hasDerivAt_const t (s i)).congr_of_eventuallyEq hevφ)
    have hcomp0 : derivWithin (γ.toFun ∘ φ) (Icc α₁ β₁) t = 0 := by
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
      exact ((hasDerivAt_const t (γ.toFun (s i))).congr_of_eventuallyEq
        (hevφ.mono fun u hu => by simp [hu])).deriv
    simp [hdφ0, hcomp0]
  · have hφIcc : φ t ∈ Icc γ.α γ.β :=
      ⟨hφα ▸ hmono (left_mem_Icc.mpr hlt₁.le) (Ioo_subset_Icc_self ht) ht.1.le,
       hφβ ▸ hmono (Ioo_subset_Icc_self ht) (right_mem_Icc.mpr hlt₁.le) ht.2.le⟩
    have hφIoo : φ t ∈ Ioo γ.α γ.β :=
      ⟨lt_of_le_of_ne hφIcc.1 fun h => hφs ⟨0, hs0.trans h⟩,
       lt_of_le_of_ne hφIcc.2 fun h => hφs ⟨Fin.last n, hsn.trans h.symm⟩⟩
    let T : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => s j ≤ φ t)
    have hTne : T.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs0 ▸ hφIcc.1⟩⟩
    let j := T.max' hTne
    have hjlt : s j < φ t := lt_of_le_of_ne (Finset.mem_filter.mp (T.max'_mem hTne)).2
      fun h => hφs ⟨j, h⟩
    have hjne : j ≠ Fin.last n := fun h => by
      have : s (Fin.last n) < φ t := h ▸ hjlt
      linarith [hsn, hφIoo.2]
    obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hjne
    rw [← hi] at hjlt
    have hsucc : φ t < s i.succ := by
      by_contra hge
      have hmax : i.succ ≤ j :=
        T.le_max' i.succ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hge⟩)
      rw [← hi] at hmax
      exact not_le.mpr i.castSucc_lt_succ hmax
    have hg : HasDerivAt γ.toFun (d i (φ t)) (φ t) :=
      (hd i (φ t) ⟨hjlt, hsucc⟩).hasDerivAt (Icc_mem_nhds hφIoo.1 hφIoo.2)
    have hφd : HasDerivAt φ (dφ t) t :=
      (hφderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hcomp_deriv : derivWithin (γ.toFun ∘ φ) (Icc α₁ β₁) t = dφ t • d i (φ t) := by
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
      exact (hg.scomp t hφd).deriv
    rw [hcomp_deriv, derivWithin_eq_piece hs hs0 hsn hd i ⟨hjlt, hsucc⟩, norm_smul,
      Real.norm_of_nonneg (hdφnonneg t ht)]

end BookPath

/-! ### 10.9: Positively oriented circles, oriented segments, and oriented triangle boundaries -/

/-- 10.9: positively oriented circular arc `t ↦ a + r * exp(i t)` on `[θ₁, θ₂]` (`θ₁ < θ₂`). -/
def circleArcPath (a : ℂ) (r : ℝ) {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) : BookPath :=
  BookPath.ofC1 hθ (circleMap a r) (deriv (circleMap a r))
    (continuous_circleMap a r).continuousOn
    (by rw [funext (deriv_circleMap a r)]; exact ((continuous_circleMap 0 r).mul continuous_const).continuousOn)
    (fun t _ => (hasDerivAt_circleMap a r t).deriv ▸ (hasDerivAt_circleMap a r t).hasDerivWithinAt)

/-- 10.9: positively oriented circle `t ↦ a + r * exp(i t)` on `[0, 2π]` (`r > 0`). -/
def positivelyOrientedCircle (a : ℂ) (r : ℝ) (_hr : 0 < r) : BookPath :=
  circleArcPath a r Real.two_pi_pos

theorem positivelyOrientedCircle_isClosed (a : ℂ) {r : ℝ} (hr : 0 < r) :
    (positivelyOrientedCircle a r hr).IsClosed := by
  simp [BookPath.IsClosed, BookCurve.IsClosed, positivelyOrientedCircle, circleArcPath,
    BookPath.ofC1, circleMap]

theorem positivelyOrientedCircle_trace (a : ℂ) {r : ℝ} (hr : 0 < r) :
    (positivelyOrientedCircle a r hr).trace = Metric.sphere a r := by
  dsimp [BookPath.trace, BookCurve.trace, positivelyOrientedCircle, circleArcPath, BookPath.ofC1]
  rw [show Metric.sphere a r = Metric.sphere a |r| by rw [abs_of_pos hr]]
  apply Subset.antisymm
  · rw [← range_circleMap]
    exact image_subset_range _ _
  · rw [← image_circleMap_Ioc]
    exact image_mono Ioc_subset_Icc_self

/-- 10.9: `pathIntegral` along `positivelyOrientedCircle a r hr` agrees identically with Mathlib's
`circleIntegral` (`CircleIntegral.lean:425`). -/
theorem pathIntegral_positivelyOrientedCircle_eq_circleIntegral
    (f : ℂ → ℂ) (a : ℂ) {r : ℝ} (hr : 0 < r) :
    pathIntegral f (positivelyOrientedCircle a r hr).toBookCurve = ∮ z in C(a, r), f z := by
  unfold pathIntegral circleIntegral positivelyOrientedCircle circleArcPath BookPath.ofC1
  dsimp only
  apply intervalIntegral.integral_congr_ae_restrict
  change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))] _
  rw [Set.uIoc_of_le Real.two_pi_pos.le, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), smul_eq_mul, mul_comm]

theorem pathLength_positivelyOrientedCircle (a : ℂ) {r : ℝ} (hr : 0 < r) :
    pathLength (positivelyOrientedCircle a r hr).toBookCurve = 2 * Real.pi * r := by
  unfold pathLength positivelyOrientedCircle circleArcPath BookPath.ofC1
  dsimp only
  have heq : (∫ t in (0 : ℝ)..2 * Real.pi, ‖derivWithin (circleMap a r) (Icc 0 (2 * Real.pi)) t‖) =
      ∫ _ in (0 : ℝ)..2 * Real.pi, r := by
    apply intervalIntegral.integral_congr_ae_restrict
    change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))] _
    rw [Set.uIoc_of_le Real.two_pi_pos.le, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), deriv_circleMap, norm_mul,
      norm_circleMap_zero, Complex.norm_I, mul_one, abs_of_pos hr]
  rw [heq, intervalIntegral.integral_const, sub_zero, smul_eq_mul]

private theorem hasDerivAt_affine_segment (a b : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => (1 - u) • a + u • b) (b - a) t := by
  have h1 := (((hasDerivAt_id t).const_sub 1).smul_const a).add ((hasDerivAt_id t).smul_const b)
  have heq : (-1 : ℝ) • a + (1 : ℝ) • b = b - a := by simp [sub_eq_add_neg, add_comm]
  rwa [heq] at h1

/-- 10.9: oriented line segment `[a, b]` on `[0, 1]`, given by `t ↦ (1 - t) a + t b`. -/
def orientedSegment (a b : ℂ) : BookPath :=
  BookPath.ofC1 zero_lt_one (fun t : ℝ => (1 - t : ℝ) • a + t • b) (fun _ => b - a)
    (((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)).continuousOn
    continuousOn_const
    (fun t _ => (hasDerivAt_affine_segment a b t).hasDerivWithinAt)

@[simp] theorem orientedSegment_start (a b : ℂ) :
    (orientedSegment a b).toFun (orientedSegment a b).α = a := by
  simp [orientedSegment, BookPath.ofC1]

@[simp] theorem orientedSegment_end (a b : ℂ) :
    (orientedSegment a b).toFun (orientedSegment a b).β = b := by
  simp [orientedSegment, BookPath.ofC1]

theorem orientedSegment_trace (a b : ℂ) :
    (orientedSegment a b).trace = segment ℝ a b := by
  ext z
  simp [BookPath.trace, BookCurve.trace, orientedSegment, BookPath.ofC1, segment_eq_image]

theorem pathIntegral_orientedSegment (f : ℂ → ℂ) (a b : ℂ) :
    pathIntegral f (orientedSegment a b).toBookCurve =
      (b - a) * ∫ t in (0 : ℝ)..1, f ((1 - t : ℝ) • a + t • b) := by
  unfold pathIntegral orientedSegment BookPath.ofC1
  dsimp only
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae_restrict
  change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc 0 1)] _
  rw [Set.uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),
    (hasDerivAt_affine_segment a b t).deriv, mul_comm]

theorem pathIntegral_orientedSegment_swap {f : ℂ → ℂ} {a b : ℂ} :
    pathIntegral f (orientedSegment b a).toBookCurve =
      -pathIntegral f (orientedSegment a b).toBookCurve := by
  rw [pathIntegral_orientedSegment, pathIntegral_orientedSegment]
  have hchg := intervalIntegral.integral_comp_sub_left
    (f := fun t : ℝ => f ((1 - t) • a + t • b)) (a := (0 : ℝ)) (b := (1 : ℝ)) (1 : ℝ)
  simp only [sub_zero, sub_self] at hchg
  have hcongr : (∫ t in (0 : ℝ)..1, f ((1 - t) • b + t • a)) =
      ∫ t in (0 : ℝ)..1, f ((1 - (1 - t)) • a + (1 - t) • b) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    congr 1
    simp [sub_smul]; abel
  rw [hcongr, hchg, intervalIntegral.integral_symm]
  ring

theorem pathLength_orientedSegment (a b : ℂ) :
    pathLength (orientedSegment a b).toBookCurve = ‖b - a‖ := by
  unfold pathLength orientedSegment BookPath.ofC1
  dsimp only
  have heq : (∫ t in (0 : ℝ)..1, ‖derivWithin (fun u : ℝ => (1 - u) • a + u • b) (Icc 0 1) t‖) =
      ∫ _ in (0 : ℝ)..1, ‖b - a‖ := by
    apply intervalIntegral.integral_congr_ae_restrict
    change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc 0 1)] _
    rw [Set.uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),
      (hasDerivAt_affine_segment a b t).deriv]
  rw [heq, intervalIntegral.integral_const, sub_zero, one_smul]

/-- 10.9: oriented triangle boundary `∂Δ(a, b, c)` formed by concatenating `[a, b]`, `[b, c]`,
and `[c, a]` (degenerate triangles permitted). -/
def triangleBoundary (a b c : ℂ) : BookPath :=
  (orientedSegment a b).concat
    ((orientedSegment b c).concat (orientedSegment c a) (by simp))
    (by simp)

theorem triangleBoundary_isClosed (a b c : ℂ) : (triangleBoundary a b c).IsClosed := by
  simp [triangleBoundary, BookPath.IsClosed, BookCurve.IsClosed]

theorem triangleBoundary_trace (a b c : ℂ) :
    (triangleBoundary a b c).trace = segment ℝ a b ∪ (segment ℝ b c ∪ segment ℝ c a) := by
  simp [triangleBoundary, BookPath.concat_trace, orientedSegment_trace]

theorem pathIntegral_triangleBoundary {f : ℂ → ℂ} {a b c : ℂ}
    (hf : ContinuousOn f (triangleBoundary a b c).trace) :
    pathIntegral f (triangleBoundary a b c).toBookCurve =
      pathIntegral f (orientedSegment a b).toBookCurve +
      pathIntegral f (orientedSegment b c).toBookCurve +
      pathIntegral f (orientedSegment c a).toBookCurve := by
  unfold triangleBoundary
  rw [BookPath.pathIntegral_concat _ _ _ hf,
    BookPath.pathIntegral_concat _ _ _
      (hf.mono (by simp only [triangleBoundary_trace, BookPath.concat_trace, orientedSegment_trace]; exact subset_union_right))]
  ring

/-- 10.9: cyclic permutation of vertices leaves the oriented triangle integral unchanged. -/
theorem pathIntegral_triangleBoundary_cycle {f : ℂ → ℂ} {a b c : ℂ}
    (hf : ContinuousOn f (triangleBoundary a b c).trace) :
    pathIntegral f (triangleBoundary b c a).toBookCurve =
      pathIntegral f (triangleBoundary a b c).toBookCurve := by
  have htr : (triangleBoundary b c a).trace = (triangleBoundary a b c).trace := by
    ext z; simp only [triangleBoundary_trace, mem_union]; tauto
  rw [pathIntegral_triangleBoundary (htr ▸ hf), pathIntegral_triangleBoundary hf]
  ring

/-- 10.9: swapping two vertices negates the oriented triangle integral. -/
theorem pathIntegral_triangleBoundary_swap {f : ℂ → ℂ} {a b c : ℂ}
    (hf : ContinuousOn f (triangleBoundary a b c).trace) :
    pathIntegral f (triangleBoundary a c b).toBookCurve =
      -pathIntegral f (triangleBoundary a b c).toBookCurve := by
  have htr : (triangleBoundary a c b).trace = (triangleBoundary a b c).trace := by
    simp only [triangleBoundary_trace, segment_symm ℝ a b, segment_symm ℝ b c, segment_symm ℝ c a]
    ext z; simp only [mem_union]; tauto
  rw [pathIntegral_triangleBoundary (htr ▸ hf), pathIntegral_triangleBoundary hf,
      pathIntegral_orientedSegment_swap (a := c) (b := a),
      pathIntegral_orientedSegment_swap (a := b) (b := c),
      pathIntegral_orientedSegment_swap (a := a) (b := b)]
  ring

theorem pathLength_triangleBoundary (a b c : ℂ) :
    pathLength (triangleBoundary a b c).toBookCurve = ‖b - a‖ + ‖c - b‖ + ‖a - c‖ := by
  unfold triangleBoundary
  rw [BookPath.pathLength_concat, BookPath.pathLength_concat,
    pathLength_orientedSegment, pathLength_orientedSegment, pathLength_orientedSegment]
  ring

/-! ### 10.10: Index (winding number) of a closed path -/

/-- 10.10: index `Ind_γ(z) = (2πi)⁻¹ ∫_γ (ζ - z)⁻¹ dζ` of a curve `γ` with respect to `z`. -/
def Ind (γ : BookCurve ℂ) (z : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * pathIntegral (fun w => (w - z)⁻¹) γ

private theorem two_pi_I_ne_zero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

/-- If `F : ℝ → ℂ` is continuous on `[a, b]` (`a ≤ b`) and has zero derivative on `(a, b)`,
then `F a = F b`. -/
private theorem eq_endpoints_of_continuousOn_of_hasDerivAt_zero {a b : ℝ} (hab : a ≤ b)
    {F : ℝ → ℂ} (hcont : ContinuousOn F (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt F 0 t) :
    F a = F b := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · rfl
  · have hdiff : DifferentiableOn ℝ F (Ioo a b) :=
      fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt
    have hzero : EqOn (deriv F) 0 (Ioo a b) := fun t ht => (hderiv t ht).deriv
    set m := (a + b) / 2 with hm_def
    have hm : m ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have hconst : ∀ t ∈ Ioo a b, F t = F m := fun t ht =>
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero ht hm
    have ha_cl : a ∈ closure (Ioo a b) := by
      rw [closure_Ioo hlt.ne]
      exact left_mem_Icc.mpr hlt.le
    have hb_cl : b ∈ closure (Ioo a b) := by
      rw [closure_Ioo hlt.ne]
      exact right_mem_Icc.mpr hlt.le
    have ha_eq : F a = F m := by
      have hnhds : Filter.NeBot (𝓝[Ioo a b] a) := mem_closure_iff_nhdsWithin_neBot.mp ha_cl
      have ht1 : Tendsto F (𝓝[Ioo a b] a) (𝓝 (F a)) :=
        (hcont a (left_mem_Icc.mpr hlt.le)).mono Ioo_subset_Icc_self
      have ht2 : Tendsto F (𝓝[Ioo a b] a) (𝓝 (F m)) :=
        tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (hconst t ht).symm)
      exact tendsto_nhds_unique ht1 ht2
    have hb_eq : F b = F m := by
      have hnhds : Filter.NeBot (𝓝[Ioo a b] b) := mem_closure_iff_nhdsWithin_neBot.mp hb_cl
      have ht1 : Tendsto F (𝓝[Ioo a b] b) (𝓝 (F b)) :=
        (hcont b (right_mem_Icc.mpr hlt.le)).mono Ioo_subset_Icc_self
      have ht2 : Tendsto F (𝓝[Ioo a b] b) (𝓝 (F m)) :=
        tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (hconst t ht).symm)
      exact tendsto_nhds_unique ht1 ht2
    exact ha_eq.trans hb_eq.symm

/-- Clamped primitive `t ↦ ∫ u in a..t, g (max a (min b u))` for a continuous function on `[a, b]`. -/
private theorem hasDerivAt_clamped_primitive {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Icc a b)) :
    ∃ ψ : ℝ → ℂ, Continuous ψ ∧ ψ a = 0 ∧
      ψ b = (∫ u in a..b, g u) ∧
      ∀ t ∈ Ioo a b, HasDerivAt ψ (g t) t := by
  let G : ℝ → ℂ := fun u => g (max a (min b u))
  have hGcont : Continuous G := by
    refine hg.comp_continuous (continuous_const.max (continuous_const.min continuous_id)) fun u => ?_
    exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  let ψ : ℝ → ℂ := fun t => ∫ u in a..t, G u
  have hψderiv : ∀ t : ℝ, HasDerivAt ψ (G t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hGcont.intervalIntegrable a t)
      (hGcont.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 t)) hGcont.continuousAt
  refine ⟨ψ, (fun t => (hψderiv t).differentiableAt) |> Differentiable.continuous,
    intervalIntegral.integral_same, ?_, ?_⟩
  · refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hab] at hu
    simp [G, min_eq_right hu.2, max_eq_right hu.1]
  · intro t ht
    have hGt : G t = g t := by simp [G, min_eq_right ht.2.le, max_eq_right ht.1.le]
    exact hGt ▸ hψderiv t

private theorem exp_piece_telescope {z : ℂ} (g : ℝ → ℂ) :
    ∀ {n : ℕ} (s : Fin (n + 1) → ℝ) (I_piece : Fin n → ℂ),
    (∀ i : Fin n, g (s i.succ) - z = Complex.exp (I_piece i) * (g (s i.castSucc) - z)) →
    g (s (Fin.last n)) - z = Complex.exp (∑ i : Fin n, I_piece i) * (g (s 0) - z)
  | 0, _, _, _ => by simp
  | n + 1, s, I_piece, hstep => by
    have hind := exp_piece_telescope g (fun j : Fin (n + 1) => s j.castSucc)
      (fun j : Fin n => I_piece j.castSucc) (fun j => by
        have h := hstep j.castSucc
        rwa [show j.castSucc.succ = j.succ.castSucc from Fin.ext (by simp)] at h)
    have hlast := hstep (Fin.last n)
    rw [Fin.sum_univ_castSucc, Complex.exp_add, mul_assoc]
    change g (s (Fin.last n).succ) - z = _
    simp only [Fin.castSucc_zero] at hind
    rw [hlast, hind]
    ring

/-- 10.10: for any path `γ` and `z ∉ γ*`, `γ(β) - z = exp(∫_γ (ζ - z)⁻¹ dζ) * (γ(α) - z)`. -/
theorem endpoint_sub_eq_exp_pathIntegral (γ : BookPath) {z : ℂ} (hz : z ∉ γ.trace) :
    γ.toFun γ.β - z =
      Complex.exp (pathIntegral (fun w => (w - z)⁻¹) γ.toBookCurve) * (γ.toFun γ.α - z) := by
  obtain ⟨n, s, d, hs, hs0, hsn, hdcont, hd⟩ := γ.piecewiseC1
  have hne : ∀ t ∈ Icc γ.α γ.β, γ.toFun t - z ≠ 0 := fun t ht h0 =>
    hz (sub_eq_zero.mp h0 ▸ γ.mem_trace_of_mem_Icc ht)
  have hfcont : ContinuousOn (fun w : ℂ => (w - z)⁻¹) γ.trace :=
    (continuous_id.sub continuous_const).continuousOn.inv₀ fun w hw h0 =>
      hz (sub_eq_zero.mp (by simpa using h0) ▸ hw)
  let I_piece : Fin n → ℂ := fun i =>
    ∫ t in s i.castSucc..s i.succ, (γ.toFun t - z)⁻¹ * d i t
  have hstep : ∀ i : Fin n,
      γ.toFun (s i.succ) - z = Complex.exp (I_piece i) * (γ.toFun (s i.castSucc) - z) := by
    intro i
    have hlt : s i.castSucc < s i.succ := hs i.castSucc_lt_succ
    have hsub : Icc (s i.castSucc) (s i.succ) ⊆ Icc γ.α γ.β :=
      Icc_subset_Icc (hs0 ▸ hs.monotone (Fin.zero_le _)) (hsn ▸ hs.monotone (Fin.le_last _))
    have hgcont : ContinuousOn (fun t => (γ.toFun t - z)⁻¹ * d i t)
        (Icc (s i.castSucc) (s i.succ)) :=
      ((hfcont.comp (γ.continuousOn.mono hsub)
        (fun t ht => γ.mem_trace_of_mem_Icc (hsub ht))).mul (hdcont i))
    obtain ⟨ψ, hψcont, hψa, hψb, hψderiv⟩ := hasDerivAt_clamped_primitive hlt.le hgcont
    let F : ℝ → ℂ := fun t => Complex.exp (-ψ t) * (γ.toFun t - z)
    have hFcont : ContinuousOn F (Icc (s i.castSucc) (s i.succ)) :=
      (Complex.continuous_exp.comp hψcont.neg).continuousOn.mul
        ((γ.continuousOn.mono hsub).sub continuousOn_const)
    have hFderiv : ∀ t ∈ Ioo (s i.castSucc) (s i.succ), HasDerivAt F 0 t := by
      intro t ht
      have htIoo : t ∈ Ioo γ.α γ.β :=
        ⟨lt_of_le_of_lt (hs0 ▸ hs.monotone (Fin.zero_le _)) ht.1,
         lt_of_lt_of_le ht.2 (hsn ▸ hs.monotone (Fin.le_last _))⟩
      have hdγ : HasDerivAt (fun u => γ.toFun u - z) (d i t) t :=
        ((hd i t ht).hasDerivAt (Icc_mem_nhds htIoo.1 htIoo.2)).sub_const z
      have hdexp : HasDerivAt (fun u => Complex.exp (-ψ u))
          (Complex.exp (-ψ t) * -((γ.toFun t - z)⁻¹ * d i t)) t :=
        (hψderiv t ht).neg.cexp
      have hprod := hdexp.mul hdγ
      have hne_t : γ.toFun t - z ≠ 0 := hne t (Ioo_subset_Icc_self htIoo)
      have hzero : Complex.exp (-ψ t) * -((γ.toFun t - z)⁻¹ * d i t) * (γ.toFun t - z) +
          Complex.exp (-ψ t) * d i t = 0 := by
        calc Complex.exp (-ψ t) * -((γ.toFun t - z)⁻¹ * d i t) * (γ.toFun t - z) +
              Complex.exp (-ψ t) * d i t
            = Complex.exp (-ψ t) * d i t * (-((γ.toFun t - z)⁻¹ * (γ.toFun t - z)) + 1) := by ring
          _ = 0 := by rw [inv_mul_cancel₀ hne_t]; ring
      exact hzero ▸ hprod
    have hFeq : F (s i.castSucc) = F (s i.succ) :=
      eq_endpoints_of_continuousOn_of_hasDerivAt_zero hlt.le hFcont hFderiv
    dsimp [F] at hFeq
    rw [hψa, neg_zero, Complex.exp_zero, one_mul, hψb] at hFeq
    calc γ.toFun (s i.succ) - z
        = Complex.exp (I_piece i) * (Complex.exp (-I_piece i) * (γ.toFun (s i.succ) - z)) := by
          rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
      _ = Complex.exp (I_piece i) * (γ.toFun (s i.castSucc) - z) := by
          dsimp [I_piece]; rw [← hFeq]
  rw [γ.pathIntegral_eq_sum_pieces hfcont hs hs0 hsn hdcont hd, ← hs0, ← hsn]
  exact exp_piece_telescope γ.toFun s I_piece hstep

/-- 10.10: for a closed path `γ` and `z ∉ γ*`, `Ind_γ(z)` is an integer. -/
theorem Ind_mem_int (γ : BookPath) (hclosed : γ.IsClosed) {z : ℂ} (hz : z ∉ γ.trace) :
    ∃ n : ℤ, Ind γ.toBookCurve z = n := by
  have hend := endpoint_sub_eq_exp_pathIntegral γ hz
  have hclosed' : γ.toFun γ.β = γ.toFun γ.α := hclosed.symm
  rw [hclosed'] at hend
  have hne : γ.toFun γ.α - z ≠ 0 := fun h0 =>
    hz (sub_eq_zero.mp h0 ▸ γ.mem_trace_of_mem_Icc (left_mem_Icc.mpr γ.le_endpoints))
  have hexp : Complex.exp (pathIntegral (fun w => (w - z)⁻¹) γ.toBookCurve) = 1 := by
    apply mul_right_cancel₀ hne
    rw [one_mul, ← hend]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  refine ⟨n, ?_⟩
  unfold Ind
  rw [hn, mul_comm (n : ℂ), ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

/-- In `ℂ`, the exterior `(closedBall a R)ᶜ` is nonempty and preconnected for every `R ≥ 0`. -/
theorem isConnected_compl_closedBall (a : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    IsConnected (Metric.closedBall a R)ᶜ := by
  let R' : ℝ := R + 1
  have hR'pos : 0 < R' := by linarith
  have hRR' : R < R' := by linarith
  let S : Set ℂ := Metric.sphere a R'
  have hS_eq : S = (positivelyOrientedCircle a R' hR'pos).trace :=
    (positivelyOrientedCircle_trace a hR'pos).symm
  have hS_conn : IsConnected S := by
    rw [hS_eq]
    exact ⟨(positivelyOrientedCircle a R' hR'pos).trace_nonempty,
      isPreconnected_Icc.image _ (positivelyOrientedCircle a R' hR'pos).continuousOn⟩
  have hS_sub : S ⊆ (Metric.closedBall a R)ᶜ := by
    intro w hw
    rw [mem_compl_iff, Metric.mem_closedBall, not_le]
    have hdist : dist w a = R' := hw
    linarith
  refine ⟨hS_conn.1.mono hS_sub, ?_⟩
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  have seg_to_S : ∀ z ∈ (Metric.closedBall a R)ᶜ,
      ∃ C : Set ℂ, C ⊆ (Metric.closedBall a R)ᶜ ∧ z ∈ C ∧ (C ∩ S).Nonempty ∧ IsPreconnected C := by
    intro z hz
    rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_eq_norm] at hz
    have hznorm_pos : 0 < ‖z - a‖ := lt_of_le_of_lt hR hz
    let z' : ℂ := a + (R' / ‖z - a‖ : ℝ) • (z - a)
    have hz'S : z' ∈ S := by
      simp only [S, Metric.mem_sphere, dist_eq_norm, z', add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (div_nonneg hR'pos.le hznorm_pos.le),
        div_mul_cancel₀ _ hznorm_pos.ne']
    refine ⟨segment ℝ z z', ?_, left_mem_segment ℝ z z',
      ⟨z', right_mem_segment ℝ z z', hz'S⟩, (convex_segment z z').isPreconnected⟩
    rintro w ⟨u, v, hu, hv, huv, rfl⟩
    rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_eq_norm]
    have hvec : u • z + v • z' - a = (u + v * (R' / ‖z - a‖)) • (z - a) := by
      have huvC : (u : ℂ) + v = 1 := by exact_mod_cast huv
      simp only [z', Complex.real_smul, Complex.ofReal_add, Complex.ofReal_mul]
      linear_combination a * huvC
    have hcoeff_nonneg : 0 ≤ u + v * (R' / ‖z - a‖) :=
      add_nonneg hu (mul_nonneg hv (div_nonneg hR'pos.le hznorm_pos.le))
    rw [hvec, norm_smul, Real.norm_of_nonneg hcoeff_nonneg, add_mul,
      mul_assoc, div_mul_cancel₀ _ hznorm_pos.ne']
    rcases eq_or_lt_of_le hu with rfl | hupos
    · simp only [zero_add] at huv; subst huv; linarith
    · have hvR : v * R ≤ v * R' := mul_le_mul_of_nonneg_left hRR'.le hv
      have huR : u * R < u * ‖z - a‖ := mul_lt_mul_of_pos_left hz hupos
      calc R = (u + v) * R := by rw [huv, one_mul]
        _ = u * R + v * R := add_mul u v R
        _ < u * ‖z - a‖ + v * R' := add_lt_add_of_lt_of_le huR hvR
  obtain ⟨Cx, hCx_sub, hxCx, ⟨zx, hzxCx, hzxS⟩, hCx_pre⟩ := seg_to_S x hx
  obtain ⟨Cy, hCy_sub, hyCy, ⟨zy, hzyCy, hzyS⟩, hCy_pre⟩ := seg_to_S y hy
  have hCSx : IsPreconnected (Cx ∪ S) := hCx_pre.union zx hzxCx hzxS hS_conn.2
  have hCSxy : IsPreconnected ((Cx ∪ S) ∪ Cy) :=
    hCSx.union zy (Or.inr hzyS) hzyCy hCy_pre
  exact ⟨(Cx ∪ S) ∪ Cy, union_subset (union_subset hCx_sub hS_sub) hCy_sub,
    Or.inl (Or.inl hxCx), Or.inr hyCy, hCSxy⟩

/-- 10.10: for any compact `K ⊆ ℂ` (in particular `γ*`), `Kᶜ` has a unique unbounded connected
component, and every other component of `Kᶜ` is bounded. -/
theorem existsUnique_unbounded_component_compl {K : Set ℂ} (hK : IsCompact K) :
    ∃! U : Set ℂ, U ∈ bookComponents Kᶜ ∧ ¬ Bornology.IsBounded U := by
  obtain ⟨R, hRpos, hKsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  have hext_sub : (Metric.closedBall (0 : ℂ) R)ᶜ ⊆ Kᶜ := compl_subset_compl.mpr hKsub
  have hext_conn := isConnected_compl_closedBall (0 : ℂ) hRpos.le
  let z₀ : ℂ := ((R + 1 : ℝ) : ℂ)
  have hz₀_ext : z₀ ∈ (Metric.closedBall (0 : ℂ) R)ᶜ := by
    rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_zero_right]
    simp only [z₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < R + 1)]
    linarith
  let U : Set ℂ := bookComponent Kᶜ z₀
  have hU_mem : U ∈ bookComponents Kᶜ := ⟨z₀, hext_sub hz₀_ext, rfl⟩
  have hext_sub_U : (Metric.closedBall (0 : ℂ) R)ᶜ ⊆ U :=
    bookComponent_maximal hext_sub ((bookConnected_iff_isPreconnected _).mpr hext_conn.2) hz₀_ext
  have hU_unbdd : ¬ Bornology.IsBounded U := by
    intro hbdd
    obtain ⟨M, _, hM⟩ := hbdd.subset_closedBall_lt 0 (0 : ℂ)
    let w : ℂ := ((max R M + 1 : ℝ) : ℂ)
    have hw_ext : w ∈ (Metric.closedBall (0 : ℂ) R)ᶜ := by
      rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_zero_right]
      have hpos : 0 < max R M + 1 := lt_of_lt_of_le hRpos (le_trans (le_max_left R M) (by linarith))
      simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      exact lt_of_le_of_lt (le_max_left R M) (by linarith)
    have hw_ball : w ∈ Metric.closedBall (0 : ℂ) M := hM (hext_sub_U hw_ext)
    rw [Metric.mem_closedBall, dist_zero_right] at hw_ball
    have hpos : 0 < max R M + 1 := lt_of_lt_of_le hRpos (le_trans (le_max_left R M) (by linarith))
    simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hw_ball
    linarith [le_max_right R M]
  refine ⟨U, ⟨hU_mem, hU_unbdd⟩, ?_⟩
  rintro V ⟨hV_mem, hV_unbdd⟩
  by_contra hne
  have hdisj : Disjoint V U := bookComponents_pairwise_disjoint Kᶜ hV_mem hU_mem hne
  have hV_bdd : V ⊆ Metric.closedBall (0 : ℂ) R := by
    intro z hzV
    by_contra hz_not
    exact Set.disjoint_left.mp hdisj hzV (hext_sub_U hz_not)
  exact hV_unbdd (Metric.isBounded_closedBall.subset hV_bdd)

/-- 10.10: `z ↦ ∫_γ (ζ - z)⁻¹ dζ` is continuous on `(γ*)ᶜ` for any path `γ`. -/
theorem continuousOn_pathIntegral_sub_inv (γ : BookPath) :
    ContinuousOn (fun z => pathIntegral (fun w => (w - z)⁻¹) γ.toBookCurve) (γ.trace)ᶜ := by
  intro z₀ hz₀
  apply ContinuousAt.continuousWithinAt
  have hopen : IsOpen (γ.trace)ᶜ := γ.isCompact_trace.isClosed.isOpen_compl
  obtain ⟨ε₀, hε₀pos, hball⟩ := Metric.isOpen_iff.mp hopen z₀ hz₀
  set δ : ℝ := ε₀ / 2 with hδ_def
  have hδpos : 0 < δ := half_pos hε₀pos
  rw [Metric.continuousAt_iff]
  intro ε hε
  let L : ℝ := pathLength γ.toBookCurve + 1
  have hLpos : 0 < L := by linarith [γ.pathLength_nonneg]
  refine ⟨min δ (ε * (2 * δ ^ 2) / L), lt_min hδpos (div_pos (mul_pos hε (by positivity)) hLpos), ?_⟩
  intro z hz_dist
  rw [dist_eq_norm] at hz_dist ⊢
  have hzδ : ‖z - z₀‖ < δ := lt_of_lt_of_le hz_dist (min_le_left _ _)
  have hz_bound : ‖z - z₀‖ < ε * (2 * δ ^ 2) / L := lt_of_lt_of_le hz_dist (min_le_right _ _)
  have hw_z₀ : ∀ w ∈ γ.trace, 2 * δ ≤ ‖w - z₀‖ := by
    intro w hw
    by_contra hlt
    have hw_ball : w ∈ Metric.ball z₀ ε₀ := by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith [not_le.mp hlt]
    exact hball hw_ball hw
  have hw_z : ∀ w ∈ γ.trace, δ ≤ ‖w - z‖ := by
    intro w hw
    have htri : ‖w - z₀‖ ≤ ‖w - z‖ + ‖z - z₀‖ := by
      simpa using norm_add_le (w - z) (z - z₀)
    linarith [hw_z₀ w hw]
  have hf_z : ContinuousOn (fun w : ℂ => (w - z)⁻¹) γ.trace :=
    (continuous_id.sub continuous_const).continuousOn.inv₀ fun w hw h0 => by
      have hsub0 : w - z = 0 := by simpa using h0
      have := hw_z w hw; rw [hsub0, norm_zero] at this; linarith
  have hf_z₀ : ContinuousOn (fun w : ℂ => (w - z₀)⁻¹) γ.trace :=
    (continuous_id.sub continuous_const).continuousOn.inv₀ fun w hw h0 => by
      have hsub0 : w - z₀ = 0 := by simpa using h0
      have := hw_z₀ w hw; rw [hsub0, norm_zero] at this; linarith
  rw [← γ.pathIntegral_sub hf_z hf_z₀]
  have hpt : ∀ w ∈ γ.trace, ‖(w - z)⁻¹ - (w - z₀)⁻¹‖ ≤ ‖z - z₀‖ / (2 * δ ^ 2) := by
    intro w hw
    have hne1 : w - z ≠ 0 := fun h0 => by have := hw_z w hw; rw [h0, norm_zero] at this; linarith
    have hne2 : w - z₀ ≠ 0 := fun h0 => by have := hw_z₀ w hw; rw [h0, norm_zero] at this; linarith
    have halg : (w - z)⁻¹ - (w - z₀)⁻¹ = (z - z₀) / ((w - z) * (w - z₀)) := by
      field_simp
      ring
    rw [halg, norm_div, norm_mul]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (by nlinarith [hw_z w hw, hw_z₀ w hw])
  have hle := γ.norm_pathIntegral_le (hf_z.sub hf_z₀) hpt
  have hlen_lt : pathLength γ.toBookCurve < L := by linarith
  calc ‖pathIntegral (fun x => (x - z)⁻¹ - (x - z₀)⁻¹) γ.toBookCurve‖
      ≤ (‖z - z₀‖ / (2 * δ ^ 2)) * pathLength γ.toBookCurve := hle
    _ ≤ (‖z - z₀‖ / (2 * δ ^ 2)) * L :=
        mul_le_mul_of_nonneg_left hlen_lt.le (div_nonneg (norm_nonneg _) (by positivity))
    _ < ((ε * (2 * δ ^ 2) / L) / (2 * δ ^ 2)) * L :=
        mul_lt_mul_of_pos_right (div_lt_div_of_pos_right hz_bound (by positivity)) hLpos
    _ = ε := by field_simp

theorem continuousOn_Ind (γ : BookPath) :
    ContinuousOn (Ind γ.toBookCurve) (γ.trace)ᶜ :=
  continuousOn_const.mul (continuousOn_pathIntegral_sub_inv γ)

/-- Any continuous function into `Set.range ((↑) : ℤ → ℂ)` on a preconnected set is constant. -/
private theorem eq_on_preconnected_of_mem_int_range {C : Set ℂ} (hC : IsPreconnected C)
    {g : ℂ → ℂ} (hg : ContinuousOn g C) (hint : ∀ z ∈ C, ∃ n : ℤ, g z = n)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ C) (hz₂ : z₂ ∈ C) :
    g z₁ = g z₂ := by
  have hsame : ∀ z ∈ C, dist (g z) (g z₁) < 1 → g z = g z₁ := by
    intro z hz hdist
    obtain ⟨n, hn⟩ := hint z hz
    obtain ⟨n₁, hn₁⟩ := hint z₁ hz₁
    rw [hn, hn₁, dist_eq_norm, ← Int.cast_sub, Complex.norm_intCast] at hdist
    have hsub : (n - n₁ : ℤ) = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hdist)
    rw [hn, hn₁, sub_eq_zero.mp hsub]
  obtain ⟨V₁, hV₁open, hV₁eq⟩ := continuousOn_iff'.mp hg (Metric.ball (g z₁) 1) Metric.isOpen_ball
  obtain ⟨V₂, hV₂open, hV₂eq⟩ := continuousOn_iff'.mp hg ({g z₁}ᶜ) isClosed_singleton.isOpen_compl
  by_contra hne
  have hcover : C ⊆ V₁ ∪ V₂ := by
    intro z hz
    by_cases heq : g z = g z₁
    · left
      have : z ∈ g ⁻¹' Metric.ball (g z₁) 1 ∩ C := ⟨by simp [heq], hz⟩
      rw [hV₁eq] at this
      exact this.1
    · right
      have : z ∈ g ⁻¹' {g z₁}ᶜ ∩ C := ⟨heq, hz⟩
      rw [hV₂eq] at this
      exact this.1
  have hCV₁ : (C ∩ V₁).Nonempty := ⟨z₁, by
    rw [inter_comm, ← hV₁eq]; exact ⟨Metric.mem_ball_self zero_lt_one, hz₁⟩⟩
  have hCV₂ : (C ∩ V₂).Nonempty := ⟨z₂, by
    rw [inter_comm, ← hV₂eq]; exact ⟨Ne.symm hne, hz₂⟩⟩
  obtain ⟨w, hwC, hwV₁, hwV₂⟩ := hC V₁ V₂ hV₁open hV₂open hcover hCV₁ hCV₂
  have hw1 : w ∈ g ⁻¹' Metric.ball (g z₁) 1 ∩ C := hV₁eq ▸ ⟨hwV₁, hwC⟩
  have hw2 : w ∈ g ⁻¹' {g z₁}ᶜ ∩ C := hV₂eq ▸ ⟨hwV₂, hwC⟩
  exact hw2.1 (hsame w hwC hw1.1)

/-- 10.10: `Ind_γ` is constant on every connected subset (in particular every component) of `(γ*)ᶜ`. -/
theorem Ind_eq_of_isPreconnected_compl (γ : BookPath) (hclosed : γ.IsClosed)
    {C : Set ℂ} (hC : IsPreconnected C) (hCsub : C ⊆ (γ.trace)ᶜ)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ C) (hz₂ : z₂ ∈ C) :
    Ind γ.toBookCurve z₁ = Ind γ.toBookCurve z₂ :=
  eq_on_preconnected_of_mem_int_range hC ((continuousOn_Ind γ).mono hCsub)
    (fun _ hz => Ind_mem_int γ hclosed (hCsub hz)) hz₁ hz₂

/-- 10.10: `Ind_γ` vanishes outside any closed disc containing `γ*`, and in particular on the
unique unbounded component of `(γ*)ᶜ`. -/
theorem Ind_eq_zero_of_mem_unbounded_component (γ : BookPath) (hclosed : γ.IsClosed)
    {U : Set ℂ} (hU : U ∈ bookComponents (γ.trace)ᶜ) (hunbdd : ¬ Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) :
    Ind γ.toBookCurve z = 0 := by
  obtain ⟨U₀, ⟨_, _⟩, hU₀_uniq⟩ :=
    existsUnique_unbounded_component_compl γ.isCompact_trace
  have hU_eq : U = U₀ := hU₀_uniq U ⟨hU, hunbdd⟩
  obtain ⟨R, hRpos, hRsub⟩ := γ.isCompact_trace.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  let M : ℝ := R + 1 + pathLength γ.toBookCurve
  have hM_gt_R : R < M := by linarith [γ.pathLength_nonneg]
  have hMpos : 0 < M := lt_trans hRpos hM_gt_R
  let zStar : ℂ := (M : ℂ)
  have hz_ext : zStar ∈ (Metric.closedBall (0 : ℂ) R)ᶜ := by
    rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_zero_right]
    simp only [zStar, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos]
    exact hM_gt_R
  have hext_sub_U : (Metric.closedBall (0 : ℂ) R)ᶜ ⊆ U := by
    have hext_conn := isConnected_compl_closedBall (0 : ℂ) hRpos.le
    have hext_compl : (Metric.closedBall (0 : ℂ) R)ᶜ ⊆ (γ.trace)ᶜ := compl_subset_compl.mpr hRsub
    let C₀ := bookComponent (γ.trace)ᶜ zStar
    have hC₀_mem : C₀ ∈ bookComponents (γ.trace)ᶜ := ⟨zStar, hext_compl hz_ext, rfl⟩
    have hsub : (Metric.closedBall (0 : ℂ) R)ᶜ ⊆ C₀ :=
      bookComponent_maximal hext_compl ((bookConnected_iff_isPreconnected _).mpr hext_conn.2) hz_ext
    have hC₀_unbdd : ¬ Bornology.IsBounded C₀ := by
      intro hbdd
      obtain ⟨B, _, hB⟩ := hbdd.subset_closedBall_lt 0 (0 : ℂ)
      let w : ℂ := ((max R B + 1 : ℝ) : ℂ)
      have hw_ext : w ∈ (Metric.closedBall (0 : ℂ) R)ᶜ := by
        rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_zero_right]
        have hp : 0 < max R B + 1 := lt_of_lt_of_le hRpos (le_trans (le_max_left R B) (by linarith))
        simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
        exact lt_of_le_of_lt (le_max_left R B) (by linarith)
      have hwB := hB (hsub hw_ext)
      rw [Metric.mem_closedBall, dist_zero_right] at hwB
      have hp : 0 < max R B + 1 := lt_of_lt_of_le hRpos (le_trans (le_max_left R B) (by linarith))
      simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp] at hwB
      linarith [le_max_right R B]
    have hC₀_eq : C₀ = U₀ := hU₀_uniq C₀ ⟨hC₀_mem, hC₀_unbdd⟩
    rwa [hU_eq, ← hC₀_eq]
  have hzStar_U : zStar ∈ U := hext_sub_U hz_ext
  obtain ⟨x, _, rfl⟩ := hU
  have hU_pre : IsPreconnected (bookComponent (γ.trace)ᶜ x) :=
    (bookConnected_iff_isPreconnected _).mp (bookComponent_connected _ _)
  rw [Ind_eq_of_isPreconnected_compl γ hclosed hU_pre (bookComponent_subset _ _) hz hzStar_U]
  have hzStar_not : zStar ∉ γ.trace := bookComponent_subset (γ.trace)ᶜ x hzStar_U
  obtain ⟨n, hn⟩ := Ind_mem_int γ hclosed hzStar_not
  have hbound : ∀ w ∈ γ.trace, ‖(w - zStar)⁻¹‖ ≤ (1 + pathLength γ.toBookCurve)⁻¹ := by
    intro w hw
    have hwR : ‖w‖ ≤ R := by simpa [Metric.mem_closedBall] using hRsub hw
    have hnorm_z : ‖zStar‖ = M := by
      simp [zStar, abs_of_pos hMpos]
    have hdiff : 1 + pathLength γ.toBookCurve ≤ ‖w - zStar‖ := by
      have htri : ‖zStar‖ ≤ ‖w - zStar‖ + ‖w‖ := by
        calc ‖zStar‖ = ‖zStar - w + w‖ := by ring_nf
          _ ≤ ‖zStar - w‖ + ‖w‖ := norm_add_le _ _
          _ = ‖w - zStar‖ + ‖w‖ := by rw [norm_sub_rev]
      linarith [γ.pathLength_nonneg]
    rw [norm_inv]
    exact inv_anti₀ (by linarith [γ.pathLength_nonneg]) hdiff
  have hf_cont : ContinuousOn (fun w : ℂ => (w - zStar)⁻¹) γ.trace :=
    (continuous_id.sub continuous_const).continuousOn.inv₀ fun w hw h0 => by
      have hwz : w = zStar := sub_eq_zero.mp (by simpa using h0)
      exact hzStar_not (hwz ▸ hw)
  have hint_le := γ.norm_pathIntegral_le hf_cont hbound
  have hlt_one : ‖Ind γ.toBookCurve zStar‖ < 1 := by
    unfold Ind
    rw [norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hnum_lt : ‖pathIntegral (fun w => (w - zStar)⁻¹) γ.toBookCurve‖ < 1 := by
      have hden_pos : 0 < 1 + pathLength γ.toBookCurve := by linarith [γ.pathLength_nonneg]
      calc ‖pathIntegral (fun w => (w - zStar)⁻¹) γ.toBookCurve‖
          ≤ (1 + pathLength γ.toBookCurve)⁻¹ * pathLength γ.toBookCurve := hint_le
        _ < (1 + pathLength γ.toBookCurve)⁻¹ * (1 + pathLength γ.toBookCurve) :=
            mul_lt_mul_of_pos_left (by linarith) (inv_pos.mpr hden_pos)
        _ = 1 := inv_mul_cancel₀ hden_pos.ne'
    have h2pi : (1 : ℝ) < 2 * Real.pi := by linarith [Real.two_le_pi]
    calc (2 * Real.pi)⁻¹ * ‖pathIntegral (fun w => (w - zStar)⁻¹) γ.toBookCurve‖
        < (2 * Real.pi)⁻¹ * 1 := mul_lt_mul_of_pos_left hnum_lt (inv_pos.mpr Real.two_pi_pos)
      _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ h2pi
  rw [hn, Complex.norm_intCast] at hlt_one
  have hn0 : n = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hlt_one)
  simp [hn, hn0]

/-- 10.10 (Theorem): full statement of Rudin Theorem 10.10 — for any closed path `γ`, `(γ*)ᶜ`
has a unique unbounded component, `Ind_γ(z)` is an integer for every `z ∉ γ*`, is constant on
each component of `(γ*)ᶜ`, and equals `0` on the unbounded component. -/
theorem theorem10_10 (γ : BookPath) (hclosed : γ.IsClosed) :
    (∃! U : Set ℂ, U ∈ bookComponents (γ.trace)ᶜ ∧ ¬ Bornology.IsBounded U) ∧
    (∀ z ∉ γ.trace, ∃ n : ℤ, Ind γ.toBookCurve z = n) ∧
    (∀ C ∈ bookComponents (γ.trace)ᶜ, ∀ z₁ ∈ C, ∀ z₂ ∈ C,
      Ind γ.toBookCurve z₁ = Ind γ.toBookCurve z₂) ∧
    (∀ U ∈ bookComponents (γ.trace)ᶜ, ¬ Bornology.IsBounded U →
      ∀ z ∈ U, Ind γ.toBookCurve z = 0) := by
  refine ⟨existsUnique_unbounded_component_compl γ.isCompact_trace,
    fun z hz => Ind_mem_int γ hclosed hz, ?_,
    fun U hU hunbdd z hz => Ind_eq_zero_of_mem_unbounded_component γ hclosed hU hunbdd hz⟩
  rintro C ⟨x, _, rfl⟩ z₁ hz₁ z₂ hz₂
  exact Ind_eq_of_isPreconnected_compl γ hclosed
    ((bookConnected_iff_isPreconnected _).mp (bookComponent_connected _ _))
    (bookComponent_subset _ _) hz₁ hz₂

/-! ### 10.11: Index of a positively oriented circle -/

/-- 10.11: for `r > 0`, `Ind_γ(z) = 1` if `|z - a| < r` and `Ind_γ(z) = 0` if `|z - a| > r`,
where `γ` is the positively oriented circle `positivelyOrientedCircle a r hr`. -/
theorem Ind_positivelyOrientedCircle_inside {a z : ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ disc a r) :
    Ind (positivelyOrientedCircle a r hr).toBookCurve z = 1 := by
  unfold Ind
  rw [pathIntegral_positivelyOrientedCircle_eq_circleIntegral _ a hr,
    circleIntegral.integral_sub_inv_of_mem_ball hz,
    inv_mul_cancel₀ two_pi_I_ne_zero]

theorem Ind_positivelyOrientedCircle_outside {a z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : r < ‖z - a‖) :
    Ind (positivelyOrientedCircle a r hr).toBookCurve z = 0 := by
  have hext_conn := isConnected_compl_closedBall a hr.le
  have htr : (positivelyOrientedCircle a r hr).trace = Metric.sphere a r :=
    positivelyOrientedCircle_trace a hr
  have hext_sub : (Metric.closedBall a r)ᶜ ⊆ ((positivelyOrientedCircle a r hr).trace)ᶜ := by
    rw [htr]
    exact compl_subset_compl.mpr Metric.sphere_subset_closedBall
  have hz_ext : z ∈ (Metric.closedBall a r)ᶜ := by
    rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_eq_norm]
    exact hz
  let U := bookComponent ((positivelyOrientedCircle a r hr).trace)ᶜ z
  have hU_mem : U ∈ bookComponents ((positivelyOrientedCircle a r hr).trace)ᶜ :=
    ⟨z, hext_sub hz_ext, rfl⟩
  have hsub_U : (Metric.closedBall a r)ᶜ ⊆ U :=
    bookComponent_maximal hext_sub ((bookConnected_iff_isPreconnected _).mpr hext_conn.2) hz_ext
  have hU_unbdd : ¬ Bornology.IsBounded U := by
    intro hbdd
    obtain ⟨B, _, hB⟩ := hbdd.subset_closedBall_lt 0 a
    let w : ℂ := a + ((max r B + 1 : ℝ) : ℂ)
    have hp : 0 < max r B + 1 := lt_of_lt_of_le hr (le_trans (le_max_left r B) (by linarith))
    have hw_ext : w ∈ (Metric.closedBall a r)ᶜ := by
      rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_eq_norm]
      simp only [w, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
      exact lt_of_le_of_lt (le_max_left r B) (by linarith)
    have hwB := hB (hsub_U hw_ext)
    rw [Metric.mem_closedBall, dist_eq_norm] at hwB
    simp only [w, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp] at hwB
    linarith [le_max_right r B]
  exact Ind_eq_zero_of_mem_unbounded_component (positivelyOrientedCircle a r hr)
    (positivelyOrientedCircle_isClosed a hr) hU_mem hU_unbdd
    (mem_bookComponent (hext_sub hz_ext))

theorem theorem10_11 (a : ℂ) {r : ℝ} (hr : 0 < r) (z : ℂ)
    (hz : z ∉ (positivelyOrientedCircle a r hr).trace) :
    Ind (positivelyOrientedCircle a r hr).toBookCurve z =
      if ‖z - a‖ < r then 1 else 0 := by
  split_ifs with hlt
  · exact Ind_positivelyOrientedCircle_inside hr (mem_disc.mpr hlt)
  · have hne : ‖z - a‖ ≠ r := by
      rw [positivelyOrientedCircle_trace a hr, Metric.mem_sphere, dist_eq_norm] at hz
      exact hz
    exact Ind_positivelyOrientedCircle_outside hr (lt_of_le_of_ne (not_lt.mp hlt) hne.symm)

/-! ### 10.34: Chains, cycles, equivalence of representations, and chain index -/

/-- Tietze extension for `ℂ`-valued continuous functions on closed subsets of `ℂ` (via real and
imaginary parts and `Real.instTietzeExtension`). -/
private theorem exists_continuous_extension_complex {K : Set ℂ} (hK : IsClosed K)
    {f : ℂ → ℂ} (hf : ContinuousOn f K) :
    ∃ F : ℂ → ℂ, Continuous F ∧ EqOn F f K := by
  let fre : C(K, ℝ) := ⟨fun x => (f x).re, (Complex.continuous_re.comp_continuousOn hf).domRestrict⟩
  let fim : C(K, ℝ) := ⟨fun x => (f x).im, (Complex.continuous_im.comp_continuousOn hf).domRestrict⟩
  obtain ⟨gre, hgre⟩ := ContinuousMap.exists_restrict_eq hK fre
  obtain ⟨gim, hgim⟩ := ContinuousMap.exists_restrict_eq hK fim
  refine ⟨fun z => ⟨gre z, gim z⟩, ?_, ?_⟩
  · have hsum : (fun z : ℂ => (⟨gre z, gim z⟩ : ℂ)) =
        fun z => (gre z : ℂ) + (gim z : ℂ) * Complex.I := by
      funext z
      apply Complex.ext <;> simp
    rw [hsum]
    exact (Complex.continuous_ofReal.comp gre.continuous).add
      ((Complex.continuous_ofReal.comp gim.continuous).mul continuous_const)
  · intro z hz
    have hre : gre z = (f z).re := congr_arg (fun φ : C(K, ℝ) => φ ⟨z, hz⟩) hgre
    have him : gim z = (f z).im := congr_arg (fun φ : C(K, ℝ) => φ ⟨z, hz⟩) hgim
    exact Complex.ext hre him

/-- 10.34: a chain `Γ = γ₁ + ⋯ + γₙ` represented as a finite formal list of paths in `ℂ`. -/
abbrev BookChain := List BookPath

namespace BookChain

/-- 10.34: trace `Γ* = γ₁* ∪ ⋯ ∪ γₙ*` of a chain. -/
def trace (Γ : BookChain) : Set ℂ :=
  ⋃ γ ∈ Γ, γ.trace

theorem isCompact_trace (Γ : BookChain) : IsCompact Γ.trace := by
  induction Γ with
  | nil => simp [trace]
  | cons γ Γ ih =>
    simp only [trace, List.mem_cons, iUnion_iUnion_eq_or_left]
    exact γ.isCompact_trace.union ih

theorem isClosed_trace (Γ : BookChain) : IsClosed Γ.trace :=
  Γ.isCompact_trace.isClosed

@[simp] theorem trace_nil : trace ([] : BookChain) = ∅ := by simp [trace]

@[simp] theorem trace_singleton (γ : BookPath) : trace [γ] = γ.trace := by simp [trace]

@[simp] theorem trace_cons (γ : BookPath) (Γ : BookChain) :
    trace (γ :: Γ) = γ.trace ∪ trace Γ := by
  simp [trace, List.mem_cons, iUnion_iUnion_eq_or_left]

@[simp] theorem trace_append (Γ₁ Γ₂ : BookChain) :
    trace (Γ₁ ++ Γ₂) = trace Γ₁ ∪ trace Γ₂ := by
  induction Γ₁ with
  | nil => simp
  | cons γ Γ₁ ih => simp [ih, union_assoc]

/-- 10.34: opposite chain `-Γ = γ₁⁻ + ⋯ + γₙ⁻`. -/
def neg (Γ : BookChain) : BookChain :=
  Γ.map BookPath.reverse

@[simp] theorem trace_neg (Γ : BookChain) : (neg Γ).trace = Γ.trace := by
  induction Γ with
  | nil => simp [neg]
  | cons γ Γ ih =>
    change trace (γ.reverse :: neg Γ) = _
    simp [ih]

/-- 10.34: integral `∫_Γ f(z) dz = ∑ᵢ ∫_{γᵢ} f(z) dz` along a chain. -/
def integral (f : ℂ → ℂ) (Γ : BookChain) : ℂ :=
  (Γ.map (fun γ => pathIntegral f γ.toBookCurve)).sum

@[simp] theorem integral_nil (f : ℂ → ℂ) : integral f [] = 0 := rfl

@[simp] theorem integral_singleton (f : ℂ → ℂ) (γ : BookPath) :
    integral f [γ] = pathIntegral f γ.toBookCurve := by
  simp [integral]

@[simp] theorem integral_cons (f : ℂ → ℂ) (γ : BookPath) (Γ : BookChain) :
    integral f (γ :: Γ) = pathIntegral f γ.toBookCurve + integral f Γ := by
  simp [integral]

@[simp] theorem integral_append (f : ℂ → ℂ) (Γ₁ Γ₂ : BookChain) :
    integral f (Γ₁ ++ Γ₂) = integral f Γ₁ + integral f Γ₂ := by
  simp [integral, List.map_append, List.sum_append]

theorem integral_congr {f g : ℂ → ℂ} (Γ : BookChain) (hfg : EqOn f g Γ.trace) :
    integral f Γ = integral g Γ := by
  induction Γ with
  | nil => rfl
  | cons γ Γ ih =>
    rw [trace_cons] at hfg
    simp only [integral_cons]
    rw [BookPath.pathIntegral_congr γ.toBookCurve (hfg.mono subset_union_left),
      ih (hfg.mono subset_union_right)]

theorem integral_add (Γ : BookChain) {f g : ℂ → ℂ}
    (hf : ContinuousOn f Γ.trace) (hg : ContinuousOn g Γ.trace) :
    integral (fun z => f z + g z) Γ = integral f Γ + integral g Γ := by
  induction Γ with
  | nil => simp
  | cons γ Γ ih =>
    rw [trace_cons] at hf hg
    simp only [integral_cons, γ.pathIntegral_add (hf.mono subset_union_left) (hg.mono subset_union_left),
      ih (hf.mono subset_union_right) (hg.mono subset_union_right)]
    ring

theorem integral_const_mul (c : ℂ) (f : ℂ → ℂ) (Γ : BookChain) :
    integral (fun z => c * f z) Γ = c * integral f Γ := by
  induction Γ with
  | nil => simp
  | cons γ Γ ih =>
    simp only [integral_cons, BookPath.pathIntegral_const_mul, ih]
    ring

theorem integral_sub (Γ : BookChain) {f g : ℂ → ℂ}
    (hf : ContinuousOn f Γ.trace) (hg : ContinuousOn g Γ.trace) :
    integral (fun z => f z - g z) Γ = integral f Γ - integral g Γ := by
  induction Γ with
  | nil => simp
  | cons γ Γ ih =>
    rw [trace_cons] at hf hg
    simp only [integral_cons, γ.pathIntegral_sub (hf.mono subset_union_left) (hg.mono subset_union_left),
      ih (hf.mono subset_union_right) (hg.mono subset_union_right)]
    ring

theorem integral_neg (Γ : BookChain) {f : ℂ → ℂ} (hf : ContinuousOn f Γ.trace) :
    integral f (neg Γ) = -integral f Γ := by
  induction Γ with
  | nil => simp [neg]
  | cons γ Γ ih =>
    rw [trace_cons] at hf
    change integral f (γ.reverse :: neg Γ) = _
    rw [integral_cons, integral_cons, γ.pathIntegral_reverse (hf.mono subset_union_left),
      ih (hf.mono subset_union_right)]
    ring

/-- 10.34: two chain representations `Γ₁` and `Γ₂` define the same integration functional if
`∫_{Γ₁} f = ∫_{Γ₂} f` for every continuous `f` on `Γ₁* ∪ Γ₂*`. -/
def Equiv (Γ₁ Γ₂ : BookChain) : Prop :=
  ∀ f : ℂ → ℂ, ContinuousOn f (Γ₁.trace ∪ Γ₂.trace) → integral f Γ₁ = integral f Γ₂

/-- By Tietze extension on the compact set `Γ₁* ∪ Γ₂*`, `BookChain.Equiv Γ₁ Γ₂` holds iff the
integrals agree on all globally continuous functions `f : ℂ → ℂ`. -/
theorem equiv_iff_forall_continuous (Γ₁ Γ₂ : BookChain) :
    Equiv Γ₁ Γ₂ ↔ ∀ f : ℂ → ℂ, Continuous f → integral f Γ₁ = integral f Γ₂ := by
  constructor
  · intro h f hf
    exact h f hf.continuousOn
  · intro h f hf
    obtain ⟨F, hFcont, hFeq⟩ := exists_continuous_extension_complex
      (Γ₁.isClosed_trace.union Γ₂.isClosed_trace) hf
    rw [← integral_congr Γ₁ (hFeq.mono subset_union_left),
        ← integral_congr Γ₂ (hFeq.mono subset_union_right)]
    exact h F hFcont

theorem equiv_refl (Γ : BookChain) : Equiv Γ Γ := fun _ _ => rfl

theorem equiv_symm {Γ₁ Γ₂ : BookChain} (h : Equiv Γ₁ Γ₂) : Equiv Γ₂ Γ₁ :=
  fun f hf => (h f (union_comm Γ₂.trace Γ₁.trace ▸ hf)).symm

theorem equiv_trans {Γ₁ Γ₂ Γ₃ : BookChain} (h₁₂ : Equiv Γ₁ Γ₂) (h₂₃ : Equiv Γ₂ Γ₃) :
    Equiv Γ₁ Γ₃ := by
  rw [equiv_iff_forall_continuous] at h₁₂ h₂₃ ⊢
  exact fun f hf => (h₁₂ f hf).trans (h₂₃ f hf)

def instSetoid : Setoid BookChain where
  r := Equiv
  iseqv := ⟨equiv_refl, equiv_symm, equiv_trans⟩

theorem equiv_append {Γ₁ Γ₁' Γ₂ Γ₂' : BookChain}
    (h₁ : Equiv Γ₁ Γ₁') (h₂ : Equiv Γ₂ Γ₂') :
    Equiv (Γ₁ ++ Γ₂) (Γ₁' ++ Γ₂') := by
  rw [equiv_iff_forall_continuous] at h₁ h₂ ⊢
  intro f hf
  simp [h₁ f hf, h₂ f hf]

theorem equiv_neg_congr {Γ₁ Γ₂ : BookChain} (h : Equiv Γ₁ Γ₂) :
    Equiv (neg Γ₁) (neg Γ₂) := by
  rw [equiv_iff_forall_continuous] at h ⊢
  intro f hf
  rw [integral_neg _ hf.continuousOn, integral_neg _ hf.continuousOn, h f hf]

theorem equiv_cancel_reverse (γ : BookPath) : Equiv [γ, γ.reverse] [] := by
  intro f hf
  simp only [trace_cons, trace_nil, BookPath.reverse_trace, union_empty, union_self] at hf
  simp [γ.pathIntegral_reverse hf]

theorem equiv_concat (γ₁ γ₂ : BookPath) (hjoin : γ₁.toFun γ₁.β = γ₂.toFun γ₂.α) :
    Equiv [γ₁.concat γ₂ hjoin] [γ₁, γ₂] := by
  intro f hf
  rw [trace_singleton] at hf
  have hf' : ContinuousOn f (γ₁.concat γ₂ hjoin).trace := hf.mono subset_union_left
  simp [γ₁.pathIntegral_concat γ₂ hjoin hf']

theorem equiv_split_restrict (γ : BookPath) {m : ℝ} (hαm : γ.α < m) (hmβ : m < γ.β) :
    Equiv [γ] [γ.restrict le_rfl hαm hmβ.le, γ.restrict hαm.le hmβ le_rfl] := by
  intro f hf
  have hfγ : ContinuousOn f γ.trace := hf.mono (by simp)
  simp only [integral_cons, integral_nil, add_zero,
    BookPath.pathIntegral_restrict]
  unfold pathIntegral
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((γ.intervalIntegrable_pathIntegral hfγ).mono_set
      (by rw [Set.uIcc_of_le hαm.le, Set.uIcc_of_le γ.le_endpoints]; exact Icc_subset_Icc le_rfl hmβ.le))
    ((γ.intervalIntegrable_pathIntegral hfγ).mono_set
      (by rw [Set.uIcc_of_le hmβ.le, Set.uIcc_of_le γ.le_endpoints]; exact Icc_subset_Icc hαm.le le_rfl))).symm

/-- 10.34: index `Ind_Γ(z) = (2πi)⁻¹ ∫_Γ (ζ - z)⁻¹ dζ = ∑ᵢ Ind_{γᵢ}(z)` of a chain. -/
def Ind (Γ : BookChain) (z : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * integral (fun w => (w - z)⁻¹) Γ

@[simp] theorem Ind_nil (z : ℂ) : Ind [] z = 0 := by simp [Ind]

@[simp] theorem Ind_singleton (γ : BookPath) (z : ℂ) :
    Ind [γ] z = RudinRCA.Chapter10.Ind γ.toBookCurve z := by
  simp [Ind, RudinRCA.Chapter10.Ind]

@[simp] theorem Ind_cons (γ : BookPath) (Γ : BookChain) (z : ℂ) :
    Ind (γ :: Γ) z = RudinRCA.Chapter10.Ind γ.toBookCurve z + Ind Γ z := by
  simp [Ind, RudinRCA.Chapter10.Ind, mul_add]

@[simp] theorem Ind_append (Γ₁ Γ₂ : BookChain) (z : ℂ) :
    Ind (Γ₁ ++ Γ₂) z = Ind Γ₁ z + Ind Γ₂ z := by
  simp [Ind, mul_add]

theorem Ind_neg (Γ : BookChain) {z : ℂ} (hz : z ∉ Γ.trace) :
    Ind (neg Γ) z = -Ind Γ z := by
  have hf : ContinuousOn (fun w : ℂ => (w - z)⁻¹) Γ.trace :=
    (continuous_id.sub continuous_const).continuousOn.inv₀ fun w hw h0 =>
      hz (sub_eq_zero.mp (by simpa using h0) ▸ hw)
  simp [Ind, integral_neg Γ hf]

/-- 10.34: `Ind_Γ(z)` is independent of the representation of `Γ` whenever `z ∉ Γ₁* ∪ Γ₂*`. -/
theorem Ind_congr_equiv {Γ₁ Γ₂ : BookChain} (heq : Equiv Γ₁ Γ₂)
    {z : ℂ} (hz : z ∉ Γ₁.trace ∪ Γ₂.trace) :
    Ind Γ₁ z = Ind Γ₂ z := by
  have hf : ContinuousOn (fun w : ℂ => (w - z)⁻¹) (Γ₁.trace ∪ Γ₂.trace) :=
    (continuous_id.sub continuous_const).continuousOn.inv₀ fun w hw h0 =>
      hz (sub_eq_zero.mp (by simpa using h0) ▸ hw)
  simp [Ind, heq _ hf]

/-- 10.34: a chain `Γ` is a cycle if it is equivalent to a chain of closed paths supported in `Γ*`. -/
def IsCycle (Γ : BookChain) : Prop :=
  ∃ Δ : BookChain, (∀ σ ∈ Δ, σ.IsClosed) ∧ Δ.trace ⊆ Γ.trace ∧ Equiv Γ Δ

theorem isCycle_nil : IsCycle [] :=
  ⟨[], by simp, Subset.rfl, equiv_refl []⟩

theorem isCycle_singleton_of_isClosed {γ : BookPath} (h : γ.IsClosed) : IsCycle [γ] :=
  ⟨[γ], by simp [h], Subset.rfl, equiv_refl [γ]⟩

theorem isCycle_of_forall_isClosed {Γ : BookChain} (h : ∀ γ ∈ Γ, γ.IsClosed) : IsCycle Γ :=
  ⟨Γ, h, Subset.rfl, equiv_refl Γ⟩

theorem isCycle_append {Γ₁ Γ₂ : BookChain} (h₁ : IsCycle Γ₁) (h₂ : IsCycle Γ₂) :
    IsCycle (Γ₁ ++ Γ₂) := by
  obtain ⟨Δ₁, hcl₁, hsub₁, heq₁⟩ := h₁
  obtain ⟨Δ₂, hcl₂, hsub₂, heq₂⟩ := h₂
  refine ⟨Δ₁ ++ Δ₂, ?_, ?_, equiv_append heq₁ heq₂⟩
  · intro σ hσ
    rcases List.mem_append.mp hσ with h | h
    · exact hcl₁ σ h
    · exact hcl₂ σ h
  · simp only [trace_append]
    exact union_subset_union hsub₁ hsub₂

theorem isCycle_neg {Γ : BookChain} (h : IsCycle Γ) : IsCycle (neg Γ) := by
  obtain ⟨Δ, hcl, hsub, heq⟩ := h
  refine ⟨neg Δ, ?_, ?_, equiv_neg_congr heq⟩
  · intro σ hσ
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hσ
    exact BookPath.reverse_isClosed (hcl τ hτ)
  · simpa using hsub

/-- 10.34: explicit witness that a cycle may be represented as a sum of paths that are NOT
individually closed (upper and lower semicircles of the unit circle). -/
theorem exists_cycle_of_open_paths :
    ∃ γ₁ γ₂ : BookPath, ¬ γ₁.IsClosed ∧ ¬ γ₂.IsClosed ∧ IsCycle [γ₁, γ₂] := by
  let γ₁ := circleArcPath 0 1 Real.pi_pos
  let γ₂ := circleArcPath 0 1 (show Real.pi < 2 * Real.pi by linarith [Real.pi_pos])
  have h1 : ¬ γ₁.IsClosed := by
    simp only [γ₁, BookPath.IsClosed, BookCurve.IsClosed, circleArcPath, BookPath.ofC1, circleMap,
      zero_add, Complex.exp_pi_mul_I]
    norm_num
  have h2 : ¬ γ₂.IsClosed := by
    simp only [γ₂, BookPath.IsClosed, BookCurve.IsClosed, circleArcPath, BookPath.ofC1, circleMap,
      zero_add, Complex.exp_pi_mul_I]
    norm_num
  have hjoin : γ₁.toFun γ₁.β = γ₂.toFun γ₂.α := rfl
  refine ⟨γ₁, γ₂, h1, h2, [γ₁.concat γ₂ hjoin], ?_, ?_, equiv_symm (equiv_concat γ₁ γ₂ hjoin)⟩
  · intro σ hσ
    rcases List.mem_singleton.mp hσ with rfl
    simp [BookPath.IsClosed, BookCurve.IsClosed, γ₁, γ₂, circleArcPath, BookPath.ofC1, circleMap]
  · simp [γ₁.concat_trace γ₂ hjoin]

/-- 10.34: for any cycle `Γ`, `Ind_Γ(z)` is an integer off `Γ*`, constant on each connected
subset of `(Γ*)ᶜ`, and `0` on the unique unbounded component of `(Γ*)ᶜ`. -/
theorem Ind_mem_int_of_isCycle {Γ : BookChain} (hcyc : IsCycle Γ) {z : ℂ} (hz : z ∉ Γ.trace) :
    ∃ n : ℤ, Ind Γ z = n := by
  obtain ⟨Δ, hcl, hsub, heq⟩ := hcyc
  have hzΔ : z ∉ Δ.trace := fun h => hz (hsub h)
  rw [Ind_congr_equiv heq (fun h => h.elim hz hzΔ)]
  clear hsub heq hz
  induction Δ with
  | nil => exact ⟨0, by simp⟩
  | cons σ Δ ih =>
    rw [trace_cons] at hzΔ
    obtain ⟨n₁, hn₁⟩ := RudinRCA.Chapter10.Ind_mem_int σ (hcl σ List.mem_cons_self)
      (fun h => hzΔ (Or.inl h))
    obtain ⟨n₂, hn₂⟩ := ih (fun τ hτ => hcl τ (List.mem_cons_of_mem _ hτ))
      (fun h => hzΔ (Or.inr h))
    exact ⟨n₁ + n₂, by simp [hn₁, hn₂]⟩

theorem continuousOn_Ind (Γ : BookChain) :
    ContinuousOn (Ind Γ) (Γ.trace)ᶜ := by
  induction Γ with
  | nil =>
    have : Ind [] = fun _ => (0 : ℂ) := funext Ind_nil
    rw [this]
    exact continuousOn_const
  | cons γ Γ ih =>
    have hfun : Ind (γ :: Γ) = fun z => RudinRCA.Chapter10.Ind γ.toBookCurve z + Ind Γ z :=
      funext (Ind_cons γ Γ)
    rw [hfun, trace_cons, compl_union]
    exact ((RudinRCA.Chapter10.continuousOn_Ind γ).mono inter_subset_left).add
      (ih.mono inter_subset_right)

theorem Ind_eq_of_isPreconnected_compl_of_isCycle {Γ : BookChain} (hcyc : IsCycle Γ)
    {C : Set ℂ} (hC : IsPreconnected C) (hCsub : C ⊆ (Γ.trace)ᶜ)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ C) (hz₂ : z₂ ∈ C) :
    Ind Γ z₁ = Ind Γ z₂ :=
  eq_on_preconnected_of_mem_int_range hC ((continuousOn_Ind Γ).mono hCsub)
    (fun _ hz => Ind_mem_int_of_isCycle hcyc (hCsub hz)) hz₁ hz₂

theorem Ind_eq_zero_of_mem_unbounded_component_of_isCycle {Γ : BookChain} (hcyc : IsCycle Γ)
    {U : Set ℂ} (hU : U ∈ bookComponents (Γ.trace)ᶜ) (hunbdd : ¬ Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) :
    Ind Γ z = 0 := by
  have ⟨Δ, hcl, hsub, heq⟩ := hcyc
  obtain ⟨R, hRpos, hRsub⟩ := Γ.isCompact_trace.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  obtain ⟨U₀, ⟨_, _⟩, hU₀_uniq⟩ := existsUnique_unbounded_component_compl Γ.isCompact_trace
  have hU_eq : U = U₀ := hU₀_uniq U ⟨hU, hunbdd⟩
  let zStar : ℂ := ((R + 1 : ℝ) : ℂ)
  have hz_ext : zStar ∈ (Metric.closedBall (0 : ℂ) R)ᶜ := by
    rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_zero_right]
    simp only [zStar, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < R + 1)]
    linarith
  have hext_compl : (Metric.closedBall (0 : ℂ) R)ᶜ ⊆ (Γ.trace)ᶜ := compl_subset_compl.mpr hRsub
  have hzStar_U : zStar ∈ U := by
    have hext_conn := isConnected_compl_closedBall (0 : ℂ) hRpos.le
    let C₀ := bookComponent (Γ.trace)ᶜ zStar
    have hC₀_mem : C₀ ∈ bookComponents (Γ.trace)ᶜ := ⟨zStar, hext_compl hz_ext, rfl⟩
    have hsubC : (Metric.closedBall (0 : ℂ) R)ᶜ ⊆ C₀ :=
      bookComponent_maximal hext_compl ((bookConnected_iff_isPreconnected _).mpr hext_conn.2) hz_ext
    have hC₀_unbdd : ¬ Bornology.IsBounded C₀ := by
      intro hbdd
      obtain ⟨B, _, hB⟩ := hbdd.subset_closedBall_lt 0 (0 : ℂ)
      let w : ℂ := ((max R B + 1 : ℝ) : ℂ)
      have hp : 0 < max R B + 1 := lt_of_lt_of_le hRpos (le_trans (le_max_left R B) (by linarith))
      have hw_ext : w ∈ (Metric.closedBall (0 : ℂ) R)ᶜ := by
        rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_zero_right]
        simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
        exact lt_of_le_of_lt (le_max_left R B) (by linarith)
      have hwB := hB (hsubC hw_ext)
      rw [Metric.mem_closedBall, dist_zero_right] at hwB
      simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp] at hwB
      linarith [le_max_right R B]
    have hC₀_eq : C₀ = U₀ := hU₀_uniq C₀ ⟨hC₀_mem, hC₀_unbdd⟩
    rw [hU_eq, ← hC₀_eq]
    exact mem_bookComponent (hext_compl hz_ext)
  obtain ⟨x, _, rfl⟩ := hU
  rw [Ind_eq_of_isPreconnected_compl_of_isCycle hcyc
    ((bookConnected_iff_isPreconnected _).mp (bookComponent_connected _ _))
    (bookComponent_subset _ _) hz hzStar_U]
  have hzStar_notΓ : zStar ∉ Γ.trace := hext_compl hz_ext
  have hzStar_notΔ : zStar ∉ Δ.trace := fun h => hzStar_notΓ (hsub h)
  rw [Ind_congr_equiv heq (fun h => h.elim hzStar_notΓ hzStar_notΔ)]
  have hΔ_ball : Δ.trace ⊆ Metric.closedBall (0 : ℂ) R := hsub.trans hRsub
  clear hsub heq
  induction Δ with
  | nil => simp
  | cons σ Δ ih =>
    rw [trace_cons] at hΔ_ball hzStar_notΔ
    rw [Ind_cons]
    have hσ0 : RudinRCA.Chapter10.Ind σ.toBookCurve zStar = 0 := by
      have hσ_sub : (Metric.closedBall (0 : ℂ) R)ᶜ ⊆ (σ.trace)ᶜ :=
        compl_subset_compl.mpr (subset_union_left.trans hΔ_ball)
      let Cσ := bookComponent (σ.trace)ᶜ zStar
      have hCσ_mem : Cσ ∈ bookComponents (σ.trace)ᶜ := ⟨zStar, hσ_sub hz_ext, rfl⟩
      have hsubσ : (Metric.closedBall (0 : ℂ) R)ᶜ ⊆ Cσ :=
        bookComponent_maximal hσ_sub
          ((bookConnected_iff_isPreconnected _).mpr (isConnected_compl_closedBall 0 hRpos.le).2) hz_ext
      have hCσ_unbdd : ¬ Bornology.IsBounded Cσ := by
        intro hbdd
        obtain ⟨B, _, hB⟩ := hbdd.subset_closedBall_lt 0 (0 : ℂ)
        let w : ℂ := ((max R B + 1 : ℝ) : ℂ)
        have hp : 0 < max R B + 1 := lt_of_lt_of_le hRpos (le_trans (le_max_left R B) (by linarith))
        have hw_ext : w ∈ (Metric.closedBall (0 : ℂ) R)ᶜ := by
          rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_zero_right]
          simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
          exact lt_of_le_of_lt (le_max_left R B) (by linarith)
        have hwB := hB (hsubσ hw_ext)
        rw [Metric.mem_closedBall, dist_zero_right] at hwB
        simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp] at hwB
        linarith [le_max_right R B]
      exact RudinRCA.Chapter10.Ind_eq_zero_of_mem_unbounded_component σ
        (hcl σ List.mem_cons_self) hCσ_mem hCσ_unbdd (mem_bookComponent (hσ_sub hz_ext))
    rw [hσ0, zero_add]
    exact ih (fun τ hτ => hcl τ (List.mem_cons_of_mem _ hτ))
      (fun h => hzStar_notΔ (Or.inr h)) (subset_union_right.trans hΔ_ball)

end BookChain

/-- 10.34: quotient type of chain integration functionals modulo `BookChain.Equiv`, forming an
abelian group under formal sum `++` and path reversal `BookChain.neg`. -/
abbrev BookChainClass := Quotient BookChain.instSetoid

namespace BookChainClass

def eval (c : BookChainClass) (f : C(ℂ, ℂ)) : ℂ :=
  Quotient.liftOn c (fun Γ => BookChain.integral f Γ)
    (fun Γ₁ Γ₂ h => (BookChain.equiv_iff_forall_continuous Γ₁ Γ₂).mp h f f.continuous)

instance : Zero BookChainClass := ⟨⟦[]⟧⟩

instance : Add BookChainClass :=
  ⟨Quotient.map₂ (· ++ ·) (fun _ _ h₁ _ _ h₂ => BookChain.equiv_append h₁ h₂)⟩

instance : Neg BookChainClass :=
  ⟨Quotient.map BookChain.neg (fun _ _ h => BookChain.equiv_neg_congr h)⟩

theorem eval_injective : Function.Injective eval := by
  intro c₁ c₂ h
  refine Quotient.inductionOn₂ c₁ c₂ (fun Γ₁ Γ₂ => ?_) h
  intro heq
  apply Quotient.sound
  change BookChain.Equiv Γ₁ Γ₂
  rw [BookChain.equiv_iff_forall_continuous]
  intro f hf
  exact congr_fun heq ⟨f, hf⟩

instance : AddCommGroup BookChainClass where
  add_assoc a b c := eval_injective <| Quotient.inductionOn₃ a b c fun Γ₁ Γ₂ Γ₃ => by
    ext f
    change BookChain.integral f ((Γ₁ ++ Γ₂) ++ Γ₃) = BookChain.integral f (Γ₁ ++ (Γ₂ ++ Γ₃))
    simp
  zero_add a := eval_injective <| Quotient.inductionOn a fun Γ => by
    ext f
    change BookChain.integral f ([] ++ Γ) = BookChain.integral f Γ
    simp
  add_zero a := eval_injective <| Quotient.inductionOn a fun Γ => by
    ext f
    change BookChain.integral f (Γ ++ []) = BookChain.integral f Γ
    simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := eval_injective <| Quotient.inductionOn a fun Γ => by
    ext f
    change BookChain.integral f (BookChain.neg Γ ++ Γ) = 0
    rw [BookChain.integral_append, BookChain.integral_neg Γ f.continuous.continuousOn, neg_add_cancel]
  add_comm a b := eval_injective <| Quotient.inductionOn₂ a b fun Γ₁ Γ₂ => by
    ext f
    change BookChain.integral f (Γ₁ ++ Γ₂) = BookChain.integral f (Γ₂ ++ Γ₁)
    simp [add_comm]

end BookChainClass

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

/-! ### 10.37: Index jump across an oriented crosscut (with fidelity disclosure E-10.37)

**Fidelity disclosure (E-10.37, printed p. 221):**
In Rudin *Real and Complex Analysis* (3rd ed., 1987), Theorem 10.37 displays
`Ind_γ(z) = 1 + Ind_γ(w)` while the final clause reads *"if `x ∈ D₊` and `w ∈ D₋`"*.
- `node10_37_literal_conclusion_counterexample` (above) shows the unconstrained-`z` formula fails
  for any index map, and `node10_37_literal_geometric_counterexample` (below) constructs an
  explicit closed path `γ = triangleBoundary (3 * I) (-2) 2` satisfying every geometric hypothesis
  of Theorem 10.37 (`a = 0, r = 1, b = 1, u = 5/4, v = 7/4, D₊, D₋`) together with `x ∈ D₊`,
  `w ∈ D₋`, and `z ∉ γ*` for which `Ind_γ(z) ≠ 1 + Ind_γ(w)`.
- Replacing the printed typo `x ∈ D₊` with the intended hypothesis `z ∈ D₊` gives
  `theorem10_37_corrected` below, proved in full under Rudin's exact crosscut and closure-marker
  hypotheses (`a + i b ∈ closure D₊`, `a - i b ∈ closure D₋`). -/

/-- Helper: `circleArcPath` on `[θ₀, θ₀ + 2π]` integrates to `∮ z in C(a, r), f z`. -/
private theorem pathIntegral_circleArc_two_pi (f : ℂ → ℂ) (a : ℂ) (r θ₀ : ℝ) :
    pathIntegral f (circleArcPath a r (show θ₀ < θ₀ + 2 * Real.pi by linarith [Real.two_pi_pos])).toBookCurve =
      ∮ z in C(a, r), f z := by
  unfold pathIntegral circleIntegral circleArcPath BookPath.ofC1
  dsimp only
  have hper : Function.Periodic (fun t => deriv (circleMap a r) t • f (circleMap a r t)) (2 * Real.pi) :=
    fun t => by
      simp only [deriv_circleMap, periodic_circleMap 0 r t, periodic_circleMap a r t]
  have hshift := hper.intervalIntegral_add_eq θ₀ 0
  rw [zero_add] at hshift
  rw [← hshift]
  apply intervalIntegral.integral_congr_ae_restrict
  change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc θ₀ (θ₀ + 2 * Real.pi))] _
  rw [Set.uIoc_of_le (by linarith [Real.two_pi_pos]), ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), smul_eq_mul, mul_comm]

/-- 10.37 (corrected `z ∈ D₊` form): let `γ` be a closed path on `[α, β]`, `a ∈ ℂ`, `r > 0`,
`α < u < v < β`, and `|b| = r` such that
(a) `γ(u) = a - b` and `γ(v) = a + b`,
(b) `|γ(t) - a| < r` for `u < t < v`,
(c) `|γ(t) - a| > r` for `α ≤ t < u` and for `v < t ≤ β`.
Suppose `D(a; r) \ γ* = D₊ ∪ D₋` where `D₊` and `D₋` are regions with
`a + i b ∈ closure D₊` and `a - i b ∈ closure D₋`.
Then `Ind_γ(z) = 1 + Ind_γ(w)` for every `z ∈ D₊` and `w ∈ D₋`. -/
theorem theorem10_37_corrected (γ : BookPath) (hclosed : γ.IsClosed)
    {a b : ℂ} {r u v : ℝ} (hr : 0 < r) (hb : ‖b‖ = r)
    (hαu : γ.α < u) (huv : u < v) (hvβ : v < γ.β)
    (ha_u : γ.toFun u = a - b) (ha_v : γ.toFun v = a + b)
    (h_in : ∀ t ∈ Ioo u v, γ.toFun t ∈ disc a r)
    (h_out : ∀ t, (t ∈ Ico γ.α u ∨ t ∈ Ioc v γ.β) → r < ‖γ.toFun t - a‖)
    {Dplus Dminus : Set ℂ}
    (hD : disc a r \ γ.trace = Dplus ∪ Dminus)
    (hDplus : IsRegion Dplus) (hDminus : IsRegion Dminus)
    (hplus_marker : a + Complex.I * b ∈ closure Dplus)
    (hminus_marker : a - Complex.I * b ∈ closure Dminus)
    {z w : ℂ} (hz : z ∈ Dplus) (hw : w ∈ Dminus) :
    Ind γ.toBookCurve z = 1 + Ind γ.toBookCurve w := by
  have hb_ne : b ≠ 0 := fun h0 => by rw [h0, norm_zero] at hb; linarith
  have hDplus_sub : Dplus ⊆ disc a r \ γ.trace := hD ▸ subset_union_left
  have hDminus_sub : Dminus ⊆ disc a r \ γ.trace := hD ▸ subset_union_right
  have hz_disc : z ∈ disc a r := (hDplus_sub hz).1
  have hz_not_γ : z ∉ γ.trace := (hDplus_sub hz).2
  have hw_disc : w ∈ disc a r := (hDminus_sub hw).1
  have hw_not_γ : w ∉ γ.trace := (hDminus_sub hw).2
  -- Split `γ` into interior crosscut `γ₁ = γ|[u, v]` (`a - b → a + b`)
  -- and exterior arc `γ₂ = γ|[v, β] · γ|[α, u]` (`a + b → a - b`).
  let γ₁ : BookPath := γ.restrict hαu.le huv hvβ.le
  let γ_vβ : BookPath := γ.restrict (le_trans hαu.le huv.le) hvβ le_rfl
  let γ_αu : BookPath := γ.restrict le_rfl hαu (le_trans huv.le hvβ.le)
  have hjoin_β_α : γ_vβ.toFun γ_vβ.β = γ_αu.toFun γ_αu.α := hclosed.symm
  let γ₂ : BookPath := γ_vβ.concat γ_αu hjoin_β_α
  have hγ₁_start : γ₁.toFun γ₁.α = a - b := ha_u
  have hγ₁_end : γ₁.toFun γ₁.β = a + b := ha_v
  have hγ₂_start : γ₂.toFun γ₂.α = a + b := by
    simp [γ₂, γ_vβ, BookPath.restrict, ha_v]
  have hγ₂_end : γ₂.toFun γ₂.β = a - b := by
    rw [BookPath.concat_end]
    exact ha_u
  have hγ_trace : γ₁.trace ∪ γ₂.trace = γ.trace := by
    rw [show γ₂.trace = γ_vβ.trace ∪ γ_αu.trace from γ_vβ.concat_trace γ_αu hjoin_β_α]
    ext ζ
    simp only [γ₁, γ_vβ, γ_αu, BookPath.trace, BookCurve.trace,
      BookPath.restrict, mem_union, mem_image, mem_Icc]
    constructor
    · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact ⟨t, ⟨le_trans hαu.le ht.1, le_trans ht.2 hvβ.le⟩, rfl⟩
      · exact ⟨t, ⟨le_trans (le_trans hαu.le huv.le) ht.1, ht.2⟩, rfl⟩
      · exact ⟨t, ⟨ht.1, le_trans ht.2 (le_trans huv.le hvβ.le)⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      by_cases htu : t ≤ u
      · exact Or.inr (Or.inr ⟨t, ⟨ht.1, htu⟩, rfl⟩)
      · by_cases htv : t ≤ v
        · exact Or.inl ⟨t, ⟨(not_le.mp htu).le, htv⟩, rfl⟩
        · exact Or.inr (Or.inl ⟨t, ⟨(not_le.mp htv).le, ht.2⟩, rfl⟩)
  have hγ_equiv : BookChain.Equiv [γ] [γ₁, γ₂] := by
    rw [BookChain.equiv_iff_forall_continuous]
    intro f hf
    have hint : ∀ (a' b' : ℝ), γ.α ≤ a' → a' ≤ b' → b' ≤ γ.β →
        IntervalIntegrable (fun t => f (γ.toFun t) * derivWithin γ.toFun (Icc γ.α γ.β) t)
          MeasureTheory.volume a' b' := fun a' b' ha' hab' hb' =>
      (γ.intervalIntegrable_pathIntegral hf.continuousOn).mono_set
        (by rw [Set.uIcc_of_le hab', Set.uIcc_of_le γ.le_endpoints]; exact Icc_subset_Icc ha' hb')
    have hsum1 := intervalIntegral.integral_add_adjacent_intervals
      (hint γ.α u le_rfl hαu.le (le_trans huv.le hvβ.le))
      (hint u γ.β hαu.le (le_trans huv.le hvβ.le) le_rfl)
    have hsum2 := intervalIntegral.integral_add_adjacent_intervals
      (hint u v hαu.le huv.le hvβ.le)
      (hint v γ.β (le_trans hαu.le huv.le) hvβ.le le_rfl)
    have hcat := γ_vβ.pathIntegral_concat γ_αu hjoin_β_α hf.continuousOn
    simp only [BookChain.integral_cons, BookChain.integral_nil, add_zero]
    change pathIntegral f γ.toBookCurve =
      pathIntegral f γ₁.toBookCurve + pathIntegral f (γ_vβ.concat γ_αu hjoin_β_α).toBookCurve
    rw [hcat, γ.pathIntegral_restrict hαu.le huv hvβ.le,
        γ.pathIntegral_restrict (le_trans hαu.le huv.le) hvβ le_rfl,
        γ.pathIntegral_restrict le_rfl hαu (le_trans huv.le hvβ.le)]
    unfold pathIntegral
    rw [← hsum1, ← hsum2]
    ring
  -- Semicircles `C₊` (`[θ₀, θ₀ + π]`, `a + b` via `a + i b` to `a - b`) and
  -- `C₋` (`[θ₀ + π, θ₀ + 2π]`, `a - b` via `a - i b` to `a + b`), where `θ₀ = arg b`.
  let θ₀ : ℝ := Complex.arg b
  have hb_exp : (r : ℂ) * Complex.exp (θ₀ * Complex.I) = b := by
    simpa [θ₀, hb] using Complex.norm_mul_exp_arg_mul_I b
  have hcm_shift : ∀ s : ℝ, circleMap a r (θ₀ + s) = a + b * Complex.exp (s * Complex.I) := by
    intro s
    simp only [circleMap, Complex.ofReal_add, add_mul, Complex.exp_add]
    rw [← mul_assoc, hb_exp]
  let Cplus : BookPath := circleArcPath a r (show θ₀ < θ₀ + Real.pi by linarith [Real.pi_pos])
  let Cminus : BookPath := circleArcPath a r
    (show θ₀ + Real.pi < θ₀ + 2 * Real.pi by linarith [Real.pi_pos])
  have hCplus_start : Cplus.toFun Cplus.α = a + b := by
    change circleMap a r θ₀ = a + b
    simpa using hcm_shift 0
  have hCplus_end : Cplus.toFun Cplus.β = a - b := by
    change circleMap a r (θ₀ + Real.pi) = a - b
    rw [hcm_shift Real.pi, Complex.exp_pi_mul_I]
    ring
  have hCminus_start : Cminus.toFun Cminus.α = a - b := hCplus_end
  have hCminus_end : Cminus.toFun Cminus.β = a + b := by
    change circleMap a r (θ₀ + 2 * Real.pi) = a + b
    have := hcm_shift (2 * Real.pi)
    rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * Real.pi * Complex.I by push_cast; ring,
      Complex.exp_two_pi_mul_I, mul_one] at this
    exact this
  have hCplus_sphere : Cplus.trace ⊆ Metric.sphere a r := by
    rintro _ ⟨t, _, rfl⟩
    exact circleMap_mem_sphere a hr.le t
  have hCminus_sphere : Cminus.trace ⊆ Metric.sphere a r := by
    rintro _ ⟨t, _, rfl⟩
    exact circleMap_mem_sphere a hr.le t
  -- Marker exclusions from `γ₁`, `C₊`, `C₋`
  have hmarker_plus_ne_ends : a + Complex.I * b ≠ a - b ∧ a + Complex.I * b ≠ a + b := by
    constructor <;> intro heq
    · have h1 : (Complex.I + 1) * b = 0 := by linear_combination heq
      have hI1 : (Complex.I + 1 : ℂ) ≠ 0 := by
        intro h0; have := congr_arg Complex.im h0; norm_num at this
      exact hb_ne ((mul_eq_zero.mp h1).resolve_left hI1)
    · have h1 : (Complex.I - 1) * b = 0 := by linear_combination heq
      have hI1 : (Complex.I - 1 : ℂ) ≠ 0 := by
        intro h0; have := congr_arg Complex.im h0; norm_num at this
      exact hb_ne ((mul_eq_zero.mp h1).resolve_left hI1)
  have hmarker_minus_ne_ends : a - Complex.I * b ≠ a - b ∧ a - Complex.I * b ≠ a + b := by
    constructor <;> intro heq
    · have h1 : (1 - Complex.I) * b = 0 := by linear_combination heq
      have hI1 : (1 - Complex.I : ℂ) ≠ 0 := by
        intro h0; have := congr_arg Complex.im h0; norm_num at this
      exact hb_ne ((mul_eq_zero.mp h1).resolve_left hI1)
    · have h1 : (1 + Complex.I) * b = 0 := by linear_combination -heq
      have hI1 : (1 + Complex.I : ℂ) ≠ 0 := by
        intro h0; have := congr_arg Complex.im h0; norm_num at this
      exact hb_ne ((mul_eq_zero.mp h1).resolve_left hI1)
  have hγ₁_ball : γ₁.trace ⊆ Metric.closedBall a r := by
    rintro _ ⟨t, ht, rfl⟩
    change t ∈ Icc u v at ht
    change γ.toFun t ∈ Metric.closedBall a r
    rcases eq_or_lt_of_le ht.1 with rfl | htu
    · rw [ha_u, Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, hb]
    · rcases eq_or_lt_of_le ht.2 with rfl | htv
      · rw [ha_v, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hb]
      · exact Metric.ball_subset_closedBall (h_in t ⟨htu, htv⟩)
  have hplus_not_γ₁ : a + Complex.I * b ∉ γ₁.trace := by
    rintro ⟨t, ht, hval⟩
    change γ.toFun t = a + Complex.I * b at hval
    rcases eq_or_lt_of_le ht.1 with rfl | htu
    · exact hmarker_plus_ne_ends.1 (hval.symm.trans ha_u)
    · rcases eq_or_lt_of_le ht.2 with rfl | htv
      · exact hmarker_plus_ne_ends.2 (hval.symm.trans ha_v)
      · have hin := mem_disc.mp (h_in t ⟨htu, htv⟩)
        rw [hval, add_sub_cancel_left, norm_mul, Complex.norm_I, one_mul, hb] at hin
        exact lt_irrefl r hin
  have hminus_not_γ₁ : a - Complex.I * b ∉ γ₁.trace := by
    rintro ⟨t, ht, hval⟩
    change γ.toFun t = a - Complex.I * b at hval
    rcases eq_or_lt_of_le ht.1 with rfl | htu
    · exact hmarker_minus_ne_ends.1 (hval.symm.trans ha_u)
    · rcases eq_or_lt_of_le ht.2 with rfl | htv
      · exact hmarker_minus_ne_ends.2 (hval.symm.trans ha_v)
      · have hin := mem_disc.mp (h_in t ⟨htu, htv⟩)
        rw [hval, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, one_mul, hb] at hin
        exact lt_irrefl r hin
  have hminus_not_Cplus : a - Complex.I * b ∉ Cplus.trace := by
    rintro ⟨t, ht, hval⟩
    change t ∈ Icc θ₀ (θ₀ + Real.pi) at ht
    change circleMap a r t = a - Complex.I * b at hval
    let s : ℝ := t - θ₀
    have hs : s ∈ Icc 0 Real.pi := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hts : t = θ₀ + s := by ring
    rw [hts, hcm_shift s] at hval
    have hexp : b * (Complex.exp (s * Complex.I) + Complex.I) = 0 := by linear_combination hval
    have hexpI : Complex.exp (s * Complex.I) = -Complex.I :=
      eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hexp).resolve_left hb_ne)
    have him := congr_arg Complex.im hexpI
    have hsin : Real.sin s = -1 := by
      rw [Complex.exp_mul_I] at him
      simpa [Complex.sin_ofReal_re] using him
    linarith [Real.sin_nonneg_of_nonneg_of_le_pi hs.1 hs.2]
  have hplus_not_Cminus : a + Complex.I * b ∉ Cminus.trace := by
    rintro ⟨t, ht, hval⟩
    change t ∈ Icc (θ₀ + Real.pi) (θ₀ + 2 * Real.pi) at ht
    change circleMap a r t = a + Complex.I * b at hval
    let s : ℝ := t - (θ₀ + Real.pi)
    have hs : s ∈ Icc 0 Real.pi := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hts : t = θ₀ + (Real.pi + s) := by ring
    rw [hts, hcm_shift (Real.pi + s), Complex.ofReal_add, add_mul, Complex.exp_add,
      Complex.exp_pi_mul_I] at hval
    have hexp : b * (Complex.exp (s * Complex.I) + Complex.I) = 0 := by linear_combination -hval
    have hexpI : Complex.exp (s * Complex.I) = -Complex.I :=
      eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hexp).resolve_left hb_ne)
    have him := congr_arg Complex.im hexpI
    have hsin : Real.sin s = -1 := by
      rw [Complex.exp_mul_I] at him
      simpa [Complex.sin_ofReal_re] using him
    linarith [Real.sin_nonneg_of_nonneg_of_le_pi hs.1 hs.2]
  -- `γ₂.trace` is disjoint from `disc a r`
  have hγ₂_disj_disc : Disjoint γ₂.trace (disc a r) := by
    rw [Set.disjoint_left]
    intro ζ hζ hζ_disc
    rw [mem_disc] at hζ_disc
    have htr_γ₂ : γ₂.trace = γ_vβ.trace ∪ γ_αu.trace := γ_vβ.concat_trace γ_αu hjoin_β_α
    rw [htr_γ₂] at hζ
    rcases hζ with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · change t ∈ Icc v γ.β at ht
      change ‖γ.toFun t - a‖ < r at hζ_disc
      rcases eq_or_lt_of_le ht.1 with rfl | hvt
      · rw [ha_v, add_sub_cancel_left, hb] at hζ_disc; exact lt_irrefl r hζ_disc
      · exact not_lt.mpr (h_out t (Or.inr ⟨hvt, ht.2⟩)).le hζ_disc
    · change t ∈ Icc γ.α u at ht
      change ‖γ.toFun t - a‖ < r at hζ_disc
      rcases eq_or_lt_of_le ht.2 with rfl | htu
      · rw [ha_u, sub_sub_cancel_left, norm_neg, hb] at hζ_disc; exact lt_irrefl r hζ_disc
      · exact not_lt.mpr (h_out t (Or.inl ⟨ht.1, htu⟩)).le hζ_disc
  -- Construct the three auxiliary closed paths `σ₁`, `σ₂`, `τ` and full circle `Cfull`
  have hjoin_σ₁ : γ₁.toFun γ₁.β = Cplus.toFun Cplus.α := hγ₁_end.trans hCplus_start.symm
  let σ₁ : BookPath := γ₁.concat Cplus hjoin_σ₁
  have hσ₁_closed : σ₁.IsClosed := by
    change σ₁.toFun σ₁.α = σ₁.toFun σ₁.β
    rw [BookPath.concat_start, BookPath.concat_end, hγ₁_start, hCplus_end]
  have hjoin_σ₂ : γ₁.toFun γ₁.β = Cminus.reverse.toFun Cminus.reverse.α := by
    rw [BookPath.reverse_start, hγ₁_end, hCminus_end]
  let σ₂ : BookPath := γ₁.concat Cminus.reverse hjoin_σ₂
  have hσ₂_closed : σ₂.IsClosed := by
    change σ₂.toFun σ₂.α = σ₂.toFun σ₂.β
    rw [BookPath.concat_start, BookPath.concat_end, BookPath.reverse_end, hγ₁_start, hCminus_start]
  have hjoin_τ : γ₂.toFun γ₂.β = Cminus.toFun Cminus.α := hγ₂_end.trans hCminus_start.symm
  let τ : BookPath := γ₂.concat Cminus hjoin_τ
  have hτ_closed : τ.IsClosed := by
    change τ.toFun τ.α = τ.toFun τ.β
    rw [BookPath.concat_start, BookPath.concat_end, hγ₂_start, hCminus_end]
  -- Helper: any closed path `σ ⊆ closedBall a r` avoiding a boundary point `p = a + c` (`‖c‖ = r`)
  -- with `p ∈ closure D` (`D` region `⊆ (σ*)ᶜ`) has `Ind σ = 0` on `D`.
  have hInd_zero_via_boundary : ∀ (σ : BookPath) (c : ℂ) (D : Set ℂ),
      σ.IsClosed → σ.trace ⊆ Metric.closedBall a r →
      ‖c‖ = r → a + c ∉ σ.trace → IsRegion D → D ⊆ (σ.trace)ᶜ →
      a + c ∈ closure D → ∀ q ∈ D, Ind σ.toBookCurve q = 0 := by
    intro σ c D hσ_cl hσ_ball hc_norm hp_not hD_reg hD_sub hp_cl q hq
    have hopen : IsOpen (σ.trace)ᶜ := σ.isCompact_trace.isClosed.isOpen_compl
    obtain ⟨δ, hδpos, hball_sub⟩ := Metric.isOpen_iff.mp hopen (a + c) hp_not
    obtain ⟨q₀, hq₀_D, hq₀_ball⟩ := Metric.mem_closure_iff.mp hp_cl δ hδpos
    let p_ext : ℂ := a + (1 + δ / (2 * r) : ℝ) • c
    have hp_ext_ball : p_ext ∈ Metric.ball (a + c) δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hdiff : p_ext - (a + c) = (δ / (2 * r) : ℝ) • c := by
        simp only [p_ext, add_smul, one_smul]
        abel
      rw [hdiff, norm_smul, Real.norm_of_nonneg (by positivity), hc_norm]
      have : δ / (2 * r) * r = δ / 2 := by field_simp
      linarith
    have hp_ext_out : p_ext ∈ (Metric.closedBall a r)ᶜ := by
      rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_eq_norm]
      simp only [p_ext, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (by positivity : 0 ≤ 1 + δ / (2 * r)), hc_norm]
      have : (1 + δ / (2 * r)) * r = r + δ / 2 := by field_simp
      linarith
    have hext_sub : (Metric.closedBall a r)ᶜ ⊆ (σ.trace)ᶜ := compl_subset_compl.mpr hσ_ball
    have hB_pre : IsPreconnected (Metric.ball (a + c) δ) := (convex_ball (a + c) δ).isPreconnected
    have hDB_pre : IsPreconnected (D ∪ Metric.ball (a + c) δ) :=
      hD_reg.2.2.union q₀ hq₀_D (by rw [Metric.mem_ball, dist_comm]; exact hq₀_ball) hB_pre
    have hAll_pre : IsPreconnected ((D ∪ Metric.ball (a + c) δ) ∪ (Metric.closedBall a r)ᶜ) :=
      hDB_pre.union p_ext (Or.inr hp_ext_ball) hp_ext_out (isConnected_compl_closedBall a hr.le).2
    have hAll_sub : (D ∪ Metric.ball (a + c) δ) ∪ (Metric.closedBall a r)ᶜ ⊆ (σ.trace)ᶜ :=
      union_subset (union_subset hD_sub hball_sub) hext_sub
    let U := bookComponent (σ.trace)ᶜ p_ext
    have hU_mem : U ∈ bookComponents (σ.trace)ᶜ := ⟨p_ext, hext_sub hp_ext_out, rfl⟩
    have hAll_U : (D ∪ Metric.ball (a + c) δ) ∪ (Metric.closedBall a r)ᶜ ⊆ U :=
      bookComponent_maximal hAll_sub ((bookConnected_iff_isPreconnected _).mpr hAll_pre)
        (Or.inr hp_ext_out)
    have hU_unbdd : ¬ Bornology.IsBounded U := by
      intro hbdd
      obtain ⟨B, _, hB⟩ := hbdd.subset_closedBall_lt 0 a
      let w_far : ℂ := a + ((max r B + 1 : ℝ) : ℂ)
      have hp_pos : 0 < max r B + 1 := lt_of_lt_of_le hr (le_trans (le_max_left r B) (by linarith))
      have hw_out : w_far ∈ (Metric.closedBall a r)ᶜ := by
        rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_eq_norm]
        simp only [w_far, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp_pos]
        exact lt_of_le_of_lt (le_max_left r B) (by linarith)
      have hwB := hB (hAll_U (Or.inr hw_out))
      rw [Metric.mem_closedBall, dist_eq_norm] at hwB
      simp only [w_far, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp_pos] at hwB
      linarith [le_max_right r B]
    exact Ind_eq_zero_of_mem_unbounded_component σ hσ_cl hU_mem hU_unbdd
      (hAll_U (Or.inl (Or.inl hq)))
  -- Step 1: `Ind σ₁ w = 0`
  have hInd_σ₁_w : Ind σ₁.toBookCurve w = 0 := by
    have hσ₁_tr : σ₁.trace = γ₁.trace ∪ Cplus.trace := γ₁.concat_trace Cplus hjoin_σ₁
    refine hInd_zero_via_boundary σ₁ (-Complex.I * b) Dminus hσ₁_closed ?_ ?_ ?_ hDminus ?_ ?_ w hw
    · rw [hσ₁_tr]
      exact union_subset hγ₁_ball (hCplus_sphere.trans Metric.sphere_subset_closedBall)
    · simp [hb]
    · rw [show a + -Complex.I * b = a - Complex.I * b by ring, hσ₁_tr]
      exact fun h => h.elim hminus_not_γ₁ hminus_not_Cplus
    · intro ζ hζ
      rw [hσ₁_tr]
      rintro (h1 | h2)
      · exact (hDminus_sub hζ).2 (hγ_trace ▸ Or.inl h1)
      · have hsp : dist ζ a = r := hCplus_sphere h2
        have hbl : dist ζ a < r := (hDminus_sub hζ).1
        linarith
    · simpa [sub_eq_add_neg] using hminus_marker
  -- Step 2: `Ind σ₂ z = 0`
  have hInd_σ₂_z : Ind σ₂.toBookCurve z = 0 := by
    have hσ₂_tr : σ₂.trace = γ₁.trace ∪ Cminus.trace := by
      simp [σ₂, γ₁.concat_trace Cminus.reverse hjoin_σ₂]
    refine hInd_zero_via_boundary σ₂ (Complex.I * b) Dplus hσ₂_closed ?_ ?_ ?_ hDplus ?_ hplus_marker z hz
    · rw [hσ₂_tr]
      exact union_subset hγ₁_ball (hCminus_sphere.trans Metric.sphere_subset_closedBall)
    · simp [hb]
    · rw [hσ₂_tr]
      exact fun h => h.elim hplus_not_γ₁ hplus_not_Cminus
    · intro ζ hζ
      rw [hσ₂_tr]
      rintro (h1 | h2)
      · exact (hDplus_sub hζ).2 (hγ_trace ▸ Or.inl h1)
      · have hsp : dist ζ a = r := hCminus_sphere h2
        have hbl : dist ζ a < r := (hDplus_sub hζ).1
        linarith
  -- Step 3: `Ind τ z = Ind τ w` since `disc a r ⊆ (τ*)ᶜ` is convex/preconnected
  have hdisc_sub_τ : disc a r ⊆ (τ.trace)ᶜ := by
    intro ζ hζ hτ_mem
    rw [show τ.trace = γ₂.trace ∪ Cminus.trace from γ₂.concat_trace Cminus hjoin_τ] at hτ_mem
    rcases hτ_mem with h1 | h2
    · exact Set.disjoint_left.mp hγ₂_disj_disc h1 hζ
    · have hsp : dist ζ a = r := hCminus_sphere h2
      have hbl : dist ζ a < r := hζ
      linarith
  have hInd_τ_eq : Ind τ.toBookCurve z = Ind τ.toBookCurve w :=
    Ind_eq_of_isPreconnected_compl τ hτ_closed (disc_isRegion a hr).2.2 hdisc_sub_τ hz_disc hw_disc
  -- Step 4: Chain index identities at `z` and `w`
  have hz_not_sphere : z ∉ Metric.sphere a r := fun hsp => by
    have h1 : dist z a = r := hsp
    have h2 : dist z a < r := hz_disc
    linarith
  have hw_not_sphere : w ∉ Metric.sphere a r := fun hsp => by
    have h1 : dist w a = r := hsp
    have h2 : dist w a < r := hw_disc
    linarith
  have hfz_γ : ContinuousOn (fun ζ : ℂ => (ζ - z)⁻¹) γ.trace :=
    (continuous_id.sub continuous_const).continuousOn.inv₀ fun ζ hζ h0 =>
      hz_not_γ (sub_eq_zero.mp (by simpa using h0) ▸ hζ)
  have hfz_Cminus : ContinuousOn (fun ζ : ℂ => (ζ - z)⁻¹) Cminus.trace :=
    (continuous_id.sub continuous_const).continuousOn.inv₀ fun ζ hζ h0 =>
      hz_not_sphere (sub_eq_zero.mp (by simpa using h0) ▸ hCminus_sphere hζ)
  have hfz_σ₂ : ContinuousOn (fun ζ : ℂ => (ζ - z)⁻¹) σ₂.trace := by
    rw [γ₁.concat_trace Cminus.reverse hjoin_σ₂, BookPath.reverse_trace]
    exact (hfz_γ.mono (hγ_trace ▸ subset_union_left)).union_of_isClosed hfz_Cminus
      γ₁.isCompact_trace.isClosed Cminus.isCompact_trace.isClosed
  have hfz_τ : ContinuousOn (fun ζ : ℂ => (ζ - z)⁻¹) τ.trace := by
    rw [γ₂.concat_trace Cminus hjoin_τ]
    exact (hfz_γ.mono (hγ_trace ▸ subset_union_right)).union_of_isClosed hfz_Cminus
      γ₂.isCompact_trace.isClosed Cminus.isCompact_trace.isClosed
  have hint_z : pathIntegral (fun ζ => (ζ - z)⁻¹) γ.toBookCurve =
      pathIntegral (fun ζ => (ζ - z)⁻¹) σ₂.toBookCurve +
      pathIntegral (fun ζ => (ζ - z)⁻¹) τ.toBookCurve := by
    have heq_γ := hγ_equiv (fun ζ => (ζ - z)⁻¹)
      (by rw [BookChain.trace_singleton, BookChain.trace_cons, BookChain.trace_singleton,
            hγ_trace, union_self]; exact hfz_γ)
    simp only [BookChain.integral_cons, BookChain.integral_nil, add_zero] at heq_γ
    rw [heq_γ, γ₁.pathIntegral_concat Cminus.reverse hjoin_σ₂ hfz_σ₂,
      Cminus.pathIntegral_reverse hfz_Cminus,
      γ₂.pathIntegral_concat Cminus hjoin_τ hfz_τ]
    ring
  have hInd_γ_z : Ind γ.toBookCurve z = Ind τ.toBookCurve z := by
    unfold Ind at hInd_σ₂_z ⊢
    rw [hint_z, mul_add, hInd_σ₂_z, zero_add]
  -- Now at `w`: `∫_{σ₁} + ∫_τ = ∫_γ + ∮_{C(a,r)} = ∫_γ + 2πi`
  have hfw_γ : ContinuousOn (fun ζ : ℂ => (ζ - w)⁻¹) γ.trace :=
    (continuous_id.sub continuous_const).continuousOn.inv₀ fun ζ hζ h0 =>
      hw_not_γ (sub_eq_zero.mp (by simpa using h0) ▸ hζ)
  have hfw_sphere : ContinuousOn (fun ζ : ℂ => (ζ - w)⁻¹) (Metric.sphere a r) :=
    (continuous_id.sub continuous_const).continuousOn.inv₀ fun ζ hζ h0 =>
      hw_not_sphere (sub_eq_zero.mp (by simpa using h0) ▸ hζ)
  have hfw_σ₁ : ContinuousOn (fun ζ : ℂ => (ζ - w)⁻¹) σ₁.trace := by
    rw [γ₁.concat_trace Cplus hjoin_σ₁]
    exact (hfw_γ.mono (hγ_trace ▸ subset_union_left)).union_of_isClosed
      (hfw_sphere.mono hCplus_sphere)
      γ₁.isCompact_trace.isClosed Cplus.isCompact_trace.isClosed
  have hfw_τ : ContinuousOn (fun ζ : ℂ => (ζ - w)⁻¹) τ.trace := by
    rw [γ₂.concat_trace Cminus hjoin_τ]
    exact (hfw_γ.mono (hγ_trace ▸ subset_union_right)).union_of_isClosed
      (hfw_sphere.mono hCminus_sphere)
      γ₂.isCompact_trace.isClosed Cminus.isCompact_trace.isClosed
  have hCplus_Cminus_sum :
      pathIntegral (fun ζ => (ζ - w)⁻¹) Cplus.toBookCurve +
      pathIntegral (fun ζ => (ζ - w)⁻¹) Cminus.toBookCurve = 2 * Real.pi * Complex.I := by
    let g : ℝ → ℂ := fun t => (circleMap a r t - w)⁻¹ * deriv (circleMap a r) t
    have hderiv_cont : Continuous (deriv (circleMap a r)) := by
      have : deriv (circleMap a r) = fun t => circleMap 0 r t * Complex.I :=
        funext (deriv_circleMap a r)
      rw [this]
      exact (continuous_circleMap 0 r).mul continuous_const
    have hg_cont' : Continuous g := by
      refine (Continuous.inv₀ ((continuous_circleMap a r).sub continuous_const) ?_).mul hderiv_cont
      intro t h0
      exact hw_not_sphere (sub_eq_zero.mp (by simpa using h0) ▸ circleMap_mem_sphere a hr.le t)
    have harc_eq : ∀ (α' β' : ℝ) (hαβ : α' < β'),
        pathIntegral (fun ζ => (ζ - w)⁻¹) (circleArcPath a r hαβ).toBookCurve =
          ∫ t in α'..β', g t := by
      intro α' β' hαβ
      unfold pathIntegral circleArcPath BookPath.ofC1
      dsimp only
      apply intervalIntegral.integral_congr_ae_restrict
      change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc α' β')] _
      rw [Set.uIoc_of_le hαβ.le, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    rw [show Cplus = circleArcPath a r (show θ₀ < θ₀ + Real.pi by linarith [Real.pi_pos]) from rfl,
        show Cminus = circleArcPath a r (show θ₀ + Real.pi < θ₀ + 2 * Real.pi by linarith [Real.pi_pos]) from rfl,
        harc_eq θ₀ (θ₀ + Real.pi) _,
        harc_eq (θ₀ + Real.pi) (θ₀ + 2 * Real.pi) _,
        intervalIntegral.integral_add_adjacent_intervals
          (hg_cont'.intervalIntegrable _ _) (hg_cont'.intervalIntegrable _ _),
        ← harc_eq θ₀ (θ₀ + 2 * Real.pi) (by linarith [Real.two_pi_pos]),
        pathIntegral_circleArc_two_pi,
        circleIntegral.integral_sub_inv_of_mem_ball hw_disc]
  have hint_w : pathIntegral (fun ζ => (ζ - w)⁻¹) σ₁.toBookCurve +
      pathIntegral (fun ζ => (ζ - w)⁻¹) τ.toBookCurve =
      pathIntegral (fun ζ => (ζ - w)⁻¹) γ.toBookCurve + 2 * Real.pi * Complex.I := by
    have heq_γ := hγ_equiv (fun ζ => (ζ - w)⁻¹)
      (by rw [BookChain.trace_singleton, BookChain.trace_cons, BookChain.trace_singleton,
            hγ_trace, union_self]; exact hfw_γ)
    simp only [BookChain.integral_cons, BookChain.integral_nil, add_zero] at heq_γ
    rw [γ₁.pathIntegral_concat Cplus hjoin_σ₁ hfw_σ₁,
      γ₂.pathIntegral_concat Cminus hjoin_τ hfw_τ, heq_γ]
    linear_combination hCplus_Cminus_sum
  have hInd_τ_w : Ind τ.toBookCurve w = 1 + Ind γ.toBookCurve w := by
    have hmul := congr_arg ((2 * Real.pi * Complex.I)⁻¹ * ·) hint_w
    rw [mul_add, mul_add, inv_mul_cancel₀ two_pi_I_ne_zero] at hmul
    change Ind σ₁.toBookCurve w + Ind τ.toBookCurve w = Ind γ.toBookCurve w + 1 at hmul
    rw [hInd_σ₁_w, zero_add, add_comm] at hmul
    exact hmul
  rw [hInd_γ_z, hInd_τ_eq, hInd_τ_w]

/-- Corollary of 10.37: under the hypotheses of Theorem 10.37, `D₊` and `D₋` are automatically disjoint. -/
theorem theorem10_37_regions_disjoint (γ : BookPath) (hclosed : γ.IsClosed)
    {a b : ℂ} {r u v : ℝ} (hr : 0 < r) (hb : ‖b‖ = r)
    (hαu : γ.α < u) (huv : u < v) (hvβ : v < γ.β)
    (ha_u : γ.toFun u = a - b) (ha_v : γ.toFun v = a + b)
    (h_in : ∀ t ∈ Ioo u v, γ.toFun t ∈ disc a r)
    (h_out : ∀ t, (t ∈ Ico γ.α u ∨ t ∈ Ioc v γ.β) → r < ‖γ.toFun t - a‖)
    {Dplus Dminus : Set ℂ}
    (hD : disc a r \ γ.trace = Dplus ∪ Dminus)
    (hDplus : IsRegion Dplus) (hDminus : IsRegion Dminus)
    (hplus_marker : a + Complex.I * b ∈ closure Dplus)
    (hminus_marker : a - Complex.I * b ∈ closure Dminus) :
    Disjoint Dplus Dminus := by
  rw [Set.disjoint_left]
  intro z hz_plus hz_minus
  have hjump := theorem10_37_corrected γ hclosed hr hb hαu huv hvβ ha_u ha_v h_in h_out
    hD hDplus hDminus hplus_marker hminus_marker hz_plus hz_minus
  have hzero : (0 : ℂ) = 1 := add_right_cancel (by simpa only [zero_add] using hjump)
  exact zero_ne_one hzero

/-- 10.37 (geometric counterexample to the literal printed wording): there exists an explicit
closed path `γ = triangleBoundary (3 * I) (-2) 2` satisfying ALL geometric hypotheses of
Theorem 10.37 (`a = 0`, `r = 1`, `b = 1`, `u = 5/4`, `v = 7/4`, regions `D₊` and `D₋` with
`a + i b ∈ closure D₊` and `a - i b ∈ closure D₋`) together with `x ∈ D₊`, `w ∈ D₋`, and
`z ∉ γ*` for which `Ind_γ(z) ≠ 1 + Ind_γ(w)`. -/
theorem node10_37_literal_geometric_counterexample :
    ∃ (γ : BookPath) (a b : ℂ) (r u v : ℝ) (Dplus Dminus : Set ℂ),
      γ.IsClosed ∧ 0 < r ∧ ‖b‖ = r ∧
      γ.α < u ∧ u < v ∧ v < γ.β ∧
      γ.toFun u = a - b ∧ γ.toFun v = a + b ∧
      (∀ t ∈ Ioo u v, γ.toFun t ∈ disc a r) ∧
      (∀ t, (t ∈ Ico γ.α u ∨ t ∈ Ioc v γ.β) → r < ‖γ.toFun t - a‖) ∧
      disc a r \ γ.trace = Dplus ∪ Dminus ∧
      IsRegion Dplus ∧ IsRegion Dminus ∧
      a + Complex.I * b ∈ closure Dplus ∧
      a - Complex.I * b ∈ closure Dminus ∧
      ∃ x ∈ Dplus, ∃ w ∈ Dminus, ∃ z ∉ γ.trace,
        Ind γ.toBookCurve z ≠ 1 + Ind γ.toBookCurve w := by
  let γ : BookPath := triangleBoundary (3 * Complex.I) (-2) 2
  let Dplus : Set ℂ := {ζ ∈ disc 0 1 | 0 < ζ.im}
  let Dminus : Set ℂ := {ζ ∈ disc 0 1 | ζ.im < 0}
  have hα : γ.α = 0 := rfl
  have hβ : γ.β = 3 := by
    change (1 : ℝ) + ((1 + (1 - 0)) - 0) = 3
    norm_num
  have hγ_eval : ∀ t : ℝ, γ.toFun t =
      if t ≤ 1 then (1 - t : ℝ) • (3 * Complex.I) + t • (-2 : ℂ)
      else if t ≤ 2 then ((4 * t - 6 : ℝ) : ℂ)
      else (1 - (t - 2) : ℝ) • (2 : ℂ) + (t - 2 : ℝ) • (3 * Complex.I) := by
    intro t
    dsimp [γ, triangleBoundary, BookPath.concat, BookPath.glue, orientedSegment, BookPath.ofC1]
    by_cases h1 : t ≤ 1
    · simp only [h1, ↓reduceIte]
    · by_cases h2 : t ≤ 2
      · have hle : t - 1 + 0 ≤ 1 := by linarith
        simp only [h1, h2, hle, ↓reduceIte]
        push_cast; ring
      · have hnle : ¬ (t - 1 + 0 ≤ 1) := by linarith
        simp only [h1, h2, hnle, ↓reduceIte]
        push_cast; ring
  have hnorm_seg1 : ∀ t : ℝ, 1 < ‖(1 - t : ℝ) • (3 * Complex.I) + t • (-2 : ℂ)‖ := by
    intro t
    have hsq : 1 < Complex.normSq ((1 - t : ℝ) • (3 * Complex.I) + t • (-2 : ℂ)) := by
      have hz_eq : (1 - t : ℝ) • (3 * Complex.I) + t • (-2 : ℂ) =
          ((-2 * t : ℝ) : ℂ) + ((3 * (1 - t) : ℝ) : ℂ) * Complex.I := by
        simp [Complex.real_smul]; ring
      rw [hz_eq, Complex.normSq_add_mul_I]
      nlinarith [sq_nonneg (13 * t - 9)]
    rw [Complex.normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg ((1 - t : ℝ) • (3 * Complex.I) + t • (-2 : ℂ))]
  have hnorm_seg3 : ∀ s : ℝ, 1 < ‖(1 - s : ℝ) • (2 : ℂ) + s • (3 * Complex.I)‖ := by
    intro s
    have hsq : 1 < Complex.normSq ((1 - s : ℝ) • (2 : ℂ) + s • (3 * Complex.I)) := by
      have hz_eq : (1 - s : ℝ) • (2 : ℂ) + s • (3 * Complex.I) =
          ((2 * (1 - s) : ℝ) : ℂ) + ((3 * s : ℝ) : ℂ) * Complex.I := by
        simp [Complex.real_smul]; ring
      rw [hz_eq, Complex.normSq_add_mul_I]
      nlinarith [sq_nonneg (13 * s - 4)]
    rw [Complex.normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg ((1 - s : ℝ) • (2 : ℂ) + s • (3 * Complex.I))]
  have hDplus_reg : IsRegion Dplus := by
    refine ⟨Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im), ?_⟩
    refine ⟨⟨Complex.I / 2, ?_, ?_⟩, ?_⟩
    · simp [disc, Metric.mem_ball]; norm_num
    · simp
    · exact ((convex_ball (0 : ℂ) 1).inter
        (convex_halfSpace_gt (Complex.imLm.isLinear) 0)).isPreconnected
  have hDminus_reg : IsRegion Dminus := by
    refine ⟨Metric.isOpen_ball.inter (isOpen_lt Complex.continuous_im continuous_const), ?_⟩
    refine ⟨⟨-Complex.I / 2, ?_, ?_⟩, ?_⟩
    · simp [disc, Metric.mem_ball]; norm_num
    · simp; norm_num
    · exact ((convex_ball (0 : ℂ) 1).inter
        (convex_halfSpace_lt (Complex.imLm.isLinear) 0)).isPreconnected
  refine ⟨γ, 0, 1, 1, 5 / 4, 7 / 4, Dplus, Dminus,
    triangleBoundary_isClosed _ _ _, zero_lt_one, norm_one,
    by rw [hα]; norm_num, by norm_num, by rw [hβ]; norm_num,
    by rw [hγ_eval]; norm_num,
    by rw [hγ_eval]; norm_num,
    ?_, ?_, ?_, hDplus_reg, hDminus_reg, ?_, ?_, ?_⟩
  · intro t ht
    rw [mem_disc, sub_zero, hγ_eval t]
    have h1 : ¬ t ≤ 1 := by linarith [ht.1]
    have h2 : t ≤ 2 := by linarith [ht.2]
    simp only [h1, h2, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro t ht
    rw [sub_zero, hγ_eval t]
    rcases ht with ⟨_, htu⟩ | ⟨hvt, _⟩
    · split_ifs with h1 h2
      · exact hnorm_seg1 t
      · rw [Complex.norm_real, Real.norm_eq_abs]
        have : 4 * t - 6 < -1 := by linarith
        rw [abs_of_neg (by linarith)]
        linarith
      · linarith
    · split_ifs with h1 h2
      · linarith
      · rw [Complex.norm_real, Real.norm_eq_abs]
        have : 1 < 4 * t - 6 := by linarith
        rw [abs_of_pos (by linarith)]
        linarith
      · exact hnorm_seg3 (t - 2)
  · ext ζ
    simp only [Set.mem_sdiff, mem_union, Dplus, Dminus, mem_ofPred]
    constructor
    · rintro ⟨hζ_disc, hζ_not⟩
      have him_ne : ζ.im ≠ 0 := by
        intro him0
        apply hζ_not
        rw [triangleBoundary_trace]
        right; left
        have hre_lt : |ζ.re| < 1 := by
          have h1 : ‖ζ‖ < 1 := by simpa [disc] using hζ_disc
          have hζ_eq : ζ = (ζ.re : ℂ) := Complex.ext rfl (by simp [him0])
          rwa [hζ_eq, Complex.norm_real, Real.norm_eq_abs] at h1
        rw [abs_lt] at hre_lt
        refine ⟨(2 - ζ.re) / 4, (2 + ζ.re) / 4, by linarith, by linarith, by ring, ?_⟩
        apply Complex.ext
        · simp; ring
        · simp [him0]
      rcases lt_or_gt_of_ne him_ne with hneg | hpos
      · exact Or.inr ⟨hζ_disc, hneg⟩
      · exact Or.inl ⟨hζ_disc, hpos⟩
    · have htr_sub : ∀ ζ ∈ Dplus ∪ Dminus, ζ ∉ γ.trace := by
        rintro ζ (⟨hζ_disc, hpos⟩ | ⟨hζ_disc, hneg⟩) ⟨t, ht, rfl⟩
        · have hnorm_lt : ‖γ.toFun t‖ < 1 := by simpa [disc] using hζ_disc
          have him_pos : 0 < (γ.toFun t).im := hpos
          rw [hγ_eval t] at hnorm_lt him_pos
          split_ifs at hnorm_lt him_pos with h1 h2
          · linarith [hnorm_seg1 t]
          · simp at him_pos
          · linarith [hnorm_seg3 (t - 2)]
        · have hnorm_lt : ‖γ.toFun t‖ < 1 := by simpa [disc] using hζ_disc
          have him_neg : (γ.toFun t).im < 0 := hneg
          rw [hγ_eval t] at hnorm_lt him_neg
          split_ifs at hnorm_lt him_neg with h1 h2
          · linarith [hnorm_seg1 t]
          · simp at him_neg
          · linarith [hnorm_seg3 (t - 2)]
      intro hmem
      rcases hmem with h | h
      · exact ⟨h.1, htr_sub ζ (Or.inl h)⟩
      · exact ⟨h.1, htr_sub ζ (Or.inr h)⟩
  · -- `0 + I * 1 = I ∈ closure Dplus`
    rw [Metric.mem_closure_iff]
    intro ε hε
    let r₀ : ℝ := max (1 / 2) (1 - ε / 2)
    have hr₀_pos : 0 < r₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hr₀_lt : r₀ < 1 := max_lt (by norm_num) (by linarith)
    refine ⟨(r₀ : ℂ) * Complex.I, ⟨?_, ?_⟩, ?_⟩
    · simp [disc, Metric.mem_ball, abs_of_pos hr₀_pos, hr₀_lt]
    · simp [hr₀_pos]
    · simp only [zero_add, mul_one, dist_eq_norm]
      have : Complex.I - (r₀ : ℂ) * Complex.I = ((1 - r₀ : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith [le_max_right (1 / 2) (1 - ε / 2)]
  · -- `0 - I * 1 = -I ∈ closure Dminus`
    rw [Metric.mem_closure_iff]
    intro ε hε
    let r₀ : ℝ := max (1 / 2) (1 - ε / 2)
    have hr₀_pos : 0 < r₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hr₀_lt : r₀ < 1 := max_lt (by norm_num) (by linarith)
    refine ⟨-(r₀ : ℂ) * Complex.I, ⟨?_, ?_⟩, ?_⟩
    · simp [disc, Metric.mem_ball, abs_of_pos hr₀_pos, hr₀_lt]
    · simp [hr₀_pos]
    · simp only [zero_sub, mul_one, dist_eq_norm]
      have : -Complex.I - -(r₀ : ℂ) * Complex.I = -(((1 - r₀ : ℝ) : ℂ) * Complex.I) := by push_cast; ring
      rw [this, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith [le_max_right (1 / 2) (1 - ε / 2)]
  · -- Choose `x = I / 2 ∈ Dplus`, `w = -I / 2 ∈ Dminus`, `z = -I / 2 ∉ γ.trace`
    have hx : Complex.I / 2 ∈ Dplus := by
      refine ⟨?_, by simp⟩
      simp [disc, Metric.mem_ball]; norm_num
    have hw : -Complex.I / 2 ∈ Dminus := by
      refine ⟨?_, by simp; norm_num⟩
      simp [disc, Metric.mem_ball]; norm_num
    have hw_not : -Complex.I / 2 ∉ γ.trace := by
      rintro ⟨t, _, hval⟩
      have hnorm : ‖γ.toFun t‖ = 1 / 2 := by rw [hval]; simp
      have him : (γ.toFun t).im = -1 / 2 := by rw [hval]; simp
      rw [hγ_eval t] at hnorm him
      split_ifs at hnorm him with h1 h2
      · linarith [hnorm_seg1 t]
      · simp at him; norm_num at him
      · linarith [hnorm_seg3 (t - 2)]
    refine ⟨Complex.I / 2, hx, -Complex.I / 2, hw, -Complex.I / 2, hw_not, ?_⟩
    intro heq
    have hzero : (0 : ℂ) = 1 := add_right_cancel (by simpa only [zero_add] using heq)
    exact zero_ne_one hzero

/-! ### 10.12–10.15 & 10.17: Holomorphic primitives, Cauchy's theorem & formula on convex sets, and Morera's theorem -/

private theorem add_piece_telescope (g : ℝ → ℂ) :
    ∀ {n : ℕ} (s : Fin (n + 1) → ℝ) (I_piece : Fin n → ℂ),
    (∀ i : Fin n, g (s i.succ) - g (s i.castSucc) = I_piece i) →
    g (s (Fin.last n)) - g (s 0) = ∑ i : Fin n, I_piece i
  | 0, _, _, _ => by simp
  | n + 1, s, I_piece, hstep => by
    have hind := add_piece_telescope g (fun j : Fin (n + 1) => s j.castSucc)
      (fun j : Fin n => I_piece j.castSucc) (fun j => by
        have h := hstep j.castSucc
        rwa [show j.castSucc.succ = j.succ.castSucc from Fin.ext (by simp)] at h)
    have hlast := hstep (Fin.last n)
    rw [Fin.sum_univ_castSucc]
    change g (s (Fin.last n).succ) - g (s 0) = _
    simp only [Fin.castSucc_zero] at hind
    rw [← hind, ← hlast]
    ring

/-- Fundamental theorem of calculus for piecewise `C¹` paths along a set `S ⊆ ℂ` on which `F` has
complex within-derivative `f` (`ContinuousOn f S`). -/
theorem pathIntegral_eq_sub_of_hasDerivWithinAt {S : Set ℂ} {F f : ℂ → ℂ}
    (hf_cont : ContinuousOn f S)
    (hF_deriv : ∀ z ∈ S, HasDerivWithinAt F (f z) S z)
    (γ : BookPath) (hγ : γ.trace ⊆ S) :
    pathIntegral f γ.toBookCurve = F (γ.toFun γ.β) - F (γ.toFun γ.α) := by
  obtain ⟨n, s, d, hs, hs0, hsn, hdcont, hd⟩ := γ.piecewiseC1
  have hF_cont : ContinuousOn F S := fun z hz => (hF_deriv z hz).continuousWithinAt
  have hf_γ : ContinuousOn f γ.trace := hf_cont.mono hγ
  let I_piece : Fin n → ℂ := fun i =>
    ∫ t in s i.castSucc..s i.succ, f (γ.toFun t) * d i t
  have hstep : ∀ i : Fin n,
      F (γ.toFun (s i.succ)) - F (γ.toFun (s i.castSucc)) = I_piece i := by
    intro i
    have hlt : s i.castSucc < s i.succ := hs i.castSucc_lt_succ
    have hsub : Icc (s i.castSucc) (s i.succ) ⊆ Icc γ.α γ.β :=
      Icc_subset_Icc (hs0 ▸ hs.monotone (Fin.zero_le _)) (hsn ▸ hs.monotone (Fin.le_last _))
    have hmaps : MapsTo γ.toFun (Icc (s i.castSucc) (s i.succ)) S :=
      fun t ht => hγ (γ.mem_trace_of_mem_Icc (hsub ht))
    have hgcont : ContinuousOn (fun t => f (γ.toFun t) * d i t)
        (Icc (s i.castSucc) (s i.succ)) :=
      (hf_cont.comp (γ.continuousOn.mono hsub) hmaps).mul (hdcont i)
    obtain ⟨ψ, hψcont, hψa, hψb, hψderiv⟩ := hasDerivAt_clamped_primitive hlt.le hgcont
    let G : ℝ → ℂ := fun t => F (γ.toFun t) - ψ t
    have hGcont : ContinuousOn G (Icc (s i.castSucc) (s i.succ)) :=
      (hF_cont.comp (γ.continuousOn.mono hsub) hmaps).sub hψcont.continuousOn
    have hGderiv : ∀ t ∈ Ioo (s i.castSucc) (s i.succ), HasDerivAt G 0 t := by
      intro t ht
      have hmemS : γ.toFun t ∈ S := hmaps (Ioo_subset_Icc_self ht)
      have hcomp_within : HasDerivWithinAt (F ∘ γ.toFun) (d i t • f (γ.toFun t))
          (Icc (s i.castSucc) (s i.succ)) t :=
        (hF_deriv (γ.toFun t) hmemS).scomp t ((hd i t ht).mono hsub) hmaps
      have hcomp : HasDerivAt (fun u => F (γ.toFun u)) (f (γ.toFun t) * d i t) t := by
        have h1 := hcomp_within.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
        simpa [Function.comp_def, smul_eq_mul, mul_comm] using h1
      have hzero : f (γ.toFun t) * d i t - f (γ.toFun t) * d i t = 0 := sub_self _
      exact hzero ▸ hcomp.sub (hψderiv t ht)
    have hGeq : G (s i.castSucc) = G (s i.succ) :=
      eq_endpoints_of_continuousOn_of_hasDerivAt_zero hlt.le hGcont hGderiv
    dsimp [G, I_piece] at hGeq ⊢
    rw [hψa, sub_zero, hψb] at hGeq
    linear_combination -hGeq
  rw [γ.pathIntegral_eq_sum_pieces hf_γ hs hs0 hsn hdcont hd, ← hs0, ← hsn]
  exact (add_piece_telescope (fun t => F (γ.toFun t)) s I_piece hstep).symm

/-- 10.12 (open-path evaluation): if `F` is holomorphic on an open set `Ω` and `F'` is continuous on `Ω`,
then `∫_γ F'(z) dz = F(γ(β)) - F(γ(α))` for every path `γ` in `Ω`. -/
theorem pathIntegral_deriv_eq_sub {Ω : Set ℂ} {F : ℂ → ℂ}
    (hF : HolomorphicOn F Ω) (hF' : ContinuousOn (deriv F) Ω)
    (γ : BookPath) (hγ : γ.trace ⊆ Ω) :
    pathIntegral (deriv F) γ.toBookCurve = F (γ.toFun γ.β) - F (γ.toFun γ.α) :=
  pathIntegral_eq_sub_of_hasDerivWithinAt hF'
    (fun z hz => (hF z hz).hasDerivAt.hasDerivWithinAt) γ hγ

/-- 10.12: if `F ∈ H(Ω)` and `F'` is continuous on `Ω`, then `∫_γ F'(z) dz = 0` for every closed path
`γ` in `Ω`. -/
theorem theorem10_12 {Ω : Set ℂ} (_hΩ : IsOpen Ω) {F : ℂ → ℂ}
    (hF : HolomorphicOn F Ω) (hF' : ContinuousOn (deriv F) Ω)
    (γ : BookPath) (hclosed : γ.IsClosed) (hγ : γ.trace ⊆ Ω) :
    pathIntegral (deriv F) γ.toBookCurve = 0 := by
  rw [pathIntegral_deriv_eq_sub hF hF' γ hγ, show γ.toFun γ.β = γ.toFun γ.α from hclosed.symm, sub_self]

/-- 10.12 (corollary): for every integer `n ≠ -1`, `a ∈ ℂ`, and closed path `γ` (avoiding `a` when
`n < 0`), `∫_γ (z - a)^n dz = 0`. -/
theorem corollary10_12_zpow {n : ℤ} (hn : n ≠ -1) (a : ℂ) (γ : BookPath)
    (hclosed : γ.IsClosed) (ha : n < 0 → a ∉ γ.trace) :
    pathIntegral (fun z => (z - a) ^ n) γ.toBookCurve = 0 := by
  have hn1_int : n + 1 ≠ 0 := by omega
  have hn1 : ((n + 1 : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn1_int
  let S : Set ℂ := if n < 0 then {a}ᶜ else Set.univ
  let F : ℂ → ℂ := fun z => (z - a) ^ (n + 1) / ((n + 1 : ℤ) : ℂ)
  have hγS : γ.trace ⊆ S := by
    intro z hz
    dsimp [S]
    split_ifs with hlt
    · exact fun hza => ha hlt (hza ▸ hz)
    · trivial
  have hcond : ∀ z ∈ S, z - a ≠ 0 ∨ 0 ≤ n + 1 := by
    intro z hz
    dsimp [S] at hz
    split_ifs at hz with hlt
    · exact Or.inl (sub_ne_zero.mpr hz)
    · exact Or.inr (by omega)
  have hF_deriv : ∀ z ∈ S, HasDerivWithinAt F ((z - a) ^ n) S z := by
    intro z hz
    have hd1 : HasDerivAt (fun w : ℂ => (w - a) ^ (n + 1))
        (((n + 1 : ℤ) : ℂ) * (z - a) ^ n * 1) z := by
      have h := (hasDerivAt_zpow (n + 1) (z - a) (hcond z hz)).comp z
        ((hasDerivAt_id z).sub_const a)
      rwa [add_sub_cancel_right] at h
    have hd2 := hd1.div_const ((n + 1 : ℤ) : ℂ)
    have hsimp : ((n + 1 : ℤ) : ℂ) * (z - a) ^ n * 1 / ((n + 1 : ℤ) : ℂ) = (z - a) ^ n := by
      rw [mul_one, mul_div_cancel_left₀ _ hn1]
    rw [hsimp] at hd2
    exact hd2.hasDerivWithinAt
  have hf_cont : ContinuousOn (fun z : ℂ => (z - a) ^ n) S := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    dsimp [S] at hz
    split_ifs at hz with hlt
    · exact ((continuousAt_id.sub continuousAt_const).zpow₀ n (Or.inl (sub_ne_zero.mpr hz)))
    · exact ((continuousAt_id.sub continuousAt_const).zpow₀ n (Or.inr (by omega)))
  rw [pathIntegral_eq_sub_of_hasDerivWithinAt hf_cont hF_deriv γ hγS,
      show γ.toFun γ.β = γ.toFun γ.α from hclosed.symm, sub_self]

/-- Helper for 10.13 & 10.14: continuity on an open set `Ω` plus holomorphy on `Ω \ {p}` upgrades to
holomorphy (`DifferentiableOn ℂ f Ω`) on all of `Ω`, whether `p ∈ Ω` or `p ∉ Ω`. -/
private theorem differentiableOn_of_continuousOn_and_holomorphicOn_sdiff_singleton
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (p : ℂ) {f : ℂ → ℂ}
    (hf_cont : ContinuousOn f Ω) (hf_holo : HolomorphicOn f (Ω \ {p})) :
    DifferentiableOn ℂ f Ω := by
  have hdiff_sdiff : DifferentiableOn ℂ f (Ω \ {p}) :=
    fun z hz => (hf_holo z hz).differentiableWithinAt
  by_cases hp : p ∈ Ω
  · exact (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (hΩ.mem_nhds hp)).mp
      ⟨hdiff_sdiff, (hf_cont p hp).continuousAt (hΩ.mem_nhds hp)⟩
  · have heq : Ω \ {p} = Ω := sdiff_eq_left.mpr (Set.disjoint_singleton_right.mpr hp)
    rwa [heq] at hdiff_sdiff

/-- 10.13 (Cauchy's theorem for a triangle): suppose `Δ = convexHull ℝ {a, b, c}` is a closed triangle
in a plane open set `Ω`, `p ∈ ℂ`, `f` is continuous on `Ω`, and `f ∈ H(Ω \ {p})`. Then
`∫_{∂Δ} f(z) dz = 0` (degenerate triangles and `p ∈ Δ` permitted). -/
theorem theorem10_13 {Ω : Set ℂ} (hΩ : IsOpen Ω) (p : ℂ) {f : ℂ → ℂ}
    (hf_cont : ContinuousOn f Ω) (hf_holo : HolomorphicOn f (Ω \ {p}))
    (a b c : ℂ) (hΔ : convexHull ℝ ({a, b, c} : Set ℂ) ⊆ Ω) :
    pathIntegral f (triangleBoundary a b c).toBookCurve = 0 := by
  let Δ : Set ℂ := convexHull ℝ ({a, b, c} : Set ℂ)
  have hf_diff : DifferentiableOn ℂ f Δ :=
    (differentiableOn_of_continuousOn_and_holomorphicOn_sdiff_singleton hΩ p hf_cont hf_holo).mono hΔ
  obtain ⟨F, hF⟩ := (convex_convexHull ℝ ({a, b, c} : Set ℂ)).exists_forall_hasDerivWithinAt hf_diff
  have haΔ : a ∈ Δ := subset_convexHull ℝ _ (by simp)
  have hbΔ : b ∈ Δ := subset_convexHull ℝ _ (by simp)
  have hcΔ : c ∈ Δ := subset_convexHull ℝ _ (by simp)
  have htrΔ : (triangleBoundary a b c).trace ⊆ Δ := by
    rw [triangleBoundary_trace]
    exact union_subset ((convex_convexHull ℝ _).segment_subset haΔ hbΔ)
      (union_subset ((convex_convexHull ℝ _).segment_subset hbΔ hcΔ)
        ((convex_convexHull ℝ _).segment_subset hcΔ haΔ))
  rw [pathIntegral_eq_sub_of_hasDerivWithinAt (hf_cont.mono hΔ) hF (triangleBoundary a b c) htrΔ,
      show (triangleBoundary a b c).toFun (triangleBoundary a b c).β =
        (triangleBoundary a b c).toFun (triangleBoundary a b c).α
        from (triangleBoundary_isClosed a b c).symm,
      sub_self]

/-- 10.14 (Cauchy's theorem in a convex set): let `Ω` be a convex open set, `p ∈ ℂ`, `f` continuous on
`Ω`, and `f ∈ H(Ω \ {p})`. Then `f = F'` for some `F ∈ H(Ω)`, and hence `∫_γ f(z) dz = 0` for every
closed path `γ` in `Ω`. -/
theorem theorem10_14 {Ω : Set ℂ} (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (p : ℂ) {f : ℂ → ℂ}
    (hf_cont : ContinuousOn f Ω) (hf_holo : HolomorphicOn f (Ω \ {p})) :
    (∃ F : ℂ → ℂ, HolomorphicOn F Ω ∧ ∀ z ∈ Ω, deriv F z = f z) ∧
      ∀ γ : BookPath, γ.IsClosed → γ.trace ⊆ Ω → pathIntegral f γ.toBookCurve = 0 := by
  have hf_diff : DifferentiableOn ℂ f Ω :=
    differentiableOn_of_continuousOn_and_holomorphicOn_sdiff_singleton hΩ p hf_cont hf_holo
  obtain ⟨F, hF_within⟩ := hconv.exists_forall_hasDerivWithinAt hf_diff
  have hF_at : ∀ z ∈ Ω, HasDerivAt F (f z) z :=
    fun z hz => (hF_within z hz).hasDerivAt (hΩ.mem_nhds hz)
  refine ⟨⟨F, fun z hz => (hF_at z hz).differentiableAt, fun z hz => (hF_at z hz).deriv⟩, ?_⟩
  intro γ hclosed hγ
  rw [pathIntegral_eq_sub_of_hasDerivWithinAt hf_cont hF_within γ hγ,
      show γ.toFun γ.β = γ.toFun γ.α from hclosed.symm, sub_self]

/-- 10.15 (Cauchy's integral formula in a convex set): suppose `γ` is a closed path in a convex open
set `Ω`, `f ∈ H(Ω)`, and `z ∈ Ω` with `z ∉ γ*`. Then
`f(z) * Ind_γ(z) = (2πi)⁻¹ ∫_γ f(ζ)/(ζ - z) dζ`. -/
theorem theorem10_15 {Ω : Set ℂ} (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) {f : ℂ → ℂ}
    (hf : HolomorphicOn f Ω) (γ : BookPath) (hclosed : γ.IsClosed) (hγ : γ.trace ⊆ Ω)
    {z : ℂ} (hz : z ∈ Ω) (hz_not : z ∉ γ.trace) :
    f z * Ind γ.toBookCurve z =
      (2 * Real.pi * Complex.I)⁻¹ * pathIntegral (fun ζ => f ζ / (ζ - z)) γ.toBookCurve := by
  let g : ℂ → ℂ := fun ζ => dividedDifference f ζ z
  have hg_cont : ContinuousOn g Ω := by
    have hj := node10_29_jointly_continuous hΩ hf
    exact hj.comp (continuousOn_id.prodMk continuousOn_const) fun ζ hζ => ⟨hζ, hz⟩
  have hg_holo : HolomorphicOn g (Ω \ {z}) := by
    intro ζ hζ
    have hne : ζ ≠ z := hζ.2
    have hev : g =ᶠ[𝓝 ζ] fun w => (f w - f z) / (w - z) := by
      filter_upwards [isOpen_ne.mem_nhds hne] with w hw
      exact dividedDifference_of_ne hw
    exact (((hf ζ hζ.1).sub (differentiableAt_const (f z))).div
      ((differentiableAt_id).sub (differentiableAt_const z)) (sub_ne_zero.mpr hne)).congr_of_eventuallyEq hev
  have hint_g : pathIntegral g γ.toBookCurve = 0 :=
    (theorem10_14 hΩ hconv z hg_cont hg_holo).2 γ hclosed hγ
  have hfg_on_γ : EqOn g (fun ζ => f ζ / (ζ - z) - f z * (ζ - z)⁻¹) γ.trace := by
    intro ζ hζ
    have hne : ζ ≠ z := fun h => hz_not (h ▸ hζ)
    dsimp [g]
    rw [dividedDifference_of_ne hne, sub_div, div_eq_mul_inv (f z)]
  have hf_cont_γ : ContinuousOn (fun ζ => f ζ / (ζ - z)) γ.trace :=
    ((continuousOn_of_holomorphicOn hf).mono hγ).div
      (continuous_id.sub continuous_const).continuousOn
      (fun ζ hζ => sub_ne_zero.mpr fun h => hz_not ((by simpa using h) ▸ hζ))
  have hinv_cont_γ : ContinuousOn (fun ζ : ℂ => (ζ - z)⁻¹) γ.trace :=
    (continuous_id.sub continuous_const).continuousOn.inv₀
      (fun ζ hζ => sub_ne_zero.mpr fun h => hz_not ((by simpa using h) ▸ hζ))
  have hlin : pathIntegral (fun ζ => f ζ / (ζ - z) - f z * (ζ - z)⁻¹) γ.toBookCurve =
      pathIntegral (fun ζ => f ζ / (ζ - z)) γ.toBookCurve -
        f z * pathIntegral (fun ζ => (ζ - z)⁻¹) γ.toBookCurve := by
    unfold pathIntegral
    have h1 := γ.intervalIntegrable_pathIntegral hf_cont_γ
    have h2' := (γ.intervalIntegrable_pathIntegral hinv_cont_γ).const_mul (f z)
    have hcongr : (∫ t in γ.α..γ.β,
        (f (γ.toFun t) / (γ.toFun t - z) - f z * (γ.toFun t - z)⁻¹) *
          derivWithin γ.toFun (Icc γ.α γ.β) t) =
        ∫ t in γ.α..γ.β,
          (f (γ.toFun t) / (γ.toFun t - z) * derivWithin γ.toFun (Icc γ.α γ.β) t -
            f z * ((γ.toFun t - z)⁻¹ * derivWithin γ.toFun (Icc γ.α γ.β) t)) :=
      intervalIntegral.integral_congr fun t _ => by ring
    rw [hcongr, intervalIntegral.integral_sub h1 h2', intervalIntegral.integral_const_mul]
  rw [BookPath.pathIntegral_congr γ.toBookCurve hfg_on_γ, hlin, sub_eq_zero] at hint_g
  unfold Ind
  rw [hint_g]
  ring

/-- 10.17 (Morera's theorem): let `f` be continuous on an open set `Ω ⊆ ℂ`. If `∫_{∂Δ} f(z) dz = 0`
for every closed triangle `Δ = convexHull ℝ {a, b, c} ⊆ Ω`, then `f ∈ H(Ω)`. -/
theorem theorem10_17 {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ}
    (hf_cont : ContinuousOn f Ω)
    (htri : ∀ a b c : ℂ, convexHull ℝ ({a, b, c} : Set ℂ) ⊆ Ω →
      pathIntegral f (triangleBoundary a b c).toBookCurve = 0) :
    HolomorphicOn f Ω := by
  intro z₀ hz₀
  obtain ⟨r, hr, hdisc_sub⟩ := Metric.isOpen_iff.mp hΩ z₀ hz₀
  let F : ℂ → ℂ := fun z => pathIntegral f (orientedSegment z₀ z).toBookCurve
  have hF_deriv : ∀ z ∈ disc z₀ r, HasDerivAt F (f z) z := by
    intro z hz
    have hzΩ : z ∈ Ω := hdisc_sub hz
    have hdiff_F : ∀ w ∈ disc z₀ r, F w - F z =
        (w - z) * ∫ t in (0 : ℝ)..1, f ((1 - t : ℝ) • z + t • w) := by
      intro w hw
      have hconv_sub : convexHull ℝ ({z₀, z, w} : Set ℂ) ⊆ disc z₀ r :=
        convexHull_min (by
          rintro ζ (rfl | rfl | rfl)
          · exact Metric.mem_ball_self hr
          · exact hz
          · exact hw) (convex_ball z₀ r)
      have h0 := htri z₀ z w (hconv_sub.trans hdisc_sub)
      have htr_sub : (triangleBoundary z₀ z w).trace ⊆ Ω := by
        rw [triangleBoundary_trace]
        have hz₀_c : z₀ ∈ convexHull ℝ ({z₀, z, w} : Set ℂ) := subset_convexHull ℝ _ (by simp)
        have hz_c : z ∈ convexHull ℝ ({z₀, z, w} : Set ℂ) := subset_convexHull ℝ _ (by simp)
        have hw_c : w ∈ convexHull ℝ ({z₀, z, w} : Set ℂ) := subset_convexHull ℝ _ (by simp)
        exact (union_subset ((convex_convexHull ℝ _).segment_subset hz₀_c hz_c)
          (union_subset ((convex_convexHull ℝ _).segment_subset hz_c hw_c)
            ((convex_convexHull ℝ _).segment_subset hw_c hz₀_c))).trans (hconv_sub.trans hdisc_sub)
      rw [pathIntegral_triangleBoundary (hf_cont.mono htr_sub),
          pathIntegral_orientedSegment_swap (a := z₀) (b := w)] at h0
      change F z + pathIntegral f (orientedSegment z w).toBookCurve + -F w = 0 at h0
      have hsub : F w - F z = pathIntegral f (orientedSegment z w).toBookCurve := by
        linear_combination -h0
      rw [hsub, pathIntegral_orientedSegment]
    rw [hasDerivAt_iff_difference_quotient, Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ₁, hδ₁, hcont_z⟩ := Metric.continuousWithinAt_iff.mp (hf_cont z hzΩ) (ε / 2) (half_pos hε)
    let δ : ℝ := min δ₁ (r - dist z z₀)
    have hδ_pos : 0 < δ := lt_min hδ₁ (sub_pos.mpr hz)
    refine ⟨δ, hδ_pos, fun w hw_ne hw_dist => ?_⟩
    have hw_disc : w ∈ disc z₀ r := by
      rw [disc, Metric.mem_ball]
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle w z z₀
        _ < δ + dist z z₀ := by linarith
        _ ≤ (r - dist z z₀) + dist z z₀ := by linarith [min_le_right δ₁ (r - dist z z₀)]
        _ = r := sub_add_cancel r _
    have hquot : (F w - F z) / (w - z) = ∫ t in (0 : ℝ)..1, f ((1 - t : ℝ) • z + t • w) := by
      rw [hdiff_F w hw_disc, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hw_ne)]
    have hconst_int : f z = ∫ _ in (0 : ℝ)..1, f z := by
      rw [intervalIntegral.integral_const, sub_zero, one_smul]
    have hg_cont : ContinuousOn (fun t : ℝ => f ((1 - t : ℝ) • z + t • w)) (Icc 0 1) := by
      refine hf_cont.comp (((continuous_const.sub continuous_id).smul continuous_const).add
        (continuous_id.smul continuous_const)).continuousOn fun t ht => hdisc_sub ?_
      exact (convex_ball z₀ r) hz hw_disc (sub_nonneg.mpr ht.2) ht.1 (by ring)
    have hg_int : IntervalIntegrable (fun t : ℝ => f ((1 - t : ℝ) • z + t • w))
        MeasureTheory.volume 0 1 :=
      hg_cont.intervalIntegrable_of_Icc zero_le_one
    rw [dist_eq_norm, hquot]
    have hdiff_int : (∫ t in (0 : ℝ)..1, f ((1 - t : ℝ) • z + t • w)) - f z =
        ∫ t in (0 : ℝ)..1, (f ((1 - t : ℝ) • z + t • w) - f z) := by
      rw [intervalIntegral.integral_sub hg_int intervalIntegrable_const, ← hconst_int]
    rw [hdiff_int]
    have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖f ((1 - t : ℝ) • z + t • w) - f z‖ ≤ ε / 2 := by
      intro t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      have ht_mem : (1 - t : ℝ) • z + t • w ∈ Ω :=
        hdisc_sub ((convex_ball z₀ r) hz hw_disc (sub_nonneg.mpr ht.2) ht.1.le (by ring))
      have ht_dist : dist ((1 - t : ℝ) • z + t • w) z < δ₁ := by
        rw [dist_eq_norm]
        have heq : (1 - t : ℝ) • z + t • w - z = t • (w - z) := by
          simp [Complex.real_smul]; ring
        rw [heq, norm_smul, Real.norm_of_nonneg ht.1.le]
        calc t * ‖w - z‖ ≤ 1 * ‖w - z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
          _ = dist w z := by rw [one_mul, dist_eq_norm]
          _ < δ := hw_dist
          _ ≤ δ₁ := min_le_left _ _
      rw [← dist_eq_norm]
      exact (hcont_z ht_mem ht_dist).le
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [sub_zero, abs_one, mul_one] at hle
    linarith
  have hF_holo : HolomorphicOn F (disc z₀ r) := fun z hz => (hF_deriv z hz).differentiableAt
  have hdf_holo : HolomorphicOn (deriv F) (disc z₀ r) := holomorphicOn_deriv Metric.isOpen_ball hF_holo
  have heq : deriv F =ᶠ[𝓝 z₀] f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with z hz
    exact (hF_deriv z hz).deriv
  exact (hdf_holo z₀ (Metric.mem_ball_self hr)).congr_of_eventuallyEq heq.symm

/-! ### 10.5, 10.7, 10.21 & 10.22: Root-test radius, Cauchy transforms of complex measures, isolated singularity trichotomy, and Parseval's identity -/

section BatchB
open scoped ENNReal NNReal

/-- 10.5: Cauchy–Hadamard radius of convergence `R = (limsup_{n→∞} |c_n|^{1/n})⁻¹ ∈ [0, ∞]` of a
scalar power series `∑ c_n (z - a)^n`. -/
noncomputable def powerSeriesRadius (c : ℕ → ℂ) : ℝ≥0∞ :=
  (Filter.limsup (fun n : ℕ => ((‖c n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop)⁻¹

/-- `powerSeriesRadius c` agrees identically with `(FormalMultilinearSeries.ofScalars ℂ c).radius`. -/
theorem powerSeriesRadius_eq_ofScalars_radius (c : ℕ → ℂ) :
    powerSeriesRadius c = (FormalMultilinearSeries.ofScalars ℂ c).radius := by
  let p := FormalMultilinearSeries.ofScalars ℂ c
  have hnorm : ∀ n : ℕ, ‖p n‖₊ = ‖c n‖₊ := fun n => by
    ext
    exact FormalMultilinearSeries.ofScalars_norm ℂ c n
  have hinv := p.radius_inv_eq_limsup
  simp_rw [hnorm] at hinv
  rw [powerSeriesRadius, ← hinv, inv_inv]

/-- 10.5: (a) absolute and uniform convergence of `∑ c_n (z - a)^n` on every closed disc
`closedDisc a r` with `0 < r` and `r < R`; (b) absolute convergence for `‖z - a‖ < R` and
divergence for `‖z - a‖ > R`. -/
theorem theorem10_5 (c : ℕ → ℂ) (a : ℂ) :
    (∀ r : ℝ, 0 < r → ENNReal.ofReal r < powerSeriesRadius c →
      Summable (fun n : ℕ => ‖c n‖ * r ^ n) ∧
      (∀ z ∈ closedDisc a r, Summable (fun n : ℕ => ‖c n * (z - a) ^ n‖)) ∧
      TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N, c n * (z - a) ^ n)
        (fun z => ∑' n : ℕ, c n * (z - a) ^ n) atTop (closedDisc a r)) ∧
    (∀ z : ℂ, ‖z - a‖ₑ < powerSeriesRadius c →
      Summable (fun n : ℕ => ‖c n * (z - a) ^ n‖)) ∧
    (∀ z : ℂ, powerSeriesRadius c < ‖z - a‖ₑ →
      ¬ Summable (fun n : ℕ => c n * (z - a) ^ n)) := by
  let p := FormalMultilinearSeries.ofScalars ℂ c
  have hrad : powerSeriesRadius c = p.radius := powerSeriesRadius_eq_ofScalars_radius c
  refine ⟨?_, ?_, ?_⟩
  · intro r hr hrR
    have hr_coe : (Real.toNNReal r : ℝ≥0∞) < p.radius := by
      rwa [← hrad, ← ENNReal.ofReal]
    have hsum_r : Summable (fun n : ℕ => ‖c n‖ * r ^ n) := by
      have h := p.summable_norm_mul_pow hr_coe
      simpa only [p, FormalMultilinearSeries.ofScalars_norm ℂ, Real.coe_toNNReal r hr.le] using h
    have hbound : ∀ z ∈ closedDisc a r, ∀ n : ℕ, ‖c n * (z - a) ^ n‖ ≤ ‖c n‖ * r ^ n := by
      intro z hz n
      have hza : ‖z - a‖ ≤ r := (mem_closedDisc hr).mp hz
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hza n) (norm_nonneg _)
    refine ⟨hsum_r, fun z hz => Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hbound z hz) hsum_r, ?_⟩
    exact tendstoUniformlyOn_tsum_nat hsum_r fun n z hz => hbound z hz n
  · intro z hz
    rw [hrad] at hz
    have hsum := p.summable_norm_mul_pow (r := ‖z - a‖₊) (by simpa [enorm_eq_nnnorm] using hz)
    simpa only [p, FormalMultilinearSeries.ofScalars_norm ℂ, coe_nnnorm, norm_mul, norm_pow] using hsum
  · intro z hz hsum
    rw [hrad] at hz
    have htend : Tendsto (fun n : ℕ => ‖p n‖ * (‖z - a‖₊ : ℝ) ^ n) atTop (𝓝 0) := by
      have h := hsum.norm.tendsto_atTop_zero
      simpa only [p, FormalMultilinearSeries.ofScalars_norm ℂ, coe_nnnorm, norm_mul, norm_pow] using h
    have hle : (‖z - a‖₊ : ℝ≥0∞) ≤ p.radius := p.le_radius_of_tendsto htend
    rw [← enorm_eq_nnnorm] at hle
    exact not_le_of_gt hz hle

/-- Every complex measure has finite total variation (Rudin 6.4, self-contained helper for 10.7). -/
private theorem complexMeasure_variation_finite {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ComplexMeasure X) : MeasureTheory.IsFiniteMeasure μ.variation where
  measure_univ_lt_top := by
    have hle : μ.variation ≤ μ.re.totalVariation + μ.im.totalVariation := by
      apply MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le
      intro E _
      have h : ‖μ E‖ ≤ μ.re.totalVariation.real E + μ.im.totalVariation.real E := by
        calc ‖μ E‖ ≤ |(μ E).re| + |(μ E).im| := Complex.norm_le_abs_re_add_abs_im _
          _ ≤ μ.re.totalVariation.real E + μ.im.totalVariation.real E := by
            have h₁ := μ.re.norm_le_totalVariation E
            have h₂ := μ.im.norm_le_totalVariation E
            change ‖(μ E).re‖ ≤ _ at h₁
            change ‖(μ E).im‖ ≤ _ at h₂
            rw [Real.norm_eq_abs] at h₁ h₂
            exact add_le_add h₁ h₂
      calc ‖μ E‖ₑ = ENNReal.ofReal ‖μ E‖ := (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (μ.re.totalVariation.real E + μ.im.totalVariation.real E) :=
          ENNReal.ofReal_le_ofReal h
        _ = (μ.re.totalVariation + μ.im.totalVariation) E := by
          rw [ENNReal.ofReal_add MeasureTheory.measureReal_nonneg MeasureTheory.measureReal_nonneg]
          simp only [MeasureTheory.measureReal_def,
            ENNReal.ofReal_toReal (MeasureTheory.measure_ne_top _ _),
            MeasureTheory.Measure.add_apply]
    exact lt_of_le_of_lt (hle Set.univ) (MeasureTheory.measure_lt_top _ _)

/-- 10.7: integral `∫_X g(x) dμ(x)` of a complex-valued function `g : X → ℂ` with respect to an
arbitrary complex measure `μ : ComplexMeasure X`. -/
noncomputable def complexMeasureIntegral {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ComplexMeasure X) (g : X → ℂ) : ℂ :=
  ∫ᵛ x, g x ∂[ContinuousLinearMap.mul ℝ ℂ; μ]

/-- Complex scalar linearity `∫ (c * g(x)) dμ(x) = c * ∫ g(x) dμ(x)` for `complexMeasureIntegral`. -/
theorem complexMeasureIntegral_const_mul {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ComplexMeasure X) (c : ℂ) (g : X → ℂ) :
    complexMeasureIntegral μ (fun x => c * g x) = c * complexMeasureIntegral μ g := by
  unfold complexMeasureIntegral MeasureTheory.VectorMeasure.integral
  exact MeasureTheory.setToFun_smul
    (MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure μ (ContinuousLinearMap.mul ℝ ℂ))
    (fun w s x => by simp [MeasureTheory.transpose_eq_cbmApplyMeasure, mul_assoc]) c g

theorem complexMeasureIntegral_mul_const {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ComplexMeasure X) (g : X → ℂ) (c : ℂ) :
    complexMeasureIntegral μ (fun x => g x * c) = complexMeasureIntegral μ g * c := by
  simp_rw [mul_comm _ c]
  exact complexMeasureIntegral_const_mul μ c g

/-- Total-variation bound `‖∫_X g dμ‖ ≤ C · |μ|(X)` whenever `‖g(x)‖ ≤ C` for all `x ∈ X`. -/
theorem norm_complexMeasureIntegral_le_of_norm_le_const {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ComplexMeasure X) {g : X → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ x : X, ‖g x‖ ≤ C) :
    ‖complexMeasureIntegral μ g‖ ≤ C * μ.variation.real Set.univ := by
  have : MeasureTheory.IsFiniteMeasure μ.variation := complexMeasure_variation_finite μ
  have hB : ‖ContinuousLinearMap.mul ℝ ℂ‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    rw [one_mul]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg z) fun w => ?_
    simp
  have h1 := MeasureTheory.VectorMeasure.norm_integral_le_of_norm_le_const
    (μ := μ) (B := ContinuousLinearMap.mul ℝ ℂ) (f := g) (C := C)
    (Filter.Eventually.of_forall hg)
  calc ‖complexMeasureIntegral μ g‖
      ≤ C * ‖ContinuousLinearMap.mul ℝ ℂ‖ * μ.variation.real Set.univ := h1
    _ ≤ C * 1 * μ.variation.real Set.univ := by
      gcongr
    _ = C * μ.variation.real Set.univ := by ring

/-- 10.7: Cauchy-type transform `f(z) = ∫_X (φ(x) - z)⁻¹ dμ(x)` of a complex measure `μ` along a
measurable map `φ : X → ℂ`. -/
noncomputable def cauchyTransform {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ComplexMeasure X) (φ : X → ℂ) (z : ℂ) : ℂ :=
  complexMeasureIntegral μ (fun x => (φ x - z)⁻¹)

/-- 10.7: let `μ` be a complex measure on a measurable space `X`, `φ : X → ℂ` be measurable, and
`Ω ⊆ ℂ` be an open set disjoint from `φ(X)`. Then `f(z) = ∫_X (φ(x) - z)⁻¹ dμ(x)` is representable
by power series in `Ω`; specifically, on every `disc a r ⊆ Ω` (`r > 0`), the coefficients
`c_n = ∫_X (φ(x) - a)^{-(n+1)} dμ(x)` satisfy `f(z) = ∑_{n=0}^∞ c_n (z - a)^n` on `disc a r` and
`‖c_n‖ ≤ |μ|(X) / r^{n+1}` (with no compactness of `X` or boundedness of `φ` assumed). -/
theorem theorem10_7 {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ComplexMeasure X) {φ : X → ℂ} (hφ : Measurable φ)
    {Ω : Set ℂ} (_hΩ : IsOpen Ω) (hdisj : Disjoint Ω (Set.range φ)) :
    RepresentableByPowerSeries (cauchyTransform μ φ) Ω ∧
      ∀ (a : ℂ) (r : ℝ), 0 < r → disc a r ⊆ Ω →
        let c : ℕ → ℂ := fun n =>
          complexMeasureIntegral μ (fun x => ((φ x - a) ^ (n + 1))⁻¹)
        (∀ z ∈ disc a r, HasSum (fun n : ℕ => c n * (z - a) ^ n) (cauchyTransform μ φ z)) ∧
        (∀ n : ℕ, ‖c n‖ ≤ μ.variation.real Set.univ / r ^ (n + 1)) := by
  have : MeasureTheory.IsFiniteMeasure μ.variation := complexMeasure_variation_finite μ
  have hmain : ∀ (a : ℂ) (r : ℝ), 0 < r → disc a r ⊆ Ω →
      let c : ℕ → ℂ := fun n =>
        complexMeasureIntegral μ (fun x => ((φ x - a) ^ (n + 1))⁻¹)
      (∀ z ∈ disc a r, HasSum (fun n : ℕ => c n * (z - a) ^ n) (cauchyTransform μ φ z)) ∧
      (∀ n : ℕ, ‖c n‖ ≤ μ.variation.real Set.univ / r ^ (n + 1)) := by
    intro a r hr hsub
    dsimp only
    let c : ℕ → ℂ := fun n => complexMeasureIntegral μ (fun x => ((φ x - a) ^ (n + 1))⁻¹)
    have hφ_ge : ∀ x : X, r ≤ ‖φ x - a‖ := by
      intro x
      by_contra hlt
      exact Set.disjoint_left.mp hdisj (hsub (mem_disc.mpr (not_le.mp hlt))) ⟨x, rfl⟩
    have hc_bound : ∀ n : ℕ, ‖c n‖ ≤ μ.variation.real Set.univ / r ^ (n + 1) := by
      intro n
      have hpt : ∀ x : X, ‖((φ x - a) ^ (n + 1))⁻¹‖ ≤ (r ^ (n + 1))⁻¹ := by
        intro x
        rw [norm_inv, norm_pow]
        exact inv_anti₀ (pow_pos hr (n + 1)) (pow_le_pow_left₀ hr.le (hφ_ge x) (n + 1))
      have hle := norm_complexMeasureIntegral_le_of_norm_le_const μ
        (inv_nonneg.mpr (pow_pos hr (n + 1)).le) hpt
      rwa [div_eq_inv_mul]
    refine ⟨?_, hc_bound⟩
    intro z hz
    have hza : ‖z - a‖ < r := mem_disc.mp hz
    let q : ℝ := ‖z - a‖ / r
    have hq_nonneg : 0 ≤ q := div_nonneg (norm_nonneg _) hr.le
    have hq_lt : q < 1 := (div_lt_one hr).mpr hza
    let F : ℕ → X → ℂ := fun n x => ((φ x - a) ^ (n + 1))⁻¹ * (z - a) ^ n
    let bound : ℕ → X → ℝ := fun n _ => r⁻¹ * q ^ n
    have hF_meas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (F n) μ.variation := by
      intro n
      exact (((((hφ.sub measurable_const).pow_const (n + 1)).inv).mul_const ((z - a) ^ n))).aestronglyMeasurable
    have hF_bound : ∀ n : ℕ, ∀ᵐ x ∂μ.variation, ‖F n x‖ ≤ bound n x := by
      intro n
      refine Filter.Eventually.of_forall fun x => ?_
      dsimp [F, bound, q]
      rw [norm_mul, norm_inv, norm_pow, norm_pow, div_pow, pow_succ', inv_mul_eq_div,
        ← mul_div_assoc, mul_comm r⁻¹]
      have h1 : ‖φ x - a‖⁻¹ ≤ r⁻¹ := inv_anti₀ hr (hφ_ge x)
      have h2 : (‖φ x - a‖ ^ n)⁻¹ ≤ (r ^ n)⁻¹ :=
        inv_anti₀ (pow_pos hr n) (pow_le_pow_left₀ hr.le (hφ_ge x) n)
      calc ‖z - a‖ ^ n / (‖φ x - a‖ * ‖φ x - a‖ ^ n)
          = ‖z - a‖ ^ n * ‖φ x - a‖⁻¹ * (‖φ x - a‖ ^ n)⁻¹ := by ring
        _ ≤ ‖z - a‖ ^ n * r⁻¹ * (r ^ n)⁻¹ := by
          gcongr
        _ = ‖z - a‖ ^ n * r⁻¹ / r ^ n := by ring
    have hsum_q : Summable (fun n : ℕ => r⁻¹ * q ^ n) :=
      (summable_geometric_of_lt_one hq_nonneg hq_lt).mul_left r⁻¹
    have hbound_sum : ∀ᵐ x ∂μ.variation, Summable (fun n : ℕ => bound n x) :=
      Filter.Eventually.of_forall fun _ => hsum_q
    have hbound_int : MeasureTheory.Integrable (fun x : X => ∑' n : ℕ, bound n x) μ.variation := by
      dsimp only [bound]
      exact MeasureTheory.integrable_const _
    have hF_lim : ∀ᵐ x ∂μ.variation, HasSum (fun n : ℕ => F n x) ((φ x - z)⁻¹) := by
      refine Filter.Eventually.of_forall fun x => ?_
      have hφ_ne : φ x - a ≠ 0 := fun h0 => by
        have := hφ_ge x; rw [h0, norm_zero] at this; linarith
      let w : ℂ := (z - a) / (φ x - a)
      have hw_lt : ‖w‖ < 1 := by
        dsimp [w]
        rw [norm_div]
        exact (div_lt_one (lt_of_lt_of_le hr (hφ_ge x))).mpr (lt_of_lt_of_le hza (hφ_ge x))
      have hgeom := (hasSum_geometric_of_norm_lt_one hw_lt).mul_left (φ x - a)⁻¹
      have hterm : (fun n : ℕ => (φ x - a)⁻¹ * w ^ n) = fun n : ℕ => F n x := by
        ext n
        dsimp [w, F]
        rw [div_pow, pow_succ', mul_inv, div_eq_mul_inv]
        ring
      have hval : (φ x - a)⁻¹ * (1 - w)⁻¹ = (φ x - z)⁻¹ := by
        have h1w : 1 - w = (φ x - z) / (φ x - a) := by
          dsimp [w]; field_simp; ring
        have hφz_ne : φ x - z ≠ 0 := fun h0 => by
          have heq : φ x = z := sub_eq_zero.mp h0
          have hx := hφ_ge x
          rw [heq] at hx
          linarith
        rw [h1w, inv_div]
        field_simp
      rwa [hterm, hval] at hgeom
    have hdom := MeasureTheory.VectorMeasure.hasSum_integral_of_dominated_convergence
      (μ := μ) (B := ContinuousLinearMap.mul ℝ ℂ) bound hF_meas hF_bound hbound_sum hbound_int hF_lim
    have hint_F : (fun n : ℕ => ∫ᵛ x, F n x ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) =
        fun n : ℕ => c n * (z - a) ^ n := by
      ext n
      exact complexMeasureIntegral_mul_const μ (fun x => ((φ x - a) ^ (n + 1))⁻¹) ((z - a) ^ n)
    rwa [hint_F] at hdom
  exact ⟨fun a r hr hsub => ⟨_, (hmain a r hr hsub).1⟩, hmain⟩

/-- 10.21: finite principal part `Q(z) = ∑_{k=1}^m c_k (z - a)^{-k}` with `m ≥ 1` and `c_m ≠ 0`. -/
def IsPrincipalPart (Q : ℂ → ℂ) (a : ℂ) : Prop :=
  ∃ (m : ℕ) (c : ℕ → ℂ), 0 < m ∧ c m ≠ 0 ∧
    ∀ z : ℂ, Q z = ∑ k ∈ Finset.Icc 1 m, c k * (z - a)⁻¹ ^ k

/-- 10.21: `f` has a pole at `a` in `Ω` if `HasIsolatedSingularity f Ω a` and `f = g + Q` on
`Ω \ {a}` with `g ∈ H(Ω)` and `Q` a principal part at `a`. -/
def HasPole (f : ℂ → ℂ) (Ω : Set ℂ) (a : ℂ) : Prop :=
  HasIsolatedSingularity f Ω a ∧
    ∃ (g Q : ℂ → ℂ), HolomorphicOn g Ω ∧ IsPrincipalPart Q a ∧
      EqOn f (fun z => g z + Q z) (Ω \ {a})

/-- 10.21: `f` has an essential singularity at `a` in `Ω` if `a` is an isolated singularity that is
neither removable nor a pole. -/
def HasEssentialSingularity (f : ℂ → ℂ) (Ω : Set ℂ) (a : ℂ) : Prop :=
  HasIsolatedSingularity f Ω a ∧ ¬ HasRemovableSingularity f Ω a ∧ ¬ HasPole f Ω a

/-- Iterated `dslope` Taylor expansion with holomorphic remainder on an open set `Ω` around `a ∈ Ω`:
`u(z) = (∑_{j < m} d_j (z - a)^j) + (z - a)^m * R(z)` for ALL `z : ℂ`, where `R ∈ H(Ω)` and
`d_0 = u(a)`. -/
theorem dslope_taylor_expansion {Ω : Set ℂ} (hΩ : IsOpen Ω) {a : ℂ} (ha : a ∈ Ω)
    {u : ℂ → ℂ} (hu : HolomorphicOn u Ω) :
    ∀ m : ℕ, ∃ (d : ℕ → ℂ) (R : ℂ → ℂ),
      HolomorphicOn R Ω ∧ d 0 = u a ∧
      ∀ z : ℂ, u z = (∑ j ∈ Finset.range m, d j * (z - a) ^ j) + (z - a) ^ m * R z
  | 0 => ⟨fun _ => u a, u, hu, rfl, fun z => by simp⟩
  | m + 1 => by
    obtain ⟨d, R, hR, hd0, heq⟩ := dslope_taylor_expansion hΩ ha hu m
    let R₁ : ℂ → ℂ := dslope R a
    have hR₁ : HolomorphicOn R₁ Ω := by
      have hd := (Complex.differentiableOn_dslope (hΩ.mem_nhds ha)).mpr
        ((holomorphicOn_iff_differentiableOn hΩ).mp hR)
      exact (holomorphicOn_iff_differentiableOn hΩ).mpr hd
    have hR_split : ∀ z : ℂ, R z = R a + (z - a) * R₁ z := by
      intro z
      by_cases hza : z = a
      · subst hza; simp
      · dsimp [R₁]
        rw [dslope_of_ne R hza, slope_def_field, mul_div_cancel₀ _ (sub_ne_zero.mpr hza)]
        ring
    let d' : ℕ → ℂ := fun j => if j = m then R a else d j
    refine ⟨d', R₁, hR₁, ?_, ?_⟩
    · dsimp [d']
      split_ifs with hm0
      · subst hm0
        have ha_eq := heq a
        simpa using ha_eq.symm
      · exact hd0
    · intro z
      rw [Finset.sum_range_succ]
      have hsum_eq : ∑ x ∈ Finset.range m, d' x * (z - a) ^ x =
          ∑ x ∈ Finset.range m, d x * (z - a) ^ x := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxm : x ≠ m := ne_of_lt (Finset.mem_range.mp hx)
        simp [d', hxm]
      have hdm : d' m = R a := by simp [d']
      rw [hsum_eq, hdm, heq z, hR_split z]
      ring

/-- Helper: if `Q` is a principal part of order `m` with leading coefficient `c_m ≠ 0`, then
`(z - a)^m * Q(z) → c_m` as `z → a` (`z ≠ a`), and hence `‖Q(z)‖ → ∞` as `z → a` (`z ≠ a`). -/
theorem tendsto_norm_atTop_of_isPrincipalPart {Q : ℂ → ℂ} {a : ℂ} (hQ : IsPrincipalPart Q a) :
    Tendsto (fun z => ‖Q z‖) (𝓝[≠] a) atTop := by
  obtain ⟨m, c, hm, hcm, hQeq⟩ := hQ
  have hmul_lim : Tendsto (fun z : ℂ => (z - a) ^ m * Q z) (𝓝[≠] a) (𝓝 (c m)) := by
    have hcongr : (fun z : ℂ => (z - a) ^ m * Q z) =ᶠ[𝓝[≠] a]
        fun z : ℂ => c m + ∑ k ∈ Finset.Ico 1 m, c k * (z - a) ^ (m - k) := by
      filter_upwards [self_mem_nhdsWithin] with z hza
      have hne : z - a ≠ 0 := sub_ne_zero.mpr hza
      rw [hQeq z, Finset.mul_sum, ← Finset.Ico_insert_right (Nat.succ_le_of_lt hm),
          Finset.sum_insert Finset.right_notMem_Ico]
      congr 1
      · rw [mul_comm (c m), ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_mul]
      · refine Finset.sum_congr rfl fun k hk => ?_
        have hkm : k ≤ m := (Finset.mem_Ico.mp hk).2.le
        have hpow : (z - a) ^ m * (z - a)⁻¹ ^ k = (z - a) ^ (m - k) := by
          have hm_split : m = (m - k) + k := (Nat.sub_add_cancel hkm).symm
          conv_lhs => rw [hm_split, pow_add]
          rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hne, one_pow, mul_one]
        linear_combination c k * hpow
    refine Tendsto.congr' hcongr.symm ?_
    have hsum0 : Tendsto (fun z : ℂ => ∑ k ∈ Finset.Ico 1 m, c k * (z - a) ^ (m - k))
        (𝓝[≠] a) (𝓝 0) := by
      have hcont : Continuous (fun z : ℂ => ∑ k ∈ Finset.Ico 1 m, c k * (z - a) ^ (m - k)) :=
        continuous_finsetSum _ fun k _ =>
          continuous_const.mul ((continuous_id.sub continuous_const).pow _)
      have hval0 : (∑ k ∈ Finset.Ico 1 m, c k * (a - a) ^ (m - k)) = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hsub_pos : 0 < m - k := Nat.sub_pos_of_lt (Finset.mem_Ico.mp hk).2
        simp [zero_pow hsub_pos.ne']
      exact hval0 ▸ hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.add hsum0
  rw [Filter.tendsto_atTop]
  intro B
  have hcm_pos : 0 < ‖c m‖ := norm_pos_iff.mpr hcm
  have hev_num : ∀ᶠ z in 𝓝[≠] a, ‖c m‖ / 2 ≤ ‖(z - a) ^ m * Q z‖ :=
    hmul_lim.norm.eventually (Ici_mem_nhds (half_lt_self hcm_pos))
  let B' : ℝ := max B 1
  have hB'_pos : 0 < B' := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  have hpow_zero : Tendsto (fun z : ℂ => ‖z - a‖ ^ m) (𝓝[≠] a) (𝓝 0) := by
    have hc : Continuous (fun z : ℂ => ‖z - a‖ ^ m) :=
      ((continuous_id.sub continuous_const).norm).pow m
    have hv : ‖a - a‖ ^ m = 0 := by simp [zero_pow hm.ne']
    exact hv ▸ hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev_den : ∀ᶠ z in 𝓝[≠] a, ‖z - a‖ ^ m < (‖c m‖ / 2) / B' :=
    hpow_zero.eventually (gt_mem_nhds (div_pos (half_pos hcm_pos) hB'_pos))
  filter_upwards [self_mem_nhdsWithin, hev_num, hev_den] with z hza hnum hden
  have hpow_pos : 0 < ‖z - a‖ ^ m := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hza)) m
  rw [norm_mul, norm_pow] at hnum
  have hlt : B' * ‖z - a‖ ^ m < ‖z - a‖ ^ m * ‖Q z‖ :=
    lt_of_lt_of_le ((lt_div_iff₀' hB'_pos).mp hden) hnum
  have hQ_gt : B' < ‖Q z‖ := lt_of_mul_lt_mul_left (by linarith) hpow_pos.le
  exact le_trans (le_max_left B 1) hQ_gt.le

/-- 10.21: at any pole `a`, `‖f(z)‖ → ∞` as `z → a` (`z ≠ a`). -/
theorem tendsto_norm_atTop_of_hasPole {f : ℂ → ℂ} {Ω : Set ℂ} {a : ℂ}
    (hpole : HasPole f Ω a) :
    Tendsto (fun z => ‖f z‖) (𝓝[≠] a) atTop := by
  obtain ⟨⟨hΩ, ha, _⟩, g, Q, hg, hQ, hfgQ⟩ := hpole
  have hQ_top := tendsto_norm_atTop_of_isPrincipalPart hQ
  have hg_lim : Tendsto (fun z => ‖g z‖) (𝓝[≠] a) (𝓝 ‖g a‖) :=
    (hg a ha).continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds
  rw [Filter.tendsto_atTop] at hQ_top ⊢
  intro B
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hΩ.mem_nhds ha),
    hQ_top (B + (‖g a‖ + 1)),
    hg_lim.eventually (gt_mem_nhds (lt_add_one ‖g a‖))] with z hza hzΩ hQz hgz
  have heq : f z = g z + Q z := hfgQ ⟨hzΩ, hza⟩
  have htri : ‖Q z‖ ≤ ‖f z‖ + ‖g z‖ := by
    calc ‖Q z‖ = ‖f z - g z‖ := by rw [heq, add_sub_cancel_left]
      _ ≤ ‖f z‖ + ‖g z‖ := norm_sub_le _ _
  linarith

/-- 10.21: the principal part of a pole is unique (`Q₁ = Q₂` everywhere on `ℂ \ {a}`). -/
theorem principalPart_unique_of_hasPole {Ω : Set ℂ} (hΩ : IsOpen Ω) {a : ℂ} (ha : a ∈ Ω)
    {g₁ g₂ Q₁ Q₂ : ℂ → ℂ} (hg₁ : HolomorphicOn g₁ Ω) (hg₂ : HolomorphicOn g₂ Ω)
    (hQ₁ : IsPrincipalPart Q₁ a) (hQ₂ : IsPrincipalPart Q₂ a)
    (heq : EqOn (fun z => g₁ z + Q₁ z) (fun z => g₂ z + Q₂ z) (Ω \ {a})) :
    EqOn Q₁ Q₂ ({a}ᶜ) := by
  obtain ⟨m₁, c₁, hm₁, _, hQ₁_eq⟩ := hQ₁
  obtain ⟨m₂, c₂, hm₂, _, hQ₂_eq⟩ := hQ₂
  let M := max m₁ m₂
  let c₁' : ℕ → ℂ := fun k => if k ≤ m₁ then c₁ k else 0
  let c₂' : ℕ → ℂ := fun k => if k ≤ m₂ then c₂ k else 0
  have hpad1 : ∀ z, Q₁ z = ∑ k ∈ Finset.Icc 1 M, c₁' k * (z - a)⁻¹ ^ k := by
    intro z
    rw [hQ₁_eq z]
    refine (Finset.sum_congr rfl fun k hk => ?_).trans
      (Finset.sum_subset (Finset.Icc_subset_Icc_right (le_max_left m₁ m₂)) fun k hk hnot => ?_)
    · simp [c₁', (Finset.mem_Icc.mp hk).2]
    · have hk_gt : ¬ k ≤ m₁ := fun hle => hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, hle⟩)
      simp [c₁', hk_gt]
  have hpad2 : ∀ z, Q₂ z = ∑ k ∈ Finset.Icc 1 M, c₂' k * (z - a)⁻¹ ^ k := by
    intro z
    rw [hQ₂_eq z]
    refine (Finset.sum_congr rfl fun k hk => ?_).trans
      (Finset.sum_subset (Finset.Icc_subset_Icc_right (le_max_right m₁ m₂)) fun k hk hnot => ?_)
    · simp [c₂', (Finset.mem_Icc.mp hk).2]
    · have hk_gt : ¬ k ≤ m₂ := fun hle => hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, hle⟩)
      simp [c₂', hk_gt]
  by_contra hne_on
  have hex_k : ∃ k ∈ Finset.Icc 1 M, c₁' k - c₂' k ≠ 0 := by
    by_contra hall
    apply hne_on
    intro z _
    rw [hpad1 z, hpad2 z]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : c₁' k - c₂' k = 0 := by
      by_contra hkne
      exact hall ⟨k, hk, hkne⟩
    rw [sub_eq_zero.mp hk0]
  let S : Finset ℕ := (Finset.Icc 1 M).filter (fun k => c₁' k - c₂' k ≠ 0)
  have hSne : S.Nonempty := by
    obtain ⟨k, hk, hkne⟩ := hex_k
    exact ⟨k, Finset.mem_filter.mpr ⟨hk, hkne⟩⟩
  let K := S.max' hSne
  have hK_mem := Finset.mem_filter.mp (S.max'_mem hSne)
  have hK_pos : 0 < K := Nat.lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hK_mem.1).1
  have hdiff_pp : IsPrincipalPart (fun z => Q₁ z - Q₂ z) a := by
    refine ⟨K, fun k => c₁' k - c₂' k, hK_pos, hK_mem.2, fun z => ?_⟩
    dsimp only
    rw [hpad1 z, hpad2 z, ← Finset.sum_sub_distrib]
    have hK_le : K ≤ M := (Finset.mem_Icc.mp hK_mem.1).2
    refine (Finset.sum_congr rfl (g := fun k => (c₁' k - c₂' k) * (z - a)⁻¹ ^ k)
      fun k _ => by ring).trans ?_
    symm
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right hK_le) fun k hk hnot => ?_
    have hk_gt : K < k := not_le.mp fun hle => hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, hle⟩)
    have hzero : c₁' k - c₂' k = 0 := by
      by_contra hkne
      exact not_le_of_gt hk_gt (S.le_max' k (Finset.mem_filter.mpr ⟨hk, hkne⟩))
    simp [hzero]
  have htop := tendsto_norm_atTop_of_isPrincipalPart hdiff_pp
  have hlim : Tendsto (fun z => ‖Q₁ z - Q₂ z‖) (𝓝[≠] a) (𝓝 ‖g₂ a - g₁ a‖) := by
    have hcongr : (fun z => ‖Q₁ z - Q₂ z‖) =ᶠ[𝓝[≠] a] fun z => ‖g₂ z - g₁ z‖ := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hΩ.mem_nhds ha)] with z hza hzΩ
      have h := heq ⟨hzΩ, hza⟩
      have hsub : Q₁ z - Q₂ z = g₂ z - g₁ z := by linear_combination h
      rw [hsub]
    exact (((hg₂ a ha).continuousAt.sub (hg₁ a ha).continuousAt).norm.tendsto.mono_left
      nhdsWithin_le_nhds).congr' hcongr.symm
  exact not_tendsto_nhds_of_tendsto_atTop htop _ hlim

/-- 10.21 (Casorati–Weierstrass & isolated singularity trichotomy): suppose `f` has an isolated
singularity at `a` in `Ω`.
1. Exclusivity: at most one of `HasRemovableSingularity f Ω a`, `HasPole f Ω a`, and
   `HasEssentialSingularity f Ω a` holds, and at least one holds.
2. If `HasPole f Ω a`, then `‖f(z)‖ → ∞` as `z → a` (`z ≠ a`) and the principal part is unique.
3. (Casorati–Weierstrass) `HasEssentialSingularity f Ω a` holds if and only if for every `r > 0`
   with `disc a r ⊆ Ω`, the image `f(D'(a; r))` is dense in `ℂ` (and hence for every `w ∈ ℂ` there
   exists a sequence `z_n ∈ D'(a; r)` with `z_n → a` and `f(z_n) → w`). -/
theorem theorem10_21 {f : ℂ → ℂ} {Ω : Set ℂ} {a : ℂ}
    (hiso : HasIsolatedSingularity f Ω a) :
    (¬ (HasRemovableSingularity f Ω a ∧ HasPole f Ω a)) ∧
    (HasRemovableSingularity f Ω a ∨ HasPole f Ω a ∨ HasEssentialSingularity f Ω a) ∧
    (HasPole f Ω a → Tendsto (fun z => ‖f z‖) (𝓝[≠] a) atTop) ∧
    (HasEssentialSingularity f Ω a ↔
      ∀ r : ℝ, 0 < r → disc a r ⊆ Ω →
        Dense (f '' puncturedDisc a r) ∧
        ∀ w : ℂ, ∃ z_seq : ℕ → ℂ,
          (∀ n : ℕ, z_seq n ∈ puncturedDisc a r) ∧
          Tendsto z_seq atTop (𝓝 a) ∧
          Tendsto (f ∘ z_seq) atTop (𝓝 w)) := by
  rcases hiso with ⟨hΩ, ha, hf_holo⟩
  have hiso' : HasIsolatedSingularity f Ω a := ⟨hΩ, ha, hf_holo⟩
  have hnot_both : ¬ (HasRemovableSingularity f Ω a ∧ HasPole f Ω a) := by
    rintro ⟨⟨g, hg, hgf⟩, hpole⟩
    have htop := tendsto_norm_atTop_of_hasPole hpole
    have hlim : Tendsto (fun z => ‖f z‖) (𝓝[≠] a) (𝓝 ‖g a‖) := by
      have hcongr : (fun z => ‖f z‖) =ᶠ[𝓝[≠] a] fun z => ‖g z‖ := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hΩ.mem_nhds ha)] with z hza hzΩ
        rw [hgf ⟨hzΩ, hza⟩]
      exact ((hg a ha).continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds).congr' hcongr.symm
    exact not_tendsto_nhds_of_tendsto_atTop htop _ hlim
  have htri : HasRemovableSingularity f Ω a ∨ HasPole f Ω a ∨ HasEssentialSingularity f Ω a := by
    by_cases hrem : HasRemovableSingularity f Ω a
    · exact Or.inl hrem
    · by_cases hpole : HasPole f Ω a
      · exact Or.inr (Or.inl hpole)
      · exact Or.inr (Or.inr ⟨hiso', hrem, hpole⟩)
  refine ⟨hnot_both, htri, tendsto_norm_atTop_of_hasPole, ?_⟩
  have hcw_core : ∀ r : ℝ, 0 < r → disc a r ⊆ Ω → ¬ Dense (f '' puncturedDisc a r) →
      HasRemovableSingularity f Ω a ∨ HasPole f Ω a := by
    intro r hr hsub hnot_dense
    rw [Metric.dense_iff] at hnot_dense
    push Not at hnot_dense
    obtain ⟨w, ε, hε, hempty⟩ := hnot_dense
    have hge : ∀ z ∈ puncturedDisc a r, ε ≤ ‖f z - w‖ := by
      intro z hz
      by_contra hlt
      have hmem : f z ∈ Metric.ball w ε ∩ f '' puncturedDisc a r :=
        ⟨by rw [Metric.mem_ball, dist_eq_norm]; exact not_le.mp hlt, ⟨z, hz, rfl⟩⟩
      exact Set.notMem_empty (f z) (hempty ▸ hmem)
    let h : ℂ → ℂ := fun z => (f z - w)⁻¹
    have hh_iso : HasIsolatedSingularity h (disc a r) a := by
      refine ⟨Metric.isOpen_ball, Metric.mem_ball_self hr, fun z hz => ?_⟩
      have hz_punc : z ∈ puncturedDisc a r := hz
      have hne : f z - w ≠ 0 := fun h0 => by
        have := hge z hz_punc; rw [h0, norm_zero] at this; linarith
      exact ((hf_holo z ⟨hsub hz.1, hz.2⟩).sub (differentiableAt_const w)).inv hne
    have hh_bdd : ∃ M : ℝ, ∀ z ∈ puncturedDisc a r, ‖h z‖ ≤ M := by
      refine ⟨ε⁻¹, fun z hz => ?_⟩
      dsimp [h]
      rw [norm_inv]
      exact inv_anti₀ hε (hge z hz)
    obtain ⟨H, hH_holo, hH_eq⟩ := removable_of_bounded hh_iso hr hh_bdd
    have hH_ne_punc : ∀ z ∈ puncturedDisc a r, H z ≠ 0 := by
      intro z hz
      rw [hH_eq hz]
      exact inv_ne_zero fun h0 => by
        have := hge z hz; rw [h0, norm_zero] at this; linarith
    by_cases hHa : H a = 0
    · -- Pole case (`H a = 0`)
      right
      have hH_not_zero : ¬ Set.EqOn H 0 (disc a r) := by
        intro hz0
        let z₁ : ℂ := a + ((r / 2 : ℝ) : ℂ)
        have hz₁_punc : z₁ ∈ puncturedDisc a r := by
          refine ⟨?_, ?_⟩
          · rw [disc, Metric.mem_ball, dist_eq_norm]
            simp only [z₁, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (half_pos hr)]
            linarith
          · intro heq
            rw [Set.mem_singleton_iff] at heq
            dsimp [z₁] at heq
            have : ((r / 2 : ℝ) : ℂ) = 0 := by linear_combination heq
            have : r / 2 = 0 := Complex.ofReal_eq_zero.mp this
            linarith
        exact hH_ne_punc z₁ hz₁_punc (hz0 hz₁_punc.1)
      obtain ⟨m, ⟨hm_pos, g₁, hg₁_holo, hg₁_a, hH_fac⟩, _⟩ :=
        existsUnique_zero_order (disc_isRegion a hr) hH_holo hH_not_zero (Metric.mem_ball_self hr) hHa
      have hg₁_nz : ∀ z ∈ disc a r, g₁ z ≠ 0 := by
        intro z hz
        by_cases hza : z = a
        · exact hza ▸ hg₁_a
        · intro hg0
          have := hH_fac z hz
          rw [hg0, mul_zero] at this
          exact hH_ne_punc z ⟨hz, hza⟩ this
      let u : ℂ → ℂ := fun z => (g₁ z)⁻¹
      have hu_holo : HolomorphicOn u (disc a r) := fun z hz => (hg₁_holo z hz).inv (hg₁_nz z hz)
      obtain ⟨d, R, hR_holo, hd0, hu_exp⟩ :=
        dslope_taylor_expansion Metric.isOpen_ball (Metric.mem_ball_self hr) hu_holo m
      let c : ℕ → ℂ := fun k => d (m - k)
      let Q : ℂ → ℂ := fun z => ∑ k ∈ Finset.Icc 1 m, c k * (z - a)⁻¹ ^ k
      have hQ_pp : IsPrincipalPart Q a := by
        refine ⟨m, c, hm_pos, ?_, fun _ => rfl⟩
        dsimp [c]
        rw [Nat.sub_self, hd0]
        exact inv_ne_zero hg₁_a
      have hQ_holo : HolomorphicOn Q ({a}ᶜ) := by
        intro z hza
        dsimp [Q]
        exact DifferentiableAt.fun_sum fun k _ =>
          (differentiableAt_const _).mul
            (((differentiableAt_id.sub (differentiableAt_const a)).inv (sub_ne_zero.mpr hza)).pow k)
      -- On `puncturedDisc a r`, `f z = w + R z + Q z`
      have hf_on_punc : ∀ z ∈ puncturedDisc a r, f z = (w + R z) + Q z := by
        intro z hz
        have hza : z - a ≠ 0 := sub_ne_zero.mpr hz.2
        have hHz := hH_eq hz
        dsimp [h] at hHz
        have hfw_ne : f z - w ≠ 0 := fun h0 => by
          have := hge z hz; rw [h0, norm_zero] at this; linarith
        have hfw : f z - w = (H z)⁻¹ := by
          rw [hHz, inv_inv]
        have hH_inv : (H z)⁻¹ = (z - a)⁻¹ ^ m * u z := by
          rw [hH_fac z hz.1, mul_inv, inv_pow, mul_comm]
        have hu_div : (z - a)⁻¹ ^ m * u z = Q z + R z := by
          rw [hu_exp z, mul_add]
          have h2 : (z - a)⁻¹ ^ m * ((z - a) ^ m * R z) = R z := by
            rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hza, one_pow, one_mul]
          have h1 : (z - a)⁻¹ ^ m * ∑ j ∈ Finset.range m, d j * (z - a) ^ j = Q z := by
            rw [Finset.mul_sum]
            dsimp [Q, c]
            -- Reindex `j = m - k` via `Finset.sum_nbij (fun j => m - j)`
            refine Finset.sum_nbij (fun j => m - j) ?_ ?_ ?_ ?_
            · intro j hj
              simp only [Finset.mem_range] at hj
              exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            · intro j₁ hj₁ j₂ hj₂ heq
              simp only [Finset.mem_coe, Finset.mem_range] at hj₁ hj₂
              dsimp at heq
              omega
            · intro k hk
              simp only [Finset.mem_coe, Finset.mem_Icc] at hk
              refine ⟨m - k, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), ?_⟩
              dsimp
              omega
            · intro j hj
              simp only [Finset.mem_range] at hj
              have hsub_sub : m - (m - j) = j := by omega
              rw [hsub_sub]
              have hpow : (z - a)⁻¹ ^ m * (z - a) ^ j = (z - a)⁻¹ ^ (m - j) := by
                have hm_eq : m = (m - j) + j := by omega
                conv_lhs => rw [hm_eq, pow_add]
                rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hza, one_pow, mul_one]
              linear_combination d j * hpow
          rw [h1, h2, add_comm]
        linear_combination hfw + hH_inv + hu_div
      let g : ℂ → ℂ := Function.update (fun z => f z - Q z) a (w + R a)
      have hg_diff_sdiff : DifferentiableOn ℂ g (Ω \ {a}) := by
        intro z hz
        have hev : g =ᶠ[𝓝 z] fun ζ => f ζ - Q ζ := by
          filter_upwards [isOpen_ne.mem_nhds hz.2] with ζ hζ
          exact Function.update_of_ne hζ _ _
        exact (((hf_holo z hz).sub (hQ_holo z hz.2)).congr_of_eventuallyEq hev).differentiableWithinAt
      have hg_cont_a : ContinuousAt g a := by
        rw [continuousAt_update_same]
        have hev : (fun z => f z - Q z) =ᶠ[𝓝[≠] a] fun z => w + R z := by
          filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds a hr)]
            with z hza hzr
          have := hf_on_punc z ⟨hzr, hza⟩
          linear_combination this
        exact ((continuousAt_const.add (hR_holo a (Metric.mem_ball_self hr)).continuousAt).tendsto.mono_left
          nhdsWithin_le_nhds).congr' hev.symm
      have hg_diff : DifferentiableOn ℂ g Ω :=
        (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (hΩ.mem_nhds ha)).mp
          ⟨hg_diff_sdiff, hg_cont_a⟩
      refine ⟨hiso', ⟨g, Q, (holomorphicOn_iff_differentiableOn hΩ).mpr hg_diff, hQ_pp, ?_⟩⟩
      intro z hz
      dsimp [g]
      rw [Function.update_of_ne hz.2]
      ring
    · -- Removable case (`H a ≠ 0`)
      left
      let g : ℂ → ℂ := Function.update f a (w + (H a)⁻¹)
      have hg_diff_sdiff : DifferentiableOn ℂ g (Ω \ {a}) := by
        intro z hz
        have hev : g =ᶠ[𝓝 z] f := by
          filter_upwards [isOpen_ne.mem_nhds hz.2] with ζ hζ
          exact Function.update_of_ne hζ _ _
        exact ((hf_holo z hz).congr_of_eventuallyEq hev).differentiableWithinAt
      have hg_cont_a : ContinuousAt g a := by
        rw [continuousAt_update_same]
        have hev : f =ᶠ[𝓝[≠] a] fun z => w + (H z)⁻¹ := by
          filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds a hr)]
            with z hza hzr
          have hHz := hH_eq ⟨hzr, hza⟩
          dsimp [h] at hHz
          have hfw : f z - w = (H z)⁻¹ := by rw [hHz, inv_inv]
          linear_combination hfw
        exact ((continuousAt_const.add
          ((hH_holo a (Metric.mem_ball_self hr)).continuousAt.inv₀ hHa)).tendsto.mono_left
          nhdsWithin_le_nhds).congr' hev.symm
      have hg_diff : DifferentiableOn ℂ g Ω :=
        (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (hΩ.mem_nhds ha)).mp
          ⟨hg_diff_sdiff, hg_cont_a⟩
      exact ⟨g, (holomorphicOn_iff_differentiableOn hΩ).mpr hg_diff,
        fun z hz => Function.update_of_ne hz.2 _ _⟩
  constructor
  · intro ⟨_, hnot_rem, hnot_pole⟩ r hr hsub
    have hdense_all : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → Dense (f '' puncturedDisc a ρ) := by
      intro ρ hρ hρr
      by_contra hnd
      rcases hcw_core ρ hρ ((Metric.ball_subset_ball hρr).trans hsub) hnd with hrem | hpole
      · exact hnot_rem hrem
      · exact hnot_pole hpole
    refine ⟨hdense_all r hr le_rfl, fun w => ?_⟩
    have hchoice : ∀ n : ℕ, ∃ z ∈ puncturedDisc a (r / (n + 1 : ℝ)),
        dist (f z) w < 1 / (n + 1 : ℝ) := by
      intro n
      have hn_pos : (0 : ℝ) < n + 1 := Nat.cast_add_one_pos n
      have hρ_pos : 0 < r / (n + 1 : ℝ) := div_pos hr hn_pos
      have hρ_le : r / (n + 1 : ℝ) ≤ r := div_le_self hr.le (by exact_mod_cast Nat.le_add_left 1 n)
      have hd := Metric.dense_iff.mp (hdense_all (r / (n + 1 : ℝ)) hρ_pos hρ_le)
        w (1 / (n + 1 : ℝ)) (div_pos zero_lt_one hn_pos)
      obtain ⟨_, hball, z, hz, rfl⟩ := hd
      exact ⟨z, hz, by rwa [Metric.mem_ball] at hball⟩
    choose z_seq hz_punc hdist_f using hchoice
    refine ⟨z_seq, fun n => ?_, ?_, ?_⟩
    · have hρ_le : r / (n + 1 : ℝ) ≤ r := div_le_self hr.le (by exact_mod_cast Nat.le_add_left 1 n)
      exact ⟨Metric.ball_subset_ball hρ_le (hz_punc n).1, (hz_punc n).2⟩
    · rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (r / ε)
      refine ⟨N, fun n hn => ?_⟩
      have hn_pos : (0 : ℝ) < n + 1 := Nat.cast_add_one_pos n
      have hr_lt : r / (n + 1 : ℝ) < ε := by
        rw [div_lt_iff₀ hn_pos]
        have := (div_lt_iff₀ hε).mp hN
        have hNn : (N : ℝ) < n + 1 := by exact_mod_cast Nat.lt_succ_of_le hn
        nlinarith
      exact lt_trans (hz_punc n).1 hr_lt
    · rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      refine ⟨N, fun n hn => ?_⟩
      have hn_pos : (0 : ℝ) < n + 1 := Nat.cast_add_one_pos n
      have h1_lt : 1 / (n + 1 : ℝ) < ε := by
        rw [div_lt_iff₀ hn_pos]
        have := (div_lt_iff₀ hε).mp hN
        have hNn : (N : ℝ) < n + 1 := by exact_mod_cast Nat.lt_succ_of_le hn
        nlinarith
      exact lt_trans (hdist_f n) h1_lt
  · intro hall
    obtain ⟨r₀, hr₀, hsub₀⟩ := Metric.isOpen_iff.mp hΩ a ha
    refine ⟨hiso', ?_, ?_⟩
    · rintro ⟨g, hg, hgf⟩
      let ρ := r₀ / 2
      have hρ_pos : 0 < ρ := half_pos hr₀
      have hcl_sub : Metric.closedBall a ρ ⊆ Ω :=
        (Metric.closedBall_subset_ball (half_lt_self hr₀)).trans hsub₀
      obtain ⟨M, hM⟩ := ((isCompact_closedBall a ρ).image_of_continuousOn
        ((continuousOn_of_holomorphicOn hg).mono hcl_sub)).isBounded.subset_closedBall 0
      have hd := (hall ρ hρ_pos ((Metric.ball_subset_closedBall).trans hcl_sub)).1
      let w₀ : ℂ := ((max M 0 + 2 : ℝ) : ℂ)
      obtain ⟨_, hball, z, hz, rfl⟩ := Metric.dense_iff.mp hd w₀ 1 zero_lt_one
      have hfz_le : ‖f z‖ ≤ M := by
        rw [← hgf ⟨hcl_sub (Metric.ball_subset_closedBall hz.1), hz.2⟩]
        simpa [Metric.mem_closedBall, dist_eq_norm] using
          hM ⟨z, Metric.ball_subset_closedBall hz.1, rfl⟩
      rw [Metric.mem_ball, dist_eq_norm] at hball
      have htri_norm : ‖w₀‖ ≤ ‖f z - w₀‖ + ‖f z‖ := by
        calc ‖w₀‖ = ‖(w₀ - f z) + f z‖ := by abel_nf
          _ ≤ ‖w₀ - f z‖ + ‖f z‖ := norm_add_le _ _
          _ = ‖f z - w₀‖ + ‖f z‖ := by rw [norm_sub_rev]
      have hnorm_rhs : ‖w₀‖ = max M 0 + 2 := by
        dsimp [w₀]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [le_max_right M 0])]
      rw [hnorm_rhs] at htri_norm
      linarith [le_max_left M 0]
    · intro hpole
      have htop := tendsto_norm_atTop_of_hasPole hpole
      obtain ⟨δ, hδ, hge1⟩ := Metric.mem_nhdsWithin_iff.mp (Filter.tendsto_atTop.mp htop 1)
      let ρ := min r₀ δ
      have hρ_pos : 0 < ρ := lt_min hr₀ hδ
      have hd := (hall ρ hρ_pos ((Metric.ball_subset_ball (min_le_left _ _)).trans hsub₀)).1
      obtain ⟨_, hball, z, hz, rfl⟩ := Metric.dense_iff.mp hd 0 (1 / 2) (by norm_num)
      have hz_ge : 1 ≤ ‖f z‖ := hge1 ⟨Metric.ball_subset_ball (min_le_right _ _) hz.1, hz.2⟩
      rw [Metric.mem_ball, dist_zero_right] at hball
      linarith

/-- Helper for 10.22: orthogonality of `θ ↦ exp(i k θ)` on `[0, 2π]`. -/
private theorem integral_exp_int_mul_I (k : ℤ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp ((k : ℂ) * θ * Complex.I)) =
      if k = 0 then (2 * Real.pi : ℂ) else 0 := by
  split_ifs with hk0
  · subst hk0
    simp [intervalIntegral.integral_const, mul_comm]
  · have hkc : (k : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hk0) Complex.I_ne_zero
    let F : ℝ → ℂ := fun θ => ((k : ℂ) * Complex.I)⁻¹ * Complex.exp ((k : ℂ) * θ * Complex.I)
    have hF_deriv : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
        HasDerivAt F (Complex.exp ((k : ℂ) * θ * Complex.I)) θ := by
      intro θ _
      have hd_unit : HasDerivAt (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I))
          (Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) * Complex.I) ((k : ℝ) * θ) := by
        have h1 := hasDerivAt_circleMap 0 1 ((k : ℝ) * θ)
        have hfn : circleMap 0 1 = fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I) := by
          ext x; simp [circleMap]
        rw [hfn] at h1
        dsimp only at h1
        push_cast at h1
        exact h1
      have hd_comp := (hd_unit.scomp θ ((hasDerivAt_id θ).const_mul (k : ℝ))).const_mul
        (((k : ℂ) * Complex.I)⁻¹)
      convert hd_comp using 1
      · ext t
        dsimp [F]
        push_cast
        rfl
      · rw [mul_one, Complex.real_smul]
        push_cast
        calc Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)
            = (((k : ℂ) * Complex.I)⁻¹ * ((k : ℂ) * Complex.I)) *
                Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) := by rw [inv_mul_cancel₀ hkc, one_mul]
          _ = ((k : ℂ) * Complex.I)⁻¹ *
                ((k : ℂ) * (Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) * Complex.I)) := by ring
    have hint : IntervalIntegrable (fun θ : ℝ => Complex.exp ((k : ℂ) * θ * Complex.I))
        MeasureTheory.volume 0 (2 * Real.pi) :=
      (Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv hint]
    dsimp [F]
    have hper : Complex.exp ((k : ℂ) * ((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
      have : (k : ℂ) * ((2 * Real.pi : ℝ) : ℂ) * Complex.I =
          (k : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [hper]
    simp

/-- 10.22 (Parseval's identity for power series on smaller circles): suppose
`f(z) = ∑_{n=0}^∞ c_n (z - a)^n` converges for `z ∈ D(a; R)` (`R > 0`). If `0 < r < R`, then
`∑_{n=0}^∞ |c_n|^2 r^{2n} = (2π)⁻¹ ∫_0^{2π} |f(a + r e^{iθ})|^2 dθ`. -/
theorem theorem10_22 {f : ℂ → ℂ} {c : ℕ → ℂ} {a : ℂ} {R r : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hc : ∀ z ∈ disc a R, HasSum (fun n : ℕ => c n * (z - a) ^ n) (f z)) :
    HasSum (fun n : ℕ => ‖c n‖ ^ 2 * r ^ (2 * n))
      ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap a r θ)‖ ^ 2) ∧
    (∑' n : ℕ, ‖c n‖ ^ 2 * r ^ (2 * n)) =
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap a r θ)‖ ^ 2 := by
  let z₁ : ℂ := a + (((r + R) / 2 : ℝ) : ℂ)
  have hr₁_pos : 0 < (r + R) / 2 := by linarith
  have hz₁_disc : z₁ ∈ disc a R := by
    rw [disc, Metric.mem_ball, dist_eq_norm]
    simp only [z₁, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₁_pos]
    linarith
  have hrad_ge : ENNReal.ofReal ((r + R) / 2) ≤ powerSeriesRadius c := by
    by_contra hgt
    have hlt : powerSeriesRadius c < ‖z₁ - a‖ₑ := by
      have hnorm : ‖z₁ - a‖ = (r + R) / 2 := by
        simp only [z₁, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₁_pos]
      rw [← ofReal_norm, hnorm]
      exact not_le.mp hgt
    exact (theorem10_5 c a).2.2 z₁ hlt (hc z₁ hz₁_disc).summable
  have hr_lt_rad : ENNReal.ofReal r < powerSeriesRadius c :=
    lt_of_lt_of_le (ENNReal.ofReal_lt_ofReal_iff hr₁_pos |>.mpr (by linarith)) hrad_ge
  have hunif_ball := (theorem10_5 c a).1 r hr hr_lt_rad |>.2.2
  let S : ℕ → ℝ → ℂ := fun N θ => ∑ n ∈ Finset.range N, c n * (circleMap a r θ - a) ^ n
  let g : ℝ → ℂ := fun θ => f (circleMap a r θ)
  have hS_cont : ∀ N : ℕ, Continuous (S N) := fun N =>
    continuous_finsetSum _ fun n _ =>
      continuous_const.mul (((continuous_circleMap a r).sub continuous_const).pow n)
  have hg_eq_tsum : ∀ θ : ℝ, g θ = ∑' n : ℕ, c n * (circleMap a r θ - a) ^ n := fun θ => by
    have hmem : circleMap a r θ ∈ disc a R := by
      rw [disc, Metric.mem_ball]
      have hsp : dist (circleMap a r θ) a = r := circleMap_mem_sphere a hr.le θ
      linarith
    exact (hc _ hmem).tsum_eq.symm
  have hunif_θ : TendstoUniformlyOn S g atTop (Icc 0 (2 * Real.pi)) := by
    rw [Metric.tendstoUniformlyOn_iff] at hunif_ball ⊢
    intro ε hε
    filter_upwards [hunif_ball ε hε] with N hN θ _
    rw [hg_eq_tsum θ]
    exact hN (circleMap a r θ)
      ((closedDisc_eq_closedBall a hr).symm ▸
        Metric.sphere_subset_closedBall (circleMap_mem_sphere a hr.le θ))
  have hg_cont : ContinuousOn g (Icc 0 (2 * Real.pi)) :=
    hunif_θ.continuousOn (Filter.Frequently.of_forall fun N => (hS_cont N).continuousOn)
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hg_cont.norm).isBounded.subset_closedBall 0
  have hM_bound : ∀ θ ∈ Icc 0 (2 * Real.pi), ‖g θ‖ ≤ max M 0 := fun θ hθ => by
    have hm : ‖g θ‖ ≤ M := by
      simpa [Metric.mem_closedBall, dist_eq_norm, abs_of_nonneg (norm_nonneg _)] using
        hM ⟨θ, hθ, rfl⟩
    exact le_trans hm (le_max_left M 0)
  have hunif_sq : TendstoUniformlyOn (fun N θ => ‖S N θ‖ ^ 2) (fun θ => ‖g θ‖ ^ 2)
      atTop (Icc 0 (2 * Real.pi)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    let C : ℝ := 2 * max M 0 + 1
    have hC_pos : 0 < C := by positivity
    let δ : ℝ := min 1 (ε / C)
    have hδ_pos : 0 < δ := lt_min zero_lt_one (div_pos hε hC_pos)
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif_θ δ hδ_pos] with N hN θ hθ
    have hd : ‖S N θ - g θ‖ < δ := by simpa [dist_eq_norm, norm_sub_rev] using hN θ hθ
    have hSN_le : ‖S N θ‖ ≤ max M 0 + 1 := by
      have htri : ‖S N θ‖ ≤ ‖S N θ - g θ‖ + ‖g θ‖ := by
        calc ‖S N θ‖ = ‖(S N θ - g θ) + g θ‖ := by abel_nf
          _ ≤ ‖S N θ - g θ‖ + ‖g θ‖ := norm_add_le _ _
      linarith [hM_bound θ hθ, min_le_left 1 (ε / C)]
    rw [Real.dist_eq]
    have hdiff_sq : |‖S N θ‖ ^ 2 - ‖g θ‖ ^ 2| ≤ ‖S N θ - g θ‖ * (‖S N θ‖ + ‖g θ‖) := by
      have h1 : |‖S N θ‖ - ‖g θ‖| ≤ ‖S N θ - g θ‖ := abs_norm_sub_norm_le _ _
      have h2 : |‖S N θ‖ ^ 2 - ‖g θ‖ ^ 2| = |‖S N θ‖ - ‖g θ‖| * (‖S N θ‖ + ‖g θ‖) := by
        rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity), mul_comm]
      rw [h2]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    calc |‖g θ‖ ^ 2 - ‖S N θ‖ ^ 2|
        = |‖S N θ‖ ^ 2 - ‖g θ‖ ^ 2| := abs_sub_comm _ _
      _ ≤ ‖S N θ - g θ‖ * (‖S N θ‖ + ‖g θ‖) := hdiff_sq
      _ ≤ ‖S N θ - g θ‖ * C := by
        gcongr
        dsimp [C]
        linarith [hM_bound θ hθ]
      _ < δ * C := mul_lt_mul_of_pos_right hd hC_pos
      _ ≤ (ε / C) * C := mul_le_mul_of_nonneg_right (min_le_right _ _) hC_pos.le
      _ = ε := div_mul_cancel₀ ε hC_pos.ne'
  have hpartial_eq : ∀ N : ℕ,
      (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2 * Real.pi, ‖S N θ‖ ^ 2) =
        ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 * r ^ (2 * n) := by
    intro N
    have hC_id : (∫ θ in (0 : ℝ)..2 * Real.pi, ((‖S N θ‖ ^ 2 : ℝ) : ℂ)) =
        ((2 * Real.pi * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 * r ^ (2 * n) : ℝ) : ℂ) := by
      have hpt : ∀ θ : ℝ, ((‖S N θ‖ ^ 2 : ℝ) : ℂ) =
          ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
            (c n * (starRingEnd ℂ) (c m) * ((r : ℂ) ^ (n + m))) *
              Complex.exp ((((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * θ * Complex.I) := by
        intro θ
        have hsq : ((‖S N θ‖ ^ 2 : ℝ) : ℂ) = S N θ * (starRingEnd ℂ) (S N θ) := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        rw [hsq]
        dsimp [S]
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        have hcm : circleMap a r θ - a = (r : ℂ) * Complex.exp (θ * Complex.I) := by
          simp [circleMap]
        rw [hcm, map_mul, map_pow, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
          mul_pow, mul_pow]
        have hconj_I : (starRingEnd ℂ) ((θ : ℂ) * Complex.I) = -((θ : ℂ) * Complex.I) := by simp
        rw [hconj_I, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
        have hexp_prod : Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I)) *
            Complex.exp ((m : ℂ) * -((θ : ℂ) * Complex.I)) =
            Complex.exp ((((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * θ * Complex.I) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        calc c n * ((r : ℂ) ^ n * Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I))) *
              ((starRingEnd ℂ) (c m) * ((r : ℂ) ^ m * Complex.exp ((m : ℂ) * -((θ : ℂ) * Complex.I))))
            = c n * (starRingEnd ℂ) (c m) * ((r : ℂ) ^ n * (r : ℂ) ^ m) *
                (Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I)) *
                  Complex.exp ((m : ℂ) * -((θ : ℂ) * Complex.I))) := by ring
          _ = c n * (starRingEnd ℂ) (c m) * (r : ℂ) ^ (n + m) *
                Complex.exp ((((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * θ * Complex.I) := by
              rw [← pow_add, hexp_prod]
      have hterm_int : ∀ (n m : ℕ), IntervalIntegrable
          (fun θ : ℝ => (c n * (starRingEnd ℂ) (c m) * ((r : ℂ) ^ (n + m))) *
            Complex.exp ((((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * θ * Complex.I))
          MeasureTheory.volume 0 (2 * Real.pi) := fun n m =>
        ((Complex.continuous_exp.comp
          ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).const_mul _).intervalIntegrable _ _
      simp_rw [hpt]
      rw [intervalIntegral.integral_finsetSum]
      · have hinner : ∀ n ∈ Finset.range N,
            (∫ θ in (0 : ℝ)..2 * Real.pi, ∑ m ∈ Finset.range N,
              (c n * (starRingEnd ℂ) (c m) * ((r : ℂ) ^ (n + m))) *
                Complex.exp ((((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * θ * Complex.I)) =
              ((2 * Real.pi * (‖c n‖ ^ 2 * r ^ (2 * n)) : ℝ) : ℂ) := by
          intro n hn
          rw [intervalIntegral.integral_finsetSum (fun m _ => hterm_int n m)]
          simp_rw [intervalIntegral.integral_const_mul, integral_exp_int_mul_I]
          rw [Finset.sum_eq_single n]
          · simp only [sub_self, ↓reduceIte]
            have hcc : c n * (starRingEnd ℂ) (c n) = ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
              rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
            have hr_eq : (r : ℂ) ^ (n + n) = ((r ^ (2 * n) : ℝ) : ℂ) := by
              rw [← two_mul, Complex.ofReal_pow]
            calc c n * (starRingEnd ℂ) (c n) * (r : ℂ) ^ (n + n) * (2 * Real.pi : ℂ)
                = (c n * (starRingEnd ℂ) (c n)) * (r : ℂ) ^ (n + n) * (2 * Real.pi : ℂ) := by ring
              _ = ((2 * Real.pi * (‖c n‖ ^ 2 * r ^ (2 * n)) : ℝ) : ℂ) := by
                rw [hcc, hr_eq]
                push_cast
                ring
          · intro m _ hmn
            have hsub_ne : (n : ℤ) - (m : ℤ) ≠ 0 :=
              sub_ne_zero.mpr (Int.ofNat_inj.not.mpr hmn.symm)
            simp [hsub_ne]
          · intro hnot
            exact (hnot hn).elim
        rw [Finset.sum_congr rfl hinner]
        push_cast
        rw [Finset.mul_sum]
      · intro n _
        exact ((continuous_finsetSum _ fun m _ =>
          ((Complex.continuous_exp.comp
            ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).const_mul _))).intervalIntegrable _ _
    have hcont_re : IntervalIntegrable (fun θ : ℝ => ‖S N θ‖ ^ 2) MeasureTheory.volume 0 (2 * Real.pi) :=
      (((hS_cont N).norm).pow 2).intervalIntegrable _ _
    have hofReal : (∫ θ in (0 : ℝ)..2 * Real.pi, ((‖S N θ‖ ^ 2 : ℝ) : ℂ)) =
        ((∫ θ in (0 : ℝ)..2 * Real.pi, ‖S N θ‖ ^ 2 : ℝ) : ℂ) := by
      simpa using (Complex.ofRealCLM.intervalIntegral_comp_comm hcont_re)
    rw [hofReal] at hC_id
    have hreal := Complex.ofReal_injective hC_id
    rw [hreal, inv_mul_cancel_left₀ Real.two_pi_pos.ne']
  have hint_tendsto : Tendsto (fun N : ℕ => ∫ θ in (0 : ℝ)..2 * Real.pi, ‖S N θ‖ ^ 2)
      atTop (𝓝 (∫ θ in (0 : ℝ)..2 * Real.pi, ‖g θ‖ ^ 2)) := by
    refine TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn ?_ ?_
    · exact Filter.Eventually.of_forall fun N => (((hS_cont N).norm).pow 2).continuousOn
    · rwa [Set.uIcc_of_le Real.two_pi_pos.le]
  have hsum_tendsto : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 * r ^ (2 * n))
      atTop (𝓝 ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖g θ‖ ^ 2)) := by
    have h := hint_tendsto.const_mul (2 * Real.pi)⁻¹
    simpa only [hpartial_eq] using h
  have hhasSum : HasSum (fun n : ℕ => ‖c n‖ ^ 2 * r ^ (2 * n))
      ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖g θ‖ ^ 2) :=
    (hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity) _).mpr hsum_tendsto
  exact ⟨hhasSum, hhasSum.tsum_eq⟩

end BatchB

/-! ### 10.30–10.33: Holomorphic inverse function theorem, positive power maps, local normal form & open mapping theorem, and injective holomorphic functions -/

section BatchC

/-- 10.30 (Holomorphic inverse function theorem): suppose `f ∈ H(Ω)` on an open set `Ω`, `z₀ ∈ Ω`,
and `f'(z₀) ≠ 0`. Then `Ω` contains an open neighborhood `U` of `z₀` on which `f` is one-to-one,
`V = f '' U` is an open neighborhood of `f(z₀)`, and the inverse `g : ℂ → ℂ` on `V` is holomorphic
with `g'(f z) = (f'(z))⁻¹` for all `z ∈ U`. -/
theorem theorem10_30 {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} (hf : HolomorphicOn f Ω)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hdf₀ : deriv f z₀ ≠ 0) :
    ∃ (U V : Set ℂ) (g : ℂ → ℂ),
      IsOpen U ∧ z₀ ∈ U ∧ U ⊆ Ω ∧
      IsOpen V ∧ f z₀ ∈ V ∧
      Set.BijOn f U V ∧
      HolomorphicOn g V ∧
      (∀ z ∈ U, deriv f z ≠ 0) ∧
      (∀ z ∈ U, g (f z) = z) ∧
      (∀ w ∈ V, g w ∈ U ∧ f (g w) = w) ∧
      (∀ z ∈ U, HasDerivAt g (deriv f z)⁻¹ (f z) ∧ deriv g (f z) = (deriv f z)⁻¹) := by
  have hana : AnalyticOnNhd ℂ f Ω :=
    ((holomorphicOn_iff_differentiableOn hΩ).mp hf).analyticOnNhd hΩ
  have hdf_cont : ContinuousOn (deriv f) Ω :=
    continuousOn_of_holomorphicOn (holomorphicOn_deriv hΩ hf)
  let U₀ : Set ℂ := {z ∈ Ω | deriv f z ≠ 0}
  have hU₀_open : IsOpen U₀ := hdf_cont.isOpen_inter_preimage hΩ isOpen_ne
  have hz₀_U₀ : z₀ ∈ U₀ := ⟨hz₀, hdf₀⟩
  have hstrict₀ : HasStrictDerivAt f (deriv f z₀) z₀ := (hana z₀ hz₀).hasStrictDerivAt
  let e := (hstrict₀.hasStrictFDerivAt_equiv hdf₀).toOpenPartialHomeomorph f
  have he_coe : (e : ℂ → ℂ) = f := rfl
  let U : Set ℂ := e.source ∩ U₀
  have hU_open : IsOpen U := e.open_source.inter hU₀_open
  have hz₀_U : z₀ ∈ U :=
    ⟨(hstrict₀.hasStrictFDerivAt_equiv hdf₀).mem_toOpenPartialHomeomorph_source, hz₀_U₀⟩
  have hU_sub : U ⊆ Ω := fun _ hz => hz.2.1
  let g : ℂ → ℂ := e.symm
  let V : Set ℂ := e.target ∩ g ⁻¹' U
  have hV_open : IsOpen V := e.continuousOn_invFun.isOpen_inter_preimage e.open_target hU_open
  have hleft : ∀ z ∈ U, g (f z) = z := fun z hz => e.left_inv hz.1
  have hmaps : Set.MapsTo f U V := fun z hz =>
    ⟨e.map_source hz.1, by rw [Set.mem_preimage, hleft z hz]; exact hz⟩
  have hright : ∀ w ∈ V, g w ∈ U ∧ f (g w) = w := fun w hw => ⟨hw.2, e.right_inv hw.1⟩
  have hbij : Set.BijOn f U V := by
    refine ⟨hmaps, ?_, ?_⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      rw [← hleft z₁ hz₁, ← hleft z₂ hz₂, heq]
    · intro w hw
      exact ⟨g w, hw.2, (hright w hw).2⟩
  have hfz₀_V : f z₀ ∈ V := hmaps hz₀_U
  have hderiv_inv : ∀ z ∈ U, HasDerivAt g (deriv f z)⁻¹ (f z) ∧ deriv g (f z) = (deriv f z)⁻¹ := by
    intro z hz
    have hstr : HasStrictDerivAt f (deriv f z) z := (hana z hz.2.1).hasStrictDerivAt
    have hev_left : ∀ᶠ ζ in 𝓝 z, g (f ζ) = ζ :=
      Filter.mem_of_superset (hU_open.mem_nhds hz) hleft
    have hinv_str : HasStrictDerivAt g (deriv f z)⁻¹ (f z) :=
      hstr.to_local_left_inverse hz.2.2 hev_left
    exact ⟨hinv_str.hasDerivAt, hinv_str.hasDerivAt.deriv⟩
  have hg_holo : HolomorphicOn g V := by
    intro w hw
    obtain ⟨z, hzU, rfl⟩ := hbij.surjOn hw
    exact (hderiv_inv z hzU).1.differentiableAt
  exact ⟨U, V, g, hU_open, hz₀_U, hU_sub, hV_open, hfz₀_V, hbij, hg_holo,
    fun _ hz => hz.2.2, hleft, hright, hderiv_inv⟩

/-- 10.31: explicit `k`-th polar `m`-th root of `w : ℂ`:
`ζ_k = |w|^{1/m} exp(i (arg w + 2π k) / m)`. -/
noncomputable def polarNthRoot (m : ℕ) (w : ℂ) (k : Fin m) : ℂ :=
  ((‖w‖ ^ (1 / (m : ℝ)) : ℝ) : ℂ) *
    Complex.exp ((((Complex.arg w + 2 * Real.pi * (k : ℝ)) / (m : ℝ) : ℝ) : ℂ) * Complex.I)

/-- 10.31 (Positive power map `z ↦ z^m`, `m ≥ 1`):
1. For every `w ≠ 0`, `polarNthRoot m w : Fin m → ℂ` enumerates `m` distinct solutions of `z^m = w`,
   and `{z : ℂ | z ^ m = w} = Set.range (polarNthRoot m w)` (hence finite of cardinality `m`).
2. `z ↦ z^m` is an open map `ℂ → ℂ`.
3. For every `r > 0`, `(· ^ m) '' D(0; r) = D(0; r^m)`. -/
theorem theorem10_31 {m : ℕ} (hm : 0 < m) :
    (∀ w : ℂ, w ≠ 0 →
      Function.Injective (polarNthRoot m w) ∧
      (∀ k : Fin m, polarNthRoot m w k ^ m = w) ∧
      {z : ℂ | z ^ m = w} = Set.range (polarNthRoot m w) ∧
      {z : ℂ | z ^ m = w}.Finite ∧
      {z : ℂ | z ^ m = w}.ncard = m) ∧
    IsOpenMap (fun z : ℂ => z ^ m) ∧
    (∀ r : ℝ, 0 < r → (fun z : ℂ => z ^ m) '' disc 0 r = disc 0 (r ^ m)) := by
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hm_real_ne : (m : ℝ) ≠ 0 := hm_real_pos.ne'
  have hm_complex_ne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hroots : ∀ w : ℂ, w ≠ 0 →
      Function.Injective (polarNthRoot m w) ∧
      (∀ k : Fin m, polarNthRoot m w k ^ m = w) ∧
      {z : ℂ | z ^ m = w} = Set.range (polarNthRoot m w) ∧
      {z : ℂ | z ^ m = w}.Finite ∧
      {z : ℂ | z ^ m = w}.ncard = m := by
    intro w hw
    have hw_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hrad_pos : 0 < ‖w‖ ^ (1 / (m : ℝ)) := Real.rpow_pos_of_pos hw_norm_pos _
    have hrad_ne : ((‖w‖ ^ (1 / (m : ℝ)) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrad_pos.ne'
    have hpow : ∀ k : Fin m, polarNthRoot m w k ^ m = w := by
      intro k
      dsimp [polarNthRoot]
      rw [mul_pow, ← Complex.ofReal_pow, ← Real.rpow_natCast,
        ← Real.rpow_mul (norm_nonneg w), one_div_mul_cancel hm_real_ne, Real.rpow_one,
        ← Complex.exp_nat_mul]
      have hexp_arg : (m : ℂ) *
          ((((Complex.arg w + 2 * Real.pi * (k : ℝ)) / (m : ℝ) : ℝ) : ℂ) * Complex.I) =
          (Complex.arg w : ℂ) * Complex.I + (k.val : ℤ) * (2 * Real.pi * Complex.I) := by
        push_cast
        field_simp [hm_complex_ne]
      rw [hexp_arg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      exact Complex.norm_mul_exp_arg_mul_I w
    have hinj : Function.Injective (polarNthRoot m w) := by
      intro j k hjk
      dsimp [polarNthRoot] at hjk
      have hexp_eq := mul_left_cancel₀ hrad_ne hjk
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp_eq
      -- Take imaginary parts (or cancel `I`) to get a real identity!
      have him := congr_arg Complex.im hn
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_one, mul_zero, add_zero, Complex.add_im, Complex.intCast_re, Complex.intCast_im,
        zero_mul] at him
      -- Wait: `(n : ℂ) * (2 * Real.pi * Complex.I)` has `im` equal to `(n : ℝ) * (2 * Real.pi)`
      have him' : (Complex.arg w + 2 * Real.pi * (j : ℝ)) / (m : ℝ) =
          (Complex.arg w + 2 * Real.pi * (k : ℝ)) / (m : ℝ) + (n : ℝ) * (2 * Real.pi) := by
        have h1 : (((((Complex.arg w + 2 * Real.pi * (j : ℝ)) / (m : ℝ) : ℝ) : ℂ) * Complex.I)).im =
            (Complex.arg w + 2 * Real.pi * (j : ℝ)) / (m : ℝ) := by simp
        have h2 : (((((Complex.arg w + 2 * Real.pi * (k : ℝ)) / (m : ℝ) : ℝ) : ℂ) * Complex.I) +
            (n : ℂ) * (2 * Real.pi * Complex.I)).im =
            (Complex.arg w + 2 * Real.pi * (k : ℝ)) / (m : ℝ) + (n : ℝ) * (2 * Real.pi) := by
          have : (n : ℂ) * (2 * Real.pi * Complex.I) = (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
            push_cast; ring
          rw [this]
          simp
        rw [← h1, hn, h2]
      have hdiff : 2 * Real.pi * ((j : ℝ) - (k : ℝ)) = 2 * Real.pi * ((n : ℝ) * (m : ℝ)) := by
        have hmul := congr_arg (· * (m : ℝ)) him'
        rw [div_mul_cancel₀ _ hm_real_ne, add_mul, div_mul_cancel₀ _ hm_real_ne] at hmul
        linarith
      have hjk_real : (j : ℝ) - (k : ℝ) = (n : ℝ) * (m : ℝ) :=
        mul_left_cancel₀ Real.two_pi_pos.ne' hdiff
      have hj_lt : (j : ℝ) < (m : ℝ) := Nat.cast_lt.mpr j.isLt
      have hk_lt : (k : ℝ) < (m : ℝ) := Nat.cast_lt.mpr k.isLt
      have hj_nn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hn0 : n = 0 := by
        by_contra hne0
        rcases lt_or_gt_of_ne hne0 with hneg | hpos
        · have hn_le : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
          nlinarith
        · have hn_ge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hpos
          nlinarith
      subst hn0
      simp only [Int.cast_zero, zero_mul, sub_eq_zero] at hjk_real
      exact Fin.ext (Nat.cast_injective hjk_real)
    -- Use degree bound of `X^m - C w` to conclude `{z | z^m = w} = Set.range (polarNthRoot m w)`
    let P : Polynomial ℂ := Polynomial.X ^ m - Polynomial.C w
    have hdeg : P.natDegree = m := Polynomial.natDegree_X_pow_sub_C
    have hP_ne : P ≠ 0 := fun h0 => by
      rw [h0, Polynomial.natDegree_zero] at hdeg
      omega
    let imgFinset : Finset ℂ := Finset.univ.image (polarNthRoot m w)
    have hsub_roots : imgFinset ⊆ P.roots.toFinset := by
      intro z hz
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP_ne, Polynomial.IsRoot.def]
      simp [P, hpow k]
    have hcard_img : imgFinset.card = m := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
    have hcard_roots : P.roots.toFinset.card ≤ m :=
      (Multiset.toFinset_card_le P.roots).trans ((Polynomial.card_roots' P).trans_eq hdeg)
    have hfinset_eq : imgFinset = P.roots.toFinset :=
      Finset.eq_of_subset_of_card_le hsub_roots (hcard_roots.trans_eq hcard_img.symm)
    have hset_eq : {z : ℂ | z ^ m = w} = Set.range (polarNthRoot m w) := by
      ext z
      have hmem_P : z ^ m = w ↔ z ∈ P.roots.toFinset := by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hP_ne, Polynomial.IsRoot.def]
        simp [P, sub_eq_zero]
      have hmem_img : z ∈ imgFinset ↔ z ∈ Set.range (polarNthRoot m w) := by
        simp [imgFinset]
      change z ^ m = w ↔ z ∈ Set.range (polarNthRoot m w)
      rw [hmem_P, ← hfinset_eq, hmem_img]
    have hfin : {z : ℂ | z ^ m = w}.Finite := hset_eq ▸ Set.finite_range (polarNthRoot m w)
    have hncard : {z : ℂ | z ^ m = w}.ncard = m := by
      have hcoe : (imgFinset : Set ℂ) = {z : ℂ | z ^ m = w} := by
        ext z; simp [imgFinset, hset_eq]
      rw [← hcoe, Set.ncard_coe_finset, hcard_img]
    exact ⟨hinj, hpow, hset_eq, hfin, hncard⟩
  have : NeZero m := ⟨hm.ne'⟩
  have hopen : IsOpenMap (fun z : ℂ => z ^ m) := (Complex.isOpenQuotientMap_pow m).isOpenMap
  refine ⟨hroots, hopen, ?_⟩
  intro r hr
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    rw [mem_disc, sub_zero] at hz ⊢
    rw [norm_pow]
    exact pow_lt_pow_left₀ hz (norm_nonneg z) hm.ne'
  · intro w hw
    rw [mem_disc, sub_zero] at hw
    by_cases hw0 : w = 0
    · subst hw0
      exact ⟨0, by simpa [disc] using hr, zero_pow hm.ne'⟩
    · let z := polarNthRoot m w ⟨0, hm⟩
      refine ⟨z, ?_, (hroots w hw0).2.1 ⟨0, hm⟩⟩
      rw [mem_disc, sub_zero]
      dsimp [z, polarNthRoot]
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hw0) _)]
      have hlt := Real.rpow_lt_rpow (norm_nonneg w) hw (one_div_pos.mpr hm_real_pos)
      rwa [← Real.rpow_natCast r m, ← Real.rpow_mul hr.le, mul_one_div_cancel hm_real_ne,
        Real.rpow_one] at hlt

/-- 10.32 (Local normal form & Open Mapping Theorem): suppose `Ω` is a region, `f ∈ H(Ω)`, and `f`
is nonconstant on `Ω`.
1. (Open mapping theorem) For every open subset `U ⊆ Ω`, `f '' U` is open; in particular `f '' Ω`
   is a region (`IsRegion (f '' Ω)`).
2. (Local power normal form) For every `z₀ ∈ Ω` with `w₀ = f z₀`, there exist a unique integer
   `m ≥ 1` (the zero multiplicity of `f - w₀` at `z₀`), an open neighborhood `V ⊆ Ω` of `z₀`, a
   radius `r > 0`, a holomorphic bijection `φ : V → D(0; r)` (`HolomorphicOn φ V`, `φ z₀ = 0`,
   `∀ z ∈ V, deriv φ z ≠ 0`) with holomorphic inverse `ψ` on `D(0; r)`, such that:
   - `∀ z ∈ V, f z = w₀ + (φ z) ^ m`,
   - `f '' V = disc w₀ (r ^ m)`,
   - for every `w ∈ puncturedDisc w₀ (r ^ m)`, `{z ∈ V | f z = w}` is finite and has exact
     cardinality `m` (`{z ∈ V | f z = w}.ncard = m`). -/
theorem theorem10_32 {Ω : Set ℂ} (hΩ : IsRegion Ω) {f : ℂ → ℂ} (hf : HolomorphicOn f Ω)
    (hnonconst : ¬ ∃ w : ℂ, ∀ z ∈ Ω, f z = w) :
    ((∀ U ⊆ Ω, IsOpen U → IsOpen (f '' U)) ∧ IsRegion (f '' Ω)) ∧
    (∀ z₀ ∈ Ω, ∃ m : ℕ, 0 < m ∧
      (∃! k : ℕ, 0 < k ∧ ∃ g : ℂ → ℂ, HolomorphicOn g Ω ∧ g z₀ ≠ 0 ∧
        ∀ z ∈ Ω, f z - f z₀ = (z - z₀) ^ k * g z) ∧
      ∃ (V : Set ℂ) (r : ℝ) (φ ψ : ℂ → ℂ),
        IsOpen V ∧ z₀ ∈ V ∧ V ⊆ Ω ∧ 0 < r ∧
        HolomorphicOn φ V ∧ HolomorphicOn ψ (disc 0 r) ∧
        φ z₀ = 0 ∧ (∀ z ∈ V, deriv φ z ≠ 0) ∧
        Set.BijOn φ V (disc 0 r) ∧
        (∀ z ∈ V, ψ (φ z) = z) ∧
        (∀ ζ ∈ disc 0 r, ψ ζ ∈ V ∧ φ (ψ ζ) = ζ) ∧
        (∀ z ∈ V, f z = f z₀ + (φ z) ^ m) ∧
        f '' V = disc (f z₀) (r ^ m) ∧
        (∀ w ∈ puncturedDisc (f z₀) (r ^ m),
          {z ∈ V | f z = w}.Finite ∧ {z ∈ V | f z = w}.ncard = m)) := by
  have hana : AnalyticOnNhd ℂ f Ω :=
    ((holomorphicOn_iff_differentiableOn hΩ.1).mp hf).analyticOnNhd hΩ.1
  have hopen_map : ∀ U ⊆ Ω, IsOpen U → IsOpen (f '' U) :=
    (hana.is_constant_or_isOpen hΩ.2.isPreconnected).resolve_left hnonconst
  have hreg_img : IsRegion (f '' Ω) :=
    ⟨hopen_map Ω Subset.rfl hΩ.1, hΩ.2.image f (continuousOn_of_holomorphicOn hf)⟩
  refine ⟨⟨hopen_map, hreg_img⟩, ?_⟩
  intro z₀ hz₀
  let f₀ : ℂ → ℂ := fun z => f z - f z₀
  have hf₀_holo : HolomorphicOn f₀ Ω := fun z hz => (hf z hz).sub_const (f z₀)
  have hf₀_not_zero : ¬ Set.EqOn f₀ 0 Ω := by
    intro hz0
    exact hnonconst ⟨f z₀, fun z hz => sub_eq_zero.mp (hz0 hz)⟩
  have hexu := existsUnique_zero_order hΩ hf₀_holo hf₀_not_zero hz₀ (sub_self (f z₀))
  obtain ⟨m, ⟨hm_pos, g, hg_holo, hg_z₀, hf_fac⟩, huniq⟩ := hexu
  refine ⟨m, hm_pos, ⟨m, ⟨hm_pos, g, hg_holo, hg_z₀, hf_fac⟩, huniq⟩, ?_⟩
  -- Find `r₁ > 0` with `disc z₀ r₁ ⊆ Ω` and `g ≠ 0` on `disc z₀ r₁`
  have hg_nhds : ∀ᶠ z in 𝓝 z₀, z ∈ Ω ∧ g z ≠ 0 :=
    Filter.inter_mem (hΩ.1.mem_nhds hz₀) ((hg_holo z₀ hz₀).continuousAt.eventually_ne hg_z₀)
  obtain ⟨r₁, hr₁, hball_g⟩ := Metric.mem_nhds_iff.mp hg_nhds
  have hdisc₁_sub : disc z₀ r₁ ⊆ Ω := fun z hz => (hball_g hz).1
  have hg_nz : ∀ z ∈ disc z₀ r₁, g z ≠ 0 := fun z hz => (hball_g hz).2
  -- Construct a holomorphic `m`-th root `h` of `g` on the convex open set `disc z₀ r₁` via `10.14`!
  let logd : ℂ → ℂ := fun z => deriv g z / g z
  have hlogd_holo : HolomorphicOn logd (disc z₀ r₁) := fun z hz =>
    (holomorphicOn_deriv hΩ.1 hg_holo z (hdisc₁_sub hz)).div
      (hg_holo z (hdisc₁_sub hz)) (hg_nz z hz)
  obtain ⟨⟨L, hL_holo, hL_deriv⟩, _⟩ :=
    theorem10_14 Metric.isOpen_ball (convex_ball z₀ r₁) z₀
      (continuousOn_of_holomorphicOn hlogd_holo)
      (fun z hz => hlogd_holo z hz.1)
  -- `k(z) = g(z) * exp(-L(z))` has derivative `0` on `disc z₀ r₁`, hence `k(z) = k(z₀)`
  let kfn : ℂ → ℂ := fun z => g z * Complex.exp (-L z)
  have hk_deriv : ∀ z ∈ disc z₀ r₁, HasDerivAt kfn 0 z := by
    intro z hz
    have hdg : HasDerivAt g (deriv g z) z := (hg_holo z (hdisc₁_sub hz)).hasDerivAt
    have hdL : HasDerivAt L (deriv g z / g z) z := by
      have h := (hL_holo z hz).hasDerivAt
      rwa [hL_deriv z hz] at h
    have hdexp : HasDerivAt (fun ζ => Complex.exp (-L ζ))
        (Complex.exp (-L z) * -(deriv g z / g z)) z := hdL.neg.cexp
    have hprod := hdg.mul hdexp
    have hzero : deriv g z * Complex.exp (-L z) +
        g z * (Complex.exp (-L z) * -(deriv g z / g z)) = 0 := by
      have hgz := hg_nz z hz
      field_simp [hgz]
      ring
    exact hzero ▸ hprod
  have hk_const : ∀ z ∈ disc z₀ r₁, kfn z = kfn z₀ := by
    intro z hz
    by_cases hzz₀ : z = z₀
    · rw [hzz₀]
    · have hseg_sub : (orientedSegment z₀ z).trace ⊆ disc z₀ r₁ := by
        rw [orientedSegment_trace]
        exact (convex_ball z₀ r₁).segment_subset (Metric.mem_ball_self hr₁) hz
      have hftc := pathIntegral_eq_sub_of_hasDerivWithinAt
        (f := fun _ => 0) (F := kfn) continuousOn_const
        (fun ζ hζ => (hk_deriv ζ hζ).hasDerivWithinAt)
        (orientedSegment z₀ z) hseg_sub
      have hint0 : pathIntegral (fun _ => 0) (orientedSegment z₀ z).toBookCurve = 0 := by
        simp [pathIntegral]
      have hα : (orientedSegment z₀ z).toFun (orientedSegment z₀ z).α = z₀ := by
        simp [orientedSegment, BookPath.ofC1]
      have hβ : (orientedSegment z₀ z).toFun (orientedSegment z₀ z).β = z := by
        simp [orientedSegment, BookPath.ofC1]
      rw [hα, hβ, hint0] at hftc
      exact sub_eq_zero.mp hftc.symm
  have hg_exp : ∀ z ∈ disc z₀ r₁, g z = g z₀ * Complex.exp (L z - L z₀) := by
    intro z hz
    have hk_eq := hk_const z hz
    dsimp [kfn] at hk_eq
    calc g z = (g z * Complex.exp (-L z)) * Complex.exp (L z) := by
          rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = (g z₀ * Complex.exp (-L z₀)) * Complex.exp (L z) := by rw [hk_eq]
      _ = g z₀ * Complex.exp (L z - L z₀) := by
          rw [mul_assoc, ← Complex.exp_add]
          congr 2
          ring
  let c₀ : ℂ := polarNthRoot m (g z₀) ⟨0, hm_pos⟩
  have hc₀_pow : c₀ ^ m = g z₀ := ((theorem10_31 hm_pos).1 (g z₀) hg_z₀).2.1 ⟨0, hm_pos⟩
  have hc₀_ne : c₀ ≠ 0 := fun h0 => hg_z₀ (by rw [← hc₀_pow, h0, zero_pow hm_pos.ne'])
  let h : ℂ → ℂ := fun z => c₀ * Complex.exp ((L z - L z₀) / (m : ℂ))
  have hh_holo : HolomorphicOn h (disc z₀ r₁) := fun z hz =>
    (differentiableAt_const c₀).mul
      ((((hL_holo z hz).sub_const (L z₀)).div_const (m : ℂ)).cexp)
  have hh_z₀ : h z₀ = c₀ := by simp [h]
  have hh_pow : ∀ z ∈ disc z₀ r₁, (h z) ^ m = g z := by
    intro z hz
    dsimp [h]
    have hm_c_ne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm_pos.ne'
    rw [mul_pow, hc₀_pow, ← Complex.exp_nat_mul, mul_div_cancel₀ _ hm_c_ne, hg_exp z hz]
  let φ : ℂ → ℂ := fun z => (z - z₀) * h z
  have hφ_holo : HolomorphicOn φ (disc z₀ r₁) := fun z hz =>
    (differentiableAt_id.sub_const z₀).mul (hh_holo z hz)
  have hφ_z₀ : φ z₀ = 0 := by simp [φ]
  have hφ_pow : ∀ z ∈ disc z₀ r₁, f z = f z₀ + (φ z) ^ m := by
    intro z hz
    dsimp [φ]
    rw [mul_pow, hh_pow z hz, ← hf_fac z (hdisc₁_sub hz)]
    dsimp [f₀]
    ring
  have hφ_deriv_z₀ : deriv φ z₀ ≠ 0 := by
    have hd : HasDerivAt φ (1 * h z₀ + (z₀ - z₀) * deriv h z₀) z₀ :=
      ((hasDerivAt_id z₀).sub_const z₀).mul (hh_holo z₀ (Metric.mem_ball_self hr₁)).hasDerivAt
    rw [hd.deriv]
    simp [hh_z₀, hc₀_ne]
  -- Apply `10.30` to `φ` on `disc z₀ r₁` at `z₀`
  obtain ⟨U₁, V₁, ψ, hU₁_open, hz₀_U₁, hU₁_sub, hV₁_open, h0_V₁, hbij₁, hψ_holo,
    hφ_deriv_nz, hleft₁, hright₁, _⟩ :=
    theorem10_30 Metric.isOpen_ball hφ_holo (Metric.mem_ball_self hr₁) hφ_deriv_z₀
  rw [hφ_z₀] at h0_V₁
  obtain ⟨r, hr, hdisc0_sub⟩ := Metric.isOpen_iff.mp hV₁_open 0 h0_V₁
  let V : Set ℂ := U₁ ∩ φ ⁻¹' disc 0 r
  have hV_open : IsOpen V :=
    (continuousOn_of_holomorphicOn (fun z hz => hφ_holo z (hU₁_sub hz))).isOpen_inter_preimage
      hU₁_open Metric.isOpen_ball
  have hz₀_V : z₀ ∈ V := ⟨hz₀_U₁, by rw [Set.mem_preimage, hφ_z₀]; exact Metric.mem_ball_self hr⟩
  have hV_sub_Ω : V ⊆ Ω := fun z hz => hdisc₁_sub (hU₁_sub hz.1)
  have hbij_V : Set.BijOn φ V (disc 0 r) := by
    refine ⟨fun z hz => hz.2, ?_, ?_⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      exact hbij₁.injOn hz₁.1 hz₂.1 heq
    · intro ζ hζ
      have hζ_V₁ : ζ ∈ V₁ := hdisc0_sub hζ
      refine ⟨ψ ζ, ⟨(hright₁ ζ hζ_V₁).1, ?_⟩, (hright₁ ζ hζ_V₁).2⟩
      rw [Set.mem_preimage, (hright₁ ζ hζ_V₁).2]
      exact hζ
  have hψ_maps : ∀ ζ ∈ disc 0 r, ψ ζ ∈ V ∧ φ (ψ ζ) = ζ := by
    intro ζ hζ
    have hζ_V₁ : ζ ∈ V₁ := hdisc0_sub hζ
    exact ⟨⟨(hright₁ ζ hζ_V₁).1, by rw [Set.mem_preimage, (hright₁ ζ hζ_V₁).2]; exact hζ⟩,
      (hright₁ ζ hζ_V₁).2⟩
  have hf_img_V : f '' V = disc (f z₀) (r ^ m) := by
    have heq_f : f '' V = (fun w => f z₀ + w) '' ((fun ζ : ℂ => ζ ^ m) '' (φ '' V)) := by
      ext w
      simp only [Set.mem_image]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨(φ z) ^ m, ⟨φ z, ⟨z, hz, rfl⟩, rfl⟩, (hφ_pow z (hU₁_sub hz.1)).symm⟩
      · rintro ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
        exact ⟨z, hz, hφ_pow z (hU₁_sub hz.1)⟩
    rw [heq_f, hbij_V.image_eq, (theorem10_31 hm_pos).2.2 r hr]
    ext w
    simp [disc, Metric.mem_ball, dist_eq_norm]
  have hfibers : ∀ w ∈ puncturedDisc (f z₀) (r ^ m),
      {z ∈ V | f z = w}.Finite ∧ {z ∈ V | f z = w}.ncard = m := by
    intro w hw
    let u : ℂ := w - f z₀
    have hu_ne : u ≠ 0 := sub_ne_zero.mpr hw.2
    have hu_lt : ‖u‖ < r ^ m := mem_disc.mp hw.1
    obtain ⟨hinj_root, hpow_root, hset_root, hfin_root, hncard_root⟩ :=
      (theorem10_31 hm_pos).1 u hu_ne
    have hroots_in_disc : {ζ : ℂ | ζ ^ m = u} ⊆ disc 0 r := by
      intro ζ hζ
      change ζ ^ m = u at hζ
      rw [mem_disc, sub_zero]
      by_contra hge
      have hle : r ≤ ‖ζ‖ := not_lt.mp hge
      have hpow_le : r ^ m ≤ ‖u‖ := by
        rw [← hζ, norm_pow]
        exact pow_le_pow_left₀ hr.le hle m
      linarith
    have hfiber_eq : {z ∈ V | f z = w} = ψ '' {ζ : ℂ | ζ ^ m = u} := by
      ext z
      constructor
      · rintro ⟨hzV, hfw⟩
        refine ⟨φ z, ?_, hleft₁ z hzV.1⟩
        change φ z ^ m = u
        have := hφ_pow z (hU₁_sub hzV.1)
        dsimp [u]
        linear_combination -this + hfw
      · rintro ⟨ζ, hζ, rfl⟩
        have hζ_disc : ζ ∈ disc 0 r := hroots_in_disc hζ
        have hψζ := hψ_maps ζ hζ_disc
        refine ⟨hψζ.1, ?_⟩
        have hζ_eq : ζ ^ m = u := hζ
        rw [hφ_pow (ψ ζ) (hU₁_sub hψζ.1.1), hψζ.2, hζ_eq]
        dsimp [u]
        ring
    have hψ_inj : Set.InjOn ψ {ζ : ℂ | ζ ^ m = u} := by
      intro ζ₁ hζ₁ ζ₂ hζ₂ heq
      rw [← (hψ_maps ζ₁ (hroots_in_disc hζ₁)).2, ← (hψ_maps ζ₂ (hroots_in_disc hζ₂)).2, heq]
    rw [hfiber_eq]
    exact ⟨hfin_root.image ψ, hψ_inj.ncard_image.trans hncard_root⟩
  exact ⟨V, r, φ, ψ, hV_open, hz₀_V, hV_sub_Ω, hr,
    fun z hz => hφ_holo z (hU₁_sub hz.1),
    fun ζ hζ => hψ_holo ζ (hdisc0_sub hζ),
    hφ_z₀, fun z hz => hφ_deriv_nz z hz.1, hbij_V,
    fun z hz => hleft₁ z hz.1, hψ_maps, fun z hz => hφ_pow z (hU₁_sub hz.1),
    hf_img_V, hfibers⟩

/-- 10.33 (Injective holomorphic functions & converse counterexample):
1. If `Ω` is open, `f ∈ H(Ω)`, and `f` is injective on `Ω` (`Set.InjOn f Ω`), then `f'(z) ≠ 0`
   for every `z ∈ Ω`, `f '' Ω` is open, and the inverse of `f` is holomorphic on `f '' Ω` with
   `g'(f z) = (f'(z))⁻¹` for all `z ∈ Ω`.
2. Converse fails globally: `Complex.exp` is entire and `deriv Complex.exp z ≠ 0` for all `z ∈ ℂ`,
   yet `Complex.exp` is not injective on `ℂ`. -/
theorem theorem10_33 :
    (∀ {Ω : Set ℂ} {f : ℂ → ℂ}, IsOpen Ω → HolomorphicOn f Ω → Set.InjOn f Ω →
      (∀ z ∈ Ω, deriv f z ≠ 0) ∧
      IsOpen (f '' Ω) ∧
      ∃ g : ℂ → ℂ, HolomorphicOn g (f '' Ω) ∧
        (∀ z ∈ Ω, g (f z) = z) ∧
        (∀ w ∈ f '' Ω, g w ∈ Ω ∧ f (g w) = w) ∧
        (∀ z ∈ Ω, deriv g (f z) = (deriv f z)⁻¹)) ∧
    (HolomorphicOn Complex.exp Set.univ ∧
      (∀ z : ℂ, deriv Complex.exp z ≠ 0) ∧
      ¬ Function.Injective Complex.exp) := by
  refine ⟨?_, ?_⟩
  · intro Ω f hΩ hf hinj
    have hdf_nz : ∀ z₀ ∈ Ω, deriv f z₀ ≠ 0 := by
      intro z₀ hz₀
      obtain ⟨r₀, hr₀, hdisc₀_sub⟩ := Metric.isOpen_iff.mp hΩ z₀ hz₀
      have hnonconst : ¬ ∃ w : ℂ, ∀ z ∈ disc z₀ r₀, f z = w := by
        rintro ⟨w, hw⟩
        let z₁ : ℂ := z₀ + ((r₀ / 2 : ℝ) : ℂ)
        have hz₁_disc : z₁ ∈ disc z₀ r₀ := by
          rw [mem_disc]
          simp only [z₁, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (half_pos hr₀)]
          linarith
        have hfz₁ : f z₁ = f z₀ := (hw z₁ hz₁_disc).trans (hw z₀ (Metric.mem_ball_self hr₀)).symm
        have heq : z₁ = z₀ := hinj (hdisc₀_sub hz₁_disc) hz₀ hfz₁
        dsimp [z₁] at heq
        have : ((r₀ / 2 : ℝ) : ℂ) = 0 := by linear_combination heq
        have : r₀ / 2 = 0 := Complex.ofReal_eq_zero.mp this
        linarith
      obtain ⟨m, hm_pos, _, V, r, φ, _, hV_open, hz₀_V, hV_sub, hr, hφ_holo, _, _,
        hφ_deriv_nz, _, _, _, hf_eq_φ, _, hfibers⟩ :=
        (theorem10_32 (disc_isRegion z₀ hr₀) (fun z hz => hf z (hdisc₀_sub hz)) hnonconst).2
          z₀ (Metric.mem_ball_self hr₀)
      let w : ℂ := f z₀ + (((r / 2) ^ m : ℝ) : ℂ)
      have hw_punc : w ∈ puncturedDisc (f z₀) (r ^ m) := by
        refine ⟨?_, ?_⟩
        · rw [mem_disc]
          simp only [w, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (pow_pos (half_pos hr) m)]
          exact pow_lt_pow_left₀ (half_lt_self hr) (half_pos hr).le hm_pos.ne'
        · intro heq
          rw [Set.mem_singleton_iff] at heq
          dsimp [w] at heq
          have : (((r / 2) ^ m : ℝ) : ℂ) = 0 := by linear_combination heq
          have hpow0 : (r / 2) ^ m = 0 := Complex.ofReal_eq_zero.mp this
          linarith [pow_pos (half_pos hr) m]
      obtain ⟨hfin, hncard⟩ := hfibers w hw_punc
      have hsubsing : {z ∈ V | f z = w}.Subsingleton := by
        rintro z₁ ⟨hz₁V, hfz₁⟩ z₂ ⟨hz₂V, hfz₂⟩
        exact hinj (hdisc₀_sub (hV_sub hz₁V)) (hdisc₀_sub (hV_sub hz₂V)) (hfz₁.trans hfz₂.symm)
      have hm_le_one : m ≤ 1 := hncard ▸ (Set.ncard_le_one hfin).mpr hsubsing
      have hm_eq : m = 1 := le_antisymm hm_le_one hm_pos
      subst hm_eq
      have hev_eq : f =ᶠ[𝓝 z₀] fun z => f z₀ + φ z := by
        filter_upwards [hV_open.mem_nhds hz₀_V] with z hz
        simpa using hf_eq_φ z hz
      have hderiv_eq : deriv f z₀ = deriv φ z₀ := by
        rw [hev_eq.deriv_eq]
        exact (((hφ_holo z₀ hz₀_V).hasDerivAt).const_add (f z₀)).deriv
      rw [hderiv_eq]
      exact hφ_deriv_nz z₀ hz₀_V
    classical
    let g : ℂ → ℂ := Function.invFunOn f Ω
    have hleft : ∀ z ∈ Ω, g (f z) = z := fun z hz =>
      hinj (Function.invFunOn_mem ⟨z, hz, rfl⟩) hz (Function.invFunOn_eq ⟨z, hz, rfl⟩)
    have hright : ∀ w ∈ f '' Ω, g w ∈ Ω ∧ f (g w) = w := by
      rintro _ ⟨z, hz, rfl⟩
      rw [hleft z hz]
      exact ⟨hz, rfl⟩
    -- At every `z₀ ∈ Ω`, `theorem10_30` gives open `U ⊆ Ω` and `V = f '' U ⊆ f '' Ω` on which `g` agrees with the holomorphic local inverse!
    have hlocal : ∀ z₀ ∈ Ω, ∃ V : Set ℂ, IsOpen V ∧ f z₀ ∈ V ∧ V ⊆ f '' Ω ∧
        HolomorphicOn g V ∧ deriv g (f z₀) = (deriv f z₀)⁻¹ := by
      intro z₀ hz₀
      obtain ⟨U, V, g₁, _, hz₀_U, hU_sub, hV_open, hfz₀_V, _, hg₁_holo, _, _, hright₁, hderiv₁⟩ :=
        theorem10_30 hΩ hf hz₀ (hdf_nz z₀ hz₀)
      have hV_sub : V ⊆ f '' Ω := fun w hw =>
        ⟨g₁ w, hU_sub (hright₁ w hw).1, (hright₁ w hw).2⟩
      have heq_on_V : Set.EqOn g g₁ V := fun w hw => by
        conv_lhs => rw [← (hright₁ w hw).2]
        exact hleft (g₁ w) (hU_sub (hright₁ w hw).1)
      have hg_holo_V : HolomorphicOn g V := fun w hw =>
        (hg₁_holo w hw).congr_of_eventuallyEq
          (Filter.mem_of_superset (hV_open.mem_nhds hw) heq_on_V)
      have hderiv_g : deriv g (f z₀) = (deriv f z₀)⁻¹ := by
        have hev : g =ᶠ[𝓝 (f z₀)] g₁ := Filter.mem_of_superset (hV_open.mem_nhds hfz₀_V) heq_on_V
        rw [hev.deriv_eq, (hderiv₁ z₀ hz₀_U).2]
      exact ⟨V, hV_open, hfz₀_V, hV_sub, hg_holo_V, hderiv_g⟩
    have himg_open : IsOpen (f '' Ω) := by
      rw [isOpen_iff_forall_mem_open]
      rintro _ ⟨z₀, hz₀, rfl⟩
      obtain ⟨V, hV_open, hfz₀_V, hV_sub, _, _⟩ := hlocal z₀ hz₀
      exact ⟨V, hV_sub, hV_open, hfz₀_V⟩
    have hg_holo : HolomorphicOn g (f '' Ω) := by
      rintro _ ⟨z₀, hz₀, rfl⟩
      obtain ⟨V, _, hfz₀_V, _, hg_V, _⟩ := hlocal z₀ hz₀
      exact hg_V (f z₀) hfz₀_V
    have hderiv_all : ∀ z₀ ∈ Ω, deriv g (f z₀) = (deriv f z₀)⁻¹ := fun z₀ hz₀ =>
      (hlocal z₀ hz₀).choose_spec.2.2.2.2
    exact ⟨hdf_nz, himg_open, g, hg_holo, hleft, hright, hderiv_all⟩
  · refine ⟨fun z _ => Complex.differentiableAt_exp, fun z => ?_, ?_⟩
    · rw [Complex.deriv_exp]
      exact Complex.exp_ne_zero z
    · intro hinj
      have heq : Complex.exp (2 * Real.pi * Complex.I) = Complex.exp 0 := by
        rw [Complex.exp_two_pi_mul_I, Complex.exp_zero]
      have h0 := hinj heq
      have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
          Complex.I_ne_zero
      exact hne h0

end BatchC

/-! ### 10.35 & 10.36: Global Cauchy theorem and integral formula for cycles; convex exteriors and cycle replacement -/

section BatchD1

/-- Helper for 10.35: for any chain `Γ` and `g` continuous on `Γ*`, `z ↦ ∫_Γ g(ζ)/(ζ - z) dζ` is
holomorphic on `(Γ*)ᶜ`. -/
private theorem holomorphicOn_chainIntegral_div_sub (Γ : BookChain) {g : ℂ → ℂ}
    (hg : ContinuousOn g Γ.trace) :
    HolomorphicOn (fun z => Γ.integral (fun ζ => g ζ / (ζ - z))) (Γ.trace)ᶜ := by
  induction Γ with
  | nil =>
    intro z _
    change DifferentiableAt ℂ (fun _ => (0 : ℂ)) z
    exact differentiableAt_const 0
  | cons γ Γ ih =>
    rw [BookChain.trace_cons] at hg ⊢
    intro z₀ hz₀
    have hz₀_γ : z₀ ∈ (γ.trace)ᶜ := fun h => hz₀ (Or.inl h)
    have hz₀_Γ : z₀ ∈ (BookChain.trace Γ)ᶜ := fun h => hz₀ (Or.inr h)
    have hg_γ : ContinuousOn g γ.trace := hg.mono subset_union_left
    have hγ_diff : DifferentiableAt ℂ
        (fun z => pathIntegral (fun ζ => g ζ / (ζ - z)) γ.toBookCurve) z₀ := by
      have hopen : IsOpen (γ.trace)ᶜ := γ.isCompact_trace.isClosed.isOpen_compl
      obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.mp hopen z₀ hz₀_γ
      let δ : ℝ := ε₀ / 2
      have hδ : 0 < δ := half_pos hε₀
      have h2δ : 2 * δ = ε₀ := by dsimp [δ]; ring
      obtain ⟨w_max, _, hw_max⟩ := γ.isCompact_trace.exists_isMaxOn γ.trace_nonempty hg_γ.norm
      set M : ℝ := ‖g w_max‖ + 1
      have hM_pos : 0 < M := by linarith [norm_nonneg (g w_max)]
      have hM_le : ∀ ζ ∈ γ.trace, ‖g ζ‖ ≤ M := fun ζ hζ =>
        le_trans (hw_max hζ) (by linarith)
      let L : ℝ := pathLength γ.toBookCurve + 1
      have hL_pos : 0 < L := by linarith [γ.pathLength_nonneg]
      have hw_z₀ : ∀ ζ ∈ γ.trace, 2 * δ ≤ ‖ζ - z₀‖ := fun ζ hζ => by
        by_contra hlt
        exact hball (show ζ ∈ Metric.ball z₀ ε₀ by
          rw [Metric.mem_ball, dist_eq_norm]; linarith [not_le.mp hlt, h2δ]) hζ
      refine HasDerivAt.differentiableAt
        (f' := pathIntegral (fun ζ => g ζ / (ζ - z₀) ^ 2) γ.toBookCurve) ?_
      rw [hasDerivAt_iff_difference_quotient, Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      have hden_pos : 0 < 4 * δ ^ 3 := by positivity
      refine ⟨min δ (ε * (4 * δ ^ 3) / (M * L)),
        lt_min hδ (div_pos (mul_pos hε hden_pos) (mul_pos hM_pos hL_pos)), ?_⟩
      intro z hz_ne hz_dist
      rw [dist_eq_norm] at hz_dist ⊢
      have hzδ : ‖z - z₀‖ < δ := lt_of_lt_of_le hz_dist (min_le_left _ _)
      have hz_bd : ‖z - z₀‖ < ε * (4 * δ ^ 3) / (M * L) :=
        lt_of_lt_of_le hz_dist (min_le_right _ _)
      have hw_z : ∀ ζ ∈ γ.trace, δ ≤ ‖ζ - z‖ := fun ζ hζ => by
        have htri : ‖ζ - z₀‖ ≤ ‖ζ - z‖ + ‖z - z₀‖ := by simpa using norm_add_le (ζ - z) (z - z₀)
        linarith [hw_z₀ ζ hζ]
      have hne_z : ∀ ζ ∈ γ.trace, ζ - z ≠ 0 := fun ζ hζ h0 => by
        have := hw_z ζ hζ; rw [h0, norm_zero] at this; linarith
      have hne_z₀ : ∀ ζ ∈ γ.trace, ζ - z₀ ≠ 0 := fun ζ hζ h0 => by
        have := hw_z₀ ζ hζ; rw [h0, norm_zero] at this; linarith
      have hf_z : ContinuousOn (fun ζ => g ζ / (ζ - z)) γ.trace :=
        hg_γ.div (continuous_id.sub continuous_const).continuousOn hne_z
      have hf_z₀ : ContinuousOn (fun ζ => g ζ / (ζ - z₀)) γ.trace :=
        hg_γ.div (continuous_id.sub continuous_const).continuousOn hne_z₀
      have hf_sq : ContinuousOn (fun ζ => g ζ / (ζ - z₀) ^ 2) γ.trace :=
        hg_γ.div ((continuous_id.sub continuous_const).pow 2).continuousOn
          (fun ζ hζ => pow_ne_zero 2 (hne_z₀ ζ hζ))
      let diff₁ : ℂ → ℂ := fun ζ => g ζ / (ζ - z) - g ζ / (ζ - z₀)
      let prod₁ : ℂ → ℂ := fun ζ => (z - z₀)⁻¹ * diff₁ ζ
      let φ : ℂ → ℂ := fun ζ => prod₁ ζ - g ζ / (ζ - z₀) ^ 2
      have hdiff₁_cont : ContinuousOn diff₁ γ.trace := hf_z.sub hf_z₀
      have hprod₁_cont : ContinuousOn prod₁ γ.trace := continuousOn_const.mul hdiff₁_cont
      have hφ_cont : ContinuousOn φ γ.trace := hprod₁_cont.sub hf_sq
      have hquot : (pathIntegral (fun ζ => g ζ / (ζ - z)) γ.toBookCurve -
            pathIntegral (fun ζ => g ζ / (ζ - z₀)) γ.toBookCurve) / (z - z₀) -
            pathIntegral (fun ζ => g ζ / (ζ - z₀) ^ 2) γ.toBookCurve =
          pathIntegral φ γ.toBookCurve := by
        rw [← γ.pathIntegral_sub (f := fun ζ => g ζ / (ζ - z)) (g := fun ζ => g ζ / (ζ - z₀)) hf_z hf_z₀,
          div_eq_inv_mul,
          ← BookPath.pathIntegral_const_mul (c := (z - z₀)⁻¹) (f := diff₁),
          ← γ.pathIntegral_sub (f := prod₁) (g := fun ζ => g ζ / (ζ - z₀) ^ 2) hprod₁_cont hf_sq]
      rw [hquot]
      have hpt : ∀ ζ ∈ γ.trace, ‖φ ζ‖ ≤ M * ‖z - z₀‖ / (4 * δ ^ 3) := by
        intro ζ hζ
        dsimp only [φ, prod₁, diff₁]
        have h1 := hne_z ζ hζ
        have h2 := hne_z₀ ζ hζ
        have h3 : z - z₀ ≠ 0 := sub_ne_zero.mpr hz_ne
        have halg : (z - z₀)⁻¹ * (g ζ / (ζ - z) - g ζ / (ζ - z₀)) - g ζ / (ζ - z₀) ^ 2 =
            g ζ * (z - z₀) / ((ζ - z) * (ζ - z₀) ^ 2) := by
          field_simp
          ring
        rw [halg, norm_div, norm_mul, norm_mul, norm_pow]
        have hnum : ‖g ζ‖ * ‖z - z₀‖ ≤ M * ‖z - z₀‖ :=
          mul_le_mul_of_nonneg_right (hM_le ζ hζ) (norm_nonneg _)
        have hden : 4 * δ ^ 3 ≤ ‖ζ - z‖ * ‖ζ - z₀‖ ^ 2 := by
          have hsq : (2 * δ) ^ 2 ≤ ‖ζ - z₀‖ ^ 2 :=
            pow_le_pow_left₀ (by positivity) (hw_z₀ ζ hζ) 2
          nlinarith [hw_z ζ hζ]
        exact le_trans (div_le_div_of_nonneg_right hnum (by positivity))
          (div_le_div_of_nonneg_left (mul_nonneg hM_pos.le (norm_nonneg _)) hden_pos hden)
      have hle := γ.norm_pathIntegral_le hφ_cont hpt
      calc ‖pathIntegral φ γ.toBookCurve‖
          ≤ (M * ‖z - z₀‖ / (4 * δ ^ 3)) * pathLength γ.toBookCurve := hle
        _ ≤ (M * ‖z - z₀‖ / (4 * δ ^ 3)) * L :=
            mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (mul_nonneg hM_pos.le (norm_nonneg _)) hden_pos.le)
        _ < (M * (ε * (4 * δ ^ 3) / (M * L)) / (4 * δ ^ 3)) * L := by
            refine mul_lt_mul_of_pos_right ?_ hL_pos
            exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hz_bd hM_pos) hden_pos
        _ = ε := by field_simp
    exact (hγ_diff.hasDerivAt.add (ih (hg.mono subset_union_right) z₀ hz₀_Γ).hasDerivAt).differentiableAt

/-- Helper for 10.35 (Dixon's lemma): for any `f ∈ H(Ω)` on an open set `Ω` and any chain `Γ` with
`Γ* ⊆ Ω`, `z ↦ ∫_Γ dividedDifference f ζ z dζ` is holomorphic on `Ω`. -/
private theorem holomorphicOn_chainIntegral_dividedDifference {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : HolomorphicOn f Ω) (Γ : BookChain) (hΓ : Γ.trace ⊆ Ω) :
    HolomorphicOn (fun z => Γ.integral (fun ζ => dividedDifference f ζ z)) Ω := by
  have hj := node10_29_jointly_continuous hΩ hf
  induction Γ with
  | nil =>
    intro z _
    change DifferentiableAt ℂ (fun _ => (0 : ℂ)) z
    exact differentiableAt_const 0
  | cons γ Γ ih =>
    rw [BookChain.trace_cons] at hΓ
    have hγ : γ.trace ⊆ Ω := subset_union_left.trans hΓ
    have hΓ' : BookChain.trace Γ ⊆ Ω := subset_union_right.trans hΓ
    have hγ_holo : HolomorphicOn
        (fun z => pathIntegral (fun ζ => dividedDifference f ζ z) γ.toBookCurve) Ω := by
      obtain ⟨n, s, d, hs, hs0, hsn, hdcont, hd⟩ := γ.piecewiseC1
      let pieceInt : Fin n → ℂ → ℂ := fun i z =>
        ∫ t in s i.castSucc..s i.succ, dividedDifference f (γ.toFun t) z * d i t
      have hpiece_eq : ∀ z ∈ Ω,
          pathIntegral (fun ζ => dividedDifference f ζ z) γ.toBookCurve =
            ∑ i : Fin n, pieceInt i z := by
        intro z hz
        have hf_z : ContinuousOn (fun ζ => dividedDifference f ζ z) γ.trace :=
          hj.comp (continuousOn_id.prodMk continuousOn_const) fun ζ hζ => ⟨hγ hζ, hz⟩
        exact γ.pathIntegral_eq_sum_pieces hf_z hs hs0 hsn hdcont hd
      have hpiece_holo : ∀ i : Fin n, HolomorphicOn (pieceInt i) Ω := by
        intro i
        have hlt : s i.castSucc < s i.succ := hs i.castSucc_lt_succ
        have hsub : Icc (s i.castSucc) (s i.succ) ⊆ Icc γ.α γ.β :=
          Icc_subset_Icc (hs0 ▸ hs.monotone (Fin.zero_le _)) (hsn ▸ hs.monotone (Fin.le_last _))
        have hγ_maps : MapsTo γ.toFun (Icc (s i.castSucc) (s i.succ)) Ω :=
          fun t ht => hγ (γ.mem_trace_of_mem_Icc (hsub ht))
        -- Continuity of `pieceInt i` on `Ω` via uniform continuity on compact `[a, b] × closedBall z₀ r`
        have hcont_i : ContinuousOn (pieceInt i) Ω := by
          intro z₀ hz₀
          apply ContinuousAt.continuousWithinAt
          obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.mp hΩ z₀ hz₀
          set r : ℝ := r₀ / 2
          have hr : 0 < r := half_pos hr₀
          have hcb_sub : Metric.closedBall z₀ r ⊆ Ω :=
            (Metric.closedBall_subset_ball (half_lt_self hr₀)).trans hball₀
          let K : Set (ℝ × ℂ) := Icc (s i.castSucc) (s i.succ) ×ˢ Metric.closedBall z₀ r
          have hK_comp : IsCompact K := isCompact_Icc.prod (isCompact_closedBall z₀ r)
          let G : ℝ × ℂ → ℂ := fun p => dividedDifference f (γ.toFun p.1) p.2 * d i p.1
          have hG_cont : ContinuousOn G K := by
            refine (hj.comp (((γ.continuousOn.mono hsub).comp continuousOn_fst
              (fun p hp => hp.1)).prodMk continuousOn_snd) ?_).mul
              ((hdcont i).comp continuousOn_fst (fun p hp => hp.1))
            intro p hp
            exact ⟨hγ_maps hp.1, hcb_sub hp.2⟩
          have hG_unif := Metric.uniformContinuousOn_iff.mp
            (hK_comp.uniformContinuousOn_of_continuous hG_cont)
          rw [Metric.continuousAt_iff]
          intro ε hε
          have hlen_pos : 0 < s i.succ - s i.castSucc + 1 := by linarith
          obtain ⟨δ, hδ, hδ_unif⟩ := hG_unif (ε / (s i.succ - s i.castSucc + 1))
            (div_pos hε hlen_pos)
          refine ⟨min r δ, lt_min hr hδ, fun z hz_dist => ?_⟩
          have hzr : z ∈ Metric.closedBall z₀ r :=
            Metric.mem_closedBall.mpr (le_trans hz_dist.le (min_le_left _ _))
          have hzδ : dist z z₀ < δ := lt_of_lt_of_le hz_dist (min_le_right _ _)
          have hint_z : IntervalIntegrable (fun t => G (t, z)) MeasureTheory.volume
              (s i.castSucc) (s i.succ) :=
            (hG_cont.comp (continuousOn_id.prodMk continuousOn_const)
              (fun t ht => ⟨ht, hzr⟩)).intervalIntegrable_of_Icc hlt.le
          have hint_z₀ : IntervalIntegrable (fun t => G (t, z₀)) MeasureTheory.volume
              (s i.castSucc) (s i.succ) :=
            (hG_cont.comp (continuousOn_id.prodMk continuousOn_const)
              (fun t ht => ⟨ht, Metric.mem_closedBall_self hr.le⟩)).intervalIntegrable_of_Icc hlt.le
          rw [dist_eq_norm]
          change ‖(∫ t in s i.castSucc..s i.succ, G (t, z)) -
              (∫ t in s i.castSucc..s i.succ, G (t, z₀))‖ < ε
          rw [← intervalIntegral.integral_sub hint_z hint_z₀]
          have hbd : ∀ t ∈ Set.uIoc (s i.castSucc) (s i.succ),
              ‖G (t, z) - G (t, z₀)‖ ≤ ε / (s i.succ - s i.castSucc + 1) := by
            intro t ht
            rw [Set.uIoc_of_le hlt.le] at ht
            have htIcc : t ∈ Icc (s i.castSucc) (s i.succ) := Ioc_subset_Icc_self ht
            have hd_prod : dist (t, z) (t, z₀) < δ := by
              simpa [Prod.dist_eq] using hzδ
            rw [← dist_eq_norm]
            exact (hδ_unif (t, z) ⟨htIcc, hzr⟩ (t, z₀)
              ⟨htIcc, Metric.mem_closedBall_self hr.le⟩ hd_prod).le
          have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbd
          rw [abs_of_pos (sub_pos.mpr hlt)] at hle
          calc ‖∫ t in s i.castSucc..s i.succ, (G (t, z) - G (t, z₀))‖
              ≤ ε / (s i.succ - s i.castSucc + 1) * (s i.succ - s i.castSucc) := hle
            _ < ε / (s i.succ - s i.castSucc + 1) * (s i.succ - s i.castSucc + 1) :=
                mul_lt_mul_of_pos_left (by linarith) (div_pos hε hlen_pos)
            _ = ε := div_mul_cancel₀ ε hlen_pos.ne'
        -- Morera's theorem (`theorem10_17`) on `pieceInt i` via Fubini + `theorem10_13`
        refine theorem10_17 hΩ hcont_i fun p₁ p₂ p₃ hΔ => ?_
        have htr_sub : (triangleBoundary p₁ p₂ p₃).trace ⊆ Ω := by
          rw [triangleBoundary_trace]
          have hp₁ : p₁ ∈ convexHull ℝ ({p₁, p₂, p₃} : Set ℂ) := subset_convexHull ℝ _ (by simp)
          have hp₂ : p₂ ∈ convexHull ℝ ({p₁, p₂, p₃} : Set ℂ) := subset_convexHull ℝ _ (by simp)
          have hp₃ : p₃ ∈ convexHull ℝ ({p₁, p₂, p₃} : Set ℂ) := subset_convexHull ℝ _ (by simp)
          exact (union_subset ((convex_convexHull ℝ _).segment_subset hp₁ hp₂)
            (union_subset ((convex_convexHull ℝ _).segment_subset hp₂ hp₃)
              ((convex_convexHull ℝ _).segment_subset hp₃ hp₁))).trans hΔ
        rw [pathIntegral_triangleBoundary (hcont_i.mono htr_sub)]
        have hseg_swap : ∀ u v : ℂ, segment ℝ u v ⊆ Ω →
            pathIntegral (pieceInt i) (orientedSegment u v).toBookCurve =
              ∫ t in s i.castSucc..s i.succ,
                pathIntegral (fun z => dividedDifference f (γ.toFun t) z)
                  (orientedSegment u v).toBookCurve * d i t := by
          intro u v huv
          rw [pathIntegral_orientedSegment]
          dsimp [pieceInt]
          rw [← intervalIntegral.integral_const_mul]
          have hmul_in : (∫ x in (0 : ℝ)..1,
              (v - u) * ∫ t in s i.castSucc..s i.succ,
                dividedDifference f (γ.toFun t) (Complex.ofReal (1 - x) * u + Complex.ofReal x * v) * d i t) =
              ∫ x in (0 : ℝ)..1, ∫ t in s i.castSucc..s i.succ,
                (v - u) * (dividedDifference f (γ.toFun t)
                  (Complex.ofReal (1 - x) * u + Complex.ofReal x * v) * d i t) :=
            intervalIntegral.integral_congr fun x _ =>
              (intervalIntegral.integral_const_mul _ _).symm
          rw [hmul_in]
          let F : ℝ → ℝ → ℂ := fun x t =>
            (v - u) * (dividedDifference f (γ.toFun t)
              (Complex.ofReal (1 - x) * u + Complex.ofReal x * v) * d i t)
          have hF_cont : ContinuousOn F.uncurry
              (Icc (0 : ℝ) 1 ×ˢ Icc (s i.castSucc) (s i.succ)) := by
            have hseg_maps : MapsTo (fun p : ℝ × ℝ => Complex.ofReal (1 - p.1) * u + Complex.ofReal p.1 * v)
                (Icc (0 : ℝ) 1 ×ˢ Icc (s i.castSucc) (s i.succ)) Ω := by
              intro p hp
              refine huv ?_
              rw [segment_eq_image]
              exact ⟨p.1, hp.1, by simp [Complex.real_smul]⟩
            refine continuousOn_const.mul ((hj.comp
              (((γ.continuousOn.mono hsub).comp continuousOn_snd (fun p hp => hp.2)).prodMk
                ((((Complex.continuous_ofReal.comp (continuous_const.sub continuous_fst)).continuousOn.mul
                  continuousOn_const).add
                  ((Complex.continuous_ofReal.comp continuous_fst).continuousOn.mul continuousOn_const))))
              (fun p hp => ⟨hγ_maps hp.2, hseg_maps hp⟩)).mul
              ((hdcont i).comp continuousOn_snd (fun p hp => hp.2)))
          have hF_int : MeasureTheory.IntegrableOn F.uncurry
              (Set.uIoc (0 : ℝ) 1 ×ˢ Set.uIoc (s i.castSucc) (s i.succ)) :=
            (hF_cont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
              (Set.prod_mono
                (by rw [Set.uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self)
                (by rw [Set.uIoc_of_le hlt.le]; exact Ioc_subset_Icc_self))
          rw [MeasureTheory.intervalIntegral_intervalIntegral_swap hF_int]
          refine intervalIntegral.integral_congr fun t _ => ?_
          rw [pathIntegral_orientedSegment]
          dsimp [F]
          have hpull : (∫ x in (0 : ℝ)..1,
              (v - u) * (dividedDifference f (γ.toFun t)
                (Complex.ofReal (1 - x) * u + Complex.ofReal x * v) * d i t)) =
              ((v - u) * ∫ x in (0 : ℝ)..1,
                dividedDifference f (γ.toFun t)
                  (Complex.ofReal (1 - x) * u + Complex.ofReal x * v)) * d i t := by
            have h1 : (fun x : ℝ =>
                (v - u) * (dividedDifference f (γ.toFun t)
                  (Complex.ofReal (1 - x) * u + Complex.ofReal x * v) * d i t)) =
                fun x : ℝ => ((v - u) * d i t) *
                  dividedDifference f (γ.toFun t)
                    (Complex.ofReal (1 - x) * u + Complex.ofReal x * v) := by
              funext x; ring
            rw [h1, intervalIntegral.integral_const_mul]
            ring
          exact hpull
        have hp₁ : p₁ ∈ convexHull ℝ ({p₁, p₂, p₃} : Set ℂ) := subset_convexHull ℝ _ (by simp)
        have hp₂ : p₂ ∈ convexHull ℝ ({p₁, p₂, p₃} : Set ℂ) := subset_convexHull ℝ _ (by simp)
        have hp₃ : p₃ ∈ convexHull ℝ ({p₁, p₂, p₃} : Set ℂ) := subset_convexHull ℝ _ (by simp)
        have hs₁₂ : segment ℝ p₁ p₂ ⊆ Ω := ((convex_convexHull ℝ _).segment_subset hp₁ hp₂).trans hΔ
        have hs₂₃ : segment ℝ p₂ p₃ ⊆ Ω := ((convex_convexHull ℝ _).segment_subset hp₂ hp₃).trans hΔ
        have hs₃₁ : segment ℝ p₃ p₁ ⊆ Ω := ((convex_convexHull ℝ _).segment_subset hp₃ hp₁).trans hΔ
        rw [hseg_swap p₁ p₂ hs₁₂, hseg_swap p₂ p₃ hs₂₃, hseg_swap p₃ p₁ hs₃₁]
        have hint_seg : ∀ u v : ℂ, segment ℝ u v ⊆ Ω →
            IntervalIntegrable (fun t =>
              pathIntegral (fun z => dividedDifference f (γ.toFun t) z)
                (orientedSegment u v).toBookCurve * d i t)
              MeasureTheory.volume (s i.castSucc) (s i.succ) := by
          intro u v huv
          refine ContinuousOn.intervalIntegrable_of_Icc hlt.le ?_
          -- Continuous in `t` on `Icc (s i.castSucc) (s i.succ)`
          have hseg_cont : ContinuousOn (fun p : ℝ × ℝ =>
              dividedDifference f (γ.toFun p.1)
                (Complex.ofReal (1 - p.2) * u + Complex.ofReal p.2 * v))
              (Icc (s i.castSucc) (s i.succ) ×ˢ Icc (0 : ℝ) 1) := by
            refine hj.comp (((γ.continuousOn.mono hsub).comp continuousOn_fst (fun p hp => hp.1)).prodMk
              ((((Complex.continuous_ofReal.comp (continuous_const.sub continuous_snd)).continuousOn.mul
                continuousOn_const).add
                ((Complex.continuous_ofReal.comp continuous_snd).continuousOn.mul continuousOn_const))))
              fun p hp => ⟨hγ_maps hp.1, huv ?_⟩
            rw [segment_eq_image]
            exact ⟨p.2, hp.2, by simp [Complex.real_smul]⟩
          have hparam_cont : ContinuousOn (fun t : ℝ =>
              ∫ x in (0 : ℝ)..1, dividedDifference f (γ.toFun t)
                (Complex.ofReal (1 - x) * u + Complex.ofReal x * v))
              (Icc (s i.castSucc) (s i.succ)) := by
            intro t₀ ht₀
            rw [Metric.continuousWithinAt_iff]
            intro ε hε
            have hunif := Metric.uniformContinuousOn_iff.mp
              ((isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hseg_cont)
            obtain ⟨δ, hδ, hδu⟩ := hunif (ε / 2) (half_pos hε)
            refine ⟨δ, hδ, fun t ht htdist => ?_⟩
            have hi1 : IntervalIntegrable
                (fun x => dividedDifference f (γ.toFun t)
                  (Complex.ofReal (1 - x) * u + Complex.ofReal x * v))
                MeasureTheory.volume 0 1 :=
              (hseg_cont.comp (continuousOn_const.prodMk continuousOn_id)
                (fun x hx => ⟨ht, hx⟩)).intervalIntegrable_of_Icc zero_le_one
            have hi2 : IntervalIntegrable
                (fun x => dividedDifference f (γ.toFun t₀)
                  (Complex.ofReal (1 - x) * u + Complex.ofReal x * v))
                MeasureTheory.volume 0 1 :=
              (hseg_cont.comp (continuousOn_const.prodMk continuousOn_id)
                (fun x hx => ⟨ht₀, hx⟩)).intervalIntegrable_of_Icc zero_le_one
            rw [dist_eq_norm, ← intervalIntegral.integral_sub hi1 hi2]
            have hbd_x : ∀ x ∈ Set.uIoc (0 : ℝ) 1,
                ‖dividedDifference f (γ.toFun t)
                    (Complex.ofReal (1 - x) * u + Complex.ofReal x * v) -
                  dividedDifference f (γ.toFun t₀)
                    (Complex.ofReal (1 - x) * u + Complex.ofReal x * v)‖ ≤ ε / 2 := by
              intro x hx
              rw [Set.uIoc_of_le zero_le_one] at hx
              rw [← dist_eq_norm]
              exact (hδu (t, x) ⟨ht, Ioc_subset_Icc_self hx⟩
                (t₀, x) ⟨ht₀, Ioc_subset_Icc_self hx⟩ (by simpa [Prod.dist_eq] using htdist)).le
            have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbd_x
            rw [sub_zero, abs_one, mul_one] at hle
            linarith
          have heq_fn : (fun t =>
              pathIntegral (fun z => dividedDifference f (γ.toFun t) z)
                (orientedSegment u v).toBookCurve * d i t) =
              fun t => ((v - u) * ∫ x in (0 : ℝ)..1,
                dividedDifference f (γ.toFun t)
                  (Complex.ofReal (1 - x) * u + Complex.ofReal x * v)) * d i t := by
            funext t; rw [pathIntegral_orientedSegment]; rfl
          rw [heq_fn]
          exact (continuousOn_const.mul hparam_cont).mul (hdcont i)
        rw [← intervalIntegral.integral_add (hint_seg p₁ p₂ hs₁₂) (hint_seg p₂ p₃ hs₂₃),
            ← intervalIntegral.integral_add
              ((hint_seg p₁ p₂ hs₁₂).add (hint_seg p₂ p₃ hs₂₃)) (hint_seg p₃ p₁ hs₃₁)]
        have hzero_int : ∀ t ∈ Set.uIcc (s i.castSucc) (s i.succ),
            pathIntegral (fun z => dividedDifference f (γ.toFun t) z)
              (orientedSegment p₁ p₂).toBookCurve * d i t +
            pathIntegral (fun z => dividedDifference f (γ.toFun t) z)
              (orientedSegment p₂ p₃).toBookCurve * d i t +
            pathIntegral (fun z => dividedDifference f (γ.toFun t) z)
              (orientedSegment p₃ p₁).toBookCurve * d i t = 0 := by
          intro t ht
          rw [Set.uIcc_of_le hlt.le] at ht
          let ζ := γ.toFun t
          have hζ : ζ ∈ Ω := hγ_maps ht
          have hφ_cont : ContinuousOn (fun z => dividedDifference f ζ z) Ω :=
            hj.comp (continuousOn_const.prodMk continuousOn_id) fun z hz => ⟨hζ, hz⟩
          have hφ_holo : HolomorphicOn (fun z => dividedDifference f ζ z) (Ω \ {ζ}) := by
            intro z hz
            have hne : ζ ≠ z := Ne.symm hz.2
            have hev : (fun w => dividedDifference f ζ w) =ᶠ[𝓝 z]
                fun w => (f ζ - f w) / (ζ - w) := by
              filter_upwards [isOpen_ne.mem_nhds (Ne.symm hne)] with w hw
              exact dividedDifference_of_ne (Ne.symm hw)
            exact (((differentiableAt_const (f ζ)).sub (hf z hz.1)).div
              ((differentiableAt_const ζ).sub differentiableAt_id)
              (sub_ne_zero.mpr hne)).congr_of_eventuallyEq hev
          have htri0 := theorem10_13 hΩ ζ hφ_cont hφ_holo p₁ p₂ p₃ hΔ
          rw [pathIntegral_triangleBoundary (hφ_cont.mono htr_sub)] at htri0
          calc pathIntegral (fun z => dividedDifference f ζ z) (orientedSegment p₁ p₂).toBookCurve * d i t +
                pathIntegral (fun z => dividedDifference f ζ z) (orientedSegment p₂ p₃).toBookCurve * d i t +
                pathIntegral (fun z => dividedDifference f ζ z) (orientedSegment p₃ p₁).toBookCurve * d i t
              = (pathIntegral (fun z => dividedDifference f ζ z) (orientedSegment p₁ p₂).toBookCurve +
                 pathIntegral (fun z => dividedDifference f ζ z) (orientedSegment p₂ p₃).toBookCurve +
                 pathIntegral (fun z => dividedDifference f ζ z) (orientedSegment p₃ p₁).toBookCurve) * d i t := by ring
            _ = 0 := by rw [htri0, zero_mul]
        rw [intervalIntegral.integral_congr hzero_int, intervalIntegral.integral_zero]
      intro z₀ hz₀
      have hev : (fun z => pathIntegral (fun ζ => dividedDifference f ζ z) γ.toBookCurve) =ᶠ[𝓝 z₀]
          fun z => ∑ i : Fin n, pieceInt i z := by
        filter_upwards [hΩ.mem_nhds hz₀] with z hz
        exact hpiece_eq z hz
      have hsum_diff : DifferentiableAt ℂ (fun z => ∑ i : Fin n, pieceInt i z) z₀ :=
        DifferentiableAt.fun_sum fun i _ => hpiece_holo i z₀ hz₀
      exact hsum_diff.congr_of_eventuallyEq hev
    intro z₀ hz₀
    exact ((hγ_holo z₀ hz₀).hasDerivAt.add (ih hΓ' z₀ hz₀).hasDerivAt).differentiableAt

/-- Core vanishing lemma for 10.35: if `Γ` is a cycle in an open set `Ω` with `Ind_Γ(w) = 0` for
every `w ∉ Ω`, and `f ∈ H(Ω)`, then `∫_Γ dividedDifference f ζ z dζ = 0` for EVERY `z ∈ Ω`. -/
private theorem chainIntegral_dividedDifference_eq_zero {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : HolomorphicOn f Ω) (Γ : BookChain) (hcyc : Γ.IsCycle)
    (hΓ : Γ.trace ⊆ Ω) (hext : ∀ w, w ∉ Ω → Γ.Ind w = 0) :
    ∀ z ∈ Ω, Γ.integral (fun ζ => dividedDifference f ζ z) = 0 := by
  let g₁ : ℂ → ℂ := fun z => Γ.integral (fun ζ => dividedDifference f ζ z)
  let g₂ : ℂ → ℂ := fun z => Γ.integral (fun ζ => f ζ / (ζ - z))
  let Ω₁ : Set ℂ := {w : ℂ | w ∉ Γ.trace ∧ Γ.Ind w = 0}
  have hΩ₁_open : IsOpen Ω₁ := by
    obtain ⟨V, hV_open, hV_eq⟩ := continuousOn_iff'.mp (BookChain.continuousOn_Ind Γ)
      (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball
    have hΩ₁_eq : Ω₁ = V ∩ (Γ.trace)ᶜ := by
      rw [← hV_eq]
      ext w
      simp only [Ω₁, Set.mem_inter_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right,
        Set.mem_compl_iff]
      constructor
      · rintro ⟨hw_not, hw0⟩
        exact ⟨by simp [hw0], hw_not⟩
      · rintro ⟨hlt, hw_not⟩
        refine ⟨hw_not, ?_⟩
        obtain ⟨n, hn⟩ := BookChain.Ind_mem_int_of_isCycle hcyc hw_not
        rw [hn, Complex.norm_intCast] at hlt
        have hn0 : n = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hlt)
        simp [hn, hn0]
    rw [hΩ₁_eq]
    exact hV_open.inter Γ.isClosed_trace.isOpen_compl
  have hcover : ∀ z : ℂ, z ∈ Ω ∨ z ∈ Ω₁ := by
    intro z
    by_cases hz : z ∈ Ω
    · exact Or.inl hz
    · exact Or.inr ⟨fun htr => hz (hΓ htr), hext z hz⟩
  have hagrees : ∀ z ∈ Ω ∩ Ω₁, g₁ z = g₂ z := by
    rintro z ⟨hzΩ, hz_not, hz_ind⟩
    have hcongr : Set.EqOn (fun ζ => dividedDifference f ζ z)
        (fun ζ => f ζ / (ζ - z) - (fun ζ => f z * (ζ - z)⁻¹) ζ) Γ.trace := by
      intro ζ hζ
      dsimp only
      have hne : ζ ≠ z := fun h => hz_not (h ▸ hζ)
      rw [dividedDifference_of_ne hne, sub_div, div_eq_mul_inv (f z)]
    have hf_div_cont : ContinuousOn (fun ζ => f ζ / (ζ - z)) Γ.trace :=
      ((continuousOn_of_holomorphicOn hf).mono hΓ).div
        (continuous_id.sub continuous_const).continuousOn
        (fun ζ hζ h0 => hz_not ((sub_eq_zero.mp (by simpa using h0)) ▸ hζ))
    have hinv_cont : ContinuousOn (fun ζ : ℂ => (ζ - z)⁻¹) Γ.trace :=
      (continuous_id.sub continuous_const).continuousOn.inv₀
        (fun ζ hζ h0 => hz_not ((sub_eq_zero.mp (by simpa using h0)) ▸ hζ))
    have hint_inv0 : Γ.integral (fun ζ => (ζ - z)⁻¹) = 0 := by
      unfold BookChain.Ind at hz_ind
      exact (mul_eq_zero.mp hz_ind).resolve_left (inv_ne_zero two_pi_I_ne_zero)
    dsimp [g₁, g₂]
    rw [BookChain.integral_congr Γ hcongr,
        BookChain.integral_sub Γ (g := fun ζ => f z * (ζ - z)⁻¹) hf_div_cont
          (continuousOn_const.mul hinv_cont),
        BookChain.integral_const_mul, hint_inv0, mul_zero, sub_zero]
  classical
  let h : ℂ → ℂ := fun z => if z ∈ Ω then g₁ z else g₂ z
  have hg₁_holo : HolomorphicOn g₁ Ω :=
    holomorphicOn_chainIntegral_dividedDifference hΩ hf Γ hΓ
  have hg₂_holo : HolomorphicOn g₂ (Γ.trace)ᶜ :=
    holomorphicOn_chainIntegral_div_sub Γ ((continuousOn_of_holomorphicOn hf).mono hΓ)
  have hh_on_Ω₁ : Set.EqOn h g₂ Ω₁ := by
    intro z hz₁
    dsimp [h]
    split_ifs with hzΩ
    · exact hagrees z ⟨hzΩ, hz₁⟩
    · rfl
  have hh_entire : HolomorphicOn h Set.univ := by
    intro z _
    rcases hcover z with hzΩ | hz₁
    · refine (hg₁_holo z hzΩ).congr_of_eventuallyEq ?_
      filter_upwards [hΩ.mem_nhds hzΩ] with w hw
      simp [h, hw]
    · refine (hg₂_holo z hz₁.1).congr_of_eventuallyEq ?_
      filter_upwards [hΩ₁_open.mem_nhds hz₁] with w hw
      exact hh_on_Ω₁ hw
  -- Outside `closedBall 0 R` (containing `Γ*`), every point lies in the unbounded component of
  -- `(Γ*)ᶜ`, hence in `Ω₁`, so `h = g₂` and `g₂(z) → 0` as `‖z‖ → ∞`.
  obtain ⟨R, hRpos, hRsub⟩ := Γ.isCompact_trace.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  have hext_in_Ω₁ : (Metric.closedBall (0 : ℂ) R)ᶜ ⊆ Ω₁ := by
    intro z hz_ext
    have hext_compl : (Metric.closedBall (0 : ℂ) R)ᶜ ⊆ (Γ.trace)ᶜ :=
      compl_subset_compl.mpr hRsub
    have hz_not : z ∉ Γ.trace := hext_compl hz_ext
    let U := bookComponent (Γ.trace)ᶜ z
    have hU_mem : U ∈ bookComponents (Γ.trace)ᶜ := ⟨z, hz_not, rfl⟩
    have hsub_U : (Metric.closedBall (0 : ℂ) R)ᶜ ⊆ U :=
      bookComponent_maximal hext_compl
        ((bookConnected_iff_isPreconnected _).mpr (isConnected_compl_closedBall 0 hRpos.le).2)
        hz_ext
    have hU_unbdd : ¬ Bornology.IsBounded U := by
      intro hbdd
      obtain ⟨B, _, hB⟩ := hbdd.subset_closedBall_lt 0 (0 : ℂ)
      let w : ℂ := ((max R B + 1 : ℝ) : ℂ)
      have hp : 0 < max R B + 1 := lt_of_lt_of_le hRpos (le_trans (le_max_left R B) (by linarith))
      have hw_ext : w ∈ (Metric.closedBall (0 : ℂ) R)ᶜ := by
        rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_zero_right]
        simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
        exact lt_of_le_of_lt (le_max_left R B) (by linarith)
      have hwB := hB (hsub_U hw_ext)
      rw [Metric.mem_closedBall, dist_zero_right] at hwB
      simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp] at hwB
      linarith [le_max_right R B]
    exact ⟨hz_not, BookChain.Ind_eq_zero_of_mem_unbounded_component_of_isCycle hcyc
      hU_mem hU_unbdd (mem_bookComponent hz_not)⟩
  -- Bound on `g₂ z` when `‖z‖ ≥ R + B` (`B > 0`)
  have hg₂_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ {z : ℂ} {B : ℝ}, 0 < B → R + B ≤ ‖z‖ →
      ‖g₂ z‖ ≤ C / B := by
    have hf_cont_Γ : ContinuousOn f Γ.trace := (continuousOn_of_holomorphicOn hf).mono hΓ
    clear hcyc hext hagrees hh_on_Ω₁ hh_entire hext_in_Ω₁ hg₁_holo hg₂_holo hΩ₁_open hcover
    induction Γ with
    | nil =>
      refine ⟨0, le_rfl, fun hB _ => ?_⟩
      simp [g₂]
    | cons γ Γ ih =>
      rw [BookChain.trace_cons] at hRsub hf_cont_Γ hΓ
      obtain ⟨C₂, hC₂_nn, hC₂⟩ := ih (subset_union_right.trans hΓ)
        (subset_union_right.trans hRsub) (hf_cont_Γ.mono subset_union_right)
      obtain ⟨w_max, _, hw_max⟩ :=
        γ.isCompact_trace.exists_isMaxOn γ.trace_nonempty (hf_cont_Γ.mono subset_union_left).norm
      let C₁ : ℝ := ‖f w_max‖ * pathLength γ.toBookCurve
      refine ⟨C₁ + C₂, add_nonneg (mul_nonneg (norm_nonneg _) γ.pathLength_nonneg) hC₂_nn, ?_⟩
      intro z B hB hz_norm
      have hγ_le : ‖pathIntegral (fun ζ => f ζ / (ζ - z)) γ.toBookCurve‖ ≤ C₁ / B := by
        have hzeta_dist : ∀ ζ ∈ γ.trace, B ≤ ‖ζ - z‖ := by
          intro ζ hζ
          have hζR : ‖ζ‖ ≤ R := by
            simpa [Metric.mem_closedBall] using hRsub (Or.inl hζ)
          have htri : ‖z‖ ≤ ‖ζ - z‖ + ‖ζ‖ := by
            calc ‖z‖ = ‖z - ζ + ζ‖ := by ring_nf
              _ ≤ ‖z - ζ‖ + ‖ζ‖ := norm_add_le _ _
              _ = ‖ζ - z‖ + ‖ζ‖ := by rw [norm_sub_rev]
          linarith
        have hcont_div : ContinuousOn (fun ζ => f ζ / (ζ - z)) γ.trace :=
          (hf_cont_Γ.mono subset_union_left).div
            (continuous_id.sub continuous_const).continuousOn
            (fun ζ hζ h0 => by have := hzeta_dist ζ hζ; rw [h0, norm_zero] at this; linarith)
        have hpt : ∀ ζ ∈ γ.trace, ‖f ζ / (ζ - z)‖ ≤ ‖f w_max‖ / B := by
          intro ζ hζ
          rw [norm_div]
          exact le_trans (div_le_div_of_nonneg_right (hw_max hζ) (norm_nonneg _))
            (div_le_div_of_nonneg_left (norm_nonneg _) hB (hzeta_dist ζ hζ))
        simpa [C₁, div_mul_eq_mul_div] using γ.norm_pathIntegral_le hcont_div hpt
      have hΓ_le := hC₂ (z := z) hB hz_norm
      calc ‖BookChain.integral (fun ζ => f ζ / (ζ - z)) (γ :: Γ)‖
          = ‖pathIntegral (fun ζ => f ζ / (ζ - z)) γ.toBookCurve +
              BookChain.integral (fun ζ => f ζ / (ζ - z)) Γ‖ := by simp [BookChain.integral_cons]
        _ ≤ ‖pathIntegral (fun ζ => f ζ / (ζ - z)) γ.toBookCurve‖ +
              ‖BookChain.integral (fun ζ => f ζ / (ζ - z)) Γ‖ := norm_add_le _ _
        _ ≤ C₁ / B + C₂ / B := add_le_add hγ_le hΓ_le
        _ = (C₁ + C₂) / B := (add_div C₁ C₂ B).symm
  obtain ⟨C, hC_nn, hC_bd⟩ := hg₂_bound
  have hh_cont : Continuous h :=
    continuous_iff_continuousAt.mpr fun z => (hh_entire z (mem_univ z)).continuousAt
  obtain ⟨z_max, _, hz_max⟩ := (isCompact_closedBall (0 : ℂ) (R + 1)).exists_isMaxOn
    (Metric.nonempty_closedBall.mpr (by linarith)) hh_cont.continuousOn.norm
  have hh_bdd : Bornology.IsBounded (Set.range h) := by
    rw [Metric.isBounded_range_iff]
    refine ⟨2 * max ‖h z_max‖ C + 1, fun z₁ z₂ => ?_⟩
    have hone : ∀ z : ℂ, ‖h z‖ ≤ max ‖h z_max‖ C := by
      intro z
      by_cases hz : z ∈ Metric.closedBall (0 : ℂ) (R + 1)
      · exact le_trans (hz_max hz) (le_max_left _ _)
      · have hz_norm : R + 1 < ‖z‖ := by
          simpa [Metric.mem_closedBall, not_le] using hz
        have hz_ext : z ∈ (Metric.closedBall (0 : ℂ) R)ᶜ := by
          rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_zero_right]
          linarith
        rw [hh_on_Ω₁ (hext_in_Ω₁ hz_ext)]
        have h1 := hC_bd (z := z) zero_lt_one hz_norm.le
        rw [div_one] at h1
        exact le_trans h1 (le_max_right _ _)
    rw [dist_eq_norm]
    calc ‖h z₁ - h z₂‖ ≤ ‖h z₁‖ + ‖h z₂‖ := norm_sub_le _ _
      _ ≤ max ‖h z_max‖ C + max ‖h z_max‖ C := add_le_add (hone z₁) (hone z₂)
      _ ≤ 2 * max ‖h z_max‖ C + 1 := by linarith
  obtain ⟨c, hc⟩ := liouville hh_entire hh_bdd
  -- Evaluate at `z = R + B` for `B > C / ε + 1` to see `c = 0`.
  have hc0 : c = 0 := by
    by_contra hc_ne
    have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc_ne
    let B : ℝ := C / (‖c‖ / 2) + 1
    have hB_pos : 0 < B := by positivity
    let zB : ℂ := ((R + B : ℝ) : ℂ)
    have hzB_pos : 0 < R + B := add_pos hRpos hB_pos
    have hzB_norm : ‖zB‖ = R + B := by
      change ‖((R + B : ℝ) : ℂ)‖ = R + B
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzB_pos]
    have hzB_ext : zB ∈ (Metric.closedBall (0 : ℂ) R)ᶜ := by
      rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_zero_right, hzB_norm]
      linarith
    have hval : c = g₂ zB := (hc zB).symm.trans (hh_on_Ω₁ (hext_in_Ω₁ hzB_ext))
    have hle := hC_bd (z := zB) hB_pos hzB_norm.ge
    rw [← hval] at hle
    have hlt_half : C / B ≤ ‖c‖ / 2 := by
      rw [div_le_iff₀ hB_pos]
      have hgt : C / (‖c‖ / 2) < B := by dsimp [B]; linarith
      have hmul := mul_lt_mul_of_pos_left hgt (half_pos hc_pos)
      rw [mul_div_cancel₀ _ (half_pos hc_pos).ne'] at hmul
      linarith
    linarith
  intro z hz
  have hh_z : h z = g₁ z := by simp [h, hz]
  dsimp [g₁] at hh_z
  rw [← hh_z, hc z, hc0]

/-- 10.35 (Global / homological Cauchy theorem and Cauchy integral formula for cycles):
Let `Ω` be any open set in `ℂ`, `f ∈ H(Ω)`, and `Γ` be a cycle in `Ω` such that `Ind_Γ(w) = 0` for
every `w ∉ Ω`. Then:
1. `(2πi)⁻¹ ∫_Γ f(ζ)/(ζ - z) dζ = f(z) * Ind_Γ(z)` for every `z ∈ Ω \ Γ*`;
2. `∫_Γ f(z) dz = 0`;
3. (Corollary) if `Γ₁, Γ₂` are cycles in `Ω` with `Ind_{Γ₁}(w) = Ind_{Γ₂}(w)` for every `w ∉ Ω`,
   then `∫_{Γ₁} f(z) dz = ∫_{Γ₂} f(z) dz`. -/
theorem theorem10_35 {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    (∀ {f : ℂ → ℂ}, HolomorphicOn f Ω →
      ∀ (Γ : BookChain), Γ.IsCycle → Γ.trace ⊆ Ω → (∀ w, w ∉ Ω → Γ.Ind w = 0) →
        (∀ z ∈ Ω, z ∉ Γ.trace →
          f z * Γ.Ind z =
            (2 * Real.pi * Complex.I)⁻¹ * Γ.integral (fun ζ => f ζ / (ζ - z))) ∧
        Γ.integral f = 0) ∧
    (∀ {f : ℂ → ℂ}, HolomorphicOn f Ω →
      ∀ (Γ₁ Γ₂ : BookChain), Γ₁.IsCycle → Γ₂.IsCycle →
        Γ₁.trace ⊆ Ω → Γ₂.trace ⊆ Ω →
        (∀ w, w ∉ Ω → Γ₁.Ind w = Γ₂.Ind w) →
        Γ₁.integral f = Γ₂.integral f) := by
  have hmain : ∀ {f : ℂ → ℂ}, HolomorphicOn f Ω →
      ∀ (Γ : BookChain), Γ.IsCycle → Γ.trace ⊆ Ω → (∀ w, w ∉ Ω → Γ.Ind w = 0) →
        (∀ z ∈ Ω, z ∉ Γ.trace →
          f z * Γ.Ind z =
            (2 * Real.pi * Complex.I)⁻¹ * Γ.integral (fun ζ => f ζ / (ζ - z))) ∧
        Γ.integral f = 0 := by
    intro f hf Γ hcyc hΓ hext
    refine ⟨?_, ?_⟩
    · intro z hz hz_not
      have h0 := chainIntegral_dividedDifference_eq_zero hΩ hf Γ hcyc hΓ hext z hz
      have hcongr : Set.EqOn (fun ζ => dividedDifference f ζ z)
          (fun ζ => f ζ / (ζ - z) - (fun ζ => f z * (ζ - z)⁻¹) ζ) Γ.trace := by
        intro ζ hζ
        dsimp only
        have hne : ζ ≠ z := fun h => hz_not (h ▸ hζ)
        rw [dividedDifference_of_ne hne, sub_div, div_eq_mul_inv (f z)]
      have hf_div_cont : ContinuousOn (fun ζ => f ζ / (ζ - z)) Γ.trace :=
        ((continuousOn_of_holomorphicOn hf).mono hΓ).div
          (continuous_id.sub continuous_const).continuousOn
          (fun ζ hζ h0 => hz_not ((sub_eq_zero.mp (by simpa using h0)) ▸ hζ))
      have hinv_cont : ContinuousOn (fun ζ : ℂ => (ζ - z)⁻¹) Γ.trace :=
        (continuous_id.sub continuous_const).continuousOn.inv₀
          (fun ζ hζ h0 => hz_not ((sub_eq_zero.mp (by simpa using h0)) ▸ hζ))
      rw [BookChain.integral_congr Γ hcongr,
          BookChain.integral_sub Γ (g := fun ζ => f z * (ζ - z)⁻¹) hf_div_cont
            (continuousOn_const.mul hinv_cont),
          BookChain.integral_const_mul, sub_eq_zero] at h0
      unfold BookChain.Ind
      rw [h0]
      ring
    · rcases Ω.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
      · cases Γ with
        | nil => simp
        | cons γ Γ' =>
          exfalso
          obtain ⟨w, hw⟩ := γ.trace_nonempty
          rw [BookChain.trace_cons] at hΓ
          exact hΓ (Or.inl hw)
      · let F : ℂ → ℂ := fun ζ => (ζ - z₀) * f ζ
        have hF_holo : HolomorphicOn F Ω :=
          fun ζ hζ => ((differentiableAt_id.sub_const z₀).mul (hf ζ hζ))
        have h0 := chainIntegral_dividedDifference_eq_zero hΩ hF_holo Γ hcyc hΓ hext z₀ hz₀
        have hF_dd : ∀ ζ ∈ Γ.trace, dividedDifference F ζ z₀ = f ζ := by
          intro ζ hζ
          by_cases hne : ζ = z₀
          · subst hne
            rw [dividedDifference_self]
            have hd : HasDerivAt F (1 * f ζ + (ζ - ζ) * deriv f ζ) ζ :=
              ((hasDerivAt_id ζ).sub_const ζ).mul (hf ζ hz₀).hasDerivAt
            simpa using hd.deriv
          · rw [dividedDifference_of_ne hne]
            dsimp [F]
            have hsub_ne : ζ - z₀ ≠ 0 := sub_ne_zero.mpr hne
            field_simp
            ring
        rwa [BookChain.integral_congr Γ hF_dd] at h0
  refine ⟨hmain, ?_⟩
  intro f hf Γ₁ Γ₂ hcyc₁ hcyc₂ hΓ₁ hΓ₂ hext_eq
  let Γ : BookChain := Γ₁ ++ Γ₂.neg
  have hcyc : Γ.IsCycle := BookChain.isCycle_append hcyc₁ (BookChain.isCycle_neg hcyc₂)
  have hΓ : Γ.trace ⊆ Ω := by
    simp only [Γ, BookChain.trace_append, BookChain.trace_neg]
    exact union_subset hΓ₁ hΓ₂
  have hext : ∀ w, w ∉ Ω → Γ.Ind w = 0 := by
    intro w hw
    have hw₂ : w ∉ Γ₂.trace := fun h => hw (hΓ₂ h)
    simp only [Γ, BookChain.Ind_append, BookChain.Ind_neg Γ₂ hw₂, hext_eq w hw, add_neg_cancel]
  have h0 := (hmain hf Γ hcyc hΓ hext).2
  simp only [Γ, BookChain.integral_append,
    BookChain.integral_neg Γ₂ ((continuousOn_of_holomorphicOn hf).mono hΓ₂)] at h0
  linear_combination h0

/-- 10.36(a): for any convex set `Ω ⊆ ℂ` and any cycle `Γ` in `Ω`, `Ind_Γ(w) = 0` for every
`w ∉ Ω` (since the ray from `z₀ ∈ Γ*` through `w` lies in `Ωᶜ ⊆ (Γ*)ᶜ` and is unbounded). -/
theorem theorem10_36_convex_exterior_Ind {Ω : Set ℂ} (hconv : Convex ℝ Ω)
    (Γ : BookChain) (hcyc : Γ.IsCycle) (hΓ : Γ.trace ⊆ Ω) :
    ∀ w, w ∉ Ω → Γ.Ind w = 0 := by
  intro w hw
  cases Γ with
  | nil => simp
  | cons γ₀ Γ' =>
    let z₀ : ℂ := γ₀.toFun γ₀.α
    have hz₀_tr : z₀ ∈ BookChain.trace (γ₀ :: Γ') := by
      rw [BookChain.trace_cons]; exact Or.inl γ₀.start_mem_trace
    have hz₀_Ω : z₀ ∈ Ω := hΓ hz₀_tr
    have hw_ne : w ≠ z₀ := fun h => hw (h ▸ hz₀_Ω)
    have hnorm_pos : 0 < ‖w - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw_ne)
    let ray : Set ℂ := (fun t : ℝ => w + t • (w - z₀)) '' Ici (0 : ℝ)
    have hw_ray : w ∈ ray := ⟨0, Set.mem_Ici.mpr le_rfl, by simp⟩
    have hray_pre : IsPreconnected ray :=
      isPreconnected_Ici.image _
        (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
    have hray_compl : ray ⊆ (BookChain.trace (γ₀ :: Γ'))ᶜ := by
      rintro _ ⟨t, ht, rfl⟩ htr
      have hp_Ω : w + t • (w - z₀) ∈ Ω := hΓ htr
      rcases eq_or_lt_of_le (mem_Ici.mp ht) with rfl | ht_pos
      · simp at hp_Ω; exact hw hp_Ω
      · have h1t : 0 < 1 + t := by linarith
        let u : ℝ := 1 / (1 + t)
        let v : ℝ := t / (1 + t)
        have hu : 0 ≤ u := div_nonneg zero_le_one h1t.le
        have hv : 0 ≤ v := div_nonneg ht_pos.le h1t.le
        have huv : u + v = 1 := by dsimp [u, v]; field_simp
        have hcomb : u • (w + t • (w - z₀)) + v • z₀ = w := by
          have h1tC : (1 + (t : ℂ)) ≠ 0 := by exact_mod_cast h1t.ne'
          dsimp [u, v]
          simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one]
          field_simp
          ring
        exact hw (hcomb ▸ hconv hp_Ω hz₀_Ω hu hv huv)
    have hw_not_tr : w ∉ BookChain.trace (γ₀ :: Γ') := hray_compl hw_ray
    let U := bookComponent (BookChain.trace (γ₀ :: Γ'))ᶜ w
    have hU_mem : U ∈ bookComponents (BookChain.trace (γ₀ :: Γ'))ᶜ := ⟨w, hw_not_tr, rfl⟩
    have hray_U : ray ⊆ U :=
      bookComponent_maximal hray_compl ((bookConnected_iff_isPreconnected _).mpr hray_pre) hw_ray
    have hU_unbdd : ¬ Bornology.IsBounded U := by
      intro hbdd
      obtain ⟨B, hB_pos, hB⟩ := hbdd.subset_closedBall_lt 0 w
      let t : ℝ := (B + 1) / ‖w - z₀‖
      have ht_nn : 0 ≤ t := div_nonneg (by linarith) hnorm_pos.le
      have hp_U : w + t • (w - z₀) ∈ U := hray_U ⟨t, ht_nn, rfl⟩
      have hp_B := hB hp_U
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg ht_nn, div_mul_cancel₀ _ hnorm_pos.ne'] at hp_B
      linarith
    exact BookChain.Ind_eq_zero_of_mem_unbounded_component_of_isCycle hcyc
      hU_mem hU_unbdd (mem_bookComponent hw_not_tr)

/-- 10.36(b) (Multi-hole circle replacement): suppose `Ω` is open, `r₀ > 0`, `r i > 0` (`i : Fin m`)
are radii such that the closed discs `closedDisc (a i) (r i)` are pairwise disjoint subsets of
`disc a₀ r₀` and `closedDisc a₀ r₀ \ ⋃ i, disc (a i) (r i) ⊆ Ω`. Then for every `f ∈ H(Ω)`,
`∫_{C(a₀, r₀)} f = ∑ᵢ ∫_{C(aᵢ, rᵢ)} f` (as `BookPath` integrals). -/
theorem theorem10_36_multi_circle {Ω : Set ℂ} (hΩ : IsOpen Ω) {m : ℕ}
    (a₀ : ℂ) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (a : Fin m → ℂ) {r : Fin m → ℝ} (hr : ∀ i, 0 < r i)
    (hsub_disc : ∀ i, closedDisc (a i) (r i) ⊆ disc a₀ r₀)
    (hdisj : Pairwise fun i j => Disjoint (closedDisc (a i) (r i)) (closedDisc (a j) (r j)))
    (hΩ_contain : closedDisc a₀ r₀ \ (⋃ i : Fin m, disc (a i) (r i)) ⊆ Ω)
    {f : ℂ → ℂ} (hf : HolomorphicOn f Ω) :
    pathIntegral f (positivelyOrientedCircle a₀ r₀ hr₀).toBookCurve =
      ∑ i : Fin m, pathIntegral f (positivelyOrientedCircle (a i) (r i) (hr i)).toBookCurve := by
  have hsub_cb : ∀ i, Metric.closedBall (a i) (r i) ⊆ disc a₀ r₀ :=
    fun i => closedDisc_eq_closedBall (a i) (hr i) ▸ hsub_disc i
  have hdisj_cb : Pairwise fun i j =>
      Disjoint (Metric.closedBall (a i) (r i)) (Metric.closedBall (a j) (r j)) :=
    fun i j hij => by
      simpa [closedDisc_eq_closedBall (a i) (hr i), closedDisc_eq_closedBall (a j) (hr j)] using
        hdisj hij
  have hΩ_cb : Metric.closedBall a₀ r₀ \ (⋃ i : Fin m, disc (a i) (r i)) ⊆ Ω := by
    rwa [← closedDisc_eq_closedBall a₀ hr₀]
  let γ₀ := positivelyOrientedCircle a₀ r₀ hr₀
  let γ : Fin m → BookPath := fun i => positivelyOrientedCircle (a i) (r i) (hr i)
  let Γ₂ : BookChain := (List.finRange m).map γ
  have hγ₀_tr : γ₀.trace ⊆ Ω := by
    rw [positivelyOrientedCircle_trace a₀ hr₀]
    intro z hz
    refine hΩ_cb ⟨Metric.sphere_subset_closedBall hz, ?_⟩
    rw [mem_iUnion]
    rintro ⟨i, hzi⟩
    have hz₀ : z ∈ disc a₀ r₀ := hsub_cb i (Metric.ball_subset_closedBall hzi)
    rw [disc, Metric.mem_ball] at hz₀
    rw [Metric.mem_sphere] at hz
    linarith
  have hγ_tr : ∀ i : Fin m, (γ i).trace ⊆ Ω := by
    intro i
    dsimp [γ]
    rw [positivelyOrientedCircle_trace (a i) (hr i)]
    intro z hz
    refine hΩ_cb ⟨Metric.ball_subset_closedBall (hsub_cb i (Metric.sphere_subset_closedBall hz)), ?_⟩
    rw [mem_iUnion]
    rintro ⟨j, hzj⟩
    by_cases hij : i = j
    · subst hij
      rw [disc, Metric.mem_ball] at hzj
      rw [Metric.mem_sphere] at hz
      linarith
    · exact Set.disjoint_left.mp (hdisj_cb hij)
        (Metric.sphere_subset_closedBall hz) (Metric.ball_subset_closedBall hzj)
  have hΓ₂_cyc : Γ₂.IsCycle := by
    refine BookChain.isCycle_of_forall_isClosed ?_
    intro σ hσ
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hσ
    exact positivelyOrientedCircle_isClosed (a i) (hr i)
  have hΓ₂_tr : Γ₂.trace ⊆ Ω := by
    intro z hz
    simp only [Γ₂, BookChain.trace, List.mem_map, List.mem_finRange, true_and,
      iUnion_exists, iUnion_iUnion_eq', mem_iUnion] at hz
    obtain ⟨i, hi⟩ := hz
    exact hγ_tr i hi
  -- Helper: `Γ₂.Ind w = ∑ i, Ind (γ i) w` and `Γ₂.integral f = ∑ i, pathIntegral f (γ i)`
  have hlist_ind : ∀ (L : List (Fin m)) (w : ℂ),
      BookChain.Ind (L.map γ) w = (L.map (fun i => Ind (γ i).toBookCurve w)).sum := by
    intro L w
    induction L with
    | nil => simp
    | cons i L ih => simp [ih]
  have hlist_int : ∀ (L : List (Fin m)),
      BookChain.integral f (L.map γ) =
        (L.map (fun i => pathIntegral f (γ i).toBookCurve)).sum := by
    intro L
    induction L with
    | nil => simp
    | cons i L ih => simp [ih]
  have hext_eq : ∀ w, w ∉ Ω → BookChain.Ind [γ₀] w = Γ₂.Ind w := by
    intro w hw
    rw [BookChain.Ind_singleton, hlist_ind, ← Fin.sum_univ_def]
    by_cases hw_c0 : w ∈ Metric.closedBall a₀ r₀
    · have hw_in_hole : w ∈ ⋃ i : Fin m, disc (a i) (r i) := by
        by_contra hnot
        exact hw (hΩ_cb ⟨hw_c0, hnot⟩)
      rw [mem_iUnion] at hw_in_hole
      obtain ⟨k, hwk⟩ := hw_in_hole
      have hw_d0 : w ∈ disc a₀ r₀ := hsub_cb k (Metric.ball_subset_closedBall hwk)
      rw [Ind_positivelyOrientedCircle_inside hr₀ hw_d0]
      have hsum_eq : (∑ i : Fin m, Ind (γ i).toBookCurve w) = Ind (γ k).toBookCurve w := by
        refine Finset.sum_eq_single k (fun j _ hjk => ?_) (fun hk => (hk (Finset.mem_univ k)).elim)
        have hw_not_cj : w ∉ Metric.closedBall (a j) (r j) :=
          Set.disjoint_left.mp (hdisj_cb (Ne.symm hjk)) (Metric.ball_subset_closedBall hwk)
        rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hw_not_cj
        exact Ind_positivelyOrientedCircle_outside (hr j) hw_not_cj
      rw [hsum_eq, Ind_positivelyOrientedCircle_inside (hr k) hwk]
    · rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hw_c0
      rw [Ind_positivelyOrientedCircle_outside hr₀ hw_c0]
      symm
      refine Finset.sum_eq_zero fun i _ => ?_
      have hw_not_ci : w ∉ Metric.closedBall (a i) (r i) := fun hci => by
        have hd : dist w a₀ ≤ r₀ :=
          Metric.mem_closedBall.mp (Metric.ball_subset_closedBall (hsub_cb i hci))
        rw [dist_eq_norm] at hd
        linarith
      rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hw_not_ci
      exact Ind_positivelyOrientedCircle_outside (hr i) hw_not_ci
  have heq := (theorem10_35 hΩ).2 hf [γ₀] Γ₂
    (BookChain.isCycle_singleton_of_isClosed (positivelyOrientedCircle_isClosed a₀ hr₀))
    hΓ₂_cyc (by simpa using hγ₀_tr) hΓ₂_tr hext_eq
  simpa [Γ₂, hlist_int, ← Fin.sum_univ_def] using heq

/-- 10.36(b) (Explicit three-hole circle example displayed in Rudin p. 221):
if three pairwise disjoint closed discs `closedDisc a₁ r₁`, `closedDisc a₂ r₂`, `closedDisc a₃ r₃`
lie inside `disc a₀ r₀` and `closedDisc a₀ r₀ \ (disc a₁ r₁ ∪ disc a₂ r₂ ∪ disc a₃ r₃) ⊆ Ω`, then
`∫_{γ₀} f = ∫_{γ₁} f + ∫_{γ₂} f + ∫_{γ₃} f` for every `f ∈ H(Ω)`. -/
theorem theorem10_36_three_circles {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (a₀ a₁ a₂ a₃ : ℂ) {r₀ r₁ r₂ r₃ : ℝ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃)
    (hsub₁ : closedDisc a₁ r₁ ⊆ disc a₀ r₀)
    (hsub₂ : closedDisc a₂ r₂ ⊆ disc a₀ r₀)
    (hsub₃ : closedDisc a₃ r₃ ⊆ disc a₀ r₀)
    (hd₁₂ : Disjoint (closedDisc a₁ r₁) (closedDisc a₂ r₂))
    (hd₁₃ : Disjoint (closedDisc a₁ r₁) (closedDisc a₃ r₃))
    (hd₂₃ : Disjoint (closedDisc a₂ r₂) (closedDisc a₃ r₃))
    (hΩ_contain : closedDisc a₀ r₀ \ (disc a₁ r₁ ∪ disc a₂ r₂ ∪ disc a₃ r₃) ⊆ Ω)
    {f : ℂ → ℂ} (hf : HolomorphicOn f Ω) :
    pathIntegral f (positivelyOrientedCircle a₀ r₀ hr₀).toBookCurve =
      pathIntegral f (positivelyOrientedCircle a₁ r₁ hr₁).toBookCurve +
      pathIntegral f (positivelyOrientedCircle a₂ r₂ hr₂).toBookCurve +
      pathIntegral f (positivelyOrientedCircle a₃ r₃ hr₃).toBookCurve := by
  let a : Fin 3 → ℂ := ![a₁, a₂, a₃]
  let r : Fin 3 → ℝ := ![r₁, r₂, r₃]
  have hr : ∀ i : Fin 3, 0 < r i := by intro i; fin_cases i <;> assumption
  have hsub : ∀ i : Fin 3, closedDisc (a i) (r i) ⊆ disc a₀ r₀ := by
    intro i; fin_cases i <;> assumption
  have hdisj : Pairwise fun i j : Fin 3 => Disjoint (closedDisc (a i) (r i)) (closedDisc (a j) (r j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
    · exact hd₁₂
    · exact hd₁₃
    · exact hd₁₂.symm
    · exact hd₂₃
    · exact hd₁₃.symm
    · exact hd₂₃.symm
  have hΩ' : closedDisc a₀ r₀ \ (⋃ i : Fin 3, disc (a i) (r i)) ⊆ Ω := by
    intro z hz
    refine hΩ_contain ⟨hz.1, ?_⟩
    intro h
    rcases h with (h | h) | h
    · exact hz.2 (mem_iUnion.mpr ⟨0, h⟩)
    · exact hz.2 (mem_iUnion.mpr ⟨1, h⟩)
    · exact hz.2 (mem_iUnion.mpr ⟨2, h⟩)
  have h := theorem10_36_multi_circle hΩ a₀ hr₀ a hr hsub hdisj hΩ' hf
  simpa [Fin.sum_univ_three, a, r, add_assoc] using h

/-! ### 10.38, 10.39 & 10.40: Free homotopy of closed curves, simple connectivity, closeness invariance, and homotopy invariance of index -/

/-- 10.38: Rudin's `Ω`-homotopy of closed curves with parameter interval `I = [0, 1]`, via a
continuous map `H : I × I → Ω` satisfying `H(s, 0) = γ₀(s)`, `H(s, 1) = γ₁(s)`, and
`H(0, t) = H(1, t)` (allowing the common start/end point to move during the deformation). -/
def AreFreeLoopHomotopicIn {X : Type*} [TopologicalSpace X] (Ω : Set X) (γ₀ γ₁ : ℝ → X) : Prop :=
  ContinuousOn γ₀ (Icc 0 1) ∧ ContinuousOn γ₁ (Icc 0 1) ∧
  γ₀ '' Icc 0 1 ⊆ Ω ∧ γ₁ '' Icc 0 1 ⊆ Ω ∧
  γ₀ 0 = γ₀ 1 ∧ γ₁ 0 = γ₁ 1 ∧
  ∃ H : ℝ × ℝ → X,
    ContinuousOn H (Icc 0 1 ×ˢ Icc 0 1) ∧
    H '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ Ω ∧
    (∀ s ∈ Icc 0 1, H (s, 0) = γ₀ s) ∧
    (∀ s ∈ Icc 0 1, H (s, 1) = γ₁ s) ∧
    (∀ t ∈ Icc 0 1, H (0, t) = H (1, t))

theorem areFreeLoopHomotopicIn_refl {X : Type*} [TopologicalSpace X] {Ω : Set X} {γ : ℝ → X}
    (hc : ContinuousOn γ (Icc 0 1)) (hΩ : γ '' Icc 0 1 ⊆ Ω) (hcl : γ 0 = γ 1) :
    AreFreeLoopHomotopicIn Ω γ γ := by
  refine ⟨hc, hc, hΩ, hΩ, hcl, hcl, fun p => γ p.1,
    hc.comp continuousOn_fst (fun p hp => hp.1), ?_,
    fun s _ => rfl, fun s _ => rfl, fun _ _ => hcl⟩
  rintro _ ⟨p, hp, rfl⟩
  exact hΩ ⟨p.1, hp.1, rfl⟩

theorem areFreeLoopHomotopicIn_symm {X : Type*} [TopologicalSpace X] {Ω : Set X} {γ₀ γ₁ : ℝ → X}
    (h : AreFreeLoopHomotopicIn Ω γ₀ γ₁) :
    AreFreeLoopHomotopicIn Ω γ₁ γ₀ := by
  obtain ⟨hc₀, hc₁, hΩ₀, hΩ₁, hcl₀, hcl₁, H, hHc, hHΩ, hH0, hH1, hHloop⟩ := h
  refine ⟨hc₁, hc₀, hΩ₁, hΩ₀, hcl₁, hcl₀, fun p => H (p.1, 1 - p.2), ?_, ?_,
    fun s hs => by simpa using hH1 s hs,
    fun s hs => by simpa using hH0 s hs,
    fun t ht => hHloop (1 - t) ⟨sub_nonneg.mpr ht.2, sub_le_self 1 ht.1⟩⟩
  · refine hHc.comp (continuousOn_fst.prodMk (continuousOn_const.sub continuousOn_snd)) ?_
    exact fun p hp => ⟨hp.1, sub_nonneg.mpr hp.2.2, sub_le_self 1 hp.2.1⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact hHΩ ⟨(p.1, 1 - p.2), ⟨hp.1, sub_nonneg.mpr hp.2.2, sub_le_self 1 hp.2.1⟩, rfl⟩

theorem areFreeLoopHomotopicIn_trans {X : Type*} [TopologicalSpace X] {Ω : Set X}
    {γ₀ γ₁ γ₂ : ℝ → X}
    (h₀₁ : AreFreeLoopHomotopicIn Ω γ₀ γ₁) (h₁₂ : AreFreeLoopHomotopicIn Ω γ₁ γ₂) :
    AreFreeLoopHomotopicIn Ω γ₀ γ₂ := by
  obtain ⟨hc₀, _, hΩ₀, _, hcl₀, _, H₁, hH₁c, hH₁Ω, hH₁0, hH₁1, hH₁loop⟩ := h₀₁
  obtain ⟨_, hc₂, _, hΩ₂, _, hcl₂, H₂, hH₂c, hH₂Ω, hH₂0, hH₂1, hH₂loop⟩ := h₁₂
  let H : ℝ × ℝ → X := fun p => if p.2 ≤ 1 / 2 then H₁ (p.1, 2 * p.2) else H₂ (p.1, 2 * p.2 - 1)
  have hHc : ContinuousOn H (Icc 0 1 ×ˢ Icc 0 1) := by
    let A : Set (ℝ × ℝ) := (Icc 0 1 ×ˢ Icc 0 1) ∩ {p | p.2 ≤ 1 / 2}
    let B : Set (ℝ × ℝ) := (Icc 0 1 ×ˢ Icc 0 1) ∩ {p | 1 / 2 ≤ p.2}
    have hHA : ContinuousOn (fun p : ℝ × ℝ => H₁ (p.1, 2 * p.2)) A :=
      hH₁c.comp (continuousOn_fst.prodMk (continuousOn_const.mul continuousOn_snd))
        fun p hp => by
          have hp2 : p.2 ≤ 1 / 2 := hp.2
          exact ⟨hp.1.1, by dsimp; linarith [hp.1.2.1], by dsimp; linarith [hp2]⟩
    have hHB : ContinuousOn (fun p : ℝ × ℝ => H₂ (p.1, 2 * p.2 - 1)) B :=
      hH₂c.comp (continuousOn_fst.prodMk ((continuousOn_const.mul continuousOn_snd).sub continuousOn_const))
        fun p hp => by
          have hp2 : 1 / 2 ≤ p.2 := hp.2
          exact ⟨hp.1.1, by dsimp; linarith [hp2], by dsimp; linarith [hp.1.2.2]⟩
    have hHA' : ContinuousOn H A := hHA.congr fun q hq => by
      dsimp [H]
      split_ifs with hle
      · rfl
      · exfalso; have hq2 : q.2 ≤ 1 / 2 := hq.2; linarith [not_le.mp hle]
    have hHB' : ContinuousOn H B := hHB.congr fun q hq => by
      dsimp [H]
      split_ifs with hle
      · have hq2 : q.2 = 1 / 2 := le_antisymm hle hq.2
        rw [hq2]; norm_num
        exact (hH₁1 q.1 hq.1.1).trans (hH₂0 q.1 hq.1.1).symm
      · rfl
    intro p hp
    by_cases hlt : p.2 < 1 / 2
    · exact (hHA' p ⟨hp, hlt.le⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset
          (inter_mem_nhdsWithin _ ((isOpen_lt continuous_snd continuous_const).mem_nhds hlt))
          fun q hq => by have hqlt : q.2 < 1 / 2 := hq.2; exact ⟨hq.1, hqlt.le⟩)
    · by_cases hgt : 1 / 2 < p.2
      · exact (hHB' p ⟨hp, hgt.le⟩).mono_of_mem_nhdsWithin
          (Filter.mem_of_superset
            (inter_mem_nhdsWithin _ ((isOpen_lt continuous_const continuous_snd).mem_nhds hgt))
            fun q hq => by have hqgt : 1 / 2 < q.2 := hq.2; exact ⟨hq.1, hqgt.le⟩)
      · have hp2 : p.2 = 1 / 2 := le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
        have hsup : nhdsWithin p (Icc 0 1 ×ˢ Icc 0 1) = nhdsWithin p A ⊔ nhdsWithin p B := by
          have hunion : Icc 0 1 ×ˢ Icc 0 1 = A ∪ B := by
            ext q; simp only [A, B, mem_union, mem_inter_iff, mem_ofPred_eq]
            exact ⟨fun hq => (le_total q.2 (1 / 2)).elim (fun h => Or.inl ⟨hq, h⟩)
              (fun h => Or.inr ⟨hq, h⟩), fun hq => hq.elim And.left And.left⟩
          conv_lhs => rw [hunion]
          exact nhdsWithin_union p A B
        rw [ContinuousWithinAt, hsup, tendsto_sup]
        exact ⟨hHA' p ⟨hp, hp2.le⟩, hHB' p ⟨hp, hp2.ge⟩⟩
  refine ⟨hc₀, hc₂, hΩ₀, hΩ₂, hcl₀, hcl₂, H, hHc, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    dsimp [H]
    split_ifs with hle
    · exact hH₁Ω ⟨(p.1, 2 * p.2), ⟨hp.1, by dsimp; linarith [hp.2.1], by dsimp; linarith [hle]⟩, rfl⟩
    · exact hH₂Ω ⟨(p.1, 2 * p.2 - 1), ⟨hp.1, by dsimp; linarith [not_le.mp hle], by dsimp; linarith [hp.2.2]⟩, rfl⟩
  · intro s hs
    dsimp [H]
    norm_num
    exact hH₁0 s hs
  · intro s hs
    dsimp [H]
    norm_num
    exact hH₂1 s hs
  · intro t ht
    dsimp [H]
    split_ifs with hle
    · exact hH₁loop (2 * t) ⟨by linarith [ht.1], by linarith [hle]⟩
    · exact hH₂loop (2 * t - 1) ⟨by linarith [not_le.mp hle], by linarith [ht.2]⟩

/-- 10.38: a closed curve on `[0, 1]` is null-homotopic in `Ω` if it is `Ω`-homotopic to a constant
curve in `Ω`. -/
def IsNullHomotopicIn {X : Type*} [TopologicalSpace X] (Ω : Set X) (γ : ℝ → X) : Prop :=
  ∃ c ∈ Ω, AreFreeLoopHomotopicIn Ω γ (fun _ => c)

/-- Affine normalization of an arbitrary-interval `BookCurve` to `[0, 1]` (`s ↦ γ((1 - s) α + s β)`). -/
def BookCurve.toUnitLoop {X : Type*} [TopologicalSpace X] (γ : BookCurve X) : ℝ → X :=
  fun s => γ.toFun ((1 - s) * γ.α + s * γ.β)

/-- Free homotopy of arbitrary-interval closed `BookCurve`s in `Ω` via their `[0, 1]` normalizations
(coinciding with `AreFreeLoopHomotopicIn` when `[α, β] = [0, 1]`). -/
def BookCurve.HomotopicIn {X : Type*} [TopologicalSpace X] (Ω : Set X)
    (γ₀ γ₁ : BookCurve X) : Prop :=
  AreFreeLoopHomotopicIn Ω γ₀.toUnitLoop γ₁.toUnitLoop

/-- 10.38: a region `Ω ⊆ ℂ` is simply connected if every closed curve in `Ω` is null-homotopic in `Ω`. -/
def BookSimplyConnected (Ω : Set ℂ) : Prop :=
  IsRegion Ω ∧ ∀ γ : ℝ → ℂ,
    ContinuousOn γ (Icc 0 1) → γ '' Icc 0 1 ⊆ Ω → γ 0 = γ 1 → IsNullHomotopicIn Ω γ

/-- 10.38 (Theorem): every convex region `Ω ⊆ ℂ` is simply connected. -/
theorem theorem10_38 {Ω : Set ℂ} (hΩ : IsRegion Ω) (hconv : Convex ℝ Ω) :
    BookSimplyConnected Ω := by
  refine ⟨hΩ, fun γ hγc hγΩ hγcl => ?_⟩
  obtain ⟨z₀, hz₀⟩ := hΩ.2.nonempty
  refine ⟨z₀, hz₀, hγc, continuousOn_const, hγΩ, ?_, hγcl, rfl,
    fun p => (1 - p.2 : ℝ) • γ p.1 + p.2 • z₀, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨_, _, rfl⟩; exact hz₀
  · exact (((continuousOn_const.sub continuousOn_snd).smul
      (hγc.comp continuousOn_fst fun p hp => hp.1)).add
      (continuousOn_snd.smul continuousOn_const))
  · rintro _ ⟨p, hp, rfl⟩
    exact hconv (hγΩ ⟨p.1, hp.1, rfl⟩) hz₀ (sub_nonneg.mpr hp.2.2) hp.2.1 (by ring)
  · intro s _; simp
  · intro s _; simp
  · intro t _; simp [hγcl]

/-- 10.39 (Closeness invariance of index): suppose `γ₀` and `γ₁` are closed paths with the same
parameter interval `[α, β]`, and `|γ₁(t) - γ₀(t)| < |z - γ₀(t)|` for every `t ∈ [α, β]`.
Then `z ∉ γ₀*`, `z ∉ γ₁*`, and `Ind_{γ₁}(z) = Ind_{γ₀}(z)`. -/
theorem theorem10_39 (γ₀ γ₁ : BookPath)
    (hα : γ₁.α = γ₀.α) (hβ : γ₁.β = γ₀.β)
    (hcl₀ : γ₀.IsClosed) (hcl₁ : γ₁.IsClosed) (z : ℂ)
    (hclose : ∀ t ∈ Icc γ₀.α γ₀.β, ‖γ₁.toFun t - γ₀.toFun t‖ < ‖z - γ₀.toFun t‖) :
    z ∉ γ₀.trace ∧ z ∉ γ₁.trace ∧ Ind γ₁.toBookCurve z = Ind γ₀.toBookCurve z := by
  have hpos₀ : ∀ t ∈ Icc γ₀.α γ₀.β, 0 < ‖z - γ₀.toFun t‖ :=
    fun t ht => lt_of_le_of_lt (norm_nonneg _) (hclose t ht)
  have hne₀ : ∀ t ∈ Icc γ₀.α γ₀.β, γ₀.toFun t - z ≠ 0 := fun t ht h0 => by
    have := hpos₀ t ht
    rw [norm_sub_rev, h0, norm_zero] at this
    linarith
  have hpos₁ : ∀ t ∈ Icc γ₀.α γ₀.β, 0 < ‖z - γ₁.toFun t‖ := fun t ht => by
    have htri : ‖z - γ₀.toFun t‖ ≤ ‖z - γ₁.toFun t‖ + ‖γ₁.toFun t - γ₀.toFun t‖ := by
      simpa using norm_add_le (z - γ₁.toFun t) (γ₁.toFun t - γ₀.toFun t)
    linarith [hclose t ht]
  have hne₁ : ∀ t ∈ Icc γ₀.α γ₀.β, γ₁.toFun t - z ≠ 0 := fun t ht h0 => by
    have := hpos₁ t ht
    rw [norm_sub_rev, h0, norm_zero] at this
    linarith
  have hz₀ : z ∉ γ₀.trace := by
    rintro ⟨t, ht, htz⟩
    exact hne₀ t ht (sub_eq_zero.mpr htz)
  have hz₁ : z ∉ γ₁.trace := by
    rintro ⟨t, ht, htz⟩
    rw [hα, hβ] at ht
    exact hne₁ t ht (sub_eq_zero.mpr htz)
  refine ⟨hz₀, hz₁, ?_⟩
  -- Construct `γ_quot(t) = (γ₁(t) - z) / (γ₀(t) - z)` on `[γ₀.α, γ₀.β]` with trace in `disc 1 1`.
  let g : ℝ → ℂ := fun t => (γ₁.toFun t - z) / (γ₀.toFun t - z)
  have hγ₁_cont : ContinuousOn γ₁.toFun (Icc γ₀.α γ₀.β) := hα ▸ hβ ▸ γ₁.continuousOn
  have hg_cont : ContinuousOn g (Icc γ₀.α γ₀.β) :=
    (hγ₁_cont.sub continuousOn_const).div (γ₀.continuousOn.sub continuousOn_const) hne₀
  obtain ⟨n₀, s₀, d₀, hs₀, hs₀0, hs₀n, hd₀cont, hd₀⟩ := γ₀.piecewiseC1
  obtain ⟨n₁, s₁, d₁, hs₁, hs₁0, hs₁n, hd₁cont, hd₁⟩ := γ₁.piecewiseC1
  have hs₁0' : s₁ 0 = γ₀.α := hs₁0.trans hα
  have hs₁n' : s₁ (Fin.last n₁) = γ₀.β := hs₁n.trans hβ
  let S : Finset ℝ := Finset.univ.image s₀ ∪ Finset.univ.image s₁
  have hg_pc1 : IsPiecewiseC1 ⟨γ₀.α, γ₀.β, γ₀.lt_endpoints, g, hg_cont⟩ := by
    refine isPiecewiseC1_of_finset ⟨γ₀.α, γ₀.β, γ₀.lt_endpoints, g, hg_cont⟩ S
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hs₀0⟩))
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Fin.last n₀, Finset.mem_univ _, hs₀n⟩))
      ?_ ?_
    · intro x hx
      simp only [S, Finset.coe_union, Finset.coe_image, Finset.coe_univ, image_univ,
        mem_union, mem_range] at hx
      rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact ⟨hs₀0 ▸ hs₀.monotone (Fin.zero_le i), hs₀n ▸ hs₀.monotone (Fin.le_last i)⟩
      · exact ⟨hs₁0' ▸ hs₁.monotone (Fin.zero_le i), hs₁n' ▸ hs₁.monotone (Fin.le_last i)⟩
    · intro a b ha hab hb hdisj
      have hdisj₀ : Disjoint (Set.range s₀) (Ioo a b) := by
        rw [Set.disjoint_left]
        rintro x ⟨i, rfl⟩ hx
        exact Set.disjoint_left.mp hdisj
          (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))) hx
      have hdisj₁ : Disjoint (Set.range s₁) (Ioo a b) := by
        rw [Set.disjoint_left]
        rintro x ⟨i, rfl⟩ hx
        exact Set.disjoint_left.mp hdisj
          (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))) hx
      obtain ⟨i₀, hia₀, hib₀⟩ := exists_piece_containing_interval hs₀ (hs₀0 ▸ ha) hab (hs₀n ▸ hb) hdisj₀
      obtain ⟨i₁, hia₁, hib₁⟩ := exists_piece_containing_interval hs₁ (hs₁0' ▸ ha) hab (hs₁n' ▸ hb) hdisj₁
      let hsub_ab : Icc a b ⊆ Icc γ₀.α γ₀.β := Icc_subset_Icc ha hb
      let dg : ℝ → ℂ := fun t =>
        (d₁ i₁ t * (γ₀.toFun t - z) - (γ₁.toFun t - z) * d₀ i₀ t) / (γ₀.toFun t - z) ^ 2
      have hdg_cont : ContinuousOn dg (Icc a b) :=
        (((hd₁cont i₁).mono (Icc_subset_Icc hia₁ hib₁)).mul
          ((γ₀.continuousOn.mono hsub_ab).sub continuousOn_const) |>.sub
          (((hγ₁_cont.mono hsub_ab).sub continuousOn_const).mul
            ((hd₀cont i₀).mono (Icc_subset_Icc hia₀ hib₀)))).div
          (((γ₀.continuousOn.mono hsub_ab).sub continuousOn_const).pow 2)
          (fun t ht => pow_ne_zero 2 (hne₀ t (hsub_ab ht)))
      refine ⟨dg, hdg_cont, fun t ht => ?_⟩
      have ht_outer : t ∈ Ioo γ₀.α γ₀.β := ⟨lt_of_le_of_lt ha ht.1, lt_of_lt_of_le ht.2 hb⟩
      have hd₀_at : HasDerivAt (fun u => γ₀.toFun u - z) (d₀ i₀ t) t :=
        ((hd₀ i₀ t ⟨lt_of_le_of_lt hia₀ ht.1, lt_of_lt_of_le ht.2 hib₀⟩).hasDerivAt
          (Icc_mem_nhds ht_outer.1 ht_outer.2)).sub_const z
      have hd₁_within := hd₁ i₁ t ⟨lt_of_le_of_lt hia₁ ht.1, lt_of_lt_of_le ht.2 hib₁⟩
      rw [hα, hβ] at hd₁_within
      have hd₁_at : HasDerivAt (fun u => γ₁.toFun u - z) (d₁ i₁ t) t :=
        (hd₁_within.hasDerivAt (Icc_mem_nhds ht_outer.1 ht_outer.2)).sub_const z
      exact (hd₁_at.div hd₀_at (hne₀ t (Ioo_subset_Icc_self ht_outer))).hasDerivWithinAt
  let γ_quot : BookPath := ⟨⟨γ₀.α, γ₀.β, γ₀.lt_endpoints, g, hg_cont⟩, hg_pc1⟩
  have hquot_cl : γ_quot.IsClosed := by
    have hcl₁' : γ₁.toFun γ₀.α = γ₁.toFun γ₀.β := by rwa [← hα, ← hβ]
    show g γ₀.α = g γ₀.β
    simp [g, hcl₁', show γ₀.toFun γ₀.α = γ₀.toFun γ₀.β from hcl₀]
  have hquot_tr : γ_quot.trace ⊆ disc 1 1 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [mem_disc]
    have h0_ne := hne₀ t ht
    have hdiff : g t - 1 = (γ₁.toFun t - γ₀.toFun t) / (γ₀.toFun t - z) := by
      dsimp [g]; field_simp; ring
    rw [hdiff, norm_div, norm_sub_rev (γ₀.toFun t) z]
    exact (div_lt_one (hpos₀ t ht)).mpr (hclose t ht)
  have hinv_disc_cont : ContinuousOn (fun w : ℂ => w⁻¹) (disc 1 1) :=
    continuous_id.continuousOn.inv₀ fun w hw h0 => by
      dsimp at h0; subst h0; simp [disc] at hw
  have hinv_disc_holo : HolomorphicOn (fun w : ℂ => w⁻¹) (disc 1 1 \ {0}) :=
    fun w hw => differentiableAt_id.inv fun h0 => by
      subst h0; simp [disc] at hw
  have hint_quot0 : pathIntegral (fun w => w⁻¹) γ_quot.toBookCurve = 0 :=
    (theorem10_14 Metric.isOpen_ball (convex_ball 1 1) 0 hinv_disc_cont hinv_disc_holo).2
      γ_quot hquot_cl hquot_tr
  -- Identify `pathIntegral w⁻¹ γ_quot` with `pathIntegral (w - z)⁻¹ γ₁ - pathIntegral (w - z)⁻¹ γ₀`
  have hf₀_cont : ContinuousOn (fun w : ℂ => (w - z)⁻¹) γ₀.trace :=
    (continuous_id.sub continuous_const).continuousOn.inv₀
      fun w hw h0 => hz₀ (sub_eq_zero.mp (by simpa using h0) ▸ hw)
  have hf₁_cont : ContinuousOn (fun w : ℂ => (w - z)⁻¹) γ₁.trace :=
    (continuous_id.sub continuous_const).continuousOn.inv₀
      fun w hw h0 => hz₁ (sub_eq_zero.mp (by simpa using h0) ▸ hw)
  have hint₁_int : IntervalIntegrable
      (fun t => (γ₁.toFun t - z)⁻¹ * derivWithin γ₁.toFun (Icc γ₀.α γ₀.β) t)
      MeasureTheory.volume γ₀.α γ₀.β := by
    have h := γ₁.intervalIntegrable_pathIntegral hf₁_cont
    rwa [hα, hβ] at h
  have hint₀_int : IntervalIntegrable
      (fun t => (γ₀.toFun t - z)⁻¹ * derivWithin γ₀.toFun (Icc γ₀.α γ₀.β) t)
      MeasureTheory.volume γ₀.α γ₀.β :=
    γ₀.intervalIntegrable_pathIntegral hf₀_cont
  have hquot_eq_diff : pathIntegral (fun w => w⁻¹) γ_quot.toBookCurve =
      pathIntegral (fun w => (w - z)⁻¹) γ₁.toBookCurve -
        pathIntegral (fun w => (w - z)⁻¹) γ₀.toBookCurve := by
    unfold pathIntegral
    change (∫ t in γ₀.α..γ₀.β, (g t)⁻¹ * derivWithin g (Icc γ₀.α γ₀.β) t) =
      (∫ t in γ₁.α..γ₁.β, (γ₁.toFun t - z)⁻¹ * derivWithin γ₁.toFun (Icc γ₁.α γ₁.β) t) -
      (∫ t in γ₀.α..γ₀.β, (γ₀.toFun t - z)⁻¹ * derivWithin γ₀.toFun (Icc γ₀.α γ₀.β) t)
    simp only [hα, hβ]
    rw [← intervalIntegral.integral_sub hint₁_int hint₀_int]
    apply intervalIntegral.integral_congr_ae_restrict
    change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc γ₀.α γ₀.β)] _
    rw [Set.uIoc_of_le γ₀.le_endpoints, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    have hS_fin : (S : Set ℝ).Finite := S.finite_toSet
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo,
      hS_fin.countable.ae_notMem _] with t ht hnotS
    have ht_Icc : t ∈ Icc γ₀.α γ₀.β := Ioo_subset_Icc_self ht
    -- Find partition pieces for `t`
    have hex₀ : ∃ i₀ : Fin n₀, t ∈ Ioo (s₀ i₀.castSucc) (s₀ i₀.succ) := by
      let T : Finset (Fin (n₀ + 1)) := Finset.univ.filter (fun j => s₀ j ≤ t)
      have hTne : T.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs₀0 ▸ ht.1.le⟩⟩
      let j := T.max' hTne
      have hjlt : s₀ j < t := lt_of_le_of_ne (Finset.mem_filter.mp (T.max'_mem hTne)).2 fun heq =>
        hnotS (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq⟩))
      have hjne : j ≠ Fin.last n₀ := fun h => by linarith [h ▸ hjlt, hs₀n, ht.2]
      obtain ⟨i₀, hi₀⟩ := Fin.eq_castSucc_of_ne_last hjne
      rw [← hi₀] at hjlt
      refine ⟨i₀, hjlt, ?_⟩
      by_contra hge
      have hmax := T.le_max' i₀.succ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hge⟩)
      change i₀.succ ≤ j at hmax
      rw [← hi₀] at hmax
      exact not_le.mpr i₀.castSucc_lt_succ hmax
    have hex₁ : ∃ i₁ : Fin n₁, t ∈ Ioo (s₁ i₁.castSucc) (s₁ i₁.succ) := by
      let T : Finset (Fin (n₁ + 1)) := Finset.univ.filter (fun j => s₁ j ≤ t)
      have hTne : T.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs₁0' ▸ ht.1.le⟩⟩
      let j := T.max' hTne
      have hjlt : s₁ j < t := lt_of_le_of_ne (Finset.mem_filter.mp (T.max'_mem hTne)).2 fun heq =>
        hnotS (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq⟩))
      have hjne : j ≠ Fin.last n₁ := fun h => by linarith [h ▸ hjlt, hs₁n', ht.2]
      obtain ⟨i₁, hi₁⟩ := Fin.eq_castSucc_of_ne_last hjne
      rw [← hi₁] at hjlt
      refine ⟨i₁, hjlt, ?_⟩
      by_contra hge
      have hmax := T.le_max' i₁.succ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hge⟩)
      change i₁.succ ≤ j at hmax
      rw [← hi₁] at hmax
      exact not_le.mpr i₁.castSucc_lt_succ hmax
    obtain ⟨i₀, hi₀⟩ := hex₀
    obtain ⟨i₁, hi₁⟩ := hex₁
    have hnhds : Icc γ₀.α γ₀.β ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hd₀_at : HasDerivAt γ₀.toFun (d₀ i₀ t) t := (hd₀ i₀ t hi₀).hasDerivAt hnhds
    have hd₁_w := hd₁ i₁ t hi₁
    rw [hα, hβ] at hd₁_w
    have hd₁_at : HasDerivAt γ₁.toFun (d₁ i₁ t) t := hd₁_w.hasDerivAt hnhds
    have hdg_at : HasDerivAt g
        (((d₁ i₁ t) * (γ₀.toFun t - z) - (γ₁.toFun t - z) * (d₀ i₀ t)) / (γ₀.toFun t - z) ^ 2) t :=
      (hd₁_at.sub_const z).div (hd₀_at.sub_const z) (hne₀ t ht_Icc)
    rw [derivWithin_of_mem_nhds hnhds, hdg_at.deriv,
        derivWithin_of_mem_nhds hnhds, hd₁_at.deriv,
        derivWithin_of_mem_nhds hnhds, hd₀_at.deriv]
    dsimp [g]
    have h0_t := hne₀ t ht_Icc
    have h1_t := hne₁ t ht_Icc
    field_simp
  rw [hint_quot0] at hquot_eq_diff
  have hint_eq : pathIntegral (fun w => (w - z)⁻¹) γ₁.toBookCurve =
      pathIntegral (fun w => (w - z)⁻¹) γ₀.toBookCurve := (sub_eq_zero.mp hquot_eq_diff.symm)
  simp [Ind, hint_eq]

/-- Helper for 10.40: piecewise-linear closed `BookPath` on `[0, 1]` interpolating `M + 1` vertices
`v 0, v 1, ..., v M` (`M ≥ 1`, `v M = v 0`), built via the telescoping sum of clamped ramps
`L v s = v 0 + ∑_{k < M} max 0 (min 1 (M s - k)) * (v (k + 1) - v k)`. -/
private def polyLoopFun (M : ℕ) (v : ℕ → ℂ) (s : ℝ) : ℂ :=
  v 0 + ∑ k ∈ Finset.range M,
    Complex.ofReal (max 0 (min 1 ((M : ℝ) * s - k))) * (v (k + 1) - v k)

private theorem polyLoopFun_piece_eq {M : ℕ} (v : ℕ → ℂ) {j : ℕ} (hj : j < M)
    {s : ℝ} (hs1 : (j : ℝ) / M ≤ s) (hs2 : s ≤ ((j + 1 : ℕ) : ℝ) / M) :
    polyLoopFun M v s =
      (1 - ((M : ℝ) * s - j) : ℝ) • v j + ((M : ℝ) * s - j) • v (j + 1) := by
  have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hj)
  have hθ0 : 0 ≤ (M : ℝ) * s - j := by
    have := (div_le_iff₀ hM_pos).mp hs1
    linarith
  have hθ1 : (M : ℝ) * s - j ≤ 1 := by
    have := (le_div_iff₀ hM_pos).mp hs2
    push_cast at this
    linarith
  unfold polyLoopFun
  -- Split `range M` into `k < j`, `k = j`, and `k > j`
  have hsplit : ∑ k ∈ Finset.range M,
      Complex.ofReal (max 0 (min 1 ((M : ℝ) * s - k))) * (v (k + 1) - v k) =
      ∑ k ∈ Finset.range j, (v (k + 1) - v k) +
        Complex.ofReal ((M : ℝ) * s - j) * (v (j + 1) - v j) := by
    have hrange : Finset.range M = Finset.range (j + 1 + (M - (j + 1))) := by congr 1; omega
    rw [hrange, Finset.sum_range_add, Finset.sum_range_succ]
    have htail : ∑ x ∈ Finset.range (M - (j + 1)),
        Complex.ofReal (max 0 (min 1 ((M : ℝ) * s - ↑(j + 1 + x)))) *
          (v (j + 1 + x + 1) - v (j + 1 + x)) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      have hle0 : (M : ℝ) * s - ((j + 1 + x : ℕ) : ℝ) ≤ 0 := by
        push_cast; linarith [Nat.cast_nonneg (α := ℝ) x]
      rw [min_eq_right (le_trans hle0 zero_le_one), max_eq_left hle0]
      simp
    have hmid : max (0 : ℝ) (min 1 ((M : ℝ) * s - j)) = (M : ℝ) * s - j := by
      rw [min_eq_right hθ1, max_eq_right hθ0]
    have hhead : ∑ k ∈ Finset.range j,
        Complex.ofReal (max 0 (min 1 ((M : ℝ) * s - k))) * (v (k + 1) - v k) =
        ∑ k ∈ Finset.range j, (v (k + 1) - v k) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_lt : k < j := Finset.mem_range.mp hk
      have hge1 : (1 : ℝ) ≤ (M : ℝ) * s - k := by
        have hkj : (1 : ℝ) ≤ (j : ℝ) - k := by
          have : (k + 1 : ℕ) ≤ j := hk_lt
          have hcast : ((k + 1 : ℕ) : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr this
          push_cast at hcast
          linarith
        linarith
      rw [min_eq_left hge1, max_eq_right zero_le_one]
      simp
    rw [htail, add_zero, hmid, hhead]
  have htele : ∀ n : ℕ, v 0 + ∑ k ∈ Finset.range n, (v (k + 1) - v k) = v n := fun n => by
    induction n with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ← add_assoc, ih]; ring
  rw [hsplit, ← add_assoc, htele j]
  simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

private def polyLoopPath (M : ℕ) (hM : 1 ≤ M) (v : ℕ → ℂ) : BookPath where
  α := 0
  β := 1
  lt_endpoints := zero_lt_one
  toFun := polyLoopFun M v
  continuousOn := by
    refine Continuous.continuousOn ?_
    unfold polyLoopFun
    exact continuous_const.add (continuous_finsetSum _ fun k _ =>
      (Complex.continuous_ofReal.comp
        (continuous_const.max (continuous_const.min
          ((continuous_const.mul continuous_id).sub continuous_const)))).mul continuous_const)
  piecewiseC1 := by
    have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
    let s : Fin (M + 1) → ℝ := fun i => (i : ℝ) / M
    let d : Fin M → ℝ → ℂ := fun i _ => (M : ℂ) * (v ((i : ℕ) + 1) - v (i : ℕ))
    have hs : StrictMono s := fun i j hij =>
      div_lt_div_of_pos_right (Nat.cast_lt.mpr hij) hM_pos
    have hs0 : s 0 = 0 := by simp [s]
    have hsn : s (Fin.last M) = 1 := by simp [s, div_self hM_pos.ne']
    refine ⟨M, s, d, hs, hs0, hsn, fun _ => continuousOn_const, fun i t ht => ?_⟩
    dsimp [s] at ht
    have hev : polyLoopFun M v =ᶠ[𝓝 t]
        fun u => (1 - ((M : ℝ) * u - (i : ℕ)) : ℝ) • v (i : ℕ) +
          ((M : ℝ) * u - (i : ℕ)) • v ((i : ℕ) + 1) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      exact polyLoopFun_piece_eq v i.isLt hu.1.le (by simpa [Nat.cast_add] using hu.2.le)
    have haff : HasDerivAt (fun u : ℝ =>
        (1 - ((M : ℝ) * u - (i : ℕ)) : ℝ) • v (i : ℕ) +
          ((M : ℝ) * u - (i : ℕ)) • v ((i : ℕ) + 1)) (d i t) t := by
      have hlin : HasDerivAt (fun u : ℝ => (M : ℝ) * u - (i : ℕ)) (M : ℝ) t := by
        simpa using ((hasDerivAt_id t).const_mul (M : ℝ)).sub_const ((i : ℕ) : ℝ)
      have h1 := ((hlin.const_sub 1).smul_const (v (i : ℕ))).add (hlin.smul_const (v ((i : ℕ) + 1)))
      have hsimp : (-(M : ℝ)) • v (i : ℕ) + (M : ℝ) • v ((i : ℕ) + 1) = d i t := by
        change ((-(M : ℝ) : ℝ) : ℂ) * v (i : ℕ) + ((M : ℝ) : ℂ) * v ((i : ℕ) + 1) =
          (M : ℂ) * (v ((i : ℕ) + 1) - v (i : ℕ))
        push_cast
        ring
      rwa [hsimp] at h1
    exact (haff.congr_of_eventuallyEq hev).hasDerivWithinAt

private theorem polyLoopPath_isClosed {M : ℕ} (hM : 1 ≤ M) {v : ℕ → ℂ} (hv : v M = v 0) :
    (polyLoopPath M hM v).IsClosed := by
  have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
  show polyLoopFun M v 0 = polyLoopFun M v 1
  have h0 := polyLoopFun_piece_eq v (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
    (by simp : ((0 : ℕ) : ℝ) / M ≤ 0) (by positivity)
  have h1 := polyLoopFun_piece_eq v (Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hM) Nat.zero_lt_one)
    (div_le_one_of_le₀ (Nat.cast_le.mpr (Nat.sub_le M 1)) hM_pos.le)
    (by rw [Nat.sub_add_cancel hM, div_self hM_pos.ne'])
  rw [Nat.sub_add_cancel hM] at h1
  simp only [Nat.cast_zero, mul_zero, sub_zero, sub_self, one_smul, zero_smul, add_zero] at h0
  have h1_theta : (M : ℝ) * 1 - ((M - 1 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_sub hM, Nat.cast_one]; ring
  rw [h1_theta, sub_self, zero_smul, one_smul, zero_add, hv] at h1
  exact h0.trans h1.symm

/-- Affine normalization of a `BookPath` on `[α, β]` to a `BookPath` on `[0, 1]` with the same
trace and path integrals. -/
def BookPath.toUnitPath (γ : BookPath) : BookPath :=
  γ.reparam zero_lt_one (fun s => (1 - s) * γ.α + s * γ.β) (fun _ => γ.β - γ.α)
    (((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const)).continuousOn
    continuousOn_const
    (fun s _ => by
      have h := (((hasDerivAt_id s).const_sub 1).mul_const γ.α).add
        ((hasDerivAt_id s).mul_const γ.β)
      have heq : -1 * γ.α + 1 * γ.β = γ.β - γ.α := by ring
      rw [heq] at h
      exact h.hasDerivWithinAt)
    (fun _ _ => sub_nonneg.mpr γ.le_endpoints)
    (by ring) (by ring)

theorem BookPath.Ind_toUnitPath (γ : BookPath) (z : ℂ) :
    Ind γ.toUnitPath.toBookCurve z = Ind γ.toBookCurve z := by
  unfold Ind BookPath.toUnitPath
  rw [γ.pathIntegral_reparam]

/-- 10.40 (Continuous free-homotopy invariance of index): if `γ₀` and `γ₁` are closed paths in any
subset `Ω ⊆ ℂ` that are freely `Ω`-homotopic (`BookCurve.HomotopicIn Ω`), then
`Ind_{γ₀}(z) = Ind_{γ₁}(z)` for every `z ∉ Ω` (the intermediate curves of `H` need only be
continuous, NOT piecewise `C¹`). -/
theorem theorem10_40 {Ω : Set ℂ} (γ₀ γ₁ : BookPath)
    (hcl₀ : γ₀.IsClosed) (hcl₁ : γ₁.IsClosed)
    (hhom : BookCurve.HomotopicIn Ω γ₀.toBookCurve γ₁.toBookCurve)
    {z : ℂ} (hz : z ∉ Ω) :
    Ind γ₀.toBookCurve z = Ind γ₁.toBookCurve z := by
  rw [← γ₀.Ind_toUnitPath z, ← γ₁.Ind_toUnitPath z]
  obtain ⟨_, _, _, _, _, _, H, hHc, hHΩ, hH0, hH1, hHloop⟩ := hhom
  let Q : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc 0 1
  have hQ_comp : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hQ_ne : Q.Nonempty := ⟨(0, 0), ⟨left_mem_Icc.mpr zero_le_one, left_mem_Icc.mpr zero_le_one⟩⟩
  -- Positive distance `ε > 0` from `z ∉ Ω` to the compact image `H(Q) ⊆ Ω`
  have hdist_cont : ContinuousOn (fun p : ℝ × ℝ => ‖z - H p‖) Q :=
    (continuousOn_const.sub hHc).norm
  obtain ⟨p_min, hp_min, hmin⟩ := hQ_comp.exists_isMinOn hQ_ne hdist_cont
  set ε : ℝ := ‖z - H p_min‖
  have hε_pos : 0 < ε := norm_pos_iff.mpr (sub_ne_zero.mpr fun heq =>
    hz (heq ▸ hHΩ ⟨p_min, hp_min, rfl⟩))
  have hε_le : ∀ p ∈ Q, ε ≤ ‖z - H p‖ := fun p hp => hmin hp
  -- Uniform continuity mesh `1 / M < δ` for `ε / 3`
  obtain ⟨δ, hδ_pos, hδ_unif⟩ := Metric.uniformContinuousOn_iff.mp
    (hQ_comp.uniformContinuousOn_of_continuous hHc) (ε / 3) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  let M : ℕ := max N 1
  have hM1 : 1 ≤ M := le_max_right N 1
  have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hM1)
  have hmesh : (1 : ℝ) / M < δ := by
    have hN_lt_M : (1 : ℝ) / δ < M := lt_of_lt_of_le hN (Nat.cast_le.mpr (le_max_left N 1))
    exact (div_lt_iff₀ hM_pos).mpr (by have := (div_lt_iff₀ hδ_pos).mp hN_lt_M; linarith)
  -- Vertex grids `v_grid t k = H(k / M, t)` for `k ≤ M`
  let v_grid : ℝ → ℕ → ℂ := fun t k => H ((k : ℝ) / M, t)
  have hv_loop : ∀ t ∈ Icc (0 : ℝ) 1, v_grid t M = v_grid t 0 := by
    intro t ht
    dsimp [v_grid]
    rw [div_self hM_pos.ne', Nat.cast_zero, zero_div]
    exact (hHloop t ht).symm
  -- Find subinterval `j < M` for any `s ∈ [0, 1]`
  have hex_sub : ∀ s ∈ Icc (0 : ℝ) 1, ∃ j : ℕ, j < M ∧
      (j : ℝ) / M ≤ s ∧ s ≤ ((j + 1 : ℕ) : ℝ) / M := by
    intro s hs
    by_cases hs1 : s = 1
    · subst hs1
      refine ⟨M - 1, Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hM1) Nat.zero_lt_one,
        div_le_one_of_le₀ (Nat.cast_le.mpr (Nat.sub_le M 1)) hM_pos.le, ?_⟩
      rw [Nat.sub_add_cancel hM1, div_self hM_pos.ne']
    · have hs_lt1 : s < 1 := lt_of_le_of_ne hs.2 hs1
      let j : ℕ := ⌊(M : ℝ) * s⌋₊
      have hMs_nn : 0 ≤ (M : ℝ) * s := mul_nonneg hM_pos.le hs.1
      have hj_lt : j < M := by
        rw [← @Nat.cast_lt ℝ]
        calc (j : ℝ) ≤ (M : ℝ) * s := Nat.floor_le hMs_nn
          _ < (M : ℝ) * 1 := mul_lt_mul_of_pos_left hs_lt1 hM_pos
          _ = M := mul_one _
      exact ⟨j, hj_lt, (div_le_iff₀ hM_pos).mpr (by linarith [Nat.floor_le hMs_nn]),
        (le_div_iff₀ hM_pos).mpr (by push_cast; linarith [Nat.lt_floor_add_one ((M : ℝ) * s)])⟩
  -- Pointwise approximation `‖polyLoopFun M (v_grid t) s - H(s, t)‖ < ε / 3`
  have hpoly_approx : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖polyLoopFun M (v_grid t) s - H (s, t)‖ < ε / 3 := by
    intro t ht s hs
    obtain ⟨j, hj, hs_lo, hs_hi⟩ := hex_sub s hs
    rw [polyLoopFun_piece_eq (v_grid t) hj hs_lo hs_hi]
    set θ : ℝ := (M : ℝ) * s - j
    have hθ0 : 0 ≤ θ := by have := (div_le_iff₀ hM_pos).mp hs_lo; dsimp [θ]; linarith
    have hθ1 : θ ≤ 1 := by
      have := (le_div_iff₀ hM_pos).mp hs_hi; push_cast at this; dsimp [θ]; linarith
    have hj_mem : ((j : ℝ) / M) ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, div_le_one_of_le₀ (Nat.cast_le.mpr hj.le) hM_pos.le⟩
    have hj1_mem : (((j + 1 : ℕ) : ℝ) / M) ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, div_le_one_of_le₀ (Nat.cast_le.mpr hj) hM_pos.le⟩
    have hd_j : dist ((j : ℝ) / M, t) (s, t) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr hs_lo), neg_sub]
      have hlen : s - (j : ℝ) / M ≤ 1 / M := by
        have h1 : ((j + 1 : ℕ) : ℝ) / M - (j : ℝ) / M = 1 / M := by push_cast; ring
        linarith
      exact lt_of_le_of_lt hlen hmesh
    have hd_j1 : dist (((j + 1 : ℕ) : ℝ) / M, t) (s, t) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr hs_hi)]
      have hlen : ((j + 1 : ℕ) : ℝ) / M - s ≤ 1 / M := by
        have h1 : ((j + 1 : ℕ) : ℝ) / M - (j : ℝ) / M = 1 / M := by push_cast; ring
        linarith
      exact lt_of_le_of_lt hlen hmesh
    have hb1 : v_grid t j ∈ Metric.ball (H (s, t)) (ε / 3) :=
      hδ_unif _ ⟨hj_mem, ht⟩ _ ⟨hs, ht⟩ hd_j
    have hb2 : v_grid t (j + 1) ∈ Metric.ball (H (s, t)) (ε / 3) :=
      hδ_unif _ ⟨hj1_mem, ht⟩ _ ⟨hs, ht⟩ hd_j1
    have hcomb := (convex_ball (H (s, t)) (ε / 3)) hb1 hb2 (sub_nonneg.mpr hθ1) hθ0 (by ring)
    rwa [Metric.mem_ball, dist_eq_norm] at hcomb
  -- Closedness of `γ₀.toUnitPath` and `γ₁.toUnitPath`
  have hunit₀_cl : γ₀.toUnitPath.IsClosed := by
    show γ₀.toFun ((1 - 0) * γ₀.α + 0 * γ₀.β) = γ₀.toFun ((1 - 1) * γ₀.α + 1 * γ₀.β)
    simpa using (show γ₀.toFun γ₀.α = γ₀.toFun γ₀.β from hcl₀)
  have hunit₁_cl : γ₁.toUnitPath.IsClosed := by
    show γ₁.toFun ((1 - 0) * γ₁.α + 0 * γ₁.β) = γ₁.toFun ((1 - 1) * γ₁.α + 1 * γ₁.β)
    simpa using (show γ₁.toFun γ₁.α = γ₁.toFun γ₁.β from hcl₁)
  let P : ℕ → BookPath := fun m => polyLoopPath M hM1 (v_grid ((m : ℝ) / M))
  -- Step 1: `Ind (P 0) z = Ind γ₀.toUnitPath z`
  have hP0 : Ind (P 0).toBookCurve z = Ind γ₀.toUnitPath.toBookCurve z := by
    refine (theorem10_39 γ₀.toUnitPath (P 0) rfl rfl hunit₀_cl
      (by dsimp [P]; rw [Nat.cast_zero, zero_div]; exact polyLoopPath_isClosed hM1 (hv_loop 0 (left_mem_Icc.mpr zero_le_one)))
      z ?_).2.2
    intro s hs
    change s ∈ Icc 0 1 at hs
    change ‖polyLoopFun M (v_grid (((0 : ℕ) : ℝ) / M)) s - γ₀.toBookCurve.toUnitLoop s‖ <
      ‖z - γ₀.toBookCurve.toUnitLoop s‖
    rw [Nat.cast_zero, zero_div, ← hH0 s hs]
    exact lt_of_lt_of_le (hpoly_approx 0 (left_mem_Icc.mpr zero_le_one) s hs)
      (by linarith [hε_le (s, 0) ⟨hs, left_mem_Icc.mpr zero_le_one⟩])
  -- Step 2: `Ind (P M) z = Ind γ₁.toUnitPath z`
  have hPM : Ind (P M).toBookCurve z = Ind γ₁.toUnitPath.toBookCurve z := by
    refine (theorem10_39 γ₁.toUnitPath (P M) rfl rfl hunit₁_cl
      (by dsimp [P]; rw [div_self hM_pos.ne']; exact polyLoopPath_isClosed hM1 (hv_loop 1 (right_mem_Icc.mpr zero_le_one)))
      z ?_).2.2
    intro s hs
    change s ∈ Icc 0 1 at hs
    change ‖polyLoopFun M (v_grid ((M : ℝ) / M)) s - γ₁.toBookCurve.toUnitLoop s‖ <
      ‖z - γ₁.toBookCurve.toUnitLoop s‖
    rw [div_self hM_pos.ne', ← hH1 s hs]
    exact lt_of_lt_of_le (hpoly_approx 1 (right_mem_Icc.mpr zero_le_one) s hs)
      (by linarith [hε_le (s, 1) ⟨hs, right_mem_Icc.mpr zero_le_one⟩])
  -- Step 3: `Ind (P (m + 1)) z = Ind (P m) z` for all `m < M`
  have hstep : ∀ m : ℕ, m ≤ M → Ind (P m).toBookCurve z = Ind (P 0).toBookCurve z := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      have hm_lt : m < M := Nat.lt_of_succ_le hm
      rw [← ih hm_lt.le]
      have htm : ((m : ℝ) / M) ∈ Icc (0 : ℝ) 1 :=
        ⟨by positivity, div_le_one_of_le₀ (Nat.cast_le.mpr hm_lt.le) hM_pos.le⟩
      have htm1 : (((m + 1 : ℕ) : ℝ) / M) ∈ Icc (0 : ℝ) 1 :=
        ⟨by positivity, div_le_one_of_le₀ (Nat.cast_le.mpr hm) hM_pos.le⟩
      refine (theorem10_39 (P m) (P (m + 1)) rfl rfl
        (polyLoopPath_isClosed hM1 (hv_loop _ htm))
        (polyLoopPath_isClosed hM1 (hv_loop _ htm1)) z ?_).2.2
      intro s hs
      change s ∈ Icc 0 1 at hs
      change ‖polyLoopFun M (v_grid (((m + 1 : ℕ) : ℝ) / M)) s -
        polyLoopFun M (v_grid ((m : ℝ) / M)) s‖ <
        ‖z - polyLoopFun M (v_grid ((m : ℝ) / M)) s‖
      have ha0 := hpoly_approx _ htm s hs
      have hlo : 2 * ε / 3 < ‖z - polyLoopFun M (v_grid ((m : ℝ) / M)) s‖ := by
        have htri : ‖z - H (s, (m : ℝ) / M)‖ ≤
            ‖z - polyLoopFun M (v_grid ((m : ℝ) / M)) s‖ +
              ‖polyLoopFun M (v_grid ((m : ℝ) / M)) s - H (s, (m : ℝ) / M)‖ := by
          simpa using norm_add_le (z - polyLoopFun M (v_grid ((m : ℝ) / M)) s)
            (polyLoopFun M (v_grid ((m : ℝ) / M)) s - H (s, (m : ℝ) / M))
        linarith [hε_le (s, (m : ℝ) / M) ⟨hs, htm⟩]
      have hstep_diff : ‖polyLoopFun M (v_grid (((m + 1 : ℕ) : ℝ) / M)) s -
          polyLoopFun M (v_grid ((m : ℝ) / M)) s‖ < ε / 3 := by
        obtain ⟨j, hj, hs_lo, hs_hi⟩ := hex_sub s hs
        rw [polyLoopFun_piece_eq (v_grid (((m + 1 : ℕ) : ℝ) / M)) hj hs_lo hs_hi,
            polyLoopFun_piece_eq (v_grid ((m : ℝ) / M)) hj hs_lo hs_hi]
        set θ : ℝ := (M : ℝ) * s - j
        have hθ0 : 0 ≤ θ := by have := (div_le_iff₀ hM_pos).mp hs_lo; dsimp [θ]; linarith
        have hθ1 : θ ≤ 1 := by
          have := (le_div_iff₀ hM_pos).mp hs_hi; push_cast at this; dsimp [θ]; linarith
        have hcomb_diff : ((1 - θ : ℝ) • v_grid (((m + 1 : ℕ) : ℝ) / M) j +
            θ • v_grid (((m + 1 : ℕ) : ℝ) / M) (j + 1)) -
            ((1 - θ : ℝ) • v_grid ((m : ℝ) / M) j + θ • v_grid ((m : ℝ) / M) (j + 1)) =
            (1 - θ : ℝ) • (v_grid (((m + 1 : ℕ) : ℝ) / M) j - v_grid ((m : ℝ) / M) j) +
              θ • (v_grid (((m + 1 : ℕ) : ℝ) / M) (j + 1) - v_grid ((m : ℝ) / M) (j + 1)) := by
          simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]; ring
        have hvert_lt : ∀ k ≤ M,
            ‖v_grid (((m + 1 : ℕ) : ℝ) / M) k - v_grid ((m : ℝ) / M) k‖ < ε / 3 := by
          intro k hk
          have hk_mem : ((k : ℝ) / M) ∈ Icc (0 : ℝ) 1 :=
            ⟨by positivity, div_le_one_of_le₀ (Nat.cast_le.mpr hk) hM_pos.le⟩
          have hdk : dist ((k : ℝ) / M, ((m + 1 : ℕ) : ℝ) / M) ((k : ℝ) / M, (m : ℝ) / M) < δ := by
            rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Real.dist_eq]
            have hdiff : ((m + 1 : ℕ) : ℝ) / M - (m : ℝ) / M = 1 / M := by push_cast; ring
            rw [hdiff, abs_of_pos (div_pos zero_lt_one hM_pos)]
            exact hmesh
          rw [← dist_eq_norm]
          exact hδ_unif _ ⟨hk_mem, htm1⟩ _ ⟨hk_mem, htm⟩ hdk
        have hb_j : v_grid (((m + 1 : ℕ) : ℝ) / M) j - v_grid ((m : ℝ) / M) j ∈
            Metric.ball (0 : ℂ) (ε / 3) := by
          simpa [Metric.mem_ball] using hvert_lt j hj.le
        have hb_j1 : v_grid (((m + 1 : ℕ) : ℝ) / M) (j + 1) - v_grid ((m : ℝ) / M) (j + 1) ∈
            Metric.ball (0 : ℂ) (ε / 3) := by
          simpa [Metric.mem_ball] using hvert_lt (j + 1) hj
        have hball_comb := (convex_ball (0 : ℂ) (ε / 3)) hb_j hb_j1 (sub_nonneg.mpr hθ1) hθ0 (by ring)
        rw [Metric.mem_ball, dist_zero_right] at hball_comb
        rw [hcomb_diff]
        exact hball_comb
      linarith
  exact hP0.symm.trans ((hstep M le_rfl).symm.trans hPM)

/-- 10.40 (Corollary 1): if a closed path `γ` in `Ω` is null-homotopic in `Ω`, then
`Ind_γ(z) = 0` for every `z ∉ Ω`. -/
theorem corollary10_40_nullHomotopic_Ind {Ω : Set ℂ} (γ : BookPath) (hcl : γ.IsClosed)
    (hnull : IsNullHomotopicIn Ω γ.toBookCurve.toUnitLoop) {z : ℂ} (hz : z ∉ Ω) :
    Ind γ.toBookCurve z = 0 := by
  obtain ⟨c, hcΩ, hhom⟩ := hnull
  let γ_const : BookPath := BookPath.ofC1 zero_lt_one (fun _ => c) (fun _ => 0)
    continuousOn_const continuousOn_const
    (fun t _ => (hasDerivAt_const t c).hasDerivWithinAt)
  have hconst_cl : γ_const.IsClosed := rfl
  have hhom' : BookCurve.HomotopicIn Ω γ.toBookCurve γ_const.toBookCurve := hhom
  rw [theorem10_40 γ γ_const hcl hconst_cl hhom' hz]
  unfold Ind pathIntegral γ_const BookPath.ofC1
  dsimp only
  have h0 : (∫ t in (0 : ℝ)..1, (c - z)⁻¹ * derivWithin (fun _ : ℝ => c) (Icc 0 1) t) =
      ∫ _ in (0 : ℝ)..1, (0 : ℂ) := by
    apply intervalIntegral.integral_congr_ae_restrict
    change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc 0 1)] _
    rw [Set.uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), deriv_const, mul_zero]
  rw [h0, intervalIntegral.integral_zero, mul_zero]

/-- 10.40 (Corollary 2 — Cauchy's theorem in a simply connected region): if `Ω` is a simply
connected region (`BookSimplyConnected Ω`), then:
1. `Ind_γ(z) = 0` for every closed path `γ` in `Ω` and every `z ∉ Ω` (and `Ind_Γ(z) = 0` for every
   cycle `Γ` in `Ω` and `z ∉ Ω`), and
2. `∫_γ f(z) dz = 0` for every `f ∈ H(Ω)` and every closed path `γ` in `Ω` (and `∫_Γ f(z) dz = 0`
   for every cycle `Γ` in `Ω`). -/
theorem corollary10_40_simplyConnected {Ω : Set ℂ} (hΩ : BookSimplyConnected Ω) :
    (∀ γ : BookPath, γ.IsClosed → γ.trace ⊆ Ω → ∀ z, z ∉ Ω → Ind γ.toBookCurve z = 0) ∧
    (∀ Γ : BookChain, Γ.IsCycle → Γ.trace ⊆ Ω → ∀ z, z ∉ Ω → Γ.Ind z = 0) ∧
    (∀ {f : ℂ → ℂ}, HolomorphicOn f Ω →
      (∀ γ : BookPath, γ.IsClosed → γ.trace ⊆ Ω → pathIntegral f γ.toBookCurve = 0) ∧
      (∀ Γ : BookChain, Γ.IsCycle → Γ.trace ⊆ Ω → Γ.integral f = 0)) := by
  have hpath_ind : ∀ γ : BookPath, γ.IsClosed → γ.trace ⊆ Ω →
      ∀ z, z ∉ Ω → Ind γ.toBookCurve z = 0 := by
    intro γ hcl hγ z hz
    have hunit_cont : ContinuousOn γ.toBookCurve.toUnitLoop (Icc 0 1) :=
      γ.continuousOn.comp (((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
        (continuousOn_id.mul continuousOn_const)) fun s hs =>
          ⟨by nlinarith [hs.1, hs.2, γ.le_endpoints], by nlinarith [hs.1, hs.2, γ.le_endpoints]⟩
    have hunit_Ω : γ.toBookCurve.toUnitLoop '' Icc 0 1 ⊆ Ω := by
      rintro _ ⟨s, hs, rfl⟩
      exact hγ (γ.mem_trace_of_mem_Icc
        ⟨by nlinarith [hs.1, hs.2, γ.le_endpoints], by nlinarith [hs.1, hs.2, γ.le_endpoints]⟩)
    have hunit_cl : γ.toBookCurve.toUnitLoop 0 = γ.toBookCurve.toUnitLoop 1 := by
      simpa [BookCurve.toUnitLoop] using (show γ.toFun γ.α = γ.toFun γ.β from hcl)
    exact corollary10_40_nullHomotopic_Ind γ hcl (hΩ.2 _ hunit_cont hunit_Ω hunit_cl) hz
  have hcyc_ind : ∀ Γ : BookChain, Γ.IsCycle → Γ.trace ⊆ Ω →
      ∀ z, z ∉ Ω → Γ.Ind z = 0 := by
    intro Γ hcyc hΓ z hz
    obtain ⟨Δ, hclΔ, hsubΔ, heq⟩ := hcyc
    have hzΓ : z ∉ Γ.trace := fun h => hz (hΓ h)
    have hzΔ : z ∉ Δ.trace := fun h => hzΓ (hsubΔ h)
    rw [BookChain.Ind_congr_equiv heq (fun h => h.elim hzΓ hzΔ)]
    have hΔΩ : Δ.trace ⊆ Ω := hsubΔ.trans hΓ
    clear heq hsubΔ hzΓ
    induction Δ with
    | nil => simp
    | cons σ Δ ih =>
      rw [BookChain.trace_cons] at hΔΩ
      rw [BookChain.Ind_cons,
          hpath_ind σ (hclΔ σ List.mem_cons_self) (subset_union_left.trans hΔΩ) z hz,
          zero_add]
      exact ih (fun τ hτ => hclΔ τ (List.mem_cons_of_mem _ hτ))
        (fun h => hz (hΔΩ (Or.inr h))) (subset_union_right.trans hΔΩ)
  refine ⟨hpath_ind, hcyc_ind, fun {f} hf => ⟨?_, ?_⟩⟩
  · intro γ hcl hγ
    have h0 := (theorem10_35 hΩ.1.1).1 hf [γ] (BookChain.isCycle_singleton_of_isClosed hcl)
      (by simpa using hγ) (hcyc_ind [γ] (BookChain.isCycle_singleton_of_isClosed hcl) (by simpa using hγ))
    simpa using h0.2
  · intro Γ hcyc hΓ
    exact ((theorem10_35 hΩ.1.1).1 hf Γ hcyc hΓ (hcyc_ind Γ hcyc hΓ)).2

end BatchD1

/-! ## Batch D2: Nodes 10.41, 10.42, 10.43, and 10.44 -/

section BatchD2

/-- Monotonicity of `HasPole` under shrinking the open neighborhood of `a`. -/
theorem HasPole.mono {f : ℂ → ℂ} {V W : Set ℂ} {a : ℂ}
    (hpole : HasPole f V a) (hW : IsOpen W) (haW : a ∈ W) (hsub : W ⊆ V) :
    HasPole f W a := by
  rcases hpole with ⟨⟨_, _, hfV⟩, g, Q, hg, hQ, heq⟩
  exact ⟨⟨hW, haW, fun z hz => hfV z (Set.sdiff_subset_sdiff_left hsub hz)⟩,
    g, Q, fun z hz => hg z (hsub hz), hQ, heq.mono (Set.sdiff_subset_sdiff_left hsub)⟩

/-- Continuity and holomorphy of a principal part `Q` at `a` on `{a}ᶜ`. -/
theorem holomorphicOn_of_isPrincipalPart {Q : ℂ → ℂ} {a : ℂ} (hQ : IsPrincipalPart Q a) :
    HolomorphicOn Q ({a}ᶜ) := by
  obtain ⟨m, c, _, _, hQeq⟩ := hQ
  intro z hz
  have hza : z - a ≠ 0 := sub_ne_zero.mpr (mem_compl_singleton_iff.mp hz)
  have hfun : Q = fun w => ∑ k ∈ Finset.Icc 1 m, c k * (w - a)⁻¹ ^ k := funext hQeq
  rw [hfun]
  have hsum := HasDerivAt.sum (u := Finset.Icc 1 m)
    (A := fun k (w : ℂ) => c k * (w - a)⁻¹ ^ k)
    fun k _ => (((hasDerivAt_id z).sub_const a).inv hza |>.pow k).const_mul (c k)
  rw [Finset.sum_fn] at hsum
  exact hsum.differentiableAt

/-- Path integral of a finite sum of continuous functions along a path `γ`. -/
theorem BookPath.pathIntegral_finset_sum {ι : Type*} (γ : BookPath) (s : Finset ι)
    (F : ι → ℂ → ℂ) (hcont : ∀ i ∈ s, ContinuousOn (F i) γ.trace) :
    pathIntegral (fun z => ∑ i ∈ s, F i z) γ.toBookCurve =
      ∑ i ∈ s, pathIntegral (F i) γ.toBookCurve := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : pathIntegral (fun _ => (0 : ℂ)) γ.toBookCurve = 0 := by
      simpa using BookPath.pathIntegral_const_mul 0 (fun _ => 0) γ.toBookCurve
    simpa using h0
  | @insert a s ha ih =>
    have h1 : ContinuousOn (F a) γ.trace := hcont a (Finset.mem_insert_self a s)
    have h2 : ContinuousOn (fun z => ∑ i ∈ s, F i z) γ.trace :=
      continuousOn_finsetSum s fun i hi => hcont i (Finset.mem_insert_of_mem hi)
    have heq : EqOn (fun z => ∑ i ∈ insert a s, F i z)
        (fun z => F a z + ∑ i ∈ s, F i z) γ.trace :=
      fun z _ => Finset.sum_insert ha
    rw [BookPath.pathIntegral_congr γ.toBookCurve heq, γ.pathIntegral_add h1 h2,
      Finset.sum_insert ha, ih (fun i hi => hcont i (Finset.mem_insert_of_mem hi))]

/-- Chain integral of a finite sum of continuous functions along a chain `Γ`. -/
theorem BookChain.integral_finset_sum {ι : Type*} (Γ : BookChain) (s : Finset ι)
    (F : ι → ℂ → ℂ) (hcont : ∀ i ∈ s, ContinuousOn (F i) Γ.trace) :
    Γ.integral (fun z => ∑ i ∈ s, F i z) = ∑ i ∈ s, Γ.integral (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : Γ.integral (fun _ => (0 : ℂ)) = 0 := by
      simpa using Γ.integral_const_mul 0 (fun _ => 0)
    simpa using h0
  | @insert a s ha ih =>
    have h1 : ContinuousOn (F a) Γ.trace := hcont a (Finset.mem_insert_self a s)
    have h2 : ContinuousOn (fun z => ∑ i ∈ s, F i z) Γ.trace :=
      continuousOn_finsetSum s fun i hi => hcont i (Finset.mem_insert_of_mem hi)
    have heq : EqOn (fun z => ∑ i ∈ insert a s, F i z)
        (fun z => F a z + ∑ i ∈ s, F i z) Γ.trace :=
      fun z _ => Finset.sum_insert ha
    rw [Γ.integral_congr heq, Γ.integral_add h1 h2, Finset.sum_insert ha,
      ih (fun i hi => hcont i (Finset.mem_insert_of_mem hi))]

/-- 10.41: integral of a principal-part sum `Q(z) = ∑_{k=1}^m c_k (z - a)^{-k}` (`m ≥ 1`) along a
closed path `γ` avoiding `a` equals `2πi * c_1 * Ind_γ(a)`. -/
theorem principalPart_closedPath_integral {Q : ℂ → ℂ} {a : ℂ} {m : ℕ} {c : ℕ → ℂ}
    (hm : 0 < m) (hQ : ∀ z : ℂ, z ≠ a → Q z = ∑ k ∈ Finset.Icc 1 m, c k * (z - a)⁻¹ ^ k)
    (γ : BookPath) (hcl : γ.IsClosed) (ha : a ∉ γ.trace) :
    pathIntegral Q γ.toBookCurve =
      2 * Real.pi * Complex.I * c 1 * Ind γ.toBookCurve a := by
  have hcongr : EqOn Q (fun z => ∑ k ∈ Finset.Icc 1 m, c k * (z - a)⁻¹ ^ k) γ.trace :=
    fun z hz => hQ z (fun hza => ha (hza ▸ hz))
  have hterm_cont : ∀ k ∈ Finset.Icc 1 m,
      ContinuousOn (fun z : ℂ => c k * (z - a)⁻¹ ^ k) γ.trace := by
    intro k _
    have hsub_c : Continuous (fun z : ℂ => z - a) := continuous_id.sub continuous_const
    exact continuousOn_const.mul ((hsub_c.continuousOn.inv₀
      fun z hz h0 => ha (sub_eq_zero.mp h0 ▸ hz)).pow k)
  rw [BookPath.pathIntegral_congr γ.toBookCurve hcongr,
    γ.pathIntegral_finset_sum (Finset.Icc 1 m) _ hterm_cont]
  have h1_mem : 1 ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨le_rfl, hm⟩
  have hsum_single : (∑ k ∈ Finset.Icc 1 m,
      pathIntegral (fun z => c k * (z - a)⁻¹ ^ k) γ.toBookCurve) =
      pathIntegral (fun z => c 1 * (z - a)⁻¹ ^ 1) γ.toBookCurve := by
    refine Finset.sum_eq_single (1 : ℕ) ?_ (fun hnot => (hnot h1_mem).elim)
    intro k hk hk1
    have hk_ge2 : 2 ≤ k := by
      have hk1' := (Finset.mem_Icc.mp hk).1
      omega
    rw [BookPath.pathIntegral_const_mul]
    have hzpow_eq : EqOn (fun z : ℂ => (z - a)⁻¹ ^ k) (fun z : ℂ => (z - a) ^ (-(k : ℤ))) γ.trace := by
      intro z _
      dsimp only
      rw [zpow_neg, zpow_natCast, inv_pow]
    rw [BookPath.pathIntegral_congr γ.toBookCurve hzpow_eq,
      corollary10_12_zpow (n := -(k : ℤ)) (by omega) a γ hcl (fun _ => ha), mul_zero]
  rw [hsum_single]
  simp only [pow_one]
  rw [BookPath.pathIntegral_const_mul]
  have htwo_pi_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  unfold Ind
  field_simp [htwo_pi_ne]

/-- 10.41: integral of a principal part `Q(z) = ∑_{k=1}^m c_k (z - a)^{-k}` (`m ≥ 1`) along ANY
cycle `Γ` with `a ∉ Γ*` satisfies `(2πi)⁻¹ ∫_Γ Q(z) dz = c_1 * Ind_Γ(a)`. -/
theorem principalPart_cycle_integral {Q : ℂ → ℂ} {a : ℂ} {m : ℕ} {c : ℕ → ℂ}
    (hm : 0 < m) (hQ : ∀ z : ℂ, z ≠ a → Q z = ∑ k ∈ Finset.Icc 1 m, c k * (z - a)⁻¹ ^ k)
    {Γ : BookChain} (hcyc : Γ.IsCycle) (ha : a ∉ Γ.trace) :
    (2 * Real.pi * Complex.I)⁻¹ * Γ.integral Q = c 1 * Γ.Ind a := by
  obtain ⟨Δ, hclΔ, hsubΔ, heq⟩ := hcyc
  have haΔ : a ∉ Δ.trace := fun h => ha (hsubΔ h)
  have hQ_cont : ContinuousOn Q (Γ.trace ∪ Δ.trace) := by
    have hsub : Γ.trace ∪ Δ.trace ⊆ {a}ᶜ := by
      intro z hz
      rw [mem_compl_singleton_iff]
      rintro rfl
      exact hz.elim ha haΔ
    have hcongr : EqOn Q (fun z => ∑ k ∈ Finset.Icc 1 m, c k * (z - a)⁻¹ ^ k) (Γ.trace ∪ Δ.trace) :=
      fun z hz => hQ z (mem_compl_singleton_iff.mp (hsub hz))
    refine (continuousOn_finsetSum (Finset.Icc 1 m) fun k _ => ?_).congr hcongr
    exact continuousOn_const.mul (((continuous_id.sub continuous_const).continuousOn.inv₀
      fun z hz h0 => mem_compl_singleton_iff.mp (hsub hz) (sub_eq_zero.mp (by simpa using h0))).pow k)
  rw [heq Q hQ_cont, BookChain.Ind_congr_equiv heq (fun h => h.elim ha haΔ)]
  have hΔ_int : Δ.integral Q = 2 * Real.pi * Complex.I * c 1 * Δ.Ind a := by
    clear heq hsubΔ hQ_cont ha
    induction Δ with
    | nil => simp
    | cons σ Δ ih =>
      rw [BookChain.trace_cons] at haΔ
      rw [BookChain.integral_cons, BookChain.Ind_cons,
        principalPart_closedPath_integral hm hQ σ (hclΔ σ List.mem_cons_self) (fun h => haΔ (Or.inl h)),
        ih (fun τ hτ => hclΔ τ (List.mem_cons_of_mem _ hτ)) (fun h => haΔ (Or.inr h))]
      ring
  have htwo_pi_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [hΔ_int]
  field_simp [htwo_pi_ne]

/-- Extraction of the `-1` coefficient of a principal part `Q` at `a` via the unit circle around `a`. -/
noncomputable def principalPartRes (Q : ℂ → ℂ) (a : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    pathIntegral Q (positivelyOrientedCircle a 1 zero_lt_one).toBookCurve

theorem principalPartRes_eq_coeff {Q : ℂ → ℂ} {a : ℂ} {m : ℕ} {c : ℕ → ℂ}
    (hm : 0 < m) (hQ : ∀ z : ℂ, z ≠ a → Q z = ∑ k ∈ Finset.Icc 1 m, c k * (z - a)⁻¹ ^ k) :
    principalPartRes Q a = c 1 := by
  let γ := positivelyOrientedCircle a 1 zero_lt_one
  have hcl : γ.IsClosed := positivelyOrientedCircle_isClosed a zero_lt_one
  have ha : a ∉ γ.trace := by
    rw [positivelyOrientedCircle_trace a zero_lt_one, Metric.mem_sphere, dist_self]
    norm_num
  have hcyc : BookChain.IsCycle [γ] := BookChain.isCycle_singleton_of_isClosed hcl
  have h := principalPart_cycle_integral hm hQ hcyc (by simpa using ha)
  have hind : Ind γ.toBookCurve a = 1 :=
    Ind_positivelyOrientedCircle_inside zero_lt_one (by simp [disc])
  simpa [principalPartRes, γ, hind] using h

/-- 10.41: the residue `Res(f; a)` of `f` at `a`, equal to the `(z - a)⁻¹` coefficient `c_1` of the
unique principal part of `f` at `a` whenever `f` has a pole at `a` in some open neighborhood of `a`
(and `0` otherwise). -/
noncomputable def residue (f : ℂ → ℂ) (a : ℂ) : ℂ :=
  open Classical in
  if h : ∃ (V : Set ℂ) (g Q : ℂ → ℂ), IsOpen V ∧ a ∈ V ∧ HolomorphicOn g V ∧
      IsPrincipalPart Q a ∧ EqOn f (fun z => g z + Q z) (V \ {a})
  then principalPartRes h.choose_spec.choose_spec.choose a
  else 0

theorem residue_eq_principalPartRes_of_decomp {f : ℂ → ℂ} {V : Set ℂ} {a : ℂ} {g Q : ℂ → ℂ}
    (hV : IsOpen V) (ha : a ∈ V) (hg : HolomorphicOn g V) (hQ : IsPrincipalPart Q a)
    (heq : EqOn f (fun z => g z + Q z) (V \ {a})) :
    residue f a = principalPartRes Q a := by
  classical
  have hex : ∃ (V' : Set ℂ) (g' Q' : ℂ → ℂ), IsOpen V' ∧ a ∈ V' ∧ HolomorphicOn g' V' ∧
      IsPrincipalPart Q' a ∧ EqOn f (fun z => g' z + Q' z) (V' \ {a}) :=
    ⟨V, g, Q, hV, ha, hg, hQ, heq⟩
  unfold residue
  simp only [hex, ↓reduceDIte]
  set V₀ := hex.choose
  set g₀ := hex.choose_spec.choose
  set Q₀ := hex.choose_spec.choose_spec.choose
  obtain ⟨hV₀, ha₀, hg₀, hQ₀, heq₀⟩ := hex.choose_spec.choose_spec.choose_spec
  have hQ_eq : EqOn Q₀ Q ({a}ᶜ) := by
    refine principalPart_unique_of_hasPole (hV₀.inter hV) ⟨ha₀, ha⟩
      (fun z hz => hg₀ z hz.1) (fun z hz => hg z hz.2) hQ₀ hQ ?_
    intro z hz
    exact (heq₀ ⟨hz.1.1, hz.2⟩).symm.trans (heq ⟨hz.1.2, hz.2⟩)
  unfold principalPartRes
  congr 1
  refine BookPath.pathIntegral_congr _ (hQ_eq.mono ?_)
  intro z hz
  change z ∈ (positivelyOrientedCircle a 1 zero_lt_one).trace at hz
  rw [positivelyOrientedCircle_trace a zero_lt_one] at hz
  rw [mem_compl_singleton_iff]
  rintro rfl
  rw [Metric.mem_sphere, dist_self] at hz
  norm_num at hz

theorem residue_eq_coeff_of_hasPole {f : ℂ → ℂ} {V : Set ℂ} {a : ℂ} {g Q : ℂ → ℂ}
    {m : ℕ} {c : ℕ → ℂ}
    (hV : IsOpen V) (ha : a ∈ V) (hg : HolomorphicOn g V)
    (hm : 0 < m) (hcm : c m ≠ 0)
    (hQ : ∀ z : ℂ, Q z = ∑ k ∈ Finset.Icc 1 m, c k * (z - a)⁻¹ ^ k)
    (heq : EqOn f (fun z => g z + Q z) (V \ {a})) :
    residue f a = c 1 := by
  rw [residue_eq_principalPartRes_of_decomp hV ha hg ⟨m, c, hm, hcm, hQ⟩ heq]
  exact principalPartRes_eq_coeff hm (fun z _ => hQ z)

/-- 10.41 (Definition): `f` is meromorphic in an open set `Ω` with pole set `A` if `A ⊆ Ω`, `A` has
no limit point in `Ω`, `f ∈ H(Ω \ A)`, and `f` has a pole at each point of `A`. -/
def BookMeromorphicWithPoles (f : ℂ → ℂ) (Ω A : Set ℂ) : Prop :=
  IsOpen Ω ∧ A ⊆ Ω ∧ (∀ z ∈ Ω, ¬ AccPt z (𝓟 A)) ∧
    HolomorphicOn f (Ω \ A) ∧
    ∀ a ∈ A, ∃ V : Set ℂ, IsOpen V ∧ a ∈ V ∧ V ⊆ Ω ∧ HasPole f V a

/-- 10.41 (Definition): `f` is meromorphic in `Ω` if `BookMeromorphicWithPoles f Ω A` holds for some
subset `A ⊆ Ω`. -/
def BookMeromorphicOn (f : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  ∃ A : Set ℂ, BookMeromorphicWithPoles f Ω A

/-- Canonical pole set of `f` in `Ω`. -/
def poleSet (f : ℂ → ℂ) (Ω : Set ℂ) : Set ℂ :=
  {a ∈ Ω | ∃ V : Set ℂ, IsOpen V ∧ a ∈ V ∧ V ⊆ Ω ∧ HasPole f V a}

/-- 10.41: `A = ∅` is allowed, so every `f ∈ H(Ω)` is meromorphic in `Ω` with empty pole set. -/
theorem HolomorphicOn.bookMeromorphicWithPoles_empty {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : HolomorphicOn f Ω) :
    BookMeromorphicWithPoles f Ω ∅ :=
  ⟨hΩ, empty_subset _, fun _ _ hacc => by
      rcases accPt_iff_nhds.mp hacc Set.univ Filter.univ_mem with ⟨_, ⟨_, h⟩, _⟩
      exact h,
    by simpa using hf, by simp⟩

theorem HolomorphicOn.bookMeromorphicOn {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : HolomorphicOn f Ω) :
    BookMeromorphicOn f Ω :=
  ⟨∅, hf.bookMeromorphicWithPoles_empty hΩ⟩

/-- Helper: if `A` has no limit point in open `Ω`, then `Ω \ A` is open and every compact `K ⊆ Ω`
meets `A` in a finite set, whence `A` is countable. -/
theorem isOpen_sdiff_of_no_accPt {Ω A : Set ℂ} (hΩ : IsOpen Ω)
    (hacc : ∀ z ∈ Ω, ¬ AccPt z (𝓟 A)) :
    IsOpen (Ω \ A) := by
  rw [Metric.isOpen_iff]
  rintro z ⟨hzΩ, hzA⟩
  have hnot := hacc z hzΩ
  rw [accPt_iff_nhds] at hnot
  push Not at hnot
  obtain ⟨U, hU, hdisj⟩ := hnot
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hzΩ)
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun w hw =>
    ⟨hball₁ (Metric.ball_subset_ball (min_le_left _ _) hw), ?_⟩⟩
  intro hwA
  have hwa : w = z := hdisj w ⟨hball₂ (Metric.ball_subset_ball (min_le_right _ _) hw), hwA⟩
  exact hzA (hwa ▸ hwA)

/-- 10.41 (Properties of meromorphic functions, pole sets, residues, and principal parts):
if `BookMeromorphicWithPoles f Ω A`, then:
1. `IsOpen (Ω \ A)` (`A` is relatively closed in `Ω`) and `A = poleSet f Ω`,
2. For every compact `K ⊆ Ω`, `(A ∩ K).Finite`,
3. `A.Countable`, and
4. At every `a ∈ A`, there exist an open neighborhood `V` of `a` with `V ⊆ Ω` and `V \ {a} ⊆ Ω \ A`,
   a function `g ∈ H(V)`, and a unique principal part `Q` at `a` such that `f = g + Q` on `V \ {a}`
   and `(2πi)⁻¹ ∫_Γ Q(z) dz = residue f a * Ind_Γ(a)` for every cycle `Γ` with `a ∉ Γ*`. -/
theorem theorem10_41 {f : ℂ → ℂ} {Ω A : Set ℂ} (hmero : BookMeromorphicWithPoles f Ω A) :
    IsOpen (Ω \ A) ∧
    A = poleSet f Ω ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ Ω → (A ∩ K).Finite) ∧
    A.Countable ∧
    (∀ a ∈ A, ∃ (V : Set ℂ) (g Q : ℂ → ℂ),
      IsOpen V ∧ a ∈ V ∧ V ⊆ Ω ∧ V \ {a} ⊆ Ω \ A ∧
      HolomorphicOn g V ∧ IsPrincipalPart Q a ∧
      EqOn f (fun z => g z + Q z) (V \ {a}) ∧
      (∀ Γ : BookChain, Γ.IsCycle → a ∉ Γ.trace →
        (2 * Real.pi * Complex.I)⁻¹ * Γ.integral Q = residue f a * Γ.Ind a)) := by
  rcases hmero with ⟨hΩ, hAΩ, hacc, hf_holo, hpoles⟩
  have hopen_sdiff : IsOpen (Ω \ A) := isOpen_sdiff_of_no_accPt hΩ hacc
  have hiso_nbhd : ∀ a ∈ A, ∃ U : Set ℂ, IsOpen U ∧ a ∈ U ∧ U ⊆ Ω ∧ U \ {a} ⊆ Ω \ A := by
    intro a ha
    have hnot := hacc a (hAΩ ha)
    rw [accPt_iff_nhds] at hnot
    push Not at hnot
    obtain ⟨U₀, hU₀, hdisj⟩ := hnot
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hΩ.mem_nhds (hAΩ ha)) hU₀)
    refine ⟨Metric.ball a ε, Metric.isOpen_ball, Metric.mem_ball_self hε,
      fun w hw => (hball hw).1,
      fun w hw => ⟨(hball hw.1).1, fun hwA => hw.2 (hdisj w ⟨(hball hw.1).2, hwA⟩)⟩⟩
  have hpole_eq : A = poleSet f Ω := by
    ext a
    simp only [poleSet, mem_ofPred_eq]
    refine ⟨fun ha => ⟨hAΩ ha, hpoles a ha⟩, ?_⟩
    rintro ⟨haΩ, V, hV, haV, _, hpoleV⟩
    by_contra haA
    have ha_sdiff : a ∈ Ω \ A := ⟨haΩ, haA⟩
    have hW_open : IsOpen (V ∩ (Ω \ A)) := hV.inter hopen_sdiff
    have haW : a ∈ V ∩ (Ω \ A) := ⟨haV, ha_sdiff⟩
    have hpoleW : HasPole f (V ∩ (Ω \ A)) a := hpoleV.mono hW_open haW inter_subset_left
    have hremW : HasRemovableSingularity f (V ∩ (Ω \ A)) a :=
      ⟨f, fun z hz => hf_holo z hz.2, fun _ _ => rfl⟩
    exact (theorem10_21 hpoleW.1).1 ⟨hremW, hpoleW⟩
  have hcod : Aᶜ ∈ codiscreteWithin Ω := by
    rw [mem_codiscreteWithin_accPt]
    have heq : Ω \ Aᶜ = A := by
      ext z
      simp only [Set.mem_sdiff, mem_compl_iff, not_not, and_iff_right_iff_imp]
      exact fun hz => hAΩ hz
    rwa [heq]
  have hfin_compact : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → (A ∩ K).Finite := by
    intro K hK hKΩ
    have hfin := hK.finite_sdiff_of_mem_codiscreteWithin (Filter.codiscreteWithin_mono hKΩ hcod)
    have heq : K \ Aᶜ = A ∩ K := by ext z; simp [and_comm]
    rwa [heq] at hfin
  have hcountable : A.Countable := by
    have hd : IsDiscrete A := by
      have hd' := isDiscrete_of_codiscreteWithin (s := A) hcod
      rwa [Set.inter_eq_self_of_subset_left hAΩ] at hd'
    exact (HereditarilyLindelofSpace.isLindelof A).countable_of_isDiscrete hd
  refine ⟨hopen_sdiff, hpole_eq, hfin_compact, hcountable, ?_⟩
  intro a ha
  obtain ⟨U, hU, haU, hUΩ, hUsdiff⟩ := hiso_nbhd a ha
  obtain ⟨V₀, hV₀, haV₀, _, hpole₀⟩ := hpoles a ha
  let V := U ∩ V₀
  have hV : IsOpen V := hU.inter hV₀
  have haV : a ∈ V := ⟨haU, haV₀⟩
  have hpoleV : HasPole f V a := hpole₀.mono hV haV inter_subset_right
  obtain ⟨_, g, Q, hg, hQ, heq⟩ := hpoleV
  obtain ⟨m, c, hm, hcm, hQeq⟩ := hQ
  refine ⟨V, g, Q, hV, haV, inter_subset_left.trans hUΩ,
    (Set.sdiff_subset_sdiff_left inter_subset_left).trans hUsdiff,
    hg, ⟨m, c, hm, hcm, hQeq⟩, heq, ?_⟩
  intro Γ hcyc haΓ
  rw [residue_eq_coeff_of_hasPole hV haV hg hm hcm hQeq heq]
  exact principalPart_cycle_integral hm (fun z _ => hQeq z) hcyc haΓ

/-- Compactness of `Γ.trace ∪ {z | Γ.Ind z ≠ 0}` for any cycle `Γ`. -/
theorem isCompact_trace_union_ind_ne_zero {Γ : BookChain} (hcyc : Γ.IsCycle) :
    IsCompact {z : ℂ | z ∈ Γ.trace ∨ Γ.Ind z ≠ 0} := by
  let K : Set ℂ := {z : ℂ | z ∈ Γ.trace ∨ Γ.Ind z ≠ 0}
  have hclosed : IsClosed K := by
    rw [← isOpen_compl_iff, Metric.isOpen_iff]
    intro z hz
    simp only [K, mem_compl_iff, mem_ofPred_eq, not_or, not_not] at hz
    rcases hz with ⟨hz_tr, hz_ind⟩
    have hcont_at : ContinuousAt Γ.Ind z :=
      (BookChain.continuousOn_Ind Γ).continuousAt (Γ.isClosed_trace.isOpen_compl.mem_nhds hz_tr)
    have hev : ∀ᶠ w in nhds z, w ∉ Γ.trace ∧ dist (Γ.Ind w) (Γ.Ind z) < 1 / 2 :=
      Filter.inter_mem (Γ.isClosed_trace.isOpen_compl.mem_nhds hz_tr)
        (Metric.tendsto_nhds.mp hcont_at.tendsto (1 / 2) (by positivity))
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hev
    refine ⟨ε, hε, fun w hw => ?_⟩
    obtain ⟨hw_tr, hw_dist⟩ := hball hw
    simp only [K, mem_compl_iff, mem_ofPred_eq, not_or, not_not]
    refine ⟨hw_tr, ?_⟩
    obtain ⟨n, hn⟩ := BookChain.Ind_mem_int_of_isCycle hcyc hw_tr
    rw [dist_eq_norm, hz_ind, sub_zero, hn, Complex.norm_intCast] at hw_dist
    have hn0 : n = 0 := by
      by_contra hne
      have : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
      linarith
    simp [hn, hn0]
  have hbdd : Bornology.IsBounded K := by
    obtain ⟨R, hRpos, hRsub⟩ := Γ.isCompact_trace.isBounded.subset_closedBall_lt 0 (0 : ℂ)
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset ?_
    intro z hz
    by_contra hz_ext
    have hext_compl : (Metric.closedBall (0 : ℂ) R)ᶜ ⊆ (Γ.trace)ᶜ := compl_subset_compl.mpr hRsub
    have hz_tr : z ∉ Γ.trace := hext_compl hz_ext
    have hext_conn := isConnected_compl_closedBall (0 : ℂ) hRpos.le
    let C₀ := bookComponent (Γ.trace)ᶜ z
    have hC₀_mem : C₀ ∈ bookComponents (Γ.trace)ᶜ := ⟨z, hz_tr, rfl⟩
    have hC₀_eq : C₀ = connectedComponentIn (Γ.trace)ᶜ z :=
      bookComponent_eq_connectedComponentIn (Γ.trace)ᶜ z
    have hsub_C₀ : (Metric.closedBall (0 : ℂ) R)ᶜ ⊆ C₀ :=
      hC₀_eq ▸ hext_conn.isPreconnected.subset_connectedComponentIn hz_ext hext_compl
    have hunbdd_ext : ¬ Bornology.IsBounded (Metric.closedBall (0 : ℂ) R)ᶜ := by
      intro hb
      obtain ⟨M, hM⟩ := hb.subset_closedBall (0 : ℂ)
      let w : ℂ := ((max R M + 1 : ℝ) : ℂ)
      have hw_norm : ‖w‖ = max R M + 1 := by
        simp only [w, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith [le_max_left R M] : 0 < max R M + 1)]
      have hw_ext : w ∈ (Metric.closedBall (0 : ℂ) R)ᶜ := by
        rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_zero_right, hw_norm]
        linarith [le_max_left R M]
      have hw_M := Metric.mem_closedBall.mp (hM hw_ext)
      rw [dist_zero_right, hw_norm] at hw_M
      linarith [le_max_right R M]
    have hunbdd_C₀ : ¬ Bornology.IsBounded C₀ := fun hb => hunbdd_ext (hb.subset hsub_C₀)
    have hz_C₀ : z ∈ C₀ := hC₀_eq ▸ mem_connectedComponentIn hz_tr
    have hind0 : Γ.Ind z = 0 :=
      BookChain.Ind_eq_zero_of_mem_unbounded_component_of_isCycle hcyc hC₀_mem hunbdd_C₀ hz_C₀
    rcases hz with hz_in | hz_ne
    · exact hz_tr hz_in
    · exact hz_ne hind0
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

/-- 10.42 (Residue Theorem): suppose `f` is meromorphic in an open set `Ω` with pole set `A`. If `Γ`
is a cycle in `Ω \ A` such that `Ind_Γ(z) = 0` for all `z ∉ Ω`, then:
1. Only finitely many points `a ∈ A` satisfy `Ind_Γ(a) ≠ 0`, and
2. `(2πi)⁻¹ ∫_Γ f(z) dz = ∑_{a ∈ A} Res(f; a) Ind_Γ(a)` (both as a finite sum over the active poles
   and as an unconditional `tsum` over `A`). -/
theorem theorem10_42 {f : ℂ → ℂ} {Ω A : Set ℂ} (hmero : BookMeromorphicWithPoles f Ω A)
    {Γ : BookChain} (hcyc : Γ.IsCycle) (hΓ : Γ.trace ⊆ Ω \ A)
    (hext : ∀ z, z ∉ Ω → Γ.Ind z = 0) :
    ∃ hfin : {a ∈ A | Γ.Ind a ≠ 0}.Finite,
      (2 * Real.pi * Complex.I)⁻¹ * Γ.integral f =
        ∑ a ∈ hfin.toFinset, residue f a * Γ.Ind a ∧
      (2 * Real.pi * Complex.I)⁻¹ * Γ.integral f =
        ∑' a : A, residue f a * Γ.Ind a := by
  classical
  have h41 := theorem10_41 hmero
  rcases h41 with ⟨hopen_sdiff, _, hfin_compact, _, hpole_data⟩
  rcases hmero with ⟨hΩ, hAΩ, hacc, hf_holo, _⟩
  let K : Set ℂ := {z : ℂ | z ∈ Γ.trace ∨ Γ.Ind z ≠ 0}
  have hK_comp : IsCompact K := isCompact_trace_union_ind_ne_zero hcyc
  have hK_sub : K ⊆ Ω := by
    rintro z (hz_tr | hz_ind)
    · exact (hΓ hz_tr).1
    · by_contra hzΩ
      exact hz_ind (hext z hzΩ)
  have hfin : {a ∈ A | Γ.Ind a ≠ 0}.Finite :=
    (hfin_compact K hK_comp hK_sub).subset fun a ha => ⟨ha.1, Or.inr ha.2⟩
  refine ⟨hfin, ?_⟩
  let F : Finset ℂ := hfin.toFinset
  have hmem_F : ∀ z : ℂ, z ∈ F ↔ z ∈ A ∧ Γ.Ind z ≠ 0 := fun z => by
    simp [F]
  -- Choose local pole decompositions `(V_a, g_a, Q_a)` for every `a ∈ F`
  have hF_A : ∀ a ∈ F, a ∈ A := fun a ha => ((hmem_F a).mp ha).1
  let V_of : (a : ℂ) → a ∈ F → Set ℂ := fun a ha => (hpole_data a (hF_A a ha)).choose
  let g_of : (a : ℂ) → a ∈ F → (ℂ → ℂ) :=
    fun a ha => (hpole_data a (hF_A a ha)).choose_spec.choose
  let Q_of : (a : ℂ) → a ∈ F → (ℂ → ℂ) :=
    fun a ha => (hpole_data a (hF_A a ha)).choose_spec.choose_spec.choose
  let Q_tot : ℂ → ℂ → ℂ := fun a z => if ha : a ∈ F then Q_of a ha z else 0
  let g_tot : ℂ → ℂ → ℂ := fun a z => if ha : a ∈ F then g_of a ha z else 0
  have hspec : ∀ (a : ℂ) (ha : a ∈ F),
      IsOpen (V_of a ha) ∧ a ∈ V_of a ha ∧ V_of a ha ⊆ Ω ∧
      V_of a ha \ {a} ⊆ Ω \ A ∧ HolomorphicOn (g_tot a) (V_of a ha) ∧
      IsPrincipalPart (Q_tot a) a ∧
      EqOn f (fun z => g_tot a z + Q_tot a z) (V_of a ha \ {a}) ∧
      (∀ Δ : BookChain, Δ.IsCycle → a ∉ Δ.trace →
        (2 * Real.pi * Complex.I)⁻¹ * Δ.integral (Q_tot a) = residue f a * Δ.Ind a) := by
    intro a ha
    have hs := (hpole_data a (hF_A a ha)).choose_spec.choose_spec.choose_spec
    have hg_eq : g_tot a = g_of a ha := funext fun z => by simp [g_tot, ha]
    have hQ_eq : Q_tot a = Q_of a ha := funext fun z => by simp [Q_tot, ha]
    rw [hg_eq, hQ_eq]
    exact hs
  -- Domain `Ω' = Ω \ (A \ F)` is open, and `h_ext` is holomorphic on `Ω'`
  let Ω' : Set ℂ := Ω \ (A \ (F : Set ℂ))
  have hΩ'_open : IsOpen Ω' :=
    isOpen_sdiff_of_no_accPt hΩ fun z hzΩ hacc' =>
      hacc z hzΩ (hacc'.mono (Filter.principal_mono.mpr Set.sdiff_subset))
  let h_ext : ℂ → ℂ := fun z =>
    if z ∈ F then g_tot z z - ∑ b ∈ F.erase z, Q_tot b z
    else f z - ∑ b ∈ F, Q_tot b z
  have hh_holo : HolomorphicOn h_ext Ω' := by
    intro z₀ hz₀
    by_cases hzF : z₀ ∈ F
    · obtain ⟨hV_open, hzV, _, hVsdiff, hg_holo, _, hfeq, _⟩ := hspec z₀ hzF
      let W : Set ℂ := V_of z₀ hzF \ ((F.erase z₀ : Finset ℂ) : Set ℂ)
      have hW_open : IsOpen W := hV_open.sdiff (Finset.finite_toSet _).isClosed
      have hzW : z₀ ∈ W := ⟨hzV, by simp⟩
      let model : ℂ → ℂ := fun z => g_tot z₀ z - ∑ b ∈ F.erase z₀, Q_tot b z
      have hmodel_diff : DifferentiableAt ℂ model z₀ := by
        have hg_at : HasDerivAt (g_tot z₀) (deriv (g_tot z₀) z₀) z₀ :=
          (hg_holo z₀ hzV).hasDerivAt
        have hsum_diff : DifferentiableAt ℂ (fun z => ∑ b ∈ F.erase z₀, Q_tot b z) z₀ := by
          have hd_each : ∀ b ∈ F.erase z₀, DifferentiableAt ℂ (Q_tot b) z₀ := by
            intro b hb
            have hbz : z₀ ≠ b := (Finset.mem_erase.mp hb).1.symm
            exact holomorphicOn_of_isPrincipalPart
              (hspec b (Finset.mem_of_mem_erase hb)).2.2.2.2.2.1 z₀ hbz
          have hsum_hd := HasDerivAt.sum fun b hb => (hd_each b hb).hasDerivAt
          rw [Finset.sum_fn] at hsum_hd
          exact hsum_hd.differentiableAt
        exact (hg_at.sub hsum_diff.hasDerivAt).differentiableAt
      have hev : h_ext =ᶠ[nhds z₀] model := by
        filter_upwards [hW_open.mem_nhds hzW] with z hz
        by_cases hzz₀ : z = z₀
        · subst hzz₀; simp [h_ext, model, hzF]
        · have hz_not_F : z ∉ F := by
            intro hz_in
            exact hz.2 (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hzz₀, hz_in⟩))
          simp only [h_ext, hz_not_F, ↓reduceIte, model]
          have hfz : f z = g_tot z₀ z + Q_tot z₀ z := hfeq ⟨hz.1, hzz₀⟩
          rw [hfz, ← Finset.add_sum_erase F (fun b => Q_tot b z) hzF]
          ring
      exact hmodel_diff.congr_of_eventuallyEq hev
    · have hz_sdiff : z₀ ∈ Ω \ A := by
        refine ⟨hz₀.1, fun hzA => ?_⟩
        exact hz₀.2 ⟨hzA, hzF⟩
      let model : ℂ → ℂ := fun z => f z - ∑ b ∈ F, Q_tot b z
      have hmodel_diff : DifferentiableAt ℂ model z₀ := by
        have hf_at : HasDerivAt f (deriv f z₀) z₀ := (hf_holo z₀ hz_sdiff).hasDerivAt
        have hsum_diff : DifferentiableAt ℂ (fun z => ∑ b ∈ F, Q_tot b z) z₀ := by
          have hd_each : ∀ b ∈ F, DifferentiableAt ℂ (Q_tot b) z₀ := by
            intro b hb
            have hbz : z₀ ≠ b := fun heq => hzF (heq ▸ hb)
            exact holomorphicOn_of_isPrincipalPart (hspec b hb).2.2.2.2.2.1 z₀ hbz
          have hsum_hd := HasDerivAt.sum fun b hb => (hd_each b hb).hasDerivAt
          rw [Finset.sum_fn] at hsum_hd
          exact hsum_hd.differentiableAt
        exact (hf_at.sub hsum_diff.hasDerivAt).differentiableAt
      have hev : h_ext =ᶠ[nhds z₀] model := by
        filter_upwards [hopen_sdiff.mem_nhds hz_sdiff] with z hz
        have hz_not_F : z ∉ F := fun hz_in => hz.2 (hF_A z hz_in)
        simp [h_ext, hz_not_F, model]
      exact hmodel_diff.congr_of_eventuallyEq hev
  -- Apply Cauchy's theorem 10.35 to `h_ext` on `Ω'`
  have hΓ_Ω' : Γ.trace ⊆ Ω' := fun z hz => ⟨(hΓ hz).1, fun h => (hΓ hz).2 h.1⟩
  have hext_Ω' : ∀ z, z ∉ Ω' → Γ.Ind z = 0 := by
    intro z hz
    by_cases hzΩ : z ∈ Ω
    · have hzAF : z ∈ A \ (F : Set ℂ) := by
        by_contra hnot
        exact hz ⟨hzΩ, hnot⟩
      have hnot_F : ¬ (z ∈ A ∧ Γ.Ind z ≠ 0) := by
        rw [← hmem_F z]
        exact hzAF.2
      by_contra hne
      exact hnot_F ⟨hzAF.1, hne⟩
    · exact hext z hzΩ
  have hint_zero : Γ.integral h_ext = 0 :=
    ((theorem10_35 hΩ'_open).1 hh_holo Γ hcyc hΓ_Ω' hext_Ω').2
  -- Expand `Γ.integral h_ext` on `Γ.trace ⊆ Ω \ A`
  have hcongr_tr : EqOn h_ext (fun z => f z - ∑ b ∈ F, Q_tot b z) Γ.trace := by
    intro z hz
    have hz_not_F : z ∉ F := fun hz_in => (hΓ hz).2 (hF_A z hz_in)
    simp [h_ext, hz_not_F]
  have hf_cont_tr : ContinuousOn f Γ.trace :=
    fun z hz => (hf_holo z (hΓ hz)).continuousAt.continuousWithinAt
  have hQ_cont_tr : ∀ b ∈ F, ContinuousOn (Q_tot b) Γ.trace := by
    intro b hb z hz
    have hzb : z ∈ ({b}ᶜ : Set ℂ) := by
      rw [mem_compl_singleton_iff]
      rintro rfl
      exact (hΓ hz).2 (hF_A z hb)
    exact (holomorphicOn_of_isPrincipalPart (hspec b hb).2.2.2.2.2.1 z hzb).continuousAt.continuousWithinAt
  have hsum_cont_tr : ContinuousOn (fun z => ∑ b ∈ F, Q_tot b z) Γ.trace :=
    continuousOn_finsetSum F hQ_cont_tr
  rw [Γ.integral_congr hcongr_tr, Γ.integral_sub hf_cont_tr hsum_cont_tr,
    Γ.integral_finset_sum F Q_tot hQ_cont_tr, sub_eq_zero] at hint_zero
  have hfin_eq : (2 * Real.pi * Complex.I)⁻¹ * Γ.integral f =
      ∑ a ∈ F, residue f a * Γ.Ind a := by
    rw [hint_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha_not_tr : a ∉ Γ.trace := fun hz => (hΓ hz).2 (hF_A a ha)
    exact (hspec a ha).2.2.2.2.2.2.2 Γ hcyc ha_not_tr
  refine ⟨hfin_eq, hfin_eq.trans ?_⟩
  -- Identify finite sum over `F` with `tsum` over `A`
  let F_sub : Finset A := F.subtype (fun z => z ∈ A)
  rw [tsum_eq_sum (s := F_sub)]
  · refine Finset.sum_bij (fun (a : ℂ) (ha : a ∈ F) => (⟨a, hF_A a ha⟩ : A))
      (fun a ha => Finset.mem_subtype.mpr ha)
      (fun _ _ _ _ h => congr_arg Subtype.val h)
      (fun ⟨a, haA⟩ ha_sub => ⟨a, Finset.mem_subtype.mp ha_sub, rfl⟩)
      (fun _ _ => rfl)
  · intro ⟨a, haA⟩ hnot
    have hnot_F : a ∉ F := fun haF => hnot (Finset.mem_subtype.mpr haF)
    rw [hmem_F] at hnot_F
    have hind0 : Γ.Ind a = 0 := by
      by_contra hne
      exact hnot_F ⟨haA, hne⟩
    simp [hind0]

/-! ### 10.43: Argument Principle & Rouché's Theorem -/

/-- Image path `f ∘ γ` of a `BookPath` under a holomorphic function `f ∈ H(Ω)` with `γ* ⊆ Ω`. -/
def BookPath.compHolomorphic (γ : BookPath) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : HolomorphicOn f Ω) (hγ : γ.trace ⊆ Ω) : BookPath where
  α := γ.α
  β := γ.β
  lt_endpoints := γ.lt_endpoints
  toFun := f ∘ γ.toFun
  continuousOn :=
    have hf_cont : ContinuousOn f Ω := fun z hz => (hf z hz).continuousAt.continuousWithinAt
    hf_cont.comp γ.continuousOn fun t ht => hγ (γ.mem_trace_of_mem_Icc ht)
  piecewiseC1 := by
    obtain ⟨n, s, d, hs, hs0, hsn, hdcont, hd⟩ := γ.piecewiseC1
    have hdf : HolomorphicOn (deriv f) Ω := holomorphicOn_deriv hΩ hf
    have hderiv_cont : ContinuousOn (deriv f) Ω :=
      fun z hz => (hdf z hz).continuousAt.continuousWithinAt
    refine ⟨n, s, fun i t => d i t * deriv f (γ.toFun t), hs, hs0, hsn, ?_, ?_⟩
    · intro i
      have hsub : Icc (s i.castSucc) (s i.succ) ⊆ Icc γ.α γ.β :=
        Icc_subset_Icc (hs0 ▸ hs.monotone (Fin.zero_le _)) (hsn ▸ hs.monotone (Fin.le_last _))
      exact (hdcont i).mul
        (hderiv_cont.comp (γ.continuousOn.mono hsub) fun t ht => hγ (γ.mem_trace_of_mem_Icc (hsub ht)))
    · intro i t ht
      have hsub : Ioo (s i.castSucc) (s i.succ) ⊆ Ioo γ.α γ.β :=
        Ioo_subset_Ioo (hs0 ▸ hs.monotone (Fin.zero_le _)) (hsn ▸ hs.monotone (Fin.le_last _))
      have ht_outer := hsub ht
      have hf_at : HasDerivAt f (deriv f (γ.toFun t)) (γ.toFun t) :=
        (hf (γ.toFun t) (hγ (γ.mem_trace_of_mem_Icc (Ioo_subset_Icc_self ht_outer)))).hasDerivAt
      simpa only [smul_eq_mul] using hf_at.scomp_hasDerivWithinAt t (hd i t ht)

@[simp] theorem BookPath.compHolomorphic_trace (γ : BookPath) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : HolomorphicOn f Ω) (hγ : γ.trace ⊆ Ω) :
    (γ.compHolomorphic hΩ hf hγ).trace = f '' γ.trace := by
  ext w
  simp [BookPath.compHolomorphic, BookPath.trace, BookCurve.trace, Set.image_image]

theorem BookPath.compHolomorphic_isClosed {γ : BookPath} (hcl : γ.IsClosed)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} (hf : HolomorphicOn f Ω) (hγ : γ.trace ⊆ Ω) :
    (γ.compHolomorphic hΩ hf hγ).IsClosed := by
  show f (γ.toFun γ.α) = f (γ.toFun γ.β)
  rw [show γ.toFun γ.α = γ.toFun γ.β from hcl]

theorem BookPath.pathIntegral_compHolomorphic (γ : BookPath) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : HolomorphicOn f Ω) (hγ : γ.trace ⊆ Ω) (g : ℂ → ℂ) :
    pathIntegral g (γ.compHolomorphic hΩ hf hγ).toBookCurve =
      pathIntegral (fun z => g (f z) * deriv f z) γ.toBookCurve := by
  unfold pathIntegral
  change (∫ t in γ.α..γ.β, g (f (γ.toFun t)) * derivWithin (f ∘ γ.toFun) (Icc γ.α γ.β) t) =
    ∫ t in γ.α..γ.β, (g (f (γ.toFun t)) * deriv f (γ.toFun t)) * derivWithin γ.toFun (Icc γ.α γ.β) t
  apply intervalIntegral.integral_congr_ae_restrict
  change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc γ.α γ.β)] _
  rw [Set.uIoc_of_le γ.le_endpoints, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  obtain ⟨n, s, d, hs, hs0, hsn, _, hd⟩ := γ.piecewiseC1
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo,
    (Set.finite_range s).countable.ae_notMem _] with t ht hnot
  let T : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => s j ≤ t)
  have hTne : T.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs0 ▸ ht.1.le⟩⟩
  let j := T.max' hTne
  have hjlt : s j < t := lt_of_le_of_ne (Finset.mem_filter.mp (T.max'_mem hTne)).2 fun h => hnot ⟨j, h⟩
  have hjne : j ≠ Fin.last n := fun h => by
    have : s (Fin.last n) < t := h ▸ hjlt
    linarith [hsn, ht.2]
  obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hjne
  rw [← hi] at hjlt
  have hsucc : t < s i.succ := by
    by_contra hge
    have hmax : i.succ ≤ j :=
      T.le_max' i.succ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hge⟩)
    rw [← hi] at hmax
    exact not_le.mpr i.castSucc_lt_succ hmax
  have hg_at : HasDerivAt γ.toFun (d i t) t :=
    (hd i t ⟨hjlt, hsucc⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hf_at : HasDerivAt f (deriv f (γ.toFun t)) (γ.toFun t) :=
    (hf (γ.toFun t) (hγ (γ.mem_trace_of_mem_Icc (Ioo_subset_Icc_self ht)))).hasDerivAt
  have hcomp_d : derivWithin (f ∘ γ.toFun) (Icc γ.α γ.β) t = d i t * deriv f (γ.toFun t) := by
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    simpa only [smul_eq_mul] using (hf_at.scomp t hg_at).deriv
  have hγ_d : derivWithin γ.toFun (Icc γ.α γ.β) t = d i t := by
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    exact hg_at.deriv
  rw [hcomp_d, hγ_d]
  ring

/-- 10.18 / 10.43: multiplicity (order) `m ≥ 1` of a zero `a ∈ Ω` of a non-identically-zero
holomorphic function `f` on a region `Ω` (`0` if `f a ≠ 0` or hypotheses do not apply). -/
noncomputable def zeroOrder (f : ℂ → ℂ) (Ω : Set ℂ) (a : ℂ) : ℕ :=
  open Classical in
  if h : IsRegion Ω ∧ HolomorphicOn f Ω ∧ ¬ Set.EqOn f 0 Ω ∧ a ∈ Ω ∧ f a = 0
  then (existsUnique_zero_order h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2).exists.choose
  else 0

theorem zeroOrder_spec {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsRegion Ω) (hf : HolomorphicOn f Ω)
    (hne : ¬ Set.EqOn f 0 Ω) {a : ℂ} (ha : a ∈ Ω) (hfa : f a = 0) :
    0 < zeroOrder f Ω a ∧
      ∃ g : ℂ → ℂ, HolomorphicOn g Ω ∧ g a ≠ 0 ∧
        ∀ z ∈ Ω, f z = (z - a) ^ zeroOrder f Ω a * g z := by
  classical
  have h : IsRegion Ω ∧ HolomorphicOn f Ω ∧ ¬ Set.EqOn f 0 Ω ∧ a ∈ Ω ∧ f a = 0 :=
    ⟨hΩ, hf, hne, ha, hfa⟩
  simp only [zeroOrder, h]
  exact (existsUnique_zero_order hΩ hf hne ha hfa).exists.choose_spec

/-- 10.43: interior index-one set `Ω₁ = {z ∈ Ω \ γ* : Ind_γ(z) = 1}` of a closed path `γ` in `Ω`. -/
def indexOneSet (γ : BookPath) (Ω : Set ℂ) : Set ℂ :=
  {a ∈ Ω | a ∉ γ.trace ∧ Ind γ.toBookCurve a = 1}

/-- 10.43: for a non-identically-zero `f ∈ H(Ω)` on a region `Ω`, `f' / f` is meromorphic in `Ω`
with pole set `zeroSet f Ω`, and has simple poles with residue `(zeroOrder f Ω a : ℂ)` at each zero. -/
theorem bookMeromorphicWithPoles_logDeriv {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsRegion Ω) (hf : HolomorphicOn f Ω) (hne : ¬ Set.EqOn f 0 Ω) :
    BookMeromorphicWithPoles (fun z => deriv f z / f z) Ω (zeroSet f Ω) ∧
    ∀ a ∈ zeroSet f Ω, residue (fun z => deriv f z / f z) a = (zeroOrder f Ω a : ℂ) := by
  have hno_acc : ∀ z ∈ Ω, ¬ AccPt z (𝓟 (zeroSet f Ω)) := by
    rcases zeroSet_eq_or_no_accumulation hΩ hf with hall | hna
    · exfalso
      apply hne
      intro z hz
      have : z ∈ zeroSet f Ω := hall.symm ▸ hz
      exact this.2
    · exact hna
  have hdf : HolomorphicOn (deriv f) Ω := holomorphicOn_deriv hΩ.1 hf
  have hholo_sdiff : HolomorphicOn (fun z => deriv f z / f z) (Ω \ zeroSet f Ω) := by
    intro z hz
    have hfz : f z ≠ 0 := fun h0 => hz.2 ⟨hz.1, h0⟩
    exact ((hdf z hz.1).hasDerivAt.div (hf z hz.1).hasDerivAt hfz).differentiableAt
  have hpole_at : ∀ a ∈ zeroSet f Ω,
      ∃ (V : Set ℂ) (g_reg Q : ℂ → ℂ),
        IsOpen V ∧ a ∈ V ∧ V ⊆ Ω ∧ V \ {a} ⊆ Ω \ zeroSet f Ω ∧ HolomorphicOn g_reg V ∧
        (∀ z : ℂ, Q z = ∑ k ∈ Finset.Icc 1 1, (fun _ => (zeroOrder f Ω a : ℂ)) k * (z - a)⁻¹ ^ k) ∧
        EqOn (fun z => deriv f z / f z) (fun z => g_reg z + Q z) (V \ {a}) := by
    intro a ha
    obtain ⟨hm_pos, g, hg, hga, hfg⟩ := zeroOrder_spec hΩ hf hne ha.1 ha.2
    set m := zeroOrder f Ω a
    let V : Set ℂ := {z ∈ Ω | g z ≠ 0}
    have hV_open : IsOpen V :=
      isOpen_iff_mem_nhds.mpr fun z hz =>
        Filter.inter_mem (hΩ.1.mem_nhds hz.1) ((hg z hz.1).continuousAt.eventually_ne hz.2)
    have haV : a ∈ V := ⟨ha.1, hga⟩
    have hVsdiff : V \ {a} ⊆ Ω \ zeroSet f Ω := by
      intro z hz
      refine ⟨hz.1.1, fun hz0 => ?_⟩
      have hfz : f z = (z - a) ^ m * g z := hfg z hz.1.1
      rw [hz0.2] at hfz
      exact mul_ne_zero (pow_ne_zero m (sub_ne_zero.mpr hz.2)) hz.1.2 hfz.symm
    let g_reg : ℂ → ℂ := fun z => deriv g z / g z
    have hdg : HolomorphicOn (deriv g) Ω := holomorphicOn_deriv hΩ.1 hg
    have hg_reg : HolomorphicOn g_reg V := fun z hz =>
      ((hdg z hz.1).hasDerivAt.div (hg z hz.1).hasDerivAt hz.2).differentiableAt
    let Q : ℂ → ℂ := fun z => ∑ k ∈ Finset.Icc 1 1, (fun _ => (m : ℂ)) k * (z - a)⁻¹ ^ k
    refine ⟨V, g_reg, Q, hV_open, haV, fun z hz => hz.1, hVsdiff, hg_reg, fun _ => rfl, ?_⟩
    intro z hz
    have hzΩ : z ∈ Ω := hz.1.1
    have hgz : g z ≠ 0 := hz.1.2
    have hza : z - a ≠ 0 := sub_ne_zero.mpr hz.2
    have hev_f : f =ᶠ[nhds z] fun w => (w - a) ^ m * g w := by
      filter_upwards [hΩ.1.mem_nhds hzΩ] with w hw
      exact hfg w hw
    have hd_prod : HasDerivAt (fun w : ℂ => (w - a) ^ m * g w)
        ((m : ℂ) * (z - a) ^ (m - 1) * g z + (z - a) ^ m * deriv g z) z := by
      convert (((hasDerivAt_id z).sub_const a).pow m).mul (hg z hzΩ).hasDerivAt using 2 <;>
        simp [Pi.pow_apply]
    have hdf_z : deriv f z = (m : ℂ) * (z - a) ^ (m - 1) * g z + (z - a) ^ m * deriv g z :=
      hev_f.deriv_eq.trans hd_prod.deriv
    have hfz : f z = (z - a) ^ m * g z := hfg z hzΩ
    have hm_split : (z - a) ^ m = (z - a) ^ (m - 1) * (z - a) := by
      conv_lhs => rw [← Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos), pow_succ]
    have hpow_ne : (z - a) ^ (m - 1) ≠ 0 := pow_ne_zero (m - 1) hza
    simp only [g_reg, Q, Finset.Icc_self, Finset.sum_singleton, pow_one]
    rw [hdf_z, hfz, hm_split]
    field_simp [hza, hgz, hpow_ne]
    ring
  refine ⟨⟨hΩ.1, fun _ hz => hz.1, hno_acc, hholo_sdiff, ?_⟩, ?_⟩
  · intro a ha
    obtain ⟨V, g_reg, Q, hV_open, haV, hVΩ, hVsdiff, hg_reg, hQeq, heq⟩ := hpole_at a ha
    obtain ⟨hm_pos, _⟩ := zeroOrder_spec hΩ hf hne ha.1 ha.2
    have hm_ne : (zeroOrder f Ω a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm_pos.ne'
    exact ⟨V, hV_open, haV, hVΩ, ⟨hV_open, haV, fun z hz => hholo_sdiff z (hVsdiff hz)⟩,
      g_reg, Q, hg_reg, ⟨1, fun _ => (zeroOrder f Ω a : ℂ), zero_lt_one, hm_ne, hQeq⟩, heq⟩
  · intro a ha
    obtain ⟨V, g_reg, Q, hV_open, haV, _, _, hg_reg, hQeq, heq⟩ := hpole_at a ha
    obtain ⟨hm_pos, _⟩ := zeroOrder_spec hΩ hf hne ha.1 ha.2
    have hm_ne : (zeroOrder f Ω a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm_pos.ne'
    exact residue_eq_coeff_of_hasPole hV_open haV hg_reg zero_lt_one hm_ne hQeq heq

/-- 10.43(a) (Argument Principle): suppose `γ` is a closed path in a region `Ω` such that
`Ind_γ(α) = 0` for all `α ∉ Ω` and `Ind_γ(α) ∈ {0, 1}` for all `α ∈ Ω \ γ*`. Let
`Ω₁ = indexOneSet γ Ω = {α ∈ Ω \ γ* | Ind_γ(α) = 1}`. If `f ∈ H(Ω)` has no zeros on `γ*`, then:
1. `zeroSet f Ω ∩ Ω₁` is finite, and
2. `Ind_{f ∘ γ}(0) = (2πi)⁻¹ ∫_γ (f'(z) / f(z)) dz = ∑_{a ∈ zeroSet f Ω ∩ Ω₁} zeroOrder f Ω a`
   (the number of zeros of `f` in `Ω₁`, counted according to multiplicity). -/
theorem theorem10_43_argument_principle {Ω : Set ℂ} (hΩ : IsRegion Ω)
    {γ : BookPath} (hcl : γ.IsClosed) (hγ : γ.trace ⊆ Ω)
    (hext : ∀ α, α ∉ Ω → Ind γ.toBookCurve α = 0)
    (h01 : ∀ α ∈ Ω, α ∉ γ.trace → Ind γ.toBookCurve α = 0 ∨ Ind γ.toBookCurve α = 1)
    {f : ℂ → ℂ} (hf : HolomorphicOn f Ω) (hnz : ∀ z ∈ γ.trace, f z ≠ 0) :
    ∃ hfin : (zeroSet f Ω ∩ indexOneSet γ Ω).Finite,
      0 ∉ (γ.compHolomorphic hΩ.1 hf hγ).trace ∧
      Ind (γ.compHolomorphic hΩ.1 hf hγ).toBookCurve 0 =
        (2 * Real.pi * Complex.I)⁻¹ * pathIntegral (fun z => deriv f z / f z) γ.toBookCurve ∧
      (2 * Real.pi * Complex.I)⁻¹ * pathIntegral (fun z => deriv f z / f z) γ.toBookCurve =
        ((∑ a ∈ hfin.toFinset, zeroOrder f Ω a : ℕ) : ℂ) := by
  classical
  have hStart_tr : γ.toFun γ.α ∈ γ.trace := γ.mem_trace_of_mem_Icc (left_mem_Icc.mpr γ.le_endpoints)
  have hne : ¬ Set.EqOn f 0 Ω := fun hall => hnz _ hStart_tr (hall (hγ hStart_tr))
  obtain ⟨hmero, hres⟩ := bookMeromorphicWithPoles_logDeriv hΩ hf hne
  have hcyc : BookChain.IsCycle [γ] := BookChain.isCycle_singleton_of_isClosed hcl
  have hΓ_sdiff : BookChain.trace [γ] ⊆ Ω \ zeroSet f Ω := by
    rw [BookChain.trace_singleton]
    exact fun z hz => ⟨hγ hz, fun hz0 => hnz z hz hz0.2⟩
  have hext_cyc : ∀ z, z ∉ Ω → BookChain.Ind [γ] z = 0 := by
    intro z hz
    simpa using hext z hz
  obtain ⟨hfin_act, hres_eq, _⟩ := theorem10_42 hmero hcyc hΓ_sdiff hext_cyc
  have hset_eq : {a ∈ zeroSet f Ω | BookChain.Ind [γ] a ≠ 0} = zeroSet f Ω ∩ indexOneSet γ Ω := by
    ext a
    simp only [mem_ofPred_eq, BookChain.Ind_singleton, mem_inter_iff, indexOneSet]
    refine ⟨?_, ?_⟩
    · rintro ⟨ha0, hind_ne⟩
      have ha_not_tr : a ∉ γ.trace := fun htr => hnz a htr ha0.2
      rcases h01 a ha0.1 ha_not_tr with h0 | h1
      · exact (hind_ne h0).elim
      · exact ⟨ha0, ha0.1, ha_not_tr, h1⟩
    · rintro ⟨ha0, _, _, h1⟩
      exact ⟨ha0, by rw [h1]; exact one_ne_zero⟩
  have hfin : (zeroSet f Ω ∩ indexOneSet γ Ω).Finite := hset_eq ▸ hfin_act
  refine ⟨hfin, ?_, ?_, ?_⟩
  · rw [BookPath.compHolomorphic_trace]
    rintro ⟨z, hz, hfz0⟩
    exact hnz z hz hfz0
  · unfold Ind
    rw [γ.pathIntegral_compHolomorphic hΩ.1 hf hγ]
    congr 1
    refine BookPath.pathIntegral_congr _ fun z _ => ?_
    simp [div_eq_inv_mul]
  · rw [BookChain.integral_singleton] at hres_eq
    rw [hres_eq, Nat.cast_sum]
    have hfinset_eq : hfin_act.toFinset = hfin.toFinset := by
      ext a
      simp only [Set.Finite.mem_toFinset]
      exact Eq.to_iff (congr_arg (a ∈ ·) hset_eq)
    rw [hfinset_eq]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha_mem : a ∈ zeroSet f Ω ∩ indexOneSet γ Ω := hfin.mem_toFinset.mp ha
    rw [BookChain.Ind_singleton, hres a ha_mem.1, ha_mem.2.2.2, mul_one]

/-- 10.43(b) (Rouché's Theorem): under the geometric hypotheses of 10.43(a), if `f, g ∈ H(Ω)` and
`‖f(z) - g(z)‖ < ‖f(z)‖` for all `z ∈ γ*`, then neither `f` nor `g` vanishes on `γ*`, and `f` and
`g` have the exact same number of zeros in `Ω₁ = indexOneSet γ Ω`, counted according to multiplicity. -/
theorem theorem10_43_rouche {Ω : Set ℂ} (hΩ : IsRegion Ω)
    {γ : BookPath} (hcl : γ.IsClosed) (hγ : γ.trace ⊆ Ω)
    (hext : ∀ α, α ∉ Ω → Ind γ.toBookCurve α = 0)
    (h01 : ∀ α ∈ Ω, α ∉ γ.trace → Ind γ.toBookCurve α = 0 ∨ Ind γ.toBookCurve α = 1)
    {f g : ℂ → ℂ} (hf : HolomorphicOn f Ω) (hg : HolomorphicOn g Ω)
    (hstrict : ∀ z ∈ γ.trace, ‖f z - g z‖ < ‖f z‖) :
    (∀ z ∈ γ.trace, f z ≠ 0 ∧ g z ≠ 0) ∧
    ∃ (hfin_f : (zeroSet f Ω ∩ indexOneSet γ Ω).Finite)
      (hfin_g : (zeroSet g Ω ∩ indexOneSet γ Ω).Finite),
      (∑ a ∈ hfin_f.toFinset, zeroOrder f Ω a) =
        ∑ a ∈ hfin_g.toFinset, zeroOrder g Ω a := by
  have hnz_f : ∀ z ∈ γ.trace, f z ≠ 0 := by
    intro z hz h0
    have hlt := hstrict z hz
    rw [h0, norm_zero] at hlt
    exact not_lt_of_ge (norm_nonneg _) hlt
  have hnz_g : ∀ z ∈ γ.trace, g z ≠ 0 := by
    intro z hz h0
    have hlt := hstrict z hz
    rw [h0, sub_zero] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨hfin_f, _, hind_f, hsum_f⟩ :=
    theorem10_43_argument_principle hΩ hcl hγ hext h01 hf hnz_f
  obtain ⟨hfin_g, _, hind_g, hsum_g⟩ :=
    theorem10_43_argument_principle hΩ hcl hγ hext h01 hg hnz_g
  refine ⟨fun z hz => ⟨hnz_f z hz, hnz_g z hz⟩, hfin_f, hfin_g, ?_⟩
  let γ_f := γ.compHolomorphic hΩ.1 hf hγ
  let γ_g := γ.compHolomorphic hΩ.1 hg hγ
  have hind_eq : Ind γ_g.toBookCurve 0 = Ind γ_f.toBookCurve 0 := by
    refine (theorem10_39 γ_f γ_g rfl rfl
      (γ.compHolomorphic_isClosed hcl hΩ.1 hf hγ)
      (γ.compHolomorphic_isClosed hcl hΩ.1 hg hγ) 0 ?_).2.2
    intro t ht
    change ‖g (γ.toFun t) - f (γ.toFun t)‖ < ‖0 - f (γ.toFun t)‖
    rw [norm_sub_rev, zero_sub, norm_neg]
    exact hstrict (γ.toFun t) (γ.mem_trace_of_mem_Icc ht)
  have hcast_eq : ((∑ a ∈ hfin_f.toFinset, zeroOrder f Ω a : ℕ) : ℂ) =
      ((∑ a ∈ hfin_g.toFinset, zeroOrder g Ω a : ℕ) : ℂ) :=
    hsum_f.symm.trans (hind_f.symm.trans (hind_eq.symm.trans (hind_g.trans hsum_g)))
  exact Nat.cast_injective hcast_eq

/-- 10.43 (Combined Argument Principle & Rouché's Theorem): packages both parts of Rudin 10.43. -/
theorem theorem10_43 {Ω : Set ℂ} (hΩ : IsRegion Ω)
    {γ : BookPath} (hcl : γ.IsClosed) (hγ : γ.trace ⊆ Ω)
    (hext : ∀ α, α ∉ Ω → Ind γ.toBookCurve α = 0)
    (h01 : ∀ α ∈ Ω, α ∉ γ.trace → Ind γ.toBookCurve α = 0 ∨ Ind γ.toBookCurve α = 1) :
    (∀ {f : ℂ → ℂ} (hf : HolomorphicOn f Ω), (∀ z ∈ γ.trace, f z ≠ 0) →
      ∃ hfin : (zeroSet f Ω ∩ indexOneSet γ Ω).Finite,
        0 ∉ (γ.compHolomorphic hΩ.1 hf hγ).trace ∧
        Ind (γ.compHolomorphic hΩ.1 hf hγ).toBookCurve 0 =
          (2 * Real.pi * Complex.I)⁻¹ * pathIntegral (fun z => deriv f z / f z) γ.toBookCurve ∧
        (2 * Real.pi * Complex.I)⁻¹ * pathIntegral (fun z => deriv f z / f z) γ.toBookCurve =
          ((∑ a ∈ hfin.toFinset, zeroOrder f Ω a : ℕ) : ℂ)) ∧
    (∀ {f g : ℂ → ℂ}, HolomorphicOn f Ω → HolomorphicOn g Ω →
      (∀ z ∈ γ.trace, ‖f z - g z‖ < ‖f z‖) →
      (∀ z ∈ γ.trace, f z ≠ 0 ∧ g z ≠ 0) ∧
      ∃ (hfin_f : (zeroSet f Ω ∩ indexOneSet γ Ω).Finite)
        (hfin_g : (zeroSet g Ω ∩ indexOneSet γ Ω).Finite),
        (∑ a ∈ hfin_f.toFinset, zeroOrder f Ω a) =
          ∑ a ∈ hfin_g.toFinset, zeroOrder g Ω a) :=
  ⟨fun hf hnz => theorem10_43_argument_principle hΩ hcl hγ hext h01 hf hnz,
   fun hf hg hst => theorem10_43_rouche hΩ hcl hγ hext h01 hf hg hst⟩

/-! ### 10.44: Symmetric Improper Sinc Transform -/

/-- Continuous sinc kernel `sinc(x) = sin x / x` (`x ≠ 0`), `sinc(0) = 1` (Rudin 10.44, p. 226). -/
noncomputable def realSinc (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sin x / x

theorem realSinc_even (x : ℝ) : realSinc (-x) = realSinc x := by
  unfold realSinc
  by_cases hx : x = 0
  · simp [hx]
  · have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
    simp only [hx, hnx, ↓reduceIte, Real.sin_neg]
    ring

theorem realSinc_ae_eq_sin_div :
    realSinc =ᵐ[MeasureTheory.volume] fun x : ℝ => Real.sin x / x := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0} : Set ℝ)) (fun x hx => ?_) (by simp)
  by_contra hne
  have hx0 : x ≠ 0 := hne
  simp [realSinc, hx0] at hx

/-- Entire divided-difference kernel `h(z) = dslope (w ↦ exp(i w)) 0 z`, whose imaginary part on `ℝ`
is identically `realSinc`. -/
private noncomputable def expIDslope : ℂ → ℂ :=
  dslope (fun w : ℂ => Complex.exp (Complex.I * w)) 0

private theorem holomorphicOn_expIDslope : HolomorphicOn expIDslope Set.univ := by
  have hd : Differentiable ℂ (fun w : ℂ => Complex.exp (Complex.I * w)) :=
    Complex.differentiable_exp.comp (differentiable_id.const_mul Complex.I)
  exact (holomorphicOn_iff_differentiableOn isOpen_univ).mpr
    ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hd.differentiableOn)

private theorem continuous_expIDslope : Continuous expIDslope :=
  continuous_iff_continuousAt.mpr fun z => (holomorphicOn_expIDslope z trivial).continuousAt

private theorem expIDslope_im_ofReal (x : ℝ) : (expIDslope (x : ℂ)).im = realSinc x := by
  unfold expIDslope realSinc
  by_cases hx : x = 0
  · subst hx
    simp only [↓reduceIte, Complex.ofReal_zero, dslope_same]
    have hd : HasDerivAt (fun w : ℂ => Complex.exp (Complex.I * w)) Complex.I 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul Complex.I).cexp
    rw [hd.deriv, Complex.I_im]
  · have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    simp only [hx, ↓reduceIte, dslope_of_ne _ hxc, slope_def_field, mul_zero, Complex.exp_zero, sub_zero]
    have hexp : Complex.exp (Complex.I * (x : ℂ)) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
      rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hdiv : (Complex.exp (Complex.I * (x : ℂ)) - 1) / (x : ℂ) =
        (((Real.cos x - 1) / x : ℝ) : ℂ) + ((Real.sin x / x : ℝ) : ℂ) * Complex.I := by
      rw [hexp]
      simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one]
      field_simp [hxc]
      ring
    rw [hdiv]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]

theorem continuous_realSinc : Continuous realSinc := by
  have hfun : realSinc = fun x : ℝ => (expIDslope (x : ℂ)).im :=
    funext fun x => (expIDslope_im_ofReal x).symm
  rw [hfun]
  exact Complex.continuous_im.comp (continuous_expIDslope.comp Complex.continuous_ofReal)

/-- Quantitative Dirichlet integral bound via contour integration of `expIDslope` around `[-R, R]`
and the upper semicircle of radius `R > 0`: `|(∫_0^R sinc u du) - π / 2| ≤ π / (2 R)`. -/
theorem dirichlet_integral_bound {R : ℝ} (hR : 0 < R) :
    |(∫ u in (0 : ℝ)..R, realSinc u) - Real.pi / 2| ≤ Real.pi / (2 * R) := by
  let γ₁ : BookPath :=
    BookPath.ofC1 (by linarith : -R < R) (fun x : ℝ => x • (1 : ℂ)) (fun _ => 1)
      (continuous_id.smul continuous_const).continuousOn continuousOn_const
      (fun x _ => by simpa using ((hasDerivAt_id x).smul_const (1 : ℂ)).hasDerivWithinAt)
  let γ₂ : BookPath := circleArcPath 0 R Real.pi_pos
  have hjoin : γ₁.toFun γ₁.β = γ₂.toFun γ₂.α := by
    simp [γ₁, γ₂, circleArcPath, BookPath.ofC1, circleMap, Complex.real_smul]
  have hcl : (γ₁.concat γ₂ hjoin).IsClosed := by
    unfold BookPath.IsClosed BookCurve.IsClosed
    rw [BookPath.concat_start, BookPath.concat_end]
    simp [γ₁, γ₂, circleArcPath, BookPath.ofC1, circleMap, Complex.exp_pi_mul_I, Complex.real_smul]
  have hzero : pathIntegral expIDslope (γ₁.concat γ₂ hjoin).toBookCurve = 0 :=
    (theorem10_14 isOpen_univ convex_univ 0 continuous_expIDslope.continuousOn
      (fun z _ => holomorphicOn_expIDslope z trivial)).2 (γ₁.concat γ₂ hjoin) hcl (subset_univ _)
  rw [γ₁.pathIntegral_concat γ₂ hjoin continuous_expIDslope.continuousOn] at hzero
  -- Evaluate `pathIntegral expIDslope γ₁` and its imaginary part
  have hint_γ₁ : pathIntegral expIDslope γ₁.toBookCurve = ∫ x in (-R)..R, expIDslope (x : ℂ) := by
    unfold pathIntegral
    change (∫ x in (-R)..R, expIDslope (x • (1 : ℂ)) * derivWithin (fun u : ℝ => u • (1 : ℂ)) (Icc (-R) R) x) =
      ∫ x in (-R)..R, expIDslope (x : ℂ)
    apply intervalIntegral.integral_congr_ae_restrict
    change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc (-R) R)] _
    rw [Set.uIoc_of_le (by linarith : -R ≤ R), ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    have hd : derivWithin (fun u : ℝ => u • (1 : ℂ)) (Icc (-R) R) x = 1 := by
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
      have h1 : HasDerivAt (fun u : ℝ => u • (1 : ℂ)) 1 x := by
        simpa using ((hasDerivAt_id x).smul_const (1 : ℂ))
      exact h1.deriv
    rw [hd, mul_one]
    simp [Complex.real_smul]
  have him_γ₁ : (pathIntegral expIDslope γ₁.toBookCurve).im =
      2 * ∫ u in (0 : ℝ)..R, realSinc u := by
    rw [hint_γ₁]
    have hint_c : IntervalIntegrable (fun x : ℝ => expIDslope (x : ℂ)) MeasureTheory.volume (-R) R :=
      (continuous_expIDslope.comp Complex.continuous_ofReal).intervalIntegrable _ _
    have him_comm : (∫ x in (-R)..R, expIDslope (x : ℂ)).im =
        ∫ x in (-R)..R, (expIDslope (x : ℂ)).im :=
      (Complex.imCLM.intervalIntegral_comp_comm hint_c).symm
    rw [him_comm]
    simp_rw [expIDslope_im_ofReal]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (continuous_realSinc.intervalIntegrable (-R) 0)
      (continuous_realSinc.intervalIntegrable 0 R)]
    have hneg : (∫ x in (-R)..(0 : ℝ), realSinc x) = ∫ u in (0 : ℝ)..R, realSinc u := by
      have h1 := intervalIntegral.integral_comp_neg (f := realSinc) (a := (0 : ℝ)) (b := R)
      simp only [neg_zero, realSinc_even] at h1
      exact h1.symm
    rw [hneg]
    ring
  -- Evaluate `pathIntegral expIDslope γ₂`
  let A : ℝ → ℂ := fun θ => Complex.I * Complex.exp (Complex.I * circleMap 0 R θ)
  have hA_cont : Continuous A :=
    continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul (continuous_circleMap 0 R)))
  have hint_γ₂ : pathIntegral expIDslope γ₂.toBookCurve =
      (∫ θ in (0 : ℝ)..Real.pi, A θ) - Real.pi * Complex.I := by
    have hcongr : pathIntegral expIDslope γ₂.toBookCurve =
        ∫ θ in (0 : ℝ)..Real.pi, (A θ - Complex.I) := by
      unfold pathIntegral
      dsimp [γ₂, circleArcPath, BookPath.ofC1]
      apply intervalIntegral.integral_congr_ae_restrict
      change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc 0 Real.pi)] _
      rw [Set.uIoc_of_le Real.pi_pos.le, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds hθ.1 hθ.2), deriv_circleMap]
      have hcm_ne : circleMap 0 R θ ≠ 0 := by
        simp [circleMap, hR.ne', Complex.exp_ne_zero]
      unfold expIDslope
      rw [dslope_of_ne _ hcm_ne, slope_def_field]
      simp only [mul_zero, Complex.exp_zero, sub_zero, A]
      field_simp [hcm_ne]
    rw [hcongr, intervalIntegral.integral_sub (hA_cont.intervalIntegrable 0 Real.pi)
      (continuous_const.intervalIntegrable 0 Real.pi), intervalIntegral.integral_const,
      sub_zero, Complex.real_smul]
  -- Bound `‖∫_0^π A θ dθ‖ ≤ π / R` via Jordan's inequality `2 / π * θ ≤ sin θ` on `[0, π / 2]`
  have hA_norm : ∀ θ : ℝ, ‖A θ‖ = Real.exp (-R * Real.sin θ) := by
    intro θ
    dsimp [A]
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp]
    congr 1
    simp [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, mul_add]
  have hhalf_bound : ‖∫ θ in (0 : ℝ)..(Real.pi / 2), A θ‖ ≤ Real.pi / (2 * R) := by
    have hpi2_nonneg : (0 : ℝ) ≤ Real.pi / 2 := by positivity
    let B : ℝ → ℝ := fun θ => Real.exp (-(2 * R / Real.pi) * θ)
    have hB_cont : Continuous B :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hle : ∀ θ ∈ Ioc (0 : ℝ) (Real.pi / 2), ‖A θ‖ ≤ B θ := by
      intro θ hθ
      rw [hA_norm]
      apply Real.exp_le_exp.mpr
      have hsin := Real.mul_le_sin hθ.1.le hθ.2
      have hmul := mul_le_mul_of_nonpos_left hsin (by linarith : -R ≤ 0)
      calc -R * Real.sin θ ≤ -R * (2 / Real.pi * θ) := hmul
        _ = -(2 * R / Real.pi) * θ := by ring
    have hnorm_le : ‖∫ θ in (0 : ℝ)..(Real.pi / 2), A θ‖ ≤ ∫ θ in (0 : ℝ)..(Real.pi / 2), B θ :=
      intervalIntegral.norm_integral_le_of_norm_le hpi2_nonneg
        (Filter.Eventually.of_forall fun θ => hle θ) (hB_cont.intervalIntegrable 0 (Real.pi / 2))
    have hftc : ∫ θ in (0 : ℝ)..(Real.pi / 2), B θ =
        (Real.pi / (2 * R)) * (1 - Real.exp (-R)) := by
      let F : ℝ → ℝ := fun θ => -(Real.pi / (2 * R)) * Real.exp (-(2 * R / Real.pi) * θ)
      have hFd : ∀ θ ∈ Set.uIcc (0 : ℝ) (Real.pi / 2), HasDerivAt F (B θ) θ := by
        intro θ _
        have h1 : HasDerivAt (fun u : ℝ => -(2 * R / Real.pi) * u) (-(2 * R / Real.pi)) θ := by
          simpa using (hasDerivAt_id θ).const_mul (-(2 * R / Real.pi))
        have h2 := h1.exp.const_mul (-(Real.pi / (2 * R)))
        have hc : -(Real.pi / (2 * R)) * (Real.exp (-(2 * R / Real.pi) * θ) * -(2 * R / Real.pi)) =
            B θ := by
          dsimp [B]
          field_simp [Real.pi_pos.ne', hR.ne']
        rwa [hc] at h2
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hFd (hB_cont.intervalIntegrable _ _)]
      dsimp [F]
      have harg : -(2 * R / Real.pi) * (Real.pi / 2) = -R := by
        field_simp [Real.pi_pos.ne']
      rw [harg, mul_zero, Real.exp_zero]
      ring
    have hexp_pos : 0 ≤ (Real.pi / (2 * R)) * Real.exp (-R) := by positivity
    linarith [hnorm_le, hftc]
  have hsecond_half_bound : ‖∫ θ in (Real.pi / 2)..Real.pi, A θ‖ ≤ Real.pi / (2 * R) := by
    have hchg := intervalIntegral.integral_comp_sub_left A Real.pi (a := 0) (b := Real.pi / 2)
    have hb : Real.pi - Real.pi / 2 = Real.pi / 2 := by ring
    have ha : Real.pi - 0 = Real.pi := by ring
    rw [hb, ha] at hchg
    rw [← hchg]
    have hpi2_nonneg : (0 : ℝ) ≤ Real.pi / 2 := by positivity
    let B : ℝ → ℝ := fun u => Real.exp (-(2 * R / Real.pi) * u)
    have hB_cont : Continuous B :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hle : ∀ u ∈ Ioc (0 : ℝ) (Real.pi / 2), ‖A (Real.pi - u)‖ ≤ B u := by
      intro u hu
      rw [hA_norm, Real.sin_pi_sub]
      apply Real.exp_le_exp.mpr
      have hsin := Real.mul_le_sin hu.1.le hu.2
      have hmul := mul_le_mul_of_nonpos_left hsin (by linarith : -R ≤ 0)
      calc -R * Real.sin u ≤ -R * (2 / Real.pi * u) := hmul
        _ = -(2 * R / Real.pi) * u := by ring
    have hnorm_le : ‖∫ u in (0 : ℝ)..(Real.pi / 2), A (Real.pi - u)‖ ≤ ∫ u in (0 : ℝ)..(Real.pi / 2), B u :=
      intervalIntegral.norm_integral_le_of_norm_le hpi2_nonneg
        (Filter.Eventually.of_forall fun u => hle u) (hB_cont.intervalIntegrable 0 (Real.pi / 2))
    have hftc : ∫ u in (0 : ℝ)..(Real.pi / 2), B u =
        (Real.pi / (2 * R)) * (1 - Real.exp (-R)) := by
      let F : ℝ → ℝ := fun u => -(Real.pi / (2 * R)) * Real.exp (-(2 * R / Real.pi) * u)
      have hFd : ∀ u ∈ Set.uIcc (0 : ℝ) (Real.pi / 2), HasDerivAt F (B u) u := by
        intro u _
        have h1 : HasDerivAt (fun v : ℝ => -(2 * R / Real.pi) * v) (-(2 * R / Real.pi)) u := by
          simpa using (hasDerivAt_id u).const_mul (-(2 * R / Real.pi))
        have h2 := h1.exp.const_mul (-(Real.pi / (2 * R)))
        have hc : -(Real.pi / (2 * R)) * (Real.exp (-(2 * R / Real.pi) * u) * -(2 * R / Real.pi)) =
            B u := by
          dsimp [B]
          field_simp [Real.pi_pos.ne', hR.ne']
        rwa [hc] at h2
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hFd (hB_cont.intervalIntegrable _ _)]
      dsimp [F]
      have harg : -(2 * R / Real.pi) * (Real.pi / 2) = -R := by
        field_simp [Real.pi_pos.ne']
      rw [harg, mul_zero, Real.exp_zero]
      ring
    have hexp_pos : 0 ≤ (Real.pi / (2 * R)) * Real.exp (-R) := by positivity
    linarith [hnorm_le, hftc]
  have hfull_bound : ‖∫ θ in (0 : ℝ)..Real.pi, A θ‖ ≤ Real.pi / R := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hA_cont.intervalIntegrable 0 (Real.pi / 2))
      (hA_cont.intervalIntegrable (Real.pi / 2) Real.pi)]
    calc ‖(∫ θ in (0 : ℝ)..(Real.pi / 2), A θ) + ∫ θ in (Real.pi / 2)..Real.pi, A θ‖
        ≤ ‖∫ θ in (0 : ℝ)..(Real.pi / 2), A θ‖ + ‖∫ θ in (Real.pi / 2)..Real.pi, A θ‖ :=
          norm_add_le _ _
      _ ≤ Real.pi / (2 * R) + Real.pi / (2 * R) := add_le_add hhalf_bound hsecond_half_bound
      _ = Real.pi / R := by ring
  -- Take imaginary part of `pathIntegral expIDslope γ₁ + pathIntegral expIDslope γ₂ = 0`
  have him_zero : (pathIntegral expIDslope γ₁.toBookCurve +
      pathIntegral expIDslope γ₂.toBookCurve).im = 0 := by
    rw [hzero, Complex.zero_im]
  rw [Complex.add_im, him_γ₁, hint_γ₂, Complex.sub_im] at him_zero
  have hpiI_im : ((Real.pi : ℂ) * Complex.I).im = Real.pi := by simp
  rw [hpiI_im] at him_zero
  have hdiff_eq : 2 * (∫ u in (0 : ℝ)..R, realSinc u) - Real.pi =
      -(∫ θ in (0 : ℝ)..Real.pi, A θ).im := by
    linarith
  have habs_two : |2 * (∫ u in (0 : ℝ)..R, realSinc u) - Real.pi| ≤ Real.pi / R := by
    rw [hdiff_eq, abs_neg]
    exact (Complex.abs_im_le_norm _).trans hfull_bound
  have hhalf : |(∫ u in (0 : ℝ)..R, realSinc u) - Real.pi / 2| =
      |2 * (∫ u in (0 : ℝ)..R, realSinc u) - Real.pi| / 2 := by
    have : (∫ u in (0 : ℝ)..R, realSinc u) - Real.pi / 2 =
        (2 * (∫ u in (0 : ℝ)..R, realSinc u) - Real.pi) / 2 := by ring
    rw [this, abs_div, abs_of_pos (a := (2 : ℝ)) two_pos]
  rw [hhalf]
  calc |2 * (∫ u in (0 : ℝ)..R, realSinc u) - Real.pi| / 2
      ≤ (Real.pi / R) / 2 := div_le_div_of_nonneg_right habs_two two_pos.le
    _ = Real.pi / (2 * R) := by ring

/-- Dirichlet's improper integral: `∫_0^R (sin u / u) du → π / 2` as `R → ∞`. -/
theorem tendsto_dirichlet_integral :
    Tendsto (fun R : ℝ => ∫ u in (0 : ℝ)..R, realSinc u) atTop (nhds (Real.pi / 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim0 : Tendsto (fun R : ℝ => Real.pi / (2 * R)) atTop (nhds 0) := by
    have h2R : Tendsto (fun R : ℝ => 2 * R) atTop atTop :=
      Filter.Tendsto.const_mul_atTop two_pos Filter.tendsto_id
    exact tendsto_const_nhds.div_atTop h2R
  refine squeeze_zero_norm' ?_ hlim0
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
  simpa [Real.norm_eq_abs] using dirichlet_integral_bound hR

/-- Limit of `∫_0^A ω * sinc(ω * x) dx` as `A → ∞` for arbitrary `ω : ℝ`. -/
private theorem tendsto_integral_scaledSinc (ω : ℝ) :
    Tendsto (fun A : ℝ => ∫ x in (0 : ℝ)..A, ω * realSinc (ω * x)) atTop
      (nhds (if 0 < ω then Real.pi / 2 else if ω = 0 then 0 else -(Real.pi / 2))) := by
  have hfun : (fun A : ℝ => ∫ x in (0 : ℝ)..A, ω * realSinc (ω * x)) =
      fun A : ℝ => ∫ u in (0 : ℝ)..(ω * A), realSinc u := by
    funext A
    have hsmul := intervalIntegral.smul_integral_comp_mul_left
      (f := realSinc) (a := (0 : ℝ)) (b := A) ω
    rw [mul_zero] at hsmul
    simpa [smul_eq_mul, intervalIntegral.integral_const_mul] using hsmul
  rw [hfun]
  split_ifs with hpos hzero
  · exact tendsto_dirichlet_integral.comp (Filter.Tendsto.const_mul_atTop hpos Filter.tendsto_id)
  · subst hzero
    simp
  · have hneg : ω < 0 := lt_of_le_of_ne (not_lt.mp hpos) hzero
    have hpos' : 0 < -ω := neg_pos.mpr hneg
    have hflip : (fun A : ℝ => ∫ u in (0 : ℝ)..(ω * A), realSinc u) =
        fun A : ℝ => -(∫ u in (0 : ℝ)..((-ω) * A), realSinc u) := by
      funext A
      have h1 := intervalIntegral.integral_comp_neg (f := realSinc) (a := (0 : ℝ)) (b := (-ω) * A)
      simp only [neg_zero, realSinc_even] at h1
      have hlim_b : -((-ω) * A) = ω * A := by ring
      rw [hlim_b] at h1
      have hsymm := intervalIntegral.integral_symm (μ := MeasureTheory.volume) (f := realSinc) (0 : ℝ) (ω * A)
      linarith [h1, hsymm]
    rw [hflip]
    exact (tendsto_dirichlet_integral.comp
      (Filter.Tendsto.const_mul_atTop hpos' Filter.tendsto_id)).neg

/-- Target value of Rudin's worked problem 10.44: `π` for `|t| < 1`, `π / 2` for `|t| = 1`, and `0`
for `|t| > 1`. -/
noncomputable def sincFourierValue (t : ℝ) : ℂ :=
  if |t| < 1 then (Real.pi : ℂ)
  else if |t| = 1 then ((Real.pi / 2 : ℝ) : ℂ)
  else 0

/-- 10.44 (Symmetric Fourier transform of `sin x / x`, Rudin pp. 226–227): for every `t ∈ ℝ`,
`lim_{A → ∞} ∫_{-A}^A (sin x / x) e^{i t x} dx` equals `π` if `|t| < 1`, `π / 2` if `t = ±1`, and
`0` if `|t| > 1` (proved for both `realSinc x` and `Real.sin x / x`). -/
theorem theorem10_44 (t : ℝ) :
    Tendsto (fun A : ℝ => ∫ x in (-A)..A, (realSinc x : ℂ) * Complex.exp (Complex.I * t * x))
      atTop (nhds (sincFourierValue t)) ∧
    Tendsto (fun A : ℝ => ∫ x in (-A)..A, ((Real.sin x / x : ℝ) : ℂ) * Complex.exp (Complex.I * t * x))
      atTop (nhds (sincFourierValue t)) ∧
    (|t| < 1 → sincFourierValue t = (Real.pi : ℂ)) ∧
    (t = 1 → sincFourierValue t = ((Real.pi / 2 : ℝ) : ℂ)) ∧
    (t = -1 → sincFourierValue t = ((Real.pi / 2 : ℝ) : ℂ)) ∧
    (1 < |t| → sincFourierValue t = 0) := by
  have hval_lt : |t| < 1 → sincFourierValue t = (Real.pi : ℂ) := fun h => by
    simp [sincFourierValue, h]
  have hval_pos1 : t = 1 → sincFourierValue t = ((Real.pi / 2 : ℝ) : ℂ) := fun h => by
    subst h; norm_num [sincFourierValue]
  have hval_neg1 : t = -1 → sincFourierValue t = ((Real.pi / 2 : ℝ) : ℂ) := fun h => by
    subst h; norm_num [sincFourierValue]
  have hval_gt : 1 < |t| → sincFourierValue t = 0 := fun h => by
    have hnlt : ¬ |t| < 1 := not_lt.mpr h.le
    have hneq : ¬ |t| = 1 := h.ne'
    simp [sincFourierValue, hnlt, hneq]
  -- Reduce the symmetric integral for `A > 0` to `∫_0^A (1+t) sinc((1+t)x) + ∫_0^A (1-t) sinc((1-t)x)`
  let g : ℝ → ℂ := fun x => (realSinc x : ℂ) * Complex.exp (Complex.I * t * x)
  have hg_cont : Continuous g :=
    (Complex.continuous_ofReal.comp continuous_realSinc).mul
      (Complex.continuous_exp.comp
        ((continuous_const.mul continuous_const).mul Complex.continuous_ofReal))
  have hsymm_eq : ∀ A : ℝ, 0 < A →
      (∫ x in (-A)..A, g x) =
        (((∫ x in (0 : ℝ)..A, (1 + t) * realSinc ((1 + t) * x)) +
          (∫ x in (0 : ℝ)..A, (1 - t) * realSinc ((1 - t) * x)) : ℝ) : ℂ) := by
    intro A hA
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hg_cont.intervalIntegrable (-A) 0) (hg_cont.intervalIntegrable 0 A)]
    have hneg : (∫ x in (-A)..(0 : ℝ), g x) = ∫ x in (0 : ℝ)..A, g (-x) := by
      have h1 := intervalIntegral.integral_comp_neg (f := g) (a := (0 : ℝ)) (b := A)
      simp only [neg_zero] at h1
      exact h1.symm
    have hg_neg_int : IntervalIntegrable (fun x : ℝ => g (-x)) MeasureTheory.volume 0 A :=
      (hg_cont.comp continuous_neg).intervalIntegrable 0 A
    rw [hneg, ← intervalIntegral.integral_add hg_neg_int (hg_cont.intervalIntegrable 0 A)]
    have h1_cont : Continuous (fun x : ℝ => (1 + t) * realSinc ((1 + t) * x)) :=
      continuous_const.mul (continuous_realSinc.comp (continuous_const.mul continuous_id))
    have h2_cont : Continuous (fun x : ℝ => (1 - t) * realSinc ((1 - t) * x)) :=
      continuous_const.mul (continuous_realSinc.comp (continuous_const.mul continuous_id))
    have h12_cont : Continuous (fun x : ℝ =>
        (1 + t) * realSinc ((1 + t) * x) + (1 - t) * realSinc ((1 - t) * x)) :=
      Continuous.add h1_cont h2_cont
    have hcast : (((∫ x in (0 : ℝ)..A,
          (1 + t) * realSinc ((1 + t) * x) + (1 - t) * realSinc ((1 - t) * x)) : ℝ) : ℂ) =
        ∫ x in (0 : ℝ)..A,
          (((1 + t) * realSinc ((1 + t) * x) + (1 - t) * realSinc ((1 - t) * x) : ℝ) : ℂ) :=
      (Complex.ofRealCLM.intervalIntegral_comp_comm (h12_cont.intervalIntegrable 0 A)).symm
    rw [← intervalIntegral.integral_add (h1_cont.intervalIntegrable 0 A)
      (h2_cont.intervalIntegrable 0 A), hcast]
    apply intervalIntegral.integral_congr_ae_restrict
    change _ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc 0 A)] _
    rw [Set.uIoc_of_le hA.le, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    have hx_ne : x ≠ 0 := hx.1.ne'
    dsimp [g]
    rw [Complex.ofReal_neg, realSinc_even]
    have hexp_pos : Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) =
        (Real.cos (t * x) : ℂ) + (Real.sin (t * x) : ℂ) * Complex.I := by
      have : Complex.I * (t : ℂ) * (x : ℂ) = (((t * x : ℝ)) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hexp_neg : Complex.exp (Complex.I * (t : ℂ) * -(x : ℂ)) =
        (Real.cos (t * x) : ℂ) - (Real.sin (t * x) : ℂ) * Complex.I := by
      have : Complex.I * (t : ℂ) * -(x : ℂ) = (((-(t * x) : ℝ)) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
      ring
    rw [hexp_pos, hexp_neg]
    have hreal_id : 2 * realSinc x * Real.cos (t * x) =
        (1 + t) * realSinc ((1 + t) * x) + (1 - t) * realSinc ((1 - t) * x) := by
      have hterm : ∀ ω : ℝ, ω * realSinc (ω * x) = Real.sin (ω * x) / x := by
        intro ω
        by_cases hω : ω = 0
        · simp [hω]
        · have hωx : ω * x ≠ 0 := mul_ne_zero hω hx_ne
          simp only [realSinc, hωx, ↓reduceIte]
          field_simp [hω, hx_ne]
      rw [hterm (1 + t), hterm (1 - t)]
      simp only [realSinc, hx_ne, ↓reduceIte]
      have htrig : 2 * Real.sin x * Real.cos (t * x) =
          Real.sin ((1 + t) * x) + Real.sin ((1 - t) * x) := by
        have h1 : (1 + t) * x = x + t * x := by ring
        have h2 : (1 - t) * x = x - t * x := by ring
        rw [h1, h2, Real.sin_add, Real.sin_sub]
        ring
      calc 2 * (Real.sin x / x) * Real.cos (t * x)
          = (2 * Real.sin x * Real.cos (t * x)) / x := by ring
        _ = (Real.sin ((1 + t) * x) + Real.sin ((1 - t) * x)) / x := by rw [htrig]
        _ = Real.sin ((1 + t) * x) / x + Real.sin ((1 - t) * x) / x := add_div _ _ _
    change (realSinc x : ℂ) * ((Real.cos (t * x) : ℂ) - (Real.sin (t * x) : ℂ) * Complex.I) +
        (realSinc x : ℂ) * ((Real.cos (t * x) : ℂ) + (Real.sin (t * x) : ℂ) * Complex.I) =
      (((1 + t) * realSinc ((1 + t) * x) + (1 - t) * realSinc ((1 - t) * x) : ℝ) : ℂ)
    have lhs_eq : (realSinc x : ℂ) * ((Real.cos (t * x) : ℂ) - (Real.sin (t * x) : ℂ) * Complex.I) +
        (realSinc x : ℂ) * ((Real.cos (t * x) : ℂ) + (Real.sin (t * x) : ℂ) * Complex.I) =
        ((2 * realSinc x * Real.cos (t * x) : ℝ) : ℂ) := by
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
      ring
    rw [lhs_eq, hreal_id]
  -- Evaluate the limit of the sum and match `sincFourierValue t`
  let L₁ : ℝ := if 0 < 1 + t then Real.pi / 2 else if 1 + t = 0 then 0 else -(Real.pi / 2)
  let L₂ : ℝ := if 0 < 1 - t then Real.pi / 2 else if 1 - t = 0 then 0 else -(Real.pi / 2)
  have hsum_lim : Tendsto (fun A : ℝ =>
      (((∫ x in (0 : ℝ)..A, (1 + t) * realSinc ((1 + t) * x)) +
        (∫ x in (0 : ℝ)..A, (1 - t) * realSinc ((1 - t) * x)) : ℝ) : ℂ))
      atTop (nhds (((L₁ + L₂ : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_integral_scaledSinc (1 + t)).add (tendsto_integral_scaledSinc (1 - t)))
  have hL_eq : ((L₁ + L₂ : ℝ) : ℂ) = sincFourierValue t := by
    dsimp [L₁, L₂]
    rcases lt_trichotomy |t| 1 with hlt | heq | hgt
    · rw [hval_lt hlt]
      have ht_bounds := abs_lt.mp hlt
      have hp1 : 0 < 1 + t := by linarith
      have hp2 : 0 < 1 - t := by linarith
      simp only [hp1, hp2, ↓reduceIte]
      push_cast; ring
    · rcases eq_or_eq_neg_of_abs_eq heq with rfl | rfl
      · rw [hval_pos1 rfl]
        norm_num
      · rw [hval_neg1 rfl]
        norm_num
    · rw [hval_gt hgt]
      rcases lt_or_gt_of_ne (by intro h0; rw [h0, abs_zero] at hgt; linarith : t ≠ 0) with ht_neg | ht_pos
      · have ht_lt : t < -1 := by
          rw [abs_of_neg ht_neg] at hgt; linarith
        have hn1 : ¬ 0 < 1 + t := by linarith
        have hnz1 : ¬ 1 + t = 0 := by linarith
        have hp2 : 0 < 1 - t := by linarith
        simp only [hn1, hnz1, hp2, ↓reduceIte]
        push_cast; ring
      · have ht_gt : 1 < t := by
          rw [abs_of_pos ht_pos] at hgt; exact hgt
        have hp1 : 0 < 1 + t := by linarith
        have hn2 : ¬ 0 < 1 - t := by linarith
        have hnz2 : ¬ 1 - t = 0 := by linarith
        simp only [hp1, hn2, hnz2, ↓reduceIte]
        push_cast; ring
  rw [hL_eq] at hsum_lim
  have htend_sinc : Tendsto (fun A : ℝ => ∫ x in (-A)..A, g x) atTop (nhds (sincFourierValue t)) := by
    refine hsum_lim.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with A hA
    exact (hsymm_eq A hA).symm
  have htend_raw : Tendsto
      (fun A : ℝ => ∫ x in (-A)..A, ((Real.sin x / x : ℝ) : ℂ) * Complex.exp (Complex.I * t * x))
      atTop (nhds (sincFourierValue t)) := by
    refine htend_sinc.congr' (Filter.Eventually.of_forall fun A => ?_)
    apply intervalIntegral.integral_congr_ae
    filter_upwards [realSinc_ae_eq_sin_div] with x hx _
    dsimp [g]
    rw [hx]
  exact ⟨htend_sinc, htend_raw, hval_lt, hval_pos1, hval_neg1, hval_gt⟩

end BatchD2

end RudinRCA.Chapter10
