import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Convex.Topology

noncomputable section
open scoped OnePoint
open Set Filter Metric
open scoped Topology

namespace RudinRCA.Chapter13

/-- The Riemann sphere of §13.1, with the one-point compactification topology. -/
abbrev RiemannSphere := OnePoint ℂ

/-- A punctured disc about infinity, viewed in the finite chart. -/
def exteriorDisc (r : ℝ) : Set ℂ := {z | r < ‖z‖}

/-- Rudin's `D(∞; r)`, the complement of the finite closed disc of radius `r`. -/
def infinityDisc (r : ℝ) : Set RiemannSphere :=
  ((↑) '' closedBall (0 : ℂ) r)ᶜ

@[simp] theorem infinity_mem_infinityDisc (r : ℝ) :
    (∞ : RiemannSphere) ∈ infinityDisc r := by
  simp [infinityDisc]

@[simp] theorem coe_mem_infinityDisc (z : ℂ) (r : ℝ) :
    (z : RiemannSphere) ∈ infinityDisc r ↔ r < ‖z‖ := by
  simp [infinityDisc, mem_closedBall, dist_zero_right]

theorem infinityDisc_eq (r : ℝ) :
    infinityDisc r = (↑) '' exteriorDisc r ∪ {∞} := by
  ext x
  induction x using OnePoint.rec with
  | infty => simp [infinityDisc]
  | coe z => simp [exteriorDisc]

theorem isOpen_infinityDisc (r : ℝ) : IsOpen (infinityDisc r) :=
  OnePoint.isOpen_compl_image_coe.mpr ⟨isClosed_closedBall, isCompact_closedBall 0 r⟩

/-- The book's positive-radius exterior discs are precisely a neighborhood basis at infinity. -/
theorem mem_nhds_infinity_iff {s : Set RiemannSphere} :
    s ∈ 𝓝 (∞ : RiemannSphere) ↔ ∃ r > 0, infinityDisc r ⊆ s := by
  constructor
  · intro hs
    obtain ⟨K, ⟨_, hK⟩, hKs⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hs
    obtain ⟨r, hr, hKr⟩ := hK.isBounded.exists_pos_norm_le
    refine ⟨r, hr, subset_trans ?_ hKs⟩
    rw [infinityDisc_eq]
    refine union_subset_union ?_ Subset.rfl
    apply image_mono
    intro z hz hzK
    exact (not_lt_of_ge (hKr z hzK)) hz
  · rintro ⟨r, _, hrs⟩
    exact Filter.mem_of_superset
      ((isOpen_infinityDisc r).mem_nhds (infinity_mem_infinityDisc r)) hrs

/-- The ordinary topology is unchanged on the finite chart. -/
theorem finite_chart_open_embedding :
    Topology.IsOpenEmbedding ((↑) : ℂ → RiemannSphere) :=
  OnePoint.isOpenEmbedding_coe

/-- The topological sphere assertion in §13.1. -/
def riemannSphereHomeomorph :
    RiemannSphere ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (by simp)

theorem riemannSphere_compact : CompactSpace RiemannSphere := inferInstance

/-- An unbounded finite-chart set accumulates at the point at infinity. -/
theorem infinity_mem_closure_of_unbounded {s : Set ℂ}
    (hs : ∀ r > 0, ∃ z ∈ s, r < ‖z‖) :
    (∞ : RiemannSphere) ∈ closure ((↑) '' s) := by
  apply _root_.mem_closure_iff.mpr
  intro t ht hinf
  obtain ⟨r, hr, hrt⟩ := mem_nhds_infinity_iff.mp (ht.mem_nhds hinf)
  obtain ⟨z, hzs, hzr⟩ := hs r hr
  exact ⟨(z : RiemannSphere), hrt ((coe_mem_infinityDisc z r).mpr hzr),
    mem_image_of_mem _ hzs⟩

theorem isConnected_insert_infinity {s : Set ℂ} (hs : IsConnected s)
    (hu : ∀ r > 0, ∃ z ∈ s, r < ‖z‖) :
    IsConnected (insert (∞ : RiemannSphere) ((↑) '' s)) := by
  refine (hs.image _ OnePoint.continuous_coe.continuousOn).subset_closure
    (subset_insert _ _) ?_
  exact insert_subset (infinity_mem_closure_of_unbounded hu) subset_closure

/-- The horizontal strip used in §13.1. -/
def horizontalStrip : Set ℂ := {z | 0 < z.im ∧ z.im < 1}

theorem horizontalStrip_isOpen : IsOpen horizontalStrip :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)

/-- The planar complement in Rudin's example is disconnected. -/
theorem horizontalStrip_planar_complement_not_preconnected :
    ¬ IsPreconnected horizontalStripᶜ := by
  intro h
  have hcover : horizontalStripᶜ ⊆
      {z : ℂ | z.im < 1 / 2} ∪ {z : ℂ | 1 / 2 < z.im} := by
    intro z hz
    simp only [horizontalStrip, mem_compl_iff, mem_setOf_eq, not_and_or, not_lt] at hz
    rcases hz with hz | hz
    · exact Or.inl (by dsimp; linarith)
    · exact Or.inr (by dsimp; linarith)
  obtain ⟨z, _, hz₁, hz₂⟩ := h _ _
    (isOpen_lt Complex.continuous_im continuous_const)
    (isOpen_lt continuous_const Complex.continuous_im) hcover
    ⟨0, by simp [horizontalStrip], by norm_num⟩
    ⟨Complex.I, by simp [horizontalStrip], by norm_num⟩
  dsimp at hz₁ hz₂
  linarith

/-- The spherical complement of exactly the same strip is connected. -/
theorem horizontalStrip_spherical_complement_connected :
    IsConnected (((↑) : ℂ → RiemannSphere) '' horizontalStrip)ᶜ := by
  let L : Set ℂ := {z | z.im ≤ 0}
  let H : Set ℂ := {z | 1 ≤ z.im}
  have hL : IsConnected L :=
    (convex_halfSpace_le (.mk Complex.add_im Complex.smul_im) 0).isConnected ⟨0, by simp [L]⟩
  have hH : IsConnected H :=
    (convex_halfSpace_ge (.mk Complex.add_im Complex.smul_im) 1).isConnected ⟨Complex.I, by simp [H]⟩
  have huL : ∀ r > 0, ∃ z ∈ L, r < ‖z‖ := by
    intro r hr
    refine ⟨(r + 1 : ℝ), by simp [L], ?_⟩
    exact (lt_add_one r).trans_le (Complex.re_le_norm ((r + 1 : ℝ) : ℂ))
  have huH : ∀ r > 0, ∃ z ∈ H, r < ‖z‖ := by
    intro r hr
    refine ⟨(r + 1 : ℝ) + Complex.I, by simp [H], ?_⟩
    have hx := Complex.re_le_norm ((r + 1 : ℝ) + Complex.I)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero] at hx
    linarith
  have heq : (((↑) : ℂ → RiemannSphere) '' horizontalStrip)ᶜ =
      insert ∞ ((↑) '' L) ∪ insert ∞ ((↑) '' H) := by
    ext x
    induction x using OnePoint.rec with
    | infty => simp
    | coe z =>
      simp only [mem_compl_iff, OnePoint.coe_injective.mem_set_image, horizontalStrip, mem_setOf_eq,
        mem_union, mem_insert_iff, OnePoint.coe_ne_infty, false_or, L, H]
      constructor
      · intro h
        by_cases hp : 0 < z.im
        · exact Or.inr (le_of_not_gt (fun hq => h ⟨hp, hq⟩))
        · exact Or.inl (le_of_not_gt hp)
      · rintro (h | h) ⟨hp, hq⟩ <;> linarith
  rw [heq]
  exact (isConnected_insert_infinity hL huL).union
    ⟨∞, mem_insert _ _, mem_insert _ _⟩ (isConnected_insert_infinity hH huH)

#print axioms infinity_mem_infinityDisc
#print axioms coe_mem_infinityDisc
#print axioms infinityDisc_eq
#print axioms isOpen_infinityDisc
#print axioms finite_chart_open_embedding
#print axioms riemannSphereHomeomorph
#print axioms riemannSphere_compact
#print axioms mem_nhds_infinity_iff
#print axioms infinity_mem_closure_of_unbounded
#print axioms isConnected_insert_infinity
#print axioms horizontalStrip_isOpen
#print axioms horizontalStrip_planar_complement_not_preconnected
#print axioms horizontalStrip_spherical_complement_connected

end RudinRCA.Chapter13
