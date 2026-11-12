import RudinRCA.Chapter13
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Connected.LocallyConnected

noncomputable section
open Set Filter Metric
open scoped Topology OnePoint
namespace RudinRCA.Chapter13

/-- The spherical complementary components, represented as sets rather than a choice of labels. -/
def sphericalComplementComponents (K : Set ℂ) : Set (Set RiemannSphere) :=
  {C | ∃ x ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
    C = connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K)ᶜ x}

/-- The countability observation in13.6. Closedness is enough for this assertion. -/
theorem countable_spherical_complement_components {K : Set ℂ} (hK : IsClosed K) :
    (sphericalComplementComponents K).Countable := by
  let T : Set RiemannSphere := (((↑) : ℂ → RiemannSphere) '' K)ᶜ
  let B : Set (Set RiemannSphere) :=
    {C | C ∈ sphericalComplementComponents K ∧ (((↑) : ℂ → RiemannSphere) ⁻¹' C).Nonempty}
  have hdis : B.PairwiseDisjoint (fun C => ((↑) : ℂ → RiemannSphere) ⁻¹' C) := by
    intro C hC D hD hne
    apply Set.disjoint_left.mpr
    intro z hzC hzD
    apply hne
    obtain ⟨x, _, rfl⟩ := hC.1
    obtain ⟨y, _, rfl⟩ := hD.1
    exact (connectedComponentIn_eq hzC).trans (connectedComponentIn_eq hzD).symm
  have hopen : ∀ C ∈ B, IsOpen (((↑) : ℂ → RiemannSphere) ⁻¹' C) := by
    intro C hC
    obtain ⟨x, _, rfl⟩ := hC.1
    rw [OnePoint.continuous_coe.continuousOn.preimage_connectedComponentIn]
    apply isOpen_biUnion
    intro a _
    have heq : ((↑) : ℂ → RiemannSphere) ⁻¹' T = Kᶜ := by
      ext z
      simp [T]
    change IsOpen (connectedComponentIn (((↑) : ℂ → RiemannSphere) ⁻¹' T) a)
    rw [heq]
    exact hK.isOpen_compl.connectedComponentIn
  have hB : B.Countable := hdis.countable_of_isOpen hopen (fun _ h => h.2)
  apply (hB.insert {∞}).mono
  intro C hC
  by_cases hfinite : (((↑) : ℂ → RiemannSphere) ⁻¹' C).Nonempty
  · exact mem_insert_of_mem _ ⟨hC, hfinite⟩
  · left
    apply Set.eq_singleton_iff_nonempty_unique_mem.mpr
    constructor
    · obtain ⟨x, hx, rfl⟩ := hC
      exact ⟨x, mem_connectedComponentIn hx⟩
    · intro x hx
      induction x using OnePoint.rec with
      | infty => rfl
      | coe z => exact False.elim (hfinite ⟨z, hx⟩)

/-- A disconnected spherical complement has a bounded component in the finite chart. -/
theorem exists_bounded_complement_component {K : Set ℂ}
    (hdisc : ¬ IsConnected (((↑) : ℂ → RiemannSphere) '' K)ᶜ) :
    ∃ a ∉ K, Bornology.IsBounded (connectedComponentIn Kᶜ a) := by
  by_contra! hall
  apply hdisc
  let T : Set RiemannSphere := (((↑) : ℂ → RiemannSphere) '' K)ᶜ
  have hinf : (∞ : RiemannSphere) ∈ T := by simp [T]
  have hsub : T ⊆ connectedComponentIn T ∞ := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact mem_connectedComponentIn hinf
    | coe a =>
      have ha : a ∉ K := by simpa [T] using hx
      have hu : ∀ r > 0, ∃ z ∈ connectedComponentIn Kᶜ a, r < ‖z‖ := by
        intro r _
        by_contra! hr
        exact hall a ha (isBounded_iff_forall_norm_le.mpr ⟨r, hr⟩)
      have hc := isConnected_insert_infinity
        (isConnected_connectedComponentIn_iff.mpr ha) hu
      have hCT : insert (∞ : RiemannSphere)
          (((↑) : ℂ → RiemannSphere) '' connectedComponentIn Kᶜ a) ⊆ T := by
        intro y hy
        rcases hy with rfl | ⟨z, hz, rfl⟩
        · exact hinf
        · simpa [T] using connectedComponentIn_subset Kᶜ a hz
      have hC := hc.isPreconnected.subset_connectedComponentIn (mem_insert _ _) hCT
      exact hC (mem_insert_of_mem _ (mem_image_of_mem _ (mem_connectedComponentIn ha)))
  have heq : connectedComponentIn T ∞ = T := (connectedComponentIn_subset _ _).antisymm hsub
  change IsConnected T
  rw [← heq]
  exact isConnected_connectedComponentIn_iff.mpr hinf

/-- The boundary of a component of the complement of a closed planar set lies in that set. -/
theorem frontier_complement_component_subset {K : Set ℂ} (hK : IsClosed K) (a : ℂ) :
    frontier (connectedComponentIn Kᶜ a) ⊆ K := by
  intro z hz
  by_contra hzK
  have hzopen : IsOpen (connectedComponentIn Kᶜ z) := hK.isOpen_compl.connectedComponentIn
  have hzC : z ∈ connectedComponentIn Kᶜ z := mem_connectedComponentIn hzK
  obtain ⟨w, hwz, hwa⟩ := _root_.mem_closure_iff.mp hz.1 _ hzopen hzC
  have heq : connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ z :=
    (connectedComponentIn_eq hwa).trans (connectedComponentIn_eq hwz).symm
  have haopen : IsOpen (connectedComponentIn Kᶜ a) := hK.isOpen_compl.connectedComponentIn
  apply hz.2
  rw [haopen.interior_eq, heq]
  exact hzC

/-- Maximum-modulus obstruction underlying13.8, for any holomorphic candidate on the
closure of the omitted complementary component. In particular this applies to every polynomial. -/
theorem reciprocal_approximation_obstruction {K V : Set ℂ} {a : ℂ} {m : ℝ}
    (hV : Bornology.IsBounded V) (haV : a ∈ V) (haK : a ∉ K)
    (hfront : frontier V ⊆ K) (hm : 0 < m)
    (hbound : ∀ z ∈ K, ‖z - a‖ ≤ m) {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g V) :
    ¬ ∀ z ∈ K, ‖g z - (z - a)⁻¹‖ < m⁻¹ := by
  intro happrox
  let F : ℂ → ℂ := fun z => (z - a) * g z - 1
  have hF : DiffContOnCl ℂ F V :=
    ((differentiable_id.sub_const a).diffContOnCl.smul hg).sub_const 1
  obtain ⟨w, hw, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm hV ⟨a, haV⟩ hF
  have hwK := hfront hw
  have hwa : w - a ≠ 0 := sub_ne_zero.mpr (fun h => haK (h ▸ hwK))
  have heq : F w = (w - a) * (g w - (w - a)⁻¹) := by
    dsimp [F]
    rw [mul_sub, mul_inv_cancel₀ hwa]
  have hsmall : ‖F w‖ < 1 := by
    rw [heq, norm_mul]
    calc
      ‖w - a‖ * ‖g w - (w - a)⁻¹‖ < ‖w - a‖ * m⁻¹ :=
        mul_lt_mul_of_pos_left (happrox w hwK) (norm_pos_iff.mpr hwa)
      _ ≤ m * m⁻¹ := mul_le_mul_of_nonneg_right (hbound w hwK) (inv_nonneg.mpr hm.le)
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hm)
  have hamax : ‖F a‖ ≤ ‖F w‖ := hmax (subset_closure haV)
  have hFa : ‖F a‖ = 1 := by simp [F]
  linarith

/-- Quantitative polynomial obstruction with any positive upper bound on distances to `a`. -/
theorem polynomial_approximation_obstruction {K : Set ℂ} (hK : IsClosed K)
    {a : ℂ} (ha : a ∉ K) (hb : Bornology.IsBounded (connectedComponentIn Kᶜ a))
    {m : ℝ} (hm : 0 < m) (hbound : ∀ z ∈ K, ‖z - a‖ ≤ m) (p : Polynomial ℂ) :
    ¬ ∀ z ∈ K, ‖p.eval z - (z - a)⁻¹‖ < m⁻¹ :=
  reciprocal_approximation_obstruction hb (mem_connectedComponentIn ha) ha
    (frontier_complement_component_subset hK a) hm hbound p.differentiable.diffContOnCl

/-- Printed13.8: a disconnected spherical complement yields a reciprocal function and
its exact positive maximum distance on `K`, with the stated obstruction for every polynomial. -/
theorem disconnected_spherical_complement_polynomial_obstruction {K : Set ℂ}
    (hK : IsCompact K)
    (hdisc : ¬ IsConnected (((↑) : ℂ → RiemannSphere) '' K)ᶜ) :
    ∃ a ∉ K, ∃ m > 0,
      (∃ z ∈ K, ‖z - a‖ = m) ∧ (∀ z ∈ K, ‖z - a‖ ≤ m) ∧
      ∀ p : Polynomial ℂ, ¬ ∀ z ∈ K, ‖p.eval z - (z - a)⁻¹‖ < m⁻¹ := by
  obtain ⟨a, ha, hb⟩ := exists_bounded_complement_component hdisc
  have hfront := frontier_complement_component_subset hK.isClosed a
  obtain ⟨w, hw, _⟩ := Complex.exists_mem_frontier_isMaxOn_norm hb
    ⟨a, mem_connectedComponentIn ha⟩ (differentiable_const (1 : ℂ)).diffContOnCl
  have hne : K.Nonempty := ⟨w, hfront hw⟩
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne
    (show ContinuousOn (fun w : ℂ => ‖w - a‖) K from
      (continuous_id.sub continuous_const).norm.continuousOn)
  have hza : z - a ≠ 0 := sub_ne_zero.mpr (fun h => ha (h ▸ hz))
  refine ⟨a, ha, ‖z - a‖, norm_pos_iff.mpr hza, ⟨z, hz, rfl⟩, ?_, ?_⟩
  · exact fun y hy => hmax hy
  · exact fun p => polynomial_approximation_obstruction hK.isClosed ha hb
      (norm_pos_iff.mpr hza) (fun y hy => hmax hy) p

/-- The counterexample in13.8 is holomorphic on an open neighborhood of `K` and is
not a uniform limit of polynomial functions on `K`. -/
theorem exists_holomorphic_not_polynomial_uniform_limit {K : Set ℂ}
    (hK : IsCompact K)
    (hdisc : ¬ IsConnected (((↑) : ℂ → RiemannSphere) '' K)ᶜ) :
    ∃ Ω : Set ℂ, IsOpen Ω ∧ K ⊆ Ω ∧ ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f Ω ∧
      ¬ ∃ p : ℕ → Polynomial ℂ,
        TendstoUniformlyOn (fun n z => (p n).eval z) f atTop K := by
  obtain ⟨a, ha, m, hm, _, _, hobstruct⟩ :=
    disconnected_spherical_complement_polynomial_obstruction hK hdisc
  refine ⟨{a}ᶜ, isClosed_singleton.isOpen_compl, ?_, fun z => (z - a)⁻¹, ?_, ?_⟩
  · intro z hz hza
    exact ha ((mem_singleton_iff.mp hza) ▸ hz)
  · intro z hz
    exact ((differentiableAt_id.sub_const a).inv
      (sub_ne_zero.mpr (by simpa only [mem_compl_iff, mem_singleton_iff, id_eq] using hz))).differentiableWithinAt
  · rintro ⟨p, hp⟩
    obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hp m⁻¹ (inv_pos.mpr hm)).exists
    apply hobstruct (p n)
    intro z hz
    simpa only [dist_eq_norm, norm_sub_rev] using hn z hz

#print axioms sphericalComplementComponents
#print axioms countable_spherical_complement_components
#print axioms exists_bounded_complement_component
#print axioms frontier_complement_component_subset
#print axioms reciprocal_approximation_obstruction
#print axioms polynomial_approximation_obstruction
#print axioms disconnected_spherical_complement_polynomial_obstruction
#print axioms exists_holomorphic_not_polynomial_uniform_limit
end RudinRCA.Chapter13
