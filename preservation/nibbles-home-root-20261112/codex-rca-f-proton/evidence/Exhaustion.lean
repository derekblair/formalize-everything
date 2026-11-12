import RudinRCA.Chapter13
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open Set Filter Metric
open scoped Topology OnePoint

namespace RudinRCA.Chapter13

/-- The explicit compact exhaustion in 13.3, with the book's positive index shifted by one. -/
def exhaustionLevel (Ω : Set ℂ) (n : ℕ) : Set ℂ :=
  closedBall 0 ((n : ℝ) + 1) ∩
    {z | ∀ a ∉ Ω, ((n : ℝ) + 1)⁻¹ ≤ dist z a}

theorem exhaustionLevel_subset (Ω : Set ℂ) (n : ℕ) : exhaustionLevel Ω n ⊆ Ω := by
  intro z hz
  by_contra hzΩ
  have hh := hz.2 z hzΩ
  simp only [dist_self] at hh
  have hp : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
  linarith

theorem exhaustionLevel_isCompact (Ω : Set ℂ) (n : ℕ) : IsCompact (exhaustionLevel Ω n) := by
  apply (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 1)).inter_right
  simp only [ofPred_forall]
  exact isClosed_iInter fun a ↦ isClosed_iInter fun _ ↦
    isClosed_le continuous_const (continuous_id.dist continuous_const)

theorem exhaustionLevel_mono (Ω : Set ℂ) : Monotone (exhaustionLevel Ω) := by
  intro n m hnm z hz
  have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnm
  refine ⟨closedBall_subset_closedBall hnm' hz.1, fun a ha ↦ ?_⟩
  exact (inv_anti₀ (by positivity) hnm').trans (hz.2 a ha)

theorem exhaustionLevel_subset_interior_succ (Ω : Set ℂ) (n : ℕ) :
    exhaustionLevel Ω n ⊆ interior (exhaustionLevel Ω (n + 1)) := by
  intro z hz
  let r : ℝ := min 1 (((n : ℝ) + 1)⁻¹ - (((n + 1 : ℕ) : ℝ) + 1)⁻¹)
  have hstep : (n : ℝ) + 1 < ((n + 1 : ℕ) : ℝ) + 1 := by norm_num
  have hinv : (((n + 1 : ℕ) : ℝ) + 1)⁻¹ < ((n : ℝ) + 1)⁻¹ :=
    (inv_lt_inv₀ (by positivity) (by positivity)).2 hstep
  have hr : 0 < r := lt_min zero_lt_one (sub_pos.mpr hinv)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrd : r ≤ ((n : ℝ) + 1)⁻¹ - (((n + 1 : ℕ) : ℝ) + 1)⁻¹ := min_le_right _ _
  refine mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨r, hr, ?_⟩)
  intro w hw
  have hwz : dist w z < r := hw
  refine ⟨?_, fun a ha ↦ ?_⟩
  · rw [mem_closedBall, dist_zero_right]
    have htri : ‖w‖ ≤ dist w z + ‖z‖ := by
      simpa [dist_eq_norm] using norm_add_le (w - z) z
    have hzn : ‖z‖ ≤ (n : ℝ) + 1 := by simpa [mem_closedBall] using hz.1
    norm_num at hstep ⊢
    linarith
  · have htri := dist_triangle z w a
    rw [dist_comm z w] at htri
    have hza := hz.2 a ha
    linarith

theorem exists_mem_exhaustionLevel {Ω : Set ℂ} (hΩ : IsOpen Ω) {z : ℂ} (hz : z ∈ Ω) :
    ∃ n, z ∈ exhaustionLevel Ω n := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (max ‖z‖ δ⁻¹)
  have hnz : ‖z‖ < (n : ℝ) := (le_max_left _ _).trans_lt hn
  have hnδ : δ⁻¹ < (n : ℝ) := (le_max_right _ _).trans_lt hn
  have hnδ' : ((n : ℝ) + 1)⁻¹ ≤ δ := by
    rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
    have hnδdiv : 1 / δ < (n : ℝ) := by simpa only [one_div] using hnδ
    have hd : 1 < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hnδdiv
    nlinarith
  refine ⟨n, ?_, fun a ha ↦ hnδ'.trans ?_⟩
  · rw [mem_closedBall, dist_zero_right]
    linarith
  · by_contra hdist
    have : a ∈ ball z δ := by
      rw [mem_ball, dist_comm]
      exact lt_of_not_ge hdist
    exact ha (hball this)

theorem iUnion_exhaustionLevel {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    ⋃ n, exhaustionLevel Ω n = Ω := by
  ext z
  simp only [mem_iUnion]
  exact ⟨fun ⟨n, hz⟩ ↦ exhaustionLevel_subset Ω n hz,
    fun hz ↦ exists_mem_exhaustionLevel hΩ hz⟩

theorem compact_subset_exhaustionLevel {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) : ∃ n, K ⊆ exhaustionLevel Ω n := by
  have hmono : Monotone (fun n ↦ interior (exhaustionLevel Ω n)) :=
    fun _ _ hnm ↦ interior_mono (exhaustionLevel_mono Ω hnm)
  obtain ⟨n, hn⟩ := hK.elim_directed_cover (fun n ↦ interior (exhaustionLevel Ω n))
    (fun _ ↦ isOpen_interior) (fun z hz ↦ by
      obtain ⟨n, hn⟩ := exists_mem_exhaustionLevel hΩ (hKΩ hz)
      exact mem_iUnion.mpr ⟨n + 1, exhaustionLevel_subset_interior_succ Ω n hn⟩)
    hmono.directed_le
  exact ⟨n, hn.trans interior_subset⟩

/-- Local connected pieces meeting `A` ensure that each component of `T` contains
    a component of `A`. -/
theorem component_contains_component_of_local_pieces {X : Type*} [TopologicalSpace X]
    {A T : Set X} (hAT : A ⊆ T)
    (hpieces : ∀ x ∈ T, ∃ S : Set X, x ∈ S ∧ S ⊆ T ∧ IsPreconnected S ∧ (S ∩ A).Nonempty) :
    ∀ x ∈ T, ∃ a ∈ A, connectedComponentIn A a ⊆ connectedComponentIn T x := by
  intro x hx
  obtain ⟨S, hxS, hST, hS, a, haS, haA⟩ := hpieces x hx
  refine ⟨a, haA, ?_⟩
  have haT := hS.subset_connectedComponentIn hxS hST haS
  rw [connectedComponentIn_eq haT]
  exact connectedComponentIn_mono a hAT

/-- The forward radial ray from a nonzero complex point is connected and unbounded. -/
theorem radialRay_connected_unbounded (z : ℂ) (hz : z ≠ 0) :
    IsConnected ((fun t : ℝ ↦ t • z) '' Ici 1) ∧
    (∀ r > 0, ∃ w ∈ ((fun t : ℝ ↦ t • z) '' Ici 1), r < ‖w‖) := by
  refine ⟨isConnected_Ici.image _ (continuous_id.smul continuous_const).continuousOn, ?_⟩
  intro r hr
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let t : ℝ := r / ‖z‖ + 1
  have ht : 1 ≤ t := by
    dsimp [t]
    linarith [div_nonneg hr.le hzpos.le]
  refine ⟨t • z, mem_image_of_mem _ ht, ?_⟩
  rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans ht)]
  dsimp [t]
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hzpos), one_mul]
  linarith

theorem exhaustionLevel_complement_components (Ω : Set ℂ) (n : ℕ) :
    ∀ x ∈ (((↑) : ℂ → RiemannSphere) '' exhaustionLevel Ω n)ᶜ,
      ∃ a ∈ (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ,
        connectedComponentIn (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ a ⊆
          connectedComponentIn (((↑) : ℂ → RiemannSphere) '' exhaustionLevel Ω n)ᶜ x := by
  apply component_contains_component_of_local_pieces
  · exact compl_subset_compl.mpr (image_mono (exhaustionLevel_subset Ω n))
  intro x hx
  induction x using OnePoint.rec with
  | infty =>
    refine ⟨{∞}, by simp, ?_, isPreconnected_singleton, ?_⟩
    · simpa using hx
    · exact ⟨∞, by simp, by simp⟩
  | coe z =>
    have hzK : z ∉ exhaustionLevel Ω n := by simpa using hx
    by_cases hzlarge : (n : ℝ) + 1 < ‖z‖
    · let S : Set ℂ := (fun t : ℝ ↦ t • z) '' Ici 1
      have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity : 0 < (n : ℝ) + 1) hzlarge.le
      obtain ⟨hS, huS⟩ := radialRay_connected_unbounded z (norm_pos_iff.mp hzpos)
      refine ⟨insert ∞ ((↑) '' S), ?_, ?_,
        (isConnected_insert_infinity hS huS).isPreconnected, ?_⟩
      · apply mem_insert_of_mem
        exact mem_image_of_mem _ ⟨1, by simp, by simp⟩
      · intro y hy
        rcases hy with rfl | ⟨w, ⟨t, ht, rfl⟩, rfl⟩
        · simp
        · simp only [mem_compl_iff, OnePoint.coe_injective.mem_set_image]
          intro hw
          have hnorm : ‖t • z‖ = t * ‖z‖ :=
            by rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans ht)]
          have hlarge : (n : ℝ) + 1 < ‖t • z‖ := by
            rw [hnorm]
            exact hzlarge.trans_le (le_mul_of_one_le_left hzpos.le ht)
          exact (not_lt_of_ge (by simpa [mem_closedBall] using hw.1)) hlarge
      · exact ⟨∞, by simp, by simp⟩
    · have hznorm : ‖z‖ ≤ (n : ℝ) + 1 := le_of_not_gt hzlarge
      have hsep : ¬∀ a ∉ Ω, ((n : ℝ) + 1)⁻¹ ≤ dist z a := by
        intro h
        exact hzK ⟨by simpa [mem_closedBall] using hznorm, h⟩
      push_neg at hsep
      obtain ⟨a, haΩ, hza⟩ := hsep
      let S : Set ℂ := ball a ((n : ℝ) + 1)⁻¹
      refine ⟨((↑) : ℂ → RiemannSphere) '' S, mem_image_of_mem _ hza, ?_,
        isPreconnected_ball.image _ OnePoint.continuous_coe.continuousOn, ?_⟩
      · rintro y ⟨w, hw, rfl⟩
        simp only [mem_compl_iff, OnePoint.coe_injective.mem_set_image]
        intro hwK
        exact not_lt_of_ge (hwK.2 a haΩ) hw
      · refine ⟨(a : RiemannSphere), mem_image_of_mem _ (mem_ball_self (by positivity)), ?_⟩
        simpa using haΩ

/-- Rudin 13.3, all clauses including the spherical complement component condition. -/
theorem compact_exhaustion_with_spherical_complement_components {Ω : Set ℂ}
    (hΩ : IsOpen Ω) :
    ∃ K : ℕ → Set ℂ,
      (∀ n, IsCompact (K n)) ∧
      (∀ n, K n ⊆ Ω) ∧
      (⋃ n, K n) = Ω ∧
      (∀ n, K n ⊆ interior (K (n + 1))) ∧
      (∀ L : Set ℂ, IsCompact L → L ⊆ Ω → ∃ n, L ⊆ K n) ∧
      (∀ n x, x ∈ (((↑) : ℂ → RiemannSphere) '' K n)ᶜ →
        ∃ a ∈ (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ,
          connectedComponentIn (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ a ⊆
            connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K n)ᶜ x) :=
  ⟨exhaustionLevel Ω, exhaustionLevel_isCompact Ω, exhaustionLevel_subset Ω,
    iUnion_exhaustionLevel hΩ, exhaustionLevel_subset_interior_succ Ω,
    fun _ hL hLΩ ↦ compact_subset_exhaustionLevel hΩ hL hLΩ,
    exhaustionLevel_complement_components Ω⟩

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.compact_exhaustion_with_spherical_complement_components
