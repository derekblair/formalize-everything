/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license; see evidence/LICENSE-mathlib-Apache-2.0.
Authors: Yury Kudryashov

Adaptation of the extremal-map proof from mathlib4 PR33505, upstream
commit d43061d911b1aeae0788591da437a3b115098962, to the holomorphic
square-root premise used in Rudin RCA 13.11(j) and 14.8.
New premise and initial-map bridge developed in the Codex Rudin RCA lane.
This file follows RiemannMappingFull.lean in the aggregate; pending check.
-/
import Mathlib.Analysis.Complex.RiemannMapping
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.UniformSpace.Ascoli

open Set Metric Function Filter
open scoped Pointwise Topology ComplexConjugate Real BigOperators Uniformity

namespace Complex

/-- The exact zero-free holomorphic square-root property in Rudin RCA 13.11(j). -/
def HasHolomorphicSquareRoots (U : Set ℂ) : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → (∀ z ∈ U, f z ≠ 0) →
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, g z ^ 2 = f z

/-- Extend the chosen root arbitrarily off the domain to make the square identity global. -/
theorem HasHolomorphicSquareRoots.exists_continuousOn_sq_eq {U : Set ℂ}
    (hroots : HasHolomorphicSquareRoots U) {f : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f U) (hf₀ : ∀ z ∈ U, f z ≠ 0) :
    ∃ g : ℂ → ℂ, ContinuousOn g U ∧ ∀ z, g z ^ 2 = f z := by
  classical
  obtain ⟨g, hgd, hgf⟩ := hroots f hfd hf₀
  refine ⟨U.piecewise g (fun z => f z ^ (1 / 2 : ℂ)), ?_, ?_⟩
  · exact hgd.continuousOn.congr (fun z hz => by simp [hz])
  · intro z
    by_cases hz : z ∈ U
    · simpa [hz] using hgf z hz
    · simp [hz, ← Complex.cpow_mul_nat]

/-- A square-root branch of `z-a` gives an injective map with non-dense image. -/
theorem exists_injective_not_dense_image_deriv_ne_zero_of_square_roots {U : Set ℂ}
    (hUo : IsOpen U) (hUne : U.Nonempty) (hU : U ≠ univ)
    (hroots : HasHolomorphicSquareRoots U) :
    ∃ f : ℂ → ℂ, Injective f ∧ ¬Dense (f '' U) ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  obtain ⟨a, ha⟩ := ne_univ_iff_exists_notMem.mp hU
  obtain ⟨f, hfc, hf_sq⟩ := hroots.exists_continuousOn_sq_eq
    (differentiableOn_id.sub_const a) (fun z hz => sub_ne_zero.mpr (ne_of_mem_of_not_mem hz ha))
  have hf_inv : LeftInverse (fun w : ℂ => w ^ 2 + a) f := by
    intro z
    simp [hf_sq]
  have hf₀ : ∀ z ∈ U, f z ≠ 0 := by
    intro z hz hfz
    have := hf_sq z
    simp only [hfz, zero_pow (by norm_num : 2 ≠ 0), zero_eq_sub] at this
    exact ha (this ▸ hz)
  have hdf : ∀ z ∈ U, HasStrictDerivAt f (2 * f z)⁻¹ z := by
    intro z hz
    apply HasStrictDerivAt.of_local_left_inverse
    · exact hfc.continuousAt (hUo.mem_nhds hz)
    · simpa using (hasStrictDerivAt_pow 2 (f z)).add_const a
    · simpa using hf₀ z hz
    · exact .of_forall hf_inv
  refine ⟨f, hf_inv.injective, ?_, fun z hz => ?_⟩
  · simp only [Dense, not_forall, mem_closure_iff_frequently, not_frequently]
    obtain ⟨x, hx⟩ := hUne
    refine ⟨-f x, ?_⟩
    have himage : f '' U ∈ 𝓝 (f x) := by
      rw [← (hdf x hx).map_nhds_eq (by simpa using hf₀ x hx)]
      exact Filter.image_mem_map (hUo.mem_nhds hx)
    rw [nhds_neg, eventually_neg]
    filter_upwards [himage]
    rintro _ ⟨b, hb, rfl⟩ ⟨c, hc, hbc⟩
    obtain rfl : b = c := by
      rw [← hf_inv c, hbc]
      simpa using (hf_inv b).symm
    apply hf₀ b hb
    linear_combination hbc / 2
  · simpa [(hdf z hz).hasDerivAt.deriv] using hf₀ z hz

/-- The initial normalized family in the Riemann proof is nonempty under square roots. -/
theorem exists_mapsTo_unitBall_injOn_deriv_ne_zero_of_square_roots {U : Set ℂ}
    (hUo : IsOpen U) (hUne : U.Nonempty) (hU : U ≠ univ)
    (hroots : HasHolomorphicSquareRoots U) :
    ∃ f : ℂ → ℂ, MapsTo f U (ball 0 1) ∧ InjOn f U ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  obtain ⟨f, hf_inj, hfd, hdf⟩ :=
    exists_injective_not_dense_image_deriv_ne_zero_of_square_roots hUo hUne hU hroots
  obtain ⟨x, ε, hε₀, hε⟩ : ∃ (x : ℂ) (ε : ℝ), 0 < ε ∧ ∀ a ∈ U, ε < dist (f a) x := by
    simpa [Dense, mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall] using hfd
  have hfx : ∀ z ∈ U, f z ≠ x := fun z hz => by simpa using hε₀.trans (hε z hz)
  refine ⟨fun z => ε / (f z - x), ?_, ?_, ?_⟩
  · intro z hz
    rw [mem_ball_zero_iff, norm_div, norm_real, Real.norm_of_nonneg hε₀.le, div_lt_one₀]
    · simpa [dist_eq_norm] using hε z hz
    · simpa [sub_eq_zero] using hfx z hz
  · intro z hz w hw heq
    simpa [div_eq_mul_inv, hε₀.ne', hf_inj.eq_iff] using heq
  · intro z hz
    have hdz : DifferentiableAt ℂ f z := differentiableAt_of_deriv_ne_zero (hdf z hz)
    rw [(hasDerivAt_const _ _).fun_div (hdz.hasDerivAt.sub_const _) _ |>.deriv] <;>
      simp [*, ne_of_gt, sub_eq_zero]

/-- A unit-disc-valued square root; global identity makes subtype arithmetic transparent. -/
theorem UnitDisc.exists_continuousOn_sq_eq_of_square_roots {U : Set ℂ}
    (hroots : HasHolomorphicSquareRoots U) {g : ℂ → UnitDisc}
    (hgd : DifferentiableOn ℂ (UnitDisc.coe ∘ g) U) (hg₀ : 0 ∉ g '' U) :
    ∃ f : ℂ → UnitDisc, ContinuousOn f U ∧ ∀ z, f z ^ (2 : ℕ+) = g z := by
  obtain ⟨f, hfc, hf⟩ := hroots.exists_continuousOn_sq_eq hgd (fun z hz => by
    simpa only [Function.comp_apply, UnitDisc.coe_eq_zero] using
      ne_of_mem_of_not_mem (mem_image_of_mem g hz) hg₀)
  have hnorm : ∀ z, ‖f z‖ < 1 := by
    intro z
    rw [← pow_lt_one_iff_of_nonneg (norm_nonneg _) (by norm_num : 2 ≠ 0), ← norm_pow, hf]
    exact (g z).norm_lt_one
  lift f to ℂ → UnitDisc using hnorm
  refine ⟨f, UnitDisc.isEmbedding_coe.continuousOn_iff.mpr hfc, fun z => ?_⟩
  apply UnitDisc.coe_injective
  simpa only [UnitDisc.coe_pow, Function.comp_apply, PNat.val_ofNat] using hf z

theorem exists_map_unitDisc_injOn_deriv_ne_zero₀_of_square_roots {U : Set ℂ} (hUo : IsOpen U)
    (hroots : HasHolomorphicSquareRoots U) (hU : U ≠ univ) {x : ℂ} (hx : x ∈ U) :
    ∃ f : ℂ → UnitDisc, f x = 0 ∧ InjOn f U ∧ (∀ z ∈ U, deriv (UnitDisc.coe ∘ f) z ≠ 0) := by
  classical
  obtain ⟨f, hf_inj, hf_deriv⟩ :
      ∃ f : ℂ → UnitDisc, InjOn f U ∧ ∀ z ∈ U, deriv (UnitDisc.coe ∘ f) z ≠ 0 := by
    rcases exists_mapsTo_unitBall_injOn_deriv_ne_zero_of_square_roots hUo ⟨x, hx⟩ hU hroots with ⟨f, hfU, hf_inj, hdf⟩
    use fun z ↦ if hz : z ∈ U then .mk (f z) (by simpa using hfU hz) else 0
    constructor
    · simp +contextual [InjOn, UnitDisc.mk_inj, hf_inj.eq_iff]
    · intro z hz
      convert hdf z hz using 1
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hUo.mem_nhds hz] with w hw
      simp [hw]
  use fun z ↦ (-f x).shift (f z)
  refine ⟨?map_x, (-f x).shift.injective.comp_injOn hf_inj, ?deriv⟩
  case map_x => simp
  case deriv =>
    simpa only [Function.comp_def, ne_eq, UnitDisc.deriv_shift_comp_eq_zero]

theorem exist_map_unitDisc_injOn_norm_deriv_gt_of_square_roots {U : Set ℂ} (hUo : IsOpen U)
    (hroots : HasHolomorphicSquareRoots U) (hU : U ≠ univ) {x : ℂ} (hx : x ∈ U) {f : ℂ → UnitDisc}
    (hdf : DifferentiableOn ℂ (UnitDisc.coe ∘ f) U) (hf₀ : f x = 0) (hf_inj : InjOn f U)
    (hsurj : ¬SurjOn f U univ) :
    ∃ g : ℂ → UnitDisc, g x = 0 ∧ InjOn g U ∧ DifferentiableOn ℂ (UnitDisc.coe ∘ g) U ∧
      ‖deriv (UnitDisc.coe ∘ f) x‖ < ‖deriv (UnitDisc.coe ∘ g) x‖ := by
  by_cases hdf₀ : deriv (UnitDisc.coe ∘ f) x = 0
  · rcases exists_map_unitDisc_injOn_deriv_ne_zero₀_of_square_roots hUo hroots hU hx with ⟨g, hg₀, hg_inj, hdg⟩
    refine ⟨g, hg₀, hg_inj, fun z hz ↦ ?_, ?_⟩
    · exact (differentiableAt_of_deriv_ne_zero (hdg z hz)).differentiableWithinAt
    · simpa [hdf₀] using hdg x hx
  obtain ⟨c, hc⟩ : ∃ c, ∀ z ∈ U, f z ≠ c := by simpa [SurjOn, eq_univ_iff_forall] using hsurj
  have hcf : ContinuousOn f U := by
    rw [UnitDisc.isEmbedding_coe.continuousOn_iff]
    exact hdf.continuousOn
  rcases UnitDisc.exists_continuousOn_sq_eq_of_square_roots hroots
    ((-c).differentiableOn_shift_comp_iff.mpr hdf) (by simpa) with ⟨g, hgc, hgf⟩
  have hg₀ : ∀ z ∈ U, g z ≠ 0 := by
    intro z hz
    suffices g z ^ (2 : ℕ+) ≠ 0 by simpa using this
    simp [hgf, hc z hz]
  have hdg : ∀ z ∈ U, HasDerivAt (g · : ℂ → ℂ)
      ((1 - ‖(c : ℂ)‖ ^ 2) / (2 * g z * (1 - conj ↑c * f z) ^ 2) * deriv (f · : ℂ → ℂ) z) z := by
    intro z hz
    convert (hasDerivAt_pow 2 _).of_comp_left
      (UnitDisc.continuous_coe.continuousAt.comp <| hgc.continuousAt <| hUo.mem_nhds hz)
      (UnitDisc.hasDerivAt_shift_comp _ <| (hdf.hasDerivAt <| hUo.mem_nhds hz)) _
      (.of_forall fun x ↦ congr(UnitDisc.coe $(hgf x))) using 1
    · simp [Function.comp_def, field]
      ring
    · simp [hg₀ z hz]
  have hg_sq_norm (z : ℂ) : ‖(g z : ℂ)‖ ^ 2 = ‖((-c).shift (f z) : ℂ)‖ := by
    rw [← norm_pow, ← PNat.val_ofNat, ← UnitDisc.coe_pow, hgf, Function.comp_apply]
  have hg_norm (z : ℂ) : ‖(g z : ℂ)‖ = √‖((-c).shift (f z) : ℂ)‖ := by
    rw [← Real.sqrt_sq (norm_nonneg _), hg_sq_norm]
  refine ⟨(-g x).shift ∘ g, ?map_x, ?injOn, ?deriv, ?norm_deriv⟩
  case map_x => simp
  case injOn =>
    refine (-g x).shift.injective.comp_injOn fun z hz w hw hzw ↦ ?_
    simpa [hgf, hf_inj.eq_iff hz hw] using congr($hzw ^ (2 : ℕ+))
  case deriv =>
    exact (-g x).differentiableOn_shift_comp_iff.mpr fun z hz ↦
      (hdg z hz).differentiableAt.differentiableWithinAt
  case norm_deriv =>
    have hkey : ‖deriv (UnitDisc.coe ∘ ⇑(-g x).shift ∘ g) x‖ =
        ‖deriv (f · : ℂ → ℂ) x‖ * (√‖(c : ℂ)‖ + √‖(c⁻¹ : ℂ)‖) / 2 := by
      have hgx : ‖(g x : ℂ)‖ = √‖(c : ℂ)‖ := by simp [hg_norm, hf₀]
      simp only [Function.comp_def, UnitDisc.deriv_shift_comp, (hdg x hx).deriv, norm_mul, norm_div,
        ← mul_assoc, conj_mul', UnitDisc.coe_neg, map_neg, neg_mul]
      conv_rhs => rw [mul_comm, mul_div_right_comm]
      congr 1
      norm_cast
      have hpos₁ : 0 < 1 - ‖(c : ℂ)‖ := sub_pos.2 c.norm_lt_one
      have hpos₂ : 0 < 1 - ‖(c : ℂ)‖ ^ 2 := sub_pos.2 c.sq_norm_lt_one
      simp [field, hgx, hf₀, ← sub_eq_add_neg, abs_of_pos, hpos₁, hpos₂]
      ring
    rw [hkey, mul_div_assoc]
    apply lt_mul_of_one_lt_right
    · simpa using hdf₀
    · have hc₀ : 0 < ‖(c : ℂ)‖ := by simpa [hf₀] using (hc x hx).symm
      suffices √‖(c : ℂ)‖ * 2 < ‖(c : ℂ)‖ + 1 by simpa [field] using this
      have : √‖(c : ℂ)‖ ≠ 1 := by simp [c.norm_ne_one]
      rw [← sub_ne_zero, ← sq_pos_iff, sub_sq, Real.sq_sqrt] at this
      · linear_combination this
      · apply norm_nonneg


open scoped UniformConvergence in
theorem exists_bijOn_unitBall_map_eq_zero_of_square_roots {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U)
    (hroots : HasHolomorphicSquareRoots U)
    (hU : U ≠ univ) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ BijOn f U (ball 0 1) ∧ f x₀ = 0 := by
  set 𝔖 : Set (Set ℂ) := {K | K ⊆ U ∧ IsCompact K}
  have h𝔖K : ∀ K ∈ 𝔖, IsCompact K := fun _ ↦ And.right
  have hcnt : (𝓤 (ℂ →ᵤ[𝔖] ℂ)).IsCountablyGenerated := by
    have := hUo.locallyCompactSpace
    have : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
    set φ : CompactExhaustion U := default
    apply UniformOnFun.isCountablyGenerated_uniformity (t := fun n ↦ (↑) '' φ n)
    · intro n
      exact ⟨image_val_subset, φ.isCompact n |>.image continuous_subtype_val⟩
    · exact monotone_image.comp φ.subset
    · rintro K ⟨hKU, hKc⟩
      lift K to Set U using hKU
      rw [← Subtype.isCompact_iff] at hKc
      exact (φ.exists_superset_of_isCompact hKc).imp fun n hn ↦ by gcongr
  set F : (ℂ →ᵤ[𝔖] ℂ) → (ℂ → ℂ) := fun f ↦ UniformOnFun.toFun _ f
  have hF : ∀ {f : ℂ →ᵤ[𝔖] ℂ} {s}, TendstoLocallyUniformlyOn F (F f) (𝓝[s] f) U := by
    intro f s
    have : Tendsto id (𝓝[s] f) (𝓝 f) := tendsto_id'.mpr nhdsWithin_le_nhds
    simpa [tendstoLocallyUniformlyOn_iff_forall_isCompact hUo,
      UniformOnFun.tendsto_iff_tendstoUniformlyOn, 𝔖] using this
  set s : Set (ℂ →ᵤ[𝔖] ℂ) :=
    {f : ℂ →ᵤ[𝔖] ℂ |
      MapsTo (F f) U (ball 0 1) ∧
      InjOn (F f) U ∧
      DifferentiableOn ℂ (F f) U ∧
      deriv (F f) x₀ ≠ 0 ∧
      F f x₀ = 0}
  have hsd : ∀ f ∈ s, DifferentiableOn ℂ (F f) U := fun f hf ↦ hf.2.2.1
  have hs_ne : s.Nonempty := by
    rcases exists_map_unitDisc_injOn_deriv_ne_zero₀_of_square_roots hUo hroots hU hx₀ with ⟨f, hf₀, hf_inj, hfd⟩
    exact ⟨UniformOnFun.ofFun 𝔖 (f ·), fun x hx ↦ (f x).2,
      by simpa [F, InjOn] using hf_inj, fun z hz ↦
        differentiableAt_of_deriv_ne_zero (hfd z hz) |>.differentiableWithinAt,
      hfd x₀ hx₀, by simp [F, hf₀]⟩
  have hcmpct := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding h𝔖K (α := ℂ) (s := s) (F := F)
    .id ?eqcont ?bdd
  case eqcont =>
    rintro K ⟨hKU, -⟩ z hz
    refine equicontinuousAt_of_forall_norm_le (hUo.mem_nhds <| hKU hz) (fun i ↦ hsd _ i.2)
      ⟨1, fun i z hz ↦ le_of_lt ?_⟩ |>.equicontinuousWithinAt _
    simpa using i.2.1 hz
  case bdd =>
    intro K hK x hx
    exact ⟨closedBall 0 1, isCompact_closedBall _ _, fun i hi ↦
      ball_subset_closedBall <| hi.1 (hK.1 hx)⟩
  have hcl : closure s ⊆
      {f | MapsTo (F f) U (ball 0 1) ∧
           ((∃ C, EqOn (F f) (const ℂ C) U) ∨ InjOn (F f) U) ∧
           DifferentiableOn ℂ (F f) U ∧
           F f x₀ = 0} := by
    intro f hf
    rw [mem_closure_iff_nhdsWithin_neBot] at hf
    have htendsto : TendstoLocallyUniformlyOn F (F f) (𝓝[s] f) U := hF
    have hdf : DifferentiableOn ℂ (F f) U := htendsto.differentiableOn
      (eventually_mem_nhdsWithin.mono hsd) hUo
    have hf_le : ∀ z ∈ U, ‖F f z‖ ≤ 1 := by
      intro z hz
      refine le_of_tendsto (htendsto.tendsto_at hz).norm <| eventually_mem_nhdsWithin.mono ?_
      intro g hg
      apply le_of_lt
      simpa using hg.1 hz
    have hfx₀ : F f x₀ = 0 := by
      refine tendsto_nhds_unique (htendsto.tendsto_at hx₀) ?_
      refine tendsto_const_nhds.congr' <| eventually_mem_nhdsWithin.mono fun g hg ↦ ?_
      exact hg.2.2.2.2.symm
    refine ⟨?_, ?_, hdf, hfx₀⟩
    · by_contra hf_ball
      obtain ⟨z, hzU, hz⟩ : ∃ z ∈ U, 1 ≤ ‖F f z‖ := by simpa [MapsTo] using hf_ball
      have : IsMaxOn (‖F f ·‖) U z := by
        intro y hy
        simpa using (hf_le y hy).trans hz
      have : F f x₀ = F f z := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
        hUc.isPreconnected hUo hdf hzU this hx₀
      norm_num [← this, hfx₀] at hz
    · exact eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn hUo
        hUc.isPreconnected
        (eventually_mem_nhdsWithin.mono fun g hg ↦ hg.2.1)
        (eventually_mem_nhdsWithin.mono hsd)
        htendsto
  have hcont : ContinuousOn (fun f ↦ ‖deriv (F f) x₀‖) (closure s) := by
    refine .mono (.norm fun f hf ↦ ?_) hcl
    refine TendstoLocallyUniformlyOn.tendsto_at (.deriv hF ?_ hUo) hx₀
    refine eventually_mem_nhdsWithin.mono fun g hg ↦ ?_
    exact hg.2.2.1
  rcases hcmpct.exists_isMaxOn hs_ne.closure hcont with ⟨f₀, hf₀_mem, hf₀_max⟩
  have hdf₀_x₀ : 0 < ‖deriv (F f₀) x₀‖ := by
    rcases hs_ne with ⟨f', hf'⟩
    refine lt_of_lt_of_le ?_ (hf₀_max <| subset_closure hf')
    simpa using hf'.2.2.2.1
  rcases hcl hf₀_mem with ⟨hf₀_mapsTo, hf₀_inj, hf₀_diff, hf₀_x₀⟩
  replace hf₀_inj : InjOn (F f₀) U := by
    refine hf₀_inj.resolve_left ?_
    rintro ⟨C, hC⟩
    rw [hC.eventuallyEq_of_mem (hUo.mem_nhds hx₀) |>.deriv_eq] at hdf₀_x₀
    unfold const at hdf₀_x₀
    simp at hdf₀_x₀
  refine ⟨F f₀, hf₀_diff, ⟨hf₀_mapsTo, hf₀_inj, ?_⟩, hf₀_x₀⟩
  by_contra! hsurj
  clear hf₀_mem hdf₀_x₀
  rw [isMaxOn_iff] at hf₀_max
  wlog hf₀_lt : ∀ z, ‖F f₀ z‖ < 1 generalizing f₀
  · classical
    apply this (UniformOnFun.ofFun _ <| U.indicator (F f₀))
    · have : deriv (U.indicator (F f₀)) x₀ = deriv (F f₀) x₀ :=
        U.eqOn_indicator.eventuallyEq_of_mem (hUo.mem_nhds hx₀) |>.deriv_eq
      simpa [this, F] using hf₀_max
    · simpa [F, U.eqOn_indicator.mapsTo_iff]
    · simpa [F, differentiableOn_congr U.eqOn_indicator]
    · simp [F, hf₀_x₀]
    · simpa [F, U.eqOn_indicator.injOn_iff]
    · simpa [F, U.eqOn_indicator.surjOn_iff]
    · intro z
      by_cases hz : z ∈ U <;> simp [F, hz, mem_ball_zero_iff.mp (hf₀_mapsTo _)]
  lift F f₀ to ℂ → UnitDisc using hf₀_lt with f hf
  replace hsurj : ¬SurjOn f U univ := by
    simpa [SurjOn, eq_univ_iff_forall, subset_def, UnitDisc.exists, ← UnitDisc.coe_inj] using hsurj
  rcases exist_map_unitDisc_injOn_norm_deriv_gt_of_square_roots hUo hroots hU hx₀ hf₀_diff (by simpa using hf₀_x₀)
    (by simpa [InjOn] using hf₀_inj) hsurj with ⟨g, hg₀, hg_inj, hdg, hg_lt⟩
  refine hf₀_max (UniformOnFun.ofFun _ (g · : ℂ → ℂ)) (subset_closure ?_) |>.not_gt hg_lt
  refine ⟨fun z _ ↦ (g z).2, by simpa [F, InjOn] using hg_inj, hdg, ?_, by simpa [F] using hg₀⟩
  rw [← norm_pos_iff]
  exact (norm_nonneg _).trans_lt hg_lt


#print axioms Complex.exists_injective_not_dense_image_deriv_ne_zero_of_square_roots
#print axioms Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero_of_square_roots
#print axioms Complex.UnitDisc.exists_continuousOn_sq_eq_of_square_roots
#print axioms Complex.exists_map_unitDisc_injOn_deriv_ne_zero₀_of_square_roots
#print axioms Complex.exist_map_unitDisc_injOn_norm_deriv_gt_of_square_roots
#print axioms Complex.exists_bijOn_unitBall_map_eq_zero_of_square_roots
end Complex
