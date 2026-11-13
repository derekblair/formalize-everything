import RudinRCA.Chapter10
import RudinRCA.Chapter11
import RudinRCA.Chapter13
import RudinRCA.Chapter14
import RudinRCA.Chapter15
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Topology.Instances.Rat
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Topology.Homotopy.Path
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Chapter 16: Analytic Continuation (`16.1`–`16.22`)

Formalization of Walter Rudin, *Real and Complex Analysis* (3rd ed., McGraw-Hill, 1987),
Chapter 16 (pp. 319–332), following `SCOPING-G.md`:
- `16.1`–`16.7`: Regular and singular boundary points, natural boundaries, lacunary series,
  Ostrowski overconvergence (`16.5`), Hadamard gap theorem (`16.6`), smooth-boundary example (`16.7`).
- `16.8`–`16.16`: Line/circle Morera gluing (`16.8`), function elements and curve continuation
  (`16.9`–`16.11`), endpoint-fixed homotopies (`16.12`–`16.14`), Monodromy Theorem (`16.15`),
  and nonsimply-connected obstruction (`16.16`).
- `16.17`–`16.20`: The modular group, congruence subgroup `Γ`, fundamental set `Q` (`16.19`),
  and the elliptic modular function `λ` (`16.20`).
- `16.21`–`16.22`: Exposition contrasting Little Picard and Big Picard (`16.21`, with
  `BigPicardStatement` recorded honestly as a `Prop` without claiming Big Picard proved),
  and Little Picard's Theorem (`16.22`).
-/

set_option autoImplicit false

noncomputable section

namespace RudinRCA.Chapter16

section Chapter16PartA
open Set Filter Metric Complex Finset
open scoped Topology NNReal ENNReal ContDiff


/-!
## 16.1: Regular and Singular Boundary Points of a Disc
-/

/-- **Rudin RCA 16.1 (Regular boundary point, p. 319):**
Given `f : ℂ → ℂ` on a disc `Metric.ball a R` (`0 < R`), a boundary point `ζ ∈ Metric.sphere a R`
is a *regular point* of `f` if there exist `r > 0` and `g : ℂ → ℂ` holomorphic on `Metric.ball ζ r`
such that `g(z) = f(z)` for all `z ∈ Metric.ball a R ∩ Metric.ball ζ r`. -/
def IsRegularBoundaryPoint (f : ℂ → ℂ) (a : ℂ) (R : ℝ) (ζ : ℂ) : Prop :=
  ζ ∈ Metric.sphere a R ∧
  ∃ (r : ℝ) (g : ℂ → ℂ), 0 < r ∧ DifferentiableOn ℂ g (Metric.ball ζ r) ∧
    Set.EqOn f g (Metric.ball a R ∩ Metric.ball ζ r)

/-- **Rudin RCA 16.1 (Singular boundary point, p. 319):**
A boundary point `ζ ∈ Metric.sphere a R` that is not a regular point of `f` is a *singular point*
of `f`. -/
def IsSingularBoundaryPoint (f : ℂ → ℂ) (a : ℂ) (R : ℝ) (ζ : ℂ) : Prop :=
  ζ ∈ Metric.sphere a R ∧ ¬ IsRegularBoundaryPoint f a R ζ

/-- Any boundary point `ζ' ∈ Metric.sphere a R` inside a regular continuation disc `Metric.ball ζ r`
is itself a regular boundary point of `f`. -/
theorem isRegularBoundaryPoint_of_mem_ball {f g : ℂ → ℂ} {a ζ ζ' : ℂ} {R r : ℝ}
    (hζ' : ζ' ∈ Metric.sphere a R)
    (hg : DifferentiableOn ℂ g (Metric.ball ζ r))
    (heq : Set.EqOn f g (Metric.ball a R ∩ Metric.ball ζ r))
    (hmem : ζ' ∈ Metric.ball ζ r) :
    IsRegularBoundaryPoint f a R ζ' := by
  have hr' : 0 < r - dist ζ' ζ := sub_pos.mpr (Metric.mem_ball.mp hmem)
  have hsub : Metric.ball ζ' (r - dist ζ' ζ) ⊆ Metric.ball ζ r := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    linarith [dist_triangle z ζ' ζ]
  refine ⟨hζ', r - dist ζ' ζ, g, hr', hg.mono hsub, ?_⟩
  exact heq.mono (Set.inter_subset_inter_right _ hsub)

/-- **Rudin RCA 16.1 (Relative openness of regular boundary points, p. 319):**
For any disc `Metric.ball a R` and `f : ℂ → ℂ`, the set of regular boundary points is relatively
open in `Metric.sphere a R` (both in ambient-intersection form and in the subspace topology on
`Metric.sphere a R`), and the set of singular boundary points is closed in `Metric.sphere a R`. -/
theorem theorem16_1 (f : ℂ → ℂ) (a : ℂ) (R : ℝ) :
    (∃ U : Set ℂ, IsOpen U ∧
      {ζ ∈ Metric.sphere a R | IsRegularBoundaryPoint f a R ζ} = Metric.sphere a R ∩ U) ∧
    IsOpen {ζ : Metric.sphere a R | IsRegularBoundaryPoint f a R ζ.1} ∧
    IsClosed {ζ : Metric.sphere a R | IsSingularBoundaryPoint f a R ζ.1} := by
  let U : Set ℂ :=
    ⋃ (ζ : ℂ) (_ : IsRegularBoundaryPoint f a R ζ)
      (r : ℝ) (_ : ∃ g : ℂ → ℂ, 0 < r ∧ DifferentiableOn ℂ g (Metric.ball ζ r) ∧
        Set.EqOn f g (Metric.ball a R ∩ Metric.ball ζ r)),
      Metric.ball ζ r
  have hU_open : IsOpen U :=
    isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦
      isOpen_iUnion fun _ ↦ Metric.isOpen_ball
  have hU_eq : {ζ ∈ Metric.sphere a R | IsRegularBoundaryPoint f a R ζ} = Metric.sphere a R ∩ U := by
    ext ζ'
    constructor
    · rintro ⟨hζ's, hreg⟩
      rcases hreg with ⟨_, r, g, hr, hg, heq⟩
      refine ⟨hζ's, Set.mem_iUnion.mpr ⟨ζ', Set.mem_iUnion.mpr ⟨⟨hζ's, r, g, hr, hg, heq⟩,
        Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨⟨g, hr, hg, heq⟩,
          Metric.mem_ball_self hr⟩⟩⟩⟩⟩
    · rintro ⟨hζ's, hmemU⟩
      simp only [U, Set.mem_iUnion] at hmemU
      rcases hmemU with ⟨ζ, _, r, ⟨g, _, hg, heq⟩, hmem⟩
      exact ⟨hζ's, isRegularBoundaryPoint_of_mem_ball hζ's hg heq hmem⟩
  have hsub_open : IsOpen {ζ : Metric.sphere a R | IsRegularBoundaryPoint f a R ζ.1} := by
    rw [isOpen_induced_iff]
    refine ⟨U, hU_open, ?_⟩
    ext ⟨ζ, hζ⟩
    change ζ ∈ U ↔ IsRegularBoundaryPoint f a R ζ
    constructor
    · intro hUζ
      have hmem : ζ ∈ Metric.sphere a R ∩ U := ⟨hζ, hUζ⟩
      rw [← hU_eq] at hmem
      exact hmem.2
    · intro hreg
      have hmem : ζ ∈ {w ∈ Metric.sphere a R | IsRegularBoundaryPoint f a R w} := ⟨hζ, hreg⟩
      rw [hU_eq] at hmem
      exact hmem.2
  have hsub_closed : IsClosed {ζ : Metric.sphere a R | IsSingularBoundaryPoint f a R ζ.1} := by
    have hcompl :
        {ζ : Metric.sphere a R | IsSingularBoundaryPoint f a R ζ.1} =
          {ζ : Metric.sphere a R | IsRegularBoundaryPoint f a R ζ.1}ᶜ := by
      ext ⟨ζ, hζ⟩
      change (ζ ∈ Metric.sphere a R ∧ ¬ IsRegularBoundaryPoint f a R ζ) ↔
        ¬ IsRegularBoundaryPoint f a R ζ
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hζ, h⟩⟩
    rw [hcompl]
    exact hsub_open.isClosed_compl
  exact ⟨⟨U, hU_open, hU_eq⟩, hsub_open, hsub_closed⟩

/-!
## 16.2: Radius of Convergence `1` and Existence of a Singular Point on `T`
-/

/-- **Rudin RCA 16.2 (Power series with radius of convergence `1`, p. 320):**
`c : ℕ → ℂ` has radius of convergence equal to `1`. -/
def HasRadiusOfConvergenceOne (c : ℕ → ℂ) : Prop :=
  (FormalMultilinearSeries.ofScalars ℂ c).radius = 1

/-- If `HasRadiusOfConvergenceOne c`, then `∑ c_n z^n` converges absolutely (and hence converges)
for every `z ∈ Metric.ball (0 : ℂ) 1`. -/
theorem summable_norm_of_hasRadiusOfConvergenceOne {c : ℕ → ℂ}
    (hc : HasRadiusOfConvergenceOne c) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    Summable (fun n : ℕ ↦ ‖c n * z ^ n‖) := by
  have hnorm : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  let r : ℝ≥0 := ⟨‖z‖, norm_nonneg z⟩
  have hr : (r : ℝ≥0∞) < (FormalMultilinearSeries.ofScalars ℂ c).radius := by
    rw [hc]
    exact_mod_cast hnorm
  have hs := (FormalMultilinearSeries.ofScalars ℂ c).summable_norm_mul_pow hr
  refine hs.congr fun n ↦ ?_
  rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow]
  rfl

theorem summable_of_hasRadiusOfConvergenceOne {c : ℕ → ℂ}
    (hc : HasRadiusOfConvergenceOne c) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    Summable (fun n : ℕ ↦ c n * z ^ n) :=
  (summable_norm_of_hasRadiusOfConvergenceOne hc hz).of_norm

/-- Equivalence of `HasRadiusOfConvergenceOne c` with convergence on `Metric.ball 0 1` and
existence of a divergent point in `Metric.closedBall 0 r` for every `r > 1`. -/
theorem hasRadiusOfConvergenceOne_iff_closedBall (c : ℕ → ℂ) :
    HasRadiusOfConvergenceOne c ↔
      (∀ z ∈ Metric.ball (0 : ℂ) 1, Summable (fun n : ℕ ↦ c n * z ^ n)) ∧
      (∀ r : ℝ, 1 < r → ∃ z ∈ Metric.closedBall (0 : ℂ) r,
        ¬ Summable (fun n : ℕ ↦ c n * z ^ n)) := by
  let p := FormalMultilinearSeries.ofScalars ℂ c
  constructor
  · intro hc
    refine ⟨fun z hz ↦ summable_of_hasRadiusOfConvergenceOne hc hz, fun r hr ↦ ?_⟩
    refine ⟨(r : ℂ), ?_, ?_⟩
    · simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (zero_lt_one.trans hr)]
    · intro hsum
      have htend : Tendsto (fun n : ℕ ↦ ‖p n‖ * r ^ n) atTop (𝓝 0) := by
        have h0 := hsum.tendsto_atTop_zero.norm
        simp only [norm_zero] at h0
        refine h0.congr fun n ↦ ?_
        have hr_pos : 0 ≤ r := (zero_lt_one.trans hr).le
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr_pos,
          ← FormalMultilinearSeries.ofScalars_norm ℂ c n]
      let r_nn : ℝ≥0 := ⟨r, (zero_lt_one.trans hr).le⟩
      have hle : (r_nn : ℝ≥0∞) ≤ p.radius := p.le_radius_of_tendsto htend
      rw [hc] at hle
      have hr_le : r ≤ 1 := by exact_mod_cast hle
      linarith
  · rintro ⟨hconv, hdiv⟩
    apply le_antisymm
    · by_contra hnot_le
      have hgt : (1 : ℝ≥0∞) < p.radius := not_le.mp hnot_le
      obtain ⟨s, hs1, hsp⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hgt
      have hs1' : (1 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
      let r : ℝ := (1 + (s : ℝ)) / 2
      have hr1 : 1 < r := by dsimp [r]; linarith
      have hrs : r < (s : ℝ) := by dsimp [r]; linarith
      obtain ⟨z, hz_cb, hz_nsum⟩ := hdiv r hr1
      apply hz_nsum
      have hznorm : ‖z‖ < (s : ℝ) := by
        have hle : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hz_cb
        exact hle.trans_lt hrs
      have hzeb : z ∈ Metric.eball (0 : ℂ) p.radius := by
        rw [Metric.mem_eball, edist_zero_right]
        have hlt_s : (‖z‖₊ : ℝ≥0∞) < (s : ℝ≥0∞) := by exact_mod_cast hznorm
        exact hlt_s.trans hsp
      have hp_sum := p.summable hzeb
      refine hp_sum.congr fun n ↦ ?_
      change FormalMultilinearSeries.ofScalars ℂ c n (fun _ ↦ z) = c n * z ^ n
      rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    · refine ENNReal.le_of_forall_pos_nnreal_lt fun r _hr_pos hr1 ↦ ?_
      have hr1' : (r : ℝ) < 1 := by exact_mod_cast hr1
      have hmem : ((r : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
        simp only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg r.coe_nonneg]
        exact hr1'
      have hsum := hconv ((r : ℝ) : ℂ) hmem
      have htend : Tendsto (fun n : ℕ ↦ ‖p n‖ * (r : ℝ) ^ n) atTop (𝓝 0) := by
        have h0 := hsum.tendsto_atTop_zero.norm
        simp only [norm_zero] at h0
        refine h0.congr fun n ↦ ?_
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg,
          ← FormalMultilinearSeries.ofScalars_norm ℂ c n]
      exact p.le_radius_of_tendsto htend

/-- Equivalence of `HasRadiusOfConvergenceOne c` with convergence on `Metric.ball 0 1` and
failure of universal convergence on `Metric.ball 0 R` for every `R > 1`. -/
theorem hasRadiusOfConvergenceOne_iff_ball (c : ℕ → ℂ) :
    HasRadiusOfConvergenceOne c ↔
      (∀ z ∈ Metric.ball (0 : ℂ) 1, Summable (fun n : ℕ ↦ c n * z ^ n)) ∧
      (∀ R : ℝ, 1 < R → ¬ ∀ z ∈ Metric.ball (0 : ℂ) R,
        Summable (fun n : ℕ ↦ c n * z ^ n)) := by
  rw [hasRadiusOfConvergenceOne_iff_closedBall]
  constructor
  · rintro ⟨hconv, hdiv⟩
    refine ⟨hconv, fun R hR hall ↦ ?_⟩
    let r : ℝ := (1 + R) / 2
    have hr1 : 1 < r := by dsimp [r]; linarith
    have hrR : r < R := by dsimp [r]; linarith
    obtain ⟨z, hz_cb, hz_nsum⟩ := hdiv r hr1
    exact hz_nsum (hall z (Metric.closedBall_subset_ball hrR hz_cb))
  · rintro ⟨hconv, hdiv⟩
    refine ⟨hconv, fun r hr ↦ ?_⟩
    by_contra! hall_cb
    apply hdiv r hr
    intro z hz
    exact hall_cb z (Metric.ball_subset_closedBall hz)

/-- Compact closed-disc thickening lemma: if an open set `U ⊆ ℂ` contains `Metric.closedBall 0 R`
(`0 ≤ R`), then `U` contains `Metric.ball 0 (R + δ)` for some `δ > 0`. -/
private theorem exists_ball_subset_of_closedBall_subset_isOpen {U : Set ℂ} {R : ℝ}
    (_hR : 0 ≤ R) (hU : IsOpen U) (hsub : Metric.closedBall (0 : ℂ) R ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball (0 : ℂ) (R + δ) ⊆ U := by
  let K : Set ℂ := Metric.closedBall (0 : ℂ) (R + 1) ∩ Uᶜ
  have hK_closed : IsClosed K := isClosed_closedBall.inter hU.isClosed_compl
  have hK_compact : IsCompact K :=
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) (R + 1)) hK_closed inter_subset_left
  by_cases hK_ne : K.Nonempty
  · obtain ⟨z₀, hz₀K, hmin⟩ := hK_compact.exists_isMinOn hK_ne continuous_norm.continuousOn
    have hz₀_not_cb : z₀ ∉ Metric.closedBall (0 : ℂ) R := fun hmem ↦ hz₀K.2 (hsub hmem)
    have hR_lt : R < ‖z₀‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hz₀_not_cb
    have hz₀_le : ‖z₀‖ ≤ R + 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz₀K.1
    let δ : ℝ := (‖z₀‖ - R) / 2
    have hδ_pos : 0 < δ := by dsimp [δ]; linarith
    refine ⟨δ, hδ_pos, fun z hz ↦ ?_⟩
    have hznorm : ‖z‖ < R + δ := by simpa [Metric.mem_ball, dist_zero_right] using hz
    by_contra hzU
    have hzK : z ∈ K := by
      refine ⟨?_, hzU⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      dsimp [δ] at hznorm
      linarith
    have hle : ‖z₀‖ ≤ ‖z‖ := hmin hzK
    dsimp [δ] at hznorm
    linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hK_ne
    refine ⟨1 / 2, by positivity, fun z hz ↦ ?_⟩
    have hznorm : ‖z‖ < R + 1 / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hz
    by_contra hzU
    have hzK : z ∈ K := by
      refine ⟨?_, hzU⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    rw [hK_ne] at hzK
    exact hzK

/-- Helper identifying `Metric.eball (0 : ℂ) 1 = Metric.ball (0 : ℂ) 1`. -/
private theorem eball_zero_one_eq_ball :
    Metric.eball (0 : ℂ) 1 = Metric.ball (0 : ℂ) 1 := by
  simpa using (Metric.eball_coe (x := (0 : ℂ)) (ε := (1 : ℝ≥0)))

/-- Holomorphicity of `f` on `Metric.ball 0 1` when `f` is represented by a radius-`1` power
series `∑' n, c n * z ^ n` on `Metric.ball 0 1`. -/
theorem hasFPowerSeriesOnBall_of_hasRadiusOfConvergenceOne {c : ℕ → ℂ} {f : ℂ → ℂ}
    (hc : HasRadiusOfConvergenceOne c)
    (hf : Set.EqOn f (fun z ↦ ∑' n : ℕ, c n * z ^ n) (Metric.ball (0 : ℂ) 1)) :
    HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ c) 0 1 := by
  let p := FormalMultilinearSeries.ofScalars ℂ c
  have hp_rad : p.radius = 1 := hc
  have hp_pos : 0 < p.radius := by rw [hp_rad]; exact zero_lt_one
  have hp_ball : HasFPowerSeriesOnBall p.sum p 0 1 := by
    have h := p.hasFPowerSeriesOnBall hp_pos
    rwa [hp_rad] at h
  refine hp_ball.congr ?_
  intro z hz
  have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := by
    rwa [← eball_zero_one_eq_ball]
  change p.sum z = f z
  rw [hf hz_ball]
  exact FormalMultilinearSeries.ofScalars_sum_eq c z

/-- **Rudin RCA 16.2 (Theorem, p. 320):**
Suppose `∑_{n=0}^∞ c_n z^n` has radius of convergence `1`, and represents `f` on `U = D(0; 1)`.
Then `f` is holomorphic on `U`, and `f` has at least one singular point on the unit circle `T`. -/
theorem theorem16_2 {c : ℕ → ℂ} {f : ℂ → ℂ}
    (hc : HasRadiusOfConvergenceOne c)
    (hf : Set.EqOn f (fun z ↦ ∑' n : ℕ, c n * z ^ n) (Metric.ball (0 : ℂ) 1)) :
    DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) ∧
    ∃ ζ ∈ Metric.sphere (0 : ℂ) 1, IsSingularBoundaryPoint f 0 1 ζ := by
  classical
  have hfp : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ c) 0 1 :=
    hasFPowerSeriesOnBall_of_hasRadiusOfConvergenceOne hc hf
  have hf_diff : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) := by
    have hd := hfp.differentiableOn
    rwa [eball_zero_one_eq_ball] at hd
  refine ⟨hf_diff, ?_⟩
  by_contra hno_sing
  have hall_reg : ∀ ζ : Metric.sphere (0 : ℂ) 1, IsRegularBoundaryPoint f 0 1 ζ.1 := by
    intro ζ
    by_contra hnot_reg
    exact hno_sing ⟨ζ.1, ζ.2, ⟨ζ.2, hnot_reg⟩⟩
  choose r g hr_pos hg_diff hg_eq using fun ζ : Metric.sphere (0 : ℂ) 1 ↦ (hall_reg ζ).2
  have hcov : Metric.sphere (0 : ℂ) 1 ⊆
      ⋃ ζ : Metric.sphere (0 : ℂ) 1, Metric.ball ζ.1 (r ζ / 4) := by
    intro z hz
    refine Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (by linarith [hr_pos ⟨z, hz⟩])⟩
  obtain ⟨F, hF_cov⟩ :=
    (isCompact_sphere (0 : ℂ) 1).elim_finite_subcover
      (fun ζ : Metric.sphere (0 : ℂ) 1 ↦ Metric.ball ζ.1 (r ζ / 4))
      (fun _ ↦ Metric.isOpen_ball) hcov
  let U_cov : Set ℂ := Metric.ball (0 : ℂ) 1 ∪ ⋃ ζ ∈ F, Metric.ball ζ.1 (r ζ / 4)
  have hU_open : IsOpen U_cov :=
    Metric.isOpen_ball.union (isOpen_biUnion fun _ _ ↦ Metric.isOpen_ball)
  have hcb_sub : Metric.closedBall (0 : ℂ) 1 ⊆ U_cov := by
    intro z hz
    rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hz) with hlt | heq
    · exact Or.inl (Metric.mem_ball.mpr hlt)
    · exact Or.inr (hF_cov (Metric.mem_sphere.mpr heq))
  obtain ⟨δ, hδ_pos, hball_sub⟩ :=
    exists_ball_subset_of_closedBall_subset_isOpen zero_le_one hU_open hcb_sub
  have hg_compat_le : ∀ (ζ₁ ζ₂ : Metric.sphere (0 : ℂ) 1) {w : ℂ},
      r ζ₁ ≤ r ζ₂ →
      w ∈ Metric.ball ζ₁.1 (r ζ₁ / 4) →
      w ∈ Metric.ball ζ₂.1 (r ζ₂ / 4) →
      g ζ₁ w = g ζ₂ w := by
    intro ζ₁ ζ₂ w hr_le hw₁ hw₂
    let B : Set ℂ := Metric.ball ζ₁.1 (r ζ₁ / 2)
    have hB_open : IsOpen B := Metric.isOpen_ball
    have hB_sub₁ : B ⊆ Metric.ball ζ₁.1 (r ζ₁) :=
      Metric.ball_subset_ball (by linarith [hr_pos ζ₁])
    have hB_sub₂ : B ⊆ Metric.ball ζ₂.1 (r ζ₂) := by
      intro u hu
      rw [Metric.mem_ball] at hu hw₁ hw₂ ⊢
      have h1 : dist ζ₁.1 w < r ζ₁ / 4 := by rwa [dist_comm]
      calc dist u ζ₂.1 ≤ dist u ζ₁.1 + dist ζ₁.1 w + dist w ζ₂.1 := dist_triangle4 u ζ₁.1 w ζ₂.1
        _ < r ζ₁ / 2 + r ζ₁ / 4 + r ζ₂ / 4 := by linarith
        _ ≤ r ζ₂ / 2 + r ζ₂ / 4 + r ζ₂ / 4 := by linarith
        _ = r ζ₂ := by ring
    have hwB : w ∈ B := Metric.ball_subset_ball (by linarith [hr_pos ζ₁]) hw₁
    let t : ℝ := min (1 / 2) (r ζ₁ / 4)
    have ht_pos : 0 < t := lt_min (by positivity) (by linarith [hr_pos ζ₁])
    have ht_le_half : t ≤ 1 / 2 := min_le_left _ _
    have ht_le_q : t ≤ r ζ₁ / 4 := min_le_right _ _
    let z_in : ℂ := ((1 - t : ℝ) : ℂ) * ζ₁.1
    have hζ₁_norm : ‖ζ₁.1‖ = 1 := by
      have h := ζ₁.2
      rwa [Metric.mem_sphere, dist_zero_right] at h
    have hzin_ball : z_in ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      dsimp [z_in]
      rw [norm_mul, hζ₁_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      linarith
    have hzin_B : z_in ∈ B := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hdiff : z_in - ζ₁.1 = ((-t : ℝ) : ℂ) * ζ₁.1 := by
        dsimp [z_in]
        push_cast
        ring
      rw [hdiff, norm_mul, hζ₁_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_neg, abs_of_pos ht_pos]
      linarith [hr_pos ζ₁]
    have hev : g ζ₁ =ᶠ[𝓝 z_in] g ζ₂ := by
      filter_upwards [(Metric.isOpen_ball.inter hB_open).mem_nhds ⟨hzin_ball, hzin_B⟩] with y hy
      have h1 : f y = g ζ₁ y := hg_eq ζ₁ ⟨hy.1, hB_sub₁ hy.2⟩
      have h2 : f y = g ζ₂ y := hg_eq ζ₂ ⟨hy.1, hB_sub₂ hy.2⟩
      exact h1.symm.trans h2
    have han₁ : AnalyticOnNhd ℂ (g ζ₁) B := ((hg_diff ζ₁).mono hB_sub₁).analyticOnNhd hB_open
    have han₂ : AnalyticOnNhd ℂ (g ζ₂) B := ((hg_diff ζ₂).mono hB_sub₂).analyticOnNhd hB_open
    exact han₁.eqOn_of_preconnected_of_eventuallyEq han₂
      (convex_ball ζ₁.1 (r ζ₁ / 2)).isPreconnected hzin_B hev hwB
  have hg_compat : ∀ (ζ₁ ζ₂ : Metric.sphere (0 : ℂ) 1) {w : ℂ},
      w ∈ Metric.ball ζ₁.1 (r ζ₁ / 4) →
      w ∈ Metric.ball ζ₂.1 (r ζ₂ / 4) →
      g ζ₁ w = g ζ₂ w := by
    intro ζ₁ ζ₂ w hw₁ hw₂
    rcases le_total (r ζ₁) (r ζ₂) with hle | hle
    · exact hg_compat_le ζ₁ ζ₂ hle hw₁ hw₂
    · exact (hg_compat_le ζ₂ ζ₁ hle hw₂ hw₁).symm
  let G : ℂ → ℂ := fun z ↦
    if z ∈ Metric.ball (0 : ℂ) 1 then f z
    else if hex : ∃ ζ ∈ F, z ∈ Metric.ball ζ.1 (r ζ / 4) then g hex.choose z
    else 0
  have hG_eq_f : Set.EqOn G f (Metric.ball (0 : ℂ) 1) := fun z hz ↦ by
    dsimp only [G]
    rw [ite_eq_left_iff]
    exact fun h ↦ (h hz).elim
  have hG_eq_g : ∀ ζ ∈ F, Set.EqOn G (g ζ) (Metric.ball ζ.1 (r ζ / 4)) := by
    intro ζ hζF z hz
    dsimp only [G]
    by_cases hz_ball : z ∈ Metric.ball (0 : ℂ) 1
    · rw [ite_eq_left_iff.mpr fun h ↦ (h hz_ball).elim]
      exact hg_eq ζ ⟨hz_ball, Metric.ball_subset_ball (by linarith [hr_pos ζ]) hz⟩
    · rw [ite_eq_right_iff.mpr fun h ↦ (hz_ball h).elim]
      split_ifs with hex
      · exact hg_compat hex.choose ζ hex.choose_spec.2 hz
      · exact (hex ⟨ζ, hζF, hz⟩).elim
  have hG_diff_U : DifferentiableOn ℂ G U_cov := by
    intro z hz
    rcases hz with hz_ball | hz_union
    · have hd : DifferentiableAt ℂ f z := hf_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hz_ball)
      have hev : G =ᶠ[𝓝 z] f :=
        Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz_ball) hG_eq_f
      exact (hev.differentiableAt_iff.mpr hd).differentiableWithinAt
    · obtain ⟨ζ, hζF, hz_ζ⟩ := Set.mem_iUnion₂.mp hz_union
      have hsub_r : Metric.ball ζ.1 (r ζ / 4) ⊆ Metric.ball ζ.1 (r ζ) :=
        Metric.ball_subset_ball (by linarith [hr_pos ζ])
      have hd : DifferentiableAt ℂ (g ζ) z :=
        ((hg_diff ζ).mono hsub_r).differentiableAt (Metric.isOpen_ball.mem_nhds hz_ζ)
      have hev : G =ᶠ[𝓝 z] g ζ :=
        Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz_ζ) (hG_eq_g ζ hζF)
      exact (hev.differentiableAt_iff.mpr hd).differentiableWithinAt
  have hG_diff_big : DifferentiableOn ℂ G (Metric.ball (0 : ℂ) (1 + δ)) :=
    hG_diff_U.mono hball_sub
  let R_mid : ℝ≥0 := ⟨1 + δ / 2, by positivity⟩
  have hR_mid_pos : 0 < R_mid := by exact_mod_cast (by positivity : (0 : ℝ) < 1 + δ / 2)
  have hcb_big : Metric.closedBall (0 : ℂ) R_mid ⊆ Metric.ball (0 : ℂ) (1 + δ) :=
    Metric.closedBall_subset_ball (by change 1 + δ / 2 < 1 + δ; linarith)
  have hG_ps : HasFPowerSeriesOnBall G (cauchyPowerSeries G 0 R_mid) 0 R_mid :=
    (hG_diff_big.mono hcb_big).hasFPowerSeriesOnBall hR_mid_pos
  have hG_at_p : HasFPowerSeriesAt G (FormalMultilinearSeries.ofScalars ℂ c) 0 := by
    refine hfp.hasFPowerSeriesAt.congr ?_
    exact Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))
      fun z hz ↦ (hG_eq_f hz).symm
  have hp_eq_q : FormalMultilinearSeries.ofScalars ℂ c = cauchyPowerSeries G 0 R_mid :=
    hG_at_p.eq_formalMultilinearSeries hG_ps.hasFPowerSeriesAt
  have hrad_ge : (R_mid : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius := by
    rw [hp_eq_q]
    exact hG_ps.r_le
  rw [hc] at hrad_ge
  have hle_one : (R_mid : ℝ) ≤ 1 := by exact_mod_cast hrad_ge
  change 1 + δ / 2 ≤ 1 at hle_one
  linarith

/-!
## 16.3: Natural Boundary of the Unit Disc
-/

/-- **Rudin RCA 16.3 (Natural boundary, p. 320):**
`f : ℂ → ℂ` is holomorphic on `Metric.ball 0 1` and has the unit circle `T = Metric.sphere 0 1`
as its *natural boundary* if every point of `T` is a singular boundary point of `f`. -/
def HasNaturalBoundaryUnitCircle (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) ∧
  ∀ ζ ∈ Metric.sphere (0 : ℂ) 1, IsSingularBoundaryPoint f 0 1 ζ

/-- Connectedness helper: if `U` is a nonempty open proper subset of a connected open set `Ω`,
then `Ω` intersects `frontier U`. -/
theorem exists_mem_inter_frontier_of_ssubset_isRegion {U Ω : Set ℂ}
    (hU_open : IsOpen U) (hU_ne : U.Nonempty) (hΩ : RudinRCA.Chapter10.IsRegion Ω)
    (hssub : U ⊂ Ω) :
    ∃ ζ : ℂ, ζ ∈ Ω ∧ ζ ∈ frontier U := by
  by_contra! hdisj
  obtain ⟨w, hwΩ, hwU⟩ := Set.exists_of_ssubset hssub
  have hcov : Ω ⊆ U ∪ (closure U)ᶜ := by
    intro z hzΩ
    by_cases hzU : z ∈ U
    · exact Or.inl hzU
    · right
      intro hz_cl
      have hz_fr : z ∈ frontier U := by
        rw [frontier, hU_open.interior_eq]
        exact ⟨hz_cl, hzU⟩
      exact hdisj z hzΩ hz_fr
  obtain ⟨z₀, hz₀U⟩ := hU_ne
  have hΩU : (Ω ∩ U).Nonempty := ⟨z₀, hssub.subset hz₀U, hz₀U⟩
  have hΩc : (Ω ∩ (closure U)ᶜ).Nonempty := by
    refine ⟨w, hwΩ, fun hw_cl ↦ ?_⟩
    have hw_fr : w ∈ frontier U := by
      rw [frontier, hU_open.interior_eq]
      exact ⟨hw_cl, hwU⟩
    exact hdisj w hwΩ hw_fr
  obtain ⟨y, _, hyU, hy_ncl⟩ :=
    hΩ.2.isPreconnected U (closure U)ᶜ hU_open isClosed_closure.isOpen_compl hcov hΩU hΩc
  exact hy_ncl (subset_closure hyU)

/-- **Rudin RCA 16.3 (Non-extendability across a natural boundary, p. 320):**
If `f` has the unit circle `T` as a natural boundary, then `f` has no holomorphic extension to any
strictly larger plane region `Ω ⊋ Metric.ball 0 1`. -/
theorem theorem16_3 {f : ℂ → ℂ} (hf : HasNaturalBoundaryUnitCircle f) :
    ¬ ∃ (Ω : Set ℂ) (F : ℂ → ℂ),
      RudinRCA.Chapter10.IsRegion Ω ∧
      Metric.ball (0 : ℂ) 1 ⊂ Ω ∧
      DifferentiableOn ℂ F Ω ∧
      Set.EqOn f F (Metric.ball (0 : ℂ) 1) := by
  rintro ⟨Ω, F, hΩ, hssub, hF_diff, heq⟩
  obtain ⟨ζ, hζΩ, hζ_fr⟩ :=
    exists_mem_inter_frontier_of_ssubset_isRegion Metric.isOpen_ball
      ⟨0, Metric.mem_ball_self zero_lt_one⟩ hΩ hssub
  have hζ_sp : ζ ∈ Metric.sphere (0 : ℂ) 1 := by
    rwa [frontier_ball (0 : ℂ) one_ne_zero] at hζ_fr
  obtain ⟨r, hr_pos, hball_sub⟩ := Metric.isOpen_iff.mp hΩ.1 ζ hζΩ
  have hreg : IsRegularBoundaryPoint f 0 1 ζ :=
    ⟨hζ_sp, r, F, hr_pos, hF_diff.mono hball_sub, heq.mono inter_subset_left⟩
  exact (hf.2 ζ hζ_sp).2 hreg

/-!
## 16.4: Remark — Explicit Dyadic Lacunary Series & Non-Extendable Functions on Any Region
-/

/-- Coefficient sequence of `∑_{n=0}^∞ z^{2^n}` (`1` when `n` is a power of `2`, `0` otherwise). -/
def lacunaryDyadicCoeffs (n : ℕ) : ℂ :=
  open Classical in
  if ∃ k : ℕ, n = 2 ^ k then 1 else 0

/-- **Rudin RCA 16.4 (Explicit dyadic lacunary series, pp. 320–321):**
`f(z) = ∑_{n=0}^∞ z^{2^n}`. -/
def lacunaryDyadicSeries (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ (2 ^ n)

private theorem summable_pow_two_pow {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    Summable (fun n : ℕ ↦ z ^ (2 ^ n)) := by
  have hnorm : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg z) hnorm) fun n ↦ ?_
  rw [norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg z) hnorm.le (Nat.lt_two_pow_self (n := n)).le

private theorem norm_exp_ofReal_mul_I_sub_one_le (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ≤ |t| := by
  have hsq : ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ^ 2 = (2 * Real.sin (t / 2)) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.exp_mul_I]
    have hre : (Complex.cos (t : ℂ) + Complex.sin (t : ℂ) * Complex.I - 1).re = Real.cos t - 1 := by
      simp [Complex.cos_ofReal_re, Complex.sin_ofReal_im]
    have him : (Complex.cos (t : ℂ) + Complex.sin (t : ℂ) * Complex.I - 1).im = Real.sin t := by
      simp [Complex.cos_ofReal_im, Complex.sin_ofReal_re]
    rw [Complex.normSq_apply, hre, him]
    have hsc : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := Real.cos_sq_add_sin_sq t
    have hc2 : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
      have h1 := Real.cos_two_mul (t / 2)
      have h2 := Real.cos_sq_add_sin_sq (t / 2)
      have htwo : 2 * (t / 2) = t := by ring
      rw [htwo] at h1
      linarith
    nlinarith
  have h1 : ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (t / 2)| := by
    rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_sq_eq_abs, abs_mul,
      abs_of_pos (two_pos : (0 : ℝ) < 2)]
  rw [h1]
  have hsin : |Real.sin (t / 2)| ≤ |t / 2| := Real.abs_sin_le_abs
  rw [abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2)] at hsin
  linarith

/-- Density of dyadic roots of unity `{ζ : ℂ | ∃ m : ℕ, ζ ^ (2 ^ m) = 1}` in `Metric.sphere 0 1`. -/
theorem dense_dyadicRootsOfUnity_in_unitCircle :
    Metric.sphere (0 : ℂ) 1 ⊆ closure {ζ : ℂ | ∃ m : ℕ, ζ ^ (2 ^ m) = 1} := by
  intro w hw
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hw_norm : ‖w‖ = 1 := by rwa [Metric.mem_sphere, dist_zero_right] at hw
  let θ : ℝ := Complex.arg w
  have hw_eq : Complex.exp ((θ : ℂ) * Complex.I) = w := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    simpa [hw_norm, θ] using h
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 * Real.pi) / ε)
  have hpow_gt : (2 * Real.pi) / ε < (2 ^ N : ℝ) :=
    hN.trans_le (by exact_mod_cast (Nat.lt_two_pow_self (n := N)).le)
  have hstep_lt : (2 * Real.pi) / (2 ^ N : ℝ) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    have := (div_lt_iff₀ hε).mp hpow_gt
    linarith
  let k : ℤ := ⌊θ * (2 ^ N : ℝ) / (2 * Real.pi)⌋
  let θ_N : ℝ := (k : ℝ) * (2 * Real.pi) / (2 ^ N : ℝ)
  let ζ : ℂ := Complex.exp ((θ_N : ℂ) * Complex.I)
  refine ⟨ζ, ⟨N, ?_⟩, ?_⟩
  · dsimp [ζ, θ_N]
    rw [← Complex.exp_nat_mul]
    have h2N_ne : ((2 : ℂ) ^ N) ≠ 0 := pow_ne_zero N two_ne_zero
    have hexp_arg :
        ((2 ^ N : ℕ) : ℂ) * ((((k : ℝ) * (2 * Real.pi) / (2 ^ N : ℝ) : ℝ) : ℂ) * Complex.I) =
          (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      push_cast
      calc (2 : ℂ) ^ N * ((k : ℂ) * (2 * ↑Real.pi) / (2 : ℂ) ^ N * Complex.I)
          = ((2 : ℂ) ^ N * ((k : ℂ) * (2 * ↑Real.pi) / (2 : ℂ) ^ N)) * Complex.I := by ring
        _ = ((k : ℂ) * (2 * ↑Real.pi)) * Complex.I := by rw [mul_div_cancel₀ _ h2N_ne]
        _ = (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by ring
    rw [hexp_arg, Complex.exp_int_mul_two_pi_mul_I]
  · rw [dist_eq_norm, ← hw_eq]
    have hfactor : Complex.exp ((θ : ℂ) * Complex.I) - ζ =
        ζ * (Complex.exp (((θ - θ_N : ℝ) : ℂ) * Complex.I) - 1) := by
      dsimp [ζ]
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hfactor, norm_mul]
    have hζ_norm : ‖ζ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ_N
    rw [hζ_norm, one_mul]
    have hle1 : ‖Complex.exp (((θ - θ_N : ℝ) : ℂ) * Complex.I) - 1‖ ≤ |θ - θ_N| :=
      norm_exp_ofReal_mul_I_sub_one_le (θ - θ_N)
    have hfl_le : (k : ℝ) ≤ θ * (2 ^ N : ℝ) / (2 * Real.pi) := Int.floor_le _
    have hfl_lt : θ * (2 ^ N : ℝ) / (2 * Real.pi) < (k : ℝ) + 1 := Int.lt_floor_add_one _
    have h2pi_pos : 0 < 2 * Real.pi := by positivity
    have h2N_pos : (0 : ℝ) < (2 ^ N : ℝ) := by positivity
    have hmul_le : (k : ℝ) * (2 * Real.pi) ≤ θ * (2 ^ N : ℝ) :=
      (le_div_iff₀ h2pi_pos).mp hfl_le
    have hmul_lt : θ * (2 ^ N : ℝ) < ((k : ℝ) + 1) * (2 * Real.pi) :=
      (div_lt_iff₀ h2pi_pos).mp hfl_lt
    have hnonneg : 0 ≤ θ - θ_N := by
      dsimp [θ_N]
      have hdiv : (k : ℝ) * (2 * Real.pi) / (2 ^ N : ℝ) ≤ θ :=
        (div_le_iff₀ h2N_pos).mpr hmul_le
      linarith
    have hlt_step : θ - θ_N < (2 * Real.pi) / (2 ^ N : ℝ) := by
      dsimp [θ_N]
      have h1 : θ < ((k : ℝ) * (2 * Real.pi) + 2 * Real.pi) / (2 ^ N : ℝ) :=
        (lt_div_iff₀ h2N_pos).mpr (by linarith)
      rw [add_div] at h1
      linarith
    rw [abs_of_nonneg hnonneg] at hle1
    exact hle1.trans_lt (hlt_step.trans hstep_lt)

private theorem nhdsWithin_Iio_one_neBot : (𝓝[<] (1 : ℝ)).NeBot := by
  refine Filter.forall_mem_nonempty_iff_neBot.mp fun s hs ↦ ?_
  rw [mem_nhdsWithin] at hs
  rcases hs with ⟨U, hU_open, h1U, hUs⟩
  obtain ⟨δ, hδ_pos, hball⟩ := Metric.isOpen_iff.mp hU_open 1 h1U
  refine ⟨1 - δ / 2, hUs ⟨?_, ?_⟩⟩
  · apply hball
    rw [Metric.mem_ball, Real.dist_eq, show (1 - δ / 2) - 1 = -(δ / 2) by ring,
      abs_neg, abs_of_pos (by linarith)]
    linarith
  · change 1 - δ / 2 < 1
    linarith

/-- **Rudin RCA 16.4 (Explicit dyadic lacunary example, pp. 320–321):**
For `f(z) = ∑_{n=0}^∞ z^{2^n}`:
- `(a)` `lacunaryDyadicCoeffs` has radius of convergence `1`, `f` agrees with its power series on
  `Metric.ball 0 1`, and `f` is holomorphic on `Metric.ball 0 1`;
- `(b)` `f(z) = z + f(z^2)` and `f(z) = (∑_{k=0}^{m-1} z^{2^k}) + f(z^{2^m})` for all `z ∈ D(0; 1)`
  and `m : ℕ`;
- `(c)` dyadic roots of unity `{ζ | ∃ m, ζ^{2^m} = 1}` are dense in `Metric.sphere 0 1`, and along
  every dyadic-root radius `r ↦ r * ζ` (`r → 1⁻`), `‖f(r * ζ)‖ → +∞`;
- `(d)` `HasNaturalBoundaryUnitCircle lacunaryDyadicSeries`. -/
theorem theorem16_4_dyadic :
    (HasRadiusOfConvergenceOne lacunaryDyadicCoeffs ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, Summable (fun n : ℕ ↦ z ^ (2 ^ n)) ∧
        lacunaryDyadicSeries z = ∑' n : ℕ, lacunaryDyadicCoeffs n * z ^ n) ∧
      DifferentiableOn ℂ lacunaryDyadicSeries (Metric.ball (0 : ℂ) 1)) ∧
    ((∀ z ∈ Metric.ball (0 : ℂ) 1,
        lacunaryDyadicSeries z = z + lacunaryDyadicSeries (z ^ 2)) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ m : ℕ,
        lacunaryDyadicSeries z =
          (∑ k ∈ Finset.range m, z ^ (2 ^ k)) + lacunaryDyadicSeries (z ^ (2 ^ m)))) ∧
    (Metric.sphere (0 : ℂ) 1 ⊆ closure {ζ : ℂ | ∃ m : ℕ, ζ ^ (2 ^ m) = 1} ∧
      ∀ (ζ : ℂ) (m : ℕ), ζ ^ (2 ^ m) = 1 →
        Tendsto (fun r : ℝ ↦ ‖lacunaryDyadicSeries ((r : ℂ) * ζ)‖) (𝓝[<] 1) Filter.atTop) ∧
    HasNaturalBoundaryUnitCircle lacunaryDyadicSeries := by
  classical
  have hpow_strict : StrictMono (fun k : ℕ ↦ 2 ^ k) :=
    strictMono_nat_of_lt_succ fun k ↦ by
      rw [pow_succ']
      have hpos : 0 < 2 ^ k := by positivity
      omega
  have hinj : Function.Injective (fun k : ℕ ↦ 2 ^ k) := hpow_strict.injective
  have hcoeff_pow : ∀ k : ℕ, lacunaryDyadicCoeffs (2 ^ k) = 1 := by
    intro k
    dsimp [lacunaryDyadicCoeffs]
    exact ite_eq_left_iff.mpr fun h ↦ (h ⟨k, rfl⟩).elim
  have htsum_eq : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      lacunaryDyadicSeries z = ∑' n : ℕ, lacunaryDyadicCoeffs n * z ^ n := by
    intro z _
    dsimp [lacunaryDyadicSeries]
    symm
    have h1 : (∑' n : ℕ, lacunaryDyadicCoeffs n * z ^ n) =
        ∑' k : ℕ, lacunaryDyadicCoeffs (2 ^ k) * z ^ (2 ^ k) := by
      refine (hinj.tsum_eq ?_).symm
      intro n hn
      rw [Function.mem_support] at hn
      by_contra hnr
      apply hn
      have h0 : lacunaryDyadicCoeffs n = 0 := by
        dsimp [lacunaryDyadicCoeffs]
        refine ite_eq_right_iff.mpr fun hex ↦ ?_
        rcases hex with ⟨k, rfl⟩
        exact (hnr ⟨k, rfl⟩).elim
      rw [h0, zero_mul]
    rw [h1]
    refine tsum_congr fun k ↦ ?_
    simp [hcoeff_pow]
  have hrad : HasRadiusOfConvergenceOne lacunaryDyadicCoeffs := by
    rw [hasRadiusOfConvergenceOne_iff_closedBall]
    refine ⟨?_, ?_⟩
    · intro z hz
      have hnorm : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
      refine Summable.of_norm_bounded
        (summable_geometric_of_lt_one (norm_nonneg z) hnorm) fun n ↦ ?_
      dsimp [lacunaryDyadicCoeffs]
      split_ifs <;> simp
    · intro r hr
      refine ⟨1, ?_, ?_⟩
      · simp [Metric.mem_closedBall, hr.le]
      · intro hsum
        have ht0 : Tendsto (fun k : ℕ ↦ lacunaryDyadicCoeffs (2 ^ k) * (1 : ℂ) ^ (2 ^ k))
            atTop (𝓝 0) :=
          hsum.tendsto_atTop_zero.comp hpow_strict.tendsto_atTop
        have hconst : (fun k : ℕ ↦ lacunaryDyadicCoeffs (2 ^ k) * (1 : ℂ) ^ (2 ^ k)) = fun _ ↦ 1 := by
          ext k
          simp [hcoeff_pow]
        rw [hconst] at ht0
        exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht0)
  have hdiff : DifferentiableOn ℂ lacunaryDyadicSeries (Metric.ball (0 : ℂ) 1) :=
    (theorem16_2 hrad htsum_eq).1
  have hfeq1 : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      lacunaryDyadicSeries z = z + lacunaryDyadicSeries (z ^ 2) := by
    intro z hz
    dsimp [lacunaryDyadicSeries]
    rw [(summable_pow_two_pow hz).tsum_eq_zero_add]
    simp only [pow_zero, pow_one]
    congr 1
    refine tsum_congr fun n ↦ ?_
    rw [pow_succ', ← pow_mul]
  have hfeq_m : ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ m : ℕ,
      lacunaryDyadicSeries z =
        (∑ k ∈ Finset.range m, z ^ (2 ^ k)) + lacunaryDyadicSeries (z ^ (2 ^ m)) := by
    intro z hz m
    induction m with
    | zero => simp
    | succ m ih =>
      have hzm : z ^ (2 ^ m) ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right, norm_pow]
        have hzn : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
        exact pow_lt_one₀ (norm_nonneg z) hzn (by positivity)
      rw [ih, hfeq1 (z ^ (2 ^ m)) hzm, Finset.sum_range_succ, ← pow_mul, ← pow_succ]
      ring
  have hdiv_one : Tendsto (fun r : ℝ ↦ ‖lacunaryDyadicSeries (r : ℂ)‖) (𝓝[<] 1) Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro B
    obtain ⟨N, hN⟩ := exists_nat_gt (max B 0 + 1)
    have hcont : Continuous (fun r : ℝ ↦ ∑ k ∈ Finset.range N, r ^ (2 ^ k)) := by fun_prop
    have hat1 : (∑ k ∈ Finset.range N, (1 : ℝ) ^ (2 ^ k)) = (N : ℝ) := by simp
    have hev_gt : ∀ᶠ r : ℝ in 𝓝 (1 : ℝ), (N : ℝ) - 1 < ∑ k ∈ Finset.range N, r ^ (2 ^ k) := by
      have hlt : (N : ℝ) - 1 < ∑ k ∈ Finset.range N, (1 : ℝ) ^ (2 ^ k) := by linarith
      exact (isOpen_lt continuous_const hcont).mem_nhds hlt
    have hev_pos : ∀ᶠ r : ℝ in 𝓝 (1 : ℝ), 0 < r := Ioi_mem_nhds zero_lt_one
    filter_upwards [nhdsWithin_le_nhds (hev_gt.and hev_pos), self_mem_nhdsWithin] with r ⟨hsum_gt, hr0⟩ hr1
    have hr1' : r < 1 := hr1
    have hrc_ball : (r : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      exact hr1'
    have hre_sum : HasSum (fun k : ℕ ↦ r ^ (2 ^ k)) (lacunaryDyadicSeries (r : ℂ)).re := by
      have h := Complex.reCLM.hasSum (summable_pow_two_pow hrc_ball).hasSum
      refine h.congr_fun fun k ↦ ?_
      change r ^ (2 ^ k) = ((r : ℂ) ^ (2 ^ k)).re
      rw [← Complex.ofReal_pow]
      exact (Complex.ofReal_re _).symm
    have hle_re : (∑ k ∈ Finset.range N, r ^ (2 ^ k)) ≤ (lacunaryDyadicSeries (r : ℂ)).re := by
      rw [← hre_sum.tsum_eq]
      exact hre_sum.summable.sum_le_tsum (Finset.range N) fun k _ ↦ pow_nonneg hr0.le _
    have hre_le_norm : (lacunaryDyadicSeries (r : ℂ)).re ≤ ‖lacunaryDyadicSeries (r : ℂ)‖ :=
      Complex.re_le_norm _
    have hBN : B < (N : ℝ) - 1 := by
      have : max B 0 + 1 < (N : ℝ) := hN
      linarith [le_max_left B 0]
    linarith
  have hdiv_root : ∀ (ζ : ℂ) (m : ℕ), ζ ^ (2 ^ m) = 1 →
      Tendsto (fun r : ℝ ↦ ‖lacunaryDyadicSeries ((r : ℂ) * ζ)‖) (𝓝[<] 1) Filter.atTop := by
    intro ζ m hζm
    have hζ_norm : ‖ζ‖ = 1 := by
      have hpow_norm : ‖ζ‖ ^ (2 ^ m) = 1 := by
        rw [← norm_pow, hζm, norm_one]
      have hnn : 0 ≤ ‖ζ‖ := norm_nonneg ζ
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · linarith [pow_lt_one₀ hnn hlt (by positivity : 2 ^ m ≠ 0)]
      · linarith [one_lt_pow₀ hgt (by positivity : 2 ^ m ≠ 0)]
    have hpow_nhds : Tendsto (fun r : ℝ ↦ r ^ (2 ^ m)) (𝓝[<] 1) (𝓝[<] 1) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hc : Continuous (fun r : ℝ ↦ r ^ (2 ^ m)) := continuous_pow (2 ^ m)
        have hct : Tendsto (fun r : ℝ ↦ r ^ (2 ^ m)) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) ^ (2 ^ m))) :=
          hc.continuousAt.tendsto
        rw [one_pow] at hct
        exact hct.mono_left nhdsWithin_le_nhds
      · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one),
          self_mem_nhdsWithin] with r hr0 hr1
        have hr0' : 0 < r := hr0
        exact pow_lt_one₀ hr0'.le hr1 (by positivity)
    have htail_top : Tendsto (fun r : ℝ ↦ ‖lacunaryDyadicSeries ((r ^ (2 ^ m) : ℝ) : ℂ)‖)
        (𝓝[<] 1) Filter.atTop := hdiv_one.comp hpow_nhds
    rw [Filter.tendsto_atTop] at htail_top ⊢
    intro B
    filter_upwards [htail_top (B + m),
      nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one),
      self_mem_nhdsWithin] with r hbig hr0 hr1
    have hr0' : 0 < r := hr0
    have hr1' : r < 1 := hr1
    have hrz_ball : (r : ℂ) * ζ ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, hζ_norm, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0']
      exact hr1'
    have hpow_eq : ((r : ℂ) * ζ) ^ (2 ^ m) = ((r ^ (2 ^ m) : ℝ) : ℂ) := by
      rw [mul_pow, hζm, mul_one]
      norm_cast
    have heq := hfeq_m ((r : ℂ) * ζ) hrz_ball m
    rw [hpow_eq] at heq
    have hinit_le : ‖∑ k ∈ Finset.range m, ((r : ℂ) * ζ) ^ (2 ^ k)‖ ≤ (m : ℝ) := by
      calc ‖∑ k ∈ Finset.range m, ((r : ℂ) * ζ) ^ (2 ^ k)‖
          ≤ ∑ k ∈ Finset.range m, ‖((r : ℂ) * ζ) ^ (2 ^ k)‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.range m, (1 : ℝ) := by
            refine Finset.sum_le_sum fun k _ ↦ ?_
            rw [norm_pow, norm_mul, hζ_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hr0']
            exact pow_le_one₀ hr0'.le hr1'.le
        _ = (m : ℝ) := by simp
    have htri : ‖lacunaryDyadicSeries ((r ^ (2 ^ m) : ℝ) : ℂ)‖ ≤
        ‖lacunaryDyadicSeries ((r : ℂ) * ζ)‖ + ‖∑ k ∈ Finset.range m, ((r : ℂ) * ζ) ^ (2 ^ k)‖ := by
      have hsub : lacunaryDyadicSeries ((r ^ (2 ^ m) : ℝ) : ℂ) =
          lacunaryDyadicSeries ((r : ℂ) * ζ) - ∑ k ∈ Finset.range m, ((r : ℂ) * ζ) ^ (2 ^ k) := by
        linear_combination -heq
      rw [hsub]
      exact norm_sub_le _ _
    linarith
  have hnat : HasNaturalBoundaryUnitCircle lacunaryDyadicSeries := by
    refine ⟨hdiff, fun w hw ↦ ⟨hw, ?_⟩⟩
    intro hreg_w
    obtain ⟨U, hU_open, hU_eq⟩ := (theorem16_1 lacunaryDyadicSeries 0 1).1
    have hw_mem : w ∈ Metric.sphere (0 : ℂ) 1 ∩ U := by
      rw [← hU_eq]
      exact ⟨hw, hreg_w⟩
    have hw_cl : w ∈ closure {ζ : ℂ | ∃ m : ℕ, ζ ^ (2 ^ m) = 1} :=
      dense_dyadicRootsOfUnity_in_unitCircle hw
    obtain ⟨ζ, hζU, m, hζm⟩ := mem_closure_iff.mp hw_cl U hU_open hw_mem.2
    have hζ_sp : ζ ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
      have hpow_norm : ‖ζ‖ ^ (2 ^ m) = 1 := by rw [← norm_pow, hζm, norm_one]
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · linarith [pow_lt_one₀ (norm_nonneg ζ) hlt (by positivity : 2 ^ m ≠ 0)]
      · linarith [one_lt_pow₀ hgt (by positivity : 2 ^ m ≠ 0)]
    have hζ_reg : IsRegularBoundaryPoint lacunaryDyadicSeries 0 1 ζ := by
      have hmem : ζ ∈ Metric.sphere (0 : ℂ) 1 ∩ U := ⟨hζ_sp, hζU⟩
      rw [← hU_eq] at hmem
      exact hmem.2
    rcases hζ_reg with ⟨_, r₀, g, hr₀, hg_diff, hg_eq⟩
    have hg_cont : ContinuousAt g ζ :=
      (hg_diff.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₀))).continuousAt
    have hrad_tend : Tendsto (fun r : ℝ ↦ (r : ℂ) * ζ) (𝓝[<] 1) (𝓝 ζ) := by
      have hc : Continuous (fun r : ℝ ↦ (r : ℂ) * ζ) := Complex.continuous_ofReal.mul continuous_const
      have hct : Tendsto (fun r : ℝ ↦ (r : ℂ) * ζ) (𝓝 (1 : ℝ)) (𝓝 (((1 : ℝ) : ℂ) * ζ)) :=
        hc.continuousAt.tendsto
      simp only [Complex.ofReal_one, one_mul] at hct
      exact hct.mono_left nhdsWithin_le_nhds
    have hnorm_bdd : Tendsto (fun r : ℝ ↦ ‖g ((r : ℂ) * ζ)‖) (𝓝[<] 1) (𝓝 ‖g ζ‖) :=
      (hg_cont.tendsto.comp hrad_tend).norm
    have hev_eq : (fun r : ℝ ↦ ‖g ((r : ℂ) * ζ)‖) =ᶠ[𝓝[<] 1]
        (fun r : ℝ ↦ ‖lacunaryDyadicSeries ((r : ℂ) * ζ)‖) := by
      have hev1 : ∀ᶠ r : ℝ in 𝓝[<] 1, (r : ℂ) * ζ ∈ Metric.ball ζ r₀ :=
        hrad_tend.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₀))
      have hev2 : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
        nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)
      filter_upwards [hev1, hev2, self_mem_nhdsWithin] with r hmem_r₀ hr0 hr1
      have hr0' : 0 < r := hr0
      have hr1' : r < 1 := hr1
      have hζ_norm : ‖ζ‖ = 1 := by rwa [Metric.mem_sphere, dist_zero_right] at hζ_sp
      have hmem_1 : (r : ℂ) * ζ ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right, norm_mul, hζ_norm, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0']
        exact hr1'
      rw [hg_eq ⟨hmem_1, hmem_r₀⟩]
    have hnorm_bdd' : Tendsto (fun r : ℝ ↦ ‖lacunaryDyadicSeries ((r : ℂ) * ζ)‖)
        (𝓝[<] 1) (𝓝 ‖g ζ‖) := hnorm_bdd.congr' hev_eq
    have : (𝓝[<] (1 : ℝ)).NeBot := nhdsWithin_Iio_one_neBot
    exact not_tendsto_atTop_of_tendsto_nhds hnorm_bdd' (hdiv_root ζ m hζm)
  exact ⟨⟨hrad, fun z hz ↦ ⟨summable_pow_two_pow hz, htsum_eq z hz⟩, hdiff⟩,
    ⟨hfeq1, hfeq_m⟩, ⟨dense_dyadicRootsOfUnity_in_unitCircle, hdiv_root⟩, hnat⟩

/-- Rational-center, unit-fraction-radius ball approximation of boundary points in `ℂ`. -/
private def ratBall (t : ℚ × ℚ × ℕ) : Set ℂ :=
  Metric.ball ((t.1 : ℝ) + (t.2.1 : ℝ) * Complex.I) (1 / ((t.2.2 : ℝ) + 1))

private theorem exists_ratBall_mem_and_subset {ζ : ℂ} {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℚ × ℚ × ℕ, ζ ∈ ratBall t ∧ ratBall t ⊆ Metric.ball ζ ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
  let r : ℝ := 1 / ((k : ℝ) + 1)
  have hr_pos : 0 < r := by positivity
  have h2r_lt : 2 * r < ε := by
    dsimp [r]
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    have := (div_lt_iff₀ hε).mp hk
    linarith
  obtain ⟨q₁, hq₁_lo, hq₁_hi⟩ := exists_rat_btwn (by linarith : ζ.re - r / 2 < ζ.re + r / 2)
  obtain ⟨q₂, hq₂_lo, hq₂_hi⟩ := exists_rat_btwn (by linarith : ζ.im - r / 2 < ζ.im + r / 2)
  let c : ℂ := ((q₁ : ℝ) : ℂ) + ((q₂ : ℝ) : ℂ) * Complex.I
  have hdist_ζc : dist ζ c < r := by
    rw [dist_eq_norm]
    have hdecomp : ζ - c = ((ζ.re - (q₁ : ℝ) : ℝ) : ℂ) + ((ζ.im - (q₂ : ℝ) : ℝ) : ℂ) * Complex.I := by
      dsimp [c]
      apply Complex.ext <;> simp
    rw [hdecomp]
    calc ‖((ζ.re - (q₁ : ℝ) : ℝ) : ℂ) + ((ζ.im - (q₂ : ℝ) : ℝ) : ℂ) * Complex.I‖
        ≤ ‖((ζ.re - (q₁ : ℝ) : ℝ) : ℂ)‖ + ‖((ζ.im - (q₂ : ℝ) : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |ζ.re - (q₁ : ℝ)| + |ζ.im - (q₂ : ℝ)| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ < r / 2 + r / 2 := add_lt_add (abs_lt.mpr ⟨by linarith, by linarith⟩)
          (abs_lt.mpr ⟨by linarith, by linarith⟩)
      _ = r := by ring
  refine ⟨(q₁, q₂, k), ?_, ?_⟩
  · change dist ζ c < r
    exact hdist_ζc
  · intro w hw
    change dist w c < r at hw
    rw [Metric.mem_ball]
    calc dist w ζ ≤ dist w c + dist c ζ := dist_triangle _ _ _
      _ = dist w c + dist ζ c := by rw [dist_comm ζ c]
      _ < r + r := add_lt_add hw hdist_ζc
      _ = 2 * r := by ring
      _ < ε := h2r_lt

/-- **Rudin RCA 16.4 (Non-extendable holomorphic function on any plane region, pp. 320–321):**
Parameterized by the plane case of Theorem 15.11 (`h15_11_plane`), for every plane region
`Ω : Set ℂ` (`RudinRCA.Chapter10.IsRegion Ω`), there exists a holomorphic function `f` on `Ω`
that admits no holomorphic extension to any strictly larger plane region `Ω₁ ⊋ Ω`. -/
theorem theorem16_4_region_using_15_11
    (h15_11_plane : ∀ {Ω₀ A₀ : Set ℂ} {m₀ : ℂ → ℕ},
      IsOpen Ω₀ → A₀ ⊆ Ω₀ → (∀ z ∈ Ω₀, z ∉ closure (A₀ \ {z})) → (∀ a ∈ A₀, 0 < m₀ a) →
      ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω₀ ∧ (∀ z ∈ Ω₀, f z = 0 ↔ z ∈ A₀))
    {Ω : Set ℂ} (hΩ : RudinRCA.Chapter10.IsRegion Ω) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧
      ¬ ∃ (Ω₁ : Set ℂ) (F : ℂ → ℂ),
        RudinRCA.Chapter10.IsRegion Ω₁ ∧ Ω ⊂ Ω₁ ∧ DifferentiableOn ℂ F Ω₁ ∧ Set.EqOn f F Ω := by
  classical
  by_cases hΩ_univ : Ω = Set.univ
  · refine ⟨fun _ ↦ 0, differentiableOn_const 0, ?_⟩
    rintro ⟨Ω₁, _, _, hssub, _, _⟩
    rw [hΩ_univ] at hssub
    exact not_ssubset_of_subset (Set.subset_univ Ω₁) hssub
  · have hfr_ne : (frontier Ω).Nonempty := by
      have hssub_univ : Ω ⊂ Set.univ := Set.ssubset_univ_iff.mpr hΩ_univ
      obtain ⟨ζ, _, hζ_fr⟩ :=
        exists_mem_inter_frontier_of_ssubset_isRegion hΩ.1 hΩ.2.nonempty
          ⟨isOpen_univ, isConnected_univ⟩ hssub_univ
      exact ⟨ζ, hζ_fr⟩
    let Idx := {t : ℚ × ℚ × ℕ // (ratBall t ∩ frontier Ω).Nonempty}
    obtain ⟨ζ₀, hζ₀_fr⟩ := hfr_ne
    obtain ⟨t₀, hζ₀_t₀, _⟩ := exists_ratBall_mem_and_subset zero_lt_one (ζ := ζ₀)
    have : Nonempty Idx := ⟨⟨t₀, ⟨ζ₀, hζ₀_t₀, hζ₀_fr⟩⟩⟩
    obtain ⟨enum, henum_surj⟩ := exists_surjective_nat Idx
    have hex_an : ∀ n : ℕ, ((ratBall (enum n).1 ∩ Ω) \ RudinRCA.Chapter13.exhaustionSet Ω n).Nonempty := by
      intro n
      obtain ⟨ζ, hζB, hζ_fr⟩ := (enum n).2
      rw [frontier, hΩ.1.interior_eq] at hζ_fr
      have hK_cl : IsClosed (RudinRCA.Chapter13.exhaustionSet Ω n) :=
        (RudinRCA.Chapter13.isCompact_exhaustionSet Ω n).isClosed
      have hζ_not_K : ζ ∉ RudinRCA.Chapter13.exhaustionSet Ω n :=
        fun hmem ↦ hζ_fr.2 (RudinRCA.Chapter13.exhaustionSet_subset Ω n hmem)
      have hU_open : IsOpen (ratBall (enum n).1 \ RudinRCA.Chapter13.exhaustionSet Ω n) :=
        Metric.isOpen_ball.sdiff hK_cl
      obtain ⟨w, ⟨hwB, hw_nK⟩, hwΩ⟩ :=
        mem_closure_iff.mp hζ_fr.1 _ hU_open ⟨hζB, hζ_not_K⟩
      exact ⟨w, ⟨hwB, hwΩ⟩, hw_nK⟩
    let a : ℕ → ℂ := fun n ↦ (hex_an n).choose
    have ha_mem : ∀ n : ℕ, a n ∈ (ratBall (enum n).1 ∩ Ω) \ RudinRCA.Chapter13.exhaustionSet Ω n :=
      fun n ↦ (hex_an n).choose_spec
    let A : Set ℂ := Set.range a
    have hA_sub : A ⊆ Ω := by
      rintro _ ⟨n, rfl⟩
      exact (ha_mem n).1.2
    have hA_loc_fin : ∀ z ∈ Ω, ∃ δ > 0, Metric.ball z δ ⊆ Ω ∧ (A ∩ Metric.ball z δ).Finite := by
      intro z hz
      obtain ⟨ε, hε, hball_ε⟩ := Metric.isOpen_iff.mp hΩ.1 z hz
      let δ : ℝ := ε / 2
      have hδ_pos : 0 < δ := by positivity
      have hcb_sub : Metric.closedBall z δ ⊆ Ω :=
        (Metric.closedBall_subset_ball (by dsimp [δ]; linarith)).trans hball_ε
      obtain ⟨N, hN⟩ :=
        RudinRCA.Chapter13.exists_subset_exhaustionSet_of_isCompact hΩ.1
          (isCompact_closedBall z δ) hcb_sub
      refine ⟨δ, hδ_pos, Metric.ball_subset_closedBall.trans hcb_sub, ?_⟩
      refine ((Finset.range N).finite_toSet.image a).subset ?_
      rintro w ⟨⟨n, rfl⟩, hw_ball⟩
      refine Set.mem_image_of_mem a ?_
      rw [Finset.mem_coe, Finset.mem_range]
      by_contra! hle
      have hmemK : a n ∈ RudinRCA.Chapter13.exhaustionSet Ω n :=
        RudinRCA.Chapter13.exhaustionSet_mono Ω hle (hN (Metric.ball_subset_closedBall hw_ball))
      exact (ha_mem n).2 hmemK
    have hA_no_acc : ∀ z ∈ Ω, z ∉ closure (A \ {z}) := by
      intro z hz hcl
      obtain ⟨δ, hδ_pos, _, hfin⟩ := hA_loc_fin z hz
      let S : Set ℂ := (A \ {z}) ∩ Metric.ball z δ
      have hS_fin : S.Finite := hfin.subset (Set.inter_subset_inter_left _ Set.sdiff_subset)
      have hz_not_S : z ∉ S := fun h ↦ h.1.2 rfl
      have hV_open : IsOpen (Metric.ball z δ \ S) := Metric.isOpen_ball.sdiff hS_fin.isClosed
      obtain ⟨w, ⟨hw_ball, hw_nS⟩, hw_Az⟩ :=
        mem_closure_iff.mp hcl _ hV_open ⟨Metric.mem_ball_self hδ_pos, hz_not_S⟩
      exact hw_nS ⟨hw_Az, hw_ball⟩
    obtain ⟨f, hf_diff, hf_zero⟩ :=
      h15_11_plane hΩ.1 hA_sub hA_no_acc (m₀ := fun _ ↦ 1) (fun _ _ ↦ zero_lt_one)
    obtain ⟨z₀, hz₀Ω⟩ := hΩ.2.nonempty
    obtain ⟨δ₀, hδ₀_pos, hball₀_sub, hfin₀⟩ := hA_loc_fin z₀ hz₀Ω
    let seq : ℕ → ℂ := fun k ↦ z₀ + ((δ₀ / ((k : ℝ) + 2) : ℝ) : ℂ)
    have hseq_inj : Function.Injective seq := by
      intro k₁ k₂ heq
      dsimp [seq] at heq
      have hreal : δ₀ / ((k₁ : ℝ) + 2) = δ₀ / ((k₂ : ℝ) + 2) :=
        Complex.ofReal_injective (add_left_cancel heq)
      have hpos₁ : (0 : ℝ) < (k₁ : ℝ) + 2 := by positivity
      have hpos₂ : (0 : ℝ) < (k₂ : ℝ) + 2 := by positivity
      have h1 : δ₀ * ((k₂ : ℝ) + 2) = δ₀ * ((k₁ : ℝ) + 2) :=
        (div_eq_div_iff hpos₁.ne' hpos₂.ne').mp hreal
      have h2 : (k₁ : ℝ) = (k₂ : ℝ) := by nlinarith [hδ₀_pos]
      exact_mod_cast h2
    have hseq_ball : ∀ k : ℕ, seq k ∈ Metric.ball z₀ δ₀ := by
      intro k
      rw [Metric.mem_ball, dist_eq_norm]
      dsimp [seq]
      rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact div_lt_self hδ₀_pos (by linarith)
    have hex_nonA : ∃ w₀ ∈ Ω, w₀ ∉ A := by
      by_contra! hall_A
      have hrange_inf : (Set.range seq).Infinite := Set.infinite_range_of_injective hseq_inj
      refine hrange_inf (hfin₀.subset ?_)
      rintro _ ⟨k, rfl⟩
      exact ⟨hall_A (seq k) (hball₀_sub (hseq_ball k)), hseq_ball k⟩
    obtain ⟨w₀, hw₀Ω, hw₀_nA⟩ := hex_nonA
    have hfw₀_ne : f w₀ ≠ 0 := fun h0 ↦ hw₀_nA ((hf_zero w₀ hw₀Ω).mp h0)
    refine ⟨f, hf_diff, ?_⟩
    rintro ⟨Ω₁, F, hΩ₁, hssub, hF_diff, heq⟩
    obtain ⟨ζ, hζΩ₁, hζ_fr⟩ :=
      exists_mem_inter_frontier_of_ssubset_isRegion hΩ.1 hΩ.2.nonempty hΩ₁ hssub
    have hζ_nΩ : ζ ∉ Ω := by
      rw [frontier, hΩ.1.interior_eq] at hζ_fr
      exact hζ_fr.2
    have hζ_cl : ζ ∈ closure ({z : ℂ | F z = 0} \ {ζ}) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨t, hζ_t, ht_sub⟩ := exists_ratBall_mem_and_subset hε (ζ := ζ)
      obtain ⟨n, hn⟩ := henum_surj ⟨t, ⟨ζ, hζ_t, hζ_fr⟩⟩
      have han_t : a n ∈ ratBall t := by
        have := (ha_mem n).1.1
        rwa [hn] at this
      have han_Ω : a n ∈ Ω := (ha_mem n).1.2
      have han_F0 : F (a n) = 0 := by
        rw [← heq han_Ω]
        exact (hf_zero (a n) han_Ω).mpr ⟨n, rfl⟩
      have han_ne : a n ≠ ζ := fun h ↦ hζ_nΩ (h ▸ han_Ω)
      have han_ball : a n ∈ Metric.ball ζ ε := ht_sub han_t
      rw [Metric.mem_ball, dist_comm] at han_ball
      exact ⟨a n, ⟨han_F0, han_ne⟩, han_ball⟩
    have hF_zero :=
      (hF_diff.analyticOnNhd hΩ₁.1).eqOn_zero_of_preconnected_of_mem_closure
        hΩ₁.2.isPreconnected hζΩ₁ hζ_cl
    have hfw₀_eq : f w₀ = 0 := (heq hw₀Ω).trans (hF_zero (hssub.subset hw₀Ω))
    exact hfw₀_ne hfw₀_eq

/-!
## 16.5: Ostrowski's Overconvergence Theorem
-/

/-- The `N`-th partial sum `s_N(z) = ∑_{n=0}^N c_n z^n` of a power series `∑ c_n z^n` (Rudin 16.5). -/
def powerSeriesPartialSum (c : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), c n * z ^ n

/-- Ostrowski's auxiliary polynomial `φ(w) = (1/2) * (w^λ + w^{λ+1})` (Rudin 16.5, p. 321). -/
def ostrowskiPoly (lam : ℕ) (w : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (w ^ lam + w ^ (lam + 1))

private theorem ostrowskiPoly_one (lam : ℕ) : ostrowskiPoly lam 1 = 1 := by
  simp [ostrowskiPoly]
  norm_num

private theorem ostrowskiPoly_differentiable (lam : ℕ) : Differentiable ℂ (ostrowskiPoly lam) := by
  unfold ostrowskiPoly
  fun_prop

private theorem norm_ostrowskiPoly_lt_one {lam : ℕ} (hlam : 0 < lam) {w : ℂ}
    (hw_cb : w ∈ Metric.closedBall (0 : ℂ) 1) (hw_ne : w ≠ 1) :
    ‖ostrowskiPoly lam w‖ < 1 := by
  have hw_le : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hw_cb
  have hfac : ostrowskiPoly lam w = (1 / 2 : ℂ) * w ^ lam * (1 + w) := by
    dsimp [ostrowskiPoly]
    rw [pow_succ]
    ring
  rw [hfac, norm_mul, norm_mul, norm_pow]
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hhalf]
  rcases eq_or_lt_of_le (norm_nonneg w) with hw0 | hw_pos
  · have hwz : w = 0 := norm_eq_zero.mp hw0.symm
    rw [hwz, norm_zero, zero_pow hlam.ne']
    norm_num
  · rcases lt_or_eq_of_le hw_le with hw_lt | hw_eq1
    · have hpow_lt : ‖w‖ ^ lam < 1 := pow_lt_one₀ (norm_nonneg w) hw_lt hlam.ne'
      have h1w_lt : ‖1 + w‖ < 2 := by
        calc ‖1 + w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_add_le 1 w
          _ = 1 + ‖w‖ := by simp
          _ < 2 := by linarith
      have hprod_lt : ‖w‖ ^ lam * ‖1 + w‖ < 1 * 2 :=
        mul_lt_mul'' hpow_lt h1w_lt (pow_nonneg (norm_nonneg w) _) (norm_nonneg _)
      linarith
    · rw [hw_eq1, one_pow, mul_one]
      have hnsq_w : Complex.normSq w = 1 := by
        rw [Complex.normSq_eq_norm_sq, hw_eq1, one_pow]
      have hw_re_lt : w.re < 1 := by
        have hsum_sq : w.re * w.re + w.im * w.im = 1 := by
          simpa [Complex.normSq_apply] using hnsq_w
        have hre_le : w.re ≤ 1 := by nlinarith [mul_self_nonneg w.im]
        rcases lt_or_eq_of_le hre_le with hlt | heq
        · exact hlt
        · exfalso
          have him_sq : w.im * w.im = 0 := by nlinarith
          have him0 : w.im = 0 := mul_self_eq_zero.mp him_sq
          apply hw_ne
          apply Complex.ext
          · simpa using heq
          · simpa using him0
      have hnsq_1w : ‖1 + w‖ ^ 2 < 2 ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq]
        have h1w_calc : Complex.normSq (1 + w) = 1 + 2 * w.re + Complex.normSq w := by
          simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
            Complex.add_im, Complex.one_im, zero_add]
          ring
        rw [h1w_calc, hnsq_w]
        linarith
      have h1w_lt2 : ‖1 + w‖ < 2 := by
        nlinarith [norm_nonneg (1 + w)]
      linarith

private theorem norm_ostrowskiPoly_le_pow {lam : ℕ} (hlam : 0 < lam) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 2) :
    ‖ostrowskiPoly lam w‖ ≤ ‖w‖ ^ lam ∧ ‖ostrowskiPoly lam w‖ ≤ 1 / 2 := by
  have hfac : ostrowskiPoly lam w = (1 / 2 : ℂ) * w ^ lam * (1 + w) := by
    dsimp [ostrowskiPoly]
    rw [pow_succ]
    ring
  have h1w : ‖1 + w‖ ≤ 3 / 2 := by
    calc ‖1 + w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_add_le 1 w
      _ = 1 + ‖w‖ := by simp
      _ ≤ 3 / 2 := by linarith
  have hle1 : ‖ostrowskiPoly lam w‖ ≤ ‖w‖ ^ lam := by
    rw [hfac, norm_mul, norm_mul, norm_pow]
    have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [hhalf]
    have hpow_nn : 0 ≤ ‖w‖ ^ lam := pow_nonneg (norm_nonneg w) lam
    nlinarith
  refine ⟨hle1, hle1.trans ?_⟩
  calc ‖w‖ ^ lam ≤ (1 / 2 : ℝ) ^ lam := pow_le_pow_left₀ (norm_nonneg w) hw lam
    _ ≤ (1 / 2 : ℝ) ^ 1 := pow_le_pow_of_le_one (by positivity) (by norm_num) hlam
    _ = 1 / 2 := pow_one _

private theorem deriv_ostrowskiPoly_one_ne_zero {lam : ℕ} :
    deriv (ostrowskiPoly lam) 1 ≠ 0 := by
  have hd1 : HasDerivAt (fun w : ℂ ↦ w ^ lam) ((lam : ℂ) * (1 : ℂ) ^ (lam - 1)) 1 :=
    hasDerivAt_pow lam (1 : ℂ)
  have hd2 : HasDerivAt (fun w : ℂ ↦ w ^ (lam + 1)) (((lam + 1 : ℕ) : ℂ) * (1 : ℂ) ^ lam) 1 :=
    hasDerivAt_pow (lam + 1) (1 : ℂ)
  have hd : HasDerivAt (ostrowskiPoly lam)
      ((1 / 2 : ℂ) * ((lam : ℂ) * (1 : ℂ) ^ (lam - 1) + ((lam + 1 : ℕ) : ℂ) * (1 : ℂ) ^ lam)) 1 := by
    unfold ostrowskiPoly
    exact (hd1.add hd2).const_mul (1 / 2 : ℂ)
  rw [hd.deriv]
  simp only [one_pow, mul_one]
  have hrew : (1 / 2 : ℂ) * ((lam : ℂ) + ((lam + 1 : ℕ) : ℂ)) =
      (1 / 2 : ℂ) * ((2 * lam + 1 : ℕ) : ℂ) := by
    push_cast
    ring
  rw [hrew]
  intro h0
  rcases mul_eq_zero.mp h0 with h1 | h2
  · norm_num at h1
  · exact absurd (Nat.cast_eq_zero.mp h2) (by omega)

/-- If a polynomial `∑_{m < K} γ_m r^m` is bounded by `C * r^K` for all `r ∈ (0, 1/2)`, then all
coefficients `γ_m` (`m < K`) vanish. -/
private theorem poly_coeff_zero_of_norm_le_pow {K : ℕ} {γ : ℕ → ℂ} {C : ℝ}
    (hbound : ∀ r : ℝ, 0 < r → r < 1 / 2 →
      ‖∑ m ∈ Finset.range K, γ m * (r : ℂ) ^ m‖ ≤ C * r ^ K) :
    ∀ m < K, γ m = 0 := by
  intro m hmK
  induction m using Nat.strong_induction_on with
  | h m ih =>
    let C' : ℝ := max C 0 + ∑ i ∈ Finset.Ico (m + 1) K, ‖γ i‖
    have hC'_nonneg : 0 ≤ C' := by
      dsimp [C']
      exact add_nonneg (le_max_right C 0) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
    have hγm_bound : ∀ r : ℝ, 0 < r → r < 1 / 2 → ‖γ m‖ ≤ C' * r := by
      intro r hr0 hr_half
      have hsplit1 : (∑ i ∈ Finset.range K, γ i * (r : ℂ) ^ i) =
          (∑ i ∈ Finset.range (m + 1), γ i * (r : ℂ) ^ i) +
            ∑ i ∈ Finset.Ico (m + 1) K, γ i * (r : ℂ) ^ i :=
        (Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hmK)).symm
      have hinit : (∑ i ∈ Finset.range (m + 1), γ i * (r : ℂ) ^ i) = γ m * (r : ℂ) ^ m := by
        rw [Finset.sum_range_succ]
        have hzero : (∑ i ∈ Finset.range m, γ i * (r : ℂ) ^ i) = 0 := by
          refine Finset.sum_eq_zero fun i hi ↦ ?_
          have hi_lt : i < m := Finset.mem_range.mp hi
          rw [ih i hi_lt (hi_lt.trans hmK), zero_mul]
        rw [hzero, zero_add]
      have hIsol : γ m * (r : ℂ) ^ m =
          (∑ i ∈ Finset.range K, γ i * (r : ℂ) ^ i) -
            ∑ i ∈ Finset.Ico (m + 1) K, γ i * (r : ℂ) ^ i := by
        rw [hsplit1, hinit]
        ring
      have hnorm_lhs : ‖γ m * (r : ℂ) ^ m‖ = ‖γ m‖ * r ^ m := by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      have hnorm_tot : ‖∑ i ∈ Finset.range K, γ i * (r : ℂ) ^ i‖ ≤ max C 0 * r ^ (m + 1) := by
        calc ‖∑ i ∈ Finset.range K, γ i * (r : ℂ) ^ i‖
            ≤ C * r ^ K := hbound r hr0 hr_half
          _ ≤ max C 0 * r ^ K :=
              mul_le_mul_of_nonneg_right (le_max_left C 0) (pow_nonneg hr0.le K)
          _ ≤ max C 0 * r ^ (m + 1) :=
              mul_le_mul_of_nonneg_left
                (pow_le_pow_of_le_one hr0.le (by linarith) (Nat.succ_le_of_lt hmK))
                (le_max_right C 0)
      have hnorm_tail : ‖∑ i ∈ Finset.Ico (m + 1) K, γ i * (r : ℂ) ^ i‖ ≤
          (∑ i ∈ Finset.Ico (m + 1) K, ‖γ i‖) * r ^ (m + 1) := by
        calc ‖∑ i ∈ Finset.Ico (m + 1) K, γ i * (r : ℂ) ^ i‖
            ≤ ∑ i ∈ Finset.Ico (m + 1) K, ‖γ i * (r : ℂ) ^ i‖ := norm_sum_le _ _
          _ = ∑ i ∈ Finset.Ico (m + 1) K, ‖γ i‖ * r ^ i := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
          _ ≤ ∑ i ∈ Finset.Ico (m + 1) K, ‖γ i‖ * r ^ (m + 1) := by
              refine Finset.sum_le_sum fun i hi ↦ ?_
              have hmi : m + 1 ≤ i := (Finset.mem_Ico.mp hi).1
              exact mul_le_mul_of_nonneg_left
                (pow_le_pow_of_le_one hr0.le (by linarith) hmi) (norm_nonneg _)
          _ = (∑ i ∈ Finset.Ico (m + 1) K, ‖γ i‖) * r ^ (m + 1) := (Finset.sum_mul _ _ _).symm
      have hmul_bound : ‖γ m‖ * r ^ m ≤ (C' * r) * r ^ m := by
        rw [← hnorm_lhs, hIsol]
        calc ‖(∑ i ∈ Finset.range K, γ i * (r : ℂ) ^ i) -
                ∑ i ∈ Finset.Ico (m + 1) K, γ i * (r : ℂ) ^ i‖
            ≤ ‖∑ i ∈ Finset.range K, γ i * (r : ℂ) ^ i‖ +
                ‖∑ i ∈ Finset.Ico (m + 1) K, γ i * (r : ℂ) ^ i‖ := norm_sub_le _ _
          _ ≤ max C 0 * r ^ (m + 1) + (∑ i ∈ Finset.Ico (m + 1) K, ‖γ i‖) * r ^ (m + 1) :=
              add_le_add hnorm_tot hnorm_tail
          _ = (C' * r) * r ^ m := by dsimp [C']; rw [pow_succ']; ring
      exact le_of_mul_le_mul_right hmul_bound (pow_pos hr0 m)
    by_contra hne
    have hpos : 0 < ‖γ m‖ := norm_pos_iff.mpr hne
    let r₀ : ℝ := min (1 / 4) (‖γ m‖ / (2 * (C' + 1)))
    have hr₀_pos : 0 < r₀ := lt_min (by positivity) (div_pos hpos (by positivity))
    have hr₀_half : r₀ < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
    have hle := hγm_bound r₀ hr₀_pos hr₀_half
    have hr₀_le : r₀ ≤ ‖γ m‖ / (2 * (C' + 1)) := min_le_right _ _
    have hstrict : C' * r₀ < ‖γ m‖ := by
      calc C' * r₀ ≤ C' * (‖γ m‖ / (2 * (C' + 1))) := mul_le_mul_of_nonneg_left hr₀_le hC'_nonneg
        _ < (C' + 1) * (‖γ m‖ / (2 * (C' + 1))) :=
            mul_lt_mul_of_pos_right (by linarith) (div_pos hpos (by positivity))
        _ = ‖γ m‖ / 2 := by
            have hne_c : C' + 1 ≠ 0 := by positivity
            field_simp [hne_c]
        _ < ‖γ m‖ := by linarith
    linarith

/-- Algebraic partial-sum identity at the heart of Ostrowski's proof: if `G(u) = ∑' m, b_m u^m`
agrees with `∑' n, c_n (φ u)^n` for `u ∈ (0, 1/2)` and `c_n = 0` for `p_k < n < q_k` with
`lam * q_k > (lam + 1) * p_k`, then for every `w : ℂ`,
`∑_{m=0}^{(lam+1) p_k} b_m w^m = s_{p_k}(φ w)`. -/
private theorem ostrowski_partial_ident {lam : ℕ} (hlam : 0 < lam)
    {p q : ℕ → ℕ} (hp_pos : ∀ k, 0 < p k)
    (hgap : ∀ k, lam * q k > (lam + 1) * p k)
    {c b : ℕ → ℂ} (hc_rad : HasRadiusOfConvergenceOne c)
    (hc_gap : ∀ k n, p k < n → n < q k → c n = 0)
    {G : ℂ → ℂ} {r₁ : ℝ} (hr₁_gt_half : 1 / 2 < r₁)
    (hsum_b_r₁ : Summable (fun m : ℕ ↦ ‖b m‖ * r₁ ^ m))
    (hG_b_real : ∀ r : ℝ, 0 < r → r < 1 / 2 → HasSum (fun m : ℕ ↦ b m * (r : ℂ) ^ m) (G (r : ℂ)))
    (hG_c_real : ∀ r : ℝ, 0 < r → r < 1 / 2 →
      G (r : ℂ) = ∑' n : ℕ, c n * (ostrowskiPoly lam (r : ℂ)) ^ n)
    (k : ℕ) (w : ℂ) :
    (∑ m ∈ Finset.range ((lam + 1) * p k + 1), b m * w ^ m) =
      powerSeriesPartialSum c (p k) (ostrowskiPoly lam w) := by
  have hr₁_pos : 0 < r₁ := by linarith
  have hsum_c_half : Summable (fun n : ℕ ↦ ‖c n‖ * (1 / 2 : ℝ) ^ n) := by
    have hmem : ((1 / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      norm_num
    have hs := summable_norm_of_hasRadiusOfConvergenceOne hc_rad hmem
    refine hs.congr fun n ↦ ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  let φP : Polynomial ℂ :=
    Polynomial.C (1 / 2 : ℂ) * (Polynomial.X ^ lam + Polynomial.X ^ (lam + 1))
  have hφP_eval : ∀ u : ℂ, φP.eval u = ostrowskiPoly lam u := by
    intro u
    simp [φP, ostrowskiPoly]
  have hφP_deg : φP.natDegree ≤ lam + 1 := by
    calc φP.natDegree
        ≤ (Polynomial.X ^ lam + Polynomial.X ^ (lam + 1) : Polynomial ℂ).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
      _ ≤ max (Polynomial.X ^ lam : Polynomial ℂ).natDegree
            (Polynomial.X ^ (lam + 1) : Polynomial ℂ).natDegree :=
          Polynomial.natDegree_add_le _ _
      _ ≤ max lam (lam + 1) :=
          max_le_max (Polynomial.natDegree_X_pow_le lam) (Polynomial.natDegree_X_pow_le (lam + 1))
      _ = lam + 1 := by omega
  set Mk : ℕ := (lam + 1) * p k
  let Pk : Polynomial ℂ := ∑ n ∈ Finset.range (p k + 1), Polynomial.C (c n) * φP ^ n
  have hPk_eval : ∀ u : ℂ, Pk.eval u = powerSeriesPartialSum c (p k) (ostrowskiPoly lam u) := by
    intro u
    dsimp [Pk, powerSeriesPartialSum]
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    simp [hφP_eval]
  have hPk_deg : Pk.natDegree ≤ Mk := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun n hn ↦ ?_
    have hn_le : n ≤ p k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    calc (Polynomial.C (c n) * φP ^ n).natDegree
        ≤ (φP ^ n).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ ≤ n * φP.natDegree := Polynomial.natDegree_pow_le
      _ ≤ p k * (lam + 1) := Nat.mul_le_mul hn_le hφP_deg
      _ = Mk := mul_comm _ _
  have hPk_sum : ∀ u : ℂ, Pk.eval u = ∑ m ∈ Finset.range (Mk + 1), Pk.coeff m * u ^ m :=
    fun u ↦ Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hPk_deg) u
  have hp_lt_q : p k < q k := by
    have hg := hgap k
    have hp0 := hp_pos k
    have : lam * p k < lam * q k := by
      calc lam * p k < lam * p k + p k := Nat.lt_add_of_pos_right hp0
        _ = (lam + 1) * p k := by ring
        _ < lam * q k := hg
    exact (Nat.mul_lt_mul_left hlam).mp this
  have hsum_c_shift : Summable (fun j : ℕ ↦ ‖c (j + q k)‖ * (1 / 2 : ℝ) ^ j) := by
    have hs : Summable (fun j : ℕ ↦ ‖c (j + q k)‖ * (1 / 2 : ℝ) ^ (j + q k)) :=
      (_root_.summable_nat_add_iff (q k) (f := fun n ↦ ‖c n‖ * (1 / 2 : ℝ) ^ n)).mpr hsum_c_half
    have hs' := hs.mul_right ((2 : ℝ) ^ (q k))
    refine hs'.congr fun j ↦ ?_
    rw [pow_add]
    have hcancel : (1 / 2 : ℝ) ^ (q k) * (2 : ℝ) ^ (q k) = 1 := by
      rw [← mul_pow]
      norm_num
    calc ‖c (j + q k)‖ * ((1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ q k) * (2 : ℝ) ^ q k
        = ‖c (j + q k)‖ * (1 / 2 : ℝ) ^ j * ((1 / 2 : ℝ) ^ q k * (2 : ℝ) ^ q k) := by ring
      _ = ‖c (j + q k)‖ * (1 / 2 : ℝ) ^ j := by rw [hcancel, mul_one]
  have hsum_b_shift : Summable (fun j : ℕ ↦ ‖b (j + (Mk + 1))‖ * r₁ ^ j) := by
    have hs : Summable (fun j : ℕ ↦ ‖b (j + (Mk + 1))‖ * r₁ ^ (j + (Mk + 1))) :=
      (_root_.summable_nat_add_iff (Mk + 1) (f := fun m ↦ ‖b m‖ * r₁ ^ m)).mpr hsum_b_r₁
    have hs' := hs.mul_right ((r₁ ^ (Mk + 1))⁻¹)
    refine hs'.congr fun j ↦ ?_
    rw [pow_add]
    have hne : r₁ ^ (Mk + 1) ≠ 0 := pow_ne_zero _ hr₁_pos.ne'
    calc ‖b (j + (Mk + 1))‖ * (r₁ ^ j * r₁ ^ (Mk + 1)) * (r₁ ^ (Mk + 1))⁻¹
        = ‖b (j + (Mk + 1))‖ * r₁ ^ j * (r₁ ^ (Mk + 1) * (r₁ ^ (Mk + 1))⁻¹) := by ring
      _ = ‖b (j + (Mk + 1))‖ * r₁ ^ j := by rw [mul_inv_cancel₀ hne, mul_one]
  let Bk : ℝ := ∑' j : ℕ, ‖c (j + q k)‖ * (1 / 2 : ℝ) ^ j
  let Dk : ℝ := ∑' j : ℕ, ‖b (j + (Mk + 1))‖ * r₁ ^ j
  have hcoeff_eq : ∀ m < Mk + 1, Pk.coeff m - b m = 0 := by
    apply poly_coeff_zero_of_norm_le_pow (C := Bk + Dk)
    intro r hr0 hr_half
    have hu_norm : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    have hu_le_half : ‖(r : ℂ)‖ ≤ 1 / 2 := by linarith
    obtain ⟨hφu_pow, hφu_half⟩ := norm_ostrowskiPoly_le_pow hlam hu_le_half
    have hφu_ball1 : ostrowskiPoly lam (r : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hφu_half.trans_lt (by norm_num)
    have hGu_eq : G (r : ℂ) = ∑' n : ℕ, c n * (ostrowskiPoly lam (r : ℂ)) ^ n :=
      hG_c_real r hr0 hr_half
    have hsplit_c :=
      (summable_of_hasRadiusOfConvergenceOne hc_rad hφu_ball1).sum_add_tsum_nat_add (q k)
    have hsum_qk : (∑ n ∈ Finset.range (q k), c n * (ostrowskiPoly lam (r : ℂ)) ^ n) =
        Pk.eval (r : ℂ) := by
      rw [hPk_eval]
      dsimp [powerSeriesPartialSum]
      symm
      refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hp_lt_q)) fun n hn_qk hn_pk ↦ ?_
      have hlt_qk : n < q k := Finset.mem_range.mp hn_qk
      have hgt_pk : p k < n := by
        have : ¬ n < p k + 1 := Finset.mem_range.not.mp hn_pk
        omega
      rw [hc_gap k n hgt_pk hlt_qk, zero_mul]
    have hGu_minus_Pk : G (r : ℂ) - Pk.eval (r : ℂ) =
        ∑' j : ℕ, c (j + q k) * (ostrowskiPoly lam (r : ℂ)) ^ (j + q k) := by
      rw [hGu_eq, ← hsplit_c, hsum_qk]
      ring
    have hsum_maj1 : Summable (fun j : ℕ ↦ ‖c (j + q k) * (ostrowskiPoly lam (r : ℂ)) ^ j‖) := by
      refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun j ↦ ?_) hsum_c_shift
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hφu_half j) (norm_nonneg _)
    have hnorm_diff1 : ‖G (r : ℂ) - Pk.eval (r : ℂ)‖ ≤ Bk * r ^ (Mk + 1) := by
      rw [hGu_minus_Pk]
      have hfac_tsum : (∑' j : ℕ, c (j + q k) * (ostrowskiPoly lam (r : ℂ)) ^ (j + q k)) =
          (ostrowskiPoly lam (r : ℂ)) ^ (q k) *
            ∑' j : ℕ, c (j + q k) * (ostrowskiPoly lam (r : ℂ)) ^ j := by
        rw [← tsum_mul_left]
        refine tsum_congr fun j ↦ ?_
        rw [pow_add]
        ring
      rw [hfac_tsum, norm_mul, norm_pow]
      have htsum_le : ‖∑' j : ℕ, c (j + q k) * (ostrowskiPoly lam (r : ℂ)) ^ j‖ ≤ Bk := by
        refine (norm_tsum_le_tsum_norm hsum_maj1).trans ?_
        refine Summable.tsum_le_tsum (fun j ↦ ?_) hsum_maj1 hsum_c_shift
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hφu_half j) (norm_nonneg _)
      have hpow_qk : ‖ostrowskiPoly lam (r : ℂ)‖ ^ (q k) ≤ r ^ (Mk + 1) := by
        calc ‖ostrowskiPoly lam (r : ℂ)‖ ^ (q k) ≤ (‖(r : ℂ)‖ ^ lam) ^ (q k) :=
              pow_le_pow_left₀ (norm_nonneg _) hφu_pow (q k)
          _ = r ^ (lam * q k) := by rw [← pow_mul, hu_norm]
          _ ≤ r ^ (Mk + 1) :=
              pow_le_pow_of_le_one hr0.le (by linarith) (Nat.succ_le_of_lt (hgap k))
      calc ‖ostrowskiPoly lam (r : ℂ)‖ ^ q k *
              ‖∑' j : ℕ, c (j + q k) * (ostrowskiPoly lam (r : ℂ)) ^ j‖
          ≤ r ^ (Mk + 1) * Bk :=
            mul_le_mul hpow_qk htsum_le (norm_nonneg _) (pow_nonneg hr0.le _)
        _ = Bk * r ^ (Mk + 1) := mul_comm _ _
    have hu_le_r₁ : ‖(r : ℂ)‖ ≤ r₁ := by rw [hu_norm]; linarith
    have hhas_b := hG_b_real r hr0 hr_half
    have hsplit_b := hhas_b.summable.sum_add_tsum_nat_add (Mk + 1)
    have hGu_b : G (r : ℂ) = ∑' m : ℕ, b m * (r : ℂ) ^ m := hhas_b.tsum_eq.symm
    have hGu_minus_b : G (r : ℂ) - (∑ m ∈ Finset.range (Mk + 1), b m * (r : ℂ) ^ m) =
        (r : ℂ) ^ (Mk + 1) * ∑' j : ℕ, b (j + (Mk + 1)) * (r : ℂ) ^ j := by
      rw [hGu_b, ← hsplit_b]
      have hfac_b : (∑' j : ℕ, b (j + (Mk + 1)) * (r : ℂ) ^ (j + (Mk + 1))) =
          (r : ℂ) ^ (Mk + 1) * ∑' j : ℕ, b (j + (Mk + 1)) * (r : ℂ) ^ j := by
        rw [← tsum_mul_left]
        refine tsum_congr fun j ↦ ?_
        rw [pow_add]
        ring
      rw [← hfac_b]
      ring
    have hsum_maj2 : Summable (fun j : ℕ ↦ ‖b (j + (Mk + 1)) * (r : ℂ) ^ j‖) := by
      refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun j ↦ ?_) hsum_b_shift
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hu_le_r₁ j) (norm_nonneg _)
    have hnorm_diff2 : ‖G (r : ℂ) - ∑ m ∈ Finset.range (Mk + 1), b m * (r : ℂ) ^ m‖ ≤
        Dk * r ^ (Mk + 1) := by
      rw [hGu_minus_b, norm_mul, norm_pow, hu_norm]
      have htsum_le2 : ‖∑' j : ℕ, b (j + (Mk + 1)) * (r : ℂ) ^ j‖ ≤ Dk := by
        refine (norm_tsum_le_tsum_norm hsum_maj2).trans ?_
        refine Summable.tsum_le_tsum (fun j ↦ ?_) hsum_maj2 hsum_b_shift
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hu_le_r₁ j) (norm_nonneg _)
      calc r ^ (Mk + 1) * ‖∑' j : ℕ, b (j + (Mk + 1)) * (r : ℂ) ^ j‖
          ≤ r ^ (Mk + 1) * Dk :=
            mul_le_mul_of_nonneg_left htsum_le2 (pow_nonneg hr0.le _)
        _ = Dk * r ^ (Mk + 1) := mul_comm _ _
    have hpoly_diff : (∑ m ∈ Finset.range (Mk + 1), (Pk.coeff m - b m) * (r : ℂ) ^ m) =
        (G (r : ℂ) - ∑ m ∈ Finset.range (Mk + 1), b m * (r : ℂ) ^ m) -
          (G (r : ℂ) - Pk.eval (r : ℂ)) := by
      rw [hPk_sum (r : ℂ)]
      have hsub_sum : (∑ m ∈ Finset.range (Mk + 1), (Pk.coeff m - b m) * (r : ℂ) ^ m) =
          (∑ m ∈ Finset.range (Mk + 1), Pk.coeff m * (r : ℂ) ^ m) -
            ∑ m ∈ Finset.range (Mk + 1), b m * (r : ℂ) ^ m := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun m _ ↦ sub_mul _ _ _
      rw [hsub_sum]
      ring
    rw [hpoly_diff]
    calc ‖(G (r : ℂ) - ∑ m ∈ Finset.range (Mk + 1), b m * (r : ℂ) ^ m) -
            (G (r : ℂ) - Pk.eval (r : ℂ))‖
        ≤ ‖G (r : ℂ) - ∑ m ∈ Finset.range (Mk + 1), b m * (r : ℂ) ^ m‖ +
            ‖G (r : ℂ) - Pk.eval (r : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ Dk * r ^ (Mk + 1) + Bk * r ^ (Mk + 1) := add_le_add hnorm_diff2 hnorm_diff1
      _ = (Bk + Dk) * r ^ (Mk + 1) := by ring
  rw [← hPk_eval w, hPk_sum w]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have h0 := hcoeff_eq m (Finset.mem_range.mp hm)
  rw [sub_eq_zero.mp h0]

/-- The `ζ = 1` case of Ostrowski's Overconvergence Theorem (Rudin 16.5). -/
private theorem theorem16_5_at_one {lam : ℕ} (hlam : 0 < lam)
    {p q : ℕ → ℕ} (hp_mono : StrictMono p) (hp_pos : ∀ k, 0 < p k)
    (hgap : ∀ k, lam * q k > (lam + 1) * p k)
    {c : ℕ → ℂ} (hc_rad : HasRadiusOfConvergenceOne c)
    (hc_gap : ∀ k n, p k < n → n < q k → c n = 0)
    {f g₀ : ℂ → ℂ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hf : Set.EqOn f (fun z ↦ ∑' n : ℕ, c n * z ^ n) (Metric.ball (0 : ℂ) 1))
    (hg₀_diff : DifferentiableOn ℂ g₀ (Metric.ball (1 : ℂ) r₀))
    (hg₀_eq : Set.EqOn f g₀ (Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) r₀)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r₀ ∧
      TendstoUniformlyOn (fun k z ↦ powerSeriesPartialSum c (p k) z) g₀
        Filter.atTop (Metric.ball (1 : ℂ) ρ) := by
  classical
  have hf_diff : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) := (theorem16_2 hc_rad hf).1
  let Ω : Set ℂ := Metric.ball (0 : ℂ) 1 ∪ Metric.ball (1 : ℂ) r₀
  have hΩ_open : IsOpen Ω := Metric.isOpen_ball.union Metric.isOpen_ball
  obtain ⟨F, hF_eq_f, hF_eq_g₀, hF_diff⟩ :
      ∃ F : ℂ → ℂ, Set.EqOn F f (Metric.ball (0 : ℂ) 1) ∧
        Set.EqOn F g₀ (Metric.ball (1 : ℂ) r₀) ∧ DifferentiableOn ℂ F Ω := by
    let F₀ : ℂ → ℂ := fun z ↦ if z ∈ Metric.ball (0 : ℂ) 1 then f z else g₀ z
    have h1 : Set.EqOn F₀ f (Metric.ball (0 : ℂ) 1) := fun z hz ↦
      ite_eq_left_iff.mpr fun h ↦ (h hz).elim
    have h2 : Set.EqOn F₀ g₀ (Metric.ball (1 : ℂ) r₀) := by
      intro z hz
      dsimp [F₀]
      split_ifs with hzb
      · exact hg₀_eq ⟨hzb, hz⟩
      · rfl
    have h3 : DifferentiableOn ℂ F₀ Ω := by
      intro z hz
      rcases hz with hz1 | hz2
      · have hd : DifferentiableAt ℂ f z :=
          hf_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hz1)
        have hev : F₀ =ᶠ[𝓝 z] f :=
          Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz1) h1
        exact (hev.differentiableAt_iff.mpr hd).differentiableWithinAt
      · have hd : DifferentiableAt ℂ g₀ z :=
          hg₀_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hz2)
        have hev : F₀ =ᶠ[𝓝 z] g₀ :=
          Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz2) h2
        exact (hev.differentiableAt_iff.mpr hd).differentiableWithinAt
    exact ⟨F₀, h1, h2, h3⟩
  let φ : ℂ → ℂ := ostrowskiPoly lam
  have hφ_diff : Differentiable ℂ φ := ostrowskiPoly_differentiable lam
  have hcb_pre : Metric.closedBall (0 : ℂ) 1 ⊆ φ ⁻¹' Ω := by
    intro w hw
    rw [Set.mem_preimage]
    by_cases hw1 : w = 1
    · rw [hw1]
      right
      have hφ1 : φ 1 = (1 : ℂ) := ostrowskiPoly_one lam
      rw [hφ1]
      exact Metric.mem_ball_self hr₀
    · left
      rw [Metric.mem_ball, dist_zero_right]
      exact norm_ostrowskiPoly_lt_one hlam hw hw1
  obtain ⟨δ, hδ_pos, hball_pre⟩ :=
    exists_ball_subset_of_closedBall_subset_isOpen zero_le_one
      (hΩ_open.preimage hφ_diff.continuous) hcb_pre
  let ε : ℝ := δ / 3
  have hε_pos : 0 < ε := by dsimp [ε]; linarith
  have hball_2ε_pre : Metric.ball (0 : ℂ) (1 + 2 * ε) ⊆ φ ⁻¹' Ω :=
    (Metric.ball_subset_ball (by dsimp [ε]; linarith)).trans hball_pre
  let G : ℂ → ℂ := F ∘ φ
  have hG_diff : DifferentiableOn ℂ G (Metric.ball (0 : ℂ) (1 + 2 * ε)) :=
    hF_diff.comp hφ_diff.differentiableOn fun w hw ↦ hball_2ε_pre hw
  obtain ⟨b, hG_hasSum⟩ :
      ∃ b : ℕ → ℂ, ∀ w ∈ Metric.ball (0 : ℂ) (1 + 2 * ε),
        HasSum (fun m : ℕ ↦ b m * w ^ m) (G w) := by
    refine ⟨fun m ↦ (m.factorial : ℂ)⁻¹ * iteratedDeriv m G 0, fun w hw ↦ ?_⟩
    have h := Complex.hasSum_taylorSeries_on_ball hG_diff hw
    refine h.congr_fun fun m ↦ ?_
    simp only [sub_zero, smul_eq_mul]
    ring
  -- Uniform convergence of Taylor partial sums of `G` on `Metric.closedBall 0 (1 + ε)`.
  let r₁ : ℝ := 1 + ε
  let r₂ : ℝ := 1 + 3 * ε / 2
  have hr₁_pos : 0 < r₁ := by positivity
  have hr₂_pos : 0 < r₂ := by positivity
  let r₁_nn : ℝ≥0 := ⟨r₁, hr₁_pos.le⟩
  let r₂_nn : ℝ≥0 := ⟨r₂, hr₂_pos.le⟩
  have hr₂_mem : (r₂ : ℂ) ∈ Metric.ball (0 : ℂ) (1 + 2 * ε) := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₂_pos]
    dsimp [r₂]; linarith
  let qb := FormalMultilinearSeries.ofScalars ℂ b
  have hqb_rad : (r₂_nn : ℝ≥0∞) ≤ qb.radius := by
    have ht0 := (hG_hasSum (r₂ : ℂ) hr₂_mem).summable.tendsto_atTop_zero.norm
    simp only [norm_zero] at ht0
    have ht0' : Tendsto (fun m : ℕ ↦ ‖qb m‖ * (r₂_nn : ℝ) ^ m) atTop (𝓝 0) := by
      refine ht0.congr fun m ↦ ?_
      change ‖b m * (r₂ : ℂ) ^ m‖ = ‖qb m‖ * r₂ ^ m
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₂_pos,
        ← FormalMultilinearSeries.ofScalars_norm ℂ b m]
    exact qb.le_radius_of_tendsto ht0'
  have hr₁_lt_qb : (r₁_nn : ℝ≥0∞) < qb.radius := by
    have hlt : (r₁_nn : ℝ≥0∞) < (r₂_nn : ℝ≥0∞) := by
      exact_mod_cast (show r₁ < r₂ by dsimp [r₁, r₂]; linarith)
    exact hlt.trans_le hqb_rad
  have hsum_b_r₁ : Summable (fun m : ℕ ↦ ‖b m‖ * r₁ ^ m) := by
    have hs := qb.summable_norm_mul_pow hr₁_lt_qb
    refine hs.congr fun m ↦ ?_
    rw [FormalMultilinearSeries.ofScalars_norm]
    rfl
  have hunif_G : TendstoUniformlyOn (fun M w ↦ ∑ m ∈ Finset.range M, b m * w ^ m)
      G Filter.atTop (Metric.closedBall (0 : ℂ) r₁) := by
    have hM := tendstoUniformlyOn_tsum_nat (f := fun m w ↦ b m * w ^ m) hsum_b_r₁
      (s := Metric.closedBall (0 : ℂ) r₁) (fun m w hw ↦ by
        have hwn : ‖w‖ ≤ r₁ := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hwn m) (norm_nonneg _))
    refine hM.congr_right fun w hw ↦ ?_
    have hw_ball : w ∈ Metric.ball (0 : ℂ) (1 + 2 * ε) :=
      Metric.closedBall_subset_ball (by dsimp [r₁]; linarith) hw
    exact (hG_hasSum w hw_ball).tsum_eq
  have hpartial_ident : ∀ (k : ℕ) (w : ℂ),
      (∑ m ∈ Finset.range ((lam + 1) * p k + 1), b m * w ^ m) =
        powerSeriesPartialSum c (p k) (φ w) := by
    intro k w
    refine ostrowski_partial_ident (G := G) hlam hp_pos hgap hc_rad hc_gap
      (show 1 / 2 < r₁ by dsimp [r₁]; linarith) hsum_b_r₁ (fun r hr0 hr_half ↦ ?_)
      (fun r hr0 hr_half ↦ ?_) k w
    · refine hG_hasSum (r : ℂ) ?_
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      linarith
    · have hu_le : ‖(r : ℂ)‖ ≤ 1 / 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
        linarith
      have hφ_ball : φ (r : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right]
        exact (norm_ostrowskiPoly_le_pow hlam hu_le).2.trans_lt (by norm_num)
      change F (φ (r : ℂ)) = _
      rw [hF_eq_f hφ_ball, hf hφ_ball]
  -- Extract subsequence `k ↦ (lam + 1) * p k + 1` and restrict to `Metric.ball 1 ε₁`.
  have hidx_top : Tendsto (fun k : ℕ ↦ (lam + 1) * p k + 1) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    have hkp : k ≤ p k := hp_mono.id_le k
    calc N ≤ k := hk
      _ ≤ 1 * p k := by omega
      _ ≤ (lam + 1) * p k + 1 := by nlinarith
  have hunif_sub : TendstoUniformlyOn (fun k w ↦ powerSeriesPartialSum c (p k) (φ w))
      G Filter.atTop (Metric.closedBall (0 : ℂ) r₁) := by
    rw [Metric.tendstoUniformlyOn_iff] at hunif_G ⊢
    intro ε_u hε_u
    filter_upwards [hidx_top.eventually (hunif_G ε_u hε_u)] with k hk w hw
    simpa [hpartial_ident k w] using hk w hw
  -- Open mapping on `Metric.ball 1 ε₁` where `φ '' Metric.ball 1 ε₁ ⊆ Metric.ball 1 r₀`.
  let V₀ : Set ℂ := Metric.ball (1 : ℂ) ε ∩ φ ⁻¹' Metric.ball (1 : ℂ) r₀
  have hV₀_open : IsOpen V₀ :=
    Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage hφ_diff.continuous)
  have h1_V₀ : (1 : ℂ) ∈ V₀ := by
    refine ⟨Metric.mem_ball_self hε_pos, ?_⟩
    rw [Set.mem_preimage]
    have hφ1 : φ 1 = (1 : ℂ) := ostrowskiPoly_one lam
    rw [hφ1]
    exact Metric.mem_ball_self hr₀
  obtain ⟨ε₁, hε₁_pos, hball_ε₁_V₀⟩ := Metric.isOpen_iff.mp hV₀_open 1 h1_V₀
  have hball_ε₁_cb : Metric.ball (1 : ℂ) ε₁ ⊆ Metric.closedBall (0 : ℂ) r₁ := by
    intro w hw
    have hw_ε : w ∈ Metric.ball (1 : ℂ) ε := (hball_ε₁_V₀ hw).1
    rw [Metric.mem_ball, dist_eq_norm] at hw_ε
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖w‖ = ‖(w - 1) + 1‖ := by ring_nf
      _ ≤ ‖w - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ ε + 1 := by simp [hw_ε.le]
      _ = r₁ := by dsimp [r₁]; ring
  have hreg_ε₁ : RudinRCA.Chapter10.IsRegion (Metric.ball (1 : ℂ) ε₁) :=
    ⟨Metric.isOpen_ball, isConnected_ball hε₁_pos⟩
  have hφ_holo : RudinRCA.Chapter10.HolomorphicOn φ (Metric.ball (1 : ℂ) ε₁) :=
    fun z _ ↦ hφ_diff.differentiableAt
  have hφ_nonconst : ¬ ∃ w₀ : ℂ, ∀ z ∈ Metric.ball (1 : ℂ) ε₁, φ z = w₀ := by
    rintro ⟨w₀, hconst⟩
    have hev : φ =ᶠ[𝓝 (1 : ℂ)] fun _ ↦ w₀ :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε₁_pos)) hconst
    have hd0 : deriv φ 1 = 0 := by rw [hev.deriv_eq, deriv_const]
    exact deriv_ostrowskiPoly_one_ne_zero hd0
  have himg_open : IsOpen (φ '' Metric.ball (1 : ℂ) ε₁) :=
    (RudinRCA.Chapter10.theorem10_32 hreg_ε₁ hφ_holo hφ_nonconst).1.1
      (Metric.ball (1 : ℂ) ε₁) Subset.rfl Metric.isOpen_ball
  have h1_img : (1 : ℂ) ∈ φ '' Metric.ball (1 : ℂ) ε₁ :=
    ⟨1, Metric.mem_ball_self hε₁_pos, ostrowskiPoly_one lam⟩
  obtain ⟨ρ₁, hρ₁_pos, hball_ρ₁_img⟩ := Metric.isOpen_iff.mp himg_open 1 h1_img
  let ρ : ℝ := min ρ₁ r₀
  have hρ_pos : 0 < ρ := lt_min hρ₁_pos hr₀
  have hρ_le_r₀ : ρ ≤ r₀ := min_le_right _ _
  have hball_ρ_img : Metric.ball (1 : ℂ) ρ ⊆ φ '' Metric.ball (1 : ℂ) ε₁ :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hball_ρ₁_img
  refine ⟨ρ, hρ_pos, hρ_le_r₀, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε_u hε_u
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hunif_sub.mono hball_ε₁_cb) ε_u hε_u] with k hk z hz
  obtain ⟨w, hw_ε₁, rfl⟩ := hball_ρ_img hz
  have hφw_r₀ : φ w ∈ Metric.ball (1 : ℂ) r₀ := (hball_ε₁_V₀ hw_ε₁).2
  have hGw_eq : G w = g₀ (φ w) := hF_eq_g₀ hφw_r₀
  simpa [hGw_eq] using hk w hw_ε₁

/-- **Rudin RCA 16.5 (Ostrowski's Overconvergence Theorem & Uniform Convergence Note, pp. 321–322):**
Let `lam > 0` be a positive integer and `{p_k}`, `{q_k}` be sequences of positive integers (`StrictMono p`,
`0 < p k`) satisfying `lam * q k > (lam + 1) * p k` for all `k`. Suppose `c : ℕ → ℂ` has radius of
convergence `1`, satisfies `c n = 0` whenever `p k < n < q k`, and represents `f(z) = ∑' n, c n * z^n`
on `Metric.ball 0 1`. Let `s_N(z) = powerSeriesPartialSum c N z`.

Then for every regular boundary point `ζ` of `f` on `Metric.sphere 0 1`, there exist `ρ > 0` and
`g : ℂ → ℂ` holomorphic on `Metric.ball ζ ρ` agreeing with `f` on `Metric.ball 0 1 ∩ Metric.ball ζ ρ`
such that `s_{p_k}` converges **uniformly** (and hence pointwise) to `g` on `Metric.ball ζ ρ`. -/
theorem theorem16_5 {lam : ℕ} (hlam : 0 < lam)
    {p q : ℕ → ℕ} (hp_mono : StrictMono p) (hp_pos : ∀ k, 0 < p k)
    (hgap : ∀ k, lam * q k > (lam + 1) * p k)
    {c : ℕ → ℂ} (hc_rad : HasRadiusOfConvergenceOne c)
    (hc_gap : ∀ k n, p k < n → n < q k → c n = 0)
    {f : ℂ → ℂ} (hf : Set.EqOn f (fun z ↦ ∑' n : ℕ, c n * z ^ n) (Metric.ball (0 : ℂ) 1))
    {ζ : ℂ} (hζ : IsRegularBoundaryPoint f 0 1 ζ) :
    ∃ (ρ : ℝ) (g : ℂ → ℂ),
      0 < ρ ∧
      DifferentiableOn ℂ g (Metric.ball ζ ρ) ∧
      Set.EqOn f g (Metric.ball (0 : ℂ) 1 ∩ Metric.ball ζ ρ) ∧
      TendstoUniformlyOn (fun k z ↦ powerSeriesPartialSum c (p k) z) g
        Filter.atTop (Metric.ball ζ ρ) ∧
      (∀ z ∈ Metric.ball ζ ρ,
        Tendsto (fun k ↦ powerSeriesPartialSum c (p k) z) Filter.atTop (𝓝 (g z))) := by
  rcases hζ with ⟨hζ_sp, r₀, g₀, hr₀, hg₀_diff, hg₀_eq⟩
  have hζ_norm : ‖ζ‖ = 1 := by rwa [Metric.mem_sphere, dist_zero_right] at hζ_sp
  have hζ_ne : ζ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hζ_norm
    norm_num at hζ_norm
  let c' : ℕ → ℂ := fun n ↦ c n * ζ ^ n
  let f' : ℂ → ℂ := fun w ↦ f (ζ * w)
  let g₀' : ℂ → ℂ := fun w ↦ g₀ (ζ * w)
  have hc'_rad : HasRadiusOfConvergenceOne c' := by
    unfold HasRadiusOfConvergenceOne at hc_rad ⊢
    rw [← hc_rad]
    apply le_antisymm
    · refine FormalMultilinearSeries.radius_le_of_le fun n ↦ ?_
      simp [c', norm_pow, hζ_norm]
    · refine FormalMultilinearSeries.radius_le_of_le fun n ↦ ?_
      simp [c', norm_pow, hζ_norm]
  have hc'_gap : ∀ k n, p k < n → n < q k → c' n = 0 := by
    intro k n h1 h2
    simp [c', hc_gap k n h1 h2]
  have hf'_eq : Set.EqOn f' (fun w ↦ ∑' n : ℕ, c' n * w ^ n) (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    have hζw : ζ * w ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right] at hw ⊢
      rw [norm_mul, hζ_norm, one_mul]
      exact hw
    dsimp [f', c']
    rw [hf hζw]
    refine tsum_congr fun n ↦ ?_
    rw [mul_pow]
    ring
  have hmaps_r₀ : Set.MapsTo (fun w : ℂ ↦ ζ * w) (Metric.ball (1 : ℂ) r₀) (Metric.ball ζ r₀) := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
    have : ζ * w - ζ = ζ * (w - 1) := by ring
    rw [this, norm_mul, hζ_norm, one_mul]
    exact hw
  have hg₀'_diff : DifferentiableOn ℂ g₀' (Metric.ball (1 : ℂ) r₀) :=
    hg₀_diff.comp (differentiable_id.const_mul ζ).differentiableOn hmaps_r₀
  have hg₀'_eq : Set.EqOn f' g₀' (Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) r₀) := by
    rintro w ⟨hw0, hw1⟩
    have hζw0 : ζ * w ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right] at hw0 ⊢
      rw [norm_mul, hζ_norm, one_mul]
      exact hw0
    exact hg₀_eq ⟨hζw0, hmaps_r₀ hw1⟩
  obtain ⟨ρ, hρ_pos, hρ_le, hunif'⟩ :=
    theorem16_5_at_one hlam hp_mono hp_pos hgap hc'_rad hc'_gap hr₀ hf'_eq hg₀'_diff hg₀'_eq
  have hsub_ρ : Metric.ball ζ ρ ⊆ Metric.ball ζ r₀ := Metric.ball_subset_ball hρ_le
  have hunif : TendstoUniformlyOn (fun k z ↦ powerSeriesPartialSum c (p k) z) g₀
      Filter.atTop (Metric.ball ζ ρ) := by
    rw [Metric.tendstoUniformlyOn_iff] at hunif' ⊢
    intro ε_u hε_u
    filter_upwards [hunif' ε_u hε_u] with k hk z hz
    let w : ℂ := ζ⁻¹ * z
    have hζw : ζ * w = z := mul_inv_cancel_left₀ hζ_ne z
    have hw_ρ : w ∈ Metric.ball (1 : ℂ) ρ := by
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      have : ζ⁻¹ * z - 1 = ζ⁻¹ * (z - ζ) := by
        rw [mul_sub, inv_mul_cancel₀ hζ_ne]
      rw [this, norm_mul, norm_inv, hζ_norm, inv_one, one_mul]
      exact hz
    have hpart_eq : powerSeriesPartialSum c' (p k) w = powerSeriesPartialSum c (p k) z := by
      dsimp [powerSeriesPartialSum, c']
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      calc c n * ζ ^ n * w ^ n = c n * (ζ * w) ^ n := by rw [mul_pow]; ring
        _ = c n * z ^ n := by rw [hζw]
    have hg_eq : g₀' w = g₀ z := by dsimp [g₀']; rw [hζw]
    simpa [hpart_eq, hg_eq] using hk w hw_ρ
  refine ⟨ρ, g₀, hρ_pos, hg₀_diff.mono hsub_ρ,
    hg₀_eq.mono (Set.inter_subset_inter_right _ hsub_ρ), hunif, fun z hz ↦ hunif.tendsto_at hz⟩

/-!
## 16.6: Hadamard's Gap Theorem
-/

/-- Lacunary coefficient sequence associated to exponents `p : ℕ → ℕ` and coefficients `a : ℕ → ℂ`:
`(lacunaryCoeffs p a) n = a k` if `p k = n`, and `0` if `n ∉ Set.range p`. -/
def lacunaryCoeffs (p : ℕ → ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  open Classical in
  if h : ∃ k : ℕ, p k = n then a h.choose else 0

/-- Equivalence between Rudin's real-form Hadamard gap condition `p_{k+1} > (1 + 1/λ) p_k` and
the integer inequality `λ p_{k+1} > (λ + 1) p_k`. -/
theorem hadamard_gap_cond_iff {lam : ℕ} (hlam : 0 < lam) (p : ℕ → ℕ) (k : ℕ) :
    (p (k + 1) : ℝ) > (1 + 1 / (lam : ℝ)) * (p k : ℝ) ↔ lam * p (k + 1) > (lam + 1) * p k := by
  have hlam_pos : (0 : ℝ) < (lam : ℝ) := by positivity
  constructor
  · intro h
    have hmul : (lam : ℝ) * ((1 + 1 / (lam : ℝ)) * (p k : ℝ)) < (lam : ℝ) * (p (k + 1) : ℝ) :=
      mul_lt_mul_of_pos_left h hlam_pos
    have hsimp : (lam : ℝ) * ((1 + 1 / (lam : ℝ)) * (p k : ℝ)) = ((lam : ℝ) + 1) * (p k : ℝ) := by
      field_simp [hlam_pos.ne']
    rw [hsimp] at hmul
    exact_mod_cast hmul
  · intro h
    have hcast : ((lam : ℝ) + 1) * (p k : ℝ) < (lam : ℝ) * (p (k + 1) : ℝ) := by exact_mod_cast h
    have hsimp : (lam : ℝ) * ((1 + 1 / (lam : ℝ)) * (p k : ℝ)) = ((lam : ℝ) + 1) * (p k : ℝ) := by
      field_simp [hlam_pos.ne']
    rw [← hsimp] at hcast
    exact lt_of_mul_lt_mul_left hcast hlam_pos.le

theorem strictMono_of_hadamard_gap {lam : ℕ} (hlam : 0 < lam) {p : ℕ → ℕ}
    (hp_pos : ∀ k, 0 < p k) (hgap : ∀ k, (p (k + 1) : ℝ) > (1 + 1 / (lam : ℝ)) * (p k : ℝ)) :
    StrictMono p := by
  refine strictMono_nat_of_lt_succ fun k ↦ ?_
  have hg := (hadamard_gap_cond_iff hlam p k).mp (hgap k)
  have hlt : lam * p k < lam * p (k + 1) := by
    calc lam * p k < lam * p k + p k := Nat.lt_add_of_pos_right (hp_pos k)
      _ = (lam + 1) * p k := by ring
      _ < lam * p (k + 1) := hg
  exact (Nat.mul_lt_mul_left hlam).mp hlt

theorem lacunaryCoeffs_apply_index {p : ℕ → ℕ} (hinj : Function.Injective p) (a : ℕ → ℂ) (k : ℕ) :
    lacunaryCoeffs p a (p k) = a k := by
  classical
  dsimp [lacunaryCoeffs]
  split_ifs with hex
  · exact congrArg a (hinj hex.choose_spec)
  · exact (hex ⟨k, rfl⟩).elim

theorem lacunaryCoeffs_apply_of_forall_ne {p : ℕ → ℕ} (a : ℕ → ℂ) {n : ℕ}
    (hne : ∀ k : ℕ, p k ≠ n) :
    lacunaryCoeffs p a n = 0 := by
  classical
  dsimp [lacunaryCoeffs]
  split_ifs with hex
  · rcases hex with ⟨k, hk⟩
    exact (hne k hk).elim
  · rfl

/-- **Rudin RCA 16.6 (Hadamard's Gap Theorem, coefficient-sequence form, p. 322):**
If `0 < lam`, `p : ℕ → ℕ` satisfies `0 < p k` and `p (k + 1) > (1 + 1 / lam) * p k`, and `c : ℕ → ℂ`
has radius of convergence `1` with `c n = 0` outside `Set.range p`, representing `f` on `D(0; 1)`,
then `f` has `T = Metric.sphere 0 1` as its natural boundary (`HasNaturalBoundaryUnitCircle f`). -/
theorem theorem16_6_coeffs {lam : ℕ} (hlam : 0 < lam)
    {p : ℕ → ℕ} (hp_pos : ∀ k, 0 < p k)
    (hgap : ∀ k, (p (k + 1) : ℝ) > (1 + 1 / (lam : ℝ)) * (p k : ℝ))
    {c : ℕ → ℂ} (hc_rad : HasRadiusOfConvergenceOne c)
    (hc_supp : ∀ n, (∀ k, n ≠ p k) → c n = 0)
    {f : ℂ → ℂ} (hf : Set.EqOn f (fun z ↦ ∑' n : ℕ, c n * z ^ n) (Metric.ball (0 : ℂ) 1)) :
    HasNaturalBoundaryUnitCircle f := by
  classical
  have hp_mono : StrictMono p := strictMono_of_hadamard_gap hlam hp_pos hgap
  have hgap_nat : ∀ k, lam * p (k + 1) > (lam + 1) * p k :=
    fun k ↦ (hadamard_gap_cond_iff hlam p k).mp (hgap k)
  have hc_gap : ∀ k n, p k < n → n < p (k + 1) → c n = 0 := by
    intro k n hgt hlt
    apply hc_supp n
    intro j hjp
    subst hjp
    rcases le_or_gt j k with hjk | hkj
    · exact absurd (hp_mono.monotone hjk) (not_le.mpr hgt)
    · have hk1 : k + 1 ≤ j := hkj
      exact absurd (hp_mono.monotone hk1) (not_le.mpr hlt)
  have hf_diff : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) := (theorem16_2 hc_rad hf).1
  refine ⟨hf_diff, fun ζ hζ_sp ↦ ⟨hζ_sp, ?_⟩⟩
  intro hζ_reg
  obtain ⟨ρ, g, hρ_pos, _, _, _, hpt⟩ :=
    theorem16_5 hlam hp_mono hp_pos hgap_nat hc_rad hc_gap hf hζ_reg
  have hζ_norm : ‖ζ‖ = 1 := by rwa [Metric.mem_sphere, dist_zero_right] at hζ_sp
  let r : ℝ := 1 + ρ / 2
  have hr_gt1 : 1 < r := by dsimp [r]; linarith
  have hr_pos : 0 < r := zero_lt_one.trans hr_gt1
  let z₀ : ℂ := (r : ℂ) * ζ
  have hz₀_mem : z₀ ∈ Metric.ball ζ ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : z₀ - ζ = ((ρ / 2 : ℝ) : ℂ) * ζ := by
      dsimp [z₀, r]
      push_cast
      ring
    rw [hsub, norm_mul, hζ_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith
  have hz₀_norm : ‖z₀‖ = r := by
    dsimp [z₀]
    rw [norm_mul, hζ_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr_pos]
  -- Rewrite `powerSeriesPartialSum c (p k) z₀` as `∑ j ∈ range (k + 1), c (p j) * z₀ ^ (p j)`.
  have hpart_z₀ : ∀ k : ℕ,
      powerSeriesPartialSum c (p k) z₀ = ∑ j ∈ Finset.range (k + 1), c (p j) * z₀ ^ (p j) := by
    intro k
    dsimp [powerSeriesPartialSum]
    have himg_sub : Finset.image p (Finset.range (k + 1)) ⊆ Finset.range (p k + 1) := by
      intro n hn
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
      rw [Finset.mem_range] at hj ⊢
      exact Nat.lt_succ_of_le (hp_mono.monotone (Nat.lt_succ_iff.mp hj))
    rw [← Finset.sum_subset himg_sub]
    · exact Finset.sum_image fun j₁ _ j₂ _ h ↦ hp_mono.injective h
    · intro n hn_range hn_nimg
      have hn_le : n ≤ p k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn_range)
      have hne_all : ∀ j, n ≠ p j := by
        intro j hnp
        subst hnp
        have hj_le : j ≤ k := hp_mono.le_iff_le.mp hn_le
        exact hn_nimg (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj_le), rfl⟩)
      rw [hc_supp n hne_all, zero_mul]
  have htend_S : Tendsto (fun k : ℕ ↦ ∑ j ∈ Finset.range (k + 1), c (p j) * z₀ ^ (p j))
      Filter.atTop (𝓝 (g z₀)) := by
    refine (hpt z₀ hz₀_mem).congr fun k ↦ hpart_z₀ k
  have htend_term : Tendsto (fun k : ℕ ↦ c (p (k + 1)) * z₀ ^ (p (k + 1)))
      Filter.atTop (𝓝 0) := by
    have ht1 : Tendsto (fun k : ℕ ↦ ∑ j ∈ Finset.range (k + 2), c (p j) * z₀ ^ (p j))
        Filter.atTop (𝓝 (g z₀)) :=
      htend_S.comp (tendsto_add_atTop_nat 1)
    have hdiff := ht1.sub htend_S
    rw [sub_self] at hdiff
    refine hdiff.congr fun k ↦ ?_
    rw [Finset.sum_range_succ (f := fun j ↦ c (p j) * z₀ ^ (p j)) (k + 1)]
    ring
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp htend_term 1 zero_lt_one
  let B₀ : ℝ := 1 + ∑ k ∈ Finset.range (N₀ + 1), ‖c (p k)‖ * r ^ (p k)
  have hB₀_nonneg : 0 ≤ B₀ := by
    dsimp [B₀]
    exact add_nonneg zero_le_one
      (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hr_pos.le _))
  have hbound_cp : ∀ k : ℕ, ‖c (p k)‖ * r ^ (p k) ≤ B₀ := by
    intro k
    by_cases hk : k < N₀ + 1
    · have hmem : k ∈ Finset.range (N₀ + 1) := Finset.mem_range.mpr hk
      have hle_sum : ‖c (p k)‖ * r ^ (p k) ≤
          ∑ j ∈ Finset.range (N₀ + 1), ‖c (p j)‖ * r ^ (p j) :=
        Finset.single_le_sum (f := fun j ↦ ‖c (p j)‖ * r ^ (p j))
          (fun _ _ ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hr_pos.le _)) hmem
      dsimp [B₀]
      linarith
    · have hk_ge : N₀ ≤ k - 1 := by omega
      have hk_eq : k - 1 + 1 = k := by omega
      have hlt1 := hN₀ (k - 1) hk_ge
      rw [hk_eq, dist_zero_right, norm_mul, norm_pow, hz₀_norm] at hlt1
      have hsum_nn : 0 ≤ ∑ j ∈ Finset.range (N₀ + 1), ‖c (p j)‖ * r ^ (p j) :=
        Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hr_pos.le _)
      dsimp [B₀]
      linarith
  have hbound_all : ∀ n : ℕ, ‖FormalMultilinearSeries.ofScalars ℂ c n‖ * r ^ n ≤ B₀ := by
    intro n
    rw [FormalMultilinearSeries.ofScalars_norm]
    by_cases hex : ∃ k : ℕ, n = p k
    · rcases hex with ⟨k, rfl⟩
      exact hbound_cp k
    · have hc0 : c n = 0 := hc_supp n fun k hnk ↦ hex ⟨k, hnk⟩
      rw [hc0, norm_zero, zero_mul]
      exact hB₀_nonneg
  let r_nn : ℝ≥0 := ⟨r, hr_pos.le⟩
  have hle_rad : (r_nn : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius :=
    (FormalMultilinearSeries.ofScalars ℂ c).le_radius_of_bound B₀ hbound_all
  rw [hc_rad] at hle_rad
  have hr_le1 : r ≤ 1 := by exact_mod_cast hle_rad
  linarith

/-- **Rudin RCA 16.6 (Hadamard's Gap Theorem, indexed lacunary series form, p. 322):**
Suppose `{p_k}` is a sequence of positive integers (`0 < p k`) satisfying
`p (k + 1) > (1 + 1 / lam) * p k` for some positive integer `lam > 0`. If the lacunary power series
`∑_{k=0}^∞ a_k z^{p_k}` (`lacunaryCoeffs p a`) has radius of convergence `1` and represents `f` on
`Metric.ball 0 1`, then `f` has the unit circle `T` as its natural boundary. -/
theorem theorem16_6 {lam : ℕ} (hlam : 0 < lam)
    {p : ℕ → ℕ} (hp_pos : ∀ k, 0 < p k)
    (hgap : ∀ k, (p (k + 1) : ℝ) > (1 + 1 / (lam : ℝ)) * (p k : ℝ))
    {a : ℕ → ℂ} (hc_rad : HasRadiusOfConvergenceOne (lacunaryCoeffs p a))
    {f : ℂ → ℂ} (hf : Set.EqOn f (fun z ↦ ∑' k : ℕ, a k * z ^ (p k)) (Metric.ball (0 : ℂ) 1)) :
    HasNaturalBoundaryUnitCircle f := by
  have hp_mono : StrictMono p := strictMono_of_hadamard_gap hlam hp_pos hgap
  have hinj : Function.Injective p := hp_mono.injective
  have hc_supp : ∀ n, (∀ k, n ≠ p k) → lacunaryCoeffs p a n = 0 :=
    fun n hne ↦ lacunaryCoeffs_apply_of_forall_ne a fun k hk ↦ hne k hk.symm
  have hf_c : Set.EqOn f (fun z ↦ ∑' n : ℕ, lacunaryCoeffs p a n * z ^ n) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    rw [hf hz]
    symm
    have h1 : (∑' n : ℕ, lacunaryCoeffs p a n * z ^ n) =
        ∑' k : ℕ, lacunaryCoeffs p a (p k) * z ^ (p k) := by
      refine (hinj.tsum_eq ?_).symm
      intro n hn
      rw [Function.mem_support] at hn
      by_contra hnr
      apply hn
      have h0 : lacunaryCoeffs p a n = 0 :=
        lacunaryCoeffs_apply_of_forall_ne a fun k hk ↦ hnr ⟨k, hk⟩
      rw [h0, zero_mul]
    dsimp only
    rw [h1]
    refine tsum_congr fun k ↦ ?_
    rw [lacunaryCoeffs_apply_index hinj]
  exact theorem16_6_coeffs hlam hp_pos hgap hc_rad hc_supp hf_c

/-!
## 16.7: Smooth-Boundary Lacunary Example (`exp(-√n)` on Powers of `2`)
-/

/-- **Rudin RCA 16.7 (Coefficients of the smooth-boundary lacunary example, pp. 322–323):**
`c_n = exp(-√n)` if `n = 2^k` for some `k ≥ 0`, and `c_n = 0` otherwise. -/
def smoothLacunaryCoeffs (n : ℕ) : ℂ :=
  open Classical in
  if ∃ k : ℕ, n = 2 ^ k then (Real.exp (-Real.sqrt (n : ℝ)) : ℂ) else 0

/-- **Rudin RCA 16.7 (Smooth-boundary lacunary series, pp. 322–323):**
`f(z) = ∑_{k=0}^∞ exp(-√(2^k)) * z^{2^k}`. -/
def smoothLacunarySeries (z : ℂ) : ℂ :=
  ∑' k : ℕ, (Real.exp (-Real.sqrt ((2 ^ k : ℕ) : ℝ)) : ℂ) * z ^ (2 ^ k)

/-- Formal `m`-th derivative term of `smoothLacunarySeries`:
`(∏_{j=0}^{m-1} (2^k - j)) * exp(-√(2^k)) * z^{2^k - m}`. -/
def smoothLacunaryDerivTerm (m k : ℕ) (z : ℂ) : ℂ :=
  (∏ j ∈ Finset.range m, (((2 ^ k : ℕ) : ℂ) - (j : ℂ))) *
    (Real.exp (-Real.sqrt ((2 ^ k : ℕ) : ℝ)) : ℂ) * z ^ (2 ^ k - m)

/-- Rapid-decay majorant: for every `m : ℕ`, `∑_{k=0}^∞ (2^k)^m * exp(-√(2^k)) < ∞`. -/
theorem summable_pow_two_pow_mul_exp_neg_sqrt (m : ℕ) :
    Summable (fun k : ℕ ↦ ((2 ^ k : ℝ) ^ m) * Real.exp (-Real.sqrt ((2 ^ k : ℕ) : ℝ))) := by
  let C : ℝ := ((2 * m + 2).factorial : ℝ)
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦ ?_)
    (summable_geometric_two.mul_left C)
  let x : ℝ := Real.sqrt ((2 ^ k : ℕ) : ℝ)
  have hx_nonneg : 0 ≤ x := Real.sqrt_nonneg _
  have hx_sq : x ^ 2 = (2 ^ k : ℝ) := by
    dsimp [x]
    rw [Real.sq_sqrt (by positivity)]
    push_cast
    rfl
  have hx_pos : 0 < (2 ^ k : ℝ) := by positivity
  have hexp_bound : x ^ (2 * m + 2) / C ≤ Real.exp x :=
    Real.pow_div_factorial_le_exp x hx_nonneg (2 * m + 2)
  have hC_pos : 0 < C := by
    dsimp [C]
    exact_mod_cast Nat.factorial_pos (2 * m + 2)
  have hx_pow_le : x ^ (2 * m + 2) ≤ C * Real.exp x := by
    linarith [(div_le_iff₀ hC_pos).mp hexp_bound]
  have hpow_2k : (2 ^ k : ℝ) ^ m = x ^ (2 * m) := by
    rw [← hx_sq, ← pow_mul, mul_comm 2 m]
  rw [hpow_2k, show Real.exp (-x) = (Real.exp x)⁻¹ from Real.exp_neg x]
  have hmul : x ^ (2 * m) * (Real.exp x)⁻¹ * (2 ^ k : ℝ) ≤ C := by
    have h1 : x ^ (2 * m) * (2 ^ k : ℝ) = x ^ (2 * m + 2) := by
      rw [← hx_sq, ← pow_add]
    calc x ^ (2 * m) * (Real.exp x)⁻¹ * (2 ^ k : ℝ)
        = x ^ (2 * m) * (2 ^ k : ℝ) * (Real.exp x)⁻¹ := by ring
      _ = x ^ (2 * m + 2) * (Real.exp x)⁻¹ := by rw [h1]
      _ ≤ (C * Real.exp x) * (Real.exp x)⁻¹ :=
          mul_le_mul_of_nonneg_right hx_pow_le (inv_nonneg.mpr (Real.exp_nonneg x))
      _ = C := by rw [mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero x), mul_one]
  have hdiv : x ^ (2 * m) * (Real.exp x)⁻¹ ≤ C / (2 ^ k : ℝ) := (le_div_iff₀ hx_pos).mpr hmul
  have hgeom : C / (2 ^ k : ℝ) = C * (1 / 2 : ℝ) ^ k := by
    rw [div_eq_mul_inv, ← inv_pow, one_div]
  rwa [hgeom] at hdiv

private theorem norm_smoothLacunaryDerivTerm_le (m k : ℕ) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    ‖smoothLacunaryDerivTerm m k z‖ ≤
      ((2 ^ k : ℝ) ^ m) * Real.exp (-Real.sqrt ((2 ^ k : ℕ) : ℝ)) := by
  have hzn : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  dsimp [smoothLacunaryDerivTerm]
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hpow_z : ‖z‖ ^ (2 ^ k - m) ≤ 1 := pow_le_one₀ (norm_nonneg z) hzn
  have hprod_le : ‖∏ j ∈ Finset.range m, (((2 ^ k : ℕ) : ℂ) - (j : ℂ))‖ ≤ (2 ^ k : ℝ) ^ m := by
    by_cases hlt : 2 ^ k < m
    · have hzero : (∏ j ∈ Finset.range m, (((2 ^ k : ℕ) : ℂ) - (j : ℂ))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.mpr hlt) (sub_self _)
      rw [hzero, norm_zero]
      positivity
    · have hle_m : m ≤ 2 ^ k := not_lt.mp hlt
      rw [Complex.norm_prod]
      calc (∏ j ∈ Finset.range m, ‖(((2 ^ k : ℕ) : ℂ) - (j : ℂ))‖)
          ≤ ∏ _j ∈ Finset.range m, (2 ^ k : ℝ) := by
            gcongr with j hj
            have hj_lt : j < m := Finset.mem_range.mp hj
            have hj_le : (j : ℝ) ≤ (2 ^ k : ℝ) := by exact_mod_cast (hj_lt.le.trans hle_m)
            have hcast : (((2 ^ k : ℕ) : ℂ) - (j : ℂ)) = (((2 ^ k : ℝ) - (j : ℝ) : ℝ) : ℂ) := by
              push_cast
              rfl
            rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
            linarith [Nat.cast_nonneg (α := ℝ) j]
        _ = (2 ^ k : ℝ) ^ m := by simp
  calc ‖∏ j ∈ Finset.range m, (((2 ^ k : ℕ) : ℂ) - (j : ℂ))‖ *
          Real.exp (-Real.sqrt ((2 ^ k : ℕ) : ℝ)) * ‖z‖ ^ (2 ^ k - m)
      ≤ ((2 ^ k : ℝ) ^ m * Real.exp (-Real.sqrt ((2 ^ k : ℕ) : ℝ))) * 1 := by
        refine mul_le_mul ?_ hpow_z (pow_nonneg (norm_nonneg z) _) (by positivity)
        exact mul_le_mul_of_nonneg_right hprod_le (Real.exp_nonneg _)
    _ = ((2 ^ k : ℝ) ^ m) * Real.exp (-Real.sqrt ((2 ^ k : ℕ) : ℝ)) := mul_one _

private theorem hasDerivAt_falling_pow (n m : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ ↦ (∏ j ∈ Finset.range m, ((n : ℂ) - (j : ℂ))) * w ^ (n - m))
      ((∏ j ∈ Finset.range (m + 1), ((n : ℂ) - (j : ℂ))) * z ^ (n - (m + 1))) z := by
  by_cases hnm : n ≤ m
  · rcases lt_or_eq_of_le hnm with hlt | rfl
    · have h0_m : (∏ j ∈ Finset.range m, ((n : ℂ) - (j : ℂ))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.mpr hlt) (sub_self _)
      have h0_m1 : (∏ j ∈ Finset.range (m + 1), ((n : ℂ) - (j : ℂ))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_succ_of_lt hlt)) (sub_self _)
      simp only [h0_m, h0_m1, zero_mul]
      exact hasDerivAt_const z (0 : ℂ)
    · have h0_m1 : (∏ j ∈ Finset.range (n + 1), ((n : ℂ) - (j : ℂ))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_succ_self n)) (sub_self _)
      simp only [Nat.sub_self, pow_zero, mul_one, h0_m1, zero_mul]
      exact hasDerivAt_const z (∏ j ∈ Finset.range n, ((n : ℂ) - (j : ℂ)))
  · have hlt : m < n := not_le.mp hnm
    have hsub_eq : n - m - 1 = n - (m + 1) := by omega
    have hd_pow : HasDerivAt (fun w : ℂ ↦ w ^ (n - m))
        (((n - m : ℕ) : ℂ) * z ^ (n - (m + 1))) z := by
      simpa [hsub_eq] using hasDerivAt_pow (n - m) z
    have hd_mul := hd_pow.const_mul (∏ j ∈ Finset.range m, ((n : ℂ) - (j : ℂ)))
    refine hd_mul.congr_deriv ?_
    rw [Nat.cast_sub hlt.le, Finset.prod_range_succ]
    ring

private theorem hasDerivAt_smoothLacunaryDerivTerm (m k : ℕ) (z : ℂ) :
    HasDerivAt (smoothLacunaryDerivTerm m k) (smoothLacunaryDerivTerm (m + 1) k z) z := by
  have hd := hasDerivAt_falling_pow (2 ^ k) m z
  have hd' := hd.const_mul (Real.exp (-Real.sqrt ((2 ^ k : ℕ) : ℝ)) : ℂ)
  have hfun : (fun w : ℂ ↦ (Real.exp (-Real.sqrt ((2 ^ k : ℕ) : ℝ)) : ℂ) *
      ((∏ j ∈ Finset.range m, (((2 ^ k : ℕ) : ℂ) - (j : ℂ))) * w ^ (2 ^ k - m))) =
      smoothLacunaryDerivTerm m k := by
    ext w
    dsimp [smoothLacunaryDerivTerm]
    ring
  rw [hfun] at hd'
  refine hd'.congr_deriv ?_
  dsimp [smoothLacunaryDerivTerm]
  ring

private theorem iteratedDeriv_boundary_term (k m : ℕ) (θ : ℝ) :
    iteratedDeriv m
      (fun t : ℝ ↦ (Real.exp (-Real.sqrt ((2 ^ k : ℕ) : ℝ)) : ℂ) *
        (Complex.exp ((t : ℂ) * Complex.I)) ^ (2 ^ k)) θ =
    (Real.exp (-Real.sqrt ((2 ^ k : ℕ) : ℝ)) : ℂ) *
      ((((2 ^ k : ℕ) : ℂ) * Complex.I) ^ m) *
      (Complex.exp ((θ : ℂ) * Complex.I)) ^ (2 ^ k) := by
  let c_k : ℂ := (Real.exp (-Real.sqrt ((2 ^ k : ℕ) : ℝ)) : ℂ)
  let α_k : ℂ := ((2 ^ k : ℕ) : ℂ) * Complex.I
  have hfun_eq :
      (fun t : ℝ ↦ c_k * (Complex.exp ((t : ℂ) * Complex.I)) ^ (2 ^ k)) =
      (fun t : ℝ ↦ c_k * Complex.exp ((t : ℂ) * α_k)) := by
    ext t
    rw [← Complex.exp_nat_mul]
    congr 2
    dsimp [α_k]
    ring
  change iteratedDeriv m (fun t : ℝ ↦ c_k * (Complex.exp ((t : ℂ) * Complex.I)) ^ (2 ^ k)) θ =
    c_k * α_k ^ m * (Complex.exp ((θ : ℂ) * Complex.I)) ^ (2 ^ k)
  rw [hfun_eq]
  have hexp_pow : ∀ t : ℝ,
      (Complex.exp ((t : ℂ) * Complex.I)) ^ (2 ^ k) = Complex.exp ((t : ℂ) * α_k) := by
    intro t
    rw [← Complex.exp_nat_mul]
    congr 1
    dsimp [α_k]
    ring
  rw [hexp_pow θ]
  induction m generalizing θ with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ]
    have hfun_m : iteratedDeriv m (fun t : ℝ ↦ c_k * Complex.exp ((t : ℂ) * α_k)) =
        fun t : ℝ ↦ (c_k * α_k ^ m) * Complex.exp ((t : ℂ) * α_k) := by
      ext t
      exact ih t
    rw [hfun_m]
    have hd_exp_c : HasDerivAt (fun w : ℂ ↦ Complex.exp (w * α_k))
        (Complex.exp ((θ : ℂ) * α_k) * α_k) (θ : ℂ) := by
      have hd_mul : HasDerivAt (fun w : ℂ ↦ w * α_k) α_k (θ : ℂ) := by
        simpa using (hasDerivAt_id (θ : ℂ)).mul_const α_k
      exact (Complex.hasDerivAt_exp ((θ : ℂ) * α_k)).comp (θ : ℂ) hd_mul
    have hd_exp : HasDerivAt (fun t : ℝ ↦ Complex.exp ((t : ℂ) * α_k))
        (Complex.exp ((θ : ℂ) * α_k) * α_k) θ := hd_exp_c.comp_ofReal
    have hd_tot := hd_exp.const_mul (c_k * α_k ^ m)
    rw [hd_tot.deriv, pow_succ]
    ring

/-- **Rudin RCA 16.7 (Smooth-boundary lacunary example, pp. 322–323):**
For `smoothLacunaryCoeffs` (`c_n = exp(-√n)` when `n = 2^k` and `0` otherwise) and
`smoothLacunarySeries(z) = ∑_{k=0}^∞ exp(-√(2^k)) * z^{2^k}`:
- `(a)` `smoothLacunaryCoeffs` has radius of convergence `1`, and `smoothLacunarySeries` agrees with
  `∑' n, smoothLacunaryCoeffs n * z^n` on all of `Metric.closedBall 0 1` (in particular on
  `Metric.ball 0 1`);
- `(b)` `HasNaturalBoundaryUnitCircle smoothLacunarySeries`;
- `(c)` for every `m : ℕ`, the `m`-th formal derivative series `∑_{k=0}^∞ smoothLacunaryDerivTerm m k z`
  has summable norms and converges **uniformly** on the closed unit disc `Metric.closedBall 0 1`
  (hence defines a continuous function on `Metric.closedBall 0 1`), and equals
  `iteratedDeriv m smoothLacunarySeries z` for all `z ∈ Metric.ball 0 1`;
- `(d)` the boundary function `θ : ℝ ↦ smoothLacunarySeries (Complex.exp (θ * Complex.I))` is `C^∞`
  smooth (`ContDiff ℝ (⊤ : ℕ∞)` and `∀ m : ℕ, ContDiff ℝ m`). -/
theorem theorem16_7 :
    (HasRadiusOfConvergenceOne smoothLacunaryCoeffs ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        smoothLacunarySeries z = ∑' n : ℕ, smoothLacunaryCoeffs n * z ^ n) ∧
      Set.EqOn smoothLacunarySeries
        (fun z ↦ ∑' n : ℕ, smoothLacunaryCoeffs n * z ^ n) (Metric.ball (0 : ℂ) 1)) ∧
    HasNaturalBoundaryUnitCircle smoothLacunarySeries ∧
    (∀ m : ℕ,
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        Summable (fun k : ℕ ↦ ‖smoothLacunaryDerivTerm m k z‖)) ∧
      TendstoUniformlyOn
        (fun N z ↦ ∑ k ∈ Finset.range N, smoothLacunaryDerivTerm m k z)
        (fun z ↦ ∑' k : ℕ, smoothLacunaryDerivTerm m k z)
        Filter.atTop (Metric.closedBall (0 : ℂ) 1) ∧
      ContinuousOn (fun z ↦ ∑' k : ℕ, smoothLacunaryDerivTerm m k z)
        (Metric.closedBall (0 : ℂ) 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1,
        iteratedDeriv m smoothLacunarySeries z =
          ∑' k : ℕ, smoothLacunaryDerivTerm m k z)) ∧
    (ContDiff ℝ (⊤ : ℕ∞)
        (fun θ : ℝ ↦ smoothLacunarySeries (Complex.exp ((θ : ℂ) * Complex.I))) ∧
      ∀ m : ℕ, ContDiff ℝ m
        (fun θ : ℝ ↦ smoothLacunarySeries (Complex.exp ((θ : ℂ) * Complex.I)))) := by
  classical
  have hpow_strict : StrictMono (fun k : ℕ ↦ 2 ^ k) :=
    strictMono_nat_of_lt_succ fun k ↦ by
      rw [pow_succ']
      have : 0 < 2 ^ k := by positivity
      omega
  have hinj : Function.Injective (fun k : ℕ ↦ 2 ^ k) := hpow_strict.injective
  have hcoeff_pow : ∀ k : ℕ, smoothLacunaryCoeffs (2 ^ k) =
      (Real.exp (-Real.sqrt ((2 ^ k : ℕ) : ℝ)) : ℂ) := by
    intro k
    dsimp [smoothLacunaryCoeffs]
    exact ite_eq_left_iff.mpr fun h ↦ (h ⟨k, rfl⟩).elim
  have hcoeff_not_pow : ∀ n : ℕ, (∀ k : ℕ, n ≠ 2 ^ k) → smoothLacunaryCoeffs n = 0 := by
    intro n hne
    dsimp [smoothLacunaryCoeffs]
    exact ite_eq_right_iff.mpr fun ⟨k, hk⟩ ↦ (hne k hk).elim
  have htsum_eq_all : ∀ z : ℂ,
      smoothLacunarySeries z = ∑' n : ℕ, smoothLacunaryCoeffs n * z ^ n := by
    intro z
    dsimp [smoothLacunarySeries]
    symm
    have h1 : (∑' n : ℕ, smoothLacunaryCoeffs n * z ^ n) =
        ∑' k : ℕ, smoothLacunaryCoeffs (2 ^ k) * z ^ (2 ^ k) := by
      refine (hinj.tsum_eq ?_).symm
      intro n hn
      rw [Function.mem_support] at hn
      by_contra hnr
      apply hn
      have h0 : smoothLacunaryCoeffs n = 0 :=
        hcoeff_not_pow n fun k hk ↦ hnr ⟨k, hk.symm⟩
      rw [h0, zero_mul]
    rw [h1]
    refine tsum_congr fun k ↦ ?_
    rw [hcoeff_pow]
  -- (a) Radius of convergence `1`.
  have hrad : HasRadiusOfConvergenceOne smoothLacunaryCoeffs := by
    rw [hasRadiusOfConvergenceOne_iff_closedBall]
    refine ⟨?_, ?_⟩
    · intro z hz
      have hz_cb : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz
      have hsum_k : Summable (fun k : ℕ ↦ smoothLacunaryCoeffs (2 ^ k) * z ^ (2 ^ k)) := by
        refine Summable.of_norm_bounded (summable_pow_two_pow_mul_exp_neg_sqrt 0) fun k ↦ ?_
        have h := norm_smoothLacunaryDerivTerm_le 0 k hz_cb
        simpa [smoothLacunaryDerivTerm, hcoeff_pow] using h
      refine (hinj.summable_iff (f := fun n : ℕ ↦ smoothLacunaryCoeffs n * z ^ n) ?_).mp hsum_k
      intro n hn
      have h0 : smoothLacunaryCoeffs n = 0 :=
        hcoeff_not_pow n fun k hk ↦ hn ⟨k, hk.symm⟩
      rw [h0, zero_mul]
    · intro r hr
      refine ⟨(r : ℂ), ?_, ?_⟩
      · simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (zero_lt_one.trans hr), le_rfl]
      · intro hsum
        have hr_pos : 0 < r := zero_lt_one.trans hr
        let δ : ℝ := Real.log r
        have hδ_pos : 0 < δ := Real.log_pos hr
        obtain ⟨K, hK⟩ := exists_nat_gt ((1 / δ) ^ 2)
        have ht0 : Tendsto (fun k : ℕ ↦ ‖smoothLacunaryCoeffs (2 ^ k) * (r : ℂ) ^ (2 ^ k)‖)
            atTop (𝓝 0) := by
          simpa using (hsum.tendsto_atTop_zero.comp hpow_strict.tendsto_atTop).norm
        obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht0 (1 / 2) (by norm_num)
        let k₀ : ℕ := max K N
        have hk₀_N : N ≤ k₀ := le_max_right K N
        have hlt_half := hN k₀ hk₀_N
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hlt_half
        have hge_one : 1 ≤ ‖smoothLacunaryCoeffs (2 ^ k₀) * (r : ℂ) ^ (2 ^ k₀)‖ := by
          rw [hcoeff_pow, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos hr_pos]
          have hr_exp : r ^ (2 ^ k₀) = Real.exp (((2 ^ k₀ : ℕ) : ℝ) * δ) := by
            conv_lhs => rw [← Real.exp_log hr_pos]
            rw [← Real.exp_nat_mul, mul_comm]
          rw [hr_exp, ← Real.exp_add, Real.one_le_exp_iff]
          let y : ℝ := Real.sqrt ((2 ^ k₀ : ℕ) : ℝ)
          have hy_sq : y ^ 2 = ((2 ^ k₀ : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
          have hy_ge : 1 / δ ≤ y := by
            have h2k_gt : (1 / δ) ^ 2 < ((2 ^ k₀ : ℕ) : ℝ) := by
              calc (1 / δ) ^ 2 < (K : ℝ) := hK
                _ ≤ (k₀ : ℝ) := by exact_mod_cast le_max_left K N
                _ ≤ ((2 ^ k₀ : ℕ) : ℝ) := by
                    exact_mod_cast (Nat.lt_two_pow_self (n := k₀)).le
            have hsq_le := Real.sqrt_le_sqrt h2k_gt.le
            rwa [Real.sqrt_sq (by positivity)] at hsq_le
          have hyδ : 1 ≤ y * δ := (div_le_iff₀ hδ_pos).mp hy_ge
          have hy_nonneg : 0 ≤ y := Real.sqrt_nonneg _
          change 0 ≤ -y + ((2 ^ k₀ : ℕ) : ℝ) * δ
          rw [← hy_sq]
          nlinarith
        linarith
  -- (b) Natural boundary `T` via Hadamard's Gap Theorem (`lam = 2`, `p k = 2 ^ k`).
  have hnat : HasNaturalBoundaryUnitCircle smoothLacunarySeries := by
    refine theorem16_6_coeffs (lam := 2) (by decide) (p := fun k : ℕ ↦ 2 ^ k)
      (fun k ↦ by positivity) (fun k ↦ ?_) hrad hcoeff_not_pow
      (fun z hz ↦ htsum_eq_all z)
    rw [hadamard_gap_cond_iff (by decide : 0 < 2)]
    rw [pow_succ']
    have : 0 < 2 ^ k := by positivity
    omega
  -- (c) Uniform convergence on `closedBall 0 1` and agreement with `iteratedDeriv` on `ball 0 1`.
  have hderiv_unif : ∀ m : ℕ,
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        Summable (fun k : ℕ ↦ ‖smoothLacunaryDerivTerm m k z‖)) ∧
      TendstoUniformlyOn
        (fun N z ↦ ∑ k ∈ Finset.range N, smoothLacunaryDerivTerm m k z)
        (fun z ↦ ∑' k : ℕ, smoothLacunaryDerivTerm m k z)
        Filter.atTop (Metric.closedBall (0 : ℂ) 1) ∧
      ContinuousOn (fun z ↦ ∑' k : ℕ, smoothLacunaryDerivTerm m k z)
        (Metric.closedBall (0 : ℂ) 1) := by
    intro m
    have hsum_norm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        Summable (fun k : ℕ ↦ ‖smoothLacunaryDerivTerm m k z‖) := fun z hz ↦
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
        (fun k ↦ norm_smoothLacunaryDerivTerm_le m k hz)
        (summable_pow_two_pow_mul_exp_neg_sqrt m)
    have hunif : TendstoUniformlyOn
        (fun N z ↦ ∑ k ∈ Finset.range N, smoothLacunaryDerivTerm m k z)
        (fun z ↦ ∑' k : ℕ, smoothLacunaryDerivTerm m k z)
        Filter.atTop (Metric.closedBall (0 : ℂ) 1) :=
      tendstoUniformlyOn_tsum_nat (summable_pow_two_pow_mul_exp_neg_sqrt m)
        fun k z hz ↦ norm_smoothLacunaryDerivTerm_le m k hz
    have hcont : ContinuousOn (fun z ↦ ∑' k : ℕ, smoothLacunaryDerivTerm m k z)
        (Metric.closedBall (0 : ℂ) 1) := by
      refine hunif.continuousOn (Frequently.of_forall fun N ↦ ?_)
      refine continuousOn_finsetSum _ fun k _ ↦ ?_
      unfold smoothLacunaryDerivTerm
      fun_prop
    exact ⟨hsum_norm, hunif, hcont⟩
  have hiter_eq : ∀ m : ℕ, ∀ z ∈ Metric.ball (0 : ℂ) 1,
      iteratedDeriv m smoothLacunarySeries z =
        ∑' k : ℕ, smoothLacunaryDerivTerm m k z := by
    intro m
    induction m with
    | zero =>
      intro z _
      simp [smoothLacunarySeries, smoothLacunaryDerivTerm]
    | succ m ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      let S_m : ℂ → ℂ := fun w ↦ ∑' k : ℕ, smoothLacunaryDerivTerm m k w
      have hev_eq : iteratedDeriv m smoothLacunarySeries =ᶠ[𝓝 z] S_m :=
        Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz) fun w hw ↦ ih w hw
      rw [hev_eq.deriv_eq]
      have hd_Sm : HasDerivAt S_m (∑' k : ℕ, smoothLacunaryDerivTerm (m + 1) k z) z := by
        refine hasDerivAt_tsum_of_isPreconnected
          (hu := summable_pow_two_pow_mul_exp_neg_sqrt (m + 1))
          (ht := Metric.isOpen_ball)
          (h't := (convex_ball (0 : ℂ) 1).isPreconnected)
          (hg := fun k w _ ↦ hasDerivAt_smoothLacunaryDerivTerm m k w)
          (hg' := fun k w hw ↦ norm_smoothLacunaryDerivTerm_le (m + 1) k
            (Metric.ball_subset_closedBall hw))
          (hy₀ := Metric.mem_ball_self zero_lt_one)
          (hg0 := ((hderiv_unif m).1 0 (Metric.mem_closedBall_self zero_le_one)).of_norm)
          (hy := hz)
      exact hd_Sm.deriv
  -- (d) Boundary smoothness `ContDiff ℝ (⊤ : ℕ∞)`.
  let bTerm : ℕ → ℝ → ℂ := fun k θ ↦
    (Real.exp (-Real.sqrt ((2 ^ k : ℕ) : ℝ)) : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I)) ^ (2 ^ k)
  have hb_contDiff : ∀ k : ℕ, ContDiff ℝ (⊤ : ℕ∞) (bTerm k) := by
    intro k
    dsimp [bTerm]
    have hc_ofReal : ContDiff ℝ (⊤ : ℕ∞) (fun θ : ℝ ↦ (θ : ℂ)) := Complex.ofRealCLM.contDiff
    have hc_exp : ContDiff ℝ (⊤ : ℕ∞) (fun θ : ℝ ↦ Complex.exp ((θ : ℂ) * Complex.I)) :=
      Complex.contDiff_exp.comp (hc_ofReal.mul contDiff_const)
    exact contDiff_const.mul (hc_exp.pow (2 ^ k))
  have hb_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun θ : ℝ ↦ smoothLacunarySeries (Complex.exp ((θ : ℂ) * Complex.I))) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun θ : ℝ ↦ ∑' k : ℕ, bTerm k θ)
    refine contDiff_tsum (v := fun m k ↦ ((2 ^ k : ℝ) ^ m) * Real.exp (-Real.sqrt ((2 ^ k : ℕ) : ℝ)))
      hb_contDiff (fun m _ ↦ summable_pow_two_pow_mul_exp_neg_sqrt m) ?_
    intro m k θ _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_boundary_term k m θ]
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow, mul_one]
    have hnorm_c : ‖(Real.exp (-Real.sqrt ((2 ^ k : ℕ) : ℝ)) : ℂ)‖ =
        Real.exp (-Real.sqrt ((2 ^ k : ℕ) : ℝ)) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hnorm_α : ‖((2 ^ k : ℕ) : ℂ) * Complex.I‖ = (2 ^ k : ℝ) := by
      rw [norm_mul, Complex.norm_I, mul_one]
      norm_cast
    rw [hnorm_c, hnorm_α, mul_comm]
  exact ⟨⟨hrad, fun z _ ↦ htsum_eq_all z, fun z _ ↦ htsum_eq_all z⟩,
    hnat,
    fun m ↦ ⟨(hderiv_unif m).1, (hderiv_unif m).2.1, (hderiv_unif m).2.2, hiter_eq m⟩,
    ⟨hb_smooth, fun m ↦ hb_smooth.of_le (by simp)⟩⟩


/-- **Rudin RCA 16.4 (Unconditional plane-region non-extendability, pp. 320–321):**
Every plane region `Ω` (`RudinRCA.Chapter10.IsRegion Ω`) admits a holomorphic function `f ∈ H(Ω)`
that has no holomorphic extension to any strictly larger plane region `Ω₁ ⊋ Ω`. -/
theorem theorem16_4_region {Ω : Set ℂ} (hΩ : RudinRCA.Chapter10.IsRegion Ω) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧
      ¬ ∃ (Ω₁ : Set ℂ) (F : ℂ → ℂ),
        RudinRCA.Chapter10.IsRegion Ω₁ ∧ Ω ⊂ Ω₁ ∧ DifferentiableOn ℂ F Ω₁ ∧ Set.EqOn f F Ω :=
  theorem16_4_region_using_15_11
    (fun hΩ₀ hA₀ hacc hm₀ ↦
      let ⟨f, hf, hzero, _, _⟩ := RudinRCA.Chapter15.theorem15_1.2.2 hΩ₀ hA₀ hacc hm₀
      ⟨f, hf, hzero⟩)
    hΩ

/-- **Rudin RCA 16.4 (Complete Remark bundle, pp. 320–321):**
1. Every plane region `Ω` admits `f ∈ H(Ω)` with no holomorphic extension to any strictly larger
   plane region `Ω₁ ⊋ Ω`;
2. `lacunaryDyadicSeries z = ∑' n, z ^ (2 ^ n)` has radius of convergence `1`, satisfies
   `f(z) = z + f(z ^ 2)` on `U`, diverges radially along all dyadic roots of unity, and has natural
   boundary `T = sphere 0 1`. -/
theorem theorem16_4 :
    (∀ {Ω : Set ℂ}, RudinRCA.Chapter10.IsRegion Ω →
      ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧
        ¬ ∃ (Ω₁ : Set ℂ) (F : ℂ → ℂ),
          RudinRCA.Chapter10.IsRegion Ω₁ ∧ Ω ⊂ Ω₁ ∧ DifferentiableOn ℂ F Ω₁ ∧ Set.EqOn f F Ω) ∧
    ((HasRadiusOfConvergenceOne lacunaryDyadicCoeffs ∧
        (∀ z ∈ Metric.ball (0 : ℂ) 1, Summable (fun n : ℕ ↦ z ^ (2 ^ n)) ∧
          lacunaryDyadicSeries z = ∑' n : ℕ, lacunaryDyadicCoeffs n * z ^ n) ∧
        DifferentiableOn ℂ lacunaryDyadicSeries (Metric.ball (0 : ℂ) 1)) ∧
      ((∀ z ∈ Metric.ball (0 : ℂ) 1,
          lacunaryDyadicSeries z = z + lacunaryDyadicSeries (z ^ 2)) ∧
        (∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ m : ℕ,
          lacunaryDyadicSeries z =
            (∑ k ∈ Finset.range m, z ^ (2 ^ k)) + lacunaryDyadicSeries (z ^ (2 ^ m)))) ∧
      (Metric.sphere (0 : ℂ) 1 ⊆ closure {ζ : ℂ | ∃ m : ℕ, ζ ^ (2 ^ m) = 1} ∧
        ∀ (ζ : ℂ) (m : ℕ), ζ ^ (2 ^ m) = 1 →
          Tendsto (fun r : ℝ ↦ ‖lacunaryDyadicSeries ((r : ℂ) * ζ)‖) (𝓝[<] 1) Filter.atTop) ∧
      HasNaturalBoundaryUnitCircle lacunaryDyadicSeries) :=
  ⟨fun hΩ ↦ theorem16_4_region hΩ, theorem16_4_dyadic⟩

/-!
## Axiom Audit (`16.1`–`16.7`)
-/

#print axioms IsRegularBoundaryPoint
#print axioms IsSingularBoundaryPoint
#print axioms isRegularBoundaryPoint_of_mem_ball
#print axioms theorem16_1
#print axioms HasRadiusOfConvergenceOne
#print axioms summable_norm_of_hasRadiusOfConvergenceOne
#print axioms summable_of_hasRadiusOfConvergenceOne
#print axioms hasRadiusOfConvergenceOne_iff_closedBall
#print axioms hasRadiusOfConvergenceOne_iff_ball
#print axioms hasFPowerSeriesOnBall_of_hasRadiusOfConvergenceOne
#print axioms theorem16_2
#print axioms HasNaturalBoundaryUnitCircle
#print axioms exists_mem_inter_frontier_of_ssubset_isRegion
#print axioms theorem16_3
#print axioms lacunaryDyadicCoeffs
#print axioms lacunaryDyadicSeries
#print axioms dense_dyadicRootsOfUnity_in_unitCircle
#print axioms theorem16_4_dyadic
#print axioms theorem16_4_region_using_15_11
#print axioms powerSeriesPartialSum
#print axioms ostrowskiPoly
#print axioms theorem16_5
#print axioms lacunaryCoeffs
#print axioms hadamard_gap_cond_iff
#print axioms strictMono_of_hadamard_gap
#print axioms lacunaryCoeffs_apply_index
#print axioms lacunaryCoeffs_apply_of_forall_ne
#print axioms theorem16_6_coeffs
#print axioms theorem16_6
#print axioms smoothLacunaryCoeffs
#print axioms smoothLacunarySeries
#print axioms smoothLacunaryDerivTerm
#print axioms summable_pow_two_pow_mul_exp_neg_sqrt
#print axioms theorem16_7

#print axioms theorem16_4_region
#print axioms theorem16_4

end Chapter16PartA

section Chapter16PartB
open Set Filter Metric Complex MeasureTheory
open scoped Topology Interval Real


/-!
## 16.8: Morera Arc Gluing Across a Straight Line or Circular Arc
-/

/-- A straight line in `ℂ`, given in real Cartesian coordinates by `a * z.re + b * z.im = c`
with `(a, b) ≠ (0, 0)`. -/
def IsStraightLine (L : Set ℂ) : Prop :=
  ∃ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ L = {z : ℂ | a * z.re + b * z.im = c}

/-- A straight line or circle (`Metric.sphere z₀ R` with `R > 0`) in `ℂ` (Rudin 16.8, p. 323). -/
def IsLineOrCircle (C : Set ℂ) : Prop :=
  IsStraightLine C ∨ ∃ (z₀ : ℂ) (R : ℝ), 0 < R ∧ C = Metric.sphere z₀ R

/-- Rectangle boundary integral vanishes when `f` is continuous on `Rectangle z w` and complex
differentiable off the real axis `{ζ : ℂ | ζ.im = 0}` on the open interior of `Rectangle z w`,
first when `0` is not in the open vertical interval `Ioo (min z.im w.im) (max z.im w.im)`. -/
private theorem rectBoundary_eq_zero_of_zero_notMem_im {Ω : Set ℂ}
    {f : ℂ → ℂ} (hf_cont : ContinuousOn f Ω)
    (hf_diff : DifferentiableOn ℂ f (Ω \ {ζ : ℂ | ζ.im = 0}))
    {z w : ℂ} (hrect : Complex.Rectangle z w ⊆ Ω)
    (h0 : (0 : ℝ) ∉ Set.Ioo (min z.im w.im) (max z.im w.im)) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) -
      (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) = 0 := by
  apply Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w
  · exact hf_cont.mono hrect
  · refine hf_diff.mono ?_
    rintro ζ ⟨hζ_re, hζ_im⟩
    refine ⟨hrect ⟨?_, ?_⟩, ?_⟩
    · rw [Set.uIcc]
      exact Set.Ioo_subset_Icc_self hζ_re
    · rw [Set.uIcc]
      exact Set.Ioo_subset_Icc_self hζ_im
    · intro him0
      exact h0 (him0 ▸ hζ_im)

/-- Morera gluing across the real axis `{z : ℂ | z.im = 0}`: if `Ω ⊆ ℂ` is open, `f` is continuous
on `Ω`, and `f` is holomorphic on `Ω \ {z : ℂ | z.im = 0}`, then `f` is holomorphic on `Ω`. -/
theorem holomorphic_of_continuous_off_real_axis {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf_cont : ContinuousOn f Ω)
    (hf_diff : DifferentiableOn ℂ f (Ω \ {z : ℂ | z.im = 0})) :
    DifferentiableOn ℂ f Ω := by
  rw [← Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hΩ]
  refine ⟨?_, hf_cont⟩
  intro z w hrect
  rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq]
  by_cases h0 : (0 : ℝ) ∈ Set.Ioo (min z.im w.im) (max z.im w.im)
  · have h0_uIcc : (0 : ℝ) ∈ [[z.im, w.im]] := by
      rw [Set.uIcc]
      exact Set.Ioo_subset_Icc_self h0
    let w₀ : ℂ := (w.re : ℂ)
    let z₀ : ℂ := (z.re : ℂ)
    have hw₀_re : w₀.re = w.re := Complex.ofReal_re w.re
    have hw₀_im : w₀.im = 0 := Complex.ofReal_im w.re
    have hz₀_re : z₀.re = z.re := Complex.ofReal_re z.re
    have hz₀_im : z₀.im = 0 := Complex.ofReal_im z.re
    have hrect₁ : Complex.Rectangle z w₀ ⊆ Ω := by
      refine Subset.trans ?_ hrect
      rintro ζ ⟨hre, him⟩
      rw [hw₀_re] at hre
      rw [hw₀_im] at him
      exact ⟨hre, Set.uIcc_subset_uIcc_left h0_uIcc him⟩
    have hrect₂ : Complex.Rectangle z₀ w ⊆ Ω := by
      refine Subset.trans ?_ hrect
      rintro ζ ⟨hre, him⟩
      rw [hz₀_re] at hre
      rw [hz₀_im] at him
      exact ⟨hre, Set.uIcc_subset_uIcc_right h0_uIcc him⟩
    have h0_not₁ : (0 : ℝ) ∉ Set.Ioo (min z.im w₀.im) (max z.im w₀.im) := by
      rw [hw₀_im]
      rintro ⟨hlt, hgt⟩
      rcases le_total z.im 0 with hle | hge
      · rw [max_eq_right hle] at hgt
        exact lt_irrefl 0 hgt
      · rw [min_eq_right hge] at hlt
        exact lt_irrefl 0 hlt
    have h0_not₂ : (0 : ℝ) ∉ Set.Ioo (min z₀.im w.im) (max z₀.im w.im) := by
      rw [hz₀_im]
      rintro ⟨hlt, hgt⟩
      rcases le_total 0 w.im with hle | hge
      · rw [min_eq_left hle] at hlt
        exact lt_irrefl 0 hlt
      · rw [max_eq_left hge] at hgt
        exact lt_irrefl 0 hgt
    have heq₁ := rectBoundary_eq_zero_of_zero_notMem_im hf_cont hf_diff hrect₁ h0_not₁
    have heq₂ := rectBoundary_eq_zero_of_zero_notMem_im hf_cont hf_diff hrect₂ h0_not₂
    simp only [hw₀_re, hw₀_im, hz₀_re, hz₀_im] at heq₁ heq₂
    have hint_vert (x₀ a b : ℝ) (ha : a ∈ [[z.im, w.im]]) (hb : b ∈ [[z.im, w.im]])
        (hx₀ : x₀ ∈ [[z.re, w.re]]) :
        IntervalIntegrable (fun y : ℝ ↦ f (x₀ + y * I)) volume a b := by
      apply ContinuousOn.intervalIntegrable
      refine (hf_cont.mono hrect).comp ((continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const)).continuousOn) ?_
      intro y hy
      refine ⟨?_, ?_⟩
      · simpa using hx₀
      · simpa using Set.uIcc_subset_uIcc ha hb hy
    have hw_re_mem : w.re ∈ [[z.re, w.re]] := Set.right_mem_uIcc
    have hz_re_mem : z.re ∈ [[z.re, w.re]] := Set.left_mem_uIcc
    have hz_im_mem : z.im ∈ [[z.im, w.im]] := Set.left_mem_uIcc
    have hw_im_mem : w.im ∈ [[z.im, w.im]] := Set.right_mem_uIcc
    have hv_w := intervalIntegral.integral_add_adjacent_intervals
      (hint_vert w.re z.im 0 hz_im_mem h0_uIcc hw_re_mem)
      (hint_vert w.re 0 w.im h0_uIcc hw_im_mem hw_re_mem)
    have hv_z := intervalIntegral.integral_add_adjacent_intervals
      (hint_vert z.re z.im 0 hz_im_mem h0_uIcc hz_re_mem)
      (hint_vert z.re 0 w.im h0_uIcc hw_im_mem hz_re_mem)
    rw [← hv_w, ← hv_z]
    simp only [smul_eq_mul] at heq₁ heq₂ ⊢
    linear_combination heq₁ + heq₂
  · exact rectBoundary_eq_zero_of_zero_notMem_im hf_cont hf_diff hrect h0

/-- Morera gluing across any straight line `L` in `ℂ`: if `Ω ⊆ ℂ` is open, `L` is a straight line,
`f` is continuous on `Ω`, and `f` is holomorphic on `Ω \ L`, then `f` is holomorphic on `Ω`. -/
theorem holomorphic_of_continuous_off_line {Ω L : Set ℂ} (hΩ : IsOpen Ω)
    (hL : IsStraightLine L) {f : ℂ → ℂ} (hf_cont : ContinuousOn f Ω)
    (hf_diff : DifferentiableOn ℂ f (Ω \ L)) :
    DifferentiableOn ℂ f Ω := by
  obtain ⟨a, b, c, hab, rfl⟩ := hL
  let α : ℂ := (b : ℂ) + (a : ℂ) * I
  have hα_ne : α ≠ 0 := by
    intro h0
    have hb0 : b = 0 := by simpa [α] using congrArg Complex.re h0
    have ha0 : a = 0 := by simpa [α] using congrArg Complex.im h0
    rcases hab with ha | hb
    · exact ha ha0
    · exact hb hb0
  let T : ℂ → ℂ := fun z ↦ α * z - (c : ℂ) * I
  let S : ℂ → ℂ := fun w ↦ α⁻¹ * (w + (c : ℂ) * I)
  have hST : ∀ z : ℂ, S (T z) = z := by
    intro z
    dsimp [S, T]
    rw [sub_add_cancel, ← mul_assoc, inv_mul_cancel₀ hα_ne, one_mul]
  have hTS : ∀ w : ℂ, T (S w) = w := by
    intro w
    dsimp [S, T]
    rw [← mul_assoc, mul_inv_cancel₀ hα_ne, one_mul, add_sub_cancel_right]
  have hT_im : ∀ z : ℂ, (T z).im = a * z.re + b * z.im - c := by
    intro z
    simp [T, α]
    ring
  have hS_diff : Differentiable ℂ S :=
    ((differentiable_id.add (differentiable_const _)).const_mul α⁻¹)
  have hT_diff : Differentiable ℂ T :=
    ((differentiable_id.const_mul α).sub (differentiable_const _))
  let Ω' : Set ℂ := S ⁻¹' Ω
  have hΩ'_open : IsOpen Ω' := hΩ.preimage hS_diff.continuous
  let g : ℂ → ℂ := f ∘ S
  have hg_cont : ContinuousOn g Ω' :=
    hf_cont.comp hS_diff.continuous.continuousOn (fun _ hw ↦ hw)
  have hg_diff_off : DifferentiableOn ℂ g (Ω' \ {w : ℂ | w.im = 0}) := by
    refine hf_diff.comp hS_diff.differentiableOn ?_
    rintro w ⟨hwΩ', hw_im⟩
    refine ⟨hwΩ', ?_⟩
    intro hwL
    change a * (S w).re + b * (S w).im = c at hwL
    apply hw_im
    change w.im = 0
    rw [← hTS w, hT_im (S w)]
    linarith
  have hg_diff : DifferentiableOn ℂ g Ω' :=
    holomorphic_of_continuous_off_real_axis hΩ'_open hg_cont hg_diff_off
  have hf_eq : f = g ∘ T := by
    ext z
    simp [g, hST z]
  rw [hf_eq]
  refine hg_diff.comp hT_diff.differentiableOn ?_
  intro z hz
  change S (T z) ∈ Ω
  rwa [hST z]

/-- Helper for `holomorphic_of_continuous_off_unit_circle`: differentiability at any `z₀ ∈ Ω`
with `z₀ ≠ -1`, via the inversion `M ζ = -1 + ζ⁻¹` mapping `{ζ | 2 * ζ.re = 1}` to
`Metric.sphere 0 1 \ {-1}`. -/
private theorem differentiableAt_off_unit_circle_ne_neg_one {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf_cont : ContinuousOn f Ω)
    (hf_diff : DifferentiableOn ℂ f (Ω \ Metric.sphere (0 : ℂ) 1))
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hne : z₀ ≠ -1) :
    DifferentiableAt ℂ f z₀ := by
  let M : ℂ → ℂ := fun ζ ↦ -1 + ζ⁻¹
  have hM_cont : ContinuousOn M ({0}ᶜ) :=
    continuousOn_const.add (continuousOn_id.inv₀ (fun _ hζ ↦ hζ))
  have hM_diff : DifferentiableOn ℂ M ({0}ᶜ) :=
    (differentiableOn_const (-1)).add (differentiableOn_id.inv (fun _ hζ ↦ hζ))
  let Ω' : Set ℂ := {ζ : ℂ | ζ ≠ 0} ∩ M ⁻¹' Ω
  have hΩ'_open : IsOpen Ω' := by
    refine hM_cont.isOpen_inter_preimage isOpen_ne hΩ
  let L : Set ℂ := {ζ : ℂ | (2 : ℝ) * ζ.re + (0 : ℝ) * ζ.im = 1}
  have hL : IsStraightLine L := ⟨2, 0, 1, Or.inl two_ne_zero, rfl⟩
  have hM_sphere : ∀ {ζ : ℂ}, ζ ≠ 0 → M ζ ∈ Metric.sphere (0 : ℂ) 1 → ζ ∈ L := by
    intro ζ hζ hsp
    rw [Metric.mem_sphere, dist_zero_right] at hsp
    have h1 : M ζ = (1 - ζ) / ζ := by
      dsimp [M]
      field_simp [hζ]
      ring
    rw [h1, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hζ)] at hsp
    have hsq : Complex.normSq (1 - ζ) = Complex.normSq ζ := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hsp]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im] at hsq
    change (2 : ℝ) * ζ.re + (0 : ℝ) * ζ.im = 1
    linarith
  let g : ℂ → ℂ := f ∘ M
  have hg_cont : ContinuousOn g Ω' :=
    hf_cont.comp (hM_cont.mono inter_subset_left) (fun _ hζ ↦ hζ.2)
  have hg_diff_off : DifferentiableOn ℂ g (Ω' \ L) := by
    refine hf_diff.comp (hM_diff.mono (Subset.trans sdiff_subset inter_subset_left)) ?_
    rintro ζ ⟨⟨hζ0, hζΩ⟩, hζL⟩
    exact ⟨hζΩ, fun hsp ↦ hζL (hM_sphere hζ0 hsp)⟩
  have hg_diff : DifferentiableOn ℂ g Ω' :=
    holomorphic_of_continuous_off_line hΩ'_open hL hg_cont hg_diff_off
  have hz₀_add : z₀ + 1 ≠ 0 := by
    intro h0
    apply hne
    linear_combination h0
  let ζ₀ : ℂ := (z₀ + 1)⁻¹
  have hζ₀_ne : ζ₀ ≠ 0 := inv_ne_zero hz₀_add
  have hM_ζ₀ : M ζ₀ = z₀ := by
    dsimp [M, ζ₀]
    rw [inv_inv]
    ring
  have hζ₀_mem : ζ₀ ∈ Ω' := ⟨hζ₀_ne, by simp [hM_ζ₀, hz₀]⟩
  have hg_at : DifferentiableAt ℂ g ζ₀ := hg_diff.differentiableAt (hΩ'_open.mem_nhds hζ₀_mem)
  let N : ℂ → ℂ := fun z ↦ (z + 1)⁻¹
  have hN_at : DifferentiableAt ℂ N z₀ :=
    (differentiableAt_id.add (differentiableAt_const 1)).inv hz₀_add
  have hcomp_at : DifferentiableAt ℂ (g ∘ N) z₀ := hg_at.comp z₀ hN_at
  have hev : (g ∘ N) =ᶠ[𝓝 z₀] f := by
    have hopen_ne : IsOpen {z : ℂ | z ≠ -1} := isOpen_ne
    filter_upwards [hopen_ne.mem_nhds hne] with z hz
    change f (-1 + ((z + 1)⁻¹)⁻¹) = f z
    rw [inv_inv]
    congr 1
    ring
  exact hcomp_at.congr_of_eventuallyEq hev.symm

/-- Morera gluing across the unit circle `Metric.sphere (0 : ℂ) 1`. -/
private theorem holomorphic_of_continuous_off_unit_circle {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf_cont : ContinuousOn f Ω)
    (hf_diff : DifferentiableOn ℂ f (Ω \ Metric.sphere (0 : ℂ) 1)) :
    DifferentiableOn ℂ f Ω := by
  intro z₀ hz₀
  apply DifferentiableAt.differentiableWithinAt
  by_cases hne : z₀ ≠ -1
  · exact differentiableAt_off_unit_circle_ne_neg_one hΩ hf_cont hf_diff hz₀ hne
  · push Not at hne
    subst hne
    let Ω₁ : Set ℂ := Neg.neg ⁻¹' Ω
    have hΩ₁ : IsOpen Ω₁ := hΩ.preimage continuous_neg
    let g : ℂ → ℂ := fun w ↦ f (-w)
    have hg_cont : ContinuousOn g Ω₁ :=
      hf_cont.comp continuous_neg.continuousOn (fun _ hw ↦ hw)
    have hg_diff : DifferentiableOn ℂ g (Ω₁ \ Metric.sphere (0 : ℂ) 1) := by
      refine hf_diff.comp differentiable_neg.differentiableOn ?_
      rintro w ⟨hwΩ, hw_sp⟩
      refine ⟨hwΩ, ?_⟩
      simpa [Metric.mem_sphere] using hw_sp
    have h1_mem : (1 : ℂ) ∈ Ω₁ := by simpa [Ω₁] using hz₀
    have hg_at : DifferentiableAt ℂ g 1 :=
      differentiableAt_off_unit_circle_ne_neg_one hΩ₁ hg_cont hg_diff h1_mem (by norm_num)
    have hg_at' : DifferentiableAt ℂ g (-(-1 : ℂ)) := by simpa using hg_at
    have hcomp : DifferentiableAt ℂ (g ∘ fun z : ℂ ↦ -z) (-1) :=
      hg_at'.comp (-1) differentiableAt_id.neg
    have hf_eq : (g ∘ fun z : ℂ ↦ -z) = f := by
      ext z
      simp [g]
    rwa [hf_eq] at hcomp

/-- Morera gluing across any circle `Metric.sphere c R` (`0 < R`): if `Ω ⊆ ℂ` is open, `f` is
continuous on `Ω`, and `f` is holomorphic on `Ω \ Metric.sphere c R`, then `f` is holomorphic
on `Ω`. -/
theorem holomorphic_of_continuous_off_circle {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ} (hf_cont : ContinuousOn f Ω)
    (hf_diff : DifferentiableOn ℂ f (Ω \ Metric.sphere c R)) :
    DifferentiableOn ℂ f Ω := by
  have hR_ne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  let A : ℂ → ℂ := fun w ↦ c + (R : ℂ) * w
  let B : ℂ → ℂ := fun z ↦ (z - c) / (R : ℂ)
  have hAB : ∀ z : ℂ, A (B z) = z := by
    intro z
    dsimp [A, B]
    rw [mul_div_cancel₀ _ hR_ne, add_sub_cancel]
  have hA_diff : Differentiable ℂ A :=
    (differentiable_const c).add (differentiable_id.const_mul (R : ℂ))
  have hB_diff : Differentiable ℂ B :=
    (differentiable_id.sub (differentiable_const c)).div_const (R : ℂ)
  let Ω' : Set ℂ := A ⁻¹' Ω
  have hΩ' : IsOpen Ω' := hΩ.preimage hA_diff.continuous
  let g : ℂ → ℂ := f ∘ A
  have hg_cont : ContinuousOn g Ω' :=
    hf_cont.comp hA_diff.continuous.continuousOn (fun _ hw ↦ hw)
  have hg_diff_off : DifferentiableOn ℂ g (Ω' \ Metric.sphere (0 : ℂ) 1) := by
    refine hf_diff.comp hA_diff.differentiableOn ?_
    rintro w ⟨hwΩ', hw_sp⟩
    refine ⟨hwΩ', ?_⟩
    intro hsp
    apply hw_sp
    rw [Metric.mem_sphere, dist_zero_right]
    rw [Metric.mem_sphere, dist_eq_norm] at hsp
    have hnorm : ‖c + (R : ℂ) * w - c‖ = R * ‖w‖ := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    rw [hnorm] at hsp
    exact mul_left_cancel₀ hR.ne' (hsp.trans (mul_one R).symm)
  have hg_diff : DifferentiableOn ℂ g Ω' :=
    holomorphic_of_continuous_off_unit_circle hΩ' hg_cont hg_diff_off
  have hf_eq : f = g ∘ B := by
    ext z
    simp [g, hAB z]
  rw [hf_eq]
  refine hg_diff.comp hB_diff.differentiableOn ?_
  intro z hz
  change A (B z) ∈ Ω
  rwa [hAB z]

/-- **Theorem 16.8 (Morera Gluing Across a Line or Circular Arc, Rudin RCA p. 323):**
Suppose `Ω` is a region, `C` is a straight line or circle, `S ⊆ Ω ∩ C` cuts `Ω` into two disjoint
regions `Ω₁` and `Ω₂` (`Ω \ S = Ω₁ ∪ Ω₂`), `f` is continuous on `Ω`, and `f` is holomorphic on
both `Ω₁` and `Ω₂`. Then `f` is holomorphic on all of `Ω`. -/
theorem theorem16_8 {Ω C S Ω₁ Ω₂ : Set ℂ} {f : ℂ → ℂ}
    (hΩ : RudinRCA.Chapter10.IsRegion Ω)
    (hC : IsLineOrCircle C)
    (hS : S ⊆ Ω ∩ C)
    (hΩ₁ : RudinRCA.Chapter10.IsRegion Ω₁)
    (hΩ₂ : RudinRCA.Chapter10.IsRegion Ω₂)
    (_hdisj : Disjoint Ω₁ Ω₂)
    (hcut : Ω \ S = Ω₁ ∪ Ω₂)
    (hf_cont : ContinuousOn f Ω)
    (hf₁ : DifferentiableOn ℂ f Ω₁)
    (hf₂ : DifferentiableOn ℂ f Ω₂) :
    DifferentiableOn ℂ f Ω := by
  have hf_off_C : DifferentiableOn ℂ f (Ω \ C) := by
    intro z ⟨hzΩ, hzC⟩
    have hzS : z ∉ S := fun hs ↦ hzC (hS hs).2
    have hz_union : z ∈ Ω₁ ∪ Ω₂ := hcut ▸ ⟨hzΩ, hzS⟩
    rcases hz_union with hz₁ | hz₂
    · exact (hf₁.differentiableAt (hΩ₁.1.mem_nhds hz₁)).differentiableWithinAt
    · exact (hf₂.differentiableAt (hΩ₂.1.mem_nhds hz₂)).differentiableWithinAt
  rcases hC with hline | ⟨z₀, R, hR, rfl⟩
  · exact holomorphic_of_continuous_off_line hΩ.1 hline hf_cont hf_off_C
  · exact holomorphic_of_continuous_off_circle hΩ.1 hR hf_cont hf_off_C

/-!
## 16.9: Function Elements, Direct Continuation, Disc Chains, Curve Continuation, and Non-Transitivity
-/

/-- **Definition 16.9(a) (Function element, Rudin RCA p. 323):**
An ordered pair `(f, D)` where `D = Metric.ball center radius` (`radius > 0`) is an open circular
disc and `f` is holomorphic on `D`. -/
structure FunctionElement where
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  fn : ℂ → ℂ
  holo : DifferentiableOn ℂ fn (Metric.ball center radius)

/-- The underlying open circular disc `D = Metric.ball φ.center φ.radius` of a `FunctionElement`. -/
def FunctionElement.disc (φ : FunctionElement) : Set ℂ :=
  Metric.ball φ.center φ.radius

@[simp]
theorem FunctionElement.center_mem_disc (φ : FunctionElement) : φ.center ∈ φ.disc :=
  Metric.mem_ball_self φ.radius_pos

theorem FunctionElement.isOpen_disc (φ : FunctionElement) : IsOpen φ.disc :=
  Metric.isOpen_ball

theorem FunctionElement.convex_disc (φ : FunctionElement) : Convex ℝ φ.disc :=
  convex_ball φ.center φ.radius

/-- **Definition 16.9(b) (Direct analytic continuation `(f₀, D₀) ~ (f₁, D₁)`, Rudin RCA p. 323):**
`D₀ ∩ D₁` is nonempty and `f₀(z) = f₁(z)` for every `z ∈ D₀ ∩ D₁`. -/
def DirectContinuation (φ₀ φ₁ : FunctionElement) : Prop :=
  (φ₀.disc ∩ φ₁.disc).Nonempty ∧ Set.EqOn φ₀.fn φ₁.fn (φ₀.disc ∩ φ₁.disc)

theorem DirectContinuation.refl (φ : FunctionElement) : DirectContinuation φ φ :=
  ⟨⟨φ.center, φ.center_mem_disc, φ.center_mem_disc⟩, fun _ _ ↦ rfl⟩

theorem DirectContinuation.symm {φ₀ φ₁ : FunctionElement} (h : DirectContinuation φ₀ φ₁) :
    DirectContinuation φ₁ φ₀ := by
  rw [DirectContinuation, Set.inter_comm]
  exact ⟨h.1, fun z hz ↦ (h.2 (Set.inter_comm _ _ ▸ hz)).symm⟩

/-- **Definition 16.9(c) (Chain of discs, Rudin RCA p. 323):**
A finite sequence `{D₀, D₁, …, D_n}` of open circular discs with `D_i ∩ D_{i+1} ≠ ∅` for each `i`. -/
def DiscChain {n : ℕ} (D : Fin (n + 1) → Set ℂ) : Prop :=
  (∀ i : Fin (n + 1), ∃ (c : ℂ) (r : ℝ), 0 < r ∧ D i = Metric.ball c r) ∧
    ∀ i : Fin n, (D i.castSucc ∩ D i.succ).Nonempty

/-- **Definition 16.9(d) (Analytic continuation along a chain, Rudin RCA p. 323):**
Adjacent function elements in `Φ = (Φ_0, …, Φ_n)` are direct continuations of each other. -/
def ChainContinuation {n : ℕ} (Φ : Fin (n + 1) → FunctionElement) : Prop :=
  ∀ i : Fin n, DirectContinuation (Φ i.castSucc) (Φ i.succ)

theorem ChainContinuation.discChain {n : ℕ} {Φ : Fin (n + 1) → FunctionElement}
    (h : ChainContinuation Φ) : DiscChain (fun i ↦ (Φ i).disc) :=
  ⟨fun i ↦ ⟨(Φ i).center, (Φ i).radius, (Φ i).radius_pos, rfl⟩, fun i ↦ (h i).1⟩

/-- **Uniqueness of continuation along a fixed disc chain (Rudin 16.9, pp. 323–324):**
If two chain continuations `Φ, Ψ` over the same sequence of discs agree on `D_0`, then they agree
on `D_i` for every `0 ≤ i ≤ n` (in particular, `(f_n, D_n)` is uniquely determined by `(f_0, D_0)`
and the chain `{D_0, …, D_n}`). -/
theorem chainContinuation_unique_on_discs {n : ℕ} {Φ Ψ : Fin (n + 1) → FunctionElement}
    (hΦ : ChainContinuation Φ) (hΨ : ChainContinuation Ψ)
    (hdisc : ∀ i : Fin (n + 1), (Φ i).disc = (Ψ i).disc)
    (h0 : Set.EqOn (Φ 0).fn (Ψ 0).fn (Φ 0).disc) :
    ∀ i : Fin (n + 1), Set.EqOn (Φ i).fn (Ψ i).fn (Φ i).disc := by
  intro i
  induction i using Fin.induction with
  | zero => exact h0
  | succ j ih =>
    have hover : ((Φ j.castSucc).disc ∩ (Φ j.succ).disc).Nonempty := (hΦ j).1
    obtain ⟨z₀, hz₀_prev, hz₀_curr⟩ := hover
    have hopen_inter : IsOpen ((Φ j.castSucc).disc ∩ (Φ j.succ).disc) :=
      (Φ j.castSucc).isOpen_disc.inter (Φ j.succ).isOpen_disc
    have hev : (Φ j.succ).fn =ᶠ[𝓝 z₀] (Ψ j.succ).fn := by
      filter_upwards [hopen_inter.mem_nhds ⟨hz₀_prev, hz₀_curr⟩] with z ⟨hz_prev, hz_curr⟩
      have h1 : (Φ j.castSucc).fn z = (Φ j.succ).fn z := (hΦ j).2 ⟨hz_prev, hz_curr⟩
      have hz_Ψ : z ∈ (Ψ j.castSucc).disc ∩ (Ψ j.succ).disc := by
        rw [← hdisc j.castSucc, ← hdisc j.succ]
        exact ⟨hz_prev, hz_curr⟩
      have h2 : (Ψ j.castSucc).fn z = (Ψ j.succ).fn z := (hΨ j).2 hz_Ψ
      exact h1.symm.trans ((ih hz_prev).trans h2)
    have hΦ_ana : AnalyticOnNhd ℂ (Φ j.succ).fn (Φ j.succ).disc :=
      (Φ j.succ).holo.analyticOnNhd (Φ j.succ).isOpen_disc
    have hΨ_holo : DifferentiableOn ℂ (Ψ j.succ).fn (Φ j.succ).disc := by
      rw [hdisc j.succ]
      exact (Ψ j.succ).holo
    have hΨ_ana : AnalyticOnNhd ℂ (Ψ j.succ).fn (Φ j.succ).disc :=
      hΨ_holo.analyticOnNhd (Φ j.succ).isOpen_disc
    exact hΦ_ana.eqOn_of_preconnected_of_eventuallyEq hΨ_ana
      (Φ j.succ).convex_disc.isPreconnected hz₀_curr hev

/-- Specialization of `chainContinuation_unique_on_discs` when `Φ 0 = Ψ 0`. -/
theorem chainContinuation_unique {n : ℕ} {Φ Ψ : Fin (n + 1) → FunctionElement}
    (hΦ : ChainContinuation Φ) (hΨ : ChainContinuation Ψ)
    (h0 : Φ 0 = Ψ 0)
    (hdisc : ∀ i : Fin (n + 1), (Φ i).disc = (Ψ i).disc) :
    ∀ i : Fin (n + 1), Set.EqOn (Φ i).fn (Ψ i).fn (Φ i).disc :=
  chainContinuation_unique_on_discs hΦ hΨ hdisc (fun _ _ ↦ by rw [h0])

/-- **Definition 16.9(e) (Chain covering a curve, Rudin RCA p. 324):**
For a continuous curve `γ : ℝ → ℂ` on `[a, b]` (`a ≤ b`), the discs of `Φ : Fin (n + 1) → FunctionElement`
cover `γ` if `(Φ 0).center = γ a`, `(Φ n).center = γ b`, and there exist partition points
`a = s_0 ≤ s_1 ≤ … ≤ s_{n+1} = b` such that `γ([s_i, s_{i+1}]) ⊆ (Φ i).disc` for `0 ≤ i ≤ n`. -/
def ChainCoversCurve {n : ℕ} (Φ : Fin (n + 1) → FunctionElement)
    (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  a ≤ b ∧ ContinuousOn γ (Set.Icc a b) ∧
    (Φ 0).center = γ a ∧ (Φ (Fin.last n)).center = γ b ∧
    ∃ s : Fin (n + 2) → ℝ,
      s 0 = a ∧ s (Fin.last (n + 1)) = b ∧ Monotone s ∧
      ∀ i : Fin (n + 1), γ '' Set.Icc (s i.castSucc) (s i.succ) ⊆ (Φ i).disc

theorem ChainCoversCurve.discChain {n : ℕ} {Φ : Fin (n + 1) → FunctionElement}
    {γ : ℝ → ℂ} {a b : ℝ} (hcov : ChainCoversCurve Φ γ a b) :
    DiscChain (fun i ↦ (Φ i).disc) := by
  obtain ⟨_, _, _, _, s, _, _, hs_mono, hsub⟩ := hcov
  refine ⟨fun i ↦ ⟨(Φ i).center, (Φ i).radius, (Φ i).radius_pos, rfl⟩, fun j ↦ ?_⟩
  let t_mid := s j.castSucc.succ
  have ht_left : t_mid ∈ Set.Icc (s j.castSucc.castSucc) (s j.castSucc.succ) :=
    ⟨hs_mono j.castSucc.castSucc_le_succ, le_rfl⟩
  have heq_idx : j.castSucc.succ = j.succ.castSucc := Fin.ext (by simp)
  have ht_right : t_mid ∈ Set.Icc (s j.succ.castSucc) (s j.succ.succ) := by
    dsimp [t_mid]
    rw [heq_idx]
    exact ⟨le_rfl, hs_mono j.succ.castSucc_le_succ⟩
  exact ⟨γ t_mid, hsub j.castSucc ⟨t_mid, ht_left, rfl⟩, hsub j.succ ⟨t_mid, ht_right, rfl⟩⟩

/-- **Definition 16.9(f) (Analytic continuation along a curve on `[0, 1]`, Rudin RCA p. 324):**
`φ₁` is obtained from `φ₀` by analytic continuation along `γ : [0, 1] → ℂ` if there is a chain
`Φ = (Φ_0, …, Φ_n)` with `Φ 0 = φ₀`, `Φ n = φ₁`, `ChainContinuation Φ`, and `ChainCoversCurve Φ γ 0 1`. -/
def ContinuedAlongCurve (φ₀ : FunctionElement) (γ : ℝ → ℂ) (φ₁ : FunctionElement) : Prop :=
  ∃ (n : ℕ) (Φ : Fin (n + 1) → FunctionElement),
    Φ 0 = φ₀ ∧ Φ (Fin.last n) = φ₁ ∧
    ChainContinuation Φ ∧ ChainCoversCurve Φ γ 0 1

/-- Strengthened curve continuation whose chain discs all lie inside a region `Ω ⊆ ℂ`. -/
def ContinuedAlongCurveIn (Ω : Set ℂ) (φ₀ : FunctionElement) (γ : ℝ → ℂ)
    (φ₁ : FunctionElement) : Prop :=
  ∃ (n : ℕ) (Φ : Fin (n + 1) → FunctionElement),
    Φ 0 = φ₀ ∧ Φ (Fin.last n) = φ₁ ∧
    (∀ i : Fin (n + 1), (Φ i).disc ⊆ Ω) ∧
    ChainContinuation Φ ∧ ChainCoversCurve Φ γ 0 1

theorem ContinuedAlongCurveIn.toContinuedAlongCurve {Ω : Set ℂ}
    {φ₀ : FunctionElement} {γ : ℝ → ℂ} {φ₁ : FunctionElement}
    (h : ContinuedAlongCurveIn Ω φ₀ γ φ₁) : ContinuedAlongCurve φ₀ γ φ₁ := by
  obtain ⟨n, Φ, h0, hn, _, hch, hcov⟩ := h
  exact ⟨n, Φ, h0, hn, hch, hcov⟩

theorem ContinuedAlongCurve.centers {φ₀ : FunctionElement} {γ : ℝ → ℂ} {φ₁ : FunctionElement}
    (h : ContinuedAlongCurve φ₀ γ φ₁) : φ₀.center = γ 0 ∧ φ₁.center = γ 1 := by
  obtain ⟨n, Φ, rfl, rfl, _, _, _, h0, h1, _⟩ := h
  exact ⟨h0, h1⟩

theorem ContinuedAlongCurve.congr_curve {φ₀ : FunctionElement} {γ γ' : ℝ → ℂ}
    {φ₁ : FunctionElement} (h : ContinuedAlongCurve φ₀ γ φ₁)
    (heq : Set.EqOn γ γ' (Set.Icc 0 1)) :
    ContinuedAlongCurve φ₀ γ' φ₁ := by
  obtain ⟨n, Φ, hΦ0, hΦlast, hch, hle, hγ_cont, hc0, hc1, s, hs0, hsn, hs_mono, hsub⟩ := h
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  refine ⟨n, Φ, hΦ0, hΦlast, hch, hle, hγ_cont.congr (fun t ht ↦ (heq ht).symm),
    hc0.trans (heq h0_mem), hc1.trans (heq h1_mem), s, hs0, hsn, hs_mono, ?_⟩
  intro i
  rintro _ ⟨t, ht, rfl⟩
  have ht01 : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hs0 ▸ (hs_mono (Fin.zero_le i.castSucc)).trans ht.1,
     ht.2.trans (hsn ▸ hs_mono (Fin.le_last i.succ))⟩
  rw [← heq ht01]
  exact hsub i ⟨t, ht, rfl⟩

/-- **Non-transitivity of `DirectContinuation` via branches of `√z` (Rudin 16.9, p. 324):**
There exist three function elements `φ₀, φ₁, φ₂` representing branches of `√z` (`(f_i(z))^2 = z`
on `D_i`) such that `φ₀ ~ φ₁`, `φ₁ ~ φ₂`, and `D₀ ∩ D₂` is nonempty, yet `¬ (φ₀ ~ φ₂)`. -/
theorem directContinuation_not_transitive_sqrt :
    ∃ φ₀ φ₁ φ₂ : FunctionElement,
      DirectContinuation φ₀ φ₁ ∧
      DirectContinuation φ₁ φ₂ ∧
      (φ₀.disc ∩ φ₂.disc).Nonempty ∧
      (∀ i : Fin ([φ₀, φ₁, φ₂].length),
        ∀ z ∈ ([φ₀, φ₁, φ₂].get i).disc, (([φ₀, φ₁, φ₂].get i).fn z) ^ 2 = z) ∧
      ¬ DirectContinuation φ₀ φ₂ := by
  let c₀ : ℂ := 1
  let r₀ : ℝ := 1
  let c₁ : ℂ := -1 + I
  let r₁ : ℝ := 7 / 5
  let c₂ : ℂ := -1 - I
  let r₂ : ℝ := 7 / 5
  have hD₀_slit : ∀ z ∈ Metric.ball c₀ r₀, z ∈ Complex.slitPlane := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hre : |z.re - 1| ≤ ‖z - 1‖ := by simpa using Complex.abs_re_le_norm (z - 1)
    have hlt : |z.re - 1| < 1 := lt_of_le_of_lt hre hz
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [(abs_lt.mp hlt).1]))
  have hD₁_slit : ∀ z ∈ Metric.ball c₁ r₁, -I * z ∈ Complex.slitPlane := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hsq : Complex.normSq (z - (-1 + I)) < (7 / 5 : ℝ) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_lt_pow_left₀ hz (norm_nonneg _) two_ne_zero
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.neg_re,
      Complex.one_re, Complex.I_re, Complex.sub_im, Complex.add_im, Complex.neg_im,
      Complex.one_im, Complex.I_im] at hsq
    rw [Complex.mem_slitPlane_iff]
    by_contra hnot
    push Not at hnot
    have him : z.im ≤ 0 := by simpa using hnot.1
    have hre : z.re = 0 := by
      have : -z.re = 0 := by simpa using hnot.2
      linarith
    rw [hre] at hsq
    nlinarith
  have hD₂_slit : ∀ z ∈ Metric.ball c₂ r₂, I * z ∈ Complex.slitPlane := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hsq : Complex.normSq (z - (-1 - I)) < (7 / 5 : ℝ) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_lt_pow_left₀ hz (norm_nonneg _) two_ne_zero
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.neg_re,
      Complex.one_re, Complex.I_re, Complex.sub_im, Complex.neg_im,
      Complex.one_im, Complex.I_im] at hsq
    rw [Complex.mem_slitPlane_iff]
    by_contra hnot
    push Not at hnot
    have him : 0 ≤ z.im := by
      have : -z.im ≤ 0 := by simpa using hnot.1
      linarith
    have hre : z.re = 0 := by simpa using hnot.2
    rw [hre] at hsq
    nlinarith
  let L₀ : ℂ → ℂ := fun z ↦ Complex.log z
  let L₁ : ℂ → ℂ := fun z ↦ Complex.log (-I * z) + (Real.pi / 2 : ℝ) * I
  let L₂ : ℂ → ℂ := fun z ↦ Complex.log (I * z) + (3 * Real.pi / 2 : ℝ) * I
  have hL₀_holo : DifferentiableOn ℂ L₀ (Metric.ball c₀ r₀) :=
    differentiableOn_id.clog hD₀_slit
  have hL₁_holo : DifferentiableOn ℂ L₁ (Metric.ball c₁ r₁) :=
    ((differentiableOn_id.const_mul (-I)).clog hD₁_slit).add (differentiableOn_const _)
  have hL₂_holo : DifferentiableOn ℂ L₂ (Metric.ball c₂ r₂) :=
    ((differentiableOn_id.const_mul I).clog hD₂_slit).add (differentiableOn_const _)
  have hL₀_exp : ∀ z ∈ Metric.ball c₀ r₀, Complex.exp (L₀ z) = z := fun z hz ↦
    Complex.exp_log (Complex.slitPlane_ne_zero (hD₀_slit z hz))
  have hL₁_exp : ∀ z ∈ Metric.ball c₁ r₁, Complex.exp (L₁ z) = z := by
    intro z hz
    dsimp [L₁]
    rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (hD₁_slit z hz))]
    have hexp_pi2 : Complex.exp ((Real.pi / 2 : ℝ) * I) = I := by
      rw [Complex.exp_mul_I]
      simp
    rw [hexp_pi2]
    ring_nf
    simp
  have hL₂_exp : ∀ z ∈ Metric.ball c₂ r₂, Complex.exp (L₂ z) = z := by
    intro z hz
    dsimp [L₂]
    rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (hD₂_slit z hz))]
    have hexp_3pi2 : Complex.exp ((3 * Real.pi / 2 : ℝ) * I) = -I := by
      have hsplit : ((3 * Real.pi / 2 : ℝ) * I : ℂ) = (Real.pi : ℂ) * I + (Real.pi / 2 : ℝ) * I := by
        push_cast
        ring
      rw [hsplit, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_mul_I]
      simp
    rw [hexp_3pi2]
    ring_nf
    simp
  let f₀ : ℂ → ℂ := fun z ↦ Complex.exp (L₀ z / 2)
  let f₁ : ℂ → ℂ := fun z ↦ Complex.exp (L₁ z / 2)
  let f₂ : ℂ → ℂ := fun z ↦ Complex.exp (L₂ z / 2)
  let φ₀ : FunctionElement :=
    ⟨c₀, r₀, by norm_num, f₀, (hL₀_holo.div_const 2).cexp⟩
  let φ₁ : FunctionElement :=
    ⟨c₁, r₁, by norm_num, f₁, (hL₁_holo.div_const 2).cexp⟩
  let φ₂ : FunctionElement :=
    ⟨c₂, r₂, by norm_num, f₂, (hL₂_holo.div_const 2).cexp⟩
  have hsq₀ : ∀ z ∈ φ₀.disc, (φ₀.fn z) ^ 2 = z := by
    intro z hz
    dsimp [φ₀, f₀]
    rw [sq, ← Complex.exp_add, add_halves, hL₀_exp z hz]
  have hsq₁ : ∀ z ∈ φ₁.disc, (φ₁.fn z) ^ 2 = z := by
    intro z hz
    dsimp [φ₁, f₁]
    rw [sq, ← Complex.exp_add, add_halves, hL₁_exp z hz]
  have hsq₂ : ∀ z ∈ φ₂.disc, (φ₂.fn z) ^ 2 = z := by
    intro z hz
    dsimp [φ₂, f₂]
    rw [sq, ← Complex.exp_add, add_halves, hL₂_exp z hz]
  have mem_ball_of_normSq {z c : ℂ} {r : ℝ} (_hr : 0 < r)
      (h : Complex.normSq (z - c) < r ^ 2) : z ∈ Metric.ball c r := by
    rw [Metric.mem_ball, dist_eq_norm]
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (z - c)]
  let z₀₁ : ℂ := (1 / 4 : ℂ) + (1 / 2 : ℂ) * I
  let z₁₂ : ℂ := -1
  let z₀₂ : ℂ := (1 / 4 : ℂ) - (1 / 2 : ℂ) * I
  have hz₀₁_0 : z₀₁ ∈ φ₀.disc := by
    change z₀₁ ∈ Metric.ball c₀ r₀
    apply mem_ball_of_normSq (by norm_num)
    simp [z₀₁, c₀, r₀, Complex.normSq_apply]
    norm_num
  have hz₀₁_1 : z₀₁ ∈ φ₁.disc := by
    change z₀₁ ∈ Metric.ball c₁ r₁
    apply mem_ball_of_normSq (by norm_num)
    simp [z₀₁, c₁, r₁, Complex.normSq_apply]
    norm_num
  have hz₁₂_1 : z₁₂ ∈ φ₁.disc := by
    change z₁₂ ∈ Metric.ball c₁ r₁
    apply mem_ball_of_normSq (by norm_num)
    simp [z₁₂, c₁, r₁, Complex.normSq_apply]
    norm_num
  have hz₁₂_2 : z₁₂ ∈ φ₂.disc := by
    change z₁₂ ∈ Metric.ball c₂ r₂
    apply mem_ball_of_normSq (by norm_num)
    simp [z₁₂, c₂, r₂, Complex.normSq_apply]
    norm_num
  have hz₀₂_0 : z₀₂ ∈ φ₀.disc := by
    change z₀₂ ∈ Metric.ball c₀ r₀
    apply mem_ball_of_normSq (by norm_num)
    simp [z₀₂, c₀, r₀, Complex.normSq_apply]
    norm_num
  have hz₀₂_2 : z₀₂ ∈ φ₂.disc := by
    change z₀₂ ∈ Metric.ball c₂ r₂
    apply mem_ball_of_normSq (by norm_num)
    simp [z₀₂, c₂, r₂, Complex.normSq_apply]
    norm_num
  have hlog_eqOn {U : Set ℂ} (hU_open : IsOpen U) (hU_conv : Convex ℝ U)
      {g₁ g₂ : ℂ → ℂ} (hg₁ : DifferentiableOn ℂ g₁ U) (hg₂ : DifferentiableOn ℂ g₂ U)
      (hexp₁ : ∀ z ∈ U, Complex.exp (g₁ z) = z) (hexp₂ : ∀ z ∈ U, Complex.exp (g₂ z) = z)
      (hne0 : ∀ z ∈ U, z ≠ 0) {w : ℂ} (hw : w ∈ U) (heqw : g₁ w = g₂ w) :
      Set.EqOn g₁ g₂ U := by
    have hderiv_eq : ∀ z ∈ U, deriv (g₁ - g₂) z = 0 := by
      intro z hz
      have hnhds : U ∈ 𝓝 z := hU_open.mem_nhds hz
      have hd₁ : HasDerivAt g₁ (deriv g₁ z) z := (hg₁.differentiableAt hnhds).hasDerivAt
      have hd₂ : HasDerivAt g₂ (deriv g₂ z) z := (hg₂.differentiableAt hnhds).hasDerivAt
      have hev₁ : (fun ζ ↦ Complex.exp (g₁ ζ)) =ᶠ[𝓝 z] id :=
        Filter.eventuallyEq_of_mem hnhds hexp₁
      have hev₂ : (fun ζ ↦ Complex.exp (g₂ ζ)) =ᶠ[𝓝 z] id :=
        Filter.eventuallyEq_of_mem hnhds hexp₂
      have h1 : Complex.exp (g₁ z) * deriv g₁ z = 1 :=
        (hd₁.cexp.congr_of_eventuallyEq hev₁.symm).unique (hasDerivAt_id z)
      have h2 : Complex.exp (g₂ z) * deriv g₂ z = 1 :=
        (hd₂.cexp.congr_of_eventuallyEq hev₂.symm).unique (hasDerivAt_id z)
      rw [hexp₁ z hz] at h1
      rw [hexp₂ z hz] at h2
      have hdg : deriv g₁ z = deriv g₂ z :=
        mul_left_cancel₀ (hne0 z hz) (h1.trans h2.symm)
      rw [(hd₁.sub hd₂).deriv, hdg, sub_self]
    intro z hz
    have hconst := hU_open.is_const_of_deriv_eq_zero hU_conv.isPreconnected
      (hg₁.sub hg₂) hderiv_eq hz hw
    change g₁ z - g₂ z = g₁ w - g₂ w at hconst
    rw [heqw, sub_self] at hconst
    exact sub_eq_zero.mp hconst
  have hdc₀₁ : DirectContinuation φ₀ φ₁ := by
    refine ⟨⟨z₀₁, hz₀₁_0, hz₀₁_1⟩, ?_⟩
    have hz₀₁_ne : z₀₁ ≠ 0 := Complex.slitPlane_ne_zero (hD₀_slit z₀₁ hz₀₁_0)
    have harg_ge : 0 ≤ Complex.arg z₀₁ :=
      Complex.arg_nonneg_iff.mpr (by simp [z₀₁] : (0 : ℝ) ≤ z₀₁.im)
    have harg_le : Complex.arg z₀₁ ≤ Real.pi := Complex.arg_le_pi z₀₁
    have hlog_mul₁ : Complex.log (-I * z₀₁) = Complex.log (-I) + Complex.log z₀₁ := by
      apply Complex.log_mul (neg_ne_zero.mpr Complex.I_ne_zero) hz₀₁_ne
      rw [Complex.arg_neg_I]
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hL_eq_pt : L₀ z₀₁ = L₁ z₀₁ := by
      dsimp [L₀, L₁]
      rw [hlog_mul₁, Complex.log_neg_I]
      push_cast
      ring
    have hL_eq : Set.EqOn L₀ L₁ (φ₀.disc ∩ φ₁.disc) :=
      hlog_eqOn (φ₀.isOpen_disc.inter φ₁.isOpen_disc) (φ₀.convex_disc.inter φ₁.convex_disc)
        (hL₀_holo.mono inter_subset_left) (hL₁_holo.mono inter_subset_right)
        (fun z hz ↦ hL₀_exp z hz.1) (fun z hz ↦ hL₁_exp z hz.2)
        (fun z hz ↦ Complex.slitPlane_ne_zero (hD₀_slit z hz.1))
        ⟨hz₀₁_0, hz₀₁_1⟩ hL_eq_pt
    intro z hz
    dsimp [φ₀, φ₁, f₀, f₁]
    rw [hL_eq hz]
  have hdc₁₂ : DirectContinuation φ₁ φ₂ := by
    refine ⟨⟨z₁₂, hz₁₂_1, hz₁₂_2⟩, ?_⟩
    have hL_eq_pt : L₁ z₁₂ = L₂ z₁₂ := by
      dsimp [L₁, L₂, z₁₂]
      have h1 : -I * (-1 : ℂ) = I := by ring
      have h2 : I * (-1 : ℂ) = -I := by ring
      rw [h1, h2, Complex.log_I, Complex.log_neg_I]
      push_cast
      ring
    have hL_eq : Set.EqOn L₁ L₂ (φ₁.disc ∩ φ₂.disc) :=
      hlog_eqOn (φ₁.isOpen_disc.inter φ₂.isOpen_disc) (φ₁.convex_disc.inter φ₂.convex_disc)
        (hL₁_holo.mono inter_subset_left) (hL₂_holo.mono inter_subset_right)
        (fun z hz ↦ hL₁_exp z hz.1) (fun z hz ↦ hL₂_exp z hz.2)
        (fun z hz ↦ by
          rw [← hL₁_exp z hz.1]
          exact Complex.exp_ne_zero _)
        ⟨hz₁₂_1, hz₁₂_2⟩ hL_eq_pt
    intro z hz
    dsimp [φ₁, φ₂, f₁, f₂]
    rw [hL_eq hz]
  have hnot_dc₀₂ : ¬ DirectContinuation φ₀ φ₂ := by
    intro hdc₀₂
    have hz₀₂_ne : z₀₂ ≠ 0 := Complex.slitPlane_ne_zero (hD₀_slit z₀₂ hz₀₂_0)
    have harg_lt : Complex.arg z₀₂ < 0 :=
      Complex.arg_neg_iff.mpr (by simp [z₀₂] : z₀₂.im < 0)
    have harg_gt : -Real.pi < Complex.arg z₀₂ := Complex.neg_pi_lt_arg z₀₂
    have hlog_mul₂ : Complex.log (I * z₀₂) = Complex.log I + Complex.log z₀₂ := by
      apply Complex.log_mul Complex.I_ne_zero hz₀₂_ne
      rw [Complex.arg_I]
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hL₂_pt : L₂ z₀₂ = L₀ z₀₂ + 2 * (Real.pi : ℂ) * I := by
      dsimp [L₀, L₂]
      rw [hlog_mul₂, Complex.log_I]
      push_cast
      ring
    have hf₂_pt : φ₂.fn z₀₂ = -φ₀.fn z₀₂ := by
      dsimp [φ₀, φ₂, f₀, f₂]
      rw [hL₂_pt]
      have hdiv : (L₀ z₀₂ + 2 * (Real.pi : ℂ) * I) / 2 = L₀ z₀₂ / 2 + (Real.pi : ℂ) * I := by
        ring
      rw [hdiv, Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    have heq_pt : φ₀.fn z₀₂ = φ₂.fn z₀₂ := hdc₀₂.2 ⟨hz₀₂_0, hz₀₂_2⟩
    rw [hf₂_pt] at heq_pt
    have h0_fn : φ₀.fn z₀₂ = 0 := by linear_combination (1 / 2 : ℂ) * heq_pt
    have hsq_pt := hsq₀ z₀₂ hz₀₂_0
    rw [h0_fn, zero_pow two_ne_zero] at hsq_pt
    exact hz₀₂_ne hsq_pt.symm
  refine ⟨φ₀, φ₁, φ₂, hdc₀₁, hdc₁₂, ⟨z₀₂, hz₀₂_0, hz₀₂_2⟩, ?_, hnot_dc₀₂⟩
  intro i
  fin_cases i
  · exact hsq₀
  · exact hsq₁
  · exact hsq₂

/-- **Node 16.9 (Combined Chain-Uniqueness and Non-Transitivity Package, Rudin RCA pp. 323–324):**
1. Analytic continuation along any fixed disc chain is unique on every disc of the chain;
2. Direct continuation is not transitive in general (square-root counterexample). -/
theorem theorem16_9 :
    (∀ {n : ℕ} {Φ Ψ : Fin (n + 1) → FunctionElement},
      ChainContinuation Φ → ChainContinuation Ψ →
      (∀ i : Fin (n + 1), (Φ i).disc = (Ψ i).disc) →
      Set.EqOn (Φ 0).fn (Ψ 0).fn (Φ 0).disc →
      ∀ i : Fin (n + 1), Set.EqOn (Φ i).fn (Ψ i).fn (Φ i).disc) ∧
    (∃ φ₀ φ₁ φ₂ : FunctionElement,
      DirectContinuation φ₀ φ₁ ∧
      DirectContinuation φ₁ φ₂ ∧
      (φ₀.disc ∩ φ₂.disc).Nonempty ∧
      (∀ i : Fin ([φ₀, φ₁, φ₂].length),
        ∀ z ∈ ([φ₀, φ₁, φ₂].get i).disc, (([φ₀, φ₁, φ₂].get i).fn z) ^ 2 = z) ∧
      ¬ DirectContinuation φ₀ φ₂) :=
  ⟨fun hΦ hΨ hdisc h0 ↦ chainContinuation_unique_on_discs hΦ hΨ hdisc h0,
   directContinuation_not_transitive_sqrt⟩

/-!
## 16.10: Transitivity of Direct Continuation on Three Discs with a Common Point
-/

/-- **Proposition 16.10 (Triple-Intersection Transitivity of Direct Continuation, Rudin RCA p. 324):**
If `φ₀ ~ φ₁`, `φ₁ ~ φ₂`, and `D₀ ∩ D₁ ∩ D₂ ≠ ∅`, then `φ₀ ~ φ₂`. -/
theorem theorem16_10 {φ₀ φ₁ φ₂ : FunctionElement}
    (h₀₁ : DirectContinuation φ₀ φ₁)
    (h₁₂ : DirectContinuation φ₁ φ₂)
    (hinter : (φ₀.disc ∩ φ₁.disc ∩ φ₂.disc).Nonempty) :
    DirectContinuation φ₀ φ₂ := by
  obtain ⟨z₀, ⟨hz₀_0, hz₀_1⟩, hz₀_2⟩ := hinter
  refine ⟨⟨z₀, hz₀_0, hz₀_2⟩, ?_⟩
  have hU_open : IsOpen (φ₀.disc ∩ φ₂.disc) := φ₀.isOpen_disc.inter φ₂.isOpen_disc
  have hU_pre : IsPreconnected (φ₀.disc ∩ φ₂.disc) :=
    (φ₀.convex_disc.inter φ₂.convex_disc).isPreconnected
  have hV_open : IsOpen (φ₀.disc ∩ φ₁.disc ∩ φ₂.disc) :=
    (φ₀.isOpen_disc.inter φ₁.isOpen_disc).inter φ₂.isOpen_disc
  have hev : φ₀.fn =ᶠ[𝓝 z₀] φ₂.fn := by
    filter_upwards [hV_open.mem_nhds ⟨⟨hz₀_0, hz₀_1⟩, hz₀_2⟩] with z ⟨⟨hz0, hz1⟩, hz2⟩
    exact (h₀₁.2 ⟨hz0, hz1⟩).trans (h₁₂.2 ⟨hz1, hz2⟩)
  have h₀_ana : AnalyticOnNhd ℂ φ₀.fn (φ₀.disc ∩ φ₂.disc) :=
    (φ₀.holo.mono inter_subset_left).analyticOnNhd hU_open
  have h₂_ana : AnalyticOnNhd ℂ φ₂.fn (φ₀.disc ∩ φ₂.disc) :=
    (φ₂.holo.mono inter_subset_right).analyticOnNhd hU_open
  exact h₀_ana.eqOn_of_preconnected_of_eventuallyEq h₂_ana hU_pre ⟨hz₀_0, hz₀_2⟩ hev

/-!
## 16.11: Uniqueness of Analytic Continuation Along a Curve
-/

/-- Every point `t ∈ [a, b]` belongs to at least one subinterval `[s_i, s_{i+1}]` of a monotone
partition `a = s_0 ≤ … ≤ s_{n+1} = b`. -/
private theorem exists_subinterval_of_monotone :
    ∀ {n : ℕ} {a b : ℝ} (s : Fin (n + 2) → ℝ),
      s 0 = a → s (Fin.last (n + 1)) = b → Monotone s →
      ∀ {t : ℝ}, t ∈ Set.Icc a b → ∃ i : Fin (n + 1), t ∈ Set.Icc (s i.castSucc) (s i.succ)
  | 0, a, b, s, hs0, hsn, _, t, ht => by
    refine ⟨0, ?_⟩
    have h0 : (0 : Fin 1).castSucc = 0 := rfl
    have h1 : (0 : Fin 1).succ = Fin.last 1 := rfl
    rw [h0, h1, hs0, hsn]
    exact ht
  | m + 1, a, b, s, hs0, hsn, hs, t, ht => by
    let p := s (Fin.last (m + 1)).castSucc
    rcases le_total t p with hle | hge
    · let s' : Fin (m + 2) → ℝ := fun j ↦ s j.castSucc
      have hs'0 : s' 0 = a := hs0
      have hs'n : s' (Fin.last (m + 1)) = p := rfl
      have hs'_mono : Monotone s' := fun j₁ j₂ hj ↦ hs (Fin.castSucc_le_castSucc_iff.mpr hj)
      obtain ⟨i, hi⟩ := exists_subinterval_of_monotone s' hs'0 hs'n hs'_mono ⟨ht.1, hle⟩
      refine ⟨i.castSucc, ?_⟩
      have hsucc : i.castSucc.succ = i.succ.castSucc := Fin.ext (by simp)
      dsimp [s'] at hi
      rwa [hsucc]
    · refine ⟨Fin.last (m + 1), hge, ?_⟩
      have hlast : (Fin.last (m + 1)).succ = Fin.last (m + 2) := Fin.ext (by simp)
      rw [hlast, hsn]
      exact ht.2

/-- If a point `z` lies in `(Φ k).disc` for all `i₁ ≤ k ≤ i₂` along a `ChainContinuation Φ`,
then `DirectContinuation (Φ i₁) (Φ i₂)` holds (iterated Proposition 16.10). -/
private theorem chain_directContinuation_of_le {m : ℕ} {Φ : Fin (m + 1) → FunctionElement}
    (hΦ : ChainContinuation Φ) {z : ℂ} :
    ∀ (d : ℕ) {i₁ i₂ : Fin (m + 1)},
      i₂.val = i₁.val + d →
      (∀ k : Fin (m + 1), i₁ ≤ k → k ≤ i₂ → z ∈ (Φ k).disc) →
      DirectContinuation (Φ i₁) (Φ i₂)
  | 0, i₁, i₂, hd, _ => by
    have heq : i₁ = i₂ := Fin.ext (by omega)
    rw [heq]
    exact DirectContinuation.refl _
  | d + 1, i₁, i₂, hd, hz => by
    have hk_lt : i₁.val + d < m := by omega
    let k : Fin m := ⟨i₁.val + d, hk_lt⟩
    have hk_succ : k.succ = i₂ := Fin.ext (by simp [k]; omega)
    have hi₁_le_k : i₁ ≤ k.castSucc := Fin.le_def.mpr (by simp [k])
    have hk_le_i₂ : k.castSucc ≤ i₂ := Fin.le_def.mpr (by simp [k]; omega)
    have hdc₁ : DirectContinuation (Φ i₁) (Φ k.castSucc) :=
      chain_directContinuation_of_le hΦ d (i₂ := k.castSucc) rfl
        (fun j hj₁ hj₂ ↦ hz j hj₁ (hj₂.trans hk_le_i₂))
    have hdc₂ : DirectContinuation (Φ k.castSucc) (Φ i₂) := hk_succ ▸ hΦ k
    exact theorem16_10 hdc₁ hdc₂
      ⟨z, ⟨hz i₁ le_rfl (hi₁_le_k.trans hk_le_i₂), hz k.castSucc hi₁_le_k hk_le_i₂⟩,
       hz i₂ (hi₁_le_k.trans hk_le_i₂) le_rfl⟩

/-- If `t` lies in both `[s_{i₁}, s_{i₁+1}]` and `[s_{i₂}, s_{i₂+1}]` of a covering chain `Φ`,
then `γ t ∈ (Φ i₁).disc ∩ (Φ i₂).disc` and `DirectContinuation (Φ i₁) (Φ i₂)` holds. -/
private theorem chainCovers_directContinuation_of_mem_both {m : ℕ}
    {Φ : Fin (m + 1) → FunctionElement} {γ : ℝ → ℂ} {s : Fin (m + 2) → ℝ}
    (hΦ : ChainContinuation Φ) (hs : Monotone s)
    (hsub : ∀ i : Fin (m + 1), γ '' Set.Icc (s i.castSucc) (s i.succ) ⊆ (Φ i).disc)
    {t : ℝ} {i₁ i₂ : Fin (m + 1)}
    (ht₁ : t ∈ Set.Icc (s i₁.castSucc) (s i₁.succ))
    (ht₂ : t ∈ Set.Icc (s i₂.castSucc) (s i₂.succ)) :
    DirectContinuation (Φ i₁) (Φ i₂) := by
  have haux : ∀ {a b : Fin (m + 1)}, a ≤ b →
      t ∈ Set.Icc (s a.castSucc) (s a.succ) →
      t ∈ Set.Icc (s b.castSucc) (s b.succ) →
      DirectContinuation (Φ a) (Φ b) := by
    intro a b hab ha hb
    refine chain_directContinuation_of_le hΦ (b.val - a.val) (z := γ t)
      (by have : a.val ≤ b.val := hab; omega) ?_
    intro k hak hkb
    have hk_mem : t ∈ Set.Icc (s k.castSucc) (s k.succ) :=
      ⟨(hs (Fin.castSucc_le_castSucc_iff.mpr hkb)).trans hb.1,
       ha.2.trans (hs (Fin.succ_le_succ_iff.mpr hak))⟩
    exact hsub k ⟨t, hk_mem, rfl⟩
  rcases le_total i₁ i₂ with hle | hge
  · exact haux hle ht₁ ht₂
  · exact (haux hge ht₂ ht₁).symm

/-- Neighborhood around `t₀` in which every subinterval `[s_i, s_{i+1}]` containing `t'` also
contains `t₀`. -/
private theorem eventually_subinterval_contains_center {m : ℕ} (s : Fin (m + 2) → ℝ) (t₀ : ℝ) :
    ∀ᶠ t' in 𝓝 t₀, ∀ i : Fin (m + 1),
      t' ∈ Set.Icc (s i.castSucc) (s i.succ) → t₀ ∈ Set.Icc (s i.castSucc) (s i.succ) := by
  let bad : Set ℝ :=
    ⋃ i ∈ ({i : Fin (m + 1) | t₀ ∉ Set.Icc (s i.castSucc) (s i.succ)} : Set (Fin (m + 1))),
      Set.Icc (s i.castSucc) (s i.succ)
  have hbad_closed : IsClosed bad :=
    (Set.toFinite _).isClosed_biUnion (fun _ _ ↦ isClosed_Icc)
  have ht₀_not : t₀ ∉ bad := by
    rintro ⟨_, ⟨i, rfl⟩, _, ⟨hnot : t₀ ∉ Set.Icc (s i.castSucc) (s i.succ), rfl⟩, ht₀⟩
    exact hnot ht₀
  filter_upwards [hbad_closed.isOpen_compl.mem_nhds ht₀_not] with t' ht' i hi
  by_contra hnot
  exact ht' (Set.mem_biUnion hnot hi)

/-- **Theorem 16.11 (Uniqueness of Analytic Continuation Along a Curve, Rudin RCA pp. 324–325):**
If `φ₀` is continued along the same continuous curve `γ : [0, 1] → ℂ` (`γ(0) = φ₀.center`) to
both `φ₁` and `φ₂`, then `φ₁ ~ φ₂` (`DirectContinuation φ₁ φ₂`), `φ₁.fn =ᶠ[𝓝 (γ 1)] φ₂.fn`,
`φ₁.fn (γ 1) = φ₂.fn (γ 1)`, and `φ₁.fn` agrees with `φ₂.fn` on `φ₁.disc ∩ φ₂.disc`. -/
theorem theorem16_11 {φ₀ φ₁ φ₂ : FunctionElement} {γ : ℝ → ℂ}
    (_hγ : ContinuousOn γ (Set.Icc 0 1))
    (h₁ : ContinuedAlongCurve φ₀ γ φ₁)
    (h₂ : ContinuedAlongCurve φ₀ γ φ₂) :
    DirectContinuation φ₁ φ₂ ∧
      φ₁.fn =ᶠ[𝓝 (γ 1)] φ₂.fn ∧
      φ₁.fn (γ 1) = φ₂.fn (γ 1) ∧
      Set.EqOn φ₁.fn φ₂.fn (φ₁.disc ∩ φ₂.disc) := by
  obtain ⟨m, Φ, hΦ0, hΦlast, hΦ_ch, _, _, _, hcΦ1, s, hs0, hsn, hs_mono, hs_sub⟩ := h₁
  obtain ⟨n, Ψ, hΨ0, hΨlast, hΨ_ch, _, _, _, hcΨ1, u, hu0, hun, hu_mono, hu_sub⟩ := h₂
  let P : ℝ → Prop := fun t ↦
    ∀ (i : Fin (m + 1)) (j : Fin (n + 1)),
      t ∈ Set.Icc (s i.castSucc) (s i.succ) →
      t ∈ Set.Icc (u j.castSucc) (u j.succ) →
      DirectContinuation (Φ i) (Ψ j)
  -- Any single pair `(i₀, j₀)` covering `t` with `Φ i₀ ~ Ψ j₀` upgrades to `P t`
  have hupgrade : ∀ {t : ℝ} {i₀ : Fin (m + 1)} {j₀ : Fin (n + 1)},
      t ∈ Set.Icc (s i₀.castSucc) (s i₀.succ) →
      t ∈ Set.Icc (u j₀.castSucc) (u j₀.succ) →
      DirectContinuation (Φ i₀) (Ψ j₀) → P t := by
    intro t i₀ j₀ hti₀ htj₀ hdc i j hti htj
    have hdc_Φ : DirectContinuation (Φ i) (Φ i₀) :=
      chainCovers_directContinuation_of_mem_both hΦ_ch hs_mono hs_sub hti hti₀
    have hdc_Ψ : DirectContinuation (Ψ j₀) (Ψ j) :=
      chainCovers_directContinuation_of_mem_both hΨ_ch hu_mono hu_sub htj₀ htj
    have hz_Φi : γ t ∈ (Φ i).disc := hs_sub i ⟨t, hti, rfl⟩
    have hz_Φi₀ : γ t ∈ (Φ i₀).disc := hs_sub i₀ ⟨t, hti₀, rfl⟩
    have hz_Ψj₀ : γ t ∈ (Ψ j₀).disc := hu_sub j₀ ⟨t, htj₀, rfl⟩
    have hz_Ψj : γ t ∈ (Ψ j).disc := hu_sub j ⟨t, htj, rfl⟩
    have hdc_mid : DirectContinuation (Φ i) (Ψ j₀) :=
      theorem16_10 hdc_Φ hdc ⟨γ t, ⟨hz_Φi, hz_Φi₀⟩, hz_Ψj₀⟩
    exact theorem16_10 hdc_mid hdc_Ψ ⟨γ t, ⟨hz_Φi, hz_Ψj₀⟩, hz_Ψj⟩
  -- `P 0` holds since `Φ 0 = φ₀ = Ψ 0`
  have hP0 : P 0 := by
    have h0_s : (0 : ℝ) ∈ Set.Icc (s (0 : Fin (m + 1)).castSucc) (s (0 : Fin (m + 1)).succ) := by
      have hc : (0 : Fin (m + 1)).castSucc = 0 := rfl
      rw [hc, hs0]
      exact ⟨le_rfl, hs0 ▸ hs_mono (Fin.zero_le _)⟩
    have h0_u : (0 : ℝ) ∈ Set.Icc (u (0 : Fin (n + 1)).castSucc) (u (0 : Fin (n + 1)).succ) := by
      have hc : (0 : Fin (n + 1)).castSucc = 0 := rfl
      rw [hc, hu0]
      exact ⟨le_rfl, hu0 ▸ hu_mono (Fin.zero_le _)⟩
    have hdc0 : DirectContinuation (Φ 0) (Ψ 0) := by
      rw [hΦ0, hΨ0]
      exact DirectContinuation.refl φ₀
    exact hupgrade h0_s h0_u hdc0
  -- Clopenness of `{t | P t}` on `[0, 1]`
  let U_pos : Set ℝ := {t : ℝ | ∀ᶠ t' in 𝓝 t, P t'}
  let U_neg : Set ℝ := {t : ℝ | ∀ᶠ t' in 𝓝 t, t' ∈ Set.Icc 0 1 → ¬ P t'}
  have hU_pos_open : IsOpen U_pos := isOpen_iff_mem_nhds.mpr fun t ht ↦ eventually_eventually_nhds.mpr ht
  have hU_neg_open : IsOpen U_neg := isOpen_iff_mem_nhds.mpr fun t ht ↦ eventually_eventually_nhds.mpr ht
  have hcov_01 : Set.Icc (0 : ℝ) 1 ⊆ U_pos ∪ U_neg := by
    intro t ht
    by_cases hPt : P t
    · left
      filter_upwards [eventually_subinterval_contains_center s t,
        eventually_subinterval_contains_center u t] with t' hts htu i j hti htj
      exact hPt i j (hts i hti) (htu j htj)
    · right
      filter_upwards [eventually_subinterval_contains_center s t,
        eventually_subinterval_contains_center u t] with t' hts htu ht'01 hPt'
      obtain ⟨i, hti⟩ := exists_subinterval_of_monotone s hs0 hsn hs_mono ht'01
      obtain ⟨j, htj⟩ := exists_subinterval_of_monotone u hu0 hun hu_mono ht'01
      exact hPt (hupgrade (hts i hti) (htu j htj) (hPt' i j hti htj))
  have h0_in_pos : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∩ U_pos := by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    rcases hcov_01 ⟨le_rfl, zero_le_one⟩ with hpos | hneg
    · exact hpos
    · exfalso
      exact hneg.self_of_nhds ⟨le_rfl, zero_le_one⟩ hP0
  have hall : ∀ t ∈ Set.Icc (0 : ℝ) 1, P t := by
    intro t ht
    by_contra hnot
    have ht_neg : t ∈ Set.Icc (0 : ℝ) 1 ∩ U_neg := by
      refine ⟨ht, ?_⟩
      rcases hcov_01 ht with hpos | hneg
      · exact False.elim (hnot hpos.self_of_nhds)
      · exact hneg
    obtain ⟨w, hw01, hw_pos, hw_neg⟩ :=
      isPreconnected_Icc U_pos U_neg hU_pos_open hU_neg_open hcov_01 ⟨0, h0_in_pos⟩ ⟨t, ht_neg⟩
    exact hw_neg.self_of_nhds hw01 hw_pos.self_of_nhds
  have hP1 : P 1 := hall 1 ⟨zero_le_one, le_rfl⟩
  have h1_s : (1 : ℝ) ∈ Set.Icc (s (Fin.last m).castSucc) (s (Fin.last m).succ) := by
    have hl : (Fin.last m).succ = Fin.last (m + 1) := Fin.ext (by simp)
    rw [hl, hsn]
    exact ⟨hsn ▸ hs_mono (Fin.le_last _), le_rfl⟩
  have h1_u : (1 : ℝ) ∈ Set.Icc (u (Fin.last n).castSucc) (u (Fin.last n).succ) := by
    have hl : (Fin.last n).succ = Fin.last (n + 1) := Fin.ext (by simp)
    rw [hl, hun]
    exact ⟨hun ▸ hu_mono (Fin.le_last _), le_rfl⟩
  have hdc₁₂ : DirectContinuation φ₁ φ₂ := by
    rw [← hΦlast, ← hΨlast]
    exact hP1 (Fin.last m) (Fin.last n) h1_s h1_u
  have hγ1_mem : γ 1 ∈ φ₁.disc ∩ φ₂.disc := by
    have hc1 : φ₁.center = γ 1 := hΦlast ▸ hcΦ1
    have hc2 : φ₂.center = γ 1 := hΨlast ▸ hcΨ1
    exact ⟨hc1 ▸ φ₁.center_mem_disc, hc2 ▸ φ₂.center_mem_disc⟩
  have hev : φ₁.fn =ᶠ[𝓝 (γ 1)] φ₂.fn :=
    Filter.eventuallyEq_of_mem ((φ₁.isOpen_disc.inter φ₂.isOpen_disc).mem_nhds hγ1_mem) hdc₁₂.2
  exact ⟨hdc₁₂, hev, hev.eq_of_nhds, hdc₁₂.2⟩

/-!
## 16.12: One-Parameter Families of Curves with Fixed Endpoints
-/

/-- **Definition 16.12 (One-parameter family of curves with common endpoints, Rudin RCA p. 325):**
A continuous mapping `Γ : [0, 1] × [0, 1] → E` into `X ⊆ E` such that for every `u ∈ [0, 1]`,
the curve `t ↦ Γ(t, u)` begins at `z₀` (`Γ(0, u) = z₀`) and ends at `z₁` (`Γ(1, u) = z₁`). -/
def IsEndpointFixedCurveFamily {E : Type*} [TopologicalSpace E]
    (Γ : ℝ × ℝ → E) (X : Set E) (z₀ z₁ : E) : Prop :=
  ContinuousOn Γ (Set.Icc 0 1 ×ˢ Set.Icc 0 1) ∧
    Set.MapsTo Γ (Set.Icc 0 1 ×ˢ Set.Icc 0 1) X ∧
    ∀ u ∈ Set.Icc (0 : ℝ) 1, Γ (0, u) = z₀ ∧ Γ (1, u) = z₁

/-- **Node 16.12 (Slice Properties and `Path.Homotopy` Bridge):**
Every parameter value `u ∈ [0, 1]` of an `IsEndpointFixedCurveFamily Γ X z₀ z₁` yields a continuous
curve `t ↦ Γ(t, u)` in `X` from `z₀` to `z₁`, and `Γ` induces a `Path.Homotopy` in the subtype `X`
between its `u = 0` and `u = 1` boundary curves. -/
theorem theorem16_12 {E : Type*} [TopologicalSpace E]
    {Γ : ℝ × ℝ → E} {X : Set E} {z₀ z₁ : E}
    (hΓ : IsEndpointFixedCurveFamily Γ X z₀ z₁) :
    (∀ u ∈ Set.Icc (0 : ℝ) 1,
      ContinuousOn (fun t ↦ Γ (t, u)) (Set.Icc 0 1) ∧
      (fun t ↦ Γ (t, u)) '' Set.Icc 0 1 ⊆ X ∧
      Γ (0, u) = z₀ ∧ Γ (1, u) = z₁) ∧
    ∃ (hz₀ : z₀ ∈ X) (hz₁ : z₁ ∈ X) (p₀ p₁ : Path (⟨z₀, hz₀⟩ : X) ⟨z₁, hz₁⟩),
      (∀ t : unitInterval, (p₀ t).1 = Γ (t.1, 0) ∧ (p₁ t).1 = Γ (t.1, 1)) ∧
      Nonempty (Path.Homotopy p₀ p₁) := by
  obtain ⟨hcont, hmaps, hend⟩ := hΓ
  have hslice : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ContinuousOn (fun t ↦ Γ (t, u)) (Set.Icc 0 1) ∧
      (fun t ↦ Γ (t, u)) '' Set.Icc 0 1 ⊆ X ∧
      Γ (0, u) = z₀ ∧ Γ (1, u) = z₁ := by
    intro u hu
    refine ⟨hcont.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht ↦ ⟨ht, hu⟩),
      ?_, hend u hu⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hmaps ⟨ht, hu⟩
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hz₀ : z₀ ∈ X := (hend 0 h0_mem).1 ▸ hmaps ⟨h0_mem, h0_mem⟩
  have hz₁ : z₁ ∈ X := (hend 0 h0_mem).2 ▸ hmaps ⟨h1_mem, h0_mem⟩
  let p₀ : Path (⟨z₀, hz₀⟩ : X) ⟨z₁, hz₁⟩ :=
    { toFun := fun t ↦ ⟨Γ (t.1, 0), hmaps ⟨t.2, h0_mem⟩⟩
      continuous_toFun := Continuous.subtype_mk
        (hcont.comp_continuous (continuous_subtype_val.prodMk continuous_const)
          (fun t ↦ ⟨t.2, h0_mem⟩)) _
      source' := Subtype.ext (hend 0 h0_mem).1
      target' := Subtype.ext (hend 0 h0_mem).2 }
  let p₁ : Path (⟨z₀, hz₀⟩ : X) ⟨z₁, hz₁⟩ :=
    { toFun := fun t ↦ ⟨Γ (t.1, 1), hmaps ⟨t.2, h1_mem⟩⟩
      continuous_toFun := Continuous.subtype_mk
        (hcont.comp_continuous (continuous_subtype_val.prodMk continuous_const)
          (fun t ↦ ⟨t.2, h1_mem⟩)) _
      source' := Subtype.ext (hend 1 h1_mem).1
      target' := Subtype.ext (hend 1 h1_mem).2 }
  refine ⟨hslice, hz₀, hz₁, p₀, p₁, fun _ ↦ ⟨rfl, rfl⟩, ⟨?_⟩⟩
  exact
    { toFun := fun q ↦ ⟨Γ (q.2.1, q.1.1), hmaps ⟨q.2.2, q.1.2⟩⟩
      continuous_toFun := Continuous.subtype_mk
        (hcont.comp_continuous
          ((continuous_subtype_val.comp continuous_snd).prodMk
            (continuous_subtype_val.comp continuous_fst))
          (fun q ↦ ⟨q.2.2, q.1.2⟩)) _
      map_zero_left := fun t ↦ rfl
      map_one_left := fun t ↦ rfl
      prop' := by
        rintro u t (rfl | rfl)
        · exact Subtype.ext ((hend u.1 u.2).1.trans (hend 0 h0_mem).1.symm)
        · exact Subtype.ext ((hend u.1 u.2).2.trans (hend 0 h0_mem).2.symm) }

/-!
## 16.13: Homotopy Invariance of Analytic Continuation Along a Curve Family
-/

/-- Local stability of chain coverage across nearby curves in an `IsEndpointFixedCurveFamily`:
a chain `Φ` continuing `φ₀` along `t ↦ Γ(t, u₀)` also continues `φ₀` along `t ↦ Γ(t, u)` for
all `u ∈ [0, 1]` sufficiently close to `u₀`. -/
private theorem eventually_continuedAlongCurve_slice {Ω : Set ℂ} {Γ : ℝ × ℝ → ℂ} {z₀ z₁ : ℂ}
    (hΓ : IsEndpointFixedCurveFamily Γ Ω z₀ z₁)
    {φ₀ : FunctionElement} {u₀ : ℝ} (hu₀ : u₀ ∈ Set.Icc (0 : ℝ) 1)
    {ψ₀ : FunctionElement}
    (hcont₀ : ContinuedAlongCurve φ₀ (fun t ↦ Γ (t, u₀)) ψ₀) :
    ∀ᶠ u in 𝓝 u₀, u ∈ Set.Icc (0 : ℝ) 1 →
      ContinuedAlongCurve φ₀ (fun t ↦ Γ (t, u)) ψ₀ := by
  obtain ⟨n, Φ, hΦ0, hΦlast, hΦ_ch, _, _, hc0, hc1, s, hs0, hsn, hs_mono, hs_sub⟩ := hcont₀
  -- Positive clearance `ε_i > 0` on each compact subinterval `[s_i, s_{i+1}]`
  have hmargin : ∀ i : Fin (n + 1), ∃ ε > 0,
      ∀ t ∈ Set.Icc (s i.castSucc) (s i.succ),
        dist (Γ (t, u₀)) (Φ i).center + ε ≤ (Φ i).radius := by
    intro i
    let K : Set ℝ := Set.Icc (s i.castSucc) (s i.succ)
    have hK_comp : IsCompact K := isCompact_Icc
    have hK_ne : K.Nonempty := ⟨s i.castSucc, ⟨le_rfl, hs_mono i.castSucc_le_succ⟩⟩
    have hK_sub : K ⊆ Set.Icc (0 : ℝ) 1 :=
      fun t ht ↦ ⟨hs0 ▸ (hs_mono (Fin.zero_le i.castSucc)).trans ht.1,
        ht.2.trans (hsn ▸ hs_mono (Fin.le_last i.succ))⟩
    have hslice_cont : ContinuousOn (fun t ↦ (Φ i).radius - dist (Γ (t, u₀)) (Φ i).center) K :=
      continuousOn_const.sub
        (continuous_dist.comp_continuousOn
          ((hΓ.1.comp (continuousOn_id.prodMk continuousOn_const)
            (fun t ht ↦ ⟨hK_sub ht, hu₀⟩)).prodMk continuousOn_const))
    obtain ⟨t_min, ht_min, hmin⟩ := hK_comp.exists_isMinOn hK_ne hslice_cont
    have hpos : 0 < (Φ i).radius - dist (Γ (t_min, u₀)) (Φ i).center := by
      have hmem : Γ (t_min, u₀) ∈ (Φ i).disc := hs_sub i ⟨t_min, ht_min, rfl⟩
      rw [FunctionElement.disc, Metric.mem_ball] at hmem
      linarith
    refine ⟨(Φ i).radius - dist (Γ (t_min, u₀)) (Φ i).center, hpos, fun t ht ↦ ?_⟩
    have hle : (Φ i).radius - dist (Γ (t_min, u₀)) (Φ i).center ≤
        (Φ i).radius - dist (Γ (t, u₀)) (Φ i).center := hmin ht
    linarith
  choose ε hε_pos hε_le using hmargin
  let ε_min : ℝ := Finset.univ.inf' Finset.univ_nonempty ε
  have hε_min_pos : 0 < ε_min :=
    (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ ↦ hε_pos i)
  let Q : Set (ℝ × ℝ) := Set.Icc 0 1 ×ˢ Set.Icc 0 1
  have hQ_comp : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hunif : UniformContinuousOn Γ Q := hQ_comp.uniformContinuousOn_of_continuous hΓ.1
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hunif ε_min hε_min_pos
  filter_upwards [Metric.ball_mem_nhds u₀ hδ_pos] with u hu_ball hu01
  refine ⟨n, Φ, hΦ0, hΦlast, hΦ_ch, zero_le_one,
    hΓ.1.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht ↦ ⟨ht, hu01⟩),
    hc0.trans ((hΓ.2.2 u₀ hu₀).1.trans (hΓ.2.2 u hu01).1.symm),
    hc1.trans ((hΓ.2.2 u₀ hu₀).2.trans (hΓ.2.2 u hu01).2.symm),
    s, hs0, hsn, hs_mono, ?_⟩
  intro i
  rintro _ ⟨t, ht, rfl⟩
  have ht01 : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hs0 ▸ (hs_mono (Fin.zero_le i.castSucc)).trans ht.1,
     ht.2.trans (hsn ▸ hs_mono (Fin.le_last i.succ))⟩
  have hdist_lt : dist (Γ (t, u)) (Γ (t, u₀)) < ε_min := by
    apply hδ (t, u) ⟨ht01, hu01⟩ (t, u₀) ⟨ht01, hu₀⟩
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
    exact Metric.mem_ball.mp hu_ball
  have hε_i : ε_min ≤ ε i := Finset.inf'_le ε (Finset.mem_univ i)
  rw [FunctionElement.disc, Metric.mem_ball]
  calc dist (Γ (t, u)) (Φ i).center
      ≤ dist (Γ (t, u)) (Γ (t, u₀)) + dist (Γ (t, u₀)) (Φ i).center := dist_triangle _ _ _
    _ < ε i + dist (Γ (t, u₀)) (Φ i).center := by linarith
    _ ≤ (Φ i).radius := by linarith [hε_le i t ht]

/-- **Theorem 16.13 (Homotopy Invariance of Analytic Continuation, Rudin RCA pp. 325–326):**
Suppose `Γ` is a one-parameter family of curves with common endpoints `z₀` and `z₁`, `φ₀` is a
function element centered at `z₀`, and for each `u ∈ [0, 1]`, `φ₀` can be continued along
`γ_u(t) = Γ(t, u)` to `ψ u`. Then for all `u, v ∈ [0, 1]`, `ψ u ~ ψ v` and
`(ψ u).fn =ᶠ[𝓝 z₁] (ψ v).fn` (in particular, `ψ 0 ~ ψ 1`, `(ψ 0).fn =ᶠ[𝓝 z₁] (ψ 1).fn`,
`Set.EqOn (ψ 0).fn (ψ 1).fn ((ψ 0).disc ∩ (ψ 1).disc)`, and `(ψ 0).fn z₁ = (ψ 1).fn z₁`). -/
theorem theorem16_13 {Ω : Set ℂ} {Γ : ℝ × ℝ → ℂ} {z₀ z₁ : ℂ}
    (hΓ : IsEndpointFixedCurveFamily Γ Ω z₀ z₁)
    {φ₀ : FunctionElement} (_hφ₀ : φ₀.center = z₀)
    {ψ : ℝ → FunctionElement}
    (hψ : ∀ u ∈ Set.Icc (0 : ℝ) 1, ContinuedAlongCurve φ₀ (fun t ↦ Γ (t, u)) (ψ u)) :
    (∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      DirectContinuation (ψ u) (ψ v) ∧ (ψ u).fn =ᶠ[𝓝 z₁] (ψ v).fn) ∧
    DirectContinuation (ψ 0) (ψ 1) ∧
    (ψ 0).fn =ᶠ[𝓝 z₁] (ψ 1).fn ∧
    Set.EqOn (ψ 0).fn (ψ 1).fn ((ψ 0).disc ∩ (ψ 1).disc) ∧
    (ψ 0).fn z₁ = (ψ 1).fn z₁ := by
  have hz₁_mem : ∀ u ∈ Set.Icc (0 : ℝ) 1, z₁ ∈ (ψ u).disc := by
    intro u hu
    have hc : (ψ u).center = z₁ := (hψ u hu).centers.2.trans (hΓ.2.2 u hu).2
    exact hc ▸ (ψ u).center_mem_disc
  have hnear : ∀ u₀ ∈ Set.Icc (0 : ℝ) 1, ∀ᶠ u in 𝓝 u₀,
      u ∈ Set.Icc (0 : ℝ) 1 → DirectContinuation (ψ u) (ψ u₀) := by
    intro u₀ hu₀
    filter_upwards [eventually_continuedAlongCurve_slice hΓ hu₀ (hψ u₀ hu₀)] with u hu hu01
    have hγu_cont : ContinuousOn (fun t ↦ Γ (t, u)) (Set.Icc 0 1) :=
      hΓ.1.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht ↦ ⟨ht, hu01⟩)
    exact (theorem16_11 hγu_cont (hψ u hu01) (hu hu01)).1
  have hall : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      DirectContinuation (ψ u) (ψ v) ∧ (ψ u).fn =ᶠ[𝓝 z₁] (ψ v).fn := by
    intro u₀ hu₀ v hv
    let U_pos : Set ℝ := {u : ℝ | ∀ᶠ u' in 𝓝 u, u' ∈ Set.Icc (0 : ℝ) 1 → DirectContinuation (ψ u') (ψ v)}
    let U_neg : Set ℝ := {u : ℝ | ∀ᶠ u' in 𝓝 u, u' ∈ Set.Icc (0 : ℝ) 1 → ¬ DirectContinuation (ψ u') (ψ v)}
    have hpos_open : IsOpen U_pos := isOpen_iff_mem_nhds.mpr fun _ h ↦ eventually_eventually_nhds.mpr h
    have hneg_open : IsOpen U_neg := isOpen_iff_mem_nhds.mpr fun _ h ↦ eventually_eventually_nhds.mpr h
    have hcov : Set.Icc (0 : ℝ) 1 ⊆ U_pos ∪ U_neg := by
      intro u hu
      by_cases hdc : DirectContinuation (ψ u) (ψ v)
      · left
        filter_upwards [hnear u hu] with u' hu' hu'01
        exact theorem16_10 (hu' hu'01) hdc ⟨z₁, ⟨hz₁_mem u' hu'01, hz₁_mem u hu⟩, hz₁_mem v hv⟩
      · right
        filter_upwards [hnear u hu] with u' hu' hu'01 hdc'
        exact hdc (theorem16_10 (hu' hu'01).symm hdc'
          ⟨z₁, ⟨hz₁_mem u hu, hz₁_mem u' hu'01⟩, hz₁_mem v hv⟩)
    have hv_pos : v ∈ Set.Icc (0 : ℝ) 1 ∩ U_pos := by
      refine ⟨hv, ?_⟩
      rcases hcov hv with hp | hn
      · exact hp
      · exfalso
        exact hn.self_of_nhds hv (DirectContinuation.refl _)
    have hdc_uv : DirectContinuation (ψ u₀) (ψ v) := by
      by_contra hnot
      have hu₀_neg : u₀ ∈ Set.Icc (0 : ℝ) 1 ∩ U_neg := by
        refine ⟨hu₀, ?_⟩
        rcases hcov hu₀ with hp | hn
        · exact False.elim (hnot (hp.self_of_nhds hu₀))
        · exact hn
      obtain ⟨w, hw01, hwp, hwn⟩ :=
        isPreconnected_Icc U_pos U_neg hpos_open hneg_open hcov ⟨v, hv_pos⟩ ⟨u₀, hu₀_neg⟩
      exact hwn.self_of_nhds hw01 (hwp.self_of_nhds hw01)
    have hev_uv : (ψ u₀).fn =ᶠ[𝓝 z₁] (ψ v).fn :=
      Filter.eventuallyEq_of_mem
        (((ψ u₀).isOpen_disc.inter (ψ v).isOpen_disc).mem_nhds ⟨hz₁_mem u₀ hu₀, hz₁_mem v hv⟩)
        hdc_uv.2
    exact ⟨hdc_uv, hev_uv⟩
  obtain ⟨hdc01, hev01⟩ := hall 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
  exact ⟨hall, hdc01, hev01, hdc01.2, hev01.eq_of_nhds⟩

/-!
## 16.14: Endpoint-Fixed Homotopy Between Curves in a Simply Connected Space
-/

/-- **Theorem 16.14 (Endpoint-Fixed Homotopy in a Simply Connected Space, Rudin RCA p. 326):**
In any simply connected topological space `X`, any two continuous curves `γ₀, γ₁ : [0, 1] → X`
sharing common endpoints `γ₀(0) = γ₁(0) = x₀` and `γ₀(1) = γ₁(1) = x₁` are joined by an
endpoint-fixed one-parameter family `Γ : [0, 1]² → X` with `Γ(t, 0) = γ₀(t)` and `Γ(t, 1) = γ₁(t)`. -/
theorem theorem16_14 {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
    {γ₀ γ₁ : ℝ → X} {x₀ x₁ : X}
    (hγ₀ : ContinuousOn γ₀ (Set.Icc 0 1))
    (hγ₁ : ContinuousOn γ₁ (Set.Icc 0 1))
    (h0₀ : γ₀ 0 = x₀) (h0₁ : γ₁ 0 = x₀)
    (h1₀ : γ₀ 1 = x₁) (h1₁ : γ₁ 1 = x₁) :
    ∃ Γ : ℝ × ℝ → X,
      IsEndpointFixedCurveFamily Γ Set.univ x₀ x₁ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Γ (t, 0) = γ₀ t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Γ (t, 1) = γ₁ t) := by
  let p₀ : Path x₀ x₁ :=
    { toFun := fun t ↦ γ₀ t.1
      continuous_toFun := hγ₀.comp_continuous continuous_subtype_val (fun t ↦ t.2)
      source' := h0₀
      target' := h1₀ }
  let p₁ : Path x₀ x₁ :=
    { toFun := fun t ↦ γ₁ t.1
      continuous_toFun := hγ₁.comp_continuous continuous_subtype_val (fun t ↦ t.2)
      source' := h0₁
      target' := h1₁ }
  obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic p₀ p₁
  let proj : ℝ → unitInterval := Set.projIcc (0 : ℝ) 1 zero_le_one
  let Γ : ℝ × ℝ → X := fun q ↦ F (proj q.2, proj q.1)
  have hΓ_cont : Continuous Γ :=
    F.continuous.comp ((continuous_projIcc.comp continuous_snd).prodMk
      (continuous_projIcc.comp continuous_fst))
  have hproj_eq : ∀ {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1), proj s = ⟨s, hs⟩ :=
    fun hs ↦ Set.projIcc_of_mem zero_le_one hs
  have hproj_0 : proj 0 = 0 := Set.projIcc_left zero_le_one
  have hproj_1 : proj 1 = 1 := Set.projIcc_right zero_le_one
  refine ⟨Γ, ⟨hΓ_cont.continuousOn, Set.mapsTo_univ _ _, ?_⟩, ?_, ?_⟩
  · intro u hu
    dsimp [Γ]
    rw [hproj_0, hproj_1, hproj_eq hu]
    exact ⟨F.source ⟨u, hu⟩, F.target ⟨u, hu⟩⟩
  · intro t ht
    dsimp [Γ]
    rw [hproj_0, hproj_eq ht]
    exact F.map_zero_left ⟨t, ht⟩
  · intro t ht
    dsimp [Γ]
    rw [hproj_1, hproj_eq ht]
    exact F.map_one_left ⟨t, ht⟩

/-- Equivalence between Rudin's `BookSimplyConnected Ω` and Mathlib's `SimplyConnectedSpace Ω`
(`IsSimplyConnected Ω`) on plane regions `Ω ⊆ ℂ` (via Theorem 13.11 `(a) ↔ (b)`). -/
theorem bookSimplyConnected_iff_simplyConnectedSpace {Ω : Set ℂ}
    (hΩ : RudinRCA.Chapter10.IsRegion Ω) :
    RudinRCA.Chapter10.BookSimplyConnected Ω ↔ SimplyConnectedSpace Ω := by
  constructor
  · intro hsc
    obtain ⟨e⟩ := (RudinRCA.Chapter13.theorem13_11 hΩ).2.1.mpr hsc
    have : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
      (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, Metric.mem_ball_self zero_lt_one⟩
    exact e.toHomotopyEquiv.simplyConnectedSpace
  · intro hsc
    refine ⟨hΩ, fun γ hγ_cont hγ_Ω hγ_cl ↦ ?_⟩
    have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    let z₀ : Ω := ⟨γ 0, hγ_Ω ⟨0, h0_mem, rfl⟩⟩
    let p : Path z₀ z₀ :=
      { toFun := fun t ↦ ⟨γ t.1, hγ_Ω ⟨t.1, t.2, rfl⟩⟩
        continuous_toFun := Continuous.subtype_mk
          (hγ_cont.comp_continuous continuous_subtype_val (fun t ↦ t.2)) _
        source' := rfl
        target' := Subtype.ext hγ_cl.symm }
    obtain ⟨F⟩ := @SimplyConnectedSpace.paths_homotopic Ω _ hsc z₀ z₀ p (Path.refl z₀)
    let proj : ℝ → unitInterval := Set.projIcc (0 : ℝ) 1 zero_le_one
    let H : ℝ × ℝ → ℂ := fun q ↦ (F (proj q.2, proj q.1)).1
    have hH_cont : Continuous H :=
      continuous_subtype_val.comp (F.continuous.comp
        ((continuous_projIcc.comp continuous_snd).prodMk
          (continuous_projIcc.comp continuous_fst)))
    refine ⟨z₀.1, z₀.2, hγ_cont, continuousOn_const, hγ_Ω,
      (by rintro _ ⟨_, _, rfl⟩; exact z₀.2), hγ_cl, rfl, H, hH_cont.continuousOn, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨q, _, rfl⟩
      exact (F (proj q.2, proj q.1)).2
    · intro s hs
      dsimp [H, proj]
      rw [Set.projIcc_left zero_le_one, Set.projIcc_of_mem zero_le_one hs]
      exact congrArg Subtype.val (F.map_zero_left ⟨s, hs⟩)
    · intro s hs
      dsimp [H, proj]
      rw [Set.projIcc_right zero_le_one, Set.projIcc_of_mem zero_le_one hs]
      exact congrArg Subtype.val (F.map_one_left ⟨s, hs⟩)
    · intro u hu
      dsimp [H, proj]
      rw [Set.projIcc_left zero_le_one, Set.projIcc_right zero_le_one,
        Set.projIcc_of_mem zero_le_one hu]
      change (F (⟨u, hu⟩, 0)).1 = (F (⟨u, hu⟩, 1)).1
      rw [F.source ⟨u, hu⟩, F.target ⟨u, hu⟩]

/-- Plane-region corollary of Theorem 16.14 for `BookSimplyConnected Ω`. -/
theorem theorem16_14_bookSimplyConnected {Ω : Set ℂ}
    (hsc : RudinRCA.Chapter10.BookSimplyConnected Ω)
    {γ₀ γ₁ : ℝ → ℂ} {z₀ z₁ : ℂ}
    (hγ₀ : ContinuousOn γ₀ (Set.Icc 0 1))
    (hγ₁ : ContinuousOn γ₁ (Set.Icc 0 1))
    (hΩ₀ : γ₀ '' Set.Icc 0 1 ⊆ Ω)
    (hΩ₁ : γ₁ '' Set.Icc 0 1 ⊆ Ω)
    (h0₀ : γ₀ 0 = z₀) (h0₁ : γ₁ 0 = z₀)
    (h1₀ : γ₀ 1 = z₁) (h1₁ : γ₁ 1 = z₁) :
    ∃ Γ : ℝ × ℝ → ℂ,
      IsEndpointFixedCurveFamily Γ Ω z₀ z₁ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Γ (t, 0) = γ₀ t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Γ (t, 1) = γ₁ t) := by
  have : SimplyConnectedSpace Ω :=
    (bookSimplyConnected_iff_simplyConnectedSpace hsc.1).mp hsc
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hz₀ : z₀ ∈ Ω := hΩ₀ ⟨0, h0_mem, h0₀⟩
  have hz₁ : z₁ ∈ Ω := hΩ₀ ⟨1, h1_mem, h1₀⟩
  let proj : ℝ → unitInterval := Set.projIcc (0 : ℝ) 1 zero_le_one
  let γ₀_sub : ℝ → Ω := fun t ↦ ⟨γ₀ (proj t).1, hΩ₀ ⟨(proj t).1, (proj t).2, rfl⟩⟩
  let γ₁_sub : ℝ → Ω := fun t ↦ ⟨γ₁ (proj t).1, hΩ₁ ⟨(proj t).1, (proj t).2, rfl⟩⟩
  have hγ₀_sub : ContinuousOn γ₀_sub (Set.Icc 0 1) :=
    (Continuous.subtype_mk
      (hγ₀.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        (fun t ↦ (proj t).2)) _).continuousOn
  have hγ₁_sub : ContinuousOn γ₁_sub (Set.Icc 0 1) :=
    (Continuous.subtype_mk
      (hγ₁.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        (fun t ↦ (proj t).2)) _).continuousOn
  have h0₀_sub : γ₀_sub 0 = ⟨z₀, hz₀⟩ := by
    apply Subtype.ext
    dsimp [γ₀_sub, proj]
    rw [Set.projIcc_left zero_le_one]
    exact h0₀
  have h0₁_sub : γ₁_sub 0 = ⟨z₀, hz₀⟩ := by
    apply Subtype.ext
    dsimp [γ₁_sub, proj]
    rw [Set.projIcc_left zero_le_one]
    exact h0₁
  have h1₀_sub : γ₀_sub 1 = ⟨z₁, hz₁⟩ := by
    apply Subtype.ext
    dsimp [γ₀_sub, proj]
    rw [Set.projIcc_right zero_le_one]
    exact h1₀
  have h1₁_sub : γ₁_sub 1 = ⟨z₁, hz₁⟩ := by
    apply Subtype.ext
    dsimp [γ₁_sub, proj]
    rw [Set.projIcc_right zero_le_one]
    exact h1₁
  obtain ⟨Γ_sub, ⟨hΓ_cont, _, hΓ_end⟩, hΓ_0, hΓ_1⟩ :=
    theorem16_14 hγ₀_sub hγ₁_sub h0₀_sub h0₁_sub h1₀_sub h1₁_sub
  refine ⟨fun q ↦ (Γ_sub q).1, ⟨continuous_subtype_val.comp_continuousOn hΓ_cont,
    fun q _ ↦ (Γ_sub q).2, fun u hu ↦ ⟨congrArg Subtype.val (hΓ_end u hu).1,
      congrArg Subtype.val (hΓ_end u hu).2⟩⟩, ?_, ?_⟩
  · intro t ht
    have h := congrArg Subtype.val (hΓ_0 t ht)
    dsimp [γ₀_sub, proj] at h
    rwa [Set.projIcc_of_mem zero_le_one ht] at h
  · intro t ht
    have h := congrArg Subtype.val (hΓ_1 t ht)
    dsimp [γ₁_sub, proj] at h
    rwa [Set.projIcc_of_mem zero_le_one ht] at h

/-!
## 16.15: The Monodromy Theorem
-/

/-- **Continuability hypothesis of the Monodromy Theorem (Rudin RCA 16.15, p. 327):**
`φ₀` has disc `D₀ ⊆ Ω` and admits analytic continuation along every continuous curve
`γ : [0, 1] → Ω` starting at `φ₀.center` (allowing arbitrary chain discs in `ℂ`, as in 16.9). -/
def CanContinueInRegion (Ω : Set ℂ) (φ₀ : FunctionElement) : Prop :=
  φ₀.disc ⊆ Ω ∧
    ∀ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) →
      γ 0 = φ₀.center → γ '' Set.Icc 0 1 ⊆ Ω →
      ∃ φ₁ : FunctionElement, ContinuedAlongCurve φ₀ γ φ₁

/-- Strengthened continuability hypothesis in `Ω` requiring all chain discs to lie inside `Ω`. -/
def CanContinueWithinRegion (Ω : Set ℂ) (φ₀ : FunctionElement) : Prop :=
  φ₀.disc ⊆ Ω ∧
    ∀ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) →
      γ 0 = φ₀.center → γ '' Set.Icc 0 1 ⊆ Ω →
      ∃ φ₁ : FunctionElement, ContinuedAlongCurveIn Ω φ₀ γ φ₁

theorem CanContinueWithinRegion.toCanContinueInRegion {Ω : Set ℂ} {φ₀ : FunctionElement}
    (h : CanContinueWithinRegion Ω φ₀) : CanContinueInRegion Ω φ₀ :=
  ⟨h.1, fun γ hγ h0 hΩ ↦
    let ⟨φ₁, hφ₁⟩ := h.2 γ hγ h0 hΩ
    ⟨φ₁, hφ₁.toContinuedAlongCurve⟩⟩

/-- Every function element `φ₀` continues along the constant curve at `φ₀.center` to itself. -/
theorem continuedAlongCurve_const (φ₀ : FunctionElement) :
    ContinuedAlongCurve φ₀ (fun _ ↦ φ₀.center) φ₀ := by
  let s : Fin 2 → ℝ := fun k ↦ if k = 0 then 0 else 1
  have hs_mono : Monotone s := by
    intro j₁ j₂ hj
    fin_cases j₁ <;> fin_cases j₂ <;> simp [s] at hj ⊢
  refine ⟨0, fun _ ↦ φ₀, rfl, rfl, fun i ↦ Fin.elim0 i, zero_le_one,
    continuousOn_const, rfl, rfl, s, rfl, by simp [s], hs_mono, ?_⟩
  intro _
  rintro _ ⟨_, _, rfl⟩
  exact φ₀.center_mem_disc

/-- Appending a short radial line segment inside `ψ₁.disc ∩ Ω` extends any curve continuation
`ContinuedAlongCurve φ₀ γ₁ ψ₁` to a curve ending at `w` with terminal function `ψ₁.fn`. -/
private theorem continuedAlongCurve_append_segment {Ω : Set ℂ}
    {φ₀ ψ₁ : FunctionElement} {γ₁ : ℝ → ℂ}
    (hcont₁ : ContinuedAlongCurve φ₀ γ₁ ψ₁)
    (hγ₁_Ω : γ₁ '' Set.Icc 0 1 ⊆ Ω)
    {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_le : ρ ≤ ψ₁.radius)
    (hball_Ω : Metric.ball (γ₁ 1) ρ ⊆ Ω)
    {w : ℂ} (hw : w ∈ Metric.ball (γ₁ 1) ρ) :
    ∃ (γ_w : ℝ → ℂ) (φ_w : FunctionElement),
      ContinuousOn γ_w (Set.Icc 0 1) ∧
      γ_w 0 = φ₀.center ∧
      γ_w 1 = w ∧
      γ_w '' Set.Icc 0 1 ⊆ Ω ∧
      φ_w.fn = ψ₁.fn ∧
      ContinuedAlongCurve φ₀ γ_w φ_w := by
  obtain ⟨n, Φ, hΦ0, hΦlast, hΦ_ch, _, hγ₁_cont, hc0, hc1, s, hs0, hsn, hs_mono, hs_sub⟩ := hcont₁
  let z₁ : ℂ := γ₁ 1
  have hψ₁_center : ψ₁.center = z₁ := hΦlast ▸ hc1
  have hr_w : 0 < ρ - dist w z₁ := by
    have hw' : dist w z₁ < ρ := Metric.mem_ball.mp hw
    linarith
  have hsub_ψ₁ : Metric.ball w (ρ - dist w z₁) ⊆ ψ₁.disc := by
    intro ζ hζ
    rw [FunctionElement.disc, hψ₁_center, Metric.mem_ball]
    have hζ' : dist ζ w < ρ - dist w z₁ := Metric.mem_ball.mp hζ
    calc dist ζ z₁ ≤ dist ζ w + dist w z₁ := dist_triangle ζ w z₁
      _ < (ρ - dist w z₁) + dist w z₁ := by linarith
      _ = ρ := sub_add_cancel ρ (dist w z₁)
      _ ≤ ψ₁.radius := hρ_le
  let φ_w : FunctionElement :=
    { center := w
      radius := ρ - dist w z₁
      radius_pos := hr_w
      fn := ψ₁.fn
      holo := ψ₁.holo.mono hsub_ψ₁ }
  have hdc_w : DirectContinuation ψ₁ φ_w :=
    ⟨⟨w, hsub_ψ₁ φ_w.center_mem_disc, φ_w.center_mem_disc⟩, fun _ _ ↦ rfl⟩
  let γ_w : ℝ → ℂ := fun t ↦
    if t ≤ 1 / 2 then γ₁ (2 * t) else (2 - 2 * t : ℝ) • z₁ + (2 * t - 1 : ℝ) • w
  have hγw_0 : γ_w 0 = φ₀.center := by
    dsimp [γ_w]
    norm_num
    exact (hΦ0 ▸ hc0).symm
  have hγw_1 : γ_w 1 = w := by
    dsimp [γ_w]
    norm_num
  have hγw_left : ContinuousOn γ_w (Set.Icc 0 (1 / 2)) := by
    have hcomp : ContinuousOn (fun t : ℝ ↦ γ₁ (2 * t)) (Set.Icc 0 (1 / 2)) :=
      hγ₁_cont.comp (continuousOn_const.mul continuousOn_id)
        (fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    refine hcomp.congr (fun t ht ↦ ?_)
    dsimp [γ_w]
    split_ifs with h
    · rfl
    · exact absurd ht.2 h
  have hγw_right : ContinuousOn γ_w (Set.Icc (1 / 2) 1) := by
    have hlin : ContinuousOn (fun t : ℝ ↦ (2 - 2 * t : ℝ) • z₁ + (2 * t - 1 : ℝ) • w)
        (Set.Icc (1 / 2) 1) :=
      (((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).smul continuousOn_const).add
        (((continuousOn_const.mul continuousOn_id).sub continuousOn_const).smul continuousOn_const))
    refine hlin.congr (fun t ht ↦ ?_)
    dsimp [γ_w]
    split_ifs with hle
    · have ht_eq : t = 1 / 2 := le_antisymm hle ht.1
      subst ht_eq
      norm_num [z₁]
    · rfl
  have hγw_cont : ContinuousOn γ_w (Set.Icc 0 1) := by
    have hunion : Set.Icc (0 : ℝ) (1 / 2) ∪ Set.Icc (1 / 2) 1 = Set.Icc 0 1 :=
      Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)
    rw [← hunion]
    exact hγw_left.union_of_isClosed hγw_right isClosed_Icc isClosed_Icc
  have hseg_ball : ∀ t : ℝ, 1 / 2 < t → t ≤ 1 →
      (2 - 2 * t : ℝ) • z₁ + (2 * t - 1 : ℝ) • w ∈ Metric.ball z₁ ρ := by
    intro t ht1 ht2
    exact (convex_ball z₁ ρ) (Metric.mem_ball_self hρ_pos) hw
      (by linarith) (by linarith) (by ring)
  have hγw_Ω : γ_w '' Set.Icc 0 1 ⊆ Ω := by
    rintro _ ⟨t, ht, rfl⟩
    dsimp [γ_w]
    split_ifs with hle
    · exact hγ₁_Ω ⟨2 * t, ⟨by linarith [ht.1], by linarith [hle]⟩, rfl⟩
    · exact hball_Ω (hseg_ball t (not_le.mp hle) ht.2)
  let Φ' : Fin (n + 2) → FunctionElement := Fin.snoc Φ φ_w
  have hΦ'0 : Φ' 0 = φ₀ := by
    change Fin.snoc (α := fun _ ↦ FunctionElement) Φ φ_w (0 : Fin (n + 1)).castSucc = φ₀
    rw [Fin.snoc_castSucc, hΦ0]
  have hΦ'last : Φ' (Fin.last (n + 1)) = φ_w := Fin.snoc_last _ _
  have hΦ'_ch : ChainContinuation Φ' := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · dsimp [Φ']
      rw [Fin.snoc_castSucc, Fin.snoc_last, hΦlast]
      exact hdc_w
    · intro j
      have hsucc : j.castSucc.succ = j.succ.castSucc := Fin.ext (by simp)
      dsimp [Φ']
      rw [Fin.snoc_castSucc, hsucc, Fin.snoc_castSucc]
      exact hΦ_ch j
  let s' : Fin (n + 3) → ℝ := fun k ↦ if hk : k.val < n + 1 then s ⟨k.val, by omega⟩ / 2 else 1
  have hs'0 : s' 0 = 0 := by
    dsimp [s']
    change s 0 / 2 = 0
    rw [hs0]
    norm_num
  have hs'last : s' (Fin.last (n + 2)) = 1 := by
    dsimp [s']
    split_ifs with h
    · simp at h
    · rfl
  have hs'_mono : Monotone s' := by
    intro k₁ k₂ hk
    have hk_val : k₁.val ≤ k₂.val := hk
    dsimp [s']
    split_ifs with h1 h2 h2
    · have hle_s : s ⟨k₁.val, by omega⟩ ≤ s ⟨k₂.val, by omega⟩ :=
        hs_mono (Fin.le_def.mpr hk_val)
      linarith
    · have hle_1 : s ⟨k₁.val, by omega⟩ ≤ 1 :=
        hsn ▸ hs_mono (Fin.le_last ⟨k₁.val, by omega⟩)
      linarith
    · omega
    · exact le_rfl
  refine ⟨γ_w, φ_w, hγw_cont, hγw_0, hγw_1, hγw_Ω, rfl,
    n + 1, Φ', hΦ'0, hΦ'last, hΦ'_ch, zero_le_one, hγw_cont,
    (hΦ'0 ▸ rfl : (Φ' 0).center = φ₀.center).trans hγw_0.symm,
    (hΦ'last ▸ rfl : (Φ' (Fin.last (n + 1))).center = w).trans hγw_1.symm,
    s', hs'0, hs'last, hs'_mono, ?_⟩
  intro i
  refine Fin.lastCases ?_ ?_ i
  · -- Last index `n + 1`: covers `[1, 1]` inside `φ_w.disc`
    rintro _ ⟨t, ht, rfl⟩
    have hc_val : ¬ ((Fin.last (n + 1)).castSucc.val < n + 1) := by simp
    have hs_val : ¬ ((Fin.last (n + 1)).succ.val < n + 1) := by simp
    have ht1 : t = 1 := by
      have h1 : s' (Fin.last (n + 1)).castSucc = 1 := by
        dsimp [s']
        split_ifs with h
        · exact absurd h hc_val
        · rfl
      have h2 : s' (Fin.last (n + 1)).succ = 1 := by
        dsimp [s']
        split_ifs with h
        · exact absurd h hs_val
        · rfl
      linarith [ht.1, ht.2]
    subst ht1
    dsimp [Φ']
    rw [Fin.snoc_last, hγw_1]
    exact φ_w.center_mem_disc
  · intro p
    refine Fin.lastCases ?_ ?_ p
    · -- Index `n`: covers `[s_n / 2, 1]` inside `(Φ n).disc = ψ₁.disc`
      rintro _ ⟨t, ht, rfl⟩
      have hs_nlt : ¬ ((Fin.last n).castSucc.succ.val < n + 1) := by simp
      have hs_left : s' (Fin.last n).castSucc.castSucc = s (Fin.last n).castSucc / 2 := by
        dsimp [s']
        split_ifs with hk
        · rfl
        · omega
      have hs_right : s' (Fin.last n).castSucc.succ = 1 := by
        dsimp [s']
        split_ifs with hk
        · exact absurd hk hs_nlt
        · rfl
      dsimp [Φ']
      rw [Fin.snoc_castSucc, hΦlast]
      dsimp [γ_w]
      split_ifs with hle
      · have h2t_mem : 2 * t ∈ Set.Icc (s (Fin.last n).castSucc) (s (Fin.last n).succ) := by
          have hl : (Fin.last n).succ = Fin.last (n + 1) := Fin.ext (by simp)
          rw [hl, hsn]
          exact ⟨by linarith [ht.1, hs_left], by linarith [hle]⟩
        rw [← hΦlast]
        exact hs_sub (Fin.last n) ⟨2 * t, h2t_mem, rfl⟩
      · have ht_le1 : t ≤ 1 := by linarith [ht.2, hs_right]
        have hmem_ρ : (2 - 2 * t : ℝ) • z₁ + (2 * t - 1 : ℝ) • w ∈ Metric.ball z₁ ρ :=
          hseg_ball t (not_le.mp hle) ht_le1
        rw [FunctionElement.disc, hψ₁_center]
        exact Metric.ball_subset_ball hρ_le hmem_ρ
    · -- Indices `0 ≤ j < n`: cover `[s_j / 2, s_{j+1} / 2]` inside `(Φ j).disc`
      intro j
      rintro _ ⟨t, ht, rfl⟩
      have hc_lt : j.castSucc.castSucc.castSucc.val < n + 1 := by simp
      have hs_lt : j.castSucc.castSucc.succ.val < n + 1 := by simp
      have hs_left : s' j.castSucc.castSucc.castSucc = s j.castSucc.castSucc / 2 := by
        dsimp [s']
        split_ifs with hk
        · rfl
        · simp at hk
      have hs_right : s' j.castSucc.castSucc.succ = s j.castSucc.succ / 2 := by
        dsimp [s']
        split_ifs with hk
        · congr 2
        · simp at hk
      have hs_le1 : s j.castSucc.succ ≤ 1 := hsn ▸ hs_mono (Fin.le_last _)
      have hle_half : t ≤ 1 / 2 := by linarith [ht.2, hs_right, hs_le1]
      dsimp [Φ', γ_w]
      rw [Fin.snoc_castSucc]
      split_ifs
      exact hs_sub j.castSucc ⟨2 * t, ⟨by linarith [ht.1, hs_left], by linarith [ht.2, hs_right]⟩, rfl⟩

/-- **Theorem 16.15 (`SimplyConnectedSpace` form of the Monodromy Theorem, Rudin RCA p. 327):**
Let `Ω ⊆ ℂ` be open and simply connected (`[SimplyConnectedSpace Ω]`), and let `φ₀` satisfy
`CanContinueInRegion Ω φ₀`. Then there exists a holomorphic function `f ∈ H(Ω)` (unique on `Ω`)
extending `φ₀.fn` from `φ₀.disc` to `Ω`, and agreeing with the terminal continuation `φ₁.fn` in a
neighborhood of `γ(1)` for every curve `γ` in `Ω` from `φ₀.center`. -/
theorem theorem16_15_simplyConnectedSpace {Ω : Set ℂ} (hΩ_open : IsOpen Ω)
    [hsc : SimplyConnectedSpace Ω] {φ₀ : FunctionElement}
    (hcont_all : CanContinueInRegion Ω φ₀) :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f Ω ∧
      Set.EqOn f φ₀.fn φ₀.disc ∧
      (∀ (γ : ℝ → ℂ) (φ₁ : FunctionElement),
        ContinuousOn γ (Set.Icc 0 1) → γ 0 = φ₀.center → γ '' Set.Icc 0 1 ⊆ Ω →
        ContinuedAlongCurve φ₀ γ φ₁ →
        f =ᶠ[𝓝 (γ 1)] φ₁.fn ∧ f (γ 1) = φ₁.fn (γ 1)) ∧
      (∀ g : ℂ → ℂ, DifferentiableOn ℂ g Ω → Set.EqOn g φ₀.fn φ₀.disc → Set.EqOn g f Ω) := by
  classical
  have hpc : IsPathConnected Ω := IsSimplyConnected.isPathConnected hsc
  have hΩ_reg : RudinRCA.Chapter10.IsRegion Ω := ⟨hΩ_open, hpc.isConnected⟩
  have hsc_book : RudinRCA.Chapter10.BookSimplyConnected Ω :=
    (bookSimplyConnected_iff_simplyConnectedSpace hΩ_reg).mpr hsc
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  let z₀ : ℂ := φ₀.center
  have hz₀ : z₀ ∈ Ω := hcont_all.1 φ₀.center_mem_disc
  -- Path independence of terminal continuations between any two curves in `Ω` from `z₀` to `z₁`
  have hpath_indep : ∀ {z₁ : ℂ} {γ₀ γ₁ : ℝ → ℂ} {ψ₀ ψ₁ : FunctionElement},
      ContinuousOn γ₀ (Set.Icc 0 1) → ContinuousOn γ₁ (Set.Icc 0 1) →
      γ₀ '' Set.Icc 0 1 ⊆ Ω → γ₁ '' Set.Icc 0 1 ⊆ Ω →
      γ₀ 0 = z₀ → γ₁ 0 = z₀ → γ₀ 1 = z₁ → γ₁ 1 = z₁ →
      ContinuedAlongCurve φ₀ γ₀ ψ₀ → ContinuedAlongCurve φ₀ γ₁ ψ₁ →
      DirectContinuation ψ₀ ψ₁ ∧ ψ₀.fn z₁ = ψ₁.fn z₁ := by
    intro z₁ γ₀ γ₁ ψ₀ ψ₁ hγ₀ hγ₁ hΩ₀ hΩ₁ h0₀ h0₁ h1₀ h1₁ hc₀ hc₁
    obtain ⟨Γ, hΓ, hΓ0, hΓ1⟩ :=
      theorem16_14_bookSimplyConnected hsc_book hγ₀ hγ₁ hΩ₀ hΩ₁ h0₀ h0₁ h1₀ h1₁
    have hslice := (theorem16_12 hΓ).1
    have hex_u : ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ∃ χ : FunctionElement, ContinuedAlongCurve φ₀ (fun t ↦ Γ (t, u)) χ :=
      fun u hu ↦ hcont_all.2 (fun t ↦ Γ (t, u))
        (hslice u hu).1 (hslice u hu).2.2.1 (hslice u hu).2.1
    let χ : ℝ → FunctionElement := fun u ↦
      if hu : u ∈ Set.Icc (0 : ℝ) 1 then Classical.choose (hex_u u hu) else φ₀
    have hχ : ∀ u ∈ Set.Icc (0 : ℝ) 1, ContinuedAlongCurve φ₀ (fun t ↦ Γ (t, u)) (χ u) := by
      intro u hu
      dsimp [χ]
      split_ifs
      exact Classical.choose_spec (hex_u u hu)
    have hdc_χ := (theorem16_13 hΓ rfl hχ).2.1
    have hc_χ0 : ContinuedAlongCurve φ₀ γ₀ (χ 0) :=
      (hχ 0 h0_mem).congr_curve hΓ0
    have hc_χ1 : ContinuedAlongCurve φ₀ γ₁ (χ 1) :=
      (hχ 1 h1_mem).congr_curve hΓ1
    have hdc_0 : DirectContinuation ψ₀ (χ 0) := (theorem16_11 hγ₀ hc₀ hc_χ0).1
    have hdc_1 : DirectContinuation (χ 1) ψ₁ := (theorem16_11 hγ₁ hc_χ1 hc₁).1
    have hz₁_ψ₀ : z₁ ∈ ψ₀.disc := (hc₀.centers.2.trans h1₀) ▸ ψ₀.center_mem_disc
    have hz₁_χ0 : z₁ ∈ (χ 0).disc := (hc_χ0.centers.2.trans h1₀) ▸ (χ 0).center_mem_disc
    have hz₁_χ1 : z₁ ∈ (χ 1).disc := (hc_χ1.centers.2.trans h1₁) ▸ (χ 1).center_mem_disc
    have hz₁_ψ₁ : z₁ ∈ ψ₁.disc := (hc₁.centers.2.trans h1₁) ▸ ψ₁.center_mem_disc
    have hdc_mid : DirectContinuation ψ₀ (χ 1) :=
      theorem16_10 hdc_0 hdc_χ ⟨z₁, ⟨hz₁_ψ₀, hz₁_χ0⟩, hz₁_χ1⟩
    have hdc_final : DirectContinuation ψ₀ ψ₁ :=
      theorem16_10 hdc_mid hdc_1 ⟨z₁, ⟨hz₁_ψ₀, hz₁_χ1⟩, hz₁_ψ₁⟩
    exact ⟨hdc_final, hdc_final.2 ⟨hz₁_ψ₀, hz₁_ψ₁⟩⟩
  -- Canonical curve and terminal continuation for each `z ∈ Ω`
  let proj : ℝ → unitInterval := Set.projIcc (0 : ℝ) 1 zero_le_one
  let curveTo : ∀ z ∈ Ω, ℝ → ℂ := fun z hz t ↦
    ((PathConnectedSpace.somePath (⟨z₀, hz₀⟩ : Ω) ⟨z, hz⟩) (proj t)).1
  have hcurveTo_cont : ∀ z (hz : z ∈ Ω), ContinuousOn (curveTo z hz) (Set.Icc 0 1) := by
    intro z hz
    exact (continuous_subtype_val.comp
      ((PathConnectedSpace.somePath (⟨z₀, hz₀⟩ : Ω) ⟨z, hz⟩).continuous.comp
        continuous_projIcc)).continuousOn
  have hcurveTo_0 : ∀ z (hz : z ∈ Ω), curveTo z hz 0 = z₀ := by
    intro z hz
    dsimp [curveTo, proj]
    rw [Set.projIcc_left zero_le_one]
    change ((PathConnectedSpace.somePath (⟨z₀, hz₀⟩ : Ω) ⟨z, hz⟩) 0).1 = z₀
    rw [Path.source]
  have hcurveTo_1 : ∀ z (hz : z ∈ Ω), curveTo z hz 1 = z := by
    intro z hz
    dsimp [curveTo, proj]
    rw [Set.projIcc_right zero_le_one]
    change ((PathConnectedSpace.somePath (⟨z₀, hz₀⟩ : Ω) ⟨z, hz⟩) 1).1 = z
    rw [Path.target]
  have hcurveTo_Ω : ∀ z (hz : z ∈ Ω), curveTo z hz '' Set.Icc 0 1 ⊆ Ω := by
    intro z hz
    rintro _ ⟨t, _, rfl⟩
    exact ((PathConnectedSpace.somePath (⟨z₀, hz₀⟩ : Ω) ⟨z, hz⟩) (proj t)).2
  have hex_elem : ∀ z (hz : z ∈ Ω),
      ∃ ψ : FunctionElement, ContinuedAlongCurve φ₀ (curveTo z hz) ψ :=
    fun z hz ↦ hcont_all.2 (curveTo z hz) (hcurveTo_cont z hz) (hcurveTo_0 z hz) (hcurveTo_Ω z hz)
  let elemAt : ∀ z ∈ Ω, FunctionElement := fun z hz ↦ Classical.choose (hex_elem z hz)
  have helemAt : ∀ z (hz : z ∈ Ω), ContinuedAlongCurve φ₀ (curveTo z hz) (elemAt z hz) :=
    fun z hz ↦ Classical.choose_spec (hex_elem z hz)
  let f : ℂ → ℂ := fun z ↦ if hz : z ∈ Ω then (elemAt z hz).fn z else 0
  -- Evaluation along any curve `γ` in `Ω` from `z₀`
  have hf_eval : ∀ {γ : ℝ → ℂ} {φ₁ : FunctionElement},
      ContinuousOn γ (Set.Icc 0 1) → γ 0 = z₀ → γ '' Set.Icc 0 1 ⊆ Ω →
      ContinuedAlongCurve φ₀ γ φ₁ → f (γ 1) = φ₁.fn (γ 1) := by
    intro γ φ₁ hγ_cont hγ_0 hγ_Ω hcont₁
    have hz₁ : γ 1 ∈ Ω := hγ_Ω ⟨1, h1_mem, rfl⟩
    dsimp [f]
    split_ifs
    exact (hpath_indep (hcurveTo_cont (γ 1) hz₁) hγ_cont
      (hcurveTo_Ω (γ 1) hz₁) hγ_Ω (hcurveTo_0 (γ 1) hz₁) hγ_0
      (hcurveTo_1 (γ 1) hz₁) rfl (helemAt (γ 1) hz₁) hcont₁).2
  -- Local agreement of `f` with `ψ₁.fn` on any ball `ball (γ₁ 1) ρ ⊆ ψ₁.disc ∩ Ω`
  have hf_ball : ∀ {γ₁ : ℝ → ℂ} {ψ₁ : FunctionElement} {ρ : ℝ},
      ContinuousOn γ₁ (Set.Icc 0 1) → γ₁ 0 = z₀ → γ₁ '' Set.Icc 0 1 ⊆ Ω →
      ContinuedAlongCurve φ₀ γ₁ ψ₁ → 0 < ρ → ρ ≤ ψ₁.radius →
      Metric.ball (γ₁ 1) ρ ⊆ Ω →
      ∀ w ∈ Metric.ball (γ₁ 1) ρ, f w = ψ₁.fn w := by
    intro γ₁ ψ₁ ρ _ _ hγ₁_Ω hcont₁ hρ_pos hρ_le hball_Ω w hw
    obtain ⟨γ_w, φ_w, hγw_cont, hγw_0, hγw_1, hγw_Ω, hφw_fn, hcont_w⟩ :=
      continuedAlongCurve_append_segment hcont₁ hγ₁_Ω hρ_pos hρ_le hball_Ω hw
    have hev := hf_eval hγw_cont hγw_0 hγw_Ω hcont_w
    rwa [hγw_1, hφw_fn] at hev
  -- `f` agrees with `φ₀.fn` on `φ₀.disc`
  have hf_eq_φ₀ : Set.EqOn f φ₀.fn φ₀.disc :=
    hf_ball continuousOn_const rfl (by rintro _ ⟨_, _, rfl⟩; exact hz₀)
      (continuedAlongCurve_const φ₀) φ₀.radius_pos le_rfl hcont_all.1
  -- `f` agrees locally with `φ₁.fn` near `γ 1` for every curve `γ` in `Ω`
  have hf_curve_nhds : ∀ (γ : ℝ → ℂ) (φ₁ : FunctionElement),
      ContinuousOn γ (Set.Icc 0 1) → γ 0 = z₀ → γ '' Set.Icc 0 1 ⊆ Ω →
      ContinuedAlongCurve φ₀ γ φ₁ →
      f =ᶠ[𝓝 (γ 1)] φ₁.fn ∧ f (γ 1) = φ₁.fn (γ 1) := by
    intro γ φ₁ hγ_cont hγ_0 hγ_Ω hcont₁
    have hz₁ : γ 1 ∈ Ω := hγ_Ω ⟨1, h1_mem, rfl⟩
    obtain ⟨r₁, hr₁_pos, hball_r₁⟩ := Metric.isOpen_iff.mp hΩ_open (γ 1) hz₁
    let ρ : ℝ := min r₁ φ₁.radius
    have hρ_pos : 0 < ρ := lt_min hr₁_pos φ₁.radius_pos
    have hρ_Ω : Metric.ball (γ 1) ρ ⊆ Ω :=
      (Metric.ball_subset_ball (min_le_left _ _)).trans hball_r₁
    have hev : f =ᶠ[𝓝 (γ 1)] φ₁.fn := by
      filter_upwards [Metric.ball_mem_nhds (γ 1) hρ_pos] with w hw
      exact hf_ball hγ_cont hγ_0 hγ_Ω hcont₁ hρ_pos (min_le_right _ _) hρ_Ω w hw
    exact ⟨hev, hev.eq_of_nhds⟩
  -- `f` is holomorphic on `Ω`
  have hf_diff : DifferentiableOn ℂ f Ω := by
    intro z hz
    have hev := (hf_curve_nhds (curveTo z hz) (elemAt z hz)
      (hcurveTo_cont z hz) (hcurveTo_0 z hz) (hcurveTo_Ω z hz) (helemAt z hz)).1
    rw [hcurveTo_1 z hz] at hev
    have hz_disc : z ∈ (elemAt z hz).disc := by
      have hc : (elemAt z hz).center = z :=
        (helemAt z hz).centers.2.trans (hcurveTo_1 z hz)
      rw [FunctionElement.disc, hc]
      exact Metric.mem_ball_self (elemAt z hz).radius_pos
    have hd_elem : DifferentiableAt ℂ (elemAt z hz).fn z :=
      (elemAt z hz).holo.differentiableAt ((elemAt z hz).isOpen_disc.mem_nhds hz_disc)
    exact (hd_elem.congr_of_eventuallyEq hev).differentiableWithinAt
  -- Uniqueness on `Ω`
  have hf_uniq : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g Ω →
      Set.EqOn g φ₀.fn φ₀.disc → Set.EqOn g f Ω := by
    intro g hg_diff hg_eq
    have hev : g =ᶠ[𝓝 z₀] f := by
      filter_upwards [φ₀.isOpen_disc.mem_nhds φ₀.center_mem_disc] with w hw
      exact (hg_eq hw).trans (hf_eq_φ₀ hw).symm
    exact (hg_diff.analyticOnNhd hΩ_open).eqOn_of_preconnected_of_eventuallyEq
      (hf_diff.analyticOnNhd hΩ_open) hΩ_reg.2.isPreconnected hz₀ hev
  exact ⟨f, hf_diff, hf_eq_φ₀, hf_curve_nhds, hf_uniq⟩

/-- **Theorem 16.15 (Monodromy Theorem, Rudin RCA p. 327):**
Suppose `Ω ⊆ ℂ` is a simply connected plane region (`BookSimplyConnected Ω`), `(f₀, D₀)` is a
function element with `D₀ ⊆ Ω`, and `(f₀, D₀)` can be analytically continued along every continuous
curve `γ : [0, 1] → Ω` starting at the center of `D₀`. Then there exists `f ∈ H(Ω)` (unique on `Ω`)
such that `f(z) = f₀(z)` for all `z ∈ D₀` (and `f` agrees locally with every terminal continuation). -/
theorem theorem16_15 {Ω : Set ℂ}
    (hsc : RudinRCA.Chapter10.BookSimplyConnected Ω)
    {φ₀ : FunctionElement}
    (hcont_all : CanContinueInRegion Ω φ₀) :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f Ω ∧
      RudinRCA.Chapter10.HolomorphicOn f Ω ∧
      Set.EqOn f φ₀.fn φ₀.disc ∧
      (∀ (γ : ℝ → ℂ) (φ₁ : FunctionElement),
        ContinuousOn γ (Set.Icc 0 1) → γ 0 = φ₀.center → γ '' Set.Icc 0 1 ⊆ Ω →
        ContinuedAlongCurve φ₀ γ φ₁ →
        f =ᶠ[𝓝 (γ 1)] φ₁.fn ∧ f (γ 1) = φ₁.fn (γ 1)) ∧
      (∀ g : ℂ → ℂ, DifferentiableOn ℂ g Ω → Set.EqOn g φ₀.fn φ₀.disc → Set.EqOn g f Ω) := by
  have : SimplyConnectedSpace Ω :=
    (bookSimplyConnected_iff_simplyConnectedSpace hsc.1).mp hsc
  obtain ⟨f, hf_diff, hf_eq, hf_curve, hf_uniq⟩ :=
    theorem16_15_simplyConnectedSpace hsc.1.1 hcont_all
  exact ⟨f, hf_diff, (RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn hsc.1.1).mpr hf_diff,
    hf_eq, hf_curve, hf_uniq⟩

/-- Specialization of Theorem 16.15 when continuations along curves in `Ω` are assumed with chain
discs contained in `Ω` (`CanContinueWithinRegion Ω φ₀`). -/
theorem theorem16_15_withinRegion {Ω : Set ℂ}
    (hsc : RudinRCA.Chapter10.BookSimplyConnected Ω)
    {φ₀ : FunctionElement}
    (hcont_within : CanContinueWithinRegion Ω φ₀) :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f Ω ∧
      RudinRCA.Chapter10.HolomorphicOn f Ω ∧
      Set.EqOn f φ₀.fn φ₀.disc ∧
      (∀ (γ : ℝ → ℂ) (φ₁ : FunctionElement),
        ContinuousOn γ (Set.Icc 0 1) → γ 0 = φ₀.center → γ '' Set.Icc 0 1 ⊆ Ω →
        ContinuedAlongCurve φ₀ γ φ₁ →
        f =ᶠ[𝓝 (γ 1)] φ₁.fn ∧ f (γ 1) = φ₁.fn (γ 1)) ∧
      (∀ g : ℂ → ℂ, DifferentiableOn ℂ g Ω → Set.EqOn g φ₀.fn φ₀.disc → Set.EqOn g f Ω) :=
  theorem16_15 hsc hcont_within.toCanContinueInRegion

/-!
## 16.16: Failure of Universal Monodromy on Nonsimply-Connected Plane Regions
-/

/-- Two holomorphic logarithms `g₁, g₂` of `z - w₀` on an open convex set `U` that agree at a
single point `p ∈ U` agree everywhere on `U`. -/
private theorem eqOn_of_holomorphic_log_sub_eq_at_point {U : Set ℂ} {w₀ p : ℂ} {g₁ g₂ : ℂ → ℂ}
    (hU_open : IsOpen U) (hU_conv : Convex ℝ U)
    (hg₁ : DifferentiableOn ℂ g₁ U) (hg₂ : DifferentiableOn ℂ g₂ U)
    (hexp₁ : ∀ z ∈ U, Complex.exp (g₁ z) = z - w₀)
    (hexp₂ : ∀ z ∈ U, Complex.exp (g₂ z) = z - w₀)
    (hp : p ∈ U) (heqp : g₁ p = g₂ p) :
    Set.EqOn g₁ g₂ U := by
  have hderiv_eq : ∀ z ∈ U, deriv (g₁ - g₂) z = 0 := by
    intro z hz
    have hd₁ : HasDerivAt g₁ (deriv g₁ z) z :=
      (hg₁.differentiableAt (hU_open.mem_nhds hz)).hasDerivAt
    have hd₂ : HasDerivAt g₂ (deriv g₂ z) z :=
      (hg₂.differentiableAt (hU_open.mem_nhds hz)).hasDerivAt
    have hev₁ : (fun ζ ↦ Complex.exp (g₁ ζ)) =ᶠ[𝓝 z] (fun ζ ↦ ζ - w₀) :=
      Filter.eventuallyEq_of_mem (hU_open.mem_nhds hz) hexp₁
    have hev₂ : (fun ζ ↦ Complex.exp (g₂ ζ)) =ᶠ[𝓝 z] (fun ζ ↦ ζ - w₀) :=
      Filter.eventuallyEq_of_mem (hU_open.mem_nhds hz) hexp₂
    have h1 : Complex.exp (g₁ z) * deriv g₁ z = 1 :=
      (hd₁.cexp.congr_of_eventuallyEq hev₁.symm).unique ((hasDerivAt_id z).sub_const w₀)
    have h2 : Complex.exp (g₂ z) * deriv g₂ z = 1 :=
      (hd₂.cexp.congr_of_eventuallyEq hev₂.symm).unique ((hasDerivAt_id z).sub_const w₀)
    rw [hexp₁ z hz, ← hexp₂ z hz] at h1
    have hdg : deriv g₁ z = deriv g₂ z := by
      have hnz₂ : Complex.exp (g₂ z) ≠ 0 := Complex.exp_ne_zero _
      exact mul_left_cancel₀ hnz₂ (h1.trans h2.symm)
    rw [(hd₁.sub hd₂).deriv, hdg, sub_self]
  intro z hz
  have hconst := hU_open.is_const_of_deriv_eq_zero hU_conv.isPreconnected
    (hg₁.sub hg₂) hderiv_eq hz hp
  change g₁ z - g₂ z = g₁ p - g₂ p at hconst
  rw [heqp, sub_self] at hconst
  exact sub_eq_zero.mp hconst

/-- On any open disc `Metric.ball c r` (`r > 0`) omitting `w₀`, there exists a holomorphic branch
`g` of `log(z - w₀)` taking a prescribed value `v` (with `exp v = p - w₀`) at `p ∈ Metric.ball c r`. -/
private theorem exists_local_log_sub_with_val {c w₀ p v : ℂ} {r : ℝ}
    (hr : 0 < r) (hw₀ : w₀ ∉ Metric.ball c r)
    (hp : p ∈ Metric.ball c r) (hv : Complex.exp v = p - w₀) :
    ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (Metric.ball c r) ∧
      (∀ z ∈ Metric.ball c r, Complex.exp (g z) = z - w₀) ∧
      g p = v := by
  have : ContractibleSpace (Metric.ball c r) :=
    (convex_ball c r).contractibleSpace ⟨c, Metric.mem_ball_self hr⟩
  have hsc : IsSimplyConnected (Metric.ball c r) := SimplyConnectedSpace.ofContractible _
  have hsub_diff : DifferentiableOn ℂ (fun z ↦ z - w₀) (Metric.ball c r) :=
    differentiableOn_id.sub_const w₀
  obtain ⟨h, hh_holo, hh_exp⟩ :=
    RudinRCA.Chapter15.exists_holomorphic_log isOpen_ball hsc hsub_diff
      (fun z hz h0 ↦ hw₀ ((sub_eq_zero.mp h0) ▸ hz))
  refine ⟨fun z ↦ h z + (v - h p), hh_holo.add (differentiableOn_const _), ?_, by ring⟩
  intro z hz
  have hexp_shift : Complex.exp (v - h p) = 1 := by
    rw [Complex.exp_sub, hv, hh_exp p hp]
    have hp_ne : p - w₀ ≠ 0 := fun h0 ↦ hw₀ ((sub_eq_zero.mp h0) ▸ hp)
    exact div_self hp_ne
  rw [Complex.exp_add, hh_exp z hz, hexp_shift, mul_one]

/-- Positive uniform ball clearance along any continuous curve `γ : [0, 1] → Ω` in an open set `Ω`. -/
private theorem exists_uniform_ball_clearance_of_curve {Ω : Set ℂ} (hΩ_open : IsOpen Ω)
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Set.Icc 0 1)) (hγ_Ω : γ '' Set.Icc 0 1 ⊆ Ω) :
    ∃ ρ > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, Metric.ball (γ t) ρ ⊆ Ω := by
  let K : Set ℂ := γ '' Set.Icc 0 1
  have hK_comp : IsCompact K := isCompact_Icc.image_of_continuousOn hγ
  have hball_pt : ∀ z : K, ∃ r > 0, Metric.ball z.1 r ⊆ Ω :=
    fun z ↦ Metric.isOpen_iff.mp hΩ_open z.1 (hγ_Ω z.2)
  choose r hr_pos hr_sub using hball_pt
  obtain ⟨F, hF_cov⟩ := hK_comp.elim_finite_subcover
    (fun z : K ↦ Metric.ball z.1 (r z / 2))
    (fun z ↦ isOpen_ball)
    (fun w hw ↦ Set.mem_iUnion.mpr ⟨⟨w, hw⟩, Metric.mem_ball_self (half_pos (hr_pos ⟨w, hw⟩))⟩)
  have h0_mem : γ 0 ∈ K := ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hF_ne : F.Nonempty := by
    obtain ⟨z, hzF, _⟩ := Set.mem_iUnion₂.mp (hF_cov h0_mem)
    exact ⟨z, hzF⟩
  let ρ : ℝ := F.inf' hF_ne (fun z ↦ r z / 2)
  have hρ_pos : 0 < ρ :=
    (Finset.lt_inf'_iff hF_ne).mpr (fun z _ ↦ half_pos (hr_pos z))
  refine ⟨ρ, hρ_pos, fun t ht w hw ↦ ?_⟩
  obtain ⟨z, hzF, hγt_z⟩ := Set.mem_iUnion₂.mp (hF_cov ⟨t, ht, rfl⟩)
  have hρ_le : ρ ≤ r z / 2 := Finset.inf'_le (fun z ↦ r z / 2) hzF
  apply hr_sub z
  rw [Metric.mem_ball] at hw hγt_z ⊢
  calc dist w z.1 ≤ dist w (γ t) + dist (γ t) z.1 := dist_triangle w (γ t) z.1
    _ < ρ + r z / 2 := add_lt_add hw hγt_z
    _ ≤ r z / 2 + r z / 2 := by linarith
    _ = r z := add_halves (r z)

/-- **Remark 16.16 (Failure of Universal Monodromy on Nonsimply-Connected Plane Regions, Rudin RCA p. 327):**
If `Ω ⊆ ℂ` is a plane region that is NOT simply connected (`¬ BookSimplyConnected Ω`), there exist
an omitted finite point `w₀ ∈ Ωᶜ` and a function element `φ₀` on a disc `D₀ ⊆ Ω` representing a
holomorphic branch of `log(z - w₀)` (`exp(φ₀.fn z) = z - w₀` on `D₀`) such that:
1. `φ₀` can be analytically continued along EVERY continuous curve `γ : [0, 1] → Ω` starting at
   `φ₀.center`, even with all chain discs contained in `Ω` (`ContinuedAlongCurveIn Ω` and
   `ContinuedAlongCurve`);
2. Yet there does NOT exist any holomorphic function `f ∈ H(Ω)` agreeing with `φ₀.fn` on `D₀`. -/
theorem theorem16_16 {Ω : Set ℂ}
    (hΩ : RudinRCA.Chapter10.IsRegion Ω)
    (hnot : ¬ RudinRCA.Chapter10.BookSimplyConnected Ω) :
    ∃ (w₀ : ℂ) (φ₀ : FunctionElement),
      w₀ ∈ Ωᶜ ∧
      φ₀.disc ⊆ Ω ∧
      (∀ z ∈ φ₀.disc, Complex.exp (φ₀.fn z) = z - w₀) ∧
      CanContinueWithinRegion Ω φ₀ ∧
      CanContinueInRegion Ω φ₀ ∧
      (∀ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) →
        γ 0 = φ₀.center → γ '' Set.Icc 0 1 ⊆ Ω →
        ∃ φ₁ : FunctionElement,
          ContinuedAlongCurveIn Ω φ₀ γ φ₁ ∧ ContinuedAlongCurve φ₀ γ φ₁) ∧
      ¬ ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ Set.EqOn f φ₀.fn φ₀.disc := by
  -- Step 1: Extract closed `BookPath` `γ_loop` in `Ω` and finite `w₀ ∉ Ω` with `Ind γ_loop w₀ ≠ 0`
  have hnot_condC :
      ¬ (∀ γ : RudinRCA.Chapter10.BookPath, γ.IsClosed → γ.trace ⊆ Ω →
          ∀ α ∈ RudinRCA.Chapter13.sphericalCompl Ω,
            RudinRCA.Chapter13.sphericalInd γ α = 0) :=
    fun hc ↦ hnot ((RudinRCA.Chapter13.theorem13_11 hΩ).2.2.1.mpr hc)
  push Not at hnot_condC
  obtain ⟨γ_loop, hγ_closed, hγ_sub, α, hα_compl, hα_ind⟩ := hnot_condC
  have hw₀_ex : ∃ w₀ : ℂ, w₀ ∉ Ω ∧ RudinRCA.Chapter10.Ind γ_loop.toBookCurve w₀ ≠ 0 := by
    induction α using OnePoint.rec with
    | infty =>
      rw [RudinRCA.Chapter13.sphericalInd_infty] at hα_ind
      exact False.elim (hα_ind rfl)
    | coe w₀ =>
      rw [RudinRCA.Chapter13.coe_mem_sphericalCompl] at hα_compl
      rw [RudinRCA.Chapter13.sphericalInd_coe] at hα_ind
      exact ⟨w₀, hα_compl, hα_ind⟩
  obtain ⟨w₀, hw₀_notMem, hInd_ne⟩ := hw₀_ex
  -- Step 2: Construct initial local logarithm element `φ₀` on `D₀ = ball z₀ r₀ ⊆ Ω`
  obtain ⟨z₀, hz₀⟩ := hΩ.2.nonempty
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ := Metric.isOpen_iff.mp hΩ.1 z₀ hz₀
  have hw₀_not_D₀ : w₀ ∉ Metric.ball z₀ r₀ := fun h ↦ hw₀_notMem (hr₀_sub h)
  have hz₀_sub_ne : z₀ - w₀ ≠ 0 := fun h ↦ hw₀_notMem (sub_eq_zero.mp h ▸ hz₀)
  obtain ⟨g₀, hg₀_holo, hg₀_exp, _⟩ :=
    exists_local_log_sub_with_val hr₀_pos hw₀_not_D₀
      (Metric.mem_ball_self hr₀_pos) (Complex.exp_log hz₀_sub_ne)
  let φ₀ : FunctionElement :=
    { center := z₀
      radius := r₀
      radius_pos := hr₀_pos
      fn := g₀
      holo := hg₀_holo }
  -- Step 3: Analytic continuation of `φ₀` along every curve `γ : [0, 1] → Ω` starting at `z₀`
  have hcont_within : CanContinueWithinRegion Ω φ₀ := by
    refine ⟨hr₀_sub, fun γ hγ hγ0 hγ_Ω ↦ ?_⟩
    obtain ⟨ρ, hρ_pos, hρ_ball⟩ := exists_uniform_ball_clearance_of_curve hΩ.1 hγ hγ_Ω
    let ρ₁ : ℝ := min r₀ ρ
    have hρ₁_pos : 0 < ρ₁ := lt_min hr₀_pos hρ_pos
    have hunif : UniformContinuousOn γ (Set.Icc 0 1) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hγ
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hunif ρ₁ hρ₁_pos
    obtain ⟨K_nat, hK_nat⟩ := exists_nat_gt (1 / δ)
    let M : ℕ := K_nat + 1
    have hM_pos : 0 < (M : ℝ) := by exact_mod_cast Nat.succ_pos K_nat
    have hinv_M_lt : (1 : ℝ) / (M : ℝ) < δ := by
      have hgt : 1 / δ < (M : ℝ) := by
        calc 1 / δ < (K_nat : ℝ) := hK_nat
          _ ≤ (K_nat : ℝ) + 1 := by linarith
          _ = (M : ℝ) := by push_cast [M]; ring
      rw [div_lt_iff₀ hM_pos]
      have h1 := (div_lt_iff₀ hδ_pos).mp hgt
      linarith
    let tau : ℕ → ℝ := fun k ↦ min ((k : ℝ) / (M : ℝ)) 1
    have htau_mem : ∀ k : ℕ, tau k ∈ Set.Icc (0 : ℝ) 1 := fun k ↦
      ⟨le_min (div_nonneg (Nat.cast_nonneg k) hM_pos.le) zero_le_one, min_le_right _ _⟩
    have htau_0 : tau 0 = 0 := by
      dsimp [tau]
      rw [Nat.cast_zero, zero_div, min_eq_left zero_le_one]
    have htau_M : tau M = 1 := by
      dsimp [tau]
      rw [div_self hM_pos.ne', min_self]
    have htau_mono : Monotone tau := by
      intro k₁ k₂ hk
      apply min_le_min_right
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hk) hM_pos.le
    have htau_step : ∀ k : ℕ, tau (k + 1) - tau k ≤ 1 / (M : ℝ) := by
      intro k
      dsimp [tau]
      have h1 : min (((k + 1 : ℕ) : ℝ) / (M : ℝ)) 1 ≤ ((k : ℝ) / (M : ℝ)) + 1 / (M : ℝ) := by
        refine (min_le_left _ _).trans ?_
        push_cast
        ring_nf
        exact le_rfl
      rcases le_total ((k : ℝ) / (M : ℝ)) 1 with hle1 | hge1
      · rw [min_eq_left hle1]
        linarith
      · rw [min_eq_right hge1]
        have hle_one : min (((k + 1 : ℕ) : ℝ) / (M : ℝ)) 1 ≤ 1 := min_le_right _ _
        have hpos_inv : 0 ≤ 1 / (M : ℝ) := by positivity
        linarith
    -- Build chain elements recursively with bundled invariants
    let ElemInv (k : ℕ) :=
      { φ : FunctionElement //
        φ.center = γ (tau k) ∧
        φ.disc ⊆ Ω ∧
        (∀ z ∈ φ.disc, Complex.exp (φ.fn z) = z - w₀) ∧
        (0 < k → φ.radius = ρ₁) }
    let seq : ∀ k : ℕ, ElemInv k :=
      Nat.rec
        ⟨φ₀, by rw [htau_0]; exact hγ0.symm, hr₀_sub, hg₀_exp, fun h ↦ (lt_irrefl 0 h).elim⟩
        (fun k prev ↦
          let pk : ℂ := γ (tau k)
          let ck1 : ℂ := γ (tau (k + 1))
          have hball_sub : Metric.ball ck1 ρ₁ ⊆ Ω :=
            (Metric.ball_subset_ball (min_le_right r₀ ρ)).trans (hρ_ball (tau (k + 1)) (htau_mem (k + 1)))
          have hw₀_not : w₀ ∉ Metric.ball ck1 ρ₁ := fun h ↦ hw₀_notMem (hball_sub h)
          have hpk_in : pk ∈ Metric.ball ck1 ρ₁ := by
            rw [Metric.mem_ball]
            apply hδ (tau k) (htau_mem k) (tau (k + 1)) (htau_mem (k + 1))
            rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (htau_mono (Nat.le_succ k))), neg_sub]
            exact (htau_step k).trans_lt hinv_M_lt
          have hpk_prev : pk ∈ prev.1.disc := by
            rw [FunctionElement.disc, prev.2.1]
            exact Metric.mem_ball_self prev.1.radius_pos
          have hexp_pk : Complex.exp (prev.1.fn pk) = pk - w₀ := prev.2.2.2.1 pk hpk_prev
          let g_ex := exists_local_log_sub_with_val hρ₁_pos hw₀_not hpk_in hexp_pk
          let g := Classical.choose g_ex
          have hg := Classical.choose_spec g_ex
          ⟨{ center := ck1
             radius := ρ₁
             radius_pos := hρ₁_pos
             fn := g
             holo := hg.1 },
           rfl, hball_sub, hg.2.1, fun _ ↦ rfl⟩)
    -- Adjacent elements in `seq` are direct continuations
    have hseq_dc : ∀ k : ℕ, DirectContinuation (seq k).1 (seq (k + 1)).1 := by
      intro k
      let pk : ℂ := γ (tau k)
      let ck1 : ℂ := γ (tau (k + 1))
      have hball_sub : Metric.ball ck1 ρ₁ ⊆ Ω :=
        (Metric.ball_subset_ball (min_le_right r₀ ρ)).trans (hρ_ball (tau (k + 1)) (htau_mem (k + 1)))
      have hw₀_not : w₀ ∉ Metric.ball ck1 ρ₁ := fun h ↦ hw₀_notMem (hball_sub h)
      have hpk_in : pk ∈ Metric.ball ck1 ρ₁ := by
        rw [Metric.mem_ball]
        apply hδ (tau k) (htau_mem k) (tau (k + 1)) (htau_mem (k + 1))
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (htau_mono (Nat.le_succ k))), neg_sub]
        exact (htau_step k).trans_lt hinv_M_lt
      have hpk_prev : pk ∈ (seq k).1.disc := by
        rw [FunctionElement.disc, (seq k).2.1]
        exact Metric.mem_ball_self (seq k).1.radius_pos
      have hpk_next : pk ∈ (seq (k + 1)).1.disc := hpk_in
      have hexp_pk : Complex.exp ((seq k).1.fn pk) = pk - w₀ := (seq k).2.2.2.1 pk hpk_prev
      have hval_eq : (seq (k + 1)).1.fn pk = (seq k).1.fn pk :=
        (Classical.choose_spec
          (exists_local_log_sub_with_val hρ₁_pos hw₀_not hpk_in hexp_pk)).2.2
      refine ⟨⟨pk, hpk_prev, hpk_next⟩, ?_⟩
      exact eqOn_of_holomorphic_log_sub_eq_at_point
        ((seq k).1.isOpen_disc.inter (seq (k + 1)).1.isOpen_disc)
        ((seq k).1.convex_disc.inter (seq (k + 1)).1.convex_disc)
        ((seq k).1.holo.mono inter_subset_left)
        ((seq (k + 1)).1.holo.mono inter_subset_right)
        (fun z hz ↦ (seq k).2.2.2.1 z hz.1)
        (fun z hz ↦ (seq (k + 1)).2.2.2.1 z hz.2)
        ⟨hpk_prev, hpk_next⟩
        hval_eq.symm
    let Φ : Fin (M + 1) → FunctionElement := fun i ↦ (seq i.val).1
    let s : Fin (M + 2) → ℝ := fun k ↦ if k.val = 0 then 0 else tau (k.val - 1)
    have hs0 : s 0 = 0 := rfl
    have hsn : s (Fin.last (M + 1)) = 1 := by
      dsimp [s]
      exact htau_M
    have hs_mono : Monotone s := by
      intro i₁ i₂ hi
      have hval : i₁.val ≤ i₂.val := hi
      dsimp [s]
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact (htau_mem _).1
      · omega
      · exact htau_mono (by omega)
    refine ⟨Φ (Fin.last M), M, Φ, rfl, rfl, fun i ↦ (seq i.val).2.2.1,
      fun k ↦ hseq_dc k.val, zero_le_one, hγ, hγ0.symm,
      ((seq M).2.1.trans (congrArg γ htau_M)),
      s, hs0, hsn, hs_mono, ?_⟩
    intro i
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · -- `i = 0`: covers `[0, 0]` inside `φ₀.disc`
      rintro _ ⟨t, ht, rfl⟩
      have hs_left : s (0 : Fin (M + 1)).castSucc = 0 := rfl
      have hs_right : s (0 : Fin (M + 1)).succ = 0 := by
        dsimp [s]
        simpa using htau_0
      have ht0 : t = 0 := by linarith [ht.1, ht.2, hs_left, hs_right]
      subst ht0
      change γ 0 ∈ φ₀.disc
      rw [hγ0]
      exact φ₀.center_mem_disc
    · -- `i = k.succ`: covers `[tau k, tau (k + 1)]` inside `ball (γ (tau (k + 1))) ρ₁`
      rintro _ ⟨t, ht, rfl⟩
      have hs_left : s k.succ.castSucc = tau k.val := rfl
      have hs_right : s k.succ.succ = tau (k.val + 1) := rfl
      have ht01 : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨(htau_mem k.val).1.trans (hs_left ▸ ht.1),
         (hs_right ▸ ht.2).trans (htau_mem (k.val + 1)).2⟩
      have hdist_t : dist t (tau (k.val + 1)) < δ := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hs_right ▸ ht.2)), neg_sub]
        calc tau (k.val + 1) - t ≤ tau (k.val + 1) - tau k.val := by linarith [ht.1, hs_left]
          _ ≤ 1 / (M : ℝ) := htau_step k.val
          _ < δ := hinv_M_lt
      have hdist_γ : dist (γ t) (γ (tau (k.val + 1))) < ρ₁ :=
        hδ t ht01 (tau (k.val + 1)) (htau_mem (k.val + 1)) hdist_t
      dsimp [Φ]
      rw [FunctionElement.disc, (seq (k.val + 1)).2.1,
        (seq (k.val + 1)).2.2.2.2 (Nat.succ_pos k.val), Metric.mem_ball]
      exact hdist_γ
  -- Step 4: Winding obstruction `Ind γ_loop w₀ ≠ 0` forbids any global extension `f ∈ H(Ω)`
  have hno_global : ¬ ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ Set.EqOn f φ₀.fn φ₀.disc := by
    rintro ⟨f, hf_diff, hf_eq⟩
    let G : ℂ → ℂ := fun z ↦ Complex.exp (f z) - (z - w₀)
    have hG_diff : DifferentiableOn ℂ G Ω :=
      (Complex.differentiable_exp.comp_differentiableOn hf_diff).sub
        (differentiableOn_id.sub_const w₀)
    have hG_ev : G =ᶠ[𝓝 z₀] 0 := by
      filter_upwards [φ₀.isOpen_disc.mem_nhds φ₀.center_mem_disc] with z hz
      dsimp [G]
      rw [hf_eq hz, hg₀_exp z hz, sub_self]
    have hG_zero : Set.EqOn G 0 Ω :=
      (hG_diff.analyticOnNhd hΩ.1).eqOn_of_preconnected_of_eventuallyEq
        analyticOnNhd_const hΩ.2.isPreconnected hz₀ hG_ev
    have hexp_f : ∀ z ∈ Ω, Complex.exp (f z) = z - w₀ :=
      fun z hz ↦ sub_eq_zero.mp (hG_zero hz)
    have hderiv_f : ∀ z ∈ Ω, deriv f z = (z - w₀)⁻¹ := by
      intro z hz
      have hd1 : HasDerivAt (fun ζ ↦ Complex.exp (f ζ)) (Complex.exp (f z) * deriv f z) z :=
        (hf_diff.differentiableAt (hΩ.1.mem_nhds hz)).hasDerivAt.cexp
      have hev : (fun ζ ↦ Complex.exp (f ζ)) =ᶠ[𝓝 z] (fun ζ ↦ ζ - w₀) :=
        Filter.eventuallyEq_of_mem (hΩ.1.mem_nhds hz) hexp_f
      have hd2 : HasDerivAt (fun ζ ↦ ζ - w₀) 1 z := (hasDerivAt_id z).sub_const w₀
      have hmul : (z - w₀) * deriv f z = 1 := by
        rw [← hexp_f z hz]
        exact hd1.unique (hd2.congr_of_eventuallyEq hev)
      exact eq_inv_of_mul_eq_one_right hmul
    have hf_holo : RudinRCA.Chapter10.HolomorphicOn f Ω :=
      (RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn hΩ.1).mpr hf_diff
    have hdf_cont : ContinuousOn (deriv f) Ω := by
      have hsub_cont : ContinuousOn (fun z : ℂ ↦ z - w₀) Ω :=
        continuousOn_id.sub continuousOn_const
      have hinv_cont : ContinuousOn (fun z : ℂ ↦ (z - w₀)⁻¹) Ω :=
        hsub_cont.inv₀ (fun z hz h0 ↦ hw₀_notMem ((sub_eq_zero.mp h0) ▸ hz))
      exact hinv_cont.congr hderiv_f
    have hint_deriv : RudinRCA.Chapter10.pathIntegral (deriv f) γ_loop.toBookCurve = 0 :=
      RudinRCA.Chapter10.theorem10_12 hΩ.1 hf_holo hdf_cont γ_loop hγ_closed hγ_sub
    have hint_inv :
        RudinRCA.Chapter10.pathIntegral (fun z ↦ (z - w₀)⁻¹) γ_loop.toBookCurve = 0 := by
      rw [← RudinRCA.Chapter10.BookPath.pathIntegral_congr γ_loop.toBookCurve
        (fun z hz ↦ hderiv_f z (hγ_sub hz))]
      exact hint_deriv
    have hInd_zero : RudinRCA.Chapter10.Ind γ_loop.toBookCurve w₀ = 0 := by
      simp [RudinRCA.Chapter10.Ind, hint_inv]
    exact hInd_ne hInd_zero
  refine ⟨w₀, φ₀, hw₀_notMem, hr₀_sub, hg₀_exp, hcont_within,
    hcont_within.toCanContinueInRegion,
    fun γ hγ hγ0 hγ_Ω ↦
      let ⟨φ₁, hφ₁⟩ := hcont_within.2 γ hγ hγ0 hγ_Ω
      ⟨φ₁, hφ₁, hφ₁.toContinuedAlongCurve⟩,
    hno_global⟩

/-!
## Axiom Audit
-/

#print axioms IsStraightLine
#print axioms IsLineOrCircle
#print axioms rectBoundary_eq_zero_of_zero_notMem_im
#print axioms holomorphic_of_continuous_off_real_axis
#print axioms holomorphic_of_continuous_off_line
#print axioms differentiableAt_off_unit_circle_ne_neg_one
#print axioms holomorphic_of_continuous_off_unit_circle
#print axioms holomorphic_of_continuous_off_circle
#print axioms theorem16_8
#print axioms FunctionElement
#print axioms FunctionElement.disc
#print axioms FunctionElement.center_mem_disc
#print axioms FunctionElement.isOpen_disc
#print axioms FunctionElement.convex_disc
#print axioms DirectContinuation
#print axioms DirectContinuation.refl
#print axioms DirectContinuation.symm
#print axioms DiscChain
#print axioms ChainContinuation
#print axioms ChainContinuation.discChain
#print axioms chainContinuation_unique_on_discs
#print axioms chainContinuation_unique
#print axioms ChainCoversCurve
#print axioms ChainCoversCurve.discChain
#print axioms ContinuedAlongCurve
#print axioms ContinuedAlongCurveIn
#print axioms ContinuedAlongCurveIn.toContinuedAlongCurve
#print axioms ContinuedAlongCurve.centers
#print axioms ContinuedAlongCurve.congr_curve
#print axioms directContinuation_not_transitive_sqrt
#print axioms theorem16_9
#print axioms theorem16_10
#print axioms exists_subinterval_of_monotone
#print axioms chain_directContinuation_of_le
#print axioms chainCovers_directContinuation_of_mem_both
#print axioms eventually_subinterval_contains_center
#print axioms theorem16_11
#print axioms IsEndpointFixedCurveFamily
#print axioms theorem16_12
#print axioms eventually_continuedAlongCurve_slice
#print axioms theorem16_13
#print axioms theorem16_14
#print axioms bookSimplyConnected_iff_simplyConnectedSpace
#print axioms theorem16_14_bookSimplyConnected
#print axioms CanContinueInRegion
#print axioms CanContinueWithinRegion
#print axioms CanContinueWithinRegion.toCanContinueInRegion
#print axioms continuedAlongCurve_const
#print axioms continuedAlongCurve_append_segment
#print axioms theorem16_15_simplyConnectedSpace
#print axioms theorem16_15
#print axioms theorem16_15_withinRegion
#print axioms eqOn_of_holomorphic_log_sub_eq_at_point
#print axioms exists_local_log_sub_with_val
#print axioms exists_uniform_ball_clearance_of_curve
#print axioms theorem16_16


end Chapter16PartB

section Chapter16PartC
open Set Function Filter Topology
open scoped MatrixGroups


/-! ### Node 16.17: The Modular Group (RCA p. 328) -/

/-- **16.17 (The open upper half-plane `Π⁺`, RCA p. 328):**
`Π⁺ = {z ∈ ℂ : Im z > 0}`. -/
def UpperHalfPlaneSet : Set ℂ :=
  {z : ℂ | 0 < z.im}

@[simp]
theorem mem_upperHalfPlaneSet {z : ℂ} : z ∈ UpperHalfPlaneSet ↔ 0 < z.im :=
  Iff.rfl

theorem I_mem_upperHalfPlaneSet : Complex.I ∈ UpperHalfPlaneSet := by
  simp [UpperHalfPlaneSet]

theorem isOpen_upperHalfPlaneSet : IsOpen UpperHalfPlaneSet :=
  isOpen_lt continuous_const Complex.continuous_im

theorem convex_upperHalfPlaneSet : Convex ℝ UpperHalfPlaneSet := by
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  rw [mem_upperHalfPlaneSet] at hz₁ hz₂ ⊢
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · have hb1 : b = 1 := by linarith
    rw [hb1]
    linarith
  · have h1 : 0 < a * z₁.im := mul_pos ha_pos hz₁
    have h2 : 0 ≤ b * z₂.im := mul_nonneg hb hz₂.le
    linarith

theorem isRegion_upperHalfPlaneSet : RudinRCA.Chapter10.IsRegion UpperHalfPlaneSet :=
  ⟨isOpen_upperHalfPlaneSet,
    ⟨⟨Complex.I, I_mem_upperHalfPlaneSet⟩, convex_upperHalfPlaneSet.isPreconnected⟩⟩

/-- **16.17 (Integral linear fractional transformation, RCA p. 328):**
`φ(z) = (a z + b) / (c z + d)` for integers `a, b, c, d : ℤ`. -/
def intMoebius (a b c d : ℤ) (z : ℂ) : ℂ :=
  ((a : ℂ) * z + (b : ℂ)) / ((c : ℂ) * z + (d : ℂ))

@[simp]
theorem intMoebius_neg (a b c d : ℤ) (z : ℂ) :
    intMoebius (-a) (-b) (-c) (-d) z = intMoebius a b c d z := by
  unfold intMoebius
  push_cast
  have hnum : -(a : ℂ) * z + -(b : ℂ) = -((a : ℂ) * z + (b : ℂ)) := by ring
  have hden : -(c : ℂ) * z + -(d : ℂ) = -((c : ℂ) * z + (d : ℂ)) := by ring
  rw [hnum, hden, neg_div_neg_eq]

@[simp]
theorem intMoebius_id (z : ℂ) : intMoebius 1 0 0 1 z = z := by
  simp [intMoebius]

theorem intMoebius_denom_ne_zero_of_im_ne_zero {c d : ℤ} (hcd : c ≠ 0 ∨ d ≠ 0)
    {z : ℂ} (hz : z.im ≠ 0) : (c : ℂ) * z + (d : ℂ) ≠ 0 := by
  intro h0
  have him : ((c : ℂ) * z + (d : ℂ)).im = 0 := by rw [h0, Complex.zero_im]
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    zero_mul, add_zero] at him
  have hc0_real : (c : ℝ) = 0 := (mul_eq_zero.mp him).resolve_right hz
  have hc0 : c = 0 := Int.cast_eq_zero.mp hc0_real
  rw [hc0, Int.cast_zero, zero_mul, zero_add] at h0
  have hd0 : d = 0 := Int.cast_eq_zero.mp h0
  rcases hcd with hc | hd
  · exact hc hc0
  · exact hd hd0

/-- **16.17 (Denominator nonvanishing on `Π⁺`, RCA p. 328):**
If `a * d - b * c = 1`, then `(c : ℂ) * z + d ≠ 0` for every `z ∈ Π⁺` (in fact whenever `z.im ≠ 0`). -/
theorem intMoebius_denom_ne_zero {a b c d : ℤ} (hdet : a * d - b * c = 1)
    {z : ℂ} (hz : z ∈ UpperHalfPlaneSet) : (c : ℂ) * z + (d : ℂ) ≠ 0 := by
  refine intMoebius_denom_ne_zero_of_im_ne_zero ?_ hz.ne'
  by_cases hc : c = 0
  · right
    intro hd
    subst hc; subst hd
    norm_num at hdet
  · exact Or.inl hc

/-- General imaginary part identity `Im((a z + b) / (c z + d)) = (a d - b c) Im(z) / |c z + d|²`. -/
theorem intMoebius_im_general (a b c d : ℤ) (z : ℂ) :
    (intMoebius a b c d z).im =
      ((a * d - b * c : ℤ) : ℝ) * z.im / ‖(c : ℂ) * z + (d : ℂ)‖ ^ 2 := by
  unfold intMoebius
  simp only [Complex.div_im, Complex.add_im, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, zero_mul, add_zero, Complex.add_re, Complex.mul_re, sub_zero,
    ← sub_div, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **16.17 (Imaginary part formula on `Π⁺`, RCA p. 328 eq. (3)):**
If `a * d - b * c = 1`, then `Im((a z + b) / (c z + d)) = Im(z) / |c z + d|²`. -/
theorem intMoebius_im {a b c d : ℤ} (hdet : a * d - b * c = 1) (z : ℂ) :
    (intMoebius a b c d z).im = z.im / ‖(c : ℂ) * z + (d : ℂ)‖ ^ 2 := by
  rw [intMoebius_im_general, hdet, Int.cast_one, one_mul]

/-- **16.17 (`intMoebius` maps `Π⁺` into `Π⁺`, RCA p. 328):**
When `a * d - b * c = 1` and `z ∈ Π⁺`, `intMoebius a b c d z ∈ Π⁺`. -/
theorem intMoebius_mem_upperHalfPlaneSet {a b c d : ℤ} (hdet : a * d - b * c = 1)
    {z : ℂ} (hz : z ∈ UpperHalfPlaneSet) :
    intMoebius a b c d z ∈ UpperHalfPlaneSet := by
  rw [mem_upperHalfPlaneSet, intMoebius_im hdet]
  have hden : (c : ℂ) * z + (d : ℂ) ≠ 0 := intMoebius_denom_ne_zero hdet hz
  exact div_pos hz (sq_pos_of_pos (norm_pos_iff.mpr hden))

/-- **16.17 (Holomorphicity on `Π⁺`, RCA p. 328):**
When `a * d - b * c = 1`, `intMoebius a b c d` is holomorphic (`DifferentiableOn ℂ` and
`Chapter10.HolomorphicOn`) on `Π⁺`. -/
theorem intMoebius_holomorphicOn {a b c d : ℤ} (hdet : a * d - b * c = 1) :
    RudinRCA.Chapter10.HolomorphicOn (intMoebius a b c d) UpperHalfPlaneSet := by
  intro z hz
  unfold intMoebius
  exact ((differentiableAt_id.const_mul (a : ℂ)).add (differentiableAt_const (b : ℂ))).div
    ((differentiableAt_id.const_mul (c : ℂ)).add (differentiableAt_const (d : ℂ)))
    (intMoebius_denom_ne_zero hdet hz)

theorem intMoebius_differentiableOn {a b c d : ℤ} (hdet : a * d - b * c = 1) :
    DifferentiableOn ℂ (intMoebius a b c d) UpperHalfPlaneSet :=
  fun z hz => (intMoebius_holomorphicOn hdet z hz).differentiableWithinAt

/-- Compatibility with `Chapter14.moebiusMap` on the Riemann sphere at every point of `Π⁺`. -/
theorem intMoebius_coe_riemannSphere {a b c d : ℤ} (hdet : a * d - b * c = 1)
    {z : ℂ} (hz : z ∈ UpperHalfPlaneSet) :
    RudinRCA.Chapter14.moebiusMap (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) (z : OnePoint ℂ) =
      ((intMoebius a b c d z : ℂ) : OnePoint ℂ) := by
  simp [RudinRCA.Chapter14.moebiusMap_coe, intMoebius, intMoebius_denom_ne_zero hdet hz]

/-- **16.17 (Composition law = matrix multiplication on `Π⁺`, RCA p. 328):** -/
theorem intMoebius_comp {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ}
    (_h₁ : a₁ * d₁ - b₁ * c₁ = 1) (h₂ : a₂ * d₂ - b₂ * c₂ = 1)
    {z : ℂ} (hz : z ∈ UpperHalfPlaneSet) :
    intMoebius a₁ b₁ c₁ d₁ (intMoebius a₂ b₂ c₂ d₂ z) =
      intMoebius (a₁ * a₂ + b₁ * c₂) (a₁ * b₂ + b₁ * d₂)
        (c₁ * a₂ + d₁ * c₂) (c₁ * b₂ + d₁ * d₂) z := by
  have hden₂ : (c₂ : ℂ) * z + (d₂ : ℂ) ≠ 0 := intMoebius_denom_ne_zero h₂ hz
  unfold intMoebius
  have hnum_eq :
      (a₁ : ℂ) * (((a₂ : ℂ) * z + (b₂ : ℂ)) / ((c₂ : ℂ) * z + (d₂ : ℂ))) + (b₁ : ℂ) =
        (((a₁ * a₂ + b₁ * c₂ : ℤ) : ℂ) * z + ((a₁ * b₂ + b₁ * d₂ : ℤ) : ℂ)) /
          ((c₂ : ℂ) * z + (d₂ : ℂ)) := by
    rw [mul_div_assoc', div_add' _ _ _ hden₂]
    congr 1
    push_cast
    ring
  have hden_eq :
      (c₁ : ℂ) * (((a₂ : ℂ) * z + (b₂ : ℂ)) / ((c₂ : ℂ) * z + (d₂ : ℂ))) + (d₁ : ℂ) =
        (((c₁ * a₂ + d₁ * c₂ : ℤ) : ℂ) * z + ((c₁ * b₂ + d₁ * d₂ : ℤ) : ℂ)) /
          ((c₂ : ℂ) * z + (d₂ : ℂ)) := by
    rw [mul_div_assoc', div_add' _ _ _ hden₂]
    congr 1
    push_cast
    ring
  rw [hnum_eq, hden_eq, div_div_div_cancel_right₀ hden₂]

/-- **16.17 (Inverse formula `φ⁻¹(z) = (d z - b) / (-c z + a)` on `Π⁺`, RCA p. 328):** -/
theorem intMoebius_inv_left {a b c d : ℤ} (hdet : a * d - b * c = 1)
    {z : ℂ} (hz : z ∈ UpperHalfPlaneSet) :
    intMoebius d (-b) (-c) a (intMoebius a b c d z) = z := by
  have hdet_inv : d * a - (-b) * (-c) = 1 := by linear_combination hdet
  rw [intMoebius_comp hdet_inv hdet hz]
  have h1 : d * a + -b * c = 1 := by linear_combination hdet
  have h2 : d * b + -b * d = 0 := by ring
  have h3 : -c * a + a * c = 0 := by ring
  have h4 : -c * b + a * d = 1 := by linear_combination hdet
  rw [h1, h2, h3, h4, intMoebius_id]

theorem intMoebius_inv_right {a b c d : ℤ} (hdet : a * d - b * c = 1)
    {z : ℂ} (hz : z ∈ UpperHalfPlaneSet) :
    intMoebius a b c d (intMoebius d (-b) (-c) a z) = z := by
  have hdet_inv : d * a - (-b) * (-c) = 1 := by linear_combination hdet
  simpa using intMoebius_inv_left hdet_inv hz

theorem intMoebius_inv_formula (a b c d : ℤ) (z : ℂ) :
    intMoebius d (-b) (-c) a z = ((d : ℂ) * z - (b : ℂ)) / (-(c : ℂ) * z + (a : ℂ)) := by
  unfold intMoebius
  push_cast
  ring

/-- **16.17 (Induced bijection `Π⁺ ≃ Π⁺` for `a * d - b * c = 1`, RCA p. 328):** -/
def intMoebiusPerm (a b c d : ℤ) (hdet : a * d - b * c = 1) :
    Equiv.Perm UpperHalfPlaneSet where
  toFun z := ⟨intMoebius a b c d z.1, intMoebius_mem_upperHalfPlaneSet hdet z.2⟩
  invFun z := ⟨intMoebius d (-b) (-c) a z.1,
    intMoebius_mem_upperHalfPlaneSet (by linear_combination hdet) z.2⟩
  left_inv z := Subtype.ext (intMoebius_inv_left hdet z.2)
  right_inv z := Subtype.ext (intMoebius_inv_right hdet z.2)

@[simp]
theorem intMoebiusPerm_apply (a b c d : ℤ) (hdet : a * d - b * c = 1)
    (z : UpperHalfPlaneSet) :
    (intMoebiusPerm a b c d hdet z).1 = intMoebius a b c d z.1 :=
  rfl

theorem intMoebiusPerm_inv (a b c d : ℤ) (hdet : a * d - b * c = 1) :
    (intMoebiusPerm a b c d hdet)⁻¹ =
      intMoebiusPerm d (-b) (-c) a (by linear_combination hdet) := by
  ext ⟨z, hz⟩
  rfl

@[simp]
theorem intMoebiusPerm_one :
    intMoebiusPerm 1 0 0 1 (by norm_num) = (1 : Equiv.Perm UpperHalfPlaneSet) := by
  ext ⟨z, hz⟩
  simp [intMoebiusPerm]

theorem intMoebiusPerm_neg (a b c d : ℤ) (hdet : a * d - b * c = 1) :
    intMoebiusPerm (-a) (-b) (-c) (-d) (by linear_combination hdet) =
      intMoebiusPerm a b c d hdet := by
  ext ⟨z, hz⟩
  simp [intMoebiusPerm]

theorem intMoebiusPerm_mul {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ}
    (h₁ : a₁ * d₁ - b₁ * c₁ = 1) (h₂ : a₂ * d₂ - b₂ * c₂ = 1) :
    intMoebiusPerm a₁ b₁ c₁ d₁ h₁ * intMoebiusPerm a₂ b₂ c₂ d₂ h₂ =
      intMoebiusPerm (a₁ * a₂ + b₁ * c₂) (a₁ * b₂ + b₁ * d₂)
        (c₁ * a₂ + d₁ * c₂) (c₁ * b₂ + d₁ * d₂)
        (by
          calc
            (a₁ * a₂ + b₁ * c₂) * (c₁ * b₂ + d₁ * d₂) -
                (a₁ * b₂ + b₁ * d₂) * (c₁ * a₂ + d₁ * c₂)
              = (a₁ * d₁ - b₁ * c₁) * (a₂ * d₂ - b₂ * c₂) := by ring
            _ = 1 := by rw [h₁, h₂]; ring) := by
  ext ⟨z, hz⟩
  exact intMoebius_comp h₁ h₂ hz

/-- **16.17 (The modular group `G` as a subgroup of `Perm Π⁺`, RCA p. 328):**
`ModularMoebiusGroup` consists of all bijections of `Π⁺` of the form
`z ↦ (a z + b) / (c z + d)` with `a, b, c, d : ℤ` and `a * d - b * c = 1`. -/
def ModularMoebiusGroup : Subgroup (Equiv.Perm UpperHalfPlaneSet) where
  carrier := {φ | ∃ a b c d : ℤ, ∃ hdet : a * d - b * c = 1, φ = intMoebiusPerm a b c d hdet}
  one_mem' := ⟨1, 0, 0, 1, by norm_num, intMoebiusPerm_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a₁, b₁, c₁, d₁, h₁, rfl⟩ ⟨a₂, b₂, c₂, d₂, h₂, rfl⟩
    have hdet₃ :
        (a₁ * a₂ + b₁ * c₂) * (c₁ * b₂ + d₁ * d₂) -
          (a₁ * b₂ + b₁ * d₂) * (c₁ * a₂ + d₁ * c₂) = 1 := by
      calc
        (a₁ * a₂ + b₁ * c₂) * (c₁ * b₂ + d₁ * d₂) -
            (a₁ * b₂ + b₁ * d₂) * (c₁ * a₂ + d₁ * c₂)
          = (a₁ * d₁ - b₁ * c₁) * (a₂ * d₂ - b₂ * c₂) := by ring
        _ = 1 := by rw [h₁, h₂]; ring
    exact ⟨a₁ * a₂ + b₁ * c₂, a₁ * b₂ + b₁ * d₂, c₁ * a₂ + d₁ * c₂, c₁ * b₂ + d₁ * d₂,
      hdet₃, intMoebiusPerm_mul h₁ h₂⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, d, hdet, rfl⟩
    exact ⟨d, -b, -c, a, by linear_combination hdet, intMoebiusPerm_inv a b c d hdet⟩

@[ext]
theorem ModularMoebiusGroup.ext {φ ψ : ModularMoebiusGroup}
    (h : ∀ z : UpperHalfPlaneSet, (φ.1 z).1 = (ψ.1 z).1) : φ = ψ := by
  apply Subtype.ext
  ext z
  exact h z

@[simp]
theorem ModularMoebiusGroup.one_apply (z : UpperHalfPlaneSet) :
    (((1 : ModularMoebiusGroup).1 z).1) = z.1 :=
  rfl

@[simp]
theorem ModularMoebiusGroup.mul_apply (φ ψ : ModularMoebiusGroup) (z : UpperHalfPlaneSet) :
    (((φ * ψ).1 z).1) = (φ.1 (ψ.1 z)).1 :=
  rfl

theorem sl2z_det_eq_one (A : SL(2, ℤ)) :
    A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0 = 1 := by
  rw [← Matrix.det_fin_two]
  exact A.2

/-- Homomorphism from `SL(2, ℤ)` into `Equiv.Perm UpperHalfPlaneSet`. -/
def sl2zToPerm : SL(2, ℤ) →* Equiv.Perm UpperHalfPlaneSet where
  toFun A := intMoebiusPerm (A.1 0 0) (A.1 0 1) (A.1 1 0) (A.1 1 1) (sl2z_det_eq_one A)
  map_one' := by
    ext ⟨z, hz⟩
    simp [intMoebiusPerm]
  map_mul' A B := by
    ext ⟨z, hz⟩
    have hcomp := intMoebius_comp (sl2z_det_eq_one A) (sl2z_det_eq_one B) hz
    simpa [intMoebiusPerm, Matrix.mul_apply, Fin.sum_univ_two] using hcomp.symm

/-- Canonical surjective group homomorphism `SL(2, ℤ) →* ModularMoebiusGroup`. -/
def sl2zToMoebius : SL(2, ℤ) →* ModularMoebiusGroup where
  toFun A := ⟨sl2zToPerm A, A.1 0 0, A.1 0 1, A.1 1 0, A.1 1 1, sl2z_det_eq_one A, rfl⟩
  map_one' := Subtype.ext sl2zToPerm.map_one
  map_mul' A B := Subtype.ext (sl2zToPerm.map_mul A B)

theorem sl2zToMoebius_apply (A : SL(2, ℤ)) (z : UpperHalfPlaneSet) :
    ((sl2zToMoebius A).1 z).1 = intMoebius (A.1 0 0) (A.1 0 1) (A.1 1 0) (A.1 1 1) z.1 :=
  rfl

@[simp]
theorem sl2zToMoebius_neg (A : SL(2, ℤ)) :
    sl2zToMoebius (-A) = sl2zToMoebius A := by
  ext z
  simp [sl2zToMoebius_apply]

theorem sl2zToMoebius_surjective : Function.Surjective sl2zToMoebius := by
  rintro ⟨φ, a, b, c, d, hdet, rfl⟩
  let A : SL(2, ℤ) := ⟨!![a, b; c, d], by simpa [Matrix.det_fin_two_of] using hdet⟩
  refine ⟨A, ?_⟩
  ext z
  rfl

/-- Characterization of when `intMoebiusPerm a b c d hdet = 1`: `(a,b,c,d) = ±(1,0,0,1)`. -/
theorem intMoebiusPerm_eq_one_iff {a b c d : ℤ} (hdet : a * d - b * c = 1) :
    intMoebiusPerm a b c d hdet = 1 ↔
      (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = -1 ∧ b = 0 ∧ c = 0 ∧ d = -1) := by
  constructor
  · intro h1
    have hI : intMoebius a b c d Complex.I = Complex.I := by
      have := congrArg (fun f : Equiv.Perm UpperHalfPlaneSet =>
        (f ⟨Complex.I, I_mem_upperHalfPlaneSet⟩).1) h1
      simpa using this
    have h2I_mem : (2 : ℂ) * Complex.I ∈ UpperHalfPlaneSet := by
      simp [UpperHalfPlaneSet]
    have h2I : intMoebius a b c d ((2 : ℂ) * Complex.I) = (2 : ℂ) * Complex.I := by
      have := congrArg (fun f : Equiv.Perm UpperHalfPlaneSet =>
        (f ⟨(2 : ℂ) * Complex.I, h2I_mem⟩).1) h1
      simpa using this
    have hden1 : (c : ℂ) * Complex.I + (d : ℂ) ≠ 0 :=
      intMoebius_denom_ne_zero hdet I_mem_upperHalfPlaneSet
    have hden2 : (c : ℂ) * ((2 : ℂ) * Complex.I) + (d : ℂ) ≠ 0 :=
      intMoebius_denom_ne_zero hdet h2I_mem
    unfold intMoebius at hI h2I
    have eq1 : (a : ℂ) * Complex.I + (b : ℂ) = Complex.I * ((c : ℂ) * Complex.I + (d : ℂ)) :=
      (div_eq_iff hden1).mp hI
    have eq2 : (a : ℂ) * ((2 : ℂ) * Complex.I) + (b : ℂ) =
        ((2 : ℂ) * Complex.I) * ((c : ℂ) * ((2 : ℂ) * Complex.I) + (d : ℂ)) :=
      (div_eq_iff hden2).mp h2I
    have hre1 : (b : ℝ) = -(c : ℝ) := by
      have := congrArg Complex.re eq1
      simpa [Complex.add_re, Complex.mul_re] using this
    have him1 : (a : ℝ) = (d : ℝ) := by
      have := congrArg Complex.im eq1
      simpa [Complex.add_im, Complex.mul_im] using this
    have hre2 : (b : ℝ) = -4 * (c : ℝ) := by
      have := congrArg Complex.re eq2
      simp only [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im,
        Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat,
        Complex.I_re, Complex.I_im] at this
      linarith
    have hc_real : (c : ℝ) = 0 := by linarith
    have hb_real : (b : ℝ) = 0 := by linarith
    have hc0 : c = 0 := Int.cast_eq_zero.mp hc_real
    have hb0 : b = 0 := Int.cast_eq_zero.mp hb_real
    have had_eq : a = d := Int.cast_inj.mp him1
    subst hc0; subst hb0; subst had_eq
    have ha2 : a * a = 1 := by linarith
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp ha2 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · left; simp
    · right; simp
  · rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩)
    · exact intMoebiusPerm_one
    · ext ⟨z, hz⟩
      simp [intMoebiusPerm, intMoebius, neg_div_neg_eq]

/-- Kernel of `sl2zToMoebius : SL(2, ℤ) →* ModularMoebiusGroup` is `{1, -1}`. -/
theorem sl2zToMoebius_eq_one_iff (A : SL(2, ℤ)) :
    sl2zToMoebius A = 1 ↔ A = 1 ∨ A = -1 := by
  constructor
  · intro h
    have hp : sl2zToPerm A = 1 := congrArg Subtype.val h
    rcases (intMoebiusPerm_eq_one_iff (sl2z_det_eq_one A)).mp hp with
      ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
    · left
      ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
    · right
      ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
  · rintro (rfl | rfl)
    · exact map_one sl2zToMoebius
    · rw [sl2zToMoebius_neg, map_one]

theorem sl2zToMoebius_ker :
    (sl2zToMoebius.ker : Set SL(2, ℤ)) = {1, -1} := by
  ext A
  simp [MonoidHom.mem_ker, sl2zToMoebius_eq_one_iff]

theorem sl2zToMoebius_eq_iff (A B : SL(2, ℤ)) :
    sl2zToMoebius A = sl2zToMoebius B ↔ A = B ∨ A = -B := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, sl2zToMoebius_eq_one_iff, mul_inv_eq_one]
  refine or_congr Iff.rfl ?_
  constructor
  · intro h
    have := congrArg (· * B) h
    simpa [inv_mul_cancel_right] using this
  · rintro rfl
    simp

/-- **16.17 (Generator `z ↦ z + 1` of the modular group, RCA p. 328):** -/
def modularT : ModularMoebiusGroup :=
  sl2zToMoebius ModularGroup.T

/-- **16.17 (Generator `z ↦ -1 / z` of the modular group, RCA p. 328):** -/
def modularS : ModularMoebiusGroup :=
  sl2zToMoebius ModularGroup.S

@[simp]
theorem modularT_apply (z : UpperHalfPlaneSet) :
    (modularT.1 z).1 = z.1 + 1 := by
  rw [modularT, sl2zToMoebius_apply]
  simp [ModularGroup.T, intMoebius]

theorem modularT_zpow_apply (n : ℤ) (z : UpperHalfPlaneSet) :
    ((modularT ^ n).1 z).1 = z.1 + (n : ℂ) := by
  have h : modularT ^ n = sl2zToMoebius (ModularGroup.T ^ n) := (map_zpow sl2zToMoebius _ n).symm
  rw [h, sl2zToMoebius_apply, ModularGroup.coe_T_zpow]
  simp [intMoebius]

@[simp]
theorem modularS_apply (z : UpperHalfPlaneSet) :
    (modularS.1 z).1 = -1 / z.1 := by
  rw [modularS, sl2zToMoebius_apply]
  simp [ModularGroup.S, intMoebius, neg_div]

theorem modularS_sq : modularS ^ 2 = 1 := by
  ext z
  simp [sq, modularS_apply]

@[simp]
theorem modularS_inv : modularS⁻¹ = modularS := by
  apply inv_eq_of_mul_eq_one_right
  simpa [sq] using modularS_sq

theorem modularT_ne_one : modularT ≠ 1 := by
  intro h
  have := congrArg (fun φ : ModularMoebiusGroup =>
    (φ.1 ⟨Complex.I, I_mem_upperHalfPlaneSet⟩).1) h
  simp [modularT_apply] at this

theorem modularMoebiusGroup_top_ne_bot : (⊤ : Subgroup ModularMoebiusGroup) ≠ ⊥ := by
  intro h
  have hT : modularT ∈ (⊥ : Subgroup ModularMoebiusGroup) := h ▸ Subgroup.mem_top modularT
  exact modularT_ne_one (Subgroup.mem_bot.mp hT)

/-- **16.17 (`ModularMoebiusGroup` is generated by `modularS` and `modularT`, RCA p. 328):**
`z ↦ -1/z` and `z ↦ z + 1` generate the entire modular group `G`. -/
theorem modularMoebiusGroup_closure_S_T :
    Subgroup.closure ({modularS, modularT} : Set ModularMoebiusGroup) = ⊤ := by
  have hgen := congrArg (Subgroup.map sl2zToMoebius) SpecialLinearGroup.SL2Z_generators
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective sl2zToMoebius sl2zToMoebius_surjective]
    at hgen
  simpa [Set.image_pair, modularS, modularT] using hgen

/-- **16.17 (Modular function for a nontrivial subgroup `H ≤ G`, RCA p. 328):**
`f` is holomorphic on `Π⁺` and invariant under a nontrivial subgroup `H` of `G`. -/
def IsModularFunctionFor (H : Subgroup ModularMoebiusGroup) (f : ℂ → ℂ) : Prop :=
  H ≠ ⊥ ∧ DifferentiableOn ℂ f UpperHalfPlaneSet ∧
    ∀ γ : H, ∀ z : UpperHalfPlaneSet, f ((γ.1.1 z).1) = f z.1

/-- **16.17 (Full modular function invariant under the entire modular group `G`, RCA p. 328):** -/
def IsFullModularFunction (f : ℂ → ℂ) : Prop :=
  IsModularFunctionFor ⊤ f

/-- **16.17 (Modular function in the general sense of RCA p. 328 — invariant under `G` or some
nontrivial subgroup of `G`):** -/
def IsModularFunction (f : ℂ → ℂ) : Prop :=
  ∃ H : Subgroup ModularMoebiusGroup, IsModularFunctionFor H f

theorem isFullModularFunction_iff (f : ℂ → ℂ) :
    IsFullModularFunction f ↔
      DifferentiableOn ℂ f UpperHalfPlaneSet ∧
        ∀ φ : ModularMoebiusGroup, ∀ z : UpperHalfPlaneSet, f ((φ.1 z).1) = f z.1 := by
  unfold IsFullModularFunction IsModularFunctionFor
  constructor
  · rintro ⟨_, hdiff, hinv⟩
    exact ⟨hdiff, fun φ z => hinv ⟨φ, Subgroup.mem_top φ⟩ z⟩
  · rintro ⟨hdiff, hinv⟩
    exact ⟨modularMoebiusGroup_top_ne_bot, hdiff, fun γ z => hinv γ.1 z⟩

theorem IsModularFunctionFor.isModularFunction {H : Subgroup ModularMoebiusGroup} {f : ℂ → ℂ}
    (hf : IsModularFunctionFor H f) : IsModularFunction f :=
  ⟨H, hf⟩

theorem IsFullModularFunction.isModularFunction {f : ℂ → ℂ}
    (hf : IsFullModularFunction f) : IsModularFunction f :=
  ⟨⊤, hf⟩

theorem differentiableOn_upperHalfPlaneSet_iff_holomorphicOn (f : ℂ → ℂ) :
    DifferentiableOn ℂ f UpperHalfPlaneSet ↔
      RudinRCA.Chapter10.HolomorphicOn f UpperHalfPlaneSet := by
  constructor
  · intro hf z hz
    exact (hf z hz).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hz)
  · intro hf z hz
    exact (hf z hz).differentiableWithinAt

/-- **Node 16.17 (The Modular Group, RCA p. 328):**
Packages the properties of determinant-one integral Möbius transformations on `Π⁺`:
1. Nonvanishing denominator `(c : ℂ) * z + d ≠ 0`, `Im(φ(z)) = Im(z) / ‖c z + d‖² > 0`, and
   holomorphicity on `Π⁺`;
2. Composition via matrix multiplication and explicit inverse `(d z - b) / (-c z + a)`, forming
   the group `ModularMoebiusGroup`;
3. Generation of `ModularMoebiusGroup` by `modularS` (`z ↦ -1 / z`) and `modularT` (`z ↦ z + 1`);
4. Characterization of full modular functions on `Π⁺`. -/
theorem theorem16_17 :
    (∀ {a b c d : ℤ}, a * d - b * c = 1 →
      DifferentiableOn ℂ (intMoebius a b c d) UpperHalfPlaneSet ∧
      ∀ z ∈ UpperHalfPlaneSet,
        (c : ℂ) * z + (d : ℂ) ≠ 0 ∧
        (intMoebius a b c d z).im = z.im / ‖(c : ℂ) * z + (d : ℂ)‖ ^ 2 ∧
        intMoebius a b c d z ∈ UpperHalfPlaneSet ∧
        intMoebius d (-b) (-c) a (intMoebius a b c d z) = z ∧
        intMoebius a b c d (intMoebius d (-b) (-c) a z) = z) ∧
    ((∀ z : UpperHalfPlaneSet, (modularT.1 z).1 = z.1 + 1) ∧
      (∀ z : UpperHalfPlaneSet, (modularS.1 z).1 = -1 / z.1) ∧
      Subgroup.closure ({modularS, modularT} : Set ModularMoebiusGroup) = ⊤) ∧
    (∀ f : ℂ → ℂ, IsFullModularFunction f ↔
      DifferentiableOn ℂ f UpperHalfPlaneSet ∧
        ∀ φ : ModularMoebiusGroup, ∀ z : UpperHalfPlaneSet, f ((φ.1 z).1) = f z.1) := by
  refine ⟨?_, ⟨modularT_apply, modularS_apply, modularMoebiusGroup_closure_S_T⟩,
    isFullModularFunction_iff⟩
  intro a b c d hdet
  refine ⟨intMoebius_differentiableOn hdet, fun z hz => ?_⟩
  exact ⟨intMoebius_denom_ne_zero hdet hz, intMoebius_im hdet z,
    intMoebius_mem_upperHalfPlaneSet hdet hz,
    intMoebius_inv_left hdet hz, intMoebius_inv_right hdet hz⟩

/-! ### Node 16.18: A Subgroup `Γ` and Fundamental Set `Q` (RCA pp. 328–329) -/

/-- Matrix `[[1, 0], [2, 1]] ∈ SL(2, ℤ)` representing `σ(z) = z / (2 z + 1)`. -/
def sigmaMatrix : SL(2, ℤ) :=
  ⟨!![1, 0; 2, 1], by simp [Matrix.det_fin_two_of]⟩

/-- Matrix `[[1, 2], [0, 1]] ∈ SL(2, ℤ)` representing `τ(z) = z + 2`. -/
def tauMatrix : SL(2, ℤ) :=
  ⟨!![1, 2; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- Matrix `[[1, 0], [-2, 1]] ∈ SL(2, ℤ)` representing `σ⁻¹(z) = z / (-2 z + 1)`. -/
def sigmaInvMatrix : SL(2, ℤ) :=
  ⟨!![1, 0; -2, 1], by simp [Matrix.det_fin_two_of]⟩

/-- **16.18 (Generator `σ(z) = z / (2 z + 1)`, RCA p. 328):** -/
def modularSigma : ModularMoebiusGroup :=
  sl2zToMoebius sigmaMatrix

/-- **16.18 (Generator `τ(z) = z + 2`, RCA p. 328):** -/
def modularTau : ModularMoebiusGroup :=
  sl2zToMoebius tauMatrix

@[simp]
theorem modularSigma_apply (z : UpperHalfPlaneSet) :
    (modularSigma.1 z).1 = z.1 / (2 * z.1 + 1) := by
  rw [modularSigma, sl2zToMoebius_apply]
  simp [sigmaMatrix, intMoebius]

theorem sigmaMatrix_inv : sigmaMatrix⁻¹ = sigmaInvMatrix := by
  ext i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j <;> simp [sigmaMatrix, sigmaInvMatrix]

@[simp]
theorem modularSigma_inv_apply (z : UpperHalfPlaneSet) :
    (modularSigma⁻¹.1 z).1 = z.1 / (-2 * z.1 + 1) := by
  have h : modularSigma⁻¹ = sl2zToMoebius sigmaInvMatrix := by
    rw [modularSigma, ← map_inv, sigmaMatrix_inv]
  rw [h, sl2zToMoebius_apply]
  simp [sigmaInvMatrix, intMoebius]

@[simp]
theorem modularTau_apply (z : UpperHalfPlaneSet) :
    (modularTau.1 z).1 = z.1 + 2 := by
  rw [modularTau, sl2zToMoebius_apply]
  simp [tauMatrix, intMoebius]

theorem modularTau_eq_T_sq : modularTau = modularT ^ 2 := by
  ext z
  simp [sq]
  ring

theorem modularSigma_eq_S_T_S :
    modularSigma = modularS⁻¹ * (modularT⁻¹ ^ 2) * modularS := by
  ext z
  have hT2 : modularT⁻¹ ^ 2 = modularT ^ (-2 : ℤ) := by group
  rw [modularS_inv, hT2, ModularMoebiusGroup.mul_apply, ModularMoebiusGroup.mul_apply,
    modularS_apply, modularT_zpow_apply, modularS_apply, modularSigma_apply]
  have hz_ne : z.1 ≠ 0 := by
    intro h0
    have := z.2
    rw [mem_upperHalfPlaneSet, h0, Complex.zero_im] at this
    exact lt_irrefl 0 this
  have hden_ne : (2 : ℂ) * z.1 + 1 ≠ 0 := by
    simpa using intMoebius_denom_ne_zero (a := 1) (b := 0) (c := 2) (d := 1) (by norm_num) z.2
  have hmid_ne : -1 / z.1 + (-2 : ℂ) ≠ 0 := by
    intro h0
    apply hden_ne
    have := congrArg (· * z.1) h0
    rw [zero_mul, add_mul, div_mul_cancel₀ (-1) hz_ne] at this
    linear_combination -this
  push_cast
  rw [div_eq_div_iff hden_ne hmid_ne, mul_add, mul_div_cancel₀ (-1) hz_ne]
  ring

theorem modularTau_zpow_apply (k : ℤ) (z : UpperHalfPlaneSet) :
    ((modularTau ^ k).1 z).1 = z.1 + 2 * (k : ℂ) := by
  have h : modularTau ^ k = modularT ^ (2 * k) := by
    rw [modularTau_eq_T_sq, ← zpow_natCast, ← zpow_mul]
    rfl
  rw [h, modularT_zpow_apply]
  push_cast
  ring

/-- **16.18 (The subgroup `Γ = ⟨σ, τ⟩ ≤ G`, RCA p. 328):** -/
def GammaSubgroup : Subgroup ModularMoebiusGroup :=
  Subgroup.closure {modularSigma, modularTau}

theorem modularSigma_mem_gamma : modularSigma ∈ GammaSubgroup :=
  Subgroup.subset_closure (Set.mem_insert modularSigma {modularTau})

theorem modularTau_mem_gamma : modularTau ∈ GammaSubgroup :=
  Subgroup.subset_closure (Set.mem_insert_of_mem modularSigma rfl)

theorem modularTau_ne_one : modularTau ≠ 1 := by
  intro h
  have := congrArg (fun φ : ModularMoebiusGroup =>
    (φ.1 ⟨Complex.I, I_mem_upperHalfPlaneSet⟩).1) h
  simp [modularTau_apply] at this

theorem gammaSubgroup_ne_bot : GammaSubgroup ≠ ⊥ := by
  intro h
  have hτ : modularTau ∈ (⊥ : Subgroup ModularMoebiusGroup) := h ▸ modularTau_mem_gamma
  exact modularTau_ne_one (Subgroup.mem_bot.mp hτ)

/-- **16.18 (Rudin's exact fundamental set `Q`, RCA p. 329 eq. (2)):**
`Q = {x + i y : y > 0, -1 ≤ x < 1, |2 z + 1| ≥ 1, |2 z - 1| > 1}`.
Note the mixed strict and non-strict boundary inequalities (`SCOPING-G.md` line 81). -/
def FundamentalSetQ : Set ℂ :=
  {z : ℂ | 0 < z.im ∧ -1 ≤ z.re ∧ z.re < 1 ∧ 1 ≤ ‖2 * z + 1‖ ∧ 1 < ‖2 * z - 1‖}

theorem fundamentalSetQ_subset_upperHalfPlaneSet :
    FundamentalSetQ ⊆ UpperHalfPlaneSet :=
  fun _ hz => hz.1

theorem norm_two_mul_add_one_sq (z : ℂ) :
    ‖2 * z + 1‖ ^ 2 = 4 * (z.re ^ 2 + z.im ^ 2) + 4 * z.re + 1 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.one_re, Complex.add_im, Complex.mul_im, Complex.one_im]
  ring

theorem norm_two_mul_sub_one_sq (z : ℂ) :
    ‖2 * z - 1‖ ^ 2 = 4 * (z.re ^ 2 + z.im ^ 2) - 4 * z.re + 1 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.one_re, Complex.sub_im, Complex.mul_im, Complex.one_im]
  ring

theorem one_le_norm_two_mul_add_one_iff (z : ℂ) :
    1 ≤ ‖2 * z + 1‖ ↔ -z.re ≤ z.re ^ 2 + z.im ^ 2 := by
  have hnn : 0 ≤ ‖2 * z + 1‖ := norm_nonneg _
  have hsq := norm_two_mul_add_one_sq z
  constructor
  · intro h
    have : 1 ≤ ‖2 * z + 1‖ ^ 2 := by nlinarith
    linarith
  · intro h
    have : 1 ≤ ‖2 * z + 1‖ ^ 2 := by linarith
    nlinarith

theorem one_lt_norm_two_mul_sub_one_iff (z : ℂ) :
    1 < ‖2 * z - 1‖ ↔ z.re < z.re ^ 2 + z.im ^ 2 := by
  have hnn : 0 ≤ ‖2 * z - 1‖ := norm_nonneg _
  have hsq := norm_two_mul_sub_one_sq z
  constructor
  · intro h
    have : 1 < ‖2 * z - 1‖ ^ 2 := by nlinarith
    linarith
  · intro h
    have : 1 < ‖2 * z - 1‖ ^ 2 := by linarith
    nlinarith

theorem norm_two_mul_add_one_eq_one_iff (z : ℂ) :
    ‖2 * z + 1‖ = 1 ↔ z.re ^ 2 + z.im ^ 2 = -z.re := by
  have hnn : 0 ≤ ‖2 * z + 1‖ := norm_nonneg _
  have hsq := norm_two_mul_add_one_sq z
  constructor
  · intro h
    have : ‖2 * z + 1‖ ^ 2 = 1 := by rw [h]; ring
    linarith
  · intro h
    have : ‖2 * z + 1‖ ^ 2 = 1 := by linarith
    nlinarith

theorem norm_two_mul_sub_one_eq_one_iff (z : ℂ) :
    ‖2 * z - 1‖ = 1 ↔ z.re ^ 2 + z.im ^ 2 = z.re := by
  have hnn : 0 ≤ ‖2 * z - 1‖ := norm_nonneg _
  have hsq := norm_two_mul_sub_one_sq z
  constructor
  · intro h
    have : ‖2 * z - 1‖ ^ 2 = 1 := by rw [h]; ring
    linarith
  · intro h
    have : ‖2 * z - 1‖ ^ 2 = 1 := by linarith
    nlinarith

theorem I_mem_fundamentalSetQ : Complex.I ∈ FundamentalSetQ := by
  refine ⟨by simp, by simp, by simp, ?_, ?_⟩
  · rw [one_le_norm_two_mul_add_one_iff]
    norm_num
  · rw [one_lt_norm_two_mul_sub_one_iff]
    norm_num

/-- **Node 16.18 (Subgroup `Γ` and Fundamental Set `Q`, RCA pp. 328–329):**
Packages the generators `modularSigma` (`z ↦ z / (2 z + 1)`) and `modularTau` (`z ↦ z + 2`),
their expressions in terms of `modularS` and `modularT`, the nontrivial subgroup `GammaSubgroup`,
and the fundamental set `FundamentalSetQ ⊆ Π⁺` containing `i`. -/
theorem theorem16_18 :
    ((∀ z : UpperHalfPlaneSet, (modularSigma.1 z).1 = z.1 / (2 * z.1 + 1)) ∧
      (∀ z : UpperHalfPlaneSet, (modularTau.1 z).1 = z.1 + 2) ∧
      modularSigma = modularS⁻¹ * (modularT⁻¹ ^ 2) * modularS ∧
      modularTau = modularT ^ 2) ∧
    (GammaSubgroup = Subgroup.closure {modularSigma, modularTau} ∧
      GammaSubgroup ≠ ⊥) ∧
    (FundamentalSetQ ⊆ UpperHalfPlaneSet ∧ Complex.I ∈ FundamentalSetQ) :=
  ⟨⟨modularSigma_apply, modularTau_apply, modularSigma_eq_S_T_S, modularTau_eq_T_sq⟩,
    ⟨rfl, gammaSubgroup_ne_bot⟩,
    ⟨fundamentalSetQ_subset_upperHalfPlaneSet, I_mem_fundamentalSetQ⟩⟩

/-! ### Node 16.19: Fundamental Domain & Parity Characterization of `Γ` (RCA pp. 329–330) -/

private lemma odd_mul_odd_add_even_mul_even {a₁ a₂ b₁ c₂ : ℤ}
    (ha₁ : Odd a₁) (ha₂ : Odd a₂) (hb₁ : Even b₁) (hc₂ : Even c₂) :
    Odd (a₁ * a₂ + b₁ * c₂) := by
  rcases ha₁ with ⟨k₁, rfl⟩
  rcases ha₂ with ⟨k₂, rfl⟩
  rcases hb₁ with ⟨m₁, rfl⟩
  rcases hc₂ with ⟨n₂, rfl⟩
  exact ⟨2 * k₁ * k₂ + k₁ + k₂ + 2 * m₁ * n₂, by ring⟩

private lemma even_mul_even_add_odd_mul_odd {c₁ b₂ d₁ d₂ : ℤ}
    (hc₁ : Even c₁) (hb₂ : Even b₂) (hd₁ : Odd d₁) (hd₂ : Odd d₂) :
    Odd (c₁ * b₂ + d₁ * d₂) := by
  rcases hc₁ with ⟨m₁, rfl⟩
  rcases hb₂ with ⟨n₂, rfl⟩
  rcases hd₁ with ⟨k₁, rfl⟩
  rcases hd₂ with ⟨k₂, rfl⟩
  exact ⟨2 * m₁ * n₂ + 2 * k₁ * k₂ + k₁ + k₂, by ring⟩

private lemma odd_mul_even_add_even_mul_odd {a₁ b₂ b₁ d₂ : ℤ}
    (ha₁ : Odd a₁) (hb₂ : Even b₂) (hb₁ : Even b₁) (hd₂ : Odd d₂) :
    Even (a₁ * b₂ + b₁ * d₂) := by
  rcases ha₁ with ⟨k₁, rfl⟩
  rcases hb₂ with ⟨n₂, rfl⟩
  rcases hb₁ with ⟨m₁, rfl⟩
  rcases hd₂ with ⟨k₂, rfl⟩
  exact ⟨(2 * k₁ + 1) * n₂ + m₁ * (2 * k₂ + 1), by ring⟩

private lemma even_mul_odd_add_odd_mul_even {c₁ a₂ d₁ c₂ : ℤ}
    (hc₁ : Even c₁) (ha₂ : Odd a₂) (hd₁ : Odd d₁) (hc₂ : Even c₂) :
    Even (c₁ * a₂ + d₁ * c₂) := by
  rcases hc₁ with ⟨m₁, rfl⟩
  rcases ha₂ with ⟨k₂, rfl⟩
  rcases hd₁ with ⟨k₁, rfl⟩
  rcases hc₂ with ⟨n₂, rfl⟩
  exact ⟨m₁ * (2 * k₂ + 1) + (2 * k₁ + 1) * n₂, by ring⟩

private lemma even_neg_int {n : ℤ} (hn : Even n) : Even (-n) := by
  rcases hn with ⟨k, rfl⟩
  exact ⟨-k, by ring⟩

private lemma odd_neg_int {n : ℤ} (hn : Odd n) : Odd (-n) := by
  rcases hn with ⟨k, rfl⟩
  exact ⟨-k - 1, by ring⟩

private lemma int_one_le_sq_of_ne_zero {u : ℤ} (hu : u ≠ 0) : 1 ≤ u ^ 2 := by
  rcases lt_trichotomy u 0 with hlt | rfl | hgt
  · have : u ≤ -1 := by omega
    nlinarith
  · exact absurd rfl hu
  · have : 1 ≤ u := by omega
    nlinarith

/-- **16.19 (Parity subgroup of `ModularMoebiusGroup`, RCA p. 329):**
Transformations in `ModularMoebiusGroup` represented by `(a, b, c, d : ℤ)` with
`a * d - b * c = 1`, `Odd a`, `Odd d`, `Even b`, and `Even c`. -/
def ParityMoebiusSubgroup : Subgroup ModularMoebiusGroup where
  carrier := {φ | ∃ a b c d : ℤ, ∃ hdet : a * d - b * c = 1,
    Odd a ∧ Odd d ∧ Even b ∧ Even c ∧ φ.1 = intMoebiusPerm a b c d hdet}
  one_mem' := ⟨1, 0, 0, 1, by norm_num, ⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩,
    intMoebiusPerm_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a₁, b₁, c₁, d₁, h₁, ha₁, hd₁, hb₁, hc₁, hφ₁⟩
      ⟨a₂, b₂, c₂, d₂, h₂, ha₂, hd₂, hb₂, hc₂, hφ₂⟩
    have hdet₃ :
        (a₁ * a₂ + b₁ * c₂) * (c₁ * b₂ + d₁ * d₂) -
          (a₁ * b₂ + b₁ * d₂) * (c₁ * a₂ + d₁ * c₂) = 1 := by
      calc
        (a₁ * a₂ + b₁ * c₂) * (c₁ * b₂ + d₁ * d₂) -
            (a₁ * b₂ + b₁ * d₂) * (c₁ * a₂ + d₁ * c₂)
          = (a₁ * d₁ - b₁ * c₁) * (a₂ * d₂ - b₂ * c₂) := by ring
        _ = 1 := by rw [h₁, h₂]; ring
    refine ⟨a₁ * a₂ + b₁ * c₂, a₁ * b₂ + b₁ * d₂, c₁ * a₂ + d₁ * c₂, c₁ * b₂ + d₁ * d₂,
      hdet₃,
      odd_mul_odd_add_even_mul_even ha₁ ha₂ hb₁ hc₂,
      even_mul_even_add_odd_mul_odd hc₁ hb₂ hd₁ hd₂,
      odd_mul_even_add_even_mul_odd ha₁ hb₂ hb₁ hd₂,
      even_mul_odd_add_odd_mul_even hc₁ ha₂ hd₁ hc₂, ?_⟩
    change (_ : Equiv.Perm UpperHalfPlaneSet) * _ = _
    rw [hφ₁, hφ₂]
    exact intMoebiusPerm_mul h₁ h₂
  inv_mem' := by
    rintro φ ⟨a, b, c, d, hdet, ha, hd, hb, hc, hφ⟩
    refine ⟨d, -b, -c, a, by linear_combination hdet, hd, ha, even_neg_int hb, even_neg_int hc, ?_⟩
    change (φ.1)⁻¹ = _
    rw [hφ]
    exact intMoebiusPerm_inv a b c d hdet

theorem modularSigma_mem_parityMoebiusSubgroup : modularSigma ∈ ParityMoebiusSubgroup :=
  ⟨1, 0, 2, 1, by norm_num, ⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩, ⟨1, by ring⟩, rfl⟩

theorem modularTau_mem_parityMoebiusSubgroup : modularTau ∈ ParityMoebiusSubgroup :=
  ⟨1, 2, 0, 1, by norm_num, ⟨0, by ring⟩, ⟨0, by ring⟩, ⟨1, by ring⟩, ⟨0, by ring⟩, rfl⟩

theorem gammaSubgroup_le_parityMoebiusSubgroup : GammaSubgroup ≤ ParityMoebiusSubgroup := by
  rw [GammaSubgroup, Subgroup.closure_le]
  intro φ hφ
  rcases hφ with rfl | hτ
  · exact modularSigma_mem_parityMoebiusSubgroup
  · rw [Set.mem_singleton_iff.mp hτ]
    exact modularTau_mem_parityMoebiusSubgroup

/-- Translate of a subset `E ⊆ ℂ` (intersected with `Π⁺`) by `φ ∈ ModularMoebiusGroup`. -/
def moebiusTranslate (φ : ModularMoebiusGroup) (E : Set ℂ) : Set ℂ :=
  Subtype.val '' (φ.1 '' {z : UpperHalfPlaneSet | z.1 ∈ E})

theorem mem_moebiusTranslate_iff {φ : ModularMoebiusGroup} {E : Set ℂ} {w : ℂ} :
    w ∈ moebiusTranslate φ E ↔
      ∃ z : UpperHalfPlaneSet, z.1 ∈ E ∧ (φ.1 z).1 = w := by
  constructor
  · rintro ⟨u, ⟨z, hzE, rfl⟩, rfl⟩
    exact ⟨z, hzE, rfl⟩
  · rintro ⟨z, hzE, rfl⟩
    exact ⟨φ.1 z, ⟨z, hzE, rfl⟩, rfl⟩

theorem mem_moebiusTranslate_fundamentalSetQ_iff {φ : ModularMoebiusGroup} {w : ℂ} :
    w ∈ moebiusTranslate φ FundamentalSetQ ↔
      ∃ (z : ℂ) (hz : z ∈ FundamentalSetQ),
        (φ.1 ⟨z, fundamentalSetQ_subset_upperHalfPlaneSet hz⟩).1 = w := by
  rw [mem_moebiusTranslate_iff]
  constructor
  · rintro ⟨⟨z, _⟩, hzQ, hw⟩
    exact ⟨z, hzQ, hw⟩
  · rintro ⟨z, hzQ, hw⟩
    exact ⟨⟨z, fundamentalSetQ_subset_upperHalfPlaneSet hzQ⟩, hzQ, hw⟩

theorem moebiusTranslate_subset_upperHalfPlaneSet (φ : ModularMoebiusGroup) (E : Set ℂ) :
    moebiusTranslate φ E ⊆ UpperHalfPlaneSet := by
  rintro w ⟨u, _, rfl⟩
  exact u.2

/-- Key half of Step 1 of Theorem 16.19 under `z.im ≤ (φ z).im`. -/
private theorem parityMoebius_eq_one_of_im_le
    {φ : ModularMoebiusGroup} (hφ : φ ∈ ParityMoebiusSubgroup)
    {z : ℂ} (hz : z ∈ FundamentalSetQ)
    (hw : (φ.1 ⟨z, fundamentalSetQ_subset_upperHalfPlaneSet hz⟩).1 ∈ FundamentalSetQ)
    (him : z.im ≤ ((φ.1 ⟨z, fundamentalSetQ_subset_upperHalfPlaneSet hz⟩).1).im) :
    φ = 1 := by
  rcases hφ with ⟨a, b, c, d, hdet, _ha, hd, hb, hc, hφ_eq⟩
  let z_sub : UpperHalfPlaneSet := ⟨z, fundamentalSetQ_subset_upperHalfPlaneSet hz⟩
  let w : ℂ := (φ.1 z_sub).1
  have hw_eq : w = intMoebius a b c d z := by
    change (φ.1 z_sub).1 = _
    rw [hφ_eq]
    rfl
  have hy : 0 < z.im := hz.1
  have hx_lo : -1 ≤ z.re := hz.2.1
  have hx_hi : z.re < 1 := hz.2.2.1
  have hq_plus : -z.re ≤ z.re ^ 2 + z.im ^ 2 :=
    (one_le_norm_two_mul_add_one_iff z).mp hz.2.2.2.1
  have hq_minus : z.re < z.re ^ 2 + z.im ^ 2 :=
    (one_lt_norm_two_mul_sub_one_iff z).mp hz.2.2.2.2
  have hw_re_lo : -1 ≤ w.re := hw.2.1
  have hw_re_hi : w.re < 1 := hw.2.2.1
  have hw_minus : 1 < ‖2 * w - 1‖ := hw.2.2.2.2
  have hden_ne : (c : ℂ) * z + (d : ℂ) ≠ 0 := intMoebius_denom_ne_zero hdet hz.1
  have hden_sq_pos : 0 < ‖(c : ℂ) * z + (d : ℂ)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hden_ne)
  have him_eq : w.im = z.im / ‖(c : ℂ) * z + (d : ℂ)‖ ^ 2 := by
    rw [hw_eq, intMoebius_im hdet]
  have hden_sq_le_one : ‖(c : ℂ) * z + (d : ℂ)‖ ^ 2 ≤ 1 := by
    have hmul : z.im * ‖(c : ℂ) * z + (d : ℂ)‖ ^ 2 ≤ z.im := by
      have : z.im ≤ z.im / ‖(c : ℂ) * z + (d : ℂ)‖ ^ 2 := him_eq ▸ him
      exact (le_div_iff₀ hden_sq_pos).mp this
    nlinarith
  by_cases hc0 : c = 0
  · subst hc0
    have had : a * d = 1 := by linarith
    rcases hb with ⟨k, rfl⟩
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp had with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hw_val : w = z + ((k + k : ℤ) : ℂ) := by
        rw [hw_eq]
        simp [intMoebius]
      have hw_re : w.re = z.re + 2 * (k : ℝ) := by
        rw [hw_val]
        simp only [Complex.add_re, Complex.intCast_re]
        push_cast
        ring
      have hk_lo_r : (-1 : ℝ) < (k : ℝ) := by linarith
      have hk_hi_r : (k : ℝ) < (1 : ℝ) := by linarith
      have hk_lo : (-1 : ℤ) < k := by exact_mod_cast hk_lo_r
      have hk_hi : k < (1 : ℤ) := by exact_mod_cast hk_hi_r
      have hk0 : k = 0 := by omega
      subst hk0
      ext u
      change (φ.1 u).1 = u.1
      rw [hφ_eq]
      simp
    · have hw_val : w = z - ((k + k : ℤ) : ℂ) := by
        rw [hw_eq]
        unfold intMoebius
        push_cast
        ring
      have hw_re : w.re = z.re - 2 * (k : ℝ) := by
        rw [hw_val]
        simp only [Complex.sub_re, Complex.intCast_re]
        push_cast
        ring
      have hk_lo_r : (-1 : ℝ) < (k : ℝ) := by linarith
      have hk_hi_r : (k : ℝ) < (1 : ℝ) := by linarith
      have hk_lo : (-1 : ℤ) < k := by exact_mod_cast hk_lo_r
      have hk_hi : k < (1 : ℤ) := by exact_mod_cast hk_hi_r
      have hk0 : k = 0 := by omega
      subst hk0
      ext u
      change (φ.1 u).1 = u.1
      rw [hφ_eq]
      simp [intMoebius, neg_div_neg_eq]
  · -- Case `c ≠ 0`: derive a contradiction!
    exfalso
    have hc_even_2 : ∃ kc : ℤ, c = 2 * kc := by
      rcases hc with ⟨kc, rfl⟩
      exact ⟨kc, by ring⟩
    rcases hc_even_2 with ⟨kc, hkc_eq⟩
    have hkc_ne : kc ≠ 0 := by omega
    have hkc_sq : 1 ≤ kc ^ 2 := int_one_le_sq_of_ne_zero hkc_ne
    have hc_sq_int : 4 ≤ c ^ 2 := by
      rw [hkc_eq]
      nlinarith
    rcases hd with ⟨kd, hkd_eq⟩
    have hd_ne : d ≠ 0 := by omega
    have hd_sq_int : 1 ≤ d ^ 2 := int_one_le_sq_of_ne_zero hd_ne
    have hcd_abs_ne : |c| - |d| ≠ 0 := by
      intro habs0
      have habs_eq : |c| = |d| := sub_eq_zero.mp habs0
      have hsq_eq : c ^ 2 = d ^ 2 := by
        rw [← sq_abs c, ← sq_abs d, habs_eq]
      have hc2_mod : c ^ 2 = 4 * kc ^ 2 := by rw [hkc_eq]; ring
      have hd2_mod : d ^ 2 = 4 * (kd ^ 2 + kd) + 1 := by rw [hkd_eq]; ring
      omega
    have hcd_diff_sq_int : 1 ≤ (|c| - |d|) ^ 2 := int_one_le_sq_of_ne_zero hcd_abs_ne
    let C : ℝ := |(c : ℝ)|
    let D : ℝ := |(d : ℝ)|
    have hC_nonneg : 0 ≤ C := abs_nonneg _
    have hD_nonneg : 0 ≤ D := abs_nonneg _
    have hC_sq_eq : C ^ 2 = (c : ℝ) ^ 2 := sq_abs _
    have hD_sq_eq : D ^ 2 = (d : ℝ) ^ 2 := sq_abs _
    have hC_sq : 4 ≤ C ^ 2 := by
      rw [hC_sq_eq]
      exact_mod_cast hc_sq_int
    have hC_ge : 2 ≤ C := by nlinarith
    have hD_sq : 1 ≤ D ^ 2 := by
      rw [hD_sq_eq]
      exact_mod_cast hd_sq_int
    have hD_ge : 1 ≤ D := by nlinarith
    have hCD_sq : 1 ≤ (C - D) ^ 2 := by
      have hcast : C - D = ((|c| - |d| : ℤ) : ℝ) := by
        dsimp [C, D]
        push_cast
        rfl
      rw [hcast]
      exact_mod_cast hcd_diff_sq_int
    have hden_expand :
        ‖(c : ℂ) * z + (d : ℂ)‖ ^ 2 =
          C ^ 2 * (z.re ^ 2 + z.im ^ 2) + 2 * ((c : ℝ) * (d : ℝ) * z.re) + D ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hC_sq_eq, hD_sq_eq]
      simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
        Complex.add_im, Complex.mul_im]
      ring
    have hcd_le :
        C ^ 2 * (z.re ^ 2 + z.im ^ 2) + 2 * ((c : ℝ) * (d : ℝ) * z.re) + D ^ 2 ≤ 1 := by
      linarith
    -- First exclude `0 ≤ z.re`:
    have hx_neg : z.re < 0 := by
      by_contra hx_nn_neg
      have hx_nn : 0 ≤ z.re := not_lt.mp hx_nn_neg
      have habs_cdx : -(C * D * z.re) ≤ (c : ℝ) * (d : ℝ) * z.re := by
        have h1 := neg_abs_le ((c : ℝ) * (d : ℝ) * z.re)
        simpa [C, D, abs_mul, abs_of_nonneg hx_nn] using h1
      have hconv :
          C ^ 2 * z.re - 2 * (C * D * z.re) + D ^ 2 =
            (1 - z.re) * D ^ 2 + z.re * (C - D) ^ 2 := by
        ring
      have h1mx_nn : 0 ≤ 1 - z.re := by linarith only [hx_hi]
      have ht1 : 1 - z.re ≤ (1 - z.re) * D ^ 2 := le_mul_of_one_le_right h1mx_nn hD_sq
      have ht2 : z.re ≤ z.re * (C - D) ^ 2 := le_mul_of_one_le_right hx_nn hCD_sq
      have hct : C ^ 2 * z.re < C ^ 2 * (z.re ^ 2 + z.im ^ 2) := by
        nlinarith only [hC_sq, hq_minus]
      linarith only [ht1, ht2, hconv, hct, habs_cdx, hcd_le]
    -- Now `z.re < 0`, so let `t = -z.re > 0`:
    let t : ℝ := -z.re
    have ht_pos : 0 < t := by dsimp [t]; linarith only [hx_neg]
    have ht_le : t ≤ 1 := by dsimp [t]; linarith only [hx_lo]
    have habs_cdx : -(C * D * t) ≤ (c : ℝ) * (d : ℝ) * z.re := by
      have h1 := neg_abs_le ((c : ℝ) * (d : ℝ) * z.re)
      have habs_x : |z.re| = t := abs_of_neg hx_neg
      simpa [C, D, abs_mul, habs_x] using h1
    have hconv :
        C ^ 2 * t - 2 * (C * D * t) + D ^ 2 =
          (1 - t) * D ^ 2 + t * (C - D) ^ 2 := by
      ring
    have hqt : t ≤ z.re ^ 2 + z.im ^ 2 := hq_plus
    have ht_lt_one : t < 1 := by
      by_contra ht_ge1
      have ht_eq1 : t = 1 := by linarith only [ht_le, ht_ge1]
      have hxz : z.re = -1 := by dsimp [t] at ht_eq1; linarith only [ht_eq1]
      have hy2 : 0 < z.im ^ 2 := sq_pos_of_pos hy
      have hstrict : t < z.re ^ 2 + z.im ^ 2 := by
        rw [ht_eq1, hxz]
        linarith only [hy2]
      have hct : C ^ 2 * t < C ^ 2 * (z.re ^ 2 + z.im ^ 2) := by
        nlinarith only [hC_sq, hstrict]
      have hconv1 : C ^ 2 * t - 2 * (C * D * t) + D ^ 2 = (C - D) ^ 2 := by
        rw [hconv, ht_eq1]; ring
      linarith only [hconv1, hCD_sq, hct, habs_cdx, hcd_le]
    have h1mt_pos : 0 < 1 - t := by linarith only [ht_lt_one]
    have ht1 : 1 - t ≤ (1 - t) * D ^ 2 := le_mul_of_one_le_right h1mt_pos.le hD_sq
    have ht2 : t ≤ t * (C - D) ^ 2 := le_mul_of_one_le_right ht_pos.le hCD_sq
    have hct : C ^ 2 * t ≤ C ^ 2 * (z.re ^ 2 + z.im ^ 2) :=
      mul_le_mul_of_nonneg_left hqt (by linarith only [hC_sq])
    have hct_eq : C ^ 2 * t = C ^ 2 * (z.re ^ 2 + z.im ^ 2) := by
      linarith only [ht1, ht2, hconv, hct, habs_cdx, hcd_le]
    have hnorm_tight : z.re ^ 2 + z.im ^ 2 = -z.re := by
      change z.re ^ 2 + z.im ^ 2 = t
      nlinarith only [hct_eq, hC_sq]
    have ht1_eq : (1 - t) * D ^ 2 = 1 - t := by
      linarith only [ht1, ht2, hconv, hct, habs_cdx, hcd_le]
    have hD_sq_eq_one : D ^ 2 = 1 := by
      nlinarith only [ht1_eq, h1mt_pos]
    have ht2_eq : t * (C - D) ^ 2 = t := by
      linarith only [ht1, ht2, hconv, hct, habs_cdx, hcd_le]
    have hCD_sq_eq_one : (C - D) ^ 2 = 1 := by
      nlinarith only [ht2_eq, ht_pos]
    have hD_one : D = 1 := by
      nlinarith only [hD_sq_eq_one, hD_ge]
    have hC_two : C = 2 := by
      nlinarith only [hCD_sq_eq_one, hD_one, hC_ge]
    have hcdx_tight : (c : ℝ) * (d : ℝ) * z.re = -(C * D * t) := by
      linarith only [ht1, ht2, hconv, hct, habs_cdx, hcd_le]
    have hcd_real : (c : ℝ) * (d : ℝ) = 2 := by
      rw [hC_two, hD_one] at hcdx_tight
      dsimp [t] at hcdx_tight
      nlinarith only [hcdx_tight, hx_neg]
    have hcd_int : c * d = 2 := by exact_mod_cast hcd_real
    have hd_sq_one_int : d * d = 1 := by
      have : (d : ℝ) ^ 2 = 1 := by rw [← hD_sq_eq, hD_sq_eq_one]
      have : d ^ 2 = 1 := by exact_mod_cast this
      simpa [sq] using this
    -- Reduce `(a, b, c, d)` to `(a', b', 2, 1)` with `a' = 2 * b' + 1` and `Even b'`:
    have hex_rep : ∃ b' : ℤ, Even b' ∧ w = intMoebius (2 * b' + 1) b' 2 1 z := by
      rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hd_sq_one_int with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · have hc2 : c = 2 := by linarith
        subst hc2
        have ha_eq : a = 2 * b + 1 := by linarith
        subst ha_eq
        exact ⟨b, hb, hw_eq⟩
      · have hc2 : c = -2 := by linarith
        subst hc2
        have ha_eq : -a = 2 * (-b) + 1 := by linarith
        refine ⟨-b, even_neg_int hb, ?_⟩
        rw [hw_eq, ← intMoebius_neg a b (-2) (-1) z, ha_eq]
        simp
    rcases hex_rep with ⟨b', hb', hw_rep⟩
    have h2z1_norm : ‖2 * z + 1‖ = 1 :=
      (norm_two_mul_add_one_eq_one_iff z).mpr hnorm_tight
    have h2z1_ne : 2 * z + 1 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h2z1_norm
      norm_num at h2z1_norm
    let u : ℂ := z / (2 * z + 1)
    have hw_u : w = (b' : ℂ) + u := by
      rw [hw_rep]
      dsimp [u]
      unfold intMoebius
      push_cast
      field_simp [h2z1_ne]
      ring
    by_cases hb'0 : b' = 0
    · subst hb'0
      have hwu : w = u := by simpa using hw_u
      have h2u_sub : 2 * u - 1 = -1 / (2 * z + 1) := by
        dsimp [u]
        field_simp [h2z1_ne]
        ring
      have hnorm_w : ‖2 * w - 1‖ = 1 := by
        rw [hwu, h2u_sub, norm_div, norm_neg, norm_one, h2z1_norm, div_one]
      linarith
    · rcases hb' with ⟨kb, rfl⟩
      have hkb_ne : kb ≠ 0 := by omega
      have h2z1_normSq : Complex.normSq (2 * z + 1) = 1 := by
        rw [Complex.normSq_eq_norm_sq, h2z1_norm, one_pow]
      have hu_re : u.re = -z.re := by
        dsimp [u]
        rw [Complex.div_re, h2z1_normSq]
        simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
          Complex.one_re, Complex.add_im, Complex.mul_im, Complex.one_im]
        linarith
      have hu_re_pos : 0 < u.re := by rw [hu_re]; linarith
      have hu_re_lt_one : u.re < 1 := by rw [hu_re]; exact ht_lt_one
      have hw_re_u : w.re = 2 * (kb : ℝ) + u.re := by
        rw [hw_u]
        simp only [Complex.add_re, Complex.intCast_re]
        push_cast
        ring
      rcases lt_trichotomy kb 0 with hkb_neg | rfl | hkb_pos
      · have hkb_le : (kb : ℝ) ≤ -1 := by
          have : kb ≤ -1 := by omega
          exact_mod_cast this
        linarith
      · exact hkb_ne rfl
      · have hkb_ge : (1 : ℝ) ≤ (kb : ℝ) := by
          have : 1 ≤ kb := by omega
          exact_mod_cast this
        linarith

/-- **16.19, Step 1 (Disjointness on `ParityMoebiusSubgroup`, RCA p. 329):**
If `φ ∈ ParityMoebiusSubgroup`, `z ∈ FundamentalSetQ`, and `φ(z) ∈ FundamentalSetQ`, then `φ = 1`. -/
theorem parityMoebius_eq_one_of_mem_fundamentalSetQ
    {φ : ModularMoebiusGroup} (hφ : φ ∈ ParityMoebiusSubgroup)
    {z : ℂ} (hz : z ∈ FundamentalSetQ)
    (hw : (φ.1 ⟨z, fundamentalSetQ_subset_upperHalfPlaneSet hz⟩).1 ∈ FundamentalSetQ) :
    φ = 1 := by
  let z_sub : UpperHalfPlaneSet := ⟨z, fundamentalSetQ_subset_upperHalfPlaneSet hz⟩
  let w_sub : UpperHalfPlaneSet := φ.1 z_sub
  by_cases him : z.im ≤ w_sub.1.im
  · exact parityMoebius_eq_one_of_im_le hφ hz hw him
  · have him' : w_sub.1.im ≤ z.im := le_of_not_ge him
    have hinv_mem : φ⁻¹ ∈ ParityMoebiusSubgroup := ParityMoebiusSubgroup.inv_mem hφ
    have hw_sub_eq : (⟨w_sub.1, fundamentalSetQ_subset_upperHalfPlaneSet hw⟩ : UpperHalfPlaneSet) =
        w_sub := rfl
    have hinv_w : (φ⁻¹.1 ⟨w_sub.1, fundamentalSetQ_subset_upperHalfPlaneSet hw⟩).1 = z := by
      rw [hw_sub_eq]
      change ((φ⁻¹ * φ).1 z_sub).1 = z
      rw [inv_mul_cancel]
      rfl
    have hinv_in_Q :
        (φ⁻¹.1 ⟨w_sub.1, fundamentalSetQ_subset_upperHalfPlaneSet hw⟩).1 ∈ FundamentalSetQ := by
      rw [hinv_w]
      exact hz
    have him_inv :
        w_sub.1.im ≤ ((φ⁻¹.1 ⟨w_sub.1, fundamentalSetQ_subset_upperHalfPlaneSet hw⟩).1).im := by
      rw [hinv_w]
      exact him'
    have hφ_inv_one : φ⁻¹ = 1 :=
      parityMoebius_eq_one_of_im_le hinv_mem hw hinv_in_Q him_inv
    exact inv_eq_one.mp hφ_inv_one

/-- Distinct elements of `ParityMoebiusSubgroup` map `FundamentalSetQ` to disjoint subsets of `Π⁺`. -/
theorem disjoint_moebiusTranslate_fundamentalSetQ_of_parity
    {φ₁ φ₂ : ModularMoebiusGroup}
    (hφ₁ : φ₁ ∈ ParityMoebiusSubgroup) (hφ₂ : φ₂ ∈ ParityMoebiusSubgroup) (hne : φ₁ ≠ φ₂) :
    Disjoint (moebiusTranslate φ₁ FundamentalSetQ) (moebiusTranslate φ₂ FundamentalSetQ) := by
  rw [Set.disjoint_left]
  intro w hw₁ hw₂
  rcases mem_moebiusTranslate_fundamentalSetQ_iff.mp hw₁ with ⟨z₁, hz₁, heq₁⟩
  rcases mem_moebiusTranslate_fundamentalSetQ_iff.mp hw₂ with ⟨z₂, hz₂, heq₂⟩
  let u₁ : UpperHalfPlaneSet := ⟨z₁, fundamentalSetQ_subset_upperHalfPlaneSet hz₁⟩
  let u₂ : UpperHalfPlaneSet := ⟨z₂, fundamentalSetQ_subset_upperHalfPlaneSet hz₂⟩
  have hφ_eq : φ₁.1 u₁ = φ₂.1 u₂ := Subtype.ext (heq₁.trans heq₂.symm)
  have hu₂_eq : (φ₂⁻¹ * φ₁).1 u₁ = u₂ := by
    apply (φ₂.1).injective
    change ((φ₂ * (φ₂⁻¹ * φ₁)).1 u₁) = φ₂.1 u₂
    rw [mul_inv_cancel_left]
    exact hφ_eq
  have hmem₂ : ((φ₂⁻¹ * φ₁).1 u₁).1 ∈ FundamentalSetQ := by
    rw [hu₂_eq]
    exact hz₂
  have hprod_mem : φ₂⁻¹ * φ₁ ∈ ParityMoebiusSubgroup :=
    ParityMoebiusSubgroup.mul_mem (ParityMoebiusSubgroup.inv_mem hφ₂) hφ₁
  have hprod_one : φ₂⁻¹ * φ₁ = 1 :=
    parityMoebius_eq_one_of_mem_fundamentalSetQ hprod_mem hz₁ hmem₂
  exact hne (inv_mul_eq_one.mp hprod_one).symm

/-- **16.19 (Part 1: Distinct `Γ`-translates of `Q` are disjoint, RCA p. 329):** -/
theorem disjoint_moebiusTranslate_fundamentalSetQ
    {γ₁ γ₂ : ModularMoebiusGroup}
    (hγ₁ : γ₁ ∈ GammaSubgroup) (hγ₂ : γ₂ ∈ GammaSubgroup) (hne : γ₁ ≠ γ₂) :
    Disjoint (moebiusTranslate γ₁ FundamentalSetQ) (moebiusTranslate γ₂ FundamentalSetQ) :=
  disjoint_moebiusTranslate_fundamentalSetQ_of_parity
    (gammaSubgroup_le_parityMoebiusSubgroup hγ₁)
    (gammaSubgroup_le_parityMoebiusSubgroup hγ₂) hne

/-- Finiteness of integer pairs `(c, d)` with `‖c z₀ + d‖² ≤ 1` for `z₀ ∈ Π⁺`. -/
private theorem finite_int_pairs_norm_sq_le_one (z₀ : UpperHalfPlaneSet) :
    ({p : ℤ × ℤ | ‖(p.1 : ℂ) * z₀.1 + (p.2 : ℂ)‖ ^ 2 ≤ 1}).Finite := by
  have hy₀ : 0 < z₀.1.im := z₀.2
  let C_bound : ℤ := ⌈1 / z₀.1.im⌉
  let D_bound : ℤ := ⌈1 + (C_bound : ℝ) * |z₀.1.re|⌉
  let box : Finset (ℤ × ℤ) :=
    Finset.Icc (-C_bound) C_bound ×ˢ Finset.Icc (-D_bound) D_bound
  refine box.finite_toSet.subset ?_
  rintro ⟨c, d⟩ hp
  change ‖(c : ℂ) * z₀.1 + (d : ℂ)‖ ^ 2 ≤ 1 at hp
  have hexp :
      ((c : ℝ) * z₀.1.re + (d : ℝ)) ^ 2 + ((c : ℝ) * z₀.1.im) ^ 2 ≤ 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hp
    simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      Complex.add_im, Complex.mul_im] at hp
    nlinarith only [hp]
  have hcy_sq : ((c : ℝ) * z₀.1.im) ^ 2 ≤ 1 := by nlinarith
  have hcy_abs : |(c : ℝ) * z₀.1.im| ≤ 1 := by
    have hnn : 0 ≤ |(c : ℝ) * z₀.1.im| := abs_nonneg _
    have hsq : |(c : ℝ) * z₀.1.im| ^ 2 ≤ 1 := by rwa [sq_abs]
    nlinarith
  rw [abs_mul, abs_of_pos hy₀] at hcy_abs
  have hc_abs : |(c : ℝ)| ≤ 1 / z₀.1.im := (le_div_iff₀ hy₀).mpr hcy_abs
  have hc_ceil : |(c : ℝ)| ≤ (C_bound : ℝ) := hc_abs.trans (Int.le_ceil _)
  have hc_lo_r : ((-C_bound : ℤ) : ℝ) ≤ (c : ℝ) := by
    push_cast
    linarith [(abs_le.mp hc_ceil).1]
  have hc_hi_r : (c : ℝ) ≤ (C_bound : ℝ) := (abs_le.mp hc_ceil).2
  have hc_lo : -C_bound ≤ c := Int.cast_le.mp hc_lo_r
  have hc_hi : c ≤ C_bound := Int.cast_le.mp hc_hi_r
  have hcd_sq : ((c : ℝ) * z₀.1.re + (d : ℝ)) ^ 2 ≤ 1 := by nlinarith
  have hcd_abs : |(c : ℝ) * z₀.1.re + (d : ℝ)| ≤ 1 := by
    have hnn : 0 ≤ |(c : ℝ) * z₀.1.re + (d : ℝ)| := abs_nonneg _
    have hsq : |(c : ℝ) * z₀.1.re + (d : ℝ)| ^ 2 ≤ 1 := by rwa [sq_abs]
    nlinarith
  have hd_abs : |(d : ℝ)| ≤ 1 + (C_bound : ℝ) * |z₀.1.re| := by
    have htri : |(d : ℝ)| ≤ |(c : ℝ) * z₀.1.re + (d : ℝ)| + |-(c : ℝ) * z₀.1.re| := by
      have heq : (d : ℝ) = ((c : ℝ) * z₀.1.re + (d : ℝ)) + (-(c : ℝ) * z₀.1.re) := by ring
      conv_lhs => rw [heq]
      exact abs_add_le _ _
    rw [neg_mul, abs_neg, abs_mul] at htri
    have hmul_le : |(c : ℝ)| * |z₀.1.re| ≤ (C_bound : ℝ) * |z₀.1.re| :=
      mul_le_mul_of_nonneg_right hc_ceil (abs_nonneg _)
    linarith
  have hd_ceil : |(d : ℝ)| ≤ (D_bound : ℝ) := hd_abs.trans (Int.le_ceil _)
  have hd_lo_r : ((-D_bound : ℤ) : ℝ) ≤ (d : ℝ) := by
    push_cast
    linarith [(abs_le.mp hd_ceil).1]
  have hd_hi_r : (d : ℝ) ≤ (D_bound : ℝ) := (abs_le.mp hd_ceil).2
  have hd_lo : -D_bound ≤ d := Int.cast_le.mp hd_lo_r
  have hd_hi : d ≤ D_bound := Int.cast_le.mp hd_hi_r
  simp only [Finset.mem_coe, box, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨hc_lo, hc_hi⟩, ⟨hd_lo, hd_hi⟩⟩

/-- Existence of an element in `GammaSubgroup` maximizing `Im(α(z₀))` on the `Γ`-orbit of `z₀`. -/
private theorem exists_gamma_max_im (z₀ : UpperHalfPlaneSet) :
    ∃ α₁ ∈ GammaSubgroup, ∀ α ∈ GammaSubgroup, ((α.1 z₀).1).im ≤ ((α₁.1 z₀).1).im := by
  have hy₀ : 0 < z₀.1.im := z₀.2
  let S : Set (ℤ × ℤ) := {p : ℤ × ℤ | ‖(p.1 : ℂ) * z₀.1 + (p.2 : ℂ)‖ ^ 2 ≤ 1}
  have hS_fin : S.Finite := finite_int_pairs_norm_sq_le_one z₀
  let V : Set ℝ := {v : ℝ | ∃ α ∈ GammaSubgroup, ((α.1 z₀).1).im = v ∧ z₀.1.im ≤ v}
  have hV_sub : V ⊆ (fun p : ℤ × ℤ => z₀.1.im / ‖(p.1 : ℂ) * z₀.1 + (p.2 : ℂ)‖ ^ 2) '' S := by
    rintro v ⟨α, _hα, rfl, hv_ge⟩
    rcases α.2 with ⟨a, b, c, d, hdet, hα_eq⟩
    have him_eq : ((α.1 z₀).1).im = z₀.1.im / ‖(c : ℂ) * z₀.1 + (d : ℂ)‖ ^ 2 := by
      rw [hα_eq]
      exact intMoebius_im hdet z₀.1
    have hden_pos : 0 < ‖(c : ℂ) * z₀.1 + (d : ℂ)‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (intMoebius_denom_ne_zero hdet z₀.2))
    have hle1 : ‖(c : ℂ) * z₀.1 + (d : ℂ)‖ ^ 2 ≤ 1 := by
      rw [him_eq] at hv_ge
      have hmul := (le_div_iff₀ hden_pos).mp hv_ge
      nlinarith
    exact ⟨(c, d), hle1, him_eq.symm⟩
  have hV_fin : V.Finite := (hS_fin.image _).subset hV_sub
  have hV_ne : V.Nonempty := ⟨z₀.1.im, 1, GammaSubgroup.one_mem, rfl, le_rfl⟩
  let vmax : ℝ := hV_fin.toFinset.max' (hV_fin.toFinset_nonempty.mpr hV_ne)
  have hvmax_mem : vmax ∈ V := hV_fin.mem_toFinset.mp (Finset.max'_mem _ _)
  rcases hvmax_mem with ⟨α₁, hα₁, hα₁_eq, hα₁_ge⟩
  refine ⟨α₁, hα₁, fun α hα => ?_⟩
  rw [hα₁_eq]
  by_cases hge : z₀.1.im ≤ ((α.1 z₀).1).im
  · have hmem : ((α.1 z₀).1).im ∈ V := ⟨α, hα, rfl, hge⟩
    exact Finset.le_max' _ _ (hV_fin.mem_toFinset.mpr hmem)
  · linarith

/-- Every `Γ`-orbit in `Π⁺` meets `FundamentalSetQ`. -/
theorem exists_gamma_apply_mem_fundamentalSetQ (z₀ : UpperHalfPlaneSet) :
    ∃ α ∈ GammaSubgroup, (α.1 z₀).1 ∈ FundamentalSetQ := by
  obtain ⟨α₁, hα₁, hmax₁⟩ := exists_gamma_max_im z₀
  let w₁ : UpperHalfPlaneSet := α₁.1 z₀
  let k : ℤ := -⌊(w₁.1.re + 1) / 2⌋
  let α₂ : ModularMoebiusGroup := modularTau ^ k * α₁
  have hα₂ : α₂ ∈ GammaSubgroup :=
    GammaSubgroup.mul_mem (GammaSubgroup.zpow_mem modularTau_mem_gamma k) hα₁
  let w₂ : UpperHalfPlaneSet := α₂.1 z₀
  have hw₂_val : w₂.1 = w₁.1 + 2 * (k : ℂ) := by
    change ((modularTau ^ k * α₁).1 z₀).1 = _
    rw [ModularMoebiusGroup.mul_apply, modularTau_zpow_apply]
  have hw₂_im : w₂.1.im = w₁.1.im := by
    rw [hw₂_val]
    simp [Complex.add_im, Complex.mul_im]
  have hw₂_re : w₂.1.re = w₁.1.re + 2 * (k : ℝ) := by
    rw [hw₂_val]
    simp [Complex.add_re, Complex.mul_re]
  have hfl_le : ((⌊(w₁.1.re + 1) / 2⌋ : ℤ) : ℝ) ≤ (w₁.1.re + 1) / 2 :=
    Int.floor_le _
  have hlt_fl : (w₁.1.re + 1) / 2 < ((⌊(w₁.1.re + 1) / 2⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hk_cast : (k : ℝ) = -((⌊(w₁.1.re + 1) / 2⌋ : ℤ) : ℝ) := by
    dsimp [k]
    push_cast
    rfl
  have hw₂_re_lo : -1 ≤ w₂.1.re := by linarith
  have hw₂_re_hi : w₂.1.re < 1 := by linarith
  have hmax₂ : ∀ β ∈ GammaSubgroup, ((β.1 w₂).1).im ≤ w₂.1.im := by
    intro β hβ
    have hβα₂ : β * α₂ ∈ GammaSubgroup := GammaSubgroup.mul_mem hβ hα₂
    calc
      ((β.1 w₂).1).im = (((β * α₂).1 z₀).1).im := rfl
      _ ≤ w₁.1.im := hmax₁ (β * α₂) hβα₂
      _ = w₂.1.im := hw₂_im.symm
  have hy₂ : 0 < w₂.1.im := w₂.2
  -- Maximality under `modularSigma` gives `1 ≤ ‖2 * w₂ + 1‖`:
  have hw₂_plus : 1 ≤ ‖2 * w₂.1 + 1‖ := by
    have hσ_im := hmax₂ modularSigma modularSigma_mem_gamma
    have him_σ : ((modularSigma.1 w₂).1).im = w₂.1.im / ‖(2 : ℂ) * w₂.1 + (1 : ℂ)‖ ^ 2 := by
      rw [modularSigma, sl2zToMoebius_apply]
      simpa [sigmaMatrix] using intMoebius_im (a := 1) (b := 0) (c := 2) (d := 1) (by norm_num) w₂.1
    rw [him_σ] at hσ_im
    have hden_ne : (2 : ℂ) * w₂.1 + 1 ≠ 0 := by
      simpa using intMoebius_denom_ne_zero (a := 1) (b := 0) (c := 2) (d := 1) (by norm_num) w₂.2
    have hsq_pos : 0 < ‖(2 : ℂ) * w₂.1 + 1‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hden_ne)
    have hmul : w₂.1.im ≤ w₂.1.im * ‖(2 : ℂ) * w₂.1 + 1‖ ^ 2 :=
      (div_le_iff₀ hsq_pos).mp hσ_im
    have hsq_ge : 1 ≤ ‖2 * w₂.1 + 1‖ ^ 2 := by nlinarith
    have hnn : 0 ≤ ‖2 * w₂.1 + 1‖ := norm_nonneg _
    nlinarith
  -- Maximality under `modularSigma⁻¹` gives `1 ≤ ‖2 * w₂ - 1‖`:
  have hw₂_minus_ge : 1 ≤ ‖2 * w₂.1 - 1‖ := by
    have hσi_mem : modularSigma⁻¹ ∈ GammaSubgroup :=
      GammaSubgroup.inv_mem modularSigma_mem_gamma
    have hσi_im := hmax₂ modularSigma⁻¹ hσi_mem
    have hσi_eq : modularSigma⁻¹ = sl2zToMoebius sigmaInvMatrix := by
      rw [modularSigma, ← map_inv, sigmaMatrix_inv]
    have him_σi : ((modularSigma⁻¹.1 w₂).1).im =
        w₂.1.im / ‖((-2 : ℤ) : ℂ) * w₂.1 + (1 : ℂ)‖ ^ 2 := by
      rw [hσi_eq, sl2zToMoebius_apply]
      simpa [sigmaInvMatrix] using
        intMoebius_im (a := 1) (b := 0) (c := -2) (d := 1) (by norm_num) w₂.1
    rw [him_σi] at hσi_im
    have hnorm_eq : ‖((-2 : ℤ) : ℂ) * w₂.1 + (1 : ℂ)‖ = ‖2 * w₂.1 - 1‖ := by
      have : ((-2 : ℤ) : ℂ) * w₂.1 + (1 : ℂ) = -(2 * w₂.1 - 1) := by push_cast; ring
      rw [this, norm_neg]
    rw [hnorm_eq] at hσi_im
    have hden_ne : 2 * w₂.1 - 1 ≠ 0 := by
      intro h0
      have hne' : ((-2 : ℤ) : ℂ) * w₂.1 + ((1 : ℤ) : ℂ) ≠ 0 :=
        intMoebius_denom_ne_zero (a := 1) (b := 0) (c := -2) (d := 1) (by norm_num) w₂.2
      apply hne'
      push_cast
      linear_combination -h0
    have hsq_pos : 0 < ‖2 * w₂.1 - 1‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hden_ne)
    have hmul : w₂.1.im ≤ w₂.1.im * ‖2 * w₂.1 - 1‖ ^ 2 :=
      (div_le_iff₀ hsq_pos).mp hσi_im
    have hsq_ge : 1 ≤ ‖2 * w₂.1 - 1‖ ^ 2 := by nlinarith
    have hnn : 0 ≤ ‖2 * w₂.1 - 1‖ := norm_nonneg _
    nlinarith
  rcases eq_or_lt_of_le hw₂_minus_ge with hw₂_minus_eq | hw₂_minus_gt
  · -- Boundary case `‖2 * w₂ - 1‖ = 1`: apply `modularSigma⁻¹`!
    let α₃ : ModularMoebiusGroup := modularSigma⁻¹ * α₂
    have hα₃ : α₃ ∈ GammaSubgroup :=
      GammaSubgroup.mul_mem (GammaSubgroup.inv_mem modularSigma_mem_gamma) hα₂
    let w₃ : UpperHalfPlaneSet := α₃.1 z₀
    have hw₃_val : w₃.1 = w₂.1 / (-2 * w₂.1 + 1) := by
      change ((modularSigma⁻¹ * α₂).1 z₀).1 = _
      rw [ModularMoebiusGroup.mul_apply, modularSigma_inv_apply]
    have hnorm_m2 : ‖-2 * w₂.1 + 1‖ = 1 := by
      have : -2 * w₂.1 + 1 = -(2 * w₂.1 - 1) := by ring
      rw [this, norm_neg, hw₂_minus_eq.symm]
    have hden_m2_ne : -2 * w₂.1 + 1 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hnorm_m2
      norm_num at hnorm_m2
    have hnormSq_m2 : Complex.normSq (-2 * w₂.1 + 1) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hnorm_m2, one_pow]
    have hcirc₂ : w₂.1.re ^ 2 + w₂.1.im ^ 2 = w₂.1.re :=
      (norm_two_mul_sub_one_eq_one_iff w₂.1).mp hw₂_minus_eq.symm
    have hx₂_pos : 0 < w₂.1.re := by
      have hy₂_sq : 0 < w₂.1.im ^ 2 := sq_pos_of_pos hy₂
      nlinarith
    have hw₃_re : w₃.1.re = -w₂.1.re := by
      rw [hw₃_val, Complex.div_re, hnormSq_m2]
      simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.re_ofNat,
        Complex.im_ofNat, Complex.neg_im, Complex.one_re, Complex.add_im, Complex.mul_im,
        Complex.one_im]
      linarith
    have hw₃_re_neg : w₃.1.re < 0 := by rw [hw₃_re]; linarith
    have hw₃_re_lo : -1 ≤ w₃.1.re := by rw [hw₃_re]; linarith
    have hw₃_re_hi : w₃.1.re < 1 := by linarith
    have hw₃_plus : 1 ≤ ‖2 * w₃.1 + 1‖ := by
      have h2w₃_add : 2 * w₃.1 + 1 = 1 / (-2 * w₂.1 + 1) := by
        rw [hw₃_val, eq_div_iff hden_m2_ne, add_mul, mul_div_assoc',
          div_mul_cancel₀ _ hden_m2_ne]
        ring
      rw [h2w₃_add, norm_div, norm_one, hnorm_m2, div_one]
    have hw₃_minus : 1 < ‖2 * w₃.1 - 1‖ := by
      rw [one_lt_norm_two_mul_sub_one_iff]
      nlinarith [sq_nonneg w₃.1.re, sq_nonneg w₃.1.im]
    exact ⟨α₃, hα₃, w₃.2, hw₃_re_lo, hw₃_re_hi, hw₃_plus, hw₃_minus⟩
  · -- Interior/non-boundary case `1 < ‖2 * w₂ - 1‖`: `w₂ ∈ FundamentalSetQ` directly!
    exact ⟨α₂, hα₂, hy₂, hw₂_re_lo, hw₂_re_hi, hw₂_plus, hw₂_minus_gt⟩

/-- **16.19 (Part 2: Union of `Γ`-translates of `Q` equals `Π⁺`, RCA p. 329):** -/
theorem iUnion_moebiusTranslate_fundamentalSetQ :
    (⋃ γ ∈ GammaSubgroup, moebiusTranslate γ FundamentalSetQ) = UpperHalfPlaneSet := by
  apply Set.Subset.antisymm
  · rw [Set.iUnion₂_subset_iff]
    intro γ _
    exact moebiusTranslate_subset_upperHalfPlaneSet γ FundamentalSetQ
  · intro z hz
    obtain ⟨α, hα, hq⟩ := exists_gamma_apply_mem_fundamentalSetQ ⟨z, hz⟩
    rw [Set.mem_iUnion₂]
    refine ⟨α⁻¹, GammaSubgroup.inv_mem hα, ?_⟩
    rw [mem_moebiusTranslate_fundamentalSetQ_iff]
    refine ⟨(α.1 ⟨z, hz⟩).1, hq, ?_⟩
    have hsub : (⟨(α.1 ⟨z, hz⟩).1, fundamentalSetQ_subset_upperHalfPlaneSet hq⟩ :
        UpperHalfPlaneSet) = α.1 ⟨z, hz⟩ := rfl
    rw [hsub]
    change ((α⁻¹ * α).1 ⟨z, hz⟩).1 = z
    rw [inv_mul_cancel]
    rfl

/-- **16.19 (Unique orbit decomposition `Π⁺ = ⊔_{γ ∈ Γ} γ(Q)`, RCA p. 329):**
For every `z ∈ Π⁺`, there exists a unique `γ ∈ GammaSubgroup` and a unique `q ∈ FundamentalSetQ`
such that `γ(q) = z`. -/
theorem existsUnique_gamma_fundamentalSetQ {z : ℂ} (hz : z ∈ UpperHalfPlaneSet) :
    ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
      (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z := by
  have hz_mem : z ∈ ⋃ γ ∈ GammaSubgroup, moebiusTranslate γ FundamentalSetQ := by
    rw [iUnion_moebiusTranslate_fundamentalSetQ]
    exact hz
  rw [Set.mem_iUnion₂] at hz_mem
  rcases hz_mem with ⟨γ, hγ, hz_tr⟩
  rcases mem_moebiusTranslate_fundamentalSetQ_iff.mp hz_tr with ⟨q, hq, hγq⟩
  refine ⟨(⟨γ, hγ⟩, ⟨q, hq⟩), hγq, ?_⟩
  rintro ⟨⟨γ', hγ'⟩, ⟨q', hq'⟩⟩ hγ'q'
  have hsame : γ' = γ := by
    by_contra hne
    have hdisj := disjoint_moebiusTranslate_fundamentalSetQ hγ' hγ hne
    have hm1 : z ∈ moebiusTranslate γ' FundamentalSetQ :=
      mem_moebiusTranslate_fundamentalSetQ_iff.mpr ⟨q', hq', hγ'q'⟩
    have hm2 : z ∈ moebiusTranslate γ FundamentalSetQ :=
      mem_moebiusTranslate_fundamentalSetQ_iff.mpr ⟨q, hq, hγq⟩
    exact Set.disjoint_left.mp hdisj hm1 hm2
  subst γ'
  have hsub_eq :
      (⟨q', fundamentalSetQ_subset_upperHalfPlaneSet hq'⟩ : UpperHalfPlaneSet) =
        ⟨q, fundamentalSetQ_subset_upperHalfPlaneSet hq⟩ :=
    (γ.1).injective (Subtype.ext (hγ'q'.trans hγq.symm))
  have hq_eq : q' = q := congrArg Subtype.val hsub_eq
  ext
  · rfl
  · exact hq_eq

/-- **16.19 (Part 3: `GammaSubgroup = ParityMoebiusSubgroup`, RCA pp. 329–330):**
`Γ` consists of ALL determinant-one integral Möbius transformations with odd diagonal entries
and even off-diagonal entries. -/
theorem gammaSubgroup_eq_parityMoebiusSubgroup :
    GammaSubgroup = ParityMoebiusSubgroup := by
  apply le_antisymm gammaSubgroup_le_parityMoebiusSubgroup
  intro φ hφ
  let i_uhp : UpperHalfPlaneSet := ⟨Complex.I, I_mem_upperHalfPlaneSet⟩
  obtain ⟨α, hα, hq⟩ := exists_gamma_apply_mem_fundamentalSetQ (φ.1 i_uhp)
  have hαφ_mem : α * φ ∈ ParityMoebiusSubgroup :=
    ParityMoebiusSubgroup.mul_mem (gammaSubgroup_le_parityMoebiusSubgroup hα) hφ
  have hαφ_I : ((α * φ).1 i_uhp).1 ∈ FundamentalSetQ := hq
  have hαφ_one : α * φ = 1 :=
    parityMoebius_eq_one_of_mem_fundamentalSetQ hαφ_mem I_mem_fundamentalSetQ hαφ_I
  have hφ_eq : φ = α⁻¹ := eq_inv_of_mul_eq_one_right hαφ_one
  rw [hφ_eq]
  exact GammaSubgroup.inv_mem hα

/-- Explicit entrywise membership criterion for `GammaSubgroup`. -/
theorem intMoebiusPerm_mem_gammaSubgroup_iff {a b c d : ℤ} (hdet : a * d - b * c = 1) :
    (⟨intMoebiusPerm a b c d hdet, a, b, c, d, hdet, rfl⟩ : ModularMoebiusGroup) ∈ GammaSubgroup ↔
      Odd a ∧ Odd d ∧ Even b ∧ Even c := by
  rw [gammaSubgroup_eq_parityMoebiusSubgroup]
  constructor
  · rintro ⟨a', b', c', d', hdet', ha', hd', hb', hc', heq⟩
    let A : SL(2, ℤ) := ⟨!![a, b; c, d], by simpa [Matrix.det_fin_two_of] using hdet⟩
    let A' : SL(2, ℤ) := ⟨!![a', b'; c', d'], by simpa [Matrix.det_fin_two_of] using hdet'⟩
    have hmoeb : sl2zToMoebius A = sl2zToMoebius A' := by
      ext z
      rw [sl2zToMoebius_apply, sl2zToMoebius_apply]
      have hz := congrArg (fun f : Equiv.Perm UpperHalfPlaneSet => (f z).1) heq
      simpa [A, A'] using hz
    rcases (sl2zToMoebius_eq_iff A A').mp hmoeb with hAB | hAB
    · have ha_eq : a = a' := by
        have := congrArg (fun M : SL(2, ℤ) => M.1 0 0) hAB; simpa [A, A'] using this
      have hb_eq : b = b' := by
        have := congrArg (fun M : SL(2, ℤ) => M.1 0 1) hAB; simpa [A, A'] using this
      have hc_eq : c = c' := by
        have := congrArg (fun M : SL(2, ℤ) => M.1 1 0) hAB; simpa [A, A'] using this
      have hd_eq : d = d' := by
        have := congrArg (fun M : SL(2, ℤ) => M.1 1 1) hAB; simpa [A, A'] using this
      subst ha_eq; subst hb_eq; subst hc_eq; subst hd_eq
      exact ⟨ha', hd', hb', hc'⟩
    · have hmat : A.1 = -A'.1 := by
        rw [hAB, Matrix.SpecialLinearGroup.coe_neg]
      have ha_eq : a = -a' := by
        have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hmat; simpa [A, A'] using this
      have hb_eq : b = -b' := by
        have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hmat; simpa [A, A'] using this
      have hc_eq : c = -c' := by
        have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) hmat; simpa [A, A'] using this
      have hd_eq : d = -d' := by
        have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 1) hmat; simpa [A, A'] using this
      subst ha_eq; subst hb_eq; subst hc_eq; subst hd_eq
      exact ⟨odd_neg_int ha', odd_neg_int hd', even_neg_int hb', even_neg_int hc'⟩
  · rintro ⟨ha, hd, hb, hc⟩
    exact ⟨a, b, c, d, hdet, ha, hd, hb, hc, rfl⟩

/-- **Theorem 16.19 (Fundamental Domain & Parity Characterization of `Γ`, RCA pp. 329–330):**
1. If `γ₁, γ₂ ∈ Γ` and `γ₁ ≠ γ₂`, then `γ₁(Q)` and `γ₂(Q)` are disjoint;
2. `⋃_{γ ∈ Γ} γ(Q) = Π⁺`;
3. `Γ` contains every transformation `(a z + b) / (c z + d)` in `G` with `a, d` odd and `b, c`
   even, and in fact `Γ = ParityMoebiusSubgroup`. -/
theorem theorem16_19 :
    (∀ γ₁ ∈ GammaSubgroup, ∀ γ₂ ∈ GammaSubgroup, γ₁ ≠ γ₂ →
      Disjoint (moebiusTranslate γ₁ FundamentalSetQ) (moebiusTranslate γ₂ FundamentalSetQ)) ∧
    ((⋃ γ ∈ GammaSubgroup, moebiusTranslate γ FundamentalSetQ) = UpperHalfPlaneSet) ∧
    (GammaSubgroup = ParityMoebiusSubgroup ∧
      ∀ (a b c d : ℤ) (hdet : a * d - b * c = 1),
        Odd a → Odd d → Even b → Even c →
          (⟨intMoebiusPerm a b c d hdet, a, b, c, d, hdet, rfl⟩ : ModularMoebiusGroup) ∈
            GammaSubgroup) :=
  ⟨fun _ hγ₁ _ hγ₂ hne => disjoint_moebiusTranslate_fundamentalSetQ hγ₁ hγ₂ hne,
    iUnion_moebiusTranslate_fundamentalSetQ,
    ⟨gammaSubgroup_eq_parityMoebiusSubgroup,
      fun _ _ _ _ hdet ha hd hb hc =>
        (intMoebiusPerm_mem_gammaSubgroup_iff hdet).mpr ⟨ha, hd, hb, hc⟩⟩⟩

/-! ### Axiom Verification -/

#print axioms UpperHalfPlaneSet
#print axioms mem_upperHalfPlaneSet
#print axioms I_mem_upperHalfPlaneSet
#print axioms isOpen_upperHalfPlaneSet
#print axioms convex_upperHalfPlaneSet
#print axioms isRegion_upperHalfPlaneSet
#print axioms intMoebius
#print axioms intMoebius_neg
#print axioms intMoebius_id
#print axioms intMoebius_denom_ne_zero_of_im_ne_zero
#print axioms intMoebius_denom_ne_zero
#print axioms intMoebius_im_general
#print axioms intMoebius_im
#print axioms intMoebius_mem_upperHalfPlaneSet
#print axioms intMoebius_holomorphicOn
#print axioms intMoebius_differentiableOn
#print axioms intMoebius_coe_riemannSphere
#print axioms intMoebius_comp
#print axioms intMoebius_inv_left
#print axioms intMoebius_inv_right
#print axioms intMoebius_inv_formula
#print axioms intMoebiusPerm
#print axioms intMoebiusPerm_apply
#print axioms intMoebiusPerm_inv
#print axioms intMoebiusPerm_one
#print axioms intMoebiusPerm_neg
#print axioms intMoebiusPerm_mul
#print axioms ModularMoebiusGroup
#print axioms ModularMoebiusGroup.ext
#print axioms ModularMoebiusGroup.one_apply
#print axioms ModularMoebiusGroup.mul_apply
#print axioms sl2z_det_eq_one
#print axioms sl2zToPerm
#print axioms sl2zToMoebius
#print axioms sl2zToMoebius_apply
#print axioms sl2zToMoebius_neg
#print axioms sl2zToMoebius_surjective
#print axioms intMoebiusPerm_eq_one_iff
#print axioms sl2zToMoebius_eq_one_iff
#print axioms sl2zToMoebius_ker
#print axioms sl2zToMoebius_eq_iff
#print axioms modularT
#print axioms modularS
#print axioms modularT_apply
#print axioms modularT_zpow_apply
#print axioms modularS_apply
#print axioms modularS_sq
#print axioms modularS_inv
#print axioms modularT_ne_one
#print axioms modularMoebiusGroup_top_ne_bot
#print axioms modularMoebiusGroup_closure_S_T
#print axioms IsModularFunctionFor
#print axioms IsFullModularFunction
#print axioms IsModularFunction
#print axioms isFullModularFunction_iff
#print axioms IsModularFunctionFor.isModularFunction
#print axioms IsFullModularFunction.isModularFunction
#print axioms differentiableOn_upperHalfPlaneSet_iff_holomorphicOn
#print axioms theorem16_17
#print axioms sigmaMatrix
#print axioms tauMatrix
#print axioms sigmaInvMatrix
#print axioms modularSigma
#print axioms modularTau
#print axioms modularSigma_apply
#print axioms sigmaMatrix_inv
#print axioms modularSigma_inv_apply
#print axioms modularTau_apply
#print axioms modularTau_eq_T_sq
#print axioms modularSigma_eq_S_T_S
#print axioms modularTau_zpow_apply
#print axioms GammaSubgroup
#print axioms modularSigma_mem_gamma
#print axioms modularTau_mem_gamma
#print axioms modularTau_ne_one
#print axioms gammaSubgroup_ne_bot
#print axioms FundamentalSetQ
#print axioms fundamentalSetQ_subset_upperHalfPlaneSet
#print axioms norm_two_mul_add_one_sq
#print axioms norm_two_mul_sub_one_sq
#print axioms one_le_norm_two_mul_add_one_iff
#print axioms one_lt_norm_two_mul_sub_one_iff
#print axioms norm_two_mul_add_one_eq_one_iff
#print axioms norm_two_mul_sub_one_eq_one_iff
#print axioms I_mem_fundamentalSetQ
#print axioms theorem16_18
#print axioms ParityMoebiusSubgroup
#print axioms modularSigma_mem_parityMoebiusSubgroup
#print axioms modularTau_mem_parityMoebiusSubgroup
#print axioms gammaSubgroup_le_parityMoebiusSubgroup
#print axioms moebiusTranslate
#print axioms mem_moebiusTranslate_iff
#print axioms mem_moebiusTranslate_fundamentalSetQ_iff
#print axioms moebiusTranslate_subset_upperHalfPlaneSet
#print axioms parityMoebius_eq_one_of_mem_fundamentalSetQ
#print axioms disjoint_moebiusTranslate_fundamentalSetQ_of_parity
#print axioms disjoint_moebiusTranslate_fundamentalSetQ
#print axioms exists_gamma_apply_mem_fundamentalSetQ
#print axioms iUnion_moebiusTranslate_fundamentalSetQ
#print axioms existsUnique_gamma_fundamentalSetQ
#print axioms gammaSubgroup_eq_parityMoebiusSubgroup
#print axioms intMoebiusPerm_mem_gammaSubgroup_iff
#print axioms theorem16_19


end Chapter16PartC

section Chapter16PartD
open Set Function Filter Metric Complex Topology
open scoped Interval Real MatrixGroups

/-!
### Section 1: Right Half `Q₀`, Order-3 Symmetry `M₃`, and Normalized Riemann Map `ψ` (`16.20`)
-/

/-- The open right-hand modular triangle
`Q₀ = {z ∈ ℂ : Im z > 0, 0 < Re z < 1, |2 z - 1| > 1}` (RCA p. 330). -/
def OpenTriangleQ0 : Set ℂ :=
  {z : ℂ | 0 < z.im ∧ 0 < z.re ∧ z.re < 1 ∧ 1 < ‖2 * z - 1‖}

theorem openTriangleQ0_subset_fundamentalSetQ : OpenTriangleQ0 ⊆ FundamentalSetQ := by
  rintro z ⟨him, hre0, hre1, hsub⟩
  refine ⟨him, by linarith, hre1, ?_, hsub⟩
  rw [one_le_norm_two_mul_add_one_iff]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

theorem openTriangleQ0_subset_upperHalfPlaneSet : OpenTriangleQ0 ⊆ UpperHalfPlaneSet :=
  fun _ hz => hz.1

theorem isOpen_openTriangleQ0 : IsOpen OpenTriangleQ0 := by
  refine (isOpen_lt continuous_const Complex.continuous_im).inter ?_
  refine (isOpen_lt continuous_const Complex.continuous_re).inter ?_
  refine (isOpen_lt Complex.continuous_re continuous_const).inter ?_
  exact isOpen_lt continuous_const
    (continuous_norm.comp ((continuous_const.mul continuous_id).sub continuous_const))

/-- Basepoint `z₀ = 1/2 + i √3 / 2 = e^{π i / 3}` of `Q₀`, fixed by `M₃(z) = 1 - 1 / z`. -/
def z0Center : ℂ :=
  1 / 2 + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I

/-- Primitive cube root of unity `ω = -1/2 - i √3 / 2 = e^{-2π i / 3} = z₀⁻²`. -/
def omegaCube : ℂ :=
  -1 / 2 - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I

@[simp]
theorem z0Center_re : z0Center.re = 1 / 2 := by
  simp [z0Center]

@[simp]
theorem z0Center_im : z0Center.im = Real.sqrt 3 / 2 := by
  simp [z0Center]

@[simp]
theorem omegaCube_re : omegaCube.re = -1 / 2 := by
  simp [omegaCube]

@[simp]
theorem omegaCube_im : omegaCube.im = -(Real.sqrt 3 / 2) := by
  simp [omegaCube]

theorem z0Center_im_pos : 0 < z0Center.im := by
  rw [z0Center_im]
  positivity

theorem z0Center_mem_openTriangleQ0 : z0Center ∈ OpenTriangleQ0 := by
  refine ⟨z0Center_im_pos, by norm_num [z0Center_re], by norm_num [z0Center_re], ?_⟩
  rw [one_lt_norm_two_mul_sub_one_iff, z0Center_re, z0Center_im]
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem half_add_im_mem_openTriangleQ0 {y : ℝ} (hy : 1 ≤ y) :
    (1 / 2 : ℂ) + (y : ℂ) * Complex.I ∈ OpenTriangleQ0 := by
  let w : ℂ := (1 / 2 : ℂ) + (y : ℂ) * Complex.I
  have hw_re : w.re = 1 / 2 := by simp [w]
  have hw_im : w.im = y := by simp [w]
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  rw [one_lt_norm_two_mul_sub_one_iff, hw_re, hw_im]
  nlinarith

theorem z0Center_ne_zero : z0Center ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem norm_omegaCube : ‖omegaCube‖ = 1 := by
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hnsq : Complex.normSq omegaCube = 1 := by
    rw [Complex.normSq_apply, omegaCube_re, omegaCube_im]
    nlinarith
  rw [Complex.norm_def, hnsq, Real.sqrt_one]

theorem omegaCube_ne_zero : omegaCube ≠ 0 := by
  intro h
  have := norm_omegaCube
  rw [h, norm_zero] at this
  norm_num at this

theorem omegaCube_pow_three : omegaCube ^ 3 = 1 := by
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcub : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by rw [pow_succ, hsq3]
  apply Complex.ext
  · simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im,
      omegaCube_re, omegaCube_im, Complex.one_re]
    ring_nf; rw [hsq3]; norm_num
  · simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im,
      omegaCube_re, omegaCube_im, Complex.one_im]
    ring_nf; rw [hcub]; ring

theorem sum_omegaCube : 1 + omegaCube + omegaCube ^ 2 = 0 := by
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    simp only [sq, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      omegaCube_re, omegaCube_im, Complex.one_re, Complex.one_im,
      Complex.zero_re, Complex.zero_im] <;>
    nlinarith

theorem omegaCube_ne_one : omegaCube ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  norm_num at this

theorem omegaCube_sq_ne_one : omegaCube ^ 2 ≠ 1 := by
  intro h
  have h3 := omegaCube_pow_three
  rw [pow_succ, h, one_mul] at h3
  exact omegaCube_ne_one h3

theorem star_omegaCube : starRingEnd ℂ omegaCube = omegaCube ^ 2 := by
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    simp only [sq, Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im,
      omegaCube_re, omegaCube_im] <;>
    nlinarith

theorem z0Center_sq_inv : (z0Center ^ 2)⁻¹ = omegaCube := by
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcub : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by rw [pow_succ, hsq3]
  have hprod : z0Center ^ 2 * omegaCube = 1 := by
    apply Complex.ext
    · simp only [sq, Complex.mul_re, Complex.mul_im, z0Center_re, z0Center_im,
        omegaCube_re, omegaCube_im, Complex.one_re]
      ring_nf; rw [hsq3]; norm_num
    · simp only [sq, Complex.mul_re, Complex.mul_im, z0Center_re, z0Center_im,
        omegaCube_re, omegaCube_im, Complex.one_im]
      ring_nf; rw [hcub]; ring
  exact inv_eq_of_mul_eq_one_right hprod

theorem neg_omegaCube_eq_z0Center : -omegaCube = z0Center := by
  apply Complex.ext <;> (simp [omegaCube, z0Center]; try norm_num)

theorem isConnected_openTriangleQ0 : IsConnected OpenTriangleQ0 := by
  let pTop : ℂ := 1 / 2 + Complex.I
  have hpTop : pTop ∈ OpenTriangleQ0 := by
    simpa [pTop] using half_add_im_mem_openTriangleQ0 (le_rfl : (1 : ℝ) ≤ 1)
  have hjoin : ∀ z ∈ OpenTriangleQ0, ∃ C : Set ℂ,
      C ⊆ OpenTriangleQ0 ∧ z ∈ C ∧ pTop ∈ C ∧ IsPreconnected C := by
    intro z ⟨him, hre0, hre1, hnorm⟩
    rw [one_lt_norm_two_mul_sub_one_iff] at hnorm
    let Y : ℝ := max z.im 1
    have hY_ge_im : z.im ≤ Y := le_max_left z.im 1
    have hY_ge_one : 1 ≤ Y := le_max_right z.im 1
    let γ₁ : ℝ → ℂ := fun t => (z.re : ℂ) + (t : ℂ) * Complex.I
    let γ₂ : ℝ → ℂ := fun x => (x : ℂ) + (Y : ℂ) * Complex.I
    let γ₃ : ℝ → ℂ := fun t => (1 / 2 : ℂ) + (t : ℂ) * Complex.I
    let S₁ : Set ℂ := γ₁ '' Set.Icc z.im Y
    let S₂ : Set ℂ := γ₂ '' Set.uIcc z.re (1 / 2)
    let S₃ : Set ℂ := γ₃ '' Set.Icc 1 Y
    have hS₁_sub : S₁ ⊆ OpenTriangleQ0 := by
      rintro _ ⟨t, ⟨ht1, _⟩, rfl⟩
      have hre : (γ₁ t).re = z.re := by simp [γ₁]
      have him_t : (γ₁ t).im = t := by simp [γ₁]
      refine ⟨by linarith, by linarith, by linarith, ?_⟩
      rw [one_lt_norm_two_mul_sub_one_iff, hre, him_t]
      nlinarith
    have hS₂_sub : S₂ ⊆ OpenTriangleQ0 := by
      rintro _ ⟨x, hx, rfl⟩
      have hx0 : 0 < x := lt_of_lt_of_le (lt_min hre0 (by norm_num)) hx.1
      have hx1 : x < 1 := lt_of_le_of_lt hx.2 (max_lt hre1 (by norm_num))
      have hre : (γ₂ x).re = x := by simp [γ₂]
      have him_x : (γ₂ x).im = Y := by simp [γ₂]
      refine ⟨by linarith, by linarith, by linarith, ?_⟩
      rw [one_lt_norm_two_mul_sub_one_iff, hre, him_x]
      nlinarith [sq_nonneg x]
    have hS₃_sub : S₃ ⊆ OpenTriangleQ0 := by
      rintro _ ⟨t, ⟨ht1, _⟩, rfl⟩
      exact half_add_im_mem_openTriangleQ0 ht1
    have hγ₁_cont : Continuous γ₁ :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hγ₂_cont : Continuous γ₂ :=
      Complex.continuous_ofReal.add continuous_const
    have hγ₃_cont : Continuous γ₃ :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hS₁_pre : IsPreconnected S₁ := (isPreconnected_Icc.image _ hγ₁_cont.continuousOn)
    have hS₂_pre : IsPreconnected S₂ := (isPreconnected_uIcc.image _ hγ₂_cont.continuousOn)
    have hS₃_pre : IsPreconnected S₃ := (isPreconnected_Icc.image _ hγ₃_cont.continuousOn)
    let p₁ : ℂ := (z.re : ℂ) + (Y : ℂ) * Complex.I
    let p₂ : ℂ := (1 / 2 : ℂ) + (Y : ℂ) * Complex.I
    have hp₁_1 : p₁ ∈ S₁ := ⟨Y, ⟨hY_ge_im, le_rfl⟩, rfl⟩
    have hp₁_2 : p₁ ∈ S₂ := ⟨z.re, Set.left_mem_uIcc, rfl⟩
    have hp₂_2 : p₂ ∈ S₂ := ⟨1 / 2, Set.right_mem_uIcc, by simp [γ₂, p₂]⟩
    have hp₂_3 : p₂ ∈ S₃ := ⟨Y, ⟨hY_ge_one, le_rfl⟩, rfl⟩
    have h12_pre : IsPreconnected (S₁ ∪ S₂) := hS₁_pre.union p₁ hp₁_1 hp₁_2 hS₂_pre
    have h123_pre : IsPreconnected ((S₁ ∪ S₂) ∪ S₃) :=
      h12_pre.union p₂ (Or.inr hp₂_2) hp₂_3 hS₃_pre
    have hz_mem : z ∈ S₁ := ⟨z.im, ⟨le_rfl, hY_ge_im⟩, Complex.re_add_im z⟩
    have hpTop_mem : pTop ∈ S₃ := ⟨1, ⟨le_rfl, hY_ge_one⟩, by simp [γ₃, pTop]⟩
    exact ⟨(S₁ ∪ S₂) ∪ S₃, union_subset (union_subset hS₁_sub hS₂_sub) hS₃_sub,
      Or.inl (Or.inl hz_mem), Or.inr hpTop_mem, h123_pre⟩
  refine ⟨⟨z0Center, z0Center_mem_openTriangleQ0⟩, isPreconnected_of_forall_pair fun x hx y hy => ?_⟩
  obtain ⟨Cx, hCx_sub, hxCx, hpCx, hCx_pre⟩ := hjoin x hx
  obtain ⟨Cy, hCy_sub, hyCy, hpCy, hCy_pre⟩ := hjoin y hy
  exact ⟨Cx ∪ Cy, union_subset hCx_sub hCy_sub, Or.inl hxCx, Or.inr hyCy,
    hCx_pre.union pTop hpCx hpCy hCy_pre⟩

theorem isRegion_openTriangleQ0 : RudinRCA.Chapter10.IsRegion OpenTriangleQ0 :=
  ⟨isOpen_openTriangleQ0, isConnected_openTriangleQ0⟩

theorem openTriangleQ0_ne_univ : OpenTriangleQ0 ≠ Set.univ := by
  intro h
  have h0 : (0 : ℂ) ∈ OpenTriangleQ0 := h.symm ▸ Set.mem_univ 0
  exact lt_irrefl 0 h0.1

/-- `OpenTriangleQ0` is simply connected (`BookSimplyConnected`) because `S² \ Q₀` is the union
of three closed half-planes through `∞` and `closedBall (1/2) (1/2)` meeting `{Im ≤ 0}` at `0`. -/
theorem bookSimplyConnected_openTriangleQ0 :
    RudinRCA.Chapter10.BookSimplyConnected OpenTriangleQ0 := by
  let S1 : Set ℂ := {z : ℂ | z.im ≤ 0}
  let S2 : Set ℂ := {z : ℂ | z.re ≤ 0}
  let S3 : Set ℂ := {z : ℂ | 1 ≤ z.re}
  let S4 : Set ℂ := Metric.closedBall (1 / 2 : ℂ) (1 / 2)
  have hS1_conn : IsConnected S1 :=
    ⟨⟨0, by simp [S1]⟩, (convex_halfSpace_le Complex.imLm.isLinear 0).isPreconnected⟩
  have hS2_conn : IsConnected S2 :=
    ⟨⟨0, by simp [S2]⟩, (convex_halfSpace_le Complex.reLm.isLinear 0).isPreconnected⟩
  have hS3_conn : IsConnected S3 :=
    ⟨⟨1, by simp [S3]⟩, (convex_halfSpace_ge Complex.reLm.isLinear 1).isPreconnected⟩
  let A1 : Set RudinRCA.Chapter13.RiemannSphere :=
    insert (OnePoint.infty : RudinRCA.Chapter13.RiemannSphere)
      (((↑) : ℂ → RudinRCA.Chapter13.RiemannSphere) '' S1)
  let A2 : Set RudinRCA.Chapter13.RiemannSphere :=
    insert (OnePoint.infty : RudinRCA.Chapter13.RiemannSphere)
      (((↑) : ℂ → RudinRCA.Chapter13.RiemannSphere) '' S2)
  let A3 : Set RudinRCA.Chapter13.RiemannSphere :=
    insert (OnePoint.infty : RudinRCA.Chapter13.RiemannSphere)
      (((↑) : ℂ → RudinRCA.Chapter13.RiemannSphere) '' S3)
  let A4 : Set RudinRCA.Chapter13.RiemannSphere :=
    ((↑) : ℂ → RudinRCA.Chapter13.RiemannSphere) '' S4
  have hA1_conn : IsConnected A1 := by
    refine RudinRCA.Chapter13.isConnected_insert_infinity hS1_conn fun r hr => ?_
    refine ⟨((-(r + 1) : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · simp [S1]; linarith
    · rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
        abs_neg, abs_of_pos (by linarith : 0 < r + 1)]
      linarith
  have hA2_conn : IsConnected A2 := by
    refine RudinRCA.Chapter13.isConnected_insert_infinity hS2_conn fun r hr => ?_
    refine ⟨((-(r + 1) : ℝ) : ℂ), ?_, ?_⟩
    · simp [S2]; linarith
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith : 0 < r + 1)]
      linarith
  have hA3_conn : IsConnected A3 := by
    refine RudinRCA.Chapter13.isConnected_insert_infinity hS3_conn fun r hr => ?_
    refine ⟨(((r + 2) : ℝ) : ℂ), ?_, ?_⟩
    · simp [S3]; linarith
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < r + 2)]
      linarith
  have hA4_conn : IsConnected A4 := by
    have hcb : IsConnected S4 :=
      ⟨⟨1 / 2, Metric.mem_closedBall_self (by norm_num)⟩, (convex_closedBall _ _).isPreconnected⟩
    exact hcb.image _ OnePoint.continuous_coe.continuousOn
  have h12_pre : IsPreconnected (A1 ∪ A2) :=
    hA1_conn.2.union OnePoint.infty (Set.mem_insert _ _) (Set.mem_insert _ _) hA2_conn.2
  have h123_pre : IsPreconnected ((A1 ∪ A2) ∪ A3) :=
    h12_pre.union OnePoint.infty (Or.inl (Set.mem_insert _ _)) (Set.mem_insert _ _) hA3_conn.2
  have h0_A1 : ((0 : ℂ) : RudinRCA.Chapter13.RiemannSphere) ∈ A1 :=
    Set.mem_insert_of_mem _ ⟨0, by simp [S1], rfl⟩
  have h0_A4 : ((0 : ℂ) : RudinRCA.Chapter13.RiemannSphere) ∈ A4 := by
    refine ⟨0, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    norm_num
  have hall_pre : IsPreconnected (((A1 ∪ A2) ∪ A3) ∪ A4) :=
    h123_pre.union ((0 : ℂ) : RudinRCA.Chapter13.RiemannSphere)
      (Or.inl (Or.inl h0_A1)) h0_A4 hA4_conn.2
  have heq : ((A1 ∪ A2) ∪ A3) ∪ A4 = RudinRCA.Chapter13.sphericalCompl OpenTriangleQ0 := by
    ext p
    induction p using OnePoint.rec with
    | infty =>
      simp [A1, RudinRCA.Chapter13.sphericalCompl]
    | coe z =>
      have hcb_iff : z ∈ S4 ↔ ‖2 * z - 1‖ ≤ 1 := by
        dsimp [S4]
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h2 : 2 * z - 1 = (2 : ℂ) * (z - 1 / 2) := by ring
        rw [h2, norm_mul, Complex.norm_ofNat]
        constructor <;> intro h <;> linarith
      simp [A1, A2, A3, A4, OnePoint.coe_ne_infty, S1, S2, S3, hcb_iff, OpenTriangleQ0]
      constructor
      · intro h h1 h2 h3
        rcases h with (((h' | h') | h') | h') <;> linarith
      · intro h
        by_cases h1 : z.im ≤ 0
        · exact Or.inl (Or.inl (Or.inl h1))
        · by_cases h2 : z.re ≤ 0
          · exact Or.inl (Or.inl (Or.inr h2))
          · by_cases h3 : 1 ≤ z.re
            · exact Or.inl (Or.inr h3)
            · exact Or.inr (h (not_le.mp h1) (not_le.mp h2) (not_le.mp h3))
  have hcomp_conn : IsConnected (RudinRCA.Chapter13.sphericalCompl OpenTriangleQ0) := by
    rw [← heq]
    exact ⟨⟨OnePoint.infty, Or.inl (Or.inl (Or.inl (Set.mem_insert _ _)))⟩, hall_pre⟩
  have h13 := RudinRCA.Chapter13.theorem13_11 isRegion_openTriangleQ0
  exact (h13.2.2.1.trans h13.2.2.2.1).mpr hcomp_conn

/-- Order-3 conformal symmetry `M₃(z) = 1 - 1 / z` permuting `(0, 1, ∞) ↦ (∞, 0, 1)`. -/
def moebiusM3 (z : ℂ) : ℂ :=
  1 - 1 / z

theorem moebiusM3_z0Center : moebiusM3 z0Center = z0Center := by
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold moebiusM3
  field_simp [z0Center_ne_zero]
  apply Complex.ext
  · simp only [sq, Complex.sub_re, Complex.mul_re, z0Center_re, z0Center_im, Complex.one_re]
    ring_nf; rw [hsq3]; norm_num
  · simp only [sq, Complex.sub_im, Complex.mul_im, z0Center_re, z0Center_im, Complex.one_im]
    ring_nf

theorem moebiusM3_ne_zero {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) : moebiusM3 z ≠ 0 := by
  unfold moebiusM3
  intro h
  have h1 : 1 / z = 1 := (sub_eq_zero.mp h).symm
  exact hz1 ((div_eq_one_iff_eq hz0).mp h1).symm

theorem moebiusM3_ne_one {z : ℂ} (hz0 : z ≠ 0) : moebiusM3 z ≠ 1 := by
  unfold moebiusM3
  intro h
  have : 1 / z = 0 := by linear_combination -h
  exact one_div_ne_zero hz0 this

theorem moebiusM3_iter2 {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    moebiusM3 (moebiusM3 z) = 1 / (1 - z) := by
  have hm0 : moebiusM3 z ≠ 0 := moebiusM3_ne_zero hz0 hz1
  have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  unfold moebiusM3 at hm0 ⊢
  field_simp [hz0, h1z, hm0]
  ring

theorem moebiusM3_iter3 {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    moebiusM3 (moebiusM3 (moebiusM3 z)) = z := by
  rw [moebiusM3_iter2 hz0 hz1]
  have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  unfold moebiusM3
  field_simp [h1z]
  ring

theorem moebiusM3_re_im (z : ℂ) :
    (moebiusM3 z).re = 1 - z.re / Complex.normSq z ∧
      (moebiusM3 z).im = z.im / Complex.normSq z := by
  unfold moebiusM3
  constructor
  · simp [one_div, Complex.inv_re]
  · simp [one_div, Complex.inv_im]; ring

theorem moebiusM3_mapsTo_openTriangleQ0 :
    Set.MapsTo moebiusM3 OpenTriangleQ0 OpenTriangleQ0 := by
  rintro z ⟨him, hre0, hre1, hnorm⟩
  rw [one_lt_norm_two_mul_sub_one_iff] at hnorm
  have hnsq_eq : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have hnsq_pos : 0 < Complex.normSq z := by
    rw [hnsq_eq]; nlinarith
  obtain ⟨hre_m, him_m⟩ := moebiusM3_re_im z
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him_m]
    exact div_pos him hnsq_pos
  · rw [hre_m, sub_pos, div_lt_one hnsq_pos, hnsq_eq]
    exact hnorm
  · rw [hre_m]
    linarith [div_pos hre0 hnsq_pos]
  · rw [one_lt_norm_two_mul_sub_one_iff, hre_m, him_m]
    have halg : (1 - z.re / Complex.normSq z) ^ 2 + (z.im / Complex.normSq z) ^ 2 -
        (1 - z.re / Complex.normSq z) = (1 - z.re) / Complex.normSq z := by
      field_simp [hnsq_pos.ne']
      rw [hnsq_eq]
      ring
    have hpos : 0 < (1 - z.re) / Complex.normSq z := div_pos (by linarith) hnsq_pos
    linarith

theorem moebiusM3_bijOn_openTriangleQ0 :
    Set.BijOn moebiusM3 OpenTriangleQ0 OpenTriangleQ0 := by
  refine ⟨moebiusM3_mapsTo_openTriangleQ0, ?_, ?_⟩
  · intro z₁ hz₁ z₂ hz₂ heq
    have hz₁0 : z₁ ≠ 0 := fun h => by have := hz₁.1; rw [h, Complex.zero_im] at this; exact lt_irrefl 0 this
    have hz₁1 : z₁ ≠ 1 := fun h => by have := hz₁.1; rw [h, Complex.one_im] at this; exact lt_irrefl 0 this
    have hz₂0 : z₂ ≠ 0 := fun h => by have := hz₂.1; rw [h, Complex.zero_im] at this; exact lt_irrefl 0 this
    have hz₂1 : z₂ ≠ 1 := fun h => by have := hz₂.1; rw [h, Complex.one_im] at this; exact lt_irrefl 0 this
    calc z₁ = moebiusM3 (moebiusM3 (moebiusM3 z₁)) := (moebiusM3_iter3 hz₁0 hz₁1).symm
      _ = moebiusM3 (moebiusM3 (moebiusM3 z₂)) := by rw [heq]
      _ = z₂ := moebiusM3_iter3 hz₂0 hz₂1
  · intro w hw
    have hw0 : w ≠ 0 := fun h => by have := hw.1; rw [h, Complex.zero_im] at this; exact lt_irrefl 0 this
    have hw1 : w ≠ 1 := fun h => by have := hw.1; rw [h, Complex.one_im] at this; exact lt_irrefl 0 this
    exact ⟨moebiusM3 (moebiusM3 w),
      moebiusM3_mapsTo_openTriangleQ0 (moebiusM3_mapsTo_openTriangleQ0 hw),
      moebiusM3_iter3 hw0 hw1⟩

theorem hasDerivAt_moebiusM3 {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt moebiusM3 ((z ^ 2)⁻¹) z := by
  have heq : moebiusM3 = fun w : ℂ => 1 - w⁻¹ := funext fun w => by simp [moebiusM3, one_div]
  rw [heq]
  have hd : HasDerivAt (fun w : ℂ => 1 - w⁻¹) (0 - -(z ^ 2)⁻¹) z :=
    (hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_inv hz)
  simpa using hd

theorem hasDerivAt_moebiusM3_z0Center :
    HasDerivAt moebiusM3 omegaCube z0Center :=
  z0Center_sq_inv ▸ hasDerivAt_moebiusM3 z0Center_ne_zero

theorem moebiusM3_holomorphicOn_openTriangleQ0 :
    RudinRCA.Chapter10.HolomorphicOn moebiusM3 OpenTriangleQ0 := by
  intro z hz
  have hz0 : z ≠ 0 := fun h => by have := hz.1; rw [h, Complex.zero_im] at this; exact lt_irrefl 0 this
  exact (hasDerivAt_moebiusM3 hz0).differentiableAt

/-- Normalized Riemann map `ψ : Q₀ → ball 0 1` with `ψ(z₀) = 0` and `ψ'(z₀) > 0` (`14.9`). -/
def riemannPsi : ℂ → ℂ :=
  Classical.choose
    (RudinRCA.Chapter14.theorem14_9 isRegion_openTriangleQ0 bookSimplyConnected_openTriangleQ0
      openTriangleQ0_ne_univ z0Center_mem_openTriangleQ0)

theorem riemannPsi_spec :
    RudinRCA.Chapter10.HolomorphicOn riemannPsi OpenTriangleQ0 ∧
    Set.BijOn riemannPsi OpenTriangleQ0 (Metric.ball (0 : ℂ) 1) ∧
    riemannPsi z0Center = 0 ∧
    0 < (deriv riemannPsi z0Center).re ∧
    (deriv riemannPsi z0Center).im = 0 ∧
    ∀ f : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn f OpenTriangleQ0 →
      Set.MapsTo f OpenTriangleQ0 (Metric.ball (0 : ℂ) 1) →
      ‖deriv f z0Center‖ ≤ ‖deriv riemannPsi z0Center‖ ∧
      (‖deriv f z0Center‖ = ‖deriv riemannPsi z0Center‖ ↔
        ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ OpenTriangleQ0, f z = c * riemannPsi z) := by
  have h := Classical.choose_spec
    (RudinRCA.Chapter14.theorem14_9 isRegion_openTriangleQ0 bookSimplyConnected_openTriangleQ0
      openTriangleQ0_ne_univ z0Center_mem_openTriangleQ0)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

theorem riemannPsi_holo : RudinRCA.Chapter10.HolomorphicOn riemannPsi OpenTriangleQ0 :=
  riemannPsi_spec.1

theorem riemannPsi_bij : Set.BijOn riemannPsi OpenTriangleQ0 (Metric.ball (0 : ℂ) 1) :=
  riemannPsi_spec.2.1

theorem riemannPsi_z0Center : riemannPsi z0Center = 0 :=
  riemannPsi_spec.2.2.1

theorem riemannPsi_deriv_z0Center_ne_zero : deriv riemannPsi z0Center ≠ 0 := by
  intro h0
  have hpos := riemannPsi_spec.2.2.2.1
  rw [h0, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- 3-fold rotational equivariance `ψ(M₃(z)) = ω · ψ(z)` on `Q₀`, deduced from extremal
uniqueness in `14.9` at the fixed point `z₀` of `M₃`. -/
theorem riemannPsi_moebiusM3 {z : ℂ} (hz : z ∈ OpenTriangleQ0) :
    riemannPsi (moebiusM3 z) = omegaCube * riemannPsi z := by
  let f : ℂ → ℂ := fun w => riemannPsi (moebiusM3 w)
  have hf_holo : RudinRCA.Chapter10.HolomorphicOn f OpenTriangleQ0 :=
    fun w hw => (riemannPsi_holo (moebiusM3 w) (moebiusM3_mapsTo_openTriangleQ0 hw)).comp w
      (moebiusM3_holomorphicOn_openTriangleQ0 w hw)
  have hf_maps : Set.MapsTo f OpenTriangleQ0 (Metric.ball (0 : ℂ) 1) :=
    riemannPsi_bij.mapsTo.comp moebiusM3_mapsTo_openTriangleQ0
  have hd_psi : HasDerivAt riemannPsi (deriv riemannPsi z0Center) z0Center :=
    (riemannPsi_holo z0Center z0Center_mem_openTriangleQ0).hasDerivAt
  have hd_psi' : HasDerivAt riemannPsi (deriv riemannPsi z0Center) (moebiusM3 z0Center) := by
    rwa [moebiusM3_z0Center]
  have hd_f : HasDerivAt f (deriv riemannPsi z0Center * omegaCube) z0Center :=
    hd_psi'.comp z0Center hasDerivAt_moebiusM3_z0Center
  have hnorm_eq : ‖deriv f z0Center‖ = ‖deriv riemannPsi z0Center‖ := by
    rw [hd_f.deriv, norm_mul, norm_omegaCube, mul_one]
  obtain ⟨c, _, hc_eq⟩ := (riemannPsi_spec.2.2.2.2.2 f hf_holo hf_maps).2.mp hnorm_eq
  have hev : f =ᶠ[𝓝 z0Center] fun w => c * riemannPsi w := by
    filter_upwards [isOpen_openTriangleQ0.mem_nhds z0Center_mem_openTriangleQ0] with w hw
    exact hc_eq w hw
  have hd_rhs : HasDerivAt (fun w => c * riemannPsi w) (c * deriv riemannPsi z0Center) z0Center :=
    hd_psi.const_mul c
  have hderiv_eq : deriv riemannPsi z0Center * omegaCube = c * deriv riemannPsi z0Center := by
    rw [← hd_f.deriv, hev.deriv_eq, hd_rhs.deriv]
  have hc_omega : c = omegaCube := by
    apply mul_right_cancel₀ riemannPsi_deriv_z0Center_ne_zero
    linear_combination hderiv_eq.symm
  rw [← hc_omega]
  exact hc_eq z hz

theorem riemannPsi_eq_zero_iff {z : ℂ} (hz : z ∈ OpenTriangleQ0) :
    riemannPsi z = 0 ↔ z = z0Center := by
  constructor
  · intro h0
    exact riemannPsi_bij.injOn hz z0Center_mem_openTriangleQ0 (h0.trans riemannPsi_z0Center.symm)
  · rintro rfl
    exact riemannPsi_z0Center

/-- Holomorphic inverse `riemannPsiInv : ball 0 1 → Q₀` of `riemannPsi` (`10.33`). -/
def riemannPsiInv : ℂ → ℂ :=
  Classical.choose
    (RudinRCA.Chapter10.theorem10_33.1 isOpen_openTriangleQ0 riemannPsi_holo riemannPsi_bij.injOn).2.2

theorem riemannPsiInv_spec :
    RudinRCA.Chapter10.HolomorphicOn riemannPsiInv (Metric.ball (0 : ℂ) 1) ∧
    (∀ z ∈ OpenTriangleQ0, riemannPsiInv (riemannPsi z) = z) ∧
    (∀ w ∈ Metric.ball (0 : ℂ) 1, riemannPsiInv w ∈ OpenTriangleQ0 ∧ riemannPsi (riemannPsiInv w) = w) := by
  have h : RudinRCA.Chapter10.HolomorphicOn riemannPsiInv (riemannPsi '' OpenTriangleQ0) ∧
      (∀ z ∈ OpenTriangleQ0, riemannPsiInv (riemannPsi z) = z) ∧
      (∀ w ∈ riemannPsi '' OpenTriangleQ0,
        riemannPsiInv w ∈ OpenTriangleQ0 ∧ riemannPsi (riemannPsiInv w) = w) ∧
      (∀ z ∈ OpenTriangleQ0, deriv riemannPsiInv (riemannPsi z) = (deriv riemannPsi z)⁻¹) :=
    Classical.choose_spec
      (RudinRCA.Chapter10.theorem10_33.1 isOpen_openTriangleQ0 riemannPsi_holo riemannPsi_bij.injOn).2.2
  rw [riemannPsi_bij.image_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Preimage of any closed subdisc `closedBall 0 r` (`0 ≤ r < 1`) in `Q₀` is compact. -/
theorem isCompact_preimage_closedBall_riemannPsi {r : ℝ} (_hr0 : 0 ≤ r) (hr1 : r < 1) :
    IsCompact {z ∈ OpenTriangleQ0 | ‖riemannPsi z‖ ≤ r} := by
  have hsub_ball : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.closedBall_subset_ball hr1
  have hcont : ContinuousOn riemannPsiInv (Metric.closedBall (0 : ℂ) r) :=
    (RudinRCA.Chapter10.continuousOn_of_holomorphicOn riemannPsiInv_spec.1).mono hsub_ball
  have hcomp : IsCompact (riemannPsiInv '' Metric.closedBall (0 : ℂ) r) :=
    (isCompact_closedBall (0 : ℂ) r).image_of_continuousOn hcont
  have heq : riemannPsiInv '' Metric.closedBall (0 : ℂ) r =
      {z ∈ OpenTriangleQ0 | ‖riemannPsi z‖ ≤ r} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hzQ, hpsi⟩ := riemannPsiInv_spec.2.2 w (hsub_ball hw)
      exact ⟨hzQ, by rw [hpsi]; simpa [Metric.mem_closedBall] using hw⟩
    · rintro ⟨hzQ, hle⟩
      refine ⟨riemannPsi z, ?_, riemannPsiInv_spec.2.1 z hzQ⟩
      simpa [Metric.mem_closedBall] using hle
  rwa [← heq]
  -- (`hr0` keeps hypothesis symmetry; `closedBall 0 r` is compact for all `r`)

/-- As `z ∈ Q₀` approaches any point `p ∉ Q₀`, `‖ψ(z)‖ → 1`. -/
theorem tendsto_norm_riemannPsi_of_notMem {p : ℂ} (hp : p ∉ OpenTriangleQ0) :
    Tendsto (fun z => ‖riemannPsi z‖) (𝓝[OpenTriangleQ0] p) (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let r : ℝ := max 0 (1 - ε / 2)
  have hr0 : 0 ≤ r := le_max_left _ _
  have hr1 : r < 1 := max_lt zero_lt_one (by linarith)
  let K : Set ℂ := {z ∈ OpenTriangleQ0 | ‖riemannPsi z‖ ≤ r}
  have hK_comp : IsCompact K := isCompact_preimage_closedBall_riemannPsi hr0 hr1
  have hp_not_K : p ∉ K := fun hK => hp hK.1
  have hcompl_mem : Kᶜ ∈ 𝓝 p := hK_comp.isClosed.isOpen_compl.mem_nhds hp_not_K
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hcompl_mem] with z hzQ hzK
  have hlt1 : ‖riemannPsi z‖ < 1 := by
    simpa [Metric.mem_ball] using riemannPsi_bij.mapsTo hzQ
  have hgt_r : r < ‖riemannPsi z‖ := not_le.mp fun hle => hzK ⟨hzQ, hle⟩
  have hgt_eps : 1 - ε / 2 < ‖riemannPsi z‖ := lt_of_le_of_lt (le_max_right _ _) hgt_r
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- As `Im z → +∞` in `Q₀`, `‖ψ(z)‖ → 1`. -/
theorem tendsto_norm_riemannPsi_im_atTop :
    Tendsto (fun z : ℂ => ‖riemannPsi z‖)
      (Filter.comap Complex.im Filter.atTop ⊓ 𝓟 OpenTriangleQ0) (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let r : ℝ := max 0 (1 - ε / 2)
  have hr0 : 0 ≤ r := le_max_left _ _
  have hr1 : r < 1 := max_lt zero_lt_one (by linarith)
  let K : Set ℂ := {z ∈ OpenTriangleQ0 | ‖riemannPsi z‖ ≤ r}
  have hK_comp : IsCompact K := isCompact_preimage_closedBall_riemannPsi hr0 hr1
  obtain ⟨R, _, hK_sub⟩ := hK_comp.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  have hev_im : {z : ℂ | R < z.im} ∈ Filter.comap Complex.im Filter.atTop :=
    ⟨Set.Ioi R, Filter.Ioi_mem_atTop R, Subset.rfl⟩
  filter_upwards [Filter.mem_inf_of_left hev_im, Filter.mem_inf_of_right (Filter.mem_principal_self _)]
    with z hzim hzQ
  have hzK : z ∉ K := by
    intro hmem
    have hb : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall] using hK_sub hmem
    have him_le : z.im ≤ ‖z‖ := le_trans (le_abs_self z.im) (Complex.abs_im_le_norm z)
    linarith
  have hlt1 : ‖riemannPsi z‖ < 1 := by
    simpa [Metric.mem_ball] using riemannPsi_bij.mapsTo hzQ
  have hgt_r : r < ‖riemannPsi z‖ := not_le.mp fun hle => hzK ⟨hzQ, hle⟩
  have hgt_eps : 1 - ε / 2 < ‖riemannPsi z‖ := lt_of_le_of_lt (le_max_right _ _) hgt_r
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩


/-!
### Section 2: Schwarz Reflection of `ψ` Across `L₁`, Periodic Strip, and Cusp Limit `α_∞`
-/

/-- The positive imaginary axis `L₁ = {i y : y > 0}` separating `Q₀` and `Q₀⁻`. -/
def BoundaryL1 : Set ℂ :=
  {z : ℂ | z.re = 0 ∧ 0 < z.im}

/-- The open reflected left triangle `Q₀⁻ = {z : -conj z ∈ Q₀}`. -/
def ReflectedQ0 : Set ℂ :=
  {z : ℂ | 0 < z.im ∧ -1 < z.re ∧ z.re < 0 ∧ 1 < ‖2 * z + 1‖}

/-- The combined open interior `OmegaL1 = Q₀ ⊔ L₁ ⊔ Q₀⁻` of `Q` across `L₁`. -/
def OmegaL1 : Set ℂ :=
  {z : ℂ | 0 < z.im ∧ -1 < z.re ∧ z.re < 1 ∧ 1 < ‖2 * z - 1‖ ∧ 1 < ‖2 * z + 1‖}

theorem isOpen_omegaL1 : IsOpen OmegaL1 := by
  refine (isOpen_lt continuous_const Complex.continuous_im).inter ?_
  refine (isOpen_lt continuous_const Complex.continuous_re).inter ?_
  refine (isOpen_lt Complex.continuous_re continuous_const).inter ?_
  refine (isOpen_lt continuous_const
    (continuous_norm.comp ((continuous_const.mul continuous_id).sub continuous_const))).inter ?_
  exact isOpen_lt continuous_const
    (continuous_norm.comp ((continuous_const.mul continuous_id).add continuous_const))

theorem isOpen_reflectedQ0 : IsOpen ReflectedQ0 := by
  refine (isOpen_lt continuous_const Complex.continuous_im).inter ?_
  refine (isOpen_lt continuous_const Complex.continuous_re).inter ?_
  refine (isOpen_lt Complex.continuous_re continuous_const).inter ?_
  exact isOpen_lt continuous_const
    (continuous_norm.comp ((continuous_const.mul continuous_id).add continuous_const))

theorem omegaL1_subset_fundamentalSetQ : OmegaL1 ⊆ FundamentalSetQ := by
  rintro z ⟨him, hre_gt, hre_lt, h1, h2⟩
  exact ⟨him, hre_gt.le, hre_lt, h2.le, h1⟩

theorem openTriangleQ0_subset_omegaL1 : OpenTriangleQ0 ⊆ OmegaL1 := by
  rintro z ⟨him, hre0, hre1, h1⟩
  refine ⟨him, by linarith, hre1, h1, ?_⟩
  have hsq := norm_two_mul_add_one_sq z
  have hgt : 1 < ‖2 * z + 1‖ ^ 2 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  nlinarith [norm_nonneg (2 * z + 1)]

theorem boundaryL1_subset_omegaL1 : BoundaryL1 ⊆ OmegaL1 := by
  rintro z ⟨hre0, him⟩
  refine ⟨him, by linarith, by linarith, ?_, ?_⟩
  · rw [one_lt_norm_two_mul_sub_one_iff, hre0]; nlinarith
  · have hsq := norm_two_mul_add_one_sq z
    rw [hre0] at hsq
    have hgt : 1 < ‖2 * z + 1‖ ^ 2 := by nlinarith
    nlinarith [norm_nonneg (2 * z + 1)]

theorem reflectedQ0_subset_omegaL1 : ReflectedQ0 ⊆ OmegaL1 := by
  rintro z ⟨him, hre_gt, hre_lt, h2⟩
  refine ⟨him, hre_gt, by linarith, ?_, h2⟩
  rw [one_lt_norm_two_mul_sub_one_iff]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

theorem neg_conj_mem_openTriangleQ0_iff {z : ℂ} :
    -starRingEnd ℂ z ∈ OpenTriangleQ0 ↔ z ∈ ReflectedQ0 := by
  have hnorm_eq : ‖2 * (-starRingEnd ℂ z) - 1‖ = ‖2 * z + 1‖ := by
    have h1 : 2 * (-starRingEnd ℂ z) - 1 = -starRingEnd ℂ (2 * z + 1) := by
      apply Complex.ext <;> (simp; try ring)
    rw [h1, norm_neg, Complex.norm_conj]
  change (0 < (-starRingEnd ℂ z).im ∧ 0 < (-starRingEnd ℂ z).re ∧
      (-starRingEnd ℂ z).re < 1 ∧ 1 < ‖2 * (-starRingEnd ℂ z) - 1‖) ↔
    (0 < z.im ∧ -1 < z.re ∧ z.re < 0 ∧ 1 < ‖2 * z + 1‖)
  simp only [Complex.neg_re, Complex.conj_re, Complex.neg_im, Complex.conj_im, neg_neg, hnorm_eq]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h1, by linarith, by linarith, h4⟩

/-- Reflection derivative rule: if `f` has complex derivative `f'` at `-conj z₀`, then
`z ↦ conj (f (-conj z))` has complex derivative `-conj f'` at `z₀`. -/
theorem hasDerivAt_conj_comp_neg_conj {f : ℂ → ℂ} {f' z₀ : ℂ}
    (hf : HasDerivAt f f' (-starRingEnd ℂ z₀)) :
    HasDerivAt (fun z : ℂ => starRingEnd ℂ (f (-starRingEnd ℂ z))) (-starRingEnd ℂ f') z₀ := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hf ⊢
  have hcont : Tendsto (fun h : ℂ => -starRingEnd ℂ h) (𝓝 0) (𝓝 0) := by
    simpa [Function.comp_def] using (continuous_neg.comp Complex.continuous_conj).tendsto (0 : ℂ)
  have hcomp := hf.comp_tendsto hcont
  have h1 : (fun h : ℂ => starRingEnd ℂ
        (f (-starRingEnd ℂ z₀ + -starRingEnd ℂ h) - f (-starRingEnd ℂ z₀) -
          (-starRingEnd ℂ h) • f')) =o[𝓝 0] (fun h : ℂ => -starRingEnd ℂ h) :=
    (Complex.conjCLE.toContinuousLinearMap.isBigO_comp _ _).trans_isLittleO hcomp
  have h2 : (fun h : ℂ => -starRingEnd ℂ h) =O[𝓝 0] (fun h : ℂ => h) :=
    Asymptotics.isBigO_iff.mpr ⟨1, Filter.Eventually.of_forall fun h => by simp⟩
  refine (h1.trans_isBigO h2).congr' ?_ Filter.EventuallyEq.rfl
  refine Filter.Eventually.of_forall fun h => ?_
  simp only [smul_eq_mul, map_sub, map_mul, map_neg, RingHomCompTriple.comp_apply,
    RingHom.id_apply, map_add]
  ring_nf

theorem differentiableAt_conj_comp_neg_conj {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : DifferentiableAt ℂ f (-starRingEnd ℂ z₀)) :
    DifferentiableAt ℂ (fun z : ℂ => starRingEnd ℂ (f (-starRingEnd ℂ z))) z₀ :=
  (hasDerivAt_conj_comp_neg_conj hf.hasDerivAt).differentiableAt

/-- Schwarz reflection of `riemannPsi` across `L₁` onto `OmegaL1 = Q₀ ⊔ L₁ ⊔ Q₀⁻`. -/
def psiExtL1 (z : ℂ) : ℂ :=
  if 0 < z.re then
    riemannPsi z
  else if z.re = 0 then
    limUnder (𝓝[OpenTriangleQ0] z) riemannPsi
  else
    (starRingEnd ℂ (riemannPsi (-starRingEnd ℂ z)))⁻¹

theorem psiExtL1_of_re_pos {z : ℂ} (hz : 0 < z.re) : psiExtL1 z = riemannPsi z := by
  simp [psiExtL1, hz]

theorem psiExtL1_of_re_neg {z : ℂ} (hz : z.re < 0) :
    psiExtL1 z = (starRingEnd ℂ (riemannPsi (-starRingEnd ℂ z)))⁻¹ := by
  have h1 : ¬ 0 < z.re := not_lt.mpr hz.le
  have h2 : z.re ≠ 0 := hz.ne
  simp [psiExtL1, h1, h2]

/-- Local Schwarz reflection of `riemannPsi` on any small ball centered at `p₁ ∈ L₁`. -/
theorem exists_local_holo_psiExtL1 {p₁ : ℂ} (hp₁ : p₁ ∈ BoundaryL1) :
    ∃ δ > 0, Metric.ball p₁ δ ⊆ OmegaL1 \ {z0Center, -starRingEnd ℂ z0Center} ∧
      DifferentiableOn ℂ psiExtL1 (Metric.ball p₁ δ) ∧
      ∀ z ∈ Metric.ball p₁ δ, z.re = 0 → ‖psiExtL1 z‖ = 1 := by
  have hp₁_om : p₁ ∈ OmegaL1 := boundaryL1_subset_omegaL1 hp₁
  have hp₁_ne1 : p₁ ≠ z0Center := by
    intro h; have := congrArg Complex.re h; simp [hp₁.1] at this
  have hp₁_ne2 : p₁ ≠ -starRingEnd ℂ z0Center := by
    intro h; have := congrArg Complex.re h; simp [hp₁.1] at this
  have hopen_target : IsOpen (OmegaL1 \ {z0Center, -starRingEnd ℂ z0Center}) :=
    isOpen_omegaL1.sdiff (isClosed_singleton.union isClosed_singleton)
  obtain ⟨δ, hδ_pos, hball_sub⟩ :=
    Metric.isOpen_iff.mp hopen_target p₁ ⟨hp₁_om, by simp [hp₁_ne1, hp₁_ne2]⟩
  let rot : ℂ → ℂ := fun w => p₁ - Complex.I * w
  have hrot_re : ∀ w : ℂ, (rot w).re = w.im := by
    intro w; simp [rot, hp₁.1]
  have hrot_ball : ∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) δ ↔ rot w ∈ Metric.ball p₁ δ := by
    intro w
    simp [rot, Metric.mem_ball, dist_eq_norm]
  let Upos : Set ℂ := {w ∈ Metric.ball (0 : ℂ) δ | 0 < w.im}
  have hUpos_open : IsOpen Upos :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hUpos_conv : Convex ℝ Upos :=
    (convex_ball (0 : ℂ) δ).inter (convex_halfSpace_gt Complex.imLm.isLinear 0)
  have hUpos_ne : Upos.Nonempty := by
    refine ⟨((δ / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · simp only [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one, abs_of_pos (half_pos hδ_pos)]
      exact half_lt_self hδ_pos
    · simp [half_pos hδ_pos]
  have hUpos_reg : RudinRCA.Chapter10.IsRegion Upos := ⟨hUpos_open, ⟨hUpos_ne, hUpos_conv.isPreconnected⟩⟩
  have hUpos_sc : RudinRCA.Chapter10.BookSimplyConnected Upos :=
    RudinRCA.Chapter10.theorem10_38 hUpos_reg hUpos_conv
  have hrot_Upos : ∀ w ∈ Upos, rot w ∈ OpenTriangleQ0 ∧ rot w ≠ z0Center := by
    intro w ⟨hw_ball, hw_im⟩
    obtain ⟨h_om, h_not⟩ := hball_sub ((hrot_ball w).mp hw_ball)
    have hre_pos : 0 < (rot w).re := by rwa [hrot_re]
    exact ⟨⟨h_om.1, hre_pos, h_om.2.2.1, h_om.2.2.2.1⟩, fun h => h_not (Or.inl h)⟩
  have hcomp_holo : RudinRCA.Chapter10.HolomorphicOn (fun w => riemannPsi (rot w)) Upos := by
    intro w hw
    exact (riemannPsi_holo (rot w) (hrot_Upos w hw).1).comp w
      (differentiableAt_const p₁ |>.sub (differentiableAt_id.const_mul Complex.I))
  have hcomp_nz : ∀ w ∈ Upos, riemannPsi (rot w) ≠ 0 := by
    intro w hw h0
    exact (hrot_Upos w hw).2 ((riemannPsi_eq_zero_iff (hrot_Upos w hw).1).mp h0)
  have h13 := RudinRCA.Chapter13.theorem13_11 hUpos_reg
  have hbh := (h13.2.2.1.trans (h13.2.2.2.1.trans (h13.2.2.2.2.1.trans
    (h13.2.2.2.2.2.1.trans (h13.2.2.2.2.2.2.1.trans h13.2.2.2.2.2.2.2.1))))).mp
  obtain ⟨g, hg_holo, hg_exp⟩ := hbh hUpos_sc _ hcomp_holo hcomp_nz
  let f : ℂ → ℂ := fun w => Complex.I * g w
  have hf_diff : DifferentiableOn ℂ f {w ∈ Metric.ball (0 : ℂ) δ | 0 < w.im} :=
    fun w hw => ((hg_holo w hw).const_mul Complex.I).differentiableWithinAt
  have hf_im : ∀ x ∈ Metric.ball (0 : ℂ) δ, x.im = 0 →
      Tendsto (fun w => (f w).im) (𝓝[Upos] x) (𝓝 0) := by
    intro x hx_ball hx_im
    have hrotx_re : (rot x).re = 0 := by rw [hrot_re, hx_im]
    have hrotx_notQ : rot x ∉ OpenTriangleQ0 := fun hQ => by linarith [hQ.2.1, hrotx_re]
    have hrot_tend : Tendsto rot (𝓝[Upos] x) (𝓝[OpenTriangleQ0] (rot x)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within rot
        ((continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact (hrot_Upos w hw).1
    have hnorm_tend : Tendsto (fun w => ‖riemannPsi (rot w)‖) (𝓝[Upos] x) (𝓝 1) :=
      (tendsto_norm_riemannPsi_of_notMem hrotx_notQ).comp hrot_tend
    have hlog_tend : Tendsto (fun w => Real.log ‖riemannPsi (rot w)‖) (𝓝[Upos] x) (𝓝 0) := by
      simpa [Function.comp_def] using (Real.continuousAt_log one_ne_zero).tendsto.comp hnorm_tend
    refine hlog_tend.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hexp := hg_exp w hw
    have hlog : Real.log ‖riemannPsi (rot w)‖ = (g w).re := by
      rw [← hexp, Complex.norm_exp, Real.log_exp]
    simp [f, hlog]
  have hball_symm : ∀ w ∈ Metric.ball (0 : ℂ) δ, starRingEnd ℂ w ∈ Metric.ball (0 : ℂ) δ := by
    intro w hw
    simpa [Metric.mem_ball, dist_zero_right] using hw
  have h11 := RudinRCA.Chapter11.theorem11_14 Metric.isOpen_ball hball_symm hf_diff hf_im
  let F : ℂ → ℂ := RudinRCA.Chapter11.schwarzReflection f (Metric.ball (0 : ℂ) δ)
  have hF_diff : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) δ) := h11.1
  let invRot : ℂ → ℂ := fun z => Complex.I * (z - p₁)
  have hinvRot_ball : ∀ z ∈ Metric.ball p₁ δ, invRot z ∈ Metric.ball (0 : ℂ) δ := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    simp [invRot, hz]
  have hrot_inv : ∀ z : ℂ, rot (invRot z) = z := by
    intro z; dsimp [rot, invRot]; ring_nf; simp [Complex.I_sq]
  have hinvRot_im : ∀ z : ℂ, (invRot z).im = z.re := by
    intro z; simp [invRot, hp₁.1]
  let Ψloc : ℂ → ℂ := fun z => Complex.exp (-Complex.I * F (invRot z))
  have hΨloc_diff : DifferentiableOn ℂ Ψloc (Metric.ball p₁ δ) := by
    have hinner : DifferentiableOn ℂ (fun z => F (invRot z)) (Metric.ball p₁ δ) :=
      hF_diff.comp ((differentiable_id.sub_const p₁).const_mul Complex.I).differentiableOn hinvRot_ball
    exact Complex.differentiable_exp.comp_differentiableOn (hinner.const_mul (-Complex.I))
  have hΨloc_pos : ∀ z ∈ Metric.ball p₁ δ, 0 < z.re → Ψloc z = riemannPsi z := by
    intro z hz hre
    have hw : invRot z ∈ Upos := ⟨hinvRot_ball z hz, by rwa [hinvRot_im]⟩
    have hFw : F (invRot z) = f (invRot z) := h11.2.1 (invRot z) hw
    dsimp [Ψloc]
    rw [hFw]
    have hmul : -Complex.I * f (invRot z) = g (invRot z) := by
      dsimp [f]; ring_nf; simp [Complex.I_sq]
    rw [hmul, hg_exp (invRot z) hw, hrot_inv]
  have hΨloc_neg : ∀ z ∈ Metric.ball p₁ δ, z.re < 0 →
      Ψloc z = (starRingEnd ℂ (riemannPsi (-starRingEnd ℂ z)))⁻¹ := by
    intro z hz hre
    have hw_neg : invRot z ∈ {w ∈ Metric.ball (0 : ℂ) δ | w.im < 0} :=
      ⟨hinvRot_ball z hz, by rwa [hinvRot_im]⟩
    have hFw : F (invRot z) = starRingEnd ℂ (f (starRingEnd ℂ (invRot z))) :=
      h11.2.2.1 (invRot z) hw_neg
    have hcw : starRingEnd ℂ (invRot z) ∈ Upos := by
      refine ⟨hball_symm _ hw_neg.1, ?_⟩
      simp [hinvRot_im, hre]
    have hrot_conj : rot (starRingEnd ℂ (invRot z)) = -starRingEnd ℂ z := by
      have hp₁_eq : p₁ = (p₁.im : ℂ) * Complex.I := by
        conv_lhs => rw [← Complex.re_add_im p₁, hp₁.1]
        simp
      dsimp [rot, invRot]
      rw [hp₁_eq]
      apply Complex.ext <;> (simp; try ring)
    dsimp [Ψloc]
    rw [hFw]
    have hmul : -Complex.I * starRingEnd ℂ (f (starRingEnd ℂ (invRot z))) =
        -starRingEnd ℂ (g (starRingEnd ℂ (invRot z))) := by
      dsimp [f]
      simp only [map_mul, Complex.conj_I]
      ring_nf
      simp [Complex.I_sq]
    rw [hmul, Complex.exp_neg, Complex.exp_conj, hg_exp _ hcw, hrot_conj]
  have hΨloc_zero : ∀ z ∈ Metric.ball p₁ δ, z.re = 0 →
      Ψloc z = limUnder (𝓝[OpenTriangleQ0] z) riemannPsi ∧ ‖Ψloc z‖ = 1 := by
    intro z hz hre
    have hw0 : invRot z ∈ {w ∈ Metric.ball (0 : ℂ) δ | w.im = 0} :=
      ⟨hinvRot_ball z hz, by rwa [hinvRot_im]⟩
    have hFim : (F (invRot z)).im = 0 := h11.2.2.2.1 (invRot z) hw0
    have hnorm1 : ‖Ψloc z‖ = 1 := by
      dsimp [Ψloc]
      rw [Complex.norm_exp]
      have hre0 : (-Complex.I * F (invRot z)).re = 0 := by simp [hFim]
      rw [hre0, Real.exp_zero]
    -- Show `𝓝[OpenTriangleQ0] z` is `NeBot` via `z + (t : ℂ)` for small `t > 0`
    obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball z hz
    have hnebot : (𝓝[OpenTriangleQ0] z).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
      intro ε hε
      let t : ℝ := min (ρ / 2) (ε / 2)
      have ht_pos : 0 < t := lt_min (half_pos hρ_pos) (half_pos hε)
      have ht_ball : z + (t : ℂ) ∈ Metric.ball p₁ δ := by
        apply hρ_sub
        rw [Metric.mem_ball, dist_eq_norm]
        simp [abs_of_pos ht_pos]
        exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ_pos)
      have ht_om : z + (t : ℂ) ∈ OmegaL1 := (hball_sub ht_ball).1
      have ht_Q0 : z + (t : ℂ) ∈ OpenTriangleQ0 :=
        ⟨ht_om.1, by simp [hre, ht_pos], ht_om.2.2.1, ht_om.2.2.2.1⟩
      refine ⟨z + (t : ℂ), ht_Q0, ?_⟩
      rw [dist_eq_norm]
      have hdiff : z - (z + (t : ℂ)) = -(t : ℂ) := by ring
      rw [hdiff, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
      exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε)
    have hΨ_cont : ContinuousAt Ψloc z :=
      hΨloc_diff.differentiableAt (Metric.ball_mem_nhds p₁ hδ_pos |> fun _ =>
        Metric.isOpen_ball.mem_nhds hz) |>.continuousAt
    have htend : Tendsto riemannPsi (𝓝[OpenTriangleQ0] z) (𝓝 (Ψloc z)) := by
      refine (hΨ_cont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hz)] with w hwQ hwB
      exact hΨloc_pos w hwB hwQ.2.1
    exact ⟨(htend.limUnder_eq).symm, hnorm1⟩
  have heq : Set.EqOn psiExtL1 Ψloc (Metric.ball p₁ δ) := by
    intro z hz
    by_cases hpos : 0 < z.re
    · rw [psiExtL1_of_re_pos hpos, hΨloc_pos z hz hpos]
    · by_cases hzero : z.re = 0
      · simp [psiExtL1, hzero, (hΨloc_zero z hz hzero).1]
      · have hneg : z.re < 0 := lt_of_le_of_ne (not_lt.mp hpos) hzero
        rw [psiExtL1_of_re_neg hneg, hΨloc_neg z hz hneg]
  exact ⟨δ, hδ_pos, hball_sub, hΨloc_diff.congr heq, fun z hz hre => by
    rw [heq hz]; exact (hΨloc_zero z hz hre).2⟩

theorem psiExtL1_holo_off_neg_conj_z0 :
    RudinRCA.Chapter10.HolomorphicOn psiExtL1 (OmegaL1 \ {-starRingEnd ℂ z0Center}) := by
  rintro z ⟨hz_om, hz_ne⟩
  by_cases hpos : 0 < z.re
  · have hzQ : z ∈ OpenTriangleQ0 := ⟨hz_om.1, hpos, hz_om.2.2.1, hz_om.2.2.2.1⟩
    refine (riemannPsi_holo z hzQ).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_openTriangleQ0.mem_nhds hzQ] with w hw
    exact psiExtL1_of_re_pos hw.2.1
  · by_cases hzero : z.re = 0
    · obtain ⟨δ, hδ_pos, _, hdiff, _⟩ := exists_local_holo_psiExtL1 (p₁ := z) ⟨hzero, hz_om.1⟩
      exact hdiff.differentiableAt (Metric.ball_mem_nhds z hδ_pos)
    · have hneg : z.re < 0 := lt_of_le_of_ne (not_lt.mp hpos) hzero
      have hzR : z ∈ ReflectedQ0 := ⟨hz_om.1, hz_om.2.1, hneg, hz_om.2.2.2.2⟩
      have hwQ : -starRingEnd ℂ z ∈ OpenTriangleQ0 := neg_conj_mem_openTriangleQ0_iff.mpr hzR
      have hw_ne : -starRingEnd ℂ z ≠ z0Center := by
        intro h
        apply hz_ne
        rw [Set.mem_singleton_iff]
        have := congrArg (fun u => -starRingEnd ℂ u) h
        simpa using this
      have hpsi_nz : riemannPsi (-starRingEnd ℂ z) ≠ 0 :=
        fun h0 => hw_ne ((riemannPsi_eq_zero_iff hwQ).mp h0)
      have hd_refl : DifferentiableAt ℂ
          (fun w : ℂ => (starRingEnd ℂ (riemannPsi (-starRingEnd ℂ w)))⁻¹) z :=
        (differentiableAt_conj_comp_neg_conj (riemannPsi_holo _ hwQ)).inv
          (by simpa using hpsi_nz)
      refine hd_refl.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_reflectedQ0.mem_nhds hzR] with w hw
      exact psiExtL1_of_re_neg hw.2.2.1

theorem norm_psiExtL1_boundaryL1 {z : ℂ} (hz : z ∈ BoundaryL1) : ‖psiExtL1 z‖ = 1 := by
  obtain ⟨δ, hδ_pos, _, _, hnorm⟩ := exists_local_holo_psiExtL1 hz
  exact hnorm z (Metric.mem_ball_self hδ_pos) hz.1

theorem one_lt_norm_psiExtL1_reflectedQ0 {z : ℂ} (hz : z ∈ ReflectedQ0)
    (hne : z ≠ -starRingEnd ℂ z0Center) : 1 < ‖psiExtL1 z‖ := by
  rw [psiExtL1_of_re_neg hz.2.2.1, norm_inv, Complex.norm_conj]
  have hwQ : -starRingEnd ℂ z ∈ OpenTriangleQ0 := neg_conj_mem_openTriangleQ0_iff.mpr hz
  have hw_ne : -starRingEnd ℂ z ≠ z0Center := by
    intro h; apply hne
    have := congrArg (fun u => -starRingEnd ℂ u) h
    simpa using this
  have hnz : 0 < ‖riemannPsi (-starRingEnd ℂ z)‖ :=
    norm_pos_iff.mpr fun h0 => hw_ne ((riemannPsi_eq_zero_iff hwQ).mp h0)
  have hlt1 : ‖riemannPsi (-starRingEnd ℂ z)‖ < 1 := by
    simpa [Metric.mem_ball] using riemannPsi_bij.mapsTo hwQ
  exact one_lt_inv_iff₀.mpr ⟨hnz, hlt1⟩

/-- Cutoff height `Y₀ ≥ 1` above which `{z ∈ Q₀ : Im z > Y₀}` avoids `ψ⁻¹(closedBall 0 (1/2))`. -/
def stripHeightY0 : ℝ :=
  max 1 (Classical.choose
    ((isCompact_preimage_closedBall_riemannPsi (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).isBounded.subset_closedBall_lt 0 (0 : ℂ)))

theorem one_le_stripHeightY0 : 1 ≤ stripHeightY0 :=
  le_max_left _ _

theorem half_lt_norm_riemannPsi_above_Y0 {z : ℂ} (hz : z ∈ OpenTriangleQ0)
    (him : stripHeightY0 < z.im) : 1 / 2 < ‖riemannPsi z‖ := by
  let K : Set ℂ := {w ∈ OpenTriangleQ0 | ‖riemannPsi w‖ ≤ 1 / 2}
  have hspec := Classical.choose_spec
    ((isCompact_preimage_closedBall_riemannPsi (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).isBounded.subset_closedBall_lt 0 (0 : ℂ))
  by_contra hle
  have hzK : z ∈ K := ⟨hz, not_lt.mp hle⟩
  have hball : ‖z‖ ≤ Classical.choose
      ((isCompact_preimage_closedBall_riemannPsi (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).isBounded.subset_closedBall_lt 0 (0 : ℂ)) := by
    simpa [Metric.mem_closedBall] using hspec.2 hzK
  have him_le : z.im ≤ ‖z‖ := le_trans (le_abs_self z.im) (Complex.abs_im_le_norm z)
  have hY_le : Classical.choose
      ((isCompact_preimage_closedBall_riemannPsi (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).isBounded.subset_closedBall_lt 0 (0 : ℂ)) ≤ stripHeightY0 :=
    le_max_right _ _
  linarith

theorem mem_omegaL1_of_im_gt_Y0 {z : ℂ} (him : stripHeightY0 < z.im)
    (hre_gt : -1 < z.re) (hre_lt : z.re < 1) :
    z ∈ OmegaL1 \ {z0Center, -starRingEnd ℂ z0Center} := by
  have him1 : 1 < z.im := lt_of_le_of_lt one_le_stripHeightY0 him
  have hsqrt3 : Real.sqrt 3 / 2 < 1 := by
    have hlt2 : Real.sqrt 3 < 2 := by
      have h4 : (2 : ℝ) = Real.sqrt 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [h4]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  refine ⟨⟨by linarith, hre_gt, hre_lt, ?_, ?_⟩, ?_⟩
  · rw [one_lt_norm_two_mul_sub_one_iff]; nlinarith [sq_nonneg z.re]
  · have hsq := norm_two_mul_add_one_sq z
    have hgt : 1 < ‖2 * z + 1‖ ^ 2 := by nlinarith [sq_nonneg z.re]
    nlinarith [norm_nonneg (2 * z + 1)]
  · rintro (rfl | rfl)
    · rw [z0Center_im] at him1; linarith
    · simp only [Complex.neg_im, Complex.conj_im, z0Center_im] at him1; linarith

/-- 2-periodic extension `psiStrip` of `riemannPsi` on `{z : Im z > Y₀}`. -/
def psiStrip (z : ℂ) : ℂ :=
  let k : ℤ := Int.floor ((z.re + 1) / 2)
  let zRed : ℂ := z - 2 * (k : ℂ)
  if zRed.re = -1 then
    omegaCube * psiExtL1 (1 / (1 - (zRed + 2)))
  else
    psiExtL1 zRed

theorem psiStrip_periodic_two (z : ℂ) (m : ℤ) :
    psiStrip (z + 2 * (m : ℂ)) = psiStrip z := by
  have hre : (z + 2 * (m : ℂ)).re = z.re + 2 * (m : ℝ) := by simp
  have hdiv : ((z + 2 * (m : ℂ)).re + 1) / 2 = (z.re + 1) / 2 + (m : ℝ) := by
    rw [hre]; ring
  have hfl : Int.floor (((z + 2 * (m : ℂ)).re + 1) / 2) =
      Int.floor ((z.re + 1) / 2) + m := by
    rw [hdiv, Int.floor_add_intCast]
  have hred : (z + 2 * (m : ℂ)) - 2 * ((Int.floor (((z + 2 * (m : ℂ)).re + 1) / 2) : ℤ) : ℂ) =
      z - 2 * ((Int.floor ((z.re + 1) / 2) : ℤ) : ℂ) := by
    rw [hfl]; push_cast; ring
  unfold psiStrip
  dsimp only
  rw [hred]

theorem psiStrip_eq_psiExtL1 {z : ℂ} (hgt : -1 < z.re) (hlt : z.re < 1) :
    psiStrip z = psiExtL1 z := by
  have hfl : Int.floor ((z.re + 1) / 2) = 0 := by
    refine Int.floor_eq_iff.mpr ⟨by linarith, by norm_num; linarith⟩
  unfold psiStrip
  simp only [hfl, Int.cast_zero, mul_zero, sub_zero]
  have hne : z.re ≠ -1 := hgt.ne'
  simp [hne]

theorem psiStrip_eq_riemannPsi {z : ℂ} (hz : z ∈ OpenTriangleQ0) :
    psiStrip z = riemannPsi z := by
  rw [psiStrip_eq_psiExtL1 (by linarith [hz.2.1]) hz.2.2.1, psiExtL1_of_re_pos hz.2.1]

theorem norm_psiStrip_le_two {z : ℂ} (him : stripHeightY0 < z.im) :
    ‖psiStrip z‖ ≤ 2 := by
  let k : ℤ := Int.floor ((z.re + 1) / 2)
  let zRed : ℂ := z - 2 * (k : ℂ)
  have hzRed_im : zRed.im = z.im := by simp [zRed]
  have hfl_le : (k : ℝ) ≤ (z.re + 1) / 2 := Int.floor_le _
  have hfl_lt : (z.re + 1) / 2 < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hzRed_re_ge : -1 ≤ zRed.re := by simp [zRed]; linarith
  have hzRed_re_lt : zRed.re < 1 := by simp [zRed]; linarith
  unfold psiStrip
  dsimp only
  split_ifs with h_neg1
  · have hzRed_neg1 : zRed.re = -1 := h_neg1
    have hz2 : zRed + 2 = 1 + (z.im : ℂ) * Complex.I :=
      Complex.ext (by simp [hzRed_neg1]; norm_num) (by simp [hzRed_im])
    have hw : 1 / (1 - (zRed + 2)) = ((1 / z.im : ℝ) : ℂ) * Complex.I := by
      rw [hz2]
      have him_ne : (z.im : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (lt_trans zero_lt_one (lt_of_le_of_lt one_le_stripHeightY0 him)).ne'
      have h1 : 1 - (1 + (z.im : ℂ) * Complex.I) = -(z.im : ℂ) * Complex.I := by ring
      rw [h1, Complex.ofReal_div, Complex.ofReal_one]
      field_simp [him_ne, Complex.I_ne_zero]
      ring_nf
      simp [Complex.I_sq]
    have hw_L1 : ((1 / z.im : ℝ) : ℂ) * Complex.I ∈ BoundaryL1 := by
      refine ⟨by simp, ?_⟩
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
      exact one_div_pos.mpr (lt_trans zero_lt_one (lt_of_le_of_lt one_le_stripHeightY0 him))
    rw [hw, norm_mul, norm_omegaCube, norm_psiExtL1_boundaryL1 hw_L1]
    norm_num
  · have hzRed_gt : -1 < zRed.re := lt_of_le_of_ne hzRed_re_ge (Ne.symm h_neg1)
    have hmem := mem_omegaL1_of_im_gt_Y0 (hzRed_im ▸ him) hzRed_gt hzRed_re_lt
    by_cases hpos : 0 < zRed.re
    · have hQ : zRed ∈ OpenTriangleQ0 := ⟨hmem.1.1, hpos, hmem.1.2.2.1, hmem.1.2.2.2.1⟩
      rw [psiExtL1_of_re_pos hpos]
      have hlt1 : ‖riemannPsi zRed‖ < 1 := by simpa [Metric.mem_ball] using riemannPsi_bij.mapsTo hQ
      linarith
    · by_cases hzero : zRed.re = 0
      · rw [norm_psiExtL1_boundaryL1 ⟨hzero, hmem.1.1⟩]
        norm_num
      · have hneg : zRed.re < 0 := lt_of_le_of_ne (not_lt.mp hpos) hzero
        rw [psiExtL1_of_re_neg hneg, norm_inv, Complex.norm_conj]
        have hR : zRed ∈ ReflectedQ0 := ⟨hmem.1.1, hzRed_gt, hneg, hmem.1.2.2.2.2⟩
        have hwQ : -starRingEnd ℂ zRed ∈ OpenTriangleQ0 := neg_conj_mem_openTriangleQ0_iff.mpr hR
        have hw_im : stripHeightY0 < (-starRingEnd ℂ zRed).im := by simp [hzRed_im, him]
        have hgt_half : 1 / 2 < ‖riemannPsi (-starRingEnd ℂ zRed)‖ :=
          half_lt_norm_riemannPsi_above_Y0 hwQ hw_im
        exact (inv_le_comm₀ (by linarith) (by norm_num)).mpr (by linarith)

/-- `psiStrip` is holomorphic throughout `{z : Im z > Y₀}`, agreeing near `Re z = 2k + 1`
with `z ↦ ω · psiExtL1 (1 / (1 - (z - 2k)))`. -/
theorem psiStrip_holo :
    RudinRCA.Chapter10.HolomorphicOn psiStrip {z : ℂ | stripHeightY0 < z.im} := by
  intro z₀ hz₀
  change stripHeightY0 < z₀.im at hz₀
  let k₀ : ℤ := Int.floor ((z₀.re + 1) / 2)
  let zRed₀ : ℂ := z₀ - 2 * (k₀ : ℂ)
  have hzRed₀_im : zRed₀.im = z₀.im := by simp [zRed₀]
  have hzRed₀_ge : -1 ≤ zRed₀.re := by
    simp [zRed₀]; linarith [Int.floor_le ((z₀.re + 1) / 2)]
  have hzRed₀_lt : zRed₀.re < 1 := by
    simp [zRed₀]; linarith [Int.lt_floor_add_one ((z₀.re + 1) / 2)]
  by_cases h_neg1 : zRed₀.re = -1
  · -- Reduce by `2`-periodicity to `z₁ = zRed₀ + 2 = 1 + i z₀.im`
    let z₁ : ℂ := zRed₀ + 2
    have hz₁_eq : z₁ = z₀ + 2 * ((1 - k₀ : ℤ) : ℂ) := by
      dsimp [z₁, zRed₀]; push_cast; ring
    have hz₁_re : z₁.re = 1 := by simp [z₁, h_neg1]; norm_num
    have hz₁_im : z₁.im = z₀.im := by simp [z₁, hzRed₀_im]
    have hz₀_pos : 0 < z₀.im := lt_trans zero_lt_one (lt_of_le_of_lt one_le_stripHeightY0 hz₀)
    let wMap : ℂ → ℂ := fun z => 1 / (1 - z)
    have hwMap_z₁ : wMap z₁ = ((1 / z₀.im : ℝ) : ℂ) * Complex.I := by
      have hz₁_val : z₁ = 1 + (z₀.im : ℂ) * Complex.I :=
        Complex.ext (by simp [hz₁_re]) (by simp [hz₁_im])
      dsimp [wMap]
      rw [hz₁_val]
      have him_ne : (z₀.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz₀_pos.ne'
      have h1 : 1 - (1 + (z₀.im : ℂ) * Complex.I) = -(z₀.im : ℂ) * Complex.I := by ring
      rw [h1, Complex.ofReal_div, Complex.ofReal_one]
      field_simp [him_ne, Complex.I_ne_zero]
      ring_nf
      simp [Complex.I_sq]
    have hw_z₁_mem : wMap z₁ ∈ OmegaL1 \ {-starRingEnd ℂ z0Center} := by
      rw [hwMap_z₁]
      refine ⟨boundaryL1_subset_omegaL1 ⟨by simp, by simp; exact hz₀_pos⟩, ?_⟩
      intro h
      have := congrArg Complex.re h
      simp at this
    have hwMap_diff_z₁ : DifferentiableAt ℂ wMap z₁ := by
      refine differentiableAt_const 1 |>.div (differentiableAt_const 1 |>.sub differentiableAt_id) ?_
      intro h0
      have him := congrArg Complex.im h0
      simp [hz₁_im, hz₀_pos.ne'] at him
    have hcomp_z₁ : DifferentiableAt ℂ (fun z => omegaCube * psiExtL1 (wMap z)) z₁ :=
      ((psiExtL1_holo_off_neg_conj_z0 (wMap z₁) hw_z₁_mem).comp z₁ hwMap_diff_z₁).const_mul omegaCube
    -- Show `psiStrip =ᶠ[𝓝 z₁] fun z => omegaCube * psiExtL1 (wMap z)`
    have hopen_V : IsOpen {z : ℂ | stripHeightY0 < z.im ∧ 1 / 2 < z.re ∧ z.re < 3 / 2} :=
      (isOpen_lt continuous_const Complex.continuous_im).inter
        ((isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const))
    have hz₁_V : z₁ ∈ {z : ℂ | stripHeightY0 < z.im ∧ 1 / 2 < z.re ∧ z.re < 3 / 2} :=
      ⟨hz₁_im ▸ hz₀, by rw [hz₁_re]; norm_num, by rw [hz₁_re]; norm_num⟩
    have hev_z₁ : psiStrip =ᶠ[𝓝 z₁] (fun z => omegaCube * psiExtL1 (wMap z)) := by
      filter_upwards [hopen_V.mem_nhds hz₁_V] with z ⟨hz_im, hz_gt, hz_lt⟩
      by_cases hlt1 : z.re < 1
      · have hzQ : z ∈ OpenTriangleQ0 := by
          have hm := (mem_omegaL1_of_im_gt_Y0 hz_im (by linarith) hlt1).1
          exact ⟨hm.1, by linarith, hlt1, hm.2.2.2.1⟩
        have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz_gt; norm_num at hz_gt
        have hz1 : z ≠ 1 := fun h => by rw [h, Complex.one_re] at hlt1; exact lt_irrefl 1 hlt1
        have hw_eq : wMap z = moebiusM3 (moebiusM3 z) := (moebiusM3_iter2 hz0 hz1).symm
        have hwQ : wMap z ∈ OpenTriangleQ0 :=
          hw_eq ▸ moebiusM3_mapsTo_openTriangleQ0 (moebiusM3_mapsTo_openTriangleQ0 hzQ)
        have hM3w : moebiusM3 (wMap z) = z := by
          rw [hw_eq]; exact moebiusM3_iter3 hz0 hz1
        rw [psiStrip_eq_riemannPsi hzQ, psiExtL1_of_re_pos hwQ.2.1,
          ← riemannPsi_moebiusM3 hwQ, hM3w]
      · by_cases heq1 : z.re = 1
        · have hfl : Int.floor ((z.re + 1) / 2) = 1 := by rw [heq1]; norm_num
          unfold psiStrip
          simp only [hfl, Int.cast_one, mul_one]
          have hre_sub : (z - 2).re = -1 := by simp [heq1]; norm_num
          simp [hre_sub, wMap]
        · have hgt1 : 1 < z.re := lt_of_le_of_ne (not_lt.mp hlt1) (Ne.symm heq1)
          have hsh_gt : -1 < (z - 2).re := by simp; linarith
          have hsh_lt : (z - 2).re < 0 := by simp; linarith
          have hsh_im : stripHeightY0 < (z - 2).im := by simp [hz_im]
          have hper : psiStrip z = psiStrip (z - 2) := by
            have := psiStrip_periodic_two (z - 2) 1
            simpa using this
          rw [hper, psiStrip_eq_psiExtL1 hsh_gt (by linarith), psiExtL1_of_re_neg hsh_lt]
          have h2zQ : -starRingEnd ℂ (z - 2) ∈ OpenTriangleQ0 := by
            have hm := (mem_omegaL1_of_im_gt_Y0 hsh_im hsh_gt (by linarith)).1
            exact neg_conj_mem_openTriangleQ0_iff.mpr ⟨hm.1, hsh_gt, hsh_lt, hm.2.2.2.2⟩
          let u : ℂ := -starRingEnd ℂ (z - 2)
          have huQ : u ∈ OpenTriangleQ0 := h2zQ
          have hu0 : u ≠ 0 := fun h => by have := huQ.1; rw [h, Complex.zero_im] at this; exact lt_irrefl 0 this
          have hu1 : u ≠ 1 := fun h => by have := huQ.1; rw [h, Complex.one_im] at this; exact lt_irrefl 0 this
          have hw_u_eq : wMap u = moebiusM3 (moebiusM3 u) := (moebiusM3_iter2 hu0 hu1).symm
          have hw_uQ : wMap u ∈ OpenTriangleQ0 :=
            hw_u_eq ▸ moebiusM3_mapsTo_openTriangleQ0 (moebiusM3_mapsTo_openTriangleQ0 huQ)
          have hM3_wu : moebiusM3 (wMap u) = u := by
            rw [hw_u_eq]; exact moebiusM3_iter3 hu0 hu1
          have hconj_wz : -starRingEnd ℂ (wMap z) = wMap u := by
            dsimp [wMap, u]
            have h1 : 1 - (-starRingEnd ℂ (z - 2)) = -(starRingEnd ℂ (1 - z)) := by
              apply Complex.ext <;> (simp; try ring)
            rw [h1, map_div₀, map_one, div_neg]
          have hwz_re_neg : (wMap z).re < 0 := by
            have := hw_uQ.2.1
            rw [← hconj_wz, Complex.neg_re, Complex.conj_re] at this
            linarith
          rw [psiExtL1_of_re_neg hwz_re_neg, hconj_wz]
          have hpsi_u : riemannPsi u = omegaCube * riemannPsi (wMap u) := by
            rw [← riemannPsi_moebiusM3 hw_uQ, hM3_wu]
          change (starRingEnd ℂ (riemannPsi u))⁻¹ =
            omegaCube * (starRingEnd ℂ (riemannPsi (wMap u)))⁻¹
          rw [hpsi_u, map_mul, mul_inv, star_omegaCube]
          have homega_inv : (omegaCube ^ 2)⁻¹ = omegaCube := by
            refine inv_eq_of_mul_eq_one_right ?_
            rw [← pow_succ, omegaCube_pow_three]
          rw [homega_inv]
    have hd_z₁ : DifferentiableAt ℂ psiStrip z₁ := hcomp_z₁.congr_of_eventuallyEq hev_z₁
    have hshift_eq : psiStrip = fun z => psiStrip (z + 2 * ((1 - k₀ : ℤ) : ℂ)) := by
      funext z; exact (psiStrip_periodic_two z (1 - k₀)).symm
    rw [hshift_eq]
    exact (hz₁_eq ▸ hd_z₁).comp z₀ (differentiableAt_id.add (differentiableAt_const _))
  · -- Interior of period strip: `-1 < zRed₀.re < 1`
    have hzRed₀_gt : -1 < zRed₀.re := lt_of_le_of_ne hzRed₀_ge (Ne.symm h_neg1)
    have hmem := mem_omegaL1_of_im_gt_Y0 (hzRed₀_im ▸ hz₀) hzRed₀_gt hzRed₀_lt
    have hd_red : DifferentiableAt ℂ (fun z => psiExtL1 (z - 2 * (k₀ : ℂ))) z₀ :=
      (psiExtL1_holo_off_neg_conj_z0 zRed₀ ⟨hmem.1, fun h => hmem.2 (Or.inr h)⟩).comp z₀
        (differentiableAt_id.sub (differentiableAt_const _))
    have hopen_strip : IsOpen {z : ℂ | -1 < (z - 2 * (k₀ : ℂ)).re ∧ (z - 2 * (k₀ : ℂ)).re < 1} :=
      (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_id.sub continuous_const))).inter
        (isOpen_lt (Complex.continuous_re.comp (continuous_id.sub continuous_const)) continuous_const)
    refine hd_red.congr_of_eventuallyEq ?_
    filter_upwards [hopen_strip.mem_nhds ⟨hzRed₀_gt, hzRed₀_lt⟩] with z ⟨hgt, hlt⟩
    have hper : psiStrip z = psiStrip (z - 2 * (k₀ : ℂ)) := by
      have := psiStrip_periodic_two (z - 2 * (k₀ : ℂ)) k₀
      simpa using this
    rw [hper, psiStrip_eq_psiExtL1 hgt hlt]

/-- Punctured-disc radius `R_q = exp(-π Y₀)` for the cusp coordinate `q = exp(π i z)`. -/
def cuspRadiusRq : ℝ :=
  Real.exp (-Real.pi * stripHeightY0)

theorem cuspRadiusRq_pos : 0 < cuspRadiusRq :=
  Real.exp_pos _

/-- Section `q ↦ -i log(q) / π` of `z ↦ exp(π i z)` on `ℂ \ {0}`. -/
def qToZ (q : ℂ) : ℂ :=
  -Complex.I * Complex.log q / (Real.pi : ℂ)

theorem exp_pi_I_mul_qToZ {q : ℂ} (hq : q ≠ 0) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * qToZ q) = q := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hmul : (Real.pi : ℂ) * Complex.I * qToZ q = Complex.log q := by
    dsimp [qToZ]
    field_simp [hpi]
    ring_nf
    simp [Complex.I_sq]
  rw [hmul, Complex.exp_log hq]

theorem qToZ_im {q : ℂ} : (qToZ q).im = -Real.log ‖q‖ / Real.pi := by
  dsimp [qToZ]
  rw [div_eq_mul_inv, ← Complex.ofReal_inv]
  simp only [Complex.mul_im, Complex.neg_re, Complex.I_re, neg_zero, zero_mul,
    Complex.neg_im, Complex.I_im, Complex.log_re, Complex.log_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero]
  ring

theorem stripHeightY0_lt_qToZ_im {q : ℂ} (hq0 : q ≠ 0) (hq_lt : ‖q‖ < cuspRadiusRq) :
    stripHeightY0 < (qToZ q).im := by
  rw [qToZ_im, lt_div_iff₀ Real.pi_pos]
  have hlog : Real.log ‖q‖ < -Real.pi * stripHeightY0 := by
    have := Real.log_lt_log (norm_pos_iff.mpr hq0) hq_lt
    rwa [cuspRadiusRq, Real.log_exp] at this
  linarith

/-- Descended function `F₀(q) = psiStrip (-i log q / π)` on `0 < ‖q‖ < R_q`. -/
def cuspFnF0 (q : ℂ) : ℂ :=
  psiStrip (qToZ q)

theorem cuspFnF0_exp_pi_I {z : ℂ} (_him : stripHeightY0 < z.im) :
    cuspFnF0 (Complex.exp ((Real.pi : ℂ) * Complex.I * z)) = psiStrip z := by
  let q : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * z)
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hexp_eq : Complex.exp ((Real.pi : ℂ) * Complex.I * qToZ q) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * z) := exp_pi_I_mul_qToZ hq0
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp_eq
  have hpiI : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero
  have hz_eq : qToZ q = z + 2 * (k : ℂ) := by
    apply mul_left_cancel₀ hpiI
    linear_combination hk
  dsimp [cuspFnF0]
  rw [hz_eq, psiStrip_periodic_two]

theorem cuspFnF0_holo :
    RudinRCA.Chapter10.HolomorphicOn cuspFnF0 (Metric.ball (0 : ℂ) cuspRadiusRq \ {0}) := by
  rintro q₀ ⟨hq₀_ball, hq₀_ne⟩
  have hq₀_norm : ‖q₀‖ < cuspRadiusRq := by simpa [Metric.mem_ball] using hq₀_ball
  have hq₀_nz : q₀ ≠ 0 := hq₀_ne
  by_cases hslit : q₀ ∈ Complex.slitPlane
  · have hqToZ_diff : DifferentiableAt ℂ qToZ q₀ := by
      unfold qToZ
      exact ((Complex.differentiableAt_log hslit).const_mul (-Complex.I)).div_const (Real.pi : ℂ)
    exact (psiStrip_holo (qToZ q₀) (stripHeightY0_lt_qToZ_im hq₀_nz hq₀_norm)).comp q₀ hqToZ_diff
  · -- When `q₀ ∉ slitPlane` and `q₀ ≠ 0`, `q₀.re < 0` and `q₀.im = 0`, so `-q₀ ∈ slitPlane`
    have hneg_slit : -q₀ ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff] at hslit ⊢
      push Not at hslit
      left
      simp only [Complex.neg_re, neg_pos]
      refine lt_of_le_of_ne hslit.1 fun hre0 => hq₀_nz ?_
      exact Complex.ext hre0 hslit.2
    let zAlt : ℂ → ℂ := fun q => qToZ (-q) + 1
    have hzAlt_im : ∀ q : ℂ, (zAlt q).im = (qToZ q).im := by
      intro q; simp [zAlt, qToZ_im]
    have hzAlt_diff : DifferentiableAt ℂ zAlt q₀ := by
      have hd_log : DifferentiableAt ℂ (fun q => Complex.log (-q)) q₀ :=
        (Complex.differentiableAt_log hneg_slit).comp q₀ differentiableAt_id.neg
      exact (((hd_log.const_mul (-Complex.I)).div_const (Real.pi : ℂ)).add (differentiableAt_const 1))
    have hcomp : DifferentiableAt ℂ (fun q => psiStrip (zAlt q)) q₀ :=
      (psiStrip_holo (zAlt q₀) (show stripHeightY0 < (zAlt q₀).im by
        rw [hzAlt_im]; exact stripHeightY0_lt_qToZ_im hq₀_nz hq₀_norm)).comp q₀ hzAlt_diff
    have hopen_neg : IsOpen {q : ℂ | q ∈ Metric.ball (0 : ℂ) cuspRadiusRq ∧ -q ∈ Complex.slitPlane} :=
      Metric.isOpen_ball.inter (Complex.isOpen_slitPlane.preimage continuous_neg)
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [hopen_neg.mem_nhds ⟨hq₀_ball, hneg_slit⟩] with q ⟨hq_ball, hq_neg_slit⟩
    have hq_nz : q ≠ 0 := by
      intro h0; rw [h0, neg_zero] at hq_neg_slit
      exact Complex.slitPlane_ne_zero hq_neg_slit rfl
    have hq_norm : ‖q‖ < cuspRadiusRq := by simpa [Metric.mem_ball] using hq_ball
    have hexp_alt : Complex.exp ((Real.pi : ℂ) * Complex.I * zAlt q) = q := by
      dsimp [zAlt]
      rw [mul_add, mul_one, Complex.exp_add, exp_pi_I_mul_qToZ (neg_ne_zero.mpr hq_nz)]
      have hexp_pi : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
      rw [hexp_pi]
      ring
    have hzAlt_gt : stripHeightY0 < (zAlt q).im := by
      rw [hzAlt_im]; exact stripHeightY0_lt_qToZ_im hq_nz hq_norm
    have h := cuspFnF0_exp_pi_I hzAlt_gt
    rwa [hexp_alt] at h

theorem cuspFnF_removable :
    RudinRCA.Chapter10.HasRemovableSingularity cuspFnF0 (Metric.ball (0 : ℂ) cuspRadiusRq) 0 := by
  refine RudinRCA.Chapter10.removable_of_bounded
    ⟨Metric.isOpen_ball, Metric.mem_ball_self cuspRadiusRq_pos, cuspFnF0_holo⟩
    cuspRadiusRq_pos ⟨2, ?_⟩
  rintro q ⟨hq_ball, hq_ne⟩
  have hq_norm : ‖q‖ < cuspRadiusRq := by
    simpa [RudinRCA.Chapter10.disc, Metric.mem_ball] using hq_ball
  exact norm_psiStrip_le_two (stripHeightY0_lt_qToZ_im hq_ne hq_norm)

/-- Holomorphic extension `cuspFnF` of `cuspFnF0` across `q = 0` on `ball 0 R_q`. -/
def cuspFnF : ℂ → ℂ :=
  Classical.choose cuspFnF_removable

theorem cuspFnF_spec :
    RudinRCA.Chapter10.HolomorphicOn cuspFnF (Metric.ball (0 : ℂ) cuspRadiusRq) ∧
    Set.EqOn cuspFnF cuspFnF0 (Metric.ball (0 : ℂ) cuspRadiusRq \ {0}) :=
  Classical.choose_spec cuspFnF_removable

theorem psiStrip_eq_cuspFnF_exp {z : ℂ} (him : stripHeightY0 < z.im) :
    psiStrip z = cuspFnF (Complex.exp ((Real.pi : ℂ) * Complex.I * z)) := by
  let q : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * z)
  have hq_norm : ‖q‖ = Real.exp (-Real.pi * z.im) := by
    dsimp [q]
    rw [Complex.norm_exp]
    congr 1
    simp [mul_assoc]
  have hq_ball : q ∈ Metric.ball (0 : ℂ) cuspRadiusRq := by
    rw [Metric.mem_ball, dist_zero_right, hq_norm, cuspRadiusRq]
    exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  rw [cuspFnF_spec.2 ⟨hq_ball, Complex.exp_ne_zero _⟩, cuspFnF0_exp_pi_I him]

/-- Cusp limit `α_∞ = lim_{z ∈ Q₀, Im z → ∞} ψ(z)` on the unit circle. -/
def cuspAlphaInf : ℂ :=
  limUnder (Filter.comap Complex.im Filter.atTop ⊓ 𝓟 OpenTriangleQ0) riemannPsi

theorem tendsto_psiStrip_im_atTop :
    Tendsto psiStrip (Filter.comap Complex.im Filter.atTop) (𝓝 (cuspFnF 0)) := by
  have hexp_zero : Tendsto (fun z : ℂ => Complex.exp ((Real.pi : ℂ) * Complex.I * z))
      (Filter.comap Complex.im Filter.atTop) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm_eq : (fun z : ℂ => ‖Complex.exp ((Real.pi : ℂ) * Complex.I * z)‖) =
        (fun y : ℝ => Real.exp (-Real.pi * y)) ∘ Complex.im := by
      funext z; simp [Complex.norm_exp, mul_assoc]
    rw [hnorm_eq]
    refine Tendsto.comp ?_ tendsto_comap
    have hlin : Tendsto (fun y : ℝ => -Real.pi * y) Filter.atTop Filter.atBot := by
      have h1 := Filter.tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop Real.pi_pos)
      exact h1.congr fun y => by simp [neg_mul]
    exact Real.tendsto_exp_atBot.comp hlin
  have hF_cont : ContinuousAt cuspFnF 0 :=
    (cuspFnF_spec.1 0 (Metric.mem_ball_self cuspRadiusRq_pos)).continuousAt
  refine (hF_cont.tendsto.comp hexp_zero).congr' ?_
  have hev : {z : ℂ | stripHeightY0 < z.im} ∈ Filter.comap Complex.im Filter.atTop :=
    ⟨Set.Ioi stripHeightY0, Filter.Ioi_mem_atTop stripHeightY0, Subset.rfl⟩
  filter_upwards [hev] with z hz
  exact (psiStrip_eq_cuspFnF_exp hz).symm

theorem cuspAlphaInf_eq_cuspFnF_zero : cuspAlphaInf = cuspFnF 0 := by
  have hnebot : (Filter.comap Complex.im Filter.atTop ⊓ 𝓟 OpenTriangleQ0).NeBot := by
    rw [Filter.inf_principal_neBot_iff]
    intro S hS
    rcases Filter.mem_comap.mp hS with ⟨T, hT, hsub⟩
    rcases Filter.mem_atTop_sets.mp hT with ⟨B, hB⟩
    let y : ℝ := max B 1
    let z : ℂ := 1 / 2 + (y : ℂ) * Complex.I
    have hzQ : z ∈ OpenTriangleQ0 := half_add_im_mem_openTriangleQ0 (le_max_right B 1)
    have hzS : z ∈ S := hsub (hB y (le_max_left B 1) |> fun hyT => by simpa [z] using hyT)
    exact ⟨z, hzS, hzQ⟩
  have htend : Tendsto riemannPsi (Filter.comap Complex.im Filter.atTop ⊓ 𝓟 OpenTriangleQ0)
      (𝓝 (cuspFnF 0)) := by
    refine (tendsto_psiStrip_im_atTop.mono_left inf_le_left).congr' ?_
    filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self _)] with z hzQ
    exact psiStrip_eq_riemannPsi hzQ
  exact htend.limUnder_eq

theorem norm_cuspAlphaInf : ‖cuspAlphaInf‖ = 1 := by
  let γ : ℝ → ℂ := fun y => 1 / 2 + (y : ℂ) * Complex.I
  have hγ_tend : Tendsto γ Filter.atTop
      (Filter.comap Complex.im Filter.atTop ⊓ 𝓟 OpenTriangleQ0) := by
    refine Filter.tendsto_inf.mpr ⟨?_, ?_⟩
    · rw [Filter.tendsto_comap_iff]
      have : Complex.im ∘ γ = id := by funext y; simp [γ]
      rw [this]; exact tendsto_id
    · rw [Filter.tendsto_principal]
      filter_upwards [Filter.Ioi_mem_atTop (1 : ℝ)] with y hy
      exact half_add_im_mem_openTriangleQ0 (le_of_lt hy)
  have hlim1 : Tendsto (fun y => ‖riemannPsi (γ y)‖) Filter.atTop (𝓝 ‖cuspAlphaInf‖) := by
    rw [cuspAlphaInf_eq_cuspFnF_zero]
    have hpsi : Tendsto (riemannPsi ∘ γ) Filter.atTop (𝓝 (cuspFnF 0)) := by
      refine (tendsto_psiStrip_im_atTop.comp (Filter.tendsto_inf.mp hγ_tend).1 |>.congr' ?_)
      filter_upwards [Filter.Ioi_mem_atTop (1 : ℝ)] with y hy
      exact psiStrip_eq_riemannPsi (half_add_im_mem_openTriangleQ0 (le_of_lt hy))
    exact hpsi.norm
  have hlim2 : Tendsto (fun y => ‖riemannPsi (γ y)‖) Filter.atTop (𝓝 1) :=
    tendsto_norm_riemannPsi_im_atTop.comp hγ_tend
  exact tendsto_nhds_unique hlim1 hlim2

theorem cuspAlphaInf_ne_zero : cuspAlphaInf ≠ 0 := by
  intro h; have := norm_cuspAlphaInf; rw [h, norm_zero] at this; norm_num at this

/-- Open-mapping helper for `psiExtL1` at any point `p ∈ BoundaryL1`: for any small ball `B` around
`p`, `psiExtL1 '' B` is an open neighborhood of `psiExtL1 p` whose intersection with `ball 0 1`
equals `riemannPsi '' (B ∩ OpenTriangleQ0)`. -/
theorem open_image_psiExtL1_ball {p : ℂ} (hp : p ∈ BoundaryL1) {δ : ℝ} (hδ : 0 < δ)
    (hsub : Metric.ball p δ ⊆ OmegaL1 \ {z0Center, -starRingEnd ℂ z0Center}) :
    IsOpen (psiExtL1 '' Metric.ball p δ) ∧
    psiExtL1 p ∈ psiExtL1 '' Metric.ball p δ ∧
    (psiExtL1 '' Metric.ball p δ) ∩ Metric.ball (0 : ℂ) 1 =
      riemannPsi '' (Metric.ball p δ ∩ OpenTriangleQ0) := by
  have hreg : RudinRCA.Chapter10.IsRegion (Metric.ball p δ) :=
    RudinRCA.Chapter10.disc_isRegion p hδ
  have hholo : RudinRCA.Chapter10.HolomorphicOn psiExtL1 (Metric.ball p δ) :=
    fun z hz => psiExtL1_holo_off_neg_conj_z0 z ⟨(hsub hz).1, fun h => (hsub hz).2 (Or.inr h)⟩
  have hnot_const : ¬ ∃ w : ℂ, ∀ z ∈ Metric.ball p δ, psiExtL1 z = w := by
    rintro ⟨w, hw⟩
    let z₁ : ℂ := p + ((δ / 2 : ℝ) : ℂ)
    let z₂ : ℂ := p + ((δ / 3 : ℝ) : ℂ)
    have hz₁_B : z₁ ∈ Metric.ball p δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [z₁, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hδ)]
      exact half_lt_self hδ
    have hz₂_B : z₂ ∈ Metric.ball p δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [z₂, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (show 0 < δ / 3 by positivity)]
      linarith
    have hz₁_Q : z₁ ∈ OpenTriangleQ0 :=
      ⟨(hsub hz₁_B).1.1, by simp [z₁, hp.1, half_pos hδ], (hsub hz₁_B).1.2.2.1, (hsub hz₁_B).1.2.2.2.1⟩
    have hz₂_Q : z₂ ∈ OpenTriangleQ0 :=
      ⟨(hsub hz₂_B).1.1, by simp [z₂, hp.1, show 0 < δ / 3 by positivity],
        (hsub hz₂_B).1.2.2.1, (hsub hz₂_B).1.2.2.2.1⟩
    have heq_psi : riemannPsi z₁ = riemannPsi z₂ := by
      rw [← psiExtL1_of_re_pos hz₁_Q.2.1, ← psiExtL1_of_re_pos hz₂_Q.2.1,
        hw z₁ hz₁_B, hw z₂ hz₂_B]
    have hz_eq : z₁ = z₂ := riemannPsi_bij.injOn hz₁_Q hz₂_Q heq_psi
    have hre := congrArg Complex.re hz_eq
    simp [z₁, z₂, hp.1] at hre
    linarith
  have hopen : IsOpen (psiExtL1 '' Metric.ball p δ) :=
    (RudinRCA.Chapter10.theorem10_32 hreg hholo hnot_const).1.1 _ Subset.rfl Metric.isOpen_ball
  refine ⟨hopen, ⟨p, Metric.mem_ball_self hδ, rfl⟩, ?_⟩
  ext w
  constructor
  · rintro ⟨⟨z, hzB, rfl⟩, hw_ball⟩
    have hnorm_lt : ‖psiExtL1 z‖ < 1 := by simpa [Metric.mem_ball] using hw_ball
    obtain ⟨hz_om, hz_not⟩ := hsub hzB
    have hz_re_pos : 0 < z.re := by
      by_contra hle
      rcases eq_or_lt_of_le (not_lt.mp hle) with hzero | hneg
      · rw [norm_psiExtL1_boundaryL1 ⟨hzero, hz_om.1⟩] at hnorm_lt
        exact lt_irrefl 1 hnorm_lt
      · have hgt := one_lt_norm_psiExtL1_reflectedQ0 ⟨hz_om.1, hz_om.2.1, hneg, hz_om.2.2.2.2⟩
          (fun h => hz_not (Or.inr h))
        linarith
    have hzQ : z ∈ OpenTriangleQ0 := ⟨hz_om.1, hz_re_pos, hz_om.2.2.1, hz_om.2.2.2.1⟩
    exact ⟨z, ⟨hzB, hzQ⟩, (psiExtL1_of_re_pos hz_re_pos).symm⟩
  · rintro ⟨z, ⟨hzB, hzQ⟩, rfl⟩
    exact ⟨⟨z, hzB, psiExtL1_of_re_pos hzQ.2.1⟩, riemannPsi_bij.mapsTo hzQ⟩

/-- `psiExtL1` is injective on `L₁ = {i y : y > 0}`. -/
theorem injOn_psiExtL1_boundaryL1 : Set.InjOn psiExtL1 BoundaryL1 := by
  intro p₁ hp₁ p₂ hp₂ heq
  by_contra hne
  have hopen_target : IsOpen (OmegaL1 \ {z0Center, -starRingEnd ℂ z0Center}) :=
    isOpen_omegaL1.sdiff (isClosed_singleton.union isClosed_singleton)
  obtain ⟨δ₁, hδ₁, hsub₁⟩ := Metric.isOpen_iff.mp hopen_target p₁
    ⟨boundaryL1_subset_omegaL1 hp₁, by
      rintro (h | h) <;> { have := congrArg Complex.re h; simp [hp₁.1] at this }⟩
  obtain ⟨δ₂, hδ₂, hsub₂⟩ := Metric.isOpen_iff.mp hopen_target p₂
    ⟨boundaryL1_subset_omegaL1 hp₂, by
      rintro (h | h) <;> { have := congrArg Complex.re h; simp [hp₂.1] at this }⟩
  let δ : ℝ := min (min δ₁ δ₂) (dist p₁ p₂ / 2)
  have hdist_pos : 0 < dist p₁ p₂ := dist_pos.mpr hne
  have hδ_pos : 0 < δ := lt_min (lt_min hδ₁ hδ₂) (half_pos hdist_pos)
  have hB₁_sub : Metric.ball p₁ δ ⊆ OmegaL1 \ {z0Center, -starRingEnd ℂ z0Center} :=
    (Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _))).trans hsub₁
  have hB₂_sub : Metric.ball p₂ δ ⊆ OmegaL1 \ {z0Center, -starRingEnd ℂ z0Center} :=
    (Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_right _ _))).trans hsub₂
  obtain ⟨hU₁_open, hw_U₁, hU₁_inter⟩ := open_image_psiExtL1_ball hp₁ hδ_pos hB₁_sub
  obtain ⟨hU₂_open, hw_U₂, hU₂_inter⟩ := open_image_psiExtL1_ball hp₂ hδ_pos hB₂_sub
  rw [← heq] at hw_U₂
  obtain ⟨ε, hε_pos, hε_sub⟩ :=
    Metric.isOpen_iff.mp (hU₁_open.inter hU₂_open) (psiExtL1 p₁) ⟨hw_U₁, hw_U₂⟩
  let t : ℝ := min (ε / 2) (1 / 2)
  have ht_pos : 0 < t := lt_min (half_pos hε_pos) (by norm_num)
  have ht_lt1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let w' : ℂ := ((1 - t : ℝ) : ℂ) * psiExtL1 p₁
  have hw'_norm_psi : ‖psiExtL1 p₁‖ = 1 := norm_psiExtL1_boundaryL1 hp₁
  have hw'_dist : w' ∈ Metric.ball (psiExtL1 p₁) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hdiff : w' - psiExtL1 p₁ = -(t : ℂ) * psiExtL1 p₁ := by dsimp [w']; push_cast; ring
    rw [hdiff, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos,
      hw'_norm_psi, mul_one]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε_pos)
  have hw'_unit : w' ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [w']
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith),
      hw'_norm_psi, mul_one]
    linarith
  obtain ⟨hw'_U₁, hw'_U₂⟩ := hε_sub hw'_dist
  have hm₁ : w' ∈ riemannPsi '' (Metric.ball p₁ δ ∩ OpenTriangleQ0) :=
    hU₁_inter ▸ ⟨hw'_U₁, hw'_unit⟩
  have hm₂ : w' ∈ riemannPsi '' (Metric.ball p₂ δ ∩ OpenTriangleQ0) :=
    hU₂_inter ▸ ⟨hw'_U₂, hw'_unit⟩
  rcases hm₁ with ⟨z₁, ⟨hz₁B, hz₁Q⟩, hpsi₁⟩
  rcases hm₂ with ⟨z₂, ⟨hz₂B, hz₂Q⟩, hpsi₂⟩
  have hz_eq : z₁ = z₂ := riemannPsi_bij.injOn hz₁Q hz₂Q (hpsi₁.trans hpsi₂.symm)
  subst hz_eq
  have hd1 : dist z₁ p₁ < dist p₁ p₂ / 2 :=
    lt_of_lt_of_le (Metric.mem_ball.mp hz₁B) (min_le_right _ _)
  have hd2 : dist z₁ p₂ < dist p₁ p₂ / 2 :=
    lt_of_lt_of_le (Metric.mem_ball.mp hz₂B) (min_le_right _ _)
  have htri : dist p₁ p₂ ≤ dist p₁ z₁ + dist z₁ p₂ := dist_triangle p₁ z₁ p₂
  rw [dist_comm p₁ z₁] at htri
  linarith

/-- On `L₁`, `psiExtL1` avoids all three cusp images `ω^k · α_∞` (`k = 0, 1, 2`). -/
theorem psiExtL1_ne_omega_pow_cuspAlphaInf {p : ℂ} (hp : p ∈ BoundaryL1) (k : ℕ) :
    omegaCube ^ k * psiExtL1 p ≠ cuspAlphaInf := by
  have hmod : omegaCube ^ k = omegaCube ^ (k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod k 3]
    rw [pow_add, pow_mul, omegaCube_pow_three, one_pow, one_mul]
  rw [hmod]
  have hj_lt : k % 3 < 3 := Nat.mod_lt k (by norm_num)
  generalize k % 3 = j at hj_lt ⊢
  intro heq
  have hopen_target : IsOpen (OmegaL1 \ {z0Center, -starRingEnd ℂ z0Center}) :=
    isOpen_omegaL1.sdiff (isClosed_singleton.union isClosed_singleton)
  obtain ⟨δ₀, hδ₀, hsub₀⟩ := Metric.isOpen_iff.mp hopen_target p
    ⟨boundaryL1_subset_omegaL1 hp, by
      rintro (h | h) <;> { have := congrArg Complex.re h; simp [hp.1] at this }⟩
  let δ : ℝ := min δ₀ (min (p.im / 2) (1 / 2))
  have hδ_pos : 0 < δ := lt_min hδ₀ (lt_min (half_pos hp.2) (by norm_num))
  have hsub : Metric.ball p δ ⊆ OmegaL1 \ {z0Center, -starRingEnd ℂ z0Center} :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hsub₀
  let M_im : ℝ := max (p.im + δ) (max ((p.im + δ) / (p.im / 2) ^ 2) ((p.im + δ) / (1 / 2) ^ 2))
  have him_le_M : ∀ z ∈ Metric.ball p δ ∩ OpenTriangleQ0, (moebiusM3^[j] z).im ≤ M_im := by
    rintro z ⟨hzB, hzQ⟩
    have hdist : ‖z - p‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hzB
    have him_abs : |z.im - p.im| < δ := by
      have hle := Complex.abs_im_le_norm (z - p)
      simp only [Complex.sub_im] at hle
      exact lt_of_le_of_lt hle hdist
    obtain ⟨him_lo, him_hi⟩ := abs_lt.mp him_abs
    have hz_im_lt : z.im < p.im + δ := by linarith
    have hz_im_gt : p.im / 2 < z.im := by
      have hδ_im : δ ≤ p.im / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
    have hz_re_lt : z.re < 1 / 2 := by
      have hle := Complex.abs_re_le_norm (z - p)
      simp only [Complex.sub_re, hp.1, sub_zero] at hle
      have hre_abs : |z.re| < δ := lt_of_le_of_lt hle hdist
      have hδ_half : δ ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
      linarith [(abs_lt.mp hre_abs).2]
    have hj_cases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj_cases with rfl | rfl | rfl
    · simp only [Function.iterate_zero, id_eq]
      exact le_trans hz_im_lt.le (le_max_left _ _)
    · simp only [Function.iterate_one]
      rw [(moebiusM3_re_im z).2]
      have hnsq_ge : (p.im / 2) ^ 2 ≤ Complex.normSq z := by
        rw [Complex.normSq_apply]
        have hp_pos : 0 < p.im / 2 := half_pos hp.2
        nlinarith [sq_nonneg z.re]
      have hle : z.im / Complex.normSq z ≤ (p.im + δ) / (p.im / 2) ^ 2 := by
        exact div_le_div₀ (by linarith [hp.2, hδ_pos]) hz_im_lt.le
          (sq_pos_of_pos (half_pos hp.2)) hnsq_ge
      exact le_trans hle (le_trans (le_max_left _ _) (le_max_right _ _))
    · simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_im] at hz_im_gt; linarith [hp.2]
      have hz1 : z ≠ 1 := fun h => by rw [h, Complex.one_re] at hz_re_lt; norm_num at hz_re_lt
      rw [moebiusM3_iter2 hz0 hz1]
      have him_inv : (1 / (1 - z)).im = z.im / Complex.normSq (1 - z) := by
        simp [one_div, Complex.inv_im]
      rw [him_inv]
      have hnsq_1z : (1 / 2 : ℝ) ^ 2 ≤ Complex.normSq (1 - z) := by
        rw [Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub]
        nlinarith [sq_nonneg z.im]
      have hle : z.im / Complex.normSq (1 - z) ≤ (p.im + δ) / (1 / 2) ^ 2 :=
        div_le_div₀ (by linarith [hp.2, hδ_pos]) hz_im_lt.le (by norm_num) hnsq_1z
      exact le_trans hle (le_trans (le_max_right _ _) (le_max_right _ _))
  let Y₁ : ℝ := max stripHeightY0 M_im + 1
  have hY₁_gt_Y0 : stripHeightY0 < Y₁ := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  have hY₁_gt_M : M_im < Y₁ := lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  let r₁ : ℝ := Real.exp (-Real.pi * Y₁)
  have hr₁_pos : 0 < r₁ := Real.exp_pos _
  have hr₁_lt : r₁ < cuspRadiusRq := by
    dsimp [r₁, cuspRadiusRq]
    exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  have hball_r₁_sub : Metric.ball (0 : ℂ) r₁ ⊆ Metric.ball (0 : ℂ) cuspRadiusRq :=
    Metric.ball_subset_ball hr₁_lt.le
  have hF_not_const : ¬ ∃ w : ℂ, ∀ q ∈ Metric.ball (0 : ℂ) r₁, cuspFnF q = w := by
    rintro ⟨w, hw⟩
    let w₁ : ℂ := 1 / 2 + ((Y₁ + 1 : ℝ) : ℂ) * Complex.I
    let w₂ : ℂ := 1 / 2 + ((Y₁ + 2 : ℝ) : ℂ) * Complex.I
    have hw₁_Q : w₁ ∈ OpenTriangleQ0 :=
      half_add_im_mem_openTriangleQ0 (by linarith [one_le_stripHeightY0])
    have hw₂_Q : w₂ ∈ OpenTriangleQ0 :=
      half_add_im_mem_openTriangleQ0 (by linarith [one_le_stripHeightY0])
    have hq₁_ball : Complex.exp ((Real.pi : ℂ) * Complex.I * w₁) ∈ Metric.ball (0 : ℂ) r₁ := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp]
      have hre : ((Real.pi : ℂ) * Complex.I * w₁).re = -Real.pi * (Y₁ + 1) := by
        simp [w₁, mul_assoc]; ring
      rw [hre]; exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
    have hq₂_ball : Complex.exp ((Real.pi : ℂ) * Complex.I * w₂) ∈ Metric.ball (0 : ℂ) r₁ := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp]
      have hre : ((Real.pi : ℂ) * Complex.I * w₂).re = -Real.pi * (Y₁ + 2) := by
        simp [w₂, mul_assoc]; ring
      rw [hre]; exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
    have hpsi_eq : riemannPsi w₁ = riemannPsi w₂ := by
      rw [← psiStrip_eq_riemannPsi hw₁_Q, ← psiStrip_eq_riemannPsi hw₂_Q,
        psiStrip_eq_cuspFnF_exp (by simp [w₁]; linarith),
        psiStrip_eq_cuspFnF_exp (by simp [w₂]; linarith),
        hw _ hq₁_ball, hw _ hq₂_ball]
    have hw_eq := riemannPsi_bij.injOn hw₁_Q hw₂_Q hpsi_eq
    have him_eq := congrArg Complex.im hw_eq
    simp [w₁, w₂] at him_eq
  have hV_open : IsOpen (cuspFnF '' Metric.ball (0 : ℂ) r₁) :=
    (RudinRCA.Chapter10.theorem10_32 (RudinRCA.Chapter10.disc_isRegion 0 hr₁_pos)
      (fun q hq => cuspFnF_spec.1 q (hball_r₁_sub hq)) hF_not_const).1.1 _ Subset.rfl Metric.isOpen_ball
  have hα_V : cuspAlphaInf ∈ cuspFnF '' Metric.ball (0 : ℂ) r₁ :=
    cuspAlphaInf_eq_cuspFnF_zero ▸ ⟨0, Metric.mem_ball_self hr₁_pos, rfl⟩
  obtain ⟨hU₁_open, hp_U₁, hU₁_inter⟩ := open_image_psiExtL1_ball hp hδ_pos hsub
  let rotU₁ : Set ℂ := (fun w => omegaCube ^ j * w) '' (psiExtL1 '' Metric.ball p δ)
  have homega_j_nz : omegaCube ^ j ≠ 0 := pow_ne_zero j omegaCube_ne_zero
  have hrotU₁_open : IsOpen rotU₁ := by
    have hhomeo : rotU₁ = (fun w => (omegaCube ^ j)⁻¹ * w) ⁻¹' (psiExtL1 '' Metric.ball p δ) := by
      ext w
      constructor
      · rintro ⟨u, hu, rfl⟩
        simpa [inv_mul_cancel_left₀ homega_j_nz] using hu
      · intro hw
        exact ⟨(omegaCube ^ j)⁻¹ * w, hw, mul_inv_cancel_left₀ homega_j_nz w⟩
    rw [hhomeo]
    exact hU₁_open.preimage (continuous_const.mul continuous_id)
  have hα_rotU₁ : cuspAlphaInf ∈ rotU₁ := ⟨psiExtL1 p, hp_U₁, heq⟩
  obtain ⟨ε, hε_pos, hε_sub⟩ :=
    Metric.isOpen_iff.mp (hrotU₁_open.inter hV_open) cuspAlphaInf ⟨hα_rotU₁, hα_V⟩
  let t : ℝ := min (ε / 2) (1 / 2)
  have ht_pos : 0 < t := lt_min (half_pos hε_pos) (by norm_num)
  have ht_lt1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let w' : ℂ := ((1 - t : ℝ) : ℂ) * cuspAlphaInf
  have hw'_dist : w' ∈ Metric.ball cuspAlphaInf ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hdiff : w' - cuspAlphaInf = -(t : ℂ) * cuspAlphaInf := by dsimp [w']; push_cast; ring
    rw [hdiff, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos,
      norm_cuspAlphaInf, mul_one]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε_pos)
  have hw'_unit : ‖w'‖ < 1 := by
    dsimp [w']
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith),
      norm_cuspAlphaInf, mul_one]
    linarith
  obtain ⟨hw'_rotU₁, hw'_V⟩ := hε_sub hw'_dist
  rcases hw'_rotU₁ with ⟨u, hu_U₁, hu_eq⟩
  dsimp only at hu_eq
  have hu_unit : u ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    have hnorm_wj : ‖omegaCube ^ j * u‖ = ‖u‖ := by
      rw [norm_mul, norm_pow, norm_omegaCube, one_pow, one_mul]
    rw [← hnorm_wj, hu_eq]
    exact hw'_unit
  have hu_mem : u ∈ riemannPsi '' (Metric.ball p δ ∩ OpenTriangleQ0) :=
    hU₁_inter ▸ ⟨hu_U₁, hu_unit⟩
  rcases hu_mem with ⟨z₁, ⟨hz₁B, hz₁Q⟩, rfl⟩
  have hiter_Q : ∀ m : ℕ, moebiusM3^[m] z₁ ∈ OpenTriangleQ0 ∧
      riemannPsi (moebiusM3^[m] z₁) = omegaCube ^ m * riemannPsi z₁ := by
    intro m
    induction m with
    | zero => simp [hz₁Q]
    | succ m ih =>
      rw [Function.iterate_succ', Function.comp_apply]
      refine ⟨moebiusM3_mapsTo_openTriangleQ0 ih.1, ?_⟩
      rw [riemannPsi_moebiusM3 ih.1, ih.2, pow_succ']
      ring
  let zLow : ℂ := moebiusM3^[j] z₁
  have hzLow_Q : zLow ∈ OpenTriangleQ0 := (hiter_Q j).1
  have hzLow_psi : riemannPsi zLow = w' := (hiter_Q j).2.trans hu_eq
  have hzLow_im : zLow.im ≤ M_im := him_le_M z₁ ⟨hz₁B, hz₁Q⟩
  rcases hw'_V with ⟨q, hq_ball, hFq⟩
  have hq_nz : q ≠ 0 := by
    intro h0
    rw [h0, ← cuspAlphaInf_eq_cuspFnF_zero] at hFq
    rw [← hFq, norm_cuspAlphaInf] at hw'_unit
    exact lt_irrefl 1 hw'_unit
  have hq_norm_r₁ : ‖q‖ < r₁ := by simpa [Metric.mem_ball] using hq_ball
  have hFq_strip : cuspFnF q = psiStrip (qToZ q) :=
    cuspFnF_spec.2 ⟨hball_r₁_sub hq_ball, hq_nz⟩
  have hzq_im_Y₁ : Y₁ < (qToZ q).im := by
    rw [qToZ_im, lt_div_iff₀ Real.pi_pos]
    have hlog := Real.log_lt_log (norm_pos_iff.mpr hq_nz) hq_norm_r₁
    rw [Real.log_exp] at hlog
    linarith
  let k_q : ℤ := Int.floor (((qToZ q).re + 1) / 2)
  let zHigh : ℂ := qToZ q - 2 * (k_q : ℂ)
  have hzHigh_im : zHigh.im = (qToZ q).im := by simp [zHigh]
  have hzHigh_re_ge : -1 ≤ zHigh.re := by
    simp [zHigh]; linarith [Int.floor_le (((qToZ q).re + 1) / 2)]
  have hzHigh_re_lt : zHigh.re < 1 := by
    simp [zHigh]; linarith [Int.lt_floor_add_one (((qToZ q).re + 1) / 2)]
  have hstrip_zHigh : psiStrip (qToZ q) = psiStrip zHigh := by
    have := psiStrip_periodic_two zHigh k_q
    simpa [zHigh] using this
  have hstrip_norm_lt : ‖psiStrip zHigh‖ < 1 := by
    rwa [← hstrip_zHigh, ← hFq_strip, hFq]
  have hzHigh_re_pos : 0 < zHigh.re := by
    by_contra hle
    rcases eq_or_lt_of_le (not_lt.mp hle) with hzero | hneg
    · have him_Y0 : stripHeightY0 < zHigh.im := by linarith
      have hm := mem_omegaL1_of_im_gt_Y0 him_Y0 (by linarith) hzHigh_re_lt
      rw [psiStrip_eq_psiExtL1 (by linarith) hzHigh_re_lt,
        norm_psiExtL1_boundaryL1 ⟨hzero, hm.1.1⟩] at hstrip_norm_lt
      exact lt_irrefl 1 hstrip_norm_lt
    · rcases eq_or_lt_of_le hzHigh_re_ge with h_neg1 | h_gt_neg1
      · have hzHigh_neg1 : zHigh.re = -1 := h_neg1.symm
        have hfl0 : Int.floor ((zHigh.re + 1) / 2) = 0 := by rw [hzHigh_neg1]; norm_num
        have hval : ‖psiStrip zHigh‖ = 1 := by
          unfold psiStrip
          dsimp only
          rw [hfl0]
          simp only [Int.cast_zero, mul_zero, sub_zero, hzHigh_neg1, ↓reduceIte]
          have hz2 : zHigh + 2 = 1 + (zHigh.im : ℂ) * Complex.I :=
            Complex.ext (by simp [hzHigh_neg1]; norm_num) (by simp)
          have him_pos : 0 < zHigh.im := by linarith [one_le_stripHeightY0]
          have hw : 1 / (1 - (zHigh + 2)) = ((1 / zHigh.im : ℝ) : ℂ) * Complex.I := by
            rw [hz2]
            have him_ne : (zHigh.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr him_pos.ne'
            have h1 : 1 - (1 + (zHigh.im : ℂ) * Complex.I) = -(zHigh.im : ℂ) * Complex.I := by ring
            rw [h1, Complex.ofReal_div, Complex.ofReal_one]
            field_simp [him_ne, Complex.I_ne_zero]; ring_nf; simp [Complex.I_sq]
          rw [hw, norm_mul, norm_omegaCube,
            norm_psiExtL1_boundaryL1 ⟨by simp, by simp; exact him_pos⟩, mul_one]
        rw [hval] at hstrip_norm_lt
        exact lt_irrefl 1 hstrip_norm_lt
      · have him_Y0 : stripHeightY0 < zHigh.im := by linarith
        have hm := mem_omegaL1_of_im_gt_Y0 him_Y0 h_gt_neg1 hzHigh_re_lt
        rw [psiStrip_eq_psiExtL1 h_gt_neg1 hzHigh_re_lt] at hstrip_norm_lt
        have hgt1 := one_lt_norm_psiExtL1_reflectedQ0
          ⟨hm.1.1, h_gt_neg1, hneg, hm.1.2.2.2.2⟩ (fun h => hm.2 (Or.inr h))
        linarith
  have hzHigh_Q : zHigh ∈ OpenTriangleQ0 := by
    have hm := (mem_omegaL1_of_im_gt_Y0 (by linarith) (by linarith) hzHigh_re_lt).1
    exact ⟨hm.1, hzHigh_re_pos, hzHigh_re_lt, hm.2.2.2.1⟩
  have hzHigh_psi : riemannPsi zHigh = w' := by
    rw [← psiStrip_eq_riemannPsi hzHigh_Q, ← hstrip_zHigh, ← hFq_strip, hFq]
  have hz_eq : zLow = zHigh :=
    riemannPsi_bij.injOn hzLow_Q hzHigh_Q (hzLow_psi.trans hzHigh_psi.symm)
  rw [hz_eq, hzHigh_im] at hzLow_im
  linarith

theorem psiExtL1_boundaryL1_notMem_cusps {p : ℂ} (hp : p ∈ BoundaryL1) :
    psiExtL1 p ≠ cuspAlphaInf ∧
    psiExtL1 p ≠ omegaCube * cuspAlphaInf ∧
    psiExtL1 p ≠ omegaCube ^ 2 * cuspAlphaInf := by
  refine ⟨?_, ?_, ?_⟩
  · have h := psiExtL1_ne_omega_pow_cuspAlphaInf hp 0
    simpa using h
  · intro heq
    apply psiExtL1_ne_omega_pow_cuspAlphaInf hp 2
    rw [heq, ← mul_assoc, ← pow_succ, omegaCube_pow_three, one_mul]
  · intro heq
    apply psiExtL1_ne_omega_pow_cuspAlphaInf hp 1
    rw [heq, pow_one, ← mul_assoc, ← pow_succ', omegaCube_pow_three, one_mul]


/-!
### Section 3: Möbius Normalization `Φ`, `λ` on `Q` and `Π⁺`, and Theorem `16.20`
-/

/-- Möbius transformation `Φ(u) = -ω² (u - ω²) / (u - 1)` sending `(ω², ω, 1) ↦ (0, 1, ∞)` and
mapping `ball 0 1` conformally onto `UpperHalfPlaneSet` with `Φ(0) = z₀`. -/
def moebiusPhi (u : ℂ) : ℂ :=
  -omegaCube ^ 2 * (u - omegaCube ^ 2) / (u - 1)

/-- Explicit inverse `Φ⁻¹(w) = (w + ω) / (w + ω²)` of `moebiusPhi`. -/
def moebiusPhiInv (w : ℂ) : ℂ :=
  (w + omegaCube) / (w + omegaCube ^ 2)

theorem omegaCube_sq_re_im :
    (omegaCube ^ 2).re = -1 / 2 ∧ (omegaCube ^ 2).im = Real.sqrt 3 / 2 := by
  rw [← star_omegaCube]
  simp [omegaCube_re, omegaCube_im]

theorem omegaCube_sub_sq_ne_zero : omegaCube - omegaCube ^ 2 ≠ 0 := by
  intro h
  have him := congrArg Complex.im (sub_eq_zero.mp h)
  rw [omegaCube_im, omegaCube_sq_re_im.2] at him
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  linarith

theorem omegaCube_pow_four : omegaCube ^ 4 = omegaCube := by
  rw [show (4 : ℕ) = 3 + 1 by rfl, pow_add, omegaCube_pow_three, one_mul, pow_one]

@[simp]
theorem moebiusPhi_omegaCube_sq : moebiusPhi (omegaCube ^ 2) = 0 := by
  simp [moebiusPhi]

@[simp]
theorem moebiusPhi_omegaCube : moebiusPhi omegaCube = 1 := by
  unfold moebiusPhi
  have h1 : omegaCube - 1 ≠ 0 := sub_ne_zero.mpr omegaCube_ne_one
  have hnum : -omegaCube ^ 2 * (omegaCube - omegaCube ^ 2) = omegaCube - 1 := by
    calc -omegaCube ^ 2 * (omegaCube - omegaCube ^ 2)
        = -omegaCube ^ 3 + omegaCube ^ 4 := by ring
      _ = -1 + omegaCube := by rw [omegaCube_pow_three, omegaCube_pow_four]
      _ = omegaCube - 1 := by ring
  rw [hnum, div_self h1]

@[simp]
theorem moebiusPhi_zero : moebiusPhi 0 = z0Center := by
  unfold moebiusPhi
  have h : -omegaCube ^ 2 * (0 - omegaCube ^ 2) / (0 - 1) = -omegaCube := by
    calc -omegaCube ^ 2 * (0 - omegaCube ^ 2) / (0 - 1)
        = -(omegaCube ^ 4) := by ring
      _ = -omegaCube := by rw [omegaCube_pow_four]
  rw [h, neg_omegaCube_eq_z0Center]

theorem moebiusPhi_add_omegaCube_sq {u : ℂ} (hu : u ≠ 1) :
    moebiusPhi u + omegaCube ^ 2 = (omegaCube - omegaCube ^ 2) / (u - 1) := by
  have hu1 : u - 1 ≠ 0 := sub_ne_zero.mpr hu
  unfold moebiusPhi
  rw [div_add' _ _ _ hu1]
  congr 1
  calc -omegaCube ^ 2 * (u - omegaCube ^ 2) + omegaCube ^ 2 * (u - 1)
      = omegaCube ^ 4 - omegaCube ^ 2 := by ring
    _ = omegaCube - omegaCube ^ 2 := by rw [omegaCube_pow_four]

theorem moebiusPhi_ne_neg_omegaCube_sq {u : ℂ} (hu : u ≠ 1) :
    moebiusPhi u + omegaCube ^ 2 ≠ 0 := by
  rw [moebiusPhi_add_omegaCube_sq hu]
  exact div_ne_zero omegaCube_sub_sq_ne_zero (sub_ne_zero.mpr hu)

theorem moebiusPhiInv_left {u : ℂ} (hu : u ≠ 1) :
    moebiusPhiInv (moebiusPhi u) = u := by
  have hu1 : u - 1 ≠ 0 := sub_ne_zero.mpr hu
  have hden := moebiusPhi_add_omegaCube_sq hu
  have hnum : moebiusPhi u + omegaCube = u * (omegaCube - omegaCube ^ 2) / (u - 1) := by
    unfold moebiusPhi
    rw [div_add' _ _ _ hu1]
    congr 1
    calc -omegaCube ^ 2 * (u - omegaCube ^ 2) + omegaCube * (u - 1)
        = u * (omegaCube - omegaCube ^ 2) + (omegaCube ^ 4 - omegaCube) := by ring
      _ = u * (omegaCube - omegaCube ^ 2) := by rw [omegaCube_pow_four]; ring
  unfold moebiusPhiInv
  rw [hnum, hden, div_div_div_cancel_right₀ hu1, mul_div_cancel_right₀ _ omegaCube_sub_sq_ne_zero]

theorem moebiusPhiInv_ne_one {w : ℂ} (hw : w + omegaCube ^ 2 ≠ 0) :
    moebiusPhiInv w ≠ 1 := by
  unfold moebiusPhiInv
  intro h
  have heq : w + omegaCube = w + omegaCube ^ 2 := (div_eq_one_iff_eq hw).mp h
  exact omegaCube_sub_sq_ne_zero (sub_eq_zero.mpr (add_left_cancel heq))

theorem moebiusPhiInv_right {w : ℂ} (hw : w + omegaCube ^ 2 ≠ 0) :
    moebiusPhi (moebiusPhiInv w) = w := by
  unfold moebiusPhi moebiusPhiInv
  have hsub1 : (w + omegaCube) / (w + omegaCube ^ 2) - 1 =
      (omegaCube - omegaCube ^ 2) / (w + omegaCube ^ 2) := by
    rw [div_sub_one hw]; ring
  have hsub2 : (w + omegaCube) / (w + omegaCube ^ 2) - omegaCube ^ 2 =
      w * (1 - omegaCube ^ 2) / (w + omegaCube ^ 2) := by
    rw [div_sub' hw]
    congr 1
    calc w + omegaCube - (w + omegaCube ^ 2) * omegaCube ^ 2
        = w * (1 - omegaCube ^ 2) + (omegaCube - omegaCube ^ 4) := by ring
      _ = w * (1 - omegaCube ^ 2) := by rw [omegaCube_pow_four]; ring
  have hmul : -omegaCube ^ 2 * (w * (1 - omegaCube ^ 2) / (w + omegaCube ^ 2)) =
      w * (omegaCube - omegaCube ^ 2) / (w + omegaCube ^ 2) := by
    rw [← mul_div_assoc]
    congr 1
    calc -omegaCube ^ 2 * (w * (1 - omegaCube ^ 2))
        = w * (omegaCube ^ 4 - omegaCube ^ 2) := by ring
      _ = w * (omegaCube - omegaCube ^ 2) := by rw [omegaCube_pow_four]
  rw [hsub1, hsub2, hmul, div_div_div_cancel_right₀ hw,
    mul_div_cancel_right₀ _ omegaCube_sub_sq_ne_zero]

theorem normSq_add_omegaCube_sq_sub (w : ℂ) :
    Complex.normSq (w + omegaCube ^ 2) - Complex.normSq (w + omegaCube) =
      2 * Real.sqrt 3 * w.im := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    omegaCube_re, omegaCube_im, omegaCube_sq_re_im.1, omegaCube_sq_re_im.2]
  ring

theorem add_omegaCube_sq_ne_zero_of_im_nonneg {w : ℂ} (hw : 0 ≤ w.im) :
    w + omegaCube ^ 2 ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  rw [Complex.add_im, omegaCube_sq_re_im.2, Complex.zero_im] at him
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  linarith

theorem moebiusPhi_im_sign {u : ℂ} (hu : u ≠ 1) :
    (0 < (moebiusPhi u).im ↔ ‖u‖ < 1) ∧
    ((moebiusPhi u).im = 0 ↔ ‖u‖ = 1) ∧
    ((moebiusPhi u).im < 0 ↔ 1 < ‖u‖) := by
  let w : ℂ := moebiusPhi u
  have hw_nz : w + omegaCube ^ 2 ≠ 0 := moebiusPhi_ne_neg_omegaCube_sq hu
  have hu_eq : u = (w + omegaCube) / (w + omegaCube ^ 2) := (moebiusPhiInv_left hu).symm
  have hden_pos : 0 < Complex.normSq (w + omegaCube ^ 2) := Complex.normSq_pos.mpr hw_nz
  have hnsq_u : ‖u‖ ^ 2 = Complex.normSq (w + omegaCube) / Complex.normSq (w + omegaCube ^ 2) := by
    rw [← Complex.normSq_eq_norm_sq, hu_eq, map_div₀]
  have hdiff := normSq_add_omegaCube_sq_sub w
  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hnn : 0 ≤ ‖u‖ := norm_nonneg u
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro him
      have hlt_sq : ‖u‖ ^ 2 < 1 := by
        rw [hnsq_u, div_lt_one hden_pos]
        nlinarith
      nlinarith
    · intro hlt
      have hlt_sq : ‖u‖ ^ 2 < 1 := by nlinarith
      rw [hnsq_u, div_lt_one hden_pos] at hlt_sq
      nlinarith
  · constructor
    · intro him
      have heq_sq : ‖u‖ ^ 2 = 1 := by
        rw [hnsq_u, div_eq_one_iff_eq hden_pos.ne']
        nlinarith
      nlinarith
    · intro heq1
      have heq_sq : ‖u‖ ^ 2 = 1 := by rw [heq1]; ring
      rw [hnsq_u, div_eq_one_iff_eq hden_pos.ne'] at heq_sq
      nlinarith
  · constructor
    · intro him
      have hgt_sq : 1 < ‖u‖ ^ 2 := by
        rw [hnsq_u, one_lt_div hden_pos]
        nlinarith
      nlinarith
    · intro hgt
      have hgt_sq : 1 < ‖u‖ ^ 2 := by nlinarith
      rw [hnsq_u, one_lt_div hden_pos] at hgt_sq
      nlinarith

theorem moebiusPhi_bijOn_unitBall :
    Set.BijOn moebiusPhi (Metric.ball (0 : ℂ) 1) UpperHalfPlaneSet := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    have hu_lt : ‖u‖ < 1 := by simpa [Metric.mem_ball] using hu
    have hu1 : u ≠ 1 := fun h => by rw [h, norm_one] at hu_lt; exact lt_irrefl 1 hu_lt
    exact (moebiusPhi_im_sign hu1).1.mpr hu_lt
  · intro u₁ hu₁ u₂ hu₂ heq
    have hu₁1 : u₁ ≠ 1 := fun h => by
      have : ‖u₁‖ < 1 := by simpa [Metric.mem_ball] using hu₁
      rw [h, norm_one] at this; exact lt_irrefl 1 this
    have hu₂1 : u₂ ≠ 1 := fun h => by
      have : ‖u₂‖ < 1 := by simpa [Metric.mem_ball] using hu₂
      rw [h, norm_one] at this; exact lt_irrefl 1 this
    calc u₁ = moebiusPhiInv (moebiusPhi u₁) := (moebiusPhiInv_left hu₁1).symm
      _ = moebiusPhiInv (moebiusPhi u₂) := by rw [heq]
      _ = u₂ := moebiusPhiInv_left hu₂1
  · intro w hw
    have hw_nz : w + omegaCube ^ 2 ≠ 0 := add_omegaCube_sq_ne_zero_of_im_nonneg (le_of_lt hw)
    let u := moebiusPhiInv w
    have hu1 : u ≠ 1 := moebiusPhiInv_ne_one hw_nz
    have hphi : moebiusPhi u = w := moebiusPhiInv_right hw_nz
    have hu_lt : ‖u‖ < 1 := (moebiusPhi_im_sign hu1).1.mp (hphi.symm ▸ hw)
    exact ⟨u, by simpa [Metric.mem_ball] using hu_lt, hphi⟩

theorem moebiusPhi_bijOn_unitCircle :
    Set.BijOn moebiusPhi (Metric.sphere (0 : ℂ) 1 \ {1}) {w : ℂ | w.im = 0} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro u ⟨hu_sph, hu1⟩
    have hu_norm : ‖u‖ = 1 := by simpa [Metric.mem_sphere] using hu_sph
    exact (moebiusPhi_im_sign hu1).2.1.mpr hu_norm
  · rintro u₁ ⟨_, hu₁1⟩ u₂ ⟨_, hu₂1⟩ heq
    calc u₁ = moebiusPhiInv (moebiusPhi u₁) := (moebiusPhiInv_left hu₁1).symm
      _ = moebiusPhiInv (moebiusPhi u₂) := by rw [heq]
      _ = u₂ := moebiusPhiInv_left hu₂1
  · intro w hw
    change w.im = 0 at hw
    have hw_nz : w + omegaCube ^ 2 ≠ 0 := add_omegaCube_sq_ne_zero_of_im_nonneg (by linarith)
    let u := moebiusPhiInv w
    have hu1 : u ≠ 1 := moebiusPhiInv_ne_one hw_nz
    have hphi : moebiusPhi u = w := moebiusPhiInv_right hw_nz
    have hu_norm : ‖u‖ = 1 := (moebiusPhi_im_sign hu1).2.1.mp (by rw [hphi]; exact hw)
    exact ⟨u, ⟨by simpa [Metric.mem_sphere] using hu_norm, hu1⟩, hphi⟩

/-- 3-fold `M₃` equivariance of `moebiusPhi`: `Φ(ω u) = M₃(Φ(u))` for `u ∉ {1, ω²}`. -/
theorem moebiusPhi_mul_omegaCube {u : ℂ} (_hu1 : u ≠ 1) (husq : u ≠ omegaCube ^ 2) :
    moebiusPhi (omegaCube * u) = moebiusM3 (moebiusPhi u) := by
  have hu_sub_sq : u - omegaCube ^ 2 ≠ 0 := sub_ne_zero.mpr husq
  have hnum_l : omegaCube * u - omegaCube ^ 2 = omegaCube * (u - omegaCube) := by ring
  have hden_l : omegaCube * u - 1 = omegaCube * (u - omegaCube ^ 2) := by
    calc omegaCube * u - 1 = omegaCube * u - omegaCube ^ 3 := by rw [omegaCube_pow_three]
      _ = omegaCube * (u - omegaCube ^ 2) := by ring
  have hlhs : moebiusPhi (omegaCube * u) =
      (-omegaCube ^ 2 * (u - omegaCube)) / (u - omegaCube ^ 2) := by
    unfold moebiusPhi
    rw [hnum_l, hden_l]
    calc -omegaCube ^ 2 * (omegaCube * (u - omegaCube)) / (omegaCube * (u - omegaCube ^ 2))
        = (omegaCube * (-omegaCube ^ 2 * (u - omegaCube))) / (omegaCube * (u - omegaCube ^ 2)) := by
            ring_nf
      _ = (-omegaCube ^ 2 * (u - omegaCube)) / (u - omegaCube ^ 2) :=
            mul_div_mul_left _ _ omegaCube_ne_zero
  have hinv_neg_sq : (-omegaCube ^ 2)⁻¹ = -omegaCube := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc (-omegaCube ^ 2) * (-omegaCube) = omegaCube ^ 3 := by ring
      _ = 1 := omegaCube_pow_three
  have hrhs : moebiusM3 (moebiusPhi u) =
      (-omegaCube ^ 2 * (u - omegaCube)) / (u - omegaCube ^ 2) := by
    unfold moebiusM3 moebiusPhi
    have hdiv : 1 / (-omegaCube ^ 2 * (u - omegaCube ^ 2) / (u - 1)) =
        -(omegaCube * (u - 1)) / (u - omegaCube ^ 2) := by
      rw [one_div_div, mul_comm (-omegaCube ^ 2), ← div_div, div_eq_mul_inv _ (-omegaCube ^ 2),
        hinv_neg_sq]
      ring
    rw [hdiv, sub_eq_add_neg, neg_div, neg_neg, add_div' _ _ _ hu_sub_sq]
    congr 1
    have hsum : 1 + omegaCube + omegaCube ^ 2 = 0 := sum_omegaCube
    have h3 : omegaCube ^ 3 = 1 := omegaCube_pow_three
    linear_combination u * hsum - hsum - h3
  rw [hlhs, hrhs]

/-- Reflection equivariance of `moebiusPhi`: `Φ((conj u)⁻¹) = conj (Φ(u))` for `u ∉ {0, 1}`. -/
theorem moebiusPhi_inv_conj {u : ℂ} (hu0 : u ≠ 0) (_hu1 : u ≠ 1) :
    moebiusPhi ((starRingEnd ℂ u)⁻¹) = starRingEnd ℂ (moebiusPhi u) := by
  let c : ℂ := starRingEnd ℂ u
  have hc0 : c ≠ 0 := fun h => hu0 (by simpa [c] using congrArg (starRingEnd ℂ) h)
  have hstar_sq : starRingEnd ℂ (omegaCube ^ 2) = omegaCube := by
    rw [map_pow, star_omegaCube, ← pow_mul, show 2 * 2 = 4 by rfl, omegaCube_pow_four]
  have hrhs : starRingEnd ℂ (moebiusPhi u) = -omegaCube * (c - omegaCube) / (c - 1) := by
    unfold moebiusPhi
    rw [map_div₀, map_mul, map_neg, map_sub, map_sub, map_one, hstar_sq]
  have hsub1 : c⁻¹ - omegaCube ^ 2 = (1 - omegaCube ^ 2 * c) / c := by
    rw [inv_eq_one_div, div_sub' hc0]
    ring
  have hsub2 : c⁻¹ - 1 = (1 - c) / c := by
    rw [inv_eq_one_div, div_sub_one hc0]
  have hlhs : moebiusPhi (c⁻¹) = -omegaCube * (c - omegaCube) / (c - 1) := by
    unfold moebiusPhi
    rw [hsub1, hsub2, ← mul_div_assoc, div_div_div_cancel_right₀ hc0]
    have hnum : -omegaCube ^ 2 * (1 - omegaCube ^ 2 * c) = -(-omegaCube * (c - omegaCube)) := by
      calc -omegaCube ^ 2 * (1 - omegaCube ^ 2 * c)
          = omegaCube ^ 4 * c - omegaCube ^ 2 := by ring
        _ = omegaCube * c - omegaCube ^ 2 := by rw [omegaCube_pow_four]
        _ = -(-omegaCube * (c - omegaCube)) := by ring
    have hden : 1 - c = -(c - 1) := by ring
    rw [hnum, hden, neg_div_neg_eq]
  exact hlhs.trans hrhs.symm

theorem hasDerivAt_moebiusPhi {u : ℂ} (hu : u ≠ 1) :
    HasDerivAt moebiusPhi (-(omegaCube - omegaCube ^ 2) / (u - 1) ^ 2) u := by
  have hu1 : u - 1 ≠ 0 := sub_ne_zero.mpr hu
  have heq : ∀ᶠ z in 𝓝 u, moebiusPhi z =
      -omegaCube ^ 2 + (omegaCube - omegaCube ^ 2) * (z - 1)⁻¹ := by
    filter_upwards [isOpen_ne.mem_nhds hu] with z hz
    rw [← div_eq_mul_inv, ← moebiusPhi_add_omegaCube_sq hz]
    ring
  have hd_sub : HasDerivAt (fun z : ℂ => z - 1) 1 u :=
    hasDerivAt_id u |>.sub_const 1
  have hd_inv : HasDerivAt (fun z : ℂ => (z - 1)⁻¹) (-((u - 1) ^ 2)⁻¹ * 1) u :=
    HasDerivAt.comp u (hasDerivAt_inv hu1) hd_sub
  have hd_rhs : HasDerivAt (fun z : ℂ => -omegaCube ^ 2 + (omegaCube - omegaCube ^ 2) * (z - 1)⁻¹)
      (0 + (omegaCube - omegaCube ^ 2) * (-((u - 1) ^ 2)⁻¹ * 1)) u :=
    (hasDerivAt_const u (-omegaCube ^ 2)).add (hd_inv.const_mul (omegaCube - omegaCube ^ 2))
  have hd := hd_rhs.congr_of_eventuallyEq heq
  convert hd using 1
  ring

theorem moebiusPhi_holo_ne_one {u : ℂ} (hu : u ≠ 1) :
    DifferentiableAt ℂ moebiusPhi u :=
  (hasDerivAt_moebiusPhi hu).differentiableAt

/-- `lambdaRight` on `OmegaL1 = Q₀ ⊔ L₁ ⊔ Q₀⁻`: composed normalized Riemann map `Φ(ψ(z) / α_∞)` for
`Re z ≥ 0`, extended across `L₁` to `Q₀⁻` by Schwarz reflection `conj (Φ(ψ(-conj z) / α_∞))`. -/
def lambdaRight (z : ℂ) : ℂ :=
  if z.re < 0 then
    starRingEnd ℂ (moebiusPhi (riemannPsi (-starRingEnd ℂ z) / cuspAlphaInf))
  else
    moebiusPhi (psiExtL1 z / cuspAlphaInf)

theorem lambdaRight_of_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) :
    lambdaRight z = moebiusPhi (psiExtL1 z / cuspAlphaInf) := by
  have hnot : ¬ z.re < 0 := not_lt.mpr hz
  simp [lambdaRight, hnot]

theorem lambdaRight_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    lambdaRight z = moebiusPhi (riemannPsi z / cuspAlphaInf) := by
  rw [lambdaRight_of_re_nonneg hz.le, psiExtL1_of_re_pos hz]

theorem lambdaRight_of_re_neg {z : ℂ} (hz : z.re < 0) :
    lambdaRight z = starRingEnd ℂ (lambdaRight (-starRingEnd ℂ z)) := by
  have hpos : 0 < (-starRingEnd ℂ z).re := by simp [hz]
  rw [lambdaRight_of_re_pos hpos]
  simp [lambdaRight, hz]

theorem psiExtL1_div_cuspAlphaInf_ne_one {z : ℂ}
    (hz : z ∈ OmegaL1 \ {-starRingEnd ℂ z0Center}) :
    psiExtL1 z / cuspAlphaInf ≠ 1 := by
  rcases hz with ⟨hz_om, hz_not⟩
  intro h1
  have heq : psiExtL1 z = cuspAlphaInf := (div_eq_one_iff_eq cuspAlphaInf_ne_zero).mp h1
  by_cases hpos : 0 < z.re
  · have hzQ : z ∈ OpenTriangleQ0 := ⟨hz_om.1, hpos, hz_om.2.2.1, hz_om.2.2.2.1⟩
    rw [psiExtL1_of_re_pos hpos] at heq
    have hlt : ‖riemannPsi z‖ < 1 := by simpa [Metric.mem_ball] using riemannPsi_bij.mapsTo hzQ
    rw [heq, norm_cuspAlphaInf] at hlt
    exact lt_irrefl 1 hlt
  · by_cases hzero : z.re = 0
    · exact (psiExtL1_boundaryL1_notMem_cusps ⟨hzero, hz_om.1⟩).1 heq
    · have hneg : z.re < 0 := lt_of_le_of_ne (not_lt.mp hpos) hzero
      have hgt := one_lt_norm_psiExtL1_reflectedQ0 ⟨hz_om.1, hz_om.2.1, hneg, hz_om.2.2.2.2⟩ hz_not
      rw [heq, norm_cuspAlphaInf] at hgt
      exact lt_irrefl 1 hgt

theorem lambdaRight_eq_moebiusPhi_psiExtL1 {z : ℂ}
    (hz : z ∈ OmegaL1 \ {-starRingEnd ℂ z0Center}) :
    lambdaRight z = moebiusPhi (psiExtL1 z / cuspAlphaInf) := by
  by_cases hneg : z.re < 0
  · obtain ⟨hz_om, hz_not⟩ := hz
    have hR : z ∈ ReflectedQ0 := ⟨hz_om.1, hz_om.2.1, hneg, hz_om.2.2.2.2⟩
    have hwQ : -starRingEnd ℂ z ∈ OpenTriangleQ0 := neg_conj_mem_openTriangleQ0_iff.mpr hR
    have hw_ne : -starRingEnd ℂ z ≠ z0Center := by
      intro h
      apply hz_not
      have := congrArg (fun w => -starRingEnd ℂ w) h
      simpa using this
    have hpsi_nz : riemannPsi (-starRingEnd ℂ z) ≠ 0 :=
      fun h0 => hw_ne ((riemannPsi_eq_zero_iff hwQ).mp h0)
    let v : ℂ := riemannPsi (-starRingEnd ℂ z) / cuspAlphaInf
    have hv_nz : v ≠ 0 := div_ne_zero hpsi_nz cuspAlphaInf_ne_zero
    have hv_lt : ‖v‖ < 1 := by
      dsimp [v]
      rw [norm_div, norm_cuspAlphaInf, div_one]
      simpa [Metric.mem_ball] using riemannPsi_bij.mapsTo hwQ
    have hv_ne1 : v ≠ 1 := fun h => by rw [h, norm_one] at hv_lt; exact lt_irrefl 1 hv_lt
    have hstar_alpha : starRingEnd ℂ cuspAlphaInf = cuspAlphaInf⁻¹ := by
      apply mul_right_cancel₀ cuspAlphaInf_ne_zero
      rw [inv_mul_cancel₀ cuspAlphaInf_ne_zero, mul_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, norm_cuspAlphaInf, one_pow, Complex.ofReal_one]
    have hinv_v : (starRingEnd ℂ v)⁻¹ = psiExtL1 z / cuspAlphaInf := by
      rw [psiExtL1_of_re_neg hneg]
      dsimp [v]
      rw [map_div₀, inv_div, div_eq_mul_inv (starRingEnd ℂ _), mul_comm,
        hstar_alpha, ← div_eq_mul_inv]
    simp only [lambdaRight, hneg, ↓reduceIte]
    rw [← moebiusPhi_inv_conj hv_nz hv_ne1, hinv_v]
  · exact lambdaRight_of_re_nonneg (not_lt.mp hneg)

theorem lambdaRight_holo : RudinRCA.Chapter10.HolomorphicOn lambdaRight OmegaL1 := by
  intro z₀ hz₀
  by_cases hneg : z₀.re < 0
  · -- On the open set `ReflectedQ0`, `lambdaRight z = conj (lambdaRight (-conj z))`
    have hzR : z₀ ∈ ReflectedQ0 := ⟨hz₀.1, hz₀.2.1, hneg, hz₀.2.2.2.2⟩
    have hwQ : -starRingEnd ℂ z₀ ∈ OpenTriangleQ0 := neg_conj_mem_openTriangleQ0_iff.mpr hzR
    have hd_pos : DifferentiableAt ℂ
        (fun w => moebiusPhi (riemannPsi w / cuspAlphaInf)) (-starRingEnd ℂ z₀) := by
      have hu_lt : ‖riemannPsi (-starRingEnd ℂ z₀) / cuspAlphaInf‖ < 1 := by
        rw [norm_div, norm_cuspAlphaInf, div_one]
        simpa [Metric.mem_ball] using riemannPsi_bij.mapsTo hwQ
      have hu1 : riemannPsi (-starRingEnd ℂ z₀) / cuspAlphaInf ≠ 1 :=
        fun h => by rw [h, norm_one] at hu_lt; exact lt_irrefl 1 hu_lt
      exact DifferentiableAt.comp (-starRingEnd ℂ z₀) (moebiusPhi_holo_ne_one hu1)
        ((riemannPsi_holo _ hwQ).div_const cuspAlphaInf)
    have hd_refl := differentiableAt_conj_comp_neg_conj hd_pos
    refine hd_refl.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hneg] with z hz
    simp [lambdaRight, hz]
  · -- Off `-conj z₀`, `lambdaRight` agrees with `moebiusPhi (psiExtL1 z / cuspAlphaInf)`
    have hz_ne : z₀ ≠ -starRingEnd ℂ z0Center := by
      intro h
      rw [h] at hneg
      simp [z0Center_re] at hneg
    have hopen : IsOpen (OmegaL1 \ {-starRingEnd ℂ z0Center}) :=
      isOpen_omegaL1.sdiff isClosed_singleton
    have hmem : z₀ ∈ OmegaL1 \ {-starRingEnd ℂ z0Center} := ⟨hz₀, hz_ne⟩
    have hd_comp : DifferentiableAt ℂ (fun z => moebiusPhi (psiExtL1 z / cuspAlphaInf)) z₀ :=
      DifferentiableAt.comp z₀ (moebiusPhi_holo_ne_one (psiExtL1_div_cuspAlphaInf_ne_one hmem))
        ((psiExtL1_holo_off_neg_conj_z0 z₀ hmem).div_const cuspAlphaInf)
    refine hd_comp.congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact lambdaRight_eq_moebiusPhi_psiExtL1 hz

/-- `M₃` equivariance of `lambdaRight` on `Q₀`: `lambdaRight (M₃ z) = M₃ (lambdaRight z)`. -/
theorem lambdaRight_moebiusM3 {z : ℂ} (hz : z ∈ OpenTriangleQ0) :
    lambdaRight (moebiusM3 z) = moebiusM3 (lambdaRight z) := by
  have hmQ : moebiusM3 z ∈ OpenTriangleQ0 := moebiusM3_mapsTo_openTriangleQ0 hz
  rw [lambdaRight_of_re_pos hmQ.2.1, lambdaRight_of_re_pos hz.2.1, riemannPsi_moebiusM3 hz,
    mul_div_assoc]
  let u : ℂ := riemannPsi z / cuspAlphaInf
  have hu_lt : ‖u‖ < 1 := by
    dsimp [u]
    rw [norm_div, norm_cuspAlphaInf, div_one]
    simpa [Metric.mem_ball] using riemannPsi_bij.mapsTo hz
  have hu1 : u ≠ 1 := fun h => by rw [h, norm_one] at hu_lt; exact lt_irrefl 1 hu_lt
  have husq : u ≠ omegaCube ^ 2 := fun h => by
    rw [h, norm_pow, norm_omegaCube, one_pow] at hu_lt
    exact lt_irrefl 1 hu_lt
  exact moebiusPhi_mul_omegaCube hu1 husq

theorem lambdaRight_bijOn_openTriangleQ0 :
    Set.BijOn lambdaRight OpenTriangleQ0 UpperHalfPlaneSet := by
  have hdiv_bij : Set.BijOn (fun w : ℂ => w / cuspAlphaInf)
      (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      simpa [Metric.mem_ball, norm_div, norm_cuspAlphaInf] using hw
    · intro w₁ _ w₂ _ h
      have hm := congrArg (· * cuspAlphaInf) h
      simpa [div_mul_cancel₀ _ cuspAlphaInf_ne_zero] using hm
    · intro u hu
      refine ⟨u * cuspAlphaInf, ?_, mul_div_cancel_right₀ u cuspAlphaInf_ne_zero⟩
      simpa [Metric.mem_ball, norm_mul, norm_cuspAlphaInf] using hu
  have hcomp : Set.BijOn (fun z => moebiusPhi (riemannPsi z / cuspAlphaInf))
      OpenTriangleQ0 UpperHalfPlaneSet :=
    moebiusPhi_bijOn_unitBall.comp (hdiv_bij.comp riemannPsi_bij)
  exact hcomp.congr fun z hz => (lambdaRight_of_re_pos hz.2.1).symm

theorem lambdaRight_bijOn_reflectedQ0 :
    Set.BijOn lambdaRight ReflectedQ0 {w : ℂ | w.im < 0} := by
  have hrefl_bij : Set.BijOn (fun z : ℂ => -starRingEnd ℂ z) ReflectedQ0 OpenTriangleQ0 := by
    refine ⟨fun z hz => neg_conj_mem_openTriangleQ0_iff.mpr hz, ?_, ?_⟩
    · intro z₁ _ z₂ _ h
      have := congrArg (fun w : ℂ => -starRingEnd ℂ w) h
      simpa using this
    · intro w hw
      refine ⟨-starRingEnd ℂ w, ?_, by simp⟩
      exact neg_conj_mem_openTriangleQ0_iff.mp (by simpa using hw)
  have hconj_bij : Set.BijOn (starRingEnd ℂ) UpperHalfPlaneSet {w : ℂ | w.im < 0} := by
    refine ⟨?_, (starRingEnd ℂ).injective.injOn, ?_⟩
    · intro w hw
      change (starRingEnd ℂ w).im < 0
      simp [UpperHalfPlaneSet] at hw ⊢
      exact hw
    · intro w hw
      change w.im < 0 at hw
      refine ⟨starRingEnd ℂ w, ?_, Complex.conj_conj w⟩
      change 0 < (starRingEnd ℂ w).im
      simp; linarith
  have hcomp := hconj_bij.comp (lambdaRight_bijOn_openTriangleQ0.comp hrefl_bij)
  exact hcomp.congr fun z hz => (lambdaRight_of_re_neg hz.2.2.1).symm

/-- Cusp identity on `L₁` near `0`: for `0 < y` with `stripHeightY0 < 1 / y`,
`ω · psiExtL1 (i y) = psiStrip (1 + i / y)`. -/
theorem omega_mul_psiExtL1_eq_psiStrip_inv {y : ℝ} (hy_pos : 0 < y)
    (hy_inv : stripHeightY0 < 1 / y) :
    omegaCube * psiExtL1 ((y : ℂ) * Complex.I) =
      psiStrip (1 + ((1 / y : ℝ) : ℂ) * Complex.I) := by
  let p : ℂ := (y : ℂ) * Complex.I
  have hp_L1 : p ∈ BoundaryL1 := ⟨by simp [p], by simp [p, hy_pos]⟩
  have hp_om : p ∈ OmegaL1 \ {-starRingEnd ℂ z0Center} := by
    refine ⟨boundaryL1_subset_omegaL1 hp_L1, ?_⟩
    intro h; have := congrArg Complex.re h; simp [p] at this
  have hp_cont : ContinuousAt psiExtL1 p :=
    (psiExtL1_holo_off_neg_conj_z0 p hp_om).continuousAt
  let zT : ℂ := 1 + ((1 / y : ℝ) : ℂ) * Complex.I
  have hzT_im : stripHeightY0 < zT.im := by simpa [zT, one_div] using hy_inv
  have hzT_cont : ContinuousAt psiStrip zT :=
    (psiStrip_holo zT hzT_im).continuousAt
  let γ : ℝ → ℂ := fun x => (x : ℂ) + (y : ℂ) * Complex.I
  have hγ_p : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 p) := by
    have hc : Continuous γ := Complex.continuous_ofReal.add continuous_const
    simpa [γ, p] using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hp_nz : p ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [p, hy_pos.ne'] at this
  have hM3_p : moebiusM3 p = zT := by
    unfold moebiusM3
    dsimp [p, zT]
    have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy_pos.ne'
    rw [Complex.ofReal_div, Complex.ofReal_one]
    field_simp [hy_ne, Complex.I_ne_zero]
    ring_nf
    simp [Complex.I_sq]
    ring
  have hM3_γ : Tendsto (moebiusM3 ∘ γ) (𝓝[>] (0 : ℝ)) (𝓝 zT) := by
    rw [← hM3_p]
    exact (hasDerivAt_moebiusM3 hp_nz).continuousAt.tendsto.comp hγ_p
  -- For small `x > 0`, `γ x ∈ OpenTriangleQ0` and `(moebiusM3 (γ x)).im > stripHeightY0`
  have hev_Q : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), γ x ∈ OpenTriangleQ0 := by
    have hev_om : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), γ x ∈ OmegaL1 :=
      hγ_p.eventually (isOpen_omegaL1.mem_nhds hp_om.1)
    filter_upwards [self_mem_nhdsWithin, hev_om] with x hx_pos hx_om
    change 0 < x at hx_pos
    exact ⟨hx_om.1, by simp [γ, hx_pos], hx_om.2.2.1, hx_om.2.2.2.1⟩
  have hev_im : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), stripHeightY0 < (moebiusM3 (γ x)).im :=
    hM3_γ.eventually ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hzT_im)
  have hlim_lhs : Tendsto (fun x : ℝ => omegaCube * psiExtL1 (γ x)) (𝓝[>] (0 : ℝ))
      (𝓝 (omegaCube * psiExtL1 p)) :=
    (hp_cont.tendsto.comp hγ_p).const_mul omegaCube
  have hlim_rhs : Tendsto (fun x : ℝ => psiStrip (moebiusM3 (γ x))) (𝓝[>] (0 : ℝ))
      (𝓝 (psiStrip zT)) :=
    hzT_cont.tendsto.comp hM3_γ
  have hcongr : (fun x : ℝ => omegaCube * psiExtL1 (γ x)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun x : ℝ => psiStrip (moebiusM3 (γ x))) := by
    filter_upwards [hev_Q, hev_im] with x hxQ _
    have hmQ : moebiusM3 (γ x) ∈ OpenTriangleQ0 := moebiusM3_mapsTo_openTriangleQ0 hxQ
    rw [psiExtL1_of_re_pos hxQ.2.1, psiStrip_eq_riemannPsi hmQ, riemannPsi_moebiusM3 hxQ]
  exact tendsto_nhds_unique hlim_lhs (hlim_rhs.congr' hcongr.symm)

theorem tendsto_norm_lambdaRight_L1_atTop :
    Tendsto (fun y : ℝ => ‖lambdaRight ((y : ℂ) * Complex.I)‖) Filter.atTop Filter.atTop := by
  -- As `y → +∞`, `u(y) = psiExtL1 (i y) / α_∞ → 1`, so `‖moebiusPhi (u y)‖ → +∞`
  have hu_tend : Tendsto (fun y : ℝ => psiExtL1 ((y : ℂ) * Complex.I) / cuspAlphaInf)
      Filter.atTop (𝓝 1) := by
    have hstrip : Tendsto (fun y : ℝ => psiStrip ((y : ℂ) * Complex.I))
        Filter.atTop (𝓝 cuspAlphaInf) := by
      rw [cuspAlphaInf_eq_cuspFnF_zero]
      refine tendsto_psiStrip_im_atTop.comp ?_
      rw [Filter.tendsto_comap_iff]
      have : (Complex.im ∘ fun y : ℝ => (y : ℂ) * Complex.I) = id := by funext y; simp
      rw [this]; exact tendsto_id
    have hpsi : Tendsto (fun y : ℝ => psiExtL1 ((y : ℂ) * Complex.I))
        Filter.atTop (𝓝 cuspAlphaInf) := by
      refine hstrip.congr' ?_
      filter_upwards [Filter.Ioi_mem_atTop stripHeightY0] with y hy
      exact psiStrip_eq_psiExtL1 (by simp) (by simp)
    simpa [div_self cuspAlphaInf_ne_zero] using hpsi.div_const cuspAlphaInf
  rw [Filter.tendsto_atTop]
  intro M
  let numLim : ℂ := -omegaCube ^ 2 * (1 - omegaCube ^ 2)
  have hnum_eq : numLim = omegaCube - omegaCube ^ 2 := by
    dsimp [numLim]; rw [mul_sub, mul_one]; ring_nf; rw [omegaCube_pow_four]; ring
  have hnum_pos : 0 < ‖numLim‖ := norm_pos_iff.mpr (hnum_eq ▸ omegaCube_sub_sq_ne_zero)
  have hnum_tend : Tendsto (fun y : ℝ =>
        ‖-omegaCube ^ 2 * (psiExtL1 ((y : ℂ) * Complex.I) / cuspAlphaInf - omegaCube ^ 2)‖)
      Filter.atTop (𝓝 ‖numLim‖) :=
    (((hu_tend.sub_const (omegaCube ^ 2)).const_mul (-omegaCube ^ 2)).norm)
  have hden_tend : Tendsto (fun y : ℝ =>
        ‖psiExtL1 ((y : ℂ) * Complex.I) / cuspAlphaInf - 1‖)
      Filter.atTop (𝓝 0) := by
    simpa using (hu_tend.sub_const (1 : ℂ)).norm
  let B : ℝ := max M 1
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hev_num : ∀ᶠ y : ℝ in Filter.atTop,
      ‖numLim‖ / 2 < ‖-omegaCube ^ 2 * (psiExtL1 ((y : ℂ) * Complex.I) / cuspAlphaInf - omegaCube ^ 2)‖ :=
    hnum_tend.eventually (Ioi_mem_nhds (half_lt_self hnum_pos))
  have hev_den : ∀ᶠ y : ℝ in Filter.atTop,
      ‖psiExtL1 ((y : ℂ) * Complex.I) / cuspAlphaInf - 1‖ < (‖numLim‖ / 2) / B :=
    hden_tend.eventually (Iio_mem_nhds (div_pos (half_pos hnum_pos) hB_pos))
  filter_upwards [Filter.Ioi_mem_atTop (0 : ℝ), hev_num, hev_den] with y hy_pos hnum_gt hden_lt
  change 0 < y at hy_pos
  have hp_L1 : (y : ℂ) * Complex.I ∈ BoundaryL1 := ⟨by simp, by simp [hy_pos]⟩
  have hp_om : (y : ℂ) * Complex.I ∈ OmegaL1 \ {-starRingEnd ℂ z0Center} :=
    ⟨boundaryL1_subset_omegaL1 hp_L1, fun h => by have := congrArg Complex.re h; simp at this⟩
  have hden_pos : 0 < ‖psiExtL1 ((y : ℂ) * Complex.I) / cuspAlphaInf - 1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (psiExtL1_div_cuspAlphaInf_ne_one hp_om))
  rw [lambdaRight_of_re_nonneg (by simp)]
  unfold moebiusPhi
  rw [norm_div]
  have hB_le : B ≤ ‖-omegaCube ^ 2 * (psiExtL1 ((y : ℂ) * Complex.I) / cuspAlphaInf - omegaCube ^ 2)‖ /
      ‖psiExtL1 ((y : ℂ) * Complex.I) / cuspAlphaInf - 1‖ := by
    rw [le_div_iff₀ hden_pos]
    have : B * ‖psiExtL1 ((y : ℂ) * Complex.I) / cuspAlphaInf - 1‖ < ‖numLim‖ / 2 :=
      (lt_div_iff₀' hB_pos).mp hden_lt
    linarith
  exact le_trans (le_max_left M 1) hB_le

theorem tendsto_lambdaRight_L1_zero :
    Tendsto (fun y : ℝ => lambdaRight ((y : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- As `y → 0⁺`, `psiExtL1 (i y) / α_∞ → ω²`, and `moebiusPhi (ω²) = 0`
  have hinv_atTop : Tendsto (fun y : ℝ => 1 / y) (𝓝[>] (0 : ℝ)) Filter.atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero
  have hstrip : Tendsto (fun y : ℝ => psiStrip (1 + ((1 / y : ℝ) : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 cuspAlphaInf) := by
    rw [cuspAlphaInf_eq_cuspFnF_zero]
    refine tendsto_psiStrip_im_atTop.comp ?_
    rw [Filter.tendsto_comap_iff]
    have : (Complex.im ∘ fun y : ℝ => 1 + ((1 / y : ℝ) : ℂ) * Complex.I) = fun y => 1 / y := by
      funext y; simp
    rw [this]; exact hinv_atTop
  have hu_tend : Tendsto (fun y : ℝ => psiExtL1 ((y : ℂ) * Complex.I) / cuspAlphaInf)
      (𝓝[>] (0 : ℝ)) (𝓝 (omegaCube ^ 2)) := by
    have hpsi : Tendsto (fun y : ℝ => omegaCube ^ 2 * psiStrip (1 + ((1 / y : ℝ) : ℂ) * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 (omegaCube ^ 2 * cuspAlphaInf)) :=
      hstrip.const_mul (omegaCube ^ 2)
    have hpsi' : Tendsto (fun y : ℝ => psiExtL1 ((y : ℂ) * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 (omegaCube ^ 2 * cuspAlphaInf)) := by
      refine hpsi.congr' ?_
      filter_upwards [self_mem_nhdsWithin,
        hinv_atTop.eventually (Filter.Ioi_mem_atTop stripHeightY0)] with y hy_pos hy_inv
      rw [← omega_mul_psiExtL1_eq_psiStrip_inv hy_pos hy_inv, ← mul_assoc,
        ← pow_succ, omegaCube_pow_three, one_mul]
    simpa [mul_div_cancel_right₀ _ cuspAlphaInf_ne_zero] using hpsi'.div_const cuspAlphaInf
  have hphi_cont : ContinuousAt moebiusPhi (omegaCube ^ 2) :=
    (moebiusPhi_holo_ne_one omegaCube_sq_ne_one).continuousAt
  have hcomp : Tendsto (fun y : ℝ => moebiusPhi (psiExtL1 ((y : ℂ) * Complex.I) / cuspAlphaInf))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    change Tendsto (moebiusPhi ∘ fun y : ℝ => psiExtL1 ((y : ℂ) * Complex.I) / cuspAlphaInf)
      (𝓝[>] (0 : ℝ)) (𝓝 0)
    rw [← moebiusPhi_omegaCube_sq]
    exact hphi_cont.tendsto.comp hu_tend
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y _
  exact (lambdaRight_of_re_nonneg (by simp)).symm

/-- `lambdaRight` maps `BoundaryL1 = {i y : y > 0}` bijectively onto `(-∞, 0)`. -/
theorem lambdaRight_bijOn_boundaryL1 :
    Set.BijOn lambdaRight BoundaryL1 {w : ℂ | w.im = 0 ∧ w.re < 0} := by
  let g : ℝ → ℝ := fun y => (lambdaRight ((y : ℂ) * Complex.I)).re
  have hg_im : ∀ y : ℝ, 0 < y → (lambdaRight ((y : ℂ) * Complex.I)).im = 0 := by
    intro y hy
    have hp : (y : ℂ) * Complex.I ∈ BoundaryL1 := ⟨by simp, by simp [hy]⟩
    rw [lambdaRight_of_re_nonneg (by simp)]
    refine moebiusPhi_bijOn_unitCircle.mapsTo ⟨?_, ?_⟩
    · rw [Metric.mem_sphere, dist_zero_right, norm_div, norm_psiExtL1_boundaryL1 hp,
        norm_cuspAlphaInf, div_one]
    · intro h1
      exact (psiExtL1_boundaryL1_notMem_cusps hp).1
        ((div_eq_one_iff_eq cuspAlphaInf_ne_zero).mp h1)
  have hg_val : ∀ y : ℝ, 0 < y → lambdaRight ((y : ℂ) * Complex.I) = (g y : ℂ) := by
    intro y hy
    exact Complex.ext rfl (by simp [hg_im y hy])
  have hg_ne : ∀ y : ℝ, 0 < y → g y ≠ 0 ∧ g y ≠ 1 := by
    intro y hy
    have hp : (y : ℂ) * Complex.I ∈ BoundaryL1 := ⟨by simp, by simp [hy]⟩
    obtain ⟨hne_inf, hne_w, hne_w2⟩ := psiExtL1_boundaryL1_notMem_cusps hp
    let u : ℂ := psiExtL1 ((y : ℂ) * Complex.I) / cuspAlphaInf
    have hu_sph : u ∈ Metric.sphere (0 : ℂ) 1 \ {1} := by
      refine ⟨?_, fun h1 => hne_inf ((div_eq_one_iff_eq cuspAlphaInf_ne_zero).mp h1)⟩
      rw [Metric.mem_sphere, dist_zero_right, norm_div, norm_psiExtL1_boundaryL1 hp,
        norm_cuspAlphaInf, div_one]
    have hlam_eq : (g y : ℂ) = moebiusPhi u := by
      rw [← hg_val y hy, lambdaRight_of_re_nonneg (by simp)]
    refine ⟨?_, ?_⟩
    · intro h0
      rw [h0, Complex.ofReal_zero, ← moebiusPhi_omegaCube_sq] at hlam_eq
      have husq_sph : omegaCube ^ 2 ∈ Metric.sphere (0 : ℂ) 1 \ {1} :=
        ⟨by rw [Metric.mem_sphere, dist_zero_right, norm_pow, norm_omegaCube, one_pow],
         omegaCube_sq_ne_one⟩
      have hu_eq := moebiusPhi_bijOn_unitCircle.injOn husq_sph hu_sph hlam_eq
      exact hne_w2 ((div_eq_iff cuspAlphaInf_ne_zero).mp hu_eq.symm)
    · intro h1
      rw [h1, Complex.ofReal_one, ← moebiusPhi_omegaCube] at hlam_eq
      have hw_sph : omegaCube ∈ Metric.sphere (0 : ℂ) 1 \ {1} :=
        ⟨by rw [Metric.mem_sphere, dist_zero_right, norm_omegaCube], omegaCube_ne_one⟩
      have hu_eq := moebiusPhi_bijOn_unitCircle.injOn hw_sph hu_sph hlam_eq
      exact hne_w ((div_eq_iff cuspAlphaInf_ne_zero).mp hu_eq.symm)
  have hg_cont : ContinuousOn g (Set.Ioi (0 : ℝ)) := by
    intro y hy
    change 0 < y at hy
    have hp_om : (y : ℂ) * Complex.I ∈ OmegaL1 :=
      boundaryL1_subset_omegaL1 ⟨by simp, by simp [hy]⟩
    have hlin : Continuous (fun t : ℝ => (t : ℂ) * Complex.I) :=
      Complex.continuous_ofReal.mul continuous_const
    have hc : ContinuousAt (Complex.re ∘ lambdaRight ∘ fun t : ℝ => (t : ℂ) * Complex.I) y :=
      ContinuousAt.comp Complex.continuous_re.continuousAt
        (ContinuousAt.comp (f := fun t : ℝ => (t : ℂ) * Complex.I)
          (lambdaRight_holo _ hp_om).continuousAt hlin.continuousAt)
    exact hc.continuousWithinAt
  have hg_zero : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    show Tendsto (Complex.re ∘ fun y : ℝ => lambdaRight ((y : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ).re) from
      Complex.continuous_re.continuousAt.tendsto.comp tendsto_lambdaRight_L1_zero
  have hg_abs_top : Tendsto (fun y : ℝ => |g y|) Filter.atTop Filter.atTop := by
    refine tendsto_norm_lambdaRight_L1_atTop.congr' ?_
    filter_upwards [Filter.Ioi_mem_atTop (0 : ℝ)] with y hy
    rw [hg_val y hy, Complex.norm_real, Real.norm_eq_abs]
  -- Deduce `g y < 0` for every `y > 0`
  have hg_neg : ∀ y₀ : ℝ, 0 < y₀ → g y₀ < 0 := by
    intro y₀ hy₀
    rcases lt_trichotomy (g y₀) 0 with hlt | heq | hgt
    · exact hlt
    · exact False.elim ((hg_ne y₀ hy₀).1 heq)
    · -- If `g y₀ > 0`, then `g > 0` on all of `(0, ∞)` by IVT since `0 ∉ g '' (0, ∞)`
      have hall_pos : ∀ y : ℝ, 0 < y → 0 < g y := by
        intro y hy
        rcases lt_trichotomy (g y) 0 with hy_lt | hy_eq | hy_gt
        · have huIcc_sub : Set.uIcc y y₀ ⊆ Set.Ioi (0 : ℝ) := by
            intro t ht; exact lt_of_lt_of_le (lt_min hy hy₀) ht.1
          have hmem0 : (0 : ℝ) ∈ g '' Set.uIcc y y₀ :=
            intermediate_value_uIcc (hg_cont.mono huIcc_sub)
              ⟨le_of_lt (min_lt_iff.mpr (Or.inl hy_lt)), le_of_lt (lt_max_iff.mpr (Or.inr hgt))⟩
          rcases hmem0 with ⟨t, ht, hgt0⟩
          exact False.elim ((hg_ne t (huIcc_sub ht)).1 hgt0)
        · exact False.elim ((hg_ne y hy).1 hy_eq)
        · exact hy_gt
      -- Pick `y₁ > 0` with `g y₁ < 1/2` (from `g → 0`) and `y₂ > 0` with `g y₂ ≥ 2` (from `|g| → ∞`)
      obtain ⟨y₁, hy₁_pos, hy₁_lt⟩ : ∃ y₁ : ℝ, 0 < y₁ ∧ g y₁ < 1 / 2 := by
        have hev := hg_zero.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
        rcases (hev.and self_mem_nhdsWithin).exists with ⟨y₁, hlt1, hy₁⟩
        exact ⟨y₁, hy₁, hlt1⟩
      obtain ⟨y₂, hy₂_pos, hy₂_ge⟩ : ∃ y₂ : ℝ, 0 < y₂ ∧ 2 ≤ |g y₂| := by
        have hev := (Filter.tendsto_atTop.mp hg_abs_top 2).and (Filter.Ioi_mem_atTop (0 : ℝ))
        rcases hev.exists with ⟨y₂, hge2, hy₂⟩
        exact ⟨y₂, hy₂, hge2⟩
      have hy₂_gt1 : 1 < g y₂ := by
        have hpos2 := hall_pos y₂ hy₂_pos
        rw [abs_of_pos hpos2] at hy₂_ge
        linarith
      have huIcc_sub : Set.uIcc y₁ y₂ ⊆ Set.Ioi (0 : ℝ) := by
        intro t ht; exact lt_of_lt_of_le (lt_min hy₁_pos hy₂_pos) ht.1
      have hmem1 : (1 : ℝ) ∈ g '' Set.uIcc y₁ y₂ :=
        intermediate_value_uIcc (hg_cont.mono huIcc_sub)
          ⟨by linarith [min_le_left (g y₁) (g y₂)], by linarith [le_max_right (g y₁) (g y₂)]⟩
      rcases hmem1 with ⟨t, ht, hgt1⟩
      exact False.elim ((hg_ne t (huIcc_sub ht)).2 hgt1)
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have hp_eq : p = (p.im : ℂ) * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im p, hp.1]; simp
    rw [hp_eq]
    exact ⟨hg_im p.im hp.2, hg_neg p.im hp.2⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    rw [lambdaRight_of_re_nonneg (by linarith [hp₁.1]),
      lambdaRight_of_re_nonneg (by linarith [hp₂.1])] at heq
    have hu₁_sph : psiExtL1 p₁ / cuspAlphaInf ∈ Metric.sphere (0 : ℂ) 1 \ {1} :=
      ⟨by rw [Metric.mem_sphere, dist_zero_right, norm_div, norm_psiExtL1_boundaryL1 hp₁,
          norm_cuspAlphaInf, div_one],
       fun h1 => (psiExtL1_boundaryL1_notMem_cusps hp₁).1
        ((div_eq_one_iff_eq cuspAlphaInf_ne_zero).mp h1)⟩
    have hu₂_sph : psiExtL1 p₂ / cuspAlphaInf ∈ Metric.sphere (0 : ℂ) 1 \ {1} :=
      ⟨by rw [Metric.mem_sphere, dist_zero_right, norm_div, norm_psiExtL1_boundaryL1 hp₂,
          norm_cuspAlphaInf, div_one],
       fun h1 => (psiExtL1_boundaryL1_notMem_cusps hp₂).1
        ((div_eq_one_iff_eq cuspAlphaInf_ne_zero).mp h1)⟩
    have hdiv_eq := moebiusPhi_bijOn_unitCircle.injOn hu₁_sph hu₂_sph heq
    have hpsi_eq : psiExtL1 p₁ = psiExtL1 p₂ := by
      have hm := congrArg (· * cuspAlphaInf) hdiv_eq
      simpa [div_mul_cancel₀ _ cuspAlphaInf_ne_zero] using hm
    exact injOn_psiExtL1_boundaryL1 hp₁ hp₂ hpsi_eq
  · rintro w ⟨hw_im, hw_re⟩
    -- Find `y > 0` with `g y = w.re < 0` by IVT
    obtain ⟨y₁, hy₁_pos, hy₁_gt⟩ : ∃ y₁ : ℝ, 0 < y₁ ∧ w.re < g y₁ := by
      have hev := hg_zero.eventually (Ioi_mem_nhds hw_re)
      rcases (hev.and self_mem_nhdsWithin).exists with ⟨y₁, hgt, hy₁⟩
      exact ⟨y₁, hy₁, hgt⟩
    obtain ⟨y₂, hy₂_pos, hy₂_ge⟩ : ∃ y₂ : ℝ, 0 < y₂ ∧ -w.re + 1 ≤ |g y₂| := by
      have hev := (Filter.tendsto_atTop.mp hg_abs_top (-w.re + 1)).and (Filter.Ioi_mem_atTop (0 : ℝ))
      rcases hev.exists with ⟨y₂, hge, hy₂⟩
      exact ⟨y₂, hy₂, hge⟩
    have hy₂_lt : g y₂ < w.re := by
      have hneg2 := hg_neg y₂ hy₂_pos
      rw [abs_of_neg hneg2] at hy₂_ge
      linarith
    have huIcc_sub : Set.uIcc y₂ y₁ ⊆ Set.Ioi (0 : ℝ) := by
      intro t ht; exact lt_of_lt_of_le (lt_min hy₂_pos hy₁_pos) ht.1
    have hmem_w : w.re ∈ g '' Set.uIcc y₂ y₁ :=
      intermediate_value_uIcc (hg_cont.mono huIcc_sub)
        ⟨by linarith [min_le_left (g y₂) (g y₁)], by linarith [le_max_right (g y₂) (g y₁)]⟩
    rcases hmem_w with ⟨y, hy_mem, hgy⟩
    have hy_pos : 0 < y := huIcc_sub hy_mem
    refine ⟨(y : ℂ) * Complex.I, ⟨by simp, by simp [hy_pos]⟩, ?_⟩
    rw [hg_val y hy_pos, hgy]
    exact Complex.ext (by simp) (by simp [hw_im])

/-- `lambdaRight` is globally injective on `OmegaL1 = Q₀ ⊔ L₁ ⊔ Q₀⁻`, mapping it bijectively onto
`ℂ \ [0, +∞)`. -/
theorem lambdaRight_bijOn_omegaL1 :
    Set.BijOn lambdaRight OmegaL1 {w : ℂ | w.im ≠ 0 ∨ w.re < 0} := by
  have hpart : ∀ z ∈ OmegaL1,
      (0 < z.re → z ∈ OpenTriangleQ0 ∧ (lambdaRight z).im > 0) ∧
      (z.re = 0 → z ∈ BoundaryL1 ∧ (lambdaRight z).im = 0 ∧ (lambdaRight z).re < 0) ∧
      (z.re < 0 → z ∈ ReflectedQ0 ∧ (lambdaRight z).im < 0) := by
    intro z hz
    refine ⟨?_, ?_, ?_⟩
    · intro hp
      have hQ : z ∈ OpenTriangleQ0 := ⟨hz.1, hp, hz.2.2.1, hz.2.2.2.1⟩
      exact ⟨hQ, lambdaRight_bijOn_openTriangleQ0.mapsTo hQ⟩
    · intro h0
      have hL : z ∈ BoundaryL1 := ⟨h0, hz.1⟩
      exact ⟨hL, lambdaRight_bijOn_boundaryL1.mapsTo hL⟩
    · intro hn
      have hR : z ∈ ReflectedQ0 := ⟨hz.1, hz.2.1, hn, hz.2.2.2.2⟩
      exact ⟨hR, lambdaRight_bijOn_reflectedQ0.mapsTo hR⟩
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rcases lt_trichotomy z.re 0 with hn | h0 | hp
    · exact Or.inl ((hpart z hz).2.2 hn).2.ne
    · exact Or.inr ((hpart z hz).2.1 h0).2.2
    · exact Or.inl ((hpart z hz).1 hp).2.ne'
  · intro z₁ hz₁ z₂ hz₂ heq
    rcases lt_trichotomy z₁.re 0 with hn₁ | h0₁ | hp₁ <;>
      rcases lt_trichotomy z₂.re 0 with hn₂ | h0₂ | hp₂
    · exact lambdaRight_bijOn_reflectedQ0.injOn ((hpart z₁ hz₁).2.2 hn₁).1
        ((hpart z₂ hz₂).2.2 hn₂).1 heq
    · have him1 := ((hpart z₁ hz₁).2.2 hn₁).2
      have him2 := ((hpart z₂ hz₂).2.1 h0₂).2.1
      rw [heq] at him1; linarith
    · have him1 := ((hpart z₁ hz₁).2.2 hn₁).2
      have him2 := ((hpart z₂ hz₂).1 hp₂).2
      rw [heq] at him1; linarith
    · have him1 := ((hpart z₁ hz₁).2.1 h0₁).2.1
      have him2 := ((hpart z₂ hz₂).2.2 hn₂).2
      rw [heq] at him1; linarith
    · exact lambdaRight_bijOn_boundaryL1.injOn ((hpart z₁ hz₁).2.1 h0₁).1
        ((hpart z₂ hz₂).2.1 h0₂).1 heq
    · have him1 := ((hpart z₁ hz₁).2.1 h0₁).2.1
      have him2 := ((hpart z₂ hz₂).1 hp₂).2
      rw [heq] at him1; linarith
    · have him1 := ((hpart z₁ hz₁).1 hp₁).2
      have him2 := ((hpart z₂ hz₂).2.2 hn₂).2
      rw [heq] at him1; linarith
    · have him1 := ((hpart z₁ hz₁).1 hp₁).2
      have him2 := ((hpart z₂ hz₂).2.1 h0₂).2.1
      rw [heq] at him1; linarith
    · exact lambdaRight_bijOn_openTriangleQ0.injOn ((hpart z₁ hz₁).1 hp₁).1
        ((hpart z₂ hz₂).1 hp₂).1 heq
  · intro w hw
    rcases lt_trichotomy w.im 0 with hn | h0 | hp
    · obtain ⟨z, hzR, hzw⟩ := lambdaRight_bijOn_reflectedQ0.surjOn hn
      exact ⟨z, reflectedQ0_subset_omegaL1 hzR, hzw⟩
    · have hw_re : w.re < 0 := hw.resolve_left (not_not.mpr h0)
      obtain ⟨z, hzL, hzw⟩ := lambdaRight_bijOn_boundaryL1.surjOn ⟨h0, hw_re⟩
      exact ⟨z, boundaryL1_subset_omegaL1 hzL, hzw⟩
    · obtain ⟨z, hzQ, hzw⟩ := lambdaRight_bijOn_openTriangleQ0.surjOn hp
      exact ⟨z, openTriangleQ0_subset_omegaL1 hzQ, hzw⟩

theorem deriv_lambdaRight_ne_zero {z : ℂ} (hz : z ∈ OmegaL1) :
    deriv lambdaRight z ≠ 0 :=
  (RudinRCA.Chapter10.theorem10_33.1 isOpen_omegaL1 lambdaRight_holo
    lambdaRight_bijOn_omegaL1.injOn).1 z hz

/-- Left vertical boundary ray `BoundaryL3Minus = {z : Re z = -1, Im z > 0}` of `FundamentalSetQ`. -/
def BoundaryL3Minus : Set ℂ :=
  {z : ℂ | z.re = -1 ∧ 0 < z.im}

/-- Left semicircular boundary arc `BoundaryL2Minus = {z : Im z > 0, ‖2 z + 1‖ = 1}` of `Q`. -/
def BoundaryL2Minus : Set ℂ :=
  {z : ℂ | 0 < z.im ∧ ‖2 * z + 1‖ = 1}

theorem boundaryL3Minus_subset_fundamentalSetQ :
    BoundaryL3Minus ⊆ FundamentalSetQ := by
  rintro z ⟨hre, him⟩
  refine ⟨him, by linarith, by linarith, ?_, ?_⟩
  · rw [one_le_norm_two_mul_add_one_iff, hre]; nlinarith
  · rw [one_lt_norm_two_mul_sub_one_iff, hre]; nlinarith

theorem boundaryL2Minus_re_bounds {z : ℂ} (hz : z ∈ BoundaryL2Minus) :
    -1 < z.re ∧ z.re < 0 := by
  obtain ⟨him, hnorm⟩ := hz
  rw [norm_two_mul_add_one_eq_one_iff] at hnorm
  have him_sq : 0 < z.im ^ 2 := sq_pos_of_pos him
  constructor <;> nlinarith [sq_nonneg (z.re + 1)]

theorem boundaryL2Minus_subset_fundamentalSetQ :
    BoundaryL2Minus ⊆ FundamentalSetQ := by
  intro z hz
  obtain ⟨hgt, hlt⟩ := boundaryL2Minus_re_bounds hz
  refine ⟨hz.1, hgt.le, by linarith, by rw [hz.2], ?_⟩
  rw [one_lt_norm_two_mul_sub_one_iff]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

/-- Extension `lambdaOnQ` of `lambdaRight` to all of `FundamentalSetQ = OmegaL1 ⊔ L₃⁻ ⊔ L₂⁻`. -/
def lambdaOnQ (z : ℂ) : ℂ :=
  if z.re = -1 then
    moebiusM3 (lambdaRight (-1 / (z + 1)))
  else if ‖2 * z + 1‖ = 1 then
    moebiusM3 (moebiusM3 (lambdaRight (-1 - 1 / z)))
  else
    lambdaRight z

theorem lambdaOnQ_eq_lambdaRight {z : ℂ} (hz : z ∈ OmegaL1) :
    lambdaOnQ z = lambdaRight z := by
  have h1 : z.re ≠ -1 := hz.2.1.ne'
  have h2 : ‖2 * z + 1‖ ≠ 1 := hz.2.2.2.2.ne'
  simp [lambdaOnQ, h1, h2]

theorem wMap2_re_im {z : ℂ} (hz : z ≠ 0) :
    (-1 - 1 / z).re = -(‖2 * z + 1‖ ^ 2 - 1) / (4 * Complex.normSq z) ∧
    (-1 - 1 / z).im = z.im / Complex.normSq z := by
  have hnsq_pos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have hsq := norm_two_mul_add_one_sq z
  have hnsq : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by rw [Complex.normSq_apply]; ring
  refine ⟨?_, ?_⟩
  · simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, one_div, Complex.inv_re]
    field_simp [hnsq_pos.ne']
    rw [hsq, hnsq]
    ring
  · simp only [Complex.sub_im, Complex.neg_im, Complex.one_im, one_div, Complex.inv_im]
    ring

theorem lambdaOnQ_bijOn_boundaryL3Minus :
    Set.BijOn lambdaOnQ BoundaryL3Minus {w : ℂ | w.im = 0 ∧ 1 < w.re} := by
  have hinv_bij : Set.BijOn (fun z : ℂ => -1 / (z + 1)) BoundaryL3Minus BoundaryL1 := by
    refine ⟨?_, ?_, ?_⟩
    · rintro z ⟨hre, him⟩
      have hz_eq : z + 1 = (z.im : ℂ) * Complex.I :=
        Complex.ext (by simp [hre]) (by simp)
      have him_ne : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr him.ne'
      have hval : -1 / (z + 1) = ((1 / z.im : ℝ) : ℂ) * Complex.I := by
        rw [hz_eq, Complex.ofReal_div, Complex.ofReal_one]
        field_simp [him_ne, Complex.I_ne_zero]; ring_nf; simp [Complex.I_sq]
      dsimp only
      rw [hval]
      exact ⟨by simp, by simp; exact him⟩
    · rintro z₁ ⟨_, him₁⟩ z₂ ⟨_, him₂⟩ heq
      dsimp only at heq
      have h1 : z₁ + 1 ≠ 0 := fun h => by
        have := congrArg Complex.im h; simp [him₁.ne'] at this
      have h2 : z₂ + 1 ≠ 0 := fun h => by
        have := congrArg Complex.im h; simp [him₂.ne'] at this
      have h_eq : z₁ + 1 = z₂ + 1 := by
        field_simp [h1, h2] at heq
        linear_combination heq
      exact add_right_cancel h_eq
    · rintro p ⟨hp_re, hp_im⟩
      have hp_nz : p ≠ 0 := fun h => by rw [h, Complex.zero_im] at hp_im; exact lt_irrefl 0 hp_im
      let z : ℂ := -1 - 1 / p
      have hz_p : -1 / (z + 1) = p := by
        dsimp [z]; field_simp [hp_nz]; ring
      have hp_eq : p = (p.im : ℂ) * Complex.I := by
        conv_lhs => rw [← Complex.re_add_im p, hp_re]; simp
      have hz_mem : z ∈ BoundaryL3Minus := by
        dsimp [z]
        rw [hp_eq]
        have him_ne : (p.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp_im.ne'
        have hinv : 1 / ((p.im : ℂ) * Complex.I) = -((1 / p.im : ℝ) : ℂ) * Complex.I := by
          rw [Complex.ofReal_div, Complex.ofReal_one]
          field_simp [him_ne, Complex.I_ne_zero]; ring_nf; simp [Complex.I_sq]
        rw [hinv]
        exact ⟨by simp, by simp; exact hp_im⟩
      exact ⟨z, hz_mem, hz_p⟩
  have hM3_bij : Set.BijOn moebiusM3 {w : ℂ | w.im = 0 ∧ w.re < 0} {w : ℂ | w.im = 0 ∧ 1 < w.re} := by
    refine ⟨?_, ?_, ?_⟩
    · rintro w ⟨hw_im, hw_re⟩
      have hw_eq : w = (w.re : ℂ) := Complex.ext rfl (by simp [hw_im])
      have hw_nz : (w.re : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw_re.ne
      rw [hw_eq]
      unfold moebiusM3
      rw [← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_sub]
      refine ⟨by simp, ?_⟩
      simp only [Complex.ofReal_re]
      have hneg_inv : 0 < -(1 / w.re) := neg_pos.mpr (one_div_neg.mpr hw_re)
      linarith
    · rintro w₁ ⟨_, hw₁_re⟩ w₂ ⟨_, hw₂_re⟩ heq
      have hw₁0 : w₁ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw₁_re; exact lt_irrefl 0 hw₁_re
      have hw₁1 : w₁ ≠ 1 := fun h => by rw [h, Complex.one_re] at hw₁_re; norm_num at hw₁_re
      have hw₂0 : w₂ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw₂_re; exact lt_irrefl 0 hw₂_re
      have hw₂1 : w₂ ≠ 1 := fun h => by rw [h, Complex.one_re] at hw₂_re; norm_num at hw₂_re
      calc w₁ = moebiusM3 (moebiusM3 (moebiusM3 w₁)) := (moebiusM3_iter3 hw₁0 hw₁1).symm
        _ = moebiusM3 (moebiusM3 (moebiusM3 w₂)) := by rw [heq]
        _ = w₂ := moebiusM3_iter3 hw₂0 hw₂1
    · rintro y ⟨hy_im, hy_re⟩
      have hy_eq : y = (y.re : ℂ) := Complex.ext rfl (by simp [hy_im])
      let x : ℝ := 1 / (1 - y.re)
      have hx_neg : x < 0 := one_div_neg.mpr (by linarith)
      refine ⟨(x : ℂ), ⟨by simp, by simp [hx_neg]⟩, ?_⟩
      unfold moebiusM3
      dsimp [x]
      have h1y : (1 : ℂ) - (y.re : ℂ) ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      push_cast
      field_simp [h1y]
      rw [← hy_eq]
      ring
  have hcomp := hM3_bij.comp (lambdaRight_bijOn_boundaryL1.comp hinv_bij)
  exact hcomp.congr fun z hz => by simp [lambdaOnQ, hz.1]

theorem lambdaOnQ_bijOn_boundaryL2Minus :
    Set.BijOn lambdaOnQ BoundaryL2Minus {w : ℂ | w.im = 0 ∧ 0 < w.re ∧ w.re < 1} := by
  have hw2_bij : Set.BijOn (fun z : ℂ => -1 - 1 / z) BoundaryL2Minus BoundaryL1 := by
    refine ⟨?_, ?_, ?_⟩
    · rintro z ⟨him, hnorm⟩
      have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_im] at him; exact lt_irrefl 0 him
      obtain ⟨hre_w, him_w⟩ := wMap2_re_im hz0
      refine ⟨by rw [hre_w, hnorm]; norm_num, ?_⟩
      rw [him_w]
      exact div_pos him (Complex.normSq_pos.mpr hz0)
    · rintro z₁ ⟨him₁, _⟩ z₂ ⟨him₂, _⟩ heq
      have hz₁0 : z₁ ≠ 0 := fun h => by rw [h, Complex.zero_im] at him₁; exact lt_irrefl 0 him₁
      have hz₂0 : z₂ ≠ 0 := fun h => by rw [h, Complex.zero_im] at him₂; exact lt_irrefl 0 him₂
      have hinv_eq : 1 / z₁ = 1 / z₂ := by
        dsimp only at heq
        linear_combination -heq
      exact inv_injective (by simpa [one_div] using hinv_eq)
    · rintro p ⟨hp_re, hp_im⟩
      let z : ℂ := -1 / (p + 1)
      have hp1_nz : p + 1 ≠ 0 := fun h => by
        have := congrArg Complex.im h; simp [hp_im.ne'] at this
      have hz0 : z ≠ 0 := div_ne_zero (by norm_num) hp1_nz
      have hz_inv : -1 - 1 / z = p := by
        dsimp [z]; field_simp [hp1_nz]; ring
      have hz_im : 0 < z.im := by
        have hnsq : 0 < Complex.normSq (p + 1) := Complex.normSq_pos.mpr hp1_nz
        dsimp [z]
        have him_eq : (-1 / (p + 1)).im = p.im / Complex.normSq (p + 1) := by
          simp [neg_div, one_div, Complex.inv_im]
        rw [him_eq]
        exact div_pos hp_im hnsq
      have hz_norm : ‖2 * z + 1‖ = 1 := by
        obtain ⟨hre_w, _⟩ := wMap2_re_im hz0
        rw [hz_inv, hp_re] at hre_w
        have hnsq_pos : (0 : ℝ) < 4 * Complex.normSq z :=
          mul_pos (by norm_num) (Complex.normSq_pos.mpr hz0)
        have hsq1 : ‖2 * z + 1‖ ^ 2 = 1 := by
          have := (div_eq_zero_iff.mp hre_w.symm).resolve_right hnsq_pos.ne'
          linarith
        nlinarith [norm_nonneg (2 * z + 1)]
      exact ⟨z, ⟨hz_im, hz_norm⟩, hz_inv⟩
  have hM32_bij : Set.BijOn (fun w => moebiusM3 (moebiusM3 w))
      {w : ℂ | w.im = 0 ∧ w.re < 0} {w : ℂ | w.im = 0 ∧ 0 < w.re ∧ w.re < 1} := by
    refine ⟨?_, ?_, ?_⟩
    · rintro w ⟨hw_im, hw_re⟩
      have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw_re; exact lt_irrefl 0 hw_re
      have hw1 : w ≠ 1 := fun h => by rw [h, Complex.one_re] at hw_re; norm_num at hw_re
      dsimp only
      rw [moebiusM3_iter2 hw0 hw1]
      have hw_eq : w = (w.re : ℂ) := Complex.ext rfl (by simp [hw_im])
      rw [hw_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div]
      refine ⟨by simp, ?_, ?_⟩
      · simp only [Complex.ofReal_re]
        exact one_div_pos.mpr (by linarith)
      · simp only [Complex.ofReal_re]
        exact (div_lt_one (by linarith)).mpr (by linarith)
    · rintro w₁ ⟨_, hw₁_re⟩ w₂ ⟨_, hw₂_re⟩ heq
      dsimp only at heq
      have hw₁0 : w₁ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw₁_re; exact lt_irrefl 0 hw₁_re
      have hw₁1 : w₁ ≠ 1 := fun h => by rw [h, Complex.one_re] at hw₁_re; norm_num at hw₁_re
      have hw₂0 : w₂ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw₂_re; exact lt_irrefl 0 hw₂_re
      have hw₂1 : w₂ ≠ 1 := fun h => by rw [h, Complex.one_re] at hw₂_re; norm_num at hw₂_re
      calc w₁ = moebiusM3 (moebiusM3 (moebiusM3 w₁)) := (moebiusM3_iter3 hw₁0 hw₁1).symm
        _ = moebiusM3 (moebiusM3 (moebiusM3 w₂)) := by rw [heq]
        _ = w₂ := moebiusM3_iter3 hw₂0 hw₂1
    · rintro y ⟨hy_im, hy0, hy1⟩
      have hy_eq : y = (y.re : ℂ) := Complex.ext rfl (by simp [hy_im])
      let x : ℝ := 1 - 1 / y.re
      have hx_neg : x < 0 := by
        dsimp [x]
        have : 1 < 1 / y.re := (one_lt_div hy0).mpr hy1
        linarith
      have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_neg.ne
      have hx1 : (x : ℂ) ≠ 1 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      refine ⟨(x : ℂ), ⟨by simp, by simp [hx_neg]⟩, ?_⟩
      dsimp only
      rw [moebiusM3_iter2 hx0 hx1]
      dsimp [x]
      have hy_nz : (y.re : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy0.ne'
      push_cast
      field_simp [hy_nz]
      rw [← hy_eq]
      ring
  have hcomp := hM32_bij.comp (lambdaRight_bijOn_boundaryL1.comp hw2_bij)
  refine hcomp.congr fun z hz => ?_
  have hre_ne : z.re ≠ -1 := (boundaryL2Minus_re_bounds hz).1.ne'
  simp [lambdaOnQ, hre_ne, hz.2]

/-- `lambdaOnQ` maps `FundamentalSetQ` bijectively onto `ℂ \ {0, 1}`. -/
theorem lambdaOnQ_bijOn_fundamentalSetQ :
    Set.BijOn lambdaOnQ FundamentalSetQ (Set.univ \ {0, 1}) := by
  -- Classify each `z ∈ FundamentalSetQ` into one of the three pairwise-disjoint pieces
  have hclass : ∀ z ∈ FundamentalSetQ,
      (z.re = -1 → z ∈ BoundaryL3Minus ∧
        (lambdaOnQ z).im = 0 ∧ 1 < (lambdaOnQ z).re) ∧
      (z.re ≠ -1 → ‖2 * z + 1‖ = 1 → z ∈ BoundaryL2Minus ∧
        (lambdaOnQ z).im = 0 ∧ 0 < (lambdaOnQ z).re ∧ (lambdaOnQ z).re < 1) ∧
      (z.re ≠ -1 → ‖2 * z + 1‖ ≠ 1 → z ∈ OmegaL1 ∧
        ((lambdaOnQ z).im ≠ 0 ∨ (lambdaOnQ z).re < 0)) := by
    intro z hz
    refine ⟨?_, ?_, ?_⟩
    · intro hre
      have hm : z ∈ BoundaryL3Minus := ⟨hre, hz.1⟩
      exact ⟨hm, lambdaOnQ_bijOn_boundaryL3Minus.mapsTo hm⟩
    · intro _ hnorm
      have hm : z ∈ BoundaryL2Minus := ⟨hz.1, hnorm⟩
      exact ⟨hm, lambdaOnQ_bijOn_boundaryL2Minus.mapsTo hm⟩
    · intro hre hnorm
      have hm : z ∈ OmegaL1 :=
        ⟨hz.1, lt_of_le_of_ne hz.2.1 (Ne.symm hre), hz.2.2.1, hz.2.2.2.2,
         lt_of_le_of_ne hz.2.2.2.1 (Ne.symm hnorm)⟩
      have hw := lambdaRight_bijOn_omegaL1.mapsTo hm
      rw [← lambdaOnQ_eq_lambdaRight hm] at hw
      exact ⟨hm, hw⟩
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    refine ⟨Set.mem_univ _, ?_⟩
    rintro (h0 | h1)
    · by_cases hre : z.re = -1
      · have := ((hclass z hz).1 hre).2.2; rw [h0, Complex.zero_re] at this; linarith
      · by_cases hnorm : ‖2 * z + 1‖ = 1
        · have := ((hclass z hz).2.1 hre hnorm).2.2.1; rw [h0, Complex.zero_re] at this; linarith
        · rcases ((hclass z hz).2.2 hre hnorm).2 with him | hneg
          · rw [h0, Complex.zero_im] at him; exact him rfl
          · rw [h0, Complex.zero_re] at hneg; exact lt_irrefl 0 hneg
    · have h1_eq : lambdaOnQ z = 1 := h1
      by_cases hre : z.re = -1
      · have := ((hclass z hz).1 hre).2.2; rw [h1_eq, Complex.one_re] at this; linarith
      · by_cases hnorm : ‖2 * z + 1‖ = 1
        · have := ((hclass z hz).2.1 hre hnorm).2.2.2; rw [h1_eq, Complex.one_re] at this; linarith
        · rcases ((hclass z hz).2.2 hre hnorm).2 with him | hneg
          · rw [h1_eq, Complex.one_im] at him; exact him rfl
          · rw [h1_eq, Complex.one_re] at hneg; linarith
  · intro z₁ hz₁ z₂ hz₂ heq
    by_cases hre₁ : z₁.re = -1 <;> by_cases hre₂ : z₂.re = -1
    · exact lambdaOnQ_bijOn_boundaryL3Minus.injOn
        ((hclass z₁ hz₁).1 hre₁).1 ((hclass z₂ hz₂).1 hre₂).1 heq
    · by_cases hn₂ : ‖2 * z₂ + 1‖ = 1
      · have h1 := ((hclass z₁ hz₁).1 hre₁).2.2
        have h2 := ((hclass z₂ hz₂).2.1 hre₂ hn₂).2.2.2
        rw [heq] at h1; linarith
      · have h1 := ((hclass z₁ hz₁).1 hre₁).2
        rcases ((hclass z₂ hz₂).2.2 hre₂ hn₂).2 with him2 | hneg2
        · exact False.elim (him2 (heq ▸ h1.1))
        · rw [heq] at h1; linarith
    · by_cases hn₁ : ‖2 * z₁ + 1‖ = 1
      · have h1 := ((hclass z₁ hz₁).2.1 hre₁ hn₁).2.2.2
        have h2 := ((hclass z₂ hz₂).1 hre₂).2.2
        rw [heq] at h1; linarith
      · have h2 := ((hclass z₂ hz₂).1 hre₂).2
        rcases ((hclass z₁ hz₁).2.2 hre₁ hn₁).2 with him1 | hneg1
        · exact False.elim (him1 (heq.symm ▸ h2.1))
        · rw [← heq] at h2; linarith
    · by_cases hn₁ : ‖2 * z₁ + 1‖ = 1 <;> by_cases hn₂ : ‖2 * z₂ + 1‖ = 1
      · exact lambdaOnQ_bijOn_boundaryL2Minus.injOn
          ((hclass z₁ hz₁).2.1 hre₁ hn₁).1 ((hclass z₂ hz₂).2.1 hre₂ hn₂).1 heq
      · have h1 := ((hclass z₁ hz₁).2.1 hre₁ hn₁).2
        rcases ((hclass z₂ hz₂).2.2 hre₂ hn₂).2 with him2 | hneg2
        · exact False.elim (him2 (heq ▸ h1.1))
        · rw [heq] at h1; linarith
      · have h2 := ((hclass z₂ hz₂).2.1 hre₂ hn₂).2
        rcases ((hclass z₁ hz₁).2.2 hre₁ hn₁).2 with him1 | hneg1
        · exact False.elim (him1 (heq.symm ▸ h2.1))
        · rw [← heq] at h2; linarith
      · have hm₁ := ((hclass z₁ hz₁).2.2 hre₁ hn₁).1
        have hm₂ := ((hclass z₂ hz₂).2.2 hre₂ hn₂).1
        rw [lambdaOnQ_eq_lambdaRight hm₁, lambdaOnQ_eq_lambdaRight hm₂] at heq
        exact lambdaRight_bijOn_omegaL1.injOn hm₁ hm₂ heq
  · rintro w ⟨_, hw_not⟩
    have hw0 : w ≠ 0 := fun h => hw_not (Or.inl h)
    have hw1 : w ≠ 1 := fun h => hw_not (Or.inr h)
    by_cases him : w.im = 0
    · rcases lt_trichotomy w.re 0 with hneg | hre0 | hpos
      · obtain ⟨z, hz, hzw⟩ := lambdaRight_bijOn_omegaL1.surjOn (Or.inr hneg)
        exact ⟨z, omegaL1_subset_fundamentalSetQ hz, (lambdaOnQ_eq_lambdaRight hz).trans hzw⟩
      · exact False.elim (hw0 (Complex.ext hre0 him))
      · rcases lt_trichotomy w.re 1 with hlt1 | hre1 | hgt1
        · obtain ⟨z, hz, hzw⟩ := lambdaOnQ_bijOn_boundaryL2Minus.surjOn ⟨him, hpos, hlt1⟩
          exact ⟨z, boundaryL2Minus_subset_fundamentalSetQ hz, hzw⟩
        · exact False.elim (hw1 (Complex.ext hre1 him))
        · obtain ⟨z, hz, hzw⟩ := lambdaOnQ_bijOn_boundaryL3Minus.surjOn ⟨him, hgt1⟩
          exact ⟨z, boundaryL3Minus_subset_fundamentalSetQ hz, hzw⟩
    · obtain ⟨z, hz, hzw⟩ := lambdaRight_bijOn_omegaL1.surjOn (Or.inl him)
      exact ⟨z, omegaL1_subset_fundamentalSetQ hz, (lambdaOnQ_eq_lambdaRight hz).trans hzw⟩

/-- The elliptic modular function `λ : ℂ → ℂ` of Rudin's Theorem `16.20` (defined on `Π⁺` by
unique `Γ`-reduction to the fundamental set `Q`, and `0` off `Π⁺`). -/
def modularLambda (z : ℂ) : ℂ :=
  letI := Classical.propDecidable
  if h : ∃ p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
      (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z then
    lambdaOnQ (Classical.choose h).2.1
  else
    0

section ModularLambdaProperties

theorem modularLambda_apply_gamma_q
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    (γ : GammaSubgroup) {q : ℂ} (hq : q ∈ FundamentalSetQ) :
    modularLambda (γ.1.1 ⟨q, fundamentalSetQ_subset_upperHalfPlaneSet hq⟩).1 = lambdaOnQ q := by
  let z : ℂ := (γ.1.1 ⟨q, fundamentalSetQ_subset_upperHalfPlaneSet hq⟩).1
  have hz : z ∈ UpperHalfPlaneSet := (γ.1.1 ⟨q, fundamentalSetQ_subset_upperHalfPlaneSet hq⟩).2
  let p₀ : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ} := (γ, ⟨q, hq⟩)
  have hex : ∃ p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
      (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z :=
    ⟨p₀, rfl⟩
  have huniq := (h_exU hz).unique (Classical.choose_spec hex) (rfl : (p₀.1.1.1 _).1 = z)
  change modularLambda z = lambdaOnQ q
  unfold modularLambda
  simp only [hex, ↓reduceDIte]
  rw [huniq]

theorem modularLambda_eq_lambdaOnQ
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    {q : ℂ} (hq : q ∈ FundamentalSetQ) :
    modularLambda q = lambdaOnQ q := by
  simpa using modularLambda_apply_gamma_q h_exU 1 hq

theorem modularLambda_gamma_invariant
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    (γ : GammaSubgroup) (z : UpperHalfPlaneSet) :
    modularLambda (γ.1.1 z).1 = modularLambda z.1 := by
  obtain ⟨⟨γ₀, ⟨q, hq⟩⟩, h_eq, _⟩ := h_exU z.2
  have hz_sub : γ₀.1.1 ⟨q, fundamentalSetQ_subset_upperHalfPlaneSet hq⟩ = z :=
    Subtype.ext h_eq
  rw [← hz_sub]
  change modularLambda (((γ * γ₀).1.1 ⟨q, fundamentalSetQ_subset_upperHalfPlaneSet hq⟩).1) =
    modularLambda ((γ₀.1.1 ⟨q, fundamentalSetQ_subset_upperHalfPlaneSet hq⟩).1)
  rw [modularLambda_apply_gamma_q h_exU (γ * γ₀) hq, modularLambda_apply_gamma_q h_exU γ₀ hq]

/-- Deck-orbit characterization: `modularLambda z₁ = modularLambda z₂` on `Π⁺` iff `z₁` and `z₂`
lie in the same `GammaSubgroup`-orbit. -/
theorem modularLambda_eq_iff_gamma_orbit
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ UpperHalfPlaneSet) (hz₂ : z₂ ∈ UpperHalfPlaneSet) :
    modularLambda z₁ = modularLambda z₂ ↔
      ∃ γ : GammaSubgroup, (γ.1.1 ⟨z₂, hz₂⟩).1 = z₁ := by
  constructor
  · intro heq
    obtain ⟨⟨γ₁, ⟨q₁, hq₁⟩⟩, h₁_eq, _⟩ := h_exU hz₁
    obtain ⟨⟨γ₂, ⟨q₂, hq₂⟩⟩, h₂_eq, _⟩ := h_exU hz₂
    have hlam₁ : modularLambda z₁ = lambdaOnQ q₁ := by
      rw [← h₁_eq]; exact modularLambda_apply_gamma_q h_exU γ₁ hq₁
    have hlam₂ : modularLambda z₂ = lambdaOnQ q₂ := by
      rw [← h₂_eq]; exact modularLambda_apply_gamma_q h_exU γ₂ hq₂
    have hq_eq : q₁ = q₂ :=
      lambdaOnQ_bijOn_fundamentalSetQ.injOn hq₁ hq₂ (hlam₁.symm.trans (heq.trans hlam₂))
    subst hq_eq
    refine ⟨γ₁ * γ₂⁻¹, ?_⟩
    have hz₂_sub : ⟨z₂, hz₂⟩ = γ₂.1.1 ⟨q₁, fundamentalSetQ_subset_upperHalfPlaneSet hq₁⟩ :=
      Subtype.ext h₂_eq.symm
    rw [hz₂_sub]
    change (γ₁.1.1 (γ₂.1.1⁻¹ (γ₂.1.1 ⟨q₁, fundamentalSetQ_subset_upperHalfPlaneSet hq₁⟩))).1 = z₁
    simp [h₁_eq]
  · rintro ⟨γ, hγ⟩
    rw [← hγ]
    exact modularLambda_gamma_invariant h_exU γ ⟨z₂, hz₂⟩

theorem hasDerivAt_intMoebius {a b c d : ℤ} (hdet : a * d - b * c = 1)
    {z : ℂ} (hz : z ∈ UpperHalfPlaneSet) :
    HasDerivAt (intMoebius a b c d) (1 / ((c : ℂ) * z + (d : ℂ)) ^ 2) z := by
  have hden : (c : ℂ) * z + (d : ℂ) ≠ 0 := intMoebius_denom_ne_zero hdet hz
  have hd_num : HasDerivAt (fun w : ℂ => (a : ℂ) * w + (b : ℂ)) (a : ℂ) z := by
    simpa using (hasDerivAt_id z |>.const_mul (a : ℂ)).add_const (b : ℂ)
  have hd_den : HasDerivAt (fun w : ℂ => (c : ℂ) * w + (d : ℂ)) (c : ℂ) z := by
    simpa using (hasDerivAt_id z |>.const_mul (c : ℂ)).add_const (d : ℂ)
  have hd := hd_num.div hd_den hden
  unfold intMoebius
  convert hd using 1
  congr 1
  have hdetC : (a : ℂ) * (d : ℂ) - (b : ℂ) * (c : ℂ) = 1 := by exact_mod_cast hdet
  linear_combination -hdetC

theorem star_moebiusM3 (w : ℂ) :
    starRingEnd ℂ (moebiusM3 w) = moebiusM3 (starRingEnd ℂ w) := by
  unfold moebiusM3
  simp

theorem lambdaRight_ne_zero_one {w : ℂ} (hw : w ∈ OmegaL1) :
    lambdaRight w ≠ 0 ∧ lambdaRight w ≠ 1 := by
  have hm := lambdaRight_bijOn_omegaL1.mapsTo hw
  refine ⟨?_, ?_⟩
  · intro h0
    rcases hm with him | hre
    · rw [h0, Complex.zero_im] at him; exact him rfl
    · rw [h0, Complex.zero_re] at hre; exact lt_irrefl 0 hre
  · intro h1
    rcases hm with him | hre
    · rw [h1, Complex.one_im] at him; exact him rfl
    · rw [h1, Complex.one_re] at hre; linarith

/-- `modularLambda` is holomorphic with nonvanishing derivative at every point of `FundamentalSetQ`. -/
theorem modularLambda_holo_and_deriv_ne_zero_on_Q
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    {q₀ : ℂ} (hq₀ : q₀ ∈ FundamentalSetQ) :
    DifferentiableAt ℂ modularLambda q₀ ∧ deriv modularLambda q₀ ≠ 0 := by
  by_cases hre : q₀.re = -1
  · -- Case 1 (`q₀ ∈ BoundaryL3Minus`): `modularLambda z = M₃(lambdaRight (-1 / (z + 1)))` near `q₀`
    let wMap1 : ℂ → ℂ := fun z => -1 / (z + 1)
    have hwMap1_cont : ContinuousOn wMap1 UpperHalfPlaneSet := by
      intro z hz
      have hz_pos : 0 < z.im := hz
      refine (continuousAt_const.div (continuousAt_id.add continuousAt_const) ?_).continuousWithinAt
      intro h0
      have him := congrArg Complex.im h0
      dsimp at him
      simp [hz_pos.ne'] at him
    let V0 : Set ℂ := UpperHalfPlaneSet ∩ wMap1 ⁻¹' OmegaL1
    have hV0_open : IsOpen V0 :=
      hwMap1_cont.isOpen_inter_preimage isOpen_upperHalfPlaneSet isOpen_omegaL1
    let V : Set ℂ :=
      V0 ∩ {z : ℂ | -2 < z.re ∧ z.re < 0 ∧ 1 < ‖2 * z + 1‖ ∧ 1 < ‖2 * (z + 2) - 1‖}
    have hV_open : IsOpen V :=
      hV0_open.inter
        ((isOpen_lt continuous_const Complex.continuous_re).inter
          ((isOpen_lt Complex.continuous_re continuous_const).inter
            ((isOpen_lt continuous_const (continuous_norm.comp
                ((continuous_const.mul continuous_id).add continuous_const))).inter
              (isOpen_lt continuous_const (continuous_norm.comp
                ((continuous_const.mul (continuous_id.add continuous_const)).sub
                  continuous_const))))))
    have hq₀_w_L1 : wMap1 q₀ ∈ BoundaryL1 := by
      have hz_eq : q₀ + 1 = (q₀.im : ℂ) * Complex.I :=
        Complex.ext (by simp [hre]) (by simp)
      have him_ne : (q₀.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq₀.1.ne'
      have hval : wMap1 q₀ = ((1 / q₀.im : ℝ) : ℂ) * Complex.I := by
        dsimp [wMap1]
        rw [hz_eq, Complex.ofReal_div, Complex.ofReal_one]
        field_simp [him_ne, Complex.I_ne_zero]; ring_nf; simp [Complex.I_sq]
      rw [hval]
      exact ⟨by simp, by simp; exact hq₀.1⟩
    have hq₀_V : q₀ ∈ V := by
      refine ⟨⟨hq₀.1, boundaryL1_subset_omegaL1 hq₀_w_L1⟩, by linarith, by linarith, ?_, ?_⟩
      · have hsq := norm_two_mul_add_one_sq q₀
        rw [hre] at hsq
        have hgt1 : 1 < ‖2 * q₀ + 1‖ ^ 2 := by
          have : 0 < q₀.im ^ 2 := sq_pos_of_pos hq₀.1
          linarith
        nlinarith [norm_nonneg (2 * q₀ + 1)]
      · rw [one_lt_norm_two_mul_sub_one_iff]
        simp only [Complex.add_re, Complex.re_ofNat, Complex.add_im, Complex.im_ofNat, add_zero, hre]
        have : 0 < q₀.im ^ 2 := sq_pos_of_pos hq₀.1
        nlinarith
    -- Show `modularLambda` agrees on `V` with `g₁(z) = moebiusM3 (lambdaRight (wMap1 z))`
    let g₁ : ℂ → ℂ := fun z => moebiusM3 (lambdaRight (wMap1 z))
    have heq_V : Set.EqOn modularLambda g₁ V := by
      intro z hz
      obtain ⟨⟨hz_im, hw_om⟩, hre_gt2, hre_lt0, hnorm_add, hnorm_tau⟩ := hz
      have hz_pos : 0 < z.im := hz_im
      have hz1_nz : z + 1 ≠ 0 := fun h => by
        have := congrArg Complex.im h; simp [hz_pos.ne'] at this
      have hw_re_eq : (wMap1 z).re = -(z.re + 1) / Complex.normSq (z + 1) := by
        dsimp [wMap1]
        simp [neg_div, one_div, Complex.inv_re]
        ring
      have hnsq_pos : 0 < Complex.normSq (z + 1) := Complex.normSq_pos.mpr hz1_nz
      rcases lt_trichotomy z.re (-1) with hlt | heq | hgt
      · -- `z.re < -1`: `z + 2 ∈ Q₀`, `wMap1 z ∈ Q₀`, `M₃ (wMap1 z) = z + 2`
        have hz2_Q0 : z + 2 ∈ OpenTriangleQ0 := by
          refine ⟨by simpa using hz_im, ?_, ?_, hnorm_tau⟩
          · simp; linarith
          · simp; linarith
        have hw_re_pos : 0 < (wMap1 z).re := by
          rw [hw_re_eq]
          exact div_pos (by linarith) hnsq_pos
        have hw_Q0 : wMap1 z ∈ OpenTriangleQ0 :=
          ⟨hw_om.1, hw_re_pos, hw_om.2.2.1, hw_om.2.2.2.1⟩
        have hM3_w : moebiusM3 (wMap1 z) = z + 2 := by
          unfold moebiusM3; dsimp [wMap1]
          field_simp [hz1_nz]; ring
        let τ : GammaSubgroup := ⟨modularTau, modularTau_mem_gamma⟩
        have htau_inv : modularLambda (z + 2) = modularLambda z := by
          simpa [τ] using modularLambda_gamma_invariant h_exU τ ⟨z, hz_im⟩
        have hz2_om : z + 2 ∈ OmegaL1 := openTriangleQ0_subset_omegaL1 hz2_Q0
        rw [← htau_inv, modularLambda_eq_lambdaOnQ h_exU (omegaL1_subset_fundamentalSetQ hz2_om),
          lambdaOnQ_eq_lambdaRight hz2_om, ← hM3_w, lambdaRight_moebiusM3 hw_Q0]
      · -- `z.re = -1`: `z ∈ BoundaryL3Minus ⊆ FundamentalSetQ`
        have hz_Q : z ∈ FundamentalSetQ := boundaryL3Minus_subset_fundamentalSetQ ⟨heq, hz_im⟩
        rw [modularLambda_eq_lambdaOnQ h_exU hz_Q]
        simp [lambdaOnQ, heq, g₁, wMap1]
      · -- `-1 < z.re < 0`: `z ∈ ReflectedQ0` and `wMap1 z ∈ ReflectedQ0`
        have hz_sub : 1 < ‖2 * z - 1‖ := by
          rw [one_lt_norm_two_mul_sub_one_iff]
          nlinarith [sq_nonneg z.re, sq_nonneg z.im]
        have hz_R : z ∈ ReflectedQ0 := ⟨hz_im, hgt, hre_lt0, hnorm_add⟩
        have hz_om : z ∈ OmegaL1 := reflectedQ0_subset_omegaL1 hz_R
        have hw_re_neg : (wMap1 z).re < 0 := by
          rw [hw_re_eq]
          exact div_neg_of_neg_of_pos (by linarith) hnsq_pos
        have hw_R : wMap1 z ∈ ReflectedQ0 := ⟨hw_om.1, hw_om.2.1, hw_re_neg, hw_om.2.2.2.2⟩
        have hw_conj_Q0 : -starRingEnd ℂ (wMap1 z) ∈ OpenTriangleQ0 :=
          neg_conj_mem_openTriangleQ0_iff.mpr hw_R
        have hM3_conj : moebiusM3 (-starRingEnd ℂ (wMap1 z)) = -starRingEnd ℂ z := by
          have hconj_nz : starRingEnd ℂ (z + 1) ≠ 0 :=
            fun hc => hz1_nz (by simpa using congrArg (starRingEnd ℂ) hc)
          unfold moebiusM3; dsimp [wMap1]
          simp only [map_div₀, map_neg, map_one, map_add] at hconj_nz ⊢
          field_simp [hconj_nz]; ring
        rw [modularLambda_eq_lambdaOnQ h_exU (omegaL1_subset_fundamentalSetQ hz_om),
          lambdaOnQ_eq_lambdaRight hz_om, lambdaRight_of_re_neg hre_lt0,
          ← hM3_conj, lambdaRight_moebiusM3 hw_conj_Q0, star_moebiusM3,
          ← lambdaRight_of_re_neg hw_re_neg]
    -- Compute the derivative of `g₁` at `q₀`
    have hq₀1_nz : q₀ + 1 ≠ 0 := fun h => by
      have := congrArg Complex.im h; simp [hq₀.1.ne'] at this
    have hd_w1 : HasDerivAt wMap1 (1 / (q₀ + 1) ^ 2) q₀ := by
      have h1 : HasDerivAt (fun z : ℂ => z + 1) 1 q₀ := by
        simpa using (hasDerivAt_id q₀).add_const (1 : ℂ)
      have hd := (hasDerivAt_const q₀ (-1 : ℂ)).div h1 hq₀1_nz
      dsimp [wMap1]
      convert hd using 1
      ring
    have hw₀_om : wMap1 q₀ ∈ OmegaL1 := boundaryL1_subset_omegaL1 hq₀_w_L1
    have hd_lam : HasDerivAt lambdaRight (deriv lambdaRight (wMap1 q₀)) (wMap1 q₀) :=
      (lambdaRight_holo _ hw₀_om).hasDerivAt
    have hlam_nz : lambdaRight (wMap1 q₀) ≠ 0 := (lambdaRight_ne_zero_one hw₀_om).1
    have hd_M3 : HasDerivAt moebiusM3 ((lambdaRight (wMap1 q₀) ^ 2)⁻¹) (lambdaRight (wMap1 q₀)) :=
      hasDerivAt_moebiusM3 hlam_nz
    have hd_lw1 : HasDerivAt (lambdaRight ∘ wMap1)
        (deriv lambdaRight (wMap1 q₀) * (1 / (q₀ + 1) ^ 2)) q₀ :=
      HasDerivAt.comp q₀ hd_lam hd_w1
    have hd_g1 : HasDerivAt (moebiusM3 ∘ (lambdaRight ∘ wMap1))
        ((lambdaRight (wMap1 q₀) ^ 2)⁻¹ * (deriv lambdaRight (wMap1 q₀) * (1 / (q₀ + 1) ^ 2))) q₀ :=
      HasDerivAt.comp q₀ hd_M3 hd_lw1
    have hd_mod : HasDerivAt modularLambda
        ((lambdaRight (wMap1 q₀) ^ 2)⁻¹ * (deriv lambdaRight (wMap1 q₀) * (1 / (q₀ + 1) ^ 2))) q₀ :=
      hd_g1.congr_of_eventuallyEq (heq_V.eventuallyEq_of_mem (hV_open.mem_nhds hq₀_V))
    refine ⟨hd_mod.differentiableAt, ?_⟩
    rw [hd_mod.deriv]
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero 2 hlam_nz))
      (mul_ne_zero (deriv_lambdaRight_ne_zero hw₀_om)
        (one_div_ne_zero (pow_ne_zero 2 hq₀1_nz)))
  · by_cases hnorm : ‖2 * q₀ + 1‖ = 1
    · -- Case 2 (`q₀ ∈ BoundaryL2Minus`): `modularLambda z = M₃(M₃(lambdaRight (-1 - 1 / z)))`
      have hq₀_L2 : q₀ ∈ BoundaryL2Minus := ⟨hq₀.1, hnorm⟩
      obtain ⟨hq₀_re_gt, hq₀_re_lt⟩ := boundaryL2Minus_re_bounds hq₀_L2
      let wMap2 : ℂ → ℂ := fun z => -1 - 1 / z
      have hwMap2_cont : ContinuousOn wMap2 UpperHalfPlaneSet := by
        intro z hz
        have hz_pos : 0 < z.im := hz
        have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_im] at hz_pos; exact lt_irrefl 0 hz_pos
        exact (continuousAt_const.sub
          (continuousAt_const.div continuousAt_id hz0)).continuousWithinAt
      let V0 : Set ℂ := UpperHalfPlaneSet ∩ wMap2 ⁻¹' OmegaL1
      have hV0_open : IsOpen V0 :=
        hwMap2_cont.isOpen_inter_preimage isOpen_upperHalfPlaneSet isOpen_omegaL1
      let V : Set ℂ := V0 ∩ {z : ℂ | -1 < z.re ∧ z.re < 0}
      have hV_open : IsOpen V :=
        hV0_open.inter
          ((isOpen_lt continuous_const Complex.continuous_re).inter
            (isOpen_lt Complex.continuous_re continuous_const))
      have hq₀_nz : q₀ ≠ 0 := fun h => by
        have := hq₀.1; rw [h, Complex.zero_im] at this; exact lt_irrefl 0 this
      have hq₀_w_L1 : wMap2 q₀ ∈ BoundaryL1 := by
        obtain ⟨hre_w, him_w⟩ := wMap2_re_im hq₀_nz
        exact ⟨by change (-1 - 1 / q₀).re = 0; rw [hre_w, hnorm]; norm_num,
          by change 0 < (-1 - 1 / q₀).im; rw [him_w]; exact div_pos hq₀.1 (Complex.normSq_pos.mpr hq₀_nz)⟩
      have hq₀_V : q₀ ∈ V :=
        ⟨⟨hq₀.1, boundaryL1_subset_omegaL1 hq₀_w_L1⟩, hq₀_re_gt, hq₀_re_lt⟩
      let g₂ : ℂ → ℂ := fun z => moebiusM3 (moebiusM3 (lambdaRight (wMap2 z)))
      have heq_V : Set.EqOn modularLambda g₂ V := by
        intro z hz
        obtain ⟨⟨hz_im, hw_om⟩, hre_gt, hre_lt⟩ := hz
        have hz_pos : 0 < z.im := hz_im
        have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_im] at hz_pos; exact lt_irrefl 0 hz_pos
        have hnsq_pos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
        obtain ⟨hw_re_eq, _⟩ := wMap2_re_im hz0
        rcases lt_trichotomy ‖2 * z + 1‖ 1 with hlt | heq | hgt
        · -- `‖2 * z + 1‖ < 1`: `wMap2 z ∈ Q₀` and `M₃(M₃(wMap2 z)) = z / (2 z + 1)`
          have hw_re_pos : 0 < (wMap2 z).re := by
            change 0 < (-1 - 1 / z).re
            rw [hw_re_eq]
            have hsq_lt : ‖2 * z + 1‖ ^ 2 < 1 := by nlinarith [norm_nonneg (2 * z + 1)]
            exact div_pos (by linarith) (by positivity)
          have hw_Q0 : wMap2 z ∈ OpenTriangleQ0 :=
            ⟨hw_om.1, hw_re_pos, hw_om.2.2.1, hw_om.2.2.2.1⟩
          have hw1_Q0 : moebiusM3 (wMap2 z) ∈ OpenTriangleQ0 :=
            moebiusM3_mapsTo_openTriangleQ0 hw_Q0
          have hw2_Q0 : moebiusM3 (moebiusM3 (wMap2 z)) ∈ OpenTriangleQ0 :=
            moebiusM3_mapsTo_openTriangleQ0 hw1_Q0
          have hw0 : wMap2 z ≠ 0 := fun h => by
            have := hw_Q0.1; rw [h, Complex.zero_im] at this; exact lt_irrefl 0 this
          have hw1 : wMap2 z ≠ 1 := fun h => by
            have := hw_Q0.1; rw [h, Complex.one_im] at this; exact lt_irrefl 0 this
          have h2z1_nz : 2 * z + 1 ≠ 0 := fun h => by
            have := congrArg Complex.im h; simp [hz_pos.ne'] at this
          have hM32_eq : moebiusM3 (moebiusM3 (wMap2 z)) = z / (2 * z + 1) := by
            rw [moebiusM3_iter2 hw0 hw1]
            dsimp [wMap2]
            field_simp [hz0, h2z1_nz]
            ring
          let σ : GammaSubgroup := ⟨modularSigma, modularSigma_mem_gamma⟩
          have hsig_inv : modularLambda (z / (2 * z + 1)) = modularLambda z := by
            simpa [σ] using modularLambda_gamma_invariant h_exU σ ⟨z, hz_im⟩
          have hw2_om : moebiusM3 (moebiusM3 (wMap2 z)) ∈ OmegaL1 :=
            openTriangleQ0_subset_omegaL1 hw2_Q0
          rw [← hsig_inv, ← hM32_eq,
            modularLambda_eq_lambdaOnQ h_exU (omegaL1_subset_fundamentalSetQ hw2_om),
            lambdaOnQ_eq_lambdaRight hw2_om,
            lambdaRight_moebiusM3 hw1_Q0, lambdaRight_moebiusM3 hw_Q0]
        · -- `‖2 * z + 1‖ = 1`: `z ∈ BoundaryL2Minus ⊆ FundamentalSetQ`
          have hz_Q : z ∈ FundamentalSetQ :=
            boundaryL2Minus_subset_fundamentalSetQ ⟨hz_im, heq⟩
          rw [modularLambda_eq_lambdaOnQ h_exU hz_Q]
          simp [lambdaOnQ, hre_gt.ne', heq, g₂, wMap2]
        · -- `1 < ‖2 * z + 1‖`: `z ∈ ReflectedQ0` and `wMap2 z ∈ ReflectedQ0`
          have hz_R : z ∈ ReflectedQ0 := ⟨hz_im, hre_gt, hre_lt, hgt⟩
          have hz_om : z ∈ OmegaL1 := reflectedQ0_subset_omegaL1 hz_R
          have hw_re_neg : (wMap2 z).re < 0 := by
            change (-1 - 1 / z).re < 0
            rw [hw_re_eq]
            have hsq_gt : 1 < ‖2 * z + 1‖ ^ 2 := by nlinarith
            exact div_neg_of_neg_of_pos (by linarith) (by positivity)
          have hw_R : wMap2 z ∈ ReflectedQ0 :=
            ⟨hw_om.1, hw_om.2.1, hw_re_neg, hw_om.2.2.2.2⟩
          have hz_conj_Q0 : -starRingEnd ℂ z ∈ OpenTriangleQ0 :=
            neg_conj_mem_openTriangleQ0_iff.mpr hz_R
          have hM3_conj : moebiusM3 (-starRingEnd ℂ z) = -starRingEnd ℂ (wMap2 z) := by
            have hconj_nz : starRingEnd ℂ z ≠ 0 :=
              fun hc => hz0 (by simpa using congrArg (starRingEnd ℂ) hc)
            unfold moebiusM3; dsimp [wMap2]
            simp only [map_sub, map_neg, map_one, map_div₀]
            field_simp [hconj_nz]; ring
          have hlam_w : lambdaRight (wMap2 z) = moebiusM3 (lambdaRight z) := by
            rw [lambdaRight_of_re_neg hw_re_neg, ← hM3_conj,
              lambdaRight_moebiusM3 hz_conj_Q0, star_moebiusM3,
              ← lambdaRight_of_re_neg hre_lt]
          obtain ⟨hz_ne0, hz_ne1⟩ := lambdaRight_ne_zero_one hz_om
          rw [modularLambda_eq_lambdaOnQ h_exU (omegaL1_subset_fundamentalSetQ hz_om),
            lambdaOnQ_eq_lambdaRight hz_om]
          dsimp [g₂]
          rw [hlam_w, moebiusM3_iter3 hz_ne0 hz_ne1]
      -- Compute the derivative of `g₂` at `q₀`
      have hd_w2 : HasDerivAt wMap2 ((q₀ ^ 2)⁻¹) q₀ := by
        have hw2_eq : wMap2 = fun z : ℂ => -1 - z⁻¹ :=
          funext fun z => by simp [wMap2, one_div]
        rw [hw2_eq]
        have hd_sub := (hasDerivAt_const q₀ (-1 : ℂ)).sub (hasDerivAt_inv hq₀_nz)
        convert hd_sub using 1
        ring
      have hw₀_om : wMap2 q₀ ∈ OmegaL1 := boundaryL1_subset_omegaL1 hq₀_w_L1
      have hd_lam : HasDerivAt lambdaRight (deriv lambdaRight (wMap2 q₀)) (wMap2 q₀) :=
        (lambdaRight_holo _ hw₀_om).hasDerivAt
      obtain ⟨hu0, hu1⟩ := lambdaRight_ne_zero_one hw₀_om
      have hmu0 : moebiusM3 (lambdaRight (wMap2 q₀)) ≠ 0 := moebiusM3_ne_zero hu0 hu1
      have hd_M3_inner : HasDerivAt moebiusM3 ((lambdaRight (wMap2 q₀) ^ 2)⁻¹)
          (lambdaRight (wMap2 q₀)) :=
        hasDerivAt_moebiusM3 hu0
      have hd_M3_outer : HasDerivAt moebiusM3
          ((moebiusM3 (lambdaRight (wMap2 q₀)) ^ 2)⁻¹) (moebiusM3 (lambdaRight (wMap2 q₀))) :=
        hasDerivAt_moebiusM3 hmu0
      have hd_lw2 : HasDerivAt (lambdaRight ∘ wMap2)
          (deriv lambdaRight (wMap2 q₀) * (q₀ ^ 2)⁻¹) q₀ :=
        HasDerivAt.comp q₀ hd_lam hd_w2
      have hd_m3_lw2 : HasDerivAt (moebiusM3 ∘ (lambdaRight ∘ wMap2))
          ((lambdaRight (wMap2 q₀) ^ 2)⁻¹ * (deriv lambdaRight (wMap2 q₀) * (q₀ ^ 2)⁻¹)) q₀ :=
        HasDerivAt.comp q₀ hd_M3_inner hd_lw2
      have hd_g2 : HasDerivAt (moebiusM3 ∘ (moebiusM3 ∘ (lambdaRight ∘ wMap2)))
          ((moebiusM3 (lambdaRight (wMap2 q₀)) ^ 2)⁻¹ *
            ((lambdaRight (wMap2 q₀) ^ 2)⁻¹ *
              (deriv lambdaRight (wMap2 q₀) * (q₀ ^ 2)⁻¹))) q₀ :=
        HasDerivAt.comp q₀ hd_M3_outer hd_m3_lw2
      have hd_mod := hd_g2.congr_of_eventuallyEq
        (heq_V.eventuallyEq_of_mem (hV_open.mem_nhds hq₀_V))
      refine ⟨hd_mod.differentiableAt, ?_⟩
      rw [hd_mod.deriv]
      exact mul_ne_zero (inv_ne_zero (pow_ne_zero 2 hmu0))
        (mul_ne_zero (inv_ne_zero (pow_ne_zero 2 hu0))
          (mul_ne_zero (deriv_lambdaRight_ne_zero hw₀_om)
            (inv_ne_zero (pow_ne_zero 2 hq₀_nz))))
    · -- Case 3 (`q₀ ∈ OmegaL1`): `OmegaL1` is an open neighborhood of `q₀` inside `Q`
      have hq₀_om : q₀ ∈ OmegaL1 :=
        ⟨hq₀.1, lt_of_le_of_ne hq₀.2.1 (Ne.symm hre), hq₀.2.2.1, hq₀.2.2.2.2,
          lt_of_le_of_ne hq₀.2.2.2.1 (Ne.symm hnorm)⟩
      have hev : modularLambda =ᶠ[𝓝 q₀] lambdaRight := by
        filter_upwards [isOpen_omegaL1.mem_nhds hq₀_om] with z hz
        rw [modularLambda_eq_lambdaOnQ h_exU (omegaL1_subset_fundamentalSetQ hz),
          lambdaOnQ_eq_lambdaRight hz]
      have hd_mod : HasDerivAt modularLambda (deriv lambdaRight q₀) q₀ :=
        (lambdaRight_holo _ hq₀_om).hasDerivAt.congr_of_eventuallyEq hev
      refine ⟨hd_mod.differentiableAt, ?_⟩
      rw [hd_mod.deriv]
      exact deriv_lambdaRight_ne_zero hq₀_om

/-- `modularLambda` is holomorphic with nonvanishing derivative throughout `UpperHalfPlaneSet`. -/
theorem modularLambda_holo_and_deriv_ne_zero
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ UpperHalfPlaneSet) :
    DifferentiableAt ℂ modularLambda z₀ ∧ deriv modularLambda z₀ ≠ 0 := by
  obtain ⟨⟨γ, ⟨q₀, hq₀⟩⟩, hz₀_eq, _⟩ := h_exU hz₀
  obtain ⟨a, b, c, d, hdet, hperm⟩ := γ.1.2
  have hdet_inv : d * a - (-b) * (-c) = 1 := by linear_combination hdet
  let g : ℂ → ℂ := intMoebius d (-b) (-c) a
  have hg_apply : ∀ {z : ℂ} (hz : z ∈ UpperHalfPlaneSet),
      g z = ((γ⁻¹).1.1 ⟨z, hz⟩).1 := by
    intro z hz
    change intMoebius d (-b) (-c) a z = ((γ.1.1)⁻¹ ⟨z, hz⟩).1
    rw [hperm, intMoebiusPerm_inv]
    rfl
  have hg_z₀ : g z₀ = q₀ := by
    rw [hg_apply hz₀]
    have hsub : (⟨z₀, hz₀⟩ : UpperHalfPlaneSet) =
        γ.1.1 ⟨q₀, fundamentalSetQ_subset_upperHalfPlaneSet hq₀⟩ :=
      Subtype.ext hz₀_eq.symm
    rw [hsub]
    change ((γ.1.1)⁻¹ (γ.1.1 ⟨q₀, fundamentalSetQ_subset_upperHalfPlaneSet hq₀⟩)).1 = q₀
    simp
  have hev : modularLambda =ᶠ[𝓝 z₀] modularLambda ∘ g := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz₀] with z hz
    dsimp [Function.comp]
    rw [hg_apply hz]
    exact (modularLambda_gamma_invariant h_exU γ⁻¹ ⟨z, hz⟩).symm
  obtain ⟨hd_q₀, hderiv_q₀⟩ := modularLambda_holo_and_deriv_ne_zero_on_Q h_exU hq₀
  have hd_g : HasDerivAt g (1 / (((-c : ℤ) : ℂ) * z₀ + (a : ℂ)) ^ 2) z₀ :=
    hasDerivAt_intMoebius hdet_inv hz₀
  have hd_comp : HasDerivAt (modularLambda ∘ g)
      (deriv modularLambda q₀ * (1 / (((-c : ℤ) : ℂ) * z₀ + (a : ℂ)) ^ 2)) z₀ := by
    have hat : DifferentiableAt ℂ modularLambda (g z₀) := hg_z₀.symm ▸ hd_q₀
    have hc := HasDerivAt.comp z₀ hat.hasDerivAt hd_g
    rwa [hg_z₀] at hc
  have hd_mod := hd_comp.congr_of_eventuallyEq hev
  refine ⟨hd_mod.differentiableAt, ?_⟩
  rw [hd_mod.deriv]
  have hden_nz : ((-c : ℤ) : ℂ) * z₀ + (a : ℂ) ≠ 0 := intMoebius_denom_ne_zero hdet_inv hz₀
  exact mul_ne_zero hderiv_q₀ (one_div_ne_zero (pow_ne_zero 2 hden_nz))

theorem modularLambda_holomorphicOn
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z) :
    RudinRCA.Chapter10.HolomorphicOn modularLambda UpperHalfPlaneSet :=
  fun _ hz => (modularLambda_holo_and_deriv_ne_zero h_exU hz).1

theorem modularLambda_isModularFunctionFor_gamma
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z) :
    IsModularFunctionFor GammaSubgroup modularLambda :=
  ⟨gammaSubgroup_ne_bot,
   fun _ hz => (modularLambda_holomorphicOn h_exU _ hz).differentiableWithinAt,
   fun γ z => modularLambda_gamma_invariant h_exU γ z⟩

theorem modularLambda_bijOn_fundamentalSetQ
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z) :
    Set.BijOn modularLambda FundamentalSetQ (Set.univ \ {0, 1}) :=
  lambdaOnQ_bijOn_fundamentalSetQ.congr fun _ hq => (modularLambda_eq_lambdaOnQ h_exU hq).symm

theorem modularLambda_image_upperHalfPlaneSet
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z) :
    modularLambda '' UpperHalfPlaneSet = Set.univ \ {0, 1} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨⟨γ, ⟨q, hq⟩⟩, hz_eq, _⟩ := h_exU hz
    rw [← hz_eq, modularLambda_apply_gamma_q h_exU γ hq]
    exact lambdaOnQ_bijOn_fundamentalSetQ.mapsTo hq
  · rw [← (modularLambda_bijOn_fundamentalSetQ h_exU).image_eq]
    exact Set.image_mono fundamentalSetQ_subset_upperHalfPlaneSet

theorem frontier_upperHalfPlaneSet :
    frontier UpperHalfPlaneSet = {ζ : ℂ | ζ.im = 0} := by
  ext ζ
  change ζ ∈ closure UpperHalfPlaneSet \ interior UpperHalfPlaneSet ↔ ζ.im = 0
  rw [isOpen_upperHalfPlaneSet.interior_eq]
  constructor
  · rintro ⟨hcl, hnot⟩
    have hle : ζ.im ≤ 0 := not_lt.mp hnot
    have hclosed : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
    have hsub : UpperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} :=
      fun _ hz => show (0 : ℝ) ≤ _ from le_of_lt hz
    have hge : 0 ≤ ζ.im := closure_minimal hsub hclosed hcl
    linarith
  · intro him
    refine ⟨Metric.mem_closure_iff.mpr fun ε hε => ?_, by rw [mem_upperHalfPlaneSet, him]; norm_num⟩
    refine ⟨ζ + ((ε / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · change 0 < (ζ + ((ε / 2 : ℝ) : ℂ) * Complex.I).im
      simp [him]; linarith
    · rw [dist_eq_norm]
      have hsub_eq : ζ - (ζ + ((ε / 2 : ℝ) : ℂ) * Complex.I) = -(((ε / 2 : ℝ) : ℂ) * Complex.I) := by
        ring
      rw [hsub_eq, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith

/-- Odd dyadic approximation: for every `x : ℝ` and `m : ℕ`, `a = 2 * ⌊x * 2^m⌋ + 1` is odd and
`|(a : ℝ) / 2^(m + 1) - x| ≤ 1 / 2^(m + 1)`. -/
theorem exists_odd_dyadic_approx (x : ℝ) (m : ℕ) :
    ∃ a : ℤ, Odd a ∧ |(a : ℝ) / (2 : ℝ) ^ (m + 1) - x| ≤ 1 / (2 : ℝ) ^ (m + 1) := by
  let k : ℤ := ⌊x * (2 : ℝ) ^ m⌋
  refine ⟨2 * k + 1, ⟨k, rfl⟩, ?_⟩
  have h1 : (k : ℝ) ≤ x * (2 : ℝ) ^ m := Int.floor_le _
  have h2 : x * (2 : ℝ) ^ m < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (m + 1) := by positivity
  have hpow_succ : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := by ring
  rw [div_sub' hpow_pos.ne', abs_div, abs_of_pos hpow_pos,
    div_le_div_iff_of_pos_right hpow_pos, abs_le]
  push_cast
  rw [hpow_succ]
  constructor <;> linarith

/-- Every odd integer `a` and `m : ℕ` fits into a `GammaSubgroup` matrix `((a, b), (2^(m+1), d))`. -/
theorem exists_gamma_with_odd_top_dyadic_bottom
    (h_gamma_parity : ∀ {a b c d : ℤ} (hdet : a * d - b * c = 1),
      (⟨intMoebiusPerm a b c d hdet, a, b, c, d, hdet, rfl⟩ : ModularMoebiusGroup) ∈ GammaSubgroup ↔
        Odd a ∧ Odd d ∧ Even b ∧ Even c)
    {a : ℤ} (ha : Odd a) (m : ℕ) :
    ∃ (b d : ℤ) (hdet : a * d - b * (2 : ℤ) ^ (m + 1) = 1),
      (⟨intMoebiusPerm a b ((2 : ℤ) ^ (m + 1)) d hdet,
        a, b, (2 : ℤ) ^ (m + 1), d, hdet, rfl⟩ : ModularMoebiusGroup) ∈ GammaSubgroup := by
  obtain ⟨k, rfl⟩ := ha
  have hcop2 : IsCoprime (2 * k + 1) (2 : ℤ) := ⟨1, -k, by ring⟩
  obtain ⟨u, v, huv⟩ := hcop2.pow_right (n := m + 1)
  let b₀ : ℤ := -v
  have hdet₀ : (2 * k + 1) * u - b₀ * (2 : ℤ) ^ (m + 1) = 1 := by
    dsimp [b₀]; linear_combination huv
  have ha_odd : Odd (2 * k + 1) := ⟨k, rfl⟩
  have hau_odd : Odd ((2 * k + 1) * u) := by
    refine ⟨b₀ * (2 : ℤ) ^ m, ?_⟩
    calc (2 * k + 1) * u = 1 + b₀ * (2 : ℤ) ^ (m + 1) := by linear_combination hdet₀
      _ = 2 * (b₀ * (2 : ℤ) ^ m) + 1 := by ring
  have hu_odd : Odd u := (Int.odd_mul.mp hau_odd).2
  have hc_even : Even ((2 : ℤ) ^ (m + 1)) := ⟨(2 : ℤ) ^ m, by ring⟩
  rcases Int.even_or_odd b₀ with hb₀_even | hb₀_odd
  · exact ⟨b₀, u, hdet₀, (h_gamma_parity hdet₀).mpr ⟨ha_odd, hu_odd, hb₀_even, hc_even⟩⟩
  · let b : ℤ := b₀ + (2 * k + 1)
    let d : ℤ := u + (2 : ℤ) ^ (m + 1)
    have hdet : (2 * k + 1) * d - b * (2 : ℤ) ^ (m + 1) = 1 := by
      dsimp [b, d]; linear_combination hdet₀
    have hd_odd : Odd d := hu_odd.add_even hc_even
    have hb_even : Even b := hb₀_odd.add_odd ha_odd
    exact ⟨b, d, hdet, (h_gamma_parity hdet).mpr ⟨ha_odd, hd_odd, hb_even, hc_even⟩⟩

/-- On the upper-half-plane portion of EVERY open disc centered at a point of `ℝ = ∂Π⁺`,
`modularLambda` assumes every value in `ℂ \ {0, 1}`! -/
theorem modularLambda_image_ball_inter_upperHalfPlaneSet
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    (h_gamma_parity : ∀ {a b c d : ℤ} (hdet : a * d - b * c = 1),
      (⟨intMoebiusPerm a b c d hdet, a, b, c, d, hdet, rfl⟩ : ModularMoebiusGroup) ∈ GammaSubgroup ↔
        Odd a ∧ Odd d ∧ Even b ∧ Even c)
    {p : ℂ} (hp : p ∈ frontier UpperHalfPlaneSet) {r : ℝ} (hr : 0 < r) :
    modularLambda '' (Metric.ball p r ∩ UpperHalfPlaneSet) = Set.univ \ {0, 1} := by
  apply Set.Subset.antisymm
  · rw [← modularLambda_image_upperHalfPlaneSet h_exU]
    exact Set.image_mono Set.inter_subset_right
  · intro w hw
    obtain ⟨q, hq, hqw⟩ := lambdaOnQ_bijOn_fundamentalSetQ.surjOn hw
    have hq_im : 0 < q.im := hq.1
    have hp_im : p.im = 0 := by rw [frontier_upperHalfPlaneSet] at hp; exact hp
    have hp_eq : p = (p.re : ℂ) := Complex.ext rfl (by simp [hp_im])
    -- Pick `m : ℕ` so `1 / 2^(m+1) < r / 2` and `1 / ((2^(m+1))^2 * q.im) < r / 2`
    obtain ⟨m, hm⟩ := exists_nat_gt (max (2 / r) (2 / (r * q.im)))
    have hm_lt_pow_nat : m < 2 ^ (m + 1) := lt_trans (Nat.lt_succ_self m) m.succ.lt_two_pow_self
    have hm_lt_pow : (m : ℝ) < (2 : ℝ) ^ (m + 1) := by exact_mod_cast hm_lt_pow_nat
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (m + 1) := by positivity
    have hpow_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
      have : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
      exact_mod_cast this
    have hpow_gt1 : 2 / r < (2 : ℝ) ^ (m + 1) :=
      lt_trans (lt_of_le_of_lt (le_max_left _ _) hm) hm_lt_pow
    have hpow_gt2 : 2 / (r * q.im) < ((2 : ℝ) ^ (m + 1)) ^ 2 := by
      have hlt : 2 / (r * q.im) < (2 : ℝ) ^ (m + 1) :=
        lt_trans (lt_of_le_of_lt (le_max_right _ _) hm) hm_lt_pow
      have hle_sq : (2 : ℝ) ^ (m + 1) ≤ ((2 : ℝ) ^ (m + 1)) ^ 2 := by nlinarith
      linarith
    have hhalf1 : 1 / (2 : ℝ) ^ (m + 1) < r / 2 := by
      rw [div_lt_div_iff₀ hpow_pos (by norm_num : (0 : ℝ) < 2)]
      have := (div_lt_iff₀ hr).mp hpow_gt1
      linarith
    have hhalf2 : 1 / (((2 : ℝ) ^ (m + 1)) ^ 2 * q.im) < r / 2 := by
      have hden_pos : 0 < ((2 : ℝ) ^ (m + 1)) ^ 2 * q.im := mul_pos (sq_pos_of_pos hpow_pos) hq_im
      rw [div_lt_div_iff₀ hden_pos (by norm_num : (0 : ℝ) < 2)]
      have := (div_lt_iff₀ (mul_pos hr hq_im)).mp hpow_gt2
      linarith
    obtain ⟨a, ha_odd, ha_approx⟩ := exists_odd_dyadic_approx p.re m
    obtain ⟨b, d, hdet, hγ_mem⟩ :=
      exists_gamma_with_odd_top_dyadic_bottom h_gamma_parity ha_odd m
    let c : ℤ := (2 : ℤ) ^ (m + 1)
    let γ : GammaSubgroup :=
      ⟨⟨intMoebiusPerm a b c d hdet, a, b, c, d, hdet, rfl⟩, hγ_mem⟩
    let z : ℂ := intMoebius a b c d q
    have hz_up : z ∈ UpperHalfPlaneSet :=
      intMoebius_mem_upperHalfPlaneSet hdet (fundamentalSetQ_subset_upperHalfPlaneSet hq)
    have hz_lam : modularLambda z = w := by
      have hmod := modularLambda_apply_gamma_q h_exU γ hq
      simpa [γ, z] using hmod.trans hqw
    -- Estimate `‖z - a / c‖ ≤ 1 / (c^2 * q.im)`
    have hc_real : (c : ℝ) = (2 : ℝ) ^ (m + 1) := by simp [c]
    have hc_nz : (c : ℂ) ≠ 0 := by
      have : (c : ℝ) ≠ 0 := by rw [hc_real]; exact hpow_pos.ne'
      exact_mod_cast this
    have hden_nz : (c : ℂ) * q + (d : ℂ) ≠ 0 :=
      intMoebius_denom_ne_zero hdet (fundamentalSetQ_subset_upperHalfPlaneSet hq)
    have hz_sub_ac : z - (a : ℂ) / (c : ℂ) = -1 / ((c : ℂ) * ((c : ℂ) * q + (d : ℂ))) := by
      dsimp [z]; unfold intMoebius
      have hdetC : (a : ℂ) * (d : ℂ) - (b : ℂ) * (c : ℂ) = 1 := by exact_mod_cast hdet
      rw [div_sub_div _ _ hden_nz hc_nz]
      have hnum : ((a : ℂ) * q + (b : ℂ)) * (c : ℂ) - ((c : ℂ) * q + (d : ℂ)) * (a : ℂ) = -1 := by
        linear_combination -hdetC
      have hden_comm : ((c : ℂ) * q + (d : ℂ)) * (c : ℂ) = (c : ℂ) * ((c : ℂ) * q + (d : ℂ)) :=
        mul_comm _ _
      rw [hnum, hden_comm]
    have hden_norm_ge : (c : ℝ) * q.im ≤ ‖(c : ℂ) * q + (d : ℂ)‖ := by
      have him_eq : ((c : ℂ) * q + (d : ℂ)).im = (c : ℝ) * q.im := by simp
      calc (c : ℝ) * q.im = |((c : ℂ) * q + (d : ℂ)).im| := by
            rw [him_eq, abs_of_pos (by rw [hc_real]; exact mul_pos hpow_pos hq_im)]
        _ ≤ ‖(c : ℂ) * q + (d : ℂ)‖ := Complex.abs_im_le_norm _
    have hz_dist_ac : ‖z - (a : ℂ) / (c : ℂ)‖ < r / 2 := by
      rw [hz_sub_ac, norm_div, norm_neg, norm_one, norm_mul, Complex.norm_intCast,
        abs_of_pos (by rw [hc_real]; exact hpow_pos)]
      have hprod_le : (c : ℝ) ^ 2 * q.im ≤ (c : ℝ) * ‖(c : ℂ) * q + (d : ℂ)‖ := by
        have hc_pos : 0 < (c : ℝ) := by rw [hc_real]; exact hpow_pos
        nlinarith
      have hle : 1 / ((c : ℝ) * ‖(c : ℂ) * q + (d : ℂ)‖) ≤ 1 / ((c : ℝ) ^ 2 * q.im) :=
        one_div_le_one_div_of_le (mul_pos (sq_pos_of_pos (by rw [hc_real]; exact hpow_pos)) hq_im)
          hprod_le
      rw [hc_real] at hle ⊢
      exact lt_of_le_of_lt hle hhalf2
    have hac_dist_p : ‖(a : ℂ) / (c : ℂ) - p‖ ≤ 1 / (2 : ℝ) ^ (m + 1) := by
      rw [hp_eq]
      have hcast : (a : ℂ) / (c : ℂ) - (p.re : ℂ) =
          (((a : ℝ) / (2 : ℝ) ^ (m + 1) - p.re : ℝ) : ℂ) := by
        have hc_complex : (c : ℂ) = (((2 : ℝ) ^ (m + 1) : ℝ) : ℂ) := by push_cast [c]; rfl
        rw [hc_complex, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_intCast]
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      exact ha_approx
    have hz_ball : z ∈ Metric.ball p r := by
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖z - p‖ = ‖(z - (a : ℂ) / (c : ℂ)) + ((a : ℂ) / (c : ℂ) - p)‖ := by ring_nf
        _ ≤ ‖z - (a : ℂ) / (c : ℂ)‖ + ‖(a : ℂ) / (c : ℂ) - p‖ := norm_add_le _ _
        _ < r / 2 + r / 2 := add_lt_add hz_dist_ac (lt_of_le_of_lt hac_dist_p hhalf1)
        _ = r := by ring
    exact ⟨z, ⟨hz_ball, hz_up⟩, hz_lam⟩

/-- Local non-extendability across any boundary point `p ∈ frontier UpperHalfPlaneSet`: no function
continuous at `p` on an open neighborhood `U` of `p` can agree with `modularLambda` on `U ∩ Π⁺`. -/
theorem modularLambda_not_continuousAt_extension_frontier
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    (h_gamma_parity : ∀ {a b c d : ℤ} (hdet : a * d - b * c = 1),
      (⟨intMoebiusPerm a b c d hdet, a, b, c, d, hdet, rfl⟩ : ModularMoebiusGroup) ∈ GammaSubgroup ↔
        Odd a ∧ Odd d ∧ Even b ∧ Even c)
    {p : ℂ} (hp : p ∈ frontier UpperHalfPlaneSet)
    {U : Set ℂ} (hU : IsOpen U) (hpU : p ∈ U)
    {g : ℂ → ℂ} (hg : ContinuousAt g p) :
    ¬ Set.EqOn g modularLambda (U ∩ UpperHalfPlaneSet) := by
  intro heq
  obtain ⟨r₁, hr₁, hball_U⟩ := Metric.isOpen_iff.mp hU p hpU
  obtain ⟨r₂, hr₂, hball_g⟩ := Metric.continuousAt_iff.mp hg 1 one_pos
  let r : ℝ := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  let M : ℝ := max 2 (‖g p‖ + 2)
  let w : ℂ := (M : ℂ)
  have hw_mem : w ∈ Set.univ \ ({0, 1} : Set ℂ) := by
    refine ⟨Set.mem_univ _, ?_⟩
    rintro (h0 | h1)
    · have := congrArg Complex.re h0
      simp only [w, Complex.ofReal_re, Complex.zero_re] at this
      linarith [le_max_left 2 (‖g p‖ + 2)]
    · have h1_eq : w = 1 := h1
      have := congrArg Complex.re h1_eq
      simp only [w, Complex.ofReal_re, Complex.one_re] at this
      linarith [le_max_left 2 (‖g p‖ + 2)]
  have hw_img : w ∈ modularLambda '' (Metric.ball p r ∩ UpperHalfPlaneSet) := by
    rw [modularLambda_image_ball_inter_upperHalfPlaneSet h_exU h_gamma_parity hp hr]
    exact hw_mem
  rcases hw_img with ⟨z, ⟨hz_ball, hz_up⟩, hz_lam⟩
  have hz_U : z ∈ U := hball_U (Metric.ball_subset_ball (min_le_left r₁ r₂) hz_ball)
  have hgz_eq : g z = w := (heq ⟨hz_U, hz_up⟩).trans hz_lam
  have hdist_lt : ‖g z - g p‖ < 1 := by
    simpa [dist_eq_norm] using hball_g (lt_of_lt_of_le hz_ball (min_le_right r₁ r₂))
  have hnorm_w : ‖g p‖ + 2 ≤ ‖w‖ := by
    dsimp [w]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le two_pos (le_max_left _ _))]
    exact le_max_right 2 (‖g p‖ + 2)
  have htri : ‖w‖ ≤ ‖g z - g p‖ + ‖g p‖ := by
    rw [← hgz_eq]
    simpa using norm_add_le (g z - g p) (g p)
  linarith

/-- Global natural-boundary property (Rudin 16.20): `Π⁺` is the natural domain of `modularLambda`;
there is no region `Ω` properly containing `Π⁺` to which `modularLambda` extends holomorphically. -/
theorem modularLambda_natural_boundary
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    (h_gamma_parity : ∀ {a b c d : ℤ} (hdet : a * d - b * c = 1),
      (⟨intMoebiusPerm a b c d hdet, a, b, c, d, hdet, rfl⟩ : ModularMoebiusGroup) ∈ GammaSubgroup ↔
        Odd a ∧ Odd d ∧ Even b ∧ Even c)
    {Ω : Set ℂ} (hΩ : RudinRCA.Chapter10.IsRegion Ω) (hssub : UpperHalfPlaneSet ⊂ Ω) :
    ¬ ∃ g : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn g Ω ∧
        Set.EqOn g modularLambda UpperHalfPlaneSet := by
  rintro ⟨g, hg_holo, heq⟩
  -- Since `Ω` is connected and meets both `Π⁺` and `(Π⁺)ᶜ`, `Ω` must meet `frontier Π⁺`
  obtain ⟨z₂, hz₂_Ω, hz₂_not⟩ := Set.exists_of_ssubset hssub
  by_cases hfront : (Ω ∩ frontier UpperHalfPlaneSet).Nonempty
  · obtain ⟨p, hp_Ω, hp_fr⟩ := hfront
    exact modularLambda_not_continuousAt_extension_frontier h_exU h_gamma_parity hp_fr
      hΩ.1 hp_Ω (hg_holo p hp_Ω).continuousAt (heq.mono Set.inter_subset_right)
  · rw [Set.not_nonempty_iff_eq_empty] at hfront
    have hz₁_Ω : Complex.I ∈ Ω := hssub.1 I_mem_upperHalfPlaneSet
    have hz₂_not_cl : z₂ ∈ (closure UpperHalfPlaneSet)ᶜ := by
      intro hcl
      have hfr : z₂ ∈ frontier UpperHalfPlaneSet := by
        change z₂ ∈ closure UpperHalfPlaneSet \ interior UpperHalfPlaneSet
        rw [isOpen_upperHalfPlaneSet.interior_eq]
        exact ⟨hcl, hz₂_not⟩
      have hmem : z₂ ∈ Ω ∩ frontier UpperHalfPlaneSet := ⟨hz₂_Ω, hfr⟩
      rw [hfront] at hmem
      exact hmem
    have hsub_cov : Ω ⊆ UpperHalfPlaneSet ∪ (closure UpperHalfPlaneSet)ᶜ := by
      intro z hz
      by_cases hz_up : z ∈ UpperHalfPlaneSet
      · exact Or.inl hz_up
      · right
        intro hcl
        have hfr : z ∈ frontier UpperHalfPlaneSet := by
          change z ∈ closure UpperHalfPlaneSet \ interior UpperHalfPlaneSet
          rw [isOpen_upperHalfPlaneSet.interior_eq]
          exact ⟨hcl, hz_up⟩
        have hmem : z ∈ Ω ∩ frontier UpperHalfPlaneSet := ⟨hz, hfr⟩
        rw [hfront] at hmem
        exact hmem
    have hdisj : Ω ∩ (UpperHalfPlaneSet ∩ (closure UpperHalfPlaneSet)ᶜ) = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hz_up, hnot_cl⟩
      exact hnot_cl (subset_closure hz_up)
    have hnonemp := hΩ.2.2 UpperHalfPlaneSet (closure UpperHalfPlaneSet)ᶜ
      isOpen_upperHalfPlaneSet isClosed_closure.isOpen_compl hsub_cov
      ⟨Complex.I, hz₁_Ω, I_mem_upperHalfPlaneSet⟩ ⟨z₂, hz₂_Ω, hz₂_not_cl⟩
    rw [hdisj] at hnonemp
    exact Set.not_nonempty_empty hnonemp

/-- **Theorem 16.20** (Rudin, *Real and Complex Analysis*, 3rd ed., pp. 330–331):
The elliptic modular function `modularLambda` (`λ`) on the upper half-plane `Π⁺` satisfies:
1. `λ ∈ H(Π⁺)` with `λ'(z) ≠ 0` for every `z ∈ Π⁺`;
2. `λ` is `Γ`-invariant (`IsModularFunctionFor GammaSubgroup modularLambda`), with
   `λ(z₁) = λ(z₂) ↔ z₁ ∈ Γ · z₂` on `Π⁺`;
3. `λ` maps the fundamental set `Q` bijectively onto `ℂ \ {0, 1}` (hence is injective on `Q`
   and has range `λ(Π⁺) = ℂ \ {0, 1}`);
4. The real axis `ℝ = ∂Π⁺` is a natural boundary of `λ`: on the `Π⁺`-part of every open disc
   centered at a real point, `λ` assumes every value in `ℂ \ {0, 1}`, and `λ` admits no holomorphic
   extension to any region `Ω` properly containing `Π⁺`. -/
theorem theorem16_20_of_deps
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    (h_gamma_parity : ∀ {a b c d : ℤ} (hdet : a * d - b * c = 1),
      (⟨intMoebiusPerm a b c d hdet, a, b, c, d, hdet, rfl⟩ : ModularMoebiusGroup) ∈ GammaSubgroup ↔
        Odd a ∧ Odd d ∧ Even b ∧ Even c) :
    RudinRCA.Chapter10.HolomorphicOn modularLambda UpperHalfPlaneSet ∧
      (∀ z ∈ UpperHalfPlaneSet, deriv modularLambda z ≠ 0) ∧
      IsModularFunctionFor GammaSubgroup modularLambda ∧
      Set.BijOn modularLambda FundamentalSetQ (Set.univ \ {0, 1}) ∧
      modularLambda '' UpperHalfPlaneSet = Set.univ \ {0, 1} ∧
      (∀ z₁ ∈ UpperHalfPlaneSet, ∀ (z₂ : ℂ) (hz₂ : z₂ ∈ UpperHalfPlaneSet),
        modularLambda z₁ = modularLambda z₂ ↔
          ∃ γ : GammaSubgroup, (γ.1.1 ⟨z₂, hz₂⟩).1 = z₁) ∧
      (∀ p ∈ frontier UpperHalfPlaneSet, ∀ r > 0,
        modularLambda '' (Metric.ball p r ∩ UpperHalfPlaneSet) = Set.univ \ {0, 1}) ∧
      (∀ Ω : Set ℂ, RudinRCA.Chapter10.IsRegion Ω → UpperHalfPlaneSet ⊂ Ω →
        ¬ ∃ g : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn g Ω ∧
            Set.EqOn g modularLambda UpperHalfPlaneSet) :=
  ⟨modularLambda_holomorphicOn h_exU,
   fun _ hz => (modularLambda_holo_and_deriv_ne_zero h_exU hz).2,
   modularLambda_isModularFunctionFor_gamma h_exU,
   modularLambda_bijOn_fundamentalSetQ h_exU,
   modularLambda_image_upperHalfPlaneSet h_exU,
   fun _ hz₁ _ hz₂ => modularLambda_eq_iff_gamma_orbit h_exU hz₁ hz₂,
   fun _ hp _ hr => modularLambda_image_ball_inter_upperHalfPlaneSet h_exU h_gamma_parity hp hr,
   fun _ hΩ hssub => modularLambda_natural_boundary h_exU h_gamma_parity hΩ hssub⟩

end ModularLambdaProperties

/-!
## Section 4: Little vs. Big Picard (`16.21`) and Little Picard's Theorem (`16.22`)

### 16.21: Exposition — Little Picard vs. Big Picard (Rudin pp. 331–332)
In node `16.21`, Rudin states Little Picard's theorem (proved in `16.22` below) and contrasts it
with Big Picard's theorem (which Rudin explicitly does not prove in Chapter 16):
- **Little Picard** (`LittlePicardStatement`, discharged unconditionally by `theorem16_22_of_deps`):
  every entire function omitting two distinct complex values is constant; equivalently, every
  nonconstant entire function assumes every complex value with at most one exception
  (`theorem16_21_nonconstant_entire_omits_at_most_one_of_deps`), and if a nonconstant entire
  function actually omits a value `w₀`, it assumes every `w ≠ w₀` infinitely often
  (`theorem16_21_entire_omitting_one_infinite_fibers_of_deps`).
- **Big Picard** (`BigPicardStatement`, recorded as a `Prop` definition without claiming it proved
  unconditionally, per `SCOPING-G.md` line 84 & Caution 6): near an isolated essential singularity
  `z₀ ∈ Ω`, `f` assumes every complex value with at most one exception on every punctured disc
  `B(z₀, r) \ {z₀} ⊆ Ω`, hence assumes every complex value *infinitely often* near `z₀` with at
  most one exception (`theorem16_21_bigPicard_infinite_preimages`). Applying this to `w ↦ f(w⁻¹)`
  at `0` (`entire_nonpolynomial_hasEssentialSingularity_inv`) yields that every nonpolynomial
  entire function assumes every complex value infinitely often with at most one exception
  (`theorem16_21_bigPicard_nonpolynomial_entire`), and in particular implies `LittlePicardStatement`
  (`theorem16_21_bigPicard_implies_littlePicard`).
-/

section PicardExpositionAndProof

/-- **Little Picard's Theorem (statement, Rudin 16.21 & 16.22):**
Every entire function omitting two distinct complex values is constant.
Discharged unconditionally below by `theorem16_22_of_deps` and `littlePicardStatement_of_deps`. -/
def LittlePicardStatement : Prop :=
  ∀ (f : ℂ → ℂ) (α β : ℂ),
    Differentiable ℂ f → α ≠ β → (∀ z : ℂ, f z ≠ α ∧ f z ≠ β) →
      ∃ c : ℂ, ∀ z : ℂ, f z = c

/-- **Big Picard's Theorem (statement, Rudin 16.21, pp. 331–332):**
If `f` has an isolated essential singularity at `z₀ ∈ Ω`, then on every punctured open disc
`B(z₀, r) \ {z₀}` with `r > 0` and `B(z₀, r) ⊆ Ω`, `f` assumes every complex value with at most
one exception. Recorded as a `Prop` definition to distinguish it cleanly from Little Picard, since
Rudin states Big Picard without proof in Chapter 16. -/
def BigPicardStatement : Prop :=
  ∀ (f : ℂ → ℂ) (Ω : Set ℂ) (z₀ : ℂ),
    RudinRCA.Chapter10.HasEssentialSingularity f Ω z₀ →
    ∀ r > 0, Metric.ball z₀ r ⊆ Ω →
      ∃ w₀ : ℂ, ∀ w : ℂ, w ≠ w₀ → ∃ z ∈ Metric.ball z₀ r \ {z₀}, f z = w

/-- Equivalent two-omitted-values formulation of `BigPicardStatement` (Rudin 16.21): near an
isolated essential singularity `z₀`, `f` cannot omit two distinct complex values `α ≠ β` on any
punctured ball `B(z₀, r) \ {z₀} ⊆ Ω`. -/
theorem bigPicardStatement_iff_no_two_omitted :
    BigPicardStatement ↔
      ∀ (f : ℂ → ℂ) (Ω : Set ℂ) (z₀ : ℂ),
        RudinRCA.Chapter10.HasEssentialSingularity f Ω z₀ →
        ∀ r > 0, Metric.ball z₀ r ⊆ Ω →
        ∀ α β : ℂ, α ≠ β →
          ¬ (∀ z ∈ Metric.ball z₀ r \ {z₀}, f z ≠ α ∧ f z ≠ β) := by
  constructor
  · intro hBP f Ω z₀ hess r hr hsub α β hne homit
    obtain ⟨w₀, hw₀⟩ := hBP f Ω z₀ hess r hr hsub
    by_cases hα : α = w₀
    · have hβ : β ≠ w₀ := by rw [← hα]; exact hne.symm
      obtain ⟨z, hz, hfz⟩ := hw₀ β hβ
      exact (homit z hz).2 hfz
    · obtain ⟨z, hz, hfz⟩ := hw₀ α hα
      exact (homit z hz).1 hfz
  · intro hno f Ω z₀ hess r hr hsub
    by_contra hnot
    push Not at hnot
    obtain ⟨α, _, hα_omit⟩ := hnot 0
    obtain ⟨β, hβα, hβ_omit⟩ := hnot α
    exact hno f Ω z₀ hess r hr hsub α β hβα.symm (fun z hz ↦ ⟨hα_omit z hz, hβ_omit z hz⟩)

/-- **Infinite-fiber consequence of Big Picard (Rudin 16.21):**
Assuming `BigPicardStatement`, near an isolated essential singularity `z₀ ∈ Ω`, `f` assumes every
complex value *infinitely often* in every punctured ball `B(z₀, r) \ {z₀} ⊆ Ω`, with at most one
exception. -/
theorem theorem16_21_bigPicard_infinite_preimages
    (hBP : BigPicardStatement)
    {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ}
    (hess : RudinRCA.Chapter10.HasEssentialSingularity f Ω z₀)
    {r : ℝ} (hr : 0 < r) (hsub : Metric.ball z₀ r ⊆ Ω) :
    ∃ w₀ : ℂ, ∀ w : ℂ, w ≠ w₀ →
      ({z ∈ Metric.ball z₀ r \ {z₀} | f z = w}).Infinite := by
  classical
  by_contra hnot
  push Not at hnot
  obtain ⟨w₁, _, hw₁_fin⟩ := hnot 0
  obtain ⟨w₂, hw₂₁, hw₂_fin⟩ := hnot w₁
  let S : Set ℂ :=
    {z ∈ Metric.ball z₀ r \ {z₀} | f z = w₁} ∪ {z ∈ Metric.ball z₀ r \ {z₀} | f z = w₂}
  have hS_fin : S.Finite := hw₁_fin.union hw₂_fin
  let F : Finset ℂ := hS_fin.toFinset
  have hF_pos : ∀ z ∈ F, 0 < dist z z₀ := by
    intro z hzF
    have hzS : z ∈ S := hS_fin.mem_toFinset.mp hzF
    rcases hzS with ⟨⟨_, hz_ne⟩, _⟩ | ⟨⟨_, hz_ne⟩, _⟩ <;>
      exact dist_pos.mpr hz_ne
  by_cases hF_ne : F.Nonempty
  · let r' : ℝ := min r (F.inf' hF_ne (fun z ↦ dist z z₀))
    have hr'_pos : 0 < r' :=
      lt_min hr ((Finset.lt_inf'_iff hF_ne).mpr hF_pos)
    have hr'_le : r' ≤ r := min_le_left _ _
    have hsub' : Metric.ball z₀ r' ⊆ Ω := (Metric.ball_subset_ball hr'_le).trans hsub
    refine (bigPicardStatement_iff_no_two_omitted.mp hBP) f Ω z₀ hess r' hr'_pos hsub'
      w₁ w₂ hw₂₁.symm ?_
    intro z hz
    have hz_ball_r : z ∈ Metric.ball z₀ r \ {z₀} :=
      ⟨Metric.ball_subset_ball hr'_le hz.1, hz.2⟩
    have hz_not_F : z ∉ F := by
      intro hzF
      have hle1 : r' ≤ F.inf' hF_ne (fun u ↦ dist u z₀) := min_le_right _ _
      have hle2 : F.inf' hF_ne (fun u ↦ dist u z₀) ≤ dist z z₀ :=
        Finset.inf'_le (fun u ↦ dist u z₀) hzF
      have hlt : dist z z₀ < r' := hz.1
      linarith
    refine ⟨fun h1 ↦ hz_not_F (hS_fin.mem_toFinset.mpr (Or.inl ⟨hz_ball_r, h1⟩)),
            fun h2 ↦ hz_not_F (hS_fin.mem_toFinset.mpr (Or.inr ⟨hz_ball_r, h2⟩))⟩
  · refine (bigPicardStatement_iff_no_two_omitted.mp hBP) f Ω z₀ hess r hr hsub
      w₁ w₂ hw₂₁.symm ?_
    intro z hz
    refine ⟨fun h1 ↦ hF_ne ⟨z, hS_fin.mem_toFinset.mpr (Or.inl ⟨hz, h1⟩)⟩,
            fun h2 ↦ hF_ne ⟨z, hS_fin.mem_toFinset.mpr (Or.inr ⟨hz, h2⟩)⟩⟩

/-- Liouville helper: if `h` is entire and `h(w⁻¹)` agrees on `ℂ \ {0}` with a function `G`
holomorphic at `0`, then `h` is bounded on all of `ℂ` and therefore constant (`10.23`). -/
private theorem entire_eq_const_of_eq_holo_inv {h G : ℂ → ℂ}
    (hh : Differentiable ℂ h)
    (hG : RudinRCA.Chapter10.HolomorphicOn G Set.univ)
    (heq : ∀ w : ℂ, w ≠ 0 → G w = h w⁻¹) :
    ∃ c₀ : ℂ, ∀ z : ℂ, h z = c₀ := by
  have hG_cont : ContinuousAt G 0 := (hG 0 (Set.mem_univ 0)).continuousAt
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hG_cont 1 zero_lt_one
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : ℂ) (2 / δ)).exists_bound_of_continuousOn hh.continuous.continuousOn
  let B : ℝ := max C (‖G 0‖ + 1)
  have hrange_sub : Set.range h ⊆ Metric.closedBall (0 : ℂ) B := by
    rintro _ ⟨z, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    rcases le_or_gt ‖z‖ (2 / δ) with hle | hgt
    · have hz_cb : z ∈ Metric.closedBall (0 : ℂ) (2 / δ) := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hle
      exact (hC z hz_cb).trans (le_max_left _ _)
    · have hz_pos : 0 < ‖z‖ := lt_trans (div_pos zero_lt_two hδ_pos) hgt
      have hz0 : z ≠ 0 := norm_pos_iff.mp hz_pos
      have hhz : h z = G z⁻¹ := by
        simpa [inv_inv] using (heq z⁻¹ (inv_ne_zero hz0)).symm
      have hdist_inv : dist z⁻¹ (0 : ℂ) < δ := by
        rw [dist_zero_right, norm_inv, inv_eq_one_div, div_lt_iff₀ hz_pos]
        have h2 : 2 < ‖z‖ * δ := (div_lt_iff₀ hδ_pos).mp hgt
        linarith
      have hG_dist : ‖G z⁻¹ - G 0‖ < 1 := by
        simpa [dist_eq_norm] using hδ hdist_inv
      have htri : ‖G z⁻¹‖ ≤ ‖G z⁻¹ - G 0‖ + ‖G 0‖ := by
        simpa using norm_add_le (G z⁻¹ - G 0) (G 0)
      rw [hhz]
      exact (htri.trans (by linarith)).trans (le_max_right _ _)
  exact RudinRCA.Chapter10.liouville (fun z _ ↦ hh z)
    (Metric.isBounded_closedBall.subset hrange_sub)

/-- If `f` is a nonpolynomial entire function, then `w ↦ f(w⁻¹)` has an isolated essential
singularity at `0` in the sense of `RudinRCA.Chapter10.HasEssentialSingularity` (matching
`RudinRCA.Chapter13.entire_nonpolynomial_hasEssentialSingularityAtInfinity` at `∞`). -/
theorem entire_nonpolynomial_hasEssentialSingularity_inv {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ P : Polynomial ℂ, ∀ z : ℂ, f z = P.eval z) :
    RudinRCA.Chapter10.HasEssentialSingularity (fun w : ℂ ↦ f w⁻¹) Set.univ 0 := by
  have hiso : RudinRCA.Chapter10.HasIsolatedSingularity (fun w : ℂ ↦ f w⁻¹) Set.univ 0 := by
    refine ⟨isOpen_univ, Set.mem_univ 0, fun w hw ↦ ?_⟩
    have hw0 : w ≠ 0 := hw.2
    exact DifferentiableAt.comp w (hf w⁻¹) (differentiableAt_inv hw0)
  refine ⟨hiso, ?_, ?_⟩
  · -- Not removable at `0`
    rintro ⟨G, hG_holo, heq⟩
    obtain ⟨c₀, hc₀⟩ := entire_eq_const_of_eq_holo_inv hf hG_holo
      (fun w hw0 ↦ heq ⟨Set.mem_univ w, hw0⟩)
    exact hnp ⟨Polynomial.C c₀, fun z ↦ by simp [hc₀ z]⟩
  · -- Not a pole at `0`
    rintro ⟨_, G, Q, hG_holo, ⟨m, c, _, _, hQ_eq⟩, heq⟩
    let P_prin : Polynomial ℂ :=
      ∑ k ∈ Finset.Icc 1 m, Polynomial.C (c k) * Polynomial.X ^ k
    have hP_eval : ∀ z : ℂ, P_prin.eval z = ∑ k ∈ Finset.Icc 1 m, c k * z ^ k := by
      intro z
      simp [P_prin, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    have hP_diff : Differentiable ℂ (fun z : ℂ ↦ P_prin.eval z) := by
      have hsum_diff : Differentiable ℂ (fun z : ℂ ↦ ∑ k ∈ Finset.Icc 1 m, c k * z ^ k) :=
        Differentiable.fun_sum fun k _ ↦ (differentiable_id.pow k).const_mul (c k)
      simpa [funext hP_eval] using hsum_diff
    have hG_diff_eq : ∀ w : ℂ, w ≠ 0 → G w = f w⁻¹ - P_prin.eval w⁻¹ := by
      intro w hw0
      have hfw : f w⁻¹ = G w + Q w := heq ⟨Set.mem_univ w, hw0⟩
      have hQw : Q w = P_prin.eval w⁻¹ := by
        rw [hQ_eq w, hP_eval w⁻¹]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [sub_zero]
      rw [hfw, hQw, add_sub_cancel_right]
    obtain ⟨c₀, hc₀⟩ :=
      entire_eq_const_of_eq_holo_inv (hf.sub hP_diff) hG_holo hG_diff_eq
    refine hnp ⟨P_prin + Polynomial.C c₀, fun z ↦ ?_⟩
    rw [Polynomial.eval_add, Polynomial.eval_C]
    have hc₀z : f z - P_prin.eval z = c₀ := hc₀ z
    linear_combination hc₀z

/-- **Nonpolynomial entire consequence of Big Picard (Rudin 16.21, pp. 331–332):**
Assuming `BigPicardStatement`, every nonpolynomial entire function assumes every complex value
infinitely often, with at most one exception. (Per `SCOPING-G.md` Caution 6, this stronger assertion
depends on `BigPicardStatement` via the essential singularity at `∞` rather than Little Picard
alone.) -/
theorem theorem16_21_bigPicard_nonpolynomial_entire
    (hBP : BigPicardStatement)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ P : Polynomial ℂ, ∀ z : ℂ, f z = P.eval z) :
    ∃ w₀ : ℂ, ∀ w : ℂ, w ≠ w₀ → ({z : ℂ | f z = w}).Infinite := by
  have hess := entire_nonpolynomial_hasEssentialSingularity_inv hf hnp
  obtain ⟨w₀, hw₀⟩ :=
    theorem16_21_bigPicard_infinite_preimages hBP hess zero_lt_one (Set.subset_univ _)
  refine ⟨w₀, fun w hw ↦ ?_⟩
  have hinf := (hw₀ w hw).image (inv_injective.injOn)
  refine hinf.mono ?_
  rintro _ ⟨u, ⟨_, hfu⟩, rfl⟩
  exact hfu

/-- `BigPicardStatement` logically implies `LittlePicardStatement` (Rudin 16.21). -/
theorem theorem16_21_bigPicard_implies_littlePicard :
    BigPicardStatement → LittlePicardStatement := by
  intro hBP f α β hf hne homit
  by_cases hpoly : ∃ P : Polynomial ℂ, ∀ z : ℂ, f z = P.eval z
  · rcases hpoly with ⟨P, hP⟩
    by_cases hdeg : 0 < P.degree
    · have hdeg_sub : 0 < (P - Polynomial.C α).degree := by
        rwa [Polynomial.degree_sub_C hdeg]
      obtain ⟨z, hz⟩ := RudinRCA.Chapter10.nonconstant_polynomial_has_zero hdeg_sub
      rw [Polynomial.eval_sub, Polynomial.eval_C, sub_eq_zero, ← hP z] at hz
      exact False.elim ((homit z).1 hz)
    · push Not at hdeg
      let c₀ : ℂ := P.coeff 0
      have hP_const : P = Polynomial.C c₀ := Polynomial.eq_C_of_degree_le_zero hdeg
      refine ⟨c₀, fun z ↦ ?_⟩
      rw [hP z, hP_const, Polynomial.eval_C]
  · obtain ⟨w₀, hw₀⟩ := theorem16_21_bigPicard_nonpolynomial_entire hBP hf hpoly
    by_cases hα : α = w₀
    · have hβ : β ≠ w₀ := by rw [← hα]; exact hne.symm
      obtain ⟨z, hz⟩ := (hw₀ β hβ).nonempty
      exact False.elim ((homit z).2 hz)
    · obtain ⟨z, hz⟩ := (hw₀ α hα).nonempty
      exact False.elim ((homit z).1 hz)

/-!
### 16.22: Proof of Little Picard's Theorem via `modularLambda` and Monodromy (Rudin p. 332)
-/

/-- Identity uniqueness for holomorphic lifts through `modularLambda`: two holomorphic maps
`g₁, g₂ : D → Π⁺` on an open preconnected set `D` satisfying `λ ∘ g₁ = λ ∘ g₂` that agree at a
single point `p₀ ∈ D` agree throughout `D`. -/
private theorem eqOn_lifts_of_modularLambda
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    {D : Set ℂ} (hD_open : IsOpen D) (hD_pre : IsPreconnected D)
    {g₁ g₂ : ℂ → ℂ} (hg₁ : DifferentiableOn ℂ g₁ D) (hg₂ : DifferentiableOn ℂ g₂ D)
    (hup₁ : ∀ z ∈ D, g₁ z ∈ UpperHalfPlaneSet)
    (hlam : ∀ z ∈ D, modularLambda (g₁ z) = modularLambda (g₂ z))
    {p₀ : ℂ} (hp₀ : p₀ ∈ D) (heq₀ : g₁ p₀ = g₂ p₀) :
    Set.EqOn g₁ g₂ D := by
  let q₀ : ℂ := g₁ p₀
  have hq₀ : q₀ ∈ UpperHalfPlaneSet := hup₁ p₀ hp₀
  obtain ⟨U, _, _, hU_open, hq₀_U, _, _, _, hbij, _, _, _, _, _⟩ :=
    RudinRCA.Chapter10.theorem10_30 isOpen_upperHalfPlaneSet (modularLambda_holomorphicOn h_exU)
      hq₀ (modularLambda_holo_and_deriv_ne_zero h_exU hq₀).2
  have hg₁_cont : ContinuousAt g₁ p₀ := (hg₁.differentiableAt (hD_open.mem_nhds hp₀)).continuousAt
  have hg₂_cont : ContinuousAt g₂ p₀ := (hg₂.differentiableAt (hD_open.mem_nhds hp₀)).continuousAt
  have hev₁ : ∀ᶠ z in 𝓝 p₀, g₁ z ∈ U := hg₁_cont.eventually (hU_open.mem_nhds hq₀_U)
  have hev₂ : ∀ᶠ z in 𝓝 p₀, g₂ z ∈ U :=
    hg₂_cont.eventually (hU_open.mem_nhds (heq₀ ▸ hq₀_U))
  have hev : g₁ =ᶠ[𝓝 p₀] g₂ := by
    filter_upwards [hD_open.mem_nhds hp₀, hev₁, hev₂] with z hzD hz₁ hz₂
    exact hbij.injOn hz₁ hz₂ (hlam z hzD)
  exact (hg₁.analyticOnNhd hD_open).eqOn_of_preconnected_of_eventuallyEq
    (hg₂.analyticOnNhd hD_open) hD_pre hp₀ hev

/-- Local holomorphic right inverse of `modularLambda` near any `w₀ ∈ ℂ \ {0, 1}`, obtained from
`10.30` since `modularLambda '' Π⁺ = ℂ \ {0, 1}` and `deriv modularLambda ≠ 0` on `Π⁺`. -/
private theorem exists_local_right_inverse_modularLambda
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    {w₀ : ℂ} (hw0 : w₀ ≠ 0) (hw1 : w₀ ≠ 1) :
    ∃ (r₀ : ℝ) (g₀ : ℂ → ℂ),
      0 < r₀ ∧
      DifferentiableOn ℂ g₀ (Metric.ball w₀ r₀) ∧
      ∀ w ∈ Metric.ball w₀ r₀, g₀ w ∈ UpperHalfPlaneSet ∧ modularLambda (g₀ w) = w := by
  have hw₀_mem : w₀ ∈ modularLambda '' UpperHalfPlaneSet := by
    rw [modularLambda_image_upperHalfPlaneSet h_exU]
    exact ⟨Set.mem_univ w₀, fun h ↦ by rcases h with rfl | rfl; exacts [hw0 rfl, hw1 rfl]⟩
  obtain ⟨z₀, hz₀_up, hz₀_eq⟩ := hw₀_mem
  obtain ⟨U, V, g₀, _, _, hU_sub, hV_open, hfz₀_V, _, hg₀_holo, _, _, hg₀_right, _⟩ :=
    RudinRCA.Chapter10.theorem10_30 isOpen_upperHalfPlaneSet (modularLambda_holomorphicOn h_exU)
      hz₀_up (modularLambda_holo_and_deriv_ne_zero h_exU hz₀_up).2
  rw [hz₀_eq] at hfz₀_V
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ := Metric.isOpen_iff.mp hV_open w₀ hfz₀_V
  have hg₀_diff : DifferentiableOn ℂ g₀ (Metric.ball w₀ r₀) :=
    fun w hw ↦ (hg₀_holo w (hr₀_sub hw)).differentiableWithinAt
  refine ⟨r₀, g₀, hr₀_pos, hg₀_diff, fun w hw ↦ ?_⟩
  obtain ⟨hw_U, hlam_w⟩ := hg₀_right w (hr₀_sub hw)
  exact ⟨hU_sub hw_U, hlam_w⟩

/-- Around any point `c ∈ ℂ`, an entire function `f₁` omitting `0` and `1` admits a radius `δ > 0`
such that on `Metric.ball c δ`, for EVERY `p ∈ Metric.ball c δ` and EVERY `z_p ∈ Π⁺` with
`λ(z_p) = f₁(p)`, there is a holomorphic lift `g : Metric.ball c δ → Π⁺` with `λ ∘ g = f₁` and
`g(p) = z_p` (achieved by composing a base local lift with a `Γ`-deck transformation). -/
private theorem exists_lift_ball_at_point
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    {f₁ : ℂ → ℂ} (hf₁ : Differentiable ℂ f₁)
    (homit : ∀ z : ℂ, f₁ z ≠ 0 ∧ f₁ z ≠ 1) (c : ℂ) :
    ∃ δ > 0, ∀ p ∈ Metric.ball c δ, ∀ z_p ∈ UpperHalfPlaneSet,
      modularLambda z_p = f₁ p →
        ∃ g : ℂ → ℂ,
          DifferentiableOn ℂ g (Metric.ball c δ) ∧
          (∀ z ∈ Metric.ball c δ, g z ∈ UpperHalfPlaneSet ∧ modularLambda (g z) = f₁ z) ∧
          g p = z_p := by
  obtain ⟨r₀, g₀, hr₀_pos, hg₀_diff, hg₀_prop⟩ :=
    exists_local_right_inverse_modularLambda h_exU (homit c).1 (homit c).2
  obtain ⟨δ, hδ_pos, hδ_maps⟩ :=
    Metric.continuousAt_iff.mp hf₁.continuous.continuousAt r₀ hr₀_pos
  refine ⟨δ, hδ_pos, fun p hp z_p hz_p hzp_lam ↦ ?_⟩
  let ψ₀ : ℂ → ℂ := fun z ↦ g₀ (f₁ z)
  have hmaps_f₁ : Set.MapsTo f₁ (Metric.ball c δ) (Metric.ball (f₁ c) r₀) :=
    fun z hz ↦ hδ_maps hz
  have hψ₀_diff : DifferentiableOn ℂ ψ₀ (Metric.ball c δ) :=
    hg₀_diff.comp hf₁.differentiableOn hmaps_f₁
  have hψ₀_up : ∀ z ∈ Metric.ball c δ, ψ₀ z ∈ UpperHalfPlaneSet :=
    fun z hz ↦ (hg₀_prop (f₁ z) (hmaps_f₁ hz)).1
  have hψ₀_lam : ∀ z ∈ Metric.ball c δ, modularLambda (ψ₀ z) = f₁ z :=
    fun z hz ↦ (hg₀_prop (f₁ z) (hmaps_f₁ hz)).2
  have hlam_eq : modularLambda z_p = modularLambda (ψ₀ p) :=
    hzp_lam.trans (hψ₀_lam p hp).symm
  obtain ⟨γ, hγ_eq⟩ :=
    (modularLambda_eq_iff_gamma_orbit h_exU hz_p (hψ₀_up p hp)).mp hlam_eq
  obtain ⟨a, b, c', d, hdet, hγ_perm⟩ := γ.1.2
  let g : ℂ → ℂ := fun z ↦ intMoebius a b c' d (ψ₀ z)
  have hg_diff : DifferentiableOn ℂ g (Metric.ball c δ) :=
    (intMoebius_differentiableOn hdet).comp hψ₀_diff hψ₀_up
  have hg_apply_perm : ∀ (z : ℂ) (hz : z ∈ Metric.ball c δ),
      g z = (γ.1.1 ⟨ψ₀ z, hψ₀_up z hz⟩).1 := by
    intro z hz
    change intMoebius a b c' d (ψ₀ z) = (γ.1.1 ⟨ψ₀ z, hψ₀_up z hz⟩).1
    rw [hγ_perm, intMoebiusPerm_apply]
  refine ⟨g, hg_diff, ?_, ?_⟩
  · intro z hz
    rw [hg_apply_perm z hz]
    exact ⟨(γ.1.1 ⟨ψ₀ z, hψ₀_up z hz⟩).2,
      (modularLambda_gamma_invariant h_exU γ ⟨ψ₀ z, hψ₀_up z hz⟩).trans (hψ₀_lam z hz)⟩
  · rw [hg_apply_perm p hp]
    exact hγ_eq

/-- Compactness of `γ '' [0, 1]` yields a uniform lift radius `ρ > 0` along any continuous curve
`γ : [0, 1] → ℂ`. -/
private theorem exists_uniform_lift_radius_along_curve
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    {f₁ : ℂ → ℂ} (hf₁ : Differentiable ℂ f₁)
    (homit : ∀ z : ℂ, f₁ z ≠ 0 ∧ f₁ z ≠ 1)
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Set.Icc 0 1)) :
    ∃ ρ > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ Metric.ball (γ t) ρ,
      ∀ z_p ∈ UpperHalfPlaneSet, modularLambda z_p = f₁ p →
        ∃ g : ℂ → ℂ,
          DifferentiableOn ℂ g (Metric.ball (γ t) ρ) ∧
          (∀ z ∈ Metric.ball (γ t) ρ, g z ∈ UpperHalfPlaneSet ∧ modularLambda (g z) = f₁ z) ∧
          g p = z_p := by
  let K : Set ℂ := γ '' Set.Icc 0 1
  have hK_comp : IsCompact K := isCompact_Icc.image_of_continuousOn hγ
  have hpt : ∀ x : K, ∃ δ > 0, ∀ p ∈ Metric.ball x.1 δ, ∀ z_p ∈ UpperHalfPlaneSet,
      modularLambda z_p = f₁ p →
        ∃ g : ℂ → ℂ,
          DifferentiableOn ℂ g (Metric.ball x.1 δ) ∧
          (∀ z ∈ Metric.ball x.1 δ, g z ∈ UpperHalfPlaneSet ∧ modularLambda (g z) = f₁ z) ∧
          g p = z_p :=
    fun x ↦ exists_lift_ball_at_point h_exU hf₁ homit x.1
  choose r_x hr_pos hr_lift using hpt
  obtain ⟨F, hF_cov⟩ := hK_comp.elim_finite_subcover
    (fun x : K ↦ Metric.ball x.1 (r_x x / 2))
    (fun _ ↦ isOpen_ball)
    (fun w hw ↦ Set.mem_iUnion.mpr ⟨⟨w, hw⟩, Metric.mem_ball_self (half_pos (hr_pos ⟨w, hw⟩))⟩)
  have h0_mem : γ 0 ∈ K := ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hF_ne : F.Nonempty := by
    obtain ⟨x, hxF, _⟩ := Set.mem_iUnion₂.mp (hF_cov h0_mem)
    exact ⟨x, hxF⟩
  let ρ : ℝ := F.inf' hF_ne (fun x ↦ r_x x / 2)
  have hρ_pos : 0 < ρ :=
    (Finset.lt_inf'_iff hF_ne).mpr (fun x _ ↦ half_pos (hr_pos x))
  refine ⟨ρ, hρ_pos, fun t ht p hp z_p hz_p hzp_lam ↦ ?_⟩
  obtain ⟨x, hxF, hγt_x⟩ := Set.mem_iUnion₂.mp (hF_cov ⟨t, ht, rfl⟩)
  have hρ_le : ρ ≤ r_x x / 2 := Finset.inf'_le (fun u ↦ r_x u / 2) hxF
  have hball_sub : Metric.ball (γ t) ρ ⊆ Metric.ball x.1 (r_x x) := by
    intro w hw
    rw [Metric.mem_ball] at hw hγt_x ⊢
    calc dist w x.1 ≤ dist w (γ t) + dist (γ t) x.1 := dist_triangle w (γ t) x.1
      _ < ρ + r_x x / 2 := add_lt_add hw hγt_x
      _ ≤ r_x x / 2 + r_x x / 2 := by linarith
      _ = r_x x := add_halves (r_x x)
  obtain ⟨g, hg_diff, hg_prop, hgp⟩ := hr_lift x p (hball_sub hp) z_p hz_p hzp_lam
  exact ⟨g, hg_diff.mono hball_sub, fun z hz ↦ hg_prop z (hball_sub hz), hgp⟩

/-- Any base lift `φ₀` of `f₁` (`λ ∘ φ₀.fn = f₁` into `Π⁺`) can be analytically continued along
EVERY continuous curve `γ : [0, 1] → ℂ` starting at `φ₀.center`, producing a terminal element `φ₁`
centered at `γ 1` whose value `φ₁.fn (γ 1)` lies in `Π⁺` and satisfies `λ(φ₁.fn (γ 1)) = f₁(γ 1)`. -/
private theorem exists_lift_continuation_along_curve
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    {f₁ : ℂ → ℂ} (hf₁ : Differentiable ℂ f₁)
    (homit : ∀ z : ℂ, f₁ z ≠ 0 ∧ f₁ z ≠ 1)
    {φ₀ : FunctionElement}
    (hφ₀_lift : ∀ z ∈ φ₀.disc, φ₀.fn z ∈ UpperHalfPlaneSet ∧ modularLambda (φ₀.fn z) = f₁ z)
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Set.Icc 0 1)) (hγ0 : γ 0 = φ₀.center) :
    ∃ φ₁ : FunctionElement,
      ContinuedAlongCurve φ₀ γ φ₁ ∧
      φ₁.center = γ 1 ∧
      φ₁.fn (γ 1) ∈ UpperHalfPlaneSet ∧
      modularLambda (φ₁.fn (γ 1)) = f₁ (γ 1) := by
  obtain ⟨ρ, hρ_pos, hρ_lift⟩ :=
    exists_uniform_lift_radius_along_curve h_exU hf₁ homit hγ
  let ρ₁ : ℝ := min φ₀.radius ρ
  have hρ₁_pos : 0 < ρ₁ := lt_min φ₀.radius_pos hρ_pos
  have hρ₁_le_ρ : ρ₁ ≤ ρ := min_le_right _ _
  have hρ₁_lift : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ Metric.ball (γ t) ρ₁,
      ∀ z_p ∈ UpperHalfPlaneSet, modularLambda z_p = f₁ p →
        ∃ g : ℂ → ℂ,
          DifferentiableOn ℂ g (Metric.ball (γ t) ρ₁) ∧
          (∀ z ∈ Metric.ball (γ t) ρ₁, g z ∈ UpperHalfPlaneSet ∧ modularLambda (g z) = f₁ z) ∧
          g p = z_p := by
    intro t ht p hp z_p hz_p hzp_lam
    have hsub : Metric.ball (γ t) ρ₁ ⊆ Metric.ball (γ t) ρ := Metric.ball_subset_ball hρ₁_le_ρ
    obtain ⟨g, hg_diff, hg_prop, hgp⟩ := hρ_lift t ht p (hsub hp) z_p hz_p hzp_lam
    exact ⟨g, hg_diff.mono hsub, fun z hz ↦ hg_prop z (hsub hz), hgp⟩
  have hunif : UniformContinuousOn γ (Set.Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hγ
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hunif ρ₁ hρ₁_pos
  obtain ⟨K_nat, hK_nat⟩ := exists_nat_gt (1 / δ)
  let M : ℕ := K_nat + 1
  have hM_pos : 0 < (M : ℝ) := by exact_mod_cast Nat.succ_pos K_nat
  have hinv_M_lt : (1 : ℝ) / (M : ℝ) < δ := by
    have hgt : 1 / δ < (M : ℝ) := by
      calc 1 / δ < (K_nat : ℝ) := hK_nat
        _ ≤ (K_nat : ℝ) + 1 := by linarith
        _ = (M : ℝ) := by push_cast [M]; ring
    rw [div_lt_iff₀ hM_pos]
    have h1 := (div_lt_iff₀ hδ_pos).mp hgt
    linarith
  let tau : ℕ → ℝ := fun k ↦ min ((k : ℝ) / (M : ℝ)) 1
  have htau_mem : ∀ k : ℕ, tau k ∈ Set.Icc (0 : ℝ) 1 := fun k ↦
    ⟨le_min (div_nonneg (Nat.cast_nonneg k) hM_pos.le) zero_le_one, min_le_right _ _⟩
  have htau_0 : tau 0 = 0 := by
    dsimp [tau]
    rw [Nat.cast_zero, zero_div, min_eq_left zero_le_one]
  have htau_M : tau M = 1 := by
    dsimp [tau]
    rw [div_self hM_pos.ne', min_self]
  have htau_mono : Monotone tau := by
    intro k₁ k₂ hk
    apply min_le_min_right
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hk) hM_pos.le
  have htau_step : ∀ k : ℕ, tau (k + 1) - tau k ≤ 1 / (M : ℝ) := by
    intro k
    dsimp [tau]
    have h1 : min (((k + 1 : ℕ) : ℝ) / (M : ℝ)) 1 ≤ ((k : ℝ) / (M : ℝ)) + 1 / (M : ℝ) := by
      refine (min_le_left _ _).trans ?_
      push_cast
      ring_nf
      exact le_rfl
    rcases le_total ((k : ℝ) / (M : ℝ)) 1 with hle1 | hge1
    · rw [min_eq_left hle1]
      linarith
    · rw [min_eq_right hge1]
      have hle_one : min (((k + 1 : ℕ) : ℝ) / (M : ℝ)) 1 ≤ 1 := min_le_right _ _
      have hpos_inv : 0 ≤ 1 / (M : ℝ) := by positivity
      linarith
  let ElemInv (k : ℕ) :=
    { φ : FunctionElement //
      φ.center = γ (tau k) ∧
      (∀ z ∈ φ.disc, φ.fn z ∈ UpperHalfPlaneSet ∧ modularLambda (φ.fn z) = f₁ z) ∧
      (0 < k → φ.radius = ρ₁) }
  let seq : ∀ k : ℕ, ElemInv k :=
    Nat.rec
      ⟨φ₀, by rw [htau_0]; exact hγ0.symm, hφ₀_lift, fun h ↦ (lt_irrefl 0 h).elim⟩
      (fun k prev ↦
        let pk : ℂ := γ (tau k)
        let ck1 : ℂ := γ (tau (k + 1))
        have hpk_in : pk ∈ Metric.ball ck1 ρ₁ := by
          rw [Metric.mem_ball]
          apply hδ (tau k) (htau_mem k) (tau (k + 1)) (htau_mem (k + 1))
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (htau_mono (Nat.le_succ k))), neg_sub]
          exact (htau_step k).trans_lt hinv_M_lt
        have hpk_prev : pk ∈ prev.1.disc := by
          rw [FunctionElement.disc, prev.2.1]
          exact Metric.mem_ball_self prev.1.radius_pos
        have hprev_pk := prev.2.2.1 pk hpk_prev
        let g_ex := hρ₁_lift (tau (k + 1)) (htau_mem (k + 1)) pk hpk_in
          (prev.1.fn pk) hprev_pk.1 hprev_pk.2
        let g := Classical.choose g_ex
        have hg := Classical.choose_spec g_ex
        ⟨{ center := ck1
           radius := ρ₁
           radius_pos := hρ₁_pos
           fn := g
           holo := hg.1 },
         rfl, hg.2.1, fun _ ↦ rfl⟩)
  have hseq_dc : ∀ k : ℕ, DirectContinuation (seq k).1 (seq (k + 1)).1 := by
    intro k
    let pk : ℂ := γ (tau k)
    let ck1 : ℂ := γ (tau (k + 1))
    have hpk_in : pk ∈ Metric.ball ck1 ρ₁ := by
      rw [Metric.mem_ball]
      apply hδ (tau k) (htau_mem k) (tau (k + 1)) (htau_mem (k + 1))
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (htau_mono (Nat.le_succ k))), neg_sub]
      exact (htau_step k).trans_lt hinv_M_lt
    have hpk_prev : pk ∈ (seq k).1.disc := by
      rw [FunctionElement.disc, (seq k).2.1]
      exact Metric.mem_ball_self (seq k).1.radius_pos
    have hpk_next : pk ∈ (seq (k + 1)).1.disc := hpk_in
    have hprev_pk := (seq k).2.2.1 pk hpk_prev
    have hval_eq : (seq (k + 1)).1.fn pk = (seq k).1.fn pk :=
      (Classical.choose_spec
        (hρ₁_lift (tau (k + 1)) (htau_mem (k + 1)) pk hpk_in
          ((seq k).1.fn pk) hprev_pk.1 hprev_pk.2)).2.2
    refine ⟨⟨pk, hpk_prev, hpk_next⟩, ?_⟩
    exact eqOn_lifts_of_modularLambda h_exU
      ((seq k).1.isOpen_disc.inter (seq (k + 1)).1.isOpen_disc)
      ((seq k).1.convex_disc.inter (seq (k + 1)).1.convex_disc).isPreconnected
      ((seq k).1.holo.mono Set.inter_subset_left)
      ((seq (k + 1)).1.holo.mono Set.inter_subset_right)
      (fun z hz ↦ ((seq k).2.2.1 z hz.1).1)
      (fun z hz ↦ (((seq k).2.2.1 z hz.1).2).trans (((seq (k + 1)).2.2.1 z hz.2).2).symm)
      ⟨hpk_prev, hpk_next⟩
      hval_eq.symm
  let Φ : Fin (M + 1) → FunctionElement := fun i ↦ (seq i.val).1
  let s : Fin (M + 2) → ℝ := fun k ↦ if k.val = 0 then 0 else tau (k.val - 1)
  have hs0 : s 0 = 0 := rfl
  have hsn : s (Fin.last (M + 1)) = 1 := by
    dsimp [s]
    exact htau_M
  have hs_mono : Monotone s := by
    intro i₁ i₂ hi
    have hval : i₁.val ≤ i₂.val := hi
    dsimp [s]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact (htau_mem _).1
    · omega
    · exact htau_mono (by omega)
  have hcenter_end : (Φ (Fin.last M)).center = γ 1 :=
    (seq M).2.1.trans (congrArg γ htau_M)
  have hcont_curve : ContinuedAlongCurve φ₀ γ (Φ (Fin.last M)) := by
    refine ⟨M, Φ, rfl, rfl, fun k ↦ hseq_dc k.val, zero_le_one, hγ, hγ0.symm,
      hcenter_end, s, hs0, hsn, hs_mono, ?_⟩
    intro i
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · rintro _ ⟨t, ht, rfl⟩
      have hs_left : s (0 : Fin (M + 1)).castSucc = 0 := rfl
      have hs_right : s (0 : Fin (M + 1)).succ = 0 := by
        dsimp [s]
        simpa using htau_0
      have ht0 : t = 0 := by linarith [ht.1, ht.2, hs_left, hs_right]
      subst ht0
      change γ 0 ∈ φ₀.disc
      rw [hγ0]
      exact φ₀.center_mem_disc
    · rintro _ ⟨t, ht, rfl⟩
      have hs_left : s k.succ.castSucc = tau k.val := rfl
      have hs_right : s k.succ.succ = tau (k.val + 1) := rfl
      have ht01 : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨(htau_mem k.val).1.trans (hs_left ▸ ht.1),
         (hs_right ▸ ht.2).trans (htau_mem (k.val + 1)).2⟩
      have hdist_t : dist t (tau (k.val + 1)) < δ := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hs_right ▸ ht.2)), neg_sub]
        calc tau (k.val + 1) - t ≤ tau (k.val + 1) - tau k.val := by linarith [ht.1, hs_left]
          _ ≤ 1 / (M : ℝ) := htau_step k.val
          _ < δ := hinv_M_lt
      have hdist_γ : dist (γ t) (γ (tau (k.val + 1))) < ρ₁ :=
        hδ t ht01 (tau (k.val + 1)) (htau_mem (k.val + 1)) hdist_t
      dsimp [Φ]
      rw [FunctionElement.disc, (seq (k.val + 1)).2.1,
        (seq (k.val + 1)).2.2.2 (Nat.succ_pos k.val), Metric.mem_ball]
      exact hdist_γ
  have hγ1_in_end : γ 1 ∈ (Φ (Fin.last M)).disc := by
    rw [FunctionElement.disc, hcenter_end]
    exact Metric.mem_ball_self (Φ (Fin.last M)).radius_pos
  have hend_lift := (seq M).2.2.1 (γ 1) hγ1_in_end
  exact ⟨Φ (Fin.last M), hcont_curve, hcenter_end, hend_lift.1, hend_lift.2⟩

/-- **Theorem 16.22 — Little Picard's Theorem** (Rudin, *Real and Complex Analysis*, 3rd ed.,
p. 332):
If `f` is an entire function that omits two distinct complex values `α` and `β`, then `f` is
constant. -/
theorem theorem16_22_of_deps
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    (h_monodromy : ∀ {Ω : Set ℂ}, RudinRCA.Chapter10.BookSimplyConnected Ω →
      ∀ {φ₀ : FunctionElement}, CanContinueInRegion Ω φ₀ →
        ∃ f : ℂ → ℂ,
          DifferentiableOn ℂ f Ω ∧
          RudinRCA.Chapter10.HolomorphicOn f Ω ∧
          Set.EqOn f φ₀.fn φ₀.disc ∧
          (∀ (γ : ℝ → ℂ) (φ₁ : FunctionElement),
            ContinuousOn γ (Set.Icc 0 1) → γ 0 = φ₀.center → γ '' Set.Icc 0 1 ⊆ Ω →
            ContinuedAlongCurve φ₀ γ φ₁ →
            f =ᶠ[𝓝 (γ 1)] φ₁.fn ∧ f (γ 1) = φ₁.fn (γ 1)) ∧
          (∀ g : ℂ → ℂ, DifferentiableOn ℂ g Ω → Set.EqOn g φ₀.fn φ₀.disc → Set.EqOn g f Ω))
    {f : ℂ → ℂ} {α β : ℂ}
    (hf : Differentiable ℂ f) (hne : α ≠ β)
    (homit : ∀ z : ℂ, f z ≠ α ∧ f z ≠ β) :
    ∃ c : ℂ, ∀ z : ℂ, f z = c := by
  -- Step 1: Normalize `f₁(z) = (f(z) - α) / (β - α)` so that `f₁` is entire and omits `0` and `1`
  have hβα : β - α ≠ 0 := sub_ne_zero.mpr hne.symm
  let f₁ : ℂ → ℂ := fun z ↦ (f z - α) / (β - α)
  have hf₁ : Differentiable ℂ f₁ := (hf.sub (differentiable_const α)).div_const (β - α)
  have homit₁ : ∀ z : ℂ, f₁ z ≠ 0 ∧ f₁ z ≠ 1 := by
    intro z
    refine ⟨?_, ?_⟩
    · intro h0
      rcases div_eq_zero_iff.mp h0 with hnum | hden
      · exact (homit z).1 (sub_eq_zero.mp hnum)
      · exact hβα hden
    · intro h1
      have heq : f z - α = β - α := (div_eq_one_iff_eq hβα).mp h1
      exact (homit z).2 (by linear_combination heq)
  -- Step 2: Construct an initial local lift `φ₀` of `f₁` through `modularLambda` centered at `0`
  obtain ⟨δ₀, hδ₀_pos, hlift₀⟩ := exists_lift_ball_at_point h_exU hf₁ homit₁ 0
  have hf₁0_mem : f₁ 0 ∈ modularLambda '' UpperHalfPlaneSet := by
    rw [modularLambda_image_upperHalfPlaneSet h_exU]
    exact ⟨Set.mem_univ _, fun h ↦ by
      rcases h with h0 | h1
      · exact (homit₁ 0).1 h0
      · exact (homit₁ 0).2 h1⟩
  obtain ⟨z_base, hz_base_up, hz_base_lam⟩ := hf₁0_mem
  obtain ⟨g_base, hg_base_diff, hg_base_prop, _⟩ :=
    hlift₀ 0 (Metric.mem_ball_self hδ₀_pos) z_base hz_base_up hz_base_lam
  let φ₀ : FunctionElement :=
    { center := 0
      radius := δ₀
      radius_pos := hδ₀_pos
      fn := g_base
      holo := hg_base_diff }
  have hφ₀_lift : ∀ z ∈ φ₀.disc, φ₀.fn z ∈ UpperHalfPlaneSet ∧ modularLambda (φ₀.fn z) = f₁ z :=
    hg_base_prop
  -- Step 3: `φ₀` continues along every curve in the simply connected plane `ℂ = Set.univ`
  have hcan : CanContinueInRegion Set.univ φ₀ :=
    ⟨Set.subset_univ _, fun γ hγ hγ0 _ ↦
      let ⟨φ₁, hcont, _, _, _⟩ :=
        exists_lift_continuation_along_curve h_exU hf₁ homit₁ hφ₀_lift hγ hγ0
      ⟨φ₁, hcont⟩⟩
  have hsc_univ : RudinRCA.Chapter10.BookSimplyConnected Set.univ :=
    RudinRCA.Chapter10.theorem10_38 ⟨isOpen_univ, isConnected_univ⟩ convex_univ
  obtain ⟨h, hh_diff_on, hh_holo, _, hh_endpt, _⟩ := h_monodromy hsc_univ hcan
  -- Step 4: By evaluating along radial segments `t ↦ t * z`, `h(z) ∈ Π⁺` and `λ(h(z)) = f₁(z)`
  have hh_lift : ∀ z : ℂ, h z ∈ UpperHalfPlaneSet ∧ modularLambda (h z) = f₁ z := by
    intro z
    let γ_z : ℝ → ℂ := fun t ↦ (t : ℂ) * z
    have hγ_cont : ContinuousOn γ_z (Set.Icc 0 1) :=
      (Complex.continuous_ofReal.mul continuous_const).continuousOn
    have hγ0 : γ_z 0 = φ₀.center := by simp [γ_z, φ₀]
    have hγ1 : γ_z 1 = z := by simp [γ_z]
    obtain ⟨φ₁, hcont₁, _, hφ₁_up, hφ₁_lam⟩ :=
      exists_lift_continuation_along_curve h_exU hf₁ homit₁ hφ₀_lift hγ_cont hγ0
    have hval_eq : h (γ_z 1) = φ₁.fn (γ_z 1) :=
      (hh_endpt γ_z φ₁ hγ_cont hγ0 (Set.subset_univ _) hcont₁).2
    rw [hγ1] at hval_eq hφ₁_up hφ₁_lam
    rw [hval_eq]
    exact ⟨hφ₁_up, hφ₁_lam⟩
  -- Step 5: `E(z) = exp(i * h(z))` is entire with `‖E(z)‖ = exp(-Im h(z)) < 1`, hence constant
  have hh_diff : Differentiable ℂ h := fun z ↦ hh_holo z (Set.mem_univ z)
  let E : ℂ → ℂ := fun z ↦ Complex.exp (Complex.I * h z)
  have hE_diff : Differentiable ℂ E :=
    Complex.differentiable_exp.comp (hh_diff.const_mul Complex.I)
  have hE_range : Set.range E ⊆ Metric.closedBall (0 : ℂ) 1 := by
    rintro _ ⟨z, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp [E]
    rw [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
    have him_pos : 0 < (h z).im := (hh_lift z).1
    exact Real.exp_le_one_iff.mpr (by linarith)
  obtain ⟨c_E, hc_E⟩ := RudinRCA.Chapter10.liouville (fun z _ ↦ hE_diff z)
    (Metric.isBounded_closedBall.subset hE_range)
  -- Step 6: Differentiating `exp(i * h(z)) = c_E` yields `h'(z) = 0`, so `h` and `f` are constant
  have hderiv_h_zero : ∀ z : ℂ, deriv h z = 0 := by
    intro z
    have hd1 : HasDerivAt E (Complex.exp (Complex.I * h z) * (Complex.I * deriv h z)) z :=
      ((hh_diff z).hasDerivAt.const_mul Complex.I).cexp
    have hd2 : HasDerivAt E 0 z := by
      have hE_eq : E = fun _ ↦ c_E := funext hc_E
      rw [hE_eq]
      exact hasDerivAt_const z c_E
    have hprod : Complex.exp (Complex.I * h z) * (Complex.I * deriv h z) = 0 :=
      hd1.unique hd2
    have himul : Complex.I * deriv h z = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (Complex.exp_ne_zero _)
    exact (mul_eq_zero.mp himul).resolve_left Complex.I_ne_zero
  have hh_const : ∀ z : ℂ, h z = h 0 := fun z ↦
    isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ hh_diff_on
      (fun w _ ↦ hderiv_h_zero w) (Set.mem_univ z) (Set.mem_univ 0)
  refine ⟨f 0, fun z ↦ ?_⟩
  have hf₁_eq : f₁ z = f₁ 0 := by
    rw [← (hh_lift z).2, hh_const z, (hh_lift 0).2]
  have hf_rec : ∀ w : ℂ, f w = f₁ w * (β - α) + α := by
    intro w
    dsimp [f₁]
    rw [div_mul_cancel₀ _ hβα, sub_add_cancel]
  rw [hf_rec z, hf₁_eq, ← hf_rec 0]

/-- Unconditional discharge of `LittlePicardStatement` (`16.21` announced claim) by `16.22`. -/
theorem littlePicardStatement_of_deps
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    (h_monodromy : ∀ {Ω : Set ℂ}, RudinRCA.Chapter10.BookSimplyConnected Ω →
      ∀ {φ₀ : FunctionElement}, CanContinueInRegion Ω φ₀ →
        ∃ f : ℂ → ℂ,
          DifferentiableOn ℂ f Ω ∧
          RudinRCA.Chapter10.HolomorphicOn f Ω ∧
          Set.EqOn f φ₀.fn φ₀.disc ∧
          (∀ (γ : ℝ → ℂ) (φ₁ : FunctionElement),
            ContinuousOn γ (Set.Icc 0 1) → γ 0 = φ₀.center → γ '' Set.Icc 0 1 ⊆ Ω →
            ContinuedAlongCurve φ₀ γ φ₁ →
            f =ᶠ[𝓝 (γ 1)] φ₁.fn ∧ f (γ 1) = φ₁.fn (γ 1)) ∧
          (∀ g : ℂ → ℂ, DifferentiableOn ℂ g Ω → Set.EqOn g φ₀.fn φ₀.disc → Set.EqOn g f Ω)) :
    LittlePicardStatement :=
  fun _ _ _ hf hne homit ↦ theorem16_22_of_deps h_exU h_monodromy hf hne homit

/-- **Unconditional `16.21` Corollary 1 (Rudin p. 331):**
Every nonconstant entire function assumes every complex value with at most one exception. -/
theorem theorem16_21_nonconstant_entire_omits_at_most_one_of_deps
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    (h_monodromy : ∀ {Ω : Set ℂ}, RudinRCA.Chapter10.BookSimplyConnected Ω →
      ∀ {φ₀ : FunctionElement}, CanContinueInRegion Ω φ₀ →
        ∃ f : ℂ → ℂ,
          DifferentiableOn ℂ f Ω ∧
          RudinRCA.Chapter10.HolomorphicOn f Ω ∧
          Set.EqOn f φ₀.fn φ₀.disc ∧
          (∀ (γ : ℝ → ℂ) (φ₁ : FunctionElement),
            ContinuousOn γ (Set.Icc 0 1) → γ 0 = φ₀.center → γ '' Set.Icc 0 1 ⊆ Ω →
            ContinuedAlongCurve φ₀ γ φ₁ →
            f =ᶠ[𝓝 (γ 1)] φ₁.fn ∧ f (γ 1) = φ₁.fn (γ 1)) ∧
          (∀ g : ℂ → ℂ, DifferentiableOn ℂ g Ω → Set.EqOn g φ₀.fn φ₀.disc → Set.EqOn g f Ω))
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnc : ¬ ∃ c : ℂ, ∀ z : ℂ, f z = c) :
    ∃ w₀ : ℂ, ∀ w : ℂ, w ≠ w₀ → ∃ z : ℂ, f z = w := by
  by_contra hnot
  push Not at hnot
  obtain ⟨α, _, hα_omit⟩ := hnot 0
  obtain ⟨β, hβα, hβ_omit⟩ := hnot α
  exact hnc (theorem16_22_of_deps h_exU h_monodromy hf hβα.symm
    (fun z ↦ ⟨hα_omit z, hβ_omit z⟩))

/-- **Unconditional `16.21` Corollary 2:**
If a nonconstant entire function `f` omits a complex value `w₀`, then Little Picard alone (`16.22`,
applied to a holomorphic logarithm of `f - w₀`) implies that `f` assumes EVERY complex value
`w ≠ w₀` infinitely often. -/
theorem theorem16_21_entire_omitting_one_infinite_fibers_of_deps
    (h_exU : ∀ {z : ℂ}, z ∈ UpperHalfPlaneSet →
      ∃! p : GammaSubgroup × {q : ℂ // q ∈ FundamentalSetQ},
        (p.1.1.1 ⟨p.2.1, fundamentalSetQ_subset_upperHalfPlaneSet p.2.2⟩).1 = z)
    (h_monodromy : ∀ {Ω : Set ℂ}, RudinRCA.Chapter10.BookSimplyConnected Ω →
      ∀ {φ₀ : FunctionElement}, CanContinueInRegion Ω φ₀ →
        ∃ f : ℂ → ℂ,
          DifferentiableOn ℂ f Ω ∧
          RudinRCA.Chapter10.HolomorphicOn f Ω ∧
          Set.EqOn f φ₀.fn φ₀.disc ∧
          (∀ (γ : ℝ → ℂ) (φ₁ : FunctionElement),
            ContinuousOn γ (Set.Icc 0 1) → γ 0 = φ₀.center → γ '' Set.Icc 0 1 ⊆ Ω →
            ContinuedAlongCurve φ₀ γ φ₁ →
            f =ᶠ[𝓝 (γ 1)] φ₁.fn ∧ f (γ 1) = φ₁.fn (γ 1)) ∧
          (∀ g : ℂ → ℂ, DifferentiableOn ℂ g Ω → Set.EqOn g φ₀.fn φ₀.disc → Set.EqOn g f Ω))
    {f : ℂ → ℂ} {w₀ : ℂ} (hf : Differentiable ℂ f)
    (hnc : ¬ ∃ c : ℂ, ∀ z : ℂ, f z = c)
    (homit : ∀ z : ℂ, f z ≠ w₀) :
    ∀ w : ℂ, w ≠ w₀ → ({z : ℂ | f z = w}).Infinite := by
  have hreg_univ : RudinRCA.Chapter10.IsRegion Set.univ := ⟨isOpen_univ, isConnected_univ⟩
  have hsc_univ : RudinRCA.Chapter10.BookSimplyConnected Set.univ :=
    RudinRCA.Chapter10.theorem10_38 hreg_univ convex_univ
  have hlog_ex :
      (RudinRCA.Chapter10.BookSimplyConnected Set.univ) →
        (∀ F : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn F Set.univ →
          (∀ z ∈ (Set.univ : Set ℂ), F z ≠ 0) →
          ∃ g : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn g Set.univ ∧
            ∀ z ∈ (Set.univ : Set ℂ), Complex.exp (g z) = F z) :=
    ((RudinRCA.Chapter13.theorem13_11 hreg_univ).1.out 2 8).mp
  obtain ⟨g, hg_holo, hg_exp⟩ := hlog_ex hsc_univ (fun z ↦ f z - w₀)
    (fun z _ ↦ (hf z).sub (differentiableAt_const w₀))
    (fun z _ ↦ sub_ne_zero.mpr (homit z))
  have hg_diff : Differentiable ℂ g := fun z ↦ hg_holo z (Set.mem_univ z)
  have hg_nc : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c := by
    rintro ⟨c, hc⟩
    refine hnc ⟨w₀ + Complex.exp c, fun z ↦ ?_⟩
    have hexp_z := hg_exp z (Set.mem_univ z)
    rw [hc z] at hexp_z
    linear_combination -hexp_z
  obtain ⟨v₀, hv₀⟩ :=
    theorem16_21_nonconstant_entire_omits_at_most_one_of_deps h_exU h_monodromy hg_diff hg_nc
  intro w hw
  let ζ : ℂ := Complex.log (w - w₀)
  have hexp_ζ : Complex.exp ζ = w - w₀ := Complex.exp_log (sub_ne_zero.mpr hw)
  let val : ℤ → ℂ := fun k ↦ ζ + (k : ℂ) * (2 * Real.pi * Complex.I)
  have htwo_pi_I_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hval_inj : Function.Injective val := by
    intro k₁ k₂ heq
    have hmul_eq : (k₁ : ℂ) * (2 * Real.pi * Complex.I) =
        (k₂ : ℂ) * (2 * Real.pi * Complex.I) := add_left_cancel heq
    exact Int.cast_injective (mul_right_cancel₀ htwo_pi_I_ne hmul_eq)
  let Idx : Set ℤ := {k : ℤ | val k ≠ v₀}
  have hcompl_sub : ({k : ℤ | val k = v₀}).Subsingleton := by
    intro k₁ hk₁ k₂ hk₂
    exact hval_inj (hk₁.trans hk₂.symm)
  have hIdx_inf : Idx.Infinite := by
    have heq_set : (Set.univ : Set ℤ) \ {k : ℤ | val k = v₀} = Idx := by
      ext k
      simp [Idx]
    rw [← heq_set]
    exact Set.Infinite.sdiff Set.infinite_univ hcompl_sub.finite
  have : Infinite Idx := hIdx_inf.to_subtype
  have hex_z : ∀ k : Idx, ∃ z : ℂ, g z = val k.1 := fun k ↦ hv₀ (val k.1) k.2
  choose z_fn hz_fn using hex_z
  have hz_inj : Function.Injective z_fn := by
    intro k₁ k₂ hzk
    apply Subtype.ext
    apply hval_inj
    rw [← hz_fn k₁, ← hz_fn k₂, hzk]
  refine (Set.infinite_range_of_injective hz_inj).mono ?_
  rintro _ ⟨k, rfl⟩
  change f (z_fn k) = w
  have hexp_zk : Complex.exp (g (z_fn k)) = w - w₀ := by
    rw [hz_fn k]
    dsimp [val]
    rw [Complex.exp_add, hexp_ζ, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hsub_zk := (hg_exp (z_fn k) (Set.mem_univ _)).symm.trans hexp_zk
  linear_combination hsub_zk

end PicardExpositionAndProof

/-!
## Axiom Audit
-/

#print axioms OpenTriangleQ0
#print axioms bookSimplyConnected_openTriangleQ0
#print axioms z0Center
#print axioms omegaCube
#print axioms moebiusM3
#print axioms moebiusM3_bijOn_openTriangleQ0
#print axioms riemannPsi
#print axioms riemannPsi_bij
#print axioms riemannPsi_moebiusM3
#print axioms psiExtL1
#print axioms psiExtL1_holo_off_neg_conj_z0
#print axioms psiStrip
#print axioms psiStrip_holo
#print axioms cuspFnF
#print axioms cuspAlphaInf
#print axioms injOn_psiExtL1_boundaryL1
#print axioms psiExtL1_boundaryL1_notMem_cusps
#print axioms moebiusPhi
#print axioms moebiusPhiInv
#print axioms lambdaRight
#print axioms lambdaRight_holo
#print axioms lambdaRight_bijOn_omegaL1
#print axioms deriv_lambdaRight_ne_zero
#print axioms lambdaOnQ
#print axioms lambdaOnQ_bijOn_fundamentalSetQ
#print axioms modularLambda
#print axioms modularLambda_gamma_invariant
#print axioms modularLambda_eq_iff_gamma_orbit
#print axioms modularLambda_holo_and_deriv_ne_zero
#print axioms modularLambda_holomorphicOn
#print axioms modularLambda_isModularFunctionFor_gamma
#print axioms modularLambda_bijOn_fundamentalSetQ
#print axioms modularLambda_image_upperHalfPlaneSet
#print axioms modularLambda_image_ball_inter_upperHalfPlaneSet
#print axioms modularLambda_not_continuousAt_extension_frontier
#print axioms modularLambda_natural_boundary
#print axioms theorem16_20_of_deps
#print axioms LittlePicardStatement
#print axioms BigPicardStatement
#print axioms bigPicardStatement_iff_no_two_omitted
#print axioms theorem16_21_bigPicard_infinite_preimages
#print axioms entire_nonpolynomial_hasEssentialSingularity_inv
#print axioms theorem16_21_bigPicard_nonpolynomial_entire
#print axioms theorem16_21_bigPicard_implies_littlePicard
#print axioms theorem16_22_of_deps
#print axioms littlePicardStatement_of_deps
#print axioms theorem16_21_nonconstant_entire_omits_at_most_one_of_deps
#print axioms theorem16_21_entire_omitting_one_infinite_fibers_of_deps


/-- **Theorem 16.20 (Unconditional Elliptic Modular Function `λ`, RCA pp. 330–331):**
`modularLambda` (`λ`) on the upper half-plane `Π⁺` satisfies:
1. `λ ∈ H(Π⁺)` with `deriv modularLambda z ≠ 0` for every `z ∈ Π⁺`;
2. `λ` is `Γ`-invariant (`IsModularFunctionFor GammaSubgroup modularLambda`), with
   `λ(z₁) = λ(z₂) ↔ z₁ ∈ Γ · z₂` on `Π⁺`;
3. `λ` maps the fundamental set `Q` bijectively onto `ℂ \ {0, 1}` (injective on `Q`,
   range `λ(Π⁺) = ℂ \ {0, 1}`);
4. `ℝ = ∂Π⁺` is a natural boundary of `λ`: on the `Π⁺`-part of every open disc centered on `ℝ`,
   `λ` assumes every value in `ℂ \ {0, 1}`, and `λ` admits no holomorphic extension to any
   region `Ω` properly containing `Π⁺`. -/
theorem theorem16_20 :
    RudinRCA.Chapter10.HolomorphicOn modularLambda UpperHalfPlaneSet ∧
      (∀ z ∈ UpperHalfPlaneSet, deriv modularLambda z ≠ 0) ∧
      IsModularFunctionFor GammaSubgroup modularLambda ∧
      Set.BijOn modularLambda FundamentalSetQ (Set.univ \ {0, 1}) ∧
      modularLambda '' UpperHalfPlaneSet = Set.univ \ {0, 1} ∧
      (∀ z₁ ∈ UpperHalfPlaneSet, ∀ (z₂ : ℂ) (hz₂ : z₂ ∈ UpperHalfPlaneSet),
        modularLambda z₁ = modularLambda z₂ ↔
          ∃ γ : GammaSubgroup, (γ.1.1 ⟨z₂, hz₂⟩).1 = z₁) ∧
      (∀ p ∈ frontier UpperHalfPlaneSet, ∀ r > 0,
        modularLambda '' (Metric.ball p r ∩ UpperHalfPlaneSet) = Set.univ \ {0, 1}) ∧
      (∀ Ω : Set ℂ, RudinRCA.Chapter10.IsRegion Ω → UpperHalfPlaneSet ⊂ Ω →
        ¬ ∃ g : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn g Ω ∧
            Set.EqOn g modularLambda UpperHalfPlaneSet) :=
  theorem16_20_of_deps (@existsUnique_gamma_fundamentalSetQ) (@intMoebiusPerm_mem_gammaSubgroup_iff)

/-- **Theorem 16.22 (Little Picard's Theorem, RCA p. 332):**
Every entire function omitting two distinct complex values `α` and `β` is constant. -/
theorem theorem16_22 {f : ℂ → ℂ} {α β : ℂ}
    (hf : Differentiable ℂ f) (hne : α ≠ β)
    (homit : ∀ z : ℂ, f z ≠ α ∧ f z ≠ β) :
    ∃ c : ℂ, ∀ z : ℂ, f z = c :=
  theorem16_22_of_deps (@existsUnique_gamma_fundamentalSetQ) (@theorem16_15) hf hne homit

/-- Unconditional discharge of `LittlePicardStatement` (`16.21` announced claim) via `16.22`. -/
theorem littlePicardStatement : LittlePicardStatement :=
  littlePicardStatement_of_deps (@existsUnique_gamma_fundamentalSetQ) (@theorem16_15)

/-- **Unconditional `16.21` Corollary 1 (RCA p. 331):**
Every nonconstant entire function assumes every complex value with at most one exception. -/
theorem theorem16_21_nonconstant_entire_omits_at_most_one {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnc : ¬ ∃ c : ℂ, ∀ z : ℂ, f z = c) :
    ∃ w₀ : ℂ, ∀ w : ℂ, w ≠ w₀ → ∃ z : ℂ, f z = w :=
  theorem16_21_nonconstant_entire_omits_at_most_one_of_deps
    (@existsUnique_gamma_fundamentalSetQ) (@theorem16_15) hf hnc

/-- **Unconditional `16.21` Corollary 2:**
If a nonconstant entire function `f` omits `w₀`, then `f` assumes every `w ≠ w₀` infinitely often. -/
theorem theorem16_21_entire_omitting_one_infinite_fibers {f : ℂ → ℂ} {w₀ : ℂ}
    (hf : Differentiable ℂ f) (hnc : ¬ ∃ c : ℂ, ∀ z : ℂ, f z = c)
    (homit : ∀ z : ℂ, f z ≠ w₀) :
    ∀ w : ℂ, w ≠ w₀ → ({z : ℂ | f z = w}).Infinite :=
  theorem16_21_entire_omitting_one_infinite_fibers_of_deps
    (@existsUnique_gamma_fundamentalSetQ) (@theorem16_15) hf hnc homit

#print axioms theorem16_20
#print axioms theorem16_22
#print axioms littlePicardStatement
#print axioms theorem16_21_nonconstant_entire_omits_at_most_one
#print axioms theorem16_21_entire_omitting_one_infinite_fibers

end Chapter16PartD

end RudinRCA.Chapter16
