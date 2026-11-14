import RudinRCA.Chapter10
import RudinRCA.Chapter13
import RudinRCA.Chapter14
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.UrysohnsLemma

/-!
# Chapter 20: Uniform Approximation by Polynomials (`20.1`–`20.5`)

Formalization of Walter Rudin, *Real and Complex Analysis* (3rd ed., McGraw-Hill, 1987),
Chapter 20: *Uniform Approximation by Polynomials* (printed pp. 386–394, nodes `20.1`–`20.5`),
culminating in Mergelyan's Theorem (`theorem20_5`), following `SCOPING-H-19-20.md`.

## Coverage Summary & Statement-Hazard Disclosures
- **Node 20.1 (`PK`, `PKSubalgebra`, `isConnected_compl_iff_sphericalCompl`, `theorem20_1`):**
  Definition of `P(K)`, uniform `ε`-polynomial equivalence, closed subalgebra structure in `C(K, ℂ)`,
  equivalence of connectedness of `Kᶜ` and `S² \ K` for compact `K ⊆ ℂ`, necessary conditions
  (`ContinuousOn f K` and `DifferentiableOn ℂ f (interior K)`), insufficiency on `sphere 0 1`
  (`z ↦ z⁻¹ ∉ P(sphere 0 1)`), Weierstrass sufficiency on compact real intervals `[a, b]`, and the
  Runge implication from `Chapter13.theorem13_7`.
- **Node 20.2 (`node20_2_diagonal_counterexample`, `theorem20_2`, `theorem20_2_compl`):**
  Built from the in-book Riemann mapping theorem (`Chapter14.theorem14_9`), area/diameter inequality
  (`Chapter14.theorem14_15`), and spherical simple connectedness (`Chapter13.theorem13_11`).
  - *Hazard 20.2a (`SCOPING-H-19-20.md` §hazards-2):* `node20_2_diagonal_counterexample` proves that
    `ball z₀ r \ E` is always nonempty for compact `E ⊆ ball z₀ r` (`r > 0`) and that the literal
    strict second estimate fails on the diagonal `z = ζ ∈ ball z₀ r \ E` under totalized division.
    `theorem20_2` proves both the everywhere-valid polynomial-multiplied bound
    `‖(z - ζ) ^ 3 * Q ζ z - (z - ζ) ^ 2‖ < 1000 * r ^ 2` on `Eᶜ × ball z₀ r` and the off-diagonal
    bound `‖Q ζ z - (z - ζ)⁻¹‖ < 1000 * r ^ 2 / ‖z - ζ‖ ^ 3` for `z ≠ ζ`.
  - *Hazard 20.2b (`SCOPING-H-19-20.md` §hazards-3):* `theorem20_2` explicitly establishes both
    `Tendsto g (Bornology.cobounded ℂ) (𝓝 0)` and holomorphy of `w ↦ g(w⁻¹)` across `0` with value `0`.
- **Node 20.3 (`wirtingerBar`, `theorem20_3`):**
  Whole-plane Cauchy–Green (Pompeiu) representation formula for `C¹` compactly supported planar
  functions `f : ℂ → ℂ`, including Lebesgue integrability of `ζ ↦ wirtingerBar f ζ / (ζ - z)` and
  both complex-plane and `ℝ × ℝ` coordinate forms.
- **Node 20.4 (`theorem20_4`, `theorem20_4_continuousOn`):**
  *Hazard 20.4 (`SCOPING-H-19-20.md` §hazards-5):* Proved on arbitrary locally compact Hausdorff
  spaces `[TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]` **without** `NormalSpace X`,
  producing a compactly supported continuous extension preserving the supremum norm via the
  one-point compactification `OnePoint X` and a Urysohn cutoff.
- **Node 20.5 (`theorem20_5`, `theorem20_5_iff`, `theorem20_5_spherical`, `theorem20_5_empty_interior`):**
  Mergelyan's Theorem and its empty-interior corollary, handling the constant/zero-modulus case
  (`SCOPING-H-19-20.md` §hazards-7) uniformly without dividing by the modulus of continuity.
-/

set_option autoImplicit false

noncomputable section

namespace RudinRCA.Chapter20

section Node20_1
open Metric Set Filter Function Complex RudinRCA.Chapter13
open scoped Topology BigOperators OnePoint BoundedContinuousFunction

/-! ### Node 20.1: Uniform Approximation by Polynomials (`P(K)`) -/

/-- **Definition 20.1 (`P(K)`, RCA p. 386):**
For `K ⊆ ℂ`, `PK K` is the set of functions `f : ℂ → ℂ` that are uniform limits on `K` of sequences
of complex polynomials. -/
def PK (K : Set ℂ) : Set (ℂ → ℂ) :=
  {f : ℂ → ℂ | ∃ P : ℕ → Polynomial ℂ,
    TendstoUniformlyOn (fun n z => (P n).eval z) f Filter.atTop K}

/-- Uniform-approximation (`ε`-polynomial) characterization of membership in `PK K`. -/
theorem mem_PK_iff {K : Set ℂ} {f : ℂ → ℂ} :
    f ∈ PK K ↔ ∀ ε > 0, ∃ P : Polynomial ℂ, ∀ z ∈ K, ‖f z - P.eval z‖ < ε := by
  constructor
  · rintro ⟨P, hP⟩ ε hε
    have h_ev := (Metric.tendstoUniformlyOn_iff.mp hP) ε hε
    obtain ⟨n, hn⟩ := h_ev.exists
    refine ⟨P n, fun z hz => ?_⟩
    simpa [dist_eq_norm] using hn z hz
  · intro h
    have hex : ∀ n : ℕ, ∃ P : Polynomial ℂ, ∀ z ∈ K, ‖f z - P.eval z‖ < 1 / ((n : ℝ) + 1) :=
      fun n => h (1 / ((n : ℝ) + 1)) (by positivity)
    choose P hP using hex
    refine ⟨P, Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    filter_upwards [Filter.Ici_mem_atTop N] with n hn z hz
    rw [dist_eq_norm]
    refine (hP n z hz).trans ?_
    have hN1 : 1 / ε < (n : ℝ) + 1 := by
      have hle : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
      linarith
    exact (div_lt_iff₀ (by positivity)).mpr ((div_lt_iff₀ hε).mp hN1 |>.trans_eq (mul_comm _ _))

/-- `P(K)` viewed as a closed subalgebra of `C(K, ℂ)` when `K` is compact: the topological closure
of complex polynomial functions on `K`. -/
def PKSubalgebra (K : Set ℂ) [CompactSpace K] : Subalgebra ℂ C(K, ℂ) :=
  (polynomialFunctions K).topologicalClosure

theorem isClosed_PKSubalgebra (K : Set ℂ) [CompactSpace K] :
    IsClosed (PKSubalgebra K : Set C(K, ℂ)) :=
  Subalgebra.isClosed_topologicalClosure _

theorem mem_PKSubalgebra_iff {K : Set ℂ} [CompactSpace K] {f : ℂ → ℂ} (hf : ContinuousOn f K) :
    (⟨K.domRestrict f, continuousOn_iff_continuous_domRestrict.mp hf⟩ : C(K, ℂ)) ∈ PKSubalgebra K ↔
      f ∈ PK K := by
  let fK : C(K, ℂ) := ⟨K.domRestrict f, continuousOn_iff_continuous_domRestrict.mp hf⟩
  change fK ∈ PKSubalgebra K ↔ f ∈ PK K
  rw [PKSubalgebra, ← SetLike.mem_coe, Subalgebra.topologicalClosure_coe,
    Metric.mem_closure_iff, mem_PK_iff]
  constructor
  · intro h ε hε
    obtain ⟨g, hg_mem, hg_dist⟩ := h ε hε
    rw [polynomialFunctions_coe] at hg_mem
    obtain ⟨P, rfl⟩ := hg_mem
    refine ⟨P, fun z hz => ?_⟩
    have hle : ‖fK ⟨z, hz⟩ - (Polynomial.toContinuousMapOn P K) ⟨z, hz⟩‖ ≤
        ‖fK - Polynomial.toContinuousMapOn P K‖ :=
      (fK - Polynomial.toContinuousMapOn P K).norm_coe_le_norm ⟨z, hz⟩
    rw [dist_eq_norm] at hg_dist
    exact hle.trans_lt hg_dist
  · intro h ε hε
    obtain ⟨P, hP⟩ := h (ε / 2) (half_pos hε)
    refine ⟨Polynomial.toContinuousMapOn P K, ?_, ?_⟩
    · rw [polynomialFunctions_coe]
      exact ⟨P, rfl⟩
    · rw [dist_eq_norm]
      have hle : ‖fK - Polynomial.toContinuousMapOn P K‖ ≤ ε / 2 := by
        refine (ContinuousMap.norm_le _ (half_pos hε).le).mpr fun ⟨z, hz⟩ => ?_
        exact (hP z hz).le
      linarith

/-- **Topological Bridge (`Kᶜ` vs `S² \ K` for compact `K ⊆ ℂ`):**
For any compact subset `K ⊆ ℂ`, the planar complement `Kᶜ` is connected if and only if the
spherical complement `S² \ K = sphericalCompl K` in the Riemann sphere is connected. -/
theorem isConnected_compl_iff_sphericalCompl {K : Set ℂ} (hK : IsCompact K) :
    IsConnected Kᶜ ↔ IsConnected (sphericalCompl K) := by
  have h_eq : sphericalCompl K = insert (∞ : RiemannSphere) (((↑) : ℂ → RiemannSphere) '' Kᶜ) := by
    ext p
    induction p using OnePoint.rec with
    | infty => simp [sphericalCompl]
    | coe z => simp [OnePoint.coe_injective.mem_set_image]
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_ball (0 : ℂ)
  let R : ℝ := max R₀ 1
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right R₀ 1)
  have hK_ball : K ⊆ ball (0 : ℂ) R :=
    hR₀.trans (ball_subset_ball (le_max_left R₀ 1))
  let E : Set ℂ := {z : ℂ | R < ‖z‖}
  have hext_sub : E ⊆ Kᶜ := by
    intro z hz hzK
    have hlt : ‖z‖ < R := by simpa using hK_ball hzK
    exact (lt_irrefl R (lt_trans hz hlt)).elim
  constructor
  · intro hconn
    rw [h_eq]
    refine RudinRCA.Chapter13.isConnected_insert_infinity hconn fun r hr => ?_
    let w : ℂ := ((max R r + 1 : ℝ) : ℂ)
    have hw_pos : 0 < max R r + 1 := by positivity
    have hw_norm : ‖w‖ = max R r + 1 := by
      dsimp [w]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw_pos]
    refine ⟨w, hext_sub ?_, ?_⟩
    · change R < ‖w‖; rw [hw_norm]; linarith [le_max_left R r]
    · rw [hw_norm]; linarith [le_max_right R r]
  · intro hsph
    refine ⟨⟨((R + 1 : ℝ) : ℂ), hext_sub ?_⟩, ?_⟩
    · change R < ‖((R + 1 : ℝ) : ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    · intro u v hu hv hcov hu_ne hv_ne
      by_contra hdisj
      let A : Set ℂ := Kᶜ ∩ u
      let B : Set ℂ := Kᶜ ∩ v
      have hA_open : IsOpen A := hK.isClosed.isOpen_compl.inter hu
      have hB_open : IsOpen B := hK.isClosed.isOpen_compl.inter hv
      have hAB_disj : A ∩ B = ∅ := by
        ext z
        simp only [A, B, mem_inter_iff, mem_empty_iff_false, iff_false]
        intro ⟨⟨hzK, hzu⟩, ⟨_, hzv⟩⟩
        exact hdisj ⟨z, hzK, hzu, hzv⟩
      have hAB_union : A ∪ B = Kᶜ := by
        ext z
        simp only [A, B, mem_union, mem_inter_iff]
        exact ⟨fun h => h.elim And.left And.left,
          fun hzK => (hcov hzK).elim (fun hzu => Or.inl ⟨hzK, hzu⟩) (fun hzv => Or.inr ⟨hzK, hzv⟩)⟩
      have hE_conn : IsConnected E :=
        RudinRCA.Chapter14.isConnected_exterior_closedBall hR_pos.le
      have hE_sub : E ⊆ A ∪ B := hAB_union.symm ▸ hext_sub
      have hE_side : E ⊆ A ∨ E ⊆ B := by
        by_contra hnot
        obtain ⟨z₁, hz₁E, hz₁nA⟩ := Set.not_subset.mp fun hEA => hnot (Or.inl hEA)
        obtain ⟨z₂, hz₂E, hz₂nB⟩ := Set.not_subset.mp fun hEB => hnot (Or.inr hEB)
        have hz₁B : z₁ ∈ B := (hE_sub hz₁E).resolve_left hz₁nA
        have hz₂A : z₂ ∈ A := (hE_sub hz₂E).resolve_right hz₂nB
        obtain ⟨z, _, hzAB⟩ :=
          hE_conn.isPreconnected A B hA_open hB_open hE_sub ⟨z₂, hz₂E, hz₂A⟩ ⟨z₁, hz₁E, hz₁B⟩
        rw [hAB_disj] at hzAB
        exact hzAB
      have hsep : ∀ (U V : Set ℂ), IsOpen U → IsOpen V → U ∪ V = Kᶜ → U ∩ V = ∅ →
          V.Nonempty → E ⊆ U → False := by
        intro U V hU hV hUV_eq hUV_disj ⟨b₀, hb₀⟩ hEU
        let W₁ : Set RiemannSphere :=
          RudinRCA.Chapter13.infinityDisc R ∪ (((↑) : ℂ → RiemannSphere) '' U)
        let W₂ : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' V
        have hW₁_open : IsOpen W₁ :=
          (RudinRCA.Chapter13.isOpen_infinityDisc R).union
            (OnePoint.isOpenEmbedding_coe.isOpenMap U hU)
        have hW₂_open : IsOpen W₂ := OnePoint.isOpenEmbedding_coe.isOpenMap V hV
        have hW_cov : sphericalCompl K ⊆ W₁ ∪ W₂ := by
          intro p hp
          induction p using OnePoint.rec with
          | infty =>
            exact Or.inl (Or.inl (RudinRCA.Chapter13.infinity_mem_infinityDisc R))
          | coe z =>
            have hzK : z ∈ Kᶜ := (RudinRCA.Chapter13.coe_mem_sphericalCompl z K).mp hp
            rw [← hUV_eq] at hzK
            rcases hzK with hzU | hzV
            · exact Or.inl (Or.inr (mem_image_of_mem _ hzU))
            · exact Or.inr (mem_image_of_mem _ hzV)
        have hW₁_ne : (sphericalCompl K ∩ W₁).Nonempty :=
          ⟨∞, RudinRCA.Chapter13.infinity_mem_sphericalCompl K,
            Or.inl (RudinRCA.Chapter13.infinity_mem_infinityDisc R)⟩
        have hW₂_ne : (sphericalCompl K ∩ W₂).Nonempty := by
          have hb₀K : b₀ ∈ Kᶜ := hUV_eq ▸ Or.inr hb₀
          exact ⟨(b₀ : RiemannSphere),
            (RudinRCA.Chapter13.coe_mem_sphericalCompl b₀ K).mpr hb₀K,
            mem_image_of_mem _ hb₀⟩
        obtain ⟨q, _, hq₁, hq₂⟩ :=
          hsph.isPreconnected W₁ W₂ hW₁_open hW₂_open hW_cov hW₁_ne hW₂_ne
        obtain ⟨b, hbV, rfl⟩ := hq₂
        have hbU : b ∈ U := by
          rcases hq₁ with hinf | ⟨a, haU, hab⟩
          · exact hEU ((RudinRCA.Chapter13.coe_mem_infinityDisc b R).mp hinf)
          · exact OnePoint.coe_injective hab ▸ haU
        have hb_emp : b ∈ (∅ : Set ℂ) := hUV_disj ▸ ⟨hbU, hbV⟩
        exact hb_emp
      rcases hE_side with hEA | hEB
      · exact hsep A B hA_open hB_open hAB_union hAB_disj hv_ne hEA
      · exact hsep B A hB_open hA_open (union_comm A B ▸ hAB_union)
          (inter_comm A B ▸ hAB_disj) hu_ne hEB

/-- **Node 20.1 (Properties of `P(K)`, Separation Counterexample, Real-Interval Weierstrass, and
Runge Implication, RCA p. 386):**
1. *(Necessary conditions)* For every `K ⊆ ℂ` (in particular compact `K`) and every `f ∈ P(K)`,
   `f` is continuous on `K` and holomorphic on `interior K`.
2. *(Insufficiency when `K` disconnects `ℂ`)* On the unit circle `K = sphere 0 1`, `K` is compact,
   `Kᶜ` is disconnected, `interior K = ∅`, and `f(z) = z⁻¹` is continuous on `K` and holomorphic on
   `interior K`, yet `f ∉ P(K)`.
3. *(Sufficiency on compact real intervals)* For every `a ≤ b` in `ℝ` and
   `K = {(x : ℂ) | x ∈ [a, b]}`, `K` is compact, `interior K = ∅`, `Kᶜ` is connected, and every
   `f : ℂ → ℂ` continuous on `K` belongs to `P(K)`.
4. *(Runge implication)* If `K ⊆ ℂ` is compact with connected complement `Kᶜ` (equivalently
   connected `S² \ K`), `Ω ⊇ K` is open, and `f` is holomorphic on `Ω`, then `f ∈ P(K)`. -/
theorem theorem20_1 :
    (∀ {K : Set ℂ}, IsCompact K → ∀ {f : ℂ → ℂ}, f ∈ PK K →
      ContinuousOn f K ∧ DifferentiableOn ℂ f (interior K) ∧
        RudinRCA.Chapter10.HolomorphicOn f (interior K)) ∧
    (let K : Set ℂ := Metric.sphere (0 : ℂ) 1;
      let f : ℂ → ℂ := fun z => z⁻¹;
      IsCompact K ∧ ¬ IsConnected Kᶜ ∧ interior K = ∅ ∧
        ContinuousOn f K ∧ DifferentiableOn ℂ f (interior K) ∧ f ∉ PK K) ∧
    (∀ {a b : ℝ}, a ≤ b →
      let K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Set.Icc a b;
      IsCompact K ∧ interior K = ∅ ∧ IsConnected Kᶜ ∧
        ∀ f : ℂ → ℂ, ContinuousOn f K → f ∈ PK K) ∧
    (∀ {K Ω : Set ℂ}, IsCompact K → IsConnected Kᶜ → IsOpen Ω → K ⊆ Ω →
      ∀ {f : ℂ → ℂ}, DifferentiableOn ℂ f Ω → f ∈ PK K) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) Necessary conditions: continuity on `K` and holomorphy on `interior K`
    intro K _ f ⟨P, hP⟩
    have hcont : ContinuousOn f K :=
      hP.continuousOn ((Eventually.of_forall fun n => (P n).continuous.continuousOn).frequently)
    have hloc : TendstoLocallyUniformlyOn (fun n z => (P n).eval z) f Filter.atTop (interior K) :=
      (hP.mono interior_subset).tendstoLocallyUniformlyOn
    have hdiff : DifferentiableOn ℂ f (interior K) :=
      hloc.differentiableOn
        (Eventually.of_forall fun n => (P n).differentiable.differentiableOn)
        isOpen_interior
    exact ⟨hcont, hdiff,
      (RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn isOpen_interior).mpr hdiff⟩
  · -- (2) Unit circle counterexample `f(z) = z⁻¹`
    dsimp only
    let K : Set ℂ := Metric.sphere (0 : ℂ) 1
    let f : ℂ → ℂ := fun z => z⁻¹
    have hK_comp : IsCompact K := isCompact_sphere 0 1
    have hK_not_conn : ¬ IsConnected Kᶜ := by
      intro hconn
      let U : Set ℂ := Metric.ball (0 : ℂ) 1
      let V : Set ℂ := {z : ℂ | 1 < ‖z‖}
      have hU_open : IsOpen U := Metric.isOpen_ball
      have hV_open : IsOpen V := isOpen_lt continuous_const continuous_norm
      have hcov : Kᶜ ⊆ U ∪ V := by
        intro z hz
        have hne : ‖z‖ ≠ 1 := by simpa [K] using hz
        exact (hne.lt_or_gt).imp (fun h => by simpa [U] using h) id
      have hU_ne : (Kᶜ ∩ U).Nonempty := ⟨0, by simp [K], by simp [U]⟩
      have hV_ne : (Kᶜ ∩ V).Nonempty := by
        refine ⟨2, ?_, ?_⟩ <;> norm_num [K, V]
      obtain ⟨z, _, hzU, hzV⟩ := hconn.isPreconnected U V hU_open hV_open hcov hU_ne hV_ne
      have h1 : ‖z‖ < 1 := by simpa [U] using hzU
      have h2 : 1 < ‖z‖ := hzV
      linarith
    have hint_empty : interior K = ∅ := by
      ext z
      simp only [mem_interior, mem_empty_iff_false, iff_false, not_exists, not_and]
      intro U hUK hU_open hzU
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU_open z hzU
      have hz_norm : ‖z‖ = 1 := by simpa [K] using hUK hzU
      let w' : ℂ := ((1 + r / 2 : ℝ) : ℂ) * z
      have hw'_mem : w' ∈ Metric.ball z r := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : w' - z = ((r / 2 : ℝ) : ℂ) * z := by dsimp [w']; push_cast; ring
        rw [hsub, norm_mul, hz_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (half_pos hr)]
        linarith
      have hw'_K : w' ∈ K := hUK (hball hw'_mem)
      have hw'_norm : ‖w'‖ = 1 := by simpa [K] using hw'_K
      have hw'_calc : ‖w'‖ = 1 + r / 2 := by
        dsimp [w']
        rw [norm_mul, hz_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
      linarith
    have hf_cont : ContinuousOn f K :=
      continuousOn_inv₀.mono fun z hz => by
        intro hz0; subst hz0; simp [K] at hz
    have hf_diff : DifferentiableOn ℂ f (interior K) := by
      rw [hint_empty]; exact differentiableOn_empty
    have hf_not_PK : f ∉ PK K := by
      intro hmem
      obtain ⟨P, hP⟩ := mem_PK_iff.mp hmem (1 / 2) (by norm_num)
      let g : ℂ → ℂ := fun z => 1 - z * P.eval z
      have hg_diff : Differentiable ℂ g :=
        (differentiable_const 1).sub (differentiable_id.mul P.differentiable)
      have h_front : ∀ z ∈ frontier (Metric.ball (0 : ℂ) 1), ‖g z‖ ≤ 1 / 2 := by
        rw [frontier_ball (0 : ℂ) one_ne_zero]
        intro z hz
        have hz_norm : ‖z‖ = 1 := by simpa using hz
        have hz_ne : z ≠ 0 := by intro h0; subst h0; norm_num at hz_norm
        have hident : g z = z * (z⁻¹ - P.eval z) := by
          dsimp [g]; rw [mul_sub, mul_inv_cancel₀ hz_ne]
        rw [hident, norm_mul, hz_norm, one_mul]
        exact (hP z hz).le
      have h0_le : ‖g 0‖ ≤ 1 / 2 :=
        Complex.norm_le_of_forall_mem_frontier_norm_le
          (Metric.isBounded_ball) hg_diff.diffContOnCl h_front
          (subset_closure (Metric.mem_ball_self zero_lt_one))
      have hg0 : ‖g 0‖ = 1 := by simp [g]
      linarith
    exact ⟨hK_comp, hK_not_conn, hint_empty, hf_cont, hf_diff, hf_not_PK⟩
  · -- (3) Compact real intervals `[a, b]` via Weierstrass
    intro a b hab
    let K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Set.Icc a b
    have hK_comp : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
    have hint_empty : interior K = ∅ := by
      ext z
      simp only [mem_interior, mem_empty_iff_false, iff_false, not_exists, not_and]
      intro U hUK hU_open hzU
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU_open z hzU
      let w : ℂ := z + ((r / 2 : ℝ) : ℂ) * Complex.I
      have hw_ball : w ∈ Metric.ball z r := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : w - z = ((r / 2 : ℝ) : ℂ) * Complex.I := by dsimp [w]; ring
        rw [hsub, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (half_pos hr)]
        linarith
      obtain ⟨x, _, hwx⟩ := hUK (hball hw_ball)
      have him0 : w.im = 0 := by rw [← hwx]; simp
      have him_pos : w.im = z.im + r / 2 := by simp [w]
      have hz_im0 : z.im = 0 := by
        obtain ⟨x₀, _, hzx₀⟩ := hUK hzU
        rw [← hzx₀]; simp
      linarith
    have hK_compl_conn : IsConnected Kᶜ := by
      rcases hab.eq_or_lt with rfl | hlt
      · have hsing : K = {(a : ℂ)} := by simp [K]
        rw [hsing]
        have h0_conn : IsConnected {z : ℂ | (0 : ℝ) < ‖z‖} :=
          RudinRCA.Chapter14.isConnected_exterior_closedBall (le_refl 0)
        have htr : {(a : ℂ)}ᶜ = (fun z : ℂ => z + (a : ℂ)) '' {z : ℂ | (0 : ℝ) < ‖z‖} := by
          ext w
          simp only [mem_compl_iff, mem_singleton_iff, mem_image, mem_ofPred_eq, norm_pos_iff]
          exact ⟨fun hne => ⟨w - (a : ℂ), sub_ne_zero.mpr hne, sub_add_cancel w (a : ℂ)⟩,
            by rintro ⟨z, hz, rfl⟩ h; exact hz (by linear_combination h)⟩
        rw [htr]
        exact h0_conn.image _ (continuous_id.add continuous_const).continuousOn
      · have hJA : RudinRCA.Chapter14.IsJordanArc K := by
          let e₁ : Set.Icc a b ≃ₜ Set.Icc (0 : ℝ) 1 := iccHomeoI a b hlt
          have hemb : Topology.IsEmbedding (fun x : Set.Icc a b => ((x : ℝ) : ℂ)) :=
            Complex.isometry_ofReal.isEmbedding.comp Topology.IsEmbedding.subtypeVal
          have hrange : Set.range (fun x : Set.Icc a b => ((x : ℝ) : ℂ)) = K := by
            ext z; simp [K]
          let e₂ : Set.Icc a b ≃ₜ K :=
            hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
          exact ⟨e₂.symm.trans e₁⟩
        exact RudinRCA.Chapter14.isConnected_compl_of_isJordanArc hJA
    refine ⟨hK_comp, hint_empty, hK_compl_conn, fun f hf => mem_PK_iff.mpr fun ε hε => ?_⟩
    let gC : C(Set.Icc a b, ℂ) :=
      ⟨fun x => f (x : ℂ),
        hf.comp_continuous (Complex.continuous_ofReal.comp continuous_subtype_val)
          fun x => mem_image_of_mem _ x.2⟩
    let uR : C(Set.Icc a b, ℝ) := ⟨fun x => (gC x).re, Complex.continuous_re.comp gC.continuous⟩
    let vR : C(Set.Icc a b, ℝ) := ⟨fun x => (gC x).im, Complex.continuous_im.comp gC.continuous⟩
    have h_weier : ∀ h : C(Set.Icc a b, ℝ), ∃ p : Polynomial ℝ,
        ∀ (x : ℝ) (hx : x ∈ Set.Icc a b), |h ⟨x, hx⟩ - p.eval x| < ε / 2 := by
      intro h
      have htop : h ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure := by
        rw [polynomialFunctions_closure_eq_top a b]; trivial
      rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe, Metric.mem_closure_iff] at htop
      obtain ⟨q, hq_mem, hq_dist⟩ := htop (ε / 2) (half_pos hε)
      rw [polynomialFunctions_coe] at hq_mem
      obtain ⟨p, rfl⟩ := hq_mem
      refine ⟨p, fun x hx => ?_⟩
      have hle : ‖h ⟨x, hx⟩ - (Polynomial.toContinuousMapOn p (Set.Icc a b)) ⟨x, hx⟩‖ ≤
          ‖h - Polynomial.toContinuousMapOn p (Set.Icc a b)‖ :=
        (h - Polynomial.toContinuousMapOn p (Set.Icc a b)).norm_coe_le_norm ⟨x, hx⟩
      rw [dist_eq_norm] at hq_dist
      simpa [Real.norm_eq_abs] using hle.trans_lt hq_dist
    obtain ⟨p_re, hp_re⟩ := h_weier uR
    obtain ⟨p_im, hp_im⟩ := h_weier vR
    let P : Polynomial ℂ :=
      p_re.map Complex.ofRealHom + Polynomial.C Complex.I * p_im.map Complex.ofRealHom
    refine ⟨P, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    have hmap_eval : ∀ p : Polynomial ℝ,
        (p.map Complex.ofRealHom).eval (x : ℂ) = ((p.eval x : ℝ) : ℂ) := by
      intro p
      rw [Polynomial.eval_map]
      exact Polynomial.eval₂_at_apply Complex.ofRealHom x
    have heval : P.eval (x : ℂ) =
        ((p_re.eval x : ℝ) : ℂ) + Complex.I * ((p_im.eval x : ℝ) : ℂ) := by
      simp [P, hmap_eval]
    have hdecomp : f (x : ℂ) - P.eval (x : ℂ) =
        (((f (x : ℂ)).re - p_re.eval x : ℝ) : ℂ) +
          Complex.I * (((f (x : ℂ)).im - p_im.eval x : ℝ) : ℂ) := by
      rw [heval]
      apply Complex.ext <;> simp
    rw [hdecomp]
    calc ‖(((f (x : ℂ)).re - p_re.eval x : ℝ) : ℂ) +
            Complex.I * (((f (x : ℂ)).im - p_im.eval x : ℝ) : ℂ)‖
        ≤ ‖(((f (x : ℂ)).re - p_re.eval x : ℝ) : ℂ)‖ +
            ‖Complex.I * (((f (x : ℂ)).im - p_im.eval x : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |(f (x : ℂ)).re - p_re.eval x| + |(f (x : ℂ)).im - p_im.eval x| := by
            rw [norm_mul, norm_I, one_mul, Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs]
      _ < ε / 2 + ε / 2 := add_lt_add (hp_re x hx) (hp_im x hx)
      _ = ε := add_halves ε
  · -- (4) Runge implication (`Theorem 13.7`)
    intro K Ω hK hK_compl hΩ hKΩ f hf
    exact RudinRCA.Chapter13.theorem13_7 hK
      ((isConnected_compl_iff_sphericalCompl hK).mp hK_compl) hΩ hKΩ
      ((RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn hΩ).mpr hf)


end Node20_1

section Node20_2
open Metric Set Filter Function Complex RudinRCA.Chapter13
open scoped Topology BigOperators OnePoint

/-! ### Node 20.2: Quantitative Cauchy-Kernel Approximation Lemma (with Diagonal & Infinity Disclosures) -/

/-- **Hazard 20.2a Disclosure (`node20_2_diagonal_counterexample`, `SCOPING-H-19-20.md` §hazards-2):**
For any open disc `D = ball z₀ r` (`r > 0`), any compact subset `E ⊆ D`, and any candidate kernel
`Q : ℂ → ℂ → ℂ`:
1. `(D \ E)` is nonempty (`E` cannot fill the open disc `D`), so diagonal pairs `z = ζ` with
   `z ∈ Eᶜ` and `ζ ∈ D` genuinely occur;
2. At every such diagonal point `z = ζ ∈ D \ E`, the literal strict second inequality
   `‖Q ζ z - (z - ζ)⁻¹‖ < 1000 * r ^ 2 / ‖z - ζ‖ ^ 3` is false under totalized division (since
   `‖z - z‖ ^ 3 = 0` makes the right-hand side `0`), so the unrestricted quantification over all
   `z ∈ Eᶜ` and `ζ ∈ D` fails for every `Q`. -/
theorem node20_2_diagonal_counterexample {z₀ : ℂ} {r : ℝ} (hr : 0 < r) {E : Set ℂ}
    (hE_comp : IsCompact E) (hED : E ⊆ Metric.ball z₀ r) (Q : ℂ → ℂ → ℂ) :
    (Metric.ball z₀ r \ E).Nonempty ∧
      (∀ z ∈ Metric.ball z₀ r \ E,
        ¬ (‖Q z z - (z - z)⁻¹‖ < 1000 * r ^ 2 / ‖z - z‖ ^ 3)) ∧
      ¬ (∀ z ∈ Eᶜ, ∀ ζ ∈ Metric.ball z₀ r,
          ‖Q ζ z - (z - ζ)⁻¹‖ < 1000 * r ^ 2 / ‖z - ζ‖ ^ 3) := by
  have hdiff_ne : (Metric.ball z₀ r \ E).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hemp
    have hE_eq : E = Metric.ball z₀ r := Subset.antisymm hED hemp
    have hball_closed : IsClosed (Metric.ball z₀ r) := hE_eq ▸ hE_comp.isClosed
    have hcl_eq : Metric.closedBall z₀ r = Metric.ball z₀ r := by
      rw [← closure_ball z₀ hr.ne', hball_closed.closure_eq]
    have hw_cb : z₀ + (r : ℂ) ∈ Metric.closedBall z₀ r := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr]
    have hw_b : z₀ + (r : ℂ) ∈ Metric.ball z₀ r := hcl_eq ▸ hw_cb
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr] at hw_b
    exact lt_irrefl r hw_b
  have hdiag_false : ∀ z ∈ Metric.ball z₀ r \ E,
      ¬ (‖Q z z - (z - z)⁻¹‖ < 1000 * r ^ 2 / ‖z - z‖ ^ 3) := by
    intro z _ hlt
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      div_zero] at hlt
    exact not_lt_of_ge (norm_nonneg _) hlt
  refine ⟨hdiff_ne, hdiag_false, ?_⟩
  obtain ⟨z, hzD, hzE⟩ := hdiff_ne
  intro hall
  exact hdiag_false z ⟨hzD, hzE⟩ (hall z hzE z hzD)

/-- **Lemma 20.2 (Quantitative Approximation of the Cauchy Kernel `(z - ζ)⁻¹`, RCA pp. 387–388):**
Let `D = ball z₀ r` (`r > 0`), and let `E ⊆ D` be compact and connected with `r ≤ diam E` and
connected spherical complement `Ω = S² \ E` (`sphericalCompl E`). Then there exist `g : ℂ → ℂ` and
`b : ℂ` such that:
1. `g` is holomorphic on `Eᶜ` (`HolomorphicOn g Eᶜ` and `DifferentiableOn ℂ g Eᶜ`);
2. *(Holomorphy and vanishing at `∞ ∈ S² \ E`, Hazard 20.2b)* `Tendsto g cobounded (𝓝 0)` and
   `w ↦ g(w⁻¹)` extends holomorphically across `0` with value `0` (`∃ G_inf, DifferentiableAt ℂ
   G_inf 0 ∧ G_inf 0 = 0 ∧ ∀ᶠ w in 𝓝[≠] 0, G_inf w = g (w⁻¹)`);
3. Putting `Q(ζ, z) = g(z) + (ζ - b) * g(z) ^ 2`:
   - *(First estimate, uniform on `Eᶜ × D`)* `∀ z ∈ Eᶜ, ∀ ζ ∈ D, ‖Q ζ z‖ < 100 / r`,
   - *(Polynomial-multiplied second estimate, everywhere on `Eᶜ × D`)*
     `∀ z ∈ Eᶜ, ∀ ζ ∈ D, ‖(z - ζ) ^ 3 * Q ζ z - (z - ζ) ^ 2‖ < 1000 * r ^ 2`,
   - *(Second estimate on the off-diagonal domain `z ≠ ζ`, Hazard 20.2a)*
     `∀ z ∈ Eᶜ, ∀ ζ ∈ D, z ≠ ζ → ‖Q ζ z - (z - ζ)⁻¹‖ < 1000 * r ^ 2 / ‖z - ζ‖ ^ 3`. -/
theorem theorem20_2 {z₀ : ℂ} {r : ℝ} (hr : 0 < r) {E : Set ℂ}
    (hED : E ⊆ Metric.ball z₀ r) (hE_comp : IsCompact E) (hE_conn : IsConnected E)
    (hdiam : r ≤ Metric.diam E) (hΩ_conn : IsConnected (sphericalCompl E)) :
    ∃ (g : ℂ → ℂ) (b : ℂ),
      RudinRCA.Chapter10.HolomorphicOn g Eᶜ ∧
      DifferentiableOn ℂ g Eᶜ ∧
      Tendsto g (Bornology.cobounded ℂ) (𝓝 0) ∧
      (∃ G_inf : ℂ → ℂ, DifferentiableAt ℂ G_inf 0 ∧ G_inf 0 = 0 ∧
        ∀ᶠ w in 𝓝[≠] (0 : ℂ), G_inf w = g (w⁻¹)) ∧
      (let Q : ℂ → ℂ → ℂ := fun ζ z => g z + (ζ - b) * (g z) ^ 2;
        (∀ z ∈ Eᶜ, ∀ ζ ∈ Metric.ball z₀ r, ‖Q ζ z‖ < 100 / r) ∧
        (∀ z ∈ Eᶜ, ∀ ζ ∈ Metric.ball z₀ r,
          ‖(z - ζ) ^ 3 * Q ζ z - (z - ζ) ^ 2‖ < 1000 * r ^ 2) ∧
        (∀ z ∈ Eᶜ, ∀ ζ ∈ Metric.ball z₀ r, z ≠ ζ →
          ‖Q ζ z - (z - ζ)⁻¹‖ < 1000 * r ^ 2 / ‖z - ζ‖ ^ 3)) := by
  -- Step 1: Pick `a₀, a₁ ∈ E` (`a₁ ≠ a₀`) and map `S² \ E` to a proper simply connected `Ω₁ ⊆ ℂ`
  obtain ⟨a₀, ha₀⟩ := hE_conn.nonempty
  obtain ⟨a₁, ha₁, ha₁_ne⟩ : ∃ a₁ ∈ E, a₁ ≠ a₀ := by
    by_contra hall_eq
    push Not at hall_eq
    have hsub_sing : E ⊆ {a₀} := fun x hx => hall_eq x hx
    have hdiam0 : Metric.diam E ≤ 0 :=
      (Metric.diam_mono hsub_sing isCompact_singleton.isBounded).trans_eq Metric.diam_singleton
    linarith
  have hdet : (0 : ℂ) * (-a₀) - 1 * 1 ≠ 0 := by norm_num
  let e : RiemannSphere ≃ₜ RiemannSphere := RudinRCA.Chapter14.moebiusHomeomorph hdet
  let Ω : Set RiemannSphere := sphericalCompl E
  have hΩ_open : IsOpen Ω := RudinRCA.Chapter13.isOpen_sphericalCompl_of_isCompact hE_comp
  have ha₀_not_Ω : (a₀ : RiemannSphere) ∉ Ω := by
    rw [RudinRCA.Chapter13.coe_mem_sphericalCompl]; exact not_not.mpr ha₀
  have h_e_a₀ : e (a₀ : RiemannSphere) = ∞ := by
    simp [e, RudinRCA.Chapter14.moebiusHomeomorph]
  have h_e_inf : e ∞ = ((0 : ℂ) : RiemannSphere) := by
    simp [e, RudinRCA.Chapter14.moebiusHomeomorph]
  have hinf_not_img : (∞ : RiemannSphere) ∉ e '' Ω := by
    rintro ⟨p, hpΩ, hp_eq⟩
    have hpa₀ : p = (a₀ : RiemannSphere) := e.injective (hp_eq.trans h_e_a₀.symm)
    exact ha₀_not_Ω (hpa₀ ▸ hpΩ)
  let Ω₁ : Set ℂ := ((↑) : ℂ → RiemannSphere) ⁻¹' (e '' Ω)
  have himg_Ω₁ : ((↑) : ℂ → RiemannSphere) '' Ω₁ = e '' Ω := by
    ext q
    induction q using OnePoint.rec with
    | infty =>
      simp only [mem_image, OnePoint.coe_ne_infty, and_false, exists_false, false_iff]
      exact hinf_not_img
    | coe w =>
      simp only [Ω₁, mem_image, mem_preimage, OnePoint.coe_injective.eq_iff, exists_eq_right]
  have hΩ₁_open : IsOpen Ω₁ := (e.isOpenMap Ω hΩ_open).preimage OnePoint.continuous_coe
  have hΩ₁_conn : IsConnected Ω₁ := by
    have he_conn : IsConnected (e '' Ω) := hΩ_conn.image e e.continuous.continuousOn
    rw [← himg_Ω₁] at he_conn
    refine ⟨?_, ?_⟩
    · obtain ⟨_, ⟨w, hw, rfl⟩⟩ := he_conn.nonempty
      exact ⟨w, hw⟩
    · exact OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image.mp he_conn.isPreconnected
  have hΩ₁_reg : RudinRCA.Chapter10.IsRegion Ω₁ := ⟨hΩ₁_open, hΩ₁_conn⟩
  have hΩ₁_sph_conn : IsConnected (sphericalCompl Ω₁) := by
    have hcompl_eq : sphericalCompl Ω₁ = e '' (((↑) : ℂ → RiemannSphere) '' E) := by
      calc sphericalCompl Ω₁
          = (((↑) : ℂ → RiemannSphere) '' Ω₁)ᶜ := rfl
        _ = (e '' Ω)ᶜ := by rw [himg_Ω₁]
        _ = e '' Ωᶜ := (e.image_compl Ω).symm
        _ = e '' (((↑) : ℂ → RiemannSphere) '' E) := by simp [Ω, sphericalCompl]
    rw [hcompl_eq]
    exact (hE_conn.image _ OnePoint.continuous_coe.continuousOn).image e e.continuous.continuousOn
  have hΩ₁_sc : RudinRCA.Chapter10.BookSimplyConnected Ω₁ :=
    ((RudinRCA.Chapter13.theorem13_11 hΩ₁_reg).1.out 2 4).mpr hΩ₁_sph_conn
  have h0_Ω₁ : (0 : ℂ) ∈ Ω₁ := by
    change ((0 : ℂ) : RiemannSphere) ∈ e '' Ω
    exact ⟨∞, RudinRCA.Chapter13.infinity_mem_sphericalCompl E, h_e_inf⟩
  have hmem_Ω₁_ne : ∀ {w : ℂ}, w ≠ 0 → (w ∈ Ω₁ ↔ a₀ + w⁻¹ ∈ Eᶜ) := by
    intro w hw
    change (w : RiemannSphere) ∈ e '' Ω ↔ a₀ + w⁻¹ ∈ Eᶜ
    have he_aw : e ((a₀ + w⁻¹ : ℂ) : RiemannSphere) = (w : RiemannSphere) := by
      change RudinRCA.Chapter14.moebiusMap 0 1 1 (-a₀) ((a₀ + w⁻¹ : ℂ) : RiemannSphere) =
        (w : RiemannSphere)
      rw [RudinRCA.Chapter14.moebiusMap_coe]
      have hden : 1 * (a₀ + w⁻¹) + -a₀ = w⁻¹ := by ring
      rw [hden]
      simp [hw]
    rw [← he_aw, e.injective.mem_set_image, RudinRCA.Chapter13.coe_mem_sphericalCompl]
    rfl
  have hΩ₁_proper : Ω₁ ≠ Set.univ := by
    intro huniv
    have hw₁_ne : (a₁ - a₀)⁻¹ ≠ 0 := inv_ne_zero (sub_ne_zero.mpr ha₁_ne)
    have hw₁_mem : (a₁ - a₀)⁻¹ ∈ Ω₁ := huniv ▸ mem_univ _
    have ha₁_compl : a₀ + ((a₁ - a₀)⁻¹)⁻¹ ∈ Eᶜ := (hmem_Ω₁_ne hw₁_ne).mp hw₁_mem
    rw [inv_inv, add_sub_cancel] at ha₁_compl
    exact ha₁_compl ha₁
  -- Step 2: Apply Theorem 14.9 (normalized Riemann map `h : Ω₁ → U` at `0`) and 10.33 (inverse `φ`)
  obtain ⟨h, hh_holo, hh_bij, hh0, hdh_re, _, _, _⟩ :=
    RudinRCA.Chapter14.theorem14_9 hΩ₁_reg hΩ₁_sc hΩ₁_proper h0_Ω₁
  let β₁ : ℂ := deriv h 0
  have hβ₁_ne : β₁ ≠ 0 := by
    intro h0; dsimp [β₁] at h0; rw [h0, Complex.zero_re] at hdh_re; exact lt_irrefl 0 hdh_re
  have hβ₁_inv_ne : β₁⁻¹ ≠ 0 := inv_ne_zero hβ₁_ne
  have hβ₁_inv_pos : 0 < ‖β₁⁻¹‖ := norm_pos_iff.mpr hβ₁_inv_ne
  obtain ⟨φ, hφ_holo_img, hφ_left, hφ_right_img, hφ_deriv⟩ :=
    (RudinRCA.Chapter10.theorem10_33.1 hΩ₁_open hh_holo hh_bij.injOn).2.2
  rw [hh_bij.image_eq] at hφ_holo_img hφ_right_img
  have hφ0 : φ 0 = 0 := by simpa [hh0] using hφ_left 0 h0_Ω₁
  have hdφ0 : deriv φ 0 = β₁⁻¹ := by simpa [hh0, β₁] using hφ_deriv 0 h0_Ω₁
  have hφ_diff : DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 1) :=
    (RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn Metric.isOpen_ball).mp hφ_holo_img
  -- Step 3: Apply Theorem 14.15 to `F(u) = β₁⁻¹ * (φ u)⁻¹` on `U \ {0}` to get `‖β₁⁻¹‖ ≤ 4 / r`
  let U_punc : Set ℂ := Metric.ball (0 : ℂ) 1 \ {0}
  have hφ_ne_on_punc : ∀ u ∈ U_punc, φ u ≠ 0 := by
    rintro u ⟨hu_ball, hu_ne⟩ h0
    have hu_eq : u = 0 := by
      have := (hφ_right_img u hu_ball).2
      rwa [h0, hh0, eq_comm] at this
    exact hu_ne hu_eq
  let F : ℂ → ℂ := fun u => β₁⁻¹ * (φ u)⁻¹
  have hF_holo : RudinRCA.Chapter10.HolomorphicOn F U_punc := fun u hu =>
    (differentiableAt_const β₁⁻¹).mul ((hφ_holo_img u hu.1).inv (hφ_ne_on_punc u hu))
  have hF_inj : Set.InjOn F U_punc := by
    intro u₁ hu₁ u₂ hu₂ heq
    have hinv_eq : (φ u₁)⁻¹ = (φ u₂)⁻¹ := mul_left_cancel₀ hβ₁_inv_ne heq
    have hφ_eq : φ u₁ = φ u₂ := inv_injective hinv_eq
    calc u₁ = h (φ u₁) := (hφ_right_img u₁ hu₁.1).2.symm
      _ = h (φ u₂) := by rw [hφ_eq]
      _ = u₂ := (hφ_right_img u₂ hu₂.1).2
  have hF_res : ∃ c : ℂ, Tendsto (fun u : ℂ => F u - u⁻¹) (𝓝[≠] 0) (𝓝 c) := by
    let φ₁ : ℂ → ℂ := dslope φ 0
    have hU_nhds : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 zero_lt_one
    have hφ₁_diff : DifferentiableOn ℂ φ₁ (Metric.ball (0 : ℂ) 1) :=
      (Complex.differentiableOn_dslope hU_nhds).mpr hφ_diff
    have hφ₁0 : φ₁ 0 = β₁⁻¹ := by simp [φ₁, dslope_same, hdφ0]
    let φ₂ : ℂ → ℂ := dslope φ₁ 0
    have hφ₂_diff : DifferentiableOn ℂ φ₂ (Metric.ball (0 : ℂ) 1) :=
      (Complex.differentiableOn_dslope hU_nhds).mpr hφ₁_diff
    have hφ₁_cont0 : ContinuousAt φ₁ 0 := (hφ₁_diff.differentiableAt hU_nhds).continuousAt
    have hφ₂_cont0 : ContinuousAt φ₂ 0 := (hφ₂_diff.differentiableAt hU_nhds).continuousAt
    refine ⟨-φ₂ 0 / β₁⁻¹, ?_⟩
    have hlim_quot : Tendsto (fun u : ℂ => -φ₂ u / φ₁ u) (𝓝 0) (𝓝 (-φ₂ 0 / β₁⁻¹)) := by
      rw [← hφ₁0]
      exact (hφ₂_cont0.tendsto.neg).div hφ₁_cont0.tendsto (hφ₁0 ▸ hβ₁_inv_ne)
    refine (hlim_quot.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [sdiff_mem_nhdsWithin_compl hU_nhds {0}] with u hu
    have hu_ne : u ≠ 0 := hu.2
    have hφu_ne : φ u ≠ 0 := hφ_ne_on_punc u hu
    have hφ_eq : φ u = u * φ₁ u := by
      have := sub_smul_dslope φ 0 u
      simpa [φ₁, hφ0, smul_eq_mul] using this.symm
    have hφ₁u_ne : φ₁ u ≠ 0 := fun h0 => hφu_ne (by rw [hφ_eq, h0, mul_zero])
    have hφ₁_eq : φ₁ u = β₁⁻¹ + u * φ₂ u := by
      have := sub_smul_dslope φ₁ 0 u
      rw [hφ₁0, sub_zero, smul_eq_mul] at this
      linear_combination -this
    dsimp [F]
    rw [hφ_eq]
    calc -φ₂ u / φ₁ u
        = (β₁⁻¹ - (β₁⁻¹ + u * φ₂ u)) / (u * φ₁ u) := by
            field_simp [hu_ne, hφ₁u_ne]; ring
      _ = (β₁⁻¹ - φ₁ u) / (u * φ₁ u) := by rw [← hφ₁_eq]
      _ = β₁⁻¹ * (u * φ₁ u)⁻¹ - u⁻¹ := by field_simp [hu_ne, hφ₁u_ne]
  have hF_omit : ∀ z ∈ E, β₁⁻¹ * (z - a₀) ∉ F '' U_punc := by
    rintro z hz ⟨u, hu, heq⟩
    dsimp [F] at heq
    have hinv_eq : (φ u)⁻¹ = z - a₀ := mul_left_cancel₀ hβ₁_inv_ne heq
    have hφu_Ω₁ : φ u ∈ Ω₁ := (hφ_right_img u hu.1).1
    have hφu_ne : φ u ≠ 0 := hφ_ne_on_punc u hu
    have hz_compl : a₀ + (φ u)⁻¹ ∈ Eᶜ := (hmem_Ω₁_ne hφu_ne).mp hφu_Ω₁
    rw [hinv_eq, add_sub_cancel] at hz_compl
    exact hz_compl hz
  have hdiam_le : Metric.diam E ≤ 4 / ‖β₁⁻¹‖ := by
    refine Metric.diam_le_of_forall_dist_le (by positivity) fun z₁ hz₁ z₂ hz₂ => ?_
    have h4 := RudinRCA.Chapter14.theorem14_15.1 hF_holo hF_inj hF_res
      (hF_omit z₁ hz₁) (hF_omit z₂ hz₂)
    have hnorm_sub : ‖β₁⁻¹ * (z₁ - a₀) - β₁⁻¹ * (z₂ - a₀)‖ = ‖β₁⁻¹‖ * dist z₁ z₂ := by
      rw [dist_eq_norm, ← norm_mul]
      congr 1; ring
    rw [hnorm_sub] at h4
    exact (le_div_iff₀' hβ₁_inv_pos).mpr h4
  have hβ₁_inv_bound : ‖β₁⁻¹‖ ≤ 4 / r := by
    have h1 : r ≤ 4 / ‖β₁⁻¹‖ := hdiam.trans hdiam_le
    rw [le_div_iff₀ hβ₁_inv_pos] at h1
    exact (le_div_iff₀ hr).mpr (by linarith)
  -- Step 4: Define `g(z) = β₁⁻¹ * h((z - a₀)⁻¹)` and prove holomorphy on `Eᶜ` and at `∞`
  let g : ℂ → ℂ := fun z => β₁⁻¹ * h ((z - a₀)⁻¹)
  have hinv_mem_Ω₁ : ∀ z ∈ Eᶜ, (z - a₀)⁻¹ ∈ Ω₁ := by
    intro z hz
    have hne : z - a₀ ≠ 0 := sub_ne_zero.mpr fun heq => hz (heq ▸ ha₀)
    rw [hmem_Ω₁_ne (inv_ne_zero hne), inv_inv, add_sub_cancel]
    exact hz
  have hg_holo : RudinRCA.Chapter10.HolomorphicOn g Eᶜ := by
    intro z hz
    have hne : z - a₀ ≠ 0 := sub_ne_zero.mpr fun heq => hz (heq ▸ ha₀)
    have h_inner : DifferentiableAt ℂ (fun w : ℂ => (w - a₀)⁻¹) z :=
      (differentiableAt_id.sub (differentiableAt_const a₀)).inv hne
    exact (differentiableAt_const β₁⁻¹).mul
      ((hh_holo _ (hinv_mem_Ω₁ z hz)).comp z h_inner)
  have hg_diff : DifferentiableOn ℂ g Eᶜ :=
    (RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn hE_comp.isClosed.isOpen_compl).mp hg_holo
  have hg_bound : ∀ z ∈ Eᶜ, ‖g z‖ < 4 / r := by
    intro z hz
    dsimp [g]
    rw [norm_mul]
    have hh_lt1 : ‖h ((z - a₀)⁻¹)‖ < 1 := by
      simpa using hh_bij.mapsTo (hinv_mem_Ω₁ z hz)
    calc ‖β₁⁻¹‖ * ‖h ((z - a₀)⁻¹)‖
        < ‖β₁⁻¹‖ * 1 := mul_lt_mul_of_pos_left hh_lt1 hβ₁_inv_pos
      _ = ‖β₁⁻¹‖ := mul_one _
      _ ≤ 4 / r := hβ₁_inv_bound
  have hg_cobounded : Tendsto g (Bornology.cobounded ℂ) (𝓝 0) := by
    have hinv_0 : Tendsto (fun z : ℂ => (z - a₀)⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [tendsto_norm_cobounded_atTop.eventually
        (eventually_gt_atTop (‖a₀‖ + 1 / ε))] with z hz_gt
      have hdiff_gt : 1 / ε < ‖z - a₀‖ := by
        linarith [norm_sub_norm_le z a₀]
      have hdiff_pos : 0 < ‖z - a₀‖ := lt_trans (by positivity) hdiff_gt
      rw [dist_zero_right, norm_inv]
      exact inv_lt_of_inv_lt₀ hε (by simpa [one_div] using hdiff_gt)
    have hh_cont0 : ContinuousAt h 0 := (hh_holo 0 h0_Ω₁).continuousAt
    have hlim : Tendsto g (Bornology.cobounded ℂ) (𝓝 (β₁⁻¹ * h 0)) :=
      (hh_cont0.tendsto.comp hinv_0).const_mul β₁⁻¹
    simpa [hh0] using hlim
  have hg_inf : ∃ G_inf : ℂ → ℂ, DifferentiableAt ℂ G_inf 0 ∧ G_inf 0 = 0 ∧
      ∀ᶠ w in 𝓝[≠] (0 : ℂ), G_inf w = g (w⁻¹) := by
    let ψ_inf : ℂ → ℂ := fun w => w / (1 - a₀ * w)
    let G_inf : ℂ → ℂ := fun w => β₁⁻¹ * h (ψ_inf w)
    have hψ_inf_0 : ψ_inf 0 = 0 := by simp [ψ_inf]
    have hψ_inf_diff0 : DifferentiableAt ℂ ψ_inf 0 :=
      differentiableAt_id.div
        ((differentiableAt_const 1).sub ((differentiableAt_const a₀).mul differentiableAt_id))
        (by simp)
    have hh_at_ψ_inf : DifferentiableAt ℂ h (ψ_inf 0) := hψ_inf_0.symm ▸ (hh_holo 0 h0_Ω₁)
    have hG_inf_diff0 : DifferentiableAt ℂ G_inf 0 :=
      (differentiableAt_const β₁⁻¹).mul (hh_at_ψ_inf.comp (0 : ℂ) hψ_inf_diff0)
    have hopen_den : IsOpen {w : ℂ | 1 - a₀ * w ≠ 0} :=
      isOpen_ne_fun (continuous_const.sub (continuous_const.mul continuous_id)) continuous_const
    have hnhds_den : {w : ℂ | 1 - a₀ * w ≠ 0} ∈ 𝓝 (0 : ℂ) := hopen_den.mem_nhds (by simp)
    refine ⟨G_inf, hG_inf_diff0, by simp [G_inf, hψ_inf_0, hh0], ?_⟩
    filter_upwards [sdiff_mem_nhdsWithin_compl hnhds_den {0}] with w ⟨hw_den, hw_ne⟩
    have hw_den' : 1 - a₀ * w ≠ 0 := hw_den
    have hw_ne' : w ≠ 0 := hw_ne
    dsimp [G_inf, ψ_inf, g]
    congr 2
    have hden' : w⁻¹ - a₀ ≠ 0 := by
      intro h0
      apply hw_den'
      have h1 : w⁻¹ = a₀ := sub_eq_zero.mp h0
      rw [← h1, inv_mul_cancel₀ hw_ne', sub_self]
    field_simp [hw_ne', hw_den', hden']
  -- Step 5: Expand `G(w) = g(z₀ + w⁻¹)` on `B = ball 0 (1 / r)` around `w = 0`
  let B : Set ℂ := Metric.ball (0 : ℂ) (1 / r)
  have h1r_pos : 0 < 1 / r := one_div_pos.mpr hr
  have hB_nhds : B ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 h1r_pos
  have ha₀_dist : ‖z₀ - a₀‖ < r := by
    have := hED ha₀
    rwa [Metric.mem_ball, dist_comm, dist_eq_norm] at this
  let ψ : ℂ → ℂ := fun w => w / (1 + (z₀ - a₀) * w)
  have hψ_den_ne : ∀ w ∈ B, 1 + (z₀ - a₀) * w ≠ 0 := by
    intro w hw h0
    have hw_lt : ‖w‖ < 1 / r := by simpa [B] using hw
    have hprod_lt : ‖(z₀ - a₀) * w‖ < 1 := by
      rw [norm_mul]
      calc ‖z₀ - a₀‖ * ‖w‖
          ≤ ‖z₀ - a₀‖ * (1 / r) := mul_le_mul_of_nonneg_left hw_lt.le (norm_nonneg _)
        _ < r * (1 / r) := mul_lt_mul_of_pos_right ha₀_dist h1r_pos
        _ = 1 := mul_one_div_cancel hr.ne'
    have h1 : (z₀ - a₀) * w = -1 := eq_neg_of_add_eq_zero_right h0
    rw [h1, norm_neg, norm_one] at hprod_lt
    exact lt_irrefl 1 hprod_lt
  have hψ_maps : Set.MapsTo ψ B Ω₁ := by
    intro w hw
    by_cases hw0 : w = 0
    · subst hw0; simpa [ψ] using h0_Ω₁
    · have hden : 1 + (z₀ - a₀) * w ≠ 0 := hψ_den_ne w hw
      have hψ_ne : ψ w ≠ 0 := div_ne_zero hw0 hden
      rw [hmem_Ω₁_ne hψ_ne]
      have hid : a₀ + (ψ w)⁻¹ = z₀ + w⁻¹ := by
        dsimp [ψ]
        field_simp [hw0, hden]
        ring
      rw [hid]
      intro hzE
      have hz_ball : ‖(z₀ + w⁻¹) - z₀‖ < r := by
        have := hED hzE
        rwa [Metric.mem_ball, dist_eq_norm] at this
      rw [add_sub_cancel_left, norm_inv] at hz_ball
      have hw_lt : ‖w‖ < 1 / r := by simpa [B] using hw
      have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hr_lt : r < ‖w‖⁻¹ := lt_inv_of_lt_inv₀ hw_pos (by simpa [one_div] using hw_lt)
      linarith
  let G : ℂ → ℂ := fun w => β₁⁻¹ * h (ψ w)
  have hG_eq_g : ∀ w ∈ B, w ≠ 0 → G w = g (z₀ + w⁻¹) := by
    intro w hw hw0
    have hden : 1 + (z₀ - a₀) * w ≠ 0 := hψ_den_ne w hw
    dsimp [G, g, ψ]
    congr 2
    have hden2 : z₀ + w⁻¹ - a₀ ≠ 0 := by
      intro h0
      apply hden
      have h1 : w⁻¹ = -(z₀ - a₀) := by linear_combination h0
      have h2 : w⁻¹ * w = -(z₀ - a₀) * w := congrArg (· * w) h1
      rw [inv_mul_cancel₀ hw0] at h2
      linear_combination h2
    field_simp [hw0, hden, hden2]
    ring
  have hG_diff : DifferentiableOn ℂ G B := by
    intro w hw
    have hψ_at : DifferentiableAt ℂ ψ w :=
      differentiableAt_id.div
        ((differentiableAt_const 1).add
          ((differentiableAt_const (z₀ - a₀)).mul differentiableAt_id))
        (hψ_den_ne w hw)
    exact ((differentiableAt_const β₁⁻¹).mul
      ((hh_holo (ψ w) (hψ_maps hw)).comp w hψ_at)).differentiableWithinAt
  have hG0 : G 0 = 0 := by simp [G, ψ, hh0]
  have hdG0 : deriv G 0 = 1 := by
    have hψ_deriv0 : HasDerivAt ψ 1 0 := by
      have h1 : HasDerivAt (fun w : ℂ => w) 1 0 := hasDerivAt_id 0
      have h2 : HasDerivAt (fun w : ℂ => 1 + (z₀ - a₀) * w) (z₀ - a₀) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (z₀ - a₀)).const_add 1
      convert h1.div h2 (by simp) using 1
      simp
    have hh_deriv0 : HasDerivAt h β₁ 0 := hh_holo 0 h0_Ω₁ |>.hasDerivAt
    have hψ0 : ψ 0 = 0 := by simp [ψ]
    have hh_deriv_ψ : HasDerivAt h β₁ (ψ 0) := hψ0.symm ▸ hh_deriv0
    have hG_deriv0 : HasDerivAt G (β₁⁻¹ * (β₁ * 1)) 0 :=
      (hh_deriv_ψ.comp (0 : ℂ) hψ_deriv0).const_mul β₁⁻¹
    rw [mul_one, inv_mul_cancel₀ hβ₁_ne] at hG_deriv0
    exact hG_deriv0.deriv
  have hG_bound : ∀ w ∈ B, ‖G w‖ ≤ 4 / r := by
    intro w hw
    dsimp [G]
    rw [norm_mul]
    have hh_lt1 : ‖h (ψ w)‖ < 1 := by simpa using hh_bij.mapsTo (hψ_maps hw)
    calc ‖β₁⁻¹‖ * ‖h (ψ w)‖
        ≤ ‖β₁⁻¹‖ * 1 := mul_le_mul_of_nonneg_left hh_lt1.le (norm_nonneg _)
      _ = ‖β₁⁻¹‖ := mul_one _
      _ ≤ 4 / r := hβ₁_inv_bound
  -- Step 6: Extract `G(w) = w + c₂ * w^2 + w^3 * H(w)` via `dslope` and prove `‖c₂‖ ≤ 4 * r`
  let G₁ : ℂ → ℂ := dslope G 0
  have hG₁_diff : DifferentiableOn ℂ G₁ B := (Complex.differentiableOn_dslope hB_nhds).mpr hG_diff
  have hG₁0 : G₁ 0 = 1 := by simp [G₁, dslope_same, hdG0]
  let G₂ : ℂ → ℂ := dslope G₁ 0
  have hG₂_diff : DifferentiableOn ℂ G₂ B := (Complex.differentiableOn_dslope hB_nhds).mpr hG₁_diff
  let c₂ : ℂ := deriv G₁ 0
  have hG₂0 : G₂ 0 = c₂ := by simp [G₂, c₂, dslope_same]
  let H : ℂ → ℂ := dslope G₂ 0
  have hH_diff : DifferentiableOn ℂ H B := (Complex.differentiableOn_dslope hB_nhds).mpr hG₂_diff
  have hG_taylor : ∀ w : ℂ, G w = w + c₂ * w ^ 2 + w ^ 3 * H w := by
    intro w
    have h1 : G w = w * G₁ w := by
      have := sub_smul_dslope G 0 w
      simpa [G₁, hG0, smul_eq_mul] using this.symm
    have h2 : G₁ w = 1 + w * G₂ w := by
      have := sub_smul_dslope G₁ 0 w
      rw [hG₁0, sub_zero, smul_eq_mul] at this
      linear_combination -this
    have h3 : G₂ w = c₂ + w * H w := by
      have := sub_smul_dslope G₂ 0 w
      rw [hG₂0, sub_zero, smul_eq_mul] at this
      linear_combination -this
    rw [h1, h2, h3]
    ring
  have hc₂_bound : ‖c₂‖ ≤ 4 * r := by
    have hcauchy_ρ : ∀ ρ ∈ Set.Ioo (0 : ℝ) (1 / r), ‖c₂‖ ≤ 4 / (r * ρ ^ 2) := by
      rintro ρ ⟨hρ_pos, hρ_lt⟩
      have hcb_sub : Metric.closedBall (0 : ℂ) ρ ⊆ B :=
        Metric.closedBall_subset_ball hρ_lt
      have hG₁_dc : DiffContOnCl ℂ G₁ (Metric.ball (0 : ℂ) ρ) :=
        ⟨hG₁_diff.mono (Metric.ball_subset_closedBall.trans hcb_sub),
          (hG₁_diff.continuousOn.mono hcb_sub).mono
            (closure_ball_subset_closedBall)⟩
      have hG₁_sph : ∀ w ∈ Metric.sphere (0 : ℂ) ρ, ‖G₁ w‖ ≤ (4 / r) / ρ := by
        intro w hw
        have hw_norm : ‖w‖ = ρ := by simpa using hw
        have hw_B : w ∈ B := hcb_sub (sphere_subset_closedBall hw)
        have hGw : G w = w * G₁ w := by
          have := sub_smul_dslope G 0 w
          simpa [G₁, hG0, smul_eq_mul] using this.symm
        have hprod_le : ρ * ‖G₁ w‖ ≤ 4 / r := by
          rw [← hw_norm, ← norm_mul, ← hGw]
          exact hG_bound w hw_B
        exact (le_div_iff₀' hρ_pos).mpr hprod_le
      have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ_pos hG₁_dc hG₁_sph
      dsimp [c₂]
      refine hd.trans_eq ?_
      field_simp [hr.ne', hρ_pos.ne']
    let ρ_seq : ℕ → ℝ := fun n => (1 / r) * (((n : ℝ) + 1) / ((n : ℝ) + 2))
    have hρ_mem : ∀ n : ℕ, ρ_seq n ∈ Set.Ioo (0 : ℝ) (1 / r) := by
      intro n
      dsimp [ρ_seq]
      have hnum : 0 < (n : ℝ) + 1 := by positivity
      have hden : 0 < (n : ℝ) + 2 := by positivity
      have hlt1 : ((n : ℝ) + 1) / ((n : ℝ) + 2) < 1 :=
        (div_lt_one hden).mpr (by linarith)
      exact ⟨by positivity, mul_lt_of_lt_one_right h1r_pos hlt1⟩
    have hfrac_tend : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) atTop (𝓝 1) := by
      have heq : (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) =
          fun n : ℕ => 1 - 1 / ((n : ℝ) + 2) := by
        ext n
        have hden : (n : ℝ) + 2 ≠ 0 := by positivity
        field_simp [hden]; ring
      rw [heq]
      have hdiv0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hdiv0
    have hρ_tend : Tendsto ρ_seq atTop (𝓝 (1 / r)) := by
      simpa [ρ_seq] using hfrac_tend.const_mul (1 / r)
    have hrhs_tend : Tendsto (fun n : ℕ => 4 / (r * (ρ_seq n) ^ 2)) atTop (𝓝 (4 * r)) := by
      have hden_tend : Tendsto (fun n : ℕ => r * (ρ_seq n) ^ 2) atTop (𝓝 (r * (1 / r) ^ 2)) :=
        (hρ_tend.pow 2).const_mul r
      have hden_val : r * (1 / r) ^ 2 = 1 / r := by field_simp [hr.ne']
      rw [hden_val] at hden_tend
      have hlim := tendsto_const_nhds (x := (4 : ℝ)).div hden_tend h1r_pos.ne'
      have hval : (4 : ℝ) / (1 / r) = 4 * r := by field_simp [hr.ne']
      rwa [hval] at hlim
    exact ge_of_tendsto hrhs_tend (Eventually.of_forall fun n => hcauchy_ρ (ρ_seq n) (hρ_mem n))
  -- Step 7: Set `b = z₀ + c₂` and prove the first estimate `‖Q ζ z‖ < 84 / r < 100 / r`
  let b : ℂ := z₀ + c₂
  let Q : ℂ → ℂ → ℂ := fun ζ z => g z + (ζ - b) * (g z) ^ 2
  have hQ_bound84 : ∀ z ∈ Eᶜ, ∀ ζ ∈ Metric.ball z₀ r, ‖Q ζ z‖ < 84 / r := by
    intro z hz ζ hζ
    have hζ_lt : ‖ζ - z₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hζ
    have hζb_lt : ‖ζ - b‖ < 5 * r := by
      have hsub : ζ - b = (ζ - z₀) - c₂ := by dsimp [b]; ring
      rw [hsub]
      calc ‖(ζ - z₀) - c₂‖ ≤ ‖ζ - z₀‖ + ‖c₂‖ := norm_sub_le _ _
        _ < r + 4 * r := add_lt_add_of_lt_of_le hζ_lt hc₂_bound
        _ = 5 * r := by ring
    have hgz : ‖g z‖ < 4 / r := hg_bound z hz
    dsimp [Q]
    calc ‖g z + (ζ - b) * (g z) ^ 2‖
        ≤ ‖g z‖ + ‖(ζ - b) * (g z) ^ 2‖ := norm_add_le _ _
      _ = ‖g z‖ + ‖ζ - b‖ * ‖g z‖ ^ 2 := by rw [norm_mul (ζ - b), norm_pow (g z) 2]
      _ < 4 / r + (5 * r) * (4 / r) ^ 2 := by
            refine add_lt_add_of_lt_of_le hgz ?_
            exact mul_le_mul hζb_lt.le (pow_le_pow_left₀ (norm_nonneg _) hgz.le 2)
              (sq_nonneg _) (by positivity)
      _ = 84 / r := by field_simp [hr.ne']; ring
  have hQ_est1 : ∀ z ∈ Eᶜ, ∀ ζ ∈ Metric.ball z₀ r, ‖Q ζ z‖ < 100 / r := by
    intro z hz ζ hζ
    refine (hQ_bound84 z hz ζ hζ).trans ?_
    exact div_lt_div_of_pos_right (by norm_num) hr
  -- Step 8: Second estimate via Maximum Modulus on `closedBall 0 (5 / (6 * r))`
  have hQ_near_est : ∀ z ∈ Eᶜ, ‖z - z₀‖ ≤ (6 / 5) * r → ∀ ζ ∈ Metric.ball z₀ r,
      ‖(z - ζ) ^ 3 * Q ζ z - (z - ζ) ^ 2‖ ≤ (112409 / 125) * r ^ 2 := by
    intro z hz hzz₀ ζ hζ
    have hζ_lt : ‖ζ - z₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hζ
    have hzζ_le : ‖z - ζ‖ ≤ (11 / 5) * r := by
      have hsub : z - ζ = (z - z₀) - (ζ - z₀) := by ring
      rw [hsub]
      calc ‖(z - z₀) - (ζ - z₀)‖ ≤ ‖z - z₀‖ + ‖ζ - z₀‖ := norm_sub_le _ _
        _ ≤ (6 / 5) * r + r := add_le_add hzz₀ hζ_lt.le
        _ = (11 / 5) * r := by ring
    have hQ_le : ‖Q ζ z‖ ≤ 84 / r := (hQ_bound84 z hz ζ hζ).le
    calc ‖(z - ζ) ^ 3 * Q ζ z - (z - ζ) ^ 2‖
        ≤ ‖(z - ζ) ^ 3 * Q ζ z‖ + ‖(z - ζ) ^ 2‖ := norm_sub_le _ _
      _ = ‖z - ζ‖ ^ 3 * ‖Q ζ z‖ + ‖z - ζ‖ ^ 2 := by rw [norm_mul, norm_pow, norm_pow]
      _ ≤ ((11 / 5) * r) ^ 3 * (84 / r) + ((11 / 5) * r) ^ 2 := by
            refine add_le_add ?_ (pow_le_pow_left₀ (norm_nonneg _) hzζ_le 2)
            exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzζ_le 3) hQ_le
              (norm_nonneg _) (by positivity)
      _ = (112409 / 125) * r ^ 2 := by field_simp [hr.ne']; ring
  have hQ_poly_est : ∀ z ∈ Eᶜ, ∀ ζ ∈ Metric.ball z₀ r,
      ‖(z - ζ) ^ 3 * Q ζ z - (z - ζ) ^ 2‖ < 1000 * r ^ 2 := by
    intro z hz ζ hζ
    have hlt_1000 : (112409 / 125) * r ^ 2 < 1000 * r ^ 2 :=
      mul_lt_mul_of_pos_right (by norm_num) (sq_pos_of_pos hr)
    by_cases hnear : ‖z - z₀‖ ≤ (6 / 5) * r
    · exact (hQ_near_est z hz hnear ζ hζ).trans_lt hlt_1000
    · push Not at hnear
      let u : ℂ := ζ - z₀
      let R_rem : ℂ → ℂ := fun w =>
        H w + (u - c₂) * (2 * (c₂ + w * H w) + w * (c₂ + w * H w) ^ 2)
      let K_ζ : ℂ → ℂ := fun w => (1 - u * w) ^ 2 * ((1 - u * w) * R_rem w - u ^ 2)
      have hR_diff : DifferentiableOn ℂ R_rem B := by
        dsimp [R_rem]
        have hlin : DifferentiableOn ℂ (fun w : ℂ => c₂ + w * H w) B :=
          (differentiableOn_const c₂).add (differentiableOn_id.mul hH_diff)
        exact hH_diff.add
          ((differentiableOn_const (u - c₂)).mul
            (((differentiableOn_const 2).mul hlin).add (differentiableOn_id.mul (hlin.pow 2))))
      have hK_diff : DifferentiableOn ℂ K_ζ B := by
        dsimp [K_ζ]
        have h1uw : DifferentiableOn ℂ (fun w : ℂ => 1 - u * w) B :=
          (differentiableOn_const 1).sub ((differentiableOn_const u).mul differentiableOn_id)
        exact (h1uw.pow 2).mul ((h1uw.mul hR_diff).sub (differentiableOn_const (u ^ 2)))
      have hK_ident : ∀ w ∈ B, w ≠ 0 →
          K_ζ w = ((z₀ + w⁻¹) - ζ) ^ 3 * Q ζ (z₀ + w⁻¹) - ((z₀ + w⁻¹) - ζ) ^ 2 := by
        intro w hw hw0
        have hGw : g (z₀ + w⁻¹) = G w := (hG_eq_g w hw hw0).symm
        have hζb : ζ - b = u - c₂ := by dsimp [u, b]; ring
        have hz_sub : (z₀ + w⁻¹) - ζ = w⁻¹ - u := by dsimp [u]; ring
        dsimp [Q]
        rw [hGw, hζb, hz_sub, hG_taylor w]
        dsimp [K_ζ, R_rem]
        field_simp [hw0]
        ring
      let ρ₀ : ℝ := 5 / (6 * r)
      have hρ₀_pos : 0 < ρ₀ := by positivity
      have hρ₀_lt : ρ₀ < 1 / r := by
        dsimp [ρ₀]
        rw [div_lt_div_iff₀ (by positivity) hr]
        linarith
      have hcb_sub : Metric.closedBall (0 : ℂ) ρ₀ ⊆ B :=
        Metric.closedBall_subset_ball hρ₀_lt
      have hK_dc : DiffContOnCl ℂ K_ζ (Metric.ball (0 : ℂ) ρ₀) :=
        ⟨hK_diff.mono (Metric.ball_subset_closedBall.trans hcb_sub),
          (hK_diff.continuousOn.mono hcb_sub).mono closure_ball_subset_closedBall⟩
      have hK_front : ∀ w' ∈ frontier (Metric.ball (0 : ℂ) ρ₀),
          ‖K_ζ w'‖ ≤ (112409 / 125) * r ^ 2 := by
        rw [frontier_ball 0 hρ₀_pos.ne']
        intro w' hw'
        have hw'_norm : ‖w'‖ = ρ₀ := by simpa using hw'
        have hw'_ne : w' ≠ 0 := by
          rintro rfl
          rw [norm_zero] at hw'_norm
          exact hρ₀_pos.ne hw'_norm
        have hw'_B : w' ∈ B := hcb_sub (sphere_subset_closedBall hw')
        let z' : ℂ := z₀ + w'⁻¹
        have hz'_dist : ‖z' - z₀‖ = (6 / 5) * r := by
          dsimp [z', ρ₀] at hw'_norm ⊢
          rw [add_sub_cancel_left, norm_inv, hw'_norm]
          field_simp [hr.ne']
        have hz'_compl : z' ∈ Eᶜ := by
          intro hz'E
          have hlt : ‖z' - z₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hED hz'E
          linarith
        rw [hK_ident w' hw'_B hw'_ne]
        exact hQ_near_est z' hz'_compl hz'_dist.le ζ hζ
      let w : ℂ := (z - z₀)⁻¹
      have hz_sub_pos : 0 < ‖z - z₀‖ := lt_trans (by positivity) hnear
      have hw_ne : w ≠ 0 := inv_ne_zero (norm_pos_iff.mp hz_sub_pos)
      have hw_norm_lt : ‖w‖ < ρ₀ := by
        dsimp [w, ρ₀]
        rw [norm_inv]
        have h1 : ((6 / 5) * r)⁻¹ = 5 / (6 * r) := by field_simp [hr.ne']
        rw [← h1]
        exact inv_strictAnti₀ (by positivity) hnear
      have hw_B : w ∈ B := hcb_sub (Metric.ball_subset_closedBall (mem_ball_zero_iff.mpr hw_norm_lt))
      have hz_eq : z₀ + w⁻¹ = z := by dsimp [w]; rw [inv_inv, add_sub_cancel]
      have hKw_le : ‖K_ζ w‖ ≤ (112409 / 125) * r ^ 2 :=
        Complex.norm_le_of_forall_mem_frontier_norm_le
          Metric.isBounded_ball hK_dc hK_front
          (subset_closure (mem_ball_zero_iff.mpr hw_norm_lt))
      rw [hK_ident w hw_B hw_ne, hz_eq] at hKw_le
      exact hKw_le.trans_lt hlt_1000
  have hQ_est2 : ∀ z ∈ Eᶜ, ∀ ζ ∈ Metric.ball z₀ r, z ≠ ζ →
      ‖Q ζ z - (z - ζ)⁻¹‖ < 1000 * r ^ 2 / ‖z - ζ‖ ^ 3 := by
    intro z hz ζ hζ hne
    have hsub_ne : z - ζ ≠ 0 := sub_ne_zero.mpr hne
    have hnorm3_pos : 0 < ‖z - ζ‖ ^ 3 := pow_pos (norm_pos_iff.mpr hsub_ne) 3
    rw [lt_div_iff₀ hnorm3_pos]
    have hmul : ‖Q ζ z - (z - ζ)⁻¹‖ * ‖z - ζ‖ ^ 3 =
        ‖(z - ζ) ^ 3 * Q ζ z - (z - ζ) ^ 2‖ := by
      rw [← norm_pow, ← norm_mul]
      congr 1
      field_simp [hsub_ne]
    rw [hmul]
    exact hQ_poly_est z hz ζ hζ
  exact ⟨g, b, hg_holo, hg_diff, hg_cobounded, hg_inf, hQ_est1, hQ_poly_est, hQ_est2⟩

/-- Planar-complement (`IsConnected Eᶜ`) wrapper for Lemma 20.2 (`theorem20_2`), using
`isConnected_compl_iff_sphericalCompl`. -/
theorem theorem20_2_compl {z₀ : ℂ} {r : ℝ} (hr : 0 < r) {E : Set ℂ}
    (hED : E ⊆ Metric.ball z₀ r) (hE_comp : IsCompact E) (hE_conn : IsConnected E)
    (hdiam : r ≤ Metric.diam E) (hEc_conn : IsConnected Eᶜ) :
    ∃ (g : ℂ → ℂ) (b : ℂ),
      RudinRCA.Chapter10.HolomorphicOn g Eᶜ ∧
      DifferentiableOn ℂ g Eᶜ ∧
      Tendsto g (Bornology.cobounded ℂ) (𝓝 0) ∧
      (∃ G_inf : ℂ → ℂ, DifferentiableAt ℂ G_inf 0 ∧ G_inf 0 = 0 ∧
        ∀ᶠ w in 𝓝[≠] (0 : ℂ), G_inf w = g (w⁻¹)) ∧
      (let Q : ℂ → ℂ → ℂ := fun ζ z => g z + (ζ - b) * (g z) ^ 2;
        (∀ z ∈ Eᶜ, ∀ ζ ∈ Metric.ball z₀ r, ‖Q ζ z‖ < 100 / r) ∧
        (∀ z ∈ Eᶜ, ∀ ζ ∈ Metric.ball z₀ r,
          ‖(z - ζ) ^ 3 * Q ζ z - (z - ζ) ^ 2‖ < 1000 * r ^ 2) ∧
        (∀ z ∈ Eᶜ, ∀ ζ ∈ Metric.ball z₀ r, z ≠ ζ →
          ‖Q ζ z - (z - ζ)⁻¹‖ < 1000 * r ^ 2 / ‖z - ζ‖ ^ 3)) :=
  theorem20_2 hr hED hE_comp hE_conn hdiam
    ((isConnected_compl_iff_sphericalCompl hE_comp).mp hEc_conn)

end Node20_2

section Node20_3
open Metric Set Filter Function Complex MeasureTheory
open scoped Topology BigOperators

/-! ### Node 20.3: Cauchy–Green (Pompeiu) Representation Formula -/

/-- **Wirtinger `∂̄` operator (`(∂_x f + i ∂_y f) / 2`, RCA p. 388, eq. (1)):**
Defined via the real Fréchet derivative `fderiv ℝ f z` evaluated at `1` (`∂_x`) and `I` (`∂_y`). -/
def wirtingerBar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / 2

/-- If `f` is complex-differentiable at `z`, then `wirtingerBar f z = 0` (Cauchy–Riemann). -/
theorem wirtingerBar_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : wirtingerBar f z = 0 := by
  have hreal : HasFDerivAt f ((fderiv ℂ f z).restrictScalars ℝ) z :=
    hf.hasFDerivAt.restrictScalars ℝ
  have hfderiv : fderiv ℝ f z = (fderiv ℂ f z).restrictScalars ℝ := hreal.fderiv
  unfold wirtingerBar
  rw [hfderiv]
  change (fderiv ℂ f z 1 + Complex.I * fderiv ℂ f z Complex.I) / 2 = 0
  have hI : fderiv ℂ f z Complex.I = Complex.I * fderiv ℂ f z 1 := by
    have h := (fderiv ℂ f z).map_smul Complex.I (1 : ℂ)
    simpa only [smul_eq_mul, mul_one] using h
  rw [hI, ← mul_assoc, Complex.I_mul_I]
  ring

/-- Continuity of `wirtingerBar f` for `C¹` planar functions `f : ℂ → ℂ`. -/
theorem continuous_wirtingerBar {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) :
    Continuous (wirtingerBar f) := by
  unfold wirtingerBar
  have hdf : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have h1 : Continuous (fun z : ℂ => fderiv ℝ f z 1) :=
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous.comp hdf
  have hI : Continuous (fun z : ℂ => fderiv ℝ f z Complex.I) :=
    (ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous.comp hdf
  exact (h1.add (continuous_const.mul hI)).div_const 2

/-- `tsupport (wirtingerBar f) ⊆ tsupport f`. -/
theorem tsupport_wirtingerBar_subset {f : ℂ → ℂ} :
    tsupport (wirtingerBar f) ⊆ tsupport f := by
  refine closure_minimal ?_ (isClosed_tsupport f)
  intro z hz
  by_contra hnot
  have hev : f =ᶠ[𝓝 z] 0 := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hnot] with w hw
    exact image_eq_zero_of_notMem_tsupport hw
  have hf0 : fderiv ℝ f z = 0 := by
    rw [hev.fderiv_eq]
    simp
  have hw0 : wirtingerBar f z = 0 := by
    simp [wirtingerBar, hf0]
  exact hz hw0

/-- Compact support of `wirtingerBar f` from compact support of `f`. -/
theorem hasCompactSupport_wirtingerBar {f : ℂ → ℂ} (hsupp : HasCompactSupport f) :
    HasCompactSupport (wirtingerBar f) :=
  HasCompactSupport.of_support_subset_isCompact hsupp
    ((subset_tsupport (wirtingerBar f)).trans tsupport_wirtingerBar_subset)

/-- Translation invariance of `wirtingerBar`: `∂̄(w ↦ f(z + w))(w) = (∂̄f)(z + w)`. -/
theorem wirtingerBar_comp_add_left (f : ℂ → ℂ) (z w : ℂ) :
    wirtingerBar (fun u => f (z + u)) w = wirtingerBar f (z + w) := by
  by_cases hdf : DifferentiableAt ℝ f (z + w)
  · have hadd : HasFDerivAt (fun u : ℂ => z + u) (ContinuousLinearMap.id ℝ ℂ) w := by
      simpa using (hasFDerivAt_id w).const_add z
    have hcomp : HasFDerivAt (fun u : ℂ => f (z + u))
        ((fderiv ℝ f (z + w)).comp (ContinuousLinearMap.id ℝ ℂ)) w :=
      hdf.hasFDerivAt.comp w hadd
    have hfderiv_eq : fderiv ℝ (fun u : ℂ => f (z + u)) w = fderiv ℝ f (z + w) := by
      rw [hcomp.fderiv]; ext x; simp
    simp [wirtingerBar, hfderiv_eq]
  · let G : ℂ → ℂ := fun u => f (z + u)
    have hdf' : ¬ DifferentiableAt ℝ G w := by
      intro hc
      have hc' : DifferentiableAt ℝ G ((z + w) - z) := by
        simpa [add_sub_cancel_left] using hc
      have hsub : DifferentiableAt ℝ (fun v : ℂ => v - z) (z + w) :=
        differentiableAt_id.sub_const z
      have h_at : DifferentiableAt ℝ (G ∘ fun v : ℂ => v - z) (z + w) :=
        DifferentiableAt.comp (z + w) hc' hsub
      have heq : (G ∘ fun v : ℂ => v - z) = f := by ext v; dsimp [G]; ring_nf
      rw [heq] at h_at
      exact hdf h_at
    simp [wirtingerBar, G, fderiv_zero_of_not_differentiableAt hdf,
      fderiv_zero_of_not_differentiableAt hdf']

private def polarUnit (θ : ℝ) : ℂ :=
  Real.cos θ + Real.sin θ * Complex.I

private theorem polarCoord_symm_eq_polarUnit (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = (r : ℂ) * polarUnit θ := by
  simp [polarUnit]

private theorem norm_polarUnit (θ : ℝ) : ‖polarUnit θ‖ = 1 := by
  unfold polarUnit
  rw [Complex.ofReal_cos, Complex.ofReal_sin]
  exact Complex.norm_cos_add_sin_mul_I θ

private theorem polarUnit_ne_zero (θ : ℝ) : polarUnit θ ≠ 0 := by
  intro h
  have := norm_polarUnit θ
  simp [h] at this

private theorem inv_polarUnit (θ : ℝ) :
    (polarUnit θ)⁻¹ = Real.cos θ - Real.sin θ * Complex.I := by
  apply inv_eq_of_mul_eq_one_right
  unfold polarUnit
  calc (Real.cos θ + Real.sin θ * Complex.I) * (Real.cos θ - Real.sin θ * Complex.I)
      = ((Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2) -
          (Real.sin θ : ℂ) ^ 2 * (Complex.I ^ 2 + 1) := by ring
    _ = ((Real.cos θ ^ 2 + Real.sin θ ^ 2 : ℝ) : ℂ) := by simp [Complex.I_sq]
    _ = 1 := by rw [Real.cos_sq_add_sin_sq]; simp

private theorem hasDerivAt_polarUnit (θ : ℝ) :
    HasDerivAt polarUnit (Complex.I * polarUnit θ) θ := by
  unfold polarUnit
  have hc : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ)) ((-Real.sin θ : ℝ) : ℂ) θ :=
    (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt θ (Real.hasDerivAt_cos θ))
  have hs : HasDerivAt (fun t : ℝ => (Real.sin t : ℂ) * Complex.I)
      (((Real.cos θ : ℝ) : ℂ) * Complex.I) θ :=
    (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt θ (Real.hasDerivAt_sin θ)).mul_const Complex.I
  convert hc.add hs using 1
  rw [Complex.ofReal_neg]
  linear_combination (Real.sin θ : ℂ) * Complex.I_sq

private theorem polarUnit_pi_eq_neg_pi : polarUnit Real.pi = polarUnit (-Real.pi) := by
  simp [polarUnit]

/-- Core `z = 0` Cauchy–Green formula: for `F ∈ C¹_c(ℂ)`, `w ↦ ∂̄F(w) / w` is integrable on `ℂ`
and `F 0 = -(1 / π) ∫ w, ∂̄F(w) / w`. -/
private theorem cauchy_green_at_zero {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hsupp : HasCompactSupport F) :
    Integrable (fun w : ℂ => wirtingerBar F w / w) volume ∧
      F 0 = -(1 / (Real.pi : ℂ)) * ∫ w : ℂ, wirtingerBar F w / w := by
  obtain ⟨R₀, hR₀⟩ := hsupp.isBounded.subset_ball (0 : ℂ)
  let R : ℝ := max R₀ 1
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right R₀ 1)
  have hsupp_ball : tsupport F ⊆ Metric.ball (0 : ℂ) R :=
    hR₀.trans (Metric.ball_subset_ball (le_max_left R₀ 1))
  have hF_zero_out : ∀ w : ℂ, R ≤ ‖w‖ → F w = 0 := by
    intro w hw
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have hlt : ‖w‖ < R := by simpa using hsupp_ball hmem
    linarith
  have hwirt_zero_out : ∀ w : ℂ, R ≤ ‖w‖ → wirtingerBar F w = 0 := by
    intro w hw
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have hlt : ‖w‖ < R := by simpa using hsupp_ball (tsupport_wirtingerBar_subset hmem)
    linarith
  have hwirt_cont : Continuous (wirtingerBar F) := continuous_wirtingerBar hF
  obtain ⟨M, hM_bound⟩ := (hasCompactSupport_wirtingerBar hsupp).exists_bound_of_continuous hwirt_cont
  have hM_nonneg : 0 ≤ M := le_trans (norm_nonneg _) (hM_bound 0)
  let K₀ : ℂ → ℂ := fun w => wirtingerBar F w / w
  let H : ℝ × ℝ → ℂ := fun p => (polarUnit p.2)⁻¹ * wirtingerBar F ((p.1 : ℂ) * polarUnit p.2)
  have hH_cont : Continuous H := by
    refine Continuous.mul ?_ ?_
    · refine Continuous.inv₀ ?_ (fun p => polarUnit_ne_zero p.2)
      unfold polarUnit
      fun_prop
    · refine hwirt_cont.comp ?_
      unfold polarUnit
      fun_prop
  have hH_norm : ∀ p : ℝ × ℝ, ‖H p‖ ≤ M := by
    intro p
    dsimp [H]
    rw [norm_mul, norm_inv, norm_polarUnit, inv_one, one_mul]
    exact hM_bound _
  have hH_out : ∀ p : ℝ × ℝ, R ≤ p.1 → H p = 0 := by
    intro p hp
    dsimp [H]
    have hnorm : R ≤ ‖(p.1 : ℂ) * polarUnit p.2‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hR_pos hp),
        norm_polarUnit, mul_one]
      exact hp
    rw [hwirt_zero_out _ hnorm, mul_zero]
  have hpolar_id : ∀ p ∈ polarCoord.target,
      p.1 • K₀ (Complex.polarCoord.symm p) = H p := by
    rintro ⟨r, θ⟩ ⟨hr : 0 < r, _⟩
    change r • (wirtingerBar F (Complex.polarCoord.symm (r, θ)) / Complex.polarCoord.symm (r, θ)) =
      (polarUnit θ)⁻¹ * wirtingerBar F ((r : ℂ) * polarUnit θ)
    rw [Complex.real_smul, polarCoord_symm_eq_polarUnit]
    have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have he_ne : polarUnit θ ≠ 0 := polarUnit_ne_zero θ
    field_simp [hr_ne, he_ne]
  -- (1) Integrability of `K₀` via polar coordinates
  let box0 : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi
  have hbox0_meas : MeasurableSet box0 := measurableSet_Ioo.prod measurableSet_Ioo
  have hbox0_fin : volume box0 < ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top measure_Ioo_lt_top measure_Ioo_lt_top
  have hH_int_box0 : IntegrableOn H box0 volume :=
    (hH_cont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hK₀_int : Integrable K₀ volume := by
    have hmeas : AEStronglyMeasurable K₀ volume :=
      (hwirt_cont.measurable.div measurable_id).aestronglyMeasurable
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, ← Complex.lintegral_comp_polarCoord_symm (fun w => ‖K₀ w‖ₑ)]
    have hcongr : ∀ p ∈ polarCoord.target,
        ENNReal.ofReal p.1 • ‖K₀ (Complex.polarCoord.symm p)‖ₑ =
          box0.indicator (fun q => ‖H q‖ₑ) p := by
      rintro ⟨r, θ⟩ hp
      have hr : 0 < r := hp.1
      have hθ : θ ∈ Set.Ioo (-Real.pi) Real.pi := hp.2
      have h1 : ENNReal.ofReal r • ‖K₀ (Complex.polarCoord.symm (r, θ))‖ₑ = ‖H (r, θ)‖ₑ := by
        rw [← hpolar_id (r, θ) hp, enorm_smul, Real.enorm_eq_ofReal hr.le, smul_eq_mul]
      rw [h1]
      by_cases hrR : r < R
      · have hmem : (r, θ) ∈ box0 := ⟨⟨hr, hrR⟩, hθ⟩
        simp [hmem]
      · have hnot : (r, θ) ∉ box0 := fun hm => hrR hm.1.2
        simp [hnot, hH_out (r, θ) (le_of_not_gt hrR)]
    rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hcongr]
    calc ∫⁻ p in polarCoord.target, box0.indicator (fun q => ‖H q‖ₑ) p
        ≤ ∫⁻ p, box0.indicator (fun q => ‖H q‖ₑ) p := setLIntegral_le_lintegral _ _
      _ = ∫⁻ p in box0, ‖H p‖ₑ := lintegral_indicator hbox0_meas _
      _ < ⊤ := hH_int_box0.2
  -- (2) Express `∫ w, K₀ w` as `∫ p in box0, H p`
  have hint_eq_box0 : (∫ w : ℂ, K₀ w) = ∫ p in box0, H p := by
    rw [← Complex.integral_comp_polarCoord_symm K₀]
    have hsub : box0 ⊆ polarCoord.target :=
      Set.prod_mono (fun _ hr => hr.1) Subset.rfl
    have heq_ind : ∀ p : ℝ × ℝ,
        polarCoord.target.indicator (fun q => q.1 • K₀ (Complex.polarCoord.symm q)) p =
          box0.indicator H p := by
      intro ⟨r, θ⟩
      by_cases hp : (r, θ) ∈ polarCoord.target
      · rw [indicator_of_mem hp, hpolar_id (r, θ) hp]
        by_cases hrR : r < R
        · have hmem : (r, θ) ∈ box0 := ⟨⟨hp.1, hrR⟩, hp.2⟩
          rw [indicator_of_mem hmem]
        · have hnot : (r, θ) ∉ box0 := fun hm => hrR hm.1.2
          rw [indicator_of_notMem hnot, hH_out (r, θ) (le_of_not_gt hrR)]
      · have hnot : (r, θ) ∉ box0 := fun hm => hp (hsub hm)
        rw [indicator_of_notMem hp, indicator_of_notMem hnot]
    rw [← integral_indicator polarCoord.open_target.measurableSet,
      ← integral_indicator hbox0_meas]
    exact integral_congr_ae (Eventually.of_forall heq_ind)
  -- (3) Polar partial-derivative identity on `(0, ∞) × ℝ`
  let g : ℝ → ℝ → ℂ := fun r θ => F ((r : ℂ) * polarUnit θ)
  let dr_g : ℝ → ℝ → ℂ := fun r θ => fderiv ℝ F ((r : ℂ) * polarUnit θ) (polarUnit θ)
  let dθ_g : ℝ → ℝ → ℂ := fun r θ =>
    fderiv ℝ F ((r : ℂ) * polarUnit θ) ((r : ℂ) * (Complex.I * polarUnit θ))
  have hdr_has : ∀ r θ : ℝ, HasDerivAt (fun s => g s θ) (dr_g r θ) r := by
    intro r θ
    have hF_diff : DifferentiableAt ℝ F ((r : ℂ) * polarUnit θ) :=
      (hF.differentiable one_ne_zero).differentiableAt
    have h_in : HasDerivAt (fun s : ℝ => (s : ℂ) * polarUnit θ) (polarUnit θ) r := by
      simpa using (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_id r)).mul_const
        (polarUnit θ)
    exact hF_diff.hasFDerivAt.comp_hasDerivAt r h_in
  have hdθ_has : ∀ r θ : ℝ, HasDerivAt (fun t => g r t) (dθ_g r θ) θ := by
    intro r θ
    have hF_diff : DifferentiableAt ℝ F ((r : ℂ) * polarUnit θ) :=
      (hF.differentiable one_ne_zero).differentiableAt
    have h_in : HasDerivAt (fun t : ℝ => (r : ℂ) * polarUnit t)
        ((r : ℂ) * (Complex.I * polarUnit θ)) θ :=
      (hasDerivAt_polarUnit θ).const_mul (r : ℂ)
    exact hF_diff.hasFDerivAt.comp_hasDerivAt θ h_in
  have h2H_decomp : ∀ r θ : ℝ, r ≠ 0 →
      2 * H (r, θ) = dr_g r θ + (Complex.I / (r : ℂ)) * dθ_g r θ := by
    intro r θ hr0
    let L : ℂ →L[ℝ] ℂ := fderiv ℝ F ((r : ℂ) * polarUnit θ)
    have hL_e : L (polarUnit θ) =
        (Real.cos θ : ℂ) * L 1 + (Real.sin θ : ℂ) * L Complex.I := by
      have he : polarUnit θ = Real.cos θ • (1 : ℂ) + Real.sin θ • Complex.I := by
        simp [polarUnit, Complex.real_smul]
      rw [he, L.map_add, L.map_smul, L.map_smul]
      simp [Complex.real_smul]
    have hL_ie : L ((r : ℂ) * (Complex.I * polarUnit θ)) =
        (-(r * Real.sin θ) : ℂ) * L 1 + ((r * Real.cos θ) : ℂ) * L Complex.I := by
      have hie : (r : ℂ) * (Complex.I * polarUnit θ) =
          (-(r * Real.sin θ)) • (1 : ℂ) + (r * Real.cos θ) • Complex.I := by
        unfold polarUnit
        simp only [Complex.real_smul, mul_one, Complex.ofReal_neg, Complex.ofReal_mul]
        linear_combination (r : ℂ) * (Real.sin θ : ℂ) * Complex.I_sq
      rw [hie, L.map_add, L.map_smul, L.map_smul]
      simp [Complex.real_smul]
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0
    dsimp [H, dr_g, dθ_g]
    change 2 * ((polarUnit θ)⁻¹ * ((L 1 + Complex.I * L Complex.I) / 2)) =
      L (polarUnit θ) + (Complex.I / (r : ℂ)) * L ((r : ℂ) * (Complex.I * polarUnit θ))
    rw [inv_polarUnit, hL_e, hL_ie]
    field_simp [hrC]
    linear_combination -(Real.sin θ : ℂ) * L Complex.I * Complex.I_sq
  -- (4) Evaluate on `Ioo ε R ×ˢ Ioo (-π) π` for `0 < ε < R`
  have hdf_cont : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  have hdr_cont : Continuous (fun p : ℝ × ℝ => dr_g p.1 p.2) := by
    dsimp [dr_g]
    have h1 : Continuous (fun p : ℝ × ℝ => fderiv ℝ F ((p.1 : ℂ) * polarUnit p.2)) := by
      refine hdf_cont.comp ?_
      unfold polarUnit; fun_prop
    have h2 : Continuous (fun p : ℝ × ℝ => polarUnit p.2) := by
      unfold polarUnit; fun_prop
    exact h1.clm_apply h2
  have hdθ_cont : Continuous (fun p : ℝ × ℝ => dθ_g p.1 p.2) := by
    dsimp [dθ_g]
    have h1 : Continuous (fun p : ℝ × ℝ => fderiv ℝ F ((p.1 : ℂ) * polarUnit p.2)) := by
      refine hdf_cont.comp ?_
      unfold polarUnit; fun_prop
    have h2 : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * (Complex.I * polarUnit p.2)) := by
      unfold polarUnit; fun_prop
    exact h1.clm_apply h2
  have hpi_le : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hannulus_eval : ∀ ε ∈ Set.Ioo (0 : ℝ) R,
      2 * (∫ p in Set.Ioo ε R ×ˢ Set.Ioo (-Real.pi) Real.pi, H p) =
        - ∫ θ in Set.Ioo (-Real.pi) Real.pi, F ((ε : ℂ) * polarUnit θ) := by
    rintro ε ⟨hε_pos, hεR⟩
    let rect : Set (ℝ × ℝ) := Set.Ioo ε R ×ˢ Set.Ioo (-Real.pi) Real.pi
    let cRect : Set (ℝ × ℝ) := Set.Icc ε R ×ˢ Set.Icc (-Real.pi) Real.pi
    have hrect_sub : rect ⊆ cRect := Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
    have hcRect_comp : IsCompact cRect := isCompact_Icc.prod isCompact_Icc
    let term1 : ℝ × ℝ → ℂ := fun p => dr_g p.1 p.2
    let term2 : ℝ × ℝ → ℂ := fun p => (Complex.I / (p.1 : ℂ)) * dθ_g p.1 p.2
    have hterm1_int : IntegrableOn term1 rect volume :=
      (hdr_cont.continuousOn.integrableOn_compact hcRect_comp).mono_set hrect_sub
    have hterm2_contOn : ContinuousOn term2 cRect := by
      refine ContinuousOn.mul ?_ hdθ_cont.continuousOn
      refine continuousOn_const.div (Complex.continuous_ofReal.comp continuous_fst).continuousOn ?_
      intro p hp
      exact Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le hε_pos hp.1.1).ne'
    have hterm2_int : IntegrableOn term2 rect volume :=
      (hterm2_contOn.integrableOn_compact hcRect_comp).mono_set hrect_sub
    have h2H_on_rect : Set.EqOn (fun p => 2 * H p) (fun p => term1 p + term2 p) rect := by
      rintro ⟨r, θ⟩ ⟨hr, _⟩
      exact h2H_decomp r θ (lt_trans hε_pos hr.1).ne'
    rw [← integral_const_mul,
      setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) h2H_on_rect,
      integral_add hterm1_int hterm2_int]
    -- Angular integral of `term2` vanishes by periodicity (`polarUnit π = polarUnit (-π)`)
    have hint_term2 : (∫ p in rect, term2 p) = 0 := by
      rw [Measure.volume_eq_prod, setIntegral_prod _ hterm2_int]
      refine setIntegral_eq_zero_of_forall_eq_zero fun r _ => ?_
      dsimp [term2]
      rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hpi_le]
      have hdθ_cont_r : Continuous (fun θ : ℝ => dθ_g r θ) :=
        hdθ_cont.comp (continuous_const.prodMk continuous_id)
      have hftc_θ : (∫ θ in (-Real.pi)..Real.pi, dθ_g r θ) = g r Real.pi - g r (-Real.pi) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun θ _ => hdθ_has r θ) (hdθ_cont_r.intervalIntegrable _ _)
      rw [hftc_θ]
      simp [g, polarUnit_pi_eq_neg_pi]
    -- Radial integral of `term1` gives `g R θ - g ε θ = -F(ε * polarUnit θ)`
    have hint_term1 : (∫ p in rect, term1 p) =
        - ∫ θ in Set.Ioo (-Real.pi) Real.pi, F ((ε : ℂ) * polarUnit θ) := by
      have hterm1_swap_int : IntegrableOn (fun q : ℝ × ℝ => term1 q.swap)
          (Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo ε R) (volume.prod volume) := by
        have hc : Continuous (fun q : ℝ × ℝ => term1 q.swap) :=
          hdr_cont.comp continuous_swap
        rw [← Measure.volume_eq_prod]
        exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
          (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
      rw [Measure.volume_eq_prod,
        ← setIntegral_prod_swap (Set.Ioo ε R) (Set.Ioo (-Real.pi) Real.pi) term1,
        setIntegral_prod _ hterm1_swap_int]
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
      dsimp [term1]
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hεR.le]
      have hdr_cont_θ : Continuous (fun r : ℝ => dr_g r θ) :=
        hdr_cont.comp (continuous_id.prodMk continuous_const)
      have hftc_r : (∫ r in ε..R, dr_g r θ) = g R θ - g ε θ :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun r _ => hdr_has r θ) (hdr_cont_θ.intervalIntegrable _ _)
      have hgR : g R θ = 0 := by
        dsimp [g]
        refine hF_zero_out _ ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR_pos,
          norm_polarUnit, mul_one]
      rw [hftc_r, hgR, zero_sub]
    rw [hint_term1, hint_term2, add_zero]
  -- (5) Send `ε → 0⁺` via Dominated Convergence along `ε_n = R / (n + 2)`
  let ε_seq : ℕ → ℝ := fun n => R / ((n : ℝ) + 2)
  have hε_mem : ∀ n : ℕ, ε_seq n ∈ Set.Ioo (0 : ℝ) R := by
    intro n
    dsimp [ε_seq]
    have hden : (1 : ℝ) < (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    exact ⟨by positivity, div_lt_self hR_pos hden⟩
  have hε_tend : Tendsto ε_seq atTop (𝓝 0) := by
    dsimp [ε_seq]
    simpa using tendsto_const_nhds.div_atTop
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
  -- LHS limit: `2 * ∫_{rect(ε_n)} H → 2 * ∫_{box0} H = 2 * ∫ K₀`
  have hlhs_tend : Tendsto
      (fun n : ℕ => 2 * ∫ p in Set.Ioo (ε_seq n) R ×ˢ Set.Ioo (-Real.pi) Real.pi, H p)
      atTop (𝓝 (2 * ∫ w : ℂ, K₀ w)) := by
    rw [hint_eq_box0]
    refine Tendsto.const_mul 2 ?_
    let f_n : ℕ → ℝ × ℝ → ℂ := fun n =>
      (Set.Ioo (ε_seq n) R ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator H
    have heq_n : ∀ n : ℕ,
        (∫ p in Set.Ioo (ε_seq n) R ×ˢ Set.Ioo (-Real.pi) Real.pi, H p) = ∫ p, f_n n p :=
      fun n => (integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)).symm
    simp_rw [heq_n, ← integral_indicator hbox0_meas]
    refine tendsto_integral_of_dominated_convergence
      (fun p => box0.indicator (fun _ => M) p) ?_ ?_ ?_ ?_
    · intro n
      exact hH_cont.aestronglyMeasurable.indicator (measurableSet_Ioo.prod measurableSet_Ioo)
    · rw [integrable_indicator_iff hbox0_meas]
      exact integrableOn_const hbox0_fin.ne
    · intro n
      refine Eventually.of_forall fun p => ?_
      have hsub_n : Set.Ioo (ε_seq n) R ×ˢ Set.Ioo (-Real.pi) Real.pi ⊆ box0 :=
        Set.prod_mono (Ioo_subset_Ioo_left (hε_mem n).1.le) Subset.rfl
      by_cases hp : p ∈ Set.Ioo (ε_seq n) R ×ˢ Set.Ioo (-Real.pi) Real.pi
      · simp [f_n, hp, hsub_n hp, hH_norm p]
      · by_cases hp0 : p ∈ box0
        · simp [f_n, hp, hp0, hM_nonneg]
        · simp [f_n, hp, hp0]
    · refine Eventually.of_forall fun p => ?_
      by_cases hp0 : p ∈ box0
      · rw [indicator_of_mem hp0]
        have hev : ∀ᶠ n : ℕ in atTop, ε_seq n < p.1 :=
          hε_tend.eventually (gt_mem_nhds hp0.1.1)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn
        have hmem_n : p ∈ Set.Ioo (ε_seq n) R ×ˢ Set.Ioo (-Real.pi) Real.pi :=
          ⟨⟨hn, hp0.1.2⟩, hp0.2⟩
        simp [f_n, hmem_n]
      · rw [indicator_of_notMem hp0]
        refine tendsto_const_nhds.congr' ?_
        refine Eventually.of_forall fun n => ?_
        have hsub_n : Set.Ioo (ε_seq n) R ×ˢ Set.Ioo (-Real.pi) Real.pi ⊆ box0 :=
          Set.prod_mono (Ioo_subset_Ioo_left (hε_mem n).1.le) Subset.rfl
        have hnot_n : p ∉ Set.Ioo (ε_seq n) R ×ˢ Set.Ioo (-Real.pi) Real.pi :=
          fun hm => hp0 (hsub_n hm)
        simp [f_n, hnot_n]
  -- RHS limit: `- ∫ θ in (-π, π), F(ε_n e^{iθ}) → -(2 π) * F 0`
  obtain ⟨MF, hMF⟩ := hsupp.exists_bound_of_continuous hF.continuous
  have hrhs_tend : Tendsto
      (fun n : ℕ => - ∫ θ in Set.Ioo (-Real.pi) Real.pi, F ((ε_seq n : ℂ) * polarUnit θ))
      atTop (𝓝 (-((2 * Real.pi : ℂ) * F 0))) := by
    refine Tendsto.neg ?_
    let μ_θ := volume.restrict (Set.Ioo (-Real.pi) Real.pi)
    have hfin_θ : μ_θ Set.univ < ⊤ := by
      simp [μ_θ]
    have _ : IsFiniteMeasure μ_θ := ⟨hfin_θ⟩
    have hdom_θ : Tendsto
        (fun n : ℕ => ∫ θ, F ((ε_seq n : ℂ) * polarUnit θ) ∂μ_θ)
        atTop (𝓝 (∫ _ : ℝ, F 0 ∂μ_θ)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => MF) ?_ ?_ ?_ ?_
      · intro n
        have hc : Continuous (fun θ : ℝ => F ((ε_seq n : ℂ) * polarUnit θ)) := by
          refine hF.continuous.comp ?_
          unfold polarUnit; fun_prop
        exact hc.aestronglyMeasurable
      · exact integrable_const MF
      · intro n
        exact Eventually.of_forall fun θ => hMF _
      · refine Eventually.of_forall fun θ => ?_
        have hlim : Tendsto (fun n : ℕ => (ε_seq n : ℂ) * polarUnit θ) atTop (𝓝 0) := by
          simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp hε_tend).mul_const
            (polarUnit θ)
        exact hF.continuous.continuousAt.tendsto.comp hlim
    have hconst_int : (∫ _ : ℝ, F 0 ∂μ_θ) = (2 * Real.pi : ℂ) * F 0 := by
      rw [integral_const, Measure.real_def, Measure.restrict_apply_univ, Real.volume_Ioo,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), Complex.real_smul]
      push_cast
      ring
    rwa [hconst_int] at hdom_θ
  -- Combine LHS and RHS limits
  have hlhs_eq_rhs : (fun n : ℕ =>
      2 * ∫ p in Set.Ioo (ε_seq n) R ×ˢ Set.Ioo (-Real.pi) Real.pi, H p) =
      (fun n : ℕ => - ∫ θ in Set.Ioo (-Real.pi) Real.pi, F ((ε_seq n : ℂ) * polarUnit θ)) :=
    funext fun n => hannulus_eval (ε_seq n) (hε_mem n)
  rw [hlhs_eq_rhs] at hlhs_tend
  have h2_eq : 2 * (∫ w : ℂ, K₀ w) = -((2 * Real.pi : ℂ) * F 0) :=
    tendsto_nhds_unique hlhs_tend hrhs_tend
  refine ⟨hK₀_int, ?_⟩
  dsimp [K₀] at h2_eq
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi_ne]
  linear_combination (1 / 2 : ℂ) * h2_eq

/-- **Lemma 20.3 (Cauchy–Green / Pompeiu Representation Formula, RCA pp. 388–389):**
Let `f : ℂ → ℂ` be a `C¹` function on the plane (`ContDiff ℝ 1 f`) with compact support
(`HasCompactSupport f`). Then for every `z : ℂ`:
1. `ζ ↦ wirtingerBar f ζ / (ζ - z)` is Lebesgue integrable on `ℂ`,
2. `f z = -(1 / π) ∫ ζ : ℂ, wirtingerBar f ζ / (ζ - z)`,
3. Equivalently in planar `(ξ, η)` coordinates (`ζ = ξ + i η`),
   `f z = -(1 / π) ∫ p : ℝ × ℝ, wirtingerBar f (p.1 + p.2 * I) / ((p.1 + p.2 * I) - z)`. -/
theorem theorem20_3 {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (hsupp : HasCompactSupport f) (z : ℂ) :
    Integrable (fun ζ : ℂ => wirtingerBar f ζ / (ζ - z)) volume ∧
      f z = -(1 / (Real.pi : ℂ)) * (∫ ζ : ℂ, wirtingerBar f ζ / (ζ - z)) ∧
      f z = -(1 / (Real.pi : ℂ)) *
        ∫ p : ℝ × ℝ,
          wirtingerBar f ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) /
            (((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) - z) := by
  let F : ℂ → ℂ := fun w => f (z + w)
  have hF_diff : ContDiff ℝ 1 F := hf.comp (contDiff_const.add contDiff_id)
  have hF_supp : HasCompactSupport F := hsupp.comp_homeomorph (Homeomorph.addLeft z)
  obtain ⟨hK₀_int, hF0_eq⟩ := cauchy_green_at_zero hF_diff hF_supp
  have h_shift : (fun w : ℂ => wirtingerBar f (z + w) / ((z + w) - z)) =
      (fun w : ℂ => wirtingerBar F w / w) := by
    ext w
    rw [wirtingerBar_comp_add_left, add_sub_cancel_left]
  -- Pull back integrability and integral from `F` via `ζ ↦ ζ - z` (`Homeomorph.subRight z`)
  have h_int : Integrable (fun ζ : ℂ => wirtingerBar f ζ / (ζ - z)) volume := by
    have hmp : MeasurePreserving (fun ζ : ℂ => ζ - z) volume volume :=
      measurePreserving_sub_right volume z
    have hemb : MeasurableEmbedding (fun ζ : ℂ => ζ - z) :=
      (Homeomorph.subRight z).measurableEmbedding
    have hcomp_int : Integrable ((fun w : ℂ => wirtingerBar F w / w) ∘ (fun ζ : ℂ => ζ - z))
        volume := (hmp.integrable_comp_emb hemb).mpr hK₀_int
    refine hcomp_int.congr (Eventually.of_forall fun ζ => ?_)
    dsimp [Function.comp]
    rw [wirtingerBar_comp_add_left, add_sub_cancel]
  have h_val : (∫ ζ : ℂ, wirtingerBar f ζ / (ζ - z)) = ∫ w : ℂ, wirtingerBar F w / w := by
    rw [← integral_add_left_eq_self (fun ζ : ℂ => wirtingerBar f ζ / (ζ - z)) z]
    exact integral_congr_ae (Eventually.of_forall fun w => congr_fun h_shift w)
  have hfz : f z = -(1 / (Real.pi : ℂ)) * ∫ ζ : ℂ, wirtingerBar f ζ / (ζ - z) := by
    have hF0 : F 0 = f z := by simp [F]
    rw [h_val, ← hF0, hF0_eq]
  have h_prod : (∫ ζ : ℂ, wirtingerBar f ζ / (ζ - z)) =
      ∫ p : ℝ × ℝ,
        wirtingerBar f ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) /
          (((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) - z) := by
    rw [← (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
      Complex.measurableEquivRealProd.symm.measurableEmbedding]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    have hp : (Complex.measurableEquivRealProd.symm p : ℂ) =
        (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
      simp [Complex.measurableEquivRealProd, Complex.equivRealProdCLM_symm_apply]
    simp [hp]
  exact ⟨h_int, hfz, h_prod ▸ hfz⟩

end Node20_3

section Node20_4
open Metric Set Filter Function Complex RudinRCA.Chapter13
open scoped Topology BigOperators OnePoint BoundedContinuousFunction

/-! ### Node 20.4: Tietze's Extension Theorem on Locally Compact Hausdorff Spaces -/

/-- **Theorem 20.4 (Tietze's Extension Theorem with Compact Support and Norm Preservation,
RCA pp. 389–390):**
Let `K` be a compact subset of a locally compact Hausdorff space `X` (without assuming
`NormalSpace X`). Every `f : C(K, ℂ)` extends to a continuous function `F : C(X, ℂ)` with compact
support such that `‖F x‖ ≤ ‖f‖` everywhere on `X` and `sup_{x ∈ X} ‖F x‖ = ‖f‖`. -/
theorem theorem20_4 {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    {K : Set X} (hK : IsCompact K) (f : C(K, ℂ)) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∃ F : C(X, ℂ),
      HasCompactSupport F ∧
      (∀ x : K, F x = f x) ∧
      (∀ x : X, ‖F x‖ ≤ ‖f‖) ∧
      sSup (Set.range (fun x : X => ‖F x‖)) = ‖f‖ := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  by_cases hf0 : ‖f‖ = 0
  · refine ⟨0, HasCompactSupport.zero, ?_, ?_, ?_⟩
    · intro x
      have hx0 : ‖f x‖ ≤ 0 := hf0 ▸ f.norm_coe_le_norm x
      exact (norm_le_zero_iff.mp hx0).symm
    · intro x
      simp [hf0]
    · rw [hf0]
      rcases isEmpty_or_nonempty X with hEmpty | hNonempty
      · have hrange : Set.range (fun x : X => ‖(0 : C(X, ℂ)) x‖) = ∅ :=
          Set.range_eq_empty_iff.mpr hEmpty
        rw [hrange, Real.sSup_empty]
      · have hrange : Set.range (fun x : X => ‖(0 : C(X, ℂ)) x‖) = {0} := by
          ext r; simp
        rw [hrange, csSup_singleton]
  · have hK_nonempty : Nonempty K := by
      by_contra hEmpty
      rw [not_nonempty_iff] at hEmpty
      have h0 : ‖f‖ = 0 := by
        rw [ContinuousMap.norm_eq_iSup_norm]
        simp
      exact hf0 h0
    let x₀ : K := Classical.arbitrary K
    have _ : Nonempty X := ⟨(x₀ : X)⟩
    -- Embed `K` into the compact Hausdorff (hence normal) one-point compactification `OnePoint X`.
    let emb : K → OnePoint X := fun x => ((x : X) : OnePoint X)
    have hemb : Topology.IsEmbedding emb :=
      OnePoint.isOpenEmbedding_coe.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    let K' : Set (OnePoint X) := Set.range emb
    have hK'_eq : K' = ((↑) : X → OnePoint X) '' K := by
      ext p; simp [K', emb]
    have hK'_comp : IsCompact K' := hK'_eq ▸ hK.image OnePoint.continuous_coe
    have hK'_closed : IsClosed K' := hK'_comp.isClosed
    let _ : CompactSpace K' := isCompact_iff_compactSpace.mp hK'_comp
    let e : K ≃ₜ K' := hemb.toHomeomorph
    let eSymmC : C(K', K) := ⟨e.symm, e.symm.continuous⟩
    let f' : K' →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact (f.comp eSymmC)
    have hf'_norm : ‖f'‖ ≤ ‖f‖ := by
      refine (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr fun y => ?_
      simpa [f', eSymmC] using f.norm_coe_le_norm (e.symm y)
    obtain ⟨G, hG_norm, hG_rest⟩ :=
      BoundedContinuousFunction.exists_norm_eq_domRestrict_eq hK'_closed ℂ f'
    obtain ⟨φ, hφ_one, _, hφ_supp, hφ_Icc⟩ :=
      exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
    let F : C(X, ℂ) :=
      ⟨fun x => (φ x : ℂ) * G (x : OnePoint X),
        (Complex.continuous_ofReal.comp φ.continuous).mul
          (G.continuous.comp OnePoint.continuous_coe)⟩
    have hF_supp : HasCompactSupport F := by
      have hφC : HasCompactSupport (fun x : X => (φ x : ℂ)) :=
        hφ_supp.comp_left Complex.ofReal_zero
      exact hφC.mul_right
    have hF_ext : ∀ x : K, F x = f x := by
      intro x
      have hφx : φ (x : X) = 1 := hφ_one x.2
      let y : K' := e x
      have hy_val : (y : OnePoint X) = ((x : X) : OnePoint X) := rfl
      have hGy : G (y : OnePoint X) = f' y :=
        congr_arg (fun h : K' →ᵇ ℂ => h y) hG_rest
      have hf'y : f' y = f x := by
        change f (e.symm (e x)) = f x
        rw [e.symm_apply_apply]
      change (φ (x : X) : ℂ) * G ((x : X) : OnePoint X) = f x
      rw [hφx, Complex.ofReal_one, one_mul, ← hy_val, hGy, hf'y]
    have hF_le : ∀ x : X, ‖F x‖ ≤ ‖f‖ := by
      intro x
      change ‖(φ x : ℂ) * G (x : OnePoint X)‖ ≤ ‖f‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ_Icc x).1]
      calc φ x * ‖G (x : OnePoint X)‖
          ≤ 1 * ‖G‖ := mul_le_mul (hφ_Icc x).2 (G.norm_coe_le_norm _) (norm_nonneg _) zero_le_one
        _ = ‖f'‖ := by rw [one_mul, hG_norm]
        _ ≤ ‖f‖ := hf'_norm
    have hF_sup : sSup (Set.range (fun x : X => ‖F x‖)) = ‖f‖ := by
      have hbdd : BddAbove (Set.range (fun x : X => ‖F x‖)) :=
        ⟨‖f‖, by rintro _ ⟨x, rfl⟩; exact hF_le x⟩
      apply le_antisymm
      · exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact hF_le x)
      · have hsup_nonneg : 0 ≤ sSup (Set.range (fun x : X => ‖F x‖)) :=
          le_trans (norm_nonneg (F x₀)) (le_csSup hbdd ⟨x₀, rfl⟩)
        refine (ContinuousMap.norm_le f hsup_nonneg).mpr fun x => ?_
        rw [← hF_ext x]
        exact le_csSup hbdd ⟨(x : X), rfl⟩
    exact ⟨F, hF_supp, hF_ext, hF_le, hF_sup⟩

/-- Unbundled `ContinuousOn` form of Theorem 20.4: every `f₀ : X → ℂ` continuous on a compact
subset `K` of a locally compact Hausdorff space `X` extends to `F : C(X, ℂ)` with compact support
and the same supremum norm. -/
theorem theorem20_4_continuousOn {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [T2Space X] {K : Set X} (hK : IsCompact K) {f₀ : X → ℂ} (hf₀ : ContinuousOn f₀ K) :
    ∃ F : C(X, ℂ),
      HasCompactSupport F ∧
      Set.EqOn F f₀ K ∧
      (∀ x : X, ‖F x‖ ≤ sSup ((fun y => ‖f₀ y‖) '' K)) ∧
      sSup (Set.range (fun x : X => ‖F x‖)) = sSup ((fun y => ‖f₀ y‖) '' K) := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : C(K, ℂ) := ⟨K.domRestrict f₀, continuousOn_iff_continuous_domRestrict.mp hf₀⟩
  have hnorm_eq : ‖f‖ = sSup ((fun y => ‖f₀ y‖) '' K) := by
    rw [ContinuousMap.norm_eq_iSup_norm]
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · have _ : IsEmpty (∅ : Set X) := Set.isEmpty_coe_sort.mpr rfl
      simp [Real.sSup_empty]
    · rw [← sSup_range]
      congr 1
      ext r
      simp only [mem_range, Subtype.exists, mem_image]
      exact ⟨fun ⟨a, ha, hr⟩ => ⟨a, ha, hr⟩, fun ⟨a, ha, hr⟩ => ⟨a, ha, hr⟩⟩
  obtain ⟨F, hF_supp, hF_ext, hF_le, hF_sup⟩ := theorem20_4 hK f
  refine ⟨F, hF_supp, fun x hx => hF_ext ⟨x, hx⟩, ?_, ?_⟩
  · simpa only [hnorm_eq] using hF_le
  · simpa only [hnorm_eq] using hF_sup

end Node20_4

section Node20_5
open Metric Set Filter Function Complex MeasureTheory RudinRCA.Chapter13
open scoped Topology BigOperators OnePoint Convolution Interval

/-! ### Node 20.5: Mergelyan's Theorem -/

/-! #### 1. Modulus of Continuity on `ℂ` for Compactly Supported Continuous Functions -/

private def modulusOfCont (f₀ : C(ℂ, ℂ)) (δ : ℝ) : ℝ :=
  sSup {t : ℝ | ∃ z₁ z₂ : ℂ, ‖z₁ - z₂‖ ≤ δ ∧ t = ‖f₀ z₁ - f₀ z₂‖}

private theorem bddAbove_modulusSet {f₀ : C(ℂ, ℂ)} (hsupp : HasCompactSupport f₀) (δ : ℝ) :
    BddAbove {t : ℝ | ∃ z₁ z₂ : ℂ, ‖z₁ - z₂‖ ≤ δ ∧ t = ‖f₀ z₁ - f₀ z₂‖} := by
  obtain ⟨M, hM⟩ := hsupp.exists_bound_of_continuous f₀.continuous
  refine ⟨2 * M, ?_⟩
  rintro t ⟨z₁, z₂, _, rfl⟩
  calc ‖f₀ z₁ - f₀ z₂‖ ≤ ‖f₀ z₁‖ + ‖f₀ z₂‖ := norm_sub_le _ _
    _ ≤ M + M := add_le_add (hM z₁) (hM z₂)
    _ = 2 * M := by ring

private theorem modulusOfCont_nonneg {f₀ : C(ℂ, ℂ)} (hsupp : HasCompactSupport f₀)
    {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ modulusOfCont f₀ δ := by
  refine le_csSup_of_le (bddAbove_modulusSet hsupp δ) ⟨0, 0, by simpa using hδ, by simp⟩ le_rfl

private theorem norm_sub_le_modulusOfCont {f₀ : C(ℂ, ℂ)} (hsupp : HasCompactSupport f₀)
    {δ : ℝ} {z₁ z₂ : ℂ} (hz : ‖z₁ - z₂‖ ≤ δ) :
    ‖f₀ z₁ - f₀ z₂‖ ≤ modulusOfCont f₀ δ :=
  le_csSup (bddAbove_modulusSet hsupp δ) ⟨z₁, z₂, hz, rfl⟩

private theorem tendsto_modulusOfCont_zero {f₀ : C(ℂ, ℂ)} (hsupp : HasCompactSupport f₀) :
    Tendsto (modulusOfCont f₀) (𝓝[>] 0) (𝓝 0) := by
  have huc : UniformContinuous f₀ := hsupp.uniformContinuous_of_continuous f₀.continuous
  rw [Metric.uniformContinuous_iff] at huc
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := huc (ε / 2) (half_pos hε)
  have hmem : Set.Ioo (0 : ℝ) (δ₀ / 2) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (half_pos hδ₀_pos)
  filter_upwards [hmem] with δ ⟨hδ_pos, hδ_lt⟩
  have hnonneg : 0 ≤ modulusOfCont f₀ δ := modulusOfCont_nonneg hsupp hδ_pos.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  have hle : modulusOfCont f₀ δ ≤ ε / 2 := by
    refine csSup_le ⟨0, 0, 0, by simpa using hδ_pos.le, by simp⟩ ?_
    rintro t ⟨z₁, z₂, hz, rfl⟩
    have hlt : dist z₁ z₂ < δ₀ := by
      rw [dist_eq_norm]
      linarith
    exact (dist_eq_norm (f₀ z₁) (f₀ z₂) ▸ (hδ₀ hlt).le)
  linarith

/-! #### 2. Radially Symmetric Smooth Mollifier and Convolution Estimates -/

private def φ_raw (z : ℂ) : ℝ :=
  expNegInvGlue (1 - 4 * (z.re ^ 2 + z.im ^ 2))

private theorem φ_raw_eq_norm (z : ℂ) :
    φ_raw z = expNegInvGlue (1 - 4 * ‖z‖ ^ 2) := by
  unfold φ_raw
  have hsq : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hsq]

private theorem contDiff_φ_raw {n : ℕ∞} : ContDiff ℝ n φ_raw := by
  have hpoly : ContDiff ℝ n (fun z : ℂ => 1 - 4 * (z.re ^ 2 + z.im ^ 2)) := by
    change ContDiff ℝ n
      (fun z : ℂ => 1 - 4 * ((Complex.reCLM z) ^ 2 + (Complex.imCLM z) ^ 2))
    fun_prop
  exact expNegInvGlue.contDiff.comp hpoly

private theorem φ_raw_nonneg (z : ℂ) : 0 ≤ φ_raw z :=
  expNegInvGlue.nonneg _

private theorem φ_raw_zero_of_le_norm {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) : φ_raw z = 0 := by
  rw [φ_raw_eq_norm]
  apply expNegInvGlue.zero_of_nonpos
  have hsq : (1 / 2 : ℝ) ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hz 2
  linarith

private theorem hasCompactSupport_φ_raw : HasCompactSupport φ_raw := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) (1 / 2)) ?_
  intro z hz
  rw [Function.mem_support] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hgt
  push Not at hgt
  exact hz (φ_raw_zero_of_le_norm hgt.le)

private theorem integral_φ_raw_pos : 0 < ∫ w : ℂ, φ_raw w := by
  have hint : Integrable φ_raw volume :=
    (contDiff_φ_raw (n := 1)).continuous.integrable_of_hasCompactSupport hasCompactSupport_φ_raw
  let B₄ : Set ℂ := Metric.closedBall (0 : ℂ) (1 / 4)
  have hB₄_meas : MeasurableSet B₄ := measurableSet_closedBall
  have hc_pos : 0 < expNegInvGlue (3 / 4) := expNegInvGlue.pos_of_pos (by norm_num)
  have hlow_on_B₄ : ∀ w ∈ B₄, expNegInvGlue (3 / 4) ≤ φ_raw w := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [φ_raw_eq_norm]
    apply expNegInvGlue.monotone
    have hsq : ‖w‖ ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    linarith
  have hvol_pos : 0 < volume.real B₄ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos
      ((Metric.measure_ball_pos volume (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)).trans_le
        (measure_mono Metric.ball_subset_closedBall)).ne'
      (ProperSpace.isCompact_closedBall (0 : ℂ) (1 / 4)).measure_lt_top.ne
  calc 0 < volume.real B₄ * expNegInvGlue (3 / 4) := mul_pos hvol_pos hc_pos
    _ = ∫ _ in B₄, expNegInvGlue (3 / 4) := by simp [smul_eq_mul]
    _ ≤ ∫ w in B₄, φ_raw w := by
          refine setIntegral_mono_on (integrableOn_const (hs := (ProperSpace.isCompact_closedBall
            (0 : ℂ) (1 / 4)).measure_lt_top.ne)) hint.integrableOn hB₄_meas hlow_on_B₄
    _ ≤ ∫ w : ℂ, φ_raw w :=
          setIntegral_le_integral hint (Eventually.of_forall φ_raw_nonneg)

private def φ_rad (z : ℂ) : ℝ :=
  φ_raw z / ∫ w : ℂ, φ_raw w

private theorem contDiff_φ_rad {n : ℕ∞} : ContDiff ℝ n φ_rad :=
  contDiff_φ_raw.div_const _

private theorem φ_rad_nonneg (z : ℂ) : 0 ≤ φ_rad z :=
  div_nonneg (φ_raw_nonneg z) integral_φ_raw_pos.le

private theorem φ_rad_zero_of_le_norm {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) : φ_rad z = 0 := by
  simp [φ_rad, φ_raw_zero_of_le_norm hz]

private theorem φ_rad_eq_of_norm_eq {z₁ z₂ : ℂ} (h : ‖z₁‖ = ‖z₂‖) : φ_rad z₁ = φ_rad z₂ := by
  simp [φ_rad, φ_raw_eq_norm, h]

private theorem hasCompactSupport_φ_rad : HasCompactSupport φ_rad := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) (1 / 2)) ?_
  intro z hz
  rw [Function.mem_support] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hgt
  push Not at hgt
  exact hz (φ_rad_zero_of_le_norm hgt.le)

private theorem integral_φ_rad : ∫ w : ℂ, φ_rad w = 1 := by
  unfold φ_rad
  rw [integral_div, div_self integral_φ_raw_pos.ne']

private def C_mollifier : ℝ :=
  ∫ u : ℂ, ‖fderiv ℝ φ_rad u‖

private theorem C_mollifier_nonneg : 0 ≤ C_mollifier :=
  integral_nonneg fun _ => norm_nonneg _

private def mollifierKernel (δ : ℝ) (w : ℂ) : ℝ :=
  δ⁻¹ ^ 2 * φ_rad (δ⁻¹ • w)

private theorem contDiff_mollifierKernel {δ : ℝ} {n : ℕ∞} :
    ContDiff ℝ n (mollifierKernel δ) := by
  unfold mollifierKernel
  have hlin : ContDiff ℝ n (fun w : ℂ => δ⁻¹ • w) :=
    (δ⁻¹ • ContinuousLinearMap.id ℝ ℂ).contDiff
  exact contDiff_const.mul (contDiff_φ_rad.comp hlin)

private theorem mollifierKernel_nonneg {δ : ℝ} (w : ℂ) : 0 ≤ mollifierKernel δ w :=
  mul_nonneg (sq_nonneg _) (φ_rad_nonneg _)

private theorem mollifierKernel_zero_of_le_norm {δ : ℝ} (hδ : 0 < δ) {w : ℂ}
    (hw : δ / 2 ≤ ‖w‖) : mollifierKernel δ w = 0 := by
  unfold mollifierKernel
  have hnorm : 1 / 2 ≤ ‖δ⁻¹ • w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)]
    calc (1 / 2 : ℝ) = δ⁻¹ * (δ / 2) := by field_simp [hδ.ne']
      _ ≤ δ⁻¹ * ‖w‖ := mul_le_mul_of_nonneg_left hw (inv_pos.mpr hδ).le
  rw [φ_rad_zero_of_le_norm hnorm, mul_zero]

private theorem hasCompactSupport_mollifierKernel {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (mollifierKernel δ) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) (δ / 2)) ?_
  intro w hw
  rw [Function.mem_support] at hw
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hgt
  push Not at hgt
  exact hw (mollifierKernel_zero_of_le_norm hδ hgt.le)

private theorem integral_mollifierKernel {δ : ℝ} (hδ : 0 < δ) :
    ∫ w : ℂ, mollifierKernel δ w = 1 := by
  unfold mollifierKernel
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume φ_rad δ⁻¹ (hR := (inv_pos.mpr hδ).le),
    Complex.finrank_real_complex, integral_φ_rad, smul_eq_mul, mul_one]
  field_simp [hδ.ne']

private theorem fderiv_mollifierKernel {δ : ℝ} (w : ℂ) :
    fderiv ℝ (mollifierKernel δ) w = (δ⁻¹ ^ 3) • fderiv ℝ φ_rad (δ⁻¹ • w) := by
  have h1 : HasFDerivAt (fun x : ℂ => δ⁻¹ • x) (δ⁻¹ • ContinuousLinearMap.id ℝ ℂ) w :=
    (δ⁻¹ • ContinuousLinearMap.id ℝ ℂ).hasFDerivAt
  have h2 : HasFDerivAt φ_rad (fderiv ℝ φ_rad (δ⁻¹ • w)) (δ⁻¹ • w) :=
    ((contDiff_φ_rad (n := 1)).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have h3 : HasFDerivAt (mollifierKernel δ)
      (δ⁻¹ ^ 2 • ((fderiv ℝ φ_rad (δ⁻¹ • w)).comp (δ⁻¹ • ContinuousLinearMap.id ℝ ℂ))) w :=
    (h2.comp w h1).const_smul (δ⁻¹ ^ 2)
  rw [h3.fderiv]
  ext v
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring

private theorem integral_norm_fderiv_mollifierKernel {δ : ℝ} (hδ : 0 < δ) :
    ∫ w : ℂ, ‖fderiv ℝ (mollifierKernel δ) w‖ = C_mollifier / δ := by
  have hcongr : (fun w : ℂ => ‖fderiv ℝ (mollifierKernel δ) w‖) =
      fun w : ℂ => δ⁻¹ ^ 3 * ‖fderiv ℝ φ_rad (δ⁻¹ • w)‖ := by
    ext w
    rw [fderiv_mollifierKernel, norm_smul, Real.norm_eq_abs,
      abs_of_pos (pow_pos (inv_pos.mpr hδ) 3)]
  rw [hcongr, integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume (fun u => ‖fderiv ℝ φ_rad u‖) δ⁻¹
      (hR := (inv_pos.mpr hδ).le),
    Complex.finrank_real_complex, smul_eq_mul]
  unfold C_mollifier
  field_simp [hδ.ne']

private def convL : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip

private def smoothApprox (f₀ : ℂ → ℂ) (δ : ℝ) : ℂ → ℂ :=
  f₀ ⋆[convL, volume] mollifierKernel δ

private theorem contDiff_smoothApprox {f₀ : C(ℂ, ℂ)} {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ 1 (smoothApprox f₀ δ) :=
  (hasCompactSupport_mollifierKernel hδ).contDiff_convolution_right convL
    f₀.continuous.locallyIntegrable (contDiff_mollifierKernel (n := 1))

private theorem hasCompactSupport_smoothApprox {f₀ : C(ℂ, ℂ)} (hsupp : HasCompactSupport f₀)
    {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (smoothApprox f₀ δ) :=
  hsupp.convolution convL (hasCompactSupport_mollifierKernel hδ)

private theorem smoothApprox_apply {f₀ : C(ℂ, ℂ)} {δ : ℝ} (z : ℂ) :
    smoothApprox f₀ δ z = ∫ w : ℂ, mollifierKernel δ w • f₀ (z - w) := by
  change (∫ u : ℂ, mollifierKernel δ (z - u) • f₀ u) =
    ∫ w : ℂ, mollifierKernel δ w • f₀ (z - w)
  have h := integral_sub_left_eq_self (fun w : ℂ => mollifierKernel δ w • f₀ (z - w)) volume z
  simpa [sub_sub_cancel] using h

private theorem norm_smoothApprox_sub_le {f₀ : C(ℂ, ℂ)} (hsupp : HasCompactSupport f₀)
    {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    ‖smoothApprox f₀ δ z - f₀ z‖ ≤ modulusOfCont f₀ δ := by
  have hk_cont : Continuous (mollifierKernel δ) := (contDiff_mollifierKernel (n := 1)).continuous
  have hint_k : Integrable (mollifierKernel δ) volume :=
    hk_cont.integrable_of_hasCompactSupport (hasCompactSupport_mollifierKernel hδ)
  have hconst_int : ∫ w : ℂ, mollifierKernel δ w • f₀ z = f₀ z := by
    rw [integral_smul_const, integral_mollifierKernel hδ, one_smul]
  have hint_sub : Integrable (fun w : ℂ => mollifierKernel δ w • f₀ (z - w)) volume := by
    have hcont : Continuous (fun w : ℂ => mollifierKernel δ w • f₀ (z - w)) :=
      hk_cont.smul (f₀.continuous.comp (continuous_const.sub continuous_id))
    have hc : HasCompactSupport (fun w : ℂ => mollifierKernel δ w • f₀ (z - w)) := by
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) (δ / 2)) ?_
      intro w hw
      rw [Function.mem_support] at hw
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hgt; push Not at hgt
      exact hw (by simp [mollifierKernel_zero_of_le_norm hδ hgt.le])
    exact hcont.integrable_of_hasCompactSupport hc
  rw [smoothApprox_apply, ← hconst_int, ← integral_sub hint_sub (hint_k.smul_const (f₀ z))]
  have hpoint : ∀ w : ℂ,
      ‖mollifierKernel δ w • f₀ (z - w) - mollifierKernel δ w • f₀ z‖ ≤
        mollifierKernel δ w * modulusOfCont f₀ δ := by
    intro w
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mollifierKernel_nonneg w)]
    by_cases hw : ‖w‖ ≤ δ / 2
    · refine mul_le_mul_of_nonneg_left ?_ (mollifierKernel_nonneg w)
      refine norm_sub_le_modulusOfCont hsupp ?_
      have hsub : (z - w) - z = -w := by ring
      rw [hsub, norm_neg]
      linarith
    · push Not at hw
      rw [mollifierKernel_zero_of_le_norm hδ hw.le, zero_mul, zero_mul]
  calc ‖∫ w : ℂ, (mollifierKernel δ w • f₀ (z - w) - mollifierKernel δ w • f₀ z)‖
      ≤ ∫ w : ℂ, ‖mollifierKernel δ w • f₀ (z - w) - mollifierKernel δ w • f₀ z‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ w : ℂ, mollifierKernel δ w * modulusOfCont f₀ δ :=
        integral_mono (hint_sub.sub (hint_k.smul_const (f₀ z))).norm
          (hint_k.mul_const _) hpoint
    _ = (∫ w : ℂ, mollifierKernel δ w) * modulusOfCont f₀ δ := integral_mul_const _ _
    _ = modulusOfCont f₀ δ := by rw [integral_mollifierKernel hδ, one_mul]

private theorem norm_wirtingerBar_smoothApprox_le {f₀ : C(ℂ, ℂ)} (hsupp : HasCompactSupport f₀)
    {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    ‖wirtingerBar (smoothApprox f₀ δ) z‖ ≤ C_mollifier * modulusOfCont f₀ δ / δ := by
  have hk_supp := hasCompactSupport_mollifierKernel hδ
  have hk_c1 : ContDiff ℝ 1 (mollifierKernel δ) := contDiff_mollifierKernel (n := 1)
  have hf_loc : LocallyIntegrable f₀ volume := f₀.continuous.locallyIntegrable
  have hfderiv_apply : ∀ v : ℂ,
      fderiv ℝ (smoothApprox f₀ δ) z v =
        ∫ w : ℂ, (fderiv ℝ (mollifierKernel δ) w v) • (f₀ (z - w) - f₀ z) := by
    intro v
    have hd₁ := (hk_supp.hasFDerivAt_convolution_right convL hf_loc hk_c1 z).fderiv
    have happ₁ := convolution_precompR_apply convL hf_loc (hk_supp.fderiv ℝ)
      (hk_c1.continuous_fderiv one_ne_zero) z v
    have hval₁ : fderiv ℝ (smoothApprox f₀ δ) z v =
        ∫ w : ℂ, (fderiv ℝ (mollifierKernel δ) w v) • f₀ (z - w) := by
      unfold smoothApprox
      rw [hd₁, happ₁]
      change (∫ u : ℂ, (fderiv ℝ (mollifierKernel δ) (z - u) v) • f₀ u) = _
      have h := integral_sub_left_eq_self
        (fun w : ℂ => (fderiv ℝ (mollifierKernel δ) w v) • f₀ (z - w)) volume z
      simpa [sub_sub_cancel] using h
    let cfun : ℂ → ℂ := fun _ => f₀ z
    have hc_loc : LocallyIntegrable cfun volume := continuous_const.locallyIntegrable
    have hcfun_conv : (cfun ⋆[convL, volume] mollifierKernel δ) = cfun := by
      ext x
      change (∫ u : ℂ, mollifierKernel δ (x - u) • f₀ z) = f₀ z
      have h := integral_sub_left_eq_self (fun w : ℂ => mollifierKernel δ w • f₀ z) volume x
      rw [h, integral_smul_const, integral_mollifierKernel hδ, one_smul]
    have hd₂ := (hk_supp.hasFDerivAt_convolution_right convL hc_loc hk_c1 z).fderiv
    have happ₂ := convolution_precompR_apply convL hc_loc (hk_supp.fderiv ℝ)
      (hk_c1.continuous_fderiv one_ne_zero) z v
    have hzero : ∫ w : ℂ, (fderiv ℝ (mollifierKernel δ) w v) • f₀ z = 0 := by
      have h0 : fderiv ℝ (cfun ⋆[convL, volume] mollifierKernel δ) z v = 0 := by
        rw [hcfun_conv]
        simp [cfun]
      rw [hd₂, happ₂] at h0
      change (∫ u : ℂ, (fderiv ℝ (mollifierKernel δ) (z - u) v) • f₀ z) = 0 at h0
      have h := integral_sub_left_eq_self
        (fun w : ℂ => (fderiv ℝ (mollifierKernel δ) w v) • f₀ z) volume z
      rwa [h] at h0
    have hint₁ : Integrable (fun w : ℂ => (fderiv ℝ (mollifierKernel δ) w v) • f₀ (z - w)) volume := by
      have hcont : Continuous (fun w : ℂ => (fderiv ℝ (mollifierKernel δ) w v) • f₀ (z - w)) :=
        ((hk_c1.continuous_fderiv one_ne_zero).clm_apply continuous_const).smul
          (f₀.continuous.comp (continuous_const.sub continuous_id))
      have hcs : HasCompactSupport (fun w : ℂ => (fderiv ℝ (mollifierKernel δ) w v) • f₀ (z - w)) :=
        HasCompactSupport.of_support_subset_isCompact (hk_supp.fderiv ℝ).isCompact fun w hw => by
          rw [Function.mem_support] at hw
          refine subset_tsupport _ ?_
          rw [Function.mem_support]
          intro h0; rw [h0] at hw; simp at hw
      exact hcont.integrable_of_hasCompactSupport hcs
    have hint₂ : Integrable (fun w : ℂ => (fderiv ℝ (mollifierKernel δ) w v) • f₀ z) volume := by
      have hcont : Continuous (fun w : ℂ => (fderiv ℝ (mollifierKernel δ) w v) • f₀ z) :=
        ((hk_c1.continuous_fderiv one_ne_zero).clm_apply continuous_const).smul continuous_const
      have hcs : HasCompactSupport (fun w : ℂ => (fderiv ℝ (mollifierKernel δ) w v) • f₀ z) :=
        HasCompactSupport.of_support_subset_isCompact (hk_supp.fderiv ℝ).isCompact fun w hw => by
          rw [Function.mem_support] at hw
          refine subset_tsupport _ ?_
          rw [Function.mem_support]
          intro h0; rw [h0] at hw; simp at hw
      exact hcont.integrable_of_hasCompactSupport hcs
    rw [hval₁, ← sub_zero (∫ w : ℂ, _), ← hzero, ← integral_sub hint₁ hint₂]
    congr 1; ext w; rw [smul_sub]
  have hfderiv_bound : ∀ v : ℂ, ‖v‖ = 1 →
      ‖fderiv ℝ (smoothApprox f₀ δ) z v‖ ≤ C_mollifier * modulusOfCont f₀ δ / δ := by
    intro v hv
    rw [hfderiv_apply v]
    have hint_norm_fderiv : Integrable (fun w : ℂ => ‖fderiv ℝ (mollifierKernel δ) w‖) volume :=
      (hk_c1.continuous_fderiv one_ne_zero).norm.integrable_of_hasCompactSupport
        (hk_supp.fderiv ℝ).norm
    have hint_diff : Integrable
        (fun w : ℂ => (fderiv ℝ (mollifierKernel δ) w v) • (f₀ (z - w) - f₀ z)) volume := by
      have hcont : Continuous
          (fun w : ℂ => (fderiv ℝ (mollifierKernel δ) w v) • (f₀ (z - w) - f₀ z)) :=
        ((hk_c1.continuous_fderiv one_ne_zero).clm_apply continuous_const).smul
          ((f₀.continuous.comp (continuous_const.sub continuous_id)).sub continuous_const)
      have hcs : HasCompactSupport
          (fun w : ℂ => (fderiv ℝ (mollifierKernel δ) w v) • (f₀ (z - w) - f₀ z)) :=
        HasCompactSupport.of_support_subset_isCompact (hk_supp.fderiv ℝ).isCompact fun w hw => by
          rw [Function.mem_support] at hw
          refine subset_tsupport _ ?_
          rw [Function.mem_support]
          intro h0; rw [h0] at hw; simp at hw
      exact hcont.integrable_of_hasCompactSupport hcs
    have hpoint : ∀ w : ℂ,
        ‖(fderiv ℝ (mollifierKernel δ) w v) • (f₀ (z - w) - f₀ z)‖ ≤
          ‖fderiv ℝ (mollifierKernel δ) w‖ * modulusOfCont f₀ δ := by
      intro w
      rw [norm_smul]
      by_cases hw : ‖w‖ ≤ δ
      · have hop : ‖fderiv ℝ (mollifierKernel δ) w v‖ ≤ ‖fderiv ℝ (mollifierKernel δ) w‖ := by
          simpa [hv] using (fderiv ℝ (mollifierKernel δ) w).le_opNorm v
        have hmod : ‖f₀ (z - w) - f₀ z‖ ≤ modulusOfCont f₀ δ := by
          refine norm_sub_le_modulusOfCont hsupp ?_
          have hsub : (z - w) - z = -w := by ring
          rwa [hsub, norm_neg]
        exact mul_le_mul hop hmod (norm_nonneg _) (norm_nonneg _)
      · push Not at hw
        have hzero_fderiv : fderiv ℝ (mollifierKernel δ) w = 0 := by
          have hev : mollifierKernel δ =ᶠ[𝓝 w] 0 := by
            have hopen : IsOpen {u : ℂ | δ / 2 < ‖u‖} :=
              isOpen_lt continuous_const continuous_norm
            filter_upwards [hopen.mem_nhds (by linarith : δ / 2 < ‖w‖)] with u hu
            exact mollifierKernel_zero_of_le_norm hδ (le_of_lt hu)
          rw [hev.fderiv_eq]
          simp
        rw [hzero_fderiv, zero_apply, norm_zero, zero_mul]
        exact mul_nonneg (norm_nonneg _) (modulusOfCont_nonneg hsupp hδ.le)
    calc ‖∫ w : ℂ, (fderiv ℝ (mollifierKernel δ) w v) • (f₀ (z - w) - f₀ z)‖
        ≤ ∫ w : ℂ, ‖(fderiv ℝ (mollifierKernel δ) w v) • (f₀ (z - w) - f₀ z)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ w : ℂ, ‖fderiv ℝ (mollifierKernel δ) w‖ * modulusOfCont f₀ δ :=
          integral_mono hint_diff.norm (hint_norm_fderiv.mul_const _) hpoint
      _ = (∫ w : ℂ, ‖fderiv ℝ (mollifierKernel δ) w‖) * modulusOfCont f₀ δ :=
          integral_mul_const _ _
      _ = C_mollifier * modulusOfCont f₀ δ / δ := by
          rw [integral_norm_fderiv_mollifierKernel hδ]
          ring
  unfold wirtingerBar
  have hb1 := hfderiv_bound 1 norm_one
  have hbI := hfderiv_bound Complex.I Complex.norm_I
  rw [norm_div, norm_ofNat]
  calc ‖fderiv ℝ (smoothApprox f₀ δ) z 1 + Complex.I * fderiv ℝ (smoothApprox f₀ δ) z Complex.I‖ / 2
      ≤ (‖fderiv ℝ (smoothApprox f₀ δ) z 1‖ +
          ‖Complex.I * fderiv ℝ (smoothApprox f₀ δ) z Complex.I‖) / 2 := by
        gcongr; exact norm_add_le _ _
    _ = (‖fderiv ℝ (smoothApprox f₀ δ) z 1‖ +
          ‖fderiv ℝ (smoothApprox f₀ δ) z Complex.I‖) / 2 := by
        rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ (C_mollifier * modulusOfCont f₀ δ / δ + C_mollifier * modulusOfCont f₀ δ / δ) / 2 := by
        gcongr
    _ = C_mollifier * modulusOfCont f₀ δ / δ := by ring

/-! #### 3. Holomorphic Mean-Value Preservation & Boundary Localization of `∂̄Φ` -/

private theorem smoothApprox_eq_of_closedBall_subset_open {f₀ : C(ℂ, ℂ)} {U : Set ℂ}
    (hU_open : IsOpen U) (hf_holo : DifferentiableOn ℂ f₀ U)
    {δ : ℝ} (hδ : 0 < δ) {z' : ℂ} (hsub : Metric.closedBall z' (δ / 2) ⊆ U) :
    smoothApprox f₀ δ z' = f₀ z' := by
  have hk_cont : Continuous (mollifierKernel δ) := (contDiff_mollifierKernel (n := 1)).continuous
  have hint_k : Integrable (mollifierKernel δ) volume :=
    hk_cont.integrable_of_hasCompactSupport (hasCompactSupport_mollifierKernel hδ)
  have hconst_int : ∫ w : ℂ, mollifierKernel δ w • f₀ z' = f₀ z' := by
    rw [integral_smul_const, integral_mollifierKernel hδ, one_smul]
  have hint_sub : Integrable (fun w : ℂ => mollifierKernel δ w • f₀ (z' - w)) volume := by
    have hcont : Continuous (fun w : ℂ => mollifierKernel δ w • f₀ (z' - w)) :=
      hk_cont.smul (f₀.continuous.comp (continuous_const.sub continuous_id))
    have hc : HasCompactSupport (fun w : ℂ => mollifierKernel δ w • f₀ (z' - w)) := by
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) (δ / 2)) ?_
      intro w hw
      rw [Function.mem_support] at hw
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hgt; push Not at hgt
      exact hw (by simp [mollifierKernel_zero_of_le_norm hδ hgt.le])
    exact hcont.integrable_of_hasCompactSupport hc
  suffices hdiff0 : smoothApprox f₀ δ z' - f₀ z' = 0 from sub_eq_zero.mp hdiff0
  rw [smoothApprox_apply, ← hconst_int, ← integral_sub hint_sub (hint_k.smul_const (f₀ z'))]
  let Ψ : ℂ → ℂ := fun w => mollifierKernel δ w • (f₀ (z' + w) - f₀ z')
  have hneg_eq : (∫ w : ℂ, (mollifierKernel δ w • f₀ (z' - w) - mollifierKernel δ w • f₀ z')) =
      ∫ w : ℂ, Ψ w := by
    rw [← integral_neg_eq_self Ψ volume]
    congr 1; ext w
    dsimp [Ψ]
    have hrad : mollifierKernel δ (-w) = mollifierKernel δ w := by
      unfold mollifierKernel
      rw [smul_neg, φ_rad_eq_of_norm_eq (norm_neg _)]
    rw [hrad]
    have hsub_eq : z' - w = z' + -w := sub_eq_add_neg z' w
    rw [hsub_eq]
    ring
  rw [hneg_eq, ← Complex.integral_comp_polarCoord_symm Ψ]
  let box : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) (δ / 2) ×ˢ Set.Ioo (-Real.pi) Real.pi
  let G : ℝ × ℝ → ℂ := fun p =>
    (p.1 * mollifierKernel δ (p.1 : ℂ)) • (f₀ (circleMap z' p.1 p.2) - f₀ z')
  have hcongr : ∀ p ∈ polarCoord.target,
      p.1 • Ψ (Complex.polarCoord.symm p) = box.indicator G p := by
    rintro ⟨r, θ⟩ ⟨hr : 0 < r, hθ : θ ∈ Set.Ioo (-Real.pi) Real.pi⟩
    dsimp [Ψ, G]
    have hsymm_exp : (Complex.polarCoord.symm (r, θ) : ℂ) = (r : ℂ) * Complex.exp (θ * Complex.I) := by
      simp [Complex.polarCoord_symm_apply, Complex.exp_mul_I]
    have hsymm : z' + Complex.polarCoord.symm (r, θ) = circleMap z' r θ := by
      rw [hsymm_exp, circleMap]
    have hnorm_symm : ‖(Complex.polarCoord.symm (r, θ) : ℂ)‖ = ‖(r : ℂ)‖ := by
      rw [hsymm_exp, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hmk : mollifierKernel δ (Complex.polarCoord.symm (r, θ)) = mollifierKernel δ (r : ℂ) := by
      unfold mollifierKernel
      rw [φ_rad_eq_of_norm_eq]
      rw [norm_smul, norm_smul, hnorm_symm]
    rw [hsymm, hmk, ← mul_assoc, ← Complex.ofReal_mul]
    by_cases hrδ : r < δ / 2
    · have hmem : (r, θ) ∈ box := ⟨⟨hr, hrδ⟩, hθ⟩
      simp [hmem]
    · have hnot : (r, θ) ∉ box := fun hm => hrδ hm.1.2
      have hnorm_r : δ / 2 ≤ ‖(r : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
        linarith
      simp [hnot, mollifierKernel_zero_of_le_norm hδ hnorm_r]
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hcongr]
  have hbox_sub : box ⊆ polarCoord.target := by
    rintro ⟨r, θ⟩ ⟨⟨hr, _⟩, hθ⟩
    exact ⟨hr, hθ⟩
  have hbox_meas : MeasurableSet box := measurableSet_Ioo.prod measurableSet_Ioo
  rw [setIntegral_indicator hbox_meas, inter_eq_right.mpr hbox_sub]
  have hG_cont : Continuous G := by
    dsimp [G]
    refine (Complex.continuous_ofReal.comp
      (continuous_fst.mul (hk_cont.comp (Complex.continuous_ofReal.comp continuous_fst)))).mul ?_
    refine (f₀.continuous.comp ?_).sub continuous_const
    unfold circleMap
    fun_prop
  have hG_int : IntegrableOn G box volume :=
    (hG_cont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [Measure.volume_eq_prod] at hG_int ⊢
  rw [setIntegral_prod G hG_int]
  refine setIntegral_eq_zero_of_forall_eq_zero fun r hr => ?_
  dsimp [G]
  rw [integral_const_mul]
  have hang_zero : ∫ θ in Set.Ioo (-Real.pi) Real.pi, (f₀ (circleMap z' r θ) - f₀ z') = 0 := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    have hper : Function.Periodic (fun θ : ℝ => f₀ (circleMap z' r θ) - f₀ z') (2 * Real.pi) :=
      fun θ => by simp [periodic_circleMap z' r θ]
    have hshift := hper.intervalIntegral_add_eq (-Real.pi) 0
    have hpi : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [hpi, zero_add] at hshift
    rw [hshift]
    have hcb_U : Metric.closedBall z' |r| ⊆ U := by
      rw [abs_of_pos hr.1]
      exact (Metric.closedBall_subset_closedBall hr.2.le).trans hsub
    have hdiff_ball : ∀ w ∈ Metric.ball z' |r| \ (∅ : Set ℂ), DifferentiableAt ℂ f₀ w := by
      intro w hw
      exact (hf_holo w (hcb_U (Metric.ball_subset_closedBall hw.1))).differentiableAt
        (hU_open.mem_nhds (hcb_U (Metric.ball_subset_closedBall hw.1)))
    have havg : Real.circleAverage f₀ z' r = f₀ z' :=
      circleAverage_of_differentiable_on_off_countable Set.countable_empty
        f₀.continuous.continuousOn hdiff_ball
    rw [Real.circleAverage_def] at havg
    have hint1 : IntervalIntegrable (fun θ => f₀ (circleMap z' r θ)) volume 0 (2 * Real.pi) :=
      (f₀.continuous.comp (continuous_circleMap z' r)).intervalIntegrable 0 (2 * Real.pi)
    have hint2 : IntervalIntegrable (fun _ : ℝ => f₀ z') volume 0 (2 * Real.pi) :=
      intervalIntegrable_const
    rw [intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const, sub_zero]
    have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    have hmul : (2 * Real.pi : ℝ) • ((2 * Real.pi : ℝ)⁻¹ •
        ∫ θ in 0..(2 * Real.pi), f₀ (circleMap z' r θ)) = (2 * Real.pi : ℝ) • f₀ z' :=
      congrArg ((2 * Real.pi : ℝ) • ·) havg
    rw [smul_smul, mul_inv_cancel₀ h2pi_ne, one_smul] at hmul
    exact sub_eq_zero.mpr hmul
  rw [hang_zero, mul_zero]

private theorem tsupport_wirtingerBar_smoothApprox_near_compl {K : Set ℂ} {f₀ : C(ℂ, ℂ)}
    (hf_holo : DifferentiableOn ℂ f₀ (interior K)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ x ∈ tsupport (wirtingerBar (smoothApprox f₀ δ)), ∃ w ∈ Kᶜ, ‖x - w‖ < δ := by
  intro x hx
  by_contra hfar
  push Not at hfar
  have hball_K : Metric.ball x δ ⊆ K := by
    intro w hw
    rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hw
    by_contra hwK
    exact lt_irrefl δ (lt_of_le_of_lt (hfar w hwK) hw)
  have hball_int : Metric.ball x δ ⊆ interior K := interior_maximal hball_K Metric.isOpen_ball
  have heq_on : ∀ z' ∈ Metric.ball x (δ / 2), smoothApprox f₀ δ z' = f₀ z' := by
    intro z' hz'
    apply smoothApprox_eq_of_closedBall_subset_open isOpen_interior hf_holo hδ
    intro u hu
    apply hball_int
    rw [Metric.mem_ball] at hz' ⊢
    rw [Metric.mem_closedBall] at hu
    calc dist u x ≤ dist u z' + dist z' x := dist_triangle u z' x
      _ < δ / 2 + δ / 2 := add_lt_add_of_le_of_lt hu hz'
      _ = δ := add_halves δ
  have hwirt_zero : ∀ z' ∈ Metric.ball x (δ / 4), wirtingerBar (smoothApprox f₀ δ) z' = 0 := by
    intro z' hz'
    have hnhds : Metric.ball x (δ / 2) ∈ 𝓝 z' :=
      Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball (by linarith) hz')
    have hev : smoothApprox f₀ δ =ᶠ[𝓝 z'] f₀ :=
      Filter.eventuallyEq_of_mem hnhds heq_on
    have hz'_int : z' ∈ interior K :=
      hball_int (Metric.ball_subset_ball (by linarith) hz')
    have hdiff_f₀ : DifferentiableAt ℂ f₀ z' :=
      (hf_holo z' hz'_int).differentiableAt (isOpen_interior.mem_nhds hz'_int)
    exact wirtingerBar_eq_zero_of_differentiableAt (hev.differentiableAt_iff.mpr hdiff_f₀)
  have hsupp_sub : Function.support (wirtingerBar (smoothApprox f₀ δ)) ⊆
      (Metric.ball x (δ / 4))ᶜ := by
    intro z' hz' hmem
    exact hz' (hwirt_zero z' hmem)
  have htsupp_sub : tsupport (wirtingerBar (smoothApprox f₀ δ)) ⊆ (Metric.ball x (δ / 4))ᶜ :=
    closure_minimal hsupp_sub Metric.isOpen_ball.isClosed_compl
  exact htsupp_sub hx (Metric.mem_ball_self (by positivity))

/-! #### 4. Simple Jordan Arc Joining Any Two Points of an Open Connected Subset `U ⊆ ℂ` -/

private abbrev I01 : Set ℝ := Set.Icc (0 : ℝ) 1

private def i01Zero : I01 := ⟨0, left_mem_Icc.mpr zero_le_one⟩
private def i01One : I01 := ⟨1, right_mem_Icc.mpr zero_le_one⟩

private def clampI01 (x : ℝ) : I01 :=
  ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩⟩

private theorem continuous_clampI01 : Continuous clampI01 :=
  (continuous_const.max (continuous_id.min continuous_const)).subtype_mk _

private theorem clampI01_coe {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (clampI01 x : ℝ) = x := by
  change max 0 (min x 1) = x
  rw [min_eq_left hx1, max_eq_right hx0]

private theorem exists_inj_segment {p q : ℂ} (hpq : p ≠ q) :
    ∃ γ : C(I01, ℂ), Function.Injective γ ∧ γ i01Zero = p ∧ γ i01One = q ∧
      Set.range γ ⊆ segment ℝ p q := by
  let g : I01 → ℂ := fun t => ((1 : ℝ) - (t : ℝ)) • p + (t : ℝ) • q
  have hg_cont : Continuous g := by
    dsimp [g]
    exact ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
      (continuous_subtype_val.smul continuous_const)
  refine ⟨⟨g, hg_cont⟩, ?_, ?_, ?_, ?_⟩
  · intro t₁ t₂ heq
    change ((1 : ℝ) - (t₁ : ℝ)) • p + (t₁ : ℝ) • q =
      ((1 : ℝ) - (t₂ : ℝ)) • p + (t₂ : ℝ) • q at heq
    have hdiff : ((t₁ : ℝ) - (t₂ : ℝ)) • (q - p) = 0 := by
      simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one] at heq ⊢
      linear_combination heq
    rcases smul_eq_zero.mp hdiff with ht | hqp
    · exact Subtype.ext (sub_eq_zero.mp ht)
    · exact (hpq (sub_eq_zero.mp hqp).symm).elim
  · change ((1 : ℝ) - (0 : ℝ)) • p + (0 : ℝ) • q = p; simp
  · change ((1 : ℝ) - (1 : ℝ)) • p + (1 : ℝ) • q = q; simp
  · rintro _ ⟨t, rfl⟩
    rw [segment_eq_image]
    exact ⟨(t : ℝ), t.2, rfl⟩

private theorem exists_inj_arc_in_open_connected {U : Set ℂ} (hU_open : IsOpen U)
    (hU_conn : IsConnected U) {w₀ w₁ : ℂ} (hw₀ : w₀ ∈ U) (hw₁ : w₁ ∈ U) (hne : w₀ ≠ w₁) :
    ∃ γ : C(I01, ℂ), Function.Injective γ ∧ γ i01Zero = w₀ ∧ γ i01One = w₁ ∧
      Set.range γ ⊆ U := by
  let S : Set ℂ := {x ∈ U | x = w₀ ∨ ∃ γ : C(I01, ℂ),
    Function.Injective γ ∧ γ i01Zero = w₀ ∧ γ i01One = x ∧ Set.range γ ⊆ U}
  have hw₀_S : w₀ ∈ S := ⟨hw₀, Or.inl rfl⟩
  have hball_S : ∀ x₀ ∈ U, ∀ ρ > 0, Metric.ball x₀ ρ ⊆ U →
      (S ∩ Metric.ball x₀ ρ).Nonempty → Metric.ball x₀ ρ ⊆ S := by
    intro x₀ hx₀ ρ hρ hB_sub ⟨y, hyS, hyB⟩ z hzB
    have hzU : z ∈ U := hB_sub hzB
    by_cases hzw₀ : z = w₀
    · exact ⟨hzU, Or.inl hzw₀⟩
    · refine ⟨hzU, Or.inr ?_⟩
      by_cases hw₀B : w₀ ∈ Metric.ball x₀ ρ
      · obtain ⟨γ, hγ_inj, hγ0, hγ1, hγ_seg⟩ := exists_inj_segment (Ne.symm hzw₀)
        refine ⟨γ, hγ_inj, hγ0, hγ1, hγ_seg.trans ?_⟩
        exact ((convex_ball x₀ ρ).segment_subset hw₀B hzB).trans hB_sub
      · have hy_ne_w₀ : y ≠ w₀ := fun heq => hw₀B (heq ▸ hyB)
        obtain ⟨γ, hγ_inj, hγ0, hγ1, hγ_U⟩ := hyS.2.resolve_left hy_ne_w₀
        let r' : ℝ := max (dist y x₀) (dist z x₀)
        have hr'_lt : r' < ρ := max_lt hyB hzB
        let D : Set ℂ := Metric.closedBall x₀ r'
        have hD_sub_B : D ⊆ Metric.ball x₀ ρ := Metric.closedBall_subset_ball hr'_lt
        have hD_sub_U : D ⊆ U := hD_sub_B.trans hB_sub
        have hyD : y ∈ D := Metric.mem_closedBall.mpr (le_max_left _ _)
        have hzD : z ∈ D := Metric.mem_closedBall.mpr (le_max_right _ _)
        have hw₀_notD : w₀ ∉ D := fun hmem => hw₀B (hD_sub_B hmem)
        let T : Set I01 := γ ⁻¹' D
        have hT_closed : IsClosed T := Metric.isClosed_closedBall.preimage γ.continuous
        have hT_comp : IsCompact (Subtype.val '' T : Set ℝ) :=
          hT_closed.isCompact.image continuous_subtype_val
        have h1_mem : (1 : ℝ) ∈ (Subtype.val '' T : Set ℝ) :=
          ⟨i01One, by simpa [T, hγ1] using hyD, rfl⟩
        have hT_ne : (Subtype.val '' T : Set ℝ).Nonempty := ⟨1, h1_mem⟩
        have ht₀_mem : sInf (Subtype.val '' T : Set ℝ) ∈ (Subtype.val '' T : Set ℝ) :=
          hT_comp.sInf_mem hT_ne
        obtain ⟨s₀, hs₀T, hs₀_eq⟩ := ht₀_mem
        let t₀ : ℝ := (s₀ : ℝ)
        have ht₀_Icc : t₀ ∈ I01 := s₀.2
        have hγ_s₀_D : γ s₀ ∈ D := hs₀T
        have ht₀_ne0 : t₀ ≠ 0 := by
          intro h0
          have hs₀_zero : s₀ = i01Zero := Subtype.ext h0
          rw [hs₀_zero, hγ0] at hγ_s₀_D
          exact hw₀_notD hγ_s₀_D
        have ht₀_pos : 0 < t₀ := lt_of_le_of_ne ht₀_Icc.1 (Ne.symm ht₀_ne0)
        have hbefore_notD : ∀ s : I01, (s : ℝ) < t₀ → γ s ∉ D := by
          intro s hs_lt hmemD
          have hmem_img : (s : ℝ) ∈ (Subtype.val '' T : Set ℝ) := ⟨s, hmemD, rfl⟩
          have hle : sInf (Subtype.val '' T : Set ℝ) ≤ (s : ℝ) :=
            csInf_le hT_comp.bddBelow hmem_img
          rw [← hs₀_eq] at hle
          exact not_lt_of_ge hle hs_lt
        let p : ℂ := γ s₀
        by_cases hpz : p = z
        · let reparam : I01 → I01 := fun s => clampI01 (t₀ * (s : ℝ))
          have hrep_cont : Continuous reparam :=
            continuous_clampI01.comp (continuous_const.mul continuous_subtype_val)
          let γ' : C(I01, ℂ) := ⟨fun s => γ (reparam s), γ.continuous.comp hrep_cont⟩
          refine ⟨γ', ?_, ?_, ?_, ?_⟩
          · intro s₁ s₂ heq
            have hrep_eq : reparam s₁ = reparam s₂ := hγ_inj heq
            have hval := congrArg Subtype.val hrep_eq
            dsimp [reparam] at hval
            rw [clampI01_coe (mul_nonneg ht₀_pos.le s₁.2.1)
                  ((mul_le_mul_of_nonneg_left s₁.2.2 ht₀_pos.le).trans (by linarith [ht₀_Icc.2])),
                clampI01_coe (mul_nonneg ht₀_pos.le s₂.2.1)
                  ((mul_le_mul_of_nonneg_left s₂.2.2 ht₀_pos.le).trans (by linarith [ht₀_Icc.2]))]
              at hval
            exact Subtype.ext (mul_left_cancel₀ ht₀_pos.ne' hval)
          · have h0 : reparam i01Zero = i01Zero := by
              apply Subtype.ext
              change (clampI01 (t₀ * 0) : ℝ) = 0
              rw [mul_zero, clampI01_coe le_rfl zero_le_one]
            simpa [γ', h0] using hγ0
          · have h1 : reparam i01One = s₀ := by
              apply Subtype.ext
              change (clampI01 (t₀ * 1) : ℝ) = t₀
              rw [mul_one, clampI01_coe ht₀_Icc.1 ht₀_Icc.2]
            simpa [γ', h1, p] using hpz
          · rintro _ ⟨s, rfl⟩
            exact hγ_U ⟨reparam s, rfl⟩
        · let f₁ : I01 → ℂ := fun s => γ (clampI01 (2 * t₀ * (s : ℝ)))
          let f₂ : I01 → ℂ := fun s =>
            ((2 : ℝ) - 2 * (s : ℝ)) • p + (2 * (s : ℝ) - (1 : ℝ)) • z
          have hf₁_cont : Continuous f₁ :=
            γ.continuous.comp
              (continuous_clampI01.comp (continuous_const.mul continuous_subtype_val))
          have hf₂_cont : Continuous f₂ :=
            (((continuous_const.sub (continuous_const.mul continuous_subtype_val)).smul
              continuous_const).add
              (((continuous_const.mul continuous_subtype_val).sub continuous_const).smul
                continuous_const))
          let g : I01 → ℂ := fun s => if (s : ℝ) ≤ 1 / 2 then f₁ s else f₂ s
          have hg_cont : Continuous g := by
            refine Continuous.if_le hf₁_cont hf₂_cont continuous_subtype_val continuous_const ?_
            intro s hs
            dsimp [f₁, f₂]
            rw [hs]
            have hcl : clampI01 (2 * t₀ * (1 / 2 : ℝ)) = s₀ := by
              apply Subtype.ext
              have hmul : 2 * t₀ * (1 / 2 : ℝ) = t₀ := by ring
              rw [hmul, clampI01_coe ht₀_Icc.1 ht₀_Icc.2]
            rw [hcl]
            have hcoef1 : (2 : ℝ) - 2 * (1 / 2 : ℝ) = 1 := by ring
            have hcoef2 : 2 * (1 / 2 : ℝ) - (1 : ℝ) = 0 := by ring
            rw [hcoef1, hcoef2]
            simp [p]
          have hf₂_mem_D : ∀ s : I01, 1 / 2 ≤ (s : ℝ) → f₂ s ∈ D := by
            intro s hs
            change ((2 : ℝ) - 2 * (s : ℝ)) • p + (2 * (s : ℝ) - (1 : ℝ)) • z ∈ D
            have hs1 : (s : ℝ) ≤ 1 := s.2.2
            exact convex_closedBall x₀ r' hγ_s₀_D hzD
              (by linarith) (by linarith) (by ring)
          refine ⟨⟨g, hg_cont⟩, ?_, ?_, ?_, ?_⟩
          · intro s₁ s₂ heq
            change g s₁ = g s₂ at heq
            by_cases h1 : (s₁ : ℝ) ≤ 1 / 2 <;> by_cases h2 : (s₂ : ℝ) ≤ 1 / 2
            · simp only [g, h1, h2, ↓reduceIte, f₁] at heq
              have hsub := congrArg Subtype.val (hγ_inj heq)
              rw [clampI01_coe (by positivity [s₁.2.1]) (by nlinarith [ht₀_Icc.2]),
                  clampI01_coe (by positivity [s₂.2.1]) (by nlinarith [ht₀_Icc.2])] at hsub
              exact Subtype.ext (by nlinarith)
            · push Not at h2
              simp only [g, h1, not_le.mpr h2, ↓reduceIte] at heq
              rcases lt_or_eq_of_le h1 with h1_lt | h1_eq
              · let q₁ : I01 := clampI01 (2 * t₀ * (s₁ : ℝ))
                have hq₁_val : (q₁ : ℝ) = 2 * t₀ * (s₁ : ℝ) :=
                  clampI01_coe (by positivity [s₁.2.1]) (by nlinarith [ht₀_Icc.2])
                have hnotD : γ q₁ ∉ D := hbefore_notD q₁ (by rw [hq₁_val]; nlinarith)
                change γ q₁ = f₂ s₂ at heq
                rw [heq] at hnotD
                exact (hnotD (hf₂_mem_D s₂ h2.le)).elim
              · have hf₁_p : f₁ s₁ = p := by
                  dsimp [f₁]
                  rw [h1_eq]
                  congr 1; apply Subtype.ext
                  have hmul : 2 * t₀ * (1 / 2 : ℝ) = t₀ := by ring
                  rw [hmul, clampI01_coe ht₀_Icc.1 ht₀_Icc.2]
                rw [hf₁_p] at heq
                dsimp [f₂] at heq
                have hdiff : (2 * (s₂ : ℝ) - (1 : ℝ)) • (z - p) = 0 := by
                  simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_mul,
                    Complex.ofReal_ofNat, Complex.ofReal_one] at heq ⊢
                  linear_combination -heq
                rcases smul_eq_zero.mp hdiff with hcoef | hzp
                · linarith
                · exact (hpz (sub_eq_zero.mp hzp).symm).elim
            · push Not at h1
              simp only [g, not_le.mpr h1, h2, ↓reduceIte] at heq
              rcases lt_or_eq_of_le h2 with h2_lt | h2_eq
              · let q₂ : I01 := clampI01 (2 * t₀ * (s₂ : ℝ))
                have hq₂_val : (q₂ : ℝ) = 2 * t₀ * (s₂ : ℝ) :=
                  clampI01_coe (by positivity [s₂.2.1]) (by nlinarith [ht₀_Icc.2])
                have hnotD : γ q₂ ∉ D := hbefore_notD q₂ (by rw [hq₂_val]; nlinarith)
                change f₂ s₁ = γ q₂ at heq
                rw [← heq] at hnotD
                exact (hnotD (hf₂_mem_D s₁ h1.le)).elim
              · have hf₁_p : f₁ s₂ = p := by
                  dsimp [f₁]
                  rw [h2_eq]
                  congr 1; apply Subtype.ext
                  have hmul : 2 * t₀ * (1 / 2 : ℝ) = t₀ := by ring
                  rw [hmul, clampI01_coe ht₀_Icc.1 ht₀_Icc.2]
                rw [hf₁_p] at heq
                dsimp [f₂] at heq
                have hdiff : (2 * (s₁ : ℝ) - (1 : ℝ)) • (z - p) = 0 := by
                  simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_mul,
                    Complex.ofReal_ofNat, Complex.ofReal_one] at heq ⊢
                  linear_combination heq
                rcases smul_eq_zero.mp hdiff with hcoef | hzp
                · linarith
                · exact (hpz (sub_eq_zero.mp hzp).symm).elim
            · push Not at h1 h2
              simp only [g, not_le.mpr h1, not_le.mpr h2, ↓reduceIte, f₂] at heq
              have hdiff : (2 * ((s₁ : ℝ) - (s₂ : ℝ))) • (z - p) = 0 := by
                simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_mul,
                  Complex.ofReal_ofNat, Complex.ofReal_one] at heq ⊢
                linear_combination heq
              rcases smul_eq_zero.mp hdiff with hcoef | hzp
              · exact Subtype.ext (by linarith)
              · exact (hpz (sub_eq_zero.mp hzp).symm).elim
          · change g i01Zero = w₀
            have hle0 : ((i01Zero : I01) : ℝ) ≤ 1 / 2 := by change (0 : ℝ) ≤ 1 / 2; norm_num
            simp only [g, hle0, ↓reduceIte, f₁]
            have h0 : clampI01 (2 * t₀ * ((i01Zero : I01) : ℝ)) = i01Zero := by
              apply Subtype.ext
              change (clampI01 (2 * t₀ * 0) : ℝ) = 0
              rw [mul_zero, clampI01_coe le_rfl zero_le_one]
            rw [h0, hγ0]
          · change g i01One = z
            have hnot1 : ¬ (((i01One : I01) : ℝ) ≤ 1 / 2) := by change ¬ ((1 : ℝ) ≤ 1 / 2); norm_num
            simp only [g, hnot1, ↓reduceIte, f₂]
            change ((2 : ℝ) - 2 * (1 : ℝ)) • p + (2 * (1 : ℝ) - (1 : ℝ)) • z = z
            norm_num
          · rintro _ ⟨s, rfl⟩
            change g s ∈ U
            by_cases hs : (s : ℝ) ≤ 1 / 2
            · simp only [g, hs, ↓reduceIte]
              exact hγ_U ⟨_, rfl⟩
            · push Not at hs
              simp only [g, not_le.mpr hs, ↓reduceIte]
              exact hD_sub_U (hf₂_mem_D s hs.le)
  have hS_open : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro x hxS
    obtain ⟨ρ, hρ, hB⟩ := Metric.isOpen_iff.mp hU_open x hxS.1
    exact ⟨ρ, hρ, hball_S x hxS.1 ρ hρ hB ⟨x, hxS, Metric.mem_ball_self hρ⟩⟩
  have hUS_open : IsOpen (U \ S) := by
    rw [Metric.isOpen_iff]
    intro x ⟨hxU, hxnotS⟩
    obtain ⟨ρ, hρ, hB⟩ := Metric.isOpen_iff.mp hU_open x hxU
    refine ⟨ρ, hρ, fun y hyB => ⟨hB hyB, fun hyS => hxnotS ?_⟩⟩
    exact hball_S x hxU ρ hρ hB ⟨y, hyS, hyB⟩ (Metric.mem_ball_self hρ)
  have hUS_empty : U \ S = ∅ := by
    by_contra hne_diff
    rw [← Ne, ← nonempty_iff_ne_empty] at hne_diff
    obtain ⟨x₁, hx₁U, hx₁notS⟩ := hne_diff
    have hcov : U ⊆ S ∪ (U \ S) := fun x hx =>
      by_cases (fun hxS : x ∈ S => Or.inl hxS) (fun hxnot => Or.inr ⟨hx, hxnot⟩)
    obtain ⟨z, _, hzS, _, hznotS⟩ :=
      hU_conn.isPreconnected S (U \ S) hS_open hUS_open hcov ⟨w₀, hw₀, hw₀_S⟩ ⟨x₁, hx₁U, hx₁U, hx₁notS⟩
    exact hznotS hzS
  have hw₁S : w₁ ∈ S := by
    by_contra hnot
    have : w₁ ∈ U \ S := ⟨hw₁, hnot⟩
    rw [hUS_empty] at this
    exact this
  exact hw₁S.2.resolve_left hne.symm

/-! #### 5. Sub-Arc of Exact Diameter `20 * δ` and Parallelogram Disc `Dⱼ` -/

private theorem isJordanArc_range_of_injective (γ : C(I01, ℂ)) (hinj : Function.Injective γ) :
    RudinRCA.Chapter14.IsJordanArc (Set.range γ) := by
  let f : I01 → Set.range γ := Set.rangeFactorization γ
  have hf_cont : Continuous f := γ.continuous.rangeFactorization
  have hf_bij : Function.Bijective f :=
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), Set.rangeFactorization_surjective⟩
  let e : I01 ≃ₜ Set.range γ :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf_bij) hf_cont
  exact ⟨e.symm⟩

private theorem exists_disc_and_arc_for_point {K : Set ℂ} (hK : IsCompact K)
    (hKc_conn : IsConnected Kᶜ) {δ : ℝ} (hδ : 0 < δ) {zⱼ wⱼ : ℂ}
    (hwⱼ : wⱼ ∈ Kᶜ) (hzw : ‖zⱼ - wⱼ‖ < δ) :
    ∃ (cⱼ : ℂ) (Eⱼ : Set ℂ),
      Eⱼ ⊆ Kᶜ ∧
      RudinRCA.Chapter14.IsJordanArc Eⱼ ∧
      Metric.diam Eⱼ = 20 * δ ∧
      Eⱼ ⊆ Metric.ball cⱼ (20 * δ) ∧
      Metric.ball zⱼ δ ⊆ Metric.ball cⱼ (20 * δ) := by
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_ball (0 : ℂ)
  let R : ℝ := max R₀ 0 + ‖wⱼ‖ + 20 * δ + 1
  let w_far : ℂ := wⱼ + (R : ℂ)
  have hR_pos : 0 < R := by
    have : 0 ≤ max R₀ 0 := le_max_right R₀ 0
    positivity
  have hw_far_compl : w_far ∈ Kᶜ := by
    intro hmem
    have hlt : ‖w_far‖ < R₀ := by simpa using hR₀ hmem
    have hge : R - ‖wⱼ‖ ≤ ‖w_far‖ := by
      have h1 : ‖(R : ℂ)‖ - ‖wⱼ‖ ≤ ‖wⱼ + (R : ℂ)‖ := by
        have := norm_sub_norm_le (R : ℂ) (-wⱼ)
        simpa [sub_neg_eq_add, add_comm] using this
      rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR_pos] at h1
    have hR₀_le : R₀ ≤ max R₀ 0 := le_max_left R₀ 0
    dsimp [R] at hge
    linarith
  have hw_far_dist : 20 * δ < dist wⱼ w_far := by
    rw [dist_eq_norm]
    have hsub : wⱼ - w_far = -(R : ℂ) := by dsimp [w_far]; ring
    rw [hsub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR_pos]
    dsimp [R]
    have : 0 ≤ max R₀ 0 := le_max_right R₀ 0
    have : 0 ≤ ‖wⱼ‖ := norm_nonneg _
    linarith
  have hw_ne : wⱼ ≠ w_far := fun heq => by
    rw [heq, dist_self] at hw_far_dist
    linarith
  obtain ⟨γ, hγ_inj, hγ0, hγ1, hγ_compl⟩ :=
    exists_inj_arc_in_open_connected hK.isClosed.isOpen_compl hKc_conn hwⱼ hw_far_compl hw_ne
  let subArc : ℝ → Set ℂ := fun t => γ '' {s : I01 | (s : ℝ) ≤ t}
  let d : ℝ → ℝ := fun t => Metric.diam (subArc t)
  have hsubArc_bdd : ∀ t : ℝ, Bornology.IsBounded (subArc t) := fun t =>
    (isCompact_range γ.continuous).isBounded.subset (image_subset_range _ _)
  have hd_cont : ContinuousOn d (Set.Icc 0 1) := by
    have hγ_uc : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous γ.continuous
    rw [Metric.uniformContinuous_iff] at hγ_uc
    rw [Metric.continuousOn_iff]
    intro t₁ ht₁ ε hε
    obtain ⟨η, hη_pos, hη⟩ := hγ_uc (ε / 3) (by positivity)
    refine ⟨η, hη_pos, fun t₂ ht₂ hdist => ?_⟩
    rw [Real.dist_eq] at hdist ⊢
    have hle_step : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        a ≤ b → b - a < η → d b ≤ d a + 2 * (ε / 3) := by
      intro a b ha _ _ hba
      have ha_i01 : (⟨a, ha⟩ : I01) ∈ {s : I01 | (s : ℝ) ≤ a} :=
        (le_rfl : ((⟨a, ha⟩ : I01) : ℝ) ≤ a)
      have hclose : ∀ x ∈ subArc b, ∃ x' ∈ subArc a, dist x x' ≤ ε / 3 := by
        rintro _ ⟨s, hs_le : (s : ℝ) ≤ b, rfl⟩
        by_cases hsa : (s : ℝ) ≤ a
        · exact ⟨γ s, ⟨s, hsa, rfl⟩, by simp; positivity⟩
        · push Not at hsa
          refine ⟨γ ⟨a, ha⟩, ⟨⟨a, ha⟩, ha_i01, rfl⟩, ?_⟩
          refine (hη ?_).le
          change |(s : ℝ) - a| < η
          rw [abs_of_pos (by linarith)]
          linarith
      have hda_nn : 0 ≤ d a := Metric.diam_nonneg
      refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
      intro x hx y hy
      obtain ⟨x', hx', hxx'⟩ := hclose x hx
      obtain ⟨y', hy', hyy'⟩ := hclose y hy
      calc dist x y ≤ dist x x' + dist x' y' + dist y' y := dist_triangle4 x x' y' y
        _ ≤ ε / 3 + d a + ε / 3 := by
              have hxy' : dist x' y' ≤ d a :=
                Metric.dist_le_diam_of_mem (hsubArc_bdd a) hx' hy'
              rw [dist_comm y' y]
              linarith
        _ = d a + 2 * (ε / 3) := by ring
    rcases le_total t₁ t₂ with h12 | h21
    · have hmono : d t₁ ≤ d t₂ :=
        Metric.diam_mono (image_mono fun s (hs : (s : ℝ) ≤ t₁) => hs.trans h12) (hsubArc_bdd t₂)
      have ht_lt : t₂ - t₁ < η := by
        rw [abs_of_nonneg (by linarith)] at hdist
        exact hdist
      have hup : d t₂ ≤ d t₁ + 2 * (ε / 3) := hle_step t₁ t₂ ht₁ ht₂ h12 ht_lt
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hmono : d t₂ ≤ d t₁ :=
        Metric.diam_mono (image_mono fun s (hs : (s : ℝ) ≤ t₂) => hs.trans h21) (hsubArc_bdd t₁)
      have ht_lt : t₁ - t₂ < η := by
        rw [abs_of_nonpos (by linarith)] at hdist
        linarith
      have hup : d t₁ ≤ d t₂ + 2 * (ε / 3) := hle_step t₂ t₁ ht₂ ht₁ h21 ht_lt
      rw [abs_of_nonpos (by linarith)]
      linarith
  have hd0 : d 0 = 0 := by
    have hsub0 : subArc 0 = {wⱼ} := by
      ext x
      simp only [subArc, mem_image, mem_ofPred_eq, mem_singleton_iff]
      constructor
      · rintro ⟨s, hs, rfl⟩
        have hs0 : s = i01Zero := Subtype.ext (le_antisymm hs s.2.1)
        rw [hs0, hγ0]
      · rintro rfl
        exact ⟨i01Zero, le_rfl, hγ0⟩
    simp [d, hsub0]
  have hd1 : 20 * δ ≤ d 1 := by
    have hw₀_mem : wⱼ ∈ subArc 1 := ⟨i01Zero, (zero_le_one : ((i01Zero : I01) : ℝ) ≤ 1), hγ0⟩
    have hw₁_mem : w_far ∈ subArc 1 := ⟨i01One, (le_rfl : ((i01One : I01) : ℝ) ≤ 1), hγ1⟩
    exact hw_far_dist.le.trans (Metric.dist_le_diam_of_mem (hsubArc_bdd 1) hw₀_mem hw₁_mem)
  have htarget_mem : 20 * δ ∈ Set.Icc (d 0) (d 1) := by
    rw [hd0]; exact ⟨by positivity, hd1⟩
  obtain ⟨t_star, ht_star_Icc, hdt_star⟩ :=
    intermediate_value_Icc zero_le_one hd_cont htarget_mem
  have ht_star_pos : 0 < t_star := by
    rcases eq_or_lt_of_le ht_star_Icc.1 with rfl | hpos
    · rw [hd0] at hdt_star; linarith
    · exact hpos
  let reparam : I01 → I01 := fun s => clampI01 (t_star * (s : ℝ))
  have hrep_cont : Continuous reparam :=
    continuous_clampI01.comp (continuous_const.mul continuous_subtype_val)
  let γ_sub : C(I01, ℂ) := ⟨fun s => γ (reparam s), γ.continuous.comp hrep_cont⟩
  have hγ_sub_inj : Function.Injective γ_sub := by
    intro s₁ s₂ heq
    have hval := congrArg Subtype.val (hγ_inj heq)
    dsimp [reparam] at hval
    rw [clampI01_coe (mul_nonneg ht_star_pos.le s₁.2.1)
          ((mul_le_mul_of_nonneg_left s₁.2.2 ht_star_pos.le).trans (by linarith [ht_star_Icc.2])),
        clampI01_coe (mul_nonneg ht_star_pos.le s₂.2.1)
          ((mul_le_mul_of_nonneg_left s₂.2.2 ht_star_pos.le).trans (by linarith [ht_star_Icc.2]))]
      at hval
    exact Subtype.ext (mul_left_cancel₀ ht_star_pos.ne' hval)
  have hrange_eq : Set.range γ_sub = subArc t_star := by
    ext x
    simp only [Set.mem_range, subArc, mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨reparam s, ?_, rfl⟩
      dsimp [reparam]
      rw [clampI01_coe (mul_nonneg ht_star_pos.le s.2.1)
        ((mul_le_mul_of_nonneg_left s.2.2 ht_star_pos.le).trans (by linarith [ht_star_Icc.2]))]
      exact mul_le_of_le_one_right ht_star_pos.le s.2.2
    · rintro ⟨u, hu_le, rfl⟩
      let s : I01 := ⟨(u : ℝ) / t_star,
        ⟨div_nonneg u.2.1 ht_star_pos.le, (div_le_one ht_star_pos).mpr hu_le⟩⟩
      refine ⟨s, ?_⟩
      change γ (reparam s) = γ u
      congr 1; apply Subtype.ext
      dsimp [reparam, s]
      rw [mul_div_cancel₀ _ ht_star_pos.ne', clampI01_coe u.2.1 u.2.2]
  let Eⱼ : Set ℂ := Set.range γ_sub
  have hE_arc : RudinRCA.Chapter14.IsJordanArc Eⱼ :=
    isJordanArc_range_of_injective γ_sub hγ_sub_inj
  have hE_comp : IsCompact Eⱼ := RudinRCA.Chapter14.isCompact_of_isJordanArc hE_arc
  have hE_diam : Metric.diam Eⱼ = 20 * δ := by
    dsimp [Eⱼ]; rw [hrange_eq]; exact hdt_star
  have hwⱼ_E : wⱼ ∈ Eⱼ := by
    refine ⟨i01Zero, ?_⟩
    have h0 : reparam i01Zero = i01Zero := by
      apply Subtype.ext
      change (clampI01 (t_star * 0) : ℝ) = 0
      rw [mul_zero, clampI01_coe le_rfl zero_le_one]
    simpa [γ_sub, h0] using hγ0
  have hE_compl : Eⱼ ⊆ Kᶜ := by
    rintro _ ⟨s, rfl⟩
    exact hγ_compl ⟨reparam s, rfl⟩
  -- Attain diameter on `Eⱼ ×ˢ Eⱼ` and apply Parallelogram Law around midpoint `cⱼ`
  have hprod_comp : IsCompact (Eⱼ ×ˢ Eⱼ) := hE_comp.prod hE_comp
  have hprod_ne : (Eⱼ ×ˢ Eⱼ).Nonempty := ⟨(wⱼ, wⱼ), hwⱼ_E, hwⱼ_E⟩
  obtain ⟨⟨p, q⟩, ⟨hpE, hqE⟩, hpq_max⟩ :=
    hprod_comp.exists_isMaxOn hprod_ne (continuous_fst.dist continuous_snd).continuousOn
  have hpq_eq_diam : dist p q = 20 * δ := by
    apply le_antisymm
    · rw [← hE_diam]
      exact Metric.dist_le_diam_of_mem hE_comp.isBounded hpE hqE
    · rw [← hE_diam]
      refine Metric.diam_le_of_forall_dist_le dist_nonneg fun x hx y hy => ?_
      change (fun b : ℂ × ℂ => dist b.1 b.2) (x, y) ≤ (fun b : ℂ × ℂ => dist b.1 b.2) (p, q)
      exact hpq_max ⟨hx, hy⟩
  let cⱼ : ℂ := (p + q) / 2
  have hE_in_18 : ∀ x ∈ Eⱼ, ‖x - cⱼ‖ < 18 * δ := by
    intro x hx
    have hxp : ‖x - p‖ ≤ 20 * δ := by
      rw [← dist_eq_norm, ← hE_diam]
      exact Metric.dist_le_diam_of_mem hE_comp.isBounded hx hpE
    have hxq : ‖x - q‖ ≤ 20 * δ := by
      rw [← dist_eq_norm, ← hE_diam]
      exact Metric.dist_le_diam_of_mem hE_comp.isBounded hx hqE
    have hpq_norm : ‖p - q‖ = 20 * δ := by rwa [← dist_eq_norm]
    have hpara : 4 * ‖x - cⱼ‖ ^ 2 + ‖p - q‖ ^ 2 = 2 * ‖x - p‖ ^ 2 + 2 * ‖x - q‖ ^ 2 := by
      simp only [← Complex.normSq_eq_norm_sq, cⱼ, Complex.normSq_apply,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.div_ofNat_re, Complex.div_ofNat_im]
      ring
    have hxp_sq : ‖x - p‖ ^ 2 ≤ (20 * δ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxp 2
    have hxq_sq : ‖x - q‖ ^ 2 ≤ (20 * δ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxq 2
    have h4sq : 4 * ‖x - cⱼ‖ ^ 2 ≤ 1200 * δ ^ 2 := by
      rw [hpq_norm] at hpara
      linarith
    have hsq_lt : ‖x - cⱼ‖ ^ 2 < (18 * δ) ^ 2 := by nlinarith [sq_pos_of_pos hδ]
    nlinarith [norm_nonneg (x - cⱼ)]
  refine ⟨cⱼ, Eⱼ, hE_compl, hE_arc, hE_diam, ?_, ?_⟩
  · intro x hx
    rw [Metric.mem_ball, dist_eq_norm]
    exact (hE_in_18 x hx).trans (by linarith)
  · intro ζ hζ
    rw [Metric.mem_ball, dist_eq_norm] at hζ ⊢
    have hw_c : ‖wⱼ - cⱼ‖ < 18 * δ := hE_in_18 wⱼ hwⱼ_E
    have hdecomp : ζ - cⱼ = (ζ - zⱼ) + (zⱼ - wⱼ) + (wⱼ - cⱼ) := by ring
    rw [hdecomp]
    calc ‖(ζ - zⱼ) + (zⱼ - wⱼ) + (wⱼ - cⱼ)‖
        ≤ ‖(ζ - zⱼ) + (zⱼ - wⱼ)‖ + ‖wⱼ - cⱼ‖ := norm_add_le _ _
      _ ≤ ‖ζ - zⱼ‖ + ‖zⱼ - wⱼ‖ + ‖wⱼ - cⱼ‖ := by gcongr; exact norm_add_le _ _
      _ < δ + δ + 18 * δ := by linarith
      _ = 20 * δ := by ring

/-! #### 6. Separated Finite Cover and Disjoint Measurable Partition of Compact `X` -/

private theorem exists_separated_finset_sub {r : ℝ} (hr : 0 < r) (F₀ : Finset ℂ) :
    ∃ Z : Finset ℂ, Z ⊆ F₀ ∧
      (∀ z₁ ∈ Z, ∀ z₂ ∈ Z, z₁ ≠ z₂ → r ≤ dist z₁ z₂) ∧
      (∀ u ∈ F₀, ∃ z ∈ Z, dist u z < r) := by
  classical
  induction F₀ using Finset.induction with
  | empty => exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
  | @insert w F' hw_not ih =>
    obtain ⟨Z', hZ'_sub, hZ'_sep, hZ'_cov⟩ := ih
    by_cases hex : ∃ z ∈ Z', dist w z < r
    · refine ⟨Z', hZ'_sub.trans (Finset.subset_insert w F'), hZ'_sep, ?_⟩
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu'
      · exact hex
      · exact hZ'_cov u hu'
    · push Not at hex
      refine ⟨insert w Z', Finset.insert_subset_insert w hZ'_sub, ?_, ?_⟩
      · intro z₁ hz₁ z₂ hz₂ hne
        rcases Finset.mem_insert.mp hz₁ with rfl | hz₁' <;>
          rcases Finset.mem_insert.mp hz₂ with rfl | hz₂'
        · exact (hne rfl).elim
        · exact hex z₂ hz₂'
        · rw [dist_comm]; exact hex z₁ hz₁'
        · exact hZ'_sep z₁ hz₁' z₂ hz₂' hne
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu'
        · exact ⟨u, Finset.mem_insert_self u Z', by simpa using hr⟩
        · obtain ⟨z, hz, hdist⟩ := hZ'_cov u hu'
          exact ⟨z, Finset.mem_insert_of_mem hz, hdist⟩

private theorem exists_separated_cover_partition {X : Set ℂ} (hX : IsCompact X)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (m : ℕ) (z : Fin m → ℂ) (XPart : Fin m → Set ℂ),
      (∀ j, z j ∈ X) ∧
      Pairwise (fun i j => Disjoint (Metric.ball (z i) (δ / 4)) (Metric.ball (z j) (δ / 4))) ∧
      (∀ j, MeasurableSet (XPart j)) ∧
      (∀ j, XPart j ⊆ X ∩ Metric.ball (z j) δ) ∧
      Pairwise (fun i j => Disjoint (XPart i) (XPart j)) ∧
      (⋃ j : Fin m, XPart j) = X := by
  classical
  obtain ⟨t_sub, ht_cov⟩ :=
    hX.elim_finite_subcover (fun x : X => Metric.ball (x : ℂ) (δ / 2))
      (fun _ => Metric.isOpen_ball)
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (half_pos hδ)⟩)
  let F₀ : Finset ℂ := t_sub.image Subtype.val
  have hF₀_sub : (F₀ : Set ℂ) ⊆ X := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨x, _, rfl⟩
    exact x.2
  have hF₀_cov : X ⊆ ⋃ u ∈ F₀, Metric.ball u (δ / 2) := by
    intro x hx
    obtain ⟨y, hy_mem⟩ := mem_iUnion.mp (ht_cov hx)
    rw [mem_iUnion] at hy_mem
    obtain ⟨hy_t, hxy⟩ := hy_mem
    exact mem_biUnion (Finset.mem_image_of_mem Subtype.val hy_t) hxy
  obtain ⟨Z, hZ_sub, hZ_sep, hZ_cov⟩ := exists_separated_finset_sub (half_pos hδ) F₀
  let m : ℕ := Z.card
  let e : Fin m ≃ {x // x ∈ Z} := (Z.equivFin).symm
  let z : Fin m → ℂ := fun j => (e j).1
  have hz_mem_Z : ∀ j, z j ∈ Z := fun j => (e j).2
  have hz_mem_X : ∀ j, z j ∈ X := fun j => hF₀_sub (hZ_sub (hz_mem_Z j))
  have hz_inj : Function.Injective z := fun i j hij => e.injective (Subtype.ext hij)
  have hballs_disj : Pairwise
      (fun i j => Disjoint (Metric.ball (z i) (δ / 4)) (Metric.ball (z j) (δ / 4))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro y hyi hyj
    have hsep : δ / 2 ≤ dist (z i) (z j) :=
      hZ_sep (z i) (hz_mem_Z i) (z j) (hz_mem_Z j) (hz_inj.ne hij)
    have hlt : dist (z i) (z j) < δ / 4 + δ / 4 := by
      calc dist (z i) (z j) ≤ dist (z i) y + dist y (z j) := dist_triangle _ _ _
        _ = dist y (z i) + dist y (z j) := by rw [dist_comm (z i) y]
        _ < δ / 4 + δ / 4 := add_lt_add hyi hyj
    linarith
  have hX_cov : ∀ x ∈ X, ∃ j : Fin m, x ∈ Metric.ball (z j) δ := by
    intro x hx
    obtain ⟨u, huF₀, hxu⟩ := mem_iUnion₂.mp (hF₀_cov hx)
    obtain ⟨w, hwZ, huw⟩ := hZ_cov u huF₀
    let j : Fin m := e.symm ⟨w, hwZ⟩
    have hzj : z j = w := by simp [z, j]
    refine ⟨j, ?_⟩
    rw [Metric.mem_ball, hzj]
    calc dist x w ≤ dist x u + dist u w := dist_triangle x u w
      _ < δ / 2 + δ / 2 := add_lt_add hxu huw
      _ = δ := add_halves δ
  let XPart : Fin m → Set ℂ := fun j =>
    (X ∩ Metric.ball (z j) δ) \ (⋃ k : Fin m, if k < j then Metric.ball (z k) δ else ∅)
  have hXP_meas : ∀ j, MeasurableSet (XPart j) := by
    intro j
    refine (hX.isClosed.measurableSet.inter measurableSet_ball).diff ?_
    refine MeasurableSet.iUnion fun k => ?_
    split_ifs
    · exact measurableSet_ball
    · exact MeasurableSet.empty
  have hXP_sub : ∀ j, XPart j ⊆ X ∩ Metric.ball (z j) δ := fun _ => sdiff_subset
  have hXP_disj : Pairwise (fun i j => Disjoint (XPart i) (XPart j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact hxj.2 (mem_iUnion.mpr ⟨i, by simp [hlt, hxi.1.2]⟩)
    · exact hij rfl
    · exact hxi.2 (mem_iUnion.mpr ⟨j, by simp [hgt, hxj.1.2]⟩)
  have hXP_union : (⋃ j : Fin m, XPart j) = X := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨j, hxj⟩
      exact (hXP_sub j hxj).1
    · intro hx
      obtain ⟨j₀, hj₀⟩ := hX_cov x hx
      let S_idx : Finset (Fin m) := Finset.univ.filter fun k => x ∈ Metric.ball (z k) δ
      have hS_ne : S_idx.Nonempty := ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₀⟩⟩
      let j_min : Fin m := S_idx.min' hS_ne
      have hj_min_mem : x ∈ Metric.ball (z j_min) δ :=
        (Finset.mem_filter.mp (Finset.min'_mem S_idx hS_ne)).2
      refine ⟨j_min, ⟨⟨hx, hj_min_mem⟩, ?_⟩⟩
      rw [mem_iUnion]
      rintro ⟨k, hk⟩
      by_cases hlt : k < j_min
      · simp only [hlt, ↓reduceIte] at hk
        have hk_S : k ∈ S_idx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
        exact not_lt_of_ge (Finset.min'_le S_idx k hk_S) hlt
      · simp [hlt] at hk
  exact ⟨m, z, XPart, hz_mem_X, hballs_disj, hXP_meas, hXP_sub, hXP_disj, hXP_union⟩

/-! #### 7. Polar Integral Bounds for Near (`‖z - ζ‖⁻¹`) and Far (`‖z - y‖⁻³`) Kernels -/

private theorem integral_ball_inv_norm_eq (z : ℂ) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun ζ : ℂ => ‖z - ζ‖⁻¹) (Metric.ball z R) volume ∧
      ∫ ζ in Metric.ball z R, ‖z - ζ‖⁻¹ = 2 * Real.pi * R := by
  let k0 : ℂ → ℝ := fun w => ‖w‖⁻¹
  let ind0 : ℂ → ℝ := (Metric.ball (0 : ℂ) R).indicator k0
  let box : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi
  have hbox_meas : MeasurableSet box := measurableSet_Ioo.prod measurableSet_Ioo
  have hbox_sub : box ⊆ polarCoord.target := fun p hp => ⟨hp.1.1, hp.2⟩
  have hcongr_enorm : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • ‖ind0 (Complex.polarCoord.symm p)‖ₑ =
        box.indicator (fun _ => (1 : ENNReal)) p := by
    rintro ⟨r, θ⟩ ⟨hr : 0 < r, hθ⟩
    have hnorm : ‖(Complex.polarCoord.symm (r, θ) : ℂ)‖ = r := by
      rw [Complex.polarCoord_symm_apply, Complex.ofReal_cos, Complex.ofReal_sin,
        ← Complex.exp_mul_I, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    by_cases hrR : r < R
    · have hmem_ball : (Complex.polarCoord.symm (r, θ) : ℂ) ∈ Metric.ball (0 : ℂ) R := by
        rwa [Metric.mem_ball, dist_zero_right, hnorm]
      have hmem_box : (r, θ) ∈ box := ⟨⟨hr, hrR⟩, hθ⟩
      simp only [ind0, indicator_of_mem hmem_ball, indicator_of_mem hmem_box, k0, hnorm,
        Real.enorm_eq_ofReal (inv_nonneg.mpr hr.le), smul_eq_mul, ← ENNReal.ofReal_mul hr.le,
        mul_inv_cancel₀ hr.ne', ENNReal.ofReal_one]
    · have hnot_ball : (Complex.polarCoord.symm (r, θ) : ℂ) ∉ Metric.ball (0 : ℂ) R := by
        rw [Metric.mem_ball, dist_zero_right, hnorm]; exact hrR
      have hnot_box : (r, θ) ∉ box := fun hm => hrR hm.1.2
      simp only [ind0, indicator_of_notMem hnot_ball, indicator_of_notMem hnot_box,
        enorm_zero, smul_zero]
  have hind0_int : Integrable ind0 volume := by
    have hmeas : AEStronglyMeasurable ind0 volume :=
      (measurable_norm.inv.aestronglyMeasurable).indicator measurableSet_ball
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm,
      ← Complex.lintegral_comp_polarCoord_symm (fun w => ‖ind0 w‖ₑ),
      setLIntegral_congr_fun polarCoord.open_target.measurableSet hcongr_enorm,
      setLIntegral_indicator hbox_meas, inter_eq_left.mpr hbox_sub, setLIntegral_one]
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top measure_Ioo_lt_top measure_Ioo_lt_top
  have hk0_int_ball : IntegrableOn k0 (Metric.ball (0 : ℂ) R) volume :=
    (integrable_indicator_iff measurableSet_ball).mp hind0_int
  have hind0_val : ∫ w : ℂ, ind0 w = 2 * Real.pi * R := by
    rw [← Complex.integral_comp_polarCoord_symm ind0]
    have hcongr_real : ∀ p ∈ polarCoord.target,
        p.1 • ind0 (Complex.polarCoord.symm p) = box.indicator (fun _ => (1 : ℝ)) p := by
      rintro ⟨r, θ⟩ ⟨hr : 0 < r, hθ⟩
      have hnorm : ‖(Complex.polarCoord.symm (r, θ) : ℂ)‖ = r := by
        rw [Complex.polarCoord_symm_apply, Complex.ofReal_cos, Complex.ofReal_sin,
          ← Complex.exp_mul_I, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      by_cases hrR : r < R
      · have hmem_ball : (Complex.polarCoord.symm (r, θ) : ℂ) ∈ Metric.ball (0 : ℂ) R := by
          rwa [Metric.mem_ball, dist_zero_right, hnorm]
        have hmem_box : (r, θ) ∈ box := ⟨⟨hr, hrR⟩, hθ⟩
        simp only [ind0, indicator_of_mem hmem_ball, indicator_of_mem hmem_box, k0, hnorm,
          smul_eq_mul, mul_inv_cancel₀ hr.ne']
      · have hnot_ball : (Complex.polarCoord.symm (r, θ) : ℂ) ∉ Metric.ball (0 : ℂ) R := by
          rw [Metric.mem_ball, dist_zero_right, hnorm]; exact hrR
        have hnot_box : (r, θ) ∉ box := fun hm => hrR hm.1.2
        simp only [ind0, indicator_of_notMem hnot_ball, indicator_of_notMem hnot_box, smul_zero]
    rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hcongr_real,
      setIntegral_indicator hbox_meas, inter_eq_right.mpr hbox_sub, setIntegral_const,
      smul_eq_mul, mul_one, Measure.real, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Ioo, Real.volume_Ioo, sub_zero, sub_neg_eq_add,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hR.le,
      ENNReal.toReal_ofReal (by positivity [Real.pi_pos])]
    ring
  -- Shift from `0` to `z` via `w ↦ z - w`
  have hshift_eq : (Metric.ball z R).indicator (fun ζ : ℂ => ‖z - ζ‖⁻¹) =
      fun ζ => ind0 (z - ζ) := by
    ext ζ
    by_cases hζ : ζ ∈ Metric.ball z R
    · have h0 : z - ζ ∈ Metric.ball (0 : ℂ) R := by
        rw [Metric.mem_ball, dist_zero_right]
        rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hζ
        exact hζ
      simp [ind0, k0, hζ, h0]
    · have h0 : z - ζ ∉ Metric.ball (0 : ℂ) R := by
        rw [Metric.mem_ball, dist_zero_right]
        rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hζ
        exact hζ
      simp [ind0, hζ, h0]
  have hint_shifted : Integrable (fun ζ : ℂ => ind0 (z - ζ)) volume := by
    have heq : (fun ζ : ℂ => ind0 (z - ζ)) = fun ζ => ind0 ((-ζ) + z) := by
      ext ζ; congr 1; ring
    rw [heq]
    exact (hind0_int.comp_add_right z).comp_neg
  refine ⟨(integrable_indicator_iff measurableSet_ball).mp (hshift_eq.symm ▸ hint_shifted), ?_⟩
  rw [← integral_indicator measurableSet_ball, hshift_eq,
    integral_sub_left_eq_self ind0 volume z, hind0_val]

private theorem integral_annulus_inv_norm_cube_le (z : ℂ) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) :
    let ann : Set ℂ := {y : ℂ | r₁ < ‖z - y‖ ∧ ‖z - y‖ < r₂}
    IntegrableOn (fun y : ℂ => 1 / ‖z - y‖ ^ 3) ann volume ∧
      ∫ y in ann, (1 / ‖z - y‖ ^ 3) ≤ 2 * Real.pi / r₁ := by
  intro ann
  have hann_open : IsOpen ann :=
    (isOpen_lt continuous_const (continuous_norm.comp (continuous_const.sub continuous_id))).inter
      (isOpen_lt (continuous_norm.comp (continuous_const.sub continuous_id)) continuous_const)
  have hann_meas : MeasurableSet ann := hann_open.measurableSet
  let ann0 : Set ℂ := {w : ℂ | r₁ < ‖w‖ ∧ ‖w‖ < r₂}
  have hann0_open : IsOpen ann0 :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hann0_meas : MeasurableSet ann0 := hann0_open.measurableSet
  have hann0_sub_cb : ann0 ⊆ Metric.closedBall (0 : ℂ) r₂ := fun w hw => by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hw.2.le
  let k3 : ℂ → ℝ := fun w => 1 / ‖w‖ ^ 3
  let ind3 : ℂ → ℝ := ann0.indicator k3
  have hind3_int : Integrable ind3 volume := by
    rw [integrable_indicator_iff hann0_meas]
    have hcont : ContinuousOn k3 (Metric.closedBall (0 : ℂ) r₂ \ Metric.ball (0 : ℂ) r₁) := by
      intro w hw
      have hw_ne : ‖w‖ ^ 3 ≠ 0 := by
        have hge : r₁ ≤ ‖w‖ := not_lt.mp (by simpa using hw.2)
        exact pow_ne_zero 3 (lt_of_lt_of_le hr₁ hge).ne'
      exact (continuousAt_const.div (continuous_norm.pow 3).continuousAt hw_ne).continuousWithinAt
    have hcomp : IsCompact (Metric.closedBall (0 : ℂ) r₂ \ Metric.ball (0 : ℂ) r₁) :=
      (isCompact_closedBall 0 r₂).diff Metric.isOpen_ball
    refine (hcont.integrableOn_compact hcomp).mono_set fun w hw => ?_
    exact ⟨hann0_sub_cb hw, by rw [Metric.mem_ball, dist_zero_right]; exact not_lt.mpr hw.1.le⟩
  let box : Set (ℝ × ℝ) := Set.Ioo r₁ r₂ ×ˢ Set.Ioo (-Real.pi) Real.pi
  have hbox_meas : MeasurableSet box := measurableSet_Ioo.prod measurableSet_Ioo
  have hbox_sub : box ⊆ polarCoord.target := fun p hp => ⟨lt_trans hr₁ hp.1.1, hp.2⟩
  have hind3_le : ∫ w : ℂ, ind3 w ≤ 2 * Real.pi / r₁ := by
    rw [← Complex.integral_comp_polarCoord_symm ind3]
    have hcongr_real : ∀ p ∈ polarCoord.target,
        p.1 • ind3 (Complex.polarCoord.symm p) =
          box.indicator (fun q : ℝ × ℝ => 1 / q.1 ^ 2) p := by
      rintro ⟨r, θ⟩ ⟨hr : 0 < r, hθ⟩
      have hnorm : ‖(Complex.polarCoord.symm (r, θ) : ℂ)‖ = r := by
        rw [Complex.polarCoord_symm_apply, Complex.ofReal_cos, Complex.ofReal_sin,
          ← Complex.exp_mul_I, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      by_cases hmem_r : r₁ < r ∧ r < r₂
      · have hm0 : (Complex.polarCoord.symm (r, θ) : ℂ) ∈ ann0 := by
          change r₁ < ‖(Complex.polarCoord.symm (r, θ) : ℂ)‖ ∧
            ‖(Complex.polarCoord.symm (r, θ) : ℂ)‖ < r₂
          rwa [hnorm]
        have hmb : (r, θ) ∈ box := ⟨hmem_r, hθ⟩
        simp only [ind3, indicator_of_mem hm0, indicator_of_mem hmb, k3, hnorm, smul_eq_mul]
        field_simp [hr.ne']
      · have hnm0 : (Complex.polarCoord.symm (r, θ) : ℂ) ∉ ann0 := by
          change ¬ (r₁ < ‖(Complex.polarCoord.symm (r, θ) : ℂ)‖ ∧
            ‖(Complex.polarCoord.symm (r, θ) : ℂ)‖ < r₂)
          rwa [hnorm]
        have hnmb : (r, θ) ∉ box := fun hm => hmem_r hm.1
        simp only [ind3, indicator_of_notMem hnm0, indicator_of_notMem hnmb, smul_zero]
    rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hcongr_real,
      setIntegral_indicator hbox_meas, inter_eq_right.mpr hbox_sub]
    have hG_cont : ContinuousOn (fun q : ℝ × ℝ => 1 / q.1 ^ 2)
        (Set.Icc r₁ r₂ ×ˢ Set.Icc (-Real.pi) Real.pi) := by
      intro q hq
      have hne : q.1 ^ 2 ≠ 0 := pow_ne_zero 2 (lt_of_lt_of_le hr₁ hq.1.1).ne'
      exact (continuousAt_const.div (continuous_fst.pow 2).continuousAt hne).continuousWithinAt
    have hG_int : IntegrableOn (fun q : ℝ × ℝ => 1 / q.1 ^ 2) box volume :=
      (hG_cont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
    rw [Measure.volume_eq_prod] at hG_int ⊢
    rw [setIntegral_prod _ hG_int]
    have hang_eq : ∀ r ∈ Set.Ioo r₁ r₂,
        ∫ _ in Set.Ioo (-Real.pi) Real.pi, (1 / r ^ 2 : ℝ) = (2 * Real.pi) * (1 / r ^ 2) := by
      intro r _
      rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo, sub_neg_eq_add,
        ENNReal.toReal_ofReal (by positivity [Real.pi_pos])]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioo hang_eq, integral_const_mul,
      ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hr₁₂.le]
    have hftc : ∫ r in r₁..r₂, (1 / r ^ 2 : ℝ) = (-r₂⁻¹) - (-r₁⁻¹) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun r : ℝ => -r⁻¹) ?_ ?_
      · intro r hr
        rw [Set.uIcc_of_le hr₁₂.le] at hr
        have hr_pos : 0 < r := lt_of_lt_of_le hr₁ hr.1
        have hd := (hasDerivAt_inv hr_pos.ne').neg
        convert hd using 1
        field_simp [hr_pos.ne']
      · refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le hr₁₂.le]
        intro r hr
        have hr_ne : r ^ 2 ≠ 0 := pow_ne_zero 2 (lt_of_lt_of_le hr₁ hr.1).ne'
        exact (continuousAt_const.div (continuous_id.pow 2).continuousAt hr_ne).continuousWithinAt
    rw [hftc]
    have hr₂_pos : 0 < r₂ := lt_trans hr₁ hr₁₂
    have : 0 < r₂⁻¹ := inv_pos.mpr hr₂_pos
    have hprod_le : (2 * Real.pi) * ((-r₂⁻¹) - (-r₁⁻¹)) ≤ (2 * Real.pi) * r₁⁻¹ :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity [Real.pi_pos])
    exact hprod_le.trans_eq (div_eq_mul_inv (2 * Real.pi) r₁).symm
  have hshift_eq : ann.indicator (fun y : ℂ => 1 / ‖z - y‖ ^ 3) = fun y => ind3 (z - y) := by
    ext y
    by_cases hy : y ∈ ann
    · have h0 : z - y ∈ ann0 := hy
      simp [ind3, k3, hy, h0]
    · have h0 : z - y ∉ ann0 := hy
      simp [ind3, hy, h0]
  have hint_shifted : Integrable (fun y : ℂ => ind3 (z - y)) volume := by
    have heq : (fun y : ℂ => ind3 (z - y)) = fun y => ind3 ((-y) + z) := by
      ext y; congr 1; ring
    rw [heq]
    exact (hind3_int.comp_add_right z).comp_neg
  refine ⟨(integrable_indicator_iff hann_meas).mp (hshift_eq.symm ▸ hint_shifted), ?_⟩
  rw [← integral_indicator hann_meas, hshift_eq,
    integral_sub_left_eq_self ind3 volume z]
  exact hind3_le

private theorem volume_real_ball_complex (z : ℂ) {R : ℝ} (hR : 0 < R) :
    volume.real (Metric.ball z R) = Real.pi * R ^ 2 := by
  let ind0 : ℂ → ℝ := (Metric.ball (0 : ℂ) R).indicator (fun _ => (1 : ℝ))
  let box : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi
  have hbox_meas : MeasurableSet box := measurableSet_Ioo.prod measurableSet_Ioo
  have hbox_sub : box ⊆ polarCoord.target := fun p hp => ⟨hp.1.1, hp.2⟩
  have hind0_val : ∫ w : ℂ, ind0 w = Real.pi * R ^ 2 := by
    rw [← Complex.integral_comp_polarCoord_symm ind0]
    have hcongr_real : ∀ p ∈ polarCoord.target,
        p.1 • ind0 (Complex.polarCoord.symm p) = box.indicator Prod.fst p := by
      rintro ⟨r, θ⟩ ⟨hr : 0 < r, hθ⟩
      have hnorm : ‖(Complex.polarCoord.symm (r, θ) : ℂ)‖ = r := by
        rw [Complex.polarCoord_symm_apply, Complex.ofReal_cos, Complex.ofReal_sin,
          ← Complex.exp_mul_I, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      by_cases hrR : r < R
      · have hm0 : (Complex.polarCoord.symm (r, θ) : ℂ) ∈ Metric.ball (0 : ℂ) R := by
          rwa [Metric.mem_ball, dist_zero_right, hnorm]
        have hmb : (r, θ) ∈ box := ⟨⟨hr, hrR⟩, hθ⟩
        simp only [ind0, indicator_of_mem hm0, indicator_of_mem hmb, smul_eq_mul, mul_one]
      · have hnm0 : (Complex.polarCoord.symm (r, θ) : ℂ) ∉ Metric.ball (0 : ℂ) R := by
          rw [Metric.mem_ball, dist_zero_right, hnorm]; exact hrR
        have hnmb : (r, θ) ∉ box := fun hm => hrR hm.1.2
        simp only [ind0, indicator_of_notMem hnm0, indicator_of_notMem hnmb, smul_zero]
    rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hcongr_real,
      setIntegral_indicator hbox_meas, inter_eq_right.mpr hbox_sub]
    have hG_int : IntegrableOn Prod.fst box volume :=
      (continuous_fst.continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
    rw [Measure.volume_eq_prod] at hG_int ⊢
    rw [setIntegral_prod Prod.fst hG_int]
    have hang_eq : ∀ r ∈ Set.Ioo (0 : ℝ) R,
        ∫ _ in Set.Ioo (-Real.pi) Real.pi, r = (2 * Real.pi) * r := by
      intro r _
      rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo, sub_neg_eq_add,
        ENNReal.toReal_ofReal (by positivity [Real.pi_pos])]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioo hang_eq, integral_const_mul,
      ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hR.le]
    have hftc : ∫ r in (0 : ℝ)..R, r = R ^ 2 / 2 - (0 : ℝ) ^ 2 / 2 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun r : ℝ => r ^ 2 / 2) ?_ (continuous_id.intervalIntegrable 0 R)
      intro r _
      have hd := (hasDerivAt_pow 2 r).div_const 2
      convert hd using 1
      ring
    rw [hftc]
    ring
  have hshift_eq : (Metric.ball z R).indicator (fun _ : ℂ => (1 : ℝ)) =
      fun ζ => ind0 (z - ζ) := by
    ext ζ
    by_cases hζ : ζ ∈ Metric.ball z R
    · have h0 : z - ζ ∈ Metric.ball (0 : ℂ) R := by
        rw [Metric.mem_ball, dist_zero_right]
        rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hζ
        exact hζ
      simp [ind0, hζ, h0]
    · have h0 : z - ζ ∉ Metric.ball (0 : ℂ) R := by
        rw [Metric.mem_ball, dist_zero_right]
        rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hζ
        exact hζ
      simp [ind0, hζ, h0]
  have hvol_eq : volume.real (Metric.ball z R) =
      ∫ ζ : ℂ, (Metric.ball z R).indicator (fun _ => (1 : ℝ)) ζ := by
    rw [integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul, mul_one]
  rw [hvol_eq, hshift_eq, integral_sub_left_eq_self ind0 volume z, hind0_val]

private theorem mergelyan_integral_approx
    (h_ball_inv : ∀ (z : ℂ) {R : ℝ}, 0 < R →
      IntegrableOn (fun ζ : ℂ => ‖z - ζ‖⁻¹) (Metric.ball z R) volume ∧
        ∫ ζ in Metric.ball z R, ‖z - ζ‖⁻¹ = 2 * Real.pi * R)
    (h_ann_cube : ∀ (z : ℂ) {r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ →
      let ann : Set ℂ := {y : ℂ | r₁ < ‖z - y‖ ∧ ‖z - y‖ < r₂}
      IntegrableOn (fun y : ℂ => 1 / ‖z - y‖ ^ 3) ann volume ∧
        ∫ y in ann, (1 / ‖z - y‖ ^ 3) ≤ 2 * Real.pi / r₁)
    {K : Set ℂ} {δ M_w : ℝ} (hδ : 0 < δ) (hMw_nn : 0 ≤ M_w)
    {Φ : ℂ → ℂ} (hw_cont : Continuous (wirtingerBar Φ))
    (hw_bound : ∀ ζ : ℂ, ‖wirtingerBar Φ ζ‖ ≤ M_w)
    (hcg : ∀ z : ℂ,
      Integrable (fun ζ : ℂ => wirtingerBar Φ ζ / (ζ - z)) volume ∧
        Φ z = -(1 / (Real.pi : ℂ)) * ∫ ζ : ℂ, wirtingerBar Φ ζ / (ζ - z))
    (hX_comp : IsCompact (tsupport (wirtingerBar Φ)))
    {m : ℕ} (z_net c_net b_net : Fin m → ℂ)
    (XPart E_net : Fin m → Set ℂ) (g_net : Fin m → ℂ → ℂ)
    (hballs_disj : Pairwise
      (fun i j => Disjoint (Metric.ball (z_net i) (δ / 4)) (Metric.ball (z_net j) (δ / 4))))
    (hXP_meas : ∀ j, MeasurableSet (XPart j))
    (hXP_sub : ∀ j, XPart j ⊆ tsupport (wirtingerBar Φ) ∩ Metric.ball (z_net j) δ)
    (hXP_disj : Pairwise (fun i j => Disjoint (XPart i) (XPart j)))
    (hXP_union : (⋃ j : Fin m, XPart j) = tsupport (wirtingerBar Φ))
    (hE_compl : ∀ j, E_net j ⊆ Kᶜ)
    (hE_comp : ∀ j, IsCompact (E_net j))
    (hball_sub_D : ∀ j, Metric.ball (z_net j) δ ⊆ Metric.ball (c_net j) (20 * δ))
    (hg_diff : ∀ j, DifferentiableOn ℂ (g_net j) (E_net j)ᶜ)
    (hQ_est1 : ∀ j, ∀ z ∈ (E_net j)ᶜ, ∀ ζ ∈ Metric.ball (c_net j) (20 * δ),
      ‖g_net j z + (ζ - b_net j) * (g_net j z) ^ 2‖ < 100 / (20 * δ))
    (hQ_est2 : ∀ j, ∀ z ∈ (E_net j)ᶜ, ∀ ζ ∈ Metric.ball (c_net j) (20 * δ), z ≠ ζ →
      ‖(g_net j z + (ζ - b_net j) * (g_net j z) ^ 2) - (z - ζ)⁻¹‖ <
        1000 * (20 * δ) ^ 2 / ‖z - ζ‖ ^ 3) :
    ∃ (Ω : Set ℂ) (R_holo : ℂ → ℂ),
      IsOpen Ω ∧
      K ⊆ Ω ∧
      DifferentiableOn ℂ R_holo Ω ∧
      ∀ z ∈ K, ‖R_holo z - Φ z‖ ≤ 51200088 * δ * M_w := by
  classical
  let X : Set ℂ := tsupport (wirtingerBar Φ)
  let Q_net : Fin m → ℂ → ℂ → ℂ := fun j ζ z => g_net j z + (ζ - b_net j) * (g_net j z) ^ 2
  let Ω : Set ℂ := (⋃ j : Fin m, E_net j)ᶜ
  have hΩ_open : IsOpen Ω := (isCompact_iUnion hE_comp).isClosed.isOpen_compl
  have hK_sub_Ω : K ⊆ Ω := by
    intro z hz hmem
    obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
    exact hE_compl j hj hz
  let α_coeff : Fin m → ℂ := fun j => ∫ ζ in XPart j, wirtingerBar Φ ζ
  let β_coeff : Fin m → ℂ := fun j => ∫ ζ in XPart j, wirtingerBar Φ ζ * (ζ - b_net j)
  let R_holo : ℂ → ℂ := fun z =>
    (1 / (Real.pi : ℂ)) * ∑ j : Fin m, (α_coeff j * g_net j z + β_coeff j * (g_net j z) ^ 2)
  have hR_diff : DifferentiableOn ℂ R_holo Ω := by
    refine (differentiableOn_const (1 / (Real.pi : ℂ))).mul ?_
    have hsum : DifferentiableOn ℂ
        (fun z => ∑ j ∈ (Finset.univ : Finset (Fin m)),
          (α_coeff j * g_net j z + β_coeff j * (g_net j z) ^ 2)) Ω := by
      refine DifferentiableOn.fun_sum fun j _ => ?_
      have hg_Ω : DifferentiableOn ℂ (g_net j) Ω :=
        (hg_diff j).mono fun z hz hzj => hz (mem_iUnion.mpr ⟨j, hzj⟩)
      exact ((differentiableOn_const (α_coeff j)).mul hg_Ω).add
        ((differentiableOn_const (β_coeff j)).mul (hg_Ω.pow 2))
    exact hsum
  refine ⟨Ω, R_holo, hΩ_open, hK_sub_Ω, hR_diff, ?_⟩
  intro z hzK
  have hz_compl : ∀ j : Fin m, z ∈ (E_net j)ᶜ := fun j hzj => hE_compl j hzj hzK
  -- Integrability of `wirtingerBar Φ` and `wirtingerBar Φ * Q_net j · z` on `XPart j`
  have hw_int_X : IntegrableOn (wirtingerBar Φ) X volume :=
    hw_cont.continuousOn.integrableOn_compact hX_comp
  have hw_int_XP : ∀ j, IntegrableOn (wirtingerBar Φ) (XPart j) volume :=
    fun j => hw_int_X.mono_set fun ζ hζ => (hXP_sub j hζ).1
  have hw_lin_int_XP : ∀ j,
      IntegrableOn (fun ζ => wirtingerBar Φ ζ * (ζ - b_net j)) (XPart j) volume :=
    fun j => ((hw_cont.mul (continuous_id.sub continuous_const)).continuousOn.integrableOn_compact
      hX_comp).mono_set fun ζ hζ => (hXP_sub j hζ).1
  have hQ_int_XP : ∀ j,
      IntegrableOn (fun ζ => wirtingerBar Φ ζ * Q_net j ζ z) (XPart j) volume := by
    intro j
    have heq : (fun ζ => wirtingerBar Φ ζ * Q_net j ζ z) =
        fun ζ => wirtingerBar Φ ζ * g_net j z +
          (wirtingerBar Φ ζ * (ζ - b_net j)) * (g_net j z) ^ 2 := by
      ext ζ; dsimp [Q_net]; ring
    rw [heq]
    exact ((hw_int_XP j).mul_const _).add ((hw_lin_int_XP j).mul_const _)
  have hR_term_eq : ∀ j,
      α_coeff j * g_net j z + β_coeff j * (g_net j z) ^ 2 =
        ∫ ζ in XPart j, wirtingerBar Φ ζ * Q_net j ζ z := by
    intro j
    dsimp [α_coeff, β_coeff]
    rw [← integral_mul_const, ← integral_mul_const,
      ← integral_add ((hw_int_XP j).mul_const _) ((hw_lin_int_XP j).mul_const _)]
    refine setIntegral_congr_fun (hXP_meas j) fun ζ _ => ?_
    dsimp [Q_net]
    ring
  -- Express `Φ z` as `(1 / π) * ∑ j, ∫ ζ in XPart j, wirtingerBar Φ ζ * (z - ζ)⁻¹`
  let K_cg : ℂ → ℂ := fun ζ => wirtingerBar Φ ζ * (z - ζ)⁻¹
  have hKcg_eq_neg : K_cg = fun ζ => -(wirtingerBar Φ ζ / (ζ - z)) := by
    ext ζ
    dsimp [K_cg]
    rw [div_eq_mul_inv, ← mul_neg, ← inv_neg, neg_sub]
  have hKcg_int : Integrable K_cg volume := by
    rw [hKcg_eq_neg]
    exact (hcg z).1.neg
  have hΦ_eq_sum : Φ z = (1 / (Real.pi : ℂ)) * ∑ j : Fin m, ∫ ζ in XPart j, K_cg ζ := by
    obtain ⟨_, hΦ_cg⟩ := hcg z
    have h1 : Φ z = (1 / (Real.pi : ℂ)) * ∫ ζ : ℂ, K_cg ζ := by
      rw [hKcg_eq_neg, integral_neg, mul_neg, ← neg_mul]
      exact hΦ_cg
    have h2 : (∫ ζ : ℂ, K_cg ζ) = ∫ ζ in X, K_cg ζ := by
      have hind : K_cg = X.indicator K_cg := by
        ext ζ
        by_cases hζ : ζ ∈ X
        · simp [hζ]
        · have hw0 : wirtingerBar Φ ζ = 0 := image_eq_zero_of_notMem_tsupport hζ
          simp [K_cg, hζ, hw0]
      conv_lhs => rw [hind]
      exact integral_indicator hX_comp.isClosed.measurableSet
    have h3 : (∫ ζ in X, K_cg ζ) = ∑ j : Fin m, ∫ ζ in XPart j, K_cg ζ := by
      dsimp only [X]
      rw [← hXP_union]
      exact integral_iUnion_fintype hXP_meas hXP_disj (fun j => hKcg_int.integrableOn)
    rw [h1, h2, h3]
  -- Subtract `Φ z` from `R_holo z` and bound norm by `(1 / π) * ∑ j, I_j`
  let err_integrand : Fin m → ℂ → ℝ :=
    fun j ζ => ‖wirtingerBar Φ ζ‖ * ‖Q_net j ζ z - (z - ζ)⁻¹‖
  have herr_int : ∀ j, IntegrableOn (err_integrand j) (XPart j) volume := by
    intro j
    have hdiff_int : IntegrableOn (fun ζ => wirtingerBar Φ ζ * (Q_net j ζ z - (z - ζ)⁻¹))
        (XPart j) volume := by
      have heq : (fun ζ => wirtingerBar Φ ζ * (Q_net j ζ z - (z - ζ)⁻¹)) =
          fun ζ => wirtingerBar Φ ζ * Q_net j ζ z - K_cg ζ := by
        ext ζ; dsimp [K_cg]; ring
      rw [heq]
      exact (hQ_int_XP j).sub hKcg_int.integrableOn
    have hnorm_eq : err_integrand j =
        fun ζ => ‖wirtingerBar Φ ζ * (Q_net j ζ z - (z - ζ)⁻¹)‖ := by
      ext ζ; exact (norm_mul _ _).symm
    rw [hnorm_eq]
    exact hdiff_int.norm
  have hdiff_formula : R_holo z - Φ z =
      (1 / (Real.pi : ℂ)) *
        ∑ j : Fin m, ∫ ζ in XPart j, wirtingerBar Φ ζ * (Q_net j ζ z - (z - ζ)⁻¹) := by
    dsimp [R_holo]
    rw [hΦ_eq_sum, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hR_term_eq j, ← integral_sub (hQ_int_XP j) hKcg_int.integrableOn]
    refine setIntegral_congr_fun (hXP_meas j) fun ζ _ => ?_
    dsimp [K_cg]
    ring
  have hnorm_le_sum : ‖R_holo z - Φ z‖ ≤
      (1 / Real.pi) * ∑ j : Fin m, ∫ ζ in XPart j, err_integrand j ζ := by
    rw [hdiff_formula, norm_mul, one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, ← one_div]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity [Real.pi_pos])
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine setIntegral_congr_fun (hXP_meas j) fun ζ _ => norm_mul _ _
  -- Split `Finset.univ` into `Near` (`‖z - z_net j‖ < 3 * δ`) and `Far` (`3 * δ ≤ ‖z - z_net j‖`)
  let Near : Finset (Fin m) := Finset.univ.filter fun j => ‖z - z_net j‖ < 3 * δ
  let Far : Finset (Fin m) := Finset.univ.filter fun j => ¬ ‖z - z_net j‖ < 3 * δ
  have hsplit : (∑ j : Fin m, ∫ ζ in XPart j, err_integrand j ζ) =
      (∑ j ∈ Near, ∫ ζ in XPart j, err_integrand j ζ) +
        (∑ j ∈ Far, ∫ ζ in XPart j, err_integrand j ζ) :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j => ‖z - z_net j‖ < 3 * δ) (fun j => ∫ ζ in XPart j, err_integrand j ζ)).symm
  -- Bound 1: Near sum (`≤ 88 * π * δ * M_w`)
  have hnear_bound : (∑ j ∈ Near, ∫ ζ in XPart j, err_integrand j ζ) ≤
      88 * Real.pi * δ * M_w := by
    let B4 : Set ℂ := Metric.ball z (4 * δ)
    have h4δ : 0 < 4 * δ := by positivity
    obtain ⟨hinv_int, hinv_val⟩ := h_ball_inv z h4δ
    have hB4_lt_top : volume B4 < ⊤ :=
      (measure_mono Metric.ball_subset_closedBall).trans_lt
        (ProperSpace.isCompact_closedBall z (4 * δ)).measure_lt_top
    have hconst_int : IntegrableOn (fun _ : ℂ => 5 / δ) B4 volume :=
      integrableOn_const (hs := hB4_lt_top.ne)
    let maj : ℂ → ℝ := fun ζ => M_w * (5 / δ + ‖z - ζ‖⁻¹)
    have hmaj_int : IntegrableOn maj B4 volume :=
      (hconst_int.add hinv_int).const_mul M_w
    have hmaj_nn : ∀ ζ : ℂ, 0 ≤ maj ζ := fun ζ => by
      dsimp [maj]; positivity
    have hXP_sub_B4 : ∀ j ∈ Near, XPart j ⊆ B4 := by
      intro j hj ζ hζ
      have hj_lt : ‖z - z_net j‖ < 3 * δ := (Finset.mem_filter.mp hj).2
      have hζ_lt : ‖z_net j - ζ‖ < δ := by
        have := (hXP_sub j hζ).2
        rwa [Metric.mem_ball, dist_comm, dist_eq_norm] at this
      rw [Metric.mem_ball, dist_comm, dist_eq_norm]
      have hdecomp : z - ζ = (z - z_net j) + (z_net j - ζ) := by ring
      rw [hdecomp]
      calc ‖(z - z_net j) + (z_net j - ζ)‖
          ≤ ‖z - z_net j‖ + ‖z_net j - ζ‖ := norm_add_le _ _
        _ < 3 * δ + δ := add_lt_add hj_lt hζ_lt
        _ = 4 * δ := by ring
    have hterm_le : ∀ j ∈ Near,
        (∫ ζ in XPart j, err_integrand j ζ) ≤ ∫ ζ in XPart j, maj ζ := by
      intro j hj
      refine setIntegral_mono_on (herr_int j) (hmaj_int.mono_set (hXP_sub_B4 j hj))
        (hXP_meas j) fun ζ hζ => ?_
      dsimp [err_integrand, maj]
      refine mul_le_mul (hw_bound ζ) ?_ (norm_nonneg _) hMw_nn
      have hζ_D : ζ ∈ Metric.ball (c_net j) (20 * δ) := hball_sub_D j (hXP_sub j hζ).2
      have hQ_lt : ‖Q_net j ζ z‖ < 5 / δ := by
        have h1 := hQ_est1 j z (hz_compl j) ζ hζ_D
        have h2 : (100 : ℝ) / (20 * δ) = 5 / δ := by field_simp [hδ.ne']; ring
        rwa [h2] at h1
      calc ‖Q_net j ζ z - (z - ζ)⁻¹‖
          ≤ ‖Q_net j ζ z‖ + ‖(z - ζ)⁻¹‖ := norm_sub_le _ _
        _ = ‖Q_net j ζ z‖ + ‖z - ζ‖⁻¹ := by rw [norm_inv]
        _ ≤ 5 / δ + ‖z - ζ‖⁻¹ := add_le_add hQ_lt.le le_rfl
    have hsum_maj_eq : (∑ j ∈ Near, ∫ ζ in XPart j, maj ζ) =
        ∫ ζ in ⋃ j ∈ Near, XPart j, maj ζ :=
      (integral_biUnion_finset Near (fun j _ => hXP_meas j)
        (fun i _ j _ hij => hXP_disj hij)
        (fun j hj => hmaj_int.mono_set (hXP_sub_B4 j hj))).symm
    have hunion_sub : (⋃ j ∈ Near, XPart j) ⊆ B4 :=
      iUnion₂_subset hXP_sub_B4
    have hmaj_B4_val : ∫ ζ in B4, maj ζ = 88 * Real.pi * δ * M_w := by
      dsimp [maj]
      rw [integral_const_mul, integral_add hconst_int hinv_int, setIntegral_const,
        smul_eq_mul, volume_real_ball_complex z h4δ, hinv_val]
      field_simp [hδ.ne']
      ring
    calc (∑ j ∈ Near, ∫ ζ in XPart j, err_integrand j ζ)
        ≤ ∑ j ∈ Near, ∫ ζ in XPart j, maj ζ := Finset.sum_le_sum hterm_le
      _ = ∫ ζ in ⋃ j ∈ Near, XPart j, maj ζ := hsum_maj_eq
      _ ≤ ∫ ζ in B4, maj ζ :=
            setIntegral_mono_set hmaj_int (Eventually.of_forall hmaj_nn)
              (Eventually.of_forall hunion_sub)
      _ = 88 * Real.pi * δ * M_w := hmaj_B4_val
  -- Bound 2: Far sum (`≤ 51200000 * π * δ * M_w`)
  have hfar_bound : (∑ j ∈ Far, ∫ ζ in XPart j, err_integrand j ζ) ≤
      51200000 * Real.pi * δ * M_w := by
    let R_max : ℝ := (∑ k : Fin m, ‖z - z_net k‖) + 3 * δ
    have hsum_nn : 0 ≤ ∑ k : Fin m, ‖z - z_net k‖ :=
      Finset.sum_nonneg fun k _ => norm_nonneg _
    have h2δ_pos : 0 < 2 * δ := by positivity
    have h2δ_lt : 2 * δ < R_max := by dsimp [R_max]; linarith
    let ann : Set ℂ := {y : ℂ | 2 * δ < ‖z - y‖ ∧ ‖z - y‖ < R_max}
    obtain ⟨hann_int, hann_le⟩ := h_ann_cube z h2δ_pos h2δ_lt
    let B_small : Fin m → Set ℂ := fun j => Metric.ball (z_net j) (δ / 4)
    have hB_sub_ann : ∀ j ∈ Far, B_small j ⊆ ann := by
      intro j hj y hy
      have hdj : 3 * δ ≤ ‖z - z_net j‖ := not_lt.mp (Finset.mem_filter.mp hj).2
      have hy_lt : ‖y - z_net j‖ < δ / 4 := by
        simpa [B_small, Metric.mem_ball, dist_eq_norm] using hy
      have hy_lt' : ‖z_net j - y‖ < δ / 4 := by
        rwa [norm_sub_rev]
      have hlow : 2 * δ < ‖z - y‖ := by
        have htri : ‖z - z_net j‖ ≤ ‖z - y‖ + ‖y - z_net j‖ := by
          have hdecomp : z - z_net j = (z - y) + (y - z_net j) := by ring
          rw [hdecomp]; exact norm_add_le _ _
        linarith
      have hhigh : ‖z - y‖ < R_max := by
        have htri : ‖z - y‖ ≤ ‖z - z_net j‖ + ‖z_net j - y‖ := by
          have hdecomp : z - y = (z - z_net j) + (z_net j - y) := by ring
          rw [hdecomp]; exact norm_add_le _ _
        have hj_le_sum : ‖z - z_net j‖ ≤ ∑ k : Fin m, ‖z - z_net k‖ :=
          Finset.single_le_sum (f := fun k : Fin m => ‖z - z_net k‖)
            (fun k _ => norm_nonneg _) (Finset.mem_univ j)
        dsimp [R_max]
        linarith
      exact ⟨hlow, hhigh⟩
    have hterm_far : ∀ j ∈ Far,
        (∫ ζ in XPart j, err_integrand j ζ) ≤
          (M_w * 51200000 * δ ^ 2) * ∫ y in B_small j, (1 / ‖z - y‖ ^ 3) := by
      intro j hj
      have hdj : 3 * δ ≤ ‖z - z_net j‖ := not_lt.mp (Finset.mem_filter.mp hj).2
      let d_j : ℝ := ‖z - z_net j‖
      have hdj_pos : 0 < d_j + δ / 4 := by dsimp [d_j]; linarith
      let C_j : ℝ := M_w * (3200000 * δ ^ 2 / (d_j + δ / 4) ^ 3)
      have hXP_lt_top : volume (XPart j) < ⊤ :=
        (measure_mono ((hXP_sub j).trans (inter_subset_right.trans Metric.ball_subset_closedBall))).trans_lt
          (ProperSpace.isCompact_closedBall (z_net j) δ).measure_lt_top
      have hpt_XP : ∀ ζ ∈ XPart j, err_integrand j ζ ≤ C_j := by
        intro ζ hζ
        have hζ_ball : ζ ∈ Metric.ball (z_net j) δ := (hXP_sub j hζ).2
        have hζ_lt : ‖ζ - z_net j‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hζ_ball
        have hzζ_gt : d_j - δ < ‖z - ζ‖ := by
          have htri : d_j ≤ ‖z - ζ‖ + ‖ζ - z_net j‖ := by
            dsimp [d_j]
            have hdecomp : z - z_net j = (z - ζ) + (ζ - z_net j) := by ring
            rw [hdecomp]; exact norm_add_le _ _
          linarith
        have hzζ_pos : 0 < ‖z - ζ‖ := by dsimp [d_j] at hzζ_gt; linarith
        have hz_ne_ζ : z ≠ ζ := sub_ne_zero.mp (norm_pos_iff.mp hzζ_pos)
        have hd_le_2 : d_j + δ / 4 ≤ 2 * ‖z - ζ‖ := by
          dsimp [d_j] at hzζ_gt ⊢
          linarith
        have hcube_le : (d_j + δ / 4) ^ 3 ≤ 8 * ‖z - ζ‖ ^ 3 := by
          calc (d_j + δ / 4) ^ 3 ≤ (2 * ‖z - ζ‖) ^ 3 :=
                pow_le_pow_left₀ hdj_pos.le hd_le_2 3
            _ = 8 * ‖z - ζ‖ ^ 3 := by ring
        have hQ_lt := hQ_est2 j z (hz_compl j) ζ (hball_sub_D j hζ_ball) hz_ne_ζ
        have hQ_le : ‖Q_net j ζ z - (z - ζ)⁻¹‖ ≤ 3200000 * δ ^ 2 / (d_j + δ / 4) ^ 3 := by
          have h1 : 1000 * (20 * δ) ^ 2 / ‖z - ζ‖ ^ 3 ≤
              3200000 * δ ^ 2 / (d_j + δ / 4) ^ 3 := by
            rw [div_le_div_iff₀ (pow_pos hzζ_pos 3) (pow_pos hdj_pos 3)]
            nlinarith [sq_nonneg δ]
          exact hQ_lt.le.trans h1
        dsimp [err_integrand, C_j]
        exact mul_le_mul (hw_bound ζ) hQ_le (norm_nonneg _) hMw_nn
      have hint_XP_le : (∫ ζ in XPart j, err_integrand j ζ) ≤ volume.real (XPart j) * C_j := by
        calc (∫ ζ in XPart j, err_integrand j ζ)
            ≤ ∫ _ in XPart j, C_j :=
              setIntegral_mono_on (herr_int j) (integrableOn_const (hs := hXP_lt_top.ne))
                (hXP_meas j) hpt_XP
          _ = volume.real (XPart j) * C_j := by rw [setIntegral_const, smul_eq_mul]
      have hvol_XP_le : volume.real (XPart j) ≤ 16 * volume.real (B_small j) := by
        have hball_lt_top : volume (Metric.ball (z_net j) δ) < ⊤ :=
          (measure_mono Metric.ball_subset_closedBall).trans_lt
            (ProperSpace.isCompact_closedBall (z_net j) δ).measure_lt_top
        have hmono : volume.real (XPart j) ≤ volume.real (Metric.ball (z_net j) δ) :=
          measureReal_mono ((hXP_sub j).trans inter_subset_right) hball_lt_top.ne
        rw [volume_real_ball_complex (z_net j) hδ] at hmono
        have hB_vol : volume.real (B_small j) = Real.pi * (δ / 4) ^ 2 :=
          volume_real_ball_complex (z_net j) (by positivity)
        have h16 : Real.pi * δ ^ 2 = 16 * volume.real (B_small j) := by
          rw [hB_vol]; ring
        linarith
      have hBj_lt_top : volume (B_small j) < ⊤ :=
        (measure_mono Metric.ball_subset_closedBall).trans_lt
          (ProperSpace.isCompact_closedBall (z_net j) (δ / 4)).measure_lt_top
      have hBj_low : volume.real (B_small j) * (1 / (d_j + δ / 4) ^ 3) ≤
          ∫ y in B_small j, (1 / ‖z - y‖ ^ 3) := by
        have hconst_Bj : IntegrableOn (fun _ : ℂ => 1 / (d_j + δ / 4) ^ 3) (B_small j) volume :=
          integrableOn_const (hs := hBj_lt_top.ne)
        calc volume.real (B_small j) * (1 / (d_j + δ / 4) ^ 3)
            = ∫ _ in B_small j, (1 / (d_j + δ / 4) ^ 3) := by
              rw [setIntegral_const, smul_eq_mul]
          _ ≤ ∫ y in B_small j, (1 / ‖z - y‖ ^ 3) := by
              refine setIntegral_mono_on hconst_Bj (hann_int.mono_set (hB_sub_ann j hj))
                measurableSet_ball fun y hy => ?_
              have hy_ann : y ∈ ann := hB_sub_ann j hj hy
              have hy_pos : 0 < ‖z - y‖ := lt_trans h2δ_pos hy_ann.1
              have hy_le : ‖z - y‖ ≤ d_j + δ / 4 := by
                have hy_lt' : ‖z_net j - y‖ < δ / 4 := by
                  rw [norm_sub_rev]
                  simpa [B_small, Metric.mem_ball, dist_eq_norm] using hy
                have hdecomp : z - y = (z - z_net j) + (z_net j - y) := by ring
                rw [hdecomp]
                calc ‖(z - z_net j) + (z_net j - y)‖
                    ≤ ‖z - z_net j‖ + ‖z_net j - y‖ := norm_add_le _ _
                  _ ≤ d_j + δ / 4 := add_le_add le_rfl hy_lt'.le
              exact one_div_le_one_div_of_le (pow_pos hy_pos 3)
                (pow_le_pow_left₀ hy_pos.le hy_le 3)
      have hCj_nn : 0 ≤ C_j := by dsimp [C_j]; positivity
      calc (∫ ζ in XPart j, err_integrand j ζ)
          ≤ volume.real (XPart j) * C_j := hint_XP_le
        _ ≤ (16 * volume.real (B_small j)) * C_j :=
              mul_le_mul_of_nonneg_right hvol_XP_le hCj_nn
        _ = (M_w * 51200000 * δ ^ 2) *
              (volume.real (B_small j) * (1 / (d_j + δ / 4) ^ 3)) := by
              dsimp [C_j]; ring
        _ ≤ (M_w * 51200000 * δ ^ 2) * ∫ y in B_small j, (1 / ‖z - y‖ ^ 3) :=
              mul_le_mul_of_nonneg_left hBj_low (by positivity)
    have hsum_B_eq : (∑ j ∈ Far, ∫ y in B_small j, (1 / ‖z - y‖ ^ 3)) =
        ∫ y in ⋃ j ∈ Far, B_small j, (1 / ‖z - y‖ ^ 3) :=
      (integral_biUnion_finset Far (fun _ _ => measurableSet_ball)
        (fun i _ j _ hij => hballs_disj hij)
        (fun j hj => hann_int.mono_set (hB_sub_ann j hj))).symm
    have hunion_B_sub : (⋃ j ∈ Far, B_small j) ⊆ ann :=
      iUnion₂_subset hB_sub_ann
    have hsum_B_le : (∑ j ∈ Far, ∫ y in B_small j, (1 / ‖z - y‖ ^ 3)) ≤ Real.pi / δ := by
      calc (∑ j ∈ Far, ∫ y in B_small j, (1 / ‖z - y‖ ^ 3))
          = ∫ y in ⋃ j ∈ Far, B_small j, (1 / ‖z - y‖ ^ 3) := hsum_B_eq
        _ ≤ ∫ y in ann, (1 / ‖z - y‖ ^ 3) :=
              setIntegral_mono_set hann_int (Eventually.of_forall fun y => by positivity)
                (Eventually.of_forall hunion_B_sub)
        _ ≤ 2 * Real.pi / (2 * δ) := hann_le
        _ = Real.pi / δ := by field_simp [hδ.ne']
    calc (∑ j ∈ Far, ∫ ζ in XPart j, err_integrand j ζ)
        ≤ ∑ j ∈ Far, (M_w * 51200000 * δ ^ 2) * ∫ y in B_small j, (1 / ‖z - y‖ ^ 3) :=
            Finset.sum_le_sum hterm_far
      _ = (M_w * 51200000 * δ ^ 2) * ∑ j ∈ Far, ∫ y in B_small j, (1 / ‖z - y‖ ^ 3) :=
            (Finset.mul_sum _ _ _).symm
      _ ≤ (M_w * 51200000 * δ ^ 2) * (Real.pi / δ) :=
            mul_le_mul_of_nonneg_left hsum_B_le (by positivity)
      _ = 51200000 * Real.pi * δ * M_w := by field_simp [hδ.ne']
  -- Combine Near and Far bounds
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  calc ‖R_holo z - Φ z‖
      ≤ (1 / Real.pi) * ∑ j : Fin m, ∫ ζ in XPart j, err_integrand j ζ := hnorm_le_sum
    _ = (1 / Real.pi) * ((∑ j ∈ Near, ∫ ζ in XPart j, err_integrand j ζ) +
          (∑ j ∈ Far, ∫ ζ in XPart j, err_integrand j ζ)) := by rw [hsplit]
    _ ≤ (1 / Real.pi) * (88 * Real.pi * δ * M_w + 51200000 * Real.pi * δ * M_w) :=
          mul_le_mul_of_nonneg_left (add_le_add hnear_bound hfar_bound)
            (by positivity [Real.pi_pos])
    _ = 51200088 * δ * M_w := by field_simp [hpi_ne]; ring

/-! #### 8. Assembly of Mergelyan's Theorem (`theorem20_5`) and Corollaries -/

/-- **Theorem 20.5 (Mergelyan's Theorem, RCA pp. 390–394):**
If `K` is a compact set in the complex plane whose complement `Kᶜ` is connected, if `f : ℂ → ℂ` is
continuous on `K` and holomorphic in `interior K`, and if `ε > 0`, then there exists a polynomial
`P : Polynomial ℂ` such that `‖f z - P.eval z‖ < ε` for all `z ∈ K` (equivalently, `f ∈ PK K`).

*(Disclosure per `SCOPING-H-19-20.md` §hazards-7: the smoothing/localization estimate bounds the
uniform error non-strictly by `(1 + 51200088 * C_mollifier) * modulusOfCont f₀ δ < ε / 2`, which
applies directly even when `modulusOfCont f₀ δ = 0`.)* -/
theorem theorem20_5 {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected Kᶜ)
    {f : ℂ → ℂ} (hf_cont : ContinuousOn f K)
    (hf_holo : DifferentiableOn ℂ f (interior K)) :
    f ∈ PK K ∧ ∀ ε > 0, ∃ P : Polynomial ℂ, ∀ z ∈ K, ‖f z - P.eval z‖ < ε := by
  suffices h_eps : ∀ ε > 0, ∃ P : Polynomial ℂ, ∀ z ∈ K, ‖f z - P.eval z‖ < ε from
    ⟨mem_PK_iff.mpr h_eps, h_eps⟩
  intro ε hε
  -- Step 1: Compactly supported continuous extension `f₀ : C(ℂ, ℂ)` via Theorem 20.4
  obtain ⟨f₀, hf₀_supp, hf₀_eq, _, _⟩ := theorem20_4_continuousOn hK hf_cont
  have hf₀_holo : DifferentiableOn ℂ f₀ (interior K) :=
    hf_holo.congr fun z hz => hf₀_eq (interior_subset hz)
  -- Step 2: Pick smoothing radius `δ > 0` with `(1 + 51200088 * C_mollifier) * ω(δ) < ε / 2`
  let C_big : ℝ := 1 + 51200088 * C_mollifier
  have htend_scaled : Tendsto (fun δ : ℝ => C_big * modulusOfCont f₀ δ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_modulusOfCont_zero hf₀_supp).const_mul C_big
  have hev_small : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      0 < δ ∧ C_big * modulusOfCont f₀ δ < ε / 2 := by
    filter_upwards [self_mem_nhdsWithin,
      htend_scaled.eventually (gt_mem_nhds (half_pos hε))] with δ hδ_pos hδ_lt
    exact ⟨hδ_pos, hδ_lt⟩
  obtain ⟨δ, hδ, hδ_small⟩ := hev_small.exists
  -- Step 3: Smooth `f₀` by radial convolution `Φ = smoothApprox f₀ δ`
  let Φ : ℂ → ℂ := smoothApprox f₀ δ
  have hΦ_c1 : ContDiff ℝ 1 Φ := contDiff_smoothApprox hδ
  have hΦ_supp : HasCompactSupport Φ := hasCompactSupport_smoothApprox hf₀_supp hδ
  have hΦ_approx : ∀ z : ℂ, ‖Φ z - f₀ z‖ ≤ modulusOfCont f₀ δ :=
    norm_smoothApprox_sub_le hf₀_supp hδ
  let M_w : ℝ := C_mollifier * modulusOfCont f₀ δ / δ
  have hMw_nn : 0 ≤ M_w :=
    div_nonneg (mul_nonneg C_mollifier_nonneg (modulusOfCont_nonneg hf₀_supp hδ.le)) hδ.le
  have hw_cont : Continuous (wirtingerBar Φ) := continuous_wirtingerBar hΦ_c1
  have hw_bound : ∀ ζ : ℂ, ‖wirtingerBar Φ ζ‖ ≤ M_w :=
    norm_wirtingerBar_smoothApprox_le hf₀_supp hδ
  have hw_supp : HasCompactSupport (wirtingerBar Φ) :=
    hasCompactSupport_wirtingerBar hΦ_supp
  have hX_near : ∀ x ∈ tsupport (wirtingerBar Φ), ∃ w ∈ Kᶜ, ‖x - w‖ < δ :=
    tsupport_wirtingerBar_smoothApprox_near_compl hf₀_holo hδ
  -- Step 4: Separated finite cover & disjoint measurable partition of `X = tsupport (∂̄Φ)`
  obtain ⟨m, z_net, XPart, hz_X, hballs_disj, hXP_meas, hXP_sub, hXP_disj, hXP_union⟩ :=
    exists_separated_cover_partition hw_supp hδ
  -- Step 5: Build diameter-`20 * δ` Jordan arcs `E_net j ⊆ Kᶜ` and apply Lemma 20.2
  have hex_arc : ∀ j : Fin m, ∃ (cⱼ : ℂ) (Eⱼ : Set ℂ),
      Eⱼ ⊆ Kᶜ ∧
      RudinRCA.Chapter14.IsJordanArc Eⱼ ∧
      Metric.diam Eⱼ = 20 * δ ∧
      Eⱼ ⊆ Metric.ball cⱼ (20 * δ) ∧
      Metric.ball (z_net j) δ ⊆ Metric.ball cⱼ (20 * δ) := by
    intro j
    obtain ⟨wⱼ, hwⱼ, hzw⟩ := hX_near (z_net j) (hz_X j)
    exact exists_disc_and_arc_for_point hK hKc hδ hwⱼ hzw
  choose c_net E_net hE_compl hE_arc hE_diam hE_sub_D hball_sub_D using hex_arc
  have hE_comp : ∀ j : Fin m, IsCompact (E_net j) :=
    fun j => RudinRCA.Chapter14.isCompact_of_isJordanArc (hE_arc j)
  have hex_Q : ∀ j : Fin m, ∃ (gⱼ : ℂ → ℂ) (bⱼ : ℂ),
      DifferentiableOn ℂ gⱼ (E_net j)ᶜ ∧
      (∀ z ∈ (E_net j)ᶜ, ∀ ζ ∈ Metric.ball (c_net j) (20 * δ),
        ‖gⱼ z + (ζ - bⱼ) * (gⱼ z) ^ 2‖ < 100 / (20 * δ)) ∧
      (∀ z ∈ (E_net j)ᶜ, ∀ ζ ∈ Metric.ball (c_net j) (20 * δ), z ≠ ζ →
        ‖(gⱼ z + (ζ - bⱼ) * (gⱼ z) ^ 2) - (z - ζ)⁻¹‖ <
          1000 * (20 * δ) ^ 2 / ‖z - ζ‖ ^ 3) := by
    intro j
    have hr20 : 0 < 20 * δ := by positivity
    have hE_conn : IsConnected (E_net j) :=
      RudinRCA.Chapter14.isConnected_of_isJordanArc (hE_arc j)
    have hΩj_conn : IsConnected (sphericalCompl (E_net j)) :=
      (isConnected_compl_iff_sphericalCompl (hE_comp j)).mp
        (RudinRCA.Chapter14.isConnected_compl_of_isJordanArc (hE_arc j))
    obtain ⟨gⱼ, bⱼ, _, hg_diff, _, _, hQ1, _, hQ2⟩ :=
      theorem20_2 hr20 (hE_sub_D j) (hE_comp j) hE_conn (hE_diam j).symm.le hΩj_conn
    exact ⟨gⱼ, bⱼ, hg_diff, hQ1, hQ2⟩
  choose g_net b_net hg_diff hQ_est1 hQ_est2 using hex_Q
  -- Step 6: Combine Cauchy–Green (Lemma 20.3) with Near/Far integral estimates
  have hcg : ∀ z : ℂ,
      Integrable (fun ζ : ℂ => wirtingerBar Φ ζ / (ζ - z)) volume ∧
        Φ z = -(1 / (Real.pi : ℂ)) * ∫ ζ : ℂ, wirtingerBar Φ ζ / (ζ - z) :=
    fun z => ⟨(theorem20_3 hΦ_c1 hΦ_supp z).1, (theorem20_3 hΦ_c1 hΦ_supp z).2.1⟩
  obtain ⟨Ω, R_holo, hΩ_open, hK_sub_Ω, hR_diff, hR_approx⟩ :=
    mergelyan_integral_approx
      (fun z {_} hR => integral_ball_inv_norm_eq z hR)
      (fun z {_ _} hr₁ hr₁₂ => integral_annulus_inv_norm_cube_le z hr₁ hr₁₂)
      hδ hMw_nn hw_cont hw_bound hcg hw_supp
      z_net c_net b_net XPart E_net g_net
      hballs_disj hXP_meas hXP_sub hXP_disj hXP_union
      hE_compl hE_comp hball_sub_D hg_diff hQ_est1 hQ_est2
  -- Step 7: Apply Runge's Theorem (`Chapter13.theorem13_7` / `theorem20_1` part 4) to `R_holo`
  have hR_PK : R_holo ∈ PK K :=
    theorem20_1.2.2.2 hK hKc hΩ_open hK_sub_Ω hR_diff
  obtain ⟨P, hP⟩ := mem_PK_iff.mp hR_PK (ε / 2) (half_pos hε)
  refine ⟨P, fun z hzK => ?_⟩
  have hRf_lt : ‖f z - R_holo z‖ < ε / 2 := by
    have h1 : ‖R_holo z - Φ z‖ ≤ 51200088 * C_mollifier * modulusOfCont f₀ δ := by
      refine (hR_approx z hzK).trans_eq ?_
      dsimp [M_w]
      field_simp [hδ.ne']
    have h2 : ‖Φ z - f z‖ ≤ modulusOfCont f₀ δ := by
      rw [← hf₀_eq hzK]
      exact hΦ_approx z
    have hsub : f z - R_holo z = -((R_holo z - Φ z) + (Φ z - f z)) := by ring
    rw [hsub, norm_neg]
    calc ‖(R_holo z - Φ z) + (Φ z - f z)‖
        ≤ ‖R_holo z - Φ z‖ + ‖Φ z - f z‖ := norm_add_le _ _
      _ ≤ 51200088 * C_mollifier * modulusOfCont f₀ δ + modulusOfCont f₀ δ :=
            add_le_add h1 h2
      _ = C_big * modulusOfCont f₀ δ := by dsimp [C_big]; ring
      _ < ε / 2 := hδ_small
  have hdecomp : f z - P.eval z = (f z - R_holo z) + (R_holo z - P.eval z) := by ring
  rw [hdecomp]
  calc ‖(f z - R_holo z) + (R_holo z - P.eval z)‖
      ≤ ‖f z - R_holo z‖ + ‖R_holo z - P.eval z‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hRf_lt (hP z hzK)
    _ = ε := add_halves ε

/-- Complete characterization of `P(K)` when `K ⊆ ℂ` is compact with connected complement
(combining necessity from `theorem20_1` and sufficiency from Mergelyan's Theorem `theorem20_5`). -/
theorem theorem20_5_iff {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected Kᶜ) {f : ℂ → ℂ} :
    f ∈ PK K ↔ ContinuousOn f K ∧ DifferentiableOn ℂ f (interior K) :=
  ⟨fun hf => ⟨(theorem20_1.1 hK hf).1, (theorem20_1.1 hK hf).2.1⟩,
   fun ⟨hc, hd⟩ => (theorem20_5 hK hKc hc hd).1⟩

/-- Spherical-complement (`IsConnected (sphericalCompl K)`) and `Chapter10.HolomorphicOn` form of
Mergelyan's Theorem (`theorem20_5`). -/
theorem theorem20_5_spherical {K : Set ℂ} (hK : IsCompact K)
    (hsph : IsConnected (RudinRCA.Chapter13.sphericalCompl K))
    {f : ℂ → ℂ} (hf_cont : ContinuousOn f K)
    (hf_holo : RudinRCA.Chapter10.HolomorphicOn f (interior K)) :
    f ∈ PK K ∧ ∀ ε > 0, ∃ P : Polynomial ℂ, ∀ z ∈ K, ‖f z - P.eval z‖ < ε :=
  theorem20_5 hK ((isConnected_compl_iff_sphericalCompl hK).mpr hsph) hf_cont
    ((RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn isOpen_interior).mp hf_holo)

/-- **Empty-Interior Corollary of Mergelyan's Theorem (RCA p. 390, Node 20.5):**
If `K ⊆ ℂ` is compact with connected complement `Kᶜ` and `interior K = ∅` (`K` itself need not be
connected), then *every* continuous complex function on `K` is uniformly approximable on `K` by
complex polynomials (`f ∈ PK K`). -/
theorem theorem20_5_empty_interior {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected Kᶜ)
    (hint : interior K = ∅) {f : ℂ → ℂ} (hf_cont : ContinuousOn f K) :
    f ∈ PK K ∧ ∀ ε > 0, ∃ P : Polynomial ℂ, ∀ z ∈ K, ‖f z - P.eval z‖ < ε := by
  refine theorem20_5 hK hKc hf_cont ?_
  rw [hint]
  exact differentiableOn_empty

end Node20_5


end RudinRCA.Chapter20

end

#print axioms RudinRCA.Chapter20.PK
#print axioms RudinRCA.Chapter20.mem_PK_iff
#print axioms RudinRCA.Chapter20.PKSubalgebra
#print axioms RudinRCA.Chapter20.isClosed_PKSubalgebra
#print axioms RudinRCA.Chapter20.mem_PKSubalgebra_iff
#print axioms RudinRCA.Chapter20.isConnected_compl_iff_sphericalCompl
#print axioms RudinRCA.Chapter20.theorem20_1
#print axioms RudinRCA.Chapter20.node20_2_diagonal_counterexample
#print axioms RudinRCA.Chapter20.theorem20_2
#print axioms RudinRCA.Chapter20.theorem20_2_compl
#print axioms RudinRCA.Chapter20.wirtingerBar
#print axioms RudinRCA.Chapter20.wirtingerBar_eq_zero_of_differentiableAt
#print axioms RudinRCA.Chapter20.continuous_wirtingerBar
#print axioms RudinRCA.Chapter20.tsupport_wirtingerBar_subset
#print axioms RudinRCA.Chapter20.hasCompactSupport_wirtingerBar
#print axioms RudinRCA.Chapter20.wirtingerBar_comp_add_left
#print axioms RudinRCA.Chapter20.theorem20_3
#print axioms RudinRCA.Chapter20.theorem20_4
#print axioms RudinRCA.Chapter20.theorem20_4_continuousOn
#print axioms RudinRCA.Chapter20.theorem20_5
#print axioms RudinRCA.Chapter20.theorem20_5_iff
#print axioms RudinRCA.Chapter20.theorem20_5_spherical
#print axioms RudinRCA.Chapter20.theorem20_5_empty_interior
