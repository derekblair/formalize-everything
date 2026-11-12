import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.Piecewise
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.TFAE
import RudinRCA.Chapter10
import RudinRCA.Chapter11
import RudinRCA.Chapter12

/-!
# Rudin RCA, Chapter 13 — Approximation by Rational Functions

Formalization of Chapter 13 (nodes 13.1–13.12) of Walter Rudin,
*Real and Complex Analysis* (3rd ed., 1987), for issue #42 at the fixed
Lean/Mathlib pins. Scope authority: `SCOPING-F.md`. Exercises are excluded.
-/

set_option autoImplicit false

noncomputable section
namespace RudinRCA.Chapter13

open scoped OnePoint
open Set Filter Metric
open scoped Topology


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




open scoped OnePoint
open Set Metric Submodule
open scoped RealInnerProductSpace


abbrev SphereAmbient := EuclideanSpace ℝ (Fin 3)

def northPole : SphereAmbient := !₂[0, 0, 1]

theorem norm_northPole : ‖northPole‖ = 1 := by
  simp [northPole, EuclideanSpace.norm_eq, Fin.sum_univ_succ]

theorem mem_north_orthogonal_iff (w : SphereAmbient) :
    w ∈ (ℝ ∙ northPole)ᗮ ↔ w 2 = 0 := by
  simp [Submodule.mem_orthogonal_singleton_iff_inner_left, northPole,
    PiLp.inner_apply, Fin.sum_univ_succ]

/-- The factor two accounts for Mathlib's normalization of stereographic projection. -/
def complexPlaneEquiv : ℂ ≃ₗ[ℝ] (ℝ ∙ northPole)ᗮ where
  toFun z := ⟨!₂[2 * z.re, 2 * z.im, 0], (mem_north_orthogonal_iff _).mpr (by simp)⟩
  invFun w := (w.1 0 / 2 : ℝ) + (w.1 1 / 2 : ℝ) * Complex.I
  left_inv z := by
    apply Complex.ext <;> simp <;> ring
  right_inv w := by
    apply Subtype.ext
    ext i
    have hw := (mem_north_orthogonal_iff w.1).mp w.2
    fin_cases i <;> simp [hw] <;> ring
  map_add' z w := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r z := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp <;> ring

@[simp] theorem complexPlaneEquiv_coe (z : ℂ) :
    (complexPlaneEquiv z : SphereAmbient) = !₂[2 * z.re, 2 * z.im, 0] := rfl

def bookSphereHomeomorph :
    OnePoint ℂ ≃ₜ sphere (0 : SphereAmbient) 1 :=
  complexPlaneEquiv.toContinuousLinearEquiv.toHomeomorph.onePointCongr.trans
    (onePointHyperplaneHomeoUnitSphere norm_northPole)

theorem bookSphereHomeomorph_infty :
    (bookSphereHomeomorph ∞ : SphereAmbient) = northPole := by
  simp [bookSphereHomeomorph, onePointHyperplaneHomeoUnitSphere]

theorem norm_complexPlaneEquiv_sq (z : ℂ) :
    ‖(complexPlaneEquiv z : SphereAmbient)‖ ^ 2 = 4 * ‖z‖ ^ 2 := by
  rw [complexPlaneEquiv_coe, EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_succ, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Rudin's displayed stereographic coordinates, in Cartesian form. -/
theorem bookSphereHomeomorph_coe (z : ℂ) :
    (bookSphereHomeomorph (z : OnePoint ℂ) : SphereAmbient) =
      !₂[2 * z.re / (‖z‖ ^ 2 + 1), 2 * z.im / (‖z‖ ^ 2 + 1),
        (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1)] := by
  change stereoInvFunAux northPole (complexPlaneEquiv z) = _
  rw [stereoInvFunAux_apply, norm_complexPlaneEquiv_sq, complexPlaneEquiv_coe]
  have hpos : 0 < ‖z‖ ^ 2 + 1 := by positivity
  have hpos' : 0 < 4 * ‖z‖ ^ 2 + 4 := by positivity
  ext i
  fin_cases i <;> simp [northPole] <;>
    field_simp [ne_of_gt hpos, ne_of_gt hpos'] <;> ring

open Filter Set Function
open scoped Topology


/-- The bounded removable-singularity statement at infinity in Rudin RCA 13.1.
The value assigned at zero to the inverse-coordinate expression is explicitly updated. -/
theorem removable_at_infinity_of_bounded
    {f : ℂ → ℂ} {r M : ℝ}
    (hf : DifferentiableOn ℂ f {z : ℂ | r < ‖z‖})
    (hb : ∀ z : ℂ, r < ‖z‖ → ‖f z‖ ≤ M) :
    ∃ c : ℂ, Tendsto f (cocompact ℂ) (𝓝 c) ∧
      AnalyticAt ℂ (Function.update (fun z : ℂ => f z⁻¹) 0 c) 0 := by
  classical
  let g : ℂ → ℂ := fun z => f z⁻¹
  have hext : ∀ᶠ z : ℂ in 𝓝[≠] 0, r < ‖z⁻¹‖ :=
    (tendsto_norm_cobounded_atTop.comp tendsto_inv₀_nhdsNE_zero).eventually_gt_atTop r
  have hd : ∀ᶠ z : ℂ in 𝓝[≠] 0, DifferentiableAt ℂ g z := by
    filter_upwards [hext, self_mem_nhdsWithin] with z hz hz0
    have hdf : DifferentiableAt ℂ f z⁻¹ :=
      hf.differentiableAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
    exact hdf.comp z (differentiableAt_inv hz0)
  have hbound : IsBoundedUnder (· ≤ ·) (𝓝[≠] (0 : ℂ))
      (fun z => ‖g z - g 0‖) := by
    refine ⟨M + ‖g 0‖, ?_⟩
    exact eventually_map.mpr (hext.mono fun z hz => norm_sub_le_of_le (hb z⁻¹ hz) le_rfl)
  let c : ℂ := limUnder (𝓝[≠] (0 : ℂ)) g
  have hlim : Tendsto g (𝓝[≠] 0) (𝓝 c) :=
    Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hd hbound
  refine ⟨c, ?_, ?_⟩
  · have h := hlim.comp (tendsto_inv₀_cobounded' (α := ℂ))
    simpa only [g, Function.comp_def, inv_inv, Metric.cobounded_eq_cocompact] using h
  · apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [hd, self_mem_nhdsWithin] with z hz hz0
      apply hz.congr_of_eventuallyEq
      filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
      exact Function.update_of_ne hw c g
    · exact continuousAt_update_same.mpr hlim

open Filter Set Function
open scoped Topology BigOperators


noncomputable def inversePrincipalPolynomial (m : ℕ) (a : ℕ → ℂ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range m, Polynomial.monomial (m - i) (a i)

theorem inversePrincipalPolynomial_natDegree {m : ℕ} (hm : 0 < m)
    {a : ℕ → ℂ} (ha : a 0 ≠ 0) :
    (inversePrincipalPolynomial m a).natDegree = m := by
  have hle : (inversePrincipalPolynomial m a).natDegree ≤ m := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_monomial_le (a i)).trans (Nat.sub_le m i)
  have hc : (inversePrincipalPolynomial m a).coeff m = a 0 := by
    simp only [inversePrincipalPolynomial, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i hi hi0
      have hne : m - i ≠ m := by omega
      simp [Polynomial.coeff_monomial, hne]
    · simp [hm]
  exact hle.antisymm (Polynomial.le_natDegree_of_ne_zero (by rwa [hc]))

theorem inversePrincipalPolynomial_coeff_zero (m : ℕ) (a : ℕ → ℂ) :
    (inversePrincipalPolynomial m a).coeff 0 = 0 := by
  simp only [inversePrincipalPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i < m := Finset.mem_range.mp hi
  have hne : m - i ≠ 0 := by omega
  simp [Polynomial.coeff_monomial, hne]

theorem inversePrincipalPolynomial_eval {m : ℕ} {a : ℕ → ℂ}
    {z : ℂ} (hz : z ≠ 0) :
    z ^ m * (inversePrincipalPolynomial m a).eval z⁻¹ =
      ∑ i ∈ Finset.range m, a i * z ^ i := by
  simp only [inversePrincipalPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inv_pow_sub₀ hz (Nat.le_of_lt (Finset.mem_range.mp hi))]
  calc
    z ^ m * (a i * ((z ^ m)⁻¹ * z ^ i)) =
        a i * (z ^ m * ((z ^ m)⁻¹ * z ^ i)) := by ring
    _ = a i * z ^ i := by rw [mul_inv_cancel_left₀ (pow_ne_zero m hz)]

/-- Exact principal-part degree for a pole at infinity, RCA 13.1.
The removable remainder is represented in the inverse coordinate with an explicit value update. -/
theorem polynomial_principal_part_at_infinity
    {f : ℂ → ℂ} {m : ℕ} (hm : 0 < m)
    (hf : MeromorphicAt (fun z : ℂ => f z⁻¹) 0)
    (ho : meromorphicOrderAt (fun z : ℂ => f z⁻¹) 0 = ((-(m : ℤ)) : WithTop ℤ)) :
    ∃ p : Polynomial ℂ, p.natDegree = m ∧ p.coeff 0 = 0 ∧
      ∃ c : ℂ, AnalyticAt ℂ
        (Function.update (fun z : ℂ => f z⁻¹ - p.eval z⁻¹) 0 c) 0 := by
  classical
  obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp ho
  obtain ⟨F, hF, hTaylor⟩ := hg.exists_eq_sum_add_pow_mul m
  let a : ℕ → ℂ := fun i => iteratedDeriv i g 0 / (i.factorial : ℂ)
  let p := inversePrincipalPolynomial m a
  have ha0 : a 0 ≠ 0 := by simpa [a] using hg0
  refine ⟨p, inversePrincipalPolynomial_natDegree hm ha0,
    inversePrincipalPolynomial_coeff_zero m a, F 0, ?_⟩
  have hrem : (fun z : ℂ => f z⁻¹ - p.eval z⁻¹) =ᶠ[𝓝[≠] 0] F := by
    filter_upwards [hfg, self_mem_nhdsWithin] with z hz hz0
    have hpoly : z ^ m * p.eval z⁻¹ =
        ∑ i ∈ Finset.range m, (z ^ i / (i.factorial : ℂ)) * iteratedDeriv i g 0 := by
      rw [inversePrincipalPolynomial_eval hz0]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [a]
      ring
    have hT := hTaylor z
    simp only [smul_eq_mul] at hT
    rw [← hpoly] at hT
    simp only [sub_zero, smul_eq_mul, zpow_neg, zpow_natCast] at hz
    rw [hz, hT, ← mul_add, inv_mul_cancel_left₀ (pow_ne_zero m hz0), add_sub_cancel_left]
  apply hF.congr
  filter_upwards [eventually_nhdsWithin_iff.mp hrem] with z hz
  by_cases hz0 : z = 0
  · simp [hz0]
  · rw [Function.update_of_ne hz0]
    exact (hz hz0).symm

/-- The same principal part also gives a finite limit for the remainder at infinity. -/
theorem polynomial_principal_part_at_infinity_with_limit
    {f : ℂ → ℂ} {m : ℕ} (hm : 0 < m)
    (hf : MeromorphicAt (fun z : ℂ => f z⁻¹) 0)
    (ho : meromorphicOrderAt (fun z : ℂ => f z⁻¹) 0 = ((-(m : ℤ)) : WithTop ℤ)) :
    ∃ p : Polynomial ℂ, p.natDegree = m ∧ p.coeff 0 = 0 ∧
      ∃ c : ℂ, AnalyticAt ℂ
        (Function.update (fun z : ℂ => f z⁻¹ - p.eval z⁻¹) 0 c) 0 ∧
        Tendsto (fun z : ℂ => f z - p.eval z) (cocompact ℂ) (𝓝 c) := by
  obtain ⟨p, hdegree, hzero, c, hA⟩ := polynomial_principal_part_at_infinity hm hf ho
  refine ⟨p, hdegree, hzero, c, hA, ?_⟩
  have hlim := continuousAt_update_same.mp hA.continuousAt
  have h := hlim.comp (tendsto_inv₀_cobounded' (α := ℂ))
  simpa only [Function.comp_def, inv_inv, Metric.cobounded_eq_cocompact] using h

open Set Metric Filter
open scoped Topology


/-- Cauchy's estimates show that every Taylor coefficient above an exterior polynomial
    growth bound vanishes. -/
theorem iteratedDeriv_zero_of_exterior_growth {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (n : ℕ) (C R : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ n)
    (k : ℕ) (hk : n < k) : iteratedDeriv k f 0 = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, hr⟩ := exists_gt (max (max R 1) ((k.factorial : ℝ) * C / ε))
  have hrR : R < r := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hr
  have hr1 : 1 < r := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hr
  have hr0 : 0 < r := lt_trans zero_lt_one hr1
  have hrε : (k.factorial : ℝ) * C / ε < r := lt_of_le_of_lt (le_max_right _ _) hr
  have hce := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    k hr0 hf.diffContOnCl (C := C * r ^ n) (c := 0) (fun z hz ↦ by
      have hz' : ‖z‖ = r := by simpa [mem_sphere_iff_norm] using hz
      simpa [hz'] using hbound z (by rw [hz']; exact hrR.le))
  have hpow : r ^ n ≤ r ^ (k - 1) := pow_le_pow_right₀ hr1.le (by omega)
  have hk1 : k - 1 + 1 = k := by omega
  have hratio : (k.factorial : ℝ) * (C * r ^ n) / r ^ k ≤
      (k.factorial : ℝ) * C / r := by
    apply (div_le_div_iff₀ (pow_pos hr0 k) hr0).2
    calc
      (k.factorial : ℝ) * (C * r ^ n) * r ≤
          (k.factorial : ℝ) * (C * r ^ (k - 1)) * r :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hC)
            (Nat.cast_nonneg _)) hr0.le
      _ = (k.factorial : ℝ) * C * (r ^ (k - 1) * r) := by ring
      _ = (k.factorial : ℝ) * C * r ^ k := by rw [← pow_succ, hk1]
  have hsmall : (k.factorial : ℝ) * C / r < ε := by
    apply (div_lt_iff₀ hr0).2
    have := (div_lt_iff₀ hε).1 hrε
    linarith
  simpa only [zero_add] using le_of_lt (lt_of_le_of_lt (hce.trans hratio) hsmall)

/-- An entire function with an exterior polynomial growth bound is a polynomial. -/
theorem exists_polynomial_of_exterior_growth {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (n : ℕ) (C R : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ n) :
    ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z := by
  classical
  let p : Polynomial ℂ := ∑ k ∈ Finset.range (n + 1),
    Polynomial.C ((k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0) * Polynomial.X ^ k
  refine ⟨p, fun z ↦ ?_⟩
  have ht := Complex.taylorSeries_eq_of_entire' 0 z hf
  rw [tsum_eq_sum (s := Finset.range (n + 1))] at ht
  · simpa [p, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] using ht.symm
  · intro k hk
    have hnk : n < k := by simpa using hk
    rw [iteratedDeriv_zero_of_exterior_growth hf n C R hC hbound k hnk]
    simp

/-- Meromorphic behavior in the inverted coordinate bounds an entire function by
    a polynomial outside a sufficiently large circle. -/
theorem exterior_growth_of_meromorphicAt_inversion {f : ℂ → ℂ}
    (hm : MeromorphicAt (fun z ↦ f z⁻¹) 0) :
    ∃ (n : ℕ) (C R : ℝ), 0 ≤ C ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ n := by
  obtain ⟨n, hn⟩ := hm
  let g : ℂ → ℂ := fun z ↦ z ^ n * f z⁻¹
  have hg : AnalyticAt ℂ g 0 := by simpa [g, sub_zero, smul_eq_mul] using hn
  have hb : ∀ᶠ z in 𝓝 (0 : ℂ), ‖g z‖ < ‖g 0‖ + 1 :=
    hg.continuousAt.norm.tendsto.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨δ, hδ, hδg⟩ := Metric.eventually_nhds_iff.mp hb
  refine ⟨n, ‖g 0‖ + 1, 2 / δ, by positivity, ?_⟩
  intro z hz
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (div_pos (by norm_num) hδ) hz
  have hzi : dist z⁻¹ 0 < δ := by
    rw [dist_zero_right, norm_inv, inv_eq_one_div, div_lt_iff₀ hzpos]
    have := (div_le_iff₀ hδ).1 hz
    nlinarith
  have hi : ‖z‖⁻¹ ^ n * ‖f z‖ ≤ ‖g 0‖ + 1 := by
    simpa only [g, norm_mul, norm_pow, norm_inv, inv_inv] using (hδg hzi).le
  have hi' := mul_le_mul_of_nonneg_left hi (le_of_lt (pow_pos hzpos n))
  simpa [← mul_assoc, ← mul_pow, ne_of_gt hzpos, mul_comm] using hi'

/-- An entire function which is meromorphic at infinity is a polynomial. -/
theorem exists_polynomial_of_entire_meromorphicAt_inversion {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hm : MeromorphicAt (fun z ↦ f z⁻¹) 0) :
    ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z := by
  obtain ⟨n, C, R, hC, hbound⟩ := exterior_growth_of_meromorphicAt_inversion hm
  exact exists_polynomial_of_exterior_growth hf n C R hC hbound

/-- Every entire nonpolynomial has an essential singularity at infinity, where
    essential means that the inverted coordinate is not meromorphic at zero. -/
theorem not_meromorphicAt_inversion_of_entire_nonpolynomial {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hnp : ¬∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) :
    ¬ MeromorphicAt (fun z ↦ f z⁻¹) 0 := by
  intro hm
  exact hnp (exists_polynomial_of_entire_meromorphicAt_inversion hf hm)

/-- Rudin 13.12: the logarithm of the modulus of a zero-free holomorphic
function is harmonic on its open domain. Neither connectedness nor simple
connectedness is assumed. -/
theorem harmonic_log_norm {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) (hzero : ∀ z ∈ Ω, f z ≠ 0) :
    InnerProductSpace.HarmonicOnNhd (fun z => Real.log ‖f z‖) Ω := by
  intro z hz
  exact (hf.analyticOnNhd hΩ z hz).harmonicAt_log_norm (hzero z hz)

/-- A holomorphic function on some punctured neighborhood of infinity (§13.1). -/
def HasIsolatedSingularityAtInfinity (f : ℂ → ℂ) : Prop :=
  ∃ r > 0, DifferentiableOn ℂ f (exteriorDisc r)

/-- Removability at infinity is analytic extendibility in the inverse coordinate;
the original arbitrary value at zero is replaced by the extension value. -/
def HasRemovableSingularityAtInfinity (f : ℂ → ℂ) : Prop :=
  ∃ c : ℂ, AnalyticAt ℂ (Function.update (fun z : ℂ => f z⁻¹) 0 c) 0

/-- A pole at infinity of order `m`, defined by the inverse-coordinate order. -/
def HasPoleAtInfinity (f : ℂ → ℂ) (m : ℕ) : Prop :=
  0 < m ∧ MeromorphicAt (fun z : ℂ => f z⁻¹) 0 ∧
    meromorphicOrderAt (fun z : ℂ => f z⁻¹) 0 = ((-(m : ℤ)) : WithTop ℤ)

/-- An isolated singularity at infinity is essential when its inverse-coordinate
germ at zero is not meromorphic. -/
def HasEssentialSingularityAtInfinity (f : ℂ → ℂ) : Prop :=
  HasIsolatedSingularityAtInfinity f ∧ ¬ MeromorphicAt (fun z : ℂ => f z⁻¹) 0

theorem entire_hasIsolatedSingularityAtInfinity {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) : HasIsolatedSingularityAtInfinity f :=
  ⟨1, zero_lt_one, hf.differentiableOn⟩

theorem bounded_hasRemovableSingularityAtInfinity {f : ℂ → ℂ} {r M : ℝ}
    (hf : DifferentiableOn ℂ f (exteriorDisc r))
    (hb : ∀ z ∈ exteriorDisc r, ‖f z‖ ≤ M) : HasRemovableSingularityAtInfinity f := by
  obtain ⟨c, _, hc⟩ := removable_at_infinity_of_bounded hf hb
  exact ⟨c, hc⟩

theorem entire_nonpolynomial_hasEssentialSingularityAtInfinity {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) :
    HasEssentialSingularityAtInfinity f :=
  ⟨entire_hasIsolatedSingularityAtInfinity hf,
    not_meromorphicAt_inversion_of_entire_nonpolynomial hf hnp⟩

theorem pole_at_infinity_has_principal_part {f : ℂ → ℂ} {m : ℕ}
    (h : HasPoleAtInfinity f m) :
    ∃ p : Polynomial ℂ, p.natDegree = m ∧ p.coeff 0 = 0 ∧
      HasRemovableSingularityAtInfinity (fun z => f z - p.eval z) := by
  obtain ⟨p, hp, hzero, c, hc⟩ := polynomial_principal_part_at_infinity h.1 h.2.1 h.2.2
  exact ⟨p, hp, hzero, c, hc⟩


/-! ## Spherical complement abbreviation and 13.1 completion -/

/-- Spherical complement `S² \ S` of a planar set `S ⊆ ℂ`, viewed in `RiemannSphere = OnePoint ℂ`. -/
abbrev sphericalCompl (S : Set ℂ) : Set RiemannSphere :=
  (((↑) : ℂ → RiemannSphere) '' S)ᶜ

@[simp] theorem infinity_mem_sphericalCompl (S : Set ℂ) :
    (∞ : RiemannSphere) ∈ sphericalCompl S := by
  simp [sphericalCompl]

@[simp] theorem coe_mem_sphericalCompl (z : ℂ) (S : Set ℂ) :
    (z : RiemannSphere) ∈ sphericalCompl S ↔ z ∉ S := by
  simp [sphericalCompl, OnePoint.coe_injective.mem_set_image]

/-- Open sets in the Riemann sphere are characterized by ordinary finite open balls around finite
points together with exterior neighborhoods `D(∞; r)` around `∞` (RCA 13.1). -/
theorem isOpen_riemannSphere_iff (U : Set RiemannSphere) :
    IsOpen U ↔
      (∀ z : ℂ, (z : RiemannSphere) ∈ U → ∃ r > 0, ((↑) : ℂ → RiemannSphere) '' ball z r ⊆ U) ∧
      ((∞ : RiemannSphere) ∈ U → ∃ r > 0, infinityDisc r ⊆ U) := by
  constructor
  · intro hU
    refine ⟨fun z hz => ?_, fun hinf => mem_nhds_infinity_iff.mp (hU.mem_nhds hinf)⟩
    have hpre : IsOpen (((↑) : ℂ → RiemannSphere) ⁻¹' U) :=
      hU.preimage OnePoint.continuous_coe
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hpre z hz
    exact ⟨r, hr, image_subset_iff.mpr hsub⟩
  · rintro ⟨hfin, hinf⟩
    rw [isOpen_iff_mem_nhds]
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact mem_nhds_infinity_iff.mpr (hinf hx)
    | coe z =>
      obtain ⟨r, hr, hsub⟩ := hfin z hx
      have hopen : IsOpen (((↑) : ℂ → RiemannSphere) '' ball z r) :=
        OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_ball
      exact Filter.mem_of_superset
        (hopen.mem_nhds (mem_image_of_mem _ (mem_ball_self hr))) hsub

/-- Stereographic projection in the exact `1 + ‖z‖ ^ 2` denominator order of RCA 13.1. -/
theorem bookSphereHomeomorph_coe_one_add (z : ℂ) :
    (bookSphereHomeomorph (z : OnePoint ℂ) : SphereAmbient) =
      !₂[2 * z.re / (1 + ‖z‖ ^ 2), 2 * z.im / (1 + ‖z‖ ^ 2),
        (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2)] := by
  simpa only [add_comm (1 : ℝ) (‖z‖ ^ 2)] using bookSphereHomeomorph_coe z

/-- Removability at infinity implies existence of a finite limit at infinity (`cocompact ℂ`). -/
theorem tendsto_cocompact_of_hasRemovableSingularityAtInfinity {f : ℂ → ℂ}
    (h : HasRemovableSingularityAtInfinity f) :
    ∃ c : ℂ, Tendsto f (cocompact ℂ) (𝓝 c) ∧
      AnalyticAt ℂ (Function.update (fun z : ℂ => f z⁻¹) 0 c) 0 := by
  obtain ⟨c, hA⟩ := h
  refine ⟨c, ?_, hA⟩
  have hlim := continuousAt_update_same.mp hA.continuousAt
  have hcomp := hlim.comp (tendsto_inv₀_cobounded' (α := ℂ))
  simpa only [Function.comp_def, inv_inv, Metric.cobounded_eq_cocompact] using hcomp

/-- Uniqueness of the constant-free polynomial principal part at infinity (RCA 13.1). -/
theorem polynomial_principal_part_at_infinity_unique {f : ℂ → ℂ}
    {p₁ p₂ : Polynomial ℂ} (hp₁ : p₁.coeff 0 = 0) (hp₂ : p₂.coeff 0 = 0)
    (hr₁ : HasRemovableSingularityAtInfinity (fun z => f z - p₁.eval z))
    (hr₂ : HasRemovableSingularityAtInfinity (fun z => f z - p₂.eval z)) :
    p₁ = p₂ := by
  obtain ⟨c₁, hlim₁, _⟩ := tendsto_cocompact_of_hasRemovableSingularityAtInfinity hr₁
  obtain ⟨c₂, hlim₂, _⟩ := tendsto_cocompact_of_hasRemovableSingularityAtInfinity hr₂
  have hdiff : Tendsto (fun z : ℂ => (p₂ - p₁).eval z) (cocompact ℂ) (𝓝 (c₁ - c₂)) := by
    refine (hlim₁.sub hlim₂).congr fun z => ?_
    rw [Polynomial.eval_sub]
    ring
  have hev : {z : ℂ | ‖(p₂ - p₁).eval z‖ < ‖c₁ - c₂‖ + 1} ∈ cocompact ℂ :=
    hdiff.norm.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨K, hK, hKc⟩ := Filter.mem_cocompact.mp hev
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn (p₂ - p₁).continuous.continuousOn
  let M : ℝ := max M₁ (‖c₁ - c₂‖ + 1)
  have hbnd : ∀ z : ℂ, ‖(p₂ - p₁).eval z‖ ≤ M := by
    intro z
    by_cases hz : z ∈ K
    · exact (hM₁ z hz).trans (le_max_left _ _)
    · exact (hKc hz).le.trans (le_max_right _ _)
  obtain ⟨d, hd⟩ := RudinRCA.Chapter10.liouville
    (RudinRCA.Chapter10.holomorphicOn_polynomial (p₂ - p₁))
    (isBounded_iff_forall_norm_le.mpr ⟨M, by rintro _ ⟨z, rfl⟩; exact hbnd z⟩)
  have hd0 : d = 0 := by
    have h0 := hd 0
    rw [Polynomial.eval_sub, ← Polynomial.coeff_zero_eq_eval_zero,
      ← Polynomial.coeff_zero_eq_eval_zero, hp₂, hp₁, sub_zero] at h0
    exact h0.symm
  apply Polynomial.funext
  intro z
  have hz := hd z
  rw [hd0, Polynomial.eval_sub] at hz
  exact (sub_eq_zero.mp hz).symm

/-- Singularity trichotomy at infinity (RCA 13.1): an isolated singularity at `∞` is exclusively
removable, a pole of unique positive order `m`, or essential. -/
theorem singularity_at_infinity_trichotomy {f : ℂ → ℂ}
    (hf : HasIsolatedSingularityAtInfinity f) :
    (HasRemovableSingularityAtInfinity f ∨
      (∃ m : ℕ, HasPoleAtInfinity f m) ∨
      HasEssentialSingularityAtInfinity f) ∧
    ¬ (HasRemovableSingularityAtInfinity f ∧ ∃ m : ℕ, HasPoleAtInfinity f m) ∧
    ¬ (HasRemovableSingularityAtInfinity f ∧ HasEssentialSingularityAtInfinity f) ∧
    ¬ ((∃ m : ℕ, HasPoleAtInfinity f m) ∧ HasEssentialSingularityAtInfinity f) ∧
    (∀ m₁ m₂ : ℕ, HasPoleAtInfinity f m₁ → HasPoleAtInfinity f m₂ → m₁ = m₂) := by
  let g : ℂ → ℂ := fun z => f z⁻¹
  have hrem_mero : HasRemovableSingularityAtInfinity f →
      MeromorphicAt g 0 ∧ 0 ≤ meromorphicOrderAt g 0 := by
    rintro ⟨c, hA⟩
    have heq : update g 0 c =ᶠ[𝓝[≠] 0] g := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact Function.update_of_ne hz c g
    have hm : MeromorphicAt g 0 := hA.meromorphicAt.congr heq
    refine ⟨hm, ?_⟩
    rw [← meromorphicOrderAt_congr heq]
    exact hA.meromorphicOrderAt_nonneg
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_cases hm : MeromorphicAt g 0
    · by_cases hnn : 0 ≤ meromorphicOrderAt g 0
      · left
        obtain ⟨F, hF, hFg⟩ := (hm.meromorphicOrderAt_nonneg_iff).mp hnn
        refine ⟨F 0, hF.congr ?_⟩
        filter_upwards [eventually_nhdsWithin_iff.mp hFg] with z hz
        by_cases hz0 : z = 0
        · simp [hz0]
        · rw [Function.update_of_ne hz0]
          exact (hz hz0).symm
      · right; left
        have hlt : meromorphicOrderAt g 0 < 0 := lt_of_not_ge hnn
        cases ho : meromorphicOrderAt g 0 with
        | top =>
          rw [ho] at hlt
          exact absurd hlt (not_lt_of_ge le_top)
        | coe k =>
          rw [ho] at hlt
          have hk : k < 0 := by exact_mod_cast hlt
          lift (-k) to ℕ using (by omega) with m hm_eq
          refine ⟨m, by omega, hm, ?_⟩
          rw [ho]
          have hkm : k = -(m : ℤ) := by omega
          rw [hkm]
          rfl
    · exact Or.inr (Or.inr ⟨hf, hm⟩)
  · rintro ⟨hrem, m, hm_pos, _, ho⟩
    have hnn := (hrem_mero hrem).2
    rw [ho] at hnn
    have hk : (0 : ℤ) ≤ -(m : ℤ) := by exact_mod_cast hnn
    omega
  · rintro ⟨hrem, _, hnmero⟩
    exact hnmero (hrem_mero hrem).1
  · rintro ⟨⟨m, _, hm, _⟩, _, hnmero⟩
    exact hnmero hm
  · intro m₁ m₂ h₁ h₂
    have heq : ((-(m₁ : ℤ)) : WithTop ℤ) = (-(m₂ : ℤ) : WithTop ℤ) :=
      h₁.2.2.symm.trans h₂.2.2
    have heq' : -(m₁ : ℤ) = -(m₂ : ℤ) := WithTop.coe_inj.mp heq
    omega

/-- **Rudin RCA 13.1** (The Riemann sphere and isolated singularities at infinity):
1. Finite open balls and exterior neighborhoods `D(∞; r) = D'(∞; r) ∪ {∞}` characterize the
   topology of `S²`, which is compact and embeds `ℂ` openly with its usual topology;
2. Stereographic projection `φ` with `φ(∞) = (0, 0, 1)` and
   `φ(z) = (2 Re z / (1 + |z|²), 2 Im z / (1 + |z|²), (|z|² - 1) / (1 + |z|²))` is a
   homeomorphism onto the unit sphere in `ℝ³`;
3. Isolated singularities at `∞` split exclusively into removable, pole of unique positive order,
   and essential via `z ↦ f(1 / z)` at `0`;
4. Boundedness on `D'(∞; r)` implies removability and a finite limit at `∞`;
5. A pole of order `m` at `∞` has a unique constant-free polynomial principal part `p` of degree
   `m` such that `f - p` has a removable singularity (and finite limit) at `∞`;
6. Every entire nonpolynomial function has an essential singularity at `∞`;
7. The horizontal strip `{0 < Im z < 1}` has disconnected planar complement in `ℂ` yet connected
   spherical complement in `S²`. -/
theorem theorem13_1 :
    (∀ r : ℝ, infinityDisc r = ((↑) : ℂ → RiemannSphere) '' exteriorDisc r ∪ {∞}) ∧
    (∀ U : Set RiemannSphere, IsOpen U ↔
      (∀ z : ℂ, (z : RiemannSphere) ∈ U → ∃ r > 0, ((↑) : ℂ → RiemannSphere) '' ball z r ⊆ U) ∧
      ((∞ : RiemannSphere) ∈ U → ∃ r > 0, infinityDisc r ⊆ U)) ∧
    Topology.IsOpenEmbedding ((↑) : ℂ → RiemannSphere) ∧
    ((bookSphereHomeomorph ∞ : SphereAmbient) = !₂[0, 0, 1] ∧
      ∀ z : ℂ, (bookSphereHomeomorph (z : RiemannSphere) : SphereAmbient) =
        !₂[2 * z.re / (1 + ‖z‖ ^ 2), 2 * z.im / (1 + ‖z‖ ^ 2),
          (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2)]) ∧
    (∀ f : ℂ → ℂ, HasIsolatedSingularityAtInfinity f →
      (HasRemovableSingularityAtInfinity f ∨
        (∃ m : ℕ, HasPoleAtInfinity f m) ∨
        HasEssentialSingularityAtInfinity f) ∧
      ¬ (HasRemovableSingularityAtInfinity f ∧ ∃ m : ℕ, HasPoleAtInfinity f m)) ∧
    (∀ (f : ℂ → ℂ) (r M : ℝ), DifferentiableOn ℂ f (exteriorDisc r) →
      (∀ z ∈ exteriorDisc r, ‖f z‖ ≤ M) →
      ∃ c : ℂ, Tendsto f (cocompact ℂ) (𝓝 c) ∧
        AnalyticAt ℂ (Function.update (fun z : ℂ => f z⁻¹) 0 c) 0) ∧
    (∀ (f : ℂ → ℂ) (m : ℕ), HasPoleAtInfinity f m →
      ∃! p : Polynomial ℂ, p.coeff 0 = 0 ∧
        (p.natDegree = m ∧
          HasRemovableSingularityAtInfinity (fun z => f z - p.eval z))) ∧
    (∀ f : ℂ → ℂ, Differentiable ℂ f → (¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) →
      HasEssentialSingularityAtInfinity f) ∧
    (¬ IsPreconnected horizontalStripᶜ ∧ IsConnected (sphericalCompl horizontalStrip)) := by
  refine ⟨infinityDisc_eq, isOpen_riemannSphere_iff, finite_chart_open_embedding,
    ⟨bookSphereHomeomorph_infty, bookSphereHomeomorph_coe_one_add⟩,
    fun f hf => ⟨(singularity_at_infinity_trichotomy hf).1,
      (singularity_at_infinity_trichotomy hf).2.1⟩,
    fun f r M hf hb => removable_at_infinity_of_bounded hf hb,
    ?_, fun f hf hnp => entire_nonpolynomial_hasEssentialSingularityAtInfinity hf hnp,
    ⟨horizontalStrip_planar_complement_not_preconnected,
      horizontalStrip_spherical_complement_connected⟩⟩
  intro f m hpole
  obtain ⟨p, hdeg, h0, hrem⟩ := pole_at_infinity_has_principal_part hpole
  refine ⟨p, ⟨h0, hdeg, hrem⟩, ?_⟩
  rintro q ⟨hq0, _, hqrem⟩
  exact polynomial_principal_part_at_infinity_unique hq0 h0 hqrem hrem


/-! ## 13.2 Rational functions and partial-fraction decomposition -/

/-- Coprimality of distinct linear factors `X - C a` and `X - C b` over `ℂ`. -/
private theorem isCoprime_X_sub_C_of_ne {a b : ℂ} (hab : a ≠ b) :
    IsCoprime (Polynomial.X - Polynomial.C a) (Polynomial.X - Polynomial.C b) := by
  refine ⟨-Polynomial.C (a - b)⁻¹, Polynomial.C (a - b)⁻¹, ?_⟩
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  calc
    -Polynomial.C (a - b)⁻¹ * (Polynomial.X - Polynomial.C a) +
        Polynomial.C (a - b)⁻¹ * (Polynomial.X - Polynomial.C b)
      = Polynomial.C (a - b)⁻¹ * (Polynomial.C a - Polynomial.C b) := by ring
    _ = Polynomial.C ((a - b)⁻¹ * (a - b)) := by rw [← Polynomial.C_sub, ← Polynomial.C_mul]
    _ = 1 := by rw [inv_mul_cancel₀ hne, Polynomial.C_1]

/-- **Rudin RCA 13.2** (Rational functions, pole multiplicities, and partial fractions):
For any polynomial numerator `P : Polynomial ℂ` and nonzero denominator `Q : Polynomial ℂ`:
1. There exist relatively prime polynomials `P₁, Q₁` with `Q₁` monic (`Q₁ ≠ 0`), `Q₁ ∣ Q`, and
   `P * Q₁ = P₁ * Q`, so `P(z) / Q(z) = P₁(z) / Q₁(z)` whenever `Q(z) ≠ 0`;
2. Letting `S = Q₁.roots.toFinset` be the finite set of distinct zeros of `Q₁`, the reduced
   rational function `f₁(z) = P₁(z) / Q₁(z)` is meromorphic on `ℂ` with exact finite pole set `S`
   (`poleSet f₁ univ = {a | Q₁.eval a = 0}`), and at each `a ∈ S` has a pole of exact multiplicity
   `Q₁.rootMultiplicity a` (`meromorphicOrderAt f₁ a = -Q₁.rootMultiplicity a`);
3. There exist a polynomial `A₀` and polynomials `A : ℂ → Polynomial ℂ` such that for each `a ∈ S`,
   `(A a).eval 0 = 0` (`(A a).coeff 0 = 0`), `(A a).natDegree = Q₁.rootMultiplicity a`,
   `z ↦ (A a).eval ((z - a)⁻¹)` is the principal part of `f₁` at `a`, and
   `P₁(z) / Q₁(z) = A₀(z) + ∑ a ∈ S, (A a)((z - a)⁻¹)` for all `z` with `Q₁(z) ≠ 0`
   (hence `P(z) / Q(z) = A₀(z) + ∑ a ∈ S, (A a)((z - a)⁻¹)` and subtracting all finite principal
   parts leaves `A₀(z)` whenever `Q(z) ≠ 0`). -/
theorem theorem13_2 (P Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ∃ (P₁ Q₁ : Polynomial ℂ) (S : Finset ℂ) (A₀ : Polynomial ℂ) (A : ℂ → Polynomial ℂ),
      Q₁.Monic ∧
      IsCoprime P₁ Q₁ ∧
      Q₁ ∣ Q ∧
      P * Q₁ = P₁ * Q ∧
      (∀ a : ℂ, a ∈ S ↔ Q₁.eval a = 0) ∧
      (∀ a ∈ S, 0 < Q₁.rootMultiplicity a ∧ (A a).coeff 0 = 0 ∧ (A a).eval 0 = 0 ∧
        (A a).natDegree = Q₁.rootMultiplicity a ∧
        RudinRCA.Chapter10.IsPrincipalPart (fun z => (A a).eval ((z - a)⁻¹)) a ∧
        meromorphicOrderAt (fun z => P₁.eval z / Q₁.eval z) a =
          ((-(Q₁.rootMultiplicity a : ℤ)) : WithTop ℤ)) ∧
      RudinRCA.Chapter10.BookMeromorphicWithPoles
        (fun z => P₁.eval z / Q₁.eval z) univ (S : Set ℂ) ∧
      RudinRCA.Chapter10.poleSet (fun z => P₁.eval z / Q₁.eval z) univ =
        {a : ℂ | Q₁.eval a = 0} ∧
      (∀ z : ℂ, Q₁.eval z ≠ 0 →
        P₁.eval z / Q₁.eval z = A₀.eval z + ∑ a ∈ S, (A a).eval ((z - a)⁻¹)) ∧
      (∀ z : ℂ, Q.eval z ≠ 0 →
        Q₁.eval z ≠ 0 ∧
        P.eval z / Q.eval z = P₁.eval z / Q₁.eval z ∧
        P.eval z / Q.eval z = A₀.eval z + ∑ a ∈ S, (A a).eval ((z - a)⁻¹) ∧
        P.eval z / Q.eval z - ∑ a ∈ S, (A a).eval ((z - a)⁻¹) = A₀.eval z) := by
  classical
  let x : RatFunc ℂ :=
    algebraMap (Polynomial ℂ) (RatFunc ℂ) P / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q
  let P₁ : Polynomial ℂ := x.num
  let Q₁ : Polynomial ℂ := x.denom
  have hQ₁_monic : Q₁.Monic := x.monic_denom
  have hQ₁_ne : Q₁ ≠ 0 := x.denom_ne_zero
  have hcop : IsCoprime P₁ Q₁ := x.isCoprime_num_denom
  have hdvd : Q₁ ∣ Q := RatFunc.denom_div_dvd P Q
  have hPQ : P * Q₁ = P₁ * Q := by
    have hdiv : algebraMap (Polynomial ℂ) (RatFunc ℂ) P₁ /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) Q₁ =
        algebraMap (Polynomial ℂ) (RatFunc ℂ) P /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) Q := x.num_div_denom
    have hQ_map : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q ≠ 0 := RatFunc.algebraMap_ne_zero hQ
    have hQ₁_map : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q₁ ≠ 0 := RatFunc.algebraMap_ne_zero hQ₁_ne
    have hm := (div_eq_div_iff hQ₁_map hQ_map).mp hdiv
    rw [← map_mul, ← map_mul] at hm
    exact (RatFunc.algebraMap_injective ℂ hm).symm
  let S : Finset ℂ := Q₁.roots.toFinset
  have hmem_S : ∀ a : ℂ, a ∈ S ↔ Q₁.eval a = 0 := by
    intro a
    simp [S, Polynomial.mem_roots hQ₁_ne, Polynomial.IsRoot]
  let m : ℂ → ℕ := fun a => Q₁.rootMultiplicity a
  have hm_pos : ∀ a ∈ S, 0 < m a := by
    intro a ha
    exact (Polynomial.rootMultiplicity_pos hQ₁_ne).mpr ((hmem_S a).mp ha)
  have hQ₁_prod : Q₁ = ∏ a ∈ S, (Polynomial.X - Polynomial.C a) ^ m a := by
    have hsp := (IsAlgClosed.splits Q₁).eq_prod_roots_of_monic hQ₁_monic
    rw [Polynomial.prod_multiset_root_eq_finset_root] at hsp
    exact hsp
  have hP₁_ne_zero_on_S : ∀ a ∈ S, P₁.eval a ≠ 0 := by
    intro a ha hp0
    obtain ⟨u, v, huv⟩ := hcop
    have hev := congrArg (Polynomial.eval a) huv
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      hp0, (hmem_S a).mp ha, mul_zero, add_zero] at hev
    exact zero_ne_one hev
  have hg_monic : ∀ a ∈ S, (Polynomial.X - Polynomial.C a).Monic :=
    fun a _ => Polynomial.monic_X_sub_C a
  have hg_cop : Set.Pairwise (S : Set ℂ)
      (fun a b => IsCoprime (Polynomial.X - Polynomial.C a) (Polynomial.X - Polynomial.C b)) :=
    fun a _ b _ hab => isCoprime_X_sub_C_of_ne hab
  obtain ⟨A₀, r, hr_deg, hP₁_eq⟩ :=
    Polynomial.eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow P₁ hg_monic hg_cop m
  have hr_const : ∀ a ∈ S, ∀ j : Fin (m a), r a j = Polynomial.C ((r a j).coeff 0) := by
    intro a ha j
    have hd := hr_deg a ha j
    rw [Polynomial.degree_X_sub_C] at hd
    apply Polynomial.eq_C_of_degree_le_zero
    cases hdeg : (r a j).degree with
    | bot => exact bot_le
    | coe d =>
      rw [hdeg] at hd
      have hd0 : d < 1 := WithBot.coe_lt_coe.mp hd
      have : d = 0 := by omega
      simp [this]
  let A : ℂ → Polynomial ℂ := fun a =>
    ∑ j : Fin (m a), Polynomial.monomial (m a - j.1) ((r a j).coeff 0)
  have hA_coeff0 : ∀ a ∈ S, (A a).coeff 0 = 0 := by
    intro a _
    simp only [A, Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro j _
    have hne : m a - j.1 ≠ 0 := by have := j.isLt; omega
    simp [Polynomial.coeff_monomial, hne]
  have hA_eval0 : ∀ a ∈ S, (A a).eval 0 = 0 := by
    intro a ha
    rw [← Polynomial.coeff_zero_eq_eval_zero, hA_coeff0 a ha]
  have hlead_ne : ∀ (a : ℂ) (ha : a ∈ S), (r a ⟨0, hm_pos a ha⟩).coeff 0 ≠ 0 := by
    intro a ha hc0
    have hev := congrArg (Polynomial.eval a) hP₁_eq
    rw [← hQ₁_prod] at hev
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_finsetSum,
      Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, (hmem_S a).mp ha, mul_zero, zero_add] at hev
    have hsum_eq : (∑ i ∈ S, ∑ j : Fin (m i),
        (r i j).eval a * (a - i) ^ j.1 * ∏ k ∈ S.erase i, (a - k) ^ m k) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j _
      by_cases hia : i = a
      · subst hia
        by_cases hj0 : j.1 = 0
        · have hj_eq : j = ⟨0, hm_pos i hi⟩ := Fin.ext hj0
          rw [hj_eq, hr_const i hi ⟨0, hm_pos i hi⟩, Polynomial.eval_C, hc0]
          ring
        · rw [sub_self, zero_pow hj0]
          ring
      · have ha_mem : a ∈ S.erase i := Finset.mem_erase.mpr ⟨Ne.symm hia, ha⟩
        have hprod0 : (∏ k ∈ S.erase i, (a - k) ^ m k) = 0 :=
          Finset.prod_eq_zero ha_mem (by rw [sub_self, zero_pow (hm_pos a ha).ne'])
        rw [hprod0, mul_zero]
    rw [hsum_eq] at hev
    exact hP₁_ne_zero_on_S a ha hev
  have hA_deg : ∀ a ∈ S, (A a).natDegree = m a := by
    intro a ha
    have hle : (A a).natDegree ≤ m a := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j _
      exact (Polynomial.natDegree_monomial_le _).trans (Nat.sub_le (m a) j.1)
    have hcm : (A a).coeff (m a) = (r a ⟨0, hm_pos a ha⟩).coeff 0 := by
      simp only [A, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single ⟨0, hm_pos a ha⟩]
      · simp
      · intro j _ hjne
        have hj0 : j.1 ≠ 0 := fun h => hjne (Fin.ext h)
        have hne : m a - j.1 ≠ m a := by have := hm_pos a ha; omega
        simp [Polynomial.coeff_monomial, hne]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    refine hle.antisymm (Polynomial.le_natDegree_of_ne_zero ?_)
    rw [hcm]
    exact hlead_ne a ha
  have hA_eval_inv : ∀ a ∈ S, ∀ z : ℂ, z - a ≠ 0 →
      (A a).eval ((z - a)⁻¹) * (z - a) ^ m a =
        ∑ j : Fin (m a), (r a j).eval z * (z - a) ^ j.1 := by
    intro a ha z hza
    simp only [A, Polynomial.eval_finsetSum, Polynomial.eval_monomial, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    have hr_ev : (r a j).eval z = (r a j).coeff 0 := by
      conv_lhs => rw [hr_const a ha j]
      exact Polynomial.eval_C
    rw [hr_ev]
    have hsub : m a - j.1 + j.1 = m a := Nat.sub_add_cancel j.isLt.le
    have hpow_split : (z - a) ^ m a = (z - a) ^ (m a - j.1) * (z - a) ^ j.1 := by
      rw [← pow_add, hsub]
    calc
      (r a j).coeff 0 * ((z - a)⁻¹) ^ (m a - j.1) * (z - a) ^ m a
        = (r a j).coeff 0 *
            (((z - a)⁻¹ ^ (m a - j.1) * (z - a) ^ (m a - j.1)) * (z - a) ^ j.1) := by
            rw [hpow_split]; ring
      _ = (r a j).coeff 0 * (((z - a)⁻¹ * (z - a)) ^ (m a - j.1) * (z - a) ^ j.1) := by
            rw [← mul_pow]
      _ = (r a j).coeff 0 * (z - a) ^ j.1 := by
            rw [inv_mul_cancel₀ hza, one_pow, one_mul]
  have hpf_Q₁ : ∀ z : ℂ, Q₁.eval z ≠ 0 →
      P₁.eval z / Q₁.eval z = A₀.eval z + ∑ a ∈ S, (A a).eval ((z - a)⁻¹) := by
    intro z hzQ₁
    have hza : ∀ a ∈ S, z - a ≠ 0 := by
      intro a ha h0
      exact hzQ₁ (by rw [sub_eq_zero.mp h0, (hmem_S a).mp ha])
    rw [div_eq_iff hzQ₁]
    have hev := congrArg (Polynomial.eval z) hP₁_eq
    have hQ₁_ev : Q₁.eval z = ∏ a ∈ S, (z - a) ^ m a := by
      rw [hQ₁_prod]
      simp [Polynomial.eval_prod]
    rw [hev]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_finsetSum,
      Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    rw [add_mul, hQ₁_ev, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.mul_prod_erase S _ ha, ← mul_assoc, hA_eval_inv a ha z (hza a ha),
      Finset.sum_mul]
  have hA_prin : ∀ a ∈ S,
      RudinRCA.Chapter10.IsPrincipalPart (fun z => (A a).eval ((z - a)⁻¹)) a := by
    intro a ha
    let coeff_fn : ℕ → ℂ := fun k => (A a).coeff k
    refine ⟨m a, coeff_fn, hm_pos a ha, ?_, ?_⟩
    · dsimp [coeff_fn]
      have hdeg := hA_deg a ha
      have hne0 : A a ≠ 0 := by
        intro h0
        have := hm_pos a ha
        rw [h0, Polynomial.natDegree_zero] at hdeg
        omega
      rw [← hdeg]
      exact Polynomial.leadingCoeff_ne_zero.mpr hne0
    · intro z
      dsimp only
      rw [Polynomial.eval_eq_sum_range, hA_deg a ha]
      have hsplit : Finset.range (m a + 1) = insert 0 (Finset.Icc 1 (m a)) := by
        ext k
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [hsplit, Finset.sum_insert (by simp), hA_coeff0 a ha, zero_mul, zero_add]
  let f₁ : ℂ → ℂ := fun z => P₁.eval z / Q₁.eval z
  have hf₁_order : ∀ a ∈ S,
      meromorphicOrderAt f₁ a = ((-(m a : ℤ)) : WithTop ℤ) := by
    intro a ha
    let R_a : Polynomial ℂ := ∏ b ∈ S.erase a, (Polynomial.X - Polynomial.C b) ^ m b
    have hQ₁_fac : Q₁ = (Polynomial.X - Polynomial.C a) ^ m a * R_a := by
      rw [hQ₁_prod, ← Finset.mul_prod_erase S _ ha]
    have hRa_ne : R_a.eval a ≠ 0 := by
      simp only [R_a, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
      rw [Finset.prod_ne_zero_iff]
      intro b hb
      exact pow_ne_zero _ (sub_ne_zero.mpr (Finset.mem_erase.mp hb).1.symm)
    have hpoly_an : ∀ p : Polynomial ℂ, AnalyticAt ℂ (fun z => p.eval z) a :=
      fun p => p.differentiable.differentiableOn.analyticOnNhd isOpen_univ a (mem_univ a)
    let u : ℂ → ℂ := fun z => P₁.eval z / R_a.eval z
    have hu_an : AnalyticAt ℂ u a := (hpoly_an P₁).div (hpoly_an R_a) hRa_ne
    have hu_a : u a ≠ 0 := div_ne_zero (hP₁_ne_zero_on_S a ha) hRa_ne
    have hf₁_mero : MeromorphicAt f₁ a :=
      (hpoly_an P₁).meromorphicAt.div (hpoly_an Q₁).meromorphicAt
    have hgoal : meromorphicOrderAt f₁ a = ((-(m a : ℤ) : ℤ) : WithTop ℤ) ↔ _ :=
      meromorphicOrderAt_eq_int_iff hf₁_mero
    refine hgoal.mpr ⟨u, hu_an, hu_a, ?_⟩
    have hRa_ev : ∀ᶠ z in 𝓝 a, R_a.eval z ≠ 0 :=
      R_a.continuous.continuousAt.eventually_ne hRa_ne
    filter_upwards [nhdsWithin_le_nhds hRa_ev, self_mem_nhdsWithin] with z hzR hza
    dsimp [f₁, u]
    have hQ₁_z : Q₁.eval z = (z - a) ^ m a * R_a.eval z := by
      rw [hQ₁_fac]
      simp
    rw [hQ₁_z, zpow_neg, zpow_natCast]
    have hpow_ne : (z - a) ^ m a ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza)
    field_simp [hpow_ne, hzR]
  have hf₁_mero_book : RudinRCA.Chapter10.BookMeromorphicWithPoles f₁ univ (S : Set ℂ) := by
    refine ⟨isOpen_univ, subset_univ _, ?_, ?_, ?_⟩
    · intro z _ hacc
      let U : Set ℂ := (↑(S.erase z) : Set ℂ)ᶜ
      have hU_open : IsOpen U := (S.erase z).finite_toSet.isClosed.isOpen_compl
      have hzU : z ∈ U := by simp [U]
      obtain ⟨w, ⟨hwU, hwS⟩, hwne⟩ := accPt_iff_nhds.mp hacc U (hU_open.mem_nhds hzU)
      exact hwU (Finset.mem_erase.mpr ⟨hwne, hwS⟩)
    · intro z hz
      have hzQ₁ : Q₁.eval z ≠ 0 := fun h0 => hz.2 ((hmem_S z).mpr h0)
      exact P₁.differentiableAt.div Q₁.differentiableAt hzQ₁
    · intro a ha
      have haS : a ∈ S := ha
      let V : Set ℂ := (↑(S.erase a) : Set ℂ)ᶜ
      have hV_open : IsOpen V := (S.erase a).finite_toSet.isClosed.isOpen_compl
      have haV : a ∈ V := by simp [V]
      have hf₁_V : RudinRCA.Chapter10.HolomorphicOn f₁ (V \ {a}) := by
        intro z hz
        have hzQ₁ : Q₁.eval z ≠ 0 := by
          intro h0
          have hzS : z ∈ S := (hmem_S z).mpr h0
          by_cases hza : z = a
          · exact hz.2 hza
          · exact hz.1 (Finset.mem_erase.mpr ⟨hza, hzS⟩)
        exact P₁.differentiableAt.div Q₁.differentiableAt hzQ₁
      let g_a : ℂ → ℂ := fun z => A₀.eval z + ∑ b ∈ S.erase a, (A b).eval ((z - b)⁻¹)
      have hga_holo : RudinRCA.Chapter10.HolomorphicOn g_a V := by
        intro z hz
        refine A₀.differentiableAt.add ?_
        have hd := DifferentiableAt.sum (u := S.erase a)
          (A := fun (b : ℂ) (w : ℂ) => (A b).eval ((w - b)⁻¹)) fun b hb => by
            have hzb : z - b ≠ 0 := sub_ne_zero.mpr fun hEq => hz (hEq ▸ hb)
            exact ((A b).differentiableAt).comp z ((differentiableAt_id.sub_const b).inv hzb)
        rwa [Finset.sum_fn] at hd
      refine ⟨V, hV_open, haV, subset_univ _, ⟨hV_open, haV, hf₁_V⟩,
        g_a, fun z => (A a).eval ((z - a)⁻¹), hga_holo, hA_prin a haS, ?_⟩
      intro z hz
      have hzQ₁ : Q₁.eval z ≠ 0 := by
        intro h0
        have hzS : z ∈ S := (hmem_S z).mpr h0
        by_cases hza : z = a
        · exact hz.2 hza
        · exact hz.1 (Finset.mem_erase.mpr ⟨hza, hzS⟩)
      dsimp [f₁, g_a]
      rw [hpf_Q₁ z hzQ₁, ← Finset.add_sum_erase S _ haS]
      ring
  have hpole_set : RudinRCA.Chapter10.poleSet f₁ univ = {a : ℂ | Q₁.eval a = 0} := by
    rw [← (RudinRCA.Chapter10.theorem10_41 hf₁_mero_book).2.1]
    ext a
    exact hmem_S a
  refine ⟨P₁, Q₁, S, A₀, A, hQ₁_monic, hcop, hdvd, hPQ, hmem_S,
    fun a ha => ⟨hm_pos a ha, hA_coeff0 a ha, hA_eval0 a ha, hA_deg a ha,
      hA_prin a ha, hf₁_order a ha⟩,
    hf₁_mero_book, hpole_set, hpf_Q₁, ?_⟩
  intro z hzQ
  have hzQ₁ : Q₁.eval z ≠ 0 := by
    obtain ⟨C_fac, hfac⟩ := hdvd
    intro h0
    apply hzQ
    rw [hfac, Polynomial.eval_mul, h0, zero_mul]
  have heq_div : P.eval z / Q.eval z = P₁.eval z / Q₁.eval z := by
    rw [div_eq_div_iff hzQ hzQ₁]
    have hev := congrArg (Polynomial.eval z) hPQ
    simpa [Polynomial.eval_mul] using hev
  refine ⟨hzQ₁, heq_div, heq_div.trans (hpf_Q₁ z hzQ₁), ?_⟩
  rw [heq_div, hpf_Q₁ z hzQ₁, add_sub_cancel_right]


/-! ## 13.3 Compact exhaustion with spherical complement condition -/

/-- Connectedness of `infinityDisc r` for `r ≥ 0`. -/
theorem isConnected_infinityDisc {r : ℝ} (hr : 0 ≤ r) :
    IsConnected (infinityDisc r) := by
  have hext : exteriorDisc r = (closedBall (0 : ℂ) r)ᶜ := by
    ext z
    simp [exteriorDisc, mem_closedBall, dist_zero_right]
  have hconn : IsConnected (exteriorDisc r) := by
    rw [hext]
    exact RudinRCA.Chapter10.isConnected_compl_closedBall 0 hr
  have hunb : ∀ R > 0, ∃ z ∈ exteriorDisc r, R < ‖z‖ := by
    intro R hR
    refine ⟨((max r R + 1 : ℝ) : ℂ), ?_, ?_⟩
    · change r < ‖((max r R + 1 : ℝ) : ℂ)‖
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith [le_max_left r R] : 0 < max r R + 1)]
      linarith [le_max_left r R]
    · simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith [le_max_right r R] : 0 < max r R + 1)]
      linarith [le_max_right r R]
  have heq : infinityDisc r = insert (∞ : RiemannSphere) (((↑) : ℂ → RiemannSphere) '' exteriorDisc r) := by
    rw [infinityDisc_eq, union_comm, singleton_union]
  rw [heq]
  exact isConnected_insert_infinity hconn hunb

/-- Rudin's explicit compact exhaustion sets `K_n` for an arbitrary open set `Ω ⊆ ℂ` (RCA 13.3). -/
def exhaustionSet (Ω : Set ℂ) (n : ℕ) : Set ℂ :=
  {z : ℂ | ‖z‖ ≤ (n : ℝ) + 1 ∧ ∀ w ∈ Ωᶜ, (1 : ℝ) / ((n : ℝ) + 1) ≤ dist z w}

theorem isCompact_exhaustionSet (Ω : Set ℂ) (n : ℕ) :
    IsCompact (exhaustionSet Ω n) := by
  have hcl : IsClosed (exhaustionSet Ω n) := by
    have heq : exhaustionSet Ω n =
        closedBall (0 : ℂ) ((n : ℝ) + 1) ∩
          ⋂ w ∈ Ωᶜ, {z : ℂ | (1 : ℝ) / ((n : ℝ) + 1) ≤ dist z w} := by
      ext z
      simp [exhaustionSet, mem_closedBall, dist_zero_right]
    rw [heq]
    exact isClosed_closedBall.inter
      (isClosed_biInter fun w _ => isClosed_le continuous_const (continuous_id.dist continuous_const))
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 1)) hcl ?_
  intro z hz
  simpa [mem_closedBall, dist_zero_right] using hz.1

theorem exhaustionSet_subset (Ω : Set ℂ) (n : ℕ) :
    exhaustionSet Ω n ⊆ Ω := by
  intro z hz
  by_contra hzΩ
  have h := hz.2 z hzΩ
  rw [dist_self] at h
  have hpos : (0 : ℝ) < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  linarith

theorem exhaustionSet_subset_interior_succ (Ω : Set ℂ) (n : ℕ) :
    exhaustionSet Ω n ⊆ interior (exhaustionSet Ω (n + 1)) := by
  intro z hz
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  let δ : ℝ := (1 : ℝ) / ((n : ℝ) + 1) - (1 : ℝ) / ((n : ℝ) + 2)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith) |> sub_pos.mpr
  have hδ_le1 : δ ≤ 1 := by
    dsimp [δ]
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
    have h2 : 0 ≤ (1 : ℝ) / ((n : ℝ) + 2) := by positivity
    linarith
  refine ⟨δ, hδ_pos, fun y hy => ⟨?_, ?_⟩⟩
  · have hyz : ‖y - z‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hy
    have htri : ‖y‖ ≤ ‖z‖ + ‖y - z‖ := norm_le_insert' y z |> fun _ => by
      calc ‖y‖ = ‖z + (y - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖y - z‖ := norm_add_le _ _
    push_cast
    linarith [hz.1]
  · intro w hw
    have hyz : dist z y < δ := by simpa [Metric.mem_ball, dist_comm] using hy
    have hzw : (1 : ℝ) / ((n : ℝ) + 1) ≤ dist z w := hz.2 w hw
    have htri : dist z w ≤ dist z y + dist y w := dist_triangle z y w
    push_cast
    have : (1 : ℝ) / ((n : ℝ) + 1 + 1) = (1 : ℝ) / ((n : ℝ) + 2) := by ring
    rw [this]
    dsimp [δ] at hyz
    linarith

theorem exhaustionSet_mono (Ω : Set ℂ) : Monotone (exhaustionSet Ω) := by
  refine monotone_nat_of_le_succ fun n => ?_
  exact (exhaustionSet_subset_interior_succ Ω n).trans interior_subset

theorem iUnion_exhaustionSet {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    (⋃ n : ℕ, exhaustionSet Ω n) = Ω := by
  apply Subset.antisymm
  · exact iUnion_subset (exhaustionSet_subset Ω)
  · intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ z hz
    obtain ⟨N, hN⟩ := exists_nat_gt (max ‖z‖ (1 / ε))
    refine mem_iUnion.mpr ⟨N, ?_, ?_⟩
    · have : ‖z‖ < N := (le_max_left _ _).trans_lt hN
      linarith
    · intro w hw
      have hdist : ε ≤ dist z w := by
        by_contra hlt
        push Not at hlt
        exact hw (hball (by simpa [Metric.mem_ball, dist_comm] using hlt))
      have hNε : 1 / ε < (N : ℝ) + 1 := by
        have : 1 / ε < N := (le_max_right _ _).trans_lt hN
        linarith
      have hle : (1 : ℝ) / ((N : ℝ) + 1) ≤ ε := by
        rw [div_le_iff₀ (by positivity)]
        have := (div_lt_iff₀ hε).mp hNε
        linarith
      exact hle.trans hdist

theorem exists_subset_exhaustionSet_of_isCompact {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ n : ℕ, K ⊆ exhaustionSet Ω n := by
  have hcov : K ⊆ ⋃ n : ℕ, interior (exhaustionSet Ω (n + 1)) := by
    intro z hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp ((iUnion_exhaustionSet hΩ).symm ▸ hKΩ hz)
    exact mem_iUnion.mpr ⟨n, exhaustionSet_subset_interior_succ Ω n hn⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun n : ℕ => interior (exhaustionSet Ω (n + 1)))
    (fun _ => isOpen_interior) hcov
  refine ⟨s.sup id + 1, fun z hz => ?_⟩
  obtain ⟨n, hn_mem, hzn⟩ := mem_iUnion₂.mp (hs hz)
  have hle : n + 1 ≤ s.sup id + 1 := Nat.add_le_add_right (Finset.le_sup (f := id) hn_mem) 1
  exact exhaustionSet_mono Ω hle (interior_subset hzn)

theorem exhaustionSet_sphericalCompl_component (Ω : Set ℂ) (n : ℕ) :
    ∀ x ∈ sphericalCompl (exhaustionSet Ω n),
      ∃ p ∈ sphericalCompl Ω,
        connectedComponentIn (sphericalCompl Ω) p ⊆
          connectedComponentIn (sphericalCompl (exhaustionSet Ω n)) x := by
  have hsub_compl : sphericalCompl Ω ⊆ sphericalCompl (exhaustionSet Ω n) :=
    compl_subset_compl.mpr (image_mono (exhaustionSet_subset Ω n))
  intro x hx
  induction x using OnePoint.rec with
  | infty =>
    refine ⟨∞, infinity_mem_sphericalCompl Ω, ?_⟩
    exact connectedComponentIn_mono ∞ hsub_compl
  | coe z =>
    have hz : z ∉ exhaustionSet Ω n := (coe_mem_sphericalCompl z _).mp hx
    change ¬ (‖z‖ ≤ (n : ℝ) + 1 ∧ ∀ w ∈ Ωᶜ, (1 : ℝ) / ((n : ℝ) + 1) ≤ dist z w) at hz
    push Not at hz
    by_cases hnorm : (n : ℝ) + 1 < ‖z‖
    · refine ⟨∞, infinity_mem_sphericalCompl Ω, ?_⟩
      have hD_sub : infinityDisc ((n : ℝ) + 1) ⊆ sphericalCompl (exhaustionSet Ω n) := by
        intro q hq
        induction q using OnePoint.rec with
        | infty => simp
        | coe y =>
          rw [coe_mem_infinityDisc] at hq
          rw [coe_mem_sphericalCompl]
          intro hy
          linarith [hy.1]
      have hD_pre : IsPreconnected (infinityDisc ((n : ℝ) + 1)) :=
        (isConnected_infinityDisc (by positivity)).isPreconnected
      have hzD : (z : RiemannSphere) ∈ infinityDisc ((n : ℝ) + 1) :=
        (coe_mem_infinityDisc z _).mpr hnorm
      have hinf_comp : (∞ : RiemannSphere) ∈
          connectedComponentIn (sphericalCompl (exhaustionSet Ω n)) (z : RiemannSphere) :=
        hD_pre.subset_connectedComponentIn hzD hD_sub (infinity_mem_infinityDisc _)
      exact (connectedComponentIn_mono ∞ hsub_compl).trans
        (connectedComponentIn_eq hinf_comp).symm.subset
    · obtain ⟨w, hw, hdist⟩ := hz (le_of_not_gt hnorm)
      refine ⟨(w : RiemannSphere), (coe_mem_sphericalCompl w Ω).mpr hw, ?_⟩
      let B : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' ball w ((1 : ℝ) / ((n : ℝ) + 1))
      have hB_pre : IsPreconnected B :=
        (convex_ball w _).isPreconnected.image _ OnePoint.continuous_coe.continuousOn
      have hB_sub : B ⊆ sphericalCompl (exhaustionSet Ω n) := by
        rintro _ ⟨y, hy, rfl⟩
        rw [coe_mem_sphericalCompl]
        intro hyK
        have := hyK.2 w hw
        rw [Metric.mem_ball] at hy
        linarith
      have hzB : (z : RiemannSphere) ∈ B := mem_image_of_mem _ (Metric.mem_ball.mpr hdist)
      have hwB : (w : RiemannSphere) ∈ B :=
        mem_image_of_mem _ (Metric.mem_ball_self (by positivity))
      have hw_comp : (w : RiemannSphere) ∈
          connectedComponentIn (sphericalCompl (exhaustionSet Ω n)) (z : RiemannSphere) :=
        hB_pre.subset_connectedComponentIn hzB hB_sub hwB
      exact (connectedComponentIn_mono (w : RiemannSphere) hsub_compl).trans
        (connectedComponentIn_eq hw_comp).symm.subset

/-- **Rudin RCA 13.3** (Compact exhaustion with spherical complement condition):
Every open set `Ω ⊆ ℂ` (without any connectedness assumption) is the union of compact subsets
`K_n ⊆ Ω` (`n : ℕ`) such that:
- `(a)` `K_n ⊆ interior (K_{n+1})` for every `n`;
- `(b)` every compact `K ⊆ Ω` satisfies `K ⊆ K_n` for some `n`;
- `(c)` every connected component of `S² \ K_n` contains a connected component of `S² \ Ω`. -/
theorem theorem13_3 {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    ∃ K : ℕ → Set ℂ,
      (∀ n : ℕ, IsCompact (K n) ∧ K n ⊆ Ω) ∧
      (⋃ n : ℕ, K n) = Ω ∧
      (∀ n : ℕ, K n ⊆ interior (K (n + 1))) ∧
      (∀ C : Set ℂ, IsCompact C → C ⊆ Ω → ∃ n : ℕ, C ⊆ K n) ∧
      (∀ (n : ℕ) (x : RiemannSphere), x ∈ sphericalCompl (K n) →
        ∃ p ∈ sphericalCompl Ω,
          connectedComponentIn (sphericalCompl Ω) p ⊆
            connectedComponentIn (sphericalCompl (K n)) x) :=
  ⟨exhaustionSet Ω,
    fun n => ⟨isCompact_exhaustionSet Ω n, exhaustionSet_subset Ω n⟩,
    iUnion_exhaustionSet hΩ,
    exhaustionSet_subset_interior_succ Ω,
    fun _ hC hCΩ => exists_subset_exhaustionSet_of_isCompact hΩ hC hCΩ,
    exhaustionSet_sphericalCompl_component Ω⟩


/-! ## 13.4 Balanced collections of oriented intervals and polygonal cycles -/

/-- Out-degree of vertex `v` in a finite list of directed intervals `L`. -/
def intervalOutDeg (L : List (ℂ × ℂ)) (v : ℂ) : ℕ :=
  open Classical in (L.filter (fun e => decide (e.1 = v))).length

/-- In-degree of vertex `v` in a finite list of directed intervals `L`. -/
def intervalInDeg (L : List (ℂ × ℂ)) (v : ℂ) : ℕ :=
  open Classical in (L.filter (fun e => decide (e.2 = v))).length

/-- A finite collection of directed intervals `L` (with multiplicity) is *balanced* if at every
vertex `v : ℂ`, the number of intervals starting at `v` equals the number ending at `v` (RCA 13.4). -/
def IsBalancedIntervals (L : List (ℂ × ℂ)) : Prop :=
  ∀ v : ℂ, intervalOutDeg L v = intervalInDeg L v

/-- Formal chain of oriented line segments corresponding to a list of directed intervals `L`. -/
def intervalsChain (L : List (ℂ × ℂ)) : RudinRCA.Chapter10.BookChain :=
  L.map (fun e => RudinRCA.Chapter10.orientedSegment e.1 e.2)

/-- A nonempty list of directed intervals `W` forms a contiguous polygonal walk from `a` to `b`. -/
inductive IsPolygonalWalkFromTo : List (ℂ × ℂ) → ℂ → ℂ → Prop
  | single (a b : ℂ) : IsPolygonalWalkFromTo [(a, b)] a b
  | cons {a m b : ℂ} {W : List (ℂ × ℂ)} :
      IsPolygonalWalkFromTo W m b → IsPolygonalWalkFromTo ((a, m) :: W) a b

/-- A nonempty closed polygonal edge-walk `C` (contiguous directed intervals closing at its start). -/
def IsClosedPolygonalWalk (C : List (ℂ × ℂ)) : Prop :=
  ∃ v : ℂ, IsPolygonalWalkFromTo C v v

private theorem isPolygonalWalkFromTo_nonempty {W : List (ℂ × ℂ)} {a b : ℂ}
    (h : IsPolygonalWalkFromTo W a b) : W ≠ [] := by
  cases h <;> simp

private theorem isPolygonalWalkFromTo_append_single {W : List (ℂ × ℂ)} {a b c : ℂ}
    (h : IsPolygonalWalkFromTo W a b) :
    IsPolygonalWalkFromTo (W ++ [(b, c)]) a c := by
  induction h with
  | single a b => exact IsPolygonalWalkFromTo.cons (IsPolygonalWalkFromTo.single b c)
  | cons hrest ih => exact IsPolygonalWalkFromTo.cons ih

private theorem intervalOutDeg_nil (v : ℂ) : intervalOutDeg [] v = 0 := by
  simp [intervalOutDeg]

private theorem intervalInDeg_nil (v : ℂ) : intervalInDeg [] v = 0 := by
  simp [intervalInDeg]

private theorem intervalOutDeg_cons (e : ℂ × ℂ) (L : List (ℂ × ℂ)) (v : ℂ) :
    intervalOutDeg (e :: L) v = (open Classical in if e.1 = v then 1 else 0) + intervalOutDeg L v := by
  classical
  by_cases h : e.1 = v <;> simp [intervalOutDeg, h, Nat.add_comm]

private theorem intervalInDeg_cons (e : ℂ × ℂ) (L : List (ℂ × ℂ)) (v : ℂ) :
    intervalInDeg (e :: L) v = (open Classical in if e.2 = v then 1 else 0) + intervalInDeg L v := by
  classical
  by_cases h : e.2 = v <;> simp [intervalInDeg, h, Nat.add_comm]

private theorem intervalOutDeg_append (L₁ L₂ : List (ℂ × ℂ)) (v : ℂ) :
    intervalOutDeg (L₁ ++ L₂) v = intervalOutDeg L₁ v + intervalOutDeg L₂ v := by
  classical
  simp [intervalOutDeg, List.filter_append]

private theorem intervalInDeg_append (L₁ L₂ : List (ℂ × ℂ)) (v : ℂ) :
    intervalInDeg (L₁ ++ L₂) v = intervalInDeg L₁ v + intervalInDeg L₂ v := by
  classical
  simp [intervalInDeg, List.filter_append]

private theorem intervalOutDeg_perm {L₁ L₂ : List (ℂ × ℂ)} (hp : L₁.Perm L₂) (v : ℂ) :
    intervalOutDeg L₁ v = intervalOutDeg L₂ v := by
  classical
  exact (hp.filter _).length_eq

private theorem intervalInDeg_perm {L₁ L₂ : List (ℂ × ℂ)} (hp : L₁.Perm L₂) (v : ℂ) :
    intervalInDeg L₁ v = intervalInDeg L₂ v := by
  classical
  exact (hp.filter _).length_eq

private theorem walk_deg_diff {W : List (ℂ × ℂ)} {a b : ℂ}
    (hW : IsPolygonalWalkFromTo W a b) (v : ℂ) :
    (intervalOutDeg W v : ℤ) - (intervalInDeg W v : ℤ) =
      (open Classical in if a = v then 1 else 0) - (open Classical in if b = v then 1 else 0) := by
  classical
  induction hW with
  | single a b =>
    rw [intervalOutDeg_cons, intervalOutDeg_nil, intervalInDeg_cons, intervalInDeg_nil]
    simp
  | @cons a m b W hrest ih =>
    rw [intervalOutDeg_cons, intervalInDeg_cons]
    push_cast
    linarith [ih]

/-- Greedy walk extension: from an open polygonal walk `W` (`a → b`) and remaining edges `M` whose
union `W ++ M` is balanced, extract a closed polygonal walk `C` and balanced remainder `R` with
`(W ++ M).Perm (C ++ R)`. -/
private theorem extend_walk_to_closed :
    ∀ (k : ℕ) (W M : List (ℂ × ℂ)) (a b : ℂ),
      M.length = k →
      IsPolygonalWalkFromTo W a b →
      IsBalancedIntervals (W ++ M) →
      ∃ C R : List (ℂ × ℂ),
        IsClosedPolygonalWalk C ∧ (W ++ M).Perm (C ++ R) ∧ IsBalancedIntervals R
  | 0, W, M, a, b, hlen, hW, hbal => by
    classical
    have hM : M = [] := List.eq_nil_of_length_eq_zero hlen
    subst hM
    rw [List.append_nil] at hbal
    have hab : a = b := by
      by_contra hne
      have hne' : b ≠ a := Ne.symm hne
      have hd := walk_deg_diff hW a
      rw [hbal a, sub_self] at hd
      simp only [↓reduceIte, hne'] at hd
      omega
    subst hab
    exact ⟨W, [], ⟨a, hW⟩, List.Perm.refl _, fun _ => rfl⟩
  | k + 1, W, M, a, b, hlen, hW, hbal => by
    classical
    by_cases hab : a = b
    · subst hab
      refine ⟨W, M, ⟨a, hW⟩, List.Perm.refl _, fun v => ?_⟩
      have hd := walk_deg_diff hW v
      simp only [sub_self] at hd
      have htot := hbal v
      rw [intervalOutDeg_append, intervalInDeg_append] at htot
      omega
    · have hout_pos : 0 < intervalOutDeg M b := by
        have hd := walk_deg_diff hW b
        simp only [hab, ↓reduceIte] at hd
        have htot := hbal b
        rw [intervalOutDeg_append, intervalInDeg_append] at htot
        omega
      have hfilt_ne : M.filter (fun e => decide (e.1 = b)) ≠ [] :=
        List.ne_nil_of_length_pos hout_pos
      obtain ⟨e, _, he_cons⟩ := List.exists_cons_of_ne_nil hfilt_ne
      have he_mem_filt : e ∈ M.filter (fun e => decide (e.1 = b)) := by
        rw [he_cons]; exact List.mem_cons_self
      obtain ⟨he_M, he_fst⟩ := List.mem_filter.mp he_mem_filt
      have he1 : e.1 = b := of_decide_eq_true he_fst
      let M' : List (ℂ × ℂ) := M.erase e
      have hpermM : M.Perm (e :: M') := List.perm_cons_erase he_M
      have hlen' : M'.length = k := by
        have := hpermM.length_eq
        simp at this
        omega
      have he_eq : e = (b, e.2) := Prod.ext he1 rfl
      let W' : List (ℂ × ℂ) := W ++ [(b, e.2)]
      have hW' : IsPolygonalWalkFromTo W' a e.2 :=
        isPolygonalWalkFromTo_append_single hW
      have hperm_tot : (W ++ M).Perm (W' ++ M') := by
        have hp1 : (W ++ M).Perm (W ++ (e :: M')) := hpermM.append_left W
        have heq_list : W ++ (e :: M') = W' ++ M' := by
          dsimp [W']
          rw [he_eq]
          simp [List.append_assoc]
        rwa [heq_list] at hp1
      have hbal' : IsBalancedIntervals (W' ++ M') := by
        intro v
        rw [← intervalOutDeg_perm hperm_tot v, ← intervalInDeg_perm hperm_tot v]
        exact hbal v
      obtain ⟨C, R, hC, hCR, hbalR⟩ := extend_walk_to_closed k W' M' a e.2 hlen' hW' hbal'
      exact ⟨C, R, hC, hperm_tot.trans hCR, hbalR⟩

/-- Partition any balanced finite list of directed intervals (up to permutation, preserving
multiplicities) into closed polygonal edge-walks. -/
theorem balancedIntervals_partition :
    ∀ (n : ℕ) (L : List (ℂ × ℂ)),
      L.length ≤ n →
      IsBalancedIntervals L →
      ∃ cycles : List (List (ℂ × ℂ)),
        (∀ C ∈ cycles, IsClosedPolygonalWalk C) ∧ L.Perm cycles.flatten
  | 0, L, hlen, _ => by
    have hL : L = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst hL
    exact ⟨[], by simp, List.Perm.refl []⟩
  | n + 1, L, hlen, hbal => by
    cases L with
    | nil => exact ⟨[], by simp, List.Perm.refl []⟩
    | cons e M =>
      have hW0 : IsPolygonalWalkFromTo [(e.1, e.2)] e.1 e.2 :=
        IsPolygonalWalkFromTo.single e.1 e.2
      have hbal0 : IsBalancedIntervals ([(e.1, e.2)] ++ M) := by
        simpa [Prod.eta] using hbal
      obtain ⟨C, R, hC, hperm, hbalR⟩ :=
        extend_walk_to_closed M.length [(e.1, e.2)] M e.1 e.2 rfl hW0 hbal0
      have hperm' : (e :: M).Perm (C ++ R) := by
        simpa [Prod.eta] using hperm
      have hC_pos : 0 < C.length := List.length_pos_of_ne_nil
        (let ⟨_, hw⟩ := hC; isPolygonalWalkFromTo_nonempty hw)
      have hR_len : R.length ≤ n := by
        have hlen_eq := hperm'.length_eq
        simp only [List.length_cons, List.length_append] at hlen_eq
        simp only [List.length_cons] at hlen
        omega
      obtain ⟨cyclesR, hclR, hpermR⟩ := balancedIntervals_partition n R hR_len hbalR
      refine ⟨C :: cyclesR, ?_, ?_⟩
      · intro D hD
        rcases List.mem_cons.mp hD with rfl | hD'
        · exact hC
        · exact hclR D hD'
      · exact hperm'.trans (hpermR.append_left C)

/-- Build a single concatenated `BookPath` from a nonempty polygonal walk `W`. -/
noncomputable def polygonalWalkToBookPath :
    (W : List (ℂ × ℂ)) → (a b : ℂ) → IsPolygonalWalkFromTo W a b →
      {γ : RudinRCA.Chapter10.BookPath //
        γ.toFun γ.α = a ∧ γ.toFun γ.β = b ∧
        γ.trace = (intervalsChain W).trace ∧
        RudinRCA.Chapter10.BookChain.Equiv [γ] (intervalsChain W)}
  | [], _, _, hW => (isPolygonalWalkFromTo_nonempty hW rfl).elim
  | [d], a, b, hW =>
    have hd : d = (a, b) := by
      cases hW with
      | single => rfl
      | cons hnil => exact (isPolygonalWalkFromTo_nonempty hnil rfl).elim
    ⟨RudinRCA.Chapter10.orientedSegment a b,
      RudinRCA.Chapter10.orientedSegment_start a b,
      RudinRCA.Chapter10.orientedSegment_end a b,
      by simp [intervalsChain, hd],
      by simpa [intervalsChain, hd] using
        RudinRCA.Chapter10.BookChain.equiv_refl [RudinRCA.Chapter10.orientedSegment a b]⟩
  | d :: e' :: es, a, b, hW =>
    have hd1 : d.1 = a := by cases hW; rfl
    have hrest : IsPolygonalWalkFromTo (e' :: es) d.2 b := by cases hW; assumption
    let ⟨σ, hσ_start, hσ_end, hσ_tr, hσ_eq⟩ := polygonalWalkToBookPath (e' :: es) d.2 b hrest
    let seg := RudinRCA.Chapter10.orientedSegment a d.2
    have hseg_d : RudinRCA.Chapter10.orientedSegment d.1 d.2 = seg := by rw [hd1]
    have hjoin : seg.toFun seg.β = σ.toFun σ.α :=
      (RudinRCA.Chapter10.orientedSegment_end a d.2).trans hσ_start.symm
    ⟨seg.concat σ hjoin,
      (seg.concat_start σ hjoin).trans (RudinRCA.Chapter10.orientedSegment_start a d.2),
      (seg.concat_end σ hjoin).trans hσ_end,
      by simp [intervalsChain, seg.concat_trace σ hjoin, hσ_tr, hseg_d],
      RudinRCA.Chapter10.BookChain.equiv_trans
        (RudinRCA.Chapter10.BookChain.equiv_concat seg σ hjoin)
        (by
          simpa [intervalsChain, hseg_d] using
            RudinRCA.Chapter10.BookChain.equiv_append
              (RudinRCA.Chapter10.BookChain.equiv_refl [seg]) hσ_eq)⟩

private theorem bookChain_trace_perm {Γ₁ Γ₂ : RudinRCA.Chapter10.BookChain}
    (hp : Γ₁.Perm Γ₂) : Γ₁.trace = Γ₂.trace := by
  induction hp with
  | nil => rfl
  | cons γ _ ih => simp [ih]
  | swap γ₁ γ₂ Γ => simp [union_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem bookChain_equiv_of_perm {Γ₁ Γ₂ : RudinRCA.Chapter10.BookChain}
    (hp : Γ₁.Perm Γ₂) : RudinRCA.Chapter10.BookChain.Equiv Γ₁ Γ₂ := by
  rw [RudinRCA.Chapter10.BookChain.equiv_iff_forall_continuous]
  intro f _
  induction hp with
  | nil => rfl
  | cons γ _ ih => simp [ih]
  | swap γ₁ γ₂ Γ => simp [add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Rudin RCA 13.4** (Balanced collections of oriented intervals):
If `L` is a balanced finite collection of directed line intervals (`IsBalancedIntervals L`), then:
1. `L` can be reordered and partitioned (preserving multiplicities via `L.Perm cycles.flatten`)
   into finitely many closed polygonal edge-walks `cycles`;
2. Each closed polygonal walk `C ∈ cycles` concatenates to a single closed polygonal `BookPath`,
   forming a chain `Δ` of closed paths with `Δ.trace = (intervalsChain L).trace` and
   `BookChain.Equiv (intervalsChain L) Δ`;
3. Consequently, the formal sum `intervalsChain L` is a cycle (`BookChain.IsCycle`). -/
theorem theorem13_4 (L : List (ℂ × ℂ)) (hbal : IsBalancedIntervals L) :
    (∃ cycles : List (List (ℂ × ℂ)),
      (∀ C ∈ cycles, IsClosedPolygonalWalk C) ∧
      L.Perm cycles.flatten ∧
      ∃ Δ : RudinRCA.Chapter10.BookChain,
        Δ.length = cycles.length ∧
        (∀ σ ∈ Δ, σ.IsClosed) ∧
        Δ.trace = (intervalsChain L).trace ∧
        RudinRCA.Chapter10.BookChain.Equiv (intervalsChain L) Δ) ∧
    (intervalsChain L).IsCycle := by
  obtain ⟨cycles, hcl, hperm⟩ := balancedIntervals_partition L.length L le_rfl hbal
  have hex_Δ : ∀ cs : List (List (ℂ × ℂ)), (∀ C ∈ cs, IsClosedPolygonalWalk C) →
      ∃ Δ : RudinRCA.Chapter10.BookChain,
        Δ.length = cs.length ∧
        (∀ σ ∈ Δ, σ.IsClosed) ∧
        Δ.trace = (intervalsChain cs.flatten).trace ∧
        RudinRCA.Chapter10.BookChain.Equiv (intervalsChain cs.flatten) Δ := by
    intro cs hcs
    induction cs with
    | nil =>
      exact ⟨[], rfl, by simp, by simp [intervalsChain],
        RudinRCA.Chapter10.BookChain.equiv_refl []⟩
    | cons C cs' ih =>
      obtain ⟨v, hCv⟩ := hcs C List.mem_cons_self
      obtain ⟨γ, hα, hβ, htrγ, heqγ⟩ := polygonalWalkToBookPath C v v hCv
      have hγ_cl : γ.IsClosed := hα.trans hβ.symm
      obtain ⟨Δ', hlen', hcl', htr', heq'⟩ :=
        ih (fun D hD => hcs D (List.mem_cons_of_mem _ hD))
      have hflat_chain : intervalsChain (C :: cs').flatten =
          intervalsChain C ++ intervalsChain cs'.flatten := by
        simp [intervalsChain, List.map_append]
      refine ⟨γ :: Δ', by simp [hlen'], ?_, ?_, ?_⟩
      · intro σ hσ
        rcases List.mem_cons.mp hσ with rfl | hσ'
        · exact hγ_cl
        · exact hcl' σ hσ'
      · rw [hflat_chain, RudinRCA.Chapter10.BookChain.trace_cons,
          RudinRCA.Chapter10.BookChain.trace_append, htrγ, htr']
      · rw [hflat_chain]
        exact RudinRCA.Chapter10.BookChain.equiv_append
          (RudinRCA.Chapter10.BookChain.equiv_symm heqγ) heq'
  obtain ⟨Δ, hlen, hΔcl, hΔtr, hΔeq⟩ := hex_Δ cycles hcl
  have hperm_map : (intervalsChain L).Perm (intervalsChain cycles.flatten) := hperm.map _
  have htr_eq : Δ.trace = (intervalsChain L).trace :=
    hΔtr.trans (bookChain_trace_perm hperm_map).symm
  have heq_tot : RudinRCA.Chapter10.BookChain.Equiv (intervalsChain L) Δ :=
    RudinRCA.Chapter10.BookChain.equiv_trans (bookChain_equiv_of_perm hperm_map) hΔeq
  refine ⟨⟨cycles, hcl, hperm, Δ, hlen, hΔcl, htr_eq, heq_tot⟩,
    ⟨Δ, hΔcl, htr_eq.subset, heq_tot⟩⟩


/-! ## 13.5 Global polygonal Cauchy cycle on an open neighborhood of a compact set -/

/-- Opposite-edge cancellation step: if `L` contains a nondegenerate interval `e` together with its
reverse `(e.2, e.1)`, remove one copy of each; repeat until no opposite pair remains. -/
noncomputable def cancelOppositeEdges : List (ℂ × ℂ) → List (ℂ × ℂ)
  | L =>
    open Classical in
    if h : ∃ e ∈ L, e.1 ≠ e.2 ∧ (e.2, e.1) ∈ L then
      have hmem1 : h.choose ∈ L := h.choose_spec.1
      have hne : h.choose.1 ≠ h.choose.2 := h.choose_spec.2.1
      have hmem2 : (h.choose.2, h.choose.1) ∈ L.erase h.choose := by
        have hswap_ne : (h.choose.2, h.choose.1) ≠ h.choose := by
          intro heq
          exact hne (Prod.mk.inj heq).2
        exact (List.mem_erase_of_ne hswap_ne).mpr h.choose_spec.2.2
      have : ((L.erase h.choose).erase (h.choose.2, h.choose.1)).length < L.length := by
        have hl1 := (List.perm_cons_erase hmem1).length_eq
        have hl2 := (List.perm_cons_erase hmem2).length_eq
        simp only [List.length_cons] at hl1 hl2
        omega
      cancelOppositeEdges ((L.erase h.choose).erase (h.choose.2, h.choose.1))
    else L
termination_by L => L.length

private theorem cancelOppositeEdges_spec :
    ∀ (n : ℕ) (L : List (ℂ × ℂ)),
      L.length ≤ n →
      (∀ e ∈ L, e.1 ≠ e.2) →
      (∀ e ∈ cancelOppositeEdges L, e ∈ L) ∧
      (∀ e ∈ cancelOppositeEdges L, (e.2, e.1) ∉ cancelOppositeEdges L) ∧
      (open Classical in ∀ d : ℂ × ℂ,
        ((cancelOppositeEdges L).count d : ℤ) - ((cancelOppositeEdges L).count (d.2, d.1) : ℤ) =
          (L.count d : ℤ) - (L.count (d.2, d.1) : ℤ)) ∧
      (IsBalancedIntervals L → IsBalancedIntervals (cancelOppositeEdges L)) ∧
      RudinRCA.Chapter10.BookChain.Equiv
        (intervalsChain (cancelOppositeEdges L)) (intervalsChain L)
  | 0, L, hlen, _ => by
    have hL : L = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst hL
    have hdef : cancelOppositeEdges [] = [] := by rw [cancelOppositeEdges]; simp
    rw [hdef]
    exact ⟨fun _ h => h, by simp, fun _ => rfl, id,
      RudinRCA.Chapter10.BookChain.equiv_refl _⟩
  | n + 1, L, hlen, hneL => by
    classical
    have hdef : cancelOppositeEdges L =
        if h : ∃ e ∈ L, e.1 ≠ e.2 ∧ (e.2, e.1) ∈ L then
          cancelOppositeEdges ((L.erase h.choose).erase (h.choose.2, h.choose.1))
        else L := by
      rw [cancelOppositeEdges]
    rw [hdef]
    split_ifs with h
    · set e := h.choose
      have he_mem : e ∈ L := h.choose_spec.1
      have he_ne : e.1 ≠ e.2 := h.choose_spec.2.1
      have hrev_mem : (e.2, e.1) ∈ L := h.choose_spec.2.2
      have hswap_ne : (e.2, e.1) ≠ e := fun heq => he_ne (Prod.mk.inj heq).2
      have hrev_mem' : (e.2, e.1) ∈ L.erase e := (List.mem_erase_of_ne hswap_ne).mpr hrev_mem
      set M := (L.erase e).erase (e.2, e.1)
      have hpermL : L.Perm (e :: (e.2, e.1) :: M) := by
        have hp1 : L.Perm (e :: L.erase e) := List.perm_cons_erase he_mem
        have hp2 : (L.erase e).Perm ((e.2, e.1) :: M) := List.perm_cons_erase hrev_mem'
        exact hp1.trans (hp2.cons e)
      have hM_len : M.length ≤ n := by
        have := hpermL.length_eq
        simp at this
        omega
      have hM_sub : ∀ d ∈ M, d ∈ L := fun d hd => hpermL.symm.subset (by simp [hd])
      have hneM : ∀ d ∈ M, d.1 ≠ d.2 := fun d hd => hneL d (hM_sub d hd)
      obtain ⟨hsub, hno_opp, hcnt, hbalM, heqM⟩ := cancelOppositeEdges_spec n M hM_len hneM
      refine ⟨fun d hd => hM_sub d (hsub d hd), hno_opp, ?_, ?_, ?_⟩
      · intro d
        rw [hcnt d, hpermL.count_eq, hpermL.count_eq]
        have hcc : ∀ (a x : ℂ × ℂ) (xs : List (ℂ × ℂ)),
            (a :: xs).count x = xs.count x + (if x = a then 1 else 0) := by
          intro a x xs
          by_cases hxa : x = a
          · subst hxa; simp
          · simp [hxa, Ne.symm hxa]
        rw [hcc, hcc, hcc, hcc]
        have heq1 : ((d.2, d.1) = (e.2, e.1)) ↔ (d = e) := by
          rcases e with ⟨u, w⟩; rcases d with ⟨x, y⟩
          simp [Prod.ext_iff, and_comm]
        have heq2 : ((d.2, d.1) = e) ↔ (d = (e.2, e.1)) := by
          rcases e with ⟨u, w⟩; rcases d with ⟨x, y⟩
          simp [Prod.ext_iff, and_comm]
        simp only [heq1, heq2]
        push_cast
        ring
      · intro hbalL
        apply hbalM
        intro v
        have htot := hbalL v
        rw [intervalOutDeg_perm hpermL v, intervalInDeg_perm hpermL v] at htot
        rw [intervalOutDeg_cons, intervalOutDeg_cons,
            intervalInDeg_cons, intervalInDeg_cons] at htot
        dsimp only at htot
        omega
      · refine RudinRCA.Chapter10.BookChain.equiv_trans heqM ?_
        refine RudinRCA.Chapter10.BookChain.equiv_trans ?_
          (bookChain_equiv_of_perm (hpermL.symm.map _))
        rw [RudinRCA.Chapter10.BookChain.equiv_iff_forall_continuous]
        intro f _
        simp only [intervalsChain, List.map_cons, RudinRCA.Chapter10.BookChain.integral_cons,
          RudinRCA.Chapter10.pathIntegral_orientedSegment_swap (f := f) (a := e.1) (b := e.2)]
        ring
    · refine ⟨fun e he => he, ?_, fun _ => rfl, id, RudinRCA.Chapter10.BookChain.equiv_refl _⟩
      intro e he hrev
      exact h ⟨e, he, hneL e he, hrev⟩

/-- Positively oriented boundary edges of the reference square `[-1, 1]²`. -/
private def refSquareEdges : List (ℂ × ℂ) :=
  [(-1 - Complex.I, 1 - Complex.I),
   (1 - Complex.I, 1 + Complex.I),
   (1 + Complex.I, -1 + Complex.I),
   (-1 + Complex.I, -1 - Complex.I)]

private def refSquareChain : RudinRCA.Chapter10.BookChain :=
  intervalsChain refSquareEdges

private theorem refSquareChain_isCycle : refSquareChain.IsCycle := by
  refine (theorem13_4 refSquareEdges ?_).2
  intro v
  classical
  simp only [refSquareEdges, intervalOutDeg_cons, intervalOutDeg_nil,
    intervalInDeg_cons, intervalInDeg_nil]
  by_cases h1 : -1 - Complex.I = v <;>
  by_cases h2 : 1 - Complex.I = v <;>
  by_cases h3 : 1 + Complex.I = v <;>
  by_cases h4 : -1 + Complex.I = v <;>
  simp [h1, h2, h3, h4]

private theorem zero_not_mem_refSquareChain_trace : (0 : ℂ) ∉ refSquareChain.trace := by
  simp only [refSquareChain, intervalsChain, refSquareEdges, List.map,
    RudinRCA.Chapter10.BookChain.trace_cons, RudinRCA.Chapter10.BookChain.trace_nil,
    RudinRCA.Chapter10.orientedSegment_trace, union_empty, mem_union]
  rintro (h | h | h | h) <;>
  · rw [segment_eq_image ℝ] at h
    obtain ⟨t, ht, heq⟩ := h
    have hre := congrArg Complex.re heq
    have him := congrArg Complex.im heq
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.smul_re, Complex.smul_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, smul_eq_mul] at hre him
    linarith [ht.1, ht.2]

private theorem pathIntegral_inv_mul_I (a b : ℂ)
    (h0 : (0 : ℂ) ∉ segment ℝ a b) :
    RudinRCA.Chapter10.pathIntegral (fun w : ℂ => w⁻¹)
      (RudinRCA.Chapter10.orientedSegment (Complex.I * a) (Complex.I * b)).toBookCurve =
    RudinRCA.Chapter10.pathIntegral (fun w : ℂ => w⁻¹)
      (RudinRCA.Chapter10.orientedSegment a b).toBookCurve := by
  rw [RudinRCA.Chapter10.pathIntegral_orientedSegment,
      RudinRCA.Chapter10.pathIntegral_orientedSegment]
  have hsub : Complex.I * b - Complex.I * a = (b - a) * Complex.I := by ring
  rw [hsub, mul_assoc, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  have hcomb : (1 - t : ℝ) • (Complex.I * a) + t • (Complex.I * b) =
      Complex.I * ((1 - t : ℝ) • a + t • b) := by
    simp only [Complex.real_smul]
    ring
  have hw_ne : (1 - t : ℝ) • a + t • b ≠ 0 := by
    intro hz
    apply h0
    rw [segment_eq_image ℝ]
    exact ⟨t, ht, hz⟩
  dsimp only
  rw [hcomb, mul_inv_rev, ← mul_assoc]
  field_simp [Complex.I_ne_zero, hw_ne]

/-- Index of the positively oriented boundary of `[-1, 1]²` around `0` is `1`. -/
private theorem refSquareChain_Ind_zero : refSquareChain.Ind 0 = 1 := by
  have h0_right : (0 : ℂ) ∉ segment ℝ (1 - Complex.I) (1 + Complex.I) := by
    rw [segment_eq_image ℝ]
    rintro ⟨t, _, heq⟩
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.sub_re, Complex.smul_re,
      Complex.one_re, Complex.I_re, Complex.zero_re, smul_eq_mul] at hre
    linarith
  have h0_top : (0 : ℂ) ∉ segment ℝ (1 + Complex.I) (-1 + Complex.I) := by
    rw [segment_eq_image ℝ]
    rintro ⟨t, _, heq⟩
    have him := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.neg_im, Complex.smul_im,
      Complex.one_im, Complex.I_im, Complex.zero_im, smul_eq_mul] at him
    linarith
  have h0_left : (0 : ℂ) ∉ segment ℝ (-1 + Complex.I) (-1 - Complex.I) := by
    rw [segment_eq_image ℝ]
    rintro ⟨t, _, heq⟩
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.smul_re,
      Complex.one_re, Complex.I_re, Complex.zero_re, smul_eq_mul] at hre
    linarith
  let J := RudinRCA.Chapter10.pathIntegral (fun w : ℂ => w⁻¹)
    (RudinRCA.Chapter10.orientedSegment (1 - Complex.I) (1 + Complex.I)).toBookCurve
  have he2 : RudinRCA.Chapter10.pathIntegral (fun w : ℂ => w⁻¹)
      (RudinRCA.Chapter10.orientedSegment (1 + Complex.I) (-1 + Complex.I)).toBookCurve = J := by
    have ha : Complex.I * (1 - Complex.I) = 1 + Complex.I := by apply Complex.ext <;> simp
    have hb : Complex.I * (1 + Complex.I) = -1 + Complex.I := by apply Complex.ext <;> simp
    rw [← ha, ← hb]
    exact pathIntegral_inv_mul_I _ _ h0_right
  have he3 : RudinRCA.Chapter10.pathIntegral (fun w : ℂ => w⁻¹)
      (RudinRCA.Chapter10.orientedSegment (-1 + Complex.I) (-1 - Complex.I)).toBookCurve = J := by
    have ha : Complex.I * (1 + Complex.I) = -1 + Complex.I := by apply Complex.ext <;> simp
    have hb : Complex.I * (-1 + Complex.I) = -1 - Complex.I := by apply Complex.ext <;> simp
    rw [← ha, ← hb, pathIntegral_inv_mul_I _ _ h0_top, he2]
  have he0 : RudinRCA.Chapter10.pathIntegral (fun w : ℂ => w⁻¹)
      (RudinRCA.Chapter10.orientedSegment (-1 - Complex.I) (1 - Complex.I)).toBookCurve = J := by
    have ha : Complex.I * (-1 + Complex.I) = -1 - Complex.I := by apply Complex.ext <;> simp
    have hb : Complex.I * (-1 - Complex.I) = 1 - Complex.I := by apply Complex.ext <;> simp
    rw [← ha, ← hb, pathIntegral_inv_mul_I _ _ h0_left, he3]
  have hint_tot : refSquareChain.integral (fun w : ℂ => (w - 0)⁻¹) = 4 * J := by
    simp only [sub_zero, refSquareChain, intervalsChain, refSquareEdges, List.map,
      RudinRCA.Chapter10.BookChain.integral_cons, RudinRCA.Chapter10.BookChain.integral_nil,
      he0, he2, he3]
    change J + (J + (J + (J + 0))) = 4 * J
    ring
  -- Compute `J.im` and bound `1 ≤ J.im ≤ 19 / 10`
  have hJ_eq : J = (2 * Complex.I) *
      ∫ t in (0 : ℝ)..1, (((1 : ℂ) + ((2 * t - 1 : ℝ) : ℂ) * Complex.I)⁻¹) := by
    dsimp [J]
    rw [RudinRCA.Chapter10.pathIntegral_orientedSegment]
    have hdiff : (1 + Complex.I) - (1 - Complex.I) = 2 * Complex.I := by ring
    rw [hdiff]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    congr 1
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  let g : ℝ → ℝ := fun t => 2 / (1 + (2 * t - 1) ^ 2)
  have hg_cont : Continuous g := by
    refine continuous_const.div ?_ (fun t => by positivity)
    exact continuous_const.add (((continuous_const.mul continuous_id).sub continuous_const).pow 2)
  have hJ_im : J.im = ∫ t in (0 : ℝ)..1, g t := by
    rw [hJ_eq, ← intervalIntegral.integral_const_mul]
    have him_eq : ∀ t : ℝ, ((2 * Complex.I) *
        (((1 : ℂ) + ((2 * t - 1 : ℝ) : ℂ) * Complex.I)⁻¹)).im = g t := by
      intro t
      set u : ℝ := 2 * t - 1
      let z : ℂ := (1 : ℂ) + (u : ℂ) * Complex.I
      have hz_re : z.re = 1 := by simp [z]
      have hz_im : z.im = u := by simp [z]
      have hz_ns : Complex.normSq z = 1 + u ^ 2 := by
        rw [Complex.normSq_apply, hz_re, hz_im]; ring
      change ((2 * Complex.I) * z⁻¹).im = 2 / (1 + u ^ 2)
      simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.inv_re, hz_re, hz_ns]
      norm_num
      ring
    have hcont_c : Continuous (fun t : ℝ =>
        (2 * Complex.I) * (((1 : ℂ) + ((2 * t - 1 : ℝ) : ℂ) * Complex.I)⁻¹)) := by
      refine continuous_const.mul (Continuous.inv₀ ?_ ?_)
      · exact continuous_const.add
          ((Complex.continuous_ofReal.comp ((continuous_const.mul continuous_id).sub continuous_const)).mul
            continuous_const)
      · intro t h0
        have hre := congrArg Complex.re h0
        simp at hre
    have him_int := Complex.imCLM.intervalIntegral_comp_comm
      (hcont_c.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
    change (∫ t in (0 : ℝ)..1,
        (2 * Complex.I) * (((1 : ℂ) + ((2 * t - 1 : ℝ) : ℂ) * Complex.I)⁻¹)).im =
      ∫ t in (0 : ℝ)..1, g t
    rw [← Complex.imCLM_apply, ← him_int]
    apply intervalIntegral.integral_congr
    intro t _
    exact him_eq t
  have hJ_ge : 1 ≤ J.im := by
    rw [hJ_im]
    have hle : ∀ t ∈ Icc (0 : ℝ) 1, (1 : ℝ) ≤ g t := by
      intro t ht
      dsimp [g]
      have hu2 : (2 * t - 1) ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hint := intervalIntegral.integral_mono_on zero_le_one
      (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
      (hg_cont.intervalIntegrable (μ := MeasureTheory.volume) 0 1) hle
    simpa using hint
  have hJ_le : J.im ≤ 19 / 10 := by
    rw [hJ_im, ← intervalIntegral.integral_add_adjacent_intervals (b := (1 / 4 : ℝ))
      (hg_cont.intervalIntegrable (μ := MeasureTheory.volume) 0 (1 / 4))
      (hg_cont.intervalIntegrable (μ := MeasureTheory.volume) (1 / 4) 1)]
    have h1 : (∫ t in (0 : ℝ)..(1 / 4), g t) ≤ 2 / 5 := by
      have hle : ∀ t ∈ Icc (0 : ℝ) (1 / 4), g t ≤ 8 / 5 := by
        intro t ht
        dsimp [g]
        have hu2 : (1 / 4 : ℝ) ≤ (2 * t - 1) ^ 2 := by nlinarith [ht.1, ht.2]
        rw [div_le_iff₀ (by positivity)]
        linarith
      have hint := intervalIntegral.integral_mono_on (by norm_num)
        (hg_cont.intervalIntegrable (μ := MeasureTheory.volume) 0 (1 / 4))
        (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) 0 (1 / 4)) hle
      simpa using hint.trans (by norm_num)
    have h2 : (∫ t in (1 / 4 : ℝ)..1, g t) ≤ 3 / 2 := by
      have hle : ∀ t ∈ Icc (1 / 4 : ℝ) 1, g t ≤ 2 := by
        intro t _
        dsimp [g]
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (2 * t - 1)]
      have hint := intervalIntegral.integral_mono_on (by norm_num)
        (hg_cont.intervalIntegrable (μ := MeasureTheory.volume) (1 / 4) 1)
        (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) (1 / 4) 1) hle
      simpa using hint.trans (by norm_num)
    linarith
  obtain ⟨n, hn⟩ := RudinRCA.Chapter10.BookChain.Ind_mem_int_of_isCycle
    refSquareChain_isCycle zero_not_mem_refSquareChain_trace
  have htwo_pi_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hrel : (4 * J : ℂ) = 2 * Real.pi * Complex.I * (n : ℂ) := by
    have hind_def : refSquareChain.Ind 0 =
        (2 * Real.pi * Complex.I)⁻¹ * refSquareChain.integral (fun w => (w - 0)⁻¹) := rfl
    rw [hint_tot, hn] at hind_def
    field_simp [htwo_pi_ne] at hind_def
    linear_combination hind_def.symm
  have him_rel : 4 * J.im = 2 * Real.pi * (n : ℝ) := by
    have him := congrArg Complex.im hrel
    simpa [mul_assoc, mul_left_comm, mul_comm] using him
  have hpi2 : 2 ≤ Real.pi := Real.two_le_pi
  have hn1 : n = 1 := by
    have hlo : (4 : ℝ) ≤ 2 * Real.pi * (n : ℝ) := by linarith
    have hhi : 2 * Real.pi * (n : ℝ) ≤ 38 / 5 := by linarith
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      by_contra hnp
      have hnp' : (n : ℝ) ≤ 0 := le_of_not_gt hnp
      have : 2 * Real.pi * (n : ℝ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hnp'
      linarith
    have hn_lt2 : (n : ℝ) < 2 := by
      by_contra hge2
      have hge2' : 2 ≤ (n : ℝ) := le_of_not_gt hge2
      have : 8 ≤ 2 * Real.pi * (n : ℝ) := by nlinarith
      linarith
    have h0z : (0 : ℤ) < n := by exact_mod_cast hn_pos
    have h2z : n < (2 : ℤ) := by exact_mod_cast hn_lt2
    omega
  rw [hn, hn1, Int.cast_one]

/-- Grid vertex `(i * δ, j * δ)` for mesh `δ > 0`. -/
private def gridVertex (δ : ℝ) (i j : ℤ) : ℂ :=
  (((i : ℝ) * δ : ℝ) : ℂ) + (((j : ℝ) * δ : ℝ) : ℂ) * Complex.I

private theorem gridVertex_re (δ : ℝ) (i j : ℤ) : (gridVertex δ i j).re = (i : ℝ) * δ := by
  simp [gridVertex]

private theorem gridVertex_im (δ : ℝ) (i j : ℤ) : (gridVertex δ i j).im = (j : ℝ) * δ := by
  simp [gridVertex]

private theorem gridVertex_inj {δ : ℝ} (hδ : 0 < δ) {i₁ j₁ i₂ j₂ : ℤ}
    (h : gridVertex δ i₁ j₁ = gridVertex δ i₂ j₂) : i₁ = i₂ ∧ j₁ = j₂ := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [gridVertex_re, gridVertex_im] at hre him
  have hi : (i₁ : ℝ) = (i₂ : ℝ) := mul_right_cancel₀ hδ.ne' hre
  have hj : (j₁ : ℝ) = (j₂ : ℝ) := mul_right_cancel₀ hδ.ne' him
  exact ⟨Int.cast_injective hi, Int.cast_injective hj⟩

/-- Closed grid square `[i δ, (i+1) δ] × [j δ, (j+1) δ]`. -/
private def gridSquare (δ : ℝ) (p : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | (p.1 : ℝ) * δ ≤ z.re ∧ z.re ≤ ((p.1 : ℝ) + 1) * δ ∧
           (p.2 : ℝ) * δ ≤ z.im ∧ z.im ≤ ((p.2 : ℝ) + 1) * δ}

/-- Open interior of the grid square `(i δ, (i+1) δ) × (j δ, (j+1) δ)`. -/
private def gridSquareOpen (δ : ℝ) (p : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | (p.1 : ℝ) * δ < z.re ∧ z.re < ((p.1 : ℝ) + 1) * δ ∧
           (p.2 : ℝ) * δ < z.im ∧ z.im < ((p.2 : ℝ) + 1) * δ}

/-- Center of the grid square `p = (i, j)`. -/
private def gridCenter (δ : ℝ) (p : ℤ × ℤ) : ℂ :=
  ((((p.1 : ℝ) + 1 / 2) * δ : ℝ) : ℂ) + ((((p.2 : ℝ) + 1 / 2) * δ : ℝ) : ℂ) * Complex.I

private theorem convex_gridSquare (δ : ℝ) (p : ℤ × ℤ) : Convex ℝ (gridSquare δ p) := by
  intro x hx y hy a b ha hb hab
  have hconv_le : ∀ {L u v : ℝ}, L ≤ u → L ≤ v → L ≤ a * u + b * v := fun {L u v} hu hv =>
    calc L = (a + b) * L := by rw [hab, one_mul]
      _ = a * L + b * L := add_mul a b L
      _ ≤ a * u + b * v := add_le_add (mul_le_mul_of_nonneg_left hu ha)
            (mul_le_mul_of_nonneg_left hv hb)
  have hconv_ge : ∀ {U u v : ℝ}, u ≤ U → v ≤ U → a * u + b * v ≤ U := fun {U u v} hu hv =>
    calc a * u + b * v ≤ a * U + b * U := add_le_add (mul_le_mul_of_nonneg_left hu ha)
            (mul_le_mul_of_nonneg_left hv hb)
      _ = (a + b) * U := (add_mul a b U).symm
      _ = U := by rw [hab, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]; exact hconv_le hx.1 hy.1
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]; exact hconv_ge hx.2.1 hy.2.1
  · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]; exact hconv_le hx.2.2.1 hy.2.2.1
  · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]; exact hconv_ge hx.2.2.2 hy.2.2.2

private theorem convex_gridSquareOpen (δ : ℝ) (p : ℤ × ℤ) : Convex ℝ (gridSquareOpen δ p) := by
  intro x hx y hy a b ha hb hab
  have hpos : 0 < a ∨ 0 < b := by
    by_contra h
    have ha0 : a ≤ 0 := le_of_not_gt fun ha' => h (Or.inl ha')
    have hb0 : b ≤ 0 := le_of_not_gt fun hb' => h (Or.inr hb')
    linarith
  have hconv_lt : ∀ {L u v : ℝ}, L < u → L < v → L < a * u + b * v := fun {L u v} hu hv => by
    rcases hpos with ha' | hb'
    · calc L = a * L + b * L := by rw [← add_mul, hab, one_mul]
        _ < a * u + b * v := add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hu ha')
              (mul_le_mul_of_nonneg_left hv.le hb)
    · calc L = a * L + b * L := by rw [← add_mul, hab, one_mul]
        _ < a * u + b * v := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hu.le ha)
              (mul_lt_mul_of_pos_left hv hb')
  have hconv_gt : ∀ {U u v : ℝ}, u < U → v < U → a * u + b * v < U := fun {U u v} hu hv => by
    rcases hpos with ha' | hb'
    · calc a * u + b * v < a * U + b * U := add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hu ha')
              (mul_le_mul_of_nonneg_left hv.le hb)
        _ = U := by rw [← add_mul, hab, one_mul]
    · calc a * u + b * v < a * U + b * U := add_lt_add_of_le_of_lt
              (mul_le_mul_of_nonneg_left hu.le ha) (mul_lt_mul_of_pos_left hv hb')
        _ = U := by rw [← add_mul, hab, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]; exact hconv_lt hx.1 hy.1
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]; exact hconv_gt hx.2.1 hy.2.1
  · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]; exact hconv_lt hx.2.2.1 hy.2.2.1
  · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]; exact hconv_gt hx.2.2.2 hy.2.2.2

/-- The 4 positively oriented boundary edges of `gridSquare δ p`. -/
private def gridSquareEdges (δ : ℝ) (p : ℤ × ℤ) : List (ℂ × ℂ) :=
  [(gridVertex δ p.1 p.2, gridVertex δ (p.1 + 1) p.2),
   (gridVertex δ (p.1 + 1) p.2, gridVertex δ (p.1 + 1) (p.2 + 1)),
   (gridVertex δ (p.1 + 1) (p.2 + 1), gridVertex δ p.1 (p.2 + 1)),
   (gridVertex δ p.1 (p.2 + 1), gridVertex δ p.1 p.2)]

private def gridSquareChain (δ : ℝ) (p : ℤ × ℤ) : RudinRCA.Chapter10.BookChain :=
  intervalsChain (gridSquareEdges δ p)

private theorem gridSquareEdges_balanced (δ : ℝ) (p : ℤ × ℤ) :
    IsBalancedIntervals (gridSquareEdges δ p) := by
  intro v
  classical
  simp only [gridSquareEdges, intervalOutDeg_cons, intervalOutDeg_nil,
    intervalInDeg_cons, intervalInDeg_nil]
  by_cases h1 : gridVertex δ p.1 p.2 = v <;>
  by_cases h2 : gridVertex δ (p.1 + 1) p.2 = v <;>
  by_cases h3 : gridVertex δ (p.1 + 1) (p.2 + 1) = v <;>
  by_cases h4 : gridVertex δ p.1 (p.2 + 1) = v <;>
  simp [h1, h2, h3, h4]

private theorem gridSquareChain_isCycle (δ : ℝ) (p : ℤ × ℤ) :
    (gridSquareChain δ p).IsCycle :=
  (theorem13_4 _ (gridSquareEdges_balanced δ p)).2

private theorem gridVertex_mem_gridSquare {δ : ℝ} (hδ : 0 < δ) (p : ℤ × ℤ) :
    gridVertex δ p.1 p.2 ∈ gridSquare δ p ∧
    gridVertex δ (p.1 + 1) p.2 ∈ gridSquare δ p ∧
    gridVertex δ (p.1 + 1) (p.2 + 1) ∈ gridSquare δ p ∧
    gridVertex δ p.1 (p.2 + 1) ∈ gridSquare δ p := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [gridVertex_re, gridVertex_im, Int.cast_add, Int.cast_one] <;>
    nlinarith

private theorem gridSquareChain_trace_subset {δ : ℝ} (hδ : 0 < δ) (p : ℤ × ℤ) :
    (gridSquareChain δ p).trace ⊆ gridSquare δ p := by
  obtain ⟨hv1, hv2, hv3, hv4⟩ := gridVertex_mem_gridSquare hδ p
  have hconv := convex_gridSquare δ p
  simp only [gridSquareChain, intervalsChain, gridSquareEdges, List.map,
    RudinRCA.Chapter10.BookChain.trace_cons, RudinRCA.Chapter10.BookChain.trace_nil,
    RudinRCA.Chapter10.orientedSegment_trace, union_empty]
  exact union_subset (hconv.segment_subset hv1 hv2)
    (union_subset (hconv.segment_subset hv2 hv3)
      (union_subset (hconv.segment_subset hv3 hv4) (hconv.segment_subset hv4 hv1)))

private theorem gridSquareOpen_disjoint_trace {δ : ℝ} (_hδ : 0 < δ) (p q : ℤ × ℤ) :
    Disjoint (gridSquareOpen δ p) (gridSquareChain δ q).trace := by
  rw [Set.disjoint_left]
  intro z hz htr
  simp only [gridSquareChain, intervalsChain, gridSquareEdges, List.map,
    RudinRCA.Chapter10.BookChain.trace_cons, RudinRCA.Chapter10.BookChain.trace_nil,
    RudinRCA.Chapter10.orientedSegment_trace, union_empty, mem_union] at htr
  rcases htr with h | h | h | h
  · rw [segment_eq_image ℝ] at h
    obtain ⟨t, _, heq⟩ := h
    have him := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, gridVertex_im] at him
    have him' : z.im = (q.2 : ℝ) * δ := by linarith
    by_cases hqp : q.2 ≤ p.2
    · have : (q.2 : ℝ) * δ ≤ (p.2 : ℝ) * δ :=
        mul_le_mul_of_nonneg_right (Int.cast_le.mpr hqp) _hδ.le
      linarith [hz.2.2.1]
    · have hqp' : p.2 + 1 ≤ q.2 := by omega
      have : ((p.2 : ℝ) + 1) * δ ≤ (q.2 : ℝ) * δ := by
        exact_mod_cast mul_le_mul_of_nonneg_right (Int.cast_le.mpr hqp') _hδ.le
      linarith [hz.2.2.2]
  · rw [segment_eq_image ℝ] at h
    obtain ⟨t, _, heq⟩ := h
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul,
      gridVertex_re, Int.cast_add, Int.cast_one] at hre
    have hre' : z.re = ((q.1 : ℝ) + 1) * δ := by linarith
    by_cases hqp : q.1 + 1 ≤ p.1
    · have : ((q.1 : ℝ) + 1) * δ ≤ (p.1 : ℝ) * δ := by
        exact_mod_cast mul_le_mul_of_nonneg_right (Int.cast_le.mpr hqp) _hδ.le
      linarith [hz.1]
    · have hqp' : p.1 + 1 ≤ q.1 + 1 := by omega
      have : ((p.1 : ℝ) + 1) * δ ≤ ((q.1 : ℝ) + 1) * δ := by
        exact_mod_cast mul_le_mul_of_nonneg_right (Int.cast_le.mpr hqp') _hδ.le
      linarith [hz.2.1]
  · rw [segment_eq_image ℝ] at h
    obtain ⟨t, _, heq⟩ := h
    have him := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul,
      gridVertex_im, Int.cast_add, Int.cast_one] at him
    have him' : z.im = ((q.2 : ℝ) + 1) * δ := by linarith
    by_cases hqp : q.2 + 1 ≤ p.2
    · have : ((q.2 : ℝ) + 1) * δ ≤ (p.2 : ℝ) * δ := by
        exact_mod_cast mul_le_mul_of_nonneg_right (Int.cast_le.mpr hqp) _hδ.le
      linarith [hz.2.2.1]
    · have hqp' : p.2 + 1 ≤ q.2 + 1 := by omega
      have : ((p.2 : ℝ) + 1) * δ ≤ ((q.2 : ℝ) + 1) * δ := by
        exact_mod_cast mul_le_mul_of_nonneg_right (Int.cast_le.mpr hqp') _hδ.le
      linarith [hz.2.2.2]
  · rw [segment_eq_image ℝ] at h
    obtain ⟨t, _, heq⟩ := h
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, gridVertex_re] at hre
    have hre' : z.re = (q.1 : ℝ) * δ := by linarith
    by_cases hqp : q.1 ≤ p.1
    · have : (q.1 : ℝ) * δ ≤ (p.1 : ℝ) * δ :=
        mul_le_mul_of_nonneg_right (Int.cast_le.mpr hqp) _hδ.le
      linarith [hz.1]
    · have hqp' : p.1 + 1 ≤ q.1 := by omega
      have : ((p.1 : ℝ) + 1) * δ ≤ (q.1 : ℝ) * δ := by
        exact_mod_cast mul_le_mul_of_nonneg_right (Int.cast_le.mpr hqp') _hδ.le
      linarith [hz.2.1]

/-- Index of `gridSquareChain δ p` at any point `z ∈ gridSquareOpen δ p` is `1`. -/
private theorem gridSquareChain_Ind_open {δ : ℝ} (hδ : 0 < δ) (p : ℤ × ℤ)
    {z : ℂ} (hz : z ∈ gridSquareOpen δ p) :
    (gridSquareChain δ p).Ind z = 1 := by
  let c := gridCenter δ p
  have hc_open : c ∈ gridSquareOpen δ p := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [c, gridCenter, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, zero_add, sub_zero] <;>
    nlinarith
  have heq_z_c : (gridSquareChain δ p).Ind z = (gridSquareChain δ p).Ind c :=
    RudinRCA.Chapter10.BookChain.Ind_eq_of_isPreconnected_compl_of_isCycle
      (gridSquareChain_isCycle δ p) (convex_gridSquareOpen δ p).isPreconnected
      (Set.disjoint_left.mp (gridSquareOpen_disjoint_trace hδ p p)) hz hc_open
  rw [heq_z_c, ← refSquareChain_Ind_zero]
  -- Affine invariance of segment winding integral under `w ↦ c + (δ / 2) * w`
  let s : ℂ := ((δ / 2 : ℝ) : ℂ)
  have hs_ne : s ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hseg_eq : ∀ a b : ℂ, (0 : ℂ) ∉ segment ℝ a b →
      RudinRCA.Chapter10.pathIntegral (fun w => (w - c)⁻¹)
        (RudinRCA.Chapter10.orientedSegment (c + s * a) (c + s * b)).toBookCurve =
      RudinRCA.Chapter10.pathIntegral (fun w => (w - 0)⁻¹)
        (RudinRCA.Chapter10.orientedSegment a b).toBookCurve := by
    intro a b h0
    rw [RudinRCA.Chapter10.pathIntegral_orientedSegment,
        RudinRCA.Chapter10.pathIntegral_orientedSegment]
    have hdiff : (c + s * b) - (c + s * a) = (b - a) * s := by ring
    rw [hdiff, mul_assoc, ← intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hcomb : ((1 - t : ℝ) • (c + s * a) + t • (c + s * b)) - c =
        s * ((1 - t : ℝ) • a + t • b) := by
      simp only [Complex.real_smul]; push_cast; ring
    have hw_ne : (1 - t : ℝ) • a + t • b ≠ 0 := by
      intro hz0
      apply h0
      rw [segment_eq_image ℝ]
      exact ⟨t, ht, hz0⟩
    dsimp only
    rw [hcomb, sub_zero, mul_inv_rev, ← mul_assoc]
    field_simp [hs_ne, hw_ne]
  have hv0 : gridVertex δ p.1 p.2 = c + s * (-1 - Complex.I) := by
    apply Complex.ext <;> simp [gridVertex, c, gridCenter, s] <;> ring
  have hv1 : gridVertex δ (p.1 + 1) p.2 = c + s * (1 - Complex.I) := by
    apply Complex.ext <;> simp [gridVertex, c, gridCenter, s] <;> ring
  have hv2 : gridVertex δ (p.1 + 1) (p.2 + 1) = c + s * (1 + Complex.I) := by
    apply Complex.ext <;> simp [gridVertex, c, gridCenter, s] <;> ring
  have hv3 : gridVertex δ p.1 (p.2 + 1) = c + s * (-1 + Complex.I) := by
    apply Complex.ext <;> simp [gridVertex, c, gridCenter, s] <;> ring
  have h0_not := zero_not_mem_refSquareChain_trace
  simp only [refSquareChain, intervalsChain, refSquareEdges, List.map,
    RudinRCA.Chapter10.BookChain.trace_cons, RudinRCA.Chapter10.BookChain.trace_nil,
    RudinRCA.Chapter10.orientedSegment_trace, union_empty, mem_union, not_or] at h0_not
  unfold RudinRCA.Chapter10.BookChain.Ind
  congr 1
  simp only [gridSquareChain, refSquareChain, intervalsChain, gridSquareEdges, refSquareEdges,
    List.map, RudinRCA.Chapter10.BookChain.integral_cons,
    RudinRCA.Chapter10.BookChain.integral_nil, hv0, hv1, hv2, hv3]
  rw [hseg_eq _ _ h0_not.1, hseg_eq _ _ h0_not.2.1,
      hseg_eq _ _ h0_not.2.2.1, hseg_eq _ _ h0_not.2.2.2]

/-- Classification of any directed edge occurring in `gridSquareEdges δ p`: each directed grid edge
belongs to at most one square `p : ℤ × ℤ`, and its reverse belongs to the unique adjacent square. -/
private theorem gridSquareEdges_mem_unique {δ : ℝ} (hδ : 0 < δ) {e : ℂ × ℂ} {p q : ℤ × ℤ}
    (hp : e ∈ gridSquareEdges δ p) (hq : e ∈ gridSquareEdges δ q) : p = q := by
  simp only [gridSquareEdges, List.mem_cons, List.not_mem_nil, or_false] at hp hq
  rcases hp with rfl | rfl | rfl | rfl <;>
  rcases hq with h | h | h | h <;>
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    obtain ⟨hi1, hj1⟩ := gridVertex_inj hδ h1
    obtain ⟨hi2, hj2⟩ := gridVertex_inj hδ h2
    ext <;> omega

/-- Each directed edge `e ∈ gridSquareEdges δ p` is nondegenerate, and its reverse `(e.2, e.1)` lies
in `gridSquareEdges δ p'` for an adjacent square `p'` sharing `segment ℝ e.1 e.2`. -/
private theorem gridSquareEdges_adjacent {δ : ℝ} (hδ : 0 < δ) {e : ℂ × ℂ} {p : ℤ × ℤ}
    (hp : e ∈ gridSquareEdges δ p) :
    e.1 ≠ e.2 ∧
    ∃ p' : ℤ × ℤ, (e.2, e.1) ∈ gridSquareEdges δ p' ∧
      segment ℝ e.1 e.2 ⊆ gridSquare δ p ∧
      segment ℝ e.1 e.2 ⊆ gridSquare δ p' := by
  have hsubp : segment ℝ e.1 e.2 ⊆ gridSquare δ p := by
    have htr := gridSquareChain_trace_subset hδ p
    intro z hz
    apply htr
    simp only [gridSquareChain, intervalsChain, gridSquareEdges, List.map,
      RudinRCA.Chapter10.BookChain.trace_cons, RudinRCA.Chapter10.BookChain.trace_nil,
      RudinRCA.Chapter10.orientedSegment_trace, union_empty, mem_union]
    simp only [gridSquareEdges, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp [hz]
  simp only [gridSquareEdges, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · refine ⟨fun h => by have := (gridVertex_inj hδ h).1; omega, (p.1, p.2 - 1), ?_, hsubp, ?_⟩
    · simp [gridSquareEdges, sub_add_cancel]
    · obtain ⟨_, _, hv3, hv4⟩ := gridVertex_mem_gridSquare hδ (p.1, p.2 - 1)
      simpa [sub_add_cancel] using (convex_gridSquare δ (p.1, p.2 - 1)).segment_subset hv4 hv3
  · refine ⟨fun h => by have := (gridVertex_inj hδ h).2; omega, (p.1 + 1, p.2), ?_, hsubp, ?_⟩
    · simp [gridSquareEdges]
    · obtain ⟨hv1, _, _, hv4⟩ := gridVertex_mem_gridSquare hδ (p.1 + 1, p.2)
      simpa using (convex_gridSquare δ (p.1 + 1, p.2)).segment_subset hv1 hv4
  · refine ⟨fun h => by have := (gridVertex_inj hδ h).1; omega, (p.1, p.2 + 1), ?_, hsubp, ?_⟩
    · simp [gridSquareEdges]
    · obtain ⟨hv1, hv2, _, _⟩ := gridVertex_mem_gridSquare hδ (p.1, p.2 + 1)
      simpa using (convex_gridSquare δ (p.1, p.2 + 1)).segment_subset hv2 hv1
  · refine ⟨fun h => by have := (gridVertex_inj hδ h).2; omega, (p.1 - 1, p.2), ?_, hsubp, ?_⟩
    · simp [gridSquareEdges, sub_add_cancel]
    · obtain ⟨_, hv2, hv3, _⟩ := gridVertex_mem_gridSquare hδ (p.1 - 1, p.2)
      simpa [sub_add_cancel] using (convex_gridSquare δ (p.1 - 1, p.2)).segment_subset hv3 hv2

/-- **Rudin RCA 13.5** (Global polygonal Cauchy cycle in `Ω \ K`):
Let `Ω ⊆ ℂ` be open and `K ⊆ Ω` be compact (without any connectedness assumptions on `Ω` or `K`).
There exists a polygonal cycle `Γ` (built from oriented line segments via 13.4) with trace in
`Ω \ K` such that:
1. `Γ.Ind w = 0` for every `w ∉ Ω`, and `Γ.Ind z = 1` for every `z ∈ K`;
2. Simultaneously for every `f ∈ H(Ω)` and every `z ∈ K`,
   `f(z) = (2πi)⁻¹ ∫_Γ f(ζ) / (ζ - z) dζ`. -/
theorem theorem13_5 {Ω K : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ (L : List (ℂ × ℂ)),
      IsBalancedIntervals L ∧
      (intervalsChain L).IsCycle ∧
      (intervalsChain L).trace ⊆ Ω \ K ∧
      (∀ w : ℂ, w ∉ Ω → (intervalsChain L).Ind w = 0) ∧
      (∀ z ∈ K, (intervalsChain L).Ind z = 1) ∧
      (∀ {f : ℂ → ℂ}, RudinRCA.Chapter10.HolomorphicOn f Ω →
        ∀ z ∈ K,
          f z = (2 * Real.pi * Complex.I)⁻¹ *
            (intervalsChain L).integral (fun ζ => f ζ / (ζ - z))) := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · refine ⟨[], fun _ => rfl, RudinRCA.Chapter10.BookChain.isCycle_nil, ?_, ?_, ?_, ?_⟩
    · simp [intervalsChain]
    · intro w _; simp [intervalsChain]
    · intro z hz; exact hz.elim
    · intro _ _ z hz; exact hz.elim
  -- Choose grid mesh `δ > 0` from compact exhaustion `13.3`
  obtain ⟨N, hKN⟩ := exists_subset_exhaustionSet_of_isCompact hΩ hK hKΩ
  let r : ℝ := (1 : ℝ) / ((N : ℝ) + 1) - (1 : ℝ) / ((N : ℝ) + 2)
  have hr_pos : 0 < r :=
    sub_pos.mpr (one_div_lt_one_div_of_lt (by positivity) (by linarith))
  have hball_Ω : ∀ z ∈ K, ball z r ⊆ Ω := by
    intro z hz y hy
    have hzN : z ∈ exhaustionSet Ω N := hKN hz
    apply exhaustionSet_subset Ω (N + 1)
    -- Direct check that `ball z r ⊆ exhaustionSet Ω (N + 1)`
    have hyz_norm : ‖y - z‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hy
    have hr_le1 : r ≤ 1 := by
      dsimp [r]
      have h1 : (1 : ℝ) / ((N : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
      have h2 : 0 ≤ (1 : ℝ) / ((N : ℝ) + 2) := by positivity
      linarith
    refine ⟨?_, ?_⟩
    · have htri : ‖y‖ ≤ ‖z‖ + ‖y - z‖ := by
        calc ‖y‖ = ‖z + (y - z)‖ := by ring_nf
          _ ≤ ‖z‖ + ‖y - z‖ := norm_add_le _ _
      push_cast
      linarith [hzN.1]
    · intro w hw
      have hyz : dist z y < r := by simpa [Metric.mem_ball, dist_comm] using hy
      have hzw : (1 : ℝ) / ((N : ℝ) + 1) ≤ dist z w := hzN.2 w hw
      have htri : dist z w ≤ dist z y + dist y w := dist_triangle z y w
      push_cast
      have : (1 : ℝ) / ((N : ℝ) + 1 + 1) = (1 : ℝ) / ((N : ℝ) + 2) := by ring
      rw [this]
      dsimp [r] at hyz
      linarith
  let δ : ℝ := r / 4
  have hδ : 0 < δ := by positivity
  let B : ℕ := ⌈((N : ℝ) + 1) / δ⌉₊ + 2
  let box : Finset (ℤ × ℤ) := Finset.Icc (-(B : ℤ)) (B : ℤ) ×ˢ Finset.Icc (-(B : ℤ)) (B : ℤ)
  let P : Finset (ℤ × ℤ) := box.filter (fun p => (gridSquare δ p ∩ K).Nonempty)
  -- Every square meeting `K` lies inside `box`, hence in `P`, and is a subset of `Ω`
  have hp_in_box : ∀ p : ℤ × ℤ, (gridSquare δ p ∩ K).Nonempty → p ∈ P := by
    rintro ⟨i, j⟩ ⟨z, hzQ, hzK⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ⟨z, hzQ, hzK⟩⟩
    · rw [Finset.mem_Icc]
      have hz_norm : ‖z‖ ≤ (N : ℝ) + 1 := (hKN hzK).1
      have hre_abs : |z.re| ≤ (N : ℝ) + 1 := (Complex.abs_re_le_norm z).trans hz_norm
      have hB_ge : ((N : ℝ) + 1) / δ ≤ (B : ℝ) - 2 := by
        dsimp [B]; push_cast; linarith [Nat.le_ceil (((N : ℝ) + 1) / δ)]
      have hBδ : (N : ℝ) + 1 ≤ ((B : ℝ) - 2) * δ := (div_le_iff₀ hδ).mp hB_ge
      have hi_hi : (i : ℝ) * δ ≤ (B : ℝ) * δ := by
        have := abs_le.mp hre_abs; linarith [hzQ.1]
      have hi_lo : (-(B : ℝ)) * δ ≤ (i : ℝ) * δ := by
        have := abs_le.mp hre_abs; linarith [hzQ.2.1]
      exact ⟨by exact_mod_cast le_of_mul_le_mul_right hi_lo hδ,
             by exact_mod_cast le_of_mul_le_mul_right hi_hi hδ⟩
    · rw [Finset.mem_Icc]
      have hz_norm : ‖z‖ ≤ (N : ℝ) + 1 := (hKN hzK).1
      have him_abs : |z.im| ≤ (N : ℝ) + 1 := (Complex.abs_im_le_norm z).trans hz_norm
      have hB_ge : ((N : ℝ) + 1) / δ ≤ (B : ℝ) - 2 := by
        dsimp [B]; push_cast; linarith [Nat.le_ceil (((N : ℝ) + 1) / δ)]
      have hBδ : (N : ℝ) + 1 ≤ ((B : ℝ) - 2) * δ := (div_le_iff₀ hδ).mp hB_ge
      have hj_hi : (j : ℝ) * δ ≤ (B : ℝ) * δ := by
        have := abs_le.mp him_abs; linarith [hzQ.2.2.1]
      have hj_lo : (-(B : ℝ)) * δ ≤ (j : ℝ) * δ := by
        have := abs_le.mp him_abs; linarith [hzQ.2.2.2]
      exact ⟨by exact_mod_cast le_of_mul_le_mul_right hj_lo hδ,
             by exact_mod_cast le_of_mul_le_mul_right hj_hi hδ⟩
  have hp_sub_Ω : ∀ p ∈ P, gridSquare δ p ⊆ Ω := by
    intro p hp y hy
    obtain ⟨z, hzQ, hzK⟩ := (Finset.mem_filter.mp hp).2
    apply hball_Ω z hzK
    rw [Metric.mem_ball, dist_eq_norm]
    have hre : |(y - z).re| ≤ δ := by
      rw [Complex.sub_re, abs_le]
      exact ⟨by linarith [hy.1, hzQ.2.1], by linarith [hy.2.1, hzQ.1]⟩
    have him : |(y - z).im| ≤ δ := by
      rw [Complex.sub_im, abs_le]
      exact ⟨by linarith [hy.2.2.1, hzQ.2.2.2], by linarith [hy.2.2.2, hzQ.2.2.1]⟩
    have hnorm : ‖y - z‖ ≤ |(y - z).re| + |(y - z).im| := Complex.norm_le_abs_re_add_abs_im _
    have hδ_eq : δ = r / 4 := rfl
    linarith
  have hz_mem_some_P : ∀ z ∈ K, ∃ p ∈ P, z ∈ gridSquare δ p := by
    intro z hzK
    let i : ℤ := ⌊z.re / δ⌋
    let j : ℤ := ⌊z.im / δ⌋
    have hzQ : z ∈ gridSquare δ (i, j) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (le_div_iff₀ hδ).mp (Int.floor_le (z.re / δ))
      · exact (div_le_iff₀ hδ).mp (Int.lt_floor_add_one (z.re / δ)).le
      · exact (le_div_iff₀ hδ).mp (Int.floor_le (z.im / δ))
      · exact (div_le_iff₀ hδ).mp (Int.lt_floor_add_one (z.im / δ)).le
    exact ⟨(i, j), hp_in_box (i, j) ⟨z, hzQ, hzK⟩, hzQ⟩
  -- Build `L_all` and `L = cancelOppositeEdges L_all`
  let plist : List (ℤ × ℤ) := P.toList
  have hnodup_p : plist.Nodup := P.nodup_toList
  let L_all : List (ℂ × ℂ) := plist.flatMap (gridSquareEdges δ)
  have hbal_all : IsBalancedIntervals L_all := by
    have hrec : ∀ ps : List (ℤ × ℤ), IsBalancedIntervals (ps.flatMap (gridSquareEdges δ)) := by
      intro ps
      induction ps with
      | nil => exact fun _ => rfl
      | cons p ps' ih =>
        intro v
        simp only [List.flatMap_cons, intervalOutDeg_append, intervalInDeg_append,
          gridSquareEdges_balanced δ p v, ih v]
    exact hrec plist
  have hne_all : ∀ e ∈ L_all, e.1 ≠ e.2 := by
    intro e he
    obtain ⟨p, _, hep⟩ := List.mem_flatMap.mp he
    exact (gridSquareEdges_adjacent hδ hep).1
  -- Each directed edge appears at most once in `L_all`
  have hcount_le_one : ∀ e : ℂ × ℂ, L_all.count e ≤ 1 := by
    have hrec : ∀ ps : List (ℤ × ℤ), ps.Nodup → ∀ e : ℂ × ℂ,
        (ps.flatMap (gridSquareEdges δ)).count e ≤ 1 := by
      intro ps hnd e
      induction ps with
      | nil => simp
      | cons p ps' ih =>
        obtain ⟨hp_not, hnd'⟩ := List.nodup_cons.mp hnd
        rw [List.flatMap_cons, List.count_append]
        by_cases hep : e ∈ gridSquareEdges δ p
        · have hnot_rest : e ∉ ps'.flatMap (gridSquareEdges δ) := by
            intro hmem
            obtain ⟨q, hq_mem, heq⟩ := List.mem_flatMap.mp hmem
            have hpq := gridSquareEdges_mem_unique hδ hep heq
            exact hp_not (hpq ▸ hq_mem)
          rw [List.count_eq_zero.mpr hnot_rest, add_zero]
          -- Count in the 4 distinct edges of `gridSquareEdges δ p` is `≤ 1`
          have hd12 : gridVertex δ p.1 p.2 ≠ gridVertex δ (p.1 + 1) p.2 :=
            fun h => by have := (gridVertex_inj hδ h).1; omega
          have hd13 : gridVertex δ p.1 p.2 ≠ gridVertex δ (p.1 + 1) (p.2 + 1) :=
            fun h => by have := (gridVertex_inj hδ h).1; omega
          have hd14 : gridVertex δ p.1 p.2 ≠ gridVertex δ p.1 (p.2 + 1) :=
            fun h => by have := (gridVertex_inj hδ h).2; omega
          have hd23 : gridVertex δ (p.1 + 1) p.2 ≠ gridVertex δ (p.1 + 1) (p.2 + 1) :=
            fun h => by have := (gridVertex_inj hδ h).2; omega
          have hd24 : gridVertex δ (p.1 + 1) p.2 ≠ gridVertex δ p.1 (p.2 + 1) :=
            fun h => by have := (gridVertex_inj hδ h).1; omega
          have hd34 : gridVertex δ (p.1 + 1) (p.2 + 1) ≠ gridVertex δ p.1 (p.2 + 1) :=
            fun h => by have := (gridVertex_inj hδ h).1; omega
          simp only [gridSquareEdges, List.mem_cons, List.not_mem_nil, or_false] at hep
          rcases hep with rfl | rfl | rfl | rfl <;>
            simp [gridSquareEdges, hd12, hd12.symm, hd13, hd13.symm, hd14, hd14.symm,
              hd23, hd23.symm, hd24, hd24.symm, hd34, hd34.symm]
        · rw [List.count_eq_zero.mpr hep, zero_add]
          exact ih hnd'
    exact hrec plist hnodup_p
  let L : List (ℂ × ℂ) := cancelOppositeEdges L_all
  obtain ⟨hL_sub, hL_no_opp, hL_cnt, hL_bal_imp, hL_equiv⟩ :=
    cancelOppositeEdges_spec L_all.length L_all le_rfl hne_all
  have hL_bal : IsBalancedIntervals L := hL_bal_imp hbal_all
  have hL_cyc : (intervalsChain L).IsCycle := (theorem13_4 L hL_bal).2
  -- Trace of `intervalsChain L` lies in `Ω \ K`
  have hL_trace : (intervalsChain L).trace ⊆ Ω \ K := by
    have hmem_tr : ∀ z ∈ (intervalsChain L).trace, ∃ e ∈ L, z ∈ segment ℝ e.1 e.2 := by
      intro z hz
      have hrec : ∀ es : List (ℂ × ℂ), z ∈ (intervalsChain es).trace →
          ∃ e ∈ es, z ∈ segment ℝ e.1 e.2 := by
        intro es hes
        induction es with
        | nil => simp [intervalsChain] at hes
        | cons d es' ih =>
          simp only [intervalsChain, List.map_cons, RudinRCA.Chapter10.BookChain.trace_cons,
            RudinRCA.Chapter10.orientedSegment_trace, mem_union] at hes
          rcases hes with hd | hes'
          · exact ⟨d, List.mem_cons_self, hd⟩
          · obtain ⟨e, he, hze⟩ := ih hes'
            exact ⟨e, List.mem_cons_of_mem _ he, hze⟩
      exact hrec L hz
    intro z hz
    obtain ⟨e, heL, hze⟩ := hmem_tr z hz
    have he_all : e ∈ L_all := hL_sub e heL
    obtain ⟨p, hp_list, hep⟩ := List.mem_flatMap.mp he_all
    have hpP : p ∈ P := P.mem_toList.mp hp_list
    obtain ⟨_, p', hrev_p', hseg_p, hseg_p'⟩ := gridSquareEdges_adjacent hδ hep
    have hzΩ : z ∈ Ω := hp_sub_Ω p hpP (hseg_p hze)
    refine ⟨hzΩ, ?_⟩
    intro hzK
    have hp'P : p' ∈ P := hp_in_box p' ⟨z, hseg_p' hze, hzK⟩
    have hrev_all : (e.2, e.1) ∈ L_all :=
      List.mem_flatMap.mpr ⟨p', P.mem_toList.mpr hp'P, hrev_p'⟩
    have hc_e_pos : 1 ≤ L.count e := List.count_pos_iff.mpr heL
    have hc_rev_zero : L.count (e.2, e.1) = 0 :=
      List.count_eq_zero.mpr (hL_no_opp e heL)
    have hdiff := hL_cnt e
    have hc_all_e : L_all.count e ≤ 1 := hcount_le_one e
    have hc_all_rev : 1 ≤ L_all.count (e.2, e.1) := List.count_pos_iff.mpr hrev_all
    change (L.count e : ℤ) - (L.count (e.2, e.1) : ℤ) =
      (L_all.count e : ℤ) - (L_all.count (e.2, e.1) : ℤ) at hdiff
    omega
  -- Relate `(intervalsChain L_all).Ind z` to sum over `p ∈ plist`
  have hL_all_trace_sub : (intervalsChain L_all).trace ⊆ ⋃ p ∈ P, gridSquare δ p := by
    have hrec : ∀ ps : List (ℤ × ℤ),
        (intervalsChain (ps.flatMap (gridSquareEdges δ))).trace ⊆
          ⋃ p ∈ ps, gridSquare δ p := by
      intro ps
      induction ps with
      | nil => simp [intervalsChain]
      | cons p ps' ih =>
        simp only [intervalsChain, List.flatMap_cons, List.map_append,
          RudinRCA.Chapter10.BookChain.trace_append]
        intro z hz
        rcases hz with hzp | hzs
        · exact mem_iUnion₂.mpr ⟨p, List.mem_cons_self, gridSquareChain_trace_subset hδ p hzp⟩
        · obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.mp (ih hzs)
          exact mem_iUnion₂.mpr ⟨q, List.mem_cons_of_mem _ hq, hzq⟩
    intro z hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp (hrec plist hz)
    exact mem_iUnion₂.mpr ⟨p, P.mem_toList.mp hp, hzp⟩
  have hInd_flatMap : ∀ (ps : List (ℤ × ℤ)) (z : ℂ),
      (intervalsChain (ps.flatMap (gridSquareEdges δ))).Ind z =
        (ps.map (fun p => (gridSquareChain δ p).Ind z)).sum := by
    intro ps z
    induction ps with
    | nil => simp [intervalsChain]
    | cons p ps' ih =>
      simp only [intervalsChain, List.flatMap_cons, List.map_append,
        RudinRCA.Chapter10.BookChain.Ind_append, List.map_cons, List.sum_cons]
      exact congrArg ((gridSquareChain δ p).Ind z + ·) ih
  -- `Ind = 0` outside `Ω`
  have hInd_ext : ∀ w : ℂ, w ∉ Ω → (intervalsChain L).Ind w = 0 := by
    intro w hw
    have hw_not_all : w ∉ (intervalsChain L_all).trace := by
      intro htr
      obtain ⟨p, hpP, hwp⟩ := mem_iUnion₂.mp (hL_all_trace_sub htr)
      exact hw (hp_sub_Ω p hpP hwp)
    have hw_not_L : w ∉ (intervalsChain L).trace := fun htr => hw (hL_trace htr).1
    rw [RudinRCA.Chapter10.BookChain.Ind_congr_equiv hL_equiv
      (fun h => h.elim hw_not_L hw_not_all), hInd_flatMap]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨p, hp_list, rfl⟩ := List.mem_map.mp hx
    have hpP : p ∈ P := P.mem_toList.mp hp_list
    have hw_not_p : w ∉ gridSquare δ p := fun hwp => hw (hp_sub_Ω p hpP hwp)
    exact RudinRCA.Chapter10.theorem10_36_convex_exterior_Ind (convex_gridSquare δ p)
      (gridSquareChain δ p) (gridSquareChain_isCycle δ p)
      (gridSquareChain_trace_subset hδ p) w hw_not_p
  -- `Ind = 1` on `gridSquareOpen δ p₀` for any `p₀ ∈ P`
  have hInd_open_P : ∀ p₀ ∈ P, ∀ z₀ ∈ gridSquareOpen δ p₀,
      (intervalsChain L).Ind z₀ = 1 := by
    intro p₀ hp₀ z₀ hz₀
    have hz₀_not_all : z₀ ∉ (intervalsChain L_all).trace := by
      have hrec : ∀ ps : List (ℤ × ℤ),
          z₀ ∉ (intervalsChain (ps.flatMap (gridSquareEdges δ))).trace := by
        intro ps
        induction ps with
        | nil => simp [intervalsChain]
        | cons q ps' ih =>
          simp only [intervalsChain, List.flatMap_cons, List.map_append,
            RudinRCA.Chapter10.BookChain.trace_append, mem_union, not_or]
          exact ⟨Set.disjoint_left.mp (gridSquareOpen_disjoint_trace hδ p₀ q) hz₀, ih⟩
      exact hrec plist
    have hz₀_not_L : z₀ ∉ (intervalsChain L).trace := by
      intro htr
      apply hz₀_not_all
      -- Every edge of `L` is an edge of `L_all`
      have hsub_tr : (intervalsChain L).trace ⊆ (intervalsChain L_all).trace := by
        have hrec : ∀ es : List (ℂ × ℂ), (∀ e ∈ es, e ∈ L_all) →
            (intervalsChain es).trace ⊆ (intervalsChain L_all).trace := by
          intro es hes
          induction es with
          | nil => simp [intervalsChain]
          | cons d es' ih =>
            rw [show intervalsChain (d :: es') =
                RudinRCA.Chapter10.orientedSegment d.1 d.2 :: intervalsChain es' from rfl,
              RudinRCA.Chapter10.BookChain.trace_cons]
            refine union_subset ?_ (ih fun e he => hes e (List.mem_cons_of_mem _ he))
            have hd_all := hes d List.mem_cons_self
            have hmem_map : RudinRCA.Chapter10.orientedSegment d.1 d.2 ∈ intervalsChain L_all :=
              List.mem_map.mpr ⟨d, hd_all, rfl⟩
            have hperm' := List.perm_cons_erase hmem_map
            rw [bookChain_trace_perm hperm', RudinRCA.Chapter10.BookChain.trace_cons]
            exact subset_union_left
        exact hrec L hL_sub
      exact hsub_tr htr
    rw [RudinRCA.Chapter10.BookChain.Ind_congr_equiv hL_equiv
      (fun h => h.elim hz₀_not_L hz₀_not_all), hInd_flatMap]
    have hp₀_list : p₀ ∈ plist := P.mem_toList.mpr hp₀
    let ps' := plist.erase p₀
    have hperm_p : plist.Perm (p₀ :: ps') := List.perm_cons_erase hp₀_list
    have hp₀_not_ps' : p₀ ∉ ps' := (List.nodup_cons.mp (hperm_p.nodup_iff.mp hnodup_p)).1
    rw [(hperm_p.map _).sum_eq, List.map_cons, List.sum_cons,
      gridSquareChain_Ind_open hδ p₀ hz₀]
    have hrest0 : (ps'.map (fun q => (gridSquareChain δ q).Ind z₀)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨q, hq_mem, rfl⟩ := List.mem_map.mp hx
      have hqp : q ≠ p₀ := fun heq => hp₀_not_ps' (heq ▸ hq_mem)
      have hz₀_not_q : z₀ ∉ gridSquare δ q := by
        intro hzq
        by_cases h1 : q.1 = p₀.1
        · have h2 : q.2 ≠ p₀.2 := fun h2 => hqp (Prod.ext h1 h2)
          by_cases hlt : q.2 < p₀.2
          · have hle : q.2 + 1 ≤ p₀.2 := by omega
            have : ((q.2 : ℝ) + 1) * δ ≤ (p₀.2 : ℝ) * δ := by
              exact_mod_cast mul_le_mul_of_nonneg_right (Int.cast_le.mpr hle) hδ.le
            linarith [hzq.2.2.2, hz₀.2.2.1]
          · have hle : p₀.2 + 1 ≤ q.2 := by omega
            have : ((p₀.2 : ℝ) + 1) * δ ≤ (q.2 : ℝ) * δ := by
              exact_mod_cast mul_le_mul_of_nonneg_right (Int.cast_le.mpr hle) hδ.le
            linarith [hz₀.2.2.2, hzq.2.2.1]
        · by_cases hlt : q.1 < p₀.1
          · have hle : q.1 + 1 ≤ p₀.1 := by omega
            have : ((q.1 : ℝ) + 1) * δ ≤ (p₀.1 : ℝ) * δ := by
              exact_mod_cast mul_le_mul_of_nonneg_right (Int.cast_le.mpr hle) hδ.le
            linarith [hzq.2.1, hz₀.1]
          · have hle : p₀.1 + 1 ≤ q.1 := by omega
            have : ((p₀.1 : ℝ) + 1) * δ ≤ (q.1 : ℝ) * δ := by
              exact_mod_cast mul_le_mul_of_nonneg_right (Int.cast_le.mpr hle) hδ.le
            linarith [hz₀.2.1, hzq.1]
      exact RudinRCA.Chapter10.theorem10_36_convex_exterior_Ind (convex_gridSquare δ q)
        (gridSquareChain δ q) (gridSquareChain_isCycle δ q)
        (gridSquareChain_trace_subset hδ q) z₀ hz₀_not_q
    rw [hrest0, add_zero]
  -- By continuity of `Ind` off `Γ.trace`, `Ind = 1` on all of `K`
  have hInd_K : ∀ z ∈ K, (intervalsChain L).Ind z = 1 := by
    intro z hzK
    obtain ⟨p₀, hp₀, hzp₀⟩ := hz_mem_some_P z hzK
    have hz_not_tr : z ∈ ((intervalsChain L).trace)ᶜ :=
      fun htr => (hL_trace htr).2 hzK
    have hopen_compl : IsOpen ((intervalsChain L).trace)ᶜ :=
      (intervalsChain L).isClosed_trace.isOpen_compl
    obtain ⟨ε, hε, hball_compl⟩ := Metric.isOpen_iff.mp hopen_compl z hz_not_tr
    let c₀ := gridCenter δ p₀
    let t : ℝ := min (1 / 2) (ε / (2 * (‖c₀ - z‖ + 1)))
    have ht_pos : 0 < t := lt_min (by norm_num) (by positivity)
    have ht_lt1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    let z_t : ℂ := (1 - t : ℝ) • z + t • c₀
    have hzt_ball : z_t ∈ ball z ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hdiff : z_t - z = t • (c₀ - z) := by
        change ((1 - t : ℝ) : ℂ) * z + (t : ℝ) * c₀ - z = (t : ℝ) * (c₀ - z)
        push_cast
        ring
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
      have ht_le : t ≤ ε / (2 * (‖c₀ - z‖ + 1)) := min_le_right _ _
      calc
        t * ‖c₀ - z‖ ≤ (ε / (2 * (‖c₀ - z‖ + 1))) * ‖c₀ - z‖ :=
          mul_le_mul_of_nonneg_right ht_le (norm_nonneg _)
        _ < (ε / (2 * (‖c₀ - z‖ + 1))) * (2 * (‖c₀ - z‖ + 1)) := by
          apply mul_lt_mul_of_pos_left _ (by positivity)
          linarith [norm_nonneg (c₀ - z)]
        _ = ε := div_mul_cancel₀ ε (by positivity)
    have hzt_open : z_t ∈ gridSquareOpen δ p₀ := by
      have hc₀_re : c₀.re = (p₀.1 : ℝ) * δ + (1 / 2) * δ := by simp [c₀, gridCenter]; ring
      have hc₀_im : c₀.im = (p₀.2 : ℝ) * δ + (1 / 2) * δ := by simp [c₀, gridCenter]; ring
      have hzt_re : z_t.re = (1 - t) * z.re + t * c₀.re := by simp [z_t]
      have hzt_im : z_t.im = (1 - t) * z.im + t * c₀.im := by simp [z_t]
      have h1mt_pos : 0 < 1 - t := by linarith
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hzt_re, hc₀_re]
        calc (p₀.1 : ℝ) * δ = (1 - t) * ((p₀.1 : ℝ) * δ) + t * ((p₀.1 : ℝ) * δ) := by ring
          _ < (1 - t) * z.re + t * ((p₀.1 : ℝ) * δ + (1 / 2) * δ) :=
            add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hzp₀.1 h1mt_pos.le)
              (mul_lt_mul_of_pos_left (by linarith) ht_pos)
      · rw [hzt_re, hc₀_re]
        have hup : z.re ≤ (p₀.1 : ℝ) * δ + δ := by linarith [hzp₀.2.1]
        calc (1 - t) * z.re + t * ((p₀.1 : ℝ) * δ + (1 / 2) * δ)
            < (1 - t) * ((p₀.1 : ℝ) * δ + δ) + t * ((p₀.1 : ℝ) * δ + δ) :=
              add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hup h1mt_pos.le)
                (mul_lt_mul_of_pos_left (by linarith) ht_pos)
          _ = ((p₀.1 : ℝ) + 1) * δ := by ring
      · rw [hzt_im, hc₀_im]
        calc (p₀.2 : ℝ) * δ = (1 - t) * ((p₀.2 : ℝ) * δ) + t * ((p₀.2 : ℝ) * δ) := by ring
          _ < (1 - t) * z.im + t * ((p₀.2 : ℝ) * δ + (1 / 2) * δ) :=
            add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hzp₀.2.2.1 h1mt_pos.le)
              (mul_lt_mul_of_pos_left (by linarith) ht_pos)
      · rw [hzt_im, hc₀_im]
        have hup : z.im ≤ (p₀.2 : ℝ) * δ + δ := by linarith [hzp₀.2.2.2]
        calc (1 - t) * z.im + t * ((p₀.2 : ℝ) * δ + (1 / 2) * δ)
            < (1 - t) * ((p₀.2 : ℝ) * δ + δ) + t * ((p₀.2 : ℝ) * δ + δ) :=
              add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hup h1mt_pos.le)
                (mul_lt_mul_of_pos_left (by linarith) ht_pos)
          _ = ((p₀.2 : ℝ) + 1) * δ := by ring
    have heq_ind := RudinRCA.Chapter10.BookChain.Ind_eq_of_isPreconnected_compl_of_isCycle
      hL_cyc (convex_ball z ε).isPreconnected hball_compl (Metric.mem_ball_self hε) hzt_ball
    rw [heq_ind]
    exact hInd_open_P p₀ hp₀ z_t hzt_open
  -- Apply global Cauchy integral formula `10.35`
  refine ⟨L, hL_bal, hL_cyc, hL_trace, hInd_ext, hInd_K, ?_⟩
  intro f hf z hzK
  have htr_Ω : (intervalsChain L).trace ⊆ Ω := hL_trace.trans sdiff_subset
  have hz_not_tr : z ∉ (intervalsChain L).trace := fun htr => (hL_trace htr).2 hzK
  have hcauchy := ((RudinRCA.Chapter10.theorem10_35 hΩ).1 hf (intervalsChain L)
    hL_cyc htr_Ω hInd_ext).1 z (hKΩ hzK) hz_not_tr
  rw [hInd_K z hzK, mul_one] at hcauchy
  exact hcauchy


/-! ## 13.6 Compact Runge approximation and countable complement components -/

/-- For any compact `K ⊆ ℂ`, `sphericalCompl K = S² \ K` is open in `S²`. -/
theorem isOpen_sphericalCompl_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    IsOpen (sphericalCompl K) :=
  OnePoint.isOpen_compl_image_coe.mpr ⟨hK.isClosed, hK⟩

/-- The connected component of any `x ∈ s` inside `s` is connected. -/
theorem isConnected_connectedComponentIn_of_mem {α : Type*} [TopologicalSpace α]
    {s : Set α} {x : α} (hx : x ∈ s) :
    IsConnected (connectedComponentIn s x) :=
  ⟨⟨x, mem_connectedComponentIn hx⟩, isPreconnected_connectedComponentIn⟩

/-- Every connected component of an open subset `U ⊆ S²` is open in `S²`. -/
theorem isOpen_connectedComponentIn_spherical {U : Set RiemannSphere} (hU : IsOpen U)
    (x : RiemannSphere) :
    IsOpen (connectedComponentIn U x) := by
  rw [isOpen_riemannSphere_iff]
  constructor
  · intro z hzC
    have hzU : (z : RiemannSphere) ∈ U := connectedComponentIn_subset U x hzC
    obtain ⟨r, hr, hsub⟩ := ((isOpen_riemannSphere_iff U).mp hU).1 z hzU
    refine ⟨r, hr, ?_⟩
    have hpre : IsPreconnected (((↑) : ℂ → RiemannSphere) '' ball z r) :=
      (convex_ball z r).isPreconnected.image _ OnePoint.continuous_coe.continuousOn
    have hmem : (z : RiemannSphere) ∈ ((↑) : ℂ → RiemannSphere) '' ball z r :=
      ⟨z, Metric.mem_ball_self hr, rfl⟩
    rw [connectedComponentIn_eq hzC]
    exact hpre.subset_connectedComponentIn hmem hsub
  · intro hinfC
    have hinfU : (∞ : RiemannSphere) ∈ U := connectedComponentIn_subset U x hinfC
    obtain ⟨r, hr, hsub⟩ := ((isOpen_riemannSphere_iff U).mp hU).2 hinfU
    let r' : ℝ := max r 1
    have hr'_pos : 0 < r' := lt_max_of_lt_left hr
    have hsub' : infinityDisc r' ⊆ U := by
      refine Subset.trans ?_ hsub
      intro p hp
      induction p using OnePoint.rec with
      | infty => exact infinity_mem_infinityDisc r
      | coe w =>
        rw [coe_mem_infinityDisc] at hp ⊢
        exact lt_of_le_of_lt (le_max_left r 1) hp
    refine ⟨r', hr'_pos, ?_⟩
    rw [connectedComponentIn_eq hinfC]
    exact (isConnected_infinityDisc hr'_pos.le).isPreconnected.subset_connectedComponentIn
      (infinity_mem_infinityDisc r') hsub'

/-- Every open subset `U ⊆ S²` has at most countably many connected components. -/
theorem countable_components_of_isOpen_spherical {U : Set RiemannSphere} (hU : IsOpen U) :
    {C : Set RiemannSphere | ∃ x ∈ U, C = connectedComponentIn U x}.Countable := by
  obtain ⟨D, hD_count, hD_dense⟩ := TopologicalSpace.exists_countable_dense ℂ
  let comps := {C : Set RiemannSphere | ∃ x ∈ U, C = connectedComponentIn U x}
  have hmeet : ∀ C : comps, ∃ d : D, ((d : ℂ) : RiemannSphere) ∈ C.1 := by
    rintro ⟨C, x, hxU, rfl⟩
    have hC_open : IsOpen (connectedComponentIn U x) :=
      isOpen_connectedComponentIn_spherical hU x
    have hxC : x ∈ connectedComponentIn U x := mem_connectedComponentIn hxU
    have hpre_open : IsOpen (((↑) : ℂ → RiemannSphere) ⁻¹' connectedComponentIn U x) :=
      hC_open.preimage OnePoint.continuous_coe
    have hpre_ne : (((↑) : ℂ → RiemannSphere) ⁻¹' connectedComponentIn U x).Nonempty := by
      induction x using OnePoint.rec with
      | infty =>
        obtain ⟨r, hr, hsub⟩ := ((isOpen_riemannSphere_iff _).mp hC_open).2 hxC
        refine ⟨((r + 1 : ℝ) : ℂ), hsub ?_⟩
        rw [coe_mem_infinityDisc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      | coe z => exact ⟨z, hxC⟩
    obtain ⟨w, hwC, hwD⟩ := hD_dense.inter_open_nonempty _ hpre_open hpre_ne
    exact ⟨⟨w, hwD⟩, hwC⟩
  let pick : comps → D := fun C => Classical.choose (hmeet C)
  have hpick_mem : ∀ C : comps, (((pick C : D) : ℂ) : RiemannSphere) ∈ C.1 :=
    fun C => Classical.choose_spec (hmeet C)
  have hinj : Function.Injective pick := by
    intro C₁ C₂ heq
    let z₀ : ℂ := ((pick C₂ : D) : ℂ)
    have hp₁ : (z₀ : RiemannSphere) ∈ C₁.1 := by
      have h := hpick_mem C₁
      rwa [heq] at h
    have hp₂ : (z₀ : RiemannSphere) ∈ C₂.1 := hpick_mem C₂
    rcases C₁ with ⟨S₁, x₁, _, rfl⟩
    rcases C₂ with ⟨S₂, x₂, _, rfl⟩
    apply Subtype.ext
    dsimp only at hp₁ hp₂ ⊢
    exact (connectedComponentIn_eq hp₁).trans (connectedComponentIn_eq hp₂).symm
  have : Countable D := hD_count.to_subtype
  have : Countable comps := hinj.countable
  exact Set.to_countable comps

/-- For any compact `K ⊆ ℂ`, `S² \ K` has at most countably many connected components (RCA 13.6). -/
theorem countable_components_sphericalCompl {K : Set ℂ} (hK : IsCompact K) :
    {C : Set RiemannSphere |
      ∃ x ∈ sphericalCompl K, C = connectedComponentIn (sphericalCompl K) x}.Countable :=
  countable_components_of_isOpen_spherical (isOpen_sphericalCompl_of_isCompact hK)

/-- Removing `∞` from an open connected subset `V ⊆ S²` preserves connectedness in `ℂ` whenever
the finite part `((↑) : ℂ → RiemannSphere) ⁻¹' V` is nonempty. -/
theorem isConnected_preimage_coe_of_isOpen {V : Set RiemannSphere}
    (hV_open : IsOpen V) (hV_conn : IsConnected V)
    (hne : (((↑) : ℂ → RiemannSphere) ⁻¹' V).Nonempty) :
    IsConnected (((↑) : ℂ → RiemannSphere) ⁻¹' V) := by
  let V₀ : Set ℂ := ((↑) : ℂ → RiemannSphere) ⁻¹' V
  refine ⟨hne, fun U₁ U₂ hU₁ hU₂ hsub hne₁ hne₂ => ?_⟩
  by_contra hdisj_not
  have hdisj : V₀ ∩ (U₁ ∩ U₂) = ∅ := Set.not_nonempty_iff_eq_empty.mp hdisj_not
  by_cases hinf : (∞ : RiemannSphere) ∈ V
  · obtain ⟨r, hr, hinf_sub⟩ := ((isOpen_riemannSphere_iff V).mp hV_open).2 hinf
    have hext_sub : exteriorDisc r ⊆ V₀ := by
      intro z hz
      exact hinf_sub ((coe_mem_infinityDisc z r).mpr hz)
    have hext_conn : IsConnected (exteriorDisc r) := by
      have heq : exteriorDisc r = (closedBall (0 : ℂ) r)ᶜ := by
        ext z; simp [exteriorDisc, mem_closedBall, dist_zero_right]
      rw [heq]
      exact RudinRCA.Chapter10.isConnected_compl_closedBall 0 hr.le
    by_cases he₁ : (exteriorDisc r ∩ U₁).Nonempty
    · by_cases he₂ : (exteriorDisc r ∩ U₂).Nonempty
      · have hoverlap := hext_conn.isPreconnected U₁ U₂ hU₁ hU₂ (hext_sub.trans hsub) he₁ he₂
        exact hdisj_not (hoverlap.mono (inter_subset_inter_left _ hext_sub))
      · have he₂_empty : exteriorDisc r ∩ U₂ = ∅ := Set.not_nonempty_iff_eq_empty.mp he₂
        have hext_U₁ : exteriorDisc r ⊆ U₁ := by
          intro z hz
          rcases hsub (hext_sub hz) with hz₁ | hz₂
          · exact hz₁
          · exfalso; exact Set.notMem_empty z (he₂_empty ▸ ⟨hz, hz₂⟩)
        let W₁ : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' U₁ ∪ infinityDisc r
        let W₂ : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' U₂
        have hW₁_open : IsOpen W₁ :=
          (finite_chart_open_embedding.isOpenMap U₁ hU₁).union (isOpen_infinityDisc r)
        have hW₂_open : IsOpen W₂ := finite_chart_open_embedding.isOpenMap U₂ hU₂
        have hV_sub : V ⊆ W₁ ∪ W₂ := by
          intro p hp
          induction p using OnePoint.rec with
          | infty => exact Or.inl (Or.inr (infinity_mem_infinityDisc r))
          | coe z =>
            rcases hsub hp with hz₁ | hz₂
            · exact Or.inl (Or.inl ⟨z, hz₁, rfl⟩)
            · exact Or.inr ⟨z, hz₂, rfl⟩
        obtain ⟨z₂, hz₂V, hz₂U⟩ := hne₂
        have hVW₁ : (V ∩ W₁).Nonempty :=
          ⟨∞, hinf, Or.inr (infinity_mem_infinityDisc r)⟩
        have hVW₂ : (V ∩ W₂).Nonempty := ⟨(z₂ : RiemannSphere), hz₂V, z₂, hz₂U, rfl⟩
        obtain ⟨p, hpV, hpW₁, hpW₂⟩ := hV_conn.isPreconnected W₁ W₂ hW₁_open hW₂_open hV_sub hVW₁ hVW₂
        rcases hpW₂ with ⟨z, hzU₂, rfl⟩
        have hzU₁ : z ∈ U₁ := by
          rcases hpW₁ with ⟨z', hz'U₁, hzeq⟩ | hzinf
          · exact OnePoint.coe_injective hzeq ▸ hz'U₁
          · exact hext_U₁ ((coe_mem_infinityDisc z r).mp hzinf)
        exact hdisj_not ⟨z, hpV, hzU₁, hzU₂⟩
    · have he₁_empty : exteriorDisc r ∩ U₁ = ∅ := Set.not_nonempty_iff_eq_empty.mp he₁
      have hext_U₂ : exteriorDisc r ⊆ U₂ := by
        intro z hz
        rcases hsub (hext_sub hz) with hz₁ | hz₂
        · exfalso; exact Set.notMem_empty z (he₁_empty ▸ ⟨hz, hz₁⟩)
        · exact hz₂
      let W₁ : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' U₁
      let W₂ : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' U₂ ∪ infinityDisc r
      have hW₁_open : IsOpen W₁ := finite_chart_open_embedding.isOpenMap U₁ hU₁
      have hW₂_open : IsOpen W₂ :=
        (finite_chart_open_embedding.isOpenMap U₂ hU₂).union (isOpen_infinityDisc r)
      have hV_sub : V ⊆ W₁ ∪ W₂ := by
        intro p hp
        induction p using OnePoint.rec with
        | infty => exact Or.inr (Or.inr (infinity_mem_infinityDisc r))
        | coe z =>
          rcases hsub hp with hz₁ | hz₂
          · exact Or.inl ⟨z, hz₁, rfl⟩
          · exact Or.inr (Or.inl ⟨z, hz₂, rfl⟩)
      obtain ⟨z₁, hz₁V, hz₁U⟩ := hne₁
      have hVW₁ : (V ∩ W₁).Nonempty := ⟨(z₁ : RiemannSphere), hz₁V, z₁, hz₁U, rfl⟩
      have hVW₂ : (V ∩ W₂).Nonempty := ⟨∞, hinf, Or.inr (infinity_mem_infinityDisc r)⟩
      obtain ⟨p, hpV, hpW₁, hpW₂⟩ := hV_conn.isPreconnected W₁ W₂ hW₁_open hW₂_open hV_sub hVW₁ hVW₂
      rcases hpW₁ with ⟨z, hzU₁, rfl⟩
      have hzU₂ : z ∈ U₂ := by
        rcases hpW₂ with ⟨z', hz'U₂, hzeq⟩ | hzinf
        · exact OnePoint.coe_injective hzeq ▸ hz'U₂
        · exact hext_U₂ ((coe_mem_infinityDisc z r).mp hzinf)
      exact hdisj_not ⟨z, hpV, hzU₁, hzU₂⟩
  · let W₁ : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' U₁
    let W₂ : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' U₂
    have hW₁_open : IsOpen W₁ := finite_chart_open_embedding.isOpenMap U₁ hU₁
    have hW₂_open : IsOpen W₂ := finite_chart_open_embedding.isOpenMap U₂ hU₂
    have hV_sub : V ⊆ W₁ ∪ W₂ := by
      intro p hp
      induction p using OnePoint.rec with
      | infty => exact False.elim (hinf hp)
      | coe z =>
        rcases hsub hp with hz₁ | hz₂
        · exact Or.inl ⟨z, hz₁, rfl⟩
        · exact Or.inr ⟨z, hz₂, rfl⟩
    obtain ⟨z₁, hz₁V, hz₁U⟩ := hne₁
    obtain ⟨z₂, hz₂V, hz₂U⟩ := hne₂
    obtain ⟨p, hpV, ⟨w₁, hw₁U, hpeq₁⟩, ⟨w₂, hw₂U, hpeq₂⟩⟩ :=
      hV_conn.isPreconnected W₁ W₂ hW₁_open hW₂_open hV_sub
        ⟨(z₁ : RiemannSphere), hz₁V, z₁, hz₁U, rfl⟩
        ⟨(z₂ : RiemannSphere), hz₂V, z₂, hz₂U, rfl⟩
    subst hpeq₁
    have hw : w₁ = w₂ := OnePoint.coe_injective hpeq₂.symm
    exact hdisj_not ⟨w₁, hpV, hw₁U, hw ▸ hw₂U⟩

/-- Homogenized polynomial in the local coordinate `w = (z - β)⁻¹` (`z = β + w⁻¹`):
for `w ≠ 0`, `(polyHomAtBeta β d P).eval w = w ^ d * P.eval (β + w⁻¹)`. -/
def polyHomAtBeta (β : ℂ) (d : ℕ) (P : Polynomial ℂ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (d + 1),
    Polynomial.C (P.coeff i) * (Polynomial.C β * Polynomial.X + 1) ^ i * Polynomial.X ^ (d - i)

theorem polyHomAtBeta_eval_zero (β : ℂ) {Q : Polynomial ℂ} (hQ : Q.Monic) :
    (polyHomAtBeta β Q.natDegree Q).eval 0 = 1 := by
  unfold polyHomAtBeta
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
    mul_zero, zero_add, one_pow, mul_one]
  rw [Finset.sum_range_succ]
  have hzero : ∑ x ∈ Finset.range Q.natDegree, Q.coeff x * (0 : ℂ) ^ (Q.natDegree - x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hlt : x < Q.natDegree := Finset.mem_range.mp hx
    rw [zero_pow (by omega), mul_zero]
  rw [hzero, zero_add, Nat.sub_self, pow_zero, mul_one, Polynomial.coeff_natDegree]
  exact hQ.leadingCoeff

theorem polyHomAtBeta_eval_ne_zero (β : ℂ) {d : ℕ} {P : Polynomial ℂ}
    (hdeg : P.natDegree ≤ d) {w : ℂ} (hw : w ≠ 0) :
    (polyHomAtBeta β d P).eval w = w ^ d * P.eval (β + w⁻¹) := by
  unfold polyHomAtBeta
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.mul_sum]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hbw : (β + w⁻¹) * w = β * w + 1 := by
    rw [add_mul, inv_mul_cancel₀ hw]
  have hwd : w ^ d = w ^ i * w ^ (d - i) := by
    rw [← pow_add, Nat.add_sub_of_le hi_le]
  calc
    P.coeff i * (β * w + 1) ^ i * w ^ (d - i)
        = P.coeff i * (((β + w⁻¹) * w) ^ i * w ^ (d - i)) := by rw [hbw, mul_assoc]
    _ = P.coeff i * ((β + w⁻¹) ^ i * (w ^ i * w ^ (d - i))) := by rw [mul_pow, mul_assoc]
    _ = w ^ d * (P.coeff i * (β + w⁻¹) ^ i) := by rw [← hwd]; ring

/-- A rational function `R : ℂ → ℂ` whose spherical poles (finite poles and any pole at `∞`) all
lie in `A ⊆ S²`, presented in reduced coprime form `P / Q` with `Q` monic. -/
def IsRationalWithSphericalPolesIn (R : ℂ → ℂ) (A : Set RiemannSphere) : Prop :=
  ∃ P Q : Polynomial ℂ, Q.Monic ∧ IsCoprime P Q ∧
    (∀ a : ℂ, Q.eval a = 0 → (a : RiemannSphere) ∈ A) ∧
    (Q.natDegree < P.natDegree → (∞ : RiemannSphere) ∈ A) ∧
    (∀ z : ℂ, R z = P.eval z / Q.eval z)

/-- Every `R` with `IsRationalWithSphericalPolesIn R A` is meromorphic on `ℂ` with finite pole set
contained in `{a | (a : S²) ∈ A}`, has an isolated singularity at `∞`, has a removable singularity
at `∞` whenever `∞ ∉ A`, and any pole at `∞` forces `∞ ∈ A`. -/
theorem isRationalWithSphericalPolesIn_poles {R : ℂ → ℂ} {A : Set RiemannSphere}
    (hR : IsRationalWithSphericalPolesIn R A) :
    RudinRCA.Chapter10.BookMeromorphicOn R Set.univ ∧
    (∀ a ∈ RudinRCA.Chapter10.poleSet R Set.univ, (a : RiemannSphere) ∈ A) ∧
    HasIsolatedSingularityAtInfinity R ∧
    ((∞ : RiemannSphere) ∉ A → HasRemovableSingularityAtInfinity R) ∧
    (∀ m : ℕ, HasPoleAtInfinity R m → (∞ : RiemannSphere) ∈ A) := by
  rcases hR with ⟨P, Q, hQ_monic, hcop, hroots, hdeg_inf, hReq⟩
  have hR_fun : R = fun z => P.eval z / Q.eval z := funext hReq
  subst hR_fun
  obtain ⟨P₁, Q₁, _, _, _, hQ₁_monic, hcop₁, hdiv₁, hmul, _, _, hmero, hpole_eq, _, _⟩ :=
    theorem13_2 P Q hQ_monic.ne_zero
  -- Since `Q` is monic and coprime to `P`, `Q₁ = Q` and `P₁ = P`
  have hQ₁_dvd_Q : Q₁ ∣ Q := hdiv₁
  have hQ_dvd_Q₁ : Q ∣ Q₁ := hcop.symm.dvd_of_dvd_mul_left (hmul ▸ dvd_mul_left Q P₁)
  have hQ_eq : Q₁ = Q := Polynomial.eq_of_monic_of_associated hQ₁_monic hQ_monic
    (associated_of_dvd_dvd hQ₁_dvd_Q hQ_dvd_Q₁)
  have hP_eq : P₁ = P :=
    mul_right_cancel₀ hQ_monic.ne_zero (by rw [hQ_eq] at hmul; exact hmul.symm)
  rw [hP_eq, hQ_eq] at hmero hpole_eq
  -- Isolated singularity at infinity: `Q` has finitely many roots
  have hfin_roots : {a : ℂ | Q.eval a = 0}.Finite := by
    have hsub : {a : ℂ | Q.eval a = 0} ⊆ (Q.roots.toFinset : Set ℂ) := by
      intro a ha
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hQ_monic.ne_zero,
        Polynomial.IsRoot.def]
      exact ha
    exact (Finset.finite_toSet _).subset hsub
  obtain ⟨B, _, hB⟩ := hfin_roots.isBounded.exists_pos_norm_le
  let rad : ℝ := max 1 (B + 1)
  have hrad_pos : 0 < rad := lt_max_of_lt_left zero_lt_one
  have hQ_ne_ext : ∀ z ∈ exteriorDisc rad, Q.eval z ≠ 0 := by
    intro z hz hQz
    have hle : ‖z‖ ≤ B := hB z hQz
    have hgt : rad < ‖z‖ := hz
    linarith [le_max_right 1 (B + 1)]
  have hiso_inf : HasIsolatedSingularityAtInfinity (fun z => P.eval z / Q.eval z) := by
    refine ⟨rad, hrad_pos, ?_⟩
    intro z hz
    exact ((P.differentiableAt (x := z)).div (Q.differentiableAt (x := z))
      (hQ_ne_ext z hz)).differentiableWithinAt
  -- Removability at `∞` when `∞ ∉ A` (`P.natDegree ≤ Q.natDegree`)
  have hrem_of_not_inf :
      (∞ : RiemannSphere) ∉ A →
        HasRemovableSingularityAtInfinity (fun z => P.eval z / Q.eval z) := by
    intro hnot_inf
    have hdeg_le : P.natDegree ≤ Q.natDegree := by
      by_contra hlt
      exact hnot_inf (hdeg_inf (Nat.lt_of_not_ge hlt))
    let d := Q.natDegree
    let P_rev := polyHomAtBeta 0 d P
    let Q_rev := polyHomAtBeta 0 d Q
    have hQ_rev0 : Q_rev.eval 0 = 1 := polyHomAtBeta_eval_zero 0 hQ_monic
    have hopen_Qrev : IsOpen {w : ℂ | Q_rev.eval w ≠ 0} :=
      isOpen_compl_singleton.preimage Q_rev.continuous
    have h0_mem : (0 : ℂ) ∈ {w : ℂ | Q_rev.eval w ≠ 0} := by
      simp [hQ_rev0]
    have hana : AnalyticAt ℂ (fun w => P_rev.eval w / Q_rev.eval w) 0 := by
      have hdiff : DifferentiableOn ℂ (fun w => P_rev.eval w / Q_rev.eval w)
          {w : ℂ | Q_rev.eval w ≠ 0} := by
        intro w hw
        exact ((P_rev.differentiableAt (x := w)).div (Q_rev.differentiableAt (x := w))
          hw).differentiableWithinAt
      exact hdiff.analyticOnNhd hopen_Qrev 0 h0_mem
    refine ⟨P_rev.eval 0, ?_⟩
    apply hana.congr
    filter_upwards [hopen_Qrev.mem_nhds h0_mem] with w hw
    by_cases hw0 : w = 0
    · subst hw0
      simp [hQ_rev0]
    · simp only [Function.update_of_ne hw0]
      have hP_w := polyHomAtBeta_eval_ne_zero 0 hdeg_le hw0
      have hQ_w := polyHomAtBeta_eval_ne_zero 0 (le_refl d) hw0
      simp only [zero_add] at hP_w hQ_w
      change P_rev.eval w / Q_rev.eval w = P.eval w⁻¹ / Q.eval w⁻¹
      rw [hP_w, hQ_w, mul_div_mul_left _ _ (pow_ne_zero d hw0)]
  refine ⟨⟨_, hmero⟩, ?_, hiso_inf, hrem_of_not_inf, ?_⟩
  · intro a ha
    rw [hpole_eq] at ha
    exact hroots a ha
  · intro m hpole
    by_contra hnot_inf
    exact (singularity_at_infinity_trichotomy hiso_inf).2.1 ⟨hrem_of_not_inf hnot_inf, m, hpole⟩

/-- If `IsRationalWithSphericalPolesIn R {∞}`, then `R` has no finite poles and is a polynomial. -/
theorem isRationalWithSphericalPolesIn_singleton_infty {R : ℂ → ℂ}
    (hR : IsRationalWithSphericalPolesIn R ({∞} : Set RiemannSphere)) :
    ∃ P : Polynomial ℂ, ∀ z : ℂ, R z = P.eval z := by
  rcases hR with ⟨P, Q, hQ_monic, _, hroots, _, hReq⟩
  have hQ_deg0 : Q.natDegree = 0 := by
    by_contra hne
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root Q (by rw [Polynomial.degree_eq_natDegree hQ_monic.ne_zero]; exact_mod_cast hne)
    have hmem := hroots a ha
    simp at hmem
  have hQ1 : Q = 1 := Polynomial.eq_one_of_monic_natDegree_zero hQ_monic hQ_deg0
  refine ⟨P, fun z => ?_⟩
  rw [hReq z, hQ1, Polynomial.eval_one, div_one]

/-- If `IsRationalWithSphericalPolesIn R ∅`, then `R` is constant on `ℂ`. -/
theorem isRationalWithSphericalPolesIn_empty {R : ℂ → ℂ}
    (hR : IsRationalWithSphericalPolesIn R ∅) :
    ∃ c : ℂ, ∀ z : ℂ, R z = c := by
  rcases hR with ⟨P, Q, hQ_monic, _, hroots, hdeg_inf, hReq⟩
  have hQ_deg0 : Q.natDegree = 0 := by
    by_contra hne
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root Q (by rw [Polynomial.degree_eq_natDegree hQ_monic.ne_zero]; exact_mod_cast hne)
    exact Set.notMem_empty _ (hroots a ha)
  have hQ1 : Q = 1 := Polynomial.eq_one_of_monic_natDegree_zero hQ_monic hQ_deg0
  have hP_deg0 : P.natDegree = 0 := by
    by_contra hne
    have hlt : Q.natDegree < P.natDegree := by omega
    exact Set.notMem_empty _ (hdeg_inf hlt)
  let c : ℂ := P.coeff 0
  have hP_eq : P = Polynomial.C c := Polynomial.eq_C_of_natDegree_eq_zero hP_deg0
  refine ⟨c, fun z => ?_⟩
  rw [hReq z, hQ1, Polynomial.eval_one, div_one, hP_eq, Polynomial.eval_C]

/-- Unreduced polynomial pairs `(P, Q)` representing rational functions with spherical poles in `A`.
Closed under addition, scalar multiplication, polynomials (if `∞ ∈ A`), and principal parts at
finite points of `A`, and reduces via `13.2` to `IsRationalWithSphericalPolesIn`. -/
def AdmissiblePolyPair (A : Set RiemannSphere) (P Q : Polynomial ℂ) : Prop :=
  Q ≠ 0 ∧
    (∀ a : ℂ, Q.eval a = 0 → (a : RiemannSphere) ∈ A) ∧
    ((∞ : RiemannSphere) ∉ A → P.natDegree ≤ Q.natDegree)

theorem admissiblePolyPair_zero (A : Set RiemannSphere) :
    AdmissiblePolyPair A 0 1 :=
  ⟨one_ne_zero, fun _ h => by simp at h, fun _ => by simp⟩

theorem admissiblePolyPair_const (A : Set RiemannSphere) (c : ℂ) :
    AdmissiblePolyPair A (Polynomial.C c) 1 :=
  ⟨one_ne_zero, fun _ h => by simp at h, fun _ => by simp⟩

theorem admissiblePolyPair_add {A : Set RiemannSphere} {P₁ Q₁ P₂ Q₂ : Polynomial ℂ}
    (h₁ : AdmissiblePolyPair A P₁ Q₁) (h₂ : AdmissiblePolyPair A P₂ Q₂) :
    AdmissiblePolyPair A (P₁ * Q₂ + P₂ * Q₁) (Q₁ * Q₂) := by
  refine ⟨mul_ne_zero h₁.1 h₂.1, ?_, ?_⟩
  · intro a ha
    rw [Polynomial.eval_mul] at ha
    rcases mul_eq_zero.mp ha with ha₁ | ha₂
    · exact h₁.2.1 a ha₁
    · exact h₂.2.1 a ha₂
  · intro hinf
    rw [Polynomial.natDegree_mul h₁.1 h₂.1]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · by_cases hP₁ : P₁ = 0
      · simp [hP₁]
      · rw [Polynomial.natDegree_mul hP₁ h₂.1]
        exact Nat.add_le_add_right (h₁.2.2 hinf) _
    · by_cases hP₂ : P₂ = 0
      · simp [hP₂]
      · rw [Polynomial.natDegree_mul hP₂ h₁.1]
        have hle := h₂.2.2 hinf
        omega

theorem admissiblePolyPair_smul {A : Set RiemannSphere} (c : ℂ) {P Q : Polynomial ℂ}
    (h : AdmissiblePolyPair A P Q) :
    AdmissiblePolyPair A (Polynomial.C c * P) Q :=
  ⟨h.1, h.2.1, fun hinf => (Polynomial.natDegree_C_mul_le c P).trans (h.2.2 hinf)⟩

theorem admissiblePolyPair_poly_of_infty_mem {A : Set RiemannSphere}
    (hinf : (∞ : RiemannSphere) ∈ A) (P : Polynomial ℂ) :
    AdmissiblePolyPair A P 1 :=
  ⟨one_ne_zero, fun _ h => by simp at h, fun hnot => False.elim (hnot hinf)⟩

theorem admissiblePolyPair_inv_pow {A : Set RiemannSphere} {a : ℂ}
    (ha : (a : RiemannSphere) ∈ A) (k : ℕ) :
    AdmissiblePolyPair A 1 ((Polynomial.X - Polynomial.C a) ^ k) := by
  refine ⟨pow_ne_zero k (Polynomial.X_sub_C_ne_zero a), ?_, fun _ => by simp⟩
  intro z hz
  rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hz
  have hza : z = a := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)
  exact hza ▸ ha

/-- Finite linear combination of admissible pairs produces an admissible pair whose quotient equals
the sum of quotients at every finite point `z` with `(z : S²) ∉ A`. -/
theorem admissiblePolyPair_finset_sum {ι : Type*} (A : Set RiemannSphere) (s : Finset ι)
    (P Q : ι → Polynomial ℂ) (h : ∀ i ∈ s, AdmissiblePolyPair A (P i) (Q i)) :
    ∃ P_tot Q_tot : Polynomial ℂ, AdmissiblePolyPair A P_tot Q_tot ∧
      ∀ z : ℂ, (z : RiemannSphere) ∉ A →
        P_tot.eval z / Q_tot.eval z = ∑ i ∈ s, (P i).eval z / (Q i).eval z := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    refine ⟨0, 1, admissiblePolyPair_zero A, fun z _ => by simp⟩
  · intro i₀ s' hi₀ ih h
    obtain ⟨P_s, Q_s, hadm_s, heval_s⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hadm₀ := h i₀ (Finset.mem_insert_self i₀ s')
    refine ⟨P i₀ * Q_s + P_s * Q i₀, Q i₀ * Q_s, admissiblePolyPair_add hadm₀ hadm_s, ?_⟩
    intro z hz
    have hQ₀z : (Q i₀).eval z ≠ 0 := fun h0 => hz (hadm₀.2.1 z h0)
    have hQsz : Q_s.eval z ≠ 0 := fun h0 => hz (hadm_s.2.1 z h0)
    rw [Finset.sum_insert hi₀, ← heval_s z hz, div_add_div _ _ hQ₀z hQsz]
    simp only [Polynomial.eval_add, Polynomial.eval_mul]
    congr 1
    ring

/-- Reducing an `AdmissiblePolyPair A P Q` via `13.2` yields `R` with
`IsRationalWithSphericalPolesIn R A` agreeing with `P.eval z / Q.eval z` whenever `(z : S²) ∉ A`. -/
theorem admissiblePolyPair_to_rational {A : Set RiemannSphere} {P Q : Polynomial ℂ}
    (hadm : AdmissiblePolyPair A P Q) :
    ∃ R : ℂ → ℂ, IsRationalWithSphericalPolesIn R A ∧
      (∀ z : ℂ, (z : RiemannSphere) ∉ A →
        Q.eval z ≠ 0 ∧ R z = P.eval z / Q.eval z) := by
  obtain ⟨P₁, Q₁, _, _, _, hQ₁_monic, hcop₁, hdiv₁, hmul, _, _, _, _, _, _⟩ := theorem13_2 P Q hadm.1
  let R : ℂ → ℂ := fun z => P₁.eval z / Q₁.eval z
  have hroots₁ : ∀ a : ℂ, Q₁.eval a = 0 → (a : RiemannSphere) ∈ A := by
    intro a ha
    rcases hdiv₁ with ⟨D, hD_eq⟩
    apply hadm.2.1 a
    rw [hD_eq]
    simp [Polynomial.eval_mul, ha]
  have hdeg₁ : Q₁.natDegree < P₁.natDegree → (∞ : RiemannSphere) ∈ A := by
    intro hlt
    by_contra hnot_inf
    have hle : P.natDegree ≤ Q.natDegree := hadm.2.2 hnot_inf
    by_cases hP : P = 0
    · subst hP
      rw [zero_mul] at hmul
      rcases mul_eq_zero.mp hmul.symm with hP₁ | hQ
      · subst hP₁
        simp at hlt
      · exact hadm.1 hQ
    · have hP₁ : P₁ ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hmul
        exact mul_ne_zero hP hQ₁_monic.ne_zero hmul
      have hdeg_eq : P.natDegree + Q₁.natDegree = P₁.natDegree + Q.natDegree := by
        rw [← Polynomial.natDegree_mul hP hQ₁_monic.ne_zero, hmul,
          Polynomial.natDegree_mul hP₁ hadm.1]
      omega
  refine ⟨R, ⟨P₁, Q₁, hQ₁_monic, hcop₁, hroots₁, hdeg₁, fun _ => rfl⟩, ?_⟩
  intro z hz
  have hQz : Q.eval z ≠ 0 := fun h0 => hz (hadm.2.1 z h0)
  have hQ₁z : Q₁.eval z ≠ 0 := fun h0 => hz (hroots₁ z h0)
  refine ⟨hQz, ?_⟩
  dsimp only [R]
  rw [div_eq_div_iff hQ₁z hQz]
  have heval := congrArg (Polynomial.eval z) hmul
  simp only [Polynomial.eval_mul] at heval
  linear_combination -heval

/-- Elementary Lipschitz bound on `k`-th powers: `‖x ^ k - y ^ k‖ ≤ k * B ^ (k - 1) * ‖x - y‖`
whenever `‖x‖ ≤ B` and `‖y‖ ≤ B`. -/
theorem norm_pow_sub_pow_le {x y : ℂ} {B : ℝ} (hB : 0 ≤ B) (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) :
    ∀ k : ℕ, ‖x ^ k - y ^ k‖ ≤ (k : ℝ) * B ^ (k - 1) * ‖x - y‖
  | 0 => by simp
  | 1 => by simp
  | k + 2 => by
    have hsplit : x ^ (k + 2) - y ^ (k + 2) = (x - y) * x ^ (k + 1) + y * (x ^ (k + 1) - y ^ (k + 1)) := by
      ring
    rw [hsplit]
    have hx_pow : ‖x ^ (k + 1)‖ ≤ B ^ (k + 1) := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg x) hx (k + 1)
    have ih := norm_pow_sub_pow_le hB hx hy (k + 1)
    simp only [Nat.add_sub_cancel] at ih ⊢
    calc
      ‖(x - y) * x ^ (k + 1) + y * (x ^ (k + 1) - y ^ (k + 1))‖
          ≤ ‖(x - y) * x ^ (k + 1)‖ + ‖y * (x ^ (k + 1) - y ^ (k + 1))‖ := norm_add_le _ _
      _ = ‖x - y‖ * ‖x ^ (k + 1)‖ + ‖y‖ * ‖x ^ (k + 1) - y ^ (k + 1)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖x - y‖ * B ^ (k + 1) + B * (((k + 1 : ℕ) : ℝ) * B ^ k * ‖x - y‖) := by
          refine add_le_add (mul_le_mul_of_nonneg_left hx_pow (norm_nonneg _)) ?_
          exact mul_le_mul hy ih (norm_nonneg _) hB
      _ = ((k + 2 : ℕ) : ℝ) * B ^ (k + 1) * ‖x - y‖ := by
          push_cast
          ring

/-- Single pole-shift step: if every `(z - w₂)⁻¹ ^ j` (`j ≥ 1`) can be uniformly approximated on
`K` by `AdmissiblePolyPair A` quotients, `∀ z ∈ K, δ₂ ≤ ‖z - w₂‖` (`δ₂ > 0`), and
`‖w₁ - w₂‖ < δ₂ / 2`, then every `(z - w₁)⁻¹ ^ k` (`k ≥ 1`) can also be uniformly approximated on
`K` by `AdmissiblePolyPair A` quotients. -/
theorem pole_shift_step {K : Set ℂ} {A : Set RiemannSphere} {w₁ w₂ : ℂ} {δ₂ : ℝ}
    (hKA : A ⊆ sphericalCompl K)
    (hδ₂_pos : 0 < δ₂) (hδ₂_le : ∀ z ∈ K, δ₂ ≤ ‖z - w₂‖)
    (hw₁₂ : ‖w₁ - w₂‖ < δ₂ / 2)
    (hw₂_good : ∀ j : ℕ, 1 ≤ j → ∀ ε > 0,
      ∃ P Q : Polynomial ℂ, AdmissiblePolyPair A P Q ∧
        ∀ z ∈ K, ‖(z - w₂)⁻¹ ^ j - P.eval z / Q.eval z‖ < ε) :
    ∀ k : ℕ, 1 ≤ k → ∀ ε > 0,
      ∃ P Q : Polynomial ℂ, AdmissiblePolyPair A P Q ∧
        ∀ z ∈ K, ‖(z - w₁)⁻¹ ^ k - P.eval z / Q.eval z‖ < ε := by
  intro k hk ε hε
  have hz_not_A : ∀ z ∈ K, (z : RiemannSphere) ∉ A := by
    intro z hzK hzA
    exact hKA hzA ⟨z, hzK, rfl⟩
  have hδ₁_le : ∀ z ∈ K, δ₂ / 2 ≤ ‖z - w₁‖ := by
    intro z hzK
    have htri : ‖z - w₂‖ ≤ ‖z - w₁‖ + ‖w₁ - w₂‖ := by
      have heq : z - w₂ = (z - w₁) + (w₁ - w₂) := by ring
      rw [heq]
      exact norm_add_le _ _
    linarith [hδ₂_le z hzK]
  let B : ℝ := 2 / δ₂ + 1
  have hB_pos : 0 < B := by positivity
  let L_lip : ℝ := (k : ℝ) * B ^ (k - 1) + 1
  have hL_pos : 0 < L_lip := by positivity
  let η : ℝ := min 1 (ε / (3 * L_lip))
  have hη_pos : 0 < η := lt_min zero_lt_one (by positivity)
  have htend : Tendsto (fun N : ℕ => (2 / δ₂) * (1 / 2 : ℝ) ^ N) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend η hη_pos
  have hN_lt : (2 / δ₂) * (1 / 2 : ℝ) ^ N < η := by
    have hdist := hN N (le_refl N)
    rwa [Real.dist_0_eq_abs, abs_of_nonneg (by positivity)] at hdist
  let Φ : Polynomial ℂ :=
    ∑ m ∈ Finset.range N, Polynomial.C ((w₁ - w₂) ^ m) * Polynomial.X ^ (m + 1)
  have hΦ0 : Φ.eval 0 = 0 := by
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_eq_zero
    intro m _
    simp [zero_pow (Nat.succ_ne_zero _)]
  have hΦ_approx : ∀ z ∈ K, ‖(z - w₁)⁻¹ - Φ.eval ((z - w₂)⁻¹)‖ < η := by
    intro z hzK
    have hzw₂_pos : 0 < ‖z - w₂‖ := lt_of_lt_of_le hδ₂_pos (hδ₂_le z hzK)
    have hzw₁_pos : 0 < ‖z - w₁‖ := lt_of_lt_of_le (by positivity) (hδ₁_le z hzK)
    have hzw₂_ne : z - w₂ ≠ 0 := norm_ne_zero_iff.mp hzw₂_pos.ne'
    have hzw₁_ne : z - w₁ ≠ 0 := norm_ne_zero_iff.mp hzw₁_pos.ne'
    let q : ℂ := (w₁ - w₂) * (z - w₂)⁻¹
    have hΦ_eval : Φ.eval ((z - w₂)⁻¹) = (z - w₂)⁻¹ * ∑ m ∈ Finset.range N, q ^ m := by
      simp only [Φ, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      simp only [q, mul_pow, pow_succ]
      ring
    have h1mq : 1 - q = (z - w₁) * (z - w₂)⁻¹ := by
      dsimp only [q]
      have : (1 : ℂ) = (z - w₂) * (z - w₂)⁻¹ := (mul_inv_cancel₀ hzw₂_ne).symm
      calc
        1 - (w₁ - w₂) * (z - w₂)⁻¹
            = (z - w₂) * (z - w₂)⁻¹ - (w₁ - w₂) * (z - w₂)⁻¹ := by rw [← this]
        _ = ((z - w₂) - (w₁ - w₂)) * (z - w₂)⁻¹ := by ring
        _ = (z - w₁) * (z - w₂)⁻¹ := by ring
    have hgeom : (z - w₁)⁻¹ - Φ.eval ((z - w₂)⁻¹) = (z - w₁)⁻¹ * q ^ N := by
      rw [hΦ_eval]
      have hg := geom_sum_mul_neg q N
      rw [h1mq] at hg
      have hg' : (z - w₁)⁻¹ * ((∑ m ∈ Finset.range N, q ^ m) * ((z - w₁) * (z - w₂)⁻¹)) =
          (z - w₁)⁻¹ * (1 - q ^ N) := congrArg ((z - w₁)⁻¹ * ·) hg
      have hlhs : (z - w₁)⁻¹ * ((∑ m ∈ Finset.range N, q ^ m) * ((z - w₁) * (z - w₂)⁻¹)) =
          (z - w₂)⁻¹ * ∑ m ∈ Finset.range N, q ^ m := by
        calc
          (z - w₁)⁻¹ * ((∑ m ∈ Finset.range N, q ^ m) * ((z - w₁) * (z - w₂)⁻¹))
              = ((z - w₁)⁻¹ * (z - w₁)) * ((z - w₂)⁻¹ * ∑ m ∈ Finset.range N, q ^ m) := by ring
          _ = (z - w₂)⁻¹ * ∑ m ∈ Finset.range N, q ^ m := by
              rw [inv_mul_cancel₀ hzw₁_ne, one_mul]
      rw [hlhs, mul_sub, mul_one] at hg'
      linear_combination hg'.symm
    rw [hgeom, norm_mul, norm_inv, norm_pow]
    have hq_le : ‖q‖ ≤ 1 / 2 := by
      dsimp only [q]
      rw [norm_mul, norm_inv]
      calc
        ‖w₁ - w₂‖ * ‖z - w₂‖⁻¹ ≤ (δ₂ / 2) * δ₂⁻¹ := by
          refine mul_le_mul hw₁₂.le (inv_anti₀ hδ₂_pos (hδ₂_le z hzK))
            (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
        _ = 1 / 2 := by field_simp [hδ₂_pos.ne']
    have hinv_le : ‖z - w₁‖⁻¹ ≤ 2 / δ₂ := by
      have h1 := inv_anti₀ (by positivity : 0 < δ₂ / 2) (hδ₁_le z hzK)
      have h2 : (δ₂ / 2)⁻¹ = 2 / δ₂ := by field_simp [hδ₂_pos.ne']
      rwa [h2] at h1
    calc
      ‖z - w₁‖⁻¹ * ‖q‖ ^ N ≤ (2 / δ₂) * (1 / 2 : ℝ) ^ N := by
        refine mul_le_mul hinv_le (pow_le_pow_left₀ (norm_nonneg q) hq_le N)
          (pow_nonneg (norm_nonneg q) N) (by positivity)
      _ < η := hN_lt
  let Ψ : Polynomial ℂ := Φ ^ k
  have hΨ_coeff0 : Ψ.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, hΦ0, zero_pow (by omega)]
  have hΨ_approx : ∀ z ∈ K, ‖(z - w₁)⁻¹ ^ k - Ψ.eval ((z - w₂)⁻¹)‖ < ε / 2 := by
    intro z hzK
    rw [Polynomial.eval_pow]
    have hzw₁_pos : 0 < ‖z - w₁‖ := lt_of_lt_of_le (by positivity) (hδ₁_le z hzK)
    have hx_le : ‖(z - w₁)⁻¹‖ ≤ B := by
      rw [norm_inv]
      have h1 := inv_anti₀ (by positivity : 0 < δ₂ / 2) (hδ₁_le z hzK)
      have h2 : (δ₂ / 2)⁻¹ = 2 / δ₂ := by field_simp [hδ₂_pos.ne']
      rw [h2] at h1
      dsimp only [B]
      linarith
    have hy_le : ‖Φ.eval ((z - w₂)⁻¹)‖ ≤ B := by
      have hdiff := hΦ_approx z hzK
      have htri : ‖Φ.eval ((z - w₂)⁻¹)‖ ≤ ‖(z - w₁)⁻¹‖ + ‖(z - w₁)⁻¹ - Φ.eval ((z - w₂)⁻¹)‖ := by
        calc
          ‖Φ.eval ((z - w₂)⁻¹)‖
              = ‖(z - w₁)⁻¹ - ((z - w₁)⁻¹ - Φ.eval ((z - w₂)⁻¹))‖ := by congr 1; ring
          _ ≤ ‖(z - w₁)⁻¹‖ + ‖(z - w₁)⁻¹ - Φ.eval ((z - w₂)⁻¹)‖ := norm_sub_le _ _
      have hinv_le : ‖(z - w₁)⁻¹‖ ≤ 2 / δ₂ := by
        rw [norm_inv]
        have h1 := inv_anti₀ (by positivity : 0 < δ₂ / 2) (hδ₁_le z hzK)
        have h2 : (δ₂ / 2)⁻¹ = 2 / δ₂ := by field_simp [hδ₂_pos.ne']
        rwa [h2] at h1
      have hη_le1 : η ≤ 1 := min_le_left _ _
      dsimp only [B]
      linarith
    have hpow := norm_pow_sub_pow_le hB_pos.le hx_le hy_le k
    have hη_le2 : η ≤ ε / (3 * L_lip) := min_le_right _ _
    have hkB_lt : (k : ℝ) * B ^ (k - 1) < L_lip := by dsimp only [L_lip]; linarith
    calc
      ‖(z - w₁)⁻¹ ^ k - Φ.eval ((z - w₂)⁻¹) ^ k‖
          ≤ (k : ℝ) * B ^ (k - 1) * ‖(z - w₁)⁻¹ - Φ.eval ((z - w₂)⁻¹)‖ := hpow
      _ ≤ L_lip * η := by
          refine mul_le_mul hkB_lt.le (hΦ_approx z hzK).le (norm_nonneg _) hL_pos.le
      _ ≤ L_lip * (ε / (3 * L_lip)) := mul_le_mul_of_nonneg_left hη_le2 hL_pos.le
      _ = ε / 3 := by field_simp [hL_pos.ne']
      _ < ε / 2 := by linarith
  -- Approximate `Ψ.eval ((z - w₂)⁻¹) = ∑ j ∈ range D, Ψ.coeff (j + 1) * (z - w₂)⁻¹ ^ (j + 1)`
  let D := Ψ.natDegree
  have hΨ_sum : ∀ u : ℂ, Ψ.eval u = ∑ j ∈ Finset.range D, Ψ.coeff (j + 1) * u ^ (j + 1) := by
    intro u
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ', hΨ_coeff0, zero_mul, add_zero]
  have hterm_approx : ∀ j : ℕ, ∃ P Q : Polynomial ℂ, AdmissiblePolyPair A P Q ∧
      ∀ z ∈ K,
        ‖Ψ.coeff (j + 1) * (z - w₂)⁻¹ ^ (j + 1) - P.eval z / Q.eval z‖ <
          ε / (2 * ((D : ℝ) + 1)) := by
    intro j
    let cj := Ψ.coeff (j + 1)
    let tol : ℝ := ε / (2 * ((D : ℝ) + 1) * (‖cj‖ + 1))
    have htol : 0 < tol := by positivity
    obtain ⟨Pj, Qj, hadm_j, hj_est⟩ := hw₂_good (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) tol htol
    refine ⟨Polynomial.C cj * Pj, Qj, admissiblePolyPair_smul cj hadm_j, ?_⟩
    intro z hzK
    change ‖cj * (z - w₂)⁻¹ ^ (j + 1) - (Polynomial.C cj * Pj).eval z / Qj.eval z‖ < _
    rw [Polynomial.eval_mul, Polynomial.eval_C, mul_div_assoc, ← mul_sub, norm_mul]
    calc
      ‖cj‖ * ‖(z - w₂)⁻¹ ^ (j + 1) - Pj.eval z / Qj.eval z‖
          ≤ (‖cj‖ + 1) * ‖(z - w₂)⁻¹ ^ (j + 1) - Pj.eval z / Qj.eval z‖ :=
            mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (‖cj‖ + 1) * tol := mul_lt_mul_of_pos_left (hj_est z hzK) (by positivity)
      _ = ε / (2 * ((D : ℝ) + 1)) := by
          dsimp only [tol]
          have hne1 : (‖cj‖ + 1 : ℝ) ≠ 0 := by positivity
          have hne2 : ((D : ℝ) + 1) ≠ 0 := by positivity
          field_simp [hne1, hne2]
  let P_j : ℕ → Polynomial ℂ := fun j => Classical.choose (hterm_approx j)
  let Q_j : ℕ → Polynomial ℂ := fun j => Classical.choose (Classical.choose_spec (hterm_approx j))
  have hPQ_spec : ∀ j : ℕ, AdmissiblePolyPair A (P_j j) (Q_j j) ∧
      ∀ z ∈ K,
        ‖Ψ.coeff (j + 1) * (z - w₂)⁻¹ ^ (j + 1) - (P_j j).eval z / (Q_j j).eval z‖ <
          ε / (2 * ((D : ℝ) + 1)) :=
    fun j => Classical.choose_spec (Classical.choose_spec (hterm_approx j))
  obtain ⟨P_tot, Q_tot, hadm_tot, heval_tot⟩ :=
    admissiblePolyPair_finset_sum A (Finset.range D) P_j Q_j (fun j _ => (hPQ_spec j).1)
  refine ⟨P_tot, Q_tot, hadm_tot, ?_⟩
  intro z hzK
  have hsum_err : ‖Ψ.eval ((z - w₂)⁻¹) - P_tot.eval z / Q_tot.eval z‖ < ε / 2 := by
    rw [hΨ_sum ((z - w₂)⁻¹), heval_tot z (hz_not_A z hzK), ← Finset.sum_sub_distrib]
    calc
      ‖∑ j ∈ Finset.range D,
          (Ψ.coeff (j + 1) * (z - w₂)⁻¹ ^ (j + 1) - (P_j j).eval z / (Q_j j).eval z)‖
          ≤ ∑ j ∈ Finset.range D,
              ‖Ψ.coeff (j + 1) * (z - w₂)⁻¹ ^ (j + 1) - (P_j j).eval z / (Q_j j).eval z‖ :=
            norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range D, (ε / (2 * ((D : ℝ) + 1))) :=
            Finset.sum_le_sum fun j _ => ((hPQ_spec j).2 z hzK).le
      _ = (D : ℝ) * (ε / (2 * ((D : ℝ) + 1))) := by
            simp [Finset.card_range, nsmul_eq_mul]
      _ < ((D : ℝ) + 1) * (ε / (2 * ((D : ℝ) + 1))) := by
            apply mul_lt_mul_of_pos_right (by linarith) (by positivity)
      _ = ε / 2 := by
            have hne : ((D : ℝ) + 1) ≠ 0 := by positivity
            field_simp [hne]
  have htri : ‖(z - w₁)⁻¹ ^ k - P_tot.eval z / Q_tot.eval z‖ ≤
      ‖(z - w₁)⁻¹ ^ k - Ψ.eval ((z - w₂)⁻¹)‖ +
        ‖Ψ.eval ((z - w₂)⁻¹) - P_tot.eval z / Q_tot.eval z‖ := by
    have heq : (z - w₁)⁻¹ ^ k - P_tot.eval z / Q_tot.eval z =
        ((z - w₁)⁻¹ ^ k - Ψ.eval ((z - w₂)⁻¹)) +
          (Ψ.eval ((z - w₂)⁻¹) - P_tot.eval z / Q_tot.eval z) := by ring
    rw [heq]
    exact norm_add_le _ _
  linarith [hΨ_approx z hzK]

/-- Positive distance from a point `w ∉ K` to a compact nonempty set `K ⊆ ℂ`. -/
theorem exists_pos_norm_sub_le {K : Set ℂ} (hK : IsCompact K) (hK_ne : K.Nonempty)
    {w : ℂ} (hw : w ∉ K) :
    ∃ δ > 0, ∀ z ∈ K, δ ≤ ‖z - w‖ := by
  obtain ⟨z₀, hz₀K, hz₀_min⟩ :=
    hK.exists_isMinOn hK_ne ((continuous_id.sub continuous_const).norm.continuousOn)
  have hne : z₀ - w ≠ 0 := sub_ne_zero.mpr (fun heq => hw (heq ▸ hz₀K))
  exact ⟨‖z₀ - w‖, norm_pos_iff.mpr hne, fun z hz => hz₀_min hz⟩

/-- Pole-pushing lemma for Runge's theorem: if `K ⊆ ℂ` is compact and nonempty, `A ⊆ S² \ K`
meets the connected component of `(w₀ : S²)` in `S² \ K` (`w₀ ∉ K`), then `(z - w₀)⁻¹` can be
uniformly approximated on `K` by `AdmissiblePolyPair A` quotients. -/
theorem runge_pole_push {K : Set ℂ} (hK : IsCompact K) (hK_ne : K.Nonempty)
    {A : Set RiemannSphere} (hKA : A ⊆ sphericalCompl K)
    {w₀ : ℂ} (hw₀ : w₀ ∉ K)
    (hA_meet : (A ∩ connectedComponentIn (sphericalCompl K) (w₀ : RiemannSphere)).Nonempty) :
    ∀ ε > 0, ∃ P Q : Polynomial ℂ, AdmissiblePolyPair A P Q ∧
      ∀ z ∈ K, ‖(z - w₀)⁻¹ - P.eval z / Q.eval z‖ < ε := by
  have hw₀_sph : (w₀ : RiemannSphere) ∈ sphericalCompl K := by
    rintro ⟨z, hzK, hzeq⟩
    exact hw₀ (OnePoint.coe_injective hzeq ▸ hzK)
  let V : Set RiemannSphere := connectedComponentIn (sphericalCompl K) (w₀ : RiemannSphere)
  have hV_open : IsOpen V :=
    isOpen_connectedComponentIn_spherical (isOpen_sphericalCompl_of_isCompact hK) _
  have hV_conn : IsConnected V := isConnected_connectedComponentIn_of_mem hw₀_sph
  let V₀ : Set ℂ := ((↑) : ℂ → RiemannSphere) ⁻¹' V
  have hV₀_open : IsOpen V₀ := hV_open.preimage OnePoint.continuous_coe
  have hw₀_V₀ : w₀ ∈ V₀ := mem_connectedComponentIn hw₀_sph
  have hV₀_conn : IsConnected V₀ := isConnected_preimage_coe_of_isOpen hV_open hV_conn ⟨w₀, hw₀_V₀⟩
  have hV₀_not_K : ∀ w ∈ V₀, w ∉ K := by
    intro w hw hwK
    have hmem : (w : RiemannSphere) ∈ sphericalCompl K :=
      connectedComponentIn_subset _ _ hw
    exact hmem ⟨w, hwK, rfl⟩
  let G : Set ℂ := {w ∈ V₀ | ∀ k : ℕ, 1 ≤ k → ∀ ε > 0,
    ∃ P Q : Polynomial ℂ, AdmissiblePolyPair A P Q ∧
      ∀ z ∈ K, ‖(z - w)⁻¹ ^ k - P.eval z / Q.eval z‖ < ε}
  -- `G` is open in `ℂ`
  have hG_open : IsOpen G := by
    rw [Metric.isOpen_iff]
    rintro w₂ ⟨hw₂_V₀, hw₂_good⟩
    obtain ⟨r, hr, hball_V₀⟩ := Metric.isOpen_iff.mp hV₀_open w₂ hw₂_V₀
    obtain ⟨δ₂, hδ₂_pos, hδ₂_le⟩ := exists_pos_norm_sub_le hK hK_ne (hV₀_not_K w₂ hw₂_V₀)
    refine ⟨min r (δ₂ / 2), lt_min hr (by positivity), ?_⟩
    intro w₁ hw₁_ball
    have hw₁_r : w₁ ∈ ball w₂ r := Metric.ball_subset_ball (min_le_left _ _) hw₁_ball
    have hw₁_δ : ‖w₁ - w₂‖ < δ₂ / 2 := by
      have hd : dist w₁ w₂ < δ₂ / 2 := lt_of_lt_of_le hw₁_ball (min_le_right _ _)
      rwa [dist_eq_norm] at hd
    exact ⟨hball_V₀ hw₁_r, pole_shift_step hKA hδ₂_pos hδ₂_le hw₁_δ hw₂_good⟩
  -- `V₀ \ G` is open in `ℂ`
  have hVG_open : IsOpen (V₀ \ G) := by
    rw [Metric.isOpen_iff]
    rintro w₁ ⟨hw₁_V₀, hw₁_bad⟩
    obtain ⟨r, hr, hball_V₀⟩ := Metric.isOpen_iff.mp hV₀_open w₁ hw₁_V₀
    obtain ⟨δ₁, hδ₁_pos, hδ₁_le⟩ := exists_pos_norm_sub_le hK hK_ne (hV₀_not_K w₁ hw₁_V₀)
    refine ⟨min r (δ₁ / 3), lt_min hr (by positivity), ?_⟩
    intro w₂ hw₂_ball
    have hw₂_r : w₂ ∈ ball w₁ r := Metric.ball_subset_ball (min_le_left _ _) hw₂_ball
    refine ⟨hball_V₀ hw₂_r, ?_⟩
    rintro ⟨_, hw₂_good⟩
    have hw₁₂ : ‖w₁ - w₂‖ < δ₁ / 3 := by
      have hd : dist w₂ w₁ < δ₁ / 3 := lt_of_lt_of_le hw₂_ball (min_le_right _ _)
      rwa [dist_comm, dist_eq_norm] at hd
    have hδ₂_le : ∀ z ∈ K, (2 / 3) * δ₁ ≤ ‖z - w₂‖ := by
      intro z hzK
      have htri : ‖z - w₁‖ ≤ ‖z - w₂‖ + ‖w₁ - w₂‖ := by
        calc
          ‖z - w₁‖ = ‖(z - w₂) - (w₁ - w₂)‖ := by congr 1; ring
          _ ≤ ‖z - w₂‖ + ‖w₁ - w₂‖ := norm_sub_le _ _
      linarith [hδ₁_le z hzK]
    have hw₁₂' : ‖w₁ - w₂‖ < ((2 / 3) * δ₁) / 2 := by linarith
    exact hw₁_bad ⟨hw₁_V₀, pole_shift_step hKA (by positivity) hδ₂_le hw₁₂' hw₂_good⟩
  -- `G` is nonempty because `A` meets `V`
  have hG_ne : G.Nonempty := by
    obtain ⟨p, hpA, hpV⟩ := hA_meet
    induction p using OnePoint.rec with
    | coe a =>
      refine ⟨a, hpV, ?_⟩
      intro k _ ε hε
      refine ⟨1, (Polynomial.X - Polynomial.C a) ^ k, admissiblePolyPair_inv_pow hpA k, ?_⟩
      intro z _
      simp only [Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, one_div, inv_pow, sub_self, norm_zero]
      exact hε
    | infty =>
      obtain ⟨r, hr, hinf_sub⟩ := ((isOpen_riemannSphere_iff V).mp hV_open).2 hpV
      obtain ⟨M, hM_pos, hM⟩ := hK.isBounded.exists_pos_norm_le
      let R_rad : ℝ := max r (2 * M) + 2
      have hR_pos : 0 < R_rad := by linarith [le_max_left r (2 * M)]
      let w₂ : ℂ := (R_rad : ℂ)
      have hw₂_norm : ‖w₂‖ = R_rad := by
        simp [w₂, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR_pos]
      have hw₂_V₀ : w₂ ∈ V₀ := by
        apply hinf_sub
        rw [coe_mem_infinityDisc, hw₂_norm]
        linarith [le_max_left r (2 * M)]
      have hw₂_ne : w₂ ≠ 0 := norm_ne_zero_iff.mp (hw₂_norm ▸ hR_pos.ne')
      refine ⟨w₂, hw₂_V₀, ?_⟩
      intro k _ ε hε
      let B : ℝ := 2
      let L_lip : ℝ := (k : ℝ) * B ^ (k - 1) + 1
      have hL_pos : 0 < L_lip := by positivity
      let η : ℝ := min 1 (ε / L_lip)
      have hη_pos : 0 < η := lt_min zero_lt_one (by positivity)
      have htend : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend η hη_pos
      have hN_lt : (1 / 2 : ℝ) ^ N < η := by
        have hd := hN N (le_refl N)
        rwa [Real.dist_0_eq_abs, abs_of_nonneg (by positivity)] at hd
      let P_N : Polynomial ℂ :=
        ∑ m ∈ Finset.range N, Polynomial.C (- (w₂⁻¹ ^ (m + 1))) * Polynomial.X ^ m
      refine ⟨P_N ^ k, 1, admissiblePolyPair_poly_of_infty_mem hpA (P_N ^ k), ?_⟩
      intro z hzK
      rw [Polynomial.eval_one, div_one, Polynomial.eval_pow]
      have hz_le : ‖z‖ ≤ M := hM z hzK
      have hM_nonneg : 0 ≤ M := hM_pos.le
      have hzw₂_ge1 : 1 ≤ ‖z - w₂‖ := by
        have htri : ‖w₂‖ ≤ ‖z - w₂‖ + ‖z‖ := by
          calc
            ‖w₂‖ = ‖z - (z - w₂)‖ := by congr 1; ring
            _ ≤ ‖z‖ + ‖z - w₂‖ := norm_sub_le _ _
            _ = ‖z - w₂‖ + ‖z‖ := add_comm _ _
        have h2M : 2 * M + 2 ≤ R_rad := by
          dsimp only [R_rad]
          linarith [le_max_right r (2 * M)]
        linarith [hw₂_norm]
      have hzw₂_ne : z - w₂ ≠ 0 := norm_ne_zero_iff.mp (by linarith : ‖z - w₂‖ ≠ 0)
      let q : ℂ := z * w₂⁻¹
      have hPN_eval : P_N.eval z = - w₂⁻¹ * ∑ m ∈ Finset.range N, q ^ m := by
        simp only [P_N, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        simp only [q, mul_pow, pow_succ]
        ring
      have h1mq : 1 - q = - (z - w₂) * w₂⁻¹ := by
        dsimp only [q]
        have : (1 : ℂ) = w₂ * w₂⁻¹ := (mul_inv_cancel₀ hw₂_ne).symm
        calc
          1 - z * w₂⁻¹ = w₂ * w₂⁻¹ - z * w₂⁻¹ := by rw [← this]
          _ = - (z - w₂) * w₂⁻¹ := by ring
      have hgeom : (z - w₂)⁻¹ - P_N.eval z = (z - w₂)⁻¹ * q ^ N := by
        rw [hPN_eval]
        have hg := geom_sum_mul_neg q N
        rw [h1mq] at hg
        have hg' : (z - w₂)⁻¹ * ((∑ m ∈ Finset.range N, q ^ m) * (- (z - w₂) * w₂⁻¹)) =
            (z - w₂)⁻¹ * (1 - q ^ N) := congrArg ((z - w₂)⁻¹ * ·) hg
        have hlhs : (z - w₂)⁻¹ * ((∑ m ∈ Finset.range N, q ^ m) * (- (z - w₂) * w₂⁻¹)) =
            - w₂⁻¹ * ∑ m ∈ Finset.range N, q ^ m := by
          calc
            (z - w₂)⁻¹ * ((∑ m ∈ Finset.range N, q ^ m) * (- (z - w₂) * w₂⁻¹))
                = ((z - w₂)⁻¹ * (z - w₂)) * (- w₂⁻¹ * ∑ m ∈ Finset.range N, q ^ m) := by ring
            _ = - w₂⁻¹ * ∑ m ∈ Finset.range N, q ^ m := by
                rw [inv_mul_cancel₀ hzw₂_ne, one_mul]
        rw [hlhs, mul_sub, mul_one] at hg'
        linear_combination hg'.symm
      have hq_le : ‖q‖ ≤ 1 / 2 := by
        dsimp only [q]
        rw [norm_mul, norm_inv, hw₂_norm]
        have h2M : 2 * M + 2 ≤ R_rad := by
          dsimp only [R_rad]
          linarith [le_max_right r (2 * M)]
        have hinv_le : R_rad⁻¹ ≤ (2 * M + 2)⁻¹ :=
          inv_anti₀ (by positivity) h2M
        calc
          ‖z‖ * R_rad⁻¹ ≤ M * (2 * M + 2)⁻¹ :=
            mul_le_mul hz_le hinv_le (inv_nonneg.mpr hR_pos.le) hM_nonneg
          _ ≤ 1 / 2 := by
            rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
            linarith
      have herr1 : ‖(z - w₂)⁻¹ - P_N.eval z‖ < η := by
        rw [hgeom, norm_mul, norm_inv, norm_pow]
        have hinv1 : ‖z - w₂‖⁻¹ ≤ 1 := by
          simpa using inv_anti₀ zero_lt_one hzw₂_ge1
        calc
          ‖z - w₂‖⁻¹ * ‖q‖ ^ N ≤ 1 * (1 / 2 : ℝ) ^ N :=
            mul_le_mul hinv1 (pow_le_pow_left₀ (norm_nonneg q) hq_le N)
              (pow_nonneg (norm_nonneg q) N) zero_le_one
          _ = (1 / 2 : ℝ) ^ N := one_mul _
          _ < η := hN_lt
      have hx_le : ‖(z - w₂)⁻¹‖ ≤ B := by
        rw [norm_inv]
        have hinv1 : ‖z - w₂‖⁻¹ ≤ 1 := by simpa using inv_anti₀ zero_lt_one hzw₂_ge1
        dsimp only [B]
        linarith
      have hy_le : ‖P_N.eval z‖ ≤ B := by
        have htri : ‖P_N.eval z‖ ≤ ‖(z - w₂)⁻¹‖ + ‖(z - w₂)⁻¹ - P_N.eval z‖ := by
          calc
            ‖P_N.eval z‖ = ‖(z - w₂)⁻¹ - ((z - w₂)⁻¹ - P_N.eval z)‖ := by congr 1; ring
            _ ≤ ‖(z - w₂)⁻¹‖ + ‖(z - w₂)⁻¹ - P_N.eval z‖ := norm_sub_le _ _
        have hinv1 : ‖(z - w₂)⁻¹‖ ≤ 1 := by
          rw [norm_inv]
          simpa using inv_anti₀ zero_lt_one hzw₂_ge1
        have hη1 : η ≤ 1 := min_le_left _ _
        dsimp only [B]
        linarith
      have hpow := norm_pow_sub_pow_le (by positivity : 0 ≤ B) hx_le hy_le k
      have hη2 : η ≤ ε / L_lip := min_le_right _ _
      have hkB_lt : (k : ℝ) * B ^ (k - 1) < L_lip := by dsimp only [L_lip]; linarith
      calc
        ‖(z - w₂)⁻¹ ^ k - P_N.eval z ^ k‖
            ≤ (k : ℝ) * B ^ (k - 1) * ‖(z - w₂)⁻¹ - P_N.eval z‖ := hpow
        _ < L_lip * η := by
            by_cases h0 : ‖(z - w₂)⁻¹ - P_N.eval z‖ = 0
            · rw [h0, mul_zero]
              positivity
            · have hpos : 0 < ‖(z - w₂)⁻¹ - P_N.eval z‖ :=
                lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
              exact mul_lt_mul hkB_lt herr1.le hpos hL_pos.le
        _ ≤ L_lip * (ε / L_lip) := mul_le_mul_of_nonneg_left hη2 hL_pos.le
        _ = ε := mul_div_cancel₀ ε hL_pos.ne'
  -- Connectedness of `V₀` forces `V₀ ⊆ G`
  have hVG_empty : V₀ \ G = ∅ := by
    by_contra hne_VG
    have hne_VG' : (V₀ \ G).Nonempty := Set.nonempty_iff_ne_empty.mpr hne_VG
    have hV₀_sub : V₀ ⊆ G ∪ (V₀ \ G) := fun w hw => by
      by_cases hwG : w ∈ G
      · exact Or.inl hwG
      · exact Or.inr ⟨hw, hwG⟩
    have hne1 : (V₀ ∩ G).Nonempty := by
      obtain ⟨w, hwG⟩ := hG_ne
      exact ⟨w, hwG.1, hwG⟩
    have hne2 : (V₀ ∩ (V₀ \ G)).Nonempty := by
      obtain ⟨w, hwV, hwG⟩ := hne_VG'
      exact ⟨w, hwV, hwV, hwG⟩
    obtain ⟨w, _, hwG, _, hwnG⟩ :=
      hV₀_conn.isPreconnected G (V₀ \ G) hG_open hVG_open hV₀_sub hne1 hne2
    exact hwnG hwG
  have hw₀_G : w₀ ∈ G := by
    by_contra hnot
    exact Set.notMem_empty w₀ (hVG_empty ▸ ⟨hw₀_V₀, hnot⟩)
  intro ε hε
  obtain ⟨P, Q, hadm, hest⟩ := hw₀_G.2 1 (le_refl 1) ε hε
  refine ⟨P, Q, hadm, fun z hzK => ?_⟩
  simpa only [pow_one] using hest z hzK

/-- Uniform Riemann-sum approximation of a segment Cauchy integral on compact `K ⊆ Ω` by a finite
linear combination of simple poles `(z - w_j)⁻¹` with `w_j ∈ Ω \ K`. -/
theorem segment_cauchy_riemann_sum {Ω K : Set ℂ} (hK : IsCompact K) (_hK_ne : K.Nonempty)
    {f : ℂ → ℂ} (hf : RudinRCA.Chapter10.HolomorphicOn f Ω) (a b : ℂ)
    (htr : (RudinRCA.Chapter10.orientedSegment a b).trace ⊆ Ω \ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ terms : List (ℂ × ℂ),
      (∀ p ∈ terms, p.2 ∈ Ω \ K) ∧
      (∀ z ∈ K,
        ‖RudinRCA.Chapter10.pathIntegral (fun ζ => f ζ / (ζ - z))
            (RudinRCA.Chapter10.orientedSegment a b).toBookCurve -
          (terms.map (fun p => p.1 * (z - p.2)⁻¹)).sum‖ < ε) := by
  let φ : ℝ → ℂ := fun t => (1 - t : ℝ) • a + t • b
  have hφ_cont : Continuous φ :=
    ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have hφ_mem : ∀ t ∈ Icc (0 : ℝ) 1, φ t ∈ Ω \ K := by
    intro t ht
    apply htr
    rw [RudinRCA.Chapter10.orientedSegment_trace, segment_eq_image]
    exact ⟨t, ht, rfl⟩
  have hf_cont : ContinuousOn f Ω := fun z hz => (hf z hz).continuousAt.continuousWithinAt
  let g : ℝ × ℂ → ℂ := fun p => (b - a) * (f (φ p.1) / (φ p.1 - p.2))
  have hf_on : ContinuousOn (fun q : ℝ × ℂ => f (φ q.1)) (Icc (0 : ℝ) 1 ×ˢ K) :=
    hf_cont.comp (hφ_cont.comp continuous_fst).continuousOn
      (fun q hq => (hφ_mem q.1 hq.1).1)
  have hg_cont : ContinuousOn g (Icc (0 : ℝ) 1 ×ˢ K) := by
    intro p hp
    have hφ_p : φ p.1 ∈ Ω \ K := hφ_mem p.1 hp.1
    have hne : φ p.1 - p.2 ≠ 0 := sub_ne_zero.mpr (fun heq => hφ_p.2 (heq ▸ hp.2))
    have hsub_at : ContinuousWithinAt (fun q : ℝ × ℂ => φ q.1 - q.2) (Icc (0 : ℝ) 1 ×ˢ K) p :=
      ((hφ_cont.comp continuous_fst).sub continuous_snd).continuousWithinAt
    exact continuousWithinAt_const.mul ((hf_on p hp).div hsub_at hne)
  have hg_ucont : UniformContinuousOn g (Icc (0 : ℝ) 1 ×ˢ K) :=
    (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hg_cont
  obtain ⟨δ, hδ_pos, hδ_uc⟩ := Metric.uniformContinuousOn_iff.mp hg_ucont (ε / 2) (by positivity)
  obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hδ_pos
  let M : ℕ := N₀ + 1
  have hM_pos : 0 < (M : ℝ) := by positivity
  have h1M_lt : 1 / (M : ℝ) < δ := by
    dsimp only [M]
    push_cast
    exact hN₀
  let pt : ℕ → ℝ := fun j => (j : ℝ) / (M : ℝ)
  have hpt0 : pt 0 = 0 := by simp [pt]
  have hptM : pt M = 1 := div_self hM_pos.ne'
  have hpt_mem : ∀ j ≤ M, pt j ∈ Icc (0 : ℝ) 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hM_pos]
    exact_mod_cast hj
  let terms : List (ℂ × ℂ) :=
    (List.range M).map (fun j =>
      (- (((1 / (M : ℝ) : ℝ) : ℂ) * (b - a) * f (φ (pt j))), φ (pt j)))
  refine ⟨terms, ?_, ?_⟩
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    exact hφ_mem (pt j) (hpt_mem j (Nat.le_of_lt (List.mem_range.mp hj)))
  · intro z hzK
    rw [RudinRCA.Chapter10.pathIntegral_orientedSegment]
    have hint_eq : (b - a) * (∫ t in (0 : ℝ)..1, f (φ t) / (φ t - z)) =
        ∫ t in (0 : ℝ)..1, g (t, z) := by
      rw [← intervalIntegral.integral_const_mul]
    rw [hint_eq]
    have hg_z_cont : ContinuousOn (fun t : ℝ => g (t, z)) (Icc (0 : ℝ) 1) :=
      hg_cont.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht => ⟨ht, hzK⟩)
    have hadj : ∑ j ∈ Finset.range M, ∫ t in pt j..pt (j + 1), g (t, z) =
        ∫ t in (0 : ℝ)..1, g (t, z) := by
      rw [← hpt0, ← hptM]
      apply intervalIntegral.sum_integral_adjacent_intervals
      intro j hj
      have hsub_Icc : Set.uIcc (pt j) (pt (j + 1)) ⊆ Icc (0 : ℝ) 1 := by
        have hle : pt j ≤ pt (j + 1) := by
          dsimp only [pt]
          apply div_le_div_of_nonneg_right _ hM_pos.le
          exact_mod_cast Nat.le_succ j
        rw [Set.uIcc_of_le hle]
        exact Icc_subset_Icc (hpt_mem j (Nat.le_of_lt hj)).1 (hpt_mem (j + 1) hj).2
      exact (hg_z_cont.mono hsub_Icc).intervalIntegrable (μ := MeasureTheory.volume)
    rw [← hadj]
    have hlist_range_sum : ∀ (F : ℕ → ℂ) (K_len : ℕ),
        ((List.range K_len).map F).sum = ∑ j ∈ Finset.range K_len, F j := by
      intro F K_len
      induction K_len with
      | zero => simp
      | succ k ih =>
        rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
        simp
    have hterms_sum : (terms.map (fun p => p.1 * (z - p.2)⁻¹)).sum =
        ∑ j ∈ Finset.range M, ∫ _t in pt j..pt (j + 1), g (pt j, z) := by
      dsimp only [terms]
      rw [List.map_map, hlist_range_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [Function.comp_def, g]
      rw [intervalIntegral.integral_const, Complex.real_smul]
      have hlen : pt (j + 1) - pt j = 1 / (M : ℝ) := by
        dsimp only [pt]
        push_cast
        ring
      rw [hlen, show φ (pt j) - z = -(z - φ (pt j)) by ring, div_neg]
      ring
    rw [hterms_sum, ← Finset.sum_sub_distrib]
    calc
      ‖∑ j ∈ Finset.range M,
          ((∫ t in pt j..pt (j + 1), g (t, z)) - ∫ _t in pt j..pt (j + 1), g (pt j, z))‖
          ≤ ∑ j ∈ Finset.range M,
              ‖(∫ t in pt j..pt (j + 1), g (t, z)) - ∫ _t in pt j..pt (j + 1), g (pt j, z)‖ :=
            norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range M, (ε / 2) * (1 / (M : ℝ)) := by
          apply Finset.sum_le_sum
          intro j hj
          have hj_lt : j < M := Finset.mem_range.mp hj
          have hle : pt j ≤ pt (j + 1) := by
            dsimp only [pt]
            apply div_le_div_of_nonneg_right _ hM_pos.le
            exact_mod_cast Nat.le_succ j
          have hsub_Icc : Set.uIcc (pt j) (pt (j + 1)) ⊆ Icc (0 : ℝ) 1 := by
            rw [Set.uIcc_of_le hle]
            exact Icc_subset_Icc (hpt_mem j (Nat.le_of_lt hj_lt)).1 (hpt_mem (j + 1) hj_lt).2
          have hint1 : IntervalIntegrable (fun t => g (t, z)) MeasureTheory.volume (pt j) (pt (j + 1)) :=
            (hg_z_cont.mono hsub_Icc).intervalIntegrable (μ := MeasureTheory.volume)
          have hint2 : IntervalIntegrable (fun _t => g (pt j, z)) MeasureTheory.volume (pt j) (pt (j + 1)) :=
            continuous_const.intervalIntegrable (μ := MeasureTheory.volume) (pt j) (pt (j + 1))
          rw [← intervalIntegral.integral_sub hint1 hint2]
          have hlen : |pt (j + 1) - pt j| = 1 / (M : ℝ) := by
            have hd : pt (j + 1) - pt j = 1 / (M : ℝ) := by dsimp only [pt]; push_cast; ring
            rw [hd, abs_of_pos (by positivity)]
          rw [← hlen]
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro t ht
          rw [Set.uIoc_of_le hle] at ht
          have ht_Icc : t ∈ Icc (0 : ℝ) 1 :=
            ⟨(hpt_mem j (Nat.le_of_lt hj_lt)).1.trans ht.1.le,
              ht.2.trans (hpt_mem (j + 1) hj_lt).2⟩
          have hptj_Icc : pt j ∈ Icc (0 : ℝ) 1 := hpt_mem j (Nat.le_of_lt hj_lt)
          have hdist_lt : dist (t, z) (pt j, z) < δ := by
            rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq,
              abs_of_pos (sub_pos.mpr ht.1)]
            have hd : pt (j + 1) - pt j = 1 / (M : ℝ) := by dsimp only [pt]; push_cast; ring
            linarith [ht.2]
          have huc := hδ_uc (t, z) ⟨ht_Icc, hzK⟩ (pt j, z) ⟨hptj_Icc, hzK⟩ hdist_lt
          rw [dist_eq_norm] at huc
          exact huc.le
      _ = (M : ℝ) * ((ε / 2) * (1 / (M : ℝ))) := by
          simp [Finset.card_range, nsmul_eq_mul]
      _ = ε / 2 := by field_simp [hM_pos.ne']
      _ < ε := by linarith

/-- **Theorem 13.6 (Compact Runge approximation and countability of complement components,
RCA pp. 270–271):**
Let `K ⊆ ℂ` be compact.
1. `S² \ K` has at most countably many connected components.
2. Given `A ⊆ S² \ K` meeting every connected component of `S² \ K` (`∞ ∈ A` is admissible),
   an open set `Ω ⊇ K`, `f ∈ H(Ω)`, and `ε > 0`, there exists a rational function `R` whose
   spherical poles all lie in `A` (`IsRationalWithSphericalPolesIn R A`) such that
   `∀ z ∈ K, ‖f z - R z‖ < ε`. -/
theorem theorem13_6 {K : Set ℂ} (hK : IsCompact K) :
    {C : Set RiemannSphere |
      ∃ x ∈ sphericalCompl K, C = connectedComponentIn (sphericalCompl K) x}.Countable ∧
    (∀ {A : Set RiemannSphere}, A ⊆ sphericalCompl K →
      (∀ x ∈ sphericalCompl K, (A ∩ connectedComponentIn (sphericalCompl K) x).Nonempty) →
      ∀ {Ω : Set ℂ}, IsOpen Ω → K ⊆ Ω →
      ∀ {f : ℂ → ℂ}, RudinRCA.Chapter10.HolomorphicOn f Ω →
      ∀ {ε : ℝ}, 0 < ε →
      ∃ R : ℂ → ℂ, IsRationalWithSphericalPolesIn R A ∧
        ∀ z ∈ K, ‖f z - R z‖ < ε) := by
  refine ⟨countable_components_sphericalCompl hK, ?_⟩
  intro A hKA hA_meet Ω hΩ hKΩ f hf ε hε
  by_cases hK_ne : K.Nonempty
  · obtain ⟨L, _, _, hL_tr, _, _, hcauchy⟩ := theorem13_5 hΩ hK hKΩ
    -- Step 1: approximate `(intervalsChain L).integral` uniformly on `K` by simple-pole sums
    let c_pi : ℂ := (2 * Real.pi * Complex.I)⁻¹
    have hc_pi_pos : 0 < ‖c_pi‖ + 1 := by positivity
    let seg_tol : ℝ := (ε / 2) / ((‖c_pi‖ + 1) * ((L.length : ℝ) + 1))
    have hseg_tol : 0 < seg_tol := by positivity
    have hL_approx : ∀ L' : List (ℂ × ℂ),
        (intervalsChain L').trace ⊆ Ω \ K →
        ∃ terms : List (ℂ × ℂ),
          (∀ p ∈ terms, p.2 ∈ Ω \ K) ∧
          (∀ z ∈ K,
            ‖(intervalsChain L').integral (fun ζ => f ζ / (ζ - z)) -
              (terms.map (fun p => p.1 * (z - p.2)⁻¹)).sum‖ ≤
              (L'.length : ℝ) * seg_tol) := by
      intro L'
      induction L' with
      | nil =>
        intro _
        exact ⟨[], by simp, fun z _ => by simp [intervalsChain]⟩
      | cons e es ih =>
        intro htr_cons
        rw [show intervalsChain (e :: es) =
            RudinRCA.Chapter10.orientedSegment e.1 e.2 :: intervalsChain es from rfl,
          RudinRCA.Chapter10.BookChain.trace_cons] at htr_cons
        obtain ⟨t₁, ht₁_mem, ht₁_est⟩ :=
          segment_cauchy_riemann_sum hK hK_ne hf e.1 e.2 (subset_union_left.trans htr_cons) hseg_tol
        obtain ⟨t₂, ht₂_mem, ht₂_est⟩ := ih (subset_union_right.trans htr_cons)
        refine ⟨t₁ ++ t₂, ?_, ?_⟩
        · intro p hp
          rcases List.mem_append.mp hp with hp₁ | hp₂
          · exact ht₁_mem p hp₁
          · exact ht₂_mem p hp₂
        · intro z hzK
          rw [show intervalsChain (e :: es) =
              RudinRCA.Chapter10.orientedSegment e.1 e.2 :: intervalsChain es from rfl,
            RudinRCA.Chapter10.BookChain.integral_cons, List.map_append, List.sum_append,
            List.length_cons]
          have htri :
              ‖(RudinRCA.Chapter10.pathIntegral (fun ζ => f ζ / (ζ - z))
                  (RudinRCA.Chapter10.orientedSegment e.1 e.2).toBookCurve +
                (intervalsChain es).integral (fun ζ => f ζ / (ζ - z))) -
                ((t₁.map (fun p => p.1 * (z - p.2)⁻¹)).sum +
                  (t₂.map (fun p => p.1 * (z - p.2)⁻¹)).sum)‖ ≤
              ‖RudinRCA.Chapter10.pathIntegral (fun ζ => f ζ / (ζ - z))
                  (RudinRCA.Chapter10.orientedSegment e.1 e.2).toBookCurve -
                (t₁.map (fun p => p.1 * (z - p.2)⁻¹)).sum‖ +
              ‖(intervalsChain es).integral (fun ζ => f ζ / (ζ - z)) -
                (t₂.map (fun p => p.1 * (z - p.2)⁻¹)).sum‖ := by
            have heq :
                (RudinRCA.Chapter10.pathIntegral (fun ζ => f ζ / (ζ - z))
                  (RudinRCA.Chapter10.orientedSegment e.1 e.2).toBookCurve +
                (intervalsChain es).integral (fun ζ => f ζ / (ζ - z))) -
                ((t₁.map (fun p => p.1 * (z - p.2)⁻¹)).sum +
                  (t₂.map (fun p => p.1 * (z - p.2)⁻¹)).sum) =
                (RudinRCA.Chapter10.pathIntegral (fun ζ => f ζ / (ζ - z))
                  (RudinRCA.Chapter10.orientedSegment e.1 e.2).toBookCurve -
                (t₁.map (fun p => p.1 * (z - p.2)⁻¹)).sum) +
                ((intervalsChain es).integral (fun ζ => f ζ / (ζ - z)) -
                (t₂.map (fun p => p.1 * (z - p.2)⁻¹)).sum) := by ring
            rw [heq]
            exact norm_add_le _ _
          have h1 := (ht₁_est z hzK).le
          have h2 := ht₂_est z hzK
          push_cast
          linarith
    obtain ⟨terms, hterms_mem, hterms_est⟩ := hL_approx L hL_tr
    let scaled_terms : List (ℂ × ℂ) := terms.map (fun p => (c_pi * p.1, p.2))
    have hstep1 : ∀ z ∈ K,
        ‖f z - (scaled_terms.map (fun p => p.1 * (z - p.2)⁻¹)).sum‖ < ε / 2 := by
      intro z hzK
      rw [hcauchy hf z hzK]
      have hsc_eq : (scaled_terms.map (fun p => p.1 * (z - p.2)⁻¹)).sum =
          c_pi * (terms.map (fun p => p.1 * (z - p.2)⁻¹)).sum := by
        change ((terms.map (fun p => (c_pi * p.1, p.2))).map (fun p => p.1 * (z - p.2)⁻¹)).sum =
          c_pi * (terms.map (fun p => p.1 * (z - p.2)⁻¹)).sum
        clear scaled_terms hterms_est hterms_mem
        induction terms with
        | nil => simp
        | cons p ps ih =>
          simp only [List.map_cons, List.sum_cons, ih]
          ring
      rw [hsc_eq]
      change ‖c_pi * (intervalsChain L).integral (fun ζ => f ζ / (ζ - z)) -
          c_pi * (terms.map (fun p => p.1 * (z - p.2)⁻¹)).sum‖ < ε / 2
      rw [← mul_sub, norm_mul]
      calc
        ‖c_pi‖ * ‖(intervalsChain L).integral (fun ζ => f ζ / (ζ - z)) -
            (terms.map (fun p => p.1 * (z - p.2)⁻¹)).sum‖
            ≤ (‖c_pi‖ + 1) * ((L.length : ℝ) * seg_tol) := by
              refine mul_le_mul (by linarith) (hterms_est z hzK) (norm_nonneg _) hc_pi_pos.le
        _ < (‖c_pi‖ + 1) * (((L.length : ℝ) + 1) * seg_tol) := by
              apply mul_lt_mul_of_pos_left _ hc_pi_pos
              exact mul_lt_mul_of_pos_right (by linarith) hseg_tol
        _ = ε / 2 := by
              dsimp only [seg_tol]
              have hne1 : (‖c_pi‖ + 1 : ℝ) ≠ 0 := hc_pi_pos.ne'
              have hne2 : ((L.length : ℝ) + 1) ≠ 0 := by positivity
              field_simp [hne1, hne2]
    -- Step 2: push each pole `p.2 ∈ Ω \ K` (`p ∈ scaled_terms`) into `A`
    have hz_not_A : ∀ z ∈ K, (z : RiemannSphere) ∉ A :=
      fun z hzK hzA => hKA hzA ⟨z, hzK, rfl⟩
    have hpush_list : ∀ ts : List (ℂ × ℂ),
        (∀ p ∈ ts, p.2 ∉ K) →
        ∀ η > 0, ∃ P Q : Polynomial ℂ, AdmissiblePolyPair A P Q ∧
          ∀ z ∈ K, ‖(ts.map (fun p => p.1 * (z - p.2)⁻¹)).sum - P.eval z / Q.eval z‖ < η := by
      intro ts
      induction ts with
      | nil =>
        intro _ η hη
        refine ⟨0, 1, admissiblePolyPair_zero A, fun z _ => by simp [hη]⟩
      | cons p ps ih =>
        intro hp_notK η hη
        have hp_K : p.2 ∉ K := hp_notK p List.mem_cons_self
        have hp_sph : (p.2 : RiemannSphere) ∈ sphericalCompl K := by
          rintro ⟨z, hzK, hzeq⟩
          exact hp_K (OnePoint.coe_injective hzeq ▸ hzK)
        let tol₁ : ℝ := (η / 2) / (‖p.1‖ + 1)
        obtain ⟨P₁, Q₁, hadm₁, hest₁⟩ :=
          runge_pole_push hK hK_ne hKA hp_K (hA_meet (p.2 : RiemannSphere) hp_sph) tol₁ (by positivity)
        obtain ⟨P₂, Q₂, hadm₂, hest₂⟩ :=
          ih (fun q hq => hp_notK q (List.mem_cons_of_mem _ hq)) (η / 2) (by positivity)
        let P_head := Polynomial.C p.1 * P₁
        have hadm_head : AdmissiblePolyPair A P_head Q₁ := admissiblePolyPair_smul p.1 hadm₁
        refine ⟨P_head * Q₂ + P₂ * Q₁, Q₁ * Q₂, admissiblePolyPair_add hadm_head hadm₂, ?_⟩
        intro z hzK
        have hQ₁z : Q₁.eval z ≠ 0 := fun h0 => hz_not_A z hzK (hadm₁.2.1 z h0)
        have hQ₂z : Q₂.eval z ≠ 0 := fun h0 => hz_not_A z hzK (hadm₂.2.1 z h0)
        have hdiv : (P_head * Q₂ + P₂ * Q₁).eval z / (Q₁ * Q₂).eval z =
            p.1 * (P₁.eval z / Q₁.eval z) + P₂.eval z / Q₂.eval z := by
          dsimp only [P_head]
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
          field_simp [hQ₁z, hQ₂z]
        rw [List.map_cons, List.sum_cons, hdiv]
        have herr_head : ‖p.1 * (z - p.2)⁻¹ - p.1 * (P₁.eval z / Q₁.eval z)‖ < η / 2 := by
          rw [← mul_sub, norm_mul]
          calc
            ‖p.1‖ * ‖(z - p.2)⁻¹ - P₁.eval z / Q₁.eval z‖
                ≤ (‖p.1‖ + 1) * ‖(z - p.2)⁻¹ - P₁.eval z / Q₁.eval z‖ :=
                  mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
            _ < (‖p.1‖ + 1) * tol₁ := mul_lt_mul_of_pos_left (hest₁ z hzK) (by positivity)
            _ = η / 2 := by
                dsimp only [tol₁]
                have hne : (‖p.1‖ + 1 : ℝ) ≠ 0 := by positivity
                field_simp [hne]
        have htri :
            ‖(p.1 * (z - p.2)⁻¹ + (ps.map (fun q => q.1 * (z - q.2)⁻¹)).sum) -
              (p.1 * (P₁.eval z / Q₁.eval z) + P₂.eval z / Q₂.eval z)‖ ≤
            ‖p.1 * (z - p.2)⁻¹ - p.1 * (P₁.eval z / Q₁.eval z)‖ +
            ‖(ps.map (fun q => q.1 * (z - q.2)⁻¹)).sum - P₂.eval z / Q₂.eval z‖ := by
          have heq :
              (p.1 * (z - p.2)⁻¹ + (ps.map (fun q => q.1 * (z - q.2)⁻¹)).sum) -
                (p.1 * (P₁.eval z / Q₁.eval z) + P₂.eval z / Q₂.eval z) =
              (p.1 * (z - p.2)⁻¹ - p.1 * (P₁.eval z / Q₁.eval z)) +
              ((ps.map (fun q => q.1 * (z - q.2)⁻¹)).sum - P₂.eval z / Q₂.eval z) := by ring
          rw [heq]
          exact norm_add_le _ _
        linarith [hest₂ z hzK]
    have hsc_notK : ∀ p ∈ scaled_terms, p.2 ∉ K := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact (hterms_mem q hq).2
    obtain ⟨P, Q, hadm, hstep2⟩ := hpush_list scaled_terms hsc_notK (ε / 2) (by positivity)
    obtain ⟨R, hR_poles, hR_eq⟩ := admissiblePolyPair_to_rational hadm
    refine ⟨R, hR_poles, ?_⟩
    intro z hzK
    rw [(hR_eq z (hz_not_A z hzK)).2]
    have htri : ‖f z - P.eval z / Q.eval z‖ ≤
        ‖f z - (scaled_terms.map (fun p => p.1 * (z - p.2)⁻¹)).sum‖ +
        ‖(scaled_terms.map (fun p => p.1 * (z - p.2)⁻¹)).sum - P.eval z / Q.eval z‖ := by
      have heq : f z - P.eval z / Q.eval z =
          (f z - (scaled_terms.map (fun p => p.1 * (z - p.2)⁻¹)).sum) +
          ((scaled_terms.map (fun p => p.1 * (z - p.2)⁻¹)).sum - P.eval z / Q.eval z) := by ring
      rw [heq]
      exact norm_add_le _ _
    linarith [hstep1 z hzK, hstep2 z hzK]
  · -- Empty `K` case
    have hK_empty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hK_ne
    subst hK_empty
    obtain ⟨R, hR_poles, _⟩ := admissiblePolyPair_to_rational (admissiblePolyPair_zero A)
    exact ⟨R, hR_poles, by simp⟩


/-! ## 13.7 Polynomial approximation on compact sets with connected spherical complement -/

/-- **Theorem 13.7 (Polynomial Runge corollary, RCA p. 271):**
If `K ⊆ ℂ` is compact (connectedness of `K` is not required), `S² \ K` is connected, `Ω ⊇ K` is
open, and `f ∈ H(Ω)`, then there exists a sequence of complex polynomials `P_n` converging
uniformly to `f` on `K`. -/
theorem theorem13_7 {K Ω : Set ℂ} (hK : IsCompact K)
    (hconn : IsConnected (sphericalCompl K)) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {f : ℂ → ℂ} (hf : RudinRCA.Chapter10.HolomorphicOn f Ω) :
    ∃ P : ℕ → Polynomial ℂ, TendstoUniformlyOn (fun n z => (P n).eval z) f atTop K := by
  let A : Set RiemannSphere := {∞}
  have hKA : A ⊆ sphericalCompl K := by
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    rintro ⟨z, _, hz⟩
    exact OnePoint.coe_ne_infty z hz
  have hA_meet : ∀ x ∈ sphericalCompl K, (A ∩ connectedComponentIn (sphericalCompl K) x).Nonempty := by
    intro x hx
    have hcomp_eq : connectedComponentIn (sphericalCompl K) x = sphericalCompl K :=
      hconn.isPreconnected.connectedComponentIn hx
    rw [hcomp_eq]
    exact ⟨∞, Set.mem_singleton ∞, hKA (Set.mem_singleton ∞)⟩
  have hex : ∀ n : ℕ, ∃ Pn : Polynomial ℂ, ∀ z ∈ K, ‖f z - Pn.eval z‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨R, hR_poles, hR_est⟩ :=
      (theorem13_6 hK).2 hKA hA_meet hΩ hKΩ hf (by positivity : 0 < 1 / ((n : ℝ) + 1))
    obtain ⟨Pn, hPn⟩ := isRationalWithSphericalPolesIn_singleton_infty hR_poles
    refine ⟨Pn, fun z hzK => ?_⟩
    rw [← hPn z]
    exact hR_est z hzK
  choose P hP using hex
  refine ⟨P, Metric.tendstoUniformlyOn_iff.mpr ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  filter_upwards [Filter.eventually_ge_atTop N] with n hn z hzK
  rw [dist_eq_norm]
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hn 1
  exact lt_of_lt_of_le (hP n z hzK) (hle.trans_lt hN).le


/-! ## 13.8 Necessity of connected spherical complement and prescribed poles -/

/-- Maximum-modulus obstruction on a bounded open set `V₀ ⊆ Kᶜ` with `frontier V₀ ⊆ K`:
for any `α ∈ V₀` and `m := sSup ((fun z => ‖z - α‖) '' K)`, we have `K.Nonempty`, `0 < m`, and
no function `R` differentiable on an open superset of `closure V₀` can satisfy
`∀ z ∈ K, ‖(z - α)⁻¹ - R z‖ < 1 / m`. -/
theorem max_modulus_inv_bound {K V₀ : Set ℂ} (hK : IsCompact K)
    (hV₀_open : IsOpen V₀) (hV₀_bdd : Bornology.IsBounded V₀) (hV₀_disj : V₀ ⊆ Kᶜ)
    (hfr_sub : frontier V₀ ⊆ K) {α : ℂ} (hα : α ∈ V₀) :
    K.Nonempty ∧
    0 < sSup ((fun z => ‖z - α‖) '' K) ∧
    (∀ {U : Set ℂ} {R : ℂ → ℂ}, IsOpen U → closure V₀ ⊆ U → DifferentiableOn ℂ R U →
      ∃ z ∈ K, 1 / sSup ((fun z => ‖z - α‖) '' K) ≤ ‖(z - α)⁻¹ - R z‖) := by
  -- `frontier V₀` is nonempty because `V₀` is nonempty, open, and bounded in connected `ℂ`
  have hfr_ne : (frontier V₀).Nonempty := by
    by_contra hfr_empty
    have hfr_eq : frontier V₀ = ∅ := Set.not_nonempty_iff_eq_empty.mp hfr_empty
    have hV₀_closed : IsClosed V₀ := by
      apply isClosed_of_closure_subset
      intro z hz_cl
      by_contra hz_not
      have hz_not_int : z ∉ interior V₀ := fun hz_int => hz_not (interior_subset hz_int)
      have hz_fr : z ∈ frontier V₀ := ⟨hz_cl, hz_not_int⟩
      exact Set.notMem_empty z (hfr_eq ▸ hz_fr)
    have hcl_open : IsClopen V₀ := ⟨hV₀_closed, hV₀_open⟩
    have hV₀_univ : V₀ = Set.univ := by
      rcases isClopen_iff.mp hcl_open with rfl | rfl
      · exact False.elim (Set.notMem_empty α hα)
      · rfl
    rw [hV₀_univ] at hV₀_bdd
    obtain ⟨B, hB_pos, hB⟩ := hV₀_bdd.exists_pos_norm_le
    let x_big : ℝ := B + 1
    have hgt : B < ‖(x_big : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by dsimp [x_big]; positivity)]
      dsimp [x_big]
      linarith
    exact absurd (hB (x_big : ℂ) (Set.mem_univ _)) (not_le.mpr hgt)
  have hK_ne : K.Nonempty := hfr_ne.mono hfr_sub
  let S_norm := (fun z : ℂ => ‖z - α‖) '' K
  have hS_comp : IsCompact S_norm :=
    hK.image ((continuous_id.sub continuous_const).norm)
  let m : ℝ := sSup S_norm
  have ⟨z_fr, hz_fr⟩ := hfr_ne
  have hz_fr_K : z_fr ∈ K := hfr_sub hz_fr
  have hz_fr_ne : z_fr - α ≠ 0 := sub_ne_zero.mpr (fun heq => hV₀_disj hα (heq ▸ hz_fr_K))
  have hm_ge : ∀ z ∈ K, ‖z - α‖ ≤ m :=
    fun z hzK => le_csSup hS_comp.bddAbove ⟨z, hzK, rfl⟩
  have hm_pos : 0 < m := lt_of_lt_of_le (norm_pos_iff.mpr hz_fr_ne) (hm_ge z_fr hz_fr_K)
  refine ⟨hK_ne, hm_pos, ?_⟩
  intro U R hU hclU hR_diff
  by_contra h_all_lt
  push Not at h_all_lt
  let g : ℂ → ℂ := fun z => (z - α) * R z - 1
  have hg_diff_U : DifferentiableOn ℂ g U :=
    ((differentiableOn_id.sub (differentiableOn_const α)).mul hR_diff).sub (differentiableOn_const 1)
  have hg_diff_V₀ : DifferentiableOn ℂ g V₀ :=
    hg_diff_U.mono (subset_closure.trans hclU)
  have hg_cont_cl : ContinuousOn g (closure V₀) :=
    hg_diff_U.continuousOn.mono hclU
  have hfr_comp : IsCompact (frontier V₀) :=
    (Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hV₀_bdd.closure⟩).of_isClosed_subset
      isClosed_frontier frontier_subset_closure
  obtain ⟨z₀, hz₀_fr, hz₀_max⟩ := hfr_comp.exists_isMaxOn hfr_ne
    ((hg_cont_cl.mono frontier_subset_closure).norm)
  have hz₀_K : z₀ ∈ K := hfr_sub hz₀_fr
  have hz₀_ne : z₀ - α ≠ 0 := sub_ne_zero.mpr (fun heq => hV₀_disj hα (heq ▸ hz₀_K))
  have hgz₀_eq : g z₀ = - (z₀ - α) * ((z₀ - α)⁻¹ - R z₀) := by
    dsimp only [g]
    have h1 : (z₀ - α) * (z₀ - α)⁻¹ = 1 := mul_inv_cancel₀ hz₀_ne
    calc
      (z₀ - α) * R z₀ - 1 = (z₀ - α) * R z₀ - (z₀ - α) * (z₀ - α)⁻¹ := by rw [h1]
      _ = - (z₀ - α) * ((z₀ - α)⁻¹ - R z₀) := by ring
  have hgz₀_lt1 : ‖g z₀‖ < 1 := by
    rw [hgz₀_eq, norm_mul, norm_neg]
    calc
      ‖z₀ - α‖ * ‖(z₀ - α)⁻¹ - R z₀‖
          ≤ m * ‖(z₀ - α)⁻¹ - R z₀‖ :=
            mul_le_mul_of_nonneg_right (hm_ge z₀ hz₀_K) (norm_nonneg _)
      _ < m * (1 / m) := mul_lt_mul_of_pos_left (h_all_lt z₀ hz₀_K) hm_pos
      _ = 1 := mul_one_div_cancel hm_pos.ne'
  have hgα_le : ‖g α‖ ≤ ‖g z₀‖ :=
    Complex.norm_le_of_forall_mem_frontier_norm_le hV₀_bdd ⟨hg_diff_V₀, hg_cont_cl⟩
      (fun w hw => hz₀_max hw) (subset_closure hα)
  have hgα_eq1 : ‖g α‖ = 1 := by simp [g]
  linarith

/-- Any connected component `V` of `S² \ K` (`K ⊆ ℂ` compact) with `∞ ∉ V` projects to a nonempty
bounded open connected subset `V₀ = ((↑) : ℂ → S²) ⁻¹' V ⊆ Kᶜ` with `frontier V₀ ⊆ K`. -/
theorem bounded_planar_component_of_not_infty_mem {K : Set ℂ} (hK : IsCompact K)
    {x : RiemannSphere} (hx : x ∈ sphericalCompl K)
    (hnot_inf : (∞ : RiemannSphere) ∉ connectedComponentIn (sphericalCompl K) x) :
    let V := connectedComponentIn (sphericalCompl K) x
    let V₀ := ((↑) : ℂ → RiemannSphere) ⁻¹' V
    V₀.Nonempty ∧ IsOpen V₀ ∧ IsConnected V₀ ∧ Bornology.IsBounded V₀ ∧
      V₀ ⊆ Kᶜ ∧ frontier V₀ ⊆ K := by
  intro V V₀
  have hSK_open : IsOpen (sphericalCompl K) := isOpen_sphericalCompl_of_isCompact hK
  have hV_open : IsOpen V := isOpen_connectedComponentIn_spherical hSK_open x
  have hV_conn : IsConnected V := isConnected_connectedComponentIn_of_mem hx
  have hV₀_ne : V₀.Nonempty := by
    induction x using OnePoint.rec with
    | infty => exact False.elim (hnot_inf (mem_connectedComponentIn hx))
    | coe z => exact ⟨z, mem_connectedComponentIn hx⟩
  have hV₀_open : IsOpen V₀ := hV_open.preimage OnePoint.continuous_coe
  have hV₀_conn : IsConnected V₀ := isConnected_preimage_coe_of_isOpen hV_open hV_conn hV₀_ne
  have hV₀_disj : V₀ ⊆ Kᶜ := by
    intro z hz hzK
    exact (connectedComponentIn_subset _ _ hz) ⟨z, hzK, rfl⟩
  -- Boundedness: `connectedComponentIn (sphericalCompl K) ∞` is open and disjoint from `V`
  have hinf_SK : (∞ : RiemannSphere) ∈ sphericalCompl K := by
    rintro ⟨z, _, hz⟩
    exact OnePoint.coe_ne_infty z hz
  let V_inf := connectedComponentIn (sphericalCompl K) ∞
  have hV_inf_open : IsOpen V_inf := isOpen_connectedComponentIn_spherical hSK_open ∞
  obtain ⟨r, hr, hinf_sub⟩ :=
    ((isOpen_riemannSphere_iff V_inf).mp hV_inf_open).2 (mem_connectedComponentIn hinf_SK)
  have hV₀_bdd : Bornology.IsBounded V₀ := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := r)).subset ?_
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    by_contra hgt
    have hz_inf : (z : RiemannSphere) ∈ V_inf :=
      hinf_sub ((coe_mem_infinityDisc z r).mpr (not_le.mp hgt))
    have heq : connectedComponentIn (sphericalCompl K) x = V_inf :=
      (connectedComponentIn_eq hz).trans (connectedComponentIn_eq hz_inf).symm
    exact hnot_inf (by rw [heq]; exact mem_connectedComponentIn hinf_SK)
  -- Frontier inclusion: `frontier V₀ ⊆ K`
  have hfr_sub : frontier V₀ ⊆ K := by
    intro z hz_fr
    by_contra hz_notK
    have hz_SK : (z : RiemannSphere) ∈ sphericalCompl K := by
      rintro ⟨w, hwK, hweq⟩
      exact hz_notK (OnePoint.coe_injective hweq ▸ hwK)
    obtain ⟨δ, hδ, hball_Kc⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl z hz_notK
    obtain ⟨w, hw_V₀, hw_ball⟩ :=
      Metric.mem_closure_iff.mp hz_fr.1 δ hδ
    rw [dist_comm] at hw_ball
    have hball_SK : ((↑) : ℂ → RiemannSphere) '' ball z δ ⊆ sphericalCompl K := by
      rintro p ⟨u, hu, rfl⟩ ⟨u', hu'K, hu'eq⟩
      exact hball_Kc hu (OnePoint.coe_injective hu'eq ▸ hu'K)
    have hpre : IsPreconnected (((↑) : ℂ → RiemannSphere) '' ball z δ) :=
      (convex_ball z δ).isPreconnected.image _ OnePoint.continuous_coe.continuousOn
    have hw_img : (w : RiemannSphere) ∈ ((↑) : ℂ → RiemannSphere) '' ball z δ :=
      ⟨w, hw_ball, rfl⟩
    have hz_img : (z : RiemannSphere) ∈ ((↑) : ℂ → RiemannSphere) '' ball z δ :=
      ⟨z, Metric.mem_ball_self hδ, rfl⟩
    have hsub_V : ((↑) : ℂ → RiemannSphere) '' ball z δ ⊆ V := by
      rw [show V = connectedComponentIn (sphericalCompl K) (w : RiemannSphere) from
        connectedComponentIn_eq hw_V₀]
      exact hpre.subset_connectedComponentIn hw_img hball_SK
    have hz_V₀ : z ∈ V₀ := hsub_V hz_img
    exact (hV₀_open.interior_eq ▸ hz_fr.2) hz_V₀
  exact ⟨hV₀_ne, hV₀_open, hV₀_conn, hV₀_bdd, hV₀_disj, hfr_sub⟩

/-- **Remark / Theorem 13.8 (Necessity of connected spherical complement and prescribed poles,
RCA pp. 271–272):**
Let `K ⊆ ℂ` be compact.
1. If `S² \ K` is not connected, then `K` is nonempty and there exists a nonempty bounded open
   connected subset `V₀ ⊆ Kᶜ` with `frontier V₀ ⊆ K` (`V₀ = ((↑) : ℂ → S²) ⁻¹' V` for a bounded
   component `V` of `S² \ K`) such that for every `α ∈ V₀`:
   - `f(z) = (z - α)⁻¹` is holomorphic on the open neighborhood `{α}ᶜ` of `K`,
   - `m := sSup ((fun z => ‖z - α‖) '' K) > 0`, and
   - for **every** polynomial `P : Polynomial ℂ`, `∃ z ∈ K, 1 / m ≤ ‖(z - α)⁻¹ - P.eval z‖`
     (in particular `(z - α)⁻¹` cannot be uniformly approximated by polynomials on `K`).
2. Prescribed-pole necessity: for any compact `K ⊆ ℂ` with at least two distinct points
   (`K.Nontrivial`) and any `A ⊆ S² \ K`, universal uniform approximation on `K` of functions
   holomorphic near `K` by rationals with spherical poles in `A` holds **if and only if** `A`
   meets every connected component of `S² \ K`. -/
theorem theorem13_8 {K : Set ℂ} (hK : IsCompact K) :
    (¬ IsConnected (sphericalCompl K) →
      K.Nonempty ∧
      ∃ V₀ : Set ℂ, V₀.Nonempty ∧ IsOpen V₀ ∧ IsConnected V₀ ∧ Bornology.IsBounded V₀ ∧
        V₀ ⊆ Kᶜ ∧ frontier V₀ ⊆ K ∧
        (∀ α ∈ V₀,
          let m := sSup ((fun z => ‖z - α‖) '' K)
          RudinRCA.Chapter10.HolomorphicOn (fun z => (z - α)⁻¹) ({α}ᶜ) ∧
          K ⊆ {α}ᶜ ∧
          0 < m ∧
          (∀ P : Polynomial ℂ, ∃ z ∈ K, 1 / m ≤ ‖(z - α)⁻¹ - P.eval z‖) ∧
          ¬ (∃ P : ℕ → Polynomial ℂ,
              TendstoUniformlyOn (fun n z => (P n).eval z) (fun z => (z - α)⁻¹) atTop K))) ∧
    (K.Nontrivial → ∀ {A : Set RiemannSphere}, A ⊆ sphericalCompl K →
      ((∀ {Ω : Set ℂ}, IsOpen Ω → K ⊆ Ω →
        ∀ {f : ℂ → ℂ}, RudinRCA.Chapter10.HolomorphicOn f Ω →
        ∀ {ε : ℝ}, 0 < ε →
        ∃ R : ℂ → ℂ, IsRationalWithSphericalPolesIn R A ∧ ∀ z ∈ K, ‖f z - R z‖ < ε) ↔
       (∀ x ∈ sphericalCompl K, (A ∩ connectedComponentIn (sphericalCompl K) x).Nonempty))) := by
  constructor
  · intro hnot_conn
    have hinf_SK : (∞ : RiemannSphere) ∈ sphericalCompl K := by
      rintro ⟨z, _, hz⟩
      exact OnePoint.coe_ne_infty z hz
    -- Since `∞ ∈ sphericalCompl K` and `sphericalCompl K` is not connected, some `x ∈ sphericalCompl K`
    -- has `∞ ∉ connectedComponentIn (sphericalCompl K) x`
    have hex_x : ∃ x ∈ sphericalCompl K,
        (∞ : RiemannSphere) ∉ connectedComponentIn (sphericalCompl K) x := by
      by_contra hall
      push Not at hall
      have heq : sphericalCompl K = connectedComponentIn (sphericalCompl K) ∞ := by
        apply Subset.antisymm
        · intro x hx
          have h := hall x hx
          rw [← connectedComponentIn_eq h]
          exact mem_connectedComponentIn hx
        · exact connectedComponentIn_subset _ _
      exact hnot_conn (heq ▸ isConnected_connectedComponentIn_of_mem hinf_SK)
    obtain ⟨x, hx, hnot_inf⟩ := hex_x
    obtain ⟨hV₀_ne, hV₀_open, hV₀_conn, hV₀_bdd, hV₀_disj, hfr_sub⟩ :=
      bounded_planar_component_of_not_infty_mem hK hx hnot_inf
    have ⟨α₀, hα₀⟩ := hV₀_ne
    obtain ⟨hK_ne, _, _⟩ := max_modulus_inv_bound hK hV₀_open hV₀_bdd hV₀_disj hfr_sub hα₀
    refine ⟨hK_ne, ((↑) : ℂ → RiemannSphere) ⁻¹' connectedComponentIn (sphericalCompl K) x,
      hV₀_ne, hV₀_open, hV₀_conn, hV₀_bdd, hV₀_disj, hfr_sub, ?_⟩
    intro α hα
    obtain ⟨_, hm_pos, hmax⟩ := max_modulus_inv_bound hK hV₀_open hV₀_bdd hV₀_disj hfr_sub hα
    have hhol_inv : RudinRCA.Chapter10.HolomorphicOn (fun z => (z - α)⁻¹) ({α}ᶜ) := by
      intro z hz
      exact (differentiableAt_id.sub (differentiableAt_const α)).inv
        (sub_ne_zero.mpr hz)
    have hK_sub : K ⊆ {α}ᶜ := by
      intro z hzK hza
      exact hV₀_disj hα (hza ▸ hzK)
    have hpoly_bound : ∀ P : Polynomial ℂ,
        ∃ z ∈ K, 1 / sSup ((fun z => ‖z - α‖) '' K) ≤ ‖(z - α)⁻¹ - P.eval z‖ := by
      intro P
      exact hmax isOpen_univ (subset_univ _) P.differentiable.differentiableOn
    refine ⟨hhol_inv, hK_sub, hm_pos, hpoly_bound, ?_⟩
    rintro ⟨P_seq, hunif⟩
    have h1m_pos : 0 < 1 / sSup ((fun z => ‖z - α‖) '' K) := by positivity
    obtain ⟨N, hN⟩ :=
      Filter.eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hunif) _ h1m_pos)
    obtain ⟨z, hzK, hge⟩ := hpoly_bound (P_seq N)
    have hlt := hN N (le_refl N) z hzK
    rw [dist_eq_norm] at hlt
    linarith
  · intro hK_nontriv A hKA
    refine ⟨?_, fun hA_meet Ω hΩ hKΩ f hf ε hε =>
      (theorem13_6 hK).2 hKA hA_meet hΩ hKΩ hf hε⟩
    intro h_approx x hx
    by_contra hmiss
    let V := connectedComponentIn (sphericalCompl K) x
    by_cases hinf_V : (∞ : RiemannSphere) ∈ V
    · by_cases hA_empty : A = ∅
      · -- `A = ∅`: every rational with poles in `∅` is constant, failing on `f(z) = z` for `K.Nontrivial`
        subst hA_empty
        obtain ⟨z₁, hz₁, z₂, hz₂, hne₁₂⟩ := hK_nontriv
        let ε₀ : ℝ := ‖z₁ - z₂‖ / 2
        have hε₀ : 0 < ε₀ := div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne₁₂)) zero_lt_two
        obtain ⟨R, hR_poles, hR_est⟩ :=
          h_approx isOpen_univ (subset_univ K) (fun _ _ => differentiableAt_id) hε₀
        obtain ⟨c, hc⟩ := isRationalWithSphericalPolesIn_empty hR_poles
        have h1 := hR_est z₁ hz₁
        have h2 := hR_est z₂ hz₂
        rw [hc z₁] at h1
        rw [hc z₂] at h2
        have htri : ‖z₁ - z₂‖ ≤ ‖z₁ - c‖ + ‖z₂ - c‖ := by
          calc
            ‖z₁ - z₂‖ = ‖(z₁ - c) - (z₂ - c)‖ := by congr 1; ring
            _ ≤ ‖z₁ - c‖ + ‖z₂ - c‖ := norm_sub_le _ _
        change ‖z₁ - c‖ < ‖z₁ - z₂‖ / 2 at h1
        change ‖z₂ - c‖ < ‖z₁ - z₂‖ / 2 at h2
        linarith
      · -- `A ≠ ∅` and `∞ ∈ V`: pick `(β : ℂ) ∈ A` (`β ∉ V`) and invert at `β` (`w = (z - β)⁻¹`)
        obtain ⟨p_a, hp_a⟩ := Set.nonempty_iff_ne_empty.mpr hA_empty
        induction p_a using OnePoint.rec with
        | infty =>
          exact hmiss ⟨∞, hp_a, hinf_V⟩
        | coe β =>
          have hβ_not_K : β ∉ K := fun hβK => hKA hp_a ⟨β, hβK, rfl⟩
          have hβ_SK : (β : RiemannSphere) ∈ sphericalCompl K := hKA hp_a
          have hβ_not_V : (β : RiemannSphere) ∉ V :=
            fun hβV => hmiss ⟨(β : RiemannSphere), hp_a, hβV⟩
          let ψ : ℂ → ℂ := fun z => (z - β)⁻¹
          have hψ_cont : ContinuousOn ψ K := by
            intro z hzK
            exact (continuousWithinAt_id.sub continuousWithinAt_const).inv₀
              (sub_ne_zero.mpr (fun (heq : z = β) => hβ_not_K (heq ▸ hzK)))
          let K_inv : Set ℂ := ψ '' K
          have hK_inv_comp : IsCompact K_inv := hK.image_of_continuousOn hψ_cont
          have h0_not_Kinv : (0 : ℂ) ∉ K_inv := by
            rintro ⟨z, hzK, h0eq⟩
            exact sub_ne_zero.mpr (fun (heq : z = β) => hβ_not_K (heq ▸ hzK))
              (inv_eq_zero.mp h0eq)
          have h0_SKinv : ((0 : ℂ) : RiemannSphere) ∈ sphericalCompl K_inv := by
            rintro ⟨w, hw, hweq⟩
            exact h0_not_Kinv (OnePoint.coe_injective hweq ▸ hw)
          -- Continuous map `Φ : ℂ → RiemannSphere`, `0 ↦ ∞`, `w ≠ 0 ↦ β + w⁻¹`
          let Φ : ℂ → RiemannSphere :=
            fun w => if w = 0 then ∞ else ((β + w⁻¹ : ℂ) : RiemannSphere)
          have hΦ_cont : Continuous Φ := by
            rw [continuous_iff_continuousAt]
            intro w₀
            by_cases hw₀ : w₀ = 0
            · subst hw₀
              rw [ContinuousAt, show Φ 0 = ∞ by simp [Φ], Filter.tendsto_iff_forall_eventually_mem]
              intro S hS
              obtain ⟨M, _, hsub_S⟩ := mem_nhds_infinity_iff.mp hS
              let r_δ : ℝ := 1 / (‖M‖ + ‖β‖ + 1)
              have hr_δ : 0 < r_δ := by positivity
              filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr_δ] with w hw
              apply hsub_S
              by_cases hw0 : w = 0
              · subst hw0
                simp [Φ, infinity_mem_infinityDisc]
              · simp only [Φ, hw0, ↓reduceIte, coe_mem_infinityDisc]
                rw [Metric.mem_ball, dist_zero_right] at hw
                have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
                have hinv_gt : ‖M‖ + ‖β‖ + 1 < ‖w‖⁻¹ := by
                  have h := inv_strictAnti₀ hw_pos hw
                  have hr_inv : r_δ⁻¹ = ‖M‖ + ‖β‖ + 1 := by
                    dsimp only [r_δ]
                    rw [one_div, inv_inv]
                  rwa [hr_inv] at h
                have htri : ‖w⁻¹‖ ≤ ‖β + w⁻¹‖ + ‖β‖ := by
                  calc
                    ‖w⁻¹‖ = ‖(β + w⁻¹) - β‖ := by congr 1; ring
                    _ ≤ ‖β + w⁻¹‖ + ‖β‖ := norm_sub_le _ _
                have hM_le : M ≤ ‖M‖ := le_abs_self M
                rw [norm_inv] at htri
                linarith
            · have hcont_fin : ContinuousAt (fun w : ℂ => ((β + w⁻¹ : ℂ) : RiemannSphere)) w₀ :=
                OnePoint.continuous_coe.continuousAt.comp
                  (continuousAt_const.add (continuousAt_id.inv₀ hw₀))
              apply hcont_fin.congr
              filter_upwards [eventually_ne_nhds hw₀] with w hw
              simp [Φ, hw]
          have hΦ_SK : ∀ w ∈ K_invᶜ, Φ w ∈ sphericalCompl K := by
            intro w hw
            by_cases hw0 : w = 0
            · subst hw0
              simp only [Φ, ↓reduceIte]
              rintro ⟨z, _, hz⟩
              exact OnePoint.coe_ne_infty z hz
            · simp only [Φ, hw0, ↓reduceIte]
              rintro ⟨z, hzK, hzeq⟩
              have hzeq' : β + w⁻¹ = z := OnePoint.coe_injective hzeq.symm
              have hw_eq : w = (z - β)⁻¹ := by
                have hsub : z - β = w⁻¹ := by linear_combination hzeq'.symm
                rw [hsub, inv_inv]
              exact hw ⟨z, hzK, hw_eq.symm⟩
          -- `W₀ := connectedComponentIn (K_invᶜ) 0` is open, nonempty, connected, bounded, `frontier W₀ ⊆ K_inv`
          let W₀ : Set ℂ := connectedComponentIn (K_invᶜ) 0
          have hKinv_compl_open : IsOpen (K_invᶜ) := hK_inv_comp.isClosed.isOpen_compl
          have hW₀_open : IsOpen W₀ := by
            rw [Metric.isOpen_iff]
            intro w hw
            obtain ⟨r_w, hr_w, hball_w⟩ :=
              Metric.isOpen_iff.mp hKinv_compl_open w (connectedComponentIn_subset _ _ hw)
            refine ⟨r_w, hr_w, ?_⟩
            rw [show W₀ = connectedComponentIn (K_invᶜ) w from connectedComponentIn_eq hw]
            exact (convex_ball w r_w).isPreconnected.subset_connectedComponentIn
              (Metric.mem_ball_self hr_w) hball_w
          have h0_W₀ : (0 : ℂ) ∈ W₀ := mem_connectedComponentIn h0_not_Kinv
          have hW₀_conn : IsConnected W₀ := isConnected_connectedComponentIn_of_mem h0_not_Kinv
          have hW₀_disj : W₀ ⊆ K_invᶜ := connectedComponentIn_subset _ _
          have hΦ_W₀_sub_V : Φ '' W₀ ⊆ V := by
            have hpre : IsPreconnected (Φ '' W₀) :=
              hW₀_conn.isPreconnected.image Φ hΦ_cont.continuousOn
            have hmem_inf : (∞ : RiemannSphere) ∈ Φ '' W₀ := ⟨0, h0_W₀, by simp [Φ]⟩
            have hsub_SK : Φ '' W₀ ⊆ sphericalCompl K := by
              rintro _ ⟨w, hw, rfl⟩
              exact hΦ_SK w (hW₀_disj hw)
            rw [show V = connectedComponentIn (sphericalCompl K) ∞ from
              connectedComponentIn_eq hinf_V]
            exact hpre.subset_connectedComponentIn hmem_inf hsub_SK
          -- `W₀` is bounded because `connectedComponentIn (sphericalCompl K) β` is open and disjoint from `V`
          have hVβ_open : IsOpen (connectedComponentIn (sphericalCompl K) (β : RiemannSphere)) :=
            isOpen_connectedComponentIn_spherical (isOpen_sphericalCompl_of_isCompact hK) _
          obtain ⟨δ_β, hδ_β, hball_β⟩ :=
            ((isOpen_riemannSphere_iff _).mp hVβ_open).1 β (mem_connectedComponentIn hβ_SK)
          have hW₀_bdd : Bornology.IsBounded W₀ := by
            refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := max 1 (1 / δ_β))).subset ?_
            intro w hw
            rw [mem_closedBall, dist_zero_right]
            by_cases hw0 : w = 0
            · subst hw0
              rw [norm_zero]
              exact zero_le_one.trans (le_max_left 1 (1 / δ_β))
            · have hΦw_V : Φ w ∈ V := hΦ_W₀_sub_V ⟨w, hw, rfl⟩
              simp only [Φ, hw0, ↓reduceIte] at hΦw_V
              have hnot_ball : β + w⁻¹ ∉ ball β δ_β := by
                intro hmem
                have hVβ : ((β + w⁻¹ : ℂ) : RiemannSphere) ∈
                    connectedComponentIn (sphericalCompl K) (β : RiemannSphere) :=
                  hball_β ⟨β + w⁻¹, hmem, rfl⟩
                have heqV : V = connectedComponentIn (sphericalCompl K) (β : RiemannSphere) :=
                  (connectedComponentIn_eq hΦw_V).trans (connectedComponentIn_eq hVβ).symm
                exact hβ_not_V (heqV ▸ mem_connectedComponentIn hβ_SK)
              rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_inv, not_lt] at hnot_ball
              have hw_le : ‖w‖ ≤ 1 / δ_β := by
                have h1 := inv_anti₀ hδ_β hnot_ball
                rwa [inv_inv, ← one_div] at h1
              exact hw_le.trans (le_max_right 1 (1 / δ_β))
          have hfr_W₀ : frontier W₀ ⊆ K_inv := by
            intro w hw_fr
            by_contra hw_not
            obtain ⟨r_w, hr_w, hball_w⟩ := Metric.isOpen_iff.mp hKinv_compl_open w hw_not
            obtain ⟨u, hu_W₀, hu_ball⟩ := Metric.mem_closure_iff.mp hw_fr.1 r_w hr_w
            rw [dist_comm] at hu_ball
            have hw_W₀ : w ∈ W₀ := by
              rw [show W₀ = connectedComponentIn (K_invᶜ) u from
                connectedComponentIn_eq hu_W₀]
              exact (convex_ball w r_w).isPreconnected.subset_connectedComponentIn
                hu_ball hball_w (Metric.mem_ball_self hr_w)
            exact (hW₀_open.interior_eq ▸ hw_fr.2) hw_W₀
          obtain ⟨_, hm'_pos, hmax_W₀⟩ :=
            max_modulus_inv_bound hK_inv_comp hW₀_open hW₀_bdd hW₀_disj hfr_W₀ h0_W₀
          let m' := sSup ((fun w => ‖w - 0‖) '' K_inv)
          obtain ⟨R, hR_poles, hR_est⟩ :=
            h_approx isOpen_univ (subset_univ K)
              (fun _ _ => differentiableAt_id.sub (differentiableAt_const β))
              (by positivity : 0 < 1 / m')
          rcases hR_poles with ⟨P, Q, hQ_monic, _, hQ_roots, hdeg_inf, hReq⟩
          have hnot_inf_A : (∞ : RiemannSphere) ∉ A :=
            fun hinfA => hmiss ⟨∞, hinfA, hinf_V⟩
          have hdeg_le : P.natDegree ≤ Q.natDegree := by
            by_contra hlt
            exact hnot_inf_A (hdeg_inf (Nat.lt_of_not_ge hlt))
          let d := Q.natDegree
          let P_hom := polyHomAtBeta β d P
          let Q_hom := polyHomAtBeta β d Q
          let U_hom : Set ℂ := {w : ℂ | Q_hom.eval w ≠ 0}
          have hU_hom_open : IsOpen U_hom := isOpen_compl_singleton.preimage Q_hom.continuous
          have hcl_sub_U : closure W₀ ⊆ U_hom := by
            intro w hw_cl hQ0
            by_cases hw0 : w = 0
            · subst hw0
              have h1 : Q_hom.eval 0 = 1 := polyHomAtBeta_eval_zero β hQ_monic
              exact one_ne_zero (h1 ▸ hQ0)
            · have hQw : Q_hom.eval w = w ^ d * Q.eval (β + w⁻¹) :=
                polyHomAtBeta_eval_ne_zero β (le_refl d) hw0
              rw [hQw] at hQ0
              rcases mul_eq_zero.mp hQ0 with hwd0 | hQ_eval0
              · exact pow_ne_zero d hw0 hwd0
              · have hmem_A : ((β + w⁻¹ : ℂ) : RiemannSphere) ∈ A := hQ_roots _ hQ_eval0
                by_cases hw_in : w ∈ W₀
                · have hmem_V : Φ w ∈ V := hΦ_W₀_sub_V ⟨w, hw_in, rfl⟩
                  simp only [Φ, hw0, ↓reduceIte] at hmem_V
                  exact hmiss ⟨((β + w⁻¹ : ℂ) : RiemannSphere), hmem_A, hmem_V⟩
                · have hw_fr : w ∈ frontier W₀ :=
                    ⟨hw_cl, fun hw_int => hw_in (interior_subset hw_int)⟩
                  obtain ⟨z, hzK, hzeq⟩ := hfr_W₀ hw_fr
                  have hβw : β + w⁻¹ = z := by
                    have hinv : w⁻¹ = z - β := by
                      rw [← hzeq]
                      exact inv_inv (z - β)
                    linear_combination hinv
                  rw [hβw] at hmem_A
                  exact hKA hmem_A ⟨z, hzK, rfl⟩
          have hR_hom_diff : DifferentiableOn ℂ (fun w => P_hom.eval w / Q_hom.eval w) U_hom := by
            intro w hw
            exact ((P_hom.differentiableAt (x := w)).div (Q_hom.differentiableAt (x := w))
              hw).differentiableWithinAt
          obtain ⟨w_bad, hw_bad_Kinv, hge_m'⟩ := hmax_W₀ hU_hom_open hcl_sub_U hR_hom_diff
          obtain ⟨z_bad, hz_bad_K, rfl⟩ := hw_bad_Kinv
          have hw_ne0 : ψ z_bad ≠ 0 := by
            dsimp only [ψ]
            exact inv_ne_zero (sub_ne_zero.mpr
              (fun (heq : z_bad = β) => hβ_not_K (heq ▸ hz_bad_K)))
          have hβw_eq : β + (ψ z_bad)⁻¹ = z_bad := by
            dsimp only [ψ]
            rw [inv_inv]
            ring
          have hhom_eq_R : P_hom.eval (ψ z_bad) / Q_hom.eval (ψ z_bad) = R z_bad := by
            rw [polyHomAtBeta_eval_ne_zero β hdeg_le hw_ne0,
              polyHomAtBeta_eval_ne_zero β (le_refl d) hw_ne0,
              mul_div_mul_left _ _ (pow_ne_zero d hw_ne0), hβw_eq, hReq z_bad]
          have hψ_inv : (ψ z_bad - 0)⁻¹ = z_bad - β := by
            dsimp only [ψ]
            rw [sub_zero, inv_inv]
          rw [hψ_inv, hhom_eq_R] at hge_m'
          have hlt_m' : ‖z_bad - β - R z_bad‖ < 1 / sSup ((fun z => ‖z - 0‖) '' K_inv) :=
            hR_est z_bad hz_bad_K
          linarith
    · -- `∞ ∉ V`: bounded complementary component `V₀`, apply `max_modulus_inv_bound` to `(z - α)⁻¹`
      obtain ⟨hV₀_ne, hV₀_open, _, hV₀_bdd, hV₀_disj, hfr_sub⟩ :=
        bounded_planar_component_of_not_infty_mem hK hx hinf_V
      obtain ⟨α, hα⟩ := hV₀_ne
      obtain ⟨_, hm_pos, hmax⟩ := max_modulus_inv_bound hK hV₀_open hV₀_bdd hV₀_disj hfr_sub hα
      let m := sSup ((fun z => ‖z - α‖) '' K)
      have hhol_inv : RudinRCA.Chapter10.HolomorphicOn (fun z => (z - α)⁻¹) ({α}ᶜ) :=
        fun z hz => (differentiableAt_id.sub (differentiableAt_const α)).inv (sub_ne_zero.mpr hz)
      have hK_sub : K ⊆ {α}ᶜ := fun z hzK hza => hV₀_disj hα (hza ▸ hzK)
      obtain ⟨R, hR_poles, hR_est⟩ :=
        h_approx isOpen_compl_singleton hK_sub hhol_inv (by positivity : 0 < 1 / m)
      rcases hR_poles with ⟨P, Q, _, _, hQ_roots, _, hReq⟩
      let U_R : Set ℂ := {z : ℂ | Q.eval z ≠ 0}
      have hUR_open : IsOpen U_R := isOpen_compl_singleton.preimage Q.continuous
      have hcl_sub : closure (((↑) : ℂ → RiemannSphere) ⁻¹' V) ⊆ U_R := by
        intro z hz_cl hQz
        have hzA : (z : RiemannSphere) ∈ A := hQ_roots z hQz
        by_cases hz_in : z ∈ ((↑) : ℂ → RiemannSphere) ⁻¹' V
        · exact hmiss ⟨(z : RiemannSphere), hzA, hz_in⟩
        · have hz_fr : z ∈ frontier (((↑) : ℂ → RiemannSphere) ⁻¹' V) :=
            ⟨hz_cl, fun hz_int => hz_in (interior_subset hz_int)⟩
          exact hKA hzA ⟨z, hfr_sub hz_fr, rfl⟩
      have hR_diff : DifferentiableOn ℂ R U_R := by
        rw [show R = fun z => P.eval z / Q.eval z from funext hReq]
        intro z hz
        exact ((P.differentiableAt (x := z)).div (Q.differentiableAt (x := z))
          hz).differentiableWithinAt
      obtain ⟨z_bad, hz_bad_K, hge⟩ := hmax hUR_open hcl_sub hR_diff
      linarith [hR_est z_bad hz_bad_K]


/-! ## 13.9 Open-set Runge approximation -/

/-- **Theorem 13.9 (Open-set Runge approximation, RCA p. 272):**
Let `Ω ⊆ ℂ` be any open set (connectedness is not required).
1. Given `A ⊆ S² \ Ω` meeting every connected component of `S² \ Ω` and `f ∈ H(Ω)`, there exists a
   sequence of rational functions `R_n`, all with spherical poles in `A`
   (`IsRationalWithSphericalPolesIn (R n) A`), converging uniformly to `f` on every compact subset
   of `Ω` (`ConvergesOnCompactSubsets R f Ω`).
2. In particular, if `S² \ Ω` is connected, then for every `f ∈ H(Ω)` there exists a sequence of
   polynomials `P_n` converging uniformly to `f` on every compact subset of `Ω`. -/
theorem theorem13_9 {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    (∀ {A : Set RiemannSphere}, A ⊆ sphericalCompl Ω →
      (∀ x ∈ sphericalCompl Ω, (A ∩ connectedComponentIn (sphericalCompl Ω) x).Nonempty) →
      ∀ {f : ℂ → ℂ}, RudinRCA.Chapter10.HolomorphicOn f Ω →
      ∃ R : ℕ → ℂ → ℂ,
        (∀ n : ℕ, IsRationalWithSphericalPolesIn (R n) A) ∧
        RudinRCA.Chapter10.ConvergesOnCompactSubsets R f Ω) ∧
    (IsConnected (sphericalCompl Ω) →
      ∀ {f : ℂ → ℂ}, RudinRCA.Chapter10.HolomorphicOn f Ω →
      ∃ P : ℕ → Polynomial ℂ,
        RudinRCA.Chapter10.ConvergesOnCompactSubsets (fun n z => (P n).eval z) f Ω) := by
  have hpart1 :
      ∀ {A : Set RiemannSphere}, A ⊆ sphericalCompl Ω →
        (∀ x ∈ sphericalCompl Ω, (A ∩ connectedComponentIn (sphericalCompl Ω) x).Nonempty) →
        ∀ {f : ℂ → ℂ}, RudinRCA.Chapter10.HolomorphicOn f Ω →
        ∃ R : ℕ → ℂ → ℂ,
          (∀ n : ℕ, IsRationalWithSphericalPolesIn (R n) A) ∧
          RudinRCA.Chapter10.ConvergesOnCompactSubsets R f Ω := by
    intro A hΩA hA_meet f hf
    have hex : ∀ n : ℕ, ∃ Rn : ℂ → ℂ, IsRationalWithSphericalPolesIn Rn A ∧
        ∀ z ∈ exhaustionSet Ω n, ‖f z - Rn z‖ < 1 / ((n : ℝ) + 1) := by
      intro n
      have hKn_sub : exhaustionSet Ω n ⊆ Ω := exhaustionSet_subset Ω n
      have hKn_A : A ⊆ sphericalCompl (exhaustionSet Ω n) := by
        refine hΩA.trans ?_
        intro p hp ⟨z, hzK, hzeq⟩
        exact hp ⟨z, hKn_sub hzK, hzeq⟩
      have hKn_meet : ∀ x ∈ sphericalCompl (exhaustionSet Ω n),
          (A ∩ connectedComponentIn (sphericalCompl (exhaustionSet Ω n)) x).Nonempty := by
        intro x hx
        obtain ⟨p, hpΩ, hcomp_sub⟩ := exhaustionSet_sphericalCompl_component Ω n x hx
        exact (hA_meet p hpΩ).mono (inter_subset_inter_right A hcomp_sub)
      exact (theorem13_6 (isCompact_exhaustionSet Ω n)).2 hKn_A hKn_meet hΩ hKn_sub hf
        (by positivity : 0 < 1 / ((n : ℝ) + 1))
    choose R hR using hex
    refine ⟨R, fun n => (hR n).1, ?_⟩
    intro K hKΩ hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := exists_subset_exhaustionSet_of_isCompact hΩ hK hKΩ
    obtain ⟨N₂, hN₂⟩ := exists_nat_one_div_lt hε
    filter_upwards [Filter.eventually_ge_atTop (max N₁ N₂)] with n hn z hzK
    rw [dist_eq_norm]
    have hz_Kn : z ∈ exhaustionSet Ω n :=
      exhaustionSet_mono Ω (le_of_max_le_left hn) (hN₁ hzK)
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N₂ : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right (le_of_max_le_right hn) 1
    exact lt_of_lt_of_le ((hR n).2 z hz_Kn) (hle.trans_lt hN₂).le
  refine ⟨hpart1, ?_⟩
  intro hconn f hf
  let A : Set RiemannSphere := {∞}
  have hΩA : A ⊆ sphericalCompl Ω := by
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    rintro ⟨z, _, hz⟩
    exact OnePoint.coe_ne_infty z hz
  have hA_meet : ∀ x ∈ sphericalCompl Ω, (A ∩ connectedComponentIn (sphericalCompl Ω) x).Nonempty := by
    intro x hx
    rw [hconn.isPreconnected.connectedComponentIn hx]
    exact ⟨∞, Set.mem_singleton ∞, hΩA (Set.mem_singleton ∞)⟩
  obtain ⟨R, hR_poles, hR_conv⟩ := hpart1 hΩA hA_meet hf
  have hpoly : ∀ n : ℕ, ∃ Pn : Polynomial ℂ, ∀ z : ℂ, R n z = Pn.eval z :=
    fun n => isRationalWithSphericalPolesIn_singleton_infty (hR_poles n)
  choose P hP using hpoly
  refine ⟨P, ?_⟩
  have hfun_eq : (fun n z => (P n).eval z) = R := by
    ext n z
    exact (hP n z).symm
  rwa [hfun_eq]


/-! ## 13.10 Mittag-Leffler's theorem -/

/-- **Theorem 13.10 (Mittag-Leffler's theorem with prescribed principal parts, RCA pp. 273–274):**
Let `Ω ⊆ ℂ` be open and `A ⊆ Ω` have no accumulation point in `Ω`. For each `α ∈ A`, prescribe a
positive integer `m α > 0` and coefficients `c α : ℕ → ℂ`, defining
`P α z := ∑ j ∈ Finset.Icc 1 (m α), c α j * (z - α)⁻¹ ^ j` (zero principal parts are permitted).
Let `A_eff := {α ∈ A | ∃ j ∈ Finset.Icc 1 (m α), c α j ≠ 0}` be the subset of `A` with nonzero
prescribed principal parts. Then there exists `f : ℂ → ℂ` such that:
1. `BookMeromorphicWithPoles f Ω A_eff` (in particular `BookMeromorphicOn f Ω`, `f ∈ H(Ω \ A_eff)`,
   and `poleSet f Ω = A_eff ⊆ A`, so `f` has no poles outside `A`), and
2. For **every** `α ∈ A` (including when `P α ≡ 0`), there exist an open neighborhood `V` of `α`
   with `V ⊆ Ω` and `V \ {α} ⊆ Ω \ A` and a function `g ∈ H(V)` such that
   `f z = g z + P α z` for all `z ∈ V \ {α}`. -/
theorem theorem13_10 {Ω A : Set ℂ} (hΩ : IsOpen Ω) (hAΩ : A ⊆ Ω)
    (hacc : ∀ z ∈ Ω, ¬ AccPt z (𝓟 A))
    (m : ℂ → ℕ) (_hm : ∀ α ∈ A, 0 < m α) (c : ℂ → ℕ → ℂ) :
    let P : ℂ → ℂ → ℂ := fun α z => ∑ j ∈ Finset.Icc 1 (m α), c α j * (z - α)⁻¹ ^ j
    let A_eff : Set ℂ := {α ∈ A | ∃ j ∈ Finset.Icc 1 (m α), c α j ≠ 0}
    ∃ f : ℂ → ℂ,
      RudinRCA.Chapter10.BookMeromorphicWithPoles f Ω A_eff ∧
      (∀ α ∈ A, ∃ (V : Set ℂ) (g : ℂ → ℂ),
        IsOpen V ∧ α ∈ V ∧ V ⊆ Ω ∧ V \ {α} ⊆ Ω \ A ∧
        RudinRCA.Chapter10.HolomorphicOn g V ∧
        EqOn f (fun z => g z + P α z) (V \ {α})) := by
  intro P A_eff
  -- Finiteness of `A ∩ K` for every compact `K ⊆ Ω`
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
  -- Disjoint finite slices `B 0 = A ∩ K_0`, `B (n + 1) = A ∩ (K_{n + 1} \ K_n)`
  let B : ℕ → Set ℂ
    | 0 => A ∩ exhaustionSet Ω 0
    | n + 1 => A ∩ (exhaustionSet Ω (n + 1) \ exhaustionSet Ω n)
  have hB_fin : ∀ k : ℕ, (B k).Finite := by
    intro k
    cases k with
    | zero => exact hfin_compact _ (isCompact_exhaustionSet Ω 0) (exhaustionSet_subset Ω 0)
    | succ n =>
      exact (hfin_compact _ (isCompact_exhaustionSet Ω (n + 1))
        (exhaustionSet_subset Ω (n + 1))).subset
        (inter_subset_inter_right A sdiff_subset)
  obtain ⟨F_slice, hmem_F⟩ : ∃ F : ℕ → Finset ℂ, ∀ k α, α ∈ F k ↔ α ∈ B k :=
    ⟨fun k => (hB_fin k).toFinset, fun k α => (hB_fin k).mem_toFinset⟩
  let Q_term : ℕ → ℂ → ℂ := fun k z => ∑ α ∈ F_slice k, P α z
  have hP_holo : ∀ α w, w ≠ α → DifferentiableAt ℂ (P α) w := by
    intro α w hw
    dsimp only [P]
    refine DifferentiableAt.fun_sum fun j _ => ?_
    exact differentiableAt_const _ |>.mul
      (((differentiableAt_id.sub (differentiableAt_const α)).inv (sub_ne_zero.mpr hw)).pow j)
  -- For each `n`, `Q_term (n + 1)` is holomorphic on `((F_slice (n + 1) : Set ℂ))ᶜ ⊇ exhaustionSet Ω n`
  have hex_R : ∀ n : ℕ, ∃ Rn : ℂ → ℂ,
      IsRationalWithSphericalPolesIn Rn (sphericalCompl Ω) ∧
      ∀ z ∈ exhaustionSet Ω n, ‖Q_term (n + 1) z - Rn z‖ < (1 / 2 : ℝ) ^ n := by
    intro n
    let U_n : Set ℂ := ((F_slice (n + 1) : Set ℂ))ᶜ
    have hUn_open : IsOpen U_n := (Finset.finite_toSet _).isClosed.isOpen_compl
    have hKn_Un : exhaustionSet Ω n ⊆ U_n := by
      intro z hzK hzF
      have hzB : z ∈ B (n + 1) := (hmem_F (n + 1) z).mp (Finset.mem_coe.mp hzF)
      exact hzB.2.2 hzK
    have hQ_holo : RudinRCA.Chapter10.HolomorphicOn (Q_term (n + 1)) U_n := by
      intro z hz
      dsimp only [Q_term]
      refine DifferentiableAt.fun_sum fun α hα => hP_holo α z ?_
      intro hza
      exact hz (hza ▸ Finset.mem_coe.mpr hα)
    have hSK_sub : sphericalCompl Ω ⊆ sphericalCompl (exhaustionSet Ω n) := by
      intro p hp ⟨z, hzK, hzeq⟩
      exact hp ⟨z, exhaustionSet_subset Ω n hzK, hzeq⟩
    have hSK_meet : ∀ x ∈ sphericalCompl (exhaustionSet Ω n),
        (sphericalCompl Ω ∩ connectedComponentIn (sphericalCompl (exhaustionSet Ω n)) x).Nonempty := by
      intro x hx
      obtain ⟨p, hpΩ, hsub⟩ := exhaustionSet_sphericalCompl_component Ω n x hx
      exact ⟨p, hpΩ, hsub (mem_connectedComponentIn hpΩ)⟩
    exact (theorem13_6 (isCompact_exhaustionSet Ω n)).2 hSK_sub hSK_meet hUn_open hKn_Un hQ_holo
      (by positivity : 0 < (1 / 2 : ℝ) ^ n)
  obtain ⟨R_approx, hR_approx⟩ : ∃ R : ℕ → ℂ → ℂ,
      ∀ n : ℕ, IsRationalWithSphericalPolesIn (R n) (sphericalCompl Ω) ∧
        ∀ z ∈ exhaustionSet Ω n, ‖Q_term (n + 1) z - R n z‖ < (1 / 2 : ℝ) ^ n :=
    ⟨fun n => Classical.choose (hex_R n), fun n => Classical.choose_spec (hex_R n)⟩
  -- Every `R_approx n` is holomorphic on `Ω` because its finite poles lie in `Ωᶜ`
  have hR_holo_Ω : ∀ n : ℕ, RudinRCA.Chapter10.HolomorphicOn (R_approx n) Ω := by
    intro n z hzΩ
    rcases (hR_approx n).1 with ⟨Pn, Qn, _, _, hQn_roots, _, hRn_eq⟩
    have hRn_fun : R_approx n = fun w => Pn.eval w / Qn.eval w := funext hRn_eq
    rw [hRn_fun]
    have hQnz : Qn.eval z ≠ 0 := by
      intro h0
      exact hQn_roots z h0 ⟨z, hzΩ, rfl⟩
    exact (Pn.differentiableAt (x := z)).div (Qn.differentiableAt (x := z)) hQnz
  -- Define `f` on `ℂ`
  let diff_term : ℕ → ℂ → ℂ := fun n z => Q_term (n + 1) z - R_approx n z
  obtain ⟨f, hf_def⟩ : ∃ f_fn : ℂ → ℂ, ∀ z, f_fn z = Q_term 0 z + ∑' n : ℕ, diff_term n z :=
    ⟨fun z => Q_term 0 z + ∑' n : ℕ, diff_term n z, fun _ => rfl⟩
  -- Tail `T_tail N z := ∑' k, diff_term (k + N) z` is holomorphic on `interior (exhaustionSet Ω N)`
  obtain ⟨T_tail, hT_def⟩ :
      ∃ T_fn : ℕ → ℂ → ℂ, ∀ N z, T_fn N z = ∑' k : ℕ, diff_term (k + N) z :=
    ⟨fun N z => ∑' k : ℕ, diff_term (k + N) z, fun _ _ => rfl⟩
  have hT_tail_holo : ∀ N : ℕ,
      RudinRCA.Chapter10.HolomorphicOn (T_tail N) (interior (exhaustionSet Ω N)) := by
    intro N
    let W_N := interior (exhaustionSet Ω N)
    have hWN_open : IsOpen W_N := isOpen_interior
    have hterm_holo : ∀ k : ℕ, RudinRCA.Chapter10.HolomorphicOn (diff_term (k + N)) W_N := by
      intro k z hzW
      have hz_KN : z ∈ exhaustionSet Ω N := interior_subset hzW
      have hz_KkN : z ∈ exhaustionSet Ω (k + N) :=
        exhaustionSet_mono Ω (Nat.le_add_left N k) hz_KN
      have hz_Ω : z ∈ Ω := exhaustionSet_subset Ω N hz_KN
      have hQ_at : DifferentiableAt ℂ (Q_term (k + N + 1)) z := by
        dsimp only [Q_term]
        refine DifferentiableAt.fun_sum fun α hα => hP_holo α z ?_
        intro hza
        subst hza
        exact ((hmem_F (k + N + 1) z).mp hα).2.2 hz_KkN
      exact hQ_at.sub (hR_holo_Ω (k + N) z hz_Ω)
    have hpart_holo : ∀ M : ℕ,
        RudinRCA.Chapter10.HolomorphicOn (fun z => ∑ k ∈ Finset.range M, diff_term (k + N) z) W_N := by
      intro M z hzW
      exact DifferentiableAt.fun_sum fun k _ => hterm_holo k z hzW
    have hu_sum : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + N)) :=
      (summable_geometric_two.comp_injective (add_left_injective N))
    have hconv_KN : TendstoUniformlyOn
        (fun M z => ∑ k ∈ Finset.range M, diff_term (k + N) z) (T_tail N) atTop
        (exhaustionSet Ω N) := by
      rw [show T_tail N = fun z => ∑' k : ℕ, diff_term (k + N) z from funext (hT_def N)]
      refine tendstoUniformlyOn_tsum_nat hu_sum ?_
      intro k z hz_KN
      have hz_KkN : z ∈ exhaustionSet Ω (k + N) :=
        exhaustionSet_mono Ω (Nat.le_add_left N k) hz_KN
      exact ((hR_approx (k + N)).2 z hz_KkN).le
    have hconv_WN : RudinRCA.Chapter10.ConvergesOnCompactSubsets
        (fun M z => ∑ k ∈ Finset.range M, diff_term (k + N) z) (T_tail N) W_N := by
      intro K hKW hK
      exact hconv_KN.mono (hKW.trans interior_subset)
    exact (RudinRCA.Chapter10.holomorphicOn_limit_and_deriv hWN_open hpart_holo hconv_WN).1
  -- Decomposition of `f` on `exhaustionSet Ω N`:
  -- `f z = (∑ k ∈ range (N + 1), Q_term k z) - (∑ n ∈ range N, R_approx n z) + T_tail N z`
  have hf_decomp : ∀ (N : ℕ), ∀ z ∈ exhaustionSet Ω N,
      f z = (∑ k ∈ Finset.range (N + 1), Q_term k z) -
        (∑ n ∈ Finset.range N, R_approx n z) + T_tail N z := by
    intro N z hz_KN
    have hsum_tail : Summable (fun k : ℕ => diff_term (k + N) z) := by
      refine Summable.of_norm_bounded
        (summable_geometric_two.comp_injective (add_left_injective N)) fun k => ?_
      have hz_KkN : z ∈ exhaustionSet Ω (k + N) :=
        exhaustionSet_mono Ω (Nat.le_add_left N k) hz_KN
      exact ((hR_approx (k + N)).2 z hz_KkN).le
    have hsplit : (∑ i ∈ Finset.range N, diff_term i z) + T_tail N z = ∑' n : ℕ, diff_term n z := by
      rw [hT_def N z]
      exact Summable.sum_add_tsum_nat_add' (f := fun n => diff_term n z) hsum_tail
    rw [hf_def z, ← hsplit]
    have hsum_diff : ∑ i ∈ Finset.range N, diff_term i z =
        (∑ i ∈ Finset.range N, Q_term (i + 1) z) - (∑ i ∈ Finset.range N, R_approx i z) :=
      Finset.sum_sub_distrib _ _
    have hQ_succ : ∑ k ∈ Finset.range (N + 1), Q_term k z =
        (∑ k ∈ Finset.range N, Q_term (k + 1) z) + Q_term 0 z :=
      Finset.sum_range_succ' (fun k => Q_term k z) N
    rw [hsum_diff, hQ_succ]
    ring
  -- Moreover, `(Finset.range (N + 1)).biUnion F_slice` has pairwise disjoint slices and equals `A ∩ K_N`
  have hslice_disj : Pairwise (fun i j => Disjoint (F_slice i) (F_slice j)) := by
    have haux : ∀ i j, i < j → ∀ α, α ∈ F_slice i → α ∈ F_slice j → False := by
      intro i j hlt α hαi hαj
      rw [hmem_F] at hαi hαj
      cases j with
      | zero => omega
      | succ n =>
        have hi_le : i ≤ n := by omega
        have hα_Ki : α ∈ exhaustionSet Ω i := by
          cases i with
          | zero => exact hαi.2
          | succ m => exact hαi.2.1
        exact hαj.2.2 (exhaustionSet_mono Ω hi_le hα_Ki)
    intro i j hij
    rw [Finset.disjoint_left]
    intro α hαi hαj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact haux i j hlt α hαi hαj
    · exact hij rfl
    · exact haux j i hgt α hαj hαi
  have hbiUnion_mem : ∀ N α,
      α ∈ (Finset.range (N + 1)).biUnion F_slice ↔ α ∈ A ∩ exhaustionSet Ω N := by
    intro N α
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨k, hk, hαk⟩
      have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [hmem_F] at hαk
      cases k with
      | zero => exact ⟨hαk.1, exhaustionSet_mono Ω hk_le hαk.2⟩
      | succ m => exact ⟨hαk.1, exhaustionSet_mono Ω hk_le hαk.2.1⟩
    · rintro ⟨hαA, hαKN⟩
      induction N with
      | zero =>
        exact ⟨0, Finset.mem_range.mpr zero_lt_one, (hmem_F 0 α).mpr ⟨hαA, hαKN⟩⟩
      | succ n ih =>
        by_cases hαKn : α ∈ exhaustionSet Ω n
        · obtain ⟨k, hk, hαk⟩ := ih hαKn
          exact ⟨k, Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hk) (Nat.lt_succ_self _)), hαk⟩
        · refine ⟨n + 1, Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
          exact (hmem_F (n + 1) α).mpr ⟨hαA, hαKN, hαKn⟩
  have hsum_Q_eq : ∀ N z,
      ∑ k ∈ Finset.range (N + 1), Q_term k z =
        ∑ α ∈ (Finset.range (N + 1)).biUnion F_slice, P α z := by
    intro N z
    symm
    exact Finset.sum_biUnion (fun i _ j _ hij => hslice_disj hij)
  -- Local principal-part property at EVERY `α ∈ A`
  have hlocal_all : ∀ α ∈ A, ∃ (V : Set ℂ) (g : ℂ → ℂ),
      IsOpen V ∧ α ∈ V ∧ V ⊆ Ω ∧ V \ {α} ⊆ Ω \ A ∧
      RudinRCA.Chapter10.HolomorphicOn g V ∧
      EqOn f (fun z => g z + P α z) (V \ {α}) := by
    intro α₀ hα₀A
    have hα₀Ω : α₀ ∈ Ω := hAΩ hα₀A
    have hmem_un : α₀ ∈ ⋃ n : ℕ, exhaustionSet Ω n := (iUnion_exhaustionSet hΩ).symm ▸ hα₀Ω
    obtain ⟨n₀, hα₀_Kn₀⟩ := Set.mem_iUnion.mp hmem_un
    let N : ℕ := n₀ + 1
    have hα₀_int : α₀ ∈ interior (exhaustionSet Ω N) :=
      exhaustionSet_subset_interior_succ Ω n₀ hα₀_Kn₀
    -- Isolate `α₀` in `A` via `¬ AccPt α₀ (𝓟 A)`
    have hnot_acc := hacc α₀ hα₀Ω
    rw [accPt_iff_nhds] at hnot_acc
    push Not at hnot_acc
    obtain ⟨U₀, hU₀, hdisj₀⟩ := hnot_acc
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem (isOpen_interior.mem_nhds hα₀_int) hU₀)
    let V : Set ℂ := ball α₀ δ
    have hV_open : IsOpen V := Metric.isOpen_ball
    have hα₀_V : α₀ ∈ V := Metric.mem_ball_self hδ
    have hV_int : V ⊆ interior (exhaustionSet Ω N) := fun z hz => (hball hz).1
    have hV_KN : V ⊆ exhaustionSet Ω N := hV_int.trans interior_subset
    have hV_Ω : V ⊆ Ω := hV_KN.trans (exhaustionSet_subset Ω N)
    have hV_sdiff : V \ {α₀} ⊆ Ω \ A := by
      rintro z ⟨hzV, hz_ne⟩
      exact ⟨hV_Ω hzV, fun hzA => hz_ne (hdisj₀ z ⟨(hball hzV).2, hzA⟩)⟩
    let S_N : Finset ℂ := (Finset.range (N + 1)).biUnion F_slice
    have hα₀_SN : α₀ ∈ S_N := (hbiUnion_mem N α₀).mpr ⟨hα₀A, hV_KN hα₀_V⟩
    let g : ℂ → ℂ := fun z =>
      (∑ β ∈ S_N.erase α₀, P β z) - (∑ n ∈ Finset.range N, R_approx n z) + T_tail N z
    have hg_holo : RudinRCA.Chapter10.HolomorphicOn g V := by
      intro z hzV
      have hsum1 : DifferentiableAt ℂ (fun w => ∑ β ∈ S_N.erase α₀, P β w) z := by
        refine DifferentiableAt.fun_sum fun β hβ => hP_holo β z ?_
        intro hzβ
        subst hzβ
        have hβA : z ∈ A := ((hbiUnion_mem N z).mp (Finset.mem_of_mem_erase hβ)).1
        have hne : z ≠ α₀ := Finset.ne_of_mem_erase hβ
        exact (hV_sdiff ⟨hzV, hne⟩).2 hβA
      have hsum2 : DifferentiableAt ℂ (fun w => ∑ n ∈ Finset.range N, R_approx n w) z :=
        DifferentiableAt.fun_sum fun n _ => hR_holo_Ω n z (hV_Ω hzV)
      exact (hsum1.sub hsum2).add (hT_tail_holo N z (hV_int hzV))
    refine ⟨V, g, hV_open, hα₀_V, hV_Ω, hV_sdiff, hg_holo, ?_⟩
    intro z hzV
    rw [hf_decomp N z (hV_KN hzV.1), hsum_Q_eq N z, ← Finset.add_sum_erase S_N (fun β => P β z) hα₀_SN]
    dsimp only [g]
    ring
  -- Check `BookMeromorphicWithPoles f Ω A_eff`
  have hAeff_sub_A : A_eff ⊆ A := fun _ h => h.1
  have hacc_eff : ∀ z ∈ Ω, ¬ AccPt z (𝓟 A_eff) :=
    fun z hz hacc' => hacc z hz (hacc'.mono (Filter.principal_mono.mpr hAeff_sub_A))
  have hf_holo_sdiff : RudinRCA.Chapter10.HolomorphicOn f (Ω \ A_eff) := by
    rintro z ⟨hzΩ, hz_not_eff⟩
    have hmem_un : z ∈ ⋃ n : ℕ, exhaustionSet Ω n := (iUnion_exhaustionSet hΩ).symm ▸ hzΩ
    obtain ⟨n₀, hz_Kn₀⟩ := Set.mem_iUnion.mp hmem_un
    let N : ℕ := n₀ + 1
    have hz_int : z ∈ interior (exhaustionSet Ω N) :=
      exhaustionSet_subset_interior_succ Ω n₀ hz_Kn₀
    let S_N : Finset ℂ := (Finset.range (N + 1)).biUnion F_slice
    let h_loc : ℂ → ℂ := fun w =>
      (∑ β ∈ S_N, P β w) - (∑ n ∈ Finset.range N, R_approx n w) + T_tail N w
    have hh_diff : DifferentiableAt ℂ h_loc z := by
      have hsum1 : DifferentiableAt ℂ (fun w => ∑ β ∈ S_N, P β w) z := by
        refine DifferentiableAt.fun_sum fun β hβ => ?_
        by_cases hzβ : z = β
        · subst hzβ
          have hzA : z ∈ A := ((hbiUnion_mem N z).mp hβ).1
          have hP_zero : P z = fun _ => 0 := by
            ext w
            dsimp only [P]
            apply Finset.sum_eq_zero
            intro j hj
            have hcj0 : c z j = 0 := by
              by_contra hne
              exact hz_not_eff ⟨hzA, j, hj, hne⟩
            rw [hcj0, zero_mul]
          rw [hP_zero]
          exact differentiableAt_const 0
        · exact hP_holo β z hzβ
      have hsum2 : DifferentiableAt ℂ (fun w => ∑ n ∈ Finset.range N, R_approx n w) z :=
        DifferentiableAt.fun_sum fun n _ => hR_holo_Ω n z hzΩ
      exact (hsum1.sub hsum2).add (hT_tail_holo N z hz_int)
    apply hh_diff.congr_of_eventuallyEq
    filter_upwards [isOpen_interior.mem_nhds hz_int] with w hw
    rw [hf_decomp N w (interior_subset hw), hsum_Q_eq N w]
  have hf_poles_eff : ∀ α ∈ A_eff,
      ∃ V : Set ℂ, IsOpen V ∧ α ∈ V ∧ V ⊆ Ω ∧ RudinRCA.Chapter10.HasPole f V α := by
    rintro α ⟨hαA, j₀, hj₀, hcj₀⟩
    obtain ⟨V, g, hV_open, hαV, hVΩ, hVsdiff, hg_holo, heq⟩ := hlocal_all α hαA
    -- Trim `P α` to its highest nonzero index `m'` in `Finset.Icc 1 (m α)`
    let S_nz := (Finset.Icc 1 (m α)).filter (fun j => c α j ≠ 0)
    have hSnz_ne : S_nz.Nonempty := ⟨j₀, Finset.mem_filter.mpr ⟨hj₀, hcj₀⟩⟩
    let m' : ℕ := S_nz.max' hSnz_ne
    have hm'_mem : m' ∈ S_nz := Finset.max'_mem S_nz hSnz_ne
    have hm'_pos : 0 < m' := by
      have h1 : 1 ≤ m' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm'_mem).1).1
      omega
    have hcm'_ne : c α m' ≠ 0 := (Finset.mem_filter.mp hm'_mem).2
    have hm'_le : m' ≤ m α := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm'_mem).1).2
    have hP_prin : RudinRCA.Chapter10.IsPrincipalPart (P α) α := by
      refine ⟨m', c α, hm'_pos, hcm'_ne, fun z => ?_⟩
      dsimp only [P]
      symm
      apply Finset.sum_subset (Finset.Icc_subset_Icc_right hm'_le)
      intro j hj_big hj_not_small
      have hcj0 : c α j = 0 := by
        by_contra hne
        have hj_Snz : j ∈ S_nz := Finset.mem_filter.mpr ⟨hj_big, hne⟩
        have hj_le_m' : j ≤ m' := Finset.le_max' S_nz j hj_Snz
        have h1 : 1 ≤ j := (Finset.mem_Icc.mp hj_big).1
        exact hj_not_small (Finset.mem_Icc.mpr ⟨h1, hj_le_m'⟩)
      rw [hcj0, zero_mul]
    have hiso : RudinRCA.Chapter10.HasIsolatedSingularity f V α := by
      refine ⟨hV_open, hαV, ?_⟩
      intro z hz
      exact hf_holo_sdiff z ⟨(hVsdiff hz).1, fun h => (hVsdiff hz).2 h.1⟩
    exact ⟨V, hV_open, hαV, hVΩ, hiso, g, P α, hg_holo, hP_prin, heq⟩
  exact ⟨f, ⟨hΩ, hAeff_sub_A.trans hAΩ, hacc_eff, hf_holo_sdiff, hf_poles_eff⟩, hlocal_all⟩


/-! ## §13.11–13.12 — Simply Connected Regions, Normal Families, Riemann Mapping Core, and `log |f|` -/

/-- Explicit radial homeomorphism `ℂ ≃ₜ U` (`z ↦ z / (1 + ‖z‖)`, inverse `w ↦ w / (1 - ‖w‖)`),
used for the `Ω = ℂ` case of `13.11` and the `14.8` contrast remark (`ℂ ≃ₜ U` topologically,
though not conformally). -/
def planeHomeomorphUnitBall : ℂ ≃ₜ ball (0 : ℂ) 1 where
  toFun z := ⟨z / ((1 + ‖z‖ : ℝ) : ℂ), by
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 1 + ‖z‖)]
    exact (div_lt_one (by positivity)).mpr (by linarith)⟩
  invFun w := w.1 / ((1 - ‖w.1‖ : ℝ) : ℂ)
  left_inv z := by
    dsimp only
    have hpos : (0 : ℝ) < 1 + ‖z‖ := by positivity
    have hnorm : ‖z / ((1 + ‖z‖ : ℝ) : ℂ)‖ = ‖z‖ / (1 + ‖z‖) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    rw [hnorm]
    have hsub : (1 : ℝ) - ‖z‖ / (1 + ‖z‖) = 1 / (1 + ‖z‖) := by
      field_simp [hpos.ne']
      ring
    rw [hsub]
    push_cast
    have hc_ne : (1 : ℂ) + (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp [hc_ne]
  right_inv w := by
    apply Subtype.ext
    dsimp only
    have hw_lt : ‖w.1‖ < 1 := mem_ball_zero_iff.mp w.2
    have hpos : (0 : ℝ) < 1 - ‖w.1‖ := by linarith
    have hnorm : ‖w.1 / ((1 - ‖w.1‖ : ℝ) : ℂ)‖ = ‖w.1‖ / (1 - ‖w.1‖) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    rw [hnorm]
    have hadd : (1 : ℝ) + ‖w.1‖ / (1 - ‖w.1‖) = 1 / (1 - ‖w.1‖) := by
      field_simp [hpos.ne']
      ring
    rw [hadd]
    push_cast
    have hc_ne : (1 : ℂ) - (‖w.1‖ : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp [hc_ne]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_id.div
      (Complex.continuous_ofReal.comp (continuous_const.add continuous_norm)) ?_
    intro z
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity : (0 : ℝ) < 1 + ‖z‖))
  continuous_invFun := by
    refine continuous_subtype_val.div
      (Complex.continuous_ofReal.comp
        (continuous_const.sub (continuous_norm.comp continuous_subtype_val))) ?_
    intro w
    have hw_lt : ‖w.1‖ < 1 := mem_ball_zero_iff.mp w.2
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith : (0 : ℝ) < 1 - ‖w.1‖))

/-- **Montel's locally bounded normality theorem (RCA 14.6, also used in 14.8 / 13.11(j)→(a)):**
If `Ω ⊆ ℂ` is open and `f : ℕ → ℂ → ℂ` is a sequence in `H(Ω)` that is uniformly bounded on every
compact subset of `Ω`, then some subsequence `f ∘ φ` (`StrictMono φ`) converges uniformly on every
compact subset of `Ω` to a holomorphic limit `g ∈ H(Ω)`. -/
theorem montel_locally_bounded {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℕ → ℂ → ℂ} (hf : ∀ n, RudinRCA.Chapter10.HolomorphicOn (f n) Ω)
    (hbdd : ∀ K ⊆ Ω, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
      RudinRCA.Chapter10.HolomorphicOn g Ω ∧
      RudinRCA.Chapter10.ConvergesOnCompactSubsets (fun k => f (φ k)) g Ω := by
  by_cases hΩ_ne : Ω.Nonempty
  · classical
    have : Nonempty Ω := hΩ_ne.to_subtype
    obtain ⟨D, hD_count, hD_dense⟩ := TopologicalSpace.exists_countable_dense Ω
    obtain ⟨d, rfl⟩ := hD_count.exists_eq_range hD_dense.nonempty
    have hex_M : ∀ m : ℕ, ∃ M : ℝ, ∀ n : ℕ, f n (d m).1 ∈ closedBall (0 : ℂ) M := by
      intro m
      obtain ⟨M, hM⟩ := hbdd {(d m).1} (singleton_subset_iff.mpr (d m).2) isCompact_singleton
      exact ⟨M, fun n => by simpa [mem_closedBall_zero_iff] using hM n (d m).1 rfl⟩
    choose M hM using hex_M
    let PiD := ∀ m : ℕ, closedBall (0 : ℂ) (M m)
    have : ∀ m : ℕ, CompactSpace (closedBall (0 : ℂ) (M m)) :=
      fun m => isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) (M m))
    let seq : ℕ → PiD := fun n m => ⟨f n (d m).1, hM m n⟩
    obtain ⟨y, _, φ, hφ_mono, hφ_lim⟩ :=
      isCompact_univ.isSeqCompact (fun n => Set.mem_univ (seq n))
    have hd_lim : ∀ m : ℕ, Tendsto (fun k => f (φ k) (d m).1) atTop (𝓝 (y m).1) := by
      intro m
      exact (continuous_subtype_val.tendsto (y m)).comp ((tendsto_pi_nhds.mp hφ_lim) m)
    -- Local uniform Lipschitz bound on `ball z₀ r` for every `z₀ ∈ Ω`
    have hlocal_lip : ∀ z₀ ∈ Ω, ∃ (r L : ℝ), 0 < r ∧ 0 < L ∧ closedBall z₀ r ⊆ Ω ∧
        ∀ n : ℕ, ∀ u ∈ ball z₀ r, ∀ v ∈ ball z₀ r, ‖f n u - f n v‖ ≤ L * ‖u - v‖ := by
      intro z₀ hz₀
      obtain ⟨R, hR, hball_Ω⟩ := Metric.isOpen_iff.mp hΩ z₀ hz₀
      let r : ℝ := R / 3
      have hr : 0 < r := by positivity
      have hcb2_Ω : closedBall z₀ (2 * r) ⊆ Ω :=
        (closedBall_subset_ball (by dsimp [r]; linarith)).trans hball_Ω
      have hcb1_Ω : closedBall z₀ r ⊆ Ω :=
        (closedBall_subset_closedBall (by linarith)).trans hcb2_Ω
      obtain ⟨B₀, hB₀⟩ := hbdd (closedBall z₀ (2 * r)) hcb2_Ω (isCompact_closedBall z₀ (2 * r))
      let B : ℝ := max B₀ 0
      let L : ℝ := B / r + 1
      have hL_pos : 0 < L := by positivity
      refine ⟨r, L, hr, hL_pos, hcb1_Ω, ?_⟩
      intro n
      have hfn_diff : DifferentiableOn ℂ (f n) Ω :=
        (RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn hΩ).mp (hf n)
      have hderiv_le : ∀ u ∈ ball z₀ r, ‖deriv (f n) u‖ ≤ L := by
        intro u hu
        have hcb_u : closedBall u r ⊆ closedBall z₀ (2 * r) := by
          intro w hw
          rw [mem_closedBall] at hw ⊢
          rw [mem_ball] at hu
          linarith [dist_triangle w u z₀]
        have hdiff_cl : DiffContOnCl ℂ (f n) (ball u r) :=
          ⟨hfn_diff.mono (ball_subset_closedBall.trans (hcb_u.trans hcb2_Ω)),
           hfn_diff.continuousOn.mono
             (closure_ball_subset_closedBall.trans (hcb_u.trans hcb2_Ω))⟩
        have hca := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdiff_cl
          (fun w hw => (hB₀ n w (hcb_u (sphere_subset_closedBall hw))).trans (le_max_left B₀ 0))
        linarith
      intro u hu v hv
      exact (convex_ball z₀ r).norm_image_sub_le_of_norm_deriv_le
        (fun w hw => hf n w (ball_subset_closedBall.trans hcb1_Ω hw))
        hderiv_le hv hu
    -- Pointwise Cauchy and limit on `Ω`
    have hcauchy : ∀ z ∈ Ω, CauchySeq (fun k => f (φ k) z) := by
      intro z hz
      obtain ⟨r, L, hr, hL_pos, _, hlip⟩ := hlocal_lip z hz
      rw [Metric.cauchySeq_iff]
      intro ε hε
      let δ : ℝ := min (r / 2) (ε / (3 * L))
      have hδ_pos : 0 < δ := lt_min (by positivity) (by positivity)
      obtain ⟨_, hzm, ⟨m, rfl⟩⟩ := Metric.dense_iff.mp hD_dense ⟨z, hz⟩ δ hδ_pos
      have hdm_dist : ‖(d m).1 - z‖ < δ := by
        simpa [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using hzm
      have hdm_ball : (d m).1 ∈ ball z r := by
        rw [mem_ball, dist_eq_norm]
        exact hdm_dist.trans_le ((min_le_left _ _).trans (by linarith))
      have hz_ball : z ∈ ball z r := Metric.mem_ball_self hr
      obtain ⟨N, hN⟩ :=
        Metric.cauchySeq_iff.mp (hd_lim m).cauchySeq (ε / 3) (by positivity)
      refine ⟨N, fun j hj k hk => ?_⟩
      have h1 : dist (f (φ j) z) (f (φ j) (d m).1) < ε / 3 := by
        rw [dist_eq_norm, norm_sub_rev]
        calc
          ‖f (φ j) (d m).1 - f (φ j) z‖ ≤ L * ‖(d m).1 - z‖ := hlip (φ j) (d m).1 hdm_ball z hz_ball
          _ < L * (ε / (3 * L)) :=
            mul_lt_mul_of_pos_left (hdm_dist.trans_le (min_le_right _ _)) hL_pos
          _ = ε / 3 := by field_simp [hL_pos.ne']
      have h2 : dist (f (φ j) (d m).1) (f (φ k) (d m).1) < ε / 3 := hN j hj k hk
      have h3 : dist (f (φ k) (d m).1) (f (φ k) z) < ε / 3 := by
        rw [dist_eq_norm]
        calc
          ‖f (φ k) (d m).1 - f (φ k) z‖ ≤ L * ‖(d m).1 - z‖ := hlip (φ k) (d m).1 hdm_ball z hz_ball
          _ < L * (ε / (3 * L)) :=
            mul_lt_mul_of_pos_left (hdm_dist.trans_le (min_le_right _ _)) hL_pos
          _ = ε / 3 := by field_simp [hL_pos.ne']
      calc
        dist (f (φ j) z) (f (φ k) z)
            ≤ dist (f (φ j) z) (f (φ j) (d m).1) + dist (f (φ j) (d m).1) (f (φ k) (d m).1) +
                dist (f (φ k) (d m).1) (f (φ k) z) := dist_triangle4 _ _ _ _
        _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add h1 h2) h3
        _ = ε := by ring
    let g : ℂ → ℂ := fun z =>
      if hz : z ∈ Ω then Classical.choose (cauchySeq_tendsto_of_complete (hcauchy z hz)) else 0
    have hg_pt : ∀ z ∈ Ω, Tendsto (fun k => f (φ k) z) atTop (𝓝 (g z)) := by
      intro z hz
      simp only [g, hz, ↓reduceDIte]
      exact Classical.choose_spec (cauchySeq_tendsto_of_complete (hcauchy z hz))
    -- Uniform convergence on `closedBall z₀ (r / 2)` around each `z₀ ∈ Ω`
    have hlocal_unif : ∀ z₀ ∈ Ω, ∃ ρ > 0,
        TendstoUniformlyOn (fun k => f (φ k)) g atTop (ball z₀ ρ) := by
      intro z₀ hz₀
      obtain ⟨r, L, hr, hL_pos, hcb1_Ω, hlip⟩ := hlocal_lip z₀ hz₀
      let C := closedBall z₀ (r / 2)
      have hC_sub_ball : C ⊆ ball z₀ r := closedBall_subset_ball (by linarith)
      have hC_sub_Ω : C ⊆ Ω := hC_sub_ball.trans (ball_subset_closedBall.trans hcb1_Ω)
      have hg_lip : ∀ u ∈ C, ∀ v ∈ C, ‖g u - g v‖ ≤ L * ‖u - v‖ := by
        intro u hu v hv
        have hlim : Tendsto (fun k => ‖f (φ k) u - f (φ k) v‖) atTop (𝓝 ‖g u - g v‖) :=
          ((hg_pt u (hC_sub_Ω hu)).sub (hg_pt v (hC_sub_Ω hv))).norm
        exact le_of_tendsto hlim (Eventually.of_forall fun k =>
          hlip (φ k) u (hC_sub_ball hu) v (hC_sub_ball hv))
      have hunif_C : TendstoUniformlyOn (fun k => f (φ k)) g atTop C := by
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        let δ : ℝ := ε / (3 * L)
        have hδ : 0 < δ := by positivity
        obtain ⟨F, hF_cov⟩ := (isCompact_closedBall z₀ (r / 2)).elim_finite_subcover
          (fun w : C => ball w.1 δ) (fun _ => isOpen_ball)
          (fun w hw => Set.mem_iUnion.mpr ⟨⟨w, hw⟩, Metric.mem_ball_self hδ⟩)
        choose N_fn hN_fn using fun w : C =>
          Filter.eventually_atTop.mp
            (Metric.tendsto_nhds.mp (hg_pt w.1 (hC_sub_Ω w.2)) (ε / 3) (by positivity))
        filter_upwards [Filter.eventually_atTop.mpr
          ⟨F.sup N_fn, fun k hk w hwF => hN_fn w k ((Finset.le_sup hwF).trans hk)⟩] with k hk x hx
        obtain ⟨w, hwF, hxw⟩ := Set.mem_iUnion₂.mp (hF_cov hx)
        have hxw_lt : ‖x - w.1‖ < δ := by simpa [mem_ball, dist_eq_norm] using hxw
        have h1 : dist (g x) (g w.1) < ε / 3 := by
          rw [dist_eq_norm]
          calc
            ‖g x - g w.1‖ ≤ L * ‖x - w.1‖ := hg_lip x hx w.1 w.2
            _ < L * δ := mul_lt_mul_of_pos_left hxw_lt hL_pos
            _ = ε / 3 := by dsimp [δ]; field_simp [hL_pos.ne']
        have h2 : dist (g w.1) (f (φ k) w.1) < ε / 3 := by
          rw [dist_comm]
          exact hk w hwF
        have h3 : dist (f (φ k) w.1) (f (φ k) x) < ε / 3 := by
          rw [dist_eq_norm, norm_sub_rev]
          calc
            ‖f (φ k) x - f (φ k) w.1‖ ≤ L * ‖x - w.1‖ :=
              hlip (φ k) x (hC_sub_ball hx) w.1 (hC_sub_ball w.2)
            _ < L * δ := mul_lt_mul_of_pos_left hxw_lt hL_pos
            _ = ε / 3 := by dsimp [δ]; field_simp [hL_pos.ne']
        calc
          dist (g x) (f (φ k) x)
              ≤ dist (g x) (g w.1) + dist (g w.1) (f (φ k) w.1) +
                  dist (f (φ k) w.1) (f (φ k) x) := dist_triangle4 _ _ _ _
          _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add h1 h2) h3
          _ = ε := by ring
      exact ⟨r / 2, half_pos hr, hunif_C.mono ball_subset_closedBall⟩
    -- Upgrade to `ConvergesOnCompactSubsets` via finite ball subcover on any compact `K ⊆ Ω`
    have hconv : RudinRCA.Chapter10.ConvergesOnCompactSubsets (fun k => f (φ k)) g Ω := by
      intro K hKΩ hK
      choose ρ hρ_pos hρ_unif using fun z : K => hlocal_unif z.1 (hKΩ z.2)
      obtain ⟨F, hF_cov⟩ := hK.elim_finite_subcover
        (fun z : K => ball z.1 (ρ z)) (fun _ => isOpen_ball)
        (fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (hρ_pos ⟨z, hz⟩)⟩)
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      choose N_fn hN_fn using fun z : K =>
        Filter.eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp (hρ_unif z) ε hε)
      filter_upwards [Filter.eventually_atTop.mpr
        ⟨F.sup N_fn, fun k hk z hzF => hN_fn z k ((Finset.le_sup hzF).trans hk)⟩] with k hk x hx
      obtain ⟨z, hzF, hxz⟩ := Set.mem_iUnion₂.mp (hF_cov hx)
      exact hk z hzF x hxz
    have hg_holo : RudinRCA.Chapter10.HolomorphicOn g Ω :=
      (RudinRCA.Chapter10.holomorphicOn_limit_and_deriv hΩ (fun k => hf (φ k)) hconv).1
    exact ⟨φ, g, hφ_mono, hg_holo, hconv⟩
  · have hΩ_emp : Ω = ∅ := Set.not_nonempty_iff_eq_empty.mp hΩ_ne
    subst hΩ_emp
    refine ⟨id, 0, strictMono_id, fun _ hz => False.elim hz, ?_⟩
    intro K hK _
    have hK_emp : K = ∅ := subset_eq_empty hK rfl
    subst hK_emp
    simp [TendstoUniformlyOn]

/-- **Hurwitz injectivity theorem (used in RCA 14.8 / 13.11(j)→(a)):**
If `Ω ⊆ ℂ` is a region, `f : ℕ → ℂ → ℂ` is a sequence of injective holomorphic functions on `Ω`,
and `f` converges uniformly on compact subsets of `Ω` to `g`, then `g` is either constant on `Ω`
or injective on `Ω`. -/
theorem hurwitz_injOn_of_limit {Ω : Set ℂ} (hΩ : RudinRCA.Chapter10.IsRegion Ω)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ k, RudinRCA.Chapter10.HolomorphicOn (f k) Ω)
    (hinj : ∀ k, Set.InjOn (f k) Ω)
    (hlim : RudinRCA.Chapter10.ConvergesOnCompactSubsets f g Ω) :
    (∃ c : ℂ, ∀ z ∈ Ω, g z = c) ∨ Set.InjOn g Ω := by
  by_cases hconst : ∃ c : ℂ, ∀ z ∈ Ω, g z = c
  · exact Or.inl hconst
  · right
    have hg : RudinRCA.Chapter10.HolomorphicOn g Ω :=
      (RudinRCA.Chapter10.holomorphicOn_limit_and_deriv hΩ.1 hf hlim).1
    intro z₁ hz₁ z₂ hz₂ heq_g
    by_contra hne₁₂
    let w₀ : ℂ := g z₁
    let h : ℂ → ℂ := fun z => g z - w₀
    have hh : RudinRCA.Chapter10.HolomorphicOn h Ω :=
      fun z hz => (hg z hz).sub (differentiableAt_const w₀)
    have hhz₁ : h z₁ = 0 := sub_self (g z₁)
    have hhz₂ : h z₂ = 0 := by dsimp [h, w₀]; rw [← heq_g, sub_self]
    have hne_zero_Ω : ¬ Set.EqOn h 0 Ω := by
      intro hall
      exact hconst ⟨w₀, fun z hz => sub_eq_zero.mp (hall hz)⟩
    have hno_acc : ∀ a ∈ Ω, ¬ AccPt a (𝓟 (RudinRCA.Chapter10.zeroSet h Ω)) := by
      rcases RudinRCA.Chapter10.zeroSet_eq_or_no_accumulation hΩ hh with hall | hna
      · exfalso
        apply hne_zero_Ω
        intro z hz
        have hz0 : z ∈ RudinRCA.Chapter10.zeroSet h Ω := hall.symm ▸ hz
        exact hz0.2
      · exact hna
    -- Helper: around any zero `a ∈ Ω` of `h`, there is `R_a > 0` with `ball a R_a ⊆ Ω` and
    -- no other zeros of `h` in `ball a R_a \ {a}`
    have hiso_zero : ∀ a ∈ Ω, ∃ R_a > 0, ball a R_a ⊆ Ω ∧
        ∀ z ∈ ball a R_a, z ≠ a → h z ≠ 0 := by
      intro a ha
      have hnot_nhds : ¬ ∀ U ∈ 𝓝 a, ∃ y ∈ U ∩ RudinRCA.Chapter10.zeroSet h Ω, y ≠ a :=
        mt accPt_iff_nhds.mpr (hno_acc a ha)
      push Not at hnot_nhds
      obtain ⟨U, hU_nhds, hU_empty⟩ := hnot_nhds
      obtain ⟨r₁, hr₁, hr₁_Ω⟩ := Metric.isOpen_iff.mp hΩ.1 a ha
      obtain ⟨r₂, hr₂, hr₂_U⟩ := Metric.mem_nhds_iff.mp hU_nhds
      refine ⟨min r₁ r₂, lt_min hr₁ hr₂,
        (ball_subset_ball (min_le_left _ _)).trans hr₁_Ω, ?_⟩
      intro z hz hza hhz
      exact hza (hU_empty z ⟨hr₂_U (ball_subset_ball (min_le_right _ _) hz),
        ⟨hr₁_Ω (ball_subset_ball (min_le_left _ _) hz), hhz⟩⟩)
    obtain ⟨R₁, hR₁, hball₁_Ω, hiso₁⟩ := hiso_zero z₁ hz₁
    obtain ⟨R₂, hR₂, hball₂_Ω, hiso₂⟩ := hiso_zero z₂ hz₂
    have hdist_pos : 0 < ‖z₁ - z₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne₁₂)
    let R : ℝ := min (min R₁ R₂) (‖z₁ - z₂‖ / 3)
    have hR : 0 < R := lt_min (lt_min hR₁ hR₂) (by positivity)
    let r : ℝ := R / 2
    have hr : 0 < r := half_pos hR
    have hr_lt_R : r < R := half_lt_self hR
    -- Rouché zero-existence helper on `ball a R` for `a ∈ {z₁, z₂}`
    have hrouche_ball : ∀ (a : ℂ), a ∈ Ω → h a = 0 → ball a R ⊆ Ω →
        (∀ z ∈ ball a R, z ≠ a → h z ≠ 0) →
        ∀ᶠ k in atTop, ∃ u ∈ ball a R, f k u = w₀ := by
      intro a _ hha hball_a hiso_a
      let D := ball a R
      have hD_reg : RudinRCA.Chapter10.IsRegion D := RudinRCA.Chapter10.disc_isRegion a hR
      let γ := RudinRCA.Chapter10.positivelyOrientedCircle a r hr
      have hγ_cl : γ.IsClosed := RudinRCA.Chapter10.positivelyOrientedCircle_isClosed a hr
      have hγ_tr_eq : γ.trace = sphere a r :=
        RudinRCA.Chapter10.positivelyOrientedCircle_trace a hr
      have hγ_sub_D : γ.trace ⊆ D := by
        rw [hγ_tr_eq]
        exact sphere_subset_closedBall.trans (closedBall_subset_ball hr_lt_R)
      have hext_γ : ∀ α, α ∉ D → RudinRCA.Chapter10.Ind γ.toBookCurve α = 0 := by
        intro α hα
        rw [mem_ball, dist_eq_norm, not_lt] at hα
        exact RudinRCA.Chapter10.Ind_positivelyOrientedCircle_outside hr (lt_of_lt_of_le hr_lt_R hα)
      have h01_γ : ∀ α ∈ D, α ∉ γ.trace →
          RudinRCA.Chapter10.Ind γ.toBookCurve α = 0 ∨
          RudinRCA.Chapter10.Ind γ.toBookCurve α = 1 := by
        intro α _ hα_not
        rw [hγ_tr_eq, mem_sphere, dist_eq_norm] at hα_not
        rcases lt_trichotomy ‖α - a‖ r with hlt | heq | hgt
        · exact Or.inr (RudinRCA.Chapter10.Ind_positivelyOrientedCircle_inside hr
            (by simpa [RudinRCA.Chapter10.disc, mem_ball, dist_eq_norm] using hlt))
        · exact False.elim (hα_not heq)
        · exact Or.inl (RudinRCA.Chapter10.Ind_positivelyOrientedCircle_outside hr hgt)
      -- Positive minimum of `‖h‖` on `sphere a r`
      have hsph_ne : (sphere a r).Nonempty :=
        ⟨a + (r : ℂ), by simp [abs_of_pos hr]⟩
      have hh_cont_sph : ContinuousOn (fun z => ‖h z‖) (sphere a r) :=
        ((RudinRCA.Chapter10.continuousOn_of_holomorphicOn hh).mono
          (hγ_tr_eq ▸ hγ_sub_D.trans hball_a)).norm
      obtain ⟨z_min, hz_min_sph, hz_min⟩ :=
        (isCompact_sphere a r).exists_isMinOn hsph_ne hh_cont_sph
      have hz_min_ne_a : z_min ≠ a := by
        intro heq
        subst heq
        rw [mem_sphere, dist_self] at hz_min_sph
        linarith
      have hm_pos : 0 < ‖h z_min‖ := norm_pos_iff.mpr
        (hiso_a z_min (hγ_sub_D (hγ_tr_eq.symm ▸ hz_min_sph)) hz_min_ne_a)
      have hunif_sph := Metric.tendstoUniformlyOn_iff.mp
        (hlim (sphere a r) (hγ_tr_eq ▸ hγ_sub_D.trans hball_a) (isCompact_sphere a r))
        ‖h z_min‖ hm_pos
      filter_upwards [hunif_sph] with k hk
      have hstrict : ∀ z ∈ γ.trace, ‖h z - (f k z - w₀)‖ < ‖h z‖ := by
        intro z hz_tr
        have hz_sph : z ∈ sphere a r := hγ_tr_eq ▸ hz_tr
        have hlt : ‖g z - f k z‖ < ‖h z_min‖ := by
          simpa [dist_eq_norm] using hk z hz_sph
        have hle : ‖h z_min‖ ≤ ‖h z‖ := hz_min hz_sph
        have heq_diff : h z - (f k z - w₀) = g z - f k z := by dsimp [h]; ring
        rw [heq_diff]
        exact lt_of_lt_of_le hlt hle
      obtain ⟨_, hfin_h, hfin_fk, hsum_eq⟩ :=
        RudinRCA.Chapter10.theorem10_43_rouche hD_reg hγ_cl hγ_sub_D hext_γ h01_γ
          (fun z hz => hh z (hball_a hz))
          (fun z hz => (hf k z (hball_a hz)).sub (differentiableAt_const w₀))
          hstrict
      have hne_D : ¬ Set.EqOn h 0 D := by
        intro hall
        have hz_D : z_min ∈ D := hγ_sub_D (hγ_tr_eq.symm ▸ hz_min_sph)
        exact (norm_pos_iff.mp hm_pos) (hall hz_D)
      have ha_D : a ∈ D := Metric.mem_ball_self hR
      obtain ⟨hord_pos, _⟩ :=
        RudinRCA.Chapter10.zeroOrder_spec hD_reg (fun z hz => hh z (hball_a hz)) hne_D ha_D hha
      have ha_mem_set : a ∈ RudinRCA.Chapter10.zeroSet h D ∩
          RudinRCA.Chapter10.indexOneSet γ D := by
        refine ⟨⟨ha_D, hha⟩, ha_D, ?_, ?_⟩
        · rw [hγ_tr_eq, mem_sphere, dist_self]
          exact hr.ne
        · exact RudinRCA.Chapter10.Ind_positivelyOrientedCircle_inside hr
            (Metric.mem_ball_self hr)
      have ha_mem_fin : a ∈ hfin_h.toFinset := hfin_h.mem_toFinset.mpr ha_mem_set
      have hsum_pos : 0 < ∑ x ∈ hfin_fk.toFinset,
          RudinRCA.Chapter10.zeroOrder (f k - fun _ => w₀) D x := by
        rw [← hsum_eq]
        exact lt_of_lt_of_le hord_pos
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha_mem_fin)
      have hfk_ne : hfin_fk.toFinset.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.sum_empty] at hsum_pos
        exact lt_irrefl 0 hsum_pos
      obtain ⟨u, hu_fin⟩ := hfk_ne
      have hu_mem := hfin_fk.mem_toFinset.mp hu_fin
      exact ⟨u, hu_mem.1.1, sub_eq_zero.mp hu_mem.1.2⟩
    have hball₁_sub : ball z₁ R ⊆ ball z₁ R₁ :=
      ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
    have hball₂_sub : ball z₂ R ⊆ ball z₂ R₂ :=
      ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _))
    have hev₁ := hrouche_ball z₁ hz₁ hhz₁ (hball₁_sub.trans hball₁_Ω)
      (fun z hz => hiso₁ z (hball₁_sub hz))
    have hev₂ := hrouche_ball z₂ hz₂ hhz₂ (hball₂_sub.trans hball₂_Ω)
      (fun z hz => hiso₂ z (hball₂_sub hz))
    obtain ⟨k, ⟨u₁, hu₁_ball, hfk₁⟩, ⟨u₂, hu₂_ball, hfk₂⟩⟩ := (hev₁.and hev₂).exists
    have hu_eq : u₁ = u₂ := hinj k
      (hball₁_Ω (hball₁_sub hu₁_ball))
      (hball₂_Ω (hball₂_sub hu₂_ball))
      (hfk₁.trans hfk₂.symm)
    subst hu_eq
    have hd₁ : ‖u₁ - z₁‖ < R := by simpa [mem_ball, dist_eq_norm] using hu₁_ball
    have hd₂ : ‖u₁ - z₂‖ < R := by simpa [mem_ball, dist_eq_norm] using hu₂_ball
    have hR_le : R ≤ ‖z₁ - z₂‖ / 3 := min_le_right _ _
    have htri : ‖z₁ - z₂‖ ≤ ‖u₁ - z₁‖ + ‖u₁ - z₂‖ := by
      calc
        ‖z₁ - z₂‖ = ‖(z₁ - u₁) + (u₁ - z₂)‖ := by congr 1; ring
        _ ≤ ‖z₁ - u₁‖ + ‖u₁ - z₂‖ := norm_add_le _ _
        _ = ‖u₁ - z₁‖ + ‖u₁ - z₂‖ := by rw [norm_sub_rev]
    linarith

/-- **Riemann Mapping & Extremal Derivative Core (RCA 14.8 & 14.9, also closing 13.11(j)→(a)):**
Let `Ω ⊆ ℂ` be a proper region (`Ω ≠ Set.univ`) and `z₀ ∈ Ω`. Assume every zero-free `f ∈ H(Ω)`
admits a holomorphic square root on `Ω`. Then there exists a holomorphic bijection
`h : Ω → ball (0 : ℂ) 1` satisfying `h z₀ = 0`, `0 < ‖deriv h z₀‖` (in fact `deriv h z₀` is real
and strictly positive), and the extremal property of Remark 14.9: for **every** `f ∈ H(Ω)` mapping
`Ω` into `ball (0 : ℂ) 1` (injective or not), `‖deriv f z₀‖ ≤ ‖deriv h z₀‖`, with equality if and
only if `∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ Ω, f z = c * h z`. -/
theorem riemann_mapping_of_holomorphic_sqrt {Ω : Set ℂ}
    (hΩ : RudinRCA.Chapter10.IsRegion Ω) (hproper : Ω ≠ Set.univ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (hsqrt : ∀ f : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn f Ω →
      (∀ z ∈ Ω, f z ≠ 0) →
      ∃ φ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn φ Ω ∧ ∀ z ∈ Ω, φ z ^ 2 = f z) :
    ∃ h : ℂ → ℂ,
      RudinRCA.Chapter10.HolomorphicOn h Ω ∧
      BijOn h Ω (ball (0 : ℂ) 1) ∧
      h z₀ = 0 ∧
      0 < (deriv h z₀).re ∧ (deriv h z₀).im = 0 ∧
      0 < ‖deriv h z₀‖ ∧
      (∀ f : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn f Ω → MapsTo f Ω (ball (0 : ℂ) 1) →
        ‖deriv f z₀‖ ≤ ‖deriv h z₀‖ ∧
        (‖deriv f z₀‖ = ‖deriv h z₀‖ ↔ ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ Ω, f z = c * h z)) := by
  let Fam : Set (ℂ → ℂ) :=
    {ψ : ℂ → ℂ | RudinRCA.Chapter10.HolomorphicOn ψ Ω ∧
      Set.InjOn ψ Ω ∧ MapsTo ψ Ω (ball (0 : ℂ) 1)}
  -- Helper: composing `ψ ∈ Fam` with disk automorphism `Chapter12.phi α` (`α ∈ ball 0 1`) stays in `Fam`
  have hcomp_phi : ∀ {ψ : ℂ → ℂ} {α : ℂ}, ψ ∈ Fam → α ∈ ball (0 : ℂ) 1 →
      (fun z => RudinRCA.Chapter12.phi α (ψ z)) ∈ Fam := by
    intro ψ α hψ hα
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      have hden := RudinRCA.Chapter12.phi_denom_ne_zero hα (ball_subset_closedBall (hψ.2.2 hz))
      exact ((RudinRCA.Chapter12.hasDerivAt_phi hden).differentiableAt.comp z (hψ.1 z hz))
    · intro z₁ hz₁ z₂ hz₂ heq
      have hbij := (RudinRCA.Chapter12.theorem12_4 hα).2.2.2.1
      exact hψ.2.1 hz₁ hz₂ (hbij.injOn (hψ.2.2 hz₁) (hψ.2.2 hz₂) heq)
    · intro z hz
      exact RudinRCA.Chapter12.mapsTo_phi_ball hα (hψ.2.2 hz)
  -- Step 1: `Fam` is nonempty
  obtain ⟨w₀, hw₀_not⟩ : ∃ w₀ : ℂ, w₀ ∉ Ω := by
    by_contra hall
    push Not at hall
    exact hproper (eq_univ_of_forall hall)
  obtain ⟨φ_sq, hφ_holo, hφ_sq⟩ := hsqrt (fun z => z - w₀)
    (fun z _ => differentiableAt_id.sub (differentiableAt_const w₀))
    (fun z hz => sub_ne_zero.mpr (fun heq => hw₀_not (heq ▸ hz)))
  have hφ_inj : Set.InjOn φ_sq Ω := by
    intro z₁ hz₁ z₂ hz₂ heq
    have h1 := hφ_sq z₁ hz₁
    have h2 := hφ_sq z₂ hz₂
    rw [heq] at h1
    linear_combination h2 - h1
  have hφ_open : IsOpen (φ_sq '' Ω) :=
    (RudinRCA.Chapter10.theorem10_33.1 hΩ.1 hφ_holo hφ_inj).2.1
  let a₀ : ℂ := φ_sq z₀
  obtain ⟨r₀, hr₀, hball_φ⟩ := Metric.isOpen_iff.mp hφ_open a₀ ⟨z₀, hz₀, rfl⟩
  have hdisj_neg : ∀ z ∈ Ω, r₀ ≤ ‖φ_sq z + a₀‖ := by
    intro z hz
    by_contra hlt
    push Not at hlt
    have hmem_ball : -φ_sq z ∈ ball a₀ r₀ := by
      rw [mem_ball, dist_eq_norm]
      have heq_n : ‖-φ_sq z - a₀‖ = ‖φ_sq z + a₀‖ := by
        rw [← norm_neg]; congr 1; ring
      rwa [heq_n]
    obtain ⟨z', hz', hφz'⟩ := hball_φ hmem_ball
    have hsq_eq : z' - w₀ = z - w₀ := by
      calc
        z' - w₀ = φ_sq z' ^ 2 := (hφ_sq z' hz').symm
        _ = (-φ_sq z) ^ 2 := by rw [hφz']
        _ = φ_sq z ^ 2 := neg_sq _
        _ = z - w₀ := hφ_sq z hz
    have hzz' : z' = z := by linear_combination hsq_eq
    subst hzz'
    have hφ0 : φ_sq z' = 0 := by linear_combination hφz' / 2
    have hzw₀ : z' - w₀ = 0 := by rw [← hφ_sq z' hz', hφ0, sq, mul_zero]
    exact hw₀_not ((sub_eq_zero.mp hzw₀) ▸ hz')
  let ψ₀ : ℂ → ℂ := fun z => ((r₀ / 2 : ℝ) : ℂ) / (φ_sq z + a₀)
  have hψ₀_Fam : ψ₀ ∈ Fam := by
    have hden_ne : ∀ z ∈ Ω, φ_sq z + a₀ ≠ 0 :=
      fun z hz h0 => by have := hdisj_neg z hz; rw [h0, norm_zero] at this; linarith
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact (differentiableAt_const _).div
        ((hφ_holo z hz).add (differentiableAt_const a₀)) (hden_ne z hz)
    · intro z₁ hz₁ z₂ hz₂ heq
      have hr_ne : ((r₀ / 2 : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (half_pos hr₀).ne'
      have h1 := hden_ne z₁ hz₁
      have h2 := hden_ne z₂ hz₂
      have heq_den : φ_sq z₁ + a₀ = φ_sq z₂ + a₀ := by
        rw [div_eq_div_iff h1 h2] at heq
        exact mul_left_cancel₀ hr_ne heq.symm
      exact hφ_inj hz₁ hz₂ (add_right_cancel heq_den)
    · intro z hz
      rw [mem_ball_zero_iff]
      dsimp only [ψ₀]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr₀)]
      calc
        (r₀ / 2) / ‖φ_sq z + a₀‖ ≤ (r₀ / 2) / r₀ :=
          div_le_div_of_nonneg_left (half_pos hr₀).le hr₀ (hdisj_neg z hz)
        _ = 1 / 2 := by field_simp [hr₀.ne']
        _ < 1 := by norm_num
  -- Step 2: Uniform derivative bound at `z₀` and maximizing sequence in `Fam`
  obtain ⟨δ₀, hδ₀, hball_z₀⟩ := Metric.isOpen_iff.mp hΩ.1 z₀ hz₀
  let r_c : ℝ := δ₀ / 2
  have hr_c : 0 < r_c := half_pos hδ₀
  have hcb_z₀ : closedBall z₀ r_c ⊆ Ω :=
    (closedBall_subset_ball (half_lt_self hδ₀)).trans hball_z₀
  have hderiv_bdd : ∀ f : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn f Ω →
      MapsTo f Ω (ball (0 : ℂ) 1) → ‖deriv f z₀‖ ≤ 1 / r_c := by
    intro f hf hmaps
    have hf_diff : DifferentiableOn ℂ f Ω :=
      (RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn hΩ.1).mp hf
    have hdiff_cl : DiffContOnCl ℂ f (ball z₀ r_c) :=
      ⟨hf_diff.mono (ball_subset_closedBall.trans hcb_z₀),
       hf_diff.continuousOn.mono (closure_ball_subset_closedBall.trans hcb_z₀)⟩
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr_c hdiff_cl
      (fun w hw => (mem_ball_zero_iff.mp (hmaps (hcb_z₀ (sphere_subset_closedBall hw)))).le)
  let S_deriv : Set ℝ := (fun ψ => ‖deriv ψ z₀‖) '' Fam
  have hS_ne : S_deriv.Nonempty := ⟨‖deriv ψ₀ z₀‖, ψ₀, hψ₀_Fam, rfl⟩
  have hS_bdd : BddAbove S_deriv := by
    refine ⟨1 / r_c, ?_⟩
    rintro _ ⟨ψ, hψ, rfl⟩
    exact hderiv_bdd ψ hψ.1 hψ.2.2
  let η : ℝ := sSup S_deriv
  have hψ₀_deriv_pos : 0 < ‖deriv ψ₀ z₀‖ :=
    norm_pos_iff.mpr ((RudinRCA.Chapter10.theorem10_33.1 hΩ.1 hψ₀_Fam.1 hψ₀_Fam.2.1).1 z₀ hz₀)
  have hη_pos : 0 < η := lt_of_lt_of_le hψ₀_deriv_pos (le_csSup hS_bdd ⟨ψ₀, hψ₀_Fam, rfl⟩)
  have hex_seq : ∀ n : ℕ, ∃ ψ ∈ Fam, η - 1 / ((n : ℝ) + 1) < ‖deriv ψ z₀‖ := by
    intro n
    have hlt : η - 1 / ((n : ℝ) + 1) < η := sub_lt_self η (by positivity)
    obtain ⟨y, ⟨ψ, hψ, rfl⟩, hy⟩ := exists_lt_of_lt_csSup hS_ne hlt
    exact ⟨ψ, hψ, hy⟩
  choose ψ_seq hψ_seq_Fam hψ_seq_gt using hex_seq
  obtain ⟨φ_sub, h₀, hφ_mono, hh₀_holo, hh₀_conv⟩ := montel_locally_bounded hΩ.1
    (fun n => (hψ_seq_Fam n).1)
    (fun K hKΩ _ => ⟨1, fun n z hzK =>
      (mem_ball_zero_iff.mp ((hψ_seq_Fam n).2.2 (hKΩ hzK))).le⟩)
  -- `deriv (ψ_seq (φ_sub k)) z₀ → deriv h₀ z₀`, so `‖deriv h₀ z₀‖ = η > 0`
  have hderiv_conv := (RudinRCA.Chapter10.holomorphicOn_limit_and_deriv hΩ.1
    (fun k => (hψ_seq_Fam (φ_sub k)).1) hh₀_conv).2
  have hderiv_pt : Tendsto (fun k => ‖deriv (ψ_seq (φ_sub k)) z₀‖) atTop (𝓝 ‖deriv h₀ z₀‖) := by
    have hunif := hderiv_conv {z₀} (singleton_subset_iff.mpr hz₀) isCompact_singleton
    exact (tendstoUniformlyOn_singleton_iff_tendsto.mp hunif).norm
  have hη_le : η ≤ ‖deriv h₀ z₀‖ := by
    have hlow : Tendsto (fun k : ℕ => η - 1 / ((φ_sub k : ℝ) + 1)) atTop (𝓝 (η - 0)) := by
      refine tendsto_const_nhds.sub ?_
      exact (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ_mono.tendsto_atTop)
    rw [sub_zero] at hlow
    exact le_of_tendsto_of_tendsto hlow hderiv_pt
      (Eventually.of_forall fun k => (hψ_seq_gt (φ_sub k)).le)
  have hh₀_le_η : ‖deriv h₀ z₀‖ ≤ η :=
    le_of_tendsto hderiv_pt (Eventually.of_forall fun k =>
      le_csSup hS_bdd ⟨ψ_seq (φ_sub k), hψ_seq_Fam (φ_sub k), rfl⟩)
  have hh₀_deriv_norm : ‖deriv h₀ z₀‖ = η := le_antisymm hh₀_le_η hη_le
  -- `h₀` is nonconstant since `‖deriv h₀ z₀‖ = η > 0`, hence injective by Hurwitz!
  have hh₀_nonconst : ¬ ∃ c : ℂ, ∀ z ∈ Ω, h₀ z = c := by
    rintro ⟨c, hc⟩
    have hev : h₀ =ᶠ[𝓝 z₀] fun _ => c := by
      filter_upwards [hΩ.1.mem_nhds hz₀] with z hz
      exact hc z hz
    have hd0 : deriv h₀ z₀ = 0 := hev.deriv_eq.trans (deriv_const z₀ c)
    rw [hd0, norm_zero] at hh₀_deriv_norm
    linarith
  have hh₀_inj : Set.InjOn h₀ Ω :=
    (hurwitz_injOn_of_limit hΩ (fun k => (hψ_seq_Fam (φ_sub k)).1)
      (fun k => (hψ_seq_Fam (φ_sub k)).2.1) hh₀_conv).resolve_left hh₀_nonconst
  -- `h₀ '' Ω` is open and `‖h₀ z‖ ≤ 1` on `Ω`, so `MapsTo h₀ Ω (ball 0 1)`
  have hh₀_le1 : ∀ z ∈ Ω, ‖h₀ z‖ ≤ 1 := by
    intro z hz
    have hpt : Tendsto (fun k => ‖ψ_seq (φ_sub k) z‖) atTop (𝓝 ‖h₀ z‖) :=
      (tendstoUniformlyOn_singleton_iff_tendsto.mp
        (hh₀_conv {z} (singleton_subset_iff.mpr hz) isCompact_singleton)).norm
    exact le_of_tendsto hpt (Eventually.of_forall fun k =>
      (mem_ball_zero_iff.mp ((hψ_seq_Fam (φ_sub k)).2.2 hz)).le)
  have hh₀_open : IsOpen (h₀ '' Ω) :=
    (RudinRCA.Chapter10.theorem10_33.1 hΩ.1 hh₀_holo hh₀_inj).2.1
  have hh₀_maps : MapsTo h₀ Ω (ball (0 : ℂ) 1) := by
    intro z hz
    rw [mem_ball_zero_iff]
    by_contra hge1
    have heq1 : ‖h₀ z‖ = 1 := le_antisymm (hh₀_le1 z hz) (not_lt.mp hge1)
    obtain ⟨ε, hε, hball_img⟩ := Metric.isOpen_iff.mp hh₀_open (h₀ z) ⟨z, hz, rfl⟩
    have hhz_ne : h₀ z ≠ 0 := fun h0 => by rw [h0, norm_zero] at heq1; norm_num at heq1
    let w_out : ℂ := ((1 + ε / 2 : ℝ) : ℂ) * h₀ z
    have hw_in_ball : w_out ∈ ball (h₀ z) ε := by
      rw [mem_ball, dist_eq_norm]
      have heq_sub : w_out - h₀ z = ((ε / 2 : ℝ) : ℂ) * h₀ z := by
        dsimp [w_out]; push_cast; ring
      rw [heq_sub, norm_mul, heq1, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      linarith
    obtain ⟨z', hz', hfz'⟩ := hball_img hw_in_ball
    have hw_norm : ‖w_out‖ = 1 + ε / 2 := by
      dsimp [w_out]
      rw [norm_mul, heq1, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    have hle1 := hh₀_le1 z' hz'
    rw [hfz', hw_norm] at hle1
    linarith
  have hh₀_Fam : h₀ ∈ Fam := ⟨hh₀_holo, hh₀_inj, hh₀_maps⟩
  -- Normalize phase at `z₀` so `deriv h z₀ = (η : ℂ) > 0`
  have hdh₀_ne : deriv h₀ z₀ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hh₀_deriv_norm; linarith
  let rot : ℂ := (η : ℂ) / deriv h₀ z₀
  have hrot_norm : ‖rot‖ = 1 := by
    dsimp [rot]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη_pos,
      hh₀_deriv_norm, div_self hη_pos.ne']
  have hrot_ne : rot ≠ 0 := fun h0 => by rw [h0, norm_zero] at hrot_norm; norm_num at hrot_norm
  let h : ℂ → ℂ := fun z => rot * h₀ z
  have hh_Fam : h ∈ Fam := by
    refine ⟨fun z hz => (hh₀_holo z hz).const_mul rot, ?_, ?_⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      exact hh₀_inj hz₁ hz₂ (mul_left_cancel₀ hrot_ne heq)
    · intro z hz
      rw [mem_ball_zero_iff]
      dsimp [h]
      rw [norm_mul, hrot_norm, one_mul]
      exact mem_ball_zero_iff.mp (hh₀_maps hz)
  have hdh_eq : deriv h z₀ = (η : ℂ) := by
    have hd : HasDerivAt h (rot * deriv h₀ z₀) z₀ :=
      (hh₀_holo z₀ hz₀).hasDerivAt.const_mul rot
    rw [hd.deriv]
    dsimp [rot]
    exact div_mul_cancel₀ (η : ℂ) hdh₀_ne
  have hh_deriv_norm : ‖deriv h z₀‖ = η := by
    rw [hdh_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη_pos]
  -- `h z₀ = 0` by maximality of `η` under `Chapter12.phi (h z₀)`
  have hhz₀ : h z₀ = 0 := by
    by_contra hne0
    let α := h z₀
    have hα_ball : α ∈ ball (0 : ℂ) 1 := hh_Fam.2.2 hz₀
    have hα_lt1 : ‖α‖ < 1 := mem_ball_zero_iff.mp hα_ball
    have hα_pos : 0 < ‖α‖ := norm_pos_iff.mpr hne0
    let h₁ : ℂ → ℂ := fun z => RudinRCA.Chapter12.phi α (h z)
    have hh₁_Fam : h₁ ∈ Fam := hcomp_phi hh_Fam hα_ball
    have hd_phi := (RudinRCA.Chapter12.theorem12_4 hα_ball).2.2.2.2.2.2
    have hden_α := RudinRCA.Chapter12.phi_denom_ne_zero hα_ball (ball_subset_closedBall hα_ball)
    have hd_h₁ : HasDerivAt h₁ (deriv (RudinRCA.Chapter12.phi α) α * deriv h z₀) z₀ := by
      have hd1 := (RudinRCA.Chapter12.hasDerivAt_phi hden_α)
      rw [← hd1.deriv] at hd1
      exact hd1.comp z₀ (hh_Fam.1 z₀ hz₀).hasDerivAt
    have hle_η : ‖deriv h₁ z₀‖ ≤ η := le_csSup hS_bdd ⟨h₁, hh₁_Fam, rfl⟩
    rw [hd_h₁.deriv, hd_phi, norm_mul, hh_deriv_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (by nlinarith : 0 < 1 - ‖α‖ ^ 2))] at hle_η
    have hpos_den : 0 < 1 - ‖α‖ ^ 2 := by nlinarith
    have hmul_le : η ≤ (1 - ‖α‖ ^ 2) * η := by
      have := mul_le_mul_of_nonneg_left hle_η hpos_den.le
      rwa [← mul_assoc, mul_inv_cancel₀ hpos_den.ne', one_mul] at this
    have hsq_pos : 0 < ‖α‖ ^ 2 * η := mul_pos (sq_pos_of_pos hα_pos) hη_pos
    nlinarith
  -- Step 3: Koebe square-root surjectivity `SurjOn h Ω (ball 0 1)`
  have hh_surj : SurjOn h Ω (ball (0 : ℂ) 1) := by
    intro α hα_ball
    by_contra hα_miss
    have hα_ne0 : α ≠ 0 := by
      rintro rfl
      exact hα_miss ⟨z₀, hz₀, hhz₀⟩
    let u : ℂ → ℂ := fun z => RudinRCA.Chapter12.phi α (h z)
    have hu_Fam : u ∈ Fam := hcomp_phi hh_Fam hα_ball
    have hu_nz : ∀ z ∈ Ω, u z ≠ 0 := by
      intro z hz hu0
      have hbij_α := (RudinRCA.Chapter12.theorem12_4 hα_ball).2.2.2.1
      have heq_α : h z = α := hbij_α.injOn (hh_Fam.2.2 hz) hα_ball
        (hu0.trans (RudinRCA.Chapter12.phi_self α).symm)
      exact hα_miss ⟨z, hz, heq_α⟩
    obtain ⟨g_sq, hg_holo, hg_sq⟩ := hsqrt u hu_Fam.1 hu_nz
    have hg_maps : MapsTo g_sq Ω (ball (0 : ℂ) 1) := by
      intro z hz
      rw [mem_ball_zero_iff]
      have hsq_lt : ‖g_sq z‖ ^ 2 < 1 := by
        rw [← norm_pow, hg_sq z hz]
        exact mem_ball_zero_iff.mp (hu_Fam.2.2 hz)
      by_contra hge1
      have h1 : 1 ≤ ‖g_sq z‖ := not_lt.mp hge1
      nlinarith
    have hg_inj : Set.InjOn g_sq Ω := by
      intro z₁ hz₁ z₂ hz₂ heq
      apply hu_Fam.2.1 hz₁ hz₂
      rw [← hg_sq z₁ hz₁, ← hg_sq z₂ hz₂, heq]
    have hg_Fam : g_sq ∈ Fam := ⟨hg_holo, hg_inj, hg_maps⟩
    let β : ℂ := g_sq z₀
    have hβ_ball : β ∈ ball (0 : ℂ) 1 := hg_maps hz₀
    have hβ_sq : β ^ 2 = -α := by
      calc
        β ^ 2 = u z₀ := hg_sq z₀ hz₀
        _ = RudinRCA.Chapter12.phi α 0 := by dsimp [u]; rw [hhz₀]
        _ = -α := RudinRCA.Chapter12.phi_zero α
    let s : ℝ := ‖β‖
    have hs_sq : s ^ 2 = ‖α‖ := by
      dsimp [s]
      rw [← norm_pow, hβ_sq, norm_neg]
    have hs_pos : 0 < s := by
      have hα_pos : 0 < ‖α‖ := norm_pos_iff.mpr hα_ne0
      by_contra hle0
      have hs0 : s = 0 := le_antisymm (not_lt.mp hle0) (norm_nonneg β)
      rw [hs0] at hs_sq
      linarith
    have hs_lt1 : s < 1 := mem_ball_zero_iff.mp hβ_ball
    let ψ_k : ℂ → ℂ := fun z => RudinRCA.Chapter12.phi β (g_sq z)
    have hψ_k_Fam : ψ_k ∈ Fam := hcomp_phi hg_Fam hβ_ball
    -- Differentiate `g_sq(z)^2 = phi α (h z)` and `ψ_k(z) = phi β (g_sq z)` at `z₀`
    have hd_gsq : HasDerivAt (fun z => g_sq z ^ 2) (2 * β * deriv g_sq z₀) z₀ :=
      ((hg_holo z₀ hz₀).hasDerivAt.pow 2).congr_deriv (by dsimp [β]; ring)
    have hev_gsq : (fun z => g_sq z ^ 2) =ᶠ[𝓝 z₀] u := by
      filter_upwards [hΩ.1.mem_nhds hz₀] with z hz
      exact hg_sq z hz
    have hd_u : HasDerivAt u (((1 - ‖α‖ ^ 2 : ℝ) : ℂ) * deriv h z₀) z₀ := by
      have hden0 : 1 - star α * h z₀ ≠ 0 := by rw [hhz₀]; simp
      have hd_phi0 := (RudinRCA.Chapter12.hasDerivAt_phi hden0).comp z₀ (hh_Fam.1 z₀ hz₀).hasDerivAt
      refine hd_phi0.congr_deriv ?_
      rw [hhz₀, mul_zero, sub_zero, one_pow, div_one]
    have heq_deriv1 : 2 * β * deriv g_sq z₀ = ((1 - ‖α‖ ^ 2 : ℝ) : ℂ) * deriv h z₀ :=
      (hd_gsq.congr_of_eventuallyEq hev_gsq.symm).unique hd_u |> Eq.symm |> Eq.symm
    have hd_ψk : HasDerivAt ψ_k ((((1 - s ^ 2)⁻¹ : ℝ) : ℂ) * deriv g_sq z₀) z₀ := by
      have hden_β := RudinRCA.Chapter12.phi_denom_ne_zero hβ_ball (ball_subset_closedBall hβ_ball)
      have hd_phiβ := RudinRCA.Chapter12.hasDerivAt_phi hden_β
      have hval := (RudinRCA.Chapter12.theorem12_4 hβ_ball).2.2.2.2.2.2
      rw [← hd_phiβ.deriv, hval] at hd_phiβ
      exact hd_phiβ.comp z₀ (hg_holo z₀ hz₀).hasDerivAt
    have hpos_1s2 : 0 < 1 - s ^ 2 := by nlinarith
    have hpos_1a2 : 0 < 1 - ‖α‖ ^ 2 := by rw [← hs_sq]; nlinarith
    have hnorm1 : 2 * s * ‖deriv g_sq z₀‖ = (1 - s ^ 4) * η := by
      have hn := congrArg norm heq_deriv1
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos_1a2,
        hh_deriv_norm, ← hs_sq] at hn
      simpa [s, pow_succ, mul_assoc] using hn
    have hnorm2 : ‖deriv ψ_k z₀‖ = (1 - s ^ 2)⁻¹ * ‖deriv g_sq z₀‖ := by
      rw [hd_ψk.deriv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hpos_1s2)]
    have h2s_ψk : 2 * s * ‖deriv ψ_k z₀‖ = (1 + s ^ 2) * η := by
      have hmul : 2 * s * ((1 - s ^ 2) * ‖deriv ψ_k z₀‖) = (1 - s ^ 2) * ((1 + s ^ 2) * η) := by
        calc
          2 * s * ((1 - s ^ 2) * ‖deriv ψ_k z₀‖)
              = (1 - s ^ 2) * (1 - s ^ 2)⁻¹ * (2 * s * ‖deriv g_sq z₀‖) := by
                rw [hnorm2]; ring
          _ = 2 * s * ‖deriv g_sq z₀‖ := by rw [mul_inv_cancel₀ hpos_1s2.ne', one_mul]
          _ = (1 - s ^ 4) * η := hnorm1
          _ = (1 - s ^ 2) * ((1 + s ^ 2) * η) := by ring
      exact mul_left_cancel₀ hpos_1s2.ne' (by linear_combination hmul)
    have hle_ψk : ‖deriv ψ_k z₀‖ ≤ η := le_csSup hS_bdd ⟨ψ_k, hψ_k_Fam, rfl⟩
    have h1s_pos : 0 < (1 - s) ^ 2 * η := mul_pos (sq_pos_of_pos (by linarith)) hη_pos
    nlinarith
  have hh_bij : BijOn h Ω (ball (0 : ℂ) 1) := ⟨hh_Fam.2.2, hh_Fam.2.1, hh_surj⟩
  -- Step 4: Remark 14.9 extremal property for ALL `f ∈ H(Ω)` with `MapsTo f Ω (ball 0 1)`
  have hh_img : h '' Ω = ball (0 : ℂ) 1 := hh_bij.image_eq
  obtain ⟨h_inv, hh_inv_holo, hh_left, hh_right, hh_inv_deriv⟩ :=
    (RudinRCA.Chapter10.theorem10_33.1 hΩ.1 hh_Fam.1 hh_Fam.2.1).2.2
  rw [hh_img] at hh_inv_holo hh_right
  have hh_inv0 : h_inv 0 = z₀ := by
    have := hh_left z₀ hz₀
    rwa [hhz₀] at this
  have hdh_inv0 : deriv h_inv 0 = (deriv h z₀)⁻¹ := by
    have := hh_inv_deriv z₀ hz₀
    rwa [hhz₀] at this
  refine ⟨h, hh_Fam.1, hh_bij, hhz₀,
    by rw [hdh_eq, Complex.ofReal_re]; exact hη_pos,
    by rw [hdh_eq, Complex.ofReal_im],
    by rw [hh_deriv_norm]; exact hη_pos, ?_⟩
  intro f hf hmaps_f
  let β_f : ℂ := f z₀
  have hβf_ball : β_f ∈ ball (0 : ℂ) 1 := hmaps_f hz₀
  have hβf_lt1 : ‖β_f‖ < 1 := mem_ball_zero_iff.mp hβf_ball
  have hpos_βf : 0 < 1 - ‖β_f‖ ^ 2 := by nlinarith [norm_nonneg β_f]
  let F : ℂ → ℂ := fun w => RudinRCA.Chapter12.phi β_f (f (h_inv w))
  have hF_diff : DifferentiableOn ℂ F (ball (0 : ℂ) 1) := by
    intro w hw
    have hw_Ω : h_inv w ∈ Ω := (hh_right w hw).1
    have hfw_ball : f (h_inv w) ∈ ball (0 : ℂ) 1 := hmaps_f hw_Ω
    have hden := RudinRCA.Chapter12.phi_denom_ne_zero hβf_ball (ball_subset_closedBall hfw_ball)
    exact ((RudinRCA.Chapter12.hasDerivAt_phi hden).differentiableAt.comp w
      ((hf (h_inv w) hw_Ω).comp w (hh_inv_holo w hw))).differentiableWithinAt
  have hF_le1 : ∀ w ∈ ball (0 : ℂ) 1, ‖F w‖ ≤ 1 := by
    intro w hw
    exact (mem_ball_zero_iff.mp (RudinRCA.Chapter12.mapsTo_phi_ball hβf_ball
      (hmaps_f (hh_right w hw).1))).le
  have hF0 : F 0 = 0 := by
    dsimp [F]
    rw [hh_inv0]
    exact RudinRCA.Chapter12.phi_self β_f
  obtain ⟨_, hF_deriv_le1, hF_eq_rot⟩ := RudinRCA.Chapter12.theorem12_2 hF_diff hF_le1 hF0
  have hd_F0 : deriv F 0 =
      (((1 - ‖β_f‖ ^ 2)⁻¹ : ℝ) : ℂ) * (deriv f z₀ * (deriv h z₀)⁻¹) := by
    have hden := RudinRCA.Chapter12.phi_denom_ne_zero hβf_ball (ball_subset_closedBall hβf_ball)
    have hd_phi := RudinRCA.Chapter12.hasDerivAt_phi hden
    have hval := (RudinRCA.Chapter12.theorem12_4 hβf_ball).2.2.2.2.2.2
    rw [← hd_phi.deriv, hval] at hd_phi
    have hd_comp : HasDerivAt F
        ((((1 - ‖β_f‖ ^ 2)⁻¹ : ℝ) : ℂ) * (deriv f z₀ * deriv h_inv 0)) 0 := by
      have hd_fh : HasDerivAt (fun w => f (h_inv w)) (deriv f z₀ * deriv h_inv 0) 0 := by
        have h1 : HasDerivAt f (deriv f z₀) (h_inv 0) :=
          hh_inv0.symm ▸ (hf z₀ hz₀).hasDerivAt
        exact h1.comp 0 (hh_inv_holo 0 (Metric.mem_ball_self zero_lt_one)).hasDerivAt
      have hd_phi' : HasDerivAt (RudinRCA.Chapter12.phi β_f)
          ((((1 - ‖β_f‖ ^ 2)⁻¹ : ℝ) : ℂ)) (f (h_inv 0)) := by
        rwa [hh_inv0]
      exact hd_phi'.comp 0 hd_fh
    rw [hd_comp.deriv, hdh_inv0]
  have hnorm_F0 : ‖deriv F 0‖ = (1 - ‖β_f‖ ^ 2)⁻¹ * (‖deriv f z₀‖ / η) := by
    rw [hd_F0, norm_mul, norm_mul, norm_inv, hh_deriv_norm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos_βf), div_eq_mul_inv]
  have hstrong_le : ‖deriv f z₀‖ ≤ (1 - ‖β_f‖ ^ 2) * η := by
    have h1 : (1 - ‖β_f‖ ^ 2)⁻¹ * (‖deriv f z₀‖ / η) ≤ 1 := hnorm_F0 ▸ hF_deriv_le1
    have h2 := mul_le_mul_of_nonneg_left h1 hpos_βf.le
    rw [← mul_assoc, mul_inv_cancel₀ hpos_βf.ne', one_mul, mul_one] at h2
    exact (div_le_iff₀ hη_pos).mp h2
  have h_le : ‖deriv f z₀‖ ≤ ‖deriv h z₀‖ := by
    rw [hh_deriv_norm]
    nlinarith [sq_nonneg ‖β_f‖, hη_pos]
  refine ⟨h_le, ?_⟩
  constructor
  · intro heq_norm
    rw [hh_deriv_norm] at heq_norm
    have hβf_zero : β_f = 0 := by
      by_contra hne
      have hpos_sq : 0 < ‖β_f‖ ^ 2 * η := mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hne)) hη_pos
      linarith
    have hF_norm1 : ‖deriv F 0‖ = 1 := by
      rw [hnorm_F0, hβf_zero, norm_zero, heq_norm]
      simp [hη_pos.ne']
    obtain ⟨c, hc_norm, hc_eq⟩ := hF_eq_rot (Or.inr hF_norm1)
    refine ⟨c, hc_norm, ?_⟩
    intro z hz
    have hFz := hc_eq (h z) (hh_Fam.2.2 hz)
    dsimp only [F] at hFz
    rw [hβf_zero, RudinRCA.Chapter12.phi, sub_zero, star_zero, zero_mul, sub_zero, div_one,
      hh_left z hz] at hFz
    exact hFz
  · rintro ⟨c, hc_norm, hc_eq⟩
    have hev : f =ᶠ[𝓝 z₀] fun z => c * h z := by
      filter_upwards [hΩ.1.mem_nhds hz₀] with z hz
      exact hc_eq z hz
    have hd : HasDerivAt (fun z => c * h z) (c * deriv h z₀) z₀ :=
      (hh_Fam.1 z₀ hz₀).hasDerivAt.const_mul c
    rw [hev.deriv_eq, hd.deriv, norm_mul, hc_norm, one_mul]

/-- Spherical winding number `Ind_γ(p)` for `p ∈ S²`: equals `Ind_γ(z)` at finite `z ∈ ℂ` and `0`
at `∞` (matching the vanishing of `Ind_γ` on the unbounded component of `(γ*)ᶜ`, RCA 10.10 / 13.11(c)). -/
def sphericalInd (γ : RudinRCA.Chapter10.BookPath) : RiemannSphere → ℂ :=
  OnePoint.rec 0 (fun z => RudinRCA.Chapter10.Ind γ.toBookCurve z)

@[simp] theorem sphericalInd_infty (γ : RudinRCA.Chapter10.BookPath) :
    sphericalInd γ ∞ = 0 := rfl

@[simp] theorem sphericalInd_coe (γ : RudinRCA.Chapter10.BookPath) (z : ℂ) :
    sphericalInd γ (z : RiemannSphere) = RudinRCA.Chapter10.Ind γ.toBookCurve z := rfl

/-- `sphericalInd γ` is continuous at `∞` (`Ind_γ(z) = 0` on `infinityDisc R` for large `R`). -/
theorem sphericalInd_eventually_zero_nhds_infty (γ : RudinRCA.Chapter10.BookPath)
    (hcl : γ.IsClosed) :
    ∀ᶠ p in 𝓝 (∞ : RiemannSphere), sphericalInd γ p = 0 := by
  obtain ⟨R, hR, htr_sub⟩ := γ.isCompact_trace.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  filter_upwards [(isOpen_infinityDisc R).mem_nhds (infinity_mem_infinityDisc R)] with p hp
  induction p using OnePoint.rec with
  | infty => rfl
  | coe z =>
    simp only [sphericalInd_coe]
    have hz_gt : R < ‖z‖ := (coe_mem_infinityDisc z R).mp hp
    have hext_conn := RudinRCA.Chapter10.isConnected_compl_closedBall (0 : ℂ) hR.le
    have hext_compl : (closedBall (0 : ℂ) R)ᶜ ⊆ (γ.trace)ᶜ := compl_subset_compl.mpr htr_sub
    have hz_ext : z ∈ (closedBall (0 : ℂ) R)ᶜ := by
      rw [mem_compl_iff, mem_closedBall_zero_iff, not_le]
      exact hz_gt
    let C := RudinRCA.Chapter10.bookComponent (γ.trace)ᶜ z
    have hC_mem : C ∈ RudinRCA.Chapter10.bookComponents (γ.trace)ᶜ :=
      ⟨z, hext_compl hz_ext, rfl⟩
    have hsub_C : (closedBall (0 : ℂ) R)ᶜ ⊆ C :=
      RudinRCA.Chapter10.bookComponent_maximal hext_compl
        ((RudinRCA.Chapter10.bookConnected_iff_isPreconnected _).mpr hext_conn.2) hz_ext
    have hC_unbdd : ¬ Bornology.IsBounded C := by
      intro hbdd
      obtain ⟨B, _, hB⟩ := hbdd.subset_closedBall_lt 0 (0 : ℂ)
      let M_big : ℝ := max R B + 1
      have hM_pos : 0 < M_big := lt_of_lt_of_le hR ((le_max_left R B).trans (by linarith))
      have hw_ext : (M_big : ℂ) ∈ (closedBall (0 : ℂ) R)ᶜ := by
        rw [mem_compl_iff, mem_closedBall_zero_iff, not_le, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hM_pos]
        exact lt_of_le_of_lt (le_max_left R B) (by dsimp [M_big]; linarith)
      have hwB := hB (hsub_C hw_ext)
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM_pos] at hwB
      linarith [le_max_right R B]
    exact RudinRCA.Chapter10.Ind_eq_zero_of_mem_unbounded_component γ hcl hC_mem hC_unbdd
      (RudinRCA.Chapter10.mem_bookComponent (hext_compl hz_ext))

/-- Every pair of points in a region `Ω ⊆ ℂ` can be joined by a `BookPath` in `Ω`. -/
theorem reachable_by_bookPath_of_isRegion {Ω : Set ℂ} (hΩ : RudinRCA.Chapter10.IsRegion Ω)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∀ z ∈ Ω, ∃ γ : RudinRCA.Chapter10.BookPath,
      γ.trace ⊆ Ω ∧ γ.toFun γ.α = z₀ ∧ γ.toFun γ.β = z := by
  let S : Set ℂ := {z ∈ Ω | ∃ γ : RudinRCA.Chapter10.BookPath,
    γ.trace ⊆ Ω ∧ γ.toFun γ.α = z₀ ∧ γ.toFun γ.β = z}
  have hz₀_S : z₀ ∈ S := by
    refine ⟨hz₀, RudinRCA.Chapter10.orientedSegment z₀ z₀, ?_,
      RudinRCA.Chapter10.orientedSegment_start z₀ z₀,
      RudinRCA.Chapter10.orientedSegment_end z₀ z₀⟩
    rw [RudinRCA.Chapter10.orientedSegment_trace, segment_same]
    exact singleton_subset_iff.mpr hz₀
  have hS_open : IsOpen S := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hz, γ, hγ_Ω, hγ_α, hγ_β⟩
    obtain ⟨r, hr, hball_Ω⟩ := Metric.isOpen_iff.mp hΩ.1 z hz
    refine ⟨r, hr, fun w hw => ⟨hball_Ω hw, ?_⟩⟩
    have hjoin : γ.toFun γ.β = (RudinRCA.Chapter10.orientedSegment z w).toFun
        (RudinRCA.Chapter10.orientedSegment z w).α :=
      hγ_β.trans (RudinRCA.Chapter10.orientedSegment_start z w).symm
    refine ⟨γ.concat (RudinRCA.Chapter10.orientedSegment z w) hjoin, ?_, ?_, ?_⟩
    · rw [RudinRCA.Chapter10.BookPath.concat_trace, RudinRCA.Chapter10.orientedSegment_trace]
      exact union_subset hγ_Ω
        (((convex_ball z r).segment_subset (Metric.mem_ball_self hr) hw).trans hball_Ω)
    · rw [RudinRCA.Chapter10.BookPath.concat_start]
      exact hγ_α
    · rw [RudinRCA.Chapter10.BookPath.concat_end, RudinRCA.Chapter10.orientedSegment_end]
  have hSc_open : IsOpen (Ω \ S) := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hz, hz_notS⟩
    obtain ⟨r, hr, hball_Ω⟩ := Metric.isOpen_iff.mp hΩ.1 z hz
    refine ⟨r, hr, fun w hw => ⟨hball_Ω hw, ?_⟩⟩
    rintro ⟨_, γ, hγ_Ω, hγ_α, hγ_β⟩
    have hjoin : γ.toFun γ.β = (RudinRCA.Chapter10.orientedSegment w z).toFun
        (RudinRCA.Chapter10.orientedSegment w z).α :=
      hγ_β.trans (RudinRCA.Chapter10.orientedSegment_start w z).symm
    apply hz_notS
    refine ⟨hz, γ.concat (RudinRCA.Chapter10.orientedSegment w z) hjoin, ?_, ?_, ?_⟩
    · rw [RudinRCA.Chapter10.BookPath.concat_trace, RudinRCA.Chapter10.orientedSegment_trace]
      exact union_subset hγ_Ω
        (((convex_ball z r).segment_subset hw (Metric.mem_ball_self hr)).trans hball_Ω)
    · rw [RudinRCA.Chapter10.BookPath.concat_start]
      exact hγ_α
    · rw [RudinRCA.Chapter10.BookPath.concat_end, RudinRCA.Chapter10.orientedSegment_end]
  intro z hz
  by_contra hnot
  have hz_diff : z ∈ Ω \ S := ⟨hz, fun hS => hnot hS.2⟩
  obtain ⟨u, _, hu_S, hu_diff⟩ := hΩ.2.isPreconnected S (Ω \ S) hS_open hSc_open
    (fun x hx => by by_cases hxS : x ∈ S; exact Or.inl hxS; exact Or.inr ⟨hx, hxS⟩)
    ⟨z₀, hz₀, hz₀_S⟩ ⟨z, hz, hz_diff⟩
  exact hu_diff.2 hu_S

/-- **Theorem 13.11 (Nine equivalent characterizations of simply connected plane regions,
RCA pp. 274–275):**
Let `Ω ⊆ ℂ` be a plane region (`IsRegion Ω`; including `Ω = ℂ`). The following nine properties are
equivalent (following Rudin's exact lettering `(a)`–`(j)`, which omits `(i)`):
- `(a)` `Ω` is homeomorphic to the open unit disc `U = ball (0 : ℂ) 1`;
- `(b)` `Ω` is simply connected (`BookSimplyConnected Ω`);
- `(c)` `Ind_γ(α) = 0` for every closed path `γ` in `Ω` and every `α ∈ S² \ Ω` (`sphericalInd`);
- `(d)` `S² \ Ω` is connected;
- `(e)` every `f ∈ H(Ω)` can be approximated by polynomials uniformly on compact subsets of `Ω`;
- `(f)` for every `f ∈ H(Ω)` and every closed path `γ` in `Ω`, `∫_γ f(z) dz = 0`;
- `(g)` every `f ∈ H(Ω)` has a holomorphic primitive `F ∈ H(Ω)` (`F' = f` on `Ω`);
- `(h)` every zero-free `f ∈ H(Ω)` (`∀ z ∈ Ω, f z ≠ 0`, i.e. `1/f ∈ H(Ω)`) has a holomorphic
  logarithm `φ ∈ H(Ω)` (`exp ∘ φ = f` on `Ω`);
- `(j)` every zero-free `f ∈ H(Ω)` (`∀ z ∈ Ω, f z ≠ 0`) has a holomorphic square root `φ ∈ H(Ω)`
  (`φ^2 = f` on `Ω`). -/
theorem theorem13_11 {Ω : Set ℂ} (hΩ : RudinRCA.Chapter10.IsRegion Ω) :
    let condA : Prop := Nonempty (Ω ≃ₜ ball (0 : ℂ) 1)
    let condB : Prop := RudinRCA.Chapter10.BookSimplyConnected Ω
    let condC : Prop :=
      ∀ γ : RudinRCA.Chapter10.BookPath, γ.IsClosed → γ.trace ⊆ Ω →
        ∀ α ∈ sphericalCompl Ω, sphericalInd γ α = 0
    let condD : Prop := IsConnected (sphericalCompl Ω)
    let condE : Prop :=
      ∀ f : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn f Ω →
        ∃ P : ℕ → Polynomial ℂ,
          RudinRCA.Chapter10.ConvergesOnCompactSubsets (fun n z => (P n).eval z) f Ω
    let condF : Prop :=
      ∀ f : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn f Ω →
        ∀ γ : RudinRCA.Chapter10.BookPath, γ.IsClosed → γ.trace ⊆ Ω →
          RudinRCA.Chapter10.pathIntegral f γ.toBookCurve = 0
    let condG : Prop :=
      ∀ f : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn f Ω →
        ∃ F : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn F Ω ∧ ∀ z ∈ Ω, deriv F z = f z
    let condH : Prop :=
      ∀ f : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn f Ω → (∀ z ∈ Ω, f z ≠ 0) →
        ∃ φ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn φ Ω ∧ ∀ z ∈ Ω, Complex.exp (φ z) = f z
    let condJ : Prop :=
      ∀ f : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn f Ω → (∀ z ∈ Ω, f z ≠ 0) →
        ∃ φ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn φ Ω ∧ ∀ z ∈ Ω, φ z ^ 2 = f z
    List.TFAE [condA, condB, condC, condD, condE, condF, condG, condH, condJ] ∧
      (condA ↔ condB) ∧ (condB ↔ condC) ∧ (condC ↔ condD) ∧ (condD ↔ condE) ∧
      (condE ↔ condF) ∧ (condF ↔ condG) ∧ (condG ↔ condH) ∧ (condH ↔ condJ) ∧
      (condJ ↔ condA) := by
  intro condA condB condC condD condE condF condG condH condJ
  -- (a) → (b): transport null-homotopy across `e : Ω ≃ₜ ball 0 1`
  have hab : condA → condB := by
    rintro ⟨e⟩
    have hU_sc : RudinRCA.Chapter10.BookSimplyConnected (ball (0 : ℂ) 1) :=
      RudinRCA.Chapter10.theorem10_38
        (RudinRCA.Chapter10.disc_isRegion 0 zero_lt_one) (convex_ball 0 1)
    refine ⟨hΩ, fun γ hγ_cont hγ_Ω hγ_cl => ?_⟩
    have h0_Icc : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
    have h1_Icc : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.mpr zero_le_one
    let p₀ : Ω := ⟨γ 0, hγ_Ω ⟨0, h0_Icc, rfl⟩⟩
    let γ_sub : ℝ → Ω := fun t =>
      if ht : t ∈ Icc (0 : ℝ) 1 then ⟨γ t, hγ_Ω ⟨t, ht, rfl⟩⟩ else p₀
    have hγ_sub_cont : ContinuousOn γ_sub (Icc 0 1) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hcont_r : Continuous (fun t : Icc (0 : ℝ) 1 =>
          (⟨γ t.1, hγ_Ω ⟨t.1, t.2, rfl⟩⟩ : Ω)) :=
        Continuous.subtype_mk (hγ_cont.comp_continuous continuous_subtype_val Subtype.prop) _
      exact hcont_r.congr fun t => by dsimp only [γ_sub, Set.domRestrict]; rw [dif_pos t.2]
    let γ_U : ℝ → ℂ := fun t => (e (γ_sub t)).1
    have hγU_cont : ContinuousOn γ_U (Icc 0 1) :=
      (continuous_subtype_val.comp e.continuous).comp_continuousOn hγ_sub_cont
    have hγU_mem : γ_U '' Icc 0 1 ⊆ ball (0 : ℂ) 1 := by
      rintro _ ⟨t, _, rfl⟩
      exact (e (γ_sub t)).2
    have hγU_cl : γ_U 0 = γ_U 1 := by
      dsimp only [γ_U, γ_sub]
      simp only [h0_Icc, h1_Icc, ↓reduceDIte]
      congr 2
      exact Subtype.ext hγ_cl
    obtain ⟨c_U, hc_U, _, _, _, _, _, _, H_U, hHU_cont, hHU_mem, hHU_0, hHU_1, hHU_loop⟩ :=
      hU_sc.2 γ_U hγU_cont hγU_mem hγU_cl
    let q₀ : ball (0 : ℂ) 1 := ⟨c_U, hc_U⟩
    let c_Ω : ℂ := (e.symm q₀).1
    have hc_Ω : c_Ω ∈ Ω := (e.symm q₀).2
    let sq01 : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
    let H_sub : ℝ × ℝ → ball (0 : ℂ) 1 := fun p =>
      if hp : p ∈ sq01 then ⟨H_U p, hHU_mem ⟨p, hp, rfl⟩⟩ else q₀
    have hH_sub_cont : ContinuousOn H_sub sq01 := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hcont_r : Continuous (fun p : sq01 => (⟨H_U p.1, hHU_mem ⟨p.1, p.2, rfl⟩⟩ : ball (0 : ℂ) 1)) :=
        Continuous.subtype_mk (hHU_cont.comp_continuous continuous_subtype_val Subtype.prop) _
      refine hcont_r.congr fun p => ?_
      simp [H_sub, p.2]
    let H : ℝ × ℝ → ℂ := fun p => (e.symm (H_sub p)).1
    have hH_cont : ContinuousOn H sq01 :=
      (continuous_subtype_val.comp e.symm.continuous).comp_continuousOn hH_sub_cont
    refine ⟨c_Ω, hc_Ω, hγ_cont, continuousOn_const, hγ_Ω,
      by rintro _ ⟨_, _, rfl⟩; exact hc_Ω, hγ_cl, rfl, H, hH_cont, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨p, _, rfl⟩
      exact (e.symm (H_sub p)).2
    · intro s hs
      have hp0 : (s, (0 : ℝ)) ∈ sq01 := ⟨hs, h0_Icc⟩
      dsimp only [H, H_sub]
      simp only [hp0, ↓reduceDIte]
      have h0eq : (⟨H_U (s, 0), hHU_mem ⟨(s, 0), hp0, rfl⟩⟩ : ball (0 : ℂ) 1) = e (γ_sub s) := by
        apply Subtype.ext
        exact hHU_0 s hs
      rw [h0eq, e.symm_apply_apply]
      dsimp only [γ_sub]
      simp [hs]
    · intro s hs
      have hp1 : (s, (1 : ℝ)) ∈ sq01 := ⟨hs, h1_Icc⟩
      dsimp only [H, H_sub]
      simp only [hp1, ↓reduceDIte]
      have h1eq : (⟨H_U (s, 1), hHU_mem ⟨(s, 1), hp1, rfl⟩⟩ : ball (0 : ℂ) 1) = q₀ := by
        apply Subtype.ext
        exact hHU_1 s hs
      rw [h1eq]
    · intro t ht
      have hp0t : ((0 : ℝ), t) ∈ sq01 := ⟨h0_Icc, ht⟩
      have hp1t : ((1 : ℝ), t) ∈ sq01 := ⟨h1_Icc, ht⟩
      dsimp only [H, H_sub]
      simp only [hp0t, hp1t, ↓reduceDIte]
      congr 2
      apply Subtype.ext
      exact hHU_loop t ht
  -- (b) → (c): `corollary10_40_simplyConnected`
  have hbc : condB → condC := by
    intro hsc γ hcl htr p hp
    induction p using OnePoint.rec with
    | infty => rfl
    | coe α =>
      simp only [sphericalInd_coe]
      have hα_not : α ∉ Ω := (coe_mem_sphericalCompl α Ω).mp hp
      exact (RudinRCA.Chapter10.corollary10_40_simplyConnected hsc).1 γ hcl htr α hα_not
  -- (c) → (d): contrapositive via closed separation of `S² \ Ω`, `theorem13_5`, and `theorem13_4`
  have hcd : condC → condD := by
    intro hcondC
    have hinf_mem : (∞ : RiemannSphere) ∈ sphericalCompl Ω := infinity_mem_sphericalCompl Ω
    refine ⟨⟨∞, hinf_mem⟩, ?_⟩
    by_contra hnot_pre
    unfold IsPreconnected at hnot_pre
    push Not at hnot_pre
    obtain ⟨U₁, U₂, hU₁, hU₂, hsub, hne₁, hne₂, hdisj⟩ := hnot_pre
    -- Helper when `∞ ∈ V_inf`, `V_fin` meets `sphericalCompl Ω`, `sphericalCompl Ω ⊆ V_fin ∪ V_inf` disjointly
    have hsep_contra : ∀ (V_fin V_inf : Set RiemannSphere),
        IsOpen V_fin → IsOpen V_inf →
        sphericalCompl Ω ⊆ V_fin ∪ V_inf →
        (sphericalCompl Ω ∩ V_fin).Nonempty →
        (∞ : RiemannSphere) ∈ V_inf →
        ¬ (sphericalCompl Ω ∩ (V_fin ∩ V_inf)).Nonempty → False := by
      intro V_fin V_inf hV_fin hV_inf hcov hfin_ne hinf_V hdisj_V
      have hSΩ_closed : IsClosed (sphericalCompl Ω) :=
        (finite_chart_open_embedding.isOpenMap Ω hΩ.1).isClosed_compl
      let A : Set RiemannSphere := sphericalCompl Ω \ V_inf
      let B : Set RiemannSphere := sphericalCompl Ω \ V_fin
      have hA_eq : A = sphericalCompl Ω ∩ V_fin := by
        ext p
        constructor
        · rintro ⟨hpS, hp_not⟩
          rcases hcov hpS with hp1 | hp2
          · exact ⟨hpS, hp1⟩
          · exact False.elim (hp_not hp2)
        · rintro ⟨hpS, hp1⟩
          exact ⟨hpS, fun hp2 => hdisj_V ⟨p, hpS, hp1, hp2⟩⟩
      have hA_closed : IsClosed A := hSΩ_closed.sdiff hV_inf
      have hB_closed : IsClosed B := hSΩ_closed.sdiff hV_fin
      let K : Set ℂ := ((↑) : ℂ → RiemannSphere) ⁻¹' A
      have hK_closed : IsClosed K := hA_closed.preimage OnePoint.continuous_coe
      obtain ⟨R, _, hR_sub⟩ := ((isOpen_riemannSphere_iff V_inf).mp hV_inf).2 hinf_V
      have hK_bdd : Bornology.IsBounded K := by
        refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset ?_
        intro z hzK
        rw [mem_closedBall_zero_iff]
        by_contra hgt
        have hz_inf : (z : RiemannSphere) ∈ V_inf :=
          hR_sub ((coe_mem_infinityDisc z R).mpr (not_le.mp hgt))
        exact hzK.2 hz_inf
      have hK_comp : IsCompact K := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hK_closed, hK_bdd⟩
      obtain ⟨p₀, hp₀⟩ := hA_eq.symm ▸ hfin_ne
      have hK_ne : K.Nonempty := by
        induction p₀ using OnePoint.rec with
        | infty => exact False.elim (hp₀.2 hinf_V)
        | coe z₀ => exact ⟨z₀, hp₀⟩
      have hK_disj : K ⊆ Ωᶜ := fun z hzK => (coe_mem_sphericalCompl z Ω).mp hzK.1
      -- `Ω₁ := Ω ∪ K = ((↑) : ℂ → S²) ⁻¹' Bᶜ`, hence open in `ℂ`!
      let Ω₁ : Set ℂ := Ω ∪ K
      have hmem_K : ∀ z : ℂ, z ∈ K ↔ z ∉ Ω ∧ (z : RiemannSphere) ∉ V_inf := by
        intro z
        change (z : RiemannSphere) ∈ sphericalCompl Ω \ V_inf ↔ _
        rw [Set.mem_sdiff, coe_mem_sphericalCompl]
      have hmem_B : ∀ z : ℂ, (z : RiemannSphere) ∈ B ↔ z ∉ Ω ∧ (z : RiemannSphere) ∉ V_fin := by
        intro z
        change (z : RiemannSphere) ∈ sphericalCompl Ω \ V_fin ↔ _
        rw [Set.mem_sdiff, coe_mem_sphericalCompl]
      have hΩ₁_eq : Ω₁ = ((↑) : ℂ → RiemannSphere) ⁻¹' Bᶜ := by
        ext z
        rw [Set.mem_union, hmem_K, Set.mem_preimage, Set.mem_compl_iff, hmem_B]
        constructor
        · rintro (hzΩ | ⟨hz_notΩ, hz_notV⟩)
          · exact fun ⟨hnot, _⟩ => hnot hzΩ
          · rintro ⟨_, hz_not_fin⟩
            rcases hcov ((coe_mem_sphericalCompl z Ω).mpr hz_notΩ) with h1 | h2
            · exact hz_not_fin h1
            · exact hz_notV h2
        · intro hnotB
          by_cases hzΩ : z ∈ Ω
          · exact Or.inl hzΩ
          · right
            refine ⟨hzΩ, fun hz_inf => ?_⟩
            have hz_fin : (z : RiemannSphere) ∈ V_fin := by
              by_contra hnot_fin
              exact hnotB ⟨hzΩ, hnot_fin⟩
            exact hdisj_V ⟨(z : RiemannSphere),
              (coe_mem_sphericalCompl z Ω).mpr hzΩ, hz_fin, hz_inf⟩
      have hΩ₁_open : IsOpen Ω₁ :=
        hΩ₁_eq ▸ (hB_closed.isOpen_compl.preimage OnePoint.continuous_coe)
      have hsdiff_eq : Ω₁ \ K = Ω := by
        ext z
        simp only [Ω₁, Set.mem_sdiff, Set.mem_union]
        exact ⟨fun ⟨h, hnotK⟩ => h.resolve_right hnotK,
          fun hzΩ => ⟨Or.inl hzΩ, fun hzK => hK_disj hzK hzΩ⟩⟩
      obtain ⟨L, hL_bal, _, hL_tr, _, hL_Ind1, _⟩ :=
        theorem13_5 hΩ₁_open hK_comp subset_union_right
      rw [hsdiff_eq] at hL_tr
      obtain ⟨z₀, hz₀K⟩ := hK_ne
      have hz₀_notΩ : z₀ ∉ Ω := hK_disj hz₀K
      have hind1 : (intervalsChain L).Ind z₀ = 1 := hL_Ind1 z₀ hz₀K
      obtain ⟨⟨_, _, _, paths, hlen_p, hpaths_closed, hpaths_tr_eq, hequiv⟩, _⟩ :=
        theorem13_4 L hL_bal
      have hz₀_not_L : z₀ ∉ (intervalsChain L).trace := fun h => hz₀_notΩ (hL_tr h)
      have hz₀_not_paths : z₀ ∉ (paths : RudinRCA.Chapter10.BookChain).trace := by
        rw [hpaths_tr_eq]; exact hz₀_not_L
      have hind_eq : (intervalsChain L).Ind z₀ = (paths : RudinRCA.Chapter10.BookChain).Ind z₀ :=
        RudinRCA.Chapter10.BookChain.Ind_congr_equiv hequiv
          (fun h => h.elim hz₀_not_L hz₀_not_paths)
      have hpaths_zero : (paths : RudinRCA.Chapter10.BookChain).Ind z₀ = 0 := by
        have hall_zero : ∀ γ ∈ paths, RudinRCA.Chapter10.Ind γ.toBookCurve z₀ = 0 := by
          intro γ hγ
          have hγ_tr : γ.trace ⊆ Ω := by
            have hsub_p : γ.trace ⊆ (paths : RudinRCA.Chapter10.BookChain).trace :=
              Set.subset_biUnion_of_mem hγ
            rw [hpaths_tr_eq] at hsub_p
            exact hsub_p.trans hL_tr
          simpa using hcondC γ (hpaths_closed γ hγ) hγ_tr (z₀ : RiemannSphere)
            ((coe_mem_sphericalCompl z₀ Ω).mpr hz₀_notΩ)
        clear hlen_p hind_eq hz₀_not_paths hpaths_tr_eq hequiv
        induction paths with
        | nil => exact RudinRCA.Chapter10.BookChain.Ind_nil z₀
        | cons γ ps ih =>
          rw [RudinRCA.Chapter10.BookChain.Ind_cons,
            hall_zero γ List.mem_cons_self, zero_add]
          exact ih (fun σ hσ => hpaths_closed σ (List.mem_cons_of_mem _ hσ))
            (fun σ hσ => hall_zero σ (List.mem_cons_of_mem _ hσ))
      rw [hind_eq, hpaths_zero] at hind1
      exact zero_ne_one hind1
    rcases hsub hinf_mem with hinf₁ | hinf₂
    · exact hsep_contra U₂ U₁ hU₂ hU₁ (hsub.trans (union_comm U₁ U₂).subset) hne₂ hinf₁
        (by rw [inter_comm U₂ U₁]; exact Set.not_nonempty_iff_eq_empty.mpr hdisj)
    · exact hsep_contra U₁ U₂ hU₁ hU₂ hsub hne₁ hinf₂
        (Set.not_nonempty_iff_eq_empty.mpr hdisj)
  -- (d) → (e): `theorem13_9`
  have hde : condD → condE := fun hconn f hf => (theorem13_9 hΩ.1).2 hconn hf
  -- (e) → (f): uniform polynomial approximation on compact `γ.trace`
  have hef : condE → condF := by
    intro hcondE f hf γ hcl htr
    obtain ⟨P, hP⟩ := hcondE f hf
    have hunif := hP γ.trace htr γ.isCompact_trace
    have hpoly_int : ∀ n : ℕ,
        RudinRCA.Chapter10.pathIntegral (fun z => (P n).eval z) γ.toBookCurve = 0 := by
      intro n
      exact (RudinRCA.Chapter10.theorem10_14 isOpen_univ convex_univ 0
        (P n).continuous.continuousOn
        (fun z _ => (P n).differentiableAt (x := z))).2 γ hcl (subset_univ _)
    by_contra hne0
    have hpos : 0 < ‖RudinRCA.Chapter10.pathIntegral f γ.toBookCurve‖ := norm_pos_iff.mpr hne0
    let L_len : ℝ := RudinRCA.Chapter10.pathLength γ.toBookCurve + 1
    have hL_pos : 0 < L_len := by linarith [γ.pathLength_nonneg]
    let ε : ℝ := ‖RudinRCA.Chapter10.pathIntegral f γ.toBookCurve‖ / (2 * L_len)
    have hε : 0 < ε := by positivity
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hunif ε hε)
    have hf_cont : ContinuousOn f γ.trace :=
      (RudinRCA.Chapter10.continuousOn_of_holomorphicOn hf).mono htr
    have hP_cont : ContinuousOn (fun z => (P N).eval z) γ.trace :=
      (P N).continuous.continuousOn
    have heq_sub : RudinRCA.Chapter10.pathIntegral f γ.toBookCurve =
        RudinRCA.Chapter10.pathIntegral (fun z => f z - (P N).eval z) γ.toBookCurve := by
      rw [γ.pathIntegral_sub hf_cont hP_cont, hpoly_int N, sub_zero]
    have hle := γ.norm_pathIntegral_le (f := fun z => f z - (P N).eval z)
      (hf_cont.sub hP_cont) (M := ε) (fun z hz => by
        have hlt := hN N (le_refl N) z hz
        rw [dist_eq_norm] at hlt
        exact hlt.le)
    rw [← heq_sub] at hle
    have hlt_strict :
        ε * RudinRCA.Chapter10.pathLength γ.toBookCurve <
          ‖RudinRCA.Chapter10.pathIntegral f γ.toBookCurve‖ := by
      calc
        ε * RudinRCA.Chapter10.pathLength γ.toBookCurve
            ≤ ε * L_len := mul_le_mul_of_nonneg_left (by dsimp [L_len]; linarith) hε.le
        _ = ‖RudinRCA.Chapter10.pathIntegral f γ.toBookCurve‖ / 2 := by
            dsimp [ε]; field_simp [hL_pos.ne']
        _ < ‖RudinRCA.Chapter10.pathIntegral f γ.toBookCurve‖ := half_lt_self hpos
    linarith
  -- (f) → (g): path-independent line integral primitive on region `Ω`
  have hfg : condF → condG := by
    intro hcondF f hf
    obtain ⟨z₀, hz₀⟩ := hΩ.2.nonempty
    have hreach := reachable_by_bookPath_of_isRegion hΩ hz₀
    have hf_cont : ContinuousOn f Ω := RudinRCA.Chapter10.continuousOn_of_holomorphicOn hf
    -- Path independence: any two paths in `Ω` from `z₀` to `z` have equal integrals
    have hpath_indep : ∀ {z : ℂ} (γ₁ γ₂ : RudinRCA.Chapter10.BookPath),
        γ₁.trace ⊆ Ω → γ₁.toFun γ₁.α = z₀ → γ₁.toFun γ₁.β = z →
        γ₂.trace ⊆ Ω → γ₂.toFun γ₂.α = z₀ → γ₂.toFun γ₂.β = z →
        RudinRCA.Chapter10.pathIntegral f γ₁.toBookCurve =
          RudinRCA.Chapter10.pathIntegral f γ₂.toBookCurve := by
      intro z γ₁ γ₂ htr₁ hα₁ hβ₁ htr₂ hα₂ hβ₂
      have hjoin : γ₁.toFun γ₁.β = γ₂.reverse.toFun γ₂.reverse.α := by
        rw [RudinRCA.Chapter10.BookPath.reverse_start, hβ₁, hβ₂]
      let loop := γ₁.concat γ₂.reverse hjoin
      have hloop_cl : loop.IsClosed := by
        change loop.toFun loop.α = loop.toFun loop.β
        rw [RudinRCA.Chapter10.BookPath.concat_start, RudinRCA.Chapter10.BookPath.concat_end,
          RudinRCA.Chapter10.BookPath.reverse_end, hα₁, hα₂]
      have hloop_tr : loop.trace ⊆ Ω := by
        rw [RudinRCA.Chapter10.BookPath.concat_trace, RudinRCA.Chapter10.BookPath.reverse_trace]
        exact union_subset htr₁ htr₂
      have h0 := hcondF f hf loop hloop_cl hloop_tr
      rw [γ₁.pathIntegral_concat γ₂.reverse hjoin (hf_cont.mono hloop_tr),
        γ₂.pathIntegral_reverse (hf_cont.mono htr₂)] at h0
      linear_combination h0
    classical
    let F : ℂ → ℂ := fun z =>
      if hz : z ∈ Ω then
        RudinRCA.Chapter10.pathIntegral f (Classical.choose (hreach z hz)).toBookCurve
      else 0
    have hF_deriv : ∀ z ∈ Ω, HasDerivAt F (f z) z := by
      intro z hz
      obtain ⟨r, hr, hball_Ω⟩ := Metric.isOpen_iff.mp hΩ.1 z hz
      obtain ⟨⟨G, hG_holo, hG_deriv⟩, _⟩ := RudinRCA.Chapter10.theorem10_14
        isOpen_ball (convex_ball z r) z (hf_cont.mono hball_Ω)
        (fun w hw => hf w (hball_Ω hw.1))
      have hG_at : HasDerivAt G (f z) z := by
        have hd := (hG_holo z (Metric.mem_ball_self hr)).hasDerivAt
        rwa [hG_deriv z (Metric.mem_ball_self hr)] at hd
      have hev : F =ᶠ[𝓝 z] fun w => F z + (G w - G z) := by
        filter_upwards [Metric.ball_mem_nhds z hr] with w hw
        have hw_Ω : w ∈ Ω := hball_Ω hw
        let γ_z := Classical.choose (hreach z hz)
        obtain ⟨hγz_tr, hγz_α, hγz_β⟩ := Classical.choose_spec (hreach z hz)
        let γ_w := Classical.choose (hreach w hw_Ω)
        obtain ⟨hγw_tr, hγw_α, hγw_β⟩ := Classical.choose_spec (hreach w hw_Ω)
        have hjoin : γ_z.toFun γ_z.β =
            (RudinRCA.Chapter10.orientedSegment z w).toFun
              (RudinRCA.Chapter10.orientedSegment z w).α :=
          hγz_β.trans (RudinRCA.Chapter10.orientedSegment_start z w).symm
        let γ_zw := γ_z.concat (RudinRCA.Chapter10.orientedSegment z w) hjoin
        have hseg_ball : (RudinRCA.Chapter10.orientedSegment z w).trace ⊆ ball z r := by
          rw [RudinRCA.Chapter10.orientedSegment_trace]
          exact (convex_ball z r).segment_subset (Metric.mem_ball_self hr) hw
        have hγzw_tr : γ_zw.trace ⊆ Ω := by
          rw [RudinRCA.Chapter10.BookPath.concat_trace]
          exact union_subset hγz_tr (hseg_ball.trans hball_Ω)
        have hFw_eq : F w = RudinRCA.Chapter10.pathIntegral f γ_zw.toBookCurve := by
          simp only [F, hw_Ω, ↓reduceDIte]
          exact hpath_indep γ_w γ_zw hγw_tr hγw_α hγw_β hγzw_tr
            (by rw [RudinRCA.Chapter10.BookPath.concat_start]; exact hγz_α)
            (by rw [RudinRCA.Chapter10.BookPath.concat_end,
                  RudinRCA.Chapter10.orientedSegment_end])
        have hFz_eq : F z = RudinRCA.Chapter10.pathIntegral f γ_z.toBookCurve := by
          simp only [F, hz, ↓reduceDIte]; rfl
        have hseg_int :
            RudinRCA.Chapter10.pathIntegral f
              (RudinRCA.Chapter10.orientedSegment z w).toBookCurve = G w - G z := by
          have hcongr : RudinRCA.Chapter10.pathIntegral f
              (RudinRCA.Chapter10.orientedSegment z w).toBookCurve =
              RudinRCA.Chapter10.pathIntegral (deriv G)
                (RudinRCA.Chapter10.orientedSegment z w).toBookCurve :=
            RudinRCA.Chapter10.BookPath.pathIntegral_congr _
              (fun u hu => (hG_deriv u (hseg_ball hu)).symm)
          have hdG_cont : ContinuousOn (deriv G) (ball z r) :=
            (hf_cont.mono hball_Ω).congr (fun u hu => hG_deriv u hu)
          rw [hcongr, RudinRCA.Chapter10.pathIntegral_deriv_eq_sub hG_holo hdG_cont
            (RudinRCA.Chapter10.orientedSegment z w) hseg_ball,
            RudinRCA.Chapter10.orientedSegment_end, RudinRCA.Chapter10.orientedSegment_start]
        exact hFw_eq.trans ((γ_z.pathIntegral_concat _ hjoin (hf_cont.mono hγzw_tr)).trans
          (congrArg₂ (· + ·) hFz_eq.symm hseg_int))
      have hd_rhs : HasDerivAt (fun w => F z + (G w - G z)) (f z) z := by
        simpa using (hG_at.sub_const (G z)).const_add (F z)
      exact hd_rhs.congr_of_eventuallyEq hev
    exact ⟨F, fun z hz => (hF_deriv z hz).differentiableAt, fun z hz => (hF_deriv z hz).deriv⟩
  -- (g) → (h): integrate `f' / f` to obtain holomorphic logarithm
  have hgh : condG → condH := by
    intro hcondG f hf hnz
    have hdf : RudinRCA.Chapter10.HolomorphicOn (deriv f) Ω :=
      RudinRCA.Chapter10.holomorphicOn_deriv hΩ.1 hf
    have hquot : RudinRCA.Chapter10.HolomorphicOn (fun z => deriv f z / f z) Ω :=
      fun z hz => (hdf z hz).div (hf z hz) (hnz z hz)
    obtain ⟨L₁, hL₁_holo, hL₁_deriv⟩ := hcondG (fun z => deriv f z / f z) hquot
    let k : ℂ → ℂ := fun z => f z * Complex.exp (-L₁ z)
    have hk_deriv : ∀ z ∈ Ω, HasDerivAt k 0 z := by
      intro z hz
      have hd_exp : HasDerivAt (fun w => Complex.exp (-L₁ w))
          (Complex.exp (-L₁ z) * (-deriv L₁ z)) z :=
        Complex.hasDerivAt_exp (-L₁ z) |>.comp z (hL₁_holo z hz).hasDerivAt.neg
      have hd_mul := (hf z hz).hasDerivAt.mul hd_exp
      refine hd_mul.congr_deriv ?_
      rw [hL₁_deriv z hz]
      have hfz : f z ≠ 0 := hnz z hz
      field_simp [hfz]
      ring
    obtain ⟨z₀, hz₀⟩ := hΩ.2.nonempty
    have hk_const : ∀ z ∈ Ω, k z = k z₀ := by
      intro z hz
      exact hΩ.1.is_const_of_deriv_eq_zero hΩ.2.isPreconnected
        (fun w hw => (hk_deriv w hw).differentiableAt.differentiableWithinAt)
        (fun w hw => (hk_deriv w hw).deriv) hz hz₀
    have hkz₀_ne : k z₀ ≠ 0 := mul_ne_zero (hnz z₀ hz₀) (Complex.exp_ne_zero _)
    let c₀ : ℂ := Complex.log (k z₀)
    have hexp_c₀ : Complex.exp c₀ = k z₀ := Complex.exp_log hkz₀_ne
    refine ⟨fun z => L₁ z + c₀, fun z hz => (hL₁_holo z hz).add (differentiableAt_const c₀), ?_⟩
    intro z hz
    rw [Complex.exp_add, hexp_c₀, ← hk_const z hz]
    dsimp [k]
    rw [mul_comm (f z), ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  -- (h) → (j): `φ(z) = exp(L(z) / 2)`
  have hhj : condH → condJ := by
    intro hcondH f hf hnz
    obtain ⟨L, hL_holo, hL_exp⟩ := hcondH f hf hnz
    refine ⟨fun z => Complex.exp (L z / 2),
      fun z hz => Complex.differentiable_exp.differentiableAt.comp z
        ((hL_holo z hz).div_const 2), ?_⟩
    intro z hz
    rw [sq, ← Complex.exp_add, add_halves, hL_exp z hz]
  -- (j) → (a): explicit radial homeomorphism for `Ω = univ`, and `riemann_mapping_of_holomorphic_sqrt` + `10.33` for `Ω ≠ univ`
  have hja : condJ → condA := by
    intro hcondJ
    by_cases huniv : Ω = Set.univ
    · subst huniv
      exact ⟨(Homeomorph.Set.univ ℂ).trans planeHomeomorphUnitBall⟩
    · obtain ⟨z₀, hz₀⟩ := hΩ.2.nonempty
      obtain ⟨h, hh_holo, hh_bij, _, _, _, _, _⟩ :=
        riemann_mapping_of_holomorphic_sqrt hΩ huniv hz₀ hcondJ
      obtain ⟨g, hg_holo, hg_left, hg_right, _⟩ :=
        (RudinRCA.Chapter10.theorem10_33.1 hΩ.1 hh_holo hh_bij.injOn).2.2
      rw [hh_bij.image_eq] at hg_holo hg_right
      have hh_cont : ContinuousOn h Ω := RudinRCA.Chapter10.continuousOn_of_holomorphicOn hh_holo
      have hg_cont : ContinuousOn g (ball (0 : ℂ) 1) :=
        RudinRCA.Chapter10.continuousOn_of_holomorphicOn hg_holo
      refine ⟨{
        toFun := fun z => ⟨h z.1, hh_bij.mapsTo z.2⟩
        invFun := fun w => ⟨g w.1, (hg_right w.1 w.2).1⟩
        left_inv := fun z => Subtype.ext (hg_left z.1 z.2)
        right_inv := fun w => Subtype.ext (hg_right w.1 w.2).2
        continuous_toFun := Continuous.subtype_mk
          (hh_cont.comp_continuous continuous_subtype_val Subtype.prop) _
        continuous_invFun := Continuous.subtype_mk
          (hg_cont.comp_continuous continuous_subtype_val Subtype.prop) _
      }⟩
  -- Assemble 9-cycle into `List.TFAE` and pairwise `↔`
  have htfae : List.TFAE [condA, condB, condC, condD, condE, condF, condG, condH, condJ] := by
    tfae_have 1 → 2 := hab
    tfae_have 2 → 3 := hbc
    tfae_have 3 → 4 := hcd
    tfae_have 4 → 5 := hde
    tfae_have 5 → 6 := hef
    tfae_have 6 → 7 := hfg
    tfae_have 7 → 8 := hgh
    tfae_have 8 → 9 := hhj
    tfae_have 9 → 1 := hja
    tfae_finish
  exact ⟨htfae,
    htfae.out 1 2, htfae.out 2 3, htfae.out 3 4, htfae.out 4 5,
    htfae.out 5 6, htfae.out 6 7, htfae.out 7 8, htfae.out 8 9, htfae.out 9 1⟩

/-- **Theorem 13.12 (Harmonicity of `log |f|` for zero-free holomorphic functions, RCA p. 276):**
Let `Ω ⊆ ℂ` be an arbitrary open set (neither connectedness nor simple connectedness is assumed),
and let `f ∈ H(Ω)` satisfy `∀ z ∈ Ω, f z ≠ 0`. Then:
1. On every open disc `ball z₀ r ⊆ Ω` (`r > 0`), `f` admits a local holomorphic logarithm
   `φ ∈ H(ball z₀ r)` (`exp ∘ φ = f`) satisfying `Real.log ‖f z‖ = (φ z).re` on `ball z₀ r`
   (by `13.11(h)` on the convex disc `ball z₀ r`);
2. The real-valued function `z ↦ Real.log ‖f z‖` is harmonic throughout `Ω`, both in Rudin's
   Chapter 11 sense (`RudinRCA.Chapter11.HarmonicOn`) and in Mathlib's sense
   (`InnerProductSpace.HarmonicOnNhd`). -/
theorem theorem13_12 {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ}
    (hf : RudinRCA.Chapter10.HolomorphicOn f Ω) (hnz : ∀ z ∈ Ω, f z ≠ 0) :
    (∀ z₀ : ℂ, ∀ r > 0, ball z₀ r ⊆ Ω →
      ∃ φ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn φ (ball z₀ r) ∧
        (∀ z ∈ ball z₀ r, Complex.exp (φ z) = f z) ∧
        (∀ z ∈ ball z₀ r, Real.log ‖f z‖ = (φ z).re)) ∧
    RudinRCA.Chapter11.HarmonicOn (fun z => Real.log ‖f z‖) Ω ∧
    InnerProductSpace.HarmonicOnNhd (fun z => Real.log ‖f z‖) Ω := by
  have hlocal : ∀ z₀ : ℂ, ∀ r > 0, ball z₀ r ⊆ Ω →
      ∃ φ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn φ (ball z₀ r) ∧
        (∀ z ∈ ball z₀ r, Complex.exp (φ z) = f z) ∧
        (∀ z ∈ ball z₀ r, Real.log ‖f z‖ = (φ z).re) := by
    intro z₀ r hr hsub
    have hreg : RudinRCA.Chapter10.IsRegion (ball z₀ r) :=
      RudinRCA.Chapter10.disc_isRegion z₀ hr
    have hsc : RudinRCA.Chapter10.BookSimplyConnected (ball z₀ r) :=
      RudinRCA.Chapter10.theorem10_38 hreg (convex_ball z₀ r)
    have htfae := (theorem13_11 hreg).1
    have hbh : (RudinRCA.Chapter10.BookSimplyConnected (ball z₀ r)) →
        (∀ g : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn g (ball z₀ r) →
          (∀ z ∈ ball z₀ r, g z ≠ 0) →
          ∃ φ : ℂ → ℂ, RudinRCA.Chapter10.HolomorphicOn φ (ball z₀ r) ∧
            ∀ z ∈ ball z₀ r, Complex.exp (φ z) = g z) :=
      (htfae.out 2 8).mp
    obtain ⟨φ, hφ_holo, hφ_exp⟩ :=
      hbh hsc f (fun z hz => hf z (hsub hz)) (fun z hz => hnz z (hsub hz))
    refine ⟨φ, hφ_holo, hφ_exp, ?_⟩
    intro z hz
    rw [← hφ_exp z hz, Complex.norm_exp, Real.log_exp]
  have hmath : InnerProductSpace.HarmonicOnNhd (fun z => Real.log ‖f z‖) Ω :=
    harmonic_log_norm hΩ ((RudinRCA.Chapter10.holomorphicOn_iff_differentiableOn hΩ).mp hf) hnz
  exact ⟨hlocal, RudinRCA.Chapter11.harmonicOn_of_mathlib hmath, hmath⟩


/-! Axiom audit for every declaration introduced in this module. -/
#print axioms RiemannSphere
#print axioms exteriorDisc
#print axioms infinityDisc
#print axioms infinity_mem_infinityDisc
#print axioms coe_mem_infinityDisc
#print axioms infinityDisc_eq
#print axioms isOpen_infinityDisc
#print axioms mem_nhds_infinity_iff
#print axioms finite_chart_open_embedding
#print axioms riemannSphereHomeomorph
#print axioms riemannSphere_compact
#print axioms infinity_mem_closure_of_unbounded
#print axioms isConnected_insert_infinity
#print axioms horizontalStrip
#print axioms horizontalStrip_isOpen
#print axioms horizontalStrip_planar_complement_not_preconnected
#print axioms horizontalStrip_spherical_complement_connected
#print axioms SphereAmbient
#print axioms northPole
#print axioms norm_northPole
#print axioms mem_north_orthogonal_iff
#print axioms complexPlaneEquiv
#print axioms complexPlaneEquiv_coe
#print axioms bookSphereHomeomorph
#print axioms bookSphereHomeomorph_infty
#print axioms norm_complexPlaneEquiv_sq
#print axioms bookSphereHomeomorph_coe
#print axioms removable_at_infinity_of_bounded
#print axioms inversePrincipalPolynomial
#print axioms inversePrincipalPolynomial_natDegree
#print axioms inversePrincipalPolynomial_coeff_zero
#print axioms inversePrincipalPolynomial_eval
#print axioms polynomial_principal_part_at_infinity
#print axioms polynomial_principal_part_at_infinity_with_limit
#print axioms iteratedDeriv_zero_of_exterior_growth
#print axioms exists_polynomial_of_exterior_growth
#print axioms exterior_growth_of_meromorphicAt_inversion
#print axioms exists_polynomial_of_entire_meromorphicAt_inversion
#print axioms not_meromorphicAt_inversion_of_entire_nonpolynomial
#print axioms harmonic_log_norm
#print axioms HasIsolatedSingularityAtInfinity
#print axioms HasRemovableSingularityAtInfinity
#print axioms HasPoleAtInfinity
#print axioms HasEssentialSingularityAtInfinity
#print axioms entire_hasIsolatedSingularityAtInfinity
#print axioms bounded_hasRemovableSingularityAtInfinity
#print axioms entire_nonpolynomial_hasEssentialSingularityAtInfinity
#print axioms pole_at_infinity_has_principal_part
#print axioms sphericalCompl
#print axioms infinity_mem_sphericalCompl
#print axioms coe_mem_sphericalCompl
#print axioms isOpen_riemannSphere_iff
#print axioms bookSphereHomeomorph_coe_one_add
#print axioms tendsto_cocompact_of_hasRemovableSingularityAtInfinity
#print axioms polynomial_principal_part_at_infinity_unique
#print axioms singularity_at_infinity_trichotomy
#print axioms theorem13_1
#print axioms theorem13_2
#print axioms isConnected_infinityDisc
#print axioms exhaustionSet
#print axioms isCompact_exhaustionSet
#print axioms exhaustionSet_subset
#print axioms exhaustionSet_subset_interior_succ
#print axioms exhaustionSet_mono
#print axioms iUnion_exhaustionSet
#print axioms exists_subset_exhaustionSet_of_isCompact
#print axioms exhaustionSet_sphericalCompl_component
#print axioms theorem13_3
#print axioms intervalOutDeg
#print axioms intervalInDeg
#print axioms IsBalancedIntervals
#print axioms intervalsChain
#print axioms IsPolygonalWalkFromTo
#print axioms IsClosedPolygonalWalk
#print axioms balancedIntervals_partition
#print axioms polygonalWalkToBookPath
#print axioms theorem13_4
#print axioms cancelOppositeEdges
#print axioms theorem13_5
#print axioms isOpen_sphericalCompl_of_isCompact
#print axioms isConnected_connectedComponentIn_of_mem
#print axioms isOpen_connectedComponentIn_spherical
#print axioms countable_components_of_isOpen_spherical
#print axioms countable_components_sphericalCompl
#print axioms isConnected_preimage_coe_of_isOpen
#print axioms polyHomAtBeta
#print axioms polyHomAtBeta_eval_zero
#print axioms polyHomAtBeta_eval_ne_zero
#print axioms IsRationalWithSphericalPolesIn
#print axioms isRationalWithSphericalPolesIn_poles
#print axioms isRationalWithSphericalPolesIn_singleton_infty
#print axioms isRationalWithSphericalPolesIn_empty
#print axioms AdmissiblePolyPair
#print axioms admissiblePolyPair_zero
#print axioms admissiblePolyPair_const
#print axioms admissiblePolyPair_add
#print axioms admissiblePolyPair_smul
#print axioms admissiblePolyPair_poly_of_infty_mem
#print axioms admissiblePolyPair_inv_pow
#print axioms admissiblePolyPair_finset_sum
#print axioms admissiblePolyPair_to_rational
#print axioms norm_pow_sub_pow_le
#print axioms pole_shift_step
#print axioms exists_pos_norm_sub_le
#print axioms runge_pole_push
#print axioms segment_cauchy_riemann_sum
#print axioms theorem13_6
#print axioms theorem13_7
#print axioms max_modulus_inv_bound
#print axioms bounded_planar_component_of_not_infty_mem
#print axioms theorem13_8
#print axioms theorem13_9
#print axioms theorem13_10
#print axioms planeHomeomorphUnitBall
#print axioms montel_locally_bounded
#print axioms hurwitz_injOn_of_limit
#print axioms riemann_mapping_of_holomorphic_sqrt
#print axioms sphericalInd
#print axioms sphericalInd_infty
#print axioms sphericalInd_coe
#print axioms sphericalInd_eventually_zero_nhds_infty
#print axioms reachable_by_bookPath_of_isRegion
#print axioms theorem13_11
#print axioms theorem13_12

end RudinRCA.Chapter13
