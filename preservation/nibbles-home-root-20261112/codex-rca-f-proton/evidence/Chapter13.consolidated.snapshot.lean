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

/-!
# Rudin RCA, Chapter 13 — Approximation by Rational Functions

Working development for issue #42 at the fixed Lean/Mathlib pins.
Printed scope and exact remaining obligations: `SCOPING-F.md` and `PROGRESS.md`.
A proof of one assertion is not counted as an entire numbered node.
Exercises are excluded. No chapter completion is claimed here.
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

end RudinRCA.Chapter13
