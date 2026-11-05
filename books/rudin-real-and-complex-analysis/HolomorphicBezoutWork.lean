import RudinRCA.Chapter15
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
Draft prerequisites for Rudin 15.15. The interpolation input in the two-function
lemma is explicit: it is the interface being constructed for 15.13, not an
axiom or a completed assertion of the printed Bézout theorem. No check yet.
-/

noncomputable section

open Filter Set WithTop.LinearOrderedAddCommGroup
open scoped Topology

namespace RudinRCA.Chapter15

/-- A holomorphic denominator of finite order divides a holomorphic numerator
exactly when its pointwise orders do not exceed the numerator orders. The
numerator may vanish identically on some components. -/
theorem exists_holomorphic_quotient_of_order_le {Ω : Set ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Ω) (hg : AnalyticOnNhd ℂ g Ω)
    (hgfinite : ∀ z ∈ Ω, analyticOrderAt g z ≠ ⊤)
    (horder : ∀ z ∈ Ω, analyticOrderAt g z ≤ analyticOrderAt f z) :
    ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q Ω ∧ ∀ z ∈ Ω, f z = q z * g z := by
  let q : ℂ → ℂ := toMeromorphicNFOn (f / g) Ω
  have hmer : MeromorphicOn (f / g) Ω :=
    fun z hz ↦ (hf z hz).meromorphicAt.div (hg z hz).meromorphicAt
  have hnf : ∀ z ∈ Ω, MeromorphicNFAt q z :=
    fun z hz ↦ meromorphicNFOn_toMeromorphicNFOn (f / g) Ω hz
  have hqorder : ∀ z ∈ Ω, 0 ≤ meromorphicOrderAt q z := by
    intro z hz
    dsimp only [q]
    rw [meromorphicOrderAt_toMeromorphicNFOn hmer hz,
      meromorphicOrderAt_div (hf z hz).meromorphicAt (hg z hz).meromorphicAt,
      (hf z hz).meromorphicOrderAt_eq, (hg z hz).meromorphicOrderAt_eq]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hgfinite z hz)
    by_cases hftop : analyticOrderAt f z = ⊤
    · simp [hftop]
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hftop
      have hnm : n ≤ m := by
        have h := horder z hz
        rw [← hn, ← hm] at h
        exact_mod_cast h
      rw [← hn, ← hm]
      change (0 : WithTop ℤ) ≤ ((m : ℤ) - (n : ℤ) : ℤ)
      exact_mod_cast (sub_nonneg.mpr (by exact_mod_cast hnm) : (0 : ℤ) ≤ m - n)
  have hqa : AnalyticOnNhd ℂ q Ω :=
    fun z hz ↦ (hnf z hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hqorder z hz)
  refine ⟨q, hqa, ?_⟩
  intro z hz
  have hgne : ∀ᶠ w in 𝓝[≠] z, g w ≠ 0 :=
    (hg z hz).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun h ↦ hgfinite z hz (analyticOrderAt_eq_top.mpr h))
  have heq : (fun w ↦ q w * g w) =ᶠ[𝓝[≠] z] f := by
    filter_upwards [hmer.toMeromorphicNFOn_eq_self_on_nhdsNE hz, hgne] with w hw hgw
    change q w = f w / g w at hw
    rw [hw, div_mul_cancel₀ _ hgw]
  have heqnhds : (fun w ↦ q w * g w) =ᶠ[𝓝 z] f :=
    (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      ((hqa z hz).continuousAt.mul (hg z hz).continuousAt) (hf z hz).continuousAt).mp heq
  exact heqnhds.eq_of_nhds.symm

/-- Finite analytic orders make the actual zero set locally discrete throughout
the domain, not merely discrete as a subspace. -/
theorem holomorphic_zeros_no_accPt {Ω : Set ℂ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g Ω) (hgfinite : ∀ z ∈ Ω, analyticOrderAt g z ≠ ⊤) :
    ∀ z ∈ Ω, ¬ AccPt z (𝓟 {w | w ∈ Ω ∧ g w = 0}) := by
  intro z hz
  rw [accPt_iff_frequently_nhdsNE, not_frequently]
  have hgne : ∀ᶠ w in 𝓝[≠] z, g w ≠ 0 :=
    (hg z hz).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun h ↦ hgfinite z hz (analyticOrderAt_eq_top.mpr h))
  filter_upwards [hgne] with w hw
  exact fun h ↦ hw h.2

/-- The first Bézout step: two holomorphic functions without a common zero
generate one, provided the second is not locally identically zero. The genuine
15.13 interpolation theorem is supplied by its exact analytic-germ interface.
The all-components form of 15.15 additionally requires the gluing step below
this helper; this helper alone does not claim that full theorem. -/
theorem holomorphic_bezout_pair_finite_second_using_interpolation
    (hinterpolate : ∀ {Ω A : Set ℂ}, IsOpen Ω → A ⊆ Ω →
      (∀ a ∈ Ω, ¬ AccPt a (𝓟 A)) → ∀ (m : ℂ → ℕ) (G : ℂ → ℂ → ℂ),
      (∀ a ∈ A, AnalyticAt ℂ (G a) a) →
      ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H Ω ∧
        ∀ a ∈ A, (m a : ℕ∞) ≤ analyticOrderAt (fun z ↦ H z - G a z) a)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Ω) (hg : AnalyticOnNhd ℂ g Ω)
    (hgfinite : ∀ z ∈ Ω, analyticOrderAt g z ≠ ⊤)
    (hnocommon : ∀ z ∈ Ω, f z ≠ 0 ∨ g z ≠ 0) :
    ∃ H Q : ℂ → ℂ, AnalyticOnNhd ℂ H Ω ∧ AnalyticOnNhd ℂ Q Ω ∧
      ∀ z ∈ Ω, H z * f z + Q z * g z = 1 := by
  let A : Set ℂ := {z | z ∈ Ω ∧ g z = 0}
  have hA : A ⊆ Ω := fun _ hz ↦ hz.1
  have hfa : ∀ a ∈ A, f a ≠ 0 :=
    fun a ha ↦ (hnocommon a ha.1).resolve_right (not_not.mpr ha.2)
  obtain ⟨H, hH, hmatch⟩ := hinterpolate hΩ hA (holomorphic_zeros_no_accPt hg hgfinite)
    (analyticOrderNatAt g) (fun _ z ↦ (f z)⁻¹)
    (fun a ha ↦ (hf a ha.1).inv (hfa a ha))
  let N : ℂ → ℂ := fun z ↦ 1 - H z * f z
  have hN : AnalyticOnNhd ℂ N Ω := fun z hz ↦ analyticAt_const.sub ((hH z hz).mul (hf z hz))
  have hNorder : ∀ z ∈ Ω, analyticOrderAt g z ≤ analyticOrderAt N z := by
    intro z hz
    by_cases hgz : g z = 0
    · have hzA : z ∈ A := ⟨hz, hgz⟩
      have hfnz := hfa z hzA
      have hinv : AnalyticAt ℂ (fun w ↦ (f w)⁻¹) z := (hf z hz).inv hfnz
      have heq : N =ᶠ[𝓝 z] (fun w ↦ -(H w - (f w)⁻¹) * f w) := by
        filter_upwards [(hf z hz).continuousAt.eventually_ne hfnz] with w hw
        dsimp only [N]
        rw [neg_sub, sub_mul, inv_mul_cancel₀ hw]
      rw [analyticOrderAt_congr heq]
      change analyticOrderAt g z ≤ analyticOrderAt (- (H - fun w ↦ (f w)⁻¹) * f) z
      rw [analyticOrderAt_mul ((hH z hz).sub hinv).neg (hf z hz),
        analyticOrderAt_neg, (hf z hz).analyticOrderAt_eq_zero.mpr hfnz, add_zero]
      simpa only [Nat.cast_analyticOrderNatAt (hgfinite z hz)] using hmatch z hzA
    · rw [(hg z hz).analyticOrderAt_eq_zero.mpr hgz]
      exact bot_le
  obtain ⟨Q, hQ, hQN⟩ := exists_holomorphic_quotient_of_order_le hN hg hgfinite hNorder
  refine ⟨H, Q, hH, hQ, ?_⟩
  intro z hz
  rw [← hQN z hz]
  dsimp only [N]
  ring

/-- On an open domain, both the finite-order locus and the locally-zero locus
of an analytic function are open in the plane. -/
theorem isOpen_analytic_order_loci {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Ω) :
    IsOpen {z | z ∈ Ω ∧ analyticOrderAt f z ≠ ⊤} ∧
      IsOpen {z | z ∈ Ω ∧ analyticOrderAt f z = ⊤} := by
  have hcl := hf.isClopen_setOfPred_analyticOrderAt_eq_top
  constructor
  · have h : IsOpen (Ω ∩ {z | analyticOrderAt f z ≠ ⊤}) :=
      hΩ.inter_preimage_val_iff.mp hcl.isClosed.isOpen_compl
    exact h
  · have h : IsOpen (Ω ∩ {z | analyticOrderAt f z = ⊤}) :=
      hΩ.inter_preimage_val_iff.mp hcl.isOpen
    exact h

/-- Analytic functions glue across disjoint open parts. All functions are total
extensions, and only the specified domain is covered. -/
theorem analyticOnNhd_piecewise_open_partition {Ω U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hcover : Ω ⊆ U ∪ V) (hdis : Disjoint U V)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g V) :
    AnalyticOnNhd ℂ (fun z ↦ if z ∈ U then f z else g z) Ω := by
  classical
  intro z hz
  by_cases hzU : z ∈ U
  · apply (hf z hzU).congr
    filter_upwards [hU.mem_nhds hzU] with w hw
    exact (if_pos hw).symm
  · have hzV : z ∈ V := (hcover hz).resolve_left hzU
    apply (hg z hzV).congr
    filter_upwards [hV.mem_nhds hzV] with w hw
    exact (if_neg (fun hwU ↦ disjoint_left.mp hdis hwU hw)).symm

/-- Two functions without a common zero generate one on an arbitrary open
domain, including components where either generator is identically zero.
The sole remaining theorem input is the actual 15.13 interpolation interface. -/
theorem holomorphic_bezout_pair_using_interpolation
    (hinterpolate : ∀ {Ω A : Set ℂ}, IsOpen Ω → A ⊆ Ω →
      (∀ a ∈ Ω, ¬ AccPt a (𝓟 A)) → ∀ (m : ℂ → ℕ) (G : ℂ → ℂ → ℂ),
      (∀ a ∈ A, AnalyticAt ℂ (G a) a) →
      ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H Ω ∧
        ∀ a ∈ A, (m a : ℕ∞) ≤ analyticOrderAt (fun z ↦ H z - G a z) a)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Ω) (hg : AnalyticOnNhd ℂ g Ω)
    (hnocommon : ∀ z ∈ Ω, f z ≠ 0 ∨ g z ≠ 0) :
    ∃ H Q : ℂ → ℂ, AnalyticOnNhd ℂ H Ω ∧ AnalyticOnNhd ℂ Q Ω ∧
      ∀ z ∈ Ω, H z * f z + Q z * g z = 1 := by
  classical
  let U : Set ℂ := {z | z ∈ Ω ∧ analyticOrderAt g z ≠ ⊤}
  let V : Set ℂ := {z | z ∈ Ω ∧ analyticOrderAt g z = ⊤}
  obtain ⟨hU, hV⟩ := isOpen_analytic_order_loci hΩ hg
  have hcover : Ω ⊆ U ∪ V := by
    intro z hz
    by_cases ho : analyticOrderAt g z = ⊤
    · exact Or.inr ⟨hz, ho⟩
    · exact Or.inl ⟨hz, ho⟩
  have hdis : Disjoint U V := disjoint_left.mpr (fun z hu hv ↦ hu.2 hv.2)
  obtain ⟨H, Q, hH, hQ, heq⟩ := holomorphic_bezout_pair_finite_second_using_interpolation
    hinterpolate hU (hf.mono (fun _ hz ↦ hz.1)) (hg.mono (fun _ hz ↦ hz.1))
    (fun _ hz ↦ hz.2) (fun z hz ↦ hnocommon z hz.1)
  have hgz : ∀ z ∈ V, g z = 0 :=
    fun _ hz ↦ (analyticOrderAt_eq_top.mp hz.2).eq_of_nhds
  have hfnz : ∀ z ∈ V, f z ≠ 0 :=
    fun z hz ↦ (hnocommon z hz.1).resolve_right (not_not.mpr (hgz z hz))
  have hfi : AnalyticOnNhd ℂ (fun z ↦ (f z)⁻¹) V :=
    fun z hz ↦ (hf z hz.1).inv (hfnz z hz)
  refine ⟨(fun z ↦ if z ∈ U then H z else (f z)⁻¹),
    (fun z ↦ if z ∈ U then Q z else 0),
    analyticOnNhd_piecewise_open_partition hU hV hcover hdis hH hfi,
    analyticOnNhd_piecewise_open_partition hU hV hcover hdis hQ
      (fun _ _ ↦ analyticAt_const), ?_⟩
  intro z hz
  by_cases hzU : z ∈ U
  · simpa only [if_pos hzU] using heq z hzU
  · have hzV := (hcover hz).resolve_left hzU
    simp only [if_neg hzU, zero_mul, add_zero, inv_mul_cancel₀ (hfnz z hzV)]

/-- Dividing by the full finite vanishing order leaves a nonzero value. -/
theorem quotient_nonzero_of_equal_orders {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f q F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F Ω) (hq : AnalyticOnNhd ℂ q Ω)
    (heq : ∀ z ∈ Ω, f z = F z * q z) {z : ℂ} (hz : z ∈ Ω)
    (hqfinite : analyticOrderAt q z ≠ ⊤)
    (horder : analyticOrderAt f z = analyticOrderAt q z) : F z ≠ 0 := by
  have hevent : f =ᶠ[𝓝 z] F * q := by
    filter_upwards [hΩ.mem_nhds hz] with w hw
    exact heq w hw
  have ho : analyticOrderAt F z + analyticOrderAt q z = analyticOrderAt q z := by
    rw [← analyticOrderAt_mul (hF z hz) (hq z hz), ← analyticOrderAt_congr hevent]
    exact horder
  have hFzero : analyticOrderAt F z = 0 :=
    ENat.add_left_injective_of_ne_top hqfinite (by simpa using ho)
  exact (hF z hz).analyticOrderAt_eq_zero.mp hFzero

/-- If at least one generator has finite order at each point, their common
zeros have no accumulation in the domain. The finite generator can vary from
one connected component to another. -/
theorem common_zeros_no_accPt {Ω : Set ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Ω) (hg : AnalyticOnNhd ℂ g Ω)
    (hfinite : ∀ z ∈ Ω, analyticOrderAt f z ≠ ⊤ ∨ analyticOrderAt g z ≠ ⊤) :
    ∀ z ∈ Ω, ¬ AccPt z (𝓟 {w | w ∈ Ω ∧ f w = 0 ∧ g w = 0}) := by
  intro z hz
  rw [accPt_iff_frequently_nhdsNE, not_frequently]
  rcases hfinite z hz with hfz | hgz
  · have hn := (hf z hz).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun h ↦ hfz (analyticOrderAt_eq_top.mpr h))
    filter_upwards [hn] with w hw
    exact fun h ↦ hw h.2.1
  · have hn := (hg z hz).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun h ↦ hgz (analyticOrderAt_eq_top.mpr h))
    filter_upwards [hn] with w hw
    exact fun h ↦ hw h.2.2

/-- A common divisor with the minimum of the two vanishing orders. This is
the exact use of 15.11 in the Bézout argument. Components on which both
generators are identically zero are handled by a subsequent open gluing. -/
theorem holomorphic_common_divisor_using_prescribed_zeros
    (hprescribed : ∀ {Ω A : Set ℂ}, IsOpen Ω → A ⊆ Ω →
      (∀ z ∈ Ω, ¬ AccPt z (𝓟 A)) → ∀ m : ℂ → ℕ, (∀ z ∈ A, 0 < m z) →
      ∃ q : ℂ → ℂ, DifferentiableOn ℂ q Ω ∧
        (∀ z ∈ Ω, q z = 0 ↔ z ∈ A) ∧
        (∀ z ∈ A, analyticOrderAt q z = (m z : ℕ∞)))
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Ω) (hg : AnalyticOnNhd ℂ g Ω)
    (hfinite : ∀ z ∈ Ω, analyticOrderAt f z ≠ ⊤ ∨ analyticOrderAt g z ≠ ⊤) :
    ∃ q F G : ℂ → ℂ, AnalyticOnNhd ℂ q Ω ∧ AnalyticOnNhd ℂ F Ω ∧
      AnalyticOnNhd ℂ G Ω ∧
      (∀ z ∈ Ω, f z = F z * q z ∧ g z = G z * q z) ∧
      (∀ z ∈ Ω, F z ≠ 0 ∨ G z ≠ 0) := by
  let A : Set ℂ := {z | z ∈ Ω ∧ f z = 0 ∧ g z = 0}
  let m : ℂ → ℕ := fun z ↦ (min (analyticOrderAt f z) (analyticOrderAt g z)).toNat
  have hminfinite : ∀ z ∈ Ω, min (analyticOrderAt f z) (analyticOrderAt g z) ≠ ⊤ := by
    intro z hz
    rcases hfinite z hz with hfz | hgz
    · exact ne_top_of_le_ne_top hfz (min_le_left _ _)
    · exact ne_top_of_le_ne_top hgz (min_le_right _ _)
  have hm : ∀ z ∈ A, 0 < m z := by
    intro z hz
    apply ENat.toNat_pos _ (hminfinite z hz.1)
    exact ne_of_gt (lt_min
      (pos_iff_ne_zero.mpr ((hf z hz.1).analyticOrderAt_ne_zero.mpr hz.2.1))
      (pos_iff_ne_zero.mpr ((hg z hz.1).analyticOrderAt_ne_zero.mpr hz.2.2)))
  obtain ⟨q, hqd, hqzero, hqorderA⟩ := hprescribed hΩ (fun _ hz ↦ hz.1)
    (common_zeros_no_accPt hf hg hfinite) m hm
  have hq : AnalyticOnNhd ℂ q Ω := hqd.analyticOnNhd hΩ
  have hqorder : ∀ z ∈ Ω,
      analyticOrderAt q z = min (analyticOrderAt f z) (analyticOrderAt g z) := by
    intro z hz
    by_cases hzA : z ∈ A
    · rw [hqorderA z hzA]
      exact ENat.natCast_toNat (hminfinite z hz)
    · have hqz : q z ≠ 0 := fun h ↦ hzA ((hqzero z hz).1 h)
      rw [(hq z hz).analyticOrderAt_eq_zero.mpr hqz]
      by_cases hfz : f z = 0
      · have hgz : g z ≠ 0 := fun h ↦ hzA ⟨hz, hfz, h⟩
        simp only [(hg z hz).analyticOrderAt_eq_zero.mpr hgz, min_zero]
      · simp only [(hf z hz).analyticOrderAt_eq_zero.mpr hfz, zero_min]
  have hqfinite : ∀ z ∈ Ω, analyticOrderAt q z ≠ ⊤ :=
    fun z hz ↦ by rw [hqorder z hz]; exact hminfinite z hz
  obtain ⟨F, hF, hFf⟩ := exists_holomorphic_quotient_of_order_le hf hq hqfinite
    (fun z hz ↦ (hqorder z hz).trans_le (min_le_left _ _))
  obtain ⟨G, hG, hGg⟩ := exists_holomorphic_quotient_of_order_le hg hq hqfinite
    (fun z hz ↦ (hqorder z hz).trans_le (min_le_right _ _))
  refine ⟨q, F, G, hq, hF, hG, fun z hz ↦ ⟨hFf z hz, hGg z hz⟩, ?_⟩
  intro z hz
  rcases le_total (analyticOrderAt f z) (analyticOrderAt g z) with hfg | hgf
  · apply Or.inl
    apply quotient_nonzero_of_equal_orders hΩ hF hq hFf hz (hqfinite z hz)
    rw [hqorder z hz, min_eq_left hfg]
  · apply Or.inr
    apply quotient_nonzero_of_equal_orders hΩ hG hq hGg hz (hqfinite z hz)
    rw [hqorder z hz, min_eq_right hgf]

/-- Two arbitrary holomorphic generators have a common generator that is an
explicit linear combination of them. All-zero components are retained and
glued with the zero generator. This theorem is conditional only on the genuine
15.11 and 15.13 interfaces, whose constructions are checked separately. -/
theorem holomorphic_pair_principal_using_zero_and_jet_constructions
    (hprescribed : ∀ {Ω A : Set ℂ}, IsOpen Ω → A ⊆ Ω →
      (∀ z ∈ Ω, ¬ AccPt z (𝓟 A)) → ∀ m : ℂ → ℕ, (∀ z ∈ A, 0 < m z) →
      ∃ q : ℂ → ℂ, DifferentiableOn ℂ q Ω ∧
        (∀ z ∈ Ω, q z = 0 ↔ z ∈ A) ∧
        (∀ z ∈ A, analyticOrderAt q z = (m z : ℕ∞)))
    (hinterpolate : ∀ {Ω A : Set ℂ}, IsOpen Ω → A ⊆ Ω →
      (∀ a ∈ Ω, ¬ AccPt a (𝓟 A)) → ∀ (m : ℂ → ℕ) (G : ℂ → ℂ → ℂ),
      (∀ a ∈ A, AnalyticAt ℂ (G a) a) →
      ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H Ω ∧
        ∀ a ∈ A, (m a : ℕ∞) ≤ analyticOrderAt (fun z ↦ H z - G a z) a)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Ω) (hg : AnalyticOnNhd ℂ g Ω) :
    ∃ q H Q F G : ℂ → ℂ, AnalyticOnNhd ℂ q Ω ∧
      AnalyticOnNhd ℂ H Ω ∧ AnalyticOnNhd ℂ Q Ω ∧
      AnalyticOnNhd ℂ F Ω ∧ AnalyticOnNhd ℂ G Ω ∧
      ∀ z ∈ Ω, q z = H z * f z + Q z * g z ∧
        f z = F z * q z ∧ g z = G z * q z := by
  classical
  let U : Set ℂ := {z | z ∈ Ω ∧
    (analyticOrderAt f z ≠ ⊤ ∨ analyticOrderAt g z ≠ ⊤)}
  let V : Set ℂ := {z | z ∈ Ω ∧
    analyticOrderAt f z = ⊤ ∧ analyticOrderAt g z = ⊤}
  obtain ⟨hfopen, hfzeroopen⟩ := isOpen_analytic_order_loci hΩ hf
  obtain ⟨hgopen, hgzeroopen⟩ := isOpen_analytic_order_loci hΩ hg
  have hU : IsOpen U := by
    convert hfopen.union hgopen using 1
    ext z
    simp only [U, mem_setOf_eq, mem_union, and_or_left]
  have hV : IsOpen V := by
    convert hfzeroopen.inter hgzeroopen using 1
    ext z
    simp only [V, mem_setOf_eq, mem_inter_iff, and_assoc, and_left_comm, and_self]
  have hcover : Ω ⊆ U ∪ V := by
    intro z hz
    by_cases hfz : analyticOrderAt f z = ⊤
    · by_cases hgz : analyticOrderAt g z = ⊤
      · exact Or.inr ⟨hz, hfz, hgz⟩
      · exact Or.inl ⟨hz, Or.inr hgz⟩
    · exact Or.inl ⟨hz, Or.inl hfz⟩
  have hdis : Disjoint U V := by
    apply disjoint_left.mpr
    intro z hzU hzV
    exact hzU.2.elim (fun h ↦ h hzV.2.1) (fun h ↦ h hzV.2.2)
  have hzero : ∀ z ∈ V, f z = 0 ∧ g z = 0 :=
    fun z hz ↦ ⟨(analyticOrderAt_eq_top.mp hz.2.1).eq_of_nhds,
      (analyticOrderAt_eq_top.mp hz.2.2).eq_of_nhds⟩
  obtain ⟨q, F, G, hq, hF, hG, hdiv, hnocommon⟩ :=
    holomorphic_common_divisor_using_prescribed_zeros hprescribed hU
      (hf.mono (fun _ hz ↦ hz.1)) (hg.mono (fun _ hz ↦ hz.1)) (fun _ hz ↦ hz.2)
  obtain ⟨H, Q, hH, hQ, hbezout⟩ :=
    holomorphic_bezout_pair_using_interpolation hinterpolate hU hF hG hnocommon
  let glue : (ℂ → ℂ) → ℂ → ℂ := fun k z ↦ if z ∈ U then k z else 0
  have hglue {k : ℂ → ℂ} (hk : AnalyticOnNhd ℂ k U) : AnalyticOnNhd ℂ (glue k) Ω :=
    analyticOnNhd_piecewise_open_partition hU hV hcover hdis hk
      (fun _ _ ↦ analyticAt_const)
  refine ⟨glue q, glue H, glue Q, glue F, glue G,
    hglue hq, hglue hH, hglue hQ, hglue hF, hglue hG, ?_⟩
  intro z hz
  by_cases hzU : z ∈ U
  · simp only [glue, if_pos hzU]
    refine ⟨?_, (hdiv z hzU).1, (hdiv z hzU).2⟩
    calc
      q z = 1 * q z := (one_mul _).symm
      _ = (H z * F z + Q z * G z) * q z := by rw [hbezout z hzU]
      _ = H z * f z + Q z * g z := by rw [(hdiv z hzU).1, (hdiv z hzU).2]; ring
  · have hzV := (hcover hz).resolve_left hzU
    simp only [glue, if_neg hzU, (hzero z hzV).1, (hzero z hzV).2,
      zero_mul, add_zero, and_self]

/-- Finite induction is purely algebraic once the two-generator construction
is available. The empty generating family has generator zero. -/
theorem holomorphic_finite_generators_principal_of_pair {Ω : Set ℂ}
    (hpair : ∀ f g : ℂ → ℂ, AnalyticOnNhd ℂ f Ω → AnalyticOnNhd ℂ g Ω →
      ∃ q H Q F G : ℂ → ℂ, AnalyticOnNhd ℂ q Ω ∧
        AnalyticOnNhd ℂ H Ω ∧ AnalyticOnNhd ℂ Q Ω ∧
        AnalyticOnNhd ℂ F Ω ∧ AnalyticOnNhd ℂ G Ω ∧
        ∀ z ∈ Ω, q z = H z * f z + Q z * g z ∧
          f z = F z * q z ∧ g z = G z * q z) :
    ∀ n : ℕ, ∀ g : Fin n → ℂ → ℂ, (∀ i, AnalyticOnNhd ℂ (g i) Ω) →
      ∃ q : ℂ → ℂ, ∃ a b : Fin n → ℂ → ℂ,
        AnalyticOnNhd ℂ q Ω ∧ (∀ i, AnalyticOnNhd ℂ (a i) Ω) ∧
        (∀ i, AnalyticOnNhd ℂ (b i) Ω) ∧
        (∀ z ∈ Ω, q z = ∑ i, a i z * g i z) ∧
        (∀ i z, z ∈ Ω → g i z = b i z * q z) := by
  intro n
  induction n with
  | zero =>
    intro g hg
    refine ⟨(fun _ ↦ 0), Fin.elim0, Fin.elim0, (fun _ _ ↦ analyticAt_const),
      (fun i ↦ Fin.elim0 i), (fun i ↦ Fin.elim0 i), ?_, ?_⟩
    · intro z hz; simp
    · intro i; exact Fin.elim0 i
  | succ n ih =>
    intro g hg
    obtain ⟨q₀, a₀, b₀, hq₀, ha₀, hb₀, heq₀, hdiv₀⟩ :=
      ih (fun i ↦ g i.succ) (fun i ↦ hg i.succ)
    obtain ⟨q, H, Q, F, G, hq, hH, hQ, hF, hG, heq⟩ := hpair (g 0) q₀ (hg 0) hq₀
    let a : Fin (n + 1) → ℂ → ℂ := Fin.cases H (fun i z ↦ Q z * a₀ i z)
    let b : Fin (n + 1) → ℂ → ℂ := Fin.cases F (fun i z ↦ b₀ i z * G z)
    refine ⟨q, a, b, hq, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases hH (fun j ↦ ?_) i
      exact fun z hz ↦ (hQ z hz).mul (ha₀ j z hz)
    · intro i
      refine Fin.cases hF (fun j ↦ ?_) i
      exact fun z hz ↦ (hb₀ j z hz).mul (hG z hz)
    · intro z hz
      rw [Fin.sum_univ_succ]
      simp only [a, Fin.cases_zero, Fin.cases_succ]
      calc
        q z = H z * g 0 z + Q z * q₀ z := (heq z hz).1
        _ = H z * g 0 z + Q z * ∑ i, a₀ i z * g i.succ z := by rw [heq₀ z hz]
        _ = H z * g 0 z + ∑ i, (Q z * a₀ i z) * g i.succ z := by
          rw [Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          exact (mul_assoc _ _ _).symm
    · intro i
      refine Fin.cases (fun z hz ↦ ?_) (fun j z hz ↦ ?_) i
      · simpa only [b, Fin.cases_zero] using (heq z hz).2.1
      · simp only [b, Fin.cases_succ]
        rw [hdiv₀ j z hz, (heq z hz).2.2]
        ring

/-- Reindexing the finite-family construction gives the same coefficient
identities for an arbitrary finite index type, including an empty one. -/
theorem holomorphic_fintype_generators_principal_of_pair {Ω : Set ℂ}
    (hpair : ∀ f g : ℂ → ℂ, AnalyticOnNhd ℂ f Ω → AnalyticOnNhd ℂ g Ω →
      ∃ q H Q F G : ℂ → ℂ, AnalyticOnNhd ℂ q Ω ∧
        AnalyticOnNhd ℂ H Ω ∧ AnalyticOnNhd ℂ Q Ω ∧
        AnalyticOnNhd ℂ F Ω ∧ AnalyticOnNhd ℂ G Ω ∧
        ∀ z ∈ Ω, q z = H z * f z + Q z * g z ∧
          f z = F z * q z ∧ g z = G z * q z)
    {ι : Type*} [Fintype ι] (g : ι → ℂ → ℂ) (hg : ∀ i, AnalyticOnNhd ℂ (g i) Ω) :
    ∃ q : ℂ → ℂ, ∃ a b : ι → ℂ → ℂ,
      AnalyticOnNhd ℂ q Ω ∧ (∀ i, AnalyticOnNhd ℂ (a i) Ω) ∧
      (∀ i, AnalyticOnNhd ℂ (b i) Ω) ∧
      (∀ z ∈ Ω, q z = ∑ i, a i z * g i z) ∧
      (∀ i z, z ∈ Ω → g i z = b i z * q z) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  obtain ⟨q, a, b, hq, ha, hb, heq, hdiv⟩ :=
    holomorphic_finite_generators_principal_of_pair hpair (Fintype.card ι)
      (fun i ↦ g (e.symm i)) (fun i ↦ hg (e.symm i))
  refine ⟨q, (fun i ↦ a (e i)), (fun i ↦ b (e i)), hq,
    (fun i ↦ ha (e i)), (fun i ↦ hb (e i)), ?_, ?_⟩
  · intro z hz
    rw [heq z hz]
    symm
    exact Fintype.sum_equiv e _ _ (fun i ↦ by simp)
  · intro i z hz
    simpa only [Equiv.symm_apply_apply] using hdiv (e i) z hz

#print axioms exists_holomorphic_quotient_of_order_le
#print axioms holomorphic_zeros_no_accPt
#print axioms holomorphic_bezout_pair_finite_second_using_interpolation
#print axioms isOpen_analytic_order_loci
#print axioms analyticOnNhd_piecewise_open_partition
#print axioms holomorphic_bezout_pair_using_interpolation
#print axioms quotient_nonzero_of_equal_orders
#print axioms common_zeros_no_accPt
#print axioms holomorphic_common_divisor_using_prescribed_zeros
#print axioms holomorphic_pair_principal_using_zero_and_jet_constructions
#print axioms holomorphic_finite_generators_principal_of_pair
#print axioms holomorphic_fintype_generators_principal_of_pair

end RudinRCA.Chapter15
