import RudinRCA.Chapter15
import SphereWork
import BoundaryProductGeometryWork
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Connected.LocallyConnected

/-! The normalized boundary-pole product for Rudin 15.11. Draft, not yet checked. -/

noncomputable section

open Filter Set Finset Metric
open scoped Topology OnePoint

namespace RudinRCA.Chapter15

def boundaryFactor (p : ℕ) (a b z : ℂ) : ℂ :=
  elementaryFactor p ((a - b) / (z - b))

def boundaryInfinityFactor (p : ℕ) (a b w : ℂ) : ℂ :=
  elementaryFactor p ((a - b) * w / (1 - b * w))

theorem analyticAt_boundaryFactor (p : ℕ) (a b : ℂ) {z : ℂ} (hzb : z ≠ b) :
    AnalyticAt ℂ (boundaryFactor p a b) z := by
  exact ((differentiable_elementaryFactor p).analyticAt ((a - b) / (z - b))).comp
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzb))

theorem analyticOrderAt_boundaryFactor (p : ℕ) {a b z : ℂ} (hab : a ≠ b) (hzb : z ≠ b) :
    analyticOrderAt (boundaryFactor p a b) z = if z = a then 1 else 0 := by
  have hg : AnalyticAt ℂ (fun w : ℂ ↦ (a - b) / (w - b)) z :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzb)
  have hd : HasDerivAt (fun w : ℂ ↦ (a - b) / (w - b))
      (-(a - b) / (z - b) ^ 2) z := by
    simpa using (hasDerivAt_const z (a - b)).div ((hasDerivAt_id z).sub_const b)
      (sub_ne_zero.mpr hzb)
  change analyticOrderAt (elementaryFactor p ∘ (fun w : ℂ ↦ (a - b) / (w - b))) z = _
  rw [analyticOrderAt_comp_of_deriv_ne_zero hg (by rw [hd.deriv];
    exact div_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr hab))
      (pow_ne_zero 2 (sub_ne_zero.mpr hzb))), analyticOrderAt_elementaryFactor]
  simp only [div_eq_one_iff_eq (sub_ne_zero.mpr hzb), sub_left_inj, eq_comm]

theorem boundaryFactor_eq_zero_iff (p : ℕ) (a b : ℂ) {z : ℂ} (hzb : z ≠ b) :
    boundaryFactor p a b z = 0 ↔ z = a := by
  simp only [boundaryFactor, elementaryFactor_eq_zero_iff,
    div_eq_one_iff_eq (sub_ne_zero.mpr hzb), sub_left_inj, eq_comm]

theorem component_nonzero_of_order_ne_top {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hfinite : ∀ z ∈ Ω, analyticOrderAt f z ≠ ⊤) :
    ∀ z ∈ Ω, ∃ w ∈ connectedComponentIn Ω z, f w ≠ 0 := by
  intro z hz
  by_contra hn
  push_neg at hn
  apply hfinite z hz
  apply analyticOrderAt_eq_top.mpr
  filter_upwards [hΩ.connectedComponentIn.mem_nhds (mem_connectedComponentIn hz)] with w hw
  exact hn w hw

theorem boundary_errors_locally_uniform (a b : ℕ → ℂ) {C : Set ℂ}
    (hC : IsClosed C) (hCne : C.Nonempty) (hb : ∀ n, b n ∈ C)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0)) :
    TendstoLocallyUniformlyOn
      (fun N z ↦ ∑ n ∈ range N, ‖1 - boundaryFactor n (a n) (b n) z‖)
      (fun z ↦ ∑' n, ‖1 - boundaryFactor n (a n) (b n) z‖) atTop Cᶜ := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hC.isOpen_compl).2
  intro K hKC hK
  have hgeo : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1)) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).comp_injective
      (fun n m h ↦ Nat.add_right_cancel h)
  apply tendstoUniformlyOn_tsum_nat_eventually hgeo
  filter_upwards [boundary_ratios_small_on_compact a b hC hCne hb hsmall hK hKC]
    with n hn z hz
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact (norm_one_sub_elementaryFactor_le n _ ((hn z hz).trans (by norm_num))).trans
    (pow_le_pow_left₀ (norm_nonneg _) (hn z hz))

/-- The finite-plane part of the normalized construction, with repeated zeros
counted by the exact indicator sum. -/
theorem boundary_product_on_complement (a b : ℕ → ℂ) {C : Set ℂ}
    (hC : IsClosed C) (hCne : C.Nonempty) (ha : ∀ n, a n ∉ C) (hb : ∀ n, b n ∈ C)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0)) :
    let f := fun z ↦ ∏' n, boundaryFactor n (a n) (b n) z
    TendstoLocallyUniformlyOn
      (fun N z ↦ ∏ n ∈ range N, boundaryFactor n (a n) (b n) z) f atTop Cᶜ ∧
    DifferentiableOn ℂ f Cᶜ ∧
    ∀ z ∈ Cᶜ, (f z = 0 ↔ ∃ n, z = a n) ∧ analyticOrderAt f z ≠ ⊤ ∧
      analyticOrderNatAt f z = ∑' n, if z = a n then (1 : ℕ) else 0 := by
  let F : ℕ → ℂ → ℂ := fun n z ↦ boundaryFactor n (a n) (b n) z
  have hab (n : ℕ) : a n ≠ b n := fun h ↦ ha n (h.symm ▸ hb n)
  have hzb {z : ℂ} (hz : z ∈ Cᶜ) (n : ℕ) : z ≠ b n := fun h ↦ hz (h.symm ▸ hb n)
  have hF : ∀ n, DifferentiableOn ℂ (F n) Cᶜ := by
    intro n z hz
    exact (analyticAt_boundaryFactor n (a n) (b n) (hzb hz n)).differentiableAt
      .differentiableWithinAt
  have hnonzero : ∀ n z, z ∈ Cᶜ →
      ∃ w ∈ connectedComponentIn Cᶜ z, F n w ≠ 0 := by
    intro n
    apply component_nonzero_of_order_ne_top hC.isOpen_compl
    intro z hz
    rw [show analyticOrderAt (F n) z = if z = a n then 1 else 0 from
      analyticOrderAt_boundaryFactor n (hab n) (hzb hz n)]
    split_ifs <;> simp
  have herr := boundary_errors_locally_uniform a b hC hCne hb hsmall
  obtain ⟨hlim, hhol, horder⟩ := holomorphic_product_multiplicity
    hC.isOpen_compl hF hnonzero ⟨_, herr⟩
  refine ⟨hlim, hhol, ?_⟩
  intro z hz
  obtain ⟨_, hfinite, hm, _⟩ := horder z hz
  have hsum : Summable (fun n ↦ ‖F n z - 1‖) := by
    simpa only [norm_sub_rev] using
      ((hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ norm_nonneg _) _).2
        (herr.tendsto_at hz)).summable
  have hzero : (∏' n, F n z) = 0 ↔ ∃ n, z = a n := by
    constructor
    · intro hprod
      by_contra hn
      push_neg at hn
      have hnone : ∀ n, F n z ≠ 0 := by
        intro n
        exact fun h ↦ hn n ((boundaryFactor_eq_zero_iff n (a n) (b n) (hzb hz n)).1 h)
      have hone (v : ℂ) : 1 + (v - 1) = v := by ring
      have hnz := tprod_one_add_ne_zero_of_summable
        (fun n ↦ by simpa only [hone] using hnone n) hsum
      exact hnz (by simpa only [hone] using hprod)
    · rintro ⟨n, hn⟩
      exact tprod_of_exists_eq_zero ⟨n,
        (boundaryFactor_eq_zero_iff n (a n) (b n) (hzb hz n)).2 hn⟩
  refine ⟨hzero, hfinite, ?_⟩
  rw [hm]
  apply tsum_congr
  intro n
  simp only [F, analyticOrderNatAt, analyticOrderAt_boundaryFactor n (hab n) (hzb hz n)]
  split_ifs <;> simp

theorem boundaryFactor_at_inv (p : ℕ) (a b : ℂ) {w : ℂ} (hw : w ≠ 0) :
    boundaryFactor p a b w⁻¹ = boundaryInfinityFactor p a b w := by
  unfold boundaryFactor boundaryInfinityFactor
  congr 1
  have hden : w⁻¹ - b = (1 - b * w) / w := by field_simp [hw]
  rw [hden, div_div_eq_mul_div]

@[simp] theorem boundaryInfinityFactor_zero (p : ℕ) (a b : ℂ) :
    boundaryInfinityFactor p a b 0 = 1 := by
  simp [boundaryInfinityFactor, elementaryFactor, elementaryExponent]

/-- The normalized product is analytic in a neighborhood of infinity in its
actual local coordinate, and takes value one there. -/
theorem boundary_product_analytic_infinity (a b : ℕ → ℂ)
    (B : ℝ) (hB : 0 < B) (hb : ∀ n, ‖b n‖ ≤ B)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0)) :
    AnalyticAt ℂ (fun w ↦ ∏' n, boundaryInfinityFactor n (a n) (b n) w) 0 := by
  obtain ⟨ρ, hρ, hden, hratio⟩ := boundary_ratios_small_at_infinity a b B hB hb hsmall
  let F : ℕ → ℂ → ℂ := fun n w ↦ boundaryInfinityFactor n (a n) (b n) w
  have hF : ∀ n, DifferentiableOn ℂ (F n) (ball 0 ρ) := by
    intro n w hw
    have hd : 1 - b n * w ≠ 0 := hden n w (by simpa using (mem_ball_zero_iff.mp hw).le)
    apply DifferentiableAt.differentiableWithinAt
    apply AnalyticAt.differentiableAt
    exact ((differentiable_elementaryFactor n).analyticAt
      ((a n - b n) * w / (1 - b n * w))).comp
      ((analyticAt_const.mul analyticAt_id).div
        (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) hd)
  have hgeo : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1)) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).comp_injective
      (fun n m h ↦ Nat.add_right_cancel h)
  have herr : TendstoUniformlyOn
      (fun N w ↦ ∑ n ∈ range N, ‖F n w - 1‖)
      (fun w ↦ ∑' n, ‖F n w - 1‖) atTop (ball 0 ρ) := by
    apply tendstoUniformlyOn_tsum_nat_eventually hgeo
    filter_upwards [hratio] with n hn w hw
    have hr := hn w (mem_ball_zero_iff.mp hw).le
    rw [Real.norm_of_nonneg (norm_nonneg _), norm_sub_rev]
    exact (norm_one_sub_elementaryFactor_le n _ (hr.trans (by norm_num))).trans
      (pow_le_pow_left₀ (norm_nonneg _) hr)
  have h := holomorphic_product_of_uniform_norm_series_using_15_4
    (fun _ u A hb hc ↦ uniform_product_of_uniform_norm_series u A hb hc)
    isOpen_ball hF herr.tendstoLocallyUniformlyOn
  exact h.2.1.analyticAt (isOpen_ball.mem_nhds (by simpa using hρ))

def boundarySphereProduct (a b : ℕ → ℂ) (p : ComplexSphere) : ℂ :=
  p.elim 1 (fun z ↦ ∏' n, boundaryFactor n (a n) (b n) z)

@[simp] theorem boundarySphereProduct_infty (a b : ℕ → ℂ) :
    boundarySphereProduct a b ∞ = 1 := rfl

@[simp] theorem boundarySphereProduct_coe (a b : ℕ → ℂ) (z : ℂ) :
    boundarySphereProduct a b (↑z) = ∏' n, boundaryFactor n (a n) (b n) z := rfl

theorem boundarySphereProduct_infinity_chart (a b : ℕ → ℂ) :
    boundarySphereProduct a b ∘ sphereInfinityChart =
      fun w ↦ ∏' n, boundaryInfinityFactor n (a n) (b n) w := by
  funext w
  by_cases hw : w = 0
  · subst w; simp
  · simp only [Function.comp_def, sphereInfinityChart_of_ne_zero hw,
      boundarySphereProduct_coe, boundaryFactor_at_inv _ _ _ hw]

theorem normalized_boundarySphereProduct_holomorphic (a b : ℕ → ℂ) {C : Set ℂ}
    (hC : IsCompact C) (hCne : C.Nonempty) (ha : ∀ n, a n ∉ C) (hb : ∀ n, b n ∈ C)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0)) :
    SphereHolomorphicOn (boundarySphereProduct a b)
      (((↑) : ℂ → ComplexSphere) '' C)ᶜ := by
  have hplane := (boundary_product_on_complement a b hC.isClosed hCne ha hb hsmall).2.1
  obtain ⟨B, hB, hbound⟩ := hC.isBounded.exists_pos_norm_le
  intro p hp
  induction p using OnePoint.rec with
  | infty =>
    rw [sphereAnalyticAt_infty, boundarySphereProduct_infinity_chart]
    exact boundary_product_analytic_infinity a b B hB (fun n ↦ hbound (b n) (hb n)) hsmall
  | coe z =>
    rw [sphereAnalyticAt_coe]
    have hz : z ∈ Cᶜ := by
      intro h
      exact hp ⟨z, h, rfl⟩
    exact hplane.analyticAt (hC.isClosed.isOpen_compl.mem_nhds hz)

def boundarySphereFactor (n : ℕ) (a b : ℂ) (p : ComplexSphere) : ℂ :=
  p.elim 1 (boundaryFactor n a b)

@[simp] theorem boundarySphereFactor_infty (n : ℕ) (a b : ℂ) :
    boundarySphereFactor n a b ∞ = 1 := rfl

@[simp] theorem boundarySphereFactor_coe (n : ℕ) (a b z : ℂ) :
    boundarySphereFactor n a b (↑z) = boundaryFactor n a b z := rfl

theorem boundarySphereFactor_infinity_chart (n : ℕ) (a b : ℂ) :
    boundarySphereFactor n a b ∘ sphereInfinityChart = boundaryInfinityFactor n a b := by
  funext w
  by_cases hw : w = 0
  · subst w; simp
  · simp only [Function.comp_def, sphereInfinityChart_of_ne_zero hw,
      boundarySphereFactor_coe, boundaryFactor_at_inv _ _ _ hw]

theorem boundarySphereFactor_holomorphic (n : ℕ) (a b : ℂ) {C : Set ℂ} (hb : b ∈ C) :
    SphereHolomorphicOn (boundarySphereFactor n a b) (((↑) : ℂ → ComplexSphere) '' C)ᶜ := by
  intro p hp
  induction p using OnePoint.rec with
  | infty =>
    rw [sphereAnalyticAt_infty, boundarySphereFactor_infinity_chart]
    exact ((differentiable_elementaryFactor n).analyticAt
      ((a - b) * (0 : ℂ) / (1 - b * 0))).comp
      ((analyticAt_const.mul analyticAt_id).div
        (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (by simp))
  | coe z =>
    rw [sphereAnalyticAt_coe]
    exact analyticAt_boundaryFactor n a b (fun h ↦ hp ⟨b, hb, by simp [h]⟩)

theorem sphereHolomorphicOn_finset_product {ι : Type*} (s : Finset ι)
    (F : ι → ComplexSphere → ℂ) {Ω : Set ComplexSphere}
    (hF : ∀ i ∈ s, SphereHolomorphicOn (F i) Ω) :
    SphereHolomorphicOn (fun p ↦ ∏ i ∈ s, F i p) Ω := by
  intro p hp
  induction p using OnePoint.rec with
  | infty =>
    change AnalyticAt ℂ (fun w ↦ ∏ i ∈ s, F i (sphereInfinityChart w)) 0
    exact s.analyticAt_fun_prod (fun i hi ↦ hF i hi ∞ hp)
  | coe z =>
    change AnalyticAt ℂ (fun w : ℂ ↦ ∏ i ∈ s, F i (↑w)) z
    exact s.analyticAt_fun_prod (fun i hi ↦ hF i hi (↑z) hp)

#print axioms analyticOrderAt_boundaryFactor
#print axioms boundary_product_on_complement
#print axioms boundary_product_analytic_infinity
#print axioms normalized_boundarySphereProduct_holomorphic
#print axioms boundarySphereFactor_holomorphic
#print axioms sphereHolomorphicOn_finset_product

end RudinRCA.Chapter15
