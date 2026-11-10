import MuntzSzaszWork
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

noncomputable section

open Filter Set Metric MeasureTheory
open scoped Topology

namespace RudinRCA.Chapter15.MuntzSzaszWork

theorem continuousMap_circleIntegral_apply {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {F : ℂ → C(X, ℂ)} {c : ℂ} {r : ℝ} (hf : CircleIntegrable F c r) (x : X) :
    (∮ z in C(c, r), F z) x = ∮ z in C(c, r), F z x := by
  simpa only [circleIntegral, map_smul, ContinuousMap.evalCLM_apply] using
    ((ContinuousMap.evalCLM ℂ x).intervalIntegral_comp_comm hf.out).symm

/-- Continuous families of continuous functions are holomorphic when every
point evaluation is holomorphic. The compact domain gives the supremum norm. -/
theorem differentiableOn_continuousMap_of_eval {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F : ℂ → C(X, ℂ)} (hF : ContinuousOn F Ω)
    (hpoint : ∀ x, DifferentiableOn ℂ (fun z ↦ F z x) Ω) : DifferentiableOn ℂ F Ω := by
  intro c hc
  obtain ⟨r, hr, hrΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hc)
  have hcircle : CircleIntegrable F c r :=
    (hF.mono (sphere_subset_closedBall.trans hrΩ)).circleIntegrable hr.le
  have hrep (w : ℂ) (hw : w ∈ ball c r) :
      (∮ z in C(c, r), (z - w)⁻¹ • F z) = (2 * Real.pi * Complex.I : ℂ) • F w := by
    have hwne : w ∉ sphere c |r| := by
      rw [abs_of_pos hr]
      exact Set.disjoint_left.mp disjoint_ball_sphere hw
    ext x
    rw [continuousMap_circleIntegral_apply
      (by simpa only [zpow_neg_one] using hcircle.sub_zpow_smul (-1) hwne) x]
    exact ((hpoint x).mono hrΩ).circleIntegral_sub_inv_smul hw
  have hcenter : c ∉ sphere c |r| := by simp [hr.ne']
  have hd := (Complex.hasDerivAt_circleIntegral_sub_inv_smul hcircle hcenter).const_smul
    ((2 * Real.pi * Complex.I : ℂ)⁻¹)
  have heq : (fun w ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      (∮ z in C(c, r), (z - w)⁻¹ • F z)) =ᶠ[𝓝 c] F := by
    filter_upwards [ball_mem_nhds c hr] with w hw
    rw [hrep w hw, smul_smul, inv_mul_cancel₀, one_smul]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  exact (hd.differentiableAt.congr_of_eventuallyEq heq.symm).differentiableWithinAt

/-- The vector-valued Mellin kernel, extended by zero outside the open right half-plane. -/
def intervalComplexPower (z : ℂ) : C(UnitInterval, ℂ) :=
  if hz : 0 < z.re then
    ⟨fun t ↦ (t.val : ℂ) ^ z,
      (Complex.continuous_ofReal_cpow_const hz).comp continuous_subtype_val⟩
  else 0

theorem intervalComplexPower_apply {z : ℂ} (hz : 0 < z.re) (t : UnitInterval) :
    intervalComplexPower z t = (t.val : ℂ) ^ z := by
  simp only [intervalComplexPower, dif_pos hz, ContinuousMap.coe_mk]

theorem intervalComplexPower_continuousOn :
    ContinuousOn intervalComplexPower {z | 0 < z.re} := by
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  have hc : ContinuousOn (fun p : ℂ × UnitInterval ↦ (p.2.val : ℂ) ^ p.1)
      ({z : ℂ | 0 < z.re} ×ˢ (univ : Set UnitInterval)) := by
    intro p hp
    have hcp := Complex.continuousAt_cpow_of_re_pos
      (p := ((p.2.val : ℂ), p.1)) (Or.inl p.2.property.1) hp.1
    have hprod : ContinuousAt (fun q : ℂ × UnitInterval ↦ ((q.2.val : ℂ), q.1)) p := by
      fun_prop
    exact (Filter.Tendsto.comp hcp hprod).continuousWithinAt
  apply hc.congr
  intro p hp
  exact (intervalComplexPower_apply hp.1 p.2).symm

theorem intervalComplexPower_differentiableOn :
    DifferentiableOn ℂ intervalComplexPower {z | 0 < z.re} := by
  apply differentiableOn_continuousMap_of_eval
    (isOpen_lt continuous_const Complex.continuous_re) intervalComplexPower_continuousOn
  intro t
  have hc : DifferentiableOn ℂ (fun z : ℂ ↦ (t.val : ℂ) ^ z) {z | 0 < z.re} :=
    differentiableOn_id.const_cpow (Or.inr fun z hz ↦ by intro h; simpa [h] using hz)
  apply hc.congr
  intro z hz
  exact (intervalComplexPower_apply hz t).symm

theorem norm_intervalComplexPower_le_one {z : ℂ} (hz : 0 < z.re) :
    ‖intervalComplexPower z‖ ≤ 1 := by
  apply (ContinuousMap.norm_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro t
  rw [intervalComplexPower_apply hz,
    Complex.norm_cpow_eq_rpow_re_of_nonneg t.property.1 hz.ne']
  exact Real.rpow_le_one t.property.1 t.property.2 hz.le

theorem intervalComplexPower_ofReal {q : ℝ} (hq : 0 < q) :
    intervalComplexPower (q : ℂ) = intervalRealPower q hq.le := by
  ext t
  rw [intervalComplexPower_apply (by simpa using hq)]
  exact (Complex.ofReal_cpow t.property.1 q).symm

/-- Applying any continuous linear functional produces the bounded holomorphic
Mellin transform needed by the separating-functional proof. -/
theorem functional_mellin_holomorphic_bounded (L : C(UnitInterval, ℂ) →L[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z ↦ L (intervalComplexPower z)) {z | 0 < z.re} ∧
      ∀ z, 0 < z.re → ‖L (intervalComplexPower z)‖ ≤ ‖L‖ := by
  constructor
  · exact L.differentiable.comp_differentiableOn intervalComplexPower_differentiableOn
  · intro z hz
    exact (L.le_opNorm _).trans (by simpa using
      mul_le_mul_of_nonneg_left (norm_intervalComplexPower_le_one hz) (norm_nonneg L))

/-- Hahn–Banach separation in the exact form needed for a closed subspace. -/
theorem mem_closed_submodule_of_annihilator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : Submodule ℂ E) (hS : IsClosed (S : Set E)) {v : E}
    (hv : ∀ L : E →L[ℂ] ℂ, (∀ w ∈ S, L w = 0) → L v = 0) : v ∈ S := by
  letI : IsClosed (S : Set E) := hS
  by_contra hvS
  have hq : (Submodule.Quotient.mk v : E ⧸ S) ≠ 0 :=
    fun h ↦ hvS (Submodule.Quotient.mk_eq_zero.mp h)
  obtain ⟨L, hL⟩ := SeparatingDual.exists_ne_zero (R := ℂ) hq
  apply hL
  apply hv (L.comp S.mkQL)
  intro w hw
  simp [Submodule.Quotient.mk_eq_zero.mpr hw]

/-- Rudin 15.26(a), the Müntz–Szász density implication for arbitrary strictly
increasing positive real exponents, including sequences with finite accumulation. -/
theorem muntz_szasz_dense {λ : ℕ → ℝ} (hλ0 : 0 < λ 0) (hλ : StrictMono λ)
    (hdiv : ¬ Summable (fun n ↦ 1 / λ n)) :
    muntzClosure λ (fun n ↦ (hλ0.trans_le (hλ.monotone (Nat.zero_le n))).le) = ⊤ := by
  let hpos : ∀ n, 0 < λ n := fun n ↦ hλ0.trans_le (hλ.monotone (Nat.zero_le n))
  apply muntzClosure_eq_top_of_contains_powers
  intro n
  by_cases hn : n = 0
  · simpa only [hn, pow_zero] using one_mem_muntzClosure λ (fun n ↦ (hpos n).le)
  · apply mem_closed_submodule_of_annihilator _ (Submodule.isClosed_topologicalClosure _)
    intro L hL
    obtain ⟨hhol, hbound⟩ := functional_mellin_holomorphic_bounded L
    have hfzero := bounded_halfPlane_zero_on_positive_reals hhol ⟨‖L‖, hbound⟩ hλ0 hλ hdiv
      (fun j ↦ by rw [intervalComplexPower_ofReal (hpos j)];
        exact hL _ (intervalRealPower_mem_muntzClosure λ (fun n ↦ (hpos n).le) j))
    have h := hfzero n (by exact_mod_cast Nat.pos_of_ne_zero hn)
    rw [intervalComplexPower_ofReal (by exact_mod_cast Nat.pos_of_ne_zero hn),
      intervalRealPower_nat] at h
    exact h

/-- The constructive deletion assertion behind 15.27: a divergent Müntz family
has a subsequence with infinitely many omitted exponents and the same dense span. -/
theorem muntz_exists_infinite_removal_dense {λ : ℕ → ℝ}
    (hλ0 : 0 < λ 0) (hλ : StrictMono λ)
    (hdiv : ¬ Summable (fun n ↦ 1 / λ n)) :
    ∃ b : ℕ → ℕ, StrictMono b ∧ (range b)ᶜ.Infinite ∧
      muntzClosure (λ ∘ b)
        (fun n ↦ (hλ0.trans_le (hλ.monotone (Nat.zero_le (b n)))).le) = ⊤ := by
  obtain ⟨b, hb, hbinf, hbdiv⟩ := exists_infinite_removal_preserving_divergence hdiv
  refine ⟨b, hb, hbinf, ?_⟩
  exact muntz_szasz_dense (hλ0.trans_le (hλ.monotone (Nat.zero_le (b 0))))
    (hλ.comp hb) hbdiv

/-- Removing the constant always strictly reduces the closed Müntz span, since
every positive power vanishes at the origin. This includes the constant member
in the non-density assertion of 15.27. -/
theorem muntz_constant_removal_strict {λ : ℕ → ℝ} (hλ : ∀ n, 0 < λ n) :
    (Submodule.span ℂ (range fun n ↦ intervalRealPower (λ n) (hλ n).le)).topologicalClosure <
      muntzClosure λ (fun n ↦ (hλ n).le) := by
  exact closed_span_strictly_decreases_of_removed_vector
    (subset_insert 1 _) (mem_insert 1 _) (one_not_mem_closed_span_positive_powers hλ)

#print axioms continuousMap_circleIntegral_apply
#print axioms differentiableOn_continuousMap_of_eval
#print axioms intervalComplexPower_continuousOn
#print axioms intervalComplexPower_differentiableOn
#print axioms norm_intervalComplexPower_le_one
#print axioms intervalComplexPower_ofReal
#print axioms functional_mellin_holomorphic_bounded
#print axioms mem_closed_submodule_of_annihilator
#print axioms muntz_szasz_dense
#print axioms muntz_exists_infinite_removal_dense
#print axioms muntz_constant_removal_strict

end RudinRCA.Chapter15.MuntzSzaszWork
