import MuntzSzaszWork
import MuntzDistanceWork
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace ComplexConjugate

namespace RudinRCA.Chapter15.MuntzSzaszWork

/-- The continuous inclusion of continuous functions on `[0,1]` into `L²`. -/
def intervalToL2 : C(UnitInterval, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure UnitInterval) :=
  ContinuousMap.toLp 2 volume ℂ

/-- Real powers viewed in `L²([0,1])`. -/
def l2Power (x : ℝ≥0) : Lp ℂ 2 (volume : Measure UnitInterval) :=
  intervalToL2 (intervalRealPower x x.property)

/-- The elementary integral which supplies the entire Gram kernel. -/
theorem l2Power_inner (x y : ℝ≥0) :
    ⟪l2Power x, l2Power y⟫_ℂ = (1 / ((x : ℝ) + y + 1) : ℝ) := by
  rw [l2Power, l2Power, intervalToL2, ContinuousMap.inner_toLp]
  have heq : (fun t : UnitInterval ↦ intervalRealPower y y.property t *
      conj (intervalRealPower x x.property t)) =
      (fun t : UnitInterval ↦ ((t.val ^ ((x : ℝ) + y) : ℝ) : ℂ)) := by
    funext t
    simp only [intervalRealPower, ContinuousMap.coe_mk, Complex.conj_ofReal]
    rw [Real.rpow_add_of_nonneg t.property.1 x.property y.property]
    push_cast
    ring
  rw [heq, integral_ofReal, integral_subtype measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_rpow (Or.inl (by linarith [x.property, y.property]))]
  simp only [Real.one_rpow, Real.zero_rpow (by positivity : (x : ℝ) + y + 1 ≠ 0), sub_zero]

/-- Inserting the constant as exponent zero keeps the positive exponents separate. -/
def exponentsWithZero (λ : ℕ → ℝ) (hλ : ∀ n, 0 ≤ λ n) : ℕ → ℝ≥0
  | 0 => 0
  | n + 1 => ⟨λ n, hλ n⟩

theorem exponentsWithZero_injective {λ : ℕ → ℝ} (hλ : ∀ n, 0 < λ n)
    (hinj : Function.Injective λ) :
    Function.Injective (exponentsWithZero λ (fun n ↦ (hλ n).le)) := by
  intro i j hij
  cases i with
  | zero =>
    cases j with
    | zero => rfl
    | succ j =>
      have h : (0 : ℝ) = λ j := congrArg NNReal.val hij
      exact False.elim ((hλ j).ne' h.symm)
  | succ i =>
    cases j with
    | zero =>
      have h : λ i = (0 : ℝ) := congrArg NNReal.val hij
      exact False.elim ((hλ i).ne' h)
    | succ j =>
      exact congrArg Nat.succ (hinj (congrArg NNReal.val hij))

theorem summable_exponentsWithZero_reciprocal {λ : ℕ → ℝ} (hλ : ∀ n, 0 < λ n)
    (hs : Summable (fun n ↦ 1 / λ n)) :
    Summable (fun i ↦ 1 / ((exponentsWithZero λ (fun n ↦ (hλ n).le) i : ℝ) + 1)) := by
  apply (summable_nat_add_iff 1).mp
  apply hs.of_nonneg_of_le (fun n ↦ by positivity)
  intro n
  change 1 / (λ n + 1) ≤ 1 / λ n
  exact one_div_le_one_div_of_le (hλ n) (by linarith)

theorem range_powers_exponentsWithZero (λ : ℕ → ℝ) (hλ : ∀ n, 0 ≤ λ n) :
    (range fun i ↦ intervalRealPower
      (exponentsWithZero λ hλ i) (exponentsWithZero λ hλ i).property) =
      insert 1 (range fun i ↦ intervalRealPower (λ i) (hλ i)) := by
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | zero =>
      left
      ext t
      simp [exponentsWithZero, intervalRealPower]
    | succ i => exact Or.inr ⟨i, rfl⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · refine ⟨0, ?_⟩
      ext t
      simp [exponentsWithZero, intervalRealPower]
    · exact ⟨i + 1, rfl⟩

/-- Rudin 15.26(b): when the reciprocal sum converges, no absent positive real
power lies in the uniform closure, with the constant function included. -/
theorem muntz_szasz_power_not_mem {λ : ℕ → ℝ} (hλ0 : 0 < λ 0) (hλ : StrictMono λ)
    (hs : Summable (fun n ↦ 1 / λ n)) {q : ℝ} (hq : 0 < q)
    (hqλ : ∀ n, q ≠ λ n) :
    intervalRealPower q hq.le ∉
      muntzClosure λ (fun n ↦ (hλ0.trans_le (hλ.monotone (Nat.zero_le n))).le) := by
  let hpos : ∀ n, 0 < λ n := fun n ↦ hλ0.trans_le (hλ.monotone (Nat.zero_le n))
  let a := exponentsWithZero λ (fun n ↦ (hpos n).le)
  have ha : Function.Injective a := exponentsWithZero_injective hpos hλ.injective
  have hs' : Summable (fun i ↦ 1 / ((a i : ℝ) + 1)) :=
    summable_exponentsWithZero_reciprocal hpos hs
  have hqa : ∀ i, (⟨q, hq.le⟩ : ℝ≥0) ≠ a i := by
    intro i hi
    cases i with
    | zero => exact hq.ne' (congrArg NNReal.val hi)
    | succ i => exact hqλ i (congrArg NNReal.val hi)
  have hnot := MuntzDistanceWork.power_not_mem_closed_span l2Power a ha l2Power_inner hs' hqa
  intro hmem
  apply hnot
  let S : Submodule ℂ C(UnitInterval, ℂ) :=
    Submodule.span ℂ (range fun i ↦ intervalRealPower (a i) (a i).property)
  have hm : intervalRealPower q hq.le ∈ S.topologicalClosure := by
    simpa only [S, a, range_powers_exponentsWithZero, muntzClosure] using hmem
  have him := (S.topologicalClosure_map intervalToL2)
    (Submodule.mem_map.mpr ⟨intervalRealPower q hq.le, hm, rfl⟩)
  have hmap : S.map intervalToL2.toLinearMap =
      Submodule.span ℂ (range fun i ↦ l2Power (a i)) := by
    rw [S, Submodule.map_span, image_range]
    rfl
  rw [hmap] at him
  exact him

#print axioms l2Power_inner
#print axioms exponentsWithZero_injective
#print axioms summable_exponentsWithZero_reciprocal
#print axioms range_powers_exponentsWithZero
#print axioms muntz_szasz_power_not_mem

end RudinRCA.Chapter15.MuntzSzaszWork
