import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Filter Finset Set
open scoped Topology InnerProductSpace ComplexConjugate

namespace RudinRCA.Chapter15.MuntzDistanceWork

/-- The finite product in the exact Müntz distance formula. -/
def distanceProduct (a : ℕ → ℝ≥0) (n : ℕ) (x : ℝ≥0) : ℝ :=
  ∏ i ∈ range n, ((x : ℝ) - a i) / ((x : ℝ) + a i + 1)

theorem distanceProduct_self_eq_zero (a : ℕ → ℝ≥0) {i n : ℕ} (hi : i < n) :
    distanceProduct a n (a i) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hi)
  simp

theorem distanceProduct_pivot_ne_zero {a : ℕ → ℝ≥0} (ha : Function.Injective a) (n : ℕ) :
    distanceProduct a n (a n) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply div_ne_zero
  · intro h
    have : a n = a i := NNReal.coe_injective (sub_eq_zero.mp h)
    exact (Nat.ne_of_lt (Finset.mem_range.mp hi)) (ha this).symm
  · positivity

/-- A single Schur-complement step for the power-function Gram kernel. -/
theorem cauchy_kernel_elimination (x y a : ℝ≥0) :
    1 / ((x : ℝ) + y + 1) - (2 * a + 1) /
      (((x : ℝ) + a + 1) * ((y : ℝ) + a + 1)) =
    (((x : ℝ) - a) / ((x : ℝ) + a + 1)) *
      (((y : ℝ) - a) / ((y : ℝ) + a + 1)) / ((x : ℝ) + y + 1) := by
  have hxy : (x : ℝ) + y + 1 ≠ 0 := by positivity
  have hxa : (x : ℝ) + a + 1 ≠ 0 := by positivity
  have hya : (y : ℝ) + a + 1 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- The first `n` power vectors span this finite-dimensional subspace. -/
def initialSpan {E : Type*} [AddCommGroup E] [Module ℂ E]
    (v : ℝ≥0 → E) (a : ℕ → ℝ≥0) (n : ℕ) : Submodule ℂ E :=
  Submodule.span ℂ {w | ∃ i < n, w = v (a i)}

theorem initialSpan_mono {E : Type*} [AddCommGroup E] [Module ℂ E]
    (v : ℝ≥0 → E) (a : ℕ → ℝ≥0) : Monotone (initialSpan v a) := by
  intro n m hnm
  apply Submodule.span_mono
  rintro w ⟨i, hi, rfl⟩
  exact ⟨i, hi.trans_le hnm, rfl⟩

/-- Exact orthogonal residuals, derived from the Gram kernel without determinants. -/
theorem exists_power_residuals {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : ℝ≥0 → E) (a : ℕ → ℝ≥0) (ha : Function.Injective a)
    (hkernel : ∀ x y, ⟪v x, v y⟫_ℂ = (1 / ((x : ℝ) + y + 1) : ℝ)) (n : ℕ) :
    ∃ R : ℝ≥0 → E,
      (∀ x y, ⟪R x, R y⟫_ℂ =
        (distanceProduct a n x * distanceProduct a n y / ((x : ℝ) + y + 1) : ℝ)) ∧
      (∀ x, v x - R x ∈ initialSpan v a n) ∧
      (∀ x w, w ∈ initialSpan v a n → ⟪R x, w⟫_ℂ = 0) := by
  induction n with
  | zero =>
    refine ⟨v, ?_, ?_, ?_⟩
    · intro x y
      simpa [distanceProduct] using hkernel x y
    · intro x
      simp
    · intro x w hw
      have hw0 : w = 0 := by simpa [initialSpan] using hw
      simp [hw0]
  | succ n ih =>
    obtain ⟨R, hR, hdiff, horth⟩ := ih
    let P := distanceProduct a n
    let b := a n
    let c : ℝ≥0 → ℝ := fun x ↦ (P x / P b) * ((2 * b + 1) / ((x : ℝ) + b + 1))
    let R' : ℝ≥0 → E := fun x ↦ R x - (c x : ℂ) • R b
    have hPb : P b ≠ 0 := distanceProduct_pivot_ne_zero ha n
    have hstep (x : ℝ≥0) : distanceProduct a (n + 1) x =
        P x * (((x : ℝ) - b) / ((x : ℝ) + b + 1)) := by
      simp only [distanceProduct, Finset.prod_range_succ, P, b]
    refine ⟨R', ?_, ?_, ?_⟩
    · intro x y
      dsimp only [R']
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        hR, map_sub, Complex.conj_ofReal]
      rw [hstep x, hstep y]
      norm_cast
      have hxy : (x : ℝ) + y + 1 ≠ 0 := by positivity
      have hxb : (x : ℝ) + b + 1 ≠ 0 := by positivity
      have hyb : (y : ℝ) + b + 1 ≠ 0 := by positivity
      have hbx : (b : ℝ) + x + 1 ≠ 0 := by positivity
      have hbb : (b : ℝ) + b + 1 ≠ 0 := by positivity
      have hb2 : 2 * (b : ℝ) + 1 ≠ 0 := by positivity
      change P x * P y / ((x : ℝ) + y + 1) -
          c y * (P x * P b / ((x : ℝ) + b + 1)) -
          c x * (P b * P y / ((b : ℝ) + y + 1) -
            c y * (P b * P b / ((b : ℝ) + b + 1))) = _
      dsimp only [c]
      field_simp [hPb]
      <;> ring
    · intro x
      have hsub : initialSpan v a n ≤ initialSpan v a (n + 1) :=
        initialSpan_mono v a (Nat.le_succ n)
      have hRb : R b ∈ initialSpan v a (n + 1) := by
        have hvb : v b ∈ initialSpan v a (n + 1) :=
          Submodule.subset_span ⟨n, Nat.lt_succ_self n, rfl⟩
        simpa only [sub_sub_cancel] using (initialSpan v a (n + 1)).sub_mem hvb (hsub (hdiff b))
      have heq : v x - R' x = (v x - R x) + (c x : ℂ) • R b := by
        dsimp [R']
        abel
      rw [heq]
      exact (initialSpan v a (n + 1)).add_mem (hsub (hdiff x))
        ((initialSpan v a (n + 1)).smul_mem _ hRb)
    · intro x w hw
      have hle : initialSpan v a (n + 1) ≤ (innerSL ℂ (R' x)).ker := by
        apply Submodule.span_le.mpr
        rintro w ⟨i, hi, rfl⟩
        change ⟪R' x, v (a i)⟫_ℂ = 0
        by_cases hin : i < n
        · have hvi : v (a i) ∈ initialSpan v a n := Submodule.subset_span ⟨i, hin, rfl⟩
          simp only [R', inner_sub_left, inner_smul_left, horth x _ hvi, horth b _ hvi,
            mul_zero, sub_zero]
        · have hin : i = n := by omega
          subst i
          have hxb : ⟪R x, v b⟫_ℂ = ⟪R x, R b⟫_ℂ := by
            exact sub_eq_zero.mp (by simpa only [inner_sub_right] using horth x _ (hdiff b))
          have hbb : ⟪R b, v b⟫_ℂ = ⟪R b, R b⟫_ℂ := by
            exact sub_eq_zero.mp (by simpa only [inner_sub_right] using horth b _ (hdiff b))
          change ⟪R' x, v b⟫_ℂ = 0
          simp only [R', inner_sub_left, inner_smul_left, Complex.conj_ofReal, hxb, hbb, hR]
          norm_cast
          change P x * P b / ((x : ℝ) + b + 1) -
            c x * (P b * P b / ((b : ℝ) + b + 1)) = 0
          dsimp [c]
          have hxb0 : (x : ℝ) + b + 1 ≠ 0 := by positivity
          have hbb0 : (b : ℝ) + b + 1 ≠ 0 := by positivity
          field_simp [hPb]
          <;> ring
      exact hle hw

/-- The exact finite-distance lower bound in an abstract Hilbert space with
power-function Gram kernel. -/
theorem power_distance_lower_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v : ℝ≥0 → E) (a : ℕ → ℝ≥0)
    (ha : Function.Injective a)
    (hkernel : ∀ x y, ⟪v x, v y⟫_ℂ = (1 / ((x : ℝ) + y + 1) : ℝ))
    (n : ℕ) (q : ℝ≥0) {g : E} (hg : g ∈ initialSpan v a n) :
    distanceProduct a n q ^ 2 / (2 * (q : ℝ) + 1) ≤ ‖v q - g‖ ^ 2 := by
  obtain ⟨R, hR, hdiff, horth⟩ := exists_power_residuals v a ha hkernel n
  have hnorm : ‖R q‖ ^ 2 = distanceProduct a n q ^ 2 / (2 * (q : ℝ) + 1) := by
    have h := congrArg Complex.re (hR q q)
    simpa only [inner_self_eq_norm_sq, Complex.ofReal_re, pow_two, two_mul] using h
  have hperp : ⟪R q, v q - R q - g⟫_ℂ = 0 :=
    horth q _ ((initialSpan v a n).sub_mem (hdiff q) hg)
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (R q) (v q - R q - g) hperp
  have heq : R q + (v q - R q - g) = v q - g := by abel
  rw [heq, hnorm] at hp
  nlinarith [sq_nonneg ‖v q - R q - g‖]

/-- For a convergent reciprocal sum, the finite products in the distance formula
have a strictly positive uniform lower bound whenever the target exponent is absent. -/
theorem distanceProduct_abs_uniform_lower {a : ℕ → ℝ≥0} {q : ℝ≥0}
    (hq : ∀ i, q ≠ a i) (hs : Summable (fun i ↦ 1 / ((a i : ℝ) + 1))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n, ε ≤ |distanceProduct a n q| := by
  let f : ℕ → ℝ := fun i ↦ |((q : ℝ) - a i) / ((q : ℝ) + a i + 1)|
  have hfpos (i : ℕ) : 0 < f i := by
    apply abs_pos.mpr
    apply div_ne_zero
    · exact sub_ne_zero.mpr (fun h ↦ hq i (NNReal.coe_injective h))
    · positivity
  have hfle (i : ℕ) : f i ≤ 1 := by
    dsimp [f]
    rw [abs_div, abs_of_pos (by positivity : 0 < (q : ℝ) + a i + 1),
      div_le_one (by positivity)]
    exact abs_le.mpr ⟨by linarith [q.property, (a i).property],
      by linarith [q.property, (a i).property]⟩
  have hgap (i : ℕ) : 1 - f i ≤ (2 * (q : ℝ) + 1) * (1 / ((a i : ℝ) + 1)) := by
    have hd : 0 < (q : ℝ) + a i + 1 := by positivity
    have habs : (a i : ℝ) - q ≤ |(q : ℝ) - a i| := by
      simpa only [abs_sub_comm] using le_abs_self ((a i : ℝ) - q)
    calc
      1 - f i = (((q : ℝ) + a i + 1) - |(q : ℝ) - a i|) /
          ((q : ℝ) + a i + 1) := by
        dsimp [f]
        rw [abs_div, abs_of_pos hd]
        field_simp
      _ ≤ (2 * (q : ℝ) + 1) / ((q : ℝ) + a i + 1) :=
        div_le_div_of_nonneg_right (by linarith) hd.le
      _ ≤ (2 * (q : ℝ) + 1) / ((a i : ℝ) + 1) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith [q.property])
      _ = _ := by ring
  have hdev : Summable (fun i ↦ f i - 1) := by
    apply (hs.mul_left (2 * (q : ℝ) + 1)).of_norm_bounded
    intro i
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hfle i)), neg_sub]
    exact hgap i
  have hlog : Summable (fun i ↦ Real.log (f i)) := by
    simpa only [add_sub_cancel] using Real.summable_log_one_add_of_summable hdev
  let ε := Real.exp (∑' i, Real.log (f i))
  have hlim : Tendsto (fun n ↦ ∏ i ∈ range n, f i) atTop (𝓝 ε) :=
    (Real.hasProd_of_hasSum_log hfpos hlog.hasSum).tendsto_prod_nat
  refine ⟨ε, Real.exp_pos _, ?_⟩
  intro n
  have hle : ε ≤ ∏ i ∈ range n, f i := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop n] with m hm
    exact Finset.prod_le_prod_of_subset_of_le_one₀ (Finset.range_mono hm)
      (fun i _ ↦ (hfpos i).le) (fun i _ _ ↦ hfle i)
  simpa only [distanceProduct, Finset.abs_prod, f] using hle

theorem mem_initialSpan_of_mem_span {E : Type*} [AddCommGroup E] [Module ℂ E]
    {v : ℝ≥0 → E} {a : ℕ → ℝ≥0} {g : E}
    (hg : g ∈ Submodule.span ℂ (Set.range fun i ↦ v (a i))) :
    ∃ n, g ∈ initialSpan v a n := by
  apply Submodule.span_induction (p := fun g _ ↦ ∃ n, g ∈ initialSpan v a n) ?_ ?_ ?_ ?_ hg
  · rintro w ⟨i, rfl⟩
    exact ⟨i + 1, Submodule.subset_span ⟨i, Nat.lt_succ_self i, rfl⟩⟩
  · exact ⟨0, Submodule.zero_mem _⟩
  · rintro x y hx hy ⟨n, hn⟩ ⟨m, hm⟩
    exact ⟨max n m, (initialSpan v a (max n m)).add_mem
      (initialSpan_mono v a (le_max_left n m) hn)
      (initialSpan_mono v a (le_max_right n m) hm)⟩
  · rintro c x hx ⟨n, hn⟩
    exact ⟨n, (initialSpan v a n).smul_mem c hn⟩

/-- Abstract Müntz non-membership for the exact Gram kernel. No completeness of
the ambient inner-product space is needed. -/
theorem power_not_mem_closed_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : ℝ≥0 → E) (a : ℕ → ℝ≥0) (ha : Function.Injective a)
    (hkernel : ∀ x y, ⟪v x, v y⟫_ℂ = (1 / ((x : ℝ) + y + 1) : ℝ))
    (hs : Summable (fun i ↦ 1 / ((a i : ℝ) + 1))) {q : ℝ≥0}
    (hq : ∀ i, q ≠ a i) :
    v q ∉ (Submodule.span ℂ (Set.range fun i ↦ v (a i))).topologicalClosure := by
  obtain ⟨ε, hε, hεprod⟩ := distanceProduct_abs_uniform_lower hq hs
  let c := ε ^ 2 / (2 * (q : ℝ) + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hclosed : IsClosed {g : E | c ≤ ‖v q - g‖ ^ 2} :=
    isClosed_le continuous_const (by fun_prop)
  have hsub : (Submodule.span ℂ (Set.range fun i ↦ v (a i)) : Set E) ⊆
      {g : E | c ≤ ‖v q - g‖ ^ 2} := by
    intro g hg
    obtain ⟨n, hn⟩ := mem_initialSpan_of_mem_span hg
    calc
      c ≤ distanceProduct a n q ^ 2 / (2 * (q : ℝ) + 1) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hprod := hεprod n
        nlinarith [sq_abs (distanceProduct a n q)]
      _ ≤ ‖v q - g‖ ^ 2 := power_distance_lower_bound v a ha hkernel n q hn
  intro h
  have : c ≤ ‖v q - v q‖ ^ 2 := closure_minimal hsub hclosed h
  simpa using (hc.not_ge (by simpa using this))

#print axioms distanceProduct_self_eq_zero
#print axioms distanceProduct_pivot_ne_zero
#print axioms cauchy_kernel_elimination
#print axioms initialSpan_mono
#print axioms exists_power_residuals
#print axioms power_distance_lower_bound
#print axioms distanceProduct_abs_uniform_lower
#print axioms mem_initialSpan_of_mem_span
#print axioms power_not_mem_closed_span

end RudinRCA.Chapter15.MuntzDistanceWork
