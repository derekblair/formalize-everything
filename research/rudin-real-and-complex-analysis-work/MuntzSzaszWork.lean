import BlaschkeNecessityWork
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

noncomputable section

open Filter Set Metric
open scoped Topology

namespace RudinRCA.Chapter15.MuntzSzaszWork

/-- Rudin's interval `I=[0,1]`, with its usual compact topology. -/
abbrev UnitInterval := Set.Icc (0 : ℝ) 1

/-- The real coordinate viewed as a complex continuous function. -/
def intervalCoordinate : C(UnitInterval, ℂ) :=
  ⟨fun t ↦ (t.val : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩

@[simp] theorem star_intervalCoordinate : star intervalCoordinate = intervalCoordinate := by
  ext t
  simp [intervalCoordinate]

/-- The finite linear combinations of ordinary monomials are dense in `C([0,1],ℂ)`. -/
theorem polynomial_span_dense :
    (Submodule.span ℂ (range fun n : ℕ ↦ intervalCoordinate ^ n)).topologicalClosure = ⊤ := by
  let A := StarAlgebra.adjoin ℂ ({intervalCoordinate} : Set C(UnitInterval, ℂ))
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    refine ⟨intervalCoordinate, ⟨intervalCoordinate,
      StarAlgebra.subset_adjoin ℂ _ (mem_singleton _), rfl⟩, ?_⟩
    intro h
    apply hxy
    apply Subtype.ext
    exact Complex.ofReal_injective h
  have hA := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hspan : A.toSubalgebra.toSubmodule =
      Submodule.span ℂ (range fun n : ℕ ↦ intervalCoordinate ^ n) := by
    dsimp [A]
    rw [StarAlgebra.adjoin_eq_span]
    simp only [star_singleton, star_intervalCoordinate, union_self,
      ← Submonoid.powers_eq_closure, Submonoid.coe_powers]
  rw [← hspan]
  exact congrArg (fun B : StarSubalgebra ℂ C(UnitInterval, ℂ) ↦ B.toSubalgebra.toSubmodule) hA

/-- A nonnegative real power, including its continuous value at the origin. -/
def intervalRealPower (q : ℝ) (hq : 0 ≤ q) : C(UnitInterval, ℂ) :=
  ⟨fun t ↦ ((t.val ^ q : ℝ) : ℂ), Complex.continuous_ofReal.comp
    ((Real.continuous_rpow_const hq).comp continuous_subtype_val)⟩

@[simp] theorem intervalRealPower_nat (n : ℕ) :
    intervalRealPower n (Nat.cast_nonneg n) = intervalCoordinate ^ n := by
  ext t
  simp [intervalRealPower, intervalCoordinate, Real.rpow_natCast]

/-- The closed span in the statement of the Müntz–Szász theorem. -/
def muntzClosure (λ : ℕ → ℝ) (hλ : ∀ n, 0 ≤ λ n) : Submodule ℂ C(UnitInterval, ℂ) :=
  (Submodule.span ℂ (insert 1 (range fun n ↦ intervalRealPower (λ n) (hλ n)))).topologicalClosure

theorem one_mem_muntzClosure (λ : ℕ → ℝ) (hλ : ∀ n, 0 ≤ λ n) :
    (1 : C(UnitInterval, ℂ)) ∈ muntzClosure λ hλ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_insert 1 _))

theorem intervalRealPower_mem_muntzClosure (λ : ℕ → ℝ) (hλ : ∀ n, 0 ≤ λ n) (n : ℕ) :
    intervalRealPower (λ n) (hλ n) ∈ muntzClosure λ hλ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_insert_of_mem _ ⟨n, rfl⟩))

/-- Once all ordinary powers belong to the Müntz closure, Weierstrass density finishes part (a). -/
theorem muntzClosure_eq_top_of_contains_powers (λ : ℕ → ℝ) (hλ : ∀ n, 0 ≤ λ n)
    (hp : ∀ n : ℕ, intervalCoordinate ^ n ∈ muntzClosure λ hλ) : muntzClosure λ hλ = ⊤ := by
  apply top_unique
  rw [← polynomial_span_dense]
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact hp n
  · exact Submodule.isClosed_topologicalClosure _

/-- Images of positive real exponents under the half-plane-to-disc map. -/
def exponentDiscPoint (x : ℝ) : ℂ := ((x - 1) / (x + 1) : ℝ)

theorem norm_exponentDiscPoint_lt_one {x : ℝ} (hx : 0 < x) :
    ‖exponentDiscPoint x‖ < 1 := by
  rw [exponentDiscPoint, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos (by linarith : 0 < x + 1), div_lt_one (by linarith : 0 < x + 1)]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem exponentDiscPoint_injectiveOn : InjOn exponentDiscPoint (Ioi (0 : ℝ)) := by
  intro x hx y hy h
  have heq : (x - 1) / (x + 1) = (y - 1) / (y + 1) := Complex.ofReal_injective h
  have hprod := (div_eq_div_iff (by linarith : x + 1 ≠ 0) (by linarith : y + 1 ≠ 0)).mp heq
  nlinarith

theorem exponentDiscPoint_gap_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    1 - ‖exponentDiscPoint x‖ = 2 / (x + 1) := by
  rw [exponentDiscPoint, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by linarith) (by linarith))]
  field_simp
  <;> ring

theorem exponentDiscPoint_gap_of_le_one {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    1 - ‖exponentDiscPoint x‖ = 2 * x / (x + 1) := by
  rw [exponentDiscPoint, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))]
  field_simp
  <;> ring

/-- Reciprocal divergence is preserved by the Cayley zero map even when the
strictly increasing exponent sequence stays bounded. -/
theorem not_summable_exponentDiscPoint_gap {λ : ℕ → ℝ}
    (hλ0 : 0 < λ 0) (hλ : StrictMono λ) (hdiv : ¬ Summable (fun n ↦ 1 / λ n)) :
    ¬ Summable (fun n ↦ 1 - ‖exponentDiscPoint (λ n)‖) := by
  intro hs
  let C : ℝ := max 1 (1 / (λ 0 * λ 0))
  have hC : 1 ≤ C := le_max_left _ _
  have hλpos (n : ℕ) : 0 < λ n := hλ0.trans_le (hλ.monotone (Nat.zero_le n))
  apply hdiv
  apply Summable.of_nonneg_of_le (fun n ↦ (one_div_pos.mpr (hλpos n)).le) _ (hs.mul_left C)
  intro n
  have hgap : 0 ≤ 1 - ‖exponentDiscPoint (λ n)‖ :=
    sub_nonneg.mpr (norm_exponentDiscPoint_lt_one (hλpos n)).le
  by_cases hn : 1 ≤ λ n
  · have hfirst : 1 / λ n ≤ 1 - ‖exponentDiscPoint (λ n)‖ := by
      rw [exponentDiscPoint_gap_of_one_le hn]
      apply (div_le_div_iff₀ (hλpos n) (by linarith : 0 < λ n + 1)).mpr
      linarith
    exact hfirst.trans (le_mul_of_one_le_left hgap hC)
  · have hn1 : λ n ≤ 1 := (lt_of_not_ge hn).le
    have hfirst : λ n ≤ 1 - ‖exponentDiscPoint (λ n)‖ := by
      rw [exponentDiscPoint_gap_of_le_one (hλpos n) hn1]
      apply (le_div_iff₀ (by linarith : 0 < λ n + 1)).mpr
      nlinarith [hλpos n]
    calc
      1 / λ n = (1 / (λ n * λ n)) * λ n := by field_simp
      _ ≤ (1 / (λ 0 * λ 0)) * λ n :=
        mul_le_mul_of_nonneg_right
          (one_div_le_one_div_of_le (mul_pos hλ0 hλ0)
            (mul_self_le_mul_self hλ0.le (hλ.monotone (Nat.zero_le n)))) (hλpos n).le
      _ ≤ C * (1 - ‖exponentDiscPoint (λ n)‖) :=
        mul_le_mul (le_max_right _ _) hfirst (hλpos n).le (zero_lt_one.trans_le hC).le

def discToRightHalfPlane (z : ℂ) : ℂ := (1 + z) / (1 - z)

theorem discToRightHalfPlane_re_pos {z : ℂ} (hz : ‖z‖ < 1) :
    0 < (discToRightHalfPlane z).re := by
  have hne : 1 - z ≠ 0 := by
    intro h
    have : z = 1 := (sub_eq_zero.mp h).symm
    simpa [this] using hz
  have heq : (discToRightHalfPlane z).re = (1 - ‖z‖ ^ 2) / ‖1 - z‖ ^ 2 := by
    rw [discToRightHalfPlane, Complex.div_re, Complex.normSq_eq_norm_sq, ← add_div]
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.add_im,
      Complex.sub_im, Complex.one_im, zero_add, zero_sub]
    rw [Complex.sq_norm, Complex.normSq_apply]
    congr 1
    ring
  rw [heq]
  exact div_pos (by nlinarith [norm_nonneg z]) (pow_pos (norm_pos_iff.mpr hne) _)

theorem discToRightHalfPlane_exponentDiscPoint {x : ℝ} (hx : 0 < x) :
    discToRightHalfPlane (exponentDiscPoint x) = (x : ℂ) := by
  have hxp : (x : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show x + 1 ≠ 0 by linarith)
  dsimp [discToRightHalfPlane, exponentDiscPoint]
  push_cast
  field_simp [hxp]
  <;> ring

/-- The analytic uniqueness step of 15.26(a), with no assumption that the
positive strictly increasing exponents tend to infinity. -/
theorem bounded_halfPlane_zero_on_positive_reals {f : ℂ → ℂ} {λ : ℕ → ℝ}
    (hf : DifferentiableOn ℂ f {z | 0 < z.re})
    (hbound : ∃ M : ℝ, ∀ z, 0 < z.re → ‖f z‖ ≤ M)
    (hλ0 : 0 < λ 0) (hλ : StrictMono λ) (hdiv : ¬ Summable (fun n ↦ 1 / λ n))
    (hz : ∀ n, f (λ n) = 0) : ∀ x : ℝ, 0 < x → f x = 0 := by
  let g : ℂ → ℂ := fun z ↦ f (discToRightHalfPlane z)
  have hψ : DifferentiableOn ℂ discToRightHalfPlane (ball 0 1) := by
    intro z hz
    have hzne : 1 - z ≠ 0 := by
      intro h
      have : z = 1 := (sub_eq_zero.mp h).symm
      simpa [this] using hz
    exact ((differentiableAt_const (1 : ℂ)).add differentiableAt_id).differentiableWithinAt.div
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).differentiableWithinAt hzne
  have hg : BoundedHolomorphic g := by
    refine ⟨hf.fun_comp hψ (fun z hz ↦ discToRightHalfPlane_re_pos (by simpa using hz)), ?_⟩
    obtain ⟨M, hM⟩ := hbound
    exact ⟨M, fun z hz ↦ hM _ (discToRightHalfPlane_re_pos (by simpa using hz))⟩
  have hλpos (n : ℕ) : 0 < λ n := hλ0.trans_le (hλ.monotone (Nat.zero_le n))
  have ha : Function.Injective (fun n ↦ exponentDiscPoint (λ n)) := by
    intro i j hij
    exact hλ.injective (exponentDiscPoint_injectiveOn (hλpos i) (hλpos j) hij)
  have hgzero := BlaschkeNecessityWork.boundedHolomorphic_zero_of_non_blaschke hg
    (fun n ↦ norm_exponentDiscPoint_lt_one (hλpos n)) ha
    (fun n ↦ by dsimp [g]; rw [discToRightHalfPlane_exponentDiscPoint (hλpos n)]; exact hz n)
    (not_summable_exponentDiscPoint_gap hλ0 hλ hdiv)
  intro x hx
  have h := hgzero (exponentDiscPoint x) (by simpa using norm_exponentDiscPoint_lt_one hx)
  simpa only [g, discToRightHalfPlane_exponentDiscPoint hx] using h

/-- Removing the constant function always changes the closed span: every
remaining positive power vanishes at the origin. -/
theorem one_not_mem_closed_span_positive_powers (λ : ℕ → ℝ) (hλ : ∀ n, 0 < λ n) :
    (1 : C(UnitInterval, ℂ)) ∉
      (Submodule.span ℂ (range fun n ↦ intervalRealPower (λ n) (hλ n).le)).topologicalClosure := by
  let e : C(UnitInterval, ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM (R := ℂ) ⟨0, by simp⟩
  have hle : (Submodule.span ℂ (range fun n ↦ intervalRealPower (λ n) (hλ n).le)).topologicalClosure ≤
      e.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      simp [e, intervalRealPower, Real.zero_rpow (hλ n).ne']
    · exact e.isClosed_ker
  intro h
  have := hle h
  simpa [e] using this

/-- Any divergent series retains divergence along either its even or odd indices.
The discarded indices are infinite in either case. This is the combinatorial
input to the first assertion of Rudin 15.27. -/
theorem exists_infinite_removal_preserving_divergence {u : ℕ → ℝ}
    (hu : ¬ Summable u) :
    ∃ b : ℕ → ℕ, StrictMono b ∧ (range b)ᶜ.Infinite ∧ ¬ Summable (fun n ↦ u (b n)) := by
  classical
  by_cases he : Summable (fun n ↦ u (2 * n))
  · refine ⟨fun n ↦ 2 * n + 1, (by intro i j hij; omega), ?_, ?_⟩
    · apply (Set.infinite_range_of_injective (f := fun n : ℕ ↦ 2 * n)
        (by intro i j hij; omega)).mono
      rintro n ⟨m, rfl⟩ ⟨j, hj⟩
      omega
    · intro ho
      exact hu (he.even_add_odd ho)
  · refine ⟨fun n ↦ 2 * n, (by intro i j hij; omega), ?_, he⟩
    apply (Set.infinite_range_of_injective (f := fun n : ℕ ↦ 2 * n + 1)
      (by intro i j hij; omega)).mono
    rintro n ⟨m, rfl⟩ ⟨j, hj⟩
    omega

/-- Abstract closed-span fact used for the second assertion of 15.27. -/
theorem closed_span_strictly_decreases_of_removed_vector
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S T : Set E} (hTS : T ⊆ S) {v : E} (hvS : v ∈ S)
    (hvT : v ∉ (Submodule.span ℂ T).topologicalClosure) :
    (Submodule.span ℂ T).topologicalClosure < (Submodule.span ℂ S).topologicalClosure := by
  refine lt_of_le_of_ne (Submodule.topologicalClosure_mono (Submodule.span_mono hTS)) ?_
  intro heq
  apply hvT
  rw [heq]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span hvS)

#print axioms polynomial_span_dense
#print axioms intervalRealPower_nat
#print axioms one_mem_muntzClosure
#print axioms intervalRealPower_mem_muntzClosure
#print axioms muntzClosure_eq_top_of_contains_powers
#print axioms norm_exponentDiscPoint_lt_one
#print axioms exponentDiscPoint_injectiveOn
#print axioms exponentDiscPoint_gap_of_one_le
#print axioms exponentDiscPoint_gap_of_le_one
#print axioms not_summable_exponentDiscPoint_gap
#print axioms discToRightHalfPlane_re_pos
#print axioms discToRightHalfPlane_exponentDiscPoint
#print axioms bounded_halfPlane_zero_on_positive_reals
#print axioms one_not_mem_closed_span_positive_powers
#print axioms exists_infinite_removal_preserving_divergence
#print axioms closed_span_strictly_decreases_of_removed_vector

end RudinRCA.Chapter15.MuntzSzaszWork
