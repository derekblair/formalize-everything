import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.LinearAlgebra.Span.Basic

/-!
Scratch packaging for Rudin 13.6. In the aggregate check this file follows
RungeFunctional.lean (compactCoordinate and its resolvent evaluation) and
RationalPartialFractions.lean (the reduced quotient evaluation bridge).
No global ring-homomorphism property of totalized rational evaluation is used.
-/

noncomputable section
open Set Polynomial Filter
open scoped Topology OnePoint

namespace RudinRCA.Chapter13

/-- The linear generators allowed by a prescribed set of spherical poles. -/
def rungeGenerators (K : Set ℂ) (A : Set (OnePoint ℂ)) : Set C(K, ℂ) :=
  {g | g = 1 ∨
    (∃ α : ℂ, (α : OnePoint ℂ) ∈ A ∧ ∃ n : ℕ,
      g = (resolvent (compactCoordinate K) α) ^ (n + 1)) ∨
    ((∞ : OnePoint ℂ) ∈ A ∧ ∃ n : ℕ, g = compactCoordinate K ^ n)}

/-- Finite complex linear combinations of the permitted rational generators. -/
def rungeSpace (K : Set ℂ) (A : Set (OnePoint ℂ)) : Submodule ℂ C(K, ℂ) :=
  Submodule.span ℂ (rungeGenerators K A)

/-- A quotient model whose possible finite poles are prescribed. Equality is
only asserted where the model denominator is nonzero. -/
def HasRungeQuotient (A : Set (OnePoint ℂ)) (F : ℂ → ℂ) : Prop :=
  ∃ P Q : ℂ[X], Q ≠ 0 ∧
    (∀ z : ℂ, Q.eval z = 0 → (z : OnePoint ℂ) ∈ A) ∧
    ∀ z : ℂ, Q.eval z ≠ 0 → P.eval z / Q.eval z = F z

/-- Holomorphic removability in the inverse chart at infinity. -/
def RungeRemovableAtInfinity (F : ℂ → ℂ) : Prop :=
  ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧
    ∀ᶠ w in 𝓝[≠] (0 : ℂ), F w⁻¹ = h w

theorem hasRungeQuotient_const (A : Set (OnePoint ℂ)) (c : ℂ) :
    HasRungeQuotient A (fun _ => c) := by
  refine ⟨C c, 1, one_ne_zero, ?_, ?_⟩ <;> simp

theorem hasRungeQuotient_add {A : Set (OnePoint ℂ)} {F G : ℂ → ℂ}
    (hF : HasRungeQuotient A F) (hG : HasRungeQuotient A G) :
    HasRungeQuotient A (fun z => F z + G z) := by
  obtain ⟨P, Q, hQ, hrootsQ, heqF⟩ := hF
  obtain ⟨R, S, hS, hrootsS, heqG⟩ := hG
  refine ⟨P * S + R * Q, Q * S, mul_ne_zero hQ hS, ?_, ?_⟩
  · intro z hz
    rw [eval_mul] at hz
    rcases mul_eq_zero.mp hz with hz | hz
    · exact hrootsQ z hz
    · exact hrootsS z hz
  · intro z hz
    rw [eval_mul] at hz
    have hQz := (mul_ne_zero_iff.mp hz).1
    have hSz := (mul_ne_zero_iff.mp hz).2
    rw [← heqF z hQz, ← heqG z hSz]
    simp only [eval_add, eval_mul]
    field_simp [hQz, hSz] <;> ring

theorem hasRungeQuotient_smul {A : Set (OnePoint ℂ)} {F : ℂ → ℂ}
    (c : ℂ) (hF : HasRungeQuotient A F) :
    HasRungeQuotient A (fun z => c * F z) := by
  obtain ⟨P, Q, hQ, hroots, heq⟩ := hF
  refine ⟨C c * P, Q, hQ, hroots, ?_⟩
  intro z hz
  rw [eval_mul, eval_C, ← heq z hz]
  ring

theorem rungeRemovableAtInfinity_const (c : ℂ) :
    RungeRemovableAtInfinity (fun _ => c) :=
  ⟨fun _ => c, analyticAt_const, Filter.Eventually.of_forall (fun _ => rfl)⟩

theorem rungeRemovableAtInfinity_add {F G : ℂ → ℂ}
    (hF : RungeRemovableAtInfinity F) (hG : RungeRemovableAtInfinity G) :
    RungeRemovableAtInfinity (fun z => F z + G z) := by
  obtain ⟨f, hf, heqf⟩ := hF
  obtain ⟨g, hg, heqg⟩ := hG
  refine ⟨fun w => f w + g w, hf.add hg, ?_⟩
  filter_upwards [heqf, heqg] with w hwf hwg
  rw [hwf, hwg]

theorem rungeRemovableAtInfinity_smul {F : ℂ → ℂ} (c : ℂ)
    (hF : RungeRemovableAtInfinity F) :
    RungeRemovableAtInfinity (fun z => c * F z) := by
  obtain ⟨f, hf, heq⟩ := hF
  refine ⟨fun w => c * f w, analyticAt_const.mul hf, ?_⟩
  filter_upwards [heq] with w hw
  rw [hw]

theorem hasRungeQuotient_reciprocal_power {A : Set (OnePoint ℂ)} (α : ℂ)
    (hα : (α : OnePoint ℂ) ∈ A) (n : ℕ) :
    HasRungeQuotient A (fun z => (α - z)⁻¹ ^ (n + 1)) := by
  have hlinear : (C α - X : ℂ[X]) ≠ 0 := by
    simpa only [neg_sub] using neg_ne_zero.mpr (X_sub_C_ne_zero α)
  refine ⟨1, (C α - X) ^ (n + 1), pow_ne_zero _ hlinear, ?_, ?_⟩
  · intro z hz
    have haz : α = z := by
      by_contra hne
      apply pow_ne_zero (n + 1) (sub_ne_zero.mpr hne)
      simpa only [eval_pow, eval_sub, eval_C, eval_X] using hz
    simpa only [← haz] using hα
  · intro z _
    simp only [eval_one, eval_pow, eval_sub, eval_C, eval_X, one_div, inv_pow]

/-- Every finite principal-part generator is holomorphic at infinity after
the inverse-chart value at zero is supplied. -/
theorem rungeRemovableAtInfinity_reciprocal_power (α : ℂ) (n : ℕ) :
    RungeRemovableAtInfinity (fun z => (α - z)⁻¹ ^ (n + 1)) := by
  have hd : AnalyticAt ℂ (fun w : ℂ => α * w - 1) 0 :=
    (analyticAt_const.mul analyticAt_id).sub analyticAt_const
  have hfrac : AnalyticAt ℂ (fun w : ℂ => w / (α * w - 1)) 0 :=
    analyticAt_id.div hd (by simp)
  refine ⟨fun w => (w / (α * w - 1)) ^ (n + 1), hfrac.pow _, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw0 : w ≠ 0 := by simpa using hw
  have hfactor : α - w⁻¹ = (α * w - 1) / w := by field_simp [hw0]; ring
  rw [hfactor, inv_div]

theorem hasRungeQuotient_coordinate_power (A : Set (OnePoint ℂ)) (n : ℕ) :
    HasRungeQuotient A (fun z => z ^ n) := by
  refine ⟨X ^ n, 1, one_ne_zero, ?_, ?_⟩ <;> simp

/-- Every permitted finite linear combination admits an explicit quotient
model, with a removable point at infinity whenever infinity is not allowed. -/
theorem rungeSpace_quotient_model (K : Set ℂ) (A : Set (OnePoint ℂ))
    (hA : A ⊆ ((fun z : ℂ => (z : OnePoint ℂ)) '' K)ᶜ)
    {g : C(K, ℂ)} (hg : g ∈ rungeSpace K A) :
    ∃ F : ℂ → ℂ, HasRungeQuotient A F ∧
      (∀ x : K, F x = g x) ∧
      ((∞ : OnePoint ℂ) ∉ A → RungeRemovableAtInfinity F) := by
  classical
  apply Submodule.span_induction (p := fun g _ =>
    ∃ F : ℂ → ℂ, HasRungeQuotient A F ∧
      (∀ x : K, F x = g x) ∧
      ((∞ : OnePoint ℂ) ∉ A → RungeRemovableAtInfinity F)) ?_ ?_ ?_ ?_ hg
  · intro g hg
    rcases hg with rfl | ⟨α, hα, n, rfl⟩ | ⟨hinf, n, rfl⟩
    · exact ⟨fun _ => 1, hasRungeQuotient_const A 1,
        fun _ => rfl, fun _ => rungeRemovableAtInfinity_const 1⟩
    · have hαK : α ∉ K := fun hαK => hA hα ⟨α, hαK, rfl⟩
      refine ⟨fun z => (α - z)⁻¹ ^ (n + 1),
        hasRungeQuotient_reciprocal_power α hα n, ?_,
        fun _ => rungeRemovableAtInfinity_reciprocal_power α n⟩
      intro x
      simp only [ContinuousMap.pow_apply, compactCoordinate_resolvent_apply K hαK]
    · refine ⟨fun z => z ^ n, hasRungeQuotient_coordinate_power A n,
        fun _ => rfl, ?_⟩
      exact fun hnot => (hnot hinf).elim
  · exact ⟨fun _ => 0, hasRungeQuotient_const A 0,
      fun _ => rfl, fun _ => rungeRemovableAtInfinity_const 0⟩
  · intro g h _ _ hg hh
    obtain ⟨F, hF, heqF, hinfF⟩ := hg
    obtain ⟨G, hG, heqG, hinfG⟩ := hh
    refine ⟨fun z => F z + G z, hasRungeQuotient_add hF hG, ?_, ?_⟩
    · intro x
      simp only [heqF, heqG, ContinuousMap.add_apply]
    · exact fun hnot => rungeRemovableAtInfinity_add (hinfF hnot) (hinfG hnot)
  · intro c g _ hg
    obtain ⟨F, hF, heqF, hinfF⟩ := hg
    refine ⟨fun z => c * F z, hasRungeQuotient_smul c hF, ?_, ?_⟩
    · intro x
      simp only [heqF, ContinuousMap.smul_apply, smul_eq_mul]
    · exact fun hnot => rungeRemovableAtInfinity_smul c (hinfF hnot)

/-- A nonzero polynomial denominator has no zeros sufficiently near infinity. -/
theorem eventually_polynomial_eval_inv_ne_zero (Q : ℂ[X]) (hQ : Q ≠ 0) :
    ∀ᶠ w in 𝓝[≠] (0 : ℂ), Q.eval w⁻¹ ≠ 0 :=
  (Filter.tendsto_inv₀_nhdsNE_zero.mono_right (Bornology.le_cofinite ℂ)).eventually
    (Polynomial.eventually_eval_ne_zero_cofinite hQ)

/-- A member of the Runge generator space is the restriction of an actual
rational function, with no finite poles outside A and no pole at infinity
when infinity is not in A. -/
theorem rungeSpace_ratFunc_witness (K : Set ℂ) (A : Set (OnePoint ℂ))
    (hA : A ⊆ ((fun z : ℂ => (z : OnePoint ℂ)) '' K)ᶜ)
    {g : C(K, ℂ)} (hg : g ∈ rungeSpace K A) :
    ∃ R : RatFunc ℂ,
      (∀ z : ℂ, R.denom.eval z = 0 → (z : OnePoint ℂ) ∈ A) ∧
      (∀ x : K, RatFunc.eval (RingHom.id ℂ) x R = g x) ∧
      ((∞ : OnePoint ℂ) ∉ A →
        RungeRemovableAtInfinity (fun z => RatFunc.eval (RingHom.id ℂ) z R)) := by
  obtain ⟨F, ⟨P, Q, hQ, hroots, heq⟩, hFK, hinf⟩ := rungeSpace_quotient_model K A hA hg
  let R : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q
  have heval (z : ℂ) (hz : Q.eval z ≠ 0) : RatFunc.eval (RingHom.id ℂ) z R = F z := by
    exact (rational_quotient_evaluation P Q z hz).2.trans (heq z hz)
  refine ⟨R, ?_, ?_, ?_⟩
  · intro z hz
    apply hroots
    obtain ⟨S, hS⟩ := RatFunc.denom_div_dvd P Q
    rw [hS, eval_mul]
    change R.denom.eval z * S.eval z = 0
    rw [hz, zero_mul]
  · intro x
    have hQx : Q.eval x ≠ 0 := fun hx => hA (hroots x hx) ⟨x, x.property, rfl⟩
    exact (heval x hQx).trans (hFK x)
  · intro hnot
    obtain ⟨h, hh, heqh⟩ := hinf hnot
    refine ⟨h, hh, ?_⟩
    filter_upwards [heqh, eventually_polynomial_eval_inv_ne_zero Q hQ] with w hw hQw
    exact (heval w⁻¹ hQw).trans hw

#print axioms hasRungeQuotient_const
#print axioms hasRungeQuotient_add
#print axioms hasRungeQuotient_smul
#print axioms rungeRemovableAtInfinity_const
#print axioms rungeRemovableAtInfinity_add
#print axioms rungeRemovableAtInfinity_smul
#print axioms hasRungeQuotient_reciprocal_power
#print axioms rungeRemovableAtInfinity_reciprocal_power
#print axioms hasRungeQuotient_coordinate_power
#print axioms rungeSpace_quotient_model
#print axioms eventually_polynomial_eval_inv_ne_zero
#print axioms rungeSpace_ratFunc_witness

end RudinRCA.Chapter13
