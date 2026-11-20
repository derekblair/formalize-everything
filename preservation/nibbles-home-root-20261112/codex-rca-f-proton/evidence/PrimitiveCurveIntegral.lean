import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
Scratch development of Rudin 13.11 (g) implies (f). Paths may have finitely
many C¹ pieces, with arbitrary partition points. The conclusion uses Mathlib's
actual curveIntegral, not only a separately defined sum of piece integrals.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace RudinRCA.Chapter13

/-- A finite C¹ partition of a path's parameter interval. Repeated partition
points are harmless; arbitrary positive-length pieces are permitted. -/
def IsPiecewiseC1Path {a b : ℂ} (γ : Path a b) : Prop :=
  ∃ (n : ℕ) (t : ℕ → ℝ), Monotone t ∧ t 0 = 0 ∧ t n = 1 ∧
    ∀ k < n, ContDiffOn ℝ 1 γ.extend (Icc (t k) (t (k + 1)))

theorem intervalIntegrable_deriv_of_contDiffOn_interval {ψ : ℝ → ℂ} {a b : ℝ}
    (hψ : ContDiffOn ℝ 1 ψ (Icc a b)) (hab : a ≤ b) :
    IntervalIntegrable (deriv ψ) volume a b := by
  rcases hab.eq_or_lt with rfl | hab'
  · simp
  have hc := (hψ.derivWithin (m := 0) (uniqueDiffOn_Icc hab') (by simp)).continuousOn
  apply (hc.intervalIntegrable_of_Icc (μ := volume) hab).congr_ae
  simp only [hab, uIoc_of_le]
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)

/-- Primitive FTC on one C¹ piece, including integrability. -/
theorem primitive_integral_on_c1_interval {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F f : ℂ → ℂ} (hF : DifferentiableOn ℂ F Ω)
    (hder : ∀ z ∈ Ω, deriv F z = f z) {ψ : ℝ → ℂ} {a b : ℝ}
    (hψ : ContDiffOn ℝ 1 ψ (Icc a b)) (hab : a ≤ b)
    (hmap : MapsTo ψ (Icc a b) Ω) :
    IntervalIntegrable (fun t => f (ψ t) * deriv ψ t) volume a b ∧
      (∫ t in a..b, f (ψ t) * deriv ψ t) = F (ψ b) - F (ψ a) := by
  have hFc : ContDiffOn ℝ 1 F Ω := (hF.contDiffOn hΩ).restrict_scalars ℝ
  have hcomp : ContDiffOn ℝ 1 (F ∘ ψ) (Icc a b) := hFc.comp hψ hmap
  have hchain (t : ℝ) (ht : t ∈ Ioo a b) :
      deriv (F ∘ ψ) t = f (ψ t) * deriv ψ t := by
    have hψt : DifferentiableAt ℝ ψ t :=
      ((hψ t (Ioo_subset_Icc_self ht)).differentiableWithinAt one_ne_zero).differentiableAt
        (Icc_mem_nhds ht.1 ht.2)
    have hFt := hF.differentiableAt (hΩ.mem_nhds (hmap (Ioo_subset_Icc_self ht)))
    rw [← hder (ψ t) (hmap (Ioo_subset_Icc_self ht))]
    exact (hFt.hasDerivAt.comp t hψt.hasDerivAt).deriv
  have hae : (fun t => f (ψ t) * deriv ψ t) =ᵐ[volume.restrict (uIoc a b)]
      deriv (F ∘ ψ) := by
    rw [uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    exact (hchain t ht).symm
  refine ⟨(intervalIntegrable_deriv_of_contDiffOn_interval hcomp hab).congr_ae hae.symm, ?_⟩
  calc
    (∫ t in a..b, f (ψ t) * deriv ψ t) = ∫ t in a..b, deriv (F ∘ ψ) t :=
      intervalIntegral.integral_congr_ae_restrict hae
    _ = F (ψ b) - F (ψ a) := intervalIntegral.integral_deriv_of_contDiffOn_Icc hcomp hab

/-- The integral of a holomorphic primitive's derivative along any finitely
piecewise C¹ path is its endpoint difference. -/
theorem curveIntegral_eq_sub_of_primitive {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F f : ℂ → ℂ} (hF : DifferentiableOn ℂ F Ω)
    (hder : ∀ z ∈ Ω, deriv F z = f z) {a b : ℂ} (γ : Path a b)
    (hγΩ : ∀ t, γ t ∈ Ω) (hγ : IsPiecewiseC1Path γ) :
    curveIntegral (fun z => f z • ContinuousLinearMap.id ℂ ℂ) γ = F b - F a := by
  obtain ⟨n, t, ht, ht0, htn, hpieces⟩ := hγ
  have hmap (s : ℝ) : γ.extend s ∈ Ω := by
    have hs : γ.extend s ∈ Set.range γ := γ.extend_range ▸ Set.mem_range_self s
    obtain ⟨u, hu⟩ := hs
    rw [← hu]
    exact hγΩ u
  have hp (k : ℕ) (hk : k < n) := primitive_integral_on_c1_interval hΩ hF hder
    (hpieces k hk) (ht (Nat.le_succ k)) (fun s _ => hmap s)
  rw [curveIntegral_eq_intervalIntegral_deriv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  have hadd := intervalIntegral.sum_integral_adjacent_intervals (fun k hk => (hp k hk).1)
  rw [ht0, htn] at hadd
  rw [← hadd]
  calc
    (∑ k ∈ Finset.range n, ∫ s in t k..t (k + 1),
      f (γ.extend s) * deriv γ.extend s) =
        ∑ k ∈ Finset.range n, (F (γ.extend (t (k + 1))) - F (γ.extend (t k))) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (hp k (Finset.mem_range.mp hk)).2
    _ = F (γ.extend (t n)) - F (γ.extend (t 0)) :=
      Finset.sum_range_sub (fun k => F (γ.extend (t k))) n
    _ = F b - F a := by simp [ht0, htn]

/-- Rudin 13.11 (g) implies (f), for the full finite piecewise C¹ path class. -/
theorem primitives_imply_zero_closed_piecewise_integrals {Ω : Set ℂ}
    (hΩ : IsOpen Ω)
    (hprimitives : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω →
      ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧ ∀ z ∈ Ω, deriv F z = f z)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) {a : ℂ} (γ : Path a a)
    (hγΩ : ∀ t, γ t ∈ Ω) (hγ : IsPiecewiseC1Path γ) :
    curveIntegral (fun z => f z • ContinuousLinearMap.id ℂ ℂ) γ = 0 := by
  obtain ⟨F, hF, hder⟩ := hprimitives f hf
  rw [curveIntegral_eq_sub_of_primitive hΩ hF hder γ hγΩ hγ]
  exact sub_self _

#print axioms intervalIntegrable_deriv_of_contDiffOn_interval
#print axioms primitive_integral_on_c1_interval
#print axioms curveIntegral_eq_sub_of_primitive
#print axioms primitives_imply_zero_closed_piecewise_integrals

end RudinRCA.Chapter13
