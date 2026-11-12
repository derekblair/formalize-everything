import RudinRCA.Chapter13
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/- Prerequisites, in order: RungeFunctional.lean, CauchyTransformSphere.lean,
   ContourAnnihilator.lean, RungeRationalWitness.lean. This file does not assert existence of the 13.5
   contour; it packages the exact universal representation needed as input. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval BigOperators OnePoint

namespace RudinRCA.Chapter13

/-- The finite integral data extracted from a 13.5 cycle. The image of every
    edge lies in Ω\K, and the Cauchy identity holds for every holomorphic f. -/
structure FiniteCauchyRepresentation (K Ω : Set ℂ) where
  edgeCount : ℕ
  lower upper : Fin edgeCount → ℝ
  path density : Fin edgeCount → ℝ → ℂ
  subset_domain : K ⊆ Ω
  path_continuous : ∀ i, ContinuousOn (path i) [[lower i, upper i]]
  density_continuous : ∀ i, ContinuousOn (density i) [[lower i, upper i]]
  path_mem : ∀ i t, t ∈ [[lower i, upper i]] → path i t ∈ Ω \ K
  cauchy_identity : ∀ (f : ℂ → ℂ), DifferentiableOn ℂ f Ω → ∀ z ∈ K,
    f z = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ∑ i, ∫ t in lower i..upper i, (f (path i t) * density i t) / (path i t - z)

/-- Restriction of a holomorphic function to a compact subset of its domain. -/
def holomorphicRestriction (K Ω : Set ℂ) (hKΩ : K ⊆ Ω)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) : C(K, ℂ) :=
  ⟨fun z ↦ f z, continuousOn_iff_continuous_domRestrict.mp (hf.continuousOn.mono hKΩ)⟩

/-- The 13.5 representation and one prescribed point per spherical complement
    component place every holomorphic restriction in the closure of any
    submodule containing the corresponding principal parts and polynomials. -/
theorem FiniteCauchyRepresentation.restriction_mem_submodule_closure
    {K Ω : Set ℂ} [CompactSpace K] (C : FiniteCauchyRepresentation K Ω)
    (A : Set RiemannSphere) (M : Submodule ℂ C(K, ℂ))
    (hA : A ⊆ (((↑) : ℂ → RiemannSphere) '' K)ᶜ)
    (hcomponents : ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
      ∃ a ∈ A, a ∈ connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K)ᶜ p)
    (hfinite : ∀ α : ℂ, (α : RiemannSphere) ∈ A →
      ∀ n : ℕ, resolvent (compactCoordinate K) α ^ (n + 1) ∈ M)
    (hinfty : (∞ : RiemannSphere) ∈ A → ∀ n : ℕ, compactCoordinate K ^ n ∈ M)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) :
    holomorphicRestriction K Ω C.subset_domain f hf ∈ M.topologicalClosure := by
  apply (mem_submodule_closure_iff_annihilators M _).mpr
  intro L hLM
  have hL : ∀ z ∉ K, L (resolvent (compactCoordinate K) z) = 0 :=
    compact_cauchy_transform_eq_zero K L A hA hcomponents
      (fun α hα n ↦ hLM _ (hfinite α hα n))
      (fun h∞ n ↦ hLM _ (hinfty h∞ n))
  apply dual_eq_zero_of_finite_contour_representation K _ L C.path
    (fun i t ↦ f (C.path i t) * C.density i t) C.lower C.upper
    ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) C.path_continuous
  · intro i
    exact (hf.continuousOn.comp (C.path_continuous i)
      (fun t ht ↦ (C.path_mem i t ht).1)).mul (C.density_continuous i)
  · intro i t ht
    exact (C.path_mem i t ht).2
  · intro x
    exact C.cauchy_identity f hf x x.property
  · exact hL

/-- Quantitative approximation follows from closure in the C(K) norm.
    The rational-function witness is supplied separately by the generator algebra. -/
theorem FiniteCauchyRepresentation.exists_submodule_approximation
    {K Ω : Set ℂ} [CompactSpace K] (C : FiniteCauchyRepresentation K Ω)
    (A : Set RiemannSphere) (M : Submodule ℂ C(K, ℂ))
    (hA : A ⊆ (((↑) : ℂ → RiemannSphere) '' K)ᶜ)
    (hcomponents : ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
      ∃ a ∈ A, a ∈ connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K)ᶜ p)
    (hfinite : ∀ α : ℂ, (α : RiemannSphere) ∈ A →
      ∀ n : ℕ, resolvent (compactCoordinate K) α ^ (n + 1) ∈ M)
    (hinfty : (∞ : RiemannSphere) ∈ A → ∀ n : ℕ, compactCoordinate K ^ n ∈ M)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ M, ∀ x : K, ‖f x - g x‖ < ε := by
  let F : C(K, ℂ) := holomorphicRestriction K Ω C.subset_domain f hf
  have hF : F ∈ closure (M : Set C(K, ℂ)) :=
    C.restriction_mem_submodule_closure A M hA hcomponents hfinite hinfty f hf
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hF ε hε
  refine ⟨g, hg, fun x ↦ ?_⟩
  have hp := ContinuousMap.dist_apply_le_dist (f := F) (g := g) x
  simpa only [dist_eq_norm] using hp.trans_lt hdist

/-- Full rational-approximation conclusion from an explicitly supplied universal
    13.5 representation. Existence of that representation is proved separately. -/
theorem FiniteCauchyRepresentation.exists_rational_approximation
    {K Ω : Set ℂ} [CompactSpace K] (C : FiniteCauchyRepresentation K Ω)
    (A : Set RiemannSphere)
    (hA : A ⊆ (((↑) : ℂ → RiemannSphere) '' K)ᶜ)
    (hcomponents : ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
      ∃ a ∈ A, a ∈ connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K)ᶜ p)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : RatFunc ℂ,
      (∀ z : ℂ, R.denom.eval z = 0 → (z : RiemannSphere) ∈ A) ∧
      ((∞ : RiemannSphere) ∉ A →
        RungeRemovableAtInfinity (fun z ↦ RatFunc.eval (RingHom.id ℂ) z R)) ∧
      ∀ z ∈ K, ‖f z - RatFunc.eval (RingHom.id ℂ) z R‖ < ε := by
  have hfinite : ∀ α : ℂ, (α : RiemannSphere) ∈ A →
      ∀ n : ℕ, resolvent (compactCoordinate K) α ^ (n + 1) ∈ rungeSpace K A := by
    intro α hα n
    exact Submodule.subset_span (Or.inr (Or.inl ⟨α, hα, n, rfl⟩))
  have hinfty : (∞ : RiemannSphere) ∈ A →
      ∀ n : ℕ, compactCoordinate K ^ n ∈ rungeSpace K A := by
    intro h∞ n
    exact Submodule.subset_span (Or.inr (Or.inr ⟨h∞, n, rfl⟩))
  obtain ⟨g, hg, herror⟩ :=
    C.exists_submodule_approximation A (rungeSpace K A) hA hcomponents hfinite hinfty f hf hε
  obtain ⟨R, hRfinite, hReval, hRinfty⟩ := rungeSpace_ratFunc_witness K A hA hg
  refine ⟨R, hRfinite, hRinfty, ?_⟩
  intro z hz
  simpa only [← hReval ⟨z, hz⟩] using herror ⟨z, hz⟩

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.FiniteCauchyRepresentation.restriction_mem_submodule_closure
#print axioms RudinRCA.Chapter13.FiniteCauchyRepresentation.exists_submodule_approximation
#print axioms RudinRCA.Chapter13.FiniteCauchyRepresentation.exists_rational_approximation
