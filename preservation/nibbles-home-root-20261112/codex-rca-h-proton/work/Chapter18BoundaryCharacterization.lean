import Chapter18Disc
import Chapter18CoreFejer
import Chapter18Maximality
import Mathlib.Tactic.FieldSimp

noncomputable section
open Set
open scoped Polynomial

namespace RudinRCA.Chapter18

/-- The angular Fourier coefficient uses exactly the normalization and
exponential appearing in printed18.19(1). -/
theorem theorem18_19_circle_coefficient_integral (f : C(DiscCircle, ℂ)) (n : ℤ) :
    fourierCoeff (discAngleTransport f) n =
      (1 / (2 * Real.pi) : ℝ) • ∫ θ in -Real.pi..Real.pi,
        f (Circle.exp θ) * Complex.exp (-((n : ℂ) * θ * Complex.I)) := by
  rw [fourierCoeff_eq_intervalIntegral (discAngleTransport f) n (-Real.pi)]
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  have hangle : discAngleHomeomorph (θ : AddCircle (2 * Real.pi)) = Circle.exp θ := by
    apply Subtype.ext
    change ((AddCircle.homeomorphCircle (by positivity)
      (θ : AddCircle (2 * Real.pi)) : Circle) : ℂ) = _
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
    simp [Real.pi_ne_zero]
  have hfourier : @fourier (2 * Real.pi) (-n) θ =
      Complex.exp (-((n : ℂ) * θ * Complex.I)) := by
    rw [fourier_coe_apply]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
    <;> ring
  change fourier (-n) (θ : AddCircle (2 * Real.pi)) *
    f (discAngleHomeomorph (θ : AddCircle (2 * Real.pi))) = _
  rw [hangle, hfourier, mul_comm]

/-- Printed18.19: continuous boundary functions of the disc algebra are exactly
the continuous functions with vanishing negative Fourier coefficients. -/
theorem theorem18_19_fourier_iff (f : C(AddCircle (2 * Real.pi), ℂ)) :
    f ∈ discAngleSubalgebra ↔ ∀ n : ℤ, n < 0 → fourierCoeff f n = 0 := by
  change f ∈ discAngleSubalgebra.toSubmodule ↔ _
  rw [discAngleSubalgebra_eq_positive_closure]
  exact (Fejer.fourier_negative_vanish_iff_mem_positive_closure f).symm

theorem theorem18_19_transport_injective : Function.Injective discAngleTransport := by
  intro f g hfg
  ext z
  obtain ⟨t, rfl⟩ := discAngleHomeomorph.surjective z
  exact congrArg (fun h : C(AddCircle (2 * Real.pi), ℂ) => h t) hfg

/-- The characterization is stated here on the printed unit circle itself;
`discAngleTransport` is the standard angular parameterization. -/
theorem theorem18_19_circle_fourier_iff (f : C(DiscCircle, ℂ)) :
    f ∈ discBoundarySubalgebra ↔
      ∀ n : ℤ, n < 0 → fourierCoeff (discAngleTransport f) n = 0 := by
  rw [← theorem18_19_fourier_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, theorem18_19_transport_injective hg⟩

/-- The analytic boundary algebra is proper: the conjugate coordinate has
a nonzero Fourier coefficient of index minus one. -/
theorem theorem18_19_proper : discAngleSubalgebra ≠ ⊤ := by
  intro htop
  have hf : (@fourier (2 * Real.pi) (-1)) ∈ discAngleSubalgebra := by
    rw [htop]
    trivial
  have h := (theorem18_19_fourier_iff _).mp hf (-1) (by norm_num)
  simpa [fourierCoeff_fourier] using h

theorem theorem18_19_circle_proper : discBoundarySubalgebra ≠ ⊤ := by
  intro htop
  have hcoord : discAngleTransport (star (discBoundary discCoordinate)) =
      @fourier (2 * Real.pi) (-1) := by
    ext t
    change star ((discAngleBoundary discCoordinate) t) = fourier (-1) t
    rw [discAngleBoundary_coordinate]
    exact (fourier_neg (n := 1) (x := t)).symm
  have hf : star (discBoundary discCoordinate) ∈ discBoundarySubalgebra := by
    rw [htop]
    trivial
  have h := (theorem18_19_circle_fourier_iff _).mp hf (-1) (by norm_num)
  rw [hcoord, fourierCoeff_fourier] at h
  simpa using h

/-- Printed18.19 maximality: a closed algebra containing the analytic boundary
algebra equals it or equals all continuous functions on the circle. -/
theorem theorem18_19_maximal
    (B : Subalgebra ℂ C(AddCircle (2 * Real.pi), ℂ))
    (hclosed : IsClosed (B : Set C(AddCircle (2 * Real.pi), ℂ)))
    (hcontains : discAngleSubalgebra ≤ B) :
    B = discAngleSubalgebra ∨ B = ⊤ := by
  by_cases htop : B = ⊤
  · exact Or.inr htop
  · apply Or.inl
    apply le_antisymm _ hcontains
    intro f hf
    apply (theorem18_19_fourier_iff f).mpr
    intro n hn
    have hcoordinate : @fourier (2 * Real.pi) 1 ∈ B :=
      hcontains ⟨discCoordinate, discAngleBoundary_coordinate⟩
    exact theorem18_20_proper_subalgebra_negative_coeff B hclosed htop hcoordinate ⟨f, hf⟩ n hn

/-- The same maximality assertion on the printed unit circle, before angular
parameterization. -/
theorem theorem18_19_circle_maximal (B : Subalgebra ℂ C(DiscCircle, ℂ))
    (hclosed : IsClosed (B : Set C(DiscCircle, ℂ)))
    (hcontains : discBoundarySubalgebra ≤ B) :
    B = discBoundarySubalgebra ∨ B = ⊤ := by
  let B' := B.map discAngleTransport
  have hisometry : Isometry discAngleTransport :=
    AddMonoidHomClass.isometry_of_norm discAngleTransport discAngleTransport_norm
  have hclosed' : IsClosed (B' : Set C(AddCircle (2 * Real.pi), ℂ)) :=
    hisometry.isClosedEmbedding.isClosedMap _ hclosed
  have hcontains' : discAngleSubalgebra ≤ B' := by
    rintro f ⟨g, rfl⟩
    exact ⟨discBoundary g, hcontains ⟨g, rfl⟩, rfl⟩
  rcases theorem18_19_maximal B' hclosed' hcontains' with hB | hB
  · apply Or.inl
    apply le_antisymm _ hcontains
    intro f hf
    apply (theorem18_19_circle_fourier_iff f).mpr
    apply (theorem18_19_fourier_iff (discAngleTransport f)).mp
    rw [← hB]
    exact ⟨f, hf, rfl⟩
  · apply Or.inr
    apply top_unique
    intro f _
    have htf : discAngleTransport f ∈ B' := by rw [hB]; trivial
    rcases htf with ⟨g, hg, hgf⟩
    have hgf' : g = f := theorem18_19_transport_injective hgf
    simpa only [hgf'] using hg

/-- Printed18.20 on the original unit circle: the coefficient polynomials use
the complex coordinate `z`, and one finite family works uniformly on the circle. -/
theorem theorem18_20_circle (g : C(DiscCircle, ℂ))
    (hg : ∃ n : ℤ, n < 0 ∧ fourierCoeff (discAngleTransport g) n ≠ 0)
    (f : C(DiscCircle, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (P : ℕ → ℂ[X]), ∀ z : DiscCircle,
      ‖f z - ∑ i ∈ Finset.range (N + 1), (P i).eval (z : ℂ) * g z ^ i‖ < ε := by
  obtain ⟨N, P, hP⟩ := theorem18_20 (discAngleTransport g) hg
    (discAngleTransport f) ε hε
  refine ⟨N, P, ?_⟩
  intro z
  let t := discAngleHomeomorph.symm z
  have ht : discAngleHomeomorph t = z := discAngleHomeomorph.apply_symm_apply z
  have hcoordinate : fourier 1 t = (z : ℂ) := by
    have h := congrArg (fun h : C(AddCircle (2 * Real.pi), ℂ) => h t)
      discAngleBoundary_coordinate
    change (discAngleHomeomorph t : ℂ) = fourier 1 t at h
    rw [ht] at h
    exact h.symm
  have h := hP t
  change ‖f (discAngleHomeomorph t) - ∑ i ∈ Finset.range (N + 1),
    (P i).eval (fourier 1 t) * g (discAngleHomeomorph t) ^ i‖ < ε at h
  simpa only [ht, hcoordinate] using h

end RudinRCA.Chapter18

#print axioms RudinRCA.Chapter18.theorem18_19_fourier_iff
#print axioms RudinRCA.Chapter18.theorem18_19_circle_coefficient_integral
#print axioms RudinRCA.Chapter18.theorem18_19_circle_fourier_iff
#print axioms RudinRCA.Chapter18.theorem18_19_proper
#print axioms RudinRCA.Chapter18.theorem18_19_circle_proper
#print axioms RudinRCA.Chapter18.theorem18_19_maximal
#print axioms RudinRCA.Chapter18.theorem18_19_circle_maximal
#print axioms RudinRCA.Chapter18.theorem18_20_circle
