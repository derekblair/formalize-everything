import Mathlib.Algebra.Lie.Basis.Base
import Mathlib.Algebra.Lie.Weights.RootSystem

open LieAlgebra LieAlgebra.IsKilling LieModule LieSubalgebra RootPairing

universe u v

namespace Humphreys14_3

section Base

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- **Humphreys, Proposition 14.3 (p. 77) — Existence of the Chevalley involution.**
For arbitrary prescribed simple-root vectors `x i ∈ L_{αᵢ}` and `y i ∈ L_{-αᵢ}` normalized by
`⁅x i, y i⁆ = αᵢ∨` (`i ∈ Δ`), there exists an involutive automorphism `σ` of `L` (of exact
order `2` whenever `L` is nontrivial) sending `x i ↦ -y i`, `y i ↦ -x i`, and negating `H`. -/
theorem exists_chevalleyInvolution_of_base
    (b : (rootSystem H).Base)
    (x y : ↥b.support → L)
    (hx : ∀ i : ↥b.support, x i ∈ rootSpace H (⇑((i : H.root) : Weight K H L)))
    (hy : ∀ i : ↥b.support, y i ∈ rootSpace H (-⇑((i : H.root) : Weight K H L)))
    (hxy : ∀ i : ↥b.support, ⁅x i, y i⁆ = (((rootSystem H).coroot i : H) : L)) :
    ∃ σ : L ≃ₗ⁅K⁆ L,
      σ.trans σ = LieEquiv.refl ∧
      (Nontrivial L → σ ≠ LieEquiv.refl) ∧
      (∀ i : ↥b.support, σ (x i) = -y i) ∧
      (∀ i : ↥b.support, σ (y i) = -x i) ∧
      (∀ h ∈ H, σ h = -h) := by
  sorry

/-- **Humphreys, §14.3 (p. 77) — Companion uniqueness of the Chevalley involution.**
Because `{x i, y i | i ∈ Δ}` generates `L` (`Prop. 14.2`), an automorphism of `L` is uniquely
determined by its action on `x` and `y`. -/
theorem chevalleyInvolution_unique_of_base
    (b : (rootSystem H).Base)
    (x y : ↥b.support → L)
    (hx : ∀ i : ↥b.support, x i ∈ rootSpace H (⇑((i : H.root) : Weight K H L)))
    (hy : ∀ i : ↥b.support, y i ∈ rootSpace H (-⇑((i : H.root) : Weight K H L)))
    (hxy : ∀ i : ↥b.support, ⁅x i, y i⁆ = (((rootSystem H).coroot i : H) : L))
    {σ₁ σ₂ : L ≃ₗ⁅K⁆ L}
    (hx₁ : ∀ i : ↥b.support, σ₁ (x i) = -y i)
    (hy₁ : ∀ i : ↥b.support, σ₁ (y i) = -x i)
    (hx₂ : ∀ i : ↥b.support, σ₂ (x i) = -y i)
    (hy₂ : ∀ i : ↥b.support, σ₂ (y i) = -x i) :
    σ₁ = σ₂ := by
  sorry

end Base

section LieBasis

variable {ι : Type*} {K : Type u} {L : Type v} [Finite ι]
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {H : LieSubalgebra K L}

/-- **Bundled `LieAlgebra.Basis` form of Proposition 14.3.**
Directly supplies the Cartan-inverting involution `ω : L ≃ₗ⁅K⁆ L` required by
`TauCeti.IsSl2System.exists_isChevalleySystem_of_lieBasis` for Proposition 25.2(a)–(b). -/
theorem existsUnique_chevalleyInvolution_of_lieBasis
    (B : LieAlgebra.Basis ι H) :
    ∃! σ : L ≃ₗ⁅K⁆ L,
      (∀ i : ι, σ (B.e i) = -B.f i) ∧
      (∀ i : ι, σ (B.f i) = -B.e i) ∧
      σ.trans σ = LieEquiv.refl ∧
      (Nontrivial L → σ ≠ LieEquiv.refl) ∧
      (∀ h ∈ H, σ h = -h) := by
  sorry

end LieBasis

end Humphreys14_3
