import Mathlib.Algebra.Lie.Basis.Base
import TauCeti.Algebra.Lie.Weights.Chevalley.BaseSquare
import TauCeti.Algebra.Lie.Weights.Chevalley.Involution
import TauCeti.Algebra.Lie.Weights.StructureConstant.Opposite

open LieAlgebra LieAlgebra.IsKilling LieModule

universe u v

namespace Humphreys25_2

section SplitKilling

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- **Humphreys, Proposition 25.2(a)–(b) (pp. 146–147) — Direct structure-constant form.**
For any finite-dimensional split Killing Lie algebra `L` over a characteristic-zero field `K`,
there exists a coroot-normalized root-vector system `x` (`IsSl2System x`, encoding `x α ∈ L_α`,
`x α ≠ 0` for `α ≠ 0`, and `(a)` `⁅x α, x (-α)⁆ = α∨`) whose structure constants satisfy `(b)`
`c(-α, -β) = -c(α, β)` on every genuine root sum `γ = α + β`. -/
theorem exists_rootVectors_chevalley_ab :
    ∃ (x : Weight K H L → L) (hx : TauCeti.IsSl2System x),
      ∀ (α β γ : Weight K H L)
        (_hα : α.IsNonZero) (_hβ : β.IsNonZero) (hγ : γ.IsNonZero)
        (hαβ : (γ : H → K) = (α : H → K) + β)
        (hneg : ((-γ : Weight K H L) : H → K) =
          ((-α : Weight K H L) : H → K) + (-β : Weight K H L)),
        hx.structureConstant (-α) (-β) (-γ) hγ.neg hneg =
          -hx.structureConstant α β γ hγ hαβ := by
  sorry

/-- **Humphreys, Proposition 25.2(a)–(b) (pp. 146–147) — `IsChevalleySystem` form.**
Equivalent (via `Opposite.structureConstant_neg_neg_eq_neg_iff` and
`Involution.exists_isChevalleySystem`) packaged form supplying both the Chevalley involution
`ω : L ≃ₗ⁅K⁆ L` and the compatible root-vector system `x : Weight K H L → L`. -/
theorem exists_isChevalleySystem :
    ∃ (ω : L ≃ₗ⁅K⁆ L) (x : Weight K H L → L),
      TauCeti.IsChevalleySystem ω x := by
  sorry

end SplitKilling

section ExtendingLieBasis

variable {ι : Type*} {K : Type u} {L : Type v} [Fintype ι]
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L}

/-- **Strongest split form of Proposition 25.2(a)–(b): Chevalley system extending a given
`LieAlgebra.Basis` on simple roots.** -/
theorem exists_isChevalleySystem_extending_lieBasis
    (B : LieAlgebra.Basis ι H) :
    letI := B.isCartanSubalgebra
    letI := B.isTriangularizable
    ∃ (ω : L ≃ₗ⁅K⁆ L) (x : Weight K H L → L),
      TauCeti.IsChevalleySystem ω x ∧
        ∀ i : ι, x (B.baseSupportEquiv i) = B.e i ∧
          x (-B.baseSupportEquiv i) = B.f i := by
  sorry

end ExtendingLieBasis

end Humphreys25_2
