import Humphreys.Ch4.ChevalleyInvolution14_3
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

omit [CharZero K] in
private lemma isChevalleySystem_zero_of_subsingleton [Subsingleton L] :
    TauCeti.IsChevalleySystem (LieEquiv.refl : L ≃ₗ⁅K⁆ L) (0 : Weight K H L → L) where
  toIsSl2System :=
    { mem_rootSpace := fun _ ↦ zero_mem _
      lie_neg := fun _ _ ↦ Subsingleton.elim _ _
      eq_zero_of_isZero := fun _ _ ↦ rfl }
  map_root _ := by simp

private lemma exists_isChevalleySystem_extending_lieBasis_of_nontrivial
    [Nontrivial L] {ι : Type*} [Fintype ι] (B : LieAlgebra.Basis ι H) :
    ∃ (ω : L ≃ₗ⁅K⁆ L) (x : Weight K H L → L),
      ω ≠ LieEquiv.refl ∧
        TauCeti.IsChevalleySystem ω x ∧
          ∀ i : ι, x (B.baseSupportEquiv i) = B.e i ∧
            x (-B.baseSupportEquiv i) = B.f i := by
  obtain ⟨ω, ⟨hωe, _, _, hω_ne_refl, hωH⟩, _⟩ :=
    Humphreys14_3.existsUnique_chevalleyInvolution_of_lieBasis B
  obtain ⟨x₀, hx₀⟩ := TauCeti.exists_isSl2System K H
  obtain ⟨x₁, hx₁⟩ := hx₀.exists_isChevalleySystem_of_lieBasis ω hωH B hωe
  obtain ⟨x, hx, hsimple⟩ := hx₁.exists_isChevalleySystem_simple_eq_lieBasis B hωe
  exact ⟨ω, x, hω_ne_refl ‹Nontrivial L›, hx, hsimple⟩

private lemma exists_isChevalleySystem_extending_lieBasis_aux
    {ι : Type*} [Fintype ι] (B : LieAlgebra.Basis ι H) :
    ∃ (ω : L ≃ₗ⁅K⁆ L) (x : Weight K H L → L),
      TauCeti.IsChevalleySystem ω x ∧
        ∀ i : ι, x (B.baseSupportEquiv i) = B.e i ∧
          x (-B.baseSupportEquiv i) = B.f i := by
  by_cases hL : Subsingleton L
  · let _ : Subsingleton L := hL
    exact ⟨LieEquiv.refl, 0, isChevalleySystem_zero_of_subsingleton,
      fun _ ↦ ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  · let _ : Nontrivial L := not_subsingleton_iff_nontrivial.mp hL
    obtain ⟨ω, x, _, hx, hsimple⟩ :=
      exists_isChevalleySystem_extending_lieBasis_of_nontrivial B
    exact ⟨ω, x, hx, hsimple⟩

private lemma exists_isChevalleySystem_aux :
    ∃ (ω : L ≃ₗ⁅K⁆ L) (x : Weight K H L → L),
      TauCeti.IsChevalleySystem ω x := by
  by_cases hL : Subsingleton L
  · let _ : Subsingleton L := hL
    exact ⟨LieEquiv.refl, 0, isChevalleySystem_zero_of_subsingleton⟩
  · let _ : Nontrivial L := not_subsingleton_iff_nontrivial.mp hL
    obtain ⟨b⟩ := (rootSystem H).nonempty_base
    obtain ⟨B, _, _⟩ := LieAlgebra.exists_basis_of_base b
    obtain ⟨ω, x, _, hx, _⟩ :=
      exists_isChevalleySystem_extending_lieBasis_of_nontrivial B
    exact ⟨ω, x, hx⟩

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
  obtain ⟨_, x, hx⟩ := exists_isChevalleySystem_aux (K := K) (L := L) (H := H)
  refine ⟨x, hx.toIsSl2System, fun α β γ hα hβ hγ hαβ _ ↦ ?_⟩
  exact (hx.toIsSl2System.structureConstant_neg_neg_eq_neg_iff α β γ hα hβ hγ hαβ).2
    (hx.structureConstant_eq_natCast_or_eq_neg_natCast α β γ hα hβ hγ hαβ)

/-- **Humphreys, Proposition 25.2(a)–(b) (pp. 146–147) — `IsChevalleySystem` form.**
Equivalent (via `Opposite.structureConstant_neg_neg_eq_neg_iff` and
`Involution.exists_isChevalleySystem`) packaged form supplying both the Chevalley involution
`ω : L ≃ₗ⁅K⁆ L` and the compatible root-vector system `x : Weight K H L → L`. -/
theorem exists_isChevalleySystem :
    ∃ (ω : L ≃ₗ⁅K⁆ L) (x : Weight K H L → L),
      TauCeti.IsChevalleySystem ω x := by
  exact exists_isChevalleySystem_aux

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
  let _ : H.IsCartanSubalgebra := B.isCartanSubalgebra
  have _ : LieModule.IsTriangularizable K H L := B.isTriangularizable
  exact exists_isChevalleySystem_extending_lieBasis_aux B

end ExtendingLieBasis

end Humphreys25_2
