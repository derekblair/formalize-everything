import Mathlib.Algebra.Lie.Basis.Base
import Mathlib.Algebra.Lie.Weights.RootSystem
import TauCeti.Algebra.Lie.Basis.Root
import TauCeti.Algebra.Lie.Presentation.Serre.Automorphism
import TauCeti.Algebra.Lie.Presentation.Serre.Injective
import TauCeti.Algebra.Lie.Presentation.Serre.Killing

open LieAlgebra LieAlgebra.IsKilling LieModule LieSubalgebra RootPairing

universe u v

namespace Humphreys14_3

section Base

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

private lemma isSl2Triple_of_mem_rootSpace_of_lie_eq_coroot
    (b : (rootSystem H).Base)
    {x y : ↥b.support → L}
    (hx : ∀ i : ↥b.support, x i ∈ rootSpace H (⇑((i : H.root) : Weight K H L)))
    (hy : ∀ i : ↥b.support, y i ∈ rootSpace H (-⇑((i : H.root) : Weight K H L)))
    (hxy : ∀ i : ↥b.support, ⁅x i, y i⁆ = (((rootSystem H).coroot i : H) : L))
    (i : ↥b.support) :
    IsSl2Triple (((rootSystem H).coroot i : H) : L) (x i) (y i) where
  h_ne_zero := by
    simpa only [ne_eq, ZeroMemClass.coe_eq_zero, rootSystem_coroot_apply,
      coroot_eq_zero_iff] using H.isNonZero_coe_root (i : H.root)
  lie_e_f := hxy i
  lie_h_e_nsmul := by
    rw [← LieSubalgebra.coe_bracket_of_module, lie_eq_smul_of_mem_rootSpace (hx i),
      rootSystem_coroot_apply, root_apply_coroot (H.isNonZero_coe_root (i : H.root)),
      two_smul, two_smul]
  lie_h_f_nsmul := by
    rw [← LieSubalgebra.coe_bracket_of_module, lie_eq_smul_of_mem_rootSpace (hy i),
      Pi.neg_apply, rootSystem_coroot_apply, root_apply_coroot (H.isNonZero_coe_root (i : H.root)),
      neg_smul, two_smul, two_smul]

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
  let _ : DecidableEq ↥b.support := Classical.decEq _
  have hsl2 : ∀ i : ↥b.support, IsSl2Triple (((rootSystem H).coroot i : H) : L) (x i) (y i) :=
    isSl2Triple_of_mem_rootSpace_of_lie_eq_coroot b hx hy hxy
  have hS : TauCeti.IsSerreSystem K b.cartanMatrix.transpose
      (fun i ↦ (((rootSystem H).coroot i : H) : L)) x y :=
    TauCeti.isSerreSystem_coroot b hsl2 hx hy
  have hspan : lieSpan K L (Set.range x ∪ Set.range y) = ⊤ :=
    lieSpan_range_union_eq_top_of_mem_rootSpace b x y hsl2 hx hy
  let eL : Matrix.ToLieAlgebra K b.cartanMatrix.transpose ≃ₗ⁅K⁆ L :=
    TauCeti.serreLiftEquiv hS hspan
  let τ :
      Matrix.ToLieAlgebra K b.cartanMatrix.transpose ≃ₗ⁅K⁆
        Matrix.ToLieAlgebra K b.cartanMatrix.transpose :=
    TauCeti.serreChevalleyInvolution K b.cartanMatrix.transpose
  let σ : L ≃ₗ⁅K⁆ L := eL.symm.trans (τ.trans eL)
  have hσx : ∀ i : ↥b.support, σ (x i) = -y i := fun i ↦ by
    simp [σ, eL, τ]
  have hσy : ∀ i : ↥b.support, σ (y i) = -x i := fun i ↦ by
    simp [σ, eL, τ]
  have hσ_coroot : ∀ i : ↥b.support,
      σ (((rootSystem H).coroot i : H) : L) = -(((rootSystem H).coroot i : H) : L) := fun i ↦ by
    rw [← hxy i, σ.map_lie, hσx i, hσy i, neg_lie, lie_neg, neg_neg, ← lie_skew]
  have hσ_inv : σ.trans σ = LieEquiv.refl := by
    ext z
    simp [σ, τ]
  have hσH : ∀ h ∈ H, σ h = -h := by
    obtain ⟨B₀, -, hB₀h⟩ := exists_basis_of_base b
    have hH_span : (H : Submodule K L) =
        Submodule.span K (Set.range fun i : ↥b.support ↦ (((rootSystem H).coroot i : H) : L)) := by
      simpa [funext hB₀h] using B₀.coe_cartan_eq_span
    intro h hh
    rw [← LieSubalgebra.mem_toSubmodule, hH_span] at hh
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hh
    · rintro _ ⟨i, rfl⟩
      exact hσ_coroot i
    · simp
    · intro u v _ _ hu hv
      rw [map_add, hu, hv, neg_add]
    · intro c u _ hu
      rw [map_smul, hu, smul_neg]
  have hσ_ne : Nontrivial L → σ ≠ LieEquiv.refl := by
    intro hnt hσ_refl
    have hne : Nonempty ↥b.support := by
      rw [← not_isEmpty_iff]
      intro hempty
      have hbot : (⊥ : LieSubalgebra K L) = ⊤ := by
        simpa [Set.range_eq_empty] using hspan
      obtain ⟨z, hz⟩ := exists_ne (0 : L)
      have hz_top : z ∈ (⊤ : LieSubalgebra K L) := LieSubalgebra.mem_top z
      rw [← hbot, LieSubalgebra.mem_bot] at hz_top
      exact hz hz_top
    obtain ⟨i⟩ := hne
    have hx_eq : x i = -y i := by
      calc
        x i = LieEquiv.refl (x i) := rfl
        _ = σ (x i) := by rw [hσ_refl]
        _ = -y i := hσx i
    have hc0 : (((rootSystem H).coroot i : H) : L) = 0 := by
      rw [← hxy i, hx_eq, neg_lie, lie_self, neg_zero]
    exact (hsl2 i).h_ne_zero hc0
  exact ⟨σ, hσ_inv, hσ_ne, hσx, hσy, hσH⟩

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
  have hsl2 : ∀ i : ↥b.support, IsSl2Triple (((rootSystem H).coroot i : H) : L) (x i) (y i) :=
    isSl2Triple_of_mem_rootSpace_of_lie_eq_coroot b hx hy hxy
  have hspan : lieSpan K L (Set.range x ∪ Set.range y) = ⊤ :=
    lieSpan_range_union_eq_top_of_mem_rootSpace b x y hsl2 hx hy
  ext z
  have hz : z ∈ lieSpan K L (Set.range x ∪ Set.range y) := by
    rw [hspan]
    exact LieSubalgebra.mem_top z
  induction hz using LieSubalgebra.lieSpan_induction with
  | mem _ hmem =>
    rcases hmem with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact (hx₁ i).trans (hx₂ i).symm
    · exact (hy₁ i).trans (hy₂ i).symm
  | zero => simp
  | add _ _ _ _ hu hv => rw [map_add, hu, hv, map_add]
  | smul _ _ _ hu => rw [map_smul, hu, map_smul]
  | lie _ _ _ _ hu hv => rw [σ₁.map_lie, hu, hv, σ₂.map_lie]

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
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : H.IsCartanSubalgebra := B.isCartanSubalgebra
  have _ : LieModule.IsTriangularizable K H L := B.isTriangularizable
  let b : (rootSystem H).Base := B.base
  let φ : ι ≃ ↥b.support := B.baseSupportEquiv
  let x : ↥b.support → L := B.e ∘ φ.symm
  let y : ↥b.support → L := B.f ∘ φ.symm
  have hx : ∀ j : ↥b.support, x j ∈ rootSpace H (⇑((j : H.root) : Weight K H L)) := by
    intro j
    obtain ⟨i, rfl⟩ := φ.surjective j
    have hij : ⇑((φ i : H.root) : Weight K H L) = ⇑(B.baseSupp i) := by
      rw [← B.coe_baseSupportEquiv_apply i, Weight.coe_coe]
    simpa [x, hij] using TauCeti.lieBasis_e_mem_rootSpace B i
  have hy : ∀ j : ↥b.support, y j ∈ rootSpace H (-⇑((j : H.root) : Weight K H L)) := by
    intro j
    obtain ⟨i, rfl⟩ := φ.surjective j
    have hij : ⇑((φ i : H.root) : Weight K H L) = ⇑(B.baseSupp i) := by
      rw [← B.coe_baseSupportEquiv_apply i, Weight.coe_coe]
    simpa [y, hij] using TauCeti.lieBasis_f_mem_rootSpace B i
  have hxy : ∀ j : ↥b.support, ⁅x j, y j⁆ = (((rootSystem H).coroot j : H) : L) := by
    intro j
    obtain ⟨i, rfl⟩ := φ.surjective j
    simp only [x, y, Function.comp_apply, Equiv.symm_apply_apply, (B.sl2 i).lie_e_f,
      rootSystem_coroot_apply]
    rw [show φ i = B.baseSupportEquiv i from rfl, LieAlgebra.Basis.coroot_eq_h']
    rfl
  obtain ⟨σ, hσ_inv, hσ_ne, hσx, hσy, hσH⟩ :=
    exists_chevalleyInvolution_of_base b x y hx hy hxy
  have hσe : ∀ i : ι, σ (B.e i) = -B.f i := fun i ↦ by
    simpa [x, y] using hσx (φ i)
  have hσf : ∀ i : ι, σ (B.f i) = -B.e i := fun i ↦ by
    simpa [x, y] using hσy (φ i)
  refine ⟨σ, ⟨hσe, hσf, hσ_inv, hσ_ne, hσH⟩, fun σ' ⟨hσ'e, hσ'f, _, _, _⟩ ↦ ?_⟩
  have hσ'x : ∀ j : ↥b.support, σ' (x j) = -y j := fun j ↦ hσ'e (φ.symm j)
  have hσ'y : ∀ j : ↥b.support, σ' (y j) = -x j := fun j ↦ hσ'f (φ.symm j)
  exact chevalleyInvolution_unique_of_base b x y hx hy hxy hσ'x hσ'y hσx hσy

end LieBasis

end Humphreys14_3
