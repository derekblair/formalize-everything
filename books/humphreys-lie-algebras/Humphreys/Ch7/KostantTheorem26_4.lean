import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Lie.Basis.Base
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.RingTheory.Binomial
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Adjoint.Basic
import TauCeti.Algebra.Lie.Weights.Chevalley.System
import TauCeti.Algebra.Module.Rat
import TauCeti.RingTheory.DividedPowers.Associative

open LieAlgebra LieAlgebra.IsKilling LieModule RootPairing TauCeti TauCeti.Associative

universe u v

namespace Humphreys26_4

section GeneralCharZeroField

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- Canonical `ℚ`-algebra structure on `UniversalEnvelopingAlgebra K L` induced by the unique
ring homomorphism `ℚ →+* K` (`DivisionRing.toRatAlgebra`), enabling `TauCeti.Associative.dividedPower`
and `Ring.choose` (via `TauCeti.moduleNNRat`) uniformly over any characteristic-zero field `K`
while agreeing definitionally with the standard instance when `K = ℚ`. -/
noncomputable local instance instAlgebraRatUEA :
    Algebra ℚ (_root_.UniversalEnvelopingAlgebra K L) :=
  Algebra.compHom (_root_.UniversalEnvelopingAlgebra K L) (algebraMap ℚ K)

attribute [local instance] TauCeti.moduleNNRat

/-- **Humphreys §26.4 (p. 156): The Kostant subring `𝔘(L)_ℤ`.**
Generated as a subring (with `1`) of `UniversalEnvelopingAlgebra K L` SOLELY by the root-vector
divided powers `x_α^t / t!` (`α ∈ Φ = H.root`, `t ∈ ℕ = ℤ⁺`). Cartan binomials are NOT included
among the defining generators. -/
noncomputable def kostantSubring (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    [LieModule.IsTriangularizable K H L] (x : Weight K H L → L) :
    Subring (_root_.UniversalEnvelopingAlgebra K L) :=
  Subring.closure
    (Set.range fun p : H.root × ℕ =>
      dividedPower p.2 (_root_.UniversalEnvelopingAlgebra.ι K (x (p.1 : Weight K H L))))

/-- Ordered negative-root divided-power product
`f_A = (x_{-α₁}^{a₁} / a₁!) ⋯ (x_{-αₘ}^{aₘ} / aₘ!)` on H p. 156. -/
noncomputable def kostantNegTerm {m : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α}) (x : Weight K H L → L)
    (A : Fin m → ℕ) : _root_.UniversalEnvelopingAlgebra K L :=
  (List.ofFn fun j : Fin m =>
    dividedPower (A j)
      (_root_.UniversalEnvelopingAlgebra.ι K (x (-((posOrd j).1 : Weight K H L))))).prod

/-- Ordered simple-coroot binomial product
`h_B = (h₁ choose b₁) ⋯ (h_ℓ choose b_ℓ)` on H p. 156, where `h_i = α_i∨` (`i ∈ Δ`). -/
noncomputable def kostantCartanTerm {ℓ : ℕ} (b : (rootSystem H).Base)
    (baseOrd : Fin ℓ ≃ ↥b.support)
    (B : Fin ℓ → ℕ) : _root_.UniversalEnvelopingAlgebra K L :=
  (List.ofFn fun i : Fin ℓ =>
    Ring.choose
      (_root_.UniversalEnvelopingAlgebra.ι K
        (((rootSystem H).coroot (baseOrd i).1 : H) : L))
      (B i)).prod

/-- Ordered positive-root divided-power product
`e_C = (x_{α₁}^{c₁} / c₁!) ⋯ (x_{αₘ}^{cₘ} / cₘ!)` on H p. 156. -/
noncomputable def kostantPosTerm {m : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α}) (x : Weight K H L → L)
    (C : Fin m → ℕ) : _root_.UniversalEnvelopingAlgebra K L :=
  (List.ofFn fun j : Fin m =>
    dividedPower (C j)
      (_root_.UniversalEnvelopingAlgebra.ι K (x ((posOrd j).1 : Weight K H L)))).prod

/-- Ordered Kostant monomial `f_A h_B e_C ∈ 𝔘(L)` on H p. 156. -/
noncomputable def kostantMonomial {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) (x : Weight K H L → L)
    (p : (Fin m → ℕ) × (Fin ℓ → ℕ) × (Fin m → ℕ)) :
    _root_.UniversalEnvelopingAlgebra K L :=
  kostantNegTerm b posOrd x p.1 *
    kostantCartanTerm b baseOrd p.2.1 *
      kostantPosTerm b posOrd x p.2.2

/-- **Humphreys §26.4 (p. 156): The Kostant lattice `𝔅`.**
The `ℤ`-submodule of `UniversalEnvelopingAlgebra K L` spanned by all `f_A h_B e_C`. -/
noncomputable def kostantLattice {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) (x : Weight K H L → L) :
    Submodule ℤ (_root_.UniversalEnvelopingAlgebra K L) :=
  Submodule.span ℤ (Set.range (kostantMonomial b posOrd baseOrd x))

/-- **Humphreys §26.4 (p. 156, setup paragraph): `K`-basis property of `{f_A h_B e_C}`.**
The ordered monomials `f_A h_B e_C` are `K`-linearly independent and span `𝔘_K(L)` over `K`
(in particular they are `ℤ`-linearly independent and form a `ℤ`-basis of `𝔅 = kostantLattice`). -/
theorem kostantMonomial_basis_over_field
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) :
    LinearIndependent K (kostantMonomial b posOrd baseOrd x) ∧
      Submodule.span K (Set.range (kostantMonomial b posOrd baseOrd x)) = ⊤ := by
  sorry

/-- **Humphreys §26.4, Theorem (Kostant) (p. 156, verbatim): `𝔅 = 𝔘(L)_ℤ`.**
For any Chevalley basis `(x_α, h_i)` of `(L, H)` and any ordering `(α₁, …, αₘ)` of `Φ⁺`, the
`ℤ`-lattice `𝔅` spanned by `f_A h_B e_C` equals the subring `𝔘(L)_ℤ` generated by all
`x_α^t / t!` (`α ∈ Φ`, `t ∈ ℕ`). -/
theorem kostantLattice_eq_kostantSubring
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) :
    (kostantLattice b posOrd baseOrd x : Set (_root_.UniversalEnvelopingAlgebra K L)) =
      (kostantSubring H x : Set (_root_.UniversalEnvelopingAlgebra K L)) := by
  sorry

/-- **Bundled `ℤ`-basis form of Kostant's Theorem (H §26.4, p. 156).**
Exhibits `(A, B, C) ↦ f_A h_B e_C` directly as a free `ℤ`-module basis of `𝔘(L)_ℤ`. -/
noncomputable def kostantSubringBasis
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) :
    Module.Basis ((Fin m → ℕ) × (Fin ℓ → ℕ) × (Fin m → ℕ)) ℤ (kostantSubring H x) := by
  sorry

@[simp]
theorem coe_kostantSubringBasis_apply
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support)
    (p : (Fin m → ℕ) × (Fin ℓ → ℕ) × (Fin m → ℕ)) :
    ((kostantSubringBasis hx b posOrd baseOrd p : kostantSubring H x) :
        _root_.UniversalEnvelopingAlgebra K L) =
      kostantMonomial b posOrd baseOrd x p := by
  sorry

end GeneralCharZeroField

section RatBridge

variable {L : Type v} [LieRing L] [LieAlgebra ℚ L]
  [FiniteDimensional ℚ L] [LieAlgebra.IsKilling ℚ L]
  {H : LieSubalgebra ℚ L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable ℚ H L]

/-- **Bridge to `TauCeti.chevalleyKostantForm` over `ℚ` (Corollary 26.2 / `C9` gate).**
Over `K = ℚ`, Humphreys's root-divided-powers-only subring `kostantSubring H x` coincides with
`TauCeti.chevalleyKostantForm x` (which explicitly includes all coroot binomials
`Ring.choose (ι ℚ (coroot α)) n` in its defining `Subring.closure`). -/
theorem kostantSubring_eq_chevalleyKostantForm_rat
    {ω : L ≃ₗ⁅ℚ⁆ L} {x : Weight ℚ H L → L} (hx : TauCeti.IsChevalleySystem ω x) :
    kostantSubring H x = TauCeti.chevalleyKostantForm x := by
  sorry

end RatBridge

end Humphreys26_4
