import Mathlib.Algebra.Lie.OfAssociative
import TauCeti.Algebra.Lie.Weights.Faithful
import TauCeti.Algebra.Lie.Weights.Root.CorootSpan
import TauCeti.Algebra.Lie.Weights.WeightLattice
import Humphreys.Ch7.AdmissibleLattice27_1

open LieAlgebra LieAlgebra.IsKilling LieModule RootPairing TauCeti TauCeti.Associative

universe u v w w'

namespace Humphreys27_2

section AdjointDividedPowerIdentity

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]

noncomputable local instance instAlgebraRatUEA :
    Algebra ℚ (_root_.UniversalEnvelopingAlgebra K L) :=
  Algebra.compHom (_root_.UniversalEnvelopingAlgebra K L) (algebraMap ℚ K)

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- **Humphreys §27.2, Lemma (p. 159, verbatim):**
For any `u ∈ 𝔘(L)`, `x ∈ L`, and `n ∈ ℕ` (`= ℤ⁺`),
`((ad x)^n / n!)(u) = ∑_{i = 0}^n (-1)^i (x^{n-i} / (n-i)!) u (x^i / i!)` in `𝔘(L)`. -/
theorem ad_dividedPower_apply_uea
    (x : L) (u : _root_.UniversalEnvelopingAlgebra K L) (n : ℕ) :
    (n.factorial : K)⁻¹ •
        ((LieAlgebra.ad K (_root_.UniversalEnvelopingAlgebra K L)
            (_root_.UniversalEnvelopingAlgebra.ι K x)) ^ n) u =
      ∑ i ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ i •
          (dividedPower (n - i) (_root_.UniversalEnvelopingAlgebra.ι K x) * u *
            dividedPower i (_root_.UniversalEnvelopingAlgebra.ι K x)) := by
  sorry

end AdjointDividedPowerIdentity

section StabilizerLattice

variable {K : Type u} {L : Type v}
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

noncomputable local instance instAlgebraRatUEA' :
    Algebra ℚ (_root_.UniversalEnvelopingAlgebra K L) :=
  Algebra.compHom (_root_.UniversalEnvelopingAlgebra K L) (algebraMap ℚ K)

attribute [local instance] TauCeti.moduleNNRat

/-- **Root lattice `Λ_r ⊂ H*` (H §13.1, §27.2 p. 159):** the `ℤ`-span of the roots of `(L, H)`
inside `Module.Dual K H`. -/
noncomputable def rootLattice (H : LieSubalgebra K L) [H.IsCartanSubalgebra] :
    Submodule ℤ (Module.Dual K H) :=
  Submodule.span ℤ
    (Set.range fun α : H.root => ((rootSystem H).root α : Module.Dual K H))

/-- **Module weight lattice `Λ(V) = ℤ Π(V) ⊂ H*` (`D27.2`, H p. 159):** the `ℤ`-span of the
weights `Weight K H V` of an `L`-module `V` inside `Module.Dual K H`. -/
noncomputable def moduleWeightLattice (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    (V : Type w) [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V] :
    Submodule ℤ (Module.Dual K H) :=
  Submodule.span ℤ (Set.range fun χ : Weight K H V => (χ : Module.Dual K H))

/-- **Humphreys Exercise 21.5, first assertion (p. 116) as invoked in §27.2 (p. 159):**
For any faithful finite-dimensional `L`-module `V`, `Λ_r ≤ Λ(V) ≤ Λ`. -/
theorem rootLattice_le_moduleWeightLattice_le_integralWeightLattice
    (V : Type w) [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K V] [LieModule.IsFaithful K L V] :
    rootLattice H ≤ moduleWeightLattice H V ∧
      moduleWeightLattice H V ≤ TauCeti.integralWeightLattice H := by
  sorry

/-- **Stabilizer `L_V` of an additive/integral submodule `M ⊂ V` in `L` (`D27.2`, H p. 159):**
`L_V(M) = {y ∈ L | y · M ⊆ M}` as a `ℤ`-submodule of `L`. -/
def stabilizerLattice (L : Type v) {V : Type w} [LieRing L] [AddCommGroup V]
    [LieRingModule L V] (M : Submodule ℤ V) : Submodule ℤ L where
  carrier := {y : L | ∀ m ∈ M, ⁅y, m⁆ ∈ M}
  zero_mem' m _ := by rw [zero_lie]; exact M.zero_mem
  add_mem' {y₁ y₂} hy₁ hy₂ m hm := by rw [add_lie]; exact M.add_mem (hy₁ m hm) (hy₂ m hm)
  smul_mem' z y hy m hm := by rw [zsmul_lie]; exact M.smul_mem z (hy m hm)

/-- **Cartan dual lattice `{h ∈ H | ∀ μ ∈ Λ(V), μ(h) ∈ ℤ}` (`D27.2`, H p. 159):**
defined intrinsically inside `H` from `Λ(V) = moduleWeightLattice H V` alone (with no reference
to `M`). -/
noncomputable def cartanWeightDualSubmodule (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    (V : Type w) [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V] :
    Submodule ℤ H :=
  ⨅ μ : moduleWeightLattice H V,
    (1 : Submodule ℤ K).comap ((μ.1 : Module.Dual K H).restrictScalars ℤ)

/-- **Humphreys §27.2 setup characterization of `H_V = H ∩ L_V` (p. 159):**
For any faithful finite-dimensional `L`-module `V` and any admissible lattice `M` in `V`,
`L_V(M) ∩ H` coincides with the image of `cartanWeightDualSubmodule H V` in `L`, and
`cartanWeightDualSubmodule H V` is a full `ℤ`-lattice in `H`. -/
theorem cartanStabilizer_eq_weightDual_and_isFullZLattice
    {V : Type w} [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K V] [LieModule.IsFaithful K L V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (M : Submodule ℤ V) (hM : Humphreys27_1.IsAdmissibleLattice H x M) :
    stabilizerLattice L M ⊓ H.toSubmodule.restrictScalars ℤ =
        (cartanWeightDualSubmodule H V).map (H.toSubmodule.restrictScalars ℤ).subtype ∧
      Humphreys27_1.IsFullZLattice K (cartanWeightDualSubmodule H V) := by
  sorry

/-- **Humphreys, Proposition 27.2 (p. 160, verbatim):**
For any faithful finite-dimensional `L`-module `V` and any admissible lattice `M` in `V`:
(1) `L_V = stabilizerLattice M` is closed under the Lie bracket of `L`;
(2) `L_V` is an admissible lattice in the adjoint `L`-module `L`;
(3) `L_V ∩ L_α = ℤ x_α` for every root `α ∈ Φ`; and
(4) `L_V = H_V ⊕ ⨁_{α ∈ Φ} ℤ x_α` where `H_V = L_V ∩ H`. -/
theorem isAdmissibleLattice_stabilizerLattice_and_decomposition
    {V : Type w} [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K V] [LieModule.IsFaithful K L V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (M : Submodule ℤ V) (hM : Humphreys27_1.IsAdmissibleLattice H x M) :
    (∀ y₁ ∈ stabilizerLattice L M, ∀ y₂ ∈ stabilizerLattice L M,
        ⁅y₁, y₂⁆ ∈ stabilizerLattice L M) ∧
      Humphreys27_1.IsAdmissibleLattice H x (stabilizerLattice L M) ∧
      (∀ α : H.root,
        stabilizerLattice L M ⊓ (rootSpace H (α : H → K)).toSubmodule.restrictScalars ℤ =
          Submodule.span ℤ {x (α : Weight K H L)}) ∧
      stabilizerLattice L M =
        (stabilizerLattice L M ⊓ H.toSubmodule.restrictScalars ℤ) ⊔
          (⨆ α : H.root, Submodule.span ℤ {x (α : Weight K H L)}) ∧
      Disjoint
        (stabilizerLattice L M ⊓ H.toSubmodule.restrictScalars ℤ)
        (⨆ α : H.root, Submodule.span ℤ {x (α : Weight K H L)}) ∧
      iSupIndep (fun α : H.root => Submodule.span ℤ {x (α : Weight K H L)}) := by
  sorry

/-- **Humphreys, Proposition 27.2 — Independence of `M` and dependence only on `Λ(V)` (p. 160):**
If two faithful finite-dimensional `L`-modules `V₁`, `V₂` have the same weight lattice
`Λ(V₁) = Λ(V₂)`, then for any admissible lattices `M₁ ⊂ V₁` and `M₂ ⊂ V₂`,
`stabilizerLattice M₁ = stabilizerLattice M₂` (in particular, for `V₁ = V₂ = V`, `L_V` does
not depend on the choice of admissible lattice `M`). -/
theorem stabilizerLattice_eq_of_moduleWeightLattice_eq
    {V₁ : Type w} [AddCommGroup V₁] [Module K V₁] [LieRingModule L V₁] [LieModule K L V₁]
    [FiniteDimensional K V₁] [LieModule.IsFaithful K L V₁]
    {V₂ : Type w'} [AddCommGroup V₂] [Module K V₂] [LieRingModule L V₂] [LieModule K L V₂]
    [FiniteDimensional K V₂] [LieModule.IsFaithful K L V₂]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (M₁ : Submodule ℤ V₁) (hM₁ : Humphreys27_1.IsAdmissibleLattice H x M₁)
    (M₂ : Submodule ℤ V₂) (hM₂ : Humphreys27_1.IsAdmissibleLattice H x M₂)
    (hΛ : moduleWeightLattice H V₁ = moduleWeightLattice H V₂) :
    stabilizerLattice L M₁ = stabilizerLattice L M₂ := by
  sorry

end StabilizerLattice

end Humphreys27_2
