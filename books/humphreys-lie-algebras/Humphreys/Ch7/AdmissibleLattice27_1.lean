import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Algebra.MvPolynomial.Eval
import TauCeti.Algebra.Lie.HighestWeight.CompleteReducibility
import TauCeti.Algebra.Lie.HighestWeight.FiniteDimensional
import TauCeti.Algebra.Lie.HighestWeight.Irreducible
import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
import TauCeti.Algebra.Lie.Weights.Diagonalizable
import TauCeti.Algebra.Module.IntegralOrbit
import Humphreys.Ch7.ChevalleyBasis25_2
import Humphreys.Ch7.KostantTheorem26_4

open LieAlgebra LieAlgebra.IsKilling LieModule RootPairing TauCeti TauCeti.Associative

universe u v w

namespace Humphreys27_1

section PolynomialSeparation

/-- **Humphreys §27.1, Lemma (p. 158, verbatim): Integer-valued polynomial separation.**
Given `d ∈ ℤ^ℓ` and a finite subset `S ⊂ ℤ^ℓ` not containing `d`, there exists a multivariate
polynomial `f ∈ K[T₁, …, T_ℓ]` such that `f(ℤ^ℓ) ⊆ ℤ`, `f(d) = 1`, and `f(s) = 0` for all
`s ∈ S`. -/
theorem exists_intValued_mvPolynomial_sep (K : Type u) [Field K] [CharZero K]
    (ℓ : ℕ) (d : Fin ℓ → ℤ) (S : Finset (Fin ℓ → ℤ)) (hd : d ∉ S) :
    ∃ f : MvPolynomial (Fin ℓ) K,
      (∀ z : Fin ℓ → ℤ,
        MvPolynomial.eval (fun i => (z i : K)) f ∈ Set.range (Int.cast : ℤ → K)) ∧
        MvPolynomial.eval (fun i => (d i : K)) f = 1 ∧
          ∀ s ∈ S, MvPolynomial.eval (fun i => (s i : K)) f = 0 := by
  sorry

end PolynomialSeparation

section AdmissibleLattices

variable {K : Type u} {L : Type v} {V : Type w}
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- Canonical `ℚ`-algebra instance on `UniversalEnvelopingAlgebra K L`, matching
`Humphreys26_4.instAlgebraRatUEA` (`KostantTheorem26_4.lean` L30–32) definitionally. -/
noncomputable local instance instAlgebraRatUEA :
    Algebra ℚ (_root_.UniversalEnvelopingAlgebra K L) :=
  Algebra.compHom (_root_.UniversalEnvelopingAlgebra K L) (algebraMap ℚ K)

attribute [local instance] TauCeti.moduleNNRat

/-- **Humphreys §27.1 (`D27.1a`, p. 157): Negative triangular subring `𝔘_ℤ⁻`.**
Generated as a subring (with `1`) of `UniversalEnvelopingAlgebra K L` by all negative-root
divided powers `x_{-α}^t / t!` (`α ∈ Φ⁺`, `t ∈ ℕ = ℤ⁺`). -/
noncomputable def kostantNegSubring (b : (rootSystem H).Base) (x : Weight K H L → L) :
    Subring (_root_.UniversalEnvelopingAlgebra K L) :=
  Subring.closure
    (Set.range fun p : {α : H.root // b.IsPos α} × ℕ =>
      dividedPower p.2
        (_root_.UniversalEnvelopingAlgebra.ι K (x (-((p.1 : H.root) : Weight K H L)))))

/-- **Humphreys §27.1 (`D27.1a`, p. 157): Cartan subring `𝔘_ℤ⁰`.**
Generated as a subring (with `1`) of `UniversalEnvelopingAlgebra K L` by all simple-coroot
binomials `(h_i choose t)` (`α_i ∈ Δ`, `t ∈ ℕ = ℤ⁺`). -/
noncomputable def kostantCartanSubring (b : (rootSystem H).Base) :
    Subring (_root_.UniversalEnvelopingAlgebra K L) :=
  Subring.closure
    (Set.range fun p : ↥b.support × ℕ =>
      Ring.choose
        (_root_.UniversalEnvelopingAlgebra.ι K
          (((rootSystem H).coroot (p.1 : H.root) : H) : L))
        p.2)

/-- **Humphreys §27.1 (`D27.1a`, p. 157): Positive triangular subring `𝔘_ℤ⁺`.**
Generated as a subring (with `1`) of `UniversalEnvelopingAlgebra K L` by all positive-root
divided powers `x_α^t / t!` (`α ∈ Φ⁺`, `t ∈ ℕ = ℤ⁺`). -/
noncomputable def kostantPosSubring (b : (rootSystem H).Base) (x : Weight K H L → L) :
    Subring (_root_.UniversalEnvelopingAlgebra K L) :=
  Subring.closure
    (Set.range fun p : {α : H.root // b.IsPos α} × ℕ =>
      dividedPower p.2
        (_root_.UniversalEnvelopingAlgebra.ι K (x ((p.1 : H.root) : Weight K H L))))

/-- **Humphreys §27.1 (`D27.1a`, p. 157): `ℤ`-bases `{f_A}`, `{h_B}`, `{e_C}` of
`𝔘_ℤ⁻`, `𝔘_ℤ⁰`, `𝔘_ℤ⁺`.** -/
theorem kostantTriangularSubrings_eq_span
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) :
    (Submodule.span ℤ (Set.range (Humphreys26_4.kostantNegTerm b posOrd x)) :
        Set (_root_.UniversalEnvelopingAlgebra K L)) =
      (kostantNegSubring b x : Set (_root_.UniversalEnvelopingAlgebra K L)) ∧
    (Submodule.span ℤ (Set.range (Humphreys26_4.kostantCartanTerm b baseOrd)) :
        Set (_root_.UniversalEnvelopingAlgebra K L)) =
      (kostantCartanSubring b : Set (_root_.UniversalEnvelopingAlgebra K L)) ∧
    (Submodule.span ℤ (Set.range (Humphreys26_4.kostantPosTerm b posOrd x)) :
        Set (_root_.UniversalEnvelopingAlgebra K L)) =
      (kostantPosSubring b x : Set (_root_.UniversalEnvelopingAlgebra K L)) := by
  sorry

/-- **Humphreys §27.1 (`D27.1b`, pp. 157–158): Full `ℤ`-lattice in `V`.**
Defined verbatim as the `ℤ`-span of a `K`-basis of `V`. -/
def IsFullZLattice (K : Type u) {W : Type w} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (M : Submodule ℤ W) : Prop :=
  ∃ bW : Module.Basis (Fin (Module.finrank K W)) K W,
    M = Submodule.span ℤ (Set.range bW)

/-- **Humphreys §27.1 (pp. 157–158, preliminary characterization):**
Over a characteristic-zero field `K`, a `ℤ`-submodule `M` of a finite-dimensional `K`-space `W`
is the `ℤ`-span of a `K`-basis of `W` iff `M` is finitely generated over `ℤ`, spans `W` over
`K`, and satisfies `Module.finrank ℤ M ≤ Module.finrank K W`. -/
theorem isFullZLattice_iff_fg_and_span_eq_top_and_finrank_le
    {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (M : Submodule ℤ W) :
    IsFullZLattice K M ↔
      M.FG ∧ Submodule.span K (M : Set W) = ⊤ ∧
        Module.finrank ℤ M ≤ Module.finrank K W := by
  sorry

variable [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]

/-- Invariance of a subset/subgroup/submodule `M` of `V` under Humphreys's Kostant `ℤ`-form
`𝔘_ℤ = Humphreys26_4.kostantSubring H x`. -/
def IsKostantInvariant {S : Type*} [SetLike S V]
    (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
    (x : Weight K H L → L) (M : S) : Prop :=
  ∀ u ∈ Humphreys26_4.kostantSubring H x, ∀ v ∈ M,
    TauCeti.UniversalEnvelopingAlgebra.representation K L V u v ∈ M

/-- **Humphreys §27.1 (`D27.1b`, p. 159): Admissible lattice in `V`.**
A full `ℤ`-lattice `M` in a finite-dimensional `L`-module `V` invariant under
`𝔘_ℤ = Humphreys26_4.kostantSubring H x`. -/
def IsAdmissibleLattice (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    [LieModule.IsTriangularizable K H L] (x : Weight K H L → L)
    [FiniteDimensional K V] (M : Submodule ℤ V) : Prop :=
  IsFullZLattice K M ∧ IsKostantInvariant H x M

/-- **Humphreys §27.1 (pp. 158, 161): Minimal admissible lattice `M_min = 𝔘_ℤ · v⁺`.** -/
noncomputable def minAdmissibleLattice (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    [LieModule.IsTriangularizable K H L] (x : Weight K H L → L) (v : V) :
    Submodule ℤ V :=
  Subring.orbitOfRep (Humphreys26_4.kostantSubring H x)
    (TauCeti.UniversalEnvelopingAlgebra.representation K L V) {v}

open scoped Classical in
/-- **Humphreys, Theorem 27.1(a) (p. 158, verbatim):**
Let `V` be a finite-dimensional `L`-module. Any additive subgroup `M` of `V` invariant under
`𝔘_ℤ = Humphreys26_4.kostantSubring H x` is the direct sum of its intersections with the
weight spaces of `V` (`M = ⨁_{χ ∈ Π(V)} (M ∩ V_χ)`). -/
theorem weightSpace_inter_directSum_of_isKostantInvariant
    [FiniteDimensional K V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (M : AddSubgroup V) (hM : IsKostantInvariant H x M) :
    (⨆ χ : Weight K H V,
        M ⊓ (LieModule.weightSpace V (χ : H → K)).toSubmodule.toAddSubgroup) = M ∧
      iSupIndep (fun χ : Weight K H V =>
        M ⊓ (LieModule.weightSpace V (χ : H → K)).toSubmodule.toAddSubgroup) ∧
      DirectSum.IsInternal (fun χ : Weight K H V =>
        ((LieModule.weightSpace V (χ : H → K)).toSubmodule.restrictScalars ℤ).comap
          (AddMonoidHom.toIntLinearMap M.subtype)) := by
  sorry

/-- **Humphreys, Theorem 27.1(b) — Irreducible highest-weight construction (pp. 158–159, 161):**
For any finite-dimensional irreducible `L`-module `V` with highest-weight vector `v` of weight
`lam` relative to base `b`, `M_min := 𝔘_ℤ · v` equals `𝔘_ℤ⁻ · v`, is an admissible lattice in
`V`, and intersects the highest weight space `V_lam` in `ℤ · v`. -/
theorem isAdmissibleLattice_minAdmissibleLattice
    [FiniteDimensional K V] [LieModule.IsIrreducible K L V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (b : (rootSystem H).Base) {lam : Module.Dual K H} {v : V}
    (hv : TauCeti.IsHighestWeightVector b lam v) :
    minAdmissibleLattice H x v =
        Subring.orbitOfRep (kostantNegSubring b x)
          (TauCeti.UniversalEnvelopingAlgebra.representation K L V) {v} ∧
      IsAdmissibleLattice H x (minAdmissibleLattice H x v) ∧
      minAdmissibleLattice H x v ⊓
          (LieModule.weightSpace V (lam : H → K)).toSubmodule.restrictScalars ℤ =
        Submodule.span ℤ {v} := by
  sorry

/-- **Named-carrier specialization at `V = V(λ)` (`TauCeti.irreducibleQuotient b lam`):**
For any dominant integral weight `lam`, `M_min` on `irreducibleQuotient b lam` generated by
`irreducibleQuotientGenerator b lam` equals `𝔘_ℤ⁻ · v⁺`, is an admissible lattice, and
intersects `V(λ)_λ` in `ℤ · v⁺`. -/
theorem isAdmissibleLattice_minAdmissibleLattice_irreducibleQuotient
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (b : (rootSystem H).Base) {lam : Module.Dual K H}
    (hlam : TauCeti.IsDominantIntegral b lam) :
    letI : FiniteDimensional K (TauCeti.irreducibleQuotient b lam) :=
      TauCeti.finiteDimensional_irreducibleQuotient_of_isDominantIntegral hlam
    let v := TauCeti.irreducibleQuotientGenerator b lam
    minAdmissibleLattice H x v =
        Subring.orbitOfRep (kostantNegSubring b x)
          (TauCeti.UniversalEnvelopingAlgebra.representation K L
            (TauCeti.irreducibleQuotient b lam)) {v} ∧
      IsAdmissibleLattice H x (minAdmissibleLattice H x v) ∧
      minAdmissibleLattice H x v ⊓
          (LieModule.weightSpace (TauCeti.irreducibleQuotient b lam)
            (lam : H → K)).toSubmodule.restrictScalars ℤ =
        Submodule.span ℤ {v} := by
  sorry

/-- **Humphreys, Theorem 27.1(b) (p. 158, verbatim): Existence of an admissible lattice.**
Every finite-dimensional `L`-module `V` contains an admissible lattice invariant under
`𝔘_ℤ = Humphreys26_4.kostantSubring H x`. -/
theorem exists_isAdmissibleLattice
    [FiniteDimensional K V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x) :
    ∃ M : Submodule ℤ V, IsAdmissibleLattice H x M := by
  sorry

/-- **Unconditional Chevalley-free corollary of Theorem 27.1(b) (combining 25.2 + 26.4 + 27.1):**
For any finite-dimensional split Killing Lie algebra `(L, H)` over a characteristic-zero field
`K` and any finite-dimensional `L`-module `V`, there exist a Chevalley system `(ω, x)` of
`(L, H)` and an admissible lattice `M` in `V` invariant under `Humphreys26_4.kostantSubring H x`. -/
theorem exists_chevalleySystem_and_admissibleLattice [FiniteDimensional K V] :
    ∃ (ω : L ≃ₗ⁅K⁆ L) (x : Weight K H L → L),
      TauCeti.IsChevalleySystem ω x ∧
        ∃ M : Submodule ℤ V, IsAdmissibleLattice H x M := by
  sorry

end AdmissibleLattices

end Humphreys27_1
