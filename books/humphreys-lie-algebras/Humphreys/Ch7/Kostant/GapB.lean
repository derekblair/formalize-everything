import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Lie.Basis.Base
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.RingTheory.Binomial
import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Polynomial.Basis
import TauCeti.Algebra.Lie.Weights.Chevalley.System
import TauCeti.Algebra.Lie.Weights.Dimension
import TauCeti.Algebra.Lie.Weights.Root.IntegralBasis
import TauCeti.Algebra.Module.Rat
import TauCeti.RingTheory.DividedPowers.Associative
import TauCeti.RingTheory.Polynomial.Binomial.Basis

open LieAlgebra LieAlgebra.IsKilling LieModule Polynomial RootPairing TauCeti TauCeti.Associative

universe u v

namespace Humphreys26_4.GapB

section PolynomialBasis

variable (K : Type u) [Field K] [CharZero K]

private noncomputable def invFactorialUnitK (n : ℕ) : Kˣ :=
  Units.mk0 (n.factorial : K)⁻¹ <| inv_ne_zero <| by exact_mod_cast n.factorial_ne_zero

/-- `K`-polymorphic divided-power polynomial basis `X ^ n / n!` of `K[X]`. -/
noncomputable def dividedPowerPolynomialBasisK : Module.Basis ℕ K K[X] :=
  (Polynomial.basisMonomials K).unitsSMul (invFactorialUnitK K)

@[simp]
theorem dividedPowerPolynomialBasisK_apply (n : ℕ) :
    dividedPowerPolynomialBasisK K n = (n.factorial : K)⁻¹ • (X : K[X]) ^ n := by
  simp [dividedPowerPolynomialBasisK, invFactorialUnitK, Module.Basis.unitsSMul_apply,
    Polynomial.coe_basisMonomials, Units.smul_def,
    ← Polynomial.C_mul_X_pow_eq_monomial, Algebra.smul_def]

end PolynomialBasis

section GeneralCharZeroField

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

noncomputable local instance instAlgebraRatUEA :
    Algebra ℚ (_root_.UniversalEnvelopingAlgebra K L) :=
  Algebra.compHom (_root_.UniversalEnvelopingAlgebra K L) (algebraMap ℚ K)

attribute [local instance] TauCeti.moduleNNRat

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L] in
private theorem aeval_dividedPowerPolynomialBasisK
    (u : _root_.UniversalEnvelopingAlgebra K L) (n : ℕ) :
    aeval u (dividedPowerPolynomialBasisK K n) = dividedPower n u := by
  rw [dividedPowerPolynomialBasisK_apply, map_smul, map_pow, aeval_X, dividedPower_def]
  have hrat : (algebraMap ℚ K) ((n.factorial : ℚ)⁻¹) = (n.factorial : K)⁻¹ := by
    rw [map_inv₀, map_natCast]
  rw [Algebra.smul_def, ← hrat]
  rfl

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L] in
private theorem aeval_binomialPolynomialBasisK
    (u : _root_.UniversalEnvelopingAlgebra K L) (n : ℕ) :
    aeval u (TauCeti.binomialPolynomialBasis K n) = Ring.choose u n := by
  rw [TauCeti.binomialPolynomialBasis_apply]
  simpa only [aeval_X] using Ring.map_choose (aeval u) (X : K[X]) n

/-- Ambient `K`-basis of `L` formed by `(x α)_{α ∈ H.root} ⊕ (coroot i)_{i ∈ b.support}` (`NB-1`). -/
noncomputable def chevalleyAmbientBasis
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (b : (rootSystem H).Base) :
    Module.Basis (H.root ⊕ ↥b.support) K L := by
  let v : H.root ⊕ ↥b.support → L := fun s => (hx.rootSimpleCorootBasis b s : L)
  have hspan_int :
      Submodule.span ℤ (Set.range v) = hx.chevalleyLieLattice.toSubmodule := by
    have hmap := congrArg (Submodule.map hx.chevalleyLieLattice.toSubmodule.subtype)
      (hx.rootSimpleCorootBasis b).span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at hmap
    exact hmap
  have hspan_K : Submodule.span K (Set.range v) = ⊤ := by
    rw [← Submodule.span_span_of_tower ℤ K (Set.range v), hspan_int]
    exact hx.span_chevalleyLieLattice_eq_top
  have hli_K : LinearIndependent K v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan_K.ge
      (TauCeti.card_root_sum_support_eq_finrank H b)
  exact Module.Basis.mk hli_K hspan_K.ge

@[simp]
theorem chevalleyAmbientBasis_inl
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (b : (rootSystem H).Base) (α : H.root) :
    chevalleyAmbientBasis hx b (Sum.inl α) = x (α : Weight K H L) := by
  rw [chevalleyAmbientBasis, Module.Basis.mk_apply]
  exact hx.coe_rootSimpleCorootBasis_inl b α

@[simp]
theorem chevalleyAmbientBasis_inr
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (b : (rootSystem H).Base) (i : ↥b.support) :
    chevalleyAmbientBasis hx b (Sum.inr i) = (((rootSystem H).coroot i.1 : H) : L) := by
  rw [chevalleyAmbientBasis, Module.Basis.mk_apply, hx.coe_rootSimpleCorootBasis_inr b i,
    rootSystem_coroot_apply]

private theorem coe_indexNeg_weight (α : H.root) :
    ((letI := (rootSystem H).indexNeg; -α : H.root) : Weight K H L) = -(α : Weight K H L) := by
  let _ := (rootSystem H).indexNeg
  apply Weight.ext
  intro h
  have hroot : (rootSystem H).root (-α) = -(rootSystem H).root α := by
    simp only [indexNeg_neg, root_reflectionPerm, reflection_apply_self]
  have hpt := DFunLike.congr_fun hroot h
  rw [Weight.coe_neg, Pi.neg_apply]
  simpa only [rootSystem_root_apply, Weight.toLinear_apply, LinearMap.neg_apply] using hpt

/-- Equivalence indexing negative roots, simple coroots, and positive roots by `Fin (m + ℓ + m)`. -/
private noncomputable def orderedChevalleyIndexEquiv
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) :
    Fin (m + ℓ + m) ≃ H.root ⊕ ↥b.support := by
  classical
  letI := (rootSystem H).indexNeg
  let negEquivPos : {α : H.root // ¬ b.IsPos α} ≃ {α : H.root // b.IsPos α} :=
    { toFun := fun α => ⟨-α.1, (RootPairing.Base.IsPos.neg_iff_not b α.1).mpr α.2⟩
      invFun := fun α =>
        ⟨-α.1, (RootPairing.Base.IsPos.neg_iff_not b (-α.1)).mp (by simpa using α.2)⟩
      left_inv := fun α => Subtype.ext (neg_neg α.1)
      right_inv := fun α => Subtype.ext (neg_neg α.1) }
  let rootSplit : (Fin m ⊕ Fin m) ≃ H.root :=
    (Equiv.sumCongr (posOrd.trans negEquivPos.symm) posOrd).trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCompl b.IsPos))
  let threeSum : ((Fin m ⊕ Fin ℓ) ⊕ Fin m) ≃ H.root ⊕ ↥b.support :=
    (Equiv.sumAssoc (Fin m) (Fin ℓ) (Fin m)).trans
      ((Equiv.sumCongr (Equiv.refl (Fin m)) (Equiv.sumComm (Fin ℓ) (Fin m))).trans
        (((Equiv.sumAssoc (Fin m) (Fin m) (Fin ℓ)).symm).trans
          (Equiv.sumCongr rootSplit baseOrd)))
  exact finSumFinEquiv.symm.trans
    ((Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl (Fin m))).trans threeSum)

private theorem orderedChevalleyIndexEquiv_neg
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) (j : Fin m) :
    orderedChevalleyIndexEquiv b posOrd baseOrd (Fin.castAdd m (Fin.castAdd ℓ j)) =
      Sum.inl (letI := (rootSystem H).indexNeg; -(posOrd j).1) := by
  simp [orderedChevalleyIndexEquiv, finSumFinEquiv_symm_apply_castAdd]

private theorem orderedChevalleyIndexEquiv_cartan
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) (i : Fin ℓ) :
    orderedChevalleyIndexEquiv b posOrd baseOrd (Fin.castAdd m (Fin.natAdd m i)) =
      Sum.inr (baseOrd i) := by
  simp [orderedChevalleyIndexEquiv, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd]

private theorem orderedChevalleyIndexEquiv_pos
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) (j : Fin m) :
    orderedChevalleyIndexEquiv b posOrd baseOrd (Fin.natAdd (m + ℓ) j) =
      Sum.inl (posOrd j).1 := by
  simp [orderedChevalleyIndexEquiv, finSumFinEquiv_symm_apply_natAdd]

private noncomputable def orderedChevalleyBasis
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) :
    Module.Basis (Fin (m + ℓ + m)) K L :=
  (chevalleyAmbientBasis hx b).reindex (orderedChevalleyIndexEquiv b posOrd baseOrd).symm

private theorem orderedChevalleyBasis_neg
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) (j : Fin m) :
    orderedChevalleyBasis hx b posOrd baseOrd (Fin.castAdd m (Fin.castAdd ℓ j)) =
      x (-((posOrd j).1 : Weight K H L)) := by
  rw [orderedChevalleyBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    orderedChevalleyIndexEquiv_neg, chevalleyAmbientBasis_inl, coe_indexNeg_weight]

private theorem orderedChevalleyBasis_cartan
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) (i : Fin ℓ) :
    orderedChevalleyBasis hx b posOrd baseOrd (Fin.castAdd m (Fin.natAdd m i)) =
      (((rootSystem H).coroot (baseOrd i).1 : H) : L) := by
  rw [orderedChevalleyBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    orderedChevalleyIndexEquiv_cartan, chevalleyAmbientBasis_inr]

private theorem orderedChevalleyBasis_pos
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) (j : Fin m) :
    orderedChevalleyBasis hx b posOrd baseOrd (Fin.natAdd (m + ℓ) j) =
      x ((posOrd j).1 : Weight K H L) := by
  rw [orderedChevalleyBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    orderedChevalleyIndexEquiv_pos, chevalleyAmbientBasis_inl]

private noncomputable def mixedCoordBasis (K : Type u) [Field K] [CharZero K] (m ℓ : ℕ)
    (idx : Fin (m + ℓ + m)) : Module.Basis ℕ K K[X] :=
  if (idx : ℕ) < m then dividedPowerPolynomialBasisK K
  else if (idx : ℕ) < m + ℓ then TauCeti.binomialPolynomialBasis K
  else dividedPowerPolynomialBasisK K

private theorem mixedCoordBasis_neg (K : Type u) [Field K] [CharZero K] (m ℓ : ℕ) (j : Fin m) :
    mixedCoordBasis K m ℓ (Fin.castAdd m (Fin.castAdd ℓ j)) = dividedPowerPolynomialBasisK K := by
  simp [mixedCoordBasis, j.isLt]

private theorem mixedCoordBasis_cartan (K : Type u) [Field K] [CharZero K] (m ℓ : ℕ) (i : Fin ℓ) :
    mixedCoordBasis K m ℓ (Fin.castAdd m (Fin.natAdd m i)) =
      TauCeti.binomialPolynomialBasis K := by
  have h1 : ¬ (m + (i : ℕ) < m) := by omega
  have h2 : m + (i : ℕ) < m + ℓ := by omega
  simp [mixedCoordBasis, h1, h2]

private theorem mixedCoordBasis_pos (K : Type u) [Field K] [CharZero K] (m ℓ : ℕ) (j : Fin m) :
    mixedCoordBasis K m ℓ (Fin.natAdd (m + ℓ) j) = dividedPowerPolynomialBasisK K := by
  have h1 : ¬ (m + ℓ + (j : ℕ) < m) := by omega
  have h2 : ¬ (m + ℓ + (j : ℕ) < m + ℓ) := by omega
  simp [mixedCoordBasis, h1, h2]

private def tupleEquiv {m ℓ : ℕ} :
    ((Fin m → ℕ) × (Fin ℓ → ℕ) × (Fin m → ℕ)) ≃ (Fin (m + ℓ + m) → ℕ) where
  toFun p := Fin.append (Fin.append p.1 p.2.1) p.2.2
  invFun f :=
    (fun j => f (Fin.castAdd m (Fin.castAdd ℓ j)),
     fun i => f (Fin.castAdd m (Fin.natAdd m i)),
     fun j => f (Fin.natAdd (m + ℓ) j))
  left_inv p := by
    rcases p with ⟨A, B, C⟩
    ext j <;> simp
  right_inv f := by
    ext idx
    refine Fin.addCases (fun idx1 => Fin.addCases (fun j => ?_) (fun i => ?_) idx1)
      (fun j => ?_) idx
    · simp
    · simp [Fin.append_left]
    · simp [Fin.append_right]

private theorem tupleEquiv_neg {m ℓ : ℕ}
    (p : (Fin m → ℕ) × (Fin ℓ → ℕ) × (Fin m → ℕ)) (j : Fin m) :
    tupleEquiv p (Fin.castAdd m (Fin.castAdd ℓ j)) = p.1 j := by
  simp [tupleEquiv]

private theorem tupleEquiv_cartan {m ℓ : ℕ}
    (p : (Fin m → ℕ) × (Fin ℓ → ℕ) × (Fin m → ℕ)) (i : Fin ℓ) :
    tupleEquiv p (Fin.castAdd m (Fin.natAdd m i)) = p.2.1 i := by
  simp [tupleEquiv, Fin.append_left]

private theorem tupleEquiv_pos {m ℓ : ℕ}
    (p : (Fin m → ℕ) × (Fin ℓ → ℕ) × (Fin m → ℕ)) (j : Fin m) :
    tupleEquiv p (Fin.natAdd (m + ℓ) j) = p.2.2 j := by
  simp [tupleEquiv, Fin.append_right]

/-- Bundled `K`-basis of `UniversalEnvelopingAlgebra K L` indexed by `(A, B, C)` whose elements are
the ordered Kostant monomials `f_A h_B e_C`. -/
noncomputable def kostantMonomialBasisK
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) :
    Module.Basis ((Fin m → ℕ) × (Fin ℓ → ℕ) × (Fin m → ℕ)) K
      (_root_.UniversalEnvelopingAlgebra K L) :=
  ((orderedChevalleyBasis hx b posOrd baseOrd).pbwPolynomialBasis
    (mixedCoordBasis K m ℓ)).reindex tupleEquiv.symm

theorem kostantMonomialBasisK_apply
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support)
    (p : (Fin m → ℕ) × (Fin ℓ → ℕ) × (Fin m → ℕ)) :
    kostantMonomialBasisK hx b posOrd baseOrd p =
      (List.ofFn fun j : Fin m =>
        dividedPower (p.1 j)
          (_root_.UniversalEnvelopingAlgebra.ι K (x (-((posOrd j).1 : Weight K H L))))).prod *
        (List.ofFn fun i : Fin ℓ =>
          Ring.choose
            (_root_.UniversalEnvelopingAlgebra.ι K
              (((rootSystem H).coroot (baseOrd i).1 : H) : L))
            (p.2.1 i)).prod *
          (List.ofFn fun j : Fin m =>
            dividedPower (p.2.2 j)
              (_root_.UniversalEnvelopingAlgebra.ι K (x ((posOrd j).1 : Weight K H L)))).prod := by
  let f : Fin (m + ℓ + m) → _root_.UniversalEnvelopingAlgebra K L := fun idx =>
    aeval (_root_.UniversalEnvelopingAlgebra.ι K (orderedChevalleyBasis hx b posOrd baseOrd idx))
      (mixedCoordBasis K m ℓ idx (tupleEquiv p idx))
  have h1 : List.ofFn f =
      List.ofFn (fun idx1 : Fin (m + ℓ) => f (Fin.castAdd m idx1)) ++
        List.ofFn (fun j : Fin m => f (Fin.natAdd (m + ℓ) j)) :=
    List.ofFn_add
  have h2 : List.ofFn (fun idx1 : Fin (m + ℓ) => f (Fin.castAdd m idx1)) =
      List.ofFn (fun j : Fin m => f (Fin.castAdd m (Fin.castAdd ℓ j))) ++
        List.ofFn (fun i : Fin ℓ => f (Fin.castAdd m (Fin.natAdd m i))) :=
    List.ofFn_add
  rw [kostantMonomialBasisK, Module.Basis.reindex_apply, Equiv.symm_symm,
    Module.Basis.pbwPolynomialBasis_apply]
  change (List.ofFn f).prod = _
  rw [h1, List.prod_append, h2, List.prod_append]
  congr 1
  · congr 1
    · refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
      dsimp only [f]
      rw [orderedChevalleyBasis_neg, mixedCoordBasis_neg, tupleEquiv_neg,
        aeval_dividedPowerPolynomialBasisK]
    · refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
      dsimp only [f]
      rw [orderedChevalleyBasis_cartan, mixedCoordBasis_cartan, tupleEquiv_cartan,
        aeval_binomialPolynomialBasisK]
  · refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
    dsimp only [f]
    rw [orderedChevalleyBasis_pos, mixedCoordBasis_pos, tupleEquiv_pos,
      aeval_dividedPowerPolynomialBasisK]

end GeneralCharZeroField

end Humphreys26_4.GapB
