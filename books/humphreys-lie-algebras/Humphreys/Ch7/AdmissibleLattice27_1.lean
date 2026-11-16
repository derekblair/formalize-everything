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
  let _ : Algebra ℚ (MvPolynomial (Fin ℓ) K) :=
    Algebra.compHom (MvPolynomial (Fin ℓ) K) (algebraMap ℚ K)
  let _ : Module ℚ≥0 (MvPolynomial (Fin ℓ) K) := TauCeti.moduleNNRat
  let _ : Module ℚ≥0 K := TauCeti.moduleNNRat
  let k : ℕ := S.sup fun s => Finset.univ.sup fun i => (s i - d i).natAbs
  let f : MvPolynomial (Fin ℓ) K :=
    ∏ i : Fin ℓ,
      Ring.choose (MvPolynomial.X i - MvPolynomial.C (d i : K) + MvPolynomial.C (k : K)) k *
        Ring.choose (-MvPolynomial.X i + MvPolynomial.C (d i : K) + MvPolynomial.C (k : K)) k
  have heval : ∀ z : Fin ℓ → ℤ,
      MvPolynomial.eval (fun i => (z i : K)) f =
        ((∏ i : Fin ℓ,
          Ring.choose (z i - d i + (k : ℤ)) k *
            Ring.choose (-z i + d i + (k : ℤ)) k : ℤ) : K) := by
    intro z
    simp only [f, map_prod, map_mul, Ring.map_choose, MvPolynomial.eval_add,
      MvPolynomial.eval_sub, MvPolynomial.eval_neg, MvPolynomial.eval_X, MvPolynomial.eval_C]
    rw [Int.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h1 : (z i : K) - (d i : K) + (k : K) = ((z i - d i + (k : ℤ) : ℤ) : K) := by push_cast; rfl
    have h2 : -(z i : K) + (d i : K) + (k : K) = ((-z i + d i + (k : ℤ) : ℤ) : K) := by push_cast; rfl
    rw [h1, h2, TauCeti.Ring.choose_intCast, TauCeti.Ring.choose_intCast, Int.cast_mul]
  refine ⟨f, fun z => ⟨_, (heval z).symm⟩, ?_, ?_⟩
  · rw [heval]
    have hprod : (∏ i : Fin ℓ,
        Ring.choose (d i - d i + (k : ℤ)) k *
          Ring.choose (-d i + d i + (k : ℤ)) k : ℤ) = 1 := by
      refine Finset.prod_eq_one fun i _ => ?_
      have hk1 : d i - d i + (k : ℤ) = (k : ℕ) := by omega
      have hk2 : -d i + d i + (k : ℤ) = (k : ℕ) := by omega
      rw [hk1, hk2, Ring.choose_natCast, Nat.choose_self, Nat.cast_one, mul_one]
    rw [hprod, Int.cast_one]
  · intro s hs
    rw [heval]
    have hsne : s ≠ d := fun hsd => hd (hsd ▸ hs)
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hsne
    have hle_k : (s i₀ - d i₀).natAbs ≤ k := by
      exact le_trans (Finset.le_sup (f := fun i => (s i - d i).natAbs) (Finset.mem_univ i₀))
        (Finset.le_sup (f := fun s' => Finset.univ.sup fun i => (s' i - d i).natAbs) hs)
    have hzero_i₀ :
        (Ring.choose (s i₀ - d i₀ + (k : ℤ)) k *
          Ring.choose (-s i₀ + d i₀ + (k : ℤ)) k : ℤ) = 0 := by
      rcases lt_trichotomy (s i₀ - d i₀) 0 with hlt | heq | hgt
      · let n : ℕ := (s i₀ - d i₀ + (k : ℤ)).toNat
        have hn_eq : (n : ℤ) = s i₀ - d i₀ + (k : ℤ) := Int.toNat_of_nonneg (by omega)
        have hn_lt : n < k := by omega
        rw [← hn_eq, Ring.choose_natCast, Nat.choose_eq_zero_of_lt hn_lt, Nat.cast_zero, zero_mul]
      · exact absurd (sub_eq_zero.mp heq) hi₀
      · let n : ℕ := (-s i₀ + d i₀ + (k : ℤ)).toNat
        have hn_eq : (n : ℤ) = -s i₀ + d i₀ + (k : ℤ) := Int.toNat_of_nonneg (by omega)
        have hn_lt : n < k := by omega
        rw [← hn_eq, Ring.choose_natCast, Nat.choose_eq_zero_of_lt hn_lt, Nat.cast_zero, mul_zero]
    rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hzero_i₀, Int.cast_zero]

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
  let _ : LieRing (_root_.UniversalEnvelopingAlgebra K L) := LieRing.ofAssociativeRing
  let _ : LieAlgebra K (_root_.UniversalEnvelopingAlgebra K L) := LieAlgebra.ofAssociativeAlgebra
  let bM := Humphreys26_4.GapB.kostantMonomialBasisK hx b posOrd baseOrd
  let bZ := Humphreys26_4.kostantSubringBasis hx b posOrd baseOrd
  have hbM_eq : ∀ p, bM p = Humphreys26_4.kostantMonomial b posOrd baseOrd x p :=
    Humphreys26_4.GapB.kostantMonomialBasisK_apply hx b posOrd baseOrd
  have hbZ_sum : ∀ (u : _root_.UniversalEnvelopingAlgebra K L)
      (hu : u ∈ Humphreys26_4.kostantSubring H x),
      u = ∑ q ∈ (bZ.repr ⟨u, hu⟩).support,
        (bZ.repr ⟨u, hu⟩ q) • Humphreys26_4.kostantMonomial b posOrd baseOrd x q := by
    intro u hu
    have hlin := congrArg (Humphreys26_4.kostantSubring H x).subtype (bZ.linearCombination_repr ⟨u, hu⟩)
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum] at hlin
    exact hlin.symm.trans (Finset.sum_congr rfl fun q _ => by
      rw [map_zsmul, Subring.coe_subtype, Humphreys26_4.coe_kostantSubringBasis_apply])
  have hbZ_repr : ∀ (u : _root_.UniversalEnvelopingAlgebra K L)
      (hu : u ∈ Humphreys26_4.kostantSubring H x) (p),
      bM.repr u p = ((bZ.repr ⟨u, hu⟩ p : ℤ) : K) := by
    intro u hu p
    have hu_eq : u = ∑ q ∈ (bZ.repr ⟨u, hu⟩).support, ((bZ.repr ⟨u, hu⟩ q : ℤ) : K) • bM q := by
      refine (hbZ_sum u hu).trans ?_
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hbM_eq, Int.cast_smul_eq_zsmul]
    conv_lhs => rw [hu_eq]
    classical
    rw [map_sum, Finsupp.finsetSum_apply]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.single_apply, Finset.sum_ite_eq']
    by_cases h0 : p ∈ (bZ.repr ⟨u, hu⟩).support
    · rw [ite_eq_left_iff.mpr (fun h => absurd h0 h)]
    · rw [ite_eq_right_iff.mpr (fun h => absurd h h0),
        Finsupp.notMem_support_iff.mp h0, Int.cast_zero]
  have haeval_dp : ∀ {S : LieSubalgebra K L} (w : S) (n : ℕ),
      (_root_.UniversalEnvelopingAlgebra.lift K
          ((_root_.UniversalEnvelopingAlgebra.ι K).comp S.incl))
        (Polynomial.aeval (_root_.UniversalEnvelopingAlgebra.ι K w)
          (Humphreys26_4.GapB.dividedPowerPolynomialBasisK K n)) =
      dividedPower n (_root_.UniversalEnvelopingAlgebra.ι K (w : L)) := by
    intro S w n
    rw [Humphreys26_4.GapB.dividedPowerPolynomialBasisK_apply, map_smul, map_pow,
      Polynomial.aeval_X, map_smul, map_pow, _root_.UniversalEnvelopingAlgebra.lift_ι_apply,
      LieHom.comp_apply, LieSubalgebra.coe_incl, dividedPower_def]
    have hrat : (algebraMap ℚ K) ((n.factorial : ℚ)⁻¹) = (n.factorial : K)⁻¹ := by
      rw [map_inv₀, map_natCast]
    rw [Algebra.smul_def, ← hrat]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · -- (1) Negative triangular subring `𝔘_ℤ⁻`
    apply Set.Subset.antisymm
    · intro u hu
      refine Submodule.span_induction ?_ (kostantNegSubring b x).zero_mem
        (fun _ _ _ _ => (kostantNegSubring b x).add_mem) (fun z _ _ h => zsmul_mem h z) hu
      rintro _ ⟨A, rfl⟩
      refine Subring.list_prod_mem _ fun y hy => ?_
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
      exact Subring.subset_closure ⟨(posOrd j, A j), rfl⟩
    · let Nneg := TauCeti.negativeNilradical H b
      have hmem_neg : ∀ j : Fin m,
          x (-((posOrd j).1 : Weight K H L)) ∈
            rootSpace H (((-(posOrd j).1 : H.root) : Weight K H L) : H → K) := by
        intro j
        rw [IsKilling.val_neg_root]
        exact hx.toIsSl2System.mem_rootSpace _
      let vNeg : Fin m → Nneg := fun j =>
        ⟨x (-((posOrd j).1 : Weight K H L)),
          TauCeti.mem_negativeNilradical_of_mem_rootSpace H b
            (TauCeti.neg_mem_negRoots_of_mem_posRoots b (posOrd j).2)
            (hmem_neg j)⟩
      have hli_neg : LinearIndependent K vNeg := by
        refine LinearIndependent.of_comp Nneg.toSubmodule.subtype ?_
        have hcomp : (Nneg.toSubmodule.subtype ∘ vNeg) =
            (Humphreys26_4.GapB.chevalleyAmbientBasis hx b) ∘
              (fun j : Fin m => Sum.inl (-(posOrd j).1)) := by
          funext j
          simp [vNeg, Humphreys26_4.GapB.chevalleyAmbientBasis_inl, IsKilling.val_neg_root]
        rw [hcomp]
        exact (Humphreys26_4.GapB.chevalleyAmbientBasis hx b).linearIndependent.comp _
          (Sum.inl_injective.comp (neg_injective.comp
            (Subtype.val_injective.comp posOrd.injective)))
      have hspan_neg : ⊤ ≤ Submodule.span K (Set.range vNeg) := by
        rintro ⟨y, hy⟩ -
        have hy' := hy
        rw [TauCeti.mem_negativeNilradical, TauCeti.rootSpaceSpan_eq_iSup,
          ← LieSubmodule.mem_toSubmodule, LieSubmodule.iSup_toSubmodule] at hy'
        have hle : (⨆ α : TauCeti.negRoots (rootSystem H) b,
            (rootSpace H ((α : H.root) : H → K)).toSubmodule) ≤
            (Submodule.span K (Set.range vNeg)).map Nneg.toSubmodule.subtype := by
          rw [Submodule.map_span, ← Set.range_comp]
          refine iSup_le fun α => ?_
          intro z hz
          have hpos : -α.1 ∈ TauCeti.posRoots (rootSystem H) b :=
            TauCeti.neg_mem_posRoots_of_mem_negRoots b α.2
          let j : Fin m := posOrd.symm ⟨-α.1, hpos⟩
          have hj_root : -(posOrd j).1 = α.1 := by simp [j]
          have hone : Module.finrank K (rootSpace H ((α.1 : Weight K H L) : H → K)) = 1 :=
            IsKilling.finrank_rootSpace_eq_one (α.1 : Weight K H L) (H.isNonZero_coe_root α.1)
          have hmem_x : x (α.1 : Weight K H L) ∈ rootSpace H ((α.1 : Weight K H L) : H → K) :=
            hx.toIsSl2System.mem_rootSpace _
          have hne_x : (⟨x (α.1 : Weight K H L), hmem_x⟩ :
              rootSpace H ((α.1 : Weight K H L) : H → K)) ≠ 0 := by
            intro h0
            exact hx.toIsSl2System.ne_zero (α.1 : Weight K H L) (H.isNonZero_coe_root α.1)
              (congrArg Subtype.val h0)
          obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' _ hne_x).mp hone ⟨z, hz⟩
          have hvj : (Nneg.toSubmodule.subtype ∘ vNeg) j = x (α.1 : Weight K H L) := by
            dsimp [vNeg]
            have hj_wt : -((posOrd j).1 : Weight K H L) = (α.1 : Weight K H L) := by
              rw [← hj_root, IsKilling.val_neg_root]
            rw [hj_wt]
          have hz_eq : z = c • (Nneg.toSubmodule.subtype ∘ vNeg) j := by
            rw [hvj]
            exact (congrArg Subtype.val hc).symm
          rw [hz_eq]
          exact Submodule.smul_mem _ c (Submodule.subset_span ⟨j, rfl⟩)
        obtain ⟨w, hw, hwy⟩ := hle hy'
        obtain rfl : w = ⟨y, hy⟩ := Subtype.ext hwy
        exact hw
      let bNeg : Module.Basis (Fin m) K Nneg := Module.Basis.mk hli_neg hspan_neg
      let φNeg : _root_.UniversalEnvelopingAlgebra K Nneg →ₐ[K]
          _root_.UniversalEnvelopingAlgebra K L :=
        _root_.UniversalEnvelopingAlgebra.lift K
          ((_root_.UniversalEnvelopingAlgebra.ι K).comp Nneg.incl)
      let bPBW := bNeg.pbwPolynomialBasis
        (fun _ => Humphreys26_4.GapB.dividedPowerPolynomialBasisK K)
      have hφ_bPBW : ∀ A : Fin m → ℕ,
          φNeg (bPBW A) = Humphreys26_4.kostantNegTerm b posOrd x A := by
        intro A
        dsimp only [bPBW]
        rw [Module.Basis.pbwPolynomialBasis_apply, map_list_prod, List.map_ofFn]
        refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
        dsimp only [Function.comp_def]
        rw [haeval_dp]
        simp [bNeg, vNeg]
      have hrange_le : (φNeg.range : Set (_root_.UniversalEnvelopingAlgebra K L)) ⊆
          (Submodule.span K (Set.range (Humphreys26_4.kostantNegTerm b posOrd x)) :
            Set (_root_.UniversalEnvelopingAlgebra K L)) := by
        rintro _ ⟨w, rfl⟩
        have hw : w ∈ Submodule.span K (Set.range bPBW) := bPBW.span_eq ▸ Submodule.mem_top
        have hmap : φNeg.toLinearMap w ∈
            Submodule.map φNeg.toLinearMap (Submodule.span K (Set.range bPBW)) := ⟨w, hw, rfl⟩
        rw [Submodule.map_span, ← Set.range_comp] at hmap
        have hfun : (φNeg.toLinearMap ∘ bPBW) = Humphreys26_4.kostantNegTerm b posOrd x :=
          funext hφ_bPBW
        rwa [hfun] at hmap
      have hsub_range : (kostantNegSubring b x : Set (_root_.UniversalEnvelopingAlgebra K L)) ⊆
          (φNeg.range : Set (_root_.UniversalEnvelopingAlgebra K L)) := by
        change kostantNegSubring b x ≤ φNeg.range.toSubring
        rw [kostantNegSubring, Subring.closure_le]
        rintro _ ⟨⟨α, t⟩, rfl⟩
        let j := posOrd.symm α
        have hj : posOrd j = α := posOrd.apply_symm_apply α
        have hmem_alg : dividedPower t (_root_.UniversalEnvelopingAlgebra.ι K
            (x (-((α.1 : H.root) : Weight K H L)))) ∈ φNeg.range := by
          refine ⟨(t.factorial : K)⁻¹ • (_root_.UniversalEnvelopingAlgebra.ι K (vNeg j)) ^ t, ?_⟩
          show φNeg ((t.factorial : K)⁻¹ • (_root_.UniversalEnvelopingAlgebra.ι K (vNeg j)) ^ t) = _
          dsimp only [φNeg]
          rw [map_smul, map_pow, _root_.UniversalEnvelopingAlgebra.lift_ι_apply,
            LieHom.comp_apply, LieSubalgebra.coe_incl, dividedPower_def]
          have hrat : (algebraMap ℚ K) ((t.factorial : ℚ)⁻¹) = (t.factorial : K)⁻¹ := by
            rw [map_inv₀, map_natCast]
          simp only [vNeg, hj, Algebra.smul_def, ← hrat]
          rfl
        exact hmem_alg
      have hsub_kostant : kostantNegSubring b x ≤ Humphreys26_4.kostantSubring H x := by
        rw [kostantNegSubring, Subring.closure_le]
        rintro _ ⟨⟨α, t⟩, rfl⟩
        exact Humphreys26_4.GapA.dividedPower_weight_mem_rootSubring hx _ t
      have hterm_eq : ∀ A : Fin m → ℕ,
          Humphreys26_4.kostantNegTerm b posOrd x A = bM (A, 0, 0) := by
        intro A
        rw [hbM_eq, Humphreys26_4.kostantMonomial]
        have hC0 : Humphreys26_4.kostantCartanTerm b baseOrd 0 = 1 := by
          simp [Humphreys26_4.kostantCartanTerm, List.ofFn_const]
        have hP0 : Humphreys26_4.kostantPosTerm b posOrd x 0 = 1 := by
          simp [Humphreys26_4.kostantPosTerm, List.ofFn_const]
        rw [hC0, hP0, mul_one, mul_one]
      intro u hu
      have huK : u ∈ Submodule.span K (Set.range (Humphreys26_4.kostantNegTerm b posOrd x)) :=
        hrange_le (hsub_range hu)
      have hrepr_zero : ∀ p, (p.2.1 ≠ 0 ∨ p.2.2 ≠ 0) → bM.repr u p = 0 := by
        refine Submodule.span_induction ?_ ?_ ?_ ?_ huK
        · rintro _ ⟨A, rfl⟩ p hp
          rw [hterm_eq A, Module.Basis.repr_self, Finsupp.single_apply]
          split_ifs with heq
          · rcases hp with h1 | h2
            · exact absurd (congrArg (fun q => q.2.1) heq).symm h1
            · exact absurd (congrArg (fun q => q.2.2) heq).symm h2
          · rfl
        · intro p _; simp
        · intro a₁ a₂ _ _ h₁ h₂ p hp; rw [map_add, Finsupp.add_apply, h₁ p hp, h₂ p hp, add_zero]
        · intro c a₁ _ h₁ p hp; rw [map_smul, Finsupp.smul_apply, h₁ p hp, smul_zero]
      have huZ : u ∈ Humphreys26_4.kostantSubring H x := hsub_kostant hu
      change u ∈ (Submodule.span ℤ (Set.range (Humphreys26_4.kostantNegTerm b posOrd x)) : Set _)
      rw [hbZ_sum u huZ]
      refine (Submodule.span ℤ (Set.range (Humphreys26_4.kostantNegTerm b posOrd x))).sum_mem
        fun p hp => ?_
      have hp_nz : bZ.repr ⟨u, huZ⟩ p ≠ 0 := Finsupp.mem_support_iff.mp hp
      have hp21 : p.2.1 = 0 := by
        by_contra hne
        exact hp_nz (Int.cast_eq_zero.mp ((hbZ_repr u huZ p).symm.trans (hrepr_zero p (Or.inl hne))))
      have hp22 : p.2.2 = 0 := by
        by_contra hne
        exact hp_nz (Int.cast_eq_zero.mp ((hbZ_repr u huZ p).symm.trans (hrepr_zero p (Or.inr hne))))
      have hp_eq : p = (p.1, 0, 0) := by
        rcases p with ⟨A, B, C⟩
        dsimp at hp21 hp22
        rw [hp21, hp22]
      rw [hp_eq, ← hbM_eq, ← hterm_eq p.1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p.1, rfl⟩)
  · -- (2) Cartan subring `𝔘_ℤ⁰`
    let fC : Fin ℓ → _root_.UniversalEnvelopingAlgebra K L := fun i =>
      _root_.UniversalEnvelopingAlgebra.ι K (((rootSystem H).coroot (baseOrd i).1 : H) : L)
    have hcomm : ∀ i j : Fin ℓ, Commute (fC i) (fC j) := by
      intro i j
      refine TauCeti.UniversalEnvelopingAlgebra.commute_of_lie_eq_zero
        (RingHom.id (_root_.UniversalEnvelopingAlgebra K L)) ?_
      rw [rootSystem_coroot_apply, rootSystem_coroot_apply]
      exact TauCeti.lie_coroot_coroot_eq_zero _ _
    have hrange_gen :
        (Set.range fun p : ↥b.support × ℕ =>
          Ring.choose
            (_root_.UniversalEnvelopingAlgebra.ι K
              (((rootSystem H).coroot (p.1 : H.root) : H) : L)) p.2) =
        (Set.range fun p : Fin ℓ × ℕ => Ring.choose (fC p.1) p.2) := by
      ext y
      constructor
      · rintro ⟨⟨s, n⟩, rfl⟩
        exact ⟨(baseOrd.symm s, n), by simp [fC]⟩
      · rintro ⟨⟨i, n⟩, rfl⟩
        exact ⟨(baseOrd i, n), rfl⟩
    ext u
    change u ∈ Submodule.span ℤ (Set.range (Humphreys26_4.kostantCartanTerm b baseOrd)) ↔
      u ∈ kostantCartanSubring b
    rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure,
      kostantCartanSubring, hrange_gen]
    exact (TauCeti.mem_subringClosure_range_ringChoose_iff_mem_closure_range_prod_ofFn
      fC hcomm).symm
  · -- (3) Positive triangular subring `𝔘_ℤ⁺`
    apply Set.Subset.antisymm
    · intro u hu
      refine Submodule.span_induction ?_ (kostantPosSubring b x).zero_mem
        (fun _ _ _ _ => (kostantPosSubring b x).add_mem) (fun z _ _ h => zsmul_mem h z) hu
      rintro _ ⟨C, rfl⟩
      refine Subring.list_prod_mem _ fun y hy => ?_
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
      exact Subring.subset_closure ⟨(posOrd j, C j), rfl⟩
    · let Npos := TauCeti.positiveNilradical H b
      let vPos : Fin m → Npos := fun j =>
        ⟨x ((posOrd j).1 : Weight K H L),
          TauCeti.mem_positiveNilradical_of_mem_rootSpace H b (posOrd j).2
            (hx.toIsSl2System.mem_rootSpace _)⟩
      have hli_pos : LinearIndependent K vPos := by
        refine LinearIndependent.of_comp Npos.toSubmodule.subtype ?_
        have hcomp : (Npos.toSubmodule.subtype ∘ vPos) =
            (Humphreys26_4.GapB.chevalleyAmbientBasis hx b) ∘
              (fun j : Fin m => Sum.inl (posOrd j).1) := by
          funext j
          simp [vPos, Humphreys26_4.GapB.chevalleyAmbientBasis_inl]
        rw [hcomp]
        exact (Humphreys26_4.GapB.chevalleyAmbientBasis hx b).linearIndependent.comp _
          (Sum.inl_injective.comp (Subtype.val_injective.comp posOrd.injective))
      have hspan_pos : ⊤ ≤ Submodule.span K (Set.range vPos) := by
        rintro ⟨y, hy⟩ -
        have hy' := hy
        rw [TauCeti.mem_positiveNilradical, TauCeti.rootSpaceSpan_eq_iSup,
          ← LieSubmodule.mem_toSubmodule, LieSubmodule.iSup_toSubmodule] at hy'
        have hle : (⨆ α : TauCeti.posRoots (rootSystem H) b,
            (rootSpace H ((α : H.root) : H → K)).toSubmodule) ≤
            (Submodule.span K (Set.range vPos)).map Npos.toSubmodule.subtype := by
          rw [Submodule.map_span, ← Set.range_comp]
          refine iSup_le fun α => ?_
          intro z hz
          let j : Fin m := posOrd.symm ⟨α.1, α.2⟩
          have hj_root : (posOrd j).1 = α.1 := by simp [j]
          have hone : Module.finrank K (rootSpace H ((α.1 : Weight K H L) : H → K)) = 1 :=
            IsKilling.finrank_rootSpace_eq_one (α.1 : Weight K H L) (H.isNonZero_coe_root α.1)
          have hmem_x : x (α.1 : Weight K H L) ∈ rootSpace H ((α.1 : Weight K H L) : H → K) :=
            hx.toIsSl2System.mem_rootSpace _
          have hne_x : (⟨x (α.1 : Weight K H L), hmem_x⟩ :
              rootSpace H ((α.1 : Weight K H L) : H → K)) ≠ 0 := by
            intro h0
            exact hx.toIsSl2System.ne_zero (α.1 : Weight K H L) (H.isNonZero_coe_root α.1)
              (congrArg Subtype.val h0)
          obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' _ hne_x).mp hone ⟨z, hz⟩
          have hvj : (Npos.toSubmodule.subtype ∘ vPos) j = x (α.1 : Weight K H L) := by
            dsimp [vPos]
            rw [hj_root]
          have hz_eq : z = c • (Npos.toSubmodule.subtype ∘ vPos) j := by
            rw [hvj]
            exact (congrArg Subtype.val hc).symm
          rw [hz_eq]
          exact Submodule.smul_mem _ c (Submodule.subset_span ⟨j, rfl⟩)
        obtain ⟨w, hw, hwy⟩ := hle hy'
        obtain rfl : w = ⟨y, hy⟩ := Subtype.ext hwy
        exact hw
      let bPos : Module.Basis (Fin m) K Npos := Module.Basis.mk hli_pos hspan_pos
      let φPos : _root_.UniversalEnvelopingAlgebra K Npos →ₐ[K]
          _root_.UniversalEnvelopingAlgebra K L :=
        _root_.UniversalEnvelopingAlgebra.lift K
          ((_root_.UniversalEnvelopingAlgebra.ι K).comp Npos.incl)
      let bPBW := bPos.pbwPolynomialBasis
        (fun _ => Humphreys26_4.GapB.dividedPowerPolynomialBasisK K)
      have hφ_bPBW : ∀ C : Fin m → ℕ,
          φPos (bPBW C) = Humphreys26_4.kostantPosTerm b posOrd x C := by
        intro C
        dsimp only [bPBW]
        rw [Module.Basis.pbwPolynomialBasis_apply, map_list_prod, List.map_ofFn]
        refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
        dsimp only [Function.comp_def]
        rw [haeval_dp]
        simp [bPos, vPos]
      have hrange_le : (φPos.range : Set (_root_.UniversalEnvelopingAlgebra K L)) ⊆
          (Submodule.span K (Set.range (Humphreys26_4.kostantPosTerm b posOrd x)) :
            Set (_root_.UniversalEnvelopingAlgebra K L)) := by
        rintro _ ⟨w, rfl⟩
        have hw : w ∈ Submodule.span K (Set.range bPBW) := bPBW.span_eq ▸ Submodule.mem_top
        have hmap : φPos.toLinearMap w ∈
            Submodule.map φPos.toLinearMap (Submodule.span K (Set.range bPBW)) := ⟨w, hw, rfl⟩
        rw [Submodule.map_span, ← Set.range_comp] at hmap
        have hfun : (φPos.toLinearMap ∘ bPBW) = Humphreys26_4.kostantPosTerm b posOrd x :=
          funext hφ_bPBW
        rwa [hfun] at hmap
      have hsub_range : (kostantPosSubring b x : Set (_root_.UniversalEnvelopingAlgebra K L)) ⊆
          (φPos.range : Set (_root_.UniversalEnvelopingAlgebra K L)) := by
        change kostantPosSubring b x ≤ φPos.range.toSubring
        rw [kostantPosSubring, Subring.closure_le]
        rintro _ ⟨⟨α, t⟩, rfl⟩
        let j := posOrd.symm α
        have hj : posOrd j = α := posOrd.apply_symm_apply α
        have hmem_alg : dividedPower t (_root_.UniversalEnvelopingAlgebra.ι K
            (x ((α.1 : H.root) : Weight K H L))) ∈ φPos.range := by
          refine ⟨(t.factorial : K)⁻¹ • (_root_.UniversalEnvelopingAlgebra.ι K (vPos j)) ^ t, ?_⟩
          show φPos ((t.factorial : K)⁻¹ • (_root_.UniversalEnvelopingAlgebra.ι K (vPos j)) ^ t) = _
          dsimp only [φPos]
          rw [map_smul, map_pow, _root_.UniversalEnvelopingAlgebra.lift_ι_apply,
            LieHom.comp_apply, LieSubalgebra.coe_incl, dividedPower_def]
          have hrat : (algebraMap ℚ K) ((t.factorial : ℚ)⁻¹) = (t.factorial : K)⁻¹ := by
            rw [map_inv₀, map_natCast]
          simp only [vPos, hj, Algebra.smul_def, ← hrat]
          rfl
        exact hmem_alg
      have hsub_kostant : kostantPosSubring b x ≤ Humphreys26_4.kostantSubring H x := by
        rw [kostantPosSubring, Subring.closure_le]
        rintro _ ⟨⟨α, t⟩, rfl⟩
        exact Humphreys26_4.GapA.dividedPower_weight_mem_rootSubring hx _ t
      have hterm_eq : ∀ C : Fin m → ℕ,
          Humphreys26_4.kostantPosTerm b posOrd x C = bM (0, 0, C) := by
        intro C
        rw [hbM_eq, Humphreys26_4.kostantMonomial]
        have hN0 : Humphreys26_4.kostantNegTerm b posOrd x 0 = 1 := by
          simp [Humphreys26_4.kostantNegTerm, List.ofFn_const]
        have hC0 : Humphreys26_4.kostantCartanTerm b baseOrd 0 = 1 := by
          simp [Humphreys26_4.kostantCartanTerm, List.ofFn_const]
        rw [hN0, hC0, one_mul, one_mul]
      intro u hu
      have huK : u ∈ Submodule.span K (Set.range (Humphreys26_4.kostantPosTerm b posOrd x)) :=
        hrange_le (hsub_range hu)
      have hrepr_zero : ∀ p, (p.1 ≠ 0 ∨ p.2.1 ≠ 0) → bM.repr u p = 0 := by
        refine Submodule.span_induction ?_ ?_ ?_ ?_ huK
        · rintro _ ⟨C, rfl⟩ p hp
          rw [hterm_eq C, Module.Basis.repr_self, Finsupp.single_apply]
          split_ifs with heq
          · rcases hp with h1 | h2
            · exact absurd (congrArg (fun q => q.1) heq).symm h1
            · exact absurd (congrArg (fun q => q.2.1) heq).symm h2
          · rfl
        · intro p _; simp
        · intro a₁ a₂ _ _ h₁ h₂ p hp; rw [map_add, Finsupp.add_apply, h₁ p hp, h₂ p hp, add_zero]
        · intro c a₁ _ h₁ p hp; rw [map_smul, Finsupp.smul_apply, h₁ p hp, smul_zero]
      have huZ : u ∈ Humphreys26_4.kostantSubring H x := hsub_kostant hu
      change u ∈ (Submodule.span ℤ (Set.range (Humphreys26_4.kostantPosTerm b posOrd x)) : Set _)
      rw [hbZ_sum u huZ]
      refine (Submodule.span ℤ (Set.range (Humphreys26_4.kostantPosTerm b posOrd x))).sum_mem
        fun p hp => ?_
      have hp_nz : bZ.repr ⟨u, huZ⟩ p ≠ 0 := Finsupp.mem_support_iff.mp hp
      have hp1 : p.1 = 0 := by
        by_contra hne
        exact hp_nz (Int.cast_eq_zero.mp ((hbZ_repr u huZ p).symm.trans (hrepr_zero p (Or.inl hne))))
      have hp21 : p.2.1 = 0 := by
        by_contra hne
        exact hp_nz (Int.cast_eq_zero.mp ((hbZ_repr u huZ p).symm.trans (hrepr_zero p (Or.inr hne))))
      have hp_eq : p = (0, 0, p.2.2) := by
        rcases p with ⟨A, B, C⟩
        dsimp at hp1 hp21
        rw [hp1, hp21]
      rw [hp_eq, ← hbM_eq, ← hterm_eq p.2.2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p.2.2, rfl⟩)

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
  constructor
  · rintro ⟨bW, rfl⟩
    refine ⟨Submodule.fg_span (Set.finite_range bW), ?_, ?_⟩
    · rw [Submodule.span_span_of_tower ℤ K (Set.range bW), bW.span_eq]
    · let bM : Module.Basis (Fin (Module.finrank K W)) ℤ
          (Submodule.span ℤ (Set.range bW)) := by
        refine Module.Basis.mk
          (v := fun i => ⟨bW i, Submodule.subset_span ⟨i, rfl⟩⟩) ?_ ?_
        · rw [linearIndependent_iff']
          intro s c hsum i hi
          have hK_li := bW.linearIndependent
          rw [linearIndependent_iff'] at hK_li
          have hsumK : ∑ j ∈ s, (c j : K) • bW j = 0 := by
            have hval := congrArg (Submodule.span ℤ (Set.range bW)).subtype hsum
            rw [map_sum, map_zero] at hval
            simpa only [map_zsmul, Submodule.coe_subtype, Int.cast_smul_eq_zsmul] using hval
          exact Int.cast_eq_zero.mp (hK_li s (fun j => (c j : K)) hsumK i hi)
        · intro y _
          suffices hlift :
              ∃ hy' : (y : W) ∈ Submodule.span ℤ (Set.range bW),
                (⟨(y : W), hy'⟩ : Submodule.span ℤ (Set.range bW)) ∈
                  Submodule.span ℤ (Set.range fun i =>
                    (⟨bW i, Submodule.subset_span ⟨i, rfl⟩⟩ :
                      Submodule.span ℤ (Set.range bW))) by
            obtain ⟨_, hmem⟩ := hlift
            exact hmem
          refine Submodule.span_induction ?_ ?_ ?_ ?_ y.2
          · rintro _ ⟨i, rfl⟩
            exact ⟨Submodule.subset_span ⟨i, rfl⟩, Submodule.subset_span ⟨i, rfl⟩⟩
          · exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
          · rintro a₁ a₂ _ _ ⟨ha₁, h₁⟩ ⟨ha₂, h₂⟩
            exact ⟨Submodule.add_mem _ ha₁ ha₂, Submodule.add_mem _ h₁ h₂⟩
          · rintro z a₁ _ ⟨ha₁, h₁⟩
            exact ⟨Submodule.smul_mem _ z ha₁, Submodule.smul_mem _ z h₁⟩
      rw [Module.finrank_eq_card_basis bM, Fintype.card_fin]
  · rintro ⟨hfg, hspan, hrank_le⟩
    classical
    have : Module.Finite ℤ M := Module.Finite.iff_fg.mpr hfg
    have : Module.IsTorsionFree ℤ W := ⟨fun z hz w₁ w₂ hw => by
      have hsub : (z : K) • (w₁ - w₂) = 0 := by
        rw [Int.cast_smul_eq_zsmul, zsmul_sub, sub_eq_zero]
        exact hw
      exact sub_eq_zero.mp
        ((smul_eq_zero.mp hsub).resolve_left (Int.cast_ne_zero.mpr hz.ne_zero))⟩
    have : Module.IsTorsionFree ℤ M := Submodule.instIsTorsionFree M
    have : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
    let r := Module.finrank ℤ M
    let bM : Module.Basis (Fin r) ℤ M := Module.finBasis ℤ M
    let v : Fin r → W := fun i => (bM i : W)
    have hspan_Z : Submodule.span ℤ (Set.range v) = M := by
      have hmap := congrArg (Submodule.map M.subtype) bM.span_eq
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at hmap
      exact hmap
    have hspan_K : Submodule.span K (Set.range v) = ⊤ := by
      rw [← Submodule.span_span_of_tower ℤ K (Set.range v), hspan_Z, hspan]
    have hle_r : Module.finrank K W ≤ r := by
      have hcard := finrank_span_le_card (R := K) (Set.range v)
      rw [hspan_K, finrank_top] at hcard
      exact le_trans hcard (le_trans (Set.toFinset_card (Set.range v) ▸ Fintype.card_range_le v)
        (by rw [Fintype.card_fin]))
    have hr_eq : r = Module.finrank K W := le_antisymm hrank_le hle_r
    have hcard_eq : Fintype.card (Fin r) = Module.finrank K W := by simp [hr_eq]
    have hli_K : LinearIndependent K v :=
      linearIndependent_of_top_le_span_of_card_eq_finrank hspan_K.ge hcard_eq
    let bW : Module.Basis (Fin (Module.finrank K W)) K W :=
      (Module.Basis.mk hli_K hspan_K.ge).reindex (finCongr hr_eq)
    refine ⟨bW, ?_⟩
    have hrange_eq : Set.range bW = Set.range v := by
      ext w
      simp [bW]
    rw [hrange_eq, hspan_Z]

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

private noncomputable local instance instAlgebraRatEnd
    {W : Type*} [AddCommGroup W] [Module K W] :
    Algebra ℚ (Module.End K W) :=
  Algebra.compHom (Module.End K W) (algebraMap ℚ K)

private theorem ringChoose_end_apply_of_apply_eq_smul_K
    {W : Type*} [AddCommGroup W] [Module K W]
    {f : Module.End K W} {w : W} {μ : K} (h : f w = μ • w) (n : ℕ) :
    (Ring.choose f n) w = Ring.choose μ n • w := by
  have hpow : ∀ k : ℕ, (f ^ k) w = μ ^ k • w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, map_smul, h, smul_smul, ← pow_succ]
  have haeval : ∀ p : Polynomial K, (Polynomial.aeval f p) w = (Polynomial.aeval μ p) • w := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, add_smul]
    | monomial k c =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, smul_mul_assoc, one_mul,
        LinearMap.smul_apply, hpow k, smul_smul, smul_eq_mul]
  have hf_ch : Polynomial.aeval f (TauCeti.binomialPolynomialBasis K n) = Ring.choose f n := by
    rw [TauCeti.binomialPolynomialBasis_apply]
    have hm := Ring.map_choose (Polynomial.aeval f).toRingHom (Polynomial.X : Polynomial K) n
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X] using hm
  have hμ_ch : Polynomial.aeval μ (TauCeti.binomialPolynomialBasis K n) = Ring.choose μ n := by
    rw [TauCeti.binomialPolynomialBasis_apply]
    have hm := Ring.map_choose (Polynomial.aeval μ).toRingHom (Polynomial.X : Polynomial K) n
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X] using hm
  rw [← hf_ch, ← hμ_ch, haeval]

open scoped Classical in
private theorem exists_kostantSubring_weightProjector
    [FiniteDimensional K V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (χ₀ : Weight K H V) :
    let W_K : Weight K H V → Submodule K V :=
      fun χ => (LieModule.weightSpace V (χ : H → K)).toSubmodule
    let eW := LinearEquiv.ofBijective (DirectSum.coeLinearMap W_K)
      (TauCeti.isInternal_weightSpace K H V)
    ∃ u ∈ Humphreys26_4.kostantSubring H x, ∀ m : V,
      TauCeti.UniversalEnvelopingAlgebra.representation K L V u m =
        ((eW.symm m χ₀ : W_K χ₀) : V) := by
  let W_K : Weight K H V → Submodule K V :=
    fun χ => (LieModule.weightSpace V (χ : H → K)).toSubmodule
  let eW := LinearEquiv.ofBijective (DirectSum.coeLinearMap W_K)
    (TauCeti.isInternal_weightSpace K H V)
  let ρ := TauCeti.UniversalEnvelopingAlgebra.representation K L V
  obtain ⟨b⟩ := (rootSystem H).nonempty_base
  let ℓ := Fintype.card ↥b.support
  let baseOrd : Fin ℓ ≃ ↥b.support := (Fintype.equivFin ↥b.support).symm
  have hint : ∀ (χ : Weight K H V) (i : Fin ℓ),
      ∃ z : ℤ, χ (((rootSystem H).coroot (baseOrd i).1 : H)) = (z : K) := by
    intro χ i
    rw [rootSystem_coroot_apply]
    exact TauCeti.exists_int_apply_coroot χ (((baseOrd i).1 : H.root) : Weight K H L)
  choose wt hwt using hint
  have hwt_inj : ∀ {χ : Weight K H V}, wt χ = wt χ₀ → χ = χ₀ := by
    intro χ h_eq
    let δ : Module.Dual K H := (χ : Module.Dual K H) - (χ₀ : Module.Dual K H)
    have hδ_supp : ∀ r ∈ b.support, δ ((rootSystem H).coroot r) = 0 := by
      intro r hr
      let i := baseOrd.symm ⟨r, hr⟩
      have hi : (baseOrd i).1 = r := by simp [i]
      have h_eq_i : wt χ i = wt χ₀ i := congrFun h_eq i
      simp only [δ, LinearMap.sub_apply, Weight.toLinear_apply, ← hi, hwt, h_eq_i, sub_self]
    have hδ_root : ∀ α : H.root, δ ((rootSystem H).coroot α) = 0 := by
      intro α
      have hmem := b.coroot_mem_span_int α
      refine Submodule.span_induction ?_ (map_zero δ)
        (fun _ _ _ _ ha hb => by rw [map_add, ha, hb, add_zero])
        (fun z a _ ha => by rw [map_zsmul, ha, zsmul_zero]) hmem
      rintro _ ⟨r, hr, rfl⟩
      exact hδ_supp r hr
    have hδ_all : ∀ h : H, δ h = 0 := by
      intro h
      have htop : h ∈ Submodule.span K (Set.range (rootSystem H).coroot) := by
        rw [RootPairing.IsRootSystem.span_coroot_eq_top]
        trivial
      refine Submodule.span_induction ?_ (map_zero δ)
        (fun _ _ _ _ ha hb => by rw [map_add, ha, hb, add_zero])
        (fun c a _ ha => by rw [map_smul, ha, smul_zero]) htop
      rintro _ ⟨α, rfl⟩
      exact hδ_root α
    apply Weight.ext
    intro h
    exact sub_eq_zero.mp (hδ_all h)
  let k : ℕ := Finset.univ.sup fun χ : Weight K H V =>
    Finset.univ.sup fun i : Fin ℓ => (wt χ i - wt χ₀ i).natAbs
  let h_uea : Fin ℓ → _root_.UniversalEnvelopingAlgebra K L := fun i =>
    _root_.UniversalEnvelopingAlgebra.ι K (((rootSystem H).coroot (baseOrd i).1 : H) : L)
  let factor : Fin ℓ → _root_.UniversalEnvelopingAlgebra K L := fun i =>
    Ring.choose (h_uea i + ((-wt χ₀ i + (k : ℤ) : ℤ) : _root_.UniversalEnvelopingAlgebra K L)) k *
      Ring.choose (-(h_uea i + ((-wt χ₀ i - (k : ℤ) : ℤ) : _root_.UniversalEnvelopingAlgebra K L))) k
  have hfactor_mem : ∀ i : Fin ℓ, factor i ∈ Humphreys26_4.kostantSubring H x := by
    intro i
    have hch : ∀ n : ℕ, Ring.choose (h_uea i) n ∈ Humphreys26_4.kostantSubring H x := by
      intro n
      dsimp only [h_uea]
      rw [rootSystem_coroot_apply]
      exact Humphreys26_4.GapA.ringChoose_coroot_mem_rootSubring hx _ n
    refine (Humphreys26_4.kostantSubring H x).mul_mem ?_ ?_
    · exact TauCeti.Ring.choose_add_intCast_mem (fun j _ => hch j) _
    · exact TauCeti.Ring.choose_neg_mem (fun j _ =>
        TauCeti.Ring.choose_add_intCast_mem (fun n _ => hch n) _)
  let u₀ : _root_.UniversalEnvelopingAlgebra K L := (List.ofFn factor).prod
  have hu₀_mem : u₀ ∈ Humphreys26_4.kostantSubring H x := by
    refine Subring.list_prod_mem _ fun y hy => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact hfactor_mem i
  have hmap_ch : ∀ (u : _root_.UniversalEnvelopingAlgebra K L) (n : ℕ),
      ρ (Ring.choose u n) = Ring.choose (ρ u) n :=
    fun u n => Ring.map_choose ρ.toRingHom u n
  have hcast_act : ∀ (z : ℤ) (w : V),
      ρ (z : _root_.UniversalEnvelopingAlgebra K L) w = (z : K) • w := by
    intro z w
    have hc : ρ (algebraMap K (_root_.UniversalEnvelopingAlgebra K L) (z : K)) =
        algebraMap K (Module.End K V) (z : K) := AlgHom.commutes ρ (z : K)
    rw [map_intCast] at hc
    rw [hc, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, one_apply_eq_self]
  have hfactor_act : ∀ (χ : Weight K H V) (i : Fin ℓ) {w : V},
      w ∈ W_K χ →
        ρ (factor i) w =
          ((Ring.choose (wt χ i - wt χ₀ i + (k : ℤ)) k *
            Ring.choose (-wt χ i + wt χ₀ i + (k : ℤ)) k : ℤ) : K) • w := by
    intro χ i w hw
    have hw_lie : ∀ h : H, ⁅(h : L), w⁆ = χ h • w := by
      have hw' : w ∈ LieModule.genWeightSpace V (χ : H → K) := by
        rwa [TauCeti.genWeightSpace_eq_weightSpace]
      exact (TauCeti.mem_genWeightSpace_iff_forall_lie_eq_smul.mp hw')
    have hh_act : ρ (h_uea i) w = (wt χ i : K) • w := by
      dsimp only [ρ, h_uea]
      rw [TauCeti.UniversalEnvelopingAlgebra.representation_ι_apply, hw_lie, hwt]
    have harg1 :
        ρ (h_uea i + ((-wt χ₀ i + (k : ℤ) : ℤ) : _root_.UniversalEnvelopingAlgebra K L)) w =
          ((wt χ i - wt χ₀ i + (k : ℤ) : ℤ) : K) • w := by
      rw [map_add, LinearMap.add_apply, hh_act, hcast_act, ← add_smul]
      congr 1
      push_cast
      ring
    have harg2 :
        ρ (-(h_uea i + ((-wt χ₀ i - (k : ℤ) : ℤ) : _root_.UniversalEnvelopingAlgebra K L))) w =
          ((-wt χ i + wt χ₀ i + (k : ℤ) : ℤ) : K) • w := by
      rw [map_neg, map_add, LinearMap.neg_apply, LinearMap.add_apply, hh_act, hcast_act,
        ← add_smul, ← neg_smul]
      congr 1
      push_cast
      ring
    dsimp only [factor]
    rw [map_mul, mul_apply_eq_comp, hmap_ch, hmap_ch,
      ringChoose_end_apply_of_apply_eq_smul_K harg2 k, map_smul,
      ringChoose_end_apply_of_apply_eq_smul_K harg1 k, smul_smul,
      TauCeti.Ring.choose_intCast, TauCeti.Ring.choose_intCast, Int.cast_mul, mul_comm]
  have hlist_act : ∀ (l : List (Fin ℓ)) (χ : Weight K H V) {w : V},
      w ∈ W_K χ →
        ρ (l.map factor).prod w =
          ((l.map fun i =>
            Ring.choose (wt χ i - wt χ₀ i + (k : ℤ)) k *
              Ring.choose (-wt χ i + wt χ₀ i + (k : ℤ)) k).prod : K) • w := by
    intro l
    induction l with
    | nil => intro χ w _; simp
    | cons i tl ih =>
      intro χ w hw
      simp only [List.map_cons, List.prod_cons, map_mul, mul_apply_eq_comp]
      rw [ih χ hw, map_smul, hfactor_act χ i hw, smul_smul]
      congr 1
      push_cast
      ring
  have hu₀_act : ∀ (χ : Weight K H V) {w : V},
      w ∈ W_K χ → ρ u₀ w = if χ = χ₀ then w else 0 := by
    intro χ w hw
    have hl : List.ofFn factor = (List.finRange ℓ).map factor := by
      rw [List.ofFn_eq_map]
    dsimp only [u₀]
    rw [hl, hlist_act (List.finRange ℓ) χ hw]
    have hprod_eq :
        ((List.finRange ℓ).map fun i =>
          Ring.choose (wt χ i - wt χ₀ i + (k : ℤ)) k *
            Ring.choose (-wt χ i + wt χ₀ i + (k : ℤ)) k).prod =
        ∏ i : Fin ℓ,
          (Ring.choose (wt χ i - wt χ₀ i + (k : ℤ)) k *
            Ring.choose (-wt χ i + wt χ₀ i + (k : ℤ)) k) := by
      rw [← Fin.prod_univ_def]
    rw [hprod_eq]
    by_cases hχ : χ = χ₀
    · subst hχ
      have h1 : (∏ i : Fin ℓ,
          (Ring.choose (wt χ i - wt χ i + (k : ℤ)) k *
            Ring.choose (-wt χ i + wt χ i + (k : ℤ)) k) : ℤ) = 1 := by
        refine Finset.prod_eq_one fun i _ => ?_
        have hk1 : wt χ i - wt χ i + (k : ℤ) = (k : ℕ) := by omega
        have hk2 : -wt χ i + wt χ i + (k : ℤ) = (k : ℕ) := by omega
        rw [hk1, hk2, Ring.choose_natCast, Nat.choose_self, Nat.cast_one, mul_one]
      rw [h1, Int.cast_one, one_smul, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
    · have hwne : wt χ ≠ wt χ₀ := fun heq => hχ (hwt_inj heq)
      obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hwne
      have hle_k : (wt χ i₀ - wt χ₀ i₀).natAbs ≤ k := by
        exact le_trans
          (Finset.le_sup (f := fun i => (wt χ i - wt χ₀ i).natAbs) (Finset.mem_univ i₀))
          (Finset.le_sup
            (f := fun χ' : Weight K H V => Finset.univ.sup fun i => (wt χ' i - wt χ₀ i).natAbs)
            (Finset.mem_univ χ))
      have hz0 :
          (Ring.choose (wt χ i₀ - wt χ₀ i₀ + (k : ℤ)) k *
            Ring.choose (-wt χ i₀ + wt χ₀ i₀ + (k : ℤ)) k : ℤ) = 0 := by
        rcases lt_trichotomy (wt χ i₀ - wt χ₀ i₀) 0 with hlt | heq | hgt
        · let n : ℕ := (wt χ i₀ - wt χ₀ i₀ + (k : ℤ)).toNat
          have hn_eq : (n : ℤ) = wt χ i₀ - wt χ₀ i₀ + (k : ℤ) := Int.toNat_of_nonneg (by omega)
          have hn_lt : n < k := by omega
          rw [← hn_eq, Ring.choose_natCast, Nat.choose_eq_zero_of_lt hn_lt, Nat.cast_zero, zero_mul]
        · exact absurd (sub_eq_zero.mp heq) hi₀
        · let n : ℕ := (-wt χ i₀ + wt χ₀ i₀ + (k : ℤ)).toNat
          have hn_eq : (n : ℤ) = -wt χ i₀ + wt χ₀ i₀ + (k : ℤ) := Int.toNat_of_nonneg (by omega)
          have hn_lt : n < k := by omega
          rw [← hn_eq, Ring.choose_natCast, Nat.choose_eq_zero_of_lt hn_lt, Nat.cast_zero, mul_zero]
      rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hz0, Int.cast_zero, zero_smul,
        ite_eq_right_iff.mpr (fun h => absurd h hχ)]
  refine ⟨u₀, hu₀_mem, fun m => ?_⟩
  have hm_sum : m = ∑ χ ∈ (eW.symm m).support, ((eW.symm m χ : W_K χ) : V) := by
    conv_lhs => rw [← eW.apply_symm_apply m, ← DirectSum.sum_support_of (eW.symm m)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun χ _ => DirectSum.coeLinearMap_of W_K χ (eW.symm m χ)
  conv_lhs => rw [hm_sum]
  rw [map_sum]
  have hcongr :
      ∑ χ ∈ (eW.symm m).support, ρ u₀ ((eW.symm m χ : W_K χ) : V) =
        ∑ χ ∈ (eW.symm m).support, if χ = χ₀ then ((eW.symm m χ : W_K χ) : V) else 0 :=
    Finset.sum_congr rfl fun χ _ => hu₀_act χ (eW.symm m χ).2
  rw [hcongr, Finset.sum_ite_eq' (eW.symm m).support χ₀]
  split_ifs with hmem
  · rfl
  · have h0 : eW.symm m χ₀ = 0 := DFinsupp.notMem_support_iff.mp hmem
    rw [h0, ZeroMemClass.coe_zero]

private theorem exists_isHighestWeightVector_split
    (W : Type w) [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]
    [FiniteDimensional K W] [Nontrivial W] (b : (rootSystem H).Base) :
    ∃ (lam : Module.Dual K H) (v : W), TauCeti.IsHighestWeightVector b lam v := by
  classical
  have hmax : ∃ χ : Weight K H W, ∀ i ∈ TauCeti.posRoots (rootSystem H) b,
      LieModule.genWeightSpace W ((i : H → K) + (χ : H → K)) = ⊥ := by
    by_contra hcon
    push Not at hcon
    choose r hrpos hrne using hcon
    let nxt : Weight K H W → Weight K H W :=
      fun χ => ⟨(r χ : H → K) + (χ : H → K), hrne χ⟩
    obtain ⟨χ₀⟩ := TauCeti.nonempty_weight K H W
    have telescope : ∀ p q : ℕ, p ≤ q →
        ((nxt^[q] χ₀ : Weight K H W) : H → K) =
          (∑ i ∈ Finset.Ico p q, ((r (nxt^[i] χ₀) : H → K))) +
            ((nxt^[p] χ₀ : Weight K H W) : H → K) := by
      intro p q hpq
      induction q, hpq using Nat.le_induction with
      | base => simp
      | succ q hq ih =>
        rw [Function.iterate_succ_apply', Finset.sum_Ico_succ_top hq]
        have hstep : ((nxt (nxt^[q] χ₀) : Weight K H W) : H → K) =
            (r (nxt^[q] χ₀) : H → K) + ((nxt^[q] χ₀ : Weight K H W) : H → K) := rfl
        rw [hstep, ih]
        abel
    have key : ∀ p q : ℕ, p < q → nxt^[p] χ₀ ≠ nxt^[q] χ₀ := by
      intro p q hpq hEq
      have hsum : (∑ i ∈ Finset.Ico p q, ((r (nxt^[i] χ₀) : H → K))) = 0 := by
        have h := telescope p q hpq.le
        rw [← hEq] at h
        simpa using h.symm
      have hroot : ∑ i ∈ Finset.Ico p q,
          (rootSystem H).root (r (nxt^[i] χ₀)) = 0 := by
        ext h
        simpa using congrFun hsum h
      exact TauCeti.sum_root_ne_zero_of_mem_posRoots (rootSystem H) b
        ⟨p, by simp [hpq]⟩ (fun i _ => hrpos _) hroot
    obtain ⟨p, q, hpq, hEq⟩ := Finite.exists_ne_map_eq_of_infinite fun k : ℕ => nxt^[k] χ₀
    rcases hpq.lt_or_gt with h | h
    · exact key p q h hEq
    · exact key q p h hEq.symm
  obtain ⟨χ, hχ⟩ := hmax
  obtain ⟨v, hv, hv0⟩ := χ.exists_ne_zero
  refine ⟨(χ : Module.Dual K H), v,
    TauCeti.isHighestWeightVector_of_forall_rootSpace hv0
      (TauCeti.mem_genWeightSpace_iff_forall_lie_eq_smul.mp hv) fun i hi y hy => ?_⟩
  have hmem : ⁅y, v⁆ ∈ LieModule.genWeightSpace W ((i : H → K) + (χ : H → K)) :=
    LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace hy hv
  rw [hχ i hi] at hmem
  simpa using hmem

private def negListShift (b : (rootSystem H).Base) :
    List ({α : H.root // b.IsPos α} × ℕ) → (H → K)
  | [] => 0
  | p :: tl => p.2 • (((p.1.1 : H.root) : Weight K H L) : H → K) + negListShift b tl

private noncomputable def negListRootSum (b : (rootSystem H).Base) :
    List ({α : H.root // b.IsPos α} × ℕ) → Module.Dual K H
  | [] => 0
  | p :: tl => p.2 • (rootSystem H).root p.1.1 + negListRootSum b tl

private theorem finrank_le_of_kostantInvariant_inter_le_span
    [FiniteDimensional K V] [LieModule.IsIrreducible K L V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (b : (rootSystem H).Base) {lam : Module.Dual K H} {v : V}
    (hv : TauCeti.IsHighestWeightVector b lam v)
    (M : Submodule ℤ V) (hM_fg : M.FG) (hM_inv : IsKostantInvariant H x M)
    (hM_inter : M ⊓ (LieModule.weightSpace V (lam : H → K)).toSubmodule.restrictScalars ℤ ≤
      Submodule.span ℤ {v}) :
    Module.finrank ℤ M ≤ Module.finrank K V := by
  classical
  let ρ := TauCeti.UniversalEnvelopingAlgebra.representation K L V
  let m := Fintype.card {α : H.root // b.IsPos α}
  let posOrd : Fin m ≃ {α : H.root // b.IsPos α} := (Fintype.equivFin _).symm
  let ℓ := Fintype.card ↥b.support
  let baseOrd : Fin ℓ ≃ ↥b.support := (Fintype.equivFin _).symm
  have hv_wt : v ∈ LieModule.weightSpace V (lam : H → K) := by
    rw [← TauCeti.genWeightSpace_eq_weightSpace]
    exact hv.mem_genWeightSpace
  have hspan_kostant_top :
      Submodule.span K (Humphreys26_4.kostantSubring H x :
        Set (_root_.UniversalEnvelopingAlgebra K L)) = ⊤ := by
    rw [← top_le_iff, ← (Humphreys26_4.kostantMonomial_basis_over_field hx b posOrd baseOrd).2]
    refine Submodule.span_mono ?_
    rintro _ ⟨p, rfl⟩
    exact Humphreys26_4.GapA.kostantMonomial_mem_rootSubring hx b posOrd baseOrd p
  have hcyclic : ∀ {w₀ : V}, w₀ ≠ 0 →
      Submodule.span K {y : V | ∃ u ∈ Humphreys26_4.kostantSubring H x, ρ u w₀ = y} = ⊤ := by
    intro w₀ hw₀
    have hlie_top : LieSubmodule.lieSpan K L {w₀} = ⊤ := by
      have hne_bot : LieSubmodule.lieSpan K L {w₀} ≠ ⊥ := by
        intro hbot
        have hw_mem : w₀ ∈ LieSubmodule.lieSpan K L {w₀} :=
          LieSubmodule.subset_lieSpan (Set.mem_singleton w₀)
        rw [hbot] at hw_mem
        exact hw₀ hw_mem
      exact eq_top_iff.mpr ((IsSimpleOrder.eq_bot_or_eq_top _).resolve_left hne_bot).ge
    have horb := Subring.span_orbitOfRep_eq_span (R := K)
      (Humphreys26_4.kostantSubring H x) ρ {w₀} hspan_kostant_top
    have htop_all : Submodule.span K {y : V | ∃ u : _root_.UniversalEnvelopingAlgebra K L,
        ∃ z ∈ ({w₀} : Set V), ρ u z = y} = ⊤ := by
      rw [eq_top_iff]
      intro y _
      obtain ⟨u, hu⟩ := TauCeti.UniversalEnvelopingAlgebra.exists_representation_apply_eq_of_lieSpan_eq_top
        hlie_top y
      exact Submodule.subset_span ⟨u, w₀, Set.mem_singleton w₀, hu⟩
    rw [htop_all] at horb
    rw [← top_le_iff, ← horb, Subring.orbitOfRep_def, Submodule.span_span_of_tower ℤ K]
    refine Submodule.span_mono ?_
    rintro _ ⟨u, hu, z, hz, rfl⟩
    obtain rfl : z = w₀ := Set.mem_singleton_iff.mp hz
    exact ⟨u, hu, rfl⟩
  have : Module.Finite ℤ M := Module.Finite.iff_fg.mpr hM_fg
  have : Module.IsTorsionFree ℤ V := ⟨fun z hz w₁ w₂ hw => by
    have hsub : (z : K) • (w₁ - w₂) = 0 := by
      rw [Int.cast_smul_eq_zsmul, zsmul_sub, sub_eq_zero]
      exact hw
    exact sub_eq_zero.mp
      ((smul_eq_zero.mp hsub).resolve_left (Int.cast_ne_zero.mpr hz.ne_zero))⟩
  have : Module.IsTorsionFree ℤ M := Submodule.instIsTorsionFree M
  have : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  let r := Module.finrank ℤ M
  let bM_Z : Module.Basis (Fin r) ℤ M := Module.finBasis ℤ M
  have hli_K : LinearIndependent K (fun i : Fin r => (bM_Z i : V)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc_sum i₀
    by_contra hci₀
    let bQK := Module.Basis.ofVectorSpace ℚ K
    have hrepr_ne : bQK.repr (c i₀) ≠ 0 := fun h0 =>
      hci₀ (bQK.repr.injective (h0.trans (map_zero bQK.repr).symm))
    obtain ⟨κ₀, hκ₀_mem⟩ : ∃ κ₀, κ₀ ∈ (bQK.repr (c i₀)).support :=
      Finsupp.support_nonempty_iff.mpr hrepr_ne
    let S_κ := Finset.univ.biUnion fun i : Fin r => (bQK.repr (c i)).support
    have hκ₀_S : κ₀ ∈ S_κ := Finset.mem_biUnion.mpr ⟨i₀, Finset.mem_univ i₀, hκ₀_mem⟩
    let D : ℕ := ∏ i : Fin r, ∏ κ ∈ S_κ, (bQK.repr (c i) κ).den
    have hD_pos : 0 < D :=
      Finset.prod_pos fun i _ => Finset.prod_pos fun κ _ => (bQK.repr (c i) κ).pos
    let z_coeff : Fin r → _ → ℤ := fun i κ =>
      (bQK.repr (c i) κ).num * ((D / (bQK.repr (c i) κ).den : ℕ) : ℤ)
    have hz_cast : ∀ (i : Fin r) {κ}, κ ∈ S_κ →
        (z_coeff i κ : ℚ) = (D : ℚ) * bQK.repr (c i) κ := by
      intro i κ hκ
      have hdvd1 : (bQK.repr (c i) κ).den ∣ ∏ κ' ∈ S_κ, (bQK.repr (c i) κ').den :=
        Finset.dvd_prod_of_mem (fun κ' => (bQK.repr (c i) κ').den) hκ
      have hdvd2 : (∏ κ' ∈ S_κ, (bQK.repr (c i) κ').den) ∣ D :=
        Finset.dvd_prod_of_mem (fun i' : Fin r => ∏ κ' ∈ S_κ, (bQK.repr (c i') κ').den)
          (Finset.mem_univ i)
      have hdvd : (bQK.repr (c i) κ).den ∣ D := dvd_trans hdvd1 hdvd2
      obtain ⟨q_nat, hq_eq⟩ := hdvd
      have hden_nz : (bQK.repr (c i) κ).den ≠ 0 := (bQK.repr (c i) κ).den_nz
      have hdiv : D / (bQK.repr (c i) κ).den = q_nat := by
        rw [hq_eq, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hden_nz)]
      dsimp only [z_coeff]
      rw [hdiv, hq_eq]
      push_cast
      have hnum_den := Rat.mul_den_eq_num (bQK.repr (c i) κ)
      calc
        ((bQK.repr (c i) κ).num : ℚ) * (q_nat : ℚ)
          = (bQK.repr (c i) κ * (bQK.repr (c i) κ).den) * (q_nat : ℚ) := by
            rw [hnum_den]
        _ = ((bQK.repr (c i) κ).den : ℚ) * (q_nat : ℚ) * bQK.repr (c i) κ := by ring
    have hz_i₀_nz : z_coeff i₀ κ₀ ≠ 0 := by
      intro hz0
      have hq0 := hz_cast i₀ hκ₀_S
      rw [hz0, Int.cast_zero] at hq0
      have hD_nz : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hD_pos)
      exact (Finsupp.mem_support_iff.mp hκ₀_mem)
        ((mul_eq_zero.mp hq0.symm).resolve_left hD_nz)
    let m_vec : _ → V := fun κ => ∑ i : Fin r, z_coeff i κ • (bM_Z i : V)
    have hm_mem : ∀ κ, m_vec κ ∈ M := fun κ =>
      M.sum_mem fun i _ => M.smul_mem (z_coeff i κ) (bM_Z i).2
    have hm_κ₀_nz : m_vec κ₀ ≠ 0 := by
      intro hm0
      have hM0 : (∑ i : Fin r, z_coeff i κ₀ • bM_Z i) = 0 := by
        apply Subtype.ext
        simpa [m_vec] using hm0
      exact hz_i₀_nz (Fintype.linearIndependent_iff.mp bM_Z.linearIndependent _ hM0 i₀)
    have hc_expand : ∀ i : Fin r,
        (D : K) * c i = ∑ κ ∈ S_κ, (z_coeff i κ : K) * bQK κ := by
      intro i
      have hci_sum : c i = ∑ κ ∈ S_κ, (bQK.repr (c i) κ : K) * bQK κ := by
        have hlin := bQK.linearCombination_repr (c i)
        rw [Finsupp.linearCombination_apply, Finsupp.sum] at hlin
        have hsub : (bQK.repr (c i)).support ⊆ S_κ := fun κ hκ =>
          Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hκ⟩
        have hsum_S : ∑ κ ∈ S_κ, (bQK.repr (c i) κ) • bQK κ = c i := by
          rw [← Finset.sum_subset hsub (fun κ _ hnot => by
            rw [Finsupp.notMem_support_iff.mp hnot, zero_smul])]
          exact hlin
        conv_lhs => rw [← hsum_S]
        exact Finset.sum_congr rfl fun κ _ => Rat.smul_def _ _
      rw [hci_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun κ hκ => ?_
      have hzc : (z_coeff i κ : K) = (D : K) * (bQK.repr (c i) κ : K) := by
        have h1 := congrArg (Rat.cast : ℚ → K) (hz_cast i hκ)
        push_cast at h1
        exact h1
      rw [hzc, mul_assoc]
    have hrel_m : ∑ κ ∈ S_κ, bQK κ • m_vec κ = 0 := by
      have hswap : ∑ κ ∈ S_κ, bQK κ • m_vec κ = (D : K) • ∑ i : Fin r, c i • (bM_Z i : V) := by
        simp only [m_vec, Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, hc_expand i, Finset.sum_smul]
        refine Finset.sum_congr rfl fun κ _ => ?_
        rw [← Int.cast_smul_eq_zsmul K (z_coeff i κ), smul_smul, mul_comm]
      rw [hswap, hc_sum, smul_zero]
    let W_K : Weight K H V → Submodule K V :=
      fun χ => (LieModule.weightSpace V (χ : H → K)).toSubmodule
    let eW := LinearEquiv.ofBijective (DirectSum.coeLinearMap W_K)
      (TauCeti.isInternal_weightSpace K H V)
    obtain ⟨u_proj, hu_proj_mem, hu_proj_act⟩ :=
      exists_kostantSubring_weightProjector (V := V) hx hv.weight
    have hu_proj_v : ρ u_proj v = v := by
      rw [hu_proj_act v]
      have heW_v : eW (DirectSum.of (fun χ => ↥(W_K χ)) hv.weight ⟨v, hv_wt⟩) = v :=
        DirectSum.coeLinearMap_of W_K hv.weight ⟨v, hv_wt⟩
      have hsymm_v : eW.symm v = DirectSum.of (fun χ => ↥(W_K χ)) hv.weight ⟨v, hv_wt⟩ :=
        eW.symm_apply_eq.mpr heW_v.symm
      rw [hsymm_v, DirectSum.of_eq_same]
    have hex_u₀ : ∃ u₀ ∈ Humphreys26_4.kostantSubring H x,
        ρ (u_proj * u₀) (m_vec κ₀) ≠ 0 := by
      by_contra hall0
      push Not at hall0
      have hv_mem_span : v ∈ Submodule.span K
          {y : V | ∃ u ∈ Humphreys26_4.kostantSubring H x, ρ u (m_vec κ₀) = y} := by
        rw [hcyclic hm_κ₀_nz]
        trivial
      have hv0 : ρ u_proj v = 0 := by
        refine Submodule.span_induction ?_ (map_zero _)
          (fun _ _ _ _ ha hb => by rw [map_add, ha, hb, add_zero])
          (fun a _ _ ha => by rw [map_smul, ha, smul_zero]) hv_mem_span
        rintro _ ⟨u, hu, rfl⟩
        have hm := hall0 u hu
        rwa [map_mul, mul_apply_eq_comp] at hm
      rw [hu_proj_v] at hv0
      exact hv.ne_zero hv0
    obtain ⟨u₀, hu₀_mem, hu_star_nz⟩ := hex_u₀
    let u_star := u_proj * u₀
    have hu_star_mem : u_star ∈ Humphreys26_4.kostantSubring H x :=
      (Humphreys26_4.kostantSubring H x).mul_mem hu_proj_mem hu₀_mem
    have hstar_int : ∀ κ, ∃ n : ℤ, ρ u_star (m_vec κ) = n • v := by
      intro κ
      have hmem_M : ρ u_star (m_vec κ) ∈ M := hM_inv u_star hu_star_mem _ (hm_mem κ)
      have hmem_lam : ρ u_star (m_vec κ) ∈
          (LieModule.weightSpace V (lam : H → K)).toSubmodule.restrictScalars ℤ := by
        dsimp only [u_star]
        rw [map_mul, mul_apply_eq_comp, hu_proj_act]
        exact (eW.symm (ρ u₀ (m_vec κ)) hv.weight).2
      have hmem_span : ρ u_star (m_vec κ) ∈ Submodule.span ℤ {v} :=
        hM_inter ⟨hmem_M, hmem_lam⟩
      obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp hmem_span
      exact ⟨n, hn.symm⟩
    choose n_star hn_star using hstar_int
    have hn_κ₀_nz : n_star κ₀ ≠ 0 := by
      intro hn0
      apply hu_star_nz
      change ρ u_star (m_vec κ₀) = 0
      rw [hn_star κ₀, hn0, zero_smul]
    have happ := congrArg (ρ u_star) hrel_m
    rw [map_zero, map_sum] at happ
    have hcomb_v : (∑ κ ∈ S_κ, (n_star κ : ℚ) • bQK κ) • v = 0 := by
      rw [Finset.sum_smul]
      refine (Finset.sum_congr rfl fun κ _ => ?_).trans happ
      rw [map_smul, hn_star κ, ← Int.cast_smul_eq_zsmul K (n_star κ), smul_smul,
        Rat.smul_def, Rat.cast_intCast, mul_comm]
    have hcomb_K : ∑ κ ∈ S_κ, (n_star κ : ℚ) • bQK κ = 0 :=
      (smul_eq_zero.mp hcomb_v).resolve_right hv.ne_zero
    have hli_QK := linearIndependent_iff'.mp bQK.linearIndependent
    have hq0 : (n_star κ₀ : ℚ) = 0 := hli_QK S_κ (fun κ => (n_star κ : ℚ)) hcomb_K κ₀ hκ₀_S
    exact hn_κ₀_nz (Int.cast_eq_zero.mp hq0)
  simpa [r] using hli_K.fintype_card_le_finrank

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
  let W_K : Weight K H V → Submodule K V :=
    fun χ => (LieModule.weightSpace V (χ : H → K)).toSubmodule
  let eW := LinearEquiv.ofBijective (DirectSum.coeLinearMap W_K)
    (TauCeti.isInternal_weightSpace K H V)
  have hproj : ∀ m ∈ M, ∀ χ : Weight K H V, ((eW.symm m χ : W_K χ) : V) ∈ M := by
    intro m hm χ
    obtain ⟨u, hu, hu_eq⟩ := exists_kostantSubring_weightProjector (V := V) hx χ
    rw [← hu_eq m]
    exact hM u hu m hm
  have hsum_m : ∀ m : V, m = ∑ χ ∈ (eW.symm m).support, ((eW.symm m χ : W_K χ) : V) := by
    intro m
    conv_lhs => rw [← eW.apply_symm_apply m, ← DirectSum.sum_support_of (eW.symm m)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun χ _ => DirectSum.coeLinearMap_of W_K χ (eW.symm m χ)
  have hK_indep := (TauCeti.isInternal_weightSpace K H V).submodule_iSupIndep
  refine ⟨?_, ?_, ?_⟩
  · refine le_antisymm (iSup_le fun _ => inf_le_left) fun m hm => ?_
    rw [hsum_m m]
    refine AddSubgroup.sum_mem _ fun χ _ => ?_
    exact le_iSup (fun χ : Weight K H V => M ⊓ (W_K χ).toAddSubgroup) χ
      ⟨hproj m hm χ, (eW.symm m χ).2⟩
  · have hZ_indep : iSupIndep (fun χ : Weight K H V =>
        AddSubgroup.toIntSubmodule (M ⊓ (W_K χ).toAddSubgroup)) := by
      rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
      intro s f hf hsum0 χ hχ
      exact (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero W_K).mp hK_indep s f
        (fun η hη => (hf η hη).2) hsum0 χ hχ
    intro χ
    rw [AddSubgroup.disjoint_def]
    intro y hy₁ hy₂
    have hy₂' : y ∈ ⨆ j, ⨆ (_ : j ≠ χ), AddSubgroup.toIntSubmodule (M ⊓ (W_K j).toAddSubgroup) := by
      have hm : y ∈ AddSubgroup.toIntSubmodule (⨆ j, ⨆ (_ : j ≠ χ), M ⊓ (W_K j).toAddSubgroup) := hy₂
      rw [map_iSup] at hm
      have hcongr : (⨆ j, AddSubgroup.toIntSubmodule
          (⨆ (_ : j ≠ χ), M ⊓ (W_K j).toAddSubgroup)) =
          (⨆ j, ⨆ (_ : j ≠ χ), AddSubgroup.toIntSubmodule (M ⊓ (W_K j).toAddSubgroup)) := by
        refine iSup_congr fun j => ?_
        by_cases hj : j ≠ χ <;> simp [hj]
      rwa [hcongr] at hm
    exact Submodule.disjoint_def.mp (hZ_indep χ) y hy₁ hy₂'
  · let N_M : Weight K H V → Submodule ℤ M := fun χ =>
      ((W_K χ).restrictScalars ℤ).comap (AddMonoidHom.toIntLinearMap M.subtype)
    change Function.Bijective (DirectSum.coeLinearMap N_M)
    refine ⟨?_, ?_⟩
    · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro d hd
      rw [LinearMap.mem_ker] at hd
      have hd_sum : d = ∑ χ ∈ d.support, DirectSum.of (fun χ => ↥(N_M χ)) χ (d χ) :=
        (DirectSum.sum_support_of d).symm
      have hV_sum : ∑ χ ∈ d.support, (((d χ : N_M χ) : M) : V) = 0 := by
        have hval := congrArg (M.subtype : M →+ V) hd
        rw [map_zero] at hval
        conv_lhs at hval => rw [hd_sum, map_sum, map_sum]
        refine (Finset.sum_congr rfl fun χ _ => ?_).trans hval
        rw [DirectSum.coeLinearMap_of]
        rfl
      apply DFinsupp.ext
      intro χ
      by_cases hχ : χ ∈ d.support
      · have h0 := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero W_K).mp hK_indep
          d.support (fun η => (((d η : N_M η) : M) : V)) (fun η _ => (d η).2) hV_sum χ hχ
        exact Subtype.ext (Subtype.ext h0)
      · exact DFinsupp.notMem_support_iff.mp hχ
    · rintro ⟨m, hm⟩
      let y : ∀ χ : Weight K H V, N_M χ :=
        fun χ => ⟨⟨((eW.symm m χ : W_K χ) : V), hproj m hm χ⟩, (eW.symm m χ).2⟩
      refine ⟨∑ χ ∈ (eW.symm m).support, DirectSum.of (fun χ => ↥(N_M χ)) χ (y χ), ?_⟩
      apply Subtype.ext
      have hval := map_sum (M.subtype.comp (DirectSum.coeLinearMap N_M).toAddMonoidHom)
        (fun χ => DirectSum.of (fun χ => ↥(N_M χ)) χ (y χ)) (eW.symm m).support
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
        AddSubgroup.coe_subtype] at hval
      rw [hval]
      refine (Finset.sum_congr rfl fun χ _ => ?_).trans (hsum_m m).symm
      rw [DirectSum.coeLinearMap_of]

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
  classical
  let ρ := TauCeti.UniversalEnvelopingAlgebra.representation K L V
  let m := Fintype.card {α : H.root // b.IsPos α}
  let posOrd : Fin m ≃ {α : H.root // b.IsPos α} := (Fintype.equivFin _).symm
  let ℓ := Fintype.card ↥b.support
  let baseOrd : Fin ℓ ≃ ↥b.support := (Fintype.equivFin _).symm
  let M_min := minAdmissibleLattice H x v
  let M_neg := Subring.orbitOfRep (kostantNegSubring b x) ρ {v}
  have hv_wt : v ∈ LieModule.weightSpace V (lam : H → K) := by
    rw [← TauCeti.genWeightSpace_eq_weightSpace]
    exact hv.mem_genWeightSpace
  -- Step 1: Action of positive divided-power products `e_C` on `v`
  have hpos_single : ∀ (α : {α : H.root // b.IsPos α}) (t : ℕ),
      ρ (dividedPower t (_root_.UniversalEnvelopingAlgebra.ι K (x ((α.1 : H.root) : Weight K H L))))
        v = if t = 0 then v else 0 := by
    intro α t
    cases t with
    | zero => simp
    | succ t =>
      have hkill : ρ (_root_.UniversalEnvelopingAlgebra.ι K
          (x ((α.1 : H.root) : Weight K H L))) v = 0 := by
        rw [TauCeti.UniversalEnvelopingAlgebra.representation_ι_apply]
        exact hv.lie_eq_zero_of_mem_rootSpace α.2 (hx.toIsSl2System.mem_rootSpace _)
      rw [dividedPower_def, Algebra.smul_def, map_mul, map_pow, pow_succ,
        mul_apply_eq_comp, mul_apply_eq_comp, hkill, map_zero, map_zero,
        ite_eq_right_iff.mpr (fun h => absurd h (Nat.succ_ne_zero t))]
  have hpos_list : ∀ l : List ({α : H.root // b.IsPos α} × ℕ),
      ρ (l.map fun p => dividedPower p.2
        (_root_.UniversalEnvelopingAlgebra.ι K (x ((p.1.1 : H.root) : Weight K H L)))).prod v =
      if ∀ p ∈ l, p.2 = 0 then v else 0 := by
    intro l
    induction l with
    | nil => simp
    | cons p tl ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, mul_apply_eq_comp]
      by_cases htl : ∀ q ∈ tl, q.2 = 0
      · rw [ih, ite_eq_left_iff.mpr (fun h => absurd htl h), hpos_single p.1 p.2]
        by_cases hp : p.2 = 0
        · have hall : ∀ q ∈ p :: tl, q.2 = 0 := List.forall_mem_cons.mpr ⟨hp, htl⟩
          rw [ite_eq_left_iff.mpr (fun h => absurd hp h),
            ite_eq_left_iff.mpr (fun h => absurd hall h)]
        · have hnall : ¬ ∀ q ∈ p :: tl, q.2 = 0 := fun h => hp (List.forall_mem_cons.mp h).1
          rw [ite_eq_right_iff.mpr (fun h => absurd h hp),
            ite_eq_right_iff.mpr (fun h => absurd h hnall)]
      · have hnall : ¬ ∀ q ∈ p :: tl, q.2 = 0 := fun h => htl (List.forall_mem_cons.mp h).2
        rw [ih, ite_eq_right_iff.mpr (fun h => absurd h htl), map_zero,
          ite_eq_right_iff.mpr (fun h => absurd h hnall)]
  have heC_act : ∀ C : Fin m → ℕ,
      ρ (Humphreys26_4.kostantPosTerm b posOrd x C) v = if C = 0 then v else 0 := by
    intro C
    let l : List ({α : H.root // b.IsPos α} × ℕ) := List.ofFn fun j : Fin m => (posOrd j, C j)
    have hprod_eq : Humphreys26_4.kostantPosTerm b posOrd x C =
        (l.map fun p => dividedPower p.2
          (_root_.UniversalEnvelopingAlgebra.ι K (x ((p.1.1 : H.root) : Weight K H L)))).prod := by
      simp [Humphreys26_4.kostantPosTerm, l, List.map_ofFn, Function.comp_def]
    have hall_iff : (∀ p ∈ l, p.2 = 0) ↔ C = 0 := by
      simp only [l, List.forall_mem_ofFn_iff, funext_iff, Pi.zero_apply]
    rw [hprod_eq, hpos_list l]
    by_cases hC : C = 0
    · rw [ite_eq_left_iff.mpr (fun h => absurd (hall_iff.mpr hC) h),
        ite_eq_left_iff.mpr (fun h => absurd hC h)]
    · rw [ite_eq_right_iff.mpr (fun h => absurd (hall_iff.mp h) hC),
        ite_eq_right_iff.mpr (fun h => absurd h hC)]
  -- Step 2: Action of Cartan binomial products `h_B` on `v`
  have hint_lam : ∀ i : Fin ℓ,
      ∃ z : ℤ, lam ((rootSystem H).coroot (baseOrd i).1) = (z : K) := by
    intro i
    rw [rootSystem_coroot_apply]
    exact TauCeti.exists_int_apply_coroot hv.weight (((baseOrd i).1 : H.root) : Weight K H L)
  choose z_lam hz_lam using hint_lam
  have hmap_ch : ∀ (u : _root_.UniversalEnvelopingAlgebra K L) (n : ℕ),
      ρ (Ring.choose u n) = Ring.choose (ρ u) n :=
    fun u n => Ring.map_choose ρ.toRingHom u n
  have hcartan_single : ∀ (i : Fin ℓ) (n : ℕ),
      ρ (Ring.choose
        (_root_.UniversalEnvelopingAlgebra.ι K
          (((rootSystem H).coroot (baseOrd i).1 : H) : L)) n) v =
      Ring.choose (z_lam i) n • v := by
    intro i n
    have hh : ρ (_root_.UniversalEnvelopingAlgebra.ι K
        (((rootSystem H).coroot (baseOrd i).1 : H) : L)) v = (z_lam i : K) • v := by
      rw [TauCeti.UniversalEnvelopingAlgebra.representation_ι_apply, hv.lie_eq_smul, hz_lam]
    rw [hmap_ch, ringChoose_end_apply_of_apply_eq_smul_K hh n,
      TauCeti.Ring.choose_intCast, Int.cast_smul_eq_zsmul]
  have hcartan_list : ∀ l : List (Fin ℓ × ℕ),
      ∃ z : ℤ, ρ (l.map fun p => Ring.choose
        (_root_.UniversalEnvelopingAlgebra.ι K
          (((rootSystem H).coroot (baseOrd p.1).1 : H) : L)) p.2).prod v = z • v := by
    intro l
    induction l with
    | nil => exact ⟨1, by simp⟩
    | cons p tl ih =>
      obtain ⟨z_tl, hz_tl⟩ := ih
      refine ⟨z_tl * Ring.choose (z_lam p.1) p.2, ?_⟩
      simp only [List.map_cons, List.prod_cons, map_mul, mul_apply_eq_comp]
      rw [hz_tl, map_zsmul, hcartan_single, smul_smul]
  have hhB_act : ∀ B : Fin ℓ → ℕ,
      ∃ z : ℤ, ρ (Humphreys26_4.kostantCartanTerm b baseOrd B) v = z • v := by
    intro B
    let l : List (Fin ℓ × ℕ) := List.ofFn fun i : Fin ℓ => (i, B i)
    have hprod_eq : Humphreys26_4.kostantCartanTerm b baseOrd B =
        (l.map fun p => Ring.choose
          (_root_.UniversalEnvelopingAlgebra.ι K
            (((rootSystem H).coroot (baseOrd p.1).1 : H) : L)) p.2).prod := by
      simp [Humphreys26_4.kostantCartanTerm, l, List.map_ofFn, Function.comp_def]
    rw [hprod_eq]
    exact hcartan_list l
  -- Step 3: `M_min = M_neg`
  have hneg_le_kostant : kostantNegSubring b x ≤ Humphreys26_4.kostantSubring H x := by
    rw [kostantNegSubring, Subring.closure_le]
    rintro _ ⟨⟨α, t⟩, rfl⟩
    exact Humphreys26_4.GapA.dividedPower_weight_mem_rootSubring hx _ t
  have hfA_mem : ∀ A : Fin m → ℕ,
      Humphreys26_4.kostantNegTerm b posOrd x A ∈ kostantNegSubring b x := by
    intro A
    refine Subring.list_prod_mem _ fun y hy => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    exact Subring.subset_closure ⟨(posOrd j, A j), rfl⟩
  have hM_eq : M_min = M_neg := by
    apply le_antisymm
    · dsimp only [M_min, minAdmissibleLattice]
      rw [Subring.orbitOfRep_le_iff]
      intro u hu y hy
      rw [Set.mem_singleton_iff.mp hy]
      have hu_lat : u ∈ Humphreys26_4.kostantLattice b posOrd baseOrd x := by
        change u ∈ (Humphreys26_4.kostantLattice b posOrd baseOrd x : Set _)
        rw [Humphreys26_4.kostantLattice_eq_kostantSubring hx b posOrd baseOrd]
        exact hu
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hu_lat
      · rintro _ ⟨⟨A, B, C⟩, rfl⟩
        dsimp only [Humphreys26_4.kostantMonomial]
        rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, heC_act C]
        by_cases hC : C = 0
        · rw [ite_eq_left_iff.mpr (fun h => absurd hC h)]
          obtain ⟨z, hz⟩ := hhB_act B
          rw [hz, map_zsmul]
          exact M_neg.smul_mem z (Subring.apply_mem_orbitOfRep _ _ _ (hfA_mem A) (Set.mem_singleton v))
        · rw [ite_eq_right_iff.mpr (fun h => absurd h hC), map_zero, map_zero]
          exact M_neg.zero_mem
      · rw [map_zero, LinearMap.zero_apply]; exact M_neg.zero_mem
      · intro a₁ a₂ _ _ h₁ h₂; rw [map_add, LinearMap.add_apply]; exact M_neg.add_mem h₁ h₂
      · intro z a₁ _ h₁; rw [map_zsmul, LinearMap.smul_apply]; exact M_neg.smul_mem z h₁
    · dsimp only [M_neg]
      rw [Subring.orbitOfRep_le_iff]
      intro u hu y hy
      exact Subring.apply_mem_orbitOfRep _ _ _ (hneg_le_kostant hu) hy
  -- Step 4: Weight shifting and `M_min ⊓ V_lam = Submodule.span ℤ {v}`
  have hdp_shift : ∀ (β : Weight K H L) (t : ℕ) (μ : H → K) {w : V},
      w ∈ LieModule.weightSpace V μ →
        ρ (dividedPower t (_root_.UniversalEnvelopingAlgebra.ι K (x β))) w ∈
          LieModule.weightSpace V (μ + t • (β : H → K)) := by
    intro β t
    have hpow_shift : ∀ (n : ℕ) (μ : H → K) {w : V},
        w ∈ LieModule.weightSpace V μ →
          ((ρ (_root_.UniversalEnvelopingAlgebra.ι K (x β))) ^ n) w ∈
            LieModule.weightSpace V (μ + n • (β : H → K)) := by
      intro n
      induction n with
      | zero => intro μ w hw; simpa using hw
      | succ n ih =>
        intro μ w hw
        rw [pow_succ', mul_apply_eq_comp, TauCeti.UniversalEnvelopingAlgebra.representation_ι_apply]
        have hstep := ih μ hw
        rw [← TauCeti.genWeightSpace_eq_weightSpace] at hstep ⊢
        have hlie := LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace
          (hx.toIsSl2System.mem_rootSpace β) hstep
        have hwt_add : (β : H → K) + (μ + n • (β : H → K)) = μ + (n + 1) • (β : H → K) := by
          rw [succ_nsmul, add_comm (β : H → K), add_assoc, add_comm (n • (β : H → K))]
        rwa [hwt_add] at hlie
    intro μ w hw
    rw [dividedPower_def, Algebra.smul_def ((t.factorial : ℚ)⁻¹) _, map_mul, map_pow,
      mul_apply_eq_comp]
    have hmem := hpow_shift t μ hw
    have hscalar : ρ ((algebraMap ℚ (_root_.UniversalEnvelopingAlgebra K L)) (t.factorial : ℚ)⁻¹)
        (((ρ (_root_.UniversalEnvelopingAlgebra.ι K (x β))) ^ t) w) =
        ((algebraMap ℚ K) (t.factorial : ℚ)⁻¹) •
          (((ρ (_root_.UniversalEnvelopingAlgebra.ι K (x β))) ^ t) w) := by
      change ρ (algebraMap K (_root_.UniversalEnvelopingAlgebra K L)
        ((algebraMap ℚ K) (t.factorial : ℚ)⁻¹)) _ = _
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, one_apply_eq_self]
    rw [hscalar]
    exact (LieModule.weightSpace V (μ + t • (β : H → K))).toSubmodule.smul_mem _ hmem
  have hshift_eq_rootSum : ∀ (l : List ({α : H.root // b.IsPos α} × ℕ)) (h : H),
      negListShift b l h = negListRootSum b l h := by
    intro l
    induction l with
    | nil => intro h; simp [negListShift, negListRootSum]
    | cons p tl ih =>
      intro h
      simp [negListShift, negListRootSum, ih h, rootSystem_root_apply]
  have hrootSum_cone : ∀ l : List ({α : H.root // b.IsPos α} × ℕ),
      negListRootSum b l ∈ TauCeti.posRootCone (rootSystem H) b := by
    intro l
    induction l with
    | nil =>
      simp only [negListRootSum]
      exact AddSubmonoid.zero_mem _
    | cons p tl ih =>
      simp only [negListRootSum]
      exact AddSubmonoid.add_mem _
        (AddSubmonoid.nsmul_mem _
          (TauCeti.root_mem_posRootCone_of_mem_posRoots (rootSystem H) b p.1.2) p.2) ih
  have hrootSum_ne_zero : ∀ l : List ({α : H.root // b.IsPos α} × ℕ),
      (∃ p ∈ l, p.2 ≠ 0) → negListRootSum b l ≠ 0 := by
    intro l
    induction l with
    | nil => rintro ⟨_, hp, _⟩; cases hp
    | cons p tl ih =>
      rintro hp_ex
      by_cases hp0 : p.2 = 0
      · simp only [negListRootSum, hp0, zero_smul, zero_add]
        rcases hp_ex with ⟨q, hq_mem, hq_nz⟩
        rcases List.mem_cons.mp hq_mem with rfl | hq_tl
        · exact absurd hp0 hq_nz
        · exact ih ⟨q, hq_tl, hq_nz⟩
      · have hp_ge : 1 ≤ p.2 := Nat.one_le_iff_ne_zero.mpr hp0
        have hdecomp : p.2 • (rootSystem H).root p.1.1 + negListRootSum b tl =
            (rootSystem H).root p.1.1 +
              ((p.2 - 1) • (rootSystem H).root p.1.1 + negListRootSum b tl) := by
          have hk : p.2 = 1 + (p.2 - 1) := by omega
          conv_lhs => rw [hk, add_nsmul, one_nsmul, add_assoc]
        simp only [negListRootSum]
        rw [hdecomp]
        exact TauCeti.root_add_ne_zero_of_mem_posRoots_of_mem_posRootCone (rootSystem H) b p.1.2
          (AddSubmonoid.add_mem _
            (AddSubmonoid.nsmul_mem _
              (TauCeti.root_mem_posRootCone_of_mem_posRoots (rootSystem H) b p.1.2) _)
            (hrootSum_cone tl))
  have hnegList_wt : ∀ (l : List ({α : H.root // b.IsPos α} × ℕ)) (μ : H → K) {w : V},
      w ∈ LieModule.weightSpace V μ →
        ρ (l.map fun p => dividedPower p.2
          (_root_.UniversalEnvelopingAlgebra.ι K (x (-((p.1.1 : H.root) : Weight K H L))))).prod w ∈
          LieModule.weightSpace V (μ - negListShift b l) := by
    intro l
    induction l with
    | nil => intro μ w hw; simpa [negListShift] using hw
    | cons p tl ih =>
      intro μ w hw
      simp only [List.map_cons, List.prod_cons, map_mul, mul_apply_eq_comp]
      let β : Weight K H L := -((p.1.1 : H.root) : Weight K H L)
      have h1 := hdp_shift β p.2 (μ - negListShift b tl) (ih μ hw)
      have hwt_eq : (μ - negListShift b tl) + p.2 • (β : H → K) =
          μ - negListShift b (p :: tl) := by
        ext h
        dsimp only [β]
        rw [Weight.coe_neg]
        simp only [negListShift, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply]
        simp only [nsmul_eq_mul]
        ring
      rwa [hwt_eq] at h1
  have hfA_wt : ∀ A : Fin m → ℕ,
      ∃ μA : H → K,
        ρ (Humphreys26_4.kostantNegTerm b posOrd x A) v ∈ LieModule.weightSpace V μA ∧
          (A ≠ 0 → μA ≠ (lam : H → K)) := by
    intro A
    let l : List ({α : H.root // b.IsPos α} × ℕ) := List.ofFn fun j : Fin m => (posOrd j, A j)
    refine ⟨(lam : H → K) - negListShift b l, ?_, ?_⟩
    · have hprod_eq : Humphreys26_4.kostantNegTerm b posOrd x A =
          (l.map fun p => dividedPower p.2
            (_root_.UniversalEnvelopingAlgebra.ι K (x (-((p.1.1 : H.root) : Weight K H L))))).prod := by
        simp [Humphreys26_4.kostantNegTerm, l, List.map_ofFn, Function.comp_def]
      rw [hprod_eq]
      exact hnegList_wt l (lam : H → K) hv_wt
    · intro hA h_eq
      obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hA
      have hex : ∃ p ∈ l, p.2 ≠ 0 := ⟨(posOrd j₀, A j₀), List.mem_ofFn.mpr ⟨j₀, rfl⟩, hj₀⟩
      apply hrootSum_ne_zero l hex
      ext h
      have hpt : ((lam : H → K) - negListShift b l) h = (lam : H → K) h := congrFun h_eq h
      have hs0 : negListShift b l h = 0 := by
        simp only [Pi.sub_apply] at hpt
        linear_combination -hpt
      rw [← hshift_eq_rootSum l h, hs0]
      rfl
  have hM_neg_span : M_neg = Submodule.span ℤ
      (Set.range fun A : Fin m → ℕ => ρ (Humphreys26_4.kostantNegTerm b posOrd x A) v) := by
    apply le_antisymm
    · dsimp only [M_neg]
      rw [Subring.orbitOfRep_le_iff]
      intro u hu y hy
      obtain rfl : y = v := Set.mem_singleton_iff.mp hy
      have hu_span : u ∈ Submodule.span ℤ (Set.range (Humphreys26_4.kostantNegTerm b posOrd x)) := by
        change u ∈ (Submodule.span ℤ (Set.range (Humphreys26_4.kostantNegTerm b posOrd x)) : Set _)
        rw [(kostantTriangularSubrings_eq_span hx b posOrd baseOrd).1]
        exact hu
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hu_span
      · rintro _ ⟨A, rfl⟩; exact Submodule.subset_span ⟨A, rfl⟩
      · rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
      · intro a₁ a₂ _ _ h₁ h₂; rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ h₁ h₂
      · intro z a₁ _ h₁; rw [map_zsmul, LinearMap.smul_apply]; exact Submodule.smul_mem _ z h₁
    · rw [Submodule.span_le]
      rintro _ ⟨A, rfl⟩
      exact Subring.apply_mem_orbitOfRep _ _ _ (hfA_mem A) (Set.mem_singleton v)
  have hM_inter : M_min ⊓ (LieModule.weightSpace V (lam : H → K)).toSubmodule.restrictScalars ℤ =
      Submodule.span ℤ {v} := by
    apply le_antisymm
    · intro w hw_both
      have hwM : w ∈ Submodule.span ℤ
          (Set.range fun A : Fin m → ℕ => ρ (Humphreys26_4.kostantNegTerm b posOrd x A) v) := by
        rw [← hM_neg_span, ← hM_eq]
        exact hw_both.1
      have hw_lam : w ∈ (LieModule.weightSpace V (lam : H → K)).toSubmodule := hw_both.2
      rw [Finsupp.mem_span_range_iff_exists_finsupp] at hwM
      obtain ⟨c, hc⟩ := hwM
      rw [Finsupp.sum] at hc
      have hf0 : ρ (Humphreys26_4.kostantNegTerm b posOrd x 0) v = v := by
        have h1 : Humphreys26_4.kostantNegTerm b posOrd x 0 = 1 := by
          simp [Humphreys26_4.kostantNegTerm, List.ofFn_const]
        rw [h1, map_one, one_apply_eq_self]
      have hrem_eq :
          w - c 0 • v = ∑ A ∈ c.support.erase 0,
            c A • ρ (Humphreys26_4.kostantNegTerm b posOrd x A) v := by
        by_cases h0 : (0 : Fin m → ℕ) ∈ c.support
        · rw [← hc, ← Finset.add_sum_erase _ _ h0, hf0, add_sub_cancel_left]
        · have hc0 : c 0 = 0 := Finsupp.notMem_support_iff.mp h0
          rw [← hc, hc0, zero_smul, sub_zero, Finset.erase_eq_of_notMem h0]
      have hrem_lam : w - c 0 • v ∈ (LieModule.weightSpace V (lam : H → K)).toSubmodule := by
        refine Submodule.sub_mem _ hw_lam ?_
        rw [← Int.cast_smul_eq_zsmul K]
        exact Submodule.smul_mem _ _ hv_wt
      have hrem_other : w - c 0 • v ∈
          ⨆ (μ : H → K) (_ : μ ≠ (lam : H → K)), (LieModule.weightSpace V μ).toSubmodule := by
        rw [hrem_eq]
        refine Submodule.sum_mem _ fun A hA => ?_
        have hA_ne : A ≠ 0 := (Finset.mem_erase.mp hA).1
        obtain ⟨μA, hμA_mem, hμA_ne⟩ := hfA_wt A
        have hsmul : c A • ρ (Humphreys26_4.kostantNegTerm b posOrd x A) v ∈
            (LieModule.weightSpace V μA).toSubmodule := by
          rw [← Int.cast_smul_eq_zsmul K]
          exact Submodule.smul_mem _ _ hμA_mem
        exact Submodule.mem_iSup_of_mem μA (Submodule.mem_iSup_of_mem (hμA_ne hA_ne) hsmul)
      have hindep : iSupIndep (fun μ : H → K => (LieModule.weightSpace V μ).toSubmodule) := by
        have hgen := LieSubmodule.iSupIndep_toSubmodule.mpr (LieModule.iSupIndep_genWeightSpace K H V)
        simpa only [TauCeti.genWeightSpace_eq_weightSpace] using hgen
      have hzero : w - c 0 • v = 0 :=
        Submodule.disjoint_def.mp (hindep (lam : H → K)) _ hrem_lam hrem_other
      rw [sub_eq_zero.mp hzero, Submodule.mem_span_singleton]
      exact ⟨c 0, rfl⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨Subring.subset_orbitOfRep _ _ _ (Set.mem_singleton v), hv_wt⟩
  -- Step 5: `M_min.FG`, `span K M_min = ⊤`, and `Module.finrank ℤ M_min ≤ Module.finrank K V`
  have hM_inv : IsKostantInvariant H x M_min := fun u hu w hw =>
    Subring.apply_mem_orbitOfRep_of_mem _ _ _ hu hw
  have hM_fg : M_min.FG := by
    let NW := Fintype.card (Weight K H V)
    have hdp_nilp : ∀ (β : H.root) {a : ℕ}, NW < a →
        ρ (dividedPower a (_root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L)))) = 0 := by
      intro β a ha
      have htopW : (⨆ χ : Weight K H V, (LieModule.weightSpace V (χ : H → K)).toSubmodule) = ⊤ := by
        simpa only [← LieSubmodule.iSup_toSubmodule, LieSubmodule.toSubmodule_eq_top] using
          TauCeti.iSup_weightSpace_eq_top K H V
      refine _root_.LinearMap.ext_of_iSup_eq_top htopW fun χ w hw => ?_
      simp only [LinearMap.zero_apply]
      have hbot_ex : ∃ r : Fin (NW + 1),
          LieModule.weightSpace V ((χ : H → K) + (r : ℕ) • ((β : Weight K H L) : H → K)) = ⊥ := by
        by_contra hall_ne
        push Not at hall_ne
        let fInj : Fin (NW + 1) → Weight K H V := fun r =>
          ⟨(χ : H → K) + (r : ℕ) • ((β : Weight K H L) : H → K), by
            rw [TauCeti.genWeightSpace_eq_weightSpace]
            exact hall_ne r⟩
        have hf_inj : Function.Injective fInj := by
          intro r₁ r₂ hr
          have hval : (χ : H → K) + (r₁ : ℕ) • ((β : Weight K H L) : H → K) =
              (χ : H → K) + (r₂ : ℕ) • ((β : Weight K H L) : H → K) :=
            congrArg (fun η : Weight K H V => (η : H → K)) hr
          have hdiff : (((r₁ : ℕ) : K) - ((r₂ : ℕ) : K)) • ((β : Weight K H L) : H → K) = 0 := by
            ext h
            have hpt := congrFun hval h
            simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
              sub_smul, Nat.cast_smul_eq_nsmul] at hpt ⊢
            linear_combination hpt
          rcases smul_eq_zero.mp hdiff with hsc | hβ0
          · exact Fin.ext (Nat.cast_injective (R := K) (sub_eq_zero.mp hsc))
          · exact absurd hβ0 (H.isNonZero_coe_root β)
        have hcard_le := Fintype.card_le_of_injective fInj hf_inj
        simp only [Fintype.card_fin, NW] at hcard_le
        omega
      obtain ⟨r, hr_bot⟩ := hbot_ex
      have hr_zero : ρ (dividedPower (r : ℕ)
          (_root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L)))) w = 0 := by
        have hmem := hdp_shift (β : Weight K H L) (r : ℕ) (χ : H → K) hw
        rw [hr_bot] at hmem
        exact hmem
      have hpow_r : ((ρ (_root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L)))) ^ (r : ℕ)) w =
          0 := by
        rw [dividedPower_def, Algebra.smul_def, map_mul, map_pow, mul_apply_eq_comp] at hr_zero
        have hsc : ((algebraMap ℚ K) ((r : ℕ).factorial : ℚ)⁻¹) •
            (((ρ (_root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L)))) ^ (r : ℕ)) w) = 0 := by
          have h1 : ρ ((algebraMap ℚ (_root_.UniversalEnvelopingAlgebra K L))
              ((r : ℕ).factorial : ℚ)⁻¹) =
              algebraMap K (Module.End K V) ((algebraMap ℚ K) ((r : ℕ).factorial : ℚ)⁻¹) :=
            AlgHom.commutes ρ _
          rwa [h1, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, one_apply_eq_self] at hr_zero
        have hne0 : (algebraMap ℚ K) ((r : ℕ).factorial : ℚ)⁻¹ ≠ 0 := by
          rw [map_inv₀, map_natCast]
          exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
        exact (smul_eq_zero.mp hsc).resolve_left hne0
      have hra : (r : ℕ) ≤ a := le_trans (Nat.le_of_lt_succ r.isLt) (le_of_lt ha)
      have hpow_a : ((ρ (_root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L)))) ^ a) w = 0 := by
        have hsplit : a = (a - (r : ℕ)) + (r : ℕ) := by omega
        rw [hsplit, pow_add, mul_apply_eq_comp, hpow_r, map_zero]
      rw [dividedPower_def, Algebra.smul_def, map_mul, map_pow, mul_apply_eq_comp, hpow_a, map_zero]
    have hfA_zero_of_gt : ∀ A : Fin m → ℕ, (∃ j : Fin m, NW < A j) →
        ρ (Humphreys26_4.kostantNegTerm b posOrd x A) v = 0 := by
      intro A ⟨j₀, hj₀⟩
      have hlist_zero : ∀ l : List ({α : H.root // b.IsPos α} × ℕ),
          (∃ p ∈ l, NW < p.2) →
            ρ (l.map fun p => dividedPower p.2
              (_root_.UniversalEnvelopingAlgebra.ι K (x (-((p.1.1 : H.root) : Weight K H L))))).prod = 0 := by
        intro l
        induction l with
        | nil => rintro ⟨_, hp, _⟩; cases hp
        | cons p tl ih =>
          rintro ⟨q, hq_mem, hq_gt⟩
          simp only [List.map_cons, List.prod_cons, map_mul]
          rcases List.mem_cons.mp hq_mem with rfl | hq_tl
          · have hneg_root : -((q.1.1 : H.root) : Weight K H L) =
                ((-(q.1.1 : H.root) : H.root) : Weight K H L) := IsKilling.val_neg_root.symm
            rw [hneg_root, hdp_nilp (-(q.1.1 : H.root)) hq_gt, zero_mul]
          · rw [ih ⟨q, hq_tl, hq_gt⟩, mul_zero]
      let l : List ({α : H.root // b.IsPos α} × ℕ) := List.ofFn fun j : Fin m => (posOrd j, A j)
      have hprod_eq : Humphreys26_4.kostantNegTerm b posOrd x A =
          (l.map fun p => dividedPower p.2
            (_root_.UniversalEnvelopingAlgebra.ι K (x (-((p.1.1 : H.root) : Weight K H L))))).prod := by
        simp [Humphreys26_4.kostantNegTerm, l, List.map_ofFn, Function.comp_def]
      rw [hprod_eq, hlist_zero l ⟨(posOrd j₀, A j₀), List.mem_ofFn.mpr ⟨j₀, rfl⟩, hj₀⟩,
        LinearMap.zero_apply]
    let finSetGen : Set V :=
      insert 0 (Set.range fun A : Fin m → Fin (NW + 1) =>
        ρ (Humphreys26_4.kostantNegTerm b posOrd x (fun j => (A j : ℕ))) v)
    have hfin : finSetGen.Finite :=
      Set.Finite.insert 0 (Set.finite_range _)
    have hspan_fin : M_min = Submodule.span ℤ finSetGen := by
      rw [hM_eq, hM_neg_span]
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨A, rfl⟩
        dsimp only
        by_cases hgt : ∃ j : Fin m, NW < A j
        · rw [hfA_zero_of_gt A hgt]
          exact Submodule.zero_mem _
        · push Not at hgt
          let A' : Fin m → Fin (NW + 1) := fun j => ⟨A j, Nat.lt_succ_of_le (hgt j)⟩
          exact Submodule.subset_span (Or.inr ⟨A', rfl⟩)
      · rw [Submodule.span_le]
        rintro y (rfl | ⟨A', rfl⟩)
        · exact Submodule.zero_mem _
        · exact Submodule.subset_span ⟨fun j => (A' j : ℕ), rfl⟩
    rw [hspan_fin]
    exact Submodule.fg_span hfin
  have hspan_kostant_top :
      Submodule.span K (Humphreys26_4.kostantSubring H x :
        Set (_root_.UniversalEnvelopingAlgebra K L)) = ⊤ := by
    rw [← top_le_iff, ← (Humphreys26_4.kostantMonomial_basis_over_field hx b posOrd baseOrd).2]
    refine Submodule.span_mono ?_
    rintro _ ⟨p, rfl⟩
    exact Humphreys26_4.GapA.kostantMonomial_mem_rootSubring hx b posOrd baseOrd p
  have hM_span_top : Submodule.span K (M_min : Set V) = ⊤ := by
    have hlie_top : LieSubmodule.lieSpan K L {v} = ⊤ := by
      have hne_bot : LieSubmodule.lieSpan K L {v} ≠ ⊥ := by
        intro hbot
        have hv_mem : v ∈ LieSubmodule.lieSpan K L {v} :=
          LieSubmodule.subset_lieSpan (Set.mem_singleton v)
        rw [hbot] at hv_mem
        exact hv.ne_zero hv_mem
      exact eq_top_iff.mpr ((IsSimpleOrder.eq_bot_or_eq_top _).resolve_left hne_bot).ge
    dsimp only [M_min, minAdmissibleLattice]
    rw [Subring.span_orbitOfRep_eq_span (R := K) _ ρ {v} hspan_kostant_top, eq_top_iff]
    intro y _
    obtain ⟨u, hu⟩ := TauCeti.UniversalEnvelopingAlgebra.exists_representation_apply_eq_of_lieSpan_eq_top
      hlie_top y
    exact Submodule.subset_span ⟨u, v, Set.mem_singleton v, hu⟩
  have hM_rank_le : Module.finrank ℤ M_min ≤ Module.finrank K V :=
    finrank_le_of_kostantInvariant_inter_le_span hx b hv M_min hM_fg hM_inv hM_inter.le
  have hM_full : IsFullZLattice K M_min :=
    (isFullZLattice_iff_fg_and_span_eq_top_and_finrank_le M_min).mpr
      ⟨hM_fg, hM_span_top, hM_rank_le⟩
  exact ⟨hM_eq, ⟨hM_full, hM_inv⟩, hM_inter⟩

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
  have : FiniteDimensional K (TauCeti.irreducibleQuotient b lam) :=
    TauCeti.finiteDimensional_irreducibleQuotient_of_isDominantIntegral hlam
  exact isAdmissibleLattice_minAdmissibleLattice hx b
    (TauCeti.isHighestWeightVector_irreducibleQuotientGenerator b lam)

/-- **Humphreys, Theorem 27.1(b) (p. 158, verbatim): Existence of an admissible lattice.**
Every finite-dimensional `L`-module `V` contains an admissible lattice invariant under
`𝔘_ℤ = Humphreys26_4.kostantSubring H x`. -/
theorem exists_isAdmissibleLattice
    [FiniteDimensional K V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x) :
    ∃ M : Submodule ℤ V, IsAdmissibleLattice H x M := by
  classical
  obtain ⟨k, N, hInt, hIrr⟩ := TauCeti.exists_isInternal_isIrreducible_of_isKilling K L V
  obtain ⟨b⟩ := (rootSystem H).nonempty_base
  have hex_summand : ∀ i : Fin k, ∃ M_i : Submodule ℤ (N i), IsAdmissibleLattice H x M_i := by
    intro i
    have : LieModule.IsIrreducible K L (N i) := hIrr i
    have : Nontrivial (N i) := LieModule.nontrivial_of_isIrreducible K L (N i)
    obtain ⟨lam_i, v_i, hv_i⟩ := exists_isHighestWeightVector_split (N i) b
    exact ⟨minAdmissibleLattice H x v_i, (isAdmissibleLattice_minAdmissibleLattice hx b hv_i).2.1⟩
  choose M_i hM_i using hex_summand
  have hbasis_i : ∀ i : Fin k,
      ∃ b_i : Module.Basis (Fin (Module.finrank K (N i))) K (N i),
        M_i i = Submodule.span ℤ (Set.range b_i) := fun i => (hM_i i).1
  choose b_i hb_i using hbasis_i
  let f_i : ∀ i : Fin k, (N i) →ₗ[ℤ] V := fun i => (N i).toSubmodule.subtype.restrictScalars ℤ
  let M : Submodule ℤ V := ⨆ i : Fin k, Submodule.map (f_i i) (M_i i)
  refine ⟨M, ?_, ?_⟩
  · let bCol : Module.Basis (Σ i : Fin k, Fin (Module.finrank K (N i))) K V :=
      hInt.collectedBasis b_i
    have hcard : Fintype.card (Σ i : Fin k, Fin (Module.finrank K (N i))) = Module.finrank K V :=
      (Module.finrank_eq_card_basis bCol).symm
    let eIdx : (Σ i : Fin k, Fin (Module.finrank K (N i))) ≃ Fin (Module.finrank K V) :=
      Fintype.equivOfCardEq (by simp [hcard])
    let bV : Module.Basis (Fin (Module.finrank K V)) K V := bCol.reindex eIdx
    refine ⟨bV, ?_⟩
    have hrange_bV : Set.range bV = ⋃ i : Fin k, (f_i i) '' Set.range (b_i i) := by
      ext w
      simp only [bV, Module.Basis.coe_reindex, Set.mem_range, Function.comp_apply,
        Set.mem_iUnion, Set.mem_image]
      constructor
      · rintro ⟨idx, rfl⟩
        obtain ⟨i, j⟩ := eIdx.symm idx
        refine ⟨i, b_i i j, ⟨j, rfl⟩, ?_⟩
        simp only [bCol, f_i, DirectSum.IsInternal.collectedBasis_coe,
          LinearMap.coe_restrictScalars]
        rfl
      · rintro ⟨i, _, ⟨j, rfl⟩, rfl⟩
        refine ⟨eIdx ⟨i, j⟩, ?_⟩
        simp only [Equiv.symm_apply_apply, bCol, f_i, DirectSum.IsInternal.collectedBasis_coe,
          LinearMap.coe_restrictScalars]
        rfl
    rw [hrange_bV, Submodule.span_iUnion]
    refine iSup_congr fun i => ?_
    rw [← Submodule.map_span, ← hb_i i]
  · intro u hu w hw
    let ρV := TauCeti.UniversalEnvelopingAlgebra.representation K L V
    have hle : M ≤ M.comap (ρV u).toAddMonoidHom.toIntLinearMap := by
      refine iSup_le fun i => ?_
      rw [Submodule.map_le_iff_le_comap]
      intro y hy
      simp only [Submodule.mem_comap, AddMonoidHom.coe_toIntLinearMap,
        LinearMap.toAddMonoidHom_coe]
      have hcomm : ρV u (f_i i y) = f_i i
          (TauCeti.UniversalEnvelopingAlgebra.representation K L (N i) u y) :=
        (TauCeti.UniversalEnvelopingAlgebra.map_representation K L (N i) V (N i).incl u y).symm
      rw [hcomm]
      exact Submodule.mem_iSup_of_mem i ⟨_, (hM_i i).2 u hu y hy, rfl⟩
    exact hle hw

/-- **Unconditional Chevalley-free corollary of Theorem 27.1(b) (combining 25.2 + 26.4 + 27.1):**
For any finite-dimensional split Killing Lie algebra `(L, H)` over a characteristic-zero field
`K` and any finite-dimensional `L`-module `V`, there exist a Chevalley system `(ω, x)` of
`(L, H)` and an admissible lattice `M` in `V` invariant under `Humphreys26_4.kostantSubring H x`. -/
theorem exists_chevalleySystem_and_admissibleLattice [FiniteDimensional K V] :
    ∃ (ω : L ≃ₗ⁅K⁆ L) (x : Weight K H L → L),
      TauCeti.IsChevalleySystem ω x ∧
        ∃ M : Submodule ℤ V, IsAdmissibleLattice H x M := by
  obtain ⟨ω, x, hx⟩ := Humphreys25_2.exists_isChevalleySystem (K := K) (L := L) (H := H)
  exact ⟨ω, x, hx, exists_isAdmissibleLattice hx⟩

end AdmissibleLattices

end Humphreys27_1
