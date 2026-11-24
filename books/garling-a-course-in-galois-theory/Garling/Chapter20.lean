import Garling.Chapter01
import Garling.Chapter03
import Garling.Chapter04
import Garling.Chapter05
import Garling.Chapter07
import Garling.Chapter10
import Garling.Chapter11
import Garling.Chapter12
import Garling.Chapter14
import Garling.Chapter15
import Garling.Chapter16
import Garling.Chapter17
import Garling.Chapter19
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.Tactic.NormNum.Prime

/-!
# Chapter 20: The calculation of Galois groups

Formalization of Chapter 20 (*The calculation of Galois groups*, printed pp. 155–162 / PDF
pp. 163–170 — the final chapter of the book) of D. J. H. Garling, *A Course in Galois Theory*
(Cambridge University Press, 1986).
-/

open scoped Polynomial IntermediateField Pointwise
open Garling.Chapter01 Garling.Chapter03 Garling.Chapter04 Garling.Chapter05
  Garling.Chapter07 Garling.Chapter10 Garling.Chapter11 Garling.Chapter12
  Garling.Chapter14 Garling.Chapter15 Garling.Chapter16 Garling.Chapter17
  Garling.Chapter19

namespace Garling.Chapter20

universe u v w

/-! ## §20.1 A procedure for determining the Galois group of a polynomial (pp. 155–158) -/

/-! ### Inline prose definitions: `σ_x`, `σ_t`, universal polynomial `P`, and Kronecker resolvent `F` -/

/-- Ring automorphism `σ_x` of `R[x₁, …, xₙ]` sending `x_i ↦ x_{σ(i)}` (§20.1, printed p. 155). -/
noncomputable def permXRingEquiv (R : Type*) [CommRing R] {n : ℕ} (σ : SigmaN n) :
    MvPolynomial (Fin n) R ≃+* MvPolynomial (Fin n) R :=
  (MvPolynomial.renameEquiv R σ).toRingEquiv

@[simp]
theorem permXRingEquiv_X (R : Type*) [CommRing R] {n : ℕ} (σ : SigmaN n) (i : Fin n) :
    permXRingEquiv R σ (MvPolynomial.X i) = MvPolynomial.X (σ i) := by
  simp [permXRingEquiv]

@[simp]
theorem permXRingEquiv_C (R : Type*) [CommRing R] {n : ℕ} (σ : SigmaN n) (r : R) :
    permXRingEquiv R σ (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [permXRingEquiv]

theorem permXRingEquiv_mul (R : Type*) [CommRing R] {n : ℕ} (σ τ : SigmaN n)
    (p : MvPolynomial (Fin n) R) :
    permXRingEquiv R (σ * τ) p = permXRingEquiv R σ (permXRingEquiv R τ p) := by
  change MvPolynomial.rename (⇑σ ∘ ⇑τ) p = MvPolynomial.rename σ (MvPolynomial.rename τ p)
  exact (MvPolynomial.rename_rename τ σ p).symm

theorem permXRingEquiv_one (R : Type*) [CommRing R] {n : ℕ} (p : MvPolynomial (Fin n) R) :
    permXRingEquiv R 1 p = p := by
  change MvPolynomial.rename id p = p
  exact AlgHom.congr_fun MvPolynomial.rename_id p

/-- Ring automorphism `σ_x` extended coefficientwise to `(R[x₁, …, xₙ])[y]` (fixing `y`)
(§20.1, printed pp. 155–156). -/
noncomputable def permXPolyEquiv (R : Type*) [CommRing R] {n : ℕ} (σ : SigmaN n) :
    (MvPolynomial (Fin n) R)[X] ≃+* (MvPolynomial (Fin n) R)[X] :=
  Polynomial.mapEquiv (permXRingEquiv R σ)

@[simp]
theorem permXPolyEquiv_X (R : Type*) [CommRing R] {n : ℕ} (σ : SigmaN n) :
    permXPolyEquiv R σ Polynomial.X = Polynomial.X := by
  simp [permXPolyEquiv]

@[simp]
theorem permXPolyEquiv_C (R : Type*) [CommRing R] {n : ℕ} (σ : SigmaN n)
    (p : MvPolynomial (Fin n) R) :
    permXPolyEquiv R σ (Polynomial.C p) = Polynomial.C (permXRingEquiv R σ p) := by
  simp [permXPolyEquiv]

theorem permXPolyEquiv_mul (R : Type*) [CommRing R] {n : ℕ} (σ τ : SigmaN n)
    (P : (MvPolynomial (Fin n) R)[X]) :
    permXPolyEquiv R (σ * τ) P = permXPolyEquiv R σ (permXPolyEquiv R τ P) := by
  ext k
  simp [permXPolyEquiv, permXRingEquiv_mul]

theorem permXPolyEquiv_one (R : Type*) [CommRing R] {n : ℕ}
    (P : (MvPolynomial (Fin n) R)[X]) :
    permXPolyEquiv R 1 P = P := by
  ext k
  simp [permXPolyEquiv, permXRingEquiv_one]

/-- Identification `R[y, x₁, …, xₙ] ≃+* (R[x₁, …, xₙ])[y]` via `MvPolynomial.optionEquivLeft`
(`none` = `y`, `some i` = `x_i`). -/
noncomputable def kroneckerRingEquiv (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Option (Fin n)) R ≃+* (MvPolynomial (Fin n) R)[X] :=
  (MvPolynomial.optionEquivLeft R (Fin n)).toRingEquiv

/-- Garling's universal polynomial (§20.1, printed p. 155):
`P = ∏_{σ ∈ Σ_n} (y - (t_1 x_{σ(1)} + ⋯ + t_n x_{σ(n)})) ∈ ((R[t₁, …, tₙ])[x₁, …, xₙ])[y]`. -/
noncomputable def universalKroneckerPoly (R : Type*) [CommRing R] (n : ℕ) :
    (MvPolynomial (Fin n) (MvPolynomial (Fin n) R))[X] :=
  ∏ σ : SigmaN n,
    (Polynomial.X - Polynomial.C (∑ i : Fin n,
      MvPolynomial.C (MvPolynomial.X i) * MvPolynomial.X (σ i)))

/-- Equivalence of the two displayed products for `P` on printed p. 155:
`∏_{σ ∈ Σ_n} (y - ∑_i t_i x_{σ(i)}) = ∏_{σ ∈ Σ_n} (y - ∑_i t_{σ(i)} x_i)`. -/
theorem universalKroneckerPoly_eq_permT (R : Type*) [CommRing R] (n : ℕ) :
    universalKroneckerPoly R n =
      ∏ σ : SigmaN n,
        (Polynomial.X - Polynomial.C (∑ i : Fin n,
          MvPolynomial.C (MvPolynomial.X (σ i)) * MvPolynomial.X i)) := by
  unfold universalKroneckerPoly
  refine Fintype.prod_equiv (Equiv.inv (SigmaN n)) _ _ fun σ => ?_
  congr 2
  refine Fintype.sum_equiv σ _ _ fun i => ?_
  simp

/-- Symmetry of every `(j, m)`-coefficient `f_m ∈ R[t₁, …, tₙ]` of `P` under `σ_t` and its
representation `f_m = g_m(s₁, …, sₙ)` via **Theorem 19.4** (§20.1, printed pp. 155–156). -/
theorem universalKroneckerPoly_coeff_symmetric (R : Type*) [CommRing R] [IsDomain R] (n : ℕ)
    (j : ℕ) (m : Fin n →₀ ℕ) :
    let f_m : MvPolynomial (Fin n) R :=
      ((universalKroneckerPoly R n).coeff j).coeff m
    IsGarlingSymmetricPoly f_m ∧
    ∃! g_m : MvPolynomial (Fin n) R, elemSymmSubst R n g_m = f_m := by
  intro f_m
  have hsym : IsGarlingSymmetricPoly f_m := by
    intro τ
    let φT : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R :=
      (MvPolynomial.rename τ).toRingHom
    let φX : MvPolynomial (Fin n) (MvPolynomial (Fin n) R) →+*
        MvPolynomial (Fin n) (MvPolynomial (Fin n) R) := MvPolynomial.map φT
    let g : SigmaN n → (MvPolynomial (Fin n) (MvPolynomial (Fin n) R))[X] :=
      fun σ => Polynomial.X - Polynomial.C (∑ i : Fin n,
        MvPolynomial.C (MvPolynomial.X (σ i)) * MvPolynomial.X i)
    have hterm : ∀ σ : SigmaN n, Polynomial.map φX (g σ) = g (τ * σ) := by
      intro σ
      dsimp only [g]
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      congr 2
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
      congr 2
      exact MvPolynomial.rename_X τ (σ i)
    have hP_inv : (universalKroneckerPoly R n).map φX = universalKroneckerPoly R n := by
      rw [universalKroneckerPoly_eq_permT]
      change Polynomial.map φX (∏ σ : SigmaN n, g σ) = ∏ σ : SigmaN n, g σ
      rw [Polynomial.map_prod]
      exact Finset.prod_bij (fun σ _ => τ * σ)
        (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => mul_left_cancel h)
        (fun σ _ => ⟨τ⁻¹ * σ, Finset.mem_univ _, mul_inv_cancel_left τ σ⟩)
        (fun σ _ => hterm σ)
    have hcoeff_j : φX ((universalKroneckerPoly R n).coeff j) =
        (universalKroneckerPoly R n).coeff j := by
      rw [← Polynomial.coeff_map, hP_inv]
    have hcoeff_m := congrArg (fun p : MvPolynomial (Fin n) (MvPolynomial (Fin n) R) => p.coeff m)
      hcoeff_j
    have hmap_m : (φX ((universalKroneckerPoly R n).coeff j)).coeff m = φT f_m :=
      MvPolynomial.coeff_map φT ((universalKroneckerPoly R n).coeff j) m
    exact hmap_m.symm.trans hcoeff_m
  exact ⟨hsym, theorem_19_4_domain hsym⟩

/-- Direct evaluation of the unique symmetric preimage `g_m(a₁, …, aₙ)` for each `(j, m)`-coefficient
of `universalKroneckerPoly R n` (§20.1, printed p. 156). -/
noncomputable def kroneckerSymmCoeff {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (a : Fin n → R) (j : ℕ) (m : Fin n →₀ ℕ) : R :=
  MvPolynomial.eval a ((universalKroneckerPoly_coeff_symmetric R n j m).2.choose)

/-- For any root tuple `α : Fin n → L`, the linear form `β = α₁ x₁ + ⋯ + αₙ xₙ ∈ L[x₁, …, xₙ]`
(§20.1, printed p. 156). -/
noncomputable def kroneckerBeta {L : Type*} [CommRing L] {n : ℕ} (α : Fin n → L) :
    MvPolynomial (Fin n) L :=
  ∑ i : Fin n, MvPolynomial.C (α i) * MvPolynomial.X i

/-- Root-permutation form `σ_α(β) = α_{σ(1)} x₁ + ⋯ + α_{σ(n)} xₙ` (§20.1, printed p. 156). -/
noncomputable def kroneckerPermAlphaBeta {L : Type*} [CommRing L] {n : ℕ}
    (α : Fin n → L) (σ : SigmaN n) : MvPolynomial (Fin n) L :=
  ∑ i : Fin n, MvPolynomial.C (α (σ i)) * MvPolynomial.X i

/-- Printed p. 156 identity `σ_α(β) = σ_x^{-1}(β)`. -/
theorem kroneckerPermAlphaBeta_eq_inv_permX {L : Type*} [CommRing L] {n : ℕ}
    (α : Fin n → L) (σ : SigmaN n) :
    kroneckerPermAlphaBeta α σ = permXRingEquiv L σ⁻¹ (kroneckerBeta α) := by
  unfold kroneckerPermAlphaBeta kroneckerBeta
  rw [map_sum]
  refine Fintype.sum_equiv σ _ _ fun i => ?_
  simp

/-- The Kronecker resolvent over `L`, `F_L = ∏_{σ ∈ Σ_n} (y - σ_x(β)) ∈ (L[x₁, …, xₙ])[y]`
(§20.1, printed p. 156). -/
noncomputable def kroneckerResolventOver {L : Type*} [CommRing L] {n : ℕ} (α : Fin n → L) :
    (MvPolynomial (Fin n) L)[X] :=
  ∏ σ : SigmaN n, (Polynomial.X - Polynomial.C (permXRingEquiv L σ (kroneckerBeta α)))

/-- Printed p. 156 equality `∏_{σ ∈ Σ_n} (y - σ_x(β)) = ∏_{σ ∈ Σ_n} (y - σ_α(β))`. -/
theorem kroneckerResolventOver_eq_permAlpha {L : Type*} [CommRing L] {n : ℕ} (α : Fin n → L) :
    kroneckerResolventOver α =
      ∏ σ : SigmaN n, (Polynomial.X - Polynomial.C (kroneckerPermAlphaBeta α σ)) := by
  unfold kroneckerResolventOver
  refine Fintype.prod_equiv (Equiv.inv (SigmaN n)) _ _ fun σ => ?_
  rw [Equiv.inv_apply, kroneckerPermAlphaBeta_eq_inv_permX, inv_inv]

theorem kroneckerResolventOver_monic {L : Type*} [CommRing L] {n : ℕ} (α : Fin n → L) :
    (kroneckerResolventOver α).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem kroneckerResolventOver_natDegree {L : Type*} [CommRing L] [Nontrivial L] {n : ℕ}
    (α : Fin n → L) :
    (kroneckerResolventOver α).natDegree = n.factorial := by
  unfold kroneckerResolventOver
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)]
  simp [Fintype.card_perm, Fintype.card_fin]

/-- Printed p. 156 distinctness: if `α₁, …, αₙ` are distinct, then `σ_x(β) ≠ τ_x(β)` for `σ ≠ τ`. -/
theorem kroneckerBeta_permX_injective {L : Type*} [CommRing L] {n : ℕ} {α : Fin n → L}
    (hinj : Function.Injective α) :
    Function.Injective (fun σ : SigmaN n => permXRingEquiv L σ (kroneckerBeta α)) := by
  intro σ τ hστ
  refine Equiv.ext fun i => ?_
  have hcoeff := congrArg (fun p : MvPolynomial (Fin n) L => p.coeff (Finsupp.single (σ i) 1)) hστ
  have hval : ∀ (ρ : SigmaN n) (k : Fin n),
      (permXRingEquiv L ρ (kroneckerBeta α)).coeff (Finsupp.single k 1) = α (ρ⁻¹ k) := by
    intro ρ k
    unfold kroneckerBeta
    rw [map_sum, MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single (ρ⁻¹ k)]
    · rw [map_mul, permXRingEquiv_C, permXRingEquiv_X,
        show ρ (ρ⁻¹ k) = k from ρ.apply_symm_apply k]
      simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
    · intro b _ hb
      rw [map_mul, permXRingEquiv_C, permXRingEquiv_X, MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_X]
      have hne : Finsupp.single (ρ b) 1 ≠ Finsupp.single k 1 := by
        intro heq
        have h1 : ρ b = k := by
          have hval_eq := congrArg (fun f : Fin n →₀ ℕ => f (ρ b)) heq
          simp only [Finsupp.single_eq_same] at hval_eq
          by_contra hne'
          have h0 : (Finsupp.single k (1 : ℕ)) (ρ b) = 0 :=
            Finsupp.single_eq_of_ne hne'
          rw [h0] at hval_eq
          exact one_ne_zero hval_eq
        exact hb (by rw [← h1]; exact (ρ.symm_apply_apply b).symm)
      simp [hne]
    · intro hmem; exact (hmem (Finset.mem_univ _)).elim
  rw [hval σ (σ i), hval τ (σ i), show σ⁻¹ (σ i) = i from σ.symm_apply_apply i] at hcoeff
  have hi_eq : i = τ⁻¹ (σ i) := hinj hcoeff
  have hτ_eq : τ i = σ i := by
    have := congrArg τ hi_eq
    rwa [show τ (τ⁻¹ (σ i)) = σ i from τ.apply_symm_apply (σ i)] at this
  exact hτ_eq.symm

/-- Coefficient-wise map `(R[x₁, …, xₙ])[y] →+* (S[x₁, …, xₙ])[y]` induced by `φ : R →+* S`. -/
noncomputable def kroneckerMapHom {R S : Type*} [CommRing R] [CommRing S] (n : ℕ)
    (φ : R →+* S) : (MvPolynomial (Fin n) R)[X] →+* (MvPolynomial (Fin n) S)[X] :=
  Polynomial.mapRingHom (MvPolynomial.map φ)

theorem kroneckerMapHom_injective {R S : Type*} [CommRing R] [CommRing S] (n : ℕ)
    {φ : R →+* S} (hφ : Function.Injective φ) :
    Function.Injective (kroneckerMapHom n φ) :=
  Polynomial.map_injective _ (MvPolynomial.map_injective φ hφ)

theorem kroneckerMapHom_comm_permX {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (σ : SigmaN n) (P : (MvPolynomial (Fin n) R)[X]) :
    kroneckerMapHom n φ (permXPolyEquiv R σ P) = permXPolyEquiv S σ (kroneckerMapHom n φ P) := by
  ext k m
  simp only [kroneckerMapHom, permXPolyEquiv, Polynomial.coe_mapRingHom, Polynomial.mapEquiv_apply,
    Polynomial.coeff_map]
  change (MvPolynomial.map φ (MvPolynomial.rename σ (P.coeff k))).coeff m =
    (MvPolynomial.rename σ (MvPolynomial.map φ (P.coeff k))).coeff m
  rw [MvPolynomial.map_rename]

/-- Evaluation of `universalKroneckerPoly R n` at `t_i ↦ α_i` produces `kroneckerResolventOver α`. -/
theorem universalKroneckerPoly_eval_eq_resolvent {R L : Type*} [CommRing R] [CommRing L]
    (φ : R →+* L) {n : ℕ} (α : Fin n → L) :
    (universalKroneckerPoly R n).map (MvPolynomial.map (MvPolynomial.eval₂Hom φ α)) =
      kroneckerResolventOver α := by
  unfold universalKroneckerPoly kroneckerResolventOver
  rw [Polynomial.map_prod]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  congr 2
  rw [kroneckerBeta, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, permXRingEquiv_C,
    permXRingEquiv_X, MvPolynomial.eval₂Hom_X']

/-- Descent of `kroneckerResolventOver α` to `(R[x₁, …, xₙ])[y]` via **Theorem 19.4** (holds over
ANY integral domain `R`, including both `R = K` for `Theorem 20.1` and `R = ℤ` for `Theorem 20.2`!). -/
theorem exists_unique_kroneckerResolvent_of_domain {R L : Type*} [CommRing R] [IsDomain R]
    [CommRing L] [IsDomain L] (φ : R →+* L) (hφ : Function.Injective φ) {n : ℕ}
    {a : Fin n → R} {α : Fin n → L}
    (hroots : (garlingGenericPoly a).map φ = generalRootsPoly α) :
    ∃! F : (MvPolynomial (Fin n) R)[X],
      kroneckerMapHom n φ F = kroneckerResolventOver α := by
  classical
  have hs_eq : ∀ k : Fin n,
      MvPolynomial.eval₂Hom φ α (elemSymmPoly R n k) = φ (a k) := by
    intro k
    have hcoeff := congrArg (fun p : L[X] => p.coeff (n - 1 - k.1)) hroots
    have hgen_map : (garlingGenericPoly a).map φ = garlingGenericPoly (fun i => φ (a i)) := by
      unfold garlingGenericPoly
      simp [Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_neg, Polynomial.map_one]
    have hroot_gen : generalRootsPoly α =
        garlingGenericPoly (fun i => MvPolynomial.eval α (elemSymmPoly L n i)) :=
      generalRootsPoly_eq_garlingGenericPoly α
    have hesymm_map : ∀ i : Fin n,
        MvPolynomial.eval₂Hom φ α (elemSymmPoly R n i) =
          MvPolynomial.eval α (elemSymmPoly L n i) := by
      intro i
      unfold elemSymmPoly
      change MvPolynomial.eval₂ φ α (MvPolynomial.esymm (Fin n) R (i.1 + 1)) = _
      rw [← MvPolynomial.eval_map, MvPolynomial.map_esymm]
    rw [hgen_map, hroot_gen, garlingGenericPoly_coeff, garlingGenericPoly_coeff] at hcoeff
    have hunit : (-1 : L) ^ (k.1 + 1) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    rw [hesymm_map]
    exact (mul_left_cancel₀ hunit hcoeff).symm
  let coeffPoly : ℕ → MvPolynomial (Fin n) R := fun j =>
    ∑ m ∈ ((universalKroneckerPoly R n).coeff j).support,
      MvPolynomial.monomial m (kroneckerSymmCoeff a j m)
  let F : (MvPolynomial (Fin n) R)[X] :=
    ∑ j ∈ (universalKroneckerPoly R n).support, Polynomial.monomial j (coeffPoly j)
  have hF_map : kroneckerMapHom n φ F = kroneckerResolventOver α := by
    rw [← universalKroneckerPoly_eval_eq_resolvent φ α]
    ext j m
    simp only [kroneckerMapHom, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
      MvPolynomial.coeff_map, F, coeffPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      Finset.sum_ite_eq', Polynomial.mem_support_iff]
    split_ifs with hj
    · rw [MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq', MvPolynomial.mem_support_iff]
      split_ifs with hm
      · have hg := (universalKroneckerPoly_coeff_symmetric R n j m).2.choose_spec.1
        unfold kroneckerSymmCoeff
        have hcomp :
            (MvPolynomial.eval₂Hom φ α).comp (elemSymmSubst R n).toRingHom =
              φ.comp (MvPolynomial.eval a) := by
          apply MvPolynomial.ringHom_ext
          · intro r; simp [elemSymmSubst]
          · intro k
            simp only [RingHom.comp_apply, elemSymmSubst, MvPolynomial.eval_X]
            change MvPolynomial.eval₂Hom φ α (MvPolynomial.aeval (elemSymmPoly R n) (MvPolynomial.X k)) = φ (a k)
            rw [MvPolynomial.aeval_X]
            exact hs_eq k
        have h1 := RingHom.congr_fun hcomp
          ((universalKroneckerPoly_coeff_symmetric R n j m).2.choose)
        change MvPolynomial.eval₂Hom φ α
          (elemSymmSubst R n (universalKroneckerPoly_coeff_symmetric R n j m).2.choose) =
          φ (MvPolynomial.eval a (universalKroneckerPoly_coeff_symmetric R n j m).2.choose) at h1
        rw [hg] at h1
        exact h1.symm
      · push Not at hm
        rw [hm, map_zero, map_zero]
    · push Not at hj
      rw [hj]
      simp
  exact ⟨F, hF_map, fun F' hF' => kroneckerMapHom_injective n hφ (hF'.trans hF_map.symm)⟩

/-- Helper: every monic polynomial of degree `n` equals `garlingGenericPoly a` for the tuple
`a_k = (-1)^{k+1} f.coeff (n - 1 - k)`. -/
def monicGenericCoeffs {R : Type*} [CommRing R] (f : R[X]) (n : ℕ) : Fin n → R :=
  fun k => (-1 : R) ^ (k.1 + 1) * f.coeff (n - 1 - k.1)

theorem garlingGenericPoly_monicGenericCoeffs {R : Type*} [CommRing R] {f : R[X]} {n : ℕ}
    (hmon : f.Monic) (hdeg : f.natDegree = n) :
    garlingGenericPoly (monicGenericCoeffs f n) = f := by
  ext m
  unfold garlingGenericPoly monicGenericCoeffs
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff]
  by_cases hmn : m = n
  · subst hmn
    rw [ite_eq_left_iff.mpr (fun h => absurd rfl h), Finset.sum_eq_zero]
    · rw [add_zero, ← hdeg, hmon.coeff_natDegree]
    · intro k _
      rw [Polynomial.coeff_C_mul_X_pow, ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hmn), zero_add]
    by_cases hlt : m < n
    · let k₀ : Fin n := ⟨n - 1 - m, by omega⟩
      rw [Finset.sum_eq_single k₀]
      · have hidx : m = n - 1 - k₀.1 := by dsimp [k₀]; omega
        rw [Polynomial.coeff_C_mul_X_pow, ite_eq_left_iff.mpr (fun h => absurd hidx h), ← hidx]
        rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
      · intro k _ hk
        rw [Polynomial.coeff_C_mul_X_pow, ite_eq_right_iff.mpr]
        intro heq
        exact (hk (Fin.ext (by dsimp [k₀]; omega))).elim
      · intro hmem; exact (hmem (Finset.mem_univ _)).elim
    · rw [Finset.sum_eq_zero]
      · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
      · intro k _
        rw [Polynomial.coeff_C_mul_X_pow, ite_eq_right_iff.mpr (fun h => absurd h (by omega))]

/-- The Kronecker resolvent `F ∈ (K[x₁, …, xₙ])[y]` of a monic polynomial `f ∈ K[x]` of degree `n`
splitting over `L` (§20.1, printed p. 156). -/
noncomputable def kroneckerResolvent {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : K[X]} {n : ℕ} (hmon : f.Monic) (hdeg : f.natDegree = n)
    {α : Fin n → L} (hroots : f.map (algebraMap K L) = generalRootsPoly α) :
    (MvPolynomial (Fin n) K)[X] :=
  (exists_unique_kroneckerResolvent_of_domain (algebraMap K L) (algebraMap K L).injective
    (a := monicGenericCoeffs f n) (α := α)
    (by rwa [garlingGenericPoly_monicGenericCoeffs hmon hdeg])).choose

theorem kroneckerResolvent_map {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : K[X]} {n : ℕ} (hmon : f.Monic) (hdeg : f.natDegree = n)
    {α : Fin n → L} (hroots : f.map (algebraMap K L) = generalRootsPoly α) :
    kroneckerMapHom n (algebraMap K L) (kroneckerResolvent hmon hdeg hroots) =
      kroneckerResolventOver α :=
  (exists_unique_kroneckerResolvent_of_domain (algebraMap K L) (algebraMap K L).injective
    (a := monicGenericCoeffs f n) (α := α)
    (by rwa [garlingGenericPoly_monicGenericCoeffs hmon hdeg])).choose_spec.1

/-- Helper: if `P.map ψ` is monic and `ψ` is injective, then `P` is monic. -/
private theorem monic_of_map_monic_of_injective {A B : Type*} [CommRing A] [CommRing B]
    {ψ : A →+* B} (hψ : Function.Injective ψ) {P : A[X]} (hm : (P.map ψ).Monic) : P.Monic := by
  apply hψ
  rw [← Polynomial.leadingCoeff_map_of_injective hψ, hm.leadingCoeff, map_one]

theorem kroneckerResolvent_monic {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : K[X]} {n : ℕ} (hmon : f.Monic) (hdeg : f.natDegree = n)
    {α : Fin n → L} (hroots : f.map (algebraMap K L) = generalRootsPoly α) :
    (kroneckerResolvent hmon hdeg hroots).Monic := by
  have hm := kroneckerResolventOver_monic α
  rw [← kroneckerResolvent_map hmon hdeg hroots] at hm
  exact monic_of_map_monic_of_injective (MvPolynomial.map_injective _ (algebraMap K L).injective) hm

theorem kroneckerResolvent_permX_inv {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : K[X]} {n : ℕ} (hmon : f.Monic) (hdeg : f.natDegree = n)
    {α : Fin n → L} (hroots : f.map (algebraMap K L) = generalRootsPoly α) (σ : SigmaN n) :
    permXPolyEquiv K σ (kroneckerResolvent hmon hdeg hroots) =
      kroneckerResolvent hmon hdeg hroots := by
  apply kroneckerMapHom_injective n (algebraMap K L).injective
  rw [kroneckerMapHom_comm_permX, kroneckerResolvent_map]
  unfold kroneckerResolventOver
  rw [map_prod]
  refine Fintype.prod_equiv (Equiv.mulLeft σ) _ _ fun τ => ?_
  rw [map_sub, permXPolyEquiv_X, permXPolyEquiv_C, Equiv.coe_mulLeft, permXRingEquiv_mul]

/-- The stabilizer `G = {σ ∈ Σ_n : σ_x F₁ = F₁} ≤ Σ_n` of a factor `F₁ ∈ (K[x₁, …, xₙ])[y]`
(§20.1, printed p. 156). -/
def kroneckerFactorStab {K : Type*} [Field K] {n : ℕ}
    (F₁ : (MvPolynomial (Fin n) K)[X]) : Subgroup (SigmaN n) where
  carrier := {σ : SigmaN n | permXPolyEquiv K σ F₁ = F₁}
  one_mem' := permXPolyEquiv_one K F₁
  mul_mem' := fun {σ τ} hσ hτ => by
    change permXPolyEquiv K (σ * τ) F₁ = F₁
    rw [permXPolyEquiv_mul, hτ, hσ]
  inv_mem' := fun {σ} hσ => by
    change permXPolyEquiv K σ⁻¹ F₁ = F₁
    calc permXPolyEquiv K σ⁻¹ F₁
        = permXPolyEquiv K σ⁻¹ (permXPolyEquiv K σ F₁) := by rw [hσ]
      _ = permXPolyEquiv K (σ⁻¹ * σ) F₁ := (permXPolyEquiv_mul K σ⁻¹ σ F₁).symm
      _ = F₁ := by rw [inv_mul_cancel, permXPolyEquiv_one]

@[simp]
theorem mem_kroneckerFactorStab_iff {K : Type*} [Field K] {n : ℕ}
    {F₁ : (MvPolynomial (Fin n) K)[X]} {σ : SigmaN n} :
    σ ∈ kroneckerFactorStab F₁ ↔ permXPolyEquiv K σ F₁ = F₁ := Iff.rfl

/-- Helper: every factor `D` of a monic polynomial `P` in `(K[x₁, …, xₙ])[y]` is associated to a
monic factor `D₀`. -/
private theorem exists_monic_associated_of_dvd_monic {K : Type*} [Field K] {n : ℕ}
    {P D : (MvPolynomial (Fin n) K)[X]} (hP : P.Monic) (hDP : D ∣ P) :
    ∃ D₀ : (MvPolynomial (Fin n) K)[X], D₀.Monic ∧ Associated D D₀ := by
  rcases hDP with ⟨Q, hQ⟩
  have hlc : D.leadingCoeff * Q.leadingCoeff = 1 := by
    rw [← Polynomial.leadingCoeff_mul, ← hQ, hP.leadingCoeff]
  have hu : IsUnit D.leadingCoeff := isUnit_iff_exists_inv.mpr ⟨Q.leadingCoeff, hlc⟩
  rcases hu with ⟨u, hu⟩
  refine ⟨Polynomial.C ((u⁻¹ : (MvPolynomial (Fin n) K)ˣ) : MvPolynomial (Fin n) K) * D, ?_, ?_⟩
  · rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, ← hu,
      Units.inv_mul]
  · refine ⟨Units.map Polynomial.C.toMonoidHom u⁻¹, ?_⟩
    change D * Polynomial.C ((u⁻¹ : (MvPolynomial (Fin n) K)ˣ) : MvPolynomial (Fin n) K) = _
    rw [mul_comm]

/-- Helper: in any integral domain `A`, a linear monic polynomial `X - C r` is prime in `A[X]`. -/
private theorem prime_X_sub_C_domain {A : Type*} [CommRing A] [IsDomain A] (r : A) :
    Prime (Polynomial.X - Polynomial.C r) := by
  refine ⟨Polynomial.X_sub_C_ne_zero r, ?_, ?_⟩
  · intro hu
    have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_X_sub_C] at hdeg
    exact one_ne_zero hdeg
  · intro p q hdiv
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_mul, mul_eq_zero] at hdiv
    exact hdiv.imp Polynomial.dvd_iff_isRoot.mpr Polynomial.dvd_iff_isRoot.mpr

/-- Helper: in `A[X]` (`A` an integral domain), if `P` is monic and divides a finite product of
pairwise distinct linear factors `∏_{i ∈ S} (X - C (r i))`, then `P = ∏_{i ∈ T} (X - C (r i))`
where `T = {i ∈ S | X - C (r i) ∣ P}`. -/
private theorem eq_prod_X_sub_C_of_monic_dvd_prod {A ι : Type*} [CommRing A] [IsDomain A]
    [DecidableEq ι] {S : Finset ι} {r : ι → A} (hr : Set.InjOn r (S : Set ι))
    {P : A[X]} (hP : P.Monic) (hdiv : P ∣ ∏ i ∈ S, (Polynomial.X - Polynomial.C (r i))) :
    ∃ T : Finset ι, T ⊆ S ∧
      P = ∏ i ∈ T, (Polynomial.X - Polynomial.C (r i)) ∧
      ∀ i ∈ S, (Polynomial.X - Polynomial.C (r i) ∣ P ↔ i ∈ T) := by
  classical
  induction S using Finset.induction_on generalizing P with
  | empty =>
    rw [Finset.prod_empty] at hdiv
    have hP1 : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hP
      (Polynomial.natDegree_eq_zero_of_isUnit (isUnit_of_dvd_one hdiv))
    exact ⟨∅, Finset.Subset.refl _, by simp [hP1], fun i hi => (Finset.notMem_empty i hi).elim⟩
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha] at hdiv
    have hr_s : Set.InjOn r (s : Set ι) := hr.mono (by simp)
    have hprime_a : Prime (Polynomial.X - Polynomial.C (r a)) := prime_X_sub_C_domain (r a)
    by_cases haP : Polynomial.X - Polynomial.C (r a) ∣ P
    · rcases haP with ⟨Q, hQ⟩
      have hQ_mon : Q.Monic := by
        have hlc := congrArg Polynomial.leadingCoeff hQ
        rw [hP.leadingCoeff, Polynomial.leadingCoeff_mul, (Polynomial.monic_X_sub_C _).leadingCoeff,
          one_mul] at hlc
        exact hlc.symm
      have hQ_div : Q ∣ ∏ i ∈ s, (Polynomial.X - Polynomial.C (r i)) := by
        rcases hdiv with ⟨R, hR⟩
        rw [hQ, mul_assoc] at hR
        exact ⟨R, mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero (r a)) hR⟩
      obtain ⟨T, hTs, hQT, hTiff⟩ := ih hr_s hQ_mon hQ_div
      have haT : a ∉ T := fun h => ha (hTs h)
      refine ⟨insert a T, Finset.insert_subset_insert a hTs, ?_, ?_⟩
      · rw [Finset.prod_insert haT, hQ, hQT]
      · intro i hi
        simp only [Finset.mem_insert] at hi ⊢
        rcases hi with rfl | his
        · simp [hQ]
        · rw [hQ, (prime_X_sub_C_domain (r i)).dvd_mul, hTiff i his]
          have hne : ¬ (Polynomial.X - Polynomial.C (r i) ∣ Polynomial.X - Polynomial.C (r a)) := by
            rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_sub,
              Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
            intro heq
            exact ha (hr (by simp [his]) (by simp) heq ▸ his)
          have hia : i ≠ a := fun h => ha (h ▸ his)
          simp [hne, hia]
    · have hP_div_s : P ∣ ∏ i ∈ s, (Polynomial.X - Polynomial.C (r i)) := by
        rcases hdiv with ⟨R, hR⟩
        have hprime_dvd_PR : Polynomial.X - Polynomial.C (r a) ∣ P * R :=
          ⟨∏ i ∈ s, (Polynomial.X - Polynomial.C (r i)), hR.symm⟩
        have haR : Polynomial.X - Polynomial.C (r a) ∣ R :=
          (hprime_a.dvd_or_dvd hprime_dvd_PR).resolve_left haP
        rcases haR with ⟨R', rfl⟩
        refine ⟨R', ?_⟩
        apply mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero (r a))
        calc (Polynomial.X - Polynomial.C (r a)) * ∏ i ∈ s, (Polynomial.X - Polynomial.C (r i))
            = P * ((Polynomial.X - Polynomial.C (r a)) * R') := hR
          _ = (Polynomial.X - Polynomial.C (r a)) * (P * R') := by ring
      obtain ⟨T, hTs, hPT, hTiff⟩ := ih hr_s hP hP_div_s
      refine ⟨T, hTs.trans (Finset.subset_insert a s), hPT, ?_⟩
      intro i hi
      simp only [Finset.mem_insert] at hi
      rcases hi with rfl | his
      · exact ⟨fun h => (haP h).elim, fun h => (ha (hTs h)).elim⟩
      · exact hTiff i his

/-- Helper: if `P, Q : (K[x₁, …, xₙ])[y]` with `P` monic and `P_L ∣ Q_L`, then `P ∣ Q`. -/
private theorem dvd_of_kroneckerMapHom_dvd_of_monic {K L : Type*} [Field K] [Field L]
    [Algebra K L] {n : ℕ} {P Q : (MvPolynomial (Fin n) K)[X]} (hP : P.Monic)
    (hdiv : kroneckerMapHom n (algebraMap K L) P ∣ kroneckerMapHom n (algebraMap K L) Q) :
    P ∣ Q := by
  have hmod_map : kroneckerMapHom n (algebraMap K L) (Q %ₘ P) = 0 := by
    have hmap_mod : (kroneckerMapHom n (algebraMap K L) Q) %ₘ
        (kroneckerMapHom n (algebraMap K L) P) =
        kroneckerMapHom n (algebraMap K L) (Q %ₘ P) :=
      (Polynomial.map_modByMonic (MvPolynomial.map (algebraMap K L)) hP).symm
    rw [← hmap_mod]
    exact (Polynomial.modByMonic_eq_zero_iff_dvd (hP.map _)).mpr hdiv
  have hmod0 : Q %ₘ P = 0 :=
    kroneckerMapHom_injective n (algebraMap K L).injective (by simpa using hmod_map)
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hP).mp hmod0

/-- Helper: every monic polynomial in `(K[x₁, …, xₙ])[y]` factors as a product of monic
irreducible polynomials. -/
private theorem exists_monic_irreducible_factors {K : Type*} [Field K] {n : ℕ}
    {P : (MvPolynomial (Fin n) K)[X]} (hP : P.Monic) :
    ∃ l : List (MvPolynomial (Fin n) K)[X],
      (∀ q ∈ l, q.Monic ∧ Irreducible q) ∧ l.prod = P := by
  classical
  suffices ∀ d : ℕ, ∀ P : (MvPolynomial (Fin n) K)[X], P.natDegree = d → P.Monic →
      ∃ l : List (MvPolynomial (Fin n) K)[X],
        (∀ q ∈ l, q.Monic ∧ Irreducible q) ∧ l.prod = P from
    this P.natDegree P rfl hP
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro P hdeg hPm
    by_cases hd0 : d = 0
    · refine ⟨[], by simp, ?_⟩
      exact (Polynomial.eq_one_of_monic_natDegree_zero hPm (hdeg.trans hd0)).symm
    · by_cases hirr : Irreducible P
      · exact ⟨[P], by simp [hPm, hirr], by simp⟩
      · have hnotu : ¬ IsUnit P := fun hu =>
          hd0 (hdeg.symm.trans (Polynomial.natDegree_eq_zero_of_isUnit hu))
        rw [irreducible_iff] at hirr
        push Not at hirr
        obtain ⟨A, B, hAB, hAu, hBu⟩ := hirr hnotu
        obtain ⟨A₀, hA₀m, hA₀a⟩ := exists_monic_associated_of_dvd_monic hPm ⟨B, hAB⟩
        obtain ⟨B₀, hB₀m, hB₀a⟩ := exists_monic_associated_of_dvd_monic hPm ⟨A, mul_comm A B ▸ hAB⟩
        have hA₀_pos : 0 < A₀.natDegree := by
          by_contra h0
          have h0' : A₀.natDegree = 0 := by omega
          have hA₀1 : A₀ = 1 := Polynomial.eq_one_of_monic_natDegree_zero hA₀m h0'
          exact hAu (hA₀a.isUnit_iff.mpr (hA₀1 ▸ isUnit_one))
        have hB₀_pos : 0 < B₀.natDegree := by
          by_contra h0
          have h0' : B₀.natDegree = 0 := by omega
          have hB₀1 : B₀ = 1 := Polynomial.eq_one_of_monic_natDegree_zero hB₀m h0'
          exact hBu (hB₀a.isUnit_iff.mpr (hB₀1 ▸ isUnit_one))
        have hP_eq : P = A₀ * B₀ := by
          rcases hA₀a with ⟨uA, huA⟩
          rcases hB₀a with ⟨uB, huB⟩
          have hprod : A₀ * B₀ = P * ((uA : (MvPolynomial (Fin n) K)[X]) * uB) := by
            rw [← huA, ← huB, hAB]; ring
          have hu_unit : IsUnit ((uA : (MvPolynomial (Fin n) K)[X]) * uB) :=
            (uA.isUnit).mul (uB.isUnit)
          have hlc := congrArg Polynomial.leadingCoeff hprod
          rw [(hA₀m.mul hB₀m).leadingCoeff, Polynomial.leadingCoeff_mul, hPm.leadingCoeff,
            one_mul] at hlc
          have hdeg_u : ((uA : (MvPolynomial (Fin n) K)[X]) * uB).natDegree = 0 :=
            Polynomial.natDegree_eq_zero_of_isUnit hu_unit
          have hu_eq1 : (uA : (MvPolynomial (Fin n) K)[X]) * uB = 1 := by
            rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg_u]
            have h0 : ((uA : (MvPolynomial (Fin n) K)[X]) * uB).coeff 0 = 1 := by
              rw [← hdeg_u]; exact hlc.symm
            rw [h0, map_one]
          rw [hu_eq1, mul_one] at hprod
          exact hprod.symm
        have hdeg_sum : A₀.natDegree + B₀.natDegree = d := by
          rw [← hdeg, hP_eq, Polynomial.natDegree_mul hA₀m.ne_zero hB₀m.ne_zero]
        obtain ⟨lA, hlA, hlAp⟩ := ih A₀.natDegree (by omega) A₀ rfl hA₀m
        obtain ⟨lB, hlB, hlBp⟩ := ih B₀.natDegree (by omega) B₀ rfl hB₀m
        refine ⟨lA ++ lB, ?_, ?_⟩
        · intro q hq
          rcases List.mem_append.mp hq with h | h
          · exact hlA q h
          · exact hlB q h
        · rw [List.prod_append, hlAp, hlBp, ← hP_eq]

/-- Galois automorphism `τ ∈ Γ_K(f)` acting on coefficients of `(L[x₁, …, xₙ])[y]` (fixing `y`
and `x₁, …, xₙ`). -/
noncomputable def galCoeffPolyEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (n : ℕ) (τ : L ≃ₐ[K] L) :
    (MvPolynomial (Fin n) L)[X] ≃+* (MvPolynomial (Fin n) L)[X] :=
  Polynomial.mapEquiv (MvPolynomial.mapEquiv (Fin n) τ.toRingEquiv)

@[simp]
theorem galCoeffPolyEquiv_kroneckerMapHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    (n : ℕ) (τ : L ≃ₐ[K] L) (P : (MvPolynomial (Fin n) K)[X]) :
    galCoeffPolyEquiv n τ (kroneckerMapHom n (algebraMap K L) P) =
      kroneckerMapHom n (algebraMap K L) P := by
  ext j m
  simp only [galCoeffPolyEquiv, kroneckerMapHom, Polynomial.mapEquiv_apply,
    Polynomial.coe_mapRingHom, Polynomial.coeff_map, MvPolynomial.coeff_map]
  exact τ.commutes ((P.coeff j).coeff m)

/-- Action of `τ ∈ Γ_K(f)` on `β = ∑ α_i x_i`: if `e : Fin n ≃ garlingRootSet K L f` labels
`α`, then `τ_*(β) = (π(τ)⁻¹)_x(β)` where `π(τ) = garlingRootLabellingPermHom e τ`. -/
theorem galCoeffPolyEquiv_beta {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : K[X]} {n : ℕ} {α : Fin n → L} (e : Fin n ≃ garlingRootSet K L f)
    (he : ∀ i : Fin n, (e i : L) = α i) (τ : GarlingPolyGaloisGroup K L f) :
    MvPolynomial.mapEquiv (Fin n) τ.toRingEquiv (kroneckerBeta α) =
      permXRingEquiv L (garlingRootLabellingPermHom e τ)⁻¹ (kroneckerBeta α) := by
  rw [← kroneckerPermAlphaBeta_eq_inv_permX]
  unfold kroneckerBeta kroneckerPermAlphaBeta
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C, MvPolynomial.map_X]
  congr 2
  rw [← he i, ← he (garlingRootLabellingPermHom e τ i)]
  exact (garlingRootLabellingPermHom_apply e τ i).symm

/-- Helper: if a prime divides a list product, it divides some element of the list. -/
private theorem prime_dvd_list_prod {A : Type*} [CommRing A] {p : A} (hp : Prime p) :
    ∀ {l : List A}, p ∣ l.prod → ∃ q ∈ l, p ∣ q
  | [], h => (hp.not_isUnit (isUnit_of_dvd_one h)).elim
  | a :: l, h => by
    rw [List.prod_cons] at h
    rcases hp.dvd_or_dvd h with ha | hl
    · exact ⟨a, List.mem_cons_self, ha⟩
    · obtain ⟨q, hql, hq⟩ := prime_dvd_list_prod hp hl
      exact ⟨q, List.mem_cons_of_mem a hql, hq⟩

/-- **Theorem 20.1** (§20.1, printed p. 157 / PDF p. 165):
*"The group `G` is isomorphic to the Galois group `Γ_K(f)`."*

Proved literally for **all** `n : ℕ` (including `n = 0`), **all** fields `K`, **all** monic
`f ∈ K[x]` of degree `n` with `n` distinct roots `α : Fin n → L` in a splitting field extension
`L : K`. -/
theorem theorem_20_1 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} {n : ℕ} (hmon : f.Monic) (hdeg : f.natDegree = n)
    (hsf : IsGarlingSplittingFieldExtension K L f)
    {α : Fin n → L} (hinj : Function.Injective α)
    (hroots : f.map (algebraMap K L) = generalRootsPoly α) :
    let F := kroneckerResolvent hmon hdeg hroots
    ∃! F₁ : (MvPolynomial (Fin n) K)[X],
      F₁.Monic ∧ Irreducible F₁ ∧ F₁ ∣ F ∧
      (Polynomial.X - Polynomial.C (kroneckerBeta α)) ∣
        kroneckerMapHom n (algebraMap K L) F₁ ∧
      (Nonempty (kroneckerFactorStab F₁ ≃* GarlingPolyGaloisGroup K L f)) ∧
      (∀ (e : Fin n ≃ garlingRootSet K L f), (∀ i, (e i : L) = α i) →
        kroneckerFactorStab F₁ = (garlingRootLabellingPermHom e).range) ∧
      (∀ F_i : (MvPolynomial (Fin n) K)[X],
        F_i.Monic → Irreducible F_i → F_i ∣ F →
        ∃ τ : SigmaN n,
          permXPolyEquiv K τ F₁ = F_i ∧
          kroneckerFactorStab F_i =
            (kroneckerFactorStab F₁).map (MulAut.conj τ).toMonoidHom ∧
          Nonempty (kroneckerFactorStab F_i ≃* GarlingPolyGaloisGroup K L f)) := by
  classical
  intro F
  have hF_mon : F.Monic := kroneckerResolvent_monic hmon hdeg hroots
  have hF_map : kroneckerMapHom n (algebraMap K L) F = kroneckerResolventOver α :=
    kroneckerResolvent_map hmon hdeg hroots
  have hβ_inj : Function.Injective (fun σ : SigmaN n => permXRingEquiv L σ (kroneckerBeta α)) :=
    kroneckerBeta_permX_injective hinj
  have hα_mem : ∀ i : Fin n, α i ∈ garlingRootSet K L f := by
    intro i
    rw [mem_garlingRootSet_iff, Polynomial.aeval_def, ← Polynomial.eval_map, hroots]
    unfold generalRootsPoly
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hα_surj : ∀ r : garlingRootSet K L f, ∃ i : Fin n, α i = r.1 := by
    intro r
    have h0 : Polynomial.eval r.1 (generalRootsPoly α) = 0 := by
      rw [← hroots, Polynomial.eval_map, ← Polynomial.aeval_def]
      exact r.2
    unfold generalRootsPoly at h0
    rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨i, _, hi⟩ := h0
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hi
    exact ⟨i, hi.symm⟩
  let e₀ : Fin n ≃ garlingRootSet K L f :=
    Equiv.ofBijective (fun i => ⟨α i, hα_mem i⟩)
      ⟨fun i j hij => hinj (congrArg Subtype.val hij),
       fun r => by obtain ⟨i, hi⟩ := hα_surj r; exact ⟨i, Subtype.ext hi⟩⟩
  have he₀ : ∀ i : Fin n, (e₀ i : L) = α i := fun _ => rfl
  -- Since `f` has `n` distinct roots in `L`, `f` is separable and `L : K` is Galois:
  have hf_sep : f.Separable := by
    rw [← Polynomial.separable_map (algebraMap K L), hroots]
    unfold generalRootsPoly
    exact Polynomial.separable_prod'
      (fun i _ j _ hij =>
        Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (fun h => hij (hinj h))).isUnit)
      (fun i _ => Polynomial.separable_X_sub_C)
  have hgal : IsGarlingGaloisExtension K L :=
    Garling.Chapter16.isGarlingGalois_of_splittingField hmon.ne_zero hsf
      ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly f).mp hf_sep).2.2
  -- Two monic irreducible factors of `F` sharing a linear factor `y - σ_x β` are equal:
  have huniq_irred : ∀ {Q₁ Q₂ : (MvPolynomial (Fin n) K)[X]} {σ : SigmaN n},
      Q₁.Monic → Irreducible Q₁ → Q₁ ∣ F →
      Q₂.Monic → Irreducible Q₂ → Q₂ ∣ F →
      (Polynomial.X - Polynomial.C (permXRingEquiv L σ (kroneckerBeta α))) ∣
        kroneckerMapHom n (algebraMap K L) Q₁ →
      (Polynomial.X - Polynomial.C (permXRingEquiv L σ (kroneckerBeta α))) ∣
        kroneckerMapHom n (algebraMap K L) Q₂ →
      Q₁ = Q₂ := by
    intro Q₁ Q₂ σ hQ₁m hQ₁i hQ₁F hQ₂m hQ₂i hQ₂F hQ₁div hQ₂div
    by_contra hne
    have hnot_assoc : ¬ Associated Q₁ Q₂ := by
      rintro ⟨u, hu⟩
      have hdeg_u : (u : (MvPolynomial (Fin n) K)[X]).natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_isUnit u.isUnit
      have hlc := congrArg Polynomial.leadingCoeff hu
      rw [Polynomial.leadingCoeff_mul, hQ₁m.leadingCoeff, hQ₂m.leadingCoeff, one_mul] at hlc
      have hu1 : (u : (MvPolynomial (Fin n) K)[X]) = 1 := by
        rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg_u]
        have : (u : (MvPolynomial (Fin n) K)[X]).coeff 0 = 1 := by rw [← hdeg_u]; exact hlc
        rw [this, map_one]
      rw [hu1, mul_one] at hu
      exact hne hu
    rcases hQ₁F with ⟨R, hR⟩
    have hQ₂_dvd_R : Q₂ ∣ R := by
      have h1 : Q₂ ∣ Q₁ * R := hR ▸ hQ₂F
      have hprime₂ : Prime Q₂ := UniqueFactorizationMonoid.irreducible_iff_prime.mp hQ₂i
      rcases hprime₂.dvd_or_dvd h1 with h21 | h2R
      · exfalso
        exact hnot_assoc (hQ₂i.associated_of_dvd hQ₁i h21).symm
      · exact h2R
    have hprod_dvd : Q₁ * Q₂ ∣ F := by
      rcases hQ₂_dvd_R with ⟨S, rfl⟩
      exact ⟨S, by rw [hR]; ring⟩
    have hsq_dvd : (Polynomial.X - Polynomial.C (permXRingEquiv L σ (kroneckerBeta α))) ^ 2 ∣
        kroneckerResolventOver α := by
      rw [sq, ← hF_map]
      exact (mul_dvd_mul hQ₁div hQ₂div).trans
        (by rw [← map_mul]; exact map_dvd (kroneckerMapHom n (algebraMap K L)) hprod_dvd)
    unfold kroneckerResolventOver at hsq_dvd
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ), sq] at hsq_dvd
    have hdiv_rest : (Polynomial.X - Polynomial.C (permXRingEquiv L σ (kroneckerBeta α))) ∣
        ∏ τ ∈ Finset.univ.erase σ,
          (Polynomial.X - Polynomial.C (permXRingEquiv L τ (kroneckerBeta α))) := by
      rcases hsq_dvd with ⟨W, hW⟩
      refine ⟨W, mul_left_cancel₀
        (Polynomial.X_sub_C_ne_zero (permXRingEquiv L σ (kroneckerBeta α))) ?_⟩
      calc (Polynomial.X - Polynomial.C (permXRingEquiv L σ (kroneckerBeta α))) *
            ∏ τ ∈ Finset.univ.erase σ,
              (Polynomial.X - Polynomial.C (permXRingEquiv L τ (kroneckerBeta α)))
          = (Polynomial.X - Polynomial.C (permXRingEquiv L σ (kroneckerBeta α))) *
              (Polynomial.X - Polynomial.C (permXRingEquiv L σ (kroneckerBeta α))) * W := hW
        _ = (Polynomial.X - Polynomial.C (permXRingEquiv L σ (kroneckerBeta α))) *
              ((Polynomial.X - Polynomial.C (permXRingEquiv L σ (kroneckerBeta α))) * W) := by ring
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_prod,
      Finset.prod_eq_zero_iff] at hdiv_rest
    obtain ⟨τ, hτmem, hτ0⟩ := hdiv_rest
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hτ0
    exact (Finset.mem_erase.mp hτmem).1 (hβ_inj hτ0.symm)
  obtain ⟨l, hl_prop, hl_prod⟩ := exists_monic_irreducible_factors hF_mon
  have hβ_dvd_F : (Polynomial.X - Polynomial.C (kroneckerBeta α)) ∣
      kroneckerMapHom n (algebraMap K L) F := by
    rw [hF_map]
    unfold kroneckerResolventOver
    have h1 := Finset.dvd_prod_of_mem
      (fun σ : SigmaN n => Polynomial.X - Polynomial.C (permXRingEquiv L σ (kroneckerBeta α)))
      (Finset.mem_univ (1 : SigmaN n))
    simpa [permXRingEquiv_one] using h1
  have hβ_prime : Prime (Polynomial.X - Polynomial.C (kroneckerBeta α)) :=
    prime_X_sub_C_domain (kroneckerBeta α)
  have hex_F₁ : ∃ F₁ ∈ l,
      (Polynomial.X - Polynomial.C (kroneckerBeta α)) ∣ kroneckerMapHom n (algebraMap K L) F₁ := by
    rw [← hl_prod, map_list_prod] at hβ_dvd_F
    obtain ⟨Q, hQl, hQdiv⟩ := prime_dvd_list_prod hβ_prime hβ_dvd_F
    obtain ⟨F₁, hF₁l, rfl⟩ := List.mem_map.mp hQl
    exact ⟨F₁, hF₁l, hQdiv⟩
  obtain ⟨F₁, hF₁l, hβ_dvd_F₁⟩ := hex_F₁
  obtain ⟨hF₁m, hF₁i⟩ := hl_prop F₁ hF₁l
  have hF₁_dvd_F : F₁ ∣ F := hl_prod ▸ List.dvd_prod hF₁l
  -- Step 1: `A₁ = {σ | y - σ_x β ∣ F₁} = kroneckerFactorStab F₁`:
  have hA₁_eq_G : ∀ σ : SigmaN n,
      ((Polynomial.X - Polynomial.C (permXRingEquiv L σ (kroneckerBeta α))) ∣
        kroneckerMapHom n (algebraMap K L) F₁) ↔ σ ∈ kroneckerFactorStab F₁ := by
    intro σ
    constructor
    · intro hdiv
      have hdiv' : (Polynomial.X - Polynomial.C (kroneckerBeta α)) ∣
          kroneckerMapHom n (algebraMap K L) (permXPolyEquiv K σ⁻¹ F₁) := by
        rw [kroneckerMapHom_comm_permX]
        have hmap := map_dvd (permXPolyEquiv L σ⁻¹) hdiv
        rw [map_sub, permXPolyEquiv_X, permXPolyEquiv_C, ← permXRingEquiv_mul, inv_mul_cancel,
          permXRingEquiv_one] at hmap
        exact hmap
      have hσinv_m : (permXPolyEquiv K σ⁻¹ F₁).Monic := hF₁m.map _
      have hσinv_i : Irreducible (permXPolyEquiv K σ⁻¹ F₁) :=
        (MulEquiv.irreducible_iff (permXPolyEquiv K σ⁻¹).toMulEquiv).mpr hF₁i
      have hσinv_F : permXPolyEquiv K σ⁻¹ F₁ ∣ F := by
        have hFinv : permXPolyEquiv K σ⁻¹ F = F :=
          kroneckerResolvent_permX_inv hmon hdeg hroots σ⁻¹
        rw [← hFinv]
        exact map_dvd (permXPolyEquiv K σ⁻¹) hF₁_dvd_F
      have heq : permXPolyEquiv K σ⁻¹ F₁ = F₁ :=
        huniq_irred (σ := 1) hσinv_m hσinv_i hσinv_F hF₁m hF₁i hF₁_dvd_F
          (by simpa [permXRingEquiv_one] using hdiv')
          (by simpa [permXRingEquiv_one] using hβ_dvd_F₁)
      exact (kroneckerFactorStab F₁).inv_mem_iff.mp heq
    · intro hσ
      have hmap := map_dvd (permXPolyEquiv L σ) hβ_dvd_F₁
      rw [← kroneckerMapHom_comm_permX, hσ] at hmap
      simpa using hmap
  -- Step 2: `kroneckerFactorStab F₁ = (garlingRootLabellingPermHom e₀).range`:
  let Γperm : Subgroup (SigmaN n) := (garlingRootLabellingPermHom e₀).range
  have hG_eq_Γ : kroneckerFactorStab F₁ = Γperm := by
    ext σ
    constructor
    · intro hσG
      let H_L : (MvPolynomial (Fin n) L)[X] :=
        ∏ ρ ∈ (Finset.univ : Finset (SigmaN n)).filter (fun ρ => ρ ∈ Γperm),
          (Polynomial.X - Polynomial.C (permXRingEquiv L ρ (kroneckerBeta α)))
      have hH_inv : ∀ τ : L ≃ₐ[K] L, galCoeffPolyEquiv n τ H_L = H_L := by
        intro τ
        dsimp [H_L]
        rw [map_prod]
        let πτ : SigmaN n := garlingRootLabellingPermHom e₀ τ
        have hπτ_mem : πτ ∈ Γperm := ⟨τ, rfl⟩
        refine Finset.prod_bij (fun ρ _ => ρ * πτ⁻¹)
          (fun ρ hρ => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
            exact Γperm.mul_mem hρ (Γperm.inv_mem hπτ_mem))
          (fun ρ₁ _ ρ₂ _ h => mul_right_cancel h)
          (fun ρ hρ => ⟨ρ * πτ, by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
            exact Γperm.mul_mem hρ hπτ_mem, by group⟩)
          fun ρ _ => ?_
        simp only [galCoeffPolyEquiv, Polynomial.mapEquiv_apply, Polynomial.map_sub,
          Polynomial.map_X, Polynomial.map_C]
        congr 2
        change MvPolynomial.mapEquiv (Fin n) τ.toRingEquiv
          (MvPolynomial.rename ρ (kroneckerBeta α)) =
          permXRingEquiv L (ρ * πτ⁻¹) (kroneckerBeta α)
        rw [MvPolynomial.mapEquiv_apply, MvPolynomial.map_rename,
          ← MvPolynomial.mapEquiv_apply, galCoeffPolyEquiv_beta e₀ he₀ τ]
        exact (permXRingEquiv_mul L ρ πτ⁻¹ (kroneckerBeta α)).symm
      have hH_coeff_K : ∀ j m,
          ∃ c : K, algebraMap K L c = (H_L.coeff j).coeff m := by
        intro j m
        have hfix : ∀ τ : L ≃ₐ[K] L, τ ((H_L.coeff j).coeff m) = (H_L.coeff j).coeff m := by
          intro τ
          have h1 := congrArg (fun P => (P.coeff j).coeff m) (hH_inv τ)
          simpa [galCoeffPolyEquiv, MvPolynomial.coeff_map] using h1
        obtain ⟨hFD, hIG⟩ := (isGarlingGaloisExtension_iff K L).mp hgal
        have hbot : IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) = ⊥ :=
          ((IsGalois.tfae (F := K) (E := L)).out 1 2).mp hIG
        have hmem_bot : (H_L.coeff j).coeff m ∈ (⊥ : IntermediateField K L) := by
          rw [← hbot, IntermediateField.mem_fixedField_iff]
          intro τ _
          exact hfix τ
        exact IntermediateField.mem_bot.mp hmem_bot
      choose cH hcH using hH_coeff_K
      let H_K : (MvPolynomial (Fin n) K)[X] :=
        ∑ j ∈ H_L.support, Polynomial.monomial j
          (∑ m ∈ (H_L.coeff j).support, MvPolynomial.monomial m (cH j m))
      have hHK_map : kroneckerMapHom n (algebraMap K L) H_K = H_L := by
        ext j m
        simp only [kroneckerMapHom, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
          MvPolynomial.coeff_map, H_K, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
          Finset.sum_ite_eq', Polynomial.mem_support_iff]
        split_ifs with hj
        · rw [MvPolynomial.coeff_sum]
          simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq', MvPolynomial.mem_support_iff]
          split_ifs with hm
          · exact hcH j m
          · push Not at hm; rw [hm, map_zero]
        · push Not at hj; rw [hj]; simp
      have hHK_mon : H_K.Monic := by
        have hHL_mon : H_L.Monic :=
          Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _
        rw [← hHK_map] at hHL_mon
        exact monic_of_map_monic_of_injective
          (MvPolynomial.map_injective _ (algebraMap K L).injective) hHL_mon
      have hHK_dvd_F : H_K ∣ F := by
        apply dvd_of_kroneckerMapHom_dvd_of_monic (L := L) hHK_mon
        rw [hHK_map, hF_map]
        exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
      have hβ_dvd_HK : (Polynomial.X - Polynomial.C (kroneckerBeta α)) ∣
          kroneckerMapHom n (algebraMap K L) H_K := by
        rw [hHK_map]
        have h1mem : (1 : SigmaN n) ∈
            (Finset.univ : Finset (SigmaN n)).filter (fun ρ => ρ ∈ Γperm) := by
          simp [Γperm.one_mem]
        simpa [permXRingEquiv_one] using Finset.dvd_prod_of_mem
          (fun ρ : SigmaN n => Polynomial.X - Polynomial.C (permXRingEquiv L ρ (kroneckerBeta α)))
          h1mem
      obtain ⟨lH, hlH_prop, hlH_prod⟩ := exists_monic_irreducible_factors hHK_mon
      have hex_Q : ∃ Q ∈ lH,
          (Polynomial.X - Polynomial.C (kroneckerBeta α)) ∣ kroneckerMapHom n (algebraMap K L) Q := by
        rw [← hlH_prod, map_list_prod] at hβ_dvd_HK
        obtain ⟨Q', hQ'l, hQ'div⟩ := prime_dvd_list_prod hβ_prime hβ_dvd_HK
        obtain ⟨Q, hQl, rfl⟩ := List.mem_map.mp hQ'l
        exact ⟨Q, hQl, hQ'div⟩
      obtain ⟨Q, hQl, hβ_dvd_Q⟩ := hex_Q
      obtain ⟨hQm, hQi⟩ := hlH_prop Q hQl
      have hQ_dvd_HK : Q ∣ H_K := hlH_prod ▸ List.dvd_prod hQl
      have hQF₁ : Q = F₁ :=
        huniq_irred (σ := 1) hQm hQi (hQ_dvd_HK.trans hHK_dvd_F) hF₁m hF₁i hF₁_dvd_F
          (by simpa [permXRingEquiv_one] using hβ_dvd_Q)
          (by simpa [permXRingEquiv_one] using hβ_dvd_F₁)
      have hF₁_dvd_HK : F₁ ∣ H_K := hQF₁ ▸ hQ_dvd_HK
      have hσ_dvd_HL : (Polynomial.X - Polynomial.C (permXRingEquiv L σ (kroneckerBeta α))) ∣ H_L :=
        ((hA₁_eq_G σ).mpr hσG).trans (hHK_map ▸ map_dvd (kroneckerMapHom n (algebraMap K L)) hF₁_dvd_HK)
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_prod,
        Finset.prod_eq_zero_iff] at hσ_dvd_HL
      obtain ⟨ρ, hρmem, hρ0⟩ := hσ_dvd_HL
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hρ0
      have hσρ : σ = ρ := hβ_inj hρ0
      rw [hσρ]
      exact (Finset.mem_filter.mp hρmem).2
    · rintro ⟨τ, rfl⟩
      have hmap := map_dvd (galCoeffPolyEquiv n τ) hβ_dvd_F₁
      rw [galCoeffPolyEquiv_kroneckerMapHom] at hmap
      have hmap' : (Polynomial.X - Polynomial.C
          (permXRingEquiv L (garlingRootLabellingPermHom e₀ τ)⁻¹ (kroneckerBeta α))) ∣
          kroneckerMapHom n (algebraMap K L) F₁ := by
        simp only [galCoeffPolyEquiv, Polynomial.mapEquiv_apply, Polynomial.map_sub,
          Polynomial.map_X, Polynomial.map_C] at hmap
        change (Polynomial.X - Polynomial.C
          (MvPolynomial.mapEquiv (Fin n) τ.toRingEquiv (kroneckerBeta α))) ∣
          kroneckerMapHom n (algebraMap K L) F₁ at hmap
        rwa [galCoeffPolyEquiv_beta e₀ he₀ τ] at hmap
      have hinv : (garlingRootLabellingPermHom e₀ τ)⁻¹ ∈ kroneckerFactorStab F₁ :=
        (hA₁_eq_G _).mp hmap'
      exact (kroneckerFactorStab F₁).inv_mem_iff.mp hinv
  have he₀_inj : Function.Injective (garlingRootLabellingPermHom e₀) := by
    intro σ₁ σ₂ h
    apply theorem_11_6 hsf
    ext r
    have h1 := Equiv.congr_fun h (e₀.symm r)
    have h2 : e₀ (garlingRootLabellingPermHom e₀ σ₁ (e₀.symm r)) =
        e₀ (garlingRootLabellingPermHom e₀ σ₂ (e₀.symm r)) := congrArg e₀ h1
    simpa [garlingRootLabellingPermHom] using congrArg Subtype.val h2
  have hiso : Nonempty (kroneckerFactorStab F₁ ≃* GarlingPolyGaloisGroup K L f) :=
    ⟨(MulEquiv.subgroupCongr hG_eq_Γ).trans
      (MulEquiv.ofBijective (garlingRootLabellingPermHom e₀).rangeRestrict
        ⟨fun a b hab => he₀_inj (congrArg Subtype.val hab),
         (garlingRootLabellingPermHom e₀).rangeRestrict_surjective⟩).symm⟩
  have hrange_all : ∀ (e : Fin n ≃ garlingRootSet K L f), (∀ i, (e i : L) = α i) →
      kroneckerFactorStab F₁ = (garlingRootLabellingPermHom e).range := by
    intro e he
    have hee₀ : e = e₀ := Equiv.ext fun i => Subtype.ext ((he i).trans (he₀ i).symm)
    rw [hee₀, hG_eq_Γ]
  have hconj_all : ∀ F_i : (MvPolynomial (Fin n) K)[X],
      F_i.Monic → Irreducible F_i → F_i ∣ F →
      ∃ τ : SigmaN n,
        permXPolyEquiv K τ F₁ = F_i ∧
        kroneckerFactorStab F_i =
          (kroneckerFactorStab F₁).map (MulAut.conj τ).toMonoidHom ∧
        Nonempty (kroneckerFactorStab F_i ≃* GarlingPolyGaloisGroup K L f) := by
    intro F_i hFim hFii hFiF
    have hFi_map_dvd : kroneckerMapHom n (algebraMap K L) F_i ∣ kroneckerResolventOver α :=
      hF_map ▸ map_dvd (kroneckerMapHom n (algebraMap K L)) hFiF
    obtain ⟨T, _, hFi_prod, hTiff⟩ := eq_prod_X_sub_C_of_monic_dvd_prod
      (r := fun σ => permXRingEquiv L σ (kroneckerBeta α))
      (fun _ _ _ _ h => hβ_inj h) (hFim.map _) hFi_map_dvd
    have hTne : T.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Finset.prod_empty] at hFi_prod
      have h1 : F_i = 1 := kroneckerMapHom_injective n (algebraMap K L).injective
        (hFi_prod.trans (map_one _).symm)
      exact hFii.not_isUnit (h1 ▸ isUnit_one)
    obtain ⟨τ, hτT⟩ := hTne
    have hτ_dvd_Fi : (Polynomial.X - Polynomial.C (permXRingEquiv L τ (kroneckerBeta α))) ∣
        kroneckerMapHom n (algebraMap K L) F_i := (hTiff τ (Finset.mem_univ τ)).mpr hτT
    have hτ_dvd_τF₁ : (Polynomial.X - Polynomial.C (permXRingEquiv L τ (kroneckerBeta α))) ∣
        kroneckerMapHom n (algebraMap K L) (permXPolyEquiv K τ F₁) := by
      rw [kroneckerMapHom_comm_permX]
      have hmap := map_dvd (permXPolyEquiv L τ) hβ_dvd_F₁
      rw [map_sub, permXPolyEquiv_X, permXPolyEquiv_C] at hmap
      exact hmap
    have hτF₁_dvd_F : permXPolyEquiv K τ F₁ ∣ F := by
      have hFinv : permXPolyEquiv K τ F = F :=
        kroneckerResolvent_permX_inv hmon hdeg hroots τ
      rw [← hFinv]
      exact map_dvd (permXPolyEquiv K τ) hF₁_dvd_F
    have hτF₁_eq : permXPolyEquiv K τ F₁ = F_i :=
      huniq_irred (hF₁m.map _)
        ((MulEquiv.irreducible_iff (permXPolyEquiv K τ).toMulEquiv).mpr hF₁i)
        hτF₁_dvd_F
        hFim hFii hFiF hτ_dvd_τF₁ hτ_dvd_Fi
    have hstab_eq : kroneckerFactorStab F_i =
        (kroneckerFactorStab F₁).map (MulAut.conj τ).toMonoidHom := by
      ext σ
      simp only [mem_kroneckerFactorStab_iff, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      constructor
      · intro hσ
        refine ⟨τ⁻¹ * σ * τ, ?_, by group⟩
        rw [permXPolyEquiv_mul, permXPolyEquiv_mul, hτF₁_eq, hσ, ← hτF₁_eq,
          ← permXPolyEquiv_mul, inv_mul_cancel, permXPolyEquiv_one]
      · rintro ⟨ρ, hρ, rfl⟩
        rw [← hτF₁_eq, ← permXPolyEquiv_mul]
        have : τ * ρ * τ⁻¹ * τ = τ * ρ := by group
        rw [this, permXPolyEquiv_mul, hρ]
    obtain ⟨e₁⟩ := hiso
    refine ⟨τ, hτF₁_eq, hstab_eq, ⟨(MulEquiv.subgroupCongr hstab_eq).trans
      (((MulAut.conj τ).subgroupMap (kroneckerFactorStab F₁)).symm.trans e₁)⟩⟩
  refine ⟨F₁, ⟨hF₁m, hF₁i, hF₁_dvd_F, hβ_dvd_F₁, hiso, hrange_all, hconj_all⟩, ?_⟩
  rintro F₁' ⟨hF₁'m, hF₁'i, hF₁'F, hβ_dvd_F₁', _, _, _⟩
  exact huniq_irred (σ := 1) hF₁'m hF₁'i hF₁'F hF₁m hF₁i hF₁_dvd_F
    (by simpa [permXRingEquiv_one] using hβ_dvd_F₁')
    (by simpa [permXRingEquiv_one] using hβ_dvd_F₁)

/-- **§20.1 Prose `ℤ[x]` Algorithm & Monic-Rescaling Remark** (printed p. 157 / PDF p. 165):
1. For any monic `f ∈ ℤ[x]` of degree `n` splitting in `L : ℚ`, its Kronecker resolvent `F`
   descends to `(ℤ[x₁, …, xₙ])[y]`.
2. Without monic rescaling (`2x - 1`, `n = 1`), the Kronecker resolvent `y - (1/2) x₁` does **not**
   lie in `(ℤ[x₁])[y]`. -/
theorem section_20_1_int_resolvent_and_monic_rescaling :
    (∀ {f : ℤ[X]} {n : ℕ}, f.Monic → f.natDegree = n →
        ∀ {L : Type u} [Field L] [Algebra ℚ L] {α : Fin n → L},
        (f.map (algebraMap ℤ ℚ)).map (algebraMap ℚ L) = generalRootsPoly α →
        ∃! F_Z : (MvPolynomial (Fin n) ℤ)[X],
          kroneckerMapHom n (algebraMap ℤ L) F_Z = kroneckerResolventOver α) ∧
    (¬ ∃ F_Z : (MvPolynomial (Fin 1) ℤ)[X],
        kroneckerMapHom 1 (algebraMap ℤ ℚ) F_Z =
          Polynomial.X - Polynomial.C (MvPolynomial.C (1 / 2 : ℚ) * MvPolynomial.X 0)) := by
  refine ⟨?_, ?_⟩
  · intro f n hmon hdeg L _ _ α hroots
    have hmap_comp : (algebraMap ℚ L).comp (algebraMap ℤ ℚ) = algebraMap ℤ L :=
      RingHom.ext fun z => by simp
    have hroots' : (garlingGenericPoly (monicGenericCoeffs f n)).map (algebraMap ℤ L) =
        generalRootsPoly α := by
      rw [garlingGenericPoly_monicGenericCoeffs hmon hdeg, ← hmap_comp, ← Polynomial.map_map, hroots]
    exact exists_unique_kroneckerResolvent_of_domain (algebraMap ℤ L)
      (by
        rw [← hmap_comp]
        exact (algebraMap ℚ L).injective.comp Int.cast_injective) hroots'
  · rintro ⟨F_Z, hFZ⟩
    have hcoeff := congrArg
      (fun P : (MvPolynomial (Fin 1) ℚ)[X] => (P.coeff 0).coeff (Finsupp.single (0 : Fin 1) 1)) hFZ
    simp only [kroneckerMapHom, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
      MvPolynomial.coeff_map, Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
      zero_sub, MvPolynomial.coeff_neg, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X] at hcoeff
    norm_num at hcoeff
    have h2 := congrArg (fun q : ℚ => 2 * q) hcoeff
    norm_num at h2
    have hZ : (2 : ℤ) * ((F_Z.coeff 0).coeff (Finsupp.single (0 : Fin 1) 1)) = -1 := by
      exact_mod_cast h2
    omega

/-! ### Theorem 20.2 (printed p. 158 / PDF p. 166) -/

/-- Helper: if a finite group `D` surjects onto a finite cyclic group `C`, then `C` is isomorphic
to a subgroup of `D`. -/
private theorem exists_subgroup_mulEquiv_of_surjective_to_cyclic
    {D : Type u} {C : Type v} [Group D] [Finite D] [Group C] [Finite C] [IsCyclic C]
    (φ : D →* C) (hsurj : Function.Surjective φ) :
    ∃ H : Subgroup D, Nonempty (C ≃* H) := by
  classical
  let _ : Fintype D := Fintype.ofFinite D
  let _ : Fintype C := Fintype.ofFinite C
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := C)
  obtain ⟨d, hd⟩ := hsurj c
  have hm_pos : 0 < orderOf c := orderOf_pos c
  have hord_dvd : orderOf c ∣ orderOf d := by
    rw [← hd]
    exact orderOf_map_dvd φ d
  let k : ℕ := orderOf d / orderOf c
  let g : D := d ^ k
  have hk_pos : 0 < k := Nat.pos_of_ne_zero fun h0 => by
    have hpos_d : 0 < orderOf d := orderOf_pos d
    have hmul : orderOf c * k = orderOf d := Nat.mul_div_cancel' hord_dvd
    rw [h0, mul_zero] at hmul
    omega
  have hg_ord : orderOf g = orderOf c := by
    dsimp [g]
    rw [orderOf_pow' d hk_pos.ne']
    have hmul : orderOf c * k = orderOf d := Nat.mul_div_cancel' hord_dvd
    have hgcd : (orderOf d).gcd k = k := Nat.gcd_eq_right ⟨orderOf c, by linarith⟩
    rw [hgcd]
    exact Nat.div_eq_of_eq_mul_left hk_pos hmul.symm
  have hC_card : Nat.card C = orderOf c := by
    rw [← Nat.card_zpowers, show Subgroup.zpowers c = ⊤ from
      eq_top_iff.mpr fun x _ => hc x]
    exact Nat.card_congr Subgroup.topEquiv.symm.toEquiv
  have hH_card : Nat.card (Subgroup.zpowers g) = orderOf c := by
    rw [Nat.card_zpowers, hg_ord]
  have _ : NeZero (orderOf c) := ⟨hm_pos.ne'⟩
  obtain ⟨eC⟩ := mulEquivMultiplicativeZModOfOrderOfEqNatCard c rfl hC_card
  have hg_in_ord : orderOf (⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.zpowers g) = orderOf c := by
    rw [Subgroup.orderOf_mk, hg_ord]
  obtain ⟨eH⟩ := mulEquivMultiplicativeZModOfOrderOfEqNatCard
    (⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.zpowers g) hg_in_ord hH_card
  exact ⟨Subgroup.zpowers g, ⟨eC.trans eH.symm⟩⟩

/-- **Theorem 20.2** (§20.1, printed p. 158 / PDF p. 166):
*"Suppose that `f` is a monic polynomial in `ℤ[x]` and that `p` is a prime. Let `f̄` be the
corresponding element of `ℤ_p[x]`. If `f` has distinct roots in a splitting field extension `L`,
then the cyclic group `Γ_{ℤ_p}(f̄)` is isomorphic to a subgroup of `Γ_ℚ(f)`."*

Proved **literally and unconditionally** for **all** monic `f ∈ ℤ[x]` with distinct roots in `L`
and **all** primes `p` — including ramified primes `p ∣ Δ(f)` where `f̄` has repeated roots (as
needed in `Exercise 20.1`). -/
theorem theorem_20_2 {f : ℤ[X]} (hmon : f.Monic) {p : ℕ} (hp : Nat.Prime p)
    {L : Type u} [Field L] [Algebra ℚ L]
    (hsfL : IsGarlingSplittingFieldExtension ℚ L (f.map (algebraMap ℤ ℚ)))
    (_hdist : ¬ HasGarlingRepeatedRoot ℚ L (f.map (algebraMap ℤ ℚ))) :
    haveI : Fact p.Prime := ⟨hp⟩
    ∀ {M : Type v} [Field M] [Algebra (ZMod p) M],
      IsGarlingSplittingFieldExtension (ZMod p) M (modPrimePolyHom p f) →
      IsCyclic (GarlingPolyGaloisGroup (ZMod p) M (modPrimePolyHom p f)) ∧
      ∃ H : Subgroup (GarlingPolyGaloisGroup ℚ L (f.map (algebraMap ℤ ℚ))),
        Nonempty (GarlingPolyGaloisGroup (ZMod p) M (modPrimePolyHom p f) ≃* H) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro M _ _ hsfM
  let fQ : ℚ[X] := f.map (algebraMap ℤ ℚ)
  let fbar : (ZMod p)[X] := modPrimePolyHom p f
  have hfQ_mon : fQ.Monic := hmon.map (algebraMap ℤ ℚ)
  have hfbar_mon : fbar.Monic := hmon.map (Int.castRingHom (ZMod p))
  have hsfM_mathlib : fbar.IsSplittingField (ZMod p) M :=
    (isGarlingSplittingFieldExtension_iff (ZMod p) M fbar).mp hsfM
  have _ : FiniteDimensional (ZMod p) M := Polynomial.IsSplittingField.finiteDimensional M fbar
  have _ : Finite M := Module.finite_of_finite (ZMod p)
  have hcycM : IsCyclic (GarlingPolyGaloisGroup (ZMod p) M fbar) :=
    (corollary_to_theorem_12_4 (ZMod p) M).1
  refine ⟨hcycM, ?_⟩
  have hsfL_mathlib : fQ.IsSplittingField ℚ L :=
    (isGarlingSplittingFieldExtension_iff ℚ L fQ).mp hsfL
  have _ : FiniteDimensional ℚ L := Polynomial.IsSplittingField.finiteDimensional L fQ
  have _ : Normal ℚ L := Normal.of_isSplittingField fQ
  have _ : IsGalois ℚ L := {}
  have _ : Finite (L ≃ₐ[ℚ] L) := inferInstance
  let B := integralClosure ℤ L
  have _ : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension ℚ L
  let _ : MulSemiringAction (L ≃ₐ[ℚ] L) B := IsIntegralClosure.MulSemiringAction ℤ ℚ L B
  have _ : SMulCommClass (L ≃ₐ[ℚ] L) ℤ B :=
    ⟨fun σ z b => Subtype.ext (by
      change (galRestrict ℤ ℚ L B σ (z • b) : L) = ((z • galRestrict ℤ ℚ L B σ b : B) : L)
      rw [map_zsmul])⟩
  have _ : Algebra.IsInvariant ℤ B (L ≃ₐ[ℚ] L) := Algebra.isInvariant_of_isGalois ℤ ℚ L B
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hP_max : P.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Int.prime_iff_natAbs_prime.mpr (by simpa using hp)).irreducible)
  have _ : P.IsMaximal := hP_max
  have _ : Algebra.IsIntegral ℤ B := Algebra.IsInvariant.isIntegral ℤ B (L ≃ₐ[ℚ] L)
  have _ : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have _ : FaithfulSMul ℤ B :=
    ⟨fun {a b} h => Int.cast_injective (α := L) (by
      have h1 := congrArg Subtype.val (h 1)
      simpa [Algebra.smul_def] using h1)⟩
  obtain ⟨Q, hQ_max, hQ_over⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := B) P
  have _ : Q.IsMaximal := hQ_max
  have _ : Q.LiesOver P := hQ_over
  let _ : Field (ℤ ⧸ P) := Ideal.Quotient.field P
  let _ : Field (B ⧸ Q) := Ideal.Quotient.field Q
  have _ : Normal (ℤ ⧸ P) (B ⧸ Q) := Ideal.Quotient.normal (L ≃ₐ[ℚ] L) P Q
  let eP : (ℤ ⧸ P) ≃+* ZMod p := Int.quotientSpanNatEquivZMod p
  obtain ⟨m, c, α, hexp⟩ := hsfL.1
  have hc1 : c = 1 :=
    (garlingSplitsExplicit_props hfQ_mon.ne_zero hexp).1.trans hfQ_mon.leadingCoeff
  subst hc1
  have hα_int : ∀ i : Fin m, α i ∈ B := by
    intro i
    refine ⟨f, hmon, ?_⟩
    have h0 : Polynomial.aeval (α i) fQ = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hexp]
      simp [Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ i)]
    rw [Polynomial.aeval_def, Polynomial.eval₂_map] at h0
    have hring : (algebraMap ℚ L).comp (algebraMap ℤ ℚ) = algebraMap ℤ L :=
      Subsingleton.elim _ _
    rwa [← hring]
  let αB : Fin m → B := fun i => ⟨α i, hα_int i⟩
  have hf_B : f.map (algebraMap ℤ B) = ∏ i : Fin m, (Polynomial.X - Polynomial.C (αB i)) := by
    apply Polynomial.map_injective (algebraMap B L) (FaithfulSMul.algebraMap_injective B L)
    rw [Polynomial.map_map, show (algebraMap B L).comp (algebraMap ℤ B) =
        (algebraMap ℚ L).comp (algebraMap ℤ ℚ) from RingHom.ext fun z => by simp,
      ← Polynomial.map_map]
    change fQ.map (algebraMap ℚ L) = _
    rw [hexp, map_one, Polynomial.C_1, one_mul, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [αB]
  let fP : (ℤ ⧸ P)[X] := f.map (Ideal.Quotient.mk P)
  let M₀ : IntermediateField (ℤ ⧸ P) (B ⧸ Q) :=
    IntermediateField.adjoin (ℤ ⧸ P) (fP.rootSet (B ⧸ Q))
  have hfP_mon : fP.Monic := hmon.map _
  have hM₀_sf : fP.IsSplittingField (ℤ ⧸ P) M₀ := by
    refine ⟨?_, ?_⟩
    · have hsub : ∀ i : Fin m, Ideal.Quotient.mk Q (αB i) ∈ M₀ := fun i => by
        apply IntermediateField.subset_adjoin
        rw [Polynomial.mem_rootSet_of_ne hfP_mon.ne_zero]
        have hcomp : (algebraMap (ℤ ⧸ P) (B ⧸ Q)).comp (Ideal.Quotient.mk P) =
            (Ideal.Quotient.mk Q).comp (algebraMap ℤ B) :=
          RingHom.ext fun z => by
            change algebraMap (ℤ ⧸ P) (B ⧸ Q) (algebraMap ℤ (ℤ ⧸ P) z) =
              algebraMap B (B ⧸ Q) (algebraMap ℤ B z)
            rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ B (B ⧸ Q)]
        rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_map, hcomp,
          ← Polynomial.map_map, hf_B, Polynomial.map_prod, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
      let γ : Fin m → M₀ := fun i => ⟨Ideal.Quotient.mk Q (αB i), hsub i⟩
      have hfac : fP.map (algebraMap (ℤ ⧸ P) M₀) = ∏ i : Fin m, (Polynomial.X - Polynomial.C (γ i)) := by
        apply Polynomial.map_injective M₀.val.toRingHom M₀.val.injective
        rw [Polynomial.map_map, Polynomial.map_prod]
        have hcomp : (M₀.val.toRingHom.comp (algebraMap (ℤ ⧸ P) M₀)).comp (Ideal.Quotient.mk P) =
            (Ideal.Quotient.mk Q).comp (algebraMap ℤ B) :=
          RingHom.ext fun z => by
            change algebraMap (ℤ ⧸ P) (B ⧸ Q) (algebraMap ℤ (ℤ ⧸ P) z) =
              algebraMap B (B ⧸ Q) (algebraMap ℤ B z)
            rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ B (B ⧸ Q)]
        change (f.map (Ideal.Quotient.mk P)).map (M₀.val.toRingHom.comp (algebraMap (ℤ ⧸ P) M₀)) = _
        rw [Polynomial.map_map, hcomp, ← Polynomial.map_map, hf_B, Polynomial.map_prod]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp [γ]
      rw [hfac]
      exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _
    · rw [eq_top_iff]
      intro x _
      have hint_roots : ∀ r ∈ fP.rootSet (B ⧸ Q), IsAlgebraic (ℤ ⧸ P) r := fun r hr => by
        have hi : IsIntegral (ℤ ⧸ P) r :=
          ⟨fP, hfP_mon, (Polynomial.mem_rootSet_of_ne hfP_mon.ne_zero).mp hr⟩
        exact hi.isAlgebraic
      have hadj_eq : (M₀.toSubalgebra : Subalgebra (ℤ ⧸ P) (B ⧸ Q)) =
          Algebra.adjoin (ℤ ⧸ P) (fP.rootSet (B ⧸ Q)) :=
        IntermediateField.adjoin_toSubalgebra_of_isAlgebraic hint_roots
      have hx_alg : x.1 ∈ Algebra.adjoin (ℤ ⧸ P) (fP.rootSet (B ⧸ Q)) := by
        rw [← hadj_eq]; exact x.2
      have hsub_map : Algebra.adjoin (ℤ ⧸ P) (fP.rootSet (B ⧸ Q)) ≤
          (Algebra.adjoin (ℤ ⧸ P) (fP.rootSet M₀)).map M₀.val := by
        rw [Algebra.adjoin_le_iff]
        intro r hr
        have hrM : r ∈ M₀ := IntermediateField.subset_adjoin _ _ hr
        refine ⟨⟨r, hrM⟩, Algebra.subset_adjoin ?_, rfl⟩
        rw [Polynomial.mem_rootSet_of_ne hfP_mon.ne_zero] at hr ⊢
        apply M₀.val.injective
        change M₀.val ((Polynomial.aeval ⟨r, hrM⟩) fP) = M₀.val 0
        rw [map_zero, ← Polynomial.aeval_algHom_apply M₀.val ⟨r, hrM⟩ fP]
        exact hr
      obtain ⟨y, hy, hyx⟩ := hsub_map hx_alg
      exact (Subtype.ext hyx : y = x) ▸ hy
  have _ : Normal (ℤ ⧸ P) M₀ := Normal.of_isSplittingField fP
  let φ₁ : MulAction.stabilizer (L ≃ₐ[ℚ] L) Q →* ((B ⧸ Q) ≃ₐ[ℤ ⧸ P] (B ⧸ Q)) :=
    Ideal.Quotient.stabilizerHom Q P (L ≃ₐ[ℚ] L)
  have hφ₁ : Function.Surjective φ₁ := Ideal.Quotient.stabilizerHom_surjective (L ≃ₐ[ℚ] L) P Q
  let φ₂ : ((B ⧸ Q) ≃ₐ[ℤ ⧸ P] (B ⧸ Q)) →* (M₀ ≃ₐ[ℤ ⧸ P] M₀) :=
    AlgEquiv.restrictNormalHom M₀
  have hφ₂ : Function.Surjective φ₂ :=
    AlgEquiv.restrictNormalHom_surjective (F := ℤ ⧸ P) (K₁ := M₀) (E := B ⧸ Q)
  have hfbar_eq : garlingMapPoly eP.toRingHom fP = fbar := by
    dsimp [fP, fbar, modPrimePolyHom, garlingMapPoly]
    rw [Polynomial.map_map]
    congr 1
  have hsfM₀_gar : IsGarlingSplittingFieldExtension (ℤ ⧸ P) M₀ fP :=
    (isGarlingSplittingFieldExtension_iff (ℤ ⧸ P) M₀ fP).mpr hM₀_sf
  have hsfM' : IsGarlingSplittingFieldExtension (ZMod p) M (garlingMapPoly eP.toRingHom fP) := by
    rw [hfbar_eq]; exact hsfM
  obtain ⟨eM, heM_comm⟩ := corollary_1_to_theorem_7_5_equiv eP fP hsfM₀_gar hsfM'
  let ψ : (M₀ ≃ₐ[ℤ ⧸ P] M₀) ≃* (M ≃ₐ[ZMod p] M) :=
    { toFun := fun σ =>
        { (eM.symm.trans (σ.toRingEquiv.trans eM)) with
          commutes' := fun a => by
            obtain ⟨b, rfl⟩ := eP.surjective a
            have hcomm : eM (algebraMap (ℤ ⧸ P) M₀ b) = algebraMap (ZMod p) M (eP b) :=
              heM_comm b
            change eM (σ (eM.symm (algebraMap (ZMod p) M (eP b)))) = algebraMap (ZMod p) M (eP b)
            rw [← hcomm, RingEquiv.symm_apply_apply, σ.commutes, hcomm] }
      invFun := fun τ =>
        { (eM.trans (τ.toRingEquiv.trans eM.symm)) with
          commutes' := fun b => by
            have hcomm : eM (algebraMap (ℤ ⧸ P) M₀ b) = algebraMap (ZMod p) M (eP b) :=
              heM_comm b
            change eM.symm (τ (eM (algebraMap (ℤ ⧸ P) M₀ b))) = algebraMap (ℤ ⧸ P) M₀ b
            rw [hcomm, τ.commutes, ← hcomm, RingEquiv.symm_apply_apply] }
      left_inv := fun σ => by ext x; simp
      right_inv := fun τ => by ext x; simp
      map_mul' := fun σ₁ σ₂ => by ext x; simp }
  let Φ : MulAction.stabilizer (L ≃ₐ[ℚ] L) Q →* GarlingPolyGaloisGroup (ZMod p) M fbar :=
    ψ.toMonoidHom.comp (φ₂.comp φ₁)
  have hΦ_surj : Function.Surjective Φ := ψ.surjective.comp (hφ₂.comp hφ₁)
  have _ : Finite (MulAction.stabilizer (L ≃ₐ[ℚ] L) Q) := inferInstance
  have _ : Finite (GarlingPolyGaloisGroup (ZMod p) M fbar) := inferInstance
  obtain ⟨H₀, ⟨eH₀⟩⟩ := exists_subgroup_mulEquiv_of_surjective_to_cyclic Φ hΦ_surj
  let incl : MulAction.stabilizer (L ≃ₐ[ℚ] L) Q →* (L ≃ₐ[ℚ] L) :=
    (MulAction.stabilizer (L ≃ₐ[ℚ] L) Q).subtype
  refine ⟨H₀.map incl, ⟨eH₀.trans (MulEquiv.ofBijective (incl.subgroupMap H₀) ?_)⟩⟩
  refine ⟨fun a b hab => ?_, ?_⟩
  · have hval : ((a : MulAction.stabilizer (L ≃ₐ[ℚ] L) Q) : L ≃ₐ[ℚ] L) =
        ((b : MulAction.stabilizer (L ≃ₐ[ℚ] L) Q) : L ≃ₐ[ℚ] L) :=
      congrArg (fun x : H₀.map incl => (x : L ≃ₐ[ℚ] L)) hab
    exact Subtype.ext (Subtype.ext hval)
  · rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- **Witness to the ramified-prime gap in Garling's p. 158 proof of `Theorem 20.2`:**
For `f = x² - 7 ∈ ℤ[x]` at `p = 7`, `f̄ = x² ∈ ℤ₇[x]` has repeated root `0`, so `Γ_{ℤ₇}(f̄)` has
order `1`, whereas `y - δ = y` (the monic irreducible factor of `F̄ = y²`) has stabilizer `Σ₂`
of order `2 ≠ 1`, so `Theorem 20.1` fails on `f̄` even though `Theorem 20.2` holds literally. -/
theorem theorem_20_2_ramified_proof_gap_witness :
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    let f : ℤ[X] := Polynomial.X ^ 2 - Polynomial.C 7
    let fbar : (ZMod 7)[X] := modPrimePolyHom 7 f
    f.Monic ∧
    fbar = Polynomial.X ^ 2 ∧
    HasGarlingRepeatedRoot (ZMod 7) (ZMod 7) fbar ∧
    Nat.card (GarlingPolyGaloisGroup (ZMod 7) (ZMod 7) fbar) = 1 ∧
    Nat.card (kroneckerFactorStab (Polynomial.X : (MvPolynomial (Fin 2) (ZMod 7))[X])) = 2 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro f fbar
  have hmon : f.Monic := Polynomial.monic_X_pow_sub_C 7 (by norm_num)
  have hfbar : fbar = Polynomial.X ^ 2 := by
    dsimp [fbar, f, modPrimePolyHom]
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    have h7 : Int.castRingHom (ZMod 7) 7 = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd 7 7).mpr dvd_rfl
    rw [h7, map_zero, sub_zero]
  have hrep : HasGarlingRepeatedRoot (ZMod 7) (ZMod 7) fbar := by
    rw [hfbar]
    refine ⟨0, 2, by norm_num, by simp⟩
  have hcard1 : Nat.card (GarlingPolyGaloisGroup (ZMod 7) (ZMod 7) fbar) = 1 := by
    have : Subsingleton (ZMod 7 ≃ₐ[ZMod 7] ZMod 7) :=
      ⟨fun σ τ => AlgEquiv.ext fun x => by
        rw [← Algebra.algebraMap_self_apply x, σ.commutes, τ.commutes]⟩
    exact Nat.card_unique
  have hstab_top : kroneckerFactorStab (Polynomial.X : (MvPolynomial (Fin 2) (ZMod 7))[X]) = ⊤ := by
    ext σ
    simp [permXPolyEquiv_X]
  have hcard2 : Nat.card (kroneckerFactorStab (Polynomial.X : (MvPolynomial (Fin 2) (ZMod 7))[X])) = 2 := by
    rw [hstab_top, Nat.card_congr Subgroup.topEquiv.toEquiv]
    change Nat.card (Equiv.Perm (Fin 2)) = 2
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  exact ⟨hmon, hfbar, hrep, hcard1, hcard2⟩

/-! ## §20.2 The soluble transitive subgroups of `Σ_p` (pp. 158–161) -/

/-! ### Inline prose definitions: *orbit* `O_H(x)`, transitivity of normal subgroups, *affine* group `W` -/

/-- Garling's inline italicized definition of the *orbit* `O_H(x) = {σ x : σ ∈ H}` of `x ∈ S`
under a subgroup `H ≤ Σ_S` (§20.2, printed p. 159 / PDF p. 167; indexed at `orbit 159`;
correcting the printed bound-variable typo `{σ x : x ∈ H}`). -/
def garlingOrbit {S : Type*} (H : Subgroup (Equiv.Perm S)) (x : S) : Set S :=
  {y : S | ∃ σ ∈ H, σ x = y}

@[simp]
theorem mem_garlingOrbit_iff {S : Type*} (H : Subgroup (Equiv.Perm S)) (x y : S) :
    y ∈ garlingOrbit H x ↔ ∃ σ ∈ H, σ x = y := Iff.rfl

theorem mem_garlingOrbit_self {S : Type*} (H : Subgroup (Equiv.Perm S)) (x : S) :
    x ∈ garlingOrbit H x :=
  ⟨1, H.one_mem, rfl⟩

/-- Orbit equivalence relation `x ~ x' ↔ ∃ σ ∈ H, σ x = x'` (§20.2, printed p. 159). -/
def garlingOrbitSetoid {S : Type*} (H : Subgroup (Equiv.Perm S)) : Setoid S where
  r x y := ∃ σ ∈ H, σ x = y
  iseqv :=
    ⟨fun x => ⟨1, H.one_mem, rfl⟩,
     fun {x _} ⟨σ, hσ, hxy⟩ => ⟨σ⁻¹, H.inv_mem hσ, by rw [← hxy]; exact σ.symm_apply_apply x⟩,
     fun ⟨σ, hσ, hxy⟩ ⟨τ, hτ, hyz⟩ => ⟨τ * σ, H.mul_mem hτ hσ, by simp [hxy, hyz]⟩⟩

/-- Printed p. 159: any two orbits `O_H(x)` and `O_H(y)` are either identical or disjoint. -/
theorem garlingOrbit_eq_or_disjoint {S : Type*} (H : Subgroup (Equiv.Perm S)) (x y : S) :
    garlingOrbit H x = garlingOrbit H y ∨ Disjoint (garlingOrbit H x) (garlingOrbit H y) := by
  by_cases h : (garlingOrbit H x ∩ garlingOrbit H y).Nonempty
  · left
    obtain ⟨z, ⟨σ₁, hσ₁, h1⟩, ⟨σ₂, hσ₂, h2⟩⟩ := h
    ext w
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      exact ⟨ρ * σ₁⁻¹ * σ₂, H.mul_mem (H.mul_mem hρ (H.inv_mem hσ₁)) hσ₂, by
        change ρ (σ₁⁻¹ (σ₂ y)) = ρ x
        rw [h2, ← h1]; exact congrArg ρ (σ₁.symm_apply_apply x)⟩
    · rintro ⟨ρ, hρ, rfl⟩
      exact ⟨ρ * σ₂⁻¹ * σ₁, H.mul_mem (H.mul_mem hρ (H.inv_mem hσ₂)) hσ₁, by
        change ρ (σ₂⁻¹ (σ₁ x)) = ρ y
        rw [h1, ← h2]; exact congrArg ρ (σ₂.symm_apply_apply y)⟩
  · right
    rw [Set.disjoint_iff_inter_eq_empty]
    exact Set.not_nonempty_iff_eq_empty.mp h

/-- **§20.2 Unnumbered Prose Theorem (printed p. 159 / PDF p. 167):**
If `p` is a prime, `G` is a transitive subgroup of `Σ_p`, and `H` is a normal subgroup of `G`
other than `{e}`, then `H` is also a transitive subgroup of `Σ_p`. -/
theorem section_20_2_normal_subgroup_transitive {p : ℕ} (hp : Nat.Prime p)
    {G H : Subgroup (SigmaN p)} (htrans : SubgroupActsTransitively G)
    (hHG : H ≤ G) (hN : (H.subgroupOf G).Normal) (hne : H ≠ ⊥) :
    SubgroupActsTransitively H := by
  classical
  -- Step 1: All `H`-orbits have the same finite cardinality `k`:
  have horb_card_eq : ∀ x y : Fin p, (garlingOrbit H x).ncard = (garlingOrbit H y).ncard := by
    intro x y
    obtain ⟨τ, hτG, hτxy⟩ := htrans x y
    have hconj : ∀ σ ∈ H, τ * σ * τ⁻¹ ∈ H := fun σ hσ => by
      have h1 : (⟨τ, hτG⟩ : G) * ⟨σ, hHG hσ⟩ * ⟨τ, hτG⟩⁻¹ ∈ H.subgroupOf G :=
        hN.conj_mem ⟨σ, hHG hσ⟩ hσ ⟨τ, hτG⟩
      exact h1
    have hconj_inv : ∀ σ ∈ H, τ⁻¹ * σ * τ ∈ H := fun σ hσ => by
      have h1 : (⟨τ⁻¹, G.inv_mem hτG⟩ : G) * ⟨σ, hHG hσ⟩ * (⟨τ⁻¹, G.inv_mem hτG⟩ : G)⁻¹ ∈
          H.subgroupOf G :=
        hN.conj_mem ⟨σ, hHG hσ⟩ hσ ⟨τ⁻¹, G.inv_mem hτG⟩
      change τ⁻¹ * σ * τ⁻¹⁻¹ ∈ H at h1
      rwa [inv_inv] at h1
    let e : garlingOrbit H x ≃ garlingOrbit H y :=
      { toFun := fun u => ⟨τ u.1, by
          obtain ⟨σ, hσ, hσx⟩ := u.2
          refine ⟨τ * σ * τ⁻¹, hconj σ hσ, ?_⟩
          change τ (σ (τ⁻¹ y)) = τ u.1
          rw [← hτxy, show τ⁻¹ (τ x) = x from τ.symm_apply_apply x, hσx]⟩
        invFun := fun v => ⟨τ⁻¹ v.1, by
          obtain ⟨σ, hσ, hσy⟩ := v.2
          refine ⟨τ⁻¹ * σ * τ, hconj_inv σ hσ, ?_⟩
          change τ⁻¹ (σ (τ x)) = τ⁻¹ v.1
          rw [hτxy, hσy]⟩
        left_inv := fun u => Subtype.ext (τ.symm_apply_apply u.1)
        right_inv := fun v => Subtype.ext (τ.apply_symm_apply v.1) }
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr e
  -- Step 2: By the orbit partition, `k ∣ p`:
  let x₀ : Fin p := ⟨0, hp.pos⟩
  let k : ℕ := (garlingOrbit H x₀).ncard
  let orbs : Finset (Finset (Fin p)) :=
    (Finset.univ : Finset (Fin p)).image fun x => (garlingOrbit H x).toFinset
  have horb_fin_card : ∀ s ∈ orbs, s.card = k := by
    intro s hs
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hs
    have h1 := horb_card_eq x x₀
    rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card'] at h1
    dsimp [k]
    rwa [Set.ncard_eq_toFinset_card']
  have horb_disj : (orbs : Set (Finset (Fin p))).PairwiseDisjoint id := by
    intro s₁ hs₁ s₂ hs₂ hne_s
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hs₁
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hs₂
    rcases garlingOrbit_eq_or_disjoint H x y with heq | hdisj
    · exfalso; exact hne_s (by simp [heq])
    · change Disjoint (garlingOrbit H x).toFinset (garlingOrbit H y).toFinset
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb hab
      subst hab
      exact Set.disjoint_left.mp hdisj ((Set.mem_toFinset).mp ha) ((Set.mem_toFinset).mp hb)
  have horb_cover : orbs.biUnion id = Finset.univ := by
    ext x
    simp only [Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
    exact ⟨(garlingOrbit H x).toFinset, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩,
      Set.mem_toFinset.mpr (mem_garlingOrbit_self H x)⟩
  have hkp : orbs.card * k = p := by
    have hcard := Finset.card_biUnion horb_disj
    rw [horb_cover, Finset.card_univ, Fintype.card_fin] at hcard
    simp only [id_eq] at hcard
    rw [Finset.sum_congr rfl (fun s hs => horb_fin_card s hs), Finset.sum_const, smul_eq_mul] at hcard
    exact hcard.symm
  -- Step 3: Since `H ≠ ⊥`, some orbit has ≥ 2 elements, so `k > 1`, forcing `k = p`:
  have hk_gt1 : 1 < k := by
    have hex_ne : ∃ σ ∈ H, σ ≠ 1 := by
      by_contra hall
      push Not at hall
      apply hne
      rw [eq_bot_iff]
      intro σ hσ
      exact Subgroup.mem_bot.mpr (hall σ hσ)
    obtain ⟨σ, hσH, hσ1⟩ := hex_ne
    have hex_move : ∃ y : Fin p, σ y ≠ y := by
      by_contra hfix
      push Not at hfix
      exact hσ1 (Equiv.ext hfix)
    obtain ⟨y, hy⟩ := hex_move
    have h2 : 2 ≤ (garlingOrbit H y).ncard := by
      have hsub : ({y, σ y} : Set (Fin p)) ⊆ garlingOrbit H y := by
        intro z hz
        rcases hz with hz | hz
        · rw [hz]; exact mem_garlingOrbit_self H y
        · rw [hz]; exact ⟨σ, hσH, rfl⟩
      have hcard_pair : ({y, σ y} : Set (Fin p)).ncard = 2 := Set.ncard_pair (Ne.symm hy)
      rw [← hcard_pair]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    have hyk : (garlingOrbit H y).ncard = k := horb_card_eq y x₀
    omega
  have hk_eq_p : k = p := (hp.eq_one_or_self_of_dvd k ⟨orbs.card, by linarith⟩).resolve_left (by omega)
  -- Step 4: Every orbit has size `p` in `Fin p`, hence equals `Set.univ`:
  intro x y
  have hcard_x : (garlingOrbit H x).toFinset.card = Fintype.card (Fin p) := by
    rw [Fintype.card_fin, ← Set.ncard_eq_toFinset_card', horb_card_eq x x₀]
    exact hk_eq_p
  have huniv : (garlingOrbit H x).toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ hcard_x
  have hy_mem : y ∈ (garlingOrbit H x).toFinset := huniv ▸ Finset.mem_univ y
  have hy_set : y ∈ garlingOrbit H x := Set.mem_toFinset.mp hy_mem
  exact hy_set

/-- Group isomorphism `Equiv.Perm α ≃* Equiv.Perm β` induced by conjugation via `e : α ≃ β`. -/
def permCongrMulEquiv {α β : Type*} (e : α ≃ β) : Equiv.Perm α ≃* Equiv.Perm β where
  toEquiv := Equiv.permCongr e
  map_mul' σ τ := by ext x; simp

@[simp]
theorem permCongrMulEquiv_apply {α β : Type*} (e : α ≃ β) (σ : Equiv.Perm α) (y : β) :
    permCongrMulEquiv e σ y = e (σ (e.symm y)) := rfl

@[simp]
theorem permCongrMulEquiv_symm {α β : Type*} (e : α ≃ β) :
    (permCongrMulEquiv e).symm = permCongrMulEquiv e.symm := by
  ext σ x; rfl

/-- Garling's inline italicized definition of an *affine* transformation `τ_{(a,b)}(k) = ak + b`
of `ℤ_p` (`a ∈ ℤ_p^*`, `b ∈ ℤ_p`) (§20.2, printed p. 159 / PDF p. 167; indexed at
`affine transformation 159` and `transformation, affine 159`). -/
def affinePerm {p : ℕ} (a : (ZMod p)ˣ) (b : ZMod p) : Equiv.Perm (ZMod p) where
  toFun k := (a : ZMod p) * k + b
  invFun k := ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (k - b)
  left_inv k := by
    have hinv : ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (a : ZMod p) = 1 := Units.inv_mul a
    calc ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((a : ZMod p) * k + b - b)
        = (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (a : ZMod p)) * k := by ring
      _ = k := by rw [hinv, one_mul]
  right_inv k := by
    have hinv : (a : ZMod p) * ((a⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 := Units.mul_inv a
    calc (a : ZMod p) * (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (k - b)) + b
        = ((a : ZMod p) * ((a⁻¹ : (ZMod p)ˣ) : ZMod p)) * (k - b) + b := by ring
      _ = k := by rw [hinv, one_mul, sub_add_cancel]

@[simp]
theorem affinePerm_apply {p : ℕ} (a : (ZMod p)ˣ) (b k : ZMod p) :
    affinePerm a b k = (a : ZMod p) * k + b := rfl

theorem affinePerm_one (p : ℕ) : affinePerm (1 : (ZMod p)ˣ) (0 : ZMod p) = 1 := by
  ext k; simp

theorem affinePerm_mul {p : ℕ} (a₁ a₂ : (ZMod p)ˣ) (b₁ b₂ : ZMod p) :
    affinePerm a₁ b₁ * affinePerm a₂ b₂ =
      affinePerm (a₁ * a₂) ((a₁ : ZMod p) * b₂ + b₁) := by
  ext k
  change (a₁ : ZMod p) * ((a₂ : ZMod p) * k + b₂) + b₁ =
    ((a₁ * a₂ : (ZMod p)ˣ) : ZMod p) * k + ((a₁ : ZMod p) * b₂ + b₁)
  rw [Units.val_mul]
  ring

theorem affinePerm_inv {p : ℕ} (a : (ZMod p)ˣ) (b : ZMod p) :
    (affinePerm a b)⁻¹ = affinePerm a⁻¹ (-(((a⁻¹ : (ZMod p)ˣ) : ZMod p) * b)) := by
  apply inv_eq_of_mul_eq_one_right
  rw [affinePerm_mul, mul_inv_cancel, mul_neg, ← mul_assoc, Units.mul_inv, one_mul, neg_add_cancel,
    affinePerm_one]

theorem affinePerm_injective {p : ℕ} (a₁ a₂ : (ZMod p)ˣ) (b₁ b₂ : ZMod p)
    (h : affinePerm a₁ b₁ = affinePerm a₂ b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have h0 := Equiv.congr_fun h (0 : ZMod p)
  have h1 := Equiv.congr_fun h (1 : ZMod p)
  simp only [affinePerm_apply, mul_zero, zero_add, mul_one] at h0 h1
  have ha : (a₁ : ZMod p) = (a₂ : ZMod p) := by linear_combination h1 - h0
  exact ⟨Units.ext ha, h0⟩

/-- Garling's subgroup `W_F = {τ_{(a,b)} : a ∈ F, b ∈ ℤ_p} ≤ Σ_{ℤ_p}` for any subgroup
`F ≤ (ℤ_p)^*` (§20.2, printed pp. 159–160). When `F = ⊤`, this is Garling's affine group `W`. -/
def garlingAffineSubgroup {p : ℕ} (F : Subgroup (ZMod p)ˣ) : Subgroup (Equiv.Perm (ZMod p)) where
  carrier := {σ | ∃ (a : (ZMod p)ˣ) (b : ZMod p), a ∈ F ∧ σ = affinePerm a b}
  one_mem' := ⟨1, 0, F.one_mem, (affinePerm_one p).symm⟩
  mul_mem' := by
    rintro _ _ ⟨a₁, b₁, ha₁, rfl⟩ ⟨a₂, b₂, ha₂, rfl⟩
    exact ⟨a₁ * a₂, (a₁ : ZMod p) * b₂ + b₁, F.mul_mem ha₁ ha₂, affinePerm_mul a₁ a₂ b₁ b₂⟩
  inv_mem' := by
    rintro _ ⟨a, b, ha, rfl⟩
    exact ⟨a⁻¹, -(((a⁻¹ : (ZMod p)ˣ) : ZMod p) * b), F.inv_mem ha, affinePerm_inv a b⟩

/-- Garling's full *affine* group `W = {τ_{(a,b)} : a ∈ ℤ_p^*, b ∈ ℤ_p} ≤ Σ_{ℤ_p}`
(§20.2, printed p. 159 / PDF p. 167). -/
abbrev garlingAffineGroup (p : ℕ) : Subgroup (Equiv.Perm (ZMod p)) :=
  garlingAffineSubgroup (⊤ : Subgroup (ZMod p)ˣ)

/-- Translation subgroup `T = {τ_{(1,b)} : b ∈ ℤ_p} ≤ W_F` (§20.2, printed p. 159). -/
abbrev garlingTranslationGroup (p : ℕ) : Subgroup (Equiv.Perm (ZMod p)) :=
  garlingAffineSubgroup (⊥ : Subgroup (ZMod p)ˣ)

theorem garlingAffineSubgroup_card {p : ℕ} (hp : 0 < p) (F : Subgroup (ZMod p)ˣ) :
    Nat.card (garlingAffineSubgroup F) = Nat.card F * p := by
  have : NeZero p := ⟨hp.ne'⟩
  let e : F × ZMod p ≃ garlingAffineSubgroup F :=
    Equiv.ofBijective (fun u => ⟨affinePerm u.1.1 u.2, ⟨u.1.1, u.2, u.1.2, rfl⟩⟩)
      ⟨fun u₁ u₂ hu => by
        obtain ⟨ha, hb⟩ := affinePerm_injective u₁.1.1 u₂.1.1 u₁.2 u₂.2 (congrArg Subtype.val hu)
        exact Prod.ext (Subtype.ext ha) hb,
       fun ⟨_, a, b, ha, hσ⟩ => ⟨(⟨a, ha⟩, b), Subtype.ext hσ.symm⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_zmod]

theorem garlingAffineGroup_card {p : ℕ} (hp : Nat.Prime p) :
    Nat.card (garlingAffineGroup p) = p * (p - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [garlingAffineSubgroup_card hp.pos, Nat.card_congr Subgroup.topEquiv.toEquiv,
    Nat.card_eq_fintype_card, ZMod.card_units p, mul_comm]

/-- Projection homomorphism `τ_{(a,b)} ↦ a` from `W_F` onto `F ≤ (ℤ_p)^*` (§20.2, printed p. 159). -/
noncomputable def garlingAffineProjHom {p : ℕ} (F : Subgroup (ZMod p)ˣ) :
    garlingAffineSubgroup F →* F where
  toFun σ := ⟨σ.2.choose, σ.2.choose_spec.choose_spec.1⟩
  map_one' := by
    apply Subtype.ext
    have hspec := (garlingAffineSubgroup F).one_mem.choose_spec.choose_spec.2
    have h1 : affinePerm (1 : (ZMod p)ˣ) 0 =
        affinePerm (garlingAffineSubgroup F).one_mem.choose
          (garlingAffineSubgroup F).one_mem.choose_spec.choose := by
      rw [affinePerm_one]; exact hspec
    exact (affinePerm_injective _ _ _ _ h1).1.symm
  map_mul' σ₁ σ₂ := by
    apply Subtype.ext
    have h1 := σ₁.2.choose_spec.choose_spec.2
    have h2 := σ₂.2.choose_spec.choose_spec.2
    have h12 := (σ₁ * σ₂).2.choose_spec.choose_spec.2
    have heq : affinePerm (σ₁ * σ₂).2.choose (σ₁ * σ₂).2.choose_spec.choose =
        affinePerm (σ₁.2.choose * σ₂.2.choose)
          ((σ₁.2.choose : ZMod p) * σ₂.2.choose_spec.choose + σ₁.2.choose_spec.choose) := by
      calc affinePerm (σ₁ * σ₂).2.choose (σ₁ * σ₂).2.choose_spec.choose
          = (σ₁ * σ₂ : Equiv.Perm (ZMod p)) := h12.symm
        _ = (σ₁ : Equiv.Perm (ZMod p)) * (σ₂ : Equiv.Perm (ZMod p)) := rfl
        _ = affinePerm σ₁.2.choose σ₁.2.choose_spec.choose *
              affinePerm σ₂.2.choose σ₂.2.choose_spec.choose := congrArg₂ (· * ·) h1 h2
        _ = _ := affinePerm_mul _ _ _ _
    exact (affinePerm_injective _ _ _ _ heq).1

theorem garlingAffineProjHom_apply {p : ℕ} {F : Subgroup (ZMod p)ˣ}
    {a : (ZMod p)ˣ} {b : ZMod p} (ha : a ∈ F) :
    (garlingAffineProjHom F ⟨affinePerm a b, ⟨a, b, ha, rfl⟩⟩ : (ZMod p)ˣ) = a := by
  have hspec := (⟨a, b, ha, rfl⟩ : affinePerm a b ∈ garlingAffineSubgroup F).choose_spec.choose_spec.2
  exact (affinePerm_injective _ _ _ _ hspec.symm).1

theorem garlingAffineProjHom_surjective {p : ℕ} (F : Subgroup (ZMod p)ˣ) :
    Function.Surjective (garlingAffineProjHom F) := fun ⟨a, ha⟩ =>
  ⟨⟨affinePerm a 0, ⟨a, 0, ha, rfl⟩⟩, Subtype.ext (garlingAffineProjHom_apply ha)⟩

/-- Kernel of `garlingAffineProjHom F` is the translation subgroup `T = {τ_{(1,b)}}`, cyclic of
order `p` (for `p > 0`), and `W_F / T ≃* F` (cyclic of order dividing `p - 1` when `p` is prime),
so `W_F` (and in particular `W`) is soluble (§20.2, printed p. 159). -/
theorem garlingAffineSubgroup_properties {p : ℕ} (hp : Nat.Prime p) (F : Subgroup (ZMod p)ˣ) :
    let T : Subgroup (garlingAffineSubgroup F) := (garlingAffineProjHom F).ker
    T.Normal ∧
    (∀ σ : garlingAffineSubgroup F, σ ∈ T ↔ ∃ b : ZMod p, (σ : Equiv.Perm (ZMod p)) = affinePerm 1 b) ∧
    SubgroupActsTransitively (T.map (garlingAffineSubgroup F).subtype) ∧
    IsCyclic T ∧
    Nat.card T = p ∧
    Nonempty ((garlingAffineSubgroup F ⧸ T) ≃* F) ∧
    IsCyclic (garlingAffineSubgroup F ⧸ T) ∧
    Nat.card (garlingAffineSubgroup F ⧸ T) ∣ p - 1 ∧
    IsGarlingSoluble (garlingAffineSubgroup F) := by
  have : Fact p.Prime := ⟨hp⟩
  intro T
  have hT_norm : T.Normal := MonoidHom.normal_ker _
  have hT_mem : ∀ σ : garlingAffineSubgroup F,
      σ ∈ T ↔ ∃ b : ZMod p, (σ : Equiv.Perm (ZMod p)) = affinePerm 1 b := by
    intro σ
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      obtain ⟨a, b, ha, hσ⟩ := σ.2
      have ha1 : a = 1 := by
        have hproj : (garlingAffineProjHom F σ : (ZMod p)ˣ) = a := by
          have : σ = ⟨affinePerm a b, ⟨a, b, ha, rfl⟩⟩ := Subtype.ext hσ
          rw [this]; exact garlingAffineProjHom_apply ha
        rw [← hproj, h1]; rfl
      exact ⟨b, by rw [hσ, ha1]⟩
    · rintro ⟨b, hσ⟩
      apply Subtype.ext
      have : σ = ⟨affinePerm 1 b, ⟨1, b, F.one_mem, rfl⟩⟩ := Subtype.ext hσ
      rw [this]
      exact garlingAffineProjHom_apply F.one_mem
  have hT_trans : SubgroupActsTransitively (T.map (garlingAffineSubgroup F).subtype) := by
    intro x y
    refine ⟨affinePerm 1 (y - x), ⟨⟨affinePerm 1 (y - x), ⟨1, y - x, F.one_mem, rfl⟩⟩,
      (hT_mem _).mpr ⟨y - x, rfl⟩, rfl⟩, ?_⟩
    simp
  -- `T ≃* Multiplicative (ZMod p)`:
  let eT : Multiplicative (ZMod p) ≃* T :=
    { toFun := fun b =>
        ⟨⟨affinePerm 1 (Multiplicative.toAdd b), ⟨1, Multiplicative.toAdd b, F.one_mem, rfl⟩⟩,
         (hT_mem _).mpr ⟨Multiplicative.toAdd b, rfl⟩⟩
      invFun := fun σ => Multiplicative.ofAdd (((σ : garlingAffineSubgroup F) : Equiv.Perm (ZMod p)) 0)
      left_inv := fun b => by
        change Multiplicative.ofAdd (((1 : (ZMod p)ˣ) : ZMod p) * 0 + Multiplicative.toAdd b) = b
        simp
      right_inv := fun σ => by
        obtain ⟨b, hb⟩ := (hT_mem σ.1).mp σ.2
        apply Subtype.ext; apply Subtype.ext
        change affinePerm 1 (σ.1.1 0) = σ.1.1
        rw [hb]; simp
      map_mul' := fun b₁ b₂ => by
        apply Subtype.ext; apply Subtype.ext
        change affinePerm 1 (Multiplicative.toAdd b₁ + Multiplicative.toAdd b₂) =
          affinePerm 1 (Multiplicative.toAdd b₁) * affinePerm 1 (Multiplicative.toAdd b₂)
        rw [affinePerm_mul]; simp [add_comm] }
  have hT_cyc : IsCyclic T := isCyclic_of_surjective eT.toMonoidHom eT.surjective
  have hT_card : Nat.card T = p := by
    rw [← Nat.card_congr eT.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  let eQ : (garlingAffineSubgroup F ⧸ T) ≃* F :=
    QuotientGroup.quotientKerEquivOfSurjective (garlingAffineProjHom F)
      (garlingAffineProjHom_surjective F)
  have hU_cyc : IsCyclic (ZMod p)ˣ := (corollary_1_to_theorem_12_3 (ZMod p)).1
  have hF_cyc : IsCyclic F := inferInstance
  have hQ_cyc : IsCyclic (garlingAffineSubgroup F ⧸ T) :=
    isCyclic_of_surjective eQ.symm.toMonoidHom eQ.symm.surjective
  have hQ_dvd : Nat.card (garlingAffineSubgroup F ⧸ T) ∣ p - 1 := by
    rw [Nat.card_congr eQ.toEquiv]
    have hdvd : Nat.card F ∣ Nat.card (ZMod p)ˣ := Subgroup.card_subgroup_dvd_card F
    rwa [Nat.card_eq_fintype_card (α := (ZMod p)ˣ), ZMod.card_units p] at hdvd
  have hsol : IsGarlingSoluble (garlingAffineSubgroup F) :=
    (theorem_17_2_ii T).mpr ⟨isGarlingSoluble_of_isCyclic, isGarlingSoluble_of_isCyclic⟩
  exact ⟨hT_norm, hT_mem, hT_trans, hT_cyc, hT_card, ⟨eQ⟩, hQ_cyc, hQ_dvd, hsol⟩

theorem garlingAffineGroup_soluble {p : ℕ} (hp : Nat.Prime p) :
    IsGarlingSoluble (garlingAffineGroup p) :=
  (garlingAffineSubgroup_properties hp ⊤).2.2.2.2.2.2.2.2

/-- Core §20.2 structural theorem (Garling's exact pp. 159–160 proof): every soluble transitive
subgroup `G ≤ Σ_p` (`p` prime) is conjugate via a relabelling `e : Fin p ≃ ZMod p` to a subgroup
`W_F = {τ_{(a,b)} : a ∈ F, b ∈ ℤ_p}` for a unique subgroup `F ≤ (ℤ_p)^*`. -/
theorem soluble_transitive_prime_eq_conj_affine {p : ℕ} (hp : Nat.Prime p)
    {G : Subgroup (SigmaN p)} (htrans : SubgroupActsTransitively G)
    (hsol : IsGarlingSoluble G) :
    ∃ (F : Subgroup (ZMod p)ˣ) (e : Fin p ≃ ZMod p),
      G = (garlingAffineSubgroup F).map (permCongrMulEquiv e.symm).toMonoidHom := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  rcases hsol with ⟨r, H, hH0, hHlast, hHle, hHstep⟩
  have hG_nontriv : (⊤ : Subgroup G) ≠ ⊥ := by
    intro htop
    have hx0 : (⟨0, hp.pos⟩ : Fin p) ≠ ⟨1, hp.one_lt⟩ := by
      intro h; exact Nat.zero_ne_one (congrArg Fin.val h)
    obtain ⟨σ, hσG, hσ01⟩ := htrans ⟨0, hp.pos⟩ ⟨1, hp.one_lt⟩
    have hmem_bot : (⟨σ, hσG⟩ : G) ∈ (⊥ : Subgroup G) := htop ▸ Subgroup.mem_top _
    have h1 : σ = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hmem_bot)
    rw [h1, Equiv.Perm.coe_one, id_eq] at hσ01
    exact hx0 hσ01
  have hH_anti : ∀ {a b : ℕ} (ha : a ≤ r) (hb : b ≤ r), a ≤ b →
      H ⟨b, Nat.lt_succ_of_le hb⟩ ≤ H ⟨a, Nat.lt_succ_of_le ha⟩ := by
    intro a b ha hb hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ m hle ihm =>
      have hm_lt : m < r := Nat.lt_of_succ_le hb
      let j : Fin r := ⟨m, hm_lt⟩
      exact (hHle j).trans (ihm (Nat.le_of_lt hm_lt))
  have hex_k : ∃ k : Fin r, H k.castSucc ≠ ⊥ ∧ H k.succ = ⊥ := by
    have h0_ne : H 0 ≠ ⊥ := hH0.symm ▸ hG_nontriv
    have hex_bot : ∃ m : ℕ, ∃ hm : m ≤ r, H ⟨m, Nat.lt_succ_of_le hm⟩ = ⊥ :=
      ⟨r, le_rfl, hHlast⟩
    let m := Nat.find hex_bot
    obtain ⟨hm_le, hm_eq⟩ := Nat.find_spec hex_bot
    have hm_pos : 0 < m := by
      by_contra h0
      have hm0 : m = 0 := by omega
      apply h0_ne
      have hfin : (⟨m, Nat.lt_succ_of_le hm_le⟩ : Fin (r + 1)) = 0 := Fin.ext hm0
      rwa [hfin] at hm_eq
    let k : Fin r := ⟨m - 1, by omega⟩
    have hk_ne : H k.castSucc ≠ ⊥ := by
      intro hbot
      have hlt : m - 1 < m := by omega
      exact Nat.find_min hex_bot hlt ⟨by omega, hbot⟩
    have hk_succ : H k.succ = ⊥ := by
      have hfin : k.succ = ⟨m, Nat.lt_succ_of_le hm_le⟩ := Fin.ext (by dsimp [k]; omega)
      rwa [hfin]
    exact ⟨k, hk_ne, hk_succ⟩
  obtain ⟨k, hk_ne, hk_succ⟩ := hex_k
  let K : Fin (r + 1) → Subgroup (SigmaN p) := fun j => (H j).map G.subtype
  have hK_le : ∀ j : Fin r, K j.succ ≤ K j.castSucc := fun j => Subgroup.map_mono (hHle j)
  have hK_norm : ∀ j : Fin r, ((K j.succ).subgroupOf (K j.castSucc)).Normal := by
    intro j
    obtain ⟨hNj, _⟩ := hHstep j
    have : ((H j.succ).subgroupOf (H j.castSucc)).Normal := hNj
    let ψ : H j.castSucc ≃* K j.castSucc :=
      MulEquiv.ofBijective (G.subtype.subgroupMap (H j.castSucc))
        ⟨fun a b hab =>
          Subtype.ext (Subtype.ext (congrArg (fun x : K j.castSucc => (x : SigmaN p)) hab)),
         fun ⟨_, ⟨x, hx, rfl⟩⟩ => ⟨⟨x, hx⟩, rfl⟩⟩
    have hmap : ((H j.succ).subgroupOf (H j.castSucc)).map ψ.toMonoidHom =
        (K j.succ).subgroupOf (K j.castSucc) := by
      ext ⟨y, hy⟩
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, K, ψ]
      constructor
      · rintro ⟨⟨x, hx⟩, hxs, heq⟩
        exact ⟨x, hxs, congrArg Subtype.val heq⟩
      · rintro ⟨x, hxs, hxy⟩
        exact ⟨⟨x, hHle j hxs⟩, hxs, Subtype.ext hxy⟩
    rw [← hmap]
    exact hNj.map ψ.toMonoidHom ψ.surjective
  have hK_trans : ∀ (j : ℕ) (hj : j ≤ k.1),
      SubgroupActsTransitively (K ⟨j, by omega⟩) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hK0 : K 0 = G := by ext g; simp [K, hH0]
      exact hK0 ▸ htrans
    | succ j ih =>
      intro hj
      let i : Fin r := ⟨j, by omega⟩
      have hprev := ih (by omega)
      have hne_i : K i.succ ≠ ⊥ := by
        intro hbot
        apply hk_ne
        have hle_ik : H k.castSucc ≤ H i.succ := hH_anti (by omega) (by omega) (by omega)
        rw [eq_bot_iff]
        intro x hx
        have hx' : (x : SigmaN p) ∈ K i.succ := ⟨x, hle_ik hx, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hx'
        exact Subgroup.mem_bot.mpr (Subtype.ext hx')
      exact section_20_2_normal_subgroup_transitive hp hprev (hK_le i) (hK_norm i) hne_i
  let T : Subgroup (SigmaN p) := K k.castSucc
  have hT_trans : SubgroupActsTransitively T := hK_trans k.1 le_rfl
  have hT_cyc : IsCyclic T := by
    obtain ⟨hNk, hCyc⟩ := hHstep k
    have : ((H k.succ).subgroupOf (H k.castSucc)).Normal := hNk
    have hbot : (H k.succ).subgroupOf (H k.castSucc) = ⊥ := by
      ext ⟨x, hx⟩; simp [hk_succ]
    let e1 : H k.castSucc ≃* (H k.castSucc ⧸ (H k.succ).subgroupOf (H k.castSucc)) :=
      (QuotientGroup.quotientBot.symm).trans
        (QuotientGroup.quotientMulEquivOfEq hbot.symm)
    let e2 : H k.castSucc ≃* T :=
      MulEquiv.ofBijective (G.subtype.subgroupMap (H k.castSucc))
        ⟨fun a b hab =>
          Subtype.ext (Subtype.ext (congrArg (fun x : T => (x : SigmaN p)) hab)),
         fun ⟨_, ⟨x, hx, rfl⟩⟩ => ⟨⟨x, hx⟩, rfl⟩⟩
    exact isCyclic_of_surjective (e1.symm.trans e2).toMonoidHom (e1.symm.trans e2).surjective
  obtain ⟨⟨σ, hσT⟩, hσ_gen⟩ := IsCyclic.exists_generator (α := T)
  have hT_card : Nat.card T = p := by
    let x₀ : Fin p := ⟨0, hp.pos⟩
    have hmap_bij : Function.Bijective (fun g : T => g.1 x₀) := by
      refine ⟨fun g₁ g₂ h12 => ?_, fun y => by
        obtain ⟨g, hgT, hgy⟩ := hT_trans x₀ y
        exact ⟨⟨g, hgT⟩, hgy⟩⟩
      apply Subtype.ext
      refine Equiv.ext fun y => ?_
      obtain ⟨h, hhT, hhy⟩ := hT_trans x₀ y
      have hcomm : ∀ a b : T, a.1 * b.1 = b.1 * a.1 := fun a b => by
        obtain ⟨ma, rfl⟩ := hσ_gen a
        obtain ⟨mb, rfl⟩ := hσ_gen b
        change (σ ^ ma) * (σ ^ mb) = (σ ^ mb) * (σ ^ ma)
        rw [← zpow_add, ← zpow_add, add_comm]
      have h1 : g₁.1 (h x₀) = h (g₁.1 x₀) :=
        congrArg (fun f : SigmaN p => f x₀) (hcomm g₁ ⟨h, hhT⟩)
      have h2 : g₂.1 (h x₀) = h (g₂.1 x₀) :=
        congrArg (fun f : SigmaN p => f x₀) (hcomm g₂ ⟨h, hhT⟩)
      rw [← hhy, h1, h2]
      exact congrArg h h12
    rw [Nat.card_congr (Equiv.ofBijective _ hmap_bij), Nat.card_eq_fintype_card, Fintype.card_fin]
  have hσ_ord : orderOf σ = p := by
    have h1 : orderOf (⟨σ, hσT⟩ : T) = Nat.card T := by
      rw [← Nat.card_zpowers, show Subgroup.zpowers (⟨σ, hσT⟩ : T) = ⊤ from
        eq_top_iff.mpr fun x _ => hσ_gen x]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [hT_card, Subgroup.orderOf_mk] at h1
    exact h1
  let x₀ : Fin p := ⟨0, hp.pos⟩
  let e_inv_fun : ZMod p → Fin p := fun z => (σ ^ z.val) x₀
  have he_inv_bij : Function.Bijective e_inv_fun := by
    have hcard_eq : Fintype.card (ZMod p) = Fintype.card (Fin p) := by simp
    refine (Fintype.bijective_iff_injective_and_card e_inv_fun).mpr ⟨?_, hcard_eq⟩
    intro z₁ z₂ h12
    have h12' : (σ ^ z₁.val) x₀ = (σ ^ z₂.val) x₀ := h12
    have hpow : σ ^ z₁.val = σ ^ z₂.val := by
      have hmem1 : σ ^ z₁.val ∈ T := T.pow_mem hσT _
      have hmem2 : σ ^ z₂.val ∈ T := T.pow_mem hσT _
      have hcomm : ∀ a b : T, a.1 * b.1 = b.1 * a.1 := fun a b => by
        obtain ⟨ma, rfl⟩ := hσ_gen a
        obtain ⟨mb, rfl⟩ := hσ_gen b
        change (σ ^ ma) * (σ ^ mb) = (σ ^ mb) * (σ ^ ma)
        rw [← zpow_add, ← zpow_add, add_comm]
      refine Equiv.ext fun y => ?_
      obtain ⟨h, hhT, hhy⟩ := hT_trans x₀ y
      have h1 : (σ ^ z₁.val) (h x₀) = h ((σ ^ z₁.val) x₀) :=
        congrArg (fun f : SigmaN p => f x₀) (hcomm ⟨_, hmem1⟩ ⟨h, hhT⟩)
      have h2 : (σ ^ z₂.val) (h x₀) = h ((σ ^ z₂.val) x₀) :=
        congrArg (fun f : SigmaN p => f x₀) (hcomm ⟨_, hmem2⟩ ⟨h, hhT⟩)
      rw [← hhy, h1, h2]
      exact congrArg h h12'
    have hlt1 : z₁.val < orderOf σ := by rw [hσ_ord]; exact z₁.val_lt
    have hlt2 : z₂.val < orderOf σ := by rw [hσ_ord]; exact z₂.val_lt
    have hval_eq : z₁.val = z₂.val := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hdiff : σ ^ (z₂.val - z₁.val) = 1 := by
          apply mul_left_cancel (a := σ ^ z₁.val)
          rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one, hpow]
        have hdvd := orderOf_dvd_of_pow_eq_one hdiff
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      · have hdiff : σ ^ (z₁.val - z₂.val) = 1 := by
          apply mul_left_cancel (a := σ ^ z₂.val)
          rw [← pow_add, Nat.add_sub_cancel' hgt.le, mul_one, hpow]
        have hdvd := orderOf_dvd_of_pow_eq_one hdiff
        have := Nat.le_of_dvd (by omega) hdvd
        omega
    exact ZMod.val_injective p hval_eq
  let e : Fin p ≃ ZMod p := (Equiv.ofBijective e_inv_fun he_inv_bij).symm
  let conjE : SigmaN p ≃* Equiv.Perm (ZMod p) := permCongrMulEquiv e
  have hconjE_σ : conjE σ = affinePerm 1 1 := by
    ext z
    rw [permCongrMulEquiv_apply, affinePerm_apply, Units.val_one, one_mul]
    apply e.symm.injective
    rw [e.symm_apply_apply]
    change σ ((σ ^ z.val) x₀) = (σ ^ (z + 1).val) x₀
    have hstep_pow : σ ((σ ^ z.val) x₀) = (σ ^ (z.val + 1)) x₀ := by
      rw [pow_succ']; rfl
    rw [hstep_pow]
    have hpow_mod : σ ^ (z.val + 1) = σ ^ ((z.val + 1) % p) := by
      have hdiv := Nat.div_add_mod (z.val + 1) p
      have hσp : σ ^ p = 1 := (congrArg (fun n => σ ^ n) hσ_ord).symm.trans (pow_orderOf_eq_one σ)
      conv_lhs => rw [← hdiv, pow_add, pow_mul, hσp, one_pow, one_mul]
    rw [hpow_mod, ← ZMod.val_natCast (n := p) (z.val + 1)]
    congr 2
    simp
  let L : Fin (r + 1) → Subgroup (Equiv.Perm (ZMod p)) := fun j => (K j).map conjE.toMonoidHom
  have hLk_eq : L k.castSucc = garlingTranslationGroup p := by
    apply le_antisymm
    · rintro _ ⟨g, hgT, rfl⟩
      obtain ⟨m, hm⟩ := hσ_gen ⟨g, hgT⟩
      have hgm : g = σ ^ m := (congrArg Subtype.val hm).symm
      change conjE g ∈ garlingTranslationGroup p
      rw [hgm, map_zpow, hconjE_σ]
      exact (garlingTranslationGroup p).zpow_mem ⟨1, 1, Subgroup.one_mem _, rfl⟩ m
    · rintro _ ⟨a, b, ha, rfl⟩
      have ha1 : a = 1 := Subgroup.mem_bot.mp ha
      subst ha1
      refine ⟨σ ^ b.val, T.pow_mem hσT b.val, ?_⟩
      change conjE (σ ^ b.val) = affinePerm 1 b
      rw [map_pow, hconjE_σ]
      have hpow_tr : ∀ n : ℕ, (affinePerm (1 : (ZMod p)ˣ) 1) ^ n = affinePerm 1 (n : ZMod p) := by
        intro n
        induction n with
        | zero => simp [affinePerm_one]
        | succ n ihn =>
          rw [pow_succ, ihn, affinePerm_mul]
          simp [add_comm]
      rw [hpow_tr, ZMod.natCast_zmod_val]
  have hL_le_W : ∀ (d : ℕ) (hd : d ≤ k.1), L ⟨k.1 - d, by omega⟩ ≤ garlingAffineGroup p := by
    intro d
    induction d with
    | zero =>
      intro _
      have hidx : (⟨k.1 - 0, by omega⟩ : Fin (r + 1)) = k.castSucc := Fin.ext (by simp)
      rw [hidx, hLk_eq]
      rintro _ ⟨a, b, _, rfl⟩
      exact ⟨a, b, Subgroup.mem_top _, rfl⟩
    | succ d ih =>
      intro hd
      have hprev := ih (by omega)
      let j : Fin r := ⟨k.1 - (d + 1), by omega⟩
      have hj_succ : j.succ = ⟨k.1 - d, by omega⟩ := Fin.ext (by dsimp [j]; omega)
      have hj_cast : j.castSucc = ⟨k.1 - (d + 1), by omega⟩ := rfl
      rw [← hj_cast]
      have hLj_le_W : L j.succ ≤ garlingAffineGroup p := hj_succ ▸ hprev
      have hσ_in_Lj : affinePerm (1 : (ZMod p)ˣ) 1 ∈ L j.succ := by
        have hle_H : H k.castSucc ≤ H j.succ :=
          hH_anti (a := j.succ.1) (b := k.castSucc.1) (by simp [j]; omega) (Nat.le_of_lt k.2)
            (by simp [j]; omega)
        have hle_jk : L k.castSucc ≤ L j.succ :=
          Subgroup.map_mono (Subgroup.map_mono hle_H)
        have hmem_k : affinePerm (1 : (ZMod p)ˣ) 1 ∈ L k.castSucc := by
          rw [hLk_eq]; exact ⟨1, 1, Subgroup.one_mem _, rfl⟩
        exact hle_jk hmem_k
      have hL_norm : ((L j.succ).subgroupOf (L j.castSucc)).Normal := by
        have hN := hK_norm j
        let ψ : K j.castSucc ≃* L j.castSucc := conjE.subgroupMap (K j.castSucc)
        have hmap : ((K j.succ).subgroupOf (K j.castSucc)).map ψ.toMonoidHom =
            (L j.succ).subgroupOf (L j.castSucc) := by
          ext ⟨y, hy⟩
          simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, L, ψ]
          constructor
          · rintro ⟨⟨x, hx⟩, hxs, heq⟩
            exact ⟨x, hxs, congrArg Subtype.val heq⟩
          · rintro ⟨x, hxs, hxy⟩
            exact ⟨⟨x, hK_le j hxs⟩, hxs, Subtype.ext hxy⟩
        rw [← hmap]
        exact hN.map ψ.toMonoidHom ψ.surjective
      intro τ hτ
      have hconj_in : τ * affinePerm (1 : (ZMod p)ˣ) 1 * τ⁻¹ ∈ L j.succ := by
        have h1 := hL_norm.conj_mem ⟨affinePerm 1 1, Subgroup.map_mono (hK_le j)
          (by obtain ⟨x, hx, hxe⟩ := hσ_in_Lj; exact ⟨x, hx, hxe⟩)⟩ hσ_in_Lj ⟨τ, hτ⟩
        exact h1
      obtain ⟨a, b, _, hconj_eq⟩ := hLj_le_W hconj_in
      have hnofix : ∀ z : ZMod p, (τ * affinePerm (1 : (ZMod p)ˣ) 1 * τ⁻¹) z ≠ z := by
        intro z hfix
        have h1 : affinePerm (1 : (ZMod p)ˣ) 1 (τ⁻¹ z) = τ⁻¹ z := by
          apply τ.injective
          simpa using hfix
        simp only [affinePerm_apply, Units.val_one, one_mul, add_eq_left] at h1
        exact one_ne_zero h1
      have ha1 : a = 1 := by
        by_contra hne1
        have ha_sub : (a : ZMod p) - 1 ≠ 0 := sub_ne_zero.mpr (fun h => hne1 (Units.ext h))
        let z₀ : ZMod p := -b * ((a : ZMod p) - 1)⁻¹
        apply hnofix z₀
        rw [hconj_eq, affinePerm_apply]
        have hmul : ((a : ZMod p) - 1) * ((a : ZMod p) - 1)⁻¹ = 1 := mul_inv_cancel₀ ha_sub
        calc (a : ZMod p) * z₀ + b
            = ((a : ZMod p) - 1) * z₀ + z₀ + b := by ring
          _ = (((a : ZMod p) - 1) * ((a : ZMod p) - 1)⁻¹) * (-b) + z₀ + b := by dsimp [z₀]; ring
          _ = z₀ := by rw [hmul]; ring
      have hb0 : b ≠ 0 := by
        intro hb0'
        apply hnofix 0
        rw [hconj_eq, ha1, hb0', affinePerm_apply]
        simp
      have hstep_τ : ∀ z : ZMod p, τ (z + 1) = τ z + b := by
        intro z
        have h1 := Equiv.congr_fun hconj_eq (τ z)
        change τ (affinePerm (1 : (ZMod p)ˣ) 1 (τ⁻¹ (τ z))) = (a : ZMod p) * τ z + b at h1
        rw [ha1, Units.val_one, one_mul, show τ⁻¹ (τ z) = z from τ.symm_apply_apply z] at h1
        simpa [affinePerm_apply] using h1
      have hτ_nat : ∀ m : ℕ, τ (m : ZMod p) = b * (m : ZMod p) + τ 0 := by
        intro m
        induction m with
        | zero => simp
        | succ m ihm =>
          push_cast
          rw [hstep_τ, ihm]
          ring
      have hτ_eq : τ = affinePerm (Units.mk0 b hb0) (τ 0) := by
        ext z
        rw [← ZMod.natCast_zmod_val z, hτ_nat, affinePerm_apply, Units.val_mk0]
      exact ⟨Units.mk0 b hb0, τ 0, Subgroup.mem_top _, hτ_eq⟩
  have hL0_le_W : L 0 ≤ garlingAffineGroup p := by
    have h := hL_le_W k.1 le_rfl
    have h0 : (⟨k.1 - k.1, by omega⟩ : Fin (r + 1)) = 0 := Fin.ext (by simp)
    exact h0 ▸ h
  have hT_le_L0 : garlingTranslationGroup p ≤ L 0 := by
    rw [← hLk_eq]
    refine Subgroup.map_mono (Subgroup.map_mono ?_)
    rw [hH0]; exact le_top
  let inclW : L 0 →* garlingAffineGroup p := Subgroup.inclusion hL0_le_W
  let F : Subgroup (ZMod p)ˣ :=
    ((garlingAffineProjHom (⊤ : Subgroup (ZMod p)ˣ)).comp inclW).range.map
      (⊤ : Subgroup (ZMod p)ˣ).subtype
  have hL0_eq_WF : L 0 = garlingAffineSubgroup F := by
    ext σ
    constructor
    · intro hσ
      obtain ⟨a, b, _, hσ_eq⟩ := hL0_le_W hσ
      refine ⟨a, b, ?_, hσ_eq⟩
      refine ⟨⟨a, Subgroup.mem_top _⟩, ⟨⟨σ, hσ⟩, ?_⟩, rfl⟩
      apply Subtype.ext
      change (garlingAffineProjHom ⊤ ⟨σ, hL0_le_W hσ⟩ : (ZMod p)ˣ) = a
      have : (⟨σ, hL0_le_W hσ⟩ : garlingAffineGroup p) =
          ⟨affinePerm a b, ⟨a, b, Subgroup.mem_top _, rfl⟩⟩ := Subtype.ext hσ_eq
      rw [this]
      exact garlingAffineProjHom_apply (Subgroup.mem_top a)
    · rintro ⟨a, b, haF, rfl⟩
      obtain ⟨⟨a', _⟩, ⟨⟨τ, hτL0⟩, hτ_proj⟩, ha'a⟩ := haF
      change a' = a at ha'a
      subst ha'a
      obtain ⟨a₀, b₀, _, hτ_eq⟩ := hL0_le_W hτL0
      have ha₀ : a₀ = a' := by
        have h1 : (garlingAffineProjHom ⊤ ⟨τ, hL0_le_W hτL0⟩ : (ZMod p)ˣ) = a₀ := by
          have : (⟨τ, hL0_le_W hτL0⟩ : garlingAffineGroup p) =
              ⟨affinePerm a₀ b₀, ⟨a₀, b₀, Subgroup.mem_top _, rfl⟩⟩ := Subtype.ext hτ_eq
          rw [this]
          exact garlingAffineProjHom_apply (Subgroup.mem_top a₀)
        exact h1.symm.trans (congrArg Subtype.val hτ_proj)
      subst ha₀
      have htr : affinePerm (1 : (ZMod p)ˣ) (b - b₀) ∈ L 0 :=
        hT_le_L0 ⟨1, b - b₀, Subgroup.one_mem _, rfl⟩
      have hprod : affinePerm (1 : (ZMod p)ˣ) (b - b₀) * τ = affinePerm a₀ b := by
        rw [hτ_eq, affinePerm_mul]
        simp
      rw [← hprod]
      exact (L 0).mul_mem htr hτL0
  refine ⟨F, e, ?_⟩
  have hK0 : K 0 = G := by ext g; simp [K, hH0]
  rw [← hL0_eq_WF]
  ext σ
  simp only [L, hK0, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · intro hσG
    refine ⟨conjE σ, ⟨σ, hσG, rfl⟩, ?_⟩
    refine Equiv.ext fun x => ?_
    simp [conjE]
  · rintro ⟨_, ⟨ρ, hρG, rfl⟩, heq⟩
    have hρσ : ρ = σ := by
      rw [← heq]
      refine Equiv.ext fun x => ?_
      simp [conjE]
    rwa [← hρσ]

/-- **Theorem 20.3 — Clauses 1 & 2** (§20.2, printed p. 160 / PDF p. 168):
*"Suppose that `G` is a soluble transitive subgroup of `Σ_p` (where `p` is a prime). `G` contains a
normal transitive cyclic subgroup `T` of order `p`, and `G/T` is cyclic, with order dividing
`p - 1`."*

These two clauses hold literally for every prime `p` (including `p = 2`). -/
theorem theorem_20_3_clauses_1_and_2 {p : ℕ} (hp : Nat.Prime p)
    {G : Subgroup (SigmaN p)} (htrans : SubgroupActsTransitively G)
    (hsol : IsGarlingSoluble G) :
    ∃ (T : Subgroup G) (_ : T.Normal),
      SubgroupActsTransitively (T.map G.subtype) ∧
      IsCyclic T ∧
      Nat.card T = p ∧
      IsCyclic (G ⧸ T) ∧
      Nat.card (G ⧸ T) ∣ p - 1 := by
  obtain ⟨F, e, hG_eq⟩ := soluble_transitive_prime_eq_conj_affine hp htrans hsol
  obtain ⟨hTN, _, hT_trans, hT_cyc, hT_card, _, hQ_cyc, hQ_dvd, _⟩ :=
    garlingAffineSubgroup_properties hp F
  let φ : garlingAffineSubgroup F ≃* G :=
    ((permCongrMulEquiv e.symm).subgroupMap (garlingAffineSubgroup F)).trans
      (MulEquiv.subgroupCongr hG_eq.symm)
  let T₀ : Subgroup (garlingAffineSubgroup F) := (garlingAffineProjHom F).ker
  let T : Subgroup G := T₀.map φ.toMonoidHom
  have hT_norm : T.Normal := hTN.map φ.toMonoidHom φ.surjective
  have hT_map_trans : SubgroupActsTransitively (T.map G.subtype) := by
    intro x y
    obtain ⟨σ, ⟨τ, hτmem, hτσ⟩, hσxy⟩ := hT_trans (e x) (e y)
    refine ⟨(permCongrMulEquiv e.symm) σ, ?_, ?_⟩
    · refine ⟨φ τ, ⟨τ, hτmem, rfl⟩, ?_⟩
      change permCongrMulEquiv e.symm (τ : Equiv.Perm (ZMod p)) = permCongrMulEquiv e.symm σ
      exact congrArg (permCongrMulEquiv e.symm) hτσ
    · rw [permCongrMulEquiv_apply, Equiv.symm_symm, hσxy, e.symm_apply_apply]
  have eTT : T₀ ≃* T := φ.subgroupMap T₀
  have hT_cyc' : IsCyclic T := isCyclic_of_surjective eTT.toMonoidHom eTT.surjective
  have hT_card' : Nat.card T = p := (Nat.card_congr eTT.symm.toEquiv).trans hT_card
  let eQ : (garlingAffineSubgroup F ⧸ T₀) ≃* (G ⧸ T) :=
    QuotientGroup.congr T₀ T φ rfl
  have hQ_cyc' : IsCyclic (G ⧸ T) := isCyclic_of_surjective eQ.toMonoidHom eQ.surjective
  have hQ_dvd' : Nat.card (G ⧸ T) ∣ p - 1 := by
    rwa [← Nat.card_congr eQ.toEquiv]
  exact ⟨T, hT_norm, hT_map_trans, hT_cyc', hT_card', hQ_cyc', hQ_dvd'⟩

/-- **Theorem 20.3 — Refutation of literal printed Clause 3** (§20.2, printed p. 160 / PDF p. 168;
`QUEUE.md` fidelity hold). -/
theorem theorem_20_3_printed_swap_counterexample {p : ℕ} (hp : Nat.Prime p)
    (F : Subgroup (ZMod p)ˣ) :
    let printedSet : Set (ZMod p → ZMod p) :=
      {f | ∃ (a : ZMod p) (b : (ZMod p)ˣ), b ∈ F ∧ ∀ k : ZMod p, f k = a * k + (b : ZMod p)}
    (∃ f ∈ printedSet, ¬ Function.Injective f) ∧
    (id ∉ printedSet) := by
  have : Fact p.Prime := ⟨hp⟩
  intro printedSet
  refine ⟨⟨fun _ => (1 : ZMod p), ⟨0, 1, F.one_mem, fun k => by simp⟩, fun hinj => ?_⟩, ?_⟩
  · exact zero_ne_one (hinj (rfl : (1 : ZMod p) = 1))
  · rintro ⟨a, b, _, hid⟩
    have h0 := hid 0
    simp only [id_eq, mul_zero, zero_add] at h0
    exact b.ne_zero h0.symm

/-- **Theorem 20.3 (Repaired)** (§20.2, printed p. 160 / PDF p. 168; `QUEUE.md` fidelity hold). -/
theorem theorem_20_3_repaired {p : ℕ} (hp : Nat.Prime p)
    {G : Subgroup (SigmaN p)} (htrans : SubgroupActsTransitively G)
    (hsol : IsGarlingSoluble G) :
    (∃ (T : Subgroup G) (_ : T.Normal),
      SubgroupActsTransitively (T.map G.subtype) ∧
      IsCyclic T ∧
      Nat.card T = p ∧
      IsCyclic (G ⧸ T) ∧
      Nat.card (G ⧸ T) ∣ p - 1) ∧
    (∃ (F : Subgroup (ZMod p)ˣ) (e : Fin p ≃ ZMod p),
      G = (garlingAffineSubgroup F).map (permCongrMulEquiv e.symm).toMonoidHom ∧
      Nonempty (G ≃* garlingAffineSubgroup F)) ∧
    Nat.card G ∣ p * (p - 1) := by
  have h12 := theorem_20_3_clauses_1_and_2 hp htrans hsol
  obtain ⟨F, e, hG_eq⟩ := soluble_transitive_prime_eq_conj_affine hp htrans hsol
  let φ : garlingAffineSubgroup F ≃* G :=
    ((permCongrMulEquiv e.symm).subgroupMap (garlingAffineSubgroup F)).trans
      (MulEquiv.subgroupCongr hG_eq.symm)
  have hdvd : Nat.card G ∣ p * (p - 1) := by
    rw [← Nat.card_congr φ.toEquiv, garlingAffineSubgroup_card hp.pos]
    have : Fact p.Prime := ⟨hp⟩
    have hF_dvd : Nat.card F ∣ p - 1 := by
      have h := Subgroup.card_subgroup_dvd_card F
      rwa [Nat.card_eq_fintype_card (α := (ZMod p)ˣ), ZMod.card_units p] at h
    rw [mul_comm p (p - 1)]
    exact mul_dvd_mul_right hF_dvd p
  exact ⟨h12, ⟨F, e, hG_eq, ⟨φ.symm⟩⟩, hdvd⟩

/-- **§20.2 Unnumbered Prose Theorem (`x^p - 2`, printed p. 160 / PDF p. 168):**
*"Recall that in Section 7.3 we showed that the degree of a splitting field extension for `x^p - 2`
over `ℚ` is `p(p - 1)`, and so the Galois group of `x^p - 2` is isomorphic to the group `W`."* -/
theorem section_20_2_xp_sub_two_galoisGroup {p : ℕ} (hp : Nat.Prime p) :
    let f : ℚ[X] := Polynomial.X ^ p - Polynomial.C 2
    Irreducible f ∧
    IsGarlingSolvableByRadicals f ∧
    ∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L f →
      Module.finrank ℚ L = p * (p - 1) ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* garlingAffineGroup p) := by
  classical
  intro f
  have hf_eq : f = Polynomial.X ^ p - 2 := by
    dsimp [f]; simp [map_ofNat]
  -- Pick a primitive `p`-th root of unity `ω = exp(2πi/p) ∈ ℂ` to invoke `Chapter07.example_7_3_1`:
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (p : ℂ))
  have hω_prim : IsPrimitiveRoot ω p := Complex.isPrimitiveRoot_exp p hp.ne_zero
  have hω_pow : ω ^ p = 1 := hω_prim.pow_eq_one
  have hω_ne1 : ω ≠ 1 := hω_prim.ne_one hp.one_lt
  have hex731 := example_7_3_1 hp hω_pow hω_ne1
  have hirr : Irreducible f := hf_eq ▸ hex731.1
  have hf_mon : f.Monic := Polynomial.monic_X_pow_sub_C 2 hp.ne_zero
  have hf_deg : f.natDegree = p := Polynomial.natDegree_X_pow_sub_C
  -- `f` is solvable by radicals over `ℚ`: `ℚ ⊆ ℚ(ω) ⊆ ℚ(ω, 2^{1/p})` is a 2-step radical tower!
  have hsol_rad : IsGarlingSolvableByRadicals f := by
    let r : ℂ := twoPowInvNat p
    let E : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({ω, r} : Set ℂ)
    have hsfE : IsGarlingSplittingFieldExtension ℚ E f := hf_eq ▸ hex731.2.2.2.2.2.2.2.2.1
    have hE_rad : IsGarlingExtensionByRadicals ℚ E := by
      let ωE : E := ⟨ω, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let rE : E := ⟨r, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let T : Fin 3 → IntermediateField ℚ E := fun i =>
        match i with
        | 0 => ⊥
        | 1 => IntermediateField.adjoin ℚ ({ωE} : Set E)
        | 2 => ⊤
      refine ⟨2, T, ![ωE, rE], rfl, rfl, fun i => ?_⟩
      fin_cases i
      · refine ⟨⟨p, hp.one_lt.le, ?_⟩, ?_⟩
        · change (ωE ^ p) ∈ (⊥ : IntermediateField ℚ E)
          have h1 : ωE ^ p = 1 := Subtype.ext hω_pow
          rw [h1]; exact (⊥ : IntermediateField ℚ E).one_mem
        · change IntermediateField.adjoin ℚ ({ωE} : Set E) =
            IntermediateField.adjoin ℚ (((⊥ : IntermediateField ℚ E) : Set E) ∪ {ωE})
          apply le_antisymm
          · exact IntermediateField.adjoin_le_iff.mpr fun z hz =>
              IntermediateField.subset_adjoin ℚ _ (Or.inr hz)
          · rw [IntermediateField.adjoin_le_iff]
            rintro x (hx | rfl)
            · obtain ⟨q, rfl⟩ := IntermediateField.mem_bot.mp hx
              exact (IntermediateField.adjoin ℚ _).algebraMap_mem q
            · exact IntermediateField.subset_adjoin ℚ _ rfl
      · refine ⟨⟨p, hp.one_lt.le, ?_⟩, ?_⟩
        · change (rE ^ p) ∈ IntermediateField.adjoin ℚ ({ωE} : Set E)
          have hr_pow : r ^ p = (2 : ℂ) := by
            have hmin := hex731.2.1
            have h0 := minpoly.aeval ℚ r
            rw [hmin] at h0
            simp only [map_sub, map_pow, Polynomial.aeval_X, map_ofNat, sub_eq_zero] at h0
            exact h0
          have h2 : rE ^ p = algebraMap ℚ E 2 := Subtype.ext (by
            change r ^ p = (2 : ℂ); exact hr_pow)
          rw [h2]; exact (IntermediateField.adjoin ℚ _).algebraMap_mem 2
        · change (⊤ : IntermediateField ℚ E) =
            IntermediateField.adjoin ℚ (((IntermediateField.adjoin ℚ ({ωE} : Set E)) : Set E) ∪ {rE})
          symm
          rw [eq_top_iff]
          intro x _
          have hxE : x.1 ∈ IntermediateField.adjoin ℚ ({ω, r} : Set ℂ) := x.2
          let M : IntermediateField ℚ E :=
            IntermediateField.adjoin ℚ (((IntermediateField.adjoin ℚ ({ωE} : Set E)) : Set E) ∪ {rE})
          have hsub : IntermediateField.adjoin ℚ ({ω, r} : Set ℂ) ≤ M.map E.val := by
            rw [IntermediateField.adjoin_le_iff]
            rintro y (rfl | rfl)
            · exact ⟨ωE, IntermediateField.subset_adjoin ℚ _ (Or.inl
                (IntermediateField.subset_adjoin ℚ _ rfl)), rfl⟩
            · exact ⟨rE, IntermediateField.subset_adjoin ℚ _ (Or.inr rfl), rfl⟩
          obtain ⟨y, hy, hyx⟩ := hsub hxE
          exact (Subtype.ext hyx : y = x) ▸ hy
    exact isGarlingSolvableByRadicals_of_extension hE_rad hsfE.1
  refine ⟨hirr, hsol_rad, ?_⟩
  intro L _ _ hsfL
  -- Compare `L` with `E = ℚ(ω, 2^{1/p})` via `Corollary 1` to `Theorem 7.5`:
  let r : ℂ := twoPowInvNat p
  let E : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({ω, r} : Set ℂ)
  have hsfE : IsGarlingSplittingFieldExtension ℚ E f := hf_eq ▸ hex731.2.2.2.2.2.2.2.2.1
  obtain ⟨eEL, heEL⟩ := corollary_1_to_theorem_7_5_equiv (RingEquiv.refl ℚ) f hsfE
    (by simpa [garlingMapPoly] using hsfL)
  let eEL_alg : E ≃ₐ[ℚ] L := { eEL with commutes' := heEL }
  have hfinL : Module.finrank ℚ L = p * (p - 1) := by
    rw [← LinearEquiv.finrank_eq eEL_alg.toLinearEquiv]
    exact hex731.2.2.2.2.2.2.2.2.2.1
  refine ⟨hfinL, ?_⟩
  -- `Γ_ℚ(f)` is soluble (from `hsol_rad` + `theorem_17_6`) and embeds as a transitive subgroup of `Σ_p`:
  have hsol_gal : IsGarlingSoluble (GarlingPolyGaloisGroup ℚ L f) := by
    rcases hsol_rad with ⟨M, fM, aM, hradM, hsplM⟩
    let _ : Field M := fM
    let _ : Algebra ℚ M := aM
    obtain ⟨m, T, β, ns, h0, hlast, hchar, hstep⟩ :=
      isGarlingRadicalExtensionNotCharDvd_of_charZero hradM
    exact theorem_17_6 h0 hlast hstep hchar hsplM hsfL
  have hsfL_m : f.IsSplittingField ℚ L := (isGarlingSplittingFieldExtension_iff ℚ L f).mp hsfL
  have _ : FiniteDimensional ℚ L := Polynomial.IsSplittingField.finiteDimensional L f
  have _ : Normal ℚ L := Normal.of_isSplittingField f
  have _ : IsGalois ℚ L := {}
  have hcard_gal : Nat.card (GarlingPolyGaloisGroup ℚ L f) = p * (p - 1) := by
    rw [← hfinL]
    exact IsGalois.card_aut_eq_finrank ℚ L
  -- Enumerate the `p` distinct roots of `f` in `L`:
  have hcard_roots : (garlingRootSet ℚ L f).ncard = p := by
    have hsep : f.Separable := hirr.separable
    have hsplit : (f.map (algebraMap ℚ L)).Splits := hsfL_m.splits
    rw [garlingRootSet_eq_rootSet hf_mon.ne_zero]
    have hnodup : (f.map (algebraMap ℚ L)).roots.Nodup :=
      Polynomial.nodup_roots (hsep.map)
    have hcard_m : (f.map (algebraMap ℚ L)).roots.card = p := by
      rw [← hf_deg, ← Polynomial.natDegree_map (algebraMap ℚ L)]
      exact Polynomial.splits_iff_card_roots.mp hsplit
    have hset_eq : f.rootSet L = ((f.map (algebraMap ℚ L)).roots.toFinset : Set L) := by
      ext x
      simp [Polynomial.mem_rootSet_of_ne hf_mon.ne_zero, Polynomial.mem_roots (Polynomial.map_monic_ne_zero hf_mon),
        Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    rw [hset_eq, Set.ncard_coe_finset, Multiset.toFinset_card_of_nodup hnodup, hcard_m]
  have _ : Finite (garlingRootSet ℚ L f) := Set.finite_of_ncard_pos (by rw [hcard_roots]; exact hp.pos)
  have hcard_rt : Nat.card (garlingRootSet ℚ L f) = p := by
    rw [Nat.card_coe_set_eq, hcard_roots]
  let eR : Fin p ≃ garlingRootSet ℚ L f :=
    (Finite.equivFinOfCardEq hcard_rt).symm
  let φ := garlingRootLabellingPermHom eR
  have hφ_inj : Function.Injective φ := by
    intro σ₁ σ₂ h
    apply theorem_11_6 hsfL
    ext r
    have h1 := Equiv.congr_fun h (eR.symm r)
    have h2 : eR (φ σ₁ (eR.symm r)) = eR (φ σ₂ (eR.symm r)) := congrArg eR h1
    simpa [φ, garlingRootLabellingPermHom] using congrArg Subtype.val h2
  let eGalRange : GarlingPolyGaloisGroup ℚ L f ≃* φ.range :=
    MulEquiv.ofBijective φ.rangeRestrict
      ⟨fun a b hab => hφ_inj (congrArg Subtype.val hab), φ.rangeRestrict_surjective⟩
  have htrans_range : SubgroupActsTransitively φ.range := by
    have htr := irreducible_imp_galoisGroup_actsTransitively hirr hsfL
    intro i j
    obtain ⟨_, ⟨σ, rfl⟩, hσ⟩ := htr (eR i) (eR j)
    refine ⟨φ σ, ⟨σ, rfl⟩, ?_⟩
    apply eR.injective
    simpa [φ, garlingRootLabellingPermHom] using hσ
  have hsol_range : IsGarlingSoluble φ.range := (isGarlingSoluble_congr eGalRange).mp hsol_gal
  obtain ⟨F, eF, _, ⟨eRangeW⟩⟩ := (theorem_20_3_repaired hp htrans_range hsol_range).2.1
  -- Since `|F| * p = |W_F| = |φ.range| = p * (p - 1) = |W|`, `F = ⊤`, so `W_F = garlingAffineGroup p`!
  have hF_top : F = ⊤ := by
    have hcard_F : Nat.card F * p = p * (p - 1) := by
      rw [← garlingAffineSubgroup_card hp.pos F, Nat.card_congr eRangeW.symm.toEquiv,
        Nat.card_congr eGalRange.symm.toEquiv, hcard_gal]
    have hcard_F' : Nat.card F = p - 1 := Nat.eq_of_mul_eq_mul_right hp.pos (by linarith)
    have : Fact p.Prime := ⟨hp⟩
    have htop_card : Nat.card (ZMod p)ˣ = p - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units p]
    exact Subgroup.eq_top_of_card_eq F (hcard_F'.trans htop_card.symm)
  exact ⟨eGalRange.trans (eRangeW.trans (MulEquiv.subgroupCongr (by rw [hF_top])))⟩

/-! ### Exercises 20.2 and 20.4 (group-theoretic consequences of `§20.2`) -/

/-- **Exercise 20.2** (§20.2, printed p. 160 / PDF p. 168):
*"Show that if `G` is a soluble transitive subgroup of `Σ_p` (where `p` is a prime) then every
element of `G` other than the identity fixes at most one point."*

Proved literally for every prime `p` and every soluble transitive `G ≤ Σ_p`. -/
theorem exercise_20_2 {p : ℕ} (hp : Nat.Prime p)
    {G : Subgroup (SigmaN p)} (htrans : SubgroupActsTransitively G)
    (hsol : IsGarlingSoluble G) :
    (∀ σ ∈ G, σ ≠ 1 → ∀ x y : Fin p, σ x = x → σ y = y → x = y) ∧
    (∀ σ ∈ G, σ ≠ 1 → {x : Fin p | σ x = x}.ncard ≤ 1) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, e, hG_eq⟩ := soluble_transitive_prime_eq_conj_affine hp htrans hsol
  have huniq : ∀ σ ∈ G, σ ≠ 1 → ∀ x y : Fin p, σ x = x → σ y = y → x = y := by
    intro σ hσG hσ1 x y hx hy
    rw [hG_eq] at hσG
    obtain ⟨_, ⟨a, b, _, rfl⟩, rfl⟩ := hσG
    have ha_ne1 : a ≠ 1 := by
      intro ha1
      subst ha1
      have hb0 : b = 0 := by
        have hx' : (e x) + b = e x := by
          have := congrArg e hx
          simpa [affinePerm_apply] using this
        simpa using hx'
      subst hb0
      apply hσ1
      refine Equiv.ext fun z => ?_
      simp [affinePerm_apply]
    have ha_sub : (a : ZMod p) - 1 ≠ 0 := sub_ne_zero.mpr (fun h => ha_ne1 (Units.ext h))
    have hex : (a : ZMod p) * e x + b = e x := by
      have := congrArg e hx
      simpa [affinePerm_apply] using this
    have hey : (a : ZMod p) * e y + b = e y := by
      have := congrArg e hy
      simpa [affinePerm_apply] using this
    have hdiff : ((a : ZMod p) - 1) * (e x - e y) = 0 := by linear_combination hex - hey
    have hexy : e x = e y := sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left ha_sub)
    exact e.injective hexy
  refine ⟨huniq, fun σ hσG hσ1 => ?_⟩
  by_cases hemp : {x : Fin p | σ x = x} = ∅
  · simp [hemp]
  · obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hemp
    have hsub : {x : Fin p | σ x = x} ⊆ {x₀} := fun y hy => huniq σ hσG hσ1 y x₀ hy hx₀
    calc {x : Fin p | σ x = x}.ncard ≤ ({x₀} : Set (Fin p)).ncard :=
          Set.ncard_le_ncard hsub (Set.finite_singleton x₀)
      _ = 1 := Set.ncard_singleton x₀

/-- **Exercise 20.4** (§20.2, printed pp. 160–161 / PDF pp. 168–169):
Preamble (Cauchy): if `|G| = p * q` with `p` prime and `p ∤ q`, then `G` has a subgroup of order `p`.
For any prime `p` and transitive subgroup `G ≤ Σ_p`:
- **(i)** `|G| = p * q` where `p ∤ q` (with `q = |Stab_G(x₀)|`);
- **(ii)** if `G` has at least two subgroups of order `p`, then there exists `σ ∈ G`, `σ ≠ 1`,
  fixing two distinct points, and hence `G` is not soluble;
- **(iii)** if `G` has a unique subgroup `K` of order `p`, then `K ◁ G` and `G` is soluble.

Proved literally for every prime `p`. -/
theorem exercise_20_4 :
    -- Group-theory preamble (Cauchy for order `p * q`, `p ∤ q`):
    (∀ {A : Type u} [Group A] [Finite A] {p q : ℕ}, Nat.Prime p → ¬ (p ∣ q) →
      Nat.card A = p * q → ∃ P : Subgroup A, Nat.card P = p) ∧
    -- Parts (i), (ii), (iii) for every prime `p` and transitive `G ≤ Σ_p`:
    (∀ {p : ℕ}, Nat.Prime p → ∀ {G : Subgroup (SigmaN p)},
      SubgroupActsTransitively G →
      -- (i) `|G| = p * q` with `p ∤ q`:
      (∃ q : ℕ, Nat.card G = p * q ∧ ¬ (p ∣ q)) ∧
      -- (ii) ≥ 2 subgroups of order `p` ⇒ ∃ `σ ≠ 1` fixing 2 distinct points, and `¬ IsGarlingSoluble G`:
      ((∃ K₁ K₂ : Subgroup G, Nat.card K₁ = p ∧ Nat.card K₂ = p ∧ K₁ ≠ K₂) →
        (∃ σ ∈ G, σ ≠ 1 ∧ ∃ x y : Fin p, x ≠ y ∧ σ x = x ∧ σ y = y) ∧
        ¬ IsGarlingSoluble G) ∧
      -- (iii) unique subgroup `K` of order `p` ⇒ `K ◁ G` and `IsGarlingSoluble G`:
      (∀ K : Subgroup G, Nat.card K = p →
        (∀ K' : Subgroup G, Nat.card K' = p → K' = K) →
        K.Normal ∧ IsGarlingSoluble G)) := by
  classical
  refine ⟨?_, ?_⟩
  · intro A _ _ p q hp _ hcard
    have : Fact p.Prime := ⟨hp⟩
    have hdvd : p ∣ Nat.card A := ⟨q, hcard⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
    exact ⟨Subgroup.zpowers g, by rw [Nat.card_zpowers, hg]⟩
  · intro p hp G htrans
    have : Fact p.Prime := ⟨hp⟩
    let x₀ : Fin p := ⟨0, hp.pos⟩
    let stab : Fin p → Subgroup G := fun x =>
      { carrier := {g : G | g.1 x = x}
        one_mem' := rfl
        mul_mem' := fun {a b} ha hb => by change a.1 (b.1 x) = x; rw [hb, ha]
        inv_mem' := fun {a} ha => by
          change a.1⁻¹ x = x
          conv_lhs => rw [← ha]
          exact a.1.symm_apply_apply x }
    -- All point stabilizers are conjugate in `G` (since `G` is transitive), hence have equal order `q`:
    have hstab_card_eq : ∀ x y : Fin p, Nat.card (stab x) = Nat.card (stab y) := by
      intro x y
      obtain ⟨τ, hτG, hτxy⟩ := htrans x y
      let e : stab x ≃* stab y :=
        { toFun := fun g => ⟨⟨τ, hτG⟩ * g.1 * ⟨τ, hτG⟩⁻¹, by
            change τ (g.1.1 (τ⁻¹ y)) = y
            rw [← hτxy, show τ⁻¹ (τ x) = x from τ.symm_apply_apply x, g.2]⟩
          invFun := fun g => ⟨⟨τ, hτG⟩⁻¹ * g.1 * ⟨τ, hτG⟩, by
            change τ⁻¹ (g.1.1 (τ x)) = x
            rw [hτxy, g.2, ← hτxy]; exact τ.symm_apply_apply x⟩
          left_inv := fun g => Subtype.ext (by group)
          right_inv := fun g => Subtype.ext (by group)
          map_mul' := fun g₁ g₂ => by
            apply Subtype.ext
            change (⟨τ, hτG⟩ : G) * (g₁.1 * g₂.1) * (⟨τ, hτG⟩ : G)⁻¹ =
              ((⟨τ, hτG⟩ : G) * g₁.1 * (⟨τ, hτG⟩ : G)⁻¹) *
                ((⟨τ, hτG⟩ : G) * g₂.1 * (⟨τ, hτG⟩ : G)⁻¹)
            group }
      exact Nat.card_congr e.toEquiv
    -- Orbit-stabilizer on `G`: `|G| = p * |stab x₀|`:
    have hcard_G : Nat.card G = p * Nat.card (stab x₀) := by
      have hidx : (stab x₀).index = p := by
        let f : G ⧸ stab x₀ → Fin p :=
          Quotient.lift (fun g : G => g.1 x₀) fun g₁ g₂ hrel => by
            have hmem : g₁⁻¹ * g₂ ∈ stab x₀ := (QuotientGroup.leftRel_apply).mp hrel
            have h1 : g₁.1⁻¹ (g₂.1 x₀) = x₀ := hmem
            calc g₁.1 x₀ = g₁.1 (g₁.1⁻¹ (g₂.1 x₀)) := by rw [h1]
              _ = g₂.1 x₀ := g₁.1.apply_symm_apply _
        have hf_bij : Function.Bijective f := by
          refine ⟨?_, ?_⟩
          · intro a b
            induction a using Quotient.ind with
            | _ g₁ =>
              induction b using Quotient.ind with
              | _ g₂ =>
                intro h12
                change g₁.1 x₀ = g₂.1 x₀ at h12
                apply Quotient.sound
                change QuotientGroup.leftRel (stab x₀) g₁ g₂
                rw [QuotientGroup.leftRel_apply]
                change g₁.1⁻¹ (g₂.1 x₀) = x₀
                rw [← h12]; exact g₁.1.symm_apply_apply x₀
          · intro y
            obtain ⟨σ, hσG, hσy⟩ := htrans x₀ y
            exact ⟨Quotient.mk _ ⟨σ, hσG⟩, hσy⟩
        change Nat.card (G ⧸ stab x₀) = p
        rw [Nat.card_congr (Equiv.ofBijective f hf_bij), Nat.card_eq_fintype_card, Fintype.card_fin]
      have him := Subgroup.index_mul_card (stab x₀)
      rw [hidx] at him
      exact him.symm
    -- `stab x₀` embeds into `Equiv.Perm {y : Fin p // y ≠ x₀}` of order `(p - 1)!`, so `p ∤ |stab x₀|`:
    have hndvd_q : ¬ (p ∣ Nat.card (stab x₀)) := by
      let S' := {y : Fin p // y ≠ x₀}
      let emb : stab x₀ →* Equiv.Perm S' :=
        { toFun := fun g =>
            { toFun := fun y => ⟨g.1.1 y.1, fun h => y.2 (g.1.1.injective (h.trans g.2.symm))⟩
              invFun := fun y => ⟨g.1.1⁻¹ y.1, fun h => y.2 (by
                have := congrArg g.1.1 h
                rw [show g.1.1 (g.1.1⁻¹ y.1) = y.1 from g.1.1.apply_symm_apply y.1, g.2] at this
                exact this)⟩
              left_inv := fun y => Subtype.ext (g.1.1.symm_apply_apply y.1)
              right_inv := fun y => Subtype.ext (g.1.1.apply_symm_apply y.1) }
          map_one' := by ext y; rfl
          map_mul' := fun g₁ g₂ => by ext y; rfl }
      have hemb_inj : Function.Injective emb := by
        intro g₁ g₂ h
        apply Subtype.ext; apply Subtype.ext
        refine Equiv.ext fun y => ?_
        by_cases hy : y = x₀
        · rw [hy, g₁.2, g₂.2]
        · exact congrArg Subtype.val (Equiv.congr_fun h ⟨y, hy⟩)
      have hdvd_fact : Nat.card (stab x₀) ∣ (p - 1).factorial := by
        have h1 : Nat.card (stab x₀) = Nat.card emb.range :=
          Nat.card_congr (MulEquiv.ofBijective emb.rangeRestrict
            ⟨fun a b hab => hemb_inj (congrArg Subtype.val hab), emb.rangeRestrict_surjective⟩).toEquiv
        have h2 := Subgroup.card_subgroup_dvd_card emb.range
        rw [← h1, Nat.card_eq_fintype_card (α := Equiv.Perm S'), Fintype.card_perm] at h2
        have hcard_S' : Fintype.card S' = p - 1 := by
          simp [S', Fintype.card_subtype_compl, Fintype.card_fin]
        rwa [hcard_S'] at h2
      intro hdiv
      have hdiv_fact : p ∣ (p - 1).factorial := hdiv.trans hdvd_fact
      have hle := hp.dvd_factorial.mp hdiv_fact
      have hp_pos := hp.pos
      omega
    -- Helper: every element of `G` of order `p` is fixed-point-free:
    have hord_p_fpf : ∀ g : G, orderOf g = p → ∀ x : Fin p, g.1 x ≠ x := by
      intro g hg x hfix
      have hmem : g ∈ stab x := hfix
      have hord_dvd : orderOf g ∣ Nat.card (stab x) := by
        have h1 := Subgroup.card_subgroup_dvd_card (Subgroup.zpowers (⟨g, hmem⟩ : stab x))
        rw [Nat.card_zpowers, Subgroup.orderOf_mk] at h1
        exact h1
      rw [hg, hstab_card_eq x x₀] at hord_dvd
      exact hndvd_q hord_dvd
    refine ⟨⟨Nat.card (stab x₀), hcard_G, hndvd_q⟩, ?_, ?_⟩
    · -- Part (ii): counting argument!
      rintro ⟨K₁, K₂, hK₁, hK₂, hK_ne⟩
      have hex_fix2 : ∃ σ ∈ G, σ ≠ 1 ∧ ∃ x y : Fin p, x ≠ y ∧ σ x = x ∧ σ y = y := by
        by_contra hno
        push Not at hno
        let S : Fin p → Finset G := fun x =>
          (Finset.univ : Finset G).filter fun g => g ≠ 1 ∧ g.1 x = x
        have hS_card : ∀ x : Fin p, (S x).card = Nat.card (stab x₀) - 1 := by
          intro x
          have h1 : (S x).card + 1 = Nat.card (stab x) := by
            let Sfull : Finset G := (Finset.univ : Finset G).filter fun g => g.1 x = x
            have hfull_eq : Sfull = insert 1 (S x) := by
              ext g
              simp only [Sfull, S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
              constructor
              · intro hg
                by_cases hg1 : g = 1
                · exact Or.inl hg1
                · exact Or.inr ⟨hg1, hg⟩
              · rintro (rfl | ⟨_, hg⟩)
                · rfl
                · exact hg
            have h1not : (1 : G) ∉ S x := by simp [S]
            rw [← Finset.card_insert_of_notMem h1not, ← hfull_eq]
            have hbij : Function.Bijective (fun g : stab x => (⟨g.1, Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, g.2⟩⟩ : Sfull)) :=
              ⟨fun a b h => Subtype.ext (congrArg (fun u : Sfull => u.1) h),
               fun ⟨g, hg⟩ => ⟨⟨g, (Finset.mem_filter.mp hg).2⟩, rfl⟩⟩
            rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_coe]
          rw [hstab_card_eq x x₀] at h1
          omega
        have hS_disj : Set.PairwiseDisjoint (Set.univ : Set (Fin p)) S := by
          intro x _ y _ hxy
          change Disjoint (S x) (S y)
          rw [Finset.disjoint_left]
          intro g hgx hgy
          have ⟨hg1, hfx⟩ := (Finset.mem_filter.mp hgx).2
          have ⟨_, hfy⟩ := (Finset.mem_filter.mp hgy).2
          exact hno g.1 g.2 (fun h => hg1 (Subtype.ext h)) x y hxy hfx hfy
        let U : Finset G := Finset.univ.biUnion S
        have hU_card : U.card = p * (Nat.card (stab x₀) - 1) := by
          rw [Finset.card_biUnion (fun x _ y _ hxy => hS_disj (Set.mem_univ x) (Set.mem_univ y) hxy)]
          simp [hS_card, Finset.card_univ, Fintype.card_fin]
        let R : Finset G := Finset.univ \ U
        have hR_card : R.card = p := by
          have hsub : U ⊆ Finset.univ := Finset.subset_univ U
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_univ,
            ← Nat.card_eq_fintype_card, hcard_G, hU_card]
          have hq_pos : 1 ≤ Nat.card (stab x₀) := Nat.card_pos
          have hsub_le : p * (Nat.card (stab x₀) - 1) ≤ p * Nat.card (stab x₀) :=
            Nat.mul_le_mul_left p (Nat.sub_le _ 1)
          zify [hq_pos, hsub_le]
          ring
        have hK_sub_R : ∀ K : Subgroup G, Nat.card K = p →
            (Finset.univ.filter fun g : G => g ∈ K) ⊆ R := by
          intro K hK g hg
          have hgK : g ∈ K := (Finset.mem_filter.mp hg).2
          rw [Finset.mem_sdiff]
          refine ⟨Finset.mem_univ g, fun hgU => ?_⟩
          obtain ⟨x, _, hgx⟩ := Finset.mem_biUnion.mp hgU
          have ⟨hg1, hfx⟩ := (Finset.mem_filter.mp hgx).2
          have hord_dvd : orderOf (⟨g, hgK⟩ : K) ∣ p := by
            have h0 := orderOf_dvd_natCard (⟨g, hgK⟩ : K)
            rwa [hK] at h0
          have hord_ne1 : orderOf (⟨g, hgK⟩ : K) ≠ 1 := fun h1 =>
            hg1 (congrArg Subtype.val (orderOf_eq_one_iff.mp h1))
          have hord_p : orderOf g = p := by
            have := (hp.eq_one_or_self_of_dvd _ hord_dvd).resolve_left hord_ne1
            rwa [Subgroup.orderOf_mk] at this
          exact hord_p_fpf g hord_p x hfx
        have hK_eq_R : ∀ K : Subgroup G, Nat.card K = p →
            Finset.univ.filter (fun g : G => g ∈ K) = R := by
          intro K hK
          apply Finset.eq_of_subset_of_card_le (hK_sub_R K hK)
          rw [hR_card]
          let Kf : Finset G := Finset.univ.filter (fun g : G => g ∈ K)
          have hbij : Function.Bijective (fun g : K => (⟨g.1, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, g.2⟩⟩ : Kf)) :=
            ⟨fun a b h => Subtype.ext (congrArg (fun u : Kf => u.1) h),
             fun ⟨g, hg⟩ => ⟨⟨g, (Finset.mem_filter.mp hg).2⟩, rfl⟩⟩
          have hcard_f : Kf.card = Nat.card K := by
            rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_coe]
          change p ≤ Kf.card
          rw [hcard_f, hK]
        apply hK_ne
        ext g
        have h1 := Finset.ext_iff.mp ((hK_eq_R K₁ hK₁).trans (hK_eq_R K₂ hK₂).symm) g
        simpa using h1
      refine ⟨hex_fix2, fun hsol => ?_⟩
      obtain ⟨σ, hσG, hσ1, x, y, hxy, hx, hy⟩ := hex_fix2
      exact hxy ((exercise_20_2 hp htrans hsol).1 σ hσG hσ1 x y hx hy)
    · -- Part (iii): unique subgroup `K` of order `p` ⇒ `K ◁ G` and `G` is soluble!
      intro K hK huniq
      have hK_norm : K.Normal := by
        constructor
        intro k hk g
        let K' : Subgroup G := K.map (MulAut.conj g).toMonoidHom
        have hK'_card : Nat.card K' = p :=
          (Nat.card_congr ((MulAut.conj g).subgroupMap K).symm.toEquiv).trans hK
        have hK'_eq : K' = K := huniq K' hK'_card
        rw [← hK'_eq]
        exact ⟨k, hk, rfl⟩
      refine ⟨hK_norm, ?_⟩
      have hK_cyc : IsCyclic K := isCyclic_of_prime_card hK
      obtain ⟨⟨⟨σ, hσG⟩, hσK⟩, hσ_gen⟩ := IsCyclic.exists_generator (α := K)
      have hσ_ord : orderOf σ = p := by
        have h1 : orderOf (⟨⟨σ, hσG⟩, hσK⟩ : K) = Nat.card K := by
          rw [← Nat.card_zpowers, show Subgroup.zpowers (⟨⟨σ, hσG⟩, hσK⟩ : K) = ⊤ from
            eq_top_iff.mpr fun x _ => hσ_gen x]
          exact Nat.card_congr Subgroup.topEquiv.toEquiv
        rw [hK, Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h1
        exact h1
      have hK_ne : K.map G.subtype ≠ ⊥ := by
        intro hbot
        have h1 : (⟨σ, hσG⟩ : G) = 1 := by
          apply Subtype.ext
          exact Subgroup.mem_bot.mp (hbot ▸ ⟨⟨σ, hσG⟩, hσK, rfl⟩)
        have hord1 : orderOf σ = 1 := by
          rw [show σ = 1 from congrArg Subtype.val h1, orderOf_one]
        rw [hσ_ord] at hord1
        exact hp.ne_one hord1
      have hK_norm_sub : ((K.map G.subtype).subgroupOf G).Normal := by
        have heq : (K.map G.subtype).subgroupOf G = K := by
          ext g; simp [Subgroup.mem_subgroupOf]
        rwa [heq]
      have hK_trans : SubgroupActsTransitively (K.map G.subtype) :=
        section_20_2_normal_subgroup_transitive hp htrans (fun _ ⟨x, _, hx⟩ => hx ▸ x.2)
          hK_norm_sub hK_ne
      let e_inv_fun : ZMod p → Fin p := fun z => (σ ^ z.val) x₀
      have he_inv_bij : Function.Bijective e_inv_fun := by
        refine (Fintype.bijective_iff_injective_and_card e_inv_fun).mpr ⟨?_, by simp⟩
        intro z₁ z₂ h12
        have hlt1 : z₁.val < p := z₁.val_lt
        have hlt2 : z₂.val < p := z₂.val_lt
        by_contra hne
        have hval_ne : z₁.val ≠ z₂.val := fun h => hne (ZMod.val_injective p h)
        have hfix : ∀ d : ℕ, 0 < d → d < p → (σ ^ d) x₀ ≠ x₀ := fun d hd0 hdp hfd => by
          have hd_cop : Nat.Coprime d p :=
            (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hd0 hdp)).symm
          have hord_d : orderOf ((⟨σ, hσG⟩ : G) ^ d) = p := by
            rw [orderOf_pow' _ hd0.ne', Subgroup.orderOf_mk, hσ_ord, Nat.gcd_comm,
              hd_cop.gcd_eq_one, Nat.div_one]
          exact hord_p_fpf ((⟨σ, hσG⟩ : G) ^ d) hord_d x₀ hfd
        rcases lt_or_gt_of_ne hval_ne with hlt | hgt
        · apply hfix (z₂.val - z₁.val) (by omega) (by omega)
          have h1 : (σ ^ z₁.val) ((σ ^ (z₂.val - z₁.val)) x₀) = (σ ^ z₁.val) x₀ := by
            change ((σ ^ z₁.val) * (σ ^ (z₂.val - z₁.val))) x₀ = _
            rw [← pow_add, Nat.add_sub_cancel' hlt.le]
            exact h12.symm
          exact (σ ^ z₁.val).injective h1
        · apply hfix (z₁.val - z₂.val) (by omega) (by omega)
          have h1 : (σ ^ z₂.val) ((σ ^ (z₁.val - z₂.val)) x₀) = (σ ^ z₂.val) x₀ := by
            change ((σ ^ z₂.val) * (σ ^ (z₁.val - z₂.val))) x₀ = _
            rw [← pow_add, Nat.add_sub_cancel' hgt.le]
            exact h12
          exact (σ ^ z₂.val).injective h1
      let e : Fin p ≃ ZMod p := (Equiv.ofBijective e_inv_fun he_inv_bij).symm
      let conjE : SigmaN p ≃* Equiv.Perm (ZMod p) := permCongrMulEquiv e
      have hconjE_σ : conjE σ = affinePerm 1 1 := by
        ext z
        rw [permCongrMulEquiv_apply, affinePerm_apply, Units.val_one, one_mul]
        apply e.symm.injective
        rw [e.symm_apply_apply]
        change σ ((σ ^ z.val) x₀) = (σ ^ (z + 1).val) x₀
        have hstep_pow : σ ((σ ^ z.val) x₀) = (σ ^ (z.val + 1)) x₀ := by
          rw [pow_succ']; rfl
        rw [hstep_pow]
        have hpow_mod : σ ^ (z.val + 1) = σ ^ ((z.val + 1) % p) := by
          have hdiv := Nat.div_add_mod (z.val + 1) p
          have hσp : σ ^ p = 1 := (congrArg (fun n => σ ^ n) hσ_ord).symm.trans (pow_orderOf_eq_one σ)
          conv_lhs => rw [← hdiv, pow_add, pow_mul, hσp, one_pow, one_mul]
        rw [hpow_mod, ← ZMod.val_natCast (n := p) (z.val + 1)]
        congr 2; simp
      have hG_le_W : G.map conjE.toMonoidHom ≤ garlingAffineGroup p := by
        rintro _ ⟨τ, hτG, rfl⟩
        have hconj_K : (⟨τ, hτG⟩ : G) * ⟨σ, hσG⟩ * (⟨τ, hτG⟩ : G)⁻¹ ∈ K :=
          hK_norm.conj_mem ⟨σ, hσG⟩ hσK ⟨τ, hτG⟩
        obtain ⟨m, hm⟩ := hσ_gen ⟨_, hconj_K⟩
        have hconj_eq : τ * σ * τ⁻¹ = σ ^ m := (congrArg (fun x : K => x.1.1) hm).symm
        have hconj_z : conjE τ * affinePerm 1 1 * (conjE τ)⁻¹ = affinePerm 1 (m : ZMod p) := by
          rw [← hconjE_σ, ← map_inv, ← map_mul, ← map_mul, hconj_eq, map_zpow, hconjE_σ]
          have hzpow_tr : ∀ n : ℤ, (affinePerm (1 : (ZMod p)ˣ) 1) ^ n = affinePerm 1 (n : ZMod p) := by
            intro n
            have hnat : ∀ k : ℕ, (affinePerm (1 : (ZMod p)ˣ) 1) ^ k = affinePerm 1 (k : ZMod p) := by
              intro k; induction k with
              | zero => simp [affinePerm_one]
              | succ k ihk => rw [pow_succ, ihk, affinePerm_mul]; simp [add_comm]
            cases n with
            | ofNat k =>
              change (affinePerm (1 : (ZMod p)ˣ) 1) ^ k = affinePerm 1 ((k : ℤ) : ZMod p)
              rw [hnat k, Int.cast_natCast]
            | negSucc k =>
              rw [zpow_negSucc, hnat, affinePerm_inv]
              simp
          exact hzpow_tr m
        have hm0 : (m : ZMod p) ≠ 0 := by
          intro h0
          rw [h0, affinePerm_one] at hconj_z
          have h1 : affinePerm (1 : (ZMod p)ˣ) 1 = 1 := by
            have := congrArg (fun g => (conjE τ)⁻¹ * g * conjE τ) hconj_z
            simpa [mul_assoc] using this
          have h01 := Equiv.congr_fun h1 (0 : ZMod p)
          simp [affinePerm_apply] at h01
        have hstep_τ : ∀ z : ZMod p, conjE τ (z + 1) = conjE τ z + (m : ZMod p) := by
          intro z
          have h1 := Equiv.congr_fun hconj_z (conjE τ z)
          change conjE τ (affinePerm (1 : (ZMod p)ˣ) 1 ((conjE τ)⁻¹ (conjE τ z))) =
            (1 : (ZMod p)ˣ) * conjE τ z + (m : ZMod p) at h1
          rw [Units.val_one, one_mul,
            show (conjE τ)⁻¹ (conjE τ z) = z from (conjE τ).symm_apply_apply z] at h1
          simpa [affinePerm_apply] using h1
        have hτ_nat : ∀ k : ℕ, conjE τ (k : ZMod p) = (m : ZMod p) * (k : ZMod p) + conjE τ 0 := by
          intro k
          induction k with
          | zero => simp
          | succ k ihk => push_cast; rw [hstep_τ, ihk]; ring
        refine ⟨Units.mk0 (m : ZMod p) hm0, conjE τ 0, Subgroup.mem_top _, ?_⟩
        ext z
        change conjE τ z = affinePerm (Units.mk0 (m : ZMod p) hm0) (conjE τ 0) z
        rw [← ZMod.natCast_zmod_val z, hτ_nat, affinePerm_apply, Units.val_mk0]
      have hsol_sub : IsGarlingSoluble ((G.map conjE.toMonoidHom).subgroupOf (garlingAffineGroup p)) :=
        theorem_17_2_i (garlingAffineGroup_soluble hp) _
      let eSub : G ≃* (G.map conjE.toMonoidHom).subgroupOf (garlingAffineGroup p) :=
        { toFun := fun g => ⟨⟨conjE g.1, hG_le_W ⟨g.1, g.2, rfl⟩⟩, ⟨g.1, g.2, rfl⟩⟩
          invFun := fun y => ⟨conjE.symm y.1.1, by
            obtain ⟨x, hx, hxy⟩ := y.2
            have hxy' : conjE x = y.1.1 := hxy
            rw [← hxy', conjE.symm_apply_apply]
            exact hx⟩
          left_inv := fun g => Subtype.ext (by simp)
          right_inv := fun y => Subtype.ext (Subtype.ext (by simp))
          map_mul' := fun g₁ g₂ => Subtype.ext (Subtype.ext (map_mul conjE _ _)) }
      exact (isGarlingSoluble_congr eSub).mpr hsol_sub

/-! ### Computable `List (ZMod p)` Rabin Irreducibility Verifier (Pure Kernel `decide`) -/

private noncomputable def zmodListToPoly {p : ℕ} : List (ZMod p) → (ZMod p)[X]
  | [] => 0
  | a :: l => Polynomial.C a + Polynomial.X * zmodListToPoly l

private def zmodListAdd {p : ℕ} : List (ZMod p) → List (ZMod p) → List (ZMod p)
  | [], l => l
  | l, [] => l
  | a :: l₁, b :: l₂ => (a + b) :: zmodListAdd l₁ l₂

private def zmodListScale {p : ℕ} (c : ZMod p) : List (ZMod p) → List (ZMod p)
  | [] => []
  | a :: l => (c * a) :: zmodListScale c l

private def zmodListMul {p : ℕ} : List (ZMod p) → List (ZMod p) → List (ZMod p)
  | [], _ => []
  | a :: l₁, l₂ => zmodListAdd (zmodListScale a l₂) (0 :: zmodListMul l₁ l₂)

private def zmodListComp {p : ℕ} : List (ZMod p) → List (ZMod p) → List (ZMod p)
  | [], _ => []
  | a :: l, g => zmodListAdd [a] (zmodListMul g (zmodListComp l g))

private def zmodListXpow {p : ℕ} : ℕ → List (ZMod p)
  | 0 => [1]
  | n + 1 => 0 :: zmodListXpow n

private def zmodListAllZero {p : ℕ} : List (ZMod p) → Bool
  | [] => true
  | a :: l => decide (a = 0) && zmodListAllZero l

private def zmodListEq {p : ℕ} : List (ZMod p) → List (ZMod p) → Bool
  | [], l => zmodListAllZero l
  | l, [] => zmodListAllZero l
  | a :: l₁, b :: l₂ => decide (a = b) && zmodListEq l₁ l₂

private theorem zmodListToPoly_add {p : ℕ} (l₁ l₂ : List (ZMod p)) :
    zmodListToPoly (zmodListAdd l₁ l₂) = zmodListToPoly l₁ + zmodListToPoly l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp [zmodListAdd, zmodListToPoly]
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp [zmodListAdd, zmodListToPoly]
    | cons b l₂ =>
      simp only [zmodListAdd, zmodListToPoly, ih, map_add, mul_add]
      ring

private theorem zmodListToPoly_scale {p : ℕ} (c : ZMod p) (l : List (ZMod p)) :
    zmodListToPoly (zmodListScale c l) = Polynomial.C c * zmodListToPoly l := by
  induction l with
  | nil => simp [zmodListScale, zmodListToPoly]
  | cons a l ih =>
    simp only [zmodListScale, zmodListToPoly, ih, map_mul, mul_add]
    ring

private theorem zmodListToPoly_mul {p : ℕ} (l₁ l₂ : List (ZMod p)) :
    zmodListToPoly (zmodListMul l₁ l₂) = zmodListToPoly l₁ * zmodListToPoly l₂ := by
  induction l₁ with
  | nil => simp [zmodListMul, zmodListToPoly]
  | cons a l₁ ih =>
    simp only [zmodListMul, zmodListToPoly_add, zmodListToPoly_scale, zmodListToPoly, ih, map_zero,
      zero_add]
    ring

private theorem zmodListToPoly_comp {p : ℕ} (l g : List (ZMod p)) :
    zmodListToPoly (zmodListComp l g) = (zmodListToPoly l).comp (zmodListToPoly g) := by
  induction l with
  | nil => simp [zmodListComp, zmodListToPoly]
  | cons a l ih =>
    simp only [zmodListComp, zmodListToPoly_add, zmodListToPoly_mul, zmodListToPoly, ih,
      Polynomial.add_comp, Polynomial.C_comp, Polynomial.mul_comp, Polynomial.X_comp,
      mul_zero, add_zero]

private theorem zmodListToPoly_Xpow {p : ℕ} (n : ℕ) :
    zmodListToPoly (zmodListXpow (p := p) n) = (Polynomial.X : (ZMod p)[X]) ^ n := by
  induction n with
  | zero => simp [zmodListXpow, zmodListToPoly]
  | succ n ih =>
    simp only [zmodListXpow, zmodListToPoly, ih, map_zero, zero_add, pow_succ']

private theorem zmodListToPoly_eq_zero_of_allZero {p : ℕ} {l : List (ZMod p)}
    (h : zmodListAllZero l = true) : zmodListToPoly l = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [zmodListAllZero, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [zmodListToPoly, h.1, ih h.2]

private theorem zmodListToPoly_eq_of_listEq {p : ℕ} {l₁ l₂ : List (ZMod p)}
    (h : zmodListEq l₁ l₂ = true) : zmodListToPoly l₁ = zmodListToPoly l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    simp only [zmodListEq] at h
    exact (zmodListToPoly_eq_zero_of_allZero h).symm
  | cons a l₁ ih =>
    cases l₂ with
    | nil =>
      simp only [zmodListEq] at h
      exact zmodListToPoly_eq_zero_of_allZero h
    | cons b l₂ =>
      simp only [zmodListEq, Bool.and_eq_true, decide_eq_true_eq] at h
      simp [zmodListToPoly, h.1, ih h.2]

/-- General Rabin irreducibility certificate over `ℤ_p` (`p` prime): if `f ∈ ℤ_p[X]` is monic of
degree `d ≥ 2`, `r k` (`1 ≤ k ≤ d / 2`) satisfies `r 1 ≡ X^p (mod f)`,
`r (k + 1) ≡ (r k).comp (r 1) (mod f)`, and `IsCoprime f (r k - X)` for all `1 ≤ k ≤ d / 2`, then
`Irreducible f`. -/
private theorem irreducible_of_rabin_certificate {p d : ℕ} [Fact p.Prime]
    {f : (ZMod p)[X]} (hf_mon : f.Monic) (hf_deg : f.natDegree = d) (hd2 : 2 ≤ d)
    (r : Fin (d / 2) → (ZMod p)[X])
    (h1 : ∃ q₁ : (ZMod p)[X], Polynomial.X ^ p = q₁ * f + r ⟨0, by omega⟩)
    (hstep : ∀ k : ℕ, (hk : k + 1 < d / 2) →
      ∃ q : (ZMod p)[X], (r ⟨k, by omega⟩).comp (r ⟨0, by omega⟩) = q * f + r ⟨k + 1, hk⟩)
    (hbez : ∀ k : Fin (d / 2), ∃ u v : (ZMod p)[X], u * f + v * (r k - Polynomial.X) = 1) :
    Irreducible f := by
  classical
  have hp : Nat.Prime p := Fact.out
  have hf_ne0 : f ≠ 0 := hf_mon.ne_zero
  have hf_not_unit : ¬ IsUnit f := fun hu => by
    have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
  -- If `f` is reducible, it has a monic irreducible divisor `g ∣ f` of degree `1 ≤ deg g ≤ d / 2`:
  by_contra hnot_irr
  have hex_div : ∃ g : (ZMod p)[X], Irreducible g ∧ g ∣ f ∧ 1 ≤ g.natDegree ∧ g.natDegree ≤ d / 2 := by
    have hnot_prime : ∃ a b : (ZMod p)[X], f = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
      by_contra hall
      push Not at hall
      exact hnot_irr ⟨hf_not_unit, fun a b hab => by
        by_contra hnot
        push Not at hnot
        exact hnot.2 (hall a b hab hnot.1)⟩
    obtain ⟨a, b, hab, ha_nu, hb_nu⟩ := hnot_prime
    have ha0 : a ≠ 0 := fun h => hf_ne0 (by rw [hab, h, zero_mul])
    have hb0 : b ≠ 0 := fun h => hf_ne0 (by rw [hab, h, mul_zero])
    have ha_pos : 1 ≤ a.natDegree := by
      by_contra h0
      have hd0 : a.natDegree = 0 := by omega
      exact ha_nu (Polynomial.isUnit_iff_degree_eq_zero.mpr (by
        rw [Polynomial.degree_eq_natDegree ha0, hd0]; rfl))
    have hb_pos : 1 ≤ b.natDegree := by
      by_contra h0
      have hd0 : b.natDegree = 0 := by omega
      exact hb_nu (Polynomial.isUnit_iff_degree_eq_zero.mpr (by
        rw [Polynomial.degree_eq_natDegree hb0, hd0]; rfl))
    have hsum : a.natDegree + b.natDegree = d := by
      rw [← Polynomial.natDegree_mul ha0 hb0, ← hab, hf_deg]
    have hex_small : ∃ c : (ZMod p)[X], c ∣ f ∧ 1 ≤ c.natDegree ∧ c.natDegree ≤ d / 2 := by
      by_cases hle : a.natDegree ≤ b.natDegree
      · exact ⟨a, ⟨b, hab⟩, ha_pos, by omega⟩
      · exact ⟨b, ⟨a, hab.trans (mul_comm a b)⟩, hb_pos, by omega⟩
    obtain ⟨c, hcf, hc1, hcle⟩ := hex_small
    have hc_nu : ¬ IsUnit c := fun hu => by
      have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
    have hc0 : c ≠ 0 := fun h => by simp [h] at hc1
    obtain ⟨g, hgirr, hgc⟩ := WfDvdMonoid.exists_irreducible_factor hc_nu hc0
    have hg0 : g ≠ 0 := hgirr.ne_zero
    have hg_pos : 1 ≤ g.natDegree := by
      by_contra h0
      have hd0 : g.natDegree = 0 := by omega
      exact hgirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr (by
        rw [Polynomial.degree_eq_natDegree hg0, hd0]; rfl))
    have hg_le : g.natDegree ≤ c.natDegree := Polynomial.natDegree_le_of_dvd hgc hc0
    exact ⟨g, hgirr, hgc.trans hcf, hg_pos, hg_le.trans hcle⟩
  obtain ⟨g, hgirr, hgf, hg1, hgle⟩ := hex_div
  -- Pass to the finite field `K = AdjoinRoot g` of cardinality `p^(deg g)` with root `α = AdjoinRoot.root g`:
  have _ : Fact (Irreducible g) := ⟨hgirr⟩
  let K := AdjoinRoot g
  let α : K := AdjoinRoot.root g
  have hfα : Polynomial.aeval α f = 0 := by
    rcases hgf with ⟨h, rfl⟩
    rw [map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
  have hfrob_aeval : ∀ (h : (ZMod p)[X]) (x : K),
      (Polynomial.aeval x h) ^ p = Polynomial.aeval (x ^ p) h := by
    intro h x
    induction h using Polynomial.induction_on' with
    | add f₁ f₂ ih₁ ih₂ =>
      have _ : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
      rw [map_add, map_add, add_pow_char, ih₁, ih₂]
    | monomial n a =>
      simp only [Polynomial.aeval_monomial, mul_pow, ← pow_mul, mul_comm n p]
      congr 1
      rw [← map_pow, ZMod.pow_card a]
  -- Inductively: `Polynomial.aeval α (r ⟨m, hm⟩) = α ^ (p ^ (m + 1))` for all `m < d / 2`:
  have haeval_r : ∀ (m : ℕ) (hm : m < d / 2),
      Polynomial.aeval α (r ⟨m, hm⟩) = α ^ (p ^ (m + 1)) := by
    intro m
    induction m with
    | zero =>
      intro hm
      obtain ⟨q₁, hq₁⟩ := h1
      have h0 := congrArg (Polynomial.aeval α) hq₁
      simp only [map_pow, Polynomial.aeval_X, map_add, map_mul, hfα, mul_zero, zero_add] at h0
      simpa [pow_one] using h0.symm
    | succ m ih =>
      intro hm
      obtain ⟨q, hq⟩ := hstep m hm
      have h0 := congrArg (Polynomial.aeval α) hq
      simp only [map_add, map_mul, hfα, mul_zero, zero_add] at h0
      rw [← h0, Polynomial.aeval_comp]
      have hr0 : Polynomial.aeval α (r ⟨0, by omega⟩) = α ^ p := by
        obtain ⟨q₁, hq₁⟩ := h1
        have he := congrArg (Polynomial.aeval α) hq₁
        simp only [map_pow, Polynomial.aeval_X, map_add, map_mul, hfα, mul_zero, zero_add] at he
        exact he.symm
      rw [hr0, ← hfrob_aeval, ih (by omega), ← pow_mul, ← pow_succ]
  -- In the finite field `K = AdjoinRoot g`, `|K| = p ^ g.natDegree`, so `α ^ (p ^ g.natDegree) = α`:
  have hfin_K : Module.finrank (ZMod p) K = g.natDegree := by
    let pb := AdjoinRoot.powerBasis hgirr.ne_zero
    rw [pb.finrank, AdjoinRoot.powerBasis_dim]
  have _ : FiniteDimensional (ZMod p) K := FiniteDimensional.of_finrank_pos (by omega)
  have _ : Finite K := Module.finite_of_finite (ZMod p)
  have _ : Fintype K := Fintype.ofFinite K
  have hcard_K : Fintype.card K = p ^ g.natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := K), ZMod.card p, hfin_K]
  have hα_frob : α ^ (p ^ g.natDegree) = α := by
    rw [← hcard_K]
    exact FiniteField.pow_card α
  -- Apply the Bézout relation at index `k = g.natDegree - 1 < d / 2`:
  let idx : Fin (d / 2) := ⟨g.natDegree - 1, by omega⟩
  have hr_idx : Polynomial.aeval α (r idx) = α := by
    have h1 := haeval_r (g.natDegree - 1) (by omega)
    rw [Nat.sub_add_cancel hg1] at h1
    exact h1.trans hα_frob
  obtain ⟨u, v, huv⟩ := hbez idx
  have hcontra := congrArg (Polynomial.aeval α) huv
  simp only [map_add, map_mul, map_sub, Polynomial.aeval_X, map_one, hfα, hr_idx,
    mul_zero, sub_self, add_zero] at hcontra
  exact zero_ne_one hcontra

/-- Helper: lift irreducibility of monic `f : ℤ[X]` modulo a prime `p` directly to `ℚ[X]`. -/
private theorem irreducible_rat_of_monic_int_mod_prime {f : ℤ[X]} {n p : ℕ}
    (hf_mon : f.Monic) (hf_deg : f.natDegree = n) (hp : Nat.Prime p)
    (hirr_bar : Irreducible (modPrimePolyHom p f)) :
    Irreducible (f.map (algebraMap ℤ ℚ)) := by
  have hcop : IsGarlingRelativelyPrime (Set.range fun i : Fin (n + 1) => f.coeff i) := by
    refine ⟨⟨f.coeff n, ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩⟩, fun _ _ => one_dvd _, fun d hd => ?_⟩
    have hdn : d ∣ f.coeff n := hd (f.coeff n) ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩
    rwa [← hf_deg, hf_mon.coeff_natDegree] at hdn
  have hndvd : ¬ ((p : ℤ) ∣ f.coeff n) := by
    rw [← hf_deg, hf_mon.coeff_natDegree]
    intro h
    have h1 : p = 1 := by
      have habs := Int.isUnit_iff_natAbs_eq.mp (isUnit_of_dvd_one h)
      simpa using habs
    exact hp.ne_one h1
  have hirr_Z : Irreducible f := (theorem_5_3 hf_deg.le hcop hp hndvd hirr_bar).2.1
  exact (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map hf_mon.isPrimitive).mp hirr_Z

/-! ### Exercise 20.1 (§20.2, printed p. 160 / PDF p. 168) -/

/-- **Exercise 20.1 (literal, §20.2, printed p. 160 / PDF p. 168):**
*"Show that `x^7 + 9x^2 + 7` is irreducible over `ℚ`, and is not solvable by radicals."*

Proof:
1. Irreducibility over `ℚ`: reduction modulo `37` is verified irreducible by a pure-kernel
   Rabin certificate (pure kernel reduction via `decide`), lifted via `Theorem 5.3` and Gauss's lemma.
2. Not solvable by radicals: modulo `7`, `x^7 + 9x^2 + 7 ≡ x^2 (x - 3) (x^4 + 3x^3 + 2x^2 + 6x + 4)`,
   where the quartic factor `q(x) = 4 · Φ_5(5x)` is irreducible over `ℤ_7` by `Exercise 15.6`
   (`7 ≡ 2` generates `(ℤ_5)^*`). Hence `4 ∣ |Γ_{ℤ_7}(f̄)|`, so `4 ∣ |Γ_ℚ(f)|` by `Theorem 20.2`.
   If `f` were solvable by radicals, `Theorem 17.6` and `Theorem 20.3` would give
   `|Γ_ℚ(f)| ∣ 7 · 6 = 42`, contradicting `4 ∤ 42`. -/
theorem exercise_20_1 :
    let f : ℚ[X] := Polynomial.X ^ 7 + Polynomial.C 9 * Polynomial.X ^ 2 + Polynomial.C 7
    Irreducible f ∧
    IsGarlingIrreducible f ∧
    ¬ IsGarlingSolvableByRadicals f := by
  classical
  intro f
  let fZ : ℤ[X] := Polynomial.X ^ 7 + Polynomial.C 9 * Polynomial.X ^ 2 + Polynomial.C 7
  have hf_map : fZ.map (algebraMap ℤ ℚ) = f := by
    simp [fZ, f, map_ofNat]
  have hfZ_mon : fZ.Monic := by
    dsimp [fZ]
    have hlt : (Polynomial.C (9 : ℤ) * Polynomial.X ^ 2 + Polynomial.C 7).natDegree < 7 := by
      compute_degree!
    rw [add_assoc]
    exact Polynomial.monic_X_pow_add (Polynomial.degree_lt_iff_coeff_zero _ _ |>.mpr fun m hm =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  have hfZ_deg : fZ.natDegree = 7 := by
    dsimp [fZ]; compute_degree!
  -- Part 1: Irreducibility mod 37 via pure-kernel Rabin certificate:
  have hirr_37 : Irreducible (modPrimePolyHom 37 fZ) := by
    let lf : List (ZMod 37) := [7, 0, 9, 0, 0, 0, 0, 1]
    let lq1 : List (ZMod 37) :=
      [10, 25, 33, 24, 27, 3, 23, 0, 25, 27, 12, 9, 0, 1, 0, 11, 12, 0, 15, 0, 7, 0, 0, 30, 0, 28,
        0, 0, 0, 0, 1]
    let lr1 : List (ZMod 37) := [4, 10, 12, 14, 32, 22, 3]
    let lu1 : List (ZMod 37) := [9, 2, 10, 25, 13, 28]
    let lv1 : List (ZMod 37) := [3, 36, 11, 12, 13, 23, 3]
    let lq2 : List (ZMod 37) :=
      [10, 29, 15, 19, 12, 32, 27, 14, 33, 5, 8, 15, 3, 23, 5, 27, 14, 21, 20, 8, 35, 6, 36, 27,
        28, 0, 29, 17, 28, 4]
    let lr2 : List (ZMod 37) := [3, 10, 8, 2, 25, 35]
    let lu2 : List (ZMod 37) := [4, 3, 4, 14, 36]
    let lv2 : List (ZMod 37) := [28, 20, 29, 9, 34, 10, 18]
    let lq3 : List (ZMod 37) :=
      [0, 16, 31, 25, 15, 3, 29, 3, 21, 19, 12, 11, 36, 16, 33, 7, 28, 20, 6, 29, 9, 25, 14, 32]
    let lr3 : List (ZMod 37) := [26, 28, 7, 12, 13, 32, 12]
    let lu3 : List (ZMod 37) := [35, 36, 29, 12, 0, 13]
    let lv3 : List (ZMod 37) := [2, 11, 35, 1, 9, 7, 2]
    have hc1 : zmodListEq (zmodListXpow (p := 37) 37) (zmodListAdd (zmodListMul lq1 lf) lr1) = true := by
      decide
    have hc2 : zmodListEq (zmodListComp lr1 lr1) (zmodListAdd (zmodListMul lq2 lf) lr2) = true := by
      decide
    have hc3 : zmodListEq (zmodListComp lr2 lr1) (zmodListAdd (zmodListMul lq3 lf) lr3) = true := by
      decide
    have hb1 : zmodListEq (zmodListAdd (zmodListMul lu1 lf) (zmodListMul lv1 (zmodListAdd lr1 [0, 36]))) [1] = true := by
      decide
    have hb2 : zmodListEq (zmodListAdd (zmodListMul lu2 lf) (zmodListMul lv2 (zmodListAdd lr2 [0, 36]))) [1] = true := by
      decide
    have hb3 : zmodListEq (zmodListAdd (zmodListMul lu3 lf) (zmodListMul lv3 (zmodListAdd lr3 [0, 36]))) [1] = true := by
      decide
    have hneg36 : (36 : ZMod 37) = -1 := by decide
    have : Fact (Nat.Prime 37) := ⟨by decide⟩
    have hfeq : modPrimePolyHom 37 fZ = zmodListToPoly lf := by
      simp only [modPrimePolyHom, Polynomial.coe_mapRingHom, fZ, lf, zmodListToPoly,
        Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_ofNat, map_zero, map_one, map_ofNat]
      ring
    have hmon37 : (modPrimePolyHom 37 fZ).Monic := hfZ_mon.map _
    have hdeg37 : (modPrimePolyHom 37 fZ).natDegree = 7 := by
      rw [← hfZ_deg]; exact hfZ_mon.natDegree_map _
    let r : Fin 3 → (ZMod 37)[X] := ![zmodListToPoly lr1, zmodListToPoly lr2, zmodListToPoly lr3]
    have hsubX : ∀ l : List (ZMod 37),
        zmodListToPoly (zmodListAdd l [0, (36 : ZMod 37)]) = zmodListToPoly l - Polynomial.X := by
      intro l
      rw [zmodListToPoly_add]
      have h36 : zmodListToPoly [0, (36 : ZMod 37)] = -Polynomial.X := by
        simp only [zmodListToPoly, map_zero, zero_add, mul_zero, add_zero]
        rw [hneg36, map_neg, map_one]; ring
      rw [h36, sub_eq_add_neg]
    refine irreducible_of_rabin_certificate hmon37 hdeg37 (by decide) r ?_ ?_ ?_
    · refine ⟨zmodListToPoly lq1, ?_⟩
      have h := zmodListToPoly_eq_of_listEq hc1
      rw [zmodListToPoly_Xpow, zmodListToPoly_add, zmodListToPoly_mul, ← hfeq] at h
      exact h
    · intro k hk
      have hk_cases : k = 0 ∨ k = 1 := by omega
      rcases hk_cases with rfl | rfl
      · refine ⟨zmodListToPoly lq2, ?_⟩
        have h := zmodListToPoly_eq_of_listEq hc2
        rw [zmodListToPoly_comp, zmodListToPoly_add, zmodListToPoly_mul, ← hfeq] at h
        exact h
      · refine ⟨zmodListToPoly lq3, ?_⟩
        have h := zmodListToPoly_eq_of_listEq hc3
        rw [zmodListToPoly_comp, zmodListToPoly_add, zmodListToPoly_mul, ← hfeq] at h
        exact h
    · intro k
      fin_cases k
      · refine ⟨zmodListToPoly lu1, zmodListToPoly lv1, ?_⟩
        have h := zmodListToPoly_eq_of_listEq hb1
        rw [zmodListToPoly_add, zmodListToPoly_mul, zmodListToPoly_mul, ← hfeq, hsubX] at h
        simpa [r, zmodListToPoly] using h
      · refine ⟨zmodListToPoly lu2, zmodListToPoly lv2, ?_⟩
        have h := zmodListToPoly_eq_of_listEq hb2
        rw [zmodListToPoly_add, zmodListToPoly_mul, zmodListToPoly_mul, ← hfeq, hsubX] at h
        simpa [r, zmodListToPoly] using h
      · refine ⟨zmodListToPoly lu3, zmodListToPoly lv3, ?_⟩
        have h := zmodListToPoly_eq_of_listEq hb3
        rw [zmodListToPoly_add, zmodListToPoly_mul, zmodListToPoly_mul, ← hfeq, hsubX] at h
        simpa [r, zmodListToPoly] using h
  have hirr_f : Irreducible f := hf_map ▸ irreducible_rat_of_monic_int_mod_prime hfZ_mon hfZ_deg (by decide) hirr_37
  refine ⟨hirr_f, (isGarlingIrreducible_iff f).mpr hirr_f, ?_⟩
  -- Part 2: Not solvable by radicals (via mod-7 factorization + Theorem 20.2 + Theorem 20.3):
  intro hsol_rad
  have h9_mod7 : (9 : ZMod 7) = 2 := by decide
  have h7_mod7 : (7 : ZMod 7) = 0 := by decide
  have h4_mod7_neg3 : (4 : ZMod 7) = -3 := by decide
  have h4_mod7_ne0 : (4 : ZMod 7) ≠ 0 := by decide
  have hc4_mod7 : (4 : ZMod 7) * 5 ^ 4 = 1 := by decide
  have hc3_mod7 : (4 : ZMod 7) * 5 ^ 3 = 3 := by decide
  have hc2_mod7 : (4 : ZMod 7) * 5 ^ 2 = 2 := by decide
  have hc1_mod7 : (4 : ZMod 7) * 5 = 6 := by decide
  have h5_mul_3_mod7 : (5 : ZMod 7) * 3 = 1 := by decide
  have h3_mul_5_mod7 : (3 : ZMod 7) * 5 = 1 := by decide
  have hl_mod7 : zmodListEq [0, 0, (2 : ZMod 7), 0, 0, 0, 0, 1]
      (zmodListMul (zmodListMul [0, 0, 1] [4, 1]) [4, 6, 2, 3, 1]) = true := by decide
  have hu5_cases : ∀ u : Garling.Chapter15.GarlingUnitsZMod 5,
      u = 1 ∨ u = ZMod.unitOfCoprime 2 (by decide) ∨
        u = ZMod.unitOfCoprime 3 (by decide) ∨ u = ZMod.unitOfCoprime 4 (by decide) := by decide
  have hp7_pow1 : (ZMod.unitOfCoprime 7 (by decide) : Garling.Chapter15.GarlingUnitsZMod 5) ^ (1 : ℤ) =
      ZMod.unitOfCoprime 2 (by decide) := by decide
  have hp7_pow3 : (ZMod.unitOfCoprime 7 (by decide) : Garling.Chapter15.GarlingUnitsZMod 5) ^ (3 : ℤ) =
      ZMod.unitOfCoprime 3 (by decide) := by decide
  have hp7_pow2 : (ZMod.unitOfCoprime 7 (by decide) : Garling.Chapter15.GarlingUnitsZMod 5) ^ (2 : ℤ) =
      ZMod.unitOfCoprime 4 (by decide) := by decide
  have hp7 : Nat.Prime 7 := by decide
  have : Fact (Nat.Prime 7) := ⟨hp7⟩
  let f7 : (ZMod 7)[X] := modPrimePolyHom 7 fZ
  let q7 : (ZMod 7)[X] :=
    Polynomial.X ^ 4 + Polynomial.C 3 * Polynomial.X ^ 3 + Polynomial.C 2 * Polynomial.X ^ 2 +
      Polynomial.C 6 * Polynomial.X + Polynomial.C 4
  have hf7_fac : f7 = Polynomial.X ^ 2 * (Polynomial.X - Polynomial.C 3) * q7 := by
    have hf7_eq : f7 = Polynomial.X ^ 7 + Polynomial.C 2 * Polynomial.X ^ 2 := by
      have h1 : f7 = (Polynomial.X ^ 7 + Polynomial.C (9 : ℤ) * Polynomial.X ^ 2 +
          Polynomial.C (7 : ℤ)).map (Int.castRingHom (ZMod 7)) := rfl
      rw [h1]
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_C]
      change Polynomial.X ^ 7 + Polynomial.C (9 : ZMod 7) * Polynomial.X ^ 2 + Polynomial.C (7 : ZMod 7) = _
      rw [h9_mod7, h7_mod7, map_zero, add_zero]
    rw [hf7_eq]
    dsimp [q7]
    have hp := zmodListToPoly_eq_of_listEq hl_mod7
    rw [zmodListToPoly_mul, zmodListToPoly_mul] at hp
    have hlhs : zmodListToPoly [0, 0, (2 : ZMod 7), 0, 0, 0, 0, 1] =
        Polynomial.X ^ 7 + Polynomial.C 2 * Polynomial.X ^ 2 := by
      dsimp [zmodListToPoly]; rw [map_zero, map_one]; ring
    have hrhs1 : zmodListToPoly [0, 0, (1 : ZMod 7)] = Polynomial.X ^ 2 := by
      dsimp [zmodListToPoly]; rw [map_zero, map_one]; ring
    have hrhs2 : zmodListToPoly [(4 : ZMod 7), 1] = Polynomial.X - Polynomial.C 3 := by
      dsimp [zmodListToPoly]; rw [map_one, h4_mod7_neg3, map_neg]; ring
    have hrhs3 : zmodListToPoly [(4 : ZMod 7), 6, 2, 3, 1] =
        Polynomial.X ^ 4 + Polynomial.C 3 * Polynomial.X ^ 3 + Polynomial.C 2 * Polynomial.X ^ 2 +
          Polynomial.C 6 * Polynomial.X + Polynomial.C 4 := by
      dsimp [zmodListToPoly]; rw [map_one]; ring
    rw [hlhs, hrhs1, hrhs2, hrhs3] at hp
    exact hp
  -- `q7` is irreducible over `ℤ_7` via `Chapter15.exercise_15_6` on `Φ_5`:
  have hphi5_irr : Irreducible (Polynomial.cyclotomic 5 (ZMod 7)) := by
    have h156 := (Garling.Chapter15.exercise_15_6.{0}.1 hp7 (by decide : ¬ (7 ∣ 5))).2.1
    rw [h156, eq_top_iff]
    intro u _
    let p7 : Garling.Chapter15.GarlingUnitsZMod 5 := ZMod.unitOfCoprime 7 (by decide)
    change u ∈ Subgroup.zpowers p7
    rcases hu5_cases u with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact ⟨(1 : ℤ), hp7_pow1⟩
    · exact ⟨(3 : ℤ), hp7_pow3⟩
    · exact ⟨(2 : ℤ), hp7_pow2⟩
  have hq7_irr : Irreducible q7 := by
    have : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hphi5_eq : Polynomial.cyclotomic 5 (ZMod 7) =
        Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1 := by
      rw [Polynomial.cyclotomic_prime (ZMod 7) 5]
      simp [Finset.sum_range_succ]; ring
    let aut : (ZMod 7)[X] ≃+* (ZMod 7)[X] :=
      { toFun := fun P => P.comp (Polynomial.C 5 * Polynomial.X)
        invFun := fun P => P.comp (Polynomial.C 3 * Polynomial.X)
        left_inv := fun P => by
          dsimp only
          rw [Polynomial.comp_assoc]
          have h15 : (Polynomial.C (5 : ZMod 7) * Polynomial.X).comp (Polynomial.C 3 * Polynomial.X) =
              Polynomial.X := by
            simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
            rw [← mul_assoc, ← map_mul, h5_mul_3_mod7, map_one, one_mul]
          rw [h15, Polynomial.comp_X]
        right_inv := fun P => by
          dsimp only
          rw [Polynomial.comp_assoc]
          have h15 : (Polynomial.C (3 : ZMod 7) * Polynomial.X).comp (Polynomial.C 5 * Polynomial.X) =
              Polynomial.X := by
            simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
            rw [← mul_assoc, ← map_mul, h3_mul_5_mod7, map_one, one_mul]
          rw [h15, Polynomial.comp_X]
        map_mul' := fun P Q => Polynomial.mul_comp P Q _
        map_add' := fun _ _ => Polynomial.add_comp }
    have hirr_aut : Irreducible (aut (Polynomial.cyclotomic 5 (ZMod 7))) := by
      refine ⟨fun hu => hphi5_irr.1 (by simpa using hu.map aut.symm.toRingHom), fun a b hab => ?_⟩
      have hab' : Polynomial.cyclotomic 5 (ZMod 7) = aut.symm a * aut.symm b := by
        rw [← map_mul, ← hab, aut.symm_apply_apply]
      rcases hphi5_irr.2 hab' with ha | hb
      · exact Or.inl (by simpa using ha.map aut.toRingHom)
      · exact Or.inr (by simpa using hb.map aut.toRingHom)
    have h4_unit : IsUnit (Polynomial.C (4 : ZMod 7)) :=
      (isUnit_iff_ne_zero.mpr h4_mod7_ne0).map Polynomial.C
    have hq7_eq : q7 = Polynomial.C (4 : ZMod 7) * aut (Polynomial.cyclotomic 5 (ZMod 7)) := by
      dsimp [aut]
      rw [hphi5_eq]
      simp only [Polynomial.add_comp, Polynomial.pow_comp, Polynomial.X_comp, Polynomial.one_comp,
        mul_pow, ← map_pow]
      dsimp [q7]
      calc Polynomial.X ^ 4 + Polynomial.C 3 * Polynomial.X ^ 3 + Polynomial.C 2 * Polynomial.X ^ 2 +
              Polynomial.C 6 * Polynomial.X + Polynomial.C 4
          = Polynomial.C ((4 : ZMod 7) * 5 ^ 4) * Polynomial.X ^ 4 +
            Polynomial.C ((4 : ZMod 7) * 5 ^ 3) * Polynomial.X ^ 3 +
            Polynomial.C ((4 : ZMod 7) * 5 ^ 2) * Polynomial.X ^ 2 +
            Polynomial.C ((4 : ZMod 7) * 5) * Polynomial.X + Polynomial.C 4 := by
              rw [hc4_mod7, hc3_mod7, hc2_mod7, hc1_mod7, map_one, one_mul]
        _ = _ := by simp only [map_mul, map_pow]; ring
    rw [hq7_eq]
    exact (associated_unit_mul_left _ _ h4_unit).irreducible_iff.mpr hirr_aut
  -- Splitting fields `L` of `f` over `ℚ` and `M` of `f7` over `ℤ_7`:
  let L := Polynomial.SplittingField f
  have hsfL : IsGarlingSplittingFieldExtension ℚ L f :=
    (isGarlingSplittingFieldExtension_iff ℚ L f).mpr inferInstance
  let M := Polynomial.SplittingField f7
  have hsfM : IsGarlingSplittingFieldExtension (ZMod 7) M f7 :=
    (isGarlingSplittingFieldExtension_iff (ZMod 7) M f7).mpr inferInstance
  -- `4 ∣ |Γ_{ℤ_7}(f7)|`:
  have h4_dvd_M : 4 ∣ Nat.card (GarlingPolyGaloisGroup (ZMod 7) M f7) := by
    have _ : FiniteDimensional (ZMod 7) M := Polynomial.IsSplittingField.finiteDimensional M f7
    have _ : Finite M := Module.finite_of_finite (ZMod 7)
    have hcard_M : Nat.card (GarlingPolyGaloisGroup (ZMod 7) M f7) = Module.finrank (ZMod 7) M :=
      (Garling.Chapter12.corollary_to_theorem_12_4 (K := ZMod 7) (L := M)).2.1
    rw [hcard_M]
    have hq7_spl : (q7.map (algebraMap (ZMod 7) M)).Splits :=
      ((isGarlingSplittingFieldExtension_iff (ZMod 7) M f7).mp hsfM).splits.of_dvd
        (Polynomial.map_monic_ne_zero (hfZ_mon.map _))
        (Polynomial.map_dvd _ ⟨Polynomial.X ^ 2 * (Polynomial.X - Polynomial.C 3),
          hf7_fac.trans (mul_comm _ _)⟩)
    have hq7_deg : q7.natDegree = 4 := by dsimp [q7]; compute_degree!
    have hq7_mon : q7.Monic := by
      have hlt : (Polynomial.C (3 : ZMod 7) * Polynomial.X ^ 3 + Polynomial.C 2 * Polynomial.X ^ 2 +
          Polynomial.C 6 * Polynomial.X + Polynomial.C 4).natDegree < 4 := by compute_degree!
      have hrew : q7 = Polynomial.X ^ 4 + (Polynomial.C (3 : ZMod 7) * Polynomial.X ^ 3 +
          Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 6 * Polynomial.X + Polynomial.C 4) := by
        dsimp [q7]; ring
      rw [hrew]
      exact Polynomial.monic_X_pow_add (Polynomial.degree_lt_iff_coeff_zero _ _ |>.mpr fun m hm =>
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
    have hdeg_ne0 : (q7.map (algebraMap (ZMod 7) M)).degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree (Polynomial.map_monic_ne_zero hq7_mon),
        Polynomial.natDegree_map_eq_of_injective (algebraMap (ZMod 7) M).injective, hq7_deg]
      decide
    obtain ⟨α, hα⟩ := Polynomial.Splits.exists_eval_eq_zero hq7_spl hdeg_ne0
    have hα_aeval : Polynomial.aeval α q7 = 0 := by
      rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    have hmin : minpoly (ZMod 7) α = q7 :=
      (minpoly.eq_of_irreducible_of_monic hq7_irr hα_aeval hq7_mon).symm
    have hfin_α : Module.finrank (ZMod 7) ((ZMod 7)⟮α⟯ : IntermediateField (ZMod 7) M) = 4 := by
      rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α), hmin, hq7_deg]
    rw [← hfin_α]
    exact ⟨Module.finrank ((ZMod 7)⟮α⟯ : IntermediateField (ZMod 7) M) M,
      (Module.finrank_mul_finrank (ZMod 7) ((ZMod 7)⟮α⟯ : IntermediateField (ZMod 7) M) M).symm⟩
  -- Shared facts about `f` over `L`:
  have hf_mon : f.Monic := hf_map ▸ hfZ_mon.map _
  have hf_deg : f.natDegree = 7 := by rw [← hf_map, hfZ_mon.natDegree_map, hfZ_deg]
  have hcard_roots : (garlingRootSet ℚ L f).ncard = 7 := by
    have hsfLm := (isGarlingSplittingFieldExtension_iff ℚ L f).mp hsfL
    rw [garlingRootSet_eq_rootSet hf_mon.ne_zero]
    have hset : f.rootSet L = ((f.map (algebraMap ℚ L)).roots.toFinset : Set L) := by
      ext x
      simp [Polynomial.mem_rootSet_of_ne hf_mon.ne_zero,
        Polynomial.mem_roots (Polynomial.map_monic_ne_zero hf_mon), Polynomial.IsRoot,
        Polynomial.eval_map, ← Polynomial.aeval_def]
    rw [hset, Set.ncard_coe_finset,
      Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hirr_f.separable.map),
      Polynomial.splits_iff_card_roots.mp hsfLm.splits,
      Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ L).injective, hf_deg]
  -- By `Theorem 20.2`, `4 ∣ |Γ_ℚ(f)|`:
  have h4_dvd_L : 4 ∣ Nat.card (GarlingPolyGaloisGroup ℚ L f) := by
    have hdist : ¬ HasGarlingRepeatedRoot ℚ L (fZ.map (algebraMap ℤ ℚ)) := by
      rw [hf_map]
      intro hrep
      obtain ⟨z, hz, hdz⟩ := (theorem_10_5 hf_mon.ne_zero hsfL).1.mp hrep
      obtain ⟨u, v, huv⟩ := hirr_f.separable
      have h0' := congrArg (Polynomial.aeval z) huv
      rw [map_add, map_mul, map_mul, map_one, show Polynomial.aeval z f = 0 from hz,
        show Polynomial.aeval z (Polynomial.derivative f) = 0 from by
          rwa [← garlingDeriv_eq_derivative], mul_zero, mul_zero, add_zero] at h0'
      exact zero_ne_one h0'
    obtain ⟨_, H, ⟨eMH⟩⟩ := theorem_20_2 hfZ_mon hp7 (hf_map.symm ▸ hsfL) hdist hsfM
    have hcard_H : Nat.card H = Nat.card (GarlingPolyGaloisGroup (ZMod 7) M f7) :=
      Nat.card_congr eMH.symm.toEquiv
    exact h4_dvd_M.trans (hcard_H ▸ Subgroup.card_subgroup_dvd_card H)
  -- On the other hand, solvability by radicals + `Theorem 17.6` + `Theorem 20.3` forces `|Γ_ℚ(f)| ∣ 42`:
  have hsol_gal : IsGarlingSoluble (GarlingPolyGaloisGroup ℚ L f) := by
    rcases hsol_rad with ⟨E, fE, aE, hradE, hsplE⟩
    let _ : Field E := fE
    let _ : Algebra ℚ E := aE
    obtain ⟨r, T, β, ns, h0, hlast, hchar, hstep⟩ :=
      isGarlingRadicalExtensionNotCharDvd_of_charZero hradE
    exact theorem_17_6 h0 hlast hstep hchar hsplE hsfL
  have hcard_dvd_42 : Nat.card (GarlingPolyGaloisGroup ℚ L f) ∣ 42 := by
    have _ : Finite (garlingRootSet ℚ L f) := Set.finite_of_ncard_pos (by omega)
    let eR : Fin 7 ≃ garlingRootSet ℚ L f :=
      (Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, hcard_roots])).symm
    let φ := garlingRootLabellingPermHom eR
    have hφ_inj : Function.Injective φ := fun σ₁ σ₂ h => by
      apply theorem_11_6 hsfL
      ext ⟨r, hr⟩
      have h1 := Equiv.congr_fun h (eR.symm ⟨r, hr⟩)
      have h2 := congrArg (fun x : Fin 7 => (eR x : L)) h1
      simpa [φ] using h2
    have hG_trans : SubgroupActsTransitively φ.range := by
      intro i j
      obtain ⟨σ, hσ⟩ := corollary_2_to_theorem_7_5_algEquiv hirr_f hsfL (eR i).2 (eR j).2
      refine ⟨φ σ, ⟨σ, rfl⟩, eR.injective (Subtype.ext ?_)⟩
      simpa [φ] using hσ
    let eG : GarlingPolyGaloisGroup ℚ L f ≃* φ.range :=
      MulEquiv.ofBijective φ.rangeRestrict
        ⟨fun a b hab => hφ_inj (congrArg Subtype.val hab), φ.rangeRestrict_surjective⟩
    have hG_sol : IsGarlingSoluble φ.range := (isGarlingSoluble_congr eG).mp hsol_gal
    rw [Nat.card_congr eG.toEquiv]
    exact (theorem_20_3_repaired hp7 hG_trans hG_sol).2.2
  have h4_dvd_42 : 4 ∣ 42 := h4_dvd_L.trans hcard_dvd_42
  omega

/-! ### Exercise 20.3 (§20.2, printed p. 160 / PDF p. 168 — `QUEUE.md` semi-open final prompt) -/

/-- Helper: every involution `σ` (`σ * σ = 1`) on a finite type `α` has an even number `2s` of
non-fixed points and sign `(-1)^s`. -/
private theorem sign_of_involution {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (hinv : σ * σ = 1) :
    ∃ s : ℕ, (Finset.univ.filter fun x => σ x ≠ x).card = 2 * s ∧
      (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ s := by
  classical
  have hind : ∀ n : ℕ, ∀ σ : Equiv.Perm α, σ * σ = 1 →
      (Finset.univ.filter fun x => σ x ≠ x).card = n →
      ∃ s : ℕ, n = 2 * s ∧ (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro σ hinv hcard
      by_cases h0 : n = 0
      · subst h0
        have hσ1 : σ = 1 := by
          ext x
          by_contra hne
          change σ x ≠ x at hne
          have hmem : x ∈ Finset.univ.filter (fun y => σ y ≠ y) := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hne⟩
          have hpos : 0 < (Finset.univ.filter (fun y => σ y ≠ y)).card := Finset.card_pos.mpr ⟨x, hmem⟩
          omega
        exact ⟨0, rfl, by rw [hσ1, map_one]; rfl⟩
      · have hne : (Finset.univ.filter fun x => σ x ≠ x).Nonempty :=
          Finset.card_pos.mp (by omega)
        obtain ⟨a, ha⟩ := hne
        have ha_ne : σ a ≠ a := (Finset.mem_filter.mp ha).2
        let b := σ a
        have hσb : σ b = a := by
          have := Equiv.congr_fun hinv a
          simpa [b] using this
        have hba_ne : b ≠ a := ha_ne
        let τ : Equiv.Perm α := σ * Equiv.swap a b
        have hτ_inv : τ * τ = 1 := by
          ext x
          change σ (Equiv.swap a b (σ (Equiv.swap a b x))) = x
          by_cases hxa : x = a
          · subst hxa; simp [Equiv.swap_apply_left, hσb, b]
          · by_cases hxb : x = b
            · subst hxb; simp [Equiv.swap_apply_right, b]
            · have hσx_a : σ x ≠ a := fun h => hxb (by
                have h1 := congrArg σ h
                rw [show σ (σ x) = x from Equiv.congr_fun hinv x] at h1
                exact h1)
              have hσx_b : σ x ≠ b := fun h => hxa (σ.injective h)
              rw [Equiv.swap_apply_of_ne_of_ne hxa hxb, Equiv.swap_apply_of_ne_of_ne hσx_a hσx_b]
              exact Equiv.congr_fun hinv x
        have hsupp_eq : (Finset.univ.filter fun x => σ x ≠ x) =
            insert a (insert b (Finset.univ.filter fun x => τ x ≠ x)) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          by_cases hxa : x = a
          · subst hxa; simp [ha_ne]
          · by_cases hxb : x = b
            · subst hxb; simp [hσb, hba_ne.symm]
            · have hτx : τ x = σ x := by
                change σ (Equiv.swap a b x) = σ x
                rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
              simp [hxa, hxb, hτx]
        have ha_not : a ∉ insert b (Finset.univ.filter fun x => τ x ≠ x) := by
          simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not]
          refine ⟨hba_ne.symm, ?_⟩
          change σ (Equiv.swap a b a) = a
          rw [Equiv.swap_apply_left]; exact hσb
        have hb_not : b ∉ (Finset.univ.filter fun x => τ x ≠ x) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
          change σ (Equiv.swap a b b) = b
          rw [Equiv.swap_apply_right]
        have hcard_τ : (Finset.univ.filter fun x => τ x ≠ x).card + 2 = n := by
          rw [← hcard, hsupp_eq, Finset.card_insert_of_notMem ha_not,
            Finset.card_insert_of_notMem hb_not]
        obtain ⟨s', hs', hsign_τ⟩ := ih (n - 2) (by omega) τ hτ_inv (by omega)
        refine ⟨s' + 1, by omega, ?_⟩
        have hsign_mul : (Equiv.Perm.sign τ : ℤ) =
            (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign (Equiv.swap a b) : ℤ) := by
          rw [show τ = σ * Equiv.swap a b from rfl, map_mul, Units.val_mul]
        rw [Equiv.Perm.sign_swap hba_ne.symm] at hsign_mul
        simp only [Units.val_neg, Units.val_one, mul_neg, mul_one] at hsign_mul
        rw [hsign_τ] at hsign_mul
        rw [pow_succ]
        linarith
  exact hind _ σ hinv rfl

/-- Helper: given an irreducible `f ∈ ℚ[X]` of odd prime degree `p` which is solvable by radicals,
construct its complex splitting field `L ≤ ℂ`, complex conjugation `τ ∈ Γ_ℚ(f)`, and prove the
exact root-count + discriminant-sign formula `sgn(Δ) = (-1)^s` where `s = 0` (if all `p` roots are
real) or `s = (p - 1)/2` (if `f` has exactly `1` real root). -/
private theorem exercise_20_3_core {p : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p)
    {f : ℚ[X]} (hirr : Irreducible f) (hdeg : f.natDegree = p)
    (hsol : IsGarlingSolvableByRadicals f) :
    -- Case 1: all `p` roots in `ℂ` are real, and `Δ > 0`; OR
    ((∀ z ∈ garlingRootSet ℚ ℂ f, z.im = 0) ∧
      {x : ℝ | Polynomial.aeval x f = 0}.ncard = p ∧
      0 < garlingDiscriminant f) ∨
    -- Case 2: exactly `1` real root (`p - 1` non-real roots), and `Δ` has sign `(-1)^((p-1)/2)`:
    ({x : ℝ | Polynomial.aeval x f = 0}.ncard = 1 ∧
      {z ∈ garlingRootSet ℚ ℂ f | z.im ≠ 0}.ncard = p - 1 ∧
      (p % 4 = 3 → garlingDiscriminant f < 0) ∧
      (p % 4 = 1 → 0 < garlingDiscriminant f)) := by
  classical
  have hf0 : f ≠ 0 := hirr.ne_zero
  have hf_sep : f.Separable := hirr.separable
  have hf_splC : (f.map (algebraMap ℚ ℂ)).Splits := IsAlgClosed.splits _
  have hcard_C : (garlingRootSet ℚ ℂ f).ncard = p := by
    rw [garlingRootSet_eq_rootSet hf0]
    have hset : f.rootSet ℂ = ((f.map (algebraMap ℚ ℂ)).roots.toFinset : Set ℂ) := by
      ext z
      simp [Polynomial.mem_rootSet_of_ne hf0,
        Polynomial.mem_roots ((Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).mpr hf0),
        Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    rw [hset, Set.ncard_coe_finset,
      Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hf_sep.map),
      Polynomial.splits_iff_card_roots.mp hf_splC,
      Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective, hdeg]
  -- Enumerate the `p` distinct complex roots `α : Fin p → ℂ` and get `GarlingSplitsExplicit ℚ ℂ f p f.leadingCoeff α`:
  have _ : Finite (garlingRootSet ℚ ℂ f) := Set.finite_of_ncard_pos (by omega)
  let eC : Fin p ≃ garlingRootSet ℚ ℂ f :=
    (Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, hcard_C])).symm
  let α : Fin p → ℂ := fun i => (eC i : ℂ)
  have hα_inj : Function.Injective α := fun i j h => eC.injective (Subtype.ext h)
  have hα_range : Set.range α = garlingRootSet ℚ ℂ f := by
    ext z
    simp only [Set.mem_range, α]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ (eC i).2, fun hz => ⟨eC.symm ⟨z, hz⟩, by simp⟩⟩
  have hexpC : GarlingSplitsExplicit ℚ ℂ f p f.leadingCoeff α := by
    unfold GarlingSplitsExplicit
    have hfac := (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
      (Polynomial.splits_iff_card_roots.mp hf_splC)).symm
    have hlc : (f.map (algebraMap ℚ ℂ)).leadingCoeff = algebraMap ℚ ℂ f.leadingCoeff :=
      Polynomial.leadingCoeff_map_of_injective (algebraMap ℚ ℂ).injective f
    rw [hlc] at hfac
    have hnodup : (f.map (algebraMap ℚ ℂ)).roots.Nodup := Polynomial.nodup_roots hf_sep.map
    have hfin_eq : (f.map (algebraMap ℚ ℂ)).roots.toFinset = Finset.univ.image α := by
      ext z
      simp only [Multiset.mem_toFinset, Polynomial.mem_roots
        ((Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).mpr hf0), Polynomial.IsRoot,
        Finset.mem_image, Finset.mem_univ, true_and, α]
      constructor
      · intro hz
        have hmem : z ∈ garlingRootSet ℚ ℂ f := by
          rw [garlingRootSet_eq_rootSet hf0, Polynomial.mem_rootSet_of_ne hf0,
            Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
          exact hz
        exact ⟨eC.symm ⟨z, hmem⟩, by simp⟩
      · rintro ⟨i, rfl⟩
        have hmem : α i ∈ garlingRootSet ℚ ℂ f := (eC i).2
        rw [garlingRootSet_eq_rootSet hf0, Polynomial.mem_rootSet_of_ne hf0,
          Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at hmem
        exact hmem
    have hprod_eq : ((f.map (algebraMap ℚ ℂ)).roots.map fun a => Polynomial.X - Polynomial.C a).prod =
        ∏ i : Fin p, (Polynomial.X - Polynomial.C (α i)) := by
      have h1 : (f.map (algebraMap ℚ ℂ)).roots = ((f.map (algebraMap ℚ ℂ)).roots.toFinset).val :=
        ((Multiset.toFinset_val _).trans (Multiset.dedup_eq_self.mpr hnodup)).symm
      conv_lhs => rw [h1, hfin_eq]
      change ∏ z ∈ Finset.univ.image α, (Polynomial.X - Polynomial.C z) = _
      exact Finset.prod_image fun i _ j _ h => hα_inj h
    rw [hfac, hprod_eq]
  -- Complex splitting field `L = ℚ(α_0, …, α_{p-1}) ≤ ℂ` via `Theorem 7.1`:
  let L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range α)
  have hsfL : IsGarlingSplittingFieldExtension ℚ L f := theorem_7_1 hf0 hexpC
  let αL : Fin p → L := fun i => ⟨α i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩
  have hαL_root : ∀ i : Fin p, αL i ∈ garlingRootSet ℚ L f := by
    intro i
    change Polynomial.aeval (αL i) f = 0
    apply L.val.injective
    change L.val (Polynomial.aeval (αL i) f) = L.val 0
    have h1 : L.val (Polynomial.aeval (αL i) f) = Polynomial.aeval (α i) f :=
      (Polynomial.aeval_algHom_apply L.val (αL i) f).symm
    rw [h1, map_zero]
    exact (eC i).2
  have hαL_bij : Function.Bijective (fun i : Fin p => (⟨αL i, hαL_root i⟩ : garlingRootSet ℚ L f)) := by
    refine ⟨fun i j h => hα_inj (congrArg (fun u : garlingRootSet ℚ L f => (u.1 : ℂ)) h), ?_⟩
    rintro ⟨⟨z, hzL⟩, hz⟩
    have hzC : z ∈ garlingRootSet ℚ ℂ f := by
      change Polynomial.aeval z f = 0
      have h1 : L.val (Polynomial.aeval (⟨z, hzL⟩ : L) f) = Polynomial.aeval z f :=
        (Polynomial.aeval_algHom_apply L.val (⟨z, hzL⟩ : L) f).symm
      rw [← h1, hz, map_zero]
    exact ⟨eC.symm ⟨z, hzC⟩, Subtype.ext (Subtype.ext (by simp [αL, α]))⟩
  let eL : Fin p ≃ garlingRootSet ℚ L f := Equiv.ofBijective _ hαL_bij
  -- Restrict `complexConjAlgEquiv : ℂ ≃ₐ[ℚ] ℂ` to `τ : GarlingPolyGaloisGroup ℚ L f`:
  have hconj_mem : ∀ z ∈ L, complexConjAlgEquiv z ∈ L := by
    intro z hz
    let M : IntermediateField ℚ ℂ := L.comap complexConjAlgEquiv.toAlgHom
    have hle : L ≤ M := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      have hroot_conj : complexConjAlgEquiv (α i) ∈ garlingRootSet ℚ ℂ f := by
        change Polynomial.aeval (complexConjAlgEquiv (α i)) f = 0
        rw [Polynomial.aeval_algHom_apply, (eC i).2, map_zero]
      rw [← hα_range] at hroot_conj
      exact IntermediateField.subset_adjoin ℚ _ hroot_conj
    exact hle hz
  let τ : GarlingPolyGaloisGroup ℚ L f :=
    { toFun := fun x => ⟨complexConjAlgEquiv x.1, hconj_mem x.1 x.2⟩
      invFun := fun x => ⟨complexConjAlgEquiv x.1, hconj_mem x.1 x.2⟩
      left_inv := fun x => Subtype.ext (by simp [complexConjAlgEquiv])
      right_inv := fun x => Subtype.ext (by simp [complexConjAlgEquiv])
      map_mul' := fun x y => Subtype.ext (map_mul complexConjAlgEquiv x.1 y.1)
      map_add' := fun x y => Subtype.ext (map_add complexConjAlgEquiv x.1 y.1)
      commutes' := fun q => Subtype.ext (complexConjAlgEquiv.commutes q) }
  have hτ_sq : τ * τ = 1 := by
    ext x
    change complexConjAlgEquiv (complexConjAlgEquiv x.1) = x.1
    simp [complexConjAlgEquiv]
  -- Embed `Γ_ℚ(f)` into `Σ_p` via `φ = garlingRootLabellingPermHom eL`:
  let φ := garlingRootLabellingPermHom eL
  have hφ_inj : Function.Injective φ := fun σ₁ σ₂ h => by
    apply theorem_11_6 hsfL
    ext ⟨r, hr⟩
    have h1 := Equiv.congr_fun h (eL.symm ⟨r, hr⟩)
    have h2 := congrArg (fun x : Fin p => (eL x : L)) h1
    simpa [φ] using h2
  have hG_trans : SubgroupActsTransitively φ.range := by
    intro i j
    obtain ⟨σ, hσ⟩ := corollary_2_to_theorem_7_5_algEquiv hirr hsfL (eL i).2 (eL j).2
    refine ⟨φ σ, ⟨σ, rfl⟩, eL.injective (Subtype.ext ?_)⟩
    simpa [φ] using hσ
  have hsol_gal : IsGarlingSoluble (GarlingPolyGaloisGroup ℚ L f) := by
    rcases hsol with ⟨E, fE, aE, hradE, hsplE⟩
    let _ : Field E := fE
    let _ : Algebra ℚ E := aE
    obtain ⟨r, T, β, ns, h0, hlast, hchar, hstep⟩ :=
      isGarlingRadicalExtensionNotCharDvd_of_charZero hradE
    exact theorem_17_6 h0 hlast hstep hchar hsplE hsfL
  let eG : GarlingPolyGaloisGroup ℚ L f ≃* φ.range :=
    MulEquiv.ofBijective φ.rangeRestrict
      ⟨fun a b hab => hφ_inj (congrArg Subtype.val hab), φ.rangeRestrict_surjective⟩
  have hG_sol : IsGarlingSoluble φ.range := (isGarlingSoluble_congr eG).mp hsol_gal
  -- Characterize fixed points of `φ τ` as real roots:
  let σ : SigmaN p := φ τ
  have hσ_inv : σ * σ = 1 := by
    dsimp [σ]; rw [← map_mul, hτ_sq, map_one]
  have hσ_fix_iff : ∀ i : Fin p, σ i = i ↔ (α i).im = 0 := by
    intro i
    have happ : α (σ i) = complexConjAlgEquiv (α i) := by
      have h1 := garlingRootLabellingPermHom_apply eL τ i
      exact congrArg Subtype.val h1
    constructor
    · intro hfix
      rw [hfix] at happ
      exact (complexConjAlgEquiv_eq_self_iff (α i)).mp happ.symm
    · intro him
      apply hα_inj
      rw [happ, (complexConjAlgEquiv_eq_self_iff (α i)).mpr him]
  -- Bijection between real roots `{x : ℝ | aeval x f = 0}` and `{i : Fin p | (α i).im = 0}`:
  have hreal_card : {x : ℝ | Polynomial.aeval x f = 0}.ncard =
      (Finset.univ.filter fun i : Fin p => σ i = i).card := by
    let Sfix : Finset (Fin p) := Finset.univ.filter fun i => σ i = i
    have hset_eq : {x : ℝ | Polynomial.aeval x f = 0} = ((Sfix.image fun i => (α i).re) : Set ℝ) := by
      ext x
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_image, Sfix, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro hx
        have hxC : (x : ℂ) ∈ garlingRootSet ℚ ℂ f := by
          change Polynomial.aeval (algebraMap ℝ ℂ x) f = 0
          rw [Polynomial.aeval_algebraMap_apply, hx, map_zero]
        rw [← hα_range] at hxC
        obtain ⟨i, hi⟩ := hxC
        refine ⟨i, (hσ_fix_iff i).mpr (by rw [hi]; simp), ?_⟩
        rw [hi]; simp
      · rintro ⟨i, hfix, rfl⟩
        have him : (α i).im = 0 := (hσ_fix_iff i).mp hfix
        have hcoe : ((α i).re : ℂ) = α i := Complex.ext rfl (by simp [him])
        have hC0 : Polynomial.aeval (α i) f = 0 := (eC i).2
        rw [← hcoe] at hC0
        have h1 : algebraMap ℝ ℂ (Polynomial.aeval (α i).re f) = 0 := by
          rw [← Polynomial.aeval_algebraMap_apply]; exact hC0
        exact (algebraMap ℝ ℂ).injective (h1.trans (map_zero _).symm)
    rw [hset_eq, Set.ncard_coe_finset]
    exact Finset.card_image_of_injOn fun i hi j hj hij => by
      have himi : (α i).im = 0 := (hσ_fix_iff i).mp (Finset.mem_filter.mp hi).2
      have himj : (α j).im = 0 := (hσ_fix_iff j).mp (Finset.mem_filter.mp hj).2
      exact hα_inj (Complex.ext hij (himi.trans himj.symm))
  have hnonreal_card : {z ∈ garlingRootSet ℚ ℂ f | z.im ≠ 0}.ncard =
      (Finset.univ.filter fun i : Fin p => σ i ≠ i).card := by
    let Smove : Finset (Fin p) := Finset.univ.filter fun i => σ i ≠ i
    have hset_eq : {z ∈ garlingRootSet ℚ ℂ f | z.im ≠ 0} = ((Smove.image α) : Set ℂ) := by
      ext z
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_image, Smove, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hz, him⟩
        rw [← hα_range] at hz
        obtain ⟨i, rfl⟩ := hz
        exact ⟨i, fun h => him ((hσ_fix_iff i).mp h), rfl⟩
      · rintro ⟨i, hne, rfl⟩
        exact ⟨(eC i).2, fun h => hne ((hσ_fix_iff i).mpr h)⟩
    rw [hset_eq, Set.ncard_coe_finset]
    exact Finset.card_image_of_injOn fun i _ j _ h => hα_inj h
  -- Relate `Δ` and `δ = garlingDeltaTuple α` via `galois_apply_garlingDeltaTuple`:
  let Δ : ℚ := garlingDiscriminant f
  let δL : L := garlingDeltaTuple (fun i : Fin p => (eL i : L))
  have hδL_val : (δL : ℂ) = garlingDeltaTuple α := map_garlingDeltaTuple L.val.toRingHom _
  have hΔ_eq : (Δ : ℂ) = (δL : ℂ) ^ 2 := by
    have h1 := garlingDiscriminant_eq_discTuple hf0 hexpC
    simpa [Δ, garlingDiscTuple, hδL_val] using h1
  have hΔ_ne0 : Δ ≠ 0 := by
    intro h0
    have hrep := (garlingDiscriminant_eq_zero_iff_hasGarlingRepeatedRoot f hsfL).mp h0
    have hsep_not := (theorem_10_5 hf0 hsfL).1.mp hrep
    obtain ⟨z, hz, hdz⟩ := hsep_not
    have hcop : IsCoprime f (Polynomial.derivative f) := hf_sep
    obtain ⟨u, v, huv⟩ := hcop
    have h0' := congrArg (Polynomial.aeval z) huv
    rw [map_add, map_mul, map_mul, map_one, show Polynomial.aeval z f = 0 from hz,
      show Polynomial.aeval z (Polynomial.derivative f) = 0 from by
        rwa [← garlingDeriv_eq_derivative], mul_zero, mul_zero, add_zero] at h0'
    exact zero_ne_one h0'
  have hδ_ne0 : (δL : ℂ) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by decide)] at hΔ_eq
    exact hΔ_ne0 ((algebraMap ℚ ℂ).injective (hΔ_eq.trans (map_zero _).symm))
  have hconj_δ : complexConjAlgEquiv (δL : ℂ) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (δL : ℂ) := by
    have h1 := congrArg Subtype.val (galois_apply_garlingDeltaTuple eL τ)
    simpa [τ, σ, φ] using h1
  -- Case split on `σ = 1` vs `σ ≠ 1`:
  by_cases hσ1 : σ = 1
  · left
    have hall_real : ∀ z ∈ garlingRootSet ℚ ℂ f, z.im = 0 := by
      intro z hz
      rw [← hα_range] at hz
      obtain ⟨i, rfl⟩ := hz
      exact (hσ_fix_iff i).mp (by rw [hσ1]; rfl)
    have hrc : {x : ℝ | Polynomial.aeval x f = 0}.ncard = p := by
      rw [hreal_card]
      have hfilt : (Finset.univ.filter fun i : Fin p => σ i = i) = Finset.univ := by
        ext i; simp [hσ1]
      rw [hfilt, Finset.card_univ, Fintype.card_fin]
    have hδ_im0 : (δL : ℂ).im = 0 := by
      rw [hσ1, map_one, Units.val_one, Int.cast_one, one_mul] at hconj_δ
      exact (complexConjAlgEquiv_eq_self_iff (δL : ℂ)).mp hconj_δ
    have hΔ_pos : 0 < Δ := by
      have hre_ne0 : (δL : ℂ).re ≠ 0 := fun hre => hδ_ne0 (Complex.ext hre hδ_im0)
      have hΔ_re : (Δ : ℝ) = ((δL : ℂ).re) ^ 2 := by
        have h1 := congrArg Complex.re hΔ_eq
        simp [sq, hδ_im0] at h1
        rw [sq]; exact h1
      have hRpos : (0 : ℝ) < (Δ : ℝ) := by
        rw [hΔ_re]; exact sq_pos_of_ne_zero hre_ne0
      exact_mod_cast hRpos
    exact ⟨hall_real, hrc, hΔ_pos⟩
  · right
    -- By `Exercise 20.2`, `σ ≠ 1` in soluble transitive `φ.range ≤ Σ_p` fixes at most 1 point!
    have hfix_le1 : (Finset.univ.filter fun i : Fin p => σ i = i).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro i hi j hj
      exact (exercise_20_2 hp hG_trans hG_sol).1 σ ⟨τ, rfl⟩ hσ1 i j
        (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    -- By `sign_of_involution`, the non-fixed count is `2s` with `sign σ = (-1)^s`:
    obtain ⟨s, hmove_card, hsign_s⟩ := sign_of_involution σ hσ_inv
    have hpart : (Finset.univ.filter fun i : Fin p => σ i = i).card +
        (Finset.univ.filter fun i : Fin p => σ i ≠ i).card = p := by
      have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin p)))
        (p := fun i => σ i = i)
      simpa [Fintype.card_fin] using h1
    have hp_odd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    have hfix_eq1 : (Finset.univ.filter fun i : Fin p => σ i = i).card = 1 := by omega
    have hs_eq : 2 * s = p - 1 := by omega
    refine ⟨by rw [hreal_card, hfix_eq1], by rw [hnonreal_card, hmove_card, hs_eq], ?_, ?_⟩
    · intro hmod3
      have hs_odd : s % 2 = 1 := by omega
      have hsign_neg1 : ((Equiv.Perm.sign σ : ℤ) : ℂ) = -1 := by
        rw [hsign_s, Int.cast_pow, Int.cast_neg, Int.cast_one]
        exact Odd.neg_one_pow (Nat.odd_iff.mpr hs_odd)
      rw [hsign_neg1, neg_one_mul] at hconj_δ
      have hδ_re0 : (δL : ℂ).re = 0 := by
        have hre := congrArg Complex.re hconj_δ
        rw [complexConjAlgEquiv_re, Complex.neg_re] at hre
        linarith
      have him_ne0 : (δL : ℂ).im ≠ 0 := fun him => hδ_ne0 (Complex.ext hδ_re0 him)
      have hΔ_re : (Δ : ℝ) = -(((δL : ℂ).im) ^ 2) := by
        have h1 := congrArg Complex.re hΔ_eq
        simp [sq, hδ_re0] at h1
        rw [sq]; exact h1
      have hRneg : (Δ : ℝ) < 0 := by
        rw [hΔ_re]; exact neg_lt_zero.mpr (sq_pos_of_ne_zero him_ne0)
      exact_mod_cast hRneg
    · intro hmod1
      have hs_even : s % 2 = 0 := by omega
      have hsign_pos1 : ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
        rw [hsign_s, Int.cast_pow, Int.cast_neg, Int.cast_one]
        exact Even.neg_one_pow (Nat.even_iff.mpr hs_even)
      rw [hsign_pos1, one_mul] at hconj_δ
      have hδ_im0 : (δL : ℂ).im = 0 := (complexConjAlgEquiv_eq_self_iff (δL : ℂ)).mp hconj_δ
      have hre_ne0 : (δL : ℂ).re ≠ 0 := fun hre => hδ_ne0 (Complex.ext hre hδ_im0)
      have hΔ_re : (Δ : ℝ) = ((δL : ℂ).re) ^ 2 := by
        have h1 := congrArg Complex.re hΔ_eq
        simp [sq, hδ_im0] at h1
        rw [sq]; exact h1
      have hRpos : (0 : ℝ) < (Δ : ℝ) := by
        rw [hΔ_re]; exact sq_pos_of_ne_zero hre_ne0
      exact_mod_cast hRpos

/-- **Exercise 20.3, Part 1 (real-root dichotomy, §20.2, printed p. 160 / PDF p. 168):**
If `f ∈ ℚ[x]` is irreducible of odd prime degree `p > 2` and solvable by radicals, then either all
`p` roots of `f` in `ℂ` are real (`{x : ℝ | aeval x f = 0}.ncard = p`) or `f` has exactly one real
root (`{x : ℝ | aeval x f = 0}.ncard = 1`). -/
theorem exercise_20_3_real_roots {p : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p)
    {f : ℚ[X]} (hirr : Irreducible f) (hdeg : f.natDegree = p)
    (hsol : IsGarlingSolvableByRadicals f) :
    ((∀ z ∈ garlingRootSet ℚ ℂ f, z.im = 0) ∧
      {x : ℝ | Polynomial.aeval x f = 0}.ncard = p) ∨
    ({x : ℝ | Polynomial.aeval x f = 0}.ncard = 1 ∧
      {z ∈ garlingRootSet ℚ ℂ f | z.im ≠ 0}.ncard = p - 1) := by
  rcases exercise_20_3_core hp hp2 hirr hdeg hsol with ⟨h1, h2, _⟩ | ⟨h1, h2, _, _⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

/-- **Exercise 20.3, Part 2 (`p = 4k + 3`, §20.2, printed p. 160 / PDF p. 168):**
For `p = 4k + 3` (`p % 4 = 3`), all roots of `f` are real if and only if `garlingDiscriminant f > 0`. -/
theorem exercise_20_3_mod4_eq_3 {p : ℕ} (hp : Nat.Prime p) (hmod : p % 4 = 3)
    {f : ℚ[X]} (hirr : Irreducible f) (hdeg : f.natDegree = p)
    (hsol : IsGarlingSolvableByRadicals f) :
    ((∀ z ∈ garlingRootSet ℚ ℂ f, z.im = 0) ↔ 0 < garlingDiscriminant f) ∧
    ({x : ℝ | Polynomial.aeval x f = 0}.ncard = p ↔ 0 < garlingDiscriminant f) := by
  have hp2 : 2 < p := by omega
  rcases exercise_20_3_core hp hp2 hirr hdeg hsol with ⟨hall, hcard, hpos⟩ | ⟨h1, hnr, hneg, _⟩
  · exact ⟨⟨fun _ => hpos, fun _ => hall⟩, ⟨fun _ => hpos, fun _ => hcard⟩⟩
  · have hlt : garlingDiscriminant f < 0 := hneg hmod
    have hnot_pos : ¬ (0 < garlingDiscriminant f) := not_lt_of_gt hlt
    have hnot_all : ¬ (∀ z ∈ garlingRootSet ℚ ℂ f, z.im = 0) := by
      intro hall
      have hne : {z ∈ garlingRootSet ℚ ℂ f | z.im ≠ 0}.Nonempty :=
        Set.nonempty_of_ncard_ne_zero (by omega)
      obtain ⟨z, hz, him⟩ := hne
      exact him (hall z hz)
    exact ⟨⟨fun h => (hnot_all h).elim, fun h => (hnot_pos h).elim⟩,
      ⟨fun h => by omega, fun h => (hnot_pos h).elim⟩⟩

/-- **Exercise 20.3, Part 3 (`p = 4k + 1`, §20.2, printed p. 160 / PDF p. 168; `QUEUE.md` semi-open
prompt `"What happens if p = 4k + 1?"`):**
Whenever `p = 4k + 1` (`p % 4 = 1`), the discriminant `garlingDiscriminant f` is **strictly positive
in both cases** (whether all `p` roots are real or only `1` root is real), so the sign of `Δ`
provides no information distinguishing all-real from 1-real. (See also `exercise_20_3_p5_square_disc_witness`
in §20.3 below showing that even `∃ r : ℚ, Δ = r^2` holds in both cases at `p = 5`.) -/
theorem exercise_20_3_mod4_eq_1 {p : ℕ} (hp : Nat.Prime p) (hmod : p % 4 = 1)
    {f : ℚ[X]} (hirr : Irreducible f) (hdeg : f.natDegree = p)
    (hsol : IsGarlingSolvableByRadicals f) :
    0 < garlingDiscriminant f := by
  have hp2 : 2 < p := by
    have := hp.two_le; omega
  rcases exercise_20_3_core hp hp2 hirr hdeg hsol with ⟨_, _, hpos⟩ | ⟨_, _, _, hpos⟩
  · exact hpos
  · exact hpos hmod

/-! ### Exercise 20.5 (§20.2, printed p. 161 / PDF p. 169 — `QUEUE.md` positive-characteristic hold) -/

/-- Local copy of Chapter 19's Frobenius reduction for radical towers in prime characteristic `q`:
every radical extension `L : F` (`ringChar F = q`) contains an intermediate field `N` with a
`q`-coprime radical tower (`IsGarlingRadicalExtensionNotCharDvd F N`) containing every `F`-separable
element of `L`. -/
private theorem frobenius_reduction_of_radical_extension_ch20 {F L : Type*} [Field F] [Field L]
    [Algebra F L] {q : ℕ} (hq : Nat.Prime q) (hcharF : ringChar F = q)
    (hrad : IsGarlingExtensionByRadicals F L) :
    ∃ (N : IntermediateField F L) (D : ℕ),
      IsGarlingRadicalExtensionNotCharDvd F N ∧
      (∀ x : L, x ^ (q ^ D) ∈ N) ∧
      (∀ α : L, IsSeparable F α → α ∈ N) := by
  classical
  have _ : Fact q.Prime := ⟨hq⟩
  have _ : CharP F q := hcharF ▸ ringChar.charP F
  have _ : CharP L q := charP_of_injective_algebraMap (algebraMap F L).injective q
  have hcharL : ringChar L = q := ringChar.eq L q
  rcases hrad with ⟨r, T, β, hT0, hTlast, hTstep⟩
  have hex : ∀ i : Fin r, ∃ (e d : ℕ), 1 ≤ d ∧ ¬ (q ∣ d) ∧
      (β i) ^ (q ^ e * d) ∈ T i.castSucc := by
    intro i
    obtain ⟨⟨m, hm1, hpow⟩, _⟩ := hTstep i
    have hm0 : m ≠ 0 := by omega
    let e := padicValNat q m
    let d := m / q ^ e
    have hdvd : q ^ e ∣ m := pow_padicValNat_dvd
    have hmul : q ^ e * d = m := Nat.mul_div_cancel' hdvd
    have hd_pos : 1 ≤ d := by
      have hd0 : d ≠ 0 := fun h => hm0 (by rw [← hmul, h, mul_zero])
      exact Nat.pos_of_ne_zero hd0
    have hqd : ¬ (q ∣ d) := by
      intro hdiv
      rcases hdiv with ⟨c, hc⟩
      have hdvd' : q ^ (e + 1) ∣ m := ⟨c, by rw [← hmul, hc, pow_succ]; ring⟩
      have hle : e + 1 ≤ padicValNat q m := (padicValNat_dvd_iff_le hm0).mp hdvd'
      omega
    exact ⟨e, d, hd_pos, hqd, hmul.symm ▸ hpow⟩
  choose e d hd_pos hqd hβ_pow using hex
  let D : Fin (r + 1) → ℕ := fun k =>
    ∑ i ∈ (Finset.univ : Finset (Fin r)).filter (fun i => i.1 < k.1), e i
  have hD0 : D 0 = 0 := by simp [D]
  have hDsucc : ∀ i : Fin r, D i.succ = D i.castSucc + e i := by
    intro i
    unfold D
    have hset : (Finset.univ : Finset (Fin r)).filter (fun j => j.1 < i.succ.1) =
        insert i ((Finset.univ : Finset (Fin r)).filter (fun j => j.1 < i.castSucc.1)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.val_succ, Fin.val_castSucc]
      constructor
      · intro hj
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr h
      · rintro (rfl | hj) <;> omega
    rw [hset, Finset.sum_insert (by simp)]
    ring
  let η : Fin r → L := fun i => (β i) ^ (q ^ D i.succ)
  let N : Fin (r + 1) → IntermediateField F L := fun k =>
    IntermediateField.adjoin F (η '' {i : Fin r | i.1 < k.1})
  have hN0 : N 0 = ⊥ := by
    have hempty : η '' {i : Fin r | i.1 < (0 : Fin (r + 1)).1} = ∅ := by ext x; simp
    rw [show N 0 = IntermediateField.adjoin F (η '' {i : Fin r | i.1 < (0 : Fin (r + 1)).1}) from rfl,
      hempty, IntermediateField.adjoin_empty]
  have hNsucc : ∀ i : Fin r,
      N i.succ = IntermediateField.adjoin F ((N i.castSucc : Set L) ∪ {η i}) := by
    intro i
    have hset : η '' {j : Fin r | j.1 < i.succ.1} =
        insert (η i) (η '' {j : Fin r | j.1 < i.castSucc.1}) := by
      ext x
      simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Fin.val_succ, Fin.val_castSucc]
      constructor
      · rintro ⟨j, hj, rfl⟩
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with h | h
        · exact Or.inl (congrArg η (Fin.ext h))
        · exact Or.inr ⟨j, h, rfl⟩
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · exact ⟨i, Nat.lt_succ_self _, rfl⟩
        · exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
    apply le_antisymm
    · rw [show N i.succ = IntermediateField.adjoin F (η '' {j : Fin r | j.1 < i.succ.1}) from rfl,
        hset, IntermediateField.adjoin_le_iff]
      rintro x (rfl | ⟨j, hj, rfl⟩)
      · exact IntermediateField.subset_adjoin F _ (Or.inr rfl)
      · exact IntermediateField.subset_adjoin F _
          (Or.inl (IntermediateField.subset_adjoin F _ ⟨j, hj, rfl⟩))
    · rw [IntermediateField.adjoin_le_iff]
      rintro x (hx | rfl)
      · exact IntermediateField.adjoin.mono F _ _ (by rw [hset]; exact Set.subset_insert _ _) hx
      · exact IntermediateField.subset_adjoin F _ ⟨i, Nat.lt_succ_self _, rfl⟩
  have h_frob_mem : ∀ (k : ℕ) (hk : k ≤ r) (x : L),
      x ∈ T ⟨k, Nat.lt_succ_of_le hk⟩ →
      x ^ (q ^ D ⟨k, Nat.lt_succ_of_le hk⟩) ∈ N ⟨k, Nat.lt_succ_of_le hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk x hx
      have hx0 : x ∈ T 0 := hx
      rw [hT0] at hx0
      rcases IntermediateField.mem_bot.mp hx0 with ⟨c, rfl⟩
      rw [show (⟨0, Nat.lt_succ_of_le hk⟩ : Fin (r + 1)) = 0 from rfl, hD0, pow_zero, pow_one, hN0]
      exact (⊥ : IntermediateField F L).algebraMap_mem c
    | succ k ih =>
      intro hk x hx
      let i : Fin r := ⟨k, hk⟩
      let E_frob : IntermediateField F L :=
        { carrier := {y : L | y ^ (q ^ D i.succ) ∈ N i.succ}
          add_mem' := fun {a b} ha hb => by
            change (a + b) ^ (q ^ D i.succ) ∈ N i.succ
            rw [add_pow_char_pow]; exact (N i.succ).add_mem ha hb
          zero_mem' := by
            change (0 : L) ^ (q ^ D i.succ) ∈ N i.succ
            rw [zero_pow (pow_ne_zero _ hq.ne_zero)]; exact (N i.succ).zero_mem
          mul_mem' := fun {a b} ha hb => by
            change (a * b) ^ (q ^ D i.succ) ∈ N i.succ
            rw [mul_pow]; exact (N i.succ).mul_mem ha hb
          one_mem' := by
            change (1 : L) ^ (q ^ D i.succ) ∈ N i.succ
            rw [one_pow]; exact (N i.succ).one_mem
          inv_mem' := fun {a} ha => by
            change a⁻¹ ^ (q ^ D i.succ) ∈ N i.succ
            rw [inv_pow]; exact (N i.succ).inv_mem ha
          algebraMap_mem' := fun c => by
            change (algebraMap F L c) ^ (q ^ D i.succ) ∈ N i.succ
            rw [← map_pow]; exact (N i.succ).algebraMap_mem _ }
      have hTi_le : T i.succ ≤ E_frob := by
        rw [(hTstep i).2, IntermediateField.adjoin_le_iff]
        rintro y (hy | rfl)
        · change y ^ (q ^ D i.succ) ∈ N i.succ
          rw [hDsucc i, pow_add, pow_mul]
          have hy' := ih (Nat.le_of_lt hk) y hy
          have hN_le : N i.castSucc ≤ N i.succ := by
            rw [hNsucc i]; exact fun z hz => IntermediateField.subset_adjoin F _ (Or.inl hz)
          exact pow_mem (hN_le hy') (q ^ e i)
        · change (β i) ^ (q ^ D i.succ) ∈ N i.succ
          exact IntermediateField.subset_adjoin F _ ⟨i, Nat.lt_succ_self _, rfl⟩
      exact hTi_le hx
  have hη_pow : ∀ i : Fin r, (η i) ^ (d i) ∈ N i.castSucc := by
    intro i
    change ((β i) ^ (q ^ D i.succ)) ^ (d i) ∈ N i.castSucc
    have heq : ((β i) ^ (q ^ D i.succ)) ^ (d i) =
        ((β i) ^ (q ^ e i * d i)) ^ (q ^ D i.castSucc) := by
      rw [← pow_mul, ← pow_mul, hDsucc i, pow_add]; congr 1; ring
    rw [heq]
    exact h_frob_mem i.1 (Nat.le_of_lt i.2) _ (hβ_pow i)
  let Ntop : IntermediateField F L := N (Fin.last r)
  have hN_le_top : ∀ j : Fin (r + 1), N j ≤ Ntop := fun j =>
    IntermediateField.adjoin.mono F _ _ (Set.image_mono fun i hi => lt_of_lt_of_le hi (Nat.le_of_lt_succ j.2))
  let NT : Fin (r + 1) → IntermediateField F Ntop := fun j =>
    { carrier := {x : Ntop | x.1 ∈ N j}
      add_mem' := fun {a b} ha hb => (N j).add_mem ha hb
      zero_mem' := (N j).zero_mem
      mul_mem' := fun {a b} ha hb => (N j).mul_mem ha hb
      one_mem' := (N j).one_mem
      inv_mem' := fun {a} ha => (N j).inv_mem ha
      algebraMap_mem' := fun c => (N j).algebraMap_mem c }
  let η' : Fin r → Ntop := fun i => ⟨η i, IntermediateField.subset_adjoin F _ ⟨i, i.2, rfl⟩⟩
  have hchar_prod : ¬ (ringChar F ∣ ∏ i : Fin r, d i) := by
    rw [hcharF]
    intro hdiv
    obtain ⟨i, _, hi⟩ := (hq.prime.dvd_finsetProd_iff d).mp hdiv
    exact hqd i hi
  have hrad_Ntop : IsGarlingRadicalExtensionNotCharDvd F Ntop := by
    refine ⟨r, NT, η', d, ?_, ?_, hchar_prod, fun i => ?_⟩
    · ext ⟨x, hx⟩
      change x ∈ N 0 ↔ (⟨x, hx⟩ : Ntop) ∈ (⊥ : IntermediateField F Ntop)
      rw [hN0, IntermediateField.mem_bot, IntermediateField.mem_bot]
      constructor
      · rintro ⟨c, hc⟩; exact ⟨c, Subtype.ext hc⟩
      · rintro ⟨c, hc⟩; exact ⟨c, congrArg Subtype.val hc⟩
    · ext ⟨x, hx⟩; change x ∈ Ntop ↔ True; simp [hx]
    · refine ⟨by change (η i) ^ (d i) ∈ N i.castSucc; exact hη_pow i, ?_⟩
      apply le_antisymm
      · intro ⟨x, hx⟩ hxi
        have hmem : x ∈ IntermediateField.adjoin F ((N i.castSucc : Set L) ∪ {η i}) := by
          rw [← hNsucc i]; exact hxi
        let M : IntermediateField F L :=
          (IntermediateField.adjoin F ((NT i.castSucc : Set Ntop) ∪ {η' i})).map Ntop.val
        have hsub : IntermediateField.adjoin F ((N i.castSucc : Set L) ∪ {η i}) ≤ M := by
          rw [IntermediateField.adjoin_le_iff]
          rintro y (hy | rfl)
          · exact ⟨⟨y, hN_le_top i.castSucc hy⟩, IntermediateField.subset_adjoin F _ (Or.inl hy), rfl⟩
          · exact ⟨η' i, IntermediateField.subset_adjoin F _ (Or.inr rfl), rfl⟩
        obtain ⟨z, hz, hzx⟩ := hsub hmem
        exact (Subtype.ext hzx : z = ⟨x, hx⟩) ▸ hz
      · rw [IntermediateField.adjoin_le_iff]
        rintro ⟨y, hy⟩ (hyi | hyi)
        · change y ∈ N i.succ; rw [hNsucc i]; exact IntermediateField.subset_adjoin F _ (Or.inl hyi)
        · rw [Set.mem_singleton_iff] at hyi
          have hyeq : y = η i := congrArg Subtype.val hyi
          change y ∈ N i.succ
          rw [hyeq, hNsucc i]
          exact IntermediateField.subset_adjoin F _ (Or.inr rfl)
  have hall_pow : ∀ x : L, x ^ (q ^ D (Fin.last r)) ∈ Ntop := fun x =>
    h_frob_mem r le_rfl x (by rw [show (⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1)) = Fin.last r from rfl, hTlast]; trivial)
  have hsep_mem : ∀ α : L, IsSeparable F α → α ∈ Ntop := by
    intro α hα_sep
    have hα_int : IsIntegral Ntop α := (hα_sep.isIntegral).tower_top
    have hα_sep_N : (minpoly Ntop α).Separable := by
      have hm_dvd : minpoly Ntop α ∣ (minpoly F α).map (algebraMap F Ntop) :=
        minpoly.dvd Ntop α (by rw [Polynomial.aeval_def, Polynomial.eval₂_map]; exact minpoly.aeval F α)
      exact ((Polynomial.separable_map (algebraMap F Ntop)).mpr hα_sep).of_dvd hm_dvd
    let c : Ntop := ⟨α ^ (q ^ D (Fin.last r)), hall_pow α⟩
    have hm_dvd_p : minpoly Ntop α ∣ Polynomial.X ^ (q ^ D (Fin.last r)) - Polynomial.C c :=
      minpoly.dvd Ntop α (by simp [c])
    have hfactor : (Polynomial.X ^ (q ^ D (Fin.last r)) - Polynomial.C c).map (algebraMap Ntop L) =
        (Polynomial.X - Polynomial.C α) ^ (q ^ D (Fin.last r)) := by
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        sub_pow_char_pow, ← map_pow]; rfl
    have hm_map_dvd : (minpoly Ntop α).map (algebraMap Ntop L) ∣
        (Polynomial.X - Polynomial.C α) ^ (q ^ D (Fin.last r)) := by
      rw [← hfactor]; exact Polynomial.map_dvd (algebraMap Ntop L) hm_dvd_p
    have hm_deg1 : (minpoly Ntop α).natDegree = 1 := by
      let mL : L[X] := (minpoly Ntop α).map (algebraMap Ntop L)
      have hm_sep_L : mL.Separable := (Polynomial.separable_map (algebraMap Ntop L)).mpr hα_sep_N
      have hmL_ne0 : mL ≠ 0 := ((minpoly.monic hα_int).map (algebraMap Ntop L)).ne_zero
      have hspl_mL : mL.Splits :=
        (Polynomial.Splits.pow (Polynomial.Splits.X_sub_C α) _).of_dvd
          (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero α)) hm_map_dvd
      have hroots_sub : ∀ x ∈ mL.roots, x = α := by
        intro x hx
        have hzero : mL.eval x = 0 := (Polynomial.mem_roots hmL_ne0).mp hx
        rcases hm_map_dvd with ⟨g, hg⟩
        have hpow0 : (x - α) ^ (q ^ D (Fin.last r)) = 0 := by
          have := congrArg (Polynomial.eval x) hg
          rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
            Polynomial.eval_mul, hzero, zero_mul] at this
          exact this
        exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpow0)
      have hcard_le1 : mL.roots.card ≤ 1 := by
        have hsub : mL.roots.toFinset ⊆ ({α} : Finset L) := fun x hx =>
          Finset.mem_singleton.mpr (hroots_sub x (Multiset.mem_toFinset.mp hx))
        calc mL.roots.card = mL.roots.toFinset.card :=
              (Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hm_sep_L)).symm
          _ ≤ ({α} : Finset L).card := Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton α
      have hdeg_eq : mL.natDegree = mL.roots.card := (Polynomial.splits_iff_card_roots.mp hspl_mL).symm
      have hle1 : (minpoly Ntop α).natDegree ≤ 1 := by
        rw [← Polynomial.natDegree_map_eq_of_injective (algebraMap Ntop L).injective]
        change mL.natDegree ≤ 1; omega
      have hpos := minpoly.natDegree_pos hα_int
      omega
    have hm_mon : (minpoly Ntop α).Monic := minpoly.monic hα_int
    have hm_eval : Polynomial.aeval α (minpoly Ntop α) = 0 := minpoly.aeval Ntop α
    have hm_eq : minpoly Ntop α = Polynomial.X + Polynomial.C ((minpoly Ntop α).coeff 0) := by
      apply Polynomial.ext; intro k
      rcases k with _ | _ | k
      · simp
      · change (minpoly Ntop α).coeff 1 = (Polynomial.X + Polynomial.C ((minpoly Ntop α).coeff 0)).coeff 1
        rw [Polynomial.coeff_add, Polynomial.coeff_X_one, Polynomial.coeff_C_succ, add_zero,
          ← hm_deg1, hm_mon.coeff_natDegree]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp [Polynomial.coeff_X]
    rw [hm_eq, map_add, Polynomial.aeval_X, Polynomial.aeval_C] at hm_eval
    have hα_eq : α = algebraMap Ntop L (-((minpoly Ntop α).coeff 0)) := by
      rw [map_neg]; exact eq_neg_of_add_eq_zero_left hm_eval
    rw [hα_eq]
    exact (-((minpoly Ntop α).coeff 0)).2
  exact ⟨Ntop, D (Fin.last r), hrad_Ntop, hall_pow, hsep_mem⟩

/-- Local copy of Chapter 19's Helper Lemma B: over an algebraically closed subfield `Kbar ≤ F`
of prime characteristic `q`, every `q`-coprime radical extension `N : F` has `q ∤ [N : F]`. -/
private theorem not_char_dvd_finrank_of_radical_over_algClosed_ch20 {Kbar : Type u} {F : Type v}
    {N : Type w} [Field Kbar] [Field F] [Field N] [Algebra Kbar F] [Algebra F N] [Algebra Kbar N]
    [IsScalarTower Kbar F N] [IsAlgClosed Kbar]
    {q : ℕ} (hq : Nat.Prime q) (hcharF : ringChar F = q)
    (hrad : IsGarlingRadicalExtensionNotCharDvd F N) :
    ¬ (q ∣ Module.finrank F N) := by
  classical
  have _ : CharP F q := hcharF ▸ ringChar.charP F
  have _ : CharP Kbar q := ⟨fun n => by
    rw [← (algebraMap Kbar F).injective.eq_iff, map_natCast, map_zero, CharP.cast_eq_zero_iff F q]⟩
  have hcharKbar : ringChar Kbar = q := ringChar.eq Kbar q
  have hstep_dvd : ∀ {A B : Type w} [Field A] [Field B] [Algebra Kbar A] [Algebra A B]
      {d : ℕ} {η : B}, 1 ≤ d → ¬ (q ∣ d) →
      (∃ c : A, η ^ d = algebraMap A B c) →
      IntermediateField.adjoin A ({η} : Set B) = ⊤ →
      Module.finrank A B ∣ d := by
    intro A B _ _ _ _ d η hd1 hqd ⟨c, hηd⟩ hadj
    by_cases hη0 : η = 0
    · have hbot : (⊥ : IntermediateField A B) = ⊤ := by
        rw [← hadj]; apply le_antisymm bot_le
        rw [IntermediateField.adjoin_le_iff]; rintro _ rfl
        rw [hη0]; exact (⊥ : IntermediateField A B).zero_mem
      have h1 : Module.finrank A B = 1 := by
        rw [← LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv, ← hbot,
          IntermediateField.finrank_bot]
      rw [h1]; exact one_dvd d
    · have hc0 : c ≠ 0 := fun h0 => hη0 (eq_zero_of_pow_eq_zero (by rw [hηd, h0, map_zero]))
      have hcharK_d : ¬ (ringChar Kbar ∣ d) := by rwa [hcharKbar]
      have hsf_Kbar : IsGarlingSplittingFieldExtension Kbar Kbar (Polynomial.X ^ d - Polynomial.C (1 : Kbar)) :=
        (isGarlingSplittingFieldExtension_iff Kbar Kbar _).mpr ⟨IsAlgClosed.splits _, Subsingleton.elim _ _⟩
      obtain ⟨_, ⟨ωK, hωK⟩, _⟩ :=
        Garling.Chapter16.theorem_16_1 (one_ne_zero : (1 : Kbar) ≠ 0) hcharK_d hsf_Kbar
      let ωA : A := algebraMap Kbar A ωK
      have hωA : IsPrimitiveRoot ωA d := hωK.map_of_injective (algebraMap Kbar A).injective
      let ωB : B := algebraMap A B ωA
      have hωB : IsPrimitiveRoot ωB d := hωA.map_of_injective (algebraMap A B).injective
      have hfac : (Polynomial.X ^ d - Polynomial.C c).map (algebraMap A B) =
          ∏ j : Fin d, (Polynomial.X - Polynomial.C (ωB ^ (j : ℕ) * η)) := by
        rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, ← hηd]
        exact Garling.Chapter16.X_pow_sub_C_pow_eq_prod hd1 hωB η
      have hspl_B : ((Polynomial.X ^ d - Polynomial.C c).map (algebraMap A B)).Splits := by
        rw [hfac]; exact Polynomial.Splits.prod fun _ _ => Polynomial.Splits.X_sub_C _
      have hη_root : η ∈ (Polynomial.X ^ d - Polynomial.C c).rootSet B := by
        rw [Polynomial.mem_rootSet]
        exact ⟨(Polynomial.monic_X_pow_sub_C c (by omega)).ne_zero, by simp [hηd]⟩
      have hint_η : IsIntegral A η :=
        ⟨Polynomial.X ^ d - Polynomial.C c, Polynomial.monic_X_pow_sub_C c (by omega),
          (Polynomial.mem_rootSet.mp hη_root).2⟩
      have hsf_B : IsGarlingSplittingFieldExtension A B (Polynomial.X ^ d - Polynomial.C c) := by
        rw [isGarlingSplittingFieldExtension_iff]
        refine ⟨hspl_B, ?_⟩
        have hAlg : Algebra.adjoin A ({η} : Set B) = ⊤ := by
          rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint_η.isAlgebraic, hadj]; rfl
        exact eq_top_iff.mpr (hAlg ▸ Algebra.adjoin_mono (Set.singleton_subset_iff.mpr hη_root))
      have hcharA : ¬ (ringChar A ∣ d) := by
        have _ : CharP A q := charP_of_injective_algebraMap (algebraMap Kbar A).injective q
        rw [ringChar.eq A q]; exact hqd
      have hpoly_sep : IsGarlingSeparablePoly (Polynomial.X ^ d - Polynomial.C c : A[X]) :=
        (Garling.Chapter16.X_pow_sub_C_separable_of_ne_zero hc0 hcharA).2.2.2.2
      have hgal_B : IsGarlingGaloisExtension A B :=
        Garling.Chapter16.isGarlingGalois_of_splittingField
          (Polynomial.monic_X_pow_sub_C c (by omega)).ne_zero hsf_B hpoly_sep
      have h161 := (Garling.Chapter16.theorem_16_1 hc0 hcharA hsf_B).2.2 ωB hωB
      have hAω_eq_bot : (A⟮ωB⟯ : IntermediateField A B) = ⊥ := by
        apply le_antisymm _ bot_le
        rw [IntermediateField.adjoin_le_iff]; rintro _ rfl; exact ⟨ωA, rfl⟩
      have hfin_eq : Module.finrank A B = Nat.card (B ≃ₐ[A] B) :=
        ((theorem_10_4_algEquiv (K := A) (L := B) hgal_B.1).1 hgal_B).symm
      let eGal : (B ≃ₐ[A] B) ≃* (B ≃ₐ[A⟮ωB⟯] B) :=
        { toFun := fun σ =>
            { σ.toRingEquiv with
              commutes' := fun ⟨y, hy⟩ => by
                rw [hAω_eq_bot, IntermediateField.mem_bot] at hy
                rcases hy with ⟨a, rfl⟩; exact σ.commutes a }
          invFun := fun σ =>
            { σ.toRingEquiv with
              commutes' := fun a => σ.commutes ⟨algebraMap A B a, (A⟮ωB⟯).algebraMap_mem a⟩ }
          left_inv := fun _ => by ext x; rfl
          right_inv := fun _ => by ext x; rfl
          map_mul' := fun _ _ => by ext x; rfl }
      rw [hfin_eq, Nat.card_congr eGal.toEquiv]
      exact h161.2.2.1
  rcases hrad with ⟨r, T, η, d, hT0, hTlast, hchar_prod, hTstep⟩
  have hchar_d : ∀ i : Fin r, 1 ≤ d i ∧ ¬ (q ∣ d i) := by
    intro i
    have hi : ¬ (ringChar F ∣ d i) := (not_ringChar_dvd_prod_iff F d).mp hchar_prod i
    rw [hcharF] at hi
    refine ⟨?_, hi⟩
    by_contra h0; have hd0 : d i = 0 := by omega
    rw [hd0] at hi; exact hi (dvd_zero q)
  have hind : ∀ (k : ℕ) (hk : k ≤ r), ¬ (q ∣ Module.finrank F (T ⟨k, Nat.lt_succ_of_le hk⟩)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      rw [show (⟨0, Nat.lt_succ_of_le hk⟩ : Fin (r + 1)) = 0 from rfl, hT0, IntermediateField.finrank_bot]
      exact hq.not_dvd_one
    | succ k ih =>
      intro hk
      let i : Fin r := ⟨k, hk⟩
      have hle : T i.castSucc ≤ T i.succ := by
        rw [(hTstep i).2]; exact fun z hz => IntermediateField.subset_adjoin F _ (Or.inl hz)
      let _ : Algebra (T i.castSucc) (T i.succ) := (IntermediateField.inclusion hle).toAlgebra
      have _ : IsScalarTower F (T i.castSucc) (T i.succ) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      let _ : Algebra Kbar (T i.castSucc) :=
        RingHom.toAlgebra ((algebraMap F (T i.castSucc)).comp (algebraMap Kbar F))
      let ηi : T i.succ := ⟨η i, by rw [(hTstep i).2]; exact IntermediateField.subset_adjoin F _ (Or.inr rfl)⟩
      have hη_pow : ∃ c : T i.castSucc, ηi ^ (d i) = algebraMap (T i.castSucc) (T i.succ) c :=
        ⟨⟨(η i) ^ (d i), (hTstep i).1⟩, Subtype.ext rfl⟩
      have hadj_step : IntermediateField.adjoin (T i.castSucc) ({ηi} : Set (T i.succ)) = ⊤ := by
        rw [eq_top_iff]; intro ⟨x, hx⟩ _
        have hx' : x ∈ IntermediateField.adjoin F ((T i.castSucc : Set N) ∪ {η i}) := by
          rw [← (hTstep i).2]; exact hx
        let M : IntermediateField F N :=
          ((IntermediateField.adjoin (T i.castSucc) ({ηi} : Set (T i.succ))).restrictScalars F).map (T i.succ).val
        have hsub : IntermediateField.adjoin F ((T i.castSucc : Set N) ∪ {η i}) ≤ M := by
          rw [IntermediateField.adjoin_le_iff]; rintro y (hy | rfl)
          · exact ⟨⟨y, hle hy⟩, (IntermediateField.adjoin (T i.castSucc) _).algebraMap_mem ⟨y, hy⟩, rfl⟩
          · exact ⟨ηi, IntermediateField.subset_adjoin (T i.castSucc) _ rfl, rfl⟩
        obtain ⟨z, hz, hzx⟩ := hsub hx'
        exact (Subtype.ext hzx : z = ⟨x, hx⟩) ▸ hz
      have hdvd_step : Module.finrank (T i.castSucc) (T i.succ) ∣ d i :=
        hstep_dvd (A := T i.castSucc) (B := T i.succ) (hchar_d i).1 (hchar_d i).2 hη_pow hadj_step
      have hq_step : ¬ (q ∣ Module.finrank (T i.castSucc) (T i.succ)) :=
        fun hdiv => (hchar_d i).2 (hdiv.trans hdvd_step)
      have hfin_FN : IsFiniteExtension F N :=
        isFiniteExtension_of_isGarlingExtensionByRadicals
          (isGarlingExtensionByRadicals_of_notCharDvd ⟨r, T, η, d, hT0, hTlast, hchar_prod, hTstep⟩)
      have _ : Module.Finite F N := (isFiniteExtension_iff_moduleFinite F N).mp hfin_FN
      have _ : Module.Finite F (T i.succ) := inferInstance
      have _ : Module.Finite F (T i.castSucc) := inferInstance
      have _ : Module.Finite (T i.castSucc) (T i.succ) := Module.Finite.right F (T i.castSucc) (T i.succ)
      have htower := Module.finrank_mul_finrank F (T i.castSucc) (T i.succ)
      change ¬ (q ∣ Module.finrank F (T i.succ))
      rw [← htower]
      exact fun hdiv => (hq.dvd_mul.mp hdiv).elim (ih (Nat.le_of_lt hk)) hq_step
  have htop := hind r le_rfl
  rw [show (⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1)) = Fin.last r from rfl, hTlast] at htop
  rwa [LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv] at htop

/-- Helper: every irreducible polynomial `f ∈ K[X]` of prime degree `p ≠ ringChar K` is separable. -/
private theorem separable_of_irreducible_prime_deg_ne_char {K : Type u} [Field K]
    {p : ℕ} (hp : Nat.Prime p) (hchar : ringChar K ≠ p)
    {f : K[X]} (hirr : Irreducible f) (hdeg : f.natDegree = p) :
    f.Separable ∧ IsGarlingSeparablePoly f := by
  have hgsep : IsGarlingSeparablePoly f := by
    by_contra hnot
    obtain ⟨q, hchar_q, hq_pos, n, a, hf_eq⟩ := (theorem_10_6 hirr).mp hnot
    have hq_prime : Nat.Prime q := by
      rcases CharP.char_is_prime_or_zero K (ringChar K) with hqp | h0
      · rwa [hchar_q] at hqp
      · omega
    have hcp : f.coeff p ≠ 0 := by
      rw [← hdeg, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero
    rw [hf_eq, Polynomial.finsetSum_coeff] at hcp
    obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcp
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at hi
    split_ifs at hi with hpi
    · have hq_dvd_p : q ∣ p := ⟨i, hpi.trans (mul_comm _ _)⟩
      rcases hp.eq_one_or_self_of_dvd q hq_dvd_p with h1 | hqp
      · exact hq_prime.ne_one h1
      · exact hchar (hchar_q.trans hqp)
    · simp at hi
  have hsep : f.Separable :=
    (mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly f).mpr
      ⟨hirr.ne_zero, hirr.squarefree, hgsep⟩
  exact ⟨hsep, hgsep⟩

/-- **Exercise 20.5, Unconditional Galois-Group Characterization (§20.2, printed p. 161 / PDF p. 169):**
For **every** field `K` (arbitrary characteristic `≠ p`) and every irreducible `f ∈ K[X]` of prime
degree `p ≠ char K` with splitting field `L : K`:
`IsGarlingSoluble (GarlingPolyGaloisGroup K L f) ↔ ∀ α β ∈ garlingRootSet K L f, α ≠ β → K(α, β) = L`.
Proved unconditionally via `Exercise 20.2`, `Exercise 20.4`, and the Fundamental Theorem of Galois Theory. -/
theorem exercise_20_5_galois_iff {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {p : ℕ} (hp : Nat.Prime p) (hchar : ringChar K ≠ p)
    {f : K[X]} (hirr : Irreducible f) (hdeg : f.natDegree = p)
    (hsf : IsGarlingSplittingFieldExtension K L f) :
    IsGarlingSoluble (GarlingPolyGaloisGroup K L f) ↔
      ∀ α ∈ garlingRootSet K L f, ∀ β ∈ garlingRootSet K L f, α ≠ β →
        IntermediateField.adjoin K ({α, β} : Set L) = ⊤ := by
  classical
  obtain ⟨hf_sep, hf_gsep⟩ := separable_of_irreducible_prime_deg_ne_char hp hchar hirr hdeg
  have hf0 : f ≠ 0 := hirr.ne_zero
  have hsf_m : f.IsSplittingField K L := (isGarlingSplittingFieldExtension_iff K L f).mp hsf
  have _ : FiniteDimensional K L := Polynomial.IsSplittingField.finiteDimensional L f
  have hgal : IsGarlingGaloisExtension K L :=
    Garling.Chapter16.isGarlingGalois_of_splittingField hf0 hsf hf_gsep
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  have hcard_roots : (garlingRootSet K L f).ncard = p := by
    rw [garlingRootSet_eq_rootSet hf0]
    have hset : f.rootSet L = ((f.map (algebraMap K L)).roots.toFinset : Set L) := by
      ext x
      simp [Polynomial.mem_rootSet_of_ne hf0,
        Polynomial.mem_roots ((Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf0),
        Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    rw [hset, Set.ncard_coe_finset,
      Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hf_sep.map),
      Polynomial.splits_iff_card_roots.mp hsf_m.splits,
      Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective, hdeg]
  have _ : Finite (garlingRootSet K L f) := Set.finite_of_ncard_pos (by rw [hcard_roots]; exact hp.pos)
  let eR : Fin p ≃ garlingRootSet K L f :=
    (Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, hcard_roots])).symm
  let φ := garlingRootLabellingPermHom eR
  have hφ_inj : Function.Injective φ := fun σ₁ σ₂ h => by
    apply theorem_11_6 hsf
    ext ⟨r, hr⟩
    have h1 := Equiv.congr_fun h (eR.symm ⟨r, hr⟩)
    have h2 := congrArg (fun x : Fin p => (eR x : L)) h1
    simpa [φ] using h2
  have hG_trans : SubgroupActsTransitively φ.range := by
    intro i j
    obtain ⟨σ, hσ⟩ := corollary_2_to_theorem_7_5_algEquiv hirr hsf (eR i).2 (eR j).2
    refine ⟨φ σ, ⟨σ, rfl⟩, eR.injective (Subtype.ext ?_)⟩
    simpa [φ] using hσ
  let eG : GarlingPolyGaloisGroup K L f ≃* φ.range :=
    MulEquiv.ofBijective φ.rangeRestrict
      ⟨fun a b hab => hφ_inj (congrArg Subtype.val hab), φ.rangeRestrict_surjective⟩
  constructor
  · intro hsol α hα β hβ hαβ
    have hG_sol : IsGarlingSoluble φ.range := (isGarlingSoluble_congr eG).mp hsol
    let M : IntermediateField K L := IntermediateField.adjoin K ({α, β} : Set L)
    -- Show `M.fixingSubgroup = ⊥`, hence `M = ⊤` by FTGT (`IsGalois.intermediateFieldEquivSubgroup`):
    have hfix_bot : M.fixingSubgroup = ⊥ := by
      rw [eq_bot_iff]
      intro σ hσ
      rw [Subgroup.mem_bot]
      have hσα : σ α = α := hσ ⟨α, IntermediateField.subset_adjoin K _ (by simp)⟩
      have hσβ : σ β = β := hσ ⟨β, IntermediateField.subset_adjoin K _ (by simp)⟩
      let i : Fin p := eR.symm ⟨α, hα⟩
      let j : Fin p := eR.symm ⟨β, hβ⟩
      have hij : i ≠ j := fun h => hαβ (by
        have := congrArg (fun k => (eR k : L)) h; simpa [i, j] using this)
      have hfi : φ σ i = i := eR.injective (Subtype.ext (by
        rw [garlingRootLabellingPermHom_apply]; simpa [i] using hσα))
      have hfj : φ σ j = j := eR.injective (Subtype.ext (by
        rw [garlingRootLabellingPermHom_apply]; simpa [j] using hσβ))
      by_contra hσ1
      have hφ1 : φ σ ≠ 1 := fun h => hσ1 (hφ_inj (h.trans (map_one φ).symm))
      exact hij ((exercise_20_2 hp hG_trans hG_sol).1 (φ σ) ⟨σ, rfl⟩ hφ1 i j hfi hfj)
    have htop := (IsGalois.intermediateFieldEquivSubgroup (F := K) (E := L)).injective
      (show M.fixingSubgroup = (⊤ : IntermediateField K L).fixingSubgroup by
        rw [hfix_bot, IntermediateField.fixingSubgroup_top])
    exact htop
  · intro hgen
    -- No non-identity element of `φ.range` fixes two distinct points:
    have hno_fix2 : ∀ g ∈ φ.range, g ≠ 1 → ∀ i j : Fin p, i ≠ j → g i = i → g j ≠ j := by
      rintro _ ⟨σ, rfl⟩ hσ1 i j hij hfi hfj
      have hσα : σ (eR i : L) = (eR i : L) := by
        rw [← garlingRootLabellingPermHom_apply eR σ i, hfi]
      have hσβ : σ (eR j : L) = (eR j : L) := by
        rw [← garlingRootLabellingPermHom_apply eR σ j, hfj]
      have hαβ : (eR i : L) ≠ (eR j : L) := fun h => hij (eR.injective (Subtype.ext h))
      have htop := hgen (eR i : L) (eR i).2 (eR j : L) (eR j).2 hαβ
      have hfix_all : ∀ x : L, σ x = x := by
        intro x
        have hzpow_fix : ∀ (y : L), σ y = y → ∀ m : ℤ, (σ ^ m) y = y := by
          intro y hy m
          have hnat : ∀ n : ℕ, (σ ^ n) y = y := fun n => by
            induction n with
            | zero => rfl
            | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hy]
          cases m with
          | ofNat n => exact hnat n
          | negSucc n =>
            rw [zpow_negSucc]
            apply (σ ^ (n + 1)).injective
            rw [show (σ ^ (n + 1)) (((σ ^ (n + 1))⁻¹) y) = y from (σ ^ (n + 1)).apply_symm_apply y,
              hnat (n + 1)]
        let FixF : IntermediateField K L := IntermediateField.fixedField (Subgroup.zpowers σ)
        have hle : IntermediateField.adjoin K ({(eR i : L), (eR j : L)} : Set L) ≤ FixF := by
          rw [IntermediateField.adjoin_le_iff]
          rintro _ (rfl | rfl)
          · intro ⟨τ, hτ⟩
            obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
            exact hzpow_fix _ hσα m
          · intro ⟨τ, hτ⟩
            obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
            exact hzpow_fix _ hσβ m
        rw [htop] at hle
        exact hle IntermediateField.mem_top ⟨σ, Subgroup.mem_zpowers σ⟩
      have hσ_eq1 : σ = 1 := AlgEquiv.ext hfix_all
      exact hσ1 (by rw [hσ_eq1, map_one])
    -- Apply `Exercise 20.4`!
    obtain ⟨⟨q, hcard, hndvd⟩, hpart2, hpart3⟩ := exercise_20_4.{0}.2 hp hG_trans
    obtain ⟨K₁, hK₁⟩ := exercise_20_4.{0}.1 hp hndvd hcard
    have huniq : ∀ K₂ : Subgroup φ.range, Nat.card K₂ = p → K₂ = K₁ := by
      intro K₂ hK₂
      by_contra hne
      obtain ⟨⟨g, hg, hg1, i, j, hij, hgi, hgj⟩, _⟩ := hpart2 ⟨K₂, K₁, hK₂, hK₁, hne⟩
      exact hno_fix2 g hg hg1 i j hij hgi hgj
    have hG_sol : IsGarlingSoluble φ.range := (hpart3 K₁ hK₁ huniq).2
    exact (isGarlingSoluble_congr eG).mpr hG_sol

/-- **Exercise 20.5, Unconditional Forward Direction (`⇒`, §20.2, printed p. 161 / PDF p. 169):**
For **every** field `K` (including all positive characteristics `≠ p`), if irreducible `f ∈ K[X]` of
prime degree `p ≠ char K` is solvable by radicals, then `L = K(α, β)` for any two distinct roots
`α, β` of `f` in any splitting field `L : K`.
(Proved in positive characteristic via Frobenius reduction `frobenius_reduction_of_radical_extension_ch20`
+ `Theorem 17.6`, and in characteristic `0` directly via `Theorem 17.6`.) -/
theorem exercise_20_5_mp {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {p : ℕ} (hp : Nat.Prime p) (hchar : ringChar K ≠ p)
    {f : K[X]} (hirr : Irreducible f) (hdeg : f.natDegree = p)
    (hsf : IsGarlingSplittingFieldExtension K L f)
    (hsol : IsGarlingSolvableByRadicals f) :
    ∀ α ∈ garlingRootSet K L f, ∀ β ∈ garlingRootSet K L f, α ≠ β →
      IntermediateField.adjoin K ({α, β} : Set L) = ⊤ := by
  classical
  obtain ⟨hf_sep, _⟩ := separable_of_irreducible_prime_deg_ne_char hp hchar hirr hdeg
  have hsol_gal : IsGarlingSoluble (GarlingPolyGaloisGroup K L f) := by
    rcases hsol with ⟨E, fE, aE, hradE, hsplE⟩
    let _ : Field E := fE
    let _ : Algebra K E := aE
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | h0
    · -- Positive characteristic `q = ringChar K ≠ p`: Frobenius-reduce `E` to `N` with `q ∤ ∏ d_i`!
      obtain ⟨N, _, hradN, _, hsepN⟩ :=
        frobenius_reduction_of_radical_extension_ch20 hq rfl hradE
      have hsplN : GarlingSplitsOver K N f := by
        rcases hsplE with ⟨m, lam, α, hexp⟩
        have hα_mem : ∀ j : Fin m, α j ∈ N := by
          intro j
          apply hsepN (α j)
          have hroot : Polynomial.aeval (α j) f = 0 := by
            rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hexp,
              Polynomial.eval_mul, Polynomial.eval_prod]
            exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) (by simp))
          exact hf_sep.of_dvd (minpoly.dvd K (α j) hroot)
        refine ⟨m, lam, fun j => ⟨α j, hα_mem j⟩, ?_⟩
        unfold GarlingSplitsExplicit
        apply Polynomial.map_injective N.val.toRingHom N.val.injective
        have h1 : (f.map (algebraMap K N)).map N.val.toRingHom = f.map (algebraMap K E) := by
          rw [Polynomial.map_map]; rfl
        rw [h1, hexp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]; rfl
      rcases hradN with ⟨r, T, β, d, h0, hlast, hchar_d, hstep⟩
      exact theorem_17_6 h0 hlast hstep hchar_d hsplN hsf
    · have _ : CharP K 0 := h0 ▸ ringChar.charP K
      have _ : CharZero K := CharP.charP_to_charZero K
      obtain ⟨r, T, β, d, h0, hlast, hchar_d, hstep⟩ :=
        isGarlingRadicalExtensionNotCharDvd_of_charZero hradE
      exact theorem_17_6 h0 hlast hstep hchar_d hsplE hsf
  exact (exercise_20_5_galois_iff hp hchar hirr hdeg hsf).mp hsol_gal

/-- Helper for `Exercise 20.5`: over ANY field `k`, `X^3 + t X + t` is irreducible over `RatFunc k`. -/
private theorem ex20_5_cubic_irred_over_ratFunc (k : Type) [Field k] :
    Irreducible (Polynomial.X ^ 3 + Polynomial.C (RatFunc.X : RatFunc k) * Polynomial.X +
      Polynomial.C (RatFunc.X : RatFunc k)) := by
  let Fk := RatFunc k
  let tk : Fk := RatFunc.X
  let fk : Fk[X] := Polynomial.X ^ 3 + Polynomial.C tk * Polynomial.X + Polynomial.C tk
  have hfk_deg : fk.natDegree = 3 := by dsimp [fk]; compute_degree!
  have hfk0 : fk ≠ 0 := fun h0 => by rw [h0, Polynomial.natDegree_zero] at hfk_deg; omega
  have hnoroot : ∀ x : Fk, fk.eval x ≠ 0 := by
    intro x hx
    let a : k[X] := x.num
    let b : k[X] := x.denom
    have hb0 : b ≠ 0 := RatFunc.denom_ne_zero x
    have hcop : IsCoprime a b := RatFunc.isCoprime_num_denom x
    have hx_eq : x = algebraMap k[X] Fk a / algebraMap k[X] Fk b := (RatFunc.num_div_denom x).symm
    have hb_alg0 : algebraMap k[X] Fk b ≠ 0 :=
      (map_ne_zero_iff (algebraMap k[X] Fk) (IsFractionRing.injective k[X] Fk)).mpr hb0
    have htk_eq : tk = algebraMap k[X] Fk Polynomial.X := rfl
    have heval : x ^ 3 + tk * x + tk = 0 := by simpa [fk] using hx
    rw [hx_eq, htk_eq] at heval
    have hclear : (algebraMap k[X] Fk a) ^ 3 +
        algebraMap k[X] Fk Polynomial.X * algebraMap k[X] Fk a * (algebraMap k[X] Fk b) ^ 2 +
        algebraMap k[X] Fk Polynomial.X * (algebraMap k[X] Fk b) ^ 3 = 0 := by
      let A := algebraMap k[X] Fk a
      let B := algebraMap k[X] Fk b
      let T := algebraMap k[X] Fk Polynomial.X
      have hmul : ((A / B) ^ 3 + T * (A / B) + T) * B ^ 3 = 0 := by
        rw [show (A / B) ^ 3 + T * (A / B) + T = 0 from heval, zero_mul]
      have h1 : (A / B) ^ 3 * B ^ 3 = A ^ 3 := by
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 3 hb_alg0)]
      have h2 : T * (A / B) * B ^ 3 = T * A * B ^ 2 := by
        calc T * (A / B) * B ^ 3
            = T * ((A / B) * B) * B ^ 2 := by ring
          _ = T * A * B ^ 2 := by rw [div_mul_cancel₀ _ hb_alg0]
      rw [add_mul, add_mul, h1, h2] at hmul
      exact hmul
    have hpoly0 : a ^ 3 + Polynomial.X * a * b ^ 2 + Polynomial.X * b ^ 3 = 0 := by
      apply IsFractionRing.injective k[X] Fk
      simpa only [map_add, map_mul, map_pow, map_zero] using hclear
    have hb_dvd_a3 : b ∣ a ^ 3 := ⟨-(Polynomial.X * a * b + Polynomial.X * b ^ 2), by linear_combination hpoly0⟩
    have hb_unit : IsUnit b := (hcop.symm.pow_right (n := 3)).isUnit_of_dvd' (dvd_refl b) hb_dvd_a3
    have hX_prime : Prime (Polynomial.X : k[X]) := Polynomial.prime_X
    have hX_dvd_a3 : Polynomial.X ∣ a ^ 3 := ⟨-(a * b ^ 2 + b ^ 3), by linear_combination hpoly0⟩
    obtain ⟨a₁, ha₁⟩ := hX_prime.dvd_of_dvd_pow hX_dvd_a3
    rw [ha₁] at hpoly0
    have hX2_dvd : Polynomial.X ^ 2 ∣ Polynomial.X * b ^ 3 :=
      ⟨-(Polynomial.X * a₁ ^ 3 + a₁ * b ^ 2), by linear_combination hpoly0⟩
    rcases hX2_dvd with ⟨c, hc⟩
    have hX_dvd_b3 : Polynomial.X ∣ b ^ 3 :=
      ⟨c, mul_left_cancel₀ Polynomial.X_ne_zero (show Polynomial.X * b ^ 3 = Polynomial.X * (Polynomial.X * c) by
        linear_combination hc)⟩
    exact hX_prime.not_isUnit (isUnit_of_dvd_unit (hX_prime.dvd_of_dvd_pow hX_dvd_b3) hb_unit)
  refine ⟨fun hu => by
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    change fk.natDegree = 0 at h0; omega, ?_⟩
  intro g h hgh
  change fk = g * h at hgh
  by_contra hboth
  push Not at hboth
  have hg0 : g ≠ 0 := fun h0 => hfk0 (by rw [hgh, h0, zero_mul])
  have hh0 : h ≠ 0 := fun h0 => hfk0 (by rw [hgh, h0, mul_zero])
  have hg1 : 1 ≤ g.natDegree := by
    by_contra h0; have : g.natDegree = 0 := by omega
    exact hboth.1 (Polynomial.isUnit_iff_degree_eq_zero.mpr (by rw [Polynomial.degree_eq_natDegree hg0, this]; rfl))
  have hh1 : 1 ≤ h.natDegree := by
    by_contra h0; have : h.natDegree = 0 := by omega
    exact hboth.2 (Polynomial.isUnit_iff_degree_eq_zero.mpr (by rw [Polynomial.degree_eq_natDegree hh0, this]; rfl))
  have hsum : g.natDegree + h.natDegree = 3 := by
    rw [← Polynomial.natDegree_mul hg0 hh0, ← hgh, hfk_deg]
  have hex1 : ∃ lin : Fk[X], lin.natDegree = 1 ∧ lin ∣ fk := by
    by_cases hg_eq1 : g.natDegree = 1
    · exact ⟨g, hg_eq1, ⟨h, hgh⟩⟩
    · exact ⟨h, by omega, ⟨g, hgh.trans (mul_comm g h)⟩⟩
  obtain ⟨lin, hlin_deg, c, hfk_eq⟩ := hex1
  let r : Fk := -(lin.coeff 0) / lin.coeff 1
  have hlc1 : lin.coeff 1 ≠ 0 := by
    rw [← hlin_deg, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr fun h0 => by simp [h0] at hlin_deg
  have hlin_r : lin.eval r = 0 := by
    have hlin_form := Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.degree_le_of_natDegree_le hlin_deg.le)
    conv_lhs => rw [hlin_form]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, r]
    rw [mul_div_cancel₀ _ hlc1, neg_add_cancel]
  exact hnoroot r (by rw [hfk_eq, Polynomial.eval_mul, hlin_r, zero_mul])

/-- Elementary characteristic-2 rational-function contradiction for `Exercise 20.5`: over any field
`Kbar`, if `αΩ ∈ Ω` is transcendental over `Kbar` in characteristic 2, `tΩ = αΩ^3 / (αΩ + 1)`, and
`βΩ ∈ Kbar(αΩ)` is a second root of `X^3 + tΩ X + tΩ = 0` (`βΩ ≠ αΩ`), then `y = βΩ / αΩ ∈ Kbar(αΩ)`
satisfies `y^2 + y = 1 / (αΩ + 1)`, giving `(u^2 + uv)(X + 1) = v^2` in `Kbar[X]` with `u, v` coprime,
contradicting `Prime (X + 1)`. -/
private theorem ex20_5_char2_ratFunc_impossible {Kbar Ω : Type} [Field Kbar] [Field Ω]
    [Algebra Kbar Ω] [CharP Ω 2] {tΩ αΩ βΩ : Ω}
    (hα_trans : IsGarlingTranscendental Kbar αΩ)
    (hα_ne0 : αΩ ≠ 0) (hα_ne_m1 : αΩ + 1 ≠ 0)
    (hα_eq : αΩ ^ 3 + tΩ * αΩ + tΩ = 0) (hβ_eq : βΩ ^ 3 + tΩ * βΩ + tΩ = 0)
    (hαβ_Ω : βΩ ≠ αΩ) (ht_expr : tΩ = αΩ ^ 3 / (αΩ + 1))
    (hβ_in : βΩ ∈ IntermediateField.adjoin Kbar ({αΩ} : Set Ω)) :
    False := by
  classical
  have h2Ω : (2 : Ω) = 0 := CharP.cast_eq_zero Ω 2
  let Kα : IntermediateField Kbar Ω := IntermediateField.adjoin Kbar ({αΩ} : Set Ω)
  have hφP_inj_Kα : Function.Injective
      (Polynomial.aeval (⟨αΩ, IntermediateField.subset_adjoin Kbar _ rfl⟩ : Kα) : Kbar[X] →ₐ[Kbar] Kα) := by
    intro P₁ P₂ h12; by_contra hne
    have h0 : Polynomial.aeval αΩ (P₁ - P₂) = 0 := by
      have h1 : Kα.val (Polynomial.aeval (⟨αΩ, IntermediateField.subset_adjoin Kbar _ rfl⟩ : Kα) (P₁ - P₂)) =
          Polynomial.aeval αΩ (P₁ - P₂) := (Polynomial.aeval_algHom_apply Kα.val _ _).symm
      rw [← h1, map_sub, show Polynomial.aeval _ P₁ = Polynomial.aeval _ P₂ from h12, sub_self, map_zero]
    exact hα_trans ⟨P₁ - P₂, sub_ne_zero.mpr hne, h0⟩
  let φRF_Kα : RatFunc Kbar →ₐ[Kbar] Kα :=
    { IsFractionRing.lift hφP_inj_Kα with
      commutes' := fun c => by
        change IsFractionRing.lift hφP_inj_Kα (algebraMap Kbar[X] (RatFunc Kbar) (Polynomial.C c)) = _
        rw [IsFractionRing.lift_algebraMap]; simp }
  have hsurj_Kα : Function.Surjective φRF_Kα := by
    intro ⟨x, hx⟩
    let Msub : IntermediateField Kbar Kα :=
      φRF_Kα.range.toIntermediateField fun _ ⟨u, hu⟩ => ⟨u⁻¹, by rw [map_inv₀, hu]⟩
    let M : IntermediateField Kbar Ω := Msub.map Kα.val
    have hsub : Kα ≤ M := by
      rw [IntermediateField.adjoin_le_iff]; rintro _ rfl
      refine ⟨⟨_, IntermediateField.subset_adjoin Kbar _ rfl⟩, ⟨RatFunc.X, ?_⟩, rfl⟩
      change IsFractionRing.lift hφP_inj_Kα (algebraMap Kbar[X] (RatFunc Kbar) Polynomial.X) = _
      rw [IsFractionRing.lift_algebraMap]; simp
    obtain ⟨z, ⟨u, rfl⟩, hzx⟩ := hsub hx
    exact ⟨u, Subtype.ext hzx⟩
  let eKα : RatFunc Kbar ≃ₐ[Kbar] Kα := AlgEquiv.ofBijective φRF_Kα ⟨φRF_Kα.injective, hsurj_Kα⟩
  have heKα_X : ((eKα RatFunc.X : Kα) : Ω) = αΩ := by
    change ((IsFractionRing.lift hφP_inj_Kα (algebraMap Kbar[X] (RatFunc Kbar) Polynomial.X) : Kα) : Ω) = αΩ
    rw [IsFractionRing.lift_algebraMap]; simp
  let yKα : Kα := ⟨βΩ / αΩ, Kα.div_mem hβ_in (IntermediateField.subset_adjoin Kbar _ rfl)⟩
  let yRF : RatFunc Kbar := eKα.symm yKα
  have hy_eq : yRF ^ 2 + yRF = (RatFunc.X + 1)⁻¹ := by
    apply eKα.injective; apply Subtype.ext
    have hy_val : ((eKα yRF : Kα) : Ω) = βΩ / αΩ := by simp [yRF, yKα]
    have hLHS : ((eKα (yRF ^ 2 + yRF) : Kα) : Ω) = (βΩ / αΩ) ^ 2 + (βΩ / αΩ) := by
      simp [map_add, map_pow, hy_val]
    have hRHS : ((eKα (RatFunc.X + 1)⁻¹ : Kα) : Ω) = (αΩ + 1)⁻¹ := by
      simp [map_inv₀, map_add, heKα_X]
    rw [hLHS, hRHS]
    have hquad : βΩ ^ 2 + αΩ * βΩ + (αΩ ^ 2 + tΩ) = 0 := by
      have hdiff : (βΩ - αΩ) * (βΩ ^ 2 + αΩ * βΩ + (αΩ ^ 2 + tΩ)) = 0 := by
        linear_combination hβ_eq - hα_eq
      exact (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hαβ_Ω)
    have hquad' : (βΩ ^ 2 + αΩ * βΩ + αΩ ^ 2) * (αΩ + 1) + αΩ ^ 3 = 0 := by
      have h1 : tΩ * (αΩ + 1) = αΩ ^ 3 := by rw [ht_expr, div_mul_cancel₀ _ hα_ne_m1]
      linear_combination (αΩ + 1) * hquad - h1
    apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 hα_ne0) hα_ne_m1)
    have h1 : ((βΩ / αΩ) ^ 2 + βΩ / αΩ) * (αΩ ^ 2 * (αΩ + 1)) = (βΩ ^ 2 + αΩ * βΩ) * (αΩ + 1) := by
      rw [add_mul, div_pow, ← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 hα_ne0)]
      have h2 : βΩ / αΩ * (αΩ ^ 2 * (αΩ + 1)) = αΩ * βΩ * (αΩ + 1) := by
        calc βΩ / αΩ * (αΩ ^ 2 * (αΩ + 1))
            = (βΩ / αΩ * αΩ) * (αΩ * (αΩ + 1)) := by ring
          _ = βΩ * (αΩ * (αΩ + 1)) := by rw [div_mul_cancel₀ _ hα_ne0]
          _ = αΩ * βΩ * (αΩ + 1) := by ring
      rw [h2]; ring
    have h3 : (αΩ + 1)⁻¹ * (αΩ ^ 2 * (αΩ + 1)) = αΩ ^ 2 := by
      calc (αΩ + 1)⁻¹ * (αΩ ^ 2 * (αΩ + 1))
          = αΩ ^ 2 * ((αΩ + 1)⁻¹ * (αΩ + 1)) := by ring
        _ = αΩ ^ 2 := by rw [inv_mul_cancel₀ hα_ne_m1, mul_one]
    rw [h1, h3]
    linear_combination hquad' - h2Ω * (αΩ ^ 3 + αΩ ^ 2)
  let u : Kbar[X] := yRF.num
  let v : Kbar[X] := yRF.denom
  have hv0 : v ≠ 0 := RatFunc.denom_ne_zero yRF
  have hcop : IsCoprime u v := RatFunc.isCoprime_num_denom yRF
  have hZ1_ne0 : (Polynomial.X + 1 : Kbar[X]) ≠ 0 := by
    intro h0; have := congrArg (Polynomial.eval 0) h0; simp at this
  have hZ1_rf0 : (RatFunc.X + 1 : RatFunc Kbar) ≠ 0 := by
    have h1 : (RatFunc.X + 1 : RatFunc Kbar) = algebraMap Kbar[X] (RatFunc Kbar) (Polynomial.X + 1) := by
      rw [map_add, map_one]; rfl
    rw [h1]
    exact (map_ne_zero_iff _ (IsFractionRing.injective Kbar[X] (RatFunc Kbar))).mpr hZ1_ne0
  have hv_rf0 : algebraMap Kbar[X] (RatFunc Kbar) v ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Kbar[X] (RatFunc Kbar))).mpr hv0
  have hpoly_eq : (u ^ 2 + u * v) * (Polynomial.X + 1) = v ^ 2 := by
    apply IsFractionRing.injective Kbar[X] (RatFunc Kbar)
    simp only [map_mul, map_add, map_pow, map_one]
    let U := algebraMap Kbar[X] (RatFunc Kbar) u
    let V := algebraMap Kbar[X] (RatFunc Kbar) v
    let Z1 : RatFunc Kbar := RatFunc.X + 1
    have hy_div : yRF = U / V := (RatFunc.num_div_denom yRF).symm
    have hL : (U / V) ^ 2 + U / V = Z1⁻¹ := hy_div ▸ hy_eq
    have hmul := congrArg (· * (V ^ 2 * Z1)) hL
    have h1 : ((U / V) ^ 2 + U / V) * (V ^ 2 * Z1) = (U ^ 2 + U * V) * Z1 := by
      rw [add_mul, div_pow, ← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 hv_rf0)]
      have h2 : U / V * (V ^ 2 * Z1) = U * V * Z1 := by
        calc U / V * (V ^ 2 * Z1) = (U / V * V) * (V * Z1) := by ring
          _ = U * (V * Z1) := by rw [div_mul_cancel₀ _ hv_rf0]
          _ = U * V * Z1 := by ring
      rw [h2]; ring
    have h3 : Z1⁻¹ * (V ^ 2 * Z1) = V ^ 2 := by
      calc Z1⁻¹ * (V ^ 2 * Z1) = V ^ 2 * (Z1⁻¹ * Z1) := by ring
        _ = V ^ 2 := by rw [inv_mul_cancel₀ hZ1_rf0, mul_one]
    rw [h1, h3] at hmul
    exact hmul
  have hZ1_prime : Prime (Polynomial.X + 1 : Kbar[X]) := by
    rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
    exact Polynomial.irreducible_of_degree_eq_one (Polynomial.degree_X_add_C 1)
  have hdvd_v2 : (Polynomial.X + 1 : Kbar[X]) ∣ v ^ 2 := ⟨u ^ 2 + u * v, by linear_combination hpoly_eq.symm⟩
  obtain ⟨w, hw⟩ := hZ1_prime.dvd_of_dvd_pow hdvd_v2
  have hpoly_w : (u ^ 2 + u * ((Polynomial.X + 1) * w)) * (Polynomial.X + 1) = ((Polynomial.X + 1) * w) ^ 2 := by
    rw [← hw]; exact hpoly_eq
  have hcancel : u ^ 2 + u * ((Polynomial.X + 1) * w) = (Polynomial.X + 1) * w ^ 2 :=
    mul_right_cancel₀ hZ1_ne0 (by linear_combination hpoly_w)
  have hdvd_u2 : (Polynomial.X + 1 : Kbar[X]) ∣ u ^ 2 := ⟨w ^ 2 - u * w, by linear_combination hcancel⟩
  have hdvd_u : (Polynomial.X + 1 : Kbar[X]) ∣ u := hZ1_prime.dvd_of_dvd_pow hdvd_u2
  exact hZ1_prime.not_isUnit (hcop.isUnit_of_dvd' hdvd_u ⟨w, hw⟩)

/-- Helper for `Exercise 20.5`: in characteristic `2`, `X^3 + t' X + t'` over `F' = Kbar(tΩ)`
(`tΩ` transcendental over `Kbar`) cannot split in any finite extension `N' : F'` of odd degree
embedded in `Ω`. -/
private theorem ex20_5_char2_odd_finrank_impossible {Kbar Ω N' : Type} [Field Kbar] [Field Ω]
    [Field N'] [Algebra Kbar Ω] [CharP Ω 2] {tΩ : Ω}
    (htΩ_trans : IsGarlingTranscendental Kbar tΩ)
    [Algebra (IntermediateField.adjoin Kbar ({tΩ} : Set Ω)) N']
    [Algebra N' Ω] [IsScalarTower (IntermediateField.adjoin Kbar ({tΩ} : Set Ω)) N' Ω]
    [Module.Finite (IntermediateField.adjoin Kbar ({tΩ} : Set Ω)) N']
    (hnot2 : ¬ (2 ∣ Module.finrank (IntermediateField.adjoin Kbar ({tΩ} : Set Ω)) N'))
    (hsplN' : GarlingSplitsOver (IntermediateField.adjoin Kbar ({tΩ} : Set Ω)) N'
      (Polynomial.X ^ 3 +
        Polynomial.C (⟨tΩ, IntermediateField.subset_adjoin Kbar _ rfl⟩ :
          IntermediateField.adjoin Kbar ({tΩ} : Set Ω)) * Polynomial.X +
        Polynomial.C ⟨tΩ, IntermediateField.subset_adjoin Kbar _ rfl⟩)) :
    False := by
  classical
  let F' : IntermediateField Kbar Ω := IntermediateField.adjoin Kbar ({tΩ} : Set Ω)
  let t' : F' := ⟨tΩ, IntermediateField.subset_adjoin Kbar _ rfl⟩
  let f' : F'[X] := Polynomial.X ^ 3 + Polynomial.C t' * Polynomial.X + Polynomial.C t'
  have hf'_mon : f'.Monic := by
    dsimp [f']
    have hlt : (Polynomial.C t' * Polynomial.X + Polynomial.C t').natDegree < 3 := by compute_degree!
    rw [add_assoc]
    exact Polynomial.monic_X_pow_add (Polynomial.degree_lt_iff_coeff_zero _ _ |>.mpr fun m hm =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  have hf'_deg : f'.natDegree = 3 := by dsimp [f']; compute_degree!
  have _ : CharP F' 2 := ⟨fun n => by
    rw [← F'.val.injective.eq_iff, map_natCast, map_zero, CharP.cast_eq_zero_iff Ω 2]⟩
  have hcharF' : ringChar F' = 2 := ringChar.eq F' 2
  -- `F' ≃ₐ[Kbar] RatFunc Kbar`, so `f'` is irreducible and separable:
  have hφP_inj_F' : Function.Injective (Polynomial.aeval t' : Kbar[X] →ₐ[Kbar] F') := by
    intro P₁ P₂ h12; by_contra hne
    have hsub0 : Polynomial.aeval tΩ (P₁ - P₂) = 0 := by
      have h1 : F'.val (Polynomial.aeval t' (P₁ - P₂)) = Polynomial.aeval tΩ (P₁ - P₂) :=
        (Polynomial.aeval_algHom_apply F'.val t' (P₁ - P₂)).symm
      rw [← h1, map_sub, show Polynomial.aeval t' P₁ = Polynomial.aeval t' P₂ from h12, sub_self, map_zero]
    exact htΩ_trans ⟨P₁ - P₂, sub_ne_zero.mpr hne, hsub0⟩
  let φRF_F' : RatFunc Kbar →ₐ[Kbar] F' :=
    { IsFractionRing.lift hφP_inj_F' with
      commutes' := fun c => by
        change IsFractionRing.lift hφP_inj_F' (algebraMap Kbar[X] (RatFunc Kbar) (Polynomial.C c)) = _
        rw [IsFractionRing.lift_algebraMap]; simp }
  have hφRF_surj_F' : Function.Surjective φRF_F' := by
    intro ⟨x, hx⟩
    let Msub : IntermediateField Kbar F' :=
      φRF_F'.range.toIntermediateField fun _ ⟨u, hu⟩ => ⟨u⁻¹, by rw [map_inv₀, hu]⟩
    let M : IntermediateField Kbar Ω := Msub.map F'.val
    have hsub : F' ≤ M := by
      rw [IntermediateField.adjoin_le_iff]; rintro _ rfl
      refine ⟨t', ⟨RatFunc.X, ?_⟩, rfl⟩
      change IsFractionRing.lift hφP_inj_F' (algebraMap Kbar[X] (RatFunc Kbar) Polynomial.X) = t'
      rw [IsFractionRing.lift_algebraMap]; simp
    obtain ⟨z, ⟨u, rfl⟩, hzx⟩ := hsub hx
    exact ⟨u, Subtype.ext hzx⟩
  let eF' : RatFunc Kbar ≃ₐ[Kbar] F' := AlgEquiv.ofBijective φRF_F' ⟨φRF_F'.injective, hφRF_surj_F'⟩
  have heF'_X : eF' RatFunc.X = t' := by
    change IsFractionRing.lift hφP_inj_F' (algebraMap Kbar[X] (RatFunc Kbar) Polynomial.X) = t'
    rw [IsFractionRing.lift_algebraMap]; simp
  have hirr_f' : Irreducible f' := by
    let gRF : (RatFunc Kbar)[X] :=
      Polynomial.X ^ 3 + Polynomial.C (RatFunc.X : RatFunc Kbar) * Polynomial.X +
        Polynomial.C (RatFunc.X : RatFunc Kbar)
    have hg_irr : Irreducible gRF := ex20_5_cubic_irred_over_ratFunc Kbar
    have hf'_map : f' = gRF.map eF'.toRingHom := by simp [f', gRF, heF'_X]
    have hg_map : gRF = f'.map eF'.symm.toRingHom := by
      rw [hf'_map, Polynomial.map_map]
      have hcomp : eF'.symm.toRingHom.comp eF'.toRingHom = RingHom.id _ := by ext x; simp
      rw [hcomp, Polynomial.map_id]
    refine ⟨fun hu => hg_irr.1 (hg_map ▸ hu.map (Polynomial.mapRingHom eF'.symm.toRingHom)), fun a b hab => ?_⟩
    have hab' : gRF = a.map eF'.symm.toRingHom * b.map eF'.symm.toRingHom := by
      rw [hg_map, hab, Polynomial.map_mul]
    rcases hg_irr.2 hab' with ha | hb
    · left
      have ha' := ha.map (Polynomial.mapRingHom eF'.toRingHom)
      have hback : (a.map eF'.symm.toRingHom).map eF'.toRingHom = a := by
        rw [Polynomial.map_map]; have : eF'.toRingHom.comp eF'.symm.toRingHom = RingHom.id _ := by ext x; simp
        rw [this, Polynomial.map_id]
      rwa [Polynomial.coe_mapRingHom, hback] at ha'
    · right
      have hb' := hb.map (Polynomial.mapRingHom eF'.toRingHom)
      have hback : (b.map eF'.symm.toRingHom).map eF'.toRingHom = b := by
        rw [Polynomial.map_map]; have : eF'.toRingHom.comp eF'.symm.toRingHom = RingHom.id _ := by ext x; simp
        rw [this, Polynomial.map_id]
      rwa [Polynomial.coe_mapRingHom, hback] at hb'
  have hf'_sep : f'.Separable :=
    (separable_of_irreducible_prime_deg_ne_char (by decide) (by omega) hirr_f' hf'_deg).1
  obtain ⟨m, lam, αN, hexpN⟩ := hsplN'
  have hm3 : m = 3 := by
    have h1 := (garlingSplitsExplicit_props hf'_mon.ne_zero hexpN).2.2.1
    rw [garlingDegree, hf'_deg] at h1; exact h1
  subst hm3
  have hα_root : ∀ j : Fin 3, Polynomial.aeval (αN j) f' = 0 := fun j => by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hexpN, Polynomial.eval_mul, Polynomial.eval_prod]
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) (by simp))
  have hα_inj : Function.Injective αN :=
    ((injective_roots_iff_separable_and_not_repeated hf'_mon.ne_zero hexpN).1.mpr hf'_sep)
  let α₀ : N' := αN 0
  let β₀ : N' := αN 1
  have hαβ_ne : β₀ ≠ α₀ := fun h => by have := hα_inj h; exact absurd this (by decide)
  let Mα : IntermediateField F' N' := IntermediateField.adjoin F' ({α₀} : Set N')
  have hβ_mem_Mα : β₀ ∈ Mα := by
    -- Work directly inside `N'` as an `Mα`-algebra (no manual `Algebra` instance, zero diamonds):
    let Mβ : IntermediateField Mα N' := IntermediateField.adjoin Mα ({β₀} : Set N')
    let αM : Mα := ⟨α₀, IntermediateField.subset_adjoin F' _ rfl⟩
    let q2 : Mα[X] := Polynomial.X ^ 2 + Polynomial.C αM * Polynomial.X +
      Polynomial.C (αM ^ 2 + algebraMap F' Mα t')
    have hq2_mon : q2.Monic := by
      dsimp [q2]
      have hlt : (Polynomial.C αM * Polynomial.X + Polynomial.C (αM ^ 2 + algebraMap F' Mα t')).natDegree < 2 := by
        compute_degree!
      rw [add_assoc]
      exact Polynomial.monic_X_pow_add (Polynomial.degree_lt_iff_coeff_zero _ _ |>.mpr fun m hm =>
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
    have hq2_deg : q2.natDegree = 2 := by dsimp [q2]; compute_degree!
    have hq2_β : Polynomial.aeval β₀ q2 = 0 := by
      have h0α : α₀ ^ 3 + algebraMap F' N' t' * α₀ + algebraMap F' N' t' = 0 := by
        simpa [f'] using hα_root 0
      have h0β : β₀ ^ 3 + algebraMap F' N' t' * β₀ + algebraMap F' N' t' = 0 := by
        simpa [f'] using hα_root 1
      have hdiff : (β₀ - α₀) * (β₀ ^ 2 + α₀ * β₀ + (α₀ ^ 2 + algebraMap F' N' t')) = 0 := by
        linear_combination h0β - h0α
      have hfac0 := (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hαβ_ne)
      simpa [q2, αM] using hfac0
    have hβ_int : IsIntegral Mα β₀ := ⟨q2, hq2_mon, hq2_β⟩
    have hfin_step : Module.finrank Mα Mβ ≤ 2 := by
      rw [IntermediateField.adjoin.finrank hβ_int]
      exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd Mα β₀ hq2_β) hq2_mon.ne_zero).trans hq2_deg.le
    have hdvd_N' : Module.finrank Mα Mβ ∣ Module.finrank F' N' := by
      have _ : Module.Finite F' Mα := inferInstance
      have _ : Module.Finite Mα N' := Module.Finite.right F' Mα N'
      have _ : Module.Finite Mα Mβ := inferInstance
      have _ : Module.Finite Mβ N' := Module.Finite.right Mα Mβ N'
      have h1 := Module.finrank_mul_finrank Mα Mβ N'
      have h2 := Module.finrank_mul_finrank F' Mα N'
      exact ⟨Module.finrank F' Mα * Module.finrank Mβ N', by rw [← h2, ← h1]; ring⟩
    have hpos_step : 0 < Module.finrank Mα Mβ := Module.finrank_pos
    have hne2 : Module.finrank Mα Mβ ≠ 2 := fun h2 => hnot2 (h2 ▸ hdvd_N')
    have hstep1 : Module.finrank Mα Mβ = 1 := by omega
    have hbot : (⊥ : IntermediateField Mα N') = Mβ :=
      IntermediateField.eq_of_le_of_finrank_eq bot_le (by rw [IntermediateField.finrank_bot, hstep1])
    have hmem : β₀ ∈ (⊥ : IntermediateField Mα N') :=
      hbot.symm ▸ IntermediateField.subset_adjoin Mα _ rfl
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp hmem
    exact hy ▸ y.2
  let αΩ : Ω := algebraMap N' Ω α₀
  let βΩ : Ω := algebraMap N' Ω β₀
  have h2Ω : (2 : Ω) = 0 := CharP.cast_eq_zero Ω 2
  have hα_eq : αΩ ^ 3 + tΩ * αΩ + tΩ = 0 := by
    have h0 := congrArg (algebraMap N' Ω) (hα_root 0)
    have ht_map : algebraMap N' Ω (algebraMap F' N' t') = tΩ := by
      rw [← IsScalarTower.algebraMap_apply F' N' Ω]; rfl
    simpa [f', αΩ, ht_map] using h0
  have hβ_eq : βΩ ^ 3 + tΩ * βΩ + tΩ = 0 := by
    have h0 := congrArg (algebraMap N' Ω) (hα_root 1)
    have ht_map : algebraMap N' Ω (algebraMap F' N' t') = tΩ := by
      rw [← IsScalarTower.algebraMap_apply F' N' Ω]; rfl
    simpa [f', βΩ, ht_map] using h0
  have hαβ_Ω : βΩ ≠ αΩ := fun h => hαβ_ne ((algebraMap N' Ω).injective h)
  have hα_ne0 : αΩ ≠ 0 := fun h0 => by
    rw [h0, zero_pow (by decide), mul_zero, zero_add, zero_add] at hα_eq
    exact htΩ_trans ⟨Polynomial.X, Polynomial.X_ne_zero, by simpa using hα_eq⟩
  have hα_ne_m1 : αΩ + 1 ≠ 0 := fun h0 => by
    have hα1 : αΩ = 1 := by linear_combination h0 - h2Ω
    rw [hα1] at hα_eq
    exact one_ne_zero (show (1 : Ω) = 0 by linear_combination hα_eq - h2Ω * tΩ)
  have ht_expr : tΩ = αΩ ^ 3 / (αΩ + 1) := by
    rw [eq_div_iff hα_ne_m1]
    linear_combination hα_eq - h2Ω * αΩ ^ 3
  let Kα : IntermediateField Kbar Ω := IntermediateField.adjoin Kbar ({αΩ} : Set Ω)
  have hα3 : αΩ ^ 3 ∈ Kα := by
    rw [pow_succ, pow_succ, pow_one]
    exact Kα.mul_mem
      (Kα.mul_mem (IntermediateField.subset_adjoin Kbar _ rfl) (IntermediateField.subset_adjoin Kbar _ rfl))
      (IntermediateField.subset_adjoin Kbar _ rfl)
  have hα_trans : IsGarlingTranscendental Kbar αΩ := by
    intro halg
    have hα_int : IsIntegral Kbar αΩ := ((isGarlingAlgebraic_iff Kbar αΩ).mp halg).isIntegral
    have _ : FiniteDimensional Kbar Kα := IntermediateField.adjoin.finiteDimensional hα_int
    have ht_in : tΩ ∈ Kα := by
      rw [ht_expr]
      exact Kα.div_mem hα3 (Kα.add_mem (IntermediateField.subset_adjoin Kbar _ rfl) Kα.one_mem)
    have ht_alg : IsAlgebraic Kbar (⟨tΩ, ht_in⟩ : Kα) := Algebra.IsAlgebraic.isAlgebraic _
    have ht_alg_Ω : IsAlgebraic Kbar tΩ := by
      obtain ⟨g, hg0, hg⟩ := ht_alg
      refine ⟨g, hg0, ?_⟩
      change Polynomial.aeval (Kα.val (⟨tΩ, ht_in⟩ : Kα)) g = 0
      rw [Polynomial.aeval_algHom_apply, hg, map_zero]
    exact htΩ_trans ((isGarlingAlgebraic_iff Kbar tΩ).mpr ht_alg_Ω)
  have hβ_in_Kbarα : βΩ ∈ Kα := by
    have hF'_le : F' ≤ Kα := by
      rw [IntermediateField.adjoin_le_iff]; rintro _ rfl
      rw [ht_expr]
      exact Kα.div_mem hα3 (Kα.add_mem (IntermediateField.subset_adjoin Kbar _ rfl) Kα.one_mem)
    let M : IntermediateField F' N' :=
      { carrier := {x : N' | algebraMap N' Ω x ∈ Kα}
        add_mem' := fun {a b} ha hb => by change algebraMap N' Ω (a + b) ∈ Kα; rw [map_add]; exact Kα.add_mem ha hb
        zero_mem' := by change algebraMap N' Ω 0 ∈ Kα; rw [map_zero]; exact Kα.zero_mem
        mul_mem' := fun {a b} ha hb => by change algebraMap N' Ω (a * b) ∈ Kα; rw [map_mul]; exact Kα.mul_mem ha hb
        one_mem' := by change algebraMap N' Ω 1 ∈ Kα; rw [map_one]; exact Kα.one_mem
        inv_mem' := fun {a} ha => by change algebraMap N' Ω a⁻¹ ∈ Kα; rw [map_inv₀]; exact Kα.inv_mem ha
        algebraMap_mem' := fun c => by
          change algebraMap N' Ω (algebraMap F' N' c) ∈ Kα
          rw [← IsScalarTower.algebraMap_apply F' N' Ω]; exact hF'_le c.2 }
    have hle : Mα ≤ M := by
      rw [IntermediateField.adjoin_le_iff]; rintro _ rfl
      exact IntermediateField.subset_adjoin Kbar _ rfl
    exact hle hβ_mem_Mα
  exact ex20_5_char2_ratFunc_impossible hα_trans hα_ne0 hα_ne_m1 hα_eq hβ_eq hαβ_Ω ht_expr hβ_in_Kbarα

/-- Helper for `Exercise 20.5`: deduces `(minpoly F' x).Separable` for a root `x ∈ L'` of
`X^3 + t' X + t'` checked via an injective ring hom `ι : L' →+* Ω` (avoiding nested
`IntermediateField` typeclass unfolding). -/
private theorem separable_minpoly_of_cubic_trinomial_inj {F' L' Ω : Type*}
    [Field F'] [Field L'] [Field Ω] [Algebra F' L']
    (ι : L' →+* Ω) (hι : Function.Injective ι)
    (t' : F') (hsep : (Polynomial.X ^ 3 + Polynomial.C t' * Polynomial.X + Polynomial.C t').Separable)
    (x : L') (hx : ι x ^ 3 + ι (algebraMap F' L' t') * ι x + ι (algebraMap F' L' t') = 0) :
    (minpoly F' x).Separable := by
  have hroot : Polynomial.aeval x
      (Polynomial.X ^ 3 + Polynomial.C t' * Polynomial.X + Polynomial.C t') = 0 := by
    apply hι
    simp only [map_zero, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    exact hx
  exact hsep.of_dvd (minpoly.dvd F' x hroot)

/-- Helper for `Exercise 20.5`: transports an explicit splitting `GarlingSplitsExplicit K E f` to
`GarlingSplitsExplicit F' N' (f.map ιKF')` along an injective ring hom `ιN'Ω : N' →+* Ω`. -/
private theorem garlingSplitsExplicit_lift_of_inj
    {K E F' N' Ω : Type*} [Field K] [Field E] [Field F'] [Field N'] [Field Ω]
    [Algebra K E] [Algebra F' N']
    (ιKF' : K →+* F') (ιEΩ : E →+* Ω) (ιN'Ω : N' →+* Ω) (hιN' : Function.Injective ιN'Ω)
    (hcomm : (ιN'Ω.comp (algebraMap F' N')).comp ιKF' = ιEΩ.comp (algebraMap K E))
    {f : K[X]} {m : ℕ} {lam : K} {α : Fin m → E}
    (hexp : GarlingSplitsExplicit K E f m lam α)
    (α' : Fin m → N') (hα' : ∀ j, ιN'Ω (α' j) = ιEΩ (α j)) :
    GarlingSplitsExplicit F' N' (f.map ιKF') m (ιKF' lam) α' := by
  unfold GarlingSplitsExplicit at hexp ⊢
  apply Polynomial.map_injective ιN'Ω hιN'
  rw [Polynomial.map_map, Polynomial.map_map, hcomm, ← Polynomial.map_map, hexp,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
  have hlam : ιN'Ω ((algebraMap F' N') (ιKF' lam)) = ιEΩ ((algebraMap K E) lam) :=
    RingHom.congr_fun hcomm lam
  refine congrArg₂ (· * ·) (congrArg Polynomial.C hlam.symm) (Finset.prod_congr rfl fun j _ => ?_)
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, (hα' j).symm]

/-- Helper for `Exercise 20.5`: lifts a radical extension `E : K` inside `Ω` to an intermediate
field `L' : IntermediateField F' Ω` containing the image of `E` that is a radical extension of `F'`. -/
private theorem lift_radical_tower_to_intermediate
    {K E F' Ω : Type*} [Field K] [Field E] [Field F'] [Field Ω]
    [Algebra K E] [Algebra E Ω] [Algebra F' Ω]
    (ιKF' : K →+* F') (hcomm : ∀ c : K, algebraMap F' Ω (ιKF' c) = algebraMap E Ω (algebraMap K E c))
    (hradE : IsGarlingExtensionByRadicals K E) :
    ∃ L' : IntermediateField F' Ω,
      (∀ x : E, algebraMap E Ω x ∈ L') ∧ IsGarlingExtensionByRadicals F' L' := by
  classical
  rcases hradE with ⟨r, TE, βE, hTE0, hTElast, hTEstep⟩
  let βΩ : Fin r → Ω := fun i => algebraMap E Ω (βE i)
  let L' : IntermediateField F' Ω := IntermediateField.adjoin F' (Set.range βΩ)
  have hE_le_L' : ∀ x : E, algebraMap E Ω x ∈ L' := by
    have hindE : ∀ (k : ℕ) (hk : k ≤ r) (x : E),
        x ∈ TE ⟨k, Nat.lt_succ_of_le hk⟩ → algebraMap E Ω x ∈ L' := by
      intro k
      induction k with
      | zero =>
        intro hk x hx
        have hx0 : x ∈ TE 0 := hx
        rw [hTE0] at hx0
        rcases IntermediateField.mem_bot.mp hx0 with ⟨c, rfl⟩
        rw [← hcomm c]
        exact L'.algebraMap_mem (ιKF' c)
      | succ k ih =>
        intro hk x hx
        let i : Fin r := ⟨k, hk⟩
        let M : IntermediateField K E :=
          { carrier := {y : E | algebraMap E Ω y ∈ L'}
            add_mem' := fun {a b} ha hb => by change algebraMap E Ω (a + b) ∈ L'; rw [map_add]; exact L'.add_mem ha hb
            zero_mem' := by change algebraMap E Ω 0 ∈ L'; rw [map_zero]; exact L'.zero_mem
            mul_mem' := fun {a b} ha hb => by change algebraMap E Ω (a * b) ∈ L'; rw [map_mul]; exact L'.mul_mem ha hb
            one_mem' := by change algebraMap E Ω 1 ∈ L'; rw [map_one]; exact L'.one_mem
            inv_mem' := fun {a} ha => by change algebraMap E Ω a⁻¹ ∈ L'; rw [map_inv₀]; exact L'.inv_mem ha
            algebraMap_mem' := fun c => by change algebraMap E Ω (algebraMap K E c) ∈ L'; rw [← hcomm c]; exact L'.algebraMap_mem (ιKF' c) }
        have hle : TE i.succ ≤ M := by
          rw [(hTEstep i).2, IntermediateField.adjoin_le_iff]
          rintro y (hy | rfl)
          · exact ih (Nat.le_of_lt hk) y hy
          · exact IntermediateField.subset_adjoin F' _ ⟨i, rfl⟩
        exact hle hx
    intro x
    exact hindE r le_rfl x (by rw [show (⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1)) = Fin.last r from rfl, hTElast]; trivial)
  have hradL' : IsGarlingExtensionByRadicals F' L' := by
    let βL' : Fin r → L' := fun i => ⟨βΩ i, IntermediateField.subset_adjoin F' _ ⟨i, rfl⟩⟩
    let TL' : Fin (r + 1) → IntermediateField F' L' := fun k =>
      IntermediateField.adjoin F' (βL' '' {i : Fin r | i.1 < k.1})
    have hTE_le_TL' : ∀ (k : ℕ) (hk : k ≤ r) (x : E),
        x ∈ TE ⟨k, Nat.lt_succ_of_le hk⟩ →
        (⟨algebraMap E Ω x, hE_le_L' x⟩ : L') ∈ TL' ⟨k, Nat.lt_succ_of_le hk⟩ := by
      intro k
      induction k with
      | zero =>
        intro hk x hx
        have hx0 : x ∈ TE 0 := hx
        rw [hTE0] at hx0
        rcases IntermediateField.mem_bot.mp hx0 with ⟨c, rfl⟩
        have h1 : (⟨algebraMap E Ω (algebraMap K E c), hE_le_L' (algebraMap K E c)⟩ : L') =
            algebraMap F' L' (ιKF' c) := Subtype.ext (hcomm c).symm
        rw [h1]
        exact (TL' _).algebraMap_mem (ιKF' c)
      | succ k ih =>
        intro hk x hx
        let i : Fin r := ⟨k, hk⟩
        let M : IntermediateField K E :=
          { carrier := {y : E | (⟨algebraMap E Ω y, hE_le_L' y⟩ : L') ∈ TL' i.succ}
            add_mem' := fun {a b} ha hb => by
              have h1 : (⟨algebraMap E Ω (a + b), hE_le_L' (a + b)⟩ : L') =
                  ⟨algebraMap E Ω a, hE_le_L' a⟩ + ⟨algebraMap E Ω b, hE_le_L' b⟩ := Subtype.ext (map_add _ _ _)
              change _ ∈ TL' i.succ; rw [h1]; exact (TL' i.succ).add_mem ha hb
            zero_mem' := by
              have h1 : (⟨algebraMap E Ω 0, hE_le_L' 0⟩ : L') = 0 := Subtype.ext (map_zero _)
              change _ ∈ TL' i.succ; rw [h1]; exact (TL' i.succ).zero_mem
            mul_mem' := fun {a b} ha hb => by
              have h1 : (⟨algebraMap E Ω (a * b), hE_le_L' (a * b)⟩ : L') =
                  ⟨algebraMap E Ω a, hE_le_L' a⟩ * ⟨algebraMap E Ω b, hE_le_L' b⟩ := Subtype.ext (map_mul _ _ _)
              change _ ∈ TL' i.succ; rw [h1]; exact (TL' i.succ).mul_mem ha hb
            one_mem' := by
              have h1 : (⟨algebraMap E Ω 1, hE_le_L' 1⟩ : L') = 1 := Subtype.ext (map_one _)
              change _ ∈ TL' i.succ; rw [h1]; exact (TL' i.succ).one_mem
            inv_mem' := fun {a} ha => by
              have h1 : (⟨algebraMap E Ω a⁻¹, hE_le_L' a⁻¹⟩ : L') =
                  (⟨algebraMap E Ω a, hE_le_L' a⟩ : L')⁻¹ := Subtype.ext (map_inv₀ (algebraMap E Ω) a)
              change _ ∈ TL' i.succ; rw [h1]; exact (TL' i.succ).inv_mem ha
            algebraMap_mem' := fun c => by
              have h1 : (⟨algebraMap E Ω (algebraMap K E c), hE_le_L' (algebraMap K E c)⟩ : L') =
                  algebraMap F' L' (ιKF' c) := Subtype.ext (hcomm c).symm
              change _ ∈ TL' i.succ; rw [h1]; exact (TL' i.succ).algebraMap_mem (ιKF' c) }
        have hle : TE i.succ ≤ M := by
          rw [(hTEstep i).2, IntermediateField.adjoin_le_iff]
          rintro y (hy | rfl)
          · exact IntermediateField.adjoin.mono F' _ _
              (Set.image_mono fun j hj => Nat.lt_succ_of_lt hj) (ih (Nat.le_of_lt hk) y hy)
          · exact IntermediateField.subset_adjoin F' _ ⟨i, Nat.lt_succ_self _, rfl⟩
        exact hle hx
    refine ⟨r, TL', βL', ?_, ?_, fun i => ?_⟩
    · have hempty : βL' '' {i : Fin r | i.1 < (0 : Fin (r + 1)).1} = ∅ := by ext x; simp
      rw [show TL' 0 = IntermediateField.adjoin F' (βL' '' {i : Fin r | i.1 < (0 : Fin (r + 1)).1}) from rfl,
        hempty, IntermediateField.adjoin_empty]
    · rw [eq_top_iff]; intro ⟨x, hx⟩ _
      let M : IntermediateField F' Ω := (TL' (Fin.last r)).map L'.val
      have hsub : L' ≤ M := by
        rw [IntermediateField.adjoin_le_iff]; rintro _ ⟨i, rfl⟩
        exact ⟨βL' i, IntermediateField.subset_adjoin F' _ ⟨i, i.2, rfl⟩, rfl⟩
      obtain ⟨z, hz, hzx⟩ := hsub hx
      exact (Subtype.ext hzx : z = ⟨x, hx⟩) ▸ hz
    · refine ⟨?_, ?_⟩
      · obtain ⟨⟨m, hm1, hpow⟩, _⟩ := hTEstep i
        refine ⟨m, hm1, ?_⟩
        have hmem := hTE_le_TL' i.1 (Nat.le_of_lt i.2) ((βE i) ^ m) hpow
        have heq : (⟨algebraMap E Ω ((βE i) ^ m), hE_le_L' _⟩ : L') = (βL' i) ^ m :=
          Subtype.ext (map_pow (algebraMap E Ω) (βE i) m)
        rwa [heq] at hmem
      · have hset : βL' '' {j : Fin r | j.1 < i.succ.1} =
            insert (βL' i) (βL' '' {j : Fin r | j.1 < i.castSucc.1}) := by
          ext x
          simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Fin.val_succ, Fin.val_castSucc]
          constructor
          · rintro ⟨j, hj, rfl⟩
            rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with h | h
            · exact Or.inl (congrArg βL' (Fin.ext h))
            · exact Or.inr ⟨j, h, rfl⟩
          · rintro (rfl | ⟨j, hj, rfl⟩)
            · exact ⟨i, Nat.lt_succ_self _, rfl⟩
            · exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
        apply le_antisymm
        · rw [show TL' i.succ = IntermediateField.adjoin F' (βL' '' {j : Fin r | j.1 < i.succ.1}) from rfl,
            hset, IntermediateField.adjoin_le_iff]
          rintro x (rfl | ⟨j, hj, rfl⟩)
          · exact IntermediateField.subset_adjoin F' _ (Or.inr rfl)
          · exact IntermediateField.subset_adjoin F' _ (Or.inl (IntermediateField.subset_adjoin F' _ ⟨j, hj, rfl⟩))
        · rw [IntermediateField.adjoin_le_iff]
          rintro x (hx | rfl)
          · exact IntermediateField.adjoin.mono F' _ _ (by rw [hset]; exact Set.subset_insert _ _) hx
          · exact IntermediateField.subset_adjoin F' _ ⟨i, Nat.lt_succ_self _, rfl⟩
  exact ⟨L', hE_le_L', hradL'⟩

/-- Helper for `Exercise 20.5`: given an opaque algebraically closed subfield `Kbar` of `Ω`
over which `tΩ = algebraMap K Ω RatFunc.X` is transcendental, derive `False` from a radical
extension `E : K` embedded in `Ω` over which `X^3 + t X + t` splits. -/
private theorem ex20_5_char2_not_solvable_over_kbar
    {Kbar E Ω : Type} [Field Kbar] [Field E] [Field Ω] [IsAlgClosed Kbar] [CharP Ω 2]
    [Algebra (ZMod 2) Kbar] [Algebra Kbar Ω]
    [Algebra (RatFunc (ZMod 2)) E] [Algebra E Ω] [Algebra (RatFunc (ZMod 2)) Ω]
    [IsScalarTower (RatFunc (ZMod 2)) E Ω]
    (hZ2 : ∀ a : ZMod 2,
      algebraMap Kbar Ω (algebraMap (ZMod 2) Kbar a) =
        algebraMap (RatFunc (ZMod 2)) Ω (algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) (Polynomial.C a)))
    (htΩ_trans : IsGarlingTranscendental Kbar (algebraMap (RatFunc (ZMod 2)) Ω RatFunc.X))
    (hradE : IsGarlingExtensionByRadicals (RatFunc (ZMod 2)) E)
    (hsplE : GarlingSplitsOver (RatFunc (ZMod 2)) E
      (Polynomial.X ^ 3 + Polynomial.C (RatFunc.X : RatFunc (ZMod 2)) * Polynomial.X +
        Polynomial.C (RatFunc.X : RatFunc (ZMod 2)))) :
    False := by
  classical
  let K := RatFunc (ZMod 2)
  let t : K := RatFunc.X
  let f : K[X] := Polynomial.X ^ 3 + Polynomial.C t * Polynomial.X + Polynomial.C t
  let tΩ : Ω := algebraMap K Ω t
  -- Build `F' = Kbar(tΩ) ≤ Ω` and map `ιKF' : K →+* F'`:
  let F' : IntermediateField Kbar Ω := IntermediateField.adjoin Kbar ({tΩ} : Set Ω)
  have hcharF' : ringChar F' = 2 := by
    have _ : CharP Kbar 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) Kbar).injective 2
    have _ : CharP F' 2 := charP_of_injective_algebraMap (algebraMap Kbar F').injective 2
    exact ringChar.eq F' 2
  have hK_le_F' : ∀ x : K, algebraMap K Ω x ∈ F' := by
    have htpow : ∀ m : ℕ, tΩ ^ m ∈ F' := by
      intro m
      induction m with
      | zero => simp [F'.one_mem]
      | succ k ih => rw [pow_succ]; exact F'.mul_mem ih (IntermediateField.subset_adjoin Kbar _ rfl)
    intro x
    rw [← RatFunc.num_div_denom x, map_div₀]
    have hpoly_mem : ∀ P : (ZMod 2)[X], algebraMap K Ω (algebraMap (ZMod 2)[X] K P) ∈ F' := by
      intro P
      induction P using Polynomial.induction_on' with
      | add p₁ p₂ ih₁ ih₂ => rw [map_add, map_add]; exact F'.add_mem ih₁ ih₂
      | monomial n a =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow, RatFunc.algebraMap_X]
        change algebraMap K Ω (algebraMap (ZMod 2)[X] K (Polynomial.C a)) * tΩ ^ n ∈ F'
        rw [← hZ2 a]
        exact F'.mul_mem (F'.algebraMap_mem (algebraMap (ZMod 2) Kbar a)) (htpow n)
    exact F'.div_mem (hpoly_mem x.num) (hpoly_mem x.denom)
  let ιKF' : K →+* F' :=
    { toFun := fun x => ⟨algebraMap K Ω x, hK_le_F' x⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  -- Transport radical tower `E : K` to a radical extension `L' : F'` inside `Ω`:
  obtain ⟨L', hE_le_L', hradL'⟩ :=
    lift_radical_tower_to_intermediate (E := E) (Ω := Ω) ιKF'
      (fun c => IsScalarTower.algebraMap_apply K E Ω c) hradE
  -- Apply Frobenius reduction + `not_char_dvd_finrank_of_radical_over_algClosed_ch20` (`q = 2`):
  obtain ⟨N', _, hradN', _, hsepN'⟩ :=
    frobenius_reduction_of_radical_extension_ch20 Nat.prime_two hcharF' hradL'
  have hnot2_N' : ¬ (2 ∣ Module.finrank F' N') :=
    not_char_dvd_finrank_of_radical_over_algClosed_ch20 (Kbar := Kbar) Nat.prime_two hcharF' hradN'
  -- Build `f' = X^3 + t' X + t'`, show `f'.Separable`, lift splitting to `N'`, apply `ex20_5_char2_odd_finrank_impossible`:
  let t' : F' := ⟨tΩ, IntermediateField.subset_adjoin Kbar _ rfl⟩
  let f' : F'[X] := f.map ιKF'
  have hf'_eq : f' = Polynomial.X ^ 3 + Polynomial.C t' * Polynomial.X + Polynomial.C t' := by
    simp [f', f, ιKF', t', tΩ]
  have hf'_sep : f'.Separable := by
    have _ : CharP Kbar 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) Kbar).injective 2
    have _ : CharP F' 2 := charP_of_injective_algebraMap (algebraMap Kbar F').injective 2
    have h2F' : (2 : F') = 0 := CharP.cast_eq_zero F' 2
    have ht'_ne0 : t' ≠ 0 := fun h0 =>
      htΩ_trans ⟨Polynomial.X, Polynomial.X_ne_zero, by
        rw [Polynomial.aeval_X]; exact congrArg Subtype.val h0⟩
    have hderiv : Polynomial.derivative f' = Polynomial.X ^ 2 + Polynomial.C t' := by
      rw [hf'_eq, Polynomial.derivative_add, Polynomial.derivative_add, Polynomial.derivative_X_pow,
        Polynomial.derivative_C_mul_X, Polynomial.derivative_C, add_zero]
      have h3F : ((3 : ℕ) : F') = 1 := by push_cast; linear_combination h2F'
      rw [h3F, map_one, one_mul]
    refine ⟨Polynomial.C t'⁻¹, -(Polynomial.C t'⁻¹ * Polynomial.X), ?_⟩
    rw [hderiv, hf'_eq]
    have hmul : Polynomial.C t'⁻¹ * Polynomial.C t' = 1 := by
      rw [← map_mul, inv_mul_cancel₀ ht'_ne0, map_one]
    linear_combination hmul
  have hsplN' : GarlingSplitsOver F' N' f' := by
    rcases hsplE with ⟨m, lam, α, hexp⟩
    have hαL' : ∀ j : Fin m, (⟨algebraMap E Ω (α j), hE_le_L' (α j)⟩ : L') ∈ N' := by
      intro j
      apply hsepN'
      have h1 : (f.map (algebraMap K E)).eval (α j) = 0 := by
        rw [hexp, Polynomial.eval_mul, Polynomial.eval_prod]
        exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) (by simp))
      have h1' : α j ^ 3 + algebraMap K E t * α j + algebraMap K E t = 0 := by
        simpa [f] using h1
      have h2 : algebraMap E Ω (α j) ^ 3 + tΩ * algebraMap E Ω (α j) + tΩ = 0 := by
        have := congrArg (algebraMap E Ω) h1'
        simpa [tΩ, IsScalarTower.algebraMap_apply K E Ω] using this
      exact separable_minpoly_of_cubic_trinomial_inj L'.val.toRingHom L'.val.injective t'
        (hf'_eq ▸ hf'_sep) ⟨algebraMap E Ω (α j), hE_le_L' (α j)⟩ h2
    exact ⟨m, ιKF' lam, fun j => ⟨⟨algebraMap E Ω (α j), hE_le_L' (α j)⟩, hαL' j⟩,
      garlingSplitsExplicit_lift_of_inj ιKF' (algebraMap E Ω)
        (L'.val.toRingHom.comp N'.val.toRingHom) (L'.val.injective.comp N'.val.injective)
        (by ext x; exact IsScalarTower.algebraMap_apply K E Ω x)
        hexp (fun j => ⟨⟨algebraMap E Ω (α j), hE_le_L' (α j)⟩, hαL' j⟩)
        (fun _ => rfl)⟩
  let _ : Algebra N' Ω := (L'.val.toRingHom.comp N'.val.toRingHom).toAlgebra
  have hst : IsScalarTower F' N' Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hfin_N' : IsFiniteExtension F' N' :=
    isFiniteExtension_of_isGarlingExtensionByRadicals (isGarlingExtensionByRadicals_of_notCharDvd hradN')
  have hfinM : Module.Finite F' N' := (isFiniteExtension_iff_moduleFinite F' N').mp hfin_N'
  rw [hf'_eq] at hsplN'
  have htΩ_trans' : IsGarlingTranscendental Kbar tΩ := htΩ_trans
  exact @ex20_5_char2_odd_finrank_impossible Kbar Ω N' _ _ _ _ _ tΩ htΩ_trans' _ _ hst hfinM
    hnot2_N' hsplN'

/-- Helper for `Exercise 20.5`: given a radical extension `E` of `K = RatFunc (ZMod 2)` over which
`f = X^3 + t X + t` splits, derive `False` inside any algebraically closed extension `Ω` of `E`. -/
private theorem ex20_5_char2_not_solvable_in_algClosed
    {E Ω : Type} [Field E] [Field Ω] [Algebra (RatFunc (ZMod 2)) E] [Algebra E Ω] [IsAlgClosed Ω]
    (hradE : IsGarlingExtensionByRadicals (RatFunc (ZMod 2)) E)
    (hsplE : GarlingSplitsOver (RatFunc (ZMod 2)) E
      (Polynomial.X ^ 3 + Polynomial.C (RatFunc.X : RatFunc (ZMod 2)) * Polynomial.X +
        Polynomial.C (RatFunc.X : RatFunc (ZMod 2)))) :
    False := by
  classical
  let K := RatFunc (ZMod 2)
  let t : K := RatFunc.X
  let _ : Algebra K Ω := RingHom.toAlgebra ((algebraMap E Ω).comp (algebraMap K E))
  have _ : IsScalarTower K E Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let _ : Algebra (ZMod 2) Ω := RingHom.toAlgebra ((algebraMap K Ω).comp (algebraMap (ZMod 2) K))
  have _ : IsScalarTower (ZMod 2) K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have _ : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) Ω).injective 2
  -- Algebraic closure `Kbar` of `ZMod 2` inside `Ω`:
  let Kbar : IntermediateField (ZMod 2) Ω := algebraicIntermediateField (ZMod 2) Ω
  have hKbar_alg : IsAlgebraicExtension (ZMod 2) Kbar := fun ⟨x, hx⟩ => by
    have ⟨g, hg0, hgx⟩ := hx
    refine ⟨g, hg0, ?_⟩
    apply Subtype.ext
    change Kbar.val (Polynomial.aeval (⟨x, hx⟩ : Kbar) g) = 0
    rw [← Polynomial.aeval_algHom_apply]
    exact hgx
  have hKbar_closed : IsAlgClosed Kbar := by
    refine IsAlgClosed.of_exists_root Kbar fun g hg_mon hg_irr => ?_
    have hdeg_pos : 0 < g.natDegree := hg_irr.natDegree_pos
    have hdeg : (g.map (algebraMap Kbar Ω)).degree ≠ 0 := by
      rw [Polynomial.degree_map_eq_of_injective (algebraMap Kbar Ω).injective,
        Polynomial.degree_eq_natDegree hg_mon.ne_zero]
      exact ne_of_gt (by exact_mod_cast hdeg_pos)
    obtain ⟨rΩ, hrΩ⟩ := IsAlgClosed.exists_root (g.map (algebraMap Kbar Ω)) hdeg
    have hr_alg_Kbar : IsGarlingAlgebraic Kbar rΩ := by
      refine ⟨g, hg_mon.ne_zero, ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]; exact hrΩ
    have hr_alg_Z2 : IsGarlingAlgebraic (ZMod 2) rΩ := by
      have h1 : IsAlgebraic Kbar rΩ := (isGarlingAlgebraic_iff Kbar rΩ).mp hr_alg_Kbar
      have _ : Algebra.IsAlgebraic (ZMod 2) Kbar := (isAlgebraicExtension_iff (ZMod 2) Kbar).mp hKbar_alg
      exact (isGarlingAlgebraic_iff (ZMod 2) rΩ).mpr (IsAlgebraic.restrictScalars (ZMod 2) h1)
    refine ⟨⟨rΩ, hr_alg_Z2⟩, ?_⟩
    apply (algebraMap Kbar Ω).injective
    rw [map_zero, ← Polynomial.eval_map_apply]
    exact hrΩ
  let _ : IsAlgClosed Kbar := hKbar_closed
  let tΩ : Ω := algebraMap K Ω t
  -- `tΩ` is transcendental over `Kbar`:
  have htΩ_trans : IsGarlingTranscendental Kbar tΩ := by
    intro halg
    have h1 : IsAlgebraic Kbar tΩ := (isGarlingAlgebraic_iff Kbar tΩ).mp halg
    have _ : Algebra.IsAlgebraic (ZMod 2) Kbar := (isAlgebraicExtension_iff (ZMod 2) Kbar).mp hKbar_alg
    have ht_alg_Z2 : IsGarlingAlgebraic (ZMod 2) tΩ :=
      (isGarlingAlgebraic_iff (ZMod 2) tΩ).mpr (IsAlgebraic.restrictScalars (ZMod 2) h1)
    obtain ⟨g, hg0, hg⟩ := ht_alg_Z2
    have hgt : Polynomial.aeval t g = 0 := by
      apply (algebraMap K Ω).injective
      change (IsScalarTower.toAlgHom (ZMod 2) K Ω) (Polynomial.aeval t g) = (algebraMap K Ω) 0
      rw [map_zero, ← Polynomial.aeval_algHom_apply]
      exact hg
    have hgt_eq : ∀ P : (ZMod 2)[X], Polynomial.aeval t P = algebraMap (ZMod 2)[X] K P := by
      intro P
      induction P using Polynomial.induction_on' with
      | add p₁ p₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂]
      | monomial n a =>
        rw [Polynomial.aeval_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
        rfl
    rw [hgt_eq g] at hgt
    exact hg0 (IsFractionRing.injective (ZMod 2)[X] K (hgt.trans (map_zero _).symm))
  exact ex20_5_char2_not_solvable_over_kbar (Kbar := Kbar) (fun _ => rfl) htΩ_trans hradE hsplE

/-- **Exercise 20.5, Positive-Characteristic Counterexample to Printed `(⇐)` (§20.2, printed p. 161;
`QUEUE.md` genuine textbook error hold):**
Over `K = RatFunc (ZMod 2) = ℤ_2(t)` (`ringChar K = 2 ≠ 3`), the cubic polynomial
`f = X^3 + t X + t ∈ K[X]` is irreducible of prime degree `3 ≠ char K`, and in every splitting
field `L : K` of `f` any two distinct roots `α, β` generate `L = K(α, β)` (since the third root is
`α + β`), **yet `f` is NOT solvable by radicals** over `K` (`¬ IsGarlingSolvableByRadicals f`). -/
theorem exercise_20_5_char_two_counterexample :
    let K := RatFunc (ZMod 2)
    let t : K := RatFunc.X
    let f : K[X] := Polynomial.X ^ 3 + Polynomial.C t * Polynomial.X + Polynomial.C t
    ringChar K = 2 ∧
    ringChar K ≠ 3 ∧
    Irreducible f ∧
    f.natDegree = 3 ∧
    (∀ (L : Type) [Field L] [Algebra K L],
      IsGarlingSplittingFieldExtension K L f →
      ∀ α ∈ garlingRootSet K L f, ∀ β ∈ garlingRootSet K L f, α ≠ β →
        IntermediateField.adjoin K ({α, β} : Set L) = ⊤) ∧
    ¬ IsGarlingSolvableByRadicals f := by
  classical
  intro K t f
  have _ : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have hcharK : ringChar K = 2 := ringChar.eq K 2
  have hf_mon : f.Monic := by
    dsimp [f]
    have hlt : (Polynomial.C t * Polynomial.X + Polynomial.C t).natDegree < 3 := by compute_degree!
    rw [add_assoc]
    exact Polynomial.monic_X_pow_add (Polynomial.degree_lt_iff_coeff_zero _ _ |>.mpr fun m hm =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  have hf_deg : f.natDegree = 3 := by dsimp [f]; compute_degree!
  have hirr_f : Irreducible f := ex20_5_cubic_irred_over_ratFunc (ZMod 2)
  have hgen_L : ∀ (L : Type) [Field L] [Algebra K L],
      IsGarlingSplittingFieldExtension K L f →
      ∀ α ∈ garlingRootSet K L f, ∀ β ∈ garlingRootSet K L f, α ≠ β →
        IntermediateField.adjoin K ({α, β} : Set L) = ⊤ := by
    intro L _ _ hsfL α hα β hβ hαβ
    have hsfLm := (isGarlingSplittingFieldExtension_iff K L f).mp hsfL
    let γ : L := -(α + β)
    have hα_root : (f.map (algebraMap K L)).eval α = 0 := by
      rwa [← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
    have hβ_root : (f.map (algebraMap K L)).eval β = 0 := by
      rwa [← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
    have hfac : f.map (algebraMap K L) =
        (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β) * (Polynomial.X - Polynomial.C γ) := by
      have hd1 : Polynomial.X - Polynomial.C α ∣ f.map (algebraMap K L) :=
        Polynomial.dvd_iff_isRoot.mpr hα_root
      rcases hd1 with ⟨q₁, hq₁⟩
      have hq₁_β : q₁.eval β = 0 := by
        have h1 := congrArg (Polynomial.eval β) hq₁
        rw [hβ_root, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
        exact (mul_eq_zero.mp h1.symm).resolve_left (sub_ne_zero.mpr hαβ.symm)
      rcases Polynomial.dvd_iff_isRoot.mpr hq₁_β with ⟨q₂, hq₂⟩
      have hq₁_eq : f.map (algebraMap K L) =
          (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β) * q₂ := by
        rw [hq₁, hq₂, mul_assoc]
      have hmon_f : (f.map (algebraMap K L)).Monic := hf_mon.map _
      have hmon_ab : ((Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)).Monic :=
        (Polynomial.monic_X_sub_C α).mul (Polynomial.monic_X_sub_C β)
      have hq₂_ne0 : q₂ ≠ 0 := fun h0 => hmon_f.ne_zero (by rw [hq₁_eq, h0, mul_zero])
      have hdeg_ab : ((Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)).natDegree = 2 := by
        rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero α) (Polynomial.X_sub_C_ne_zero β),
          Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]
      have hdeg_q₂ : q₂.natDegree = 1 := by
        have h1 := congrArg Polynomial.natDegree hq₁_eq
        rw [Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective, hf_deg,
          Polynomial.natDegree_mul hmon_ab.ne_zero hq₂_ne0, hdeg_ab] at h1
        omega
      have hlc_q₂ : q₂.leadingCoeff = 1 := by
        have h1 := congrArg Polynomial.leadingCoeff hq₁_eq
        rw [hmon_f.leadingCoeff, Polynomial.leadingCoeff_mul, hmon_ab.leadingCoeff, one_mul] at h1
        exact h1.symm
      have hq₂_form : q₂ = Polynomial.X + Polynomial.C (q₂.coeff 0) := by
        have h1 := Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.degree_le_of_natDegree_le hdeg_q₂.le)
        rw [show q₂.coeff 1 = 1 from by rw [← hdeg_q₂, Polynomial.coeff_natDegree, hlc_q₂],
          map_one, one_mul] at h1
        exact h1
      have hc2_f : (f.map (algebraMap K L)).coeff 2 = 0 := by simp [f]
      have hc2_rhs : ((Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β) *
          (Polynomial.X + Polynomial.C (q₂.coeff 0))).coeff 2 = q₂.coeff 0 - α - β := by
        have hexp : (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β) *
            (Polynomial.X + Polynomial.C (q₂.coeff 0)) =
            Polynomial.X ^ 3 + Polynomial.C (q₂.coeff 0 - α - β) * Polynomial.X ^ 2 +
              Polynomial.C (α * β - (α + β) * q₂.coeff 0) * Polynomial.X +
              Polynomial.C (α * β * q₂.coeff 0) := by
          simp only [map_sub, map_add, map_mul]; ring
        rw [hexp]
        simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          Polynomial.coeff_X, Polynomial.coeff_C]
        simp
      have hq0 : q₂.coeff 0 = α + β := by
        rw [hq₁_eq, hq₂_form, hc2_rhs] at hc2_f
        linear_combination hc2_f
      rw [hq₁_eq, hq₂_form, hq0]
      simp only [γ, map_neg, sub_neg_eq_add]
    rw [eq_top_iff]
    have hadj_top : Algebra.adjoin K (f.rootSet L) = ⊤ := hsfLm.adjoin_rootSet
    have hsub_alg : Algebra.adjoin K (f.rootSet L) ≤
        (IntermediateField.adjoin K ({α, β} : Set L)).toSubalgebra := by
      rw [Algebra.adjoin_le_iff]
      intro z hz
      have hzero : (f.map (algebraMap K L)).eval z = 0 := by
        have h1 := (Polynomial.mem_rootSet_of_ne hf_mon.ne_zero).mp hz
        rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at h1
      rw [hfac, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_sub,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_C, Polynomial.eval_C] at hzero
      rcases mul_eq_zero.mp hzero with h1 | h3
      · rcases mul_eq_zero.mp h1 with h1a | h1b
        · rw [sub_eq_zero.mp h1a]
          exact IntermediateField.subset_adjoin K _ (by simp)
        · rw [sub_eq_zero.mp h1b]
          exact IntermediateField.subset_adjoin K _ (by simp)
      · rw [sub_eq_zero.mp h3]
        exact neg_mem (add_mem (IntermediateField.subset_adjoin K _ (by simp))
          (IntermediateField.subset_adjoin K _ (by simp)))
    intro x _
    exact hsub_alg (hadj_top.symm ▸ Algebra.mem_top)
  refine ⟨hcharK, by omega, hirr_f, hf_deg, hgen_L, ?_⟩
  rintro ⟨E, fE, aE, hradE, hsplE⟩
  let _ : Field E := fE
  let _ : Algebra K E := aE
  exact ex20_5_char2_not_solvable_in_algClosed (E := E) (Ω := AlgebraicClosure E) hradE hsplE

/-- **Exercise 20.5, Repaired Characterization (§20.2, printed p. 161 / PDF p. 169; `QUEUE.md`):**
Under the natural `Theorem 17.3` guard `¬ (ringChar K ∣ |Γ_K(f)|)` (which holds automatically
whenever `CharZero K`, or `¬ (ringChar K ∣ p * (p - 1))`, or `p = 2` since `char K ≠ 2`), the
printed biconditional holds literally:
`IsGarlingSolvableByRadicals f ↔ ∀ α β ∈ garlingRootSet K L f, α ≠ β → K(α, β) = L`. -/
theorem exercise_20_5_repaired {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {p : ℕ} (hp : Nat.Prime p) (hchar : ringChar K ≠ p)
    {f : K[X]} (hirr : Irreducible f) (hdeg : f.natDegree = p)
    (hsf : IsGarlingSplittingFieldExtension K L f)
    (hchar_gal : ¬ (ringChar K ∣ Nat.card (GarlingPolyGaloisGroup K L f))) :
    IsGarlingSolvableByRadicals f ↔
      ∀ α ∈ garlingRootSet K L f, ∀ β ∈ garlingRootSet K L f, α ≠ β →
        IntermediateField.adjoin K ({α, β} : Set L) = ⊤ := by
  refine ⟨exercise_20_5_mp hp hchar hirr hdeg hsf, fun hgen => ?_⟩
  have hsol := (exercise_20_5_galois_iff hp hchar hirr hdeg hsf).mpr hgen
  have hf_gsep := (separable_of_irreducible_prime_deg_ne_char hp hchar hirr hdeg).2
  exact theorem_17_3 hf_gsep hsf hsol hchar_gal

theorem exercise_20_5_charZero {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [CharZero K] {p : ℕ} (hp : Nat.Prime p)
    {f : K[X]} (hirr : Irreducible f) (hdeg : f.natDegree = p)
    (hsf : IsGarlingSplittingFieldExtension K L f) :
    IsGarlingSolvableByRadicals f ↔
      ∀ α ∈ garlingRootSet K L f, ∀ β ∈ garlingRootSet K L f, α ≠ β →
        IntermediateField.adjoin K ({α, β} : Set L) = ⊤ := by
  have hchar : ringChar K ≠ p := by rw [ringChar.eq_zero]; exact hp.ne_zero.symm
  have hchar_gal : ¬ (ringChar K ∣ Nat.card (GarlingPolyGaloisGroup K L f)) := by
    rw [ringChar.eq_zero]
    intro h0
    have hsf_m := (isGarlingSplittingFieldExtension_iff K L f).mp hsf
    have _ : FiniteDimensional K L := Polynomial.IsSplittingField.finiteDimensional L f
    have _ : Finite (GarlingPolyGaloisGroup K L f) := inferInstance
    exact Nat.card_pos.ne' (zero_dvd_iff.mp h0)
  exact exercise_20_5_repaired hp hchar hirr hdeg hsf hchar_gal

/-! ## §20.3 The Galois group of a quintic (printed pp. 161–162 / PDF pp. 169–170)

We formalize:
1. The inline prose definition of the pentagon symmetry group `D₁₀` (`pentagonDihedral := s5D5`),
   its isomorphism `DihedralGroup 5 ≃* pentagonDihedral`, its order `10`, and the subgroup chain
   `C₅ ≤ D₁₀ ≤ W` (`s5C5`, `pentagonDihedral`, `garlingAffineGroup 5`) and `C₅, D₁₀ ≤ A₅`.
2. The unnumbered main-text 5-way classification of the Galois group of an irreducible quintic
   over `ℚ` (`section_20_3_quintic_galois_classification`): up to conjugacy in `Σ₅` (and hence
   up to isomorphism), `Γ_ℚ(f)` is one of `ℤ₅` (order `5`), `D₁₀` (order `10`), `W` (order `20`),
   `A₅` (order `60`), or `Σ₅` (order `120`), with solvability by radicals iff `|Γ_ℚ(f)| ∣ 20`
   and `Γ_ℚ(f) ⊆ A₅` iff `Δ(f)` is a rational square.
3. **`Exercise 20.6`** (printed p. 162, singular `Exercise`, DONE literally): if a quintic
   `f ∈ ℚ[x]` has Galois group containing `D₁₀` (proved in both abstract-subgroup and
   permutation-containment forms), then `f` is automatically irreducible and separable and the
   `10` pairwise sums `α_i + α_j` (`1 ≤ i < j ≤ 5`) are pairwise distinct.
4. All five concrete quintic realizations `(a)`–`(e)` in §20.3 (printed pp. 161–162):
   - `(a)` `x⁵ + x⁴ - 4x³ - 3x² + 3x + 1`: `Γ ≃* Multiplicative (ZMod 5)`, all `5` real roots,
     rational-square positive discriminant;
   - `(b)` `x⁵ - 5x + 12`: `Γ ≃* DihedralGroup 5` (`pentagonDihedral`), `Δ = 2¹² 5⁶ = (2⁶ 5³)²`,
     explicit pair-sum resolvent `g(x) = x¹⁰ + 15x⁶ - 132x⁵ - 100x² - 240x - 144 =
     (x⁵ + 5x³ + 10x² + 10x + 4)(x⁵ - 5x³ - 10x² + 30x - 36)` proved via `Chapter14.exercise_14_2_iii`
     Newton power sums, and exactly `1` real root;
   - `(c)` `x⁵ - 2`: `Γ ≃* garlingAffineGroup 5` (`W`, order `20`);
   - `(d)` `x⁵ + 20x + 16`: `Γ ≃* alternatingGroup (Fin 5)` (`A₅`, order `60`), `Δ = 2¹⁶ 5⁶ =
     (2⁸ 5³)²`, not solvable by radicals;
   - `(e)` `x⁵ - 4x + 2`: `Γ ≃* SigmaN 5` (`Σ₅`, order `120`), not solvable by radicals.
5. `exercise_20_3_p5_square_disc_witness`: pairing `(a)` (`5` real roots) and `(b)` (`1` real root)
   at `p = 5 = 4·1 + 1`, showing even rational-squareness of `Δ(f)` fails to distinguish the two
   cases when `p ≡ 1 (mod 4)`.
-/

/-! ### Pentagon dihedral group `D₁₀` and 5-way quintic classification (§20.3, printed p. 161) -/

/-- **§20.3 Inline Prose Definition (`D₁₀`, printed p. 161):**
The dihedral group of order `10` (the group of symmetries of a regular pentagon) realized as a
transitive subgroup of `Σ₅` (`s5D5 = (dihedralFinPermHom 4).range`). -/
def pentagonDihedral : Subgroup (SigmaN 5) :=
  s5D5

/-- Explicit isomorphism `DihedralGroup 5 ≃* pentagonDihedral`. -/
noncomputable def pentagonDihedralMulEquiv : DihedralGroup 5 ≃* pentagonDihedral :=
  MulEquiv.ofBijective (dihedralFinPermHom 4).rangeRestrict
    ⟨fun a b hab => dihedralFinPermHom_injective (by decide) (congrArg Subtype.val hab),
     (dihedralFinPermHom 4).rangeRestrict_surjective⟩

/-- `|D₁₀| = 10`. -/
theorem pentagonDihedral_card : Nat.card pentagonDihedral = 10 :=
  exercise_11_5_s5.1 1

/-- Every element of `D₁₀ ≤ Σ₅` is an even permutation (`D₁₀ ≤ A₅`). -/
theorem pentagonDihedral_le_alternatingGroup :
    pentagonDihedral ≤ alternatingGroup (Fin 5) := by
  rintro σ ⟨x, rfl⟩
  rw [Equiv.Perm.mem_alternatingGroup]
  cases x with
  | r k => fin_cases k <;> decide
  | sr k => fin_cases k <;> decide

/-- `C₅ ≤ A₅` (`s5C5 ≤ alternatingGroup (Fin 5)`). -/
theorem s5C5_le_alternatingGroup : s5C5 ≤ alternatingGroup (Fin 5) := by
  rw [s5C5, Subgroup.zpowers_le, Equiv.Perm.mem_alternatingGroup]
  decide

/-- `D₁₀ ≤ W = garlingAffineGroup 5` (rotations are `x ↦ x - k` and reflections are `x ↦ -x + k`). -/
theorem pentagonDihedral_le_garlingAffineGroup :
    (pentagonDihedral : Subgroup (Equiv.Perm (ZMod 5))) ≤ garlingAffineGroup 5 := by
  rintro σ ⟨x, rfl⟩
  cases x with
  | r k =>
    refine ⟨1, -k, trivial, Equiv.ext fun y : ZMod 5 => ?_⟩
    change dihedralZModPerm 5 (DihedralGroup.r k) y = (1 : ZMod 5) * y + (-k)
    rw [dihedralZModPerm_r]; ring
  | sr k =>
    refine ⟨-1, k, trivial, Equiv.ext fun y : ZMod 5 => ?_⟩
    change dihedralZModPerm 5 (DihedralGroup.sr k) y = ((-1 : (ZMod 5)ˣ) : ZMod 5) * y + k
    rw [dihedralZModPerm_sr, Units.val_neg, Units.val_one]; ring

/-- Chapter 11's `s5F20` coincides identically with Chapter 20's `garlingAffineGroup 5` (`W`). -/
theorem s5F20_eq_garlingAffineGroup :
    (s5F20 : Subgroup (Equiv.Perm (ZMod 5))) = garlingAffineGroup 5 := by
  ext σ
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u.1, u.2, trivial, Equiv.ext fun y : ZMod 5 => rfl⟩
  · rintro ⟨a, b, _, hσ⟩
    exact ⟨(a, b), hσ.symm ▸ Equiv.ext fun y : ZMod 5 => rfl⟩

/-- `s5C5 ≤ garlingAffineGroup 5` (`C₅ ≤ W`). -/
theorem s5C5_le_garlingAffineGroup :
    (s5C5 : Subgroup (Equiv.Perm (ZMod 5))) ≤ garlingAffineGroup 5 := by
  have hmem : (s5ShiftPerm : Equiv.Perm (ZMod 5)) ∈ garlingAffineGroup 5 := by
    refine ⟨1, 1, trivial, Equiv.ext fun y : ZMod 5 => ?_⟩
    change y + 1 = (1 : ZMod 5) * y + 1
    ring
  exact (Subgroup.zpowers_le (H := garlingAffineGroup 5)).mpr hmem

/-- Explicit isomorphism `Multiplicative (ZMod 5) ≃* s5C5`. -/
noncomputable def s5C5MulEquiv : Multiplicative (ZMod 5) ≃* s5C5 := by
  have hpow : ∀ a b : ZMod 5, s5ShiftPerm ^ (a + b).val = s5ShiftPerm ^ a.val * s5ShiftPerm ^ b.val := by
    intro a b
    fin_cases a <;> fin_cases b <;> decide
  have hinj : ∀ a b : ZMod 5, s5ShiftPerm ^ a.val = s5ShiftPerm ^ b.val → a = b := by
    intro a b h
    fin_cases a <;> fin_cases b <;> first | rfl | exact absurd h (by decide)
  let φ : Multiplicative (ZMod 5) →* s5C5 :=
    { toFun := fun k => ⟨s5ShiftPerm ^ (Multiplicative.toAdd k).val,
        Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _⟩
      map_one' := Subtype.ext (by change s5ShiftPerm ^ (0 : ZMod 5).val = 1; decide)
      map_mul' := fun a b => Subtype.ext (hpow (Multiplicative.toAdd a) (Multiplicative.toAdd b)) }
  have hφ_inj : Function.Injective φ := fun a b h => by
    have h1 := hinj (Multiplicative.toAdd a) (Multiplicative.toAdd b) (congrArg Subtype.val h)
    exact Multiplicative.toAdd.injective h1
  have hcard : Nat.card (Multiplicative (ZMod 5)) = Nat.card s5C5 := by
    change Nat.card (Multiplicative (ZMod 5)) = Nat.card (s5TransitiveModel 0)
    rw [exercise_11_5_s5.1 0]
    exact Nat.card_eq_fintype_card.trans (by decide)
  have _ : Finite s5C5 := inferInstance
  have hφ_surj : Function.Surjective φ := by
    have _ : Fintype (Multiplicative (ZMod 5)) := inferInstance
    have _ : Fintype s5C5 := Fintype.ofFinite s5C5
    exact (Fintype.bijective_iff_injective_and_card φ).mpr
      ⟨hφ_inj, by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard]⟩ |>.2
  exact MulEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩

/-- Helper: `garlingAffineGroup 5` is NOT contained in `alternatingGroup (Fin 5)`. -/
private theorem garlingAffineGroup_five_not_le_alternating :
    ¬ (garlingAffineGroup 5 : Subgroup (SigmaN 5)) ≤ alternatingGroup (Fin 5) := by
  have hu : IsUnit (2 : ZMod 5) := ⟨⟨2, 3, by decide, by decide⟩, rfl⟩
  let a2 : (ZMod 5)ˣ := ⟨2, 3, by decide, by decide⟩
  have hsign : Equiv.Perm.sign (affinePerm a2 (0 : ZMod 5) : SigmaN 5) ≠ 1 := by decide
  intro hle
  have hmem : (affinePerm a2 (0 : ZMod 5) : SigmaN 5) ∈ (garlingAffineGroup 5 : Subgroup (SigmaN 5)) :=
    ⟨a2, 0, trivial, rfl⟩
  exact hsign (Equiv.Perm.mem_alternatingGroup.mp (hle hmem))

/-- Helper: injectivity of `garlingRootLabellingPermHom e` from `Theorem 11.6`. -/
private theorem garlingRootLabellingPermHom_injective_ch20
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hsf : IsGarlingSplittingFieldExtension K L f)
    {n : ℕ} (e : Fin n ≃ garlingRootSet K L f) :
    Function.Injective (garlingRootLabellingPermHom e) := by
  intro σ τ h
  apply theorem_11_6 hsf
  ext r
  have h1 := congrArg (fun p : Equiv.Perm (Fin n) => (e (p (e.symm r))).1) h
  simpa [garlingRootLabellingPermHom_apply] using h1

/-- Helper: `⊤ : Subgroup (SigmaN 5)` is NOT contained in `alternatingGroup (Fin 5)`. -/
private theorem top_not_le_alternating_five :
    ¬ (⊤ : Subgroup (SigmaN 5)) ≤ alternatingGroup (Fin 5) := by
  intro hle
  have hev := Equiv.Perm.mem_alternatingGroup.mp (hle (Subgroup.mem_top (Equiv.swap (0 : Fin 5) 1)))
  exact absurd hev (by decide)

/-- Helper: conjugacy in `SigmaN 5` preserves membership in `alternatingGroup (Fin 5)` (since `A₅ ⊴ Σ₅`). -/
private theorem isConjugateSubgroup_le_alternating_iff {H₁ H₂ : Subgroup (SigmaN 5)}
    (hconj : IsConjugateSubgroup H₁ H₂) :
    H₁ ≤ alternatingGroup (Fin 5) ↔ H₂ ≤ alternatingGroup (Fin 5) := by
  rcases hconj with ⟨g, rfl⟩
  constructor
  · rintro hle _ ⟨σ, hσ, rfl⟩
    exact Subgroup.Normal.conj_mem inferInstance σ (hle hσ) g
  · intro hle σ hσ
    have h1 : g * σ * g⁻¹ ∈ alternatingGroup (Fin 5) := hle ⟨σ, hσ, rfl⟩
    have h2 : g⁻¹ * (g * σ * g⁻¹) * g ∈ alternatingGroup (Fin 5) := by
      simpa using Subgroup.Normal.conj_mem inferInstance (g * σ * g⁻¹) h1 g⁻¹
    simpa [mul_assoc] using h2

/-- Helper: conjugacy of subgroups induces a `MulEquiv`. -/
private theorem mulEquiv_of_isConjugateSubgroup {G : Type*} [Group G] {H₁ H₂ : Subgroup G}
    (hconj : IsConjugateSubgroup H₁ H₂) : Nonempty (H₁ ≃* H₂) := by
  rcases hconj with ⟨g, rfl⟩
  exact ⟨MulEquiv.subgroupMap (MulAut.conj g) H₁⟩

/-- **§20.3 Unnumbered Main-Text Classification Theorem (printed p. 161 / PDF p. 169):**
Let `f ∈ ℚ[x]` be an irreducible quintic (`f.natDegree = 5`) with splitting field `L : ℚ`. Then:
1. `f` is separable (`5` distinct roots in `L`), and for every root-labelling bijection
   `e : Fin 5 ≃ garlingRootSet ℚ L f`, the permutation Galois group
   `H = (garlingRootLabellingPermHom e).range ≤ Σ₅` is conjugate in `Σ₅` to a **unique** one of
   the five transitive subgroups `s5C5` (`ℤ₅`, order `5`), `pentagonDihedral` (`D₁₀`, order `10`),
   `garlingAffineGroup 5` (`W`, order `20`), `alternatingGroup (Fin 5)` (`A₅`, order `60`), or
   `⊤` (`Σ₅`, order `120`).
2. Consequently, `Γ_ℚ(f)` is isomorphic to one of `Multiplicative (ZMod 5)`, `DihedralGroup 5`,
   `garlingAffineGroup 5`, `alternatingGroup (Fin 5)`, or `SigmaN 5`, and `|Γ_ℚ(f)| ∈ {5, 10, 20, 60, 120}`.
3. `f` is solvable by radicals over `ℚ` iff `Γ_ℚ(f)` is soluble iff `|Γ_ℚ(f)| ∣ 20`
   (i.e. `|Γ_ℚ(f)| ∈ {5, 10, 20}`).
4. `garlingDiscriminant f` is a rational square (`∃ d : ℚ, d ^ 2 = garlingDiscriminant f`) iff
   `|Γ_ℚ(f)| ∈ {5, 10, 60}` (iff `H ≤ A₅`). -/
theorem section_20_3_quintic_galois_classification
    {L : Type u} [Field L] [Algebra ℚ L] {f : ℚ[X]}
    (hirr : Irreducible f) (hdeg : f.natDegree = 5)
    (hsf : IsGarlingSplittingFieldExtension ℚ L f) :
    let Γ := GarlingPolyGaloisGroup ℚ L f
    f.Separable ∧
    Nonempty (Fin 5 ≃ garlingRootSet ℚ L f) ∧
    (∀ e : Fin 5 ≃ garlingRootSet ℚ L f,
      ∃! i : Fin 5, IsConjugateSubgroup (s5TransitiveModel i) (garlingRootLabellingPermHom e).range) ∧
    (Nonempty (Γ ≃* Multiplicative (ZMod 5)) ∨
      Nonempty (Γ ≃* DihedralGroup 5) ∨
      Nonempty (Γ ≃* garlingAffineGroup 5) ∨
      Nonempty (Γ ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (Γ ≃* SigmaN 5)) ∧
    (IsGarlingSolvableByRadicals f ↔ IsGarlingSoluble Γ) ∧
    (IsGarlingSoluble Γ ↔ Nat.card Γ ∣ 20) ∧
    ((∃ d : ℚ, d ^ 2 = garlingDiscriminant f) ↔
      Nat.card Γ = 5 ∨ Nat.card Γ = 10 ∨ Nat.card Γ = 60) := by
  classical
  intro Γ
  have hf_sep : f.Separable := hirr.separable
  have hf_gsep : IsGarlingSeparablePoly f :=
    ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly f).mp hf_sep).2.2
  have hsf_m := (isGarlingSplittingFieldExtension_iff ℚ L f).mp hsf
  have hfin_roots : (garlingRootSet ℚ L f).Finite := by
    have hsub : garlingRootSet ℚ L f ⊆ ((f.map (algebraMap ℚ L)).roots.toFinset : Set L) := by
      intro α hα
      change Polynomial.aeval α f = 0 at hα
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots
        (Polynomial.map_ne_zero hirr.ne_zero), Polynomial.IsRoot.def]
      rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at hα
    exact (Finset.finite_toSet _).subset hsub
  have _ : Finite (garlingRootSet ℚ L f) := hfin_roots.to_subtype
  have hcard_roots : Nat.card (garlingRootSet ℚ L f) = 5 := by
    rw [Nat.card_coe_set_eq, ncard_garlingRootSet_eq_natDegree_of_separable hf_sep hsf, hdeg]
  have he_nonempty : Nonempty (Fin 5 ≃ garlingRootSet ℚ L f) :=
    ⟨(Finite.equivFinOfCardEq hcard_roots).symm⟩
  have htrans : ∀ e : Fin 5 ≃ garlingRootSet ℚ L f,
      SubgroupActsTransitively (garlingRootLabellingPermHom e).range := by
    intro e i j
    obtain ⟨σ, hσ⟩ := corollary_2_to_theorem_7_5_algEquiv hirr hsf (e i).2 (e j).2
    refine ⟨garlingRootLabellingPermHom e σ, ⟨σ, rfl⟩, ?_⟩
    apply e.injective
    apply Subtype.ext
    simpa [garlingRootLabellingPermHom_apply] using hσ
  have huniq : ∀ e : Fin 5 ≃ garlingRootSet ℚ L f,
      ∃! i : Fin 5, IsConjugateSubgroup (s5TransitiveModel i) (garlingRootLabellingPermHom e).range :=
    fun e => exercise_11_5_s5.2.2.2 _ (htrans e)
  obtain ⟨e⟩ := he_nonempty
  obtain ⟨i, hconj_i, _⟩ := huniq e
  let φ := garlingRootLabellingPermHom e
  have hφ_inj : Function.Injective φ := garlingRootLabellingPermHom_injective_ch20 hsf e
  let eΓH : Γ ≃* φ.range :=
    MulEquiv.ofBijective φ.rangeRestrict
      ⟨fun a b h => hφ_inj (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  obtain ⟨eModel⟩ := mulEquiv_of_isConjugateSubgroup hconj_i
  let eΓModel : Γ ≃* s5TransitiveModel i := eΓH.trans eModel.symm
  have hcard_Γ : Nat.card Γ = (![5, 10, 20, 60, 120] : Fin 5 → ℕ) i := by
    rw [Nat.card_congr eΓModel.toEquiv, exercise_11_5_s5.1 i]
  have hsol_W : IsGarlingSoluble (garlingAffineGroup 5) :=
    garlingAffineGroup_soluble (by decide : Nat.Prime 5)
  have hsol_C5 : IsGarlingSoluble s5C5 := by
    have hsub : IsGarlingSoluble ((s5C5 : Subgroup (Equiv.Perm (ZMod 5))).subgroupOf (garlingAffineGroup 5)) :=
      theorem_17_2_i hsol_W _
    let eSub : s5C5 ≃* (s5C5 : Subgroup (Equiv.Perm (ZMod 5))).subgroupOf (garlingAffineGroup 5) :=
      { toFun := fun x => ⟨⟨x.1, s5C5_le_garlingAffineGroup x.2⟩, x.2⟩
        invFun := fun x => ⟨x.1.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    exact (isGarlingSoluble_congr eSub).mpr hsub
  have hsol_D10 : IsGarlingSoluble pentagonDihedral := by
    have hsub : IsGarlingSoluble ((pentagonDihedral : Subgroup (Equiv.Perm (ZMod 5))).subgroupOf (garlingAffineGroup 5)) :=
      theorem_17_2_i hsol_W _
    let eSub : pentagonDihedral ≃* (pentagonDihedral : Subgroup (Equiv.Perm (ZMod 5))).subgroupOf (garlingAffineGroup 5) :=
      { toFun := fun x => ⟨⟨x.1, pentagonDihedral_le_garlingAffineGroup x.2⟩, x.2⟩
        invFun := fun x => ⟨x.1.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    exact (isGarlingSoluble_congr eSub).mpr hsub
  have h5way : Nonempty (Γ ≃* Multiplicative (ZMod 5)) ∨
      Nonempty (Γ ≃* DihedralGroup 5) ∨
      Nonempty (Γ ≃* garlingAffineGroup 5) ∨
      Nonempty (Γ ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (Γ ≃* SigmaN 5) := by
    fin_cases i
    · exact Or.inl ⟨eΓModel.trans s5C5MulEquiv.symm⟩
    · exact Or.inr (Or.inl ⟨eΓModel.trans pentagonDihedralMulEquiv.symm⟩)
    · refine Or.inr (Or.inr (Or.inl ⟨eΓModel.trans ?_⟩))
      exact MulEquiv.subgroupCongr s5F20_eq_garlingAffineGroup
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨eΓModel⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨eΓModel.trans Subgroup.topEquiv⟩)))
  have hrad_iff_sol : IsGarlingSolvableByRadicals f ↔ IsGarlingSoluble Γ := by
    constructor
    · rintro ⟨E, fE, aE, hrad, hspl⟩
      let _ : Field E := fE
      let _ : Algebra ℚ E := aE
      obtain ⟨r, T, β, n, h0, hlast, hchar, hstep⟩ :=
        isGarlingRadicalExtensionNotCharDvd_of_charZero hrad
      exact theorem_17_6 h0 hlast hstep hchar hspl hsf
    · intro hsol
      have hchar_ndvd : ¬ (ringChar ℚ ∣ Nat.card Γ) := by
        rw [ringChar.eq_zero]
        intro h0
        have _ : FiniteDimensional ℚ L := Polynomial.IsSplittingField.finiteDimensional L f
        have _ : Finite Γ := inferInstance
        exact Nat.card_pos.ne' (zero_dvd_iff.mp h0)
      exact theorem_17_3 hf_gsep hsf hsol hchar_ndvd
  have hsol_iff_dvd : IsGarlingSoluble Γ ↔ Nat.card Γ ∣ 20 := by
    rw [isGarlingSoluble_congr eΓModel, hcard_Γ]
    fin_cases i
    · exact ⟨fun _ => by decide, fun _ => hsol_C5⟩
    · exact ⟨fun _ => by decide, fun _ => hsol_D10⟩
    · let eF20W : s5F20 ≃* garlingAffineGroup 5 :=
        { toFun := fun x => ⟨x.1, s5F20_eq_garlingAffineGroup ▸ x.2⟩
          invFun := fun x => ⟨x.1, s5F20_eq_garlingAffineGroup.symm ▸ x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_mul' := fun _ _ => rfl }
      have hsol_F20 : IsGarlingSoluble s5F20 := (isGarlingSoluble_congr eF20W).mpr hsol_W
      exact ⟨fun _ => by decide, fun _ => hsol_F20⟩
    · have hnsol : ¬ IsGarlingSoluble (alternatingGroup (Fin 5)) :=
        (section_17_1_alternating_simple_and_not_soluble (le_refl 5)).2.2.2.1
      exact ⟨fun h => absurd h hnsol, fun hd => absurd hd (by decide)⟩
    · have hnsol : ¬ IsGarlingSoluble (⊤ : Subgroup (SigmaN 5)) := fun h =>
        (corollary_to_theorem_17_2 (le_refl 5)).1 ((isGarlingSoluble_congr Subgroup.topEquiv).mp h)
      exact ⟨fun h => absurd h hnsol, fun hd => absurd hd (by decide)⟩
  have hdisc_iff : (∃ d : ℚ, d ^ 2 = garlingDiscriminant f) ↔
      Nat.card Γ = 5 ∨ Nat.card Γ = 10 ∨ Nat.card Γ = 60 := by
    have hchar2 : ringChar ℚ ≠ 2 := by rw [ringChar.eq_zero]; decide
    have h14 := theorem_14_1 hchar2 f hsf
    have hΔ_ne0 : garlingDiscriminant f ≠ 0 := fun h0 => by
      have hrep := h14.1 h0
      rcases hsf.1 with ⟨m, c, α, hexp⟩
      exact ((injective_roots_iff_separable_and_not_repeated hirr.ne_zero hexp).2.mpr hrep)
        ((injective_roots_iff_separable_and_not_repeated hirr.ne_zero hexp).1.mpr hf_sep)
    let e' : Fin f.natDegree ≃ garlingRootSet ℚ L f := (finCongr hdeg).trans e
    have hsign_eq : ∀ σ : Γ,
        Equiv.Perm.sign (garlingRootLabellingPermHom e' σ) = Equiv.Perm.sign (φ σ) := by
      intro σ
      have hconj : garlingRootLabellingPermHom e' σ = (finCongr hdeg).symm.permCongr (φ σ) := by
        apply Equiv.ext; intro k
        apply e'.injective
        change e' (garlingRootLabellingPermHom e' σ k) = e' (((finCongr hdeg).symm.permCongr (φ σ)) k)
        apply Subtype.ext
        rw [garlingRootLabellingPermHom_apply]
        simp only [Equiv.permCongr_apply, Equiv.symm_symm, e', Equiv.trans_apply, Equiv.apply_symm_apply]
        exact (garlingRootLabellingPermHom_apply e σ (finCongr hdeg k)).symm
      rw [hconj, Equiv.Perm.sign_permCongr]
    have hsq_iff_le : (∃ d : ℚ, d ^ 2 = garlingDiscriminant f) ↔
        φ.range ≤ alternatingGroup (Fin 5) := by
      constructor
      · intro hsq
        rintro _ ⟨σ, rfl⟩
        rw [Equiv.Perm.mem_alternatingGroup, ← hsign_eq σ, ← Equiv.Perm.mem_alternatingGroup]
        exact (h14.2.1 hΔ_ne0 hsq).2 e' σ
      · intro hle
        by_contra hnsq
        obtain ⟨_, _, _, _, hall⟩ := h14.2.2 hnsq
        exact (hall e').1 fun σ => by
          rw [Equiv.Perm.mem_alternatingGroup, hsign_eq σ, ← Equiv.Perm.mem_alternatingGroup]
          exact hle ⟨σ, rfl⟩
    rw [hsq_iff_le, ← isConjugateSubgroup_le_alternating_iff hconj_i, hcard_Γ]
    fin_cases i
    · exact ⟨fun _ => Or.inl rfl, fun _ => s5C5_le_alternatingGroup⟩
    · exact ⟨fun _ => Or.inr (Or.inl rfl), fun _ => pentagonDihedral_le_alternatingGroup⟩
    · dsimp [s5TransitiveModel]
      rw [show s5F20 = (garlingAffineGroup 5 : Subgroup (SigmaN 5)) from s5F20_eq_garlingAffineGroup]
      exact ⟨fun h => absurd h garlingAffineGroup_five_not_le_alternating, by decide⟩
    · exact ⟨fun _ => Or.inr (Or.inr rfl), fun _ => le_rfl⟩
    · exact ⟨fun h => absurd h top_not_le_alternating_five, by decide⟩
  exact ⟨hf_sep, ⟨e⟩, huniq, h5way, hrad_iff_sol, hsol_iff_dvd, hdisc_iff⟩

/-! ### Exercise 20.6 (§20.3, printed p. 162 / PDF p. 170) -/

/-- Finite partition lemma on `ZMod 5 \ {4}`. -/
private theorem zmod5_four_distinct_partition (a b c d : ZMod 5)
    (ha4 : a ≠ 4) (hb4 : b ≠ 4) (hc4 : c ≠ 4) (hd4 : d ≠ 4)
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) ∧ ((c = 2 ∧ d = 3) ∨ (c = 3 ∧ d = 2)) ∨
     ((a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)) ∧ ((c = 0 ∧ d = 1) ∨ (c = 1 ∧ d = 0)) ∨
     ((a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0)) ∧ ((c = 1 ∧ d = 3) ∨ (c = 3 ∧ d = 1)) ∨
     ((a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1)) ∧ ((c = 0 ∧ d = 2) ∨ (c = 2 ∧ d = 0)) ∨
     ((a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0)) ∧ ((c = 1 ∧ d = 2) ∨ (c = 2 ∧ d = 1)) ∨
     ((a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)) ∧ ((c = 0 ∧ d = 3) ∨ (c = 3 ∧ d = 0))) := by
  have h4 : ∀ x : ZMod 5, x ≠ 4 → x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
    intro x hx
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact absurd rfl hx
  rcases h4 a ha4 with rfl | rfl | rfl | rfl <;>
  (rcases h4 b hb4 with rfl | rfl | rfl | rfl <;>
   first | exact absurd rfl hab |
     (rcases h4 c hc4 with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hac | exact absurd rfl hbc |
        (rcases h4 d hd4 with rfl | rfl | rfl | rfl <;>
         first | exact absurd rfl hcd | exact absurd rfl had | exact absurd rfl hbd | simp)))

/-- Helper for `Exercise 20.6`: any quintic `f ∈ ℚ[x]` whose Galois group contains an element `σ`
of order `5` is automatically irreducible and separable, and the `10` pairwise root sums
`α_i + α_j` (`1 ≤ i < j ≤ 5`) are pairwise distinct. -/
private theorem quintic_pair_sums_distinct_of_five_cycle
    {L : Type u} [Field L] [Algebra ℚ L] {f : ℚ[X]} (hdeg : f.natDegree = 5)
    (hsf : IsGarlingSplittingFieldExtension ℚ L f)
    (σ : GarlingPolyGaloisGroup ℚ L f) (hord : orderOf σ = 5) :
    Irreducible f ∧
    f.Separable ∧
    Nonempty (Fin 5 ≃ garlingRootSet ℚ L f) ∧
    ∀ (e : Fin 5 ≃ garlingRootSet ℚ L f) (i j k l : Fin 5),
      i < j → k < l → (e i : L) + (e j : L) = (e k : L) + (e l : L) → i = k ∧ j = l := by
  classical
  have hf0 : f ≠ 0 := fun h0 => by simp [h0] at hdeg
  have hsf_m := (isGarlingSplittingFieldExtension_iff ℚ L f).mp hsf
  have _ : FiniteDimensional ℚ L := Polynomial.IsSplittingField.finiteDimensional L f
  have _ : Finite (garlingRootSet ℚ L f) := by
    have hsub : {α : L | Polynomial.aeval α f = 0} ⊆ ((f.map (algebraMap ℚ L)).roots.toFinset : Set L) := by
      intro α hα
      change Polynomial.aeval α f = 0 at hα
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots
        (Polynomial.map_ne_zero hf0), Polynomial.IsRoot.def]
      rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at hα
    exact Set.Finite.to_subtype ((Finset.finite_toSet _).subset hsub)
  -- `σ` acts faithfully on `garlingRootSet ℚ L f` (`Theorem 11.6`), forcing `|roots| = 5`:
  have hperm_ord : orderOf (garlingRootPermHom ℚ L f σ) = 5 := by
    rw [orderOf_injective (garlingRootPermHom ℚ L f) (theorem_11_6 hsf) σ, hord]
  have h5_dvd_perm : 5 ∣ Nat.card (Equiv.Perm (garlingRootSet ℚ L f)) := by
    rw [← hperm_ord]; exact orderOf_dvd_natCard _
  rw [Nat.card_perm] at h5_dvd_perm
  have hcard_le5 : Nat.card (garlingRootSet ℚ L f) ≤ 5 := by
    have _ : Fintype (garlingRootSet ℚ L f) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card]
    let emb : garlingRootSet ℚ L f ↪ (f.map (algebraMap ℚ L)).roots.toFinset :=
      ⟨fun r => ⟨r.1, by
        simp only [Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.map_ne_zero hf0),
          Polynomial.IsRoot.def]
        have hr : Polynomial.aeval r.1 f = 0 := r.2
        rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at hr⟩,
       fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h)⟩
    calc Fintype.card (garlingRootSet ℚ L f)
        ≤ Fintype.card (f.map (algebraMap ℚ L)).roots.toFinset := Fintype.card_le_of_injective emb emb.injective
      _ = (f.map (algebraMap ℚ L)).roots.toFinset.card := Fintype.card_coe _
      _ ≤ (f.map (algebraMap ℚ L)).roots.card := Multiset.toFinset_card_le _
      _ ≤ (f.map (algebraMap ℚ L)).natDegree := Polynomial.card_roots' _
      _ = 5 := by rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ L).injective, hdeg]
  have hcard_eq5 : Nat.card (garlingRootSet ℚ L f) = 5 := by
    by_contra hne
    have hlt : Nat.card (garlingRootSet ℚ L f) ≤ 4 := by omega
    have hdvd24 : (Nat.card (garlingRootSet ℚ L f)).factorial ∣ 24 :=
      Nat.factorial_dvd_factorial hlt
    exact absurd (dvd_trans h5_dvd_perm hdvd24) (by decide)
  have hf_sep : f.Separable := by
    rcases hsf.1 with ⟨m, c, α, hexp⟩
    have hm5 : m = 5 := by
      have h1 := (garlingSplitsExplicit_props hf0 hexp).2.2.1
      rwa [garlingDegree, hdeg] at h1
    subst hm5
    have hα_mem : ∀ i : Fin 5, α i ∈ garlingRootSet ℚ L f := fun i => by
      change Polynomial.aeval (α i) f = 0
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hexp, Polynomial.eval_mul, Polynomial.eval_prod]
      exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) (by simp))
    have hα_surj : Function.Surjective (fun i : Fin 5 => (⟨α i, hα_mem i⟩ : garlingRootSet ℚ L f)) := by
      rintro ⟨r, hr⟩
      have hr0 : (f.map (algebraMap ℚ L)).eval r = 0 := by
        rwa [← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
      rw [hexp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod] at hr0
      have hc0 : algebraMap ℚ L c ≠ 0 := by
        have hcne : c ≠ 0 := (garlingSplitsExplicit_props hf0 hexp).1 ▸ Polynomial.leadingCoeff_ne_zero.mpr hf0
        exact (map_ne_zero _).mpr hcne
      obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp ((mul_eq_zero.mp hr0).resolve_left hc0)
      exact ⟨i, Subtype.ext (sub_eq_zero.mp (by simpa using hi)).symm⟩
    have _ : Fintype (garlingRootSet ℚ L f) := Fintype.ofFinite _
    have hα_inj' : Function.Injective (fun i : Fin 5 => (⟨α i, hα_mem i⟩ : garlingRootSet ℚ L f)) :=
      (Fintype.bijective_iff_surjective_and_card _).mpr
        ⟨hα_surj, by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard_eq5]⟩ |>.1
    have hα_inj : Function.Injective α := fun i j hij => hα_inj' (Subtype.ext hij)
    exact (injective_roots_iff_separable_and_not_repeated hf0 hexp).1.mp hα_inj
  -- Pick any root `r₀` and label the 5 roots along the `σ`-orbit `b k = (σ ^ k.val) r₀`:
  have hnonempty : Nonempty (garlingRootSet ℚ L f) := (Nat.card_pos_iff.mp (by omega)).1
  obtain ⟨r₀⟩ := hnonempty
  have hσ_pow5 : σ ^ 5 = 1 := hord ▸ pow_orderOf_eq_one σ
  let b : ZMod 5 → garlingRootSet ℚ L f := fun k =>
    ⟨(σ ^ k.val) r₀.1, by
      change Polynomial.aeval ((σ ^ k.val).toAlgHom r₀.1) f = 0
      rw [Polynomial.aeval_algHom_apply]
      have hr0 : Polynomial.aeval r₀.1 f = 0 := r₀.2
      rw [hr0, map_zero]⟩
  have hb_step : ∀ k : ZMod 5, σ (b k).1 = (b (k + 1)).1 := by
    intro k
    fin_cases k
    · change σ ((σ ^ 0) r₀.1) = (σ ^ 1) r₀.1; simp
    · change σ ((σ ^ 1) r₀.1) = (σ ^ 2) r₀.1; simp [pow_succ']
    · change σ ((σ ^ 2) r₀.1) = (σ ^ 3) r₀.1; simp [pow_succ']
    · change σ ((σ ^ 3) r₀.1) = (σ ^ 4) r₀.1; simp [pow_succ']
    · change σ ((σ ^ 4) r₀.1) = (σ ^ 0) r₀.1
      have h5 : (σ ^ 5) r₀.1 = r₀.1 := by rw [hσ_pow5]; rfl
      simpa [pow_succ'] using h5
  have hb_inj : Function.Injective b := by
    intro k₁ k₂ h12
    by_contra hne
    have hfix_r0 : σ r₀.1 = r₀.1 := by
      have hdiff : ((σ ^ (k₁ - k₂).val) r₀.1) = r₀.1 := by
        have hstep_n : ∀ (n : ℕ) (x : ZMod 5), (σ ^ n) (b x).1 = (b (x + n)).1 := by
          intro n
          induction n with
          | zero => intro x; simp
          | succ n ih =>
            intro x
            rw [pow_succ', AlgEquiv.mul_apply, ih, hb_step]
            congr 2; push_cast; ring
        have h1 : (b (k₂ + (k₁ - k₂))).1 = (b k₂).1 := by
          have : k₂ + (k₁ - k₂) = k₁ := by ring
          rw [this, h12]
        have h2 : (σ ^ (k₁ - k₂).val) (b k₂).1 = (b k₂).1 := by
          rw [hstep_n, show ((k₁ - k₂).val : ZMod 5) = k₁ - k₂ from ZMod.natCast_zmod_val _, h1]
        have h3 := congrArg (σ ^ (5 - k₂.val)) h2
        have hcomm : (σ ^ (5 - k₂.val)) ((σ ^ (k₁ - k₂).val) (b k₂).1) =
            (σ ^ (k₁ - k₂).val) ((σ ^ (5 - k₂.val)) (b k₂).1) := by
          change ((σ ^ (5 - k₂.val)) * (σ ^ (k₁ - k₂).val)) (b k₂).1 =
            ((σ ^ (k₁ - k₂).val) * (σ ^ (5 - k₂.val))) (b k₂).1
          rw [← pow_add, ← pow_add, add_comm]
        rw [hcomm] at h3
        have hback : (σ ^ (5 - k₂.val)) (b k₂).1 = r₀.1 := by
          change ((σ ^ (5 - k₂.val)) * (σ ^ k₂.val)) r₀.1 = r₀.1
          rw [← pow_add, Nat.sub_add_cancel (ZMod.val_lt k₂).le, hσ_pow5]; rfl
        rwa [hback] at h3
      -- Since `k₁ - k₂ ≠ 0` in `ZMod 5`, `(k₁ - k₂)⁻¹` lifts to `t` with `t * m ≡ 1 (mod 5)`:
      have hex_inv : ∃ t : ℕ, (t * (k₁ - k₂).val) % 5 = 1 := by
        have hm_ne : (k₁ - k₂) ≠ 0 := sub_ne_zero.mpr hne
        have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
        refine ⟨(k₁ - k₂)⁻¹.val, ?_⟩
        have hmul : (((k₁ - k₂)⁻¹.val * (k₁ - k₂).val : ℕ) : ZMod 5) = 1 := by
          push_cast; simp [inv_mul_cancel₀ hm_ne]
        have hval : (((k₁ - k₂)⁻¹.val * (k₁ - k₂).val) % 5) = (1 : ZMod 5).val := by
          rw [← ZMod.val_natCast, hmul]
        exact hval
      obtain ⟨t, ht⟩ := hex_inv
      have hpow_fix : ∀ q : ℕ, (σ ^ (q * (k₁ - k₂).val)) r₀.1 = r₀.1 := by
        intro q
        induction q with
        | zero => simp
        | succ q ih =>
          rw [Nat.succ_mul, add_comm, pow_add, AlgEquiv.mul_apply, ih, hdiff]
      have h1 := hpow_fix t
      rw [← Nat.div_add_mod (t * (k₁ - k₂).val) 5, ht, pow_add, pow_mul, hσ_pow5, one_pow,
        one_mul, pow_one] at h1
      exact h1
    -- If `σ r₀ = r₀`, then `σ` permutes the remaining `4` roots, forcing `σ^24 = 1`, contradicting `ord(σ) = 5`!
    let S4 := {r : garlingRootSet ℚ L f // r ≠ r₀}
    have _ : Fintype (garlingRootSet ℚ L f) := Fintype.ofFinite _
    have _ : Fintype S4 := inferInstance
    have hcard_S4 : Fintype.card S4 = 4 := by
      have h5 : Fintype.card (garlingRootSet ℚ L f) = 5 := by
        rw [← Nat.card_eq_fintype_card, hcard_eq5]
      have h1 := Fintype.card_subtype_compl (fun r : garlingRootSet ℚ L f => r = r₀)
      have h2 : Fintype.card {r : garlingRootSet ℚ L f // r = r₀} = 1 :=
        Fintype.card_subtype_eq r₀
      change Fintype.card {r : garlingRootSet ℚ L f // ¬ r = r₀} = 4
      omega
    let π4 : Equiv.Perm S4 :=
      { toFun := fun ⟨r, hr⟩ =>
          ⟨garlingRootPermHom ℚ L f σ r, fun h =>
            hr ((garlingRootPermHom ℚ L f σ).injective (h.trans (Subtype.ext hfix_r0).symm))⟩
        invFun := fun ⟨r, hr⟩ =>
          ⟨(garlingRootPermHom ℚ L f σ).symm r, fun h => by
            apply hr
            have := congrArg (garlingRootPermHom ℚ L f σ) h
            simpa using this.trans (Subtype.ext hfix_r0)⟩
        left_inv := fun ⟨r, hr⟩ => Subtype.ext (by simp)
        right_inv := fun ⟨r, hr⟩ => Subtype.ext (by simp) }
    have hπ4_24 : π4 ^ 24 = 1 := by
      have hdvd : orderOf π4 ∣ 24 := by
        have h1 : orderOf π4 ∣ Fintype.card (Equiv.Perm S4) := orderOf_dvd_card
        rw [Fintype.card_perm, hcard_S4] at h1
        exact h1
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hperm24 : (garlingRootPermHom ℚ L f σ) ^ 24 = 1 := by
      ext r
      by_cases hr : r = r₀
      · rw [hr]
        have hfix_pow : ∀ n : ℕ, ((garlingRootPermHom ℚ L f σ) ^ n) r₀ = r₀ := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih =>
            rw [pow_succ', Equiv.Perm.mul_apply, ih]
            exact Subtype.ext hfix_r0
        exact congrArg Subtype.val (hfix_pow 24)
      · have hact : ∀ n : ℕ, ((π4 ^ n) ⟨r, hr⟩).1 = ((garlingRootPermHom ℚ L f σ) ^ n) r := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih =>
            rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← ih]
            rfl
        have h24 := congrArg (fun p : Equiv.Perm S4 => (p ⟨r, hr⟩).1) hπ4_24
        rw [hact 24] at h24
        exact congrArg Subtype.val h24
    have h5_dvd_24 : 5 ∣ 24 := by
      rw [← hperm_ord]
      exact orderOf_dvd_iff_pow_eq_one.mpr hperm24
    exact absurd h5_dvd_24 (by decide)
  have _ : Fintype (garlingRootSet ℚ L f) := Fintype.ofFinite _
  have hb_bij : Function.Bijective b :=
    (Fintype.bijective_iff_injective_and_card b).mpr
      ⟨hb_inj, by rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard_eq5]⟩
  let eb : ZMod 5 ≃ garlingRootSet ℚ L f := Equiv.ofBijective b hb_bij
  -- Deduce `Irreducible f` from the single 5-element `σ`-orbit on the roots of `f`:
  have hirr : Irreducible f := by
    refine ⟨fun hu => ?_, fun g h hgh => ?_⟩
    · have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
    · have hg0 : g ≠ 0 := fun h0 => hf0 (by rw [hgh, h0, zero_mul])
      have hh0 : h ≠ 0 := fun h0 => hf0 (by rw [hgh, h0, mul_zero])
      have hdeg_add : g.natDegree + h.natDegree = 5 := by
        rw [← Polynomial.natDegree_mul hg0 hh0, ← hgh, hdeg]
      by_cases hg_deg : g.natDegree = 0
      · left; exact Polynomial.isUnit_iff_degree_eq_zero.mpr
          (by rw [Polynomial.degree_eq_natDegree hg0, hg_deg]; rfl)
      · right
        have hspl_f : (f.map (algebraMap ℚ L)).Splits := hsf_m.splits
        have hspl_g : (g.map (algebraMap ℚ L)).Splits :=
          Polynomial.Splits.of_dvd hspl_f (Polynomial.map_ne_zero hf0)
            (hgh ▸ Polynomial.map_dvd (algebraMap ℚ L) (dvd_mul_right g h))
        have hg_roots_pos : 0 < (g.map (algebraMap ℚ L)).roots.card := by
          rw [Polynomial.splits_iff_card_roots.mp hspl_g,
            Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ L).injective]
          omega
        obtain ⟨αg, hαg⟩ := Multiset.card_pos_iff_exists_mem.mp hg_roots_pos
        have hαg_zero : Polynomial.aeval αg g = 0 := by
          have h1 := (Polynomial.mem_roots (Polynomial.map_ne_zero hg0)).mp hαg
          rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
        have hαg_f : αg ∈ garlingRootSet ℚ L f := by
          change Polynomial.aeval αg f = 0
          rw [hgh, map_mul, hαg_zero, zero_mul]
        obtain ⟨k₀, hk₀⟩ := eb.surjective ⟨αg, hαg_f⟩
        have hall_g : ∀ k : ZMod 5, Polynomial.aeval (b k).1 g = 0 := by
          intro k
          have hstep_n : ∀ (n : ℕ) (x : ZMod 5), (σ ^ n) (b x).1 = (b (x + n)).1 := by
            intro n
            induction n with
            | zero => intro x; simp
            | succ n ih =>
              intro x
              rw [pow_succ', AlgEquiv.mul_apply, ih, hb_step]
              congr 2; push_cast; ring
          have heq : (b k).1 = (σ ^ (k - k₀).val) αg := by
            have hk0_val : (b k₀).1 = αg := congrArg Subtype.val hk₀
            rw [← hk0_val, hstep_n, show ((k - k₀).val : ZMod 5) = k - k₀ from ZMod.natCast_zmod_val _,
              add_sub_cancel]
          rw [heq]
          change Polynomial.aeval ((σ ^ (k - k₀).val).toAlgHom αg) g = 0
          rw [Polynomial.aeval_algHom_apply, hαg_zero, map_zero]
        have h5_le_g : 5 ≤ g.natDegree := by
          let emb : ZMod 5 ↪ (g.map (algebraMap ℚ L)).roots.toFinset :=
            ⟨fun k => ⟨(b k).1, by
              simp only [Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.map_ne_zero hg0),
                Polynomial.IsRoot.def]
              have hk := hall_g k
              rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at hk⟩,
             fun k₁ k₂ h => hb_inj (Subtype.ext (by simpa using congrArg Subtype.val h))⟩
          calc 5 = Fintype.card (ZMod 5) := (ZMod.card 5).symm
            _ ≤ Fintype.card (g.map (algebraMap ℚ L)).roots.toFinset :=
                Fintype.card_le_of_injective emb emb.injective
            _ = (g.map (algebraMap ℚ L)).roots.toFinset.card := Fintype.card_coe _
            _ ≤ (g.map (algebraMap ℚ L)).roots.card := Multiset.toFinset_card_le _
            _ ≤ (g.map (algebraMap ℚ L)).natDegree := Polynomial.card_roots' _
            _ = g.natDegree := Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ L).injective g
        have hh_deg : h.natDegree = 0 := by omega
        exact Polynomial.isUnit_iff_degree_eq_zero.mpr
          (by rw [Polynomial.degree_eq_natDegree hh0, hh_deg]; rfl)
  -- Core pair-sum distinctness on the `σ`-orbit labelling `b : ZMod 5 → garlingRootSet`:
  have hpair_b : ∀ a₁ a₂ b₁ b₂ : ZMod 5,
      a₁ ≠ a₂ → b₁ ≠ b₂ → (b a₁).1 + (b a₂).1 = (b b₁).1 + (b b₂).1 →
      (a₁ = b₁ ∧ a₂ = b₂) ∨ (a₁ = b₂ ∧ a₂ = b₁) := by
    intro a₁ a₂ b₁ b₂ ha hb heq
    have hb_val_inj : Function.Injective (fun k : ZMod 5 => (b k).1) :=
      fun _ _ h => hb_inj (Subtype.ext h)
    by_cases h1 : a₁ = b₁
    · left; refine ⟨h1, hb_val_inj ?_⟩; subst h1; linear_combination heq
    by_cases h2 : a₁ = b₂
    · right; refine ⟨h2, hb_val_inj ?_⟩; subst h2; linear_combination heq
    by_cases h3 : a₂ = b₁
    · right; refine ⟨hb_val_inj ?_, h3⟩; subst h3; linear_combination heq
    by_cases h4 : a₂ = b₂
    · left; refine ⟨hb_val_inj ?_, h4⟩; subst h4; linear_combination heq
    -- Disjoint pairs `{a₁, a₂} ∩ {b₁, b₂} = ∅`: find the unique 5th element `m` and shift so `m ↦ 4`:
    exfalso
    have hex_m : ∃ m : ZMod 5, m ≠ a₁ ∧ m ≠ a₂ ∧ m ≠ b₁ ∧ m ≠ b₂ := by
      have hcard_lt : ({a₁, a₂, b₁, b₂} : Finset (ZMod 5)).card < (Finset.univ : Finset (ZMod 5)).card := by
        have hle4 : ({a₁, a₂, b₁, b₂} : Finset (ZMod 5)).card ≤ 4 := by
          calc ({a₁, a₂, b₁, b₂} : Finset (ZMod 5)).card
              ≤ ({a₂, b₁, b₂} : Finset (ZMod 5)).card + 1 := Finset.card_insert_le _ _
            _ ≤ ({b₁, b₂} : Finset (ZMod 5)).card + 1 + 1 := by gcongr; exact Finset.card_insert_le _ _
            _ ≤ ({b₂} : Finset (ZMod 5)).card + 1 + 1 + 1 := by gcongr; exact Finset.card_insert_le _ _
            _ = 4 := by simp
        have h5 : (Finset.univ : Finset (ZMod 5)).card = 5 := by simp
        omega
      obtain ⟨m, _, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      exact ⟨m, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2⟩
    obtain ⟨m, hm1, hm2, hm3, hm4⟩ := hex_m
    let s : ZMod 5 := m + 1
    let c : ZMod 5 → L := fun k => (b (k + s)).1
    have hc_inj : Function.Injective c := fun x y hxy => by
      have := hb_val_inj hxy; exact add_right_cancel this
    have hc_step : ∀ k : ZMod 5, σ (c k) = c (k + 1) := fun k => by
      dsimp [c]; rw [hb_step]; congr 2; ring
    have hc_pow : ∀ (n : ℕ) (k : ZMod 5), (σ ^ n) (c k) = c (k + n) := by
      intro n
      induction n with
      | zero => intro k; simp
      | succ n ih =>
        intro k
        rw [pow_succ', AlgEquiv.mul_apply, ih, hc_step]
        congr 1; push_cast; ring
    let x₁ : ZMod 5 := a₁ - s
    let x₂ : ZMod 5 := a₂ - s
    let y₁ : ZMod 5 := b₁ - s
    let y₂ : ZMod 5 := b₂ - s
    have hshift_eq : ∀ n : ℕ, c (x₁ + n) + c (x₂ + n) = c (y₁ + n) + c (y₂ + n) := by
      intro n
      have h0 : c x₁ + c x₂ = c y₁ + c y₂ := by
        simpa [c, x₁, x₂, y₁, y₂, sub_add_cancel] using heq
      have hn := congrArg (σ ^ n) h0
      simpa only [map_add, hc_pow] using hn
    -- All four shifted indices lie in `{0, 1, 2, 3}` (none equals `4 = m - s`) and are pairwise distinct:
    have hne4 : x₁ ≠ 4 ∧ x₂ ≠ 4 ∧ y₁ ≠ 4 ∧ y₂ ≠ 4 := by
      have hms : m - s = 4 := by
        dsimp [s]
        have hneg1 : (-1 : ZMod 5) = 4 := by decide
        linear_combination hneg1
      refine ⟨fun h => hm1 (by linear_combination hms - h),
              fun h => hm2 (by linear_combination hms - h),
              fun h => hm3 (by linear_combination hms - h),
              fun h => hm4 (by linear_combination hms - h)⟩
    have hpair_ne : x₁ ≠ x₂ ∧ y₁ ≠ y₂ ∧ x₁ ≠ y₁ ∧ x₁ ≠ y₂ ∧ x₂ ≠ y₁ ∧ x₂ ≠ y₂ :=
      ⟨fun h => ha (by linear_combination h), fun h => hb (by linear_combination h),
       fun h => h1 (by linear_combination h), fun h => h2 (by linear_combination h),
       fun h => h3 (by linear_combination h), fun h => h4 (by linear_combination h)⟩
    -- Unordered partition of `{0, 1, 2, 3}` into `{x₁, x₂}` and `{y₁, y₂}` reduces to 3 patterns:
    have h3cases :
        (∀ r : ZMod 5, c r + c (r + 1) = c (r + 2) + c (r + 3)) ∨
        (∀ r : ZMod 5, c r + c (r + 2) = c (r + 1) + c (r + 3)) ∨
        (∀ r : ZMod 5, c r + c (r + 3) = c (r + 1) + c (r + 2)) := by
      have hshift_z : ∀ r : ZMod 5, c (x₁ + r) + c (x₂ + r) = c (y₁ + r) + c (y₂ + r) := fun r => by
        have := hshift_eq r.val
        rwa [ZMod.natCast_zmod_val] at this
      -- Check all 24 valid 4-tuples `(x₁, x₂, y₁, y₂)` of distinct elements in `{0, 1, 2, 3}`:
      have hcomb : ((x₁ = 0 ∧ x₂ = 1) ∨ (x₁ = 1 ∧ x₂ = 0)) ∧ ((y₁ = 2 ∧ y₂ = 3) ∨ (y₁ = 3 ∧ y₂ = 2)) ∨
          ((x₁ = 2 ∧ x₂ = 3) ∨ (x₁ = 3 ∧ x₂ = 2)) ∧ ((y₁ = 0 ∧ y₂ = 1) ∨ (y₁ = 1 ∧ y₂ = 0)) ∨
          ((x₁ = 0 ∧ x₂ = 2) ∨ (x₁ = 2 ∧ x₂ = 0)) ∧ ((y₁ = 1 ∧ y₂ = 3) ∨ (y₁ = 3 ∧ y₂ = 1)) ∨
          ((x₁ = 1 ∧ x₂ = 3) ∨ (x₁ = 3 ∧ x₂ = 1)) ∧ ((y₁ = 0 ∧ y₂ = 2) ∨ (y₁ = 2 ∧ y₂ = 0)) ∨
          ((x₁ = 0 ∧ x₂ = 3) ∨ (x₁ = 3 ∧ x₂ = 0)) ∧ ((y₁ = 1 ∧ y₂ = 2) ∨ (y₁ = 2 ∧ y₂ = 1)) ∨
          ((x₁ = 1 ∧ x₂ = 2) ∨ (x₁ = 2 ∧ x₂ = 1)) ∧ ((y₁ = 0 ∧ y₂ = 3) ∨ (y₁ = 3 ∧ y₂ = 0)) :=
        zmod5_four_distinct_partition x₁ x₂ y₁ y₂ hne4.1 hne4.2.1 hne4.2.2.1 hne4.2.2.2
          hpair_ne.1 hpair_ne.2.1 hpair_ne.2.2.1 hpair_ne.2.2.2.1 hpair_ne.2.2.2.2.1 hpair_ne.2.2.2.2.2
      rcases hcomb with (⟨hA | hA, hB | hB⟩ | ⟨hA | hA, hB | hB⟩ | ⟨hA | hA, hB | hB⟩ |
          ⟨hA | hA, hB | hB⟩ | ⟨hA | hA, hB | hB⟩ | ⟨hA | hA, hB | hB⟩)
      · left; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination this
      · left; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination this
      · left; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination this
      · left; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination this
      · left; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination -this
      · left; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination -this
      · left; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination -this
      · left; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination -this
      · right; left; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination this
      · right; left; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination this
      · right; left; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination this
      · right; left; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination this
      · right; left; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination -this
      · right; left; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination -this
      · right; left; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination -this
      · right; left; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination -this
      · right; right; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination this
      · right; right; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination this
      · right; right; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination this
      · right; right; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination this
      · right; right; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination -this
      · right; right; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination -this
      · right; right; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination -this
      · right; right; intro r; have := hshift_z r; rw [hA.1, hA.2, hB.1, hB.2] at this; ring_nf at this ⊢; linear_combination -this
    rcases h3cases with hA | hB | hC
    · -- Pattern A: `c r + c (r + 1) = c (r + 2) + c (r + 3)` ⇒ `c 1 = c 4`
      have e0 : c 0 + c 1 = c 2 + c 3 := by simpa using hA 0
      have e2 : c 2 + c 3 = c 4 + c 0 := by
        simpa only [show (2 : ZMod 5) + 1 = 3 from rfl, show (2 : ZMod 5) + 2 = 4 from rfl,
          show (2 : ZMod 5) + 3 = 0 from rfl] using hA 2
      have h14 : c 1 = c 4 := by linear_combination e0 + e2
      exact absurd (hc_inj h14) (by decide)
    · -- Pattern B: `c r + c (r + 2) = c (r + 1) + c (r + 3)` ⇒ `c 2 = c 3`
      have e0 : c 0 + c 2 = c 1 + c 3 := by simpa using hB 0
      have e1 : c 1 + c 3 = c 2 + c 4 := by
        simpa only [show (1 : ZMod 5) + 2 = 3 from rfl, show (1 : ZMod 5) + 1 = 2 from rfl,
          show (1 : ZMod 5) + 3 = 4 from rfl] using hB 1
      have e2 : c 2 + c 4 = c 3 + c 0 := by
        simpa only [show (2 : ZMod 5) + 2 = 4 from rfl, show (2 : ZMod 5) + 1 = 3 from rfl,
          show (2 : ZMod 5) + 3 = 0 from rfl] using hB 2
      have h23 : c 2 = c 3 := by linear_combination e0 + e1 + e2
      exact absurd (hc_inj h23) (by decide)
    · -- Pattern C: `c r + c (r + 3) = c (r + 1) + c (r + 2)` ⇒ `5 * (c 2 - c 0) = 0` ⇒ `c 2 = c 0`
      have e0 : c 0 + c 3 = c 1 + c 2 := by simpa using hC 0
      have e1 : c 1 + c 4 = c 2 + c 3 := by
        simpa only [show (1 : ZMod 5) + 3 = 4 from rfl, show (1 : ZMod 5) + 1 = 2 from rfl,
          show (1 : ZMod 5) + 2 = 3 from rfl] using hC 1
      have e2 : c 2 + c 0 = c 3 + c 4 := by
        simpa only [show (2 : ZMod 5) + 3 = 0 from rfl, show (2 : ZMod 5) + 1 = 3 from rfl,
          show (2 : ZMod 5) + 2 = 4 from rfl] using hC 2
      have e4 : c 4 + c 2 = c 0 + c 1 := by
        simpa only [show (4 : ZMod 5) + 3 = 2 from rfl, show (4 : ZMod 5) + 1 = 0 from rfl,
          show (4 : ZMod 5) + 2 = 1 from rfl] using hC 4
      have h5 : (5 : L) * (c 2 - c 0) = 0 := by
        linear_combination -3 * e0 - 2 * e1 - e2 + e4
      have h5_ne0 : (5 : L) ≠ 0 := by
        have hm : algebraMap ℚ L (5 : ℚ) = (5 : L) := map_ofNat (algebraMap ℚ L) 5
        rw [← hm]; exact (map_ne_zero _).mpr (by norm_num)
      have h20 : c 2 = c 0 := sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_left h5_ne0)
      exact absurd (hc_inj h20) (by decide)
  -- Transport `hpair_b` to any root-labelling bijection `e : Fin 5 ≃ garlingRootSet ℚ L f`:
  refine ⟨hirr, hf_sep, ⟨eb⟩, fun e i j k l hij hkl heq => ?_⟩
  let a₁ := eb.symm (e i)
  let a₂ := eb.symm (e j)
  let b₁ := eb.symm (e k)
  let b₂ := eb.symm (e l)
  have ha : a₁ ≠ a₂ := fun h => ne_of_lt hij (e.injective (eb.symm.injective h))
  have hb : b₁ ≠ b₂ := fun h => ne_of_lt hkl (e.injective (eb.symm.injective h))
  have heq' : (b a₁).1 + (b a₂).1 = (b b₁).1 + (b b₂).1 := by
    have hfun : ∀ r : garlingRootSet ℚ L f, (b (eb.symm r)).1 = r.1 :=
      fun r => congrArg Subtype.val (eb.apply_symm_apply r)
    simpa only [a₁, a₂, b₁, b₂, hfun] using heq
  rcases hpair_b a₁ a₂ b₁ b₂ ha hb heq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨e.injective (eb.symm.injective h1), e.injective (eb.symm.injective h2)⟩
  · exfalso
    have hik : i = l := e.injective (eb.symm.injective h1)
    have hjl : j = k := e.injective (eb.symm.injective h2)
    omega

/-- **Exercise 20.6 (literal, §20.3, printed p. 162 / PDF p. 170):**
*"Suppose that `f` is a quintic in `ℚ[x]` whose Galois group contains `D₁₀`. Show that the `10`
sums `α_i + α_j` (`1 ≤ i < j ≤ 5`) of pairs of roots of `f` are distinct."*

Formalized in abstract-subgroup form (`∃ H ≤ Γ_ℚ(f), Nonempty (H ≃* DihedralGroup 5)`), without
assuming irreducibility or separability (both follow automatically from `10 ∣ |Γ_ℚ(f)|`), and
complemented by `exercise_20_6_perm` for direct permutation-subgroup containment `D₁₀ ≤ Γ ⊆ Σ₅`. -/
theorem exercise_20_6 {L : Type u} [Field L] [Algebra ℚ L]
    {f : ℚ[X]} (hdeg : f.natDegree = 5)
    (hsf : IsGarlingSplittingFieldExtension ℚ L f)
    (hD10 : ∃ H : Subgroup (GarlingPolyGaloisGroup ℚ L f), Nonempty (H ≃* DihedralGroup 5)) :
    Irreducible f ∧
    f.Separable ∧
    Nonempty (Fin 5 ≃ garlingRootSet ℚ L f) ∧
    ∀ (e : Fin 5 ≃ garlingRootSet ℚ L f) (i j k l : Fin 5),
      i < j → k < l → (e i : L) + (e j : L) = (e k : L) + (e l : L) → i = k ∧ j = l := by
  rcases hD10 with ⟨H, ⟨eH⟩⟩
  have hr1_ord : orderOf (DihedralGroup.r (1 : ZMod 5)) = 5 := by
    rw [orderOf_eq_iff (by decide)]
    refine ⟨by decide, fun m hm hpos => ?_⟩
    interval_cases m <;> decide
  let σ : GarlingPolyGaloisGroup ℚ L f := (eH.symm (DihedralGroup.r (1 : ZMod 5))).1
  have hσ_ord : orderOf σ = 5 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hr1_ord]
  exact quintic_pair_sums_distinct_of_five_cycle hdeg hsf σ hσ_ord

/-- **Exercise 20.6 (permutation-subgroup containment form, §20.3, printed p. 162):**
If `pentagonDihedral ≤ (garlingRootLabellingPermHom e).range` (or any conjugate thereof), then the
`10` pairwise root sums `(e i : L) + (e j : L)` (`i < j`) are pairwise distinct. -/
theorem exercise_20_6_perm {L : Type u} [Field L] [Algebra ℚ L]
    {f : ℚ[X]} (hdeg : f.natDegree = 5)
    (hsf : IsGarlingSplittingFieldExtension ℚ L f)
    (e : Fin 5 ≃ garlingRootSet ℚ L f)
    (hD10 : pentagonDihedral ≤ (garlingRootLabellingPermHom e).range) :
    ∀ i j k l : Fin 5,
      i < j → k < l → (e i : L) + (e j : L) = (e k : L) + (e l : L) → i = k ∧ j = l := by
  let φ := garlingRootLabellingPermHom e
  have hφ_inj : Function.Injective φ := garlingRootLabellingPermHom_injective_ch20 hsf e
  let H : Subgroup (GarlingPolyGaloisGroup ℚ L f) := pentagonDihedral.comap φ
  let eH : H ≃* pentagonDihedral :=
    MulEquiv.ofBijective
      ({ toFun := fun x => ⟨φ x.1, x.2⟩
         map_one' := Subtype.ext (map_one φ)
         map_mul' := fun a b => Subtype.ext (map_mul φ a.1 b.1) } : H →* pentagonDihedral)
      ⟨fun a b h => Subtype.ext (hφ_inj (congrArg Subtype.val h)),
       fun y => by
         obtain ⟨σ, hσ⟩ := hD10 y.2
         exact ⟨⟨σ, show φ σ ∈ pentagonDihedral by rw [hσ]; exact y.2⟩, Subtype.ext hσ⟩⟩
  exact (exercise_20_6 hdeg hsf ⟨H, ⟨eH.trans pentagonDihedralMulEquiv.symm⟩⟩).2.2.2 e

/-! ### The five concrete §20.3 quintics `(a)`–`(e)` (printed pp. 161–162 / PDF pp. 169–170) -/

/-- **§20.3 Example `(a)` (printed p. 161 / PDF p. 169):**
`f_a = x⁵ + x⁴ - 4x³ - 3x² + 3x + 1 ∈ ℚ[x]` is irreducible of degree `5`, has all `5` roots real
(`2 cos(2πk/11)` for `k = 1, …, 5`), has positive rational-square discriminant, is solvable by
radicals, and for every splitting field `L : ℚ` has `Γ_ℚ(f_a) ≃* Multiplicative (ZMod 5)` (`ℤ₅`). -/
theorem section_20_3_example_a :
    let f : ℚ[X] :=
      Polynomial.X ^ 5 + Polynomial.X ^ 4 - Polynomial.C 4 * Polynomial.X ^ 3 -
        Polynomial.C 3 * Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 1
    Irreducible f ∧
    f.natDegree = 5 ∧
    {x : ℝ | Polynomial.aeval x f = 0}.ncard = 5 ∧
    0 < garlingDiscriminant f ∧
    (∃ d : ℚ, d ^ 2 = garlingDiscriminant f) ∧
    IsGarlingSolvableByRadicals f ∧
    ∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L f →
      Nat.card (GarlingPolyGaloisGroup ℚ L f) = 5 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* Multiplicative (ZMod 5)) := by
  classical
  intro f
  have hf_mon : f.Monic := by
    dsimp [f]
    have hform : Polynomial.X ^ 5 + Polynomial.X ^ 4 - Polynomial.C (4 : ℚ) * Polynomial.X ^ 3 -
        Polynomial.C 3 * Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 1 =
        Polynomial.X ^ 5 + (Polynomial.X ^ 4 - Polynomial.C 4 * Polynomial.X ^ 3 -
          Polynomial.C 3 * Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 1) := by
      ring
    rw [hform]
    have hlt : (Polynomial.X ^ 4 - Polynomial.C (4 : ℚ) * Polynomial.X ^ 3 -
        Polynomial.C 3 * Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 1).natDegree < 5 := by
      compute_degree!
    exact Polynomial.monic_X_pow_add (Polynomial.degree_lt_iff_coeff_zero _ _ |>.mpr fun m hm =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  have hf_deg : f.natDegree = 5 := by dsimp [f]; compute_degree!
  -- Realize the 5 roots via `ε = exp(2πi/11) ∈ ℂ`:
  let ε : ℂ := Complex.exp (2 * Real.pi * Complex.I / 11)
  have hε_prim : IsPrimitiveRoot ε 11 := Complex.isPrimitiveRoot_exp 11 (by decide)
  have hε_gar : IsGarlingPrimitiveRoot 11 ε :=
    (isGarlingPrimitiveRoot_iff_isPrimitiveRoot (by decide : 1 ≤ 11) ε).mpr hε_prim
  have hε_ne0 : ε ≠ 0 := hε_prim.ne_zero (by decide)
  have hε_11 : ε ^ 11 = 1 := hε_prim.pow_eq_one
  -- Algebraic identity: for any `z ≠ 0` with `z^11 = 1` and `z ≠ 1`, `aeval (z + z⁻¹) f = 0`:
  have hroot_of_prim : ∀ z : ℂ, z ≠ 0 → z ^ 11 = 1 → z ≠ 1 → Polynomial.aeval (z + z⁻¹) f = 0 := by
    intro z hz0 hz11 hz1
    have hsum : ∑ j ∈ Finset.range 11, z ^ j = 0 := by
      have hgeom : (z - 1) * ∑ j ∈ Finset.range 11, z ^ j = z ^ 11 - 1 := by
        simpa [mul_comm] using geom_sum_mul z 11
      rw [hz11, sub_self] at hgeom
      exact (mul_eq_zero.mp hgeom).resolve_left (sub_ne_zero.mpr hz1)
    have hmul : z ^ 5 * Polynomial.aeval (z + z⁻¹) f = ∑ j ∈ Finset.range 11, z ^ j := by
      simp only [f, map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
        map_ofNat, map_one, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      field_simp [hz0]
      ring
    have hprod0 : z ^ 5 * Polynomial.aeval (z + z⁻¹) f = 0 := hmul.trans hsum
    exact (mul_eq_zero.mp hprod0).resolve_left (pow_ne_zero 5 hz0)
  -- Define `η = ε + ε⁻¹`, prove `finrank ℚ ℚ⟮η⟯ = 5` via `Chapter15.exercise_15_4`, deduce `Irreducible f`:
  let η : ℂ := ε + ε⁻¹
  let F : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({η} : Set ℂ)
  have hfin_F : Module.finrank ℚ F = 5 := by
    have h15 := (Chapter15.exercise_15_4 (by decide : 2 < 11) hε_gar).2.2.2.2.1
    have htot : Nat.totient 11 / 2 = 5 := by decide
    exact h15.trans htot
  have hη_root : Polynomial.aeval η f = 0 :=
    hroot_of_prim ε hε_ne0 hε_11 (hε_prim.ne_one (by decide))
  have hη_int : IsIntegral ℚ η := ⟨f, hf_mon, hη_root⟩
  have hmin_eq : minpoly ℚ η = f := by
    have hdvd : minpoly ℚ η ∣ f := minpoly.dvd ℚ η hη_root
    have hdeg_min : (minpoly ℚ η).natDegree = 5 := by
      rw [← IntermediateField.adjoin.finrank hη_int]; exact hfin_F
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hη_int) hf_mon hdvd
      (by omega)).symm
  have hirr : Irreducible f := hmin_eq ▸ minpoly.irreducible hη_int
  -- The 5 real roots `r k = 2 cos(2π(k+1)/11)` (`k : Fin 5`):
  let r : Fin 5 → ℝ := fun k => 2 * Real.cos (2 * Real.pi * ((k.val + 1 : ℕ) : ℝ) / 11)
  have hr_eq_pow : ∀ k : Fin 5, (r k : ℂ) = ε ^ (k.val + 1) + (ε ^ (k.val + 1))⁻¹ := by
    intro k
    let θ : ℝ := 2 * Real.pi * ((k.val + 1 : ℕ) : ℝ) / 11
    have harg : ((k.val + 1 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 11) =
        (θ : ℂ) * Complex.I := by
      dsimp [θ]; push_cast; ring
    have hexp_k : ε ^ (k.val + 1) = Complex.exp ((θ : ℂ) * Complex.I) := by
      dsimp [ε]
      rw [← Complex.exp_nat_mul, harg]
    have hneg_k : (ε ^ (k.val + 1))⁻¹ = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
      rw [hexp_k, ← Complex.exp_neg]
      congr 1; push_cast; ring
    rw [hneg_k, hexp_k, Complex.exp_mul_I, Complex.exp_mul_I, Complex.ofReal_neg,
      Complex.cos_neg, Complex.sin_neg]
    dsimp [r, θ]
    push_cast
    ring
  have hr_root_C : ∀ k : Fin 5, Polynomial.aeval (r k : ℂ) f = 0 := by
    intro k
    rw [hr_eq_pow k]
    exact hroot_of_prim (ε ^ (k.val + 1)) (pow_ne_zero _ hε_ne0)
      (by rw [← pow_mul, mul_comm, pow_mul, hε_11, one_pow])
      (hε_prim.pow_ne_one_of_pos_of_lt (Nat.succ_ne_zero _) (by omega))
  have hr_root_R : ∀ k : Fin 5, Polynomial.aeval (r k) f = 0 := by
    intro k
    apply Complex.ofReal_injective
    have h1 := hr_root_C k
    have hcomm : Complex.ofRealHom (Polynomial.aeval (r k) f) = Polynomial.aeval (r k : ℂ) f := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
      rfl
    exact hcomm.trans h1 |>.trans (map_zero Complex.ofRealHom).symm
  have hr_inj : Function.Injective r := by
    intro i j hij
    have hcos : Real.cos (2 * Real.pi * ((i.val + 1 : ℕ) : ℝ) / 11) =
        Real.cos (2 * Real.pi * ((j.val + 1 : ℕ) : ℝ) / 11) := by
      dsimp [r] at hij; linarith
    have hpi : 0 < Real.pi := Real.pi_pos
    have hmem : ∀ k : Fin 5, 2 * Real.pi * ((k.val + 1 : ℕ) : ℝ) / 11 ∈ Set.Icc 0 Real.pi := by
      intro k
      have hk1 : (1 : ℝ) ≤ (k.val + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k.val
      have hk5 : ((k.val + 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (show k.val + 1 ≤ 5 by omega)
      constructor <;> nlinarith
    have heq_arg := Real.strictAntiOn_cos.injOn (hmem i) (hmem j) hcos
    have hnat : ((i.val + 1 : ℕ) : ℝ) = ((j.val + 1 : ℕ) : ℝ) := by
      have hpos : (2 * Real.pi / 11 : ℝ) ≠ 0 := by positivity
      have : (2 * Real.pi / 11) * ((i.val + 1 : ℕ) : ℝ) = (2 * Real.pi / 11) * ((j.val + 1 : ℕ) : ℝ) := by
        linarith
      exact mul_left_cancel₀ hpos this
    have hnat' : i.val + 1 = j.val + 1 := by exact_mod_cast hnat
    exact Fin.ext (by omega)
  have hreal_ncard : {x : ℝ | Polynomial.aeval x f = 0}.ncard = 5 := by
    have hfin : {x : ℝ | Polynomial.aeval x f = 0}.Finite :=
      (separable_rat_roots_partition hirr.separable).2.2.1
    have hsub : Set.range r ⊆ {x : ℝ | Polynomial.aeval x f = 0} := by
      rintro _ ⟨k, rfl⟩; exact hr_root_R k
    have hge5 : 5 ≤ {x : ℝ | Polynomial.aeval x f = 0}.ncard := by
      calc 5 = (Set.range r).ncard := by rw [Set.ncard_range_of_injective hr_inj, Nat.card_fin]
        _ ≤ {x : ℝ | Polynomial.aeval x f = 0}.ncard := Set.ncard_le_ncard hsub hfin
    have hle5 : {x : ℝ | Polynomial.aeval x f = 0}.ncard ≤ 5 := by
      have hsub2 : {x : ℝ | Polynomial.aeval x f = 0} ⊆ ((f.map (algebraMap ℚ ℝ)).roots.toFinset : Set ℝ) := by
        intro x hx
        change Polynomial.aeval x f = 0 at hx
        simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots
          (Polynomial.map_ne_zero hirr.ne_zero), Polynomial.IsRoot.def]
        rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at hx
      calc {x : ℝ | Polynomial.aeval x f = 0}.ncard
          ≤ ((f.map (algebraMap ℚ ℝ)).roots.toFinset : Set ℝ).ncard :=
            Set.ncard_le_ncard hsub2 (Finset.finite_toSet _)
        _ = (f.map (algebraMap ℚ ℝ)).roots.toFinset.card := Set.ncard_coe_finset _
        _ ≤ (f.map (algebraMap ℚ ℝ)).roots.card := Multiset.toFinset_card_le _
        _ ≤ (f.map (algebraMap ℚ ℝ)).natDegree := Polynomial.card_roots' _
        _ = 5 := by rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective, hf_deg]
    omega
  -- Every root `(r k : ℂ) = ε^(k+1) + ε^(-(k+1))` lies in `F = ℚ⟮η⟯` (Chebyshev polynomials in `η`):
  have hr_mem_F : ∀ k : Fin 5, (r k : ℂ) ∈ F := by
    have hηF : η ∈ F := IntermediateField.mem_adjoin_simple_self ℚ η
    have hzi : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε_ne0
    have hzi2 : ε ^ 2 * ε⁻¹ ^ 2 = 1 := by linear_combination (ε * ε⁻¹ + 1) * hzi
    have hzi3 : ε ^ 3 * ε⁻¹ ^ 3 = 1 := by linear_combination (ε ^ 2 * ε⁻¹ ^ 2 + ε * ε⁻¹ + 1) * hzi
    have hzi4 : ε ^ 4 * ε⁻¹ ^ 4 = 1 := by linear_combination (ε ^ 3 * ε⁻¹ ^ 3 + ε ^ 2 * ε⁻¹ ^ 2 + ε * ε⁻¹ + 1) * hzi
    intro k
    rw [hr_eq_pow k]
    fin_cases k
    · simpa [η] using hηF
    · have h2 : ε ^ 2 + (ε ^ 2)⁻¹ = η ^ 2 - 2 := by
        rw [← inv_pow]; dsimp [η]; linear_combination -2 * hzi
      rw [h2]; exact F.sub_mem (F.pow_mem hηF 2) (by exact_mod_cast F.algebraMap_mem (2 : ℚ))
    · have h3 : ε ^ 3 + (ε ^ 3)⁻¹ = η ^ 3 - 3 * η := by
        rw [← inv_pow]; dsimp [η]; linear_combination -3 * (ε + ε⁻¹) * hzi
      rw [h3]
      exact F.sub_mem (F.pow_mem hηF 3)
        (F.mul_mem (by exact_mod_cast F.algebraMap_mem (3 : ℚ)) hηF)
    · have h4 : ε ^ 4 + (ε ^ 4)⁻¹ = η ^ 4 - 4 * η ^ 2 + 2 := by
        rw [← inv_pow]; dsimp [η]; linear_combination -4 * (ε ^ 2 + ε⁻¹ ^ 2) * hzi - 6 * hzi2 + 8 * hzi
      rw [h4]
      exact F.add_mem (F.sub_mem (F.pow_mem hηF 4)
        (F.mul_mem (by exact_mod_cast F.algebraMap_mem (4 : ℚ)) (F.pow_mem hηF 2)))
        (by exact_mod_cast F.algebraMap_mem (2 : ℚ))
    · have h5 : ε ^ 5 + (ε ^ 5)⁻¹ = η ^ 5 - 5 * η ^ 3 + 5 * η := by
        rw [← inv_pow]; dsimp [η]
        linear_combination -5 * (ε ^ 3 + ε⁻¹ ^ 3) * hzi - 10 * (ε + ε⁻¹) * hzi2 +
          15 * (ε + ε⁻¹) * hzi
      rw [h5]
      exact F.add_mem (F.sub_mem (F.pow_mem hηF 5)
        (F.mul_mem (by exact_mod_cast F.algebraMap_mem (5 : ℚ)) (F.pow_mem hηF 3)))
        (F.mul_mem (by exact_mod_cast F.algebraMap_mem (5 : ℚ)) hηF)
  -- Hence `F = ℚ⟮η⟯` is a splitting field of `f` over `ℚ` of degree `5`:
  have hsf_F : IsGarlingSplittingFieldExtension ℚ F f := by
    let αF : Fin 5 → F := fun k => ⟨(r k : ℂ), hr_mem_F k⟩
    have hαF_inj : Function.Injective αF := fun i j hij =>
      hr_inj (Complex.ofReal_injective (congrArg Subtype.val hij))
    have hαF_root : ∀ k : Fin 5, (f.map (algebraMap ℚ F)).IsRoot (αF k) := fun k => by
      rw [Polynomial.IsRoot.def]
      apply F.val.injective
      change F.val.toRingHom ((f.map (algebraMap ℚ F)).eval (αF k)) = F.val.toRingHom 0
      rw [map_zero, ← Polynomial.eval₂_eq_eval_map, Polynomial.hom_eval₂]
      exact hr_root_C k
    have hprod_dvd : (∏ k : Fin 5, (Polynomial.X - Polynomial.C (αF k))) ∣ f.map (algebraMap ℚ F) := by
      have hpw : Set.Pairwise (Finset.univ : Finset (Fin 5)) fun i j =>
          IsCoprime (Polynomial.X - Polynomial.C (αF i)) (Polynomial.X - Polynomial.C (αF j)) := by
        intro i _ j _ hij
        exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr
          (sub_ne_zero.mpr (fun h => hij (hαF_inj h))))
      exact Finset.prod_dvd_of_coprime hpw fun k _ => Polynomial.dvd_iff_isRoot.mpr (hαF_root k)
    have hmon_prod : (∏ k : Fin 5, (Polynomial.X - Polynomial.C (αF k))).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C _
    have hdeg_prod : (∏ k : Fin 5, (Polynomial.X - Polynomial.C (αF k))).natDegree = 5 := by
      rw [Polynomial.natDegree_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C _]
      simp
    have hexp_F : GarlingSplitsExplicit ℚ F f 5 1 αF := by
      unfold GarlingSplitsExplicit
      rw [map_one, Polynomial.C_1, one_mul]
      exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon_prod (hf_mon.map _) hprod_dvd
        (by rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ F).injective, hf_deg, hdeg_prod])
    have hgen_F : IntermediateField.adjoin ℚ (Set.range αF) = ⊤ := by
      rw [eq_top_iff]; intro ⟨x, hx⟩ _
      let M : IntermediateField ℚ ℂ := (IntermediateField.adjoin ℚ (Set.range αF)).map F.val
      have hsub : F ≤ M := by
        rw [IntermediateField.adjoin_le_iff]; rintro _ rfl
        exact ⟨αF 0, IntermediateField.subset_adjoin ℚ _ ⟨0, rfl⟩, by
          show (r 0 : ℂ) = η; rw [hr_eq_pow 0]; simp [η]⟩
      obtain ⟨z, hz, hzx⟩ := hsub hx
      exact (Subtype.ext hzx : z = ⟨x, hx⟩) ▸ hz
    refine ⟨⟨5, 1, αF, hexp_F⟩, fun M hne hM => hne ?_⟩
    rcases hM with ⟨m, lam, β, hβ⟩
    have hle : IntermediateField.adjoin ℚ (Set.range αF) ≤ M := by
      rw [IntermediateField.adjoin_le_iff]; rintro _ ⟨k, rfl⟩
      have hmap_eq : f.map (algebraMap ℚ F) =
          Polynomial.C (algebraMap ℚ F lam) * ∏ j : Fin m, (Polynomial.X - Polynomial.C (M.val (β j))) := by
        have h1 := congrArg (Polynomial.map M.val.toRingHom) hβ
        rw [Polynomial.map_map, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod] at h1
        have hcomp : M.val.toRingHom.comp (algebraMap ℚ M) = algebraMap ℚ F := rfl
        rw [hcomp] at h1
        rw [h1]
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        simp [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      have hroot0 := hαF_root k
      rw [Polynomial.IsRoot.def, hmap_eq, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod] at hroot0
      have hlam0 : algebraMap ℚ F lam ≠ 0 := by
        have hlc : lam = f.leadingCoeff := (garlingSplitsExplicit_props hirr.ne_zero hβ).1
        rw [hlc, hf_mon.leadingCoeff, map_one]; exact one_ne_zero
      obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp ((mul_eq_zero.mp hroot0).resolve_left hlam0)
      have heq : αF k = M.val (β j) := sub_eq_zero.mp (by simpa using hj)
      exact heq ▸ (β j).2
    exact top_le_iff.mp (hgen_F ▸ hle)
  -- Deduce `|Γ_ℚ(f)| = 5` and `Γ_ℚ(f) ≃* Multiplicative (ZMod 5)` for EVERY splitting field `L : ℚ`:
  have hgal_all : ∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L f →
      Nat.card (GarlingPolyGaloisGroup ℚ L f) = 5 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* Multiplicative (ZMod 5)) := by
    intro L _ _ hsfL
    obtain ⟨eLF⟩ := splitting_field_unique_up_to_algEquiv hsfL hsf_F
    have hfinL : Module.finrank ℚ L = 5 := by
      rw [LinearEquiv.finrank_eq eLF.toLinearEquiv, hfin_F]
    have _ : Polynomial.IsSplittingField ℚ L f := (isGarlingSplittingFieldExtension_iff ℚ L f).mp hsfL
    have _ : FiniteDimensional ℚ L := Polynomial.IsSplittingField.finiteDimensional L f
    have _ : Normal ℚ L := Normal.of_isSplittingField f
    have _ : IsGalois ℚ L := ⟨⟩
    have hcardL : Nat.card (GarlingPolyGaloisGroup ℚ L f) = 5 := by
      rw [IsGalois.card_aut_eq_finrank, hfinL]
    refine ⟨hcardL, ?_⟩
    obtain ⟨_, _, _, h5way, _, _, _⟩ := section_20_3_quintic_galois_classification hirr hf_deg hsfL
    rcases h5way with h | h | h | h | h
    · exact h
    · exfalso; obtain ⟨e⟩ := h; have hc := Nat.card_congr e.toEquiv; rw [hcardL, DihedralGroup.nat_card] at hc; omega
    · exfalso; obtain ⟨e⟩ := h; have hc := Nat.card_congr e.toEquiv
      rw [hcardL, garlingAffineGroup_card (by decide : Nat.Prime 5)] at hc; norm_num at hc
    · exfalso; obtain ⟨e⟩ := h; have hc := Nat.card_congr e.toEquiv
      have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := exercise_11_5_s5.1 3
      rw [hcardL, h60] at hc; omega
    · exfalso; obtain ⟨e⟩ := h; have hc := Nat.card_congr e.toEquiv
      rw [hcardL, Nat.card_perm, Nat.card_fin] at hc; norm_num at hc
  have hcl_F := section_20_3_quintic_galois_classification hirr hf_deg hsf_F
  have _ : Polynomial.IsSplittingField ℚ F f := (isGarlingSplittingFieldExtension_iff ℚ F f).mp hsf_F
  have _ : FiniteDimensional ℚ F := Polynomial.IsSplittingField.finiteDimensional F f
  have _ : Normal ℚ F := Normal.of_isSplittingField f
  have _ : IsGalois ℚ F := ⟨⟩
  have hcard_F : Nat.card (GarlingPolyGaloisGroup ℚ F f) = 5 := by
    rw [IsGalois.card_aut_eq_finrank, hfin_F]
  have hsol_F : IsGarlingSoluble (GarlingPolyGaloisGroup ℚ F f) :=
    hcl_F.2.2.2.2.2.1.mpr (hcard_F ▸ (by decide : 5 ∣ 20))
  have hrad_f : IsGarlingSolvableByRadicals f := hcl_F.2.2.2.2.1.mpr hsol_F
  have hsq_f : ∃ d : ℚ, d ^ 2 = garlingDiscriminant f :=
    hcl_F.2.2.2.2.2.2.mpr (Or.inl hcard_F)
  have hpos_f : 0 < garlingDiscriminant f :=
    exercise_20_3_mod4_eq_1 (p := 5) (by decide) (by decide) hirr hf_deg hrad_f
  exact ⟨hirr, hf_deg, hreal_ncard, hpos_f, hsq_f, hrad_f, hgal_all⟩

/-- Explicit indexing of the `10` unordered pairs `(i, j)` (`i < j`) in `Fin 5`, for §20.3 Example `(b)`. -/
def quinticPairIdx : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

/-- Helper: double symmetric sum over `Fin 5 × Fin 5` splits into diagonal plus twice the `10` pairs. -/
private theorem sum_fin5_symm_eq_diag_add_two_mul_pairs {R : Type*} [CommRing R]
    (F : Fin 5 → Fin 5 → R) (hcomm : ∀ i j, F i j = F j i) :
    ∑ i : Fin 5, ∑ j : Fin 5, F i j =
      (∑ i : Fin 5, F i i) + 2 * ∑ t : Fin 10, F (quinticPairIdx t).1 (quinticPairIdx t).2 := by
  simp only [Fin.sum_univ_five]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, quinticPairIdx, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one, add_zero]
  simp only [hcomm 1 0, hcomm 2 0, hcomm 3 0, hcomm 4 0, hcomm 2 1, hcomm 3 1, hcomm 4 1,
    hcomm 3 2, hcomm 4 2, hcomm 4 3]
  ring

/-- Helper: `A₅` acts transitively on unordered pairs `{i, j}` of `Fin 5`. -/
private theorem alternatingGroup_five_transitive_on_pairs (t : Fin 10) :
    ∃ π : Equiv.Perm (Fin 5), π ∈ alternatingGroup (Fin 5) ∧
      ((π 0 = (quinticPairIdx t).1 ∧ π 1 = (quinticPairIdx t).2) ∨
        (π 0 = (quinticPairIdx t).2 ∧ π 1 = (quinticPairIdx t).1)) := by
  let p0 : Equiv.Perm (Fin 5) := 1
  let p1 : Equiv.Perm (Fin 5) := Equiv.swap 1 2 * Equiv.swap 2 3
  let p2 : Equiv.Perm (Fin 5) := Equiv.swap 1 3 * Equiv.swap 3 2
  let p3 : Equiv.Perm (Fin 5) := Equiv.swap 1 4 * Equiv.swap 4 2
  let p4 : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 0 1
  let p5 : Equiv.Perm (Fin 5) := Equiv.swap 0 3 * Equiv.swap 0 1
  let p6 : Equiv.Perm (Fin 5) := Equiv.swap 0 4 * Equiv.swap 0 1
  let p7 : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3
  let p8 : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 4
  let p9 : Equiv.Perm (Fin 5) := Equiv.swap 0 3 * Equiv.swap 1 4
  fin_cases t
  · exact ⟨p0, Equiv.Perm.mem_alternatingGroup.mpr (by decide), by decide⟩
  · exact ⟨p1, Equiv.Perm.mem_alternatingGroup.mpr (by decide), by decide⟩
  · exact ⟨p2, Equiv.Perm.mem_alternatingGroup.mpr (by decide), by decide⟩
  · exact ⟨p3, Equiv.Perm.mem_alternatingGroup.mpr (by decide), by decide⟩
  · exact ⟨p4, Equiv.Perm.mem_alternatingGroup.mpr (by decide), by decide⟩
  · exact ⟨p5, Equiv.Perm.mem_alternatingGroup.mpr (by decide), by decide⟩
  · exact ⟨p6, Equiv.Perm.mem_alternatingGroup.mpr (by decide), by decide⟩
  · exact ⟨p7, Equiv.Perm.mem_alternatingGroup.mpr (by decide), by decide⟩
  · exact ⟨p8, Equiv.Perm.mem_alternatingGroup.mpr (by decide), by decide⟩
  · exact ⟨p9, Equiv.Perm.mem_alternatingGroup.mpr (by decide), by decide⟩

/-- **§20.3 Inline Prose Definition (`g`, printed p. 162 / PDF p. 170):**
Given `5` roots `α : Fin 5 → L`, the degree-`10` pair-sum resolvent polynomial
`g(x) = ∏_{1 ≤ i < j ≤ 5} (x - (α_i + α_j)) ∈ L[x]`. -/
noncomputable def garlingPairSumResolvent {L : Type*} [CommRing L] (α : Fin 5 → L) : L[X] :=
  ∏ t : Fin 10, (Polynomial.X - Polynomial.C (α (quinticPairIdx t).1 + α (quinticPairIdx t).2))

/-- Helper: power sum of the `10` pairwise sums of `5` elements satisfies
`2 · P_m = ∑_{r=0}^m C(m, r) S_r S_{m-r} - 2^m S_m`. -/
private theorem two_mul_garlingPowerSum_pairs {L : Type*} [CommRing L] (α : Fin 5 → L) (m : ℕ) :
    let γ : Fin 10 → L := fun t => α (quinticPairIdx t).1 + α (quinticPairIdx t).2
    2 * garlingPowerSum γ m =
      (∑ r ∈ Finset.range (m + 1),
        (Nat.choose m r : L) * garlingPowerSum α r * garlingPowerSum α (m - r)) -
      (2 : L) ^ m * garlingPowerSum α m := by
  intro γ
  have hdouble := sum_fin5_symm_eq_diag_add_two_mul_pairs
    (fun i j : Fin 5 => (α i + α j) ^ m) (fun i j => by rw [add_comm])
  have hdiag : (∑ i : Fin 5, (α i + α i) ^ m) = (2 : L) ^ m * garlingPowerSum α m := by
    unfold garlingPowerSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← two_mul, mul_pow]
  have hbinom : (∑ i : Fin 5, ∑ j : Fin 5, (α i + α j) ^ m) =
      ∑ r ∈ Finset.range (m + 1),
        (Nat.choose m r : L) * garlingPowerSum α r * garlingPowerSum α (m - r) := by
    calc (∑ i : Fin 5, ∑ j : Fin 5, (α i + α j) ^ m)
        = ∑ i : Fin 5, ∑ j : Fin 5, ∑ r ∈ Finset.range (m + 1),
            (α i) ^ r * (α j) ^ (m - r) * (Nat.choose m r : L) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [add_pow]
      _ = ∑ i : Fin 5, ∑ r ∈ Finset.range (m + 1), ∑ j : Fin 5,
            (Nat.choose m r : L) * (α i) ^ r * (α j) ^ (m - r) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ r ∈ Finset.range (m + 1), ∑ i : Fin 5, ∑ j : Fin 5,
            (Nat.choose m r : L) * (α i) ^ r * (α j) ^ (m - r) := Finset.sum_comm
      _ = ∑ r ∈ Finset.range (m + 1),
            (Nat.choose m r : L) * garlingPowerSum α r * garlingPowerSum α (m - r) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          unfold garlingPowerSum
          calc (∑ i : Fin 5, ∑ j : Fin 5, (Nat.choose m r : L) * (α i) ^ r * (α j) ^ (m - r))
              = ∑ i : Fin 5, ((Nat.choose m r : L) * (α i) ^ r) * ∑ j : Fin 5, (α j) ^ (m - r) := by
                refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
            _ = (∑ i : Fin 5, (Nat.choose m r : L) * (α i) ^ r) * ∑ j : Fin 5, (α j) ^ (m - r) :=
                (Finset.sum_mul _ _ _).symm
            _ = (Nat.choose m r : L) * (∑ i : Fin 5, (α i) ^ r) * ∑ j : Fin 5, (α j) ^ (m - r) := by
                rw [← Finset.mul_sum]
  have hpairs : (∑ t : Fin 10, (α (quinticPairIdx t).1 + α (quinticPairIdx t).2) ^ m) =
      garlingPowerSum γ m := rfl
  rw [hbinom, hdiag, hpairs] at hdouble
  linear_combination -hdouble

/-- Helper: explicit integer factorization of the pair-sum resolvent of `x⁵ - 5x + 12` via Newton's
power-sum identities (`Chapter14.exercise_14_2_iii`). -/
private theorem pairSumResolvent_example_b {L : Type*} [Field L] [Algebra ℚ L]
    {α : Fin 5 → L}
    (hexp : GarlingSplitsExplicit ℚ L (Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X + Polynomial.C 12) 5 1 α) :
    let g1 : ℚ[X] := Polynomial.X ^ 5 + Polynomial.C 5 * Polynomial.X ^ 3 +
      Polynomial.C 10 * Polynomial.X ^ 2 + Polynomial.C 10 * Polynomial.X + Polynomial.C 4
    let g2 : ℚ[X] := Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X ^ 3 -
      Polynomial.C 10 * Polynomial.X ^ 2 + Polynomial.C 30 * Polynomial.X - Polynomial.C 36
    garlingPairSumResolvent α = (g1 * g2).map (algebraMap ℚ L) := by
  intro g1 g2
  let fb : ℚ[X] := Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X + Polynomial.C 12
  have hfb_deg : fb.natDegree = 5 := by dsimp [fb]; compute_degree!
  have hfb0 : fb ≠ 0 := fun h0 => by simp [h0] at hfb_deg
  have hfb_c : ∀ k : ℕ, fb.coeff k = match k with
      | 0 => 12 | 1 => -5 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 1 | _ => 0 := by
    intro k
    have hform : fb = Polynomial.X ^ 5 + Polynomial.C (-5 : ℚ) * Polynomial.X + Polynomial.C 12 := by
      dsimp [fb]; simp; ring
    rw [hform]
    rcases k with _ | _ | _ | _ | _ | _ | k
    all_goals simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  have hexp' : GarlingSplitsExplicit ℚ L fb 5 (fb.coeff 5) α := by
    rw [hfb_c 5]; exact hexp
  have hnewt := Chapter14.exercise_14_2_iii hfb0 (show garlingDegree fb hfb0 = 5 from hfb_deg) hexp'
  -- Compute `S_k = garlingPowerSum α k` for `k = 0..10`:
  have hS0 : garlingPowerSum α 0 = 5 := by simp [garlingPowerSum]
  have hS1 : garlingPowerSum α 1 = 0 := by
    have h := hnewt.1 1 (by decide) (by decide)
    simp only [Finset.Icc_self, Finset.sum_singleton, hfb_c, map_zero, map_one, one_mul,
      mul_zero, zero_add] at h
    exact h
  have hS2 : garlingPowerSum α 2 = 0 := by
    have h := hnewt.1 2 (by decide) (by decide)
    rw [show Finset.Icc 1 2 = {1, 2} from by decide, Finset.sum_pair (by decide)] at h
    simp only [hfb_c, hS1, map_zero, map_one, one_mul, mul_zero, zero_add] at h
    exact h
  have hS3 : garlingPowerSum α 3 = 0 := by
    have h := hnewt.1 3 (by decide) (by decide)
    rw [show Finset.Icc 1 3 = {1, 2, 3} from by decide,
      Finset.sum_insert (by decide), Finset.sum_pair (by decide)] at h
    simp only [hfb_c, hS1, hS2, map_zero, map_one, one_mul, mul_zero, zero_add] at h
    exact h
  have hS4 : garlingPowerSum α 4 = 20 := by
    have h := hnewt.1 4 (by decide) (by decide)
    rw [show Finset.Icc 1 4 = {1, 2, 3, 4} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by decide)] at h
    simp only [hfb_c, hS1, hS2, hS3, map_zero, map_one, map_neg, map_ofNat] at h
    linear_combination h
  have hS5 : garlingPowerSum α 5 = -60 := by
    have h := hnewt.1 5 (by decide) (by decide)
    rw [show Finset.Icc 1 5 = {1, 2, 3, 4, 5} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_pair (by decide)] at h
    simp only [hfb_c, hS1, hS2, hS3, hS4, map_zero, map_one, map_neg, map_ofNat] at h
    linear_combination h
  have hSrec : ∀ k : ℕ, 1 ≤ k →
      garlingPowerSum α (k + 5) = 5 * garlingPowerSum α (k + 1) - 12 * garlingPowerSum α k := by
    intro k hk
    have h := hnewt.2 k hk
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, hfb_c,
      map_zero, map_one, map_neg, map_ofNat] at h
    linear_combination h
  have hS6 : garlingPowerSum α 6 = 0 := by rw [hSrec 1 (by decide), hS2, hS1]; ring
  have hS7 : garlingPowerSum α 7 = 0 := by rw [hSrec 2 (by decide), hS3, hS2]; ring
  have hS8 : garlingPowerSum α 8 = 100 := by rw [hSrec 3 (by decide), hS4, hS3]; ring
  have hS9 : garlingPowerSum α 9 = -540 := by rw [hSrec 4 (by decide), hS5, hS4]; ring
  have hS10 : garlingPowerSum α 10 = 720 := by rw [hSrec 5 (by decide), hS6, hS5]; ring
  -- Compute `P_m = garlingPowerSum γ m` for `m = 1..10`:
  let γ : Fin 10 → L := fun t => α (quinticPairIdx t).1 + α (quinticPairIdx t).2
  have hcharL : ∀ n : ℕ, 0 < n → (n : L) ≠ 0 := fun n hn => by
    have hm : algebraMap ℚ L (n : ℚ) = (n : L) := map_natCast (algebraMap ℚ L) n
    rw [← hm]; exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hn.ne')
  have h2L : (2 : L) ≠ 0 := hcharL 2 (by decide)
  have hP1 : garlingPowerSum γ 1 = 0 := by
    have h := two_mul_garlingPowerSum_pairs α 1
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.choose, hS0, hS1] at h
    apply mul_left_cancel₀ h2L; linear_combination h
  have hP2 : garlingPowerSum γ 2 = 0 := by
    have h := two_mul_garlingPowerSum_pairs α 2
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.choose, hS0, hS1, hS2] at h
    apply mul_left_cancel₀ h2L; linear_combination h
  have hP3 : garlingPowerSum γ 3 = 0 := by
    have h := two_mul_garlingPowerSum_pairs α 3
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.choose, hS0, hS1, hS2, hS3] at h
    apply mul_left_cancel₀ h2L; linear_combination h
  have hP4 : garlingPowerSum γ 4 = -60 := by
    have h := two_mul_garlingPowerSum_pairs α 4
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.choose, hS0, hS1, hS2, hS3, hS4] at h
    apply mul_left_cancel₀ h2L; norm_num at h; linear_combination h
  have hP5 : garlingPowerSum γ 5 = 660 := by
    have h := two_mul_garlingPowerSum_pairs α 5
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.choose, hS0, hS1, hS2, hS3, hS4, hS5] at h
    apply mul_left_cancel₀ h2L; norm_num at h; linear_combination h
  have hP6 : garlingPowerSum γ 6 = 0 := by
    have h := two_mul_garlingPowerSum_pairs α 6
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.choose, hS0, hS1, hS2, hS3, hS4, hS5, hS6] at h
    apply mul_left_cancel₀ h2L; ring_nf at h; linear_combination h
  have hP7 : garlingPowerSum γ 7 = 0 := by
    have h := two_mul_garlingPowerSum_pairs α 7
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.choose, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7] at h
    apply mul_left_cancel₀ h2L; ring_nf at h; linear_combination h
  have hP8 : garlingPowerSum γ 8 = 1700 := by
    have h := two_mul_garlingPowerSum_pairs α 8
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.choose, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8] at h
    apply mul_left_cancel₀ h2L; norm_num at h; linear_combination h
  have hP9 : garlingPowerSum γ 9 = -15660 := by
    have h := two_mul_garlingPowerSum_pairs α 9
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.choose, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9] at h
    apply mul_left_cancel₀ h2L; norm_num at h; linear_combination h
  have hP10 : garlingPowerSum γ 10 = 88560 := by
    have h := two_mul_garlingPowerSum_pairs α 10
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.choose, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10] at h
    apply mul_left_cancel₀ h2L; norm_num at h; linear_combination h
  -- Apply Newton's identities to `G = garlingPairSumResolvent α` over `L` to determine all 11 coefficients:
  let G : L[X] := garlingPairSumResolvent α
  have hG_mon : G.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun t _ => Polynomial.monic_X_sub_C _
  have hG_deg : G.natDegree = 10 := by
    dsimp [G, garlingPairSumResolvent]
    rw [Polynomial.natDegree_prod_of_monic _ _ fun t _ => Polynomial.monic_X_sub_C _]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
  have hG_c10 : G.coeff 10 = 1 := by rw [← hG_deg]; exact hG_mon.coeff_natDegree
  have hG_exp : GarlingSplitsExplicit L L G 10 (G.coeff 10) γ := by
    unfold GarlingSplitsExplicit
    rw [hG_c10, map_one, Polynomial.C_1, one_mul, Algebra.algebraMap_self, Polynomial.map_id]
    rfl
  have hG_newt := (Chapter14.exercise_14_2_iii (K := L) (L := L) hG_mon.ne_zero
    (show garlingDegree G hG_mon.ne_zero = 10 from hG_deg) hG_exp).1
  have hGc9 : G.coeff 9 = 0 := by
    have h := hG_newt 1 (by decide) (by decide)
    simp only [Finset.Icc_self, Finset.sum_singleton, Algebra.algebraMap_self, RingHom.id_apply,
      hG_c10, hP1] at h
    linear_combination h
  have hGc8 : G.coeff 8 = 0 := by
    have h := hG_newt 2 (by decide) (by decide)
    rw [show Finset.Icc 1 2 = {1, 2} from by decide, Finset.sum_pair (by decide)] at h
    simp only [Algebra.algebraMap_self, RingHom.id_apply, hG_c10, hGc9, hP1, hP2] at h
    apply mul_left_cancel₀ (hcharL 2 (by decide)); linear_combination h
  have hGc7 : G.coeff 7 = 0 := by
    have h := hG_newt 3 (by decide) (by decide)
    rw [show Finset.Icc 1 3 = {1, 2, 3} from by decide,
      Finset.sum_insert (by decide), Finset.sum_pair (by decide)] at h
    simp only [Algebra.algebraMap_self, RingHom.id_apply, hG_c10, hGc9, hGc8, hP1, hP2, hP3] at h
    apply mul_left_cancel₀ (hcharL 3 (by decide)); linear_combination h
  have hGc6 : G.coeff 6 = 15 := by
    have h := hG_newt 4 (by decide) (by decide)
    rw [show Finset.Icc 1 4 = {1, 2, 3, 4} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by decide)] at h
    simp only [Algebra.algebraMap_self, RingHom.id_apply, hG_c10, hGc9, hGc8, hGc7,
      hP1, hP2, hP3, hP4] at h
    apply mul_left_cancel₀ (hcharL 4 (by decide)); norm_num at h; linear_combination h
  have hGc5 : G.coeff 5 = -132 := by
    have h := hG_newt 5 (by decide) (by decide)
    rw [show Finset.Icc 1 5 = {1, 2, 3, 4, 5} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_pair (by decide)] at h
    simp only [Algebra.algebraMap_self, RingHom.id_apply, hG_c10, hGc9, hGc8, hGc7, hGc6,
      hP1, hP2, hP3, hP4, hP5] at h
    apply mul_left_cancel₀ (hcharL 5 (by decide)); norm_num at h; linear_combination h
  have hGc4 : G.coeff 4 = 0 := by
    have h := hG_newt 6 (by decide) (by decide)
    rw [show Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by decide)] at h
    simp only [Algebra.algebraMap_self, RingHom.id_apply, hG_c10, hGc9, hGc8, hGc7, hGc6, hGc5,
      hP1, hP2, hP3, hP4, hP5, hP6] at h
    apply mul_left_cancel₀ (hcharL 6 (by decide)); ring_nf at h; linear_combination h
  have hGc3 : G.coeff 3 = 0 := by
    have h := hG_newt 7 (by decide) (by decide)
    rw [show Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_pair (by decide)] at h
    simp only [Algebra.algebraMap_self, RingHom.id_apply, hG_c10, hGc9, hGc8, hGc7, hGc6, hGc5, hGc4,
      hP1, hP2, hP3, hP4, hP5, hP6, hP7] at h
    apply mul_left_cancel₀ (hcharL 7 (by decide)); ring_nf at h; linear_combination h
  have hGc2 : G.coeff 2 = -100 := by
    have h := hG_newt 8 (by decide) (by decide)
    rw [show Finset.Icc 1 8 = {1, 2, 3, 4, 5, 6, 7, 8} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by decide)] at h
    simp only [Algebra.algebraMap_self, RingHom.id_apply, hG_c10, hGc9, hGc8, hGc7, hGc6, hGc5,
      hGc4, hGc3, hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8] at h
    apply mul_left_cancel₀ (hcharL 8 (by decide)); norm_num at h; linear_combination h
  have hGc1 : G.coeff 1 = -240 := by
    have h := hG_newt 9 (by decide) (by decide)
    rw [show Finset.Icc 1 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_pair (by decide)] at h
    simp only [Algebra.algebraMap_self, RingHom.id_apply, hG_c10, hGc9, hGc8, hGc7, hGc6, hGc5,
      hGc4, hGc3, hGc2, hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9] at h
    apply mul_left_cancel₀ (hcharL 9 (by decide)); norm_num at h; linear_combination h
  have hGc0 : G.coeff 0 = -144 := by
    have h := hG_newt 10 (by decide) (by decide)
    rw [show Finset.Icc 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by decide)] at h
    simp only [Algebra.algebraMap_self, RingHom.id_apply, hG_c10, hGc9, hGc8, hGc7, hGc6, hGc5,
      hGc4, hGc3, hGc2, hGc1, hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9, hP10] at h
    apply mul_left_cancel₀ (hcharL 10 (by decide)); norm_num at h; linear_combination h
  -- Match coefficients with `g1 * g2`:
  have hg12_eq : g1 * g2 =
      Polynomial.X ^ 10 + Polynomial.C 15 * Polynomial.X ^ 6 - Polynomial.C 132 * Polynomial.X ^ 5 -
        Polynomial.C 100 * Polynomial.X ^ 2 - Polynomial.C 240 * Polynomial.X - Polynomial.C 144 := by
    dsimp [g1, g2]
    simp only [map_ofNat]
    ring
  rw [hg12_eq]
  have hmap_eq : (Polynomial.X ^ 10 + Polynomial.C (15 : ℚ) * Polynomial.X ^ 6 -
      Polynomial.C 132 * Polynomial.X ^ 5 - Polynomial.C 100 * Polynomial.X ^ 2 -
      Polynomial.C 240 * Polynomial.X - Polynomial.C 144).map (algebraMap ℚ L) =
      Polynomial.X ^ 10 + Polynomial.C (15 : L) * Polynomial.X ^ 6 -
        Polynomial.C (132 : L) * Polynomial.X ^ 5 - Polynomial.C (100 : L) * Polynomial.X ^ 2 -
        Polynomial.C (240 : L) * Polynomial.X - Polynomial.C (144 : L) := by
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C]
    simp only [map_ofNat]
  rw [hmap_eq]
  ext k
  change G.coeff k = _
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  · simp only [hGc0, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]; norm_num
  · simp only [hGc1, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]; norm_num
  · simp only [hGc2, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]; norm_num
  · simp only [hGc3, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]; norm_num
  · simp only [hGc4, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]; norm_num
  · simp only [hGc5, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]; norm_num
  · simp only [hGc6, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]; norm_num
  · simp only [hGc7, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]; norm_num
  · simp only [hGc8, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]; norm_num
  · simp only [hGc9, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]; norm_num
  · simp only [hG_c10, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]; norm_num
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hG_deg]; omega)]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    simp

/-- Helper: a polynomial of degree `2` or `3` over a field with no root in that field is irreducible. -/
private theorem irreducible_of_natDegree_le_three_of_no_root {K : Type*} [Field K] {q : K[X]}
    (h2 : 2 ≤ q.natDegree) (h3 : q.natDegree ≤ 3) (hno : ∀ c : K, q.eval c ≠ 0) :
    Irreducible q := by
  have hq0 : q ≠ 0 := fun h => by simp [h] at h2
  refine ⟨fun hu => by have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega, fun a b hab => ?_⟩
  have ha0 : a ≠ 0 := fun h => hq0 (by rw [hab, h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hq0 (by rw [hab, h, mul_zero])
  have hsum : a.natDegree + b.natDegree = q.natDegree := by
    rw [hab, Polynomial.natDegree_mul ha0 hb0]
  by_cases ha : a.natDegree = 0
  · left
    exact Polynomial.isUnit_iff_degree_eq_zero.mpr
      (by rw [Polynomial.degree_eq_natDegree ha0, ha]; rfl)
  · by_cases hb : b.natDegree = 0
    · right
      exact Polynomial.isUnit_iff_degree_eq_zero.mpr
        (by rw [Polynomial.degree_eq_natDegree hb0, hb]; rfl)
    · exfalso
      have h1 : a.natDegree = 1 ∨ b.natDegree = 1 := by omega
      have hex_root : ∀ p : K[X], p.natDegree = 1 → p ∣ q → False := fun p hp1 hdvd => by
        have hlc : p.leadingCoeff ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mpr (fun h => by simp [h] at hp1)
        let r : K := -(p.coeff 0) / p.leadingCoeff
        have hp_eval : p.eval r = 0 := by
          rw [Polynomial.eval_eq_sum_range' (show p.natDegree < 2 by omega),
            Finset.sum_range_succ, Finset.sum_range_one]
          have hcoeff1 : p.coeff 1 = p.leadingCoeff := by rw [← hp1]; rfl
          simp only [pow_zero, mul_one, pow_one, hcoeff1, r]
          field_simp [hlc]
          ring
        rcases hdvd with ⟨c, rfl⟩
        exact hno r (by rw [Polynomial.eval_mul, hp_eval, zero_mul])
      rcases h1 with ha1 | hb1
      · exact hex_root a ha1 ⟨b, hab⟩
      · exact hex_root b hb1 ⟨a, hab.trans (mul_comm a b)⟩

/-- Helper for §20.3 Example `(b)`: universe-polymorphic Galois-group computation for
`f_b = x⁵ - 5x + 12` over any splitting field `L : Type u`. -/
private theorem example_b_galois_aux
    (hirr : Irreducible (Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X + Polynomial.C 12 : ℚ[X]))
    (hdisc_sq : ∃ d : ℚ, d ^ 2 = garlingDiscriminant
      (Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X + Polynomial.C 12 : ℚ[X]))
    {L : Type u} [Field L] [Algebra ℚ L]
    (hsfL : IsGarlingSplittingFieldExtension ℚ L
      (Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X + Polynomial.C 12 : ℚ[X])) :
    Nat.card (GarlingPolyGaloisGroup ℚ L
      (Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X + Polynomial.C 12 : ℚ[X])) = 10 ∧
    Nonempty (GarlingPolyGaloisGroup ℚ L
      (Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X + Polynomial.C 12 : ℚ[X]) ≃* DihedralGroup 5) ∧
    Nonempty (GarlingPolyGaloisGroup ℚ L
      (Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X + Polynomial.C 12 : ℚ[X]) ≃* pentagonDihedral) := by
  classical
  let f : ℚ[X] := Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X + Polynomial.C 12
  let fZ : ℤ[X] := Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X + Polynomial.C 12
  have hf_map : fZ.map (algebraMap ℤ ℚ) = f := by simp [fZ, f, map_ofNat]
  have hfZ_mon : fZ.Monic := by
    have hform : fZ = Polynomial.X ^ 5 + (-(Polynomial.C (5 : ℤ) * Polynomial.X) + Polynomial.C 12) := by
      dsimp [fZ]; ring
    rw [hform]
    have hlt : (-(Polynomial.C (5 : ℤ) * Polynomial.X) + Polynomial.C 12).natDegree < 5 := by compute_degree!
    exact Polynomial.monic_X_pow_add (Polynomial.degree_lt_iff_coeff_zero _ _ |>.mpr fun m hm =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  have hf_deg : f.natDegree = 5 := by dsimp [f]; compute_degree!
  -- `2 ∣ |Γ_ℚ(f)|` via `Theorem 20.2` at `p = 3` (`f̄ = X (X² + X + 2)(X² + 2X + 2)`):
  have h2_dvd : 2 ∣ Nat.card (GarlingPolyGaloisGroup ℚ L f) := by
    have hq_no_root : ∀ c : ZMod 3, c ^ 2 + c + 2 ≠ 0 := by decide
    have hfac_list : zmodListEq
        (zmodListMul (p := 3) [2, 1, 1] [0, 2, 2, 1]) [0, 1, 0, 0, 0, 1] = true := by decide
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    let q : (ZMod 3)[X] := Polynomial.X ^ 2 + Polynomial.X + Polynomial.C 2
    have hq_deg : q.natDegree = 2 := by dsimp [q]; compute_degree!
    have hq_irr : Irreducible q :=
      irreducible_of_natDegree_le_three_of_no_root (by omega) (by omega) fun c hc =>
        hq_no_root c (by simpa [q] using hc)
    have hq_dvd : q ∣ modPrimePolyHom 3 fZ := by
      refine ⟨Polynomial.X ^ 3 + Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 2 * Polynomial.X, ?_⟩
      have hpoly := zmodListToPoly_eq_of_listEq hfac_list
      simp only [zmodListToPoly_mul, zmodListToPoly, map_zero, map_one, zero_add] at hpoly
      have hfeq : modPrimePolyHom 3 fZ = Polynomial.X ^ 5 + Polynomial.X := by
        dsimp [modPrimePolyHom, fZ]
        rw [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
          Polynomial.map_X, Polynomial.map_C, Polynomial.map_C]
        change Polynomial.X ^ 5 - Polynomial.C ((5 : ℤ) : ZMod 3) * Polynomial.X +
          Polynomial.C ((12 : ℤ) : ZMod 3) = _
        have h5 : ((5 : ℤ) : ZMod 3) = 2 := rfl
        have h12 : ((12 : ℤ) : ZMod 3) = 0 := rfl
        have hneg2 : -(Polynomial.C (2 : ZMod 3)) = 1 := by
          rw [← map_neg, show -(2 : ZMod 3) = 1 from rfl, map_one]
        rw [h5, h12, map_zero, add_zero]
        linear_combination Polynomial.X * hneg2
      rw [hfeq]
      dsimp [q]
      linear_combination -hpoly
    let fbar := modPrimePolyHom 3 fZ
    let M := Polynomial.SplittingField fbar
    have hsfM : IsGarlingSplittingFieldExtension (ZMod 3) M fbar :=
      (isGarlingSplittingFieldExtension_iff (ZMod 3) M fbar).mpr inferInstance
    have hsfM_m := (isGarlingSplittingFieldExtension_iff (ZMod 3) M fbar).mp hsfM
    have hq_splits : (q.map (algebraMap (ZMod 3) M)).Splits :=
      Polynomial.Splits.of_dvd hsfM_m.splits (Polynomial.map_ne_zero (hfZ_mon.map _).ne_zero)
        (Polynomial.map_dvd _ hq_dvd)
    have hq_roots_pos : 0 < (q.map (algebraMap (ZMod 3) M)).roots.card := by
      rw [Polynomial.splits_iff_card_roots.mp hq_splits,
        Polynomial.natDegree_map_eq_of_injective (algebraMap (ZMod 3) M).injective, hq_deg]
      decide
    obtain ⟨β, hβ⟩ := Multiset.card_pos_iff_exists_mem.mp hq_roots_pos
    have hβ_root : Polynomial.aeval β q = 0 := by
      have h1 := (Polynomial.mem_roots (Polynomial.map_ne_zero hq_irr.ne_zero)).mp hβ
      rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    have hq_mon : q.Monic := by
      dsimp [q]
      rw [add_assoc]
      exact Polynomial.monic_X_pow_add (Polynomial.degree_lt_iff_coeff_zero _ _ |>.mpr fun m hm =>
        Polynomial.coeff_eq_zero_of_natDegree_lt (by
          have : (Polynomial.X + Polynomial.C (2 : ZMod 3)).natDegree < 2 := by compute_degree!
          omega))
    have hmin_β : minpoly (ZMod 3) β = q := (minpoly.eq_of_irreducible_of_monic hq_irr hβ_root hq_mon).symm
    have h2_dvd_M : 2 ∣ Module.finrank (ZMod 3) M := by
      let Kβ := IntermediateField.adjoin (ZMod 3) ({β} : Set M)
      have hfin_β : Module.finrank (ZMod 3) Kβ = 2 := by
        rw [IntermediateField.adjoin.finrank ⟨q, hq_mon, hβ_root⟩, hmin_β, hq_deg]
      have _ : Module.Finite (ZMod 3) M := Polynomial.IsSplittingField.finiteDimensional M fbar
      have _ : Module.Finite (ZMod 3) Kβ := inferInstance
      have _ : Module.Finite Kβ M := Module.Finite.right (ZMod 3) Kβ M
      have hmul := Module.finrank_mul_finrank (ZMod 3) Kβ M
      rw [hfin_β] at hmul
      exact ⟨Module.finrank Kβ M, hmul.symm⟩
    have _ : FiniteDimensional (ZMod 3) M := Polynomial.IsSplittingField.finiteDimensional M fbar
    have _ : Normal (ZMod 3) M := Normal.of_isSplittingField fbar
    have _ : IsGalois (ZMod 3) M := ⟨⟩
    have hcardM : Nat.card (GarlingPolyGaloisGroup (ZMod 3) M fbar) = Module.finrank (ZMod 3) M :=
      IsGalois.card_aut_eq_finrank (ZMod 3) M
    have hdistinct_L : ¬ HasGarlingRepeatedRoot ℚ L f := by
      rcases hsfL.1 with ⟨m, c, α, hexp⟩
      exact fun hrep => ((injective_roots_iff_separable_and_not_repeated hirr.ne_zero hexp).2.mpr hrep)
        ((injective_roots_iff_separable_and_not_repeated hirr.ne_zero hexp).1.mpr hirr.separable)
    have h20_2 := theorem_20_2 hfZ_mon (by decide : Nat.Prime 3) (hf_map ▸ hsfL) (hf_map ▸ hdistinct_L) hsfM
    obtain ⟨H, ⟨eH⟩⟩ := h20_2.2
    have hdvd : Nat.card (GarlingPolyGaloisGroup (ZMod 3) M fbar) ∣
        Nat.card (GarlingPolyGaloisGroup ℚ L f) := by
      have h1 : Nat.card (GarlingPolyGaloisGroup (ZMod 3) M fbar) = Nat.card H :=
        Nat.card_congr eH.toEquiv
      have h2 : Nat.card H ∣ Nat.card (GarlingPolyGaloisGroup ℚ L (fZ.map (algebraMap ℤ ℚ))) :=
        Subgroup.card_subgroup_dvd_card H
      rw [hf_map] at h2
      exact h1 ▸ h2
    exact dvd_trans (hcardM ▸ h2_dvd_M) hdvd
  -- Rule out `C₅` and `A₅` via discriminant square, `2 ∣ |Γ|`, and pair-sum resolvent `g = g1 * g2`:
  obtain ⟨_, ⟨e⟩, huniq, h5way, _, _, hdisc_iff⟩ :=
    section_20_3_quintic_galois_classification hirr hf_deg hsfL
  have hcard_3 := hdisc_iff.mp hdisc_sq
  have hnot5 : Nat.card (GarlingPolyGaloisGroup ℚ L f) ≠ 5 := fun h5 => by
    rw [h5] at h2_dvd; exact absurd h2_dvd (by decide)
  have hnot60 : Nat.card (GarlingPolyGaloisGroup ℚ L f) ≠ 60 := by
    intro h60
    let φ := garlingRootLabellingPermHom e
    have hφ_inj : Function.Injective φ := garlingRootLabellingPermHom_injective_ch20 hsfL e
    obtain ⟨i, hconj_i, _⟩ := huniq e
    have hcard_i : (![5, 10, 20, 60, 120] : Fin 5 → ℕ) i = 60 := by
      have h1 : Nat.card φ.range = 60 := by
        rw [← h60]; exact (Nat.card_congr (Equiv.ofBijective φ.rangeRestrict
          ⟨fun a b h => hφ_inj (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩)).symm
      calc (![5, 10, 20, 60, 120] : Fin 5 → ℕ) i
          = Nat.card (s5TransitiveModel i) := (exercise_11_5_s5.1 i).symm
        _ = Nat.card φ.range := isConjugateSubgroup_natCard_eq hconj_i
        _ = 60 := h1
    have hi3 : i = 3 := by fin_cases i <;> first | rfl | exact absurd hcard_i (by decide)
    subst hi3
    have hrange_A5 : φ.range = alternatingGroup (Fin 5) := by
      rcases hconj_i with ⟨g, hg⟩
      rw [← hg]; dsimp [s5TransitiveModel]
      ext σ; simp only [Subgroup.mem_map]
      constructor
      · rintro ⟨τ, hτ, rfl⟩; exact Subgroup.Normal.conj_mem inferInstance τ hτ g
      · intro hσ
        refine ⟨g⁻¹ * σ * g, by simpa using Subgroup.Normal.conj_mem inferInstance σ hσ g⁻¹, ?_⟩
        change MulAut.conj g (g⁻¹ * σ * g) = σ
        rw [MulAut.conj_apply]
        group
    have hdist := exercise_20_6_perm hf_deg hsfL e (hrange_A5 ▸ pentagonDihedral_le_alternatingGroup)
    let α : Fin 5 → L := fun k => (e k).1
    have hmon_f : f.Monic := hf_map ▸ hfZ_mon.map _
    have hexp_α : GarlingSplitsExplicit ℚ L f 5 1 α := by
      unfold GarlingSplitsExplicit
      rw [map_one, Polynomial.C_1, one_mul]
      have hpw : Set.Pairwise (Finset.univ : Finset (Fin 5)) fun a b =>
          IsCoprime (Polynomial.X - Polynomial.C (α a)) (Polynomial.X - Polynomial.C (α b)) := by
        intro a _ b _ hab
        exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr
          (sub_ne_zero.mpr fun h => hab (e.injective (Subtype.ext h))))
      have hdvd : (∏ a : Fin 5, (Polynomial.X - Polynomial.C (α a))) ∣ f.map (algebraMap ℚ L) :=
        Finset.prod_dvd_of_coprime hpw fun a _ => Polynomial.dvd_iff_isRoot.mpr (by
          have hr : Polynomial.aeval (e a).1 f = 0 := (e a).2
          rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at hr)
      have hmon_p : (∏ a : Fin 5, (Polynomial.X - Polynomial.C (α a))).Monic :=
        Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _
      have hdeg_p : (∏ a : Fin 5, (Polynomial.X - Polynomial.C (α a))).natDegree = 5 := by
        rw [Polynomial.natDegree_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _]
        simp
      exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon_p (hmon_f.map _) hdvd
        (by rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ L).injective, hf_deg, hdeg_p])
    have hres := pairSumResolvent_example_b hexp_α
    let g1 : ℚ[X] := Polynomial.X ^ 5 + Polynomial.C 5 * Polynomial.X ^ 3 +
      Polynomial.C 10 * Polynomial.X ^ 2 + Polynomial.C 10 * Polynomial.X + Polynomial.C 4
    let g2 : ℚ[X] := Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X ^ 3 -
      Polynomial.C 10 * Polynomial.X ^ 2 + Polynomial.C 30 * Polynomial.X - Polynomial.C 36
    let γ : Fin 10 → L := fun t => α (quinticPairIdx t).1 + α (quinticPairIdx t).2
    have hγ_inj : Function.Injective γ := by
      intro t₁ t₂ ht
      have hlt1 : (quinticPairIdx t₁).1 < (quinticPairIdx t₁).2 := by fin_cases t₁ <;> decide
      have hlt2 : (quinticPairIdx t₂).1 < (quinticPairIdx t₂).2 := by fin_cases t₂ <;> decide
      obtain ⟨h1, h2⟩ := hdist _ _ _ _ hlt1 hlt2 ht
      have hpair : quinticPairIdx t₁ = quinticPairIdx t₂ := Prod.ext h1 h2
      have hq_inj : Function.Injective quinticPairIdx := by decide
      exact hq_inj hpair
    have hγ0_root : Polynomial.aeval (γ 0) (g1 * g2) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, ← hres]
      dsimp [garlingPairSumResolvent]
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ 0) (by simp [γ])
    have hex_q : ∃ q : ℚ[X], q.natDegree = 5 ∧ Polynomial.aeval (γ 0) q = 0 := by
      rw [map_mul] at hγ0_root
      rcases mul_eq_zero.mp hγ0_root with h1 | h2
      · exact ⟨g1, by dsimp [g1]; compute_degree!, h1⟩
      · exact ⟨g2, by dsimp [g2]; compute_degree!, h2⟩
    obtain ⟨q, hq_deg, hq0⟩ := hex_q
    have hq_ne0 : q ≠ 0 := fun h0 => by simp [h0] at hq_deg
    have hall_q : ∀ t : Fin 10, Polynomial.aeval (γ t) q = 0 := by
      intro t
      obtain ⟨π, hπA5, hπ_pair⟩ := alternatingGroup_five_transitive_on_pairs t
      have hπ_mem : π ∈ φ.range := hrange_A5.symm ▸ hπA5
      obtain ⟨σ, hσ⟩ := hπ_mem
      have hσ_α : ∀ k : Fin 5, σ (α k) = α (π k) := fun k => by
        have h1 := congrArg (fun p : Equiv.Perm (Fin 5) => (e (p k)).1) hσ
        simpa [φ, α, garlingRootLabellingPermHom_apply] using h1
      have hσ_γ0 : σ (γ 0) = γ t := by
        change σ (α 0 + α 1) = α (quinticPairIdx t).1 + α (quinticPairIdx t).2
        rw [map_add, hσ_α 0, hσ_α 1]
        rcases hπ_pair with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1, h2, add_comm]
      rw [← hσ_γ0]
      change Polynomial.aeval (σ.toAlgHom (γ 0)) q = 0
      rw [Polynomial.aeval_algHom_apply, hq0, map_zero]
    have h10_le5 : 10 ≤ 5 := by
      let emb : Fin 10 ↪ (q.map (algebraMap ℚ L)).roots.toFinset :=
        ⟨fun t => ⟨γ t, by
          simp only [Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.map_ne_zero hq_ne0),
            Polynomial.IsRoot.def]
          have ht := hall_q t
          rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at ht⟩,
         fun _ _ h => hγ_inj (by simpa using congrArg Subtype.val h)⟩
      calc 10 = Fintype.card (Fin 10) := (Fintype.card_fin 10).symm
        _ ≤ Fintype.card (q.map (algebraMap ℚ L)).roots.toFinset :=
            Fintype.card_le_of_injective emb emb.injective
        _ = (q.map (algebraMap ℚ L)).roots.toFinset.card := Fintype.card_coe _
        _ ≤ (q.map (algebraMap ℚ L)).roots.card := Multiset.toFinset_card_le _
        _ ≤ (q.map (algebraMap ℚ L)).natDegree := Polynomial.card_roots' _
        _ = 5 := by rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ L).injective, hq_deg]
    omega
  have hcard10 : Nat.card (GarlingPolyGaloisGroup ℚ L f) = 10 := by
    rcases hcard_3 with h5 | h10 | h60
    · exact absurd h5 hnot5
    · exact h10
    · exact absurd h60 hnot60
  have heD10 : Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* DihedralGroup 5) := by
    rcases h5way with h | h | h | h | h
    · exfalso; obtain ⟨e0⟩ := h; have hc := Nat.card_congr e0.toEquiv; rw [hcard10] at hc
      have h5 : Nat.card (Multiplicative (ZMod 5)) = 5 := Nat.card_eq_fintype_card.trans (by decide)
      omega
    · exact h
    · exfalso; obtain ⟨e2⟩ := h; have hc := Nat.card_congr e2.toEquiv
      rw [hcard10, garlingAffineGroup_card (by decide : Nat.Prime 5)] at hc; norm_num at hc
    · exfalso; obtain ⟨e3⟩ := h; have hc := Nat.card_congr e3.toEquiv
      have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := exercise_11_5_s5.1 3
      rw [hcard10, h60] at hc; omega
    · exfalso; obtain ⟨e4⟩ := h; have hc := Nat.card_congr e4.toEquiv
      rw [hcard10, Nat.card_perm, Nat.card_fin] at hc; norm_num at hc
  obtain ⟨eD⟩ := heD10
  exact ⟨hcard10, ⟨eD⟩, ⟨eD.trans pentagonDihedralMulEquiv⟩⟩

/-- **§20.3 Example `(b)` (printed pp. 161–162 / PDF pp. 169–170):**
`f_b = x⁵ - 5x + 12 ∈ ℚ[x]` is irreducible of degree `5` (certified modulo `7`), has discriminant
`Δ(f_b) = 2¹² · 5⁶ = (2⁶ · 5³)²`, has pair-sum resolvent
`g(x) = x¹⁰ + 15x⁶ - 132x⁵ - 100x² - 240x - 144 = (x⁵ + 5x³ + 10x² + 10x + 4)(x⁵ - 5x³ - 10x² + 30x - 36)`,
has **exactly `1` real root**, is solvable by radicals, and for every splitting field `L : ℚ` has
`Γ_ℚ(f_b) ≃* DihedralGroup 5` (and `≃* pentagonDihedral`, order `10`). -/
theorem section_20_3_example_b :
    let f : ℚ[X] := Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X + Polynomial.C 12
    Irreducible f ∧
    f.natDegree = 5 ∧
    garlingDiscriminant f = 2 ^ 12 * 5 ^ 6 ∧
    (∃ d : ℚ, d ^ 2 = garlingDiscriminant f) ∧
    {x : ℝ | Polynomial.aeval x f = 0}.ncard = 1 ∧
    IsGarlingSolvableByRadicals f ∧
    ∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L f →
      Nat.card (GarlingPolyGaloisGroup ℚ L f) = 10 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* DihedralGroup 5) ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* pentagonDihedral) := by
  classical
  intro f
  let fZ : ℤ[X] := Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X + Polynomial.C 12
  have hf_map : fZ.map (algebraMap ℤ ℚ) = f := by
    simp [fZ, f, map_ofNat]
  have hfZ_mon : fZ.Monic := by
    have hform : fZ = Polynomial.X ^ 5 + (-(Polynomial.C (5 : ℤ) * Polynomial.X) + Polynomial.C 12) := by
      dsimp [fZ]; ring
    rw [hform]
    have hlt : (-(Polynomial.C (5 : ℤ) * Polynomial.X) + Polynomial.C 12).natDegree < 5 := by compute_degree!
    exact Polynomial.monic_X_pow_add (Polynomial.degree_lt_iff_coeff_zero _ _ |>.mpr fun m hm =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  have hfZ_deg : fZ.natDegree = 5 := by dsimp [fZ]; compute_degree!
  have hf_deg : f.natDegree = 5 := by dsimp [f]; compute_degree!
  -- 1. Irreducibility over `ℚ` via mod-7 pure-kernel Rabin certificate:
  have hirr_7 : Irreducible (modPrimePolyHom 7 fZ) := by
    let lf : List (ZMod 7) := [5, 2, 0, 0, 0, 1]
    let lq1 : List (ZMod 7) := [0, 0, 1]
    let lr1 : List (ZMod 7) := [0, 0, 2, 5]
    let lu1 : List (ZMod 7) := [3]
    let lv1 : List (ZMod 7) := [6, 5, 5]
    let lq2 : List (ZMod 7) := [1, 6, 6, 1, 2]
    let lr2 : List (ZMod 7) := [2, 3, 0, 4, 3]
    let lu2 : List (ZMod 7) := [5, 1, 4, 3]
    let lv2 : List (ZMod 7) := [2, 1, 2, 0, 6]
    have hc1 : zmodListEq (zmodListXpow (p := 7) 7) (zmodListAdd (zmodListMul lq1 lf) lr1) = true := by decide
    have hc2 : zmodListEq (zmodListComp lr1 lr1) (zmodListAdd (zmodListMul lq2 lf) lr2) = true := by decide
    have hb1 : zmodListEq (zmodListAdd (zmodListMul lu1 lf) (zmodListMul lv1 (zmodListAdd lr1 [0, 6]))) [1] = true := by decide
    have hb2 : zmodListEq (zmodListAdd (zmodListMul lu2 lf) (zmodListMul lv2 (zmodListAdd lr2 [0, 6]))) [1] = true := by decide
    have hneg6 : (6 : ZMod 7) = -1 := by decide
    have hneg5 : (-(5 : ZMod 7)) = 2 := by decide
    have hp7 : Nat.Prime 7 := by decide
    have : Fact (Nat.Prime 7) := ⟨hp7⟩
    have hfeq : modPrimePolyHom 7 fZ = zmodListToPoly lf := by
      dsimp [modPrimePolyHom, fZ, lf, zmodListToPoly]
      rw [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_C, Polynomial.map_C]
      change Polynomial.X ^ 5 - Polynomial.C ((5 : ℤ) : ZMod 7) * Polynomial.X +
        Polynomial.C ((12 : ℤ) : ZMod 7) = _
      have h5 : ((5 : ℤ) : ZMod 7) = 5 := rfl
      have h12 : ((12 : ℤ) : ZMod 7) = 5 := rfl
      rw [h5, h12, map_zero, map_one]
      rw [show Polynomial.C (2 : ZMod 7) = -Polynomial.C (5 : ZMod 7) from by rw [← map_neg, hneg5]]
      ring
    have hmon7 : (modPrimePolyHom 7 fZ).Monic := hfZ_mon.map _
    have hdeg7 : (modPrimePolyHom 7 fZ).natDegree = 5 := by
      rw [← hfZ_deg]; exact hfZ_mon.natDegree_map _
    have hnegX : zmodListToPoly [0, (6 : ZMod 7)] = -Polynomial.X := by
      dsimp [zmodListToPoly]; rw [map_zero, hneg6, map_neg, map_one]; ring
    have honeP : zmodListToPoly [(1 : ZMod 7)] = 1 := by
      dsimp [zmodListToPoly]; rw [map_one]; ring
    refine irreducible_of_rabin_certificate (p := 7) (d := 5) hmon7 hdeg7 (by decide : 2 ≤ 5)
      (r := fun k : Fin (5 / 2) => match k.1 with | 0 => zmodListToPoly lr1 | _ => zmodListToPoly lr2) ?_ ?_ ?_
    · dsimp only
      rw [hfeq, ← zmodListToPoly_Xpow]
      refine ⟨zmodListToPoly lq1, ?_⟩
      simpa only [zmodListToPoly_add, zmodListToPoly_mul] using zmodListToPoly_eq_of_listEq hc1
    · intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      dsimp only
      rw [hfeq]
      refine ⟨zmodListToPoly lq2, ?_⟩
      simpa only [zmodListToPoly_comp, zmodListToPoly_add, zmodListToPoly_mul] using
        zmodListToPoly_eq_of_listEq hc2
    · intro k
      fin_cases k
      · dsimp only
        refine ⟨zmodListToPoly lu1, zmodListToPoly lv1, ?_⟩
        have h := (zmodListToPoly_eq_of_listEq hb1).trans honeP
        rw [zmodListToPoly_add, zmodListToPoly_mul, zmodListToPoly_mul, zmodListToPoly_add,
          hnegX, ← hfeq] at h
        linear_combination h
      · dsimp only
        refine ⟨zmodListToPoly lu2, zmodListToPoly lv2, ?_⟩
        have h := (zmodListToPoly_eq_of_listEq hb2).trans honeP
        rw [zmodListToPoly_add, zmodListToPoly_mul, zmodListToPoly_mul, zmodListToPoly_add,
          hnegX, ← hfeq] at h
        linear_combination h
  have hirr : Irreducible f := hf_map ▸ irreducible_rat_of_monic_int_mod_prime hfZ_mon hfZ_deg (by decide) hirr_7
  -- 2. Discriminant `Δ(f) = 2¹² · 5⁶ = (2⁶ · 5³)²`:
  have hdisc : garlingDiscriminant f = 2 ^ 12 * 5 ^ 6 := by
    have hform : f = Polynomial.X ^ 5 + Polynomial.C (-5 : ℚ) * Polynomial.X + Polynomial.C 12 := by
      dsimp [f]; simp; ring
    rw [hform, Chapter14.exercise_14_3_discriminant (by decide : 2 ≤ 5) (-5 : ℚ) (12 : ℚ)]
    have heta5 : garlingEta 5 = 1 := rfl
    have heta6 : garlingEta 6 = -1 := rfl
    rw [heta5, heta6]
    norm_num
  have hdisc_sq : ∃ d : ℚ, d ^ 2 = garlingDiscriminant f := ⟨2 ^ 6 * 5 ^ 3, by rw [hdisc]; norm_num⟩
  -- 3. Solvability by radicals and exact real-root count (`1` real root):
  let L0 := Polynomial.SplittingField f
  have hsf0 : IsGarlingSplittingFieldExtension ℚ L0 f :=
    (isGarlingSplittingFieldExtension_iff ℚ L0 f).mpr inferInstance
  have hcl0 := section_20_3_quintic_galois_classification hirr hf_deg hsf0
  have hcard0 : Nat.card (GarlingPolyGaloisGroup ℚ L0 f) = 10 :=
    (example_b_galois_aux.{0} hirr hdisc_sq hsf0).1
  have hrad_f : IsGarlingSolvableByRadicals f :=
    hcl0.2.2.2.2.1.mpr (hcl0.2.2.2.2.2.1.mpr (hcard0 ▸ (by decide : 10 ∣ 20)))
  have hreal_ncard : {x : ℝ | Polynomial.aeval x f = 0}.ncard = 1 := by
    have hdich := exercise_20_3_real_roots (by decide : Nat.Prime 5) (by decide : 2 < 5) hirr hf_deg hrad_f
    let fR : ℝ[X] := f.map (algebraMap ℚ ℝ)
    have hfR_eq : fR = Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X + Polynomial.C 12 := by
      simp [fR, f, map_ofNat]
    have hfR0 : fR ≠ 0 := Polynomial.map_ne_zero hirr.ne_zero
    have hderiv_eq : Polynomial.derivative fR = Polynomial.C 5 * Polynomial.X ^ 4 - Polynomial.C 5 := by
      rw [hfR_eq, Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_pow,
        Polynomial.derivative_X, mul_one, Polynomial.derivative_C_mul_X, Polynomial.derivative_C, add_zero]
      simp [map_ofNat]
    have hderiv_roots : {x : ℝ | (Polynomial.derivative fR).eval x = 0} ⊆ ({-1, 1} : Set ℝ) := by
      intro x hx
      rw [Set.mem_ofPred_eq, hderiv_eq, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C] at hx
      have hx4 : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by linarith
      have hx2 : x ^ 2 - 1 = 0 := (mul_eq_zero.mp hx4).resolve_right (by positivity)
      have hfac : (x - 1) * (x + 1) = 0 := by linarith
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases mul_eq_zero.mp hfac with h1 | h2
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    have hderiv_fin : {x : ℝ | (Polynomial.derivative fR).eval x = 0}.Finite :=
      (Set.toFinite ({-1, 1} : Set ℝ)).subset hderiv_roots
    have hderiv_le2 : {x : ℝ | (Polynomial.derivative fR).eval x = 0}.ncard ≤ 2 := by
      calc {x : ℝ | (Polynomial.derivative fR).eval x = 0}.ncard
          ≤ ({-1, 1} : Set ℝ).ncard := Set.ncard_le_ncard hderiv_roots (Set.toFinite _)
        _ ≤ 2 := by
          have : ({-1, 1} : Set ℝ) = (({-1, 1} : Finset ℝ) : Set ℝ) := by simp
          rw [this, Set.ncard_coe_finset]
          exact Finset.card_le_two
    have hle3 : {x : ℝ | Polynomial.aeval x f = 0}.ncard ≤ 3 := by
      have hset : {x : ℝ | Polynomial.aeval x f = 0} = {x : ℝ | fR.eval x = 0} := by
        ext x; simp [fR, Polynomial.aeval_def, Polynomial.eval_map]
      rw [hset]
      exact ncard_real_roots_le_succ_of_deriv_bound hfR0 hderiv_fin hderiv_le2
    rcases hdich with ⟨_, h5⟩ | ⟨h1, _⟩
    · omega
    · exact h1
  exact ⟨hirr, hf_deg, hdisc, hdisc_sq, hreal_ncard, hrad_f,
    fun L _ _ hsfL => example_b_galois_aux.{u} hirr hdisc_sq hsfL⟩

/-- **§20.3 Example `(c)` (printed p. 161 / PDF p. 169):**
`f_c = x⁵ - 2 ∈ ℚ[x]` is irreducible of degree `5`, is solvable by radicals, and for every
splitting field `L : ℚ` has `Γ_ℚ(x⁵ - 2) ≃* garlingAffineGroup 5` (`W`, order `20`). -/
theorem section_20_3_example_c :
    let f : ℚ[X] := Polynomial.X ^ 5 - Polynomial.C 2
    Irreducible f ∧
    f.natDegree = 5 ∧
    IsGarlingSolvableByRadicals f ∧
    ∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L f →
      Nat.card (GarlingPolyGaloisGroup ℚ L f) = 20 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* garlingAffineGroup 5) := by
  intro f
  have h5 := section_20_2_xp_sub_two_galoisGroup.{u} (by decide : Nat.Prime 5)
  have hf_deg : f.natDegree = 5 := by dsimp [f]; compute_degree!
  refine ⟨h5.1, hf_deg, h5.2.1, fun L _ _ hsfL => ?_⟩
  obtain ⟨_, ⟨eW⟩⟩ := h5.2.2 L hsfL
  have hcard : Nat.card (GarlingPolyGaloisGroup ℚ L f) = 20 := by
    rw [Nat.card_congr eW.toEquiv, garlingAffineGroup_card (by decide : Nat.Prime 5)]
  exact ⟨hcard, ⟨eW⟩⟩

/-- Helper for §20.3 Example `(d)`: universe-polymorphic Galois-group computation for
`f_d = x⁵ + 20x + 16` over any splitting field `L : Type u`. -/
private theorem example_d_galois_aux
    (hirr : Irreducible (Polynomial.X ^ 5 + Polynomial.C 20 * Polynomial.X + Polynomial.C 16 : ℚ[X]))
    (hdisc_sq : ∃ d : ℚ, d ^ 2 = garlingDiscriminant
      (Polynomial.X ^ 5 + Polynomial.C 20 * Polynomial.X + Polynomial.C 16 : ℚ[X]))
    {L : Type u} [Field L] [Algebra ℚ L]
    (hsfL : IsGarlingSplittingFieldExtension ℚ L
      (Polynomial.X ^ 5 + Polynomial.C 20 * Polynomial.X + Polynomial.C 16 : ℚ[X])) :
    Nat.card (GarlingPolyGaloisGroup ℚ L
      (Polynomial.X ^ 5 + Polynomial.C 20 * Polynomial.X + Polynomial.C 16 : ℚ[X])) = 60 ∧
    Nonempty (GarlingPolyGaloisGroup ℚ L
      (Polynomial.X ^ 5 + Polynomial.C 20 * Polynomial.X + Polynomial.C 16 : ℚ[X]) ≃* alternatingGroup (Fin 5)) := by
  classical
  let f : ℚ[X] := Polynomial.X ^ 5 + Polynomial.C 20 * Polynomial.X + Polynomial.C 16
  let fZ : ℤ[X] := Polynomial.X ^ 5 + Polynomial.C 20 * Polynomial.X + Polynomial.C 16
  have hf_map : fZ.map (algebraMap ℤ ℚ) = f := by simp [fZ, f, map_ofNat]
  have hfZ_mon : fZ.Monic := by
    dsimp [fZ]
    have hlt : (Polynomial.C (20 : ℤ) * Polynomial.X + Polynomial.C 16).natDegree < 5 := by compute_degree!
    rw [add_assoc]
    exact Polynomial.monic_X_pow_add (Polynomial.degree_lt_iff_coeff_zero _ _ |>.mpr fun m hm =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  have hf_deg : f.natDegree = 5 := by dsimp [f]; compute_degree!
  -- `3 ∣ |Γ_ℚ(f)|` via `Theorem 20.2` at `p = 7` (`f̄ = (X + 2)(X + 3)(X³ + 2X² + 5X + 5)`):
  have h3_dvd : 3 ∣ Nat.card (GarlingPolyGaloisGroup ℚ L f) := by
    have hq_no_root : ∀ c : ZMod 7, c ^ 3 + 2 * c ^ 2 + 5 * c + 5 ≠ 0 := by decide
    have hfac_list : zmodListEq
        (zmodListMul (p := 7) (zmodListMul (p := 7) [2, 1] [3, 1]) [5, 5, 2, 1]) [2, 6, 0, 0, 0, 1] = true := by
      decide
    have : Fact (Nat.Prime 7) := ⟨by decide⟩
    let q : (ZMod 7)[X] := Polynomial.X ^ 3 + Polynomial.C 2 * Polynomial.X ^ 2 +
      Polynomial.C 5 * Polynomial.X + Polynomial.C 5
    have hq_deg : q.natDegree = 3 := by dsimp [q]; compute_degree!
    have hq_irr : Irreducible q :=
      irreducible_of_natDegree_le_three_of_no_root (by omega) (by omega) fun c hc =>
        hq_no_root c (by simpa [q] using hc)
    have hq_dvd : q ∣ modPrimePolyHom 7 fZ := by
      refine ⟨(Polynomial.X + Polynomial.C 2) * (Polynomial.X + Polynomial.C 3), ?_⟩
      have hpoly := zmodListToPoly_eq_of_listEq hfac_list
      simp only [zmodListToPoly_mul, zmodListToPoly, map_zero, map_one, zero_add] at hpoly
      have hfeq : modPrimePolyHom 7 fZ =
          Polynomial.X ^ 5 + Polynomial.C (6 : ZMod 7) * Polynomial.X + Polynomial.C 2 := by
        dsimp [modPrimePolyHom, fZ]
        rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
          Polynomial.map_X, Polynomial.map_C, Polynomial.map_C]
        change Polynomial.X ^ 5 + Polynomial.C ((20 : ℤ) : ZMod 7) * Polynomial.X +
          Polynomial.C ((16 : ℤ) : ZMod 7) = _
        have h20 : ((20 : ℤ) : ZMod 7) = 6 := rfl
        have h16 : ((16 : ℤ) : ZMod 7) = 2 := rfl
        rw [h20, h16]
      rw [hfeq]
      dsimp [q]
      linear_combination -hpoly
    let fbar := modPrimePolyHom 7 fZ
    let M := Polynomial.SplittingField fbar
    have hsfM : IsGarlingSplittingFieldExtension (ZMod 7) M fbar :=
      (isGarlingSplittingFieldExtension_iff (ZMod 7) M fbar).mpr inferInstance
    have hsfM_m := (isGarlingSplittingFieldExtension_iff (ZMod 7) M fbar).mp hsfM
    have hq_splits : (q.map (algebraMap (ZMod 7) M)).Splits :=
      Polynomial.Splits.of_dvd hsfM_m.splits (Polynomial.map_ne_zero (hfZ_mon.map _).ne_zero)
        (Polynomial.map_dvd _ hq_dvd)
    have hq_roots_pos : 0 < (q.map (algebraMap (ZMod 7) M)).roots.card := by
      rw [Polynomial.splits_iff_card_roots.mp hq_splits,
        Polynomial.natDegree_map_eq_of_injective (algebraMap (ZMod 7) M).injective, hq_deg]
      decide
    obtain ⟨β, hβ⟩ := Multiset.card_pos_iff_exists_mem.mp hq_roots_pos
    have hβ_root : Polynomial.aeval β q = 0 := by
      have h1 := (Polynomial.mem_roots (Polynomial.map_ne_zero hq_irr.ne_zero)).mp hβ
      rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    have hq_mon : q.Monic := by
      have hq_eq : q = Polynomial.X ^ 3 + (Polynomial.C (2 : ZMod 7) * Polynomial.X ^ 2 +
          Polynomial.C 5 * Polynomial.X + Polynomial.C 5) := by
        dsimp [q]; ring
      have hlt : (Polynomial.C (2 : ZMod 7) * Polynomial.X ^ 2 + Polynomial.C 5 * Polynomial.X +
          Polynomial.C 5).natDegree < 3 := by compute_degree!
      rw [hq_eq]
      exact Polynomial.monic_X_pow_add (Polynomial.degree_lt_iff_coeff_zero _ _ |>.mpr fun m hm =>
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
    have hmin_β : minpoly (ZMod 7) β = q := (minpoly.eq_of_irreducible_of_monic hq_irr hβ_root hq_mon).symm
    have h3_dvd_M : 3 ∣ Module.finrank (ZMod 7) M := by
      let Kβ := IntermediateField.adjoin (ZMod 7) ({β} : Set M)
      have hfin_β : Module.finrank (ZMod 7) Kβ = 3 := by
        rw [IntermediateField.adjoin.finrank ⟨q, hq_mon, hβ_root⟩, hmin_β, hq_deg]
      have _ : Module.Finite (ZMod 7) M := Polynomial.IsSplittingField.finiteDimensional M fbar
      have _ : Module.Finite (ZMod 7) Kβ := inferInstance
      have _ : Module.Finite Kβ M := Module.Finite.right (ZMod 7) Kβ M
      have hmul := Module.finrank_mul_finrank (ZMod 7) Kβ M
      rw [hfin_β] at hmul
      exact ⟨Module.finrank Kβ M, hmul.symm⟩
    have _ : FiniteDimensional (ZMod 7) M := Polynomial.IsSplittingField.finiteDimensional M fbar
    have _ : Normal (ZMod 7) M := Normal.of_isSplittingField fbar
    have _ : IsGalois (ZMod 7) M := ⟨⟩
    have hcardM : Nat.card (GarlingPolyGaloisGroup (ZMod 7) M fbar) = Module.finrank (ZMod 7) M :=
      IsGalois.card_aut_eq_finrank (ZMod 7) M
    have hdistinct_L : ¬ HasGarlingRepeatedRoot ℚ L f := by
      rcases hsfL.1 with ⟨m, c, α, hexp⟩
      exact fun hrep => ((injective_roots_iff_separable_and_not_repeated hirr.ne_zero hexp).2.mpr hrep)
        ((injective_roots_iff_separable_and_not_repeated hirr.ne_zero hexp).1.mpr hirr.separable)
    have h20_2 := theorem_20_2 hfZ_mon (by decide : Nat.Prime 7) (hf_map ▸ hsfL) (hf_map ▸ hdistinct_L) hsfM
    obtain ⟨H, ⟨eH⟩⟩ := h20_2.2
    have hdvd : Nat.card (GarlingPolyGaloisGroup (ZMod 7) M fbar) ∣
        Nat.card (GarlingPolyGaloisGroup ℚ L f) := by
      have h1 : Nat.card (GarlingPolyGaloisGroup (ZMod 7) M fbar) = Nat.card H :=
        Nat.card_congr eH.toEquiv
      have h2 : Nat.card H ∣ Nat.card (GarlingPolyGaloisGroup ℚ L (fZ.map (algebraMap ℤ ℚ))) :=
        Subgroup.card_subgroup_dvd_card H
      rw [hf_map] at h2
      exact h1 ▸ h2
    exact dvd_trans (hcardM ▸ h3_dvd_M) hdvd
  obtain ⟨_, _, _, h5way, _, _, hdisc_iff⟩ :=
    section_20_3_quintic_galois_classification hirr hf_deg hsfL
  have hcard_3 := hdisc_iff.mp hdisc_sq
  have hcard60 : Nat.card (GarlingPolyGaloisGroup ℚ L f) = 60 := by
    rcases hcard_3 with h5 | h10 | h60
    · rw [h5] at h3_dvd; exact absurd h3_dvd (by decide)
    · rw [h10] at h3_dvd; exact absurd h3_dvd (by decide)
    · exact h60
  refine ⟨hcard60, ?_⟩
  rcases h5way with h | h | h | h | h
  · exfalso; obtain ⟨e0⟩ := h; have hc := Nat.card_congr e0.toEquiv; rw [hcard60] at hc
    have h5 : Nat.card (Multiplicative (ZMod 5)) = 5 := Nat.card_eq_fintype_card.trans (by decide)
    omega
  · exfalso; obtain ⟨e1⟩ := h; have hc := Nat.card_congr e1.toEquiv; rw [hcard60, DihedralGroup.nat_card] at hc; omega
  · exfalso; obtain ⟨e2⟩ := h; have hc := Nat.card_congr e2.toEquiv
    rw [hcard60, garlingAffineGroup_card (by decide : Nat.Prime 5)] at hc; norm_num at hc
  · exact h
  · exfalso; obtain ⟨e4⟩ := h; have hc := Nat.card_congr e4.toEquiv
    rw [hcard60, Nat.card_perm, Nat.card_fin] at hc; norm_num at hc

/-- **§20.3 Example `(d)` (printed pp. 161–162 / PDF pp. 169–170):**
`f_d = x⁵ + 20x + 16 ∈ ℚ[x]` is irreducible of degree `5` (certified modulo `3`), has discriminant
`Δ(f_d) = 2¹⁶ · 5⁶ = (2⁸ · 5³)²`, reduces modulo `7` as `(x + 2)(x + 3)(x³ + 2x² + 5x + 5)` with
an irreducible cubic factor (so `3 ∣ |Γ_ℚ(f_d)|` by `Theorem 20.2`), is **not** solvable by
radicals, and for every splitting field `L : ℚ` has `Γ_ℚ(f_d) ≃* alternatingGroup (Fin 5)` (`A₅`,
order `60`). -/
theorem section_20_3_example_d :
    let f : ℚ[X] := Polynomial.X ^ 5 + Polynomial.C 20 * Polynomial.X + Polynomial.C 16
    Irreducible f ∧
    f.natDegree = 5 ∧
    garlingDiscriminant f = 2 ^ 16 * 5 ^ 6 ∧
    (∃ d : ℚ, d ^ 2 = garlingDiscriminant f) ∧
    ¬ IsGarlingSolvableByRadicals f ∧
    ∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L f →
      Nat.card (GarlingPolyGaloisGroup ℚ L f) = 60 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* alternatingGroup (Fin 5)) := by
  classical
  intro f
  let fZ : ℤ[X] := Polynomial.X ^ 5 + Polynomial.C 20 * Polynomial.X + Polynomial.C 16
  have hf_map : fZ.map (algebraMap ℤ ℚ) = f := by simp [fZ, f, map_ofNat]
  have hfZ_mon : fZ.Monic := by
    dsimp [fZ]
    have hlt : (Polynomial.C (20 : ℤ) * Polynomial.X + Polynomial.C 16).natDegree < 5 := by compute_degree!
    rw [add_assoc]
    exact Polynomial.monic_X_pow_add (Polynomial.degree_lt_iff_coeff_zero _ _ |>.mpr fun m hm =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  have hfZ_deg : fZ.natDegree = 5 := by dsimp [fZ]; compute_degree!
  have hf_deg : f.natDegree = 5 := by dsimp [f]; compute_degree!
  -- 1. Irreducibility over `ℚ` via mod-3 pure-kernel Rabin certificate:
  have hirr_3 : Irreducible (modPrimePolyHom 3 fZ) := by
    let lf : List (ZMod 3) := [1, 2, 0, 0, 0, 1]
    let lq1 : List (ZMod 3) := []
    let lr1 : List (ZMod 3) := [0, 0, 0, 1]
    let lu1 : List (ZMod 3) := [1]
    let lv1 : List (ZMod 3) := [2, 0, 2]
    let lq2 : List (ZMod 3) := [1, 0, 0, 0, 1]
    let lr2 : List (ZMod 3) := [2, 1, 0, 0, 2]
    let lu2 : List (ZMod 3) := [2, 1, 2, 1]
    let lv2 : List (ZMod 3) := [1, 2, 1, 2, 1]
    have hc1 : zmodListEq (zmodListXpow (p := 3) 3) (zmodListAdd (zmodListMul lq1 lf) lr1) = true := by decide
    have hc2 : zmodListEq (zmodListComp lr1 lr1) (zmodListAdd (zmodListMul lq2 lf) lr2) = true := by decide
    have hb1 : zmodListEq (zmodListAdd (zmodListMul lu1 lf) (zmodListMul lv1 (zmodListAdd lr1 [0, 2]))) [1] = true := by decide
    have hb2 : zmodListEq (zmodListAdd (zmodListMul lu2 lf) (zmodListMul lv2 (zmodListAdd lr2 [0, 2]))) [1] = true := by decide
    have hneg2 : (2 : ZMod 3) = -1 := by decide
    have hp3 : Nat.Prime 3 := by decide
    have : Fact (Nat.Prime 3) := ⟨hp3⟩
    have hfeq : modPrimePolyHom 3 fZ = zmodListToPoly lf := by
      dsimp [modPrimePolyHom, fZ, lf, zmodListToPoly]
      rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_C, Polynomial.map_C]
      change Polynomial.X ^ 5 + Polynomial.C ((20 : ℤ) : ZMod 3) * Polynomial.X +
        Polynomial.C ((16 : ℤ) : ZMod 3) = _
      have h20 : ((20 : ℤ) : ZMod 3) = 2 := rfl
      have h16 : ((16 : ℤ) : ZMod 3) = 1 := rfl
      rw [h20, h16, map_zero, map_one]
      ring
    have hmon3 : (modPrimePolyHom 3 fZ).Monic := hfZ_mon.map _
    have hdeg3 : (modPrimePolyHom 3 fZ).natDegree = 5 := by
      rw [← hfZ_deg]; exact hfZ_mon.natDegree_map _
    have hnegX : zmodListToPoly [0, (2 : ZMod 3)] = -Polynomial.X := by
      dsimp [zmodListToPoly]; rw [map_zero, hneg2, map_neg, map_one]; ring
    have honeP : zmodListToPoly [(1 : ZMod 3)] = 1 := by
      dsimp [zmodListToPoly]; rw [map_one]; ring
    refine irreducible_of_rabin_certificate (p := 3) (d := 5) hmon3 hdeg3 (by decide : 2 ≤ 5)
      (r := fun k : Fin (5 / 2) => match k.1 with | 0 => zmodListToPoly lr1 | _ => zmodListToPoly lr2) ?_ ?_ ?_
    · dsimp only
      rw [hfeq, ← zmodListToPoly_Xpow]
      refine ⟨zmodListToPoly lq1, ?_⟩
      simpa only [zmodListToPoly_add, zmodListToPoly_mul] using zmodListToPoly_eq_of_listEq hc1
    · intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      dsimp only
      rw [hfeq]
      refine ⟨zmodListToPoly lq2, ?_⟩
      simpa only [zmodListToPoly_comp, zmodListToPoly_add, zmodListToPoly_mul] using
        zmodListToPoly_eq_of_listEq hc2
    · intro k
      fin_cases k
      · dsimp only
        refine ⟨zmodListToPoly lu1, zmodListToPoly lv1, ?_⟩
        have h := (zmodListToPoly_eq_of_listEq hb1).trans honeP
        rw [zmodListToPoly_add, zmodListToPoly_mul, zmodListToPoly_mul, zmodListToPoly_add,
          hnegX, ← hfeq] at h
        linear_combination h
      · dsimp only
        refine ⟨zmodListToPoly lu2, zmodListToPoly lv2, ?_⟩
        have h := (zmodListToPoly_eq_of_listEq hb2).trans honeP
        rw [zmodListToPoly_add, zmodListToPoly_mul, zmodListToPoly_mul, zmodListToPoly_add,
          hnegX, ← hfeq] at h
        linear_combination h
  have hirr : Irreducible f := hf_map ▸ irreducible_rat_of_monic_int_mod_prime hfZ_mon hfZ_deg (by decide) hirr_3
  -- 2. Discriminant `Δ(f) = 2¹⁶ · 5⁶ = (2⁸ · 5³)²`:
  have hdisc : garlingDiscriminant f = 2 ^ 16 * 5 ^ 6 := by
    dsimp [f]
    rw [Chapter14.exercise_14_3_discriminant (by decide : 2 ≤ 5) (20 : ℚ) (16 : ℚ)]
    have heta5 : garlingEta 5 = 1 := rfl
    have heta6 : garlingEta 6 = -1 := rfl
    rw [heta5, heta6]
    norm_num
  have hdisc_sq : ∃ d : ℚ, d ^ 2 = garlingDiscriminant f := ⟨2 ^ 8 * 5 ^ 3, by rw [hdisc]; norm_num⟩
  -- 3. Non-solvability by radicals and `Γ_ℚ(f) ≃* A₅`:
  let L0 := Polynomial.SplittingField f
  have hsf0 : IsGarlingSplittingFieldExtension ℚ L0 f :=
    (isGarlingSplittingFieldExtension_iff ℚ L0 f).mpr inferInstance
  have hcl0 := section_20_3_quintic_galois_classification hirr hf_deg hsf0
  have hcard0 : Nat.card (GarlingPolyGaloisGroup ℚ L0 f) = 60 :=
    (example_d_galois_aux.{0} hirr hdisc_sq hsf0).1
  have hnrad : ¬ IsGarlingSolvableByRadicals f := fun hrad => by
    have hd := hcl0.2.2.2.2.2.1.mp (hcl0.2.2.2.2.1.mp hrad)
    rw [hcard0] at hd
    exact absurd hd (by decide)
  exact ⟨hirr, hf_deg, hdisc, hdisc_sq, hnrad,
    fun L _ _ hsfL => example_d_galois_aux.{u} hirr hdisc_sq hsfL⟩

/-- **§20.3 Example `(e)` (printed p. 161 / PDF p. 169):**
`f_e = x⁵ - 4x + 2 ∈ ℚ[x]` is irreducible of degree `5`, is not solvable by radicals, and for every
splitting field `L : ℚ` has `Γ_ℚ(f_e) ≃* SigmaN 5` (`Σ₅`, order `120`).
(Directly imports `Chapter11.section_11_3_quintic_example` and
`Chapter17.section_17_4_quintic_not_solvable_by_radicals`.) -/
theorem section_20_3_example_e :
    let f : ℚ[X] := Polynomial.X ^ 5 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2
    Irreducible f ∧
    f.natDegree = 5 ∧
    ¬ IsGarlingSolvableByRadicals f ∧
    ∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L f →
      Nat.card (GarlingPolyGaloisGroup ℚ L f) = 120 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* SigmaN 5) := by
  intro f
  have h11 := section_11_3_quintic_example.{u}
  have h17 := section_17_4_quintic_not_solvable_by_radicals.{u}
  refine ⟨h11.1, h11.2.1, h17.2.2, fun L _ _ hsfL => ?_⟩
  obtain ⟨_, ⟨e⟩⟩ := h11.2.2.2.2.2 L hsfL
  have hcard : Nat.card (GarlingPolyGaloisGroup ℚ L f) = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]; norm_num
  exact ⟨hcard, ⟨e⟩⟩

/-- **Exercise 20.3 (`p = 4k + 1` discriminant-square ambiguity witness, §20.2 p. 160 & §20.3 pp. 161–162):**
At `p = 5 = 4·1 + 1`, §20.3 Examples `(a)` (`x⁵ + x⁴ - 4x³ - 3x² + 3x + 1`) and `(b)`
(`x⁵ - 5x + 12`) are both irreducible quintics over `ℚ` solvable by radicals whose discriminants
are **both positive rational squares** (`0 < Δ` and `∃ d : ℚ, d² = Δ`), yet `(a)` has all `5` roots
real while `(b)` has only `1` real root. Thus when `p = 4k + 1`, neither the sign nor even the
rational-square class of the discriminant distinguishes the two cases of `Exercise 20.3`. -/
theorem exercise_20_3_p5_square_disc_witness :
    let fa : ℚ[X] :=
      Polynomial.X ^ 5 + Polynomial.X ^ 4 - Polynomial.C 4 * Polynomial.X ^ 3 -
        Polynomial.C 3 * Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 1
    let fb : ℚ[X] := Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X + Polynomial.C 12
    (Irreducible fa ∧ fa.natDegree = 5 ∧ IsGarlingSolvableByRadicals fa ∧
      0 < garlingDiscriminant fa ∧ (∃ d : ℚ, d ^ 2 = garlingDiscriminant fa) ∧
      {x : ℝ | Polynomial.aeval x fa = 0}.ncard = 5) ∧
    (Irreducible fb ∧ fb.natDegree = 5 ∧ IsGarlingSolvableByRadicals fb ∧
      0 < garlingDiscriminant fb ∧ (∃ d : ℚ, d ^ 2 = garlingDiscriminant fb) ∧
      {x : ℝ | Polynomial.aeval x fb = 0}.ncard = 1) := by
  intro fa fb
  have ha := section_20_3_example_a.{0}
  have hb := section_20_3_example_b.{0}
  refine ⟨⟨ha.1, ha.2.1, ha.2.2.2.2.2.1, ha.2.2.2.1, ha.2.2.2.2.1, ha.2.2.1⟩,
    ⟨hb.1, hb.2.1, hb.2.2.2.2.2.1, ?_, hb.2.2.2.1, hb.2.2.2.2.1⟩⟩
  rw [hb.2.2.1]
  norm_num

/-! ## §20.4 Concluding remarks (printed p. 162 / PDF p. 170)

Garling closes the book (printed p. 162 / PDF p. 170; `0` numbered theorems, `0` exercises) with an
unnumbered historical remark on the **inverse Galois problem** over `ℚ`:
- Does every finite group `G` arise as the Galois group `Γ_ℚ(f)` of some polynomial `f ∈ ℚ[x]`?
- By a celebrated theorem of I. R. Safarevich (Shafarevich, 1954), every finite **soluble** group
  is realizable as a Galois group over `ℚ`; the general question for arbitrary finite groups remains
  open.
- Garling also acknowledges Leonard Soicher for the §20.3 quintic examples and closes the book with:
  *"Galois theory has a long and distinguished history: nevertheless, many interesting problems remain."*

Per `BRIEF.md` §3, this §20.4 prose remark is recorded as documentation commentary rather than a
formalized theorem.
-/

end Garling.Chapter20
