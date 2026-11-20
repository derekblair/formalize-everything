import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Binomial
import TauCeti.Algebra.Module.Rat
import TauCeti.RingTheory.Binomial
import TauCeti.RingTheory.MvPolynomial.Binomial.Basis
import TauCeti.RingTheory.Polynomial.Binomial.Filtration

open MvPolynomial Polynomial TauCeti

universe u

namespace Humphreys26_1

section MultivariateBinomialBasis

attribute [local instance] TauCeti.moduleNNRat

/-- **Humphreys §26.1 (p. 152): Product of binomial polynomials**
`binomialMvPoly K ℓ b = (T₁ choose b₁)(T₂ choose b₂) ⋯ (T_ℓ choose b_ℓ)` in
`MvPolynomial (Fin ℓ) K`, where `b : Fin ℓ → ℕ` (`ℕ = ℤ⁺`, H p. viii). -/
noncomputable def binomialMvPoly (K : Type u) [Field K] [CharZero K] (ℓ : ℕ)
    (b : Fin ℓ → ℕ) : MvPolynomial (Fin ℓ) K :=
  ∏ i : Fin ℓ, Ring.choose (MvPolynomial.X i : MvPolynomial (Fin ℓ) K) (b i)

/-- **Humphreys §26.1 (p. 152): Subring of integer-valued polynomials in `ℓ` variables over `K`**,
`{f ∈ K[T₁, …, T_ℓ] | ∀ n ∈ ℤ^ℓ, f(n₁, …, n_ℓ) ∈ ℤ}`. -/
noncomputable def intValuedMvSubring (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) :
    Subring (MvPolynomial (Fin ℓ) K) :=
  ⨅ n : Fin ℓ → ℤ,
    (Int.castRingHom K).range.comap (MvPolynomial.eval (fun i : Fin ℓ => (n i : K)))

private theorem mem_intValuedMvSubring_iff
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) (f : MvPolynomial (Fin ℓ) K) :
    f ∈ intValuedMvSubring K ℓ ↔
      ∀ n : Fin ℓ → ℤ,
        MvPolynomial.eval (fun i => (n i : K)) f ∈ Set.range (Int.cast : ℤ → K) := by
  simp only [intValuedMvSubring, Subring.mem_iInf, Subring.mem_comap, RingHom.mem_range,
    Int.coe_castRingHom, Set.mem_range]

private theorem eval_binomialMvPoly_int
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) (b : Fin ℓ → ℕ) (n : Fin ℓ → ℤ) :
    MvPolynomial.eval (fun i => (n i : K)) (binomialMvPoly K ℓ b) =
      ((∏ i : Fin ℓ, Ring.choose (n i) (b i) : ℤ) : K) := by
  simp only [binomialMvPoly, map_prod, Ring.map_choose, MvPolynomial.eval_X,
    TauCeti.Ring.choose_intCast, Int.cast_prod]

private theorem binomialMvPoly_mem_intValuedMvSubring
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) (b : Fin ℓ → ℕ) :
    binomialMvPoly K ℓ b ∈ intValuedMvSubring K ℓ :=
  (mem_intValuedMvSubring_iff K ℓ _).mpr fun n => ⟨_, (eval_binomialMvPoly_int K ℓ b n).symm⟩

private theorem linearIndependent_binomialMvPoly_int
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) :
    LinearIndependent ℤ (binomialMvPoly K ℓ) := by
  have hfun : binomialMvPoly K ℓ =
      (fun n : Fin ℓ →₀ ℕ =>
        n.prod (fun i k => Ring.choose (MvPolynomial.X i : MvPolynomial (Fin ℓ) K) k)) ∘
          Finsupp.equivFunOnFinite.symm := by
    funext b
    simp only [Function.comp_apply, binomialMvPoly]
    rw [Finsupp.prod_fintype _ _ (fun _ => Ring.choose_zero_right _)]
    rfl
  rw [hfun]
  exact (TauCeti.linearIndependent_prod_ringChoose_X_int K (Fin ℓ)).comp _
    Finsupp.equivFunOnFinite.symm.injective

private noncomputable def polyDiff {R : Type*} [Ring R] (Q : Polynomial R) : Polynomial R :=
  Q.comp (Polynomial.X + 1) - Q

private theorem polyDiff_zero {R : Type*} [Ring R] :
    polyDiff (0 : Polynomial R) = 0 := by
  simp [polyDiff]

private theorem polyDiff_add {R : Type*} [Ring R] (P Q : Polynomial R) :
    polyDiff (P + Q) = polyDiff P + polyDiff Q := by
  simp only [polyDiff, Polynomial.add_comp]
  abel

private theorem polyDiff_C_mul {R : Type*} [CommRing R] (a : R) (Q : Polynomial R) :
    polyDiff (Polynomial.C a * Q) = Polynomial.C a * polyDiff Q := by
  simp only [polyDiff, Polynomial.mul_comp, Polynomial.C_comp, mul_sub]

private theorem polyDiff_C {R : Type*} [Ring R] (a : R) :
    polyDiff (Polynomial.C a) = 0 := by
  simp [polyDiff]

private theorem polyDiff_finset_sum {R : Type*} [Ring R] {ι : Type*} (s : Finset ι)
    (F : ι → Polynomial R) :
    polyDiff (∑ i ∈ s, F i) = ∑ i ∈ s, polyDiff (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polyDiff_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, polyDiff_add, ih]

private theorem polyDiff_iterate_finset_sum {R : Type*} [Ring R] {ι : Type*} (s : Finset ι)
    (F : ι → Polynomial R) :
    ∀ m : ℕ, polyDiff^[m] (∑ i ∈ s, F i) = ∑ i ∈ s, polyDiff^[m] (F i)
  | 0 => rfl
  | m + 1 => by
      simp only [Function.iterate_succ_apply', polyDiff_iterate_finset_sum s F m,
        polyDiff_finset_sum]

private theorem comp_add_one_ringChoose_X
    {A : Type*} [CommRing A] [Algebra ℚ A] (k : ℕ) :
    (Ring.choose (Polynomial.X : Polynomial A) k).comp (Polynomial.X + 1) =
      Ring.choose (Polynomial.X + 1 : Polynomial A) k := by
  let φ : Polynomial A →+* Polynomial A :=
    Polynomial.eval₂RingHom Polynomial.C (Polynomial.X + 1)
  have hφ : ∀ Q : Polynomial A, φ Q = Q.comp (Polynomial.X + 1) := fun _ => rfl
  rw [← hφ, Ring.map_choose]
  simp [φ]

private theorem polyDiff_ringChoose_X_zero {A : Type*} [CommRing A] [Algebra ℚ A] :
    polyDiff (Ring.choose (Polynomial.X : Polynomial A) 0) = 0 := by
  simp [polyDiff]

private theorem polyDiff_ringChoose_X_succ {A : Type*} [CommRing A] [Algebra ℚ A] (k : ℕ) :
    polyDiff (Ring.choose (Polynomial.X : Polynomial A) (k + 1)) =
      Ring.choose (Polynomial.X : Polynomial A) k := by
  rw [polyDiff, comp_add_one_ringChoose_X, Ring.choose_succ_succ, add_sub_cancel_right]

private theorem polyDiff_iterate_C_mul_ringChoose_X
    {A : Type*} [CommRing A] [Algebra ℚ A] (a : A) :
    ∀ (m k : ℕ),
      polyDiff^[m] (Polynomial.C a * Ring.choose (Polynomial.X : Polynomial A) k) =
        if k < m then 0
        else Polynomial.C a * Ring.choose (Polynomial.X : Polynomial A) (k - m)
  | 0, k => by simp
  | m + 1, k => by
      rw [Function.iterate_succ_apply', polyDiff_iterate_C_mul_ringChoose_X a m k]
      by_cases hkm : k < m
      · have hklt : k < m + 1 := Nat.lt_succ_of_lt hkm
        simp [hkm, hklt, polyDiff_zero]
      · simp only [hkm, ↓reduceIte]
        by_cases hkeq : k = m
        · subst hkeq
          simp [polyDiff_C]
        · have hnotlt : ¬ k < m + 1 := by omega
          have hsub : k - m = (k - (m + 1)) + 1 := by omega
          simp only [hnotlt, ↓reduceIte, hsub, polyDiff_C_mul, polyDiff_ringChoose_X_succ]

private theorem map_polyDiff {A B : Type*} [CommRing A] [CommRing B] (e : A →+* B)
    (Q : Polynomial A) :
    Polynomial.map e (polyDiff Q) = polyDiff (Polynomial.map e Q) := by
  simp only [polyDiff, Polynomial.map_sub, Polynomial.map_comp, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_one]

private theorem map_polyDiff_iterate {A B : Type*} [CommRing A] [CommRing B] (e : A →+* B)
    (Q : Polynomial A) :
    ∀ m : ℕ, Polynomial.map e (polyDiff^[m] Q) = polyDiff^[m] (Polynomial.map e Q)
  | 0 => rfl
  | m + 1 => by
      simp only [Function.iterate_succ_apply', map_polyDiff, map_polyDiff_iterate e Q m]

private theorem eval_polyDiff_iterate_mem_intRange
    (K : Type u) [Field K] [CharZero K] (q : Polynomial K)
    (hq : ∀ n : ℤ, Polynomial.eval (n : K) q ∈ Set.range (Int.cast : ℤ → K)) :
    ∀ (m : ℕ) (n : ℤ),
      Polynomial.eval (n : K) (polyDiff^[m] q) ∈ Set.range (Int.cast : ℤ → K)
  | 0, n => hq n
  | m + 1, n => by
      rw [Function.iterate_succ_apply']
      obtain ⟨z₁, hz₁⟩ := eval_polyDiff_iterate_mem_intRange K q hq m (n + 1)
      obtain ⟨z₂, hz₂⟩ := eval_polyDiff_iterate_mem_intRange K q hq m n
      refine ⟨z₁ - z₂, ?_⟩
      simp only [polyDiff, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_one]
      have hcast : (n : K) + 1 = ((n + 1 : ℤ) : K) := by push_cast; rfl
      rw [hcast, ← hz₁, ← hz₂, Int.cast_sub]

private theorem finSuccEquiv_rename_succ
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) (q : MvPolynomial (Fin ℓ) K) :
    MvPolynomial.finSuccEquiv K ℓ (MvPolynomial.rename Fin.succ q) = Polynomial.C q := by
  have h : (MvPolynomial.finSuccEquiv K ℓ).toRingHom.comp
      (MvPolynomial.rename (R := K) Fin.succ).toRingHom =
      (Polynomial.C : MvPolynomial (Fin ℓ) K →+* Polynomial (MvPolynomial (Fin ℓ) K)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [MvPolynomial.finSuccEquiv_apply]
    · intro j
      simp [MvPolynomial.finSuccEquiv_X_succ]
  exact RingHom.congr_fun h q

private theorem coeff_finset_sum {R : Type*} [Semiring R] {ι : Type*} (s : Finset ι)
    (F : ι → Polynomial R) (n : ℕ) :
    (∑ i ∈ s, F i).coeff n = ∑ i ∈ s, (F i).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.coeff_add, ih]

private theorem coeff_ringChoose_X_self {A : Type*} [CommRing A] [Algebra ℚ A] [Nontrivial A]
    (r : ℕ) :
    (Ring.choose (Polynomial.X : Polynomial A) r).coeff r =
      algebraMap ℚ A (r.factorial : ℚ)⁻¹ := by
  have h1 : (Ring.choose (Polynomial.X : Polynomial A) r).natDegree = r :=
    TauCeti.natDegree_ringChoose_X A r
  have h2 : (Ring.choose (Polynomial.X : Polynomial A) r).leadingCoeff =
      algebraMap ℚ A (r.factorial : ℚ)⁻¹ :=
    TauCeti.leadingCoeff_ringChoose_X A r
  rw [Polynomial.leadingCoeff, h1] at h2
  exact h2

private theorem top_binomial_coeff_eq {A : Type*} [CommRing A] [Algebra ℚ A] [Nontrivial A]
    (r : ℕ) (g : ℕ → A) :
    (∑ k ∈ Finset.range (r + 1),
        Polynomial.C (g k) * Ring.choose (Polynomial.X : Polynomial A) k).coeff r =
      g r * algebraMap ℚ A (r.factorial : ℚ)⁻¹ := by
  rw [coeff_finset_sum, Finset.sum_range_succ]
  have hlow : ∑ k ∈ Finset.range r,
      (Polynomial.C (g k) * Ring.choose (Polynomial.X : Polynomial A) k).coeff r = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Polynomial.coeff_C_mul]
    have hlt : (Ring.choose (Polynomial.X : Polynomial A) k).natDegree < r := by
      rw [TauCeti.natDegree_ringChoose_X]
      exact Finset.mem_range.mp hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
  rw [hlow, zero_add, Polynomial.coeff_C_mul, coeff_ringChoose_X_self]

private theorem polyDiff_iterate_binomial_sum {A : Type*} [CommRing A] [Algebra ℚ A]
    (r : ℕ) (g : ℕ → A) :
    polyDiff^[r] (∑ k ∈ Finset.range (r + 1),
        Polynomial.C (g k) * Ring.choose (Polynomial.X : Polynomial A) k) =
      Polynomial.C (g r) := by
  rw [polyDiff_iterate_finset_sum, Finset.sum_range_succ]
  have hlow : ∑ k ∈ Finset.range r,
      polyDiff^[r] (Polynomial.C (g k) * Ring.choose (Polynomial.X : Polynomial A) k) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [polyDiff_iterate_C_mul_ringChoose_X]
    simp [Finset.mem_range.mp hk]
  rw [hlow, zero_add, polyDiff_iterate_C_mul_ringChoose_X]
  simp

private theorem degreeOf_toMvPolynomial_of_ne
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) {i j : Fin ℓ} (hij : i ≠ j)
    (q : Polynomial K) :
    (q.toMvPolynomial j).degreeOf i = 0 := by
  induction q using Polynomial.induction_on' with
  | add p₁ p₂ ih₁ ih₂ =>
      rw [map_add]
      exact Nat.eq_zero_of_le_zero ((MvPolynomial.degreeOf_add_le i _ _).trans (by simp [ih₁, ih₂]))
  | monomial k a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, Polynomial.toMvPolynomial_C,
        Polynomial.toMvPolynomial_X]
      exact Nat.eq_zero_of_le_zero
        ((MvPolynomial.degreeOf_mul_le i _ _).trans
          (by simp [MvPolynomial.degreeOf_X_pow_of_ne k hij]))

private theorem degreeOf_ringChoose_X_of_ne
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) {i j : Fin ℓ} (hij : i ≠ j) (k : ℕ) :
    (Ring.choose (MvPolynomial.X j : MvPolynomial (Fin ℓ) K) k).degreeOf i = 0 := by
  have heq : Ring.choose (MvPolynomial.X j : MvPolynomial (Fin ℓ) K) k =
      (Ring.choose (Polynomial.X : Polynomial K) k).toMvPolynomial j := by
    rw [Ring.map_choose, Polynomial.toMvPolynomial_X]
  rw [heq]
  exact degreeOf_toMvPolynomial_of_ne K ℓ hij _

private theorem degreeOf_sub_le
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) (i : Fin ℓ)
    (p q : MvPolynomial (Fin ℓ) K) :
    (p - q).degreeOf i ≤ max (p.degreeOf i) (q.degreeOf i) := by
  rw [sub_eq_add_neg]
  refine (MvPolynomial.degreeOf_add_le i p (-q)).trans (max_le_max le_rfl ?_)
  have hneg : -q = MvPolynomial.C (-1 : K) * q := by simp
  rw [hneg]
  exact MvPolynomial.degreeOf_C_mul_le q i (-1)

private theorem exists_zsmul_binomialMvPoly_and_degreeOf_le
    (K : Type u) [Field K] [CharZero K] :
    ∀ (ℓ : ℕ) (f : MvPolynomial (Fin ℓ) K),
      (∀ n : Fin ℓ → ℤ,
          MvPolynomial.eval (fun i => (n i : K)) f ∈ Set.range (Int.cast : ℤ → K)) →
        ∃ c : (Fin ℓ → ℕ) →₀ ℤ,
          c.sum (fun b a => a • binomialMvPoly K ℓ b) = f ∧
            ∀ b ∈ c.support, ∀ i : Fin ℓ, b i ≤ f.degreeOf i := by
  intro ℓ
  induction ℓ with
  | zero =>
      intro f hf
      obtain ⟨z, hz⟩ := hf Fin.elim0
      have hf_C : f = MvPolynomial.C (f.coeff 0) := by
        ext d
        have hd : d = 0 := Subsingleton.elim d 0
        subst hd
        simp [MvPolynomial.coeff_C]
      have hf_eq : f = MvPolynomial.C (z : K) := by
        have hev : MvPolynomial.eval (fun i : Fin 0 => ((Fin.elim0 i : ℤ) : K)) f = f.coeff 0 := by
          conv_lhs => rw [hf_C]
          simp
        rw [hf_C, ← hev, ← hz]
      refine ⟨Finsupp.single (Fin.elim0 : Fin 0 → ℕ) z, ?_, fun _ _ i => i.elim0⟩
      rw [Finsupp.sum_single_index (by simp : (0 : ℤ) • binomialMvPoly K 0 Fin.elim0 = 0), hf_eq]
      simp [binomialMvPoly, zsmul_eq_mul]
  | succ ℓ ih =>
      have hstep : ∀ (r : ℕ) (f : MvPolynomial (Fin (ℓ + 1)) K),
          f.degreeOf 0 ≤ r →
          (∀ n : Fin (ℓ + 1) → ℤ,
              MvPolynomial.eval (fun i => (n i : K)) f ∈ Set.range (Int.cast : ℤ → K)) →
          ∃ c : (Fin (ℓ + 1) → ℕ) →₀ ℤ,
            c.sum (fun b a => a • binomialMvPoly K (ℓ + 1) b) = f ∧
              ∀ b ∈ c.support, ∀ i : Fin (ℓ + 1), b i ≤ f.degreeOf i := by
        intro r
        induction r with
        | zero =>
            intro f hdeg0 hf
            have hdeg0_eq : f.degreeOf 0 = 0 := Nat.eq_zero_of_le_zero hdeg0
            let A := MvPolynomial (Fin ℓ) K
            let P : Polynomial A := MvPolynomial.finSuccEquiv K ℓ f
            have hP_deg : P.natDegree = 0 := by
              rw [MvPolynomial.natDegree_finSuccEquiv, hdeg0_eq]
            let g0 : A := P.coeff 0
            have hP_eq : P = Polynomial.C g0 := Polynomial.eq_C_of_natDegree_eq_zero hP_deg
            have hf_eq : f = MvPolynomial.rename Fin.succ g0 := by
              apply (MvPolynomial.finSuccEquiv K ℓ).injective
              rw [finSuccEquiv_rename_succ]
              exact hP_eq
            have hg0_int : ∀ s : Fin ℓ → ℤ,
                MvPolynomial.eval (fun j => (s j : K)) g0 ∈ Set.range (Int.cast : ℤ → K) := by
              intro s
              have hev := MvPolynomial.eval_eq_eval_mv_eval' (fun j => (s j : K)) (0 : K) f
              have hcons : (Fin.cons (0 : K) (fun j => (s j : K))) =
                  (fun i : Fin (ℓ + 1) => ((Fin.cons (0 : ℤ) s : Fin (ℓ + 1) → ℤ) i : K)) := by
                funext i
                refine Fin.cases ?_ ?_ i <;> simp
              rw [hcons] at hev
              have hmap : Polynomial.eval (0 : K)
                  (Polynomial.map (MvPolynomial.eval (fun j => (s j : K))) P) =
                  MvPolynomial.eval (fun j => (s j : K)) g0 := by
                rw [hP_eq, Polynomial.map_C, Polynomial.eval_C]
              rw [← hmap, ← hev]
              exact hf (Fin.cons 0 s)
            obtain ⟨c0, hc0_sum, hc0_deg⟩ := ih g0 hg0_int
            let consEmb : (Fin ℓ → ℕ) ↪ (Fin (ℓ + 1) → ℕ) :=
              ⟨fun b' => Fin.cons (α := fun _ => ℕ) 0 b', fun b₁ b₂ h => by
                funext j
                simpa [Fin.cons_succ] using congrFun h j.succ⟩
            refine ⟨c0.embDomain consEmb, ?_, ?_⟩
            · rw [Finsupp.sum, Finsupp.support_embDomain, Finset.sum_map]
              calc
                ∑ b' ∈ c0.support,
                    (c0.embDomain consEmb) (consEmb b') • binomialMvPoly K (ℓ + 1) (consEmb b')
                  = ∑ b' ∈ c0.support, c0 b' • MvPolynomial.rename Fin.succ (binomialMvPoly K ℓ b') := by
                      refine Finset.sum_congr rfl fun b' _ => ?_
                      rw [Finsupp.embDomain_apply_self]
                      congr 1
                      change binomialMvPoly K (ℓ + 1) (Fin.cons (α := fun _ => ℕ) 0 b') = _
                      simp only [binomialMvPoly, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
                        Ring.choose_zero_right, one_mul, map_prod, Ring.map_choose,
                        MvPolynomial.rename_X]
                _ = MvPolynomial.rename Fin.succ
                      (c0.sum fun b' a => a • binomialMvPoly K ℓ b') := by
                      rw [Finsupp.sum, map_sum]
                      refine Finset.sum_congr rfl fun b' _ => ?_
                      rw [map_zsmul]
                _ = f := by rw [hc0_sum, ← hf_eq]
            · intro b hb i
              rw [Finsupp.support_embDomain, Finset.mem_map] at hb
              obtain ⟨b', hb', rfl⟩ := hb
              refine Fin.cases ?_ ?_ i
              · change Fin.cons (α := fun _ => ℕ) 0 b' 0 ≤ f.degreeOf 0
                simp
              · intro j
                have hle := hc0_deg b' hb' j
                have hdeg_succ : g0.degreeOf j ≤ f.degreeOf j.succ :=
                  MvPolynomial.degreeOf_coeff_finSuccEquiv f j 0
                change Fin.cons (α := fun _ => ℕ) 0 b' j.succ ≤ f.degreeOf j.succ
                simpa using hle.trans hdeg_succ
        | succ d ih_r =>
            intro f hdeg0 hf
            by_cases hle_d : f.degreeOf 0 ≤ d
            · exact ih_r f hle_d hf
            · have hdeg0_eq : f.degreeOf 0 = d + 1 := by omega
              let r := d + 1
              let A := MvPolynomial (Fin ℓ) K
              let P : Polynomial A := MvPolynomial.finSuccEquiv K ℓ f
              let B := TauCeti.binomialPolynomialBasis A
              let g : ℕ → A := fun k => B.repr P k
              have hP_degLE : P ∈ Polynomial.degreeLE A r := by
                rw [Polynomial.mem_degreeLE]
                exact Polynomial.degree_le_natDegree.trans (by
                  rw [MvPolynomial.natDegree_finSuccEquiv, hdeg0_eq])
              have hsupp : (B.repr P).support ⊆ Finset.range (r + 1) := by
                have hmem : P ∈ Submodule.span A (B '' Set.Iic r) := by
                  rwa [TauCeti.span_binomialPolynomialBasis_image_Iic_eq_degreeLE A r]
                have hsub := (B.mem_span_image (m := P) (s := Set.Iic r)).mp hmem
                intro k hk
                exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hsub hk))
              have hP_eq : P = ∑ k ∈ Finset.range (r + 1),
                  Polynomial.C (g k) * Ring.choose (Polynomial.X : Polynomial A) k := by
                rw [← B.linearCombination_repr P, Finsupp.linearCombination_apply, Finsupp.sum]
                rw [Finset.sum_subset hsupp]
                · refine Finset.sum_congr rfl fun k _ => ?_
                  rw [TauCeti.binomialPolynomialBasis_apply, Polynomial.smul_eq_C_mul]
                · intro k _ hk
                  rw [Finsupp.notMem_support_iff.mp hk, zero_smul]
              -- Isolate top coefficient `g r` via `r`-fold polynomial forward difference `polyDiff`.
              have hdiff_P : polyDiff^[r] P = Polynomial.C (g r) := by
                rw [hP_eq]
                exact polyDiff_iterate_binomial_sum r g
              -- Hence `g r` takes integer values on `ℤ^ℓ`.
              have hgr_int : ∀ s : Fin ℓ → ℤ,
                  MvPolynomial.eval (fun j => (s j : K)) (g r) ∈ Set.range (Int.cast : ℤ → K) := by
                intro s
                let e : A →+* K := MvPolynomial.eval (fun j => (s j : K))
                have hq_int : ∀ m : ℤ,
                    Polynomial.eval (m : K) (Polynomial.map e P) ∈ Set.range (Int.cast : ℤ → K) := by
                  intro m
                  have hev := MvPolynomial.eval_eq_eval_mv_eval' (fun j => (s j : K)) (m : K) f
                  have hcons : (Fin.cons (m : K) (fun j => (s j : K))) =
                      (fun i : Fin (ℓ + 1) => ((Fin.cons m s : Fin (ℓ + 1) → ℤ) i : K)) := by
                    funext i
                    refine Fin.cases ?_ ?_ i <;> simp
                  rw [hcons] at hev
                  change Polynomial.eval (m : K) (Polynomial.map e P) ∈ _
                  rw [← hev]
                  exact hf (Fin.cons m s)
                have hiter := eval_polyDiff_iterate_mem_intRange K (Polynomial.map e P) hq_int r 0
                rw [← map_polyDiff_iterate e P r, hdiff_P, Polynomial.map_C, Polynomial.eval_C] at hiter
                exact hiter
              -- Show `g r = r! • P.coeff r` so `(g r).degreeOf j ≤ f.degreeOf j.succ`.
              have hcoeff_r : P.coeff r = g r * algebraMap ℚ A (r.factorial : ℚ)⁻¹ := by
                rw [hP_eq]
                exact top_binomial_coeff_eq r g
              have hgr_eq : g r = MvPolynomial.C (r.factorial : K) * P.coeff r := by
                have hfac : MvPolynomial.C (r.factorial : K) =
                    algebraMap ℚ A (r.factorial : ℚ) := by
                  simp
                rw [hcoeff_r, hfac, mul_left_comm, ← map_mul,
                  mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)),
                  map_one, mul_one]
              have hgr_deg : ∀ j : Fin ℓ, (g r).degreeOf j ≤ f.degreeOf j.succ := fun j => by
                rw [hgr_eq]
                exact (MvPolynomial.degreeOf_C_mul_le (P.coeff r) j (r.factorial : K)).trans
                  (MvPolynomial.degreeOf_coeff_finSuccEquiv f j r)
              -- Subtract the top binomial term `h_top`.
              let h_top : MvPolynomial (Fin (ℓ + 1)) K :=
                MvPolynomial.rename Fin.succ (g r) *
                  Ring.choose (MvPolynomial.X 0 : MvPolynomial (Fin (ℓ + 1)) K) r
              let f₁ : MvPolynomial (Fin (ℓ + 1)) K := f - h_top
              have htop_int : h_top ∈ intValuedMvSubring K (ℓ + 1) := by
                rw [mem_intValuedMvSubring_iff]
                intro n
                obtain ⟨z₁, hz₁⟩ := hgr_int (fun j => n j.succ)
                refine ⟨z₁ * Ring.choose (n 0) r, ?_⟩
                simp only [h_top, map_mul, Ring.map_choose, MvPolynomial.eval_X,
                  MvPolynomial.eval_rename, TauCeti.Ring.choose_intCast, Int.cast_mul]
                exact congrArg (· * ((Ring.choose (n 0) r : ℤ) : K)) hz₁
              have hf₁_int : ∀ n : Fin (ℓ + 1) → ℤ,
                  MvPolynomial.eval (fun i => (n i : K)) f₁ ∈ Set.range (Int.cast : ℤ → K) := by
                rw [← mem_intValuedMvSubring_iff]
                exact sub_mem ((mem_intValuedMvSubring_iff K (ℓ + 1) f).mpr hf) htop_int
              have hfin_f₁ : MvPolynomial.finSuccEquiv K ℓ f₁ =
                  ∑ k ∈ Finset.range r,
                    Polynomial.C (g k) * Ring.choose (Polynomial.X : Polynomial A) k := by
                have hfin_top : MvPolynomial.finSuccEquiv K ℓ h_top =
                    Polynomial.C (g r) * Ring.choose (Polynomial.X : Polynomial A) r := by
                  simp only [h_top, map_mul, Ring.map_choose, finSuccEquiv_rename_succ,
                    MvPolynomial.finSuccEquiv_X_zero]
                rw [map_sub, hfin_top]
                change P - Polynomial.C (g r) * Ring.choose (Polynomial.X : Polynomial A) r = _
                rw [hP_eq, Finset.sum_range_succ, add_sub_cancel_right]
              have hf₁_deg0 : f₁.degreeOf 0 ≤ d := by
                rw [← MvPolynomial.natDegree_finSuccEquiv, hfin_f₁]
                have hmem : ∑ k ∈ Finset.range r,
                    Polynomial.C (g k) * Ring.choose (Polynomial.X : Polynomial A) k ∈
                    Polynomial.degreeLE A d := by
                  refine Submodule.sum_mem _ fun k hk => ?_
                  rw [← Polynomial.smul_eq_C_mul]
                  refine Submodule.smul_mem _ (g k) ?_
                  rw [Polynomial.mem_degreeLE, TauCeti.degree_ringChoose_X]
                  exact WithBot.coe_le_coe.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
                exact Polynomial.natDegree_le_of_degree_le (Polynomial.mem_degreeLE.mp hmem)
              have hf₁_deg_succ : ∀ j : Fin ℓ, f₁.degreeOf j.succ ≤ f.degreeOf j.succ := fun j => by
                refine (degreeOf_sub_le K (ℓ + 1) j.succ f h_top).trans (max_le le_rfl ?_)
                refine (MvPolynomial.degreeOf_mul_le j.succ _ _).trans ?_
                rw [MvPolynomial.degreeOf_rename_of_injective (Fin.succ_injective ℓ) j,
                  degreeOf_ringChoose_X_of_ne K (ℓ + 1) (Fin.succ_ne_zero j) r, add_zero]
                exact hgr_deg j
              -- Apply outer IH to `g r` and inner IH to `f₁`, then recombine.
              obtain ⟨c_top, hc_top_sum, hc_top_deg⟩ := ih (g r) hgr_int
              obtain ⟨c₁, hc₁_sum, hc₁_deg⟩ := ih_r f₁ hf₁_deg0 hf₁_int
              let consEmb : (Fin ℓ → ℕ) ↪ (Fin (ℓ + 1) → ℕ) :=
                ⟨fun b' => Fin.cons (α := fun _ => ℕ) r b', fun b₁ b₂ h => by
                  funext j
                  simpa [Fin.cons_succ] using congrFun h j.succ⟩
              have hcons_sum :
                  (c_top.embDomain consEmb).sum (fun b a => a • binomialMvPoly K (ℓ + 1) b) =
                    h_top := by
                rw [Finsupp.sum, Finsupp.support_embDomain, Finset.sum_map]
                calc
                  ∑ b' ∈ c_top.support,
                      (c_top.embDomain consEmb) (consEmb b') •
                        binomialMvPoly K (ℓ + 1) (consEmb b')
                    = ∑ b' ∈ c_top.support,
                        c_top b' • (MvPolynomial.rename Fin.succ (binomialMvPoly K ℓ b') *
                          Ring.choose (MvPolynomial.X 0 : MvPolynomial (Fin (ℓ + 1)) K) r) := by
                        refine Finset.sum_congr rfl fun b' _ => ?_
                        rw [Finsupp.embDomain_apply_self]
                        congr 1
                        change binomialMvPoly K (ℓ + 1) (Fin.cons (α := fun _ => ℕ) r b') = _
                        simp only [binomialMvPoly, Fin.prod_univ_succ, Fin.cons_zero,
                          Fin.cons_succ, map_prod, Ring.map_choose, MvPolynomial.rename_X,
                          mul_comm]
                  _ = MvPolynomial.rename Fin.succ
                        (c_top.sum fun b' a => a • binomialMvPoly K ℓ b') *
                        Ring.choose (MvPolynomial.X 0 : MvPolynomial (Fin (ℓ + 1)) K) r := by
                        rw [Finsupp.sum, map_sum, Finset.sum_mul]
                        refine Finset.sum_congr rfl fun b' _ => ?_
                        rw [map_zsmul, smul_mul_assoc]
                  _ = h_top := by rw [hc_top_sum]
              refine ⟨c₁ + c_top.embDomain consEmb, ?_, ?_⟩
              · rw [Finsupp.sum_add_index'
                    (fun b => zero_smul ℤ (binomialMvPoly K (ℓ + 1) b))
                    (fun b a₁ a₂ => add_smul a₁ a₂ (binomialMvPoly K (ℓ + 1) b)),
                  hc₁_sum, hcons_sum]
                simp [f₁]
              · intro b hb i
                have hmem := Finsupp.support_add hb
                rcases Finset.mem_union.mp hmem with hb₁ | hb_top
                · refine Fin.cases ?_ ?_ i
                  · exact (hc₁_deg b hb₁ 0).trans (hf₁_deg0.trans (by omega))
                  · intro j
                    exact (hc₁_deg b hb₁ j.succ).trans (hf₁_deg_succ j)
                · rw [Finsupp.support_embDomain, Finset.mem_map] at hb_top
                  obtain ⟨b', hb', rfl⟩ := hb_top
                  refine Fin.cases ?_ ?_ i
                  · change Fin.cons (α := fun _ => ℕ) r b' 0 ≤ f.degreeOf 0
                    simp [r, hdeg0_eq]
                  · intro j
                    change Fin.cons (α := fun _ => ℕ) r b' j.succ ≤ f.degreeOf j.succ
                    simpa using (hc_top_deg b' hb' j).trans (hgr_deg j)
      intro f hf
      exact hstep (f.degreeOf 0) f le_rfl hf

/-- **Humphreys §26.1, Lemma (p. 152, verbatim with uniqueness & coordinatewise degree bounds):**
Let `f ∈ K[T₁, …, T_ℓ]` over a characteristic-zero field `K`. Then `f(n₁, …, n_ℓ) ∈ ℤ` for all
`n₁, …, n_ℓ ∈ ℤ` if and only if `f` has a unique `ℤ`-linear expansion in the binomial products
`∏_{i : Fin ℓ} (T_i choose b_i)` (`b_i ∈ ℕ = ℤ⁺`), and every multi-index `b` in the support of
that expansion satisfies `b i ≤ f.degreeOf i` for all `i : Fin ℓ`. -/
theorem existsUnique_zsmul_binomialMvPoly_and_degreeOf_le
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) (f : MvPolynomial (Fin ℓ) K) :
    (∀ n : Fin ℓ → ℤ,
        MvPolynomial.eval (fun i => (n i : K)) f ∈ Set.range (Int.cast : ℤ → K)) ↔
      ∃! c : (Fin ℓ → ℕ) →₀ ℤ,
        c.sum (fun b a => a • binomialMvPoly K ℓ b) = f ∧
          ∀ b ∈ c.support, ∀ i : Fin ℓ, b i ≤ f.degreeOf i := by
  constructor
  · intro hf
    obtain ⟨c, hc_sum, hc_deg⟩ := exists_zsmul_binomialMvPoly_and_degreeOf_le K ℓ f hf
    refine ⟨c, ⟨hc_sum, hc_deg⟩, ?_⟩
    rintro c' ⟨hc'_sum, _⟩
    exact linearIndependent_binomialMvPoly_int K ℓ
      (by simpa [Finsupp.linearCombination_apply] using hc'_sum.trans hc_sum.symm)
  · rintro ⟨c, ⟨hc_sum, _⟩, _⟩
    rw [← mem_intValuedMvSubring_iff, ← hc_sum]
    exact sum_mem fun b _ => zsmul_mem (binomialMvPoly_mem_intValuedMvSubring K ℓ b) (c b)

/-- **Span & subring-generation characterization of `intValuedMvSubring K ℓ` (H §26.1, p. 152):**
The subring of integer-valued polynomials in `K[T₁, …, T_ℓ]` coincides as a set with the
`ℤ`-span of `{binomialMvPoly K ℓ b | b : Fin ℓ → ℕ}`, and equals as a subring the closure of
the single-variable binomial polynomials `{Ring.choose (X i) k | i : Fin ℓ, k : ℕ}`. -/
theorem intValuedMvSubring_eq_span_and_subringClosure
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) :
    (intValuedMvSubring K ℓ : Set (MvPolynomial (Fin ℓ) K)) =
        (Submodule.span ℤ (Set.range (binomialMvPoly K ℓ)) :
          Set (MvPolynomial (Fin ℓ) K)) ∧
      intValuedMvSubring K ℓ =
        Subring.closure
          (Set.range fun p : Fin ℓ × ℕ =>
            Ring.choose (MvPolynomial.X p.1 : MvPolynomial (Fin ℓ) K) p.2) := by
  have hspan_eq :
      (intValuedMvSubring K ℓ : Set (MvPolynomial (Fin ℓ) K)) =
        (Submodule.span ℤ (Set.range (binomialMvPoly K ℓ)) :
          Set (MvPolynomial (Fin ℓ) K)) := by
    ext f
    simp only [SetLike.mem_coe]
    constructor
    · intro hf
      obtain ⟨c, ⟨hc_sum, _⟩, _⟩ :=
        (existsUnique_zsmul_binomialMvPoly_and_degreeOf_le K ℓ f).mp
          ((mem_intValuedMvSubring_iff K ℓ f).mp hf)
      rw [← hc_sum]
      exact Submodule.sum_mem _ fun b _ =>
        Submodule.smul_mem _ (c b) (Submodule.subset_span ⟨b, rfl⟩)
    · intro hf
      induction hf using Submodule.span_induction with
      | mem _ hx =>
          rcases hx with ⟨b, rfl⟩
          exact binomialMvPoly_mem_intValuedMvSubring K ℓ b
      | zero => exact zero_mem _
      | add _ _ _ _ hx hy => exact add_mem hx hy
      | smul a _ _ hx => exact zsmul_mem hx a
  refine ⟨hspan_eq, le_antisymm ?_ ?_⟩
  · intro f hf
    have hf_span : f ∈ Submodule.span ℤ (Set.range (binomialMvPoly K ℓ)) := by
      have : f ∈ (intValuedMvSubring K ℓ : Set (MvPolynomial (Fin ℓ) K)) := hf
      rwa [hspan_eq] at this
    clear hf
    induction hf_span using Submodule.span_induction with
    | mem _ hx =>
        rcases hx with ⟨b, rfl⟩
        exact prod_mem fun i _ => Subring.subset_closure ⟨(i, b i), rfl⟩
    | zero => exact zero_mem _
    | add _ _ _ _ hx hy => exact add_mem hx hy
    | smul a _ _ hx => exact zsmul_mem hx a
  · rw [Subring.closure_le]
    rintro _ ⟨⟨i, k⟩, rfl⟩
    rw [SetLike.mem_coe, mem_intValuedMvSubring_iff]
    intro n
    refine ⟨Ring.choose (n i) k, ?_⟩
    simp only [Ring.map_choose, MvPolynomial.eval_X, TauCeti.Ring.choose_intCast]

private theorem exists_intValuedBinomialBasis
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) :
    ∃ B : Module.Basis (Fin ℓ → ℕ) ℤ (intValuedMvSubring K ℓ),
      ∀ b : Fin ℓ → ℕ,
        ((B b : intValuedMvSubring K ℓ) : MvPolynomial (Fin ℓ) K) =
          binomialMvPoly K ℓ b := by
  let v : (Fin ℓ → ℕ) → intValuedMvSubring K ℓ :=
    fun b => ⟨binomialMvPoly K ℓ b, binomialMvPoly_mem_intValuedMvSubring K ℓ b⟩
  let incl : intValuedMvSubring K ℓ →ₗ[ℤ] MvPolynomial (Fin ℓ) K :=
    (intValuedMvSubring K ℓ).toAddSubgroup.subtype.toIntLinearMap
  have hli : LinearIndependent ℤ v :=
    (linearIndependent_binomialMvPoly_int K ℓ).of_comp incl
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    intro x _
    obtain ⟨c, ⟨hc_sum, _⟩, _⟩ :=
      (existsUnique_zsmul_binomialMvPoly_and_degreeOf_le K ℓ x.1).mp
        ((mem_intValuedMvSubring_iff K ℓ x.1).mp x.2)
    have hx_eq : x = c.sum fun b a => a • v b := by
      apply Subtype.ext
      change (x : MvPolynomial (Fin ℓ) K) =
        (intValuedMvSubring K ℓ).subtype (c.sum fun b a => a • v b)
      rw [← hc_sum, Finsupp.sum, Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl fun b _ => rfl
    rw [hx_eq]
    exact Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ (c b) (Submodule.subset_span ⟨b, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun b => by simp [Module.Basis.mk_apply, v]⟩

/-- **Bundled `ℤ`-basis form of Humphreys Lemma 26.1 (p. 152):**
The binomial products `b ↦ ∏_{i : Fin ℓ} (T_i choose b_i)` form a free `ℤ`-module basis of
`intValuedMvSubring K ℓ` (using the `TauCeti.mvBinomialPolynomialBasis` `.choose` pattern so no
`def` carries a `sorry`). -/
noncomputable def intValuedBinomialBasis
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) :
    Module.Basis (Fin ℓ → ℕ) ℤ (intValuedMvSubring K ℓ) :=
  (exists_intValuedBinomialBasis K ℓ).choose

@[simp]
theorem coe_intValuedBinomialBasis_apply
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) (b : Fin ℓ → ℕ) :
    ((intValuedBinomialBasis K ℓ b : intValuedMvSubring K ℓ) :
        MvPolynomial (Fin ℓ) K) =
      binomialMvPoly K ℓ b :=
  (exists_intValuedBinomialBasis K ℓ).choose_spec b

/-- **Univariate (`ℓ = 1`) specialization of Humphreys Lemma 26.1 (p. 152, as invoked in
Corollary 26.2 on p. 153):**
A polynomial `p ∈ K[X]` satisfies `p(ℤ) ⊆ ℤ` if and only if it has a unique `ℤ`-linear
expansion in `{Ring.choose Polynomial.X k | k : ℕ}` supported on `k ≤ p.natDegree`. -/
theorem existsUnique_zsmul_ringChoose_X_and_natDegree_le
    (K : Type u) [Field K] [CharZero K] (p : Polynomial K) :
    (∀ n : ℤ, Polynomial.eval (n : K) p ∈ Set.range (Int.cast : ℤ → K)) ↔
      ∃! c : ℕ →₀ ℤ,
        c.sum (fun k a => a • Ring.choose (Polynomial.X : Polynomial K) k) = p ∧
          ∀ k ∈ c.support, k ≤ p.natDegree := by
  let f : MvPolynomial (Fin 1) K := p.toMvPolynomial (0 : Fin 1)
  have hdeg : f.degreeOf 0 = p.natDegree := by
    rw [← MvPolynomial.natDegree_finSuccEquiv]
    have hfin : MvPolynomial.finSuccEquiv K 0 f =
        Polynomial.map (MvPolynomial.C : K →+* MvPolynomial (Fin 0) K) p := by
      have hhom : (MvPolynomial.finSuccEquiv K 0).toRingHom.comp
          (Polynomial.toMvPolynomial (R := K) (0 : Fin 1)).toRingHom =
          Polynomial.mapRingHom (MvPolynomial.C : K →+* MvPolynomial (Fin 0) K) := by
        apply Polynomial.ringHom_ext
        · intro a
          simp [MvPolynomial.finSuccEquiv_apply]
        · simp [MvPolynomial.finSuccEquiv_X_zero]
      exact RingHom.congr_fun hhom p
    rw [hfin, Polynomial.natDegree_map_eq_of_injective (MvPolynomial.C_injective (Fin 0) K)]
  have heval_iff :
      (∀ n : ℤ, Polynomial.eval (n : K) p ∈ Set.range (Int.cast : ℤ → K)) ↔
        (∀ n : Fin 1 → ℤ,
          MvPolynomial.eval (fun i => (n i : K)) f ∈ Set.range (Int.cast : ℤ → K)) := by
    constructor
    · intro hp n
      simpa [f] using hp (n 0)
    · intro hf n
      simpa [f] using hf (fun _ => n)
  let eIdx : ℕ ≃ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm
  let eFinsupp : (ℕ →₀ ℤ) ≃ ((Fin 1 → ℕ) →₀ ℤ) := Finsupp.equivCongrLeft eIdx
  have hsum_eq : ∀ c : ℕ →₀ ℤ,
      (eFinsupp c).sum (fun b a => a • binomialMvPoly K 1 b) =
        (c.sum fun k a => a • Ring.choose (Polynomial.X : Polynomial K) k).toMvPolynomial 0 := by
    intro c
    rw [Finsupp.sum, Finsupp.sum, map_sum]
    have hsupp : (eFinsupp c).support = c.support.map eIdx.toEmbedding := by
      ext b
      simp [eFinsupp, eIdx]
    rw [hsupp, Finset.sum_map]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [eFinsupp, Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_apply,
      Equiv.toEmbedding_apply, Equiv.symm_apply_apply, map_zsmul, binomialMvPoly,
      Fin.prod_univ_one, Ring.map_choose, Polynomial.toMvPolynomial_X]
    rfl
  have hcond_iff : ∀ c : ℕ →₀ ℤ,
      (c.sum (fun k a => a • Ring.choose (Polynomial.X : Polynomial K) k) = p ∧
          ∀ k ∈ c.support, k ≤ p.natDegree) ↔
        ((eFinsupp c).sum (fun b a => a • binomialMvPoly K 1 b) = f ∧
          ∀ b ∈ (eFinsupp c).support, ∀ i : Fin 1, b i ≤ f.degreeOf i) := by
    intro c
    constructor
    · rintro ⟨hc_sum, hc_deg⟩
      refine ⟨by rw [hsum_eq, hc_sum], ?_⟩
      intro b hb i
      rw [Fin.eq_zero i, hdeg]
      have hk : eIdx.symm b ∈ c.support := by
        simpa [eFinsupp] using hb
      simpa [eIdx] using hc_deg (eIdx.symm b) hk
    · rintro ⟨hc_sum, hc_deg⟩
      refine ⟨Polynomial.toMvPolynomial_injective 0 ((hsum_eq c).symm.trans hc_sum), ?_⟩
      intro k hk
      have hb : eIdx k ∈ (eFinsupp c).support := by
        simpa [eFinsupp] using hk
      simpa [eIdx, hdeg] using hc_deg (eIdx k) hb 0
  rw [heval_iff, existsUnique_zsmul_binomialMvPoly_and_degreeOf_le K 1 f]
  constructor
  · rintro ⟨c', hc', huniq⟩
    refine ⟨eFinsupp.symm c', (hcond_iff _).mpr (by simpa using hc'), fun c hc => ?_⟩
    exact eFinsupp.injective (by simpa using huniq (eFinsupp c) ((hcond_iff c).mp hc))
  · rintro ⟨c, hc, huniq⟩
    refine ⟨eFinsupp c, (hcond_iff c).mp hc, fun c' hc' => ?_⟩
    have := huniq (eFinsupp.symm c') ((hcond_iff _).mpr (by simpa using hc'))
    exact eFinsupp.symm.injective (by simpa using this)

end MultivariateBinomialBasis

end Humphreys26_1
