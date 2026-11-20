import Humphreys.Ch7.AdmissibleLattice27_1
import Humphreys.Ch7.Kostant.GapB
import Humphreys.Ch7.Kostant.GapC
import Humphreys.Ch7.Kostant.GapCRootPlane

open LieAlgebra LieAlgebra.IsKilling LieModule RootPairing TauCeti TauCeti.Associative

universe u v

namespace Humphreys26_3B

section ClosedSubsetBasis

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

noncomputable local instance instAlgebraRatUEA :
    Algebra ℚ (_root_.UniversalEnvelopingAlgebra K L) :=
  Algebra.compHom (_root_.UniversalEnvelopingAlgebra K L) (algebraMap ℚ K)

attribute [local instance] TauCeti.moduleNNRat

/-- **Humphreys §26.3 (p. 154, verbatim): Closed subset of roots `Ψ ⊆ Φ`.**
A subset `Ψ : Set H.root` is closed if `α, β ∈ Ψ` and `α + β ∈ Φ` imply `α + β ∈ Ψ`. -/
def IsClosedRootSubset
    (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
    (Ψ : Set H.root) : Prop :=
  ∀ ⦃α β γ : H.root⦄, α ∈ Ψ → β ∈ Ψ →
    (rootSystem H).root γ = (rootSystem H).root α + (rootSystem H).root β → γ ∈ Ψ

/-- **Humphreys §26.3 (p. 154, verbatim): Asymmetry hypothesis `Ψ ∩ -Ψ = ∅`.**
No two roots in `Ψ` are negatives of one another in `H*`. -/
def IsAsymmetricRootSubset
    (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
    (Ψ : Set H.root) : Prop :=
  ∀ ⦃α β : H.root⦄, α ∈ Ψ → β ∈ Ψ →
    (rootSystem H).root α ≠ -(rootSystem H).root β

/-- **Humphreys §26.3 Lemma B (p. 154): Subring `𝔛 ⊂ 𝔘(L)` generated (with `1`) by
`{x_α^t / t! | α ∈ Ψ, t ∈ ℕ = ℤ⁺}`.** -/
noncomputable def closedSubsetSubring
    (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
    (Ψ : Set H.root) (x : Weight K H L → L) :
    Subring (_root_.UniversalEnvelopingAlgebra K L) :=
  Subring.closure
    (Set.range fun p : ↥Ψ × ℕ =>
      dividedPower p.2
        (_root_.UniversalEnvelopingAlgebra.ι K (x ((p.1 : H.root) : Weight K H L))))

/-- **Humphreys §26.3 Lemma B (p. 154): Ordered divided-power product
`∏_{α ∈ Ψ} x_α^{t_α} / t_α!` written in a fixed ordering `ψOrd : Fin s ≃ ↥Ψ`.** -/
noncomputable def closedSubsetMonomial {s : ℕ}
    {Ψ : Set H.root} (ψOrd : Fin s ≃ ↥Ψ) (x : Weight K H L → L)
    (t : Fin s → ℕ) : _root_.UniversalEnvelopingAlgebra K L :=
  (List.ofFn fun j : Fin s =>
    dividedPower (t j)
      (_root_.UniversalEnvelopingAlgebra.ι K
        (x (((ψOrd j : ↥Ψ) : H.root) : Weight K H L)))).prod

/-- **PBW `K`-linear independence of ordered `Ψ`-monomials (H p. 154, Proof line 2):**
For any Chevalley system `hx`, any subset `Ψ : Set H.root`, and any bijection
`ψOrd : Fin s ≃ ↥Ψ`, the ordered divided-power products `closedSubsetMonomial ψOrd x` are
`K`-linearly independent in `UniversalEnvelopingAlgebra K L`. -/
theorem closedSubsetMonomial_linearIndependent_over_field
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {s : ℕ} {Ψ : Set H.root} (ψOrd : Fin s ≃ ↥Ψ) :
    LinearIndependent K (closedSubsetMonomial ψOrd x) := by
  classical
  obtain ⟨b⟩ := (rootSystem H).nonempty_base
  let r : ℕ := Fintype.card ({α : H.root // ¬ α ∈ Ψ} ⊕ ↥b.support)
  let restEquiv : Fin r ≃ {α : H.root // ¬ α ∈ Ψ} ⊕ ↥b.support := (Fintype.equivFin _).symm
  let e : Fin (s + r) ≃ H.root ⊕ ↥b.support :=
    finSumFinEquiv.symm.trans
      ((Equiv.sumCongr ψOrd restEquiv).trans
        (((Equiv.sumAssoc ↥Ψ {α : H.root // ¬ α ∈ Ψ} ↥b.support).symm).trans
          (Equiv.sumCongr (Equiv.sumCompl (· ∈ Ψ)) (Equiv.refl ↥b.support))))
  let B_L : Module.Basis (Fin (s + r)) K L :=
    (Humphreys26_4.GapB.chevalleyAmbientBasis hx b).reindex e.symm
  let B_U : Module.Basis (Fin (s + r) → ℕ) K (_root_.UniversalEnvelopingAlgebra K L) :=
    B_L.pbwPolynomialBasis (fun _ => Humphreys26_4.GapB.dividedPowerPolynomialBasisK K)
  have haeval_dp : ∀ (u : _root_.UniversalEnvelopingAlgebra K L) (n : ℕ),
      Polynomial.aeval u (Humphreys26_4.GapB.dividedPowerPolynomialBasisK K n) =
        dividedPower n u := by
    intro u n
    rw [Humphreys26_4.GapB.dividedPowerPolynomialBasisK_apply, map_smul, map_pow,
      Polynomial.aeval_X, dividedPower_def]
    have hrat : (algebraMap ℚ K) ((n.factorial : ℚ)⁻¹) = (n.factorial : K)⁻¹ := by
      rw [map_inv₀, map_natCast]
    rw [Algebra.smul_def, ← hrat]
    rfl
  let ext0 : (Fin s → ℕ) → (Fin (s + r) → ℕ) := fun t => Fin.append t (fun _ => 0)
  have hext0_inj : Function.Injective ext0 := by
    intro t₁ t₂ h
    ext j
    have hj := congrFun h (Fin.castAdd r j)
    simpa only [ext0, Fin.append_left] using hj
  have hcomp : closedSubsetMonomial ψOrd x = B_U ∘ ext0 := by
    funext t
    simp only [Function.comp_apply, B_U, Module.Basis.pbwPolynomialBasis_apply]
    let f : Fin (s + r) → _root_.UniversalEnvelopingAlgebra K L := fun idx =>
      Polynomial.aeval (_root_.UniversalEnvelopingAlgebra.ι K (B_L idx))
        (Humphreys26_4.GapB.dividedPowerPolynomialBasisK K (ext0 t idx))
    have hsplit : List.ofFn f =
        List.ofFn (fun j : Fin s => f (Fin.castAdd r j)) ++
          List.ofFn (fun i : Fin r => f (Fin.natAdd s i)) :=
      List.ofFn_add
    change closedSubsetMonomial ψOrd x t = (List.ofFn f).prod
    rw [hsplit, List.prod_append]
    have hright : (List.ofFn fun i : Fin r => f (Fin.natAdd s i)).prod = 1 := by
      have h1 : (fun i : Fin r => f (Fin.natAdd s i)) = fun _ => 1 := by
        funext i
        dsimp only [f, ext0]
        rw [Fin.append_right, haeval_dp, dividedPower_zero]
      rw [h1, List.ofFn_const, List.prod_replicate, one_pow]
    rw [hright, mul_one]
    refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
    dsimp only [f, ext0]
    rw [Fin.append_left, haeval_dp]
    have hBL : B_L (Fin.castAdd r j) = x (((ψOrd j : ↥Ψ) : H.root) : Weight K H L) := by
      simp only [B_L, Module.Basis.reindex_apply, Equiv.symm_symm, e, Equiv.trans_apply,
        finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
        Equiv.sumAssoc_symm_apply_inl, Equiv.sumCompl_apply_inl,
        Humphreys26_4.GapB.chevalleyAmbientBasis_inl]
    rw [hBL]
  rw [hcomp]
  exact B_U.linearIndependent.comp ext0 hext0_inj

private def lookupExp {N : ℕ} : List (Fin N × ℕ) → Fin N → ℕ
  | [], _ => 0
  | (j, k) :: rest, i => if j = i then k else lookupExp rest i

private theorem lookupExp_zero_of_ne_zero {N : ℕ} :
    ∀ (xs : List (Fin (N + 1) × ℕ)), (∀ q ∈ xs, q.1 ≠ 0) → lookupExp xs 0 = 0
  | [], _ => rfl
  | (j, k) :: tl, hne => by
    have hj : j ≠ 0 := hne (j, k) (by simp)
    simp only [lookupExp, hj, ↓reduceIte]
    exact lookupExp_zero_of_ne_zero tl fun r hr => hne r (by simp [hr])

private theorem lookupExp_succ_eq_pmap {N : ℕ} (i : Fin N) :
    ∀ (xs : List (Fin (N + 1) × ℕ)) (hne : ∀ q ∈ xs, q.1 ≠ 0),
      lookupExp xs i.succ =
        lookupExp (xs.pmap (fun q (hq : q.1 ≠ 0) => (q.1.pred hq, q.2)) hne) i
  | [], _ => rfl
  | (j, k) :: tl, hne => by
    have hj : j ≠ 0 := hne (j, k) (by simp)
    have htl : ∀ r ∈ tl, r.1 ≠ 0 := fun r hr => hne r (by simp [hr])
    have heq_iff : (j.pred hj = i) ↔ (j = i.succ) :=
      ⟨fun h => by rw [← h, Fin.succ_pred], fun h => by subst h; simp⟩
    simp only [List.pmap, lookupExp, heq_iff]
    split_ifs
    · rfl
    · exact lookupExp_succ_eq_pmap i tl htl

private theorem prod_map_eq_prod_ofFn_of_pairwise {M : Type*} [Monoid M] :
    ∀ {N : ℕ} (g : Fin N → ℕ → M) (_ : ∀ i, g i 0 = 1) (l : List (Fin N × ℕ))
      (_ : l.Pairwise (fun p q => p.1 < q.1)),
      (l.map fun p => g p.1 p.2).prod =
        (List.ofFn fun i : Fin N => g i (lookupExp l i)).prod
  | 0, _, _, l, _ => by
    cases l with
    | nil => simp
    | cons p _ => exact Fin.elim0 p.1
  | N + 1, g, hg0, [], _ => by
    have hconst : (fun i : Fin (N + 1) => g i (lookupExp [] i)) = fun _ => (1 : M) := by
      funext i
      exact hg0 i
    simp [hconst, List.ofFn_const]
  | N + 1, g, hg0, (j, k) :: rest, hpw => by
    rw [List.pairwise_cons] at hpw
    obtain ⟨hhead, hpw_rest⟩ := hpw
    by_cases hj0 : j = 0
    · subst hj0
      have hne0 : ∀ q ∈ rest, q.1 ≠ 0 := fun q hq h0 => by
        have hlt := hhead q hq
        rw [h0] at hlt
        exact lt_irrefl 0 hlt
      let rest' : List (Fin N × ℕ) :=
        rest.pmap (fun q (hq : q.1 ≠ 0) => (q.1.pred hq, q.2)) hne0
      have hpw' : rest'.Pairwise (fun p q => p.1 < q.1) := by
        rw [List.pairwise_pmap]
        exact hpw_rest.imp_of_mem fun {a b} _ _ hab ha hb => by
          rw [← Fin.succ_lt_succ_iff, Fin.succ_pred, Fin.succ_pred]
          exact hab
      have hmap_eq :
          (rest.map fun p => g p.1 p.2) =
            (rest'.map fun p => g p.1.succ p.2) := by
        simp [rest', List.map_pmap]
      have hlookup0 : lookupExp ((0, k) :: rest) 0 = k := by
        simp [lookupExp]
      have hlookup_succ : ∀ i : Fin N,
          lookupExp ((0, k) :: rest) i.succ = lookupExp rest' i := by
        intro i
        have h0s : (0 : Fin (N + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
        simp only [lookupExp, h0s, ↓reduceIte]
        exact lookupExp_succ_eq_pmap i rest hne0
      rw [List.map_cons, List.prod_cons, hmap_eq,
        prod_map_eq_prod_ofFn_of_pairwise (fun i => g i.succ) (fun i => hg0 i.succ) rest' hpw',
        List.ofFn_succ, List.prod_cons, hlookup0]
      simp only [hlookup_succ]
    · have hall_ne0 : ∀ q ∈ ((j, k) :: rest), q.1 ≠ 0 := by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq_rest
        · exact hj0
        · have hj_pos : (0 : Fin (N + 1)) < j := Fin.pos_iff_ne_zero.mpr hj0
          exact ne_of_gt (lt_trans hj_pos (hhead q hq_rest))
      let l' : List (Fin N × ℕ) :=
        ((j, k) :: rest).pmap (fun q (hq : q.1 ≠ 0) => (q.1.pred hq, q.2)) hall_ne0
      have hpw_all : ((j, k) :: rest).Pairwise (fun p q => p.1 < q.1) :=
        List.pairwise_cons.mpr ⟨hhead, hpw_rest⟩
      have hpw' : l'.Pairwise (fun p q => p.1 < q.1) := by
        rw [List.pairwise_pmap]
        exact hpw_all.imp_of_mem fun {a b} _ _ hab ha hb => by
          rw [← Fin.succ_lt_succ_iff, Fin.succ_pred, Fin.succ_pred]
          exact hab
      have hmap_eq :
          (((j, k) :: rest).map fun p => g p.1 p.2) =
            (l'.map fun p => g p.1.succ p.2) := by
        simp [l', List.map_pmap]
      have hlookup0 : lookupExp ((j, k) :: rest) 0 = 0 :=
        lookupExp_zero_of_ne_zero ((j, k) :: rest) hall_ne0
      have hlookup_succ : ∀ i : Fin N,
          lookupExp ((j, k) :: rest) i.succ = lookupExp l' i := fun i =>
        lookupExp_succ_eq_pmap i ((j, k) :: rest) hall_ne0
      rw [hmap_eq,
        prod_map_eq_prod_ofFn_of_pairwise (fun i => g i.succ) (fun i => hg0 i.succ) l' hpw',
        List.ofFn_succ, List.prod_cons, hlookup0, hg0 0, one_mul]
      simp only [hlookup_succ]

private def invCount {α : Type*} (pos : α → ℕ) : List (α × ℕ) → ℕ
  | [] => 0
  | p :: rest => (rest.filter fun q => decide (pos q.1 < pos p.1)).length + invCount pos rest

private def wordMeasure {α : Type*} (pos : α → ℕ) (w : List (α × ℕ)) : ℕ :=
  invCount pos w + w.length

private theorem exists_adj_ge_of_not_pairwise {α : Type*} (pos : α → ℕ) :
    ∀ (w : List (α × ℕ)), ¬ w.Pairwise (fun p q => pos p.1 < pos q.1) →
      ∃ w₁ p q w₂, w = w₁ ++ p :: q :: w₂ ∧ pos q.1 ≤ pos p.1
  | [], h => absurd List.Pairwise.nil h
  | [_], h => absurd (List.pairwise_singleton _ _) h
  | p :: q :: rest, h => by
    by_cases hpq : pos p.1 < pos q.1
    · have hnot_tail : ¬ (q :: rest).Pairwise (fun u v => pos u.1 < pos v.1) := by
        intro htail
        apply h
        rw [List.pairwise_cons]
        refine ⟨fun u hu => ?_, htail⟩
        rcases List.mem_cons.mp hu with rfl | hu_rest
        · exact hpq
        · exact lt_trans hpq ((List.pairwise_cons.mp htail).1 u hu_rest)
      obtain ⟨w₁', p', q', w₂', heq, hge⟩ := exists_adj_ge_of_not_pairwise pos (q :: rest) hnot_tail
      exact ⟨p :: w₁', p', q', w₂', by simp [heq], hge⟩
    · exact ⟨[], p, q, rest, rfl, Nat.le_of_not_lt hpq⟩

private theorem invCount_swap_lt {α : Type*} (pos : α → ℕ)
    {p q : α × ℕ} (hlt : pos q.1 < pos p.1) (w₂ : List (α × ℕ)) :
    ∀ w₁ : List (α × ℕ),
      invCount pos (w₁ ++ q :: p :: w₂) < invCount pos (w₁ ++ p :: q :: w₂)
  | [] => by
    have hnot : ¬ pos p.1 < pos q.1 := by omega
    simp [invCount, hlt, hnot]
    omega
  | u :: rest => by
    have ih := invCount_swap_lt pos hlt w₂ rest
    have hflen :
        ((rest ++ q :: p :: w₂).filter fun v => decide (pos v.1 < pos u.1)).length =
          ((rest ++ p :: q :: w₂).filter fun v => decide (pos v.1 < pos u.1)).length := by
      simp only [List.filter_append, List.filter_cons, List.length_append]
      split_ifs <;> simp
    simp only [List.cons_append, invCount, hflen]
    omega

private theorem invCount_merge_le {α : Type*} (pos : α → ℕ)
    {p q r : α × ℕ} (hqp : pos q.1 = pos p.1) (hrp : pos r.1 = pos p.1) (w₂ : List (α × ℕ)) :
    ∀ w₁ : List (α × ℕ),
      invCount pos (w₁ ++ r :: w₂) ≤ invCount pos (w₁ ++ p :: q :: w₂)
  | [] => by
    simp [invCount, hqp, hrp]
  | u :: rest => by
    have ih := invCount_merge_le pos hqp hrp w₂ rest
    have hflen :
        ((rest ++ r :: w₂).filter fun v => decide (pos v.1 < pos u.1)).length ≤
          ((rest ++ p :: q :: w₂).filter fun v => decide (pos v.1 < pos u.1)).length := by
      simp only [List.filter_append, List.filter_cons, List.length_append, hqp, hrp]
      split_ifs <;> simp
    simp only [List.cons_append, invCount]
    omega

private theorem wordMeasure_swap_lt {α : Type*} (pos : α → ℕ)
    {p q : α × ℕ} (hlt : pos q.1 < pos p.1) (w₁ w₂ : List (α × ℕ)) :
    wordMeasure pos (w₁ ++ q :: p :: w₂) < wordMeasure pos (w₁ ++ p :: q :: w₂) := by
  have hinv := invCount_swap_lt pos hlt w₂ w₁
  simp only [wordMeasure, List.length_append, List.length_cons]
  omega

private theorem wordMeasure_merge_lt {α : Type*} (pos : α → ℕ)
    {p q r : α × ℕ} (hqp : pos q.1 = pos p.1) (hrp : pos r.1 = pos p.1) (w₁ w₂ : List (α × ℕ)) :
    wordMeasure pos (w₁ ++ r :: w₂) < wordMeasure pos (w₁ ++ p :: q :: w₂) := by
  have hinv := invCount_merge_le pos hqp hrp w₂ w₁
  simp only [wordMeasure, List.length_append, List.length_cons]
  omega

private noncomputable def psiWordProd {Ψ : Set H.root} (x : Weight K H L → L)
    (w : List (↥Ψ × ℕ)) : _root_.UniversalEnvelopingAlgebra K L :=
  (w.map fun p =>
    dividedPower p.2
      (_root_.UniversalEnvelopingAlgebra.ι K (x ((p.1 : H.root) : Weight K H L)))).prod

omit [LieAlgebra.IsKilling K L] [LieModule.IsTriangularizable K H L] in
private theorem psiWordProd_append {Ψ : Set H.root} (x : Weight K H L → L)
    (w₁ w₂ : List (↥Ψ × ℕ)) :
    psiWordProd x (w₁ ++ w₂) = psiWordProd x w₁ * psiWordProd x w₂ := by
  simp only [psiWordProd, List.map_append, List.prod_append]

private noncomputable def psiLowDegSpan (Ψ : Set H.root) (x : Weight K H L → L) (d : ℕ) :
    Submodule ℤ (_root_.UniversalEnvelopingAlgebra K L) :=
  Submodule.span ℤ
    {u : _root_.UniversalEnvelopingAlgebra K L |
      ∃ w : List (↥Ψ × ℕ), Humphreys26_4.GapC.rootWordDeg w < d ∧ psiWordProd x w = u}

omit [LieAlgebra.IsKilling K L] [LieModule.IsTriangularizable K H L] in
private theorem psiWordProd_mem_psiLowDegSpan {Ψ : Set H.root} {x : Weight K H L → L}
    {w : List (↥Ψ × ℕ)} {d : ℕ} (hdeg : Humphreys26_4.GapC.rootWordDeg w < d) :
    psiWordProd x w ∈ psiLowDegSpan Ψ x d :=
  Submodule.subset_span ⟨w, hdeg, rfl⟩

private theorem comb_ne_zero_of_lin {α β : H.root}
    (hlin : LinearIndependent K ![(rootSystem H).root α, (rootSystem H).root β])
    {a b : ℕ} (hab : 0 < a + b) :
    a • (rootSystem H).root α + b • (rootSystem H).root β ≠ 0 := by
  intro h0
  rw [← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K] at h0
  obtain ⟨ha, hb⟩ := hlin.eq_zero_of_pair h0
  have ha0 : a = 0 := Nat.cast_eq_zero.mp ha
  have hb0 : b = 0 := Nat.cast_eq_zero.mp hb
  omega

private theorem commute_ι_of_add_not_mem_range
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {ξ η : H.root}
    (hne0 : (rootSystem H).root ξ + (rootSystem H).root η ≠ 0)
    (hnot : (rootSystem H).root ξ + (rootSystem H).root η ∉ Set.range (rootSystem H).root) :
    Commute
      (_root_.UniversalEnvelopingAlgebra.ι K (x (ξ : Weight K H L)))
      (_root_.UniversalEnvelopingAlgebra.ι K (x (η : Weight K H L))) := by
  let _ : LieRing (_root_.UniversalEnvelopingAlgebra K L) := LieRing.ofAssociativeRing
  let _ : LieAlgebra K (_root_.UniversalEnvelopingAlgebra K L) := LieAlgebra.ofAssociativeAlgebra
  have hbot : rootSpace H (((ξ : Weight K H L) : H → K) + (η : Weight K H L)) = ⊥ := by
    by_contra h_ne_bot
    let w : Weight K H L := ⟨((ξ : Weight K H L) : H → K) + (η : Weight K H L), h_ne_bot⟩
    have hw_nz : w.IsNonZero := by
      intro hw0
      apply hne0
      ext h
      have hpt : (w : H → K) h = 0 := congrFun hw0 h
      simpa [w, rootSystem_root_apply, Weight.toLinear_apply] using hpt
    let rw_idx : H.root := ⟨w, by simpa using hw_nz⟩
    apply hnot
    refine ⟨rw_idx, ?_⟩
    ext h
    simp [rw_idx, w, rootSystem_root_apply, Weight.toLinear_apply]
  have hlie := hx.toIsSl2System.lie_eq_zero_of_rootSpace_add_eq_bot ξ η hbot
  have hmap := (_root_.UniversalEnvelopingAlgebra.ι K).map_lie
    (x (ξ : Weight K H L)) (x (η : Weight K H L))
  rw [hlie, map_zero, LieRing.of_associative_ring_bracket] at hmap
  exact sub_eq_zero.mp hmap.symm

private theorem coe_eq_add_of_root_eq_add {ξ η τ : H.root}
    (hτ : (rootSystem H).root τ = (rootSystem H).root ξ + (rootSystem H).root η) :
    ((τ : Weight K H L) : H → K) = ((ξ : Weight K H L) : H → K) + (η : Weight K H L) := by
  ext h
  simpa [rootSystem_root_apply, Weight.toLinear_apply] using DFunLike.congr_fun hτ h

private theorem mul_eq_mul_add_intStructureConstant
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {ξ η τ : H.root}
    (hτ : (rootSystem H).root τ = (rootSystem H).root ξ + (rootSystem H).root η) :
    _root_.UniversalEnvelopingAlgebra.ι K (x (ξ : Weight K H L)) *
        _root_.UniversalEnvelopingAlgebra.ι K (x (η : Weight K H L)) =
      _root_.UniversalEnvelopingAlgebra.ι K (x (η : Weight K H L)) *
          _root_.UniversalEnvelopingAlgebra.ι K (x (ξ : Weight K H L)) +
        hx.intStructureConstant ξ η τ (H.isNonZero_coe_root τ)
          (coe_eq_add_of_root_eq_add hτ) •
          _root_.UniversalEnvelopingAlgebra.ι K (x (τ : Weight K H L)) := by
  let _ : LieRing (_root_.UniversalEnvelopingAlgebra K L) := LieRing.ofAssociativeRing
  let _ : LieAlgebra K (_root_.UniversalEnvelopingAlgebra K L) := LieAlgebra.ofAssociativeAlgebra
  have hlie := hx.lie_eq_intStructureConstant_zsmul ξ η τ (H.isNonZero_coe_root τ)
    (coe_eq_add_of_root_eq_add hτ)
  have hmap := (_root_.UniversalEnvelopingAlgebra.ι K).map_lie
    (x (ξ : Weight K H L)) (x (η : Weight K H L))
  rw [hlie, map_zsmul, LieRing.of_associative_ring_bracket] at hmap
  rw [add_comm]
  exact eq_add_of_sub_eq hmap.symm

private theorem exists_sign_mul_of_chainBotCoeff
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {ξ η τ : H.root}
    (hτ : (rootSystem H).root τ = (rootSystem H).root ξ + (rootSystem H).root η)
    {p : ℕ} (hp : (rootSystem H).chainBotCoeff ξ η = p) :
    ∃ s : ℤ,
      _root_.UniversalEnvelopingAlgebra.ι K (x (ξ : Weight K H L)) *
          _root_.UniversalEnvelopingAlgebra.ι K (x (η : Weight K H L)) =
        _root_.UniversalEnvelopingAlgebra.ι K (x (η : Weight K H L)) *
            _root_.UniversalEnvelopingAlgebra.ι K (x (ξ : Weight K H L)) +
          (p + 1) • (s • _root_.UniversalEnvelopingAlgebra.ι K (x (τ : Weight K H L))) := by
  have hlin : LinearIndependent K ![(rootSystem H).root ξ, (rootSystem H).root η] :=
    (rootSystem H).linearIndependent_of_add_mem_range_root' ⟨τ, hτ⟩
  have hab : LinearIndependent K
      ![((ξ : Weight K H L) : Module.Dual K H), ((η : Weight K H L) : Module.Dual K H)] := by
    simpa only [rootSystem_root_apply] using hlin
  have hp_lie : LieModule.chainBotCoeff (ξ : Weight K H L) (η : Weight K H L) = p := by
    have hce := (TauCeti.rootSystem_chainCoeffs_eq hab).2
    have hξ : (⟨(ξ : Weight K H L), _⟩ : H.root) = ξ := Subtype.ext rfl
    have hη : (⟨(η : Weight K H L), _⟩ : H.root) = η := Subtype.ext rfl
    rw [hξ, hη] at hce
    exact hce.symm.trans hp
  have hmul := mul_eq_mul_add_intStructureConstant hx hτ
  rcases hx.intStructureConstant_eq_natCast_or_eq_neg_natCast
      ξ η τ (H.isNonZero_coe_root ξ) (H.isNonZero_coe_root η) (H.isNonZero_coe_root τ)
      (coe_eq_add_of_root_eq_add hτ) with hpos | hneg
  · refine ⟨1, ?_⟩
    rw [hmul, hpos, hp_lie, one_zsmul, Nat.cast_smul_eq_nsmul]
  · refine ⟨-1, ?_⟩
    rw [hmul, hneg, hp_lie, neg_one_zsmul, smul_neg, neg_zsmul, Nat.cast_smul_eq_nsmul]

private theorem exists_chain21_commutators
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {α β γ δ : H.root}
    (hγ : (rootSystem H).root γ = (rootSystem H).root α + (rootSystem H).root β)
    (hδ : (rootSystem H).root δ = (2 : ℕ) • (rootSystem H).root α + (rootSystem H).root β) :
    ∃ c d : ℤ,
      _root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L)) *
          _root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L)) =
        _root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L)) *
            _root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L)) +
          c • _root_.UniversalEnvelopingAlgebra.ι K (x (γ : Weight K H L)) ∧
      _root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L)) *
          (_root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L)) *
              _root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L)) -
            _root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L)) *
              _root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L))) =
        (_root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L)) *
            _root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L)) -
          _root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L)) *
            _root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L))) *
          _root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L)) +
        (2 * d) • _root_.UniversalEnvelopingAlgebra.ι K (x (δ : Weight K H L)) := by
  let _ : LieRing (_root_.UniversalEnvelopingAlgebra K L) := LieRing.ofAssociativeRing
  let _ : LieAlgebra K (_root_.UniversalEnvelopingAlgebra K L) := LieAlgebra.ofAssociativeAlgebra
  have hγ_coe := coe_eq_add_of_root_eq_add hγ
  have hδ_add : (rootSystem H).root δ = (rootSystem H).root α + (rootSystem H).root γ := by
    rw [hδ, hγ]; abel
  have hδ_coe_add := coe_eq_add_of_root_eq_add hδ_add
  have hab : ((α : Weight K H L) : H → K) + (β : Weight K H L) ≠ 0 := by
    rw [← hγ_coe]
    exact H.isNonZero_coe_root γ
  have hγ_str : ((γ : Weight K H L) : H → K) =
      ((β : Weight K H L) : H → K) + ((1 : ℕ) : K) • ((α : Weight K H L) : H → K) := by
    rw [hγ_coe, Nat.cast_one, one_smul, add_comm]
  have hδ_str : ((δ : Weight K H L) : H → K) =
      ((β : Weight K H L) : H → K) + ((1 + 1 : ℕ) : K) • ((α : Weight K H L) : H → K) := by
    rw [hδ_coe_add, hγ_coe]
    ext h
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  let c : ℤ := hx.intStructureConstant α β γ (H.isNonZero_coe_root γ) hγ_coe
  let c₂ : ℤ := hx.intStructureConstant α γ δ (H.isNonZero_coe_root δ) hδ_coe_add
  let d : ℤ := hx.intDividedStructureConstant α β
    (H.isNonZero_coe_root α) (H.isNonZero_coe_root β) hab δ 2 hδ_str
  have hrec := hx.succ_mul_intDividedStructureConstant α β
    (H.isNonZero_coe_root α) (H.isNonZero_coe_root β) hab γ δ 1 hγ_str hδ_str
  have hone := hx.intDividedStructureConstant_one α β
    (H.isNonZero_coe_root α) (H.isNonZero_coe_root β) hab γ hγ_coe
  have h2d : (2 : ℤ) * d = c * c₂ := by
    have hrec' : ((1 + 1 : ℕ) : ℤ) * d =
        hx.intDividedStructureConstant α β
          (H.isNonZero_coe_root α) (H.isNonZero_coe_root β) hab γ 1 hγ_str * c₂ := hrec
    rw [hone] at hrec'
    simpa using hrec'
  refine ⟨c, d, mul_eq_mul_add_intStructureConstant hx hγ, ?_⟩
  let φ := _root_.UniversalEnvelopingAlgebra.ι K (L := L)
  have hlie1 : ⁅x (α : Weight K H L), x (β : Weight K H L)⁆ = c • x (γ : Weight K H L) :=
    hx.lie_eq_intStructureConstant_zsmul α β γ (H.isNonZero_coe_root γ) hγ_coe
  have hlie2 : ⁅x (α : Weight K H L), x (γ : Weight K H L)⁆ = c₂ • x (δ : Weight K H L) :=
    hx.lie_eq_intStructureConstant_zsmul α γ δ (H.isNonZero_coe_root δ) hδ_coe_add
  have hlie_iter :
      ⁅x (α : Weight K H L), ⁅x (α : Weight K H L), x (β : Weight K H L)⁆⁆ =
        (2 * d) • x (δ : Weight K H L) := by
    rw [hlie1, lie_zsmul, hlie2, smul_smul, ← h2d]
  have hmap1 := φ.map_lie (x (α : Weight K H L)) (x (β : Weight K H L))
  rw [LieRing.of_associative_ring_bracket] at hmap1
  have hmap2 := φ.map_lie (x (α : Weight K H L)) ⁅x (α : Weight K H L), x (β : Weight K H L)⁆
  rw [hlie_iter, map_zsmul, LieRing.of_associative_ring_bracket, hmap1] at hmap2
  rw [add_comm]
  exact eq_add_of_sub_eq hmap2.symm

private theorem psi_sub_comm_mem_lowDegSpan_of_orientedCone
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {Ψ : Set H.root} (hclosed : IsClosedRootSubset H Ψ)
    {α β : ↥Ψ}
    (hlin : LinearIndependent K ![(rootSystem H).root α.1, (rootSystem H).root β.1])
    (hcone : Humphreys26_4.GapCRootPlane.OrientedCone (rootSystem H) α.1 β.1) (m n : ℕ) :
    dividedPower m (_root_.UniversalEnvelopingAlgebra.ι K (x ((α : H.root) : Weight K H L))) *
        dividedPower n (_root_.UniversalEnvelopingAlgebra.ι K (x ((β : H.root) : Weight K H L))) -
      dividedPower n (_root_.UniversalEnvelopingAlgebra.ι K (x ((β : H.root) : Weight K H L))) *
        dividedPower m (_root_.UniversalEnvelopingAlgebra.ι K (x ((α : H.root) : Weight K H L))) ∈
      psiLowDegSpan Ψ x (m + n) := by
  classical
  let P := rootSystem H
  let E (r : H.root) : _root_.UniversalEnvelopingAlgebra K L :=
    _root_.UniversalEnvelopingAlgebra.ι K (x (r : Weight K H L))
  have comm_of {ξ η : H.root} {a b : ℕ} (hab : 0 < a + b)
      (hsum_eq : P.root ξ + P.root η = a • P.root α.1 + b • P.root β.1)
      (hnot : a • P.root α.1 + b • P.root β.1 ∉ Set.range P.root) :
      Commute (E ξ) (E η) := by
    apply commute_ι_of_add_not_mem_range hx
    · rw [hsum_eq]; exact comb_ne_zero_of_lin hlin hab
    · rwa [hsum_eq]
  rcases hcone with
    (_ | ⟨γ, hγ, h21, h12⟩ | ⟨γ, δ, hγ, hδ, h31, h22, h12⟩ |
     ⟨γ, δ, ε, hγ, hδ, hε, hp1, hp2, hp3, h31, h22, h13, h32, h23, h33⟩ |
     ⟨γ, δ, ε, ζ, hγ, hδ, hε, hζ, hp1, hp2, hp3, hp4,
      h41, h42, h12, h52, h43, h53, h63⟩)
  · -- Case 1: Empty (`α + β ∉ Φ`)
    rename_i hempty
    have hcomm : Commute (E α.1) (E β.1) :=
      comm_of (a := 1) (b := 1) (by decide) (by simp) (by simpa only [one_smul] using hempty)
    have hdp := (commute_dividedPower_dividedPower hcomm m n).eq
    change dividedPower m (E α.1) * dividedPower n (E β.1) -
      dividedPower n (E β.1) * dividedPower m (E α.1) ∈ psiLowDegSpan Ψ x (m + n)
    rw [hdp, sub_self]
    exact (psiLowDegSpan Ψ x (m + n)).zero_mem
  · -- Case 2: Class-two (`{(1, 1)}`)
    have hγΨ : γ ∈ Ψ := hclosed α.2 β.2 hγ
    let c : ℤ := hx.intStructureConstant α.1 β.1 γ (H.isNonZero_coe_root γ)
      (coe_eq_add_of_root_eq_add hγ)
    have hxy : E α.1 * E β.1 = E β.1 * E α.1 + c • E γ :=
      mul_eq_mul_add_intStructureConstant hx hγ
    have hxz : Commute (E α.1) (c • E γ) :=
      (comm_of (a := 2) (b := 1) (by decide) (by rw [hγ]; abel)
        (by simpa only [one_smul] using h21)).smul_right c
    have hyz : Commute (E β.1) (c • E γ) :=
      (comm_of (a := 1) (b := 2) (by decide) (by rw [hγ]; abel)
        (by simpa only [one_smul] using h12)).smul_right c
    have hstr := dividedPower_mul_dividedPower_of_commutator_eq hxy hxz hyz m n
    have h0mem : (0 : ℕ) ∈ Finset.range (min m n + 1) := Finset.mem_range.mpr (by omega)
    rw [← Finset.add_sum_erase _ _ h0mem] at hstr
    have h0term :
        dividedPower (n - 0) (E β.1) * dividedPower 0 (c • E γ) * dividedPower (m - 0) (E α.1) =
          dividedPower n (E β.1) * dividedPower m (E α.1) := by
      simp
    rw [h0term] at hstr
    change dividedPower m (E α.1) * dividedPower n (E β.1) -
      dividedPower n (E β.1) * dividedPower m (E α.1) ∈ psiLowDegSpan Ψ x (m + n)
    rw [hstr, add_sub_cancel_left]
    refine (psiLowDegSpan Ψ x (m + n)).sum_mem fun k hk => ?_
    obtain ⟨hk_ne, hk_range⟩ := Finset.mem_erase.mp hk
    have hk_le : k ≤ min m n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_range)
    rw [dividedPower_zsmul, mul_smul_comm, smul_mul_assoc]
    have hw_eq :
        dividedPower (n - k) (E β.1) * dividedPower k (E γ) * dividedPower (m - k) (E α.1) =
          psiWordProd x [(β, n - k), (⟨γ, hγΨ⟩, k), (α, m - k)] := by
      simp [psiWordProd, E, mul_assoc]
    rw [hw_eq]
    exact (psiLowDegSpan Ψ x (m + n)).smul_mem (c ^ k)
      (psiWordProd_mem_psiLowDegSpan (by simp [Humphreys26_4.GapC.rootWordDeg]; omega))
  · -- Case 3: Length-2 chain (`{(1, 1), (2, 1)}`)
    have hγΨ : γ ∈ Ψ := hclosed α.2 β.2 hγ
    have hδΨ : δ ∈ Ψ := hclosed α.2 hγΨ (by rw [hδ, hγ]; abel)
    obtain ⟨c, d, hxy, hxxy⟩ := exists_chain21_commutators hx hγ hδ
    have hxw : Commute (E α.1) (E δ) :=
      comm_of (a := 3) (b := 1) (by decide) (by rw [hδ]; abel)
        (by simpa only [one_smul] using h31)
    have hyz : Commute (E β.1) (E γ) :=
      comm_of (a := 1) (b := 2) (by decide) (by rw [hγ]; abel)
        (by simpa only [one_smul] using h12)
    have hstr := dividedPower_mul_dividedPower_of_commutator_eq_of_iterated_commutator_eq
      hxy hxxy hxw hyz m n
    have h0mem : ((0, 0) : ℕ × ℕ) ∈ chainLeTwoIndex m n := by
      rw [mem_chainLeTwoIndex]; dsimp; omega
    rw [← Finset.add_sum_erase _ _ h0mem] at hstr
    have h0term :
        (c ^ (0 : ℕ) * d ^ (0 : ℕ)) •
          (dividedPower (n - 0 - 0) (E β.1) * dividedPower 0 (E γ) *
            dividedPower 0 (E δ) * dividedPower (m - 0 - 2 * 0) (E α.1)) =
          dividedPower n (E β.1) * dividedPower m (E α.1) := by
      simp
    rw [h0term] at hstr
    change dividedPower m (E α.1) * dividedPower n (E β.1) -
      dividedPower n (E β.1) * dividedPower m (E α.1) ∈ psiLowDegSpan Ψ x (m + n)
    rw [hstr, add_sub_cancel_left]
    refine (psiLowDegSpan Ψ x (m + n)).sum_mem fun p hp => ?_
    obtain ⟨hp_ne, hp_mem⟩ := Finset.mem_erase.mp hp
    rcases p with ⟨p1, p2⟩
    obtain ⟨hpn, hpm⟩ := mem_chainLeTwoIndex.mp hp_mem
    dsimp only at hpn hpm ⊢
    have hp_pos : 0 < p1 + p2 := by
      simp only [ne_eq, Prod.mk.injEq, not_and] at hp_ne
      omega
    have hw_eq :
        dividedPower (n - p1 - p2) (E β.1) * dividedPower p1 (E γ) *
          dividedPower p2 (E δ) * dividedPower (m - p1 - 2 * p2) (E α.1) =
          psiWordProd x
            [(β, n - p1 - p2), (⟨γ, hγΨ⟩, p1), (⟨δ, hδΨ⟩, p2), (α, m - p1 - 2 * p2)] := by
      simp [psiWordProd, E, mul_assoc]
    rw [hw_eq]
    exact (psiLowDegSpan Ψ x (m + n)).smul_mem (c ^ p1 * d ^ p2)
      (psiWordProd_mem_psiLowDegSpan (by simp [Humphreys26_4.GapC.rootWordDeg]; omega))
  · -- Case 4: `G₂` `120°` short pair (`{(1, 1), (2, 1), (1, 2)}`)
    have hγΨ : γ ∈ Ψ := hclosed α.2 β.2 hγ
    have hδΨ : δ ∈ Ψ := hclosed α.2 hγΨ (by rw [hδ, hγ]; abel)
    have hεΨ : ε ∈ Ψ := hclosed hγΨ β.2 (by rw [hε, hγ]; abel)
    obtain ⟨c, hc⟩ := exists_sign_mul_of_chainBotCoeff hx hγ hp1
    obtain ⟨c₁, hc₁⟩ := exists_sign_mul_of_chainBotCoeff hx
      (show P.root δ = P.root α.1 + P.root γ by rw [hδ, hγ]; abel) hp2
    obtain ⟨c₂, hc₂⟩ := exists_sign_mul_of_chainBotCoeff hx
      (show P.root ε = P.root γ + P.root β.1 by rw [hε, hγ]; abel) hp3
    let z' := (2 * c) • E γ
    let w' := (3 * (c * c₁)) • E δ
    let s' := (3 * (c * c₂)) • E ε
    have hxy : E α.1 * E β.1 = E β.1 * E α.1 + z' := by
      change E α.1 * E β.1 = E β.1 * E α.1 + (2 * c) • E γ
      rw [show E α.1 * E β.1 = E β.1 * E α.1 + (1 + 1) • (c • E γ) from hc,
        ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
      rfl
    have hxz : E α.1 * z' = z' * E α.1 + 2 • w' := by
      dsimp only [z', w']
      rw [mul_smul_comm, smul_mul_assoc,
        show E α.1 * E γ = E γ * E α.1 + (2 + 1) • (c₁ • E δ) from hc₁, smul_add]
      simp only [← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
      congr 2; ring
    have hzy : z' * E β.1 = E β.1 * z' + 2 • s' := by
      dsimp only [z', s']
      rw [smul_mul_assoc, mul_smul_comm,
        show E γ * E β.1 = E β.1 * E γ + (2 + 1) • (c₂ • E ε) from hc₂, smul_add]
      simp only [← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
      congr 2; ring
    have hxw : Commute (E α.1) w' :=
      (comm_of (a := 3) (b := 1) (by decide) (by rw [hδ]; abel)
        (by simpa only [one_smul] using h31)).smul_right _
    have hxs : Commute (E α.1) s' :=
      (comm_of (a := 2) (b := 2) (by decide) (by rw [hε]; abel) h22).smul_right _
    have hys : Commute (E β.1) s' :=
      (comm_of (a := 1) (b := 3) (by decide) (by rw [hε]; abel)
        (by simpa only [one_smul] using h13)).smul_right _
    have hzw : Commute z' w' :=
      ((comm_of (a := 3) (b := 2) (by decide) (by rw [hγ, hδ]; abel)
        h32).smul_left _).smul_right _
    have hzs : Commute z' s' :=
      ((comm_of (a := 2) (b := 3) (by decide) (by rw [hγ, hε]; abel)
        h23).smul_left _).smul_right _
    have hws : Commute w' s' :=
      ((comm_of (a := 3) (b := 3) (by decide) (by rw [hδ, hε]; abel)
        h33).smul_left _).smul_right _
    have hstr := dividedPower_mul_dividedPower_of_g2_short_pair_scaled
      hxy hxz hzy hxw hxs hys hzw hzs hws m n
    have h0mem : ((0, (0, 0)) : ℕ × ℕ × ℕ) ∈ g2ShortPairIndex m n := by
      rw [mem_g2ShortPairIndex]; dsimp; omega
    rw [← Finset.add_sum_erase _ _ h0mem] at hstr
    have h0term :
        dividedPower (n - 0 - 0 - 2 * 0) (E β.1) * dividedPower 0 z' *
          dividedPower 0 w' * dividedPower 0 s' *
          dividedPower (m - 0 - 2 * 0 - 0) (E α.1) =
          dividedPower n (E β.1) * dividedPower m (E α.1) := by
      simp
    rw [h0term] at hstr
    change dividedPower m (E α.1) * dividedPower n (E β.1) -
      dividedPower n (E β.1) * dividedPower m (E α.1) ∈ psiLowDegSpan Ψ x (m + n)
    rw [hstr, add_sub_cancel_left]
    refine (psiLowDegSpan Ψ x (m + n)).sum_mem fun p hp => ?_
    obtain ⟨hp_ne, hp_mem⟩ := Finset.mem_erase.mp hp
    rcases p with ⟨p1, p2, p3⟩
    obtain ⟨hpn, hpm⟩ := mem_g2ShortPairIndex.mp hp_mem
    dsimp only at hpn hpm ⊢
    have hp_pos : 0 < p1 + p2 + p3 := by
      simp only [ne_eq, Prod.mk.injEq, not_and] at hp_ne
      omega
    dsimp only [z', w', s']
    simp only [dividedPower_zsmul, mul_smul_comm, smul_mul_assoc, smul_smul]
    have hw_eq :
        dividedPower (n - p1 - p2 - 2 * p3) (E β.1) *
          (dividedPower p1 (E γ) *
            (dividedPower p2 (E δ) *
              (dividedPower p3 (E ε) *
                dividedPower (m - p1 - 2 * p2 - p3) (E α.1)))) =
          psiWordProd x
            [(β, n - p1 - p2 - 2 * p3), (⟨γ, hγΨ⟩, p1), (⟨δ, hδΨ⟩, p2),
             (⟨ε, hεΨ⟩, p3), (α, m - p1 - 2 * p2 - p3)] := by
      simp [psiWordProd, E]
    simp only [mul_assoc]
    rw [hw_eq]
    exact (psiLowDegSpan Ψ x (m + n)).smul_mem _
      (psiWordProd_mem_psiLowDegSpan (by simp [Humphreys26_4.GapC.rootWordDeg]; omega))
  · -- Case 5: `G₂` `150°` simple pair (`{(1, 1), (2, 1), (3, 1), (3, 2)}`)
    have hγΨ : γ ∈ Ψ := hclosed α.2 β.2 hγ
    have hδΨ : δ ∈ Ψ := hclosed α.2 hγΨ (by rw [hδ, hγ]; abel)
    have hεΨ : ε ∈ Ψ := hclosed α.2 hδΨ (by rw [hε, hδ]; abel)
    have hζΨ : ζ ∈ Ψ := hclosed hδΨ hγΨ (by rw [hζ, hδ, hγ]; abel)
    obtain ⟨a, ha⟩ := exists_sign_mul_of_chainBotCoeff hx hγ hp1
    obtain ⟨b, hb⟩ := exists_sign_mul_of_chainBotCoeff hx
      (show P.root δ = P.root α.1 + P.root γ by rw [hδ, hγ]; abel) hp2
    obtain ⟨c, hc⟩ := exists_sign_mul_of_chainBotCoeff hx
      (show P.root ε = P.root α.1 + P.root δ by rw [hε, hδ]; abel) hp3
    obtain ⟨d, hd⟩ := exists_sign_mul_of_chainBotCoeff hx
      (show P.root ζ = P.root δ + P.root γ by rw [hζ, hδ, hγ]; abel) hp4
    have hxy : E α.1 * E β.1 = E β.1 * E α.1 + a • E γ := by
      rw [show E α.1 * E β.1 = E β.1 * E α.1 + (0 + 1) • (a • E γ) from ha, zero_add, one_smul]
    have hxz : E α.1 * E γ = E γ * E α.1 + 2 • (b • E δ) := hb
    have hxw : E α.1 * E δ = E δ * E α.1 + 3 • (c • E ε) := hc
    have hwz : E δ * E γ = E γ * E δ + 3 • (d • E ζ) := hd
    have hxv : Commute (E α.1) (E ε) :=
      comm_of (a := 4) (b := 1) (by decide) (by rw [hε]; abel)
        (by simpa only [one_smul] using h41)
    have hxs : Commute (E α.1) (E ζ) :=
      comm_of (a := 4) (b := 2) (by decide) (by rw [hζ]; abel) h42
    have hyz : Commute (E β.1) (E γ) :=
      comm_of (a := 1) (b := 2) (by decide) (by rw [hγ]; abel)
        (by simpa only [one_smul] using h12)
    have hwv : Commute (E δ) (E ε) :=
      comm_of (a := 5) (b := 2) (by decide) (by rw [hδ, hε]; abel) h52
    have hzs : Commute (E γ) (E ζ) :=
      comm_of (a := 4) (b := 3) (by decide) (by rw [hγ, hζ]; abel) h43
    have hws : Commute (E δ) (E ζ) :=
      comm_of (a := 5) (b := 3) (by decide) (by rw [hδ, hζ]; abel) h53
    have hvs : Commute (E ε) (E ζ) :=
      comm_of (a := 6) (b := 3) (by decide) (by rw [hε, hζ]; abel) h63
    have hstr := dividedPower_mul_dividedPower_of_g2_zsmul
      a b c d hxy hxz hxw hwz hxv hxs hyz hwv hzs hws hvs m n
    have h0mem : ((0, (0, (0, 0))) : ℕ × ℕ × ℕ × ℕ) ∈ chainG2Index m n := by
      rw [mem_chainG2Index]; dsimp; omega
    rw [← Finset.add_sum_erase _ _ h0mem] at hstr
    have h0term :
        (a ^ (0 : ℕ) * (a * b) ^ (0 : ℕ) * (a * b * c) ^ (0 : ℕ) *
          (a ^ 2 * b * d) ^ (0 : ℕ)) •
        (dividedPower (n - 0 - 0 - 0 - 2 * 0) (E β.1) * dividedPower 0 (E γ) *
          dividedPower 0 (E δ) * dividedPower 0 (E ε) * dividedPower 0 (E ζ) *
          dividedPower (m - 0 - 2 * 0 - 3 * 0 - 3 * 0) (E α.1)) =
          dividedPower n (E β.1) * dividedPower m (E α.1) := by
      simp
    rw [h0term] at hstr
    change dividedPower m (E α.1) * dividedPower n (E β.1) -
      dividedPower n (E β.1) * dividedPower m (E α.1) ∈ psiLowDegSpan Ψ x (m + n)
    rw [hstr, add_sub_cancel_left]
    refine (psiLowDegSpan Ψ x (m + n)).sum_mem fun p hp => ?_
    obtain ⟨hp_ne, hp_mem⟩ := Finset.mem_erase.mp hp
    rcases p with ⟨p1, p2, p3, p4⟩
    obtain ⟨hpn, hpm⟩ := mem_chainG2Index.mp hp_mem
    dsimp only at hpn hpm ⊢
    have hp_pos : 0 < p1 + p2 + p3 + p4 := by
      simp only [ne_eq, Prod.mk.injEq, not_and] at hp_ne
      omega
    have hw_eq :
        dividedPower (n - p1 - p2 - p3 - 2 * p4) (E β.1) *
          dividedPower p1 (E γ) * dividedPower p2 (E δ) *
          dividedPower p3 (E ε) * dividedPower p4 (E ζ) *
          dividedPower (m - p1 - 2 * p2 - 3 * p3 - 3 * p4) (E α.1) =
          psiWordProd x
            [(β, n - p1 - p2 - p3 - 2 * p4), (⟨γ, hγΨ⟩, p1), (⟨δ, hδΨ⟩, p2),
             (⟨ε, hεΨ⟩, p3), (⟨ζ, hζΨ⟩, p4),
             (α, m - p1 - 2 * p2 - 3 * p3 - 3 * p4)] := by
      simp [psiWordProd, E, mul_assoc]
    rw [hw_eq]
    exact (psiLowDegSpan Ψ x (m + n)).smul_mem _
      (psiWordProd_mem_psiLowDegSpan (by simp [Humphreys26_4.GapC.rootWordDeg]; omega))

private theorem psi_sub_comm_mem_lowDegSpan
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {Ψ : Set H.root} (hclosed : IsClosedRootSubset H Ψ) (hasym : IsAsymmetricRootSubset H Ψ)
    {α β : ↥Ψ} (hne : α ≠ β) (m n : ℕ) :
    dividedPower m (_root_.UniversalEnvelopingAlgebra.ι K (x ((α : H.root) : Weight K H L))) *
        dividedPower n (_root_.UniversalEnvelopingAlgebra.ι K (x ((β : H.root) : Weight K H L))) -
      dividedPower n (_root_.UniversalEnvelopingAlgebra.ι K (x ((β : H.root) : Weight K H L))) *
        dividedPower m (_root_.UniversalEnvelopingAlgebra.ι K (x ((α : H.root) : Weight K H L))) ∈
      psiLowDegSpan Ψ x (m + n) := by
  have hne' : (α : H.root) ≠ (β : H.root) := fun h => hne (Subtype.ext h)
  have hneg : (rootSystem H).root α.1 ≠ -(rootSystem H).root β.1 := hasym α.2 β.2
  have hlin : LinearIndependent K ![(rootSystem H).root α.1, (rootSystem H).root β.1] :=
    (IsReduced.linearIndependent_iff (rootSystem H)).mpr ⟨hne', hneg⟩
  rcases Humphreys26_4.GapCRootPlane.orientedCone_or_symm (rootSystem H) hlin with
    hcone | hcone_symm
  · exact psi_sub_comm_mem_lowDegSpan_of_orientedCone hx hclosed hlin hcone m n
  · have hlin' : LinearIndependent K ![(rootSystem H).root β.1, (rootSystem H).root α.1] :=
      LinearIndependent.pair_symm_iff.mpr hlin
    have hsym := psi_sub_comm_mem_lowDegSpan_of_orientedCone hx hclosed hlin' hcone_symm n m
    rw [Nat.add_comm] at hsym
    simpa only [neg_sub] using (psiLowDegSpan Ψ x (m + n)).neg_mem hsym

private theorem psiWordProd_mem_span
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {s : ℕ} {Ψ : Set H.root}
    (hclosed : IsClosedRootSubset H Ψ) (hasym : IsAsymmetricRootSubset H Ψ)
    (ψOrd : Fin s ≃ ↥Ψ) (w : List (↥Ψ × ℕ)) :
    psiWordProd x w ∈ Submodule.span ℤ (Set.range (closedSubsetMonomial ψOrd x)) := by
  let M := Submodule.span ℤ (Set.range (closedSubsetMonomial ψOrd x))
  let pos : ↥Ψ → ℕ := fun α => (ψOrd.symm α : ℕ)
  have hpos_inj : Function.Injective pos := fun α β h =>
    ψOrd.symm.injective (Fin.ext h)
  suffices hmain : ∀ d : ℕ, ∀ k : ℕ, ∀ w : List (↥Ψ × ℕ),
      Humphreys26_4.GapC.rootWordDeg w = d → wordMeasure pos w = k → psiWordProd x w ∈ M from
    hmain _ _ w rfl rfl
  intro d
  induction d using Nat.strongRecOn with
  | ind d ihd =>
    intro k
    induction k using Nat.strongRecOn with
    | ind k ihk =>
      intro w hd hk
      by_cases hpw : w.Pairwise (fun p q => pos p.1 < pos q.1)
      · let w' : List (Fin s × ℕ) := w.map fun p => (ψOrd.symm p.1, p.2)
        have hpw' : w'.Pairwise (fun p q => p.1 < q.1) := by
          rw [List.pairwise_map]
          exact hpw
        let g : Fin s → ℕ → _root_.UniversalEnvelopingAlgebra K L := fun i n =>
          dividedPower n (_root_.UniversalEnvelopingAlgebra.ι K
            (x (((ψOrd i : ↥Ψ) : H.root) : Weight K H L)))
        have hprod_eq : psiWordProd x w = closedSubsetMonomial ψOrd x (lookupExp w') := by
          have h1 : psiWordProd x w = (w'.map fun p => g p.1 p.2).prod := by
            simp only [psiWordProd, w', List.map_map, g, Function.comp_def,
              Equiv.apply_symm_apply]
          rw [h1, prod_map_eq_prod_ofFn_of_pairwise g (fun i => dividedPower_zero _) w' hpw']
          rfl
        rw [hprod_eq]
        exact Submodule.subset_span ⟨lookupExp w', rfl⟩
      · obtain ⟨w₁, p, q, w₂, rfl, hle⟩ := exists_adj_ge_of_not_pairwise pos w hpw
        rcases lt_or_eq_of_le hle with hlt | heq
        · have hne : p.1 ≠ q.1 := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
          have hcomm := psi_sub_comm_mem_lowDegSpan hx hclosed hasym hne p.2 q.2
          have hswap_deg :
              Humphreys26_4.GapC.rootWordDeg (w₁ ++ q :: p :: w₂) = d := by
            rw [← hd]
            simp only [Humphreys26_4.GapC.rootWordDeg, List.map_append, List.map_cons,
              List.sum_append, List.sum_cons]
            omega
          have hswap_meas : wordMeasure pos (w₁ ++ q :: p :: w₂) < k := by
            rw [← hk]
            exact wordMeasure_swap_lt pos hlt w₁ w₂
          have hswap_mem : psiWordProd x (w₁ ++ q :: p :: w₂) ∈ M :=
            ihk _ hswap_meas _ hswap_deg rfl
          have hdiff_mem :
              psiWordProd x w₁ *
                (dividedPower p.2
                    (_root_.UniversalEnvelopingAlgebra.ι K (x ((p.1 : H.root) : Weight K H L))) *
                  dividedPower q.2
                    (_root_.UniversalEnvelopingAlgebra.ι K (x ((q.1 : H.root) : Weight K H L))) -
                dividedPower q.2
                    (_root_.UniversalEnvelopingAlgebra.ι K (x ((q.1 : H.root) : Weight K H L))) *
                  dividedPower p.2
                    (_root_.UniversalEnvelopingAlgebra.ι K (x ((p.1 : H.root) : Weight K H L)))) *
                psiWordProd x w₂ ∈ M := by
            refine Submodule.span_induction ?_ ?_ ?_ ?_ hcomm
            · rintro _ ⟨wm, hwm_deg, rfl⟩
              have hcat_eq :
                  psiWordProd x w₁ * psiWordProd x wm * psiWordProd x w₂ =
                    psiWordProd x (w₁ ++ wm ++ w₂) := by
                rw [psiWordProd_append, psiWordProd_append]
              rw [hcat_eq]
              have hcat_deg : Humphreys26_4.GapC.rootWordDeg (w₁ ++ wm ++ w₂) < d := by
                rw [← hd]
                simp only [Humphreys26_4.GapC.rootWordDeg, List.map_append, List.map_cons,
                  List.sum_append, List.sum_cons] at hwm_deg ⊢
                omega
              exact ihd _ hcat_deg _ _ rfl rfl
            · simp [M.zero_mem]
            · intro u₁ u₂ _ _ hu₁ hu₂
              have hadd : psiWordProd x w₁ * (u₁ + u₂) * psiWordProd x w₂ =
                  psiWordProd x w₁ * u₁ * psiWordProd x w₂ +
                  psiWordProd x w₁ * u₂ * psiWordProd x w₂ := by
                rw [mul_add, add_mul]
              rw [hadd]
              exact M.add_mem hu₁ hu₂
            · intro z u _ hu
              have hsmul : psiWordProd x w₁ * (z • u) * psiWordProd x w₂ =
                  z • (psiWordProd x w₁ * u * psiWordProd x w₂) := by
                rw [mul_smul_comm, smul_mul_assoc]
              rw [hsmul]
              exact M.smul_mem z hu
          have hdecomp :
              psiWordProd x (w₁ ++ p :: q :: w₂) =
                psiWordProd x (w₁ ++ q :: p :: w₂) +
                  psiWordProd x w₁ *
                    (dividedPower p.2
                        (_root_.UniversalEnvelopingAlgebra.ι K (x ((p.1 : H.root) : Weight K H L))) *
                      dividedPower q.2
                        (_root_.UniversalEnvelopingAlgebra.ι K (x ((q.1 : H.root) : Weight K H L))) -
                    dividedPower q.2
                        (_root_.UniversalEnvelopingAlgebra.ι K (x ((q.1 : H.root) : Weight K H L))) *
                      dividedPower p.2
                        (_root_.UniversalEnvelopingAlgebra.ι K (x ((p.1 : H.root) : Weight K H L)))) *
                    psiWordProd x w₂ := by
            rw [psiWordProd_append, psiWordProd_append]
            simp only [psiWordProd, List.map_cons, List.prod_cons, mul_sub, sub_mul, mul_assoc]
            abel
          rw [hdecomp]
          exact M.add_mem hswap_mem hdiff_mem
        · have hqp : q.1 = p.1 := hpos_inj heq
          let r : ↥Ψ × ℕ := (p.1, p.2 + q.2)
          have hmerge_deg : Humphreys26_4.GapC.rootWordDeg (w₁ ++ r :: w₂) = d := by
            rw [← hd]
            simp only [Humphreys26_4.GapC.rootWordDeg, r, List.map_append, List.map_cons,
              List.sum_append, List.sum_cons]
            omega
          have hmerge_meas : wordMeasure pos (w₁ ++ r :: w₂) < k := by
            rw [← hk]
            exact wordMeasure_merge_lt pos (r := r) heq rfl w₁ w₂
          have hmerge_mem : psiWordProd x (w₁ ++ r :: w₂) ∈ M :=
            ihk _ hmerge_meas _ hmerge_deg rfl
          have hmerge_eq :
              psiWordProd x (w₁ ++ p :: q :: w₂) =
                (Nat.choose (p.2 + q.2) p.2 : ℤ) • psiWordProd x (w₁ ++ r :: w₂) := by
            rw [psiWordProd_append, psiWordProd_append]
            simp only [psiWordProd, List.map_cons, List.prod_cons, r, hqp]
            rw [← mul_assoc (dividedPower p.2 _), mul_dividedPower,
              ← Nat.cast_smul_eq_nsmul ℤ, smul_mul_assoc, mul_smul_comm]
          rw [hmerge_eq]
          exact M.smul_mem _ hmerge_mem

/-- **Humphreys §26.3, Lemma B (p. 154, verbatim spanning & unique `ℤ`-expansion):**
Let `Ψ ⊆ Φ` be a closed set of roots (`IsClosedRootSubset H Ψ`) with `Ψ ∩ -Ψ = ∅`
(`IsAsymmetricRootSubset H Ψ`), and let `ψOrd : Fin s ≃ ↥Ψ` be any fixed ordering of `Ψ`.
Then the subring `𝔛 = closedSubsetSubring H Ψ x` coincides as a set with the `ℤ`-span of
`closedSubsetMonomial ψOrd x`, and every `u ∈ 𝔘(L)` lies in `𝔛` if and only if it has a
unique `ℤ`-linear expansion in `closedSubsetMonomial ψOrd x`. -/
theorem closedSubsetSubring_eq_span_and_existsUnique
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {s : ℕ} {Ψ : Set H.root}
    (hclosed : IsClosedRootSubset H Ψ) (hasym : IsAsymmetricRootSubset H Ψ)
    (ψOrd : Fin s ≃ ↥Ψ) :
    (Submodule.span ℤ (Set.range (closedSubsetMonomial ψOrd x)) :
        Set (_root_.UniversalEnvelopingAlgebra K L)) =
      (closedSubsetSubring H Ψ x :
        Set (_root_.UniversalEnvelopingAlgebra K L)) ∧
    ∀ u : _root_.UniversalEnvelopingAlgebra K L,
      u ∈ closedSubsetSubring H Ψ x ↔
        ∃! c : (Fin s → ℕ) →₀ ℤ,
          c.sum (fun t a => a • closedSubsetMonomial ψOrd x t) = u := by
  let M := Submodule.span ℤ (Set.range (closedSubsetMonomial ψOrd x))
  have hmono_eq_word : ∀ t : Fin s → ℕ,
      closedSubsetMonomial ψOrd x t = psiWordProd x (List.ofFn fun j : Fin s => (ψOrd j, t j)) := by
    intro t
    simp [closedSubsetMonomial, psiWordProd, List.map_ofFn, Function.comp_def]
  have hset_eq : (M : Set (_root_.UniversalEnvelopingAlgebra K L)) =
      (closedSubsetSubring H Ψ x : Set (_root_.UniversalEnvelopingAlgebra K L)) := by
    apply Set.Subset.antisymm
    · intro u hu
      refine Submodule.span_induction ?_ (closedSubsetSubring H Ψ x).zero_mem
        (fun _ _ _ _ => (closedSubsetSubring H Ψ x).add_mem) (fun z _ _ h => zsmul_mem h z) hu
      rintro _ ⟨t, rfl⟩
      refine Subring.list_prod_mem _ fun y hy => ?_
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
      exact Subring.subset_closure ⟨(ψOrd j, t j), rfl⟩
    · have hmul_mem : ∀ a ∈ M, ∀ b ∈ M, a * b ∈ M := by
        intro a ha
        refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
        · rintro _ ⟨t₁, rfl⟩ b hb
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
          · rintro _ ⟨t₂, rfl⟩
            rw [hmono_eq_word t₁, hmono_eq_word t₂, ← psiWordProd_append]
            exact psiWordProd_mem_span hx hclosed hasym ψOrd _
          · simp [M.zero_mem]
          · intro b₁ b₂ _ _ h₁ h₂
            rw [mul_add]
            exact M.add_mem h₁ h₂
          · intro z b₁ _ h₁
            rw [mul_smul_comm]
            exact M.smul_mem z h₁
        · intro b _; simp [M.zero_mem]
        · intro a₁ a₂ _ _ h₁ h₂ b hb
          rw [add_mul]
          exact M.add_mem (h₁ b hb) (h₂ b hb)
        · intro z a₁ _ h₁ b hb
          rw [smul_mul_assoc]
          exact M.smul_mem z (h₁ b hb)
      have hone_mem : (1 : _root_.UniversalEnvelopingAlgebra K L) ∈ M := by
        simpa [psiWordProd] using psiWordProd_mem_span hx hclosed hasym ψOrd []
      intro u hu
      induction hu using Subring.closure_induction with
      | mem y hy =>
        obtain ⟨⟨α, t⟩, rfl⟩ := hy
        simpa [psiWordProd] using psiWordProd_mem_span hx hclosed hasym ψOrd [(α, t)]
      | zero => exact M.zero_mem
      | one => exact hone_mem
      | add a b _ _ ha hb => exact M.add_mem ha hb
      | neg a _ ha => exact M.neg_mem ha
      | mul a b _ _ ha hb => exact hmul_mem a ha b hb
  have hliZ : LinearIndependent ℤ (closedSubsetMonomial ψOrd x) := by
    have hliK := closedSubsetMonomial_linearIndependent_over_field hx ψOrd
    rw [linearIndependent_iff'] at hliK ⊢
    intro S c hsum t ht
    have hsumK : ∑ q ∈ S, (c q : K) • closedSubsetMonomial ψOrd x q = 0 := by
      simpa only [Int.cast_smul_eq_zsmul] using hsum
    exact Int.cast_eq_zero.mp (hliK S (fun q => (c q : K)) hsumK t ht)
  refine ⟨hset_eq, fun u => ?_⟩
  constructor
  · intro hu
    have huM : u ∈ M := by
      change u ∈ (M : Set (_root_.UniversalEnvelopingAlgebra K L))
      rw [hset_eq]
      exact hu
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp huM
    refine ⟨c, hc, fun c' hc' => ?_⟩
    have hlc : Finsupp.linearCombination ℤ (closedSubsetMonomial ψOrd x) c' =
        Finsupp.linearCombination ℤ (closedSubsetMonomial ψOrd x) c := by
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, hc', hc]
    exact linearIndependent_iff.mp hliZ (c' - c) (by rw [map_sub, hlc, sub_self]) |> sub_eq_zero.mp
  · rintro ⟨c, hc, -⟩
    have huM : u ∈ M := Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨c, hc⟩
    change u ∈ (closedSubsetSubring H Ψ x : Set (_root_.UniversalEnvelopingAlgebra K L))
    rw [← hset_eq]
    exact huM

private theorem exists_closedSubsetSubringBasis
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {s : ℕ} {Ψ : Set H.root}
    (hclosed : IsClosedRootSubset H Ψ) (hasym : IsAsymmetricRootSubset H Ψ)
    (ψOrd : Fin s ≃ ↥Ψ) :
    ∃ B : Module.Basis (Fin s → ℕ) ℤ (closedSubsetSubring H Ψ x),
      ∀ t : Fin s → ℕ,
        ((B t : closedSubsetSubring H Ψ x) :
            _root_.UniversalEnvelopingAlgebra K L) =
          closedSubsetMonomial ψOrd x t := by
  have hmem : ∀ t : Fin s → ℕ,
      closedSubsetMonomial ψOrd x t ∈ closedSubsetSubring H Ψ x := by
    intro t
    refine Subring.list_prod_mem _ fun y hy => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    exact Subring.subset_closure ⟨(ψOrd j, t j), rfl⟩
  let v : (Fin s → ℕ) → closedSubsetSubring H Ψ x :=
    fun t => ⟨closedSubsetMonomial ψOrd x t, hmem t⟩
  have hli : LinearIndependent ℤ v := by
    rw [linearIndependent_iff']
    intro S c hsum t ht
    have hliK := closedSubsetMonomial_linearIndependent_over_field hx ψOrd
    rw [linearIndependent_iff'] at hliK
    have hsumK : ∑ q ∈ S, (c q : K) • closedSubsetMonomial ψOrd x q = 0 := by
      have hval := congrArg (closedSubsetSubring H Ψ x).subtype hsum
      rw [map_sum, map_zero] at hval
      simpa only [map_zsmul, Subring.coe_subtype, Int.cast_smul_eq_zsmul] using hval
    exact Int.cast_eq_zero.mp (hliK S (fun q => (c q : K)) hsumK t ht)
  have hspan : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    intro y _
    have hy : (y : _root_.UniversalEnvelopingAlgebra K L) ∈
        Submodule.span ℤ (Set.range (closedSubsetMonomial ψOrd x)) := by
      change (y : _root_.UniversalEnvelopingAlgebra K L) ∈
        (Submodule.span ℤ (Set.range (closedSubsetMonomial ψOrd x)) :
          Set (_root_.UniversalEnvelopingAlgebra K L))
      rw [(closedSubsetSubring_eq_span_and_existsUnique hx hclosed hasym ψOrd).1]
      exact y.2
    suffices hlift :
        ∃ hy' : (y : _root_.UniversalEnvelopingAlgebra K L) ∈ closedSubsetSubring H Ψ x,
          (⟨(y : _root_.UniversalEnvelopingAlgebra K L), hy'⟩ : closedSubsetSubring H Ψ x) ∈
            Submodule.span ℤ (Set.range v) by
      obtain ⟨_, hlift_mem⟩ := hlift
      exact hlift_mem
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨t, rfl⟩
      exact ⟨hmem t, Submodule.subset_span ⟨t, rfl⟩⟩
    · exact ⟨(closedSubsetSubring H Ψ x).zero_mem, Submodule.zero_mem _⟩
    · rintro a₁ a₂ _ _ ⟨ha₁, h₁⟩ ⟨ha₂, h₂⟩
      exact ⟨(closedSubsetSubring H Ψ x).add_mem ha₁ ha₂, Submodule.add_mem _ h₁ h₂⟩
    · rintro z a₁ _ ⟨ha₁, h₁⟩
      exact ⟨zsmul_mem ha₁ z, Submodule.smul_mem _ z h₁⟩
  refine ⟨Module.Basis.mk hli hspan, fun t => ?_⟩
  rw [Module.Basis.mk_apply]

/-- **Bundled `ℤ`-basis form of Humphreys Lemma 26.3B (p. 154):**
Relative to any fixed ordering `ψOrd : Fin s ≃ ↥Ψ` of a closed root subset `Ψ` with
`Ψ ∩ -Ψ = ∅`, the ordered products `∏_{α ∈ Ψ} x_α^{t_α} / t_α!` form a free `ℤ`-module
basis of `closedSubsetSubring H Ψ x`. -/
noncomputable def closedSubsetSubringBasis
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {s : ℕ} {Ψ : Set H.root}
    (hclosed : IsClosedRootSubset H Ψ) (hasym : IsAsymmetricRootSubset H Ψ)
    (ψOrd : Fin s ≃ ↥Ψ) :
    Module.Basis (Fin s → ℕ) ℤ (closedSubsetSubring H Ψ x) :=
  (exists_closedSubsetSubringBasis hx hclosed hasym ψOrd).choose

@[simp]
theorem coe_closedSubsetSubringBasis_apply
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {s : ℕ} {Ψ : Set H.root}
    (hclosed : IsClosedRootSubset H Ψ) (hasym : IsAsymmetricRootSubset H Ψ)
    (ψOrd : Fin s ≃ ↥Ψ) (t : Fin s → ℕ) :
    ((closedSubsetSubringBasis hx hclosed hasym ψOrd t :
        closedSubsetSubring H Ψ x) :
        _root_.UniversalEnvelopingAlgebra K L) =
      closedSubsetMonomial ψOrd x t :=
  (exists_closedSubsetSubringBasis hx hclosed hasym ψOrd).choose_spec t

/-- **Humphreys §26.3 canonical examples (p. 154):**
(1) For every base `b : (rootSystem H).Base`, `Φ⁺ = {α : H.root | b.IsPos α}` is a closed
asymmetric subset of `Φ` whose `closedSubsetSubring` equals `Humphreys27_1.kostantPosSubring b x`;
(2) For any linearly independent roots `α, β ∈ Φ`, the two-root positive cone
`{γ : H.root | ∃ i j : ℕ, (rootSystem H).root γ = i • (rootSystem H).root α + j • (rootSystem H).root β}`
is a closed asymmetric subset of `Φ`. -/
theorem isClosed_and_isAsymmetric_posRoots_and_twoRootCone
    (x : Weight K H L → L) :
    (∀ b : (rootSystem H).Base,
        IsClosedRootSubset H {α : H.root | b.IsPos α} ∧
          IsAsymmetricRootSubset H {α : H.root | b.IsPos α} ∧
          closedSubsetSubring H {α : H.root | b.IsPos α} x =
            Humphreys27_1.kostantPosSubring b x) ∧
      ∀ (α β : H.root),
        LinearIndependent K ![(rootSystem H).root α, (rootSystem H).root β] →
          IsClosedRootSubset H
            {γ : H.root | ∃ i j : ℕ,
              (rootSystem H).root γ =
                i • (rootSystem H).root α + j • (rootSystem H).root β} ∧
          IsAsymmetricRootSubset H
            {γ : H.root | ∃ i j : ℕ,
              (rootSystem H).root γ =
                i • (rootSystem H).root α + j • (rootSystem H).root β} := by
  refine ⟨fun b => ⟨?_, ?_, ?_⟩, fun α β hlin => ⟨?_, ?_⟩⟩
  · intro α β γ hα hβ hγ
    exact hα.add hβ hγ
  · intro α β hα hβ hneg
    let _ := (rootSystem H).indexNeg
    have hroot_neg : (rootSystem H).root (-β) = -(rootSystem H).root β := by
      simp only [indexNeg_neg, root_reflectionPerm, reflection_apply_self]
    have hα_eq : α = -β := (rootSystem H).root.injective (hneg.trans hroot_neg.symm)
    rw [hα_eq] at hα
    exact (RootPairing.Base.IsPos.neg_iff_not b β).mp hα hβ
  · rfl
  · rintro γ₁ γ₂ γ ⟨i₁, j₁, h₁⟩ ⟨i₂, j₂, h₂⟩ hγ
    refine ⟨i₁ + i₂, j₁ + j₂, ?_⟩
    rw [hγ, h₁, h₂, add_smul, add_smul]
    abel
  · rintro γ₁ γ₂ ⟨i₁, j₁, h₁⟩ ⟨i₂, j₂, h₂⟩ hneg
    have hsum0 : (i₁ + i₂) • (rootSystem H).root α + (j₁ + j₂) • (rootSystem H).root β = 0 := by
      have h0 : (rootSystem H).root γ₁ + (rootSystem H).root γ₂ = 0 := by
        rw [hneg, neg_add_cancel]
      rw [h₁, h₂] at h0
      calc
        (i₁ + i₂) • (rootSystem H).root α + (j₁ + j₂) • (rootSystem H).root β
          = (i₁ • (rootSystem H).root α + j₁ • (rootSystem H).root β) +
              (i₂ • (rootSystem H).root α + j₂ • (rootSystem H).root β) := by
                rw [add_smul, add_smul]; abel
        _ = 0 := h0
    rw [← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K] at hsum0
    obtain ⟨hi, hj⟩ := hlin.eq_zero_of_pair hsum0
    have hi0 : i₁ + i₂ = 0 := Nat.cast_eq_zero.mp hi
    have hj0 : j₁ + j₂ = 0 := Nat.cast_eq_zero.mp hj
    have hγ₁0 : (rootSystem H).root γ₁ = 0 := by
      rw [h₁, show i₁ = 0 by omega, show j₁ = 0 by omega]
      simp
    exact (rootSystem H).ne_zero γ₁ hγ₁0

end ClosedSubsetBasis

end Humphreys26_3B
