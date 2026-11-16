import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Lie.Basis.Base
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.RingTheory.Binomial
import TauCeti.Algebra.Lie.Sl2.Straightening
import TauCeti.Algebra.Lie.UniversalEnveloping.Commutation
import TauCeti.Algebra.Lie.Weights.Chevalley.System
import TauCeti.Algebra.Lie.Weights.Root.CorootSpan
import TauCeti.Algebra.Module.Rat
import TauCeti.RingTheory.Binomial
import TauCeti.RingTheory.Binomial.IntegralSpan
import TauCeti.RingTheory.DividedPowers.Associative
import TauCeti.RingTheory.DividedPowers.Commutation
import Humphreys.Ch7.Kostant.GapA
import Humphreys.Ch7.Kostant.GapB
import Humphreys.Ch7.Kostant.GapC

open LieAlgebra LieAlgebra.IsKilling LieModule RootPairing TauCeti TauCeti.Associative
open Humphreys26_4.GapA Humphreys26_4.GapB Humphreys26_4.GapC

universe u v

namespace Humphreys26_4.GapD

/-! ### Pure Monoid & List Inversion Helpers -/

section MonoidListHelpers

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

end MonoidListHelpers

/-! ### Gap 26.4-D Straightening in `U_K(L)` -/

section GeneralCharZeroField

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

noncomputable local instance instAlgebraRatUEA :
    Algebra ℚ (_root_.UniversalEnvelopingAlgebra K L) :=
  Algebra.compHom (_root_.UniversalEnvelopingAlgebra K L) (algebraMap ℚ K)

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- Subring generated by the simple-coroot binomials `Ring.choose h_i n`. -/
private noncomputable def cartanSubring {ℓ : ℕ} (b : (rootSystem H).Base)
    (baseOrd : Fin ℓ ≃ ↥b.support) : Subring (_root_.UniversalEnvelopingAlgebra K L) :=
  Subring.closure
    (Set.range fun p : Fin ℓ × ℕ =>
      Ring.choose
        (_root_.UniversalEnvelopingAlgebra.ι K
          (((rootSystem H).coroot (baseOrd p.1).1 : H) : L))
        p.2)

private theorem commute_simple_coroots {ℓ : ℕ} (b : (rootSystem H).Base)
    (baseOrd : Fin ℓ ≃ ↥b.support) (i j : Fin ℓ) :
    Commute
      (_root_.UniversalEnvelopingAlgebra.ι K
        (((rootSystem H).coroot (baseOrd i).1 : H) : L))
      (_root_.UniversalEnvelopingAlgebra.ι K
        (((rootSystem H).coroot (baseOrd j).1 : H) : L)) := by
  have hlie :
      ⁅(((rootSystem H).coroot (baseOrd i).1 : H) : L),
       (((rootSystem H).coroot (baseOrd j).1 : H) : L)⁆ = 0 := by
    rw [rootSystem_coroot_apply, rootSystem_coroot_apply]
    exact TauCeti.lie_coroot_coroot_eq_zero _ _
  have hmap := (_root_.UniversalEnvelopingAlgebra.ι K).map_lie
    (((rootSystem H).coroot (baseOrd i).1 : H) : L)
    (((rootSystem H).coroot (baseOrd j).1 : H) : L)
  rw [hlie, map_zero, LieRing.of_associative_ring_bracket] at hmap
  exact sub_eq_zero.mp hmap.symm

private theorem mem_cartanSubring_iff_mem_closure_cartanTerms
    {ℓ : ℕ} (b : (rootSystem H).Base) (baseOrd : Fin ℓ ≃ ↥b.support)
    {c : _root_.UniversalEnvelopingAlgebra K L} :
    c ∈ cartanSubring b baseOrd ↔
      c ∈ AddSubgroup.closure
        (Set.range fun B : Fin ℓ → ℕ =>
          (List.ofFn fun i : Fin ℓ =>
            Ring.choose
              (_root_.UniversalEnvelopingAlgebra.ι K
                (((rootSystem H).coroot (baseOrd i).1 : H) : L))
              (B i)).prod) :=
  TauCeti.mem_subringClosure_range_ringChoose_iff_mem_closure_range_prod_ofFn
    (fun i : Fin ℓ =>
      _root_.UniversalEnvelopingAlgebra.ι K
        (((rootSystem H).coroot (baseOrd i).1 : H) : L))
    (commute_simple_coroots b baseOrd)

private theorem ringChoose_coroot_add_intCast_mem_cartanSubring
    {ℓ : ℕ} (b : (rootSystem H).Base) (baseOrd : Fin ℓ ≃ ↥b.support)
    (α : H.root) (z : ℤ) (n : ℕ) :
    Ring.choose
      (_root_.UniversalEnvelopingAlgebra.ι K ((coroot (α : Weight K H L) : H) : L) +
        (z : _root_.UniversalEnvelopingAlgebra K L)) n ∈
      cartanSubring b baseOrd := by
  let s : Set (_root_.UniversalEnvelopingAlgebra K L) :=
    Set.range fun i : Fin ℓ =>
      _root_.UniversalEnvelopingAlgebra.ι K
        (((rootSystem H).coroot (baseOrd i).1 : H) : L)
  have hcomm : ∀ u ∈ s, ∀ v ∈ s, Commute u v := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact commute_simple_coroots b baseOrd i j
  have hs : ∀ u ∈ s, ∀ m : ℕ, Ring.choose u m ∈ cartanSubring b baseOrd := by
    rintro _ ⟨i, rfl⟩ m
    exact Subring.subset_closure ⟨(i, m), rfl⟩
  have hmem_span :
      _root_.UniversalEnvelopingAlgebra.ι K ((coroot (α : Weight K H L) : H) : L) ∈
        Submodule.span ℤ s := by
    have ha : (rootSystem H).coroot α ∈ Submodule.span ℤ ((rootSystem H).coroot '' b.support) :=
      b.coroot_mem_span_int α
    let fℤ : H →ₗ[ℤ] _root_.UniversalEnvelopingAlgebra K L :=
      ((_root_.UniversalEnvelopingAlgebra.ι K).toLinearMap.comp H.incl.toLinearMap).restrictScalars ℤ
    have hmap : fℤ ((rootSystem H).coroot α) ∈
        Submodule.map fℤ (Submodule.span ℤ ((rootSystem H).coroot '' b.support)) :=
      ⟨(rootSystem H).coroot α, ha, rfl⟩
    rw [Submodule.map_span] at hmap
    have hle : Submodule.span ℤ (fℤ '' ((rootSystem H).coroot '' b.support)) ≤
        Submodule.span ℤ s := by
      refine Submodule.span_mono ?_
      rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      refine ⟨baseOrd.symm ⟨r, hr⟩, ?_⟩
      simp [fℤ]
    have hm := hle hmap
    simpa [fℤ, rootSystem_coroot_apply] using hm
  exact TauCeti.Ring.choose_add_intCast_mem
    (fun k _ => TauCeti.Ring.choose_mem_of_mem_span (cartanSubring b baseOrd) hcomm hs hmem_span k)
    z

/-- Lemma 26.3D (`K`-polymorphic): move `c ∈ cartanSubring` to the right past `x_α^{(n)}`. -/
private theorem exists_mem_cartanSubring_mul_dividedPower
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {ℓ : ℕ} (b : (rootSystem H).Base) (baseOrd : Fin ℓ ≃ ↥b.support)
    (α : H.root) (n : ℕ)
    {c : _root_.UniversalEnvelopingAlgebra K L} (hc : c ∈ cartanSubring b baseOrd) :
    ∃ c' ∈ cartanSubring b baseOrd,
      c * dividedPower n (_root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L))) =
        dividedPower n (_root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L))) * c' := by
  induction hc using Subring.closure_induction with
  | mem u hu =>
    obtain ⟨⟨i, k⟩, rfl⟩ := hu
    let z : ℤ := TauCeti.rootCartanWeight (α : Weight K H L) (((baseOrd i).1 : H.root) : Weight K H L)
    have hlie :
        ⁅(((rootSystem H).coroot (baseOrd i).1 : H) : L), x (α : Weight K H L)⁆ =
          z • x (α : Weight K H L) := by
      rw [rootSystem_coroot_apply, hx.toIsSl2System.lie_coroot,
        ← TauCeti.intCast_rootCartanWeight_apply, Int.cast_smul_eq_zsmul]
    have hrel :=
      TauCeti.UniversalEnvelopingAlgebra.ι_mul_ι_eq_ι_mul_ι_add_zsmul_one (R := K) hlie
    have hcomm := ringChoose_mul_dividedPower k hrel ((Commute.one_left _).smul_left z) n
    have hshift :
        _root_.UniversalEnvelopingAlgebra.ι K (((rootSystem H).coroot (baseOrd i).1 : H) : L) +
            n • (z • (1 : _root_.UniversalEnvelopingAlgebra K L)) =
          _root_.UniversalEnvelopingAlgebra.ι K
              ((coroot (((baseOrd i).1 : H.root) : Weight K H L) : H) : L) +
            (((n : ℤ) * z : ℤ) : _root_.UniversalEnvelopingAlgebra K L) := by
      rw [rootSystem_coroot_apply, ← Nat.cast_smul_eq_nsmul ℤ, smul_smul, zsmul_one]
    refine ⟨Ring.choose
      (_root_.UniversalEnvelopingAlgebra.ι K (((rootSystem H).coroot (baseOrd i).1 : H) : L) +
        n • (z • (1 : _root_.UniversalEnvelopingAlgebra K L))) k, ?_, hcomm⟩
    rw [hshift]
    exact ringChoose_coroot_add_intCast_mem_cartanSubring b baseOrd (baseOrd i).1 ((n : ℤ) * z) k
  | zero => exact ⟨0, (cartanSubring b baseOrd).zero_mem, by simp⟩
  | one => exact ⟨1, (cartanSubring b baseOrd).one_mem, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨u', hu', heu⟩ := hu
    obtain ⟨v', hv', hev⟩ := hv
    exact ⟨u' + v', (cartanSubring b baseOrd).add_mem hu' hv',
      by simp only [add_mul, mul_add, heu, hev]⟩
  | neg u _ hu =>
    obtain ⟨u', hu', heu⟩ := hu
    exact ⟨-u', (cartanSubring b baseOrd).neg_mem hu', by simp only [neg_mul, mul_neg, heu]⟩
  | mul u v _ _ hu hv =>
    obtain ⟨u', hu', heu⟩ := hu
    obtain ⟨v', hv', hev⟩ := hv
    exact ⟨u' * v', (cartanSubring b baseOrd).mul_mem hu' hv',
      by rw [mul_assoc, hev, ← mul_assoc, heu, mul_assoc]⟩

/-- Move `c ∈ cartanSubring` to the right past an entire `rootWordProd`. -/
private theorem exists_mem_cartanSubring_mul_rootWordProd
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {ℓ : ℕ} (b : (rootSystem H).Base) (baseOrd : Fin ℓ ≃ ↥b.support)
    (w : List (H.root × ℕ)) :
    ∀ {c : _root_.UniversalEnvelopingAlgebra K L}, c ∈ cartanSubring b baseOrd →
      ∃ c' ∈ cartanSubring b baseOrd, c * rootWordProd x w = rootWordProd x w * c' := by
  induction w with
  | nil =>
    intro c hc
    exact ⟨c, hc, by simp [rootWordProd]⟩
  | cons p rest ih =>
    intro c hc
    obtain ⟨c₁, hc₁, he1⟩ :=
      exists_mem_cartanSubring_mul_dividedPower hx b baseOrd p.1 p.2 hc
    obtain ⟨c₂, hc₂, he2⟩ := ih hc₁
    refine ⟨c₂, hc₂, ?_⟩
    simp only [rootWordProd, List.map_cons, List.prod_cons] at he2 ⊢
    rw [← mul_assoc, he1, mul_assoc, he2, mul_assoc]

/-- Move `c ∈ cartanSubring` to the left past `x_α^{(n)}`. -/
private theorem exists_mem_cartanSubring_dividedPower_mul
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {ℓ : ℕ} (b : (rootSystem H).Base) (baseOrd : Fin ℓ ≃ ↥b.support)
    (α : H.root) (n : ℕ)
    {c : _root_.UniversalEnvelopingAlgebra K L} (hc : c ∈ cartanSubring b baseOrd) :
    ∃ c' ∈ cartanSubring b baseOrd,
      dividedPower n (_root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L))) * c =
        c' * dividedPower n (_root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L))) := by
  induction hc using Subring.closure_induction with
  | mem u hu =>
    obtain ⟨⟨i, k⟩, rfl⟩ := hu
    let z : ℤ := TauCeti.rootCartanWeight (α : Weight K H L) (((baseOrd i).1 : H.root) : Weight K H L)
    have hlie :
        ⁅(((rootSystem H).coroot (baseOrd i).1 : H) : L), x (α : Weight K H L)⁆ =
          z • x (α : Weight K H L) := by
      rw [rootSystem_coroot_apply, hx.toIsSl2System.lie_coroot,
        ← TauCeti.intCast_rootCartanWeight_apply, Int.cast_smul_eq_zsmul]
    have hrel :=
      TauCeti.UniversalEnvelopingAlgebra.ι_mul_ι_eq_ι_mul_ι_add_zsmul_one (R := K) hlie
    have hcomm := dividedPower_mul_ringChoose k hrel ((Commute.one_left _).smul_left z) n
    have hshift :
        _root_.UniversalEnvelopingAlgebra.ι K (((rootSystem H).coroot (baseOrd i).1 : H) : L) -
            n • (z • (1 : _root_.UniversalEnvelopingAlgebra K L)) =
          _root_.UniversalEnvelopingAlgebra.ι K
              ((coroot (((baseOrd i).1 : H.root) : Weight K H L) : H) : L) +
            ((-((n : ℤ) * z) : ℤ) : _root_.UniversalEnvelopingAlgebra K L) := by
      rw [rootSystem_coroot_apply, ← Nat.cast_smul_eq_nsmul ℤ, smul_smul, zsmul_one,
        Int.cast_neg, sub_eq_add_neg]
    refine ⟨Ring.choose
      (_root_.UniversalEnvelopingAlgebra.ι K (((rootSystem H).coroot (baseOrd i).1 : H) : L) -
        n • (z • (1 : _root_.UniversalEnvelopingAlgebra K L))) k, ?_, hcomm⟩
    rw [hshift]
    exact ringChoose_coroot_add_intCast_mem_cartanSubring b baseOrd (baseOrd i).1 (-((n : ℤ) * z)) k
  | zero => exact ⟨0, (cartanSubring b baseOrd).zero_mem, by simp⟩
  | one => exact ⟨1, (cartanSubring b baseOrd).one_mem, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨u', hu', heu⟩ := hu
    obtain ⟨v', hv', hev⟩ := hv
    exact ⟨u' + v', (cartanSubring b baseOrd).add_mem hu' hv',
      by simp only [add_mul, mul_add, heu, hev]⟩
  | neg u _ hu =>
    obtain ⟨u', hu', heu⟩ := hu
    exact ⟨-u', (cartanSubring b baseOrd).neg_mem hu', by simp only [neg_mul, mul_neg, heu]⟩
  | mul u v _ _ hu hv =>
    obtain ⟨u', hu', heu⟩ := hu
    obtain ⟨v', hv', hev⟩ := hv
    exact ⟨u' * v', (cartanSubring b baseOrd).mul_mem hu' hv',
      by rw [← mul_assoc, heu, mul_assoc, hev, ← mul_assoc]⟩

/-- Move `c ∈ cartanSubring` to the left past any list product of root divided powers. -/
private theorem exists_mem_cartanSubring_list_dividedPower_mul
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {ℓ : ℕ} (b : (rootSystem H).Base) (baseOrd : Fin ℓ ≃ ↥b.support)
    (l : List (H.root × ℕ)) :
    ∀ {c : _root_.UniversalEnvelopingAlgebra K L}, c ∈ cartanSubring b baseOrd →
      ∃ c' ∈ cartanSubring b baseOrd,
        (l.map fun p =>
          dividedPower p.2 (_root_.UniversalEnvelopingAlgebra.ι K (x (p.1 : Weight K H L)))).prod * c =
        c' * (l.map fun p =>
          dividedPower p.2 (_root_.UniversalEnvelopingAlgebra.ι K (x (p.1 : Weight K H L)))).prod := by
  induction l with
  | nil =>
    intro c hc
    exact ⟨c, hc, by simp⟩
  | cons p rest ih =>
    intro c hc
    obtain ⟨c₁, hc₁, he1⟩ := ih hc
    obtain ⟨c₂, hc₂, he2⟩ :=
      exists_mem_cartanSubring_dividedPower_mul hx b baseOrd p.1 p.2 hc₁
    refine ⟨c₂, hc₂, ?_⟩
    simp only [List.map_cons, List.prod_cons]
    rw [mul_assoc, he1, ← mul_assoc, he2, mul_assoc]

/-! ### Equivalence `H.root ≃ Fin (m + m)` and Ordered Words → `kostantLattice` -/

private theorem coe_indexNeg_weight' (α : H.root) :
    ((letI := (rootSystem H).indexNeg; -α : H.root) : Weight K H L) = -(α : Weight K H L) := by
  let _ := (rootSystem H).indexNeg
  apply Weight.ext
  intro h
  have hroot : (rootSystem H).root (-α) = -(rootSystem H).root α := by
    simp only [indexNeg_neg, root_reflectionPerm, reflection_apply_self]
  have hpt := DFunLike.congr_fun hroot h
  rw [Weight.coe_neg, Pi.neg_apply]
  simpa only [rootSystem_root_apply, Weight.toLinear_apply, LinearMap.neg_apply] using hpt

private noncomputable def finRootEquiv {m : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α}) :
    Fin (m + m) ≃ H.root := by
  classical
  letI := (rootSystem H).indexNeg
  let negEquivPos : {α : H.root // ¬ b.IsPos α} ≃ {α : H.root // b.IsPos α} :=
    { toFun := fun α => ⟨-α.1, (RootPairing.Base.IsPos.neg_iff_not b α.1).mpr α.2⟩
      invFun := fun α =>
        ⟨-α.1, (RootPairing.Base.IsPos.neg_iff_not b (-α.1)).mp (by simpa using α.2)⟩
      left_inv := fun α => Subtype.ext (neg_neg α.1)
      right_inv := fun α => Subtype.ext (neg_neg α.1) }
  exact finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (posOrd.trans negEquivPos.symm) posOrd).trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCompl b.IsPos)))

private theorem finRootEquiv_neg {m : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α}) (j : Fin m) :
    ((finRootEquiv b posOrd (Fin.castAdd m j) : H.root) : Weight K H L) =
      -((posOrd j).1 : Weight K H L) := by
  have h1 : finRootEquiv b posOrd (Fin.castAdd m j) =
      (letI := (rootSystem H).indexNeg; -(posOrd j).1) := by
    dsimp only [finRootEquiv]
    simp [finSumFinEquiv_symm_apply_castAdd]
  rw [h1, coe_indexNeg_weight']

private theorem finRootEquiv_pos {m : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α}) (j : Fin m) :
    ((finRootEquiv b posOrd (Fin.natAdd m j) : H.root) : Weight K H L) =
      ((posOrd j).1 : Weight K H L) := by
  have h1 : finRootEquiv b posOrd (Fin.natAdd m j) = (posOrd j).1 := by
    dsimp only [finRootEquiv]
    rw [Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd]
    simp
  rw [h1]

/-- Mirror of `kostantLattice` so `GapD` unifies definitionally (`rfl`) with `KostantTheorem26_4`. -/
noncomputable abbrev latticeSpan {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) (x : Weight K H L → L) :
    Submodule ℤ (_root_.UniversalEnvelopingAlgebra K L) :=
  Submodule.span ℤ
    (Set.range fun p : (Fin m → ℕ) × (Fin ℓ → ℕ) × (Fin m → ℕ) =>
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
              (_root_.UniversalEnvelopingAlgebra.ι K (x ((posOrd j).1 : Weight K H L)))).prod)

private theorem ordered_rootWordProd_mul_cartan_mem_latticeSpan
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support)
    {w : List (H.root × ℕ)}
    (hpw : w.Pairwise (fun p q =>
      ((finRootEquiv b posOrd).symm p.1 : ℕ) < ((finRootEquiv b posOrd).symm q.1 : ℕ)))
    {c : _root_.UniversalEnvelopingAlgebra K L} (hc : c ∈ cartanSubring b baseOrd) :
    rootWordProd x w * c ∈ latticeSpan b posOrd baseOrd x := by
  let e := (finRootEquiv b posOrd).symm
  let lFin : List (Fin (m + m) × ℕ) := w.map fun p => (e p.1, p.2)
  have hpw_fin : lFin.Pairwise (fun p q => p.1 < q.1) := by
    rw [List.pairwise_map]
    exact hpw.imp fun h => Fin.lt_def.mpr h
  let g : Fin (m + m) → ℕ → _root_.UniversalEnvelopingAlgebra K L := fun idx k =>
    dividedPower k (_root_.UniversalEnvelopingAlgebra.ι K
      (x ((finRootEquiv b posOrd idx : H.root) : Weight K H L)))
  have hw_eq : rootWordProd x w =
      (List.ofFn fun idx : Fin (m + m) => g idx (lookupExp lFin idx)).prod := by
    have hmap :
        (w.map fun p =>
          dividedPower p.2 (_root_.UniversalEnvelopingAlgebra.ι K (x (p.1 : Weight K H L)))) =
        (lFin.map fun p => g p.1 p.2) := by
      simp [lFin, g, e, List.map_map]
    rw [rootWordProd, hmap]
    exact prod_map_eq_prod_ofFn_of_pairwise g (fun _ => dividedPower_zero _) lFin hpw_fin
  let A : Fin m → ℕ := fun j => lookupExp lFin (Fin.castAdd m j)
  let C : Fin m → ℕ := fun j => lookupExp lFin (Fin.natAdd m j)
  have hsplit :
      (List.ofFn fun idx : Fin (m + m) => g idx (lookupExp lFin idx)).prod =
        (List.ofFn fun j : Fin m =>
          dividedPower (A j)
            (_root_.UniversalEnvelopingAlgebra.ι K (x (-((posOrd j).1 : Weight K H L))))).prod *
        (List.ofFn fun j : Fin m =>
          dividedPower (C j)
            (_root_.UniversalEnvelopingAlgebra.ι K (x ((posOrd j).1 : Weight K H L)))).prod := by
    rw [List.ofFn_add, List.prod_append]
    congr 1
    · refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
      change g (Fin.castAdd m j) (A j) = _
      simp only [g, finRootEquiv_neg]
    · refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
      change g (Fin.natAdd m j) (C j) = _
      simp only [g, finRootEquiv_pos]
  let lPos : List (H.root × ℕ) := List.ofFn fun j : Fin m => ((posOrd j).1, C j)
  have heC_eq :
      (List.ofFn fun j : Fin m =>
        dividedPower (C j)
          (_root_.UniversalEnvelopingAlgebra.ι K (x ((posOrd j).1 : Weight K H L)))).prod =
      (lPos.map fun p =>
        dividedPower p.2 (_root_.UniversalEnvelopingAlgebra.ι K (x (p.1 : Weight K H L)))).prod := by
    simp [lPos, List.map_ofFn, Function.comp_def]
  obtain ⟨c', hc', hecomm⟩ :=
    exists_mem_cartanSubring_list_dividedPower_mul hx b baseOrd lPos hc
  rw [← heC_eq] at hecomm
  rw [hw_eq, hsplit, mul_assoc, hecomm, ← mul_assoc]
  have hc'_span := (mem_cartanSubring_iff_mem_closure_cartanTerms b baseOrd).mp hc'
  clear hc hecomm hc'
  induction hc'_span using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨B, rfl⟩ := hu
    exact Submodule.subset_span ⟨(A, B, C), rfl⟩
  | zero =>
    simp only [mul_zero, zero_mul]
    exact (latticeSpan b posOrd baseOrd x).zero_mem
  | add u v _ _ hu hv =>
    simp only [mul_add, add_mul]
    exact (latticeSpan b posOrd baseOrd x).add_mem hu hv
  | neg u _ hu =>
    simp only [mul_neg, neg_mul]
    exact (latticeSpan b posOrd baseOrd x).neg_mem hu

omit [LieAlgebra.IsKilling K L] [LieModule.IsTriangularizable K H L] in
private theorem rootWordProd_append (x : Weight K H L → L) (w₁ w₂ : List (H.root × ℕ)) :
    rootWordProd x (w₁ ++ w₂) = rootWordProd x w₁ * rootWordProd x w₂ := by
  simp [rootWordProd, List.map_append, List.prod_append]

private theorem rootWordDeg_append {α : Type*} (w₁ w₂ : List (α × ℕ)) :
    rootWordDeg (w₁ ++ w₂) = rootWordDeg w₁ + rootWordDeg w₂ := by
  simp [rootWordDeg, List.map_append, List.sum_append]

/-- **Main Straightening Induction (Gap 26.4-D / `NB-4`):**
Every `(rootWordProd x w) * c` with `c ∈ cartanSubring b baseOrd` belongs to `kostantLattice`. -/
theorem rootWordProd_mul_cartan_mem_latticeSpan
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) :
    ∀ (w : List (H.root × ℕ)) {c : _root_.UniversalEnvelopingAlgebra K L},
      c ∈ cartanSubring b baseOrd →
      rootWordProd x w * c ∈ latticeSpan b posOrd baseOrd x := by
  classical
  let pos : H.root → ℕ := fun r => ((finRootEquiv b posOrd).symm r : ℕ)
  have main_ind :
      ∀ (d : ℕ) (M : ℕ) (w : List (H.root × ℕ))
        {c : _root_.UniversalEnvelopingAlgebra K L},
        rootWordDeg w = d → wordMeasure pos w = M → c ∈ cartanSubring b baseOrd →
        rootWordProd x w * c ∈ latticeSpan b posOrd baseOrd x := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih_d =>
      intro M
      induction M using Nat.strong_induction_on with
      | ind M ih_M =>
        intro w c hd hM hc
        by_cases hpw : w.Pairwise (fun p q => pos p.1 < pos q.1)
        · exact ordered_rootWordProd_mul_cartan_mem_latticeSpan hx b posOrd baseOrd hpw hc
        · obtain ⟨w₁, ⟨α, a⟩, ⟨β, k⟩, w₂, rfl, hge⟩ :=
            exists_adj_ge_of_not_pairwise pos w hpw
          let E (r : H.root) : _root_.UniversalEnvelopingAlgebra K L :=
            _root_.UniversalEnvelopingAlgebra.ι K (x (r : Weight K H L))
          have hw_decomp :
              rootWordProd x (w₁ ++ (α, a) :: (β, k) :: w₂) * c =
                rootWordProd x w₁ * (dividedPower a (E α) * dividedPower k (E β)) *
                  rootWordProd x w₂ * c := by
            rw [rootWordProd_append]
            simp only [rootWordProd, List.map_cons, List.prod_cons, E, mul_assoc]
          rcases lt_or_eq_of_le hge with hlt | heq_pos
          · -- Strict inversion `pos β < pos α`, hence `α ≠ β`
            have hne : α ≠ β := fun h => by subst h; exact lt_irrefl _ hlt
            have hswap_mem :
                rootWordProd x w₁ * (dividedPower k (E β) * dividedPower a (E α)) *
                  rootWordProd x w₂ * c ∈ latticeSpan b posOrd baseOrd x := by
              have hprod :
                  rootWordProd x w₁ * (dividedPower k (E β) * dividedPower a (E α)) *
                    rootWordProd x w₂ * c =
                    rootWordProd x (w₁ ++ (β, k) :: (α, a) :: w₂) * c := by
                rw [rootWordProd_append]
                simp only [rootWordProd, List.map_cons, List.prod_cons, E, mul_assoc]
              rw [hprod]
              refine ih_M (wordMeasure pos (w₁ ++ (β, k) :: (α, a) :: w₂)) ?_ _ ?_ rfl hc
              · rw [← hM]
                exact wordMeasure_swap_lt pos hlt w₁ w₂
              · rw [← hd, rootWordDeg_append, rootWordDeg_append]
                simp [rootWordDeg]
                omega
            by_cases hneg : (rootSystem H).root α = -(rootSystem H).root β
            · -- Opposite-root `sl₂` straightening (Lemma 26.2)
              have hβ_eq : (β : Weight K H L) = -(α : Weight K H L) := by
                apply Weight.ext
                intro h
                have hpt := DFunLike.congr_fun hneg h
                rw [Weight.coe_neg, Pi.neg_apply]
                have hpt' : ((α : Weight K H L) : H → K) h = -((β : Weight K H L) : H → K) h := by
                  simpa [rootSystem_root_apply, Weight.toLinear_apply] using hpt
                rw [hpt', neg_neg]
              have ht := hx.toIsSl2System.isSl2Triple (α : Weight K H L) (H.isNonZero_coe_root α)
              have hstr := LieHom.dividedPower_map_e_mul_dividedPower_map_f
                (_root_.UniversalEnvelopingAlgebra.ι K)
                ht.lie_e_f ht.lie_h_e_nsmul ht.lie_h_f_nsmul a k
              have hEβ : E β = _root_.UniversalEnvelopingAlgebra.ι K (x (-(α : Weight K H L))) := by
                simp only [E, hβ_eq]
              rw [← hEβ] at hstr
              have h0mem : (0 : ℕ) ∈ Finset.range (min a k + 1) := Finset.mem_range.mpr (by omega)
              rw [← Finset.add_sum_erase _ _ h0mem] at hstr
              have h0term :
                  dividedPower (k - 0) (E β) *
                    Ring.choose
                      (_root_.UniversalEnvelopingAlgebra.ι K ((coroot (α : Weight K H L) : H) : L) -
                        (a + k : ℕ) + (2 * 0 : ℕ)) 0 *
                    dividedPower (a - 0) (E α) =
                  dividedPower k (E β) * dividedPower a (E α) := by
                simp
              rw [h0term] at hstr
              rw [hw_decomp, hstr, mul_add, add_mul, add_mul]
              refine (latticeSpan b posOrd baseOrd x).add_mem hswap_mem ?_
              rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
              refine (latticeSpan b posOrd baseOrd x).sum_mem fun j hj => ?_
              obtain ⟨hj_ne, hj_range⟩ := Finset.mem_erase.mp hj
              have hj_le : j ≤ min a k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj_range)
              let zj : ℤ := 2 * (j : ℤ) - ((a + k : ℕ) : ℤ)
              have harg_eq :
                  _root_.UniversalEnvelopingAlgebra.ι K ((coroot (α : Weight K H L) : H) : L) -
                      (a + k : ℕ) + (2 * j : ℕ) =
                    _root_.UniversalEnvelopingAlgebra.ι K ((coroot (α : Weight K H L) : H) : L) +
                      (zj : _root_.UniversalEnvelopingAlgebra K L) := by
                have hz : (zj : _root_.UniversalEnvelopingAlgebra K L) =
                    (2 * j : ℕ) - (a + k : ℕ) := by
                  rw [← Int.cast_natCast (2 * j), ← Int.cast_natCast (a + k), ← Int.cast_sub]
                  congr 1
                rw [hz]; abel
              rw [harg_eq]
              have hch_mem :
                  Ring.choose
                    (_root_.UniversalEnvelopingAlgebra.ι K ((coroot (α : Weight K H L) : H) : L) +
                      (zj : _root_.UniversalEnvelopingAlgebra K L)) j ∈
                  cartanSubring b baseOrd :=
                ringChoose_coroot_add_intCast_mem_cartanSubring b baseOrd α zj j
              obtain ⟨cj, hcj, hecj⟩ :=
                exists_mem_cartanSubring_mul_rootWordProd hx b baseOrd
                  ((α, a - j) :: w₂) hch_mem
              have htail_eq :
                  rootWordProd x ((α, a - j) :: w₂) =
                    dividedPower (a - j) (E α) * rootWordProd x w₂ := by
                simp [rootWordProd, E]
              rw [htail_eq] at hecj
              have hterm_eq :
                  rootWordProd x w₁ *
                    (dividedPower (k - j) (E β) *
                      Ring.choose
                        (_root_.UniversalEnvelopingAlgebra.ι K
                            ((coroot (α : Weight K H L) : H) : L) +
                          (zj : _root_.UniversalEnvelopingAlgebra K L)) j *
                      dividedPower (a - j) (E α)) *
                    rootWordProd x w₂ * c =
                  rootWordProd x (w₁ ++ (β, k - j) :: (α, a - j) :: w₂) * (cj * c) := by
                calc
                  _ = rootWordProd x w₁ * dividedPower (k - j) (E β) *
                        (Ring.choose
                          (_root_.UniversalEnvelopingAlgebra.ι K
                              ((coroot (α : Weight K H L) : H) : L) +
                            (zj : _root_.UniversalEnvelopingAlgebra K L)) j *
                          (dividedPower (a - j) (E α) * rootWordProd x w₂)) * c := by
                    simp only [mul_assoc]
                  _ = rootWordProd x w₁ * dividedPower (k - j) (E β) *
                        (dividedPower (a - j) (E α) * rootWordProd x w₂ * cj) * c := by
                    rw [hecj]
                  _ = rootWordProd x (w₁ ++ (β, k - j) :: (α, a - j) :: w₂) * (cj * c) := by
                    rw [rootWordProd_append]
                    simp only [rootWordProd, List.map_cons, List.prod_cons, E, mul_assoc]
              rw [hterm_eq]
              refine ih_d (rootWordDeg (w₁ ++ (β, k - j) :: (α, a - j) :: w₂)) ?_
                _ _ rfl rfl ((cartanSubring b baseOrd).mul_mem hcj hc)
              rw [← hd, rootWordDeg_append, rootWordDeg_append]
              simp only [rootWordDeg, List.map_cons, List.sum_cons]
              omega
            · -- Non-opposite multi-root commutation (Lemma 26.3C, Gap 26.4-C)
              have hcomm :=
                dividedPower_mul_dividedPower_sub_comm_mem_lowDegSpan hx α β hne hneg a k
              have hsplit_comm :
                  dividedPower a (E α) * dividedPower k (E β) =
                    dividedPower k (E β) * dividedPower a (E α) +
                      (dividedPower a (E α) * dividedPower k (E β) -
                        dividedPower k (E β) * dividedPower a (E α)) := by
                abel
              rw [hw_decomp, hsplit_comm, mul_add, add_mul, add_mul]
              refine (latticeSpan b posOrd baseOrd x).add_mem hswap_mem ?_
              refine Submodule.span_induction ?_ ?_ ?_ ?_ hcomm
              · rintro _ ⟨u, hu_deg, rfl⟩
                have hprod :
                    rootWordProd x w₁ * rootWordProd x u * rootWordProd x w₂ * c =
                      rootWordProd x (w₁ ++ u ++ w₂) * c := by
                  simp only [rootWordProd_append, mul_assoc]
                rw [hprod]
                refine ih_d (rootWordDeg (w₁ ++ u ++ w₂)) ?_ _ _ rfl rfl hc
                rw [← hd, rootWordDeg_append, rootWordDeg_append, rootWordDeg_append]
                simp only [rootWordDeg, List.map_cons, List.sum_cons] at hu_deg ⊢
                omega
              · simp only [mul_zero, zero_mul]
                exact (latticeSpan b posOrd baseOrd x).zero_mem
              · intro u v _ _ hu hv
                simp only [mul_add, add_mul]
                exact (latticeSpan b posOrd baseOrd x).add_mem hu hv
              · intro z u _ hu
                simp only [mul_smul_comm, smul_mul_assoc]
                exact (latticeSpan b posOrd baseOrd x).smul_mem z hu
          · -- Same root `pos β = pos α`, hence `α = β` (`Associative.mul_dividedPower`)
            have hαβ : α = β := by
              apply (finRootEquiv b posOrd).symm.injective
              exact Fin.ext heq_pos.symm
            subst hαβ
            have hmerge :
                dividedPower a (E α) * dividedPower k (E α) =
                  Nat.choose (a + k) a • dividedPower (a + k) (E α) :=
              mul_dividedPower a k (E α)
            have hprod :
                rootWordProd x w₁ * dividedPower (a + k) (E α) * rootWordProd x w₂ * c =
                  rootWordProd x (w₁ ++ (α, a + k) :: w₂) * c := by
              rw [rootWordProd_append]
              simp only [rootWordProd, List.map_cons, List.prod_cons, E, mul_assoc]
            rw [hw_decomp, hmerge, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, hprod,
              ← natCast_zsmul]
            refine (latticeSpan b posOrd baseOrd x).smul_mem (Nat.choose (a + k) a : ℤ) ?_
            refine ih_M (wordMeasure pos (w₁ ++ (α, a + k) :: w₂)) ?_ _ ?_ rfl hc
            · rw [← hM]
              exact wordMeasure_merge_lt pos (p := (α, a)) (q := (α, k)) (r := (α, a + k))
                rfl rfl w₁ w₂
            · rw [← hd, rootWordDeg_append, rootWordDeg_append]
              simp only [rootWordDeg, List.map_cons, List.sum_cons]
              omega
  intro w c hc
  exact main_ind (rootWordDeg w) (wordMeasure pos w) w rfl rfl hc

/-- Proof of `kostantLattice_eq_kostantSubring`: `𝔅 = 𝔘(L)_ℤ`. -/
theorem latticeSpan_eq_rootSubring
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support) :
    (latticeSpan b posOrd baseOrd x : Set (_root_.UniversalEnvelopingAlgebra K L)) =
      (rootSubring H x : Set (_root_.UniversalEnvelopingAlgebra K L)) := by
  apply Set.Subset.antisymm
  · -- `𝔅 ⊆ 𝔘(L)_ℤ` (from Gap 26.4-A)
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨p, rfl⟩
      exact kostantMonomial_mem_rootSubring hx b posOrd baseOrd p
    · exact (rootSubring H x).zero_mem
    · intro a₁ a₂ _ _ h₁ h₂
      exact (rootSubring H x).add_mem h₁ h₂
    · intro z a₁ _ h₁
      exact zsmul_mem h₁ z
  · -- `𝔘(L)_ℤ ⊆ 𝔅` (word subring contained in `𝔅` by `rootWordProd_mul_cartan_mem_latticeSpan`)
    let wordSpan : Submodule ℤ (_root_.UniversalEnvelopingAlgebra K L) :=
      Submodule.span ℤ (Set.range (rootWordProd x))
    have hmul_wordSpan : ∀ {u v : _root_.UniversalEnvelopingAlgebra K L},
        u ∈ wordSpan → v ∈ wordSpan → u * v ∈ wordSpan := by
      intro u v hu hv
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
      · rintro _ ⟨w₁, rfl⟩
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
        · rintro _ ⟨w₂, rfl⟩
          rw [← rootWordProd_append]
          exact Submodule.subset_span ⟨w₁ ++ w₂, rfl⟩
        · simp only [mul_zero]; exact wordSpan.zero_mem
        · intro x₁ x₂ _ _ hx₁ hx₂
          rw [mul_add]; exact wordSpan.add_mem hx₁ hx₂
        · intro z x₁ _ hx₁
          rw [mul_smul_comm]; exact wordSpan.smul_mem z hx₁
      · simp only [zero_mul]; exact wordSpan.zero_mem
      · intro x₁ x₂ _ _ hx₁ hx₂
        rw [add_mul]; exact wordSpan.add_mem hx₁ hx₂
      · intro z x₁ _ hx₁
        rw [smul_mul_assoc]; exact wordSpan.smul_mem z hx₁
    let wordSubring : Subring (_root_.UniversalEnvelopingAlgebra K L) :=
      { carrier := (wordSpan : Set (_root_.UniversalEnvelopingAlgebra K L))
        mul_mem' := fun ha hb => hmul_wordSpan ha hb
        one_mem' := Submodule.subset_span ⟨[], by simp [rootWordProd]⟩
        add_mem' := fun ha hb => wordSpan.add_mem ha hb
        zero_mem' := wordSpan.zero_mem
        neg_mem' := fun ha => wordSpan.neg_mem ha }
    have hsub_le : rootSubring H x ≤ wordSubring := by
      rw [Subring.closure_le]
      rintro _ ⟨⟨α, n⟩, rfl⟩
      exact Submodule.subset_span ⟨[(α, n)], by simp [rootWordProd]⟩
    have hword_le : wordSpan ≤ latticeSpan b posOrd baseOrd x := by
      rw [Submodule.span_le]
      rintro _ ⟨w, rfl⟩
      have hm := rootWordProd_mul_cartan_mem_latticeSpan hx b posOrd baseOrd w
        (cartanSubring b baseOrd).one_mem
      rwa [mul_one] at hm
    intro u hu
    exact hword_le (hsub_le hu)

end GeneralCharZeroField

end Humphreys26_4.GapD
