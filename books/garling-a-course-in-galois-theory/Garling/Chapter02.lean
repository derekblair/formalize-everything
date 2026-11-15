import Garling.Chapter01
import Mathlib.Order.Zorn
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Chapter 2: The axiom of choice, and Zorn's lemma

Formalization of Chapter 2 (printed pp. 14–17, PDF pp. 22–25) of D. J. H. Garling,
*A Course in Galois Theory* (Cambridge University Press, 1986), following the chapter's
three sections (§2.1 *The axiom of choice*, §2.2 *Zorn's lemma*, §2.3 *The existence of a basis*)
and all numbered/headed items in source order.
-/

namespace Garling.Chapter02

open Garling.Chapter01

universe u v

/-! ## §2.1 The axiom of choice (printed p. 14, PDF p. 22) -/

/-- The Cartesian product `∏_{α ∈ A} E_α` of an indexed family of subsets `{E_α}_{α ∈ A}` of `X`,
consisting of all indexed tuples `(c_α)_{α ∈ A}` with `c_α ∈ E_α` for every `α ∈ A` (§2.1, p. 14). -/
def CartesianProduct {A : Type u} {X : Type v} (E : A → Set X) : Set (A → X) :=
  {c | ∀ α : A, c α ∈ E α}

@[simp]
theorem mem_cartesianProduct_iff {A : Type u} {X : Type v} {E : A → Set X} {c : A → X} :
    c ∈ CartesianProduct E ↔ ∀ α : A, c α ∈ E α :=
  Iff.rfl

theorem cartesianProduct_eq_univ_pi {A : Type u} {X : Type v} (E : A → Set X) :
    CartesianProduct E = Set.pi Set.univ E := by
  ext c
  simp [CartesianProduct]

/-- Garling's §2.1 formulation of the Axiom of Choice at universe `u`: for every indexed family
`{E_α}_{α ∈ A}` of non-empty subsets of `X`, the Cartesian product `∏_{α ∈ A} E_α` is non-empty
(§2.1, p. 14). -/
def GarlingAxiomOfChoice : Prop :=
  ∀ (A X : Type u) (E : A → Set X), (∀ α : A, (E α).Nonempty) → (CartesianProduct E).Nonempty

/-- Dependent indexed-family formulation of the Axiom of Choice at universe `u`: if every `E α` is
non-empty, then `(α : A) → E α` is non-empty (§2.1, p. 14). -/
def GarlingAxiomOfChoiceDep : Prop :=
  ∀ (A : Type u) (E : A → Type u), (∀ α : A, Nonempty (E α)) → Nonempty ((α : A) → E α)

/-- Equivalence between the subset-family Cartesian product formulation and the dependent
indexed-family formulation of the Axiom of Choice (§2.1, p. 14). -/
theorem garlingAxiomOfChoice_iff_dep :
    GarlingAxiomOfChoice.{u} ↔ GarlingAxiomOfChoiceDep.{u} := by
  constructor
  · intro hac A E hne
    let X : Type u := Σ α : A, E α
    let E' : A → Set X := fun α => {p | p.1 = α}
    have hne' : ∀ α : A, (E' α).Nonempty := fun α =>
      let ⟨x⟩ := hne α
      ⟨⟨α, x⟩, rfl⟩
    obtain ⟨c, hc⟩ := hac A X E' hne'
    exact ⟨fun α => hc α ▸ (c α).2⟩
  · intro hdep A X E hne
    have hne' : ∀ α : A, Nonempty {x : X // x ∈ E α} := fun α =>
      let ⟨x, hx⟩ := hne α
      ⟨⟨x, hx⟩⟩
    obtain ⟨f⟩ := hdep A (fun α => {x : X // x ∈ E α}) hne'
    exact ⟨fun α => (f α).1, fun α => (f α).2⟩

/-- The Axiom of Choice as stated in §2.1 (p. 14), proved in Lean's classical foundation. -/
theorem axiom_of_choice {A : Type u} {X : Type v} (E : A → Set X)
    (hne : ∀ α : A, (E α).Nonempty) :
    (CartesianProduct E).Nonempty :=
  ⟨fun α => (hne α).choose, fun α => (hne α).choose_spec⟩

/-- `GarlingAxiomOfChoice` holds at every universe level (§2.1, p. 14). -/
theorem garlingAxiomOfChoice_holds : GarlingAxiomOfChoice.{u} :=
  fun _ _ E hne => axiom_of_choice E hne

/-! ## §2.2 Zorn's lemma (printed pp. 14–15, PDF pp. 22–23) -/

/-- Garling's literal three-axiom definition of a partial order `≤` on a subset `S` (§2.2, p. 15):
(a) reflexivity, (b) transitivity, and (c) antisymmetry on `S`. Notice that p. 15 does not require
`S` to be non-empty. -/
structure IsGarlingPartialOrder {X : Type u} (S : Set X) (le : X → X → Prop) : Prop where
  refl : ∀ x ∈ S, le x x
  trans : ∀ ⦃x y z⦄, x ∈ S → y ∈ S → z ∈ S → le x y → le y z → le x z
  antisymm : ∀ ⦃x y⦄, x ∈ S → y ∈ S → le x y → le y x → x = y

/-- Type-level counterpart of Garling's partial order axioms (§2.2, p. 15). -/
structure IsGarlingPartialOrderType (S : Type u) (le : S → S → Prop) : Prop where
  refl : ∀ x : S, le x x
  trans : ∀ ⦃x y z : S⦄, le x y → le y z → le x z
  antisymm : ∀ ⦃x y : S⦄, le x y → le y x → x = y

/-- Every Mathlib `PartialOrder` satisfies Garling's partial order axioms (§2.2, p. 15). -/
theorem PartialOrder.isGarlingPartialOrderType (S : Type u) [PartialOrder S] :
    IsGarlingPartialOrderType S (· ≤ ·) where
  refl := le_refl
  trans _ _ _ := le_trans
  antisymm _ _ := le_antisymm

/-- Build a Mathlib `PartialOrder` structure from `IsGarlingPartialOrderType`. -/
@[reducible]
def IsGarlingPartialOrderType.toPartialOrder {S : Type u} {le : S → S → Prop}
    (h : IsGarlingPartialOrderType S le) : PartialOrder S where
  le := le
  le_refl := h.refl
  le_trans _ _ _ hab hbc := h.trans hab hbc
  le_antisymm _ _ hab hba := h.antisymm hab hba

/-- Example (§2.2, p. 15): On any collection `S` of subsets of `X`, ordering by inclusion `⊆` is a
partial order. -/
theorem inclusion_isGarlingPartialOrder {X : Type u} (S : Set (Set X)) :
    IsGarlingPartialOrder S (· ⊆ ·) where
  refl _ _ := Set.Subset.refl _
  trans _ _ _ _ _ _ h1 h2 := h1.trans h2
  antisymm _ _ _ _ h1 h2 := Set.Subset.antisymm h1 h2

/-- A partially ordered set `(S, ≤)` is *totally ordered* if any two elements of `S` are comparable
(§2.2, p. 15). -/
structure IsTotallyOrderedOn {X : Type u} (S : Set X) (le : X → X → Prop) : Prop extends
    IsGarlingPartialOrder S le where
  total : ∀ x ∈ S, ∀ y ∈ S, le x y ∨ le y x

/-- Type-level total order on `S` (§2.2, p. 15). -/
structure IsGarlingTotalOrder (S : Type u) (le : S → S → Prop) : Prop extends
    IsGarlingPartialOrderType S le where
  total : ∀ x y : S, le x y ∨ le y x

/-- Garling's literal definition of a *chain* in `(S, ≤)` (§2.2, p. 15): a **non-empty** subset
`C ⊆ S` that is totally ordered in the ordering inherited from `S`. -/
def IsGarlingChain {X : Type u} (S : Set X) (le : X → X → Prop) (C : Set X) : Prop :=
  C ⊆ S ∧ C.Nonempty ∧ ∀ x ∈ C, ∀ y ∈ C, le x y ∨ le y x

/-- Type-level counterpart of Garling's non-empty chain in `(S, ≤)` (§2.2, p. 15). -/
def IsGarlingChainType (S : Type u) (le : S → S → Prop) (C : Set S) : Prop :=
  C.Nonempty ∧ ∀ x ∈ C, ∀ y ∈ C, le x y ∨ le y x

/-- An element `x` of `S` is an *upper bound* for `A ⊆ S` if `a ≤ x` for each `a ∈ A` (§2.2, p. 15). -/
def IsGarlingUpperBound {X : Type u} (S : Set X) (le : X → X → Prop) (A : Set X) (x : X) : Prop :=
  x ∈ S ∧ ∀ a ∈ A, le a x

/-- Type-level upper bound for `A : Set S` (§2.2, p. 15). -/
def IsGarlingUpperBoundType {S : Type u} (le : S → S → Prop) (A : Set S) (x : S) : Prop :=
  ∀ a ∈ A, le a x

/-- The collection of finite subsets of `X` (§2.2, p. 15). -/
def FiniteSubsets (X : Type u) : Set (Set X) :=
  {F : Set X | F.Finite}

/-- Example (§2.2, p. 15): If `X` is infinite and `S = FiniteSubsets X` is ordered by inclusion,
`S` itself has no upper bound in `S`. -/
theorem finiteSubsets_no_upperBound {X : Type u} [Infinite X] :
    ¬ ∃ U, IsGarlingUpperBound (FiniteSubsets X) (· ⊆ ·) (FiniteSubsets X) U := by
  rintro ⟨U, hUfin, hUub⟩
  have hUniv : (Set.univ : Set X) ⊆ U := fun x _ =>
    hUub {x} (Set.finite_singleton x) (Set.mem_singleton x)
  exact Set.infinite_univ (hUfin.subset hUniv)

/-- Example (§2.2, p. 15): In `S = FiniteSubsets X` ordered by inclusion, a subset `𝒜 ⊆ S` has an
upper bound in `S` if and only if `𝒜` is finite. -/
theorem finiteSubsets_hasUpperBound_iff_finite {X : Type u} {𝒜 : Set (Set X)}
    (h𝒜 : 𝒜 ⊆ FiniteSubsets X) :
    (∃ U, IsGarlingUpperBound (FiniteSubsets X) (· ⊆ ·) 𝒜 U) ↔ 𝒜.Finite := by
  constructor
  · rintro ⟨U, hUfin, hUub⟩
    refine hUfin.finite_subsets.subset ?_
    intro F hF
    exact hUub F hF
  · intro h𝒜fin
    refine ⟨⋃₀ 𝒜, h𝒜fin.sUnion fun F hF => h𝒜 hF, ?_⟩
    intro F hF
    exact Set.subset_sUnion_of_mem hF

/-- An element `x` of `S` is *maximal* in `S` if whenever `y ∈ S` and `x ≤ y`, `x = y`
(§2.2, p. 15). -/
def IsGarlingMaximal {X : Type u} (S : Set X) (le : X → X → Prop) (x : X) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, le x y → x = y

/-- Type-level maximal element in `(S, ≤)` (§2.2, p. 15). -/
def IsGarlingMaximalType {S : Type u} (le : S → S → Prop) (x : S) : Prop :=
  ∀ y : S, le x y → x = y

/-- **Counterexample to Zorn's lemma at `S = ∅`** (`QUEUE.md` fidelity hold, §2.2, p. 15):
Because Garling defines a *chain* on p. 15 to be a **non-empty** totally ordered subset `C ⊆ S`
without restricting partial orders to non-empty sets `S`, `S = ∅` satisfies `IsGarlingPartialOrder`
and vacuously satisfies *"every chain in `S` has an upper bound"*, yet has no maximal element. -/
theorem zorn_lemma_empty_counterexample (X : Type u) (le : X → X → Prop) :
    IsGarlingPartialOrder (∅ : Set X) le ∧
      (∀ C : Set X, IsGarlingChain (∅ : Set X) le C →
        ∃ x : X, IsGarlingUpperBound (∅ : Set X) le C x) ∧
      ¬ ∃ m : X, IsGarlingMaximal (∅ : Set X) le m := by
  refine ⟨⟨by simp, by simp, by simp⟩, ?_, ?_⟩
  · rintro C ⟨hCsub, ⟨x, hxC⟩, _⟩
    exact False.elim (hCsub hxC)
  · rintro ⟨m, hm, _⟩
    exact hm

/-- **Zorn's lemma (subset version with explicit `S.Nonempty` guard)** (§2.2, p. 15):
If `S` is a non-empty partially ordered set in which every non-empty chain has an upper bound in
`S`, then `S` has at least one maximal element. -/
theorem zorn_lemma_set {X : Type u} {S : Set X} {le : X → X → Prop}
    (hpo : IsGarlingPartialOrder S le) (hne : S.Nonempty)
    (hchains : ∀ C : Set X, IsGarlingChain S le C → ∃ x : X, IsGarlingUpperBound S le C x) :
    ∃ m : X, IsGarlingMaximal S le m := by
  have : Nonempty S := hne.to_subtype
  let r : S → S → Prop := fun a b => le a.1 b.1
  have hr_trans : ∀ {a b c : S}, r a b → r b c → r a c :=
    fun {_ _ _} hab hbc => hpo.trans (Subtype.prop _) (Subtype.prop _) (Subtype.prop _) hab hbc
  have hsub : ∀ c : Set S, IsChain r c → c.Nonempty → ∃ ub : S, ∀ a ∈ c, r a ub := by
    intro c hc hcne
    let C : Set X := Subtype.val '' c
    have hCchain : IsGarlingChain S le C := by
      refine ⟨?_, hcne.image Subtype.val, ?_⟩
      · rintro _ ⟨a, _, rfl⟩
        exact a.2
      · rintro _ ⟨a, hac, rfl⟩ _ ⟨b, hbc, rfl⟩
        by_cases hab : a = b
        · subst hab
          exact Or.inl (hpo.refl a.1 a.2)
        · exact hc hac hbc hab
    obtain ⟨x, hxS, hxub⟩ := hchains C hCchain
    exact ⟨⟨x, hxS⟩, fun a hac => hxub a.1 ⟨a, hac, rfl⟩⟩
  obtain ⟨m, hm⟩ := exists_maximal_of_nonempty_chains_bounded hsub hr_trans
  refine ⟨m.1, m.2, fun y hyS hmy => ?_⟩
  have hym : le y m.1 := hm ⟨y, hyS⟩ hmy
  exact hpo.antisymm m.2 hyS hmy hym

/-- **Zorn's lemma (type-level version with explicit `Nonempty S` guard)** (§2.2, p. 15). -/
theorem zorn_lemma {S : Type u} {le : S → S → Prop}
    (hpo : IsGarlingPartialOrderType S le) [hne : Nonempty S]
    (hchains : ∀ C : Set S, IsGarlingChainType S le C → ∃ x : S, IsGarlingUpperBoundType le C x) :
    ∃ m : S, IsGarlingMaximalType le m := by
  have hpo_univ : IsGarlingPartialOrder (Set.univ : Set S) le :=
    ⟨fun x _ => hpo.refl x,
     fun _ _ _ _ _ _ h1 h2 => hpo.trans h1 h2,
     fun _ _ _ _ h1 h2 => hpo.antisymm h1 h2⟩
  obtain ⟨m, _, hm⟩ := zorn_lemma_set hpo_univ Set.univ_nonempty fun C ⟨_, hCne, hCtot⟩ =>
    let ⟨x, hx⟩ := hchains C ⟨hCne, hCtot⟩
    ⟨x, trivial, hx⟩
  exact ⟨m, fun y hmy => hm y trivial hmy⟩

/-- **Zorn's lemma (Halmos's possibly-empty-chains formulation, §2.2 footnote 1, p. 15)**:
When *every* totally ordered subset `C ⊆ S` (including `C = ∅`) has an upper bound in `S`, the
upper bound of `∅` witnesses `S.Nonempty`, so `S` has a maximal element with no separate
non-emptiness hypothesis. -/
theorem zorn_lemma_possibly_empty_chains {X : Type u} {S : Set X} {le : X → X → Prop}
    (hpo : IsGarlingPartialOrder S le)
    (hchains : ∀ C : Set X, C ⊆ S → (∀ x ∈ C, ∀ y ∈ C, le x y ∨ le y x) →
      ∃ x : X, IsGarlingUpperBound S le C x) :
    ∃ m : X, IsGarlingMaximal S le m := by
  obtain ⟨x₀, hx₀S, _⟩ := hchains ∅ (Set.empty_subset S) (by simp)
  exact zorn_lemma_set hpo ⟨x₀, hx₀S⟩ fun C ⟨hCS, _, hCtot⟩ => hchains C hCS hCtot

/-- The sound Zorn's lemma proposition at universe `u`, used as the explicit hypothesis in
Exercises 2.1 and 2.2 (§2.2, p. 15; §2.3, pp. 16–17). -/
def GarlingZornLemma : Prop :=
  ∀ (S : Type u) (le : S → S → Prop),
    IsGarlingPartialOrderType S le → Nonempty S →
    (∀ C : Set S, IsGarlingChainType S le C → ∃ x : S, IsGarlingUpperBoundType le C x) →
    ∃ m : S, IsGarlingMaximalType le m

/-- `GarlingZornLemma` holds at every universe level (§2.2, p. 15). -/
theorem garlingZornLemma_holds : GarlingZornLemma.{u} :=
  fun _ _ hpo hne hchains => @zorn_lemma _ _ hpo hne hchains

/-- Subset-based formulation of Zorn's lemma (with explicit `S.Nonempty` guard) at universe `u`
(§2.2, p. 15). -/
def GarlingZornLemmaSet : Prop :=
  ∀ (X : Type u) (S : Set X) (le : X → X → Prop),
    IsGarlingPartialOrder S le → S.Nonempty →
    (∀ C : Set X, IsGarlingChain S le C → ∃ x : X, IsGarlingUpperBound S le C x) →
    ∃ m : X, IsGarlingMaximal S le m

/-- Equivalence between the type-level (`GarlingZornLemma`) and subset-level
(`GarlingZornLemmaSet`) formulations of Zorn's lemma (§2.2, p. 15). -/
theorem garlingZornLemma_iff_set :
    GarlingZornLemma.{u} ↔ GarlingZornLemmaSet.{u} := by
  constructor
  · intro hzorn X S le hpo hne hchains
    let leSub : S → S → Prop := fun a b => le a.1 b.1
    have hpoSub : IsGarlingPartialOrderType S leSub :=
      { refl := fun a => hpo.refl a.1 a.2
        trans := fun {a b c} h1 h2 => hpo.trans a.2 b.2 c.2 h1 h2
        antisymm := fun {a b} h1 h2 => Subtype.ext (hpo.antisymm a.2 b.2 h1 h2) }
    obtain ⟨m, hm⟩ := hzorn S leSub hpoSub hne.to_subtype fun C ⟨hCne, hCtot⟩ => by
      have hCchain : IsGarlingChain S le (Subtype.val '' C) := by
        refine ⟨?_, hCne.image Subtype.val, ?_⟩
        · rintro _ ⟨a, _, rfl⟩
          exact a.2
        · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
          exact hCtot a ha b hb
      obtain ⟨x, hxS, hxub⟩ := hchains (Subtype.val '' C) hCchain
      exact ⟨⟨x, hxS⟩, fun a ha => hxub a.1 ⟨a, ha, rfl⟩⟩
    exact ⟨m.1, m.2, fun y hyS hmy => congrArg Subtype.val (hm ⟨y, hyS⟩ hmy)⟩
  · intro hzornSet S le hpo hne hchains
    have hpo_univ : IsGarlingPartialOrder (Set.univ : Set S) le :=
      ⟨fun x _ => hpo.refl x,
       fun _ _ _ _ _ _ h1 h2 => hpo.trans h1 h2,
       fun _ _ _ _ h1 h2 => hpo.antisymm h1 h2⟩
    obtain ⟨m, _, hm⟩ :=
      hzornSet S Set.univ le hpo_univ (@Set.univ_nonempty S hne) fun C ⟨_, hCne, hCtot⟩ =>
        let ⟨x, hx⟩ := hchains C ⟨hCne, hCtot⟩
        ⟨x, trivial, hx⟩
    exact ⟨m, fun y hmy => hm y trivial hmy⟩

/-! ## §2.3 The existence of a basis (printed pp. 15–17, PDF pp. 23–25) -/

/-- **Theorem 2.1** (§2.3, p. 16): Suppose that `A` is a subset of a vector space `V` over `K`
which spans `V` and that `C` is a linearly independent subset of `A` (`C` may be empty). There
exists a basis `B` of `V` with `C ⊆ B ⊆ A`.

Proved following Garling's printed Zorn's-lemma argument on p. 16 (`S` = subsets of `A` containing
`C` that are linearly independent, ordered by inclusion). -/
theorem theorem_2_1 {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {A C : Set V} (hAspan : Spans K V A) (hCA : C ⊆ A) (hCind : IsLinearlyIndependent K C) :
    ∃ B : Set V, C ⊆ B ∧ B ⊆ A ∧ IsBasis K V B := by
  classical
  let S : Set (Set V) := {D : Set V | D ⊆ A ∧ C ⊆ D ∧ IsLinearlyIndependent K D}
  have hCS : C ∈ S := ⟨hCA, Set.Subset.refl C, hCind⟩
  have hpo : IsGarlingPartialOrder S (· ⊆ ·) := inclusion_isGarlingPartialOrder S
  have hchains : ∀ T : Set (Set V), IsGarlingChain S (· ⊆ ·) T →
      ∃ E : Set V, IsGarlingUpperBound S (· ⊆ ·) T E := by
    rintro T ⟨hTS, ⟨D₀, hD₀T⟩, hTtot⟩
    let E : Set V := ⋃₀ T
    refine ⟨E, ⟨?_, ?_, ?_⟩, fun D hDT => Set.subset_sUnion_of_mem hDT⟩
    · exact Set.sUnion_subset fun D hDT => (hTS hDT).1
    · exact (hTS hD₀T).2.1.trans (Set.subset_sUnion_of_mem hD₀T)
    · -- Garling's finite-subset chain argument: any finite `x₁, ..., x_k` in `E` lie in a single
      -- `D_j ∈ T`, which is linearly independent.
      rintro ⟨k, x, c, hx_inj, hx_mem, hnz, hsum⟩
      have hex_sub : ∀ F : Finset (Fin k), ∃ D ∈ T, ∀ i ∈ F, x i ∈ D := by
        intro F
        refine Finset.induction_on F ⟨D₀, hD₀T, by simp⟩ ?_
        intro i F' _ ⟨D₁, hD₁T, hD₁⟩
        obtain ⟨D₂, hD₂T, hxD₂⟩ := hx_mem i
        rcases hTtot D₁ hD₁T D₂ hD₂T with h12 | h21
        · refine ⟨D₂, hD₂T, fun j hj => ?_⟩
          rcases Finset.mem_insert.mp hj with rfl | hj'
          · exact hxD₂
          · exact h12 (hD₁ j hj')
        · refine ⟨D₁, hD₁T, fun j hj => ?_⟩
          rcases Finset.mem_insert.mp hj with rfl | hj'
          · exact h21 hxD₂
          · exact hD₁ j hj'
      obtain ⟨D_j, hDjT, hxDj⟩ := hex_sub Finset.univ
      exact (hTS hDjT).2.2 ⟨k, x, c, hx_inj, fun i => hxDj i (Finset.mem_univ i), hnz, hsum⟩
  obtain ⟨B, ⟨hBA, hCB, hBind⟩, hBmax⟩ := zorn_lemma_set hpo ⟨C, hCS⟩ hchains
  refine ⟨B, hCB, hBA, hBind, ?_⟩
  -- Garling's maximality argument: `A ⊆ span(B)`, else `B₀ = {a} ∪ B ∈ S` strictly contains `B`.
  rw [Spans, eq_top_iff, ← hAspan, Submodule.span_le]
  intro a haA
  by_contra ha_nspan
  have ha_notB : a ∉ B := fun haB => ha_nspan (Submodule.subset_span haB)
  let B₀ : Set V := insert a B
  have hB₀_ind : IsLinearlyIndependent K B₀ := by
    rw [isLinearlyIndependent_iff, linearIndepOn_id_insert ha_notB]
    exact ⟨(isLinearlyIndependent_iff B).mp hBind, ha_nspan⟩
  have hB₀S : B₀ ∈ S :=
    ⟨Set.insert_subset haA hBA, hCB.trans (Set.subset_insert a B), hB₀_ind⟩
  have hBB₀ : B = B₀ := hBmax B₀ hB₀S (Set.subset_insert a B)
  have haB : a ∈ B := by
    rw [hBB₀]
    exact Set.mem_insert a B
  exact ha_notB haB

/-- Immediate consequence noted after Theorem 2.1 (§2.3, p. 16): Taking `A = V` (`Set.univ`) and
`C = ∅`, every vector space over `K` has a basis. -/
theorem exists_basis (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V] :
    ∃ B : Set V, IsBasis K V B := by
  have hspan : Spans K V (Set.univ : Set V) := by
    simp [Spans]
  obtain ⟨B, _, _, hB⟩ :=
    theorem_2_1 hspan (Set.empty_subset Set.univ) (empty_isLinearlyIndependent K)
  exact ⟨B, hB⟩

/-! ### Exercise 2.1 (printed pp. 16–17, PDF pp. 24–25) -/

/-- Garling's partial-choice poset element `(B, (c_β)_{β ∈ B})` from the Hint to Exercise 2.1
(§2.3, pp. 16–17): a subset `B ⊆ A` together with a choice `c_β ∈ E_β` for each `β ∈ B`. -/
structure Ex21PartialChoice {A : Type u} {X : Type v} (E : A → Set X) where
  dom : Set A
  choice : ∀ β : A, β ∈ dom → {x : X // x ∈ E β}

namespace Ex21PartialChoice

/-- Partial order on `Ex21PartialChoice E` (§2.3, p. 17): `(B, c) ≤ (C, c')` iff `B ⊆ C` and
`c_β = c'_β` for every `β ∈ B`. -/
def Le {A : Type u} {X : Type v} {E : A → Set X}
    (p q : Ex21PartialChoice E) : Prop :=
  ∃ h : p.dom ⊆ q.dom, ∀ (β : A) (hβ : β ∈ p.dom), p.choice β hβ = q.choice β (h hβ)

@[ext (iff := false)]
theorem ext {A : Type u} {X : Type v} {E : A → Set X}
    {p q : Ex21PartialChoice E} (hdom : p.dom = q.dom)
    (hch : ∀ (β : A) (hβ : β ∈ p.dom), p.choice β hβ = q.choice β (hdom ▸ hβ)) :
    p = q := by
  cases p with
  | mk dom₁ ch₁ =>
    cases q with
    | mk dom₂ ch₂ =>
      simp only at hdom hch
      subst hdom
      congr
      funext β hβ
      exact hch β hβ

theorem isGarlingPartialOrderType {A : Type u} {X : Type v} (E : A → Set X) :
    IsGarlingPartialOrderType (Ex21PartialChoice E) Le where
  refl p := ⟨Set.Subset.refl p.dom, fun _ _ => rfl⟩
  trans := by
    rintro p q r ⟨hpq, hch1⟩ ⟨hqr, hch2⟩
    exact ⟨hpq.trans hqr, fun β hβ => (hch1 β hβ).trans (hch2 β (hpq hβ))⟩
  antisymm := by
    rintro p q ⟨hpq, hch1⟩ ⟨hqp, _⟩
    have hdom : p.dom = q.dom := Set.Subset.antisymm hpq hqp
    exact ext hdom fun β hβ => hch1 β hβ

/-- The empty partial choice `(∅, ())` witnesses that `Ex21PartialChoice E` is non-empty. -/
def empty {A : Type u} {X : Type v} (E : A → Set X) : Ex21PartialChoice E where
  dom := ∅
  choice _ h := False.elim h

theorem chain_has_upperBound {A : Type u} {X : Type v} (E : A → Set X)
    (T : Set (Ex21PartialChoice E))
    (hT : IsGarlingChainType (Ex21PartialChoice E) Le T) :
    ∃ ub : Ex21PartialChoice E, IsGarlingUpperBoundType Le T ub := by
  classical
  let D : Set A := {β : A | ∃ p ∈ T, β ∈ p.dom}
  have hex : ∀ β : A, β ∈ D → ∃ p : Ex21PartialChoice E, p ∈ T ∧ β ∈ p.dom := fun _ h => h
  let ub : Ex21PartialChoice E :=
    { dom := D
      choice := fun β hβ =>
        let p := Classical.choose (hex β hβ)
        have hp : p ∈ T ∧ β ∈ p.dom := Classical.choose_spec (hex β hβ)
        p.choice β hp.2 }
  refine ⟨ub, fun q hqT => ?_⟩
  refine ⟨fun β hβ => ⟨q, hqT, hβ⟩, fun β hβ => ?_⟩
  have hβD : β ∈ D := ⟨q, hqT, hβ⟩
  let p := Classical.choose (hex β hβD)
  have hp : p ∈ T ∧ β ∈ p.dom := Classical.choose_spec (hex β hβD)
  change q.choice β hβ = p.choice β hp.2
  rcases hT.2 q hqT p hp.1 with ⟨hqp, hch⟩ | ⟨hpq, hch⟩
  · exact hch β hβ
  · exact (hch β hp.2).symm

end Ex21PartialChoice

/-- **Exercise 2.1** (§2.3, pp. 16–17): The Axiom of Choice is a consequence of Zorn's lemma,
proved by carrying out Garling's partial-choice poset argument on `Ex21PartialChoice E`. -/
theorem exercise_2_1 (hzorn : GarlingZornLemma.{max u v})
    {A : Type u} {X : Type v} (E : A → Set X) (hne : ∀ α : A, (E α).Nonempty) :
    (CartesianProduct E).Nonempty := by
  classical
  obtain ⟨m, hm_max⟩ :=
    hzorn (Ex21PartialChoice E) Ex21PartialChoice.Le
      (Ex21PartialChoice.isGarlingPartialOrderType E)
      ⟨Ex21PartialChoice.empty E⟩
      (Ex21PartialChoice.chain_has_upperBound E)
  have hdom_univ : m.dom = Set.univ := by
    ext α
    simp only [Set.mem_univ, iff_true]
    by_contra hα
    obtain ⟨x₀, hx₀⟩ := hne α
    let m' : Ex21PartialChoice E :=
      { dom := insert α m.dom
        choice := fun β hβ =>
          if h : β ∈ m.dom then m.choice β h
          else ⟨x₀, by
            rcases Set.mem_insert_iff.mp hβ with rfl | hmem
            · exact hx₀
            · exact False.elim (h hmem)⟩ }
    have hle : Ex21PartialChoice.Le m m' :=
      ⟨Set.subset_insert α m.dom, fun β hβ => by simp [m', hβ]⟩
    have heq : m = m' := hm_max m' hle
    have hα_mem : α ∈ m.dom := by
      have : α ∈ m'.dom := Set.mem_insert α m.dom
      rwa [← heq] at this
    exact hα hα_mem
  exact ⟨fun α => (m.choice α (hdom_univ ▸ Set.mem_univ α)).1,
    fun α => (m.choice α (hdom_univ ▸ Set.mem_univ α)).2⟩

/-- Same-universe specialization of **Exercise 2.1**: `GarlingZornLemma` implies
`GarlingAxiomOfChoice` (§2.3, pp. 16–17). -/
theorem exercise_2_1_axiomOfChoice (hzorn : GarlingZornLemma.{u}) :
    GarlingAxiomOfChoice.{u} :=
  fun _ _ E hne => exercise_2_1 hzorn E hne

/-- Dependent indexed-family corollary of **Exercise 2.1** (§2.3, pp. 16–17). -/
theorem exercise_2_1_dep (hzorn : GarlingZornLemma.{u}) :
    GarlingAxiomOfChoiceDep.{u} :=
  garlingAxiomOfChoice_iff_dep.mp (exercise_2_1_axiomOfChoice hzorn)

/-! ### Exercise 2.2 (printed p. 17, PDF p. 25) -/

/-- Garling's definition of a *well-ordering* on a set `S` (§2.3, Exercise 2.2, p. 17):
a total order `≤` on `S` such that every non-empty subset of `S` has a least element. -/
structure IsGarlingWellOrder (S : Type u) (le : S → S → Prop) : Prop extends
    IsGarlingTotalOrder S le where
  exists_least : ∀ A : Set S, A.Nonempty → ∃ m ∈ A, ∀ a ∈ A, le m a

/-- Subset version of Garling's well-ordering on `T ⊆ S` (§2.3, Exercise 2.2, p. 17). -/
structure IsGarlingWellOrderOn {S : Type u} (T : Set S) (le : S → S → Prop) : Prop extends
    IsTotallyOrderedOn T le where
  exists_least : ∀ A : Set S, A ⊆ T → A.Nonempty → ∃ m ∈ A, ∀ a ∈ A, le m a

/-- Every Mathlib `[LinearOrder S] [WellFoundedLT S]` satisfies `IsGarlingWellOrder S (· ≤ ·)`
(§2.3, p. 17). -/
theorem LinearOrder.isGarlingWellOrder (S : Type u) [LinearOrder S] [WellFoundedLT S] :
    IsGarlingWellOrder S (· ≤ ·) where
  refl := le_refl
  trans _ _ _ := le_trans
  antisymm _ _ := le_antisymm
  total := le_total
  exists_least A hAne :=
    let wf : WellFounded (· < · : S → S → Prop) := wellFounded_lt
    ⟨wf.min A hAne,
     wf.min_mem A hAne,
     fun _ ha => not_lt.mp (wf.not_lt_min A ha)⟩

/-- Build a `LinearOrder` from `IsGarlingTotalOrder` (choosing decidability classically). -/
@[reducible]
noncomputable def IsGarlingTotalOrder.toLinearOrder {S : Type u} {le : S → S → Prop}
    (h : IsGarlingTotalOrder S le) : LinearOrder S :=
  letI po : PartialOrder S := h.toIsGarlingPartialOrderType.toPartialOrder
  { po with
    le_total := h.total
    toDecidableLE := fun x y => Classical.propDecidable (le x y) }

/-- Under `IsGarlingWellOrder.toLinearOrder`, `WellFoundedLT S` holds. -/
theorem IsGarlingWellOrder.wellFoundedLT {S : Type u} {le : S → S → Prop}
    (h : IsGarlingWellOrder S le) :
    @WellFoundedLT S h.toIsGarlingTotalOrder.toLinearOrder.toLT := by
  let lo : LinearOrder S := h.toIsGarlingTotalOrder.toLinearOrder
  refine @WellFounded.intro S lo.lt fun x => ?_
  by_contra hnot
  let Bad : Set S := {y : S | ¬ Acc lo.lt y}
  obtain ⟨m, hmBad, hm_least⟩ := h.exists_least Bad ⟨x, hnot⟩
  apply hmBad
  refine Acc.intro m fun y hym => ?_
  by_contra hyBad
  have hmy : le m y := hm_least y hyBad
  exact (@not_le_of_gt S lo.toPreorder y m hym) hmy

/-- Garling's poset of well-ordered subsets `(T, ≤)` of `S` from the Hint to Exercise 2.2
(§2.3, p. 17). To avoid dependent equality over `T`, `rel` is restricted to `T × T`. -/
structure Ex22WellOrderedSub (S : Type u) where
  carrier : Set S
  rel : S → S → Prop
  rel_mem : ∀ ⦃x y : S⦄, rel x y → x ∈ carrier ∧ y ∈ carrier
  isWellOrder : IsGarlingWellOrderOn carrier rel

namespace Ex22WellOrderedSub

@[ext]
theorem ext {S : Type u} {w₁ w₂ : Ex22WellOrderedSub S}
    (hc : w₁.carrier = w₂.carrier)
    (hr : ∀ x y : S, w₁.rel x y ↔ w₂.rel x y) :
    w₁ = w₂ := by
  cases w₁
  cases w₂
  simp only [mk.injEq] at *
  refine ⟨hc, ?_⟩
  funext x y
  exact propext (hr x y)

/-- Garling's partial order `≺` on `Ex22WellOrderedSub S` (§2.3, p. 17):
1. `T₁ ⊆ T₂`;
2. `≤₁` and `≤₂` coincide on `T₁`;
3. `P_t = {x ∈ T₂ : x ≤₂ t} ⊆ T₁` whenever `t ∈ T₁`. -/
structure Prec {S : Type u} (w₁ w₂ : Ex22WellOrderedSub S) : Prop where
  subset : w₁.carrier ⊆ w₂.carrier
  coincide : ∀ ⦃x y : S⦄, x ∈ w₁.carrier → y ∈ w₁.carrier → (w₁.rel x y ↔ w₂.rel x y)
  initial : ∀ ⦃t : S⦄, t ∈ w₁.carrier → {x ∈ w₂.carrier | w₂.rel x t} ⊆ w₁.carrier

theorem isGarlingPartialOrderType (S : Type u) :
    IsGarlingPartialOrderType (Ex22WellOrderedSub S) Prec where
  refl w :=
    { subset := Set.Subset.refl _
      coincide := fun _ _ _ _ => Iff.rfl
      initial := fun _ _ _ hx => hx.1 }
  trans := by
    intro w₁ w₂ w₃ h12 h23
    refine
      { subset := h12.subset.trans h23.subset
        coincide := fun x y hx hy =>
          (h12.coincide hx hy).trans (h23.coincide (h12.subset hx) (h12.subset hy))
        initial := fun t ht x hx => ?_ }
    have hx2 : x ∈ w₂.carrier := h23.initial (h12.subset ht) hx
    have hxt2 : w₂.rel x t := (h23.coincide hx2 (h12.subset ht)).mpr hx.2
    exact h12.initial ht ⟨hx2, hxt2⟩
  antisymm := by
    intro w₁ w₂ h12 h21
    have hc : w₁.carrier = w₂.carrier := Set.Subset.antisymm h12.subset h21.subset
    refine ext hc fun x y => ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨hx, hy⟩ := w₁.rel_mem h
      exact (h12.coincide hx hy).mp h
    · obtain ⟨hx, hy⟩ := w₂.rel_mem h
      rw [← hc] at hx hy
      exact (h12.coincide hx hy).mpr h

/-- Empty well-ordered subset `(∅, False)`, witnessing non-emptiness of `Ex22WellOrderedSub S`. -/
def empty (S : Type u) : Ex22WellOrderedSub S where
  carrier := ∅
  rel _ _ := False
  rel_mem {_ _} h := False.elim h
  isWellOrder :=
    { refl := by simp
      trans := by simp
      antisymm := by simp
      total := by simp
      exists_least := fun A hA ⟨x, hx⟩ => False.elim (hA hx) }

/-- Key initial-segment lemma along a chain `C` in `Ex22WellOrderedSub S`: if `w ∈ C`,
`t ∈ w.carrier`, and `(∃ w' ∈ C, w'.rel x t)`, then `x ∈ w.carrier ∧ w.rel x t`. -/
private theorem mem_and_rel_of_chain {S : Type u}
    {C : Set (Ex22WellOrderedSub S)}
    (hC : IsGarlingChainType (Ex22WellOrderedSub S) Prec C)
    {w : Ex22WellOrderedSub S} (hw : w ∈ C) {x t : S} (ht : t ∈ w.carrier)
    (hrel : ∃ w' ∈ C, w'.rel x t) :
    x ∈ w.carrier ∧ w.rel x t := by
  obtain ⟨w', hw'C, hxt'⟩ := hrel
  obtain ⟨hx', ht'⟩ := w'.rel_mem hxt'
  rcases hC.2 w hw w' hw'C with hww' | hw'w
  · have hx_mem : x ∈ w.carrier := hww'.initial ht ⟨hx', hxt'⟩
    exact ⟨hx_mem, (hww'.coincide hx_mem ht).mpr hxt'⟩
  · exact ⟨hw'w.subset hx', (hw'w.coincide hx' ht').mp hxt'⟩

theorem chain_has_upperBound (S : Type u)
    (C : Set (Ex22WellOrderedSub S))
    (hC : IsGarlingChainType (Ex22WellOrderedSub S) Prec C) :
    ∃ ub : Ex22WellOrderedSub S, IsGarlingUpperBoundType Prec C ub := by
  let T : Set S := {x : S | ∃ w ∈ C, x ∈ w.carrier}
  let R : S → S → Prop := fun x y => ∃ w ∈ C, w.rel x y
  have hmem : ∀ ⦃x y : S⦄, R x y → x ∈ T ∧ y ∈ T := by
    rintro x y ⟨w, hwC, hxy⟩
    obtain ⟨hx, hy⟩ := w.rel_mem hxy
    exact ⟨⟨w, hwC, hx⟩, ⟨w, hwC, hy⟩⟩
  have htot : IsTotallyOrderedOn T R :=
    { refl := by
        rintro x ⟨w, hwC, hx⟩
        exact ⟨w, hwC, w.isWellOrder.refl x hx⟩
      trans := by
        rintro x y z _ _ ⟨w₃, hw₃C, hz⟩ hxy hyz
        obtain ⟨hy3, hyz3⟩ := mem_and_rel_of_chain hC hw₃C hz hyz
        obtain ⟨hx3, hxy3⟩ := mem_and_rel_of_chain hC hw₃C hy3 hxy
        exact ⟨w₃, hw₃C, w₃.isWellOrder.trans hx3 hy3 hz hxy3 hyz3⟩
      antisymm := by
        rintro x y ⟨w, hwC, hx⟩ _ hxy hyx
        obtain ⟨hy, hyx_w⟩ := mem_and_rel_of_chain hC hwC hx hyx
        obtain ⟨_, hxy_w⟩ := mem_and_rel_of_chain hC hwC hy hxy
        exact w.isWellOrder.antisymm hx hy hxy_w hyx_w
      total := by
        rintro x ⟨w₁, hw₁C, hx⟩ y ⟨w₂, hw₂C, hy⟩
        rcases hC.2 w₁ hw₁C w₂ hw₂C with h12 | h21
        · rcases w₂.isWellOrder.total x (h12.subset hx) y hy with h | h
          · exact Or.inl ⟨w₂, hw₂C, h⟩
          · exact Or.inr ⟨w₂, hw₂C, h⟩
        · rcases w₁.isWellOrder.total x hx y (h21.subset hy) with h | h
          · exact Or.inl ⟨w₁, hw₁C, h⟩
          · exact Or.inr ⟨w₁, hw₁C, h⟩ }
  have hwo : IsGarlingWellOrderOn T R :=
    { toIsTotallyOrderedOn := htot
      exists_least := by
        intro A hAT ⟨a₀, ha₀A⟩
        obtain ⟨w₀, hw₀C, ha₀w₀⟩ := hAT ha₀A
        have hsub : A ∩ w₀.carrier ⊆ w₀.carrier := Set.inter_subset_right
        have hne : (A ∩ w₀.carrier).Nonempty := ⟨a₀, ha₀A, ha₀w₀⟩
        obtain ⟨m, ⟨hmA, hmw₀⟩, hm_least⟩ := w₀.isWellOrder.exists_least (A ∩ w₀.carrier) hsub hne
        refine ⟨m, hmA, fun a haA => ?_⟩
        rcases htot.total m (hAT hmA) a (hAT haA) with hma | ham
        · exact hma
        · obtain ⟨haw₀, _⟩ := mem_and_rel_of_chain hC hw₀C hmw₀ ham
          exact ⟨w₀, hw₀C, hm_least a ⟨haA, haw₀⟩⟩ }
  let ub : Ex22WellOrderedSub S :=
    { carrier := T
      rel := R
      rel_mem := hmem
      isWellOrder := hwo }
  refine ⟨ub, fun w hwC => ?_⟩
  refine
    { subset := fun x hx => ⟨w, hwC, hx⟩
      coincide := fun x y hx hy =>
        ⟨fun h => ⟨w, hwC, h⟩, fun h => (mem_and_rel_of_chain hC hwC hy h).2⟩
      initial := fun t ht x hx => (mem_and_rel_of_chain hC hwC ht hx.2).1 }

/-- Adjoining a new top element `s ∉ w.carrier` strictly above `w.carrier` yields an element
`w' ∈ Ex22WellOrderedSub S` with `Prec w w'` and `s ∈ w'.carrier` (§2.3, p. 17). -/
def insertTop {S : Type u} (w : Ex22WellOrderedSub S) (s : S) (hs : s ∉ w.carrier) :
    Ex22WellOrderedSub S :=
  let T' : Set S := insert s w.carrier
  let R' : S → S → Prop := fun x y => w.rel x y ∨ (x ∈ T' ∧ y = s)
  { carrier := T'
    rel := R'
    rel_mem := by
      rintro x y (hxy | ⟨hxT', hy_eq⟩)
      · obtain ⟨hx, hy⟩ := w.rel_mem hxy
        exact ⟨Set.mem_insert_of_mem s hx, Set.mem_insert_of_mem s hy⟩
      · exact ⟨hxT', hy_eq ▸ Set.mem_insert s w.carrier⟩
    isWellOrder :=
      { refl := by
          intro x hx
          rcases Set.mem_insert_iff.mp hx with hx_eq | hxw
          · exact Or.inr ⟨hx, hx_eq⟩
          · exact Or.inl (w.isWellOrder.refl x hxw)
        trans := by
          rintro x y z hx _ _ (hxy | ⟨_, hy_eq⟩) (hyz | ⟨_, hz_eq⟩)
          · obtain ⟨hxw, hyw⟩ := w.rel_mem hxy
            obtain ⟨_, hzw⟩ := w.rel_mem hyz
            exact Or.inl (w.isWellOrder.trans hxw hyw hzw hxy hyz)
          · exact Or.inr ⟨hx, hz_eq⟩
          · obtain ⟨hyw, _⟩ := w.rel_mem hyz
            exact False.elim (hs (hy_eq ▸ hyw))
          · exact Or.inr ⟨hx, hz_eq⟩
        antisymm := by
          rintro x y _ _ (hxy | ⟨_, hy_eq⟩) (hyx | ⟨_, hx_eq⟩)
          · obtain ⟨hxw, hyw⟩ := w.rel_mem hxy
            exact w.isWellOrder.antisymm hxw hyw hxy hyx
          · obtain ⟨hxw, _⟩ := w.rel_mem hxy
            exact False.elim (hs (hx_eq ▸ hxw))
          · obtain ⟨hyw, _⟩ := w.rel_mem hyx
            exact False.elim (hs (hy_eq ▸ hyw))
          · exact hx_eq.trans hy_eq.symm
        total := by
          intro x hx y hy
          rcases Set.mem_insert_iff.mp hx with hx_eq | hxw
          · exact Or.inr (Or.inr ⟨hy, hx_eq⟩)
          · rcases Set.mem_insert_iff.mp hy with hy_eq | hyw
            · exact Or.inl (Or.inr ⟨hx, hy_eq⟩)
            · rcases w.isWellOrder.total x hxw y hyw with h | h
              · exact Or.inl (Or.inl h)
              · exact Or.inr (Or.inl h)
        exists_least := by
          intro A hAT' ⟨a₀, ha₀A⟩
          by_cases hAw : (A ∩ w.carrier).Nonempty
          · obtain ⟨m, ⟨hmA, hmw⟩, hm_least⟩ :=
              w.isWellOrder.exists_least (A ∩ w.carrier) Set.inter_subset_right hAw
            refine ⟨m, hmA, fun a haA => ?_⟩
            rcases Set.mem_insert_iff.mp (hAT' haA) with ha_eq | haw
            · exact Or.inr ⟨Set.mem_insert_of_mem s hmw, ha_eq⟩
            · exact Or.inl (hm_least a ⟨haA, haw⟩)
          · refine ⟨s, ?_, fun a haA => ?_⟩
            · rcases Set.mem_insert_iff.mp (hAT' ha₀A) with ha₀_eq | ha₀w
              · exact ha₀_eq ▸ ha₀A
              · exact False.elim (hAw ⟨a₀, ha₀A, ha₀w⟩)
            · rcases Set.mem_insert_iff.mp (hAT' haA) with ha_eq | haw
              · exact Or.inr ⟨Set.mem_insert s w.carrier, ha_eq⟩
              · exact False.elim (hAw ⟨a, haA, haw⟩) } }

theorem prec_insertTop {S : Type u} (w : Ex22WellOrderedSub S) (s : S) (hs : s ∉ w.carrier) :
    Prec w (insertTop w s hs) where
  subset := Set.subset_insert s w.carrier
  coincide x y hx hy := by
    have hys : y ≠ s := fun h => hs (h ▸ hy)
    simp [insertTop, hys]
  initial t ht x hx := by
    have hts : t ≠ s := fun h => hs (h ▸ ht)
    rcases hx.2 with hxt | ⟨_, hts'⟩
    · exact (w.rel_mem hxt).1
    · exact False.elim (hts hts')

end Ex22WellOrderedSub

/-- **Exercise 2.2** (§2.3, p. 17): Assuming Zorn's lemma, every non-empty set `S` can be given a
well-ordering, proved via Garling's initial-segment poset `(Ex22WellOrderedSub S, Prec)`. -/
theorem exercise_2_2 (hzorn : GarlingZornLemma.{u}) (S : Type u) (_hS : Nonempty S) :
    ∃ le : S → S → Prop, IsGarlingWellOrder S le := by
  classical
  obtain ⟨m, hm_max⟩ :=
    hzorn (Ex22WellOrderedSub S) Ex22WellOrderedSub.Prec
      (Ex22WellOrderedSub.isGarlingPartialOrderType S)
      ⟨Ex22WellOrderedSub.empty S⟩
      (Ex22WellOrderedSub.chain_has_upperBound S)
  have hc_univ : m.carrier = Set.univ := by
    ext s
    simp only [Set.mem_univ, iff_true]
    by_contra hs
    have heq : m = Ex22WellOrderedSub.insertTop m s hs :=
      hm_max _ (Ex22WellOrderedSub.prec_insertTop m s hs)
    have hs_mem : s ∈ m.carrier := by
      have : s ∈ (Ex22WellOrderedSub.insertTop m s hs).carrier := Set.mem_insert s m.carrier
      rwa [← heq] at this
    exact hs hs_mem
  refine ⟨m.rel,
    { refl := fun x => m.isWellOrder.refl x (hc_univ ▸ Set.mem_univ x)
      trans := fun x y z =>
        m.isWellOrder.trans (hc_univ ▸ Set.mem_univ x) (hc_univ ▸ Set.mem_univ y)
          (hc_univ ▸ Set.mem_univ z)
      antisymm := fun x y =>
        m.isWellOrder.antisymm (hc_univ ▸ Set.mem_univ x) (hc_univ ▸ Set.mem_univ y)
      total := fun x y =>
        m.isWellOrder.total x (hc_univ ▸ Set.mem_univ x) y (hc_univ ▸ Set.mem_univ y)
      exists_least := fun A hAne =>
        m.isWellOrder.exists_least A (hc_univ ▸ Set.subset_univ A) hAne }⟩

/-- Subset-level counterpart of **Exercise 2.2** (§2.3, p. 17): assuming Zorn's lemma, every
non-empty subset `S : Set X` can be given a well-ordering. -/
theorem exercise_2_2_set (hzorn : GarlingZornLemma.{u}) {X : Type u} (S : Set X) (hS : S.Nonempty) :
    ∃ le : X → X → Prop, IsGarlingWellOrderOn S le := by
  obtain ⟨leSub, hwo⟩ := exercise_2_2 hzorn S hS.to_subtype
  refine ⟨fun x y => ∃ (hx : x ∈ S) (hy : y ∈ S), leSub ⟨x, hx⟩ ⟨y, hy⟩,
    { refl := fun x hx => ⟨hx, hx, hwo.refl ⟨x, hx⟩⟩
      trans := fun _ _ _ _ _ _ ⟨hx, hy, h1⟩ ⟨_, hz, h2⟩ => ⟨hx, hz, hwo.trans h1 h2⟩
      antisymm := fun _ _ _ _ ⟨_, _, h1⟩ ⟨_, _, h2⟩ =>
        congrArg Subtype.val (hwo.antisymm h1 h2)
      total := fun x hx y hy =>
        (hwo.total ⟨x, hx⟩ ⟨y, hy⟩).imp (fun h => ⟨hx, hy, h⟩) (fun h => ⟨hy, hx, h⟩)
      exists_least := fun A hAS ⟨a₀, ha₀A⟩ => by
        let A' : Set S := {s : S | s.1 ∈ A}
        obtain ⟨m, hmA', hm_least⟩ := hwo.exists_least A' ⟨⟨a₀, hAS ha₀A⟩, ha₀A⟩
        exact ⟨m.1, hmA', fun a haA => ⟨m.2, hAS haA, hm_least ⟨a, hAS haA⟩ haA⟩⟩ }⟩

/-- Unconditional Well-Ordering Theorem deduced by combining `garlingZornLemma_holds` and
`exercise_2_2` (§2.3, p. 17). -/
theorem every_nonempty_set_has_wellOrdering (S : Type u) (hS : Nonempty S) :
    ∃ le : S → S → Prop, IsGarlingWellOrder S le :=
  exercise_2_2 garlingZornLemma_holds S hS

/-! ### Exercise 2.3 (printed p. 17, PDF p. 25 — `QUEUE.md` fidelity hold) -/

/-- Strict order `<` induced by a partial/well-ordering `≤`: `x < y` iff `x ≤ y ∧ ¬ y ≤ x`
(equivalently `x ≤ y ∧ x ≠ y`, see `garlingStrictLt_iff`; §2.3, p. 17). -/
def garlingStrictLt {A : Type u} (le : A → A → Prop) (x y : A) : Prop :=
  le x y ∧ ¬ le y x

theorem garlingStrictLt_iff {A : Type u} {le : A → A → Prop}
    (hpo : IsGarlingPartialOrderType A le) (x y : A) :
    garlingStrictLt le x y ↔ le x y ∧ x ≠ y :=
  ⟨fun ⟨hxy, hnyx⟩ => ⟨hxy, fun h => hnyx (h ▸ hpo.refl x)⟩,
   fun ⟨hxy, hne⟩ => ⟨hxy, fun hyx => hne (hpo.antisymm hxy hyx)⟩⟩

/-- Helper: in any well-ordered set `(A, ≤)`, for any predicate `P : A → Prop`, there exists a
unique `a : A` such that `P a` and `∀ b < a, ¬ P b` if and only if `∃ a : A, P a`. -/
private theorem existsUnique_first_iff_exists {A : Type u} [LinearOrder A] [WellFoundedLT A]
    (P : A → Prop) :
    (∃! a : A, P a ∧ ∀ b : A, b < a → ¬ P b) ↔ ∃ a : A, P a := by
  constructor
  · rintro ⟨a, ⟨hPa, _⟩, _⟩
    exact ⟨a, hPa⟩
  · intro hex
    let wf : WellFounded (· < · : A → A → Prop) := wellFounded_lt
    let S : Set A := {x : A | P x}
    let a₀ : A := wf.min S hex
    have ha₀P : P a₀ := wf.min_mem S hex
    have ha₀_min : ∀ b : A, b < a₀ → ¬ P b := fun b hb hPb => wf.not_lt_min S hPb hb
    refine ⟨a₀, ⟨ha₀P, ha₀_min⟩, fun a' ⟨hPa', ha'_min⟩ => ?_⟩
    rcases lt_trichotomy a' a₀ with hlt | heq | hgt
    · exact False.elim (ha₀_min a' hlt hPa')
    · exact heq
    · exact False.elim (ha'_min a₀ hgt ha₀P)

/-- **Counterexample to Exercise 2.3, Part 1** (`QUEUE.md` fidelity hold, §2.3, p. 17):
`(ℕ, ≤)` (order type `ω`) is an infinite well-ordered set, yet `{x ∈ ℕ : x < a}` is finite for
every `a ∈ ℕ`, so neither `∃ a : ℕ, ({x : ℕ | x < a}).Infinite` nor the printed `∃! a` conclusion
holds. -/
theorem exercise_2_3_infinite_counterexample :
    Infinite ℕ ∧ IsGarlingWellOrder ℕ (· ≤ ·) ∧
      (¬ ∃ a : ℕ, ({x : ℕ | x < a}).Infinite) ∧
      ¬ ∃! a : ℕ, ({x : ℕ | x < a}).Infinite ∧ ∀ b : ℕ, b < a → ({x : ℕ | x < b}).Finite := by
  have hno : ¬ ∃ a : ℕ, ({x : ℕ | x < a}).Infinite := by
    rintro ⟨a, ha_inf⟩
    have hfin : ({x : ℕ | x < a}).Finite :=
      (Finset.range a).finite_toSet.subset fun x hx => Finset.mem_coe.mpr (Finset.mem_range.mpr hx)
    exact ha_inf hfin
  refine ⟨inferInstance, LinearOrder.isGarlingWellOrder ℕ, hno, ?_⟩
  rintro ⟨a, ⟨ha_inf, _⟩, _⟩
  exact hno ⟨a, ha_inf⟩

/-- The type `ω₁` of countable ordinals (`(ℵ₁).ord.ToType`), used as the counterexample to the
second part of Exercise 2.3 (§2.3, p. 17). -/
abbrev Omega1 : Type := (Cardinal.aleph.{0} 1).ord.ToType

/-- **Counterexample to Exercise 2.3, Part 2** (`QUEUE.md` fidelity hold, §2.3, p. 17):
`Omega1` (`ω₁`) is an uncountable well-ordered set, yet `{x ∈ Omega1 : x < c}` is countable for
every `c ∈ Omega1`, so neither `∃ c : Omega1, ¬ ({x : Omega1 | x < c}).Countable` nor the printed
`∃! c` conclusion holds. -/
theorem exercise_2_3_uncountable_counterexample :
    ¬ Countable Omega1 ∧ IsGarlingWellOrder Omega1 (· ≤ ·) ∧
      (¬ ∃ c : Omega1, ¬ ({x : Omega1 | x < c}).Countable) ∧
      ¬ ∃! c : Omega1, ¬ ({x : Omega1 | x < c}).Countable ∧
        ∀ d : Omega1, d < c → ({x : Omega1 | x < d}).Countable := by
  have hunc : ¬ Countable Omega1 := by
    intro hcount
    have hle : Cardinal.mk Omega1 ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr hcount
    have heq : Cardinal.mk Omega1 = Cardinal.aleph 1 :=
      Cardinal.mk_ord_toType (Cardinal.aleph.{0} 1)
    rw [heq] at hle
    exact not_lt_of_ge hle Cardinal.aleph0_lt_aleph_one
  have hno : ¬ ∃ c : Omega1, ¬ ({x : Omega1 | x < c}).Countable := by
    rintro ⟨c, hnot_count⟩
    apply hnot_count
    have hlt : Cardinal.mk (Set.Iio c) < Cardinal.mk Omega1 :=
      Cardinal.mk_Iio_lt c (by simp)
    have heq : Cardinal.mk Omega1 = Cardinal.aleph 1 :=
      Cardinal.mk_ord_toType (Cardinal.aleph.{0} 1)
    rw [heq, Cardinal.lt_aleph_one_iff] at hlt
    exact Cardinal.le_aleph0_iff_set_countable.mp hlt
  refine ⟨hunc, LinearOrder.isGarlingWellOrder Omega1, hno, ?_⟩
  rintro ⟨c, ⟨hc_unc, _⟩, _⟩
  exact hno ⟨c, hc_unc⟩

/-- **Exercise 2.3, Part 1 (exact characterization)** (§2.3, p. 17):
In a well-ordered set `(A, ≤)`, there exists a unique `a ∈ A` such that `{x : x < a}` is infinite
while `{x : x < b}` is finite for each `b < a` if and only if `{x : x < a}` is infinite for at
least one `a ∈ A`. -/
theorem exercise_2_3_infinite_iff {A : Type u} [LinearOrder A] [WellFoundedLT A] :
    (∃! a : A, ({x : A | x < a}).Infinite ∧ ∀ b : A, b < a → ({x : A | x < b}).Finite) ↔
      ∃ a : A, ({x : A | x < a}).Infinite := by
  have h := existsUnique_first_iff_exists (fun a : A => ({x : A | x < a}).Infinite)
  simpa only [Set.not_infinite] using h

/-- **Exercise 2.3, Part 1 (dichotomy for infinite well-ordered sets)** (§2.3, p. 17):
For every infinite well-ordered set `(A, ≤)`, exclusively either every strict initial segment
`{x : x < b}` is finite (in which case `(A, ≤) ≃o (ℕ, ≤)`, see
`exercise_2_3_orderIso_nat_of_forall_Iio_finite`), or there exists a unique `a ∈ A` with
`{x : x < a}` infinite and `{x : x < b}` finite for all `b < a`. -/
theorem exercise_2_3_infinite_dichotomy {A : Type u} [LinearOrder A] [WellFoundedLT A]
    [Infinite A] :
    ((∀ b : A, ({x : A | x < b}).Finite) ∧
      ¬ ∃! a : A, ({x : A | x < a}).Infinite ∧ ∀ b : A, b < a → ({x : A | x < b}).Finite) ∨
    (¬ (∀ b : A, ({x : A | x < b}).Finite) ∧
      ∃! a : A, ({x : A | x < a}).Infinite ∧ ∀ b : A, b < a → ({x : A | x < b}).Finite) := by
  by_cases hall : ∀ b : A, ({x : A | x < b}).Finite
  · refine Or.inl ⟨hall, ?_⟩
    rw [exercise_2_3_infinite_iff]
    rintro ⟨a, ha⟩
    exact ha (hall a)
  · push Not at hall
    exact Or.inr ⟨fun h => let ⟨b, hb⟩ := hall; hb (h b), exercise_2_3_infinite_iff.mpr hall⟩

/-- Every infinite well-ordered set `(A, ≤)` whose strict initial segments `{x : x < b}` are all
finite is order-isomorphic to `(ℕ, ≤)` — showing `(ℕ, ≤)` is up to unique order isomorphism the
only counterexample to Part 1 of Exercise 2.3 (§2.3, p. 17). -/
theorem exercise_2_3_orderIso_nat_of_forall_Iio_finite {A : Type u}
    [LinearOrder A] [WellFoundedLT A] [Infinite A]
    (hall : ∀ b : A, ({x : A | x < b}).Finite) :
    Nonempty (A ≃o ℕ) := by
  classical
  let f : A → ℕ := fun a => (hall a).toFinset.card
  have hf_strict : StrictMono f := by
    intro a₁ a₂ h12
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset] at hx ⊢
      exact lt_trans hx h12
    · intro heq
      have hmem : a₁ ∈ (hall a₂).toFinset := (hall a₂).mem_toFinset.mpr h12
      rw [← heq, Set.Finite.mem_toFinset] at hmem
      exact lt_irrefl a₁ hmem
  have hf_img_Iio : ∀ a : A, Finset.image f (hall a).toFinset = Finset.range (f a) := by
    intro a
    refine Finset.eq_of_subset_of_card_le (fun m hm => ?_) ?_
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
      rw [Finset.mem_range]
      exact hf_strict ((hall a).mem_toFinset.mp hx)
    · rw [Finset.card_range, Finset.card_image_of_injective _ hf_strict.injective]
  have hf_surj : Function.Surjective f := by
    intro n
    have hinf_range : (Set.range f).Infinite := Set.infinite_range_of_injective hf_strict.injective
    have hnot_sub : ¬ Set.range f ⊆ ↑(Finset.range (n + 1)) := fun hsub =>
      hinf_range ((Finset.range (n + 1)).finite_toSet.subset hsub)
    obtain ⟨m, ⟨a, rfl⟩, hm_not⟩ := Set.not_subset.mp hnot_sub
    rw [Finset.mem_coe, Finset.mem_range, not_lt] at hm_not
    have hn_mem : n ∈ Finset.range (f a) := Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self n) hm_not)
    rw [← hf_img_Iio a, Finset.mem_image] at hn_mem
    obtain ⟨x, _, hfx⟩ := hn_mem
    exact ⟨x, hfx⟩
  exact ⟨{ Equiv.ofBijective f ⟨hf_strict.injective, hf_surj⟩ with
    map_rel_iff' := hf_strict.le_iff_le }⟩

/-- **Exercise 2.3, Part 1 (repaired under uncountability)** (§2.3, p. 17):
If `(A, ≤)` is an *uncountable* well-ordered set, then there exists a unique `a ∈ A` such that
`{x : x < a}` is infinite while `{x : x < b}` is finite for each `b < a`. -/
theorem exercise_2_3_infinite_of_uncountable {A : Type u}
    [LinearOrder A] [WellFoundedLT A] (hunc : ¬ Countable A) :
    ∃! a : A, ({x : A | x < a}).Infinite ∧ ∀ b : A, b < a → ({x : A | x < b}).Finite := by
  have : Infinite A := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    exact hunc inferInstance
  rw [exercise_2_3_infinite_iff]
  by_contra hnone
  push Not at hnone
  obtain ⟨e⟩ := exercise_2_3_orderIso_nat_of_forall_Iio_finite hnone
  exact hunc (Countable.of_equiv ℕ e.toEquiv.symm)

/-- **Exercise 2.3, Part 2 (exact characterization)** (§2.3, p. 17):
In a well-ordered set `(A, ≤)`, there exists a unique `c ∈ A` such that `{x : x < c}` is
uncountable while `{x : x < d}` is countable for each `d < c` if and only if `{x : x < c}` is
uncountable for at least one `c ∈ A`. -/
theorem exercise_2_3_uncountable_iff {A : Type u} [LinearOrder A] [WellFoundedLT A] :
    (∃! c : A, ¬ ({x : A | x < c}).Countable ∧ ∀ d : A, d < c → ({x : A | x < d}).Countable) ↔
      ∃ c : A, ¬ ({x : A | x < c}).Countable := by
  simpa [not_not] using
    existsUnique_first_iff_exists (fun c : A => ¬ ({x : A | x < c}).Countable)

/-- **Exercise 2.3, Part 2 (dichotomy for uncountable well-ordered sets)** (§2.3, p. 17):
For every uncountable well-ordered set `(A, ≤)`, exclusively either every strict initial segment
`{x : x < d}` is countable, or there exists a unique `c ∈ A` such that `{x : x < c}` is
uncountable while `{x : x < d}` is countable for each `d < c`. -/
theorem exercise_2_3_uncountable_dichotomy {A : Type u} [LinearOrder A] [WellFoundedLT A]
    (_hunc : ¬ Countable A) :
    ((∀ d : A, ({x : A | x < d}).Countable) ∧
      ¬ ∃! c : A, ¬ ({x : A | x < c}).Countable ∧
        ∀ d : A, d < c → ({x : A | x < d}).Countable) ∨
    (¬ (∀ d : A, ({x : A | x < d}).Countable) ∧
      ∃! c : A, ¬ ({x : A | x < c}).Countable ∧
        ∀ d : A, d < c → ({x : A | x < d}).Countable) := by
  by_cases hall : ∀ d : A, ({x : A | x < d}).Countable
  · refine Or.inl ⟨hall, ?_⟩
    rw [exercise_2_3_uncountable_iff]
    rintro ⟨c, hc⟩
    exact hc (hall c)
  · push Not at hall
    exact Or.inr ⟨fun h => let ⟨d, hd⟩ := hall; hd (h d), exercise_2_3_uncountable_iff.mpr hall⟩

/-- **Exercise 2.3, Part 2 (repaired under `ℵ₁ < |A|`)** (§2.3, p. 17):
If `(A, ≤)` is a well-ordered set of cardinality strictly greater than `ℵ₁`, then there exists a
unique `c ∈ A` such that `{x : x < c}` is uncountable while `{x : x < d}` is countable for each
`d < c`. -/
theorem exercise_2_3_uncountable_of_aleph1_lt {A : Type u}
    [LinearOrder A] [WellFoundedLT A] (hcard : Cardinal.aleph.{u} 1 < Cardinal.mk A) :
    ∃! c : A, ¬ ({x : A | x < c}).Countable ∧ ∀ d : A, d < c → ({x : A | x < d}).Countable := by
  rw [exercise_2_3_uncountable_iff]
  let r : A → A → Prop := (· < ·)
  have hlt_ord : Ordinal.omega.{u} 1 < Ordinal.type r := by
    refine lt_of_not_ge fun hle => ?_
    have hcle : (Ordinal.type r).card ≤ (Ordinal.omega.{u} 1).card := Ordinal.card_le_card hle
    rw [Ordinal.card_type, Ordinal.card_omega] at hcle
    exact not_lt_of_ge hcle hcard
  obtain ⟨c, hc⟩ := Ordinal.typein_surj r hlt_ord
  refine ⟨c, fun hcount => ?_⟩
  have hle : Cardinal.mk (Set.Iio c) ≤ Cardinal.aleph0 :=
    Cardinal.le_aleph0_iff_set_countable.mpr hcount
  have hc_card : Cardinal.mk (Set.Iio c) = Cardinal.aleph.{u} 1 := by
    have h1 : (Ordinal.typein r c).card = Cardinal.mk {y : A // r y c} := Ordinal.card_typein c
    rw [hc, Ordinal.card_omega] at h1
    exact h1.symm
  rw [hc_card] at hle
  exact not_lt_of_ge hle Cardinal.aleph0_lt_aleph_one

/-- Raw `IsGarlingWellOrder` counterpart of `exercise_2_3_infinite_iff` (§2.3, p. 17). -/
theorem exercise_2_3_infinite_iff_raw {A : Type u} {le : A → A → Prop}
    (hA : IsGarlingWellOrder A le) :
    (∃! a : A, ({x : A | garlingStrictLt le x a}).Infinite ∧
        ∀ b : A, garlingStrictLt le b a → ({x : A | garlingStrictLt le x b}).Finite) ↔
      ∃ a : A, ({x : A | garlingStrictLt le x a}).Infinite :=
  @exercise_2_3_infinite_iff A hA.toIsGarlingTotalOrder.toLinearOrder hA.wellFoundedLT

/-- Raw `IsGarlingWellOrder` counterpart of `exercise_2_3_uncountable_iff` (§2.3, p. 17). -/
theorem exercise_2_3_uncountable_iff_raw {A : Type u} {le : A → A → Prop}
    (hA : IsGarlingWellOrder A le) :
    (∃! c : A, ¬ ({x : A | garlingStrictLt le x c}).Countable ∧
        ∀ d : A, garlingStrictLt le d c → ({x : A | garlingStrictLt le x d}).Countable) ↔
      ∃ c : A, ¬ ({x : A | garlingStrictLt le x c}).Countable :=
  @exercise_2_3_uncountable_iff A hA.toIsGarlingTotalOrder.toLinearOrder hA.wellFoundedLT

/-! ### Exercise 2.4 (printed p. 17, PDF p. 25) -/

/-- An *order-preserving bijection* `i : X → Y` between preordered sets (§2.3, Exercise 2.4, p. 17):
a bijection such that `x₁ ≤ x₂ → i x₁ ≤ i x₂`. -/
def IsOrderPreservingBijection {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]
    (i : X → Y) : Prop :=
  Function.Bijective i ∧ Monotone i

/-- Raw relation counterpart of an order-preserving bijection (§2.3, Exercise 2.4, p. 17). -/
def IsOrderPreservingBijectionRel {X : Type u} {Y : Type v}
    (leX : X → X → Prop) (leY : Y → Y → Prop) (i : X → Y) : Prop :=
  Function.Bijective i ∧ ∀ x₁ x₂ : X, leX x₁ x₂ → leY (i x₁) (i x₂)

/-- On a linearly ordered domain and partially ordered codomain, every order-preserving bijection
upgrades to an `OrderIso` (`X ≃o Y`). -/
noncomputable def IsOrderPreservingBijection.toOrderIso {X : Type u} {Y : Type v}
    [LinearOrder X] [PartialOrder Y] {i : X → Y} (hi : IsOrderPreservingBijection i) :
    X ≃o Y :=
  { Equiv.ofBijective i hi.1 with
    map_rel_iff' := fun {x₁ x₂} =>
      ⟨fun hle => by
        rcases le_total x₁ x₂ with h12 | h21
        · exact h12
        · have heq : i x₁ = i x₂ := le_antisymm hle (hi.2 h21)
          exact le_of_eq (hi.1.1 heq),
       fun hle => hi.2 hle⟩ }

theorem OrderIso.isOrderPreservingBijection {X : Type u} {Y : Type v}
    [Preorder X] [Preorder Y] (e : X ≃o Y) :
    IsOrderPreservingBijection (e : X → Y) :=
  ⟨e.bijective, e.monotone⟩

/-- On a linearly ordered domain and partially ordered codomain (in particular, between any two
well-ordered sets), one-way order preservation (`x₁ ≤ x₂ → i x₁ ≤ i x₂`) and two-way order
isomorphism (`x₁ ≤ x₂ ↔ i x₁ ≤ i x₂`) coincide for every bijection `i : X → Y` (§2.3, p. 17). -/
theorem isOrderPreservingBijection_iff {X : Type u} {Y : Type v}
    [LinearOrder X] [PartialOrder Y] (i : X → Y) :
    IsOrderPreservingBijection i ↔
      (Function.Bijective i ∧ ∀ x₁ x₂ : X, x₁ ≤ x₂ ↔ i x₁ ≤ i x₂) :=
  ⟨fun hi =>
    let e := hi.toOrderIso
    ⟨hi.1, fun _ _ => e.le_iff_le.symm⟩,
   fun ⟨hbij, hiff⟩ => ⟨hbij, fun _ _ hle => (hiff _ _).mp hle⟩⟩

/-- Fundamental rigidity lemma for well-ordered sets: every strictly increasing map `f : X → X` on
a well-ordered set satisfies `x ≤ f x` for all `x : X` (§2.3, p. 17). -/
theorem wellOrder_le_strictMono_self {X : Type u} [LinearOrder X] [WellFoundedLT X]
    {f : X → X} (hf : StrictMono f) (x : X) :
    x ≤ f x := by
  by_contra hnot
  have hlt : f x < x := not_le.mp hnot
  let wf : WellFounded (· < · : X → X → Prop) := wellFounded_lt
  let S : Set X := {z : X | f z < z}
  have hne : S.Nonempty := ⟨x, hlt⟩
  let m : X := wf.min S hne
  have hm : f m < m := wf.min_mem S hne
  have hfm : f (f m) < f m := hf hm
  exact wf.not_lt_min S hfm hm

/-- No well-ordered set has an order-preserving bijection onto a strict initial segment
`{x : x < a}` of itself (§2.3, p. 17). -/
theorem not_isOrderPreservingBijection_Iio_self {A : Type u} [LinearOrder A] [WellFoundedLT A]
    (a : A) (f : A → Set.Iio a) :
    ¬ IsOrderPreservingBijection f := by
  intro hf
  let e : A ≃o Set.Iio a := hf.toOrderIso
  have hsm : StrictMono (fun x : A => (e x).1) := fun x₁ x₂ h12 => e.lt_iff_lt.mpr h12
  have hle : a ≤ (e a).1 := wellOrder_le_strictMono_self hsm a
  exact not_lt_of_ge hle (e a).2

/-- Two strict initial segments `{x : x < a₁}` and `{x : x < a₂}` of a well-ordered set are
order-isomorphic only when `a₁ = a₂` (§2.3, p. 17). -/
theorem eq_of_isOrderPreservingBijection_Iio {A : Type u} [LinearOrder A] [WellFoundedLT A]
    {a₁ a₂ : A} {f : Set.Iio a₁ → Set.Iio a₂} (hf : IsOrderPreservingBijection f) :
    a₁ = a₂ := by
  let e : Set.Iio a₁ ≃o Set.Iio a₂ := hf.toOrderIso
  rcases lt_trichotomy a₁ a₂ with h12 | heq | h21
  · let g : Set.Iio a₂ → Set.Iio a₂ := fun y => ⟨(e.symm y).1, (e.symm y).2.trans h12⟩
    have hg : StrictMono g := fun y₁ y₂ hy => e.symm.lt_iff_lt.mpr hy
    have hle : (⟨a₁, h12⟩ : Set.Iio a₂) ≤ g ⟨a₁, h12⟩ :=
      wellOrder_le_strictMono_self hg ⟨a₁, h12⟩
    exact False.elim (not_lt_of_ge hle (e.symm ⟨a₁, h12⟩).2)
  · exact heq
  · let g : Set.Iio a₁ → Set.Iio a₁ := fun x => ⟨(e x).1, (e x).2.trans h21⟩
    have hg : StrictMono g := fun x₁ x₂ hx => e.lt_iff_lt.mpr hx
    have hle : (⟨a₂, h21⟩ : Set.Iio a₁) ≤ g ⟨a₂, h21⟩ :=
      wellOrder_le_strictMono_self hg ⟨a₂, h21⟩
    exact False.elim (not_lt_of_ge hle (e ⟨a₂, h21⟩).2)

/-- At most one order-preserving bijection exists between any two well-ordered sets (§2.3, p. 17). -/
theorem unique_isOrderPreservingBijection {X : Type u} {Y : Type v}
    [LinearOrder X] [WellFoundedLT X] [LinearOrder Y] [WellFoundedLT Y]
    {f g : X → Y} (hf : IsOrderPreservingBijection f) (hg : IsOrderPreservingBijection g) :
    f = g := by
  let ef : X ≃o Y := hf.toOrderIso
  let eg : X ≃o Y := hg.toOrderIso
  funext x
  have h1 : x ≤ eg.symm (ef x) :=
    wellOrder_le_strictMono_self (eg.symm.strictMono.comp ef.strictMono) x
  have h2 : x ≤ ef.symm (eg x) :=
    wellOrder_le_strictMono_self (ef.symm.strictMono.comp eg.strictMono) x
  have hgf : g x ≤ f x := by
    have := eg.monotone h1
    simpa [ef, eg, IsOrderPreservingBijection.toOrderIso] using this
  have hfg : f x ≤ g x := by
    have := ef.monotone h2
    simpa [ef, eg, IsOrderPreservingBijection.toOrderIso] using this
  exact le_antisymm hfg hgf

/-- Branch (i) of Exercise 2.4 (§2.3, p. 17): there is a unique order-preserving bijection
`i : A → B`. -/
def Ex24Branch1 (A : Type u) (B : Type v) [Preorder A] [Preorder B] : Prop :=
  ∃! i : A → B, IsOrderPreservingBijection i

/-- Branch (ii) of Exercise 2.4 (§2.3, p. 17): there exists a unique element `a ∈ A` and a unique
order-preserving bijection `i : {x : x < a} → B`. -/
def Ex24Branch2 (A : Type u) (B : Type v) [Preorder A] [Preorder B] : Prop :=
  ∃! p : (a : A) × (Set.Iio a → B), IsOrderPreservingBijection p.2

/-- Branch (iii) of Exercise 2.4 (§2.3, p. 17): there exists a unique element `b ∈ B` and a unique
order-preserving bijection `i : A → {y : y < b}`. -/
def Ex24Branch3 (A : Type u) (B : Type v) [Preorder A] [Preorder B] : Prop :=
  ∃! p : (b : B) × (A → Set.Iio b), IsOrderPreservingBijection p.2

/-- Equivalence between the dependent-pair formulation `Ex24Branch2` and separate uniqueness of
`a ∈ A` and `i : {x : x < a} → B` (§2.3, p. 17). -/
theorem ex24Branch2_iff {A : Type u} {B : Type v}
    [LinearOrder A] [WellFoundedLT A] [LinearOrder B] [WellFoundedLT B] :
    Ex24Branch2 A B ↔
      (∃! a : A, ∃ i : Set.Iio a → B, IsOrderPreservingBijection i) ∧
        ∀ (a : A) (i₁ i₂ : Set.Iio a → B),
          IsOrderPreservingBijection i₁ → IsOrderPreservingBijection i₂ → i₁ = i₂ := by
  constructor
  · rintro ⟨⟨a₀, i₀⟩, hi₀, huniq⟩
    refine ⟨⟨a₀, ⟨i₀, hi₀⟩, fun a' ⟨i', hi'⟩ => ?_⟩,
      fun a i₁ i₂ h₁ h₂ => unique_isOrderPreservingBijection h₁ h₂⟩
    exact congrArg Sigma.fst (huniq ⟨a', i'⟩ hi')
  · rintro ⟨⟨a₀, ⟨i₀, hi₀⟩, ha_uniq⟩, hi_uniq⟩
    refine ⟨⟨a₀, i₀⟩, hi₀, fun ⟨a', i'⟩ hi' => ?_⟩
    have ha : a' = a₀ := ha_uniq a' ⟨i', hi'⟩
    subst ha
    exact congrArg (Sigma.mk a') (hi_uniq a' i' i₀ hi' hi₀)

/-- Equivalence between the dependent-pair formulation `Ex24Branch3` and separate uniqueness of
`b ∈ B` and `i : A → {y : y < b}` (§2.3, p. 17). -/
theorem ex24Branch3_iff {A : Type u} {B : Type v}
    [LinearOrder A] [WellFoundedLT A] [LinearOrder B] [WellFoundedLT B] :
    Ex24Branch3 A B ↔
      (∃! b : B, ∃ i : A → Set.Iio b, IsOrderPreservingBijection i) ∧
        ∀ (b : B) (i₁ i₂ : A → Set.Iio b),
          IsOrderPreservingBijection i₁ → IsOrderPreservingBijection i₂ → i₁ = i₂ := by
  constructor
  · rintro ⟨⟨b₀, i₀⟩, hi₀, huniq⟩
    refine ⟨⟨b₀, ⟨i₀, hi₀⟩, fun b' ⟨i', hi'⟩ => ?_⟩,
      fun b i₁ i₂ h₁ h₂ => unique_isOrderPreservingBijection h₁ h₂⟩
    exact congrArg Sigma.fst (huniq ⟨b', i'⟩ hi')
  · rintro ⟨⟨b₀, ⟨i₀, hi₀⟩, hb_uniq⟩, hi_uniq⟩
    refine ⟨⟨b₀, i₀⟩, hi₀, fun ⟨b', i'⟩ hi' => ?_⟩
    have hb : b' = b₀ := hb_uniq b' ⟨i', hi'⟩
    subst hb
    exact congrArg (Sigma.mk b') (hi_uniq b' i' i₀ hi' hi₀)

private theorem ex24_not_1_and_2 {A : Type u} {B : Type v}
    [LinearOrder A] [WellFoundedLT A] [LinearOrder B] [WellFoundedLT B] :
    Ex24Branch1 A B → ¬ Ex24Branch2 A B := by
  rintro ⟨i, hi, _⟩ ⟨⟨a, j⟩, hj, _⟩
  let e : A ≃o Set.Iio a := hi.toOrderIso.trans hj.toOrderIso.symm
  exact not_isOrderPreservingBijection_Iio_self a e (OrderIso.isOrderPreservingBijection e)

private theorem ex24_not_1_and_3 {A : Type u} {B : Type v}
    [LinearOrder A] [WellFoundedLT A] [LinearOrder B] [WellFoundedLT B] :
    Ex24Branch1 A B → ¬ Ex24Branch3 A B := by
  rintro ⟨i, hi, _⟩ ⟨⟨b, k⟩, hk, _⟩
  let e : B ≃o Set.Iio b := hi.toOrderIso.symm.trans hk.toOrderIso
  exact not_isOrderPreservingBijection_Iio_self b e (OrderIso.isOrderPreservingBijection e)

private theorem ex24_not_2_and_3 {A : Type u} {B : Type v}
    [LinearOrder A] [WellFoundedLT A] [LinearOrder B] [WellFoundedLT B] :
    Ex24Branch2 A B → ¬ Ex24Branch3 A B := by
  rintro ⟨⟨a, j⟩, hj, _⟩ ⟨⟨b, k⟩, hk, _⟩
  let ej : Set.Iio a ≃o B := hj.toOrderIso
  let ek : A ≃o Set.Iio b := hk.toOrderIso
  let f : B → B := fun y => (ek (ej.symm y).1).1
  have hf : StrictMono f := fun y₁ y₂ hy =>
    ek.lt_iff_lt.mpr (ej.symm.lt_iff_lt.mpr hy)
  let y₀ : B := (ek a).1
  have hle : y₀ ≤ f y₀ := wellOrder_le_strictMono_self hf y₀
  have hlt : f y₀ < y₀ := ek.lt_iff_lt.mpr (ej.symm y₀).2
  exact not_lt_of_ge hle hlt

private noncomputable def restrictOrderIsoIio {A : Type u} {B : Type v}
    [LinearOrder A] [LinearOrder B] {a₂ : A} {b₂ : B}
    (e : Set.Iio a₂ ≃o Set.Iio b₂) {a₁ : A} (ha : a₁ < a₂) :
    Set.Iio a₁ ≃o Set.Iio (e ⟨a₁, ha⟩).1 where
  toFun x := ⟨(e ⟨x.1, x.2.trans ha⟩).1, e.lt_iff_lt.mpr x.2⟩
  invFun y :=
    let y' : Set.Iio b₂ := ⟨y.1, y.2.trans (e ⟨a₁, ha⟩).2⟩
    let x' : Set.Iio a₂ := e.symm y'
    ⟨x'.1, by
      have hlt : e x' < e ⟨a₁, ha⟩ := by
        rw [OrderIso.apply_symm_apply]
        exact y.2
      exact e.lt_iff_lt.mp hlt⟩
  left_inv x := by
    apply Subtype.ext
    change (e.symm (e ⟨x.1, x.2.trans ha⟩)).1 = x.1
    rw [OrderIso.symm_apply_apply]
  right_inv y := by
    apply Subtype.ext
    change (e (e.symm ⟨y.1, y.2.trans (e ⟨a₁, ha⟩).2⟩)).1 = y.1
    rw [OrderIso.apply_symm_apply]
  map_rel_iff' := e.le_iff_le

/-- **Exercise 2.4** (§2.3, p. 17): Suppose that `(A, ≤)` and `(B, ≤)` are two well-ordered sets.
Then one and only one of the following occurs:
(i) there is a unique order-preserving bijection `i : A → B`;
(ii) there exists a unique `a ∈ A` and a unique order-preserving bijection `i : {x : x < a} → B`;
(iii) there exists a unique `b ∈ B` and a unique order-preserving bijection `i : A → {y : y < b}`. -/
theorem exercise_2_4 (A : Type u) (B : Type v)
    [LinearOrder A] [WellFoundedLT A] [LinearOrder B] [WellFoundedLT B] :
    (Ex24Branch1 A B ∧ ¬ Ex24Branch2 A B ∧ ¬ Ex24Branch3 A B) ∨
    (¬ Ex24Branch1 A B ∧ Ex24Branch2 A B ∧ ¬ Ex24Branch3 A B) ∨
    (¬ Ex24Branch1 A B ∧ ¬ Ex24Branch2 A B ∧ Ex24Branch3 A B) := by
  classical
  suffices hex : Ex24Branch1 A B ∨ Ex24Branch2 A B ∨ Ex24Branch3 A B by
    rcases hex with h1 | h2 | h3
    · exact Or.inl ⟨h1, ex24_not_1_and_2 h1, ex24_not_1_and_3 h1⟩
    · exact Or.inr (Or.inl ⟨fun h1 => ex24_not_1_and_2 h1 h2, h2, ex24_not_2_and_3 h2⟩)
    · exact Or.inr (Or.inr
        ⟨fun h1 => ex24_not_1_and_3 h1 h3, fun h2 => ex24_not_2_and_3 h2 h3, h3⟩)
  let R : A → B → Prop := fun a b =>
    ∃ i : Set.Iio a → Set.Iio b, IsOrderPreservingBijection i
  have hR_fun : ∀ {a : A} {b₁ b₂ : B}, R a b₁ → R a b₂ → b₁ = b₂ := by
    rintro a b₁ b₂ ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩
    let e : Set.Iio b₁ ≃o Set.Iio b₂ := hi₁.toOrderIso.symm.trans hi₂.toOrderIso
    exact eq_of_isOrderPreservingBijection_Iio (OrderIso.isOrderPreservingBijection e)
  have hR_inj : ∀ {a₁ a₂ : A} {b : B}, R a₁ b → R a₂ b → a₁ = a₂ := by
    rintro a₁ a₂ b ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩
    let e : Set.Iio a₁ ≃o Set.Iio a₂ := hi₁.toOrderIso.trans hi₂.toOrderIso.symm
    exact eq_of_isOrderPreservingBijection_Iio (OrderIso.isOrderPreservingBijection e)
  let DomR : Set A := {a : A | ∃ b : B, R a b}
  let RanR : Set B := {b : B | ∃ a : A, R a b}
  have hDom_down : ∀ {a₁ a₂ : A}, a₂ ∈ DomR → a₁ < a₂ → a₁ ∈ DomR := by
    rintro a₁ a₂ ⟨b₂, i₂, hi₂⟩ ha₁₂
    let e' := restrictOrderIsoIio hi₂.toOrderIso ha₁₂
    exact ⟨(hi₂.toOrderIso ⟨a₁, ha₁₂⟩).1, e', OrderIso.isOrderPreservingBijection e'⟩
  have hRan_down : ∀ {b₁ b₂ : B}, b₂ ∈ RanR → b₁ < b₂ → b₁ ∈ RanR := by
    rintro b₁ b₂ ⟨a₂, i₂, hi₂⟩ hb₁₂
    let e' := restrictOrderIsoIio hi₂.toOrderIso.symm hb₁₂
    exact ⟨(hi₂.toOrderIso.symm ⟨b₁, hb₁₂⟩).1, e'.symm,
      OrderIso.isOrderPreservingBijection e'.symm⟩
  have hR_mono : ∀ {a₁ a₂ : A} {b₁ b₂ : B}, R a₁ b₁ → R a₂ b₂ → a₁ < a₂ → b₁ < b₂ := by
    rintro a₁ a₂ b₁ b₂ hR₁ ⟨i₂, hi₂⟩ ha₁₂
    let e₂ := hi₂.toOrderIso
    let e' := restrictOrderIsoIio e₂ ha₁₂
    have hR₁' : R a₁ (e₂ ⟨a₁, ha₁₂⟩).1 := ⟨e', OrderIso.isOrderPreservingBijection e'⟩
    have hb_eq : b₁ = (e₂ ⟨a₁, ha₁₂⟩).1 := hR_fun hR₁ hR₁'
    rw [hb_eq]
    exact (e₂ ⟨a₁, ha₁₂⟩).2
  -- Construct the canonical order isomorphism `DomR ≃o RanR`.
  let phi : DomR → RanR := fun x =>
    ⟨Classical.choose x.2, x.1, Classical.choose_spec x.2⟩
  have hphi_R : ∀ x : DomR, R x.1 (phi x).1 := fun x => Classical.choose_spec x.2
  have hphi_strict : StrictMono phi := fun x₁ x₂ hx =>
    hR_mono (hphi_R x₁) (hphi_R x₂) hx
  have hphi_surj : Function.Surjective phi := by
    rintro ⟨b, a, hRab⟩
    have ha : a ∈ DomR := ⟨b, hRab⟩
    refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
    exact hR_fun (hphi_R ⟨a, ha⟩) hRab
  let eDomRan : DomR ≃o RanR :=
    { Equiv.ofBijective phi ⟨hphi_strict.injective, hphi_surj⟩ with
      map_rel_iff' := hphi_strict.le_iff_le }
  let eqvUnivA : (Set.univ : Set A) ≃o A :=
    { Equiv.Set.univ A with map_rel_iff' := Iff.rfl }
  let eqvUnivB : (Set.univ : Set B) ≃o B :=
    { Equiv.Set.univ B with map_rel_iff' := Iff.rfl }
  by_cases hDom : DomR = Set.univ
  · by_cases hRan : RanR = Set.univ
    · -- Case (i): `DomR = univ` and `RanR = univ`.
      refine Or.inl ?_
      let eAB : A ≃o B :=
        eqvUnivA.symm.trans ((Set.orderIsoOfEq DomR Set.univ hDom).symm.trans
          (eDomRan.trans ((Set.orderIsoOfEq RanR Set.univ hRan).trans eqvUnivB)))
      exact ⟨eAB, OrderIso.isOrderPreservingBijection eAB,
        fun i' hi' => unique_isOrderPreservingBijection hi'
          (OrderIso.isOrderPreservingBijection eAB)⟩
    · -- Case (iii): `DomR = univ` and `RanR ≠ univ`.
      refine Or.inr (Or.inr ?_)
      have hRan_compl : RanRᶜ.Nonempty := by
        by_contra hne
        apply hRan
        ext y
        simp only [Set.mem_univ, iff_true]
        by_contra hy
        exact hne ⟨y, hy⟩
      let wfB : WellFounded (· < · : B → B → Prop) := wellFounded_lt
      let b₀ : B := wfB.min RanRᶜ hRan_compl
      have hb₀_not : b₀ ∉ RanR := wfB.min_mem RanRᶜ hRan_compl
      have hRan_eq : RanR = Set.Iio b₀ := by
        ext y
        simp only [Set.mem_Iio]
        refine ⟨fun hy => ?_, fun hlt => ?_⟩
        · rcases lt_trichotomy y b₀ with hlt | rfl | hgt
          · exact hlt
          · exact False.elim (hb₀_not hy)
          · exact False.elim (hb₀_not (hRan_down hy hgt))
        · by_contra hy_not
          exact wfB.not_lt_min RanRᶜ hy_not hlt
      let eAIio : A ≃o Set.Iio b₀ :=
        eqvUnivA.symm.trans ((Set.orderIsoOfEq DomR Set.univ hDom).symm.trans
          (eDomRan.trans (Set.orderIsoOfEq RanR (Set.Iio b₀) hRan_eq)))
      rw [ex24Branch3_iff]
      refine ⟨⟨b₀, ⟨eAIio, OrderIso.isOrderPreservingBijection eAIio⟩, fun b' ⟨i', hi'⟩ => ?_⟩,
        fun _ _ _ h₁ h₂ => unique_isOrderPreservingBijection h₁ h₂⟩
      let eSub : Set.Iio b' ≃o Set.Iio b₀ := hi'.toOrderIso.symm.trans eAIio
      exact eq_of_isOrderPreservingBijection_Iio (OrderIso.isOrderPreservingBijection eSub)
  · have hDom_compl : DomRᶜ.Nonempty := by
      by_contra hne
      apply hDom
      ext x
      simp only [Set.mem_univ, iff_true]
      by_contra hx
      exact hne ⟨x, hx⟩
    let wfA : WellFounded (· < · : A → A → Prop) := wellFounded_lt
    let a₀ : A := wfA.min DomRᶜ hDom_compl
    have ha₀_not : a₀ ∉ DomR := wfA.min_mem DomRᶜ hDom_compl
    have hDom_eq : DomR = Set.Iio a₀ := by
      ext x
      simp only [Set.mem_Iio]
      refine ⟨fun hx => ?_, fun hlt => ?_⟩
      · rcases lt_trichotomy x a₀ with hlt | rfl | hgt
        · exact hlt
        · exact False.elim (ha₀_not hx)
        · exact False.elim (ha₀_not (hDom_down hx hgt))
      · by_contra hx_not
        exact wfA.not_lt_min DomRᶜ hx_not hlt
    by_cases hRan : RanR = Set.univ
    · -- Case (ii): `DomR ≠ univ` and `RanR = univ`.
      refine Or.inr (Or.inl ?_)
      let eIioB : Set.Iio a₀ ≃o B :=
        (Set.orderIsoOfEq DomR (Set.Iio a₀) hDom_eq).symm.trans
          (eDomRan.trans ((Set.orderIsoOfEq RanR Set.univ hRan).trans eqvUnivB))
      rw [ex24Branch2_iff]
      refine ⟨⟨a₀, ⟨eIioB, OrderIso.isOrderPreservingBijection eIioB⟩, fun a' ⟨i', hi'⟩ => ?_⟩,
        fun _ _ _ h₁ h₂ => unique_isOrderPreservingBijection h₁ h₂⟩
      let eSub : Set.Iio a' ≃o Set.Iio a₀ := hi'.toOrderIso.trans eIioB.symm
      exact eq_of_isOrderPreservingBijection_Iio (OrderIso.isOrderPreservingBijection eSub)
    · -- Impossible case: `DomR ≠ univ` and `RanR ≠ univ` would yield `R a₀ b₀`, contradiction!
      have hRan_compl : RanRᶜ.Nonempty := by
        by_contra hne
        apply hRan
        ext y
        simp only [Set.mem_univ, iff_true]
        by_contra hy
        exact hne ⟨y, hy⟩
      let wfB : WellFounded (· < · : B → B → Prop) := wellFounded_lt
      let b₀ : B := wfB.min RanRᶜ hRan_compl
      have hb₀_not : b₀ ∉ RanR := wfB.min_mem RanRᶜ hRan_compl
      have hRan_eq : RanR = Set.Iio b₀ := by
        ext y
        simp only [Set.mem_Iio]
        refine ⟨fun hy => ?_, fun hlt => ?_⟩
        · rcases lt_trichotomy y b₀ with hlt | rfl | hgt
          · exact hlt
          · exact False.elim (hb₀_not hy)
          · exact False.elim (hb₀_not (hRan_down hy hgt))
        · by_contra hy_not
          exact wfB.not_lt_min RanRᶜ hy_not hlt
      let eIio : Set.Iio a₀ ≃o Set.Iio b₀ :=
        (Set.orderIsoOfEq DomR (Set.Iio a₀) hDom_eq).symm.trans
          (eDomRan.trans (Set.orderIsoOfEq RanR (Set.Iio b₀) hRan_eq))
      have ha₀_in : a₀ ∈ DomR := ⟨b₀, eIio, OrderIso.isOrderPreservingBijection eIio⟩
      exact False.elim (ha₀_not ha₀_in)

/-- Raw-relation formulation of Branch (i) of Exercise 2.4 (§2.3, p. 17). -/
def Ex24Branch1Rel {A : Type u} {B : Type v}
    (leA : A → A → Prop) (leB : B → B → Prop) : Prop :=
  ∃! i : A → B, IsOrderPreservingBijectionRel leA leB i

/-- Raw-relation formulation of Branch (ii) of Exercise 2.4 (§2.3, p. 17). -/
def Ex24Branch2Rel {A : Type u} {B : Type v}
    (leA : A → A → Prop) (leB : B → B → Prop) : Prop :=
  ∃! p : (a : A) × ({x : A // garlingStrictLt leA x a} → B),
    IsOrderPreservingBijectionRel (fun x₁ x₂ => leA x₁.1 x₂.1) leB p.2

/-- Raw-relation formulation of Branch (iii) of Exercise 2.4 (§2.3, p. 17). -/
def Ex24Branch3Rel {A : Type u} {B : Type v}
    (leA : A → A → Prop) (leB : B → B → Prop) : Prop :=
  ∃! p : (b : B) × (A → {y : B // garlingStrictLt leB y b}),
    IsOrderPreservingBijectionRel leA (fun y₁ y₂ => leB y₁.1 y₂.1) p.2

/-- Raw `IsGarlingWellOrder` formulation of **Exercise 2.4** (§2.3, p. 17), stated directly on
relations `leA` and `leB` satisfying Garling's well-ordering axioms. -/
theorem exercise_2_4_raw {A : Type u} {B : Type v}
    {leA : A → A → Prop} {leB : B → B → Prop}
    (hA : IsGarlingWellOrder A leA) (hB : IsGarlingWellOrder B leB) :
    (Ex24Branch1Rel leA leB ∧ ¬ Ex24Branch2Rel leA leB ∧ ¬ Ex24Branch3Rel leA leB) ∨
    (¬ Ex24Branch1Rel leA leB ∧ Ex24Branch2Rel leA leB ∧ ¬ Ex24Branch3Rel leA leB) ∨
    (¬ Ex24Branch1Rel leA leB ∧ ¬ Ex24Branch2Rel leA leB ∧ Ex24Branch3Rel leA leB) :=
  @exercise_2_4 A B
    hA.toIsGarlingTotalOrder.toLinearOrder hA.wellFoundedLT
    hB.toIsGarlingTotalOrder.toLinearOrder hB.wellFoundedLT

end Garling.Chapter02
