# Progress — Garling, *A Course in Galois Theory* (1986)

- **Source text:** D. J. H. Garling, *A Course in Galois Theory* (Cambridge University Press, 1986; ISBN `0 521 32077 1` / `0 521 31249 3`).
- **Source-text provenance:** Staged 1986 CUP scan `garling1986.pdf` (6,924,939 B, MD5 `f0eaa8b28b59e9c8be6d59c05130a703`) and full-text extraction `garling1986_pages.txt` (316,147 B, MD5 `a1c10c3ef4129917c3fcfd9c8ec1fbfd`), authorized as the Stage 1 working copy by Derek on 2026-11-14 (~21:34 PST; `derekblair/formalize-everything#2`).
- **Toolchain & Mathlib pins:** `leanprover/lean4:v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- **Novelty gate (FE #2, 2026-11-06, comment `6689821337`):** `PARTIAL` — no book-level formalization of Garling exists in any proof assistant.

## Chapter Summary

| Chapter | Title | Main-text results (done / total) | Exercises (done / total) | Combined numbered/headed items (done / total) | Notes |
|---:|---|---:|---:|---:|---|
| 1 | Groups, fields and vector spaces | 7 / 7 | 15 / 18 (+ 3 fidelity holds in `QUEUE.md`) | 22 / 25 (+ 3 fidelity holds in `QUEUE.md`) | Enumerated from 1986 scan before proving; all 7 main-text items and 15 exercises proved literally; 3 exercises (`1.7`, `1.10`, `1.18`) held in `QUEUE.md` with kernel-proved counterexamples and repaired theorems |
| 2 | The axiom of choice, and Zorn's lemma | 1 / 1 numbered (`Theorem 2.1`) + 0 / 1 unnumbered headed (`Zorn's lemma` hold in `QUEUE.md`) [1 / 2 headed] | 3 / 4 (+ 1 fidelity hold in `QUEUE.md`) | 4 / 5 strictly numbered (+ 1 hold) / 4 / 6 headed (+ 2 holds in `QUEUE.md`) | Enumerated from 1986 scan before proving; Theorem 2.1 and Exercises 2.1, 2.2, 2.4 proved literally; Zorn's lemma (`S = ∅` non-empty-chain defect) and Exercise 2.3 (`(ℕ, ≤)` and `ω₁` counterexamples) held in `QUEUE.md` with kernel-proved counterexamples and repaired theorems |

## Chapter 1 Scope of Record (Enumerated from 1986 Scan, Printed pp. 3–13 / PDF pp. 11–21)

All definitions in Chapter 1 (§1.1 *Groups*, §1.2 *Fields*, §1.3 *Vector spaces*) and early prose theorems (Lagrange's theorem, first isomorphism theorem, Viergruppe normality in $\Sigma_4$, subgroup classification of $\mathbb{Z}$, $\sqrt{2} \notin \mathbb{Q}$, and subfield $\mathbb{Q}(\sqrt{2}) \subseteq \mathbb{R}$) are unnumbered prose in the 1986 CUP edition (and are also formalized in `Garling/Chapter01.lean` to anchor the chapter's vocabulary). The chapter contains **7 main-text theorem/corollary results** (all in §1.3) and **18 numbered exercises** (`1.1`–`1.18`), listed below in exact source order:

| # | Printed Label | Section | Printed p. | Kind | Lean Declaration(s) in `Garling/Chapter01.lean` | Status |
|---:|---|---|---:|---|---|---|
| 1 | Exercise 1.1 | §1.1 | 7 | Exercise | `exercise_1_1_raw`, `exercise_1_1` | Done (proved) |
| 2 | Exercise 1.2 | §1.1 | 7 | Exercise | `exercise_1_2` | Done (proved) |
| 3 | Exercise 1.3 | §1.1 | 7 | Exercise | `exercise_1_3` | Done (proved) |
| 4 | Exercise 1.4 | §1.1 | 7 | Exercise | `exercise_1_4` | Done (proved) |
| 5 | Exercise 1.5 | §1.1 | 7 | Exercise | `exercise_1_5` | Done (proved) |
| 6 | Exercise 1.6 | §1.1 | 7 | Exercise | `exercise_1_6` | Done (proved) |
| 7 | Exercise 1.7 | §1.1 | 7 | Exercise | `exercise_1_7` + `exercise_1_7_trivial_counterexample` | Queued (`QUEUE.md` fidelity hold: printed statement omits `\|G\| > 1`) |
| 8 | Exercise 1.8 | §1.1 | 8 | Exercise | `exercise_1_8` | Done (proved) |
| 9 | Exercise 1.9 | §1.1 | 8 | Exercise | `exercise_1_9` | Done (proved) |
| 10 | Exercise 1.10 | §1.1 | 8 | Exercise | `exercise_1_10_ker`, `exercise_1_10_surjective` + `exercise_1_10_not_surjective_of_lt_two` | Queued (`QUEUE.md` fidelity hold: onto `{1, -1}` requires `n ≥ 2`) |
| 11 | Exercise 1.11 | §1.2 | 9 | Exercise | `exercise_1_11` | Done (proved) |
| 12 | Exercise 1.12 | §1.2 | 9 | Exercise | `exercise_1_12_well_defined`, `exercise_1_12` | Done (proved) |
| 13 | Exercise 1.13 | §1.2 | 9 | Exercise | `exercise_1_13` | Done (proved) |
| 14 | **Theorem 1.1** | §1.3 | 10 | Main-text theorem | `theorem_1_1` | Done (proved) |
| 15 | **Theorem 1.2** | §1.3 | 11 | Main-text theorem | `theorem_1_2` | Done (proved) |
| 16 | **Theorem 1.3 (The Steinitz exchange theorem)** | §1.3 | 11 | Main-text theorem | `theorem_1_3` | Done (proved) |
| 17 | **Corollary (to Theorem 1.2)** | §1.3 | 12 | Main-text corollary | `corollary_to_theorem_1_2` | Done (proved) |
| 18 | **Theorem 1.4** | §1.3 | 12 | Main-text theorem | `theorem_1_4` (with `subspace_isFiniteDimensional`) | Done (proved) |
| 19 | **Corollary 1** [to Theorem 1.4] | §1.3 | 12 | Main-text corollary | `corollary_1_to_theorem_1_4` | Done (proved) |
| 20 | **Corollary 2** [to Theorem 1.4] | §1.3 | 12 | Main-text corollary | `corollary_2_to_theorem_1_4` | Done (proved) |
| 21 | Exercise 1.14 | §1.3 | 13 | Exercise | `exercise_1_14` (`exercise_1_14_a`, `exercise_1_14_b`, `exercise_1_14_c_set`, `exercise_1_14_c_tuple_not_linearIndependent`) | Done (proved; see formulation note below) |
| 22 | Exercise 1.15 | §1.3 | 13 | Exercise | `exercise_1_15_linearlyIndependent`, `exercise_1_15` | Done (proved) |
| 23 | Exercise 1.16 | §1.3 | 13 | Exercise | `exercise_1_16` (`primeLogSet_infinite`, `primeLogSet_linearlyIndependent`) | Done (proved) |
| 24 | Exercise 1.17 | §1.3 | 13 | Exercise | `exercise_1_17` | Done (proved) |
| 25 | Exercise 1.18 | §1.3 | 13 | Exercise | `exercise_1_18_sharp_lower_bound`, `exercise_1_18_one_dim_lower_bound`, `exercise_1_18_exists_proper_subspaces_union` + `exercise_1_18_printed_lower_bound_counterexample`, `exercise_1_18_no_proper_cover_of_dim_le_one` | Queued (`QUEUE.md` fidelity hold: printed lower bound false for `r ≥ 3`; cover existence requires `r ≥ 2`) |

## Chapter 2 Scope of Record (Enumerated from 1986 Scan, Printed pp. 14–17 / PDF pp. 22–25)

All definitions and examples in Chapter 2 (§2.1 *The axiom of choice*, §2.2 *Zorn's lemma*, §2.3 *The existence of a basis*) — namely the Cartesian-product statement of the axiom of choice (§2.1, p. 14), partial order, inclusion order on subsets, totally ordered set, chain (explicitly defined as a *non-empty* totally ordered subset), upper bound, the finite-subsets-of-an-infinite-set example, and maximal element (§2.2, p. 15), well-ordering (introduced inside Exercise 2.2, §2.3, p. 17), and the prose deduction that every vector space has a basis (§2.3, p. 16) — are unnumbered in the 1986 CUP edition (and are formalized in `Garling/Chapter02.lean` to anchor the chapter's vocabulary). The chapter contains **1 numbered main-text theorem** (`Theorem 2.1` in §2.3) plus **1 unnumbered bold-headed lemma block** (`Zorn's lemma` in §2.2, stated without proof in the book) = **2 main-text headed results**, and **4 numbered exercises** (`2.1`–`2.4`, all in §2.3), listed below in exact source order:

| # | Printed Label | Section | Printed p. | Kind | Lean Declaration(s) in `Garling/Chapter02.lean` | Status |
|---:|---|---|---:|---|---|---|
| 1 | **Zorn's lemma** *(unnumbered bold-headed block)* | §2.2 | 15 | Main-text lemma (stated without proof) | `zorn_lemma_set`, `zorn_lemma`, `zorn_lemma_possibly_empty_chains`, `garlingZornLemma_holds`, `garlingZornLemma_iff_set` + `zorn_lemma_empty_counterexample` | Queued (`QUEUE.md` fidelity hold: printed p. 15 defines chains to be non-empty without requiring `S ≠ ∅`) |
| 2 | **Theorem 2.1** | §2.3 | 16 | Main-text theorem | `theorem_2_1` (plus `exists_basis`) | Done (proved) |
| 3 | Exercise 2.1 | §2.3 | 16–17 | Exercise | `exercise_2_1`, `exercise_2_1_axiomOfChoice`, `exercise_2_1_dep` | Done (proved) |
| 4 | Exercise 2.2 | §2.3 | 17 | Exercise | `exercise_2_2`, `exercise_2_2_set`, `every_nonempty_set_has_wellOrdering` | Done (proved) |
| 5 | Exercise 2.3 | §2.3 | 17 | Exercise | `exercise_2_3_infinite_iff`, `exercise_2_3_infinite_iff_raw`, `exercise_2_3_infinite_dichotomy`, `exercise_2_3_orderIso_nat_of_forall_Iio_finite`, `exercise_2_3_infinite_of_uncountable`, `exercise_2_3_uncountable_iff`, `exercise_2_3_uncountable_iff_raw`, `exercise_2_3_uncountable_dichotomy`, `exercise_2_3_uncountable_of_aleph1_lt` + `exercise_2_3_infinite_counterexample`, `exercise_2_3_uncountable_counterexample` | Queued (`QUEUE.md` fidelity hold: printed claims false on `(ℕ, ≤)` and `ω₁`) |
| 6 | Exercise 2.4 | §2.3 | 17 | Exercise | `exercise_2_4`, `exercise_2_4_raw` (with `ex24Branch2_iff`, `ex24Branch3_iff`, `isOrderPreservingBijection_iff`) | Done (proved) |

## Explicit Formulation Notes (No Silent Deviations)

1. **Order / cardinality without junk values (`setOrder`):** Garling (§1.1, p. 4) defines the order $|S|$ of a set $S$ to be the number of elements in $S$, taking values in $\mathbb{N} \cup \{+\infty\}$. To avoid `Nat.card` / `Set.ncard`'s junk value `0` on infinite sets, `Garling.Chapter01.setOrder` is defined as `ENat.card S : ℕ∞`, and right cosets `RightCoset H g = {h * g | h ∈ H}` and `RightCosets H` are defined literally as on p. 4 (used in `lagrange_theorem`, `exercise_1_3`, `exercise_1_4`, `theorem_1_2`, `theorem_1_3`, `corollary_to_theorem_1_2`, and `corollary_1_to_theorem_1_4`).
2. **Subset linear independence, basis, and dimension without junk values:** Following Garling (§1.3, p. 10 & p. 12), `IsLinearlyDependent`, `IsLinearlyIndependent`, `IsBasis`, and `IsFiniteDimensional` are defined directly on subsets `A : Set V` (and bridged to Mathlib's `LinearIndepOn K id A` via `isLinearlyIndependent_iff`). `garlingDim K V (hV : IsFiniteDimensional K V) : ℕ` requires an explicit `IsFiniteDimensional K V` proof rather than returning `0` on infinite-dimensional spaces.
3. **Exercise 1.14(c) (`{e_1, f_1, f_2, ..., f_n}` in `K^n`, printed p. 13):** Visually verified in the 150 DPI render of printed p. 13 (`PDF p. 21`), Garling defines $f_j = e_1 + \dots + e_j$ (so $f_1 = e_1$) and asks in part (c): *"Is $\{e_1, f_1, f_2, \dots, f_n\}$ a basis for $K^n$?"* (for $n \ge 1$, typed via `Fin (n + 1)`). Because $e_1 = f_1$:
   - As a **subset** of $K^{n+1}$ (Garling's §1.3 definition of basis), `insert e_1 {f_1, ..., f_{n+1}} = {f_1, ..., f_{n+1}}` **is** a basis (`exercise_1_14_c_set`).
   - As an **indexed `(n + 2)`-tuple** `(e_1, f_1, f_2, ..., f_{n+1})` (`garlingEx114cTuple`), the repeated vector $e_1 = f_1$ makes the family **not** linearly independent (`exercise_1_14_c_tuple_not_linearIndependent`).
   Both statements are kernel-proved and conjoined in `exercise_1_14` so neither reading is left unaddressed.
4. **Exercises 1.7, 1.10, and 1.18:** Held in `QUEUE.md` as fidelity holds with both kernel-proved counterexamples to the literal degenerate/false printed claims and kernel-proved repaired statements.
5. **Axiom of Choice (§2.1, printed p. 14) and non-vacuous Zorn implications (Exercises 2.1–2.2, printed pp. 16–17):** Garling (§2.1, p. 14) states the Axiom of Choice via non-emptiness of the Cartesian product $\prod_{\alpha \in A} E_\alpha$ of non-empty sets $E_\alpha$. `Garling/Chapter02.lean` defines `CartesianProduct E = {c : A → X | ∀ α, c α ∈ E α}`, proves equivalence between the subset-family statement `GarlingAxiomOfChoice` and the dependent-family statement `GarlingAxiomOfChoiceDep` (`garlingAxiomOfChoice_iff_dep`), and proves `axiom_of_choice` / `garlingAxiomOfChoice_holds`. Because Lean's classical foundation already includes `Classical.choice`, `exercise_2_1` (`exercise_2_1_axiomOfChoice`, `exercise_2_1_dep`) and `exercise_2_2` (`exercise_2_2_set`) take Zorn's lemma (`hzorn : GarlingZornLemma`) as an **explicit hypothesis** and construct Garling's exact partial-choice poset `Ex21PartialChoice` and initial-segment well-ordered-subset poset `Ex22WellOrderedSub` rather than proving the conclusions directly from `Classical.choice` ignoring `hzorn`.
6. **Zorn's lemma (§2.2, printed p. 15 — `QUEUE.md` fidelity hold):** On p. 15, Garling defines a partial order on an arbitrary set $S$ (not requiring $S \ne \emptyset$), then explicitly defines a chain as *"A non-empty subset $C$ of a partially ordered set $S$..."*, and states Zorn's lemma without requiring $S \ne \emptyset$. For $S = \emptyset$, there are no non-empty subsets $C \subseteq \emptyset$, so every chain vacuously has an upper bound while $S = \emptyset$ has no maximal element (`zorn_lemma_empty_counterexample`). Both the `S.Nonempty` / `Nonempty S` guarded versions (`zorn_lemma_set`, `zorn_lemma`, `garlingZornLemma_holds`, `garlingZornLemma_iff_set`) and Halmos's possibly-empty-chains formulation (`zorn_lemma_possibly_empty_chains`, citing footnote 1 on p. 15) are kernel-proved, and the unnumbered Zorn's lemma block is held in `QUEUE.md`.
7. **Exercise 2.3 (§2.3, printed p. 17 — `QUEUE.md` fidelity hold):** In Part 2 (*"...while $\{x : x < d\}$ is countable for each $d < c$"*), taking $d$ to be the least element of $A$ gives $\{x : x < d\} = \emptyset$, confirming that "countable" in Garling includes finite sets (`Set.Countable`, $|S| \le \aleph_0$) and "uncountable" means `¬ Countable` ($> \aleph_0$; matching Ch. 4 p. 41 & Ch. 18 p. 131). Both parts of Exercise 2.3 are false as printed (`(ℕ, ≤)` refutes Part 1 in `exercise_2_3_infinite_counterexample`, and `Omega1 = (ℵ₁).ord.ToType` refutes Part 2 in `exercise_2_3_uncountable_counterexample`). `Garling/Chapter02.lean` proves both counterexamples, the exact characterizations (`exercise_2_3_infinite_iff` / `_raw`, `exercise_2_3_uncountable_iff` / `_raw`), the dichotomies (`exercise_2_3_infinite_dichotomy`, `exercise_2_3_uncountable_dichotomy`), uniqueness up to order isomorphism of `(ℕ, ≤)` as the infinite counterexample (`exercise_2_3_orderIso_nat_of_forall_Iio_finite`), and the repaired sufficiency theorems (`exercise_2_3_infinite_of_uncountable` and `exercise_2_3_uncountable_of_aleph1_lt`).
8. **Exercise 2.4 (§2.3, printed p. 17):** Both the Mathlib `[LinearOrder] [WellFoundedLT]` formulation (`exercise_2_4`) and the raw `IsGarlingWellOrder` relation formulation (`exercise_2_4_raw`) are proved. `isOrderPreservingBijection_iff` proves that on well-ordered (or linearly ordered) sets, one-way monotonicity (`x₁ ≤ x₂ → i x₁ ≤ i x₂`) and two-way order isomorphism (`x₁ ≤ x₂ ↔ i x₁ ≤ i x₂`) coincide for every bijection, and `ex24Branch2_iff` / `ex24Branch3_iff` prove equivalence between the dependent-pair `∃!` formulation and separate uniqueness of the cut point and the bijection.
