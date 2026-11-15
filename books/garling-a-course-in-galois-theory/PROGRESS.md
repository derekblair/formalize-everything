# Progress — Garling, *A Course in Galois Theory* (1986)

- **Source text:** D. J. H. Garling, *A Course in Galois Theory* (Cambridge University Press, 1986; ISBN `0 521 32077 1` / `0 521 31249 3`).
- **Source-text provenance:** Staged 1986 CUP scan `garling1986.pdf` (6,924,939 B, MD5 `f0eaa8b28b59e9c8be6d59c05130a703`) and full-text extraction `garling1986_pages.txt` (316,147 B, MD5 `a1c10c3ef4129917c3fcfd9c8ec1fbfd`), authorized as the Stage 1 working copy by Derek on 2026-11-14 (~21:34 PST; `derekblair/formalize-everything#2`).
- **Toolchain & Mathlib pins:** `leanprover/lean4:v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- **Novelty gate (FE #2, 2026-11-06, comment `6689821337`):** `PARTIAL` — no book-level formalization of Garling exists in any proof assistant.

## Chapter Summary

| Chapter | Title | Main-text results (done / total) | Exercises (done / total) | Combined numbered/headed items (done / total) | Notes |
|---:|---|---:|---:|---:|---|
| 1 | Groups, fields and vector spaces | 7 / 7 | 15 / 18 (+ 3 fidelity holds in `QUEUE.md`) | 22 / 25 (+ 3 fidelity holds in `QUEUE.md`) | Enumerated from 1986 scan before proving; all 7 main-text items and 15 exercises proved literally; 3 exercises (`1.7`, `1.10`, `1.18`) held in `QUEUE.md` with kernel-proved counterexamples and repaired theorems |

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

## Explicit Formulation Notes (No Silent Deviations)

1. **Order / cardinality without junk values (`setOrder`):** Garling (§1.1, p. 4) defines the order $|S|$ of a set $S$ to be the number of elements in $S$, taking values in $\mathbb{N} \cup \{+\infty\}$. To avoid `Nat.card` / `Set.ncard`'s junk value `0` on infinite sets, `Garling.Chapter01.setOrder` is defined as `ENat.card S : ℕ∞`, and right cosets `RightCoset H g = {h * g | h ∈ H}` and `RightCosets H` are defined literally as on p. 4 (used in `lagrange_theorem`, `exercise_1_3`, `exercise_1_4`, `theorem_1_2`, `theorem_1_3`, `corollary_to_theorem_1_2`, and `corollary_1_to_theorem_1_4`).
2. **Subset linear independence, basis, and dimension without junk values:** Following Garling (§1.3, p. 10 & p. 12), `IsLinearlyDependent`, `IsLinearlyIndependent`, `IsBasis`, and `IsFiniteDimensional` are defined directly on subsets `A : Set V` (and bridged to Mathlib's `LinearIndepOn K id A` via `isLinearlyIndependent_iff`). `garlingDim K V (hV : IsFiniteDimensional K V) : ℕ` requires an explicit `IsFiniteDimensional K V` proof rather than returning `0` on infinite-dimensional spaces.
3. **Exercise 1.14(c) (`{e_1, f_1, f_2, ..., f_n}` in `K^n`, printed p. 13):** Visually verified in the 150 DPI render of printed p. 13 (`PDF p. 21`), Garling defines $f_j = e_1 + \dots + e_j$ (so $f_1 = e_1$) and asks in part (c): *"Is $\{e_1, f_1, f_2, \dots, f_n\}$ a basis for $K^n$?"* (for $n \ge 1$, typed via `Fin (n + 1)`). Because $e_1 = f_1$:
   - As a **subset** of $K^{n+1}$ (Garling's §1.3 definition of basis), `insert e_1 {f_1, ..., f_{n+1}} = {f_1, ..., f_{n+1}}` **is** a basis (`exercise_1_14_c_set`).
   - As an **indexed `(n + 2)`-tuple** `(e_1, f_1, f_2, ..., f_{n+1})` (`garlingEx114cTuple`), the repeated vector $e_1 = f_1$ makes the family **not** linearly independent (`exercise_1_14_c_tuple_not_linearIndependent`).
   Both statements are kernel-proved and conjoined in `exercise_1_14` so neither reading is left unaddressed.
4. **Exercises 1.7, 1.10, and 1.18:** Held in `QUEUE.md` as fidelity holds with both kernel-proved counterexamples to the literal degenerate/false printed claims and kernel-proved repaired statements.
