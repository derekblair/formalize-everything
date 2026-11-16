# Progress — Humphreys, *Introduction to Lie Algebras and Representation Theory* (GTM 9, 1972)

- **Source text:** J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Graduate Texts in Mathematics, vol. 9, Springer-Verlag, New York–Heidelberg–Berlin, 1972 (Third printing, revised, 1980; ISBN `0-387-90052-7`).
- **Ticket:** `derekblair/formalize-everything#69`.
- **Toolchain & dependency pins:**
  - `lean-toolchain`: `leanprover/lean4:v4.36.0-rc2` (book-local pin; `formalize-everything`'s `v4.34.1` default does not apply to `books/humphreys-lie-algebras/`).
  - `TauCetiProject/TauCeti`: `83769e442d55cda9d85b3927a93b286831c595ff`.
  - `leanprover-community/mathlib4`: `1b1ccf4b088b32fa3f23f2de1127433254a81e1e` (exact `lake-manifest.json` lock of `TauCeti` @ `83769e44…`).

## Formalized Pin Milestones

| Target Contract | Book Location | Module | Pinned Declarations (proved / total) | Axioms | Review Status |
|---|---|---|---|---|---|
| `PIN-CHEVALLEY-14-3` | Ch. IV, §14.3, Proposition & uniqueness (p. 77) | `Humphreys/Ch4/ChevalleyInvolution14_3.lean` | 3 / 3 | `[propext, Classical.choice, Quot.sound]` | Merged in FE PR #121 (`35155479`) |
| `PIN-CHEVALLEY-25-2` | Ch. VII, §25.2, Proposition (a)–(b) (pp. 146–147) | `Humphreys/Ch7/ChevalleyBasis25_2.lean` | 3 / 3 | `[propext, Classical.choice, Quot.sound]` | Merged in FE PR #122 (`5a9afe6d`) |
| `PIN-KOSTANT-26-4` | Ch. VII, §26.4, Theorem (Kostant) (p. 156) | `Humphreys/Ch7/KostantTheorem26_4.lean` (+ `Kostant/GapA..GapD.lean`) | 11 / 11 (7 defs + 4 theorems) | `[propext, Classical.choice, Quot.sound]` | Merged in FE PR #124 (`5c3001aa`) |
| `PIN-ADMISSIBLE-LATTICE-27-1` | Ch. VII, §27.1, Lemma 27.1 & Theorem 27.1(a)–(b) (pp. 157–159) | `Humphreys/Ch7/AdmissibleLattice27_1.lean` | 15 / 15 (7 defs + 8 theorems) | `[propext, Classical.choice, Quot.sound]` | Proved; crossed review PENDING |

## `PIN-CHEVALLEY-14-3` Declarations (`Humphreys/Ch4/ChevalleyInvolution14_3.lean`)

1. `Humphreys14_3.exists_chevalleyInvolution_of_base` — Split characteristic-zero existence of an involutive Lie algebra automorphism `σ : L ≃ₗ⁅K⁆ L` (of exact order `2` whenever `Nontrivial L`) sending prescribed simple-root standard generators `x i ↦ -y i`, `y i ↦ -x i` (`⁅x i, y i⁆ = coroot i`), and negating `H`.
2. `Humphreys14_3.chevalleyInvolution_unique_of_base` — Uniqueness of `σ : L ≃ₗ⁅K⁆ L` from its action on the simple-root generators `x` and `y` (§14.3, p. 77).
3. `Humphreys14_3.existsUnique_chevalleyInvolution_of_lieBasis` — Bundled `LieAlgebra.Basis ι H` existence-and-uniqueness corollary (`∃! σ : L ≃ₗ⁅K⁆ L`).

## `PIN-CHEVALLEY-25-2` Declarations (`Humphreys/Ch7/ChevalleyBasis25_2.lean`)

1. `Humphreys25_2.exists_rootVectors_chevalley_ab` — Direct structure-constant form: unconditional existence of a coroot-normalized root-vector system `(x, hx : TauCeti.IsSl2System x)` over an arbitrary characteristic-zero field `K` and splitting Cartan subalgebra `H` whose structure constants satisfy `c(-α, -β) = -c(α, β)` on every genuine root sum `γ = α + β`.
2. `Humphreys25_2.exists_isChevalleySystem` — Packaged Chevalley-system form: unconditional existence of `(ω : L ≃ₗ⁅K⁆ L)` and `(x : Weight K H L → L)` satisfying `TauCeti.IsChevalleySystem ω x`.
3. `Humphreys25_2.exists_isChevalleySystem_extending_lieBasis` — Strongest split form: existence of a Chevalley system `(ω, x)` extending a prescribed `B : LieAlgebra.Basis ι H` on simple roots (`x (B.baseSupportEquiv i) = B.e i`, `x (-B.baseSupportEquiv i) = B.f i`).

## `PIN-KOSTANT-26-4` Declarations (`Humphreys/Ch7/KostantTheorem26_4.lean`)

1. `Humphreys26_4.kostantSubring` — Root-divided-power Kostant subring `𝔘(L)_ℤ` generated solely by `x_α^t / t!`.
2. `Humphreys26_4.kostantNegTerm`, `kostantCartanTerm`, `kostantPosTerm`, `kostantMonomial`, `kostantLattice` — Ordered monomials `f_A h_B e_C` and `ℤ`-lattice `𝔅`.
3. `Humphreys26_4.kostantMonomial_basis_over_field` — `K`-linear independence and `K`-spanning of `{f_A h_B e_C}`.
4. `Humphreys26_4.kostantLattice_eq_kostantSubring` — Kostant's Theorem (`𝔅 = 𝔘(L)_ℤ`).
5. `Humphreys26_4.kostantSubringBasis` (with `coe_kostantSubringBasis_apply`) — Bundled free `ℤ`-basis of `𝔘(L)_ℤ`.
6. `Humphreys26_4.kostantSubring_eq_chevalleyKostantForm_rat` — Bridge to `TauCeti.chevalleyKostantForm` over `ℚ`.

## `PIN-ADMISSIBLE-LATTICE-27-1` Declarations (`Humphreys/Ch7/AdmissibleLattice27_1.lean`)

1. `Humphreys27_1.exists_intValued_mvPolynomial_sep` — Lemma 27.1 (p. 158): integer-valued multivariate polynomial separating `d ∈ ℤ^ℓ` from a finite subset `S ⊂ ℤ^ℓ \ {d}` over an arbitrary characteristic-zero field `K`.
2. `Humphreys27_1.kostantNegSubring`, `Humphreys27_1.kostantCartanSubring`, `Humphreys27_1.kostantPosSubring` (`D27.1a`, p. 157) and `Humphreys27_1.kostantTriangularSubrings_eq_span` — Triangular subrings `𝔘_ℤ⁻`, `𝔘_ℤ⁰`, `𝔘_ℤ⁺` of `U_K(L)` and equality with the `ℤ`-spans of `{f_A}`, `{h_B}`, `{e_C}`.
3. `Humphreys27_1.IsFullZLattice` (`D27.1b`, pp. 157–158) and `Humphreys27_1.isFullZLattice_iff_fg_and_span_eq_top_and_finrank_le` — Full `ℤ`-lattice in `W` (`∃ b : Module.Basis (Fin (Module.finrank K W)) K W, M = Submodule.span ℤ (Set.range b)`) and characterization via `M.FG ∧ Submodule.span K M = ⊤ ∧ Module.finrank ℤ M ≤ Module.finrank K W`.
4. `Humphreys27_1.IsKostantInvariant`, `Humphreys27_1.IsAdmissibleLattice`, `Humphreys27_1.minAdmissibleLattice` (`D27.1b`, pp. 158–159, 161).
5. `Humphreys27_1.weightSpace_inter_directSum_of_isKostantInvariant` — Theorem 27.1(a) (p. 158): any additive subgroup `M ≤ V` invariant under `𝔘_ℤ` decomposes as the internal direct sum `⨁_χ (M ∩ V_χ)`.
6. `Humphreys27_1.isAdmissibleLattice_minAdmissibleLattice` & `Humphreys27_1.isAdmissibleLattice_minAdmissibleLattice_irreducibleQuotient` — Theorem 27.1(b) irreducible construction (`M_min = 𝔘_ℤ · v = 𝔘_ℤ⁻ · v`, admissibility, and `M_min ∩ V_lam = ℤ · v`, plus specialization to `V(λ)`).
7. `Humphreys27_1.exists_isAdmissibleLattice` & `Humphreys27_1.exists_chevalleySystem_and_admissibleLattice` — Theorem 27.1(b) existence of an admissible lattice in any finite-dimensional `L`-module `V` over a characteristic-zero field `K` with split `H` (both for given `(ω, x)` and unconditionally via §25.2).
