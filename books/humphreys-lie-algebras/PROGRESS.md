# Progress — Humphreys, *Introduction to Lie Algebras and Representation Theory* (GTM 9, 1972)

- **Source text:** J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Graduate Texts in Mathematics, vol. 9, Springer-Verlag, New York–Heidelberg–Berlin, 1972 (Third printing, revised, 1980; ISBN `0-387-90052-7`).
- **Ticket:** `derekblair/formalize-everything#69`.
- **Toolchain & dependency pins (coordinator day-zero waiver):**
  - `lean-toolchain`: `leanprover/lean4:v4.36.0-rc2` (pinned from day zero of this book; `formalize-everything`'s `v4.34.1` default does not apply to `books/humphreys-lie-algebras/`).
  - `TauCetiProject/TauCeti`: `83769e442d55cda9d85b3927a93b286831c595ff`.
  - `leanprover-community/mathlib4`: `1b1ccf4b088b32fa3f23f2de1127433254a81e1e` (exact `lake-manifest.json` lock of `TauCeti` @ `83769e44…`).

## Formalized Pin Milestones

| Target Contract | Book Location | Module | Pinned Declarations (proved / total) | Axioms | Review Status |
|---|---|---|---:|---|---|
| `PIN-CHEVALLEY-14-3` | Ch. IV, §14.3, Proposition & uniqueness (p. 77) | `Humphreys/Ch4/ChevalleyInvolution14_3.lean` | 3 / 3 | `[propext, Classical.choice, Quot.sound]` | Authored (`carbon-humphreys-14-3-proof-20261115`); crossed review **PENDING** |

## `PIN-CHEVALLEY-14-3` Declarations (`Humphreys/Ch4/ChevalleyInvolution14_3.lean`)

1. `Humphreys14_3.exists_chevalleyInvolution_of_base` — Split characteristic-zero existence of an involutive Lie algebra automorphism `σ : L ≃ₗ⁅K⁆ L` (of exact order `2` whenever `Nontrivial L`) sending prescribed simple-root standard generators `x i ↦ -y i`, `y i ↦ -x i` (`⁅x i, y i⁆ = coroot i`), and negating `H`.
2. `Humphreys14_3.chevalleyInvolution_unique_of_base` — Uniqueness of `σ : L ≃ₗ⁅K⁆ L` from its action on the simple-root generators `x` and `y` (§14.3, p. 77).
3. `Humphreys14_3.existsUnique_chevalleyInvolution_of_lieBasis` — Bundled `LieAlgebra.Basis ι H` existence-and-uniqueness corollary (`∃! σ : L ≃ₗ⁅K⁆ L`).
