# Queue — Open Targets and Holds (`humphreys-lie-algebras`)

Ticket: `derekblair/formalize-everything#69`.

## Current Milestone (`PIN-BINOMIAL-BASIS-26-1`)

- **Proved, pending independent crossed review (draft PR, lane `neon-humphreys-26-1-proof-20261120`):** Ch. VII, §26.1 (`Humphreys/Ch7/BinomialBasis26_1.lean`) — Lemma 26.1 integer-valued polynomial binomial `ℤ`-basis with coordinatewise degree bounds, subring generation, bundled `Module.Basis`, and univariate `ℓ = 1` specialization (3 definitions + 4 public theorems, 0 `sorry`).
- **Proved, landed (merged in FE PR #150, `665faebc`):** Ch. VII, §26.3 Lemma B (`Humphreys/Ch7/ClosedSubsetBasis26_3B.lean`) — PBW `K`-linear independence of ordered `Ψ`-monomials, spanning and unique `ℤ`-expansion of `closedSubsetSubring H Ψ x` for arbitrary closed asymmetric root subsets `Ψ ⊆ Φ` and arbitrary orderings `ψOrd : Fin s ≃ ↥Ψ`, bundled `Module.Basis (Fin s → ℕ) ℤ (closedSubsetSubring H Ψ x)`, and Humphreys's canonical `Φ⁺` / two-root-cone examples (5 defs + 4 public theorems + 1 frozen private theorem, 0 `sorry`).
- **Proved, landed (merged in FE PR #148, `a138dbbc`):** Ch. VII, §25.1(c) & §25.2(c) (`Humphreys/Ch7/SquareIdentity25_2c.lean`) — Proposition 25.1(c) (abstract `RootPairing.InvariantForm` & Killing-form `(L, H)` squared-length ratio), universal Proposition 25.2(c) (under `IsSl2System` + scalar `(b)`), `(r + 1)²` reduction, `IsChevalleySystem` specialization, and unconditional Proposition 25.2(a)–(b)–(c) (6 theorems, 0 `sorry`).
- **Landed Ch. VII foundations:** Ch. VII, §25.2(a)–(b) (`Humphreys/Ch7/ChevalleyBasis25_2.lean`, PR #122), §25.1(c) & §25.2(c) (`Humphreys/Ch7/SquareIdentity25_2c.lean`, PR #148, `a138dbbc`), §26.3 Lemma B (`Humphreys/Ch7/ClosedSubsetBasis26_3B.lean`, PR #150, `665faebc`), §26.4 (`Humphreys/Ch7/KostantTheorem26_4.lean`, PR #124), §27.1 (`Humphreys/Ch7/AdmissibleLattice27_1.lean`, PR #129, `a790602f`), §27.2 (`Humphreys/Ch7/StabilizerLattice27_2.lean`, PR #131, `b9b927dd`), and §27.3 (`Humphreys/Ch7/LatticeVariation27_3.lean`, PR #132).
- **Fidelity holds:** None (`0`).

- **Remaining chapters/nodes of GTM 9:** Tracked on `derekblair/formalize-everything#69`.
