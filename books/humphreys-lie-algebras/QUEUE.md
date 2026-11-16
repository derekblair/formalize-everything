# Queue — Open Targets and Holds (`humphreys-lie-algebras`)

Ticket: `derekblair/formalize-everything#69`.

## Fidelity Holds in Current Milestone (`PIN-CHEVALLEY-25-2`)

- **None (`0`).** All three pinned declarations in `Humphreys/Ch7/ChevalleyBasis25_2.lean` (`exists_rootVectors_chevalley_ab`, `exists_isChevalleySystem`, `exists_isChevalleySystem_extending_lieBasis`) are kernel-proved in the split characteristic-zero setting (`[Field K] [CharZero K]`, without `[IsAlgClosed K]`), matching `PIN-CHEVALLEY-25-2` verbatim with `0` sorries and standard axioms `[propext, Classical.choice, Quot.sound]` only. Per `PIN-CHEVALLEY-25-2`, Proposition 25.2(c) (`c_{α,β}² = (r + 1)²`) is excluded from the open obligation because it is already proved in `TauCeti/Algebra/Lie/Weights/StructureConstant/Normalization.lean` (L120 & L175).

## Downstream Targets Out of Scope for the `25-2` Lane

- **Ch. VII, §26.4, Kostant's Theorem (`PIN-KOSTANT-26-4`):** Equality of the Kostant `ℤ`-lattice `𝔅` and divided-power subring `𝔘(L)_ℤ` (separate lane).
- **Remaining chapters/nodes of GTM 9:** Tracked on `derekblair/formalize-everything#69`.
