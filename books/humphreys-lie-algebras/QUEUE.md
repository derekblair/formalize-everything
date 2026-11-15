# Queue — Open Targets and Holds (`humphreys-lie-algebras`)

Ticket: `derekblair/formalize-everything#69`.

## Fidelity Holds in Current Milestone (`PIN-CHEVALLEY-14-3`)

- **None (`0`).** All three pinned declarations in `Humphreys/Ch4/ChevalleyInvolution14_3.lean` (`exists_chevalleyInvolution_of_base`, `chevalleyInvolution_unique_of_base`, `existsUnique_chevalleyInvolution_of_lieBasis`) are kernel-proved in the split characteristic-zero setting (`[Field K] [CharZero K]`, without `[IsAlgClosed K]`), matching `PIN-CHEVALLEY-14-3` verbatim with `0` sorries and standard axioms `[propext, Classical.choice, Quot.sound]` only.

## Downstream Targets Out of Scope for the `14-3` Lane

- **Ch. VII, §25.2, Proposition (a)–(b) (`PIN-CHEVALLEY-25-2`):** Unconditional existence of a Chevalley system over an arbitrary characteristic-zero field `K` (separate lane).
- **Ch. VII, §26.4, Kostant's Theorem (`PIN-KOSTANT-26-4`):** Equality of the Kostant `ℤ`-lattice `𝔅` and divided-power subring `𝔘(L)_ℤ` (separate lane).
- **Remaining chapters/nodes of GTM 9:** Tracked on `derekblair/formalize-everything#69`.
