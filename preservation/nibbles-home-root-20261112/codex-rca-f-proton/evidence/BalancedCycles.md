# Balanced interval families: proof evidence

Source node: Rudin RCA third edition, 13.4, printed p. 268. Scratch source: `evidence/BalancedCycles.lean`.

The intended theorem `balanced_closed_cycle_partition` takes a finite type `E` indexing the supplied directed intervals, a vertex type `V`, initial and terminal maps `E -> V`, and equality of the incoming/outgoing fiber cardinalities at every vertex. Taking `V = C` gives the printed complex-plane situation.

The conclusion is a finite family `cycles` of finite subsets of `E` with these properties:

1. Every supplied edge index belongs to exactly one member of `cycles`.
2. Every member has positive cardinality.
3. Each member has an injective enumeration by `Fin cardinality` covering exactly its edge indices.
4. The terminal endpoint of each enumerated interval equals the initial endpoint of its cyclic successor, including the successor from the last index back to the first.

These are explicit closed polygonal edge sequences, not merely a single loop or an arbitrary permutation. Repeated geometric intervals remain distinct when they have different indices. The theorem allows singleton cycles when endpoints agree and handles the empty family without adding an unnecessary hypothesis.

Proof route: equal incoming/outgoing fiber cardinalities give equivalences of fibers. `Equiv.ofFiberEquiv` combines them into a successor permutation. Its `SameCycle` classes form a finite partition including fixed points. `IsCycleOn.pow_apply_eq_pow_apply` proves the enumeration by powers is injective below the class cardinality, and `IsCycleOn.exists_pow_eq` proves coverage. Modular successor closes each sequence.

Validation: all seven theorem families passed elaboration in the parent's `AllPending.lean` aggregate check and report only `[propext, Classical.choice, Quot.sound]`. The extracted output is `BalancedCycles.aggregate-check.log`; the complete output is `all-pending-check-1.log`. The aggregate contains errors in other files, so this is a successful check of this source's declarations, not an exit-0 claim for the complete aggregate or a clean-slate chapter build. The source SHA-256 is `914be3da192730330941e2d4dad404ebc5e17b90f5d072cf5b3c85c4d9ed6d58`, matching the parent source map. Pins: Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
