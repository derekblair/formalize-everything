# Rudin, *Real and Complex Analysis* ("Papa Rudin")

Walter Rudin, *Real and Complex Analysis*, 3rd edition, McGraw-Hill, 1987.
The sequel to *Principles of Mathematical Analysis* (complete in
`derekblair/rudin-lean`); queued in this repo's CATALOGUE since 2026-10-21
and started 2026-10-27 on Derek's order.

**Bar.** Every numbered node (theorem, lemma, corollary, proposition,
definition-bearing item) of Chapters 1–20 proved in Lean 4 at the pinned
Mathlib, zero sorries/admits, axioms only `propext`, `Classical.choice`,
`Quot.sound`, statements faithful to the printed text. Exercises are out
of scope for v1, as with PMA.

**Pins.** Lean `leanprover/lean4:v4.34.1`; Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` — never float mid-book.

**Novelty gate.** PARTIAL (live Google verification, 2026-10-27). The sole
prior formalization of any part of the book is Michikazu Hirata's Archive
of Formal Proofs entry "The Riesz Representation Theorem" (Isabelle/HOL,
2024), proving the Riesz–Markov–Kakutani fragment following pp. 37–47
(Chapter 2). No complete or multi-chapter development exists anywhere.
Mathlib's scattered coverage of the book's territory is background, mapped
per node by each chapter's claims check.

**Layout.** One module per chapter under `RudinRCA/` (`Chapter01.lean`,
…), imported by the `RudinRCA.lean` umbrella. `PROGRESS.md` tracks node
counts; `QUEUE.md` tracks stuck nodes. Work is ticketed per chapter
cluster in this repo's issues; every PR takes an independent crossed
review (reviewer pool ≠ author pool) and merges only on PASS.

## Cluster A development

The current branch adds Chapter 1 and 14 foundational items from Chapter
2. See [PROGRESS.md](PROGRESS.md), the three chapter inventories and
[SCOPING-A.md](SCOPING-A.md) for exact coverage. The printed definition
3.7 has a zero-measure fidelity hold in [QUEUE.md](QUEUE.md); its repair is
explicit and does not count as a completed original item.

From this directory, with the already provisioned pinned Lean toolchain:

```sh
lake exe cache get
lake build
python3 scripts/check_clean_build.py
python3 scripts/check_audit.py
```

`lake build` includes `RudinRCA.AuditA`. The audit checks transitive axioms,
project ownership (including private/generated declarations), namespace
coverage, and source-module coverage. Only `propext`, `Classical.choice`
and `Quot.sound` are permitted. When adding a chapter, update the umbrella
and the audit's expected-module inventory together.

The regression harness uses isolated fresh fixture builds, checks one
nonvacuous pass plus rejection of a sorry, an explicit axiom, a private
foreign-namespace axiom, and an unimported source, and never changes the
live chapter sources. It tests audit enforcement, not book fidelity.

`check_clean_build.py` copies the current Lean sources and pinned package
configuration into a fresh temporary directory, shares only the provisioned
dependency cache, and runs `lake build` with no existing project outputs.
It records source hashes, verifies that the live inputs remained unchanged,
and retains the snapshot for inspection. The checkout's sources and build
outputs are preserved.
