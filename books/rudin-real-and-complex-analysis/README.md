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
