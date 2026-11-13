import RudinRCA.Chapter01
import RudinRCA.Chapter02
import RudinRCA.Chapter03
import RudinRCA.Chapter04
import RudinRCA.Chapter05
import RudinRCA.Chapter06
import RudinRCA.Chapter07
import RudinRCA.Chapter08
import RudinRCA.Chapter09
import RudinRCA.Chapter10
import RudinRCA.Chapter11
import RudinRCA.Chapter12
import RudinRCA.Chapter13
import RudinRCA.Chapter14
import RudinRCA.Chapter15
import RudinRCA.AuditE

/-!
Rudin, *Real and Complex Analysis* (3rd edition, McGraw-Hill, 1987).
Chapter coverage and remaining numbered nodes are tracked in PROGRESS.md and SCOPING-D.md.

This umbrella imports the current book development (Chapters 1–15, and `AuditE`).
Inventory, precise coverage and fidelity holds are recorded in PROGRESS.md,
the chapter inventories, SCOPING-A.md and QUEUE.md.
The independently built AuditA module audits this entire import graph.

  The programme target is a complete formalization: every numbered node of
  Chapters 1–20, zero sorries, axioms only propext / Classical.choice /
  Quot.sound, statements faithful to the printed text.

  Novelty gate (2026-10-27): PARTIAL — the only prior formalization of any
  part of the book is Hirata's AFP entry (Isabelle/HOL, 2024) proving the
  Riesz–Markov–Kakutani fragment of Chapter 2. No book development exists
  in any proof assistant. Record:
  research/prior-art-rca.md in the programme's files (ticket umbrella).

  Current coverage is partial; see PROGRESS.md and inventory/README.md.
  Chapter modules are added under RudinRCA/ as their lanes land them.
-/
