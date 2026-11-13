Formalizes all 18 numbered nodes of Rudin RCA Chapter 8 in `RudinRCA/Chapter08.lean`, and adds the chapter to the umbrella library. The reconstructed cluster inventory counts 18 nodes in Chapter 8 and 23 in Chapter 9; exercises are excluded. Chapter 9 implementation follows separately. Refs #40 and #36.

The module retains the distinctions needed by the printed statements: measurable sections everywhere for the uncompleted product; completed factor/product sigma algebras in 8.10–8.12; the explicit unit-square counterexamples in 8.9, including conditional CH as a hypothesis; extended values and local absolute continuity in 8.16; and the actual centered maximal function in 8.17–8.18. The final bound uses Rudin's displayed `(A * exp 1 * p * q)^(1/p)` with the proved dimension constant `A = 5^k`, and proves both endpoint limits of that constant.

`SCOPING-D.md` maps every Chapter 8 node to its declarations and records the pinned-library claims check. `CLAIMS-D-CH09.md` records Chapter 9 normalization and adaptation research. The inventory was reconstructed from the printed text; no separately produced Stage 1 deliverable was received. The source scan is not committed.

Validation details and evidence links will be inserted here only after the clean-slate build and complete axiom audit pass. This file is a local pending draft and must not be submitted in this state.

Lean remains `leanprover/lean4:v4.34.1`; Mathlib remains `d13f23b723b8a846827a245b89c10fc7d3f11612`. Main's Done counts remain zero pending the coordinator-appointed crossed review and merge. No review has been arranged by this lane, and no merge is requested or performed by it.
