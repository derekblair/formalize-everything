# Cluster A scope and evidence

Ticket: [#37](https://github.com/derekblair/formalize-everything/issues/37).
Author pool: ChatGPT/Codex. Independent review is coordinator-appointed;
this lane neither arranges review nor merges.

Stage 1 inventories all 83 numbered items in Chapters 1–3, rather than
inferring theorem numbers from chapter titles. The three chapter inventories
contain per-item pinned-Mathlib claims checks. Numbering and statements
were checked against a public scan of the 1987 third edition; the publisher
contents independently checks chapter identity. All numbering is verified.

The 48 result-bearing numbered groups include 1.9, 1.15 and 1.24, which
contain explicit propositions without a theorem heading. Definition and
exposition entries still remain in the 83-item denominator. A result group
is complete only when all its clauses and attached corollaries are covered.

Mathlib U/V/M labels describe library reuse, not book proofs. Definitions
are not counted complete merely because a similarly named Mathlib type
exists. In particular finite-valued simple functions, ordinary versus
almost-everywhere measurability, completed sigma algebras, and the complex
Riesz functional need explicit representation bridges.

Chapter 2 maps Hirata's AFP pp.37–47 fragment separately from Mathlib. The
third edition numbers Lusin 2.24 and Vitali–Carathéodory 2.25; Mathlib's 2.24
Vitali citation is not used to renumber the book. Mathlib regularity and
sigma-finiteness assumptions are not silently substituted for Rudin's.

The printed section 3.7 threshold definition has a zero-measure defect,
documented in the inventory and QUEUE. Its repair is explicit and does not
count as a proof of the original item.

## What this does NOT show

An inventory is not a complete formalization. A successful axiom audit
checks the included declarations, not unimplemented nodes or faithfulness
to the book. A compilation of a partial chapter does not certify chapter
completion. Claims of new mathematics or absence of all prior work are
not made by this lane. The inherited README novelty claim is programme
background, not a conclusion re-established here.
