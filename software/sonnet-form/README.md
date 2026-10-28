# Shakespeare sonnets — the form as a formal spec

The Shakespearean sonnet form as decidable Lean predicates — 14 lines,
rhyme scheme ABAB CDCD EFEF GG, iambic pentameter under an enumerated
license set — with all 154 sonnets encoded from a recorded public-domain
edition and kernel-checked against the spec, and every deviation
catalogued as licensed or anomalous. Ticket #45 (milestone 1).

The three calibration anomalies the conformance run must surface:
Sonnet 99 (15 lines), Sonnet 126 (12 lines), Sonnet 145 (iambic
tetrameter). Pure Lean at pin v4.34.1; zero sorries; axioms only
propext / Classical.choice / Quot.sound.
