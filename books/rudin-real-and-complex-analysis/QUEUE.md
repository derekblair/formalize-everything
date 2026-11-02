# Queue — stuck nodes

Nothing here is silently dropped. A node leaves this file only after a
faithful proof or a coordinator ruling recorded on its ticket.

## 3.7 — essential supremum at zero measure (fidelity hold)

The printed third-edition pp.65–66 define the threshold set using **all real
α**, even for nonnegative functions. With the zero measure on a singleton
and the zero function, every real threshold belongs to the set. The note
after 1.18 explicitly permits the zero measure as a positive measure. It is
unbounded below, so the stated real infimum does not exist; an extended-real
interpretation gives minus infinity rather than a nonnegative norm.

Evidence and scan links: [Chapter 3 inventory](INVENTORY-CH03.md).
`RudinRCA/Chapter03.lean` records the counterexample and an explicitly
labelled correction using nonnegative extended thresholds. The original
node remains held; no downstream node is counted complete using an
unannounced correction. Coordinator ruling is pending.

## Chapter 2 continuation — 17 original items pending

These are explicit implementation boundaries, not assertions that the
printed statements are false. See the per-node claims check for evidence.

| Node | Remaining work |
|---|---|
| 2.1 | Formalize the vector-space/linear-functional interface. |
| 2.2 | State the integration functional examples and positivity. |
| 2.3 | Package the topological definitions and their precise neighborhood convention. |
| 2.8 | Package semicontinuity, indicators and arbitrary extrema. |
| 2.9 | State the compact-support definition and its representation bridge. |
| 2.14 | Complete complex Riesz representation on the completed sigma algebra, including uniqueness and all regularity clauses. |
| 2.15 | Bridge Rudin regularity on all Borel sets; Mathlib Regular alone is insufficient. |
| 2.16 | State sigma-compact/sigma-finite definitions and implications under 2.14. |
| 2.17 | Closed/open and Fσ/Gδ approximations on the completed measure space. |
| 2.18 | Automatic regularity under exactly the book's topological assumptions. |
| 2.19 | Euclidean cells and half-open dyadic decompositions. |
| 2.20 | The complete Lebesgue-measure existence/uniqueness/transformation package. |
| 2.21 | Interval/Riemann integral comparison and non-Borel-set discussion. |
| 2.22 | Nonmeasurable-subset existence and attached corollary; exact Mathlib theorem not found. |
| 2.23 | All determinant scaling cases, including singular maps. |
| 2.24 | Full Lusin statement and bounded a.e. approximation corollary; exact Mathlib theorem not found. |
| 2.25 | Full non-strict Vitali–Carathéodory statement without introducing sigma-finiteness. |

## Chapter 3 continuation

Original items 3.1–3.6 and 3.8–3.17 (16 items) are inventoried and deferred
after Stage 1; Stage 2 of this lane requests Chapter 1 and continuation into
Chapter 2. Items involving infinity depend on the explicit 3.7 convention
disposition. No original Chapter 3 item is silently marked complete.

## Bibliographic discrepancy (no mathematical correction)

Pinned Mathlib cites Vitali–Carathéodory as RCA 2.24 with `rudin2006real`.
The verified 1987 third edition has Lusin 2.24 and Vitali–Carathéodory 2.25.
This lane retains the book's numbering. See the Chapter 2 overlap analysis.
