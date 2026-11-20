# Cyclic edge indexing and actual closed path draft

`CyclicVertices.lean` is unvalidated scratch code prepared for the next check.
It converts the modulo-successor edge sequences supplied by `BalancedCycles`
into `Fin (n+1)` vertex lists whose first and last vertices agree. Every edge's
two listed vertices equal its original initial and terminal endpoints.

`cyclicPolygonalPath` then constructs an actual closed Mathlib path by
concatenating those directed segments. It has no integrand argument, making
the geometric choice independent of the holomorphic function in printed 13.5.
`cyclicPolygonalEdgePath` only casts endpoint proofs, so its curve integral
equals that of the originally supplied segment.

This file fills the indexing step between the proved balanced finite-edge
partition and the `Path.concat` integration lemmas in `PolygonalConcat.lean`.
Six theorem families have axiom-print statements; validation is pending.
