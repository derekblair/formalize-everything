# Finite path concatenation draft

`PolygonalConcat.lean` is unvalidated scratch code for the next aggregate check.
It supplies integrability and finite-sum integration for Mathlib's `Path.concat`,
and proves that range restrictions survive concatenation. Equal initial and
final vertices produce an actual closed path with the same integral sum.

For the polygonal cycles of printed 13.4–13.5, take the constituent paths to be
`Path.segment` along the enumerated intervals. `SegmentIntegralBridge.lean`
identifies their curve integrals with the raw oriented edge integrals used in
the grid calculation. Thus this file makes the finite-sum-to-closed-path
integration step explicit.

Four theorem families have `#print axioms`; no successful check is claimed yet.
