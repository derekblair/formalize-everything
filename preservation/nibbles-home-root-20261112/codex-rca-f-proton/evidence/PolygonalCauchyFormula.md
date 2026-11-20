# Full polygonal Cauchy representation and separation bridge

`PolygonalCauchyFormula.lean` depends on the parent's `GridRepresentation.lean` plus
`PolygonalCyclePackage.lean` and `PolygonalRegularity.lean`. It turns the balanced finite grid
boundary into finitely many actual closed paths, all polygonal and piecewise C¹, with range in
Ω minus K. The path family is chosen before the holomorphic function and evaluation point.
For every holomorphic f on Ω and z in K, the theorem proves integrability of each Cauchy kernel
and the normalized Cauchy formula. Empty K is permitted. This is the complete geometric and
analytic statement of printed Rudin 13.5, conditional only on the constituent proved helpers
once their aggregate checks succeed; no hypothesis assumes the desired integral identity.

`PolygonalCycleSeparation.lean` adds the bridge from actual closed polygonal paths with zero
reciprocal integrals to `ReciprocalBalancedCyclesVanish`, and then the parent's spherical
complement criterion. A corollary accepts the full piecewise C¹ path class. This supplies the
actual-path version needed for 13.11(c) implies (d).

Validation: both files are prepared for the next aggregate and have not yet compiled. They
contain one and three theorem-family axiom audits respectively.

SHA-256:

- PolygonalCauchyFormula.lean: `b48f31cb816083fc5da923b4076c36556393ebfc707ecb0a4ff109b5c94a091a`
- PolygonalCycleSeparation.lean: `b46cbef3c34f7e4b2a47fe881c81cf1049bb5889e7f3f6c111403f33e4aca591`
