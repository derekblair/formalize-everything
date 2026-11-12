# Polygonal path regularity

`PolygonalRegularity.lean` depends on `PrimitiveCurveIntegral.lean` (the exact
`Chapter13.IsPiecewiseC1Path` definition) and `PolygonalCyclePackage.lean`.

The proof gives a single-piece partition for segments and constant paths, proves stability under
endpoint casts, and explicitly combines two finite partitions for binary path concatenation. Left
knots are halved; right knots are translated by 1 then halved. At the shared knot both definitions
equal 1/2. On each closed partition interval the extended concatenation agrees with the correct
affine reparametrization of its original C¹ piece. Thus the proof includes partition endpoints,
not merely open subintervals or almost-everywhere differentiability.

`isPiecewiseC1Path_of_isPolygonalPath` proves the bridge by induction over the finite polygonal
construction. `IndexedPolygonalCycle.path_piecewiseC1` applies it to the cycle package's actual paths.

Validation: prepared for the next aggregate; not yet compiled. Ten theorem-family axiom audits
are included. SHA-256: `e3a7d819bbed5f9b336b49d54122b7070ad734e55f2184dfa3d3714bade6af7c`.
