# Segment integral bridge draft

`SegmentIntegralBridge.lean` is an unvalidated scratch proof prepared for the
next aggregate check. It defines

```
complexSegmentIntegral f a b =
  ∫ t in 0..1, f (AffineMap.lineMap a b t) * (b-a)
```

and identifies it with Mathlib's `curveIntegral` of the complex 1-form
`ContinuousLinearMap.mul ℂ ℂ (f z)` along `Path.segment a b`.

The two axis-aligned specialization theorems express horizontal integration as
`∫ x in a..b, f (x+c*I)` and vertical integration as
`I * ∫ y in a..b, f (c+y*I)`. Both use affine change of variables and hold
without an ordering restriction on the endpoints, including degenerate
segments. The reversal theorem changes the sign.

These formulas connect the raw grid-edge integrals used in the rectangle
Cauchy proof with actual path-based curve integrals. Each new theorem family
has `#print axioms`; validation is pending.
