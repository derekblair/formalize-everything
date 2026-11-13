# Cauchy contour continuity draft

`ContourContinuity.lean` is a new, unvalidated scratch proof. No compile has
been launched; the parent agent is aggregating proof checks to avoid repeated
costly import loads on this memory-constrained host.

The main drafted theorem `continuousAt_kernel_intervalIntegral` states that,
for continuous `γ, g : ℝ → ℂ` on `uIcc a b`, the function

```
w ↦ ∫ t in a..b, g t / (γ t - w)
```

is continuous at every point outside `γ '' uIcc a b`. The numerator may include
the contour velocity. The theorem therefore applies both to horizontal and
vertical edge integrals and to the usual affine parametrization of a segment.
The accompanying `continuousOn_kernel_intervalIntegral` states continuity on
the full complement of the compact contour image.

Proof: compactness gives a positive minimum distance δ from the contour to
the chosen point, and a maximum numerator norm M. Within the ball of radius
δ/2 the denominators have norm at least δ/2, so the integrands are bounded by
the constant `M / (δ / 2)`. The interval dominated convergence continuity
theorem supplies continuity. This bound argument is exposed separately as
`continuousAt_kernel_intervalIntegral_of_bounds`.

All three theorem families include `#print axioms`; results are pending.
