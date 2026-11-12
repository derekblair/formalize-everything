# Chapter 13.1: nonpolynomial entire functions at infinity

Scratch proof target in `InfinityPolynomial.lean`:

```lean
Differentiable ℂ f → MeromorphicAt (fun z ↦ f z⁻¹) 0 →
  ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z
```

Proof route (no new axioms): extract a meromorphic exponent `n`, so that
`g(z)=z^n f(1/z)` is analytic at zero. Continuity bounds `g` on a small ball,
therefore `|f(z)| ≤ C |z|^n` outside a large circle. Cauchy's estimate for each
Taylor derivative of order `k>n` and arbitrarily large radius forces that
derivative at zero to vanish. Mathlib's global Taylor-series representation
of an entire function then truncates to a polynomial. Contraposition gives
the essential-singularity assertion, with essential encoded as nonmeromorphic
in the inverted coordinate. The entire hypothesis already ensures analyticity
on the deleted inverted neighborhood.

This plan and scratch source are not a build certificate. Compilation output
must be checked before any theorem from the scratch file is counted.

Verified 2026-10-29 17:45 UTC: `lake env lean -j1` completed with exit 0
under the lane compile lock. `infinity-polynomial-check.log` records both
principal theorem audits with only `propext`, `Classical.choice`, `Quot.sound`.
The source contains no sorry/admit. This is a scratch-file check, not yet a
clean-slate chapter-module certificate.
