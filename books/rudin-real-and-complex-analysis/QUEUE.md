# Queue — stuck nodes

Nodes that resist their lane, with the obstruction stated exactly.
Nothing here is silently dropped: a node leaves this file only by being
proved at the bar or by a coordinator ruling recorded on its ticket.

## Cluster E — ticket #41, source fidelity stops

### E-10.37 — variable mismatch in the printed statement

Printed p. 221 displays `Indγ(z) = 1 + Indγ(w)` but ends with the
membership condition `x ∈ D₊` and `w ∈ D₋`. The free `z`/bound `x`
mismatch is visible in the scan, not an OCR invention. Stop the literal
node. The intended repair is to replace that `x` by `z`, supported by
the following proof, but the repaired geometric theorem is **not yet
formalized**. No theorem with a silently changed binder is admitted.
The closure bars on the earlier `a ± bi` membership conditions were
also checked visually and are present; those conditions are not errors.
Source: [printed p.221](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/233.webp).

### E-11.5 — false strict inequality at radius zero

Printed p. 233, equation (4), allows `0 ≤ r < 1` while claiming strict
angular decrease. At `r = 0` the Poisson kernel is the constant 1, so
`δ = 1`, `t = 2` satisfies the printed angular restrictions and falsifies
the strict inequality. Stop this subclaim. `Chapter11.lean` contains
`node11_5_strict_inequality_counterexample` and
`node11_5_strict_inequality_corrected`; the latter explicitly adds `0 < r`.
Neither proves the false printed claim or completes numbered node 11.5.
Source: [printed p.233](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/245.webp).

## Cluster E — formalization gaps

- The pinned Mathlib has general `curveIntegral` machinery and a convex
  primitive theorem. A bridge to Rudin's finite piecewise C¹ paths,
  reparametrizations, path sums/cycles, and integral-defined integer index
  is still required. The claims check found no full global winding-number,
  cycle Cauchy, residue, or argument-principle package. Circle Cauchy
  theorems alone cannot discharge 10.8–10.15 or 10.34–10.43.
- 10.7 needs the Cauchy transform for an arbitrary finite **complex**
  measure; a positive-measure Bochner theorem with altered hypotheses
  is not a faithful replacement.
- 11.3 defines harmonicity by continuity and existence of the two pure
  second partials with zero sum. Mathlib's harmonic predicate includes
  C² regularity. The reverse regularity bridge is needed for 11.10 and
  later applications to all of Rudin's harmonic functions.
- All other unfinished nodes and the exact compound obligations are
  retained in the [complete inventory](inventory/README.md). Claims-check
  availability is not proof completion; these nodes remain in scope.

These gaps require further proof development, not pin changes or imports
of unfinished Chapters 1–9. This lane's delivery remains a draft until
the Chapter 10 coverage and fidelity requirements are resolved.
