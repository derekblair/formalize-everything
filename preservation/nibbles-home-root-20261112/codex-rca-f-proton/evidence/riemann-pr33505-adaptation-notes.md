# Riemann mapping source and adaptation record

## Primary source

Pinned Mathlib `Analysis/Complex/RiemannMapping.lean` explicitly links the
complete, still-draft proof in
[mathlib4 PR 33505](https://github.com/leanprover-community/mathlib4/pull/33505).
The read-only GitHub REST response is retained in
`RiemannMapping-pr33505-metadata.json`; its upstream head is
`d43061d911b1aeae0788591da437a3b115098962` in `urkud/mathlib4`.
The original author is Yury Kudryashov. The copied code is Apache 2.0;
`LICENSE-mathlib-Apache-2.0` retains the full license.

Exact original snapshots:

| File | SHA-256 |
| --- | --- |
| `RiemannMapping-pr33505-original.lean` | `335a97ee3cf41c2f56581b80176decde8de8bb60491a342d3b7eec2146aa8caa` |
| `UnitDiscShift-pr33505-original.lean` | `5892b5e8a85d532b934f481af0900d564fcb76e08a4b58a3667729e4f0eb448e` |
| `LICENSE-mathlib-Apache-2.0` | `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` |

The Riemann source hash was independently matched against the immutable raw
commit URL after retrieving the metadata. No upstream code, project pins,
Mathlib checkout, or other lane was changed. No dependency was installed.
The failed authenticated `gh pr view` request was replaced with unauthenticated
public REST/raw reads; no credentials were recorded.

## Adapted source order

1. `RiemannUnitDiscShift.lean`: unit-disc Möbius shifts, inverse and continuity.
   The PR's missing `UnitDisc/Shift.lean` was reduced to the portion needed by
   the mapping proof, with module visibility syntax removed.
2. `RiemannInitialMap.lean`: exports attributed `rca_` copies of the two exact
   initial-map proofs already present but **private** in pinned Mathlib.
3. `RiemannHurwitz.lean`: finite-zero factorization, circle argument principle,
   Hurwitz zero-free limit theorem, and constant-or-injective limit theorem.
   Already-merged circle convergence and topological lemmas are reused.
4. `RiemannMappingFull.lean`: normalized extremal maps, derivative improvement,
   normal-family compactness, and the standard Riemann map to the unit disc.
   Root API names and initial-map visibility are adjusted for the pinned tree.
5. `RiemannMappingSquareRoots.lean`: changes the original premise to the exact
   property that **every zero-free holomorphic function on the region has a
   holomorphic square root**. New helpers extend root identities outside the
   domain and obtain the initial non-dense injective image from `sqrt(z-a)`.
   The extremal-map proof then uses connectedness and this property, with no
   simple-connectivity assumption. This is essential to avoid circularity in
   Rudin 13.11(j) → (a).
6. `RiemannHomeomorphism.lean`: obtains an actual homeomorphism from a holomorphic
   bijection by the open mapping theorem; handles the whole-plane case via the
   standard topological unit-ball homeomorphism; exposes the book's 14.8 and
   13.11(j) → (a) conclusions.

All six are drafts awaiting the parent-run aggregate. The existence of a
complete upstream proof is **not** a claim that these adaptations compile.
There are 23 audit commands across these files, no `sorry`, no `admit`, and no
custom axiom. The parent owns compilation, fixes after diagnostics, and final
chapter integration. Original upstream snapshots are reference material and
must not be compiled or concatenated alongside the adapted copies.
