# Chapter 13 inventory / rational-functions agent handoff

All files are in this lane's `evidence/` directory. The agent made no clone,
chapter-module, PR, install, removal, or other-lane changes.

## Inventory

`inventory-ch13.md` is complete: all 12 printed nodes 13.1–13.12, printed
pp. 266–276, excluding exercises. Ticket numbering discrepancies and the
13.11(j) → 14.8 forward dependency are recorded there.

## Lean source state

| Source | Families | Verified state / role |
| --- | ---: | --- |
| `RationalPartialFractions.lean` | 11 | All families passed with permitted axioms in `all-pending-check-1.log`, source mapped by `all-pending-sources.json`. Complete finite-plane 13.2 package. |
| `HolomorphicLog.lean` | 5 | All families passed with permitted axioms in the same aggregate log. 13.11(b)→(h), (h)→(j), and local lift regularity. |
| `PrimitiveLog.lean` | 2 | First aggregate found one missing explicit argument to `differentiableOn_const`. Original source corrected; recheck pending. 13.11(g)→(h). |
| `SimplyConnectedImplications.lean` | 2 | First check pending. 13.11(a)→(b), through contractibility of the open unit disc. |
| `RungeRationalWitness.lean` | 12 | First check pending. Defines agreed `rungeGenerators` and `rungeSpace`, packages every span element as a RatFunc with prescribed finite poles and removability at infinity when required. Uses global `resolvent`, corrected after pinned-API diagnostics. |
| `RungePolynomialWitness.lean` | 1 | First check pending. A member of `rungeSpace K {∞}` has an actual polynomial witness. |
| `PrimitiveCurveIntegral.lean` | 4 | First check pending. Primitive FTC for arbitrary finite C¹ partitions of actual Mathlib paths, then 13.11(g)→(f). |
| `PolynomialApproximationCurve.lean` | 4 | New draft, next aggregate. Actual compactwise polynomial approximation implies zero closed piecewise C¹ curve integrals, 13.11(e)→(f). |
| `RiemannUnitDiscShift.lean`, `RiemannInitialMap.lean`, `RiemannHurwitz.lean`, `RiemannMappingFull.lean`, `RiemannMappingSquareRoots.lean`, `RiemannHomeomorphism.lean` | 23 audit commands | New primary-source adaptations, next aggregate. Standard 14.8 and stronger square-root-premise form needed for independent 13.11(j)→(a). Attribution, exact source revision, hashes, and dependency order in `riemann-pr33505-adaptation-notes.md`. |

The aggregate has errors in other source sections, so the verified sections
above do not constitute an aggregate exit-zero claim. No chapter integration
or clean-slate build is claimed by this agent. Every theorem family in these
sources has a `#print axioms` command. No `sorry`, `admit`, or custom axiom was
introduced.

`RungeRationalWitness.lean` must follow the corrected `RungeFunctional.lean`
body and `RationalPartialFractions.lean` in an aggregate, because it uses their
coordinate/resolvent and canonical quotient evaluation results.
`RungePolynomialWitness.lean` follows `RungeRationalWitness.lean`.
`PolynomialApproximationCurve.lean` follows `PrimitiveCurveIntegral.lean`.
The six Riemann drafts must follow the order recorded in their adaptation notes.
Other files have independent Mathlib imports.

The parent owns aggregate checks, chapter integration, STATUS/REPORT, and all
programme gates. Individual compiler waiters were deliberately superseded by
parent-run aggregate checks to share import loading under host memory pressure.
