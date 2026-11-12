# Later Chapter 6 proof implementation ledger

Source: `formalize-everything/books/rudin-real-and-complex-analysis/Scratch69.lean`.

The root's first aggregate diagnostic pass **accepted all 20 public Scratch69 theorem-family audits**, each using exactly `propext`, `Classical.choice`, and `Quot.sound`; see `book/evidence/aggregate-1.log:118–137` (and the source map `aggregate-1-source-map.json`). This includes every 6.9–6.15 family and all four partial 6.18 families. The aggregate as a whole exited 1 because unrelated 6.3, 6.18 extension/bridge, and 6.16 drafts had errors; this is not a clean-slate chapter build claim.

The earlier standalone diagnostic pass, session 5615 (`lake env lean -j1 Scratch69.lean`), exited 1 with three local family errors; those were patched and are all resolved by the aggregate audit. Its historical evidence is `Scratch69.build.log`. The native C0 wrapper, LCH density repair, regular-measure uniqueness/norm, and final complex RMK assembly are later drafts awaiting aggregate checks.

Two earlier checks were stopped with exit 130, before diagnostics, at root's instruction because the shared machine was out of RAM/swap. The lane now schedules one compiler at a time. The root Chapter06 module has compiled successfully and supplies the proved finite-variation instance; the scratch file imports it. No installation/removal, other-lane edit, review request, or external message was made.

| Node | Encoded obligations | Remaining obligation before counting complete |
|---|---|---|
| 6.9 | Measurable integrable real weight, strict `0 < w x < 1` for every x; existence of finite measure with precisely the same null sets | Root module integration and clean-slate build |
| 6.10 | Unique complex pair with sum/ac/singular clauses; arbitrary ac complex measure has measurable integrable density unique a.e.; unique positive finite decomposition for positive finite input | Root module integration and clean-slate build; positive subcase uses the positive-measure encoding, and complex density is obtained by applying RN to the ac component |
| 6.11 | Uniform epsilon/delta iff absolute continuity, with arbitrary positive reference measure; both ENNReal and literal positive-real parameter formulations; unconditional wrapper uses proved 6.4 | Root module integration and clean-slate build |
| 6.12 | Measurable polar density with modulus one everywhere, integrability, reconstruction; unconditional wrapper uses proved 6.4 | Root module integration and clean-slate build |
| 6.13 | Equality of variation measure with norm-density measure; explicit real set-integral formula | Root module integration and clean-slate build |
| 6.14 | Measurable Hahn partition, union/disjointness, canonical Jordan part identities; Jordan minimality for a well-defined difference of positive finite measures | Root module integration and clean-slate build |
| 6.15 | Continuous complex-linear integral functional with operator norm at most Lq norm | Root module integration and clean-slate build |
| 6.18 (partial) | Native complex vector integral; indicator identity; additivity in measure for every bounded measurable function; variation norm bound; bounded complex functional on C0 from any supplied measurable unit polar density | These four families accepted in aggregate1; **polar-density integral identification and Cc/C0 density-extension claims remain open in this file** (other agents are implementing those). Do not count node complete from this file alone. |

6.16 and 6.19 are not implemented here. The pinned-source research establishing their genuine Mathlib gaps is in `CH6-MATHLIB-MAP.md`. No placeholders, unproved axioms, `sorry`, or `admit` have been deliberately introduced.

`Scratch618Final.lean` was subsequently drafted, still unverified: it defines `IsRegularComplexMeasure c` as `Measure.Regular c.variation` and combines 6.12, the polar C0 functional, and root's `vectorIntegral_eq_polar` to obtain the actual native complex-integral functional on C0 with its norm bound. Its snapshot hash is `dc71db52f2732a35f4bb30c7b81802341c50ea1accdd451f298a5eb9add87b60`. Root will include it in a later aggregate check.

Later 6.19 work is in `Scratch619Density.lean`, `Scratch619Uniqueness.lean`, and `Scratch619Assembly.lean`, all uncompiled at this checkpoint. The density proof deliberately repairs the pinned API's hidden NormalSpace assumption using compact/closed Urysohn, preserving arbitrary locally compact Hausdorff spaces. The final `theorem_6_19` draft combines four finite positive RMK measures with unit complex densities, extends equality from Cc to C0, and includes regularity, exact norm, and uniqueness. No full-node completion is claimed before checking these drafts.

Current later-draft SHA256 checkpoints after the explicit regularity-instance elaboration fix:

- `Scratch618Final.lean`: `dc71db52f2732a35f4bb30c7b81802341c50ea1accdd451f298a5eb9add87b60`.
- `Scratch619Density.lean`: `60f6d548ecb064cdf05513d1e9e09b1e66d0b929c35b30aef909659a387bdfeb`.
- `Scratch619Uniqueness.lean`: `31d2b728e478f8c94b198527748105becfb9599b17229130cecdddf727c0d6a2`.
- `Scratch619Assembly.lean`: `83ccb4abcbe4575ac1e3863a483da74ec15b1a9942944a9fa4f4dde3adf133c9`.

`Scratch615Infinity.lean` now drafts the attached6.15 assertion that a bounded complex functional on Lebesgue L∞([0,1]) need not have any L¹ density. It uses endpoint evaluation extended by Hahn–Banach and shrinking polynomial bumps with dominated convergence. This draft is uncompiled and not a completion claim. The unrestricted-measure1<p<∞ prose assertion is separately flagged in `CH6-STATIC-FIDELITY-AUDIT.md`.
