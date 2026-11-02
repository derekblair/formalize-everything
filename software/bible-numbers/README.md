# Bible numerical systems — arithmetic of specified source datasets

Milestone 1 of [ticket #47](https://github.com/derekblair/formalize-everything/issues/47).
Pure Lean/Std, pinned to `leanprover/lean4:v4.34.1`; no Mathlib dependency.
The implementation awaits the coordinator's independent crossed review.

## Build and audit

```sh
cd software/bible-numbers
python3 scripts/generate_data.py --check
lake clean
lake build
```

The default build includes `BibleNumbers.Audit`. It inventories all package
source modules, checks their presence in the import graph, and audits all
package declarations (including private/generated declarations) and every
`BibleNumbers.*` constant. It rejects locally declared axioms and transitive
dependencies beyond `propext`, `Classical.choice`, and `Quot.sound`.
Finite arithmetic uses kernel `decide`; general arithmetic uses proof-producing
Lean tactics. There are no admitted proofs or native decision trust exceptions.

## Genealogy datasets and totals

[PROVENANCE.md](PROVENANCE.md) describes the published sources and all fidelity
decisions. [data/provenance.csv](data/provenance.csv) records 360 coordinates:
variant, witness, chapter, patriarch, field, value, status, source, and locator.
`scripts/generate_data.py` generates `BibleNumbers/Data.lean` from that table and
the sourced chronology inputs; `--check` verifies exact agreement.

Six named profiles cover MT, SP, Smith's LXX comparison table, Brenton's main
LXX text, Smith's reported Arpachshad330 alternative, and Brenton's Alexandrinus
numerical apparatus. They do not claim to exhaust every manuscript. Missing
patriarchs and fields not explicitly stated are represented as `none`, not zero.
Lifespans calculated by a modern author are not inserted as textual lifespans.

All entries below are theorems in `BibleNumbers/Totals.lean`:

| Profile | Adam → Flood | Flood → Abraham, Terah70 | Flood → Abraham, Terah130 | Adam → Abraham, Terah70 | Adam → Abraham, Terah130 |
| --- | ---: | ---: | ---: | ---: | ---: |
| MT | 1656 | 292 | 352 | 1948 | 2008 |
| SP | 1307 | 942 | 1002 | 2249 | 2309 |
| LXX Smith Table2 | 2262 | 1072 | 1132 | 3334 | 3394 |
| LXX Brenton main text | 2242 | 1172 | 1232 | 3414 | 3474 |
| LXX Smith Arpachshad330 alternative | 2262 | 1072 | 1132 | 3334 | 3394 |
| LXX Brenton Alexandrinus apparatus (`lxxShelah330`) | 2262 | 1072 | 1132 | 3334 | 3394 |

These elapsed-year sums assume a consecutive, gapless chain of the named
begettings. Genesis5 adds Noah's Flood age600 after the steps Adam through
Lamech. Genesis11 starts with the sourced two-year Flood-to-Arpachshad offset,
then follows the named chain, including Kainan in the LXX profiles. Shem's100
and Noah's500 are not misused as those bridge intervals.

`TerahEndpoint.listed70` uses the recorded Genesis11:26 number; it treats that
terminal step as Abraham's birth for the arithmetic scenario. `.inferred130`
is the separate inferred chronology discussed in Smith Table4 notes D–F; for
SP it is explicitly a counterfactual corrected-age scenario. Neither proves
which named son was born when Terah was70. `begettingSum_missing` proves that
any missing requested begetting age invalidates the entire sum.

## Exact divergence and systematic patterns

`BibleNumbers/Divergence.lean` computes the differing coordinates, proves an
explicit list for every unordered pair of the six profiles, and proves the
membership equivalence for arbitrary profiles and coordinates. Thus it covers
all three fields and both chapters, including presence versus absence.

The systematic patterns are propositions over the cells, with exact sets of
patriarchs: the six familiar Genesis5 LXX/MT shifts are +100 at begetting and
−100 in remaining years; the Genesis11 SP/MT compensated +100 pattern has
Eber as an exception, and Nahor has a compensated +50 shift. Theorems also
separate simple begetting offsets from compensating changes; equal or missing
cells cannot satisfy a nonzero shift accidentally.

## Sabbatical and jubilee arithmetic

`BibleNumbers/Jubilee.lean` parameterizes period49 versus period50. It proves
the number of actual sabbatical years in `(start, start + span]` is
`(start + span) / 7 - start / 7`, then specializes both periods. It proves
phase alignment for49, a one-year phase drift per50-year period, and the full
common-multiple characterization with least positive realignment2450.

Elapsed boundaries and numbered jubilee years are separate coordinates.
The first numbered jubilee is year50 in both readings. Under period49,
numbered jubilees remain immediately after a sabbatical year; under period50
their phase drifts. Their next shared numbered year is2500, a2450-year gap
after the common first jubilee. See [JUBILEE-SOURCES.md](JUBILEE-SOURCES.md).

## Source findings

- Smith Table2's LXX Lamech188 yields2262 to the Flood and3394 to Abraham
  with Terah130. His reconstructed Table1 uses Lamech182 and gives2256;
  Table4 gives3388. The six-year discrepancy is explained by different inputs,
  and is proved explicitly; it is not repaired by changing Table2.
- Smith's claim that SP remaining years from Arpachshad through Serug are all
  exactly100 below MT fails on the raw Eber cells430 versus270: the difference
  is160. His proposed MT reconstruction370 would produce100, but is not the
  printed MT reading.
- Millam's table headed “Age at Death” uses remaining years for several
  Genesis11 patriarchs. These labels and the chronology's missing two-year
  offset are documented in PROVENANCE.md; they do not override source cells.

## What this does NOT show

This does not prove historicity, chronology without genealogical gaps, a date
for creation or the Flood, inspiration, textual priority, a complete census of
LXX manuscripts, or a historical calendrical epoch. Arithmetic validity is
conditional on the encoded published observations and stated conventions.
The sabbatical rhythm is continuous with a common epoch. Nedarim61a describes
the full50 reading restarting its sabbatical count after jubilee; that calendar
differs from the continuous reference grid required for the drift theorem.
Models that pause or reset the rhythm require different definitions. No
theological or manuscript authenticity conclusion follows from these theorems.
