# Scansion validation

## Scope and authorship

The sample comprises **11 complete sonnets, 154 lines**: 2, 18, 19, 20, 29, 55, 60, 73, 116, 130, and 145. This is a **manual reading by a Codex author-agent**, not independent human or scholarly validation. The syllable-by-syllable annotations in [data/validation-scans.tsv](data/validation-scans.tsv) were written before inspecting the machine annotation output. They were not retuned to improve agreement. Each records one defensible performance, rather than asserting that poetry has a unique stress sequence. Uppercase syllables are strong; lowercase syllables are weak; vertical bars group feet. The original edition text remains unchanged in the fixture.

The selection is purposive, not random. It includes pyrrhic and spondaic substitutions (2), initial inversion (20.6, 29.5, 60.7), feminine endings (all fourteen lines of 20), contractions, rhetorical interior inversions, and the tetrameter control (145). The denominator includes every line of every sampled sonnet. [data/validation.json](data/validation.json) contains the complete hand fixture, and [data/validation-results.json](data/validation-results.json) contains every machine comparison.

## Method

`python3 tools/validate_scansion.py` joins the frozen hand source to the exact corpus text and compares it with `data/annotations.json`. `python3 tools/validate_scansion.py --check` rejects stale fixtures, results, or this document. This Python comparison is a reproducible validation measurement, not a Lean proof that a reading is linguistically correct. The conformance verdicts it consumes are separately checked by the Lean audit.

Syllable and stress comparisons apply the candidate's explicitly indexed elision but retain a feminine ending. “Any supplied reading” means the finite baseline/elision candidates, not an unbounded search for a favorable reading. “Selected” means the first licensed reading, or the baseline when none passes. Fixed-stress compatibility allows the supplied monosyllabic masks to take the hand stress, but requires exact length and every fixed multisyllabic stress to agree. It is a sequence-level compatibility measurement; it does not certify word-by-word phonetics. The meter-family comparison expects pentameter for the ten ordinary sonnets and rejects pentameter for every line of 145; it does not require the preferred rhetorical scan itself to obey the spec's restricted substitution budget.

## Agreement

| Measurement | Agree | Total | Agreement |
|---|---:|---:|---:|
| Baseline syllable count | 137 | 154 | 89.0% |
| Any supplied reading: syllable count | 143 | 154 | 92.9% |
| Baseline complete stress sequence | 77 | 154 | 50.0% |
| Any supplied reading: complete stress sequence | 79 | 154 | 51.3% |
| Selected reading: complete stress sequence | 77 | 154 | 50.0% |
| Fixed lexical stresses compatible with hand reading | 128 | 154 | 83.1% |
| Licensed-meter verdict versus hand verse family | 149 | 154 | 96.8% |
| Whole-poem licensed-meter verdict versus hand family | 8 | 11 | 72.7% |

Low exact stress agreement partly reflects a deliberate model choice: monosyllables are realized in alternating positions, while the hand reading often stresses adjacent content words. Such differences do not by themselves disprove either performance. Syllabification and fixed multisyllabic-stress disagreements are stronger evidence of the current lexical model's limits.

| Sonnet | Baseline syllables | Any-reading syllables | Exact baseline stress | Exact any-reading stress | Fixed-stress compatibility | Line-family agreement | Model poem verdict | Poem-family agreement |
|---:|---:|---:|---:|---:|---:|---:|---|---|
| 2 | 14/14 | 14/14 | 4/14 | 4/14 | 14/14 | 14/14 | PASS | agree |
| 18 | 14/14 | 14/14 | 9/14 | 9/14 | 12/14 | 14/14 | PASS | agree |
| 19 | 11/14 | 12/14 | 5/14 | 5/14 | 12/14 | 13/14 | FAIL | disagree |
| 20 | 14/14 | 14/14 | 9/14 | 9/14 | 14/14 | 14/14 | PASS | agree |
| 29 | 12/14 | 13/14 | 5/14 | 5/14 | 9/14 | 14/14 | PASS | agree |
| 55 | 10/14 | 10/14 | 5/14 | 5/14 | 8/14 | 12/14 | FAIL | disagree |
| 60 | 11/14 | 12/14 | 6/14 | 6/14 | 10/14 | 12/14 | FAIL | disagree |
| 73 | 13/14 | 13/14 | 7/14 | 7/14 | 11/14 | 14/14 | PASS | agree |
| 116 | 12/14 | 13/14 | 8/14 | 8/14 | 11/14 | 14/14 | PASS | agree |
| 130 | 13/14 | 14/14 | 9/14 | 10/14 | 13/14 | 14/14 | PASS | agree |
| 145 | 13/14 | 14/14 | 10/14 | 11/14 | 14/14 | 14/14 | FAIL | agree |

## What the discrepancies establish

The hand reading expands `temperate` (18.2) and `fixed` (116.5), contracts `every`/`wandering` (116.7), and uses one syllable for both instances of `wires` (130.4). Those discrepancies motivated the explicit sourced lexical annotations in [PRONUNCIATION.md](PRONUNCIATION.md). The noun/verb ambiguity of `record` (55.8), the historical stress of `antique` (19.10), and the prosodic reading of `contents` (55.3) are now treated by documented lexical/context rules rather than the unqualified first dictionary reading. The interior inversion on `ever` in 19.14 now has the named third/fourth-foot license; Kiparsky directly discusses this example. The generic license still lacks phrase/proclitic annotation and checks only positional feasibility, as detailed in [SPEC.md](SPEC.md).

These findings support the implementation as an auditable **conditional baseline**, but do not establish that its extra failures are genuine exceptions to Shakespearean verse. The original hand fixture remains frozen. This is now a development/regression sample because its named discrepancies informed the revisions, not a held-out estimate of generalization. Remaining disagreements and restrictions are listed below; source evidence justifies specific annotations, not a unique performance of every line. A claim of reliable full-corpus historical conformance would also require validating historical rhyme classes; this sample is a scansion check only. No independent reviewer was appointed or consulted by the author lane.

## Every disagreement

The table includes any line with a disagreement on any metric. `S` means strong and `u` weak. Candidate strings are after their declared elision; the full text and individual Boolean measurements are in the result JSON. “Fixed stress” means the hand sequence conflicts with all supplied masks or lengths. “Realization” means the masks permit the hand sequence but the deterministic candidates did not choose it.

| Line | Hand stress | Model candidate stresses | Disagreement |
|---|---|---|---|
| 2.1 | `uSuSuuuSuS` | `uSuSuSuSuS` | realization |
| 2.2 | `uSSSuuuSuS` | `uSuSuSuSuS` | realization |
| 2.3 | `uSSSuuuSSS` | `uSuSuuuSuS` | realization |
| 2.4 | `uSuSuSuSSS` | `uSuSuSuSuS` | realization |
| 2.7 | `uSuSuSSSuS` | `uSuSuSuSuS` | realization |
| 2.8 | `uuSSuSuSuS` | `uSuSuSuSuS` | realization |
| 2.9 | `uSSSuSuSuS` | `uSuSuSuSuS` | realization |
| 2.10 | `uSuSuSSSuS` | `uSuSuSuSuS` | realization |
| 2.13 | `uSuSSSuSuS` | `uSuSuSuSuS` | realization |
| 2.14 | `uSuSSuuSuS` | `uSuSuSuSuS` | realization |
| 18.3 | `SSuSuSuSuS` | `uSuSuSuSuS` | realization |
| 18.5 | `SuuSuSuSuS` | `SSuSuSuSuS`; `SSuSuSuSu` | fixed stress/length |
| 18.7 | `uSuSuSuSuS` | `uSuSuSSSuS` | fixed stress/length |
| 18.11 | `uSSSuSuSuS` | `uSuSuSuSuS` | realization |
| 18.14 | `uSSSuSuSuS` | `uSuSuSuSuS` | realization |
| 19.1 | `uSuSSuuSuS` | `uSuuuSuSSuu` | baseline syllable count; all candidate syllable counts; fixed stress/length; meter family |
| 19.2 | `uSuSuSuSuS` | `uSuSuSuSuSu` | baseline syllable count; all candidate syllable counts; fixed stress/length |
| 19.3 | `SuSSuuSSuS` | `uSuSuSuSuS` | realization |
| 19.5 | `SSuSuSuSuS` | `uSuSuSuSuS` | realization |
| 19.6 | `uSuSuSSSuS` | `uSuSuSuSuS` | realization |
| 19.7 | `uuSSuSuSuS` | `uSuSuSuSuS` | realization |
| 19.9 | `uSuSuSuSSS` | `uSuSuSuSuSu`; `uSuSuSuSuS` | baseline syllable count; realization |
| 19.11 | `SuuSuSuSuS` | `uSuSuSuSuS` | realization |
| 19.13 | `uSuSSSuSuS` | `uSuSuSuSuS` | realization |
| 20.2 | `SuuSuSuSuSu` | `uSuSuSuSuSu` | realization |
| 20.4 | `uSuSuSSSuSu` | `uSuSuSuSuSu` | realization |
| 20.8 | `uSSSuSuSuSu` | `uSuSuSuSuSu` | realization |
| 20.12 | `uSuSSuuSuSu` | `uSuSuSuSuSu` | realization |
| 20.14 | `SuuSuSuSuSu` | `uSuSuSuSuSu` | realization |
| 29.2 | `uSuSuSuSuS` | `uSuSuSuSSS` | fixed stress/length |
| 29.3 | `uSuSSuuSuS` | `uSuSSuuSSuu`; `uSuSSSuSuS` | baseline syllable count; realization |
| 29.4 | `uSuSuSuSuS` | `uSuSSSuSuS` | fixed stress/length |
| 29.7 | `uSuSuSuSuS` | `uSuuuSuSuSu` | baseline syllable count; all candidate syllable counts; fixed stress/length |
| 29.8 | `uSuSuSuSuS` | `uSuSSSuSuS` | fixed stress/length |
| 29.9 | `uSuSuSuSuSu` | `uSuSuSSSuSu` | fixed stress/length |
| 29.11 | `SuuSuSuSuSu` | `uSuSuSuSuSu` | realization |
| 29.12 | `uSuSSSuSuS` | `uSuSuSuSuS`; `uSuSuSuSu` | realization |
| 29.13 | `uSSSuSuSSS` | `uSuSuSuSuS` | realization |
| 55.2 | `uSuSuSuSuS` | `uSuSSSuSuuu` | baseline syllable count; all candidate syllable counts; fixed stress/length |
| 55.4 | `uSuSuSuSuS` | `uuSSuSuSuS` | fixed stress/length |
| 55.5 | `uSuSuSuSuS` | `uSuSuSSSuS` | fixed stress/length |
| 55.6 | `uSSSuSuSuu` | `uSuSuSuSuu` | realization |
| 55.7 | `uSuSuSSSuS` | `uSuSuSuSuSu` | baseline syllable count; all candidate syllable counts; fixed stress/length |
| 55.9 | `uSuSuSuSuu` | `uSuSuSuuSuu` | baseline syllable count; all candidate syllable counts; fixed stress/length; meter family |
| 55.10 | `uSSSuSuSuS` | `uSuSuSuSuS` | realization |
| 55.11 | `SuuSuSuSuu` | `SuuSuSuuSuu` | baseline syllable count; all candidate syllable counts; fixed stress/length; meter family |
| 55.12 | `uSuSSuuSuS` | `uSuSuSuSuS` | realization |
| 60.1 | `SuuSuSuSuS` | `uSuSuuSSSuu` | baseline syllable count; all candidate syllable counts; fixed stress/length; meter family |
| 60.2 | `uSuSuSuSuS` | `uSSuSuSuuSu`; `uSSSuSuSuS` | baseline syllable count; fixed stress/length |
| 60.3 | `SSuSuSuSuS` | `uSuSuSuSuS` | realization |
| 60.5 | `uSuuSuuSuS` | `uSuuuSuSuS` | realization |
| 60.6 | `SuuSuuuSuS` | `uSuSuuuSSuu` | baseline syllable count; all candidate syllable counts; fixed stress/length; meter family |
| 60.9 | `SuuSuSuSuS` | `uSuSuSuSuS` | realization |
| 60.10 | `uSuSuuuSuS` | `uSuSuSuSuS` | fixed stress/length |
| 60.11 | `SuuSuuuSuS` | `uSuSuuuSuS` | realization |
| 73.4 | `SSuSuSuSSS` | `uSuSuSuSuS` | realization |
| 73.5 | `uSuSuSuSuS` | `uSuSuSSSuS` | fixed stress/length |
| 73.6 | `uSuSuSuSuS` | `uSuSSSuSuS` | fixed stress/length |
| 73.7 | `uSuSSSuSuS` | `uSuSuSuSuS` | realization |
| 73.8 | `SSuSuSuSuS` | `uSuSuSuSuS` | realization |
| 73.9 | `uSuSuSuSuS` | `uSuSuSuSuSu` | baseline syllable count; all candidate syllable counts; fixed stress/length |
| 73.11 | `uuSSuSuSuS` | `uSuSuSuSuS` | realization |
| 116.1 | `SuSuuSuuSS` | `uSuSuSuSuS` | realization |
| 116.2 | `uSuSuuSuSS` | `uSSSuuuSuS` | fixed stress/length |
| 116.8 | `uSuSuSuSuSu` | `uSuSSSuSuSu` | fixed stress/length |
| 116.9 | `SSSSuSuSuS` | `uSuSuSuSuS` | realization |
| 116.11 | `SSuSuSSSuS` | `uSuSuSuSuSu`; `uSuSuSuSuS` | baseline syllable count; realization |
| 116.12 | `uSuSSuuSuS` | `uSuSSuuSuSu` | baseline syllable count; all candidate syllable counts; fixed stress/length |
| 130.2 | `SuuSuSuSSS` | `SuuSuSuSuS` | realization |
| 130.4 | `uSuSSSuSuS` | `uSuSuSuSuS` | realization |
| 130.7 | `uSuSuSuSuS` | `uSuuSSuSuS` | fixed stress/length |
| 130.12 | `uSuSuSSuuS` | `uSuSuSuSuS` | realization |
| 130.13 | `uSuSuSuSuS` | `uSuSuSuSuSu`; `uSuSuSuSuS` | baseline syllable count; baseline stress; another candidate agrees; selected stress |
| 145.2 | `SSuSuSuS` | `uSuSuSuS` | realization |
| 145.5 | `SuuSuSuS` | `uSuSuSuS` | realization |
| 145.12 | `uSuSuSuS` | `uSuSuSuuS`; `uSuSuSuS` | baseline syllable count; baseline stress; another candidate agrees; selected stress |
| 145.14 | `uSuSSuSS` | `uSuSSuuS` | realization |

## Sources and limits

Consulted 2026-10-27 (America/Los_Angeles). The corpus edition is exclusively the Gutenberg source in [PROVENANCE.md](PROVENANCE.md); the following references inform the model discussion and do not replace its wording or lineation.

- Barbara Mowat and Paul Werstine, [Reading Shakespeare’s Language: Sonnets](https://www.folger.edu/explore/shakespeares-works/shakespeares-sonnets/reading-shakespeares-language-sonnets/). Their analysis of 2.1–4 supports the hand fixture's pyrrhic/spondaic readings and distinguishes lexical stress from sentence stress.
- Folger Shakespeare Library, [Write a sonnet](https://www.folger.edu/explore/write-a-sonnet/), for the conventional fourteen-line, rhyme-scheme and pentameter account.
- [CMUdict project](https://github.com/cmusphinx/cmudict), whose own documentation identifies the dictionary as US English and warns of errors and omissions. See [PRONUNCIATION.md](PRONUNCIATION.md) for the frozen commit and model choices.

Hand-source SHA-256: `a6b57916618c23d9699c79c3e1fc5d2fed5b5e185ca7a497b1784e85d46fafbb`.

Compared annotation SHA-256: `a1ada37e538b2c4bd2ef1e8d4775f71068f6edbe43242a21fd6040acbe8c0269`.
