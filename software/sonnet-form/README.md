# Shakespeare sonnets: an executable form model and full-corpus audit

**Draft milestone 1 for [ticket #45](https://github.com/derekblair/formalize-everything/issues/45).**
All 154 sonnets from one frozen Gutenberg edition are encoded, and all component
verdicts and line diagnostics are kernel-checked. The linguistic model remains
an explicitly limited baseline: the validation sample exposes syllabification,
contextual stress, and substitution-scope failures. This does not establish
historical poetic conformance. See the exact blockers below.

Pure Lean, pinned to `leanprover/lean4:v4.34.1`, without Mathlib. Proofs use
kernel `decide` and ordinary theorem composition. There are no proof holes,
new axioms, or native-evaluation proofs.

## Reproduce

Use the already installed pinned toolchain and Python 3 standard library:

```sh
cd software/sonnet-form
lake clean
lake build
python3 tools/import_corpus.py --check
python3 tools/generate.py --check
python3 tools/validate_scansion.py --check
python3 tools/check_model.py
python3 tools/audit_axioms.py --write
```

No downloads or package installations are needed. `lake build` imports the
whole corpus audit through `SonnetForm.lean`. The source check compares every
verse line with the frozen edition. The generator check compares all committed
Lean data, expected audit rows, annotations, counts, and the deviation catalogue
with a fresh generation. The expected audit rows are proved equal to the Lean
specification; Python output alone is not the verification claim. The axiom
script invokes `#print axioms` on every project theorem and rejects dependencies
outside `propext`, `Classical.choice`, and `Quot.sound`.

To regenerate after an intentional annotation change, run the same Python
commands without `--check`, rebuild Lean, and inspect the changed catalogue and
validation disagreements. The manual validation TSV must not be rewritten to
make the model look more accurate.

## What is checked

- Exactly 14 verse lines, with no repair license.
- Exact phonetic equality signature ABAB CDCD EFEF GG, including distinct
  A–G classes; no rhyme repair license.
- Strict iambic pentameter, and separately pentameter with named initial
  and third/fourth-foot interior inversion, feminine ending, pyrrhic/spondaic substitution, and eligible
  unstressed-elision rules. At least three of the five feet must be iambs.
- All 154 per-sonnet rows, every line's verdict and license list, selected
  stress/elision evidence, and rhyme class. The aggregate theorem
  `SonnetForm.full_table_checked` assembles the complete table. Further
  theorems check corpus numbering, summary counts, anomaly lists, and the
  99/126/145 calibration cases.

| Component | Passing sonnets | Failing sonnets |
|---|---:|---:|
| Line count | 152 | 2 |
| Rhyme under the recorded phonology | 21 | 133 |
| Strict meter | 1 | 153 |
| Meter with licenses | 47 | 107 |

At line level, 1,248/2,155 pass strict meter and 1,960/2,155 pass with licenses.
A failed check is catalogued as **ANOMALOUS under this model**, not automatically
as a literary anomaly. Every strict meter failure rescued by a named rule is
**LICENSED**, including licensed lines inside otherwise failing sonnets.

Required calibration: 99 has 15 lines; 126 has 12; 145 has 14 lines, all rejected
as pentameter. Every line of 145 has an eight-syllable reading in the supplied
model (145.12 uses the explicitly recorded contraction of _heaven_). No poem
text was changed to obtain these results.

## Evidence map

- [SPEC.md](SPEC.md): named modeling decisions, license predicates, assurance boundary.
- [PROVENANCE.md](PROVENANCE.md): sole edition, frozen bytes, retrieval date,
  source hash, extraction rules, and all fidelity events.
- [PRONUNCIATION.md](PRONUNCIATION.md): pinned CMU source, explicit lexical
  overrides, modern pronunciation assumptions, and explicit source-token interpretations.
- [DEVIATIONS.md](DEVIATIONS.md): all 154 rows, complete anomaly lists, and every
  failing component/line with a LICENSED or ANOMALOUS classification.
- [VALIDATION.md](VALIDATION.md): 11 full sonnets / 154 hand-scanned lines,
  all comparison metrics and disagreements, and references.
- `data/annotations.json`: token-by-token pronunciation derivations, masks,
  finite readings, and results; original poem strings remain intact.
- `verification/`: clean build/check logs and exhaustive axiom census.

## Exact blockers to a completed linguistic milestone

The eleven-sonnet sample was hand-scanned by an author-agent before examining
machine output; it is not independent human validation. Baseline syllable
counts agree on 137/154 lines; supplied alternatives raise this to 143/154.
Exact selected stress agrees on 77/154, and any candidate on 79/154. Meter-family
verdicts agree on 149/154 lines but only 8/11 complete poems. Genuine rhetorical
ambiguity explains some stress differences, but it does not explain all errors:
_temperate_ (18.2), _record_ (55.8), _fixed_ (116.5), _every/wandering_ (116.7),
and _wires_ (130.4), plus _antique_ and _contents_, now have explicit sourced
lexical/context annotations in PRONUNCIATION.md. Their improved agreement is
development-sample regression evidence; it is not independent validation.

Modern American first-pronunciation rhyme classes also reject 133 sonnets;
these are not established historical rhyme anomalies. A contextual/historical
pronunciation and stress annotation pass, with justified additional licenses
where needed, is required before claiming reliable literary conformance.
The edition's `respose` at 27.2 is preserved and has an explicit, sourced
pronunciation alias to _repose_; see PRONUNCIATION.md.
The complete formal baseline is supplied for coordinator-appointed review;
this author lane neither arranges that review nor merges.

## What this does NOT show

The kernel cannot certify that an Internet edition is authoritative, that a
lexical dictionary describes Shakespeare's accent, that the chosen stress is
the unique right reading, or that the selected finite licenses capture every
accepted poetic practice. It proves exact facts about recorded data under a
named model. No claim of complete historical scansion, phonetic truth, or
independent scholarly validation is made.
