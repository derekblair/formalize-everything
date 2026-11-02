# Milestone 1 execution record

Scope: [issue #47](https://github.com/derekblair/formalize-everything/issues/47)
and the coordinator's `/tmp/build-bible-numbers-codex.md` brief.
Author pool: ChatGPT/Codex. Branch: `texts/bible-numbers-m1`.
Independent crossed review is reserved for the coordinator; this lane does not
appoint a reviewer or merge.

## Checkpoints

- `74da011`: sourced datasets/provenance committed and pushed. Verified 360
  provenance coordinates against generated Lean; `lake build BibleNumbers.Data`
  exited 0. All 298 populated cells and twelve bridge inputs have sources.
- `5f8ff66`: totals and divergence committed and pushed: six profiles, both Terah endpoint scenarios, exact
  lists for all fifteen unordered profile pairs, and the systematic offsets.
  Missing requested ages are proved to invalidate a sum. No data were changed
  to reproduce a printed source total.
- Jubilee arithmetic: both period readings, recursive sabbatical counting,
  drift/alignment, the common-multiple characterization and minimum 2450.
  Numbered jubilee years start at 50; their next shared label is 2500.
  The requested drift model uses a continuous sabbatical reference grid and
  does not claim to implement a calendar that restarts the grid after jubilee.
- The complete fidelity-event record is in `PROVENANCE.md` and
  `JUBILEE-SOURCES.md`; the final checkout report is `../../REPORT.md`.
- Resumed 2026-11-02 UTC after the reboot. The required checkpoint matched
  exactly: branch `texts/bible-numbers-m1`, HEAD `5f8ff66`, eight dirty entries.
  The session transcript confirmed `gpt-6-astra` at `ultra` effort. All
  preserved changes were read before new edits; no work was discarded and
  main was neither merged nor rebased into this branch.
- Final validation 2026-11-02 UTC: `python3 scripts/generate_data.py --check`
  exited 0. The previous `.lake` directory was moved intact to
  `/tmp/bible-numbers-validation-20261102-szprwzff/preserved-lake`; with no
  package build cache present, `lake build` exited 0 (8 jobs) under Lean
  4.34.1. The default-target audit passed for 733 declarations across five
  imported project modules plus the import-only audit entrypoint (six source
  modules total), using only `propext`, `Classical.choice`, and `Quot.sound`.
  The build log and exit code are preserved in that validation directory.

## Implementation sequence

1. Source and encode named witness datasets with a cell-level provenance table;
   push the datasets/provenance checkpoint.
2. Prove totals and exhaustive divergence tables and patterns;
   push the totals/divergence checkpoint.
3. Prove the two jubilee readings and import the environment axiom audit;
   push the jubilee checkpoint.
4. Perform a clean build, report source fidelity findings, and open the PR.

## Fidelity decisions

- Theorems concern finite encoded datasets and explicitly chosen chronological
  endpoint conventions. They do not adjudicate textual priority or historicity.
- Genesis 11:26's 70 and the inferred 130-year Terah chronology must remain
  distinct. Smith (2018), Table 4 notes D–F, discusses both. No raw cell will be
  changed to force an author's printed total.
- Missing witness entries, source conjectures, and unpublished/unsourced numbers
  must not silently become ordinary numeric observations.

## Validation contract

Lean is pinned to `leanprover/lean4:v4.34.1`. Use pure Lean/Std, no Mathlib,
no admitted proofs, no native decision trust. The build must import an audit
of all project declarations, including generated/private declarations, allowing
only `propext`, `Classical.choice`, and `Quot.sound` transitively.
