# Milestone 1 execution record

Scope: [issue #47](https://github.com/derekblair/formalize-everything/issues/47)
and the coordinator's `/tmp/build-bible-numbers-codex.md` brief.
Author pool: ChatGPT/Codex. Branch: `texts/bible-numbers-m1`.
Independent crossed review is reserved for the coordinator; this lane does not
appoint a reviewer or merge.

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
