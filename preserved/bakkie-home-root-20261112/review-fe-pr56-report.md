FAIL

Crossed Codex review of derekblair/formalize-everything PR #56, final head `9e2224ec3de26895fb293e1edbae6e6ac13bd7e6`, branch `texts/sonnet-form`, ticket #45. Assigned reviewer pool: chatgpt-live on bakkie; author pool: chatgpt-proton on dominic. Reviewed on 2026-11-09 Pacific / 2026-11-10 UTC. Final recorded live-state check: 2026-11-10T00:41:46Z.

The implementation and its six required verification commands pass. This is **not a merge-authorizing PASS**: item 1's mandatory live-main equality is false. There is also a review-history wording issue in the live PR body. The acknowledged incomplete linguistic milestone is not itself being treated as an undisclosed implementation defect.

Review workspace: `/home/derekblair/review-fe-pr56-codex/fresh/`, newly cloned from GitHub for this review. Evidence: `/home/derekblair/review-fe-pr56-evidence/`. No tracked repository file was modified. No install, removal, GitHub comment, PR edit, merge, or further review was arranged. All builds ran in this fresh reviewer clone. Limited read-only SSH to dominic recovered the historical renderer traceback; no author clone was built or changed.

**Findings and exact remedies**

1. **Blocking review-state mismatch.** The actual `origin/main` is `34a7ea8e45c0005494904b55a4d39384c69500d7`, not the required `34098c7573b62ae7de730573b255057a55459c31`. Exact evidence: [git-check-1.log:1](/home/derekblair/review-fe-pr56-evidence/git-check-1.log:1). Fetch and GitHub checks were repeated. The expected main is an ancestor of current main; the intervening changes concern four Rudin RCA files, not sonnet-form, and the true merge-base remains exactly the requested `fa8bcd6f…`. **Remedy:** the coordinator must explicitly reconcile/update the review's pinned live-main criterion to the current main, retaining the exact reviewed PR head and true merge-base, before relying on a PASS. Do not roll main back or change the sonnet code merely to satisfy a stale brief. This is an external gate mismatch, not a repository source defect.
2. **Review-history wording is incomplete/misleading.** The live PR body says “crossed Codex re-review,” but does not state that no prior independent review ran. Exact location: [captured PR body:58](/home/derekblair/review-fe-pr56-evidence/pr-body.md:58), last paragraph of [PR #56](https://github.com/derekblair/formalize-everything/pull/56). GitHub's review list is empty. The phase-1 rebase check is not an earlier crossed content review. **Remedy:** replace that wording with an explicit history, e.g. “No independent crossed content review ran before this final-head review. Phase-1 coordinator verification covered rebase/tree fidelity only. This first crossed review is Codex, chatgpt-live on bakkie, against author pool chatgpt-proton on dominic,” and record this report's actual verdict. This wording issue is not evidence that an earlier reviewer fabricated a PASS; the body does not explicitly claim such a PASS.

**1. Live state, workspace, and toolchain — FAIL on required main equality; other checks PASS.**

First command: `gh pr view 56 --repo derekblair/formalize-everything --json headRefOid,mergeable,mergeStateStatus,isDraft`, exit 0. The first response had GitHub's transient UNKNOWN merge fields; subsequent responses resolved to the following and remained so:

```json
{"headRefOid":"9e2224ec3de26895fb293e1edbae6e6ac13bd7e6","isDraft":true,"mergeStateStatus":"CLEAN","mergeable":"MERGEABLE"}
```

`git clone --no-hardlinks https://github.com/derekblair/formalize-everything.git /home/derekblair/review-fe-pr56-codex/fresh`, fetch of `refs/pull/56/head`, and detached checkout of the exact head all exited 0. The clone pre-existed neither this review's fetch nor its build. The parent directory was left intact.

| Measurement | Observed | Verdict |
|---|---|---|
| PR HEAD | `9e2224ec3de26895fb293e1edbae6e6ac13bd7e6` | PASS |
| GitHub state | MERGEABLE / CLEAN / draft | PASS |
| True merge-base with live origin/main | `fa8bcd6f97aa0f78c392f9fc0565022ee11eb922` | PASS |
| Live origin/main | `34a7ea8e45c0005494904b55a4d39384c69500d7` | FAIL against mandated SHA |
| `lean-toolchain` | `leanprover/lean4:v4.34.1` | PASS |
| `lake env lean --version` | `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)` | PASS, exit 0 |
| Final `git status --porcelain`; `git diff --exit-code` | empty output, exits 0 | PASS |

The pinned toolchain was already installed. The package manifest lists no external packages. Recorded live metadata and command outputs: [live-pr.json](/home/derekblair/review-fe-pr56-evidence/live-pr.json), [final-live-pr.json](/home/derekblair/review-fe-pr56-evidence/final-live-pr.json), [state-command-results.json](/home/derekblair/review-fe-pr56-evidence/state-command-results.json), [lean-version.log](/home/derekblair/review-fe-pr56-evidence/lean-version.log).

**2. Rebase fidelity — PASS.**

`git rev-parse cfdc1c78e8f12deb451df8ae8c2425a8de159a38^{tree}` gives exactly `e5e47139e7e492101ad9c3f6d69c30329ff5028c`, exit 0. The old force-pushed commits were not initially present in the fresh clone; fetching the two supplied old SHA objects succeeded. Then the exact requested command succeeded:

```sh
git range-diff b7593a842e03c909f50dda6388697a23cda18766..5b5dfa6ca05e938adc7781cbdbaa5a243abbeff3 fa8bcd6f97aa0f78c392f9fc0565022ee11eb922..cfdc1c78e8f12deb451df8ae8c2425a8de159a38
```

Recorded output: [range-diff.log](/home/derekblair/review-fe-pr56-evidence/range-diff.log). Commits 1 and 2 are `=`; commit 3 is `!` solely for the CATALOGUE context/resolution. I compared the actual row strings: checkpoint rows 28 and 29 are byte-exact main Bible/Mirath rows, and row 30 is the byte-exact original branch's reworded Sonnets row. All three are present; neither main row was dropped. The surrounding proposal section remains present. Location: [CATALOGUE.md:28](/home/derekblair/review-fe-pr56-codex/fresh/CATALOGUE.md:28).

**3. Five phase-2 commits and recomputed verdict changes — PASS.**

I inspected each commit and executed its actual pronunciation/generator source in isolated in-memory Python modules, with that commit's own override JSON and the frozen corpus/dictionary. No old source was written into the checkout. The baseline and final annotation objects were reproduced exactly, including every line's masks, scans, derivations, rhyme, and verdict. Script, inputs/hashes, outputs: [recompute.py](/home/derekblair/review-fe-pr56-evidence/recompute.py), [recomputed-verdicts.json](/home/derekblair/review-fe-pr56-evidence/recomputed-verdicts.json), [recompute.log](/home/derekblair/review-fe-pr56-evidence/recompute.log).

| Commit | Verified behavior |
|---|---|
| `db0a4da` | Adds the exact `respose` editorial override, keeps the source token, uses phones equal to pinned CMU `repose`; 27.2 gains a licensed feminine-ending reading. |
| `a9c84ab` | Adds six global lexical readings and finite `record` / `ever fixed` token-context cues. Sources and modern/historical limits are documented. Corpus masks/diagnostics and the Python validation results are regenerated consistently. |
| `f755964` | Adds `License.interiorTrochaicInversion`, its predicate/name, Python mirror, and kernel boundary checks. Interior positions are zero-based 2 or 3, at most one interior trochee, total at most two noniambic feet. |
| `e3d617d` | Requires listed determiner + `ever` + `fixed` + a following token. Bare `ever fixed`, end-of-line `an ever fixed`, and verbal `have you ever fixed this` retain fallback. No corpus verdict changes at this stage. |
| `9e2224e` | Adds source-bound historical findings/renderer/coverage checks, records open blockers and verification history. Historical evidence does not feed phonology or Lean verdicts. Corpus verdicts are unchanged from the context-guard stage. |

The resolver's only context API is `resolve_in_context(tokens, index)`; it reads the local token frame and returns a pronunciation. It receives no sonnet/line identifier, meter target, deficit, or rhyme partner. The code actually uses the finite cue lists documented in PRONUNCIATION.md. Locations: [tools/pronunciations.py:17](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/tools/pronunciations.py:17), [tools/pronunciations.py:87](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/tools/pronunciations.py:87), [tools/generate.py:70](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/tools/generate.py:70), [PRONUNCIATION.md:108](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/PRONUNCIATION.md:108). Lexical resolution is external annotation, not a Lean linguistic theorem; the resulting masks and verdict equations are checked in Lean.

The Lean meter implementation and Python mirror agree at [SonnetForm/Spec.lean:88](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/SonnetForm/Spec.lean:88) and [tools/generate.py:45](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/tools/generate.py:45). Kernel boundary theorems cover allowed third/fourth and forbidden second/fifth inversion, two-interior rejection, initial-plus-interior composition, pyrrhic/spondaic composition, budget excess, elision/feminine composition, and no license for a failed whole scan (Spec.lean:241 onward). Fixed masks remain fixed (Phonology.lean:42 onward). These theorems were built and audited, not merely read.

| Line | Before strict / licensed | Final strict / licensed | Final selected licenses |
|---|---|---|---|
| 18.2 | false / false | false / true | PYRRHIC_SUBSTITUTION |
| 116.5 | false / false | true / true | none |
| 116.7 | false / false | true / true | none |
| 130.4 | false / false | true / true | none |
| 55.8 | false / false | false / true | PYRRHIC_SUBSTITUTION |
| 19.10 | false / true | true / true | none |
| 55.3 | false / false | true / true | none |
| 19.14 | false / false | false / true | INTERIOR_TROCHAIC_INVERSION |
| 27.2 | false / false | false / true | FEMININE_ENDING |
| 53.12 | false / true | false / false | none |
| 59.5 | true / true | false / false | none |

Recomputed totals: strict gains 21 / loses 1; licensed gains 79 / loses 2. All **104 changed-line records and 19 changed-poem records**, including every before/after field and changed word pronunciation, match the committed change log; see [finish-evidence.py](/home/derekblair/review-fe-pr56-evidence/finish-evidence.py) and [final-extra-checks.json](/home/derekblair/review-fe-pr56-evidence/final-extra-checks.json). The selected interior-inversion count is 63.

Source checks were independent of the author's conclusions. Exact CMU variant equality for temperate/every/wires/contents/record and the respose→repose phones is recorded in [lexical-variant-equality.json](/home/derekblair/review-fe-pr56-evidence/lexical-variant-equality.json). The [Poetry Foundation text](https://www.poetryfoundation.org/poems/45106/sonnet-116-let-me-not-to-the-marriage-of-true-minds) supplies the marked fixed/wandering forms; [Cambridge](https://dictionary.cambridge.org/pronunciation/english/record) supplies the noun/verb stress distinction. Direct web opens initially returned 403 for these two pages; publisher-domain search reproduced their text, and a separate local HTTP fetch also recovered Cambridge. [Schmidt's scan](https://api.pageplace.de/preview/DT0400.9783112315330_A39774742/preview-9783112315330_A39774742.pdf), p.43, supports initial antique stress, and the [Audio Shakespeare guide](https://www.audioshakespearepronunciationapp.com/shakespeare-pronunciation-dictionary/) supports final contents stress. [Folger 27](https://www.folger.edu/explore/shakespeares-works/shakespeares-sonnets/read/27/) has repose. These are scoped supports, not proof of unique historical performance.

I independently downloaded and viewed [Kiparsky 1977](https://brucehayes.org/251metrics/papers/KiparskyRhythmicStructureEnglishVerse1977Shorter.pdf), p.217 example 75d, and checked [Hayes 1989](https://brucehayes.org/201A/readings/HayesProsodicHierarchy1989.pdf), pp.256–257. They support the specific ever example / positional motivation and also impose linguistic boundary conditions. The repo explicitly says those conditions are absent. Source download hashes are in [source-downloads.json](/home/derekblair/review-fe-pr56-evidence/source-downloads.json).

**4. Clean-slate six-command verification — PASS.**

`.lake` was absent before the first build in the fresh clone; there was nothing to move aside. The recorder would preserve any pre-existing directory outside the checkout. No cache download or installation occurred. Exact working directory: `/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form`. Script: [run-suite.py](/home/derekblair/review-fe-pr56-evidence/run-suite.py). All six commands ran sequentially and exited 0:

| Command | Exit | Seconds | Full recorded log | SHA-256 |
|---|---:|---:|---|---|
| `lake --no-cache build` | 0 | 11.155 | [01-review.log](/home/derekblair/review-fe-pr56-evidence/01-review.log) | `63fdf1f3f7167e7e23c492e2cdb1ff5d8adb67d493589b6d3ef3402095ecebef` |
| `python3 tools/import_corpus.py --check` | 0 | 0.040 | [02-review.log](/home/derekblair/review-fe-pr56-evidence/02-review.log) | `b3ddcda2ea15bc8595f13f5575a68ca6a667dcf1bf30a5214c90293dfe570ab7` |
| `python3 tools/generate.py --check` | 0 | 0.298 | [03-review.log](/home/derekblair/review-fe-pr56-evidence/03-review.log) | `8f0f715f837db250f519da8dd1736e113cba642c61f3128fc55781bb988287dc` |
| `python3 tools/validate_scansion.py --check` | 0 | 0.072 | [04-review.log](/home/derekblair/review-fe-pr56-evidence/04-review.log) | `2adad77d73d02487ce5b8370e93a256b1ab4244a9966a25af78ba72805bfc949` |
| `python3 tools/check_model.py` | 0 | 0.234 | [05-review.log](/home/derekblair/review-fe-pr56-evidence/05-review.log) | `54a747705850e51ae7e7d66ab34c9545fddc1997036cd41cec2b528ba34b6888` |
| `python3 tools/audit_axioms.py` | 0 | 0.300 | [06-review.log](/home/derekblair/review-fe-pr56-evidence/06-review.log) | `e833d4662997b25b96c3dcfb976c7ffd75c4dd69e0ffe8fc0ec51cf5bfc61cca` |

Exact outputs are included at the end of this report. The fresh build completed 19 jobs in 11.155 seconds. Its log hash differs from the author's because task timings and parallel completion order are nondeterministic; that is not a proof discrepancy. The committed final-retry build log itself hashes exactly to `67a5acf7b5a4d2c2db36998e1951584f7e992548481251ca7e107d4c01493df6`. Both the committed audit log and my audit summary hash to `e833d4662997b25b96c3dcfb976c7ffd75c4dd69e0ffe8fc0ec51cf5bfc61cca`.

All 39 command records in the seven forward-fix stage directories have log bytes matching their recorded SHA-256 values. All seven recorded Lean builds have exit 0. The only nonzero recorded suite command is phase2-final's generator freshness check, exit 1 for stale DEVIATIONS.md. See [recorded-log-validation.json](/home/derekblair/review-fe-pr56-evidence/recorded-log-validation.json).

The disclosed TypeError is real in the retained author task trace: `tools/rhyme_review.py:118`, `TypeError: string indices must be integers, not 'str'`, reached through `generate.py:268` after the historical evidence dictionary was shadowed by a line-meter evidence string. I retrieved the relevant trace read-only from the recorded dominic task path; [author-failure-excerpt.log](/home/derekblair/review-fe-pr56-evidence/author-failure-excerpt.log) retains it. I also reversed just the two variable-name changes in memory and reproduced the same TypeError without modifying a repository file; [renderer-reproduction.log](/home/derekblair/review-fe-pr56-evidence/renderer-reproduction.log). Final source uses `historical_evidence` at [tools/generate.py:226](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/tools/generate.py:226) and [tools/generate.py:268](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/tools/generate.py:268). The committed phase2-final/03-generate.log contains the later stale-output AssertionError, not the earlier TypeError; those are separate failures in the disclosed chronology.

No Lean failure appears in the inspected retained build records or relevant author trace, and this review's clean build passed. “No Lean build ever failed” is verified within that retained evidence scope; no finite log review can certify absent/unrecorded executions.

**5. Axiom audit and every theorem output — PASS.**

The actual census is **219 named project theorem declarations**, found independently after lexical stripping. There are **zero literal `#print axioms` commands in the sonnet Lean source files**; the Python audit constructs them dynamically. I generated an external driver containing all 219 commands and executed `lake env lean /home/derekblair/review-fe-pr56-evidence/PrintAllAxioms.lean`, exit 0. Driver: [PrintAllAxioms.lean](/home/derekblair/review-fe-pr56-evidence/PrintAllAxioms.lean); complete raw output: [print-all-axioms.log](/home/derekblair/review-fe-pr56-evidence/print-all-axioms.log), SHA-256 `c907a868817fcadcc993093a341e8577e5b4c654f2151f4d46933db6bfe47ce5`.

Every individual result matches `verification/axiom-audit.json`, and the full raw output is byte-identical to `verification/axiom-audit.txt`. All 219 use propext; exactly two also use Quot.sound: `SonnetForm.realizeFrom_compatible` and `SonnetForm.realizeStress_compatible`. **Classical.choice usage is zero.** No theorem depends on sorryAx, native reduction axioms, or another unapproved axiom. Full per-theorem findings: [independent-axioms.json](/home/derekblair/review-fe-pr56-evidence/independent-axioms.json). There is no separate named “pin manifest” in this package; lean-toolchain, the empty dependency manifest, README's allowed-axiom policy, ticket #45, and the exhaustive axiom-audit JSON provide the relevant pins/census. I audited the entire census, not just selected headline theorems.

**6. Lexical trust-escape screen / Annex C — PASS for the solution; brief's raw count not reproduced.**

[screen.py](/home/derekblair/review-fe-pr56-evidence/screen.py) strips nested block comments, line comments and string literals while preserving newlines and positions. It follows local imports from SonnetForm.lean; [toolchain-closure.py](/home/derekblair/review-fe-pr56-evidence/toolchain-closure.py) additionally follows the pinned Init/Std imports (including implicit Init and `import all`). The complete closure is 1,155 source modules: 17 project modules and 1,138 installed toolchain modules; no missing import remained.

Each of the eight required whole-word tokens has count **0 in every project module**. Counts by token and file, including the toolchain boundary, are attached as [lexical-counts-by-file.md](/home/derekblair/review-fe-pr56-evidence/lexical-counts-by-file.md) and included below. Complete paths/positions are in [full-import-closure-screen.json](/home/derekblair/review-fe-pr56-evidence/full-import-closure-screen.json). The pinned core has expected implementation/syntax primitives: sorry=6, admit=0, sorryAx=1, axiom=15, native_decide=0, ofReduceBool=1, implemented_by=36, unsafe=59. These are explicitly explained, not ignored: the six sorry tokens are tactic quotation/syntax definitions in Init.Tactics, Init.TacticsExtra and Init.Grind.Interactive; Init.Prelude defines the core sorryAx/choice/quotient/runtime primitives; Init.Core defines propext and native-reduction/trust primitives; the remaining unsafe/implemented_by sites implement standard runtime data/IO operations. None is a PR-added escape. The exhaustive theorem dependency output above shows that only propext and Quot.sound reach these 219 proofs.

The supplied **117 raw sorry hits in changed Lean files is not reproducible** from the live commits. `git diff fa8bcd6f..HEAD -- '*.lean'` contains exactly **one** matching line: [SonnetForm/Corpus.lean:338](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/SonnetForm/Corpus.lean:338), the original verse string “Make glad and sorry seasons as thou fleets,” removed by the string-literal strip. It is neither a proof hole nor a challenge placeholder. The final tracked repository has seven matching lines / nine substring occurrences, all classified in [raw-sorry-classification.json](/home/derekblair/review-fe-pr56-evidence/raw-sorry-classification.json):

| File:line | Raw substring occurrences | Classification |
|---|---:|---|
| software/sonnet-form/SonnetForm/Corpus.lean:338 | 1 | Frozen verse string |
| software/uri-rfc3986/UriRfc3986/Checks.lean:7 | 1 | Block-comment prose, outside solution closure |
| software/sha256-bridge/Sha256Bridge/Audit.lean:197 | 1 | Identifier `sorryReach`, outside closure, not whole-word sorry |
| software/sha256-bridge/Sha256Bridge/Audit.lean:212 | 1 | Quoted constant name `sorryAx` used to detect forbidden dependencies, outside closure |
| software/sha256-bridge/Sha256Bridge/Audit.lean:213 | 2 | `sorryReach` identifier occurrences, outside closure |
| software/sha256-bridge/Sha256Bridge/Audit.lean:222 | 1 | `sorryReach` identifier, outside closure |
| software/sha256-bridge/Sha256Bridge/Audit.lean:224 | 2 | Interpolated diagnostic string, outside closure |

I also checked fa8bcd6f, the rebase checkpoint, original branch head, the expected main and current main; none has 117 matching tracked Lean lines. Full revision-level classifications: [raw-sorry-by-revision.json](/home/derekblair/review-fe-pr56-evidence/raw-sorry-by-revision.json). The import closure including pinned library sources has 61 raw matching lines, also not 117. There are no unclassified project hits and no frozen challenge proof placeholders in this solution. The exact raw command/file list behind the coordinator's 117 would be needed to identify a different scope; I do not invent classifications for nonexistent matches or use that raw number as an assurance result.

**7. Diff hygiene and frozen-file fidelity — PASS, with the diff algorithm made explicit.**

This machine has `diff.algorithm=histogram`. Therefore the literal default `git diff --stat fa8bcd6f..9e2224e` gives **116 files, +558,004/-22**. `git diff --stat --diff-algorithm=myers fa8bcd6f..9e2224e` gives the brief's exact **116 files, +558,006/-24**, exit 0. This is line-alignment accounting, not changed bytes or a different head. Both outputs were recorded.

`git diff --check fa8bcd6f..9e2224e` exits **2** and emits exactly **6,012 lines**, SHA-256 `04c50f24a06dfec1064d8a54f6b2845865a80358b8b0810655e4066fbd5613b8`. All diagnostics are confined to vendored data: 3,005 Gutenberg trailing-whitespace findings, one Gutenberg new-blank-line-at-EOF finding, and one cmudict-README new-blank-line-at-EOF finding. Thus the brief's hash matches exactly; its prose omitted the extra Gutenberg EOF diagnostic. Full output: [diff-check.log](/home/derekblair/review-fe-pr56-evidence/diff-check.log). `git diff --check cfdc1c7..9e2224e` exits **0**, empty output.

I compared actual frozen bytes at cfdc1c7 with final-head bytes and the fidelity.json claimed hashes. All nine records are byte-identical and all hashes match:

| Frozen file | SHA-256 |
|---|---|
| `data/gutenberg-1041.txt` | `4a3a5466591e30ca93b2c19daeb24770bb08833b57b1616c972b97246e23580f` |
| `data/cmudict.dict` | `81917843c7f44ce2b094ac63873c2c7a4cf802040792c455ba3ca406891c3d22` |
| `data/cmudict-source.json` | `4a3449846be4ebfc47c68125f30be456af1b7bf18decdc145352893eb91c8a0d` |
| `data/corpus-manifest.json` | `83d23bd11652c395b575c863efedb8cb586d4dfa7b12b9282d333c45772722a6` |
| `data/sonnets.json` | `04a445b7ad225a9b0e19328f02e453b2986440a62600e108e179648123225dc2` |
| `data/validation-scans.tsv` | `a6b57916618c23d9699c79c3e1fc5d2fed5b5e185ca7a497b1784e85d46fafbb` |
| `data/validation.json` | `e646ff6edfeb8eb72026cad5adc08678a728d929caecc04048121c0671caa962` |
| `lean-toolchain` | `d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b` |
| `lake-manifest.json` | `b9c0c6f5173f69141534c4e2c7062764166aeb26ec227152402ec66c46ea9c23` |

Full independent result: [independent-fidelity.json](/home/derekblair/review-fe-pr56-evidence/independent-fidelity.json). Source parsing additionally checks every verse against the frozen Gutenberg text, with only declared outer layout whitespace removed. No source token was repaired to make a check pass.

**8. Content, retained blockers, validation, and status — PASS on computational/content claims; review wording issue remains.**

The historical review was recomputed from the baseline annotations reproduced from baseline code, not accepted from its summary fields. All 133 original failed sonnets and their exact baseline rhyme vectors match. There are 236 unequal intended-pair constraints and 83 cross-class collisions (319 pair constraints), plus the two structural exceptions. Recounting nonempty open questions gives **163** constraints across **81** sonnets; the rendered DEVIATIONS is freshly regenerated by `--check` and matches the JSON. Whole-scheme statuses are 116 `not_established`, 15 `impossible_under_context_free_exact_classes`, and 2 `excluded_by_line_count`: **zero validated complete historical schemes**. See [historical-recomputation.json](/home/derekblair/review-fe-pr56-evidence/historical-recomputation.json), [HISTORICAL-RHYME.md:9](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/HISTORICAL-RHYME.md:9) and [MILESTONE1-STATUS.md:8](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/MILESTONE1-STATUS.md:8).

| Constraint category | Observed count |
|---|---:|
| Scholarly pair support | 131 |
| Scholarly rule/form inference | 8 |
| Partial support | 2 |
| Modern variant only | 2 |
| Scholarly imperfect analysis | 5 |
| Scholarly disagreement | 1 |
| Open unequal pair | 87 |
| Same-token cross-class obstruction | 21 |
| Scholarly repeated class | 4 |
| Open modern cross-class collision | 58 |

The open total is 87+8+2+2+5+1+58=163. Pair support is not a reconstruction of seven coherent historical classes. The context-free distinctness obstructions are explicitly conditional on that lookup policy, not universal claims about context-sensitive performance.

I independently retrieved the cited Crystal and Viëtor PDFs; their hashes match the JSON snapshots exactly. Crystal's discussions and appendix support the cited pair families; the source's numbering/wording mismatches are retained as inferences, and costs/boast retains its consonantal question. Viëtor's cited sections support the distinctions among attested pair discussion, partial syllabification evidence, doubtful spirit/merit, quantity disagreement, and imperfect/assonantal readings; his index's rhyme-driven transcriptions are not counted as independent phonetic validation. The appendix supports brow/mow and the 105 alone/one relation even where the prose has a different spelling/number list. [Crystal](https://www.davidcrystal.com/Files/BooksAndArticles/-4836.pdf), [Viëtor](https://archive.org/details/shakespearespron00virich). The narrowly used repeated-rhyme observation for 46/134 is present in [Delmonte §3.2.3](https://www.mdpi.com/2078-2489/14/10/576); the 99/126 structural observations are present in [Folger](https://www.folger.edu/explore/shakespeares-works/shakespeares-sonnets/reading-shakespeares-language-sonnets/).

The regressions are concrete: [SonnetForm/Corpus.lean:957](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/SonnetForm/Corpus.lean:957) (53.12) has one nine-syllable reading after two-syllable every while blessed stays monosyllabic, so licensed=false. [SonnetForm/Corpus.lean:1058](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/SonnetForm/Corpus.lean:1058) (59.5) realizes `uSSuuSuSuS`; its second foot is a forbidden trochee, so licensed=false. Both are explained at [PRONUNCIATION.md:235](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/PRONUNCIATION.md:235) and retained in the data/audit rather than rescued by a line-specific override.

Phrase/proclitic conditions are unimplemented: Scan contains only stresses and an optional elision; no phrase-boundary field/check exists. This matches [SPEC.md:120](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/SPEC.md:120) and MILESTONE1-STATUS.md:9. The hand fixture is unchanged and explicitly called author-agent, purposive, and a development/regression sample rather than held-out historical validation ([VALIDATION.md:5](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/VALIDATION.md:5), [VALIDATION.md:47](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/VALIDATION.md:47)). The exact fresh measurements are 137/154 baseline syllables, 143/154 any-candidate syllables, 77/154 selected exact stress, 79/154 any-candidate exact stress, 128/154 fixed-stress compatibility, 149/154 line-family agreement and 8/11 poem agreement.

MILESTONE1-STATUS and the PR's counts/blocker claims match the actual files. Both retain the incomplete milestone, open historical model, unencoded phrase conditions, and regressions. The only PR-history wording finding is the “re-review” paragraph identified above.

**9. Strength delta / Annex D — conditional formal result PASS; linguistic milestone is partial.**

The intended result in ticket #45 is a faithful full-corpus form/conformance formalization with a stated scansion validation sample. The strongest proved result here is the equality of the actual computed audit for all 154 frozen annotated sonnets with the complete expected table: [SonnetForm/Audit.lean:25](/home/derekblair/review-fe-pr56-codex/fresh/software/sonnet-form/SonnetForm/Audit.lean:25), supplemented by numbering, 99/126/145 calibration, aggregate counts/failure lists and realization-preservation theorems. That is exact for this fixed data and this specification. It is not a theorem that all 154 poems satisfy the model; the table proves their positive and negative verdicts separately.

Relative to a reliable historical conformance claim it is **weaker / partial**, not equal: modern phoneme tails and lexical choices remain assumptions; monosyllables are flexibly realized toward an alternating template; only a finite set of readings/licenses is considered; exact rhyme demands seven distinct classes; the one-interior/two-substitution bounds are chosen restrictions; phrase/proclitic conditions are missing; no complete historical rhyme scheme is validated. These limitations can cause both acceptance of historically unjustified stress patterns and rejection of defensible performances. No exponent/rate comparison applies to this finite linguistic artifact.

The PR's final sentence fairly states the annotation dependence and absence of unique historical performance/full historical-rhyme certification. SPEC.md:3, SPEC.md:120, README.md's “What this does NOT show,” HISTORICAL-RHYME.md:3/26, and VALIDATION.md's regression label make the same boundary explicit. I found **no additional overstatement of what the kernel proved** in those final claims. The review-history wording issue is separate from mathematical strength. No unpublished assumption is being promoted into a historical theorem.

**Annex A — recorded-output evidence: satisfied for the computational review.**

This report links full build logs with exact commands/exits/hashes, all 219 actual axiom outputs, recomputation scripts with their source/data hashes and output values, and frozen-file checks. The source/pin binding is [all-project-sha256.json](/home/derekblair/review-fe-pr56-evidence/all-project-sha256.json) (SHA-256 `29e691d3609958b47facf80d1fd8c8645a3820f213cd4e3e7fb666000fa4a048`), which records the exact final Git head, `leanprover/lean4:v4.34.1`, and SHA-256 for all 117 tracked package files. The 17-module closure source hashes are also in [source-sha256.json](/home/derekblair/review-fe-pr56-evidence/source-sha256.json). Key source hashes:

| Module | SHA-256 |
|---|---|
| `SonnetForm/Spec.lean` | `99f37f90c4775d7cf75c4876233d438341d2981c0c570bf193561ac6fbe6072c` |
| `SonnetForm/Phonology.lean` | `d1530d5e1ee2344bda0680d97b9906e43bdf2a5b42b76f24f48e9360d504928e` |
| `SonnetForm/Corpus.lean` | `4e90f2b7b9696f29ef5e46c13b2a5fdca9df80d50cf8ee0f04268ae50dec1060` |
| `SonnetForm/AuditTypes.lean` | `3ae12abf50c948e330c72d7edee04247e94e678bca76a68b962123578734ed99` |
| `SonnetForm/Audit.lean` | `44e7d421fdcc416dedf2e35eb85feae39545462ed039b638814cbf866d720d88` |

**Annex B — vacuity and hidden assumptions: CLEAR for the stated conditional result.**

- **Hidden hypotheses in data types — CLEAR.** Scan, Line and Sonnet (Spec.lean:14/21/27) contain explicit data, not proof fields assuming conformance. Annotations are an openly stated trust boundary. Verdict stores each Boolean; a positive branch is not supplied as a field assumption. AuditRow/LineDiagnostic likewise hold data, and the equality proof checks it.
- **Vacuous branches doing the real work — CLEAR.** Empty scans fail existential line meter (Spec.lean:152); empty poems fail meter through the nonempty guard (Spec.lean:179/182); rhyme requires length 14 and nonempty present classes (Spec.lean:169). `empty_poem_fails_all_components`, missing/empty rhyme tests and unknown-annotation tests are kernel-checked. The full-table theorem includes 154 actual sonnets / 2,155 actual lines, not an empty corpus. Passing nonempty cases execute the actual finite predicates; they are not discharged by an impossible premise.
- **Regularity/positivity asserted instead of constructed — CLEAR / not a real-analysis obligation here.** The relevant analogous obligations are syllable/mask lengths, fixed-stress compatibility and finite readings. Phonology.lean:42–61 proves compatibility and length preservation by induction. The proof does not assert linguistic correctness of phonemes; that remains explicitly external.
- **Quantifier order / constants / oracle — CLEAR for the declared model.** Per-line meter is existential over the supplied finite readings, while poem meter is universal over all actual nonempty lines. Constants (five feet, allowed positions, one interior trochee, two noniambic feet, one indexed weak elision) are fixed in definitions before data. No sonnet-number, desired result, rhyme-partner or deficit argument reaches lexical choice. The fixed corpus-specific lexical policy was informed by a development sample; it is not claimed to be held-out validation or a universal historical algorithm.

**Annex E — provenance honesty: wording correction required.**

GitHub has no prior submitted reviews in the retrieved metadata. The repo calls its historical investigation author-side scholarship; VALIDATION.md states that the author lane appointed/consulted no independent reviewer, and MILESTONE1-STATUS.md identifies the forward fix as not a crossed review. The author report's internal/support review is not an independent crossed gate. There is no observed false claim that a prior independent review passed; however, the PR's “re-review” wording and absent explicit first-review history do not meet this brief's requested disclosure. Remedy is finding 2, without retroactively crediting rebase verification as a content review.

**Recorded lexical counts by file.**

| Module | Scope | sorry | admit | sorryAx | axiom | native_decide | ofReduceBool | implemented_by | unsafe |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Init.Core | pinned Lean core/Std | 0 | 0 | 0 | 4 | 0 | 1 | 0 | 0 |
| Init.Data.Array.Attach | pinned Lean core/Std | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 1 |
| Init.Data.Array.Basic | pinned Lean core/Std | 0 | 0 | 0 | 0 | 0 | 0 | 7 | 8 |
| Init.Data.Array.BasicAux | pinned Lean core/Std | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 1 |
| Init.Data.ByteArray.Basic | pinned Lean core/Std | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 2 |
| Init.Data.FloatArray.Basic | pinned Lean core/Std | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 2 |
| Init.Data.List.Attach | pinned Lean core/Std | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 1 |
| Init.Data.List.BasicAux | pinned Lean core/Std | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 1 |
| Init.Data.Option.Attach | pinned Lean core/Std | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 1 |
| Init.Data.Repr | pinned Lean core/Std | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 |
| Init.Data.Vector.Attach | pinned Lean core/Std | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 1 |
| Init.Dynamic | pinned Lean core/Std | 0 | 0 | 0 | 0 | 0 | 0 | 4 | 5 |
| Init.Grind.Interactive | pinned Lean core/Std | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Init.Prelude | pinned Lean core/Std | 0 | 0 | 1 | 11 | 0 | 0 | 4 | 15 |
| Init.ShareCommon | pinned Lean core/Std | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 7 |
| Init.System.IO | pinned Lean core/Std | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 4 |
| Init.System.ST | pinned Lean core/Std | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 4 |
| Init.Tactics | pinned Lean core/Std | 3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Init.TacticsExtra | pinned Lean core/Std | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Init.Util | pinned Lean core/Std | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 6 |
| Init.WFExtrinsicFix | pinned Lean core/Std | 0 | 0 | 0 | 0 | 0 | 0 | 3 | 0 |
| Init.While | pinned Lean core/Std | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 |
| SonnetForm | PR solution | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| SonnetForm.Audit | PR solution | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| SonnetForm.AuditPart01 | PR solution | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| SonnetForm.AuditPart02 | PR solution | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| SonnetForm.AuditPart03 | PR solution | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| SonnetForm.AuditPart04 | PR solution | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| SonnetForm.AuditPart05 | PR solution | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| SonnetForm.AuditPart06 | PR solution | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| SonnetForm.AuditPart07 | PR solution | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| SonnetForm.AuditPart08 | PR solution | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| SonnetForm.AuditPart09 | PR solution | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| SonnetForm.AuditPart10 | PR solution | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| SonnetForm.AuditPart11 | PR solution | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| SonnetForm.AuditTypes | PR solution | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| SonnetForm.Corpus | PR solution | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| SonnetForm.Phonology | PR solution | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| SonnetForm.Spec | PR solution | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

All other 1,116 pinned toolchain source modules have zero counts for all eight tokens; the JSON contains their individual rows too.

**Exact six-command outputs observed.**

`lake --no-cache build` — exit 0; full log [01-review.log](/home/derekblair/review-fe-pr56-evidence/01-review.log):

```text
✔ [2/19] Built SonnetForm.Spec (1.5s)
✔ [3/19] Built SonnetForm.Phonology (290ms)
✔ [4/19] Built SonnetForm.Corpus (3.3s)
✔ [5/19] Built SonnetForm.AuditTypes (277ms)
✔ [6/19] Built SonnetForm.AuditPart08 (3.4s)
✔ [7/19] Built SonnetForm.AuditPart10 (3.5s)
✔ [8/19] Built SonnetForm.AuditPart11 (3.7s)
✔ [9/19] Built SonnetForm.AuditPart01 (3.8s)
✔ [10/19] Built SonnetForm.AuditPart02 (3.8s)
✔ [11/19] Built SonnetForm.AuditPart04 (3.8s)
✔ [12/19] Built SonnetForm.AuditPart09 (3.9s)
✔ [13/19] Built SonnetForm.AuditPart05 (3.9s)
✔ [14/19] Built SonnetForm.AuditPart03 (3.0s)
✔ [15/19] Built SonnetForm.AuditPart07 (3.0s)
✔ [16/19] Built SonnetForm.AuditPart06 (4.1s)
✔ [17/19] Built SonnetForm.Audit (1.4s)
✔ [18/19] Built SonnetForm (176ms)
Build completed successfully (19 jobs).
```

`python3 tools/import_corpus.py --check` — exit 0; full log [02-review.log](/home/derekblair/review-fe-pr56-evidence/02-review.log):

```text
PASS: 154 sonnets; 2155 verse lines; source SHA-256 and every normalized verse line verified
Line-count distribution: 152 × 14; sonnet 99 = 15; sonnet 126 = 12
```

`python3 tools/generate.py --check` — exit 0; full log [03-review.log](/home/derekblair/review-fe-pr56-evidence/03-review.log):

```text
{
  "sonnets": 154,
  "lines": 2155,
  "line_count": {
    "pass": 152,
    "fail": 2
  },
  "rhyme": {
    "pass": 21,
    "fail": 133
  },
  "strict_meter": {
    "pass": 1,
    "fail": 153
  },
  "licensed_meter": {
    "pass": 47,
    "fail": 107
  },
  "line_strict": {
    "pass": 1248,
    "fail": 907
  },
  "line_licensed": {
    "pass": 1960,
    "fail": 195
  },
  "unresolved_lines": 0,
  "licenses": {
    "INITIAL_TROCHAIC_INVERSION": 98,
    "INTERIOR_TROCHAIC_INVERSION": 63,
    "FEMININE_ENDING": 261,
    "PYRRHIC_SUBSTITUTION": 251,
    "SPONDAIC_SUBSTITUTION": 230,
    "UNSTRESSED_ELISION": 32
  }
}
CHECKED 17 files
```

`python3 tools/validate_scansion.py --check` — exit 0; full log [04-review.log](/home/derekblair/review-fe-pr56-evidence/04-review.log):

```text
Hand fixture: 11 complete sonnets, 154 lines
Baseline syllable count: 137/154
Any supplied reading: syllable count: 143/154
Baseline complete stress sequence: 77/154
Any supplied reading: complete stress sequence: 79/154
Selected reading: complete stress sequence: 77/154
Fixed lexical stresses compatible with hand reading: 128/154
Licensed-meter verdict versus hand verse family: 149/154
Whole-poem verdict agreement: 8/11
```

`python3 tools/check_model.py` — exit 0; full log [05-review.log](/home/derekblair/review-fe-pr56-evidence/05-review.log):

```text
................
----------------------------------------------------------------------
Ran 16 tests in 0.137s

OK
```

`python3 tools/audit_axioms.py` — exit 0; full log [06-review.log](/home/derekblair/review-fe-pr56-evidence/06-review.log):

```text
PASS: 219 theorems audited; axioms used: ['Quot.sound', 'propext']; no prohibited source tokens
```

**Merge disposition: PR #56 may not merge on this report.** It is a draft and this verdict is FAIL because the mandated live-main gate is not met; the PR-history wording also needs correction. All six computational checks and the conditional-model review pass, but this report supplies no independent PASS for the coordinator's merge rule. The coordinator owns disposition after reconciling the stated findings. This reviewer has neither merged nor arranged another review.
