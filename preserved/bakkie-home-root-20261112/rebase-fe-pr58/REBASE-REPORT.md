# PR #58 rebase report — STOPPED, NOT PUSHED

Owner: Derek Blair. Repository: `derekblair/formalize-everything`.
Task directory: `/home/derekblair/rebase-fe-pr58-codex`.
Recorded stop time: `2026-11-10T02:06:59.540564+00:00`.

The mandatory Lean-conflict stop condition fired at replay **5 of 7**, commit
`50584052c55c8546d9837a3297fa0f38aa7d3bdd` (`Rudin RCA E: recover harmonic foundations and transitive axiom audit`).
The conflict is in `books/rudin-real-and-complex-analysis/RudinRCA.lean`, in the umbrella imports and module commentary.
It remains unresolved. No manual Lean source edit or conflict resolution was made.
The checkout is intentionally left in the stopped rebase for inspection.

**No push occurred. No cache fetch or build ran after this stop. No PR merge, ready-for-review action, or PR-body edit was performed.**
Chapter 10 remains incomplete; this report does not certify ticket #41 or perform the future crossed review.

## Exact Git state

| Item | Value |
|---|---|
| Original reviewed head | `a0538ea8a84843ad36bd1eb96cc9453ee723b7a1` |
| Original merge-base with fetched main | `b7593a842e03c909f50dda6388697a23cda18766` |
| `origin/main` fetched at start | `3cd1541c5970c0f099cac2c2626be1ba8381c588` |
| Current partial detached HEAD (four completed replays; **not** a completed rebased head) | `0f1ff40798052f33d1de64cce3ffc5ca9460c766` |
| Partial HEAD merge-base with `origin/main` | `3cd1541c5970c0f099cac2c2626be1ba8381c588` |
| Local branch ref `books/rca-holomorphic` | `a0538ea8a84843ad36bd1eb96cc9453ee723b7a1` |
| Remote branch at stop | `a0538ea8a84843ad36bd1eb96cc9453ee723b7a1` |
| Remote main at stop | `3cd1541c5970c0f099cac2c2626be1ba8381c588` |
| New completed/pushed head | None |
| `origin/main` at push time | Not applicable: no push |
| Observed main moves | 0 |

The branch was already checked out at the requested head, with a clean tracked worktree.
`codex --version` returned `codex-cli 0.167.0`; selected native config fields were
`model = gpt-6-astra`, `model_reasoning_effort = ultra`, and `service_tier = fast`.
These are CLI/config observations, not a separate service-side attestation.
Initial commands and outputs are in [01-start-state.log](rebase-evidence-20261109/01-start-state.log),
with start fetch in [02-fetch-start.log](rebase-evidence-20261109/02-fetch-start.log) and fetched values in [state.json](rebase-evidence-20261109/state.json).

```text
$ git rev-parse HEAD REBASE_HEAD ORIG_HEAD refs/heads/books/rca-holomorphic origin/main origin/books/rca-holomorphic
0f1ff40798052f33d1de64cce3ffc5ca9460c766
50584052c55c8546d9837a3297fa0f38aa7d3bdd
a0538ea8a84843ad36bd1eb96cc9453ee723b7a1
a0538ea8a84843ad36bd1eb96cc9453ee723b7a1
3cd1541c5970c0f099cac2c2626be1ba8381c588
a0538ea8a84843ad36bd1eb96cc9453ee723b7a1
[exit_status=0]
```

```text
$ git ls-remote origin refs/heads/main refs/heads/books/rca-holomorphic
a0538ea8a84843ad36bd1eb96cc9453ee723b7a1	refs/heads/books/rca-holomorphic
3cd1541c5970c0f099cac2c2626be1ba8381c588	refs/heads/main
[exit_status=0]
```

## Bookkeeping resolution and stop evidence

The first replay matched the coordinator's initial observation: two regions in
`PROGRESS.md`, one in `QUEUE.md`; all four E inventory additions applied cleanly.
The resolution kept main's exact chapter rows for 1–9 and 13–20 and E's exact
10–12 rows (44/32/14). All main prose and all E prose were retained verbatim,
with only a blank separator between their sections. A separate read-only helper
confirmed the exact byte reconstruction before staging.

Preservation outputs: [08-resolution-preservation.log](rebase-evidence-20261109/08-resolution-preservation.log)
and [09-helper-resolution-audit.log](rebase-evidence-20261109/09-helper-resolution-audit.log).
Original three-way blobs, conflict files, and resolved first-commit snapshots are retained in the evidence directory.

Commits 1–4 replayed; commit 5 stopped. No later commit was skipped, resolved, or replayed.
Full recorded continuation output:

```text
$ git add books/rudin-real-and-complex-analysis/PROGRESS.md books/rudin-real-and-complex-analysis/QUEUE.md
[exit_status=0]
$ GIT_EDITOR=true git rebase --continue
Recorded resolution for 'books/rudin-real-and-complex-analysis/PROGRESS.md'.
Recorded resolution for 'books/rudin-real-and-complex-analysis/QUEUE.md'.
[detached HEAD b1b2909] Rudin RCA E: inventory all 90 nodes and check pinned Mathlib claims
 6 files changed, 404 insertions(+), 3 deletions(-)
 create mode 100644 books/rudin-real-and-complex-analysis/inventory/Chapter10.md
 create mode 100644 books/rudin-real-and-complex-analysis/inventory/Chapter11.md
 create mode 100644 books/rudin-real-and-complex-analysis/inventory/Chapter12.md
 create mode 100644 books/rudin-real-and-complex-analysis/inventory/README.md
Rebasing (2/7)
Rebasing (3/7)
Rebasing (4/7)
Rebasing (5/7)
Auto-merging books/rudin-real-and-complex-analysis/RudinRCA.lean
CONFLICT (content): Merge conflict in books/rudin-real-and-complex-analysis/RudinRCA.lean
error: could not apply 5058405... Rudin RCA E: recover harmonic foundations and transitive axiom audit
hint: Resolve all conflicts manually, mark them as resolved with
hint: "git add/rm <conflicted_files>", then run "git rebase --continue".
hint: You can instead skip this commit: run "git rebase --skip".
hint: To abort and get back to the state before "git rebase", run "git rebase --abort".
hint: Disable this message with "git config set advice.mergeConflict false"
Recorded preimage for 'books/rudin-real-and-complex-analysis/RudinRCA.lean'
Could not apply 5058405... # Rudin RCA E: recover harmonic foundations and transitive axiom audit
[exit_status=1]
```

The captured unmerged diff is:

```diff
$ git diff --cc
diff --cc books/rudin-real-and-complex-analysis/RudinRCA.lean
index 49a6716,c81d08e..0000000
--- i/books/rudin-real-and-complex-analysis/RudinRCA.lean
+++ w/books/rudin-real-and-complex-analysis/RudinRCA.lean
@@@ -1,19 -1,23 +1,41 @@@
 +import RudinRCA.Chapter01
 +import RudinRCA.Chapter02
 +import RudinRCA.Chapter03
  import RudinRCA.Chapter04
  import RudinRCA.Chapter05
++<<<<<<< HEAD
 +import RudinRCA.Chapter08
 +import RudinRCA.Chapter13
 +import RudinRCA.Chapter15
++=======
+ import RudinRCA.Chapter10
+ import RudinRCA.Chapter11
+ import RudinRCA.Chapter12
+ import RudinRCA.AuditE
++>>>>>>> 5058405 (Rudin RCA E: recover harmonic foundations and transitive axiom audit)
  
 -/-
 -  Rudin, *Real and Complex Analysis* (3rd edition, McGraw-Hill, 1987).
 +/-!
 +Rudin, *Real and Complex Analysis*, third edition.
 +Chapter coverage and remaining numbered nodes are tracked in PROGRESS.md and SCOPING-D.md.
  
++<<<<<<< HEAD
 +Rudin, Real and Complex Analysis (third edition, 1987).
 +This umbrella imports the current partial Cluster A development.
 +Inventory, precise coverage and fidelity holds are recorded in PROGRESS.md,
 +the chapter inventories, SCOPING-A.md and QUEUE.md.
 +The independently built AuditA module audits this entire import graph.
++=======
+   The programme target is a complete formalization: every numbered node of
+   Chapters 1–20, zero sorries, axioms only propext / Classical.choice /
+   Quot.sound, statements faithful to the printed text.
+ 
+   Novelty gate (2026-10-27): PARTIAL — the only prior formalization of any
+   part of the book is Hirata's AFP entry (Isabelle/HOL, 2024) proving the
+   Riesz–Markov–Kakutani fragment of Chapter 2. No book development exists
+   in any proof assistant. Record:
+   research/prior-art-rca.md in the programme's files (ticket umbrella).
+ 
+   Current coverage is partial; see PROGRESS.md and inventory/README.md.
+   Chapter modules are added under RudinRCA/ as their lanes land them.
++>>>>>>> 5058405 (Rudin RCA E: recover harmonic foundations and transitive axiom audit)
  -/
[exit_status=0]
```

## Verification status

There is **no completed rebased head**. The following requested diff commands were
nevertheless executed and recorded against the **partial HEAD at the stop**, as
diagnostics only. They are not successful final verification.

| Requested check | Observed outcome |
|---|---|
| `git diff a0538ea8..HEAD --stat` | Nonempty, more than PROGRESS/QUEUE; complete literal output below. |
| `git diff a0538ea8..HEAD -- '*.lean'` | Nonempty: 2,090,640 output bytes / 31,972 lines; full output in [17-lean-diff.log](rebase-evidence-20261109/17-lean-diff.log). Lean byte identity is **not established**. |
| `git diff a0538ea8..HEAD -- books/rudin-real-and-complex-analysis/inventory/` | Nonempty: 14,299 output bytes / 181 lines; full output in [18-inventory-diff.log](rebase-evidence-20261109/18-inventory-diff.log). Inventory byte identity is **not established at this partial HEAD**, since later commits have not completed replay. No inventory conflict occurred. |
| `git diff --check` | Exit 2; six deliberately unresolved conflict-marker diagnostics, recorded below. |
| Cache fetch | Not run: mandatory conflict stop reached first. |
| Build | Not run: mandatory conflict stop reached first. No build success or exit code claimed. |

The intended cache command was `lake exe cache get`, followed only on success by
`lake build`, each with working directory
`/home/derekblair/rebase-fe-pr58-codex/books/rudin-real-and-complex-analysis`.
The RCA book has its own `lakefile.toml`; there is no root Lake package.
No build log/hash exists because no build process was started. No Mathlib compilation,
package installation, or toolchain installation was performed.

Independently of the conflict, the literal whole-tree verification requirements
cannot hold for a preserving rebase onto this main: main changed **260 paths,
including 104 Lean paths**, since the original merge-base. Those upstream changes
would necessarily appear in an endpoint comparison with the old reviewed head.
[22-main-only-name-status.log](rebase-evidence-20261109/22-main-only-name-status.log)
records the full upstream path list. A future authorized attempt needs a verification
criterion that distinguishes inherited main changes from PR changes. No exception
was assumed or used to push in this attempt.

### Literal requested diff stat at partial HEAD

```text
$ git diff a0538ea8..HEAD --stat
 CATALOGUE.md                                       |      2 +-
 .../BlaschkeMeansWork.lean                         |     81 +
 .../BlaschkeNecessityWork.lean                     |    292 +
 .../BlaschkeWork.lean                              |    333 +
 .../BoundaryProductGeometryWork.lean               |    140 +
 .../BoundaryProductWork.lean                       |    267 +
 .../CLAIMS-D-CH09.md                               |     64 +
 .../rudin-real-and-complex-analysis/COVERAGE-C.md  |     33 +
 .../Chapter15QuotientInterpolationWork.lean        |   1397 +
 ...hapter15QuotientInterpolationWork.manifest.json |    129 +
 .../DevelopmentAggregate.lean                      |   3753 +
 .../DevelopmentImports.lean                        |     14 +
 .../ElementaryFactorWork.check1.exit               |      1 +
 .../ElementaryFactorWork.check1.log                |     46 +
 .../ElementaryFactorWork.check1.snapshot.lean      |    156 +
 .../ElementaryFactorWork.lean                      |    154 +
 .../EntireLogWork.lean                             |    193 +
 .../EntireProductWork.lean                         |    139 +
 .../FactorizationWork.lean                         |    115 +
 .../FiniteProductWork.check.log                    |      3 +
 .../FiniteProductWork.lean                         |     56 +
 .../HolomorphicBezoutWork.lean                     |    471 +
 .../HolomorphicIdealAssemblyWork.lean              |     62 +
 .../HolomorphicIdealTheoremWork.lean               |     51 +
 .../HolomorphicIdealsWork.lean                     |     67 +
 .../HolomorphicProductWork.lean                    |    271 +
 .../INVENTORY-CH01.md                              |    134 +
 .../INVENTORY-CH02.md                              |    133 +
 .../INVENTORY-CH03.md                              |     35 +
 .../InterpolationLocalWork.lean                    |    140 +
 .../InterpolationWork.lean                         |    145 +
 .../JensenWork.lean                                |    143 +
 .../JensenZeroGrowthCheck.lean                     |    612 +
 .../LogMeansWork.lean                              |    666 +
 .../MellinFunctionalWork.lean                      |    179 +
 .../MeromorphicPoleDataWork.lean                   |    129 +
 .../MeromorphicQuotientAssemblyWork.lean           |     72 +
 .../MeromorphicQuotientWork.lean                   |     68 +
 .../MittagLefflerInfinityWork.lean                 |    143 +
 .../MittagLefflerKernelWork.lean                   |    148 +
 .../MittagLefflerSeriesWork.lean                   |    275 +
 .../MittagLefflerSetWork.lean                      |    148 +
 .../MuntzConclusionsWork.lean                      |    106 +
 .../MuntzDistanceWork.lean                         |    272 +
 .../MuntzNonDensityWork.lean                       |    129 +
 .../MuntzSzaszWork.lean                            |    270 +
 .../NevanlinnaWork.lean                            |     62 +
 .../NormalizedInterpolationWork.lean               |    119 +
 books/rudin-real-and-complex-analysis/PROGRESS.md  |    125 +-
 .../PrescribedZerosWork.lean                       |    206 +
 books/rudin-real-and-complex-analysis/QUEUE.md     |     70 +-
 books/rudin-real-and-complex-analysis/README.md    |     35 +
 .../RadialBoundaryWork.lean                        |    387 +
 .../rudin-real-and-complex-analysis/RudinRCA.lean  |     32 +-
 .../RudinRCA/AuditA.lean                           |    201 +
 .../RudinRCA/AuditE.lean                           |     58 -
 .../RudinRCA/Chapter01.lean                        |   1140 +
 .../RudinRCA/Chapter02.lean                        |    536 +
 .../RudinRCA/Chapter03.lean                        |     51 +
 .../RudinRCA/Chapter06.lean                        |    442 +
 .../RudinRCA/Chapter08.lean                        |   2934 +
 .../RudinRCA/Chapter10.lean                        |    537 -
 .../RudinRCA/Chapter11.lean                        |    409 -
 .../RudinRCA/Chapter12.lean                        |     42 +-
 .../RudinRCA/Chapter13.lean                        |    593 +
 .../RudinRCA/Chapter15.lean                        |   1249 +
 books/rudin-real-and-complex-analysis/SCOPING-A.md |     59 +
 books/rudin-real-and-complex-analysis/SCOPING-C.md |    159 +
 books/rudin-real-and-complex-analysis/SCOPING-D.md |    133 +
 books/rudin-real-and-complex-analysis/SCOPING-F.md |    378 +
 books/rudin-real-and-complex-analysis/SCOPING-G.md |    139 +
 .../SCOPING-H-19-20.md                             |    102 +
 books/rudin-real-and-complex-analysis/SCOPING-H.md |     89 +
 .../rudin-real-and-complex-analysis/Scratch61.lean |     53 +
 .../Scratch610Discussion.lean                      |    216 +
 .../Scratch610Exhaustion.lean                      |     34 +
 .../Scratch611Completed.lean                       |     83 +
 .../Scratch611Example.lean                         |     57 +
 .../Scratch614Signs.lean                           |     37 +
 .../Scratch615General.lean                         |    152 +
 .../Scratch615GeneralSupport.lean                  |    171 +
 .../Scratch615Infinity.lean                        |    139 +
 .../Scratch616.lean                                |    172 +
 .../Scratch616B.lean                               |    114 +
 .../Scratch616C.lean                               |     99 +
 .../Scratch616D.lean                               |    146 +
 .../Scratch616E.lean                               |    141 +
 .../Scratch616F.lean                               |     93 +
 .../Scratch616G.lean                               |     57 +
 .../Scratch616H.lean                               |     81 +
 .../Scratch616I.lean                               |    134 +
 .../Scratch616J.lean                               |     76 +
 .../Scratch617.lean                                |     43 +
 .../Scratch618Extension.lean                       |    100 +
 .../Scratch618Final.lean                           |     39 +
 .../Scratch618Polar.lean                           |     68 +
 .../Scratch619Assembly.lean                        |    163 +
 .../Scratch619Clip.lean                            |     83 +
 .../Scratch619Density.lean                         |    153 +
 .../Scratch619PositivePart.lean                    |    331 +
 .../Scratch619Regular.lean                         |     58 +
 .../Scratch619Uniqueness.lean                      |    122 +
 .../rudin-real-and-complex-analysis/Scratch63.lean |    124 +
 .../rudin-real-and-complex-analysis/Scratch64.lean |    126 +
 .../Scratch69.build.log                            |     74 +
 .../rudin-real-and-complex-analysis/Scratch69.lean |    448 +
 .../SpherePrescribedZerosWork.lean                 |   1266 +
 .../SphereWork.lean                                |    429 +
 .../UniformProductWork.check.log                   |     10 +
 .../UniformProductWork.lean                        |    199 +
 .../ZeroGrowthWork.lean                            |    469 +
 .../ZeroMultiplicityEnumerationWork.lean           |    109 +
 .../ZeroSetNormalizationWork.lean                  |    116 +
 .../assemble_quotient_interpolation.py             |     61 +
 .../evidence/aggregate-1-mapped-current.txt        |    570 +
 .../evidence/aggregate-1-mapped.log                |    570 +
 .../evidence/aggregate-1-source-map.json           |     62 +
 .../evidence/aggregate-1.log                       |    570 +
 .../evidence/aggregate-2-mapped-current.txt        |    736 +
 .../evidence/aggregate-2-mapped.log                |    736 +
 .../evidence/aggregate-2-result.json               |      9 +
 .../evidence/aggregate-2-source-map.json           |    134 +
 .../evidence/aggregate-2.log                       |    736 +
 .../evidence/aggregate-3-mapped-current.txt        |      1 +
 .../evidence/aggregate-3-mapped.log                |      0
 .../evidence/aggregate-3-run.json                  |     14 +
 .../evidence/aggregate-3-source-map.json           |    158 +
 .../evidence/aggregate-3.log                       |      0
 .../evidence/aggregate-4-sources.json              |     33 +
 .../evidence/assemble-development.py               |     42 +
 .../evidence/cache-get.log                         |     63 +
 .../evidence/ch06-development-2.log                |    106 +
 .../evidence/ch06-development-3.log                |     91 +
 .../evidence/ch06-development.log                  |      9 +
 .../evidence/chapter08-clean-axioms.log            |      4 +
 .../evidence/chapter08-clean-build.log             |   1011 +
 .../evidence/chapter08-clean-cache.log             |     63 +
 .../evidence/check-chapter06.sh                    |     35 +
 .../evidence/check_axiom_audit.py                  |     11 +-
 .../evidence/map-diagnostics.py                    |     24 +
 .../evidence/run-development.py                    |     43 +
 .../evidence/scratch61.log                         |      0
 .../evidence/scratch64-check.log                   |     22 +
 .../inventory/Chapter10.md                         |     47 +-
 .../inventory/Chapter11.md                         |     28 +-
 .../inventory/Chapter12.md                         |     24 +-
 .../inventory/README.md                            |     11 -
 .../rudin-real-and-complex-analysis/lakefile.toml  |      2 +-
 .../scripts/build-cluster-e-clean.py               |     57 -
 .../scripts/check_audit.py                         |    177 +
 .../scripts/check_clean_build.py                   |     80 +
 .../validation/clean-build.log                     |      9 +
 .../validation/resume-2026-11-01.md                |     53 +
 .../validation/resume-clean-build-2026-11-01.log   |     16 +
 software/sonnet-form/.gitignore                    |      2 +
 software/sonnet-form/DEVIATIONS.md                 |   3728 +
 software/sonnet-form/HISTORICAL-RHYME.md           |     49 +
 software/sonnet-form/MILESTONE1-STATUS.md          |     48 +
 software/sonnet-form/PRONUNCIATION.md              |    250 +
 software/sonnet-form/PROVENANCE.md                 |     85 +
 software/sonnet-form/README.md                     |    134 +-
 software/sonnet-form/SPEC.md                       |    256 +
 software/sonnet-form/SonnetForm.lean               |     12 +-
 software/sonnet-form/SonnetForm/Audit.lean         |    255 +
 software/sonnet-form/SonnetForm/AuditPart01.lean   |     53 +
 software/sonnet-form/SonnetForm/AuditPart02.lean   |     53 +
 software/sonnet-form/SonnetForm/AuditPart03.lean   |     53 +
 software/sonnet-form/SonnetForm/AuditPart04.lean   |     53 +
 software/sonnet-form/SonnetForm/AuditPart05.lean   |     53 +
 software/sonnet-form/SonnetForm/AuditPart06.lean   |     53 +
 software/sonnet-form/SonnetForm/AuditPart07.lean   |     53 +
 software/sonnet-form/SonnetForm/AuditPart08.lean   |     53 +
 software/sonnet-form/SonnetForm/AuditPart09.lean   |     53 +
 software/sonnet-form/SonnetForm/AuditPart10.lean   |     53 +
 software/sonnet-form/SonnetForm/AuditPart11.lean   |     53 +
 software/sonnet-form/SonnetForm/AuditTypes.lean    |     27 +
 software/sonnet-form/SonnetForm/Corpus.lean        |   2781 +
 software/sonnet-form/SonnetForm/Phonology.lean     |    141 +
 software/sonnet-form/SonnetForm/Spec.lean          |    326 +
 software/sonnet-form/VALIDATION.md                 |    144 +
 software/sonnet-form/data/annotations.json         | 362867 ++++++++++++++++++
 software/sonnet-form/data/cmudict-LICENSE          |     33 +
 software/sonnet-form/data/cmudict-README           |     32 +
 software/sonnet-form/data/cmudict-source.json      |     22 +
 software/sonnet-form/data/cmudict.dict             | 135166 +++++++
 software/sonnet-form/data/conformance-summary.json |     37 +
 software/sonnet-form/data/corpus-manifest.json     |   3543 +
 software/sonnet-form/data/gutenberg-1041.txt       |   3005 +
 .../sonnet-form/data/historical-rhyme-review.json  |  15414 +
 .../sonnet-form/data/pronunciation-overrides.json  |   2435 +
 .../sonnet-form/data/pronunciation-unknowns.json   |      4 +
 software/sonnet-form/data/sonnets.json             |   2927 +
 software/sonnet-form/data/validation-results.json  |   3890 +
 software/sonnet-form/data/validation-scans.tsv     |    156 +
 software/sonnet-form/data/validation.json          |   1567 +
 software/sonnet-form/lake-manifest.json            |      6 +
 software/sonnet-form/tools/audit_axioms.py         |     66 +
 software/sonnet-form/tools/check_model.py          |    210 +
 software/sonnet-form/tools/generate.py             |    306 +
 software/sonnet-form/tools/import_corpus.py        |     94 +
 software/sonnet-form/tools/pronunciations.py       |    226 +
 software/sonnet-form/tools/rhyme_review.py         |    172 +
 software/sonnet-form/tools/validate_scansion.py    |    267 +
 software/sonnet-form/verification/README.md        |     27 +
 software/sonnet-form/verification/axiom-audit.json |    675 +
 software/sonnet-form/verification/axiom-audit.txt  |    219 +
 software/sonnet-form/verification/checks.json      |     22 +
 software/sonnet-form/verification/checks.txt       |     64 +
 software/sonnet-form/verification/clean-build.json |     15 +
 software/sonnet-form/verification/clean-build.txt  |     22 +
 .../forward-fix-2026-11-10/phase1/01-build.log     |     18 +
 .../phase1/02-import_corpus.log                    |      2 +
 .../forward-fix-2026-11-10/phase1/03-generate.log  |     37 +
 .../phase1/04-validate_scansion.log                |      9 +
 .../phase1/05-check_model.log                      |      5 +
 .../phase1/06-audit_axioms.log                     |      1 +
 .../forward-fix-2026-11-10/phase1/results.json     |     56 +
 .../phase2-context-guard/01-build.log              |      1 +
 .../phase2-context-guard/02-import_corpus.log      |      2 +
 .../phase2-context-guard/03-generate.log           |     38 +
 .../phase2-context-guard/04-validate_scansion.log  |      9 +
 .../phase2-context-guard/05-check_model.log        |      5 +
 .../phase2-context-guard/06-audit_axioms.log       |      1 +
 .../phase2-context-guard/results.json              |     56 +
 .../phase2-final-retry/01-build.log                |     18 +
 .../phase2-final-retry/02-import_corpus.log        |      2 +
 .../phase2-final-retry/03-generate.log             |     38 +
 .../phase2-final-retry/04-validate_scansion.log    |      9 +
 .../phase2-final-retry/05-check_model.log          |      5 +
 .../phase2-final-retry/06-audit_axioms.log         |      1 +
 .../phase2-final-retry/fidelity.json               |     50 +
 .../phase2-final-retry/results.json                |     56 +
 .../phase2-final-retry/verdict-changes.json        |   5331 +
 .../phase2-final/01-build.log                      |     18 +
 .../phase2-final/02-import_corpus.log              |      2 +
 .../phase2-final/03-generate.log                   |      8 +
 .../phase2-final/results.json                      |     29 +
 .../phase2-inversion/01-build.log                  |     18 +
 .../phase2-inversion/02-import_corpus.log          |      2 +
 .../phase2-inversion/03-generate.log               |     38 +
 .../phase2-inversion/04-validate_scansion.log      |      9 +
 .../phase2-inversion/05-check_model.log            |      5 +
 .../phase2-inversion/06-audit_axioms.log           |      1 +
 .../phase2-inversion/results.json                  |     56 +
 .../phase2-inversion/verdict-changes.json          |   5331 +
 .../phase2-pronunciation/01-build.log              |     16 +
 .../phase2-pronunciation/02-import_corpus.log      |      2 +
 .../phase2-pronunciation/03-generate.log           |     37 +
 .../phase2-pronunciation/04-validate_scansion.log  |      9 +
 .../phase2-pronunciation/05-check_model.log        |      5 +
 .../phase2-pronunciation/06-audit_axioms.log       |      1 +
 .../phase2-pronunciation/results.json              |     56 +
 .../phase2-pronunciation/verdict-changes.json      |   3959 +
 .../phase2-respose/01-build.log                    |     16 +
 .../phase2-respose/02-import_corpus.log            |      2 +
 .../phase2-respose/03-generate.log                 |     37 +
 .../phase2-respose/04-validate_scansion.log        |      9 +
 .../phase2-respose/05-check_model.log              |      5 +
 .../phase2-respose/06-audit_axioms.log             |      1 +
 .../phase2-respose/results.json                    |     56 +
 .../phase2-respose/verdict-changes.json            |     90 +
 .../verification/resume-2026-11-01/01-build.txt    |     21 +
 .../resume-2026-11-01/02-import_corpus.txt         |      5 +
 .../verification/resume-2026-11-01/03-generate.txt |     40 +
 .../resume-2026-11-01/04-validate_scansion.txt     |     12 +
 .../resume-2026-11-01/05-check_model.txt           |      8 +
 .../resume-2026-11-01/06-audit_axioms.txt          |      4 +
 .../verification/resume-2026-11-01/checkpoint.json |     12 +
 .../verification/resume-2026-11-01/results.json    |     44 +
 269 files changed, 592263 insertions(+), 1288 deletions(-)
[exit_status=0]
```

### Literal requested whitespace/conflict check

```text
$ git diff --check
books/rudin-real-and-complex-analysis/RudinRCA.lean:6: leftover conflict marker
books/rudin-real-and-complex-analysis/RudinRCA.lean:10: leftover conflict marker
books/rudin-real-and-complex-analysis/RudinRCA.lean:15: leftover conflict marker
books/rudin-real-and-complex-analysis/RudinRCA.lean:21: leftover conflict marker
books/rudin-real-and-complex-analysis/RudinRCA.lean:27: leftover conflict marker
books/rudin-real-and-complex-analysis/RudinRCA.lean:40: leftover conflict marker
[exit_status=2]
```

## Evidence integrity

All logs below are local to `rebase-evidence-20261109/`. Each records the exact
command, full combined stdout/stderr, and exit status. SHA-256 hashes cover the
complete log file, including command and exit-status framing. Byte counts measure
command output only. Empty output would be recorded explicitly by the zero byte
count; neither requested content-diff output was empty at the stop.

| Log | Exit | Output bytes | SHA-256 |
|---|---:|---:|---|
| `14-stop-refs.log` | 0 | 246 | `c876b48b6d9b8a00cc5aee8bc10ac02a9b03d30a596dd2473be242ca9254892c` |
| `15-stop-merge-base.log` | 0 | 41 | `4ea61a5536591c242b6971f066c4b877a5c6b76b6c726aa1d0fb2d6db991d878` |
| `16-diff-stat.log` | 0 | 17,036 | `78ab5b666edc65abece492a779336e56bf2db479788057953142890adf4773d1` |
| `17-lean-diff.log` | 0 | 2,090,640 | `f06471514f78c904315246fd7ffabf24c7083735b62777a985786535da1ca693` |
| `18-inventory-diff.log` | 0 | 14,299 | `b505f0c2bcfd8b911c3507a8b3f3bfacf4da1e55af16c850c67818c849247c87` |
| `19-diff-check.log` | 2 | 485 | `cbcbc74202d52ddd3ffcb271195b31651316caa4f21ff4bb668def8cc744ce6f` |
| `20-remote-at-stop.log` | 0 | 131 | `3f059f5adb178dc997c473f15e89fbfdff93602369ab127b081440c752c2cf4a` |
| `21-partial-replay-log.log` | 0 | 292 | `8df9ebc9535b68da6452923b064131cee29de7a00ac617e1467a7dca9d7cd0db` |
| `22-main-only-name-status.log` | 0 | 17,342 | `ee51f74160a3fb2bb414273b6374170eb108e114be7c8d78367110997b9699de` |
| `23-rebase-status.log` | 0 | 1,450 | `d14c940397c2ad1d89df255c904642e657445d333f912cbcdcfbcf4ec4928b02` |

Additional evidence: [23-rebase-status.log](rebase-evidence-20261109/23-rebase-status.log),
the `RudinRCA.lean.stage1/2/3` blobs, `RudinRCA.lean.conflicted`, and copied rebase
metadata (`done`, `git-rebase-todo`, `head-name`, `onto`, `orig-head`, `msgnum`, `end`).
The stopped conflict and both original branch refs are preserved. This lane ends
under the user's explicit Lean-conflict stop condition, with no push.
