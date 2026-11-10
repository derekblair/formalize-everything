# Milestone 1 status — 2026-11-10

**Incomplete; PR #56 remains draft.** This is the author lane's forward fix,
not a crossed review or a claim of historically complete sonnet validation.

| Blocker | Status | Delivered and precise remainder |
|---|---|---|
| Named pronunciation/stress annotations | Resolved for the eight named choices | Sourced temperate, fixed, every, wandering, wires, record, antique and contents annotations; all seven target lines pass. Global coverage remains limited: 53.12 and 59.5 newly fail licensed meter under the documented choices and need further sourced work. |
| Interior inversion on ever (19.14) | Partially resolved | Direct Kiparsky evidence; explicit third/fourth-foot license; 19.14 now passes. Generic phrase-boundary/proclitic conditions are unencoded; all 63 selected interior-license readings need that validation. |
| respose (27.2) | Resolved as an explicit editorial interpretation | Folger supports a lookup alias to repose; original Gutenberg text is unchanged. The interpretation remains an annotation assumption. |
| Historical rhyme | Partially resolved | Every original failed sonnet has source-linked findings in DEVIATIONS. There are 163 open original constraints across 81 sonnets, and zero complete historical schemes validated. |

The historical review's 236 unequal pairs comprise 131 scholarly pair supports,
8 rule/form inferences, 2 partial supports, 2 modern-only diagnostics, 5 scholarly
imperfect analyses, 1 disagreement, and 87 open relations. The 83 cross-class
collisions include 21 same-token obstructions, 4 source-discussed repeated-class
constraints, and 58 open historical relations. Pair support does not establish
all seven historical classes or their 21 distinctions. See HISTORICAL-RHYME.md.

Final model counts: line count 152/154, rhyme 21/154, strict meter 1/154,
licensed meter 47/154. At line level, strict meter passes 1,248/2,155 and licensed
meter 1,960/2,155. Relative to the rebase baseline, licensed meter gains 79 lines
and loses two (53.12 and 59.5); strict meter gains 21 and loses one (59.5).
All source strings, dictionary bytes, source/dependency pins and the hand fixture
remain byte-identical to the rebase baseline.

All six final commands exited 0 in `verification/forward-fix-2026-11-10/phase2-final-retry/`.
The clean-slate Lean build took 14.588 seconds. The current exhaustive census
covers 219 theorems, using only `propext` and `Quot.sound`; no prohibited proof
or source tokens were found. Sixteen boundary tests pass. Every original failed
sonnet and every baseline constraint is checked for complete, source-bound
review coverage by the generator.

An earlier final preparation attempt hit a catalogue-renderer variable collision;
the following generator check rejected stale DEVIATIONS.md. The renderer was
fixed and regenerated, then all six commands were rerun from an absent .lake.
The failed attempt remains in `phase2-final/`; the successful final record is
`phase2-final-retry/`. No Lean build failed. Earlier model-change suites also
passed; logs and SHA-256 hashes are retained per stage.

Next lane: coordinator-appointed crossed **Codex** review from a pool other than
this author lane's **proton** pool, against the final pushed branch head. It must
review the conditional annotations, two new failures, interior phrase/proclitic
boundary work, and historical evidence/status distinctions. Subsequent modeling
must source the remaining lexical contexts and historical relations, avoid
sonnet-number/rhyme-partner fitting, retain the frozen corpus/hand fixture, and
rerun all six commands. Milestone 1 must remain incomplete until its linguistic
blockers and full verification requirements are met. This lane does not merge.
