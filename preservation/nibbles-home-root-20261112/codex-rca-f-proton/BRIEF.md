# BRIEF — codex-rca-f-proton (Codex, GPT-6-Astra ultra, nibbles, chatgpt-proton pool)

You are a coding lane in Derek's formalization programme. Do Stage 2 formalization for one RCA cluster, end to end, autonomously. Work as hard and as fast as you can — this lane exists to burn the proton Codex pool productively, so keep moving through nodes in dependency order and do not idle waiting for review.

## Authority
GitHub issue **derekblair/formalize-everything#42** — "Rudin RCA cluster F: Chapters 13-14 (Approximation by Rational Functions; Conformal Mapping)". Read it in full first (`gh issue view 42 -R derekblair/formalize-everything`), and the umbrella issue #36. The ticket is the spec: Stage 2 bar, pins, and review gates. This brief adds only machine/scope mechanics.

## Setup
- Work in a FRESH clone: `git clone git@github.com:derekblair/formalize-everything.git ~/lane-work/codex-rca-f-proton/formalize-everything` (do not touch `~/projects/formalize-everything` or any other lane's workdir).
- Branch: `rca-f-stage2-proton`.
- Pins: Lean v4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 — never float. Fetch the Mathlib cache (`lake exe cache get`) before building.
- The book skeleton is on main under `books/rudin-real-and-complex-analysis/` (library `RudinRCA`). One module per chapter under `RudinRCA/`, umbrella imports updated, PROGRESS.md kept current.

## Execution
- Stage 2, in dependency order, first chapter first: formalize the numbered nodes of Chapters 13-14 at the programme bar — zero sorry/admit, `#print axioms` on every new theorem family shows at most propext / Classical.choice / Quot.sound, faithful statements (never weaken silently — a printed claim that fails gets a proved counterexample or a corrected form, disclosed, and that node stops until disclosed), clean-slate build exit 0 per module (`rm -rf .lake && lake build` for the module path, or full build when it is cheap enough).
- Exercises are out of scope for v1.
- Stage 1 inventories were produced by separate research lanes and are NOT in this repo yet — do not claim to have them. Enumerate the nodes yourself from the printed text and the skeleton, record your counts in STATUS.md, and flag any discrepancy against the ticket scope there.
- Keep `lake build` green at each stage; do not accumulate a broken tree.

## Hard gates
- Never merge; never arrange your own review. Open a normal PR (not draft) when your first chapter module passes clean-slate build + axiom audit, with the evidence in the body via `--body-file`. Further chapters go on the same branch / PR updates only if the PR is still open and unreviewed; otherwise open a follow-up PR per chapter.
- No installs or removals on this machine. If a Codex update prompt appears, choose Skip.
- No work outside this cluster's chapters, no Dot tickets, no other repo.

## Reporting
- Maintain `STATUS.md` in this workdir (chapter, node counts, build state, last check) as you go — this is a long build; the coordinator harvests STATUS.md.
- Final: `REPORT.md` in this workdir — module-by-module results, axiom-audit output summary, clean-slate build results, and PR URLs. Claims name their evidence inline.
