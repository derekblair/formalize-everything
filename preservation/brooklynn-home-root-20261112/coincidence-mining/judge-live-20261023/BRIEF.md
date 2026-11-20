# BRIEF — Judge coincidence-mining packet ranks 61–160 (Codex, live pool)

You are an independent judge for the coincidence-mining programme. The packet was built by a Codex lane on the gmail pool; you are on a different pool and did not build it. Judge it cold.

## Input (staged in this directory, read-only)
- `PACKET2-FULL.md` — 100 candidate pairs (pass-2 ranks 61–160): pairs of OEIS sequences whose listed terms agree, proposed as possibly unpublished identities.

## The programme's gates (from Derek, 2026-10-21)
1. **Novelty is the primary gate.** The target is an identity NOBODY HAS PUBLISHED BEFORE. If the equality is already asserted anywhere — OEIS comments/formulas on either sequence's record, or the literature — it is NOT a target, even if unproved. Drop it.
2. **Interestingness.** Super beautiful, unexpected, very symmetrical — the kind of identity that almost seems untrue. Trivial transforms (offset shifts, leading zeros, sign flips, abs) and boring patterns (constant/arithmetic/geometric/short-period) are drops.
3. **Data integrity.** Check the agreement is not an artifact of misaligned offsets or truncated lists. Where a sequence's own formula contradicts its listed terms, flag it explicitly — that contradiction killed the packet-#1 survivor.

## Task
For every candidate: fetch both OEIS records, verify the claimed agreement with correct offsets, run the novelty check, and deliver a verdict: KEEP (survives all three gates) or DROP (name the gate it fails). Be hostile — packet #1's three-judge panel kept exactly 1 of 60, and it later died under adversarial verification.

## Deliverable
`JUDGE-LIVE.md` in this directory ending with the line `JUDGE COMPLETE`: one section per candidate with verdict + evidence (agreement length after offset correction, novelty evidence, integrity flags), and a summary count. No Lean, no statement drafting — judging only.
