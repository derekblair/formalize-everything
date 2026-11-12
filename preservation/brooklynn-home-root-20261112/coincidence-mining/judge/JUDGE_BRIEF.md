# Coincidence mining — judgment lane brief

You are one of five independent judgment lanes (different AI harnesses) ranking
the same candidate packet. Work only from the packet file you are given plus
your own knowledge; do not look for other lanes' answers.

## The operation's goal (Derek's definition)

Find interesting integer identities that **nobody has published before**:
pairs of independently defined integer sequences that agree far beyond
coincidence, where the equality itself has never been asserted in print, in
the OEIS, or anywhere else. Beauty matters — the ideal find looks almost
untrue at first glance: very different definitions, striking agreement.

## Input

`finalist_packet.md` — candidate pairs with both OEIS records (names,
comments, formulas, cross-references, keywords). Each pair survived
deterministic filters and an index-aware extended-terms stress test.

## Your task

For EVERY candidate, produce one row:

`CANDIDATE <n> | NOVELTY: <UNPUBLISHED|ASSERTED|DISGUISED> | INTEREST: <0-10> | VERDICT: <KEEP|DROP> | <one-sentence reason>`

- **UNPUBLISHED** — the equality is not asserted in either record (no comment,
  formula, or cross-reference states or implies it) and you know of no
  publication of it. This is the target class.
- **ASSERTED** — the equality (or an equivalent form) is stated somewhere:
  an OEIS comment/formula/xref, a named theorem, a paper you know. Not a
  target for this operation, however beautiful.
- **DISGUISED** — the two definitions are the same definition in disguise, a
  trivial transformation of each other, or both are mechanical consequences
  of a shared third definition. Drop these regardless of agreement length.
- **INTEREST 0–10** — judge by: distance between the two definitions'
  mathematical worlds, surprise/symmetry of the identity, and whether
  proving it would teach something or open a family of questions. Long
  agreement alone is not interest.
- **KEEP** only UNPUBLISHED candidates with INTEREST >= 6.

Then give your **top 5 ranking** with 2–3 sentences each: why it looks true,
why it matters, and the most plausible way it could still be an artifact.

Rules: no proof attempts; no Lean. If a record is too thin to judge novelty,
say NOVELTY: UNPUBLISHED with reason "record silent — novelty unverified"
and cap INTEREST at 6. End your report with the line JUDGING COMPLETE.
Write your report to JUDGE-<lane>.md in this directory.
