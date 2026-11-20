# BRIEF — Moonshine candidate literature kill-check

You are a literature-check lane for a mathematics programme. A mined candidate claims an identity between:
- A093085 — a quotient of Ramanujan theta functions (involves phi(-x) and psi(x^4); fetch the record for its exact definition/formula lines), and
- A112171 — coefficients of the Monster group's McKay–Thompson series T_32c.

One judging lane called the pair a genuine cross-domain surprise (the two records do not cross-reference each other). Another lane called it DISGUISED: both sides allegedly reduce to the same level-16 eta-quotient family (both are expressible via the eta-quotients behind A029838 and its reciprocal A083365, up to a fourth-root-of-unity sign twist x^4 -> -x^4), which would make the identity a known consequence of classical eta-product theory rather than a discovery.

Your job: settle which is true, with citations. Check:
1. Both OEIS records in full (definitions, formulas, comments, links, cross-references): https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A093/A093085.seq and https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A112/A112171.seq
2. Conway–Norton / Ford–McKay–Norton: the eta-product expressions for McKay–Thompson series, in particular T_32c — is it a known eta-quotient, and does its eta-product coincide with the A093085 side's?
3. Whether the theta-quotient on the A093085 side is a known Hauptmodul / eta-quotient at level 16 or 32 (LMFDB, moonshine eta-quotient catalogues, or the literature on Ramanujan's theta-function quotients).
4. Directly: expand both sides' eta-quotient expressions symbolically if you can find them, and state whether the identity follows from a published eta-product identity.

Deliverable: `VERDICT.md` in this directory containing: the search log (sources, queries, dates); the key evidence quoted; and a final verdict line, exactly one of:
- `VERDICT: DISGUISED` — followed by the citation(s) that already contain the identity or make it a direct consequence.
- `VERDICT: NOVEL` — the identity does not appear and does not follow trivially from the tables.
- `VERDICT: UNSURE` — followed by exactly what could not be checked.
End the file with the line `LITCHECK COMPLETE`.
