# Cluster E: numbered-node inventory

Stage 1 for ticket #41, umbrella #36. Author pool: ChatGPT/Codex.
Book: Walter Rudin, *Real and Complex Analysis*, third edition (1987).

| Chapter | Numbered nodes | Verified | Unverified | Detailed claims check |
|---|---:|---:|---:|---|
| 10 | 44 | 44 | 0 | [10.1–10.44](Chapter10.md) |
| 11 | 32 | 32 | 0 | [11.1–11.32](Chapter11.md) |
| 12 | 14 | 14 | 0 | [12.1–12.14](Chapter12.md) |
| Total | 90 | 90 | 0 | |

Every numbered theorem, definition-bearing item, remark, example, and
numbered worked problem is included. In particular, 10.44 is a numbered
worked problem in the chapter, not an end-of-chapter exercise. Unnumbered
corollaries are part of their parent node. A definition or one subclaim
alone does not complete a node containing further assertions.

The [public third-edition scan](https://djvu.online/file/NKmAEzkLVs8Io)
establishes individual numbers and statements. The
[publisher's table of contents](https://www.mheducation.co.in/real-and-complex-analysis-9789355326119-india)
independently confirms the three chapter titles, but does not establish
individual node numbers. Scan images resolve lost bars and mathematical
symbols in OCR. Source-specific page links and provenance are in each table.
No scan or copyrighted book text is committed: the tables record mathematical
facts and source/API identifiers, not transcriptions of the book.

All claims checks use Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` with Lean
`leanprover/lean4:v4.34.1`. `A` means usable content or a primitive
definition; `V` means a variant or components requiring a faithful bridge;
`M` means no complete match located after the stated searches. `M` is not a
proof that no match exists. These labels describe upstream coverage, not
completed local proofs. A fidelity flag is additional to those labels.

Mathlib's measure, integration, and Fourier results can supply book-proof
dependencies from Chapters 1–9 without importing unfinished book modules.
Specific dependencies are listed per node or by node groups in the tables.

Two source issues require explicit tracking: the variable mismatch in
10.37 and the false radius-zero strict inequality in 11.5(4). See
`QUEUE.md`; neither is silently repaired or counted as a completed node.
