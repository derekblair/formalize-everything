# Catalogue

Every formalization target, its status, and where it lives. A target is **done** only when it meets the standard in the README: zero sorrys, exit-0 build, standard axioms only, faithful statements, hostile review passed.

## Books

| Target | Status | Home |
|---|---|---|
| Rudin, *Principles of Mathematical Analysis* (3rd ed.) | In progress — Chapters 1–7 complete and verified (252 nodes); Chapter 8 underway | [rudin-lean](https://github.com/derekblair/rudin-lean) |
| Rudin, *Real and Complex Analysis* | In progress — 455/456 numbered body nodes Done across Chapters 1–20 (novelty gate PARTIAL: sole prior art Hirata's AFP Riesz-representation fragment, Isabelle, 2024; Big Picard 16.21 proved unconditionally in Lean via modular λ on FE #141, advancing Ch. 16 to 22/22; only Ch. 2 exposition 2.21 converse remains to close RCA at 456/456) | here, [books/rudin-real-and-complex-analysis/](books/rudin-real-and-complex-analysis/) |
| Rudin, *Functional Analysis* | Queued — follows RCA | here (planned) |
| Garling, *A Course in Galois Theory* | In progress — milestone 2: Ch. 16 formalized (3/7 main-text theorems/corollaries + 6/16 exercises literal + 14 holds in QUEUE.md; 9/23 total, plus §§16.1–16.4 prose definitions/factorizations); Ch. 15 formalized (5/5 main-text theorems/lemma/corollary + 2/10 exercises literal + 8 holds in QUEUE.md; 7/15 total, plus §§15.1–15.3 prose cyclotomic/unit-group derivations); Ch. 14 formalized (1/1 main-text theorem + 3/8 exercises literal + 5 holds in QUEUE.md; 4/9 total, plus §§14.3–14.4 prose cubic/quartic solvability by radicals); Ch. 13 formalized (3/3 main-text theorems/corollaries + 4/5 exercises literal + 1 hold in QUEUE.md; 7/8 total); Ch. 12 formalized (9/10 main-text theorems/corollaries + 7/11 exercises literal + 5 holds in QUEUE.md; 16/21 total); Ch. 11 formalized (8/10 main-text theorems/corollaries + 6/12 exercises literal + 8 holds in QUEUE.md; 14/22 total); Ch. 10 formalized (14/15 main-text theorems/corollaries + 10/11 exercises literal + 2 holds in QUEUE.md; 24/26 total); Ch. 9 formalized (5/5 main-text theorems/corollaries + 7/7 exercises literal + 0 holds in QUEUE.md; 12/12 total); Ch. 8 formalized (5/5 main-text theorems/corollaries + 6/8 exercises literal + 2 holds in QUEUE.md; 11/13 total); Ch. 7 formalized (7/10 main-text + 4/10 exercises literal + 9 holds in QUEUE.md; 11/20 total, plus §7.3 Examples 1–4); Ch. 6 formalized (1/1 main-text theorem + 6/7 exercises literal + 1 hold in QUEUE.md; 7/8 total, plus §6.2 prose trisection theorem); Ch. 5 1/3 main-text + 6/12 exercises literal + 8 holds; Ch. 4 10/10 main-text + 10/11 exercises literal + 1 hold; Ch. 3 21/21 main-text + 25/27 exercises literal + 2 holds; Ch. 2 4/5 strictly numbered / 4/6 headed literal + 2 holds; Ch. 1 22/25 literal + 3 holds | here (planned) |

## Software

| Target | Status | Home |
|---|---|---|
| Bech32 / Bech32m (BIP-173 / BIP-350) | Milestones 1–2 landed (PR #9, PR #29) — executable spec, vectors, round-trip proofs, and the machine-checked error-detection guarantee: distance theorem, refined string-level detection forms with minimality counterexamples, BIP-350 insertion point, cross-variant disjointness | here, [software/bech32/](software/bech32/) |
| URI (RFC 3986) | Milestones 1-2 landed (PR #10, PR #31) — complete ABNF as inductive spec, §5.3 recomposition, §5.2 resolution, guarded target validity, §5.4 resolution theorems | here, [software/uri-rfc3986/](software/uri-rfc3986/) |
| Merkle proofs (RFC 6962) | Milestone 2 landed — hash-abstract spec, executable verifiers, completeness, symbolic vectors, and fixed-width collision-explicit inclusion soundness, tree binding, and consistency soundness; kernel-checked width-gap attacks | here, [software/merkle-rfc6962/](software/merkle-rfc6962/) |
| UTF-8 (RFC 3629 / Unicode Table 3-7) | Milestone 1 landed (PR #20) — independent Table 3-7 spec, Valid ↔ decode characterization, exact agreement with Lean core `IsValidUTF8`/`validateUTF8`, kernel-checked examples | here, [software/utf8/](software/utf8/) |
| SHA-256 pure Lean bridge (FIPS 180-4) | Milestone landed (PR #27) — LeanSha256 ↔ independent lean4-hash spec, explicit `< 2^61`-byte FIPS domain and total mod-`2^64` length extension; discharges **NONE** of SizzLean’s three FFI axioms; pinned LGPL-3.0-only / MIT dependencies | here, [software/sha256-bridge/](software/sha256-bridge/) |
| CBOR (RFC 8949) | Milestone 1 landed (`e629a63`, PR #60, ticket #34); Milestone 2 landed (`c41602be`, PR #128, ticket #126) — novelty gate PARTIAL (EverCBOR, lean-cbor, Proven-Commons/cbor PR #2, cbor_ada); M1: float-free grammar & deterministic round trips (scaffolding) plus size-hypothesised indefinite deflation with both `< 2^64` boundary counterexamples, tag 2/3 bignums, extended duplicate-key/first-wins semantics, §4.2.1/§4.2.3/CTAP2 ordering profiles, and 58 float-free Appendix A / 94 Appendix F.1 / 8 ordering vectors in-kernel; M2: explicit bit-level IEEE 754 half/single/double (`0xf9`/`0xfa`/`0xfb`, §3.3/Appendix D), shortest-float narrowing (`binary64 → binary32 → binary16`, §4.1/§4.2.1) & `0xf97e00` NaN canonicalization, boundary theorems, §2/§5.6.1 float data-model equivalence, full-grammar F.1 refusal, and all 23 float Appendix A rows (`19..40` + `49`) in-kernel (81/81 Appendix A complete) | here, [software/cbor-rfc8949/](software/cbor-rfc8949/) |

## Papers and shorter texts

| Target | Status | Home |
|---|---|---|
| The Bible's numerical systems (Genesis 5 & 11; Leviticus 25) | Milestone 1 landed: six sourced witness profiles, totals, exhaustive divergence, both jubilee periods, environment axiom audit; crossed review PASS (Argon, google-ai-ultra) (ticket #47) | here, [software/bible-numbers/](software/bible-numbers/) |
| Quranic inheritance (mirath, An-Nisa 4:11–12, 4:176) | Milestone 1 landed: rational inheritance schedule, whole-estate conservation proof, 31 sourced cases; crossed review PASS (Argon, google-ai-ultra) (ticket #46) | here, [software/mirath/](software/mirath/) |
| Shakespeare, the Sonnets (form spec + corpus) | Draft milestone 1, 2026-10-27 — full 154-sonnet kernel audit; linguistic validation exposes unresolved pronunciation/stress model limitations (ticket #45) | here, [software/sonnet-form/](software/sonnet-form/) |

## Proposing a target

Add a row here with the text, edition, and scope (complete book vs selected results), plus a landscape check: has anyone already formalized it, completely or partially? Complete coverage is the point of this repo — selected-results passes belong elsewhere unless they're a deliberate first milestone.
