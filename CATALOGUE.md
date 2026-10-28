# Catalogue

Every formalization target, its status, and where it lives. A target is **done** only when it meets the standard in the README: zero sorrys, exit-0 build, standard axioms only, faithful statements, hostile review passed.

## Books

| Target | Status | Home |
|---|---|---|
| Rudin, *Principles of Mathematical Analysis* (3rd ed.) | In progress — Chapters 1–7 complete and verified (252 nodes); Chapter 8 underway | [rudin-lean](https://github.com/derekblair/rudin-lean) |
| Rudin, *Real and Complex Analysis* | Started 2026-10-27 — novelty gate PARTIAL (sole prior art: Hirata's AFP Riesz-representation fragment, Isabelle, 2024); book skeleton landed, chapter-cluster lanes running | here, [books/rudin-real-and-complex-analysis/](books/rudin-real-and-complex-analysis/) |
| Rudin, *Functional Analysis* | Queued — follows RCA | here (planned) |
| Garling, *A Course in Galois Theory* | Candidate — landscape checked 2026-10-10, no complete formalization found | here (planned) |

## Software

| Target | Status | Home |
|---|---|---|
| Bech32 / Bech32m (BIP-173 / BIP-350) | Milestones 1–2 landed (PR #9, PR #29) — executable spec, vectors, round-trip proofs, and the machine-checked error-detection guarantee: distance theorem, refined string-level detection forms with minimality counterexamples, BIP-350 insertion point, cross-variant disjointness | here, [software/bech32/](software/bech32/) |
| URI (RFC 3986) | Milestones 1-2 landed (PR #10, PR #31) — complete ABNF as inductive spec, §5.3 recomposition, §5.2 resolution, guarded target validity, §5.4 resolution theorems | here, [software/uri-rfc3986/](software/uri-rfc3986/) |
| Merkle proofs (RFC 6962) | Milestone 2 landed — hash-abstract spec, executable verifiers, completeness, symbolic vectors, and fixed-width collision-explicit inclusion soundness, tree binding, and consistency soundness; kernel-checked width-gap attacks | here, [software/merkle-rfc6962/](software/merkle-rfc6962/) |
| UTF-8 (RFC 3629 / Unicode Table 3-7) | Milestone 1 landed (PR #20) — independent Table 3-7 spec, Valid ↔ decode characterization, exact agreement with Lean core `IsValidUTF8`/`validateUTF8`, kernel-checked examples | here, [software/utf8/](software/utf8/) |
| SHA-256 pure Lean bridge (FIPS 180-4) | Milestone landed (PR #27) — LeanSha256 ↔ independent lean4-hash spec, explicit `< 2^61`-byte FIPS domain and total mod-`2^64` length extension; discharges **NONE** of SizzLean’s three FFI axioms; pinned LGPL-3.0-only / MIT dependencies | here, [software/sha256-bridge/](software/sha256-bridge/) |

## Papers and shorter texts

| Target | Status | Home |
|---|---|---|
| — | none yet | — |

## Proposing a target

Add a row here with the text, edition, and scope (complete book vs selected results), plus a landscape check: has anyone already formalized it, completely or partially? Complete coverage is the point of this repo — selected-results passes belong elsewhere unless they're a deliberate first milestone.
