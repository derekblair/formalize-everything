# Catalogue

Every formalization target, its status, and where it lives. A target is **done** only when it meets the standard in the README: zero sorrys, exit-0 build, standard axioms only, faithful statements, hostile review passed.

## Books

| Target | Status | Home |
|---|---|---|
| Rudin, *Principles of Mathematical Analysis* (3rd ed.) | In progress — Chapters 1–7 complete and verified (252 nodes); Chapter 8 underway | [rudin-lean](https://github.com/derekblair/rudin-lean) |
| Rudin, *Real and Complex Analysis* | Queued — follows PMA | here (planned) |
| Rudin, *Functional Analysis* | Queued — follows RCA | here (planned) |
| Garling, *A Course in Galois Theory* | Candidate — landscape checked 2026-10-10, no complete formalization found | here (planned) |

## Software

| Target | Status | Home |
|---|---|---|
| Bech32 / Bech32m (BIP-173 / BIP-350) | Milestone 1 landed (PR #9) — executable spec, vectors, and round-trip proofs; error-detection guarantee is milestone 2 | here, [software/bech32/](software/bech32/) |
| URI (RFC 3986) | Milestone 1 landed (PR #10) — complete ABNF as inductive spec, §5.3 recomposition, §5.4 examples | here, [software/uri-rfc3986/](software/uri-rfc3986/) |

## Papers and shorter texts

| Target | Status | Home |
|---|---|---|
| — | none yet | — |

## Proposing a target

Add a row here with the text, edition, and scope (complete book vs selected results), plus a landscape check: has anyone already formalized it, completely or partially? Complete coverage is the point of this repo — selected-results passes belong elsewhere unless they're a deliberate first milestone.
