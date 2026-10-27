# Bech32 and Bech32m

Milestone 1 of [issue #6](https://github.com/derekblair/formalize-everything/issues/6): an executable generic checksummed base32 specification, kernel-checked vectors, and encode/decode correctness. The catalogue remains **milestone 1 in progress** until the required independent review passes. Milestone 2 — the error-detection guarantee of issue #16 — is delivered by this change, pending its own independent review; see "Milestone 2" below.

## Sources and scope

The specification is [BIP-173](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0173.mediawiki) and [BIP-350](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0350.mediawiki), pinned for this milestone to bitcoin/bips commit `100ba872c808946155b1eeb8c4568058f2eea0a7`. Their reference snippets define the polynomial recurrence and checksum construction. The [Python reference linked by the BIPs](https://github.com/sipa/bech32/blob/master/ref/python/segwit_addr.py) clarifies the order of textual decoding checks. The BIP specifications and their test vectors are BSD-2-Clause licensed.

This project implements the generic format. SegWit network names, witness versions, byte conversion/padding, program lengths, scriptPubKey conversion, and witness-version/checksum-variant matching are separate address-layer rules and remain a later milestone. In particular, a string listed as an invalid SegWit address may be a valid generic Bech32 string.

## Toolchain and representation

Use **Lean 4.34.1**, with Lean's core and `Std` only. There is no Mathlib dependency or external proof solver. The checksum state is `BitVec 30`; each payload symbol is `Word := BitVec 5`, whose underlying value is bounded by 32. `encode` receives those five-bit values directly and does not reduce arbitrary input integers modulo 32.

The 30-bit state makes the reference mask-and-shift operation explicit through a fixed-width left shift. The five generator constants and both final constants (`1` and `0x2bc830a3`) are exposed in `Bech32/Checksum.lean`. `hrpExpand` has the BIP's high-bits / zero / low-bits order. Its intended input domain is printable ASCII, enforced by the text layer.

This dependency choice keeps milestone 1 small and independently buildable. For milestone 2, `polymodStep`, its XOR-linearity theorem, and the list fold remain available as the concrete machine against which to connect finite-field and polynomial algebra. If that proof needs Mathlib, add it at the umbrella pin `d13f23b723b8a846827a245b89c10fc7d3f11612`; do not float the dependency or change the executable recurrence.

## Interface and validity

```lean
encode    : Variant → String → List Word → String
decode    : Variant → String → Option (String × List Word)
decodeAny : String → Option (Variant × String × List Word)
```

`Variant.bech32` selects BIP-173; `Variant.bech32m` selects BIP-350. `verifyChecksum` takes the HRP as a character list and data **including** the six checksum words. `createChecksum` takes payload data **excluding** those words. The low-level checksum functions expect an already normalized HRP.

`decode` checks the 90-character limit, printable ASCII 33–126, uniform letter case, the **last** `1` separator, a nonempty HRP, at least six data characters, alphabet membership, and the selected checksum constant. Accepted uppercase strings return a lowercase HRP. The remaining data is returned without its six checksum words. Checking the ASCII range over the entire string matches the linked reference decoder; alphabet membership further restricts the data part.

`encode` emits lowercase and, like the BIP's low-level encoding helper, leaves the input length/HRP preconditions to the caller. `ValidInput` states them for canonical inputs: a nonempty printable HRP with no uppercase letters and `hrp.length + data.length + 7 ≤ 90`. The HRP's 83-character bound follows from that inequality. The payload type supplies the five-bit bound.

There is a case-related interface choice in the sources: BIP-173 requires lowercase encoder output, while its linked Python helper concatenates its supplied HRP without lowercasing it. This implementation follows the normative lowercase-output requirement and normalizes the HRP before checksumming. Exact round-trip identity is stated for canonical lowercase HRPs. For a printable uppercase HRP, the decoder returns its lowercase normalization, as the reference decoder does; preserving its original case would be a different specification.

## General theorems

All names below are in namespace `Bech32`.

| Theorem | Statement |
|---|---|
| `decode_encode` | For either variant and every `ValidInput`, decoding its encoding returns exactly the original HRP and payload. |
| `decode_encode_bech32` | BIP-173 specialization of that identity. |
| `decode_encode_bech32m` | BIP-350 specialization of that identity. |
| `decode_encode_normalized` | For every nonempty printable HRP satisfying the total length bound, decoding its encoding returns the lowercase HRP and original payload; no HRP case assumption is needed. |
| `verifyChecksum_createChecksum` | Appending the generated checksum makes verification succeed, for every HRP, payload, and variant. |
| `verifyChecksum_iff_createChecksum` | A six-symbol suffix verifies if and only if it equals the generated checksum. |
| `hrpExpand_toNat` | HRP expansion matches the BIP's natural-number high/low bits on its ASCII domain, without truncation. |
| `polymodStep_xor` | The concrete update is linear in its state and symbol under bitwise XOR. |
| `length_encode` | Encoded length is HRP length plus payload length plus seven. |
| `ValidInput.hrp_length_le_83` | Valid inputs satisfy the BIP's HRP length bound. |

The round-trip preconditions contain no checksum-acceptance assumption. The checksum proof derives acceptance from the state transition, and the parser proof uses that result.

## Build and audit

From this directory:

```sh
lake build
lake env lean Bech32/Audit.lean
```

The default library imports the vector modules, the milestone-2 modules, and the axiom audit. Every named vector is proved by kernel reduction using `decide`. The audit traverses every public `Bech32` declaration's transitive dependencies and fails the build if any axiom is outside `propext`, `Classical.choice`, and `Quot.sound`.

[VECTORS.md](VECTORS.md) inventories all 40 generic vectors and all 39 address-list occurrences from the two BIPs, including exact payload expectations and the distinction between format and address validity. `Bech32/EdgeCases.lean` adds boundary cases for case handling, ASCII endpoints, Unicode rejection, separators, length, and the full alphabet.

## Milestone 2: the error-detection guarantee

Milestone 2 (issue #16) machine-checks the BIPs' error-detection claims
against this implementation. Three new modules, all pure Lean core +
`Std` (still no Mathlib), all axioms audited to `propext`,
`Classical.choice`, `Quot.sound`:

* `Bech32/GF1024.lean` — the field `F_1024 = GF(32)[z]/(z² + z + 1)` on
  `BitVec 10`, with kernel-certified `exp`/`log` tables for the primitive
  element `γ = 1 + 3z`, the field laws, the log homomorphism, and the
  constant-word characterization `gf1024Log_mod_33`: for `a ≠ 0`,
  `gf1024Hi a = 0 ↔ gf1024Log a % 33 = 0` (the BCH view of the checksum:
  symbols are the residues of the syndrome polynomial at the generator's
  roots, and `33 = 1023 / 31` is the order of the constant subfield's
  multiplicative group).
* `Bech32/Distance.lean` — the distance theorem. The checksum transition
  is intertwined with multiplication in `F_1024^6`; the primitive
  (length-1023) code has designed distance 4, and the shortened code
  keeps distance 5 exactly up to **89 expanded symbols**: any error
  pattern of Hamming weight `≤ 4` in at most 89 expanded symbols has a
  nonzero syndrome (`polymod_ne_of_hammingDist_le_four`, and
  `verifyChecksum_false_of_substitutions_le_four`, uniform in
  `Variant`). The finite checks behind the elimination are boolean
  certificates discharged by `decide` — never `native_decide` — at
  bounded size. Sharpness witnesses (`exists_weight_four_kernel_length_90`
  and siblings) show the bounds cannot be improved: weight-4 kernel
  words exist at length 90, weight-5 at length 19, weight-6 at length 9,
  weight-2 at length 1024.
* `Bech32/ErrorDetection.lean` — parser inversion
  (`splitLast_eq_some_iff`, `decodeChars_eq_some_iff`: a complete
  characterization of when `decodeChars` succeeds), the string-level
  guarantees below, the BIP-350 insertion theorems, and the
  counterexample theorems.

### The BIP prose vs. the formal truth

BIP-173's prose says the checksum is "guaranteed to detect up to 4
errors" and BIP-350 repeats the claim for Bech32m. **As an unqualified
statement about strings, that claim is false**, and the boundary is
exact — each hypothesis of the true statements is witnessed necessary
by a kernel-checked counterexample pair of strings that both decode
(`decide`-proved, in `Bech32/ErrorDetection.lean`):

| Failure mechanism | Why the naive claim fails | Counterexample | Hypothesis that repairs it |
|---|---|---|---|
| Case twins | Decoding lowercases first, so an all-uppercase and the all-lowercase form of a short string are different strings at distance `≤ 4` that both decode. | `cex1_case_twins_bech32` / `_bech32m` | Compare strings after lowercasing (`hne` on lowered forms). |
| Separator relocation | The separator is the **last** `1`; a substitution can create or destroy a later `1`, moving the HRP/data boundary while keeping both strings valid. | `cex2a_separator_in_data_*`, `cex2b_separator_relocation_*` | Fix the separator positions (`hsep`), or fix the HRP outright (Form A). |
| Cross-block HRP characters | `hrpExpand` keeps only `c >>> 5` and `c &&& 31`; substitutions that change the high part (`c >>> 5` moving between the blocks `1, 2, 3`) alter the syndrome by a multiple the checksum cannot see at distance `≤ 4`. BIP-173 mentions the needed assumption only in Footnote 4. | `cex3a_cross_block_hrp_*`, `cex3b_*`, `cex3c_*` (at 2, 3, and 4 substitutions) | Preserve HRP high bits (`hhi`), as Footnote 4 assumes. |
| The 90-character cap | The cap is load-bearing: at 91 characters there are cross-HRP pairs at distance 4 whose data both verify (such strings are still rejected by `decode`, by length). | `cex_length_91_bech32` / `_bech32m` (at the `verifyChecksum` level) | Total length `≤ 90` characters (89 expanded symbols). |
| Cross-variant confusion | Bech32 and Bech32m share the transition and differ only in the final constant. | `cex_cross_variant_distance_three` (distance 3 exists) | Disjointness holds at distance `≤ 2` in range: `verifyChecksum_bech32_bech32m_disjoint_of_dist_le_two`. |

The true statements, all machine-checked, are:

* **Checksum layer** (`Distance.lean`): with the expanded form fixed —
  HRP length, separator, and HRP high bits as in `verifyChecksum`'s
  input — at most 4 substitutions among at most 89 expanded symbols
  never take a valid word to another valid word, for either variant
  (`verifyChecksum_false_of_substitutions_le_four`); with only the data
  varying, `verifyChecksum_false_of_data_substitutions_le_four`.
* **String level, fixed HRP (Form A)**: two same-length strings at
  Hamming distance `≤ 4` whose lowerings differ cannot both decode to
  the same HRP (`decode_ne_same_hrp_of_substitutions_le_four`, and the
  `encode` form `decode_encode_ne_same_hrp_of_substitutions_le_four`).
* **String level, separator + Footnote-4 form (Form B)**: if the
  separator positions agree and the HRP prefixes' high bits agree after
  lowercasing, a string at distance `≤ 4` from a decoding string does
  not decode at all (`decode_eq_none_of_substitutions_le_four`); the
  high-bit hypothesis comes for free when both HRP prefixes are
  alphabetic (`decode_eq_none_of_alpha_hrp_substitutions_le_four`), and
  for a **single** substitution it is unnecessary
  (`decode_eq_none_of_single_substitution`).

### The BIP-350 insertion point

BIP-350 changed the checksum constant to repair Bech32's insertion
weakness. Both directions are now theorems:

* `bech32_q_insertion_undetected`: for Bech32, inserting any number `k`
  of `q` characters (zero words) immediately before the final data word
  of a valid word **still verifies** — the weakness is real.
* `bech32m_q_insertion_detected`: for Bech32m, inserting
  `1 ≤ k ≤ 1022` zero words there **never verifies**. The proof
  evaluates states at the generator root `r = γ^172` of order 1023:
  insertion multiplies the evaluation by `r^k ≠ 1`
  (`rPow_ne_one`), and the Bech32m constant's evaluation has a nonzero
  high chunk (`stateEval_const_hi`), so no state fixed by the
  insertion can carry the constant.

## Prior art and next milestone

The programme's [issue #6 landscape assessment](https://github.com/derekblair/formalize-everything/issues/6), dated 2026-10-26, found one prior Lean artifact: [Dion/Network/Bech32.lean](https://github.com/RSoulatIOHK/Dion/blob/0c3c01f64b6e935e75cf9cb53061a0ae8605489e/Dion/Network/Bech32.lean). That file contains definitions and zero theorems, implements only the Bech32m final constant, and has neither decoding nor verification. Its encoder clamps byte values modulo 32. The assessment found no proof-assistant formalization of the BIPs' four-character error-detection guarantee. That absence is a dated research finding, not a theorem of this library.

Milestone 2 — the error-detection theorem and Bech32m's insertion-weakness repair property — is delivered by this change (issue #16), pending the crossed-pool review required before merge. A later landscape check (recorded on issue #16) also found the ACL2/Kestrel Bech32 development: it formalizes the Bech32 definitions and guard lemmas, but not the error-detection guarantee, which remained unproved in any proof assistant before this work. As the milestone-2 section above documents, the guarantee holds only in its refined forms: the substitution model, case normalization, length bounds, and HRP assumptions are part of the theorems, and each is witnessed necessary by a kernel-checked counterexample.
