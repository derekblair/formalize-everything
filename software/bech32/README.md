# Bech32 and Bech32m

Milestone 1 of [issue #6](https://github.com/derekblair/formalize-everything/issues/6): an executable generic checksummed base32 specification, kernel-checked vectors, and encode/decode correctness. The catalogue remains **milestone 1 in progress** until the required independent review passes.

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

The default library imports both vector modules and the axiom audit. Every named vector is proved by kernel reduction using `decide`. The audit traverses every public `Bech32` declaration's transitive dependencies and fails the build if any axiom is outside `propext`, `Classical.choice`, and `Quot.sound`.

[VECTORS.md](VECTORS.md) inventories all 40 generic vectors and all 39 address-list occurrences from the two BIPs, including exact payload expectations and the distinction between format and address validity. `Bech32/EdgeCases.lean` adds boundary cases for case handling, ASCII endpoints, Unicode rejection, separators, length, and the full alphabet.

## Prior art and next milestone

The programme's [issue #6 landscape assessment](https://github.com/derekblair/formalize-everything/issues/6), dated 2026-10-26, found one prior Lean artifact: [Dion/Network/Bech32.lean](https://github.com/RSoulatIOHK/Dion/blob/0c3c01f64b6e935e75cf9cb53061a0ae8605489e/Dion/Network/Bech32.lean). That file contains definitions and zero theorems, implements only the Bech32m final constant, and has neither decoding nor verification. Its encoder clamps byte values modulo 32. The assessment found no proof-assistant formalization of the BIPs' four-character error-detection guarantee. That absence is a dated research finding, not a theorem of this library.

Milestone 2 still needs the error-detection theorem and Bech32m's insertion-weakness repair property. The executable parser, explicit character alphabet, normalized HRP expansion, fixed-width state transition, and variant constants expose the ingredients needed to state those properties against this implementation. The future proof must specify its substitution model, case normalization, length bounds, and HRP assumptions faithfully; checksum correctness alone does not prove distance or insertion guarantees. Crossed-pool review on the issue's designated reviewer pool remains required before merge.
