# Test-vector inventory

The authoritative inputs are [BIP-173](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0173.mediawiki#test-vectors) and [BIP-350](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0350.mediawiki#test-vectors), pinned to bitcoin/bips commit `100ba872c808946155b1eeb8c4568058f2eea0a7`.

| Source list | Occurrences | Generic acceptance | Generic rejection |
|---|---:|---:|---:|
| BIP-173 generic valid | 7 | 7 | 0 |
| BIP-173 generic invalid | 12 | 0 | 12 |
| BIP-350 generic valid | 7 | 7 | 0 |
| BIP-350 generic invalid | 14 | 0 | 14 |
| BIP-173 address valid | 6 | 6 | 0 |
| BIP-173 address invalid | 10 | 8 | 2 |
| BIP-350 address valid | 8 | 8 | 0 |
| BIP-350 address invalid | 15 | 13 | 2 |
| **Total** | **79** | **49** | **30** |

There are **40 generic vectors**, all checked against the BIPs' stated generic validity. The additional **39 address-list occurrences** retain duplicates between BIPs and test their generic encoding layer only. Many invalid SegWit addresses are valid generic Bech32 or Bech32m strings. Rejecting those strings here would be a specification error. These tests do not claim SegWit validation or scriptPubKey conversion.

Every occurrence has a named theorem in `Bech32/Vectors.lean`, proved with `by decide`. Accepted strings have four assertions: exact decoded HRP and five-bit payload, successful checksum verification using the literal data including its six checksum symbols, exact lowercase re-encoding, and rejection by the opposite checksum variant. Rejected strings have two assertions: rejection by each variant. Expected payload symbols are read directly through the BIP alphabet; they are literals in the Lean source, independent of the codec under test. There are **256 assertions** across the 79 theorems.

`Bech32/EdgeCases.lean` adds **14 boundary theorems with 29 assertions**, also checked by `decide`: empty input and HRP, missing and repeated separators, both directions of mixed case, printable-ASCII endpoints, out-of-range and Unicode characters, total length 90 versus 91, empty payload, all 32 alphabet symbols, the opposite checksum variant, and uppercase encoder-input normalization. These extra checks are not counted as BIP vector occurrences.

In the table below, “Bech32” and “Bech32m” mean accepted by that generic decoder and rejected by the other. “Reject” means rejected by both generic decoders. The source description concerns the original list's layer. `\xNN` represents the literal character with the given code point; it is not the four characters backslash, x, and two digits.

| Theorem | Literal input | Generic result | Source description |
|---|---|---|---|
| `bip173_valid_01` | `A12UEL5L` | Bech32 | Valid generic checksum encoding |
| `bip173_valid_02` | `a12uel5l` | Bech32 | Valid generic checksum encoding |
| `bip173_valid_03` | `an83characterlonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio1tt5tgs` | Bech32 | Valid generic checksum encoding |
| `bip173_valid_04` | `abcdef1qpzry9x8gf2tvdw0s3jn54khce6mua7lmqqqxw` | Bech32 | Valid generic checksum encoding |
| `bip173_valid_05` | `11qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqc8247j` | Bech32 | Valid generic checksum encoding |
| `bip173_valid_06` | `split1checkupstagehandshakeupstreamerranterredcaperred2y9e3w` | Bech32 | Valid generic checksum encoding |
| `bip173_valid_07` | `?1ezyfcl` | Bech32 | Valid generic checksum encoding |
| `bip173_invalid_01` | ` 1nwldj5` | Reject | HRP character out of range |
| `bip173_invalid_02` | `\x7f1axkwrx` | Reject | HRP character out of range |
| `bip173_invalid_03` | `\x801eym55h` | Reject | HRP character out of range |
| `bip173_invalid_04` | `an84characterslonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio1569pvx` | Reject | overall max length exceeded |
| `bip173_invalid_05` | `pzry9x0s0muk` | Reject | No separator character |
| `bip173_invalid_06` | `1pzry9x0s0muk` | Reject | Empty HRP |
| `bip173_invalid_07` | `x1b4n0q5v` | Reject | Invalid data character |
| `bip173_invalid_08` | `li1dgmt3` | Reject | Too short checksum |
| `bip173_invalid_09` | `de1lg7wt\xff` | Reject | Invalid character in checksum |
| `bip173_invalid_10` | `A1G7SGD8` | Reject | checksum calculated with uppercase form of HRP |
| `bip173_invalid_11` | `10a06t8` | Reject | empty HRP |
| `bip173_invalid_12` | `1qzzfhee` | Reject | empty HRP |
| `bip173_address_valid_01` | `BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4` | Bech32 | Valid SegWit address in the source BIP |
| `bip173_address_valid_02` | `tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7` | Bech32 | Valid SegWit address in the source BIP |
| `bip173_address_valid_03` | `bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7k7grplx` | Bech32 | Valid SegWit address in the source BIP |
| `bip173_address_valid_04` | `BC1SW50QA3JX3S` | Bech32 | Valid SegWit address in the source BIP |
| `bip173_address_valid_05` | `bc1zw508d6qejxtdg4y5r3zarvaryvg6kdaj` | Bech32 | Valid SegWit address in the source BIP |
| `bip173_address_valid_06` | `tb1qqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesrxh6hy` | Bech32 | Valid SegWit address in the source BIP |
| `bip173_address_invalid_01` | `tc1qw508d6qejxtdg4y5r3zarvary0c5xw7kg3g4ty` | Bech32 | Invalid human-readable part |
| `bip173_address_invalid_02` | `bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t5` | Reject | Invalid checksum |
| `bip173_address_invalid_03` | `BC13W508D6QEJXTDG4Y5R3ZARVARY0C5XW7KN40WF2` | Bech32 | Invalid witness version |
| `bip173_address_invalid_04` | `bc1rw5uspcuh` | Bech32 | Invalid program length |
| `bip173_address_invalid_05` | `bc10w508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kw5rljs90` | Bech32 | Invalid program length |
| `bip173_address_invalid_06` | `BC1QR508D6QEJXTDG4Y5R3ZARVARYV98GJ9P` | Bech32 | Invalid program length for witness version 0 (per BIP141) |
| `bip173_address_invalid_07` | `tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sL5k7` | Reject | Mixed case |
| `bip173_address_invalid_08` | `bc1zw508d6qejxtdg4y5r3zarvaryvqyzf3du` | Bech32 | zero padding of more than 4 bits |
| `bip173_address_invalid_09` | `tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3pjxtptv` | Bech32 | Non-zero padding in 8-to-5 conversion |
| `bip173_address_invalid_10` | `bc1gmk9yu` | Bech32 | Empty data section |
| `bip350_valid_01` | `A1LQFN3A` | Bech32m | Valid generic checksum encoding |
| `bip350_valid_02` | `a1lqfn3a` | Bech32m | Valid generic checksum encoding |
| `bip350_valid_03` | `an83characterlonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11sg7hg6` | Bech32m | Valid generic checksum encoding |
| `bip350_valid_04` | `abcdef1l7aum6echk45nj3s0wdvt2fg8x9yrzpqzd3ryx` | Bech32m | Valid generic checksum encoding |
| `bip350_valid_05` | `11llllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllludsr8` | Bech32m | Valid generic checksum encoding |
| `bip350_valid_06` | `split1checkupstagehandshakeupstreamerranterredcaperredlc445v` | Bech32m | Valid generic checksum encoding |
| `bip350_valid_07` | `?1v759aa` | Bech32m | Valid generic checksum encoding |
| `bip350_invalid_01` | ` 1xj0phk` | Reject | HRP character out of range |
| `bip350_invalid_02` | `\x7f1g6xzxy` | Reject | HRP character out of range |
| `bip350_invalid_03` | `\x801vctc34` | Reject | HRP character out of range |
| `bip350_invalid_04` | `an84characterslonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11d6pts4` | Reject | overall max length exceeded |
| `bip350_invalid_05` | `qyrz8wqd2c9m` | Reject | No separator character |
| `bip350_invalid_06` | `1qyrz8wqd2c9m` | Reject | Empty HRP |
| `bip350_invalid_07` | `y1b0jsk6g` | Reject | Invalid data character |
| `bip350_invalid_08` | `lt1igcx5c0` | Reject | Invalid data character |
| `bip350_invalid_09` | `in1muywd` | Reject | Too short checksum |
| `bip350_invalid_10` | `mm1crxm3i` | Reject | Invalid character in checksum |
| `bip350_invalid_11` | `au1s5cgom` | Reject | Invalid character in checksum |
| `bip350_invalid_12` | `M1VUXWEZ` | Reject | checksum calculated with uppercase form of HRP |
| `bip350_invalid_13` | `16plkw9` | Reject | empty HRP |
| `bip350_invalid_14` | `1p2gdwpf` | Reject | empty HRP |
| `bip350_address_valid_01` | `BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4` | Bech32 | Valid SegWit address in the source BIP |
| `bip350_address_valid_02` | `tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7` | Bech32 | Valid SegWit address in the source BIP |
| `bip350_address_valid_03` | `bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kt5nd6y` | Bech32m | Valid SegWit address in the source BIP |
| `bip350_address_valid_04` | `BC1SW50QGDZ25J` | Bech32m | Valid SegWit address in the source BIP |
| `bip350_address_valid_05` | `bc1zw508d6qejxtdg4y5r3zarvaryvaxxpcs` | Bech32m | Valid SegWit address in the source BIP |
| `bip350_address_valid_06` | `tb1qqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesrxh6hy` | Bech32 | Valid SegWit address in the source BIP |
| `bip350_address_valid_07` | `tb1pqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesf3hn0c` | Bech32m | Valid SegWit address in the source BIP |
| `bip350_address_valid_08` | `bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0` | Bech32m | Valid SegWit address in the source BIP |
| `bip350_address_invalid_01` | `tc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq5zuyut` | Bech32m | Invalid human-readable part |
| `bip350_address_invalid_02` | `bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqh2y7hd` | Bech32 | Invalid checksum (Bech32 instead of Bech32m) |
| `bip350_address_invalid_03` | `tb1z0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqglt7rf` | Bech32 | Invalid checksum (Bech32 instead of Bech32m) |
| `bip350_address_invalid_04` | `BC1S0XLXVLHEMJA6C4DQV22UAPCTQUPFHLXM9H8Z3K2E72Q4K9HCZ7VQ54WELL` | Bech32 | Invalid checksum (Bech32 instead of Bech32m) |
| `bip350_address_invalid_05` | `bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kemeawh` | Bech32m | Invalid checksum (Bech32m instead of Bech32) |
| `bip350_address_invalid_06` | `tb1q0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq24jc47` | Bech32m | Invalid checksum (Bech32m instead of Bech32) |
| `bip350_address_invalid_07` | `bc1p38j9r5y49hruaue7wxjce0updqjuyyx0kh56v8s25huc6995vvpql3jow4` | Reject | Invalid character in checksum |
| `bip350_address_invalid_08` | `BC130XLXVLHEMJA6C4DQV22UAPCTQUPFHLXM9H8Z3K2E72Q4K9HCZ7VQ7ZWS8R` | Bech32m | Invalid witness version |
| `bip350_address_invalid_09` | `bc1pw5dgrnzv` | Bech32m | Invalid program length (1 byte) |
| `bip350_address_invalid_10` | `bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v8n0nx0muaewav253zgeav` | Bech32m | Invalid program length (41 bytes) |
| `bip350_address_invalid_11` | `BC1QR508D6QEJXTDG4Y5R3ZARVARYV98GJ9P` | Bech32 | Invalid program length for witness version 0 (per BIP141) |
| `bip350_address_invalid_12` | `tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq47Zagq` | Reject | Mixed case |
| `bip350_address_invalid_13` | `bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v07qwwzcrf` | Bech32m | zero padding of more than 4 bits |
| `bip350_address_invalid_14` | `tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vpggkg4j` | Bech32m | Non-zero padding in 8-to-5 conversion |
| `bip350_address_invalid_15` | `bc1gmk9yu` | Bech32 | Empty data section |
