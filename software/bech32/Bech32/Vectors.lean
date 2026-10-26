import Bech32.Codec

/-!
# BIP-173 and BIP-350 vectors

Source: bitcoin/bips at commit 100ba872c808946155b1eeb8c4568058f2eea0a7.
Each theorem is proved by kernel reduction. The 40 generic vectors have the
validity expected by the BIP. The 39 address-list occurrences test only their
generic checksum layer: witness version, program length, network, bit conversion,
and witness/checksum-variant matching belong to the later SegWit milestone.
See VECTORS.md for the per-list inventory and the distinction between these layers.
-/

namespace Bech32.Vectors

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- BIP-173: valid (7 occurrences). -/

theorem bip173_valid_01 :
    decode .bech32 "A12UEL5L" =
      some ("a", []) ∧
    verifyChecksum .bech32 "a".toList [10, 28, 25, 31, 20, 31] = true ∧
    encode .bech32 "a" [] = "a12uel5l" ∧
    decode .bech32m "A12UEL5L" = none := by decide

theorem bip173_valid_02 :
    decode .bech32 "a12uel5l" =
      some ("a", []) ∧
    verifyChecksum .bech32 "a".toList [10, 28, 25, 31, 20, 31] = true ∧
    encode .bech32 "a" [] = "a12uel5l" ∧
    decode .bech32m "a12uel5l" = none := by decide

theorem bip173_valid_03 :
    decode .bech32 "an83characterlonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio1tt5tgs" =
      some ("an83characterlonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio", []) ∧
    verifyChecksum .bech32 "an83characterlonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio".toList [11, 11, 20, 11, 8, 16] = true ∧
    encode .bech32 "an83characterlonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio" [] = "an83characterlonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio1tt5tgs" ∧
    decode .bech32m "an83characterlonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio1tt5tgs" = none := by decide

theorem bip173_valid_04 :
    decode .bech32 "abcdef1qpzry9x8gf2tvdw0s3jn54khce6mua7lmqqqxw" =
      some ("abcdef", [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]) ∧
    verifyChecksum .bech32 "abcdef".toList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 27, 0, 0, 0, 6, 14] = true ∧
    encode .bech32 "abcdef" [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] = "abcdef1qpzry9x8gf2tvdw0s3jn54khce6mua7lmqqqxw" ∧
    decode .bech32m "abcdef1qpzry9x8gf2tvdw0s3jn54khce6mua7lmqqqxw" = none := by decide

theorem bip173_valid_05 :
    decode .bech32 "11qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqc8247j" =
      some ("1", [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
    verifyChecksum .bech32 "1".toList [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 7, 10, 21, 30, 18] = true ∧
    encode .bech32 "1" [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = "11qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqc8247j" ∧
    decode .bech32m "11qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqc8247j" = none := by decide

theorem bip173_valid_06 :
    decode .bech32 "split1checkupstagehandshakeupstreamerranterredcaperred2y9e3w" =
      some ("split", [24, 23, 25, 24, 22, 28, 1, 16, 11, 29, 8, 25, 23, 29, 19, 13, 16, 23, 29, 22, 25, 28, 1, 16, 11, 3, 25, 29, 27, 25, 3, 3, 29, 19, 11, 25, 3, 3, 25, 13, 24, 29, 1, 25, 3, 3, 25, 13]) ∧
    verifyChecksum .bech32 "split".toList [24, 23, 25, 24, 22, 28, 1, 16, 11, 29, 8, 25, 23, 29, 19, 13, 16, 23, 29, 22, 25, 28, 1, 16, 11, 3, 25, 29, 27, 25, 3, 3, 29, 19, 11, 25, 3, 3, 25, 13, 24, 29, 1, 25, 3, 3, 25, 13, 10, 4, 5, 25, 17, 14] = true ∧
    encode .bech32 "split" [24, 23, 25, 24, 22, 28, 1, 16, 11, 29, 8, 25, 23, 29, 19, 13, 16, 23, 29, 22, 25, 28, 1, 16, 11, 3, 25, 29, 27, 25, 3, 3, 29, 19, 11, 25, 3, 3, 25, 13, 24, 29, 1, 25, 3, 3, 25, 13] = "split1checkupstagehandshakeupstreamerranterredcaperred2y9e3w" ∧
    decode .bech32m "split1checkupstagehandshakeupstreamerranterredcaperred2y9e3w" = none := by decide

theorem bip173_valid_07 :
    decode .bech32 "?1ezyfcl" =
      some ("?", []) ∧
    verifyChecksum .bech32 "?".toList [25, 2, 4, 9, 24, 31] = true ∧
    encode .bech32 "?" [] = "?1ezyfcl" ∧
    decode .bech32m "?1ezyfcl" = none := by decide

/- BIP-173: invalid (12 occurrences). -/

theorem bip173_invalid_01 :
    decode .bech32 " 1nwldj5" = none ∧
    decode .bech32m " 1nwldj5" = none := by decide

theorem bip173_invalid_02 :
    decode .bech32 "\x7f1axkwrx" = none ∧
    decode .bech32m "\x7f1axkwrx" = none := by decide

theorem bip173_invalid_03 :
    decode .bech32 "\x801eym55h" = none ∧
    decode .bech32m "\x801eym55h" = none := by decide

theorem bip173_invalid_04 :
    decode .bech32 "an84characterslonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio1569pvx" = none ∧
    decode .bech32m "an84characterslonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio1569pvx" = none := by decide

theorem bip173_invalid_05 :
    decode .bech32 "pzry9x0s0muk" = none ∧
    decode .bech32m "pzry9x0s0muk" = none := by decide

theorem bip173_invalid_06 :
    decode .bech32 "1pzry9x0s0muk" = none ∧
    decode .bech32m "1pzry9x0s0muk" = none := by decide

theorem bip173_invalid_07 :
    decode .bech32 "x1b4n0q5v" = none ∧
    decode .bech32m "x1b4n0q5v" = none := by decide

theorem bip173_invalid_08 :
    decode .bech32 "li1dgmt3" = none ∧
    decode .bech32m "li1dgmt3" = none := by decide

theorem bip173_invalid_09 :
    decode .bech32 "de1lg7wt\xff" = none ∧
    decode .bech32m "de1lg7wt\xff" = none := by decide

theorem bip173_invalid_10 :
    decode .bech32 "A1G7SGD8" = none ∧
    decode .bech32m "A1G7SGD8" = none := by decide

theorem bip173_invalid_11 :
    decode .bech32 "10a06t8" = none ∧
    decode .bech32m "10a06t8" = none := by decide

theorem bip173_invalid_12 :
    decode .bech32 "1qzzfhee" = none ∧
    decode .bech32m "1qzzfhee" = none := by decide

/- BIP-173: address valid (6 occurrences). -/

theorem bip173_address_valid_01 :
    decode .bech32 "BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4" =
      some ("bc", [0, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22]) ∧
    verifyChecksum .bech32 "bc".toList [0, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 12, 7, 9, 17, 11, 21] = true ∧
    encode .bech32 "bc" [0, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22] = "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4" ∧
    decode .bech32m "BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4" = none := by decide

theorem bip173_address_valid_02 :
    decode .bech32 "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7" =
      some ("tb", [0, 3, 1, 17, 17, 8, 15, 0, 20, 24, 20, 11, 6, 16, 1, 5, 29, 3, 4, 16, 3, 6, 21, 22, 26, 2, 13, 22, 9, 16, 21, 19, 24, 25, 21, 6, 18, 15, 8, 13, 24, 24, 24, 25, 9, 12, 1, 4, 16, 6, 9, 17, 0]) ∧
    verifyChecksum .bech32 "tb".toList [0, 3, 1, 17, 17, 8, 15, 0, 20, 24, 20, 11, 6, 16, 1, 5, 29, 3, 4, 16, 3, 6, 21, 22, 26, 2, 13, 22, 9, 16, 21, 19, 24, 25, 21, 6, 18, 15, 8, 13, 24, 24, 24, 25, 9, 12, 1, 4, 16, 6, 9, 17, 0, 15, 16, 31, 20, 22, 30] = true ∧
    encode .bech32 "tb" [0, 3, 1, 17, 17, 8, 15, 0, 20, 24, 20, 11, 6, 16, 1, 5, 29, 3, 4, 16, 3, 6, 21, 22, 26, 2, 13, 22, 9, 16, 21, 19, 24, 25, 21, 6, 18, 15, 8, 13, 24, 24, 24, 25, 9, 12, 1, 4, 16, 6, 9, 17, 0] = "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7" ∧
    decode .bech32m "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7" = none := by decide

theorem bip173_address_valid_03 :
    decode .bech32 "bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7k7grplx" =
      some ("bc", [1, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22]) ∧
    verifyChecksum .bech32 "bc".toList [1, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 30, 8, 3, 1, 31, 6] = true ∧
    encode .bech32 "bc" [1, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22] = "bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7k7grplx" ∧
    decode .bech32m "bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7k7grplx" = none := by decide

theorem bip173_address_valid_04 :
    decode .bech32 "BC1SW50QA3JX3S" =
      some ("bc", [16, 14, 20, 15, 0]) ∧
    verifyChecksum .bech32 "bc".toList [16, 14, 20, 15, 0, 29, 17, 18, 6, 17, 16] = true ∧
    encode .bech32 "bc" [16, 14, 20, 15, 0] = "bc1sw50qa3jx3s" ∧
    decode .bech32m "BC1SW50QA3JX3S" = none := by decide

theorem bip173_address_valid_05 :
    decode .bech32 "bc1zw508d6qejxtdg4y5r3zarvaryvg6kdaj" =
      some ("bc", [2, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 12]) ∧
    verifyChecksum .bech32 "bc".toList [2, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 12, 8, 26, 22, 13, 29, 18] = true ∧
    encode .bech32 "bc" [2, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 12] = "bc1zw508d6qejxtdg4y5r3zarvaryvg6kdaj" ∧
    decode .bech32m "bc1zw508d6qejxtdg4y5r3zarvaryvg6kdaj" = none := by decide

theorem bip173_address_valid_06 :
    decode .bech32 "tb1qqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesrxh6hy" =
      some ("tb", [0, 0, 0, 0, 0, 1, 17, 5, 5, 25, 11, 10, 6, 4, 8, 13, 18, 20, 6, 3, 25, 0, 23, 18, 18, 12, 24, 27, 2, 23, 6, 14, 21, 29, 4, 14, 6, 25, 24, 18, 13, 2, 25, 14, 26, 23, 4, 31, 8, 12, 16, 25, 16]) ∧
    verifyChecksum .bech32 "tb".toList [0, 0, 0, 0, 0, 1, 17, 5, 5, 25, 11, 10, 6, 4, 8, 13, 18, 20, 6, 3, 25, 0, 23, 18, 18, 12, 24, 27, 2, 23, 6, 14, 21, 29, 4, 14, 6, 25, 24, 18, 13, 2, 25, 14, 26, 23, 4, 31, 8, 12, 16, 25, 16, 3, 6, 23, 26, 23, 4] = true ∧
    encode .bech32 "tb" [0, 0, 0, 0, 0, 1, 17, 5, 5, 25, 11, 10, 6, 4, 8, 13, 18, 20, 6, 3, 25, 0, 23, 18, 18, 12, 24, 27, 2, 23, 6, 14, 21, 29, 4, 14, 6, 25, 24, 18, 13, 2, 25, 14, 26, 23, 4, 31, 8, 12, 16, 25, 16] = "tb1qqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesrxh6hy" ∧
    decode .bech32m "tb1qqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesrxh6hy" = none := by decide

/- BIP-173: address invalid (10 occurrences). -/

theorem bip173_address_invalid_01 :
    decode .bech32 "tc1qw508d6qejxtdg4y5r3zarvary0c5xw7kg3g4ty" =
      some ("tc", [0, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22]) ∧
    verifyChecksum .bech32 "tc".toList [0, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 8, 17, 8, 21, 11, 4] = true ∧
    encode .bech32 "tc" [0, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22] = "tc1qw508d6qejxtdg4y5r3zarvary0c5xw7kg3g4ty" ∧
    decode .bech32m "tc1qw508d6qejxtdg4y5r3zarvary0c5xw7kg3g4ty" = none := by decide

theorem bip173_address_invalid_02 :
    decode .bech32 "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t5" = none ∧
    decode .bech32m "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t5" = none := by decide

theorem bip173_address_invalid_03 :
    decode .bech32 "BC13W508D6QEJXTDG4Y5R3ZARVARY0C5XW7KN40WF2" =
      some ("bc", [17, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22]) ∧
    verifyChecksum .bech32 "bc".toList [17, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 19, 21, 15, 14, 9, 10] = true ∧
    encode .bech32 "bc" [17, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22] = "bc13w508d6qejxtdg4y5r3zarvary0c5xw7kn40wf2" ∧
    decode .bech32m "BC13W508D6QEJXTDG4Y5R3ZARVARY0C5XW7KN40WF2" = none := by decide

theorem bip173_address_invalid_04 :
    decode .bech32 "bc1rw5uspcuh" =
      some ("bc", [3, 14, 20]) ∧
    verifyChecksum .bech32 "bc".toList [3, 14, 20, 28, 16, 1, 24, 28, 23] = true ∧
    encode .bech32 "bc" [3, 14, 20] = "bc1rw5uspcuh" ∧
    decode .bech32m "bc1rw5uspcuh" = none := by decide

theorem bip173_address_invalid_05 :
    decode .bech32 "bc10w508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kw5rljs90" =
      some ("bc", [15, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 14, 20]) ∧
    verifyChecksum .bech32 "bc".toList [15, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 14, 20, 3, 31, 18, 16, 5, 15] = true ∧
    encode .bech32 "bc" [15, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 14, 20] = "bc10w508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kw5rljs90" ∧
    decode .bech32m "bc10w508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kw5rljs90" = none := by decide

theorem bip173_address_invalid_06 :
    decode .bech32 "BC1QR508D6QEJXTDG4Y5R3ZARVARYV98GJ9P" =
      some ("bc", [0, 3, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 12]) ∧
    verifyChecksum .bech32 "bc".toList [0, 3, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 12, 5, 7, 8, 18, 5, 1] = true ∧
    encode .bech32 "bc" [0, 3, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 12] = "bc1qr508d6qejxtdg4y5r3zarvaryv98gj9p" ∧
    decode .bech32m "BC1QR508D6QEJXTDG4Y5R3ZARVARYV98GJ9P" = none := by decide

theorem bip173_address_invalid_07 :
    decode .bech32 "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sL5k7" = none ∧
    decode .bech32m "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sL5k7" = none := by decide

theorem bip173_address_invalid_08 :
    decode .bech32 "bc1zw508d6qejxtdg4y5r3zarvaryvqyzf3du" =
      some ("bc", [2, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 12, 0]) ∧
    verifyChecksum .bech32 "bc".toList [2, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 12, 0, 4, 2, 9, 17, 13, 28] = true ∧
    encode .bech32 "bc" [2, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 12, 0] = "bc1zw508d6qejxtdg4y5r3zarvaryvqyzf3du" ∧
    decode .bech32m "bc1zw508d6qejxtdg4y5r3zarvaryvqyzf3du" = none := by decide

theorem bip173_address_invalid_09 :
    decode .bech32 "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3pjxtptv" =
      some ("tb", [0, 3, 1, 17, 17, 8, 15, 0, 20, 24, 20, 11, 6, 16, 1, 5, 29, 3, 4, 16, 3, 6, 21, 22, 26, 2, 13, 22, 9, 16, 21, 19, 24, 25, 21, 6, 18, 15, 8, 13, 24, 24, 24, 25, 9, 12, 1, 4, 16, 6, 9, 17, 1]) ∧
    verifyChecksum .bech32 "tb".toList [0, 3, 1, 17, 17, 8, 15, 0, 20, 24, 20, 11, 6, 16, 1, 5, 29, 3, 4, 16, 3, 6, 21, 22, 26, 2, 13, 22, 9, 16, 21, 19, 24, 25, 21, 6, 18, 15, 8, 13, 24, 24, 24, 25, 9, 12, 1, 4, 16, 6, 9, 17, 1, 18, 6, 11, 1, 11, 12] = true ∧
    encode .bech32 "tb" [0, 3, 1, 17, 17, 8, 15, 0, 20, 24, 20, 11, 6, 16, 1, 5, 29, 3, 4, 16, 3, 6, 21, 22, 26, 2, 13, 22, 9, 16, 21, 19, 24, 25, 21, 6, 18, 15, 8, 13, 24, 24, 24, 25, 9, 12, 1, 4, 16, 6, 9, 17, 1] = "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3pjxtptv" ∧
    decode .bech32m "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3pjxtptv" = none := by decide

theorem bip173_address_invalid_10 :
    decode .bech32 "bc1gmk9yu" =
      some ("bc", []) ∧
    verifyChecksum .bech32 "bc".toList [8, 27, 22, 5, 4, 28] = true ∧
    encode .bech32 "bc" [] = "bc1gmk9yu" ∧
    decode .bech32m "bc1gmk9yu" = none := by decide

/- BIP-350: valid (7 occurrences). -/

theorem bip350_valid_01 :
    decode .bech32m "A1LQFN3A" =
      some ("a", []) ∧
    verifyChecksum .bech32m "a".toList [31, 0, 9, 19, 17, 29] = true ∧
    encode .bech32m "a" [] = "a1lqfn3a" ∧
    decode .bech32 "A1LQFN3A" = none := by decide

theorem bip350_valid_02 :
    decode .bech32m "a1lqfn3a" =
      some ("a", []) ∧
    verifyChecksum .bech32m "a".toList [31, 0, 9, 19, 17, 29] = true ∧
    encode .bech32m "a" [] = "a1lqfn3a" ∧
    decode .bech32 "a1lqfn3a" = none := by decide

theorem bip350_valid_03 :
    decode .bech32m "an83characterlonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11sg7hg6" =
      some ("an83characterlonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber1", []) ∧
    verifyChecksum .bech32m "an83characterlonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber1".toList [16, 8, 30, 23, 8, 26] = true ∧
    encode .bech32m "an83characterlonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber1" [] = "an83characterlonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11sg7hg6" ∧
    decode .bech32 "an83characterlonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11sg7hg6" = none := by decide

theorem bip350_valid_04 :
    decode .bech32m "abcdef1l7aum6echk45nj3s0wdvt2fg8x9yrzpqzd3ryx" =
      some ("abcdef", [31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]) ∧
    verifyChecksum .bech32m "abcdef".toList [31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 2, 13, 17, 3, 4, 6] = true ∧
    encode .bech32m "abcdef" [31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] = "abcdef1l7aum6echk45nj3s0wdvt2fg8x9yrzpqzd3ryx" ∧
    decode .bech32 "abcdef1l7aum6echk45nj3s0wdvt2fg8x9yrzpqzd3ryx" = none := by decide

theorem bip350_valid_05 :
    decode .bech32m "11llllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllludsr8" =
      some ("1", [31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31]) ∧
    verifyChecksum .bech32m "1".toList [31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 28, 13, 16, 3, 7] = true ∧
    encode .bech32m "1" [31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31] = "11llllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllludsr8" ∧
    decode .bech32 "11llllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllludsr8" = none := by decide

theorem bip350_valid_06 :
    decode .bech32m "split1checkupstagehandshakeupstreamerranterredcaperredlc445v" =
      some ("split", [24, 23, 25, 24, 22, 28, 1, 16, 11, 29, 8, 25, 23, 29, 19, 13, 16, 23, 29, 22, 25, 28, 1, 16, 11, 3, 25, 29, 27, 25, 3, 3, 29, 19, 11, 25, 3, 3, 25, 13, 24, 29, 1, 25, 3, 3, 25, 13]) ∧
    verifyChecksum .bech32m "split".toList [24, 23, 25, 24, 22, 28, 1, 16, 11, 29, 8, 25, 23, 29, 19, 13, 16, 23, 29, 22, 25, 28, 1, 16, 11, 3, 25, 29, 27, 25, 3, 3, 29, 19, 11, 25, 3, 3, 25, 13, 24, 29, 1, 25, 3, 3, 25, 13, 31, 24, 21, 21, 20, 12] = true ∧
    encode .bech32m "split" [24, 23, 25, 24, 22, 28, 1, 16, 11, 29, 8, 25, 23, 29, 19, 13, 16, 23, 29, 22, 25, 28, 1, 16, 11, 3, 25, 29, 27, 25, 3, 3, 29, 19, 11, 25, 3, 3, 25, 13, 24, 29, 1, 25, 3, 3, 25, 13] = "split1checkupstagehandshakeupstreamerranterredcaperredlc445v" ∧
    decode .bech32 "split1checkupstagehandshakeupstreamerranterredcaperredlc445v" = none := by decide

theorem bip350_valid_07 :
    decode .bech32m "?1v759aa" =
      some ("?", []) ∧
    verifyChecksum .bech32m "?".toList [12, 30, 20, 5, 29, 29] = true ∧
    encode .bech32m "?" [] = "?1v759aa" ∧
    decode .bech32 "?1v759aa" = none := by decide

/- BIP-350: invalid (14 occurrences). -/

theorem bip350_invalid_01 :
    decode .bech32 " 1xj0phk" = none ∧
    decode .bech32m " 1xj0phk" = none := by decide

theorem bip350_invalid_02 :
    decode .bech32 "\x7f1g6xzxy" = none ∧
    decode .bech32m "\x7f1g6xzxy" = none := by decide

theorem bip350_invalid_03 :
    decode .bech32 "\x801vctc34" = none ∧
    decode .bech32m "\x801vctc34" = none := by decide

theorem bip350_invalid_04 :
    decode .bech32 "an84characterslonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11d6pts4" = none ∧
    decode .bech32m "an84characterslonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11d6pts4" = none := by decide

theorem bip350_invalid_05 :
    decode .bech32 "qyrz8wqd2c9m" = none ∧
    decode .bech32m "qyrz8wqd2c9m" = none := by decide

theorem bip350_invalid_06 :
    decode .bech32 "1qyrz8wqd2c9m" = none ∧
    decode .bech32m "1qyrz8wqd2c9m" = none := by decide

theorem bip350_invalid_07 :
    decode .bech32 "y1b0jsk6g" = none ∧
    decode .bech32m "y1b0jsk6g" = none := by decide

theorem bip350_invalid_08 :
    decode .bech32 "lt1igcx5c0" = none ∧
    decode .bech32m "lt1igcx5c0" = none := by decide

theorem bip350_invalid_09 :
    decode .bech32 "in1muywd" = none ∧
    decode .bech32m "in1muywd" = none := by decide

theorem bip350_invalid_10 :
    decode .bech32 "mm1crxm3i" = none ∧
    decode .bech32m "mm1crxm3i" = none := by decide

theorem bip350_invalid_11 :
    decode .bech32 "au1s5cgom" = none ∧
    decode .bech32m "au1s5cgom" = none := by decide

theorem bip350_invalid_12 :
    decode .bech32 "M1VUXWEZ" = none ∧
    decode .bech32m "M1VUXWEZ" = none := by decide

theorem bip350_invalid_13 :
    decode .bech32 "16plkw9" = none ∧
    decode .bech32m "16plkw9" = none := by decide

theorem bip350_invalid_14 :
    decode .bech32 "1p2gdwpf" = none ∧
    decode .bech32m "1p2gdwpf" = none := by decide

/- BIP-350: address valid (8 occurrences). -/

theorem bip350_address_valid_01 :
    decode .bech32 "BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4" =
      some ("bc", [0, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22]) ∧
    verifyChecksum .bech32 "bc".toList [0, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 12, 7, 9, 17, 11, 21] = true ∧
    encode .bech32 "bc" [0, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22] = "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4" ∧
    decode .bech32m "BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4" = none := by decide

theorem bip350_address_valid_02 :
    decode .bech32 "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7" =
      some ("tb", [0, 3, 1, 17, 17, 8, 15, 0, 20, 24, 20, 11, 6, 16, 1, 5, 29, 3, 4, 16, 3, 6, 21, 22, 26, 2, 13, 22, 9, 16, 21, 19, 24, 25, 21, 6, 18, 15, 8, 13, 24, 24, 24, 25, 9, 12, 1, 4, 16, 6, 9, 17, 0]) ∧
    verifyChecksum .bech32 "tb".toList [0, 3, 1, 17, 17, 8, 15, 0, 20, 24, 20, 11, 6, 16, 1, 5, 29, 3, 4, 16, 3, 6, 21, 22, 26, 2, 13, 22, 9, 16, 21, 19, 24, 25, 21, 6, 18, 15, 8, 13, 24, 24, 24, 25, 9, 12, 1, 4, 16, 6, 9, 17, 0, 15, 16, 31, 20, 22, 30] = true ∧
    encode .bech32 "tb" [0, 3, 1, 17, 17, 8, 15, 0, 20, 24, 20, 11, 6, 16, 1, 5, 29, 3, 4, 16, 3, 6, 21, 22, 26, 2, 13, 22, 9, 16, 21, 19, 24, 25, 21, 6, 18, 15, 8, 13, 24, 24, 24, 25, 9, 12, 1, 4, 16, 6, 9, 17, 0] = "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7" ∧
    decode .bech32m "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7" = none := by decide

theorem bip350_address_valid_03 :
    decode .bech32m "bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kt5nd6y" =
      some ("bc", [1, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22]) ∧
    verifyChecksum .bech32m "bc".toList [1, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 11, 20, 19, 13, 26, 4] = true ∧
    encode .bech32m "bc" [1, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22] = "bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kt5nd6y" ∧
    decode .bech32 "bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kt5nd6y" = none := by decide

theorem bip350_address_valid_04 :
    decode .bech32m "BC1SW50QGDZ25J" =
      some ("bc", [16, 14, 20, 15, 0]) ∧
    verifyChecksum .bech32m "bc".toList [16, 14, 20, 15, 0, 8, 13, 2, 10, 20, 18] = true ∧
    encode .bech32m "bc" [16, 14, 20, 15, 0] = "bc1sw50qgdz25j" ∧
    decode .bech32 "BC1SW50QGDZ25J" = none := by decide

theorem bip350_address_valid_05 :
    decode .bech32m "bc1zw508d6qejxtdg4y5r3zarvaryvaxxpcs" =
      some ("bc", [2, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 12]) ∧
    verifyChecksum .bech32m "bc".toList [2, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 12, 29, 6, 6, 1, 24, 16] = true ∧
    encode .bech32m "bc" [2, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 12] = "bc1zw508d6qejxtdg4y5r3zarvaryvaxxpcs" ∧
    decode .bech32 "bc1zw508d6qejxtdg4y5r3zarvaryvaxxpcs" = none := by decide

theorem bip350_address_valid_06 :
    decode .bech32 "tb1qqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesrxh6hy" =
      some ("tb", [0, 0, 0, 0, 0, 1, 17, 5, 5, 25, 11, 10, 6, 4, 8, 13, 18, 20, 6, 3, 25, 0, 23, 18, 18, 12, 24, 27, 2, 23, 6, 14, 21, 29, 4, 14, 6, 25, 24, 18, 13, 2, 25, 14, 26, 23, 4, 31, 8, 12, 16, 25, 16]) ∧
    verifyChecksum .bech32 "tb".toList [0, 0, 0, 0, 0, 1, 17, 5, 5, 25, 11, 10, 6, 4, 8, 13, 18, 20, 6, 3, 25, 0, 23, 18, 18, 12, 24, 27, 2, 23, 6, 14, 21, 29, 4, 14, 6, 25, 24, 18, 13, 2, 25, 14, 26, 23, 4, 31, 8, 12, 16, 25, 16, 3, 6, 23, 26, 23, 4] = true ∧
    encode .bech32 "tb" [0, 0, 0, 0, 0, 1, 17, 5, 5, 25, 11, 10, 6, 4, 8, 13, 18, 20, 6, 3, 25, 0, 23, 18, 18, 12, 24, 27, 2, 23, 6, 14, 21, 29, 4, 14, 6, 25, 24, 18, 13, 2, 25, 14, 26, 23, 4, 31, 8, 12, 16, 25, 16] = "tb1qqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesrxh6hy" ∧
    decode .bech32m "tb1qqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesrxh6hy" = none := by decide

theorem bip350_address_valid_07 :
    decode .bech32m "tb1pqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesf3hn0c" =
      some ("tb", [1, 0, 0, 0, 0, 1, 17, 5, 5, 25, 11, 10, 6, 4, 8, 13, 18, 20, 6, 3, 25, 0, 23, 18, 18, 12, 24, 27, 2, 23, 6, 14, 21, 29, 4, 14, 6, 25, 24, 18, 13, 2, 25, 14, 26, 23, 4, 31, 8, 12, 16, 25, 16]) ∧
    verifyChecksum .bech32m "tb".toList [1, 0, 0, 0, 0, 1, 17, 5, 5, 25, 11, 10, 6, 4, 8, 13, 18, 20, 6, 3, 25, 0, 23, 18, 18, 12, 24, 27, 2, 23, 6, 14, 21, 29, 4, 14, 6, 25, 24, 18, 13, 2, 25, 14, 26, 23, 4, 31, 8, 12, 16, 25, 16, 9, 17, 23, 19, 15, 24] = true ∧
    encode .bech32m "tb" [1, 0, 0, 0, 0, 1, 17, 5, 5, 25, 11, 10, 6, 4, 8, 13, 18, 20, 6, 3, 25, 0, 23, 18, 18, 12, 24, 27, 2, 23, 6, 14, 21, 29, 4, 14, 6, 25, 24, 18, 13, 2, 25, 14, 26, 23, 4, 31, 8, 12, 16, 25, 16] = "tb1pqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesf3hn0c" ∧
    decode .bech32 "tb1pqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesf3hn0c" = none := by decide

theorem bip350_address_valid_08 :
    decode .bech32m "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0" =
      some ("bc", [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0]) ∧
    verifyChecksum .bech32m "bc".toList [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0, 2, 22, 20, 18, 18, 15] = true ∧
    encode .bech32m "bc" [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0] = "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0" ∧
    decode .bech32 "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0" = none := by decide

/- BIP-350: address invalid (15 occurrences). -/

theorem bip350_address_invalid_01 :
    decode .bech32m "tc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq5zuyut" =
      some ("tc", [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0]) ∧
    verifyChecksum .bech32m "tc".toList [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0, 20, 2, 28, 4, 28, 11] = true ∧
    encode .bech32m "tc" [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0] = "tc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq5zuyut" ∧
    decode .bech32 "tc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq5zuyut" = none := by decide

theorem bip350_address_invalid_02 :
    decode .bech32 "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqh2y7hd" =
      some ("bc", [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0]) ∧
    verifyChecksum .bech32 "bc".toList [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0, 23, 10, 4, 30, 23, 13] = true ∧
    encode .bech32 "bc" [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0] = "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqh2y7hd" ∧
    decode .bech32m "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqh2y7hd" = none := by decide

theorem bip350_address_invalid_03 :
    decode .bech32 "tb1z0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqglt7rf" =
      some ("tb", [2, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0]) ∧
    verifyChecksum .bech32 "tb".toList [2, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0, 8, 31, 11, 30, 3, 9] = true ∧
    encode .bech32 "tb" [2, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0] = "tb1z0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqglt7rf" ∧
    decode .bech32m "tb1z0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqglt7rf" = none := by decide

theorem bip350_address_invalid_04 :
    decode .bech32 "BC1S0XLXVLHEMJA6C4DQV22UAPCTQUPFHLXM9H8Z3K2E72Q4K9HCZ7VQ54WELL" =
      some ("bc", [16, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0]) ∧
    verifyChecksum .bech32 "bc".toList [16, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0, 20, 21, 14, 25, 31, 31] = true ∧
    encode .bech32 "bc" [16, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0] = "bc1s0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq54well" ∧
    decode .bech32m "BC1S0XLXVLHEMJA6C4DQV22UAPCTQUPFHLXM9H8Z3K2E72Q4K9HCZ7VQ54WELL" = none := by decide

theorem bip350_address_invalid_05 :
    decode .bech32m "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kemeawh" =
      some ("bc", [0, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22]) ∧
    verifyChecksum .bech32m "bc".toList [0, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22, 25, 27, 25, 29, 14, 23] = true ∧
    encode .bech32m "bc" [0, 14, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 15, 24, 20, 6, 14, 30, 22] = "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kemeawh" ∧
    decode .bech32 "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kemeawh" = none := by decide

theorem bip350_address_invalid_06 :
    decode .bech32m "tb1q0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq24jc47" =
      some ("tb", [0, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0]) ∧
    verifyChecksum .bech32m "tb".toList [0, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0, 10, 21, 18, 24, 21, 30] = true ∧
    encode .bech32m "tb" [0, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0] = "tb1q0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq24jc47" ∧
    decode .bech32 "tb1q0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq24jc47" = none := by decide

theorem bip350_address_invalid_07 :
    decode .bech32 "bc1p38j9r5y49hruaue7wxjce0updqjuyyx0kh56v8s25huc6995vvpql3jow4" = none ∧
    decode .bech32m "bc1p38j9r5y49hruaue7wxjce0updqjuyyx0kh56v8s25huc6995vvpql3jow4" = none := by decide

theorem bip350_address_invalid_08 :
    decode .bech32m "BC130XLXVLHEMJA6C4DQV22UAPCTQUPFHLXM9H8Z3K2E72Q4K9HCZ7VQ7ZWS8R" =
      some ("bc", [17, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0]) ∧
    verifyChecksum .bech32m "bc".toList [17, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0, 30, 2, 14, 16, 7, 3] = true ∧
    encode .bech32m "bc" [17, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 0] = "bc130xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq7zws8r" ∧
    decode .bech32 "BC130XLXVLHEMJA6C4DQV22UAPCTQUPFHLXM9H8Z3K2E72Q4K9HCZ7VQ7ZWS8R" = none := by decide

theorem bip350_address_invalid_09 :
    decode .bech32m "bc1pw5dgrnzv" =
      some ("bc", [1, 14, 20]) ∧
    verifyChecksum .bech32m "bc".toList [1, 14, 20, 13, 8, 3, 19, 2, 12] = true ∧
    encode .bech32m "bc" [1, 14, 20] = "bc1pw5dgrnzv" ∧
    decode .bech32 "bc1pw5dgrnzv" = none := by decide

theorem bip350_address_invalid_10 :
    decode .bech32m "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v8n0nx0muaewav253zgeav" =
      some ("bc", [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 7, 19, 15, 19, 6, 15, 27, 28, 29, 25, 14, 29, 12, 10, 20]) ∧
    verifyChecksum .bech32m "bc".toList [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 7, 19, 15, 19, 6, 15, 27, 28, 29, 25, 14, 29, 12, 10, 20, 17, 2, 8, 25, 29, 12] = true ∧
    encode .bech32m "bc" [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 7, 19, 15, 19, 6, 15, 27, 28, 29, 25, 14, 29, 12, 10, 20] = "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v8n0nx0muaewav253zgeav" ∧
    decode .bech32 "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v8n0nx0muaewav253zgeav" = none := by decide

theorem bip350_address_invalid_11 :
    decode .bech32 "BC1QR508D6QEJXTDG4Y5R3ZARVARYV98GJ9P" =
      some ("bc", [0, 3, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 12]) ∧
    verifyChecksum .bech32 "bc".toList [0, 3, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 12, 5, 7, 8, 18, 5, 1] = true ∧
    encode .bech32 "bc" [0, 3, 20, 15, 7, 13, 26, 0, 25, 18, 6, 11, 13, 8, 21, 4, 20, 3, 17, 2, 29, 3, 12, 29, 3, 4, 12] = "bc1qr508d6qejxtdg4y5r3zarvaryv98gj9p" ∧
    decode .bech32m "BC1QR508D6QEJXTDG4Y5R3ZARVARYV98GJ9P" = none := by decide

theorem bip350_address_invalid_12 :
    decode .bech32 "tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq47Zagq" = none ∧
    decode .bech32m "tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq47Zagq" = none := by decide

theorem bip350_address_invalid_13 :
    decode .bech32m "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v07qwwzcrf" =
      some ("bc", [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 15, 30, 0]) ∧
    verifyChecksum .bech32m "bc".toList [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 15, 30, 0, 14, 14, 2, 24, 3, 9] = true ∧
    encode .bech32m "bc" [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 15, 30, 0] = "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v07qwwzcrf" ∧
    decode .bech32 "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v07qwwzcrf" = none := by decide

theorem bip350_address_invalid_14 :
    decode .bech32m "tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vpggkg4j" =
      some ("tb", [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 1]) ∧
    verifyChecksum .bech32m "tb".toList [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 1, 8, 8, 22, 8, 21, 18] = true ∧
    encode .bech32m "tb" [1, 15, 6, 31, 6, 12, 31, 23, 25, 27, 18, 29, 26, 24, 21, 13, 0, 12, 10, 10, 28, 29, 1, 24, 11, 0, 28, 1, 9, 23, 31, 6, 27, 5, 23, 7, 2, 17, 22, 10, 25, 30, 10, 0, 21, 22, 5, 23, 24, 2, 30, 12, 1] = "tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vpggkg4j" ∧
    decode .bech32 "tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vpggkg4j" = none := by decide

theorem bip350_address_invalid_15 :
    decode .bech32 "bc1gmk9yu" =
      some ("bc", []) ∧
    verifyChecksum .bech32 "bc".toList [8, 27, 22, 5, 4, 28] = true ∧
    encode .bech32 "bc" [] = "bc1gmk9yu" ∧
    decode .bech32m "bc1gmk9yu" = none := by decide

end Bech32.Vectors
