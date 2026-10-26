import Bech32.Codec

/-! Additional boundary regressions, separate from the 79 BIP vector occurrences. -/

namespace Bech32.EdgeCases

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem empty_input :
    decode .bech32 "" = none ∧ decode .bech32m "" = none := by decide

theorem empty_hrp :
    decode .bech32 (encode .bech32 "" []) = none ∧
    decode .bech32m (encode .bech32m "" []) = none := by decide

theorem missing_separator :
    decode .bech32 "qqqqqqq" = none ∧
    decode .bech32m "qqqqqqq" = none := by decide

theorem last_separator :
    decode .bech32 "a1b11j8es2a" = some ("a1b1", []) := by decide

theorem mixed_case_hrp :
    decode .bech32 "A12uel5l" = none ∧
    decode .bech32m "A1lqfn3a" = none := by decide

theorem mixed_case_data :
    decode .bech32 "a12UEL5L" = none ∧
    decode .bech32m "a1LQFN3A" = none := by decide

theorem ascii_endpoints :
    decode .bech32 "!1wctc0x" = some ("!", []) ∧
    decode .bech32 "~1qszm75" = some ("~", []) := by decide

theorem outside_ascii :
    decode .bech32 " 1nwldj5" = none ∧
    decode .bech32 "\x7f1axkwrx" = none ∧
    decode .bech32 "\x801eym55h" = none := by decide

theorem unicode_rejected :
    decode .bech32 "é1uqsa4e" = none ∧
    decode .bech32 "🙂1tkmamq" = none := by decide

theorem maximum_length :
    (encode .bech32 "a" (List.replicate 82 0)).length = 90 ∧
    decode .bech32 (encode .bech32 "a" (List.replicate 82 0)) =
      some ("a", List.replicate 82 0) := by decide

theorem overlong_rejected :
    (encode .bech32 "a" (List.replicate 83 0)).length = 91 ∧
    decode .bech32 (encode .bech32 "a" (List.replicate 83 0)) = none ∧
    decode .bech32m (encode .bech32m "a" (List.replicate 83 0)) = none := by decide

theorem empty_payload :
    decode .bech32 "a12uel5l" = some ("a", []) ∧
    decode .bech32m "a1lqfn3a" = some ("a", []) := by decide

theorem full_alphabet :
    decode .bech32 "abcdef1qpzry9x8gf2tvdw0s3jn54khce6mua7lmqqqxw" =
      some ("abcdef", [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]) ∧
    decode .bech32m "abcdef1qpzry9x8gf2tvdw0s3jn54khce6mua7lmqqqxw" = none := by decide

theorem uppercase_hrp_canonicalized :
    encode .bech32 "A" [] = "a12uel5l" ∧
    encode .bech32m "A" [] = "a1lqfn3a" := by decide

end Bech32.EdgeCases
