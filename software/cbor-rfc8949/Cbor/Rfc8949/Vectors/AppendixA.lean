/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Ordering

/-!
# RFC 8949 Appendix A: all 58 float-free diagnostic/hex test vectors

RFC 8949 Appendix A contains 81 example rows (`1..81` in table order).
Per ticket #34 as amended (comment 6460668308), exactly **58** rows belong to
the Milestone 1 float-free fragment and **23** belong to Milestone 2 (IEEE 754
floating-point):

* **58 float-free rows (verified here in both directions):**
  - Rows `1..18`: unsigned integers, negative integers, and tag-2/3 bignums;
  - Rows `41..48`: simple values (`false`, `true`, `null`, `undefined`,
    `simple(16)`, `simple(255)`) and tags `0` and `1(1363896240)`;
  - Rows `50..81`: tags `23`, `24`, `32`, definite byte and text strings
    (including UTF-8 2/3/4-byte scalars), definite arrays and maps, and
    indefinite-length strings, arrays, and maps (`71..81`).
* **23 float-containing rows (deferred to Milestone 2):**
  - Rows `19..40` (22 bare half/single/double float rows, `0xf9`/`0xfa`/`0xfb`);
  - Row `49`: `1(1363896240.5)` (`c1 fb 41 d4 52 d9 ec 20 00 00`), a tag-1
    epoch timestamp wrapping a `binary64` float.

Every float-free row is checked in-kernel in both directions:
`parseWellFormed v.wire = some v.item` and `encodePreferred v.item = v.wire`.
In addition, all 47 definite rows are checked under `decodeDeterministic` and
`encodeDeterministic`, all 11 indefinite rows (`71..81`) are checked to be
rejected by `decodeDeterministic` and deflated by `deflateIndefinite` to
`v.item.toDefinite`, and all 18 integer/bignum rows (`1..18`) are checked
against `Item.intValue?` and `encodeInt`.
-/

namespace Cbor.Rfc8949.Vectors

/-- One float-free test vector from RFC 8949 Appendix A. -/
structure AppendixAVector where
  /-- 1-based row number in RFC 8949 Appendix A (`1..81`). -/
  row : Nat
  /-- Diagnostic notation from RFC 8949 Appendix A. -/
  diagnostic : String
  /-- Exact wire bytes from RFC 8949 Appendix A. -/
  wire : List UInt8
  /-- Expected Milestone-1 `Item` AST. -/
  item : Item
  /-- Whether the wire encoding uses definite lengths throughout. -/
  definite : Bool
  deriving Repr

/-- Appendix A row 1: `0` (`00`). -/
def appendixARow01 : AppendixAVector where
  row := 1
  diagnostic := "0"
  wire := [0x00]
  item := (.uint 0)
  definite := true

/-- Appendix A row 2: `1` (`01`). -/
def appendixARow02 : AppendixAVector where
  row := 2
  diagnostic := "1"
  wire := [0x01]
  item := (.uint 1)
  definite := true

/-- Appendix A row 3: `10` (`0a`). -/
def appendixARow03 : AppendixAVector where
  row := 3
  diagnostic := "10"
  wire := [0x0a]
  item := (.uint 10)
  definite := true

/-- Appendix A row 4: `23` (`17`). -/
def appendixARow04 : AppendixAVector where
  row := 4
  diagnostic := "23"
  wire := [0x17]
  item := (.uint 23)
  definite := true

/-- Appendix A row 5: `24` (`1818`). -/
def appendixARow05 : AppendixAVector where
  row := 5
  diagnostic := "24"
  wire := [0x18, 0x18]
  item := (.uint 24)
  definite := true

/-- Appendix A row 6: `25` (`1819`). -/
def appendixARow06 : AppendixAVector where
  row := 6
  diagnostic := "25"
  wire := [0x18, 0x19]
  item := (.uint 25)
  definite := true

/-- Appendix A row 7: `100` (`1864`). -/
def appendixARow07 : AppendixAVector where
  row := 7
  diagnostic := "100"
  wire := [0x18, 0x64]
  item := (.uint 100)
  definite := true

/-- Appendix A row 8: `1000` (`1903e8`). -/
def appendixARow08 : AppendixAVector where
  row := 8
  diagnostic := "1000"
  wire := [0x19, 0x03, 0xe8]
  item := (.uint 1000)
  definite := true

/-- Appendix A row 9: `1000000` (`1a000f4240`). -/
def appendixARow09 : AppendixAVector where
  row := 9
  diagnostic := "1000000"
  wire := [0x1a, 0x00, 0x0f, 0x42, 0x40]
  item := (.uint 1000000)
  definite := true

/-- Appendix A row 10: `1000000000000` (`1b000000e8d4a51000`). -/
def appendixARow10 : AppendixAVector where
  row := 10
  diagnostic := "1000000000000"
  wire := [0x1b, 0x00, 0x00, 0x00, 0xe8, 0xd4, 0xa5, 0x10, 0x00]
  item := (.uint 1000000000000)
  definite := true

/-- Appendix A row 11: `18446744073709551615` (`1bffffffffffffffff`). -/
def appendixARow11 : AppendixAVector where
  row := 11
  diagnostic := "18446744073709551615"
  wire := [0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
  item := (.uint 18446744073709551615)
  definite := true

/-- Appendix A row 12: `18446744073709551616` (`c249010000000000000000`). -/
def appendixARow12 : AppendixAVector where
  row := 12
  diagnostic := "18446744073709551616"
  wire := [0xc2, 0x49, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  item := (.tag 2 (.bytes [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]))
  definite := true

/-- Appendix A row 13: `-18446744073709551616` (`3bffffffffffffffff`). -/
def appendixARow13 : AppendixAVector where
  row := 13
  diagnostic := "-18446744073709551616"
  wire := [0x3b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
  item := (.nint 18446744073709551615)
  definite := true

/-- Appendix A row 14: `-18446744073709551617` (`c349010000000000000000`). -/
def appendixARow14 : AppendixAVector where
  row := 14
  diagnostic := "-18446744073709551617"
  wire := [0xc3, 0x49, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  item := (.tag 3 (.bytes [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]))
  definite := true

/-- Appendix A row 15: `-1` (`20`). -/
def appendixARow15 : AppendixAVector where
  row := 15
  diagnostic := "-1"
  wire := [0x20]
  item := (.nint 0)
  definite := true

/-- Appendix A row 16: `-10` (`29`). -/
def appendixARow16 : AppendixAVector where
  row := 16
  diagnostic := "-10"
  wire := [0x29]
  item := (.nint 9)
  definite := true

/-- Appendix A row 17: `-100` (`3863`). -/
def appendixARow17 : AppendixAVector where
  row := 17
  diagnostic := "-100"
  wire := [0x38, 0x63]
  item := (.nint 99)
  definite := true

/-- Appendix A row 18: `-1000` (`3903e7`). -/
def appendixARow18 : AppendixAVector where
  row := 18
  diagnostic := "-1000"
  wire := [0x39, 0x03, 0xe7]
  item := (.nint 999)
  definite := true

/-- Appendix A row 41: `false` (`f4`). -/
def appendixARow41 : AppendixAVector where
  row := 41
  diagnostic := "false"
  wire := [0xf4]
  item := Item.false_
  definite := true

/-- Appendix A row 42: `true` (`f5`). -/
def appendixARow42 : AppendixAVector where
  row := 42
  diagnostic := "true"
  wire := [0xf5]
  item := Item.true_
  definite := true

/-- Appendix A row 43: `null` (`f6`). -/
def appendixARow43 : AppendixAVector where
  row := 43
  diagnostic := "null"
  wire := [0xf6]
  item := Item.null
  definite := true

/-- Appendix A row 44: `undefined` (`f7`). -/
def appendixARow44 : AppendixAVector where
  row := 44
  diagnostic := "undefined"
  wire := [0xf7]
  item := Item.undefined
  definite := true

/-- Appendix A row 45: `simple(16)` (`f0`). -/
def appendixARow45 : AppendixAVector where
  row := 45
  diagnostic := "simple(16)"
  wire := [0xf0]
  item := (.simple 16)
  definite := true

/-- Appendix A row 46: `simple(255)` (`f8ff`). -/
def appendixARow46 : AppendixAVector where
  row := 46
  diagnostic := "simple(255)"
  wire := [0xf8, 0xff]
  item := (.simple 255)
  definite := true

/-- Appendix A row 47: `0("2013-03-21T20:04:00Z")` (`c074323031332d30332d32315432303a30343a30305a`). -/
def appendixARow47 : AppendixAVector where
  row := 47
  diagnostic := "0(\"2013-03-21T20:04:00Z\")"
  wire := [0xc0, 0x74, 0x32, 0x30, 0x31, 0x33, 0x2d, 0x30, 0x33, 0x2d, 0x32, 0x31, 0x54, 0x32, 0x30, 0x3a, 0x30, 0x34, 0x3a, 0x30, 0x30, 0x5a]
  item := (.tag 0 (.text [0x32, 0x30, 0x31, 0x33, 0x2d, 0x30, 0x33, 0x2d, 0x32, 0x31, 0x54, 0x32, 0x30, 0x3a, 0x30, 0x34, 0x3a, 0x30, 0x30, 0x5a]))
  definite := true

/-- Appendix A row 48: `1(1363896240)` (`c11a514b67b0`). -/
def appendixARow48 : AppendixAVector where
  row := 48
  diagnostic := "1(1363896240)"
  wire := [0xc1, 0x1a, 0x51, 0x4b, 0x67, 0xb0]
  item := (.tag 1 (.uint 1363896240))
  definite := true

/-- Appendix A row 50: `23(h'01020304')` (`d74401020304`). -/
def appendixARow50 : AppendixAVector where
  row := 50
  diagnostic := "23(h'01020304')"
  wire := [0xd7, 0x44, 0x01, 0x02, 0x03, 0x04]
  item := (.tag 23 (.bytes [0x01, 0x02, 0x03, 0x04]))
  definite := true

/-- Appendix A row 51: `24(h'6449455446')` (`d818456449455446`). -/
def appendixARow51 : AppendixAVector where
  row := 51
  diagnostic := "24(h'6449455446')"
  wire := [0xd8, 0x18, 0x45, 0x64, 0x49, 0x45, 0x54, 0x46]
  item := (.tag 24 (.bytes [0x64, 0x49, 0x45, 0x54, 0x46]))
  definite := true

/-- Appendix A row 52: `32("http://www.example.com")` (`d82076687474703a2f2f7777772e6578616d706c652e636f6d`). -/
def appendixARow52 : AppendixAVector where
  row := 52
  diagnostic := "32(\"http://www.example.com\")"
  wire := [0xd8, 0x20, 0x76, 0x68, 0x74, 0x74, 0x70, 0x3a, 0x2f, 0x2f, 0x77, 0x77, 0x77, 0x2e, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x63, 0x6f, 0x6d]
  item := (.tag 32 (.text [0x68, 0x74, 0x74, 0x70, 0x3a, 0x2f, 0x2f, 0x77, 0x77, 0x77, 0x2e, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x63, 0x6f, 0x6d]))
  definite := true

/-- Appendix A row 53: `h''` (`40`). -/
def appendixARow53 : AppendixAVector where
  row := 53
  diagnostic := "h''"
  wire := [0x40]
  item := (.bytes [])
  definite := true

/-- Appendix A row 54: `h'01020304'` (`4401020304`). -/
def appendixARow54 : AppendixAVector where
  row := 54
  diagnostic := "h'01020304'"
  wire := [0x44, 0x01, 0x02, 0x03, 0x04]
  item := (.bytes [0x01, 0x02, 0x03, 0x04])
  definite := true

/-- Appendix A row 55: `""` (`60`). -/
def appendixARow55 : AppendixAVector where
  row := 55
  diagnostic := "\"\""
  wire := [0x60]
  item := (.text [])
  definite := true

/-- Appendix A row 56: `"a"` (`6161`). -/
def appendixARow56 : AppendixAVector where
  row := 56
  diagnostic := "\"a\""
  wire := [0x61, 0x61]
  item := (.text [0x61])
  definite := true

/-- Appendix A row 57: `"IETF"` (`6449455446`). -/
def appendixARow57 : AppendixAVector where
  row := 57
  diagnostic := "\"IETF\""
  wire := [0x64, 0x49, 0x45, 0x54, 0x46]
  item := (.text [0x49, 0x45, 0x54, 0x46])
  definite := true

/-- Appendix A row 58: `"\"\\"` (`62225c`). -/
def appendixARow58 : AppendixAVector where
  row := 58
  diagnostic := "\"\\\"\\\\\""
  wire := [0x62, 0x22, 0x5c]
  item := (.text [0x22, 0x5c])
  definite := true

/-- Appendix A row 59: `"\u00fc"` (`62c3bc`). -/
def appendixARow59 : AppendixAVector where
  row := 59
  diagnostic := "\"\\u00fc\""
  wire := [0x62, 0xc3, 0xbc]
  item := (.text [0xc3, 0xbc])
  definite := true

/-- Appendix A row 60: `"\u6c34"` (`63e6b0b4`). -/
def appendixARow60 : AppendixAVector where
  row := 60
  diagnostic := "\"\\u6c34\""
  wire := [0x63, 0xe6, 0xb0, 0xb4]
  item := (.text [0xe6, 0xb0, 0xb4])
  definite := true

/-- Appendix A row 61: `"\ud800\udd51"` (`64f0908591`). -/
def appendixARow61 : AppendixAVector where
  row := 61
  diagnostic := "\"\\ud800\\udd51\""
  wire := [0x64, 0xf0, 0x90, 0x85, 0x91]
  item := (.text [0xf0, 0x90, 0x85, 0x91])
  definite := true

/-- Appendix A row 62: `[]` (`80`). -/
def appendixARow62 : AppendixAVector where
  row := 62
  diagnostic := "[]"
  wire := [0x80]
  item := (.array [])
  definite := true

/-- Appendix A row 63: `[1, 2, 3]` (`83010203`). -/
def appendixARow63 : AppendixAVector where
  row := 63
  diagnostic := "[1, 2, 3]"
  wire := [0x83, 0x01, 0x02, 0x03]
  item := (.array [(.uint 1), (.uint 2), (.uint 3)])
  definite := true

/-- Appendix A row 64: `[1, [2, 3], [4, 5]]` (`8301820203820405`). -/
def appendixARow64 : AppendixAVector where
  row := 64
  diagnostic := "[1, [2, 3], [4, 5]]"
  wire := [0x83, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05]
  item := (.array [(.uint 1), (.array [(.uint 2), (.uint 3)]), (.array [(.uint 4), (.uint 5)])])
  definite := true

/-- Appendix A row 65: `[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]` (`98190102030405060708090a0b0c0d0e0f101112131415161718181819`). -/
def appendixARow65 : AppendixAVector where
  row := 65
  diagnostic := "[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]"
  wire := [0x98, 0x19, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x18, 0x18, 0x19]
  item := (.array [(.uint 1), (.uint 2), (.uint 3), (.uint 4), (.uint 5), (.uint 6), (.uint 7), (.uint 8), (.uint 9), (.uint 10), (.uint 11), (.uint 12), (.uint 13), (.uint 14), (.uint 15), (.uint 16), (.uint 17), (.uint 18), (.uint 19), (.uint 20), (.uint 21), (.uint 22), (.uint 23), (.uint 24), (.uint 25)])
  definite := true

/-- Appendix A row 66: `{}` (`a0`). -/
def appendixARow66 : AppendixAVector where
  row := 66
  diagnostic := "{}"
  wire := [0xa0]
  item := (.map [])
  definite := true

/-- Appendix A row 67: `{1: 2, 3: 4}` (`a201020304`). -/
def appendixARow67 : AppendixAVector where
  row := 67
  diagnostic := "{1: 2, 3: 4}"
  wire := [0xa2, 0x01, 0x02, 0x03, 0x04]
  item := (.map [((.uint 1), (.uint 2)), ((.uint 3), (.uint 4))])
  definite := true

/-- Appendix A row 68: `{"a": 1, "b": [2, 3]}` (`a26161016162820203`). -/
def appendixARow68 : AppendixAVector where
  row := 68
  diagnostic := "{\"a\": 1, \"b\": [2, 3]}"
  wire := [0xa2, 0x61, 0x61, 0x01, 0x61, 0x62, 0x82, 0x02, 0x03]
  item := (.map [((.text [0x61]), (.uint 1)), ((.text [0x62]), (.array [(.uint 2), (.uint 3)]))])
  definite := true

/-- Appendix A row 69: `["a", {"b": "c"}]` (`826161a161626163`). -/
def appendixARow69 : AppendixAVector where
  row := 69
  diagnostic := "[\"a\", {\"b\": \"c\"}]"
  wire := [0x82, 0x61, 0x61, 0xa1, 0x61, 0x62, 0x61, 0x63]
  item := (.array [(.text [0x61]), (.map [((.text [0x62]), (.text [0x63]))])])
  definite := true

/-- Appendix A row 70: `{"a": "A", "b": "B", "c": "C", "d": "D", "e": "E"}` (`a56161614161626142616361436164614461656145`). -/
def appendixARow70 : AppendixAVector where
  row := 70
  diagnostic := "{\"a\": \"A\", \"b\": \"B\", \"c\": \"C\", \"d\": \"D\", \"e\": \"E\"}"
  wire := [0xa5, 0x61, 0x61, 0x61, 0x41, 0x61, 0x62, 0x61, 0x42, 0x61, 0x63, 0x61, 0x43, 0x61, 0x64, 0x61, 0x44, 0x61, 0x65, 0x61, 0x45]
  item := (.map [((.text [0x61]), (.text [0x41])), ((.text [0x62]), (.text [0x42])), ((.text [0x63]), (.text [0x43])), ((.text [0x64]), (.text [0x44])), ((.text [0x65]), (.text [0x45]))])
  definite := true

/-- Appendix A row 71: `(_ h'0102', h'030405')` (`5f42010243030405ff`). -/
def appendixARow71 : AppendixAVector where
  row := 71
  diagnostic := "(_ h'0102', h'030405')"
  wire := [0x5f, 0x42, 0x01, 0x02, 0x43, 0x03, 0x04, 0x05, 0xff]
  item := (.bytesIndef [[0x01, 0x02], [0x03, 0x04, 0x05]])
  definite := false

/-- Appendix A row 72: `(_ "strea", "ming")` (`7f657374726561646d696e67ff`). -/
def appendixARow72 : AppendixAVector where
  row := 72
  diagnostic := "(_ \"strea\", \"ming\")"
  wire := [0x7f, 0x65, 0x73, 0x74, 0x72, 0x65, 0x61, 0x64, 0x6d, 0x69, 0x6e, 0x67, 0xff]
  item := (.textIndef [[0x73, 0x74, 0x72, 0x65, 0x61], [0x6d, 0x69, 0x6e, 0x67]])
  definite := false

/-- Appendix A row 73: `[_ ]` (`9fff`). -/
def appendixARow73 : AppendixAVector where
  row := 73
  diagnostic := "[_ ]"
  wire := [0x9f, 0xff]
  item := (.arrayIndef [])
  definite := false

/-- Appendix A row 74: `[_ 1, [2, 3], [_ 4, 5]]` (`9f018202039f0405ffff`). -/
def appendixARow74 : AppendixAVector where
  row := 74
  diagnostic := "[_ 1, [2, 3], [_ 4, 5]]"
  wire := [0x9f, 0x01, 0x82, 0x02, 0x03, 0x9f, 0x04, 0x05, 0xff, 0xff]
  item := (.arrayIndef [(.uint 1), (.array [(.uint 2), (.uint 3)]), (.arrayIndef [(.uint 4), (.uint 5)])])
  definite := false

/-- Appendix A row 75: `[_ 1, [2, 3], [4, 5]]` (`9f01820203820405ff`). -/
def appendixARow75 : AppendixAVector where
  row := 75
  diagnostic := "[_ 1, [2, 3], [4, 5]]"
  wire := [0x9f, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05, 0xff]
  item := (.arrayIndef [(.uint 1), (.array [(.uint 2), (.uint 3)]), (.array [(.uint 4), (.uint 5)])])
  definite := false

/-- Appendix A row 76: `[1, [2, 3], [_ 4, 5]]` (`83018202039f0405ff`). -/
def appendixARow76 : AppendixAVector where
  row := 76
  diagnostic := "[1, [2, 3], [_ 4, 5]]"
  wire := [0x83, 0x01, 0x82, 0x02, 0x03, 0x9f, 0x04, 0x05, 0xff]
  item := (.array [(.uint 1), (.array [(.uint 2), (.uint 3)]), (.arrayIndef [(.uint 4), (.uint 5)])])
  definite := false

/-- Appendix A row 77: `[1, [_ 2, 3], [4, 5]]` (`83019f0203ff820405`). -/
def appendixARow77 : AppendixAVector where
  row := 77
  diagnostic := "[1, [_ 2, 3], [4, 5]]"
  wire := [0x83, 0x01, 0x9f, 0x02, 0x03, 0xff, 0x82, 0x04, 0x05]
  item := (.array [(.uint 1), (.arrayIndef [(.uint 2), (.uint 3)]), (.array [(.uint 4), (.uint 5)])])
  definite := false

/-- Appendix A row 78: `[_ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]` (`9f0102030405060708090a0b0c0d0e0f101112131415161718181819ff`). -/
def appendixARow78 : AppendixAVector where
  row := 78
  diagnostic := "[_ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]"
  wire := [0x9f, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x18, 0x18, 0x19, 0xff]
  item := (.arrayIndef [(.uint 1), (.uint 2), (.uint 3), (.uint 4), (.uint 5), (.uint 6), (.uint 7), (.uint 8), (.uint 9), (.uint 10), (.uint 11), (.uint 12), (.uint 13), (.uint 14), (.uint 15), (.uint 16), (.uint 17), (.uint 18), (.uint 19), (.uint 20), (.uint 21), (.uint 22), (.uint 23), (.uint 24), (.uint 25)])
  definite := false

/-- Appendix A row 79: `{_ "a": 1, "b": [_ 2, 3]}` (`bf61610161629f0203ffff`). -/
def appendixARow79 : AppendixAVector where
  row := 79
  diagnostic := "{_ \"a\": 1, \"b\": [_ 2, 3]}"
  wire := [0xbf, 0x61, 0x61, 0x01, 0x61, 0x62, 0x9f, 0x02, 0x03, 0xff, 0xff]
  item := (.mapIndef [((.text [0x61]), (.uint 1)), ((.text [0x62]), (.arrayIndef [(.uint 2), (.uint 3)]))])
  definite := false

/-- Appendix A row 80: `["a", {_ "b": "c"}]` (`826161bf61626163ff`). -/
def appendixARow80 : AppendixAVector where
  row := 80
  diagnostic := "[\"a\", {_ \"b\": \"c\"}]"
  wire := [0x82, 0x61, 0x61, 0xbf, 0x61, 0x62, 0x61, 0x63, 0xff]
  item := (.array [(.text [0x61]), (.mapIndef [((.text [0x62]), (.text [0x63]))])])
  definite := false

/-- Appendix A row 81: `{_ "Fun": true, "Amt": -2}` (`bf6346756ef563416d7421ff`). -/
def appendixARow81 : AppendixAVector where
  row := 81
  diagnostic := "{_ \"Fun\": true, \"Amt\": -2}"
  wire := [0xbf, 0x63, 0x46, 0x75, 0x6e, 0xf5, 0x63, 0x41, 0x6d, 0x74, 0x21, 0xff]
  item := (.mapIndef [((.text [0x46, 0x75, 0x6e]), Item.true_), ((.text [0x41, 0x6d, 0x74]), (.nint 1))])
  definite := false

/-- Complete table of all 58 float-free RFC 8949 Appendix A test vectors. -/
def appendixAFloatFreeVectors : List AppendixAVector := [
  appendixARow01,
  appendixARow02,
  appendixARow03,
  appendixARow04,
  appendixARow05,
  appendixARow06,
  appendixARow07,
  appendixARow08,
  appendixARow09,
  appendixARow10,
  appendixARow11,
  appendixARow12,
  appendixARow13,
  appendixARow14,
  appendixARow15,
  appendixARow16,
  appendixARow17,
  appendixARow18,
  appendixARow41,
  appendixARow42,
  appendixARow43,
  appendixARow44,
  appendixARow45,
  appendixARow46,
  appendixARow47,
  appendixARow48,
  appendixARow50,
  appendixARow51,
  appendixARow52,
  appendixARow53,
  appendixARow54,
  appendixARow55,
  appendixARow56,
  appendixARow57,
  appendixARow58,
  appendixARow59,
  appendixARow60,
  appendixARow61,
  appendixARow62,
  appendixARow63,
  appendixARow64,
  appendixARow65,
  appendixARow66,
  appendixARow67,
  appendixARow68,
  appendixARow69,
  appendixARow70,
  appendixARow71,
  appendixARow72,
  appendixARow73,
  appendixARow74,
  appendixARow75,
  appendixARow76,
  appendixARow77,
  appendixARow78,
  appendixARow79,
  appendixARow80,
  appendixARow81
]

theorem appendixAFloatFreeVectors_length : appendixAFloatFreeVectors.length = 58 := rfl

theorem appendixAFloatFreeVectors_definite_count :
    (appendixAFloatFreeVectors.filter AppendixAVector.definite).length = 47 := rfl

theorem appendixAFloatFreeVectors_indefinite_count :
    (appendixAFloatFreeVectors.filter (fun v => !v.definite)).length = 11 := rfl

theorem appendixAFloatFreeVectors_rows :
    appendixAFloatFreeVectors.map AppendixAVector.row = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 41, 42, 43, 44, 45, 46, 47, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81] := rfl

theorem appendixAFloatFreeVectors_rows_nodup :
    (appendixAFloatFreeVectors.map AppendixAVector.row).Nodup := by decide

/-- Row 49 (`1(1363896240.5)`, tag 1 wrapping binary64) is excluded from M1. -/
theorem appendixAFloatFreeVectors_excludes_row49 :
    49 ∉ appendixAFloatFreeVectors.map AppendixAVector.row := by decide

/-! ## Per-row bidirectional kernel verification (all 58 rows) -/

theorem appendixARow01_bidirectional :
    parseWellFormed appendixARow01.wire = some appendixARow01.item ∧
    encodePreferred appendixARow01.item = appendixARow01.wire ∧
    decodeDeterministic appendixARow01.wire = some appendixARow01.item ∧
    encodeDeterministic appendixARow01.item = appendixARow01.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow02_bidirectional :
    parseWellFormed appendixARow02.wire = some appendixARow02.item ∧
    encodePreferred appendixARow02.item = appendixARow02.wire ∧
    decodeDeterministic appendixARow02.wire = some appendixARow02.item ∧
    encodeDeterministic appendixARow02.item = appendixARow02.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow03_bidirectional :
    parseWellFormed appendixARow03.wire = some appendixARow03.item ∧
    encodePreferred appendixARow03.item = appendixARow03.wire ∧
    decodeDeterministic appendixARow03.wire = some appendixARow03.item ∧
    encodeDeterministic appendixARow03.item = appendixARow03.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow04_bidirectional :
    parseWellFormed appendixARow04.wire = some appendixARow04.item ∧
    encodePreferred appendixARow04.item = appendixARow04.wire ∧
    decodeDeterministic appendixARow04.wire = some appendixARow04.item ∧
    encodeDeterministic appendixARow04.item = appendixARow04.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow05_bidirectional :
    parseWellFormed appendixARow05.wire = some appendixARow05.item ∧
    encodePreferred appendixARow05.item = appendixARow05.wire ∧
    decodeDeterministic appendixARow05.wire = some appendixARow05.item ∧
    encodeDeterministic appendixARow05.item = appendixARow05.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow06_bidirectional :
    parseWellFormed appendixARow06.wire = some appendixARow06.item ∧
    encodePreferred appendixARow06.item = appendixARow06.wire ∧
    decodeDeterministic appendixARow06.wire = some appendixARow06.item ∧
    encodeDeterministic appendixARow06.item = appendixARow06.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow07_bidirectional :
    parseWellFormed appendixARow07.wire = some appendixARow07.item ∧
    encodePreferred appendixARow07.item = appendixARow07.wire ∧
    decodeDeterministic appendixARow07.wire = some appendixARow07.item ∧
    encodeDeterministic appendixARow07.item = appendixARow07.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow08_bidirectional :
    parseWellFormed appendixARow08.wire = some appendixARow08.item ∧
    encodePreferred appendixARow08.item = appendixARow08.wire ∧
    decodeDeterministic appendixARow08.wire = some appendixARow08.item ∧
    encodeDeterministic appendixARow08.item = appendixARow08.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow09_bidirectional :
    parseWellFormed appendixARow09.wire = some appendixARow09.item ∧
    encodePreferred appendixARow09.item = appendixARow09.wire ∧
    decodeDeterministic appendixARow09.wire = some appendixARow09.item ∧
    encodeDeterministic appendixARow09.item = appendixARow09.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow10_bidirectional :
    parseWellFormed appendixARow10.wire = some appendixARow10.item ∧
    encodePreferred appendixARow10.item = appendixARow10.wire ∧
    decodeDeterministic appendixARow10.wire = some appendixARow10.item ∧
    encodeDeterministic appendixARow10.item = appendixARow10.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow11_bidirectional :
    parseWellFormed appendixARow11.wire = some appendixARow11.item ∧
    encodePreferred appendixARow11.item = appendixARow11.wire ∧
    decodeDeterministic appendixARow11.wire = some appendixARow11.item ∧
    encodeDeterministic appendixARow11.item = appendixARow11.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow12_bidirectional :
    parseWellFormed appendixARow12.wire = some appendixARow12.item ∧
    encodePreferred appendixARow12.item = appendixARow12.wire ∧
    decodeDeterministic appendixARow12.wire = some appendixARow12.item ∧
    encodeDeterministic appendixARow12.item = appendixARow12.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow13_bidirectional :
    parseWellFormed appendixARow13.wire = some appendixARow13.item ∧
    encodePreferred appendixARow13.item = appendixARow13.wire ∧
    decodeDeterministic appendixARow13.wire = some appendixARow13.item ∧
    encodeDeterministic appendixARow13.item = appendixARow13.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow14_bidirectional :
    parseWellFormed appendixARow14.wire = some appendixARow14.item ∧
    encodePreferred appendixARow14.item = appendixARow14.wire ∧
    decodeDeterministic appendixARow14.wire = some appendixARow14.item ∧
    encodeDeterministic appendixARow14.item = appendixARow14.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow15_bidirectional :
    parseWellFormed appendixARow15.wire = some appendixARow15.item ∧
    encodePreferred appendixARow15.item = appendixARow15.wire ∧
    decodeDeterministic appendixARow15.wire = some appendixARow15.item ∧
    encodeDeterministic appendixARow15.item = appendixARow15.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow16_bidirectional :
    parseWellFormed appendixARow16.wire = some appendixARow16.item ∧
    encodePreferred appendixARow16.item = appendixARow16.wire ∧
    decodeDeterministic appendixARow16.wire = some appendixARow16.item ∧
    encodeDeterministic appendixARow16.item = appendixARow16.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow17_bidirectional :
    parseWellFormed appendixARow17.wire = some appendixARow17.item ∧
    encodePreferred appendixARow17.item = appendixARow17.wire ∧
    decodeDeterministic appendixARow17.wire = some appendixARow17.item ∧
    encodeDeterministic appendixARow17.item = appendixARow17.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow18_bidirectional :
    parseWellFormed appendixARow18.wire = some appendixARow18.item ∧
    encodePreferred appendixARow18.item = appendixARow18.wire ∧
    decodeDeterministic appendixARow18.wire = some appendixARow18.item ∧
    encodeDeterministic appendixARow18.item = appendixARow18.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow41_bidirectional :
    parseWellFormed appendixARow41.wire = some appendixARow41.item ∧
    encodePreferred appendixARow41.item = appendixARow41.wire ∧
    decodeDeterministic appendixARow41.wire = some appendixARow41.item ∧
    encodeDeterministic appendixARow41.item = appendixARow41.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow42_bidirectional :
    parseWellFormed appendixARow42.wire = some appendixARow42.item ∧
    encodePreferred appendixARow42.item = appendixARow42.wire ∧
    decodeDeterministic appendixARow42.wire = some appendixARow42.item ∧
    encodeDeterministic appendixARow42.item = appendixARow42.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow43_bidirectional :
    parseWellFormed appendixARow43.wire = some appendixARow43.item ∧
    encodePreferred appendixARow43.item = appendixARow43.wire ∧
    decodeDeterministic appendixARow43.wire = some appendixARow43.item ∧
    encodeDeterministic appendixARow43.item = appendixARow43.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow44_bidirectional :
    parseWellFormed appendixARow44.wire = some appendixARow44.item ∧
    encodePreferred appendixARow44.item = appendixARow44.wire ∧
    decodeDeterministic appendixARow44.wire = some appendixARow44.item ∧
    encodeDeterministic appendixARow44.item = appendixARow44.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow45_bidirectional :
    parseWellFormed appendixARow45.wire = some appendixARow45.item ∧
    encodePreferred appendixARow45.item = appendixARow45.wire ∧
    decodeDeterministic appendixARow45.wire = some appendixARow45.item ∧
    encodeDeterministic appendixARow45.item = appendixARow45.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow46_bidirectional :
    parseWellFormed appendixARow46.wire = some appendixARow46.item ∧
    encodePreferred appendixARow46.item = appendixARow46.wire ∧
    decodeDeterministic appendixARow46.wire = some appendixARow46.item ∧
    encodeDeterministic appendixARow46.item = appendixARow46.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow47_bidirectional :
    parseWellFormed appendixARow47.wire = some appendixARow47.item ∧
    encodePreferred appendixARow47.item = appendixARow47.wire ∧
    decodeDeterministic appendixARow47.wire = some appendixARow47.item ∧
    encodeDeterministic appendixARow47.item = appendixARow47.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow48_bidirectional :
    parseWellFormed appendixARow48.wire = some appendixARow48.item ∧
    encodePreferred appendixARow48.item = appendixARow48.wire ∧
    decodeDeterministic appendixARow48.wire = some appendixARow48.item ∧
    encodeDeterministic appendixARow48.item = appendixARow48.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow50_bidirectional :
    parseWellFormed appendixARow50.wire = some appendixARow50.item ∧
    encodePreferred appendixARow50.item = appendixARow50.wire ∧
    decodeDeterministic appendixARow50.wire = some appendixARow50.item ∧
    encodeDeterministic appendixARow50.item = appendixARow50.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow51_bidirectional :
    parseWellFormed appendixARow51.wire = some appendixARow51.item ∧
    encodePreferred appendixARow51.item = appendixARow51.wire ∧
    decodeDeterministic appendixARow51.wire = some appendixARow51.item ∧
    encodeDeterministic appendixARow51.item = appendixARow51.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow52_bidirectional :
    parseWellFormed appendixARow52.wire = some appendixARow52.item ∧
    encodePreferred appendixARow52.item = appendixARow52.wire ∧
    decodeDeterministic appendixARow52.wire = some appendixARow52.item ∧
    encodeDeterministic appendixARow52.item = appendixARow52.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow53_bidirectional :
    parseWellFormed appendixARow53.wire = some appendixARow53.item ∧
    encodePreferred appendixARow53.item = appendixARow53.wire ∧
    decodeDeterministic appendixARow53.wire = some appendixARow53.item ∧
    encodeDeterministic appendixARow53.item = appendixARow53.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow54_bidirectional :
    parseWellFormed appendixARow54.wire = some appendixARow54.item ∧
    encodePreferred appendixARow54.item = appendixARow54.wire ∧
    decodeDeterministic appendixARow54.wire = some appendixARow54.item ∧
    encodeDeterministic appendixARow54.item = appendixARow54.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow55_bidirectional :
    parseWellFormed appendixARow55.wire = some appendixARow55.item ∧
    encodePreferred appendixARow55.item = appendixARow55.wire ∧
    decodeDeterministic appendixARow55.wire = some appendixARow55.item ∧
    encodeDeterministic appendixARow55.item = appendixARow55.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow56_bidirectional :
    parseWellFormed appendixARow56.wire = some appendixARow56.item ∧
    encodePreferred appendixARow56.item = appendixARow56.wire ∧
    decodeDeterministic appendixARow56.wire = some appendixARow56.item ∧
    encodeDeterministic appendixARow56.item = appendixARow56.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow57_bidirectional :
    parseWellFormed appendixARow57.wire = some appendixARow57.item ∧
    encodePreferred appendixARow57.item = appendixARow57.wire ∧
    decodeDeterministic appendixARow57.wire = some appendixARow57.item ∧
    encodeDeterministic appendixARow57.item = appendixARow57.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow58_bidirectional :
    parseWellFormed appendixARow58.wire = some appendixARow58.item ∧
    encodePreferred appendixARow58.item = appendixARow58.wire ∧
    decodeDeterministic appendixARow58.wire = some appendixARow58.item ∧
    encodeDeterministic appendixARow58.item = appendixARow58.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow59_bidirectional :
    parseWellFormed appendixARow59.wire = some appendixARow59.item ∧
    encodePreferred appendixARow59.item = appendixARow59.wire ∧
    decodeDeterministic appendixARow59.wire = some appendixARow59.item ∧
    encodeDeterministic appendixARow59.item = appendixARow59.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow60_bidirectional :
    parseWellFormed appendixARow60.wire = some appendixARow60.item ∧
    encodePreferred appendixARow60.item = appendixARow60.wire ∧
    decodeDeterministic appendixARow60.wire = some appendixARow60.item ∧
    encodeDeterministic appendixARow60.item = appendixARow60.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow61_bidirectional :
    parseWellFormed appendixARow61.wire = some appendixARow61.item ∧
    encodePreferred appendixARow61.item = appendixARow61.wire ∧
    decodeDeterministic appendixARow61.wire = some appendixARow61.item ∧
    encodeDeterministic appendixARow61.item = appendixARow61.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow62_bidirectional :
    parseWellFormed appendixARow62.wire = some appendixARow62.item ∧
    encodePreferred appendixARow62.item = appendixARow62.wire ∧
    decodeDeterministic appendixARow62.wire = some appendixARow62.item ∧
    encodeDeterministic appendixARow62.item = appendixARow62.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow63_bidirectional :
    parseWellFormed appendixARow63.wire = some appendixARow63.item ∧
    encodePreferred appendixARow63.item = appendixARow63.wire ∧
    decodeDeterministic appendixARow63.wire = some appendixARow63.item ∧
    encodeDeterministic appendixARow63.item = appendixARow63.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow64_bidirectional :
    parseWellFormed appendixARow64.wire = some appendixARow64.item ∧
    encodePreferred appendixARow64.item = appendixARow64.wire ∧
    decodeDeterministic appendixARow64.wire = some appendixARow64.item ∧
    encodeDeterministic appendixARow64.item = appendixARow64.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow65_bidirectional :
    parseWellFormed appendixARow65.wire = some appendixARow65.item ∧
    encodePreferred appendixARow65.item = appendixARow65.wire ∧
    decodeDeterministic appendixARow65.wire = some appendixARow65.item ∧
    encodeDeterministic appendixARow65.item = appendixARow65.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow66_bidirectional :
    parseWellFormed appendixARow66.wire = some appendixARow66.item ∧
    encodePreferred appendixARow66.item = appendixARow66.wire ∧
    decodeDeterministic appendixARow66.wire = some appendixARow66.item ∧
    encodeDeterministic appendixARow66.item = appendixARow66.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow67_bidirectional :
    parseWellFormed appendixARow67.wire = some appendixARow67.item ∧
    encodePreferred appendixARow67.item = appendixARow67.wire ∧
    decodeDeterministic appendixARow67.wire = some appendixARow67.item ∧
    encodeDeterministic appendixARow67.item = appendixARow67.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow68_bidirectional :
    parseWellFormed appendixARow68.wire = some appendixARow68.item ∧
    encodePreferred appendixARow68.item = appendixARow68.wire ∧
    decodeDeterministic appendixARow68.wire = some appendixARow68.item ∧
    encodeDeterministic appendixARow68.item = appendixARow68.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow69_bidirectional :
    parseWellFormed appendixARow69.wire = some appendixARow69.item ∧
    encodePreferred appendixARow69.item = appendixARow69.wire ∧
    decodeDeterministic appendixARow69.wire = some appendixARow69.item ∧
    encodeDeterministic appendixARow69.item = appendixARow69.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow70_bidirectional :
    parseWellFormed appendixARow70.wire = some appendixARow70.item ∧
    encodePreferred appendixARow70.item = appendixARow70.wire ∧
    decodeDeterministic appendixARow70.wire = some appendixARow70.item ∧
    encodeDeterministic appendixARow70.item = appendixARow70.wire :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow71_bidirectional :
    parseWellFormed appendixARow71.wire = some appendixARow71.item ∧
    encodePreferred appendixARow71.item = appendixARow71.wire ∧
    decodeDeterministic appendixARow71.wire = none ∧
    parseWellFormed (deflateIndefinite appendixARow71.wire) = some appendixARow71.item.toDefinite :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow72_bidirectional :
    parseWellFormed appendixARow72.wire = some appendixARow72.item ∧
    encodePreferred appendixARow72.item = appendixARow72.wire ∧
    decodeDeterministic appendixARow72.wire = none ∧
    parseWellFormed (deflateIndefinite appendixARow72.wire) = some appendixARow72.item.toDefinite :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow73_bidirectional :
    parseWellFormed appendixARow73.wire = some appendixARow73.item ∧
    encodePreferred appendixARow73.item = appendixARow73.wire ∧
    decodeDeterministic appendixARow73.wire = none ∧
    parseWellFormed (deflateIndefinite appendixARow73.wire) = some appendixARow73.item.toDefinite :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow74_bidirectional :
    parseWellFormed appendixARow74.wire = some appendixARow74.item ∧
    encodePreferred appendixARow74.item = appendixARow74.wire ∧
    decodeDeterministic appendixARow74.wire = none ∧
    parseWellFormed (deflateIndefinite appendixARow74.wire) = some appendixARow74.item.toDefinite :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow75_bidirectional :
    parseWellFormed appendixARow75.wire = some appendixARow75.item ∧
    encodePreferred appendixARow75.item = appendixARow75.wire ∧
    decodeDeterministic appendixARow75.wire = none ∧
    parseWellFormed (deflateIndefinite appendixARow75.wire) = some appendixARow75.item.toDefinite :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow76_bidirectional :
    parseWellFormed appendixARow76.wire = some appendixARow76.item ∧
    encodePreferred appendixARow76.item = appendixARow76.wire ∧
    decodeDeterministic appendixARow76.wire = none ∧
    parseWellFormed (deflateIndefinite appendixARow76.wire) = some appendixARow76.item.toDefinite :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow77_bidirectional :
    parseWellFormed appendixARow77.wire = some appendixARow77.item ∧
    encodePreferred appendixARow77.item = appendixARow77.wire ∧
    decodeDeterministic appendixARow77.wire = none ∧
    parseWellFormed (deflateIndefinite appendixARow77.wire) = some appendixARow77.item.toDefinite :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow78_bidirectional :
    parseWellFormed appendixARow78.wire = some appendixARow78.item ∧
    encodePreferred appendixARow78.item = appendixARow78.wire ∧
    decodeDeterministic appendixARow78.wire = none ∧
    parseWellFormed (deflateIndefinite appendixARow78.wire) = some appendixARow78.item.toDefinite :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow79_bidirectional :
    parseWellFormed appendixARow79.wire = some appendixARow79.item ∧
    encodePreferred appendixARow79.item = appendixARow79.wire ∧
    decodeDeterministic appendixARow79.wire = none ∧
    parseWellFormed (deflateIndefinite appendixARow79.wire) = some appendixARow79.item.toDefinite :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow80_bidirectional :
    parseWellFormed appendixARow80.wire = some appendixARow80.item ∧
    encodePreferred appendixARow80.item = appendixARow80.wire ∧
    decodeDeterministic appendixARow80.wire = none ∧
    parseWellFormed (deflateIndefinite appendixARow80.wire) = some appendixARow80.item.toDefinite :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem appendixARow81_bidirectional :
    parseWellFormed appendixARow81.wire = some appendixARow81.item ∧
    encodePreferred appendixARow81.item = appendixARow81.wire ∧
    decodeDeterministic appendixARow81.wire = none ∧
    parseWellFormed (deflateIndefinite appendixARow81.wire) = some appendixARow81.item.toDefinite :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Integer and tag-2/3 bignum semantic round trips (Appendix A rows 1..18) -/

theorem appendixARow01_int_roundtrip :
    appendixARow01.item.intValue? = some (0 : Int) ∧
    encodeInt (0 : Int) = appendixARow01.item ∧
    encodeDeterministic (encodeInt (0 : Int)) = appendixARow01.wire := by
  have henc : encodeInt (0 : Int) = appendixARow01.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow01.item) (z := (0 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow01_bidirectional.2.2.2⟩

theorem appendixARow02_int_roundtrip :
    appendixARow02.item.intValue? = some (1 : Int) ∧
    encodeInt (1 : Int) = appendixARow02.item ∧
    encodeDeterministic (encodeInt (1 : Int)) = appendixARow02.wire := by
  have henc : encodeInt (1 : Int) = appendixARow02.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow02.item) (z := (1 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow02_bidirectional.2.2.2⟩

theorem appendixARow03_int_roundtrip :
    appendixARow03.item.intValue? = some (10 : Int) ∧
    encodeInt (10 : Int) = appendixARow03.item ∧
    encodeDeterministic (encodeInt (10 : Int)) = appendixARow03.wire := by
  have henc : encodeInt (10 : Int) = appendixARow03.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow03.item) (z := (10 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow03_bidirectional.2.2.2⟩

theorem appendixARow04_int_roundtrip :
    appendixARow04.item.intValue? = some (23 : Int) ∧
    encodeInt (23 : Int) = appendixARow04.item ∧
    encodeDeterministic (encodeInt (23 : Int)) = appendixARow04.wire := by
  have henc : encodeInt (23 : Int) = appendixARow04.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow04.item) (z := (23 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow04_bidirectional.2.2.2⟩

theorem appendixARow05_int_roundtrip :
    appendixARow05.item.intValue? = some (24 : Int) ∧
    encodeInt (24 : Int) = appendixARow05.item ∧
    encodeDeterministic (encodeInt (24 : Int)) = appendixARow05.wire := by
  have henc : encodeInt (24 : Int) = appendixARow05.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow05.item) (z := (24 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow05_bidirectional.2.2.2⟩

theorem appendixARow06_int_roundtrip :
    appendixARow06.item.intValue? = some (25 : Int) ∧
    encodeInt (25 : Int) = appendixARow06.item ∧
    encodeDeterministic (encodeInt (25 : Int)) = appendixARow06.wire := by
  have henc : encodeInt (25 : Int) = appendixARow06.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow06.item) (z := (25 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow06_bidirectional.2.2.2⟩

theorem appendixARow07_int_roundtrip :
    appendixARow07.item.intValue? = some (100 : Int) ∧
    encodeInt (100 : Int) = appendixARow07.item ∧
    encodeDeterministic (encodeInt (100 : Int)) = appendixARow07.wire := by
  have henc : encodeInt (100 : Int) = appendixARow07.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow07.item) (z := (100 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow07_bidirectional.2.2.2⟩

theorem appendixARow08_int_roundtrip :
    appendixARow08.item.intValue? = some (1000 : Int) ∧
    encodeInt (1000 : Int) = appendixARow08.item ∧
    encodeDeterministic (encodeInt (1000 : Int)) = appendixARow08.wire := by
  have henc : encodeInt (1000 : Int) = appendixARow08.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow08.item) (z := (1000 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow08_bidirectional.2.2.2⟩

theorem appendixARow09_int_roundtrip :
    appendixARow09.item.intValue? = some (1000000 : Int) ∧
    encodeInt (1000000 : Int) = appendixARow09.item ∧
    encodeDeterministic (encodeInt (1000000 : Int)) = appendixARow09.wire := by
  have henc : encodeInt (1000000 : Int) = appendixARow09.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow09.item) (z := (1000000 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow09_bidirectional.2.2.2⟩

theorem appendixARow10_int_roundtrip :
    appendixARow10.item.intValue? = some (1000000000000 : Int) ∧
    encodeInt (1000000000000 : Int) = appendixARow10.item ∧
    encodeDeterministic (encodeInt (1000000000000 : Int)) = appendixARow10.wire := by
  have henc : encodeInt (1000000000000 : Int) = appendixARow10.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow10.item) (z := (1000000000000 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow10_bidirectional.2.2.2⟩

theorem appendixARow11_int_roundtrip :
    appendixARow11.item.intValue? = some (18446744073709551615 : Int) ∧
    encodeInt (18446744073709551615 : Int) = appendixARow11.item ∧
    encodeDeterministic (encodeInt (18446744073709551615 : Int)) = appendixARow11.wire := by
  have henc : encodeInt (18446744073709551615 : Int) = appendixARow11.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow11.item) (z := (18446744073709551615 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow11_bidirectional.2.2.2⟩

theorem appendixARow12_int_roundtrip :
    appendixARow12.item.intValue? = some (18446744073709551616 : Int) ∧
    encodeInt (18446744073709551616 : Int) = appendixARow12.item ∧
    encodeDeterministic (encodeInt (18446744073709551616 : Int)) = appendixARow12.wire := by
  have henc : encodeInt (18446744073709551616 : Int) = appendixARow12.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow12.item) (z := (18446744073709551616 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow12_bidirectional.2.2.2⟩

theorem appendixARow13_int_roundtrip :
    appendixARow13.item.intValue? = some (-18446744073709551616 : Int) ∧
    encodeInt (-18446744073709551616 : Int) = appendixARow13.item ∧
    encodeDeterministic (encodeInt (-18446744073709551616 : Int)) = appendixARow13.wire := by
  have henc : encodeInt (-18446744073709551616 : Int) = appendixARow13.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow13.item) (z := (-18446744073709551616 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow13_bidirectional.2.2.2⟩

theorem appendixARow14_int_roundtrip :
    appendixARow14.item.intValue? = some (-18446744073709551617 : Int) ∧
    encodeInt (-18446744073709551617 : Int) = appendixARow14.item ∧
    encodeDeterministic (encodeInt (-18446744073709551617 : Int)) = appendixARow14.wire := by
  have henc : encodeInt (-18446744073709551617 : Int) = appendixARow14.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow14.item) (z := (-18446744073709551617 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow14_bidirectional.2.2.2⟩

theorem appendixARow15_int_roundtrip :
    appendixARow15.item.intValue? = some (-1 : Int) ∧
    encodeInt (-1 : Int) = appendixARow15.item ∧
    encodeDeterministic (encodeInt (-1 : Int)) = appendixARow15.wire := by
  have henc : encodeInt (-1 : Int) = appendixARow15.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow15.item) (z := (-1 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow15_bidirectional.2.2.2⟩

theorem appendixARow16_int_roundtrip :
    appendixARow16.item.intValue? = some (-10 : Int) ∧
    encodeInt (-10 : Int) = appendixARow16.item ∧
    encodeDeterministic (encodeInt (-10 : Int)) = appendixARow16.wire := by
  have henc : encodeInt (-10 : Int) = appendixARow16.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow16.item) (z := (-10 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow16_bidirectional.2.2.2⟩

theorem appendixARow17_int_roundtrip :
    appendixARow17.item.intValue? = some (-100 : Int) ∧
    encodeInt (-100 : Int) = appendixARow17.item ∧
    encodeDeterministic (encodeInt (-100 : Int)) = appendixARow17.wire := by
  have henc : encodeInt (-100 : Int) = appendixARow17.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow17.item) (z := (-100 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow17_bidirectional.2.2.2⟩

theorem appendixARow18_int_roundtrip :
    appendixARow18.item.intValue? = some (-1000 : Int) ∧
    encodeInt (-1000 : Int) = appendixARow18.item ∧
    encodeDeterministic (encodeInt (-1000 : Int)) = appendixARow18.wire := by
  have henc : encodeInt (-1000 : Int) = appendixARow18.item :=
    (eq_encodeInt_of_isPreferredInt (x := appendixARow18.item) (z := (-1000 : Int)) (by decide) (by decide)).symm
  exact ⟨by decide, henc, by rw [henc]; exact appendixARow18_bidirectional.2.2.2⟩

/-- Row 81 (`{_ "Fun": true, "Amt": -2}`) illustrates the distinction between
`deflateIndefinite` (which preserves wire entry order `"Fun"` then `"Amt"`)
and `encodeDeterministic` (which sorts `"Amt"` before `"Fun"` per §4.2.1). -/
theorem appendixARow81_deflate_vs_deterministic :
    deflateIndefinite appendixARow81.wire =
      [0xa2, 0x63, 0x46, 0x75, 0x6e, 0xf5, 0x63, 0x41, 0x6d, 0x74, 0x21] ∧
    encodeDeterministic appendixARow81.item =
      [0xa2, 0x63, 0x41, 0x6d, 0x74, 0x21, 0x63, 0x46, 0x75, 0x6e, 0xf5] :=
  ⟨rfl, rfl⟩

/-- **Universal Appendix A float-free theorem:** all 58 float-free vectors
round-trip in both directions through `parseWellFormed` / `encodePreferred`,
and satisfy deterministic round-trip (47 definite rows) or indefinite
rejection + deflation (11 indefinite rows). -/
theorem appendixAFloatFree_all_bidirectional :
    ∀ v ∈ appendixAFloatFreeVectors,
      parseWellFormed v.wire = some v.item ∧
      encodePreferred v.item = v.wire ∧
      (if v.definite then
         decodeDeterministic v.wire = some v.item ∧
         encodeDeterministic v.item = v.wire
       else
         decodeDeterministic v.wire = none ∧
         parseWellFormed (deflateIndefinite v.wire) = some v.item.toDefinite) := by
  intro v hv
  simp only [appendixAFloatFreeVectors, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨appendixARow01_bidirectional.1, appendixARow01_bidirectional.2.1, appendixARow01_bidirectional.2.2⟩
  · exact ⟨appendixARow02_bidirectional.1, appendixARow02_bidirectional.2.1, appendixARow02_bidirectional.2.2⟩
  · exact ⟨appendixARow03_bidirectional.1, appendixARow03_bidirectional.2.1, appendixARow03_bidirectional.2.2⟩
  · exact ⟨appendixARow04_bidirectional.1, appendixARow04_bidirectional.2.1, appendixARow04_bidirectional.2.2⟩
  · exact ⟨appendixARow05_bidirectional.1, appendixARow05_bidirectional.2.1, appendixARow05_bidirectional.2.2⟩
  · exact ⟨appendixARow06_bidirectional.1, appendixARow06_bidirectional.2.1, appendixARow06_bidirectional.2.2⟩
  · exact ⟨appendixARow07_bidirectional.1, appendixARow07_bidirectional.2.1, appendixARow07_bidirectional.2.2⟩
  · exact ⟨appendixARow08_bidirectional.1, appendixARow08_bidirectional.2.1, appendixARow08_bidirectional.2.2⟩
  · exact ⟨appendixARow09_bidirectional.1, appendixARow09_bidirectional.2.1, appendixARow09_bidirectional.2.2⟩
  · exact ⟨appendixARow10_bidirectional.1, appendixARow10_bidirectional.2.1, appendixARow10_bidirectional.2.2⟩
  · exact ⟨appendixARow11_bidirectional.1, appendixARow11_bidirectional.2.1, appendixARow11_bidirectional.2.2⟩
  · exact ⟨appendixARow12_bidirectional.1, appendixARow12_bidirectional.2.1, appendixARow12_bidirectional.2.2⟩
  · exact ⟨appendixARow13_bidirectional.1, appendixARow13_bidirectional.2.1, appendixARow13_bidirectional.2.2⟩
  · exact ⟨appendixARow14_bidirectional.1, appendixARow14_bidirectional.2.1, appendixARow14_bidirectional.2.2⟩
  · exact ⟨appendixARow15_bidirectional.1, appendixARow15_bidirectional.2.1, appendixARow15_bidirectional.2.2⟩
  · exact ⟨appendixARow16_bidirectional.1, appendixARow16_bidirectional.2.1, appendixARow16_bidirectional.2.2⟩
  · exact ⟨appendixARow17_bidirectional.1, appendixARow17_bidirectional.2.1, appendixARow17_bidirectional.2.2⟩
  · exact ⟨appendixARow18_bidirectional.1, appendixARow18_bidirectional.2.1, appendixARow18_bidirectional.2.2⟩
  · exact ⟨appendixARow41_bidirectional.1, appendixARow41_bidirectional.2.1, appendixARow41_bidirectional.2.2⟩
  · exact ⟨appendixARow42_bidirectional.1, appendixARow42_bidirectional.2.1, appendixARow42_bidirectional.2.2⟩
  · exact ⟨appendixARow43_bidirectional.1, appendixARow43_bidirectional.2.1, appendixARow43_bidirectional.2.2⟩
  · exact ⟨appendixARow44_bidirectional.1, appendixARow44_bidirectional.2.1, appendixARow44_bidirectional.2.2⟩
  · exact ⟨appendixARow45_bidirectional.1, appendixARow45_bidirectional.2.1, appendixARow45_bidirectional.2.2⟩
  · exact ⟨appendixARow46_bidirectional.1, appendixARow46_bidirectional.2.1, appendixARow46_bidirectional.2.2⟩
  · exact ⟨appendixARow47_bidirectional.1, appendixARow47_bidirectional.2.1, appendixARow47_bidirectional.2.2⟩
  · exact ⟨appendixARow48_bidirectional.1, appendixARow48_bidirectional.2.1, appendixARow48_bidirectional.2.2⟩
  · exact ⟨appendixARow50_bidirectional.1, appendixARow50_bidirectional.2.1, appendixARow50_bidirectional.2.2⟩
  · exact ⟨appendixARow51_bidirectional.1, appendixARow51_bidirectional.2.1, appendixARow51_bidirectional.2.2⟩
  · exact ⟨appendixARow52_bidirectional.1, appendixARow52_bidirectional.2.1, appendixARow52_bidirectional.2.2⟩
  · exact ⟨appendixARow53_bidirectional.1, appendixARow53_bidirectional.2.1, appendixARow53_bidirectional.2.2⟩
  · exact ⟨appendixARow54_bidirectional.1, appendixARow54_bidirectional.2.1, appendixARow54_bidirectional.2.2⟩
  · exact ⟨appendixARow55_bidirectional.1, appendixARow55_bidirectional.2.1, appendixARow55_bidirectional.2.2⟩
  · exact ⟨appendixARow56_bidirectional.1, appendixARow56_bidirectional.2.1, appendixARow56_bidirectional.2.2⟩
  · exact ⟨appendixARow57_bidirectional.1, appendixARow57_bidirectional.2.1, appendixARow57_bidirectional.2.2⟩
  · exact ⟨appendixARow58_bidirectional.1, appendixARow58_bidirectional.2.1, appendixARow58_bidirectional.2.2⟩
  · exact ⟨appendixARow59_bidirectional.1, appendixARow59_bidirectional.2.1, appendixARow59_bidirectional.2.2⟩
  · exact ⟨appendixARow60_bidirectional.1, appendixARow60_bidirectional.2.1, appendixARow60_bidirectional.2.2⟩
  · exact ⟨appendixARow61_bidirectional.1, appendixARow61_bidirectional.2.1, appendixARow61_bidirectional.2.2⟩
  · exact ⟨appendixARow62_bidirectional.1, appendixARow62_bidirectional.2.1, appendixARow62_bidirectional.2.2⟩
  · exact ⟨appendixARow63_bidirectional.1, appendixARow63_bidirectional.2.1, appendixARow63_bidirectional.2.2⟩
  · exact ⟨appendixARow64_bidirectional.1, appendixARow64_bidirectional.2.1, appendixARow64_bidirectional.2.2⟩
  · exact ⟨appendixARow65_bidirectional.1, appendixARow65_bidirectional.2.1, appendixARow65_bidirectional.2.2⟩
  · exact ⟨appendixARow66_bidirectional.1, appendixARow66_bidirectional.2.1, appendixARow66_bidirectional.2.2⟩
  · exact ⟨appendixARow67_bidirectional.1, appendixARow67_bidirectional.2.1, appendixARow67_bidirectional.2.2⟩
  · exact ⟨appendixARow68_bidirectional.1, appendixARow68_bidirectional.2.1, appendixARow68_bidirectional.2.2⟩
  · exact ⟨appendixARow69_bidirectional.1, appendixARow69_bidirectional.2.1, appendixARow69_bidirectional.2.2⟩
  · exact ⟨appendixARow70_bidirectional.1, appendixARow70_bidirectional.2.1, appendixARow70_bidirectional.2.2⟩
  · exact ⟨appendixARow71_bidirectional.1, appendixARow71_bidirectional.2.1, appendixARow71_bidirectional.2.2⟩
  · exact ⟨appendixARow72_bidirectional.1, appendixARow72_bidirectional.2.1, appendixARow72_bidirectional.2.2⟩
  · exact ⟨appendixARow73_bidirectional.1, appendixARow73_bidirectional.2.1, appendixARow73_bidirectional.2.2⟩
  · exact ⟨appendixARow74_bidirectional.1, appendixARow74_bidirectional.2.1, appendixARow74_bidirectional.2.2⟩
  · exact ⟨appendixARow75_bidirectional.1, appendixARow75_bidirectional.2.1, appendixARow75_bidirectional.2.2⟩
  · exact ⟨appendixARow76_bidirectional.1, appendixARow76_bidirectional.2.1, appendixARow76_bidirectional.2.2⟩
  · exact ⟨appendixARow77_bidirectional.1, appendixARow77_bidirectional.2.1, appendixARow77_bidirectional.2.2⟩
  · exact ⟨appendixARow78_bidirectional.1, appendixARow78_bidirectional.2.1, appendixARow78_bidirectional.2.2⟩
  · exact ⟨appendixARow79_bidirectional.1, appendixARow79_bidirectional.2.1, appendixARow79_bidirectional.2.2⟩
  · exact ⟨appendixARow80_bidirectional.1, appendixARow80_bidirectional.2.1, appendixARow80_bidirectional.2.2⟩
  · exact ⟨appendixARow81_bidirectional.1, appendixARow81_bidirectional.2.1, appendixARow81_bidirectional.2.2⟩

end Cbor.Rfc8949.Vectors
