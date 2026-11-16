/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Ordering

/-!
# RFC 8949 Appendix F.1: all 94 not-well-formed byte sequences refused

RFC 8949 Appendix F.1 lists 94 malformed CBOR byte sequences across 14
failure categories (group counts `[18, 6, 7, 1, 2, 8, 24, 4, 8, 2, 1, 8, 2, 3]`,
sum = 94): truncated heads, short definite-length strings, unclosed definite
and indefinite arrays/maps, bare tag heads, reserved additional information
`28..30`, reserved two-byte simple values `0xf8 0x00..0x1f`, mistyped or
indefinite string chunks, bare or misplaced `break` (`0xff`) stop codes,
odd-item indefinite maps, and additional information `31` on major types
`0, 1, 6`.

**Note on the 3 truncated float heads in Group 1 (`f900`, `fa0000`, `fb000000`):**
Group 1 ("End of input in a head", 18 sequences) includes 15 truncated
integer/string/array/map/tag/simple heads and 3 truncated IEEE 754 float
heads (`0xf9 0x00`, `0xfa 0x00 0x00`, `0xfb 0x00 0x00 0x00`). In Milestone 1,
`decodeHead` rejects `0xf9`/`0xfa`/`0xfb` unconditionally because floats are
outside the float-free fragment; Milestone 2 will accept complete 2/4/8-byte
float heads while continuing to reject these 3 truncated heads.

Every one of the 94 sequences is verified in-kernel to return `none` under
`parseWellFormed`, `parseRaw`, `decodeDeterministic`, `decodeStrict` (both
`.basic` and `.extended`), and `decodeFirstWins` (both `.basic` and
`.extended`).
-/

namespace Cbor.Rfc8949.Vectors

/-- One category of malformed byte sequences from RFC 8949 Appendix F.1. -/
structure AppendixF1Group where
  /-- 1-based group index (`1..14`). -/
  groupIndex : Nat
  /-- Category label from RFC 8949 Appendix F.1. -/
  label : String
  /-- Malformed byte sequences in this category. -/
  sequences : List (List UInt8)
  deriving Repr

/-- Appendix F.1 sequence 1 (group 1, `18`). -/
def appendixF1Seq01 : List UInt8 := [0x18]

/-- Appendix F.1 sequence 2 (group 1, `19`). -/
def appendixF1Seq02 : List UInt8 := [0x19]

/-- Appendix F.1 sequence 3 (group 1, `1a`). -/
def appendixF1Seq03 : List UInt8 := [0x1a]

/-- Appendix F.1 sequence 4 (group 1, `1b`). -/
def appendixF1Seq04 : List UInt8 := [0x1b]

/-- Appendix F.1 sequence 5 (group 1, `1901`). -/
def appendixF1Seq05 : List UInt8 := [0x19, 0x01]

/-- Appendix F.1 sequence 6 (group 1, `1a0102`). -/
def appendixF1Seq06 : List UInt8 := [0x1a, 0x01, 0x02]

/-- Appendix F.1 sequence 7 (group 1, `1b01020304050607`). -/
def appendixF1Seq07 : List UInt8 := [0x1b, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]

/-- Appendix F.1 sequence 8 (group 1, `38`). -/
def appendixF1Seq08 : List UInt8 := [0x38]

/-- Appendix F.1 sequence 9 (group 1, `58`). -/
def appendixF1Seq09 : List UInt8 := [0x58]

/-- Appendix F.1 sequence 10 (group 1, `78`). -/
def appendixF1Seq10 : List UInt8 := [0x78]

/-- Appendix F.1 sequence 11 (group 1, `98`). -/
def appendixF1Seq11 : List UInt8 := [0x98]

/-- Appendix F.1 sequence 12 (group 1, `9a01ff00`). -/
def appendixF1Seq12 : List UInt8 := [0x9a, 0x01, 0xff, 0x00]

/-- Appendix F.1 sequence 13 (group 1, `b8`). -/
def appendixF1Seq13 : List UInt8 := [0xb8]

/-- Appendix F.1 sequence 14 (group 1, `d8`). -/
def appendixF1Seq14 : List UInt8 := [0xd8]

/-- Appendix F.1 sequence 15 (group 1, `f8`). -/
def appendixF1Seq15 : List UInt8 := [0xf8]

/-- Appendix F.1 sequence 16 (group 1, `f900`). -/
def appendixF1Seq16 : List UInt8 := [0xf9, 0x00]

/-- Appendix F.1 sequence 17 (group 1, `fa0000`). -/
def appendixF1Seq17 : List UInt8 := [0xfa, 0x00, 0x00]

/-- Appendix F.1 sequence 18 (group 1, `fb000000`). -/
def appendixF1Seq18 : List UInt8 := [0xfb, 0x00, 0x00, 0x00]

/-- Appendix F.1 group 1: End of input in a head: (18 sequences). -/
def appendixF1Group01 : AppendixF1Group where
  groupIndex := 1
  label := "End of input in a head:"
  sequences := [appendixF1Seq01, appendixF1Seq02, appendixF1Seq03, appendixF1Seq04, appendixF1Seq05, appendixF1Seq06, appendixF1Seq07, appendixF1Seq08, appendixF1Seq09, appendixF1Seq10, appendixF1Seq11, appendixF1Seq12, appendixF1Seq13, appendixF1Seq14, appendixF1Seq15, appendixF1Seq16, appendixF1Seq17, appendixF1Seq18]

/-- Appendix F.1 sequence 19 (group 2, `41`). -/
def appendixF1Seq19 : List UInt8 := [0x41]

/-- Appendix F.1 sequence 20 (group 2, `61`). -/
def appendixF1Seq20 : List UInt8 := [0x61]

/-- Appendix F.1 sequence 21 (group 2, `5affffffff00`). -/
def appendixF1Seq21 : List UInt8 := [0x5a, 0xff, 0xff, 0xff, 0xff, 0x00]

/-- Appendix F.1 sequence 22 (group 2, `5bffffffffffffffff010203`). -/
def appendixF1Seq22 : List UInt8 := [0x5b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01, 0x02, 0x03]

/-- Appendix F.1 sequence 23 (group 2, `7affffffff00`). -/
def appendixF1Seq23 : List UInt8 := [0x7a, 0xff, 0xff, 0xff, 0xff, 0x00]

/-- Appendix F.1 sequence 24 (group 2, `7b7fffffffffffffff010203`). -/
def appendixF1Seq24 : List UInt8 := [0x7b, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01, 0x02, 0x03]

/-- Appendix F.1 group 2: Definite-length strings with short data: (6 sequences). -/
def appendixF1Group02 : AppendixF1Group where
  groupIndex := 2
  label := "Definite-length strings with short data:"
  sequences := [appendixF1Seq19, appendixF1Seq20, appendixF1Seq21, appendixF1Seq22, appendixF1Seq23, appendixF1Seq24]

/-- Appendix F.1 sequence 25 (group 3, `81`). -/
def appendixF1Seq25 : List UInt8 := [0x81]

/-- Appendix F.1 sequence 26 (group 3, `818181818181818181`). -/
def appendixF1Seq26 : List UInt8 := [0x81, 0x81, 0x81, 0x81, 0x81, 0x81, 0x81, 0x81, 0x81]

/-- Appendix F.1 sequence 27 (group 3, `8200`). -/
def appendixF1Seq27 : List UInt8 := [0x82, 0x00]

/-- Appendix F.1 sequence 28 (group 3, `a1`). -/
def appendixF1Seq28 : List UInt8 := [0xa1]

/-- Appendix F.1 sequence 29 (group 3, `a20102`). -/
def appendixF1Seq29 : List UInt8 := [0xa2, 0x01, 0x02]

/-- Appendix F.1 sequence 30 (group 3, `a100`). -/
def appendixF1Seq30 : List UInt8 := [0xa1, 0x00]

/-- Appendix F.1 sequence 31 (group 3, `a2000000`). -/
def appendixF1Seq31 : List UInt8 := [0xa2, 0x00, 0x00, 0x00]

/-- Appendix F.1 group 3: Definite-length maps and arrays not closed with enough items: (7 sequences). -/
def appendixF1Group03 : AppendixF1Group where
  groupIndex := 3
  label := "Definite-length maps and arrays not closed with enough items:"
  sequences := [appendixF1Seq25, appendixF1Seq26, appendixF1Seq27, appendixF1Seq28, appendixF1Seq29, appendixF1Seq30, appendixF1Seq31]

/-- Appendix F.1 sequence 32 (group 4, `c0`). -/
def appendixF1Seq32 : List UInt8 := [0xc0]

/-- Appendix F.1 group 4: Tag number not followed by tag content: (1 sequences). -/
def appendixF1Group04 : AppendixF1Group where
  groupIndex := 4
  label := "Tag number not followed by tag content:"
  sequences := [appendixF1Seq32]

/-- Appendix F.1 sequence 33 (group 5, `5f4100`). -/
def appendixF1Seq33 : List UInt8 := [0x5f, 0x41, 0x00]

/-- Appendix F.1 sequence 34 (group 5, `7f6100`). -/
def appendixF1Seq34 : List UInt8 := [0x7f, 0x61, 0x00]

/-- Appendix F.1 group 5: Indefinite-length strings not closed by a "break" stop code: (2 sequences). -/
def appendixF1Group05 : AppendixF1Group where
  groupIndex := 5
  label := "Indefinite-length strings not closed by a \"break\" stop code:"
  sequences := [appendixF1Seq33, appendixF1Seq34]

/-- Appendix F.1 sequence 35 (group 6, `9f`). -/
def appendixF1Seq35 : List UInt8 := [0x9f]

/-- Appendix F.1 sequence 36 (group 6, `9f0102`). -/
def appendixF1Seq36 : List UInt8 := [0x9f, 0x01, 0x02]

/-- Appendix F.1 sequence 37 (group 6, `bf`). -/
def appendixF1Seq37 : List UInt8 := [0xbf]

/-- Appendix F.1 sequence 38 (group 6, `bf01020102`). -/
def appendixF1Seq38 : List UInt8 := [0xbf, 0x01, 0x02, 0x01, 0x02]

/-- Appendix F.1 sequence 39 (group 6, `819f`). -/
def appendixF1Seq39 : List UInt8 := [0x81, 0x9f]

/-- Appendix F.1 sequence 40 (group 6, `9f8000`). -/
def appendixF1Seq40 : List UInt8 := [0x9f, 0x80, 0x00]

/-- Appendix F.1 sequence 41 (group 6, `9f9f9f9f9fffffffff`). -/
def appendixF1Seq41 : List UInt8 := [0x9f, 0x9f, 0x9f, 0x9f, 0x9f, 0xff, 0xff, 0xff, 0xff]

/-- Appendix F.1 sequence 42 (group 6, `9f819f819f9fffffff`). -/
def appendixF1Seq42 : List UInt8 := [0x9f, 0x81, 0x9f, 0x81, 0x9f, 0x9f, 0xff, 0xff, 0xff]

/-- Appendix F.1 group 6: Indefinite-length maps and arrays not closed by a "break" stop code: (8 sequences). -/
def appendixF1Group06 : AppendixF1Group where
  groupIndex := 6
  label := "Indefinite-length maps and arrays not closed by a \"break\" stop code:"
  sequences := [appendixF1Seq35, appendixF1Seq36, appendixF1Seq37, appendixF1Seq38, appendixF1Seq39, appendixF1Seq40, appendixF1Seq41, appendixF1Seq42]

/-- Appendix F.1 sequence 43 (group 7, `1c`). -/
def appendixF1Seq43 : List UInt8 := [0x1c]

/-- Appendix F.1 sequence 44 (group 7, `1d`). -/
def appendixF1Seq44 : List UInt8 := [0x1d]

/-- Appendix F.1 sequence 45 (group 7, `1e`). -/
def appendixF1Seq45 : List UInt8 := [0x1e]

/-- Appendix F.1 sequence 46 (group 7, `3c`). -/
def appendixF1Seq46 : List UInt8 := [0x3c]

/-- Appendix F.1 sequence 47 (group 7, `3d`). -/
def appendixF1Seq47 : List UInt8 := [0x3d]

/-- Appendix F.1 sequence 48 (group 7, `3e`). -/
def appendixF1Seq48 : List UInt8 := [0x3e]

/-- Appendix F.1 sequence 49 (group 7, `5c`). -/
def appendixF1Seq49 : List UInt8 := [0x5c]

/-- Appendix F.1 sequence 50 (group 7, `5d`). -/
def appendixF1Seq50 : List UInt8 := [0x5d]

/-- Appendix F.1 sequence 51 (group 7, `5e`). -/
def appendixF1Seq51 : List UInt8 := [0x5e]

/-- Appendix F.1 sequence 52 (group 7, `7c`). -/
def appendixF1Seq52 : List UInt8 := [0x7c]

/-- Appendix F.1 sequence 53 (group 7, `7d`). -/
def appendixF1Seq53 : List UInt8 := [0x7d]

/-- Appendix F.1 sequence 54 (group 7, `7e`). -/
def appendixF1Seq54 : List UInt8 := [0x7e]

/-- Appendix F.1 sequence 55 (group 7, `9c`). -/
def appendixF1Seq55 : List UInt8 := [0x9c]

/-- Appendix F.1 sequence 56 (group 7, `9d`). -/
def appendixF1Seq56 : List UInt8 := [0x9d]

/-- Appendix F.1 sequence 57 (group 7, `9e`). -/
def appendixF1Seq57 : List UInt8 := [0x9e]

/-- Appendix F.1 sequence 58 (group 7, `bc`). -/
def appendixF1Seq58 : List UInt8 := [0xbc]

/-- Appendix F.1 sequence 59 (group 7, `bd`). -/
def appendixF1Seq59 : List UInt8 := [0xbd]

/-- Appendix F.1 sequence 60 (group 7, `be`). -/
def appendixF1Seq60 : List UInt8 := [0xbe]

/-- Appendix F.1 sequence 61 (group 7, `dc`). -/
def appendixF1Seq61 : List UInt8 := [0xdc]

/-- Appendix F.1 sequence 62 (group 7, `dd`). -/
def appendixF1Seq62 : List UInt8 := [0xdd]

/-- Appendix F.1 sequence 63 (group 7, `de`). -/
def appendixF1Seq63 : List UInt8 := [0xde]

/-- Appendix F.1 sequence 64 (group 7, `fc`). -/
def appendixF1Seq64 : List UInt8 := [0xfc]

/-- Appendix F.1 sequence 65 (group 7, `fd`). -/
def appendixF1Seq65 : List UInt8 := [0xfd]

/-- Appendix F.1 sequence 66 (group 7, `fe`). -/
def appendixF1Seq66 : List UInt8 := [0xfe]

/-- Appendix F.1 group 7: Reserved additional information values: (24 sequences). -/
def appendixF1Group07 : AppendixF1Group where
  groupIndex := 7
  label := "Reserved additional information values:"
  sequences := [appendixF1Seq43, appendixF1Seq44, appendixF1Seq45, appendixF1Seq46, appendixF1Seq47, appendixF1Seq48, appendixF1Seq49, appendixF1Seq50, appendixF1Seq51, appendixF1Seq52, appendixF1Seq53, appendixF1Seq54, appendixF1Seq55, appendixF1Seq56, appendixF1Seq57, appendixF1Seq58, appendixF1Seq59, appendixF1Seq60, appendixF1Seq61, appendixF1Seq62, appendixF1Seq63, appendixF1Seq64, appendixF1Seq65, appendixF1Seq66]

/-- Appendix F.1 sequence 67 (group 8, `f800`). -/
def appendixF1Seq67 : List UInt8 := [0xf8, 0x00]

/-- Appendix F.1 sequence 68 (group 8, `f801`). -/
def appendixF1Seq68 : List UInt8 := [0xf8, 0x01]

/-- Appendix F.1 sequence 69 (group 8, `f818`). -/
def appendixF1Seq69 : List UInt8 := [0xf8, 0x18]

/-- Appendix F.1 sequence 70 (group 8, `f81f`). -/
def appendixF1Seq70 : List UInt8 := [0xf8, 0x1f]

/-- Appendix F.1 group 8: Reserved two-byte encodings of simple values: (4 sequences). -/
def appendixF1Group08 : AppendixF1Group where
  groupIndex := 8
  label := "Reserved two-byte encodings of simple values:"
  sequences := [appendixF1Seq67, appendixF1Seq68, appendixF1Seq69, appendixF1Seq70]

/-- Appendix F.1 sequence 71 (group 9, `5f00ff`). -/
def appendixF1Seq71 : List UInt8 := [0x5f, 0x00, 0xff]

/-- Appendix F.1 sequence 72 (group 9, `5f21ff`). -/
def appendixF1Seq72 : List UInt8 := [0x5f, 0x21, 0xff]

/-- Appendix F.1 sequence 73 (group 9, `5f6100ff`). -/
def appendixF1Seq73 : List UInt8 := [0x5f, 0x61, 0x00, 0xff]

/-- Appendix F.1 sequence 74 (group 9, `5f80ff`). -/
def appendixF1Seq74 : List UInt8 := [0x5f, 0x80, 0xff]

/-- Appendix F.1 sequence 75 (group 9, `5fa0ff`). -/
def appendixF1Seq75 : List UInt8 := [0x5f, 0xa0, 0xff]

/-- Appendix F.1 sequence 76 (group 9, `5fc000ff`). -/
def appendixF1Seq76 : List UInt8 := [0x5f, 0xc0, 0x00, 0xff]

/-- Appendix F.1 sequence 77 (group 9, `5fe0ff`). -/
def appendixF1Seq77 : List UInt8 := [0x5f, 0xe0, 0xff]

/-- Appendix F.1 sequence 78 (group 9, `7f4100ff`). -/
def appendixF1Seq78 : List UInt8 := [0x7f, 0x41, 0x00, 0xff]

/-- Appendix F.1 group 9: Indefinite-length string chunks not of the correct type: (8 sequences). -/
def appendixF1Group09 : AppendixF1Group where
  groupIndex := 9
  label := "Indefinite-length string chunks not of the correct type:"
  sequences := [appendixF1Seq71, appendixF1Seq72, appendixF1Seq73, appendixF1Seq74, appendixF1Seq75, appendixF1Seq76, appendixF1Seq77, appendixF1Seq78]

/-- Appendix F.1 sequence 79 (group 10, `5f5f4100ffff`). -/
def appendixF1Seq79 : List UInt8 := [0x5f, 0x5f, 0x41, 0x00, 0xff, 0xff]

/-- Appendix F.1 sequence 80 (group 10, `7f7f6100ffff`). -/
def appendixF1Seq80 : List UInt8 := [0x7f, 0x7f, 0x61, 0x00, 0xff, 0xff]

/-- Appendix F.1 group 10: Indefinite-length string chunks not definite length: (2 sequences). -/
def appendixF1Group10 : AppendixF1Group where
  groupIndex := 10
  label := "Indefinite-length string chunks not definite length:"
  sequences := [appendixF1Seq79, appendixF1Seq80]

/-- Appendix F.1 sequence 81 (group 11, `ff`). -/
def appendixF1Seq81 : List UInt8 := [0xff]

/-- Appendix F.1 group 11: Break occurring on its own outside of an indefinite-length item: (1 sequences). -/
def appendixF1Group11 : AppendixF1Group where
  groupIndex := 11
  label := "Break occurring on its own outside of an indefinite-length item:"
  sequences := [appendixF1Seq81]

/-- Appendix F.1 sequence 82 (group 12, `81ff`). -/
def appendixF1Seq82 : List UInt8 := [0x81, 0xff]

/-- Appendix F.1 sequence 83 (group 12, `8200ff`). -/
def appendixF1Seq83 : List UInt8 := [0x82, 0x00, 0xff]

/-- Appendix F.1 sequence 84 (group 12, `a1ff`). -/
def appendixF1Seq84 : List UInt8 := [0xa1, 0xff]

/-- Appendix F.1 sequence 85 (group 12, `a1ff00`). -/
def appendixF1Seq85 : List UInt8 := [0xa1, 0xff, 0x00]

/-- Appendix F.1 sequence 86 (group 12, `a100ff`). -/
def appendixF1Seq86 : List UInt8 := [0xa1, 0x00, 0xff]

/-- Appendix F.1 sequence 87 (group 12, `a20000ff`). -/
def appendixF1Seq87 : List UInt8 := [0xa2, 0x00, 0x00, 0xff]

/-- Appendix F.1 sequence 88 (group 12, `9f81ff`). -/
def appendixF1Seq88 : List UInt8 := [0x9f, 0x81, 0xff]

/-- Appendix F.1 sequence 89 (group 12, `9f829f819f9fffffffff`). -/
def appendixF1Seq89 : List UInt8 := [0x9f, 0x82, 0x9f, 0x81, 0x9f, 0x9f, 0xff, 0xff, 0xff, 0xff]

/-- Appendix F.1 group 12: Break occurring in a definite-length array or map or a tag: (8 sequences). -/
def appendixF1Group12 : AppendixF1Group where
  groupIndex := 12
  label := "Break occurring in a definite-length array or map or a tag:"
  sequences := [appendixF1Seq82, appendixF1Seq83, appendixF1Seq84, appendixF1Seq85, appendixF1Seq86, appendixF1Seq87, appendixF1Seq88, appendixF1Seq89]

/-- Appendix F.1 sequence 90 (group 13, `bf00ff`). -/
def appendixF1Seq90 : List UInt8 := [0xbf, 0x00, 0xff]

/-- Appendix F.1 sequence 91 (group 13, `bf000000ff`). -/
def appendixF1Seq91 : List UInt8 := [0xbf, 0x00, 0x00, 0x00, 0xff]

/-- Appendix F.1 group 13: Break in an indefinite-length map that would lead to an odd number of items (break in a value position): (2 sequences). -/
def appendixF1Group13 : AppendixF1Group where
  groupIndex := 13
  label := "Break in an indefinite-length map that would lead to an odd number of items (break in a value position):"
  sequences := [appendixF1Seq90, appendixF1Seq91]

/-- Appendix F.1 sequence 92 (group 14, `1f`). -/
def appendixF1Seq92 : List UInt8 := [0x1f]

/-- Appendix F.1 sequence 93 (group 14, `3f`). -/
def appendixF1Seq93 : List UInt8 := [0x3f]

/-- Appendix F.1 sequence 94 (group 14, `df`). -/
def appendixF1Seq94 : List UInt8 := [0xdf]

/-- Appendix F.1 group 14: Major type 0, 1, 6 with additional information 31: (3 sequences). -/
def appendixF1Group14 : AppendixF1Group where
  groupIndex := 14
  label := "Major type 0, 1, 6 with additional information 31:"
  sequences := [appendixF1Seq92, appendixF1Seq93, appendixF1Seq94]

/-- All 14 malformed-input categories from RFC 8949 Appendix F.1. -/
def appendixF1Groups : List AppendixF1Group := [
  appendixF1Group01,
  appendixF1Group02,
  appendixF1Group03,
  appendixF1Group04,
  appendixF1Group05,
  appendixF1Group06,
  appendixF1Group07,
  appendixF1Group08,
  appendixF1Group09,
  appendixF1Group10,
  appendixF1Group11,
  appendixF1Group12,
  appendixF1Group13,
  appendixF1Group14
]

/-- Flat list of all 94 malformed byte sequences from RFC 8949 Appendix F.1. -/
def appendixF1Vectors : List (List UInt8) :=
  (appendixF1Groups.map AppendixF1Group.sequences).flatten

theorem appendixF1Groups_length : appendixF1Groups.length = 14 := rfl

theorem appendixF1Groups_counts :
    appendixF1Groups.map (fun g => g.sequences.length) =
      [18, 6, 7, 1, 2, 8, 24, 4, 8, 2, 1, 8, 2, 3] := rfl

theorem appendixF1Vectors_length : appendixF1Vectors.length = 94 := rfl

theorem appendixF1Vectors_nodup : appendixF1Vectors.Nodup := by decide

/-! ## Per-sequence refusal theorems (all 94 sequences) -/

/-- All decoders in the package refuse byte sequence `bs`. -/
def AllDecodersRefuse (bs : List UInt8) : Prop :=
  parseWellFormed bs = none ∧
  parseRaw bs = none ∧
  decodeDeterministic bs = none ∧
  decodeStrict .basic bs = none ∧
  decodeStrict .extended bs = none ∧
  decodeFirstWins .basic bs = none ∧
  decodeFirstWins .extended bs = none

theorem allDecodersRefuse_of_parseRaw_none {bs : List UInt8} (h : parseRaw bs = none) :
    AllDecodersRefuse bs := by
  have hpwf : parseWellFormed bs = none := by simp [parseWellFormed, h]
  refine ⟨hpwf, h, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [decodeDeterministic, decodeStrict, decodeFirstWins, hpwf]

theorem appendixF1Seq01_refused : AllDecodersRefuse appendixF1Seq01 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq02_refused : AllDecodersRefuse appendixF1Seq02 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq03_refused : AllDecodersRefuse appendixF1Seq03 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq04_refused : AllDecodersRefuse appendixF1Seq04 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq05_refused : AllDecodersRefuse appendixF1Seq05 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq06_refused : AllDecodersRefuse appendixF1Seq06 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq07_refused : AllDecodersRefuse appendixF1Seq07 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq08_refused : AllDecodersRefuse appendixF1Seq08 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq09_refused : AllDecodersRefuse appendixF1Seq09 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq10_refused : AllDecodersRefuse appendixF1Seq10 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq11_refused : AllDecodersRefuse appendixF1Seq11 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq12_refused : AllDecodersRefuse appendixF1Seq12 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq13_refused : AllDecodersRefuse appendixF1Seq13 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq14_refused : AllDecodersRefuse appendixF1Seq14 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq15_refused : AllDecodersRefuse appendixF1Seq15 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq16_refused : AllDecodersRefuse appendixF1Seq16 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq17_refused : AllDecodersRefuse appendixF1Seq17 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq18_refused : AllDecodersRefuse appendixF1Seq18 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq19_refused : AllDecodersRefuse appendixF1Seq19 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq20_refused : AllDecodersRefuse appendixF1Seq20 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq21_refused : AllDecodersRefuse appendixF1Seq21 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq22_refused : AllDecodersRefuse appendixF1Seq22 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq23_refused : AllDecodersRefuse appendixF1Seq23 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq24_refused : AllDecodersRefuse appendixF1Seq24 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq25_refused : AllDecodersRefuse appendixF1Seq25 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq26_refused : AllDecodersRefuse appendixF1Seq26 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq27_refused : AllDecodersRefuse appendixF1Seq27 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq28_refused : AllDecodersRefuse appendixF1Seq28 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq29_refused : AllDecodersRefuse appendixF1Seq29 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq30_refused : AllDecodersRefuse appendixF1Seq30 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq31_refused : AllDecodersRefuse appendixF1Seq31 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq32_refused : AllDecodersRefuse appendixF1Seq32 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq33_refused : AllDecodersRefuse appendixF1Seq33 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq34_refused : AllDecodersRefuse appendixF1Seq34 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq35_refused : AllDecodersRefuse appendixF1Seq35 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq36_refused : AllDecodersRefuse appendixF1Seq36 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq37_refused : AllDecodersRefuse appendixF1Seq37 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq38_refused : AllDecodersRefuse appendixF1Seq38 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq39_refused : AllDecodersRefuse appendixF1Seq39 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq40_refused : AllDecodersRefuse appendixF1Seq40 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq41_refused : AllDecodersRefuse appendixF1Seq41 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq42_refused : AllDecodersRefuse appendixF1Seq42 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq43_refused : AllDecodersRefuse appendixF1Seq43 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq44_refused : AllDecodersRefuse appendixF1Seq44 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq45_refused : AllDecodersRefuse appendixF1Seq45 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq46_refused : AllDecodersRefuse appendixF1Seq46 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq47_refused : AllDecodersRefuse appendixF1Seq47 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq48_refused : AllDecodersRefuse appendixF1Seq48 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq49_refused : AllDecodersRefuse appendixF1Seq49 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq50_refused : AllDecodersRefuse appendixF1Seq50 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq51_refused : AllDecodersRefuse appendixF1Seq51 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq52_refused : AllDecodersRefuse appendixF1Seq52 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq53_refused : AllDecodersRefuse appendixF1Seq53 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq54_refused : AllDecodersRefuse appendixF1Seq54 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq55_refused : AllDecodersRefuse appendixF1Seq55 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq56_refused : AllDecodersRefuse appendixF1Seq56 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq57_refused : AllDecodersRefuse appendixF1Seq57 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq58_refused : AllDecodersRefuse appendixF1Seq58 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq59_refused : AllDecodersRefuse appendixF1Seq59 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq60_refused : AllDecodersRefuse appendixF1Seq60 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq61_refused : AllDecodersRefuse appendixF1Seq61 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq62_refused : AllDecodersRefuse appendixF1Seq62 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq63_refused : AllDecodersRefuse appendixF1Seq63 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq64_refused : AllDecodersRefuse appendixF1Seq64 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq65_refused : AllDecodersRefuse appendixF1Seq65 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq66_refused : AllDecodersRefuse appendixF1Seq66 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq67_refused : AllDecodersRefuse appendixF1Seq67 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq68_refused : AllDecodersRefuse appendixF1Seq68 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq69_refused : AllDecodersRefuse appendixF1Seq69 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq70_refused : AllDecodersRefuse appendixF1Seq70 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq71_refused : AllDecodersRefuse appendixF1Seq71 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq72_refused : AllDecodersRefuse appendixF1Seq72 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq73_refused : AllDecodersRefuse appendixF1Seq73 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq74_refused : AllDecodersRefuse appendixF1Seq74 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq75_refused : AllDecodersRefuse appendixF1Seq75 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq76_refused : AllDecodersRefuse appendixF1Seq76 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq77_refused : AllDecodersRefuse appendixF1Seq77 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq78_refused : AllDecodersRefuse appendixF1Seq78 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq79_refused : AllDecodersRefuse appendixF1Seq79 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq80_refused : AllDecodersRefuse appendixF1Seq80 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq81_refused : AllDecodersRefuse appendixF1Seq81 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq82_refused : AllDecodersRefuse appendixF1Seq82 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq83_refused : AllDecodersRefuse appendixF1Seq83 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq84_refused : AllDecodersRefuse appendixF1Seq84 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq85_refused : AllDecodersRefuse appendixF1Seq85 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq86_refused : AllDecodersRefuse appendixF1Seq86 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq87_refused : AllDecodersRefuse appendixF1Seq87 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq88_refused : AllDecodersRefuse appendixF1Seq88 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq89_refused : AllDecodersRefuse appendixF1Seq89 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq90_refused : AllDecodersRefuse appendixF1Seq90 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq91_refused : AllDecodersRefuse appendixF1Seq91 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq92_refused : AllDecodersRefuse appendixF1Seq92 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq93_refused : AllDecodersRefuse appendixF1Seq93 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Seq94_refused : AllDecodersRefuse appendixF1Seq94 :=
  allDecodersRefuse_of_parseRaw_none rfl

theorem appendixF1Vectors_eq_explicit :
    appendixF1Vectors = [appendixF1Seq01, appendixF1Seq02, appendixF1Seq03, appendixF1Seq04, appendixF1Seq05, appendixF1Seq06, appendixF1Seq07, appendixF1Seq08, appendixF1Seq09, appendixF1Seq10, appendixF1Seq11, appendixF1Seq12, appendixF1Seq13, appendixF1Seq14, appendixF1Seq15, appendixF1Seq16, appendixF1Seq17, appendixF1Seq18, appendixF1Seq19, appendixF1Seq20, appendixF1Seq21, appendixF1Seq22, appendixF1Seq23, appendixF1Seq24, appendixF1Seq25, appendixF1Seq26, appendixF1Seq27, appendixF1Seq28, appendixF1Seq29, appendixF1Seq30, appendixF1Seq31, appendixF1Seq32, appendixF1Seq33, appendixF1Seq34, appendixF1Seq35, appendixF1Seq36, appendixF1Seq37, appendixF1Seq38, appendixF1Seq39, appendixF1Seq40, appendixF1Seq41, appendixF1Seq42, appendixF1Seq43, appendixF1Seq44, appendixF1Seq45, appendixF1Seq46, appendixF1Seq47, appendixF1Seq48, appendixF1Seq49, appendixF1Seq50, appendixF1Seq51, appendixF1Seq52, appendixF1Seq53, appendixF1Seq54, appendixF1Seq55, appendixF1Seq56, appendixF1Seq57, appendixF1Seq58, appendixF1Seq59, appendixF1Seq60, appendixF1Seq61, appendixF1Seq62, appendixF1Seq63, appendixF1Seq64, appendixF1Seq65, appendixF1Seq66, appendixF1Seq67, appendixF1Seq68, appendixF1Seq69, appendixF1Seq70, appendixF1Seq71, appendixF1Seq72, appendixF1Seq73, appendixF1Seq74, appendixF1Seq75, appendixF1Seq76, appendixF1Seq77, appendixF1Seq78, appendixF1Seq79, appendixF1Seq80, appendixF1Seq81, appendixF1Seq82, appendixF1Seq83, appendixF1Seq84, appendixF1Seq85, appendixF1Seq86, appendixF1Seq87, appendixF1Seq88, appendixF1Seq89, appendixF1Seq90, appendixF1Seq91, appendixF1Seq92, appendixF1Seq93, appendixF1Seq94] := rfl

/-- **Universal Appendix F.1 refusal theorem:** every one of the 94 malformed
byte sequences in RFC 8949 Appendix F.1 is refused by `parseWellFormed`,
`parseRaw`, `decodeDeterministic`, `decodeStrict`, and `decodeFirstWins`. -/
theorem appendixF1_all_refused : ∀ bs ∈ appendixF1Vectors, AllDecodersRefuse bs := by
  rw [appendixF1Vectors_eq_explicit]
  intro bs hbs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hbs
  rcases hbs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact appendixF1Seq01_refused
  · exact appendixF1Seq02_refused
  · exact appendixF1Seq03_refused
  · exact appendixF1Seq04_refused
  · exact appendixF1Seq05_refused
  · exact appendixF1Seq06_refused
  · exact appendixF1Seq07_refused
  · exact appendixF1Seq08_refused
  · exact appendixF1Seq09_refused
  · exact appendixF1Seq10_refused
  · exact appendixF1Seq11_refused
  · exact appendixF1Seq12_refused
  · exact appendixF1Seq13_refused
  · exact appendixF1Seq14_refused
  · exact appendixF1Seq15_refused
  · exact appendixF1Seq16_refused
  · exact appendixF1Seq17_refused
  · exact appendixF1Seq18_refused
  · exact appendixF1Seq19_refused
  · exact appendixF1Seq20_refused
  · exact appendixF1Seq21_refused
  · exact appendixF1Seq22_refused
  · exact appendixF1Seq23_refused
  · exact appendixF1Seq24_refused
  · exact appendixF1Seq25_refused
  · exact appendixF1Seq26_refused
  · exact appendixF1Seq27_refused
  · exact appendixF1Seq28_refused
  · exact appendixF1Seq29_refused
  · exact appendixF1Seq30_refused
  · exact appendixF1Seq31_refused
  · exact appendixF1Seq32_refused
  · exact appendixF1Seq33_refused
  · exact appendixF1Seq34_refused
  · exact appendixF1Seq35_refused
  · exact appendixF1Seq36_refused
  · exact appendixF1Seq37_refused
  · exact appendixF1Seq38_refused
  · exact appendixF1Seq39_refused
  · exact appendixF1Seq40_refused
  · exact appendixF1Seq41_refused
  · exact appendixF1Seq42_refused
  · exact appendixF1Seq43_refused
  · exact appendixF1Seq44_refused
  · exact appendixF1Seq45_refused
  · exact appendixF1Seq46_refused
  · exact appendixF1Seq47_refused
  · exact appendixF1Seq48_refused
  · exact appendixF1Seq49_refused
  · exact appendixF1Seq50_refused
  · exact appendixF1Seq51_refused
  · exact appendixF1Seq52_refused
  · exact appendixF1Seq53_refused
  · exact appendixF1Seq54_refused
  · exact appendixF1Seq55_refused
  · exact appendixF1Seq56_refused
  · exact appendixF1Seq57_refused
  · exact appendixF1Seq58_refused
  · exact appendixF1Seq59_refused
  · exact appendixF1Seq60_refused
  · exact appendixF1Seq61_refused
  · exact appendixF1Seq62_refused
  · exact appendixF1Seq63_refused
  · exact appendixF1Seq64_refused
  · exact appendixF1Seq65_refused
  · exact appendixF1Seq66_refused
  · exact appendixF1Seq67_refused
  · exact appendixF1Seq68_refused
  · exact appendixF1Seq69_refused
  · exact appendixF1Seq70_refused
  · exact appendixF1Seq71_refused
  · exact appendixF1Seq72_refused
  · exact appendixF1Seq73_refused
  · exact appendixF1Seq74_refused
  · exact appendixF1Seq75_refused
  · exact appendixF1Seq76_refused
  · exact appendixF1Seq77_refused
  · exact appendixF1Seq78_refused
  · exact appendixF1Seq79_refused
  · exact appendixF1Seq80_refused
  · exact appendixF1Seq81_refused
  · exact appendixF1Seq82_refused
  · exact appendixF1Seq83_refused
  · exact appendixF1Seq84_refused
  · exact appendixF1Seq85_refused
  · exact appendixF1Seq86_refused
  · exact appendixF1Seq87_refused
  · exact appendixF1Seq88_refused
  · exact appendixF1Seq89_refused
  · exact appendixF1Seq90_refused
  · exact appendixF1Seq91_refused
  · exact appendixF1Seq92_refused
  · exact appendixF1Seq93_refused
  · exact appendixF1Seq94_refused

end Cbor.Rfc8949.Vectors
