/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Item

/-!
# The step-fueled well-formedness parser

`decodeRaw fuel bs` decodes one wire-level tree from the front of `bs`.
Recursion is structural in `fuel`: each item consumes one unit, and each
step of an indefinite-length loop (0x5f, 0x7f, 0x9f, 0xbf … 0xff) consumes
one unit per element, chunk or key/value pair (ticket #34, binding guidance
I5). The public entry points start with `bs.length + 1` units, which
`Cbor.Rfc8949.Grammar` proves is enough for every well-formed input, so the
fuel never truncates the grammar.

Naming (ticket #34, binding amendment I4): `parseWellFormed` is the generic
parser. It accepts non-preferred heads, indefinite-length items, unsorted
maps, maps with duplicate keys and text strings whose bytes are not valid
UTF-8 — all well-formed (§3, §5.3.1). The strict decoder is
`decodeDeterministic` (`Cbor.Rfc8949.Deterministic`). There is no
overloaded `decode`.
-/

namespace Cbor.Rfc8949

/-- One chunk of an indefinite-length string of major type `m`: a
definite-length string of the same major type (§3.2.3). Any other head —
another major type, a nested indefinite string, a break — is refused. -/
def decodeChunk (m : Nat) (bs : List UInt8) : Option ((Width × List UInt8) × List UInt8) :=
  match decodeHead bs with
  | some (.arg m' w n, rest) =>
    if m' = m ∧ n ≤ rest.length then some ((w, rest.take n), rest.drop n) else none
  | _ => none

/-- Decode exactly `n` elements (definite-length arrays and maps, §3.1). -/
def decodeCount {α : Type} (dec : List UInt8 → Option (α × List UInt8)) :
    Nat → List UInt8 → Option (List α × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    match dec bs with
    | none => none
    | some (x, rest) =>
      match decodeCount dec n rest with
      | none => none
      | some (xs, rest') => some (x :: xs, rest')

/-- Decode elements until the "break" stop code 0xff (§3.2.1–§3.2.3). Each
element step consumes one unit of step fuel (I5). -/
def decodeUntilBreak {α : Type} (dec : List UInt8 → Option (α × List UInt8)) :
    Nat → List UInt8 → Option (List α × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, b :: bs =>
    if b = 0xff then some ([], bs)
    else
      match dec (b :: bs) with
      | none => none
      | some (x, rest) =>
        match decodeUntilBreak dec fuel rest with
        | none => none
        | some (xs, rest') => some (x :: xs, rest')

/-- A map entry: a key immediately followed by its value (§3.1). -/
def decodePair {α : Type} (dec : List UInt8 → Option (α × List UInt8)) (bs : List UInt8) :
    Option ((α × α) × List UInt8) :=
  match dec bs with
  | none => none
  | some (k, rest) =>
    match dec rest with
    | none => none
    | some (v, rest') => some ((k, v), rest')

/-- Everything after a decoded head: string payloads, the elements of
definite arrays and maps, a tag's content, or the chunks / elements / pairs
of an indefinite-length item up to its break. `item` decodes nested items;
`fuel` bounds the indefinite-length loops (one unit per step, I5). -/
def decodeBody (item : List UInt8 → Option (RawItem × List UInt8)) (fuel : Nat) :
    Head → List UInt8 → Option (RawItem × List UInt8)
  | .arg 0 w n, rest => some (.uint w n, rest)
  | .arg 1 w n, rest => some (.nint w n, rest)
  | .arg 2 w n, rest =>
    if n ≤ rest.length then some (.bytes w (rest.take n), rest.drop n) else none
  | .arg 3 w n, rest =>
    if n ≤ rest.length then some (.text w (rest.take n), rest.drop n) else none
  | .arg 4 w n, rest =>
    match decodeCount item n rest with
    | none => none
    | some (xs, rest') => some (.array w xs, rest')
  | .arg 5 w n, rest =>
    match decodeCount (decodePair item) n rest with
    | none => none
    | some (kvs, rest') => some (.map w kvs, rest')
  | .arg 6 w t, rest =>
    match item rest with
    | none => none
    | some (x, rest') => some (.tag w t x, rest')
  | .arg _ _ _, _ => none
  | .indef 2, rest =>
    match decodeUntilBreak (decodeChunk 2) fuel rest with
    | none => none
    | some (cs, rest') => some (.bytesIndef cs, rest')
  | .indef 3, rest =>
    match decodeUntilBreak (decodeChunk 3) fuel rest with
    | none => none
    | some (cs, rest') => some (.textIndef cs, rest')
  | .indef 4, rest =>
    match decodeUntilBreak item fuel rest with
    | none => none
    | some (xs, rest') => some (.arrayIndef xs, rest')
  | .indef 5, rest =>
    match decodeUntilBreak (decodePair item) fuel rest with
    | none => none
    | some (kvs, rest') => some (.mapIndef kvs, rest')
  | .indef _, _ => none
  | .brk, _ => none
  | .simple v, rest => some (.simple v, rest)

/-- The step-fueled wire decoder (§3, Appendix C): one unit of fuel per
item, nested items get the remaining fuel. -/
def decodeRaw : Nat → List UInt8 → Option (RawItem × List UInt8)
  | 0, _ => none
  | fuel + 1, bs =>
    match decodeHead bs with
    | none => none
    | some (h, rest) => decodeBody (decodeRaw fuel) fuel h rest

/-- Decode one wire-level tree from the front of `bs`, with the initial fuel
`bs.length + 1` (I5). -/
def decodePrefixRaw (bs : List UInt8) : Option (RawItem × List UInt8) :=
  decodeRaw (bs.length + 1) bs

/-- The whole input must be exactly one well-formed item (§3, Appendix C). -/
def parseRaw (bs : List UInt8) : Option RawItem :=
  match decodePrefixRaw bs with
  | some (r, []) => some r
  | _ => none

/-- Decode one item from the front of `bs` and return the unread bytes (the
self-delimiting use of §3, as in CBOR sequences). -/
def decodePrefix (bs : List UInt8) : Option (Item × List UInt8) :=
  match decodePrefixRaw bs with
  | some (r, rest) => some (r.toItem, rest)
  | none => none

/-- The generic float-free parser: `some x` exactly when `bs` is one
well-formed float-free encoded data item (proved in
`Cbor.Rfc8949.Grammar`). Floating-point heads are milestone 2 and are
refused here. -/
def parseWellFormed (bs : List UInt8) : Option Item :=
  match parseRaw bs with
  | some r => some r.toItem
  | none => none

end Cbor.Rfc8949
