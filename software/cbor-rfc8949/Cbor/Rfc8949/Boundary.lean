/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Indefinite

/-!
# The size hypothesis cannot be dropped

The two fidelity-gate findings on ticket #34, restated against this
package's own parser and equivalence:

* **Array count** (comment 6460345651): `9f · 00^(2^64) · ff` is a
  well-formed indefinite array of 2^64 zeros. No well-formed wire whatsoever
  parses to a definite item equivalent to it, because a definite array head
  carries at most 2^64 - 1 elements.
* **String byte length** (comment 6487185741): two definite chunks of 2^63
  zero bytes inside `5f … ff`. The string has two chunks — it meets the
  withdrawn chunk-count bound — yet its 2^64 payload bytes fit no definite
  head. This is why the second amendment bounds the *total chunk payload
  bytes* of every indefinite string.

Both wires violate `Item.IndefBounded`; both are left indefinite by
`deflateIndefinite`. The lists are symbolic: nothing of length 2^63 or 2^64
is ever evaluated. Concretely, no proof in this file may use `decide`,
`native_decide`, a bare `rfl` (definitional equality), or `simp` with a
definition argument on any goal mentioning `arrayWire`, `arrayItem`,
`arrayRaw`, `stringWire`, `stringItem`, `stringRaw`, or `chunkPayload`:
kernel evaluation and definitional unfolding traverse the 2^63/2^64-element
lists element by element and exhaust memory (Nov 2026: three lanes
OOM-killed, `lean` at ~53 GB anon RSS on a 61 GiB machine, before this
file ever elaborated). Lengths are always computed symbolically via
`List.length_replicate`, `List.length_flatten`, and `List.map_replicate`,
and equalities between giant lists are proved by rewriting plus `congr`,
never by `rfl`. The grammar-fragment proofs from those comments are kept
verbatim (hash-checked) in `Cbor.Rfc8949.Boundary.ArrayCountFragment` and
`Cbor.Rfc8949.Boundary.ChunkCountFragment`.
-/

namespace Cbor.Rfc8949.Boundary

open Item

theorem flatten_replicate_singleton (n : Nat) (a : UInt8) :
    (List.replicate n [a]).flatten = List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/-- No item equivalent to an array of length `≥ 2^64` is a well-formed
definite item. -/
theorem no_definite_equiv_of_array {xs : List Item} (hlen : 2 ^ 64 ≤ xs.length)
    {y : Item} (hwf : y.WF) (hd : y.Definite) (heq : Equiv (.arrayIndef xs) y) : False := by
  cases y with
  | array ys =>
    simp only [Equiv, canon, canonWith, canonWithList_eq, array.injEq] at heq
    have := congrArg List.length heq
    simp only [List.length_map] at this
    exact absurd hwf.1 (by omega)
  | arrayIndef ys => exact hd
  | bytesIndef _ | textIndef _ | mapIndef _ => exact hd
  | _ => simp [Equiv, canon, canonWith] at heq

/-- No item equivalent to a byte string of `≥ 2^64` bytes is a well-formed
definite item. -/
theorem no_definite_equiv_of_bytes {cs : List (List UInt8)} (hlen : 2 ^ 64 ≤ cs.flatten.length)
    {y : Item} (hwf : y.WF) (hd : y.Definite) (heq : Equiv (.bytesIndef cs) y) : False := by
  cases y with
  | bytes p =>
    simp only [Equiv, canon, canonWith, bytes.injEq] at heq
    have hp : p.length < 2 ^ 64 := hwf
    rw [← heq] at hp
    omega
  | bytesIndef _ | textIndef _ | arrayIndef _ | mapIndef _ => exact hd
  | _ => simp [Equiv, canon, canonWith] at heq

/-! ## The array-count boundary -/

/-- `9f · 00^(2^64) · ff`. -/
def arrayWire : List UInt8 := 0x9f :: (List.replicate (2 ^ 64) 0x00 ++ [0xff])

/-- An indefinite array of 2^64 zeros. -/
def arrayItem : Item := .arrayIndef (List.replicate (2 ^ 64) (.uint 0))

def arrayRaw : RawItem := .arrayIndef (List.replicate (2 ^ 64) (.uint .inline 0))

theorem arrayRaw_WF : arrayRaw.WF := by
  show RawItem.WFList _
  rw [RawItem.WFList_iff]
  intro x hx
  rw [List.eq_of_mem_replicate hx]
  rfl

theorem arrayRaw_encode : arrayRaw.encode = arrayWire := by
  simp only [arrayRaw, arrayWire, RawItem.encode, RawItem.encodeList_eq, List.map_replicate]
  rw [show encodeHead 0 Width.inline 0 = [0x00] from rfl, flatten_replicate_singleton]

/-- The wire is well-formed: an indefinite array of 2^64 zeros (§3.2.2). -/
theorem parseWellFormed_arrayWire : parseWellFormed arrayWire = some arrayItem :=
  parseWellFormed_eq_some_iff.2 ⟨arrayRaw, arrayRaw_WF, arrayRaw_encode, by
    show Item.arrayIndef (RawItem.toItemList (List.replicate (2 ^ 64) (.uint .inline 0)))
        = Item.arrayIndef (List.replicate (2 ^ 64) (.uint 0))
    rw [RawItem.toItemList_eq, List.map_replicate]
    congr⟩

/-- It violates the size hypothesis (2^64 elements). -/
theorem arrayItem_not_indefBounded : ¬ arrayItem.IndefBounded := by
  intro h
  have hlen : (List.replicate (2 ^ 64) (Item.uint 0)).length < 2 ^ 64 := h.1
  rw [List.length_replicate] at hlen
  exact Nat.lt_irrefl _ hlen

/-- **No definite encoding exists**: no well-formed wire parses to a definite
item equivalent to the array. -/
theorem no_definite_encoding_arrayItem :
    ¬ ∃ bs y, parseWellFormed bs = some y ∧ y.Definite ∧ Equiv arrayItem y := by
  rintro ⟨bs, y, hp, hd, heq⟩
  have hlen : 2 ^ 64 ≤ (List.replicate (2 ^ 64) (Item.uint 0)).length := by
    rw [List.length_replicate]
    exact Nat.le_refl _
  exact no_definite_equiv_of_array hlen (parseWellFormed_WF hp) hd heq

/-- Hence no transformation can be both syntax-preserving (∃ form) and
definite-producing on this input. -/
theorem array_deflation_counterexample :
    ¬ ∀ bs x, parseWellFormed bs = some x →
      ∃ y, parseWellFormed (deflateIndefinite bs) = some y ∧ y.Definite ∧ Equiv x y := by
  intro h
  obtain ⟨y, hp, hd, heq⟩ := h arrayWire arrayItem parseWellFormed_arrayWire
  exact no_definite_encoding_arrayItem ⟨_, y, hp, hd, heq⟩

/-! ## The string byte-length boundary -/

/-- One chunk payload: 2^63 zero bytes. -/
def chunkPayload : List UInt8 := List.replicate (2 ^ 63) 0x00

/-- `5f · (5b 80 00 00 00 00 00 00 00 · 00^(2^63))² · ff`. -/
def stringWire : List UInt8 :=
  0x5f :: (([0x5b, 0x80, 0, 0, 0, 0, 0, 0, 0] ++ chunkPayload) ++
    ([0x5b, 0x80, 0, 0, 0, 0, 0, 0, 0] ++ chunkPayload) ++ [0xff])

/-- An indefinite byte string of two 2^63-byte chunks. -/
def stringItem : Item := .bytesIndef [chunkPayload, chunkPayload]

def stringRaw : RawItem := .bytesIndef [(.w8, chunkPayload), (.w8, chunkPayload)]

theorem chunkPayload_length : chunkPayload.length = 2 ^ 63 := by
  rw [chunkPayload, List.length_replicate]

theorem stringRaw_WF : stringRaw.WF := by
  show ∀ c ∈ [((Width.w8, chunkPayload)), (Width.w8, chunkPayload)], c.1.fits c.2.length = true
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> show Width.w8.fits chunkPayload.length = true <;>
    rw [chunkPayload_length] <;> decide

theorem stringRaw_encode : stringRaw.encode = stringWire := by
  have hhead : encodeHead 2 .w8 (2 ^ 63) = [0x5b, 0x80, 0, 0, 0, 0, 0, 0, 0] := by decide
  simp only [stringRaw, stringWire, RawItem.encode, RawItem.encodeChunks, chunkPayload_length,
    hhead, List.append_nil, List.append_assoc]

/-- The wire is well-formed: an indefinite byte string with two definite
chunks (§3.2.3). -/
theorem parseWellFormed_stringWire : parseWellFormed stringWire = some stringItem :=
  parseWellFormed_eq_some_iff.2 ⟨stringRaw, stringRaw_WF, stringRaw_encode, rfl⟩

/-- It meets the withdrawn chunk-count bound: two chunks. -/
theorem stringItem_chunk_count : stringItem = .bytesIndef [chunkPayload, chunkPayload] ∧
    [chunkPayload, chunkPayload].length < 2 ^ 64 := ⟨rfl, by decide⟩

/-- Its concatenated payload has exactly 2^64 bytes. -/
theorem stringItem_payload_length : [chunkPayload, chunkPayload].flatten.length = 2 ^ 64 := by
  simp [chunkPayload_length]

/-- It violates the amended size hypothesis (total chunk bytes 2^64). -/
theorem stringItem_not_indefBounded : ¬ stringItem.IndefBounded := by
  show ¬ [chunkPayload, chunkPayload].flatten.length < 2 ^ 64
  rw [stringItem_payload_length]
  exact Nat.lt_irrefl _

/-- **No definite encoding exists**, although the chunk count is 2. -/
theorem no_definite_encoding_stringItem :
    ¬ ∃ bs y, parseWellFormed bs = some y ∧ y.Definite ∧ Equiv stringItem y := by
  rintro ⟨bs, y, hp, hd, heq⟩
  have hlen : 2 ^ 64 ≤ [chunkPayload, chunkPayload].flatten.length := by
    rw [stringItem_payload_length]
    exact Nat.le_refl _
  exact no_definite_equiv_of_bytes hlen (parseWellFormed_WF hp) hd heq

/-- A chunk-count-only hypothesis would not suffice for definite production. -/
theorem chunk_count_bound_insufficient :
    ¬ ∀ bs cs, parseWellFormed bs = some (.bytesIndef cs) → cs.length < 2 ^ 64 →
      ∃ y, parseWellFormed (deflateIndefinite bs) = some y ∧ y.Definite ∧
        Equiv (.bytesIndef cs) y := by
  intro h
  obtain ⟨y, hp, hd, heq⟩ := h stringWire _ parseWellFormed_stringWire (by decide)
  exact no_definite_encoding_stringItem ⟨_, y, hp, hd, heq⟩

end Cbor.Rfc8949.Boundary
