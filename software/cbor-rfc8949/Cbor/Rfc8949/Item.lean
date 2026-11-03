/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Head

/-!
# The float-free item AST and the wire-level syntax tree

`Item` is the milestone-1 abstract syntax: unsigned and negative integers
(major types 0, 1), byte and text strings (2, 3) — definite or as
indefinite-length chunk lists (§3.2.3) — definite and indefinite arrays and
maps with arbitrary `Item` keys (4, 5; §3.2.2), tags (6) and all simple
values (7; §3.3). Floating-point values are milestone 2 and have no
constructor here. Text payloads are raw bytes: UTF-8 validity is a
*validity* condition (§5.3.1), not a well-formedness one, so the generic
parser keeps invalid text as is.

`RawItem` is the same tree with every head's argument `Width` recorded. It
is the grammar of the wire: `RawItem.encode` serializes a tree, and
`RawItem.WF` says each width carries its argument and each simple value is
one §3.3 allows. The parser is proved to invert `encode` exactly on `WF`
trees (`Cbor.Rfc8949.Grammar`), so every well-formed float-free wire —
preferred or not — is `r.encode` for exactly one `WF` tree `r`.
`RawItem.toItem` forgets widths; `Item.toRaw` chooses preferred widths.
-/

namespace Cbor.Rfc8949

/-- Float-free CBOR data items (RFC 8949 §3.1, §3.2, §3.3, §3.4).
`nint n` is the negative integer `-1 - n` (major type 1). Indefinite-length
strings keep their chunks; indefinite arrays and maps are separate
constructors, so the tree records the serialization choice of §3.2. -/
inductive Item where
  | uint (n : Nat)
  | nint (n : Nat)
  | bytes (payload : List UInt8)
  | text (payload : List UInt8)
  | bytesIndef (chunks : List (List UInt8))
  | textIndef (chunks : List (List UInt8))
  | array (items : List Item)
  | arrayIndef (items : List Item)
  | map (entries : List (Item × Item))
  | mapIndef (entries : List (Item × Item))
  | tag (number : Nat) (content : Item)
  | simple (value : Nat)
  deriving Repr, Inhabited

/-- The wire-level syntax tree: an `Item` with the `Width` of every head. -/
inductive RawItem where
  | uint (w : Width) (n : Nat)
  | nint (w : Width) (n : Nat)
  | bytes (w : Width) (payload : List UInt8)
  | text (w : Width) (payload : List UInt8)
  | bytesIndef (chunks : List (Width × List UInt8))
  | textIndef (chunks : List (Width × List UInt8))
  | array (w : Width) (items : List RawItem)
  | arrayIndef (items : List RawItem)
  | map (w : Width) (entries : List (RawItem × RawItem))
  | mapIndef (entries : List (RawItem × RawItem))
  | tag (w : Width) (number : Nat) (content : RawItem)
  | simple (value : Nat)
  deriving Repr, Inhabited

namespace Item

/-- §3.3 Table 4: `false`, `true`, `null`, `undefined` are simple values 20–23. -/
abbrev false_ : Item := .simple 20
abbrev true_ : Item := .simple 21
abbrev null : Item := .simple 22
abbrev undefined : Item := .simple 23

/-- Structural induction for the nested `Item` type. -/
@[elab_as_elim]
theorem rec' {motive : Item → Prop}
    (uint : ∀ n, motive (.uint n)) (nint : ∀ n, motive (.nint n))
    (bytes : ∀ p, motive (.bytes p)) (text : ∀ p, motive (.text p))
    (bytesIndef : ∀ cs, motive (.bytesIndef cs)) (textIndef : ∀ cs, motive (.textIndef cs))
    (array : ∀ xs, (∀ x ∈ xs, motive x) → motive (.array xs))
    (arrayIndef : ∀ xs, (∀ x ∈ xs, motive x) → motive (.arrayIndef xs))
    (map : ∀ kvs, (∀ kv ∈ kvs, motive kv.1 ∧ motive kv.2) → motive (.map kvs))
    (mapIndef : ∀ kvs, (∀ kv ∈ kvs, motive kv.1 ∧ motive kv.2) → motive (.mapIndef kvs))
    (tag : ∀ t x, motive x → motive (.tag t x))
    (simple : ∀ v, motive (.simple v)) (x : Item) : motive x :=
  @Item.rec motive (fun xs => ∀ x ∈ xs, motive x) (fun kvs => ∀ kv ∈ kvs, motive kv.1 ∧ motive kv.2)
    (fun kv => motive kv.1 ∧ motive kv.2)
    uint nint bytes text bytesIndef textIndef array arrayIndef map mapIndef tag simple
    (by simp)
    (fun x xs hx hxs => by
      simp only [List.mem_cons]
      rintro y (rfl | hy)
      · exact hx
      · exact hxs y hy)
    (by simp)
    (fun kv kvs hkv hkvs => by
      simp only [List.mem_cons]
      rintro y (rfl | hy)
      · exact hkv
      · exact hkvs y hy)
    (fun k v hk hv => ⟨hk, hv⟩) x

end Item

namespace RawItem

/-- Structural induction for the nested `RawItem` type. -/
@[elab_as_elim]
theorem rec' {motive : RawItem → Prop}
    (uint : ∀ w n, motive (.uint w n)) (nint : ∀ w n, motive (.nint w n))
    (bytes : ∀ w p, motive (.bytes w p)) (text : ∀ w p, motive (.text w p))
    (bytesIndef : ∀ cs, motive (.bytesIndef cs)) (textIndef : ∀ cs, motive (.textIndef cs))
    (array : ∀ w xs, (∀ x ∈ xs, motive x) → motive (.array w xs))
    (arrayIndef : ∀ xs, (∀ x ∈ xs, motive x) → motive (.arrayIndef xs))
    (map : ∀ w kvs, (∀ kv ∈ kvs, motive kv.1 ∧ motive kv.2) → motive (.map w kvs))
    (mapIndef : ∀ kvs, (∀ kv ∈ kvs, motive kv.1 ∧ motive kv.2) → motive (.mapIndef kvs))
    (tag : ∀ w t x, motive x → motive (.tag w t x))
    (simple : ∀ v, motive (.simple v)) (x : RawItem) : motive x :=
  @RawItem.rec motive (fun xs => ∀ x ∈ xs, motive x)
    (fun kvs => ∀ kv ∈ kvs, motive kv.1 ∧ motive kv.2)
    (fun kv => motive kv.1 ∧ motive kv.2)
    uint nint bytes text bytesIndef textIndef array arrayIndef map mapIndef tag simple
    (by simp)
    (fun x xs hx hxs => by
      simp only [List.mem_cons]
      rintro y (rfl | hy)
      · exact hx
      · exact hxs y hy)
    (by simp)
    (fun kv kvs hkv hkvs => by
      simp only [List.mem_cons]
      rintro y (rfl | hy)
      · exact hkv
      · exact hkvs y hy)
    (fun k v hk hv => ⟨hk, hv⟩) x

/-! ## Serialization: the grammar of the wire -/

/-- Chunks of an indefinite-length string of major type `m`: each chunk is a
definite-length string of the same major type (§3.2.3). -/
def encodeChunks (m : Nat) : List (Width × List UInt8) → List UInt8
  | [] => []
  | (w, p) :: cs => encodeHead m w p.length ++ p ++ encodeChunks m cs

mutual
/-- Serialize a wire-level tree (§3, §3.1, §3.2, §3.3). -/
def encode : RawItem → List UInt8
  | .uint w n => encodeHead 0 w n
  | .nint w n => encodeHead 1 w n
  | .bytes w p => encodeHead 2 w p.length ++ p
  | .text w p => encodeHead 3 w p.length ++ p
  | .bytesIndef cs => 0x5f :: (encodeChunks 2 cs ++ [0xff])
  | .textIndef cs => 0x7f :: (encodeChunks 3 cs ++ [0xff])
  | .array w xs => encodeHead 4 w xs.length ++ encodeList xs
  | .arrayIndef xs => 0x9f :: (encodeList xs ++ [0xff])
  | .map w kvs => encodeHead 5 w kvs.length ++ encodePairs kvs
  | .mapIndef kvs => 0xbf :: (encodePairs kvs ++ [0xff])
  | .tag w t x => encodeHead 6 w t ++ encode x
  | .simple v => encodeHead 7 (simpleWidth v) v
/-- Concatenated encodings of array elements. -/
def encodeList : List RawItem → List UInt8
  | [] => []
  | x :: xs => encode x ++ encodeList xs
/-- Concatenated encodings of map entries, each key followed by its value (§3.1). -/
def encodePairs : List (RawItem × RawItem) → List UInt8
  | [] => []
  | (k, v) :: kvs => encode k ++ encode v ++ encodePairs kvs
end

mutual
/-- Well-formedness of a wire-level tree: every head's width carries its
argument (§3), and simple values are 0..23 or 32..255 (§3.3). -/
def WF : RawItem → Prop
  | .uint w n => w.fits n = true
  | .nint w n => w.fits n = true
  | .bytes w p => w.fits p.length = true
  | .text w p => w.fits p.length = true
  | .bytesIndef cs => ∀ c ∈ cs, c.1.fits c.2.length = true
  | .textIndef cs => ∀ c ∈ cs, c.1.fits c.2.length = true
  | .array w xs => w.fits xs.length = true ∧ WFList xs
  | .arrayIndef xs => WFList xs
  | .map w kvs => w.fits kvs.length = true ∧ WFPairs kvs
  | .mapIndef kvs => WFPairs kvs
  | .tag w t x => w.fits t = true ∧ WF x
  | .simple v => v < 24 ∨ (32 ≤ v ∧ v < 256)
def WFList : List RawItem → Prop
  | [] => True
  | x :: xs => WF x ∧ WFList xs
def WFPairs : List (RawItem × RawItem) → Prop
  | [] => True
  | (k, v) :: kvs => WF k ∧ WF v ∧ WFPairs kvs
end

mutual
/-- Forget the argument widths. -/
def toItem : RawItem → Item
  | .uint _ n => .uint n
  | .nint _ n => .nint n
  | .bytes _ p => .bytes p
  | .text _ p => .text p
  | .bytesIndef cs => .bytesIndef (cs.map Prod.snd)
  | .textIndef cs => .textIndef (cs.map Prod.snd)
  | .array _ xs => .array (toItemList xs)
  | .arrayIndef xs => .arrayIndef (toItemList xs)
  | .map _ kvs => .map (toItemPairs kvs)
  | .mapIndef kvs => .mapIndef (toItemPairs kvs)
  | .tag _ t x => .tag t (toItem x)
  | .simple v => .simple v
def toItemList : List RawItem → List Item
  | [] => []
  | x :: xs => toItem x :: toItemList xs
def toItemPairs : List (RawItem × RawItem) → List (Item × Item)
  | [] => []
  | (k, v) :: kvs => (toItem k, toItem v) :: toItemPairs kvs
end

mutual
/-- A tree with no indefinite-length item anywhere (§3.2 not used). -/
def Definite : RawItem → Prop
  | .bytesIndef _ | .textIndef _ | .arrayIndef _ | .mapIndef _ => False
  | .array _ xs => DefiniteList xs
  | .map _ kvs => DefinitePairs kvs
  | .tag _ _ x => Definite x
  | _ => True
def DefiniteList : List RawItem → Prop
  | [] => True
  | x :: xs => Definite x ∧ DefiniteList xs
def DefinitePairs : List (RawItem × RawItem) → Prop
  | [] => True
  | (k, v) :: kvs => Definite k ∧ Definite v ∧ DefinitePairs kvs
end

end RawItem

namespace Item

mutual
/-- Every argument fits the 64-bit argument range of §3, and simple values
are ones §3.3 allows. These are exactly the items that have an encoding. -/
def WF : Item → Prop
  | .uint n => n < 2 ^ 64
  | .nint n => n < 2 ^ 64
  | .bytes p => p.length < 2 ^ 64
  | .text p => p.length < 2 ^ 64
  | .bytesIndef cs => ∀ c ∈ cs, c.length < 2 ^ 64
  | .textIndef cs => ∀ c ∈ cs, c.length < 2 ^ 64
  | .array xs => xs.length < 2 ^ 64 ∧ WFList xs
  | .arrayIndef xs => WFList xs
  | .map kvs => kvs.length < 2 ^ 64 ∧ WFPairs kvs
  | .mapIndef kvs => WFPairs kvs
  | .tag t x => t < 2 ^ 64 ∧ WF x
  | .simple v => v < 24 ∨ (32 ≤ v ∧ v < 256)
def WFList : List Item → Prop
  | [] => True
  | x :: xs => WF x ∧ WFList xs
def WFPairs : List (Item × Item) → Prop
  | [] => True
  | (k, v) :: kvs => WF k ∧ WF v ∧ WFPairs kvs
end

mutual
/-- The wire-level tree using the preferred (shortest) width for every
argument (§4.1). Indefinite items stay indefinite; each chunk gets its
preferred head. -/
def toRaw : Item → RawItem
  | .uint n => .uint (Width.preferred n) n
  | .nint n => .nint (Width.preferred n) n
  | .bytes p => .bytes (Width.preferred p.length) p
  | .text p => .text (Width.preferred p.length) p
  | .bytesIndef cs => .bytesIndef (cs.map fun c => (Width.preferred c.length, c))
  | .textIndef cs => .textIndef (cs.map fun c => (Width.preferred c.length, c))
  | .array xs => .array (Width.preferred xs.length) (toRawList xs)
  | .arrayIndef xs => .arrayIndef (toRawList xs)
  | .map kvs => .map (Width.preferred kvs.length) (toRawPairs kvs)
  | .mapIndef kvs => .mapIndef (toRawPairs kvs)
  | .tag t x => .tag (Width.preferred t) t (toRaw x)
  | .simple v => .simple v
def toRawList : List Item → List RawItem
  | [] => []
  | x :: xs => toRaw x :: toRawList xs
def toRawPairs : List (Item × Item) → List (RawItem × RawItem)
  | [] => []
  | (k, v) :: kvs => (toRaw k, toRaw v) :: toRawPairs kvs
end

end Item

/-! ## List views of the mutual helpers -/

namespace RawItem

theorem encodeList_eq (xs : List RawItem) : encodeList xs = (xs.map encode).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeList, ih]

theorem encodePairs_eq (kvs : List (RawItem × RawItem)) :
    encodePairs kvs = (kvs.map fun kv => encode kv.1 ++ encode kv.2).flatten := by
  induction kvs with
  | nil => rfl
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [encodePairs, ih]

theorem WFList_iff (xs : List RawItem) : WFList xs ↔ ∀ x ∈ xs, WF x := by
  induction xs with
  | nil => simp [WFList]
  | cons x xs ih => simp [WFList, ih]

theorem WFPairs_iff (kvs : List (RawItem × RawItem)) :
    WFPairs kvs ↔ ∀ kv ∈ kvs, WF kv.1 ∧ WF kv.2 := by
  induction kvs with
  | nil => simp [WFPairs]
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [WFPairs, ih, and_assoc]

theorem toItemList_eq (xs : List RawItem) : toItemList xs = xs.map toItem := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [toItemList, ih]

theorem toItemPairs_eq (kvs : List (RawItem × RawItem)) :
    toItemPairs kvs = kvs.map fun kv => (toItem kv.1, toItem kv.2) := by
  induction kvs with
  | nil => rfl
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [toItemPairs, ih]

theorem DefiniteList_iff (xs : List RawItem) : DefiniteList xs ↔ ∀ x ∈ xs, Definite x := by
  induction xs with
  | nil => simp [DefiniteList]
  | cons x xs ih => simp [DefiniteList, ih]

theorem DefinitePairs_iff (kvs : List (RawItem × RawItem)) :
    DefinitePairs kvs ↔ ∀ kv ∈ kvs, Definite kv.1 ∧ Definite kv.2 := by
  induction kvs with
  | nil => simp [DefinitePairs]
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [DefinitePairs, ih, and_assoc]

end RawItem

namespace Item

theorem WFList_iff (xs : List Item) : WFList xs ↔ ∀ x ∈ xs, WF x := by
  induction xs with
  | nil => simp [WFList]
  | cons x xs ih => simp [WFList, ih]

theorem WFPairs_iff (kvs : List (Item × Item)) :
    WFPairs kvs ↔ ∀ kv ∈ kvs, WF kv.1 ∧ WF kv.2 := by
  induction kvs with
  | nil => simp [WFPairs]
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [WFPairs, ih, and_assoc]

theorem toRawList_eq (xs : List Item) : toRawList xs = xs.map toRaw := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [toRawList, ih]

theorem toRawPairs_eq (kvs : List (Item × Item)) :
    toRawPairs kvs = kvs.map fun kv => (toRaw kv.1, toRaw kv.2) := by
  induction kvs with
  | nil => rfl
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [toRawPairs, ih]

end Item

/-- Preferred serialization of an item (§4.1): shortest arguments, and the
item's own definite/indefinite choice. -/
def encodePreferred (x : Item) : List UInt8 := x.toRaw.encode

end Cbor.Rfc8949
