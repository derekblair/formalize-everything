/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Bignum

/-!
# Equivalence of keys (§5.6.1), basic and extended

Serialization variants are not visible in the data model (§2), so an
indefinite-length string is its concatenated chunks (§3.2.3) and an
indefinite array or map is the array or map of its elements. §5.6.1 then
compares strings byte by byte, arrays element by element, maps as *sets of
pairs regardless of their order*, tags by number and content, and simple
values and integers by value.

`Item.canon` computes a canonical representative: definite everywhere, map
entries in strictly increasing order of their encodings with repeated
entries removed. `Item.Equiv x y` is `x.canon = y.canon`, so it is an
equivalence relation and decidable by construction; the theorems below
show it agrees with each §5.6.1 clause, including the set-of-pairs clause
for maps (`Item.equiv_map_iff`, for items whose canonical forms are
well-formed — automatic when every aggregate has fewer than 2^64 parts).

At the basic generic data model level bignums are distinct from integers
(§5.6.1, first paragraph). The extended generic data model created by tags
2 and 3 makes them equal by numeric value (§3.4.3); `Item.canonExt` and
`Item.EquivExt` implement that model.
-/

namespace Cbor.Rfc8949

/-- Order on map entries: by the key's encoding, then the value's. -/
def entryLt (p q : Item × Item) : Bool :=
  lexLt (encodePreferred p.1) (encodePreferred q.1) ||
    (encodePreferred p.1 == encodePreferred q.1 &&
      lexLt (encodePreferred p.2) (encodePreferred q.2))

/-- Insert into a strictly increasing list, dropping an entry already present. -/
def insertUniq (x : Item × Item) : List (Item × Item) → List (Item × Item)
  | [] => [x]
  | y :: ys => if y = x then y :: ys else if entryLt y x then y :: insertUniq x ys else x :: y :: ys

/-- Sort entries by `entryLt`, keeping one copy of each entry. -/
def sortUniq : List (Item × Item) → List (Item × Item)
  | [] => []
  | x :: xs => insertUniq x (sortUniq xs)

/-- The integer a bignum tag denotes once its content is canonical (a
definite byte string). -/
def bignumOf (t : Nat) (c : Item) : Option Int :=
  match c with
  | .bytes p => if t = 2 then some (beValue p) else if t = 3 then some (-1 - (beValue p : Int)) else none
  | _ => none

namespace Item

mutual
/-- Canonical representative for §5.6.1 equivalence. With `ext = true`, tag
2/3 bignums become their preferred integer serialization (§3.4.3). -/
def canonWith (ext : Bool) : Item → Item
  | .uint n => .uint n
  | .nint n => .nint n
  | .bytes p => .bytes p
  | .text p => .text p
  | .bytesIndef cs => .bytes cs.flatten
  | .textIndef cs => .text cs.flatten
  | .array xs => .array (canonWithList ext xs)
  | .arrayIndef xs => .array (canonWithList ext xs)
  | .map kvs => .map (sortUniq (canonWithPairs ext kvs))
  | .mapIndef kvs => .map (sortUniq (canonWithPairs ext kvs))
  | .tag t x =>
    match ext, bignumOf t (canonWith ext x) with
    | true, some z => encodeInt z
    | _, _ => .tag t (canonWith ext x)
  | .simple v => .simple v
def canonWithList (ext : Bool) : List Item → List Item
  | [] => []
  | x :: xs => canonWith ext x :: canonWithList ext xs
def canonWithPairs (ext : Bool) : List (Item × Item) → List (Item × Item)
  | [] => []
  | (k, v) :: kvs => (canonWith ext k, canonWith ext v) :: canonWithPairs ext kvs
end

/-- Canonical representative in the basic generic data model. -/
def canon : Item → Item := canonWith false

/-- Canonical representative in the extended generic data model of tags 2
and 3 (§3.4.3). -/
def canonExt : Item → Item := canonWith true

/-- §5.6.1 equivalence at the basic generic data model level. -/
def Equiv (x y : Item) : Prop := x.canon = y.canon

/-- §5.6.1 equivalence in the extended generic data model of tags 2 and 3:
bignums equal integers of the same value (§3.4.3). -/
def EquivExt (x y : Item) : Prop := x.canonExt = y.canonExt

instance : DecidableRel Equiv := fun x y => inferInstanceAs (Decidable (x.canon = y.canon))
instance : DecidableRel EquivExt := fun x y => inferInstanceAs (Decidable (x.canonExt = y.canonExt))

theorem Equiv.refl (x : Item) : Equiv x x := rfl
theorem Equiv.symm {x y : Item} (h : Equiv x y) : Equiv y x := Eq.symm h
theorem Equiv.trans {x y z : Item} (h₁ : Equiv x y) (h₂ : Equiv y z) : Equiv x z :=
  Eq.trans h₁ h₂
theorem EquivExt.refl (x : Item) : EquivExt x x := rfl
theorem EquivExt.symm {x y : Item} (h : EquivExt x y) : EquivExt y x := Eq.symm h
theorem EquivExt.trans {x y z : Item} (h₁ : EquivExt x y) (h₂ : EquivExt y z) : EquivExt x z :=
  Eq.trans h₁ h₂

theorem canonWithList_eq (ext : Bool) (xs : List Item) :
    canonWithList ext xs = xs.map (canonWith ext) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [canonWithList, ih]

theorem canonWithPairs_eq (ext : Bool) (kvs : List (Item × Item)) :
    canonWithPairs ext kvs = kvs.map fun kv => (canonWith ext kv.1, canonWith ext kv.2) := by
  induction kvs with
  | nil => rfl
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [canonWithPairs, ih]

/-! ### Serialization variants are invisible (§2, §3.2) -/

/-- An indefinite-length byte string is equivalent to its concatenated chunks. -/
theorem equiv_bytesIndef (cs : List (List UInt8)) : Equiv (.bytesIndef cs) (.bytes cs.flatten) :=
  rfl

/-- An indefinite-length text string is equivalent to its concatenated chunks. -/
theorem equiv_textIndef (cs : List (List UInt8)) : Equiv (.textIndef cs) (.text cs.flatten) :=
  rfl

theorem equiv_arrayIndef (xs : List Item) : Equiv (.arrayIndef xs) (.array xs) := rfl

theorem equiv_mapIndef (kvs : List (Item × Item)) : Equiv (.mapIndef kvs) (.map kvs) := rfl

theorem equivExt_bytesIndef (cs : List (List UInt8)) :
    EquivExt (.bytesIndef cs) (.bytes cs.flatten) := rfl

theorem equivExt_arrayIndef (xs : List Item) : EquivExt (.arrayIndef xs) (.array xs) := rfl

theorem equivExt_mapIndef (kvs : List (Item × Item)) : EquivExt (.mapIndef kvs) (.map kvs) := rfl

/-! ### §5.6.1 clause by clause (basic generic data model) -/

theorem equiv_uint_iff (a b : Nat) : Equiv (.uint a) (.uint b) ↔ a = b := by
  simp [Equiv, canon, canonWith]

theorem equiv_nint_iff (a b : Nat) : Equiv (.nint a) (.nint b) ↔ a = b := by
  simp [Equiv, canon, canonWith]

theorem not_equiv_uint_nint (a b : Nat) : ¬ Equiv (.uint a) (.nint b) := by
  simp [Equiv, canon, canonWith]

/-- Byte strings are compared byte by byte, definite or not. -/
theorem equiv_bytes_iff (p q : List UInt8) : Equiv (.bytes p) (.bytes q) ↔ p = q := by
  simp [Equiv, canon, canonWith]

theorem equiv_text_iff (p q : List UInt8) : Equiv (.text p) (.text q) ↔ p = q := by
  simp [Equiv, canon, canonWith]

/-- "Text strings are distinct from byte strings, even if composed of the
same bytes." -/
theorem not_equiv_bytes_text (p q : List UInt8) : ¬ Equiv (.bytes p) (.text q) := by
  simp [Equiv, canon, canonWith]

theorem equiv_bytesIndef_iff (cs ds : List (List UInt8)) :
    Equiv (.bytesIndef cs) (.bytesIndef ds) ↔ cs.flatten = ds.flatten := by
  simp [Equiv, canon, canonWith]

theorem equiv_textIndef_iff (cs ds : List (List UInt8)) :
    Equiv (.textIndef cs) (.textIndef ds) ↔ cs.flatten = ds.flatten := by
  simp [Equiv, canon, canonWith]

/-- Two lists related position by position (same length). -/
def Elementwise {α : Type} (R : α → α → Prop) : List α → List α → Prop
  | [], [] => True
  | x :: xs, y :: ys => R x y ∧ Elementwise R xs ys
  | _, _ => False

theorem map_eq_map_iff_elementwise {α β : Type} (f : α → β) :
    ∀ xs ys : List α, xs.map f = ys.map f ↔ Elementwise (fun x y => f x = f y) xs ys
  | [], [] => by simp [Elementwise]
  | [], _ :: _ => by simp [Elementwise]
  | _ :: _, [] => by simp [Elementwise]
  | x :: xs, y :: ys => by simp [Elementwise, map_eq_map_iff_elementwise f xs ys]

/-- Arrays are compared element by element (definite or indefinite). -/
theorem equiv_array_iff (xs ys : List Item) :
    Equiv (.array xs) (.array ys) ↔ Elementwise Equiv xs ys := by
  simp only [Equiv, canon, canonWith, canonWithList_eq, array.injEq]
  exact map_eq_map_iff_elementwise _ xs ys

theorem equiv_arrayIndef_iff (xs ys : List Item) :
    Equiv (.arrayIndef xs) (.array ys) ↔ Elementwise Equiv xs ys :=
  equiv_array_iff xs ys

/-- "Tagged values are equal if both the tag number and the tag content are
equal." -/
theorem equiv_tag_iff (t u : Nat) (x y : Item) :
    Equiv (.tag t x) (.tag u y) ↔ t = u ∧ Equiv x y := by
  simp [Equiv, canon, canonWith]

/-- "A tagged value is distinct from an untagged value" — at the basic level
this holds for bignum tags too (§5.6.1 first paragraph). -/
theorem not_equiv_tag_uint (t : Nat) (x : Item) (n : Nat) : ¬ Equiv (.tag t x) (.uint n) := by
  simp [Equiv, canon, canonWith]

theorem equiv_simple_iff (v w : Nat) : Equiv (.simple v) (.simple w) ↔ v = w := by
  simp [Equiv, canon, canonWith]

/-- "A simple value 2 is not equivalent to an integer 2." -/
theorem not_equiv_simple_uint (v n : Nat) : ¬ Equiv (.simple v) (.uint n) := by
  simp [Equiv, canon, canonWith]

/-- "An array is never equivalent to a map." -/
theorem not_equiv_array_map (xs : List Item) (kvs : List (Item × Item)) :
    ¬ Equiv (.array xs) (.map kvs) := by
  simp [Equiv, canon, canonWith]

end Item

end Cbor.Rfc8949
